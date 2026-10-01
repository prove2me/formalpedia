-- Prove2me | solution 1 for syracuse_descends_range_2097435_2099435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:16:31.934145+00:00
-- url     : https://prove2.me/submissions/a41d7260-a43d-4c17-80a9-9b84138e6134

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

theorem B7175429 : Blo 2097435 7175429 := bbase (se 4 (by rfl) ⟨672696, by rfl⟩ : syracuseStep 7175429 = 1345393) (by norm_num)
theorem B4783619 : Blo 2097435 4783619 := bstep (se 1 (by rfl) ⟨3587714, by rfl⟩ : syracuseStep 4783619 = 7175429) B7175429
theorem B3189079 : Blo 2097435 3189079 := bstep (se 1 (by rfl) ⟨2391809, by rfl⟩ : syracuseStep 3189079 = 4783619) B4783619
theorem B4252105 : Blo 2097435 4252105 := bstep (se 2 (by rfl) ⟨1594539, by rfl⟩ : syracuseStep 4252105 = 3189079) B3189079
theorem B22677893 : Blo 2097435 22677893 := bstep (se 4 (by rfl) ⟨2126052, by rfl⟩ : syracuseStep 22677893 = 4252105) B4252105
theorem B15118595 : Blo 2097435 15118595 := bstep (se 1 (by rfl) ⟨11338946, by rfl⟩ : syracuseStep 15118595 = 22677893) B22677893
theorem B10079063 : Blo 2097435 10079063 := bstep (se 1 (by rfl) ⟨7559297, by rfl⟩ : syracuseStep 10079063 = 15118595) B15118595
theorem B6719375 : Blo 2097435 6719375 := bstep (se 1 (by rfl) ⟨5039531, by rfl⟩ : syracuseStep 6719375 = 10079063) B10079063
theorem B17918333 : Blo 2097435 17918333 := bstep (se 3 (by rfl) ⟨3359687, by rfl⟩ : syracuseStep 17918333 = 6719375) B6719375
theorem B11945555 : Blo 2097435 11945555 := bstep (se 1 (by rfl) ⟨8959166, by rfl⟩ : syracuseStep 11945555 = 17918333) B17918333
theorem B7963703 : Blo 2097435 7963703 := bstep (se 1 (by rfl) ⟨5972777, by rfl⟩ : syracuseStep 7963703 = 11945555) B11945555
theorem B5309135 : Blo 2097435 5309135 := bstep (se 1 (by rfl) ⟨3981851, by rfl⟩ : syracuseStep 5309135 = 7963703) B7963703
theorem B3539423 : Blo 2097435 3539423 := bstep (se 1 (by rfl) ⟨2654567, by rfl⟩ : syracuseStep 3539423 = 5309135) B5309135
theorem B2359615 : Blo 2097435 2359615 := bstep (se 1 (by rfl) ⟨1769711, by rfl⟩ : syracuseStep 2359615 = 3539423) B3539423
theorem B3146153 : Blo 2097435 3146153 := bstep (se 2 (by rfl) ⟨1179807, by rfl⟩ : syracuseStep 3146153 = 2359615) B2359615
theorem B2097435 : Blo 2097435 2097435 := bstep (se 1 (by rfl) ⟨1573076, by rfl⟩ : syracuseStep 2097435 = 3146153) B3146153
theorem B7963717 : Blo 2097435 7963717 := bbase (se 4 (by rfl) ⟨746598, by rfl⟩ : syracuseStep 7963717 = 1493197) (by norm_num)
theorem B10618289 : Blo 2097435 10618289 := bstep (se 2 (by rfl) ⟨3981858, by rfl⟩ : syracuseStep 10618289 = 7963717) B7963717
theorem B7078859 : Blo 2097435 7078859 := bstep (se 1 (by rfl) ⟨5309144, by rfl⟩ : syracuseStep 7078859 = 10618289) B10618289
theorem B4719239 : Blo 2097435 4719239 := bstep (se 1 (by rfl) ⟨3539429, by rfl⟩ : syracuseStep 4719239 = 7078859) B7078859
theorem B3146159 : Blo 2097435 3146159 := bstep (se 1 (by rfl) ⟨2359619, by rfl⟩ : syracuseStep 3146159 = 4719239) B4719239
theorem B2097439 : Blo 2097435 2097439 := bstep (se 1 (by rfl) ⟨1573079, by rfl⟩ : syracuseStep 2097439 = 3146159) B3146159
theorem B3146165 : Blo 2097435 3146165 := bbase (se 5 (by rfl) ⟨147476, by rfl⟩ : syracuseStep 3146165 = 294953) (by norm_num)
theorem B2097443 : Blo 2097435 2097443 := bstep (se 1 (by rfl) ⟨1573082, by rfl⟩ : syracuseStep 2097443 = 3146165) B3146165
theorem B5309165 : Blo 2097435 5309165 := bbase (se 3 (by rfl) ⟨995468, by rfl⟩ : syracuseStep 5309165 = 1990937) (by norm_num)
theorem B3539443 : Blo 2097435 3539443 := bstep (se 1 (by rfl) ⟨2654582, by rfl⟩ : syracuseStep 3539443 = 5309165) B5309165
theorem B4719257 : Blo 2097435 4719257 := bstep (se 2 (by rfl) ⟨1769721, by rfl⟩ : syracuseStep 4719257 = 3539443) B3539443
theorem B3146171 : Blo 2097435 3146171 := bstep (se 1 (by rfl) ⟨2359628, by rfl⟩ : syracuseStep 3146171 = 4719257) B4719257
theorem B2097447 : Blo 2097435 2097447 := bstep (se 1 (by rfl) ⟨1573085, by rfl⟩ : syracuseStep 2097447 = 3146171) B3146171
theorem B2359633 : Blo 2097435 2359633 := bbase (se 2 (by rfl) ⟨884862, by rfl⟩ : syracuseStep 2359633 = 1769725) (by norm_num)
theorem B3146177 : Blo 2097435 3146177 := bstep (se 2 (by rfl) ⟨1179816, by rfl⟩ : syracuseStep 3146177 = 2359633) B2359633
theorem B2097451 : Blo 2097435 2097451 := bstep (se 1 (by rfl) ⟨1573088, by rfl⟩ : syracuseStep 2097451 = 3146177) B3146177
theorem B2239813 : Blo 2097435 2239813 := bbase (se 4 (by rfl) ⟨209982, by rfl⟩ : syracuseStep 2239813 = 419965) (by norm_num)
theorem B2986417 : Blo 2097435 2986417 := bstep (se 2 (by rfl) ⟨1119906, by rfl⟩ : syracuseStep 2986417 = 2239813) B2239813
theorem B3981889 : Blo 2097435 3981889 := bstep (se 2 (by rfl) ⟨1493208, by rfl⟩ : syracuseStep 3981889 = 2986417) B2986417
theorem B5309185 : Blo 2097435 5309185 := bstep (se 2 (by rfl) ⟨1990944, by rfl⟩ : syracuseStep 5309185 = 3981889) B3981889
theorem B7078913 : Blo 2097435 7078913 := bstep (se 2 (by rfl) ⟨2654592, by rfl⟩ : syracuseStep 7078913 = 5309185) B5309185
theorem B4719275 : Blo 2097435 4719275 := bstep (se 1 (by rfl) ⟨3539456, by rfl⟩ : syracuseStep 4719275 = 7078913) B7078913
theorem B3146183 : Blo 2097435 3146183 := bstep (se 1 (by rfl) ⟨2359637, by rfl⟩ : syracuseStep 3146183 = 4719275) B4719275
theorem B2097455 : Blo 2097435 2097455 := bstep (se 1 (by rfl) ⟨1573091, by rfl⟩ : syracuseStep 2097455 = 3146183) B3146183
theorem B3146189 : Blo 2097435 3146189 := bbase (se 3 (by rfl) ⟨589910, by rfl⟩ : syracuseStep 3146189 = 1179821) (by norm_num)
theorem B2097459 : Blo 2097435 2097459 := bstep (se 1 (by rfl) ⟨1573094, by rfl⟩ : syracuseStep 2097459 = 3146189) B3146189
theorem B4719293 : Blo 2097435 4719293 := bbase (se 3 (by rfl) ⟨884867, by rfl⟩ : syracuseStep 4719293 = 1769735) (by norm_num)
theorem B3146195 : Blo 2097435 3146195 := bstep (se 1 (by rfl) ⟨2359646, by rfl⟩ : syracuseStep 3146195 = 4719293) B4719293
theorem B2097463 : Blo 2097435 2097463 := bstep (se 1 (by rfl) ⟨1573097, by rfl⟩ : syracuseStep 2097463 = 3146195) B3146195
theorem B3539477 : Blo 2097435 3539477 := bbase (se 6 (by rfl) ⟨82956, by rfl⟩ : syracuseStep 3539477 = 165913) (by norm_num)
theorem B2359651 : Blo 2097435 2359651 := bstep (se 1 (by rfl) ⟨1769738, by rfl⟩ : syracuseStep 2359651 = 3539477) B3539477
theorem B3146201 : Blo 2097435 3146201 := bstep (se 2 (by rfl) ⟨1179825, by rfl⟩ : syracuseStep 3146201 = 2359651) B2359651
theorem B2097467 : Blo 2097435 2097467 := bstep (se 1 (by rfl) ⟨1573100, by rfl⟩ : syracuseStep 2097467 = 3146201) B3146201
theorem B2126089 : Blo 2097435 2126089 := bbase (se 2 (by rfl) ⟨797283, by rfl⟩ : syracuseStep 2126089 = 1594567) (by norm_num)
theorem B2834785 : Blo 2097435 2834785 := bstep (se 2 (by rfl) ⟨1063044, by rfl⟩ : syracuseStep 2834785 = 2126089) B2126089
theorem B3779713 : Blo 2097435 3779713 := bstep (se 2 (by rfl) ⟨1417392, by rfl⟩ : syracuseStep 3779713 = 2834785) B2834785
theorem B20158469 : Blo 2097435 20158469 := bstep (se 4 (by rfl) ⟨1889856, by rfl⟩ : syracuseStep 20158469 = 3779713) B3779713
theorem B13438979 : Blo 2097435 13438979 := bstep (se 1 (by rfl) ⟨10079234, by rfl⟩ : syracuseStep 13438979 = 20158469) B20158469
theorem B8959319 : Blo 2097435 8959319 := bstep (se 1 (by rfl) ⟨6719489, by rfl⟩ : syracuseStep 8959319 = 13438979) B13438979
theorem B5972879 : Blo 2097435 5972879 := bstep (se 1 (by rfl) ⟨4479659, by rfl⟩ : syracuseStep 5972879 = 8959319) B8959319
theorem B15927677 : Blo 2097435 15927677 := bstep (se 3 (by rfl) ⟨2986439, by rfl⟩ : syracuseStep 15927677 = 5972879) B5972879
theorem B10618451 : Blo 2097435 10618451 := bstep (se 1 (by rfl) ⟨7963838, by rfl⟩ : syracuseStep 10618451 = 15927677) B15927677
theorem B7078967 : Blo 2097435 7078967 := bstep (se 1 (by rfl) ⟨5309225, by rfl⟩ : syracuseStep 7078967 = 10618451) B10618451
theorem B4719311 : Blo 2097435 4719311 := bstep (se 1 (by rfl) ⟨3539483, by rfl⟩ : syracuseStep 4719311 = 7078967) B7078967
theorem B3146207 : Blo 2097435 3146207 := bstep (se 1 (by rfl) ⟨2359655, by rfl⟩ : syracuseStep 3146207 = 4719311) B4719311
theorem B2097471 : Blo 2097435 2097471 := bstep (se 1 (by rfl) ⟨1573103, by rfl⟩ : syracuseStep 2097471 = 3146207) B3146207
theorem B3146213 : Blo 2097435 3146213 := bbase (se 4 (by rfl) ⟨294957, by rfl⟩ : syracuseStep 3146213 = 589915) (by norm_num)
theorem B2097475 : Blo 2097435 2097475 := bstep (se 1 (by rfl) ⟨1573106, by rfl⟩ : syracuseStep 2097475 = 3146213) B3146213
theorem B8504389 : Blo 2097435 8504389 := bbase (se 4 (by rfl) ⟨797286, by rfl⟩ : syracuseStep 8504389 = 1594573) (by norm_num)
theorem B11339185 : Blo 2097435 11339185 := bstep (se 2 (by rfl) ⟨4252194, by rfl⟩ : syracuseStep 11339185 = 8504389) B8504389
theorem B15118913 : Blo 2097435 15118913 := bstep (se 2 (by rfl) ⟨5669592, by rfl⟩ : syracuseStep 15118913 = 11339185) B11339185
theorem B10079275 : Blo 2097435 10079275 := bstep (se 1 (by rfl) ⟨7559456, by rfl⟩ : syracuseStep 10079275 = 15118913) B15118913
theorem B13439033 : Blo 2097435 13439033 := bstep (se 2 (by rfl) ⟨5039637, by rfl⟩ : syracuseStep 13439033 = 10079275) B10079275
theorem B8959355 : Blo 2097435 8959355 := bstep (se 1 (by rfl) ⟨6719516, by rfl⟩ : syracuseStep 8959355 = 13439033) B13439033
theorem B5972903 : Blo 2097435 5972903 := bstep (se 1 (by rfl) ⟨4479677, by rfl⟩ : syracuseStep 5972903 = 8959355) B8959355
theorem B3981935 : Blo 2097435 3981935 := bstep (se 1 (by rfl) ⟨2986451, by rfl⟩ : syracuseStep 3981935 = 5972903) B5972903
theorem B2654623 : Blo 2097435 2654623 := bstep (se 1 (by rfl) ⟨1990967, by rfl⟩ : syracuseStep 2654623 = 3981935) B3981935
theorem B3539497 : Blo 2097435 3539497 := bstep (se 2 (by rfl) ⟨1327311, by rfl⟩ : syracuseStep 3539497 = 2654623) B2654623
theorem B4719329 : Blo 2097435 4719329 := bstep (se 2 (by rfl) ⟨1769748, by rfl⟩ : syracuseStep 4719329 = 3539497) B3539497
theorem B3146219 : Blo 2097435 3146219 := bstep (se 1 (by rfl) ⟨2359664, by rfl⟩ : syracuseStep 3146219 = 4719329) B4719329
theorem B2097479 : Blo 2097435 2097479 := bstep (se 1 (by rfl) ⟨1573109, by rfl⟩ : syracuseStep 2097479 = 3146219) B3146219
theorem B2359669 : Blo 2097435 2359669 := bbase (se 5 (by rfl) ⟨110609, by rfl⟩ : syracuseStep 2359669 = 221219) (by norm_num)
theorem B3146225 : Blo 2097435 3146225 := bstep (se 2 (by rfl) ⟨1179834, by rfl⟩ : syracuseStep 3146225 = 2359669) B2359669
theorem B2097483 : Blo 2097435 2097483 := bstep (se 1 (by rfl) ⟨1573112, by rfl⟩ : syracuseStep 2097483 = 3146225) B3146225
theorem B2654633 : Blo 2097435 2654633 := bbase (se 2 (by rfl) ⟨995487, by rfl⟩ : syracuseStep 2654633 = 1990975) (by norm_num)
theorem B7079021 : Blo 2097435 7079021 := bstep (se 3 (by rfl) ⟨1327316, by rfl⟩ : syracuseStep 7079021 = 2654633) B2654633
theorem B4719347 : Blo 2097435 4719347 := bstep (se 1 (by rfl) ⟨3539510, by rfl⟩ : syracuseStep 4719347 = 7079021) B7079021
theorem B3146231 : Blo 2097435 3146231 := bstep (se 1 (by rfl) ⟨2359673, by rfl⟩ : syracuseStep 3146231 = 4719347) B4719347
theorem B2097487 : Blo 2097435 2097487 := bstep (se 1 (by rfl) ⟨1573115, by rfl⟩ : syracuseStep 2097487 = 3146231) B3146231
theorem B3146237 : Blo 2097435 3146237 := bbase (se 3 (by rfl) ⟨589919, by rfl⟩ : syracuseStep 3146237 = 1179839) (by norm_num)
theorem B2097491 : Blo 2097435 2097491 := bstep (se 1 (by rfl) ⟨1573118, by rfl⟩ : syracuseStep 2097491 = 3146237) B3146237
theorem B4719365 : Blo 2097435 4719365 := bbase (se 4 (by rfl) ⟨442440, by rfl⟩ : syracuseStep 4719365 = 884881) (by norm_num)
theorem B3146243 : Blo 2097435 3146243 := bstep (se 1 (by rfl) ⟨2359682, by rfl⟩ : syracuseStep 3146243 = 4719365) B4719365
theorem B2097495 : Blo 2097435 2097495 := bstep (se 1 (by rfl) ⟨1573121, by rfl⟩ : syracuseStep 2097495 = 3146243) B3146243
theorem B3981973 : Blo 2097435 3981973 := bbase (se 6 (by rfl) ⟨93327, by rfl⟩ : syracuseStep 3981973 = 186655) (by norm_num)
theorem B5309297 : Blo 2097435 5309297 := bstep (se 2 (by rfl) ⟨1990986, by rfl⟩ : syracuseStep 5309297 = 3981973) B3981973
theorem B3539531 : Blo 2097435 3539531 := bstep (se 1 (by rfl) ⟨2654648, by rfl⟩ : syracuseStep 3539531 = 5309297) B5309297
theorem B2359687 : Blo 2097435 2359687 := bstep (se 1 (by rfl) ⟨1769765, by rfl⟩ : syracuseStep 2359687 = 3539531) B3539531
theorem B3146249 : Blo 2097435 3146249 := bstep (se 2 (by rfl) ⟨1179843, by rfl⟩ : syracuseStep 3146249 = 2359687) B2359687
theorem B2097499 : Blo 2097435 2097499 := bstep (se 1 (by rfl) ⟨1573124, by rfl⟩ : syracuseStep 2097499 = 3146249) B3146249
theorem B10618613 : Blo 2097435 10618613 := bbase (se 5 (by rfl) ⟨497747, by rfl⟩ : syracuseStep 10618613 = 995495) (by norm_num)
theorem B7079075 : Blo 2097435 7079075 := bstep (se 1 (by rfl) ⟨5309306, by rfl⟩ : syracuseStep 7079075 = 10618613) B10618613
theorem B4719383 : Blo 2097435 4719383 := bstep (se 1 (by rfl) ⟨3539537, by rfl⟩ : syracuseStep 4719383 = 7079075) B7079075
theorem B3146255 : Blo 2097435 3146255 := bstep (se 1 (by rfl) ⟨2359691, by rfl⟩ : syracuseStep 3146255 = 4719383) B4719383
theorem B2097503 : Blo 2097435 2097503 := bstep (se 1 (by rfl) ⟨1573127, by rfl⟩ : syracuseStep 2097503 = 3146255) B3146255
theorem B3146261 : Blo 2097435 3146261 := bbase (se 6 (by rfl) ⟨73740, by rfl⟩ : syracuseStep 3146261 = 147481) (by norm_num)
theorem B2097507 : Blo 2097435 2097507 := bstep (se 1 (by rfl) ⟨1573130, by rfl⟩ : syracuseStep 2097507 = 3146261) B3146261
theorem B2519857 : Blo 2097435 2519857 := bbase (se 2 (by rfl) ⟨944946, by rfl⟩ : syracuseStep 2519857 = 1889893) (by norm_num)
theorem B3359809 : Blo 2097435 3359809 := bstep (se 2 (by rfl) ⟨1259928, by rfl⟩ : syracuseStep 3359809 = 2519857) B2519857
theorem B17918981 : Blo 2097435 17918981 := bstep (se 4 (by rfl) ⟨1679904, by rfl⟩ : syracuseStep 17918981 = 3359809) B3359809
theorem B11945987 : Blo 2097435 11945987 := bstep (se 1 (by rfl) ⟨8959490, by rfl⟩ : syracuseStep 11945987 = 17918981) B17918981
theorem B7963991 : Blo 2097435 7963991 := bstep (se 1 (by rfl) ⟨5972993, by rfl⟩ : syracuseStep 7963991 = 11945987) B11945987
theorem B5309327 : Blo 2097435 5309327 := bstep (se 1 (by rfl) ⟨3981995, by rfl⟩ : syracuseStep 5309327 = 7963991) B7963991
theorem B3539551 : Blo 2097435 3539551 := bstep (se 1 (by rfl) ⟨2654663, by rfl⟩ : syracuseStep 3539551 = 5309327) B5309327
theorem B4719401 : Blo 2097435 4719401 := bstep (se 2 (by rfl) ⟨1769775, by rfl⟩ : syracuseStep 4719401 = 3539551) B3539551
theorem B3146267 : Blo 2097435 3146267 := bstep (se 1 (by rfl) ⟨2359700, by rfl⟩ : syracuseStep 3146267 = 4719401) B4719401
theorem B2097511 : Blo 2097435 2097511 := bstep (se 1 (by rfl) ⟨1573133, by rfl⟩ : syracuseStep 2097511 = 3146267) B3146267
theorem B2359705 : Blo 2097435 2359705 := bbase (se 2 (by rfl) ⟨884889, by rfl⟩ : syracuseStep 2359705 = 1769779) (by norm_num)
theorem B3146273 : Blo 2097435 3146273 := bstep (se 2 (by rfl) ⟨1179852, by rfl⟩ : syracuseStep 3146273 = 2359705) B2359705
theorem B2097515 : Blo 2097435 2097515 := bstep (se 1 (by rfl) ⟨1573136, by rfl⟩ : syracuseStep 2097515 = 3146273) B3146273
theorem B7964021 : Blo 2097435 7964021 := bbase (se 5 (by rfl) ⟨373313, by rfl⟩ : syracuseStep 7964021 = 746627) (by norm_num)
theorem B5309347 : Blo 2097435 5309347 := bstep (se 1 (by rfl) ⟨3982010, by rfl⟩ : syracuseStep 5309347 = 7964021) B7964021
theorem B7079129 : Blo 2097435 7079129 := bstep (se 2 (by rfl) ⟨2654673, by rfl⟩ : syracuseStep 7079129 = 5309347) B5309347
theorem B4719419 : Blo 2097435 4719419 := bstep (se 1 (by rfl) ⟨3539564, by rfl⟩ : syracuseStep 4719419 = 7079129) B7079129
theorem B3146279 : Blo 2097435 3146279 := bstep (se 1 (by rfl) ⟨2359709, by rfl⟩ : syracuseStep 3146279 = 4719419) B4719419
theorem B2097519 : Blo 2097435 2097519 := bstep (se 1 (by rfl) ⟨1573139, by rfl⟩ : syracuseStep 2097519 = 3146279) B3146279
theorem B3146285 : Blo 2097435 3146285 := bbase (se 3 (by rfl) ⟨589928, by rfl⟩ : syracuseStep 3146285 = 1179857) (by norm_num)
theorem B2097523 : Blo 2097435 2097523 := bstep (se 1 (by rfl) ⟨1573142, by rfl⟩ : syracuseStep 2097523 = 3146285) B3146285
theorem B4719437 : Blo 2097435 4719437 := bbase (se 3 (by rfl) ⟨884894, by rfl⟩ : syracuseStep 4719437 = 1769789) (by norm_num)
theorem B3146291 : Blo 2097435 3146291 := bstep (se 1 (by rfl) ⟨2359718, by rfl⟩ : syracuseStep 3146291 = 4719437) B4719437
theorem B2097527 : Blo 2097435 2097527 := bstep (se 1 (by rfl) ⟨1573145, by rfl⟩ : syracuseStep 2097527 = 3146291) B3146291
theorem B2654689 : Blo 2097435 2654689 := bbase (se 2 (by rfl) ⟨995508, by rfl⟩ : syracuseStep 2654689 = 1991017) (by norm_num)
theorem B3539585 : Blo 2097435 3539585 := bstep (se 2 (by rfl) ⟨1327344, by rfl⟩ : syracuseStep 3539585 = 2654689) B2654689
theorem B2359723 : Blo 2097435 2359723 := bstep (se 1 (by rfl) ⟨1769792, by rfl⟩ : syracuseStep 2359723 = 3539585) B3539585
theorem B3146297 : Blo 2097435 3146297 := bstep (se 2 (by rfl) ⟨1179861, by rfl⟩ : syracuseStep 3146297 = 2359723) B2359723
theorem B2097531 : Blo 2097435 2097531 := bstep (se 1 (by rfl) ⟨1573148, by rfl⟩ : syracuseStep 2097531 = 3146297) B3146297
theorem B23892245 : Blo 2097435 23892245 := bbase (se 6 (by rfl) ⟨559974, by rfl⟩ : syracuseStep 23892245 = 1119949) (by norm_num)
theorem B15928163 : Blo 2097435 15928163 := bstep (se 1 (by rfl) ⟨11946122, by rfl⟩ : syracuseStep 15928163 = 23892245) B23892245
theorem B10618775 : Blo 2097435 10618775 := bstep (se 1 (by rfl) ⟨7964081, by rfl⟩ : syracuseStep 10618775 = 15928163) B15928163
theorem B7079183 : Blo 2097435 7079183 := bstep (se 1 (by rfl) ⟨5309387, by rfl⟩ : syracuseStep 7079183 = 10618775) B10618775
theorem B4719455 : Blo 2097435 4719455 := bstep (se 1 (by rfl) ⟨3539591, by rfl⟩ : syracuseStep 4719455 = 7079183) B7079183
theorem B3146303 : Blo 2097435 3146303 := bstep (se 1 (by rfl) ⟨2359727, by rfl⟩ : syracuseStep 3146303 = 4719455) B4719455
theorem B2097535 : Blo 2097435 2097535 := bstep (se 1 (by rfl) ⟨1573151, by rfl⟩ : syracuseStep 2097535 = 3146303) B3146303
theorem B3146309 : Blo 2097435 3146309 := bbase (se 4 (by rfl) ⟨294966, by rfl⟩ : syracuseStep 3146309 = 589933) (by norm_num)
theorem B2097539 : Blo 2097435 2097539 := bstep (se 1 (by rfl) ⟨1573154, by rfl⟩ : syracuseStep 2097539 = 3146309) B3146309
theorem B3539605 : Blo 2097435 3539605 := bbase (se 6 (by rfl) ⟨82959, by rfl⟩ : syracuseStep 3539605 = 165919) (by norm_num)
theorem B4719473 : Blo 2097435 4719473 := bstep (se 2 (by rfl) ⟨1769802, by rfl⟩ : syracuseStep 4719473 = 3539605) B3539605
theorem B3146315 : Blo 2097435 3146315 := bstep (se 1 (by rfl) ⟨2359736, by rfl⟩ : syracuseStep 3146315 = 4719473) B4719473
theorem B2097543 : Blo 2097435 2097543 := bstep (se 1 (by rfl) ⟨1573157, by rfl⟩ : syracuseStep 2097543 = 3146315) B3146315
theorem B2359741 : Blo 2097435 2359741 := bbase (se 3 (by rfl) ⟨442451, by rfl⟩ : syracuseStep 2359741 = 884903) (by norm_num)
theorem B3146321 : Blo 2097435 3146321 := bstep (se 2 (by rfl) ⟨1179870, by rfl⟩ : syracuseStep 3146321 = 2359741) B2359741
theorem B2097547 : Blo 2097435 2097547 := bstep (se 1 (by rfl) ⟨1573160, by rfl⟩ : syracuseStep 2097547 = 3146321) B3146321
theorem B7079237 : Blo 2097435 7079237 := bbase (se 4 (by rfl) ⟨663678, by rfl⟩ : syracuseStep 7079237 = 1327357) (by norm_num)
theorem B4719491 : Blo 2097435 4719491 := bstep (se 1 (by rfl) ⟨3539618, by rfl⟩ : syracuseStep 4719491 = 7079237) B7079237
theorem B3146327 : Blo 2097435 3146327 := bstep (se 1 (by rfl) ⟨2359745, by rfl⟩ : syracuseStep 3146327 = 4719491) B4719491
theorem B2097551 : Blo 2097435 2097551 := bstep (se 1 (by rfl) ⟨1573163, by rfl⟩ : syracuseStep 2097551 = 3146327) B3146327
theorem B3146333 : Blo 2097435 3146333 := bbase (se 3 (by rfl) ⟨589937, by rfl⟩ : syracuseStep 3146333 = 1179875) (by norm_num)
theorem B2097555 : Blo 2097435 2097555 := bstep (se 1 (by rfl) ⟨1573166, by rfl⟩ : syracuseStep 2097555 = 3146333) B3146333
theorem B4719509 : Blo 2097435 4719509 := bbase (se 6 (by rfl) ⟨110613, by rfl⟩ : syracuseStep 4719509 = 221227) (by norm_num)
theorem B3146339 : Blo 2097435 3146339 := bstep (se 1 (by rfl) ⟨2359754, by rfl⟩ : syracuseStep 3146339 = 4719509) B4719509
theorem B2097559 : Blo 2097435 2097559 := bstep (se 1 (by rfl) ⟨1573169, by rfl⟩ : syracuseStep 2097559 = 3146339) B3146339
theorem B3359893 : Blo 2097435 3359893 := bbase (se 6 (by rfl) ⟨78747, by rfl⟩ : syracuseStep 3359893 = 157495) (by norm_num)
theorem B4479857 : Blo 2097435 4479857 := bstep (se 2 (by rfl) ⟨1679946, by rfl⟩ : syracuseStep 4479857 = 3359893) B3359893
theorem B2986571 : Blo 2097435 2986571 := bstep (se 1 (by rfl) ⟨2239928, by rfl⟩ : syracuseStep 2986571 = 4479857) B4479857
theorem B7964189 : Blo 2097435 7964189 := bstep (se 3 (by rfl) ⟨1493285, by rfl⟩ : syracuseStep 7964189 = 2986571) B2986571
theorem B5309459 : Blo 2097435 5309459 := bstep (se 1 (by rfl) ⟨3982094, by rfl⟩ : syracuseStep 5309459 = 7964189) B7964189
theorem B3539639 : Blo 2097435 3539639 := bstep (se 1 (by rfl) ⟨2654729, by rfl⟩ : syracuseStep 3539639 = 5309459) B5309459
theorem B2359759 : Blo 2097435 2359759 := bstep (se 1 (by rfl) ⟨1769819, by rfl⟩ : syracuseStep 2359759 = 3539639) B3539639
theorem B3146345 : Blo 2097435 3146345 := bstep (se 2 (by rfl) ⟨1179879, by rfl⟩ : syracuseStep 3146345 = 2359759) B2359759
theorem B2097563 : Blo 2097435 2097563 := bstep (se 1 (by rfl) ⟨1573172, by rfl⟩ : syracuseStep 2097563 = 3146345) B3146345
theorem B6719797 : Blo 2097435 6719797 := bbase (se 5 (by rfl) ⟨314990, by rfl⟩ : syracuseStep 6719797 = 629981) (by norm_num)
theorem B8959729 : Blo 2097435 8959729 := bstep (se 2 (by rfl) ⟨3359898, by rfl⟩ : syracuseStep 8959729 = 6719797) B6719797
theorem B11946305 : Blo 2097435 11946305 := bstep (se 2 (by rfl) ⟨4479864, by rfl⟩ : syracuseStep 11946305 = 8959729) B8959729
theorem B7964203 : Blo 2097435 7964203 := bstep (se 1 (by rfl) ⟨5973152, by rfl⟩ : syracuseStep 7964203 = 11946305) B11946305
theorem B10618937 : Blo 2097435 10618937 := bstep (se 2 (by rfl) ⟨3982101, by rfl⟩ : syracuseStep 10618937 = 7964203) B7964203
theorem B7079291 : Blo 2097435 7079291 := bstep (se 1 (by rfl) ⟨5309468, by rfl⟩ : syracuseStep 7079291 = 10618937) B10618937
theorem B4719527 : Blo 2097435 4719527 := bstep (se 1 (by rfl) ⟨3539645, by rfl⟩ : syracuseStep 4719527 = 7079291) B7079291
theorem B3146351 : Blo 2097435 3146351 := bstep (se 1 (by rfl) ⟨2359763, by rfl⟩ : syracuseStep 3146351 = 4719527) B4719527
theorem B2097567 : Blo 2097435 2097567 := bstep (se 1 (by rfl) ⟨1573175, by rfl⟩ : syracuseStep 2097567 = 3146351) B3146351
theorem B3146357 : Blo 2097435 3146357 := bbase (se 5 (by rfl) ⟨147485, by rfl⟩ : syracuseStep 3146357 = 294971) (by norm_num)
theorem B2097571 : Blo 2097435 2097571 := bstep (se 1 (by rfl) ⟨1573178, by rfl⟩ : syracuseStep 2097571 = 3146357) B3146357
theorem B3982117 : Blo 2097435 3982117 := bbase (se 4 (by rfl) ⟨373323, by rfl⟩ : syracuseStep 3982117 = 746647) (by norm_num)
theorem B5309489 : Blo 2097435 5309489 := bstep (se 2 (by rfl) ⟨1991058, by rfl⟩ : syracuseStep 5309489 = 3982117) B3982117
theorem B3539659 : Blo 2097435 3539659 := bstep (se 1 (by rfl) ⟨2654744, by rfl⟩ : syracuseStep 3539659 = 5309489) B5309489
theorem B4719545 : Blo 2097435 4719545 := bstep (se 2 (by rfl) ⟨1769829, by rfl⟩ : syracuseStep 4719545 = 3539659) B3539659
theorem B3146363 : Blo 2097435 3146363 := bstep (se 1 (by rfl) ⟨2359772, by rfl⟩ : syracuseStep 3146363 = 4719545) B4719545
theorem B2097575 : Blo 2097435 2097575 := bstep (se 1 (by rfl) ⟨1573181, by rfl⟩ : syracuseStep 2097575 = 3146363) B3146363
theorem B2359777 : Blo 2097435 2359777 := bbase (se 2 (by rfl) ⟨884916, by rfl⟩ : syracuseStep 2359777 = 1769833) (by norm_num)
theorem B3146369 : Blo 2097435 3146369 := bstep (se 2 (by rfl) ⟨1179888, by rfl⟩ : syracuseStep 3146369 = 2359777) B2359777
theorem B2097579 : Blo 2097435 2097579 := bstep (se 1 (by rfl) ⟨1573184, by rfl⟩ : syracuseStep 2097579 = 3146369) B3146369
theorem B5309509 : Blo 2097435 5309509 := bbase (se 4 (by rfl) ⟨497766, by rfl⟩ : syracuseStep 5309509 = 995533) (by norm_num)
theorem B7079345 : Blo 2097435 7079345 := bstep (se 2 (by rfl) ⟨2654754, by rfl⟩ : syracuseStep 7079345 = 5309509) B5309509
theorem B4719563 : Blo 2097435 4719563 := bstep (se 1 (by rfl) ⟨3539672, by rfl⟩ : syracuseStep 4719563 = 7079345) B7079345
theorem B3146375 : Blo 2097435 3146375 := bstep (se 1 (by rfl) ⟨2359781, by rfl⟩ : syracuseStep 3146375 = 4719563) B4719563
theorem B2097583 : Blo 2097435 2097583 := bstep (se 1 (by rfl) ⟨1573187, by rfl⟩ : syracuseStep 2097583 = 3146375) B3146375
theorem B3146381 : Blo 2097435 3146381 := bbase (se 3 (by rfl) ⟨589946, by rfl⟩ : syracuseStep 3146381 = 1179893) (by norm_num)
theorem B2097587 : Blo 2097435 2097587 := bstep (se 1 (by rfl) ⟨1573190, by rfl⟩ : syracuseStep 2097587 = 3146381) B3146381
theorem B4719581 : Blo 2097435 4719581 := bbase (se 3 (by rfl) ⟨884921, by rfl⟩ : syracuseStep 4719581 = 1769843) (by norm_num)
theorem B3146387 : Blo 2097435 3146387 := bstep (se 1 (by rfl) ⟨2359790, by rfl⟩ : syracuseStep 3146387 = 4719581) B4719581
theorem B2097591 : Blo 2097435 2097591 := bstep (se 1 (by rfl) ⟨1573193, by rfl⟩ : syracuseStep 2097591 = 3146387) B3146387
theorem B3539693 : Blo 2097435 3539693 := bbase (se 3 (by rfl) ⟨663692, by rfl⟩ : syracuseStep 3539693 = 1327385) (by norm_num)
theorem B2359795 : Blo 2097435 2359795 := bstep (se 1 (by rfl) ⟨1769846, by rfl⟩ : syracuseStep 2359795 = 3539693) B3539693
theorem B3146393 : Blo 2097435 3146393 := bstep (se 2 (by rfl) ⟨1179897, by rfl⟩ : syracuseStep 3146393 = 2359795) B2359795
theorem B2097595 : Blo 2097435 2097595 := bstep (se 1 (by rfl) ⟨1573196, by rfl⟩ : syracuseStep 2097595 = 3146393) B3146393
theorem B5455421 : Blo 2097435 5455421 := bbase (se 3 (by rfl) ⟨1022891, by rfl⟩ : syracuseStep 5455421 = 2045783) (by norm_num)
theorem B3636947 : Blo 2097435 3636947 := bstep (se 1 (by rfl) ⟨2727710, by rfl⟩ : syracuseStep 3636947 = 5455421) B5455421
theorem B2424631 : Blo 2097435 2424631 := bstep (se 1 (by rfl) ⟨1818473, by rfl⟩ : syracuseStep 2424631 = 3636947) B3636947
theorem B3232841 : Blo 2097435 3232841 := bstep (se 2 (by rfl) ⟨1212315, by rfl⟩ : syracuseStep 3232841 = 2424631) B2424631
theorem B34483637 : Blo 2097435 34483637 := bstep (se 5 (by rfl) ⟨1616420, by rfl⟩ : syracuseStep 34483637 = 3232841) B3232841
theorem B22989091 : Blo 2097435 22989091 := bstep (se 1 (by rfl) ⟨17241818, by rfl⟩ : syracuseStep 22989091 = 34483637) B34483637
theorem B30652121 : Blo 2097435 30652121 := bstep (se 2 (by rfl) ⟨11494545, by rfl⟩ : syracuseStep 30652121 = 22989091) B22989091
theorem B81738989 : Blo 2097435 81738989 := bstep (se 3 (by rfl) ⟨15326060, by rfl⟩ : syracuseStep 81738989 = 30652121) B30652121
theorem B54492659 : Blo 2097435 54492659 := bstep (se 1 (by rfl) ⟨40869494, by rfl⟩ : syracuseStep 54492659 = 81738989) B81738989
theorem B36328439 : Blo 2097435 36328439 := bstep (se 1 (by rfl) ⟨27246329, by rfl⟩ : syracuseStep 36328439 = 54492659) B54492659
theorem B24218959 : Blo 2097435 24218959 := bstep (se 1 (by rfl) ⟨18164219, by rfl⟩ : syracuseStep 24218959 = 36328439) B36328439
theorem B32291945 : Blo 2097435 32291945 := bstep (se 2 (by rfl) ⟨12109479, by rfl⟩ : syracuseStep 32291945 = 24218959) B24218959
theorem B21527963 : Blo 2097435 21527963 := bstep (se 1 (by rfl) ⟨16145972, by rfl⟩ : syracuseStep 21527963 = 32291945) B32291945
theorem B14351975 : Blo 2097435 14351975 := bstep (se 1 (by rfl) ⟨10763981, by rfl⟩ : syracuseStep 14351975 = 21527963) B21527963
theorem B9567983 : Blo 2097435 9567983 := bstep (se 1 (by rfl) ⟨7175987, by rfl⟩ : syracuseStep 9567983 = 14351975) B14351975
theorem B25514621 : Blo 2097435 25514621 := bstep (se 3 (by rfl) ⟨4783991, by rfl⟩ : syracuseStep 25514621 = 9567983) B9567983
theorem B17009747 : Blo 2097435 17009747 := bstep (se 1 (by rfl) ⟨12757310, by rfl⟩ : syracuseStep 17009747 = 25514621) B25514621
theorem B11339831 : Blo 2097435 11339831 := bstep (se 1 (by rfl) ⟨8504873, by rfl⟩ : syracuseStep 11339831 = 17009747) B17009747
theorem B7559887 : Blo 2097435 7559887 := bstep (se 1 (by rfl) ⟨5669915, by rfl⟩ : syracuseStep 7559887 = 11339831) B11339831
theorem B10079849 : Blo 2097435 10079849 := bstep (se 2 (by rfl) ⟨3779943, by rfl⟩ : syracuseStep 10079849 = 7559887) B7559887
theorem B26879597 : Blo 2097435 26879597 := bstep (se 3 (by rfl) ⟨5039924, by rfl⟩ : syracuseStep 26879597 = 10079849) B10079849
theorem B17919731 : Blo 2097435 17919731 := bstep (se 1 (by rfl) ⟨13439798, by rfl⟩ : syracuseStep 17919731 = 26879597) B26879597
theorem B11946487 : Blo 2097435 11946487 := bstep (se 1 (by rfl) ⟨8959865, by rfl⟩ : syracuseStep 11946487 = 17919731) B17919731
theorem B15928649 : Blo 2097435 15928649 := bstep (se 2 (by rfl) ⟨5973243, by rfl⟩ : syracuseStep 15928649 = 11946487) B11946487
theorem B10619099 : Blo 2097435 10619099 := bstep (se 1 (by rfl) ⟨7964324, by rfl⟩ : syracuseStep 10619099 = 15928649) B15928649
theorem B7079399 : Blo 2097435 7079399 := bstep (se 1 (by rfl) ⟨5309549, by rfl⟩ : syracuseStep 7079399 = 10619099) B10619099
theorem B4719599 : Blo 2097435 4719599 := bstep (se 1 (by rfl) ⟨3539699, by rfl⟩ : syracuseStep 4719599 = 7079399) B7079399
theorem B3146399 : Blo 2097435 3146399 := bstep (se 1 (by rfl) ⟨2359799, by rfl⟩ : syracuseStep 3146399 = 4719599) B4719599
theorem B2097599 : Blo 2097435 2097599 := bstep (se 1 (by rfl) ⟨1573199, by rfl⟩ : syracuseStep 2097599 = 3146399) B3146399
theorem B3146405 : Blo 2097435 3146405 := bbase (se 4 (by rfl) ⟨294975, by rfl⟩ : syracuseStep 3146405 = 589951) (by norm_num)
theorem B2097603 : Blo 2097435 2097603 := bstep (se 1 (by rfl) ⟨1573202, by rfl⟩ : syracuseStep 2097603 = 3146405) B3146405
theorem B2654785 : Blo 2097435 2654785 := bbase (se 2 (by rfl) ⟨995544, by rfl⟩ : syracuseStep 2654785 = 1991089) (by norm_num)
theorem B3539713 : Blo 2097435 3539713 := bstep (se 2 (by rfl) ⟨1327392, by rfl⟩ : syracuseStep 3539713 = 2654785) B2654785
theorem B4719617 : Blo 2097435 4719617 := bstep (se 2 (by rfl) ⟨1769856, by rfl⟩ : syracuseStep 4719617 = 3539713) B3539713
theorem B3146411 : Blo 2097435 3146411 := bstep (se 1 (by rfl) ⟨2359808, by rfl⟩ : syracuseStep 3146411 = 4719617) B4719617
theorem B2097607 : Blo 2097435 2097607 := bstep (se 1 (by rfl) ⟨1573205, by rfl⟩ : syracuseStep 2097607 = 3146411) B3146411
theorem B2359813 : Blo 2097435 2359813 := bbase (se 4 (by rfl) ⟨221232, by rfl⟩ : syracuseStep 2359813 = 442465) (by norm_num)
theorem B3146417 : Blo 2097435 3146417 := bstep (se 2 (by rfl) ⟨1179906, by rfl⟩ : syracuseStep 3146417 = 2359813) B2359813
theorem B2097611 : Blo 2097435 2097611 := bstep (se 1 (by rfl) ⟨1573208, by rfl⟩ : syracuseStep 2097611 = 3146417) B3146417
theorem B2986645 : Blo 2097435 2986645 := bbase (se 6 (by rfl) ⟨69999, by rfl⟩ : syracuseStep 2986645 = 139999) (by norm_num)
theorem B3982193 : Blo 2097435 3982193 := bstep (se 2 (by rfl) ⟨1493322, by rfl⟩ : syracuseStep 3982193 = 2986645) B2986645
theorem B2654795 : Blo 2097435 2654795 := bstep (se 1 (by rfl) ⟨1991096, by rfl⟩ : syracuseStep 2654795 = 3982193) B3982193
theorem B7079453 : Blo 2097435 7079453 := bstep (se 3 (by rfl) ⟨1327397, by rfl⟩ : syracuseStep 7079453 = 2654795) B2654795
theorem B4719635 : Blo 2097435 4719635 := bstep (se 1 (by rfl) ⟨3539726, by rfl⟩ : syracuseStep 4719635 = 7079453) B7079453
theorem B3146423 : Blo 2097435 3146423 := bstep (se 1 (by rfl) ⟨2359817, by rfl⟩ : syracuseStep 3146423 = 4719635) B4719635
theorem B2097615 : Blo 2097435 2097615 := bstep (se 1 (by rfl) ⟨1573211, by rfl⟩ : syracuseStep 2097615 = 3146423) B3146423
theorem B3146429 : Blo 2097435 3146429 := bbase (se 3 (by rfl) ⟨589955, by rfl⟩ : syracuseStep 3146429 = 1179911) (by norm_num)
theorem B2097619 : Blo 2097435 2097619 := bstep (se 1 (by rfl) ⟨1573214, by rfl⟩ : syracuseStep 2097619 = 3146429) B3146429
theorem B4719653 : Blo 2097435 4719653 := bbase (se 4 (by rfl) ⟨442467, by rfl⟩ : syracuseStep 4719653 = 884935) (by norm_num)
theorem B3146435 : Blo 2097435 3146435 := bstep (se 1 (by rfl) ⟨2359826, by rfl⟩ : syracuseStep 3146435 = 4719653) B4719653
theorem B2097623 : Blo 2097435 2097623 := bstep (se 1 (by rfl) ⟨1573217, by rfl⟩ : syracuseStep 2097623 = 3146435) B3146435
theorem B5309621 : Blo 2097435 5309621 := bbase (se 5 (by rfl) ⟨248888, by rfl⟩ : syracuseStep 5309621 = 497777) (by norm_num)
theorem B3539747 : Blo 2097435 3539747 := bstep (se 1 (by rfl) ⟨2654810, by rfl⟩ : syracuseStep 3539747 = 5309621) B5309621
theorem B2359831 : Blo 2097435 2359831 := bstep (se 1 (by rfl) ⟨1769873, by rfl⟩ : syracuseStep 2359831 = 3539747) B3539747
theorem B3146441 : Blo 2097435 3146441 := bstep (se 2 (by rfl) ⟨1179915, by rfl⟩ : syracuseStep 3146441 = 2359831) B2359831
theorem B2097627 : Blo 2097435 2097627 := bstep (se 1 (by rfl) ⟨1573220, by rfl⟩ : syracuseStep 2097627 = 3146441) B3146441
theorem B2520001 : Blo 2097435 2520001 := bbase (se 2 (by rfl) ⟨945000, by rfl⟩ : syracuseStep 2520001 = 1890001) (by norm_num)
theorem B13440005 : Blo 2097435 13440005 := bstep (se 4 (by rfl) ⟨1260000, by rfl⟩ : syracuseStep 13440005 = 2520001) B2520001
theorem B8960003 : Blo 2097435 8960003 := bstep (se 1 (by rfl) ⟨6720002, by rfl⟩ : syracuseStep 8960003 = 13440005) B13440005
theorem B5973335 : Blo 2097435 5973335 := bstep (se 1 (by rfl) ⟨4480001, by rfl⟩ : syracuseStep 5973335 = 8960003) B8960003
theorem B3982223 : Blo 2097435 3982223 := bstep (se 1 (by rfl) ⟨2986667, by rfl⟩ : syracuseStep 3982223 = 5973335) B5973335
theorem B10619261 : Blo 2097435 10619261 := bstep (se 3 (by rfl) ⟨1991111, by rfl⟩ : syracuseStep 10619261 = 3982223) B3982223
theorem B7079507 : Blo 2097435 7079507 := bstep (se 1 (by rfl) ⟨5309630, by rfl⟩ : syracuseStep 7079507 = 10619261) B10619261
theorem B4719671 : Blo 2097435 4719671 := bstep (se 1 (by rfl) ⟨3539753, by rfl⟩ : syracuseStep 4719671 = 7079507) B7079507
theorem B3146447 : Blo 2097435 3146447 := bstep (se 1 (by rfl) ⟨2359835, by rfl⟩ : syracuseStep 3146447 = 4719671) B4719671
theorem B2097631 : Blo 2097435 2097631 := bstep (se 1 (by rfl) ⟨1573223, by rfl⟩ : syracuseStep 2097631 = 3146447) B3146447
theorem B3146453 : Blo 2097435 3146453 := bbase (se 7 (by rfl) ⟨36872, by rfl⟩ : syracuseStep 3146453 = 73745) (by norm_num)
theorem B2097635 : Blo 2097435 2097635 := bstep (se 1 (by rfl) ⟨1573226, by rfl⟩ : syracuseStep 2097635 = 3146453) B3146453
theorem B2835013 : Blo 2097435 2835013 := bbase (se 4 (by rfl) ⟨265782, by rfl⟩ : syracuseStep 2835013 = 531565) (by norm_num)
theorem B3780017 : Blo 2097435 3780017 := bstep (se 2 (by rfl) ⟨1417506, by rfl⟩ : syracuseStep 3780017 = 2835013) B2835013
theorem B2520011 : Blo 2097435 2520011 := bstep (se 1 (by rfl) ⟨1890008, by rfl⟩ : syracuseStep 2520011 = 3780017) B3780017
theorem B6720029 : Blo 2097435 6720029 := bstep (se 3 (by rfl) ⟨1260005, by rfl⟩ : syracuseStep 6720029 = 2520011) B2520011
theorem B4480019 : Blo 2097435 4480019 := bstep (se 1 (by rfl) ⟨3360014, by rfl⟩ : syracuseStep 4480019 = 6720029) B6720029
theorem B2986679 : Blo 2097435 2986679 := bstep (se 1 (by rfl) ⟨2240009, by rfl⟩ : syracuseStep 2986679 = 4480019) B4480019
theorem B7964477 : Blo 2097435 7964477 := bstep (se 3 (by rfl) ⟨1493339, by rfl⟩ : syracuseStep 7964477 = 2986679) B2986679
theorem B5309651 : Blo 2097435 5309651 := bstep (se 1 (by rfl) ⟨3982238, by rfl⟩ : syracuseStep 5309651 = 7964477) B7964477
theorem B3539767 : Blo 2097435 3539767 := bstep (se 1 (by rfl) ⟨2654825, by rfl⟩ : syracuseStep 3539767 = 5309651) B5309651
theorem B4719689 : Blo 2097435 4719689 := bstep (se 2 (by rfl) ⟨1769883, by rfl⟩ : syracuseStep 4719689 = 3539767) B3539767
theorem B3146459 : Blo 2097435 3146459 := bstep (se 1 (by rfl) ⟨2359844, by rfl⟩ : syracuseStep 3146459 = 4719689) B4719689
theorem B2097639 : Blo 2097435 2097639 := bstep (se 1 (by rfl) ⟨1573229, by rfl⟩ : syracuseStep 2097639 = 3146459) B3146459
theorem B2359849 : Blo 2097435 2359849 := bbase (se 2 (by rfl) ⟨884943, by rfl⟩ : syracuseStep 2359849 = 1769887) (by norm_num)
theorem B3146465 : Blo 2097435 3146465 := bstep (se 2 (by rfl) ⟨1179924, by rfl⟩ : syracuseStep 3146465 = 2359849) B2359849
theorem B2097643 : Blo 2097435 2097643 := bstep (se 1 (by rfl) ⟨1573232, by rfl⟩ : syracuseStep 2097643 = 3146465) B3146465
theorem B19136405 : Blo 2097435 19136405 := bbase (se 6 (by rfl) ⟨448509, by rfl⟩ : syracuseStep 19136405 = 897019) (by norm_num)
theorem B12757603 : Blo 2097435 12757603 := bstep (se 1 (by rfl) ⟨9568202, by rfl⟩ : syracuseStep 12757603 = 19136405) B19136405
theorem B17010137 : Blo 2097435 17010137 := bstep (se 2 (by rfl) ⟨6378801, by rfl⟩ : syracuseStep 17010137 = 12757603) B12757603
theorem B11340091 : Blo 2097435 11340091 := bstep (se 1 (by rfl) ⟨8505068, by rfl⟩ : syracuseStep 11340091 = 17010137) B17010137
theorem B15120121 : Blo 2097435 15120121 := bstep (se 2 (by rfl) ⟨5670045, by rfl⟩ : syracuseStep 15120121 = 11340091) B11340091
theorem B20160161 : Blo 2097435 20160161 := bstep (se 2 (by rfl) ⟨7560060, by rfl⟩ : syracuseStep 20160161 = 15120121) B15120121
theorem B13440107 : Blo 2097435 13440107 := bstep (se 1 (by rfl) ⟨10080080, by rfl⟩ : syracuseStep 13440107 = 20160161) B20160161
theorem B8960071 : Blo 2097435 8960071 := bstep (se 1 (by rfl) ⟨6720053, by rfl⟩ : syracuseStep 8960071 = 13440107) B13440107
theorem B11946761 : Blo 2097435 11946761 := bstep (se 2 (by rfl) ⟨4480035, by rfl⟩ : syracuseStep 11946761 = 8960071) B8960071
theorem B7964507 : Blo 2097435 7964507 := bstep (se 1 (by rfl) ⟨5973380, by rfl⟩ : syracuseStep 7964507 = 11946761) B11946761
theorem B5309671 : Blo 2097435 5309671 := bstep (se 1 (by rfl) ⟨3982253, by rfl⟩ : syracuseStep 5309671 = 7964507) B7964507
theorem B7079561 : Blo 2097435 7079561 := bstep (se 2 (by rfl) ⟨2654835, by rfl⟩ : syracuseStep 7079561 = 5309671) B5309671
theorem B4719707 : Blo 2097435 4719707 := bstep (se 1 (by rfl) ⟨3539780, by rfl⟩ : syracuseStep 4719707 = 7079561) B7079561
theorem B3146471 : Blo 2097435 3146471 := bstep (se 1 (by rfl) ⟨2359853, by rfl⟩ : syracuseStep 3146471 = 4719707) B4719707
theorem B2097647 : Blo 2097435 2097647 := bstep (se 1 (by rfl) ⟨1573235, by rfl⟩ : syracuseStep 2097647 = 3146471) B3146471
theorem B3146477 : Blo 2097435 3146477 := bbase (se 3 (by rfl) ⟨589964, by rfl⟩ : syracuseStep 3146477 = 1179929) (by norm_num)
theorem B2097651 : Blo 2097435 2097651 := bstep (se 1 (by rfl) ⟨1573238, by rfl⟩ : syracuseStep 2097651 = 3146477) B3146477
theorem B4719725 : Blo 2097435 4719725 := bbase (se 3 (by rfl) ⟨884948, by rfl⟩ : syracuseStep 4719725 = 1769897) (by norm_num)
theorem B3146483 : Blo 2097435 3146483 := bstep (se 1 (by rfl) ⟨2359862, by rfl⟩ : syracuseStep 3146483 = 4719725) B4719725
theorem B2097655 : Blo 2097435 2097655 := bstep (se 1 (by rfl) ⟨1573241, by rfl⟩ : syracuseStep 2097655 = 3146483) B3146483
theorem B3982277 : Blo 2097435 3982277 := bbase (se 4 (by rfl) ⟨373338, by rfl⟩ : syracuseStep 3982277 = 746677) (by norm_num)
theorem B2654851 : Blo 2097435 2654851 := bstep (se 1 (by rfl) ⟨1991138, by rfl⟩ : syracuseStep 2654851 = 3982277) B3982277
theorem B3539801 : Blo 2097435 3539801 := bstep (se 2 (by rfl) ⟨1327425, by rfl⟩ : syracuseStep 3539801 = 2654851) B2654851
theorem B2359867 : Blo 2097435 2359867 := bstep (se 1 (by rfl) ⟨1769900, by rfl⟩ : syracuseStep 2359867 = 3539801) B3539801
theorem B3146489 : Blo 2097435 3146489 := bstep (se 2 (by rfl) ⟨1179933, by rfl⟩ : syracuseStep 3146489 = 2359867) B2359867
theorem B2097659 : Blo 2097435 2097659 := bstep (se 1 (by rfl) ⟨1573244, by rfl⟩ : syracuseStep 2097659 = 3146489) B3146489
theorem B30240469 : Blo 2097435 30240469 := bbase (se 7 (by rfl) ⟨354380, by rfl⟩ : syracuseStep 30240469 = 708761) (by norm_num)
theorem B40320625 : Blo 2097435 40320625 := bstep (se 2 (by rfl) ⟨15120234, by rfl⟩ : syracuseStep 40320625 = 30240469) B30240469
theorem B53760833 : Blo 2097435 53760833 := bstep (se 2 (by rfl) ⟨20160312, by rfl⟩ : syracuseStep 53760833 = 40320625) B40320625
theorem B35840555 : Blo 2097435 35840555 := bstep (se 1 (by rfl) ⟨26880416, by rfl⟩ : syracuseStep 35840555 = 53760833) B53760833
theorem B23893703 : Blo 2097435 23893703 := bstep (se 1 (by rfl) ⟨17920277, by rfl⟩ : syracuseStep 23893703 = 35840555) B35840555
theorem B15929135 : Blo 2097435 15929135 := bstep (se 1 (by rfl) ⟨11946851, by rfl⟩ : syracuseStep 15929135 = 23893703) B23893703
theorem B10619423 : Blo 2097435 10619423 := bstep (se 1 (by rfl) ⟨7964567, by rfl⟩ : syracuseStep 10619423 = 15929135) B15929135
theorem B7079615 : Blo 2097435 7079615 := bstep (se 1 (by rfl) ⟨5309711, by rfl⟩ : syracuseStep 7079615 = 10619423) B10619423
theorem B4719743 : Blo 2097435 4719743 := bstep (se 1 (by rfl) ⟨3539807, by rfl⟩ : syracuseStep 4719743 = 7079615) B7079615
theorem B3146495 : Blo 2097435 3146495 := bstep (se 1 (by rfl) ⟨2359871, by rfl⟩ : syracuseStep 3146495 = 4719743) B4719743
theorem B2097663 : Blo 2097435 2097663 := bstep (se 1 (by rfl) ⟨1573247, by rfl⟩ : syracuseStep 2097663 = 3146495) B3146495
theorem B3146501 : Blo 2097435 3146501 := bbase (se 4 (by rfl) ⟨294984, by rfl⟩ : syracuseStep 3146501 = 589969) (by norm_num)
theorem B2097667 : Blo 2097435 2097667 := bstep (se 1 (by rfl) ⟨1573250, by rfl⟩ : syracuseStep 2097667 = 3146501) B3146501
theorem B3539821 : Blo 2097435 3539821 := bbase (se 3 (by rfl) ⟨663716, by rfl⟩ : syracuseStep 3539821 = 1327433) (by norm_num)
theorem B4719761 : Blo 2097435 4719761 := bstep (se 2 (by rfl) ⟨1769910, by rfl⟩ : syracuseStep 4719761 = 3539821) B3539821
theorem B3146507 : Blo 2097435 3146507 := bstep (se 1 (by rfl) ⟨2359880, by rfl⟩ : syracuseStep 3146507 = 4719761) B4719761
theorem B2097671 : Blo 2097435 2097671 := bstep (se 1 (by rfl) ⟨1573253, by rfl⟩ : syracuseStep 2097671 = 3146507) B3146507
theorem B2359885 : Blo 2097435 2359885 := bbase (se 3 (by rfl) ⟨442478, by rfl⟩ : syracuseStep 2359885 = 884957) (by norm_num)
theorem B3146513 : Blo 2097435 3146513 := bstep (se 2 (by rfl) ⟨1179942, by rfl⟩ : syracuseStep 3146513 = 2359885) B2359885
theorem B2097675 : Blo 2097435 2097675 := bstep (se 1 (by rfl) ⟨1573256, by rfl⟩ : syracuseStep 2097675 = 3146513) B3146513
theorem B7079669 : Blo 2097435 7079669 := bbase (se 5 (by rfl) ⟨331859, by rfl⟩ : syracuseStep 7079669 = 663719) (by norm_num)
theorem B4719779 : Blo 2097435 4719779 := bstep (se 1 (by rfl) ⟨3539834, by rfl⟩ : syracuseStep 4719779 = 7079669) B7079669
theorem B3146519 : Blo 2097435 3146519 := bstep (se 1 (by rfl) ⟨2359889, by rfl⟩ : syracuseStep 3146519 = 4719779) B4719779
theorem B2097679 : Blo 2097435 2097679 := bstep (se 1 (by rfl) ⟨1573259, by rfl⟩ : syracuseStep 2097679 = 3146519) B3146519
theorem B3146525 : Blo 2097435 3146525 := bbase (se 3 (by rfl) ⟨589973, by rfl⟩ : syracuseStep 3146525 = 1179947) (by norm_num)
theorem B2097683 : Blo 2097435 2097683 := bstep (se 1 (by rfl) ⟨1573262, by rfl⟩ : syracuseStep 2097683 = 3146525) B3146525
theorem B4719797 : Blo 2097435 4719797 := bbase (se 5 (by rfl) ⟨221240, by rfl⟩ : syracuseStep 4719797 = 442481) (by norm_num)
theorem B3146531 : Blo 2097435 3146531 := bstep (se 1 (by rfl) ⟨2359898, by rfl⟩ : syracuseStep 3146531 = 4719797) B4719797
theorem B2097687 : Blo 2097435 2097687 := bstep (se 1 (by rfl) ⟨1573265, by rfl⟩ : syracuseStep 2097687 = 3146531) B3146531
theorem B2240065 : Blo 2097435 2240065 := bbase (se 2 (by rfl) ⟨840024, by rfl⟩ : syracuseStep 2240065 = 1680049) (by norm_num)
theorem B11947013 : Blo 2097435 11947013 := bstep (se 4 (by rfl) ⟨1120032, by rfl⟩ : syracuseStep 11947013 = 2240065) B2240065
theorem B7964675 : Blo 2097435 7964675 := bstep (se 1 (by rfl) ⟨5973506, by rfl⟩ : syracuseStep 7964675 = 11947013) B11947013
theorem B5309783 : Blo 2097435 5309783 := bstep (se 1 (by rfl) ⟨3982337, by rfl⟩ : syracuseStep 5309783 = 7964675) B7964675
theorem B3539855 : Blo 2097435 3539855 := bstep (se 1 (by rfl) ⟨2654891, by rfl⟩ : syracuseStep 3539855 = 5309783) B5309783
theorem B2359903 : Blo 2097435 2359903 := bstep (se 1 (by rfl) ⟨1769927, by rfl⟩ : syracuseStep 2359903 = 3539855) B3539855
theorem B3146537 : Blo 2097435 3146537 := bstep (se 2 (by rfl) ⟨1179951, by rfl⟩ : syracuseStep 3146537 = 2359903) B2359903
theorem B2097691 : Blo 2097435 2097691 := bstep (se 1 (by rfl) ⟨1573268, by rfl⟩ : syracuseStep 2097691 = 3146537) B3146537
theorem B2240069 : Blo 2097435 2240069 := bbase (se 4 (by rfl) ⟨210006, by rfl⟩ : syracuseStep 2240069 = 420013) (by norm_num)
theorem B5973517 : Blo 2097435 5973517 := bstep (se 3 (by rfl) ⟨1120034, by rfl⟩ : syracuseStep 5973517 = 2240069) B2240069
theorem B7964689 : Blo 2097435 7964689 := bstep (se 2 (by rfl) ⟨2986758, by rfl⟩ : syracuseStep 7964689 = 5973517) B5973517
theorem B10619585 : Blo 2097435 10619585 := bstep (se 2 (by rfl) ⟨3982344, by rfl⟩ : syracuseStep 10619585 = 7964689) B7964689
theorem B7079723 : Blo 2097435 7079723 := bstep (se 1 (by rfl) ⟨5309792, by rfl⟩ : syracuseStep 7079723 = 10619585) B10619585
theorem B4719815 : Blo 2097435 4719815 := bstep (se 1 (by rfl) ⟨3539861, by rfl⟩ : syracuseStep 4719815 = 7079723) B7079723
theorem B3146543 : Blo 2097435 3146543 := bstep (se 1 (by rfl) ⟨2359907, by rfl⟩ : syracuseStep 3146543 = 4719815) B4719815
theorem B2097695 : Blo 2097435 2097695 := bstep (se 1 (by rfl) ⟨1573271, by rfl⟩ : syracuseStep 2097695 = 3146543) B3146543
theorem B3146549 : Blo 2097435 3146549 := bbase (se 5 (by rfl) ⟨147494, by rfl⟩ : syracuseStep 3146549 = 294989) (by norm_num)
theorem B2097699 : Blo 2097435 2097699 := bstep (se 1 (by rfl) ⟨1573274, by rfl⟩ : syracuseStep 2097699 = 3146549) B3146549
theorem B5309813 : Blo 2097435 5309813 := bbase (se 5 (by rfl) ⟨248897, by rfl⟩ : syracuseStep 5309813 = 497795) (by norm_num)
theorem B3539875 : Blo 2097435 3539875 := bstep (se 1 (by rfl) ⟨2654906, by rfl⟩ : syracuseStep 3539875 = 5309813) B5309813
theorem B4719833 : Blo 2097435 4719833 := bstep (se 2 (by rfl) ⟨1769937, by rfl⟩ : syracuseStep 4719833 = 3539875) B3539875
theorem B3146555 : Blo 2097435 3146555 := bstep (se 1 (by rfl) ⟨2359916, by rfl⟩ : syracuseStep 3146555 = 4719833) B4719833
theorem B2097703 : Blo 2097435 2097703 := bstep (se 1 (by rfl) ⟨1573277, by rfl⟩ : syracuseStep 2097703 = 3146555) B3146555
theorem B2359921 : Blo 2097435 2359921 := bbase (se 2 (by rfl) ⟨884970, by rfl⟩ : syracuseStep 2359921 = 1769941) (by norm_num)
theorem B3146561 : Blo 2097435 3146561 := bstep (se 2 (by rfl) ⟨1179960, by rfl⟩ : syracuseStep 3146561 = 2359921) B2359921
theorem B2097707 : Blo 2097435 2097707 := bstep (se 1 (by rfl) ⟨1573280, by rfl⟩ : syracuseStep 2097707 = 3146561) B3146561
theorem B10080389 : Blo 2097435 10080389 := bbase (se 4 (by rfl) ⟨945036, by rfl⟩ : syracuseStep 10080389 = 1890073) (by norm_num)
theorem B6720259 : Blo 2097435 6720259 := bstep (se 1 (by rfl) ⟨5040194, by rfl⟩ : syracuseStep 6720259 = 10080389) B10080389
theorem B8960345 : Blo 2097435 8960345 := bstep (se 2 (by rfl) ⟨3360129, by rfl⟩ : syracuseStep 8960345 = 6720259) B6720259
theorem B5973563 : Blo 2097435 5973563 := bstep (se 1 (by rfl) ⟨4480172, by rfl⟩ : syracuseStep 5973563 = 8960345) B8960345
theorem B3982375 : Blo 2097435 3982375 := bstep (se 1 (by rfl) ⟨2986781, by rfl⟩ : syracuseStep 3982375 = 5973563) B5973563
theorem B5309833 : Blo 2097435 5309833 := bstep (se 2 (by rfl) ⟨1991187, by rfl⟩ : syracuseStep 5309833 = 3982375) B3982375
theorem B7079777 : Blo 2097435 7079777 := bstep (se 2 (by rfl) ⟨2654916, by rfl⟩ : syracuseStep 7079777 = 5309833) B5309833
theorem B4719851 : Blo 2097435 4719851 := bstep (se 1 (by rfl) ⟨3539888, by rfl⟩ : syracuseStep 4719851 = 7079777) B7079777
theorem B3146567 : Blo 2097435 3146567 := bstep (se 1 (by rfl) ⟨2359925, by rfl⟩ : syracuseStep 3146567 = 4719851) B4719851
theorem B2097711 : Blo 2097435 2097711 := bstep (se 1 (by rfl) ⟨1573283, by rfl⟩ : syracuseStep 2097711 = 3146567) B3146567
theorem B3146573 : Blo 2097435 3146573 := bbase (se 3 (by rfl) ⟨589982, by rfl⟩ : syracuseStep 3146573 = 1179965) (by norm_num)
theorem B2097715 : Blo 2097435 2097715 := bstep (se 1 (by rfl) ⟨1573286, by rfl⟩ : syracuseStep 2097715 = 3146573) B3146573
theorem B4719869 : Blo 2097435 4719869 := bbase (se 3 (by rfl) ⟨884975, by rfl⟩ : syracuseStep 4719869 = 1769951) (by norm_num)
theorem B3146579 : Blo 2097435 3146579 := bstep (se 1 (by rfl) ⟨2359934, by rfl⟩ : syracuseStep 3146579 = 4719869) B4719869
theorem B2097719 : Blo 2097435 2097719 := bstep (se 1 (by rfl) ⟨1573289, by rfl⟩ : syracuseStep 2097719 = 3146579) B3146579
theorem B3539909 : Blo 2097435 3539909 := bbase (se 4 (by rfl) ⟨331866, by rfl⟩ : syracuseStep 3539909 = 663733) (by norm_num)
theorem B2359939 : Blo 2097435 2359939 := bstep (se 1 (by rfl) ⟨1769954, by rfl⟩ : syracuseStep 2359939 = 3539909) B3539909
theorem B3146585 : Blo 2097435 3146585 := bstep (se 2 (by rfl) ⟨1179969, by rfl⟩ : syracuseStep 3146585 = 2359939) B2359939
theorem B2097723 : Blo 2097435 2097723 := bstep (se 1 (by rfl) ⟨1573292, by rfl⟩ : syracuseStep 2097723 = 3146585) B3146585
theorem B15929621 : Blo 2097435 15929621 := bbase (se 6 (by rfl) ⟨373350, by rfl⟩ : syracuseStep 15929621 = 746701) (by norm_num)
theorem B10619747 : Blo 2097435 10619747 := bstep (se 1 (by rfl) ⟨7964810, by rfl⟩ : syracuseStep 10619747 = 15929621) B15929621
theorem B7079831 : Blo 2097435 7079831 := bstep (se 1 (by rfl) ⟨5309873, by rfl⟩ : syracuseStep 7079831 = 10619747) B10619747
theorem B4719887 : Blo 2097435 4719887 := bstep (se 1 (by rfl) ⟨3539915, by rfl⟩ : syracuseStep 4719887 = 7079831) B7079831
theorem B3146591 : Blo 2097435 3146591 := bstep (se 1 (by rfl) ⟨2359943, by rfl⟩ : syracuseStep 3146591 = 4719887) B4719887
theorem B2097727 : Blo 2097435 2097727 := bstep (se 1 (by rfl) ⟨1573295, by rfl⟩ : syracuseStep 2097727 = 3146591) B3146591
theorem B3146597 : Blo 2097435 3146597 := bbase (se 4 (by rfl) ⟨294993, by rfl⟩ : syracuseStep 3146597 = 589987) (by norm_num)
theorem B2097731 : Blo 2097435 2097731 := bstep (se 1 (by rfl) ⟨1573298, by rfl⟩ : syracuseStep 2097731 = 3146597) B3146597
theorem B3982421 : Blo 2097435 3982421 := bbase (se 8 (by rfl) ⟨23334, by rfl⟩ : syracuseStep 3982421 = 46669) (by norm_num)
theorem B2654947 : Blo 2097435 2654947 := bstep (se 1 (by rfl) ⟨1991210, by rfl⟩ : syracuseStep 2654947 = 3982421) B3982421
theorem B3539929 : Blo 2097435 3539929 := bstep (se 2 (by rfl) ⟨1327473, by rfl⟩ : syracuseStep 3539929 = 2654947) B2654947
theorem B4719905 : Blo 2097435 4719905 := bstep (se 2 (by rfl) ⟨1769964, by rfl⟩ : syracuseStep 4719905 = 3539929) B3539929
theorem B3146603 : Blo 2097435 3146603 := bstep (se 1 (by rfl) ⟨2359952, by rfl⟩ : syracuseStep 3146603 = 4719905) B4719905
theorem B2097735 : Blo 2097435 2097735 := bstep (se 1 (by rfl) ⟨1573301, by rfl⟩ : syracuseStep 2097735 = 3146603) B3146603
theorem B2359957 : Blo 2097435 2359957 := bbase (se 6 (by rfl) ⟨55311, by rfl⟩ : syracuseStep 2359957 = 110623) (by norm_num)
theorem B3146609 : Blo 2097435 3146609 := bstep (se 2 (by rfl) ⟨1179978, by rfl⟩ : syracuseStep 3146609 = 2359957) B2359957
theorem B2097739 : Blo 2097435 2097739 := bstep (se 1 (by rfl) ⟨1573304, by rfl⟩ : syracuseStep 2097739 = 3146609) B3146609
theorem B2654957 : Blo 2097435 2654957 := bbase (se 3 (by rfl) ⟨497804, by rfl⟩ : syracuseStep 2654957 = 995609) (by norm_num)
theorem B7079885 : Blo 2097435 7079885 := bstep (se 3 (by rfl) ⟨1327478, by rfl⟩ : syracuseStep 7079885 = 2654957) B2654957
theorem B4719923 : Blo 2097435 4719923 := bstep (se 1 (by rfl) ⟨3539942, by rfl⟩ : syracuseStep 4719923 = 7079885) B7079885
theorem B3146615 : Blo 2097435 3146615 := bstep (se 1 (by rfl) ⟨2359961, by rfl⟩ : syracuseStep 3146615 = 4719923) B4719923
theorem B2097743 : Blo 2097435 2097743 := bstep (se 1 (by rfl) ⟨1573307, by rfl⟩ : syracuseStep 2097743 = 3146615) B3146615
theorem B3146621 : Blo 2097435 3146621 := bbase (se 3 (by rfl) ⟨589991, by rfl⟩ : syracuseStep 3146621 = 1179983) (by norm_num)
theorem B2097747 : Blo 2097435 2097747 := bstep (se 1 (by rfl) ⟨1573310, by rfl⟩ : syracuseStep 2097747 = 3146621) B3146621
theorem B4719941 : Blo 2097435 4719941 := bbase (se 4 (by rfl) ⟨442494, by rfl⟩ : syracuseStep 4719941 = 884989) (by norm_num)
theorem B3146627 : Blo 2097435 3146627 := bstep (se 1 (by rfl) ⟨2359970, by rfl⟩ : syracuseStep 3146627 = 4719941) B4719941
theorem B2097751 : Blo 2097435 2097751 := bstep (se 1 (by rfl) ⟨1573313, by rfl⟩ : syracuseStep 2097751 = 3146627) B3146627
theorem B5040301 : Blo 2097435 5040301 := bbase (se 3 (by rfl) ⟨945056, by rfl⟩ : syracuseStep 5040301 = 1890113) (by norm_num)
theorem B6720401 : Blo 2097435 6720401 := bstep (se 2 (by rfl) ⟨2520150, by rfl⟩ : syracuseStep 6720401 = 5040301) B5040301
theorem B4480267 : Blo 2097435 4480267 := bstep (se 1 (by rfl) ⟨3360200, by rfl⟩ : syracuseStep 4480267 = 6720401) B6720401
theorem B5973689 : Blo 2097435 5973689 := bstep (se 2 (by rfl) ⟨2240133, by rfl⟩ : syracuseStep 5973689 = 4480267) B4480267
theorem B3982459 : Blo 2097435 3982459 := bstep (se 1 (by rfl) ⟨2986844, by rfl⟩ : syracuseStep 3982459 = 5973689) B5973689
theorem B5309945 : Blo 2097435 5309945 := bstep (se 2 (by rfl) ⟨1991229, by rfl⟩ : syracuseStep 5309945 = 3982459) B3982459
theorem B3539963 : Blo 2097435 3539963 := bstep (se 1 (by rfl) ⟨2654972, by rfl⟩ : syracuseStep 3539963 = 5309945) B5309945
theorem B2359975 : Blo 2097435 2359975 := bstep (se 1 (by rfl) ⟨1769981, by rfl⟩ : syracuseStep 2359975 = 3539963) B3539963
theorem B3146633 : Blo 2097435 3146633 := bstep (se 2 (by rfl) ⟨1179987, by rfl⟩ : syracuseStep 3146633 = 2359975) B2359975
theorem B2097755 : Blo 2097435 2097755 := bstep (se 1 (by rfl) ⟨1573316, by rfl⟩ : syracuseStep 2097755 = 3146633) B3146633
theorem B10619909 : Blo 2097435 10619909 := bbase (se 4 (by rfl) ⟨995616, by rfl⟩ : syracuseStep 10619909 = 1991233) (by norm_num)
theorem B7079939 : Blo 2097435 7079939 := bstep (se 1 (by rfl) ⟨5309954, by rfl⟩ : syracuseStep 7079939 = 10619909) B10619909
theorem B4719959 : Blo 2097435 4719959 := bstep (se 1 (by rfl) ⟨3539969, by rfl⟩ : syracuseStep 4719959 = 7079939) B7079939
theorem B3146639 : Blo 2097435 3146639 := bstep (se 1 (by rfl) ⟨2359979, by rfl⟩ : syracuseStep 3146639 = 4719959) B4719959
theorem B2097759 : Blo 2097435 2097759 := bstep (se 1 (by rfl) ⟨1573319, by rfl⟩ : syracuseStep 2097759 = 3146639) B3146639
theorem B3146645 : Blo 2097435 3146645 := bbase (se 6 (by rfl) ⟨73749, by rfl⟩ : syracuseStep 3146645 = 147499) (by norm_num)
theorem B2097763 : Blo 2097435 2097763 := bstep (se 1 (by rfl) ⟨1573322, by rfl⟩ : syracuseStep 2097763 = 3146645) B3146645
theorem B11947445 : Blo 2097435 11947445 := bbase (se 5 (by rfl) ⟨560036, by rfl⟩ : syracuseStep 11947445 = 1120073) (by norm_num)
theorem B7964963 : Blo 2097435 7964963 := bstep (se 1 (by rfl) ⟨5973722, by rfl⟩ : syracuseStep 7964963 = 11947445) B11947445
theorem B5309975 : Blo 2097435 5309975 := bstep (se 1 (by rfl) ⟨3982481, by rfl⟩ : syracuseStep 5309975 = 7964963) B7964963
theorem B3539983 : Blo 2097435 3539983 := bstep (se 1 (by rfl) ⟨2654987, by rfl⟩ : syracuseStep 3539983 = 5309975) B5309975
theorem B4719977 : Blo 2097435 4719977 := bstep (se 2 (by rfl) ⟨1769991, by rfl⟩ : syracuseStep 4719977 = 3539983) B3539983
theorem B3146651 : Blo 2097435 3146651 := bstep (se 1 (by rfl) ⟨2359988, by rfl⟩ : syracuseStep 3146651 = 4719977) B4719977
theorem B2097767 : Blo 2097435 2097767 := bstep (se 1 (by rfl) ⟨1573325, by rfl⟩ : syracuseStep 2097767 = 3146651) B3146651
theorem B2359993 : Blo 2097435 2359993 := bbase (se 2 (by rfl) ⟨884997, by rfl⟩ : syracuseStep 2359993 = 1769995) (by norm_num)
theorem B3146657 : Blo 2097435 3146657 := bstep (se 2 (by rfl) ⟨1179996, by rfl⟩ : syracuseStep 3146657 = 2359993) B2359993
theorem B2097771 : Blo 2097435 2097771 := bstep (se 1 (by rfl) ⟨1573328, by rfl⟩ : syracuseStep 2097771 = 3146657) B3146657
theorem B4480309 : Blo 2097435 4480309 := bbase (se 5 (by rfl) ⟨210014, by rfl⟩ : syracuseStep 4480309 = 420029) (by norm_num)
theorem B5973745 : Blo 2097435 5973745 := bstep (se 2 (by rfl) ⟨2240154, by rfl⟩ : syracuseStep 5973745 = 4480309) B4480309
theorem B7964993 : Blo 2097435 7964993 := bstep (se 2 (by rfl) ⟨2986872, by rfl⟩ : syracuseStep 7964993 = 5973745) B5973745
theorem B5309995 : Blo 2097435 5309995 := bstep (se 1 (by rfl) ⟨3982496, by rfl⟩ : syracuseStep 5309995 = 7964993) B7964993
theorem B7079993 : Blo 2097435 7079993 := bstep (se 2 (by rfl) ⟨2654997, by rfl⟩ : syracuseStep 7079993 = 5309995) B5309995
theorem B4719995 : Blo 2097435 4719995 := bstep (se 1 (by rfl) ⟨3539996, by rfl⟩ : syracuseStep 4719995 = 7079993) B7079993
theorem B3146663 : Blo 2097435 3146663 := bstep (se 1 (by rfl) ⟨2359997, by rfl⟩ : syracuseStep 3146663 = 4719995) B4719995
theorem B2097775 : Blo 2097435 2097775 := bstep (se 1 (by rfl) ⟨1573331, by rfl⟩ : syracuseStep 2097775 = 3146663) B3146663
theorem B3146669 : Blo 2097435 3146669 := bbase (se 3 (by rfl) ⟨590000, by rfl⟩ : syracuseStep 3146669 = 1180001) (by norm_num)
theorem B2097779 : Blo 2097435 2097779 := bstep (se 1 (by rfl) ⟨1573334, by rfl⟩ : syracuseStep 2097779 = 3146669) B3146669
theorem B4720013 : Blo 2097435 4720013 := bbase (se 3 (by rfl) ⟨885002, by rfl⟩ : syracuseStep 4720013 = 1770005) (by norm_num)
theorem B3146675 : Blo 2097435 3146675 := bstep (se 1 (by rfl) ⟨2360006, by rfl⟩ : syracuseStep 3146675 = 4720013) B4720013
theorem B2097783 : Blo 2097435 2097783 := bstep (se 1 (by rfl) ⟨1573337, by rfl⟩ : syracuseStep 2097783 = 3146675) B3146675
theorem B2655013 : Blo 2097435 2655013 := bbase (se 4 (by rfl) ⟨248907, by rfl⟩ : syracuseStep 2655013 = 497815) (by norm_num)
theorem B3540017 : Blo 2097435 3540017 := bstep (se 2 (by rfl) ⟨1327506, by rfl⟩ : syracuseStep 3540017 = 2655013) B2655013
theorem B2360011 : Blo 2097435 2360011 := bstep (se 1 (by rfl) ⟨1770008, by rfl⟩ : syracuseStep 2360011 = 3540017) B3540017
theorem B3146681 : Blo 2097435 3146681 := bstep (se 2 (by rfl) ⟨1180005, by rfl⟩ : syracuseStep 3146681 = 2360011) B2360011
theorem B2097787 : Blo 2097435 2097787 := bstep (se 1 (by rfl) ⟨1573340, by rfl⟩ : syracuseStep 2097787 = 3146681) B3146681
theorem B4784429 : Blo 2097435 4784429 := bbase (se 3 (by rfl) ⟨897080, by rfl⟩ : syracuseStep 4784429 = 1794161) (by norm_num)
theorem B12758477 : Blo 2097435 12758477 := bstep (se 3 (by rfl) ⟨2392214, by rfl⟩ : syracuseStep 12758477 = 4784429) B4784429
theorem B34022605 : Blo 2097435 34022605 := bstep (se 3 (by rfl) ⟨6379238, by rfl⟩ : syracuseStep 34022605 = 12758477) B12758477
theorem B45363473 : Blo 2097435 45363473 := bstep (se 2 (by rfl) ⟨17011302, by rfl⟩ : syracuseStep 45363473 = 34022605) B34022605
theorem B30242315 : Blo 2097435 30242315 := bstep (se 1 (by rfl) ⟨22681736, by rfl⟩ : syracuseStep 30242315 = 45363473) B45363473
theorem B20161543 : Blo 2097435 20161543 := bstep (se 1 (by rfl) ⟨15121157, by rfl⟩ : syracuseStep 20161543 = 30242315) B30242315
theorem B26882057 : Blo 2097435 26882057 := bstep (se 2 (by rfl) ⟨10080771, by rfl⟩ : syracuseStep 26882057 = 20161543) B20161543
theorem B17921371 : Blo 2097435 17921371 := bstep (se 1 (by rfl) ⟨13441028, by rfl⟩ : syracuseStep 17921371 = 26882057) B26882057
theorem B23895161 : Blo 2097435 23895161 := bstep (se 2 (by rfl) ⟨8960685, by rfl⟩ : syracuseStep 23895161 = 17921371) B17921371
theorem B15930107 : Blo 2097435 15930107 := bstep (se 1 (by rfl) ⟨11947580, by rfl⟩ : syracuseStep 15930107 = 23895161) B23895161
theorem B10620071 : Blo 2097435 10620071 := bstep (se 1 (by rfl) ⟨7965053, by rfl⟩ : syracuseStep 10620071 = 15930107) B15930107
theorem B7080047 : Blo 2097435 7080047 := bstep (se 1 (by rfl) ⟨5310035, by rfl⟩ : syracuseStep 7080047 = 10620071) B10620071
theorem B4720031 : Blo 2097435 4720031 := bstep (se 1 (by rfl) ⟨3540023, by rfl⟩ : syracuseStep 4720031 = 7080047) B7080047
theorem B3146687 : Blo 2097435 3146687 := bstep (se 1 (by rfl) ⟨2360015, by rfl⟩ : syracuseStep 3146687 = 4720031) B4720031
theorem B2097791 : Blo 2097435 2097791 := bstep (se 1 (by rfl) ⟨1573343, by rfl⟩ : syracuseStep 2097791 = 3146687) B3146687
theorem B3146693 : Blo 2097435 3146693 := bbase (se 4 (by rfl) ⟨295002, by rfl⟩ : syracuseStep 3146693 = 590005) (by norm_num)
theorem B2097795 : Blo 2097435 2097795 := bstep (se 1 (by rfl) ⟨1573346, by rfl⟩ : syracuseStep 2097795 = 3146693) B3146693
theorem B3540037 : Blo 2097435 3540037 := bbase (se 4 (by rfl) ⟨331878, by rfl⟩ : syracuseStep 3540037 = 663757) (by norm_num)
theorem B4720049 : Blo 2097435 4720049 := bstep (se 2 (by rfl) ⟨1770018, by rfl⟩ : syracuseStep 4720049 = 3540037) B3540037
theorem B3146699 : Blo 2097435 3146699 := bstep (se 1 (by rfl) ⟨2360024, by rfl⟩ : syracuseStep 3146699 = 4720049) B4720049
theorem B2097799 : Blo 2097435 2097799 := bstep (se 1 (by rfl) ⟨1573349, by rfl⟩ : syracuseStep 2097799 = 3146699) B3146699
theorem B2360029 : Blo 2097435 2360029 := bbase (se 3 (by rfl) ⟨442505, by rfl⟩ : syracuseStep 2360029 = 885011) (by norm_num)
theorem B3146705 : Blo 2097435 3146705 := bstep (se 2 (by rfl) ⟨1180014, by rfl⟩ : syracuseStep 3146705 = 2360029) B2360029
theorem B2097803 : Blo 2097435 2097803 := bstep (se 1 (by rfl) ⟨1573352, by rfl⟩ : syracuseStep 2097803 = 3146705) B3146705
theorem B7080101 : Blo 2097435 7080101 := bbase (se 4 (by rfl) ⟨663759, by rfl⟩ : syracuseStep 7080101 = 1327519) (by norm_num)
theorem B4720067 : Blo 2097435 4720067 := bstep (se 1 (by rfl) ⟨3540050, by rfl⟩ : syracuseStep 4720067 = 7080101) B7080101
theorem B3146711 : Blo 2097435 3146711 := bstep (se 1 (by rfl) ⟨2360033, by rfl⟩ : syracuseStep 3146711 = 4720067) B4720067
theorem B2097807 : Blo 2097435 2097807 := bstep (se 1 (by rfl) ⟨1573355, by rfl⟩ : syracuseStep 2097807 = 3146711) B3146711
theorem B3146717 : Blo 2097435 3146717 := bbase (se 3 (by rfl) ⟨590009, by rfl⟩ : syracuseStep 3146717 = 1180019) (by norm_num)
theorem B2097811 : Blo 2097435 2097811 := bstep (se 1 (by rfl) ⟨1573358, by rfl⟩ : syracuseStep 2097811 = 3146717) B3146717
theorem B4720085 : Blo 2097435 4720085 := bbase (se 7 (by rfl) ⟨55313, by rfl⟩ : syracuseStep 4720085 = 110627) (by norm_num)
theorem B3146723 : Blo 2097435 3146723 := bstep (se 1 (by rfl) ⟨2360042, by rfl⟩ : syracuseStep 3146723 = 4720085) B4720085
theorem B2097815 : Blo 2097435 2097815 := bstep (se 1 (by rfl) ⟨1573361, by rfl⟩ : syracuseStep 2097815 = 3146723) B3146723
theorem B16147669 : Blo 2097435 16147669 := bbase (se 7 (by rfl) ⟨189230, by rfl⟩ : syracuseStep 16147669 = 378461) (by norm_num)
theorem B21530225 : Blo 2097435 21530225 := bstep (se 2 (by rfl) ⟨8073834, by rfl⟩ : syracuseStep 21530225 = 16147669) B16147669
theorem B14353483 : Blo 2097435 14353483 := bstep (se 1 (by rfl) ⟨10765112, by rfl⟩ : syracuseStep 14353483 = 21530225) B21530225
theorem B19137977 : Blo 2097435 19137977 := bstep (se 2 (by rfl) ⟨7176741, by rfl⟩ : syracuseStep 19137977 = 14353483) B14353483
theorem B12758651 : Blo 2097435 12758651 := bstep (se 1 (by rfl) ⟨9568988, by rfl⟩ : syracuseStep 12758651 = 19137977) B19137977
theorem B8505767 : Blo 2097435 8505767 := bstep (se 1 (by rfl) ⟨6379325, by rfl⟩ : syracuseStep 8505767 = 12758651) B12758651
theorem B22682045 : Blo 2097435 22682045 := bstep (se 3 (by rfl) ⟨4252883, by rfl⟩ : syracuseStep 22682045 = 8505767) B8505767
theorem B15121363 : Blo 2097435 15121363 := bstep (se 1 (by rfl) ⟨11341022, by rfl⟩ : syracuseStep 15121363 = 22682045) B22682045
theorem B20161817 : Blo 2097435 20161817 := bstep (se 2 (by rfl) ⟨7560681, by rfl⟩ : syracuseStep 20161817 = 15121363) B15121363
theorem B13441211 : Blo 2097435 13441211 := bstep (se 1 (by rfl) ⟨10080908, by rfl⟩ : syracuseStep 13441211 = 20161817) B20161817
theorem B8960807 : Blo 2097435 8960807 := bstep (se 1 (by rfl) ⟨6720605, by rfl⟩ : syracuseStep 8960807 = 13441211) B13441211
theorem B5973871 : Blo 2097435 5973871 := bstep (se 1 (by rfl) ⟨4480403, by rfl⟩ : syracuseStep 5973871 = 8960807) B8960807
theorem B7965161 : Blo 2097435 7965161 := bstep (se 2 (by rfl) ⟨2986935, by rfl⟩ : syracuseStep 7965161 = 5973871) B5973871
theorem B5310107 : Blo 2097435 5310107 := bstep (se 1 (by rfl) ⟨3982580, by rfl⟩ : syracuseStep 5310107 = 7965161) B7965161
theorem B3540071 : Blo 2097435 3540071 := bstep (se 1 (by rfl) ⟨2655053, by rfl⟩ : syracuseStep 3540071 = 5310107) B5310107
theorem B2360047 : Blo 2097435 2360047 := bstep (se 1 (by rfl) ⟨1770035, by rfl⟩ : syracuseStep 2360047 = 3540071) B3540071
theorem B3146729 : Blo 2097435 3146729 := bstep (se 2 (by rfl) ⟨1180023, by rfl⟩ : syracuseStep 3146729 = 2360047) B2360047
theorem B2097819 : Blo 2097435 2097819 := bstep (se 1 (by rfl) ⟨1573364, by rfl⟩ : syracuseStep 2097819 = 3146729) B3146729
theorem B4036925 : Blo 2097435 4036925 := bbase (se 3 (by rfl) ⟨756923, by rfl⟩ : syracuseStep 4036925 = 1513847) (by norm_num)
theorem B10765133 : Blo 2097435 10765133 := bstep (se 3 (by rfl) ⟨2018462, by rfl⟩ : syracuseStep 10765133 = 4036925) B4036925
theorem B7176755 : Blo 2097435 7176755 := bstep (se 1 (by rfl) ⟨5382566, by rfl⟩ : syracuseStep 7176755 = 10765133) B10765133
theorem B4784503 : Blo 2097435 4784503 := bstep (se 1 (by rfl) ⟨3588377, by rfl⟩ : syracuseStep 4784503 = 7176755) B7176755
theorem B6379337 : Blo 2097435 6379337 := bstep (se 2 (by rfl) ⟨2392251, by rfl⟩ : syracuseStep 6379337 = 4784503) B4784503
theorem B17011565 : Blo 2097435 17011565 := bstep (se 3 (by rfl) ⟨3189668, by rfl⟩ : syracuseStep 17011565 = 6379337) B6379337
theorem B11341043 : Blo 2097435 11341043 := bstep (se 1 (by rfl) ⟨8505782, by rfl⟩ : syracuseStep 11341043 = 17011565) B17011565
theorem B7560695 : Blo 2097435 7560695 := bstep (se 1 (by rfl) ⟨5670521, by rfl⟩ : syracuseStep 7560695 = 11341043) B11341043
theorem B5040463 : Blo 2097435 5040463 := bstep (se 1 (by rfl) ⟨3780347, by rfl⟩ : syracuseStep 5040463 = 7560695) B7560695
theorem B6720617 : Blo 2097435 6720617 := bstep (se 2 (by rfl) ⟨2520231, by rfl⟩ : syracuseStep 6720617 = 5040463) B5040463
theorem B17921645 : Blo 2097435 17921645 := bstep (se 3 (by rfl) ⟨3360308, by rfl⟩ : syracuseStep 17921645 = 6720617) B6720617
theorem B11947763 : Blo 2097435 11947763 := bstep (se 1 (by rfl) ⟨8960822, by rfl⟩ : syracuseStep 11947763 = 17921645) B17921645
theorem B7965175 : Blo 2097435 7965175 := bstep (se 1 (by rfl) ⟨5973881, by rfl⟩ : syracuseStep 7965175 = 11947763) B11947763
theorem B10620233 : Blo 2097435 10620233 := bstep (se 2 (by rfl) ⟨3982587, by rfl⟩ : syracuseStep 10620233 = 7965175) B7965175
theorem B7080155 : Blo 2097435 7080155 := bstep (se 1 (by rfl) ⟨5310116, by rfl⟩ : syracuseStep 7080155 = 10620233) B10620233
theorem B4720103 : Blo 2097435 4720103 := bstep (se 1 (by rfl) ⟨3540077, by rfl⟩ : syracuseStep 4720103 = 7080155) B7080155
theorem B3146735 : Blo 2097435 3146735 := bstep (se 1 (by rfl) ⟨2360051, by rfl⟩ : syracuseStep 3146735 = 4720103) B4720103
theorem B2097823 : Blo 2097435 2097823 := bstep (se 1 (by rfl) ⟨1573367, by rfl⟩ : syracuseStep 2097823 = 3146735) B3146735
theorem B3146741 : Blo 2097435 3146741 := bbase (se 5 (by rfl) ⟨147503, by rfl⟩ : syracuseStep 3146741 = 295007) (by norm_num)
theorem B2097827 : Blo 2097435 2097827 := bstep (se 1 (by rfl) ⟨1573370, by rfl⟩ : syracuseStep 2097827 = 3146741) B3146741
theorem B4480429 : Blo 2097435 4480429 := bbase (se 3 (by rfl) ⟨840080, by rfl⟩ : syracuseStep 4480429 = 1680161) (by norm_num)
theorem B5973905 : Blo 2097435 5973905 := bstep (se 2 (by rfl) ⟨2240214, by rfl⟩ : syracuseStep 5973905 = 4480429) B4480429
theorem B3982603 : Blo 2097435 3982603 := bstep (se 1 (by rfl) ⟨2986952, by rfl⟩ : syracuseStep 3982603 = 5973905) B5973905
theorem B5310137 : Blo 2097435 5310137 := bstep (se 2 (by rfl) ⟨1991301, by rfl⟩ : syracuseStep 5310137 = 3982603) B3982603
theorem B3540091 : Blo 2097435 3540091 := bstep (se 1 (by rfl) ⟨2655068, by rfl⟩ : syracuseStep 3540091 = 5310137) B5310137
theorem B4720121 : Blo 2097435 4720121 := bstep (se 2 (by rfl) ⟨1770045, by rfl⟩ : syracuseStep 4720121 = 3540091) B3540091
theorem B3146747 : Blo 2097435 3146747 := bstep (se 1 (by rfl) ⟨2360060, by rfl⟩ : syracuseStep 3146747 = 4720121) B4720121
theorem B2097831 : Blo 2097435 2097831 := bstep (se 1 (by rfl) ⟨1573373, by rfl⟩ : syracuseStep 2097831 = 3146747) B3146747
theorem B2360065 : Blo 2097435 2360065 := bbase (se 2 (by rfl) ⟨885024, by rfl⟩ : syracuseStep 2360065 = 1770049) (by norm_num)
theorem B3146753 : Blo 2097435 3146753 := bstep (se 2 (by rfl) ⟨1180032, by rfl⟩ : syracuseStep 3146753 = 2360065) B2360065
theorem B2097835 : Blo 2097435 2097835 := bstep (se 1 (by rfl) ⟨1573376, by rfl⟩ : syracuseStep 2097835 = 3146753) B3146753
theorem B5310157 : Blo 2097435 5310157 := bbase (se 3 (by rfl) ⟨995654, by rfl⟩ : syracuseStep 5310157 = 1991309) (by norm_num)
theorem B7080209 : Blo 2097435 7080209 := bstep (se 2 (by rfl) ⟨2655078, by rfl⟩ : syracuseStep 7080209 = 5310157) B5310157
theorem B4720139 : Blo 2097435 4720139 := bstep (se 1 (by rfl) ⟨3540104, by rfl⟩ : syracuseStep 4720139 = 7080209) B7080209
theorem B3146759 : Blo 2097435 3146759 := bstep (se 1 (by rfl) ⟨2360069, by rfl⟩ : syracuseStep 3146759 = 4720139) B4720139
theorem B2097839 : Blo 2097435 2097839 := bstep (se 1 (by rfl) ⟨1573379, by rfl⟩ : syracuseStep 2097839 = 3146759) B3146759
theorem B3146765 : Blo 2097435 3146765 := bbase (se 3 (by rfl) ⟨590018, by rfl⟩ : syracuseStep 3146765 = 1180037) (by norm_num)
theorem B2097843 : Blo 2097435 2097843 := bstep (se 1 (by rfl) ⟨1573382, by rfl⟩ : syracuseStep 2097843 = 3146765) B3146765
theorem B4720157 : Blo 2097435 4720157 := bbase (se 3 (by rfl) ⟨885029, by rfl⟩ : syracuseStep 4720157 = 1770059) (by norm_num)
theorem B3146771 : Blo 2097435 3146771 := bstep (se 1 (by rfl) ⟨2360078, by rfl⟩ : syracuseStep 3146771 = 4720157) B4720157
theorem B2097847 : Blo 2097435 2097847 := bstep (se 1 (by rfl) ⟨1573385, by rfl⟩ : syracuseStep 2097847 = 3146771) B3146771
theorem B3540125 : Blo 2097435 3540125 := bbase (se 3 (by rfl) ⟨663773, by rfl⟩ : syracuseStep 3540125 = 1327547) (by norm_num)
theorem B2360083 : Blo 2097435 2360083 := bstep (se 1 (by rfl) ⟨1770062, by rfl⟩ : syracuseStep 2360083 = 3540125) B3540125
theorem B3146777 : Blo 2097435 3146777 := bstep (se 2 (by rfl) ⟨1180041, by rfl⟩ : syracuseStep 3146777 = 2360083) B2360083
theorem B2097851 : Blo 2097435 2097851 := bstep (se 1 (by rfl) ⟨1573388, by rfl⟩ : syracuseStep 2097851 = 3146777) B3146777
theorem B8295797 : Blo 2097435 8295797 := bbase (se 5 (by rfl) ⟨388865, by rfl⟩ : syracuseStep 8295797 = 777731) (by norm_num)
theorem B5530531 : Blo 2097435 5530531 := bstep (se 1 (by rfl) ⟨4147898, by rfl⟩ : syracuseStep 5530531 = 8295797) B8295797
theorem B7374041 : Blo 2097435 7374041 := bstep (se 2 (by rfl) ⟨2765265, by rfl⟩ : syracuseStep 7374041 = 5530531) B5530531
theorem B4916027 : Blo 2097435 4916027 := bstep (se 1 (by rfl) ⟨3687020, by rfl⟩ : syracuseStep 4916027 = 7374041) B7374041
theorem B3277351 : Blo 2097435 3277351 := bstep (se 1 (by rfl) ⟨2458013, by rfl⟩ : syracuseStep 3277351 = 4916027) B4916027
theorem B4369801 : Blo 2097435 4369801 := bstep (se 2 (by rfl) ⟨1638675, by rfl⟩ : syracuseStep 4369801 = 3277351) B3277351
theorem B5826401 : Blo 2097435 5826401 := bstep (se 2 (by rfl) ⟨2184900, by rfl⟩ : syracuseStep 5826401 = 4369801) B4369801
theorem B3884267 : Blo 2097435 3884267 := bstep (se 1 (by rfl) ⟨2913200, by rfl⟩ : syracuseStep 3884267 = 5826401) B5826401
theorem B2589511 : Blo 2097435 2589511 := bstep (se 1 (by rfl) ⟨1942133, by rfl⟩ : syracuseStep 2589511 = 3884267) B3884267
theorem B3452681 : Blo 2097435 3452681 := bstep (se 2 (by rfl) ⟨1294755, by rfl⟩ : syracuseStep 3452681 = 2589511) B2589511
theorem B2301787 : Blo 2097435 2301787 := bstep (se 1 (by rfl) ⟨1726340, by rfl⟩ : syracuseStep 2301787 = 3452681) B3452681
theorem B12276197 : Blo 2097435 12276197 := bstep (se 4 (by rfl) ⟨1150893, by rfl⟩ : syracuseStep 12276197 = 2301787) B2301787
theorem B8184131 : Blo 2097435 8184131 := bstep (se 1 (by rfl) ⟨6138098, by rfl⟩ : syracuseStep 8184131 = 12276197) B12276197
theorem B5456087 : Blo 2097435 5456087 := bstep (se 1 (by rfl) ⟨4092065, by rfl⟩ : syracuseStep 5456087 = 8184131) B8184131
theorem B3637391 : Blo 2097435 3637391 := bstep (se 1 (by rfl) ⟨2728043, by rfl⟩ : syracuseStep 3637391 = 5456087) B5456087
theorem B38798837 : Blo 2097435 38798837 := bstep (se 5 (by rfl) ⟨1818695, by rfl⟩ : syracuseStep 38798837 = 3637391) B3637391
theorem B25865891 : Blo 2097435 25865891 := bstep (se 1 (by rfl) ⟨19399418, by rfl⟩ : syracuseStep 25865891 = 38798837) B38798837
theorem B17243927 : Blo 2097435 17243927 := bstep (se 1 (by rfl) ⟨12932945, by rfl⟩ : syracuseStep 17243927 = 25865891) B25865891
theorem B11495951 : Blo 2097435 11495951 := bstep (se 1 (by rfl) ⟨8621963, by rfl⟩ : syracuseStep 11495951 = 17243927) B17243927
theorem B7663967 : Blo 2097435 7663967 := bstep (se 1 (by rfl) ⟨5747975, by rfl⟩ : syracuseStep 7663967 = 11495951) B11495951
theorem B5109311 : Blo 2097435 5109311 := bstep (se 1 (by rfl) ⟨3831983, by rfl⟩ : syracuseStep 5109311 = 7663967) B7663967
theorem B3406207 : Blo 2097435 3406207 := bstep (se 1 (by rfl) ⟨2554655, by rfl⟩ : syracuseStep 3406207 = 5109311) B5109311
theorem B4541609 : Blo 2097435 4541609 := bstep (se 2 (by rfl) ⟨1703103, by rfl⟩ : syracuseStep 4541609 = 3406207) B3406207
theorem B12110957 : Blo 2097435 12110957 := bstep (se 3 (by rfl) ⟨2270804, by rfl⟩ : syracuseStep 12110957 = 4541609) B4541609
theorem B8073971 : Blo 2097435 8073971 := bstep (se 1 (by rfl) ⟨6055478, by rfl⟩ : syracuseStep 8073971 = 12110957) B12110957
theorem B5382647 : Blo 2097435 5382647 := bstep (se 1 (by rfl) ⟨4036985, by rfl⟩ : syracuseStep 5382647 = 8073971) B8073971
theorem B57414901 : Blo 2097435 57414901 := bstep (se 5 (by rfl) ⟨2691323, by rfl⟩ : syracuseStep 57414901 = 5382647) B5382647
theorem B76553201 : Blo 2097435 76553201 := bstep (se 2 (by rfl) ⟨28707450, by rfl⟩ : syracuseStep 76553201 = 57414901) B57414901
theorem B51035467 : Blo 2097435 51035467 := bstep (se 1 (by rfl) ⟨38276600, by rfl⟩ : syracuseStep 51035467 = 76553201) B76553201
theorem B68047289 : Blo 2097435 68047289 := bstep (se 2 (by rfl) ⟨25517733, by rfl⟩ : syracuseStep 68047289 = 51035467) B51035467
theorem B45364859 : Blo 2097435 45364859 := bstep (se 1 (by rfl) ⟨34023644, by rfl⟩ : syracuseStep 45364859 = 68047289) B68047289
theorem B30243239 : Blo 2097435 30243239 := bstep (se 1 (by rfl) ⟨22682429, by rfl⟩ : syracuseStep 30243239 = 45364859) B45364859
theorem B20162159 : Blo 2097435 20162159 := bstep (se 1 (by rfl) ⟨15121619, by rfl⟩ : syracuseStep 20162159 = 30243239) B30243239
theorem B13441439 : Blo 2097435 13441439 := bstep (se 1 (by rfl) ⟨10081079, by rfl⟩ : syracuseStep 13441439 = 20162159) B20162159
theorem B8960959 : Blo 2097435 8960959 := bstep (se 1 (by rfl) ⟨6720719, by rfl⟩ : syracuseStep 8960959 = 13441439) B13441439
theorem B11947945 : Blo 2097435 11947945 := bstep (se 2 (by rfl) ⟨4480479, by rfl⟩ : syracuseStep 11947945 = 8960959) B8960959
theorem B15930593 : Blo 2097435 15930593 := bstep (se 2 (by rfl) ⟨5973972, by rfl⟩ : syracuseStep 15930593 = 11947945) B11947945
theorem B10620395 : Blo 2097435 10620395 := bstep (se 1 (by rfl) ⟨7965296, by rfl⟩ : syracuseStep 10620395 = 15930593) B15930593
theorem B7080263 : Blo 2097435 7080263 := bstep (se 1 (by rfl) ⟨5310197, by rfl⟩ : syracuseStep 7080263 = 10620395) B10620395
theorem B4720175 : Blo 2097435 4720175 := bstep (se 1 (by rfl) ⟨3540131, by rfl⟩ : syracuseStep 4720175 = 7080263) B7080263
theorem B3146783 : Blo 2097435 3146783 := bstep (se 1 (by rfl) ⟨2360087, by rfl⟩ : syracuseStep 3146783 = 4720175) B4720175
theorem B2097855 : Blo 2097435 2097855 := bstep (se 1 (by rfl) ⟨1573391, by rfl⟩ : syracuseStep 2097855 = 3146783) B3146783
theorem B3146789 : Blo 2097435 3146789 := bbase (se 4 (by rfl) ⟨295011, by rfl⟩ : syracuseStep 3146789 = 590023) (by norm_num)
theorem B2097859 : Blo 2097435 2097859 := bstep (se 1 (by rfl) ⟨1573394, by rfl⟩ : syracuseStep 2097859 = 3146789) B3146789
theorem B2655109 : Blo 2097435 2655109 := bbase (se 4 (by rfl) ⟨248916, by rfl⟩ : syracuseStep 2655109 = 497833) (by norm_num)
theorem B3540145 : Blo 2097435 3540145 := bstep (se 2 (by rfl) ⟨1327554, by rfl⟩ : syracuseStep 3540145 = 2655109) B2655109
theorem B4720193 : Blo 2097435 4720193 := bstep (se 2 (by rfl) ⟨1770072, by rfl⟩ : syracuseStep 4720193 = 3540145) B3540145
theorem B3146795 : Blo 2097435 3146795 := bstep (se 1 (by rfl) ⟨2360096, by rfl⟩ : syracuseStep 3146795 = 4720193) B4720193
theorem B2097863 : Blo 2097435 2097863 := bstep (se 1 (by rfl) ⟨1573397, by rfl⟩ : syracuseStep 2097863 = 3146795) B3146795
theorem B2360101 : Blo 2097435 2360101 := bbase (se 4 (by rfl) ⟨221259, by rfl⟩ : syracuseStep 2360101 = 442519) (by norm_num)
theorem B3146801 : Blo 2097435 3146801 := bstep (se 2 (by rfl) ⟨1180050, by rfl⟩ : syracuseStep 3146801 = 2360101) B2360101
theorem B2097867 : Blo 2097435 2097867 := bstep (se 1 (by rfl) ⟨1573400, by rfl⟩ : syracuseStep 2097867 = 3146801) B3146801
theorem B8961029 : Blo 2097435 8961029 := bbase (se 4 (by rfl) ⟨840096, by rfl⟩ : syracuseStep 8961029 = 1680193) (by norm_num)
theorem B5974019 : Blo 2097435 5974019 := bstep (se 1 (by rfl) ⟨4480514, by rfl⟩ : syracuseStep 5974019 = 8961029) B8961029
theorem B3982679 : Blo 2097435 3982679 := bstep (se 1 (by rfl) ⟨2987009, by rfl⟩ : syracuseStep 3982679 = 5974019) B5974019
theorem B2655119 : Blo 2097435 2655119 := bstep (se 1 (by rfl) ⟨1991339, by rfl⟩ : syracuseStep 2655119 = 3982679) B3982679
theorem B7080317 : Blo 2097435 7080317 := bstep (se 3 (by rfl) ⟨1327559, by rfl⟩ : syracuseStep 7080317 = 2655119) B2655119
theorem B4720211 : Blo 2097435 4720211 := bstep (se 1 (by rfl) ⟨3540158, by rfl⟩ : syracuseStep 4720211 = 7080317) B7080317
theorem B3146807 : Blo 2097435 3146807 := bstep (se 1 (by rfl) ⟨2360105, by rfl⟩ : syracuseStep 3146807 = 4720211) B4720211
theorem B2097871 : Blo 2097435 2097871 := bstep (se 1 (by rfl) ⟨1573403, by rfl⟩ : syracuseStep 2097871 = 3146807) B3146807
theorem B3146813 : Blo 2097435 3146813 := bbase (se 3 (by rfl) ⟨590027, by rfl⟩ : syracuseStep 3146813 = 1180055) (by norm_num)
theorem B2097875 : Blo 2097435 2097875 := bstep (se 1 (by rfl) ⟨1573406, by rfl⟩ : syracuseStep 2097875 = 3146813) B3146813
theorem B4720229 : Blo 2097435 4720229 := bbase (se 4 (by rfl) ⟨442521, by rfl⟩ : syracuseStep 4720229 = 885043) (by norm_num)
theorem B3146819 : Blo 2097435 3146819 := bstep (se 1 (by rfl) ⟨2360114, by rfl⟩ : syracuseStep 3146819 = 4720229) B4720229
theorem B2097879 : Blo 2097435 2097879 := bstep (se 1 (by rfl) ⟨1573409, by rfl⟩ : syracuseStep 2097879 = 3146819) B3146819
theorem B5310269 : Blo 2097435 5310269 := bbase (se 3 (by rfl) ⟨995675, by rfl⟩ : syracuseStep 5310269 = 1991351) (by norm_num)
theorem B3540179 : Blo 2097435 3540179 := bstep (se 1 (by rfl) ⟨2655134, by rfl⟩ : syracuseStep 3540179 = 5310269) B5310269
theorem B2360119 : Blo 2097435 2360119 := bstep (se 1 (by rfl) ⟨1770089, by rfl⟩ : syracuseStep 2360119 = 3540179) B3540179
theorem B3146825 : Blo 2097435 3146825 := bstep (se 2 (by rfl) ⟨1180059, by rfl⟩ : syracuseStep 3146825 = 2360119) B2360119
theorem B2097883 : Blo 2097435 2097883 := bstep (se 1 (by rfl) ⟨1573412, by rfl⟩ : syracuseStep 2097883 = 3146825) B3146825
theorem B3982709 : Blo 2097435 3982709 := bbase (se 5 (by rfl) ⟨186689, by rfl⟩ : syracuseStep 3982709 = 373379) (by norm_num)
theorem B10620557 : Blo 2097435 10620557 := bstep (se 3 (by rfl) ⟨1991354, by rfl⟩ : syracuseStep 10620557 = 3982709) B3982709
theorem B7080371 : Blo 2097435 7080371 := bstep (se 1 (by rfl) ⟨5310278, by rfl⟩ : syracuseStep 7080371 = 10620557) B10620557
theorem B4720247 : Blo 2097435 4720247 := bstep (se 1 (by rfl) ⟨3540185, by rfl⟩ : syracuseStep 4720247 = 7080371) B7080371
theorem B3146831 : Blo 2097435 3146831 := bstep (se 1 (by rfl) ⟨2360123, by rfl⟩ : syracuseStep 3146831 = 4720247) B4720247
theorem B2097887 : Blo 2097435 2097887 := bstep (se 1 (by rfl) ⟨1573415, by rfl⟩ : syracuseStep 2097887 = 3146831) B3146831
theorem B3146837 : Blo 2097435 3146837 := bbase (se 8 (by rfl) ⟨18438, by rfl⟩ : syracuseStep 3146837 = 36877) (by norm_num)
theorem B2097891 : Blo 2097435 2097891 := bstep (se 1 (by rfl) ⟨1573418, by rfl⟩ : syracuseStep 2097891 = 3146837) B3146837
theorem B4849949 : Blo 2097435 4849949 := bbase (se 3 (by rfl) ⟨909365, by rfl⟩ : syracuseStep 4849949 = 1818731) (by norm_num)
theorem B3233299 : Blo 2097435 3233299 := bstep (se 1 (by rfl) ⟨2424974, by rfl⟩ : syracuseStep 3233299 = 4849949) B4849949
theorem B4311065 : Blo 2097435 4311065 := bstep (se 2 (by rfl) ⟨1616649, by rfl⟩ : syracuseStep 4311065 = 3233299) B3233299
theorem B2874043 : Blo 2097435 2874043 := bstep (se 1 (by rfl) ⟨2155532, by rfl⟩ : syracuseStep 2874043 = 4311065) B4311065
theorem B3832057 : Blo 2097435 3832057 := bstep (se 2 (by rfl) ⟨1437021, by rfl⟩ : syracuseStep 3832057 = 2874043) B2874043
theorem B5109409 : Blo 2097435 5109409 := bstep (se 2 (by rfl) ⟨1916028, by rfl⟩ : syracuseStep 5109409 = 3832057) B3832057
theorem B27250181 : Blo 2097435 27250181 := bstep (se 4 (by rfl) ⟨2554704, by rfl⟩ : syracuseStep 27250181 = 5109409) B5109409
theorem B18166787 : Blo 2097435 18166787 := bstep (se 1 (by rfl) ⟨13625090, by rfl⟩ : syracuseStep 18166787 = 27250181) B27250181
theorem B12111191 : Blo 2097435 12111191 := bstep (se 1 (by rfl) ⟨9083393, by rfl⟩ : syracuseStep 12111191 = 18166787) B18166787
theorem B8074127 : Blo 2097435 8074127 := bstep (se 1 (by rfl) ⟨6055595, by rfl⟩ : syracuseStep 8074127 = 12111191) B12111191
theorem B21531005 : Blo 2097435 21531005 := bstep (se 3 (by rfl) ⟨4037063, by rfl⟩ : syracuseStep 21531005 = 8074127) B8074127
theorem B14354003 : Blo 2097435 14354003 := bstep (se 1 (by rfl) ⟨10765502, by rfl⟩ : syracuseStep 14354003 = 21531005) B21531005
theorem B9569335 : Blo 2097435 9569335 := bstep (se 1 (by rfl) ⟨7177001, by rfl⟩ : syracuseStep 9569335 = 14354003) B14354003
theorem B12759113 : Blo 2097435 12759113 := bstep (se 2 (by rfl) ⟨4784667, by rfl⟩ : syracuseStep 12759113 = 9569335) B9569335
theorem B8506075 : Blo 2097435 8506075 := bstep (se 1 (by rfl) ⟨6379556, by rfl⟩ : syracuseStep 8506075 = 12759113) B12759113
theorem B11341433 : Blo 2097435 11341433 := bstep (se 2 (by rfl) ⟨4253037, by rfl⟩ : syracuseStep 11341433 = 8506075) B8506075
theorem B7560955 : Blo 2097435 7560955 := bstep (se 1 (by rfl) ⟨5670716, by rfl⟩ : syracuseStep 7560955 = 11341433) B11341433
theorem B10081273 : Blo 2097435 10081273 := bstep (se 2 (by rfl) ⟨3780477, by rfl⟩ : syracuseStep 10081273 = 7560955) B7560955
theorem B13441697 : Blo 2097435 13441697 := bstep (se 2 (by rfl) ⟨5040636, by rfl⟩ : syracuseStep 13441697 = 10081273) B10081273
theorem B8961131 : Blo 2097435 8961131 := bstep (se 1 (by rfl) ⟨6720848, by rfl⟩ : syracuseStep 8961131 = 13441697) B13441697
theorem B5974087 : Blo 2097435 5974087 := bstep (se 1 (by rfl) ⟨4480565, by rfl⟩ : syracuseStep 5974087 = 8961131) B8961131
theorem B7965449 : Blo 2097435 7965449 := bstep (se 2 (by rfl) ⟨2987043, by rfl⟩ : syracuseStep 7965449 = 5974087) B5974087
theorem B5310299 : Blo 2097435 5310299 := bstep (se 1 (by rfl) ⟨3982724, by rfl⟩ : syracuseStep 5310299 = 7965449) B7965449
theorem B3540199 : Blo 2097435 3540199 := bstep (se 1 (by rfl) ⟨2655149, by rfl⟩ : syracuseStep 3540199 = 5310299) B5310299
theorem B4720265 : Blo 2097435 4720265 := bstep (se 2 (by rfl) ⟨1770099, by rfl⟩ : syracuseStep 4720265 = 3540199) B3540199
theorem B3146843 : Blo 2097435 3146843 := bstep (se 1 (by rfl) ⟨2360132, by rfl⟩ : syracuseStep 3146843 = 4720265) B4720265
theorem B2097895 : Blo 2097435 2097895 := bstep (se 1 (by rfl) ⟨1573421, by rfl⟩ : syracuseStep 2097895 = 3146843) B3146843
theorem B2360137 : Blo 2097435 2360137 := bbase (se 2 (by rfl) ⟨885051, by rfl⟩ : syracuseStep 2360137 = 1770103) (by norm_num)
theorem B3146849 : Blo 2097435 3146849 := bstep (se 2 (by rfl) ⟨1180068, by rfl⟩ : syracuseStep 3146849 = 2360137) B2360137
theorem B2097899 : Blo 2097435 2097899 := bstep (se 1 (by rfl) ⟨1573424, by rfl⟩ : syracuseStep 2097899 = 3146849) B3146849
theorem B17012213 : Blo 2097435 17012213 := bbase (se 5 (by rfl) ⟨797447, by rfl⟩ : syracuseStep 17012213 = 1594895) (by norm_num)
theorem B11341475 : Blo 2097435 11341475 := bstep (se 1 (by rfl) ⟨8506106, by rfl⟩ : syracuseStep 11341475 = 17012213) B17012213
theorem B7560983 : Blo 2097435 7560983 := bstep (se 1 (by rfl) ⟨5670737, by rfl⟩ : syracuseStep 7560983 = 11341475) B11341475
theorem B20162621 : Blo 2097435 20162621 := bstep (se 3 (by rfl) ⟨3780491, by rfl⟩ : syracuseStep 20162621 = 7560983) B7560983
theorem B13441747 : Blo 2097435 13441747 := bstep (se 1 (by rfl) ⟨10081310, by rfl⟩ : syracuseStep 13441747 = 20162621) B20162621
theorem B17922329 : Blo 2097435 17922329 := bstep (se 2 (by rfl) ⟨6720873, by rfl⟩ : syracuseStep 17922329 = 13441747) B13441747
theorem B11948219 : Blo 2097435 11948219 := bstep (se 1 (by rfl) ⟨8961164, by rfl⟩ : syracuseStep 11948219 = 17922329) B17922329
theorem B7965479 : Blo 2097435 7965479 := bstep (se 1 (by rfl) ⟨5974109, by rfl⟩ : syracuseStep 7965479 = 11948219) B11948219
theorem B5310319 : Blo 2097435 5310319 := bstep (se 1 (by rfl) ⟨3982739, by rfl⟩ : syracuseStep 5310319 = 7965479) B7965479
theorem B7080425 : Blo 2097435 7080425 := bstep (se 2 (by rfl) ⟨2655159, by rfl⟩ : syracuseStep 7080425 = 5310319) B5310319
theorem B4720283 : Blo 2097435 4720283 := bstep (se 1 (by rfl) ⟨3540212, by rfl⟩ : syracuseStep 4720283 = 7080425) B7080425
theorem B3146855 : Blo 2097435 3146855 := bstep (se 1 (by rfl) ⟨2360141, by rfl⟩ : syracuseStep 3146855 = 4720283) B4720283
theorem B2097903 : Blo 2097435 2097903 := bstep (se 1 (by rfl) ⟨1573427, by rfl⟩ : syracuseStep 2097903 = 3146855) B3146855
theorem B3146861 : Blo 2097435 3146861 := bbase (se 3 (by rfl) ⟨590036, by rfl⟩ : syracuseStep 3146861 = 1180073) (by norm_num)
theorem B2097907 : Blo 2097435 2097907 := bstep (se 1 (by rfl) ⟨1573430, by rfl⟩ : syracuseStep 2097907 = 3146861) B3146861
theorem B4720301 : Blo 2097435 4720301 := bbase (se 3 (by rfl) ⟨885056, by rfl⟩ : syracuseStep 4720301 = 1770113) (by norm_num)
theorem B3146867 : Blo 2097435 3146867 := bstep (se 1 (by rfl) ⟨2360150, by rfl⟩ : syracuseStep 3146867 = 4720301) B4720301
theorem B2097911 : Blo 2097435 2097911 := bstep (se 1 (by rfl) ⟨1573433, by rfl⟩ : syracuseStep 2097911 = 3146867) B3146867
theorem B5670773 : Blo 2097435 5670773 := bbase (se 5 (by rfl) ⟨265817, by rfl⟩ : syracuseStep 5670773 = 531635) (by norm_num)
theorem B3780515 : Blo 2097435 3780515 := bstep (se 1 (by rfl) ⟨2835386, by rfl⟩ : syracuseStep 3780515 = 5670773) B5670773
theorem B2520343 : Blo 2097435 2520343 := bstep (se 1 (by rfl) ⟨1890257, by rfl⟩ : syracuseStep 2520343 = 3780515) B3780515
theorem B3360457 : Blo 2097435 3360457 := bstep (se 2 (by rfl) ⟨1260171, by rfl⟩ : syracuseStep 3360457 = 2520343) B2520343
theorem B4480609 : Blo 2097435 4480609 := bstep (se 2 (by rfl) ⟨1680228, by rfl⟩ : syracuseStep 4480609 = 3360457) B3360457
theorem B5974145 : Blo 2097435 5974145 := bstep (se 2 (by rfl) ⟨2240304, by rfl⟩ : syracuseStep 5974145 = 4480609) B4480609
theorem B3982763 : Blo 2097435 3982763 := bstep (se 1 (by rfl) ⟨2987072, by rfl⟩ : syracuseStep 3982763 = 5974145) B5974145
theorem B2655175 : Blo 2097435 2655175 := bstep (se 1 (by rfl) ⟨1991381, by rfl⟩ : syracuseStep 2655175 = 3982763) B3982763
theorem B3540233 : Blo 2097435 3540233 := bstep (se 2 (by rfl) ⟨1327587, by rfl⟩ : syracuseStep 3540233 = 2655175) B2655175
theorem B2360155 : Blo 2097435 2360155 := bstep (se 1 (by rfl) ⟨1770116, by rfl⟩ : syracuseStep 2360155 = 3540233) B3540233
theorem B3146873 : Blo 2097435 3146873 := bstep (se 2 (by rfl) ⟨1180077, by rfl⟩ : syracuseStep 3146873 = 2360155) B2360155
theorem B2097915 : Blo 2097435 2097915 := bstep (se 1 (by rfl) ⟨1573436, by rfl⟩ : syracuseStep 2097915 = 3146873) B3146873
theorem B20162773 : Blo 2097435 20162773 := bbase (se 7 (by rfl) ⟨236282, by rfl⟩ : syracuseStep 20162773 = 472565) (by norm_num)
theorem B26883697 : Blo 2097435 26883697 := bstep (se 2 (by rfl) ⟨10081386, by rfl⟩ : syracuseStep 26883697 = 20162773) B20162773
theorem B35844929 : Blo 2097435 35844929 := bstep (se 2 (by rfl) ⟨13441848, by rfl⟩ : syracuseStep 35844929 = 26883697) B26883697
theorem B23896619 : Blo 2097435 23896619 := bstep (se 1 (by rfl) ⟨17922464, by rfl⟩ : syracuseStep 23896619 = 35844929) B35844929
theorem B15931079 : Blo 2097435 15931079 := bstep (se 1 (by rfl) ⟨11948309, by rfl⟩ : syracuseStep 15931079 = 23896619) B23896619
theorem B10620719 : Blo 2097435 10620719 := bstep (se 1 (by rfl) ⟨7965539, by rfl⟩ : syracuseStep 10620719 = 15931079) B15931079
theorem B7080479 : Blo 2097435 7080479 := bstep (se 1 (by rfl) ⟨5310359, by rfl⟩ : syracuseStep 7080479 = 10620719) B10620719
theorem B4720319 : Blo 2097435 4720319 := bstep (se 1 (by rfl) ⟨3540239, by rfl⟩ : syracuseStep 4720319 = 7080479) B7080479
theorem B3146879 : Blo 2097435 3146879 := bstep (se 1 (by rfl) ⟨2360159, by rfl⟩ : syracuseStep 3146879 = 4720319) B4720319
theorem B2097919 : Blo 2097435 2097919 := bstep (se 1 (by rfl) ⟨1573439, by rfl⟩ : syracuseStep 2097919 = 3146879) B3146879
theorem B3146885 : Blo 2097435 3146885 := bbase (se 4 (by rfl) ⟨295020, by rfl⟩ : syracuseStep 3146885 = 590041) (by norm_num)
theorem B2097923 : Blo 2097435 2097923 := bstep (se 1 (by rfl) ⟨1573442, by rfl⟩ : syracuseStep 2097923 = 3146885) B3146885
theorem B3540253 : Blo 2097435 3540253 := bbase (se 3 (by rfl) ⟨663797, by rfl⟩ : syracuseStep 3540253 = 1327595) (by norm_num)
theorem B4720337 : Blo 2097435 4720337 := bstep (se 2 (by rfl) ⟨1770126, by rfl⟩ : syracuseStep 4720337 = 3540253) B3540253
theorem B3146891 : Blo 2097435 3146891 := bstep (se 1 (by rfl) ⟨2360168, by rfl⟩ : syracuseStep 3146891 = 4720337) B4720337
theorem B2097927 : Blo 2097435 2097927 := bstep (se 1 (by rfl) ⟨1573445, by rfl⟩ : syracuseStep 2097927 = 3146891) B3146891
theorem B2360173 : Blo 2097435 2360173 := bbase (se 3 (by rfl) ⟨442532, by rfl⟩ : syracuseStep 2360173 = 885065) (by norm_num)
theorem B3146897 : Blo 2097435 3146897 := bstep (se 2 (by rfl) ⟨1180086, by rfl⟩ : syracuseStep 3146897 = 2360173) B2360173
theorem B2097931 : Blo 2097435 2097931 := bstep (se 1 (by rfl) ⟨1573448, by rfl⟩ : syracuseStep 2097931 = 3146897) B3146897
theorem B7080533 : Blo 2097435 7080533 := bbase (se 8 (by rfl) ⟨41487, by rfl⟩ : syracuseStep 7080533 = 82975) (by norm_num)
theorem B4720355 : Blo 2097435 4720355 := bstep (se 1 (by rfl) ⟨3540266, by rfl⟩ : syracuseStep 4720355 = 7080533) B7080533
theorem B3146903 : Blo 2097435 3146903 := bstep (se 1 (by rfl) ⟨2360177, by rfl⟩ : syracuseStep 3146903 = 4720355) B4720355
theorem B2097935 : Blo 2097435 2097935 := bstep (se 1 (by rfl) ⟨1573451, by rfl⟩ : syracuseStep 2097935 = 3146903) B3146903
theorem B3146909 : Blo 2097435 3146909 := bbase (se 3 (by rfl) ⟨590045, by rfl⟩ : syracuseStep 3146909 = 1180091) (by norm_num)
theorem B2097939 : Blo 2097435 2097939 := bstep (se 1 (by rfl) ⟨1573454, by rfl⟩ : syracuseStep 2097939 = 3146909) B3146909
theorem B4720373 : Blo 2097435 4720373 := bbase (se 5 (by rfl) ⟨221267, by rfl⟩ : syracuseStep 4720373 = 442535) (by norm_num)
theorem B3146915 : Blo 2097435 3146915 := bstep (se 1 (by rfl) ⟨2360186, by rfl⟩ : syracuseStep 3146915 = 4720373) B4720373
theorem B2097943 : Blo 2097435 2097943 := bstep (se 1 (by rfl) ⟨1573457, by rfl⟩ : syracuseStep 2097943 = 3146915) B3146915
theorem B9569573 : Blo 2097435 9569573 := bbase (se 4 (by rfl) ⟨897147, by rfl⟩ : syracuseStep 9569573 = 1794295) (by norm_num)
theorem B6379715 : Blo 2097435 6379715 := bstep (se 1 (by rfl) ⟨4784786, by rfl⟩ : syracuseStep 6379715 = 9569573) B9569573
theorem B4253143 : Blo 2097435 4253143 := bstep (se 1 (by rfl) ⟨3189857, by rfl⟩ : syracuseStep 4253143 = 6379715) B6379715
theorem B5670857 : Blo 2097435 5670857 := bstep (se 2 (by rfl) ⟨2126571, by rfl⟩ : syracuseStep 5670857 = 4253143) B4253143
theorem B15122285 : Blo 2097435 15122285 := bstep (se 3 (by rfl) ⟨2835428, by rfl⟩ : syracuseStep 15122285 = 5670857) B5670857
theorem B10081523 : Blo 2097435 10081523 := bstep (se 1 (by rfl) ⟨7561142, by rfl⟩ : syracuseStep 10081523 = 15122285) B15122285
theorem B26884061 : Blo 2097435 26884061 := bstep (se 3 (by rfl) ⟨5040761, by rfl⟩ : syracuseStep 26884061 = 10081523) B10081523
theorem B17922707 : Blo 2097435 17922707 := bstep (se 1 (by rfl) ⟨13442030, by rfl⟩ : syracuseStep 17922707 = 26884061) B26884061
theorem B11948471 : Blo 2097435 11948471 := bstep (se 1 (by rfl) ⟨8961353, by rfl⟩ : syracuseStep 11948471 = 17922707) B17922707
theorem B7965647 : Blo 2097435 7965647 := bstep (se 1 (by rfl) ⟨5974235, by rfl⟩ : syracuseStep 7965647 = 11948471) B11948471
theorem B5310431 : Blo 2097435 5310431 := bstep (se 1 (by rfl) ⟨3982823, by rfl⟩ : syracuseStep 5310431 = 7965647) B7965647
theorem B3540287 : Blo 2097435 3540287 := bstep (se 1 (by rfl) ⟨2655215, by rfl⟩ : syracuseStep 3540287 = 5310431) B5310431
theorem B2360191 : Blo 2097435 2360191 := bstep (se 1 (by rfl) ⟨1770143, by rfl⟩ : syracuseStep 2360191 = 3540287) B3540287
theorem B3146921 : Blo 2097435 3146921 := bstep (se 2 (by rfl) ⟨1180095, by rfl⟩ : syracuseStep 3146921 = 2360191) B2360191
theorem B2097947 : Blo 2097435 2097947 := bstep (se 1 (by rfl) ⟨1573460, by rfl⟩ : syracuseStep 2097947 = 3146921) B3146921
theorem B4480685 : Blo 2097435 4480685 := bbase (se 3 (by rfl) ⟨840128, by rfl⟩ : syracuseStep 4480685 = 1680257) (by norm_num)
theorem B2987123 : Blo 2097435 2987123 := bstep (se 1 (by rfl) ⟨2240342, by rfl⟩ : syracuseStep 2987123 = 4480685) B4480685
theorem B7965661 : Blo 2097435 7965661 := bstep (se 3 (by rfl) ⟨1493561, by rfl⟩ : syracuseStep 7965661 = 2987123) B2987123
theorem B10620881 : Blo 2097435 10620881 := bstep (se 2 (by rfl) ⟨3982830, by rfl⟩ : syracuseStep 10620881 = 7965661) B7965661
theorem B7080587 : Blo 2097435 7080587 := bstep (se 1 (by rfl) ⟨5310440, by rfl⟩ : syracuseStep 7080587 = 10620881) B10620881
theorem B4720391 : Blo 2097435 4720391 := bstep (se 1 (by rfl) ⟨3540293, by rfl⟩ : syracuseStep 4720391 = 7080587) B7080587
theorem B3146927 : Blo 2097435 3146927 := bstep (se 1 (by rfl) ⟨2360195, by rfl⟩ : syracuseStep 3146927 = 4720391) B4720391
theorem B2097951 : Blo 2097435 2097951 := bstep (se 1 (by rfl) ⟨1573463, by rfl⟩ : syracuseStep 2097951 = 3146927) B3146927
theorem B3146933 : Blo 2097435 3146933 := bbase (se 5 (by rfl) ⟨147512, by rfl⟩ : syracuseStep 3146933 = 295025) (by norm_num)
theorem B2097955 : Blo 2097435 2097955 := bstep (se 1 (by rfl) ⟨1573466, by rfl⟩ : syracuseStep 2097955 = 3146933) B3146933
theorem B5310461 : Blo 2097435 5310461 := bbase (se 3 (by rfl) ⟨995711, by rfl⟩ : syracuseStep 5310461 = 1991423) (by norm_num)
theorem B3540307 : Blo 2097435 3540307 := bstep (se 1 (by rfl) ⟨2655230, by rfl⟩ : syracuseStep 3540307 = 5310461) B5310461
theorem B4720409 : Blo 2097435 4720409 := bstep (se 2 (by rfl) ⟨1770153, by rfl⟩ : syracuseStep 4720409 = 3540307) B3540307
theorem B3146939 : Blo 2097435 3146939 := bstep (se 1 (by rfl) ⟨2360204, by rfl⟩ : syracuseStep 3146939 = 4720409) B4720409
theorem B2097959 : Blo 2097435 2097959 := bstep (se 1 (by rfl) ⟨1573469, by rfl⟩ : syracuseStep 2097959 = 3146939) B3146939
theorem B2360209 : Blo 2097435 2360209 := bbase (se 2 (by rfl) ⟨885078, by rfl⟩ : syracuseStep 2360209 = 1770157) (by norm_num)
theorem B3146945 : Blo 2097435 3146945 := bstep (se 2 (by rfl) ⟨1180104, by rfl⟩ : syracuseStep 3146945 = 2360209) B2360209
theorem B2097963 : Blo 2097435 2097963 := bstep (se 1 (by rfl) ⟨1573472, by rfl⟩ : syracuseStep 2097963 = 3146945) B3146945
theorem B3982861 : Blo 2097435 3982861 := bbase (se 3 (by rfl) ⟨746786, by rfl⟩ : syracuseStep 3982861 = 1493573) (by norm_num)
theorem B5310481 : Blo 2097435 5310481 := bstep (se 2 (by rfl) ⟨1991430, by rfl⟩ : syracuseStep 5310481 = 3982861) B3982861
theorem B7080641 : Blo 2097435 7080641 := bstep (se 2 (by rfl) ⟨2655240, by rfl⟩ : syracuseStep 7080641 = 5310481) B5310481
theorem B4720427 : Blo 2097435 4720427 := bstep (se 1 (by rfl) ⟨3540320, by rfl⟩ : syracuseStep 4720427 = 7080641) B7080641
theorem B3146951 : Blo 2097435 3146951 := bstep (se 1 (by rfl) ⟨2360213, by rfl⟩ : syracuseStep 3146951 = 4720427) B4720427
theorem B2097967 : Blo 2097435 2097967 := bstep (se 1 (by rfl) ⟨1573475, by rfl⟩ : syracuseStep 2097967 = 3146951) B3146951
theorem B3146957 : Blo 2097435 3146957 := bbase (se 3 (by rfl) ⟨590054, by rfl⟩ : syracuseStep 3146957 = 1180109) (by norm_num)
theorem B2097971 : Blo 2097435 2097971 := bstep (se 1 (by rfl) ⟨1573478, by rfl⟩ : syracuseStep 2097971 = 3146957) B3146957
theorem B4720445 : Blo 2097435 4720445 := bbase (se 3 (by rfl) ⟨885083, by rfl⟩ : syracuseStep 4720445 = 1770167) (by norm_num)
theorem B3146963 : Blo 2097435 3146963 := bstep (se 1 (by rfl) ⟨2360222, by rfl⟩ : syracuseStep 3146963 = 4720445) B4720445
theorem B2097975 : Blo 2097435 2097975 := bstep (se 1 (by rfl) ⟨1573481, by rfl⟩ : syracuseStep 2097975 = 3146963) B3146963
theorem B3540341 : Blo 2097435 3540341 := bbase (se 5 (by rfl) ⟨165953, by rfl⟩ : syracuseStep 3540341 = 331907) (by norm_num)
theorem B2360227 : Blo 2097435 2360227 := bstep (se 1 (by rfl) ⟨1770170, by rfl⟩ : syracuseStep 2360227 = 3540341) B3540341
theorem B3146969 : Blo 2097435 3146969 := bstep (se 2 (by rfl) ⟨1180113, by rfl⟩ : syracuseStep 3146969 = 2360227) B2360227
theorem B2097979 : Blo 2097435 2097979 := bstep (se 1 (by rfl) ⟨1573484, by rfl⟩ : syracuseStep 2097979 = 3146969) B3146969
theorem B3360565 : Blo 2097435 3360565 := bbase (se 5 (by rfl) ⟨157526, by rfl⟩ : syracuseStep 3360565 = 315053) (by norm_num)
theorem B4480753 : Blo 2097435 4480753 := bstep (se 2 (by rfl) ⟨1680282, by rfl⟩ : syracuseStep 4480753 = 3360565) B3360565
theorem B5974337 : Blo 2097435 5974337 := bstep (se 2 (by rfl) ⟨2240376, by rfl⟩ : syracuseStep 5974337 = 4480753) B4480753
theorem B15931565 : Blo 2097435 15931565 := bstep (se 3 (by rfl) ⟨2987168, by rfl⟩ : syracuseStep 15931565 = 5974337) B5974337
theorem B10621043 : Blo 2097435 10621043 := bstep (se 1 (by rfl) ⟨7965782, by rfl⟩ : syracuseStep 10621043 = 15931565) B15931565
theorem B7080695 : Blo 2097435 7080695 := bstep (se 1 (by rfl) ⟨5310521, by rfl⟩ : syracuseStep 7080695 = 10621043) B10621043
theorem B4720463 : Blo 2097435 4720463 := bstep (se 1 (by rfl) ⟨3540347, by rfl⟩ : syracuseStep 4720463 = 7080695) B7080695
theorem B3146975 : Blo 2097435 3146975 := bstep (se 1 (by rfl) ⟨2360231, by rfl⟩ : syracuseStep 3146975 = 4720463) B4720463
theorem B2097983 : Blo 2097435 2097983 := bstep (se 1 (by rfl) ⟨1573487, by rfl⟩ : syracuseStep 2097983 = 3146975) B3146975
theorem B3146981 : Blo 2097435 3146981 := bbase (se 4 (by rfl) ⟨295029, by rfl⟩ : syracuseStep 3146981 = 590059) (by norm_num)
theorem B2097987 : Blo 2097435 2097987 := bstep (se 1 (by rfl) ⟨1573490, by rfl⟩ : syracuseStep 2097987 = 3146981) B3146981
theorem B6721157 : Blo 2097435 6721157 := bbase (se 4 (by rfl) ⟨630108, by rfl⟩ : syracuseStep 6721157 = 1260217) (by norm_num)
theorem B4480771 : Blo 2097435 4480771 := bstep (se 1 (by rfl) ⟨3360578, by rfl⟩ : syracuseStep 4480771 = 6721157) B6721157
theorem B5974361 : Blo 2097435 5974361 := bstep (se 2 (by rfl) ⟨2240385, by rfl⟩ : syracuseStep 5974361 = 4480771) B4480771
theorem B3982907 : Blo 2097435 3982907 := bstep (se 1 (by rfl) ⟨2987180, by rfl⟩ : syracuseStep 3982907 = 5974361) B5974361
theorem B2655271 : Blo 2097435 2655271 := bstep (se 1 (by rfl) ⟨1991453, by rfl⟩ : syracuseStep 2655271 = 3982907) B3982907
theorem B3540361 : Blo 2097435 3540361 := bstep (se 2 (by rfl) ⟨1327635, by rfl⟩ : syracuseStep 3540361 = 2655271) B2655271
theorem B4720481 : Blo 2097435 4720481 := bstep (se 2 (by rfl) ⟨1770180, by rfl⟩ : syracuseStep 4720481 = 3540361) B3540361
theorem B3146987 : Blo 2097435 3146987 := bstep (se 1 (by rfl) ⟨2360240, by rfl⟩ : syracuseStep 3146987 = 4720481) B4720481
theorem B2097991 : Blo 2097435 2097991 := bstep (se 1 (by rfl) ⟨1573493, by rfl⟩ : syracuseStep 2097991 = 3146987) B3146987
theorem B2360245 : Blo 2097435 2360245 := bbase (se 5 (by rfl) ⟨110636, by rfl⟩ : syracuseStep 2360245 = 221273) (by norm_num)
theorem B3146993 : Blo 2097435 3146993 := bstep (se 2 (by rfl) ⟨1180122, by rfl⟩ : syracuseStep 3146993 = 2360245) B2360245
theorem B2097995 : Blo 2097435 2097995 := bstep (se 1 (by rfl) ⟨1573496, by rfl⟩ : syracuseStep 2097995 = 3146993) B3146993
theorem B2655281 : Blo 2097435 2655281 := bbase (se 2 (by rfl) ⟨995730, by rfl⟩ : syracuseStep 2655281 = 1991461) (by norm_num)
theorem B7080749 : Blo 2097435 7080749 := bstep (se 3 (by rfl) ⟨1327640, by rfl⟩ : syracuseStep 7080749 = 2655281) B2655281
theorem B4720499 : Blo 2097435 4720499 := bstep (se 1 (by rfl) ⟨3540374, by rfl⟩ : syracuseStep 4720499 = 7080749) B7080749
theorem B3146999 : Blo 2097435 3146999 := bstep (se 1 (by rfl) ⟨2360249, by rfl⟩ : syracuseStep 3146999 = 4720499) B4720499
theorem B2097999 : Blo 2097435 2097999 := bstep (se 1 (by rfl) ⟨1573499, by rfl⟩ : syracuseStep 2097999 = 3146999) B3146999
theorem B3147005 : Blo 2097435 3147005 := bbase (se 3 (by rfl) ⟨590063, by rfl⟩ : syracuseStep 3147005 = 1180127) (by norm_num)
theorem B2098003 : Blo 2097435 2098003 := bstep (se 1 (by rfl) ⟨1573502, by rfl⟩ : syracuseStep 2098003 = 3147005) B3147005
theorem B4720517 : Blo 2097435 4720517 := bbase (se 4 (by rfl) ⟨442548, by rfl⟩ : syracuseStep 4720517 = 885097) (by norm_num)
theorem B3147011 : Blo 2097435 3147011 := bstep (se 1 (by rfl) ⟨2360258, by rfl⟩ : syracuseStep 3147011 = 4720517) B4720517
theorem B2098007 : Blo 2097435 2098007 := bstep (se 1 (by rfl) ⟨1573505, by rfl⟩ : syracuseStep 2098007 = 3147011) B3147011
theorem B5040917 : Blo 2097435 5040917 := bbase (se 6 (by rfl) ⟨118146, by rfl⟩ : syracuseStep 5040917 = 236293) (by norm_num)
theorem B3360611 : Blo 2097435 3360611 := bstep (se 1 (by rfl) ⟨2520458, by rfl⟩ : syracuseStep 3360611 = 5040917) B5040917
theorem B2240407 : Blo 2097435 2240407 := bstep (se 1 (by rfl) ⟨1680305, by rfl⟩ : syracuseStep 2240407 = 3360611) B3360611
theorem B2987209 : Blo 2097435 2987209 := bstep (se 2 (by rfl) ⟨1120203, by rfl⟩ : syracuseStep 2987209 = 2240407) B2240407
theorem B3982945 : Blo 2097435 3982945 := bstep (se 2 (by rfl) ⟨1493604, by rfl⟩ : syracuseStep 3982945 = 2987209) B2987209
theorem B5310593 : Blo 2097435 5310593 := bstep (se 2 (by rfl) ⟨1991472, by rfl⟩ : syracuseStep 5310593 = 3982945) B3982945
theorem B3540395 : Blo 2097435 3540395 := bstep (se 1 (by rfl) ⟨2655296, by rfl⟩ : syracuseStep 3540395 = 5310593) B5310593
theorem B2360263 : Blo 2097435 2360263 := bstep (se 1 (by rfl) ⟨1770197, by rfl⟩ : syracuseStep 2360263 = 3540395) B3540395
theorem B3147017 : Blo 2097435 3147017 := bstep (se 2 (by rfl) ⟨1180131, by rfl⟩ : syracuseStep 3147017 = 2360263) B2360263
theorem B2098011 : Blo 2097435 2098011 := bstep (se 1 (by rfl) ⟨1573508, by rfl⟩ : syracuseStep 2098011 = 3147017) B3147017
theorem B10621205 : Blo 2097435 10621205 := bbase (se 6 (by rfl) ⟨248934, by rfl⟩ : syracuseStep 10621205 = 497869) (by norm_num)
theorem B7080803 : Blo 2097435 7080803 := bstep (se 1 (by rfl) ⟨5310602, by rfl⟩ : syracuseStep 7080803 = 10621205) B10621205
theorem B4720535 : Blo 2097435 4720535 := bstep (se 1 (by rfl) ⟨3540401, by rfl⟩ : syracuseStep 4720535 = 7080803) B7080803
theorem B3147023 : Blo 2097435 3147023 := bstep (se 1 (by rfl) ⟨2360267, by rfl⟩ : syracuseStep 3147023 = 4720535) B4720535
theorem B2098015 : Blo 2097435 2098015 := bstep (se 1 (by rfl) ⟨1573511, by rfl⟩ : syracuseStep 2098015 = 3147023) B3147023
theorem B3147029 : Blo 2097435 3147029 := bbase (se 6 (by rfl) ⟨73758, by rfl⟩ : syracuseStep 3147029 = 147517) (by norm_num)
theorem B2098019 : Blo 2097435 2098019 := bstep (se 1 (by rfl) ⟨1573514, by rfl⟩ : syracuseStep 2098019 = 3147029) B3147029
theorem B2425121 : Blo 2097435 2425121 := bbase (se 2 (by rfl) ⟨909420, by rfl⟩ : syracuseStep 2425121 = 1818841) (by norm_num)
theorem B25867957 : Blo 2097435 25867957 := bstep (se 5 (by rfl) ⟨1212560, by rfl⟩ : syracuseStep 25867957 = 2425121) B2425121
theorem B34490609 : Blo 2097435 34490609 := bstep (se 2 (by rfl) ⟨12933978, by rfl⟩ : syracuseStep 34490609 = 25867957) B25867957
theorem B22993739 : Blo 2097435 22993739 := bstep (se 1 (by rfl) ⟨17245304, by rfl⟩ : syracuseStep 22993739 = 34490609) B34490609
theorem B15329159 : Blo 2097435 15329159 := bstep (se 1 (by rfl) ⟨11496869, by rfl⟩ : syracuseStep 15329159 = 22993739) B22993739
theorem B10219439 : Blo 2097435 10219439 := bstep (se 1 (by rfl) ⟨7664579, by rfl⟩ : syracuseStep 10219439 = 15329159) B15329159
theorem B6812959 : Blo 2097435 6812959 := bstep (se 1 (by rfl) ⟨5109719, by rfl⟩ : syracuseStep 6812959 = 10219439) B10219439
theorem B9083945 : Blo 2097435 9083945 := bstep (se 2 (by rfl) ⟨3406479, by rfl⟩ : syracuseStep 9083945 = 6812959) B6812959
theorem B24223853 : Blo 2097435 24223853 := bstep (se 3 (by rfl) ⟨4541972, by rfl⟩ : syracuseStep 24223853 = 9083945) B9083945
theorem B64596941 : Blo 2097435 64596941 := bstep (se 3 (by rfl) ⟨12111926, by rfl⟩ : syracuseStep 64596941 = 24223853) B24223853
theorem B43064627 : Blo 2097435 43064627 := bstep (se 1 (by rfl) ⟨32298470, by rfl⟩ : syracuseStep 43064627 = 64596941) B64596941
theorem B114839005 : Blo 2097435 114839005 := bstep (se 3 (by rfl) ⟨21532313, by rfl⟩ : syracuseStep 114839005 = 43064627) B43064627
theorem B153118673 : Blo 2097435 153118673 := bstep (se 2 (by rfl) ⟨57419502, by rfl⟩ : syracuseStep 153118673 = 114839005) B114839005
theorem B102079115 : Blo 2097435 102079115 := bstep (se 1 (by rfl) ⟨76559336, by rfl⟩ : syracuseStep 102079115 = 153118673) B153118673
theorem B68052743 : Blo 2097435 68052743 := bstep (se 1 (by rfl) ⟨51039557, by rfl⟩ : syracuseStep 68052743 = 102079115) B102079115
theorem B45368495 : Blo 2097435 45368495 := bstep (se 1 (by rfl) ⟨34026371, by rfl⟩ : syracuseStep 45368495 = 68052743) B68052743
theorem B30245663 : Blo 2097435 30245663 := bstep (se 1 (by rfl) ⟨22684247, by rfl⟩ : syracuseStep 30245663 = 45368495) B45368495
theorem B20163775 : Blo 2097435 20163775 := bstep (se 1 (by rfl) ⟨15122831, by rfl⟩ : syracuseStep 20163775 = 30245663) B30245663
theorem B26885033 : Blo 2097435 26885033 := bstep (se 2 (by rfl) ⟨10081887, by rfl⟩ : syracuseStep 26885033 = 20163775) B20163775
theorem B17923355 : Blo 2097435 17923355 := bstep (se 1 (by rfl) ⟨13442516, by rfl⟩ : syracuseStep 17923355 = 26885033) B26885033
theorem B11948903 : Blo 2097435 11948903 := bstep (se 1 (by rfl) ⟨8961677, by rfl⟩ : syracuseStep 11948903 = 17923355) B17923355
theorem B7965935 : Blo 2097435 7965935 := bstep (se 1 (by rfl) ⟨5974451, by rfl⟩ : syracuseStep 7965935 = 11948903) B11948903
theorem B5310623 : Blo 2097435 5310623 := bstep (se 1 (by rfl) ⟨3982967, by rfl⟩ : syracuseStep 5310623 = 7965935) B7965935
theorem B3540415 : Blo 2097435 3540415 := bstep (se 1 (by rfl) ⟨2655311, by rfl⟩ : syracuseStep 3540415 = 5310623) B5310623
theorem B4720553 : Blo 2097435 4720553 := bstep (se 2 (by rfl) ⟨1770207, by rfl⟩ : syracuseStep 4720553 = 3540415) B3540415
theorem B3147035 : Blo 2097435 3147035 := bstep (se 1 (by rfl) ⟨2360276, by rfl⟩ : syracuseStep 3147035 = 4720553) B4720553
theorem B2098023 : Blo 2097435 2098023 := bstep (se 1 (by rfl) ⟨1573517, by rfl⟩ : syracuseStep 2098023 = 3147035) B3147035
theorem B2360281 : Blo 2097435 2360281 := bbase (se 2 (by rfl) ⟨885105, by rfl⟩ : syracuseStep 2360281 = 1770211) (by norm_num)
theorem B3147041 : Blo 2097435 3147041 := bstep (se 2 (by rfl) ⟨1180140, by rfl⟩ : syracuseStep 3147041 = 2360281) B2360281
theorem B2098027 : Blo 2097435 2098027 := bstep (se 1 (by rfl) ⟨1573520, by rfl⟩ : syracuseStep 2098027 = 3147041) B3147041
theorem B2987237 : Blo 2097435 2987237 := bbase (se 4 (by rfl) ⟨280053, by rfl⟩ : syracuseStep 2987237 = 560107) (by norm_num)
theorem B7965965 : Blo 2097435 7965965 := bstep (se 3 (by rfl) ⟨1493618, by rfl⟩ : syracuseStep 7965965 = 2987237) B2987237
theorem B5310643 : Blo 2097435 5310643 := bstep (se 1 (by rfl) ⟨3982982, by rfl⟩ : syracuseStep 5310643 = 7965965) B7965965
theorem B7080857 : Blo 2097435 7080857 := bstep (se 2 (by rfl) ⟨2655321, by rfl⟩ : syracuseStep 7080857 = 5310643) B5310643
theorem B4720571 : Blo 2097435 4720571 := bstep (se 1 (by rfl) ⟨3540428, by rfl⟩ : syracuseStep 4720571 = 7080857) B7080857
theorem B3147047 : Blo 2097435 3147047 := bstep (se 1 (by rfl) ⟨2360285, by rfl⟩ : syracuseStep 3147047 = 4720571) B4720571
theorem B2098031 : Blo 2097435 2098031 := bstep (se 1 (by rfl) ⟨1573523, by rfl⟩ : syracuseStep 2098031 = 3147047) B3147047
theorem B3147053 : Blo 2097435 3147053 := bbase (se 3 (by rfl) ⟨590072, by rfl⟩ : syracuseStep 3147053 = 1180145) (by norm_num)
theorem B2098035 : Blo 2097435 2098035 := bstep (se 1 (by rfl) ⟨1573526, by rfl⟩ : syracuseStep 2098035 = 3147053) B3147053
theorem B4720589 : Blo 2097435 4720589 := bbase (se 3 (by rfl) ⟨885110, by rfl⟩ : syracuseStep 4720589 = 1770221) (by norm_num)
theorem B3147059 : Blo 2097435 3147059 := bstep (se 1 (by rfl) ⟨2360294, by rfl⟩ : syracuseStep 3147059 = 4720589) B4720589
theorem B2098039 : Blo 2097435 2098039 := bstep (se 1 (by rfl) ⟨1573529, by rfl⟩ : syracuseStep 2098039 = 3147059) B3147059
theorem B2655337 : Blo 2097435 2655337 := bbase (se 2 (by rfl) ⟨995751, by rfl⟩ : syracuseStep 2655337 = 1991503) (by norm_num)
theorem B3540449 : Blo 2097435 3540449 := bstep (se 2 (by rfl) ⟨1327668, by rfl⟩ : syracuseStep 3540449 = 2655337) B2655337
theorem B2360299 : Blo 2097435 2360299 := bstep (se 1 (by rfl) ⟨1770224, by rfl⟩ : syracuseStep 2360299 = 3540449) B3540449
theorem B3147065 : Blo 2097435 3147065 := bstep (se 2 (by rfl) ⟨1180149, by rfl⟩ : syracuseStep 3147065 = 2360299) B2360299
theorem B2098043 : Blo 2097435 2098043 := bstep (se 1 (by rfl) ⟨1573532, by rfl⟩ : syracuseStep 2098043 = 3147065) B3147065
theorem B4037357 : Blo 2097435 4037357 := bbase (se 3 (by rfl) ⟨757004, by rfl⟩ : syracuseStep 4037357 = 1514009) (by norm_num)
theorem B2691571 : Blo 2097435 2691571 := bstep (se 1 (by rfl) ⟨2018678, by rfl⟩ : syracuseStep 2691571 = 4037357) B4037357
theorem B3588761 : Blo 2097435 3588761 := bstep (se 2 (by rfl) ⟨1345785, by rfl⟩ : syracuseStep 3588761 = 2691571) B2691571
theorem B2392507 : Blo 2097435 2392507 := bstep (se 1 (by rfl) ⟨1794380, by rfl⟩ : syracuseStep 2392507 = 3588761) B3588761
theorem B12760037 : Blo 2097435 12760037 := bstep (se 4 (by rfl) ⟨1196253, by rfl⟩ : syracuseStep 12760037 = 2392507) B2392507
theorem B8506691 : Blo 2097435 8506691 := bstep (se 1 (by rfl) ⟨6380018, by rfl⟩ : syracuseStep 8506691 = 12760037) B12760037
theorem B5671127 : Blo 2097435 5671127 := bstep (se 1 (by rfl) ⟨4253345, by rfl⟩ : syracuseStep 5671127 = 8506691) B8506691
theorem B3780751 : Blo 2097435 3780751 := bstep (se 1 (by rfl) ⟨2835563, by rfl⟩ : syracuseStep 3780751 = 5671127) B5671127
theorem B5041001 : Blo 2097435 5041001 := bstep (se 2 (by rfl) ⟨1890375, by rfl⟩ : syracuseStep 5041001 = 3780751) B3780751
theorem B13442669 : Blo 2097435 13442669 := bstep (se 3 (by rfl) ⟨2520500, by rfl⟩ : syracuseStep 13442669 = 5041001) B5041001
theorem B8961779 : Blo 2097435 8961779 := bstep (se 1 (by rfl) ⟨6721334, by rfl⟩ : syracuseStep 8961779 = 13442669) B13442669
theorem B23898077 : Blo 2097435 23898077 := bstep (se 3 (by rfl) ⟨4480889, by rfl⟩ : syracuseStep 23898077 = 8961779) B8961779
theorem B15932051 : Blo 2097435 15932051 := bstep (se 1 (by rfl) ⟨11949038, by rfl⟩ : syracuseStep 15932051 = 23898077) B23898077
theorem B10621367 : Blo 2097435 10621367 := bstep (se 1 (by rfl) ⟨7966025, by rfl⟩ : syracuseStep 10621367 = 15932051) B15932051
theorem B7080911 : Blo 2097435 7080911 := bstep (se 1 (by rfl) ⟨5310683, by rfl⟩ : syracuseStep 7080911 = 10621367) B10621367
theorem B4720607 : Blo 2097435 4720607 := bstep (se 1 (by rfl) ⟨3540455, by rfl⟩ : syracuseStep 4720607 = 7080911) B7080911
theorem B3147071 : Blo 2097435 3147071 := bstep (se 1 (by rfl) ⟨2360303, by rfl⟩ : syracuseStep 3147071 = 4720607) B4720607
theorem B2098047 : Blo 2097435 2098047 := bstep (se 1 (by rfl) ⟨1573535, by rfl⟩ : syracuseStep 2098047 = 3147071) B3147071
theorem B3147077 : Blo 2097435 3147077 := bbase (se 4 (by rfl) ⟨295038, by rfl⟩ : syracuseStep 3147077 = 590077) (by norm_num)
theorem B2098051 : Blo 2097435 2098051 := bstep (se 1 (by rfl) ⟨1573538, by rfl⟩ : syracuseStep 2098051 = 3147077) B3147077
theorem B3540469 : Blo 2097435 3540469 := bbase (se 5 (by rfl) ⟨165959, by rfl⟩ : syracuseStep 3540469 = 331919) (by norm_num)
theorem B4720625 : Blo 2097435 4720625 := bstep (se 2 (by rfl) ⟨1770234, by rfl⟩ : syracuseStep 4720625 = 3540469) B3540469
theorem B3147083 : Blo 2097435 3147083 := bstep (se 1 (by rfl) ⟨2360312, by rfl⟩ : syracuseStep 3147083 = 4720625) B4720625
theorem B2098055 : Blo 2097435 2098055 := bstep (se 1 (by rfl) ⟨1573541, by rfl⟩ : syracuseStep 2098055 = 3147083) B3147083
theorem B2360317 : Blo 2097435 2360317 := bbase (se 3 (by rfl) ⟨442559, by rfl⟩ : syracuseStep 2360317 = 885119) (by norm_num)
theorem B3147089 : Blo 2097435 3147089 := bstep (se 2 (by rfl) ⟨1180158, by rfl⟩ : syracuseStep 3147089 = 2360317) B2360317
theorem B2098059 : Blo 2097435 2098059 := bstep (se 1 (by rfl) ⟨1573544, by rfl⟩ : syracuseStep 2098059 = 3147089) B3147089
theorem B7080965 : Blo 2097435 7080965 := bbase (se 4 (by rfl) ⟨663840, by rfl⟩ : syracuseStep 7080965 = 1327681) (by norm_num)
theorem B4720643 : Blo 2097435 4720643 := bstep (se 1 (by rfl) ⟨3540482, by rfl⟩ : syracuseStep 4720643 = 7080965) B7080965
theorem B3147095 : Blo 2097435 3147095 := bstep (se 1 (by rfl) ⟨2360321, by rfl⟩ : syracuseStep 3147095 = 4720643) B4720643
theorem B2098063 : Blo 2097435 2098063 := bstep (se 1 (by rfl) ⟨1573547, by rfl⟩ : syracuseStep 2098063 = 3147095) B3147095
theorem B3147101 : Blo 2097435 3147101 := bbase (se 3 (by rfl) ⟨590081, by rfl⟩ : syracuseStep 3147101 = 1180163) (by norm_num)
theorem B2098067 : Blo 2097435 2098067 := bstep (se 1 (by rfl) ⟨1573550, by rfl⟩ : syracuseStep 2098067 = 3147101) B3147101
theorem B4720661 : Blo 2097435 4720661 := bbase (se 6 (by rfl) ⟨110640, by rfl⟩ : syracuseStep 4720661 = 221281) (by norm_num)
theorem B3147107 : Blo 2097435 3147107 := bstep (se 1 (by rfl) ⟨2360330, by rfl⟩ : syracuseStep 3147107 = 4720661) B4720661
theorem B2098071 : Blo 2097435 2098071 := bstep (se 1 (by rfl) ⟨1573553, by rfl⟩ : syracuseStep 2098071 = 3147107) B3147107
theorem B7966133 : Blo 2097435 7966133 := bbase (se 5 (by rfl) ⟨373412, by rfl⟩ : syracuseStep 7966133 = 746825) (by norm_num)
theorem B5310755 : Blo 2097435 5310755 := bstep (se 1 (by rfl) ⟨3983066, by rfl⟩ : syracuseStep 5310755 = 7966133) B7966133
theorem B3540503 : Blo 2097435 3540503 := bstep (se 1 (by rfl) ⟨2655377, by rfl⟩ : syracuseStep 3540503 = 5310755) B5310755
theorem B2360335 : Blo 2097435 2360335 := bstep (se 1 (by rfl) ⟨1770251, by rfl⟩ : syracuseStep 2360335 = 3540503) B3540503
theorem B3147113 : Blo 2097435 3147113 := bstep (se 2 (by rfl) ⟨1180167, by rfl⟩ : syracuseStep 3147113 = 2360335) B2360335
theorem B2098075 : Blo 2097435 2098075 := bstep (se 1 (by rfl) ⟨1573556, by rfl⟩ : syracuseStep 2098075 = 3147113) B3147113
theorem B6380117 : Blo 2097435 6380117 := bbase (se 8 (by rfl) ⟨37383, by rfl⟩ : syracuseStep 6380117 = 74767) (by norm_num)
theorem B4253411 : Blo 2097435 4253411 := bstep (se 1 (by rfl) ⟨3190058, by rfl⟩ : syracuseStep 4253411 = 6380117) B6380117
theorem B11342429 : Blo 2097435 11342429 := bstep (se 3 (by rfl) ⟨2126705, by rfl⟩ : syracuseStep 11342429 = 4253411) B4253411
theorem B7561619 : Blo 2097435 7561619 := bstep (se 1 (by rfl) ⟨5671214, by rfl⟩ : syracuseStep 7561619 = 11342429) B11342429
theorem B5041079 : Blo 2097435 5041079 := bstep (se 1 (by rfl) ⟨3780809, by rfl⟩ : syracuseStep 5041079 = 7561619) B7561619
theorem B3360719 : Blo 2097435 3360719 := bstep (se 1 (by rfl) ⟨2520539, by rfl⟩ : syracuseStep 3360719 = 5041079) B5041079
theorem B2240479 : Blo 2097435 2240479 := bstep (se 1 (by rfl) ⟨1680359, by rfl⟩ : syracuseStep 2240479 = 3360719) B3360719
theorem B11949221 : Blo 2097435 11949221 := bstep (se 4 (by rfl) ⟨1120239, by rfl⟩ : syracuseStep 11949221 = 2240479) B2240479
theorem B7966147 : Blo 2097435 7966147 := bstep (se 1 (by rfl) ⟨5974610, by rfl⟩ : syracuseStep 7966147 = 11949221) B11949221
theorem B10621529 : Blo 2097435 10621529 := bstep (se 2 (by rfl) ⟨3983073, by rfl⟩ : syracuseStep 10621529 = 7966147) B7966147
theorem B7081019 : Blo 2097435 7081019 := bstep (se 1 (by rfl) ⟨5310764, by rfl⟩ : syracuseStep 7081019 = 10621529) B10621529
theorem B4720679 : Blo 2097435 4720679 := bstep (se 1 (by rfl) ⟨3540509, by rfl⟩ : syracuseStep 4720679 = 7081019) B7081019
theorem B3147119 : Blo 2097435 3147119 := bstep (se 1 (by rfl) ⟨2360339, by rfl⟩ : syracuseStep 3147119 = 4720679) B4720679
theorem B2098079 : Blo 2097435 2098079 := bstep (se 1 (by rfl) ⟨1573559, by rfl⟩ : syracuseStep 2098079 = 3147119) B3147119
theorem B3147125 : Blo 2097435 3147125 := bbase (se 5 (by rfl) ⟨147521, by rfl⟩ : syracuseStep 3147125 = 295043) (by norm_num)
theorem B2098083 : Blo 2097435 2098083 := bstep (se 1 (by rfl) ⟨1573562, by rfl⟩ : syracuseStep 2098083 = 3147125) B3147125
theorem B2987317 : Blo 2097435 2987317 := bbase (se 5 (by rfl) ⟨140030, by rfl⟩ : syracuseStep 2987317 = 280061) (by norm_num)
theorem B3983089 : Blo 2097435 3983089 := bstep (se 2 (by rfl) ⟨1493658, by rfl⟩ : syracuseStep 3983089 = 2987317) B2987317
theorem B5310785 : Blo 2097435 5310785 := bstep (se 2 (by rfl) ⟨1991544, by rfl⟩ : syracuseStep 5310785 = 3983089) B3983089
theorem B3540523 : Blo 2097435 3540523 := bstep (se 1 (by rfl) ⟨2655392, by rfl⟩ : syracuseStep 3540523 = 5310785) B5310785
theorem B4720697 : Blo 2097435 4720697 := bstep (se 2 (by rfl) ⟨1770261, by rfl⟩ : syracuseStep 4720697 = 3540523) B3540523
theorem B3147131 : Blo 2097435 3147131 := bstep (se 1 (by rfl) ⟨2360348, by rfl⟩ : syracuseStep 3147131 = 4720697) B4720697
theorem B2098087 : Blo 2097435 2098087 := bstep (se 1 (by rfl) ⟨1573565, by rfl⟩ : syracuseStep 2098087 = 3147131) B3147131
theorem B2360353 : Blo 2097435 2360353 := bbase (se 2 (by rfl) ⟨885132, by rfl⟩ : syracuseStep 2360353 = 1770265) (by norm_num)
theorem B3147137 : Blo 2097435 3147137 := bstep (se 2 (by rfl) ⟨1180176, by rfl⟩ : syracuseStep 3147137 = 2360353) B2360353
theorem B2098091 : Blo 2097435 2098091 := bstep (se 1 (by rfl) ⟨1573568, by rfl⟩ : syracuseStep 2098091 = 3147137) B3147137
theorem B5310805 : Blo 2097435 5310805 := bbase (se 10 (by rfl) ⟨7779, by rfl⟩ : syracuseStep 5310805 = 15559) (by norm_num)
theorem B7081073 : Blo 2097435 7081073 := bstep (se 2 (by rfl) ⟨2655402, by rfl⟩ : syracuseStep 7081073 = 5310805) B5310805
theorem B4720715 : Blo 2097435 4720715 := bstep (se 1 (by rfl) ⟨3540536, by rfl⟩ : syracuseStep 4720715 = 7081073) B7081073
theorem B3147143 : Blo 2097435 3147143 := bstep (se 1 (by rfl) ⟨2360357, by rfl⟩ : syracuseStep 3147143 = 4720715) B4720715
theorem B2098095 : Blo 2097435 2098095 := bstep (se 1 (by rfl) ⟨1573571, by rfl⟩ : syracuseStep 2098095 = 3147143) B3147143
theorem B3147149 : Blo 2097435 3147149 := bbase (se 3 (by rfl) ⟨590090, by rfl⟩ : syracuseStep 3147149 = 1180181) (by norm_num)
theorem B2098099 : Blo 2097435 2098099 := bstep (se 1 (by rfl) ⟨1573574, by rfl⟩ : syracuseStep 2098099 = 3147149) B3147149
theorem B4720733 : Blo 2097435 4720733 := bbase (se 3 (by rfl) ⟨885137, by rfl⟩ : syracuseStep 4720733 = 1770275) (by norm_num)
theorem B3147155 : Blo 2097435 3147155 := bstep (se 1 (by rfl) ⟨2360366, by rfl⟩ : syracuseStep 3147155 = 4720733) B4720733
theorem B2098103 : Blo 2097435 2098103 := bstep (se 1 (by rfl) ⟨1573577, by rfl⟩ : syracuseStep 2098103 = 3147155) B3147155
theorem B3540557 : Blo 2097435 3540557 := bbase (se 3 (by rfl) ⟨663854, by rfl⟩ : syracuseStep 3540557 = 1327709) (by norm_num)
theorem B2360371 : Blo 2097435 2360371 := bstep (se 1 (by rfl) ⟨1770278, by rfl⟩ : syracuseStep 2360371 = 3540557) B3540557
theorem B3147161 : Blo 2097435 3147161 := bstep (se 2 (by rfl) ⟨1180185, by rfl⟩ : syracuseStep 3147161 = 2360371) B2360371
theorem B2098107 : Blo 2097435 2098107 := bstep (se 1 (by rfl) ⟨1573580, by rfl⟩ : syracuseStep 2098107 = 3147161) B3147161
theorem B8506949 : Blo 2097435 8506949 := bbase (se 4 (by rfl) ⟨797526, by rfl⟩ : syracuseStep 8506949 = 1595053) (by norm_num)
theorem B22685197 : Blo 2097435 22685197 := bstep (se 3 (by rfl) ⟨4253474, by rfl⟩ : syracuseStep 22685197 = 8506949) B8506949
theorem B30246929 : Blo 2097435 30246929 := bstep (se 2 (by rfl) ⟨11342598, by rfl⟩ : syracuseStep 30246929 = 22685197) B22685197
theorem B20164619 : Blo 2097435 20164619 := bstep (se 1 (by rfl) ⟨15123464, by rfl⟩ : syracuseStep 20164619 = 30246929) B30246929
theorem B13443079 : Blo 2097435 13443079 := bstep (se 1 (by rfl) ⟨10082309, by rfl⟩ : syracuseStep 13443079 = 20164619) B20164619
theorem B17924105 : Blo 2097435 17924105 := bstep (se 2 (by rfl) ⟨6721539, by rfl⟩ : syracuseStep 17924105 = 13443079) B13443079
theorem B11949403 : Blo 2097435 11949403 := bstep (se 1 (by rfl) ⟨8962052, by rfl⟩ : syracuseStep 11949403 = 17924105) B17924105
theorem B15932537 : Blo 2097435 15932537 := bstep (se 2 (by rfl) ⟨5974701, by rfl⟩ : syracuseStep 15932537 = 11949403) B11949403
theorem B10621691 : Blo 2097435 10621691 := bstep (se 1 (by rfl) ⟨7966268, by rfl⟩ : syracuseStep 10621691 = 15932537) B15932537
theorem B7081127 : Blo 2097435 7081127 := bstep (se 1 (by rfl) ⟨5310845, by rfl⟩ : syracuseStep 7081127 = 10621691) B10621691
theorem B4720751 : Blo 2097435 4720751 := bstep (se 1 (by rfl) ⟨3540563, by rfl⟩ : syracuseStep 4720751 = 7081127) B7081127
theorem B3147167 : Blo 2097435 3147167 := bstep (se 1 (by rfl) ⟨2360375, by rfl⟩ : syracuseStep 3147167 = 4720751) B4720751
theorem B2098111 : Blo 2097435 2098111 := bstep (se 1 (by rfl) ⟨1573583, by rfl⟩ : syracuseStep 2098111 = 3147167) B3147167
theorem B3147173 : Blo 2097435 3147173 := bbase (se 4 (by rfl) ⟨295047, by rfl⟩ : syracuseStep 3147173 = 590095) (by norm_num)
theorem B2098115 : Blo 2097435 2098115 := bstep (se 1 (by rfl) ⟨1573586, by rfl⟩ : syracuseStep 2098115 = 3147173) B3147173
theorem B2655433 : Blo 2097435 2655433 := bbase (se 2 (by rfl) ⟨995787, by rfl⟩ : syracuseStep 2655433 = 1991575) (by norm_num)
theorem B3540577 : Blo 2097435 3540577 := bstep (se 2 (by rfl) ⟨1327716, by rfl⟩ : syracuseStep 3540577 = 2655433) B2655433
theorem B4720769 : Blo 2097435 4720769 := bstep (se 2 (by rfl) ⟨1770288, by rfl⟩ : syracuseStep 4720769 = 3540577) B3540577
theorem B3147179 : Blo 2097435 3147179 := bstep (se 1 (by rfl) ⟨2360384, by rfl⟩ : syracuseStep 3147179 = 4720769) B4720769
theorem B2098119 : Blo 2097435 2098119 := bstep (se 1 (by rfl) ⟨1573589, by rfl⟩ : syracuseStep 2098119 = 3147179) B3147179
theorem B2360389 : Blo 2097435 2360389 := bbase (se 4 (by rfl) ⟨221286, by rfl⟩ : syracuseStep 2360389 = 442573) (by norm_num)
theorem B3147185 : Blo 2097435 3147185 := bstep (se 2 (by rfl) ⟨1180194, by rfl⟩ : syracuseStep 3147185 = 2360389) B2360389
theorem B2098123 : Blo 2097435 2098123 := bstep (se 1 (by rfl) ⟨1573592, by rfl⟩ : syracuseStep 2098123 = 3147185) B3147185
theorem B3983165 : Blo 2097435 3983165 := bbase (se 3 (by rfl) ⟨746843, by rfl⟩ : syracuseStep 3983165 = 1493687) (by norm_num)
theorem B2655443 : Blo 2097435 2655443 := bstep (se 1 (by rfl) ⟨1991582, by rfl⟩ : syracuseStep 2655443 = 3983165) B3983165
theorem B7081181 : Blo 2097435 7081181 := bstep (se 3 (by rfl) ⟨1327721, by rfl⟩ : syracuseStep 7081181 = 2655443) B2655443
theorem B4720787 : Blo 2097435 4720787 := bstep (se 1 (by rfl) ⟨3540590, by rfl⟩ : syracuseStep 4720787 = 7081181) B7081181
theorem B3147191 : Blo 2097435 3147191 := bstep (se 1 (by rfl) ⟨2360393, by rfl⟩ : syracuseStep 3147191 = 4720787) B4720787
theorem B2098127 : Blo 2097435 2098127 := bstep (se 1 (by rfl) ⟨1573595, by rfl⟩ : syracuseStep 2098127 = 3147191) B3147191
theorem B3147197 : Blo 2097435 3147197 := bbase (se 3 (by rfl) ⟨590099, by rfl⟩ : syracuseStep 3147197 = 1180199) (by norm_num)
theorem B2098131 : Blo 2097435 2098131 := bstep (se 1 (by rfl) ⟨1573598, by rfl⟩ : syracuseStep 2098131 = 3147197) B3147197
theorem B4720805 : Blo 2097435 4720805 := bbase (se 4 (by rfl) ⟨442575, by rfl⟩ : syracuseStep 4720805 = 885151) (by norm_num)
theorem B3147203 : Blo 2097435 3147203 := bstep (se 1 (by rfl) ⟨2360402, by rfl⟩ : syracuseStep 3147203 = 4720805) B4720805
theorem B2098135 : Blo 2097435 2098135 := bstep (se 1 (by rfl) ⟨1573601, by rfl⟩ : syracuseStep 2098135 = 3147203) B3147203
theorem B5310917 : Blo 2097435 5310917 := bbase (se 4 (by rfl) ⟨497898, by rfl⟩ : syracuseStep 5310917 = 995797) (by norm_num)
theorem B3540611 : Blo 2097435 3540611 := bstep (se 1 (by rfl) ⟨2655458, by rfl⟩ : syracuseStep 3540611 = 5310917) B5310917
theorem B2360407 : Blo 2097435 2360407 := bstep (se 1 (by rfl) ⟨1770305, by rfl⟩ : syracuseStep 2360407 = 3540611) B3540611
theorem B3147209 : Blo 2097435 3147209 := bstep (se 2 (by rfl) ⟨1180203, by rfl⟩ : syracuseStep 3147209 = 2360407) B2360407
theorem B2098139 : Blo 2097435 2098139 := bstep (se 1 (by rfl) ⟨1573604, by rfl⟩ : syracuseStep 2098139 = 3147209) B3147209
theorem B14355701 : Blo 2097435 14355701 := bbase (se 5 (by rfl) ⟨672923, by rfl⟩ : syracuseStep 14355701 = 1345847) (by norm_num)
theorem B9570467 : Blo 2097435 9570467 := bstep (se 1 (by rfl) ⟨7177850, by rfl⟩ : syracuseStep 9570467 = 14355701) B14355701
theorem B6380311 : Blo 2097435 6380311 := bstep (se 1 (by rfl) ⟨4785233, by rfl⟩ : syracuseStep 6380311 = 9570467) B9570467
theorem B8507081 : Blo 2097435 8507081 := bstep (se 2 (by rfl) ⟨3190155, by rfl⟩ : syracuseStep 8507081 = 6380311) B6380311
theorem B5671387 : Blo 2097435 5671387 := bstep (se 1 (by rfl) ⟨4253540, by rfl⟩ : syracuseStep 5671387 = 8507081) B8507081
theorem B7561849 : Blo 2097435 7561849 := bstep (se 2 (by rfl) ⟨2835693, by rfl⟩ : syracuseStep 7561849 = 5671387) B5671387
theorem B10082465 : Blo 2097435 10082465 := bstep (se 2 (by rfl) ⟨3780924, by rfl⟩ : syracuseStep 10082465 = 7561849) B7561849
theorem B6721643 : Blo 2097435 6721643 := bstep (se 1 (by rfl) ⟨5041232, by rfl⟩ : syracuseStep 6721643 = 10082465) B10082465
theorem B4481095 : Blo 2097435 4481095 := bstep (se 1 (by rfl) ⟨3360821, by rfl⟩ : syracuseStep 4481095 = 6721643) B6721643
theorem B5974793 : Blo 2097435 5974793 := bstep (se 2 (by rfl) ⟨2240547, by rfl⟩ : syracuseStep 5974793 = 4481095) B4481095
theorem B3983195 : Blo 2097435 3983195 := bstep (se 1 (by rfl) ⟨2987396, by rfl⟩ : syracuseStep 3983195 = 5974793) B5974793
theorem B10621853 : Blo 2097435 10621853 := bstep (se 3 (by rfl) ⟨1991597, by rfl⟩ : syracuseStep 10621853 = 3983195) B3983195
theorem B7081235 : Blo 2097435 7081235 := bstep (se 1 (by rfl) ⟨5310926, by rfl⟩ : syracuseStep 7081235 = 10621853) B10621853
theorem B4720823 : Blo 2097435 4720823 := bstep (se 1 (by rfl) ⟨3540617, by rfl⟩ : syracuseStep 4720823 = 7081235) B7081235
theorem B3147215 : Blo 2097435 3147215 := bstep (se 1 (by rfl) ⟨2360411, by rfl⟩ : syracuseStep 3147215 = 4720823) B4720823
theorem B2098143 : Blo 2097435 2098143 := bstep (se 1 (by rfl) ⟨1573607, by rfl⟩ : syracuseStep 2098143 = 3147215) B3147215
theorem B3147221 : Blo 2097435 3147221 := bbase (se 7 (by rfl) ⟨36881, by rfl⟩ : syracuseStep 3147221 = 73763) (by norm_num)
theorem B2098147 : Blo 2097435 2098147 := bstep (se 1 (by rfl) ⟨1573610, by rfl⟩ : syracuseStep 2098147 = 3147221) B3147221
theorem B7966421 : Blo 2097435 7966421 := bbase (se 7 (by rfl) ⟨93356, by rfl⟩ : syracuseStep 7966421 = 186713) (by norm_num)
theorem B5310947 : Blo 2097435 5310947 := bstep (se 1 (by rfl) ⟨3983210, by rfl⟩ : syracuseStep 5310947 = 7966421) B7966421
theorem B3540631 : Blo 2097435 3540631 := bstep (se 1 (by rfl) ⟨2655473, by rfl⟩ : syracuseStep 3540631 = 5310947) B5310947
theorem B4720841 : Blo 2097435 4720841 := bstep (se 2 (by rfl) ⟨1770315, by rfl⟩ : syracuseStep 4720841 = 3540631) B3540631
theorem B3147227 : Blo 2097435 3147227 := bstep (se 1 (by rfl) ⟨2360420, by rfl⟩ : syracuseStep 3147227 = 4720841) B4720841
theorem B2098151 : Blo 2097435 2098151 := bstep (se 1 (by rfl) ⟨1573613, by rfl⟩ : syracuseStep 2098151 = 3147227) B3147227
theorem B2360425 : Blo 2097435 2360425 := bbase (se 2 (by rfl) ⟨885159, by rfl⟩ : syracuseStep 2360425 = 1770319) (by norm_num)
theorem B3147233 : Blo 2097435 3147233 := bstep (se 2 (by rfl) ⟨1180212, by rfl⟩ : syracuseStep 3147233 = 2360425) B2360425
theorem B2098155 : Blo 2097435 2098155 := bstep (se 1 (by rfl) ⟨1573616, by rfl⟩ : syracuseStep 2098155 = 3147233) B3147233
theorem B4253573 : Blo 2097435 4253573 := bbase (se 4 (by rfl) ⟨398772, by rfl⟩ : syracuseStep 4253573 = 797545) (by norm_num)
theorem B11342861 : Blo 2097435 11342861 := bstep (se 3 (by rfl) ⟨2126786, by rfl⟩ : syracuseStep 11342861 = 4253573) B4253573
theorem B7561907 : Blo 2097435 7561907 := bstep (se 1 (by rfl) ⟨5671430, by rfl⟩ : syracuseStep 7561907 = 11342861) B11342861
theorem B5041271 : Blo 2097435 5041271 := bstep (se 1 (by rfl) ⟨3780953, by rfl⟩ : syracuseStep 5041271 = 7561907) B7561907
theorem B3360847 : Blo 2097435 3360847 := bstep (se 1 (by rfl) ⟨2520635, by rfl⟩ : syracuseStep 3360847 = 5041271) B5041271
theorem B4481129 : Blo 2097435 4481129 := bstep (se 2 (by rfl) ⟨1680423, by rfl⟩ : syracuseStep 4481129 = 3360847) B3360847
theorem B11949677 : Blo 2097435 11949677 := bstep (se 3 (by rfl) ⟨2240564, by rfl⟩ : syracuseStep 11949677 = 4481129) B4481129
theorem B7966451 : Blo 2097435 7966451 := bstep (se 1 (by rfl) ⟨5974838, by rfl⟩ : syracuseStep 7966451 = 11949677) B11949677
theorem B5310967 : Blo 2097435 5310967 := bstep (se 1 (by rfl) ⟨3983225, by rfl⟩ : syracuseStep 5310967 = 7966451) B7966451
theorem B7081289 : Blo 2097435 7081289 := bstep (se 2 (by rfl) ⟨2655483, by rfl⟩ : syracuseStep 7081289 = 5310967) B5310967
theorem B4720859 : Blo 2097435 4720859 := bstep (se 1 (by rfl) ⟨3540644, by rfl⟩ : syracuseStep 4720859 = 7081289) B7081289
theorem B3147239 : Blo 2097435 3147239 := bstep (se 1 (by rfl) ⟨2360429, by rfl⟩ : syracuseStep 3147239 = 4720859) B4720859
theorem B2098159 : Blo 2097435 2098159 := bstep (se 1 (by rfl) ⟨1573619, by rfl⟩ : syracuseStep 2098159 = 3147239) B3147239
theorem B3147245 : Blo 2097435 3147245 := bbase (se 3 (by rfl) ⟨590108, by rfl⟩ : syracuseStep 3147245 = 1180217) (by norm_num)
theorem B2098163 : Blo 2097435 2098163 := bstep (se 1 (by rfl) ⟨1573622, by rfl⟩ : syracuseStep 2098163 = 3147245) B3147245
theorem B4720877 : Blo 2097435 4720877 := bbase (se 3 (by rfl) ⟨885164, by rfl⟩ : syracuseStep 4720877 = 1770329) (by norm_num)
theorem B3147251 : Blo 2097435 3147251 := bstep (se 1 (by rfl) ⟨2360438, by rfl⟩ : syracuseStep 3147251 = 4720877) B4720877
theorem B2098167 : Blo 2097435 2098167 := bstep (se 1 (by rfl) ⟨1573625, by rfl⟩ : syracuseStep 2098167 = 3147251) B3147251
theorem B2987437 : Blo 2097435 2987437 := bbase (se 3 (by rfl) ⟨560144, by rfl⟩ : syracuseStep 2987437 = 1120289) (by norm_num)
theorem B3983249 : Blo 2097435 3983249 := bstep (se 2 (by rfl) ⟨1493718, by rfl⟩ : syracuseStep 3983249 = 2987437) B2987437
theorem B2655499 : Blo 2097435 2655499 := bstep (se 1 (by rfl) ⟨1991624, by rfl⟩ : syracuseStep 2655499 = 3983249) B3983249
theorem B3540665 : Blo 2097435 3540665 := bstep (se 2 (by rfl) ⟨1327749, by rfl⟩ : syracuseStep 3540665 = 2655499) B2655499
theorem B2360443 : Blo 2097435 2360443 := bstep (se 1 (by rfl) ⟨1770332, by rfl⟩ : syracuseStep 2360443 = 3540665) B3540665
theorem B3147257 : Blo 2097435 3147257 := bstep (se 2 (by rfl) ⟨1180221, by rfl⟩ : syracuseStep 3147257 = 2360443) B2360443
theorem B2098171 : Blo 2097435 2098171 := bstep (se 1 (by rfl) ⟨1573628, by rfl⟩ : syracuseStep 2098171 = 3147257) B3147257
theorem B15123925 : Blo 2097435 15123925 := bbase (se 7 (by rfl) ⟨177233, by rfl⟩ : syracuseStep 15123925 = 354467) (by norm_num)
theorem B80660933 : Blo 2097435 80660933 := bstep (se 4 (by rfl) ⟨7561962, by rfl⟩ : syracuseStep 80660933 = 15123925) B15123925
theorem B53773955 : Blo 2097435 53773955 := bstep (se 1 (by rfl) ⟨40330466, by rfl⟩ : syracuseStep 53773955 = 80660933) B80660933
theorem B35849303 : Blo 2097435 35849303 := bstep (se 1 (by rfl) ⟨26886977, by rfl⟩ : syracuseStep 35849303 = 53773955) B53773955
theorem B23899535 : Blo 2097435 23899535 := bstep (se 1 (by rfl) ⟨17924651, by rfl⟩ : syracuseStep 23899535 = 35849303) B35849303
theorem B15933023 : Blo 2097435 15933023 := bstep (se 1 (by rfl) ⟨11949767, by rfl⟩ : syracuseStep 15933023 = 23899535) B23899535
theorem B10622015 : Blo 2097435 10622015 := bstep (se 1 (by rfl) ⟨7966511, by rfl⟩ : syracuseStep 10622015 = 15933023) B15933023
theorem B7081343 : Blo 2097435 7081343 := bstep (se 1 (by rfl) ⟨5311007, by rfl⟩ : syracuseStep 7081343 = 10622015) B10622015
theorem B4720895 : Blo 2097435 4720895 := bstep (se 1 (by rfl) ⟨3540671, by rfl⟩ : syracuseStep 4720895 = 7081343) B7081343
theorem B3147263 : Blo 2097435 3147263 := bstep (se 1 (by rfl) ⟨2360447, by rfl⟩ : syracuseStep 3147263 = 4720895) B4720895
theorem B2098175 : Blo 2097435 2098175 := bstep (se 1 (by rfl) ⟨1573631, by rfl⟩ : syracuseStep 2098175 = 3147263) B3147263
theorem B3147269 : Blo 2097435 3147269 := bbase (se 4 (by rfl) ⟨295056, by rfl⟩ : syracuseStep 3147269 = 590113) (by norm_num)
theorem B2098179 : Blo 2097435 2098179 := bstep (se 1 (by rfl) ⟨1573634, by rfl⟩ : syracuseStep 2098179 = 3147269) B3147269
theorem B3540685 : Blo 2097435 3540685 := bbase (se 3 (by rfl) ⟨663878, by rfl⟩ : syracuseStep 3540685 = 1327757) (by norm_num)
theorem B4720913 : Blo 2097435 4720913 := bstep (se 2 (by rfl) ⟨1770342, by rfl⟩ : syracuseStep 4720913 = 3540685) B3540685
theorem B3147275 : Blo 2097435 3147275 := bstep (se 1 (by rfl) ⟨2360456, by rfl⟩ : syracuseStep 3147275 = 4720913) B4720913
theorem B2098183 : Blo 2097435 2098183 := bstep (se 1 (by rfl) ⟨1573637, by rfl⟩ : syracuseStep 2098183 = 3147275) B3147275
theorem B2360461 : Blo 2097435 2360461 := bbase (se 3 (by rfl) ⟨442586, by rfl⟩ : syracuseStep 2360461 = 885173) (by norm_num)
theorem B3147281 : Blo 2097435 3147281 := bstep (se 2 (by rfl) ⟨1180230, by rfl⟩ : syracuseStep 3147281 = 2360461) B2360461
theorem B2098187 : Blo 2097435 2098187 := bstep (se 1 (by rfl) ⟨1573640, by rfl⟩ : syracuseStep 2098187 = 3147281) B3147281
theorem B7081397 : Blo 2097435 7081397 := bbase (se 5 (by rfl) ⟨331940, by rfl⟩ : syracuseStep 7081397 = 663881) (by norm_num)
theorem B4720931 : Blo 2097435 4720931 := bstep (se 1 (by rfl) ⟨3540698, by rfl⟩ : syracuseStep 4720931 = 7081397) B7081397
theorem B3147287 : Blo 2097435 3147287 := bstep (se 1 (by rfl) ⟨2360465, by rfl⟩ : syracuseStep 3147287 = 4720931) B4720931
theorem B2098191 : Blo 2097435 2098191 := bstep (se 1 (by rfl) ⟨1573643, by rfl⟩ : syracuseStep 2098191 = 3147287) B3147287
theorem B3147293 : Blo 2097435 3147293 := bbase (se 3 (by rfl) ⟨590117, by rfl⟩ : syracuseStep 3147293 = 1180235) (by norm_num)
theorem B2098195 : Blo 2097435 2098195 := bstep (se 1 (by rfl) ⟨1573646, by rfl⟩ : syracuseStep 2098195 = 3147293) B3147293
theorem B4720949 : Blo 2097435 4720949 := bbase (se 5 (by rfl) ⟨221294, by rfl⟩ : syracuseStep 4720949 = 442589) (by norm_num)
theorem B3147299 : Blo 2097435 3147299 := bstep (se 1 (by rfl) ⟨2360474, by rfl⟩ : syracuseStep 3147299 = 4720949) B4720949
theorem B2098199 : Blo 2097435 2098199 := bstep (se 1 (by rfl) ⟨1573649, by rfl⟩ : syracuseStep 2098199 = 3147299) B3147299
theorem B4542365 : Blo 2097435 4542365 := bbase (se 3 (by rfl) ⟨851693, by rfl⟩ : syracuseStep 4542365 = 1703387) (by norm_num)
theorem B12112973 : Blo 2097435 12112973 := bstep (se 3 (by rfl) ⟨2271182, by rfl⟩ : syracuseStep 12112973 = 4542365) B4542365
theorem B8075315 : Blo 2097435 8075315 := bstep (se 1 (by rfl) ⟨6056486, by rfl⟩ : syracuseStep 8075315 = 12112973) B12112973
theorem B5383543 : Blo 2097435 5383543 := bstep (se 1 (by rfl) ⟨4037657, by rfl⟩ : syracuseStep 5383543 = 8075315) B8075315
theorem B7178057 : Blo 2097435 7178057 := bstep (se 2 (by rfl) ⟨2691771, by rfl⟩ : syracuseStep 7178057 = 5383543) B5383543
theorem B4785371 : Blo 2097435 4785371 := bstep (se 1 (by rfl) ⟨3589028, by rfl⟩ : syracuseStep 4785371 = 7178057) B7178057
theorem B3190247 : Blo 2097435 3190247 := bstep (se 1 (by rfl) ⟨2392685, by rfl⟩ : syracuseStep 3190247 = 4785371) B4785371
theorem B2126831 : Blo 2097435 2126831 := bstep (se 1 (by rfl) ⟨1595123, by rfl⟩ : syracuseStep 2126831 = 3190247) B3190247
theorem B5671549 : Blo 2097435 5671549 := bstep (se 3 (by rfl) ⟨1063415, by rfl⟩ : syracuseStep 5671549 = 2126831) B2126831
theorem B30248261 : Blo 2097435 30248261 := bstep (se 4 (by rfl) ⟨2835774, by rfl⟩ : syracuseStep 30248261 = 5671549) B5671549
theorem B20165507 : Blo 2097435 20165507 := bstep (se 1 (by rfl) ⟨15124130, by rfl⟩ : syracuseStep 20165507 = 30248261) B30248261
theorem B13443671 : Blo 2097435 13443671 := bstep (se 1 (by rfl) ⟨10082753, by rfl⟩ : syracuseStep 13443671 = 20165507) B20165507
theorem B8962447 : Blo 2097435 8962447 := bstep (se 1 (by rfl) ⟨6721835, by rfl⟩ : syracuseStep 8962447 = 13443671) B13443671
theorem B11949929 : Blo 2097435 11949929 := bstep (se 2 (by rfl) ⟨4481223, by rfl⟩ : syracuseStep 11949929 = 8962447) B8962447
theorem B7966619 : Blo 2097435 7966619 := bstep (se 1 (by rfl) ⟨5974964, by rfl⟩ : syracuseStep 7966619 = 11949929) B11949929
theorem B5311079 : Blo 2097435 5311079 := bstep (se 1 (by rfl) ⟨3983309, by rfl⟩ : syracuseStep 5311079 = 7966619) B7966619
theorem B3540719 : Blo 2097435 3540719 := bstep (se 1 (by rfl) ⟨2655539, by rfl⟩ : syracuseStep 3540719 = 5311079) B5311079
theorem B2360479 : Blo 2097435 2360479 := bstep (se 1 (by rfl) ⟨1770359, by rfl⟩ : syracuseStep 2360479 = 3540719) B3540719
theorem B3147305 : Blo 2097435 3147305 := bstep (se 2 (by rfl) ⟨1180239, by rfl⟩ : syracuseStep 3147305 = 2360479) B2360479
theorem B2098203 : Blo 2097435 2098203 := bstep (se 1 (by rfl) ⟨1573652, by rfl⟩ : syracuseStep 2098203 = 3147305) B3147305
theorem B25870229 : Blo 2097435 25870229 := bbase (se 6 (by rfl) ⟨606333, by rfl⟩ : syracuseStep 25870229 = 1212667) (by norm_num)
theorem B17246819 : Blo 2097435 17246819 := bstep (se 1 (by rfl) ⟨12935114, by rfl⟩ : syracuseStep 17246819 = 25870229) B25870229
theorem B11497879 : Blo 2097435 11497879 := bstep (se 1 (by rfl) ⟨8623409, by rfl⟩ : syracuseStep 11497879 = 17246819) B17246819
theorem B15330505 : Blo 2097435 15330505 := bstep (se 2 (by rfl) ⟨5748939, by rfl⟩ : syracuseStep 15330505 = 11497879) B11497879
theorem B20440673 : Blo 2097435 20440673 := bstep (se 2 (by rfl) ⟨7665252, by rfl⟩ : syracuseStep 20440673 = 15330505) B15330505
theorem B13627115 : Blo 2097435 13627115 := bstep (se 1 (by rfl) ⟨10220336, by rfl⟩ : syracuseStep 13627115 = 20440673) B20440673
theorem B9084743 : Blo 2097435 9084743 := bstep (se 1 (by rfl) ⟨6813557, by rfl⟩ : syracuseStep 9084743 = 13627115) B13627115
theorem B6056495 : Blo 2097435 6056495 := bstep (se 1 (by rfl) ⟨4542371, by rfl⟩ : syracuseStep 6056495 = 9084743) B9084743
theorem B4037663 : Blo 2097435 4037663 := bstep (se 1 (by rfl) ⟨3028247, by rfl⟩ : syracuseStep 4037663 = 6056495) B6056495
theorem B10767101 : Blo 2097435 10767101 := bstep (se 3 (by rfl) ⟨2018831, by rfl⟩ : syracuseStep 10767101 = 4037663) B4037663
theorem B28712269 : Blo 2097435 28712269 := bstep (se 3 (by rfl) ⟨5383550, by rfl⟩ : syracuseStep 28712269 = 10767101) B10767101
theorem B38283025 : Blo 2097435 38283025 := bstep (se 2 (by rfl) ⟨14356134, by rfl⟩ : syracuseStep 38283025 = 28712269) B28712269
theorem B51044033 : Blo 2097435 51044033 := bstep (se 2 (by rfl) ⟨19141512, by rfl⟩ : syracuseStep 51044033 = 38283025) B38283025
theorem B34029355 : Blo 2097435 34029355 := bstep (se 1 (by rfl) ⟨25522016, by rfl⟩ : syracuseStep 34029355 = 51044033) B51044033
theorem B45372473 : Blo 2097435 45372473 := bstep (se 2 (by rfl) ⟨17014677, by rfl⟩ : syracuseStep 45372473 = 34029355) B34029355
theorem B30248315 : Blo 2097435 30248315 := bstep (se 1 (by rfl) ⟨22686236, by rfl⟩ : syracuseStep 30248315 = 45372473) B45372473
theorem B20165543 : Blo 2097435 20165543 := bstep (se 1 (by rfl) ⟨15124157, by rfl⟩ : syracuseStep 20165543 = 30248315) B30248315
theorem B13443695 : Blo 2097435 13443695 := bstep (se 1 (by rfl) ⟨10082771, by rfl⟩ : syracuseStep 13443695 = 20165543) B20165543
theorem B8962463 : Blo 2097435 8962463 := bstep (se 1 (by rfl) ⟨6721847, by rfl⟩ : syracuseStep 8962463 = 13443695) B13443695
theorem B5974975 : Blo 2097435 5974975 := bstep (se 1 (by rfl) ⟨4481231, by rfl⟩ : syracuseStep 5974975 = 8962463) B8962463
theorem B7966633 : Blo 2097435 7966633 := bstep (se 2 (by rfl) ⟨2987487, by rfl⟩ : syracuseStep 7966633 = 5974975) B5974975
theorem B10622177 : Blo 2097435 10622177 := bstep (se 2 (by rfl) ⟨3983316, by rfl⟩ : syracuseStep 10622177 = 7966633) B7966633
theorem B7081451 : Blo 2097435 7081451 := bstep (se 1 (by rfl) ⟨5311088, by rfl⟩ : syracuseStep 7081451 = 10622177) B10622177
theorem B4720967 : Blo 2097435 4720967 := bstep (se 1 (by rfl) ⟨3540725, by rfl⟩ : syracuseStep 4720967 = 7081451) B7081451
theorem B3147311 : Blo 2097435 3147311 := bstep (se 1 (by rfl) ⟨2360483, by rfl⟩ : syracuseStep 3147311 = 4720967) B4720967
theorem B2098207 : Blo 2097435 2098207 := bstep (se 1 (by rfl) ⟨1573655, by rfl⟩ : syracuseStep 2098207 = 3147311) B3147311
theorem B3147317 : Blo 2097435 3147317 := bbase (se 5 (by rfl) ⟨147530, by rfl⟩ : syracuseStep 3147317 = 295061) (by norm_num)
theorem B2098211 : Blo 2097435 2098211 := bstep (se 1 (by rfl) ⟨1573658, by rfl⟩ : syracuseStep 2098211 = 3147317) B3147317
theorem B5311109 : Blo 2097435 5311109 := bbase (se 4 (by rfl) ⟨497916, by rfl⟩ : syracuseStep 5311109 = 995833) (by norm_num)
theorem B3540739 : Blo 2097435 3540739 := bstep (se 1 (by rfl) ⟨2655554, by rfl⟩ : syracuseStep 3540739 = 5311109) B5311109
theorem B4720985 : Blo 2097435 4720985 := bstep (se 2 (by rfl) ⟨1770369, by rfl⟩ : syracuseStep 4720985 = 3540739) B3540739
theorem B3147323 : Blo 2097435 3147323 := bstep (se 1 (by rfl) ⟨2360492, by rfl⟩ : syracuseStep 3147323 = 4720985) B4720985
theorem B2098215 : Blo 2097435 2098215 := bstep (se 1 (by rfl) ⟨1573661, by rfl⟩ : syracuseStep 2098215 = 3147323) B3147323
theorem B2360497 : Blo 2097435 2360497 := bbase (se 2 (by rfl) ⟨885186, by rfl⟩ : syracuseStep 2360497 = 1770373) (by norm_num)
theorem B3147329 : Blo 2097435 3147329 := bstep (se 2 (by rfl) ⟨1180248, by rfl⟩ : syracuseStep 3147329 = 2360497) B2360497
theorem B2098219 : Blo 2097435 2098219 := bstep (se 1 (by rfl) ⟨1573664, by rfl⟩ : syracuseStep 2098219 = 3147329) B3147329
theorem B2240633 : Blo 2097435 2240633 := bbase (se 2 (by rfl) ⟨840237, by rfl⟩ : syracuseStep 2240633 = 1680475) (by norm_num)
theorem B5975021 : Blo 2097435 5975021 := bstep (se 3 (by rfl) ⟨1120316, by rfl⟩ : syracuseStep 5975021 = 2240633) B2240633
theorem B3983347 : Blo 2097435 3983347 := bstep (se 1 (by rfl) ⟨2987510, by rfl⟩ : syracuseStep 3983347 = 5975021) B5975021
theorem B5311129 : Blo 2097435 5311129 := bstep (se 2 (by rfl) ⟨1991673, by rfl⟩ : syracuseStep 5311129 = 3983347) B3983347
theorem B7081505 : Blo 2097435 7081505 := bstep (se 2 (by rfl) ⟨2655564, by rfl⟩ : syracuseStep 7081505 = 5311129) B5311129
theorem B4721003 : Blo 2097435 4721003 := bstep (se 1 (by rfl) ⟨3540752, by rfl⟩ : syracuseStep 4721003 = 7081505) B7081505
theorem B3147335 : Blo 2097435 3147335 := bstep (se 1 (by rfl) ⟨2360501, by rfl⟩ : syracuseStep 3147335 = 4721003) B4721003
theorem B2098223 : Blo 2097435 2098223 := bstep (se 1 (by rfl) ⟨1573667, by rfl⟩ : syracuseStep 2098223 = 3147335) B3147335
theorem B3147341 : Blo 2097435 3147341 := bbase (se 3 (by rfl) ⟨590126, by rfl⟩ : syracuseStep 3147341 = 1180253) (by norm_num)
theorem B2098227 : Blo 2097435 2098227 := bstep (se 1 (by rfl) ⟨1573670, by rfl⟩ : syracuseStep 2098227 = 3147341) B3147341
theorem B4721021 : Blo 2097435 4721021 := bbase (se 3 (by rfl) ⟨885191, by rfl⟩ : syracuseStep 4721021 = 1770383) (by norm_num)
theorem B3147347 : Blo 2097435 3147347 := bstep (se 1 (by rfl) ⟨2360510, by rfl⟩ : syracuseStep 3147347 = 4721021) B4721021
theorem B2098231 : Blo 2097435 2098231 := bstep (se 1 (by rfl) ⟨1573673, by rfl⟩ : syracuseStep 2098231 = 3147347) B3147347
theorem B3540773 : Blo 2097435 3540773 := bbase (se 4 (by rfl) ⟨331947, by rfl⟩ : syracuseStep 3540773 = 663895) (by norm_num)
theorem B2360515 : Blo 2097435 2360515 := bstep (se 1 (by rfl) ⟨1770386, by rfl⟩ : syracuseStep 2360515 = 3540773) B3540773
theorem B3147353 : Blo 2097435 3147353 := bstep (se 2 (by rfl) ⟨1180257, by rfl⟩ : syracuseStep 3147353 = 2360515) B2360515
theorem B2098235 : Blo 2097435 2098235 := bstep (se 1 (by rfl) ⟨1573676, by rfl⟩ : syracuseStep 2098235 = 3147353) B3147353
theorem B2987533 : Blo 2097435 2987533 := bbase (se 3 (by rfl) ⟨560162, by rfl⟩ : syracuseStep 2987533 = 1120325) (by norm_num)
theorem B15933509 : Blo 2097435 15933509 := bstep (se 4 (by rfl) ⟨1493766, by rfl⟩ : syracuseStep 15933509 = 2987533) B2987533
theorem B10622339 : Blo 2097435 10622339 := bstep (se 1 (by rfl) ⟨7966754, by rfl⟩ : syracuseStep 10622339 = 15933509) B15933509
theorem B7081559 : Blo 2097435 7081559 := bstep (se 1 (by rfl) ⟨5311169, by rfl⟩ : syracuseStep 7081559 = 10622339) B10622339
theorem B4721039 : Blo 2097435 4721039 := bstep (se 1 (by rfl) ⟨3540779, by rfl⟩ : syracuseStep 4721039 = 7081559) B7081559
theorem B3147359 : Blo 2097435 3147359 := bstep (se 1 (by rfl) ⟨2360519, by rfl⟩ : syracuseStep 3147359 = 4721039) B4721039
theorem B2098239 : Blo 2097435 2098239 := bstep (se 1 (by rfl) ⟨1573679, by rfl⟩ : syracuseStep 2098239 = 3147359) B3147359
theorem B3147365 : Blo 2097435 3147365 := bbase (se 4 (by rfl) ⟨295065, by rfl⟩ : syracuseStep 3147365 = 590131) (by norm_num)
theorem B2098243 : Blo 2097435 2098243 := bstep (se 1 (by rfl) ⟨1573682, by rfl⟩ : syracuseStep 2098243 = 3147365) B3147365
theorem B3360989 : Blo 2097435 3360989 := bbase (se 3 (by rfl) ⟨630185, by rfl⟩ : syracuseStep 3360989 = 1260371) (by norm_num)
theorem B2240659 : Blo 2097435 2240659 := bstep (se 1 (by rfl) ⟨1680494, by rfl⟩ : syracuseStep 2240659 = 3360989) B3360989
theorem B2987545 : Blo 2097435 2987545 := bstep (se 2 (by rfl) ⟨1120329, by rfl⟩ : syracuseStep 2987545 = 2240659) B2240659
theorem B3983393 : Blo 2097435 3983393 := bstep (se 2 (by rfl) ⟨1493772, by rfl⟩ : syracuseStep 3983393 = 2987545) B2987545
theorem B2655595 : Blo 2097435 2655595 := bstep (se 1 (by rfl) ⟨1991696, by rfl⟩ : syracuseStep 2655595 = 3983393) B3983393
theorem B3540793 : Blo 2097435 3540793 := bstep (se 2 (by rfl) ⟨1327797, by rfl⟩ : syracuseStep 3540793 = 2655595) B2655595
theorem B4721057 : Blo 2097435 4721057 := bstep (se 2 (by rfl) ⟨1770396, by rfl⟩ : syracuseStep 4721057 = 3540793) B3540793
theorem B3147371 : Blo 2097435 3147371 := bstep (se 1 (by rfl) ⟨2360528, by rfl⟩ : syracuseStep 3147371 = 4721057) B4721057
theorem B2098247 : Blo 2097435 2098247 := bstep (se 1 (by rfl) ⟨1573685, by rfl⟩ : syracuseStep 2098247 = 3147371) B3147371
theorem B2360533 : Blo 2097435 2360533 := bbase (se 7 (by rfl) ⟨27662, by rfl⟩ : syracuseStep 2360533 = 55325) (by norm_num)
theorem B3147377 : Blo 2097435 3147377 := bstep (se 2 (by rfl) ⟨1180266, by rfl⟩ : syracuseStep 3147377 = 2360533) B2360533
theorem B2098251 : Blo 2097435 2098251 := bstep (se 1 (by rfl) ⟨1573688, by rfl⟩ : syracuseStep 2098251 = 3147377) B3147377
theorem B2655605 : Blo 2097435 2655605 := bbase (se 5 (by rfl) ⟨124481, by rfl⟩ : syracuseStep 2655605 = 248963) (by norm_num)
theorem B7081613 : Blo 2097435 7081613 := bstep (se 3 (by rfl) ⟨1327802, by rfl⟩ : syracuseStep 7081613 = 2655605) B2655605
theorem B4721075 : Blo 2097435 4721075 := bstep (se 1 (by rfl) ⟨3540806, by rfl⟩ : syracuseStep 4721075 = 7081613) B7081613
theorem B3147383 : Blo 2097435 3147383 := bstep (se 1 (by rfl) ⟨2360537, by rfl⟩ : syracuseStep 3147383 = 4721075) B4721075
theorem B2098255 : Blo 2097435 2098255 := bstep (se 1 (by rfl) ⟨1573691, by rfl⟩ : syracuseStep 2098255 = 3147383) B3147383
theorem B3147389 : Blo 2097435 3147389 := bbase (se 3 (by rfl) ⟨590135, by rfl⟩ : syracuseStep 3147389 = 1180271) (by norm_num)
theorem B2098259 : Blo 2097435 2098259 := bstep (se 1 (by rfl) ⟨1573694, by rfl⟩ : syracuseStep 2098259 = 3147389) B3147389
theorem B4721093 : Blo 2097435 4721093 := bbase (se 4 (by rfl) ⟨442602, by rfl⟩ : syracuseStep 4721093 = 885205) (by norm_num)
theorem B3147395 : Blo 2097435 3147395 := bstep (se 1 (by rfl) ⟨2360546, by rfl⟩ : syracuseStep 3147395 = 4721093) B4721093
theorem B2098263 : Blo 2097435 2098263 := bstep (se 1 (by rfl) ⟨1573697, by rfl⟩ : syracuseStep 2098263 = 3147395) B3147395
theorem B4785517 : Blo 2097435 4785517 := bbase (se 3 (by rfl) ⟨897284, by rfl⟩ : syracuseStep 4785517 = 1794569) (by norm_num)
theorem B6380689 : Blo 2097435 6380689 := bstep (se 2 (by rfl) ⟨2392758, by rfl⟩ : syracuseStep 6380689 = 4785517) B4785517
theorem B8507585 : Blo 2097435 8507585 := bstep (se 2 (by rfl) ⟨3190344, by rfl⟩ : syracuseStep 8507585 = 6380689) B6380689
theorem B5671723 : Blo 2097435 5671723 := bstep (se 1 (by rfl) ⟨4253792, by rfl⟩ : syracuseStep 5671723 = 8507585) B8507585
theorem B7562297 : Blo 2097435 7562297 := bstep (se 2 (by rfl) ⟨2835861, by rfl⟩ : syracuseStep 7562297 = 5671723) B5671723
theorem B5041531 : Blo 2097435 5041531 := bstep (se 1 (by rfl) ⟨3781148, by rfl⟩ : syracuseStep 5041531 = 7562297) B7562297
theorem B6722041 : Blo 2097435 6722041 := bstep (se 2 (by rfl) ⟨2520765, by rfl⟩ : syracuseStep 6722041 = 5041531) B5041531
theorem B8962721 : Blo 2097435 8962721 := bstep (se 2 (by rfl) ⟨3361020, by rfl⟩ : syracuseStep 8962721 = 6722041) B6722041
theorem B5975147 : Blo 2097435 5975147 := bstep (se 1 (by rfl) ⟨4481360, by rfl⟩ : syracuseStep 5975147 = 8962721) B8962721
theorem B3983431 : Blo 2097435 3983431 := bstep (se 1 (by rfl) ⟨2987573, by rfl⟩ : syracuseStep 3983431 = 5975147) B5975147
theorem B5311241 : Blo 2097435 5311241 := bstep (se 2 (by rfl) ⟨1991715, by rfl⟩ : syracuseStep 5311241 = 3983431) B3983431
theorem B3540827 : Blo 2097435 3540827 := bstep (se 1 (by rfl) ⟨2655620, by rfl⟩ : syracuseStep 3540827 = 5311241) B5311241
theorem B2360551 : Blo 2097435 2360551 := bstep (se 1 (by rfl) ⟨1770413, by rfl⟩ : syracuseStep 2360551 = 3540827) B3540827
theorem B3147401 : Blo 2097435 3147401 := bstep (se 2 (by rfl) ⟨1180275, by rfl⟩ : syracuseStep 3147401 = 2360551) B2360551
theorem B2098267 : Blo 2097435 2098267 := bstep (se 1 (by rfl) ⟨1573700, by rfl⟩ : syracuseStep 2098267 = 3147401) B3147401
theorem B10622501 : Blo 2097435 10622501 := bbase (se 4 (by rfl) ⟨995859, by rfl⟩ : syracuseStep 10622501 = 1991719) (by norm_num)
theorem B7081667 : Blo 2097435 7081667 := bstep (se 1 (by rfl) ⟨5311250, by rfl⟩ : syracuseStep 7081667 = 10622501) B10622501
theorem B4721111 : Blo 2097435 4721111 := bstep (se 1 (by rfl) ⟨3540833, by rfl⟩ : syracuseStep 4721111 = 7081667) B7081667
theorem B3147407 : Blo 2097435 3147407 := bstep (se 1 (by rfl) ⟨2360555, by rfl⟩ : syracuseStep 3147407 = 4721111) B4721111
theorem B2098271 : Blo 2097435 2098271 := bstep (se 1 (by rfl) ⟨1573703, by rfl⟩ : syracuseStep 2098271 = 3147407) B3147407
theorem B3147413 : Blo 2097435 3147413 := bbase (se 6 (by rfl) ⟨73767, by rfl⟩ : syracuseStep 3147413 = 147535) (by norm_num)
theorem B2098275 : Blo 2097435 2098275 := bstep (se 1 (by rfl) ⟨1573706, by rfl⟩ : syracuseStep 2098275 = 3147413) B3147413
theorem B11343509 : Blo 2097435 11343509 := bbase (se 6 (by rfl) ⟨265863, by rfl⟩ : syracuseStep 11343509 = 531727) (by norm_num)
theorem B7562339 : Blo 2097435 7562339 := bstep (se 1 (by rfl) ⟨5671754, by rfl⟩ : syracuseStep 7562339 = 11343509) B11343509
theorem B5041559 : Blo 2097435 5041559 := bstep (se 1 (by rfl) ⟨3781169, by rfl⟩ : syracuseStep 5041559 = 7562339) B7562339
theorem B13444157 : Blo 2097435 13444157 := bstep (se 3 (by rfl) ⟨2520779, by rfl⟩ : syracuseStep 13444157 = 5041559) B5041559
theorem B8962771 : Blo 2097435 8962771 := bstep (se 1 (by rfl) ⟨6722078, by rfl⟩ : syracuseStep 8962771 = 13444157) B13444157
theorem B11950361 : Blo 2097435 11950361 := bstep (se 2 (by rfl) ⟨4481385, by rfl⟩ : syracuseStep 11950361 = 8962771) B8962771
theorem B7966907 : Blo 2097435 7966907 := bstep (se 1 (by rfl) ⟨5975180, by rfl⟩ : syracuseStep 7966907 = 11950361) B11950361
theorem B5311271 : Blo 2097435 5311271 := bstep (se 1 (by rfl) ⟨3983453, by rfl⟩ : syracuseStep 5311271 = 7966907) B7966907
theorem B3540847 : Blo 2097435 3540847 := bstep (se 1 (by rfl) ⟨2655635, by rfl⟩ : syracuseStep 3540847 = 5311271) B5311271
theorem B4721129 : Blo 2097435 4721129 := bstep (se 2 (by rfl) ⟨1770423, by rfl⟩ : syracuseStep 4721129 = 3540847) B3540847
theorem B3147419 : Blo 2097435 3147419 := bstep (se 1 (by rfl) ⟨2360564, by rfl⟩ : syracuseStep 3147419 = 4721129) B4721129
theorem B2098279 : Blo 2097435 2098279 := bstep (se 1 (by rfl) ⟨1573709, by rfl⟩ : syracuseStep 2098279 = 3147419) B3147419
theorem B2360569 : Blo 2097435 2360569 := bbase (se 2 (by rfl) ⟨885213, by rfl⟩ : syracuseStep 2360569 = 1770427) (by norm_num)
theorem B3147425 : Blo 2097435 3147425 := bstep (se 2 (by rfl) ⟨1180284, by rfl⟩ : syracuseStep 3147425 = 2360569) B2360569
theorem B2098283 : Blo 2097435 2098283 := bstep (se 1 (by rfl) ⟨1573712, by rfl⟩ : syracuseStep 2098283 = 3147425) B3147425
theorem B8962805 : Blo 2097435 8962805 := bbase (se 5 (by rfl) ⟨420131, by rfl⟩ : syracuseStep 8962805 = 840263) (by norm_num)
theorem B5975203 : Blo 2097435 5975203 := bstep (se 1 (by rfl) ⟨4481402, by rfl⟩ : syracuseStep 5975203 = 8962805) B8962805
theorem B7966937 : Blo 2097435 7966937 := bstep (se 2 (by rfl) ⟨2987601, by rfl⟩ : syracuseStep 7966937 = 5975203) B5975203
theorem B5311291 : Blo 2097435 5311291 := bstep (se 1 (by rfl) ⟨3983468, by rfl⟩ : syracuseStep 5311291 = 7966937) B7966937
theorem B7081721 : Blo 2097435 7081721 := bstep (se 2 (by rfl) ⟨2655645, by rfl⟩ : syracuseStep 7081721 = 5311291) B5311291
theorem B4721147 : Blo 2097435 4721147 := bstep (se 1 (by rfl) ⟨3540860, by rfl⟩ : syracuseStep 4721147 = 7081721) B7081721
theorem B3147431 : Blo 2097435 3147431 := bstep (se 1 (by rfl) ⟨2360573, by rfl⟩ : syracuseStep 3147431 = 4721147) B4721147
theorem B2098287 : Blo 2097435 2098287 := bstep (se 1 (by rfl) ⟨1573715, by rfl⟩ : syracuseStep 2098287 = 3147431) B3147431
theorem B3147437 : Blo 2097435 3147437 := bbase (se 3 (by rfl) ⟨590144, by rfl⟩ : syracuseStep 3147437 = 1180289) (by norm_num)
theorem B2098291 : Blo 2097435 2098291 := bstep (se 1 (by rfl) ⟨1573718, by rfl⟩ : syracuseStep 2098291 = 3147437) B3147437
theorem B4721165 : Blo 2097435 4721165 := bbase (se 3 (by rfl) ⟨885218, by rfl⟩ : syracuseStep 4721165 = 1770437) (by norm_num)
theorem B3147443 : Blo 2097435 3147443 := bstep (se 1 (by rfl) ⟨2360582, by rfl⟩ : syracuseStep 3147443 = 4721165) B4721165
theorem B2098295 : Blo 2097435 2098295 := bstep (se 1 (by rfl) ⟨1573721, by rfl⟩ : syracuseStep 2098295 = 3147443) B3147443
theorem B2655661 : Blo 2097435 2655661 := bbase (se 3 (by rfl) ⟨497936, by rfl⟩ : syracuseStep 2655661 = 995873) (by norm_num)
theorem B3540881 : Blo 2097435 3540881 := bstep (se 2 (by rfl) ⟨1327830, by rfl⟩ : syracuseStep 3540881 = 2655661) B2655661
theorem B2360587 : Blo 2097435 2360587 := bstep (se 1 (by rfl) ⟨1770440, by rfl⟩ : syracuseStep 2360587 = 3540881) B3540881
theorem B3147449 : Blo 2097435 3147449 := bstep (se 2 (by rfl) ⟨1180293, by rfl⟩ : syracuseStep 3147449 = 2360587) B2360587
theorem B2098299 : Blo 2097435 2098299 := bstep (se 1 (by rfl) ⟨1573724, by rfl⟩ : syracuseStep 2098299 = 3147449) B3147449
theorem B13444309 : Blo 2097435 13444309 := bbase (se 7 (by rfl) ⟨157550, by rfl⟩ : syracuseStep 13444309 = 315101) (by norm_num)
theorem B17925745 : Blo 2097435 17925745 := bstep (se 2 (by rfl) ⟨6722154, by rfl⟩ : syracuseStep 17925745 = 13444309) B13444309
theorem B23900993 : Blo 2097435 23900993 := bstep (se 2 (by rfl) ⟨8962872, by rfl⟩ : syracuseStep 23900993 = 17925745) B17925745
theorem B15933995 : Blo 2097435 15933995 := bstep (se 1 (by rfl) ⟨11950496, by rfl⟩ : syracuseStep 15933995 = 23900993) B23900993
theorem B10622663 : Blo 2097435 10622663 := bstep (se 1 (by rfl) ⟨7966997, by rfl⟩ : syracuseStep 10622663 = 15933995) B15933995
theorem B7081775 : Blo 2097435 7081775 := bstep (se 1 (by rfl) ⟨5311331, by rfl⟩ : syracuseStep 7081775 = 10622663) B10622663
theorem B4721183 : Blo 2097435 4721183 := bstep (se 1 (by rfl) ⟨3540887, by rfl⟩ : syracuseStep 4721183 = 7081775) B7081775
theorem B3147455 : Blo 2097435 3147455 := bstep (se 1 (by rfl) ⟨2360591, by rfl⟩ : syracuseStep 3147455 = 4721183) B4721183
theorem B2098303 : Blo 2097435 2098303 := bstep (se 1 (by rfl) ⟨1573727, by rfl⟩ : syracuseStep 2098303 = 3147455) B3147455
theorem B3147461 : Blo 2097435 3147461 := bbase (se 4 (by rfl) ⟨295074, by rfl⟩ : syracuseStep 3147461 = 590149) (by norm_num)
theorem B2098307 : Blo 2097435 2098307 := bstep (se 1 (by rfl) ⟨1573730, by rfl⟩ : syracuseStep 2098307 = 3147461) B3147461
theorem B3540901 : Blo 2097435 3540901 := bbase (se 4 (by rfl) ⟨331959, by rfl⟩ : syracuseStep 3540901 = 663919) (by norm_num)
theorem B4721201 : Blo 2097435 4721201 := bstep (se 2 (by rfl) ⟨1770450, by rfl⟩ : syracuseStep 4721201 = 3540901) B3540901
theorem B3147467 : Blo 2097435 3147467 := bstep (se 1 (by rfl) ⟨2360600, by rfl⟩ : syracuseStep 3147467 = 4721201) B4721201
theorem B2098311 : Blo 2097435 2098311 := bstep (se 1 (by rfl) ⟨1573733, by rfl⟩ : syracuseStep 2098311 = 3147467) B3147467
theorem B2360605 : Blo 2097435 2360605 := bbase (se 3 (by rfl) ⟨442613, by rfl⟩ : syracuseStep 2360605 = 885227) (by norm_num)
theorem B3147473 : Blo 2097435 3147473 := bstep (se 2 (by rfl) ⟨1180302, by rfl⟩ : syracuseStep 3147473 = 2360605) B2360605
theorem B2098315 : Blo 2097435 2098315 := bstep (se 1 (by rfl) ⟨1573736, by rfl⟩ : syracuseStep 2098315 = 3147473) B3147473
theorem B7081829 : Blo 2097435 7081829 := bbase (se 4 (by rfl) ⟨663921, by rfl⟩ : syracuseStep 7081829 = 1327843) (by norm_num)
theorem B4721219 : Blo 2097435 4721219 := bstep (se 1 (by rfl) ⟨3540914, by rfl⟩ : syracuseStep 4721219 = 7081829) B7081829
theorem B3147479 : Blo 2097435 3147479 := bstep (se 1 (by rfl) ⟨2360609, by rfl⟩ : syracuseStep 3147479 = 4721219) B4721219
theorem B2098319 : Blo 2097435 2098319 := bstep (se 1 (by rfl) ⟨1573739, by rfl⟩ : syracuseStep 2098319 = 3147479) B3147479
theorem B3147485 : Blo 2097435 3147485 := bbase (se 3 (by rfl) ⟨590153, by rfl⟩ : syracuseStep 3147485 = 1180307) (by norm_num)
theorem B2098323 : Blo 2097435 2098323 := bstep (se 1 (by rfl) ⟨1573742, by rfl⟩ : syracuseStep 2098323 = 3147485) B3147485
theorem B4721237 : Blo 2097435 4721237 := bbase (se 8 (by rfl) ⟨27663, by rfl⟩ : syracuseStep 4721237 = 55327) (by norm_num)
theorem B3147491 : Blo 2097435 3147491 := bstep (se 1 (by rfl) ⟨2360618, by rfl⟩ : syracuseStep 3147491 = 4721237) B4721237
theorem B2098327 : Blo 2097435 2098327 := bstep (se 1 (by rfl) ⟨1573745, by rfl⟩ : syracuseStep 2098327 = 3147491) B3147491
theorem B5041685 : Blo 2097435 5041685 := bbase (se 6 (by rfl) ⟨118164, by rfl⟩ : syracuseStep 5041685 = 236329) (by norm_num)
theorem B3361123 : Blo 2097435 3361123 := bstep (se 1 (by rfl) ⟨2520842, by rfl⟩ : syracuseStep 3361123 = 5041685) B5041685
theorem B4481497 : Blo 2097435 4481497 := bstep (se 2 (by rfl) ⟨1680561, by rfl⟩ : syracuseStep 4481497 = 3361123) B3361123
theorem B5975329 : Blo 2097435 5975329 := bstep (se 2 (by rfl) ⟨2240748, by rfl⟩ : syracuseStep 5975329 = 4481497) B4481497
theorem B7967105 : Blo 2097435 7967105 := bstep (se 2 (by rfl) ⟨2987664, by rfl⟩ : syracuseStep 7967105 = 5975329) B5975329
theorem B5311403 : Blo 2097435 5311403 := bstep (se 1 (by rfl) ⟨3983552, by rfl⟩ : syracuseStep 5311403 = 7967105) B7967105
theorem B3540935 : Blo 2097435 3540935 := bstep (se 1 (by rfl) ⟨2655701, by rfl⟩ : syracuseStep 3540935 = 5311403) B5311403
theorem B2360623 : Blo 2097435 2360623 := bstep (se 1 (by rfl) ⟨1770467, by rfl⟩ : syracuseStep 2360623 = 3540935) B3540935
theorem B3147497 : Blo 2097435 3147497 := bstep (se 2 (by rfl) ⟨1180311, by rfl⟩ : syracuseStep 3147497 = 2360623) B2360623
theorem B2098331 : Blo 2097435 2098331 := bstep (se 1 (by rfl) ⟨1573748, by rfl⟩ : syracuseStep 2098331 = 3147497) B3147497
theorem B5041693 : Blo 2097435 5041693 := bbase (se 3 (by rfl) ⟨945317, by rfl⟩ : syracuseStep 5041693 = 1890635) (by norm_num)
theorem B26889029 : Blo 2097435 26889029 := bstep (se 4 (by rfl) ⟨2520846, by rfl⟩ : syracuseStep 26889029 = 5041693) B5041693
theorem B17926019 : Blo 2097435 17926019 := bstep (se 1 (by rfl) ⟨13444514, by rfl⟩ : syracuseStep 17926019 = 26889029) B26889029
theorem B11950679 : Blo 2097435 11950679 := bstep (se 1 (by rfl) ⟨8963009, by rfl⟩ : syracuseStep 11950679 = 17926019) B17926019
theorem B7967119 : Blo 2097435 7967119 := bstep (se 1 (by rfl) ⟨5975339, by rfl⟩ : syracuseStep 7967119 = 11950679) B11950679
theorem B10622825 : Blo 2097435 10622825 := bstep (se 2 (by rfl) ⟨3983559, by rfl⟩ : syracuseStep 10622825 = 7967119) B7967119
theorem B7081883 : Blo 2097435 7081883 := bstep (se 1 (by rfl) ⟨5311412, by rfl⟩ : syracuseStep 7081883 = 10622825) B10622825
theorem B4721255 : Blo 2097435 4721255 := bstep (se 1 (by rfl) ⟨3540941, by rfl⟩ : syracuseStep 4721255 = 7081883) B7081883
theorem B3147503 : Blo 2097435 3147503 := bstep (se 1 (by rfl) ⟨2360627, by rfl⟩ : syracuseStep 3147503 = 4721255) B4721255
theorem B2098335 : Blo 2097435 2098335 := bstep (se 1 (by rfl) ⟨1573751, by rfl⟩ : syracuseStep 2098335 = 3147503) B3147503
theorem B3147509 : Blo 2097435 3147509 := bbase (se 5 (by rfl) ⟨147539, by rfl⟩ : syracuseStep 3147509 = 295079) (by norm_num)
theorem B2098339 : Blo 2097435 2098339 := bstep (se 1 (by rfl) ⟨1573754, by rfl⟩ : syracuseStep 2098339 = 3147509) B3147509
theorem B8963045 : Blo 2097435 8963045 := bbase (se 4 (by rfl) ⟨840285, by rfl⟩ : syracuseStep 8963045 = 1680571) (by norm_num)
theorem B5975363 : Blo 2097435 5975363 := bstep (se 1 (by rfl) ⟨4481522, by rfl⟩ : syracuseStep 5975363 = 8963045) B8963045
theorem B3983575 : Blo 2097435 3983575 := bstep (se 1 (by rfl) ⟨2987681, by rfl⟩ : syracuseStep 3983575 = 5975363) B5975363
theorem B5311433 : Blo 2097435 5311433 := bstep (se 2 (by rfl) ⟨1991787, by rfl⟩ : syracuseStep 5311433 = 3983575) B3983575
theorem B3540955 : Blo 2097435 3540955 := bstep (se 1 (by rfl) ⟨2655716, by rfl⟩ : syracuseStep 3540955 = 5311433) B5311433
theorem B4721273 : Blo 2097435 4721273 := bstep (se 2 (by rfl) ⟨1770477, by rfl⟩ : syracuseStep 4721273 = 3540955) B3540955
theorem B3147515 : Blo 2097435 3147515 := bstep (se 1 (by rfl) ⟨2360636, by rfl⟩ : syracuseStep 3147515 = 4721273) B4721273
theorem B2098343 : Blo 2097435 2098343 := bstep (se 1 (by rfl) ⟨1573757, by rfl⟩ : syracuseStep 2098343 = 3147515) B3147515
theorem B2360641 : Blo 2097435 2360641 := bbase (se 2 (by rfl) ⟨885240, by rfl⟩ : syracuseStep 2360641 = 1770481) (by norm_num)
theorem B3147521 : Blo 2097435 3147521 := bstep (se 2 (by rfl) ⟨1180320, by rfl⟩ : syracuseStep 3147521 = 2360641) B2360641
theorem B2098347 : Blo 2097435 2098347 := bstep (se 1 (by rfl) ⟨1573760, by rfl⟩ : syracuseStep 2098347 = 3147521) B3147521
theorem B5311453 : Blo 2097435 5311453 := bbase (se 3 (by rfl) ⟨995897, by rfl⟩ : syracuseStep 5311453 = 1991795) (by norm_num)
theorem B7081937 : Blo 2097435 7081937 := bstep (se 2 (by rfl) ⟨2655726, by rfl⟩ : syracuseStep 7081937 = 5311453) B5311453
theorem B4721291 : Blo 2097435 4721291 := bstep (se 1 (by rfl) ⟨3540968, by rfl⟩ : syracuseStep 4721291 = 7081937) B7081937
theorem B3147527 : Blo 2097435 3147527 := bstep (se 1 (by rfl) ⟨2360645, by rfl⟩ : syracuseStep 3147527 = 4721291) B4721291
theorem B2098351 : Blo 2097435 2098351 := bstep (se 1 (by rfl) ⟨1573763, by rfl⟩ : syracuseStep 2098351 = 3147527) B3147527
theorem B3147533 : Blo 2097435 3147533 := bbase (se 3 (by rfl) ⟨590162, by rfl⟩ : syracuseStep 3147533 = 1180325) (by norm_num)
theorem B2098355 : Blo 2097435 2098355 := bstep (se 1 (by rfl) ⟨1573766, by rfl⟩ : syracuseStep 2098355 = 3147533) B3147533
theorem B4721309 : Blo 2097435 4721309 := bbase (se 3 (by rfl) ⟨885245, by rfl⟩ : syracuseStep 4721309 = 1770491) (by norm_num)
theorem B3147539 : Blo 2097435 3147539 := bstep (se 1 (by rfl) ⟨2360654, by rfl⟩ : syracuseStep 3147539 = 4721309) B4721309
theorem B2098359 : Blo 2097435 2098359 := bstep (se 1 (by rfl) ⟨1573769, by rfl⟩ : syracuseStep 2098359 = 3147539) B3147539
theorem B3540989 : Blo 2097435 3540989 := bbase (se 3 (by rfl) ⟨663935, by rfl⟩ : syracuseStep 3540989 = 1327871) (by norm_num)
theorem B2360659 : Blo 2097435 2360659 := bstep (se 1 (by rfl) ⟨1770494, by rfl⟩ : syracuseStep 2360659 = 3540989) B3540989
theorem B3147545 : Blo 2097435 3147545 := bstep (se 2 (by rfl) ⟨1180329, by rfl⟩ : syracuseStep 3147545 = 2360659) B2360659
theorem B2098363 : Blo 2097435 2098363 := bstep (se 1 (by rfl) ⟨1573772, by rfl⟩ : syracuseStep 2098363 = 3147545) B3147545
theorem B4481573 : Blo 2097435 4481573 := bbase (se 4 (by rfl) ⟨420147, by rfl⟩ : syracuseStep 4481573 = 840295) (by norm_num)
theorem B11950861 : Blo 2097435 11950861 := bstep (se 3 (by rfl) ⟨2240786, by rfl⟩ : syracuseStep 11950861 = 4481573) B4481573
theorem B15934481 : Blo 2097435 15934481 := bstep (se 2 (by rfl) ⟨5975430, by rfl⟩ : syracuseStep 15934481 = 11950861) B11950861
theorem B10622987 : Blo 2097435 10622987 := bstep (se 1 (by rfl) ⟨7967240, by rfl⟩ : syracuseStep 10622987 = 15934481) B15934481
theorem B7081991 : Blo 2097435 7081991 := bstep (se 1 (by rfl) ⟨5311493, by rfl⟩ : syracuseStep 7081991 = 10622987) B10622987
theorem B4721327 : Blo 2097435 4721327 := bstep (se 1 (by rfl) ⟨3540995, by rfl⟩ : syracuseStep 4721327 = 7081991) B7081991
theorem B3147551 : Blo 2097435 3147551 := bstep (se 1 (by rfl) ⟨2360663, by rfl⟩ : syracuseStep 3147551 = 4721327) B4721327
theorem B2098367 : Blo 2097435 2098367 := bstep (se 1 (by rfl) ⟨1573775, by rfl⟩ : syracuseStep 2098367 = 3147551) B3147551
theorem B3147557 : Blo 2097435 3147557 := bbase (se 4 (by rfl) ⟨295083, by rfl⟩ : syracuseStep 3147557 = 590167) (by norm_num)
theorem B2098371 : Blo 2097435 2098371 := bstep (se 1 (by rfl) ⟨1573778, by rfl⟩ : syracuseStep 2098371 = 3147557) B3147557
theorem B2655757 : Blo 2097435 2655757 := bbase (se 3 (by rfl) ⟨497954, by rfl⟩ : syracuseStep 2655757 = 995909) (by norm_num)
theorem B3541009 : Blo 2097435 3541009 := bstep (se 2 (by rfl) ⟨1327878, by rfl⟩ : syracuseStep 3541009 = 2655757) B2655757
theorem B4721345 : Blo 2097435 4721345 := bstep (se 2 (by rfl) ⟨1770504, by rfl⟩ : syracuseStep 4721345 = 3541009) B3541009
theorem B3147563 : Blo 2097435 3147563 := bstep (se 1 (by rfl) ⟨2360672, by rfl⟩ : syracuseStep 3147563 = 4721345) B4721345
theorem B2098375 : Blo 2097435 2098375 := bstep (se 1 (by rfl) ⟨1573781, by rfl⟩ : syracuseStep 2098375 = 3147563) B3147563
theorem B2360677 : Blo 2097435 2360677 := bbase (se 4 (by rfl) ⟨221313, by rfl⟩ : syracuseStep 2360677 = 442627) (by norm_num)
theorem B3147569 : Blo 2097435 3147569 := bstep (se 2 (by rfl) ⟨1180338, by rfl⟩ : syracuseStep 3147569 = 2360677) B2360677
theorem B2098379 : Blo 2097435 2098379 := bstep (se 1 (by rfl) ⟨1573784, by rfl⟩ : syracuseStep 2098379 = 3147569) B3147569
theorem B5975477 : Blo 2097435 5975477 := bbase (se 5 (by rfl) ⟨280100, by rfl⟩ : syracuseStep 5975477 = 560201) (by norm_num)
theorem B3983651 : Blo 2097435 3983651 := bstep (se 1 (by rfl) ⟨2987738, by rfl⟩ : syracuseStep 3983651 = 5975477) B5975477
theorem B2655767 : Blo 2097435 2655767 := bstep (se 1 (by rfl) ⟨1991825, by rfl⟩ : syracuseStep 2655767 = 3983651) B3983651
theorem B7082045 : Blo 2097435 7082045 := bstep (se 3 (by rfl) ⟨1327883, by rfl⟩ : syracuseStep 7082045 = 2655767) B2655767
theorem B4721363 : Blo 2097435 4721363 := bstep (se 1 (by rfl) ⟨3541022, by rfl⟩ : syracuseStep 4721363 = 7082045) B7082045
theorem B3147575 : Blo 2097435 3147575 := bstep (se 1 (by rfl) ⟨2360681, by rfl⟩ : syracuseStep 3147575 = 4721363) B4721363
theorem B2098383 : Blo 2097435 2098383 := bstep (se 1 (by rfl) ⟨1573787, by rfl⟩ : syracuseStep 2098383 = 3147575) B3147575
theorem B3147581 : Blo 2097435 3147581 := bbase (se 3 (by rfl) ⟨590171, by rfl⟩ : syracuseStep 3147581 = 1180343) (by norm_num)
theorem B2098387 : Blo 2097435 2098387 := bstep (se 1 (by rfl) ⟨1573790, by rfl⟩ : syracuseStep 2098387 = 3147581) B3147581
theorem B4721381 : Blo 2097435 4721381 := bbase (se 4 (by rfl) ⟨442629, by rfl⟩ : syracuseStep 4721381 = 885259) (by norm_num)
theorem B3147587 : Blo 2097435 3147587 := bstep (se 1 (by rfl) ⟨2360690, by rfl⟩ : syracuseStep 3147587 = 4721381) B4721381
theorem B2098391 : Blo 2097435 2098391 := bstep (se 1 (by rfl) ⟨1573793, by rfl⟩ : syracuseStep 2098391 = 3147587) B3147587
theorem B5311565 : Blo 2097435 5311565 := bbase (se 3 (by rfl) ⟨995918, by rfl⟩ : syracuseStep 5311565 = 1991837) (by norm_num)
theorem B3541043 : Blo 2097435 3541043 := bstep (se 1 (by rfl) ⟨2655782, by rfl⟩ : syracuseStep 3541043 = 5311565) B5311565
theorem B2360695 : Blo 2097435 2360695 := bstep (se 1 (by rfl) ⟨1770521, by rfl⟩ : syracuseStep 2360695 = 3541043) B3541043
theorem B3147593 : Blo 2097435 3147593 := bstep (se 2 (by rfl) ⟨1180347, by rfl⟩ : syracuseStep 3147593 = 2360695) B2360695
theorem B2098395 : Blo 2097435 2098395 := bstep (se 1 (by rfl) ⟨1573796, by rfl⟩ : syracuseStep 2098395 = 3147593) B3147593
theorem B2240821 : Blo 2097435 2240821 := bbase (se 5 (by rfl) ⟨105038, by rfl⟩ : syracuseStep 2240821 = 210077) (by norm_num)
theorem B2987761 : Blo 2097435 2987761 := bstep (se 2 (by rfl) ⟨1120410, by rfl⟩ : syracuseStep 2987761 = 2240821) B2240821
theorem B3983681 : Blo 2097435 3983681 := bstep (se 2 (by rfl) ⟨1493880, by rfl⟩ : syracuseStep 3983681 = 2987761) B2987761
theorem B10623149 : Blo 2097435 10623149 := bstep (se 3 (by rfl) ⟨1991840, by rfl⟩ : syracuseStep 10623149 = 3983681) B3983681
theorem B7082099 : Blo 2097435 7082099 := bstep (se 1 (by rfl) ⟨5311574, by rfl⟩ : syracuseStep 7082099 = 10623149) B10623149
theorem B4721399 : Blo 2097435 4721399 := bstep (se 1 (by rfl) ⟨3541049, by rfl⟩ : syracuseStep 4721399 = 7082099) B7082099
theorem B3147599 : Blo 2097435 3147599 := bstep (se 1 (by rfl) ⟨2360699, by rfl⟩ : syracuseStep 3147599 = 4721399) B4721399
theorem B2098399 : Blo 2097435 2098399 := bstep (se 1 (by rfl) ⟨1573799, by rfl⟩ : syracuseStep 2098399 = 3147599) B3147599
theorem B3147605 : Blo 2097435 3147605 := bbase (se 9 (by rfl) ⟨9221, by rfl⟩ : syracuseStep 3147605 = 18443) (by norm_num)
theorem B2098403 : Blo 2097435 2098403 := bstep (se 1 (by rfl) ⟨1573802, by rfl⟩ : syracuseStep 2098403 = 3147605) B3147605
theorem B5672101 : Blo 2097435 5672101 := bbase (se 4 (by rfl) ⟨531759, by rfl⟩ : syracuseStep 5672101 = 1063519) (by norm_num)
theorem B7562801 : Blo 2097435 7562801 := bstep (se 2 (by rfl) ⟨2836050, by rfl⟩ : syracuseStep 7562801 = 5672101) B5672101
theorem B5041867 : Blo 2097435 5041867 := bstep (se 1 (by rfl) ⟨3781400, by rfl⟩ : syracuseStep 5041867 = 7562801) B7562801
theorem B6722489 : Blo 2097435 6722489 := bstep (se 2 (by rfl) ⟨2520933, by rfl⟩ : syracuseStep 6722489 = 5041867) B5041867
theorem B4481659 : Blo 2097435 4481659 := bstep (se 1 (by rfl) ⟨3361244, by rfl⟩ : syracuseStep 4481659 = 6722489) B6722489
theorem B5975545 : Blo 2097435 5975545 := bstep (se 2 (by rfl) ⟨2240829, by rfl⟩ : syracuseStep 5975545 = 4481659) B4481659
theorem B7967393 : Blo 2097435 7967393 := bstep (se 2 (by rfl) ⟨2987772, by rfl⟩ : syracuseStep 7967393 = 5975545) B5975545
theorem B5311595 : Blo 2097435 5311595 := bstep (se 1 (by rfl) ⟨3983696, by rfl⟩ : syracuseStep 5311595 = 7967393) B7967393
theorem B3541063 : Blo 2097435 3541063 := bstep (se 1 (by rfl) ⟨2655797, by rfl⟩ : syracuseStep 3541063 = 5311595) B5311595
theorem B4721417 : Blo 2097435 4721417 := bstep (se 2 (by rfl) ⟨1770531, by rfl⟩ : syracuseStep 4721417 = 3541063) B3541063
theorem B3147611 : Blo 2097435 3147611 := bstep (se 1 (by rfl) ⟨2360708, by rfl⟩ : syracuseStep 3147611 = 4721417) B4721417
theorem B2098407 : Blo 2097435 2098407 := bstep (se 1 (by rfl) ⟨1573805, by rfl⟩ : syracuseStep 2098407 = 3147611) B3147611
theorem B2360713 : Blo 2097435 2360713 := bbase (se 2 (by rfl) ⟨885267, by rfl⟩ : syracuseStep 2360713 = 1770535) (by norm_num)
theorem B3147617 : Blo 2097435 3147617 := bstep (se 2 (by rfl) ⟨1180356, by rfl⟩ : syracuseStep 3147617 = 2360713) B2360713
theorem B2098411 : Blo 2097435 2098411 := bstep (se 1 (by rfl) ⟨1573808, by rfl⟩ : syracuseStep 2098411 = 3147617) B3147617
theorem B14357557 : Blo 2097435 14357557 := bbase (se 5 (by rfl) ⟨673010, by rfl⟩ : syracuseStep 14357557 = 1346021) (by norm_num)
theorem B76573637 : Blo 2097435 76573637 := bstep (se 4 (by rfl) ⟨7178778, by rfl⟩ : syracuseStep 76573637 = 14357557) B14357557
theorem B51049091 : Blo 2097435 51049091 := bstep (se 1 (by rfl) ⟨38286818, by rfl⟩ : syracuseStep 51049091 = 76573637) B76573637
theorem B34032727 : Blo 2097435 34032727 := bstep (se 1 (by rfl) ⟨25524545, by rfl⟩ : syracuseStep 34032727 = 51049091) B51049091
theorem B45376969 : Blo 2097435 45376969 := bstep (se 2 (by rfl) ⟨17016363, by rfl⟩ : syracuseStep 45376969 = 34032727) B34032727
theorem B60502625 : Blo 2097435 60502625 := bstep (se 2 (by rfl) ⟨22688484, by rfl⟩ : syracuseStep 60502625 = 45376969) B45376969
theorem B40335083 : Blo 2097435 40335083 := bstep (se 1 (by rfl) ⟨30251312, by rfl⟩ : syracuseStep 40335083 = 60502625) B60502625
theorem B26890055 : Blo 2097435 26890055 := bstep (se 1 (by rfl) ⟨20167541, by rfl⟩ : syracuseStep 26890055 = 40335083) B40335083
theorem B17926703 : Blo 2097435 17926703 := bstep (se 1 (by rfl) ⟨13445027, by rfl⟩ : syracuseStep 17926703 = 26890055) B26890055
theorem B11951135 : Blo 2097435 11951135 := bstep (se 1 (by rfl) ⟨8963351, by rfl⟩ : syracuseStep 11951135 = 17926703) B17926703
theorem B7967423 : Blo 2097435 7967423 := bstep (se 1 (by rfl) ⟨5975567, by rfl⟩ : syracuseStep 7967423 = 11951135) B11951135
theorem B5311615 : Blo 2097435 5311615 := bstep (se 1 (by rfl) ⟨3983711, by rfl⟩ : syracuseStep 5311615 = 7967423) B7967423
theorem B7082153 : Blo 2097435 7082153 := bstep (se 2 (by rfl) ⟨2655807, by rfl⟩ : syracuseStep 7082153 = 5311615) B5311615
theorem B4721435 : Blo 2097435 4721435 := bstep (se 1 (by rfl) ⟨3541076, by rfl⟩ : syracuseStep 4721435 = 7082153) B7082153
theorem B3147623 : Blo 2097435 3147623 := bstep (se 1 (by rfl) ⟨2360717, by rfl⟩ : syracuseStep 3147623 = 4721435) B4721435
theorem B2098415 : Blo 2097435 2098415 := bstep (se 1 (by rfl) ⟨1573811, by rfl⟩ : syracuseStep 2098415 = 3147623) B3147623
theorem B3147629 : Blo 2097435 3147629 := bbase (se 3 (by rfl) ⟨590180, by rfl⟩ : syracuseStep 3147629 = 1180361) (by norm_num)
theorem B2098419 : Blo 2097435 2098419 := bstep (se 1 (by rfl) ⟨1573814, by rfl⟩ : syracuseStep 2098419 = 3147629) B3147629
theorem B4721453 : Blo 2097435 4721453 := bbase (se 3 (by rfl) ⟨885272, by rfl⟩ : syracuseStep 4721453 = 1770545) (by norm_num)
theorem B3147635 : Blo 2097435 3147635 := bstep (se 1 (by rfl) ⟨2360726, by rfl⟩ : syracuseStep 3147635 = 4721453) B4721453
theorem B2098423 : Blo 2097435 2098423 := bstep (se 1 (by rfl) ⟨1573817, by rfl⟩ : syracuseStep 2098423 = 3147635) B3147635
theorem B3361277 : Blo 2097435 3361277 := bbase (se 3 (by rfl) ⟨630239, by rfl⟩ : syracuseStep 3361277 = 1260479) (by norm_num)
theorem B8963405 : Blo 2097435 8963405 := bstep (se 3 (by rfl) ⟨1680638, by rfl⟩ : syracuseStep 8963405 = 3361277) B3361277
theorem B5975603 : Blo 2097435 5975603 := bstep (se 1 (by rfl) ⟨4481702, by rfl⟩ : syracuseStep 5975603 = 8963405) B8963405
theorem B3983735 : Blo 2097435 3983735 := bstep (se 1 (by rfl) ⟨2987801, by rfl⟩ : syracuseStep 3983735 = 5975603) B5975603
theorem B2655823 : Blo 2097435 2655823 := bstep (se 1 (by rfl) ⟨1991867, by rfl⟩ : syracuseStep 2655823 = 3983735) B3983735
theorem B3541097 : Blo 2097435 3541097 := bstep (se 2 (by rfl) ⟨1327911, by rfl⟩ : syracuseStep 3541097 = 2655823) B2655823
theorem B2360731 : Blo 2097435 2360731 := bstep (se 1 (by rfl) ⟨1770548, by rfl⟩ : syracuseStep 2360731 = 3541097) B3541097
theorem B3147641 : Blo 2097435 3147641 := bstep (se 2 (by rfl) ⟨1180365, by rfl⟩ : syracuseStep 3147641 = 2360731) B2360731
theorem B2098427 : Blo 2097435 2098427 := bstep (se 1 (by rfl) ⟨1573820, by rfl⟩ : syracuseStep 2098427 = 3147641) B3147641
theorem B3234125 : Blo 2097435 3234125 := bbase (se 3 (by rfl) ⟨606398, by rfl⟩ : syracuseStep 3234125 = 1212797) (by norm_num)
theorem B8624333 : Blo 2097435 8624333 := bstep (se 3 (by rfl) ⟨1617062, by rfl⟩ : syracuseStep 8624333 = 3234125) B3234125
theorem B5749555 : Blo 2097435 5749555 := bstep (se 1 (by rfl) ⟨4312166, by rfl⟩ : syracuseStep 5749555 = 8624333) B8624333
theorem B7666073 : Blo 2097435 7666073 := bstep (se 2 (by rfl) ⟨2874777, by rfl⟩ : syracuseStep 7666073 = 5749555) B5749555
theorem B5110715 : Blo 2097435 5110715 := bstep (se 1 (by rfl) ⟨3833036, by rfl⟩ : syracuseStep 5110715 = 7666073) B7666073
theorem B13628573 : Blo 2097435 13628573 := bstep (se 3 (by rfl) ⟨2555357, by rfl⟩ : syracuseStep 13628573 = 5110715) B5110715
theorem B9085715 : Blo 2097435 9085715 := bstep (se 1 (by rfl) ⟨6814286, by rfl⟩ : syracuseStep 9085715 = 13628573) B13628573
theorem B6057143 : Blo 2097435 6057143 := bstep (se 1 (by rfl) ⟨4542857, by rfl⟩ : syracuseStep 6057143 = 9085715) B9085715
theorem B4038095 : Blo 2097435 4038095 := bstep (se 1 (by rfl) ⟨3028571, by rfl⟩ : syracuseStep 4038095 = 6057143) B6057143
theorem B2692063 : Blo 2097435 2692063 := bstep (se 1 (by rfl) ⟨2019047, by rfl⟩ : syracuseStep 2692063 = 4038095) B4038095
theorem B3589417 : Blo 2097435 3589417 := bstep (se 2 (by rfl) ⟨1346031, by rfl⟩ : syracuseStep 3589417 = 2692063) B2692063
theorem B4785889 : Blo 2097435 4785889 := bstep (se 2 (by rfl) ⟨1794708, by rfl⟩ : syracuseStep 4785889 = 3589417) B3589417
theorem B6381185 : Blo 2097435 6381185 := bstep (se 2 (by rfl) ⟨2392944, by rfl⟩ : syracuseStep 6381185 = 4785889) B4785889
theorem B17016493 : Blo 2097435 17016493 := bstep (se 3 (by rfl) ⟨3190592, by rfl⟩ : syracuseStep 17016493 = 6381185) B6381185
theorem B22688657 : Blo 2097435 22688657 := bstep (se 2 (by rfl) ⟨8508246, by rfl⟩ : syracuseStep 22688657 = 17016493) B17016493
theorem B15125771 : Blo 2097435 15125771 := bstep (se 1 (by rfl) ⟨11344328, by rfl⟩ : syracuseStep 15125771 = 22688657) B22688657
theorem B10083847 : Blo 2097435 10083847 := bstep (se 1 (by rfl) ⟨7562885, by rfl⟩ : syracuseStep 10083847 = 15125771) B15125771
theorem B13445129 : Blo 2097435 13445129 := bstep (se 2 (by rfl) ⟨5041923, by rfl⟩ : syracuseStep 13445129 = 10083847) B10083847
theorem B35853677 : Blo 2097435 35853677 := bstep (se 3 (by rfl) ⟨6722564, by rfl⟩ : syracuseStep 35853677 = 13445129) B13445129
theorem B23902451 : Blo 2097435 23902451 := bstep (se 1 (by rfl) ⟨17926838, by rfl⟩ : syracuseStep 23902451 = 35853677) B35853677
theorem B15934967 : Blo 2097435 15934967 := bstep (se 1 (by rfl) ⟨11951225, by rfl⟩ : syracuseStep 15934967 = 23902451) B23902451
theorem B10623311 : Blo 2097435 10623311 := bstep (se 1 (by rfl) ⟨7967483, by rfl⟩ : syracuseStep 10623311 = 15934967) B15934967
theorem B7082207 : Blo 2097435 7082207 := bstep (se 1 (by rfl) ⟨5311655, by rfl⟩ : syracuseStep 7082207 = 10623311) B10623311
theorem B4721471 : Blo 2097435 4721471 := bstep (se 1 (by rfl) ⟨3541103, by rfl⟩ : syracuseStep 4721471 = 7082207) B7082207
theorem B3147647 : Blo 2097435 3147647 := bstep (se 1 (by rfl) ⟨2360735, by rfl⟩ : syracuseStep 3147647 = 4721471) B4721471
theorem B2098431 : Blo 2097435 2098431 := bstep (se 1 (by rfl) ⟨1573823, by rfl⟩ : syracuseStep 2098431 = 3147647) B3147647
theorem B3147653 : Blo 2097435 3147653 := bbase (se 4 (by rfl) ⟨295092, by rfl⟩ : syracuseStep 3147653 = 590185) (by norm_num)
theorem B2098435 : Blo 2097435 2098435 := bstep (se 1 (by rfl) ⟨1573826, by rfl⟩ : syracuseStep 2098435 = 3147653) B3147653
theorem B3541117 : Blo 2097435 3541117 := bbase (se 3 (by rfl) ⟨663959, by rfl⟩ : syracuseStep 3541117 = 1327919) (by norm_num)
theorem B4721489 : Blo 2097435 4721489 := bstep (se 2 (by rfl) ⟨1770558, by rfl⟩ : syracuseStep 4721489 = 3541117) B3541117
theorem B3147659 : Blo 2097435 3147659 := bstep (se 1 (by rfl) ⟨2360744, by rfl⟩ : syracuseStep 3147659 = 4721489) B4721489
theorem B2098439 : Blo 2097435 2098439 := bstep (se 1 (by rfl) ⟨1573829, by rfl⟩ : syracuseStep 2098439 = 3147659) B3147659
theorem B2360749 : Blo 2097435 2360749 := bbase (se 3 (by rfl) ⟨442640, by rfl⟩ : syracuseStep 2360749 = 885281) (by norm_num)
theorem B3147665 : Blo 2097435 3147665 := bstep (se 2 (by rfl) ⟨1180374, by rfl⟩ : syracuseStep 3147665 = 2360749) B2360749
theorem B2098443 : Blo 2097435 2098443 := bstep (se 1 (by rfl) ⟨1573832, by rfl⟩ : syracuseStep 2098443 = 3147665) B3147665
theorem B7082261 : Blo 2097435 7082261 := bbase (se 6 (by rfl) ⟨165990, by rfl⟩ : syracuseStep 7082261 = 331981) (by norm_num)
theorem B4721507 : Blo 2097435 4721507 := bstep (se 1 (by rfl) ⟨3541130, by rfl⟩ : syracuseStep 4721507 = 7082261) B7082261
theorem B3147671 : Blo 2097435 3147671 := bstep (se 1 (by rfl) ⟨2360753, by rfl⟩ : syracuseStep 3147671 = 4721507) B4721507
theorem B2098447 : Blo 2097435 2098447 := bstep (se 1 (by rfl) ⟨1573835, by rfl⟩ : syracuseStep 2098447 = 3147671) B3147671
theorem B3147677 : Blo 2097435 3147677 := bbase (se 3 (by rfl) ⟨590189, by rfl⟩ : syracuseStep 3147677 = 1180379) (by norm_num)
theorem B2098451 : Blo 2097435 2098451 := bstep (se 1 (by rfl) ⟨1573838, by rfl⟩ : syracuseStep 2098451 = 3147677) B3147677
theorem B4721525 : Blo 2097435 4721525 := bbase (se 5 (by rfl) ⟨221321, by rfl⟩ : syracuseStep 4721525 = 442643) (by norm_num)
theorem B3147683 : Blo 2097435 3147683 := bstep (se 1 (by rfl) ⟨2360762, by rfl⟩ : syracuseStep 3147683 = 4721525) B4721525
theorem B2098455 : Blo 2097435 2098455 := bstep (se 1 (by rfl) ⟨1573841, by rfl⟩ : syracuseStep 2098455 = 3147683) B3147683
theorem B4038149 : Blo 2097435 4038149 := bbase (se 4 (by rfl) ⟨378576, by rfl⟩ : syracuseStep 4038149 = 757153) (by norm_num)
theorem B2692099 : Blo 2097435 2692099 := bstep (se 1 (by rfl) ⟨2019074, by rfl⟩ : syracuseStep 2692099 = 4038149) B4038149
theorem B3589465 : Blo 2097435 3589465 := bstep (se 2 (by rfl) ⟨1346049, by rfl⟩ : syracuseStep 3589465 = 2692099) B2692099
theorem B76575253 : Blo 2097435 76575253 := bstep (se 6 (by rfl) ⟨1794732, by rfl⟩ : syracuseStep 76575253 = 3589465) B3589465
theorem B102100337 : Blo 2097435 102100337 := bstep (se 2 (by rfl) ⟨38287626, by rfl⟩ : syracuseStep 102100337 = 76575253) B76575253
theorem B68066891 : Blo 2097435 68066891 := bstep (se 1 (by rfl) ⟨51050168, by rfl⟩ : syracuseStep 68066891 = 102100337) B102100337
theorem B45377927 : Blo 2097435 45377927 := bstep (se 1 (by rfl) ⟨34033445, by rfl⟩ : syracuseStep 45377927 = 68066891) B68066891
theorem B30251951 : Blo 2097435 30251951 := bstep (se 1 (by rfl) ⟨22688963, by rfl⟩ : syracuseStep 30251951 = 45377927) B45377927
theorem B20167967 : Blo 2097435 20167967 := bstep (se 1 (by rfl) ⟨15125975, by rfl⟩ : syracuseStep 20167967 = 30251951) B30251951
theorem B13445311 : Blo 2097435 13445311 := bstep (se 1 (by rfl) ⟨10083983, by rfl⟩ : syracuseStep 13445311 = 20167967) B20167967
theorem B17927081 : Blo 2097435 17927081 := bstep (se 2 (by rfl) ⟨6722655, by rfl⟩ : syracuseStep 17927081 = 13445311) B13445311
theorem B11951387 : Blo 2097435 11951387 := bstep (se 1 (by rfl) ⟨8963540, by rfl⟩ : syracuseStep 11951387 = 17927081) B17927081
theorem B7967591 : Blo 2097435 7967591 := bstep (se 1 (by rfl) ⟨5975693, by rfl⟩ : syracuseStep 7967591 = 11951387) B11951387
theorem B5311727 : Blo 2097435 5311727 := bstep (se 1 (by rfl) ⟨3983795, by rfl⟩ : syracuseStep 5311727 = 7967591) B7967591
theorem B3541151 : Blo 2097435 3541151 := bstep (se 1 (by rfl) ⟨2655863, by rfl⟩ : syracuseStep 3541151 = 5311727) B5311727
theorem B2360767 : Blo 2097435 2360767 := bstep (se 1 (by rfl) ⟨1770575, by rfl⟩ : syracuseStep 2360767 = 3541151) B3541151
theorem B3147689 : Blo 2097435 3147689 := bstep (se 2 (by rfl) ⟨1180383, by rfl⟩ : syracuseStep 3147689 = 2360767) B2360767
theorem B2098459 : Blo 2097435 2098459 := bstep (se 1 (by rfl) ⟨1573844, by rfl⟩ : syracuseStep 2098459 = 3147689) B3147689
theorem B7967605 : Blo 2097435 7967605 := bbase (se 5 (by rfl) ⟨373481, by rfl⟩ : syracuseStep 7967605 = 746963) (by norm_num)
theorem B10623473 : Blo 2097435 10623473 := bstep (se 2 (by rfl) ⟨3983802, by rfl⟩ : syracuseStep 10623473 = 7967605) B7967605
theorem B7082315 : Blo 2097435 7082315 := bstep (se 1 (by rfl) ⟨5311736, by rfl⟩ : syracuseStep 7082315 = 10623473) B10623473
theorem B4721543 : Blo 2097435 4721543 := bstep (se 1 (by rfl) ⟨3541157, by rfl⟩ : syracuseStep 4721543 = 7082315) B7082315
theorem B3147695 : Blo 2097435 3147695 := bstep (se 1 (by rfl) ⟨2360771, by rfl⟩ : syracuseStep 3147695 = 4721543) B4721543
theorem B2098463 : Blo 2097435 2098463 := bstep (se 1 (by rfl) ⟨1573847, by rfl⟩ : syracuseStep 2098463 = 3147695) B3147695
theorem B3147701 : Blo 2097435 3147701 := bbase (se 5 (by rfl) ⟨147548, by rfl⟩ : syracuseStep 3147701 = 295097) (by norm_num)
theorem B2098467 : Blo 2097435 2098467 := bstep (se 1 (by rfl) ⟨1573850, by rfl⟩ : syracuseStep 2098467 = 3147701) B3147701
theorem B5311757 : Blo 2097435 5311757 := bbase (se 3 (by rfl) ⟨995954, by rfl⟩ : syracuseStep 5311757 = 1991909) (by norm_num)
theorem B3541171 : Blo 2097435 3541171 := bstep (se 1 (by rfl) ⟨2655878, by rfl⟩ : syracuseStep 3541171 = 5311757) B5311757
theorem B4721561 : Blo 2097435 4721561 := bstep (se 2 (by rfl) ⟨1770585, by rfl⟩ : syracuseStep 4721561 = 3541171) B3541171
theorem B3147707 : Blo 2097435 3147707 := bstep (se 1 (by rfl) ⟨2360780, by rfl⟩ : syracuseStep 3147707 = 4721561) B4721561
theorem B2098471 : Blo 2097435 2098471 := bstep (se 1 (by rfl) ⟨1573853, by rfl⟩ : syracuseStep 2098471 = 3147707) B3147707
theorem B2360785 : Blo 2097435 2360785 := bbase (se 2 (by rfl) ⟨885294, by rfl⟩ : syracuseStep 2360785 = 1770589) (by norm_num)
theorem B3147713 : Blo 2097435 3147713 := bstep (se 2 (by rfl) ⟨1180392, by rfl⟩ : syracuseStep 3147713 = 2360785) B2360785
theorem B2098475 : Blo 2097435 2098475 := bstep (se 1 (by rfl) ⟨1573856, by rfl⟩ : syracuseStep 2098475 = 3147713) B3147713
theorem B4481813 : Blo 2097435 4481813 := bbase (se 6 (by rfl) ⟨105042, by rfl⟩ : syracuseStep 4481813 = 210085) (by norm_num)
theorem B2987875 : Blo 2097435 2987875 := bstep (se 1 (by rfl) ⟨2240906, by rfl⟩ : syracuseStep 2987875 = 4481813) B4481813
theorem B3983833 : Blo 2097435 3983833 := bstep (se 2 (by rfl) ⟨1493937, by rfl⟩ : syracuseStep 3983833 = 2987875) B2987875
theorem B5311777 : Blo 2097435 5311777 := bstep (se 2 (by rfl) ⟨1991916, by rfl⟩ : syracuseStep 5311777 = 3983833) B3983833
theorem B7082369 : Blo 2097435 7082369 := bstep (se 2 (by rfl) ⟨2655888, by rfl⟩ : syracuseStep 7082369 = 5311777) B5311777
theorem B4721579 : Blo 2097435 4721579 := bstep (se 1 (by rfl) ⟨3541184, by rfl⟩ : syracuseStep 4721579 = 7082369) B7082369
theorem B3147719 : Blo 2097435 3147719 := bstep (se 1 (by rfl) ⟨2360789, by rfl⟩ : syracuseStep 3147719 = 4721579) B4721579
theorem B2098479 : Blo 2097435 2098479 := bstep (se 1 (by rfl) ⟨1573859, by rfl⟩ : syracuseStep 2098479 = 3147719) B3147719
theorem B3147725 : Blo 2097435 3147725 := bbase (se 3 (by rfl) ⟨590198, by rfl⟩ : syracuseStep 3147725 = 1180397) (by norm_num)
theorem B2098483 : Blo 2097435 2098483 := bstep (se 1 (by rfl) ⟨1573862, by rfl⟩ : syracuseStep 2098483 = 3147725) B3147725
theorem B4721597 : Blo 2097435 4721597 := bbase (se 3 (by rfl) ⟨885299, by rfl⟩ : syracuseStep 4721597 = 1770599) (by norm_num)
theorem B3147731 : Blo 2097435 3147731 := bstep (se 1 (by rfl) ⟨2360798, by rfl⟩ : syracuseStep 3147731 = 4721597) B4721597
theorem B2098487 : Blo 2097435 2098487 := bstep (se 1 (by rfl) ⟨1573865, by rfl⟩ : syracuseStep 2098487 = 3147731) B3147731
theorem B3541205 : Blo 2097435 3541205 := bbase (se 7 (by rfl) ⟨41498, by rfl⟩ : syracuseStep 3541205 = 82997) (by norm_num)
theorem B2360803 : Blo 2097435 2360803 := bstep (se 1 (by rfl) ⟨1770602, by rfl⟩ : syracuseStep 2360803 = 3541205) B3541205
theorem B3147737 : Blo 2097435 3147737 := bstep (se 2 (by rfl) ⟨1180401, by rfl⟩ : syracuseStep 3147737 = 2360803) B2360803
theorem B2098491 : Blo 2097435 2098491 := bstep (se 1 (by rfl) ⟨1573868, by rfl⟩ : syracuseStep 2098491 = 3147737) B3147737
theorem B4786037 : Blo 2097435 4786037 := bbase (se 5 (by rfl) ⟨224345, by rfl⟩ : syracuseStep 4786037 = 448691) (by norm_num)
theorem B3190691 : Blo 2097435 3190691 := bstep (se 1 (by rfl) ⟨2393018, by rfl⟩ : syracuseStep 3190691 = 4786037) B4786037
theorem B8508509 : Blo 2097435 8508509 := bstep (se 3 (by rfl) ⟨1595345, by rfl⟩ : syracuseStep 8508509 = 3190691) B3190691
theorem B5672339 : Blo 2097435 5672339 := bstep (se 1 (by rfl) ⟨4254254, by rfl⟩ : syracuseStep 5672339 = 8508509) B8508509
theorem B3781559 : Blo 2097435 3781559 := bstep (se 1 (by rfl) ⟨2836169, by rfl⟩ : syracuseStep 3781559 = 5672339) B5672339
theorem B2521039 : Blo 2097435 2521039 := bstep (se 1 (by rfl) ⟨1890779, by rfl⟩ : syracuseStep 2521039 = 3781559) B3781559
theorem B3361385 : Blo 2097435 3361385 := bstep (se 2 (by rfl) ⟨1260519, by rfl⟩ : syracuseStep 3361385 = 2521039) B2521039
theorem B8963693 : Blo 2097435 8963693 := bstep (se 3 (by rfl) ⟨1680692, by rfl⟩ : syracuseStep 8963693 = 3361385) B3361385
theorem B5975795 : Blo 2097435 5975795 := bstep (se 1 (by rfl) ⟨4481846, by rfl⟩ : syracuseStep 5975795 = 8963693) B8963693
theorem B15935453 : Blo 2097435 15935453 := bstep (se 3 (by rfl) ⟨2987897, by rfl⟩ : syracuseStep 15935453 = 5975795) B5975795
theorem B10623635 : Blo 2097435 10623635 := bstep (se 1 (by rfl) ⟨7967726, by rfl⟩ : syracuseStep 10623635 = 15935453) B15935453
theorem B7082423 : Blo 2097435 7082423 := bstep (se 1 (by rfl) ⟨5311817, by rfl⟩ : syracuseStep 7082423 = 10623635) B10623635
theorem B4721615 : Blo 2097435 4721615 := bstep (se 1 (by rfl) ⟨3541211, by rfl⟩ : syracuseStep 4721615 = 7082423) B7082423
theorem B3147743 : Blo 2097435 3147743 := bstep (se 1 (by rfl) ⟨2360807, by rfl⟩ : syracuseStep 3147743 = 4721615) B4721615
theorem B2098495 : Blo 2097435 2098495 := bstep (se 1 (by rfl) ⟨1573871, by rfl⟩ : syracuseStep 2098495 = 3147743) B3147743
theorem B3147749 : Blo 2097435 3147749 := bbase (se 4 (by rfl) ⟨295101, by rfl⟩ : syracuseStep 3147749 = 590203) (by norm_num)
theorem B2098499 : Blo 2097435 2098499 := bstep (se 1 (by rfl) ⟨1573874, by rfl⟩ : syracuseStep 2098499 = 3147749) B3147749
theorem B2521049 : Blo 2097435 2521049 := bbase (se 2 (by rfl) ⟨945393, by rfl⟩ : syracuseStep 2521049 = 1890787) (by norm_num)
theorem B6722797 : Blo 2097435 6722797 := bstep (se 3 (by rfl) ⟨1260524, by rfl⟩ : syracuseStep 6722797 = 2521049) B2521049
theorem B8963729 : Blo 2097435 8963729 := bstep (se 2 (by rfl) ⟨3361398, by rfl⟩ : syracuseStep 8963729 = 6722797) B6722797
theorem B5975819 : Blo 2097435 5975819 := bstep (se 1 (by rfl) ⟨4481864, by rfl⟩ : syracuseStep 5975819 = 8963729) B8963729
theorem B3983879 : Blo 2097435 3983879 := bstep (se 1 (by rfl) ⟨2987909, by rfl⟩ : syracuseStep 3983879 = 5975819) B5975819
theorem B2655919 : Blo 2097435 2655919 := bstep (se 1 (by rfl) ⟨1991939, by rfl⟩ : syracuseStep 2655919 = 3983879) B3983879
theorem B3541225 : Blo 2097435 3541225 := bstep (se 2 (by rfl) ⟨1327959, by rfl⟩ : syracuseStep 3541225 = 2655919) B2655919
theorem B4721633 : Blo 2097435 4721633 := bstep (se 2 (by rfl) ⟨1770612, by rfl⟩ : syracuseStep 4721633 = 3541225) B3541225
theorem B3147755 : Blo 2097435 3147755 := bstep (se 1 (by rfl) ⟨2360816, by rfl⟩ : syracuseStep 3147755 = 4721633) B4721633
theorem B2098503 : Blo 2097435 2098503 := bstep (se 1 (by rfl) ⟨1573877, by rfl⟩ : syracuseStep 2098503 = 3147755) B3147755
theorem B2360821 : Blo 2097435 2360821 := bbase (se 5 (by rfl) ⟨110663, by rfl⟩ : syracuseStep 2360821 = 221327) (by norm_num)
theorem B3147761 : Blo 2097435 3147761 := bstep (se 2 (by rfl) ⟨1180410, by rfl⟩ : syracuseStep 3147761 = 2360821) B2360821
theorem B2098507 : Blo 2097435 2098507 := bstep (se 1 (by rfl) ⟨1573880, by rfl⟩ : syracuseStep 2098507 = 3147761) B3147761
theorem B2655929 : Blo 2097435 2655929 := bbase (se 2 (by rfl) ⟨995973, by rfl⟩ : syracuseStep 2655929 = 1991947) (by norm_num)
theorem B7082477 : Blo 2097435 7082477 := bstep (se 3 (by rfl) ⟨1327964, by rfl⟩ : syracuseStep 7082477 = 2655929) B2655929
theorem B4721651 : Blo 2097435 4721651 := bstep (se 1 (by rfl) ⟨3541238, by rfl⟩ : syracuseStep 4721651 = 7082477) B7082477
theorem B3147767 : Blo 2097435 3147767 := bstep (se 1 (by rfl) ⟨2360825, by rfl⟩ : syracuseStep 3147767 = 4721651) B4721651
theorem B2098511 : Blo 2097435 2098511 := bstep (se 1 (by rfl) ⟨1573883, by rfl⟩ : syracuseStep 2098511 = 3147767) B3147767
theorem B3147773 : Blo 2097435 3147773 := bbase (se 3 (by rfl) ⟨590207, by rfl⟩ : syracuseStep 3147773 = 1180415) (by norm_num)
theorem B2098515 : Blo 2097435 2098515 := bstep (se 1 (by rfl) ⟨1573886, by rfl⟩ : syracuseStep 2098515 = 3147773) B3147773
theorem B4721669 : Blo 2097435 4721669 := bbase (se 4 (by rfl) ⟨442656, by rfl⟩ : syracuseStep 4721669 = 885313) (by norm_num)
theorem B3147779 : Blo 2097435 3147779 := bstep (se 1 (by rfl) ⟨2360834, by rfl⟩ : syracuseStep 3147779 = 4721669) B4721669
theorem B2098519 : Blo 2097435 2098519 := bstep (se 1 (by rfl) ⟨1573889, by rfl⟩ : syracuseStep 2098519 = 3147779) B3147779
theorem B3983917 : Blo 2097435 3983917 := bbase (se 3 (by rfl) ⟨746984, by rfl⟩ : syracuseStep 3983917 = 1493969) (by norm_num)
theorem B5311889 : Blo 2097435 5311889 := bstep (se 2 (by rfl) ⟨1991958, by rfl⟩ : syracuseStep 5311889 = 3983917) B3983917
theorem B3541259 : Blo 2097435 3541259 := bstep (se 1 (by rfl) ⟨2655944, by rfl⟩ : syracuseStep 3541259 = 5311889) B5311889
theorem B2360839 : Blo 2097435 2360839 := bstep (se 1 (by rfl) ⟨1770629, by rfl⟩ : syracuseStep 2360839 = 3541259) B3541259
theorem B3147785 : Blo 2097435 3147785 := bstep (se 2 (by rfl) ⟨1180419, by rfl⟩ : syracuseStep 3147785 = 2360839) B2360839
theorem B2098523 : Blo 2097435 2098523 := bstep (se 1 (by rfl) ⟨1573892, by rfl⟩ : syracuseStep 2098523 = 3147785) B3147785
theorem B10623797 : Blo 2097435 10623797 := bbase (se 5 (by rfl) ⟨497990, by rfl⟩ : syracuseStep 10623797 = 995981) (by norm_num)
theorem B7082531 : Blo 2097435 7082531 := bstep (se 1 (by rfl) ⟨5311898, by rfl⟩ : syracuseStep 7082531 = 10623797) B10623797
theorem B4721687 : Blo 2097435 4721687 := bstep (se 1 (by rfl) ⟨3541265, by rfl⟩ : syracuseStep 4721687 = 7082531) B7082531
theorem B3147791 : Blo 2097435 3147791 := bstep (se 1 (by rfl) ⟨2360843, by rfl⟩ : syracuseStep 3147791 = 4721687) B4721687
theorem B2098527 : Blo 2097435 2098527 := bstep (se 1 (by rfl) ⟨1573895, by rfl⟩ : syracuseStep 2098527 = 3147791) B3147791
theorem B3147797 : Blo 2097435 3147797 := bbase (se 6 (by rfl) ⟨73776, by rfl⟩ : syracuseStep 3147797 = 147553) (by norm_num)
theorem B2098531 : Blo 2097435 2098531 := bstep (se 1 (by rfl) ⟨1573898, by rfl⟩ : syracuseStep 2098531 = 3147797) B3147797
theorem B38811413 : Blo 2097435 38811413 := bbase (se 6 (by rfl) ⟨909642, by rfl⟩ : syracuseStep 38811413 = 1819285) (by norm_num)
theorem B103497101 : Blo 2097435 103497101 := bstep (se 3 (by rfl) ⟨19405706, by rfl⟩ : syracuseStep 103497101 = 38811413) B38811413
theorem B68998067 : Blo 2097435 68998067 := bstep (se 1 (by rfl) ⟨51748550, by rfl⟩ : syracuseStep 68998067 = 103497101) B103497101
theorem B45998711 : Blo 2097435 45998711 := bstep (se 1 (by rfl) ⟨34499033, by rfl⟩ : syracuseStep 45998711 = 68998067) B68998067
theorem B30665807 : Blo 2097435 30665807 := bstep (se 1 (by rfl) ⟨22999355, by rfl⟩ : syracuseStep 30665807 = 45998711) B45998711
theorem B20443871 : Blo 2097435 20443871 := bstep (se 1 (by rfl) ⟨15332903, by rfl⟩ : syracuseStep 20443871 = 30665807) B30665807
theorem B54516989 : Blo 2097435 54516989 := bstep (se 3 (by rfl) ⟨10221935, by rfl⟩ : syracuseStep 54516989 = 20443871) B20443871
theorem B145378637 : Blo 2097435 145378637 := bstep (se 3 (by rfl) ⟨27258494, by rfl⟩ : syracuseStep 145378637 = 54516989) B54516989
theorem B96919091 : Blo 2097435 96919091 := bstep (se 1 (by rfl) ⟨72689318, by rfl⟩ : syracuseStep 96919091 = 145378637) B145378637
theorem B64612727 : Blo 2097435 64612727 := bstep (se 1 (by rfl) ⟨48459545, by rfl⟩ : syracuseStep 64612727 = 96919091) B96919091
theorem B43075151 : Blo 2097435 43075151 := bstep (se 1 (by rfl) ⟨32306363, by rfl⟩ : syracuseStep 43075151 = 64612727) B64612727
theorem B28716767 : Blo 2097435 28716767 := bstep (se 1 (by rfl) ⟨21537575, by rfl⟩ : syracuseStep 28716767 = 43075151) B43075151
theorem B19144511 : Blo 2097435 19144511 := bstep (se 1 (by rfl) ⟨14358383, by rfl⟩ : syracuseStep 19144511 = 28716767) B28716767
theorem B12763007 : Blo 2097435 12763007 := bstep (se 1 (by rfl) ⟨9572255, by rfl⟩ : syracuseStep 12763007 = 19144511) B19144511
theorem B8508671 : Blo 2097435 8508671 := bstep (se 1 (by rfl) ⟨6381503, by rfl⟩ : syracuseStep 8508671 = 12763007) B12763007
theorem B5672447 : Blo 2097435 5672447 := bstep (se 1 (by rfl) ⟨4254335, by rfl⟩ : syracuseStep 5672447 = 8508671) B8508671
theorem B3781631 : Blo 2097435 3781631 := bstep (se 1 (by rfl) ⟨2836223, by rfl⟩ : syracuseStep 3781631 = 5672447) B5672447
theorem B2521087 : Blo 2097435 2521087 := bstep (se 1 (by rfl) ⟨1890815, by rfl⟩ : syracuseStep 2521087 = 3781631) B3781631
theorem B13445797 : Blo 2097435 13445797 := bstep (se 4 (by rfl) ⟨1260543, by rfl⟩ : syracuseStep 13445797 = 2521087) B2521087
theorem B17927729 : Blo 2097435 17927729 := bstep (se 2 (by rfl) ⟨6722898, by rfl⟩ : syracuseStep 17927729 = 13445797) B13445797
theorem B11951819 : Blo 2097435 11951819 := bstep (se 1 (by rfl) ⟨8963864, by rfl⟩ : syracuseStep 11951819 = 17927729) B17927729
theorem B7967879 : Blo 2097435 7967879 := bstep (se 1 (by rfl) ⟨5975909, by rfl⟩ : syracuseStep 7967879 = 11951819) B11951819
theorem B5311919 : Blo 2097435 5311919 := bstep (se 1 (by rfl) ⟨3983939, by rfl⟩ : syracuseStep 5311919 = 7967879) B7967879
theorem B3541279 : Blo 2097435 3541279 := bstep (se 1 (by rfl) ⟨2655959, by rfl⟩ : syracuseStep 3541279 = 5311919) B5311919
theorem B4721705 : Blo 2097435 4721705 := bstep (se 2 (by rfl) ⟨1770639, by rfl⟩ : syracuseStep 4721705 = 3541279) B3541279
theorem B3147803 : Blo 2097435 3147803 := bstep (se 1 (by rfl) ⟨2360852, by rfl⟩ : syracuseStep 3147803 = 4721705) B4721705
theorem B2098535 : Blo 2097435 2098535 := bstep (se 1 (by rfl) ⟨1573901, by rfl⟩ : syracuseStep 2098535 = 3147803) B3147803
theorem B2360857 : Blo 2097435 2360857 := bbase (se 2 (by rfl) ⟨885321, by rfl⟩ : syracuseStep 2360857 = 1770643) (by norm_num)
theorem B3147809 : Blo 2097435 3147809 := bstep (se 2 (by rfl) ⟨1180428, by rfl⟩ : syracuseStep 3147809 = 2360857) B2360857
theorem B2098539 : Blo 2097435 2098539 := bstep (se 1 (by rfl) ⟨1573904, by rfl⟩ : syracuseStep 2098539 = 3147809) B3147809
theorem B7967909 : Blo 2097435 7967909 := bbase (se 4 (by rfl) ⟨746991, by rfl⟩ : syracuseStep 7967909 = 1493983) (by norm_num)
theorem B5311939 : Blo 2097435 5311939 := bstep (se 1 (by rfl) ⟨3983954, by rfl⟩ : syracuseStep 5311939 = 7967909) B7967909
theorem B7082585 : Blo 2097435 7082585 := bstep (se 2 (by rfl) ⟨2655969, by rfl⟩ : syracuseStep 7082585 = 5311939) B5311939
theorem B4721723 : Blo 2097435 4721723 := bstep (se 1 (by rfl) ⟨3541292, by rfl⟩ : syracuseStep 4721723 = 7082585) B7082585
theorem B3147815 : Blo 2097435 3147815 := bstep (se 1 (by rfl) ⟨2360861, by rfl⟩ : syracuseStep 3147815 = 4721723) B4721723
theorem B2098543 : Blo 2097435 2098543 := bstep (se 1 (by rfl) ⟨1573907, by rfl⟩ : syracuseStep 2098543 = 3147815) B3147815
theorem B3147821 : Blo 2097435 3147821 := bbase (se 3 (by rfl) ⟨590216, by rfl⟩ : syracuseStep 3147821 = 1180433) (by norm_num)
theorem B2098547 : Blo 2097435 2098547 := bstep (se 1 (by rfl) ⟨1573910, by rfl⟩ : syracuseStep 2098547 = 3147821) B3147821
theorem B4721741 : Blo 2097435 4721741 := bbase (se 3 (by rfl) ⟨885326, by rfl⟩ : syracuseStep 4721741 = 1770653) (by norm_num)
theorem B3147827 : Blo 2097435 3147827 := bstep (se 1 (by rfl) ⟨2360870, by rfl⟩ : syracuseStep 3147827 = 4721741) B4721741
theorem B2098551 : Blo 2097435 2098551 := bstep (se 1 (by rfl) ⟨1573913, by rfl⟩ : syracuseStep 2098551 = 3147827) B3147827
theorem B2655985 : Blo 2097435 2655985 := bbase (se 2 (by rfl) ⟨995994, by rfl⟩ : syracuseStep 2655985 = 1991989) (by norm_num)
theorem B3541313 : Blo 2097435 3541313 := bstep (se 2 (by rfl) ⟨1327992, by rfl⟩ : syracuseStep 3541313 = 2655985) B2655985
theorem B2360875 : Blo 2097435 2360875 := bstep (se 1 (by rfl) ⟨1770656, by rfl⟩ : syracuseStep 2360875 = 3541313) B3541313
theorem B3147833 : Blo 2097435 3147833 := bstep (se 2 (by rfl) ⟨1180437, by rfl⟩ : syracuseStep 3147833 = 2360875) B2360875
theorem B2098555 : Blo 2097435 2098555 := bstep (se 1 (by rfl) ⟨1573916, by rfl⟩ : syracuseStep 2098555 = 3147833) B3147833
theorem B7277221 : Blo 2097435 7277221 := bbase (se 4 (by rfl) ⟨682239, by rfl⟩ : syracuseStep 7277221 = 1364479) (by norm_num)
theorem B38811845 : Blo 2097435 38811845 := bstep (se 4 (by rfl) ⟨3638610, by rfl⟩ : syracuseStep 38811845 = 7277221) B7277221
theorem B25874563 : Blo 2097435 25874563 := bstep (se 1 (by rfl) ⟨19405922, by rfl⟩ : syracuseStep 25874563 = 38811845) B38811845
theorem B34499417 : Blo 2097435 34499417 := bstep (se 2 (by rfl) ⟨12937281, by rfl⟩ : syracuseStep 34499417 = 25874563) B25874563
theorem B91998445 : Blo 2097435 91998445 := bstep (se 3 (by rfl) ⟨17249708, by rfl⟩ : syracuseStep 91998445 = 34499417) B34499417
theorem B122664593 : Blo 2097435 122664593 := bstep (se 2 (by rfl) ⟨45999222, by rfl⟩ : syracuseStep 122664593 = 91998445) B91998445
theorem B81776395 : Blo 2097435 81776395 := bstep (se 1 (by rfl) ⟨61332296, by rfl⟩ : syracuseStep 81776395 = 122664593) B122664593
theorem B109035193 : Blo 2097435 109035193 := bstep (se 2 (by rfl) ⟨40888197, by rfl⟩ : syracuseStep 109035193 = 81776395) B81776395
theorem B145380257 : Blo 2097435 145380257 := bstep (se 2 (by rfl) ⟨54517596, by rfl⟩ : syracuseStep 145380257 = 109035193) B109035193
theorem B96920171 : Blo 2097435 96920171 := bstep (se 1 (by rfl) ⟨72690128, by rfl⟩ : syracuseStep 96920171 = 145380257) B145380257
theorem B64613447 : Blo 2097435 64613447 := bstep (se 1 (by rfl) ⟨48460085, by rfl⟩ : syracuseStep 64613447 = 96920171) B96920171
theorem B43075631 : Blo 2097435 43075631 := bstep (se 1 (by rfl) ⟨32306723, by rfl⟩ : syracuseStep 43075631 = 64613447) B64613447
theorem B28717087 : Blo 2097435 28717087 := bstep (se 1 (by rfl) ⟨21537815, by rfl⟩ : syracuseStep 28717087 = 43075631) B43075631
theorem B38289449 : Blo 2097435 38289449 := bstep (se 2 (by rfl) ⟨14358543, by rfl⟩ : syracuseStep 38289449 = 28717087) B28717087
theorem B25526299 : Blo 2097435 25526299 := bstep (se 1 (by rfl) ⟨19144724, by rfl⟩ : syracuseStep 25526299 = 38289449) B38289449
theorem B34035065 : Blo 2097435 34035065 := bstep (se 2 (by rfl) ⟨12763149, by rfl⟩ : syracuseStep 34035065 = 25526299) B25526299
theorem B22690043 : Blo 2097435 22690043 := bstep (se 1 (by rfl) ⟨17017532, by rfl⟩ : syracuseStep 22690043 = 34035065) B34035065
theorem B15126695 : Blo 2097435 15126695 := bstep (se 1 (by rfl) ⟨11345021, by rfl⟩ : syracuseStep 15126695 = 22690043) B22690043
theorem B10084463 : Blo 2097435 10084463 := bstep (se 1 (by rfl) ⟨7563347, by rfl⟩ : syracuseStep 10084463 = 15126695) B15126695
theorem B6722975 : Blo 2097435 6722975 := bstep (se 1 (by rfl) ⟨5042231, by rfl⟩ : syracuseStep 6722975 = 10084463) B10084463
theorem B4481983 : Blo 2097435 4481983 := bstep (se 1 (by rfl) ⟨3361487, by rfl⟩ : syracuseStep 4481983 = 6722975) B6722975
theorem B23903909 : Blo 2097435 23903909 := bstep (se 4 (by rfl) ⟨2240991, by rfl⟩ : syracuseStep 23903909 = 4481983) B4481983
theorem B15935939 : Blo 2097435 15935939 := bstep (se 1 (by rfl) ⟨11951954, by rfl⟩ : syracuseStep 15935939 = 23903909) B23903909
theorem B10623959 : Blo 2097435 10623959 := bstep (se 1 (by rfl) ⟨7967969, by rfl⟩ : syracuseStep 10623959 = 15935939) B15935939
theorem B7082639 : Blo 2097435 7082639 := bstep (se 1 (by rfl) ⟨5311979, by rfl⟩ : syracuseStep 7082639 = 10623959) B10623959
theorem B4721759 : Blo 2097435 4721759 := bstep (se 1 (by rfl) ⟨3541319, by rfl⟩ : syracuseStep 4721759 = 7082639) B7082639
theorem B3147839 : Blo 2097435 3147839 := bstep (se 1 (by rfl) ⟨2360879, by rfl⟩ : syracuseStep 3147839 = 4721759) B4721759
theorem B2098559 : Blo 2097435 2098559 := bstep (se 1 (by rfl) ⟨1573919, by rfl⟩ : syracuseStep 2098559 = 3147839) B3147839
theorem B3147845 : Blo 2097435 3147845 := bbase (se 4 (by rfl) ⟨295110, by rfl⟩ : syracuseStep 3147845 = 590221) (by norm_num)
theorem B2098563 : Blo 2097435 2098563 := bstep (se 1 (by rfl) ⟨1573922, by rfl⟩ : syracuseStep 2098563 = 3147845) B3147845
theorem B3541333 : Blo 2097435 3541333 := bbase (se 10 (by rfl) ⟨5187, by rfl⟩ : syracuseStep 3541333 = 10375) (by norm_num)
theorem B4721777 : Blo 2097435 4721777 := bstep (se 2 (by rfl) ⟨1770666, by rfl⟩ : syracuseStep 4721777 = 3541333) B3541333
theorem B3147851 : Blo 2097435 3147851 := bstep (se 1 (by rfl) ⟨2360888, by rfl⟩ : syracuseStep 3147851 = 4721777) B4721777
theorem B2098567 : Blo 2097435 2098567 := bstep (se 1 (by rfl) ⟨1573925, by rfl⟩ : syracuseStep 2098567 = 3147851) B3147851
theorem B2360893 : Blo 2097435 2360893 := bbase (se 3 (by rfl) ⟨442667, by rfl⟩ : syracuseStep 2360893 = 885335) (by norm_num)
theorem B3147857 : Blo 2097435 3147857 := bstep (se 2 (by rfl) ⟨1180446, by rfl⟩ : syracuseStep 3147857 = 2360893) B2360893
theorem B2098571 : Blo 2097435 2098571 := bstep (se 1 (by rfl) ⟨1573928, by rfl⟩ : syracuseStep 2098571 = 3147857) B3147857
theorem B7082693 : Blo 2097435 7082693 := bbase (se 4 (by rfl) ⟨664002, by rfl⟩ : syracuseStep 7082693 = 1328005) (by norm_num)
theorem B4721795 : Blo 2097435 4721795 := bstep (se 1 (by rfl) ⟨3541346, by rfl⟩ : syracuseStep 4721795 = 7082693) B7082693
theorem B3147863 : Blo 2097435 3147863 := bstep (se 1 (by rfl) ⟨2360897, by rfl⟩ : syracuseStep 3147863 = 4721795) B4721795
theorem B2098575 : Blo 2097435 2098575 := bstep (se 1 (by rfl) ⟨1573931, by rfl⟩ : syracuseStep 2098575 = 3147863) B3147863
theorem B3147869 : Blo 2097435 3147869 := bbase (se 3 (by rfl) ⟨590225, by rfl⟩ : syracuseStep 3147869 = 1180451) (by norm_num)
theorem B2098579 : Blo 2097435 2098579 := bstep (se 1 (by rfl) ⟨1573934, by rfl⟩ : syracuseStep 2098579 = 3147869) B3147869
theorem B4721813 : Blo 2097435 4721813 := bbase (se 6 (by rfl) ⟨110667, by rfl⟩ : syracuseStep 4721813 = 221335) (by norm_num)
theorem B3147875 : Blo 2097435 3147875 := bstep (se 1 (by rfl) ⟨2360906, by rfl⟩ : syracuseStep 3147875 = 4721813) B4721813
theorem B2098583 : Blo 2097435 2098583 := bstep (se 1 (by rfl) ⟨1573937, by rfl⟩ : syracuseStep 2098583 = 3147875) B3147875
theorem B2988029 : Blo 2097435 2988029 := bbase (se 3 (by rfl) ⟨560255, by rfl⟩ : syracuseStep 2988029 = 1120511) (by norm_num)
theorem B7968077 : Blo 2097435 7968077 := bstep (se 3 (by rfl) ⟨1494014, by rfl⟩ : syracuseStep 7968077 = 2988029) B2988029
theorem B5312051 : Blo 2097435 5312051 := bstep (se 1 (by rfl) ⟨3984038, by rfl⟩ : syracuseStep 5312051 = 7968077) B7968077
theorem B3541367 : Blo 2097435 3541367 := bstep (se 1 (by rfl) ⟨2656025, by rfl⟩ : syracuseStep 3541367 = 5312051) B5312051
theorem B2360911 : Blo 2097435 2360911 := bstep (se 1 (by rfl) ⟨1770683, by rfl⟩ : syracuseStep 2360911 = 3541367) B3541367
theorem B3147881 : Blo 2097435 3147881 := bstep (se 2 (by rfl) ⟨1180455, by rfl⟩ : syracuseStep 3147881 = 2360911) B2360911
theorem B2098587 : Blo 2097435 2098587 := bstep (se 1 (by rfl) ⟨1573940, by rfl⟩ : syracuseStep 2098587 = 3147881) B3147881
theorem B5672597 : Blo 2097435 5672597 := bbase (se 6 (by rfl) ⟨132951, by rfl⟩ : syracuseStep 5672597 = 265903) (by norm_num)
theorem B15126925 : Blo 2097435 15126925 := bstep (se 3 (by rfl) ⟨2836298, by rfl⟩ : syracuseStep 15126925 = 5672597) B5672597
theorem B20169233 : Blo 2097435 20169233 := bstep (se 2 (by rfl) ⟨7563462, by rfl⟩ : syracuseStep 20169233 = 15126925) B15126925
theorem B13446155 : Blo 2097435 13446155 := bstep (se 1 (by rfl) ⟨10084616, by rfl⟩ : syracuseStep 13446155 = 20169233) B20169233
theorem B8964103 : Blo 2097435 8964103 := bstep (se 1 (by rfl) ⟨6723077, by rfl⟩ : syracuseStep 8964103 = 13446155) B13446155
theorem B11952137 : Blo 2097435 11952137 := bstep (se 2 (by rfl) ⟨4482051, by rfl⟩ : syracuseStep 11952137 = 8964103) B8964103
theorem B7968091 : Blo 2097435 7968091 := bstep (se 1 (by rfl) ⟨5976068, by rfl⟩ : syracuseStep 7968091 = 11952137) B11952137
theorem B10624121 : Blo 2097435 10624121 := bstep (se 2 (by rfl) ⟨3984045, by rfl⟩ : syracuseStep 10624121 = 7968091) B7968091
theorem B7082747 : Blo 2097435 7082747 := bstep (se 1 (by rfl) ⟨5312060, by rfl⟩ : syracuseStep 7082747 = 10624121) B10624121
theorem B4721831 : Blo 2097435 4721831 := bstep (se 1 (by rfl) ⟨3541373, by rfl⟩ : syracuseStep 4721831 = 7082747) B7082747
theorem B3147887 : Blo 2097435 3147887 := bstep (se 1 (by rfl) ⟨2360915, by rfl⟩ : syracuseStep 3147887 = 4721831) B4721831
theorem B2098591 : Blo 2097435 2098591 := bstep (se 1 (by rfl) ⟨1573943, by rfl⟩ : syracuseStep 2098591 = 3147887) B3147887
theorem B3147893 : Blo 2097435 3147893 := bbase (se 5 (by rfl) ⟨147557, by rfl⟩ : syracuseStep 3147893 = 295115) (by norm_num)
theorem B2098595 : Blo 2097435 2098595 := bstep (se 1 (by rfl) ⟨1573946, by rfl⟩ : syracuseStep 2098595 = 3147893) B3147893
theorem B3984061 : Blo 2097435 3984061 := bbase (se 3 (by rfl) ⟨747011, by rfl⟩ : syracuseStep 3984061 = 1494023) (by norm_num)
theorem B5312081 : Blo 2097435 5312081 := bstep (se 2 (by rfl) ⟨1992030, by rfl⟩ : syracuseStep 5312081 = 3984061) B3984061
theorem B3541387 : Blo 2097435 3541387 := bstep (se 1 (by rfl) ⟨2656040, by rfl⟩ : syracuseStep 3541387 = 5312081) B5312081
theorem B4721849 : Blo 2097435 4721849 := bstep (se 2 (by rfl) ⟨1770693, by rfl⟩ : syracuseStep 4721849 = 3541387) B3541387
theorem B3147899 : Blo 2097435 3147899 := bstep (se 1 (by rfl) ⟨2360924, by rfl⟩ : syracuseStep 3147899 = 4721849) B4721849
theorem B2098599 : Blo 2097435 2098599 := bstep (se 1 (by rfl) ⟨1573949, by rfl⟩ : syracuseStep 2098599 = 3147899) B3147899
theorem B2360929 : Blo 2097435 2360929 := bbase (se 2 (by rfl) ⟨885348, by rfl⟩ : syracuseStep 2360929 = 1770697) (by norm_num)
theorem B3147905 : Blo 2097435 3147905 := bstep (se 2 (by rfl) ⟨1180464, by rfl⟩ : syracuseStep 3147905 = 2360929) B2360929
theorem B2098603 : Blo 2097435 2098603 := bstep (se 1 (by rfl) ⟨1573952, by rfl⟩ : syracuseStep 2098603 = 3147905) B3147905
theorem B5312101 : Blo 2097435 5312101 := bbase (se 4 (by rfl) ⟨498009, by rfl⟩ : syracuseStep 5312101 = 996019) (by norm_num)
theorem B7082801 : Blo 2097435 7082801 := bstep (se 2 (by rfl) ⟨2656050, by rfl⟩ : syracuseStep 7082801 = 5312101) B5312101
theorem B4721867 : Blo 2097435 4721867 := bstep (se 1 (by rfl) ⟨3541400, by rfl⟩ : syracuseStep 4721867 = 7082801) B7082801
theorem B3147911 : Blo 2097435 3147911 := bstep (se 1 (by rfl) ⟨2360933, by rfl⟩ : syracuseStep 3147911 = 4721867) B4721867
theorem B2098607 : Blo 2097435 2098607 := bstep (se 1 (by rfl) ⟨1573955, by rfl⟩ : syracuseStep 2098607 = 3147911) B3147911
theorem B3147917 : Blo 2097435 3147917 := bbase (se 3 (by rfl) ⟨590234, by rfl⟩ : syracuseStep 3147917 = 1180469) (by norm_num)
theorem B2098611 : Blo 2097435 2098611 := bstep (se 1 (by rfl) ⟨1573958, by rfl⟩ : syracuseStep 2098611 = 3147917) B3147917
theorem B4721885 : Blo 2097435 4721885 := bbase (se 3 (by rfl) ⟨885353, by rfl⟩ : syracuseStep 4721885 = 1770707) (by norm_num)
theorem B3147923 : Blo 2097435 3147923 := bstep (se 1 (by rfl) ⟨2360942, by rfl⟩ : syracuseStep 3147923 = 4721885) B4721885
theorem B2098615 : Blo 2097435 2098615 := bstep (se 1 (by rfl) ⟨1573961, by rfl⟩ : syracuseStep 2098615 = 3147923) B3147923
theorem B3541421 : Blo 2097435 3541421 := bbase (se 3 (by rfl) ⟨664016, by rfl⟩ : syracuseStep 3541421 = 1328033) (by norm_num)
theorem B2360947 : Blo 2097435 2360947 := bstep (se 1 (by rfl) ⟨1770710, by rfl⟩ : syracuseStep 2360947 = 3541421) B3541421
theorem B3147929 : Blo 2097435 3147929 := bstep (se 2 (by rfl) ⟨1180473, by rfl⟩ : syracuseStep 3147929 = 2360947) B2360947
theorem B2098619 : Blo 2097435 2098619 := bstep (se 1 (by rfl) ⟨1573964, by rfl⟩ : syracuseStep 2098619 = 3147929) B3147929
theorem B2692309 : Blo 2097435 2692309 := bbase (se 7 (by rfl) ⟨31550, by rfl⟩ : syracuseStep 2692309 = 63101) (by norm_num)
theorem B3589745 : Blo 2097435 3589745 := bstep (se 2 (by rfl) ⟨1346154, by rfl⟩ : syracuseStep 3589745 = 2692309) B2692309
theorem B9572653 : Blo 2097435 9572653 := bstep (se 3 (by rfl) ⟨1794872, by rfl⟩ : syracuseStep 9572653 = 3589745) B3589745
theorem B12763537 : Blo 2097435 12763537 := bstep (se 2 (by rfl) ⟨4786326, by rfl⟩ : syracuseStep 12763537 = 9572653) B9572653
theorem B68072197 : Blo 2097435 68072197 := bstep (se 4 (by rfl) ⟨6381768, by rfl⟩ : syracuseStep 68072197 = 12763537) B12763537
theorem B90762929 : Blo 2097435 90762929 := bstep (se 2 (by rfl) ⟨34036098, by rfl⟩ : syracuseStep 90762929 = 68072197) B68072197
theorem B60508619 : Blo 2097435 60508619 := bstep (se 1 (by rfl) ⟨45381464, by rfl⟩ : syracuseStep 60508619 = 90762929) B90762929
theorem B40339079 : Blo 2097435 40339079 := bstep (se 1 (by rfl) ⟨30254309, by rfl⟩ : syracuseStep 40339079 = 60508619) B60508619
theorem B26892719 : Blo 2097435 26892719 := bstep (se 1 (by rfl) ⟨20169539, by rfl⟩ : syracuseStep 26892719 = 40339079) B40339079
theorem B17928479 : Blo 2097435 17928479 := bstep (se 1 (by rfl) ⟨13446359, by rfl⟩ : syracuseStep 17928479 = 26892719) B26892719
theorem B11952319 : Blo 2097435 11952319 := bstep (se 1 (by rfl) ⟨8964239, by rfl⟩ : syracuseStep 11952319 = 17928479) B17928479
theorem B15936425 : Blo 2097435 15936425 := bstep (se 2 (by rfl) ⟨5976159, by rfl⟩ : syracuseStep 15936425 = 11952319) B11952319
theorem B10624283 : Blo 2097435 10624283 := bstep (se 1 (by rfl) ⟨7968212, by rfl⟩ : syracuseStep 10624283 = 15936425) B15936425
theorem B7082855 : Blo 2097435 7082855 := bstep (se 1 (by rfl) ⟨5312141, by rfl⟩ : syracuseStep 7082855 = 10624283) B10624283
theorem B4721903 : Blo 2097435 4721903 := bstep (se 1 (by rfl) ⟨3541427, by rfl⟩ : syracuseStep 4721903 = 7082855) B7082855
theorem B3147935 : Blo 2097435 3147935 := bstep (se 1 (by rfl) ⟨2360951, by rfl⟩ : syracuseStep 3147935 = 4721903) B4721903
theorem B2098623 : Blo 2097435 2098623 := bstep (se 1 (by rfl) ⟨1573967, by rfl⟩ : syracuseStep 2098623 = 3147935) B3147935
theorem B3147941 : Blo 2097435 3147941 := bbase (se 4 (by rfl) ⟨295119, by rfl⟩ : syracuseStep 3147941 = 590239) (by norm_num)
theorem B2098627 : Blo 2097435 2098627 := bstep (se 1 (by rfl) ⟨1573970, by rfl⟩ : syracuseStep 2098627 = 3147941) B3147941
theorem B2656081 : Blo 2097435 2656081 := bbase (se 2 (by rfl) ⟨996030, by rfl⟩ : syracuseStep 2656081 = 1992061) (by norm_num)
theorem B3541441 : Blo 2097435 3541441 := bstep (se 2 (by rfl) ⟨1328040, by rfl⟩ : syracuseStep 3541441 = 2656081) B2656081
theorem B4721921 : Blo 2097435 4721921 := bstep (se 2 (by rfl) ⟨1770720, by rfl⟩ : syracuseStep 4721921 = 3541441) B3541441
theorem B3147947 : Blo 2097435 3147947 := bstep (se 1 (by rfl) ⟨2360960, by rfl⟩ : syracuseStep 3147947 = 4721921) B4721921
theorem B2098631 : Blo 2097435 2098631 := bstep (se 1 (by rfl) ⟨1573973, by rfl⟩ : syracuseStep 2098631 = 3147947) B3147947
theorem B2360965 : Blo 2097435 2360965 := bbase (se 4 (by rfl) ⟨221340, by rfl⟩ : syracuseStep 2360965 = 442681) (by norm_num)
theorem B3147953 : Blo 2097435 3147953 := bstep (se 2 (by rfl) ⟨1180482, by rfl⟩ : syracuseStep 3147953 = 2360965) B2360965
theorem B2098635 : Blo 2097435 2098635 := bstep (se 1 (by rfl) ⟨1573976, by rfl⟩ : syracuseStep 2098635 = 3147953) B3147953
theorem B4312597 : Blo 2097435 4312597 := bbase (se 6 (by rfl) ⟨101076, by rfl⟩ : syracuseStep 4312597 = 202153) (by norm_num)
theorem B5750129 : Blo 2097435 5750129 := bstep (se 2 (by rfl) ⟨2156298, by rfl⟩ : syracuseStep 5750129 = 4312597) B4312597
theorem B3833419 : Blo 2097435 3833419 := bstep (se 1 (by rfl) ⟨2875064, by rfl⟩ : syracuseStep 3833419 = 5750129) B5750129
theorem B5111225 : Blo 2097435 5111225 := bstep (se 2 (by rfl) ⟨1916709, by rfl⟩ : syracuseStep 5111225 = 3833419) B3833419
theorem B3407483 : Blo 2097435 3407483 := bstep (se 1 (by rfl) ⟨2555612, by rfl⟩ : syracuseStep 3407483 = 5111225) B5111225
theorem B2271655 : Blo 2097435 2271655 := bstep (se 1 (by rfl) ⟨1703741, by rfl⟩ : syracuseStep 2271655 = 3407483) B3407483
theorem B12115493 : Blo 2097435 12115493 := bstep (se 4 (by rfl) ⟨1135827, by rfl⟩ : syracuseStep 12115493 = 2271655) B2271655
theorem B8076995 : Blo 2097435 8076995 := bstep (se 1 (by rfl) ⟨6057746, by rfl⟩ : syracuseStep 8076995 = 12115493) B12115493
theorem B5384663 : Blo 2097435 5384663 := bstep (se 1 (by rfl) ⟨4038497, by rfl⟩ : syracuseStep 5384663 = 8076995) B8076995
theorem B3589775 : Blo 2097435 3589775 := bstep (se 1 (by rfl) ⟨2692331, by rfl⟩ : syracuseStep 3589775 = 5384663) B5384663
theorem B2393183 : Blo 2097435 2393183 := bstep (se 1 (by rfl) ⟨1794887, by rfl⟩ : syracuseStep 2393183 = 3589775) B3589775
theorem B6381821 : Blo 2097435 6381821 := bstep (se 3 (by rfl) ⟨1196591, by rfl⟩ : syracuseStep 6381821 = 2393183) B2393183
theorem B4254547 : Blo 2097435 4254547 := bstep (se 1 (by rfl) ⟨3190910, by rfl⟩ : syracuseStep 4254547 = 6381821) B6381821
theorem B5672729 : Blo 2097435 5672729 := bstep (se 2 (by rfl) ⟨2127273, by rfl⟩ : syracuseStep 5672729 = 4254547) B4254547
theorem B3781819 : Blo 2097435 3781819 := bstep (se 1 (by rfl) ⟨2836364, by rfl⟩ : syracuseStep 3781819 = 5672729) B5672729
theorem B5042425 : Blo 2097435 5042425 := bstep (se 2 (by rfl) ⟨1890909, by rfl⟩ : syracuseStep 5042425 = 3781819) B3781819
theorem B6723233 : Blo 2097435 6723233 := bstep (se 2 (by rfl) ⟨2521212, by rfl⟩ : syracuseStep 6723233 = 5042425) B5042425
theorem B4482155 : Blo 2097435 4482155 := bstep (se 1 (by rfl) ⟨3361616, by rfl⟩ : syracuseStep 4482155 = 6723233) B6723233
theorem B2988103 : Blo 2097435 2988103 := bstep (se 1 (by rfl) ⟨2241077, by rfl⟩ : syracuseStep 2988103 = 4482155) B4482155
theorem B3984137 : Blo 2097435 3984137 := bstep (se 2 (by rfl) ⟨1494051, by rfl⟩ : syracuseStep 3984137 = 2988103) B2988103
theorem B2656091 : Blo 2097435 2656091 := bstep (se 1 (by rfl) ⟨1992068, by rfl⟩ : syracuseStep 2656091 = 3984137) B3984137
theorem B7082909 : Blo 2097435 7082909 := bstep (se 3 (by rfl) ⟨1328045, by rfl⟩ : syracuseStep 7082909 = 2656091) B2656091
theorem B4721939 : Blo 2097435 4721939 := bstep (se 1 (by rfl) ⟨3541454, by rfl⟩ : syracuseStep 4721939 = 7082909) B7082909
theorem B3147959 : Blo 2097435 3147959 := bstep (se 1 (by rfl) ⟨2360969, by rfl⟩ : syracuseStep 3147959 = 4721939) B4721939
theorem B2098639 : Blo 2097435 2098639 := bstep (se 1 (by rfl) ⟨1573979, by rfl⟩ : syracuseStep 2098639 = 3147959) B3147959
theorem B3147965 : Blo 2097435 3147965 := bbase (se 3 (by rfl) ⟨590243, by rfl⟩ : syracuseStep 3147965 = 1180487) (by norm_num)
theorem B2098643 : Blo 2097435 2098643 := bstep (se 1 (by rfl) ⟨1573982, by rfl⟩ : syracuseStep 2098643 = 3147965) B3147965
theorem B4721957 : Blo 2097435 4721957 := bbase (se 4 (by rfl) ⟨442683, by rfl⟩ : syracuseStep 4721957 = 885367) (by norm_num)
theorem B3147971 : Blo 2097435 3147971 := bstep (se 1 (by rfl) ⟨2360978, by rfl⟩ : syracuseStep 3147971 = 4721957) B4721957
theorem B2098647 : Blo 2097435 2098647 := bstep (se 1 (by rfl) ⟨1573985, by rfl⟩ : syracuseStep 2098647 = 3147971) B3147971
theorem B5312213 : Blo 2097435 5312213 := bbase (se 7 (by rfl) ⟨62252, by rfl⟩ : syracuseStep 5312213 = 124505) (by norm_num)
theorem B3541475 : Blo 2097435 3541475 := bstep (se 1 (by rfl) ⟨2656106, by rfl⟩ : syracuseStep 3541475 = 5312213) B5312213
theorem B2360983 : Blo 2097435 2360983 := bstep (se 1 (by rfl) ⟨1770737, by rfl⟩ : syracuseStep 2360983 = 3541475) B3541475
theorem B3147977 : Blo 2097435 3147977 := bstep (se 2 (by rfl) ⟨1180491, by rfl⟩ : syracuseStep 3147977 = 2360983) B2360983
theorem B2098651 : Blo 2097435 2098651 := bstep (se 1 (by rfl) ⟨1573988, by rfl⟩ : syracuseStep 2098651 = 3147977) B3147977
theorem B8509157 : Blo 2097435 8509157 := bbase (se 4 (by rfl) ⟨797733, by rfl⟩ : syracuseStep 8509157 = 1595467) (by norm_num)
theorem B5672771 : Blo 2097435 5672771 := bstep (se 1 (by rfl) ⟨4254578, by rfl⟩ : syracuseStep 5672771 = 8509157) B8509157
theorem B3781847 : Blo 2097435 3781847 := bstep (se 1 (by rfl) ⟨2836385, by rfl⟩ : syracuseStep 3781847 = 5672771) B5672771
theorem B10084925 : Blo 2097435 10084925 := bstep (se 3 (by rfl) ⟨1890923, by rfl⟩ : syracuseStep 10084925 = 3781847) B3781847
theorem B6723283 : Blo 2097435 6723283 := bstep (se 1 (by rfl) ⟨5042462, by rfl⟩ : syracuseStep 6723283 = 10084925) B10084925
theorem B8964377 : Blo 2097435 8964377 := bstep (se 2 (by rfl) ⟨3361641, by rfl⟩ : syracuseStep 8964377 = 6723283) B6723283
theorem B5976251 : Blo 2097435 5976251 := bstep (se 1 (by rfl) ⟨4482188, by rfl⟩ : syracuseStep 5976251 = 8964377) B8964377
theorem B3984167 : Blo 2097435 3984167 := bstep (se 1 (by rfl) ⟨2988125, by rfl⟩ : syracuseStep 3984167 = 5976251) B5976251
theorem B10624445 : Blo 2097435 10624445 := bstep (se 3 (by rfl) ⟨1992083, by rfl⟩ : syracuseStep 10624445 = 3984167) B3984167
theorem B7082963 : Blo 2097435 7082963 := bstep (se 1 (by rfl) ⟨5312222, by rfl⟩ : syracuseStep 7082963 = 10624445) B10624445
theorem B4721975 : Blo 2097435 4721975 := bstep (se 1 (by rfl) ⟨3541481, by rfl⟩ : syracuseStep 4721975 = 7082963) B7082963
theorem B3147983 : Blo 2097435 3147983 := bstep (se 1 (by rfl) ⟨2360987, by rfl⟩ : syracuseStep 3147983 = 4721975) B4721975
theorem B2098655 : Blo 2097435 2098655 := bstep (se 1 (by rfl) ⟨1573991, by rfl⟩ : syracuseStep 2098655 = 3147983) B3147983
theorem B3147989 : Blo 2097435 3147989 := bbase (se 7 (by rfl) ⟨36890, by rfl⟩ : syracuseStep 3147989 = 73781) (by norm_num)
theorem B2098659 : Blo 2097435 2098659 := bstep (se 1 (by rfl) ⟨1573994, by rfl⟩ : syracuseStep 2098659 = 3147989) B3147989
theorem B2836397 : Blo 2097435 2836397 := bbase (se 3 (by rfl) ⟨531824, by rfl⟩ : syracuseStep 2836397 = 1063649) (by norm_num)
theorem B7563725 : Blo 2097435 7563725 := bstep (se 3 (by rfl) ⟨1418198, by rfl⟩ : syracuseStep 7563725 = 2836397) B2836397
theorem B5042483 : Blo 2097435 5042483 := bstep (se 1 (by rfl) ⟨3781862, by rfl⟩ : syracuseStep 5042483 = 7563725) B7563725
theorem B3361655 : Blo 2097435 3361655 := bstep (se 1 (by rfl) ⟨2521241, by rfl⟩ : syracuseStep 3361655 = 5042483) B5042483
theorem B2241103 : Blo 2097435 2241103 := bstep (se 1 (by rfl) ⟨1680827, by rfl⟩ : syracuseStep 2241103 = 3361655) B3361655
theorem B2988137 : Blo 2097435 2988137 := bstep (se 2 (by rfl) ⟨1120551, by rfl⟩ : syracuseStep 2988137 = 2241103) B2241103
theorem B7968365 : Blo 2097435 7968365 := bstep (se 3 (by rfl) ⟨1494068, by rfl⟩ : syracuseStep 7968365 = 2988137) B2988137
theorem B5312243 : Blo 2097435 5312243 := bstep (se 1 (by rfl) ⟨3984182, by rfl⟩ : syracuseStep 5312243 = 7968365) B7968365
theorem B3541495 : Blo 2097435 3541495 := bstep (se 1 (by rfl) ⟨2656121, by rfl⟩ : syracuseStep 3541495 = 5312243) B5312243
theorem B4721993 : Blo 2097435 4721993 := bstep (se 2 (by rfl) ⟨1770747, by rfl⟩ : syracuseStep 4721993 = 3541495) B3541495
theorem B3147995 : Blo 2097435 3147995 := bstep (se 1 (by rfl) ⟨2360996, by rfl⟩ : syracuseStep 3147995 = 4721993) B4721993
theorem B2098663 : Blo 2097435 2098663 := bstep (se 1 (by rfl) ⟨1573997, by rfl⟩ : syracuseStep 2098663 = 3147995) B3147995
theorem B2361001 : Blo 2097435 2361001 := bbase (se 2 (by rfl) ⟨885375, by rfl⟩ : syracuseStep 2361001 = 1770751) (by norm_num)
theorem B3148001 : Blo 2097435 3148001 := bstep (se 2 (by rfl) ⟨1180500, by rfl⟩ : syracuseStep 3148001 = 2361001) B2361001
theorem B2098667 : Blo 2097435 2098667 := bstep (se 1 (by rfl) ⟨1574000, by rfl⟩ : syracuseStep 2098667 = 3148001) B3148001
theorem B5042501 : Blo 2097435 5042501 := bbase (se 4 (by rfl) ⟨472734, by rfl⟩ : syracuseStep 5042501 = 945469) (by norm_num)
theorem B3361667 : Blo 2097435 3361667 := bstep (se 1 (by rfl) ⟨2521250, by rfl⟩ : syracuseStep 3361667 = 5042501) B5042501
theorem B8964445 : Blo 2097435 8964445 := bstep (se 3 (by rfl) ⟨1680833, by rfl⟩ : syracuseStep 8964445 = 3361667) B3361667
theorem B11952593 : Blo 2097435 11952593 := bstep (se 2 (by rfl) ⟨4482222, by rfl⟩ : syracuseStep 11952593 = 8964445) B8964445
theorem B7968395 : Blo 2097435 7968395 := bstep (se 1 (by rfl) ⟨5976296, by rfl⟩ : syracuseStep 7968395 = 11952593) B11952593
theorem B5312263 : Blo 2097435 5312263 := bstep (se 1 (by rfl) ⟨3984197, by rfl⟩ : syracuseStep 5312263 = 7968395) B7968395
theorem B7083017 : Blo 2097435 7083017 := bstep (se 2 (by rfl) ⟨2656131, by rfl⟩ : syracuseStep 7083017 = 5312263) B5312263
theorem B4722011 : Blo 2097435 4722011 := bstep (se 1 (by rfl) ⟨3541508, by rfl⟩ : syracuseStep 4722011 = 7083017) B7083017
theorem B3148007 : Blo 2097435 3148007 := bstep (se 1 (by rfl) ⟨2361005, by rfl⟩ : syracuseStep 3148007 = 4722011) B4722011
theorem B2098671 : Blo 2097435 2098671 := bstep (se 1 (by rfl) ⟨1574003, by rfl⟩ : syracuseStep 2098671 = 3148007) B3148007
theorem B3148013 : Blo 2097435 3148013 := bbase (se 3 (by rfl) ⟨590252, by rfl⟩ : syracuseStep 3148013 = 1180505) (by norm_num)
theorem B2098675 : Blo 2097435 2098675 := bstep (se 1 (by rfl) ⟨1574006, by rfl⟩ : syracuseStep 2098675 = 3148013) B3148013
theorem B4722029 : Blo 2097435 4722029 := bbase (se 3 (by rfl) ⟨885380, by rfl⟩ : syracuseStep 4722029 = 1770761) (by norm_num)
theorem B3148019 : Blo 2097435 3148019 := bstep (se 1 (by rfl) ⟨2361014, by rfl⟩ : syracuseStep 3148019 = 4722029) B4722029
theorem B2098679 : Blo 2097435 2098679 := bstep (se 1 (by rfl) ⟨1574009, by rfl⟩ : syracuseStep 2098679 = 3148019) B3148019
theorem B3984221 : Blo 2097435 3984221 := bbase (se 3 (by rfl) ⟨747041, by rfl⟩ : syracuseStep 3984221 = 1494083) (by norm_num)
theorem B2656147 : Blo 2097435 2656147 := bstep (se 1 (by rfl) ⟨1992110, by rfl⟩ : syracuseStep 2656147 = 3984221) B3984221
theorem B3541529 : Blo 2097435 3541529 := bstep (se 2 (by rfl) ⟨1328073, by rfl⟩ : syracuseStep 3541529 = 2656147) B2656147
theorem B2361019 : Blo 2097435 2361019 := bstep (se 1 (by rfl) ⟨1770764, by rfl⟩ : syracuseStep 2361019 = 3541529) B3541529
theorem B3148025 : Blo 2097435 3148025 := bstep (se 2 (by rfl) ⟨1180509, by rfl⟩ : syracuseStep 3148025 = 2361019) B2361019
theorem B2098683 : Blo 2097435 2098683 := bstep (se 1 (by rfl) ⟨1574012, by rfl⟩ : syracuseStep 2098683 = 3148025) B3148025
theorem B10085077 : Blo 2097435 10085077 := bbase (se 7 (by rfl) ⟨118184, by rfl⟩ : syracuseStep 10085077 = 236369) (by norm_num)
theorem B53787077 : Blo 2097435 53787077 := bstep (se 4 (by rfl) ⟨5042538, by rfl⟩ : syracuseStep 53787077 = 10085077) B10085077
theorem B35858051 : Blo 2097435 35858051 := bstep (se 1 (by rfl) ⟨26893538, by rfl⟩ : syracuseStep 35858051 = 53787077) B53787077
theorem B23905367 : Blo 2097435 23905367 := bstep (se 1 (by rfl) ⟨17929025, by rfl⟩ : syracuseStep 23905367 = 35858051) B35858051
theorem B15936911 : Blo 2097435 15936911 := bstep (se 1 (by rfl) ⟨11952683, by rfl⟩ : syracuseStep 15936911 = 23905367) B23905367
theorem B10624607 : Blo 2097435 10624607 := bstep (se 1 (by rfl) ⟨7968455, by rfl⟩ : syracuseStep 10624607 = 15936911) B15936911
theorem B7083071 : Blo 2097435 7083071 := bstep (se 1 (by rfl) ⟨5312303, by rfl⟩ : syracuseStep 7083071 = 10624607) B10624607
theorem B4722047 : Blo 2097435 4722047 := bstep (se 1 (by rfl) ⟨3541535, by rfl⟩ : syracuseStep 4722047 = 7083071) B7083071
theorem B3148031 : Blo 2097435 3148031 := bstep (se 1 (by rfl) ⟨2361023, by rfl⟩ : syracuseStep 3148031 = 4722047) B4722047
theorem B2098687 : Blo 2097435 2098687 := bstep (se 1 (by rfl) ⟨1574015, by rfl⟩ : syracuseStep 2098687 = 3148031) B3148031
theorem B3148037 : Blo 2097435 3148037 := bbase (se 4 (by rfl) ⟨295128, by rfl⟩ : syracuseStep 3148037 = 590257) (by norm_num)
theorem B2098691 : Blo 2097435 2098691 := bstep (se 1 (by rfl) ⟨1574018, by rfl⟩ : syracuseStep 2098691 = 3148037) B3148037
theorem B3541549 : Blo 2097435 3541549 := bbase (se 3 (by rfl) ⟨664040, by rfl⟩ : syracuseStep 3541549 = 1328081) (by norm_num)
theorem B4722065 : Blo 2097435 4722065 := bstep (se 2 (by rfl) ⟨1770774, by rfl⟩ : syracuseStep 4722065 = 3541549) B3541549
theorem B3148043 : Blo 2097435 3148043 := bstep (se 1 (by rfl) ⟨2361032, by rfl⟩ : syracuseStep 3148043 = 4722065) B4722065
theorem B2098695 : Blo 2097435 2098695 := bstep (se 1 (by rfl) ⟨1574021, by rfl⟩ : syracuseStep 2098695 = 3148043) B3148043
theorem B2361037 : Blo 2097435 2361037 := bbase (se 3 (by rfl) ⟨442694, by rfl⟩ : syracuseStep 2361037 = 885389) (by norm_num)
theorem B3148049 : Blo 2097435 3148049 := bstep (se 2 (by rfl) ⟨1180518, by rfl⟩ : syracuseStep 3148049 = 2361037) B2361037
theorem B2098699 : Blo 2097435 2098699 := bstep (se 1 (by rfl) ⟨1574024, by rfl⟩ : syracuseStep 2098699 = 3148049) B3148049
theorem B7083125 : Blo 2097435 7083125 := bbase (se 5 (by rfl) ⟨332021, by rfl⟩ : syracuseStep 7083125 = 664043) (by norm_num)
theorem B4722083 : Blo 2097435 4722083 := bstep (se 1 (by rfl) ⟨3541562, by rfl⟩ : syracuseStep 4722083 = 7083125) B7083125
theorem B3148055 : Blo 2097435 3148055 := bstep (se 1 (by rfl) ⟨2361041, by rfl⟩ : syracuseStep 3148055 = 4722083) B4722083
theorem B2098703 : Blo 2097435 2098703 := bstep (se 1 (by rfl) ⟨1574027, by rfl⟩ : syracuseStep 2098703 = 3148055) B3148055
theorem B3148061 : Blo 2097435 3148061 := bbase (se 3 (by rfl) ⟨590261, by rfl⟩ : syracuseStep 3148061 = 1180523) (by norm_num)
theorem B2098707 : Blo 2097435 2098707 := bstep (se 1 (by rfl) ⟨1574030, by rfl⟩ : syracuseStep 2098707 = 3148061) B3148061
theorem B4722101 : Blo 2097435 4722101 := bbase (se 5 (by rfl) ⟨221348, by rfl⟩ : syracuseStep 4722101 = 442697) (by norm_num)
theorem B3148067 : Blo 2097435 3148067 := bstep (se 1 (by rfl) ⟨2361050, by rfl⟩ : syracuseStep 3148067 = 4722101) B4722101
theorem B2098711 : Blo 2097435 2098711 := bstep (se 1 (by rfl) ⟨1574033, by rfl⟩ : syracuseStep 2098711 = 3148067) B3148067
theorem B4482317 : Blo 2097435 4482317 := bbase (se 3 (by rfl) ⟨840434, by rfl⟩ : syracuseStep 4482317 = 1680869) (by norm_num)
theorem B11952845 : Blo 2097435 11952845 := bstep (se 3 (by rfl) ⟨2241158, by rfl⟩ : syracuseStep 11952845 = 4482317) B4482317
theorem B7968563 : Blo 2097435 7968563 := bstep (se 1 (by rfl) ⟨5976422, by rfl⟩ : syracuseStep 7968563 = 11952845) B11952845
theorem B5312375 : Blo 2097435 5312375 := bstep (se 1 (by rfl) ⟨3984281, by rfl⟩ : syracuseStep 5312375 = 7968563) B7968563
theorem B3541583 : Blo 2097435 3541583 := bstep (se 1 (by rfl) ⟨2656187, by rfl⟩ : syracuseStep 3541583 = 5312375) B5312375
theorem B2361055 : Blo 2097435 2361055 := bstep (se 1 (by rfl) ⟨1770791, by rfl⟩ : syracuseStep 2361055 = 3541583) B3541583
theorem B3148073 : Blo 2097435 3148073 := bstep (se 2 (by rfl) ⟨1180527, by rfl⟩ : syracuseStep 3148073 = 2361055) B2361055
theorem B2098715 : Blo 2097435 2098715 := bstep (se 1 (by rfl) ⟨1574036, by rfl⟩ : syracuseStep 2098715 = 3148073) B3148073
theorem B4482325 : Blo 2097435 4482325 := bbase (se 6 (by rfl) ⟨105054, by rfl⟩ : syracuseStep 4482325 = 210109) (by norm_num)
theorem B5976433 : Blo 2097435 5976433 := bstep (se 2 (by rfl) ⟨2241162, by rfl⟩ : syracuseStep 5976433 = 4482325) B4482325
theorem B7968577 : Blo 2097435 7968577 := bstep (se 2 (by rfl) ⟨2988216, by rfl⟩ : syracuseStep 7968577 = 5976433) B5976433
theorem B10624769 : Blo 2097435 10624769 := bstep (se 2 (by rfl) ⟨3984288, by rfl⟩ : syracuseStep 10624769 = 7968577) B7968577
theorem B7083179 : Blo 2097435 7083179 := bstep (se 1 (by rfl) ⟨5312384, by rfl⟩ : syracuseStep 7083179 = 10624769) B10624769
theorem B4722119 : Blo 2097435 4722119 := bstep (se 1 (by rfl) ⟨3541589, by rfl⟩ : syracuseStep 4722119 = 7083179) B7083179
theorem B3148079 : Blo 2097435 3148079 := bstep (se 1 (by rfl) ⟨2361059, by rfl⟩ : syracuseStep 3148079 = 4722119) B4722119
theorem B2098719 : Blo 2097435 2098719 := bstep (se 1 (by rfl) ⟨1574039, by rfl⟩ : syracuseStep 2098719 = 3148079) B3148079
theorem B3148085 : Blo 2097435 3148085 := bbase (se 5 (by rfl) ⟨147566, by rfl⟩ : syracuseStep 3148085 = 295133) (by norm_num)
theorem B2098723 : Blo 2097435 2098723 := bstep (se 1 (by rfl) ⟨1574042, by rfl⟩ : syracuseStep 2098723 = 3148085) B3148085
theorem B5312405 : Blo 2097435 5312405 := bbase (se 6 (by rfl) ⟨124509, by rfl⟩ : syracuseStep 5312405 = 249019) (by norm_num)
theorem B3541603 : Blo 2097435 3541603 := bstep (se 1 (by rfl) ⟨2656202, by rfl⟩ : syracuseStep 3541603 = 5312405) B5312405
theorem B4722137 : Blo 2097435 4722137 := bstep (se 2 (by rfl) ⟨1770801, by rfl⟩ : syracuseStep 4722137 = 3541603) B3541603
theorem B3148091 : Blo 2097435 3148091 := bstep (se 1 (by rfl) ⟨2361068, by rfl⟩ : syracuseStep 3148091 = 4722137) B4722137
theorem B2098727 : Blo 2097435 2098727 := bstep (se 1 (by rfl) ⟨1574045, by rfl⟩ : syracuseStep 2098727 = 3148091) B3148091
theorem B2361073 : Blo 2097435 2361073 := bbase (se 2 (by rfl) ⟨885402, by rfl⟩ : syracuseStep 2361073 = 1770805) (by norm_num)
theorem B3148097 : Blo 2097435 3148097 := bstep (se 2 (by rfl) ⟨1180536, by rfl⟩ : syracuseStep 3148097 = 2361073) B2361073
theorem B2098731 : Blo 2097435 2098731 := bstep (se 1 (by rfl) ⟨1574048, by rfl⟩ : syracuseStep 2098731 = 3148097) B3148097
theorem B17251157 : Blo 2097435 17251157 := bbase (se 9 (by rfl) ⟨50540, by rfl⟩ : syracuseStep 17251157 = 101081) (by norm_num)
theorem B46003085 : Blo 2097435 46003085 := bstep (se 3 (by rfl) ⟨8625578, by rfl⟩ : syracuseStep 46003085 = 17251157) B17251157
theorem B30668723 : Blo 2097435 30668723 := bstep (se 1 (by rfl) ⟨23001542, by rfl⟩ : syracuseStep 30668723 = 46003085) B46003085
theorem B20445815 : Blo 2097435 20445815 := bstep (se 1 (by rfl) ⟨15334361, by rfl⟩ : syracuseStep 20445815 = 30668723) B30668723
theorem B54522173 : Blo 2097435 54522173 := bstep (se 3 (by rfl) ⟨10222907, by rfl⟩ : syracuseStep 54522173 = 20445815) B20445815
theorem B36348115 : Blo 2097435 36348115 := bstep (se 1 (by rfl) ⟨27261086, by rfl⟩ : syracuseStep 36348115 = 54522173) B54522173
theorem B48464153 : Blo 2097435 48464153 := bstep (se 2 (by rfl) ⟨18174057, by rfl⟩ : syracuseStep 48464153 = 36348115) B36348115
theorem B32309435 : Blo 2097435 32309435 := bstep (se 1 (by rfl) ⟨24232076, by rfl⟩ : syracuseStep 32309435 = 48464153) B48464153
theorem B21539623 : Blo 2097435 21539623 := bstep (se 1 (by rfl) ⟨16154717, by rfl⟩ : syracuseStep 21539623 = 32309435) B32309435
theorem B28719497 : Blo 2097435 28719497 := bstep (se 2 (by rfl) ⟨10769811, by rfl⟩ : syracuseStep 28719497 = 21539623) B21539623
theorem B19146331 : Blo 2097435 19146331 := bstep (se 1 (by rfl) ⟨14359748, by rfl⟩ : syracuseStep 19146331 = 28719497) B28719497
theorem B25528441 : Blo 2097435 25528441 := bstep (se 2 (by rfl) ⟨9573165, by rfl⟩ : syracuseStep 25528441 = 19146331) B19146331
theorem B34037921 : Blo 2097435 34037921 := bstep (se 2 (by rfl) ⟨12764220, by rfl⟩ : syracuseStep 34037921 = 25528441) B25528441
theorem B22691947 : Blo 2097435 22691947 := bstep (se 1 (by rfl) ⟨17018960, by rfl⟩ : syracuseStep 22691947 = 34037921) B34037921
theorem B30255929 : Blo 2097435 30255929 := bstep (se 2 (by rfl) ⟨11345973, by rfl⟩ : syracuseStep 30255929 = 22691947) B22691947
theorem B20170619 : Blo 2097435 20170619 := bstep (se 1 (by rfl) ⟨15127964, by rfl⟩ : syracuseStep 20170619 = 30255929) B30255929
theorem B13447079 : Blo 2097435 13447079 := bstep (se 1 (by rfl) ⟨10085309, by rfl⟩ : syracuseStep 13447079 = 20170619) B20170619
theorem B8964719 : Blo 2097435 8964719 := bstep (se 1 (by rfl) ⟨6723539, by rfl⟩ : syracuseStep 8964719 = 13447079) B13447079
theorem B5976479 : Blo 2097435 5976479 := bstep (se 1 (by rfl) ⟨4482359, by rfl⟩ : syracuseStep 5976479 = 8964719) B8964719
theorem B3984319 : Blo 2097435 3984319 := bstep (se 1 (by rfl) ⟨2988239, by rfl⟩ : syracuseStep 3984319 = 5976479) B5976479
theorem B5312425 : Blo 2097435 5312425 := bstep (se 2 (by rfl) ⟨1992159, by rfl⟩ : syracuseStep 5312425 = 3984319) B3984319
theorem B7083233 : Blo 2097435 7083233 := bstep (se 2 (by rfl) ⟨2656212, by rfl⟩ : syracuseStep 7083233 = 5312425) B5312425
theorem B4722155 : Blo 2097435 4722155 := bstep (se 1 (by rfl) ⟨3541616, by rfl⟩ : syracuseStep 4722155 = 7083233) B7083233
theorem B3148103 : Blo 2097435 3148103 := bstep (se 1 (by rfl) ⟨2361077, by rfl⟩ : syracuseStep 3148103 = 4722155) B4722155
theorem B2098735 : Blo 2097435 2098735 := bstep (se 1 (by rfl) ⟨1574051, by rfl⟩ : syracuseStep 2098735 = 3148103) B3148103
theorem B3148109 : Blo 2097435 3148109 := bbase (se 3 (by rfl) ⟨590270, by rfl⟩ : syracuseStep 3148109 = 1180541) (by norm_num)
theorem B2098739 : Blo 2097435 2098739 := bstep (se 1 (by rfl) ⟨1574054, by rfl⟩ : syracuseStep 2098739 = 3148109) B3148109
theorem B4722173 : Blo 2097435 4722173 := bbase (se 3 (by rfl) ⟨885407, by rfl⟩ : syracuseStep 4722173 = 1770815) (by norm_num)
theorem B3148115 : Blo 2097435 3148115 := bstep (se 1 (by rfl) ⟨2361086, by rfl⟩ : syracuseStep 3148115 = 4722173) B4722173
theorem B2098743 : Blo 2097435 2098743 := bstep (se 1 (by rfl) ⟨1574057, by rfl⟩ : syracuseStep 2098743 = 3148115) B3148115
theorem B3541637 : Blo 2097435 3541637 := bbase (se 4 (by rfl) ⟨332028, by rfl⟩ : syracuseStep 3541637 = 664057) (by norm_num)
theorem B2361091 : Blo 2097435 2361091 := bstep (se 1 (by rfl) ⟨1770818, by rfl⟩ : syracuseStep 2361091 = 3541637) B3541637
theorem B3148121 : Blo 2097435 3148121 := bstep (se 2 (by rfl) ⟨1180545, by rfl⟩ : syracuseStep 3148121 = 2361091) B2361091
theorem B2098747 : Blo 2097435 2098747 := bstep (se 1 (by rfl) ⟨1574060, by rfl⟩ : syracuseStep 2098747 = 3148121) B3148121
theorem B15937397 : Blo 2097435 15937397 := bbase (se 5 (by rfl) ⟨747065, by rfl⟩ : syracuseStep 15937397 = 1494131) (by norm_num)
theorem B10624931 : Blo 2097435 10624931 := bstep (se 1 (by rfl) ⟨7968698, by rfl⟩ : syracuseStep 10624931 = 15937397) B15937397
theorem B7083287 : Blo 2097435 7083287 := bstep (se 1 (by rfl) ⟨5312465, by rfl⟩ : syracuseStep 7083287 = 10624931) B10624931
theorem B4722191 : Blo 2097435 4722191 := bstep (se 1 (by rfl) ⟨3541643, by rfl⟩ : syracuseStep 4722191 = 7083287) B7083287
theorem B3148127 : Blo 2097435 3148127 := bstep (se 1 (by rfl) ⟨2361095, by rfl⟩ : syracuseStep 3148127 = 4722191) B4722191
theorem B2098751 : Blo 2097435 2098751 := bstep (se 1 (by rfl) ⟨1574063, by rfl⟩ : syracuseStep 2098751 = 3148127) B3148127
theorem B3148133 : Blo 2097435 3148133 := bbase (se 4 (by rfl) ⟨295137, by rfl⟩ : syracuseStep 3148133 = 590275) (by norm_num)
theorem B2098755 : Blo 2097435 2098755 := bstep (se 1 (by rfl) ⟨1574066, by rfl⟩ : syracuseStep 2098755 = 3148133) B3148133
theorem B3984365 : Blo 2097435 3984365 := bbase (se 3 (by rfl) ⟨747068, by rfl⟩ : syracuseStep 3984365 = 1494137) (by norm_num)
theorem B2656243 : Blo 2097435 2656243 := bstep (se 1 (by rfl) ⟨1992182, by rfl⟩ : syracuseStep 2656243 = 3984365) B3984365
theorem B3541657 : Blo 2097435 3541657 := bstep (se 2 (by rfl) ⟨1328121, by rfl⟩ : syracuseStep 3541657 = 2656243) B2656243
theorem B4722209 : Blo 2097435 4722209 := bstep (se 2 (by rfl) ⟨1770828, by rfl⟩ : syracuseStep 4722209 = 3541657) B3541657
theorem B3148139 : Blo 2097435 3148139 := bstep (se 1 (by rfl) ⟨2361104, by rfl⟩ : syracuseStep 3148139 = 4722209) B4722209
theorem B2098759 : Blo 2097435 2098759 := bstep (se 1 (by rfl) ⟨1574069, by rfl⟩ : syracuseStep 2098759 = 3148139) B3148139
theorem B2361109 : Blo 2097435 2361109 := bbase (se 6 (by rfl) ⟨55338, by rfl⟩ : syracuseStep 2361109 = 110677) (by norm_num)
theorem B3148145 : Blo 2097435 3148145 := bstep (se 2 (by rfl) ⟨1180554, by rfl⟩ : syracuseStep 3148145 = 2361109) B2361109
theorem B2098763 : Blo 2097435 2098763 := bstep (se 1 (by rfl) ⟨1574072, by rfl⟩ : syracuseStep 2098763 = 3148145) B3148145
theorem B2656253 : Blo 2097435 2656253 := bbase (se 3 (by rfl) ⟨498047, by rfl⟩ : syracuseStep 2656253 = 996095) (by norm_num)
theorem B7083341 : Blo 2097435 7083341 := bstep (se 3 (by rfl) ⟨1328126, by rfl⟩ : syracuseStep 7083341 = 2656253) B2656253
theorem B4722227 : Blo 2097435 4722227 := bstep (se 1 (by rfl) ⟨3541670, by rfl⟩ : syracuseStep 4722227 = 7083341) B7083341
theorem B3148151 : Blo 2097435 3148151 := bstep (se 1 (by rfl) ⟨2361113, by rfl⟩ : syracuseStep 3148151 = 4722227) B4722227
theorem B2098767 : Blo 2097435 2098767 := bstep (se 1 (by rfl) ⟨1574075, by rfl⟩ : syracuseStep 2098767 = 3148151) B3148151
theorem B3148157 : Blo 2097435 3148157 := bbase (se 3 (by rfl) ⟨590279, by rfl⟩ : syracuseStep 3148157 = 1180559) (by norm_num)
theorem B2098771 : Blo 2097435 2098771 := bstep (se 1 (by rfl) ⟨1574078, by rfl⟩ : syracuseStep 2098771 = 3148157) B3148157
theorem B4722245 : Blo 2097435 4722245 := bbase (se 4 (by rfl) ⟨442710, by rfl⟩ : syracuseStep 4722245 = 885421) (by norm_num)
theorem B3148163 : Blo 2097435 3148163 := bstep (se 1 (by rfl) ⟨2361122, by rfl⟩ : syracuseStep 3148163 = 4722245) B4722245
theorem B2098775 : Blo 2097435 2098775 := bstep (se 1 (by rfl) ⟨1574081, by rfl⟩ : syracuseStep 2098775 = 3148163) B3148163
theorem B2521381 : Blo 2097435 2521381 := bbase (se 4 (by rfl) ⟨236379, by rfl⟩ : syracuseStep 2521381 = 472759) (by norm_num)
theorem B3361841 : Blo 2097435 3361841 := bstep (se 2 (by rfl) ⟨1260690, by rfl⟩ : syracuseStep 3361841 = 2521381) B2521381
theorem B2241227 : Blo 2097435 2241227 := bstep (se 1 (by rfl) ⟨1680920, by rfl⟩ : syracuseStep 2241227 = 3361841) B3361841
theorem B5976605 : Blo 2097435 5976605 := bstep (se 3 (by rfl) ⟨1120613, by rfl⟩ : syracuseStep 5976605 = 2241227) B2241227
theorem B3984403 : Blo 2097435 3984403 := bstep (se 1 (by rfl) ⟨2988302, by rfl⟩ : syracuseStep 3984403 = 5976605) B5976605
theorem B5312537 : Blo 2097435 5312537 := bstep (se 2 (by rfl) ⟨1992201, by rfl⟩ : syracuseStep 5312537 = 3984403) B3984403
theorem B3541691 : Blo 2097435 3541691 := bstep (se 1 (by rfl) ⟨2656268, by rfl⟩ : syracuseStep 3541691 = 5312537) B5312537
theorem B2361127 : Blo 2097435 2361127 := bstep (se 1 (by rfl) ⟨1770845, by rfl⟩ : syracuseStep 2361127 = 3541691) B3541691
theorem B3148169 : Blo 2097435 3148169 := bstep (se 2 (by rfl) ⟨1180563, by rfl⟩ : syracuseStep 3148169 = 2361127) B2361127
theorem B2098779 : Blo 2097435 2098779 := bstep (se 1 (by rfl) ⟨1574084, by rfl⟩ : syracuseStep 2098779 = 3148169) B3148169
theorem B10625093 : Blo 2097435 10625093 := bbase (se 4 (by rfl) ⟨996102, by rfl⟩ : syracuseStep 10625093 = 1992205) (by norm_num)
theorem B7083395 : Blo 2097435 7083395 := bstep (se 1 (by rfl) ⟨5312546, by rfl⟩ : syracuseStep 7083395 = 10625093) B10625093
theorem B4722263 : Blo 2097435 4722263 := bstep (se 1 (by rfl) ⟨3541697, by rfl⟩ : syracuseStep 4722263 = 7083395) B7083395
theorem B3148175 : Blo 2097435 3148175 := bstep (se 1 (by rfl) ⟨2361131, by rfl⟩ : syracuseStep 3148175 = 4722263) B4722263
theorem B2098783 : Blo 2097435 2098783 := bstep (se 1 (by rfl) ⟨1574087, by rfl⟩ : syracuseStep 2098783 = 3148175) B3148175
theorem B3148181 : Blo 2097435 3148181 := bbase (se 6 (by rfl) ⟨73785, by rfl⟩ : syracuseStep 3148181 = 147571) (by norm_num)
theorem B2098787 : Blo 2097435 2098787 := bstep (se 1 (by rfl) ⟨1574090, by rfl⟩ : syracuseStep 2098787 = 3148181) B3148181
theorem B3191141 : Blo 2097435 3191141 := bbase (se 4 (by rfl) ⟨299169, by rfl⟩ : syracuseStep 3191141 = 598339) (by norm_num)
theorem B2127427 : Blo 2097435 2127427 := bstep (se 1 (by rfl) ⟨1595570, by rfl⟩ : syracuseStep 2127427 = 3191141) B3191141
theorem B11346277 : Blo 2097435 11346277 := bstep (se 4 (by rfl) ⟨1063713, by rfl⟩ : syracuseStep 11346277 = 2127427) B2127427
theorem B15128369 : Blo 2097435 15128369 := bstep (se 2 (by rfl) ⟨5673138, by rfl⟩ : syracuseStep 15128369 = 11346277) B11346277
theorem B10085579 : Blo 2097435 10085579 := bstep (se 1 (by rfl) ⟨7564184, by rfl⟩ : syracuseStep 10085579 = 15128369) B15128369
theorem B6723719 : Blo 2097435 6723719 := bstep (se 1 (by rfl) ⟨5042789, by rfl⟩ : syracuseStep 6723719 = 10085579) B10085579
theorem B4482479 : Blo 2097435 4482479 := bstep (se 1 (by rfl) ⟨3361859, by rfl⟩ : syracuseStep 4482479 = 6723719) B6723719
theorem B11953277 : Blo 2097435 11953277 := bstep (se 3 (by rfl) ⟨2241239, by rfl⟩ : syracuseStep 11953277 = 4482479) B4482479
theorem B7968851 : Blo 2097435 7968851 := bstep (se 1 (by rfl) ⟨5976638, by rfl⟩ : syracuseStep 7968851 = 11953277) B11953277
theorem B5312567 : Blo 2097435 5312567 := bstep (se 1 (by rfl) ⟨3984425, by rfl⟩ : syracuseStep 5312567 = 7968851) B7968851
theorem B3541711 : Blo 2097435 3541711 := bstep (se 1 (by rfl) ⟨2656283, by rfl⟩ : syracuseStep 3541711 = 5312567) B5312567
theorem B4722281 : Blo 2097435 4722281 := bstep (se 2 (by rfl) ⟨1770855, by rfl⟩ : syracuseStep 4722281 = 3541711) B3541711
theorem B3148187 : Blo 2097435 3148187 := bstep (se 1 (by rfl) ⟨2361140, by rfl⟩ : syracuseStep 3148187 = 4722281) B4722281
theorem B2098791 : Blo 2097435 2098791 := bstep (se 1 (by rfl) ⟨1574093, by rfl⟩ : syracuseStep 2098791 = 3148187) B3148187
theorem B2361145 : Blo 2097435 2361145 := bbase (se 2 (by rfl) ⟨885429, by rfl⟩ : syracuseStep 2361145 = 1770859) (by norm_num)
theorem B3148193 : Blo 2097435 3148193 := bstep (se 2 (by rfl) ⟨1180572, by rfl⟩ : syracuseStep 3148193 = 2361145) B2361145
theorem B2098795 : Blo 2097435 2098795 := bstep (se 1 (by rfl) ⟨1574096, by rfl⟩ : syracuseStep 2098795 = 3148193) B3148193
theorem B5976661 : Blo 2097435 5976661 := bbase (se 8 (by rfl) ⟨35019, by rfl⟩ : syracuseStep 5976661 = 70039) (by norm_num)
theorem B7968881 : Blo 2097435 7968881 := bstep (se 2 (by rfl) ⟨2988330, by rfl⟩ : syracuseStep 7968881 = 5976661) B5976661
theorem B5312587 : Blo 2097435 5312587 := bstep (se 1 (by rfl) ⟨3984440, by rfl⟩ : syracuseStep 5312587 = 7968881) B7968881
theorem B7083449 : Blo 2097435 7083449 := bstep (se 2 (by rfl) ⟨2656293, by rfl⟩ : syracuseStep 7083449 = 5312587) B5312587
theorem B4722299 : Blo 2097435 4722299 := bstep (se 1 (by rfl) ⟨3541724, by rfl⟩ : syracuseStep 4722299 = 7083449) B7083449
theorem B3148199 : Blo 2097435 3148199 := bstep (se 1 (by rfl) ⟨2361149, by rfl⟩ : syracuseStep 3148199 = 4722299) B4722299
theorem B2098799 : Blo 2097435 2098799 := bstep (se 1 (by rfl) ⟨1574099, by rfl⟩ : syracuseStep 2098799 = 3148199) B3148199
theorem B3148205 : Blo 2097435 3148205 := bbase (se 3 (by rfl) ⟨590288, by rfl⟩ : syracuseStep 3148205 = 1180577) (by norm_num)
theorem B2098803 : Blo 2097435 2098803 := bstep (se 1 (by rfl) ⟨1574102, by rfl⟩ : syracuseStep 2098803 = 3148205) B3148205
theorem B4722317 : Blo 2097435 4722317 := bbase (se 3 (by rfl) ⟨885434, by rfl⟩ : syracuseStep 4722317 = 1770869) (by norm_num)
theorem B3148211 : Blo 2097435 3148211 := bstep (se 1 (by rfl) ⟨2361158, by rfl⟩ : syracuseStep 3148211 = 4722317) B4722317
theorem B2098807 : Blo 2097435 2098807 := bstep (se 1 (by rfl) ⟨1574105, by rfl⟩ : syracuseStep 2098807 = 3148211) B3148211
theorem B2656309 : Blo 2097435 2656309 := bbase (se 5 (by rfl) ⟨124514, by rfl⟩ : syracuseStep 2656309 = 249029) (by norm_num)
theorem B3541745 : Blo 2097435 3541745 := bstep (se 2 (by rfl) ⟨1328154, by rfl⟩ : syracuseStep 3541745 = 2656309) B2656309
theorem B2361163 : Blo 2097435 2361163 := bstep (se 1 (by rfl) ⟨1770872, by rfl⟩ : syracuseStep 2361163 = 3541745) B3541745
theorem B3148217 : Blo 2097435 3148217 := bstep (se 2 (by rfl) ⟨1180581, by rfl⟩ : syracuseStep 3148217 = 2361163) B2361163
theorem B2098811 : Blo 2097435 2098811 := bstep (se 1 (by rfl) ⟨1574108, by rfl⟩ : syracuseStep 2098811 = 3148217) B3148217
theorem B2271845 : Blo 2097435 2271845 := bbase (se 4 (by rfl) ⟨212985, by rfl⟩ : syracuseStep 2271845 = 425971) (by norm_num)
theorem B6058253 : Blo 2097435 6058253 := bstep (se 3 (by rfl) ⟨1135922, by rfl⟩ : syracuseStep 6058253 = 2271845) B2271845
theorem B4038835 : Blo 2097435 4038835 := bstep (se 1 (by rfl) ⟨3029126, by rfl⟩ : syracuseStep 4038835 = 6058253) B6058253
theorem B5385113 : Blo 2097435 5385113 := bstep (se 2 (by rfl) ⟨2019417, by rfl⟩ : syracuseStep 5385113 = 4038835) B4038835
theorem B3590075 : Blo 2097435 3590075 := bstep (se 1 (by rfl) ⟨2692556, by rfl⟩ : syracuseStep 3590075 = 5385113) B5385113
theorem B2393383 : Blo 2097435 2393383 := bstep (se 1 (by rfl) ⟨1795037, by rfl⟩ : syracuseStep 2393383 = 3590075) B3590075
theorem B3191177 : Blo 2097435 3191177 := bstep (se 2 (by rfl) ⟨1196691, by rfl⟩ : syracuseStep 3191177 = 2393383) B2393383
theorem B2127451 : Blo 2097435 2127451 := bstep (se 1 (by rfl) ⟨1595588, by rfl⟩ : syracuseStep 2127451 = 3191177) B3191177
theorem B2836601 : Blo 2097435 2836601 := bstep (se 2 (by rfl) ⟨1063725, by rfl⟩ : syracuseStep 2836601 = 2127451) B2127451
theorem B30257077 : Blo 2097435 30257077 := bstep (se 5 (by rfl) ⟨1418300, by rfl⟩ : syracuseStep 30257077 = 2836601) B2836601
theorem B40342769 : Blo 2097435 40342769 := bstep (se 2 (by rfl) ⟨15128538, by rfl⟩ : syracuseStep 40342769 = 30257077) B30257077
theorem B26895179 : Blo 2097435 26895179 := bstep (se 1 (by rfl) ⟨20171384, by rfl⟩ : syracuseStep 26895179 = 40342769) B40342769
theorem B17930119 : Blo 2097435 17930119 := bstep (se 1 (by rfl) ⟨13447589, by rfl⟩ : syracuseStep 17930119 = 26895179) B26895179
theorem B23906825 : Blo 2097435 23906825 := bstep (se 2 (by rfl) ⟨8965059, by rfl⟩ : syracuseStep 23906825 = 17930119) B17930119
theorem B15937883 : Blo 2097435 15937883 := bstep (se 1 (by rfl) ⟨11953412, by rfl⟩ : syracuseStep 15937883 = 23906825) B23906825
theorem B10625255 : Blo 2097435 10625255 := bstep (se 1 (by rfl) ⟨7968941, by rfl⟩ : syracuseStep 10625255 = 15937883) B15937883
theorem B7083503 : Blo 2097435 7083503 := bstep (se 1 (by rfl) ⟨5312627, by rfl⟩ : syracuseStep 7083503 = 10625255) B10625255
theorem B4722335 : Blo 2097435 4722335 := bstep (se 1 (by rfl) ⟨3541751, by rfl⟩ : syracuseStep 4722335 = 7083503) B7083503
theorem B3148223 : Blo 2097435 3148223 := bstep (se 1 (by rfl) ⟨2361167, by rfl⟩ : syracuseStep 3148223 = 4722335) B4722335
theorem B2098815 : Blo 2097435 2098815 := bstep (se 1 (by rfl) ⟨1574111, by rfl⟩ : syracuseStep 2098815 = 3148223) B3148223
theorem B3148229 : Blo 2097435 3148229 := bbase (se 4 (by rfl) ⟨295146, by rfl⟩ : syracuseStep 3148229 = 590293) (by norm_num)
theorem B2098819 : Blo 2097435 2098819 := bstep (se 1 (by rfl) ⟨1574114, by rfl⟩ : syracuseStep 2098819 = 3148229) B3148229
theorem B3541765 : Blo 2097435 3541765 := bbase (se 4 (by rfl) ⟨332040, by rfl⟩ : syracuseStep 3541765 = 664081) (by norm_num)
theorem B4722353 : Blo 2097435 4722353 := bstep (se 2 (by rfl) ⟨1770882, by rfl⟩ : syracuseStep 4722353 = 3541765) B3541765
theorem B3148235 : Blo 2097435 3148235 := bstep (se 1 (by rfl) ⟨2361176, by rfl⟩ : syracuseStep 3148235 = 4722353) B4722353
theorem B2098823 : Blo 2097435 2098823 := bstep (se 1 (by rfl) ⟨1574117, by rfl⟩ : syracuseStep 2098823 = 3148235) B3148235
theorem B2361181 : Blo 2097435 2361181 := bbase (se 3 (by rfl) ⟨442721, by rfl⟩ : syracuseStep 2361181 = 885443) (by norm_num)
theorem B3148241 : Blo 2097435 3148241 := bstep (se 2 (by rfl) ⟨1180590, by rfl⟩ : syracuseStep 3148241 = 2361181) B2361181
theorem B2098827 : Blo 2097435 2098827 := bstep (se 1 (by rfl) ⟨1574120, by rfl⟩ : syracuseStep 2098827 = 3148241) B3148241
theorem B7083557 : Blo 2097435 7083557 := bbase (se 4 (by rfl) ⟨664083, by rfl⟩ : syracuseStep 7083557 = 1328167) (by norm_num)
theorem B4722371 : Blo 2097435 4722371 := bstep (se 1 (by rfl) ⟨3541778, by rfl⟩ : syracuseStep 4722371 = 7083557) B7083557
theorem B3148247 : Blo 2097435 3148247 := bstep (se 1 (by rfl) ⟨2361185, by rfl⟩ : syracuseStep 3148247 = 4722371) B4722371
theorem B2098831 : Blo 2097435 2098831 := bstep (se 1 (by rfl) ⟨1574123, by rfl⟩ : syracuseStep 2098831 = 3148247) B3148247
theorem B3148253 : Blo 2097435 3148253 := bbase (se 3 (by rfl) ⟨590297, by rfl⟩ : syracuseStep 3148253 = 1180595) (by norm_num)
theorem B2098835 : Blo 2097435 2098835 := bstep (se 1 (by rfl) ⟨1574126, by rfl⟩ : syracuseStep 2098835 = 3148253) B3148253
theorem B4722389 : Blo 2097435 4722389 := bbase (se 7 (by rfl) ⟨55340, by rfl⟩ : syracuseStep 4722389 = 110681) (by norm_num)
theorem B3148259 : Blo 2097435 3148259 := bstep (se 1 (by rfl) ⟨2361194, by rfl⟩ : syracuseStep 3148259 = 4722389) B4722389
theorem B2098839 : Blo 2097435 2098839 := bstep (se 1 (by rfl) ⟨1574129, by rfl⟩ : syracuseStep 2098839 = 3148259) B3148259
theorem B7564373 : Blo 2097435 7564373 := bbase (se 8 (by rfl) ⟨44322, by rfl⟩ : syracuseStep 7564373 = 88645) (by norm_num)
theorem B5042915 : Blo 2097435 5042915 := bstep (se 1 (by rfl) ⟨3782186, by rfl⟩ : syracuseStep 5042915 = 7564373) B7564373
theorem B3361943 : Blo 2097435 3361943 := bstep (se 1 (by rfl) ⟨2521457, by rfl⟩ : syracuseStep 3361943 = 5042915) B5042915
theorem B8965181 : Blo 2097435 8965181 := bstep (se 3 (by rfl) ⟨1680971, by rfl⟩ : syracuseStep 8965181 = 3361943) B3361943
theorem B5976787 : Blo 2097435 5976787 := bstep (se 1 (by rfl) ⟨4482590, by rfl⟩ : syracuseStep 5976787 = 8965181) B8965181
theorem B7969049 : Blo 2097435 7969049 := bstep (se 2 (by rfl) ⟨2988393, by rfl⟩ : syracuseStep 7969049 = 5976787) B5976787
theorem B5312699 : Blo 2097435 5312699 := bstep (se 1 (by rfl) ⟨3984524, by rfl⟩ : syracuseStep 5312699 = 7969049) B7969049
theorem B3541799 : Blo 2097435 3541799 := bstep (se 1 (by rfl) ⟨2656349, by rfl⟩ : syracuseStep 3541799 = 5312699) B5312699
theorem B2361199 : Blo 2097435 2361199 := bstep (se 1 (by rfl) ⟨1770899, by rfl⟩ : syracuseStep 2361199 = 3541799) B3541799
theorem B3148265 : Blo 2097435 3148265 := bstep (se 2 (by rfl) ⟨1180599, by rfl⟩ : syracuseStep 3148265 = 2361199) B2361199
theorem B2098843 : Blo 2097435 2098843 := bstep (se 1 (by rfl) ⟨1574132, by rfl⟩ : syracuseStep 2098843 = 3148265) B3148265
theorem B2692597 : Blo 2097435 2692597 := bbase (se 5 (by rfl) ⟨126215, by rfl⟩ : syracuseStep 2692597 = 252431) (by norm_num)
theorem B3590129 : Blo 2097435 3590129 := bstep (se 2 (by rfl) ⟨1346298, by rfl⟩ : syracuseStep 3590129 = 2692597) B2692597
theorem B9573677 : Blo 2097435 9573677 := bstep (se 3 (by rfl) ⟨1795064, by rfl⟩ : syracuseStep 9573677 = 3590129) B3590129
theorem B6382451 : Blo 2097435 6382451 := bstep (se 1 (by rfl) ⟨4786838, by rfl⟩ : syracuseStep 6382451 = 9573677) B9573677
theorem B4254967 : Blo 2097435 4254967 := bstep (se 1 (by rfl) ⟨3191225, by rfl⟩ : syracuseStep 4254967 = 6382451) B6382451
theorem B5673289 : Blo 2097435 5673289 := bstep (se 2 (by rfl) ⟨2127483, by rfl⟩ : syracuseStep 5673289 = 4254967) B4254967
theorem B7564385 : Blo 2097435 7564385 := bstep (se 2 (by rfl) ⟨2836644, by rfl⟩ : syracuseStep 7564385 = 5673289) B5673289
theorem B20171693 : Blo 2097435 20171693 := bstep (se 3 (by rfl) ⟨3782192, by rfl⟩ : syracuseStep 20171693 = 7564385) B7564385
theorem B13447795 : Blo 2097435 13447795 := bstep (se 1 (by rfl) ⟨10085846, by rfl⟩ : syracuseStep 13447795 = 20171693) B20171693
theorem B17930393 : Blo 2097435 17930393 := bstep (se 2 (by rfl) ⟨6723897, by rfl⟩ : syracuseStep 17930393 = 13447795) B13447795
theorem B11953595 : Blo 2097435 11953595 := bstep (se 1 (by rfl) ⟨8965196, by rfl⟩ : syracuseStep 11953595 = 17930393) B17930393
theorem B7969063 : Blo 2097435 7969063 := bstep (se 1 (by rfl) ⟨5976797, by rfl⟩ : syracuseStep 7969063 = 11953595) B11953595
theorem B10625417 : Blo 2097435 10625417 := bstep (se 2 (by rfl) ⟨3984531, by rfl⟩ : syracuseStep 10625417 = 7969063) B7969063
theorem B7083611 : Blo 2097435 7083611 := bstep (se 1 (by rfl) ⟨5312708, by rfl⟩ : syracuseStep 7083611 = 10625417) B10625417
theorem B4722407 : Blo 2097435 4722407 := bstep (se 1 (by rfl) ⟨3541805, by rfl⟩ : syracuseStep 4722407 = 7083611) B7083611
theorem B3148271 : Blo 2097435 3148271 := bstep (se 1 (by rfl) ⟨2361203, by rfl⟩ : syracuseStep 3148271 = 4722407) B4722407
theorem B2098847 : Blo 2097435 2098847 := bstep (se 1 (by rfl) ⟨1574135, by rfl⟩ : syracuseStep 2098847 = 3148271) B3148271
theorem B3148277 : Blo 2097435 3148277 := bbase (se 5 (by rfl) ⟨147575, by rfl⟩ : syracuseStep 3148277 = 295151) (by norm_num)
theorem B2098851 : Blo 2097435 2098851 := bstep (se 1 (by rfl) ⟨1574138, by rfl⟩ : syracuseStep 2098851 = 3148277) B3148277
theorem B5976821 : Blo 2097435 5976821 := bbase (se 5 (by rfl) ⟨280163, by rfl⟩ : syracuseStep 5976821 = 560327) (by norm_num)
theorem B3984547 : Blo 2097435 3984547 := bstep (se 1 (by rfl) ⟨2988410, by rfl⟩ : syracuseStep 3984547 = 5976821) B5976821
theorem B5312729 : Blo 2097435 5312729 := bstep (se 2 (by rfl) ⟨1992273, by rfl⟩ : syracuseStep 5312729 = 3984547) B3984547
theorem B3541819 : Blo 2097435 3541819 := bstep (se 1 (by rfl) ⟨2656364, by rfl⟩ : syracuseStep 3541819 = 5312729) B5312729
theorem B4722425 : Blo 2097435 4722425 := bstep (se 2 (by rfl) ⟨1770909, by rfl⟩ : syracuseStep 4722425 = 3541819) B3541819
theorem B3148283 : Blo 2097435 3148283 := bstep (se 1 (by rfl) ⟨2361212, by rfl⟩ : syracuseStep 3148283 = 4722425) B4722425
theorem B2098855 : Blo 2097435 2098855 := bstep (se 1 (by rfl) ⟨1574141, by rfl⟩ : syracuseStep 2098855 = 3148283) B3148283
theorem B2361217 : Blo 2097435 2361217 := bbase (se 2 (by rfl) ⟨885456, by rfl⟩ : syracuseStep 2361217 = 1770913) (by norm_num)
theorem B3148289 : Blo 2097435 3148289 := bstep (se 2 (by rfl) ⟨1180608, by rfl⟩ : syracuseStep 3148289 = 2361217) B2361217
theorem B2098859 : Blo 2097435 2098859 := bstep (se 1 (by rfl) ⟨1574144, by rfl⟩ : syracuseStep 2098859 = 3148289) B3148289
theorem B5312749 : Blo 2097435 5312749 := bbase (se 3 (by rfl) ⟨996140, by rfl⟩ : syracuseStep 5312749 = 1992281) (by norm_num)
theorem B7083665 : Blo 2097435 7083665 := bstep (se 2 (by rfl) ⟨2656374, by rfl⟩ : syracuseStep 7083665 = 5312749) B5312749
theorem B4722443 : Blo 2097435 4722443 := bstep (se 1 (by rfl) ⟨3541832, by rfl⟩ : syracuseStep 4722443 = 7083665) B7083665
theorem B3148295 : Blo 2097435 3148295 := bstep (se 1 (by rfl) ⟨2361221, by rfl⟩ : syracuseStep 3148295 = 4722443) B4722443
theorem B2098863 : Blo 2097435 2098863 := bstep (se 1 (by rfl) ⟨1574147, by rfl⟩ : syracuseStep 2098863 = 3148295) B3148295
theorem B3148301 : Blo 2097435 3148301 := bbase (se 3 (by rfl) ⟨590306, by rfl⟩ : syracuseStep 3148301 = 1180613) (by norm_num)
theorem B2098867 : Blo 2097435 2098867 := bstep (se 1 (by rfl) ⟨1574150, by rfl⟩ : syracuseStep 2098867 = 3148301) B3148301
theorem B4722461 : Blo 2097435 4722461 := bbase (se 3 (by rfl) ⟨885461, by rfl⟩ : syracuseStep 4722461 = 1770923) (by norm_num)
theorem B3148307 : Blo 2097435 3148307 := bstep (se 1 (by rfl) ⟨2361230, by rfl⟩ : syracuseStep 3148307 = 4722461) B4722461
theorem B2098871 : Blo 2097435 2098871 := bstep (se 1 (by rfl) ⟨1574153, by rfl⟩ : syracuseStep 2098871 = 3148307) B3148307
theorem B3541853 : Blo 2097435 3541853 := bbase (se 3 (by rfl) ⟨664097, by rfl⟩ : syracuseStep 3541853 = 1328195) (by norm_num)
theorem B2361235 : Blo 2097435 2361235 := bstep (se 1 (by rfl) ⟨1770926, by rfl⟩ : syracuseStep 2361235 = 3541853) B3541853
theorem B3148313 : Blo 2097435 3148313 := bstep (se 2 (by rfl) ⟨1180617, by rfl⟩ : syracuseStep 3148313 = 2361235) B2361235
theorem B2098875 : Blo 2097435 2098875 := bstep (se 1 (by rfl) ⟨1574156, by rfl⟩ : syracuseStep 2098875 = 3148313) B3148313
theorem B8965333 : Blo 2097435 8965333 := bbase (se 7 (by rfl) ⟨105062, by rfl⟩ : syracuseStep 8965333 = 210125) (by norm_num)
theorem B11953777 : Blo 2097435 11953777 := bstep (se 2 (by rfl) ⟨4482666, by rfl⟩ : syracuseStep 11953777 = 8965333) B8965333
theorem B15938369 : Blo 2097435 15938369 := bstep (se 2 (by rfl) ⟨5976888, by rfl⟩ : syracuseStep 15938369 = 11953777) B11953777
theorem B10625579 : Blo 2097435 10625579 := bstep (se 1 (by rfl) ⟨7969184, by rfl⟩ : syracuseStep 10625579 = 15938369) B15938369
theorem B7083719 : Blo 2097435 7083719 := bstep (se 1 (by rfl) ⟨5312789, by rfl⟩ : syracuseStep 7083719 = 10625579) B10625579
theorem B4722479 : Blo 2097435 4722479 := bstep (se 1 (by rfl) ⟨3541859, by rfl⟩ : syracuseStep 4722479 = 7083719) B7083719
theorem B3148319 : Blo 2097435 3148319 := bstep (se 1 (by rfl) ⟨2361239, by rfl⟩ : syracuseStep 3148319 = 4722479) B4722479
theorem B2098879 : Blo 2097435 2098879 := bstep (se 1 (by rfl) ⟨1574159, by rfl⟩ : syracuseStep 2098879 = 3148319) B3148319
theorem B3148325 : Blo 2097435 3148325 := bbase (se 4 (by rfl) ⟨295155, by rfl⟩ : syracuseStep 3148325 = 590311) (by norm_num)
theorem B2098883 : Blo 2097435 2098883 := bstep (se 1 (by rfl) ⟨1574162, by rfl⟩ : syracuseStep 2098883 = 3148325) B3148325
theorem B2656405 : Blo 2097435 2656405 := bbase (se 6 (by rfl) ⟨62259, by rfl⟩ : syracuseStep 2656405 = 124519) (by norm_num)
theorem B3541873 : Blo 2097435 3541873 := bstep (se 2 (by rfl) ⟨1328202, by rfl⟩ : syracuseStep 3541873 = 2656405) B2656405
theorem B4722497 : Blo 2097435 4722497 := bstep (se 2 (by rfl) ⟨1770936, by rfl⟩ : syracuseStep 4722497 = 3541873) B3541873
theorem B3148331 : Blo 2097435 3148331 := bstep (se 1 (by rfl) ⟨2361248, by rfl⟩ : syracuseStep 3148331 = 4722497) B4722497
theorem B2098887 : Blo 2097435 2098887 := bstep (se 1 (by rfl) ⟨1574165, by rfl⟩ : syracuseStep 2098887 = 3148331) B3148331
theorem B2361253 : Blo 2097435 2361253 := bbase (se 4 (by rfl) ⟨221367, by rfl⟩ : syracuseStep 2361253 = 442735) (by norm_num)
theorem B3148337 : Blo 2097435 3148337 := bstep (se 2 (by rfl) ⟨1180626, by rfl⟩ : syracuseStep 3148337 = 2361253) B2361253
theorem B2098891 : Blo 2097435 2098891 := bstep (se 1 (by rfl) ⟨1574168, by rfl⟩ : syracuseStep 2098891 = 3148337) B3148337
theorem B18175445 : Blo 2097435 18175445 := bbase (se 7 (by rfl) ⟨212993, by rfl⟩ : syracuseStep 18175445 = 425987) (by norm_num)
theorem B12116963 : Blo 2097435 12116963 := bstep (se 1 (by rfl) ⟨9087722, by rfl⟩ : syracuseStep 12116963 = 18175445) B18175445
theorem B8077975 : Blo 2097435 8077975 := bstep (se 1 (by rfl) ⟨6058481, by rfl⟩ : syracuseStep 8077975 = 12116963) B12116963
theorem B43082533 : Blo 2097435 43082533 := bstep (se 4 (by rfl) ⟨4038987, by rfl⟩ : syracuseStep 43082533 = 8077975) B8077975
theorem B57443377 : Blo 2097435 57443377 := bstep (se 2 (by rfl) ⟨21541266, by rfl⟩ : syracuseStep 57443377 = 43082533) B43082533
theorem B76591169 : Blo 2097435 76591169 := bstep (se 2 (by rfl) ⟨28721688, by rfl⟩ : syracuseStep 76591169 = 57443377) B57443377
theorem B51060779 : Blo 2097435 51060779 := bstep (se 1 (by rfl) ⟨38295584, by rfl⟩ : syracuseStep 51060779 = 76591169) B76591169
theorem B34040519 : Blo 2097435 34040519 := bstep (se 1 (by rfl) ⟨25530389, by rfl⟩ : syracuseStep 34040519 = 51060779) B51060779
theorem B22693679 : Blo 2097435 22693679 := bstep (se 1 (by rfl) ⟨17020259, by rfl⟩ : syracuseStep 22693679 = 34040519) B34040519
theorem B15129119 : Blo 2097435 15129119 := bstep (se 1 (by rfl) ⟨11346839, by rfl⟩ : syracuseStep 15129119 = 22693679) B22693679
theorem B10086079 : Blo 2097435 10086079 := bstep (se 1 (by rfl) ⟨7564559, by rfl⟩ : syracuseStep 10086079 = 15129119) B15129119
theorem B13448105 : Blo 2097435 13448105 := bstep (se 2 (by rfl) ⟨5043039, by rfl⟩ : syracuseStep 13448105 = 10086079) B10086079
theorem B8965403 : Blo 2097435 8965403 := bstep (se 1 (by rfl) ⟨6724052, by rfl⟩ : syracuseStep 8965403 = 13448105) B13448105
theorem B5976935 : Blo 2097435 5976935 := bstep (se 1 (by rfl) ⟨4482701, by rfl⟩ : syracuseStep 5976935 = 8965403) B8965403
theorem B3984623 : Blo 2097435 3984623 := bstep (se 1 (by rfl) ⟨2988467, by rfl⟩ : syracuseStep 3984623 = 5976935) B5976935
theorem B2656415 : Blo 2097435 2656415 := bstep (se 1 (by rfl) ⟨1992311, by rfl⟩ : syracuseStep 2656415 = 3984623) B3984623
theorem B7083773 : Blo 2097435 7083773 := bstep (se 3 (by rfl) ⟨1328207, by rfl⟩ : syracuseStep 7083773 = 2656415) B2656415
theorem B4722515 : Blo 2097435 4722515 := bstep (se 1 (by rfl) ⟨3541886, by rfl⟩ : syracuseStep 4722515 = 7083773) B7083773
theorem B3148343 : Blo 2097435 3148343 := bstep (se 1 (by rfl) ⟨2361257, by rfl⟩ : syracuseStep 3148343 = 4722515) B4722515
theorem B2098895 : Blo 2097435 2098895 := bstep (se 1 (by rfl) ⟨1574171, by rfl⟩ : syracuseStep 2098895 = 3148343) B3148343
theorem B3148349 : Blo 2097435 3148349 := bbase (se 3 (by rfl) ⟨590315, by rfl⟩ : syracuseStep 3148349 = 1180631) (by norm_num)
theorem B2098899 : Blo 2097435 2098899 := bstep (se 1 (by rfl) ⟨1574174, by rfl⟩ : syracuseStep 2098899 = 3148349) B3148349
theorem B4722533 : Blo 2097435 4722533 := bbase (se 4 (by rfl) ⟨442737, by rfl⟩ : syracuseStep 4722533 = 885475) (by norm_num)
theorem B3148355 : Blo 2097435 3148355 := bstep (se 1 (by rfl) ⟨2361266, by rfl⟩ : syracuseStep 3148355 = 4722533) B4722533
theorem B2098903 : Blo 2097435 2098903 := bstep (se 1 (by rfl) ⟨1574177, by rfl⟩ : syracuseStep 2098903 = 3148355) B3148355
theorem B5312861 : Blo 2097435 5312861 := bbase (se 3 (by rfl) ⟨996161, by rfl⟩ : syracuseStep 5312861 = 1992323) (by norm_num)
theorem B3541907 : Blo 2097435 3541907 := bstep (se 1 (by rfl) ⟨2656430, by rfl⟩ : syracuseStep 3541907 = 5312861) B5312861
theorem B2361271 : Blo 2097435 2361271 := bstep (se 1 (by rfl) ⟨1770953, by rfl⟩ : syracuseStep 2361271 = 3541907) B3541907
theorem B3148361 : Blo 2097435 3148361 := bstep (se 2 (by rfl) ⟨1180635, by rfl⟩ : syracuseStep 3148361 = 2361271) B2361271
theorem B2098907 : Blo 2097435 2098907 := bstep (se 1 (by rfl) ⟨1574180, by rfl⟩ : syracuseStep 2098907 = 3148361) B3148361
theorem B3984653 : Blo 2097435 3984653 := bbase (se 3 (by rfl) ⟨747122, by rfl⟩ : syracuseStep 3984653 = 1494245) (by norm_num)
theorem B10625741 : Blo 2097435 10625741 := bstep (se 3 (by rfl) ⟨1992326, by rfl⟩ : syracuseStep 10625741 = 3984653) B3984653
theorem B7083827 : Blo 2097435 7083827 := bstep (se 1 (by rfl) ⟨5312870, by rfl⟩ : syracuseStep 7083827 = 10625741) B10625741
theorem B4722551 : Blo 2097435 4722551 := bstep (se 1 (by rfl) ⟨3541913, by rfl⟩ : syracuseStep 4722551 = 7083827) B7083827
theorem B3148367 : Blo 2097435 3148367 := bstep (se 1 (by rfl) ⟨2361275, by rfl⟩ : syracuseStep 3148367 = 4722551) B4722551
theorem B2098911 : Blo 2097435 2098911 := bstep (se 1 (by rfl) ⟨1574183, by rfl⟩ : syracuseStep 2098911 = 3148367) B3148367
theorem B3148373 : Blo 2097435 3148373 := bbase (se 8 (by rfl) ⟨18447, by rfl⟩ : syracuseStep 3148373 = 36895) (by norm_num)
theorem B2098915 : Blo 2097435 2098915 := bstep (se 1 (by rfl) ⟨1574186, by rfl⟩ : syracuseStep 2098915 = 3148373) B3148373
theorem B2127557 : Blo 2097435 2127557 := bbase (se 4 (by rfl) ⟨199458, by rfl⟩ : syracuseStep 2127557 = 398917) (by norm_num)
theorem B5673485 : Blo 2097435 5673485 := bstep (se 3 (by rfl) ⟨1063778, by rfl⟩ : syracuseStep 5673485 = 2127557) B2127557
theorem B3782323 : Blo 2097435 3782323 := bstep (se 1 (by rfl) ⟨2836742, by rfl⟩ : syracuseStep 3782323 = 5673485) B5673485
theorem B5043097 : Blo 2097435 5043097 := bstep (se 2 (by rfl) ⟨1891161, by rfl⟩ : syracuseStep 5043097 = 3782323) B3782323
theorem B6724129 : Blo 2097435 6724129 := bstep (se 2 (by rfl) ⟨2521548, by rfl⟩ : syracuseStep 6724129 = 5043097) B5043097
theorem B8965505 : Blo 2097435 8965505 := bstep (se 2 (by rfl) ⟨3362064, by rfl⟩ : syracuseStep 8965505 = 6724129) B6724129
theorem B5977003 : Blo 2097435 5977003 := bstep (se 1 (by rfl) ⟨4482752, by rfl⟩ : syracuseStep 5977003 = 8965505) B8965505
theorem B7969337 : Blo 2097435 7969337 := bstep (se 2 (by rfl) ⟨2988501, by rfl⟩ : syracuseStep 7969337 = 5977003) B5977003
theorem B5312891 : Blo 2097435 5312891 := bstep (se 1 (by rfl) ⟨3984668, by rfl⟩ : syracuseStep 5312891 = 7969337) B7969337
theorem B3541927 : Blo 2097435 3541927 := bstep (se 1 (by rfl) ⟨2656445, by rfl⟩ : syracuseStep 3541927 = 5312891) B5312891
theorem B4722569 : Blo 2097435 4722569 := bstep (se 2 (by rfl) ⟨1770963, by rfl⟩ : syracuseStep 4722569 = 3541927) B3541927
theorem B3148379 : Blo 2097435 3148379 := bstep (se 1 (by rfl) ⟨2361284, by rfl⟩ : syracuseStep 3148379 = 4722569) B4722569
theorem B2098919 : Blo 2097435 2098919 := bstep (se 1 (by rfl) ⟨1574189, by rfl⟩ : syracuseStep 2098919 = 3148379) B3148379
theorem B2361289 : Blo 2097435 2361289 := bbase (se 2 (by rfl) ⟨885483, by rfl⟩ : syracuseStep 2361289 = 1770967) (by norm_num)
theorem B3148385 : Blo 2097435 3148385 := bstep (se 2 (by rfl) ⟨1180644, by rfl⟩ : syracuseStep 3148385 = 2361289) B2361289
theorem B2098923 : Blo 2097435 2098923 := bstep (se 1 (by rfl) ⟨1574192, by rfl⟩ : syracuseStep 2098923 = 3148385) B3148385
theorem B3362077 : Blo 2097435 3362077 := bbase (se 3 (by rfl) ⟨630389, by rfl⟩ : syracuseStep 3362077 = 1260779) (by norm_num)
theorem B17931077 : Blo 2097435 17931077 := bstep (se 4 (by rfl) ⟨1681038, by rfl⟩ : syracuseStep 17931077 = 3362077) B3362077
theorem B11954051 : Blo 2097435 11954051 := bstep (se 1 (by rfl) ⟨8965538, by rfl⟩ : syracuseStep 11954051 = 17931077) B17931077
theorem B7969367 : Blo 2097435 7969367 := bstep (se 1 (by rfl) ⟨5977025, by rfl⟩ : syracuseStep 7969367 = 11954051) B11954051
theorem B5312911 : Blo 2097435 5312911 := bstep (se 1 (by rfl) ⟨3984683, by rfl⟩ : syracuseStep 5312911 = 7969367) B7969367
theorem B7083881 : Blo 2097435 7083881 := bstep (se 2 (by rfl) ⟨2656455, by rfl⟩ : syracuseStep 7083881 = 5312911) B5312911
theorem B4722587 : Blo 2097435 4722587 := bstep (se 1 (by rfl) ⟨3541940, by rfl⟩ : syracuseStep 4722587 = 7083881) B7083881
theorem B3148391 : Blo 2097435 3148391 := bstep (se 1 (by rfl) ⟨2361293, by rfl⟩ : syracuseStep 3148391 = 4722587) B4722587
theorem B2098927 : Blo 2097435 2098927 := bstep (se 1 (by rfl) ⟨1574195, by rfl⟩ : syracuseStep 2098927 = 3148391) B3148391
theorem B3148397 : Blo 2097435 3148397 := bbase (se 3 (by rfl) ⟨590324, by rfl⟩ : syracuseStep 3148397 = 1180649) (by norm_num)
theorem B2098931 : Blo 2097435 2098931 := bstep (se 1 (by rfl) ⟨1574198, by rfl⟩ : syracuseStep 2098931 = 3148397) B3148397
theorem B4722605 : Blo 2097435 4722605 := bbase (se 3 (by rfl) ⟨885488, by rfl⟩ : syracuseStep 4722605 = 1770977) (by norm_num)
theorem B3148403 : Blo 2097435 3148403 := bstep (se 1 (by rfl) ⟨2361302, by rfl⟩ : syracuseStep 3148403 = 4722605) B4722605
theorem B2098935 : Blo 2097435 2098935 := bstep (se 1 (by rfl) ⟨1574201, by rfl⟩ : syracuseStep 2098935 = 3148403) B3148403
theorem B5977061 : Blo 2097435 5977061 := bbase (se 4 (by rfl) ⟨560349, by rfl⟩ : syracuseStep 5977061 = 1120699) (by norm_num)
theorem B3984707 : Blo 2097435 3984707 := bstep (se 1 (by rfl) ⟨2988530, by rfl⟩ : syracuseStep 3984707 = 5977061) B5977061
theorem B2656471 : Blo 2097435 2656471 := bstep (se 1 (by rfl) ⟨1992353, by rfl⟩ : syracuseStep 2656471 = 3984707) B3984707
theorem B3541961 : Blo 2097435 3541961 := bstep (se 2 (by rfl) ⟨1328235, by rfl⟩ : syracuseStep 3541961 = 2656471) B2656471
theorem B2361307 : Blo 2097435 2361307 := bstep (se 1 (by rfl) ⟨1770980, by rfl⟩ : syracuseStep 2361307 = 3541961) B3541961
theorem B3148409 : Blo 2097435 3148409 := bstep (se 2 (by rfl) ⟨1180653, by rfl⟩ : syracuseStep 3148409 = 2361307) B2361307
theorem B2098939 : Blo 2097435 2098939 := bstep (se 1 (by rfl) ⟨1574204, by rfl⟩ : syracuseStep 2098939 = 3148409) B3148409
theorem B15129461 : Blo 2097435 15129461 := bbase (se 5 (by rfl) ⟨709193, by rfl⟩ : syracuseStep 15129461 = 1418387) (by norm_num)
theorem B40345229 : Blo 2097435 40345229 := bstep (se 3 (by rfl) ⟨7564730, by rfl⟩ : syracuseStep 40345229 = 15129461) B15129461
theorem B26896819 : Blo 2097435 26896819 := bstep (se 1 (by rfl) ⟨20172614, by rfl⟩ : syracuseStep 26896819 = 40345229) B40345229
theorem B35862425 : Blo 2097435 35862425 := bstep (se 2 (by rfl) ⟨13448409, by rfl⟩ : syracuseStep 35862425 = 26896819) B26896819
theorem B23908283 : Blo 2097435 23908283 := bstep (se 1 (by rfl) ⟨17931212, by rfl⟩ : syracuseStep 23908283 = 35862425) B35862425
theorem B15938855 : Blo 2097435 15938855 := bstep (se 1 (by rfl) ⟨11954141, by rfl⟩ : syracuseStep 15938855 = 23908283) B23908283
theorem B10625903 : Blo 2097435 10625903 := bstep (se 1 (by rfl) ⟨7969427, by rfl⟩ : syracuseStep 10625903 = 15938855) B15938855
theorem B7083935 : Blo 2097435 7083935 := bstep (se 1 (by rfl) ⟨5312951, by rfl⟩ : syracuseStep 7083935 = 10625903) B10625903
theorem B4722623 : Blo 2097435 4722623 := bstep (se 1 (by rfl) ⟨3541967, by rfl⟩ : syracuseStep 4722623 = 7083935) B7083935
theorem B3148415 : Blo 2097435 3148415 := bstep (se 1 (by rfl) ⟨2361311, by rfl⟩ : syracuseStep 3148415 = 4722623) B4722623
theorem B2098943 : Blo 2097435 2098943 := bstep (se 1 (by rfl) ⟨1574207, by rfl⟩ : syracuseStep 2098943 = 3148415) B3148415
theorem B3148421 : Blo 2097435 3148421 := bbase (se 4 (by rfl) ⟨295164, by rfl⟩ : syracuseStep 3148421 = 590329) (by norm_num)
theorem B2098947 : Blo 2097435 2098947 := bstep (se 1 (by rfl) ⟨1574210, by rfl⟩ : syracuseStep 2098947 = 3148421) B3148421
theorem B3541981 : Blo 2097435 3541981 := bbase (se 3 (by rfl) ⟨664121, by rfl⟩ : syracuseStep 3541981 = 1328243) (by norm_num)
theorem B4722641 : Blo 2097435 4722641 := bstep (se 2 (by rfl) ⟨1770990, by rfl⟩ : syracuseStep 4722641 = 3541981) B3541981
theorem B3148427 : Blo 2097435 3148427 := bstep (se 1 (by rfl) ⟨2361320, by rfl⟩ : syracuseStep 3148427 = 4722641) B4722641
theorem B2098951 : Blo 2097435 2098951 := bstep (se 1 (by rfl) ⟨1574213, by rfl⟩ : syracuseStep 2098951 = 3148427) B3148427
theorem B2361325 : Blo 2097435 2361325 := bbase (se 3 (by rfl) ⟨442748, by rfl⟩ : syracuseStep 2361325 = 885497) (by norm_num)
theorem B3148433 : Blo 2097435 3148433 := bstep (se 2 (by rfl) ⟨1180662, by rfl⟩ : syracuseStep 3148433 = 2361325) B2361325
theorem B2098955 : Blo 2097435 2098955 := bstep (se 1 (by rfl) ⟨1574216, by rfl⟩ : syracuseStep 2098955 = 3148433) B3148433
theorem B7083989 : Blo 2097435 7083989 := bbase (se 7 (by rfl) ⟨83015, by rfl⟩ : syracuseStep 7083989 = 166031) (by norm_num)
theorem B4722659 : Blo 2097435 4722659 := bstep (se 1 (by rfl) ⟨3541994, by rfl⟩ : syracuseStep 4722659 = 7083989) B7083989
theorem B3148439 : Blo 2097435 3148439 := bstep (se 1 (by rfl) ⟨2361329, by rfl⟩ : syracuseStep 3148439 = 4722659) B4722659
theorem B2098959 : Blo 2097435 2098959 := bstep (se 1 (by rfl) ⟨1574219, by rfl⟩ : syracuseStep 2098959 = 3148439) B3148439
theorem B3148445 : Blo 2097435 3148445 := bbase (se 3 (by rfl) ⟨590333, by rfl⟩ : syracuseStep 3148445 = 1180667) (by norm_num)
theorem B2098963 : Blo 2097435 2098963 := bstep (se 1 (by rfl) ⟨1574222, by rfl⟩ : syracuseStep 2098963 = 3148445) B3148445
theorem B4722677 : Blo 2097435 4722677 := bbase (se 5 (by rfl) ⟨221375, by rfl⟩ : syracuseStep 4722677 = 442751) (by norm_num)
theorem B3148451 : Blo 2097435 3148451 := bstep (se 1 (by rfl) ⟨2361338, by rfl⟩ : syracuseStep 3148451 = 4722677) B4722677
theorem B2098967 : Blo 2097435 2098967 := bstep (se 1 (by rfl) ⟨1574225, by rfl⟩ : syracuseStep 2098967 = 3148451) B3148451
theorem B64626133 : Blo 2097435 64626133 := bbase (se 7 (by rfl) ⟨757337, by rfl⟩ : syracuseStep 64626133 = 1514675) (by norm_num)
theorem B86168177 : Blo 2097435 86168177 := bstep (se 2 (by rfl) ⟨32313066, by rfl⟩ : syracuseStep 86168177 = 64626133) B64626133
theorem B57445451 : Blo 2097435 57445451 := bstep (se 1 (by rfl) ⟨43084088, by rfl⟩ : syracuseStep 57445451 = 86168177) B86168177
theorem B38296967 : Blo 2097435 38296967 := bstep (se 1 (by rfl) ⟨28722725, by rfl⟩ : syracuseStep 38296967 = 57445451) B57445451
theorem B102125245 : Blo 2097435 102125245 := bstep (se 3 (by rfl) ⟨19148483, by rfl⟩ : syracuseStep 102125245 = 38296967) B38296967
theorem B136166993 : Blo 2097435 136166993 := bstep (se 2 (by rfl) ⟨51062622, by rfl⟩ : syracuseStep 136166993 = 102125245) B102125245
theorem B90777995 : Blo 2097435 90777995 := bstep (se 1 (by rfl) ⟨68083496, by rfl⟩ : syracuseStep 90777995 = 136166993) B136166993
theorem B60518663 : Blo 2097435 60518663 := bstep (se 1 (by rfl) ⟨45388997, by rfl⟩ : syracuseStep 60518663 = 90777995) B90777995
theorem B40345775 : Blo 2097435 40345775 := bstep (se 1 (by rfl) ⟨30259331, by rfl⟩ : syracuseStep 40345775 = 60518663) B60518663
theorem B26897183 : Blo 2097435 26897183 := bstep (se 1 (by rfl) ⟨20172887, by rfl⟩ : syracuseStep 26897183 = 40345775) B40345775
theorem B17931455 : Blo 2097435 17931455 := bstep (se 1 (by rfl) ⟨13448591, by rfl⟩ : syracuseStep 17931455 = 26897183) B26897183
theorem B11954303 : Blo 2097435 11954303 := bstep (se 1 (by rfl) ⟨8965727, by rfl⟩ : syracuseStep 11954303 = 17931455) B17931455
theorem B7969535 : Blo 2097435 7969535 := bstep (se 1 (by rfl) ⟨5977151, by rfl⟩ : syracuseStep 7969535 = 11954303) B11954303
theorem B5313023 : Blo 2097435 5313023 := bstep (se 1 (by rfl) ⟨3984767, by rfl⟩ : syracuseStep 5313023 = 7969535) B7969535
theorem B3542015 : Blo 2097435 3542015 := bstep (se 1 (by rfl) ⟨2656511, by rfl⟩ : syracuseStep 3542015 = 5313023) B5313023
theorem B2361343 : Blo 2097435 2361343 := bstep (se 1 (by rfl) ⟨1771007, by rfl⟩ : syracuseStep 2361343 = 3542015) B3542015
theorem B3148457 : Blo 2097435 3148457 := bstep (se 2 (by rfl) ⟨1180671, by rfl⟩ : syracuseStep 3148457 = 2361343) B2361343
theorem B2098971 : Blo 2097435 2098971 := bstep (se 1 (by rfl) ⟨1574228, by rfl⟩ : syracuseStep 2098971 = 3148457) B3148457
theorem B2988581 : Blo 2097435 2988581 := bbase (se 4 (by rfl) ⟨280179, by rfl⟩ : syracuseStep 2988581 = 560359) (by norm_num)
theorem B7969549 : Blo 2097435 7969549 := bstep (se 3 (by rfl) ⟨1494290, by rfl⟩ : syracuseStep 7969549 = 2988581) B2988581
theorem B10626065 : Blo 2097435 10626065 := bstep (se 2 (by rfl) ⟨3984774, by rfl⟩ : syracuseStep 10626065 = 7969549) B7969549
theorem B7084043 : Blo 2097435 7084043 := bstep (se 1 (by rfl) ⟨5313032, by rfl⟩ : syracuseStep 7084043 = 10626065) B10626065
theorem B4722695 : Blo 2097435 4722695 := bstep (se 1 (by rfl) ⟨3542021, by rfl⟩ : syracuseStep 4722695 = 7084043) B7084043
theorem B3148463 : Blo 2097435 3148463 := bstep (se 1 (by rfl) ⟨2361347, by rfl⟩ : syracuseStep 3148463 = 4722695) B4722695
theorem B2098975 : Blo 2097435 2098975 := bstep (se 1 (by rfl) ⟨1574231, by rfl⟩ : syracuseStep 2098975 = 3148463) B3148463
theorem B3148469 : Blo 2097435 3148469 := bbase (se 5 (by rfl) ⟨147584, by rfl⟩ : syracuseStep 3148469 = 295169) (by norm_num)
theorem B2098979 : Blo 2097435 2098979 := bstep (se 1 (by rfl) ⟨1574234, by rfl⟩ : syracuseStep 2098979 = 3148469) B3148469
theorem B5313053 : Blo 2097435 5313053 := bbase (se 3 (by rfl) ⟨996197, by rfl⟩ : syracuseStep 5313053 = 1992395) (by norm_num)
theorem B3542035 : Blo 2097435 3542035 := bstep (se 1 (by rfl) ⟨2656526, by rfl⟩ : syracuseStep 3542035 = 5313053) B5313053
theorem B4722713 : Blo 2097435 4722713 := bstep (se 2 (by rfl) ⟨1771017, by rfl⟩ : syracuseStep 4722713 = 3542035) B3542035
theorem B3148475 : Blo 2097435 3148475 := bstep (se 1 (by rfl) ⟨2361356, by rfl⟩ : syracuseStep 3148475 = 4722713) B4722713
theorem B2098983 : Blo 2097435 2098983 := bstep (se 1 (by rfl) ⟨1574237, by rfl⟩ : syracuseStep 2098983 = 3148475) B3148475
theorem B2361361 : Blo 2097435 2361361 := bbase (se 2 (by rfl) ⟨885510, by rfl⟩ : syracuseStep 2361361 = 1771021) (by norm_num)
theorem B3148481 : Blo 2097435 3148481 := bstep (se 2 (by rfl) ⟨1180680, by rfl⟩ : syracuseStep 3148481 = 2361361) B2361361
theorem B2098987 : Blo 2097435 2098987 := bstep (se 1 (by rfl) ⟨1574240, by rfl⟩ : syracuseStep 2098987 = 3148481) B3148481
theorem B3984805 : Blo 2097435 3984805 := bbase (se 4 (by rfl) ⟨373575, by rfl⟩ : syracuseStep 3984805 = 747151) (by norm_num)
theorem B5313073 : Blo 2097435 5313073 := bstep (se 2 (by rfl) ⟨1992402, by rfl⟩ : syracuseStep 5313073 = 3984805) B3984805
theorem B7084097 : Blo 2097435 7084097 := bstep (se 2 (by rfl) ⟨2656536, by rfl⟩ : syracuseStep 7084097 = 5313073) B5313073
theorem B4722731 : Blo 2097435 4722731 := bstep (se 1 (by rfl) ⟨3542048, by rfl⟩ : syracuseStep 4722731 = 7084097) B7084097
theorem B3148487 : Blo 2097435 3148487 := bstep (se 1 (by rfl) ⟨2361365, by rfl⟩ : syracuseStep 3148487 = 4722731) B4722731
theorem B2098991 : Blo 2097435 2098991 := bstep (se 1 (by rfl) ⟨1574243, by rfl⟩ : syracuseStep 2098991 = 3148487) B3148487
theorem B3148493 : Blo 2097435 3148493 := bbase (se 3 (by rfl) ⟨590342, by rfl⟩ : syracuseStep 3148493 = 1180685) (by norm_num)
theorem B2098995 : Blo 2097435 2098995 := bstep (se 1 (by rfl) ⟨1574246, by rfl⟩ : syracuseStep 2098995 = 3148493) B3148493
theorem B4722749 : Blo 2097435 4722749 := bbase (se 3 (by rfl) ⟨885515, by rfl⟩ : syracuseStep 4722749 = 1771031) (by norm_num)
theorem B3148499 : Blo 2097435 3148499 := bstep (se 1 (by rfl) ⟨2361374, by rfl⟩ : syracuseStep 3148499 = 4722749) B4722749
theorem B2098999 : Blo 2097435 2098999 := bstep (se 1 (by rfl) ⟨1574249, by rfl⟩ : syracuseStep 2098999 = 3148499) B3148499
theorem B3542069 : Blo 2097435 3542069 := bbase (se 5 (by rfl) ⟨166034, by rfl⟩ : syracuseStep 3542069 = 332069) (by norm_num)
theorem B2361379 : Blo 2097435 2361379 := bstep (se 1 (by rfl) ⟨1771034, by rfl⟩ : syracuseStep 2361379 = 3542069) B3542069
theorem B3148505 : Blo 2097435 3148505 := bstep (se 2 (by rfl) ⟨1180689, by rfl⟩ : syracuseStep 3148505 = 2361379) B2361379
theorem B2099003 : Blo 2097435 2099003 := bstep (se 1 (by rfl) ⟨1574252, by rfl⟩ : syracuseStep 2099003 = 3148505) B3148505
theorem B5977253 : Blo 2097435 5977253 := bbase (se 4 (by rfl) ⟨560367, by rfl⟩ : syracuseStep 5977253 = 1120735) (by norm_num)
theorem B15939341 : Blo 2097435 15939341 := bstep (se 3 (by rfl) ⟨2988626, by rfl⟩ : syracuseStep 15939341 = 5977253) B5977253
theorem B10626227 : Blo 2097435 10626227 := bstep (se 1 (by rfl) ⟨7969670, by rfl⟩ : syracuseStep 10626227 = 15939341) B15939341
theorem B7084151 : Blo 2097435 7084151 := bstep (se 1 (by rfl) ⟨5313113, by rfl⟩ : syracuseStep 7084151 = 10626227) B10626227
theorem B4722767 : Blo 2097435 4722767 := bstep (se 1 (by rfl) ⟨3542075, by rfl⟩ : syracuseStep 4722767 = 7084151) B7084151
theorem B3148511 : Blo 2097435 3148511 := bstep (se 1 (by rfl) ⟨2361383, by rfl⟩ : syracuseStep 3148511 = 4722767) B4722767
theorem B2099007 : Blo 2097435 2099007 := bstep (se 1 (by rfl) ⟨1574255, by rfl⟩ : syracuseStep 2099007 = 3148511) B3148511
theorem B3148517 : Blo 2097435 3148517 := bbase (se 4 (by rfl) ⟨295173, by rfl⟩ : syracuseStep 3148517 = 590347) (by norm_num)
theorem B2099011 : Blo 2097435 2099011 := bstep (se 1 (by rfl) ⟨1574258, by rfl⟩ : syracuseStep 2099011 = 3148517) B3148517
theorem B5385629 : Blo 2097435 5385629 := bbase (se 3 (by rfl) ⟨1009805, by rfl⟩ : syracuseStep 5385629 = 2019611) (by norm_num)
theorem B3590419 : Blo 2097435 3590419 := bstep (se 1 (by rfl) ⟨2692814, by rfl⟩ : syracuseStep 3590419 = 5385629) B5385629
theorem B4787225 : Blo 2097435 4787225 := bstep (se 2 (by rfl) ⟨1795209, by rfl⟩ : syracuseStep 4787225 = 3590419) B3590419
theorem B3191483 : Blo 2097435 3191483 := bstep (se 1 (by rfl) ⟨2393612, by rfl⟩ : syracuseStep 3191483 = 4787225) B4787225
theorem B2127655 : Blo 2097435 2127655 := bstep (se 1 (by rfl) ⟨1595741, by rfl⟩ : syracuseStep 2127655 = 3191483) B3191483
theorem B2836873 : Blo 2097435 2836873 := bstep (se 2 (by rfl) ⟨1063827, by rfl⟩ : syracuseStep 2836873 = 2127655) B2127655
theorem B3782497 : Blo 2097435 3782497 := bstep (se 2 (by rfl) ⟨1418436, by rfl⟩ : syracuseStep 3782497 = 2836873) B2836873
theorem B5043329 : Blo 2097435 5043329 := bstep (se 2 (by rfl) ⟨1891248, by rfl⟩ : syracuseStep 5043329 = 3782497) B3782497
theorem B3362219 : Blo 2097435 3362219 := bstep (se 1 (by rfl) ⟨2521664, by rfl⟩ : syracuseStep 3362219 = 5043329) B5043329
theorem B2241479 : Blo 2097435 2241479 := bstep (se 1 (by rfl) ⟨1681109, by rfl⟩ : syracuseStep 2241479 = 3362219) B3362219
theorem B5977277 : Blo 2097435 5977277 := bstep (se 3 (by rfl) ⟨1120739, by rfl⟩ : syracuseStep 5977277 = 2241479) B2241479
theorem B3984851 : Blo 2097435 3984851 := bstep (se 1 (by rfl) ⟨2988638, by rfl⟩ : syracuseStep 3984851 = 5977277) B5977277
theorem B2656567 : Blo 2097435 2656567 := bstep (se 1 (by rfl) ⟨1992425, by rfl⟩ : syracuseStep 2656567 = 3984851) B3984851
theorem B3542089 : Blo 2097435 3542089 := bstep (se 2 (by rfl) ⟨1328283, by rfl⟩ : syracuseStep 3542089 = 2656567) B2656567
theorem B4722785 : Blo 2097435 4722785 := bstep (se 2 (by rfl) ⟨1771044, by rfl⟩ : syracuseStep 4722785 = 3542089) B3542089
theorem B3148523 : Blo 2097435 3148523 := bstep (se 1 (by rfl) ⟨2361392, by rfl⟩ : syracuseStep 3148523 = 4722785) B4722785
theorem B2099015 : Blo 2097435 2099015 := bstep (se 1 (by rfl) ⟨1574261, by rfl⟩ : syracuseStep 2099015 = 3148523) B3148523
theorem B2361397 : Blo 2097435 2361397 := bbase (se 5 (by rfl) ⟨110690, by rfl⟩ : syracuseStep 2361397 = 221381) (by norm_num)
theorem B3148529 : Blo 2097435 3148529 := bstep (se 2 (by rfl) ⟨1180698, by rfl⟩ : syracuseStep 3148529 = 2361397) B2361397
theorem B2099019 : Blo 2097435 2099019 := bstep (se 1 (by rfl) ⟨1574264, by rfl⟩ : syracuseStep 2099019 = 3148529) B3148529
theorem B2656577 : Blo 2097435 2656577 := bbase (se 2 (by rfl) ⟨996216, by rfl⟩ : syracuseStep 2656577 = 1992433) (by norm_num)
theorem B7084205 : Blo 2097435 7084205 := bstep (se 3 (by rfl) ⟨1328288, by rfl⟩ : syracuseStep 7084205 = 2656577) B2656577
theorem B4722803 : Blo 2097435 4722803 := bstep (se 1 (by rfl) ⟨3542102, by rfl⟩ : syracuseStep 4722803 = 7084205) B7084205
theorem B3148535 : Blo 2097435 3148535 := bstep (se 1 (by rfl) ⟨2361401, by rfl⟩ : syracuseStep 3148535 = 4722803) B4722803
theorem B2099023 : Blo 2097435 2099023 := bstep (se 1 (by rfl) ⟨1574267, by rfl⟩ : syracuseStep 2099023 = 3148535) B3148535
theorem B3148541 : Blo 2097435 3148541 := bbase (se 3 (by rfl) ⟨590351, by rfl⟩ : syracuseStep 3148541 = 1180703) (by norm_num)
theorem B2099027 : Blo 2097435 2099027 := bstep (se 1 (by rfl) ⟨1574270, by rfl⟩ : syracuseStep 2099027 = 3148541) B3148541
theorem B4722821 : Blo 2097435 4722821 := bbase (se 4 (by rfl) ⟨442764, by rfl⟩ : syracuseStep 4722821 = 885529) (by norm_num)
theorem B3148547 : Blo 2097435 3148547 := bstep (se 1 (by rfl) ⟨2361410, by rfl⟩ : syracuseStep 3148547 = 4722821) B4722821
theorem B2099031 : Blo 2097435 2099031 := bstep (se 1 (by rfl) ⟨1574273, by rfl⟩ : syracuseStep 2099031 = 3148547) B3148547
theorem B3782533 : Blo 2097435 3782533 := bbase (se 4 (by rfl) ⟨354612, by rfl⟩ : syracuseStep 3782533 = 709225) (by norm_num)
theorem B5043377 : Blo 2097435 5043377 := bstep (se 2 (by rfl) ⟨1891266, by rfl⟩ : syracuseStep 5043377 = 3782533) B3782533
theorem B3362251 : Blo 2097435 3362251 := bstep (se 1 (by rfl) ⟨2521688, by rfl⟩ : syracuseStep 3362251 = 5043377) B5043377
theorem B4483001 : Blo 2097435 4483001 := bstep (se 2 (by rfl) ⟨1681125, by rfl⟩ : syracuseStep 4483001 = 3362251) B3362251
theorem B2988667 : Blo 2097435 2988667 := bstep (se 1 (by rfl) ⟨2241500, by rfl⟩ : syracuseStep 2988667 = 4483001) B4483001
theorem B3984889 : Blo 2097435 3984889 := bstep (se 2 (by rfl) ⟨1494333, by rfl⟩ : syracuseStep 3984889 = 2988667) B2988667
theorem B5313185 : Blo 2097435 5313185 := bstep (se 2 (by rfl) ⟨1992444, by rfl⟩ : syracuseStep 5313185 = 3984889) B3984889
theorem B3542123 : Blo 2097435 3542123 := bstep (se 1 (by rfl) ⟨2656592, by rfl⟩ : syracuseStep 3542123 = 5313185) B5313185
theorem B2361415 : Blo 2097435 2361415 := bstep (se 1 (by rfl) ⟨1771061, by rfl⟩ : syracuseStep 2361415 = 3542123) B3542123
theorem B3148553 : Blo 2097435 3148553 := bstep (se 2 (by rfl) ⟨1180707, by rfl⟩ : syracuseStep 3148553 = 2361415) B2361415
theorem B2099035 : Blo 2097435 2099035 := bstep (se 1 (by rfl) ⟨1574276, by rfl⟩ : syracuseStep 2099035 = 3148553) B3148553
theorem B10626389 : Blo 2097435 10626389 := bbase (se 12 (by rfl) ⟨3891, by rfl⟩ : syracuseStep 10626389 = 7783) (by norm_num)
theorem B7084259 : Blo 2097435 7084259 := bstep (se 1 (by rfl) ⟨5313194, by rfl⟩ : syracuseStep 7084259 = 10626389) B10626389
theorem B4722839 : Blo 2097435 4722839 := bstep (se 1 (by rfl) ⟨3542129, by rfl⟩ : syracuseStep 4722839 = 7084259) B7084259
theorem B3148559 : Blo 2097435 3148559 := bstep (se 1 (by rfl) ⟨2361419, by rfl⟩ : syracuseStep 3148559 = 4722839) B4722839
theorem B2099039 : Blo 2097435 2099039 := bstep (se 1 (by rfl) ⟨1574279, by rfl⟩ : syracuseStep 2099039 = 3148559) B3148559
theorem B3148565 : Blo 2097435 3148565 := bbase (se 6 (by rfl) ⟨73794, by rfl⟩ : syracuseStep 3148565 = 147589) (by norm_num)
theorem B2099043 : Blo 2097435 2099043 := bstep (se 1 (by rfl) ⟨1574282, by rfl⟩ : syracuseStep 2099043 = 3148565) B3148565
theorem B7278917 : Blo 2097435 7278917 := bbase (se 4 (by rfl) ⟨682398, by rfl⟩ : syracuseStep 7278917 = 1364797) (by norm_num)
theorem B19410445 : Blo 2097435 19410445 := bstep (se 3 (by rfl) ⟨3639458, by rfl⟩ : syracuseStep 19410445 = 7278917) B7278917
theorem B25880593 : Blo 2097435 25880593 := bstep (se 2 (by rfl) ⟨9705222, by rfl⟩ : syracuseStep 25880593 = 19410445) B19410445
theorem B34507457 : Blo 2097435 34507457 := bstep (se 2 (by rfl) ⟨12940296, by rfl⟩ : syracuseStep 34507457 = 25880593) B25880593
theorem B23004971 : Blo 2097435 23004971 := bstep (se 1 (by rfl) ⟨17253728, by rfl⟩ : syracuseStep 23004971 = 34507457) B34507457
theorem B15336647 : Blo 2097435 15336647 := bstep (se 1 (by rfl) ⟨11502485, by rfl⟩ : syracuseStep 15336647 = 23004971) B23004971
theorem B10224431 : Blo 2097435 10224431 := bstep (se 1 (by rfl) ⟨7668323, by rfl⟩ : syracuseStep 10224431 = 15336647) B15336647
theorem B6816287 : Blo 2097435 6816287 := bstep (se 1 (by rfl) ⟨5112215, by rfl⟩ : syracuseStep 6816287 = 10224431) B10224431
theorem B4544191 : Blo 2097435 4544191 := bstep (se 1 (by rfl) ⟨3408143, by rfl⟩ : syracuseStep 4544191 = 6816287) B6816287
theorem B6058921 : Blo 2097435 6058921 := bstep (se 2 (by rfl) ⟨2272095, by rfl⟩ : syracuseStep 6058921 = 4544191) B4544191
theorem B8078561 : Blo 2097435 8078561 := bstep (se 2 (by rfl) ⟨3029460, by rfl⟩ : syracuseStep 8078561 = 6058921) B6058921
theorem B5385707 : Blo 2097435 5385707 := bstep (se 1 (by rfl) ⟨4039280, by rfl⟩ : syracuseStep 5385707 = 8078561) B8078561
theorem B3590471 : Blo 2097435 3590471 := bstep (se 1 (by rfl) ⟨2692853, by rfl⟩ : syracuseStep 3590471 = 5385707) B5385707
theorem B2393647 : Blo 2097435 2393647 := bstep (se 1 (by rfl) ⟨1795235, by rfl⟩ : syracuseStep 2393647 = 3590471) B3590471
theorem B51064469 : Blo 2097435 51064469 := bstep (se 6 (by rfl) ⟨1196823, by rfl⟩ : syracuseStep 51064469 = 2393647) B2393647
theorem B34042979 : Blo 2097435 34042979 := bstep (se 1 (by rfl) ⟨25532234, by rfl⟩ : syracuseStep 34042979 = 51064469) B51064469
theorem B22695319 : Blo 2097435 22695319 := bstep (se 1 (by rfl) ⟨17021489, by rfl⟩ : syracuseStep 22695319 = 34042979) B34042979
theorem B30260425 : Blo 2097435 30260425 := bstep (se 2 (by rfl) ⟨11347659, by rfl⟩ : syracuseStep 30260425 = 22695319) B22695319
theorem B40347233 : Blo 2097435 40347233 := bstep (se 2 (by rfl) ⟨15130212, by rfl⟩ : syracuseStep 40347233 = 30260425) B30260425
theorem B26898155 : Blo 2097435 26898155 := bstep (se 1 (by rfl) ⟨20173616, by rfl⟩ : syracuseStep 26898155 = 40347233) B40347233
theorem B17932103 : Blo 2097435 17932103 := bstep (se 1 (by rfl) ⟨13449077, by rfl⟩ : syracuseStep 17932103 = 26898155) B26898155
theorem B11954735 : Blo 2097435 11954735 := bstep (se 1 (by rfl) ⟨8966051, by rfl⟩ : syracuseStep 11954735 = 17932103) B17932103
theorem B7969823 : Blo 2097435 7969823 := bstep (se 1 (by rfl) ⟨5977367, by rfl⟩ : syracuseStep 7969823 = 11954735) B11954735
theorem B5313215 : Blo 2097435 5313215 := bstep (se 1 (by rfl) ⟨3984911, by rfl⟩ : syracuseStep 5313215 = 7969823) B7969823
theorem B3542143 : Blo 2097435 3542143 := bstep (se 1 (by rfl) ⟨2656607, by rfl⟩ : syracuseStep 3542143 = 5313215) B5313215
theorem B4722857 : Blo 2097435 4722857 := bstep (se 2 (by rfl) ⟨1771071, by rfl⟩ : syracuseStep 4722857 = 3542143) B3542143
theorem B3148571 : Blo 2097435 3148571 := bstep (se 1 (by rfl) ⟨2361428, by rfl⟩ : syracuseStep 3148571 = 4722857) B4722857
theorem B2099047 : Blo 2097435 2099047 := bstep (se 1 (by rfl) ⟨1574285, by rfl⟩ : syracuseStep 2099047 = 3148571) B3148571
theorem B2361433 : Blo 2097435 2361433 := bbase (se 2 (by rfl) ⟨885537, by rfl⟩ : syracuseStep 2361433 = 1771075) (by norm_num)
theorem B3148577 : Blo 2097435 3148577 := bstep (se 2 (by rfl) ⟨1180716, by rfl⟩ : syracuseStep 3148577 = 2361433) B2361433
theorem B2099051 : Blo 2097435 2099051 := bstep (se 1 (by rfl) ⟨1574288, by rfl⟩ : syracuseStep 2099051 = 3148577) B3148577
theorem B6724565 : Blo 2097435 6724565 := bbase (se 7 (by rfl) ⟨78803, by rfl⟩ : syracuseStep 6724565 = 157607) (by norm_num)
theorem B4483043 : Blo 2097435 4483043 := bstep (se 1 (by rfl) ⟨3362282, by rfl⟩ : syracuseStep 4483043 = 6724565) B6724565
theorem B2988695 : Blo 2097435 2988695 := bstep (se 1 (by rfl) ⟨2241521, by rfl⟩ : syracuseStep 2988695 = 4483043) B4483043
theorem B7969853 : Blo 2097435 7969853 := bstep (se 3 (by rfl) ⟨1494347, by rfl⟩ : syracuseStep 7969853 = 2988695) B2988695
theorem B5313235 : Blo 2097435 5313235 := bstep (se 1 (by rfl) ⟨3984926, by rfl⟩ : syracuseStep 5313235 = 7969853) B7969853
theorem B7084313 : Blo 2097435 7084313 := bstep (se 2 (by rfl) ⟨2656617, by rfl⟩ : syracuseStep 7084313 = 5313235) B5313235
theorem B4722875 : Blo 2097435 4722875 := bstep (se 1 (by rfl) ⟨3542156, by rfl⟩ : syracuseStep 4722875 = 7084313) B7084313
theorem B3148583 : Blo 2097435 3148583 := bstep (se 1 (by rfl) ⟨2361437, by rfl⟩ : syracuseStep 3148583 = 4722875) B4722875
theorem B2099055 : Blo 2097435 2099055 := bstep (se 1 (by rfl) ⟨1574291, by rfl⟩ : syracuseStep 2099055 = 3148583) B3148583
theorem B3148589 : Blo 2097435 3148589 := bbase (se 3 (by rfl) ⟨590360, by rfl⟩ : syracuseStep 3148589 = 1180721) (by norm_num)
theorem B2099059 : Blo 2097435 2099059 := bstep (se 1 (by rfl) ⟨1574294, by rfl⟩ : syracuseStep 2099059 = 3148589) B3148589
theorem B4722893 : Blo 2097435 4722893 := bbase (se 3 (by rfl) ⟨885542, by rfl⟩ : syracuseStep 4722893 = 1771085) (by norm_num)
theorem B3148595 : Blo 2097435 3148595 := bstep (se 1 (by rfl) ⟨2361446, by rfl⟩ : syracuseStep 3148595 = 4722893) B4722893
theorem B2099063 : Blo 2097435 2099063 := bstep (se 1 (by rfl) ⟨1574297, by rfl⟩ : syracuseStep 2099063 = 3148595) B3148595
theorem B2656633 : Blo 2097435 2656633 := bbase (se 2 (by rfl) ⟨996237, by rfl⟩ : syracuseStep 2656633 = 1992475) (by norm_num)
theorem B3542177 : Blo 2097435 3542177 := bstep (se 2 (by rfl) ⟨1328316, by rfl⟩ : syracuseStep 3542177 = 2656633) B2656633
theorem B2361451 : Blo 2097435 2361451 := bstep (se 1 (by rfl) ⟨1771088, by rfl⟩ : syracuseStep 2361451 = 3542177) B3542177
theorem B3148601 : Blo 2097435 3148601 := bstep (se 2 (by rfl) ⟨1180725, by rfl⟩ : syracuseStep 3148601 = 2361451) B2361451
theorem B2099067 : Blo 2097435 2099067 := bstep (se 1 (by rfl) ⟨1574300, by rfl⟩ : syracuseStep 2099067 = 3148601) B3148601
theorem B4255421 : Blo 2097435 4255421 := bbase (se 3 (by rfl) ⟨797891, by rfl⟩ : syracuseStep 4255421 = 1595783) (by norm_num)
theorem B11347789 : Blo 2097435 11347789 := bstep (se 3 (by rfl) ⟨2127710, by rfl⟩ : syracuseStep 11347789 = 4255421) B4255421
theorem B15130385 : Blo 2097435 15130385 := bstep (se 2 (by rfl) ⟨5673894, by rfl⟩ : syracuseStep 15130385 = 11347789) B11347789
theorem B10086923 : Blo 2097435 10086923 := bstep (se 1 (by rfl) ⟨7565192, by rfl⟩ : syracuseStep 10086923 = 15130385) B15130385
theorem B6724615 : Blo 2097435 6724615 := bstep (se 1 (by rfl) ⟨5043461, by rfl⟩ : syracuseStep 6724615 = 10086923) B10086923
theorem B8966153 : Blo 2097435 8966153 := bstep (se 2 (by rfl) ⟨3362307, by rfl⟩ : syracuseStep 8966153 = 6724615) B6724615
theorem B23909741 : Blo 2097435 23909741 := bstep (se 3 (by rfl) ⟨4483076, by rfl⟩ : syracuseStep 23909741 = 8966153) B8966153
theorem B15939827 : Blo 2097435 15939827 := bstep (se 1 (by rfl) ⟨11954870, by rfl⟩ : syracuseStep 15939827 = 23909741) B23909741
theorem B10626551 : Blo 2097435 10626551 := bstep (se 1 (by rfl) ⟨7969913, by rfl⟩ : syracuseStep 10626551 = 15939827) B15939827
theorem B7084367 : Blo 2097435 7084367 := bstep (se 1 (by rfl) ⟨5313275, by rfl⟩ : syracuseStep 7084367 = 10626551) B10626551
theorem B4722911 : Blo 2097435 4722911 := bstep (se 1 (by rfl) ⟨3542183, by rfl⟩ : syracuseStep 4722911 = 7084367) B7084367
theorem B3148607 : Blo 2097435 3148607 := bstep (se 1 (by rfl) ⟨2361455, by rfl⟩ : syracuseStep 3148607 = 4722911) B4722911
theorem B2099071 : Blo 2097435 2099071 := bstep (se 1 (by rfl) ⟨1574303, by rfl⟩ : syracuseStep 2099071 = 3148607) B3148607
theorem B3148613 : Blo 2097435 3148613 := bbase (se 4 (by rfl) ⟨295182, by rfl⟩ : syracuseStep 3148613 = 590365) (by norm_num)
theorem B2099075 : Blo 2097435 2099075 := bstep (se 1 (by rfl) ⟨1574306, by rfl⟩ : syracuseStep 2099075 = 3148613) B3148613
theorem B3542197 : Blo 2097435 3542197 := bbase (se 5 (by rfl) ⟨166040, by rfl⟩ : syracuseStep 3542197 = 332081) (by norm_num)
theorem B4722929 : Blo 2097435 4722929 := bstep (se 2 (by rfl) ⟨1771098, by rfl⟩ : syracuseStep 4722929 = 3542197) B3542197
theorem B3148619 : Blo 2097435 3148619 := bstep (se 1 (by rfl) ⟨2361464, by rfl⟩ : syracuseStep 3148619 = 4722929) B4722929
theorem B2099079 : Blo 2097435 2099079 := bstep (se 1 (by rfl) ⟨1574309, by rfl⟩ : syracuseStep 2099079 = 3148619) B3148619
theorem B2361469 : Blo 2097435 2361469 := bbase (se 3 (by rfl) ⟨442775, by rfl⟩ : syracuseStep 2361469 = 885551) (by norm_num)
theorem B3148625 : Blo 2097435 3148625 := bstep (se 2 (by rfl) ⟨1180734, by rfl⟩ : syracuseStep 3148625 = 2361469) B2361469
theorem B2099083 : Blo 2097435 2099083 := bstep (se 1 (by rfl) ⟨1574312, by rfl⟩ : syracuseStep 2099083 = 3148625) B3148625
theorem B7084421 : Blo 2097435 7084421 := bbase (se 4 (by rfl) ⟨664164, by rfl⟩ : syracuseStep 7084421 = 1328329) (by norm_num)
theorem B4722947 : Blo 2097435 4722947 := bstep (se 1 (by rfl) ⟨3542210, by rfl⟩ : syracuseStep 4722947 = 7084421) B7084421
theorem B3148631 : Blo 2097435 3148631 := bstep (se 1 (by rfl) ⟨2361473, by rfl⟩ : syracuseStep 3148631 = 4722947) B4722947
theorem B2099087 : Blo 2097435 2099087 := bstep (se 1 (by rfl) ⟨1574315, by rfl⟩ : syracuseStep 2099087 = 3148631) B3148631
theorem B3148637 : Blo 2097435 3148637 := bbase (se 3 (by rfl) ⟨590369, by rfl⟩ : syracuseStep 3148637 = 1180739) (by norm_num)
theorem B2099091 : Blo 2097435 2099091 := bstep (se 1 (by rfl) ⟨1574318, by rfl⟩ : syracuseStep 2099091 = 3148637) B3148637
theorem B4722965 : Blo 2097435 4722965 := bbase (se 6 (by rfl) ⟨110694, by rfl⟩ : syracuseStep 4722965 = 221389) (by norm_num)
theorem B3148643 : Blo 2097435 3148643 := bstep (se 1 (by rfl) ⟨2361482, by rfl⟩ : syracuseStep 3148643 = 4722965) B4722965
theorem B2099095 : Blo 2097435 2099095 := bstep (se 1 (by rfl) ⟨1574321, by rfl⟩ : syracuseStep 2099095 = 3148643) B3148643
theorem B7970021 : Blo 2097435 7970021 := bbase (se 4 (by rfl) ⟨747189, by rfl⟩ : syracuseStep 7970021 = 1494379) (by norm_num)
theorem B5313347 : Blo 2097435 5313347 := bstep (se 1 (by rfl) ⟨3985010, by rfl⟩ : syracuseStep 5313347 = 7970021) B7970021
theorem B3542231 : Blo 2097435 3542231 := bstep (se 1 (by rfl) ⟨2656673, by rfl⟩ : syracuseStep 3542231 = 5313347) B5313347
theorem B2361487 : Blo 2097435 2361487 := bstep (se 1 (by rfl) ⟨1771115, by rfl⟩ : syracuseStep 2361487 = 3542231) B3542231
theorem B3148649 : Blo 2097435 3148649 := bstep (se 2 (by rfl) ⟨1180743, by rfl⟩ : syracuseStep 3148649 = 2361487) B2361487
theorem B2099099 : Blo 2097435 2099099 := bstep (se 1 (by rfl) ⟨1574324, by rfl⟩ : syracuseStep 2099099 = 3148649) B3148649
theorem B4918949 : Blo 2097435 4918949 := bbase (se 4 (by rfl) ⟨461151, by rfl⟩ : syracuseStep 4918949 = 922303) (by norm_num)
theorem B3279299 : Blo 2097435 3279299 := bstep (se 1 (by rfl) ⟨2459474, by rfl⟩ : syracuseStep 3279299 = 4918949) B4918949
theorem B8744797 : Blo 2097435 8744797 := bstep (se 3 (by rfl) ⟨1639649, by rfl⟩ : syracuseStep 8744797 = 3279299) B3279299
theorem B11659729 : Blo 2097435 11659729 := bstep (se 2 (by rfl) ⟨4372398, by rfl⟩ : syracuseStep 11659729 = 8744797) B8744797
theorem B15546305 : Blo 2097435 15546305 := bstep (se 2 (by rfl) ⟨5829864, by rfl⟩ : syracuseStep 15546305 = 11659729) B11659729
theorem B10364203 : Blo 2097435 10364203 := bstep (se 1 (by rfl) ⟨7773152, by rfl⟩ : syracuseStep 10364203 = 15546305) B15546305
theorem B13818937 : Blo 2097435 13818937 := bstep (se 2 (by rfl) ⟨5182101, by rfl⟩ : syracuseStep 13818937 = 10364203) B10364203
theorem B18425249 : Blo 2097435 18425249 := bstep (se 2 (by rfl) ⟨6909468, by rfl⟩ : syracuseStep 18425249 = 13818937) B13818937
theorem B12283499 : Blo 2097435 12283499 := bstep (se 1 (by rfl) ⟨9212624, by rfl⟩ : syracuseStep 12283499 = 18425249) B18425249
theorem B32755997 : Blo 2097435 32755997 := bstep (se 3 (by rfl) ⟨6141749, by rfl⟩ : syracuseStep 32755997 = 12283499) B12283499
theorem B21837331 : Blo 2097435 21837331 := bstep (se 1 (by rfl) ⟨16377998, by rfl⟩ : syracuseStep 21837331 = 32755997) B32755997
theorem B29116441 : Blo 2097435 29116441 := bstep (se 2 (by rfl) ⟨10918665, by rfl⟩ : syracuseStep 29116441 = 21837331) B21837331
theorem B155287685 : Blo 2097435 155287685 := bstep (se 4 (by rfl) ⟨14558220, by rfl⟩ : syracuseStep 155287685 = 29116441) B29116441
theorem B103525123 : Blo 2097435 103525123 := bstep (se 1 (by rfl) ⟨77643842, by rfl⟩ : syracuseStep 103525123 = 155287685) B155287685
theorem B138033497 : Blo 2097435 138033497 := bstep (se 2 (by rfl) ⟨51762561, by rfl⟩ : syracuseStep 138033497 = 103525123) B103525123
theorem B92022331 : Blo 2097435 92022331 := bstep (se 1 (by rfl) ⟨69016748, by rfl⟩ : syracuseStep 92022331 = 138033497) B138033497
theorem B122696441 : Blo 2097435 122696441 := bstep (se 2 (by rfl) ⟨46011165, by rfl⟩ : syracuseStep 122696441 = 92022331) B92022331
theorem B81797627 : Blo 2097435 81797627 := bstep (se 1 (by rfl) ⟨61348220, by rfl⟩ : syracuseStep 81797627 = 122696441) B122696441
theorem B54531751 : Blo 2097435 54531751 := bstep (se 1 (by rfl) ⟨40898813, by rfl⟩ : syracuseStep 54531751 = 81797627) B81797627
theorem B72709001 : Blo 2097435 72709001 := bstep (se 2 (by rfl) ⟨27265875, by rfl⟩ : syracuseStep 72709001 = 54531751) B54531751
theorem B48472667 : Blo 2097435 48472667 := bstep (se 1 (by rfl) ⟨36354500, by rfl⟩ : syracuseStep 48472667 = 72709001) B72709001
theorem B32315111 : Blo 2097435 32315111 := bstep (se 1 (by rfl) ⟨24236333, by rfl⟩ : syracuseStep 32315111 = 48472667) B48472667
theorem B21543407 : Blo 2097435 21543407 := bstep (se 1 (by rfl) ⟨16157555, by rfl⟩ : syracuseStep 21543407 = 32315111) B32315111
theorem B14362271 : Blo 2097435 14362271 := bstep (se 1 (by rfl) ⟨10771703, by rfl⟩ : syracuseStep 14362271 = 21543407) B21543407
theorem B9574847 : Blo 2097435 9574847 := bstep (se 1 (by rfl) ⟨7181135, by rfl⟩ : syracuseStep 9574847 = 14362271) B14362271
theorem B6383231 : Blo 2097435 6383231 := bstep (se 1 (by rfl) ⟨4787423, by rfl⟩ : syracuseStep 6383231 = 9574847) B9574847
theorem B4255487 : Blo 2097435 4255487 := bstep (se 1 (by rfl) ⟨3191615, by rfl⟩ : syracuseStep 4255487 = 6383231) B6383231
theorem B2836991 : Blo 2097435 2836991 := bstep (se 1 (by rfl) ⟨2127743, by rfl⟩ : syracuseStep 2836991 = 4255487) B4255487
theorem B7565309 : Blo 2097435 7565309 := bstep (se 3 (by rfl) ⟨1418495, by rfl⟩ : syracuseStep 7565309 = 2836991) B2836991
theorem B5043539 : Blo 2097435 5043539 := bstep (se 1 (by rfl) ⟨3782654, by rfl⟩ : syracuseStep 5043539 = 7565309) B7565309
theorem B3362359 : Blo 2097435 3362359 := bstep (se 1 (by rfl) ⟨2521769, by rfl⟩ : syracuseStep 3362359 = 5043539) B5043539
theorem B4483145 : Blo 2097435 4483145 := bstep (se 2 (by rfl) ⟨1681179, by rfl⟩ : syracuseStep 4483145 = 3362359) B3362359
theorem B11955053 : Blo 2097435 11955053 := bstep (se 3 (by rfl) ⟨2241572, by rfl⟩ : syracuseStep 11955053 = 4483145) B4483145
theorem B7970035 : Blo 2097435 7970035 := bstep (se 1 (by rfl) ⟨5977526, by rfl⟩ : syracuseStep 7970035 = 11955053) B11955053
theorem B10626713 : Blo 2097435 10626713 := bstep (se 2 (by rfl) ⟨3985017, by rfl⟩ : syracuseStep 10626713 = 7970035) B7970035
theorem B7084475 : Blo 2097435 7084475 := bstep (se 1 (by rfl) ⟨5313356, by rfl⟩ : syracuseStep 7084475 = 10626713) B10626713
theorem B4722983 : Blo 2097435 4722983 := bstep (se 1 (by rfl) ⟨3542237, by rfl⟩ : syracuseStep 4722983 = 7084475) B7084475
theorem B3148655 : Blo 2097435 3148655 := bstep (se 1 (by rfl) ⟨2361491, by rfl⟩ : syracuseStep 3148655 = 4722983) B4722983
theorem B2099103 : Blo 2097435 2099103 := bstep (se 1 (by rfl) ⟨1574327, by rfl⟩ : syracuseStep 2099103 = 3148655) B3148655
theorem B3148661 : Blo 2097435 3148661 := bbase (se 5 (by rfl) ⟨147593, by rfl⟩ : syracuseStep 3148661 = 295187) (by norm_num)
theorem B2099107 : Blo 2097435 2099107 := bstep (se 1 (by rfl) ⟨1574330, by rfl⟩ : syracuseStep 2099107 = 3148661) B3148661
theorem B10918709 : Blo 2097435 10918709 := bbase (se 5 (by rfl) ⟨511814, by rfl⟩ : syracuseStep 10918709 = 1023629) (by norm_num)
theorem B7279139 : Blo 2097435 7279139 := bstep (se 1 (by rfl) ⟨5459354, by rfl⟩ : syracuseStep 7279139 = 10918709) B10918709
theorem B4852759 : Blo 2097435 4852759 := bstep (se 1 (by rfl) ⟨3639569, by rfl⟩ : syracuseStep 4852759 = 7279139) B7279139
theorem B6470345 : Blo 2097435 6470345 := bstep (se 2 (by rfl) ⟨2426379, by rfl⟩ : syracuseStep 6470345 = 4852759) B4852759
theorem B17254253 : Blo 2097435 17254253 := bstep (se 3 (by rfl) ⟨3235172, by rfl⟩ : syracuseStep 17254253 = 6470345) B6470345
theorem B46011341 : Blo 2097435 46011341 := bstep (se 3 (by rfl) ⟨8627126, by rfl⟩ : syracuseStep 46011341 = 17254253) B17254253
theorem B30674227 : Blo 2097435 30674227 := bstep (se 1 (by rfl) ⟨23005670, by rfl⟩ : syracuseStep 30674227 = 46011341) B46011341
theorem B40898969 : Blo 2097435 40898969 := bstep (se 2 (by rfl) ⟨15337113, by rfl⟩ : syracuseStep 40898969 = 30674227) B30674227
theorem B27265979 : Blo 2097435 27265979 := bstep (se 1 (by rfl) ⟨20449484, by rfl⟩ : syracuseStep 27265979 = 40898969) B40898969
theorem B18177319 : Blo 2097435 18177319 := bstep (se 1 (by rfl) ⟨13632989, by rfl⟩ : syracuseStep 18177319 = 27265979) B27265979
theorem B24236425 : Blo 2097435 24236425 := bstep (se 2 (by rfl) ⟨9088659, by rfl⟩ : syracuseStep 24236425 = 18177319) B18177319
theorem B32315233 : Blo 2097435 32315233 := bstep (se 2 (by rfl) ⟨12118212, by rfl⟩ : syracuseStep 32315233 = 24236425) B24236425
theorem B43086977 : Blo 2097435 43086977 := bstep (se 2 (by rfl) ⟨16157616, by rfl⟩ : syracuseStep 43086977 = 32315233) B32315233
theorem B28724651 : Blo 2097435 28724651 := bstep (se 1 (by rfl) ⟨21543488, by rfl⟩ : syracuseStep 28724651 = 43086977) B43086977
theorem B19149767 : Blo 2097435 19149767 := bstep (se 1 (by rfl) ⟨14362325, by rfl⟩ : syracuseStep 19149767 = 28724651) B28724651
theorem B12766511 : Blo 2097435 12766511 := bstep (se 1 (by rfl) ⟨9574883, by rfl⟩ : syracuseStep 12766511 = 19149767) B19149767
theorem B8511007 : Blo 2097435 8511007 := bstep (se 1 (by rfl) ⟨6383255, by rfl⟩ : syracuseStep 8511007 = 12766511) B12766511
theorem B11348009 : Blo 2097435 11348009 := bstep (se 2 (by rfl) ⟨4255503, by rfl⟩ : syracuseStep 11348009 = 8511007) B8511007
theorem B7565339 : Blo 2097435 7565339 := bstep (se 1 (by rfl) ⟨5674004, by rfl⟩ : syracuseStep 7565339 = 11348009) B11348009
theorem B5043559 : Blo 2097435 5043559 := bstep (se 1 (by rfl) ⟨3782669, by rfl⟩ : syracuseStep 5043559 = 7565339) B7565339
theorem B6724745 : Blo 2097435 6724745 := bstep (se 2 (by rfl) ⟨2521779, by rfl⟩ : syracuseStep 6724745 = 5043559) B5043559
theorem B4483163 : Blo 2097435 4483163 := bstep (se 1 (by rfl) ⟨3362372, by rfl⟩ : syracuseStep 4483163 = 6724745) B6724745
theorem B2988775 : Blo 2097435 2988775 := bstep (se 1 (by rfl) ⟨2241581, by rfl⟩ : syracuseStep 2988775 = 4483163) B4483163
theorem B3985033 : Blo 2097435 3985033 := bstep (se 2 (by rfl) ⟨1494387, by rfl⟩ : syracuseStep 3985033 = 2988775) B2988775
theorem B5313377 : Blo 2097435 5313377 := bstep (se 2 (by rfl) ⟨1992516, by rfl⟩ : syracuseStep 5313377 = 3985033) B3985033
theorem B3542251 : Blo 2097435 3542251 := bstep (se 1 (by rfl) ⟨2656688, by rfl⟩ : syracuseStep 3542251 = 5313377) B5313377
theorem B4723001 : Blo 2097435 4723001 := bstep (se 2 (by rfl) ⟨1771125, by rfl⟩ : syracuseStep 4723001 = 3542251) B3542251
theorem B3148667 : Blo 2097435 3148667 := bstep (se 1 (by rfl) ⟨2361500, by rfl⟩ : syracuseStep 3148667 = 4723001) B4723001
theorem B2099111 : Blo 2097435 2099111 := bstep (se 1 (by rfl) ⟨1574333, by rfl⟩ : syracuseStep 2099111 = 3148667) B3148667
theorem B2361505 : Blo 2097435 2361505 := bbase (se 2 (by rfl) ⟨885564, by rfl⟩ : syracuseStep 2361505 = 1771129) (by norm_num)
theorem B3148673 : Blo 2097435 3148673 := bstep (se 2 (by rfl) ⟨1180752, by rfl⟩ : syracuseStep 3148673 = 2361505) B2361505
theorem B2099115 : Blo 2097435 2099115 := bstep (se 1 (by rfl) ⟨1574336, by rfl⟩ : syracuseStep 2099115 = 3148673) B3148673
theorem B5313397 : Blo 2097435 5313397 := bbase (se 5 (by rfl) ⟨249065, by rfl⟩ : syracuseStep 5313397 = 498131) (by norm_num)
theorem B7084529 : Blo 2097435 7084529 := bstep (se 2 (by rfl) ⟨2656698, by rfl⟩ : syracuseStep 7084529 = 5313397) B5313397
theorem B4723019 : Blo 2097435 4723019 := bstep (se 1 (by rfl) ⟨3542264, by rfl⟩ : syracuseStep 4723019 = 7084529) B7084529
theorem B3148679 : Blo 2097435 3148679 := bstep (se 1 (by rfl) ⟨2361509, by rfl⟩ : syracuseStep 3148679 = 4723019) B4723019
theorem B2099119 : Blo 2097435 2099119 := bstep (se 1 (by rfl) ⟨1574339, by rfl⟩ : syracuseStep 2099119 = 3148679) B3148679
theorem B3148685 : Blo 2097435 3148685 := bbase (se 3 (by rfl) ⟨590378, by rfl⟩ : syracuseStep 3148685 = 1180757) (by norm_num)
theorem B2099123 : Blo 2097435 2099123 := bstep (se 1 (by rfl) ⟨1574342, by rfl⟩ : syracuseStep 2099123 = 3148685) B3148685
theorem B4723037 : Blo 2097435 4723037 := bbase (se 3 (by rfl) ⟨885569, by rfl⟩ : syracuseStep 4723037 = 1771139) (by norm_num)
theorem B3148691 : Blo 2097435 3148691 := bstep (se 1 (by rfl) ⟨2361518, by rfl⟩ : syracuseStep 3148691 = 4723037) B4723037
theorem B2099127 : Blo 2097435 2099127 := bstep (se 1 (by rfl) ⟨1574345, by rfl⟩ : syracuseStep 2099127 = 3148691) B3148691
theorem B3542285 : Blo 2097435 3542285 := bbase (se 3 (by rfl) ⟨664178, by rfl⟩ : syracuseStep 3542285 = 1328357) (by norm_num)
theorem B2361523 : Blo 2097435 2361523 := bstep (se 1 (by rfl) ⟨1771142, by rfl⟩ : syracuseStep 2361523 = 3542285) B3542285
theorem B3148697 : Blo 2097435 3148697 := bstep (se 2 (by rfl) ⟨1180761, by rfl⟩ : syracuseStep 3148697 = 2361523) B2361523
theorem B2099131 : Blo 2097435 2099131 := bstep (se 1 (by rfl) ⟨1574348, by rfl⟩ : syracuseStep 2099131 = 3148697) B3148697
theorem B17932853 : Blo 2097435 17932853 := bbase (se 5 (by rfl) ⟨840602, by rfl⟩ : syracuseStep 17932853 = 1681205) (by norm_num)
theorem B11955235 : Blo 2097435 11955235 := bstep (se 1 (by rfl) ⟨8966426, by rfl⟩ : syracuseStep 11955235 = 17932853) B17932853
theorem B15940313 : Blo 2097435 15940313 := bstep (se 2 (by rfl) ⟨5977617, by rfl⟩ : syracuseStep 15940313 = 11955235) B11955235
theorem B10626875 : Blo 2097435 10626875 := bstep (se 1 (by rfl) ⟨7970156, by rfl⟩ : syracuseStep 10626875 = 15940313) B15940313
theorem B7084583 : Blo 2097435 7084583 := bstep (se 1 (by rfl) ⟨5313437, by rfl⟩ : syracuseStep 7084583 = 10626875) B10626875
theorem B4723055 : Blo 2097435 4723055 := bstep (se 1 (by rfl) ⟨3542291, by rfl⟩ : syracuseStep 4723055 = 7084583) B7084583
theorem B3148703 : Blo 2097435 3148703 := bstep (se 1 (by rfl) ⟨2361527, by rfl⟩ : syracuseStep 3148703 = 4723055) B4723055
theorem B2099135 : Blo 2097435 2099135 := bstep (se 1 (by rfl) ⟨1574351, by rfl⟩ : syracuseStep 2099135 = 3148703) B3148703
theorem B3148709 : Blo 2097435 3148709 := bbase (se 4 (by rfl) ⟨295191, by rfl⟩ : syracuseStep 3148709 = 590383) (by norm_num)
theorem B2099139 : Blo 2097435 2099139 := bstep (se 1 (by rfl) ⟨1574354, by rfl⟩ : syracuseStep 2099139 = 3148709) B3148709
theorem B2656729 : Blo 2097435 2656729 := bbase (se 2 (by rfl) ⟨996273, by rfl⟩ : syracuseStep 2656729 = 1992547) (by norm_num)
theorem B3542305 : Blo 2097435 3542305 := bstep (se 2 (by rfl) ⟨1328364, by rfl⟩ : syracuseStep 3542305 = 2656729) B2656729
theorem B4723073 : Blo 2097435 4723073 := bstep (se 2 (by rfl) ⟨1771152, by rfl⟩ : syracuseStep 4723073 = 3542305) B3542305
theorem B3148715 : Blo 2097435 3148715 := bstep (se 1 (by rfl) ⟨2361536, by rfl⟩ : syracuseStep 3148715 = 4723073) B4723073
theorem B2099143 : Blo 2097435 2099143 := bstep (se 1 (by rfl) ⟨1574357, by rfl⟩ : syracuseStep 2099143 = 3148715) B3148715
theorem B2361541 : Blo 2097435 2361541 := bbase (se 4 (by rfl) ⟨221394, by rfl⟩ : syracuseStep 2361541 = 442789) (by norm_num)
theorem B3148721 : Blo 2097435 3148721 := bstep (se 2 (by rfl) ⟨1180770, by rfl⟩ : syracuseStep 3148721 = 2361541) B2361541
theorem B2099147 : Blo 2097435 2099147 := bstep (se 1 (by rfl) ⟨1574360, by rfl⟩ : syracuseStep 2099147 = 3148721) B3148721
theorem B3985109 : Blo 2097435 3985109 := bbase (se 7 (by rfl) ⟨46700, by rfl⟩ : syracuseStep 3985109 = 93401) (by norm_num)
theorem B2656739 : Blo 2097435 2656739 := bstep (se 1 (by rfl) ⟨1992554, by rfl⟩ : syracuseStep 2656739 = 3985109) B3985109
theorem B7084637 : Blo 2097435 7084637 := bstep (se 3 (by rfl) ⟨1328369, by rfl⟩ : syracuseStep 7084637 = 2656739) B2656739
theorem B4723091 : Blo 2097435 4723091 := bstep (se 1 (by rfl) ⟨3542318, by rfl⟩ : syracuseStep 4723091 = 7084637) B7084637
theorem B3148727 : Blo 2097435 3148727 := bstep (se 1 (by rfl) ⟨2361545, by rfl⟩ : syracuseStep 3148727 = 4723091) B4723091
theorem B2099151 : Blo 2097435 2099151 := bstep (se 1 (by rfl) ⟨1574363, by rfl⟩ : syracuseStep 2099151 = 3148727) B3148727
theorem B3148733 : Blo 2097435 3148733 := bbase (se 3 (by rfl) ⟨590387, by rfl⟩ : syracuseStep 3148733 = 1180775) (by norm_num)
theorem B2099155 : Blo 2097435 2099155 := bstep (se 1 (by rfl) ⟨1574366, by rfl⟩ : syracuseStep 2099155 = 3148733) B3148733
theorem B4723109 : Blo 2097435 4723109 := bbase (se 4 (by rfl) ⟨442791, by rfl⟩ : syracuseStep 4723109 = 885583) (by norm_num)
theorem B3148739 : Blo 2097435 3148739 := bstep (se 1 (by rfl) ⟨2361554, by rfl⟩ : syracuseStep 3148739 = 4723109) B4723109
theorem B2099159 : Blo 2097435 2099159 := bstep (se 1 (by rfl) ⟨1574369, by rfl⟩ : syracuseStep 2099159 = 3148739) B3148739
theorem B5313509 : Blo 2097435 5313509 := bbase (se 4 (by rfl) ⟨498141, by rfl⟩ : syracuseStep 5313509 = 996283) (by norm_num)
theorem B3542339 : Blo 2097435 3542339 := bstep (se 1 (by rfl) ⟨2656754, by rfl⟩ : syracuseStep 3542339 = 5313509) B5313509
theorem B2361559 : Blo 2097435 2361559 := bstep (se 1 (by rfl) ⟨1771169, by rfl⟩ : syracuseStep 2361559 = 3542339) B3542339
theorem B3148745 : Blo 2097435 3148745 := bstep (se 2 (by rfl) ⟨1180779, by rfl⟩ : syracuseStep 3148745 = 2361559) B2361559
theorem B2099163 : Blo 2097435 2099163 := bstep (se 1 (by rfl) ⟨1574372, by rfl⟩ : syracuseStep 2099163 = 3148745) B3148745
theorem B2241641 : Blo 2097435 2241641 := bbase (se 2 (by rfl) ⟨840615, by rfl⟩ : syracuseStep 2241641 = 1681231) (by norm_num)
theorem B5977709 : Blo 2097435 5977709 := bstep (se 3 (by rfl) ⟨1120820, by rfl⟩ : syracuseStep 5977709 = 2241641) B2241641
theorem B3985139 : Blo 2097435 3985139 := bstep (se 1 (by rfl) ⟨2988854, by rfl⟩ : syracuseStep 3985139 = 5977709) B5977709
theorem B10627037 : Blo 2097435 10627037 := bstep (se 3 (by rfl) ⟨1992569, by rfl⟩ : syracuseStep 10627037 = 3985139) B3985139
theorem B7084691 : Blo 2097435 7084691 := bstep (se 1 (by rfl) ⟨5313518, by rfl⟩ : syracuseStep 7084691 = 10627037) B10627037
theorem B4723127 : Blo 2097435 4723127 := bstep (se 1 (by rfl) ⟨3542345, by rfl⟩ : syracuseStep 4723127 = 7084691) B7084691
theorem B3148751 : Blo 2097435 3148751 := bstep (se 1 (by rfl) ⟨2361563, by rfl⟩ : syracuseStep 3148751 = 4723127) B4723127
theorem B2099167 : Blo 2097435 2099167 := bstep (se 1 (by rfl) ⟨1574375, by rfl⟩ : syracuseStep 2099167 = 3148751) B3148751
theorem B3148757 : Blo 2097435 3148757 := bbase (se 7 (by rfl) ⟨36899, by rfl⟩ : syracuseStep 3148757 = 73799) (by norm_num)
theorem B2099171 : Blo 2097435 2099171 := bstep (se 1 (by rfl) ⟨1574378, by rfl⟩ : syracuseStep 2099171 = 3148757) B3148757
theorem B7970309 : Blo 2097435 7970309 := bbase (se 4 (by rfl) ⟨747216, by rfl⟩ : syracuseStep 7970309 = 1494433) (by norm_num)
theorem B5313539 : Blo 2097435 5313539 := bstep (se 1 (by rfl) ⟨3985154, by rfl⟩ : syracuseStep 5313539 = 7970309) B7970309
theorem B3542359 : Blo 2097435 3542359 := bstep (se 1 (by rfl) ⟨2656769, by rfl⟩ : syracuseStep 3542359 = 5313539) B5313539
theorem B4723145 : Blo 2097435 4723145 := bstep (se 2 (by rfl) ⟨1771179, by rfl⟩ : syracuseStep 4723145 = 3542359) B3542359
theorem B3148763 : Blo 2097435 3148763 := bstep (se 1 (by rfl) ⟨2361572, by rfl⟩ : syracuseStep 3148763 = 4723145) B4723145
theorem B2099175 : Blo 2097435 2099175 := bstep (se 1 (by rfl) ⟨1574381, by rfl⟩ : syracuseStep 2099175 = 3148763) B3148763
theorem B2361577 : Blo 2097435 2361577 := bbase (se 2 (by rfl) ⟨885591, by rfl⟩ : syracuseStep 2361577 = 1771183) (by norm_num)
theorem B3148769 : Blo 2097435 3148769 := bstep (se 2 (by rfl) ⟨1180788, by rfl⟩ : syracuseStep 3148769 = 2361577) B2361577
theorem B2099179 : Blo 2097435 2099179 := bstep (se 1 (by rfl) ⟨1574384, by rfl⟩ : syracuseStep 2099179 = 3148769) B3148769
theorem B11955509 : Blo 2097435 11955509 := bbase (se 5 (by rfl) ⟨560414, by rfl⟩ : syracuseStep 11955509 = 1120829) (by norm_num)
theorem B7970339 : Blo 2097435 7970339 := bstep (se 1 (by rfl) ⟨5977754, by rfl⟩ : syracuseStep 7970339 = 11955509) B11955509
theorem B5313559 : Blo 2097435 5313559 := bstep (se 1 (by rfl) ⟨3985169, by rfl⟩ : syracuseStep 5313559 = 7970339) B7970339
theorem B7084745 : Blo 2097435 7084745 := bstep (se 2 (by rfl) ⟨2656779, by rfl⟩ : syracuseStep 7084745 = 5313559) B5313559
theorem B4723163 : Blo 2097435 4723163 := bstep (se 1 (by rfl) ⟨3542372, by rfl⟩ : syracuseStep 4723163 = 7084745) B7084745
theorem B3148775 : Blo 2097435 3148775 := bstep (se 1 (by rfl) ⟨2361581, by rfl⟩ : syracuseStep 3148775 = 4723163) B4723163
theorem B2099183 : Blo 2097435 2099183 := bstep (se 1 (by rfl) ⟨1574387, by rfl⟩ : syracuseStep 2099183 = 3148775) B3148775
theorem B3148781 : Blo 2097435 3148781 := bbase (se 3 (by rfl) ⟨590396, by rfl⟩ : syracuseStep 3148781 = 1180793) (by norm_num)
theorem B2099187 : Blo 2097435 2099187 := bstep (se 1 (by rfl) ⟨1574390, by rfl⟩ : syracuseStep 2099187 = 3148781) B3148781
theorem B4723181 : Blo 2097435 4723181 := bbase (se 3 (by rfl) ⟨885596, by rfl⟩ : syracuseStep 4723181 = 1771193) (by norm_num)
theorem B3148787 : Blo 2097435 3148787 := bstep (se 1 (by rfl) ⟨2361590, by rfl⟩ : syracuseStep 3148787 = 4723181) B4723181
theorem B2099191 : Blo 2097435 2099191 := bstep (se 1 (by rfl) ⟨1574393, by rfl⟩ : syracuseStep 2099191 = 3148787) B3148787
theorem B15131285 : Blo 2097435 15131285 := bbase (se 6 (by rfl) ⟨354639, by rfl⟩ : syracuseStep 15131285 = 709279) (by norm_num)
theorem B10087523 : Blo 2097435 10087523 := bstep (se 1 (by rfl) ⟨7565642, by rfl⟩ : syracuseStep 10087523 = 15131285) B15131285
theorem B6725015 : Blo 2097435 6725015 := bstep (se 1 (by rfl) ⟨5043761, by rfl⟩ : syracuseStep 6725015 = 10087523) B10087523
theorem B4483343 : Blo 2097435 4483343 := bstep (se 1 (by rfl) ⟨3362507, by rfl⟩ : syracuseStep 4483343 = 6725015) B6725015
theorem B2988895 : Blo 2097435 2988895 := bstep (se 1 (by rfl) ⟨2241671, by rfl⟩ : syracuseStep 2988895 = 4483343) B4483343
theorem B3985193 : Blo 2097435 3985193 := bstep (se 2 (by rfl) ⟨1494447, by rfl⟩ : syracuseStep 3985193 = 2988895) B2988895
theorem B2656795 : Blo 2097435 2656795 := bstep (se 1 (by rfl) ⟨1992596, by rfl⟩ : syracuseStep 2656795 = 3985193) B3985193
theorem B3542393 : Blo 2097435 3542393 := bstep (se 2 (by rfl) ⟨1328397, by rfl⟩ : syracuseStep 3542393 = 2656795) B2656795
theorem B2361595 : Blo 2097435 2361595 := bstep (se 1 (by rfl) ⟨1771196, by rfl⟩ : syracuseStep 2361595 = 3542393) B3542393
theorem B3148793 : Blo 2097435 3148793 := bstep (se 2 (by rfl) ⟨1180797, by rfl⟩ : syracuseStep 3148793 = 2361595) B2361595
theorem B2099195 : Blo 2097435 2099195 := bstep (se 1 (by rfl) ⟨1574396, by rfl⟩ : syracuseStep 2099195 = 3148793) B3148793
theorem B49136213 : Blo 2097435 49136213 := bbase (se 8 (by rfl) ⟨287907, by rfl⟩ : syracuseStep 49136213 = 575815) (by norm_num)
theorem B32757475 : Blo 2097435 32757475 := bstep (se 1 (by rfl) ⟨24568106, by rfl⟩ : syracuseStep 32757475 = 49136213) B49136213
theorem B43676633 : Blo 2097435 43676633 := bstep (se 2 (by rfl) ⟨16378737, by rfl⟩ : syracuseStep 43676633 = 32757475) B32757475
theorem B29117755 : Blo 2097435 29117755 := bstep (se 1 (by rfl) ⟨21838316, by rfl⟩ : syracuseStep 29117755 = 43676633) B43676633
theorem B38823673 : Blo 2097435 38823673 := bstep (se 2 (by rfl) ⟨14558877, by rfl⟩ : syracuseStep 38823673 = 29117755) B29117755
theorem B51764897 : Blo 2097435 51764897 := bstep (se 2 (by rfl) ⟨19411836, by rfl⟩ : syracuseStep 51764897 = 38823673) B38823673
theorem B34509931 : Blo 2097435 34509931 := bstep (se 1 (by rfl) ⟨25882448, by rfl⟩ : syracuseStep 34509931 = 51764897) B51764897
theorem B736211861 : Blo 2097435 736211861 := bstep (se 6 (by rfl) ⟨17254965, by rfl⟩ : syracuseStep 736211861 = 34509931) B34509931
theorem B490807907 : Blo 2097435 490807907 := bstep (se 1 (by rfl) ⟨368105930, by rfl⟩ : syracuseStep 490807907 = 736211861) B736211861
theorem B327205271 : Blo 2097435 327205271 := bstep (se 1 (by rfl) ⟨245403953, by rfl⟩ : syracuseStep 327205271 = 490807907) B490807907
theorem B872547389 : Blo 2097435 872547389 := bstep (se 3 (by rfl) ⟨163602635, by rfl⟩ : syracuseStep 872547389 = 327205271) B327205271
theorem B581698259 : Blo 2097435 581698259 := bstep (se 1 (by rfl) ⟨436273694, by rfl⟩ : syracuseStep 581698259 = 872547389) B872547389
theorem B387798839 : Blo 2097435 387798839 := bstep (se 1 (by rfl) ⟨290849129, by rfl⟩ : syracuseStep 387798839 = 581698259) B581698259
theorem B258532559 : Blo 2097435 258532559 := bstep (se 1 (by rfl) ⟨193899419, by rfl⟩ : syracuseStep 258532559 = 387798839) B387798839
theorem B172355039 : Blo 2097435 172355039 := bstep (se 1 (by rfl) ⟨129266279, by rfl⟩ : syracuseStep 172355039 = 258532559) B258532559
theorem B114903359 : Blo 2097435 114903359 := bstep (se 1 (by rfl) ⟨86177519, by rfl⟩ : syracuseStep 114903359 = 172355039) B172355039
theorem B76602239 : Blo 2097435 76602239 := bstep (se 1 (by rfl) ⟨57451679, by rfl⟩ : syracuseStep 76602239 = 114903359) B114903359
theorem B51068159 : Blo 2097435 51068159 := bstep (se 1 (by rfl) ⟨38301119, by rfl⟩ : syracuseStep 51068159 = 76602239) B76602239
theorem B34045439 : Blo 2097435 34045439 := bstep (se 1 (by rfl) ⟨25534079, by rfl⟩ : syracuseStep 34045439 = 51068159) B51068159
theorem B90787837 : Blo 2097435 90787837 := bstep (se 3 (by rfl) ⟨17022719, by rfl⟩ : syracuseStep 90787837 = 34045439) B34045439
theorem B121050449 : Blo 2097435 121050449 := bstep (se 2 (by rfl) ⟨45393918, by rfl⟩ : syracuseStep 121050449 = 90787837) B90787837
theorem B80700299 : Blo 2097435 80700299 := bstep (se 1 (by rfl) ⟨60525224, by rfl⟩ : syracuseStep 80700299 = 121050449) B121050449
theorem B53800199 : Blo 2097435 53800199 := bstep (se 1 (by rfl) ⟨40350149, by rfl⟩ : syracuseStep 53800199 = 80700299) B80700299
theorem B35866799 : Blo 2097435 35866799 := bstep (se 1 (by rfl) ⟨26900099, by rfl⟩ : syracuseStep 35866799 = 53800199) B53800199
theorem B23911199 : Blo 2097435 23911199 := bstep (se 1 (by rfl) ⟨17933399, by rfl⟩ : syracuseStep 23911199 = 35866799) B35866799
theorem B15940799 : Blo 2097435 15940799 := bstep (se 1 (by rfl) ⟨11955599, by rfl⟩ : syracuseStep 15940799 = 23911199) B23911199
theorem B10627199 : Blo 2097435 10627199 := bstep (se 1 (by rfl) ⟨7970399, by rfl⟩ : syracuseStep 10627199 = 15940799) B15940799
theorem B7084799 : Blo 2097435 7084799 := bstep (se 1 (by rfl) ⟨5313599, by rfl⟩ : syracuseStep 7084799 = 10627199) B10627199
theorem B4723199 : Blo 2097435 4723199 := bstep (se 1 (by rfl) ⟨3542399, by rfl⟩ : syracuseStep 4723199 = 7084799) B7084799
theorem B3148799 : Blo 2097435 3148799 := bstep (se 1 (by rfl) ⟨2361599, by rfl⟩ : syracuseStep 3148799 = 4723199) B4723199
theorem B2099199 : Blo 2097435 2099199 := bstep (se 1 (by rfl) ⟨1574399, by rfl⟩ : syracuseStep 2099199 = 3148799) B3148799
theorem B3148805 : Blo 2097435 3148805 := bbase (se 4 (by rfl) ⟨295200, by rfl⟩ : syracuseStep 3148805 = 590401) (by norm_num)
theorem B2099203 : Blo 2097435 2099203 := bstep (se 1 (by rfl) ⟨1574402, by rfl⟩ : syracuseStep 2099203 = 3148805) B3148805
theorem B3542413 : Blo 2097435 3542413 := bbase (se 3 (by rfl) ⟨664202, by rfl⟩ : syracuseStep 3542413 = 1328405) (by norm_num)
theorem B4723217 : Blo 2097435 4723217 := bstep (se 2 (by rfl) ⟨1771206, by rfl⟩ : syracuseStep 4723217 = 3542413) B3542413
theorem B3148811 : Blo 2097435 3148811 := bstep (se 1 (by rfl) ⟨2361608, by rfl⟩ : syracuseStep 3148811 = 4723217) B4723217
theorem B2099207 : Blo 2097435 2099207 := bstep (se 1 (by rfl) ⟨1574405, by rfl⟩ : syracuseStep 2099207 = 3148811) B3148811
theorem B2361613 : Blo 2097435 2361613 := bbase (se 3 (by rfl) ⟨442802, by rfl⟩ : syracuseStep 2361613 = 885605) (by norm_num)
theorem B3148817 : Blo 2097435 3148817 := bstep (se 2 (by rfl) ⟨1180806, by rfl⟩ : syracuseStep 3148817 = 2361613) B2361613
theorem B2099211 : Blo 2097435 2099211 := bstep (se 1 (by rfl) ⟨1574408, by rfl⟩ : syracuseStep 2099211 = 3148817) B3148817
theorem B7084853 : Blo 2097435 7084853 := bbase (se 5 (by rfl) ⟨332102, by rfl⟩ : syracuseStep 7084853 = 664205) (by norm_num)
theorem B4723235 : Blo 2097435 4723235 := bstep (se 1 (by rfl) ⟨3542426, by rfl⟩ : syracuseStep 4723235 = 7084853) B7084853
theorem B3148823 : Blo 2097435 3148823 := bstep (se 1 (by rfl) ⟨2361617, by rfl⟩ : syracuseStep 3148823 = 4723235) B4723235
theorem B2099215 : Blo 2097435 2099215 := bstep (se 1 (by rfl) ⟨1574411, by rfl⟩ : syracuseStep 2099215 = 3148823) B3148823
theorem B3148829 : Blo 2097435 3148829 := bbase (se 3 (by rfl) ⟨590405, by rfl⟩ : syracuseStep 3148829 = 1180811) (by norm_num)
theorem B2099219 : Blo 2097435 2099219 := bstep (se 1 (by rfl) ⟨1574414, by rfl⟩ : syracuseStep 2099219 = 3148829) B3148829
theorem B4723253 : Blo 2097435 4723253 := bbase (se 5 (by rfl) ⟨221402, by rfl⟩ : syracuseStep 4723253 = 442805) (by norm_num)
theorem B3148835 : Blo 2097435 3148835 := bstep (se 1 (by rfl) ⟨2361626, by rfl⟩ : syracuseStep 3148835 = 4723253) B4723253
theorem B2099223 : Blo 2097435 2099223 := bstep (se 1 (by rfl) ⟨1574417, by rfl⟩ : syracuseStep 2099223 = 3148835) B3148835
theorem B8966821 : Blo 2097435 8966821 := bbase (se 4 (by rfl) ⟨840639, by rfl⟩ : syracuseStep 8966821 = 1681279) (by norm_num)
theorem B11955761 : Blo 2097435 11955761 := bstep (se 2 (by rfl) ⟨4483410, by rfl⟩ : syracuseStep 11955761 = 8966821) B8966821
theorem B7970507 : Blo 2097435 7970507 := bstep (se 1 (by rfl) ⟨5977880, by rfl⟩ : syracuseStep 7970507 = 11955761) B11955761
theorem B5313671 : Blo 2097435 5313671 := bstep (se 1 (by rfl) ⟨3985253, by rfl⟩ : syracuseStep 5313671 = 7970507) B7970507
theorem B3542447 : Blo 2097435 3542447 := bstep (se 1 (by rfl) ⟨2656835, by rfl⟩ : syracuseStep 3542447 = 5313671) B5313671
theorem B2361631 : Blo 2097435 2361631 := bstep (se 1 (by rfl) ⟨1771223, by rfl⟩ : syracuseStep 2361631 = 3542447) B3542447
theorem B3148841 : Blo 2097435 3148841 := bstep (se 2 (by rfl) ⟨1180815, by rfl⟩ : syracuseStep 3148841 = 2361631) B2361631
theorem B2099227 : Blo 2097435 2099227 := bstep (se 1 (by rfl) ⟨1574420, by rfl⟩ : syracuseStep 2099227 = 3148841) B3148841
theorem B8966837 : Blo 2097435 8966837 := bbase (se 5 (by rfl) ⟨420320, by rfl⟩ : syracuseStep 8966837 = 840641) (by norm_num)
theorem B5977891 : Blo 2097435 5977891 := bstep (se 1 (by rfl) ⟨4483418, by rfl⟩ : syracuseStep 5977891 = 8966837) B8966837
theorem B7970521 : Blo 2097435 7970521 := bstep (se 2 (by rfl) ⟨2988945, by rfl⟩ : syracuseStep 7970521 = 5977891) B5977891
theorem B10627361 : Blo 2097435 10627361 := bstep (se 2 (by rfl) ⟨3985260, by rfl⟩ : syracuseStep 10627361 = 7970521) B7970521
theorem B7084907 : Blo 2097435 7084907 := bstep (se 1 (by rfl) ⟨5313680, by rfl⟩ : syracuseStep 7084907 = 10627361) B10627361
theorem B4723271 : Blo 2097435 4723271 := bstep (se 1 (by rfl) ⟨3542453, by rfl⟩ : syracuseStep 4723271 = 7084907) B7084907
theorem B3148847 : Blo 2097435 3148847 := bstep (se 1 (by rfl) ⟨2361635, by rfl⟩ : syracuseStep 3148847 = 4723271) B4723271
theorem B2099231 : Blo 2097435 2099231 := bstep (se 1 (by rfl) ⟨1574423, by rfl⟩ : syracuseStep 2099231 = 3148847) B3148847
theorem B3148853 : Blo 2097435 3148853 := bbase (se 5 (by rfl) ⟨147602, by rfl⟩ : syracuseStep 3148853 = 295205) (by norm_num)
theorem B2099235 : Blo 2097435 2099235 := bstep (se 1 (by rfl) ⟨1574426, by rfl⟩ : syracuseStep 2099235 = 3148853) B3148853
theorem B5313701 : Blo 2097435 5313701 := bbase (se 4 (by rfl) ⟨498159, by rfl⟩ : syracuseStep 5313701 = 996319) (by norm_num)
theorem B3542467 : Blo 2097435 3542467 := bstep (se 1 (by rfl) ⟨2656850, by rfl⟩ : syracuseStep 3542467 = 5313701) B5313701
theorem B4723289 : Blo 2097435 4723289 := bstep (se 2 (by rfl) ⟨1771233, by rfl⟩ : syracuseStep 4723289 = 3542467) B3542467
theorem B3148859 : Blo 2097435 3148859 := bstep (se 1 (by rfl) ⟨2361644, by rfl⟩ : syracuseStep 3148859 = 4723289) B4723289
theorem B2099239 : Blo 2097435 2099239 := bstep (se 1 (by rfl) ⟨1574429, by rfl⟩ : syracuseStep 2099239 = 3148859) B3148859
theorem B2361649 : Blo 2097435 2361649 := bbase (se 2 (by rfl) ⟨885618, by rfl⟩ : syracuseStep 2361649 = 1771237) (by norm_num)
theorem B3148865 : Blo 2097435 3148865 := bstep (se 2 (by rfl) ⟨1180824, by rfl⟩ : syracuseStep 3148865 = 2361649) B2361649
theorem B2099243 : Blo 2097435 2099243 := bstep (se 1 (by rfl) ⟨1574432, by rfl⟩ : syracuseStep 2099243 = 3148865) B3148865
theorem B4483453 : Blo 2097435 4483453 := bbase (se 3 (by rfl) ⟨840647, by rfl⟩ : syracuseStep 4483453 = 1681295) (by norm_num)
theorem B5977937 : Blo 2097435 5977937 := bstep (se 2 (by rfl) ⟨2241726, by rfl⟩ : syracuseStep 5977937 = 4483453) B4483453
theorem B3985291 : Blo 2097435 3985291 := bstep (se 1 (by rfl) ⟨2988968, by rfl⟩ : syracuseStep 3985291 = 5977937) B5977937
theorem B5313721 : Blo 2097435 5313721 := bstep (se 2 (by rfl) ⟨1992645, by rfl⟩ : syracuseStep 5313721 = 3985291) B3985291
theorem B7084961 : Blo 2097435 7084961 := bstep (se 2 (by rfl) ⟨2656860, by rfl⟩ : syracuseStep 7084961 = 5313721) B5313721
theorem B4723307 : Blo 2097435 4723307 := bstep (se 1 (by rfl) ⟨3542480, by rfl⟩ : syracuseStep 4723307 = 7084961) B7084961
theorem B3148871 : Blo 2097435 3148871 := bstep (se 1 (by rfl) ⟨2361653, by rfl⟩ : syracuseStep 3148871 = 4723307) B4723307
theorem B2099247 : Blo 2097435 2099247 := bstep (se 1 (by rfl) ⟨1574435, by rfl⟩ : syracuseStep 2099247 = 3148871) B3148871
theorem B3148877 : Blo 2097435 3148877 := bbase (se 3 (by rfl) ⟨590414, by rfl⟩ : syracuseStep 3148877 = 1180829) (by norm_num)
theorem B2099251 : Blo 2097435 2099251 := bstep (se 1 (by rfl) ⟨1574438, by rfl⟩ : syracuseStep 2099251 = 3148877) B3148877
theorem B4723325 : Blo 2097435 4723325 := bbase (se 3 (by rfl) ⟨885623, by rfl⟩ : syracuseStep 4723325 = 1771247) (by norm_num)
theorem B3148883 : Blo 2097435 3148883 := bstep (se 1 (by rfl) ⟨2361662, by rfl⟩ : syracuseStep 3148883 = 4723325) B4723325
theorem B2099255 : Blo 2097435 2099255 := bstep (se 1 (by rfl) ⟨1574441, by rfl⟩ : syracuseStep 2099255 = 3148883) B3148883
theorem B3542501 : Blo 2097435 3542501 := bbase (se 4 (by rfl) ⟨332109, by rfl⟩ : syracuseStep 3542501 = 664219) (by norm_num)
theorem B2361667 : Blo 2097435 2361667 := bstep (se 1 (by rfl) ⟨1771250, by rfl⟩ : syracuseStep 2361667 = 3542501) B3542501
theorem B3148889 : Blo 2097435 3148889 := bstep (se 2 (by rfl) ⟨1180833, by rfl⟩ : syracuseStep 3148889 = 2361667) B2361667
theorem B2099259 : Blo 2097435 2099259 := bstep (se 1 (by rfl) ⟨1574444, by rfl⟩ : syracuseStep 2099259 = 3148889) B3148889
theorem B5386261 : Blo 2097435 5386261 := bbase (se 6 (by rfl) ⟨126240, by rfl⟩ : syracuseStep 5386261 = 252481) (by norm_num)
theorem B7181681 : Blo 2097435 7181681 := bstep (se 2 (by rfl) ⟨2693130, by rfl⟩ : syracuseStep 7181681 = 5386261) B5386261
theorem B19151149 : Blo 2097435 19151149 := bstep (se 3 (by rfl) ⟨3590840, by rfl⟩ : syracuseStep 19151149 = 7181681) B7181681
theorem B25534865 : Blo 2097435 25534865 := bstep (se 2 (by rfl) ⟨9575574, by rfl⟩ : syracuseStep 25534865 = 19151149) B19151149
theorem B17023243 : Blo 2097435 17023243 := bstep (se 1 (by rfl) ⟨12767432, by rfl⟩ : syracuseStep 17023243 = 25534865) B25534865
theorem B22697657 : Blo 2097435 22697657 := bstep (se 2 (by rfl) ⟨8511621, by rfl⟩ : syracuseStep 22697657 = 17023243) B17023243
theorem B15131771 : Blo 2097435 15131771 := bstep (se 1 (by rfl) ⟨11348828, by rfl⟩ : syracuseStep 15131771 = 22697657) B22697657
theorem B10087847 : Blo 2097435 10087847 := bstep (se 1 (by rfl) ⟨7565885, by rfl⟩ : syracuseStep 10087847 = 15131771) B15131771
theorem B6725231 : Blo 2097435 6725231 := bstep (se 1 (by rfl) ⟨5043923, by rfl⟩ : syracuseStep 6725231 = 10087847) B10087847
theorem B4483487 : Blo 2097435 4483487 := bstep (se 1 (by rfl) ⟨3362615, by rfl⟩ : syracuseStep 4483487 = 6725231) B6725231
theorem B2988991 : Blo 2097435 2988991 := bstep (se 1 (by rfl) ⟨2241743, by rfl⟩ : syracuseStep 2988991 = 4483487) B4483487
theorem B15941285 : Blo 2097435 15941285 := bstep (se 4 (by rfl) ⟨1494495, by rfl⟩ : syracuseStep 15941285 = 2988991) B2988991
theorem B10627523 : Blo 2097435 10627523 := bstep (se 1 (by rfl) ⟨7970642, by rfl⟩ : syracuseStep 10627523 = 15941285) B15941285
theorem B7085015 : Blo 2097435 7085015 := bstep (se 1 (by rfl) ⟨5313761, by rfl⟩ : syracuseStep 7085015 = 10627523) B10627523
theorem B4723343 : Blo 2097435 4723343 := bstep (se 1 (by rfl) ⟨3542507, by rfl⟩ : syracuseStep 4723343 = 7085015) B7085015
theorem B3148895 : Blo 2097435 3148895 := bstep (se 1 (by rfl) ⟨2361671, by rfl⟩ : syracuseStep 3148895 = 4723343) B4723343
theorem B2099263 : Blo 2097435 2099263 := bstep (se 1 (by rfl) ⟨1574447, by rfl⟩ : syracuseStep 2099263 = 3148895) B3148895
theorem B3148901 : Blo 2097435 3148901 := bbase (se 4 (by rfl) ⟨295209, by rfl⟩ : syracuseStep 3148901 = 590419) (by norm_num)
theorem B2099267 : Blo 2097435 2099267 := bstep (se 1 (by rfl) ⟨1574450, by rfl⟩ : syracuseStep 2099267 = 3148901) B3148901
theorem B3362629 : Blo 2097435 3362629 := bbase (se 4 (by rfl) ⟨315246, by rfl⟩ : syracuseStep 3362629 = 630493) (by norm_num)
theorem B4483505 : Blo 2097435 4483505 := bstep (se 2 (by rfl) ⟨1681314, by rfl⟩ : syracuseStep 4483505 = 3362629) B3362629
theorem B2989003 : Blo 2097435 2989003 := bstep (se 1 (by rfl) ⟨2241752, by rfl⟩ : syracuseStep 2989003 = 4483505) B4483505
theorem B3985337 : Blo 2097435 3985337 := bstep (se 2 (by rfl) ⟨1494501, by rfl⟩ : syracuseStep 3985337 = 2989003) B2989003
theorem B2656891 : Blo 2097435 2656891 := bstep (se 1 (by rfl) ⟨1992668, by rfl⟩ : syracuseStep 2656891 = 3985337) B3985337
theorem B3542521 : Blo 2097435 3542521 := bstep (se 2 (by rfl) ⟨1328445, by rfl⟩ : syracuseStep 3542521 = 2656891) B2656891
theorem B4723361 : Blo 2097435 4723361 := bstep (se 2 (by rfl) ⟨1771260, by rfl⟩ : syracuseStep 4723361 = 3542521) B3542521
theorem B3148907 : Blo 2097435 3148907 := bstep (se 1 (by rfl) ⟨2361680, by rfl⟩ : syracuseStep 3148907 = 4723361) B4723361
theorem B2099271 : Blo 2097435 2099271 := bstep (se 1 (by rfl) ⟨1574453, by rfl⟩ : syracuseStep 2099271 = 3148907) B3148907
theorem B2361685 : Blo 2097435 2361685 := bbase (se 10 (by rfl) ⟨3459, by rfl⟩ : syracuseStep 2361685 = 6919) (by norm_num)
theorem B3148913 : Blo 2097435 3148913 := bstep (se 2 (by rfl) ⟨1180842, by rfl⟩ : syracuseStep 3148913 = 2361685) B2361685
theorem B2099275 : Blo 2097435 2099275 := bstep (se 1 (by rfl) ⟨1574456, by rfl⟩ : syracuseStep 2099275 = 3148913) B3148913
theorem B2656901 : Blo 2097435 2656901 := bbase (se 4 (by rfl) ⟨249084, by rfl⟩ : syracuseStep 2656901 = 498169) (by norm_num)
theorem B7085069 : Blo 2097435 7085069 := bstep (se 3 (by rfl) ⟨1328450, by rfl⟩ : syracuseStep 7085069 = 2656901) B2656901
theorem B4723379 : Blo 2097435 4723379 := bstep (se 1 (by rfl) ⟨3542534, by rfl⟩ : syracuseStep 4723379 = 7085069) B7085069
theorem B3148919 : Blo 2097435 3148919 := bstep (se 1 (by rfl) ⟨2361689, by rfl⟩ : syracuseStep 3148919 = 4723379) B4723379
theorem B2099279 : Blo 2097435 2099279 := bstep (se 1 (by rfl) ⟨1574459, by rfl⟩ : syracuseStep 2099279 = 3148919) B3148919
theorem B3148925 : Blo 2097435 3148925 := bbase (se 3 (by rfl) ⟨590423, by rfl⟩ : syracuseStep 3148925 = 1180847) (by norm_num)
theorem B2099283 : Blo 2097435 2099283 := bstep (se 1 (by rfl) ⟨1574462, by rfl⟩ : syracuseStep 2099283 = 3148925) B3148925
theorem B4723397 : Blo 2097435 4723397 := bbase (se 4 (by rfl) ⟨442818, by rfl⟩ : syracuseStep 4723397 = 885637) (by norm_num)
theorem B3148931 : Blo 2097435 3148931 := bstep (se 1 (by rfl) ⟨2361698, by rfl⟩ : syracuseStep 3148931 = 4723397) B4723397
theorem B2099287 : Blo 2097435 2099287 := bstep (se 1 (by rfl) ⟨1574465, by rfl⟩ : syracuseStep 2099287 = 3148931) B3148931
theorem B11348981 : Blo 2097435 11348981 := bbase (se 5 (by rfl) ⟨531983, by rfl⟩ : syracuseStep 11348981 = 1063967) (by norm_num)
theorem B7565987 : Blo 2097435 7565987 := bstep (se 1 (by rfl) ⟨5674490, by rfl⟩ : syracuseStep 7565987 = 11348981) B11348981
theorem B20175965 : Blo 2097435 20175965 := bstep (se 3 (by rfl) ⟨3782993, by rfl⟩ : syracuseStep 20175965 = 7565987) B7565987
theorem B13450643 : Blo 2097435 13450643 := bstep (se 1 (by rfl) ⟨10087982, by rfl⟩ : syracuseStep 13450643 = 20175965) B20175965
theorem B8967095 : Blo 2097435 8967095 := bstep (se 1 (by rfl) ⟨6725321, by rfl⟩ : syracuseStep 8967095 = 13450643) B13450643
theorem B5978063 : Blo 2097435 5978063 := bstep (se 1 (by rfl) ⟨4483547, by rfl⟩ : syracuseStep 5978063 = 8967095) B8967095
theorem B3985375 : Blo 2097435 3985375 := bstep (se 1 (by rfl) ⟨2989031, by rfl⟩ : syracuseStep 3985375 = 5978063) B5978063
theorem B5313833 : Blo 2097435 5313833 := bstep (se 2 (by rfl) ⟨1992687, by rfl⟩ : syracuseStep 5313833 = 3985375) B3985375
theorem B3542555 : Blo 2097435 3542555 := bstep (se 1 (by rfl) ⟨2656916, by rfl⟩ : syracuseStep 3542555 = 5313833) B5313833
theorem B2361703 : Blo 2097435 2361703 := bstep (se 1 (by rfl) ⟨1771277, by rfl⟩ : syracuseStep 2361703 = 3542555) B3542555
theorem B3148937 : Blo 2097435 3148937 := bstep (se 2 (by rfl) ⟨1180851, by rfl⟩ : syracuseStep 3148937 = 2361703) B2361703
theorem B2099291 : Blo 2097435 2099291 := bstep (se 1 (by rfl) ⟨1574468, by rfl⟩ : syracuseStep 2099291 = 3148937) B3148937
theorem B10627685 : Blo 2097435 10627685 := bbase (se 4 (by rfl) ⟨996345, by rfl⟩ : syracuseStep 10627685 = 1992691) (by norm_num)
theorem B7085123 : Blo 2097435 7085123 := bstep (se 1 (by rfl) ⟨5313842, by rfl⟩ : syracuseStep 7085123 = 10627685) B10627685
theorem B4723415 : Blo 2097435 4723415 := bstep (se 1 (by rfl) ⟨3542561, by rfl⟩ : syracuseStep 4723415 = 7085123) B7085123
theorem B3148943 : Blo 2097435 3148943 := bstep (se 1 (by rfl) ⟨2361707, by rfl⟩ : syracuseStep 3148943 = 4723415) B4723415
theorem B2099295 : Blo 2097435 2099295 := bstep (se 1 (by rfl) ⟨1574471, by rfl⟩ : syracuseStep 2099295 = 3148943) B3148943
theorem B3148949 : Blo 2097435 3148949 := bbase (se 6 (by rfl) ⟨73803, by rfl⟩ : syracuseStep 3148949 = 147607) (by norm_num)
theorem B2099299 : Blo 2097435 2099299 := bstep (se 1 (by rfl) ⟨1574474, by rfl⟩ : syracuseStep 2099299 = 3148949) B3148949
theorem B3834629 : Blo 2097435 3834629 := bbase (se 4 (by rfl) ⟨359496, by rfl⟩ : syracuseStep 3834629 = 718993) (by norm_num)
theorem B2556419 : Blo 2097435 2556419 := bstep (se 1 (by rfl) ⟨1917314, by rfl⟩ : syracuseStep 2556419 = 3834629) B3834629
theorem B6817117 : Blo 2097435 6817117 := bstep (se 3 (by rfl) ⟨1278209, by rfl⟩ : syracuseStep 6817117 = 2556419) B2556419
theorem B9089489 : Blo 2097435 9089489 := bstep (se 2 (by rfl) ⟨3408558, by rfl⟩ : syracuseStep 9089489 = 6817117) B6817117
theorem B6059659 : Blo 2097435 6059659 := bstep (se 1 (by rfl) ⟨4544744, by rfl⟩ : syracuseStep 6059659 = 9089489) B9089489
theorem B8079545 : Blo 2097435 8079545 := bstep (se 2 (by rfl) ⟨3029829, by rfl⟩ : syracuseStep 8079545 = 6059659) B6059659
theorem B21545453 : Blo 2097435 21545453 := bstep (se 3 (by rfl) ⟨4039772, by rfl⟩ : syracuseStep 21545453 = 8079545) B8079545
theorem B57454541 : Blo 2097435 57454541 := bstep (se 3 (by rfl) ⟨10772726, by rfl⟩ : syracuseStep 57454541 = 21545453) B21545453
theorem B38303027 : Blo 2097435 38303027 := bstep (se 1 (by rfl) ⟨28727270, by rfl⟩ : syracuseStep 38303027 = 57454541) B57454541
theorem B25535351 : Blo 2097435 25535351 := bstep (se 1 (by rfl) ⟨19151513, by rfl⟩ : syracuseStep 25535351 = 38303027) B38303027
theorem B17023567 : Blo 2097435 17023567 := bstep (se 1 (by rfl) ⟨12767675, by rfl⟩ : syracuseStep 17023567 = 25535351) B25535351
theorem B22698089 : Blo 2097435 22698089 := bstep (se 2 (by rfl) ⟨8511783, by rfl⟩ : syracuseStep 22698089 = 17023567) B17023567
theorem B15132059 : Blo 2097435 15132059 := bstep (se 1 (by rfl) ⟨11349044, by rfl⟩ : syracuseStep 15132059 = 22698089) B22698089
theorem B10088039 : Blo 2097435 10088039 := bstep (se 1 (by rfl) ⟨7566029, by rfl⟩ : syracuseStep 10088039 = 15132059) B15132059
theorem B6725359 : Blo 2097435 6725359 := bstep (se 1 (by rfl) ⟨5044019, by rfl⟩ : syracuseStep 6725359 = 10088039) B10088039
theorem B8967145 : Blo 2097435 8967145 := bstep (se 2 (by rfl) ⟨3362679, by rfl⟩ : syracuseStep 8967145 = 6725359) B6725359
theorem B11956193 : Blo 2097435 11956193 := bstep (se 2 (by rfl) ⟨4483572, by rfl⟩ : syracuseStep 11956193 = 8967145) B8967145
theorem B7970795 : Blo 2097435 7970795 := bstep (se 1 (by rfl) ⟨5978096, by rfl⟩ : syracuseStep 7970795 = 11956193) B11956193
theorem B5313863 : Blo 2097435 5313863 := bstep (se 1 (by rfl) ⟨3985397, by rfl⟩ : syracuseStep 5313863 = 7970795) B7970795
theorem B3542575 : Blo 2097435 3542575 := bstep (se 1 (by rfl) ⟨2656931, by rfl⟩ : syracuseStep 3542575 = 5313863) B5313863
theorem B4723433 : Blo 2097435 4723433 := bstep (se 2 (by rfl) ⟨1771287, by rfl⟩ : syracuseStep 4723433 = 3542575) B3542575
theorem B3148955 : Blo 2097435 3148955 := bstep (se 1 (by rfl) ⟨2361716, by rfl⟩ : syracuseStep 3148955 = 4723433) B4723433
theorem B2099303 : Blo 2097435 2099303 := bstep (se 1 (by rfl) ⟨1574477, by rfl⟩ : syracuseStep 2099303 = 3148955) B3148955
theorem B2361721 : Blo 2097435 2361721 := bbase (se 2 (by rfl) ⟨885645, by rfl⟩ : syracuseStep 2361721 = 1771291) (by norm_num)
theorem B3148961 : Blo 2097435 3148961 := bstep (se 2 (by rfl) ⟨1180860, by rfl⟩ : syracuseStep 3148961 = 2361721) B2361721
theorem B2099307 : Blo 2097435 2099307 := bstep (se 1 (by rfl) ⟨1574480, by rfl⟩ : syracuseStep 2099307 = 3148961) B3148961
theorem B3783029 : Blo 2097435 3783029 := bbase (se 5 (by rfl) ⟨177329, by rfl⟩ : syracuseStep 3783029 = 354659) (by norm_num)
theorem B10088077 : Blo 2097435 10088077 := bstep (se 3 (by rfl) ⟨1891514, by rfl⟩ : syracuseStep 10088077 = 3783029) B3783029
theorem B13450769 : Blo 2097435 13450769 := bstep (se 2 (by rfl) ⟨5044038, by rfl⟩ : syracuseStep 13450769 = 10088077) B10088077
theorem B8967179 : Blo 2097435 8967179 := bstep (se 1 (by rfl) ⟨6725384, by rfl⟩ : syracuseStep 8967179 = 13450769) B13450769
theorem B5978119 : Blo 2097435 5978119 := bstep (se 1 (by rfl) ⟨4483589, by rfl⟩ : syracuseStep 5978119 = 8967179) B8967179
theorem B7970825 : Blo 2097435 7970825 := bstep (se 2 (by rfl) ⟨2989059, by rfl⟩ : syracuseStep 7970825 = 5978119) B5978119
theorem B5313883 : Blo 2097435 5313883 := bstep (se 1 (by rfl) ⟨3985412, by rfl⟩ : syracuseStep 5313883 = 7970825) B7970825
theorem B7085177 : Blo 2097435 7085177 := bstep (se 2 (by rfl) ⟨2656941, by rfl⟩ : syracuseStep 7085177 = 5313883) B5313883
theorem B4723451 : Blo 2097435 4723451 := bstep (se 1 (by rfl) ⟨3542588, by rfl⟩ : syracuseStep 4723451 = 7085177) B7085177
theorem B3148967 : Blo 2097435 3148967 := bstep (se 1 (by rfl) ⟨2361725, by rfl⟩ : syracuseStep 3148967 = 4723451) B4723451
theorem B2099311 : Blo 2097435 2099311 := bstep (se 1 (by rfl) ⟨1574483, by rfl⟩ : syracuseStep 2099311 = 3148967) B3148967
theorem B3148973 : Blo 2097435 3148973 := bbase (se 3 (by rfl) ⟨590432, by rfl⟩ : syracuseStep 3148973 = 1180865) (by norm_num)
theorem B2099315 : Blo 2097435 2099315 := bstep (se 1 (by rfl) ⟨1574486, by rfl⟩ : syracuseStep 2099315 = 3148973) B3148973
theorem B4723469 : Blo 2097435 4723469 := bbase (se 3 (by rfl) ⟨885650, by rfl⟩ : syracuseStep 4723469 = 1771301) (by norm_num)
theorem B3148979 : Blo 2097435 3148979 := bstep (se 1 (by rfl) ⟨2361734, by rfl⟩ : syracuseStep 3148979 = 4723469) B4723469
theorem B2099319 : Blo 2097435 2099319 := bstep (se 1 (by rfl) ⟨1574489, by rfl⟩ : syracuseStep 2099319 = 3148979) B3148979
theorem B2656957 : Blo 2097435 2656957 := bbase (se 3 (by rfl) ⟨498179, by rfl⟩ : syracuseStep 2656957 = 996359) (by norm_num)
theorem B3542609 : Blo 2097435 3542609 := bstep (se 2 (by rfl) ⟨1328478, by rfl⟩ : syracuseStep 3542609 = 2656957) B2656957
theorem B2361739 : Blo 2097435 2361739 := bstep (se 1 (by rfl) ⟨1771304, by rfl⟩ : syracuseStep 2361739 = 3542609) B3542609
theorem B3148985 : Blo 2097435 3148985 := bstep (se 2 (by rfl) ⟨1180869, by rfl⟩ : syracuseStep 3148985 = 2361739) B2361739
theorem B2099323 : Blo 2097435 2099323 := bstep (se 1 (by rfl) ⟨1574492, by rfl⟩ : syracuseStep 2099323 = 3148985) B3148985
theorem B11349173 : Blo 2097435 11349173 := bbase (se 5 (by rfl) ⟨531992, by rfl⟩ : syracuseStep 11349173 = 1063985) (by norm_num)
theorem B7566115 : Blo 2097435 7566115 := bstep (se 1 (by rfl) ⟨5674586, by rfl⟩ : syracuseStep 7566115 = 11349173) B11349173
theorem B10088153 : Blo 2097435 10088153 := bstep (se 2 (by rfl) ⟨3783057, by rfl⟩ : syracuseStep 10088153 = 7566115) B7566115
theorem B6725435 : Blo 2097435 6725435 := bstep (se 1 (by rfl) ⟨5044076, by rfl⟩ : syracuseStep 6725435 = 10088153) B10088153
theorem B17934493 : Blo 2097435 17934493 := bstep (se 3 (by rfl) ⟨3362717, by rfl⟩ : syracuseStep 17934493 = 6725435) B6725435
theorem B23912657 : Blo 2097435 23912657 := bstep (se 2 (by rfl) ⟨8967246, by rfl⟩ : syracuseStep 23912657 = 17934493) B17934493
theorem B15941771 : Blo 2097435 15941771 := bstep (se 1 (by rfl) ⟨11956328, by rfl⟩ : syracuseStep 15941771 = 23912657) B23912657
theorem B10627847 : Blo 2097435 10627847 := bstep (se 1 (by rfl) ⟨7970885, by rfl⟩ : syracuseStep 10627847 = 15941771) B15941771
theorem B7085231 : Blo 2097435 7085231 := bstep (se 1 (by rfl) ⟨5313923, by rfl⟩ : syracuseStep 7085231 = 10627847) B10627847
theorem B4723487 : Blo 2097435 4723487 := bstep (se 1 (by rfl) ⟨3542615, by rfl⟩ : syracuseStep 4723487 = 7085231) B7085231
theorem B3148991 : Blo 2097435 3148991 := bstep (se 1 (by rfl) ⟨2361743, by rfl⟩ : syracuseStep 3148991 = 4723487) B4723487
theorem B2099327 : Blo 2097435 2099327 := bstep (se 1 (by rfl) ⟨1574495, by rfl⟩ : syracuseStep 2099327 = 3148991) B3148991
theorem B3148997 : Blo 2097435 3148997 := bbase (se 4 (by rfl) ⟨295218, by rfl⟩ : syracuseStep 3148997 = 590437) (by norm_num)
theorem B2099331 : Blo 2097435 2099331 := bstep (se 1 (by rfl) ⟨1574498, by rfl⟩ : syracuseStep 2099331 = 3148997) B3148997
theorem B3542629 : Blo 2097435 3542629 := bbase (se 4 (by rfl) ⟨332121, by rfl⟩ : syracuseStep 3542629 = 664243) (by norm_num)
theorem B4723505 : Blo 2097435 4723505 := bstep (se 2 (by rfl) ⟨1771314, by rfl⟩ : syracuseStep 4723505 = 3542629) B3542629
theorem B3149003 : Blo 2097435 3149003 := bstep (se 1 (by rfl) ⟨2361752, by rfl⟩ : syracuseStep 3149003 = 4723505) B4723505
theorem B2099335 : Blo 2097435 2099335 := bstep (se 1 (by rfl) ⟨1574501, by rfl⟩ : syracuseStep 2099335 = 3149003) B3149003
theorem B2361757 : Blo 2097435 2361757 := bbase (se 3 (by rfl) ⟨442829, by rfl⟩ : syracuseStep 2361757 = 885659) (by norm_num)
theorem B3149009 : Blo 2097435 3149009 := bstep (se 2 (by rfl) ⟨1180878, by rfl⟩ : syracuseStep 3149009 = 2361757) B2361757
theorem B2099339 : Blo 2097435 2099339 := bstep (se 1 (by rfl) ⟨1574504, by rfl⟩ : syracuseStep 2099339 = 3149009) B3149009
theorem B7085285 : Blo 2097435 7085285 := bbase (se 4 (by rfl) ⟨664245, by rfl⟩ : syracuseStep 7085285 = 1328491) (by norm_num)
theorem B4723523 : Blo 2097435 4723523 := bstep (se 1 (by rfl) ⟨3542642, by rfl⟩ : syracuseStep 4723523 = 7085285) B7085285
theorem B3149015 : Blo 2097435 3149015 := bstep (se 1 (by rfl) ⟨2361761, by rfl⟩ : syracuseStep 3149015 = 4723523) B4723523
theorem B2099343 : Blo 2097435 2099343 := bstep (se 1 (by rfl) ⟨1574507, by rfl⟩ : syracuseStep 2099343 = 3149015) B3149015
theorem B3149021 : Blo 2097435 3149021 := bbase (se 3 (by rfl) ⟨590441, by rfl⟩ : syracuseStep 3149021 = 1180883) (by norm_num)
theorem B2099347 : Blo 2097435 2099347 := bstep (se 1 (by rfl) ⟨1574510, by rfl⟩ : syracuseStep 2099347 = 3149021) B3149021
theorem B4723541 : Blo 2097435 4723541 := bbase (se 9 (by rfl) ⟨13838, by rfl⟩ : syracuseStep 4723541 = 27677) (by norm_num)
theorem B3149027 : Blo 2097435 3149027 := bstep (se 1 (by rfl) ⟨2361770, by rfl⟩ : syracuseStep 3149027 = 4723541) B4723541
theorem B2099351 : Blo 2097435 2099351 := bstep (se 1 (by rfl) ⟨1574513, by rfl⟩ : syracuseStep 2099351 = 3149027) B3149027
theorem B5978245 : Blo 2097435 5978245 := bbase (se 4 (by rfl) ⟨560460, by rfl⟩ : syracuseStep 5978245 = 1120921) (by norm_num)
theorem B7970993 : Blo 2097435 7970993 := bstep (se 2 (by rfl) ⟨2989122, by rfl⟩ : syracuseStep 7970993 = 5978245) B5978245
theorem B5313995 : Blo 2097435 5313995 := bstep (se 1 (by rfl) ⟨3985496, by rfl⟩ : syracuseStep 5313995 = 7970993) B7970993
theorem B3542663 : Blo 2097435 3542663 := bstep (se 1 (by rfl) ⟨2656997, by rfl⟩ : syracuseStep 3542663 = 5313995) B5313995
theorem B2361775 : Blo 2097435 2361775 := bstep (se 1 (by rfl) ⟨1771331, by rfl⟩ : syracuseStep 2361775 = 3542663) B3542663
theorem B3149033 : Blo 2097435 3149033 := bstep (se 2 (by rfl) ⟨1180887, by rfl⟩ : syracuseStep 3149033 = 2361775) B2361775
theorem B2099355 : Blo 2097435 2099355 := bstep (se 1 (by rfl) ⟨1574516, by rfl⟩ : syracuseStep 2099355 = 3149033) B3149033
theorem B10773013 : Blo 2097435 10773013 := bbase (se 6 (by rfl) ⟨252492, by rfl⟩ : syracuseStep 10773013 = 504985) (by norm_num)
theorem B14364017 : Blo 2097435 14364017 := bstep (se 2 (by rfl) ⟨5386506, by rfl⟩ : syracuseStep 14364017 = 10773013) B10773013
theorem B9576011 : Blo 2097435 9576011 := bstep (se 1 (by rfl) ⟨7182008, by rfl⟩ : syracuseStep 9576011 = 14364017) B14364017
theorem B6384007 : Blo 2097435 6384007 := bstep (se 1 (by rfl) ⟨4788005, by rfl⟩ : syracuseStep 6384007 = 9576011) B9576011
theorem B8512009 : Blo 2097435 8512009 := bstep (se 2 (by rfl) ⟨3192003, by rfl⟩ : syracuseStep 8512009 = 6384007) B6384007
theorem B45397381 : Blo 2097435 45397381 := bstep (se 4 (by rfl) ⟨4256004, by rfl⟩ : syracuseStep 45397381 = 8512009) B8512009
theorem B60529841 : Blo 2097435 60529841 := bstep (se 2 (by rfl) ⟨22698690, by rfl⟩ : syracuseStep 60529841 = 45397381) B45397381
theorem B40353227 : Blo 2097435 40353227 := bstep (se 1 (by rfl) ⟨30264920, by rfl⟩ : syracuseStep 40353227 = 60529841) B60529841
theorem B26902151 : Blo 2097435 26902151 := bstep (se 1 (by rfl) ⟨20176613, by rfl⟩ : syracuseStep 26902151 = 40353227) B40353227
theorem B17934767 : Blo 2097435 17934767 := bstep (se 1 (by rfl) ⟨13451075, by rfl⟩ : syracuseStep 17934767 = 26902151) B26902151
theorem B11956511 : Blo 2097435 11956511 := bstep (se 1 (by rfl) ⟨8967383, by rfl⟩ : syracuseStep 11956511 = 17934767) B17934767
theorem B7971007 : Blo 2097435 7971007 := bstep (se 1 (by rfl) ⟨5978255, by rfl⟩ : syracuseStep 7971007 = 11956511) B11956511
theorem B10628009 : Blo 2097435 10628009 := bstep (se 2 (by rfl) ⟨3985503, by rfl⟩ : syracuseStep 10628009 = 7971007) B7971007
theorem B7085339 : Blo 2097435 7085339 := bstep (se 1 (by rfl) ⟨5314004, by rfl⟩ : syracuseStep 7085339 = 10628009) B10628009
theorem B4723559 : Blo 2097435 4723559 := bstep (se 1 (by rfl) ⟨3542669, by rfl⟩ : syracuseStep 4723559 = 7085339) B7085339
theorem B3149039 : Blo 2097435 3149039 := bstep (se 1 (by rfl) ⟨2361779, by rfl⟩ : syracuseStep 3149039 = 4723559) B4723559
theorem B2099359 : Blo 2097435 2099359 := bstep (se 1 (by rfl) ⟨1574519, by rfl⟩ : syracuseStep 2099359 = 3149039) B3149039
theorem B3149045 : Blo 2097435 3149045 := bbase (se 5 (by rfl) ⟨147611, by rfl⟩ : syracuseStep 3149045 = 295223) (by norm_num)
theorem B2099363 : Blo 2097435 2099363 := bstep (se 1 (by rfl) ⟨1574522, by rfl⟩ : syracuseStep 2099363 = 3149045) B3149045
theorem B7182037 : Blo 2097435 7182037 := bbase (se 7 (by rfl) ⟨84164, by rfl⟩ : syracuseStep 7182037 = 168329) (by norm_num)
theorem B38304197 : Blo 2097435 38304197 := bstep (se 4 (by rfl) ⟨3591018, by rfl⟩ : syracuseStep 38304197 = 7182037) B7182037
theorem B25536131 : Blo 2097435 25536131 := bstep (se 1 (by rfl) ⟨19152098, by rfl⟩ : syracuseStep 25536131 = 38304197) B38304197
theorem B17024087 : Blo 2097435 17024087 := bstep (se 1 (by rfl) ⟨12768065, by rfl⟩ : syracuseStep 17024087 = 25536131) B25536131
theorem B11349391 : Blo 2097435 11349391 := bstep (se 1 (by rfl) ⟨8512043, by rfl⟩ : syracuseStep 11349391 = 17024087) B17024087
theorem B15132521 : Blo 2097435 15132521 := bstep (se 2 (by rfl) ⟨5674695, by rfl⟩ : syracuseStep 15132521 = 11349391) B11349391
theorem B10088347 : Blo 2097435 10088347 := bstep (se 1 (by rfl) ⟨7566260, by rfl⟩ : syracuseStep 10088347 = 15132521) B15132521
theorem B13451129 : Blo 2097435 13451129 := bstep (se 2 (by rfl) ⟨5044173, by rfl⟩ : syracuseStep 13451129 = 10088347) B10088347
theorem B8967419 : Blo 2097435 8967419 := bstep (se 1 (by rfl) ⟨6725564, by rfl⟩ : syracuseStep 8967419 = 13451129) B13451129
theorem B5978279 : Blo 2097435 5978279 := bstep (se 1 (by rfl) ⟨4483709, by rfl⟩ : syracuseStep 5978279 = 8967419) B8967419
theorem B3985519 : Blo 2097435 3985519 := bstep (se 1 (by rfl) ⟨2989139, by rfl⟩ : syracuseStep 3985519 = 5978279) B5978279
theorem B5314025 : Blo 2097435 5314025 := bstep (se 2 (by rfl) ⟨1992759, by rfl⟩ : syracuseStep 5314025 = 3985519) B3985519
theorem B3542683 : Blo 2097435 3542683 := bstep (se 1 (by rfl) ⟨2657012, by rfl⟩ : syracuseStep 3542683 = 5314025) B5314025
theorem B4723577 : Blo 2097435 4723577 := bstep (se 2 (by rfl) ⟨1771341, by rfl⟩ : syracuseStep 4723577 = 3542683) B3542683
theorem B3149051 : Blo 2097435 3149051 := bstep (se 1 (by rfl) ⟨2361788, by rfl⟩ : syracuseStep 3149051 = 4723577) B4723577
theorem B2099367 : Blo 2097435 2099367 := bstep (se 1 (by rfl) ⟨1574525, by rfl⟩ : syracuseStep 2099367 = 3149051) B3149051
theorem B2361793 : Blo 2097435 2361793 := bbase (se 2 (by rfl) ⟨885672, by rfl⟩ : syracuseStep 2361793 = 1771345) (by norm_num)
theorem B3149057 : Blo 2097435 3149057 := bstep (se 2 (by rfl) ⟨1180896, by rfl⟩ : syracuseStep 3149057 = 2361793) B2361793
theorem B2099371 : Blo 2097435 2099371 := bstep (se 1 (by rfl) ⟨1574528, by rfl⟩ : syracuseStep 2099371 = 3149057) B3149057
theorem B5314045 : Blo 2097435 5314045 := bbase (se 3 (by rfl) ⟨996383, by rfl⟩ : syracuseStep 5314045 = 1992767) (by norm_num)
theorem B7085393 : Blo 2097435 7085393 := bstep (se 2 (by rfl) ⟨2657022, by rfl⟩ : syracuseStep 7085393 = 5314045) B5314045
theorem B4723595 : Blo 2097435 4723595 := bstep (se 1 (by rfl) ⟨3542696, by rfl⟩ : syracuseStep 4723595 = 7085393) B7085393
theorem B3149063 : Blo 2097435 3149063 := bstep (se 1 (by rfl) ⟨2361797, by rfl⟩ : syracuseStep 3149063 = 4723595) B4723595
theorem B2099375 : Blo 2097435 2099375 := bstep (se 1 (by rfl) ⟨1574531, by rfl⟩ : syracuseStep 2099375 = 3149063) B3149063
theorem B3149069 : Blo 2097435 3149069 := bbase (se 3 (by rfl) ⟨590450, by rfl⟩ : syracuseStep 3149069 = 1180901) (by norm_num)
theorem B2099379 : Blo 2097435 2099379 := bstep (se 1 (by rfl) ⟨1574534, by rfl⟩ : syracuseStep 2099379 = 3149069) B3149069
theorem B4723613 : Blo 2097435 4723613 := bbase (se 3 (by rfl) ⟨885677, by rfl⟩ : syracuseStep 4723613 = 1771355) (by norm_num)
theorem B3149075 : Blo 2097435 3149075 := bstep (se 1 (by rfl) ⟨2361806, by rfl⟩ : syracuseStep 3149075 = 4723613) B4723613
theorem B2099383 : Blo 2097435 2099383 := bstep (se 1 (by rfl) ⟨1574537, by rfl⟩ : syracuseStep 2099383 = 3149075) B3149075
theorem B3542717 : Blo 2097435 3542717 := bbase (se 3 (by rfl) ⟨664259, by rfl⟩ : syracuseStep 3542717 = 1328519) (by norm_num)
theorem B2361811 : Blo 2097435 2361811 := bstep (se 1 (by rfl) ⟨1771358, by rfl⟩ : syracuseStep 2361811 = 3542717) B3542717
theorem B3149081 : Blo 2097435 3149081 := bstep (se 2 (by rfl) ⟨1180905, by rfl⟩ : syracuseStep 3149081 = 2361811) B2361811
theorem B2099387 : Blo 2097435 2099387 := bstep (se 1 (by rfl) ⟨1574540, by rfl⟩ : syracuseStep 2099387 = 3149081) B3149081
theorem B11956693 : Blo 2097435 11956693 := bbase (se 7 (by rfl) ⟨140117, by rfl⟩ : syracuseStep 11956693 = 280235) (by norm_num)
theorem B15942257 : Blo 2097435 15942257 := bstep (se 2 (by rfl) ⟨5978346, by rfl⟩ : syracuseStep 15942257 = 11956693) B11956693
theorem B10628171 : Blo 2097435 10628171 := bstep (se 1 (by rfl) ⟨7971128, by rfl⟩ : syracuseStep 10628171 = 15942257) B15942257
theorem B7085447 : Blo 2097435 7085447 := bstep (se 1 (by rfl) ⟨5314085, by rfl⟩ : syracuseStep 7085447 = 10628171) B10628171
theorem B4723631 : Blo 2097435 4723631 := bstep (se 1 (by rfl) ⟨3542723, by rfl⟩ : syracuseStep 4723631 = 7085447) B7085447
theorem B3149087 : Blo 2097435 3149087 := bstep (se 1 (by rfl) ⟨2361815, by rfl⟩ : syracuseStep 3149087 = 4723631) B4723631
theorem B2099391 : Blo 2097435 2099391 := bstep (se 1 (by rfl) ⟨1574543, by rfl⟩ : syracuseStep 2099391 = 3149087) B3149087
theorem B3149093 : Blo 2097435 3149093 := bbase (se 4 (by rfl) ⟨295227, by rfl⟩ : syracuseStep 3149093 = 590455) (by norm_num)
theorem B2099395 : Blo 2097435 2099395 := bstep (se 1 (by rfl) ⟨1574546, by rfl⟩ : syracuseStep 2099395 = 3149093) B3149093
theorem B2657053 : Blo 2097435 2657053 := bbase (se 3 (by rfl) ⟨498197, by rfl⟩ : syracuseStep 2657053 = 996395) (by norm_num)
theorem B3542737 : Blo 2097435 3542737 := bstep (se 2 (by rfl) ⟨1328526, by rfl⟩ : syracuseStep 3542737 = 2657053) B2657053
theorem B4723649 : Blo 2097435 4723649 := bstep (se 2 (by rfl) ⟨1771368, by rfl⟩ : syracuseStep 4723649 = 3542737) B3542737
theorem B3149099 : Blo 2097435 3149099 := bstep (se 1 (by rfl) ⟨2361824, by rfl⟩ : syracuseStep 3149099 = 4723649) B4723649
theorem B2099399 : Blo 2097435 2099399 := bstep (se 1 (by rfl) ⟨1574549, by rfl⟩ : syracuseStep 2099399 = 3149099) B3149099
theorem B2361829 : Blo 2097435 2361829 := bbase (se 4 (by rfl) ⟨221421, by rfl⟩ : syracuseStep 2361829 = 442843) (by norm_num)
theorem B3149105 : Blo 2097435 3149105 := bstep (se 2 (by rfl) ⟨1180914, by rfl⟩ : syracuseStep 3149105 = 2361829) B2361829
theorem B2099403 : Blo 2097435 2099403 := bstep (se 1 (by rfl) ⟨1574552, by rfl⟩ : syracuseStep 2099403 = 3149105) B3149105
theorem B5674805 : Blo 2097435 5674805 := bbase (se 5 (by rfl) ⟨266006, by rfl⟩ : syracuseStep 5674805 = 532013) (by norm_num)
theorem B3783203 : Blo 2097435 3783203 := bstep (se 1 (by rfl) ⟨2837402, by rfl⟩ : syracuseStep 3783203 = 5674805) B5674805
theorem B2522135 : Blo 2097435 2522135 := bstep (se 1 (by rfl) ⟨1891601, by rfl⟩ : syracuseStep 2522135 = 3783203) B3783203
theorem B6725693 : Blo 2097435 6725693 := bstep (se 3 (by rfl) ⟨1261067, by rfl⟩ : syracuseStep 6725693 = 2522135) B2522135
theorem B4483795 : Blo 2097435 4483795 := bstep (se 1 (by rfl) ⟨3362846, by rfl⟩ : syracuseStep 4483795 = 6725693) B6725693
theorem B5978393 : Blo 2097435 5978393 := bstep (se 2 (by rfl) ⟨2241897, by rfl⟩ : syracuseStep 5978393 = 4483795) B4483795
theorem B3985595 : Blo 2097435 3985595 := bstep (se 1 (by rfl) ⟨2989196, by rfl⟩ : syracuseStep 3985595 = 5978393) B5978393
theorem B2657063 : Blo 2097435 2657063 := bstep (se 1 (by rfl) ⟨1992797, by rfl⟩ : syracuseStep 2657063 = 3985595) B3985595
theorem B7085501 : Blo 2097435 7085501 := bstep (se 3 (by rfl) ⟨1328531, by rfl⟩ : syracuseStep 7085501 = 2657063) B2657063
theorem B4723667 : Blo 2097435 4723667 := bstep (se 1 (by rfl) ⟨3542750, by rfl⟩ : syracuseStep 4723667 = 7085501) B7085501
theorem B3149111 : Blo 2097435 3149111 := bstep (se 1 (by rfl) ⟨2361833, by rfl⟩ : syracuseStep 3149111 = 4723667) B4723667
theorem B2099407 : Blo 2097435 2099407 := bstep (se 1 (by rfl) ⟨1574555, by rfl⟩ : syracuseStep 2099407 = 3149111) B3149111
theorem B3149117 : Blo 2097435 3149117 := bbase (se 3 (by rfl) ⟨590459, by rfl⟩ : syracuseStep 3149117 = 1180919) (by norm_num)
theorem B2099411 : Blo 2097435 2099411 := bstep (se 1 (by rfl) ⟨1574558, by rfl⟩ : syracuseStep 2099411 = 3149117) B3149117
theorem B4723685 : Blo 2097435 4723685 := bbase (se 4 (by rfl) ⟨442845, by rfl⟩ : syracuseStep 4723685 = 885691) (by norm_num)
theorem B3149123 : Blo 2097435 3149123 := bstep (se 1 (by rfl) ⟨2361842, by rfl⟩ : syracuseStep 3149123 = 4723685) B4723685
theorem B2099415 : Blo 2097435 2099415 := bstep (se 1 (by rfl) ⟨1574561, by rfl⟩ : syracuseStep 2099415 = 3149123) B3149123
theorem B5314157 : Blo 2097435 5314157 := bbase (se 3 (by rfl) ⟨996404, by rfl⟩ : syracuseStep 5314157 = 1992809) (by norm_num)
theorem B3542771 : Blo 2097435 3542771 := bstep (se 1 (by rfl) ⟨2657078, by rfl⟩ : syracuseStep 3542771 = 5314157) B5314157
theorem B2361847 : Blo 2097435 2361847 := bstep (se 1 (by rfl) ⟨1771385, by rfl⟩ : syracuseStep 2361847 = 3542771) B3542771
theorem B3149129 : Blo 2097435 3149129 := bstep (se 2 (by rfl) ⟨1180923, by rfl⟩ : syracuseStep 3149129 = 2361847) B2361847
theorem B2099419 : Blo 2097435 2099419 := bstep (se 1 (by rfl) ⟨1574564, by rfl⟩ : syracuseStep 2099419 = 3149129) B3149129
theorem B4483829 : Blo 2097435 4483829 := bbase (se 5 (by rfl) ⟨210179, by rfl⟩ : syracuseStep 4483829 = 420359) (by norm_num)
theorem B2989219 : Blo 2097435 2989219 := bstep (se 1 (by rfl) ⟨2241914, by rfl⟩ : syracuseStep 2989219 = 4483829) B4483829
theorem B3985625 : Blo 2097435 3985625 := bstep (se 2 (by rfl) ⟨1494609, by rfl⟩ : syracuseStep 3985625 = 2989219) B2989219
theorem B10628333 : Blo 2097435 10628333 := bstep (se 3 (by rfl) ⟨1992812, by rfl⟩ : syracuseStep 10628333 = 3985625) B3985625
theorem B7085555 : Blo 2097435 7085555 := bstep (se 1 (by rfl) ⟨5314166, by rfl⟩ : syracuseStep 7085555 = 10628333) B10628333
theorem B4723703 : Blo 2097435 4723703 := bstep (se 1 (by rfl) ⟨3542777, by rfl⟩ : syracuseStep 4723703 = 7085555) B7085555
theorem B3149135 : Blo 2097435 3149135 := bstep (se 1 (by rfl) ⟨2361851, by rfl⟩ : syracuseStep 3149135 = 4723703) B4723703
theorem B2099423 : Blo 2097435 2099423 := bstep (se 1 (by rfl) ⟨1574567, by rfl⟩ : syracuseStep 2099423 = 3149135) B3149135
theorem B3149141 : Blo 2097435 3149141 := bbase (se 11 (by rfl) ⟨2306, by rfl⟩ : syracuseStep 3149141 = 4613) (by norm_num)
theorem B2099427 : Blo 2097435 2099427 := bstep (se 1 (by rfl) ⟨1574570, by rfl⟩ : syracuseStep 2099427 = 3149141) B3149141
theorem B3362885 : Blo 2097435 3362885 := bbase (se 4 (by rfl) ⟨315270, by rfl⟩ : syracuseStep 3362885 = 630541) (by norm_num)
theorem B2241923 : Blo 2097435 2241923 := bstep (se 1 (by rfl) ⟨1681442, by rfl⟩ : syracuseStep 2241923 = 3362885) B3362885
theorem B5978461 : Blo 2097435 5978461 := bstep (se 3 (by rfl) ⟨1120961, by rfl⟩ : syracuseStep 5978461 = 2241923) B2241923
theorem B7971281 : Blo 2097435 7971281 := bstep (se 2 (by rfl) ⟨2989230, by rfl⟩ : syracuseStep 7971281 = 5978461) B5978461
theorem B5314187 : Blo 2097435 5314187 := bstep (se 1 (by rfl) ⟨3985640, by rfl⟩ : syracuseStep 5314187 = 7971281) B7971281
theorem B3542791 : Blo 2097435 3542791 := bstep (se 1 (by rfl) ⟨2657093, by rfl⟩ : syracuseStep 3542791 = 5314187) B5314187
theorem B4723721 : Blo 2097435 4723721 := bstep (se 2 (by rfl) ⟨1771395, by rfl⟩ : syracuseStep 4723721 = 3542791) B3542791
theorem B3149147 : Blo 2097435 3149147 := bstep (se 1 (by rfl) ⟨2361860, by rfl⟩ : syracuseStep 3149147 = 4723721) B4723721
theorem B2099431 : Blo 2097435 2099431 := bstep (se 1 (by rfl) ⟨1574573, by rfl⟩ : syracuseStep 2099431 = 3149147) B3149147
theorem B2361865 : Blo 2097435 2361865 := bbase (se 2 (by rfl) ⟨885699, by rfl⟩ : syracuseStep 2361865 = 1771399) (by norm_num)
theorem B3149153 : Blo 2097435 3149153 := bstep (se 2 (by rfl) ⟨1180932, by rfl⟩ : syracuseStep 3149153 = 2361865) B2361865
theorem B2099435 : Blo 2097435 2099435 := bstep (se 1 (by rfl) ⟨1574576, by rfl⟩ : syracuseStep 2099435 = 3149153) B3149153
theorem C0 (j : ℕ) (h1 : 524358 ≤ j) (h2 : j ≤ 524858) : Blo 2097435 (4 * j + 3) := by
  interval_cases j
  · exact B2097435
  · exact B2097439
  · exact B2097443
  · exact B2097447
  · exact B2097451
  · exact B2097455
  · exact B2097459
  · exact B2097463
  · exact B2097467
  · exact B2097471
  · exact B2097475
  · exact B2097479
  · exact B2097483
  · exact B2097487
  · exact B2097491
  · exact B2097495
  · exact B2097499
  · exact B2097503
  · exact B2097507
  · exact B2097511
  · exact B2097515
  · exact B2097519
  · exact B2097523
  · exact B2097527
  · exact B2097531
  · exact B2097535
  · exact B2097539
  · exact B2097543
  · exact B2097547
  · exact B2097551
  · exact B2097555
  · exact B2097559
  · exact B2097563
  · exact B2097567
  · exact B2097571
  · exact B2097575
  · exact B2097579
  · exact B2097583
  · exact B2097587
  · exact B2097591
  · exact B2097595
  · exact B2097599
  · exact B2097603
  · exact B2097607
  · exact B2097611
  · exact B2097615
  · exact B2097619
  · exact B2097623
  · exact B2097627
  · exact B2097631
  · exact B2097635
  · exact B2097639
  · exact B2097643
  · exact B2097647
  · exact B2097651
  · exact B2097655
  · exact B2097659
  · exact B2097663
  · exact B2097667
  · exact B2097671
  · exact B2097675
  · exact B2097679
  · exact B2097683
  · exact B2097687
  · exact B2097691
  · exact B2097695
  · exact B2097699
  · exact B2097703
  · exact B2097707
  · exact B2097711
  · exact B2097715
  · exact B2097719
  · exact B2097723
  · exact B2097727
  · exact B2097731
  · exact B2097735
  · exact B2097739
  · exact B2097743
  · exact B2097747
  · exact B2097751
  · exact B2097755
  · exact B2097759
  · exact B2097763
  · exact B2097767
  · exact B2097771
  · exact B2097775
  · exact B2097779
  · exact B2097783
  · exact B2097787
  · exact B2097791
  · exact B2097795
  · exact B2097799
  · exact B2097803
  · exact B2097807
  · exact B2097811
  · exact B2097815
  · exact B2097819
  · exact B2097823
  · exact B2097827
  · exact B2097831
  · exact B2097835
  · exact B2097839
  · exact B2097843
  · exact B2097847
  · exact B2097851
  · exact B2097855
  · exact B2097859
  · exact B2097863
  · exact B2097867
  · exact B2097871
  · exact B2097875
  · exact B2097879
  · exact B2097883
  · exact B2097887
  · exact B2097891
  · exact B2097895
  · exact B2097899
  · exact B2097903
  · exact B2097907
  · exact B2097911
  · exact B2097915
  · exact B2097919
  · exact B2097923
  · exact B2097927
  · exact B2097931
  · exact B2097935
  · exact B2097939
  · exact B2097943
  · exact B2097947
  · exact B2097951
  · exact B2097955
  · exact B2097959
  · exact B2097963
  · exact B2097967
  · exact B2097971
  · exact B2097975
  · exact B2097979
  · exact B2097983
  · exact B2097987
  · exact B2097991
  · exact B2097995
  · exact B2097999
  · exact B2098003
  · exact B2098007
  · exact B2098011
  · exact B2098015
  · exact B2098019
  · exact B2098023
  · exact B2098027
  · exact B2098031
  · exact B2098035
  · exact B2098039
  · exact B2098043
  · exact B2098047
  · exact B2098051
  · exact B2098055
  · exact B2098059
  · exact B2098063
  · exact B2098067
  · exact B2098071
  · exact B2098075
  · exact B2098079
  · exact B2098083
  · exact B2098087
  · exact B2098091
  · exact B2098095
  · exact B2098099
  · exact B2098103
  · exact B2098107
  · exact B2098111
  · exact B2098115
  · exact B2098119
  · exact B2098123
  · exact B2098127
  · exact B2098131
  · exact B2098135
  · exact B2098139
  · exact B2098143
  · exact B2098147
  · exact B2098151
  · exact B2098155
  · exact B2098159
  · exact B2098163
  · exact B2098167
  · exact B2098171
  · exact B2098175
  · exact B2098179
  · exact B2098183
  · exact B2098187
  · exact B2098191
  · exact B2098195
  · exact B2098199
  · exact B2098203
  · exact B2098207
  · exact B2098211
  · exact B2098215
  · exact B2098219
  · exact B2098223
  · exact B2098227
  · exact B2098231
  · exact B2098235
  · exact B2098239
  · exact B2098243
  · exact B2098247
  · exact B2098251
  · exact B2098255
  · exact B2098259
  · exact B2098263
  · exact B2098267
  · exact B2098271
  · exact B2098275
  · exact B2098279
  · exact B2098283
  · exact B2098287
  · exact B2098291
  · exact B2098295
  · exact B2098299
  · exact B2098303
  · exact B2098307
  · exact B2098311
  · exact B2098315
  · exact B2098319
  · exact B2098323
  · exact B2098327
  · exact B2098331
  · exact B2098335
  · exact B2098339
  · exact B2098343
  · exact B2098347
  · exact B2098351
  · exact B2098355
  · exact B2098359
  · exact B2098363
  · exact B2098367
  · exact B2098371
  · exact B2098375
  · exact B2098379
  · exact B2098383
  · exact B2098387
  · exact B2098391
  · exact B2098395
  · exact B2098399
  · exact B2098403
  · exact B2098407
  · exact B2098411
  · exact B2098415
  · exact B2098419
  · exact B2098423
  · exact B2098427
  · exact B2098431
  · exact B2098435
  · exact B2098439
  · exact B2098443
  · exact B2098447
  · exact B2098451
  · exact B2098455
  · exact B2098459
  · exact B2098463
  · exact B2098467
  · exact B2098471
  · exact B2098475
  · exact B2098479
  · exact B2098483
  · exact B2098487
  · exact B2098491
  · exact B2098495
  · exact B2098499
  · exact B2098503
  · exact B2098507
  · exact B2098511
  · exact B2098515
  · exact B2098519
  · exact B2098523
  · exact B2098527
  · exact B2098531
  · exact B2098535
  · exact B2098539
  · exact B2098543
  · exact B2098547
  · exact B2098551
  · exact B2098555
  · exact B2098559
  · exact B2098563
  · exact B2098567
  · exact B2098571
  · exact B2098575
  · exact B2098579
  · exact B2098583
  · exact B2098587
  · exact B2098591
  · exact B2098595
  · exact B2098599
  · exact B2098603
  · exact B2098607
  · exact B2098611
  · exact B2098615
  · exact B2098619
  · exact B2098623
  · exact B2098627
  · exact B2098631
  · exact B2098635
  · exact B2098639
  · exact B2098643
  · exact B2098647
  · exact B2098651
  · exact B2098655
  · exact B2098659
  · exact B2098663
  · exact B2098667
  · exact B2098671
  · exact B2098675
  · exact B2098679
  · exact B2098683
  · exact B2098687
  · exact B2098691
  · exact B2098695
  · exact B2098699
  · exact B2098703
  · exact B2098707
  · exact B2098711
  · exact B2098715
  · exact B2098719
  · exact B2098723
  · exact B2098727
  · exact B2098731
  · exact B2098735
  · exact B2098739
  · exact B2098743
  · exact B2098747
  · exact B2098751
  · exact B2098755
  · exact B2098759
  · exact B2098763
  · exact B2098767
  · exact B2098771
  · exact B2098775
  · exact B2098779
  · exact B2098783
  · exact B2098787
  · exact B2098791
  · exact B2098795
  · exact B2098799
  · exact B2098803
  · exact B2098807
  · exact B2098811
  · exact B2098815
  · exact B2098819
  · exact B2098823
  · exact B2098827
  · exact B2098831
  · exact B2098835
  · exact B2098839
  · exact B2098843
  · exact B2098847
  · exact B2098851
  · exact B2098855
  · exact B2098859
  · exact B2098863
  · exact B2098867
  · exact B2098871
  · exact B2098875
  · exact B2098879
  · exact B2098883
  · exact B2098887
  · exact B2098891
  · exact B2098895
  · exact B2098899
  · exact B2098903
  · exact B2098907
  · exact B2098911
  · exact B2098915
  · exact B2098919
  · exact B2098923
  · exact B2098927
  · exact B2098931
  · exact B2098935
  · exact B2098939
  · exact B2098943
  · exact B2098947
  · exact B2098951
  · exact B2098955
  · exact B2098959
  · exact B2098963
  · exact B2098967
  · exact B2098971
  · exact B2098975
  · exact B2098979
  · exact B2098983
  · exact B2098987
  · exact B2098991
  · exact B2098995
  · exact B2098999
  · exact B2099003
  · exact B2099007
  · exact B2099011
  · exact B2099015
  · exact B2099019
  · exact B2099023
  · exact B2099027
  · exact B2099031
  · exact B2099035
  · exact B2099039
  · exact B2099043
  · exact B2099047
  · exact B2099051
  · exact B2099055
  · exact B2099059
  · exact B2099063
  · exact B2099067
  · exact B2099071
  · exact B2099075
  · exact B2099079
  · exact B2099083
  · exact B2099087
  · exact B2099091
  · exact B2099095
  · exact B2099099
  · exact B2099103
  · exact B2099107
  · exact B2099111
  · exact B2099115
  · exact B2099119
  · exact B2099123
  · exact B2099127
  · exact B2099131
  · exact B2099135
  · exact B2099139
  · exact B2099143
  · exact B2099147
  · exact B2099151
  · exact B2099155
  · exact B2099159
  · exact B2099163
  · exact B2099167
  · exact B2099171
  · exact B2099175
  · exact B2099179
  · exact B2099183
  · exact B2099187
  · exact B2099191
  · exact B2099195
  · exact B2099199
  · exact B2099203
  · exact B2099207
  · exact B2099211
  · exact B2099215
  · exact B2099219
  · exact B2099223
  · exact B2099227
  · exact B2099231
  · exact B2099235
  · exact B2099239
  · exact B2099243
  · exact B2099247
  · exact B2099251
  · exact B2099255
  · exact B2099259
  · exact B2099263
  · exact B2099267
  · exact B2099271
  · exact B2099275
  · exact B2099279
  · exact B2099283
  · exact B2099287
  · exact B2099291
  · exact B2099295
  · exact B2099299
  · exact B2099303
  · exact B2099307
  · exact B2099311
  · exact B2099315
  · exact B2099319
  · exact B2099323
  · exact B2099327
  · exact B2099331
  · exact B2099335
  · exact B2099339
  · exact B2099343
  · exact B2099347
  · exact B2099351
  · exact B2099355
  · exact B2099359
  · exact B2099363
  · exact B2099367
  · exact B2099371
  · exact B2099375
  · exact B2099379
  · exact B2099383
  · exact B2099387
  · exact B2099391
  · exact B2099395
  · exact B2099399
  · exact B2099403
  · exact B2099407
  · exact B2099411
  · exact B2099415
  · exact B2099419
  · exact B2099423
  · exact B2099427
  · exact B2099431
  · exact B2099435
theorem solution (m : ℕ) (hlo : 2097435 ≤ m) (hhi : m ≤ 2099435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 524358 ≤ j := by omega
    have hj2 : j ≤ 524858 := by omega
    have hb : Blo 2097435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
