-- Prove2me | solution 1 for syracuse_descends_range_1961435_1963435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:47:52.834233+00:00
-- url     : https://prove2.me/submissions/f7c4165a-d68b-49a8-ace2-3ec3c70522ce

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

theorem B4964885 : Blo 1961435 4964885 := bbase (se 6 (by rfl) ⟨116364, by rfl⟩ : syracuseStep 4964885 = 232729) (by norm_num)
theorem B3309923 : Blo 1961435 3309923 := bstep (se 1 (by rfl) ⟨2482442, by rfl⟩ : syracuseStep 3309923 = 4964885) B4964885
theorem B2206615 : Blo 1961435 2206615 := bstep (se 1 (by rfl) ⟨1654961, by rfl⟩ : syracuseStep 2206615 = 3309923) B3309923
theorem B2942153 : Blo 1961435 2942153 := bstep (se 2 (by rfl) ⟨1103307, by rfl⟩ : syracuseStep 2942153 = 2206615) B2206615
theorem B1961435 : Blo 1961435 1961435 := bstep (se 1 (by rfl) ⟨1471076, by rfl⟩ : syracuseStep 1961435 = 2942153) B2942153
theorem B8378261 : Blo 1961435 8378261 := bbase (se 6 (by rfl) ⟨196365, by rfl⟩ : syracuseStep 8378261 = 392731) (by norm_num)
theorem B5585507 : Blo 1961435 5585507 := bstep (se 1 (by rfl) ⟨4189130, by rfl⟩ : syracuseStep 5585507 = 8378261) B8378261
theorem B3723671 : Blo 1961435 3723671 := bstep (se 1 (by rfl) ⟨2792753, by rfl⟩ : syracuseStep 3723671 = 5585507) B5585507
theorem B9929789 : Blo 1961435 9929789 := bstep (se 3 (by rfl) ⟨1861835, by rfl⟩ : syracuseStep 9929789 = 3723671) B3723671
theorem B6619859 : Blo 1961435 6619859 := bstep (se 1 (by rfl) ⟨4964894, by rfl⟩ : syracuseStep 6619859 = 9929789) B9929789
theorem B4413239 : Blo 1961435 4413239 := bstep (se 1 (by rfl) ⟨3309929, by rfl⟩ : syracuseStep 4413239 = 6619859) B6619859
theorem B2942159 : Blo 1961435 2942159 := bstep (se 1 (by rfl) ⟨2206619, by rfl⟩ : syracuseStep 2942159 = 4413239) B4413239
theorem B1961439 : Blo 1961435 1961439 := bstep (se 1 (by rfl) ⟨1471079, by rfl⟩ : syracuseStep 1961439 = 2942159) B2942159
theorem B2942165 : Blo 1961435 2942165 := bbase (se 7 (by rfl) ⟨34478, by rfl⟩ : syracuseStep 2942165 = 68957) (by norm_num)
theorem B1961443 : Blo 1961435 1961443 := bstep (se 1 (by rfl) ⟨1471082, by rfl⟩ : syracuseStep 1961443 = 2942165) B2942165
theorem B2792765 : Blo 1961435 2792765 := bbase (se 3 (by rfl) ⟨523643, by rfl⟩ : syracuseStep 2792765 = 1047287) (by norm_num)
theorem B7447373 : Blo 1961435 7447373 := bstep (se 3 (by rfl) ⟨1396382, by rfl⟩ : syracuseStep 7447373 = 2792765) B2792765
theorem B4964915 : Blo 1961435 4964915 := bstep (se 1 (by rfl) ⟨3723686, by rfl⟩ : syracuseStep 4964915 = 7447373) B7447373
theorem B3309943 : Blo 1961435 3309943 := bstep (se 1 (by rfl) ⟨2482457, by rfl⟩ : syracuseStep 3309943 = 4964915) B4964915
theorem B4413257 : Blo 1961435 4413257 := bstep (se 2 (by rfl) ⟨1654971, by rfl⟩ : syracuseStep 4413257 = 3309943) B3309943
theorem B2942171 : Blo 1961435 2942171 := bstep (se 1 (by rfl) ⟨2206628, by rfl⟩ : syracuseStep 2942171 = 4413257) B4413257
theorem B1961447 : Blo 1961435 1961447 := bstep (se 1 (by rfl) ⟨1471085, by rfl⟩ : syracuseStep 1961447 = 2942171) B2942171
theorem B2206633 : Blo 1961435 2206633 := bbase (se 2 (by rfl) ⟨827487, by rfl⟩ : syracuseStep 2206633 = 1654975) (by norm_num)
theorem B2942177 : Blo 1961435 2942177 := bstep (se 2 (by rfl) ⟨1103316, by rfl⟩ : syracuseStep 2942177 = 2206633) B2206633
theorem B1961451 : Blo 1961435 1961451 := bstep (se 1 (by rfl) ⟨1471088, by rfl⟩ : syracuseStep 1961451 = 2942177) B2942177
theorem B9425621 : Blo 1961435 9425621 := bbase (se 7 (by rfl) ⟨110456, by rfl⟩ : syracuseStep 9425621 = 220913) (by norm_num)
theorem B6283747 : Blo 1961435 6283747 := bstep (se 1 (by rfl) ⟨4712810, by rfl⟩ : syracuseStep 6283747 = 9425621) B9425621
theorem B8378329 : Blo 1961435 8378329 := bstep (se 2 (by rfl) ⟨3141873, by rfl⟩ : syracuseStep 8378329 = 6283747) B6283747
theorem B11171105 : Blo 1961435 11171105 := bstep (se 2 (by rfl) ⟨4189164, by rfl⟩ : syracuseStep 11171105 = 8378329) B8378329
theorem B7447403 : Blo 1961435 7447403 := bstep (se 1 (by rfl) ⟨5585552, by rfl⟩ : syracuseStep 7447403 = 11171105) B11171105
theorem B4964935 : Blo 1961435 4964935 := bstep (se 1 (by rfl) ⟨3723701, by rfl⟩ : syracuseStep 4964935 = 7447403) B7447403
theorem B6619913 : Blo 1961435 6619913 := bstep (se 2 (by rfl) ⟨2482467, by rfl⟩ : syracuseStep 6619913 = 4964935) B4964935
theorem B4413275 : Blo 1961435 4413275 := bstep (se 1 (by rfl) ⟨3309956, by rfl⟩ : syracuseStep 4413275 = 6619913) B6619913
theorem B2942183 : Blo 1961435 2942183 := bstep (se 1 (by rfl) ⟨2206637, by rfl⟩ : syracuseStep 2942183 = 4413275) B4413275
theorem B1961455 : Blo 1961435 1961455 := bstep (se 1 (by rfl) ⟨1471091, by rfl⟩ : syracuseStep 1961455 = 2942183) B2942183
theorem B2942189 : Blo 1961435 2942189 := bbase (se 3 (by rfl) ⟨551660, by rfl⟩ : syracuseStep 2942189 = 1103321) (by norm_num)
theorem B1961459 : Blo 1961435 1961459 := bstep (se 1 (by rfl) ⟨1471094, by rfl⟩ : syracuseStep 1961459 = 2942189) B2942189
theorem B4413293 : Blo 1961435 4413293 := bbase (se 3 (by rfl) ⟨827492, by rfl⟩ : syracuseStep 4413293 = 1654985) (by norm_num)
theorem B2942195 : Blo 1961435 2942195 := bstep (se 1 (by rfl) ⟨2206646, by rfl⟩ : syracuseStep 2942195 = 4413293) B4413293
theorem B1961463 : Blo 1961435 1961463 := bstep (se 1 (by rfl) ⟨1471097, by rfl⟩ : syracuseStep 1961463 = 2942195) B2942195
theorem B3723725 : Blo 1961435 3723725 := bbase (se 3 (by rfl) ⟨698198, by rfl⟩ : syracuseStep 3723725 = 1396397) (by norm_num)
theorem B2482483 : Blo 1961435 2482483 := bstep (se 1 (by rfl) ⟨1861862, by rfl⟩ : syracuseStep 2482483 = 3723725) B3723725
theorem B3309977 : Blo 1961435 3309977 := bstep (se 2 (by rfl) ⟨1241241, by rfl⟩ : syracuseStep 3309977 = 2482483) B2482483
theorem B2206651 : Blo 1961435 2206651 := bstep (se 1 (by rfl) ⟨1654988, by rfl⟩ : syracuseStep 2206651 = 3309977) B3309977
theorem B2942201 : Blo 1961435 2942201 := bstep (se 2 (by rfl) ⟨1103325, by rfl⟩ : syracuseStep 2942201 = 2206651) B2206651
theorem B1961467 : Blo 1961435 1961467 := bstep (se 1 (by rfl) ⟨1471100, by rfl⟩ : syracuseStep 1961467 = 2942201) B2942201
theorem B1988233 : Blo 1961435 1988233 := bbase (se 2 (by rfl) ⟨745587, by rfl⟩ : syracuseStep 1988233 = 1491175) (by norm_num)
theorem B10603909 : Blo 1961435 10603909 := bstep (se 4 (by rfl) ⟨994116, by rfl⟩ : syracuseStep 10603909 = 1988233) B1988233
theorem B14138545 : Blo 1961435 14138545 := bstep (se 2 (by rfl) ⟨5301954, by rfl⟩ : syracuseStep 14138545 = 10603909) B10603909
theorem B18851393 : Blo 1961435 18851393 := bstep (se 2 (by rfl) ⟨7069272, by rfl⟩ : syracuseStep 18851393 = 14138545) B14138545
theorem B50270381 : Blo 1961435 50270381 := bstep (se 3 (by rfl) ⟨9425696, by rfl⟩ : syracuseStep 50270381 = 18851393) B18851393
theorem B33513587 : Blo 1961435 33513587 := bstep (se 1 (by rfl) ⟨25135190, by rfl⟩ : syracuseStep 33513587 = 50270381) B50270381
theorem B22342391 : Blo 1961435 22342391 := bstep (se 1 (by rfl) ⟨16756793, by rfl⟩ : syracuseStep 22342391 = 33513587) B33513587
theorem B14894927 : Blo 1961435 14894927 := bstep (se 1 (by rfl) ⟨11171195, by rfl⟩ : syracuseStep 14894927 = 22342391) B22342391
theorem B9929951 : Blo 1961435 9929951 := bstep (se 1 (by rfl) ⟨7447463, by rfl⟩ : syracuseStep 9929951 = 14894927) B14894927
theorem B6619967 : Blo 1961435 6619967 := bstep (se 1 (by rfl) ⟨4964975, by rfl⟩ : syracuseStep 6619967 = 9929951) B9929951
theorem B4413311 : Blo 1961435 4413311 := bstep (se 1 (by rfl) ⟨3309983, by rfl⟩ : syracuseStep 4413311 = 6619967) B6619967
theorem B2942207 : Blo 1961435 2942207 := bstep (se 1 (by rfl) ⟨2206655, by rfl⟩ : syracuseStep 2942207 = 4413311) B4413311
theorem B1961471 : Blo 1961435 1961471 := bstep (se 1 (by rfl) ⟨1471103, by rfl⟩ : syracuseStep 1961471 = 2942207) B2942207
theorem B2942213 : Blo 1961435 2942213 := bbase (se 4 (by rfl) ⟨275832, by rfl⟩ : syracuseStep 2942213 = 551665) (by norm_num)
theorem B1961475 : Blo 1961435 1961475 := bstep (se 1 (by rfl) ⟨1471106, by rfl⟩ : syracuseStep 1961475 = 2942213) B2942213
theorem B3309997 : Blo 1961435 3309997 := bbase (se 3 (by rfl) ⟨620624, by rfl⟩ : syracuseStep 3309997 = 1241249) (by norm_num)
theorem B4413329 : Blo 1961435 4413329 := bstep (se 2 (by rfl) ⟨1654998, by rfl⟩ : syracuseStep 4413329 = 3309997) B3309997
theorem B2942219 : Blo 1961435 2942219 := bstep (se 1 (by rfl) ⟨2206664, by rfl⟩ : syracuseStep 2942219 = 4413329) B4413329
theorem B1961479 : Blo 1961435 1961479 := bstep (se 1 (by rfl) ⟨1471109, by rfl⟩ : syracuseStep 1961479 = 2942219) B2942219
theorem B2206669 : Blo 1961435 2206669 := bbase (se 3 (by rfl) ⟨413750, by rfl⟩ : syracuseStep 2206669 = 827501) (by norm_num)
theorem B2942225 : Blo 1961435 2942225 := bstep (se 2 (by rfl) ⟨1103334, by rfl⟩ : syracuseStep 2942225 = 2206669) B2206669
theorem B1961483 : Blo 1961435 1961483 := bstep (se 1 (by rfl) ⟨1471112, by rfl⟩ : syracuseStep 1961483 = 2942225) B2942225
theorem B6620021 : Blo 1961435 6620021 := bbase (se 5 (by rfl) ⟨310313, by rfl⟩ : syracuseStep 6620021 = 620627) (by norm_num)
theorem B4413347 : Blo 1961435 4413347 := bstep (se 1 (by rfl) ⟨3310010, by rfl⟩ : syracuseStep 4413347 = 6620021) B6620021
theorem B2942231 : Blo 1961435 2942231 := bstep (se 1 (by rfl) ⟨2206673, by rfl⟩ : syracuseStep 2942231 = 4413347) B4413347
theorem B1961487 : Blo 1961435 1961487 := bstep (se 1 (by rfl) ⟨1471115, by rfl⟩ : syracuseStep 1961487 = 2942231) B2942231
theorem B2942237 : Blo 1961435 2942237 := bbase (se 3 (by rfl) ⟨551669, by rfl⟩ : syracuseStep 2942237 = 1103339) (by norm_num)
theorem B1961491 : Blo 1961435 1961491 := bstep (se 1 (by rfl) ⟨1471118, by rfl⟩ : syracuseStep 1961491 = 2942237) B2942237
theorem B4413365 : Blo 1961435 4413365 := bbase (se 5 (by rfl) ⟨206876, by rfl⟩ : syracuseStep 4413365 = 413753) (by norm_num)
theorem B2942243 : Blo 1961435 2942243 := bstep (se 1 (by rfl) ⟨2206682, by rfl⟩ : syracuseStep 2942243 = 4413365) B4413365
theorem B1961495 : Blo 1961435 1961495 := bstep (se 1 (by rfl) ⟨1471121, by rfl⟩ : syracuseStep 1961495 = 2942243) B2942243
theorem B4712917 : Blo 1961435 4712917 := bbase (se 7 (by rfl) ⟨55229, by rfl⟩ : syracuseStep 4712917 = 110459) (by norm_num)
theorem B6283889 : Blo 1961435 6283889 := bstep (se 2 (by rfl) ⟨2356458, by rfl⟩ : syracuseStep 6283889 = 4712917) B4712917
theorem B4189259 : Blo 1961435 4189259 := bstep (se 1 (by rfl) ⟨3141944, by rfl⟩ : syracuseStep 4189259 = 6283889) B6283889
theorem B11171357 : Blo 1961435 11171357 := bstep (se 3 (by rfl) ⟨2094629, by rfl⟩ : syracuseStep 11171357 = 4189259) B4189259
theorem B7447571 : Blo 1961435 7447571 := bstep (se 1 (by rfl) ⟨5585678, by rfl⟩ : syracuseStep 7447571 = 11171357) B11171357
theorem B4965047 : Blo 1961435 4965047 := bstep (se 1 (by rfl) ⟨3723785, by rfl⟩ : syracuseStep 4965047 = 7447571) B7447571
theorem B3310031 : Blo 1961435 3310031 := bstep (se 1 (by rfl) ⟨2482523, by rfl⟩ : syracuseStep 3310031 = 4965047) B4965047
theorem B2206687 : Blo 1961435 2206687 := bstep (se 1 (by rfl) ⟨1655015, by rfl⟩ : syracuseStep 2206687 = 3310031) B3310031
theorem B2942249 : Blo 1961435 2942249 := bstep (se 2 (by rfl) ⟨1103343, by rfl⟩ : syracuseStep 2942249 = 2206687) B2206687
theorem B1961499 : Blo 1961435 1961499 := bstep (se 1 (by rfl) ⟨1471124, by rfl⟩ : syracuseStep 1961499 = 2942249) B2942249
theorem B3631805 : Blo 1961435 3631805 := bbase (se 3 (by rfl) ⟨680963, by rfl⟩ : syracuseStep 3631805 = 1361927) (by norm_num)
theorem B2421203 : Blo 1961435 2421203 := bstep (se 1 (by rfl) ⟨1815902, by rfl⟩ : syracuseStep 2421203 = 3631805) B3631805
theorem B25826165 : Blo 1961435 25826165 := bstep (se 5 (by rfl) ⟨1210601, by rfl⟩ : syracuseStep 25826165 = 2421203) B2421203
theorem B17217443 : Blo 1961435 17217443 := bstep (se 1 (by rfl) ⟨12913082, by rfl⟩ : syracuseStep 17217443 = 25826165) B25826165
theorem B11478295 : Blo 1961435 11478295 := bstep (se 1 (by rfl) ⟨8608721, by rfl⟩ : syracuseStep 11478295 = 17217443) B17217443
theorem B15304393 : Blo 1961435 15304393 := bstep (se 2 (by rfl) ⟨5739147, by rfl⟩ : syracuseStep 15304393 = 11478295) B11478295
theorem B20405857 : Blo 1961435 20405857 := bstep (se 2 (by rfl) ⟨7652196, by rfl⟩ : syracuseStep 20405857 = 15304393) B15304393
theorem B27207809 : Blo 1961435 27207809 := bstep (se 2 (by rfl) ⟨10202928, by rfl⟩ : syracuseStep 27207809 = 20405857) B20405857
theorem B18138539 : Blo 1961435 18138539 := bstep (se 1 (by rfl) ⟨13603904, by rfl⟩ : syracuseStep 18138539 = 27207809) B27207809
theorem B12092359 : Blo 1961435 12092359 := bstep (se 1 (by rfl) ⟨9069269, by rfl⟩ : syracuseStep 12092359 = 18138539) B18138539
theorem B16123145 : Blo 1961435 16123145 := bstep (se 2 (by rfl) ⟨6046179, by rfl⟩ : syracuseStep 16123145 = 12092359) B12092359
theorem B42995053 : Blo 1961435 42995053 := bstep (se 3 (by rfl) ⟨8061572, by rfl⟩ : syracuseStep 42995053 = 16123145) B16123145
theorem B229306949 : Blo 1961435 229306949 := bstep (se 4 (by rfl) ⟨21497526, by rfl⟩ : syracuseStep 229306949 = 42995053) B42995053
theorem B152871299 : Blo 1961435 152871299 := bstep (se 1 (by rfl) ⟨114653474, by rfl⟩ : syracuseStep 152871299 = 229306949) B229306949
theorem B101914199 : Blo 1961435 101914199 := bstep (se 1 (by rfl) ⟨76435649, by rfl⟩ : syracuseStep 101914199 = 152871299) B152871299
theorem B67942799 : Blo 1961435 67942799 := bstep (se 1 (by rfl) ⟨50957099, by rfl⟩ : syracuseStep 67942799 = 101914199) B101914199
theorem B45295199 : Blo 1961435 45295199 := bstep (se 1 (by rfl) ⟨33971399, by rfl⟩ : syracuseStep 45295199 = 67942799) B67942799
theorem B30196799 : Blo 1961435 30196799 := bstep (se 1 (by rfl) ⟨22647599, by rfl⟩ : syracuseStep 30196799 = 45295199) B45295199
theorem B20131199 : Blo 1961435 20131199 := bstep (se 1 (by rfl) ⟨15098399, by rfl⟩ : syracuseStep 20131199 = 30196799) B30196799
theorem B13420799 : Blo 1961435 13420799 := bstep (se 1 (by rfl) ⟨10065599, by rfl⟩ : syracuseStep 13420799 = 20131199) B20131199
theorem B8947199 : Blo 1961435 8947199 := bstep (se 1 (by rfl) ⟨6710399, by rfl⟩ : syracuseStep 8947199 = 13420799) B13420799
theorem B5964799 : Blo 1961435 5964799 := bstep (se 1 (by rfl) ⟨4473599, by rfl⟩ : syracuseStep 5964799 = 8947199) B8947199
theorem B7953065 : Blo 1961435 7953065 := bstep (se 2 (by rfl) ⟨2982399, by rfl⟩ : syracuseStep 7953065 = 5964799) B5964799
theorem B5302043 : Blo 1961435 5302043 := bstep (se 1 (by rfl) ⟨3976532, by rfl⟩ : syracuseStep 5302043 = 7953065) B7953065
theorem B3534695 : Blo 1961435 3534695 := bstep (se 1 (by rfl) ⟨2651021, by rfl⟩ : syracuseStep 3534695 = 5302043) B5302043
theorem B2356463 : Blo 1961435 2356463 := bstep (se 1 (by rfl) ⟨1767347, by rfl⟩ : syracuseStep 2356463 = 3534695) B3534695
theorem B6283901 : Blo 1961435 6283901 := bstep (se 3 (by rfl) ⟨1178231, by rfl⟩ : syracuseStep 6283901 = 2356463) B2356463
theorem B4189267 : Blo 1961435 4189267 := bstep (se 1 (by rfl) ⟨3141950, by rfl⟩ : syracuseStep 4189267 = 6283901) B6283901
theorem B5585689 : Blo 1961435 5585689 := bstep (se 2 (by rfl) ⟨2094633, by rfl⟩ : syracuseStep 5585689 = 4189267) B4189267
theorem B7447585 : Blo 1961435 7447585 := bstep (se 2 (by rfl) ⟨2792844, by rfl⟩ : syracuseStep 7447585 = 5585689) B5585689
theorem B9930113 : Blo 1961435 9930113 := bstep (se 2 (by rfl) ⟨3723792, by rfl⟩ : syracuseStep 9930113 = 7447585) B7447585
theorem B6620075 : Blo 1961435 6620075 := bstep (se 1 (by rfl) ⟨4965056, by rfl⟩ : syracuseStep 6620075 = 9930113) B9930113
theorem B4413383 : Blo 1961435 4413383 := bstep (se 1 (by rfl) ⟨3310037, by rfl⟩ : syracuseStep 4413383 = 6620075) B6620075
theorem B2942255 : Blo 1961435 2942255 := bstep (se 1 (by rfl) ⟨2206691, by rfl⟩ : syracuseStep 2942255 = 4413383) B4413383
theorem B1961503 : Blo 1961435 1961503 := bstep (se 1 (by rfl) ⟨1471127, by rfl⟩ : syracuseStep 1961503 = 2942255) B2942255
theorem B2942261 : Blo 1961435 2942261 := bbase (se 5 (by rfl) ⟨137918, by rfl⟩ : syracuseStep 2942261 = 275837) (by norm_num)
theorem B1961507 : Blo 1961435 1961507 := bstep (se 1 (by rfl) ⟨1471130, by rfl⟩ : syracuseStep 1961507 = 2942261) B2942261
theorem B4965077 : Blo 1961435 4965077 := bbase (se 7 (by rfl) ⟨58184, by rfl⟩ : syracuseStep 4965077 = 116369) (by norm_num)
theorem B3310051 : Blo 1961435 3310051 := bstep (se 1 (by rfl) ⟨2482538, by rfl⟩ : syracuseStep 3310051 = 4965077) B4965077
theorem B4413401 : Blo 1961435 4413401 := bstep (se 2 (by rfl) ⟨1655025, by rfl⟩ : syracuseStep 4413401 = 3310051) B3310051
theorem B2942267 : Blo 1961435 2942267 := bstep (se 1 (by rfl) ⟨2206700, by rfl⟩ : syracuseStep 2942267 = 4413401) B4413401
theorem B1961511 : Blo 1961435 1961511 := bstep (se 1 (by rfl) ⟨1471133, by rfl⟩ : syracuseStep 1961511 = 2942267) B2942267
theorem B2206705 : Blo 1961435 2206705 := bbase (se 2 (by rfl) ⟨827514, by rfl⟩ : syracuseStep 2206705 = 1655029) (by norm_num)
theorem B2942273 : Blo 1961435 2942273 := bstep (se 2 (by rfl) ⟨1103352, by rfl⟩ : syracuseStep 2942273 = 2206705) B2206705
theorem B1961515 : Blo 1961435 1961515 := bstep (se 1 (by rfl) ⟨1471136, by rfl⟩ : syracuseStep 1961515 = 2942273) B2942273
theorem B6710453 : Blo 1961435 6710453 := bbase (se 5 (by rfl) ⟨314552, by rfl⟩ : syracuseStep 6710453 = 629105) (by norm_num)
theorem B4473635 : Blo 1961435 4473635 := bstep (se 1 (by rfl) ⟨3355226, by rfl⟩ : syracuseStep 4473635 = 6710453) B6710453
theorem B11929693 : Blo 1961435 11929693 := bstep (se 3 (by rfl) ⟨2236817, by rfl⟩ : syracuseStep 11929693 = 4473635) B4473635
theorem B15906257 : Blo 1961435 15906257 := bstep (se 2 (by rfl) ⟨5964846, by rfl⟩ : syracuseStep 15906257 = 11929693) B11929693
theorem B10604171 : Blo 1961435 10604171 := bstep (se 1 (by rfl) ⟨7953128, by rfl⟩ : syracuseStep 10604171 = 15906257) B15906257
theorem B7069447 : Blo 1961435 7069447 := bstep (se 1 (by rfl) ⟨5302085, by rfl⟩ : syracuseStep 7069447 = 10604171) B10604171
theorem B9425929 : Blo 1961435 9425929 := bstep (se 2 (by rfl) ⟨3534723, by rfl⟩ : syracuseStep 9425929 = 7069447) B7069447
theorem B12567905 : Blo 1961435 12567905 := bstep (se 2 (by rfl) ⟨4712964, by rfl⟩ : syracuseStep 12567905 = 9425929) B9425929
theorem B8378603 : Blo 1961435 8378603 := bstep (se 1 (by rfl) ⟨6283952, by rfl⟩ : syracuseStep 8378603 = 12567905) B12567905
theorem B5585735 : Blo 1961435 5585735 := bstep (se 1 (by rfl) ⟨4189301, by rfl⟩ : syracuseStep 5585735 = 8378603) B8378603
theorem B3723823 : Blo 1961435 3723823 := bstep (se 1 (by rfl) ⟨2792867, by rfl⟩ : syracuseStep 3723823 = 5585735) B5585735
theorem B4965097 : Blo 1961435 4965097 := bstep (se 2 (by rfl) ⟨1861911, by rfl⟩ : syracuseStep 4965097 = 3723823) B3723823
theorem B6620129 : Blo 1961435 6620129 := bstep (se 2 (by rfl) ⟨2482548, by rfl⟩ : syracuseStep 6620129 = 4965097) B4965097
theorem B4413419 : Blo 1961435 4413419 := bstep (se 1 (by rfl) ⟨3310064, by rfl⟩ : syracuseStep 4413419 = 6620129) B6620129
theorem B2942279 : Blo 1961435 2942279 := bstep (se 1 (by rfl) ⟨2206709, by rfl⟩ : syracuseStep 2942279 = 4413419) B4413419
theorem B1961519 : Blo 1961435 1961519 := bstep (se 1 (by rfl) ⟨1471139, by rfl⟩ : syracuseStep 1961519 = 2942279) B2942279
theorem B2942285 : Blo 1961435 2942285 := bbase (se 3 (by rfl) ⟨551678, by rfl⟩ : syracuseStep 2942285 = 1103357) (by norm_num)
theorem B1961523 : Blo 1961435 1961523 := bstep (se 1 (by rfl) ⟨1471142, by rfl⟩ : syracuseStep 1961523 = 2942285) B2942285
theorem B4413437 : Blo 1961435 4413437 := bbase (se 3 (by rfl) ⟨827519, by rfl⟩ : syracuseStep 4413437 = 1655039) (by norm_num)
theorem B2942291 : Blo 1961435 2942291 := bstep (se 1 (by rfl) ⟨2206718, by rfl⟩ : syracuseStep 2942291 = 4413437) B4413437
theorem B1961527 : Blo 1961435 1961527 := bstep (se 1 (by rfl) ⟨1471145, by rfl⟩ : syracuseStep 1961527 = 2942291) B2942291
theorem B3310085 : Blo 1961435 3310085 := bbase (se 4 (by rfl) ⟨310320, by rfl⟩ : syracuseStep 3310085 = 620641) (by norm_num)
theorem B2206723 : Blo 1961435 2206723 := bstep (se 1 (by rfl) ⟨1655042, by rfl⟩ : syracuseStep 2206723 = 3310085) B3310085
theorem B2942297 : Blo 1961435 2942297 := bstep (se 2 (by rfl) ⟨1103361, by rfl⟩ : syracuseStep 2942297 = 2206723) B2206723
theorem B1961531 : Blo 1961435 1961531 := bstep (se 1 (by rfl) ⟨1471148, by rfl⟩ : syracuseStep 1961531 = 2942297) B2942297
theorem B14895413 : Blo 1961435 14895413 := bbase (se 5 (by rfl) ⟨698222, by rfl⟩ : syracuseStep 14895413 = 1396445) (by norm_num)
theorem B9930275 : Blo 1961435 9930275 := bstep (se 1 (by rfl) ⟨7447706, by rfl⟩ : syracuseStep 9930275 = 14895413) B14895413
theorem B6620183 : Blo 1961435 6620183 := bstep (se 1 (by rfl) ⟨4965137, by rfl⟩ : syracuseStep 6620183 = 9930275) B9930275
theorem B4413455 : Blo 1961435 4413455 := bstep (se 1 (by rfl) ⟨3310091, by rfl⟩ : syracuseStep 4413455 = 6620183) B6620183
theorem B2942303 : Blo 1961435 2942303 := bstep (se 1 (by rfl) ⟨2206727, by rfl⟩ : syracuseStep 2942303 = 4413455) B4413455
theorem B1961535 : Blo 1961435 1961535 := bstep (se 1 (by rfl) ⟨1471151, by rfl⟩ : syracuseStep 1961535 = 2942303) B2942303
theorem B2942309 : Blo 1961435 2942309 := bbase (se 4 (by rfl) ⟨275841, by rfl⟩ : syracuseStep 2942309 = 551683) (by norm_num)
theorem B1961539 : Blo 1961435 1961539 := bstep (se 1 (by rfl) ⟨1471154, by rfl⟩ : syracuseStep 1961539 = 2942309) B2942309
theorem B3723869 : Blo 1961435 3723869 := bbase (se 3 (by rfl) ⟨698225, by rfl⟩ : syracuseStep 3723869 = 1396451) (by norm_num)
theorem B2482579 : Blo 1961435 2482579 := bstep (se 1 (by rfl) ⟨1861934, by rfl⟩ : syracuseStep 2482579 = 3723869) B3723869
theorem B3310105 : Blo 1961435 3310105 := bstep (se 2 (by rfl) ⟨1241289, by rfl⟩ : syracuseStep 3310105 = 2482579) B2482579
theorem B4413473 : Blo 1961435 4413473 := bstep (se 2 (by rfl) ⟨1655052, by rfl⟩ : syracuseStep 4413473 = 3310105) B3310105
theorem B2942315 : Blo 1961435 2942315 := bstep (se 1 (by rfl) ⟨2206736, by rfl⟩ : syracuseStep 2942315 = 4413473) B4413473
theorem B1961543 : Blo 1961435 1961543 := bstep (se 1 (by rfl) ⟨1471157, by rfl⟩ : syracuseStep 1961543 = 2942315) B2942315
theorem B2206741 : Blo 1961435 2206741 := bbase (se 6 (by rfl) ⟨51720, by rfl⟩ : syracuseStep 2206741 = 103441) (by norm_num)
theorem B2942321 : Blo 1961435 2942321 := bstep (se 2 (by rfl) ⟨1103370, by rfl⟩ : syracuseStep 2942321 = 2206741) B2206741
theorem B1961547 : Blo 1961435 1961547 := bstep (se 1 (by rfl) ⟨1471160, by rfl⟩ : syracuseStep 1961547 = 2942321) B2942321
theorem B2482589 : Blo 1961435 2482589 := bbase (se 3 (by rfl) ⟨465485, by rfl⟩ : syracuseStep 2482589 = 930971) (by norm_num)
theorem B6620237 : Blo 1961435 6620237 := bstep (se 3 (by rfl) ⟨1241294, by rfl⟩ : syracuseStep 6620237 = 2482589) B2482589
theorem B4413491 : Blo 1961435 4413491 := bstep (se 1 (by rfl) ⟨3310118, by rfl⟩ : syracuseStep 4413491 = 6620237) B6620237
theorem B2942327 : Blo 1961435 2942327 := bstep (se 1 (by rfl) ⟨2206745, by rfl⟩ : syracuseStep 2942327 = 4413491) B4413491
theorem B1961551 : Blo 1961435 1961551 := bstep (se 1 (by rfl) ⟨1471163, by rfl⟩ : syracuseStep 1961551 = 2942327) B2942327
theorem B2942333 : Blo 1961435 2942333 := bbase (se 3 (by rfl) ⟨551687, by rfl⟩ : syracuseStep 2942333 = 1103375) (by norm_num)
theorem B1961555 : Blo 1961435 1961555 := bstep (se 1 (by rfl) ⟨1471166, by rfl⟩ : syracuseStep 1961555 = 2942333) B2942333
theorem B4413509 : Blo 1961435 4413509 := bbase (se 4 (by rfl) ⟨413766, by rfl⟩ : syracuseStep 4413509 = 827533) (by norm_num)
theorem B2942339 : Blo 1961435 2942339 := bstep (se 1 (by rfl) ⟨2206754, by rfl⟩ : syracuseStep 2942339 = 4413509) B4413509
theorem B1961559 : Blo 1961435 1961559 := bstep (se 1 (by rfl) ⟨1471169, by rfl⟩ : syracuseStep 1961559 = 2942339) B2942339
theorem B5585861 : Blo 1961435 5585861 := bbase (se 4 (by rfl) ⟨523674, by rfl⟩ : syracuseStep 5585861 = 1047349) (by norm_num)
theorem B3723907 : Blo 1961435 3723907 := bstep (se 1 (by rfl) ⟨2792930, by rfl⟩ : syracuseStep 3723907 = 5585861) B5585861
theorem B4965209 : Blo 1961435 4965209 := bstep (se 2 (by rfl) ⟨1861953, by rfl⟩ : syracuseStep 4965209 = 3723907) B3723907
theorem B3310139 : Blo 1961435 3310139 := bstep (se 1 (by rfl) ⟨2482604, by rfl⟩ : syracuseStep 3310139 = 4965209) B4965209
theorem B2206759 : Blo 1961435 2206759 := bstep (se 1 (by rfl) ⟨1655069, by rfl⟩ : syracuseStep 2206759 = 3310139) B3310139
theorem B2942345 : Blo 1961435 2942345 := bstep (se 2 (by rfl) ⟨1103379, by rfl⟩ : syracuseStep 2942345 = 2206759) B2206759
theorem B1961563 : Blo 1961435 1961563 := bstep (se 1 (by rfl) ⟨1471172, by rfl⟩ : syracuseStep 1961563 = 2942345) B2942345
theorem B9930437 : Blo 1961435 9930437 := bbase (se 4 (by rfl) ⟨930978, by rfl⟩ : syracuseStep 9930437 = 1861957) (by norm_num)
theorem B6620291 : Blo 1961435 6620291 := bstep (se 1 (by rfl) ⟨4965218, by rfl⟩ : syracuseStep 6620291 = 9930437) B9930437
theorem B4413527 : Blo 1961435 4413527 := bstep (se 1 (by rfl) ⟨3310145, by rfl⟩ : syracuseStep 4413527 = 6620291) B6620291
theorem B2942351 : Blo 1961435 2942351 := bstep (se 1 (by rfl) ⟨2206763, by rfl⟩ : syracuseStep 2942351 = 4413527) B4413527
theorem B1961567 : Blo 1961435 1961567 := bstep (se 1 (by rfl) ⟨1471175, by rfl⟩ : syracuseStep 1961567 = 2942351) B2942351
theorem B2942357 : Blo 1961435 2942357 := bbase (se 6 (by rfl) ⟨68961, by rfl⟩ : syracuseStep 2942357 = 137923) (by norm_num)
theorem B1961571 : Blo 1961435 1961571 := bstep (se 1 (by rfl) ⟨1471178, by rfl⟩ : syracuseStep 1961571 = 2942357) B2942357
theorem B4189421 : Blo 1961435 4189421 := bbase (se 3 (by rfl) ⟨785516, by rfl⟩ : syracuseStep 4189421 = 1571033) (by norm_num)
theorem B11171789 : Blo 1961435 11171789 := bstep (se 3 (by rfl) ⟨2094710, by rfl⟩ : syracuseStep 11171789 = 4189421) B4189421
theorem B7447859 : Blo 1961435 7447859 := bstep (se 1 (by rfl) ⟨5585894, by rfl⟩ : syracuseStep 7447859 = 11171789) B11171789
theorem B4965239 : Blo 1961435 4965239 := bstep (se 1 (by rfl) ⟨3723929, by rfl⟩ : syracuseStep 4965239 = 7447859) B7447859
theorem B3310159 : Blo 1961435 3310159 := bstep (se 1 (by rfl) ⟨2482619, by rfl⟩ : syracuseStep 3310159 = 4965239) B4965239
theorem B4413545 : Blo 1961435 4413545 := bstep (se 2 (by rfl) ⟨1655079, by rfl⟩ : syracuseStep 4413545 = 3310159) B3310159
theorem B2942363 : Blo 1961435 2942363 := bstep (se 1 (by rfl) ⟨2206772, by rfl⟩ : syracuseStep 2942363 = 4413545) B4413545
theorem B1961575 : Blo 1961435 1961575 := bstep (se 1 (by rfl) ⟨1471181, by rfl⟩ : syracuseStep 1961575 = 2942363) B2942363
theorem B2206777 : Blo 1961435 2206777 := bbase (se 2 (by rfl) ⟨827541, by rfl⟩ : syracuseStep 2206777 = 1655083) (by norm_num)
theorem B2942369 : Blo 1961435 2942369 := bstep (se 2 (by rfl) ⟨1103388, by rfl⟩ : syracuseStep 2942369 = 2206777) B2206777
theorem B1961579 : Blo 1961435 1961579 := bstep (se 1 (by rfl) ⟨1471184, by rfl⟩ : syracuseStep 1961579 = 2942369) B2942369
theorem B3184949 : Blo 1961435 3184949 := bbase (se 5 (by rfl) ⟨149294, by rfl⟩ : syracuseStep 3184949 = 298589) (by norm_num)
theorem B2123299 : Blo 1961435 2123299 := bstep (se 1 (by rfl) ⟨1592474, by rfl⟩ : syracuseStep 2123299 = 3184949) B3184949
theorem B11324261 : Blo 1961435 11324261 := bstep (se 4 (by rfl) ⟨1061649, by rfl⟩ : syracuseStep 11324261 = 2123299) B2123299
theorem B7549507 : Blo 1961435 7549507 := bstep (se 1 (by rfl) ⟨5662130, by rfl⟩ : syracuseStep 7549507 = 11324261) B11324261
theorem B40264037 : Blo 1961435 40264037 := bstep (se 4 (by rfl) ⟨3774753, by rfl⟩ : syracuseStep 40264037 = 7549507) B7549507
theorem B26842691 : Blo 1961435 26842691 := bstep (se 1 (by rfl) ⟨20132018, by rfl⟩ : syracuseStep 26842691 = 40264037) B40264037
theorem B17895127 : Blo 1961435 17895127 := bstep (se 1 (by rfl) ⟨13421345, by rfl⟩ : syracuseStep 17895127 = 26842691) B26842691
theorem B23860169 : Blo 1961435 23860169 := bstep (se 2 (by rfl) ⟨8947563, by rfl⟩ : syracuseStep 23860169 = 17895127) B17895127
theorem B15906779 : Blo 1961435 15906779 := bstep (se 1 (by rfl) ⟨11930084, by rfl⟩ : syracuseStep 15906779 = 23860169) B23860169
theorem B10604519 : Blo 1961435 10604519 := bstep (se 1 (by rfl) ⟨7953389, by rfl⟩ : syracuseStep 10604519 = 15906779) B15906779
theorem B7069679 : Blo 1961435 7069679 := bstep (se 1 (by rfl) ⟨5302259, by rfl⟩ : syracuseStep 7069679 = 10604519) B10604519
theorem B4713119 : Blo 1961435 4713119 := bstep (se 1 (by rfl) ⟨3534839, by rfl⟩ : syracuseStep 4713119 = 7069679) B7069679
theorem B3142079 : Blo 1961435 3142079 := bstep (se 1 (by rfl) ⟨2356559, by rfl⟩ : syracuseStep 3142079 = 4713119) B4713119
theorem B2094719 : Blo 1961435 2094719 := bstep (se 1 (by rfl) ⟨1571039, by rfl⟩ : syracuseStep 2094719 = 3142079) B3142079
theorem B5585917 : Blo 1961435 5585917 := bstep (se 3 (by rfl) ⟨1047359, by rfl⟩ : syracuseStep 5585917 = 2094719) B2094719
theorem B7447889 : Blo 1961435 7447889 := bstep (se 2 (by rfl) ⟨2792958, by rfl⟩ : syracuseStep 7447889 = 5585917) B5585917
theorem B4965259 : Blo 1961435 4965259 := bstep (se 1 (by rfl) ⟨3723944, by rfl⟩ : syracuseStep 4965259 = 7447889) B7447889
theorem B6620345 : Blo 1961435 6620345 := bstep (se 2 (by rfl) ⟨2482629, by rfl⟩ : syracuseStep 6620345 = 4965259) B4965259
theorem B4413563 : Blo 1961435 4413563 := bstep (se 1 (by rfl) ⟨3310172, by rfl⟩ : syracuseStep 4413563 = 6620345) B6620345
theorem B2942375 : Blo 1961435 2942375 := bstep (se 1 (by rfl) ⟨2206781, by rfl⟩ : syracuseStep 2942375 = 4413563) B4413563
theorem B1961583 : Blo 1961435 1961583 := bstep (se 1 (by rfl) ⟨1471187, by rfl⟩ : syracuseStep 1961583 = 2942375) B2942375
theorem B2942381 : Blo 1961435 2942381 := bbase (se 3 (by rfl) ⟨551696, by rfl⟩ : syracuseStep 2942381 = 1103393) (by norm_num)
theorem B1961587 : Blo 1961435 1961587 := bstep (se 1 (by rfl) ⟨1471190, by rfl⟩ : syracuseStep 1961587 = 2942381) B2942381
theorem B4413581 : Blo 1961435 4413581 := bbase (se 3 (by rfl) ⟨827546, by rfl⟩ : syracuseStep 4413581 = 1655093) (by norm_num)
theorem B2942387 : Blo 1961435 2942387 := bstep (se 1 (by rfl) ⟨2206790, by rfl⟩ : syracuseStep 2942387 = 4413581) B4413581
theorem B1961591 : Blo 1961435 1961591 := bstep (se 1 (by rfl) ⟨1471193, by rfl⟩ : syracuseStep 1961591 = 2942387) B2942387
theorem B2482645 : Blo 1961435 2482645 := bbase (se 7 (by rfl) ⟨29093, by rfl⟩ : syracuseStep 2482645 = 58187) (by norm_num)
theorem B3310193 : Blo 1961435 3310193 := bstep (se 2 (by rfl) ⟨1241322, by rfl⟩ : syracuseStep 3310193 = 2482645) B2482645
theorem B2206795 : Blo 1961435 2206795 := bstep (se 1 (by rfl) ⟨1655096, by rfl⟩ : syracuseStep 2206795 = 3310193) B3310193
theorem B2942393 : Blo 1961435 2942393 := bstep (se 2 (by rfl) ⟨1103397, by rfl⟩ : syracuseStep 2942393 = 2206795) B2206795
theorem B1961595 : Blo 1961435 1961595 := bstep (se 1 (by rfl) ⟨1471196, by rfl⟩ : syracuseStep 1961595 = 2942393) B2942393
theorem B3023237 : Blo 1961435 3023237 := bbase (se 4 (by rfl) ⟨283428, by rfl⟩ : syracuseStep 3023237 = 566857) (by norm_num)
theorem B2015491 : Blo 1961435 2015491 := bstep (se 1 (by rfl) ⟨1511618, by rfl⟩ : syracuseStep 2015491 = 3023237) B3023237
theorem B2687321 : Blo 1961435 2687321 := bstep (se 2 (by rfl) ⟨1007745, by rfl⟩ : syracuseStep 2687321 = 2015491) B2015491
theorem B7166189 : Blo 1961435 7166189 := bstep (se 3 (by rfl) ⟨1343660, by rfl⟩ : syracuseStep 7166189 = 2687321) B2687321
theorem B19109837 : Blo 1961435 19109837 := bstep (se 3 (by rfl) ⟨3583094, by rfl⟩ : syracuseStep 19109837 = 7166189) B7166189
theorem B12739891 : Blo 1961435 12739891 := bstep (se 1 (by rfl) ⟨9554918, by rfl⟩ : syracuseStep 12739891 = 19109837) B19109837
theorem B16986521 : Blo 1961435 16986521 := bstep (se 2 (by rfl) ⟨6369945, by rfl⟩ : syracuseStep 16986521 = 12739891) B12739891
theorem B11324347 : Blo 1961435 11324347 := bstep (se 1 (by rfl) ⟨8493260, by rfl⟩ : syracuseStep 11324347 = 16986521) B16986521
theorem B60396517 : Blo 1961435 60396517 := bstep (se 4 (by rfl) ⟨5662173, by rfl⟩ : syracuseStep 60396517 = 11324347) B11324347
theorem B80528689 : Blo 1961435 80528689 := bstep (se 2 (by rfl) ⟨30198258, by rfl⟩ : syracuseStep 80528689 = 60396517) B60396517
theorem B107371585 : Blo 1961435 107371585 := bstep (se 2 (by rfl) ⟨40264344, by rfl⟩ : syracuseStep 107371585 = 80528689) B80528689
theorem B143162113 : Blo 1961435 143162113 := bstep (se 2 (by rfl) ⟨53685792, by rfl⟩ : syracuseStep 143162113 = 107371585) B107371585
theorem B190882817 : Blo 1961435 190882817 := bstep (se 2 (by rfl) ⟨71581056, by rfl⟩ : syracuseStep 190882817 = 143162113) B143162113
theorem B127255211 : Blo 1961435 127255211 := bstep (se 1 (by rfl) ⟨95441408, by rfl⟩ : syracuseStep 127255211 = 190882817) B190882817
theorem B84836807 : Blo 1961435 84836807 := bstep (se 1 (by rfl) ⟨63627605, by rfl⟩ : syracuseStep 84836807 = 127255211) B127255211
theorem B56557871 : Blo 1961435 56557871 := bstep (se 1 (by rfl) ⟨42418403, by rfl⟩ : syracuseStep 56557871 = 84836807) B84836807
theorem B37705247 : Blo 1961435 37705247 := bstep (se 1 (by rfl) ⟨28278935, by rfl⟩ : syracuseStep 37705247 = 56557871) B56557871
theorem B25136831 : Blo 1961435 25136831 := bstep (se 1 (by rfl) ⟨18852623, by rfl⟩ : syracuseStep 25136831 = 37705247) B37705247
theorem B16757887 : Blo 1961435 16757887 := bstep (se 1 (by rfl) ⟨12568415, by rfl⟩ : syracuseStep 16757887 = 25136831) B25136831
theorem B22343849 : Blo 1961435 22343849 := bstep (se 2 (by rfl) ⟨8378943, by rfl⟩ : syracuseStep 22343849 = 16757887) B16757887
theorem B14895899 : Blo 1961435 14895899 := bstep (se 1 (by rfl) ⟨11171924, by rfl⟩ : syracuseStep 14895899 = 22343849) B22343849
theorem B9930599 : Blo 1961435 9930599 := bstep (se 1 (by rfl) ⟨7447949, by rfl⟩ : syracuseStep 9930599 = 14895899) B14895899
theorem B6620399 : Blo 1961435 6620399 := bstep (se 1 (by rfl) ⟨4965299, by rfl⟩ : syracuseStep 6620399 = 9930599) B9930599
theorem B4413599 : Blo 1961435 4413599 := bstep (se 1 (by rfl) ⟨3310199, by rfl⟩ : syracuseStep 4413599 = 6620399) B6620399
theorem B2942399 : Blo 1961435 2942399 := bstep (se 1 (by rfl) ⟨2206799, by rfl⟩ : syracuseStep 2942399 = 4413599) B4413599
theorem B1961599 : Blo 1961435 1961599 := bstep (se 1 (by rfl) ⟨1471199, by rfl⟩ : syracuseStep 1961599 = 2942399) B2942399
theorem B2942405 : Blo 1961435 2942405 := bbase (se 4 (by rfl) ⟨275850, by rfl⟩ : syracuseStep 2942405 = 551701) (by norm_num)
theorem B1961603 : Blo 1961435 1961603 := bstep (se 1 (by rfl) ⟨1471202, by rfl⟩ : syracuseStep 1961603 = 2942405) B2942405
theorem B3310213 : Blo 1961435 3310213 := bbase (se 4 (by rfl) ⟨310332, by rfl⟩ : syracuseStep 3310213 = 620665) (by norm_num)
theorem B4413617 : Blo 1961435 4413617 := bstep (se 2 (by rfl) ⟨1655106, by rfl⟩ : syracuseStep 4413617 = 3310213) B3310213
theorem B2942411 : Blo 1961435 2942411 := bstep (se 1 (by rfl) ⟨2206808, by rfl⟩ : syracuseStep 2942411 = 4413617) B4413617
theorem B1961607 : Blo 1961435 1961607 := bstep (se 1 (by rfl) ⟨1471205, by rfl⟩ : syracuseStep 1961607 = 2942411) B2942411
theorem B2206813 : Blo 1961435 2206813 := bbase (se 3 (by rfl) ⟨413777, by rfl⟩ : syracuseStep 2206813 = 827555) (by norm_num)
theorem B2942417 : Blo 1961435 2942417 := bstep (se 2 (by rfl) ⟨1103406, by rfl⟩ : syracuseStep 2942417 = 2206813) B2206813
theorem B1961611 : Blo 1961435 1961611 := bstep (se 1 (by rfl) ⟨1471208, by rfl⟩ : syracuseStep 1961611 = 2942417) B2942417
theorem B6620453 : Blo 1961435 6620453 := bbase (se 4 (by rfl) ⟨620667, by rfl⟩ : syracuseStep 6620453 = 1241335) (by norm_num)
theorem B4413635 : Blo 1961435 4413635 := bstep (se 1 (by rfl) ⟨3310226, by rfl⟩ : syracuseStep 4413635 = 6620453) B6620453
theorem B2942423 : Blo 1961435 2942423 := bstep (se 1 (by rfl) ⟨2206817, by rfl⟩ : syracuseStep 2942423 = 4413635) B4413635
theorem B1961615 : Blo 1961435 1961615 := bstep (se 1 (by rfl) ⟨1471211, by rfl⟩ : syracuseStep 1961615 = 2942423) B2942423
theorem B2942429 : Blo 1961435 2942429 := bbase (se 3 (by rfl) ⟨551705, by rfl⟩ : syracuseStep 2942429 = 1103411) (by norm_num)
theorem B1961619 : Blo 1961435 1961619 := bstep (se 1 (by rfl) ⟨1471214, by rfl⟩ : syracuseStep 1961619 = 2942429) B2942429
theorem B4413653 : Blo 1961435 4413653 := bbase (se 7 (by rfl) ⟨51722, by rfl⟩ : syracuseStep 4413653 = 103445) (by norm_num)
theorem B2942435 : Blo 1961435 2942435 := bstep (se 1 (by rfl) ⟨2206826, by rfl⟩ : syracuseStep 2942435 = 4413653) B4413653
theorem B1961623 : Blo 1961435 1961623 := bstep (se 1 (by rfl) ⟨1471217, by rfl⟩ : syracuseStep 1961623 = 2942435) B2942435
theorem B2651189 : Blo 1961435 2651189 := bbase (se 5 (by rfl) ⟨124274, by rfl⟩ : syracuseStep 2651189 = 248549) (by norm_num)
theorem B7069837 : Blo 1961435 7069837 := bstep (se 3 (by rfl) ⟨1325594, by rfl⟩ : syracuseStep 7069837 = 2651189) B2651189
theorem B9426449 : Blo 1961435 9426449 := bstep (se 2 (by rfl) ⟨3534918, by rfl⟩ : syracuseStep 9426449 = 7069837) B7069837
theorem B6284299 : Blo 1961435 6284299 := bstep (se 1 (by rfl) ⟨4713224, by rfl⟩ : syracuseStep 6284299 = 9426449) B9426449
theorem B8379065 : Blo 1961435 8379065 := bstep (se 2 (by rfl) ⟨3142149, by rfl⟩ : syracuseStep 8379065 = 6284299) B6284299
theorem B5586043 : Blo 1961435 5586043 := bstep (se 1 (by rfl) ⟨4189532, by rfl⟩ : syracuseStep 5586043 = 8379065) B8379065
theorem B7448057 : Blo 1961435 7448057 := bstep (se 2 (by rfl) ⟨2793021, by rfl⟩ : syracuseStep 7448057 = 5586043) B5586043
theorem B4965371 : Blo 1961435 4965371 := bstep (se 1 (by rfl) ⟨3724028, by rfl⟩ : syracuseStep 4965371 = 7448057) B7448057
theorem B3310247 : Blo 1961435 3310247 := bstep (se 1 (by rfl) ⟨2482685, by rfl⟩ : syracuseStep 3310247 = 4965371) B4965371
theorem B2206831 : Blo 1961435 2206831 := bstep (se 1 (by rfl) ⟨1655123, by rfl⟩ : syracuseStep 2206831 = 3310247) B3310247
theorem B2942441 : Blo 1961435 2942441 := bstep (se 2 (by rfl) ⟨1103415, by rfl⟩ : syracuseStep 2942441 = 2206831) B2206831
theorem B1961627 : Blo 1961435 1961627 := bstep (se 1 (by rfl) ⟨1471220, by rfl⟩ : syracuseStep 1961627 = 2942441) B2942441
theorem B3534925 : Blo 1961435 3534925 := bbase (se 3 (by rfl) ⟨662798, by rfl⟩ : syracuseStep 3534925 = 1325597) (by norm_num)
theorem B4713233 : Blo 1961435 4713233 := bstep (se 2 (by rfl) ⟨1767462, by rfl⟩ : syracuseStep 4713233 = 3534925) B3534925
theorem B12568621 : Blo 1961435 12568621 := bstep (se 3 (by rfl) ⟨2356616, by rfl⟩ : syracuseStep 12568621 = 4713233) B4713233
theorem B16758161 : Blo 1961435 16758161 := bstep (se 2 (by rfl) ⟨6284310, by rfl⟩ : syracuseStep 16758161 = 12568621) B12568621
theorem B11172107 : Blo 1961435 11172107 := bstep (se 1 (by rfl) ⟨8379080, by rfl⟩ : syracuseStep 11172107 = 16758161) B16758161
theorem B7448071 : Blo 1961435 7448071 := bstep (se 1 (by rfl) ⟨5586053, by rfl⟩ : syracuseStep 7448071 = 11172107) B11172107
theorem B9930761 : Blo 1961435 9930761 := bstep (se 2 (by rfl) ⟨3724035, by rfl⟩ : syracuseStep 9930761 = 7448071) B7448071
theorem B6620507 : Blo 1961435 6620507 := bstep (se 1 (by rfl) ⟨4965380, by rfl⟩ : syracuseStep 6620507 = 9930761) B9930761
theorem B4413671 : Blo 1961435 4413671 := bstep (se 1 (by rfl) ⟨3310253, by rfl⟩ : syracuseStep 4413671 = 6620507) B6620507
theorem B2942447 : Blo 1961435 2942447 := bstep (se 1 (by rfl) ⟨2206835, by rfl⟩ : syracuseStep 2942447 = 4413671) B4413671
theorem B1961631 : Blo 1961435 1961631 := bstep (se 1 (by rfl) ⟨1471223, by rfl⟩ : syracuseStep 1961631 = 2942447) B2942447
theorem B2942453 : Blo 1961435 2942453 := bbase (se 5 (by rfl) ⟨137927, by rfl⟩ : syracuseStep 2942453 = 275855) (by norm_num)
theorem B1961635 : Blo 1961435 1961635 := bstep (se 1 (by rfl) ⟨1471226, by rfl⟩ : syracuseStep 1961635 = 2942453) B2942453
theorem B3534941 : Blo 1961435 3534941 := bbase (se 3 (by rfl) ⟨662801, by rfl⟩ : syracuseStep 3534941 = 1325603) (by norm_num)
theorem B2356627 : Blo 1961435 2356627 := bstep (se 1 (by rfl) ⟨1767470, by rfl⟩ : syracuseStep 2356627 = 3534941) B3534941
theorem B3142169 : Blo 1961435 3142169 := bstep (se 2 (by rfl) ⟨1178313, by rfl⟩ : syracuseStep 3142169 = 2356627) B2356627
theorem B2094779 : Blo 1961435 2094779 := bstep (se 1 (by rfl) ⟨1571084, by rfl⟩ : syracuseStep 2094779 = 3142169) B3142169
theorem B5586077 : Blo 1961435 5586077 := bstep (se 3 (by rfl) ⟨1047389, by rfl⟩ : syracuseStep 5586077 = 2094779) B2094779
theorem B3724051 : Blo 1961435 3724051 := bstep (se 1 (by rfl) ⟨2793038, by rfl⟩ : syracuseStep 3724051 = 5586077) B5586077
theorem B4965401 : Blo 1961435 4965401 := bstep (se 2 (by rfl) ⟨1862025, by rfl⟩ : syracuseStep 4965401 = 3724051) B3724051
theorem B3310267 : Blo 1961435 3310267 := bstep (se 1 (by rfl) ⟨2482700, by rfl⟩ : syracuseStep 3310267 = 4965401) B4965401
theorem B4413689 : Blo 1961435 4413689 := bstep (se 2 (by rfl) ⟨1655133, by rfl⟩ : syracuseStep 4413689 = 3310267) B3310267
theorem B2942459 : Blo 1961435 2942459 := bstep (se 1 (by rfl) ⟨2206844, by rfl⟩ : syracuseStep 2942459 = 4413689) B4413689
theorem B1961639 : Blo 1961435 1961639 := bstep (se 1 (by rfl) ⟨1471229, by rfl⟩ : syracuseStep 1961639 = 2942459) B2942459
theorem B2206849 : Blo 1961435 2206849 := bbase (se 2 (by rfl) ⟨827568, by rfl⟩ : syracuseStep 2206849 = 1655137) (by norm_num)
theorem B2942465 : Blo 1961435 2942465 := bstep (se 2 (by rfl) ⟨1103424, by rfl⟩ : syracuseStep 2942465 = 2206849) B2206849
theorem B1961643 : Blo 1961435 1961643 := bstep (se 1 (by rfl) ⟨1471232, by rfl⟩ : syracuseStep 1961643 = 2942465) B2942465
theorem B4965421 : Blo 1961435 4965421 := bbase (se 3 (by rfl) ⟨931016, by rfl⟩ : syracuseStep 4965421 = 1862033) (by norm_num)
theorem B6620561 : Blo 1961435 6620561 := bstep (se 2 (by rfl) ⟨2482710, by rfl⟩ : syracuseStep 6620561 = 4965421) B4965421
theorem B4413707 : Blo 1961435 4413707 := bstep (se 1 (by rfl) ⟨3310280, by rfl⟩ : syracuseStep 4413707 = 6620561) B6620561
theorem B2942471 : Blo 1961435 2942471 := bstep (se 1 (by rfl) ⟨2206853, by rfl⟩ : syracuseStep 2942471 = 4413707) B4413707
theorem B1961647 : Blo 1961435 1961647 := bstep (se 1 (by rfl) ⟨1471235, by rfl⟩ : syracuseStep 1961647 = 2942471) B2942471
theorem B2942477 : Blo 1961435 2942477 := bbase (se 3 (by rfl) ⟨551714, by rfl⟩ : syracuseStep 2942477 = 1103429) (by norm_num)
theorem B1961651 : Blo 1961435 1961651 := bstep (se 1 (by rfl) ⟨1471238, by rfl⟩ : syracuseStep 1961651 = 2942477) B2942477
theorem B4413725 : Blo 1961435 4413725 := bbase (se 3 (by rfl) ⟨827573, by rfl⟩ : syracuseStep 4413725 = 1655147) (by norm_num)
theorem B2942483 : Blo 1961435 2942483 := bstep (se 1 (by rfl) ⟨2206862, by rfl⟩ : syracuseStep 2942483 = 4413725) B4413725
theorem B1961655 : Blo 1961435 1961655 := bstep (se 1 (by rfl) ⟨1471241, by rfl⟩ : syracuseStep 1961655 = 2942483) B2942483
theorem B3310301 : Blo 1961435 3310301 := bbase (se 3 (by rfl) ⟨620681, by rfl⟩ : syracuseStep 3310301 = 1241363) (by norm_num)
theorem B2206867 : Blo 1961435 2206867 := bstep (se 1 (by rfl) ⟨1655150, by rfl⟩ : syracuseStep 2206867 = 3310301) B3310301
theorem B2942489 : Blo 1961435 2942489 := bstep (se 2 (by rfl) ⟨1103433, by rfl⟩ : syracuseStep 2942489 = 2206867) B2206867
theorem B1961659 : Blo 1961435 1961659 := bstep (se 1 (by rfl) ⟨1471244, by rfl⟩ : syracuseStep 1961659 = 2942489) B2942489
theorem B5965285 : Blo 1961435 5965285 := bbase (se 4 (by rfl) ⟨559245, by rfl⟩ : syracuseStep 5965285 = 1118491) (by norm_num)
theorem B7953713 : Blo 1961435 7953713 := bstep (se 2 (by rfl) ⟨2982642, by rfl⟩ : syracuseStep 7953713 = 5965285) B5965285
theorem B5302475 : Blo 1961435 5302475 := bstep (se 1 (by rfl) ⟨3976856, by rfl⟩ : syracuseStep 5302475 = 7953713) B7953713
theorem B3534983 : Blo 1961435 3534983 := bstep (se 1 (by rfl) ⟨2651237, by rfl⟩ : syracuseStep 3534983 = 5302475) B5302475
theorem B2356655 : Blo 1961435 2356655 := bstep (se 1 (by rfl) ⟨1767491, by rfl⟩ : syracuseStep 2356655 = 3534983) B3534983
theorem B6284413 : Blo 1961435 6284413 := bstep (se 3 (by rfl) ⟨1178327, by rfl⟩ : syracuseStep 6284413 = 2356655) B2356655
theorem B8379217 : Blo 1961435 8379217 := bstep (se 2 (by rfl) ⟨3142206, by rfl⟩ : syracuseStep 8379217 = 6284413) B6284413
theorem B11172289 : Blo 1961435 11172289 := bstep (se 2 (by rfl) ⟨4189608, by rfl⟩ : syracuseStep 11172289 = 8379217) B8379217
theorem B14896385 : Blo 1961435 14896385 := bstep (se 2 (by rfl) ⟨5586144, by rfl⟩ : syracuseStep 14896385 = 11172289) B11172289
theorem B9930923 : Blo 1961435 9930923 := bstep (se 1 (by rfl) ⟨7448192, by rfl⟩ : syracuseStep 9930923 = 14896385) B14896385
theorem B6620615 : Blo 1961435 6620615 := bstep (se 1 (by rfl) ⟨4965461, by rfl⟩ : syracuseStep 6620615 = 9930923) B9930923
theorem B4413743 : Blo 1961435 4413743 := bstep (se 1 (by rfl) ⟨3310307, by rfl⟩ : syracuseStep 4413743 = 6620615) B6620615
theorem B2942495 : Blo 1961435 2942495 := bstep (se 1 (by rfl) ⟨2206871, by rfl⟩ : syracuseStep 2942495 = 4413743) B4413743
theorem B1961663 : Blo 1961435 1961663 := bstep (se 1 (by rfl) ⟨1471247, by rfl⟩ : syracuseStep 1961663 = 2942495) B2942495
theorem B2942501 : Blo 1961435 2942501 := bbase (se 4 (by rfl) ⟨275859, by rfl⟩ : syracuseStep 2942501 = 551719) (by norm_num)
theorem B1961667 : Blo 1961435 1961667 := bstep (se 1 (by rfl) ⟨1471250, by rfl⟩ : syracuseStep 1961667 = 2942501) B2942501
theorem B2482741 : Blo 1961435 2482741 := bbase (se 5 (by rfl) ⟨116378, by rfl⟩ : syracuseStep 2482741 = 232757) (by norm_num)
theorem B3310321 : Blo 1961435 3310321 := bstep (se 2 (by rfl) ⟨1241370, by rfl⟩ : syracuseStep 3310321 = 2482741) B2482741
theorem B4413761 : Blo 1961435 4413761 := bstep (se 2 (by rfl) ⟨1655160, by rfl⟩ : syracuseStep 4413761 = 3310321) B3310321
theorem B2942507 : Blo 1961435 2942507 := bstep (se 1 (by rfl) ⟨2206880, by rfl⟩ : syracuseStep 2942507 = 4413761) B4413761
theorem B1961671 : Blo 1961435 1961671 := bstep (se 1 (by rfl) ⟨1471253, by rfl⟩ : syracuseStep 1961671 = 2942507) B2942507
theorem B2206885 : Blo 1961435 2206885 := bbase (se 4 (by rfl) ⟨206895, by rfl⟩ : syracuseStep 2206885 = 413791) (by norm_num)
theorem B2942513 : Blo 1961435 2942513 := bstep (se 2 (by rfl) ⟨1103442, by rfl⟩ : syracuseStep 2942513 = 2206885) B2206885
theorem B1961675 : Blo 1961435 1961675 := bstep (se 1 (by rfl) ⟨1471256, by rfl⟩ : syracuseStep 1961675 = 2942513) B2942513
theorem B18853397 : Blo 1961435 18853397 := bbase (se 6 (by rfl) ⟨441876, by rfl⟩ : syracuseStep 18853397 = 883753) (by norm_num)
theorem B12568931 : Blo 1961435 12568931 := bstep (se 1 (by rfl) ⟨9426698, by rfl⟩ : syracuseStep 12568931 = 18853397) B18853397
theorem B8379287 : Blo 1961435 8379287 := bstep (se 1 (by rfl) ⟨6284465, by rfl⟩ : syracuseStep 8379287 = 12568931) B12568931
theorem B5586191 : Blo 1961435 5586191 := bstep (se 1 (by rfl) ⟨4189643, by rfl⟩ : syracuseStep 5586191 = 8379287) B8379287
theorem B3724127 : Blo 1961435 3724127 := bstep (se 1 (by rfl) ⟨2793095, by rfl⟩ : syracuseStep 3724127 = 5586191) B5586191
theorem B2482751 : Blo 1961435 2482751 := bstep (se 1 (by rfl) ⟨1862063, by rfl⟩ : syracuseStep 2482751 = 3724127) B3724127
theorem B6620669 : Blo 1961435 6620669 := bstep (se 3 (by rfl) ⟨1241375, by rfl⟩ : syracuseStep 6620669 = 2482751) B2482751
theorem B4413779 : Blo 1961435 4413779 := bstep (se 1 (by rfl) ⟨3310334, by rfl⟩ : syracuseStep 4413779 = 6620669) B6620669
theorem B2942519 : Blo 1961435 2942519 := bstep (se 1 (by rfl) ⟨2206889, by rfl⟩ : syracuseStep 2942519 = 4413779) B4413779
theorem B1961679 : Blo 1961435 1961679 := bstep (se 1 (by rfl) ⟨1471259, by rfl⟩ : syracuseStep 1961679 = 2942519) B2942519
theorem B2942525 : Blo 1961435 2942525 := bbase (se 3 (by rfl) ⟨551723, by rfl⟩ : syracuseStep 2942525 = 1103447) (by norm_num)
theorem B1961683 : Blo 1961435 1961683 := bstep (se 1 (by rfl) ⟨1471262, by rfl⟩ : syracuseStep 1961683 = 2942525) B2942525
theorem B4413797 : Blo 1961435 4413797 := bbase (se 4 (by rfl) ⟨413793, by rfl⟩ : syracuseStep 4413797 = 827587) (by norm_num)
theorem B2942531 : Blo 1961435 2942531 := bstep (se 1 (by rfl) ⟨2206898, by rfl⟩ : syracuseStep 2942531 = 4413797) B4413797
theorem B1961687 : Blo 1961435 1961687 := bstep (se 1 (by rfl) ⟨1471265, by rfl⟩ : syracuseStep 1961687 = 2942531) B2942531
theorem B4965533 : Blo 1961435 4965533 := bbase (se 3 (by rfl) ⟨931037, by rfl⟩ : syracuseStep 4965533 = 1862075) (by norm_num)
theorem B3310355 : Blo 1961435 3310355 := bstep (se 1 (by rfl) ⟨2482766, by rfl⟩ : syracuseStep 3310355 = 4965533) B4965533
theorem B2206903 : Blo 1961435 2206903 := bstep (se 1 (by rfl) ⟨1655177, by rfl⟩ : syracuseStep 2206903 = 3310355) B3310355
theorem B2942537 : Blo 1961435 2942537 := bstep (se 2 (by rfl) ⟨1103451, by rfl⟩ : syracuseStep 2942537 = 2206903) B2206903
theorem B1961691 : Blo 1961435 1961691 := bstep (se 1 (by rfl) ⟨1471268, by rfl⟩ : syracuseStep 1961691 = 2942537) B2942537
theorem B3724157 : Blo 1961435 3724157 := bbase (se 3 (by rfl) ⟨698279, by rfl⟩ : syracuseStep 3724157 = 1396559) (by norm_num)
theorem B9931085 : Blo 1961435 9931085 := bstep (se 3 (by rfl) ⟨1862078, by rfl⟩ : syracuseStep 9931085 = 3724157) B3724157
theorem B6620723 : Blo 1961435 6620723 := bstep (se 1 (by rfl) ⟨4965542, by rfl⟩ : syracuseStep 6620723 = 9931085) B9931085
theorem B4413815 : Blo 1961435 4413815 := bstep (se 1 (by rfl) ⟨3310361, by rfl⟩ : syracuseStep 4413815 = 6620723) B6620723
theorem B2942543 : Blo 1961435 2942543 := bstep (se 1 (by rfl) ⟨2206907, by rfl⟩ : syracuseStep 2942543 = 4413815) B4413815
theorem B1961695 : Blo 1961435 1961695 := bstep (se 1 (by rfl) ⟨1471271, by rfl⟩ : syracuseStep 1961695 = 2942543) B2942543
theorem B2942549 : Blo 1961435 2942549 := bbase (se 8 (by rfl) ⟨17241, by rfl⟩ : syracuseStep 2942549 = 34483) (by norm_num)
theorem B1961699 : Blo 1961435 1961699 := bstep (se 1 (by rfl) ⟨1471274, by rfl⟩ : syracuseStep 1961699 = 2942549) B2942549
theorem B7652981 : Blo 1961435 7652981 := bbase (se 5 (by rfl) ⟨358733, by rfl⟩ : syracuseStep 7652981 = 717467) (by norm_num)
theorem B5101987 : Blo 1961435 5101987 := bstep (se 1 (by rfl) ⟨3826490, by rfl⟩ : syracuseStep 5101987 = 7652981) B7652981
theorem B6802649 : Blo 1961435 6802649 := bstep (se 2 (by rfl) ⟨2550993, by rfl⟩ : syracuseStep 6802649 = 5101987) B5101987
theorem B4535099 : Blo 1961435 4535099 := bstep (se 1 (by rfl) ⟨3401324, by rfl⟩ : syracuseStep 4535099 = 6802649) B6802649
theorem B3023399 : Blo 1961435 3023399 := bstep (se 1 (by rfl) ⟨2267549, by rfl⟩ : syracuseStep 3023399 = 4535099) B4535099
theorem B2015599 : Blo 1961435 2015599 := bstep (se 1 (by rfl) ⟨1511699, by rfl⟩ : syracuseStep 2015599 = 3023399) B3023399
theorem B2687465 : Blo 1961435 2687465 := bstep (se 2 (by rfl) ⟨1007799, by rfl⟩ : syracuseStep 2687465 = 2015599) B2015599
theorem B7166573 : Blo 1961435 7166573 := bstep (se 3 (by rfl) ⟨1343732, by rfl⟩ : syracuseStep 7166573 = 2687465) B2687465
theorem B4777715 : Blo 1961435 4777715 := bstep (se 1 (by rfl) ⟨3583286, by rfl⟩ : syracuseStep 4777715 = 7166573) B7166573
theorem B3185143 : Blo 1961435 3185143 := bstep (se 1 (by rfl) ⟨2388857, by rfl⟩ : syracuseStep 3185143 = 4777715) B4777715
theorem B16987429 : Blo 1961435 16987429 := bstep (se 4 (by rfl) ⟨1592571, by rfl⟩ : syracuseStep 16987429 = 3185143) B3185143
theorem B22649905 : Blo 1961435 22649905 := bstep (se 2 (by rfl) ⟨8493714, by rfl⟩ : syracuseStep 22649905 = 16987429) B16987429
theorem B30199873 : Blo 1961435 30199873 := bstep (se 2 (by rfl) ⟨11324952, by rfl⟩ : syracuseStep 30199873 = 22649905) B22649905
theorem B40266497 : Blo 1961435 40266497 := bstep (se 2 (by rfl) ⟨15099936, by rfl⟩ : syracuseStep 40266497 = 30199873) B30199873
theorem B26844331 : Blo 1961435 26844331 := bstep (se 1 (by rfl) ⟨20133248, by rfl⟩ : syracuseStep 26844331 = 40266497) B40266497
theorem B35792441 : Blo 1961435 35792441 := bstep (se 2 (by rfl) ⟨13422165, by rfl⟩ : syracuseStep 35792441 = 26844331) B26844331
theorem B23861627 : Blo 1961435 23861627 := bstep (se 1 (by rfl) ⟨17896220, by rfl⟩ : syracuseStep 23861627 = 35792441) B35792441
theorem B15907751 : Blo 1961435 15907751 := bstep (se 1 (by rfl) ⟨11930813, by rfl⟩ : syracuseStep 15907751 = 23861627) B23861627
theorem B10605167 : Blo 1961435 10605167 := bstep (se 1 (by rfl) ⟨7953875, by rfl⟩ : syracuseStep 10605167 = 15907751) B15907751
theorem B7070111 : Blo 1961435 7070111 := bstep (se 1 (by rfl) ⟨5302583, by rfl⟩ : syracuseStep 7070111 = 10605167) B10605167
theorem B4713407 : Blo 1961435 4713407 := bstep (se 1 (by rfl) ⟨3535055, by rfl⟩ : syracuseStep 4713407 = 7070111) B7070111
theorem B3142271 : Blo 1961435 3142271 := bstep (se 1 (by rfl) ⟨2356703, by rfl⟩ : syracuseStep 3142271 = 4713407) B4713407
theorem B8379389 : Blo 1961435 8379389 := bstep (se 3 (by rfl) ⟨1571135, by rfl⟩ : syracuseStep 8379389 = 3142271) B3142271
theorem B5586259 : Blo 1961435 5586259 := bstep (se 1 (by rfl) ⟨4189694, by rfl⟩ : syracuseStep 5586259 = 8379389) B8379389
theorem B7448345 : Blo 1961435 7448345 := bstep (se 2 (by rfl) ⟨2793129, by rfl⟩ : syracuseStep 7448345 = 5586259) B5586259
theorem B4965563 : Blo 1961435 4965563 := bstep (se 1 (by rfl) ⟨3724172, by rfl⟩ : syracuseStep 4965563 = 7448345) B7448345
theorem B3310375 : Blo 1961435 3310375 := bstep (se 1 (by rfl) ⟨2482781, by rfl⟩ : syracuseStep 3310375 = 4965563) B4965563
theorem B4413833 : Blo 1961435 4413833 := bstep (se 2 (by rfl) ⟨1655187, by rfl⟩ : syracuseStep 4413833 = 3310375) B3310375
theorem B2942555 : Blo 1961435 2942555 := bstep (se 1 (by rfl) ⟨2206916, by rfl⟩ : syracuseStep 2942555 = 4413833) B4413833
theorem B1961703 : Blo 1961435 1961703 := bstep (se 1 (by rfl) ⟨1471277, by rfl⟩ : syracuseStep 1961703 = 2942555) B2942555
theorem B2206921 : Blo 1961435 2206921 := bbase (se 2 (by rfl) ⟨827595, by rfl⟩ : syracuseStep 2206921 = 1655191) (by norm_num)
theorem B2942561 : Blo 1961435 2942561 := bstep (se 2 (by rfl) ⟨1103460, by rfl⟩ : syracuseStep 2942561 = 2206921) B2206921
theorem B1961707 : Blo 1961435 1961707 := bstep (se 1 (by rfl) ⟨1471280, by rfl⟩ : syracuseStep 1961707 = 2942561) B2942561
theorem B14140277 : Blo 1961435 14140277 := bbase (se 5 (by rfl) ⟨662825, by rfl⟩ : syracuseStep 14140277 = 1325651) (by norm_num)
theorem B9426851 : Blo 1961435 9426851 := bstep (se 1 (by rfl) ⟨7070138, by rfl⟩ : syracuseStep 9426851 = 14140277) B14140277
theorem B6284567 : Blo 1961435 6284567 := bstep (se 1 (by rfl) ⟨4713425, by rfl⟩ : syracuseStep 6284567 = 9426851) B9426851
theorem B16758845 : Blo 1961435 16758845 := bstep (se 3 (by rfl) ⟨3142283, by rfl⟩ : syracuseStep 16758845 = 6284567) B6284567
theorem B11172563 : Blo 1961435 11172563 := bstep (se 1 (by rfl) ⟨8379422, by rfl⟩ : syracuseStep 11172563 = 16758845) B16758845
theorem B7448375 : Blo 1961435 7448375 := bstep (se 1 (by rfl) ⟨5586281, by rfl⟩ : syracuseStep 7448375 = 11172563) B11172563
theorem B4965583 : Blo 1961435 4965583 := bstep (se 1 (by rfl) ⟨3724187, by rfl⟩ : syracuseStep 4965583 = 7448375) B7448375
theorem B6620777 : Blo 1961435 6620777 := bstep (se 2 (by rfl) ⟨2482791, by rfl⟩ : syracuseStep 6620777 = 4965583) B4965583
theorem B4413851 : Blo 1961435 4413851 := bstep (se 1 (by rfl) ⟨3310388, by rfl⟩ : syracuseStep 4413851 = 6620777) B6620777
theorem B2942567 : Blo 1961435 2942567 := bstep (se 1 (by rfl) ⟨2206925, by rfl⟩ : syracuseStep 2942567 = 4413851) B4413851
theorem B1961711 : Blo 1961435 1961711 := bstep (se 1 (by rfl) ⟨1471283, by rfl⟩ : syracuseStep 1961711 = 2942567) B2942567
theorem B2942573 : Blo 1961435 2942573 := bbase (se 3 (by rfl) ⟨551732, by rfl⟩ : syracuseStep 2942573 = 1103465) (by norm_num)
theorem B1961715 : Blo 1961435 1961715 := bstep (se 1 (by rfl) ⟨1471286, by rfl⟩ : syracuseStep 1961715 = 2942573) B2942573
theorem B4413869 : Blo 1961435 4413869 := bbase (se 3 (by rfl) ⟨827600, by rfl⟩ : syracuseStep 4413869 = 1655201) (by norm_num)
theorem B2942579 : Blo 1961435 2942579 := bstep (se 1 (by rfl) ⟨2206934, by rfl⟩ : syracuseStep 2942579 = 4413869) B4413869
theorem B1961719 : Blo 1961435 1961719 := bstep (se 1 (by rfl) ⟨1471289, by rfl⟩ : syracuseStep 1961719 = 2942579) B2942579
theorem B2094869 : Blo 1961435 2094869 := bbase (se 6 (by rfl) ⟨49098, by rfl⟩ : syracuseStep 2094869 = 98197) (by norm_num)
theorem B5586317 : Blo 1961435 5586317 := bstep (se 3 (by rfl) ⟨1047434, by rfl⟩ : syracuseStep 5586317 = 2094869) B2094869
theorem B3724211 : Blo 1961435 3724211 := bstep (se 1 (by rfl) ⟨2793158, by rfl⟩ : syracuseStep 3724211 = 5586317) B5586317
theorem B2482807 : Blo 1961435 2482807 := bstep (se 1 (by rfl) ⟨1862105, by rfl⟩ : syracuseStep 2482807 = 3724211) B3724211
theorem B3310409 : Blo 1961435 3310409 := bstep (se 2 (by rfl) ⟨1241403, by rfl⟩ : syracuseStep 3310409 = 2482807) B2482807
theorem B2206939 : Blo 1961435 2206939 := bstep (se 1 (by rfl) ⟨1655204, by rfl⟩ : syracuseStep 2206939 = 3310409) B3310409
theorem B2942585 : Blo 1961435 2942585 := bstep (se 2 (by rfl) ⟨1103469, by rfl⟩ : syracuseStep 2942585 = 2206939) B2206939
theorem B1961723 : Blo 1961435 1961723 := bstep (se 1 (by rfl) ⟨1471292, by rfl⟩ : syracuseStep 1961723 = 2942585) B2942585
theorem B23861909 : Blo 1961435 23861909 := bbase (se 6 (by rfl) ⟨559263, by rfl⟩ : syracuseStep 23861909 = 1118527) (by norm_num)
theorem B63631757 : Blo 1961435 63631757 := bstep (se 3 (by rfl) ⟨11930954, by rfl⟩ : syracuseStep 63631757 = 23861909) B23861909
theorem B42421171 : Blo 1961435 42421171 := bstep (se 1 (by rfl) ⟨31815878, by rfl⟩ : syracuseStep 42421171 = 63631757) B63631757
theorem B56561561 : Blo 1961435 56561561 := bstep (se 2 (by rfl) ⟨21210585, by rfl⟩ : syracuseStep 56561561 = 42421171) B42421171
theorem B37707707 : Blo 1961435 37707707 := bstep (se 1 (by rfl) ⟨28280780, by rfl⟩ : syracuseStep 37707707 = 56561561) B56561561
theorem B25138471 : Blo 1961435 25138471 := bstep (se 1 (by rfl) ⟨18853853, by rfl⟩ : syracuseStep 25138471 = 37707707) B37707707
theorem B33517961 : Blo 1961435 33517961 := bstep (se 2 (by rfl) ⟨12569235, by rfl⟩ : syracuseStep 33517961 = 25138471) B25138471
theorem B22345307 : Blo 1961435 22345307 := bstep (se 1 (by rfl) ⟨16758980, by rfl⟩ : syracuseStep 22345307 = 33517961) B33517961
theorem B14896871 : Blo 1961435 14896871 := bstep (se 1 (by rfl) ⟨11172653, by rfl⟩ : syracuseStep 14896871 = 22345307) B22345307
theorem B9931247 : Blo 1961435 9931247 := bstep (se 1 (by rfl) ⟨7448435, by rfl⟩ : syracuseStep 9931247 = 14896871) B14896871
theorem B6620831 : Blo 1961435 6620831 := bstep (se 1 (by rfl) ⟨4965623, by rfl⟩ : syracuseStep 6620831 = 9931247) B9931247
theorem B4413887 : Blo 1961435 4413887 := bstep (se 1 (by rfl) ⟨3310415, by rfl⟩ : syracuseStep 4413887 = 6620831) B6620831
theorem B2942591 : Blo 1961435 2942591 := bstep (se 1 (by rfl) ⟨2206943, by rfl⟩ : syracuseStep 2942591 = 4413887) B4413887
theorem B1961727 : Blo 1961435 1961727 := bstep (se 1 (by rfl) ⟨1471295, by rfl⟩ : syracuseStep 1961727 = 2942591) B2942591
theorem B2942597 : Blo 1961435 2942597 := bbase (se 4 (by rfl) ⟨275868, by rfl⟩ : syracuseStep 2942597 = 551737) (by norm_num)
theorem B1961731 : Blo 1961435 1961731 := bstep (se 1 (by rfl) ⟨1471298, by rfl⟩ : syracuseStep 1961731 = 2942597) B2942597
theorem B3310429 : Blo 1961435 3310429 := bbase (se 3 (by rfl) ⟨620705, by rfl⟩ : syracuseStep 3310429 = 1241411) (by norm_num)
theorem B4413905 : Blo 1961435 4413905 := bstep (se 2 (by rfl) ⟨1655214, by rfl⟩ : syracuseStep 4413905 = 3310429) B3310429
theorem B2942603 : Blo 1961435 2942603 := bstep (se 1 (by rfl) ⟨2206952, by rfl⟩ : syracuseStep 2942603 = 4413905) B4413905
theorem B1961735 : Blo 1961435 1961735 := bstep (se 1 (by rfl) ⟨1471301, by rfl⟩ : syracuseStep 1961735 = 2942603) B2942603
theorem B2206957 : Blo 1961435 2206957 := bbase (se 3 (by rfl) ⟨413804, by rfl⟩ : syracuseStep 2206957 = 827609) (by norm_num)
theorem B2942609 : Blo 1961435 2942609 := bstep (se 2 (by rfl) ⟨1103478, by rfl⟩ : syracuseStep 2942609 = 2206957) B2206957
theorem B1961739 : Blo 1961435 1961739 := bstep (se 1 (by rfl) ⟨1471304, by rfl⟩ : syracuseStep 1961739 = 2942609) B2942609
theorem B6620885 : Blo 1961435 6620885 := bbase (se 7 (by rfl) ⟨77588, by rfl⟩ : syracuseStep 6620885 = 155177) (by norm_num)
theorem B4413923 : Blo 1961435 4413923 := bstep (se 1 (by rfl) ⟨3310442, by rfl⟩ : syracuseStep 4413923 = 6620885) B6620885
theorem B2942615 : Blo 1961435 2942615 := bstep (se 1 (by rfl) ⟨2206961, by rfl⟩ : syracuseStep 2942615 = 4413923) B4413923
theorem B1961743 : Blo 1961435 1961743 := bstep (se 1 (by rfl) ⟨1471307, by rfl⟩ : syracuseStep 1961743 = 2942615) B2942615
theorem B2942621 : Blo 1961435 2942621 := bbase (se 3 (by rfl) ⟨551741, by rfl⟩ : syracuseStep 2942621 = 1103483) (by norm_num)
theorem B1961747 : Blo 1961435 1961747 := bstep (se 1 (by rfl) ⟨1471310, by rfl⟩ : syracuseStep 1961747 = 2942621) B2942621
theorem B4413941 : Blo 1961435 4413941 := bbase (se 5 (by rfl) ⟨206903, by rfl⟩ : syracuseStep 4413941 = 413807) (by norm_num)
theorem B2942627 : Blo 1961435 2942627 := bstep (se 1 (by rfl) ⟨2206970, by rfl⟩ : syracuseStep 2942627 = 4413941) B4413941
theorem B1961751 : Blo 1961435 1961751 := bstep (se 1 (by rfl) ⟨1471313, by rfl⟩ : syracuseStep 1961751 = 2942627) B2942627
theorem B7954085 : Blo 1961435 7954085 := bbase (se 4 (by rfl) ⟨745695, by rfl⟩ : syracuseStep 7954085 = 1491391) (by norm_num)
theorem B21210893 : Blo 1961435 21210893 := bstep (se 3 (by rfl) ⟨3977042, by rfl⟩ : syracuseStep 21210893 = 7954085) B7954085
theorem B14140595 : Blo 1961435 14140595 := bstep (se 1 (by rfl) ⟨10605446, by rfl⟩ : syracuseStep 14140595 = 21210893) B21210893
theorem B37708253 : Blo 1961435 37708253 := bstep (se 3 (by rfl) ⟨7070297, by rfl⟩ : syracuseStep 37708253 = 14140595) B14140595
theorem B25138835 : Blo 1961435 25138835 := bstep (se 1 (by rfl) ⟨18854126, by rfl⟩ : syracuseStep 25138835 = 37708253) B37708253
theorem B16759223 : Blo 1961435 16759223 := bstep (se 1 (by rfl) ⟨12569417, by rfl⟩ : syracuseStep 16759223 = 25138835) B25138835
theorem B11172815 : Blo 1961435 11172815 := bstep (se 1 (by rfl) ⟨8379611, by rfl⟩ : syracuseStep 11172815 = 16759223) B16759223
theorem B7448543 : Blo 1961435 7448543 := bstep (se 1 (by rfl) ⟨5586407, by rfl⟩ : syracuseStep 7448543 = 11172815) B11172815
theorem B4965695 : Blo 1961435 4965695 := bstep (se 1 (by rfl) ⟨3724271, by rfl⟩ : syracuseStep 4965695 = 7448543) B7448543
theorem B3310463 : Blo 1961435 3310463 := bstep (se 1 (by rfl) ⟨2482847, by rfl⟩ : syracuseStep 3310463 = 4965695) B4965695
theorem B2206975 : Blo 1961435 2206975 := bstep (se 1 (by rfl) ⟨1655231, by rfl⟩ : syracuseStep 2206975 = 3310463) B3310463
theorem B2942633 : Blo 1961435 2942633 := bstep (se 2 (by rfl) ⟨1103487, by rfl⟩ : syracuseStep 2942633 = 2206975) B2206975
theorem B1961755 : Blo 1961435 1961755 := bstep (se 1 (by rfl) ⟨1471316, by rfl⟩ : syracuseStep 1961755 = 2942633) B2942633
theorem B3535157 : Blo 1961435 3535157 := bbase (se 5 (by rfl) ⟨165710, by rfl⟩ : syracuseStep 3535157 = 331421) (by norm_num)
theorem B2356771 : Blo 1961435 2356771 := bstep (se 1 (by rfl) ⟨1767578, by rfl⟩ : syracuseStep 2356771 = 3535157) B3535157
theorem B3142361 : Blo 1961435 3142361 := bstep (se 2 (by rfl) ⟨1178385, by rfl⟩ : syracuseStep 3142361 = 2356771) B2356771
theorem B2094907 : Blo 1961435 2094907 := bstep (se 1 (by rfl) ⟨1571180, by rfl⟩ : syracuseStep 2094907 = 3142361) B3142361
theorem B2793209 : Blo 1961435 2793209 := bstep (se 2 (by rfl) ⟨1047453, by rfl⟩ : syracuseStep 2793209 = 2094907) B2094907
theorem B7448557 : Blo 1961435 7448557 := bstep (se 3 (by rfl) ⟨1396604, by rfl⟩ : syracuseStep 7448557 = 2793209) B2793209
theorem B9931409 : Blo 1961435 9931409 := bstep (se 2 (by rfl) ⟨3724278, by rfl⟩ : syracuseStep 9931409 = 7448557) B7448557
theorem B6620939 : Blo 1961435 6620939 := bstep (se 1 (by rfl) ⟨4965704, by rfl⟩ : syracuseStep 6620939 = 9931409) B9931409
theorem B4413959 : Blo 1961435 4413959 := bstep (se 1 (by rfl) ⟨3310469, by rfl⟩ : syracuseStep 4413959 = 6620939) B6620939
theorem B2942639 : Blo 1961435 2942639 := bstep (se 1 (by rfl) ⟨2206979, by rfl⟩ : syracuseStep 2942639 = 4413959) B4413959
theorem B1961759 : Blo 1961435 1961759 := bstep (se 1 (by rfl) ⟨1471319, by rfl⟩ : syracuseStep 1961759 = 2942639) B2942639
theorem B2942645 : Blo 1961435 2942645 := bbase (se 5 (by rfl) ⟨137936, by rfl⟩ : syracuseStep 2942645 = 275873) (by norm_num)
theorem B1961763 : Blo 1961435 1961763 := bstep (se 1 (by rfl) ⟨1471322, by rfl⟩ : syracuseStep 1961763 = 2942645) B2942645
theorem B4965725 : Blo 1961435 4965725 := bbase (se 3 (by rfl) ⟨931073, by rfl⟩ : syracuseStep 4965725 = 1862147) (by norm_num)
theorem B3310483 : Blo 1961435 3310483 := bstep (se 1 (by rfl) ⟨2482862, by rfl⟩ : syracuseStep 3310483 = 4965725) B4965725
theorem B4413977 : Blo 1961435 4413977 := bstep (se 2 (by rfl) ⟨1655241, by rfl⟩ : syracuseStep 4413977 = 3310483) B3310483
theorem B2942651 : Blo 1961435 2942651 := bstep (se 1 (by rfl) ⟨2206988, by rfl⟩ : syracuseStep 2942651 = 4413977) B4413977
theorem B1961767 : Blo 1961435 1961767 := bstep (se 1 (by rfl) ⟨1471325, by rfl⟩ : syracuseStep 1961767 = 2942651) B2942651
theorem B2206993 : Blo 1961435 2206993 := bbase (se 2 (by rfl) ⟨827622, by rfl⟩ : syracuseStep 2206993 = 1655245) (by norm_num)
theorem B2942657 : Blo 1961435 2942657 := bstep (se 2 (by rfl) ⟨1103496, by rfl⟩ : syracuseStep 2942657 = 2206993) B2206993
theorem B1961771 : Blo 1961435 1961771 := bstep (se 1 (by rfl) ⟨1471328, by rfl⟩ : syracuseStep 1961771 = 2942657) B2942657
theorem B3724309 : Blo 1961435 3724309 := bbase (se 6 (by rfl) ⟨87288, by rfl⟩ : syracuseStep 3724309 = 174577) (by norm_num)
theorem B4965745 : Blo 1961435 4965745 := bstep (se 2 (by rfl) ⟨1862154, by rfl⟩ : syracuseStep 4965745 = 3724309) B3724309
theorem B6620993 : Blo 1961435 6620993 := bstep (se 2 (by rfl) ⟨2482872, by rfl⟩ : syracuseStep 6620993 = 4965745) B4965745
theorem B4413995 : Blo 1961435 4413995 := bstep (se 1 (by rfl) ⟨3310496, by rfl⟩ : syracuseStep 4413995 = 6620993) B6620993
theorem B2942663 : Blo 1961435 2942663 := bstep (se 1 (by rfl) ⟨2206997, by rfl⟩ : syracuseStep 2942663 = 4413995) B4413995
theorem B1961775 : Blo 1961435 1961775 := bstep (se 1 (by rfl) ⟨1471331, by rfl⟩ : syracuseStep 1961775 = 2942663) B2942663
theorem B2942669 : Blo 1961435 2942669 := bbase (se 3 (by rfl) ⟨551750, by rfl⟩ : syracuseStep 2942669 = 1103501) (by norm_num)
theorem B1961779 : Blo 1961435 1961779 := bstep (se 1 (by rfl) ⟨1471334, by rfl⟩ : syracuseStep 1961779 = 2942669) B2942669
theorem B4414013 : Blo 1961435 4414013 := bbase (se 3 (by rfl) ⟨827627, by rfl⟩ : syracuseStep 4414013 = 1655255) (by norm_num)
theorem B2942675 : Blo 1961435 2942675 := bstep (se 1 (by rfl) ⟨2207006, by rfl⟩ : syracuseStep 2942675 = 4414013) B4414013
theorem B1961783 : Blo 1961435 1961783 := bstep (se 1 (by rfl) ⟨1471337, by rfl⟩ : syracuseStep 1961783 = 2942675) B2942675
theorem B3310517 : Blo 1961435 3310517 := bbase (se 5 (by rfl) ⟨155180, by rfl⟩ : syracuseStep 3310517 = 310361) (by norm_num)
theorem B2207011 : Blo 1961435 2207011 := bstep (se 1 (by rfl) ⟨1655258, by rfl⟩ : syracuseStep 2207011 = 3310517) B3310517
theorem B2942681 : Blo 1961435 2942681 := bstep (se 2 (by rfl) ⟨1103505, by rfl⟩ : syracuseStep 2942681 = 2207011) B2207011
theorem B1961787 : Blo 1961435 1961787 := bstep (se 1 (by rfl) ⟨1471340, by rfl⟩ : syracuseStep 1961787 = 2942681) B2942681
theorem B2094941 : Blo 1961435 2094941 := bbase (se 3 (by rfl) ⟨392801, by rfl⟩ : syracuseStep 2094941 = 785603) (by norm_num)
theorem B5586509 : Blo 1961435 5586509 := bstep (se 3 (by rfl) ⟨1047470, by rfl⟩ : syracuseStep 5586509 = 2094941) B2094941
theorem B14897357 : Blo 1961435 14897357 := bstep (se 3 (by rfl) ⟨2793254, by rfl⟩ : syracuseStep 14897357 = 5586509) B5586509
theorem B9931571 : Blo 1961435 9931571 := bstep (se 1 (by rfl) ⟨7448678, by rfl⟩ : syracuseStep 9931571 = 14897357) B14897357
theorem B6621047 : Blo 1961435 6621047 := bstep (se 1 (by rfl) ⟨4965785, by rfl⟩ : syracuseStep 6621047 = 9931571) B9931571
theorem B4414031 : Blo 1961435 4414031 := bstep (se 1 (by rfl) ⟨3310523, by rfl⟩ : syracuseStep 4414031 = 6621047) B6621047
theorem B2942687 : Blo 1961435 2942687 := bstep (se 1 (by rfl) ⟨2207015, by rfl⟩ : syracuseStep 2942687 = 4414031) B4414031
theorem B1961791 : Blo 1961435 1961791 := bstep (se 1 (by rfl) ⟨1471343, by rfl⟩ : syracuseStep 1961791 = 2942687) B2942687
theorem B2942693 : Blo 1961435 2942693 := bbase (se 4 (by rfl) ⟨275877, by rfl⟩ : syracuseStep 2942693 = 551755) (by norm_num)
theorem B1961795 : Blo 1961435 1961795 := bstep (se 1 (by rfl) ⟨1471346, by rfl⟩ : syracuseStep 1961795 = 2942693) B2942693
theorem B5586533 : Blo 1961435 5586533 := bbase (se 4 (by rfl) ⟨523737, by rfl⟩ : syracuseStep 5586533 = 1047475) (by norm_num)
theorem B3724355 : Blo 1961435 3724355 := bstep (se 1 (by rfl) ⟨2793266, by rfl⟩ : syracuseStep 3724355 = 5586533) B5586533
theorem B2482903 : Blo 1961435 2482903 := bstep (se 1 (by rfl) ⟨1862177, by rfl⟩ : syracuseStep 2482903 = 3724355) B3724355
theorem B3310537 : Blo 1961435 3310537 := bstep (se 2 (by rfl) ⟨1241451, by rfl⟩ : syracuseStep 3310537 = 2482903) B2482903
theorem B4414049 : Blo 1961435 4414049 := bstep (se 2 (by rfl) ⟨1655268, by rfl⟩ : syracuseStep 4414049 = 3310537) B3310537
theorem B2942699 : Blo 1961435 2942699 := bstep (se 1 (by rfl) ⟨2207024, by rfl⟩ : syracuseStep 2942699 = 4414049) B4414049
theorem B1961799 : Blo 1961435 1961799 := bstep (se 1 (by rfl) ⟨1471349, by rfl⟩ : syracuseStep 1961799 = 2942699) B2942699
theorem B2207029 : Blo 1961435 2207029 := bbase (se 5 (by rfl) ⟨103454, by rfl⟩ : syracuseStep 2207029 = 206909) (by norm_num)
theorem B2942705 : Blo 1961435 2942705 := bstep (se 2 (by rfl) ⟨1103514, by rfl⟩ : syracuseStep 2942705 = 2207029) B2207029
theorem B1961803 : Blo 1961435 1961803 := bstep (se 1 (by rfl) ⟨1471352, by rfl⟩ : syracuseStep 1961803 = 2942705) B2942705
theorem B2482913 : Blo 1961435 2482913 := bbase (se 2 (by rfl) ⟨931092, by rfl⟩ : syracuseStep 2482913 = 1862185) (by norm_num)
theorem B6621101 : Blo 1961435 6621101 := bstep (se 3 (by rfl) ⟨1241456, by rfl⟩ : syracuseStep 6621101 = 2482913) B2482913
theorem B4414067 : Blo 1961435 4414067 := bstep (se 1 (by rfl) ⟨3310550, by rfl⟩ : syracuseStep 4414067 = 6621101) B6621101
theorem B2942711 : Blo 1961435 2942711 := bstep (se 1 (by rfl) ⟨2207033, by rfl⟩ : syracuseStep 2942711 = 4414067) B4414067
theorem B1961807 : Blo 1961435 1961807 := bstep (se 1 (by rfl) ⟨1471355, by rfl⟩ : syracuseStep 1961807 = 2942711) B2942711
theorem B2942717 : Blo 1961435 2942717 := bbase (se 3 (by rfl) ⟨551759, by rfl⟩ : syracuseStep 2942717 = 1103519) (by norm_num)
theorem B1961811 : Blo 1961435 1961811 := bstep (se 1 (by rfl) ⟨1471358, by rfl⟩ : syracuseStep 1961811 = 2942717) B2942717
theorem B4414085 : Blo 1961435 4414085 := bbase (se 4 (by rfl) ⟨413820, by rfl⟩ : syracuseStep 4414085 = 827641) (by norm_num)
theorem B2942723 : Blo 1961435 2942723 := bstep (se 1 (by rfl) ⟨2207042, by rfl⟩ : syracuseStep 2942723 = 4414085) B4414085
theorem B1961815 : Blo 1961435 1961815 := bstep (se 1 (by rfl) ⟨1471361, by rfl⟩ : syracuseStep 1961815 = 2942723) B2942723
theorem B2237161 : Blo 1961435 2237161 := bbase (se 2 (by rfl) ⟨838935, by rfl⟩ : syracuseStep 2237161 = 1677871) (by norm_num)
theorem B2982881 : Blo 1961435 2982881 := bstep (se 2 (by rfl) ⟨1118580, by rfl⟩ : syracuseStep 2982881 = 2237161) B2237161
theorem B1988587 : Blo 1961435 1988587 := bstep (se 1 (by rfl) ⟨1491440, by rfl⟩ : syracuseStep 1988587 = 2982881) B2982881
theorem B2651449 : Blo 1961435 2651449 := bstep (se 2 (by rfl) ⟨994293, by rfl⟩ : syracuseStep 2651449 = 1988587) B1988587
theorem B3535265 : Blo 1961435 3535265 := bstep (se 2 (by rfl) ⟨1325724, by rfl⟩ : syracuseStep 3535265 = 2651449) B2651449
theorem B9427373 : Blo 1961435 9427373 := bstep (se 3 (by rfl) ⟨1767632, by rfl⟩ : syracuseStep 9427373 = 3535265) B3535265
theorem B6284915 : Blo 1961435 6284915 := bstep (se 1 (by rfl) ⟨4713686, by rfl⟩ : syracuseStep 6284915 = 9427373) B9427373
theorem B4189943 : Blo 1961435 4189943 := bstep (se 1 (by rfl) ⟨3142457, by rfl⟩ : syracuseStep 4189943 = 6284915) B6284915
theorem B2793295 : Blo 1961435 2793295 := bstep (se 1 (by rfl) ⟨2094971, by rfl⟩ : syracuseStep 2793295 = 4189943) B4189943
theorem B3724393 : Blo 1961435 3724393 := bstep (se 2 (by rfl) ⟨1396647, by rfl⟩ : syracuseStep 3724393 = 2793295) B2793295
theorem B4965857 : Blo 1961435 4965857 := bstep (se 2 (by rfl) ⟨1862196, by rfl⟩ : syracuseStep 4965857 = 3724393) B3724393
theorem B3310571 : Blo 1961435 3310571 := bstep (se 1 (by rfl) ⟨2482928, by rfl⟩ : syracuseStep 3310571 = 4965857) B4965857
theorem B2207047 : Blo 1961435 2207047 := bstep (se 1 (by rfl) ⟨1655285, by rfl⟩ : syracuseStep 2207047 = 3310571) B3310571
theorem B2942729 : Blo 1961435 2942729 := bstep (se 2 (by rfl) ⟨1103523, by rfl⟩ : syracuseStep 2942729 = 2207047) B2207047
theorem B1961819 : Blo 1961435 1961819 := bstep (se 1 (by rfl) ⟨1471364, by rfl⟩ : syracuseStep 1961819 = 2942729) B2942729
theorem B9931733 : Blo 1961435 9931733 := bbase (se 7 (by rfl) ⟨116387, by rfl⟩ : syracuseStep 9931733 = 232775) (by norm_num)
theorem B6621155 : Blo 1961435 6621155 := bstep (se 1 (by rfl) ⟨4965866, by rfl⟩ : syracuseStep 6621155 = 9931733) B9931733
theorem B4414103 : Blo 1961435 4414103 := bstep (se 1 (by rfl) ⟨3310577, by rfl⟩ : syracuseStep 4414103 = 6621155) B6621155
theorem B2942735 : Blo 1961435 2942735 := bstep (se 1 (by rfl) ⟨2207051, by rfl⟩ : syracuseStep 2942735 = 4414103) B4414103
theorem B1961823 : Blo 1961435 1961823 := bstep (se 1 (by rfl) ⟨1471367, by rfl⟩ : syracuseStep 1961823 = 2942735) B2942735
theorem B2942741 : Blo 1961435 2942741 := bbase (se 6 (by rfl) ⟨68970, by rfl⟩ : syracuseStep 2942741 = 137941) (by norm_num)
theorem B1961827 : Blo 1961435 1961827 := bstep (se 1 (by rfl) ⟨1471370, by rfl⟩ : syracuseStep 1961827 = 2942741) B2942741
theorem B9818581 : Blo 1961435 9818581 := bbase (se 7 (by rfl) ⟨115061, by rfl⟩ : syracuseStep 9818581 = 230123) (by norm_num)
theorem B13091441 : Blo 1961435 13091441 := bstep (se 2 (by rfl) ⟨4909290, by rfl⟩ : syracuseStep 13091441 = 9818581) B9818581
theorem B34910509 : Blo 1961435 34910509 := bstep (se 3 (by rfl) ⟨6545720, by rfl⟩ : syracuseStep 34910509 = 13091441) B13091441
theorem B46547345 : Blo 1961435 46547345 := bstep (se 2 (by rfl) ⟨17455254, by rfl⟩ : syracuseStep 46547345 = 34910509) B34910509
theorem B124126253 : Blo 1961435 124126253 := bstep (se 3 (by rfl) ⟨23273672, by rfl⟩ : syracuseStep 124126253 = 46547345) B46547345
theorem B82750835 : Blo 1961435 82750835 := bstep (se 1 (by rfl) ⟨62063126, by rfl⟩ : syracuseStep 82750835 = 124126253) B124126253
theorem B220668893 : Blo 1961435 220668893 := bstep (se 3 (by rfl) ⟨41375417, by rfl⟩ : syracuseStep 220668893 = 82750835) B82750835
theorem B147112595 : Blo 1961435 147112595 := bstep (se 1 (by rfl) ⟨110334446, by rfl⟩ : syracuseStep 147112595 = 220668893) B220668893
theorem B98075063 : Blo 1961435 98075063 := bstep (se 1 (by rfl) ⟨73556297, by rfl⟩ : syracuseStep 98075063 = 147112595) B147112595
theorem B261533501 : Blo 1961435 261533501 := bstep (se 3 (by rfl) ⟨49037531, by rfl⟩ : syracuseStep 261533501 = 98075063) B98075063
theorem B174355667 : Blo 1961435 174355667 := bstep (se 1 (by rfl) ⟨130766750, by rfl⟩ : syracuseStep 174355667 = 261533501) B261533501
theorem B116237111 : Blo 1961435 116237111 := bstep (se 1 (by rfl) ⟨87177833, by rfl⟩ : syracuseStep 116237111 = 174355667) B174355667
theorem B309965629 : Blo 1961435 309965629 := bstep (se 3 (by rfl) ⟨58118555, by rfl⟩ : syracuseStep 309965629 = 116237111) B116237111
theorem B413287505 : Blo 1961435 413287505 := bstep (se 2 (by rfl) ⟨154982814, by rfl⟩ : syracuseStep 413287505 = 309965629) B309965629
theorem B275525003 : Blo 1961435 275525003 := bstep (se 1 (by rfl) ⟨206643752, by rfl⟩ : syracuseStep 275525003 = 413287505) B413287505
theorem B183683335 : Blo 1961435 183683335 := bstep (se 1 (by rfl) ⟨137762501, by rfl⟩ : syracuseStep 183683335 = 275525003) B275525003
theorem B244911113 : Blo 1961435 244911113 := bstep (se 2 (by rfl) ⟨91841667, by rfl⟩ : syracuseStep 244911113 = 183683335) B183683335
theorem B163274075 : Blo 1961435 163274075 := bstep (se 1 (by rfl) ⟨122455556, by rfl⟩ : syracuseStep 163274075 = 244911113) B244911113
theorem B108849383 : Blo 1961435 108849383 := bstep (se 1 (by rfl) ⟨81637037, by rfl⟩ : syracuseStep 108849383 = 163274075) B163274075
theorem B72566255 : Blo 1961435 72566255 := bstep (se 1 (by rfl) ⟨54424691, by rfl⟩ : syracuseStep 72566255 = 108849383) B108849383
theorem B48377503 : Blo 1961435 48377503 := bstep (se 1 (by rfl) ⟨36283127, by rfl⟩ : syracuseStep 48377503 = 72566255) B72566255
theorem B64503337 : Blo 1961435 64503337 := bstep (se 2 (by rfl) ⟨24188751, by rfl⟩ : syracuseStep 64503337 = 48377503) B48377503
theorem B86004449 : Blo 1961435 86004449 := bstep (se 2 (by rfl) ⟨32251668, by rfl⟩ : syracuseStep 86004449 = 64503337) B64503337
theorem B57336299 : Blo 1961435 57336299 := bstep (se 1 (by rfl) ⟨43002224, by rfl⟩ : syracuseStep 57336299 = 86004449) B86004449
theorem B38224199 : Blo 1961435 38224199 := bstep (se 1 (by rfl) ⟨28668149, by rfl⟩ : syracuseStep 38224199 = 57336299) B57336299
theorem B25482799 : Blo 1961435 25482799 := bstep (se 1 (by rfl) ⟨19112099, by rfl⟩ : syracuseStep 25482799 = 38224199) B38224199
theorem B33977065 : Blo 1961435 33977065 := bstep (se 2 (by rfl) ⟨12741399, by rfl⟩ : syracuseStep 33977065 = 25482799) B25482799
theorem B45302753 : Blo 1961435 45302753 := bstep (se 2 (by rfl) ⟨16988532, by rfl⟩ : syracuseStep 45302753 = 33977065) B33977065
theorem B30201835 : Blo 1961435 30201835 := bstep (se 1 (by rfl) ⟨22651376, by rfl⟩ : syracuseStep 30201835 = 45302753) B45302753
theorem B40269113 : Blo 1961435 40269113 := bstep (se 2 (by rfl) ⟨15100917, by rfl⟩ : syracuseStep 40269113 = 30201835) B30201835
theorem B26846075 : Blo 1961435 26846075 := bstep (se 1 (by rfl) ⟨20134556, by rfl⟩ : syracuseStep 26846075 = 40269113) B40269113
theorem B17897383 : Blo 1961435 17897383 := bstep (se 1 (by rfl) ⟨13423037, by rfl⟩ : syracuseStep 17897383 = 26846075) B26846075
theorem B23863177 : Blo 1961435 23863177 := bstep (se 2 (by rfl) ⟨8948691, by rfl⟩ : syracuseStep 23863177 = 17897383) B17897383
theorem B127270277 : Blo 1961435 127270277 := bstep (se 4 (by rfl) ⟨11931588, by rfl⟩ : syracuseStep 127270277 = 23863177) B23863177
theorem B84846851 : Blo 1961435 84846851 := bstep (se 1 (by rfl) ⟨63635138, by rfl⟩ : syracuseStep 84846851 = 127270277) B127270277
theorem B56564567 : Blo 1961435 56564567 := bstep (se 1 (by rfl) ⟨42423425, by rfl⟩ : syracuseStep 56564567 = 84846851) B84846851
theorem B37709711 : Blo 1961435 37709711 := bstep (se 1 (by rfl) ⟨28282283, by rfl⟩ : syracuseStep 37709711 = 56564567) B56564567
theorem B25139807 : Blo 1961435 25139807 := bstep (se 1 (by rfl) ⟨18854855, by rfl⟩ : syracuseStep 25139807 = 37709711) B37709711
theorem B16759871 : Blo 1961435 16759871 := bstep (se 1 (by rfl) ⟨12569903, by rfl⟩ : syracuseStep 16759871 = 25139807) B25139807
theorem B11173247 : Blo 1961435 11173247 := bstep (se 1 (by rfl) ⟨8379935, by rfl⟩ : syracuseStep 11173247 = 16759871) B16759871
theorem B7448831 : Blo 1961435 7448831 := bstep (se 1 (by rfl) ⟨5586623, by rfl⟩ : syracuseStep 7448831 = 11173247) B11173247
theorem B4965887 : Blo 1961435 4965887 := bstep (se 1 (by rfl) ⟨3724415, by rfl⟩ : syracuseStep 4965887 = 7448831) B7448831
theorem B3310591 : Blo 1961435 3310591 := bstep (se 1 (by rfl) ⟨2482943, by rfl⟩ : syracuseStep 3310591 = 4965887) B4965887
theorem B4414121 : Blo 1961435 4414121 := bstep (se 2 (by rfl) ⟨1655295, by rfl⟩ : syracuseStep 4414121 = 3310591) B3310591
theorem B2942747 : Blo 1961435 2942747 := bstep (se 1 (by rfl) ⟨2207060, by rfl⟩ : syracuseStep 2942747 = 4414121) B4414121
theorem B1961831 : Blo 1961435 1961831 := bstep (se 1 (by rfl) ⟨1471373, by rfl⟩ : syracuseStep 1961831 = 2942747) B2942747
theorem B2207065 : Blo 1961435 2207065 := bbase (se 2 (by rfl) ⟨827649, by rfl⟩ : syracuseStep 2207065 = 1655299) (by norm_num)
theorem B2942753 : Blo 1961435 2942753 := bstep (se 2 (by rfl) ⟨1103532, by rfl⟩ : syracuseStep 2942753 = 2207065) B2207065
theorem B1961835 : Blo 1961435 1961835 := bstep (se 1 (by rfl) ⟨1471376, by rfl⟩ : syracuseStep 1961835 = 2942753) B2942753
theorem B3535301 : Blo 1961435 3535301 := bbase (se 4 (by rfl) ⟨331434, by rfl⟩ : syracuseStep 3535301 = 662869) (by norm_num)
theorem B2356867 : Blo 1961435 2356867 := bstep (se 1 (by rfl) ⟨1767650, by rfl⟩ : syracuseStep 2356867 = 3535301) B3535301
theorem B3142489 : Blo 1961435 3142489 := bstep (se 2 (by rfl) ⟨1178433, by rfl⟩ : syracuseStep 3142489 = 2356867) B2356867
theorem B4189985 : Blo 1961435 4189985 := bstep (se 2 (by rfl) ⟨1571244, by rfl⟩ : syracuseStep 4189985 = 3142489) B3142489
theorem B2793323 : Blo 1961435 2793323 := bstep (se 1 (by rfl) ⟨2094992, by rfl⟩ : syracuseStep 2793323 = 4189985) B4189985
theorem B7448861 : Blo 1961435 7448861 := bstep (se 3 (by rfl) ⟨1396661, by rfl⟩ : syracuseStep 7448861 = 2793323) B2793323
theorem B4965907 : Blo 1961435 4965907 := bstep (se 1 (by rfl) ⟨3724430, by rfl⟩ : syracuseStep 4965907 = 7448861) B7448861
theorem B6621209 : Blo 1961435 6621209 := bstep (se 2 (by rfl) ⟨2482953, by rfl⟩ : syracuseStep 6621209 = 4965907) B4965907
theorem B4414139 : Blo 1961435 4414139 := bstep (se 1 (by rfl) ⟨3310604, by rfl⟩ : syracuseStep 4414139 = 6621209) B6621209
theorem B2942759 : Blo 1961435 2942759 := bstep (se 1 (by rfl) ⟨2207069, by rfl⟩ : syracuseStep 2942759 = 4414139) B4414139
theorem B1961839 : Blo 1961435 1961839 := bstep (se 1 (by rfl) ⟨1471379, by rfl⟩ : syracuseStep 1961839 = 2942759) B2942759
theorem B2942765 : Blo 1961435 2942765 := bbase (se 3 (by rfl) ⟨551768, by rfl⟩ : syracuseStep 2942765 = 1103537) (by norm_num)
theorem B1961843 : Blo 1961435 1961843 := bstep (se 1 (by rfl) ⟨1471382, by rfl⟩ : syracuseStep 1961843 = 2942765) B2942765
theorem B4414157 : Blo 1961435 4414157 := bbase (se 3 (by rfl) ⟨827654, by rfl⟩ : syracuseStep 4414157 = 1655309) (by norm_num)
theorem B2942771 : Blo 1961435 2942771 := bstep (se 1 (by rfl) ⟨2207078, by rfl⟩ : syracuseStep 2942771 = 4414157) B4414157
theorem B1961847 : Blo 1961435 1961847 := bstep (se 1 (by rfl) ⟨1471385, by rfl⟩ : syracuseStep 1961847 = 2942771) B2942771
theorem B2482969 : Blo 1961435 2482969 := bbase (se 2 (by rfl) ⟨931113, by rfl⟩ : syracuseStep 2482969 = 1862227) (by norm_num)
theorem B3310625 : Blo 1961435 3310625 := bstep (se 2 (by rfl) ⟨1241484, by rfl⟩ : syracuseStep 3310625 = 2482969) B2482969
theorem B2207083 : Blo 1961435 2207083 := bstep (se 1 (by rfl) ⟨1655312, by rfl⟩ : syracuseStep 2207083 = 3310625) B3310625
theorem B2942777 : Blo 1961435 2942777 := bstep (se 2 (by rfl) ⟨1103541, by rfl⟩ : syracuseStep 2942777 = 2207083) B2207083
theorem B1961851 : Blo 1961435 1961851 := bstep (se 1 (by rfl) ⟨1471388, by rfl⟩ : syracuseStep 1961851 = 2942777) B2942777
theorem B8380037 : Blo 1961435 8380037 := bbase (se 4 (by rfl) ⟨785628, by rfl⟩ : syracuseStep 8380037 = 1571257) (by norm_num)
theorem B22346765 : Blo 1961435 22346765 := bstep (se 3 (by rfl) ⟨4190018, by rfl⟩ : syracuseStep 22346765 = 8380037) B8380037
theorem B14897843 : Blo 1961435 14897843 := bstep (se 1 (by rfl) ⟨11173382, by rfl⟩ : syracuseStep 14897843 = 22346765) B22346765
theorem B9931895 : Blo 1961435 9931895 := bstep (se 1 (by rfl) ⟨7448921, by rfl⟩ : syracuseStep 9931895 = 14897843) B14897843
theorem B6621263 : Blo 1961435 6621263 := bstep (se 1 (by rfl) ⟨4965947, by rfl⟩ : syracuseStep 6621263 = 9931895) B9931895
theorem B4414175 : Blo 1961435 4414175 := bstep (se 1 (by rfl) ⟨3310631, by rfl⟩ : syracuseStep 4414175 = 6621263) B6621263
theorem B2942783 : Blo 1961435 2942783 := bstep (se 1 (by rfl) ⟨2207087, by rfl⟩ : syracuseStep 2942783 = 4414175) B4414175
theorem B1961855 : Blo 1961435 1961855 := bstep (se 1 (by rfl) ⟨1471391, by rfl⟩ : syracuseStep 1961855 = 2942783) B2942783
theorem B2942789 : Blo 1961435 2942789 := bbase (se 4 (by rfl) ⟨275886, by rfl⟩ : syracuseStep 2942789 = 551773) (by norm_num)
theorem B1961859 : Blo 1961435 1961859 := bstep (se 1 (by rfl) ⟨1471394, by rfl⟩ : syracuseStep 1961859 = 2942789) B2942789
theorem B3310645 : Blo 1961435 3310645 := bbase (se 5 (by rfl) ⟨155186, by rfl⟩ : syracuseStep 3310645 = 310373) (by norm_num)
theorem B4414193 : Blo 1961435 4414193 := bstep (se 2 (by rfl) ⟨1655322, by rfl⟩ : syracuseStep 4414193 = 3310645) B3310645
theorem B2942795 : Blo 1961435 2942795 := bstep (se 1 (by rfl) ⟨2207096, by rfl⟩ : syracuseStep 2942795 = 4414193) B4414193
theorem B1961863 : Blo 1961435 1961863 := bstep (se 1 (by rfl) ⟨1471397, by rfl⟩ : syracuseStep 1961863 = 2942795) B2942795
theorem B2207101 : Blo 1961435 2207101 := bbase (se 3 (by rfl) ⟨413831, by rfl⟩ : syracuseStep 2207101 = 827663) (by norm_num)
theorem B2942801 : Blo 1961435 2942801 := bstep (se 2 (by rfl) ⟨1103550, by rfl⟩ : syracuseStep 2942801 = 2207101) B2207101
theorem B1961867 : Blo 1961435 1961867 := bstep (se 1 (by rfl) ⟨1471400, by rfl⟩ : syracuseStep 1961867 = 2942801) B2942801
theorem B6621317 : Blo 1961435 6621317 := bbase (se 4 (by rfl) ⟨620748, by rfl⟩ : syracuseStep 6621317 = 1241497) (by norm_num)
theorem B4414211 : Blo 1961435 4414211 := bstep (se 1 (by rfl) ⟨3310658, by rfl⟩ : syracuseStep 4414211 = 6621317) B6621317
theorem B2942807 : Blo 1961435 2942807 := bstep (se 1 (by rfl) ⟨2207105, by rfl⟩ : syracuseStep 2942807 = 4414211) B4414211
theorem B1961871 : Blo 1961435 1961871 := bstep (se 1 (by rfl) ⟨1471403, by rfl⟩ : syracuseStep 1961871 = 2942807) B2942807
theorem B2942813 : Blo 1961435 2942813 := bbase (se 3 (by rfl) ⟨551777, by rfl⟩ : syracuseStep 2942813 = 1103555) (by norm_num)
theorem B1961875 : Blo 1961435 1961875 := bstep (se 1 (by rfl) ⟨1471406, by rfl⟩ : syracuseStep 1961875 = 2942813) B2942813
theorem B4414229 : Blo 1961435 4414229 := bbase (se 6 (by rfl) ⟨103458, by rfl⟩ : syracuseStep 4414229 = 206917) (by norm_num)
theorem B2942819 : Blo 1961435 2942819 := bstep (se 1 (by rfl) ⟨2207114, by rfl⟩ : syracuseStep 2942819 = 4414229) B4414229
theorem B1961879 : Blo 1961435 1961879 := bstep (se 1 (by rfl) ⟨1471409, by rfl⟩ : syracuseStep 1961879 = 2942819) B2942819
theorem B7449029 : Blo 1961435 7449029 := bbase (se 4 (by rfl) ⟨698346, by rfl⟩ : syracuseStep 7449029 = 1396693) (by norm_num)
theorem B4966019 : Blo 1961435 4966019 := bstep (se 1 (by rfl) ⟨3724514, by rfl⟩ : syracuseStep 4966019 = 7449029) B7449029
theorem B3310679 : Blo 1961435 3310679 := bstep (se 1 (by rfl) ⟨2483009, by rfl⟩ : syracuseStep 3310679 = 4966019) B4966019
theorem B2207119 : Blo 1961435 2207119 := bstep (se 1 (by rfl) ⟨1655339, by rfl⟩ : syracuseStep 2207119 = 3310679) B3310679
theorem B2942825 : Blo 1961435 2942825 := bstep (se 2 (by rfl) ⟨1103559, by rfl⟩ : syracuseStep 2942825 = 2207119) B2207119
theorem B1961883 : Blo 1961435 1961883 := bstep (se 1 (by rfl) ⟨1471412, by rfl⟩ : syracuseStep 1961883 = 2942825) B2942825
theorem B7070773 : Blo 1961435 7070773 := bbase (se 5 (by rfl) ⟨331442, by rfl⟩ : syracuseStep 7070773 = 662885) (by norm_num)
theorem B9427697 : Blo 1961435 9427697 := bstep (se 2 (by rfl) ⟨3535386, by rfl⟩ : syracuseStep 9427697 = 7070773) B7070773
theorem B6285131 : Blo 1961435 6285131 := bstep (se 1 (by rfl) ⟨4713848, by rfl⟩ : syracuseStep 6285131 = 9427697) B9427697
theorem B4190087 : Blo 1961435 4190087 := bstep (se 1 (by rfl) ⟨3142565, by rfl⟩ : syracuseStep 4190087 = 6285131) B6285131
theorem B11173565 : Blo 1961435 11173565 := bstep (se 3 (by rfl) ⟨2095043, by rfl⟩ : syracuseStep 11173565 = 4190087) B4190087
theorem B7449043 : Blo 1961435 7449043 := bstep (se 1 (by rfl) ⟨5586782, by rfl⟩ : syracuseStep 7449043 = 11173565) B11173565
theorem B9932057 : Blo 1961435 9932057 := bstep (se 2 (by rfl) ⟨3724521, by rfl⟩ : syracuseStep 9932057 = 7449043) B7449043
theorem B6621371 : Blo 1961435 6621371 := bstep (se 1 (by rfl) ⟨4966028, by rfl⟩ : syracuseStep 6621371 = 9932057) B9932057
theorem B4414247 : Blo 1961435 4414247 := bstep (se 1 (by rfl) ⟨3310685, by rfl⟩ : syracuseStep 4414247 = 6621371) B6621371
theorem B2942831 : Blo 1961435 2942831 := bstep (se 1 (by rfl) ⟨2207123, by rfl⟩ : syracuseStep 2942831 = 4414247) B4414247
theorem B1961887 : Blo 1961435 1961887 := bstep (se 1 (by rfl) ⟨1471415, by rfl⟩ : syracuseStep 1961887 = 2942831) B2942831
theorem B2942837 : Blo 1961435 2942837 := bbase (se 5 (by rfl) ⟨137945, by rfl⟩ : syracuseStep 2942837 = 275891) (by norm_num)
theorem B1961891 : Blo 1961435 1961891 := bstep (se 1 (by rfl) ⟨1471418, by rfl⟩ : syracuseStep 1961891 = 2942837) B2942837
theorem B4713869 : Blo 1961435 4713869 := bbase (se 3 (by rfl) ⟨883850, by rfl⟩ : syracuseStep 4713869 = 1767701) (by norm_num)
theorem B3142579 : Blo 1961435 3142579 := bstep (se 1 (by rfl) ⟨2356934, by rfl⟩ : syracuseStep 3142579 = 4713869) B4713869
theorem B4190105 : Blo 1961435 4190105 := bstep (se 2 (by rfl) ⟨1571289, by rfl⟩ : syracuseStep 4190105 = 3142579) B3142579
theorem B2793403 : Blo 1961435 2793403 := bstep (se 1 (by rfl) ⟨2095052, by rfl⟩ : syracuseStep 2793403 = 4190105) B4190105
theorem B3724537 : Blo 1961435 3724537 := bstep (se 2 (by rfl) ⟨1396701, by rfl⟩ : syracuseStep 3724537 = 2793403) B2793403
theorem B4966049 : Blo 1961435 4966049 := bstep (se 2 (by rfl) ⟨1862268, by rfl⟩ : syracuseStep 4966049 = 3724537) B3724537
theorem B3310699 : Blo 1961435 3310699 := bstep (se 1 (by rfl) ⟨2483024, by rfl⟩ : syracuseStep 3310699 = 4966049) B4966049
theorem B4414265 : Blo 1961435 4414265 := bstep (se 2 (by rfl) ⟨1655349, by rfl⟩ : syracuseStep 4414265 = 3310699) B3310699
theorem B2942843 : Blo 1961435 2942843 := bstep (se 1 (by rfl) ⟨2207132, by rfl⟩ : syracuseStep 2942843 = 4414265) B4414265
theorem B1961895 : Blo 1961435 1961895 := bstep (se 1 (by rfl) ⟨1471421, by rfl⟩ : syracuseStep 1961895 = 2942843) B2942843
theorem B2207137 : Blo 1961435 2207137 := bbase (se 2 (by rfl) ⟨827676, by rfl⟩ : syracuseStep 2207137 = 1655353) (by norm_num)
theorem B2942849 : Blo 1961435 2942849 := bstep (se 2 (by rfl) ⟨1103568, by rfl⟩ : syracuseStep 2942849 = 2207137) B2207137
theorem B1961899 : Blo 1961435 1961899 := bstep (se 1 (by rfl) ⟨1471424, by rfl⟩ : syracuseStep 1961899 = 2942849) B2942849
theorem B4966069 : Blo 1961435 4966069 := bbase (se 5 (by rfl) ⟨232784, by rfl⟩ : syracuseStep 4966069 = 465569) (by norm_num)
theorem B6621425 : Blo 1961435 6621425 := bstep (se 2 (by rfl) ⟨2483034, by rfl⟩ : syracuseStep 6621425 = 4966069) B4966069
theorem B4414283 : Blo 1961435 4414283 := bstep (se 1 (by rfl) ⟨3310712, by rfl⟩ : syracuseStep 4414283 = 6621425) B6621425
theorem B2942855 : Blo 1961435 2942855 := bstep (se 1 (by rfl) ⟨2207141, by rfl⟩ : syracuseStep 2942855 = 4414283) B4414283
theorem B1961903 : Blo 1961435 1961903 := bstep (se 1 (by rfl) ⟨1471427, by rfl⟩ : syracuseStep 1961903 = 2942855) B2942855
theorem B2942861 : Blo 1961435 2942861 := bbase (se 3 (by rfl) ⟨551786, by rfl⟩ : syracuseStep 2942861 = 1103573) (by norm_num)
theorem B1961907 : Blo 1961435 1961907 := bstep (se 1 (by rfl) ⟨1471430, by rfl⟩ : syracuseStep 1961907 = 2942861) B2942861
theorem B4414301 : Blo 1961435 4414301 := bbase (se 3 (by rfl) ⟨827681, by rfl⟩ : syracuseStep 4414301 = 1655363) (by norm_num)
theorem B2942867 : Blo 1961435 2942867 := bstep (se 1 (by rfl) ⟨2207150, by rfl⟩ : syracuseStep 2942867 = 4414301) B4414301
theorem B1961911 : Blo 1961435 1961911 := bstep (se 1 (by rfl) ⟨1471433, by rfl⟩ : syracuseStep 1961911 = 2942867) B2942867
theorem B3310733 : Blo 1961435 3310733 := bbase (se 3 (by rfl) ⟨620762, by rfl⟩ : syracuseStep 3310733 = 1241525) (by norm_num)
theorem B2207155 : Blo 1961435 2207155 := bstep (se 1 (by rfl) ⟨1655366, by rfl⟩ : syracuseStep 2207155 = 3310733) B3310733
theorem B2942873 : Blo 1961435 2942873 := bstep (se 2 (by rfl) ⟨1103577, by rfl⟩ : syracuseStep 2942873 = 2207155) B2207155
theorem B1961915 : Blo 1961435 1961915 := bstep (se 1 (by rfl) ⟨1471436, by rfl⟩ : syracuseStep 1961915 = 2942873) B2942873
theorem B4713925 : Blo 1961435 4713925 := bbase (se 4 (by rfl) ⟨441930, by rfl⟩ : syracuseStep 4713925 = 883861) (by norm_num)
theorem B6285233 : Blo 1961435 6285233 := bstep (se 2 (by rfl) ⟨2356962, by rfl⟩ : syracuseStep 6285233 = 4713925) B4713925
theorem B16760621 : Blo 1961435 16760621 := bstep (se 3 (by rfl) ⟨3142616, by rfl⟩ : syracuseStep 16760621 = 6285233) B6285233
theorem B11173747 : Blo 1961435 11173747 := bstep (se 1 (by rfl) ⟨8380310, by rfl⟩ : syracuseStep 11173747 = 16760621) B16760621
theorem B14898329 : Blo 1961435 14898329 := bstep (se 2 (by rfl) ⟨5586873, by rfl⟩ : syracuseStep 14898329 = 11173747) B11173747
theorem B9932219 : Blo 1961435 9932219 := bstep (se 1 (by rfl) ⟨7449164, by rfl⟩ : syracuseStep 9932219 = 14898329) B14898329
theorem B6621479 : Blo 1961435 6621479 := bstep (se 1 (by rfl) ⟨4966109, by rfl⟩ : syracuseStep 6621479 = 9932219) B9932219
theorem B4414319 : Blo 1961435 4414319 := bstep (se 1 (by rfl) ⟨3310739, by rfl⟩ : syracuseStep 4414319 = 6621479) B6621479
theorem B2942879 : Blo 1961435 2942879 := bstep (se 1 (by rfl) ⟨2207159, by rfl⟩ : syracuseStep 2942879 = 4414319) B4414319
theorem B1961919 : Blo 1961435 1961919 := bstep (se 1 (by rfl) ⟨1471439, by rfl⟩ : syracuseStep 1961919 = 2942879) B2942879
theorem B2942885 : Blo 1961435 2942885 := bbase (se 4 (by rfl) ⟨275895, by rfl⟩ : syracuseStep 2942885 = 551791) (by norm_num)
theorem B1961923 : Blo 1961435 1961923 := bstep (se 1 (by rfl) ⟨1471442, by rfl⟩ : syracuseStep 1961923 = 2942885) B2942885
theorem B2483065 : Blo 1961435 2483065 := bbase (se 2 (by rfl) ⟨931149, by rfl⟩ : syracuseStep 2483065 = 1862299) (by norm_num)
theorem B3310753 : Blo 1961435 3310753 := bstep (se 2 (by rfl) ⟨1241532, by rfl⟩ : syracuseStep 3310753 = 2483065) B2483065
theorem B4414337 : Blo 1961435 4414337 := bstep (se 2 (by rfl) ⟨1655376, by rfl⟩ : syracuseStep 4414337 = 3310753) B3310753
theorem B2942891 : Blo 1961435 2942891 := bstep (se 1 (by rfl) ⟨2207168, by rfl⟩ : syracuseStep 2942891 = 4414337) B4414337
theorem B1961927 : Blo 1961435 1961927 := bstep (se 1 (by rfl) ⟨1471445, by rfl⟩ : syracuseStep 1961927 = 2942891) B2942891
theorem B2207173 : Blo 1961435 2207173 := bbase (se 4 (by rfl) ⟨206922, by rfl⟩ : syracuseStep 2207173 = 413845) (by norm_num)
theorem B2942897 : Blo 1961435 2942897 := bstep (se 2 (by rfl) ⟨1103586, by rfl⟩ : syracuseStep 2942897 = 2207173) B2207173
theorem B1961931 : Blo 1961435 1961931 := bstep (se 1 (by rfl) ⟨1471448, by rfl⟩ : syracuseStep 1961931 = 2942897) B2942897
theorem B3724613 : Blo 1961435 3724613 := bbase (se 4 (by rfl) ⟨349182, by rfl⟩ : syracuseStep 3724613 = 698365) (by norm_num)
theorem B2483075 : Blo 1961435 2483075 := bstep (se 1 (by rfl) ⟨1862306, by rfl⟩ : syracuseStep 2483075 = 3724613) B3724613
theorem B6621533 : Blo 1961435 6621533 := bstep (se 3 (by rfl) ⟨1241537, by rfl⟩ : syracuseStep 6621533 = 2483075) B2483075
theorem B4414355 : Blo 1961435 4414355 := bstep (se 1 (by rfl) ⟨3310766, by rfl⟩ : syracuseStep 4414355 = 6621533) B6621533
theorem B2942903 : Blo 1961435 2942903 := bstep (se 1 (by rfl) ⟨2207177, by rfl⟩ : syracuseStep 2942903 = 4414355) B4414355
theorem B1961935 : Blo 1961435 1961935 := bstep (se 1 (by rfl) ⟨1471451, by rfl⟩ : syracuseStep 1961935 = 2942903) B2942903
theorem B2942909 : Blo 1961435 2942909 := bbase (se 3 (by rfl) ⟨551795, by rfl⟩ : syracuseStep 2942909 = 1103591) (by norm_num)
theorem B1961939 : Blo 1961435 1961939 := bstep (se 1 (by rfl) ⟨1471454, by rfl⟩ : syracuseStep 1961939 = 2942909) B2942909
theorem B4414373 : Blo 1961435 4414373 := bbase (se 4 (by rfl) ⟨413847, by rfl⟩ : syracuseStep 4414373 = 827695) (by norm_num)
theorem B2942915 : Blo 1961435 2942915 := bstep (se 1 (by rfl) ⟨2207186, by rfl⟩ : syracuseStep 2942915 = 4414373) B4414373
theorem B1961943 : Blo 1961435 1961943 := bstep (se 1 (by rfl) ⟨1471457, by rfl⟩ : syracuseStep 1961943 = 2942915) B2942915
theorem B4966181 : Blo 1961435 4966181 := bbase (se 4 (by rfl) ⟨465579, by rfl⟩ : syracuseStep 4966181 = 931159) (by norm_num)
theorem B3310787 : Blo 1961435 3310787 := bstep (se 1 (by rfl) ⟨2483090, by rfl⟩ : syracuseStep 3310787 = 4966181) B4966181
theorem B2207191 : Blo 1961435 2207191 := bstep (se 1 (by rfl) ⟨1655393, by rfl⟩ : syracuseStep 2207191 = 3310787) B3310787
theorem B2942921 : Blo 1961435 2942921 := bstep (se 2 (by rfl) ⟨1103595, by rfl⟩ : syracuseStep 2942921 = 2207191) B2207191
theorem B1961947 : Blo 1961435 1961947 := bstep (se 1 (by rfl) ⟨1471460, by rfl⟩ : syracuseStep 1961947 = 2942921) B2942921
theorem B5586965 : Blo 1961435 5586965 := bbase (se 6 (by rfl) ⟨130944, by rfl⟩ : syracuseStep 5586965 = 261889) (by norm_num)
theorem B3724643 : Blo 1961435 3724643 := bstep (se 1 (by rfl) ⟨2793482, by rfl⟩ : syracuseStep 3724643 = 5586965) B5586965
theorem B9932381 : Blo 1961435 9932381 := bstep (se 3 (by rfl) ⟨1862321, by rfl⟩ : syracuseStep 9932381 = 3724643) B3724643
theorem B6621587 : Blo 1961435 6621587 := bstep (se 1 (by rfl) ⟨4966190, by rfl⟩ : syracuseStep 6621587 = 9932381) B9932381
theorem B4414391 : Blo 1961435 4414391 := bstep (se 1 (by rfl) ⟨3310793, by rfl⟩ : syracuseStep 4414391 = 6621587) B6621587
theorem B2942927 : Blo 1961435 2942927 := bstep (se 1 (by rfl) ⟨2207195, by rfl⟩ : syracuseStep 2942927 = 4414391) B4414391
theorem B1961951 : Blo 1961435 1961951 := bstep (se 1 (by rfl) ⟨1471463, by rfl⟩ : syracuseStep 1961951 = 2942927) B2942927
theorem B2942933 : Blo 1961435 2942933 := bbase (se 7 (by rfl) ⟨34487, by rfl⟩ : syracuseStep 2942933 = 68975) (by norm_num)
theorem B1961955 : Blo 1961435 1961955 := bstep (se 1 (by rfl) ⟨1471466, by rfl⟩ : syracuseStep 1961955 = 2942933) B2942933
theorem B7449317 : Blo 1961435 7449317 := bbase (se 4 (by rfl) ⟨698373, by rfl⟩ : syracuseStep 7449317 = 1396747) (by norm_num)
theorem B4966211 : Blo 1961435 4966211 := bstep (se 1 (by rfl) ⟨3724658, by rfl⟩ : syracuseStep 4966211 = 7449317) B7449317
theorem B3310807 : Blo 1961435 3310807 := bstep (se 1 (by rfl) ⟨2483105, by rfl⟩ : syracuseStep 3310807 = 4966211) B4966211
theorem B4414409 : Blo 1961435 4414409 := bstep (se 2 (by rfl) ⟨1655403, by rfl⟩ : syracuseStep 4414409 = 3310807) B3310807
theorem B2942939 : Blo 1961435 2942939 := bstep (se 1 (by rfl) ⟨2207204, by rfl⟩ : syracuseStep 2942939 = 4414409) B4414409
theorem B1961959 : Blo 1961435 1961959 := bstep (se 1 (by rfl) ⟨1471469, by rfl⟩ : syracuseStep 1961959 = 2942939) B2942939
theorem B2207209 : Blo 1961435 2207209 := bbase (se 2 (by rfl) ⟨827703, by rfl⟩ : syracuseStep 2207209 = 1655407) (by norm_num)
theorem B2942945 : Blo 1961435 2942945 := bstep (se 2 (by rfl) ⟨1103604, by rfl⟩ : syracuseStep 2942945 = 2207209) B2207209
theorem B1961963 : Blo 1961435 1961963 := bstep (se 1 (by rfl) ⟨1471472, by rfl⟩ : syracuseStep 1961963 = 2942945) B2942945
theorem B2095129 : Blo 1961435 2095129 := bbase (se 2 (by rfl) ⟨785673, by rfl⟩ : syracuseStep 2095129 = 1571347) (by norm_num)
theorem B11174021 : Blo 1961435 11174021 := bstep (se 4 (by rfl) ⟨1047564, by rfl⟩ : syracuseStep 11174021 = 2095129) B2095129
theorem B7449347 : Blo 1961435 7449347 := bstep (se 1 (by rfl) ⟨5587010, by rfl⟩ : syracuseStep 7449347 = 11174021) B11174021
theorem B4966231 : Blo 1961435 4966231 := bstep (se 1 (by rfl) ⟨3724673, by rfl⟩ : syracuseStep 4966231 = 7449347) B7449347
theorem B6621641 : Blo 1961435 6621641 := bstep (se 2 (by rfl) ⟨2483115, by rfl⟩ : syracuseStep 6621641 = 4966231) B4966231
theorem B4414427 : Blo 1961435 4414427 := bstep (se 1 (by rfl) ⟨3310820, by rfl⟩ : syracuseStep 4414427 = 6621641) B6621641
theorem B2942951 : Blo 1961435 2942951 := bstep (se 1 (by rfl) ⟨2207213, by rfl⟩ : syracuseStep 2942951 = 4414427) B4414427
theorem B1961967 : Blo 1961435 1961967 := bstep (se 1 (by rfl) ⟨1471475, by rfl⟩ : syracuseStep 1961967 = 2942951) B2942951
theorem B2942957 : Blo 1961435 2942957 := bbase (se 3 (by rfl) ⟨551804, by rfl⟩ : syracuseStep 2942957 = 1103609) (by norm_num)
theorem B1961971 : Blo 1961435 1961971 := bstep (se 1 (by rfl) ⟨1471478, by rfl⟩ : syracuseStep 1961971 = 2942957) B2942957
theorem B4414445 : Blo 1961435 4414445 := bbase (se 3 (by rfl) ⟨827708, by rfl⟩ : syracuseStep 4414445 = 1655417) (by norm_num)
theorem B2942963 : Blo 1961435 2942963 := bstep (se 1 (by rfl) ⟨2207222, by rfl⟩ : syracuseStep 2942963 = 4414445) B4414445
theorem B1961975 : Blo 1961435 1961975 := bstep (se 1 (by rfl) ⟨1471481, by rfl⟩ : syracuseStep 1961975 = 2942963) B2942963
theorem B4190285 : Blo 1961435 4190285 := bbase (se 3 (by rfl) ⟨785678, by rfl⟩ : syracuseStep 4190285 = 1571357) (by norm_num)
theorem B2793523 : Blo 1961435 2793523 := bstep (se 1 (by rfl) ⟨2095142, by rfl⟩ : syracuseStep 2793523 = 4190285) B4190285
theorem B3724697 : Blo 1961435 3724697 := bstep (se 2 (by rfl) ⟨1396761, by rfl⟩ : syracuseStep 3724697 = 2793523) B2793523
theorem B2483131 : Blo 1961435 2483131 := bstep (se 1 (by rfl) ⟨1862348, by rfl⟩ : syracuseStep 2483131 = 3724697) B3724697
theorem B3310841 : Blo 1961435 3310841 := bstep (se 2 (by rfl) ⟨1241565, by rfl⟩ : syracuseStep 3310841 = 2483131) B2483131
theorem B2207227 : Blo 1961435 2207227 := bstep (se 1 (by rfl) ⟨1655420, by rfl⟩ : syracuseStep 2207227 = 3310841) B3310841
theorem B2942969 : Blo 1961435 2942969 := bstep (se 2 (by rfl) ⟨1103613, by rfl⟩ : syracuseStep 2942969 = 2207227) B2207227
theorem B1961979 : Blo 1961435 1961979 := bstep (se 1 (by rfl) ⟨1471484, by rfl⟩ : syracuseStep 1961979 = 2942969) B2942969
theorem B2043389 : Blo 1961435 2043389 := bbase (se 3 (by rfl) ⟨383135, by rfl⟩ : syracuseStep 2043389 = 766271) (by norm_num)
theorem B5449037 : Blo 1961435 5449037 := bstep (se 3 (by rfl) ⟨1021694, by rfl⟩ : syracuseStep 5449037 = 2043389) B2043389
theorem B14530765 : Blo 1961435 14530765 := bstep (se 3 (by rfl) ⟨2724518, by rfl⟩ : syracuseStep 14530765 = 5449037) B5449037
theorem B19374353 : Blo 1961435 19374353 := bstep (se 2 (by rfl) ⟨7265382, by rfl⟩ : syracuseStep 19374353 = 14530765) B14530765
theorem B12916235 : Blo 1961435 12916235 := bstep (se 1 (by rfl) ⟨9687176, by rfl⟩ : syracuseStep 12916235 = 19374353) B19374353
theorem B8610823 : Blo 1961435 8610823 := bstep (se 1 (by rfl) ⟨6458117, by rfl⟩ : syracuseStep 8610823 = 12916235) B12916235
theorem B11481097 : Blo 1961435 11481097 := bstep (se 2 (by rfl) ⟨4305411, by rfl⟩ : syracuseStep 11481097 = 8610823) B8610823
theorem B15308129 : Blo 1961435 15308129 := bstep (se 2 (by rfl) ⟨5740548, by rfl⟩ : syracuseStep 15308129 = 11481097) B11481097
theorem B40821677 : Blo 1961435 40821677 := bstep (se 3 (by rfl) ⟨7654064, by rfl⟩ : syracuseStep 40821677 = 15308129) B15308129
theorem B27214451 : Blo 1961435 27214451 := bstep (se 1 (by rfl) ⟨20410838, by rfl⟩ : syracuseStep 27214451 = 40821677) B40821677
theorem B18142967 : Blo 1961435 18142967 := bstep (se 1 (by rfl) ⟨13607225, by rfl⟩ : syracuseStep 18142967 = 27214451) B27214451
theorem B12095311 : Blo 1961435 12095311 := bstep (se 1 (by rfl) ⟨9071483, by rfl⟩ : syracuseStep 12095311 = 18142967) B18142967
theorem B16127081 : Blo 1961435 16127081 := bstep (se 2 (by rfl) ⟨6047655, by rfl⟩ : syracuseStep 16127081 = 12095311) B12095311
theorem B10751387 : Blo 1961435 10751387 := bstep (se 1 (by rfl) ⟨8063540, by rfl⟩ : syracuseStep 10751387 = 16127081) B16127081
theorem B28670365 : Blo 1961435 28670365 := bstep (se 3 (by rfl) ⟨5375693, by rfl⟩ : syracuseStep 28670365 = 10751387) B10751387
theorem B38227153 : Blo 1961435 38227153 := bstep (se 2 (by rfl) ⟨14335182, by rfl⟩ : syracuseStep 38227153 = 28670365) B28670365
theorem B50969537 : Blo 1961435 50969537 := bstep (se 2 (by rfl) ⟨19113576, by rfl⟩ : syracuseStep 50969537 = 38227153) B38227153
theorem B33979691 : Blo 1961435 33979691 := bstep (se 1 (by rfl) ⟨25484768, by rfl⟩ : syracuseStep 33979691 = 50969537) B50969537
theorem B22653127 : Blo 1961435 22653127 := bstep (se 1 (by rfl) ⟨16989845, by rfl⟩ : syracuseStep 22653127 = 33979691) B33979691
theorem B120816677 : Blo 1961435 120816677 := bstep (se 4 (by rfl) ⟨11326563, by rfl⟩ : syracuseStep 120816677 = 22653127) B22653127
theorem B80544451 : Blo 1961435 80544451 := bstep (se 1 (by rfl) ⟨60408338, by rfl⟩ : syracuseStep 80544451 = 120816677) B120816677
theorem B107392601 : Blo 1961435 107392601 := bstep (se 2 (by rfl) ⟨40272225, by rfl⟩ : syracuseStep 107392601 = 80544451) B80544451
theorem B286380269 : Blo 1961435 286380269 := bstep (se 3 (by rfl) ⟨53696300, by rfl⟩ : syracuseStep 286380269 = 107392601) B107392601
theorem B190920179 : Blo 1961435 190920179 := bstep (se 1 (by rfl) ⟨143190134, by rfl⟩ : syracuseStep 190920179 = 286380269) B286380269
theorem B127280119 : Blo 1961435 127280119 := bstep (se 1 (by rfl) ⟨95460089, by rfl⟩ : syracuseStep 127280119 = 190920179) B190920179
theorem B169706825 : Blo 1961435 169706825 := bstep (se 2 (by rfl) ⟨63640059, by rfl⟩ : syracuseStep 169706825 = 127280119) B127280119
theorem B113137883 : Blo 1961435 113137883 := bstep (se 1 (by rfl) ⟨84853412, by rfl⟩ : syracuseStep 113137883 = 169706825) B169706825
theorem B75425255 : Blo 1961435 75425255 := bstep (se 1 (by rfl) ⟨56568941, by rfl⟩ : syracuseStep 75425255 = 113137883) B113137883
theorem B50283503 : Blo 1961435 50283503 := bstep (se 1 (by rfl) ⟨37712627, by rfl⟩ : syracuseStep 50283503 = 75425255) B75425255
theorem B33522335 : Blo 1961435 33522335 := bstep (se 1 (by rfl) ⟨25141751, by rfl⟩ : syracuseStep 33522335 = 50283503) B50283503
theorem B22348223 : Blo 1961435 22348223 := bstep (se 1 (by rfl) ⟨16761167, by rfl⟩ : syracuseStep 22348223 = 33522335) B33522335
theorem B14898815 : Blo 1961435 14898815 := bstep (se 1 (by rfl) ⟨11174111, by rfl⟩ : syracuseStep 14898815 = 22348223) B22348223
theorem B9932543 : Blo 1961435 9932543 := bstep (se 1 (by rfl) ⟨7449407, by rfl⟩ : syracuseStep 9932543 = 14898815) B14898815
theorem B6621695 : Blo 1961435 6621695 := bstep (se 1 (by rfl) ⟨4966271, by rfl⟩ : syracuseStep 6621695 = 9932543) B9932543
theorem B4414463 : Blo 1961435 4414463 := bstep (se 1 (by rfl) ⟨3310847, by rfl⟩ : syracuseStep 4414463 = 6621695) B6621695
theorem B2942975 : Blo 1961435 2942975 := bstep (se 1 (by rfl) ⟨2207231, by rfl⟩ : syracuseStep 2942975 = 4414463) B4414463
theorem B1961983 : Blo 1961435 1961983 := bstep (se 1 (by rfl) ⟨1471487, by rfl⟩ : syracuseStep 1961983 = 2942975) B2942975
theorem B2942981 : Blo 1961435 2942981 := bbase (se 4 (by rfl) ⟨275904, by rfl⟩ : syracuseStep 2942981 = 551809) (by norm_num)
theorem B1961987 : Blo 1961435 1961987 := bstep (se 1 (by rfl) ⟨1471490, by rfl⟩ : syracuseStep 1961987 = 2942981) B2942981
theorem B3310861 : Blo 1961435 3310861 := bbase (se 3 (by rfl) ⟨620786, by rfl⟩ : syracuseStep 3310861 = 1241573) (by norm_num)
theorem B4414481 : Blo 1961435 4414481 := bstep (se 2 (by rfl) ⟨1655430, by rfl⟩ : syracuseStep 4414481 = 3310861) B3310861
theorem B2942987 : Blo 1961435 2942987 := bstep (se 1 (by rfl) ⟨2207240, by rfl⟩ : syracuseStep 2942987 = 4414481) B4414481
theorem B1961991 : Blo 1961435 1961991 := bstep (se 1 (by rfl) ⟨1471493, by rfl⟩ : syracuseStep 1961991 = 2942987) B2942987
theorem B2207245 : Blo 1961435 2207245 := bbase (se 3 (by rfl) ⟨413858, by rfl⟩ : syracuseStep 2207245 = 827717) (by norm_num)
theorem B2942993 : Blo 1961435 2942993 := bstep (se 2 (by rfl) ⟨1103622, by rfl⟩ : syracuseStep 2942993 = 2207245) B2207245
theorem B1961995 : Blo 1961435 1961995 := bstep (se 1 (by rfl) ⟨1471496, by rfl⟩ : syracuseStep 1961995 = 2942993) B2942993
theorem B6621749 : Blo 1961435 6621749 := bbase (se 5 (by rfl) ⟨310394, by rfl⟩ : syracuseStep 6621749 = 620789) (by norm_num)
theorem B4414499 : Blo 1961435 4414499 := bstep (se 1 (by rfl) ⟨3310874, by rfl⟩ : syracuseStep 4414499 = 6621749) B6621749
theorem B2942999 : Blo 1961435 2942999 := bstep (se 1 (by rfl) ⟨2207249, by rfl⟩ : syracuseStep 2942999 = 4414499) B4414499
theorem B1961999 : Blo 1961435 1961999 := bstep (se 1 (by rfl) ⟨1471499, by rfl⟩ : syracuseStep 1961999 = 2942999) B2942999
theorem B2943005 : Blo 1961435 2943005 := bbase (se 3 (by rfl) ⟨551813, by rfl⟩ : syracuseStep 2943005 = 1103627) (by norm_num)
theorem B1962003 : Blo 1961435 1962003 := bstep (se 1 (by rfl) ⟨1471502, by rfl⟩ : syracuseStep 1962003 = 2943005) B2943005
theorem B4414517 : Blo 1961435 4414517 := bbase (se 5 (by rfl) ⟨206930, by rfl⟩ : syracuseStep 4414517 = 413861) (by norm_num)
theorem B2943011 : Blo 1961435 2943011 := bstep (se 1 (by rfl) ⟨2207258, by rfl⟩ : syracuseStep 2943011 = 4414517) B4414517
theorem B1962007 : Blo 1961435 1962007 := bstep (se 1 (by rfl) ⟨1471505, by rfl⟩ : syracuseStep 1962007 = 2943011) B2943011
theorem B7071221 : Blo 1961435 7071221 := bbase (se 5 (by rfl) ⟨331463, by rfl⟩ : syracuseStep 7071221 = 662927) (by norm_num)
theorem B4714147 : Blo 1961435 4714147 := bstep (se 1 (by rfl) ⟨3535610, by rfl⟩ : syracuseStep 4714147 = 7071221) B7071221
theorem B6285529 : Blo 1961435 6285529 := bstep (se 2 (by rfl) ⟨2357073, by rfl⟩ : syracuseStep 6285529 = 4714147) B4714147
theorem B8380705 : Blo 1961435 8380705 := bstep (se 2 (by rfl) ⟨3142764, by rfl⟩ : syracuseStep 8380705 = 6285529) B6285529
theorem B11174273 : Blo 1961435 11174273 := bstep (se 2 (by rfl) ⟨4190352, by rfl⟩ : syracuseStep 11174273 = 8380705) B8380705
theorem B7449515 : Blo 1961435 7449515 := bstep (se 1 (by rfl) ⟨5587136, by rfl⟩ : syracuseStep 7449515 = 11174273) B11174273
theorem B4966343 : Blo 1961435 4966343 := bstep (se 1 (by rfl) ⟨3724757, by rfl⟩ : syracuseStep 4966343 = 7449515) B7449515
theorem B3310895 : Blo 1961435 3310895 := bstep (se 1 (by rfl) ⟨2483171, by rfl⟩ : syracuseStep 3310895 = 4966343) B4966343
theorem B2207263 : Blo 1961435 2207263 := bstep (se 1 (by rfl) ⟨1655447, by rfl⟩ : syracuseStep 2207263 = 3310895) B3310895
theorem B2943017 : Blo 1961435 2943017 := bstep (se 2 (by rfl) ⟨1103631, by rfl⟩ : syracuseStep 2943017 = 2207263) B2207263
theorem B1962011 : Blo 1961435 1962011 := bstep (se 1 (by rfl) ⟨1471508, by rfl⟩ : syracuseStep 1962011 = 2943017) B2943017
theorem B6285541 : Blo 1961435 6285541 := bbase (se 4 (by rfl) ⟨589269, by rfl⟩ : syracuseStep 6285541 = 1178539) (by norm_num)
theorem B8380721 : Blo 1961435 8380721 := bstep (se 2 (by rfl) ⟨3142770, by rfl⟩ : syracuseStep 8380721 = 6285541) B6285541
theorem B5587147 : Blo 1961435 5587147 := bstep (se 1 (by rfl) ⟨4190360, by rfl⟩ : syracuseStep 5587147 = 8380721) B8380721
theorem B7449529 : Blo 1961435 7449529 := bstep (se 2 (by rfl) ⟨2793573, by rfl⟩ : syracuseStep 7449529 = 5587147) B5587147
theorem B9932705 : Blo 1961435 9932705 := bstep (se 2 (by rfl) ⟨3724764, by rfl⟩ : syracuseStep 9932705 = 7449529) B7449529
theorem B6621803 : Blo 1961435 6621803 := bstep (se 1 (by rfl) ⟨4966352, by rfl⟩ : syracuseStep 6621803 = 9932705) B9932705
theorem B4414535 : Blo 1961435 4414535 := bstep (se 1 (by rfl) ⟨3310901, by rfl⟩ : syracuseStep 4414535 = 6621803) B6621803
theorem B2943023 : Blo 1961435 2943023 := bstep (se 1 (by rfl) ⟨2207267, by rfl⟩ : syracuseStep 2943023 = 4414535) B4414535
theorem B1962015 : Blo 1961435 1962015 := bstep (se 1 (by rfl) ⟨1471511, by rfl⟩ : syracuseStep 1962015 = 2943023) B2943023
theorem B2943029 : Blo 1961435 2943029 := bbase (se 5 (by rfl) ⟨137954, by rfl⟩ : syracuseStep 2943029 = 275909) (by norm_num)
theorem B1962019 : Blo 1961435 1962019 := bstep (se 1 (by rfl) ⟨1471514, by rfl⟩ : syracuseStep 1962019 = 2943029) B2943029
theorem B4966373 : Blo 1961435 4966373 := bbase (se 4 (by rfl) ⟨465597, by rfl⟩ : syracuseStep 4966373 = 931195) (by norm_num)
theorem B3310915 : Blo 1961435 3310915 := bstep (se 1 (by rfl) ⟨2483186, by rfl⟩ : syracuseStep 3310915 = 4966373) B4966373
theorem B4414553 : Blo 1961435 4414553 := bstep (se 2 (by rfl) ⟨1655457, by rfl⟩ : syracuseStep 4414553 = 3310915) B3310915
theorem B2943035 : Blo 1961435 2943035 := bstep (se 1 (by rfl) ⟨2207276, by rfl⟩ : syracuseStep 2943035 = 4414553) B4414553
theorem B1962023 : Blo 1961435 1962023 := bstep (se 1 (by rfl) ⟨1471517, by rfl⟩ : syracuseStep 1962023 = 2943035) B2943035
theorem B2207281 : Blo 1961435 2207281 := bbase (se 2 (by rfl) ⟨827730, by rfl⟩ : syracuseStep 2207281 = 1655461) (by norm_num)
theorem B2943041 : Blo 1961435 2943041 := bstep (se 2 (by rfl) ⟨1103640, by rfl⟩ : syracuseStep 2943041 = 2207281) B2207281
theorem B1962027 : Blo 1961435 1962027 := bstep (se 1 (by rfl) ⟨1471520, by rfl⟩ : syracuseStep 1962027 = 2943041) B2943041
theorem B5966405 : Blo 1961435 5966405 := bbase (se 4 (by rfl) ⟨559350, by rfl⟩ : syracuseStep 5966405 = 1118701) (by norm_num)
theorem B3977603 : Blo 1961435 3977603 := bstep (se 1 (by rfl) ⟨2983202, by rfl⟩ : syracuseStep 3977603 = 5966405) B5966405
theorem B2651735 : Blo 1961435 2651735 := bstep (se 1 (by rfl) ⟨1988801, by rfl⟩ : syracuseStep 2651735 = 3977603) B3977603
theorem B7071293 : Blo 1961435 7071293 := bstep (se 3 (by rfl) ⟨1325867, by rfl⟩ : syracuseStep 7071293 = 2651735) B2651735
theorem B4714195 : Blo 1961435 4714195 := bstep (se 1 (by rfl) ⟨3535646, by rfl⟩ : syracuseStep 4714195 = 7071293) B7071293
theorem B6285593 : Blo 1961435 6285593 := bstep (se 2 (by rfl) ⟨2357097, by rfl⟩ : syracuseStep 6285593 = 4714195) B4714195
theorem B4190395 : Blo 1961435 4190395 := bstep (se 1 (by rfl) ⟨3142796, by rfl⟩ : syracuseStep 4190395 = 6285593) B6285593
theorem B5587193 : Blo 1961435 5587193 := bstep (se 2 (by rfl) ⟨2095197, by rfl⟩ : syracuseStep 5587193 = 4190395) B4190395
theorem B3724795 : Blo 1961435 3724795 := bstep (se 1 (by rfl) ⟨2793596, by rfl⟩ : syracuseStep 3724795 = 5587193) B5587193
theorem B4966393 : Blo 1961435 4966393 := bstep (se 2 (by rfl) ⟨1862397, by rfl⟩ : syracuseStep 4966393 = 3724795) B3724795
theorem B6621857 : Blo 1961435 6621857 := bstep (se 2 (by rfl) ⟨2483196, by rfl⟩ : syracuseStep 6621857 = 4966393) B4966393
theorem B4414571 : Blo 1961435 4414571 := bstep (se 1 (by rfl) ⟨3310928, by rfl⟩ : syracuseStep 4414571 = 6621857) B6621857
theorem B2943047 : Blo 1961435 2943047 := bstep (se 1 (by rfl) ⟨2207285, by rfl⟩ : syracuseStep 2943047 = 4414571) B4414571
theorem B1962031 : Blo 1961435 1962031 := bstep (se 1 (by rfl) ⟨1471523, by rfl⟩ : syracuseStep 1962031 = 2943047) B2943047
theorem B2943053 : Blo 1961435 2943053 := bbase (se 3 (by rfl) ⟨551822, by rfl⟩ : syracuseStep 2943053 = 1103645) (by norm_num)
theorem B1962035 : Blo 1961435 1962035 := bstep (se 1 (by rfl) ⟨1471526, by rfl⟩ : syracuseStep 1962035 = 2943053) B2943053
theorem B4414589 : Blo 1961435 4414589 := bbase (se 3 (by rfl) ⟨827735, by rfl⟩ : syracuseStep 4414589 = 1655471) (by norm_num)
theorem B2943059 : Blo 1961435 2943059 := bstep (se 1 (by rfl) ⟨2207294, by rfl⟩ : syracuseStep 2943059 = 4414589) B4414589
theorem B1962039 : Blo 1961435 1962039 := bstep (se 1 (by rfl) ⟨1471529, by rfl⟩ : syracuseStep 1962039 = 2943059) B2943059
theorem B3310949 : Blo 1961435 3310949 := bbase (se 4 (by rfl) ⟨310401, by rfl⟩ : syracuseStep 3310949 = 620803) (by norm_num)
theorem B2207299 : Blo 1961435 2207299 := bstep (se 1 (by rfl) ⟨1655474, by rfl⟩ : syracuseStep 2207299 = 3310949) B3310949
theorem B2943065 : Blo 1961435 2943065 := bstep (se 2 (by rfl) ⟨1103649, by rfl⟩ : syracuseStep 2943065 = 2207299) B2207299
theorem B1962043 : Blo 1961435 1962043 := bstep (se 1 (by rfl) ⟨1471532, by rfl⟩ : syracuseStep 1962043 = 2943065) B2943065
theorem B4190429 : Blo 1961435 4190429 := bbase (se 3 (by rfl) ⟨785705, by rfl⟩ : syracuseStep 4190429 = 1571411) (by norm_num)
theorem B2793619 : Blo 1961435 2793619 := bstep (se 1 (by rfl) ⟨2095214, by rfl⟩ : syracuseStep 2793619 = 4190429) B4190429
theorem B14899301 : Blo 1961435 14899301 := bstep (se 4 (by rfl) ⟨1396809, by rfl⟩ : syracuseStep 14899301 = 2793619) B2793619
theorem B9932867 : Blo 1961435 9932867 := bstep (se 1 (by rfl) ⟨7449650, by rfl⟩ : syracuseStep 9932867 = 14899301) B14899301
theorem B6621911 : Blo 1961435 6621911 := bstep (se 1 (by rfl) ⟨4966433, by rfl⟩ : syracuseStep 6621911 = 9932867) B9932867
theorem B4414607 : Blo 1961435 4414607 := bstep (se 1 (by rfl) ⟨3310955, by rfl⟩ : syracuseStep 4414607 = 6621911) B6621911
theorem B2943071 : Blo 1961435 2943071 := bstep (se 1 (by rfl) ⟨2207303, by rfl⟩ : syracuseStep 2943071 = 4414607) B4414607
theorem B1962047 : Blo 1961435 1962047 := bstep (se 1 (by rfl) ⟨1471535, by rfl⟩ : syracuseStep 1962047 = 2943071) B2943071
theorem B2943077 : Blo 1961435 2943077 := bbase (se 4 (by rfl) ⟨275913, by rfl⟩ : syracuseStep 2943077 = 551827) (by norm_num)
theorem B1962051 : Blo 1961435 1962051 := bstep (se 1 (by rfl) ⟨1471538, by rfl⟩ : syracuseStep 1962051 = 2943077) B2943077
theorem B3401933 : Blo 1961435 3401933 := bbase (se 3 (by rfl) ⟨637862, by rfl⟩ : syracuseStep 3401933 = 1275725) (by norm_num)
theorem B9071821 : Blo 1961435 9071821 := bstep (se 3 (by rfl) ⟨1700966, by rfl⟩ : syracuseStep 9071821 = 3401933) B3401933
theorem B48383045 : Blo 1961435 48383045 := bstep (se 4 (by rfl) ⟨4535910, by rfl⟩ : syracuseStep 48383045 = 9071821) B9071821
theorem B32255363 : Blo 1961435 32255363 := bstep (se 1 (by rfl) ⟨24191522, by rfl⟩ : syracuseStep 32255363 = 48383045) B48383045
theorem B21503575 : Blo 1961435 21503575 := bstep (se 1 (by rfl) ⟨16127681, by rfl⟩ : syracuseStep 21503575 = 32255363) B32255363
theorem B114685733 : Blo 1961435 114685733 := bstep (se 4 (by rfl) ⟨10751787, by rfl⟩ : syracuseStep 114685733 = 21503575) B21503575
theorem B76457155 : Blo 1961435 76457155 := bstep (se 1 (by rfl) ⟨57342866, by rfl⟩ : syracuseStep 76457155 = 114685733) B114685733
theorem B101942873 : Blo 1961435 101942873 := bstep (se 2 (by rfl) ⟨38228577, by rfl⟩ : syracuseStep 101942873 = 76457155) B76457155
theorem B67961915 : Blo 1961435 67961915 := bstep (se 1 (by rfl) ⟨50971436, by rfl⟩ : syracuseStep 67961915 = 101942873) B101942873
theorem B45307943 : Blo 1961435 45307943 := bstep (se 1 (by rfl) ⟨33980957, by rfl⟩ : syracuseStep 45307943 = 67961915) B67961915
theorem B30205295 : Blo 1961435 30205295 := bstep (se 1 (by rfl) ⟨22653971, by rfl⟩ : syracuseStep 30205295 = 45307943) B45307943
theorem B20136863 : Blo 1961435 20136863 := bstep (se 1 (by rfl) ⟨15102647, by rfl⟩ : syracuseStep 20136863 = 30205295) B30205295
theorem B53698301 : Blo 1961435 53698301 := bstep (se 3 (by rfl) ⟨10068431, by rfl⟩ : syracuseStep 53698301 = 20136863) B20136863
theorem B35798867 : Blo 1961435 35798867 := bstep (se 1 (by rfl) ⟨26849150, by rfl⟩ : syracuseStep 35798867 = 53698301) B53698301
theorem B23865911 : Blo 1961435 23865911 := bstep (se 1 (by rfl) ⟨17899433, by rfl⟩ : syracuseStep 23865911 = 35798867) B35798867
theorem B15910607 : Blo 1961435 15910607 := bstep (se 1 (by rfl) ⟨11932955, by rfl⟩ : syracuseStep 15910607 = 23865911) B23865911
theorem B10607071 : Blo 1961435 10607071 := bstep (se 1 (by rfl) ⟨7955303, by rfl⟩ : syracuseStep 10607071 = 15910607) B15910607
theorem B14142761 : Blo 1961435 14142761 := bstep (se 2 (by rfl) ⟨5303535, by rfl⟩ : syracuseStep 14142761 = 10607071) B10607071
theorem B9428507 : Blo 1961435 9428507 := bstep (se 1 (by rfl) ⟨7071380, by rfl⟩ : syracuseStep 9428507 = 14142761) B14142761
theorem B6285671 : Blo 1961435 6285671 := bstep (se 1 (by rfl) ⟨4714253, by rfl⟩ : syracuseStep 6285671 = 9428507) B9428507
theorem B4190447 : Blo 1961435 4190447 := bstep (se 1 (by rfl) ⟨3142835, by rfl⟩ : syracuseStep 4190447 = 6285671) B6285671
theorem B2793631 : Blo 1961435 2793631 := bstep (se 1 (by rfl) ⟨2095223, by rfl⟩ : syracuseStep 2793631 = 4190447) B4190447
theorem B3724841 : Blo 1961435 3724841 := bstep (se 2 (by rfl) ⟨1396815, by rfl⟩ : syracuseStep 3724841 = 2793631) B2793631
theorem B2483227 : Blo 1961435 2483227 := bstep (se 1 (by rfl) ⟨1862420, by rfl⟩ : syracuseStep 2483227 = 3724841) B3724841
theorem B3310969 : Blo 1961435 3310969 := bstep (se 2 (by rfl) ⟨1241613, by rfl⟩ : syracuseStep 3310969 = 2483227) B2483227
theorem B4414625 : Blo 1961435 4414625 := bstep (se 2 (by rfl) ⟨1655484, by rfl⟩ : syracuseStep 4414625 = 3310969) B3310969
theorem B2943083 : Blo 1961435 2943083 := bstep (se 1 (by rfl) ⟨2207312, by rfl⟩ : syracuseStep 2943083 = 4414625) B4414625
theorem B1962055 : Blo 1961435 1962055 := bstep (se 1 (by rfl) ⟨1471541, by rfl⟩ : syracuseStep 1962055 = 2943083) B2943083
theorem B2207317 : Blo 1961435 2207317 := bbase (se 8 (by rfl) ⟨12933, by rfl⟩ : syracuseStep 2207317 = 25867) (by norm_num)
theorem B2943089 : Blo 1961435 2943089 := bstep (se 2 (by rfl) ⟨1103658, by rfl⟩ : syracuseStep 2943089 = 2207317) B2207317
theorem B1962059 : Blo 1961435 1962059 := bstep (se 1 (by rfl) ⟨1471544, by rfl⟩ : syracuseStep 1962059 = 2943089) B2943089
theorem B2483237 : Blo 1961435 2483237 := bbase (se 4 (by rfl) ⟨232803, by rfl⟩ : syracuseStep 2483237 = 465607) (by norm_num)
theorem B6621965 : Blo 1961435 6621965 := bstep (se 3 (by rfl) ⟨1241618, by rfl⟩ : syracuseStep 6621965 = 2483237) B2483237
theorem B4414643 : Blo 1961435 4414643 := bstep (se 1 (by rfl) ⟨3310982, by rfl⟩ : syracuseStep 4414643 = 6621965) B6621965
theorem B2943095 : Blo 1961435 2943095 := bstep (se 1 (by rfl) ⟨2207321, by rfl⟩ : syracuseStep 2943095 = 4414643) B4414643
theorem B1962063 : Blo 1961435 1962063 := bstep (se 1 (by rfl) ⟨1471547, by rfl⟩ : syracuseStep 1962063 = 2943095) B2943095
theorem B2943101 : Blo 1961435 2943101 := bbase (se 3 (by rfl) ⟨551831, by rfl⟩ : syracuseStep 2943101 = 1103663) (by norm_num)
theorem B1962067 : Blo 1961435 1962067 := bstep (se 1 (by rfl) ⟨1471550, by rfl⟩ : syracuseStep 1962067 = 2943101) B2943101
theorem B4414661 : Blo 1961435 4414661 := bbase (se 4 (by rfl) ⟨413874, by rfl⟩ : syracuseStep 4414661 = 827749) (by norm_num)
theorem B2943107 : Blo 1961435 2943107 := bstep (se 1 (by rfl) ⟨2207330, by rfl⟩ : syracuseStep 2943107 = 4414661) B4414661
theorem B1962071 : Blo 1961435 1962071 := bstep (se 1 (by rfl) ⟨1471553, by rfl⟩ : syracuseStep 1962071 = 2943107) B2943107
theorem B4714301 : Blo 1961435 4714301 := bbase (se 3 (by rfl) ⟨883931, by rfl⟩ : syracuseStep 4714301 = 1767863) (by norm_num)
theorem B12571469 : Blo 1961435 12571469 := bstep (se 3 (by rfl) ⟨2357150, by rfl⟩ : syracuseStep 12571469 = 4714301) B4714301
theorem B8380979 : Blo 1961435 8380979 := bstep (se 1 (by rfl) ⟨6285734, by rfl⟩ : syracuseStep 8380979 = 12571469) B12571469
theorem B5587319 : Blo 1961435 5587319 := bstep (se 1 (by rfl) ⟨4190489, by rfl⟩ : syracuseStep 5587319 = 8380979) B8380979
theorem B3724879 : Blo 1961435 3724879 := bstep (se 1 (by rfl) ⟨2793659, by rfl⟩ : syracuseStep 3724879 = 5587319) B5587319
theorem B4966505 : Blo 1961435 4966505 := bstep (se 2 (by rfl) ⟨1862439, by rfl⟩ : syracuseStep 4966505 = 3724879) B3724879
theorem B3311003 : Blo 1961435 3311003 := bstep (se 1 (by rfl) ⟨2483252, by rfl⟩ : syracuseStep 3311003 = 4966505) B4966505
theorem B2207335 : Blo 1961435 2207335 := bstep (se 1 (by rfl) ⟨1655501, by rfl⟩ : syracuseStep 2207335 = 3311003) B3311003
theorem B2943113 : Blo 1961435 2943113 := bstep (se 2 (by rfl) ⟨1103667, by rfl⟩ : syracuseStep 2943113 = 2207335) B2207335
theorem B1962075 : Blo 1961435 1962075 := bstep (se 1 (by rfl) ⟨1471556, by rfl⟩ : syracuseStep 1962075 = 2943113) B2943113
theorem B9933029 : Blo 1961435 9933029 := bbase (se 4 (by rfl) ⟨931221, by rfl⟩ : syracuseStep 9933029 = 1862443) (by norm_num)
theorem B6622019 : Blo 1961435 6622019 := bstep (se 1 (by rfl) ⟨4966514, by rfl⟩ : syracuseStep 6622019 = 9933029) B9933029
theorem B4414679 : Blo 1961435 4414679 := bstep (se 1 (by rfl) ⟨3311009, by rfl⟩ : syracuseStep 4414679 = 6622019) B6622019
theorem B2943119 : Blo 1961435 2943119 := bstep (se 1 (by rfl) ⟨2207339, by rfl⟩ : syracuseStep 2943119 = 4414679) B4414679
theorem B1962079 : Blo 1961435 1962079 := bstep (se 1 (by rfl) ⟨1471559, by rfl⟩ : syracuseStep 1962079 = 2943119) B2943119
theorem B2943125 : Blo 1961435 2943125 := bbase (se 6 (by rfl) ⟨68979, by rfl⟩ : syracuseStep 2943125 = 137959) (by norm_num)
theorem B1962083 : Blo 1961435 1962083 := bstep (se 1 (by rfl) ⟨1471562, by rfl⟩ : syracuseStep 1962083 = 2943125) B2943125
theorem B8381029 : Blo 1961435 8381029 := bbase (se 4 (by rfl) ⟨785721, by rfl⟩ : syracuseStep 8381029 = 1571443) (by norm_num)
theorem B11174705 : Blo 1961435 11174705 := bstep (se 2 (by rfl) ⟨4190514, by rfl⟩ : syracuseStep 11174705 = 8381029) B8381029
theorem B7449803 : Blo 1961435 7449803 := bstep (se 1 (by rfl) ⟨5587352, by rfl⟩ : syracuseStep 7449803 = 11174705) B11174705
theorem B4966535 : Blo 1961435 4966535 := bstep (se 1 (by rfl) ⟨3724901, by rfl⟩ : syracuseStep 4966535 = 7449803) B7449803
theorem B3311023 : Blo 1961435 3311023 := bstep (se 1 (by rfl) ⟨2483267, by rfl⟩ : syracuseStep 3311023 = 4966535) B4966535
theorem B4414697 : Blo 1961435 4414697 := bstep (se 2 (by rfl) ⟨1655511, by rfl⟩ : syracuseStep 4414697 = 3311023) B3311023
theorem B2943131 : Blo 1961435 2943131 := bstep (se 1 (by rfl) ⟨2207348, by rfl⟩ : syracuseStep 2943131 = 4414697) B4414697
theorem B1962087 : Blo 1961435 1962087 := bstep (se 1 (by rfl) ⟨1471565, by rfl⟩ : syracuseStep 1962087 = 2943131) B2943131
theorem B2207353 : Blo 1961435 2207353 := bbase (se 2 (by rfl) ⟨827757, by rfl⟩ : syracuseStep 2207353 = 1655515) (by norm_num)
theorem B2943137 : Blo 1961435 2943137 := bstep (se 2 (by rfl) ⟨1103676, by rfl⟩ : syracuseStep 2943137 = 2207353) B2207353
theorem B1962091 : Blo 1961435 1962091 := bstep (se 1 (by rfl) ⟨1471568, by rfl⟩ : syracuseStep 1962091 = 2943137) B2943137
theorem B2651821 : Blo 1961435 2651821 := bbase (se 3 (by rfl) ⟨497216, by rfl⟩ : syracuseStep 2651821 = 994433) (by norm_num)
theorem B14143045 : Blo 1961435 14143045 := bstep (se 4 (by rfl) ⟨1325910, by rfl⟩ : syracuseStep 14143045 = 2651821) B2651821
theorem B18857393 : Blo 1961435 18857393 := bstep (se 2 (by rfl) ⟨7071522, by rfl⟩ : syracuseStep 18857393 = 14143045) B14143045
theorem B12571595 : Blo 1961435 12571595 := bstep (se 1 (by rfl) ⟨9428696, by rfl⟩ : syracuseStep 12571595 = 18857393) B18857393
theorem B8381063 : Blo 1961435 8381063 := bstep (se 1 (by rfl) ⟨6285797, by rfl⟩ : syracuseStep 8381063 = 12571595) B12571595
theorem B5587375 : Blo 1961435 5587375 := bstep (se 1 (by rfl) ⟨4190531, by rfl⟩ : syracuseStep 5587375 = 8381063) B8381063
theorem B7449833 : Blo 1961435 7449833 := bstep (se 2 (by rfl) ⟨2793687, by rfl⟩ : syracuseStep 7449833 = 5587375) B5587375
theorem B4966555 : Blo 1961435 4966555 := bstep (se 1 (by rfl) ⟨3724916, by rfl⟩ : syracuseStep 4966555 = 7449833) B7449833
theorem B6622073 : Blo 1961435 6622073 := bstep (se 2 (by rfl) ⟨2483277, by rfl⟩ : syracuseStep 6622073 = 4966555) B4966555
theorem B4414715 : Blo 1961435 4414715 := bstep (se 1 (by rfl) ⟨3311036, by rfl⟩ : syracuseStep 4414715 = 6622073) B6622073
theorem B2943143 : Blo 1961435 2943143 := bstep (se 1 (by rfl) ⟨2207357, by rfl⟩ : syracuseStep 2943143 = 4414715) B4414715
theorem B1962095 : Blo 1961435 1962095 := bstep (se 1 (by rfl) ⟨1471571, by rfl⟩ : syracuseStep 1962095 = 2943143) B2943143
theorem B2943149 : Blo 1961435 2943149 := bbase (se 3 (by rfl) ⟨551840, by rfl⟩ : syracuseStep 2943149 = 1103681) (by norm_num)
theorem B1962099 : Blo 1961435 1962099 := bstep (se 1 (by rfl) ⟨1471574, by rfl⟩ : syracuseStep 1962099 = 2943149) B2943149
theorem B4414733 : Blo 1961435 4414733 := bbase (se 3 (by rfl) ⟨827762, by rfl⟩ : syracuseStep 4414733 = 1655525) (by norm_num)
theorem B2943155 : Blo 1961435 2943155 := bstep (se 1 (by rfl) ⟨2207366, by rfl⟩ : syracuseStep 2943155 = 4414733) B4414733
theorem B1962103 : Blo 1961435 1962103 := bstep (se 1 (by rfl) ⟨1471577, by rfl⟩ : syracuseStep 1962103 = 2943155) B2943155
theorem B2483293 : Blo 1961435 2483293 := bbase (se 3 (by rfl) ⟨465617, by rfl⟩ : syracuseStep 2483293 = 931235) (by norm_num)
theorem B3311057 : Blo 1961435 3311057 := bstep (se 2 (by rfl) ⟨1241646, by rfl⟩ : syracuseStep 3311057 = 2483293) B2483293
theorem B2207371 : Blo 1961435 2207371 := bstep (se 1 (by rfl) ⟨1655528, by rfl⟩ : syracuseStep 2207371 = 3311057) B3311057
theorem B2943161 : Blo 1961435 2943161 := bstep (se 2 (by rfl) ⟨1103685, by rfl⟩ : syracuseStep 2943161 = 2207371) B2207371
theorem B1962107 : Blo 1961435 1962107 := bstep (se 1 (by rfl) ⟨1471580, by rfl⟩ : syracuseStep 1962107 = 2943161) B2943161
theorem B16762261 : Blo 1961435 16762261 := bbase (se 6 (by rfl) ⟨392865, by rfl⟩ : syracuseStep 16762261 = 785731) (by norm_num)
theorem B22349681 : Blo 1961435 22349681 := bstep (se 2 (by rfl) ⟨8381130, by rfl⟩ : syracuseStep 22349681 = 16762261) B16762261
theorem B14899787 : Blo 1961435 14899787 := bstep (se 1 (by rfl) ⟨11174840, by rfl⟩ : syracuseStep 14899787 = 22349681) B22349681
theorem B9933191 : Blo 1961435 9933191 := bstep (se 1 (by rfl) ⟨7449893, by rfl⟩ : syracuseStep 9933191 = 14899787) B14899787
theorem B6622127 : Blo 1961435 6622127 := bstep (se 1 (by rfl) ⟨4966595, by rfl⟩ : syracuseStep 6622127 = 9933191) B9933191
theorem B4414751 : Blo 1961435 4414751 := bstep (se 1 (by rfl) ⟨3311063, by rfl⟩ : syracuseStep 4414751 = 6622127) B6622127
theorem B2943167 : Blo 1961435 2943167 := bstep (se 1 (by rfl) ⟨2207375, by rfl⟩ : syracuseStep 2943167 = 4414751) B4414751
theorem B1962111 : Blo 1961435 1962111 := bstep (se 1 (by rfl) ⟨1471583, by rfl⟩ : syracuseStep 1962111 = 2943167) B2943167
theorem B2943173 : Blo 1961435 2943173 := bbase (se 4 (by rfl) ⟨275922, by rfl⟩ : syracuseStep 2943173 = 551845) (by norm_num)
theorem B1962115 : Blo 1961435 1962115 := bstep (se 1 (by rfl) ⟨1471586, by rfl⟩ : syracuseStep 1962115 = 2943173) B2943173
theorem B3311077 : Blo 1961435 3311077 := bbase (se 4 (by rfl) ⟨310413, by rfl⟩ : syracuseStep 3311077 = 620827) (by norm_num)
theorem B4414769 : Blo 1961435 4414769 := bstep (se 2 (by rfl) ⟨1655538, by rfl⟩ : syracuseStep 4414769 = 3311077) B3311077
theorem B2943179 : Blo 1961435 2943179 := bstep (se 1 (by rfl) ⟨2207384, by rfl⟩ : syracuseStep 2943179 = 4414769) B4414769
theorem B1962119 : Blo 1961435 1962119 := bstep (se 1 (by rfl) ⟨1471589, by rfl⟩ : syracuseStep 1962119 = 2943179) B2943179
theorem B2207389 : Blo 1961435 2207389 := bbase (se 3 (by rfl) ⟨413885, by rfl⟩ : syracuseStep 2207389 = 827771) (by norm_num)
theorem B2943185 : Blo 1961435 2943185 := bstep (se 2 (by rfl) ⟨1103694, by rfl⟩ : syracuseStep 2943185 = 2207389) B2207389
theorem B1962123 : Blo 1961435 1962123 := bstep (se 1 (by rfl) ⟨1471592, by rfl⟩ : syracuseStep 1962123 = 2943185) B2943185
theorem B6622181 : Blo 1961435 6622181 := bbase (se 4 (by rfl) ⟨620829, by rfl⟩ : syracuseStep 6622181 = 1241659) (by norm_num)
theorem B4414787 : Blo 1961435 4414787 := bstep (se 1 (by rfl) ⟨3311090, by rfl⟩ : syracuseStep 4414787 = 6622181) B6622181
theorem B2943191 : Blo 1961435 2943191 := bstep (se 1 (by rfl) ⟨2207393, by rfl⟩ : syracuseStep 2943191 = 4414787) B4414787
theorem B1962127 : Blo 1961435 1962127 := bstep (se 1 (by rfl) ⟨1471595, by rfl⟩ : syracuseStep 1962127 = 2943191) B2943191
theorem B2943197 : Blo 1961435 2943197 := bbase (se 3 (by rfl) ⟨551849, by rfl⟩ : syracuseStep 2943197 = 1103699) (by norm_num)
theorem B1962131 : Blo 1961435 1962131 := bstep (se 1 (by rfl) ⟨1471598, by rfl⟩ : syracuseStep 1962131 = 2943197) B2943197
theorem B4414805 : Blo 1961435 4414805 := bbase (se 11 (by rfl) ⟨3233, by rfl⟩ : syracuseStep 4414805 = 6467) (by norm_num)
theorem B2943203 : Blo 1961435 2943203 := bstep (se 1 (by rfl) ⟨2207402, by rfl⟩ : syracuseStep 2943203 = 4414805) B4414805
theorem B1962135 : Blo 1961435 1962135 := bstep (se 1 (by rfl) ⟨1471601, by rfl⟩ : syracuseStep 1962135 = 2943203) B2943203
theorem B2095313 : Blo 1961435 2095313 := bbase (se 2 (by rfl) ⟨785742, by rfl⟩ : syracuseStep 2095313 = 1571485) (by norm_num)
theorem B5587501 : Blo 1961435 5587501 := bstep (se 3 (by rfl) ⟨1047656, by rfl⟩ : syracuseStep 5587501 = 2095313) B2095313
theorem B7450001 : Blo 1961435 7450001 := bstep (se 2 (by rfl) ⟨2793750, by rfl⟩ : syracuseStep 7450001 = 5587501) B5587501
theorem B4966667 : Blo 1961435 4966667 := bstep (se 1 (by rfl) ⟨3725000, by rfl⟩ : syracuseStep 4966667 = 7450001) B7450001
theorem B3311111 : Blo 1961435 3311111 := bstep (se 1 (by rfl) ⟨2483333, by rfl⟩ : syracuseStep 3311111 = 4966667) B4966667
theorem B2207407 : Blo 1961435 2207407 := bstep (se 1 (by rfl) ⟨1655555, by rfl⟩ : syracuseStep 2207407 = 3311111) B3311111
theorem B2943209 : Blo 1961435 2943209 := bstep (se 2 (by rfl) ⟨1103703, by rfl⟩ : syracuseStep 2943209 = 2207407) B2207407
theorem B1962139 : Blo 1961435 1962139 := bstep (se 1 (by rfl) ⟨1471604, by rfl⟩ : syracuseStep 1962139 = 2943209) B2943209
theorem B3356293 : Blo 1961435 3356293 := bbase (se 4 (by rfl) ⟨314652, by rfl⟩ : syracuseStep 3356293 = 629305) (by norm_num)
theorem B4475057 : Blo 1961435 4475057 := bstep (se 2 (by rfl) ⟨1678146, by rfl⟩ : syracuseStep 4475057 = 3356293) B3356293
theorem B47733941 : Blo 1961435 47733941 := bstep (se 5 (by rfl) ⟨2237528, by rfl⟩ : syracuseStep 47733941 = 4475057) B4475057
theorem B31822627 : Blo 1961435 31822627 := bstep (se 1 (by rfl) ⟨23866970, by rfl⟩ : syracuseStep 31822627 = 47733941) B47733941
theorem B42430169 : Blo 1961435 42430169 := bstep (se 2 (by rfl) ⟨15911313, by rfl⟩ : syracuseStep 42430169 = 31822627) B31822627
theorem B28286779 : Blo 1961435 28286779 := bstep (se 1 (by rfl) ⟨21215084, by rfl⟩ : syracuseStep 28286779 = 42430169) B42430169
theorem B37715705 : Blo 1961435 37715705 := bstep (se 2 (by rfl) ⟨14143389, by rfl⟩ : syracuseStep 37715705 = 28286779) B28286779
theorem B25143803 : Blo 1961435 25143803 := bstep (se 1 (by rfl) ⟨18857852, by rfl⟩ : syracuseStep 25143803 = 37715705) B37715705
theorem B16762535 : Blo 1961435 16762535 := bstep (se 1 (by rfl) ⟨12571901, by rfl⟩ : syracuseStep 16762535 = 25143803) B25143803
theorem B11175023 : Blo 1961435 11175023 := bstep (se 1 (by rfl) ⟨8381267, by rfl⟩ : syracuseStep 11175023 = 16762535) B16762535
theorem B7450015 : Blo 1961435 7450015 := bstep (se 1 (by rfl) ⟨5587511, by rfl⟩ : syracuseStep 7450015 = 11175023) B11175023
theorem B9933353 : Blo 1961435 9933353 := bstep (se 2 (by rfl) ⟨3725007, by rfl⟩ : syracuseStep 9933353 = 7450015) B7450015
theorem B6622235 : Blo 1961435 6622235 := bstep (se 1 (by rfl) ⟨4966676, by rfl⟩ : syracuseStep 6622235 = 9933353) B9933353
theorem B4414823 : Blo 1961435 4414823 := bstep (se 1 (by rfl) ⟨3311117, by rfl⟩ : syracuseStep 4414823 = 6622235) B6622235
theorem B2943215 : Blo 1961435 2943215 := bstep (se 1 (by rfl) ⟨2207411, by rfl⟩ : syracuseStep 2943215 = 4414823) B4414823
theorem B1962143 : Blo 1961435 1962143 := bstep (se 1 (by rfl) ⟨1471607, by rfl⟩ : syracuseStep 1962143 = 2943215) B2943215
theorem B2943221 : Blo 1961435 2943221 := bbase (se 5 (by rfl) ⟨137963, by rfl⟩ : syracuseStep 2943221 = 275927) (by norm_num)
theorem B1962147 : Blo 1961435 1962147 := bstep (se 1 (by rfl) ⟨1471610, by rfl⟩ : syracuseStep 1962147 = 2943221) B2943221
theorem B3356309 : Blo 1961435 3356309 := bbase (se 6 (by rfl) ⟨78663, by rfl⟩ : syracuseStep 3356309 = 157327) (by norm_num)
theorem B2237539 : Blo 1961435 2237539 := bstep (se 1 (by rfl) ⟨1678154, by rfl⟩ : syracuseStep 2237539 = 3356309) B3356309
theorem B2983385 : Blo 1961435 2983385 := bstep (se 2 (by rfl) ⟨1118769, by rfl⟩ : syracuseStep 2983385 = 2237539) B2237539
theorem B1988923 : Blo 1961435 1988923 := bstep (se 1 (by rfl) ⟨1491692, by rfl⟩ : syracuseStep 1988923 = 2983385) B2983385
theorem B2651897 : Blo 1961435 2651897 := bstep (se 2 (by rfl) ⟨994461, by rfl⟩ : syracuseStep 2651897 = 1988923) B1988923
theorem B7071725 : Blo 1961435 7071725 := bstep (se 3 (by rfl) ⟨1325948, by rfl⟩ : syracuseStep 7071725 = 2651897) B2651897
theorem B18857933 : Blo 1961435 18857933 := bstep (se 3 (by rfl) ⟨3535862, by rfl⟩ : syracuseStep 18857933 = 7071725) B7071725
theorem B12571955 : Blo 1961435 12571955 := bstep (se 1 (by rfl) ⟨9428966, by rfl⟩ : syracuseStep 12571955 = 18857933) B18857933
theorem B8381303 : Blo 1961435 8381303 := bstep (se 1 (by rfl) ⟨6285977, by rfl⟩ : syracuseStep 8381303 = 12571955) B12571955
theorem B5587535 : Blo 1961435 5587535 := bstep (se 1 (by rfl) ⟨4190651, by rfl⟩ : syracuseStep 5587535 = 8381303) B8381303
theorem B3725023 : Blo 1961435 3725023 := bstep (se 1 (by rfl) ⟨2793767, by rfl⟩ : syracuseStep 3725023 = 5587535) B5587535
theorem B4966697 : Blo 1961435 4966697 := bstep (se 2 (by rfl) ⟨1862511, by rfl⟩ : syracuseStep 4966697 = 3725023) B3725023
theorem B3311131 : Blo 1961435 3311131 := bstep (se 1 (by rfl) ⟨2483348, by rfl⟩ : syracuseStep 3311131 = 4966697) B4966697
theorem B4414841 : Blo 1961435 4414841 := bstep (se 2 (by rfl) ⟨1655565, by rfl⟩ : syracuseStep 4414841 = 3311131) B3311131
theorem B2943227 : Blo 1961435 2943227 := bstep (se 1 (by rfl) ⟨2207420, by rfl⟩ : syracuseStep 2943227 = 4414841) B4414841
theorem B1962151 : Blo 1961435 1962151 := bstep (se 1 (by rfl) ⟨1471613, by rfl⟩ : syracuseStep 1962151 = 2943227) B2943227
theorem B2207425 : Blo 1961435 2207425 := bbase (se 2 (by rfl) ⟨827784, by rfl⟩ : syracuseStep 2207425 = 1655569) (by norm_num)
theorem B2943233 : Blo 1961435 2943233 := bstep (se 2 (by rfl) ⟨1103712, by rfl⟩ : syracuseStep 2943233 = 2207425) B2207425
theorem B1962155 : Blo 1961435 1962155 := bstep (se 1 (by rfl) ⟨1471616, by rfl⟩ : syracuseStep 1962155 = 2943233) B2943233
theorem B4966717 : Blo 1961435 4966717 := bbase (se 3 (by rfl) ⟨931259, by rfl⟩ : syracuseStep 4966717 = 1862519) (by norm_num)
theorem B6622289 : Blo 1961435 6622289 := bstep (se 2 (by rfl) ⟨2483358, by rfl⟩ : syracuseStep 6622289 = 4966717) B4966717
theorem B4414859 : Blo 1961435 4414859 := bstep (se 1 (by rfl) ⟨3311144, by rfl⟩ : syracuseStep 4414859 = 6622289) B6622289
theorem B2943239 : Blo 1961435 2943239 := bstep (se 1 (by rfl) ⟨2207429, by rfl⟩ : syracuseStep 2943239 = 4414859) B4414859
theorem B1962159 : Blo 1961435 1962159 := bstep (se 1 (by rfl) ⟨1471619, by rfl⟩ : syracuseStep 1962159 = 2943239) B2943239
theorem B2943245 : Blo 1961435 2943245 := bbase (se 3 (by rfl) ⟨551858, by rfl⟩ : syracuseStep 2943245 = 1103717) (by norm_num)
theorem B1962163 : Blo 1961435 1962163 := bstep (se 1 (by rfl) ⟨1471622, by rfl⟩ : syracuseStep 1962163 = 2943245) B2943245
theorem B4414877 : Blo 1961435 4414877 := bbase (se 3 (by rfl) ⟨827789, by rfl⟩ : syracuseStep 4414877 = 1655579) (by norm_num)
theorem B2943251 : Blo 1961435 2943251 := bstep (se 1 (by rfl) ⟨2207438, by rfl⟩ : syracuseStep 2943251 = 4414877) B4414877
theorem B1962167 : Blo 1961435 1962167 := bstep (se 1 (by rfl) ⟨1471625, by rfl⟩ : syracuseStep 1962167 = 2943251) B2943251
theorem B3311165 : Blo 1961435 3311165 := bbase (se 3 (by rfl) ⟨620843, by rfl⟩ : syracuseStep 3311165 = 1241687) (by norm_num)
theorem B2207443 : Blo 1961435 2207443 := bstep (se 1 (by rfl) ⟨1655582, by rfl⟩ : syracuseStep 2207443 = 3311165) B3311165
theorem B2943257 : Blo 1961435 2943257 := bstep (se 2 (by rfl) ⟨1103721, by rfl⟩ : syracuseStep 2943257 = 2207443) B2207443
theorem B1962171 : Blo 1961435 1962171 := bstep (se 1 (by rfl) ⟨1471628, by rfl⟩ : syracuseStep 1962171 = 2943257) B2943257
theorem B4714541 : Blo 1961435 4714541 := bbase (se 3 (by rfl) ⟨883976, by rfl⟩ : syracuseStep 4714541 = 1767953) (by norm_num)
theorem B3143027 : Blo 1961435 3143027 := bstep (se 1 (by rfl) ⟨2357270, by rfl⟩ : syracuseStep 3143027 = 4714541) B4714541
theorem B2095351 : Blo 1961435 2095351 := bstep (se 1 (by rfl) ⟨1571513, by rfl⟩ : syracuseStep 2095351 = 3143027) B3143027
theorem B11175205 : Blo 1961435 11175205 := bstep (se 4 (by rfl) ⟨1047675, by rfl⟩ : syracuseStep 11175205 = 2095351) B2095351
theorem B14900273 : Blo 1961435 14900273 := bstep (se 2 (by rfl) ⟨5587602, by rfl⟩ : syracuseStep 14900273 = 11175205) B11175205
theorem B9933515 : Blo 1961435 9933515 := bstep (se 1 (by rfl) ⟨7450136, by rfl⟩ : syracuseStep 9933515 = 14900273) B14900273
theorem B6622343 : Blo 1961435 6622343 := bstep (se 1 (by rfl) ⟨4966757, by rfl⟩ : syracuseStep 6622343 = 9933515) B9933515
theorem B4414895 : Blo 1961435 4414895 := bstep (se 1 (by rfl) ⟨3311171, by rfl⟩ : syracuseStep 4414895 = 6622343) B6622343
theorem B2943263 : Blo 1961435 2943263 := bstep (se 1 (by rfl) ⟨2207447, by rfl⟩ : syracuseStep 2943263 = 4414895) B4414895
theorem B1962175 : Blo 1961435 1962175 := bstep (se 1 (by rfl) ⟨1471631, by rfl⟩ : syracuseStep 1962175 = 2943263) B2943263
theorem B2943269 : Blo 1961435 2943269 := bbase (se 4 (by rfl) ⟨275931, by rfl⟩ : syracuseStep 2943269 = 551863) (by norm_num)
theorem B1962179 : Blo 1961435 1962179 := bstep (se 1 (by rfl) ⟨1471634, by rfl⟩ : syracuseStep 1962179 = 2943269) B2943269
theorem B2483389 : Blo 1961435 2483389 := bbase (se 3 (by rfl) ⟨465635, by rfl⟩ : syracuseStep 2483389 = 931271) (by norm_num)
theorem B3311185 : Blo 1961435 3311185 := bstep (se 2 (by rfl) ⟨1241694, by rfl⟩ : syracuseStep 3311185 = 2483389) B2483389
theorem B4414913 : Blo 1961435 4414913 := bstep (se 2 (by rfl) ⟨1655592, by rfl⟩ : syracuseStep 4414913 = 3311185) B3311185
theorem B2943275 : Blo 1961435 2943275 := bstep (se 1 (by rfl) ⟨2207456, by rfl⟩ : syracuseStep 2943275 = 4414913) B4414913
theorem B1962183 : Blo 1961435 1962183 := bstep (se 1 (by rfl) ⟨1471637, by rfl⟩ : syracuseStep 1962183 = 2943275) B2943275
theorem B2207461 : Blo 1961435 2207461 := bbase (se 4 (by rfl) ⟨206949, by rfl⟩ : syracuseStep 2207461 = 413899) (by norm_num)
theorem B2943281 : Blo 1961435 2943281 := bstep (se 2 (by rfl) ⟨1103730, by rfl⟩ : syracuseStep 2943281 = 2207461) B2207461
theorem B1962187 : Blo 1961435 1962187 := bstep (se 1 (by rfl) ⟨1471640, by rfl⟩ : syracuseStep 1962187 = 2943281) B2943281
theorem B3143053 : Blo 1961435 3143053 := bbase (se 3 (by rfl) ⟨589322, by rfl⟩ : syracuseStep 3143053 = 1178645) (by norm_num)
theorem B4190737 : Blo 1961435 4190737 := bstep (se 2 (by rfl) ⟨1571526, by rfl⟩ : syracuseStep 4190737 = 3143053) B3143053
theorem B5587649 : Blo 1961435 5587649 := bstep (se 2 (by rfl) ⟨2095368, by rfl⟩ : syracuseStep 5587649 = 4190737) B4190737
theorem B3725099 : Blo 1961435 3725099 := bstep (se 1 (by rfl) ⟨2793824, by rfl⟩ : syracuseStep 3725099 = 5587649) B5587649
theorem B2483399 : Blo 1961435 2483399 := bstep (se 1 (by rfl) ⟨1862549, by rfl⟩ : syracuseStep 2483399 = 3725099) B3725099
theorem B6622397 : Blo 1961435 6622397 := bstep (se 3 (by rfl) ⟨1241699, by rfl⟩ : syracuseStep 6622397 = 2483399) B2483399
theorem B4414931 : Blo 1961435 4414931 := bstep (se 1 (by rfl) ⟨3311198, by rfl⟩ : syracuseStep 4414931 = 6622397) B6622397
theorem B2943287 : Blo 1961435 2943287 := bstep (se 1 (by rfl) ⟨2207465, by rfl⟩ : syracuseStep 2943287 = 4414931) B4414931
theorem B1962191 : Blo 1961435 1962191 := bstep (se 1 (by rfl) ⟨1471643, by rfl⟩ : syracuseStep 1962191 = 2943287) B2943287
theorem B2943293 : Blo 1961435 2943293 := bbase (se 3 (by rfl) ⟨551867, by rfl⟩ : syracuseStep 2943293 = 1103735) (by norm_num)
theorem B1962195 : Blo 1961435 1962195 := bstep (se 1 (by rfl) ⟨1471646, by rfl⟩ : syracuseStep 1962195 = 2943293) B2943293
theorem B4414949 : Blo 1961435 4414949 := bbase (se 4 (by rfl) ⟨413901, by rfl⟩ : syracuseStep 4414949 = 827803) (by norm_num)
theorem B2943299 : Blo 1961435 2943299 := bstep (se 1 (by rfl) ⟨2207474, by rfl⟩ : syracuseStep 2943299 = 4414949) B4414949
theorem B1962199 : Blo 1961435 1962199 := bstep (se 1 (by rfl) ⟨1471649, by rfl⟩ : syracuseStep 1962199 = 2943299) B2943299
theorem B4966829 : Blo 1961435 4966829 := bbase (se 3 (by rfl) ⟨931280, by rfl⟩ : syracuseStep 4966829 = 1862561) (by norm_num)
theorem B3311219 : Blo 1961435 3311219 := bstep (se 1 (by rfl) ⟨2483414, by rfl⟩ : syracuseStep 3311219 = 4966829) B4966829
theorem B2207479 : Blo 1961435 2207479 := bstep (se 1 (by rfl) ⟨1655609, by rfl⟩ : syracuseStep 2207479 = 3311219) B3311219
theorem B2943305 : Blo 1961435 2943305 := bstep (se 2 (by rfl) ⟨1103739, by rfl⟩ : syracuseStep 2943305 = 2207479) B2207479
theorem B1962203 : Blo 1961435 1962203 := bstep (se 1 (by rfl) ⟨1471652, by rfl⟩ : syracuseStep 1962203 = 2943305) B2943305
theorem B2357309 : Blo 1961435 2357309 := bbase (se 3 (by rfl) ⟨441995, by rfl⟩ : syracuseStep 2357309 = 883991) (by norm_num)
theorem B6286157 : Blo 1961435 6286157 := bstep (se 3 (by rfl) ⟨1178654, by rfl⟩ : syracuseStep 6286157 = 2357309) B2357309
theorem B4190771 : Blo 1961435 4190771 := bstep (se 1 (by rfl) ⟨3143078, by rfl⟩ : syracuseStep 4190771 = 6286157) B6286157
theorem B2793847 : Blo 1961435 2793847 := bstep (se 1 (by rfl) ⟨2095385, by rfl⟩ : syracuseStep 2793847 = 4190771) B4190771
theorem B3725129 : Blo 1961435 3725129 := bstep (se 2 (by rfl) ⟨1396923, by rfl⟩ : syracuseStep 3725129 = 2793847) B2793847
theorem B9933677 : Blo 1961435 9933677 := bstep (se 3 (by rfl) ⟨1862564, by rfl⟩ : syracuseStep 9933677 = 3725129) B3725129
theorem B6622451 : Blo 1961435 6622451 := bstep (se 1 (by rfl) ⟨4966838, by rfl⟩ : syracuseStep 6622451 = 9933677) B9933677
theorem B4414967 : Blo 1961435 4414967 := bstep (se 1 (by rfl) ⟨3311225, by rfl⟩ : syracuseStep 4414967 = 6622451) B6622451
theorem B2943311 : Blo 1961435 2943311 := bstep (se 1 (by rfl) ⟨2207483, by rfl⟩ : syracuseStep 2943311 = 4414967) B4414967
theorem B1962207 : Blo 1961435 1962207 := bstep (se 1 (by rfl) ⟨1471655, by rfl⟩ : syracuseStep 1962207 = 2943311) B2943311
theorem B2943317 : Blo 1961435 2943317 := bbase (se 10 (by rfl) ⟨4311, by rfl⟩ : syracuseStep 2943317 = 8623) (by norm_num)
theorem B1962211 : Blo 1961435 1962211 := bstep (se 1 (by rfl) ⟨1471658, by rfl⟩ : syracuseStep 1962211 = 2943317) B2943317
theorem B5587717 : Blo 1961435 5587717 := bbase (se 4 (by rfl) ⟨523848, by rfl⟩ : syracuseStep 5587717 = 1047697) (by norm_num)
theorem B7450289 : Blo 1961435 7450289 := bstep (se 2 (by rfl) ⟨2793858, by rfl⟩ : syracuseStep 7450289 = 5587717) B5587717
theorem B4966859 : Blo 1961435 4966859 := bstep (se 1 (by rfl) ⟨3725144, by rfl⟩ : syracuseStep 4966859 = 7450289) B7450289
theorem B3311239 : Blo 1961435 3311239 := bstep (se 1 (by rfl) ⟨2483429, by rfl⟩ : syracuseStep 3311239 = 4966859) B4966859
theorem B4414985 : Blo 1961435 4414985 := bstep (se 2 (by rfl) ⟨1655619, by rfl⟩ : syracuseStep 4414985 = 3311239) B3311239
theorem B2943323 : Blo 1961435 2943323 := bstep (se 1 (by rfl) ⟨2207492, by rfl⟩ : syracuseStep 2943323 = 4414985) B4414985
theorem B1962215 : Blo 1961435 1962215 := bstep (se 1 (by rfl) ⟨1471661, by rfl⟩ : syracuseStep 1962215 = 2943323) B2943323
theorem B2207497 : Blo 1961435 2207497 := bbase (se 2 (by rfl) ⟨827811, by rfl⟩ : syracuseStep 2207497 = 1655623) (by norm_num)
theorem B2943329 : Blo 1961435 2943329 := bstep (se 2 (by rfl) ⟨1103748, by rfl⟩ : syracuseStep 2943329 = 2207497) B2207497
theorem B1962219 : Blo 1961435 1962219 := bstep (se 1 (by rfl) ⟨1471664, by rfl⟩ : syracuseStep 1962219 = 2943329) B2943329
theorem B2762029 : Blo 1961435 2762029 := bbase (se 3 (by rfl) ⟨517880, by rfl⟩ : syracuseStep 2762029 = 1035761) (by norm_num)
theorem B14730821 : Blo 1961435 14730821 := bstep (se 4 (by rfl) ⟨1381014, by rfl⟩ : syracuseStep 14730821 = 2762029) B2762029
theorem B9820547 : Blo 1961435 9820547 := bstep (se 1 (by rfl) ⟨7365410, by rfl⟩ : syracuseStep 9820547 = 14730821) B14730821
theorem B6547031 : Blo 1961435 6547031 := bstep (se 1 (by rfl) ⟨4910273, by rfl⟩ : syracuseStep 6547031 = 9820547) B9820547
theorem B4364687 : Blo 1961435 4364687 := bstep (se 1 (by rfl) ⟨3273515, by rfl⟩ : syracuseStep 4364687 = 6547031) B6547031
theorem B2909791 : Blo 1961435 2909791 := bstep (se 1 (by rfl) ⟨2182343, by rfl⟩ : syracuseStep 2909791 = 4364687) B4364687
theorem B3879721 : Blo 1961435 3879721 := bstep (se 2 (by rfl) ⟨1454895, by rfl⟩ : syracuseStep 3879721 = 2909791) B2909791
theorem B20691845 : Blo 1961435 20691845 := bstep (se 4 (by rfl) ⟨1939860, by rfl⟩ : syracuseStep 20691845 = 3879721) B3879721
theorem B13794563 : Blo 1961435 13794563 := bstep (se 1 (by rfl) ⟨10345922, by rfl⟩ : syracuseStep 13794563 = 20691845) B20691845
theorem B36785501 : Blo 1961435 36785501 := bstep (se 3 (by rfl) ⟨6897281, by rfl⟩ : syracuseStep 36785501 = 13794563) B13794563
theorem B24523667 : Blo 1961435 24523667 := bstep (se 1 (by rfl) ⟨18392750, by rfl⟩ : syracuseStep 24523667 = 36785501) B36785501
theorem B16349111 : Blo 1961435 16349111 := bstep (se 1 (by rfl) ⟨12261833, by rfl⟩ : syracuseStep 16349111 = 24523667) B24523667
theorem B10899407 : Blo 1961435 10899407 := bstep (se 1 (by rfl) ⟨8174555, by rfl⟩ : syracuseStep 10899407 = 16349111) B16349111
theorem B7266271 : Blo 1961435 7266271 := bstep (se 1 (by rfl) ⟨5449703, by rfl⟩ : syracuseStep 7266271 = 10899407) B10899407
theorem B9688361 : Blo 1961435 9688361 := bstep (se 2 (by rfl) ⟨3633135, by rfl⟩ : syracuseStep 9688361 = 7266271) B7266271
theorem B25835629 : Blo 1961435 25835629 := bstep (se 3 (by rfl) ⟨4844180, by rfl⟩ : syracuseStep 25835629 = 9688361) B9688361
theorem B551160085 : Blo 1961435 551160085 := bstep (se 6 (by rfl) ⟨12917814, by rfl⟩ : syracuseStep 551160085 = 25835629) B25835629
theorem B734880113 : Blo 1961435 734880113 := bstep (se 2 (by rfl) ⟨275580042, by rfl⟩ : syracuseStep 734880113 = 551160085) B551160085
theorem B489920075 : Blo 1961435 489920075 := bstep (se 1 (by rfl) ⟨367440056, by rfl⟩ : syracuseStep 489920075 = 734880113) B734880113
theorem B326613383 : Blo 1961435 326613383 := bstep (se 1 (by rfl) ⟨244960037, by rfl⟩ : syracuseStep 326613383 = 489920075) B489920075
theorem B217742255 : Blo 1961435 217742255 := bstep (se 1 (by rfl) ⟨163306691, by rfl⟩ : syracuseStep 217742255 = 326613383) B326613383
theorem B145161503 : Blo 1961435 145161503 := bstep (se 1 (by rfl) ⟨108871127, by rfl⟩ : syracuseStep 145161503 = 217742255) B217742255
theorem B96774335 : Blo 1961435 96774335 := bstep (se 1 (by rfl) ⟨72580751, by rfl⟩ : syracuseStep 96774335 = 145161503) B145161503
theorem B64516223 : Blo 1961435 64516223 := bstep (se 1 (by rfl) ⟨48387167, by rfl⟩ : syracuseStep 64516223 = 96774335) B96774335
theorem B172043261 : Blo 1961435 172043261 := bstep (se 3 (by rfl) ⟨32258111, by rfl⟩ : syracuseStep 172043261 = 64516223) B64516223
theorem B114695507 : Blo 1961435 114695507 := bstep (se 1 (by rfl) ⟨86021630, by rfl⟩ : syracuseStep 114695507 = 172043261) B172043261
theorem B76463671 : Blo 1961435 76463671 := bstep (se 1 (by rfl) ⟨57347753, by rfl⟩ : syracuseStep 76463671 = 114695507) B114695507
theorem B101951561 : Blo 1961435 101951561 := bstep (se 2 (by rfl) ⟨38231835, by rfl⟩ : syracuseStep 101951561 = 76463671) B76463671
theorem B67967707 : Blo 1961435 67967707 := bstep (se 1 (by rfl) ⟨50975780, by rfl⟩ : syracuseStep 67967707 = 101951561) B101951561
theorem B90623609 : Blo 1961435 90623609 := bstep (se 2 (by rfl) ⟨33983853, by rfl⟩ : syracuseStep 90623609 = 67967707) B67967707
theorem B60415739 : Blo 1961435 60415739 := bstep (se 1 (by rfl) ⟨45311804, by rfl⟩ : syracuseStep 60415739 = 90623609) B90623609
theorem B40277159 : Blo 1961435 40277159 := bstep (se 1 (by rfl) ⟨30207869, by rfl⟩ : syracuseStep 40277159 = 60415739) B60415739
theorem B26851439 : Blo 1961435 26851439 := bstep (se 1 (by rfl) ⟨20138579, by rfl⟩ : syracuseStep 26851439 = 40277159) B40277159
theorem B71603837 : Blo 1961435 71603837 := bstep (se 3 (by rfl) ⟨13425719, by rfl⟩ : syracuseStep 71603837 = 26851439) B26851439
theorem B47735891 : Blo 1961435 47735891 := bstep (se 1 (by rfl) ⟨35801918, by rfl⟩ : syracuseStep 47735891 = 71603837) B71603837
theorem B31823927 : Blo 1961435 31823927 := bstep (se 1 (by rfl) ⟨23867945, by rfl⟩ : syracuseStep 31823927 = 47735891) B47735891
theorem B21215951 : Blo 1961435 21215951 := bstep (se 1 (by rfl) ⟨15911963, by rfl⟩ : syracuseStep 21215951 = 31823927) B31823927
theorem B14143967 : Blo 1961435 14143967 := bstep (se 1 (by rfl) ⟨10607975, by rfl⟩ : syracuseStep 14143967 = 21215951) B21215951
theorem B9429311 : Blo 1961435 9429311 := bstep (se 1 (by rfl) ⟨7071983, by rfl⟩ : syracuseStep 9429311 = 14143967) B14143967
theorem B25144829 : Blo 1961435 25144829 := bstep (se 3 (by rfl) ⟨4714655, by rfl⟩ : syracuseStep 25144829 = 9429311) B9429311
theorem B16763219 : Blo 1961435 16763219 := bstep (se 1 (by rfl) ⟨12572414, by rfl⟩ : syracuseStep 16763219 = 25144829) B25144829
theorem B11175479 : Blo 1961435 11175479 := bstep (se 1 (by rfl) ⟨8381609, by rfl⟩ : syracuseStep 11175479 = 16763219) B16763219
theorem B7450319 : Blo 1961435 7450319 := bstep (se 1 (by rfl) ⟨5587739, by rfl⟩ : syracuseStep 7450319 = 11175479) B11175479
theorem B4966879 : Blo 1961435 4966879 := bstep (se 1 (by rfl) ⟨3725159, by rfl⟩ : syracuseStep 4966879 = 7450319) B7450319
theorem B6622505 : Blo 1961435 6622505 := bstep (se 2 (by rfl) ⟨2483439, by rfl⟩ : syracuseStep 6622505 = 4966879) B4966879
theorem B4415003 : Blo 1961435 4415003 := bstep (se 1 (by rfl) ⟨3311252, by rfl⟩ : syracuseStep 4415003 = 6622505) B6622505
theorem B2943335 : Blo 1961435 2943335 := bstep (se 1 (by rfl) ⟨2207501, by rfl⟩ : syracuseStep 2943335 = 4415003) B4415003
theorem B1962223 : Blo 1961435 1962223 := bstep (se 1 (by rfl) ⟨1471667, by rfl⟩ : syracuseStep 1962223 = 2943335) B2943335
theorem B2943341 : Blo 1961435 2943341 := bbase (se 3 (by rfl) ⟨551876, by rfl⟩ : syracuseStep 2943341 = 1103753) (by norm_num)
theorem B1962227 : Blo 1961435 1962227 := bstep (se 1 (by rfl) ⟨1471670, by rfl⟩ : syracuseStep 1962227 = 2943341) B2943341
theorem B4415021 : Blo 1961435 4415021 := bbase (se 3 (by rfl) ⟨827816, by rfl⟩ : syracuseStep 4415021 = 1655633) (by norm_num)
theorem B2943347 : Blo 1961435 2943347 := bstep (se 1 (by rfl) ⟨2207510, by rfl⟩ : syracuseStep 2943347 = 4415021) B4415021
theorem B1962231 : Blo 1961435 1962231 := bstep (se 1 (by rfl) ⟨1471673, by rfl⟩ : syracuseStep 1962231 = 2943347) B2943347
theorem B7168517 : Blo 1961435 7168517 := bbase (se 4 (by rfl) ⟨672048, by rfl⟩ : syracuseStep 7168517 = 1344097) (by norm_num)
theorem B4779011 : Blo 1961435 4779011 := bstep (se 1 (by rfl) ⟨3584258, by rfl⟩ : syracuseStep 4779011 = 7168517) B7168517
theorem B12744029 : Blo 1961435 12744029 := bstep (se 3 (by rfl) ⟨2389505, by rfl⟩ : syracuseStep 12744029 = 4779011) B4779011
theorem B8496019 : Blo 1961435 8496019 := bstep (se 1 (by rfl) ⟨6372014, by rfl⟩ : syracuseStep 8496019 = 12744029) B12744029
theorem B11328025 : Blo 1961435 11328025 := bstep (se 2 (by rfl) ⟨4248009, by rfl⟩ : syracuseStep 11328025 = 8496019) B8496019
theorem B15104033 : Blo 1961435 15104033 := bstep (se 2 (by rfl) ⟨5664012, by rfl⟩ : syracuseStep 15104033 = 11328025) B11328025
theorem B10069355 : Blo 1961435 10069355 := bstep (se 1 (by rfl) ⟨7552016, by rfl⟩ : syracuseStep 10069355 = 15104033) B15104033
theorem B6712903 : Blo 1961435 6712903 := bstep (se 1 (by rfl) ⟨5034677, by rfl⟩ : syracuseStep 6712903 = 10069355) B10069355
theorem B8950537 : Blo 1961435 8950537 := bstep (se 2 (by rfl) ⟨3356451, by rfl⟩ : syracuseStep 8950537 = 6712903) B6712903
theorem B11934049 : Blo 1961435 11934049 := bstep (se 2 (by rfl) ⟨4475268, by rfl⟩ : syracuseStep 11934049 = 8950537) B8950537
theorem B15912065 : Blo 1961435 15912065 := bstep (se 2 (by rfl) ⟨5967024, by rfl⟩ : syracuseStep 15912065 = 11934049) B11934049
theorem B42432173 : Blo 1961435 42432173 := bstep (se 3 (by rfl) ⟨7956032, by rfl⟩ : syracuseStep 42432173 = 15912065) B15912065
theorem B28288115 : Blo 1961435 28288115 := bstep (se 1 (by rfl) ⟨21216086, by rfl⟩ : syracuseStep 28288115 = 42432173) B42432173
theorem B18858743 : Blo 1961435 18858743 := bstep (se 1 (by rfl) ⟨14144057, by rfl⟩ : syracuseStep 18858743 = 28288115) B28288115
theorem B12572495 : Blo 1961435 12572495 := bstep (se 1 (by rfl) ⟨9429371, by rfl⟩ : syracuseStep 12572495 = 18858743) B18858743
theorem B8381663 : Blo 1961435 8381663 := bstep (se 1 (by rfl) ⟨6286247, by rfl⟩ : syracuseStep 8381663 = 12572495) B12572495
theorem B5587775 : Blo 1961435 5587775 := bstep (se 1 (by rfl) ⟨4190831, by rfl⟩ : syracuseStep 5587775 = 8381663) B8381663
theorem B3725183 : Blo 1961435 3725183 := bstep (se 1 (by rfl) ⟨2793887, by rfl⟩ : syracuseStep 3725183 = 5587775) B5587775
theorem B2483455 : Blo 1961435 2483455 := bstep (se 1 (by rfl) ⟨1862591, by rfl⟩ : syracuseStep 2483455 = 3725183) B3725183
theorem B3311273 : Blo 1961435 3311273 := bstep (se 2 (by rfl) ⟨1241727, by rfl⟩ : syracuseStep 3311273 = 2483455) B2483455
theorem B2207515 : Blo 1961435 2207515 := bstep (se 1 (by rfl) ⟨1655636, by rfl⟩ : syracuseStep 2207515 = 3311273) B3311273
theorem B2943353 : Blo 1961435 2943353 := bstep (se 2 (by rfl) ⟨1103757, by rfl⟩ : syracuseStep 2943353 = 2207515) B2207515
theorem B1962235 : Blo 1961435 1962235 := bstep (se 1 (by rfl) ⟨1471676, by rfl⟩ : syracuseStep 1962235 = 2943353) B2943353
theorem B3536021 : Blo 1961435 3536021 := bbase (se 6 (by rfl) ⟨82875, by rfl⟩ : syracuseStep 3536021 = 165751) (by norm_num)
theorem B2357347 : Blo 1961435 2357347 := bstep (se 1 (by rfl) ⟨1768010, by rfl⟩ : syracuseStep 2357347 = 3536021) B3536021
theorem B3143129 : Blo 1961435 3143129 := bstep (se 2 (by rfl) ⟨1178673, by rfl⟩ : syracuseStep 3143129 = 2357347) B2357347
theorem B33526709 : Blo 1961435 33526709 := bstep (se 5 (by rfl) ⟨1571564, by rfl⟩ : syracuseStep 33526709 = 3143129) B3143129
theorem B22351139 : Blo 1961435 22351139 := bstep (se 1 (by rfl) ⟨16763354, by rfl⟩ : syracuseStep 22351139 = 33526709) B33526709
theorem B14900759 : Blo 1961435 14900759 := bstep (se 1 (by rfl) ⟨11175569, by rfl⟩ : syracuseStep 14900759 = 22351139) B22351139
theorem B9933839 : Blo 1961435 9933839 := bstep (se 1 (by rfl) ⟨7450379, by rfl⟩ : syracuseStep 9933839 = 14900759) B14900759
theorem B6622559 : Blo 1961435 6622559 := bstep (se 1 (by rfl) ⟨4966919, by rfl⟩ : syracuseStep 6622559 = 9933839) B9933839
theorem B4415039 : Blo 1961435 4415039 := bstep (se 1 (by rfl) ⟨3311279, by rfl⟩ : syracuseStep 4415039 = 6622559) B6622559
theorem B2943359 : Blo 1961435 2943359 := bstep (se 1 (by rfl) ⟨2207519, by rfl⟩ : syracuseStep 2943359 = 4415039) B4415039
theorem B1962239 : Blo 1961435 1962239 := bstep (se 1 (by rfl) ⟨1471679, by rfl⟩ : syracuseStep 1962239 = 2943359) B2943359
theorem B2943365 : Blo 1961435 2943365 := bbase (se 4 (by rfl) ⟨275940, by rfl⟩ : syracuseStep 2943365 = 551881) (by norm_num)
theorem B1962243 : Blo 1961435 1962243 := bstep (se 1 (by rfl) ⟨1471682, by rfl⟩ : syracuseStep 1962243 = 2943365) B2943365
theorem B3311293 : Blo 1961435 3311293 := bbase (se 3 (by rfl) ⟨620867, by rfl⟩ : syracuseStep 3311293 = 1241735) (by norm_num)
theorem B4415057 : Blo 1961435 4415057 := bstep (se 2 (by rfl) ⟨1655646, by rfl⟩ : syracuseStep 4415057 = 3311293) B3311293
theorem B2943371 : Blo 1961435 2943371 := bstep (se 1 (by rfl) ⟨2207528, by rfl⟩ : syracuseStep 2943371 = 4415057) B4415057
theorem B1962247 : Blo 1961435 1962247 := bstep (se 1 (by rfl) ⟨1471685, by rfl⟩ : syracuseStep 1962247 = 2943371) B2943371
theorem B2207533 : Blo 1961435 2207533 := bbase (se 3 (by rfl) ⟨413912, by rfl⟩ : syracuseStep 2207533 = 827825) (by norm_num)
theorem B2943377 : Blo 1961435 2943377 := bstep (se 2 (by rfl) ⟨1103766, by rfl⟩ : syracuseStep 2943377 = 2207533) B2207533
theorem B1962251 : Blo 1961435 1962251 := bstep (se 1 (by rfl) ⟨1471688, by rfl⟩ : syracuseStep 1962251 = 2943377) B2943377
theorem B6622613 : Blo 1961435 6622613 := bbase (se 6 (by rfl) ⟨155217, by rfl⟩ : syracuseStep 6622613 = 310435) (by norm_num)
theorem B4415075 : Blo 1961435 4415075 := bstep (se 1 (by rfl) ⟨3311306, by rfl⟩ : syracuseStep 4415075 = 6622613) B6622613
theorem B2943383 : Blo 1961435 2943383 := bstep (se 1 (by rfl) ⟨2207537, by rfl⟩ : syracuseStep 2943383 = 4415075) B4415075
theorem B1962255 : Blo 1961435 1962255 := bstep (se 1 (by rfl) ⟨1471691, by rfl⟩ : syracuseStep 1962255 = 2943383) B2943383
theorem B2943389 : Blo 1961435 2943389 := bbase (se 3 (by rfl) ⟨551885, by rfl⟩ : syracuseStep 2943389 = 1103771) (by norm_num)
theorem B1962259 : Blo 1961435 1962259 := bstep (se 1 (by rfl) ⟨1471694, by rfl⟩ : syracuseStep 1962259 = 2943389) B2943389
theorem B4415093 : Blo 1961435 4415093 := bbase (se 5 (by rfl) ⟨206957, by rfl⟩ : syracuseStep 4415093 = 413915) (by norm_num)
theorem B2943395 : Blo 1961435 2943395 := bstep (se 1 (by rfl) ⟨2207546, by rfl⟩ : syracuseStep 2943395 = 4415093) B4415093
theorem B1962263 : Blo 1961435 1962263 := bstep (se 1 (by rfl) ⟨1471697, by rfl⟩ : syracuseStep 1962263 = 2943395) B2943395
theorem B2357381 : Blo 1961435 2357381 := bbase (se 4 (by rfl) ⟨221004, by rfl⟩ : syracuseStep 2357381 = 442009) (by norm_num)
theorem B6286349 : Blo 1961435 6286349 := bstep (se 3 (by rfl) ⟨1178690, by rfl⟩ : syracuseStep 6286349 = 2357381) B2357381
theorem B16763597 : Blo 1961435 16763597 := bstep (se 3 (by rfl) ⟨3143174, by rfl⟩ : syracuseStep 16763597 = 6286349) B6286349
theorem B11175731 : Blo 1961435 11175731 := bstep (se 1 (by rfl) ⟨8381798, by rfl⟩ : syracuseStep 11175731 = 16763597) B16763597
theorem B7450487 : Blo 1961435 7450487 := bstep (se 1 (by rfl) ⟨5587865, by rfl⟩ : syracuseStep 7450487 = 11175731) B11175731
theorem B4966991 : Blo 1961435 4966991 := bstep (se 1 (by rfl) ⟨3725243, by rfl⟩ : syracuseStep 4966991 = 7450487) B7450487
theorem B3311327 : Blo 1961435 3311327 := bstep (se 1 (by rfl) ⟨2483495, by rfl⟩ : syracuseStep 3311327 = 4966991) B4966991
theorem B2207551 : Blo 1961435 2207551 := bstep (se 1 (by rfl) ⟨1655663, by rfl⟩ : syracuseStep 2207551 = 3311327) B3311327
theorem B2943401 : Blo 1961435 2943401 := bstep (se 2 (by rfl) ⟨1103775, by rfl⟩ : syracuseStep 2943401 = 2207551) B2207551
theorem B1962267 : Blo 1961435 1962267 := bstep (se 1 (by rfl) ⟨1471700, by rfl⟩ : syracuseStep 1962267 = 2943401) B2943401
theorem B7450501 : Blo 1961435 7450501 := bbase (se 4 (by rfl) ⟨698484, by rfl⟩ : syracuseStep 7450501 = 1396969) (by norm_num)
theorem B9934001 : Blo 1961435 9934001 := bstep (se 2 (by rfl) ⟨3725250, by rfl⟩ : syracuseStep 9934001 = 7450501) B7450501
theorem B6622667 : Blo 1961435 6622667 := bstep (se 1 (by rfl) ⟨4967000, by rfl⟩ : syracuseStep 6622667 = 9934001) B9934001
theorem B4415111 : Blo 1961435 4415111 := bstep (se 1 (by rfl) ⟨3311333, by rfl⟩ : syracuseStep 4415111 = 6622667) B6622667
theorem B2943407 : Blo 1961435 2943407 := bstep (se 1 (by rfl) ⟨2207555, by rfl⟩ : syracuseStep 2943407 = 4415111) B4415111
theorem B1962271 : Blo 1961435 1962271 := bstep (se 1 (by rfl) ⟨1471703, by rfl⟩ : syracuseStep 1962271 = 2943407) B2943407
theorem B2943413 : Blo 1961435 2943413 := bbase (se 5 (by rfl) ⟨137972, by rfl⟩ : syracuseStep 2943413 = 275945) (by norm_num)
theorem B1962275 : Blo 1961435 1962275 := bstep (se 1 (by rfl) ⟨1471706, by rfl⟩ : syracuseStep 1962275 = 2943413) B2943413
theorem B4967021 : Blo 1961435 4967021 := bbase (se 3 (by rfl) ⟨931316, by rfl⟩ : syracuseStep 4967021 = 1862633) (by norm_num)
theorem B3311347 : Blo 1961435 3311347 := bstep (se 1 (by rfl) ⟨2483510, by rfl⟩ : syracuseStep 3311347 = 4967021) B4967021
theorem B4415129 : Blo 1961435 4415129 := bstep (se 2 (by rfl) ⟨1655673, by rfl⟩ : syracuseStep 4415129 = 3311347) B3311347
theorem B2943419 : Blo 1961435 2943419 := bstep (se 1 (by rfl) ⟨2207564, by rfl⟩ : syracuseStep 2943419 = 4415129) B4415129
theorem B1962279 : Blo 1961435 1962279 := bstep (se 1 (by rfl) ⟨1471709, by rfl⟩ : syracuseStep 1962279 = 2943419) B2943419
theorem B2207569 : Blo 1961435 2207569 := bbase (se 2 (by rfl) ⟨827838, by rfl⟩ : syracuseStep 2207569 = 1655677) (by norm_num)
theorem B2943425 : Blo 1961435 2943425 := bstep (se 2 (by rfl) ⟨1103784, by rfl⟩ : syracuseStep 2943425 = 2207569) B2207569
theorem B1962283 : Blo 1961435 1962283 := bstep (se 1 (by rfl) ⟨1471712, by rfl⟩ : syracuseStep 1962283 = 2943425) B2943425
theorem B7956245 : Blo 1961435 7956245 := bbase (se 6 (by rfl) ⟨186474, by rfl⟩ : syracuseStep 7956245 = 372949) (by norm_num)
theorem B5304163 : Blo 1961435 5304163 := bstep (se 1 (by rfl) ⟨3978122, by rfl⟩ : syracuseStep 5304163 = 7956245) B7956245
theorem B7072217 : Blo 1961435 7072217 := bstep (se 2 (by rfl) ⟨2652081, by rfl⟩ : syracuseStep 7072217 = 5304163) B5304163
theorem B4714811 : Blo 1961435 4714811 := bstep (se 1 (by rfl) ⟨3536108, by rfl⟩ : syracuseStep 4714811 = 7072217) B7072217
theorem B3143207 : Blo 1961435 3143207 := bstep (se 1 (by rfl) ⟨2357405, by rfl⟩ : syracuseStep 3143207 = 4714811) B4714811
theorem B2095471 : Blo 1961435 2095471 := bstep (se 1 (by rfl) ⟨1571603, by rfl⟩ : syracuseStep 2095471 = 3143207) B3143207
theorem B2793961 : Blo 1961435 2793961 := bstep (se 2 (by rfl) ⟨1047735, by rfl⟩ : syracuseStep 2793961 = 2095471) B2095471
theorem B3725281 : Blo 1961435 3725281 := bstep (se 2 (by rfl) ⟨1396980, by rfl⟩ : syracuseStep 3725281 = 2793961) B2793961
theorem B4967041 : Blo 1961435 4967041 := bstep (se 2 (by rfl) ⟨1862640, by rfl⟩ : syracuseStep 4967041 = 3725281) B3725281
theorem B6622721 : Blo 1961435 6622721 := bstep (se 2 (by rfl) ⟨2483520, by rfl⟩ : syracuseStep 6622721 = 4967041) B4967041
theorem B4415147 : Blo 1961435 4415147 := bstep (se 1 (by rfl) ⟨3311360, by rfl⟩ : syracuseStep 4415147 = 6622721) B6622721
theorem B2943431 : Blo 1961435 2943431 := bstep (se 1 (by rfl) ⟨2207573, by rfl⟩ : syracuseStep 2943431 = 4415147) B4415147
theorem B1962287 : Blo 1961435 1962287 := bstep (se 1 (by rfl) ⟨1471715, by rfl⟩ : syracuseStep 1962287 = 2943431) B2943431
theorem B2943437 : Blo 1961435 2943437 := bbase (se 3 (by rfl) ⟨551894, by rfl⟩ : syracuseStep 2943437 = 1103789) (by norm_num)
theorem B1962291 : Blo 1961435 1962291 := bstep (se 1 (by rfl) ⟨1471718, by rfl⟩ : syracuseStep 1962291 = 2943437) B2943437
theorem B4415165 : Blo 1961435 4415165 := bbase (se 3 (by rfl) ⟨827843, by rfl⟩ : syracuseStep 4415165 = 1655687) (by norm_num)
theorem B2943443 : Blo 1961435 2943443 := bstep (se 1 (by rfl) ⟨2207582, by rfl⟩ : syracuseStep 2943443 = 4415165) B4415165
theorem B1962295 : Blo 1961435 1962295 := bstep (se 1 (by rfl) ⟨1471721, by rfl⟩ : syracuseStep 1962295 = 2943443) B2943443
theorem B3311381 : Blo 1961435 3311381 := bbase (se 6 (by rfl) ⟨77610, by rfl⟩ : syracuseStep 3311381 = 155221) (by norm_num)
theorem B2207587 : Blo 1961435 2207587 := bstep (se 1 (by rfl) ⟨1655690, by rfl⟩ : syracuseStep 2207587 = 3311381) B3311381
theorem B2943449 : Blo 1961435 2943449 := bstep (se 2 (by rfl) ⟨1103793, by rfl⟩ : syracuseStep 2943449 = 2207587) B2207587
theorem B1962299 : Blo 1961435 1962299 := bstep (se 1 (by rfl) ⟨1471724, by rfl⟩ : syracuseStep 1962299 = 2943449) B2943449
theorem B135940949 : Blo 1961435 135940949 := bbase (se 9 (by rfl) ⟨398264, by rfl⟩ : syracuseStep 135940949 = 796529) (by norm_num)
theorem B90627299 : Blo 1961435 90627299 := bstep (se 1 (by rfl) ⟨67970474, by rfl⟩ : syracuseStep 90627299 = 135940949) B135940949
theorem B60418199 : Blo 1961435 60418199 := bstep (se 1 (by rfl) ⟨45313649, by rfl⟩ : syracuseStep 60418199 = 90627299) B90627299
theorem B40278799 : Blo 1961435 40278799 := bstep (se 1 (by rfl) ⟨30209099, by rfl⟩ : syracuseStep 40278799 = 60418199) B60418199
theorem B214820261 : Blo 1961435 214820261 := bstep (se 4 (by rfl) ⟨20139399, by rfl⟩ : syracuseStep 214820261 = 40278799) B40278799
theorem B143213507 : Blo 1961435 143213507 := bstep (se 1 (by rfl) ⟨107410130, by rfl⟩ : syracuseStep 143213507 = 214820261) B214820261
theorem B95475671 : Blo 1961435 95475671 := bstep (se 1 (by rfl) ⟨71606753, by rfl⟩ : syracuseStep 95475671 = 143213507) B143213507
theorem B63650447 : Blo 1961435 63650447 := bstep (se 1 (by rfl) ⟨47737835, by rfl⟩ : syracuseStep 63650447 = 95475671) B95475671
theorem B42433631 : Blo 1961435 42433631 := bstep (se 1 (by rfl) ⟨31825223, by rfl⟩ : syracuseStep 42433631 = 63650447) B63650447
theorem B28289087 : Blo 1961435 28289087 := bstep (se 1 (by rfl) ⟨21216815, by rfl⟩ : syracuseStep 28289087 = 42433631) B42433631
theorem B18859391 : Blo 1961435 18859391 := bstep (se 1 (by rfl) ⟨14144543, by rfl⟩ : syracuseStep 18859391 = 28289087) B28289087
theorem B12572927 : Blo 1961435 12572927 := bstep (se 1 (by rfl) ⟨9429695, by rfl⟩ : syracuseStep 12572927 = 18859391) B18859391
theorem B8381951 : Blo 1961435 8381951 := bstep (se 1 (by rfl) ⟨6286463, by rfl⟩ : syracuseStep 8381951 = 12572927) B12572927
theorem B5587967 : Blo 1961435 5587967 := bstep (se 1 (by rfl) ⟨4190975, by rfl⟩ : syracuseStep 5587967 = 8381951) B8381951
theorem B14901245 : Blo 1961435 14901245 := bstep (se 3 (by rfl) ⟨2793983, by rfl⟩ : syracuseStep 14901245 = 5587967) B5587967
theorem B9934163 : Blo 1961435 9934163 := bstep (se 1 (by rfl) ⟨7450622, by rfl⟩ : syracuseStep 9934163 = 14901245) B14901245
theorem B6622775 : Blo 1961435 6622775 := bstep (se 1 (by rfl) ⟨4967081, by rfl⟩ : syracuseStep 6622775 = 9934163) B9934163
theorem B4415183 : Blo 1961435 4415183 := bstep (se 1 (by rfl) ⟨3311387, by rfl⟩ : syracuseStep 4415183 = 6622775) B6622775
theorem B2943455 : Blo 1961435 2943455 := bstep (se 1 (by rfl) ⟨2207591, by rfl⟩ : syracuseStep 2943455 = 4415183) B4415183
theorem B1962303 : Blo 1961435 1962303 := bstep (se 1 (by rfl) ⟨1471727, by rfl⟩ : syracuseStep 1962303 = 2943455) B2943455
theorem B2943461 : Blo 1961435 2943461 := bbase (se 4 (by rfl) ⟨275949, by rfl⟩ : syracuseStep 2943461 = 551899) (by norm_num)
theorem B1962307 : Blo 1961435 1962307 := bstep (se 1 (by rfl) ⟨1471730, by rfl⟩ : syracuseStep 1962307 = 2943461) B2943461
theorem B12572981 : Blo 1961435 12572981 := bbase (se 5 (by rfl) ⟨589358, by rfl⟩ : syracuseStep 12572981 = 1178717) (by norm_num)
theorem B8381987 : Blo 1961435 8381987 := bstep (se 1 (by rfl) ⟨6286490, by rfl⟩ : syracuseStep 8381987 = 12572981) B12572981
theorem B5587991 : Blo 1961435 5587991 := bstep (se 1 (by rfl) ⟨4190993, by rfl⟩ : syracuseStep 5587991 = 8381987) B8381987
theorem B3725327 : Blo 1961435 3725327 := bstep (se 1 (by rfl) ⟨2793995, by rfl⟩ : syracuseStep 3725327 = 5587991) B5587991
theorem B2483551 : Blo 1961435 2483551 := bstep (se 1 (by rfl) ⟨1862663, by rfl⟩ : syracuseStep 2483551 = 3725327) B3725327
theorem B3311401 : Blo 1961435 3311401 := bstep (se 2 (by rfl) ⟨1241775, by rfl⟩ : syracuseStep 3311401 = 2483551) B2483551
theorem B4415201 : Blo 1961435 4415201 := bstep (se 2 (by rfl) ⟨1655700, by rfl⟩ : syracuseStep 4415201 = 3311401) B3311401
theorem B2943467 : Blo 1961435 2943467 := bstep (se 1 (by rfl) ⟨2207600, by rfl⟩ : syracuseStep 2943467 = 4415201) B4415201
theorem B1962311 : Blo 1961435 1962311 := bstep (se 1 (by rfl) ⟨1471733, by rfl⟩ : syracuseStep 1962311 = 2943467) B2943467
theorem B2207605 : Blo 1961435 2207605 := bbase (se 5 (by rfl) ⟨103481, by rfl⟩ : syracuseStep 2207605 = 206963) (by norm_num)
theorem B2943473 : Blo 1961435 2943473 := bstep (se 2 (by rfl) ⟨1103802, by rfl⟩ : syracuseStep 2943473 = 2207605) B2207605
theorem B1962315 : Blo 1961435 1962315 := bstep (se 1 (by rfl) ⟨1471736, by rfl⟩ : syracuseStep 1962315 = 2943473) B2943473
theorem B2483561 : Blo 1961435 2483561 := bbase (se 2 (by rfl) ⟨931335, by rfl⟩ : syracuseStep 2483561 = 1862671) (by norm_num)
theorem B6622829 : Blo 1961435 6622829 := bstep (se 3 (by rfl) ⟨1241780, by rfl⟩ : syracuseStep 6622829 = 2483561) B2483561
theorem B4415219 : Blo 1961435 4415219 := bstep (se 1 (by rfl) ⟨3311414, by rfl⟩ : syracuseStep 4415219 = 6622829) B6622829
theorem B2943479 : Blo 1961435 2943479 := bstep (se 1 (by rfl) ⟨2207609, by rfl⟩ : syracuseStep 2943479 = 4415219) B4415219
theorem B1962319 : Blo 1961435 1962319 := bstep (se 1 (by rfl) ⟨1471739, by rfl⟩ : syracuseStep 1962319 = 2943479) B2943479
theorem B2943485 : Blo 1961435 2943485 := bbase (se 3 (by rfl) ⟨551903, by rfl⟩ : syracuseStep 2943485 = 1103807) (by norm_num)
theorem B1962323 : Blo 1961435 1962323 := bstep (se 1 (by rfl) ⟨1471742, by rfl⟩ : syracuseStep 1962323 = 2943485) B2943485
theorem B4415237 : Blo 1961435 4415237 := bbase (se 4 (by rfl) ⟨413928, by rfl⟩ : syracuseStep 4415237 = 827857) (by norm_num)
theorem B2943491 : Blo 1961435 2943491 := bstep (se 1 (by rfl) ⟨2207618, by rfl⟩ : syracuseStep 2943491 = 4415237) B4415237
theorem B1962327 : Blo 1961435 1962327 := bstep (se 1 (by rfl) ⟨1471745, by rfl⟩ : syracuseStep 1962327 = 2943491) B2943491
theorem B3725365 : Blo 1961435 3725365 := bbase (se 5 (by rfl) ⟨174626, by rfl⟩ : syracuseStep 3725365 = 349253) (by norm_num)
theorem B4967153 : Blo 1961435 4967153 := bstep (se 2 (by rfl) ⟨1862682, by rfl⟩ : syracuseStep 4967153 = 3725365) B3725365
theorem B3311435 : Blo 1961435 3311435 := bstep (se 1 (by rfl) ⟨2483576, by rfl⟩ : syracuseStep 3311435 = 4967153) B4967153
theorem B2207623 : Blo 1961435 2207623 := bstep (se 1 (by rfl) ⟨1655717, by rfl⟩ : syracuseStep 2207623 = 3311435) B3311435
theorem B2943497 : Blo 1961435 2943497 := bstep (se 2 (by rfl) ⟨1103811, by rfl⟩ : syracuseStep 2943497 = 2207623) B2207623
theorem B1962331 : Blo 1961435 1962331 := bstep (se 1 (by rfl) ⟨1471748, by rfl⟩ : syracuseStep 1962331 = 2943497) B2943497
theorem B9934325 : Blo 1961435 9934325 := bbase (se 5 (by rfl) ⟨465671, by rfl⟩ : syracuseStep 9934325 = 931343) (by norm_num)
theorem B6622883 : Blo 1961435 6622883 := bstep (se 1 (by rfl) ⟨4967162, by rfl⟩ : syracuseStep 6622883 = 9934325) B9934325
theorem B4415255 : Blo 1961435 4415255 := bstep (se 1 (by rfl) ⟨3311441, by rfl⟩ : syracuseStep 4415255 = 6622883) B6622883
theorem B2943503 : Blo 1961435 2943503 := bstep (se 1 (by rfl) ⟨2207627, by rfl⟩ : syracuseStep 2943503 = 4415255) B4415255
theorem B1962335 : Blo 1961435 1962335 := bstep (se 1 (by rfl) ⟨1471751, by rfl⟩ : syracuseStep 1962335 = 2943503) B2943503
theorem B2943509 : Blo 1961435 2943509 := bbase (se 6 (by rfl) ⟨68988, by rfl⟩ : syracuseStep 2943509 = 137977) (by norm_num)
theorem B1962339 : Blo 1961435 1962339 := bstep (se 1 (by rfl) ⟨1471754, by rfl⟩ : syracuseStep 1962339 = 2943509) B2943509
theorem B16764245 : Blo 1961435 16764245 := bbase (se 11 (by rfl) ⟨12278, by rfl⟩ : syracuseStep 16764245 = 24557) (by norm_num)
theorem B11176163 : Blo 1961435 11176163 := bstep (se 1 (by rfl) ⟨8382122, by rfl⟩ : syracuseStep 11176163 = 16764245) B16764245
theorem B7450775 : Blo 1961435 7450775 := bstep (se 1 (by rfl) ⟨5588081, by rfl⟩ : syracuseStep 7450775 = 11176163) B11176163
theorem B4967183 : Blo 1961435 4967183 := bstep (se 1 (by rfl) ⟨3725387, by rfl⟩ : syracuseStep 4967183 = 7450775) B7450775
theorem B3311455 : Blo 1961435 3311455 := bstep (se 1 (by rfl) ⟨2483591, by rfl⟩ : syracuseStep 3311455 = 4967183) B4967183
theorem B4415273 : Blo 1961435 4415273 := bstep (se 2 (by rfl) ⟨1655727, by rfl⟩ : syracuseStep 4415273 = 3311455) B3311455
theorem B2943515 : Blo 1961435 2943515 := bstep (se 1 (by rfl) ⟨2207636, by rfl⟩ : syracuseStep 2943515 = 4415273) B4415273
theorem B1962343 : Blo 1961435 1962343 := bstep (se 1 (by rfl) ⟨1471757, by rfl⟩ : syracuseStep 1962343 = 2943515) B2943515
theorem B2207641 : Blo 1961435 2207641 := bbase (se 2 (by rfl) ⟨827865, by rfl⟩ : syracuseStep 2207641 = 1655731) (by norm_num)
theorem B2943521 : Blo 1961435 2943521 := bstep (se 2 (by rfl) ⟨1103820, by rfl⟩ : syracuseStep 2943521 = 2207641) B2207641
theorem B1962347 : Blo 1961435 1962347 := bstep (se 1 (by rfl) ⟨1471760, by rfl⟩ : syracuseStep 1962347 = 2943521) B2943521
theorem B7450805 : Blo 1961435 7450805 := bbase (se 5 (by rfl) ⟨349256, by rfl⟩ : syracuseStep 7450805 = 698513) (by norm_num)
theorem B4967203 : Blo 1961435 4967203 := bstep (se 1 (by rfl) ⟨3725402, by rfl⟩ : syracuseStep 4967203 = 7450805) B7450805
theorem B6622937 : Blo 1961435 6622937 := bstep (se 2 (by rfl) ⟨2483601, by rfl⟩ : syracuseStep 6622937 = 4967203) B4967203
theorem B4415291 : Blo 1961435 4415291 := bstep (se 1 (by rfl) ⟨3311468, by rfl⟩ : syracuseStep 4415291 = 6622937) B6622937
theorem B2943527 : Blo 1961435 2943527 := bstep (se 1 (by rfl) ⟨2207645, by rfl⟩ : syracuseStep 2943527 = 4415291) B4415291
theorem B1962351 : Blo 1961435 1962351 := bstep (se 1 (by rfl) ⟨1471763, by rfl⟩ : syracuseStep 1962351 = 2943527) B2943527
theorem B2943533 : Blo 1961435 2943533 := bbase (se 3 (by rfl) ⟨551912, by rfl⟩ : syracuseStep 2943533 = 1103825) (by norm_num)
theorem B1962355 : Blo 1961435 1962355 := bstep (se 1 (by rfl) ⟨1471766, by rfl⟩ : syracuseStep 1962355 = 2943533) B2943533
theorem B4415309 : Blo 1961435 4415309 := bbase (se 3 (by rfl) ⟨827870, by rfl⟩ : syracuseStep 4415309 = 1655741) (by norm_num)
theorem B2943539 : Blo 1961435 2943539 := bstep (se 1 (by rfl) ⟨2207654, by rfl⟩ : syracuseStep 2943539 = 4415309) B4415309
theorem B1962359 : Blo 1961435 1962359 := bstep (se 1 (by rfl) ⟨1471769, by rfl⟩ : syracuseStep 1962359 = 2943539) B2943539
theorem B2483617 : Blo 1961435 2483617 := bbase (se 2 (by rfl) ⟨931356, by rfl⟩ : syracuseStep 2483617 = 1862713) (by norm_num)
theorem B3311489 : Blo 1961435 3311489 := bstep (se 2 (by rfl) ⟨1241808, by rfl⟩ : syracuseStep 3311489 = 2483617) B2483617
theorem B2207659 : Blo 1961435 2207659 := bstep (se 1 (by rfl) ⟨1655744, by rfl⟩ : syracuseStep 2207659 = 3311489) B3311489
theorem B2943545 : Blo 1961435 2943545 := bstep (se 2 (by rfl) ⟨1103829, by rfl⟩ : syracuseStep 2943545 = 2207659) B2207659
theorem B1962363 : Blo 1961435 1962363 := bstep (se 1 (by rfl) ⟨1471772, by rfl⟩ : syracuseStep 1962363 = 2943545) B2943545
theorem B22352597 : Blo 1961435 22352597 := bbase (se 7 (by rfl) ⟨261944, by rfl⟩ : syracuseStep 22352597 = 523889) (by norm_num)
theorem B14901731 : Blo 1961435 14901731 := bstep (se 1 (by rfl) ⟨11176298, by rfl⟩ : syracuseStep 14901731 = 22352597) B22352597
theorem B9934487 : Blo 1961435 9934487 := bstep (se 1 (by rfl) ⟨7450865, by rfl⟩ : syracuseStep 9934487 = 14901731) B14901731
theorem B6622991 : Blo 1961435 6622991 := bstep (se 1 (by rfl) ⟨4967243, by rfl⟩ : syracuseStep 6622991 = 9934487) B9934487
theorem B4415327 : Blo 1961435 4415327 := bstep (se 1 (by rfl) ⟨3311495, by rfl⟩ : syracuseStep 4415327 = 6622991) B6622991
theorem B2943551 : Blo 1961435 2943551 := bstep (se 1 (by rfl) ⟨2207663, by rfl⟩ : syracuseStep 2943551 = 4415327) B4415327
theorem B1962367 : Blo 1961435 1962367 := bstep (se 1 (by rfl) ⟨1471775, by rfl⟩ : syracuseStep 1962367 = 2943551) B2943551
theorem B2943557 : Blo 1961435 2943557 := bbase (se 4 (by rfl) ⟨275958, by rfl⟩ : syracuseStep 2943557 = 551917) (by norm_num)
theorem B1962371 : Blo 1961435 1962371 := bstep (se 1 (by rfl) ⟨1471778, by rfl⟩ : syracuseStep 1962371 = 2943557) B2943557
theorem B3311509 : Blo 1961435 3311509 := bbase (se 6 (by rfl) ⟨77613, by rfl⟩ : syracuseStep 3311509 = 155227) (by norm_num)
theorem B4415345 : Blo 1961435 4415345 := bstep (se 2 (by rfl) ⟨1655754, by rfl⟩ : syracuseStep 4415345 = 3311509) B3311509
theorem B2943563 : Blo 1961435 2943563 := bstep (se 1 (by rfl) ⟨2207672, by rfl⟩ : syracuseStep 2943563 = 4415345) B4415345
theorem B1962375 : Blo 1961435 1962375 := bstep (se 1 (by rfl) ⟨1471781, by rfl⟩ : syracuseStep 1962375 = 2943563) B2943563
theorem B2207677 : Blo 1961435 2207677 := bbase (se 3 (by rfl) ⟨413939, by rfl⟩ : syracuseStep 2207677 = 827879) (by norm_num)
theorem B2943569 : Blo 1961435 2943569 := bstep (se 2 (by rfl) ⟨1103838, by rfl⟩ : syracuseStep 2943569 = 2207677) B2207677
theorem B1962379 : Blo 1961435 1962379 := bstep (se 1 (by rfl) ⟨1471784, by rfl⟩ : syracuseStep 1962379 = 2943569) B2943569
theorem B6623045 : Blo 1961435 6623045 := bbase (se 4 (by rfl) ⟨620910, by rfl⟩ : syracuseStep 6623045 = 1241821) (by norm_num)
theorem B4415363 : Blo 1961435 4415363 := bstep (se 1 (by rfl) ⟨3311522, by rfl⟩ : syracuseStep 4415363 = 6623045) B6623045
theorem B2943575 : Blo 1961435 2943575 := bstep (se 1 (by rfl) ⟨2207681, by rfl⟩ : syracuseStep 2943575 = 4415363) B4415363
theorem B1962383 : Blo 1961435 1962383 := bstep (se 1 (by rfl) ⟨1471787, by rfl⟩ : syracuseStep 1962383 = 2943575) B2943575
theorem B2943581 : Blo 1961435 2943581 := bbase (se 3 (by rfl) ⟨551921, by rfl⟩ : syracuseStep 2943581 = 1103843) (by norm_num)
theorem B1962387 : Blo 1961435 1962387 := bstep (se 1 (by rfl) ⟨1471790, by rfl⟩ : syracuseStep 1962387 = 2943581) B2943581
theorem B4415381 : Blo 1961435 4415381 := bbase (se 6 (by rfl) ⟨103485, by rfl⟩ : syracuseStep 4415381 = 206971) (by norm_num)
theorem B2943587 : Blo 1961435 2943587 := bstep (se 1 (by rfl) ⟨2207690, by rfl⟩ : syracuseStep 2943587 = 4415381) B4415381
theorem B1962391 : Blo 1961435 1962391 := bstep (se 1 (by rfl) ⟨1471793, by rfl⟩ : syracuseStep 1962391 = 2943587) B2943587
theorem B4191173 : Blo 1961435 4191173 := bbase (se 4 (by rfl) ⟨392922, by rfl⟩ : syracuseStep 4191173 = 785845) (by norm_num)
theorem B2794115 : Blo 1961435 2794115 := bstep (se 1 (by rfl) ⟨2095586, by rfl⟩ : syracuseStep 2794115 = 4191173) B4191173
theorem B7450973 : Blo 1961435 7450973 := bstep (se 3 (by rfl) ⟨1397057, by rfl⟩ : syracuseStep 7450973 = 2794115) B2794115
theorem B4967315 : Blo 1961435 4967315 := bstep (se 1 (by rfl) ⟨3725486, by rfl⟩ : syracuseStep 4967315 = 7450973) B7450973
theorem B3311543 : Blo 1961435 3311543 := bstep (se 1 (by rfl) ⟨2483657, by rfl⟩ : syracuseStep 3311543 = 4967315) B4967315
theorem B2207695 : Blo 1961435 2207695 := bstep (se 1 (by rfl) ⟨1655771, by rfl⟩ : syracuseStep 2207695 = 3311543) B3311543
theorem B2943593 : Blo 1961435 2943593 := bstep (se 2 (by rfl) ⟨1103847, by rfl⟩ : syracuseStep 2943593 = 2207695) B2207695
theorem B1962395 : Blo 1961435 1962395 := bstep (se 1 (by rfl) ⟨1471796, by rfl⟩ : syracuseStep 1962395 = 2943593) B2943593
theorem B3536309 : Blo 1961435 3536309 := bbase (se 5 (by rfl) ⟨165764, by rfl⟩ : syracuseStep 3536309 = 331529) (by norm_num)
theorem B9430157 : Blo 1961435 9430157 := bstep (se 3 (by rfl) ⟨1768154, by rfl⟩ : syracuseStep 9430157 = 3536309) B3536309
theorem B6286771 : Blo 1961435 6286771 := bstep (se 1 (by rfl) ⟨4715078, by rfl⟩ : syracuseStep 6286771 = 9430157) B9430157
theorem B8382361 : Blo 1961435 8382361 := bstep (se 2 (by rfl) ⟨3143385, by rfl⟩ : syracuseStep 8382361 = 6286771) B6286771
theorem B11176481 : Blo 1961435 11176481 := bstep (se 2 (by rfl) ⟨4191180, by rfl⟩ : syracuseStep 11176481 = 8382361) B8382361
theorem B7450987 : Blo 1961435 7450987 := bstep (se 1 (by rfl) ⟨5588240, by rfl⟩ : syracuseStep 7450987 = 11176481) B11176481
theorem B9934649 : Blo 1961435 9934649 := bstep (se 2 (by rfl) ⟨3725493, by rfl⟩ : syracuseStep 9934649 = 7450987) B7450987
theorem B6623099 : Blo 1961435 6623099 := bstep (se 1 (by rfl) ⟨4967324, by rfl⟩ : syracuseStep 6623099 = 9934649) B9934649
theorem B4415399 : Blo 1961435 4415399 := bstep (se 1 (by rfl) ⟨3311549, by rfl⟩ : syracuseStep 4415399 = 6623099) B6623099
theorem B2943599 : Blo 1961435 2943599 := bstep (se 1 (by rfl) ⟨2207699, by rfl⟩ : syracuseStep 2943599 = 4415399) B4415399
theorem B1962399 : Blo 1961435 1962399 := bstep (se 1 (by rfl) ⟨1471799, by rfl⟩ : syracuseStep 1962399 = 2943599) B2943599
theorem B2943605 : Blo 1961435 2943605 := bbase (se 5 (by rfl) ⟨137981, by rfl⟩ : syracuseStep 2943605 = 275963) (by norm_num)
theorem B1962403 : Blo 1961435 1962403 := bstep (se 1 (by rfl) ⟨1471802, by rfl⟩ : syracuseStep 1962403 = 2943605) B2943605
theorem B3725509 : Blo 1961435 3725509 := bbase (se 4 (by rfl) ⟨349266, by rfl⟩ : syracuseStep 3725509 = 698533) (by norm_num)
theorem B4967345 : Blo 1961435 4967345 := bstep (se 2 (by rfl) ⟨1862754, by rfl⟩ : syracuseStep 4967345 = 3725509) B3725509
theorem B3311563 : Blo 1961435 3311563 := bstep (se 1 (by rfl) ⟨2483672, by rfl⟩ : syracuseStep 3311563 = 4967345) B4967345
theorem B4415417 : Blo 1961435 4415417 := bstep (se 2 (by rfl) ⟨1655781, by rfl⟩ : syracuseStep 4415417 = 3311563) B3311563
theorem B2943611 : Blo 1961435 2943611 := bstep (se 1 (by rfl) ⟨2207708, by rfl⟩ : syracuseStep 2943611 = 4415417) B4415417
theorem B1962407 : Blo 1961435 1962407 := bstep (se 1 (by rfl) ⟨1471805, by rfl⟩ : syracuseStep 1962407 = 2943611) B2943611
theorem B2207713 : Blo 1961435 2207713 := bbase (se 2 (by rfl) ⟨827892, by rfl⟩ : syracuseStep 2207713 = 1655785) (by norm_num)
theorem B2943617 : Blo 1961435 2943617 := bstep (se 2 (by rfl) ⟨1103856, by rfl⟩ : syracuseStep 2943617 = 2207713) B2207713
theorem B1962411 : Blo 1961435 1962411 := bstep (se 1 (by rfl) ⟨1471808, by rfl⟩ : syracuseStep 1962411 = 2943617) B2943617
theorem B4967365 : Blo 1961435 4967365 := bbase (se 4 (by rfl) ⟨465690, by rfl⟩ : syracuseStep 4967365 = 931381) (by norm_num)
theorem B6623153 : Blo 1961435 6623153 := bstep (se 2 (by rfl) ⟨2483682, by rfl⟩ : syracuseStep 6623153 = 4967365) B4967365
theorem B4415435 : Blo 1961435 4415435 := bstep (se 1 (by rfl) ⟨3311576, by rfl⟩ : syracuseStep 4415435 = 6623153) B6623153
theorem B2943623 : Blo 1961435 2943623 := bstep (se 1 (by rfl) ⟨2207717, by rfl⟩ : syracuseStep 2943623 = 4415435) B4415435
theorem B1962415 : Blo 1961435 1962415 := bstep (se 1 (by rfl) ⟨1471811, by rfl⟩ : syracuseStep 1962415 = 2943623) B2943623
theorem B2943629 : Blo 1961435 2943629 := bbase (se 3 (by rfl) ⟨551930, by rfl⟩ : syracuseStep 2943629 = 1103861) (by norm_num)
theorem B1962419 : Blo 1961435 1962419 := bstep (se 1 (by rfl) ⟨1471814, by rfl⟩ : syracuseStep 1962419 = 2943629) B2943629
theorem B4415453 : Blo 1961435 4415453 := bbase (se 3 (by rfl) ⟨827897, by rfl⟩ : syracuseStep 4415453 = 1655795) (by norm_num)
theorem B2943635 : Blo 1961435 2943635 := bstep (se 1 (by rfl) ⟨2207726, by rfl⟩ : syracuseStep 2943635 = 4415453) B4415453
theorem B1962423 : Blo 1961435 1962423 := bstep (se 1 (by rfl) ⟨1471817, by rfl⟩ : syracuseStep 1962423 = 2943635) B2943635
theorem B3311597 : Blo 1961435 3311597 := bbase (se 3 (by rfl) ⟨620924, by rfl⟩ : syracuseStep 3311597 = 1241849) (by norm_num)
theorem B2207731 : Blo 1961435 2207731 := bstep (se 1 (by rfl) ⟨1655798, by rfl⟩ : syracuseStep 2207731 = 3311597) B3311597
theorem B2943641 : Blo 1961435 2943641 := bstep (se 2 (by rfl) ⟨1103865, by rfl⟩ : syracuseStep 2943641 = 2207731) B2207731
theorem B1962427 : Blo 1961435 1962427 := bstep (se 1 (by rfl) ⟨1471820, by rfl⟩ : syracuseStep 1962427 = 2943641) B2943641
theorem B3978413 : Blo 1961435 3978413 := bbase (se 3 (by rfl) ⟨745952, by rfl⟩ : syracuseStep 3978413 = 1491905) (by norm_num)
theorem B2652275 : Blo 1961435 2652275 := bstep (se 1 (by rfl) ⟨1989206, by rfl⟩ : syracuseStep 2652275 = 3978413) B3978413
theorem B7072733 : Blo 1961435 7072733 := bstep (se 3 (by rfl) ⟨1326137, by rfl⟩ : syracuseStep 7072733 = 2652275) B2652275
theorem B4715155 : Blo 1961435 4715155 := bstep (se 1 (by rfl) ⟨3536366, by rfl⟩ : syracuseStep 4715155 = 7072733) B7072733
theorem B25147493 : Blo 1961435 25147493 := bstep (se 4 (by rfl) ⟨2357577, by rfl⟩ : syracuseStep 25147493 = 4715155) B4715155
theorem B16764995 : Blo 1961435 16764995 := bstep (se 1 (by rfl) ⟨12573746, by rfl⟩ : syracuseStep 16764995 = 25147493) B25147493
theorem B11176663 : Blo 1961435 11176663 := bstep (se 1 (by rfl) ⟨8382497, by rfl⟩ : syracuseStep 11176663 = 16764995) B16764995
theorem B14902217 : Blo 1961435 14902217 := bstep (se 2 (by rfl) ⟨5588331, by rfl⟩ : syracuseStep 14902217 = 11176663) B11176663
theorem B9934811 : Blo 1961435 9934811 := bstep (se 1 (by rfl) ⟨7451108, by rfl⟩ : syracuseStep 9934811 = 14902217) B14902217
theorem B6623207 : Blo 1961435 6623207 := bstep (se 1 (by rfl) ⟨4967405, by rfl⟩ : syracuseStep 6623207 = 9934811) B9934811
theorem B4415471 : Blo 1961435 4415471 := bstep (se 1 (by rfl) ⟨3311603, by rfl⟩ : syracuseStep 4415471 = 6623207) B6623207
theorem B2943647 : Blo 1961435 2943647 := bstep (se 1 (by rfl) ⟨2207735, by rfl⟩ : syracuseStep 2943647 = 4415471) B4415471
theorem B1962431 : Blo 1961435 1962431 := bstep (se 1 (by rfl) ⟨1471823, by rfl⟩ : syracuseStep 1962431 = 2943647) B2943647
theorem B2943653 : Blo 1961435 2943653 := bbase (se 4 (by rfl) ⟨275967, by rfl⟩ : syracuseStep 2943653 = 551935) (by norm_num)
theorem B1962435 : Blo 1961435 1962435 := bstep (se 1 (by rfl) ⟨1471826, by rfl⟩ : syracuseStep 1962435 = 2943653) B2943653
theorem B2483713 : Blo 1961435 2483713 := bbase (se 2 (by rfl) ⟨931392, by rfl⟩ : syracuseStep 2483713 = 1862785) (by norm_num)
theorem B3311617 : Blo 1961435 3311617 := bstep (se 2 (by rfl) ⟨1241856, by rfl⟩ : syracuseStep 3311617 = 2483713) B2483713
theorem B4415489 : Blo 1961435 4415489 := bstep (se 2 (by rfl) ⟨1655808, by rfl⟩ : syracuseStep 4415489 = 3311617) B3311617
theorem B2943659 : Blo 1961435 2943659 := bstep (se 1 (by rfl) ⟨2207744, by rfl⟩ : syracuseStep 2943659 = 4415489) B4415489
theorem B1962439 : Blo 1961435 1962439 := bstep (se 1 (by rfl) ⟨1471829, by rfl⟩ : syracuseStep 1962439 = 2943659) B2943659
theorem B2207749 : Blo 1961435 2207749 := bbase (se 4 (by rfl) ⟨206976, by rfl⟩ : syracuseStep 2207749 = 413953) (by norm_num)
theorem B2943665 : Blo 1961435 2943665 := bstep (se 2 (by rfl) ⟨1103874, by rfl⟩ : syracuseStep 2943665 = 2207749) B2207749
theorem B1962443 : Blo 1961435 1962443 := bstep (se 1 (by rfl) ⟨1471832, by rfl⟩ : syracuseStep 1962443 = 2943665) B2943665
theorem B2794189 : Blo 1961435 2794189 := bbase (se 3 (by rfl) ⟨523910, by rfl⟩ : syracuseStep 2794189 = 1047821) (by norm_num)
theorem B3725585 : Blo 1961435 3725585 := bstep (se 2 (by rfl) ⟨1397094, by rfl⟩ : syracuseStep 3725585 = 2794189) B2794189
theorem B2483723 : Blo 1961435 2483723 := bstep (se 1 (by rfl) ⟨1862792, by rfl⟩ : syracuseStep 2483723 = 3725585) B3725585
theorem B6623261 : Blo 1961435 6623261 := bstep (se 3 (by rfl) ⟨1241861, by rfl⟩ : syracuseStep 6623261 = 2483723) B2483723
theorem B4415507 : Blo 1961435 4415507 := bstep (se 1 (by rfl) ⟨3311630, by rfl⟩ : syracuseStep 4415507 = 6623261) B6623261
theorem B2943671 : Blo 1961435 2943671 := bstep (se 1 (by rfl) ⟨2207753, by rfl⟩ : syracuseStep 2943671 = 4415507) B4415507
theorem B1962447 : Blo 1961435 1962447 := bstep (se 1 (by rfl) ⟨1471835, by rfl⟩ : syracuseStep 1962447 = 2943671) B2943671
theorem B2943677 : Blo 1961435 2943677 := bbase (se 3 (by rfl) ⟨551939, by rfl⟩ : syracuseStep 2943677 = 1103879) (by norm_num)
theorem B1962451 : Blo 1961435 1962451 := bstep (se 1 (by rfl) ⟨1471838, by rfl⟩ : syracuseStep 1962451 = 2943677) B2943677
theorem B4415525 : Blo 1961435 4415525 := bbase (se 4 (by rfl) ⟨413955, by rfl⟩ : syracuseStep 4415525 = 827911) (by norm_num)
theorem B2943683 : Blo 1961435 2943683 := bstep (se 1 (by rfl) ⟨2207762, by rfl⟩ : syracuseStep 2943683 = 4415525) B4415525
theorem B1962455 : Blo 1961435 1962455 := bstep (se 1 (by rfl) ⟨1471841, by rfl⟩ : syracuseStep 1962455 = 2943683) B2943683
theorem B4967477 : Blo 1961435 4967477 := bbase (se 5 (by rfl) ⟨232850, by rfl⟩ : syracuseStep 4967477 = 465701) (by norm_num)
theorem B3311651 : Blo 1961435 3311651 := bstep (se 1 (by rfl) ⟨2483738, by rfl⟩ : syracuseStep 3311651 = 4967477) B4967477
theorem B2207767 : Blo 1961435 2207767 := bstep (se 1 (by rfl) ⟨1655825, by rfl⟩ : syracuseStep 2207767 = 3311651) B3311651
theorem B2943689 : Blo 1961435 2943689 := bstep (se 2 (by rfl) ⟨1103883, by rfl⟩ : syracuseStep 2943689 = 2207767) B2207767
theorem B1962459 : Blo 1961435 1962459 := bstep (se 1 (by rfl) ⟨1471844, by rfl⟩ : syracuseStep 1962459 = 2943689) B2943689
theorem B4475789 : Blo 1961435 4475789 := bbase (se 3 (by rfl) ⟨839210, by rfl⟩ : syracuseStep 4475789 = 1678421) (by norm_num)
theorem B2983859 : Blo 1961435 2983859 := bstep (se 1 (by rfl) ⟨2237894, by rfl⟩ : syracuseStep 2983859 = 4475789) B4475789
theorem B1989239 : Blo 1961435 1989239 := bstep (se 1 (by rfl) ⟨1491929, by rfl⟩ : syracuseStep 1989239 = 2983859) B2983859
theorem B5304637 : Blo 1961435 5304637 := bstep (se 3 (by rfl) ⟨994619, by rfl⟩ : syracuseStep 5304637 = 1989239) B1989239
theorem B7072849 : Blo 1961435 7072849 := bstep (se 2 (by rfl) ⟨2652318, by rfl⟩ : syracuseStep 7072849 = 5304637) B5304637
theorem B9430465 : Blo 1961435 9430465 := bstep (se 2 (by rfl) ⟨3536424, by rfl⟩ : syracuseStep 9430465 = 7072849) B7072849
theorem B12573953 : Blo 1961435 12573953 := bstep (se 2 (by rfl) ⟨4715232, by rfl⟩ : syracuseStep 12573953 = 9430465) B9430465
theorem B8382635 : Blo 1961435 8382635 := bstep (se 1 (by rfl) ⟨6286976, by rfl⟩ : syracuseStep 8382635 = 12573953) B12573953
theorem B5588423 : Blo 1961435 5588423 := bstep (se 1 (by rfl) ⟨4191317, by rfl⟩ : syracuseStep 5588423 = 8382635) B8382635
theorem B3725615 : Blo 1961435 3725615 := bstep (se 1 (by rfl) ⟨2794211, by rfl⟩ : syracuseStep 3725615 = 5588423) B5588423
theorem B9934973 : Blo 1961435 9934973 := bstep (se 3 (by rfl) ⟨1862807, by rfl⟩ : syracuseStep 9934973 = 3725615) B3725615
theorem B6623315 : Blo 1961435 6623315 := bstep (se 1 (by rfl) ⟨4967486, by rfl⟩ : syracuseStep 6623315 = 9934973) B9934973
theorem B4415543 : Blo 1961435 4415543 := bstep (se 1 (by rfl) ⟨3311657, by rfl⟩ : syracuseStep 4415543 = 6623315) B6623315
theorem B2943695 : Blo 1961435 2943695 := bstep (se 1 (by rfl) ⟨2207771, by rfl⟩ : syracuseStep 2943695 = 4415543) B4415543
theorem B1962463 : Blo 1961435 1962463 := bstep (se 1 (by rfl) ⟨1471847, by rfl⟩ : syracuseStep 1962463 = 2943695) B2943695
theorem B2943701 : Blo 1961435 2943701 := bbase (se 7 (by rfl) ⟨34496, by rfl⟩ : syracuseStep 2943701 = 68993) (by norm_num)
theorem B1962467 : Blo 1961435 1962467 := bstep (se 1 (by rfl) ⟨1471850, by rfl⟩ : syracuseStep 1962467 = 2943701) B2943701
theorem B22658773 : Blo 1961435 22658773 := bbase (se 7 (by rfl) ⟨265532, by rfl⟩ : syracuseStep 22658773 = 531065) (by norm_num)
theorem B30211697 : Blo 1961435 30211697 := bstep (se 2 (by rfl) ⟨11329386, by rfl⟩ : syracuseStep 30211697 = 22658773) B22658773
theorem B20141131 : Blo 1961435 20141131 := bstep (se 1 (by rfl) ⟨15105848, by rfl⟩ : syracuseStep 20141131 = 30211697) B30211697
theorem B26854841 : Blo 1961435 26854841 := bstep (se 2 (by rfl) ⟨10070565, by rfl⟩ : syracuseStep 26854841 = 20141131) B20141131
theorem B17903227 : Blo 1961435 17903227 := bstep (se 1 (by rfl) ⟨13427420, by rfl⟩ : syracuseStep 17903227 = 26854841) B26854841
theorem B23870969 : Blo 1961435 23870969 := bstep (se 2 (by rfl) ⟨8951613, by rfl⟩ : syracuseStep 23870969 = 17903227) B17903227
theorem B15913979 : Blo 1961435 15913979 := bstep (se 1 (by rfl) ⟨11935484, by rfl⟩ : syracuseStep 15913979 = 23870969) B23870969
theorem B10609319 : Blo 1961435 10609319 := bstep (se 1 (by rfl) ⟨7956989, by rfl⟩ : syracuseStep 10609319 = 15913979) B15913979
theorem B7072879 : Blo 1961435 7072879 := bstep (se 1 (by rfl) ⟨5304659, by rfl⟩ : syracuseStep 7072879 = 10609319) B10609319
theorem B9430505 : Blo 1961435 9430505 := bstep (se 2 (by rfl) ⟨3536439, by rfl⟩ : syracuseStep 9430505 = 7072879) B7072879
theorem B6287003 : Blo 1961435 6287003 := bstep (se 1 (by rfl) ⟨4715252, by rfl⟩ : syracuseStep 6287003 = 9430505) B9430505
theorem B4191335 : Blo 1961435 4191335 := bstep (se 1 (by rfl) ⟨3143501, by rfl⟩ : syracuseStep 4191335 = 6287003) B6287003
theorem B2794223 : Blo 1961435 2794223 := bstep (se 1 (by rfl) ⟨2095667, by rfl⟩ : syracuseStep 2794223 = 4191335) B4191335
theorem B7451261 : Blo 1961435 7451261 := bstep (se 3 (by rfl) ⟨1397111, by rfl⟩ : syracuseStep 7451261 = 2794223) B2794223
theorem B4967507 : Blo 1961435 4967507 := bstep (se 1 (by rfl) ⟨3725630, by rfl⟩ : syracuseStep 4967507 = 7451261) B7451261
theorem B3311671 : Blo 1961435 3311671 := bstep (se 1 (by rfl) ⟨2483753, by rfl⟩ : syracuseStep 3311671 = 4967507) B4967507
theorem B4415561 : Blo 1961435 4415561 := bstep (se 2 (by rfl) ⟨1655835, by rfl⟩ : syracuseStep 4415561 = 3311671) B3311671
theorem B2943707 : Blo 1961435 2943707 := bstep (se 1 (by rfl) ⟨2207780, by rfl⟩ : syracuseStep 2943707 = 4415561) B4415561
theorem B1962471 : Blo 1961435 1962471 := bstep (se 1 (by rfl) ⟨1471853, by rfl⟩ : syracuseStep 1962471 = 2943707) B2943707
theorem B2207785 : Blo 1961435 2207785 := bbase (se 2 (by rfl) ⟨827919, by rfl⟩ : syracuseStep 2207785 = 1655839) (by norm_num)
theorem B2943713 : Blo 1961435 2943713 := bstep (se 2 (by rfl) ⟨1103892, by rfl⟩ : syracuseStep 2943713 = 2207785) B2207785
theorem B1962475 : Blo 1961435 1962475 := bstep (se 1 (by rfl) ⟨1471856, by rfl⟩ : syracuseStep 1962475 = 2943713) B2943713
theorem B7760453 : Blo 1961435 7760453 := bbase (se 4 (by rfl) ⟨727542, by rfl⟩ : syracuseStep 7760453 = 1455085) (by norm_num)
theorem B82778165 : Blo 1961435 82778165 := bstep (se 5 (by rfl) ⟨3880226, by rfl⟩ : syracuseStep 82778165 = 7760453) B7760453
theorem B55185443 : Blo 1961435 55185443 := bstep (se 1 (by rfl) ⟨41389082, by rfl⟩ : syracuseStep 55185443 = 82778165) B82778165
theorem B36790295 : Blo 1961435 36790295 := bstep (se 1 (by rfl) ⟨27592721, by rfl⟩ : syracuseStep 36790295 = 55185443) B55185443
theorem B98107453 : Blo 1961435 98107453 := bstep (se 3 (by rfl) ⟨18395147, by rfl⟩ : syracuseStep 98107453 = 36790295) B36790295
theorem B130809937 : Blo 1961435 130809937 := bstep (se 2 (by rfl) ⟨49053726, by rfl⟩ : syracuseStep 130809937 = 98107453) B98107453
theorem B174413249 : Blo 1961435 174413249 := bstep (se 2 (by rfl) ⟨65404968, by rfl⟩ : syracuseStep 174413249 = 130809937) B130809937
theorem B116275499 : Blo 1961435 116275499 := bstep (se 1 (by rfl) ⟨87206624, by rfl⟩ : syracuseStep 116275499 = 174413249) B174413249
theorem B77516999 : Blo 1961435 77516999 := bstep (se 1 (by rfl) ⟨58137749, by rfl⟩ : syracuseStep 77516999 = 116275499) B116275499
theorem B51677999 : Blo 1961435 51677999 := bstep (se 1 (by rfl) ⟨38758499, by rfl⟩ : syracuseStep 51677999 = 77516999) B77516999
theorem B34451999 : Blo 1961435 34451999 := bstep (se 1 (by rfl) ⟨25838999, by rfl⟩ : syracuseStep 34451999 = 51677999) B51677999
theorem B22967999 : Blo 1961435 22967999 := bstep (se 1 (by rfl) ⟨17225999, by rfl⟩ : syracuseStep 22967999 = 34451999) B34451999
theorem B244991989 : Blo 1961435 244991989 := bstep (se 5 (by rfl) ⟨11483999, by rfl⟩ : syracuseStep 244991989 = 22967999) B22967999
theorem B326655985 : Blo 1961435 326655985 := bstep (se 2 (by rfl) ⟨122495994, by rfl⟩ : syracuseStep 326655985 = 244991989) B244991989
theorem B435541313 : Blo 1961435 435541313 := bstep (se 2 (by rfl) ⟨163327992, by rfl⟩ : syracuseStep 435541313 = 326655985) B326655985
theorem B290360875 : Blo 1961435 290360875 := bstep (se 1 (by rfl) ⟨217770656, by rfl⟩ : syracuseStep 290360875 = 435541313) B435541313
theorem B387147833 : Blo 1961435 387147833 := bstep (se 2 (by rfl) ⟨145180437, by rfl⟩ : syracuseStep 387147833 = 290360875) B290360875
theorem B258098555 : Blo 1961435 258098555 := bstep (se 1 (by rfl) ⟨193573916, by rfl⟩ : syracuseStep 258098555 = 387147833) B387147833
theorem B172065703 : Blo 1961435 172065703 := bstep (se 1 (by rfl) ⟨129049277, by rfl⟩ : syracuseStep 172065703 = 258098555) B258098555
theorem B229420937 : Blo 1961435 229420937 := bstep (se 2 (by rfl) ⟨86032851, by rfl⟩ : syracuseStep 229420937 = 172065703) B172065703
theorem B152947291 : Blo 1961435 152947291 := bstep (se 1 (by rfl) ⟨114710468, by rfl⟩ : syracuseStep 152947291 = 229420937) B229420937
theorem B203929721 : Blo 1961435 203929721 := bstep (se 2 (by rfl) ⟨76473645, by rfl⟩ : syracuseStep 203929721 = 152947291) B152947291
theorem B135953147 : Blo 1961435 135953147 := bstep (se 1 (by rfl) ⟨101964860, by rfl⟩ : syracuseStep 135953147 = 203929721) B203929721
theorem B90635431 : Blo 1961435 90635431 := bstep (se 1 (by rfl) ⟨67976573, by rfl⟩ : syracuseStep 90635431 = 135953147) B135953147
theorem B120847241 : Blo 1961435 120847241 := bstep (se 2 (by rfl) ⟨45317715, by rfl⟩ : syracuseStep 120847241 = 90635431) B90635431
theorem B80564827 : Blo 1961435 80564827 := bstep (se 1 (by rfl) ⟨60423620, by rfl⟩ : syracuseStep 80564827 = 120847241) B120847241
theorem B107419769 : Blo 1961435 107419769 := bstep (se 2 (by rfl) ⟨40282413, by rfl⟩ : syracuseStep 107419769 = 80564827) B80564827
theorem B71613179 : Blo 1961435 71613179 := bstep (se 1 (by rfl) ⟨53709884, by rfl⟩ : syracuseStep 71613179 = 107419769) B107419769
theorem B47742119 : Blo 1961435 47742119 := bstep (se 1 (by rfl) ⟨35806589, by rfl⟩ : syracuseStep 47742119 = 71613179) B71613179
theorem B31828079 : Blo 1961435 31828079 := bstep (se 1 (by rfl) ⟨23871059, by rfl⟩ : syracuseStep 31828079 = 47742119) B47742119
theorem B21218719 : Blo 1961435 21218719 := bstep (se 1 (by rfl) ⟨15914039, by rfl⟩ : syracuseStep 21218719 = 31828079) B31828079
theorem B28291625 : Blo 1961435 28291625 := bstep (se 2 (by rfl) ⟨10609359, by rfl⟩ : syracuseStep 28291625 = 21218719) B21218719
theorem B18861083 : Blo 1961435 18861083 := bstep (se 1 (by rfl) ⟨14145812, by rfl⟩ : syracuseStep 18861083 = 28291625) B28291625
theorem B12574055 : Blo 1961435 12574055 := bstep (se 1 (by rfl) ⟨9430541, by rfl⟩ : syracuseStep 12574055 = 18861083) B18861083
theorem B8382703 : Blo 1961435 8382703 := bstep (se 1 (by rfl) ⟨6287027, by rfl⟩ : syracuseStep 8382703 = 12574055) B12574055
theorem B11176937 : Blo 1961435 11176937 := bstep (se 2 (by rfl) ⟨4191351, by rfl⟩ : syracuseStep 11176937 = 8382703) B8382703
theorem B7451291 : Blo 1961435 7451291 := bstep (se 1 (by rfl) ⟨5588468, by rfl⟩ : syracuseStep 7451291 = 11176937) B11176937
theorem B4967527 : Blo 1961435 4967527 := bstep (se 1 (by rfl) ⟨3725645, by rfl⟩ : syracuseStep 4967527 = 7451291) B7451291
theorem B6623369 : Blo 1961435 6623369 := bstep (se 2 (by rfl) ⟨2483763, by rfl⟩ : syracuseStep 6623369 = 4967527) B4967527
theorem B4415579 : Blo 1961435 4415579 := bstep (se 1 (by rfl) ⟨3311684, by rfl⟩ : syracuseStep 4415579 = 6623369) B6623369
theorem B2943719 : Blo 1961435 2943719 := bstep (se 1 (by rfl) ⟨2207789, by rfl⟩ : syracuseStep 2943719 = 4415579) B4415579
theorem B1962479 : Blo 1961435 1962479 := bstep (se 1 (by rfl) ⟨1471859, by rfl⟩ : syracuseStep 1962479 = 2943719) B2943719
theorem B2943725 : Blo 1961435 2943725 := bbase (se 3 (by rfl) ⟨551948, by rfl⟩ : syracuseStep 2943725 = 1103897) (by norm_num)
theorem B1962483 : Blo 1961435 1962483 := bstep (se 1 (by rfl) ⟨1471862, by rfl⟩ : syracuseStep 1962483 = 2943725) B2943725
theorem B4415597 : Blo 1961435 4415597 := bbase (se 3 (by rfl) ⟨827924, by rfl⟩ : syracuseStep 4415597 = 1655849) (by norm_num)
theorem B2943731 : Blo 1961435 2943731 := bstep (se 1 (by rfl) ⟨2207798, by rfl⟩ : syracuseStep 2943731 = 4415597) B4415597
theorem B1962487 : Blo 1961435 1962487 := bstep (se 1 (by rfl) ⟨1471865, by rfl⟩ : syracuseStep 1962487 = 2943731) B2943731
theorem B3725669 : Blo 1961435 3725669 := bbase (se 4 (by rfl) ⟨349281, by rfl⟩ : syracuseStep 3725669 = 698563) (by norm_num)
theorem B2483779 : Blo 1961435 2483779 := bstep (se 1 (by rfl) ⟨1862834, by rfl⟩ : syracuseStep 2483779 = 3725669) B3725669
theorem B3311705 : Blo 1961435 3311705 := bstep (se 2 (by rfl) ⟨1241889, by rfl⟩ : syracuseStep 3311705 = 2483779) B2483779
theorem B2207803 : Blo 1961435 2207803 := bstep (se 1 (by rfl) ⟨1655852, by rfl⟩ : syracuseStep 2207803 = 3311705) B3311705
theorem B2943737 : Blo 1961435 2943737 := bstep (se 2 (by rfl) ⟨1103901, by rfl⟩ : syracuseStep 2943737 = 2207803) B2207803
theorem B1962491 : Blo 1961435 1962491 := bstep (se 1 (by rfl) ⟨1471868, by rfl⟩ : syracuseStep 1962491 = 2943737) B2943737
theorem B4475861 : Blo 1961435 4475861 := bbase (se 7 (by rfl) ⟨52451, by rfl⟩ : syracuseStep 4475861 = 104903) (by norm_num)
theorem B2983907 : Blo 1961435 2983907 := bstep (se 1 (by rfl) ⟨2237930, by rfl⟩ : syracuseStep 2983907 = 4475861) B4475861
theorem B1989271 : Blo 1961435 1989271 := bstep (se 1 (by rfl) ⟨1491953, by rfl⟩ : syracuseStep 1989271 = 2983907) B2983907
theorem B10609445 : Blo 1961435 10609445 := bstep (se 4 (by rfl) ⟨994635, by rfl⟩ : syracuseStep 10609445 = 1989271) B1989271
theorem B7072963 : Blo 1961435 7072963 := bstep (se 1 (by rfl) ⟨5304722, by rfl⟩ : syracuseStep 7072963 = 10609445) B10609445
theorem B37722469 : Blo 1961435 37722469 := bstep (se 4 (by rfl) ⟨3536481, by rfl⟩ : syracuseStep 37722469 = 7072963) B7072963
theorem B50296625 : Blo 1961435 50296625 := bstep (se 2 (by rfl) ⟨18861234, by rfl⟩ : syracuseStep 50296625 = 37722469) B37722469
theorem B33531083 : Blo 1961435 33531083 := bstep (se 1 (by rfl) ⟨25148312, by rfl⟩ : syracuseStep 33531083 = 50296625) B50296625
theorem B22354055 : Blo 1961435 22354055 := bstep (se 1 (by rfl) ⟨16765541, by rfl⟩ : syracuseStep 22354055 = 33531083) B33531083
theorem B14902703 : Blo 1961435 14902703 := bstep (se 1 (by rfl) ⟨11177027, by rfl⟩ : syracuseStep 14902703 = 22354055) B22354055
theorem B9935135 : Blo 1961435 9935135 := bstep (se 1 (by rfl) ⟨7451351, by rfl⟩ : syracuseStep 9935135 = 14902703) B14902703
theorem B6623423 : Blo 1961435 6623423 := bstep (se 1 (by rfl) ⟨4967567, by rfl⟩ : syracuseStep 6623423 = 9935135) B9935135
theorem B4415615 : Blo 1961435 4415615 := bstep (se 1 (by rfl) ⟨3311711, by rfl⟩ : syracuseStep 4415615 = 6623423) B6623423
theorem B2943743 : Blo 1961435 2943743 := bstep (se 1 (by rfl) ⟨2207807, by rfl⟩ : syracuseStep 2943743 = 4415615) B4415615
theorem B1962495 : Blo 1961435 1962495 := bstep (se 1 (by rfl) ⟨1471871, by rfl⟩ : syracuseStep 1962495 = 2943743) B2943743
theorem B2943749 : Blo 1961435 2943749 := bbase (se 4 (by rfl) ⟨275976, by rfl⟩ : syracuseStep 2943749 = 551953) (by norm_num)
theorem B1962499 : Blo 1961435 1962499 := bstep (se 1 (by rfl) ⟨1471874, by rfl⟩ : syracuseStep 1962499 = 2943749) B2943749
theorem B3311725 : Blo 1961435 3311725 := bbase (se 3 (by rfl) ⟨620948, by rfl⟩ : syracuseStep 3311725 = 1241897) (by norm_num)
theorem B4415633 : Blo 1961435 4415633 := bstep (se 2 (by rfl) ⟨1655862, by rfl⟩ : syracuseStep 4415633 = 3311725) B3311725
theorem B2943755 : Blo 1961435 2943755 := bstep (se 1 (by rfl) ⟨2207816, by rfl⟩ : syracuseStep 2943755 = 4415633) B4415633
theorem B1962503 : Blo 1961435 1962503 := bstep (se 1 (by rfl) ⟨1471877, by rfl⟩ : syracuseStep 1962503 = 2943755) B2943755
theorem B2207821 : Blo 1961435 2207821 := bbase (se 3 (by rfl) ⟨413966, by rfl⟩ : syracuseStep 2207821 = 827933) (by norm_num)
theorem B2943761 : Blo 1961435 2943761 := bstep (se 2 (by rfl) ⟨1103910, by rfl⟩ : syracuseStep 2943761 = 2207821) B2207821
theorem B1962507 : Blo 1961435 1962507 := bstep (se 1 (by rfl) ⟨1471880, by rfl⟩ : syracuseStep 1962507 = 2943761) B2943761
theorem B6623477 : Blo 1961435 6623477 := bbase (se 5 (by rfl) ⟨310475, by rfl⟩ : syracuseStep 6623477 = 620951) (by norm_num)
theorem B4415651 : Blo 1961435 4415651 := bstep (se 1 (by rfl) ⟨3311738, by rfl⟩ : syracuseStep 4415651 = 6623477) B6623477
theorem B2943767 : Blo 1961435 2943767 := bstep (se 1 (by rfl) ⟨2207825, by rfl⟩ : syracuseStep 2943767 = 4415651) B4415651
theorem B1962511 : Blo 1961435 1962511 := bstep (se 1 (by rfl) ⟨1471883, by rfl⟩ : syracuseStep 1962511 = 2943767) B2943767
theorem B2943773 : Blo 1961435 2943773 := bbase (se 3 (by rfl) ⟨551957, by rfl⟩ : syracuseStep 2943773 = 1103915) (by norm_num)
theorem B1962515 : Blo 1961435 1962515 := bstep (se 1 (by rfl) ⟨1471886, by rfl⟩ : syracuseStep 1962515 = 2943773) B2943773
theorem B4415669 : Blo 1961435 4415669 := bbase (se 5 (by rfl) ⟨206984, by rfl⟩ : syracuseStep 4415669 = 413969) (by norm_num)
theorem B2943779 : Blo 1961435 2943779 := bstep (se 1 (by rfl) ⟨2207834, by rfl⟩ : syracuseStep 2943779 = 4415669) B4415669
theorem B1962519 : Blo 1961435 1962519 := bstep (se 1 (by rfl) ⟨1471889, by rfl⟩ : syracuseStep 1962519 = 2943779) B2943779
theorem B2357689 : Blo 1961435 2357689 := bbase (se 2 (by rfl) ⟨884133, by rfl⟩ : syracuseStep 2357689 = 1768267) (by norm_num)
theorem B3143585 : Blo 1961435 3143585 := bstep (se 2 (by rfl) ⟨1178844, by rfl⟩ : syracuseStep 3143585 = 2357689) B2357689
theorem B2095723 : Blo 1961435 2095723 := bstep (se 1 (by rfl) ⟨1571792, by rfl⟩ : syracuseStep 2095723 = 3143585) B3143585
theorem B11177189 : Blo 1961435 11177189 := bstep (se 4 (by rfl) ⟨1047861, by rfl⟩ : syracuseStep 11177189 = 2095723) B2095723
theorem B7451459 : Blo 1961435 7451459 := bstep (se 1 (by rfl) ⟨5588594, by rfl⟩ : syracuseStep 7451459 = 11177189) B11177189
theorem B4967639 : Blo 1961435 4967639 := bstep (se 1 (by rfl) ⟨3725729, by rfl⟩ : syracuseStep 4967639 = 7451459) B7451459
theorem B3311759 : Blo 1961435 3311759 := bstep (se 1 (by rfl) ⟨2483819, by rfl⟩ : syracuseStep 3311759 = 4967639) B4967639
theorem B2207839 : Blo 1961435 2207839 := bstep (se 1 (by rfl) ⟨1655879, by rfl⟩ : syracuseStep 2207839 = 3311759) B3311759
theorem B2943785 : Blo 1961435 2943785 := bstep (se 2 (by rfl) ⟨1103919, by rfl⟩ : syracuseStep 2943785 = 2207839) B2207839
theorem B1962523 : Blo 1961435 1962523 := bstep (se 1 (by rfl) ⟨1471892, by rfl⟩ : syracuseStep 1962523 = 2943785) B2943785
theorem B2153305 : Blo 1961435 2153305 := bbase (se 2 (by rfl) ⟨807489, by rfl⟩ : syracuseStep 2153305 = 1614979) (by norm_num)
theorem B2871073 : Blo 1961435 2871073 := bstep (se 2 (by rfl) ⟨1076652, by rfl⟩ : syracuseStep 2871073 = 2153305) B2153305
theorem B3828097 : Blo 1961435 3828097 := bstep (se 2 (by rfl) ⟨1435536, by rfl⟩ : syracuseStep 3828097 = 2871073) B2871073
theorem B5104129 : Blo 1961435 5104129 := bstep (se 2 (by rfl) ⟨1914048, by rfl⟩ : syracuseStep 5104129 = 3828097) B3828097
theorem B6805505 : Blo 1961435 6805505 := bstep (se 2 (by rfl) ⟨2552064, by rfl⟩ : syracuseStep 6805505 = 5104129) B5104129
theorem B4537003 : Blo 1961435 4537003 := bstep (se 1 (by rfl) ⟨3402752, by rfl⟩ : syracuseStep 4537003 = 6805505) B6805505
theorem B6049337 : Blo 1961435 6049337 := bstep (se 2 (by rfl) ⟨2268501, by rfl⟩ : syracuseStep 6049337 = 4537003) B4537003
theorem B16131565 : Blo 1961435 16131565 := bstep (se 3 (by rfl) ⟨3024668, by rfl⟩ : syracuseStep 16131565 = 6049337) B6049337
theorem B21508753 : Blo 1961435 21508753 := bstep (se 2 (by rfl) ⟨8065782, by rfl⟩ : syracuseStep 21508753 = 16131565) B16131565
theorem B28678337 : Blo 1961435 28678337 := bstep (se 2 (by rfl) ⟨10754376, by rfl⟩ : syracuseStep 28678337 = 21508753) B21508753
theorem B19118891 : Blo 1961435 19118891 := bstep (se 1 (by rfl) ⟨14339168, by rfl⟩ : syracuseStep 19118891 = 28678337) B28678337
theorem B12745927 : Blo 1961435 12745927 := bstep (se 1 (by rfl) ⟨9559445, by rfl⟩ : syracuseStep 12745927 = 19118891) B19118891
theorem B16994569 : Blo 1961435 16994569 := bstep (se 2 (by rfl) ⟨6372963, by rfl⟩ : syracuseStep 16994569 = 12745927) B12745927
theorem B22659425 : Blo 1961435 22659425 := bstep (se 2 (by rfl) ⟨8497284, by rfl⟩ : syracuseStep 22659425 = 16994569) B16994569
theorem B15106283 : Blo 1961435 15106283 := bstep (se 1 (by rfl) ⟨11329712, by rfl⟩ : syracuseStep 15106283 = 22659425) B22659425
theorem B10070855 : Blo 1961435 10070855 := bstep (se 1 (by rfl) ⟨7553141, by rfl⟩ : syracuseStep 10070855 = 15106283) B15106283
theorem B6713903 : Blo 1961435 6713903 := bstep (se 1 (by rfl) ⟨5035427, by rfl⟩ : syracuseStep 6713903 = 10070855) B10070855
theorem B4475935 : Blo 1961435 4475935 := bstep (se 1 (by rfl) ⟨3356951, by rfl⟩ : syracuseStep 4475935 = 6713903) B6713903
theorem B5967913 : Blo 1961435 5967913 := bstep (se 2 (by rfl) ⟨2237967, by rfl⟩ : syracuseStep 5967913 = 4475935) B4475935
theorem B7957217 : Blo 1961435 7957217 := bstep (se 2 (by rfl) ⟨2983956, by rfl⟩ : syracuseStep 7957217 = 5967913) B5967913
theorem B5304811 : Blo 1961435 5304811 := bstep (se 1 (by rfl) ⟨3978608, by rfl⟩ : syracuseStep 5304811 = 7957217) B7957217
theorem B7073081 : Blo 1961435 7073081 := bstep (se 2 (by rfl) ⟨2652405, by rfl⟩ : syracuseStep 7073081 = 5304811) B5304811
theorem B4715387 : Blo 1961435 4715387 := bstep (se 1 (by rfl) ⟨3536540, by rfl⟩ : syracuseStep 4715387 = 7073081) B7073081
theorem B3143591 : Blo 1961435 3143591 := bstep (se 1 (by rfl) ⟨2357693, by rfl⟩ : syracuseStep 3143591 = 4715387) B4715387
theorem B2095727 : Blo 1961435 2095727 := bstep (se 1 (by rfl) ⟨1571795, by rfl⟩ : syracuseStep 2095727 = 3143591) B3143591
theorem B5588605 : Blo 1961435 5588605 := bstep (se 3 (by rfl) ⟨1047863, by rfl⟩ : syracuseStep 5588605 = 2095727) B2095727
theorem B7451473 : Blo 1961435 7451473 := bstep (se 2 (by rfl) ⟨2794302, by rfl⟩ : syracuseStep 7451473 = 5588605) B5588605
theorem B9935297 : Blo 1961435 9935297 := bstep (se 2 (by rfl) ⟨3725736, by rfl⟩ : syracuseStep 9935297 = 7451473) B7451473
theorem B6623531 : Blo 1961435 6623531 := bstep (se 1 (by rfl) ⟨4967648, by rfl⟩ : syracuseStep 6623531 = 9935297) B9935297
theorem B4415687 : Blo 1961435 4415687 := bstep (se 1 (by rfl) ⟨3311765, by rfl⟩ : syracuseStep 4415687 = 6623531) B6623531
theorem B2943791 : Blo 1961435 2943791 := bstep (se 1 (by rfl) ⟨2207843, by rfl⟩ : syracuseStep 2943791 = 4415687) B4415687
theorem B1962527 : Blo 1961435 1962527 := bstep (se 1 (by rfl) ⟨1471895, by rfl⟩ : syracuseStep 1962527 = 2943791) B2943791
theorem B2943797 : Blo 1961435 2943797 := bbase (se 5 (by rfl) ⟨137990, by rfl⟩ : syracuseStep 2943797 = 275981) (by norm_num)
theorem B1962531 : Blo 1961435 1962531 := bstep (se 1 (by rfl) ⟨1471898, by rfl⟩ : syracuseStep 1962531 = 2943797) B2943797
theorem B4967669 : Blo 1961435 4967669 := bbase (se 5 (by rfl) ⟨232859, by rfl⟩ : syracuseStep 4967669 = 465719) (by norm_num)
theorem B3311779 : Blo 1961435 3311779 := bstep (se 1 (by rfl) ⟨2483834, by rfl⟩ : syracuseStep 3311779 = 4967669) B4967669
theorem B4415705 : Blo 1961435 4415705 := bstep (se 2 (by rfl) ⟨1655889, by rfl⟩ : syracuseStep 4415705 = 3311779) B3311779
theorem B2943803 : Blo 1961435 2943803 := bstep (se 1 (by rfl) ⟨2207852, by rfl⟩ : syracuseStep 2943803 = 4415705) B4415705
theorem B1962535 : Blo 1961435 1962535 := bstep (se 1 (by rfl) ⟨1471901, by rfl⟩ : syracuseStep 1962535 = 2943803) B2943803
theorem B2207857 : Blo 1961435 2207857 := bbase (se 2 (by rfl) ⟨827946, by rfl⟩ : syracuseStep 2207857 = 1655893) (by norm_num)
theorem B2943809 : Blo 1961435 2943809 := bstep (se 2 (by rfl) ⟨1103928, by rfl⟩ : syracuseStep 2943809 = 2207857) B2207857
theorem B1962539 : Blo 1961435 1962539 := bstep (se 1 (by rfl) ⟨1471904, by rfl⟩ : syracuseStep 1962539 = 2943809) B2943809
theorem B2983981 : Blo 1961435 2983981 := bbase (se 3 (by rfl) ⟨559496, by rfl⟩ : syracuseStep 2983981 = 1118993) (by norm_num)
theorem B3978641 : Blo 1961435 3978641 := bstep (se 2 (by rfl) ⟨1491990, by rfl⟩ : syracuseStep 3978641 = 2983981) B2983981
theorem B2652427 : Blo 1961435 2652427 := bstep (se 1 (by rfl) ⟨1989320, by rfl⟩ : syracuseStep 2652427 = 3978641) B3978641
theorem B3536569 : Blo 1961435 3536569 := bstep (se 2 (by rfl) ⟨1326213, by rfl⟩ : syracuseStep 3536569 = 2652427) B2652427
theorem B4715425 : Blo 1961435 4715425 := bstep (se 2 (by rfl) ⟨1768284, by rfl⟩ : syracuseStep 4715425 = 3536569) B3536569
theorem B6287233 : Blo 1961435 6287233 := bstep (se 2 (by rfl) ⟨2357712, by rfl⟩ : syracuseStep 6287233 = 4715425) B4715425
theorem B8382977 : Blo 1961435 8382977 := bstep (se 2 (by rfl) ⟨3143616, by rfl⟩ : syracuseStep 8382977 = 6287233) B6287233
theorem B5588651 : Blo 1961435 5588651 := bstep (se 1 (by rfl) ⟨4191488, by rfl⟩ : syracuseStep 5588651 = 8382977) B8382977
theorem B3725767 : Blo 1961435 3725767 := bstep (se 1 (by rfl) ⟨2794325, by rfl⟩ : syracuseStep 3725767 = 5588651) B5588651
theorem B4967689 : Blo 1961435 4967689 := bstep (se 2 (by rfl) ⟨1862883, by rfl⟩ : syracuseStep 4967689 = 3725767) B3725767
theorem B6623585 : Blo 1961435 6623585 := bstep (se 2 (by rfl) ⟨2483844, by rfl⟩ : syracuseStep 6623585 = 4967689) B4967689
theorem B4415723 : Blo 1961435 4415723 := bstep (se 1 (by rfl) ⟨3311792, by rfl⟩ : syracuseStep 4415723 = 6623585) B6623585
theorem B2943815 : Blo 1961435 2943815 := bstep (se 1 (by rfl) ⟨2207861, by rfl⟩ : syracuseStep 2943815 = 4415723) B4415723
theorem B1962543 : Blo 1961435 1962543 := bstep (se 1 (by rfl) ⟨1471907, by rfl⟩ : syracuseStep 1962543 = 2943815) B2943815
theorem B2943821 : Blo 1961435 2943821 := bbase (se 3 (by rfl) ⟨551966, by rfl⟩ : syracuseStep 2943821 = 1103933) (by norm_num)
theorem B1962547 : Blo 1961435 1962547 := bstep (se 1 (by rfl) ⟨1471910, by rfl⟩ : syracuseStep 1962547 = 2943821) B2943821
theorem B4415741 : Blo 1961435 4415741 := bbase (se 3 (by rfl) ⟨827951, by rfl⟩ : syracuseStep 4415741 = 1655903) (by norm_num)
theorem B2943827 : Blo 1961435 2943827 := bstep (se 1 (by rfl) ⟨2207870, by rfl⟩ : syracuseStep 2943827 = 4415741) B4415741
theorem B1962551 : Blo 1961435 1962551 := bstep (se 1 (by rfl) ⟨1471913, by rfl⟩ : syracuseStep 1962551 = 2943827) B2943827
theorem B3311813 : Blo 1961435 3311813 := bbase (se 4 (by rfl) ⟨310482, by rfl⟩ : syracuseStep 3311813 = 620965) (by norm_num)
theorem B2207875 : Blo 1961435 2207875 := bstep (se 1 (by rfl) ⟨1655906, by rfl⟩ : syracuseStep 2207875 = 3311813) B3311813
theorem B2943833 : Blo 1961435 2943833 := bstep (se 2 (by rfl) ⟨1103937, by rfl⟩ : syracuseStep 2943833 = 2207875) B2207875
theorem B1962555 : Blo 1961435 1962555 := bstep (se 1 (by rfl) ⟨1471916, by rfl⟩ : syracuseStep 1962555 = 2943833) B2943833
theorem B14903189 : Blo 1961435 14903189 := bbase (se 6 (by rfl) ⟨349293, by rfl⟩ : syracuseStep 14903189 = 698587) (by norm_num)
theorem B9935459 : Blo 1961435 9935459 := bstep (se 1 (by rfl) ⟨7451594, by rfl⟩ : syracuseStep 9935459 = 14903189) B14903189
theorem B6623639 : Blo 1961435 6623639 := bstep (se 1 (by rfl) ⟨4967729, by rfl⟩ : syracuseStep 6623639 = 9935459) B9935459
theorem B4415759 : Blo 1961435 4415759 := bstep (se 1 (by rfl) ⟨3311819, by rfl⟩ : syracuseStep 4415759 = 6623639) B6623639
theorem B2943839 : Blo 1961435 2943839 := bstep (se 1 (by rfl) ⟨2207879, by rfl⟩ : syracuseStep 2943839 = 4415759) B4415759
theorem B1962559 : Blo 1961435 1962559 := bstep (se 1 (by rfl) ⟨1471919, by rfl⟩ : syracuseStep 1962559 = 2943839) B2943839
theorem B2943845 : Blo 1961435 2943845 := bbase (se 4 (by rfl) ⟨275985, by rfl⟩ : syracuseStep 2943845 = 551971) (by norm_num)
theorem B1962563 : Blo 1961435 1962563 := bstep (se 1 (by rfl) ⟨1471922, by rfl⟩ : syracuseStep 1962563 = 2943845) B2943845
theorem B3725813 : Blo 1961435 3725813 := bbase (se 5 (by rfl) ⟨174647, by rfl⟩ : syracuseStep 3725813 = 349295) (by norm_num)
theorem B2483875 : Blo 1961435 2483875 := bstep (se 1 (by rfl) ⟨1862906, by rfl⟩ : syracuseStep 2483875 = 3725813) B3725813
theorem B3311833 : Blo 1961435 3311833 := bstep (se 2 (by rfl) ⟨1241937, by rfl⟩ : syracuseStep 3311833 = 2483875) B2483875
theorem B4415777 : Blo 1961435 4415777 := bstep (se 2 (by rfl) ⟨1655916, by rfl⟩ : syracuseStep 4415777 = 3311833) B3311833
theorem B2943851 : Blo 1961435 2943851 := bstep (se 1 (by rfl) ⟨2207888, by rfl⟩ : syracuseStep 2943851 = 4415777) B4415777
theorem B1962567 : Blo 1961435 1962567 := bstep (se 1 (by rfl) ⟨1471925, by rfl⟩ : syracuseStep 1962567 = 2943851) B2943851
theorem B2207893 : Blo 1961435 2207893 := bbase (se 6 (by rfl) ⟨51747, by rfl⟩ : syracuseStep 2207893 = 103495) (by norm_num)
theorem B2943857 : Blo 1961435 2943857 := bstep (se 2 (by rfl) ⟨1103946, by rfl⟩ : syracuseStep 2943857 = 2207893) B2207893
theorem B1962571 : Blo 1961435 1962571 := bstep (se 1 (by rfl) ⟨1471928, by rfl⟩ : syracuseStep 1962571 = 2943857) B2943857
theorem B2483885 : Blo 1961435 2483885 := bbase (se 3 (by rfl) ⟨465728, by rfl⟩ : syracuseStep 2483885 = 931457) (by norm_num)
theorem B6623693 : Blo 1961435 6623693 := bstep (se 3 (by rfl) ⟨1241942, by rfl⟩ : syracuseStep 6623693 = 2483885) B2483885
theorem B4415795 : Blo 1961435 4415795 := bstep (se 1 (by rfl) ⟨3311846, by rfl⟩ : syracuseStep 4415795 = 6623693) B6623693
theorem B2943863 : Blo 1961435 2943863 := bstep (se 1 (by rfl) ⟨2207897, by rfl⟩ : syracuseStep 2943863 = 4415795) B4415795
theorem B1962575 : Blo 1961435 1962575 := bstep (se 1 (by rfl) ⟨1471931, by rfl⟩ : syracuseStep 1962575 = 2943863) B2943863
theorem B2943869 : Blo 1961435 2943869 := bbase (se 3 (by rfl) ⟨551975, by rfl⟩ : syracuseStep 2943869 = 1103951) (by norm_num)
theorem B1962579 : Blo 1961435 1962579 := bstep (se 1 (by rfl) ⟨1471934, by rfl⟩ : syracuseStep 1962579 = 2943869) B2943869
theorem B4415813 : Blo 1961435 4415813 := bbase (se 4 (by rfl) ⟨413982, by rfl⟩ : syracuseStep 4415813 = 827965) (by norm_num)
theorem B2943875 : Blo 1961435 2943875 := bstep (se 1 (by rfl) ⟨2207906, by rfl⟩ : syracuseStep 2943875 = 4415813) B4415813
theorem B1962583 : Blo 1961435 1962583 := bstep (se 1 (by rfl) ⟨1471937, by rfl⟩ : syracuseStep 1962583 = 2943875) B2943875
theorem B1989365 : Blo 1961435 1989365 := bbase (se 5 (by rfl) ⟨93251, by rfl⟩ : syracuseStep 1989365 = 186503) (by norm_num)
theorem B21219893 : Blo 1961435 21219893 := bstep (se 5 (by rfl) ⟨994682, by rfl⟩ : syracuseStep 21219893 = 1989365) B1989365
theorem B14146595 : Blo 1961435 14146595 := bstep (se 1 (by rfl) ⟨10609946, by rfl⟩ : syracuseStep 14146595 = 21219893) B21219893
theorem B9431063 : Blo 1961435 9431063 := bstep (se 1 (by rfl) ⟨7073297, by rfl⟩ : syracuseStep 9431063 = 14146595) B14146595
theorem B6287375 : Blo 1961435 6287375 := bstep (se 1 (by rfl) ⟨4715531, by rfl⟩ : syracuseStep 6287375 = 9431063) B9431063
theorem B4191583 : Blo 1961435 4191583 := bstep (se 1 (by rfl) ⟨3143687, by rfl⟩ : syracuseStep 4191583 = 6287375) B6287375
theorem B5588777 : Blo 1961435 5588777 := bstep (se 2 (by rfl) ⟨2095791, by rfl⟩ : syracuseStep 5588777 = 4191583) B4191583
theorem B3725851 : Blo 1961435 3725851 := bstep (se 1 (by rfl) ⟨2794388, by rfl⟩ : syracuseStep 3725851 = 5588777) B5588777
theorem B4967801 : Blo 1961435 4967801 := bstep (se 2 (by rfl) ⟨1862925, by rfl⟩ : syracuseStep 4967801 = 3725851) B3725851
theorem B3311867 : Blo 1961435 3311867 := bstep (se 1 (by rfl) ⟨2483900, by rfl⟩ : syracuseStep 3311867 = 4967801) B4967801
theorem B2207911 : Blo 1961435 2207911 := bstep (se 1 (by rfl) ⟨1655933, by rfl⟩ : syracuseStep 2207911 = 3311867) B3311867
theorem B2943881 : Blo 1961435 2943881 := bstep (se 2 (by rfl) ⟨1103955, by rfl⟩ : syracuseStep 2943881 = 2207911) B2207911
theorem B1962587 : Blo 1961435 1962587 := bstep (se 1 (by rfl) ⟨1471940, by rfl⟩ : syracuseStep 1962587 = 2943881) B2943881
theorem B9935621 : Blo 1961435 9935621 := bbase (se 4 (by rfl) ⟨931464, by rfl⟩ : syracuseStep 9935621 = 1862929) (by norm_num)
theorem B6623747 : Blo 1961435 6623747 := bstep (se 1 (by rfl) ⟨4967810, by rfl⟩ : syracuseStep 6623747 = 9935621) B9935621
theorem B4415831 : Blo 1961435 4415831 := bstep (se 1 (by rfl) ⟨3311873, by rfl⟩ : syracuseStep 4415831 = 6623747) B6623747
theorem B2943887 : Blo 1961435 2943887 := bstep (se 1 (by rfl) ⟨2207915, by rfl⟩ : syracuseStep 2943887 = 4415831) B4415831
theorem B1962591 : Blo 1961435 1962591 := bstep (se 1 (by rfl) ⟨1471943, by rfl⟩ : syracuseStep 1962591 = 2943887) B2943887
theorem B2943893 : Blo 1961435 2943893 := bbase (se 6 (by rfl) ⟨68997, by rfl⟩ : syracuseStep 2943893 = 137995) (by norm_num)
theorem B1962595 : Blo 1961435 1962595 := bstep (se 1 (by rfl) ⟨1471946, by rfl⟩ : syracuseStep 1962595 = 2943893) B2943893
theorem B11177621 : Blo 1961435 11177621 := bbase (se 6 (by rfl) ⟨261975, by rfl⟩ : syracuseStep 11177621 = 523951) (by norm_num)
theorem B7451747 : Blo 1961435 7451747 := bstep (se 1 (by rfl) ⟨5588810, by rfl⟩ : syracuseStep 7451747 = 11177621) B11177621
theorem B4967831 : Blo 1961435 4967831 := bstep (se 1 (by rfl) ⟨3725873, by rfl⟩ : syracuseStep 4967831 = 7451747) B7451747
theorem B3311887 : Blo 1961435 3311887 := bstep (se 1 (by rfl) ⟨2483915, by rfl⟩ : syracuseStep 3311887 = 4967831) B4967831
theorem B4415849 : Blo 1961435 4415849 := bstep (se 2 (by rfl) ⟨1655943, by rfl⟩ : syracuseStep 4415849 = 3311887) B3311887
theorem B2943899 : Blo 1961435 2943899 := bstep (se 1 (by rfl) ⟨2207924, by rfl⟩ : syracuseStep 2943899 = 4415849) B4415849
theorem B1962599 : Blo 1961435 1962599 := bstep (se 1 (by rfl) ⟨1471949, by rfl⟩ : syracuseStep 1962599 = 2943899) B2943899
theorem B2207929 : Blo 1961435 2207929 := bbase (se 2 (by rfl) ⟨827973, by rfl⟩ : syracuseStep 2207929 = 1655947) (by norm_num)
theorem B2943905 : Blo 1961435 2943905 := bstep (se 2 (by rfl) ⟨1103964, by rfl⟩ : syracuseStep 2943905 = 2207929) B2207929
theorem B1962603 : Blo 1961435 1962603 := bstep (se 1 (by rfl) ⟨1471952, by rfl⟩ : syracuseStep 1962603 = 2943905) B2943905
theorem B7957541 : Blo 1961435 7957541 := bbase (se 4 (by rfl) ⟨746019, by rfl⟩ : syracuseStep 7957541 = 1492039) (by norm_num)
theorem B5305027 : Blo 1961435 5305027 := bstep (se 1 (by rfl) ⟨3978770, by rfl⟩ : syracuseStep 5305027 = 7957541) B7957541
theorem B7073369 : Blo 1961435 7073369 := bstep (se 2 (by rfl) ⟨2652513, by rfl⟩ : syracuseStep 7073369 = 5305027) B5305027
theorem B4715579 : Blo 1961435 4715579 := bstep (se 1 (by rfl) ⟨3536684, by rfl⟩ : syracuseStep 4715579 = 7073369) B7073369
theorem B3143719 : Blo 1961435 3143719 := bstep (se 1 (by rfl) ⟨2357789, by rfl⟩ : syracuseStep 3143719 = 4715579) B4715579
theorem B4191625 : Blo 1961435 4191625 := bstep (se 2 (by rfl) ⟨1571859, by rfl⟩ : syracuseStep 4191625 = 3143719) B3143719
theorem B5588833 : Blo 1961435 5588833 := bstep (se 2 (by rfl) ⟨2095812, by rfl⟩ : syracuseStep 5588833 = 4191625) B4191625
theorem B7451777 : Blo 1961435 7451777 := bstep (se 2 (by rfl) ⟨2794416, by rfl⟩ : syracuseStep 7451777 = 5588833) B5588833
theorem B4967851 : Blo 1961435 4967851 := bstep (se 1 (by rfl) ⟨3725888, by rfl⟩ : syracuseStep 4967851 = 7451777) B7451777
theorem B6623801 : Blo 1961435 6623801 := bstep (se 2 (by rfl) ⟨2483925, by rfl⟩ : syracuseStep 6623801 = 4967851) B4967851
theorem B4415867 : Blo 1961435 4415867 := bstep (se 1 (by rfl) ⟨3311900, by rfl⟩ : syracuseStep 4415867 = 6623801) B6623801
theorem B2943911 : Blo 1961435 2943911 := bstep (se 1 (by rfl) ⟨2207933, by rfl⟩ : syracuseStep 2943911 = 4415867) B4415867
theorem B1962607 : Blo 1961435 1962607 := bstep (se 1 (by rfl) ⟨1471955, by rfl⟩ : syracuseStep 1962607 = 2943911) B2943911
theorem B2943917 : Blo 1961435 2943917 := bbase (se 3 (by rfl) ⟨551984, by rfl⟩ : syracuseStep 2943917 = 1103969) (by norm_num)
theorem B1962611 : Blo 1961435 1962611 := bstep (se 1 (by rfl) ⟨1471958, by rfl⟩ : syracuseStep 1962611 = 2943917) B2943917
theorem B4415885 : Blo 1961435 4415885 := bbase (se 3 (by rfl) ⟨827978, by rfl⟩ : syracuseStep 4415885 = 1655957) (by norm_num)
theorem B2943923 : Blo 1961435 2943923 := bstep (se 1 (by rfl) ⟨2207942, by rfl⟩ : syracuseStep 2943923 = 4415885) B4415885
theorem B1962615 : Blo 1961435 1962615 := bstep (se 1 (by rfl) ⟨1471961, by rfl⟩ : syracuseStep 1962615 = 2943923) B2943923
theorem B2483941 : Blo 1961435 2483941 := bbase (se 4 (by rfl) ⟨232869, by rfl⟩ : syracuseStep 2483941 = 465739) (by norm_num)
theorem B3311921 : Blo 1961435 3311921 := bstep (se 2 (by rfl) ⟨1241970, by rfl⟩ : syracuseStep 3311921 = 2483941) B2483941
theorem B2207947 : Blo 1961435 2207947 := bstep (se 1 (by rfl) ⟨1655960, by rfl⟩ : syracuseStep 2207947 = 3311921) B3311921
theorem B2943929 : Blo 1961435 2943929 := bstep (se 2 (by rfl) ⟨1103973, by rfl⟩ : syracuseStep 2943929 = 2207947) B2207947
theorem B1962619 : Blo 1961435 1962619 := bstep (se 1 (by rfl) ⟨1471964, by rfl⟩ : syracuseStep 1962619 = 2943929) B2943929
theorem B11936405 : Blo 1961435 11936405 := bbase (se 6 (by rfl) ⟨279759, by rfl⟩ : syracuseStep 11936405 = 559519) (by norm_num)
theorem B7957603 : Blo 1961435 7957603 := bstep (se 1 (by rfl) ⟨5968202, by rfl⟩ : syracuseStep 7957603 = 11936405) B11936405
theorem B10610137 : Blo 1961435 10610137 := bstep (se 2 (by rfl) ⟨3978801, by rfl⟩ : syracuseStep 10610137 = 7957603) B7957603
theorem B14146849 : Blo 1961435 14146849 := bstep (se 2 (by rfl) ⟨5305068, by rfl⟩ : syracuseStep 14146849 = 10610137) B10610137
theorem B18862465 : Blo 1961435 18862465 := bstep (se 2 (by rfl) ⟨7073424, by rfl⟩ : syracuseStep 18862465 = 14146849) B14146849
theorem B25149953 : Blo 1961435 25149953 := bstep (se 2 (by rfl) ⟨9431232, by rfl⟩ : syracuseStep 25149953 = 18862465) B18862465
theorem B16766635 : Blo 1961435 16766635 := bstep (se 1 (by rfl) ⟨12574976, by rfl⟩ : syracuseStep 16766635 = 25149953) B25149953
theorem B22355513 : Blo 1961435 22355513 := bstep (se 2 (by rfl) ⟨8383317, by rfl⟩ : syracuseStep 22355513 = 16766635) B16766635
theorem B14903675 : Blo 1961435 14903675 := bstep (se 1 (by rfl) ⟨11177756, by rfl⟩ : syracuseStep 14903675 = 22355513) B22355513
theorem B9935783 : Blo 1961435 9935783 := bstep (se 1 (by rfl) ⟨7451837, by rfl⟩ : syracuseStep 9935783 = 14903675) B14903675
theorem B6623855 : Blo 1961435 6623855 := bstep (se 1 (by rfl) ⟨4967891, by rfl⟩ : syracuseStep 6623855 = 9935783) B9935783
theorem B4415903 : Blo 1961435 4415903 := bstep (se 1 (by rfl) ⟨3311927, by rfl⟩ : syracuseStep 4415903 = 6623855) B6623855
theorem B2943935 : Blo 1961435 2943935 := bstep (se 1 (by rfl) ⟨2207951, by rfl⟩ : syracuseStep 2943935 = 4415903) B4415903
theorem B1962623 : Blo 1961435 1962623 := bstep (se 1 (by rfl) ⟨1471967, by rfl⟩ : syracuseStep 1962623 = 2943935) B2943935
theorem B2943941 : Blo 1961435 2943941 := bbase (se 4 (by rfl) ⟨275994, by rfl⟩ : syracuseStep 2943941 = 551989) (by norm_num)
theorem B1962627 : Blo 1961435 1962627 := bstep (se 1 (by rfl) ⟨1471970, by rfl⟩ : syracuseStep 1962627 = 2943941) B2943941
theorem B3311941 : Blo 1961435 3311941 := bbase (se 4 (by rfl) ⟨310494, by rfl⟩ : syracuseStep 3311941 = 620989) (by norm_num)
theorem B4415921 : Blo 1961435 4415921 := bstep (se 2 (by rfl) ⟨1655970, by rfl⟩ : syracuseStep 4415921 = 3311941) B3311941
theorem B2943947 : Blo 1961435 2943947 := bstep (se 1 (by rfl) ⟨2207960, by rfl⟩ : syracuseStep 2943947 = 4415921) B4415921
theorem B1962631 : Blo 1961435 1962631 := bstep (se 1 (by rfl) ⟨1471973, by rfl⟩ : syracuseStep 1962631 = 2943947) B2943947
theorem B2207965 : Blo 1961435 2207965 := bbase (se 3 (by rfl) ⟨413993, by rfl⟩ : syracuseStep 2207965 = 827987) (by norm_num)
theorem B2943953 : Blo 1961435 2943953 := bstep (se 2 (by rfl) ⟨1103982, by rfl⟩ : syracuseStep 2943953 = 2207965) B2207965
theorem B1962635 : Blo 1961435 1962635 := bstep (se 1 (by rfl) ⟨1471976, by rfl⟩ : syracuseStep 1962635 = 2943953) B2943953
theorem B6623909 : Blo 1961435 6623909 := bbase (se 4 (by rfl) ⟨620991, by rfl⟩ : syracuseStep 6623909 = 1241983) (by norm_num)
theorem B4415939 : Blo 1961435 4415939 := bstep (se 1 (by rfl) ⟨3311954, by rfl⟩ : syracuseStep 4415939 = 6623909) B6623909
theorem B2943959 : Blo 1961435 2943959 := bstep (se 1 (by rfl) ⟨2207969, by rfl⟩ : syracuseStep 2943959 = 4415939) B4415939
theorem B1962639 : Blo 1961435 1962639 := bstep (se 1 (by rfl) ⟨1471979, by rfl⟩ : syracuseStep 1962639 = 2943959) B2943959
theorem B2943965 : Blo 1961435 2943965 := bbase (se 3 (by rfl) ⟨551993, by rfl⟩ : syracuseStep 2943965 = 1103987) (by norm_num)
theorem B1962643 : Blo 1961435 1962643 := bstep (se 1 (by rfl) ⟨1471982, by rfl⟩ : syracuseStep 1962643 = 2943965) B2943965
theorem B4415957 : Blo 1961435 4415957 := bbase (se 7 (by rfl) ⟨51749, by rfl⟩ : syracuseStep 4415957 = 103499) (by norm_num)
theorem B2943971 : Blo 1961435 2943971 := bstep (se 1 (by rfl) ⟨2207978, by rfl⟩ : syracuseStep 2943971 = 4415957) B4415957
theorem B1962647 : Blo 1961435 1962647 := bstep (se 1 (by rfl) ⟨1471985, by rfl⟩ : syracuseStep 1962647 = 2943971) B2943971
theorem B5104453 : Blo 1961435 5104453 := bbase (se 4 (by rfl) ⟨478542, by rfl⟩ : syracuseStep 5104453 = 957085) (by norm_num)
theorem B6805937 : Blo 1961435 6805937 := bstep (se 2 (by rfl) ⟨2552226, by rfl⟩ : syracuseStep 6805937 = 5104453) B5104453
theorem B4537291 : Blo 1961435 4537291 := bstep (se 1 (by rfl) ⟨3402968, by rfl⟩ : syracuseStep 4537291 = 6805937) B6805937
theorem B6049721 : Blo 1961435 6049721 := bstep (se 2 (by rfl) ⟨2268645, by rfl⟩ : syracuseStep 6049721 = 4537291) B4537291
theorem B4033147 : Blo 1961435 4033147 := bstep (se 1 (by rfl) ⟨3024860, by rfl⟩ : syracuseStep 4033147 = 6049721) B6049721
theorem B5377529 : Blo 1961435 5377529 := bstep (se 2 (by rfl) ⟨2016573, by rfl⟩ : syracuseStep 5377529 = 4033147) B4033147
theorem B14340077 : Blo 1961435 14340077 := bstep (se 3 (by rfl) ⟨2688764, by rfl⟩ : syracuseStep 14340077 = 5377529) B5377529
theorem B9560051 : Blo 1961435 9560051 := bstep (se 1 (by rfl) ⟨7170038, by rfl⟩ : syracuseStep 9560051 = 14340077) B14340077
theorem B6373367 : Blo 1961435 6373367 := bstep (se 1 (by rfl) ⟨4780025, by rfl⟩ : syracuseStep 6373367 = 9560051) B9560051
theorem B4248911 : Blo 1961435 4248911 := bstep (se 1 (by rfl) ⟨3186683, by rfl⟩ : syracuseStep 4248911 = 6373367) B6373367
theorem B2832607 : Blo 1961435 2832607 := bstep (se 1 (by rfl) ⟨2124455, by rfl⟩ : syracuseStep 2832607 = 4248911) B4248911
theorem B3776809 : Blo 1961435 3776809 := bstep (se 2 (by rfl) ⟨1416303, by rfl⟩ : syracuseStep 3776809 = 2832607) B2832607
theorem B5035745 : Blo 1961435 5035745 := bstep (se 2 (by rfl) ⟨1888404, by rfl⟩ : syracuseStep 5035745 = 3776809) B3776809
theorem B3357163 : Blo 1961435 3357163 := bstep (se 1 (by rfl) ⟨2517872, by rfl⟩ : syracuseStep 3357163 = 5035745) B5035745
theorem B4476217 : Blo 1961435 4476217 := bstep (se 2 (by rfl) ⟨1678581, by rfl⟩ : syracuseStep 4476217 = 3357163) B3357163
theorem B5968289 : Blo 1961435 5968289 := bstep (se 2 (by rfl) ⟨2238108, by rfl⟩ : syracuseStep 5968289 = 4476217) B4476217
theorem B15915437 : Blo 1961435 15915437 := bstep (se 3 (by rfl) ⟨2984144, by rfl⟩ : syracuseStep 15915437 = 5968289) B5968289
theorem B10610291 : Blo 1961435 10610291 := bstep (se 1 (by rfl) ⟨7957718, by rfl⟩ : syracuseStep 10610291 = 15915437) B15915437
theorem B28294109 : Blo 1961435 28294109 := bstep (se 3 (by rfl) ⟨5305145, by rfl⟩ : syracuseStep 28294109 = 10610291) B10610291
theorem B18862739 : Blo 1961435 18862739 := bstep (se 1 (by rfl) ⟨14147054, by rfl⟩ : syracuseStep 18862739 = 28294109) B28294109
theorem B12575159 : Blo 1961435 12575159 := bstep (se 1 (by rfl) ⟨9431369, by rfl⟩ : syracuseStep 12575159 = 18862739) B18862739
theorem B8383439 : Blo 1961435 8383439 := bstep (se 1 (by rfl) ⟨6287579, by rfl⟩ : syracuseStep 8383439 = 12575159) B12575159
theorem B5588959 : Blo 1961435 5588959 := bstep (se 1 (by rfl) ⟨4191719, by rfl⟩ : syracuseStep 5588959 = 8383439) B8383439
theorem B7451945 : Blo 1961435 7451945 := bstep (se 2 (by rfl) ⟨2794479, by rfl⟩ : syracuseStep 7451945 = 5588959) B5588959
theorem B4967963 : Blo 1961435 4967963 := bstep (se 1 (by rfl) ⟨3725972, by rfl⟩ : syracuseStep 4967963 = 7451945) B7451945
theorem B3311975 : Blo 1961435 3311975 := bstep (se 1 (by rfl) ⟨2483981, by rfl⟩ : syracuseStep 3311975 = 4967963) B4967963
theorem B2207983 : Blo 1961435 2207983 := bstep (se 1 (by rfl) ⟨1655987, by rfl⟩ : syracuseStep 2207983 = 3311975) B3311975
theorem B2943977 : Blo 1961435 2943977 := bstep (se 2 (by rfl) ⟨1103991, by rfl⟩ : syracuseStep 2943977 = 2207983) B2207983
theorem B1962651 : Blo 1961435 1962651 := bstep (se 1 (by rfl) ⟨1471988, by rfl⟩ : syracuseStep 1962651 = 2943977) B2943977
theorem B2517877 : Blo 1961435 2517877 := bbase (se 5 (by rfl) ⟨118025, by rfl⟩ : syracuseStep 2517877 = 236051) (by norm_num)
theorem B3357169 : Blo 1961435 3357169 := bstep (se 2 (by rfl) ⟨1258938, by rfl⟩ : syracuseStep 3357169 = 2517877) B2517877
theorem B17904901 : Blo 1961435 17904901 := bstep (se 4 (by rfl) ⟨1678584, by rfl⟩ : syracuseStep 17904901 = 3357169) B3357169
theorem B23873201 : Blo 1961435 23873201 := bstep (se 2 (by rfl) ⟨8952450, by rfl⟩ : syracuseStep 23873201 = 17904901) B17904901
theorem B15915467 : Blo 1961435 15915467 := bstep (se 1 (by rfl) ⟨11936600, by rfl⟩ : syracuseStep 15915467 = 23873201) B23873201
theorem B10610311 : Blo 1961435 10610311 := bstep (se 1 (by rfl) ⟨7957733, by rfl⟩ : syracuseStep 10610311 = 15915467) B15915467
theorem B14147081 : Blo 1961435 14147081 := bstep (se 2 (by rfl) ⟨5305155, by rfl⟩ : syracuseStep 14147081 = 10610311) B10610311
theorem B9431387 : Blo 1961435 9431387 := bstep (se 1 (by rfl) ⟨7073540, by rfl⟩ : syracuseStep 9431387 = 14147081) B14147081
theorem B6287591 : Blo 1961435 6287591 := bstep (se 1 (by rfl) ⟨4715693, by rfl⟩ : syracuseStep 6287591 = 9431387) B9431387
theorem B16766909 : Blo 1961435 16766909 := bstep (se 3 (by rfl) ⟨3143795, by rfl⟩ : syracuseStep 16766909 = 6287591) B6287591
theorem B11177939 : Blo 1961435 11177939 := bstep (se 1 (by rfl) ⟨8383454, by rfl⟩ : syracuseStep 11177939 = 16766909) B16766909
theorem B7451959 : Blo 1961435 7451959 := bstep (se 1 (by rfl) ⟨5588969, by rfl⟩ : syracuseStep 7451959 = 11177939) B11177939
theorem B9935945 : Blo 1961435 9935945 := bstep (se 2 (by rfl) ⟨3725979, by rfl⟩ : syracuseStep 9935945 = 7451959) B7451959
theorem B6623963 : Blo 1961435 6623963 := bstep (se 1 (by rfl) ⟨4967972, by rfl⟩ : syracuseStep 6623963 = 9935945) B9935945
theorem B4415975 : Blo 1961435 4415975 := bstep (se 1 (by rfl) ⟨3311981, by rfl⟩ : syracuseStep 4415975 = 6623963) B6623963
theorem B2943983 : Blo 1961435 2943983 := bstep (se 1 (by rfl) ⟨2207987, by rfl⟩ : syracuseStep 2943983 = 4415975) B4415975
theorem B1962655 : Blo 1961435 1962655 := bstep (se 1 (by rfl) ⟨1471991, by rfl⟩ : syracuseStep 1962655 = 2943983) B2943983
theorem B2943989 : Blo 1961435 2943989 := bbase (se 5 (by rfl) ⟨137999, by rfl⟩ : syracuseStep 2943989 = 275999) (by norm_num)
theorem B1962659 : Blo 1961435 1962659 := bstep (se 1 (by rfl) ⟨1471994, by rfl⟩ : syracuseStep 1962659 = 2943989) B2943989
theorem B2357857 : Blo 1961435 2357857 := bbase (se 2 (by rfl) ⟨884196, by rfl⟩ : syracuseStep 2357857 = 1768393) (by norm_num)
theorem B3143809 : Blo 1961435 3143809 := bstep (se 2 (by rfl) ⟨1178928, by rfl⟩ : syracuseStep 3143809 = 2357857) B2357857
theorem B4191745 : Blo 1961435 4191745 := bstep (se 2 (by rfl) ⟨1571904, by rfl⟩ : syracuseStep 4191745 = 3143809) B3143809
theorem B5588993 : Blo 1961435 5588993 := bstep (se 2 (by rfl) ⟨2095872, by rfl⟩ : syracuseStep 5588993 = 4191745) B4191745
theorem B3725995 : Blo 1961435 3725995 := bstep (se 1 (by rfl) ⟨2794496, by rfl⟩ : syracuseStep 3725995 = 5588993) B5588993
theorem B4967993 : Blo 1961435 4967993 := bstep (se 2 (by rfl) ⟨1862997, by rfl⟩ : syracuseStep 4967993 = 3725995) B3725995
theorem B3311995 : Blo 1961435 3311995 := bstep (se 1 (by rfl) ⟨2483996, by rfl⟩ : syracuseStep 3311995 = 4967993) B4967993
theorem B4415993 : Blo 1961435 4415993 := bstep (se 2 (by rfl) ⟨1655997, by rfl⟩ : syracuseStep 4415993 = 3311995) B3311995
theorem B2943995 : Blo 1961435 2943995 := bstep (se 1 (by rfl) ⟨2207996, by rfl⟩ : syracuseStep 2943995 = 4415993) B4415993
theorem B1962663 : Blo 1961435 1962663 := bstep (se 1 (by rfl) ⟨1471997, by rfl⟩ : syracuseStep 1962663 = 2943995) B2943995
theorem B2208001 : Blo 1961435 2208001 := bbase (se 2 (by rfl) ⟨828000, by rfl⟩ : syracuseStep 2208001 = 1656001) (by norm_num)
theorem B2944001 : Blo 1961435 2944001 := bstep (se 2 (by rfl) ⟨1104000, by rfl⟩ : syracuseStep 2944001 = 2208001) B2208001
theorem B1962667 : Blo 1961435 1962667 := bstep (se 1 (by rfl) ⟨1472000, by rfl⟩ : syracuseStep 1962667 = 2944001) B2944001
theorem B4968013 : Blo 1961435 4968013 := bbase (se 3 (by rfl) ⟨931502, by rfl⟩ : syracuseStep 4968013 = 1863005) (by norm_num)
theorem B6624017 : Blo 1961435 6624017 := bstep (se 2 (by rfl) ⟨2484006, by rfl⟩ : syracuseStep 6624017 = 4968013) B4968013
theorem B4416011 : Blo 1961435 4416011 := bstep (se 1 (by rfl) ⟨3312008, by rfl⟩ : syracuseStep 4416011 = 6624017) B6624017
theorem B2944007 : Blo 1961435 2944007 := bstep (se 1 (by rfl) ⟨2208005, by rfl⟩ : syracuseStep 2944007 = 4416011) B4416011
theorem B1962671 : Blo 1961435 1962671 := bstep (se 1 (by rfl) ⟨1472003, by rfl⟩ : syracuseStep 1962671 = 2944007) B2944007
theorem B2944013 : Blo 1961435 2944013 := bbase (se 3 (by rfl) ⟨552002, by rfl⟩ : syracuseStep 2944013 = 1104005) (by norm_num)
theorem B1962675 : Blo 1961435 1962675 := bstep (se 1 (by rfl) ⟨1472006, by rfl⟩ : syracuseStep 1962675 = 2944013) B2944013
theorem B4416029 : Blo 1961435 4416029 := bbase (se 3 (by rfl) ⟨828005, by rfl⟩ : syracuseStep 4416029 = 1656011) (by norm_num)
theorem B2944019 : Blo 1961435 2944019 := bstep (se 1 (by rfl) ⟨2208014, by rfl⟩ : syracuseStep 2944019 = 4416029) B4416029
theorem B1962679 : Blo 1961435 1962679 := bstep (se 1 (by rfl) ⟨1472009, by rfl⟩ : syracuseStep 1962679 = 2944019) B2944019
theorem B3312029 : Blo 1961435 3312029 := bbase (se 3 (by rfl) ⟨621005, by rfl⟩ : syracuseStep 3312029 = 1242011) (by norm_num)
theorem B2208019 : Blo 1961435 2208019 := bstep (se 1 (by rfl) ⟨1656014, by rfl⟩ : syracuseStep 2208019 = 3312029) B3312029
theorem B2944025 : Blo 1961435 2944025 := bstep (se 2 (by rfl) ⟨1104009, by rfl⟩ : syracuseStep 2944025 = 2208019) B2208019
theorem B1962683 : Blo 1961435 1962683 := bstep (se 1 (by rfl) ⟨1472012, by rfl⟩ : syracuseStep 1962683 = 2944025) B2944025
theorem B2124493 : Blo 1961435 2124493 := bbase (se 3 (by rfl) ⟨398342, by rfl⟩ : syracuseStep 2124493 = 796685) (by norm_num)
theorem B45322517 : Blo 1961435 45322517 := bstep (se 6 (by rfl) ⟨1062246, by rfl⟩ : syracuseStep 45322517 = 2124493) B2124493
theorem B120860045 : Blo 1961435 120860045 := bstep (se 3 (by rfl) ⟨22661258, by rfl⟩ : syracuseStep 120860045 = 45322517) B45322517
theorem B80573363 : Blo 1961435 80573363 := bstep (se 1 (by rfl) ⟨60430022, by rfl⟩ : syracuseStep 80573363 = 120860045) B120860045
theorem B53715575 : Blo 1961435 53715575 := bstep (se 1 (by rfl) ⟨40286681, by rfl⟩ : syracuseStep 53715575 = 80573363) B80573363
theorem B35810383 : Blo 1961435 35810383 := bstep (se 1 (by rfl) ⟨26857787, by rfl⟩ : syracuseStep 35810383 = 53715575) B53715575
theorem B47747177 : Blo 1961435 47747177 := bstep (se 2 (by rfl) ⟨17905191, by rfl⟩ : syracuseStep 47747177 = 35810383) B35810383
theorem B31831451 : Blo 1961435 31831451 := bstep (se 1 (by rfl) ⟨23873588, by rfl⟩ : syracuseStep 31831451 = 47747177) B47747177
theorem B21220967 : Blo 1961435 21220967 := bstep (se 1 (by rfl) ⟨15915725, by rfl⟩ : syracuseStep 21220967 = 31831451) B31831451
theorem B14147311 : Blo 1961435 14147311 := bstep (se 1 (by rfl) ⟨10610483, by rfl⟩ : syracuseStep 14147311 = 21220967) B21220967
theorem B18863081 : Blo 1961435 18863081 := bstep (se 2 (by rfl) ⟨7073655, by rfl⟩ : syracuseStep 18863081 = 14147311) B14147311
theorem B12575387 : Blo 1961435 12575387 := bstep (se 1 (by rfl) ⟨9431540, by rfl⟩ : syracuseStep 12575387 = 18863081) B18863081
theorem B8383591 : Blo 1961435 8383591 := bstep (se 1 (by rfl) ⟨6287693, by rfl⟩ : syracuseStep 8383591 = 12575387) B12575387
theorem B11178121 : Blo 1961435 11178121 := bstep (se 2 (by rfl) ⟨4191795, by rfl⟩ : syracuseStep 11178121 = 8383591) B8383591
theorem B14904161 : Blo 1961435 14904161 := bstep (se 2 (by rfl) ⟨5589060, by rfl⟩ : syracuseStep 14904161 = 11178121) B11178121
theorem B9936107 : Blo 1961435 9936107 := bstep (se 1 (by rfl) ⟨7452080, by rfl⟩ : syracuseStep 9936107 = 14904161) B14904161
theorem B6624071 : Blo 1961435 6624071 := bstep (se 1 (by rfl) ⟨4968053, by rfl⟩ : syracuseStep 6624071 = 9936107) B9936107
theorem B4416047 : Blo 1961435 4416047 := bstep (se 1 (by rfl) ⟨3312035, by rfl⟩ : syracuseStep 4416047 = 6624071) B6624071
theorem B2944031 : Blo 1961435 2944031 := bstep (se 1 (by rfl) ⟨2208023, by rfl⟩ : syracuseStep 2944031 = 4416047) B4416047
theorem B1962687 : Blo 1961435 1962687 := bstep (se 1 (by rfl) ⟨1472015, by rfl⟩ : syracuseStep 1962687 = 2944031) B2944031
theorem B2944037 : Blo 1961435 2944037 := bbase (se 4 (by rfl) ⟨276003, by rfl⟩ : syracuseStep 2944037 = 552007) (by norm_num)
theorem B1962691 : Blo 1961435 1962691 := bstep (se 1 (by rfl) ⟨1472018, by rfl⟩ : syracuseStep 1962691 = 2944037) B2944037
theorem B2484037 : Blo 1961435 2484037 := bbase (se 4 (by rfl) ⟨232878, by rfl⟩ : syracuseStep 2484037 = 465757) (by norm_num)
theorem B3312049 : Blo 1961435 3312049 := bstep (se 2 (by rfl) ⟨1242018, by rfl⟩ : syracuseStep 3312049 = 2484037) B2484037
theorem B4416065 : Blo 1961435 4416065 := bstep (se 2 (by rfl) ⟨1656024, by rfl⟩ : syracuseStep 4416065 = 3312049) B3312049
theorem B2944043 : Blo 1961435 2944043 := bstep (se 1 (by rfl) ⟨2208032, by rfl⟩ : syracuseStep 2944043 = 4416065) B4416065
theorem B1962695 : Blo 1961435 1962695 := bstep (se 1 (by rfl) ⟨1472021, by rfl⟩ : syracuseStep 1962695 = 2944043) B2944043
theorem B2208037 : Blo 1961435 2208037 := bbase (se 4 (by rfl) ⟨207003, by rfl⟩ : syracuseStep 2208037 = 414007) (by norm_num)
theorem B2944049 : Blo 1961435 2944049 := bstep (se 2 (by rfl) ⟨1104018, by rfl⟩ : syracuseStep 2944049 = 2208037) B2208037
theorem B1962699 : Blo 1961435 1962699 := bstep (se 1 (by rfl) ⟨1472024, by rfl⟩ : syracuseStep 1962699 = 2944049) B2944049
theorem B2357905 : Blo 1961435 2357905 := bbase (se 2 (by rfl) ⟨884214, by rfl⟩ : syracuseStep 2357905 = 1768429) (by norm_num)
theorem B3143873 : Blo 1961435 3143873 := bstep (se 2 (by rfl) ⟨1178952, by rfl⟩ : syracuseStep 3143873 = 2357905) B2357905
theorem B8383661 : Blo 1961435 8383661 := bstep (se 3 (by rfl) ⟨1571936, by rfl⟩ : syracuseStep 8383661 = 3143873) B3143873
theorem B5589107 : Blo 1961435 5589107 := bstep (se 1 (by rfl) ⟨4191830, by rfl⟩ : syracuseStep 5589107 = 8383661) B8383661
theorem B3726071 : Blo 1961435 3726071 := bstep (se 1 (by rfl) ⟨2794553, by rfl⟩ : syracuseStep 3726071 = 5589107) B5589107
theorem B2484047 : Blo 1961435 2484047 := bstep (se 1 (by rfl) ⟨1863035, by rfl⟩ : syracuseStep 2484047 = 3726071) B3726071
theorem B6624125 : Blo 1961435 6624125 := bstep (se 3 (by rfl) ⟨1242023, by rfl⟩ : syracuseStep 6624125 = 2484047) B2484047
theorem B4416083 : Blo 1961435 4416083 := bstep (se 1 (by rfl) ⟨3312062, by rfl⟩ : syracuseStep 4416083 = 6624125) B6624125
theorem B2944055 : Blo 1961435 2944055 := bstep (se 1 (by rfl) ⟨2208041, by rfl⟩ : syracuseStep 2944055 = 4416083) B4416083
theorem B1962703 : Blo 1961435 1962703 := bstep (se 1 (by rfl) ⟨1472027, by rfl⟩ : syracuseStep 1962703 = 2944055) B2944055
theorem B2944061 : Blo 1961435 2944061 := bbase (se 3 (by rfl) ⟨552011, by rfl⟩ : syracuseStep 2944061 = 1104023) (by norm_num)
theorem B1962707 : Blo 1961435 1962707 := bstep (se 1 (by rfl) ⟨1472030, by rfl⟩ : syracuseStep 1962707 = 2944061) B2944061
theorem B4416101 : Blo 1961435 4416101 := bbase (se 4 (by rfl) ⟨414009, by rfl⟩ : syracuseStep 4416101 = 828019) (by norm_num)
theorem B2944067 : Blo 1961435 2944067 := bstep (se 1 (by rfl) ⟨2208050, by rfl⟩ : syracuseStep 2944067 = 4416101) B4416101
theorem B1962711 : Blo 1961435 1962711 := bstep (se 1 (by rfl) ⟨1472033, by rfl⟩ : syracuseStep 1962711 = 2944067) B2944067
theorem B4968125 : Blo 1961435 4968125 := bbase (se 3 (by rfl) ⟨931523, by rfl⟩ : syracuseStep 4968125 = 1863047) (by norm_num)
theorem B3312083 : Blo 1961435 3312083 := bstep (se 1 (by rfl) ⟨2484062, by rfl⟩ : syracuseStep 3312083 = 4968125) B4968125
theorem B2208055 : Blo 1961435 2208055 := bstep (se 1 (by rfl) ⟨1656041, by rfl⟩ : syracuseStep 2208055 = 3312083) B3312083
theorem B2944073 : Blo 1961435 2944073 := bstep (se 2 (by rfl) ⟨1104027, by rfl⟩ : syracuseStep 2944073 = 2208055) B2208055
theorem B1962715 : Blo 1961435 1962715 := bstep (se 1 (by rfl) ⟨1472036, by rfl⟩ : syracuseStep 1962715 = 2944073) B2944073
theorem B3726101 : Blo 1961435 3726101 := bbase (se 6 (by rfl) ⟨87330, by rfl⟩ : syracuseStep 3726101 = 174661) (by norm_num)
theorem B9936269 : Blo 1961435 9936269 := bstep (se 3 (by rfl) ⟨1863050, by rfl⟩ : syracuseStep 9936269 = 3726101) B3726101
theorem B6624179 : Blo 1961435 6624179 := bstep (se 1 (by rfl) ⟨4968134, by rfl⟩ : syracuseStep 6624179 = 9936269) B9936269
theorem B4416119 : Blo 1961435 4416119 := bstep (se 1 (by rfl) ⟨3312089, by rfl⟩ : syracuseStep 4416119 = 6624179) B6624179
theorem B2944079 : Blo 1961435 2944079 := bstep (se 1 (by rfl) ⟨2208059, by rfl⟩ : syracuseStep 2944079 = 4416119) B4416119
theorem B1962719 : Blo 1961435 1962719 := bstep (se 1 (by rfl) ⟨1472039, by rfl⟩ : syracuseStep 1962719 = 2944079) B2944079
theorem B2944085 : Blo 1961435 2944085 := bbase (se 8 (by rfl) ⟨17250, by rfl⟩ : syracuseStep 2944085 = 34501) (by norm_num)
theorem B1962723 : Blo 1961435 1962723 := bstep (se 1 (by rfl) ⟨1472042, by rfl⟩ : syracuseStep 1962723 = 2944085) B2944085
theorem B3357293 : Blo 1961435 3357293 := bbase (se 3 (by rfl) ⟨629492, by rfl⟩ : syracuseStep 3357293 = 1258985) (by norm_num)
theorem B8952781 : Blo 1961435 8952781 := bstep (se 3 (by rfl) ⟨1678646, by rfl⟩ : syracuseStep 8952781 = 3357293) B3357293
theorem B11937041 : Blo 1961435 11937041 := bstep (se 2 (by rfl) ⟨4476390, by rfl⟩ : syracuseStep 11937041 = 8952781) B8952781
theorem B7958027 : Blo 1961435 7958027 := bstep (se 1 (by rfl) ⟨5968520, by rfl⟩ : syracuseStep 7958027 = 11937041) B11937041
theorem B5305351 : Blo 1961435 5305351 := bstep (se 1 (by rfl) ⟨3979013, by rfl⟩ : syracuseStep 5305351 = 7958027) B7958027
theorem B7073801 : Blo 1961435 7073801 := bstep (se 2 (by rfl) ⟨2652675, by rfl⟩ : syracuseStep 7073801 = 5305351) B5305351
theorem B4715867 : Blo 1961435 4715867 := bstep (se 1 (by rfl) ⟨3536900, by rfl⟩ : syracuseStep 4715867 = 7073801) B7073801
theorem B12575645 : Blo 1961435 12575645 := bstep (se 3 (by rfl) ⟨2357933, by rfl⟩ : syracuseStep 12575645 = 4715867) B4715867
theorem B8383763 : Blo 1961435 8383763 := bstep (se 1 (by rfl) ⟨6287822, by rfl⟩ : syracuseStep 8383763 = 12575645) B12575645
theorem B5589175 : Blo 1961435 5589175 := bstep (se 1 (by rfl) ⟨4191881, by rfl⟩ : syracuseStep 5589175 = 8383763) B8383763
theorem B7452233 : Blo 1961435 7452233 := bstep (se 2 (by rfl) ⟨2794587, by rfl⟩ : syracuseStep 7452233 = 5589175) B5589175
theorem B4968155 : Blo 1961435 4968155 := bstep (se 1 (by rfl) ⟨3726116, by rfl⟩ : syracuseStep 4968155 = 7452233) B7452233
theorem B3312103 : Blo 1961435 3312103 := bstep (se 1 (by rfl) ⟨2484077, by rfl⟩ : syracuseStep 3312103 = 4968155) B4968155
theorem B4416137 : Blo 1961435 4416137 := bstep (se 2 (by rfl) ⟨1656051, by rfl⟩ : syracuseStep 4416137 = 3312103) B3312103
theorem B2944091 : Blo 1961435 2944091 := bstep (se 1 (by rfl) ⟨2208068, by rfl⟩ : syracuseStep 2944091 = 4416137) B4416137
theorem B1962727 : Blo 1961435 1962727 := bstep (se 1 (by rfl) ⟨1472045, by rfl⟩ : syracuseStep 1962727 = 2944091) B2944091
theorem B2208073 : Blo 1961435 2208073 := bbase (se 2 (by rfl) ⟨828027, by rfl⟩ : syracuseStep 2208073 = 1656055) (by norm_num)
theorem B2944097 : Blo 1961435 2944097 := bstep (se 2 (by rfl) ⟨1104036, by rfl⟩ : syracuseStep 2944097 = 2208073) B2208073
theorem B1962731 : Blo 1961435 1962731 := bstep (se 1 (by rfl) ⟨1472048, by rfl⟩ : syracuseStep 1962731 = 2944097) B2944097
theorem B4725749 : Blo 1961435 4725749 := bbase (se 5 (by rfl) ⟨221519, by rfl⟩ : syracuseStep 4725749 = 443039) (by norm_num)
theorem B3150499 : Blo 1961435 3150499 := bstep (se 1 (by rfl) ⟨2362874, by rfl⟩ : syracuseStep 3150499 = 4725749) B4725749
theorem B4200665 : Blo 1961435 4200665 := bstep (se 2 (by rfl) ⟨1575249, by rfl⟩ : syracuseStep 4200665 = 3150499) B3150499
theorem B11201773 : Blo 1961435 11201773 := bstep (se 3 (by rfl) ⟨2100332, by rfl⟩ : syracuseStep 11201773 = 4200665) B4200665
theorem B14935697 : Blo 1961435 14935697 := bstep (se 2 (by rfl) ⟨5600886, by rfl⟩ : syracuseStep 14935697 = 11201773) B11201773
theorem B9957131 : Blo 1961435 9957131 := bstep (se 1 (by rfl) ⟨7467848, by rfl⟩ : syracuseStep 9957131 = 14935697) B14935697
theorem B6638087 : Blo 1961435 6638087 := bstep (se 1 (by rfl) ⟨4978565, by rfl⟩ : syracuseStep 6638087 = 9957131) B9957131
theorem B4425391 : Blo 1961435 4425391 := bstep (se 1 (by rfl) ⟨3319043, by rfl⟩ : syracuseStep 4425391 = 6638087) B6638087
theorem B23602085 : Blo 1961435 23602085 := bstep (se 4 (by rfl) ⟨2212695, by rfl⟩ : syracuseStep 23602085 = 4425391) B4425391
theorem B15734723 : Blo 1961435 15734723 := bstep (se 1 (by rfl) ⟨11801042, by rfl⟩ : syracuseStep 15734723 = 23602085) B23602085
theorem B41959261 : Blo 1961435 41959261 := bstep (se 3 (by rfl) ⟨7867361, by rfl⟩ : syracuseStep 41959261 = 15734723) B15734723
theorem B223782725 : Blo 1961435 223782725 := bstep (se 4 (by rfl) ⟨20979630, by rfl⟩ : syracuseStep 223782725 = 41959261) B41959261
theorem B149188483 : Blo 1961435 149188483 := bstep (se 1 (by rfl) ⟨111891362, by rfl⟩ : syracuseStep 149188483 = 223782725) B223782725
theorem B198917977 : Blo 1961435 198917977 := bstep (se 2 (by rfl) ⟨74594241, by rfl⟩ : syracuseStep 198917977 = 149188483) B149188483
theorem B265223969 : Blo 1961435 265223969 := bstep (se 2 (by rfl) ⟨99458988, by rfl⟩ : syracuseStep 265223969 = 198917977) B198917977
theorem B176815979 : Blo 1961435 176815979 := bstep (se 1 (by rfl) ⟨132611984, by rfl⟩ : syracuseStep 176815979 = 265223969) B265223969
theorem B117877319 : Blo 1961435 117877319 := bstep (se 1 (by rfl) ⟨88407989, by rfl⟩ : syracuseStep 117877319 = 176815979) B176815979
theorem B78584879 : Blo 1961435 78584879 := bstep (se 1 (by rfl) ⟨58938659, by rfl⟩ : syracuseStep 78584879 = 117877319) B117877319
theorem B52389919 : Blo 1961435 52389919 := bstep (se 1 (by rfl) ⟨39292439, by rfl⟩ : syracuseStep 52389919 = 78584879) B78584879
theorem B69853225 : Blo 1961435 69853225 := bstep (se 2 (by rfl) ⟨26194959, by rfl⟩ : syracuseStep 69853225 = 52389919) B52389919
theorem B93137633 : Blo 1961435 93137633 := bstep (se 2 (by rfl) ⟨34926612, by rfl⟩ : syracuseStep 93137633 = 69853225) B69853225
theorem B62091755 : Blo 1961435 62091755 := bstep (se 1 (by rfl) ⟨46568816, by rfl⟩ : syracuseStep 62091755 = 93137633) B93137633
theorem B41394503 : Blo 1961435 41394503 := bstep (se 1 (by rfl) ⟨31045877, by rfl⟩ : syracuseStep 41394503 = 62091755) B62091755
theorem B110385341 : Blo 1961435 110385341 := bstep (se 3 (by rfl) ⟨20697251, by rfl⟩ : syracuseStep 110385341 = 41394503) B41394503
theorem B73590227 : Blo 1961435 73590227 := bstep (se 1 (by rfl) ⟨55192670, by rfl⟩ : syracuseStep 73590227 = 110385341) B110385341
theorem B49060151 : Blo 1961435 49060151 := bstep (se 1 (by rfl) ⟨36795113, by rfl⟩ : syracuseStep 49060151 = 73590227) B73590227
theorem B32706767 : Blo 1961435 32706767 := bstep (se 1 (by rfl) ⟨24530075, by rfl⟩ : syracuseStep 32706767 = 49060151) B49060151
theorem B21804511 : Blo 1961435 21804511 := bstep (se 1 (by rfl) ⟨16353383, by rfl⟩ : syracuseStep 21804511 = 32706767) B32706767
theorem B29072681 : Blo 1961435 29072681 := bstep (se 2 (by rfl) ⟨10902255, by rfl⟩ : syracuseStep 29072681 = 21804511) B21804511
theorem B19381787 : Blo 1961435 19381787 := bstep (se 1 (by rfl) ⟨14536340, by rfl⟩ : syracuseStep 19381787 = 29072681) B29072681
theorem B12921191 : Blo 1961435 12921191 := bstep (se 1 (by rfl) ⟨9690893, by rfl⟩ : syracuseStep 12921191 = 19381787) B19381787
theorem B8614127 : Blo 1961435 8614127 := bstep (se 1 (by rfl) ⟨6460595, by rfl⟩ : syracuseStep 8614127 = 12921191) B12921191
theorem B5742751 : Blo 1961435 5742751 := bstep (se 1 (by rfl) ⟨4307063, by rfl⟩ : syracuseStep 5742751 = 8614127) B8614127
theorem B7657001 : Blo 1961435 7657001 := bstep (se 2 (by rfl) ⟨2871375, by rfl⟩ : syracuseStep 7657001 = 5742751) B5742751
theorem B5104667 : Blo 1961435 5104667 := bstep (se 1 (by rfl) ⟨3828500, by rfl⟩ : syracuseStep 5104667 = 7657001) B7657001
theorem B13612445 : Blo 1961435 13612445 := bstep (se 3 (by rfl) ⟨2552333, by rfl⟩ : syracuseStep 13612445 = 5104667) B5104667
theorem B9074963 : Blo 1961435 9074963 := bstep (se 1 (by rfl) ⟨6806222, by rfl⟩ : syracuseStep 9074963 = 13612445) B13612445
theorem B6049975 : Blo 1961435 6049975 := bstep (se 1 (by rfl) ⟨4537481, by rfl⟩ : syracuseStep 6049975 = 9074963) B9074963
theorem B8066633 : Blo 1961435 8066633 := bstep (se 2 (by rfl) ⟨3024987, by rfl⟩ : syracuseStep 8066633 = 6049975) B6049975
theorem B21511021 : Blo 1961435 21511021 := bstep (se 3 (by rfl) ⟨4033316, by rfl⟩ : syracuseStep 21511021 = 8066633) B8066633
theorem B28681361 : Blo 1961435 28681361 := bstep (se 2 (by rfl) ⟨10755510, by rfl⟩ : syracuseStep 28681361 = 21511021) B21511021
theorem B19120907 : Blo 1961435 19120907 := bstep (se 1 (by rfl) ⟨14340680, by rfl⟩ : syracuseStep 19120907 = 28681361) B28681361
theorem B50989085 : Blo 1961435 50989085 := bstep (se 3 (by rfl) ⟨9560453, by rfl⟩ : syracuseStep 50989085 = 19120907) B19120907
theorem B33992723 : Blo 1961435 33992723 := bstep (se 1 (by rfl) ⟨25494542, by rfl⟩ : syracuseStep 33992723 = 50989085) B50989085
theorem B22661815 : Blo 1961435 22661815 := bstep (se 1 (by rfl) ⟨16996361, by rfl⟩ : syracuseStep 22661815 = 33992723) B33992723
theorem B30215753 : Blo 1961435 30215753 := bstep (se 2 (by rfl) ⟨11330907, by rfl⟩ : syracuseStep 30215753 = 22661815) B22661815
theorem B20143835 : Blo 1961435 20143835 := bstep (se 1 (by rfl) ⟨15107876, by rfl⟩ : syracuseStep 20143835 = 30215753) B30215753
theorem B13429223 : Blo 1961435 13429223 := bstep (se 1 (by rfl) ⟨10071917, by rfl⟩ : syracuseStep 13429223 = 20143835) B20143835
theorem B8952815 : Blo 1961435 8952815 := bstep (se 1 (by rfl) ⟨6714611, by rfl⟩ : syracuseStep 8952815 = 13429223) B13429223
theorem B23874173 : Blo 1961435 23874173 := bstep (se 3 (by rfl) ⟨4476407, by rfl⟩ : syracuseStep 23874173 = 8952815) B8952815
theorem B15916115 : Blo 1961435 15916115 := bstep (se 1 (by rfl) ⟨11937086, by rfl⟩ : syracuseStep 15916115 = 23874173) B23874173
theorem B42442973 : Blo 1961435 42442973 := bstep (se 3 (by rfl) ⟨7958057, by rfl⟩ : syracuseStep 42442973 = 15916115) B15916115
theorem B28295315 : Blo 1961435 28295315 := bstep (se 1 (by rfl) ⟨21221486, by rfl⟩ : syracuseStep 28295315 = 42442973) B42442973
theorem B18863543 : Blo 1961435 18863543 := bstep (se 1 (by rfl) ⟨14147657, by rfl⟩ : syracuseStep 18863543 = 28295315) B28295315
theorem B12575695 : Blo 1961435 12575695 := bstep (se 1 (by rfl) ⟨9431771, by rfl⟩ : syracuseStep 12575695 = 18863543) B18863543
theorem B16767593 : Blo 1961435 16767593 := bstep (se 2 (by rfl) ⟨6287847, by rfl⟩ : syracuseStep 16767593 = 12575695) B12575695
theorem B11178395 : Blo 1961435 11178395 := bstep (se 1 (by rfl) ⟨8383796, by rfl⟩ : syracuseStep 11178395 = 16767593) B16767593
theorem B7452263 : Blo 1961435 7452263 := bstep (se 1 (by rfl) ⟨5589197, by rfl⟩ : syracuseStep 7452263 = 11178395) B11178395
theorem B4968175 : Blo 1961435 4968175 := bstep (se 1 (by rfl) ⟨3726131, by rfl⟩ : syracuseStep 4968175 = 7452263) B7452263
theorem B6624233 : Blo 1961435 6624233 := bstep (se 2 (by rfl) ⟨2484087, by rfl⟩ : syracuseStep 6624233 = 4968175) B4968175
theorem B4416155 : Blo 1961435 4416155 := bstep (se 1 (by rfl) ⟨3312116, by rfl⟩ : syracuseStep 4416155 = 6624233) B6624233
theorem B2944103 : Blo 1961435 2944103 := bstep (se 1 (by rfl) ⟨2208077, by rfl⟩ : syracuseStep 2944103 = 4416155) B4416155
theorem B1962735 : Blo 1961435 1962735 := bstep (se 1 (by rfl) ⟨1472051, by rfl⟩ : syracuseStep 1962735 = 2944103) B2944103
theorem B2944109 : Blo 1961435 2944109 := bbase (se 3 (by rfl) ⟨552020, by rfl⟩ : syracuseStep 2944109 = 1104041) (by norm_num)
theorem B1962739 : Blo 1961435 1962739 := bstep (se 1 (by rfl) ⟨1472054, by rfl⟩ : syracuseStep 1962739 = 2944109) B2944109
theorem B4416173 : Blo 1961435 4416173 := bbase (se 3 (by rfl) ⟨828032, by rfl⟩ : syracuseStep 4416173 = 1656065) (by norm_num)
theorem B2944115 : Blo 1961435 2944115 := bstep (se 1 (by rfl) ⟨2208086, by rfl⟩ : syracuseStep 2944115 = 4416173) B4416173
theorem B1962743 : Blo 1961435 1962743 := bstep (se 1 (by rfl) ⟨1472057, by rfl⟩ : syracuseStep 1962743 = 2944115) B2944115
theorem B4191925 : Blo 1961435 4191925 := bbase (se 5 (by rfl) ⟨196496, by rfl⟩ : syracuseStep 4191925 = 392993) (by norm_num)
theorem B5589233 : Blo 1961435 5589233 := bstep (se 2 (by rfl) ⟨2095962, by rfl⟩ : syracuseStep 5589233 = 4191925) B4191925
theorem B3726155 : Blo 1961435 3726155 := bstep (se 1 (by rfl) ⟨2794616, by rfl⟩ : syracuseStep 3726155 = 5589233) B5589233
theorem B2484103 : Blo 1961435 2484103 := bstep (se 1 (by rfl) ⟨1863077, by rfl⟩ : syracuseStep 2484103 = 3726155) B3726155
theorem B3312137 : Blo 1961435 3312137 := bstep (se 2 (by rfl) ⟨1242051, by rfl⟩ : syracuseStep 3312137 = 2484103) B2484103
theorem B2208091 : Blo 1961435 2208091 := bstep (se 1 (by rfl) ⟨1656068, by rfl⟩ : syracuseStep 2208091 = 3312137) B3312137
theorem B2944121 : Blo 1961435 2944121 := bstep (se 2 (by rfl) ⟨1104045, by rfl⟩ : syracuseStep 2944121 = 2208091) B2208091
theorem B1962747 : Blo 1961435 1962747 := bstep (se 1 (by rfl) ⟨1472060, by rfl⟩ : syracuseStep 1962747 = 2944121) B2944121
theorem B5104709 : Blo 1961435 5104709 := bbase (se 4 (by rfl) ⟨478566, by rfl⟩ : syracuseStep 5104709 = 957133) (by norm_num)
theorem B3403139 : Blo 1961435 3403139 := bstep (se 1 (by rfl) ⟨2552354, by rfl⟩ : syracuseStep 3403139 = 5104709) B5104709
theorem B9075037 : Blo 1961435 9075037 := bstep (se 3 (by rfl) ⟨1701569, by rfl⟩ : syracuseStep 9075037 = 3403139) B3403139
theorem B12100049 : Blo 1961435 12100049 := bstep (se 2 (by rfl) ⟨4537518, by rfl⟩ : syracuseStep 12100049 = 9075037) B9075037
theorem B8066699 : Blo 1961435 8066699 := bstep (se 1 (by rfl) ⟨6050024, by rfl⟩ : syracuseStep 8066699 = 12100049) B12100049
theorem B5377799 : Blo 1961435 5377799 := bstep (se 1 (by rfl) ⟨4033349, by rfl⟩ : syracuseStep 5377799 = 8066699) B8066699
theorem B14340797 : Blo 1961435 14340797 := bstep (se 3 (by rfl) ⟨2688899, by rfl⟩ : syracuseStep 14340797 = 5377799) B5377799
theorem B9560531 : Blo 1961435 9560531 := bstep (se 1 (by rfl) ⟨7170398, by rfl⟩ : syracuseStep 9560531 = 14340797) B14340797
theorem B25494749 : Blo 1961435 25494749 := bstep (se 3 (by rfl) ⟨4780265, by rfl⟩ : syracuseStep 25494749 = 9560531) B9560531
theorem B16996499 : Blo 1961435 16996499 := bstep (se 1 (by rfl) ⟨12747374, by rfl⟩ : syracuseStep 16996499 = 25494749) B25494749
theorem B11330999 : Blo 1961435 11330999 := bstep (se 1 (by rfl) ⟨8498249, by rfl⟩ : syracuseStep 11330999 = 16996499) B16996499
theorem B7553999 : Blo 1961435 7553999 := bstep (se 1 (by rfl) ⟨5665499, by rfl⟩ : syracuseStep 7553999 = 11330999) B11330999
theorem B20143997 : Blo 1961435 20143997 := bstep (se 3 (by rfl) ⟨3776999, by rfl⟩ : syracuseStep 20143997 = 7553999) B7553999
theorem B13429331 : Blo 1961435 13429331 := bstep (se 1 (by rfl) ⟨10071998, by rfl⟩ : syracuseStep 13429331 = 20143997) B20143997
theorem B8952887 : Blo 1961435 8952887 := bstep (se 1 (by rfl) ⟨6714665, by rfl⟩ : syracuseStep 8952887 = 13429331) B13429331
theorem B23874365 : Blo 1961435 23874365 := bstep (se 3 (by rfl) ⟨4476443, by rfl⟩ : syracuseStep 23874365 = 8952887) B8952887
theorem B63664973 : Blo 1961435 63664973 := bstep (se 3 (by rfl) ⟨11937182, by rfl⟩ : syracuseStep 63664973 = 23874365) B23874365
theorem B42443315 : Blo 1961435 42443315 := bstep (se 1 (by rfl) ⟨31832486, by rfl⟩ : syracuseStep 42443315 = 63664973) B63664973
theorem B28295543 : Blo 1961435 28295543 := bstep (se 1 (by rfl) ⟨21221657, by rfl⟩ : syracuseStep 28295543 = 42443315) B42443315
theorem B18863695 : Blo 1961435 18863695 := bstep (se 1 (by rfl) ⟨14147771, by rfl⟩ : syracuseStep 18863695 = 28295543) B28295543
theorem B25151593 : Blo 1961435 25151593 := bstep (se 2 (by rfl) ⟨9431847, by rfl⟩ : syracuseStep 25151593 = 18863695) B18863695
theorem B33535457 : Blo 1961435 33535457 := bstep (se 2 (by rfl) ⟨12575796, by rfl⟩ : syracuseStep 33535457 = 25151593) B25151593
theorem B22356971 : Blo 1961435 22356971 := bstep (se 1 (by rfl) ⟨16767728, by rfl⟩ : syracuseStep 22356971 = 33535457) B33535457
theorem B14904647 : Blo 1961435 14904647 := bstep (se 1 (by rfl) ⟨11178485, by rfl⟩ : syracuseStep 14904647 = 22356971) B22356971
theorem B9936431 : Blo 1961435 9936431 := bstep (se 1 (by rfl) ⟨7452323, by rfl⟩ : syracuseStep 9936431 = 14904647) B14904647
theorem B6624287 : Blo 1961435 6624287 := bstep (se 1 (by rfl) ⟨4968215, by rfl⟩ : syracuseStep 6624287 = 9936431) B9936431
theorem B4416191 : Blo 1961435 4416191 := bstep (se 1 (by rfl) ⟨3312143, by rfl⟩ : syracuseStep 4416191 = 6624287) B6624287
theorem B2944127 : Blo 1961435 2944127 := bstep (se 1 (by rfl) ⟨2208095, by rfl⟩ : syracuseStep 2944127 = 4416191) B4416191
theorem B1962751 : Blo 1961435 1962751 := bstep (se 1 (by rfl) ⟨1472063, by rfl⟩ : syracuseStep 1962751 = 2944127) B2944127
theorem B2944133 : Blo 1961435 2944133 := bbase (se 4 (by rfl) ⟨276012, by rfl⟩ : syracuseStep 2944133 = 552025) (by norm_num)
theorem B1962755 : Blo 1961435 1962755 := bstep (se 1 (by rfl) ⟨1472066, by rfl⟩ : syracuseStep 1962755 = 2944133) B2944133
theorem B3312157 : Blo 1961435 3312157 := bbase (se 3 (by rfl) ⟨621029, by rfl⟩ : syracuseStep 3312157 = 1242059) (by norm_num)
theorem B4416209 : Blo 1961435 4416209 := bstep (se 2 (by rfl) ⟨1656078, by rfl⟩ : syracuseStep 4416209 = 3312157) B3312157
theorem B2944139 : Blo 1961435 2944139 := bstep (se 1 (by rfl) ⟨2208104, by rfl⟩ : syracuseStep 2944139 = 4416209) B4416209
theorem B1962759 : Blo 1961435 1962759 := bstep (se 1 (by rfl) ⟨1472069, by rfl⟩ : syracuseStep 1962759 = 2944139) B2944139
theorem B2208109 : Blo 1961435 2208109 := bbase (se 3 (by rfl) ⟨414020, by rfl⟩ : syracuseStep 2208109 = 828041) (by norm_num)
theorem B2944145 : Blo 1961435 2944145 := bstep (se 2 (by rfl) ⟨1104054, by rfl⟩ : syracuseStep 2944145 = 2208109) B2208109
theorem B1962763 : Blo 1961435 1962763 := bstep (se 1 (by rfl) ⟨1472072, by rfl⟩ : syracuseStep 1962763 = 2944145) B2944145
theorem B6624341 : Blo 1961435 6624341 := bbase (se 8 (by rfl) ⟨38814, by rfl⟩ : syracuseStep 6624341 = 77629) (by norm_num)
theorem B4416227 : Blo 1961435 4416227 := bstep (se 1 (by rfl) ⟨3312170, by rfl⟩ : syracuseStep 4416227 = 6624341) B6624341
theorem B2944151 : Blo 1961435 2944151 := bstep (se 1 (by rfl) ⟨2208113, by rfl⟩ : syracuseStep 2944151 = 4416227) B4416227
theorem B1962767 : Blo 1961435 1962767 := bstep (se 1 (by rfl) ⟨1472075, by rfl⟩ : syracuseStep 1962767 = 2944151) B2944151
theorem B2944157 : Blo 1961435 2944157 := bbase (se 3 (by rfl) ⟨552029, by rfl⟩ : syracuseStep 2944157 = 1104059) (by norm_num)
theorem B1962771 : Blo 1961435 1962771 := bstep (se 1 (by rfl) ⟨1472078, by rfl⟩ : syracuseStep 1962771 = 2944157) B2944157
theorem B4416245 : Blo 1961435 4416245 := bbase (se 5 (by rfl) ⟨207011, by rfl⟩ : syracuseStep 4416245 = 414023) (by norm_num)
theorem B2944163 : Blo 1961435 2944163 := bstep (se 1 (by rfl) ⟨2208122, by rfl⟩ : syracuseStep 2944163 = 4416245) B4416245
theorem B1962775 : Blo 1961435 1962775 := bstep (se 1 (by rfl) ⟨1472081, by rfl⟩ : syracuseStep 1962775 = 2944163) B2944163
theorem B25151957 : Blo 1961435 25151957 := bbase (se 7 (by rfl) ⟨294749, by rfl⟩ : syracuseStep 25151957 = 589499) (by norm_num)
theorem B16767971 : Blo 1961435 16767971 := bstep (se 1 (by rfl) ⟨12575978, by rfl⟩ : syracuseStep 16767971 = 25151957) B25151957
theorem B11178647 : Blo 1961435 11178647 := bstep (se 1 (by rfl) ⟨8383985, by rfl⟩ : syracuseStep 11178647 = 16767971) B16767971
theorem B7452431 : Blo 1961435 7452431 := bstep (se 1 (by rfl) ⟨5589323, by rfl⟩ : syracuseStep 7452431 = 11178647) B11178647
theorem B4968287 : Blo 1961435 4968287 := bstep (se 1 (by rfl) ⟨3726215, by rfl⟩ : syracuseStep 4968287 = 7452431) B7452431
theorem B3312191 : Blo 1961435 3312191 := bstep (se 1 (by rfl) ⟨2484143, by rfl⟩ : syracuseStep 3312191 = 4968287) B4968287
theorem B2208127 : Blo 1961435 2208127 := bstep (se 1 (by rfl) ⟨1656095, by rfl⟩ : syracuseStep 2208127 = 3312191) B3312191
theorem B2944169 : Blo 1961435 2944169 := bstep (se 2 (by rfl) ⟨1104063, by rfl⟩ : syracuseStep 2944169 = 2208127) B2208127
theorem B1962779 : Blo 1961435 1962779 := bstep (se 1 (by rfl) ⟨1472084, by rfl⟩ : syracuseStep 1962779 = 2944169) B2944169
theorem B2358001 : Blo 1961435 2358001 := bbase (se 2 (by rfl) ⟨884250, by rfl⟩ : syracuseStep 2358001 = 1768501) (by norm_num)
theorem B3144001 : Blo 1961435 3144001 := bstep (se 2 (by rfl) ⟨1179000, by rfl⟩ : syracuseStep 3144001 = 2358001) B2358001
theorem B4192001 : Blo 1961435 4192001 := bstep (se 2 (by rfl) ⟨1572000, by rfl⟩ : syracuseStep 4192001 = 3144001) B3144001
theorem B2794667 : Blo 1961435 2794667 := bstep (se 1 (by rfl) ⟨2096000, by rfl⟩ : syracuseStep 2794667 = 4192001) B4192001
theorem B7452445 : Blo 1961435 7452445 := bstep (se 3 (by rfl) ⟨1397333, by rfl⟩ : syracuseStep 7452445 = 2794667) B2794667
theorem B9936593 : Blo 1961435 9936593 := bstep (se 2 (by rfl) ⟨3726222, by rfl⟩ : syracuseStep 9936593 = 7452445) B7452445
theorem B6624395 : Blo 1961435 6624395 := bstep (se 1 (by rfl) ⟨4968296, by rfl⟩ : syracuseStep 6624395 = 9936593) B9936593
theorem B4416263 : Blo 1961435 4416263 := bstep (se 1 (by rfl) ⟨3312197, by rfl⟩ : syracuseStep 4416263 = 6624395) B6624395
theorem B2944175 : Blo 1961435 2944175 := bstep (se 1 (by rfl) ⟨2208131, by rfl⟩ : syracuseStep 2944175 = 4416263) B4416263
theorem B1962783 : Blo 1961435 1962783 := bstep (se 1 (by rfl) ⟨1472087, by rfl⟩ : syracuseStep 1962783 = 2944175) B2944175
theorem B2944181 : Blo 1961435 2944181 := bbase (se 5 (by rfl) ⟨138008, by rfl⟩ : syracuseStep 2944181 = 276017) (by norm_num)
theorem B1962787 : Blo 1961435 1962787 := bstep (se 1 (by rfl) ⟨1472090, by rfl⟩ : syracuseStep 1962787 = 2944181) B2944181
theorem B4968317 : Blo 1961435 4968317 := bbase (se 3 (by rfl) ⟨931559, by rfl⟩ : syracuseStep 4968317 = 1863119) (by norm_num)
theorem B3312211 : Blo 1961435 3312211 := bstep (se 1 (by rfl) ⟨2484158, by rfl⟩ : syracuseStep 3312211 = 4968317) B4968317
theorem B4416281 : Blo 1961435 4416281 := bstep (se 2 (by rfl) ⟨1656105, by rfl⟩ : syracuseStep 4416281 = 3312211) B3312211
theorem B2944187 : Blo 1961435 2944187 := bstep (se 1 (by rfl) ⟨2208140, by rfl⟩ : syracuseStep 2944187 = 4416281) B4416281
theorem B1962791 : Blo 1961435 1962791 := bstep (se 1 (by rfl) ⟨1472093, by rfl⟩ : syracuseStep 1962791 = 2944187) B2944187
theorem B2208145 : Blo 1961435 2208145 := bbase (se 2 (by rfl) ⟨828054, by rfl⟩ : syracuseStep 2208145 = 1656109) (by norm_num)
theorem B2944193 : Blo 1961435 2944193 := bstep (se 2 (by rfl) ⟨1104072, by rfl⟩ : syracuseStep 2944193 = 2208145) B2208145
theorem B1962795 : Blo 1961435 1962795 := bstep (se 1 (by rfl) ⟨1472096, by rfl⟩ : syracuseStep 1962795 = 2944193) B2944193
theorem B3726253 : Blo 1961435 3726253 := bbase (se 3 (by rfl) ⟨698672, by rfl⟩ : syracuseStep 3726253 = 1397345) (by norm_num)
theorem B4968337 : Blo 1961435 4968337 := bstep (se 2 (by rfl) ⟨1863126, by rfl⟩ : syracuseStep 4968337 = 3726253) B3726253
theorem B6624449 : Blo 1961435 6624449 := bstep (se 2 (by rfl) ⟨2484168, by rfl⟩ : syracuseStep 6624449 = 4968337) B4968337
theorem B4416299 : Blo 1961435 4416299 := bstep (se 1 (by rfl) ⟨3312224, by rfl⟩ : syracuseStep 4416299 = 6624449) B6624449
theorem B2944199 : Blo 1961435 2944199 := bstep (se 1 (by rfl) ⟨2208149, by rfl⟩ : syracuseStep 2944199 = 4416299) B4416299
theorem B1962799 : Blo 1961435 1962799 := bstep (se 1 (by rfl) ⟨1472099, by rfl⟩ : syracuseStep 1962799 = 2944199) B2944199
theorem B2944205 : Blo 1961435 2944205 := bbase (se 3 (by rfl) ⟨552038, by rfl⟩ : syracuseStep 2944205 = 1104077) (by norm_num)
theorem B1962803 : Blo 1961435 1962803 := bstep (se 1 (by rfl) ⟨1472102, by rfl⟩ : syracuseStep 1962803 = 2944205) B2944205
theorem B4416317 : Blo 1961435 4416317 := bbase (se 3 (by rfl) ⟨828059, by rfl⟩ : syracuseStep 4416317 = 1656119) (by norm_num)
theorem B2944211 : Blo 1961435 2944211 := bstep (se 1 (by rfl) ⟨2208158, by rfl⟩ : syracuseStep 2944211 = 4416317) B4416317
theorem B1962807 : Blo 1961435 1962807 := bstep (se 1 (by rfl) ⟨1472105, by rfl⟩ : syracuseStep 1962807 = 2944211) B2944211
theorem B3312245 : Blo 1961435 3312245 := bbase (se 5 (by rfl) ⟨155261, by rfl⟩ : syracuseStep 3312245 = 310523) (by norm_num)
theorem B2208163 : Blo 1961435 2208163 := bstep (se 1 (by rfl) ⟨1656122, by rfl⟩ : syracuseStep 2208163 = 3312245) B3312245
theorem B2944217 : Blo 1961435 2944217 := bstep (se 2 (by rfl) ⟨1104081, by rfl⟩ : syracuseStep 2944217 = 2208163) B2208163
theorem B1962811 : Blo 1961435 1962811 := bstep (se 1 (by rfl) ⟨1472108, by rfl⟩ : syracuseStep 1962811 = 2944217) B2944217
theorem B4192069 : Blo 1961435 4192069 := bbase (se 4 (by rfl) ⟨393006, by rfl⟩ : syracuseStep 4192069 = 786013) (by norm_num)
theorem B5589425 : Blo 1961435 5589425 := bstep (se 2 (by rfl) ⟨2096034, by rfl⟩ : syracuseStep 5589425 = 4192069) B4192069
theorem B14905133 : Blo 1961435 14905133 := bstep (se 3 (by rfl) ⟨2794712, by rfl⟩ : syracuseStep 14905133 = 5589425) B5589425
theorem B9936755 : Blo 1961435 9936755 := bstep (se 1 (by rfl) ⟨7452566, by rfl⟩ : syracuseStep 9936755 = 14905133) B14905133
theorem B6624503 : Blo 1961435 6624503 := bstep (se 1 (by rfl) ⟨4968377, by rfl⟩ : syracuseStep 6624503 = 9936755) B9936755
theorem B4416335 : Blo 1961435 4416335 := bstep (se 1 (by rfl) ⟨3312251, by rfl⟩ : syracuseStep 4416335 = 6624503) B6624503
theorem B2944223 : Blo 1961435 2944223 := bstep (se 1 (by rfl) ⟨2208167, by rfl⟩ : syracuseStep 2944223 = 4416335) B4416335
theorem B1962815 : Blo 1961435 1962815 := bstep (se 1 (by rfl) ⟨1472111, by rfl⟩ : syracuseStep 1962815 = 2944223) B2944223
theorem B2944229 : Blo 1961435 2944229 := bbase (se 4 (by rfl) ⟨276021, by rfl⟩ : syracuseStep 2944229 = 552043) (by norm_num)
theorem B1962819 : Blo 1961435 1962819 := bstep (se 1 (by rfl) ⟨1472114, by rfl⟩ : syracuseStep 1962819 = 2944229) B2944229
theorem B9432197 : Blo 1961435 9432197 := bbase (se 4 (by rfl) ⟨884268, by rfl⟩ : syracuseStep 9432197 = 1768537) (by norm_num)
theorem B6288131 : Blo 1961435 6288131 := bstep (se 1 (by rfl) ⟨4716098, by rfl⟩ : syracuseStep 6288131 = 9432197) B9432197
theorem B4192087 : Blo 1961435 4192087 := bstep (se 1 (by rfl) ⟨3144065, by rfl⟩ : syracuseStep 4192087 = 6288131) B6288131
theorem B5589449 : Blo 1961435 5589449 := bstep (se 2 (by rfl) ⟨2096043, by rfl⟩ : syracuseStep 5589449 = 4192087) B4192087
theorem B3726299 : Blo 1961435 3726299 := bstep (se 1 (by rfl) ⟨2794724, by rfl⟩ : syracuseStep 3726299 = 5589449) B5589449
theorem B2484199 : Blo 1961435 2484199 := bstep (se 1 (by rfl) ⟨1863149, by rfl⟩ : syracuseStep 2484199 = 3726299) B3726299
theorem B3312265 : Blo 1961435 3312265 := bstep (se 2 (by rfl) ⟨1242099, by rfl⟩ : syracuseStep 3312265 = 2484199) B2484199
theorem B4416353 : Blo 1961435 4416353 := bstep (se 2 (by rfl) ⟨1656132, by rfl⟩ : syracuseStep 4416353 = 3312265) B3312265
theorem B2944235 : Blo 1961435 2944235 := bstep (se 1 (by rfl) ⟨2208176, by rfl⟩ : syracuseStep 2944235 = 4416353) B4416353
theorem B1962823 : Blo 1961435 1962823 := bstep (se 1 (by rfl) ⟨1472117, by rfl⟩ : syracuseStep 1962823 = 2944235) B2944235
theorem B2208181 : Blo 1961435 2208181 := bbase (se 5 (by rfl) ⟨103508, by rfl⟩ : syracuseStep 2208181 = 207017) (by norm_num)
theorem B2944241 : Blo 1961435 2944241 := bstep (se 2 (by rfl) ⟨1104090, by rfl⟩ : syracuseStep 2944241 = 2208181) B2208181
theorem B1962827 : Blo 1961435 1962827 := bstep (se 1 (by rfl) ⟨1472120, by rfl⟩ : syracuseStep 1962827 = 2944241) B2944241
theorem B2484209 : Blo 1961435 2484209 := bbase (se 2 (by rfl) ⟨931578, by rfl⟩ : syracuseStep 2484209 = 1863157) (by norm_num)
theorem B6624557 : Blo 1961435 6624557 := bstep (se 3 (by rfl) ⟨1242104, by rfl⟩ : syracuseStep 6624557 = 2484209) B2484209
theorem B4416371 : Blo 1961435 4416371 := bstep (se 1 (by rfl) ⟨3312278, by rfl⟩ : syracuseStep 4416371 = 6624557) B6624557
theorem B2944247 : Blo 1961435 2944247 := bstep (se 1 (by rfl) ⟨2208185, by rfl⟩ : syracuseStep 2944247 = 4416371) B4416371
theorem B1962831 : Blo 1961435 1962831 := bstep (se 1 (by rfl) ⟨1472123, by rfl⟩ : syracuseStep 1962831 = 2944247) B2944247
theorem B2944253 : Blo 1961435 2944253 := bbase (se 3 (by rfl) ⟨552047, by rfl⟩ : syracuseStep 2944253 = 1104095) (by norm_num)
theorem B1962835 : Blo 1961435 1962835 := bstep (se 1 (by rfl) ⟨1472126, by rfl⟩ : syracuseStep 1962835 = 2944253) B2944253
theorem B4416389 : Blo 1961435 4416389 := bbase (se 4 (by rfl) ⟨414036, by rfl⟩ : syracuseStep 4416389 = 828073) (by norm_num)
theorem B2944259 : Blo 1961435 2944259 := bstep (se 1 (by rfl) ⟨2208194, by rfl⟩ : syracuseStep 2944259 = 4416389) B4416389
theorem B1962839 : Blo 1961435 1962839 := bstep (se 1 (by rfl) ⟨1472129, by rfl⟩ : syracuseStep 1962839 = 2944259) B2944259
theorem B2096065 : Blo 1961435 2096065 := bbase (se 2 (by rfl) ⟨786024, by rfl⟩ : syracuseStep 2096065 = 1572049) (by norm_num)
theorem B2794753 : Blo 1961435 2794753 := bstep (se 2 (by rfl) ⟨1048032, by rfl⟩ : syracuseStep 2794753 = 2096065) B2096065
theorem B3726337 : Blo 1961435 3726337 := bstep (se 2 (by rfl) ⟨1397376, by rfl⟩ : syracuseStep 3726337 = 2794753) B2794753
theorem B4968449 : Blo 1961435 4968449 := bstep (se 2 (by rfl) ⟨1863168, by rfl⟩ : syracuseStep 4968449 = 3726337) B3726337
theorem B3312299 : Blo 1961435 3312299 := bstep (se 1 (by rfl) ⟨2484224, by rfl⟩ : syracuseStep 3312299 = 4968449) B4968449
theorem B2208199 : Blo 1961435 2208199 := bstep (se 1 (by rfl) ⟨1656149, by rfl⟩ : syracuseStep 2208199 = 3312299) B3312299
theorem B2944265 : Blo 1961435 2944265 := bstep (se 2 (by rfl) ⟨1104099, by rfl⟩ : syracuseStep 2944265 = 2208199) B2208199
theorem B1962843 : Blo 1961435 1962843 := bstep (se 1 (by rfl) ⟨1472132, by rfl⟩ : syracuseStep 1962843 = 2944265) B2944265
theorem B9936917 : Blo 1961435 9936917 := bbase (se 6 (by rfl) ⟨232896, by rfl⟩ : syracuseStep 9936917 = 465793) (by norm_num)
theorem B6624611 : Blo 1961435 6624611 := bstep (se 1 (by rfl) ⟨4968458, by rfl⟩ : syracuseStep 6624611 = 9936917) B9936917
theorem B4416407 : Blo 1961435 4416407 := bstep (se 1 (by rfl) ⟨3312305, by rfl⟩ : syracuseStep 4416407 = 6624611) B6624611
theorem B2944271 : Blo 1961435 2944271 := bstep (se 1 (by rfl) ⟨2208203, by rfl⟩ : syracuseStep 2944271 = 4416407) B4416407
theorem B1962847 : Blo 1961435 1962847 := bstep (se 1 (by rfl) ⟨1472135, by rfl⟩ : syracuseStep 1962847 = 2944271) B2944271
theorem B2944277 : Blo 1961435 2944277 := bbase (se 6 (by rfl) ⟨69006, by rfl⟩ : syracuseStep 2944277 = 138013) (by norm_num)
theorem B1962851 : Blo 1961435 1962851 := bstep (se 1 (by rfl) ⟨1472138, by rfl⟩ : syracuseStep 1962851 = 2944277) B2944277
theorem B4033565 : Blo 1961435 4033565 := bbase (se 3 (by rfl) ⟨756293, by rfl⟩ : syracuseStep 4033565 = 1512587) (by norm_num)
theorem B2689043 : Blo 1961435 2689043 := bstep (se 1 (by rfl) ⟨2016782, by rfl⟩ : syracuseStep 2689043 = 4033565) B4033565
theorem B7170781 : Blo 1961435 7170781 := bstep (se 3 (by rfl) ⟨1344521, by rfl⟩ : syracuseStep 7170781 = 2689043) B2689043
theorem B9561041 : Blo 1961435 9561041 := bstep (se 2 (by rfl) ⟨3585390, by rfl⟩ : syracuseStep 9561041 = 7170781) B7170781
theorem B6374027 : Blo 1961435 6374027 := bstep (se 1 (by rfl) ⟨4780520, by rfl⟩ : syracuseStep 6374027 = 9561041) B9561041
theorem B4249351 : Blo 1961435 4249351 := bstep (se 1 (by rfl) ⟨3187013, by rfl⟩ : syracuseStep 4249351 = 6374027) B6374027
theorem B5665801 : Blo 1961435 5665801 := bstep (se 2 (by rfl) ⟨2124675, by rfl⟩ : syracuseStep 5665801 = 4249351) B4249351
theorem B7554401 : Blo 1961435 7554401 := bstep (se 2 (by rfl) ⟨2832900, by rfl⟩ : syracuseStep 7554401 = 5665801) B5665801
theorem B5036267 : Blo 1961435 5036267 := bstep (se 1 (by rfl) ⟨3777200, by rfl⟩ : syracuseStep 5036267 = 7554401) B7554401
theorem B13430045 : Blo 1961435 13430045 := bstep (se 3 (by rfl) ⟨2518133, by rfl⟩ : syracuseStep 13430045 = 5036267) B5036267
theorem B8953363 : Blo 1961435 8953363 := bstep (se 1 (by rfl) ⟨6715022, by rfl⟩ : syracuseStep 8953363 = 13430045) B13430045
theorem B11937817 : Blo 1961435 11937817 := bstep (se 2 (by rfl) ⟨4476681, by rfl⟩ : syracuseStep 11937817 = 8953363) B8953363
theorem B15917089 : Blo 1961435 15917089 := bstep (se 2 (by rfl) ⟨5968908, by rfl⟩ : syracuseStep 15917089 = 11937817) B11937817
theorem B21222785 : Blo 1961435 21222785 := bstep (se 2 (by rfl) ⟨7958544, by rfl⟩ : syracuseStep 21222785 = 15917089) B15917089
theorem B14148523 : Blo 1961435 14148523 := bstep (se 1 (by rfl) ⟨10611392, by rfl⟩ : syracuseStep 14148523 = 21222785) B21222785
theorem B18864697 : Blo 1961435 18864697 := bstep (se 2 (by rfl) ⟨7074261, by rfl⟩ : syracuseStep 18864697 = 14148523) B14148523
theorem B25152929 : Blo 1961435 25152929 := bstep (se 2 (by rfl) ⟨9432348, by rfl⟩ : syracuseStep 25152929 = 18864697) B18864697
theorem B16768619 : Blo 1961435 16768619 := bstep (se 1 (by rfl) ⟨12576464, by rfl⟩ : syracuseStep 16768619 = 25152929) B25152929
theorem B11179079 : Blo 1961435 11179079 := bstep (se 1 (by rfl) ⟨8384309, by rfl⟩ : syracuseStep 11179079 = 16768619) B16768619
theorem B7452719 : Blo 1961435 7452719 := bstep (se 1 (by rfl) ⟨5589539, by rfl⟩ : syracuseStep 7452719 = 11179079) B11179079
theorem B4968479 : Blo 1961435 4968479 := bstep (se 1 (by rfl) ⟨3726359, by rfl⟩ : syracuseStep 4968479 = 7452719) B7452719
theorem B3312319 : Blo 1961435 3312319 := bstep (se 1 (by rfl) ⟨2484239, by rfl⟩ : syracuseStep 3312319 = 4968479) B4968479
theorem B4416425 : Blo 1961435 4416425 := bstep (se 2 (by rfl) ⟨1656159, by rfl⟩ : syracuseStep 4416425 = 3312319) B3312319
theorem B2944283 : Blo 1961435 2944283 := bstep (se 1 (by rfl) ⟨2208212, by rfl⟩ : syracuseStep 2944283 = 4416425) B4416425
theorem B1962855 : Blo 1961435 1962855 := bstep (se 1 (by rfl) ⟨1472141, by rfl⟩ : syracuseStep 1962855 = 2944283) B2944283
theorem B2208217 : Blo 1961435 2208217 := bbase (se 2 (by rfl) ⟨828081, by rfl⟩ : syracuseStep 2208217 = 1656163) (by norm_num)
theorem B2944289 : Blo 1961435 2944289 := bstep (se 2 (by rfl) ⟨1104108, by rfl⟩ : syracuseStep 2944289 = 2208217) B2208217
theorem B1962859 : Blo 1961435 1962859 := bstep (se 1 (by rfl) ⟨1472144, by rfl⟩ : syracuseStep 1962859 = 2944289) B2944289
theorem B2794781 : Blo 1961435 2794781 := bbase (se 3 (by rfl) ⟨524021, by rfl⟩ : syracuseStep 2794781 = 1048043) (by norm_num)
theorem B7452749 : Blo 1961435 7452749 := bstep (se 3 (by rfl) ⟨1397390, by rfl⟩ : syracuseStep 7452749 = 2794781) B2794781
theorem B4968499 : Blo 1961435 4968499 := bstep (se 1 (by rfl) ⟨3726374, by rfl⟩ : syracuseStep 4968499 = 7452749) B7452749
theorem B6624665 : Blo 1961435 6624665 := bstep (se 2 (by rfl) ⟨2484249, by rfl⟩ : syracuseStep 6624665 = 4968499) B4968499
theorem B4416443 : Blo 1961435 4416443 := bstep (se 1 (by rfl) ⟨3312332, by rfl⟩ : syracuseStep 4416443 = 6624665) B6624665
theorem B2944295 : Blo 1961435 2944295 := bstep (se 1 (by rfl) ⟨2208221, by rfl⟩ : syracuseStep 2944295 = 4416443) B4416443
theorem B1962863 : Blo 1961435 1962863 := bstep (se 1 (by rfl) ⟨1472147, by rfl⟩ : syracuseStep 1962863 = 2944295) B2944295
theorem B2944301 : Blo 1961435 2944301 := bbase (se 3 (by rfl) ⟨552056, by rfl⟩ : syracuseStep 2944301 = 1104113) (by norm_num)
theorem B1962867 : Blo 1961435 1962867 := bstep (se 1 (by rfl) ⟨1472150, by rfl⟩ : syracuseStep 1962867 = 2944301) B2944301
theorem B4416461 : Blo 1961435 4416461 := bbase (se 3 (by rfl) ⟨828086, by rfl⟩ : syracuseStep 4416461 = 1656173) (by norm_num)
theorem B2944307 : Blo 1961435 2944307 := bstep (se 1 (by rfl) ⟨2208230, by rfl⟩ : syracuseStep 2944307 = 4416461) B4416461
theorem B1962871 : Blo 1961435 1962871 := bstep (se 1 (by rfl) ⟨1472153, by rfl⟩ : syracuseStep 1962871 = 2944307) B2944307
theorem B2484265 : Blo 1961435 2484265 := bbase (se 2 (by rfl) ⟨931599, by rfl⟩ : syracuseStep 2484265 = 1863199) (by norm_num)
theorem B3312353 : Blo 1961435 3312353 := bstep (se 2 (by rfl) ⟨1242132, by rfl⟩ : syracuseStep 3312353 = 2484265) B2484265
theorem B2208235 : Blo 1961435 2208235 := bstep (se 1 (by rfl) ⟨1656176, by rfl⟩ : syracuseStep 2208235 = 3312353) B3312353
theorem B2944313 : Blo 1961435 2944313 := bstep (se 2 (by rfl) ⟨1104117, by rfl⟩ : syracuseStep 2944313 = 2208235) B2208235
theorem B1962875 : Blo 1961435 1962875 := bstep (se 1 (by rfl) ⟨1472156, by rfl⟩ : syracuseStep 1962875 = 2944313) B2944313
theorem B5968981 : Blo 1961435 5968981 := bbase (se 8 (by rfl) ⟨34974, by rfl⟩ : syracuseStep 5968981 = 69949) (by norm_num)
theorem B31834565 : Blo 1961435 31834565 := bstep (se 4 (by rfl) ⟨2984490, by rfl⟩ : syracuseStep 31834565 = 5968981) B5968981
theorem B21223043 : Blo 1961435 21223043 := bstep (se 1 (by rfl) ⟨15917282, by rfl⟩ : syracuseStep 21223043 = 31834565) B31834565
theorem B14148695 : Blo 1961435 14148695 := bstep (se 1 (by rfl) ⟨10611521, by rfl⟩ : syracuseStep 14148695 = 21223043) B21223043
theorem B9432463 : Blo 1961435 9432463 := bstep (se 1 (by rfl) ⟨7074347, by rfl⟩ : syracuseStep 9432463 = 14148695) B14148695
theorem B12576617 : Blo 1961435 12576617 := bstep (se 2 (by rfl) ⟨4716231, by rfl⟩ : syracuseStep 12576617 = 9432463) B9432463
theorem B8384411 : Blo 1961435 8384411 := bstep (se 1 (by rfl) ⟨6288308, by rfl⟩ : syracuseStep 8384411 = 12576617) B12576617
theorem B22358429 : Blo 1961435 22358429 := bstep (se 3 (by rfl) ⟨4192205, by rfl⟩ : syracuseStep 22358429 = 8384411) B8384411
theorem B14905619 : Blo 1961435 14905619 := bstep (se 1 (by rfl) ⟨11179214, by rfl⟩ : syracuseStep 14905619 = 22358429) B22358429
theorem B9937079 : Blo 1961435 9937079 := bstep (se 1 (by rfl) ⟨7452809, by rfl⟩ : syracuseStep 9937079 = 14905619) B14905619
theorem B6624719 : Blo 1961435 6624719 := bstep (se 1 (by rfl) ⟨4968539, by rfl⟩ : syracuseStep 6624719 = 9937079) B9937079
theorem B4416479 : Blo 1961435 4416479 := bstep (se 1 (by rfl) ⟨3312359, by rfl⟩ : syracuseStep 4416479 = 6624719) B6624719
theorem B2944319 : Blo 1961435 2944319 := bstep (se 1 (by rfl) ⟨2208239, by rfl⟩ : syracuseStep 2944319 = 4416479) B4416479
theorem B1962879 : Blo 1961435 1962879 := bstep (se 1 (by rfl) ⟨1472159, by rfl⟩ : syracuseStep 1962879 = 2944319) B2944319
theorem B2944325 : Blo 1961435 2944325 := bbase (se 4 (by rfl) ⟨276030, by rfl⟩ : syracuseStep 2944325 = 552061) (by norm_num)
theorem B1962883 : Blo 1961435 1962883 := bstep (se 1 (by rfl) ⟨1472162, by rfl⟩ : syracuseStep 1962883 = 2944325) B2944325
theorem B3312373 : Blo 1961435 3312373 := bbase (se 5 (by rfl) ⟨155267, by rfl⟩ : syracuseStep 3312373 = 310535) (by norm_num)
theorem B4416497 : Blo 1961435 4416497 := bstep (se 2 (by rfl) ⟨1656186, by rfl⟩ : syracuseStep 4416497 = 3312373) B3312373
theorem B2944331 : Blo 1961435 2944331 := bstep (se 1 (by rfl) ⟨2208248, by rfl⟩ : syracuseStep 2944331 = 4416497) B4416497
theorem B1962887 : Blo 1961435 1962887 := bstep (se 1 (by rfl) ⟨1472165, by rfl⟩ : syracuseStep 1962887 = 2944331) B2944331
theorem B2208253 : Blo 1961435 2208253 := bbase (se 3 (by rfl) ⟨414047, by rfl⟩ : syracuseStep 2208253 = 828095) (by norm_num)
theorem B2944337 : Blo 1961435 2944337 := bstep (se 2 (by rfl) ⟨1104126, by rfl⟩ : syracuseStep 2944337 = 2208253) B2208253
theorem B1962891 : Blo 1961435 1962891 := bstep (se 1 (by rfl) ⟨1472168, by rfl⟩ : syracuseStep 1962891 = 2944337) B2944337
theorem B6624773 : Blo 1961435 6624773 := bbase (se 4 (by rfl) ⟨621072, by rfl⟩ : syracuseStep 6624773 = 1242145) (by norm_num)
theorem B4416515 : Blo 1961435 4416515 := bstep (se 1 (by rfl) ⟨3312386, by rfl⟩ : syracuseStep 4416515 = 6624773) B6624773
theorem B2944343 : Blo 1961435 2944343 := bstep (se 1 (by rfl) ⟨2208257, by rfl⟩ : syracuseStep 2944343 = 4416515) B4416515
theorem B1962895 : Blo 1961435 1962895 := bstep (se 1 (by rfl) ⟨1472171, by rfl⟩ : syracuseStep 1962895 = 2944343) B2944343
theorem B2944349 : Blo 1961435 2944349 := bbase (se 3 (by rfl) ⟨552065, by rfl⟩ : syracuseStep 2944349 = 1104131) (by norm_num)
theorem B1962899 : Blo 1961435 1962899 := bstep (se 1 (by rfl) ⟨1472174, by rfl⟩ : syracuseStep 1962899 = 2944349) B2944349
theorem B4416533 : Blo 1961435 4416533 := bbase (se 6 (by rfl) ⟨103512, by rfl⟩ : syracuseStep 4416533 = 207025) (by norm_num)
theorem B2944355 : Blo 1961435 2944355 := bstep (se 1 (by rfl) ⟨2208266, by rfl⟩ : syracuseStep 2944355 = 4416533) B4416533
theorem B1962903 : Blo 1961435 1962903 := bstep (se 1 (by rfl) ⟨1472177, by rfl⟩ : syracuseStep 1962903 = 2944355) B2944355
theorem B7452917 : Blo 1961435 7452917 := bbase (se 5 (by rfl) ⟨349355, by rfl⟩ : syracuseStep 7452917 = 698711) (by norm_num)
theorem B4968611 : Blo 1961435 4968611 := bstep (se 1 (by rfl) ⟨3726458, by rfl⟩ : syracuseStep 4968611 = 7452917) B7452917
theorem B3312407 : Blo 1961435 3312407 := bstep (se 1 (by rfl) ⟨2484305, by rfl⟩ : syracuseStep 3312407 = 4968611) B4968611
theorem B2208271 : Blo 1961435 2208271 := bstep (se 1 (by rfl) ⟨1656203, by rfl⟩ : syracuseStep 2208271 = 3312407) B3312407
theorem B2944361 : Blo 1961435 2944361 := bstep (se 2 (by rfl) ⟨1104135, by rfl⟩ : syracuseStep 2944361 = 2208271) B2208271
theorem B1962907 : Blo 1961435 1962907 := bstep (se 1 (by rfl) ⟨1472180, by rfl⟩ : syracuseStep 1962907 = 2944361) B2944361
theorem B2096137 : Blo 1961435 2096137 := bbase (se 2 (by rfl) ⟨786051, by rfl⟩ : syracuseStep 2096137 = 1572103) (by norm_num)
theorem B11179397 : Blo 1961435 11179397 := bstep (se 4 (by rfl) ⟨1048068, by rfl⟩ : syracuseStep 11179397 = 2096137) B2096137
theorem B7452931 : Blo 1961435 7452931 := bstep (se 1 (by rfl) ⟨5589698, by rfl⟩ : syracuseStep 7452931 = 11179397) B11179397
theorem B9937241 : Blo 1961435 9937241 := bstep (se 2 (by rfl) ⟨3726465, by rfl⟩ : syracuseStep 9937241 = 7452931) B7452931
theorem B6624827 : Blo 1961435 6624827 := bstep (se 1 (by rfl) ⟨4968620, by rfl⟩ : syracuseStep 6624827 = 9937241) B9937241
theorem B4416551 : Blo 1961435 4416551 := bstep (se 1 (by rfl) ⟨3312413, by rfl⟩ : syracuseStep 4416551 = 6624827) B6624827
theorem B2944367 : Blo 1961435 2944367 := bstep (se 1 (by rfl) ⟨2208275, by rfl⟩ : syracuseStep 2944367 = 4416551) B4416551
theorem B1962911 : Blo 1961435 1962911 := bstep (se 1 (by rfl) ⟨1472183, by rfl⟩ : syracuseStep 1962911 = 2944367) B2944367
theorem B2944373 : Blo 1961435 2944373 := bbase (se 5 (by rfl) ⟨138017, by rfl⟩ : syracuseStep 2944373 = 276035) (by norm_num)
theorem B1962915 : Blo 1961435 1962915 := bstep (se 1 (by rfl) ⟨1472186, by rfl⟩ : syracuseStep 1962915 = 2944373) B2944373
theorem B2794861 : Blo 1961435 2794861 := bbase (se 3 (by rfl) ⟨524036, by rfl⟩ : syracuseStep 2794861 = 1048073) (by norm_num)
theorem B3726481 : Blo 1961435 3726481 := bstep (se 2 (by rfl) ⟨1397430, by rfl⟩ : syracuseStep 3726481 = 2794861) B2794861
theorem B4968641 : Blo 1961435 4968641 := bstep (se 2 (by rfl) ⟨1863240, by rfl⟩ : syracuseStep 4968641 = 3726481) B3726481
theorem B3312427 : Blo 1961435 3312427 := bstep (se 1 (by rfl) ⟨2484320, by rfl⟩ : syracuseStep 3312427 = 4968641) B4968641
theorem B4416569 : Blo 1961435 4416569 := bstep (se 2 (by rfl) ⟨1656213, by rfl⟩ : syracuseStep 4416569 = 3312427) B3312427
theorem B2944379 : Blo 1961435 2944379 := bstep (se 1 (by rfl) ⟨2208284, by rfl⟩ : syracuseStep 2944379 = 4416569) B4416569
theorem B1962919 : Blo 1961435 1962919 := bstep (se 1 (by rfl) ⟨1472189, by rfl⟩ : syracuseStep 1962919 = 2944379) B2944379
theorem B2208289 : Blo 1961435 2208289 := bbase (se 2 (by rfl) ⟨828108, by rfl⟩ : syracuseStep 2208289 = 1656217) (by norm_num)
theorem B2944385 : Blo 1961435 2944385 := bstep (se 2 (by rfl) ⟨1104144, by rfl⟩ : syracuseStep 2944385 = 2208289) B2208289
theorem B1962923 : Blo 1961435 1962923 := bstep (se 1 (by rfl) ⟨1472192, by rfl⟩ : syracuseStep 1962923 = 2944385) B2944385
theorem B4968661 : Blo 1961435 4968661 := bbase (se 7 (by rfl) ⟨58226, by rfl⟩ : syracuseStep 4968661 = 116453) (by norm_num)
theorem B6624881 : Blo 1961435 6624881 := bstep (se 2 (by rfl) ⟨2484330, by rfl⟩ : syracuseStep 6624881 = 4968661) B4968661
theorem B4416587 : Blo 1961435 4416587 := bstep (se 1 (by rfl) ⟨3312440, by rfl⟩ : syracuseStep 4416587 = 6624881) B6624881
theorem B2944391 : Blo 1961435 2944391 := bstep (se 1 (by rfl) ⟨2208293, by rfl⟩ : syracuseStep 2944391 = 4416587) B4416587
theorem B1962927 : Blo 1961435 1962927 := bstep (se 1 (by rfl) ⟨1472195, by rfl⟩ : syracuseStep 1962927 = 2944391) B2944391
theorem B2944397 : Blo 1961435 2944397 := bbase (se 3 (by rfl) ⟨552074, by rfl⟩ : syracuseStep 2944397 = 1104149) (by norm_num)
theorem B1962931 : Blo 1961435 1962931 := bstep (se 1 (by rfl) ⟨1472198, by rfl⟩ : syracuseStep 1962931 = 2944397) B2944397
theorem B4416605 : Blo 1961435 4416605 := bbase (se 3 (by rfl) ⟨828113, by rfl⟩ : syracuseStep 4416605 = 1656227) (by norm_num)
theorem B2944403 : Blo 1961435 2944403 := bstep (se 1 (by rfl) ⟨2208302, by rfl⟩ : syracuseStep 2944403 = 4416605) B4416605
theorem B1962935 : Blo 1961435 1962935 := bstep (se 1 (by rfl) ⟨1472201, by rfl⟩ : syracuseStep 1962935 = 2944403) B2944403
theorem B3312461 : Blo 1961435 3312461 := bbase (se 3 (by rfl) ⟨621086, by rfl⟩ : syracuseStep 3312461 = 1242173) (by norm_num)
theorem B2208307 : Blo 1961435 2208307 := bstep (se 1 (by rfl) ⟨1656230, by rfl⟩ : syracuseStep 2208307 = 3312461) B3312461
theorem B2944409 : Blo 1961435 2944409 := bstep (se 2 (by rfl) ⟨1104153, by rfl⟩ : syracuseStep 2944409 = 2208307) B2208307
theorem B1962939 : Blo 1961435 1962939 := bstep (se 1 (by rfl) ⟨1472204, by rfl⟩ : syracuseStep 1962939 = 2944409) B2944409
theorem B5105213 : Blo 1961435 5105213 := bbase (se 3 (by rfl) ⟨957227, by rfl⟩ : syracuseStep 5105213 = 1914455) (by norm_num)
theorem B3403475 : Blo 1961435 3403475 := bstep (se 1 (by rfl) ⟨2552606, by rfl⟩ : syracuseStep 3403475 = 5105213) B5105213
theorem B2268983 : Blo 1961435 2268983 := bstep (se 1 (by rfl) ⟨1701737, by rfl⟩ : syracuseStep 2268983 = 3403475) B3403475
theorem B6050621 : Blo 1961435 6050621 := bstep (se 3 (by rfl) ⟨1134491, by rfl⟩ : syracuseStep 6050621 = 2268983) B2268983
theorem B4033747 : Blo 1961435 4033747 := bstep (se 1 (by rfl) ⟨3025310, by rfl⟩ : syracuseStep 4033747 = 6050621) B6050621
theorem B5378329 : Blo 1961435 5378329 := bstep (se 2 (by rfl) ⟨2016873, by rfl⟩ : syracuseStep 5378329 = 4033747) B4033747
theorem B7171105 : Blo 1961435 7171105 := bstep (se 2 (by rfl) ⟨2689164, by rfl⟩ : syracuseStep 7171105 = 5378329) B5378329
theorem B9561473 : Blo 1961435 9561473 := bstep (se 2 (by rfl) ⟨3585552, by rfl⟩ : syracuseStep 9561473 = 7171105) B7171105
theorem B6374315 : Blo 1961435 6374315 := bstep (se 1 (by rfl) ⟨4780736, by rfl⟩ : syracuseStep 6374315 = 9561473) B9561473
theorem B4249543 : Blo 1961435 4249543 := bstep (se 1 (by rfl) ⟨3187157, by rfl⟩ : syracuseStep 4249543 = 6374315) B6374315
theorem B5666057 : Blo 1961435 5666057 := bstep (se 2 (by rfl) ⟨2124771, by rfl⟩ : syracuseStep 5666057 = 4249543) B4249543
theorem B3777371 : Blo 1961435 3777371 := bstep (se 1 (by rfl) ⟨2833028, by rfl⟩ : syracuseStep 3777371 = 5666057) B5666057
theorem B2518247 : Blo 1961435 2518247 := bstep (se 1 (by rfl) ⟨1888685, by rfl⟩ : syracuseStep 2518247 = 3777371) B3777371
theorem B6715325 : Blo 1961435 6715325 := bstep (se 3 (by rfl) ⟨1259123, by rfl⟩ : syracuseStep 6715325 = 2518247) B2518247
theorem B4476883 : Blo 1961435 4476883 := bstep (se 1 (by rfl) ⟨3357662, by rfl⟩ : syracuseStep 4476883 = 6715325) B6715325
theorem B5969177 : Blo 1961435 5969177 := bstep (se 2 (by rfl) ⟨2238441, by rfl⟩ : syracuseStep 5969177 = 4476883) B4476883
theorem B3979451 : Blo 1961435 3979451 := bstep (se 1 (by rfl) ⟨2984588, by rfl⟩ : syracuseStep 3979451 = 5969177) B5969177
theorem B2652967 : Blo 1961435 2652967 := bstep (se 1 (by rfl) ⟨1989725, by rfl⟩ : syracuseStep 2652967 = 3979451) B3979451
theorem B3537289 : Blo 1961435 3537289 := bstep (se 2 (by rfl) ⟨1326483, by rfl⟩ : syracuseStep 3537289 = 2652967) B2652967
theorem B18865541 : Blo 1961435 18865541 := bstep (se 4 (by rfl) ⟨1768644, by rfl⟩ : syracuseStep 18865541 = 3537289) B3537289
theorem B12577027 : Blo 1961435 12577027 := bstep (se 1 (by rfl) ⟨9432770, by rfl⟩ : syracuseStep 12577027 = 18865541) B18865541
theorem B16769369 : Blo 1961435 16769369 := bstep (se 2 (by rfl) ⟨6288513, by rfl⟩ : syracuseStep 16769369 = 12577027) B12577027
theorem B11179579 : Blo 1961435 11179579 := bstep (se 1 (by rfl) ⟨8384684, by rfl⟩ : syracuseStep 11179579 = 16769369) B16769369
theorem B14906105 : Blo 1961435 14906105 := bstep (se 2 (by rfl) ⟨5589789, by rfl⟩ : syracuseStep 14906105 = 11179579) B11179579
theorem B9937403 : Blo 1961435 9937403 := bstep (se 1 (by rfl) ⟨7453052, by rfl⟩ : syracuseStep 9937403 = 14906105) B14906105
theorem B6624935 : Blo 1961435 6624935 := bstep (se 1 (by rfl) ⟨4968701, by rfl⟩ : syracuseStep 6624935 = 9937403) B9937403
theorem B4416623 : Blo 1961435 4416623 := bstep (se 1 (by rfl) ⟨3312467, by rfl⟩ : syracuseStep 4416623 = 6624935) B6624935
theorem B2944415 : Blo 1961435 2944415 := bstep (se 1 (by rfl) ⟨2208311, by rfl⟩ : syracuseStep 2944415 = 4416623) B4416623
theorem B1962943 : Blo 1961435 1962943 := bstep (se 1 (by rfl) ⟨1472207, by rfl⟩ : syracuseStep 1962943 = 2944415) B2944415
theorem B2944421 : Blo 1961435 2944421 := bbase (se 4 (by rfl) ⟨276039, by rfl⟩ : syracuseStep 2944421 = 552079) (by norm_num)
theorem B1962947 : Blo 1961435 1962947 := bstep (se 1 (by rfl) ⟨1472210, by rfl⟩ : syracuseStep 1962947 = 2944421) B2944421
theorem B2484361 : Blo 1961435 2484361 := bbase (se 2 (by rfl) ⟨931635, by rfl⟩ : syracuseStep 2484361 = 1863271) (by norm_num)
theorem B3312481 : Blo 1961435 3312481 := bstep (se 2 (by rfl) ⟨1242180, by rfl⟩ : syracuseStep 3312481 = 2484361) B2484361
theorem B4416641 : Blo 1961435 4416641 := bstep (se 2 (by rfl) ⟨1656240, by rfl⟩ : syracuseStep 4416641 = 3312481) B3312481
theorem B2944427 : Blo 1961435 2944427 := bstep (se 1 (by rfl) ⟨2208320, by rfl⟩ : syracuseStep 2944427 = 4416641) B4416641
theorem B1962951 : Blo 1961435 1962951 := bstep (se 1 (by rfl) ⟨1472213, by rfl⟩ : syracuseStep 1962951 = 2944427) B2944427
theorem B2208325 : Blo 1961435 2208325 := bbase (se 4 (by rfl) ⟨207030, by rfl⟩ : syracuseStep 2208325 = 414061) (by norm_num)
theorem B2944433 : Blo 1961435 2944433 := bstep (se 2 (by rfl) ⟨1104162, by rfl⟩ : syracuseStep 2944433 = 2208325) B2208325
theorem B1962955 : Blo 1961435 1962955 := bstep (se 1 (by rfl) ⟨1472216, by rfl⟩ : syracuseStep 1962955 = 2944433) B2944433
theorem B3726557 : Blo 1961435 3726557 := bbase (se 3 (by rfl) ⟨698729, by rfl⟩ : syracuseStep 3726557 = 1397459) (by norm_num)
theorem B2484371 : Blo 1961435 2484371 := bstep (se 1 (by rfl) ⟨1863278, by rfl⟩ : syracuseStep 2484371 = 3726557) B3726557
theorem B6624989 : Blo 1961435 6624989 := bstep (se 3 (by rfl) ⟨1242185, by rfl⟩ : syracuseStep 6624989 = 2484371) B2484371
theorem B4416659 : Blo 1961435 4416659 := bstep (se 1 (by rfl) ⟨3312494, by rfl⟩ : syracuseStep 4416659 = 6624989) B6624989
theorem B2944439 : Blo 1961435 2944439 := bstep (se 1 (by rfl) ⟨2208329, by rfl⟩ : syracuseStep 2944439 = 4416659) B4416659
theorem B1962959 : Blo 1961435 1962959 := bstep (se 1 (by rfl) ⟨1472219, by rfl⟩ : syracuseStep 1962959 = 2944439) B2944439
theorem B2944445 : Blo 1961435 2944445 := bbase (se 3 (by rfl) ⟨552083, by rfl⟩ : syracuseStep 2944445 = 1104167) (by norm_num)
theorem B1962963 : Blo 1961435 1962963 := bstep (se 1 (by rfl) ⟨1472222, by rfl⟩ : syracuseStep 1962963 = 2944445) B2944445
theorem B4416677 : Blo 1961435 4416677 := bbase (se 4 (by rfl) ⟨414063, by rfl⟩ : syracuseStep 4416677 = 828127) (by norm_num)
theorem B2944451 : Blo 1961435 2944451 := bstep (se 1 (by rfl) ⟨2208338, by rfl⟩ : syracuseStep 2944451 = 4416677) B4416677
theorem B1962967 : Blo 1961435 1962967 := bstep (se 1 (by rfl) ⟨1472225, by rfl⟩ : syracuseStep 1962967 = 2944451) B2944451
theorem B4968773 : Blo 1961435 4968773 := bbase (se 4 (by rfl) ⟨465822, by rfl⟩ : syracuseStep 4968773 = 931645) (by norm_num)
theorem B3312515 : Blo 1961435 3312515 := bstep (se 1 (by rfl) ⟨2484386, by rfl⟩ : syracuseStep 3312515 = 4968773) B4968773
theorem B2208343 : Blo 1961435 2208343 := bstep (se 1 (by rfl) ⟨1656257, by rfl⟩ : syracuseStep 2208343 = 3312515) B3312515
theorem B2944457 : Blo 1961435 2944457 := bstep (se 2 (by rfl) ⟨1104171, by rfl⟩ : syracuseStep 2944457 = 2208343) B2208343
theorem B1962971 : Blo 1961435 1962971 := bstep (se 1 (by rfl) ⟨1472228, by rfl⟩ : syracuseStep 1962971 = 2944457) B2944457
theorem B11938549 : Blo 1961435 11938549 := bbase (se 5 (by rfl) ⟨559619, by rfl⟩ : syracuseStep 11938549 = 1119239) (by norm_num)
theorem B15918065 : Blo 1961435 15918065 := bstep (se 2 (by rfl) ⟨5969274, by rfl⟩ : syracuseStep 15918065 = 11938549) B11938549
theorem B10612043 : Blo 1961435 10612043 := bstep (se 1 (by rfl) ⟨7959032, by rfl⟩ : syracuseStep 10612043 = 15918065) B15918065
theorem B7074695 : Blo 1961435 7074695 := bstep (se 1 (by rfl) ⟨5306021, by rfl⟩ : syracuseStep 7074695 = 10612043) B10612043
theorem B4716463 : Blo 1961435 4716463 := bstep (se 1 (by rfl) ⟨3537347, by rfl⟩ : syracuseStep 4716463 = 7074695) B7074695
theorem B6288617 : Blo 1961435 6288617 := bstep (se 2 (by rfl) ⟨2358231, by rfl⟩ : syracuseStep 6288617 = 4716463) B4716463
theorem B4192411 : Blo 1961435 4192411 := bstep (se 1 (by rfl) ⟨3144308, by rfl⟩ : syracuseStep 4192411 = 6288617) B6288617
theorem B5589881 : Blo 1961435 5589881 := bstep (se 2 (by rfl) ⟨2096205, by rfl⟩ : syracuseStep 5589881 = 4192411) B4192411
theorem B3726587 : Blo 1961435 3726587 := bstep (se 1 (by rfl) ⟨2794940, by rfl⟩ : syracuseStep 3726587 = 5589881) B5589881
theorem B9937565 : Blo 1961435 9937565 := bstep (se 3 (by rfl) ⟨1863293, by rfl⟩ : syracuseStep 9937565 = 3726587) B3726587
theorem B6625043 : Blo 1961435 6625043 := bstep (se 1 (by rfl) ⟨4968782, by rfl⟩ : syracuseStep 6625043 = 9937565) B9937565
theorem B4416695 : Blo 1961435 4416695 := bstep (se 1 (by rfl) ⟨3312521, by rfl⟩ : syracuseStep 4416695 = 6625043) B6625043
theorem B2944463 : Blo 1961435 2944463 := bstep (se 1 (by rfl) ⟨2208347, by rfl⟩ : syracuseStep 2944463 = 4416695) B4416695
theorem B1962975 : Blo 1961435 1962975 := bstep (se 1 (by rfl) ⟨1472231, by rfl⟩ : syracuseStep 1962975 = 2944463) B2944463
theorem B2944469 : Blo 1961435 2944469 := bbase (se 7 (by rfl) ⟨34505, by rfl⟩ : syracuseStep 2944469 = 69011) (by norm_num)
theorem B1962979 : Blo 1961435 1962979 := bstep (se 1 (by rfl) ⟨1472234, by rfl⟩ : syracuseStep 1962979 = 2944469) B2944469
theorem B7453205 : Blo 1961435 7453205 := bbase (se 6 (by rfl) ⟨174684, by rfl⟩ : syracuseStep 7453205 = 349369) (by norm_num)
theorem B4968803 : Blo 1961435 4968803 := bstep (se 1 (by rfl) ⟨3726602, by rfl⟩ : syracuseStep 4968803 = 7453205) B7453205
theorem B3312535 : Blo 1961435 3312535 := bstep (se 1 (by rfl) ⟨2484401, by rfl⟩ : syracuseStep 3312535 = 4968803) B4968803
theorem B4416713 : Blo 1961435 4416713 := bstep (se 2 (by rfl) ⟨1656267, by rfl⟩ : syracuseStep 4416713 = 3312535) B3312535
theorem B2944475 : Blo 1961435 2944475 := bstep (se 1 (by rfl) ⟨2208356, by rfl⟩ : syracuseStep 2944475 = 4416713) B4416713
theorem B1962983 : Blo 1961435 1962983 := bstep (se 1 (by rfl) ⟨1472237, by rfl⟩ : syracuseStep 1962983 = 2944475) B2944475
theorem B2208361 : Blo 1961435 2208361 := bbase (se 2 (by rfl) ⟨828135, by rfl⟩ : syracuseStep 2208361 = 1656271) (by norm_num)
theorem B2944481 : Blo 1961435 2944481 := bstep (se 2 (by rfl) ⟨1104180, by rfl⟩ : syracuseStep 2944481 = 2208361) B2208361
theorem B1962987 : Blo 1961435 1962987 := bstep (se 1 (by rfl) ⟨1472240, by rfl⟩ : syracuseStep 1962987 = 2944481) B2944481
theorem B4192445 : Blo 1961435 4192445 := bbase (se 3 (by rfl) ⟨786083, by rfl⟩ : syracuseStep 4192445 = 1572167) (by norm_num)
theorem B11179853 : Blo 1961435 11179853 := bstep (se 3 (by rfl) ⟨2096222, by rfl⟩ : syracuseStep 11179853 = 4192445) B4192445
theorem B7453235 : Blo 1961435 7453235 := bstep (se 1 (by rfl) ⟨5589926, by rfl⟩ : syracuseStep 7453235 = 11179853) B11179853
theorem B4968823 : Blo 1961435 4968823 := bstep (se 1 (by rfl) ⟨3726617, by rfl⟩ : syracuseStep 4968823 = 7453235) B7453235
theorem B6625097 : Blo 1961435 6625097 := bstep (se 2 (by rfl) ⟨2484411, by rfl⟩ : syracuseStep 6625097 = 4968823) B4968823
theorem B4416731 : Blo 1961435 4416731 := bstep (se 1 (by rfl) ⟨3312548, by rfl⟩ : syracuseStep 4416731 = 6625097) B6625097
theorem B2944487 : Blo 1961435 2944487 := bstep (se 1 (by rfl) ⟨2208365, by rfl⟩ : syracuseStep 2944487 = 4416731) B4416731
theorem B1962991 : Blo 1961435 1962991 := bstep (se 1 (by rfl) ⟨1472243, by rfl⟩ : syracuseStep 1962991 = 2944487) B2944487
theorem B2944493 : Blo 1961435 2944493 := bbase (se 3 (by rfl) ⟨552092, by rfl⟩ : syracuseStep 2944493 = 1104185) (by norm_num)
theorem B1962995 : Blo 1961435 1962995 := bstep (se 1 (by rfl) ⟨1472246, by rfl⟩ : syracuseStep 1962995 = 2944493) B2944493
theorem B4416749 : Blo 1961435 4416749 := bbase (se 3 (by rfl) ⟨828140, by rfl⟩ : syracuseStep 4416749 = 1656281) (by norm_num)
theorem B2944499 : Blo 1961435 2944499 := bstep (se 1 (by rfl) ⟨2208374, by rfl⟩ : syracuseStep 2944499 = 4416749) B4416749
theorem B1962999 : Blo 1961435 1962999 := bstep (se 1 (by rfl) ⟨1472249, by rfl⟩ : syracuseStep 1962999 = 2944499) B2944499
theorem B2794981 : Blo 1961435 2794981 := bbase (se 4 (by rfl) ⟨262029, by rfl⟩ : syracuseStep 2794981 = 524059) (by norm_num)
theorem B3726641 : Blo 1961435 3726641 := bstep (se 2 (by rfl) ⟨1397490, by rfl⟩ : syracuseStep 3726641 = 2794981) B2794981
theorem B2484427 : Blo 1961435 2484427 := bstep (se 1 (by rfl) ⟨1863320, by rfl⟩ : syracuseStep 2484427 = 3726641) B3726641
theorem B3312569 : Blo 1961435 3312569 := bstep (se 2 (by rfl) ⟨1242213, by rfl⟩ : syracuseStep 3312569 = 2484427) B2484427
theorem B2208379 : Blo 1961435 2208379 := bstep (se 1 (by rfl) ⟨1656284, by rfl⟩ : syracuseStep 2208379 = 3312569) B3312569
theorem B2944505 : Blo 1961435 2944505 := bstep (se 2 (by rfl) ⟨1104189, by rfl⟩ : syracuseStep 2944505 = 2208379) B2208379
theorem B1963003 : Blo 1961435 1963003 := bstep (se 1 (by rfl) ⟨1472252, by rfl⟩ : syracuseStep 1963003 = 2944505) B2944505
theorem B7269173 : Blo 1961435 7269173 := bbase (se 5 (by rfl) ⟨340742, by rfl⟩ : syracuseStep 7269173 = 681485) (by norm_num)
theorem B77537845 : Blo 1961435 77537845 := bstep (se 5 (by rfl) ⟨3634586, by rfl⟩ : syracuseStep 77537845 = 7269173) B7269173
theorem B103383793 : Blo 1961435 103383793 := bstep (se 2 (by rfl) ⟨38768922, by rfl⟩ : syracuseStep 103383793 = 77537845) B77537845
theorem B551380229 : Blo 1961435 551380229 := bstep (se 4 (by rfl) ⟨51691896, by rfl⟩ : syracuseStep 551380229 = 103383793) B103383793
theorem B367586819 : Blo 1961435 367586819 := bstep (se 1 (by rfl) ⟨275690114, by rfl⟩ : syracuseStep 367586819 = 551380229) B551380229
theorem B245057879 : Blo 1961435 245057879 := bstep (se 1 (by rfl) ⟨183793409, by rfl⟩ : syracuseStep 245057879 = 367586819) B367586819
theorem B163371919 : Blo 1961435 163371919 := bstep (se 1 (by rfl) ⟨122528939, by rfl⟩ : syracuseStep 163371919 = 245057879) B245057879
theorem B217829225 : Blo 1961435 217829225 := bstep (se 2 (by rfl) ⟨81685959, by rfl⟩ : syracuseStep 217829225 = 163371919) B163371919
theorem B145219483 : Blo 1961435 145219483 := bstep (se 1 (by rfl) ⟨108914612, by rfl⟩ : syracuseStep 145219483 = 217829225) B217829225
theorem B193625977 : Blo 1961435 193625977 := bstep (se 2 (by rfl) ⟨72609741, by rfl⟩ : syracuseStep 193625977 = 145219483) B145219483
theorem B258167969 : Blo 1961435 258167969 := bstep (se 2 (by rfl) ⟨96812988, by rfl⟩ : syracuseStep 258167969 = 193625977) B193625977
theorem B172111979 : Blo 1961435 172111979 := bstep (se 1 (by rfl) ⟨129083984, by rfl⟩ : syracuseStep 172111979 = 258167969) B258167969
theorem B458965277 : Blo 1961435 458965277 := bstep (se 3 (by rfl) ⟨86055989, by rfl⟩ : syracuseStep 458965277 = 172111979) B172111979
theorem B305976851 : Blo 1961435 305976851 := bstep (se 1 (by rfl) ⟨229482638, by rfl⟩ : syracuseStep 305976851 = 458965277) B458965277
theorem B203984567 : Blo 1961435 203984567 := bstep (se 1 (by rfl) ⟨152988425, by rfl⟩ : syracuseStep 203984567 = 305976851) B305976851
theorem B135989711 : Blo 1961435 135989711 := bstep (se 1 (by rfl) ⟨101992283, by rfl⟩ : syracuseStep 135989711 = 203984567) B203984567
theorem B90659807 : Blo 1961435 90659807 := bstep (se 1 (by rfl) ⟨67994855, by rfl⟩ : syracuseStep 90659807 = 135989711) B135989711
theorem B60439871 : Blo 1961435 60439871 := bstep (se 1 (by rfl) ⟨45329903, by rfl⟩ : syracuseStep 60439871 = 90659807) B90659807
theorem B40293247 : Blo 1961435 40293247 := bstep (se 1 (by rfl) ⟨30219935, by rfl⟩ : syracuseStep 40293247 = 60439871) B60439871
theorem B53724329 : Blo 1961435 53724329 := bstep (se 2 (by rfl) ⟨20146623, by rfl⟩ : syracuseStep 53724329 = 40293247) B40293247
theorem B35816219 : Blo 1961435 35816219 := bstep (se 1 (by rfl) ⟨26862164, by rfl⟩ : syracuseStep 35816219 = 53724329) B53724329
theorem B23877479 : Blo 1961435 23877479 := bstep (se 1 (by rfl) ⟨17908109, by rfl⟩ : syracuseStep 23877479 = 35816219) B35816219
theorem B15918319 : Blo 1961435 15918319 := bstep (se 1 (by rfl) ⟨11938739, by rfl⟩ : syracuseStep 15918319 = 23877479) B23877479
theorem B21224425 : Blo 1961435 21224425 := bstep (se 2 (by rfl) ⟨7959159, by rfl⟩ : syracuseStep 21224425 = 15918319) B15918319
theorem B28299233 : Blo 1961435 28299233 := bstep (se 2 (by rfl) ⟨10612212, by rfl⟩ : syracuseStep 28299233 = 21224425) B21224425
theorem B75464621 : Blo 1961435 75464621 := bstep (se 3 (by rfl) ⟨14149616, by rfl⟩ : syracuseStep 75464621 = 28299233) B28299233
theorem B50309747 : Blo 1961435 50309747 := bstep (se 1 (by rfl) ⟨37732310, by rfl⟩ : syracuseStep 50309747 = 75464621) B75464621
theorem B33539831 : Blo 1961435 33539831 := bstep (se 1 (by rfl) ⟨25154873, by rfl⟩ : syracuseStep 33539831 = 50309747) B50309747
theorem B22359887 : Blo 1961435 22359887 := bstep (se 1 (by rfl) ⟨16769915, by rfl⟩ : syracuseStep 22359887 = 33539831) B33539831
theorem B14906591 : Blo 1961435 14906591 := bstep (se 1 (by rfl) ⟨11179943, by rfl⟩ : syracuseStep 14906591 = 22359887) B22359887
theorem B9937727 : Blo 1961435 9937727 := bstep (se 1 (by rfl) ⟨7453295, by rfl⟩ : syracuseStep 9937727 = 14906591) B14906591
theorem B6625151 : Blo 1961435 6625151 := bstep (se 1 (by rfl) ⟨4968863, by rfl⟩ : syracuseStep 6625151 = 9937727) B9937727
theorem B4416767 : Blo 1961435 4416767 := bstep (se 1 (by rfl) ⟨3312575, by rfl⟩ : syracuseStep 4416767 = 6625151) B6625151
theorem B2944511 : Blo 1961435 2944511 := bstep (se 1 (by rfl) ⟨2208383, by rfl⟩ : syracuseStep 2944511 = 4416767) B4416767
theorem B1963007 : Blo 1961435 1963007 := bstep (se 1 (by rfl) ⟨1472255, by rfl⟩ : syracuseStep 1963007 = 2944511) B2944511
theorem B2944517 : Blo 1961435 2944517 := bbase (se 4 (by rfl) ⟨276048, by rfl⟩ : syracuseStep 2944517 = 552097) (by norm_num)
theorem B1963011 : Blo 1961435 1963011 := bstep (se 1 (by rfl) ⟨1472258, by rfl⟩ : syracuseStep 1963011 = 2944517) B2944517
theorem B3312589 : Blo 1961435 3312589 := bbase (se 3 (by rfl) ⟨621110, by rfl⟩ : syracuseStep 3312589 = 1242221) (by norm_num)
theorem B4416785 : Blo 1961435 4416785 := bstep (se 2 (by rfl) ⟨1656294, by rfl⟩ : syracuseStep 4416785 = 3312589) B3312589
theorem B2944523 : Blo 1961435 2944523 := bstep (se 1 (by rfl) ⟨2208392, by rfl⟩ : syracuseStep 2944523 = 4416785) B4416785
theorem B1963015 : Blo 1961435 1963015 := bstep (se 1 (by rfl) ⟨1472261, by rfl⟩ : syracuseStep 1963015 = 2944523) B2944523
theorem B2208397 : Blo 1961435 2208397 := bbase (se 3 (by rfl) ⟨414074, by rfl⟩ : syracuseStep 2208397 = 828149) (by norm_num)
theorem B2944529 : Blo 1961435 2944529 := bstep (se 2 (by rfl) ⟨1104198, by rfl⟩ : syracuseStep 2944529 = 2208397) B2208397
theorem B1963019 : Blo 1961435 1963019 := bstep (se 1 (by rfl) ⟨1472264, by rfl⟩ : syracuseStep 1963019 = 2944529) B2944529
theorem B6625205 : Blo 1961435 6625205 := bbase (se 5 (by rfl) ⟨310556, by rfl⟩ : syracuseStep 6625205 = 621113) (by norm_num)
theorem B4416803 : Blo 1961435 4416803 := bstep (se 1 (by rfl) ⟨3312602, by rfl⟩ : syracuseStep 4416803 = 6625205) B6625205
theorem B2944535 : Blo 1961435 2944535 := bstep (se 1 (by rfl) ⟨2208401, by rfl⟩ : syracuseStep 2944535 = 4416803) B4416803
theorem B1963023 : Blo 1961435 1963023 := bstep (se 1 (by rfl) ⟨1472267, by rfl⟩ : syracuseStep 1963023 = 2944535) B2944535
theorem B2944541 : Blo 1961435 2944541 := bbase (se 3 (by rfl) ⟨552101, by rfl⟩ : syracuseStep 2944541 = 1104203) (by norm_num)
theorem B1963027 : Blo 1961435 1963027 := bstep (se 1 (by rfl) ⟨1472270, by rfl⟩ : syracuseStep 1963027 = 2944541) B2944541
theorem B4416821 : Blo 1961435 4416821 := bbase (se 5 (by rfl) ⟨207038, by rfl⟩ : syracuseStep 4416821 = 414077) (by norm_num)
theorem B2944547 : Blo 1961435 2944547 := bstep (se 1 (by rfl) ⟨2208410, by rfl⟩ : syracuseStep 2944547 = 4416821) B4416821
theorem B1963031 : Blo 1961435 1963031 := bstep (se 1 (by rfl) ⟨1472273, by rfl⟩ : syracuseStep 1963031 = 2944547) B2944547
theorem B4249741 : Blo 1961435 4249741 := bbase (se 3 (by rfl) ⟨796826, by rfl⟩ : syracuseStep 4249741 = 1593653) (by norm_num)
theorem B5666321 : Blo 1961435 5666321 := bstep (se 2 (by rfl) ⟨2124870, by rfl⟩ : syracuseStep 5666321 = 4249741) B4249741
theorem B15110189 : Blo 1961435 15110189 := bstep (se 3 (by rfl) ⟨2833160, by rfl⟩ : syracuseStep 15110189 = 5666321) B5666321
theorem B10073459 : Blo 1961435 10073459 := bstep (se 1 (by rfl) ⟨7555094, by rfl⟩ : syracuseStep 10073459 = 15110189) B15110189
theorem B6715639 : Blo 1961435 6715639 := bstep (se 1 (by rfl) ⟨5036729, by rfl⟩ : syracuseStep 6715639 = 10073459) B10073459
theorem B35816741 : Blo 1961435 35816741 := bstep (se 4 (by rfl) ⟨3357819, by rfl⟩ : syracuseStep 35816741 = 6715639) B6715639
theorem B23877827 : Blo 1961435 23877827 := bstep (se 1 (by rfl) ⟨17908370, by rfl⟩ : syracuseStep 23877827 = 35816741) B35816741
theorem B15918551 : Blo 1961435 15918551 := bstep (se 1 (by rfl) ⟨11938913, by rfl⟩ : syracuseStep 15918551 = 23877827) B23877827
theorem B10612367 : Blo 1961435 10612367 := bstep (se 1 (by rfl) ⟨7959275, by rfl⟩ : syracuseStep 10612367 = 15918551) B15918551
theorem B7074911 : Blo 1961435 7074911 := bstep (se 1 (by rfl) ⟨5306183, by rfl⟩ : syracuseStep 7074911 = 10612367) B10612367
theorem B18866429 : Blo 1961435 18866429 := bstep (se 3 (by rfl) ⟨3537455, by rfl⟩ : syracuseStep 18866429 = 7074911) B7074911
theorem B12577619 : Blo 1961435 12577619 := bstep (se 1 (by rfl) ⟨9433214, by rfl⟩ : syracuseStep 12577619 = 18866429) B18866429
theorem B8385079 : Blo 1961435 8385079 := bstep (se 1 (by rfl) ⟨6288809, by rfl⟩ : syracuseStep 8385079 = 12577619) B12577619
theorem B11180105 : Blo 1961435 11180105 := bstep (se 2 (by rfl) ⟨4192539, by rfl⟩ : syracuseStep 11180105 = 8385079) B8385079
theorem B7453403 : Blo 1961435 7453403 := bstep (se 1 (by rfl) ⟨5590052, by rfl⟩ : syracuseStep 7453403 = 11180105) B11180105
theorem B4968935 : Blo 1961435 4968935 := bstep (se 1 (by rfl) ⟨3726701, by rfl⟩ : syracuseStep 4968935 = 7453403) B7453403
theorem B3312623 : Blo 1961435 3312623 := bstep (se 1 (by rfl) ⟨2484467, by rfl⟩ : syracuseStep 3312623 = 4968935) B4968935
theorem B2208415 : Blo 1961435 2208415 := bstep (se 1 (by rfl) ⟨1656311, by rfl⟩ : syracuseStep 2208415 = 3312623) B3312623
theorem B2944553 : Blo 1961435 2944553 := bstep (se 2 (by rfl) ⟨1104207, by rfl⟩ : syracuseStep 2944553 = 2208415) B2208415
theorem B1963035 : Blo 1961435 1963035 := bstep (se 1 (by rfl) ⟨1472276, by rfl⟩ : syracuseStep 1963035 = 2944553) B2944553
theorem B15918581 : Blo 1961435 15918581 := bbase (se 5 (by rfl) ⟨746183, by rfl⟩ : syracuseStep 15918581 = 1492367) (by norm_num)
theorem B10612387 : Blo 1961435 10612387 := bstep (se 1 (by rfl) ⟨7959290, by rfl⟩ : syracuseStep 10612387 = 15918581) B15918581
theorem B14149849 : Blo 1961435 14149849 := bstep (se 2 (by rfl) ⟨5306193, by rfl⟩ : syracuseStep 14149849 = 10612387) B10612387
theorem B18866465 : Blo 1961435 18866465 := bstep (se 2 (by rfl) ⟨7074924, by rfl⟩ : syracuseStep 18866465 = 14149849) B14149849
theorem B12577643 : Blo 1961435 12577643 := bstep (se 1 (by rfl) ⟨9433232, by rfl⟩ : syracuseStep 12577643 = 18866465) B18866465
theorem B8385095 : Blo 1961435 8385095 := bstep (se 1 (by rfl) ⟨6288821, by rfl⟩ : syracuseStep 8385095 = 12577643) B12577643
theorem B5590063 : Blo 1961435 5590063 := bstep (se 1 (by rfl) ⟨4192547, by rfl⟩ : syracuseStep 5590063 = 8385095) B8385095
theorem B7453417 : Blo 1961435 7453417 := bstep (se 2 (by rfl) ⟨2795031, by rfl⟩ : syracuseStep 7453417 = 5590063) B5590063
theorem B9937889 : Blo 1961435 9937889 := bstep (se 2 (by rfl) ⟨3726708, by rfl⟩ : syracuseStep 9937889 = 7453417) B7453417
theorem B6625259 : Blo 1961435 6625259 := bstep (se 1 (by rfl) ⟨4968944, by rfl⟩ : syracuseStep 6625259 = 9937889) B9937889
theorem B4416839 : Blo 1961435 4416839 := bstep (se 1 (by rfl) ⟨3312629, by rfl⟩ : syracuseStep 4416839 = 6625259) B6625259
theorem B2944559 : Blo 1961435 2944559 := bstep (se 1 (by rfl) ⟨2208419, by rfl⟩ : syracuseStep 2944559 = 4416839) B4416839
theorem B1963039 : Blo 1961435 1963039 := bstep (se 1 (by rfl) ⟨1472279, by rfl⟩ : syracuseStep 1963039 = 2944559) B2944559
theorem B2944565 : Blo 1961435 2944565 := bbase (se 5 (by rfl) ⟨138026, by rfl⟩ : syracuseStep 2944565 = 276053) (by norm_num)
theorem B1963043 : Blo 1961435 1963043 := bstep (se 1 (by rfl) ⟨1472282, by rfl⟩ : syracuseStep 1963043 = 2944565) B2944565
theorem B4968965 : Blo 1961435 4968965 := bbase (se 4 (by rfl) ⟨465840, by rfl⟩ : syracuseStep 4968965 = 931681) (by norm_num)
theorem B3312643 : Blo 1961435 3312643 := bstep (se 1 (by rfl) ⟨2484482, by rfl⟩ : syracuseStep 3312643 = 4968965) B4968965
theorem B4416857 : Blo 1961435 4416857 := bstep (se 2 (by rfl) ⟨1656321, by rfl⟩ : syracuseStep 4416857 = 3312643) B3312643
theorem B2944571 : Blo 1961435 2944571 := bstep (se 1 (by rfl) ⟨2208428, by rfl⟩ : syracuseStep 2944571 = 4416857) B4416857
theorem B1963047 : Blo 1961435 1963047 := bstep (se 1 (by rfl) ⟨1472285, by rfl⟩ : syracuseStep 1963047 = 2944571) B2944571
theorem B2208433 : Blo 1961435 2208433 := bbase (se 2 (by rfl) ⟨828162, by rfl⟩ : syracuseStep 2208433 = 1656325) (by norm_num)
theorem B2944577 : Blo 1961435 2944577 := bstep (se 2 (by rfl) ⟨1104216, by rfl⟩ : syracuseStep 2944577 = 2208433) B2208433
theorem B1963051 : Blo 1961435 1963051 := bstep (se 1 (by rfl) ⟨1472288, by rfl⟩ : syracuseStep 1963051 = 2944577) B2944577
theorem B3144437 : Blo 1961435 3144437 := bbase (se 5 (by rfl) ⟨147395, by rfl⟩ : syracuseStep 3144437 = 294791) (by norm_num)
theorem B2096291 : Blo 1961435 2096291 := bstep (se 1 (by rfl) ⟨1572218, by rfl⟩ : syracuseStep 2096291 = 3144437) B3144437
theorem B5590109 : Blo 1961435 5590109 := bstep (se 3 (by rfl) ⟨1048145, by rfl⟩ : syracuseStep 5590109 = 2096291) B2096291
theorem B3726739 : Blo 1961435 3726739 := bstep (se 1 (by rfl) ⟨2795054, by rfl⟩ : syracuseStep 3726739 = 5590109) B5590109
theorem B4968985 : Blo 1961435 4968985 := bstep (se 2 (by rfl) ⟨1863369, by rfl⟩ : syracuseStep 4968985 = 3726739) B3726739
theorem B6625313 : Blo 1961435 6625313 := bstep (se 2 (by rfl) ⟨2484492, by rfl⟩ : syracuseStep 6625313 = 4968985) B4968985
theorem B4416875 : Blo 1961435 4416875 := bstep (se 1 (by rfl) ⟨3312656, by rfl⟩ : syracuseStep 4416875 = 6625313) B6625313
theorem B2944583 : Blo 1961435 2944583 := bstep (se 1 (by rfl) ⟨2208437, by rfl⟩ : syracuseStep 2944583 = 4416875) B4416875
theorem B1963055 : Blo 1961435 1963055 := bstep (se 1 (by rfl) ⟨1472291, by rfl⟩ : syracuseStep 1963055 = 2944583) B2944583
theorem B2944589 : Blo 1961435 2944589 := bbase (se 3 (by rfl) ⟨552110, by rfl⟩ : syracuseStep 2944589 = 1104221) (by norm_num)
theorem B1963059 : Blo 1961435 1963059 := bstep (se 1 (by rfl) ⟨1472294, by rfl⟩ : syracuseStep 1963059 = 2944589) B2944589
theorem B4416893 : Blo 1961435 4416893 := bbase (se 3 (by rfl) ⟨828167, by rfl⟩ : syracuseStep 4416893 = 1656335) (by norm_num)
theorem B2944595 : Blo 1961435 2944595 := bstep (se 1 (by rfl) ⟨2208446, by rfl⟩ : syracuseStep 2944595 = 4416893) B4416893
theorem B1963063 : Blo 1961435 1963063 := bstep (se 1 (by rfl) ⟨1472297, by rfl⟩ : syracuseStep 1963063 = 2944595) B2944595
theorem B3312677 : Blo 1961435 3312677 := bbase (se 4 (by rfl) ⟨310563, by rfl⟩ : syracuseStep 3312677 = 621127) (by norm_num)
theorem B2208451 : Blo 1961435 2208451 := bstep (se 1 (by rfl) ⟨1656338, by rfl⟩ : syracuseStep 2208451 = 3312677) B3312677
theorem B2944601 : Blo 1961435 2944601 := bstep (se 2 (by rfl) ⟨1104225, by rfl⟩ : syracuseStep 2944601 = 2208451) B2208451
theorem B1963067 : Blo 1961435 1963067 := bstep (se 1 (by rfl) ⟨1472300, by rfl⟩ : syracuseStep 1963067 = 2944601) B2944601
theorem B2795077 : Blo 1961435 2795077 := bbase (se 4 (by rfl) ⟨262038, by rfl⟩ : syracuseStep 2795077 = 524077) (by norm_num)
theorem B14907077 : Blo 1961435 14907077 := bstep (se 4 (by rfl) ⟨1397538, by rfl⟩ : syracuseStep 14907077 = 2795077) B2795077
theorem B9938051 : Blo 1961435 9938051 := bstep (se 1 (by rfl) ⟨7453538, by rfl⟩ : syracuseStep 9938051 = 14907077) B14907077
theorem B6625367 : Blo 1961435 6625367 := bstep (se 1 (by rfl) ⟨4969025, by rfl⟩ : syracuseStep 6625367 = 9938051) B9938051
theorem B4416911 : Blo 1961435 4416911 := bstep (se 1 (by rfl) ⟨3312683, by rfl⟩ : syracuseStep 4416911 = 6625367) B6625367
theorem B2944607 : Blo 1961435 2944607 := bstep (se 1 (by rfl) ⟨2208455, by rfl⟩ : syracuseStep 2944607 = 4416911) B4416911
theorem B1963071 : Blo 1961435 1963071 := bstep (se 1 (by rfl) ⟨1472303, by rfl⟩ : syracuseStep 1963071 = 2944607) B2944607
theorem B2944613 : Blo 1961435 2944613 := bbase (se 4 (by rfl) ⟨276057, by rfl⟩ : syracuseStep 2944613 = 552115) (by norm_num)
theorem B1963075 : Blo 1961435 1963075 := bstep (se 1 (by rfl) ⟨1472306, by rfl⟩ : syracuseStep 1963075 = 2944613) B2944613
theorem B2096317 : Blo 1961435 2096317 := bbase (se 3 (by rfl) ⟨393059, by rfl⟩ : syracuseStep 2096317 = 786119) (by norm_num)
theorem B2795089 : Blo 1961435 2795089 := bstep (se 2 (by rfl) ⟨1048158, by rfl⟩ : syracuseStep 2795089 = 2096317) B2096317
theorem B3726785 : Blo 1961435 3726785 := bstep (se 2 (by rfl) ⟨1397544, by rfl⟩ : syracuseStep 3726785 = 2795089) B2795089
theorem B2484523 : Blo 1961435 2484523 := bstep (se 1 (by rfl) ⟨1863392, by rfl⟩ : syracuseStep 2484523 = 3726785) B3726785
theorem B3312697 : Blo 1961435 3312697 := bstep (se 2 (by rfl) ⟨1242261, by rfl⟩ : syracuseStep 3312697 = 2484523) B2484523
theorem B4416929 : Blo 1961435 4416929 := bstep (se 2 (by rfl) ⟨1656348, by rfl⟩ : syracuseStep 4416929 = 3312697) B3312697
theorem B2944619 : Blo 1961435 2944619 := bstep (se 1 (by rfl) ⟨2208464, by rfl⟩ : syracuseStep 2944619 = 4416929) B4416929
theorem B1963079 : Blo 1961435 1963079 := bstep (se 1 (by rfl) ⟨1472309, by rfl⟩ : syracuseStep 1963079 = 2944619) B2944619
theorem B2208469 : Blo 1961435 2208469 := bbase (se 7 (by rfl) ⟨25880, by rfl⟩ : syracuseStep 2208469 = 51761) (by norm_num)
theorem B2944625 : Blo 1961435 2944625 := bstep (se 2 (by rfl) ⟨1104234, by rfl⟩ : syracuseStep 2944625 = 2208469) B2208469
theorem B1963083 : Blo 1961435 1963083 := bstep (se 1 (by rfl) ⟨1472312, by rfl⟩ : syracuseStep 1963083 = 2944625) B2944625
theorem B2484533 : Blo 1961435 2484533 := bbase (se 5 (by rfl) ⟨116462, by rfl⟩ : syracuseStep 2484533 = 232925) (by norm_num)
theorem B6625421 : Blo 1961435 6625421 := bstep (se 3 (by rfl) ⟨1242266, by rfl⟩ : syracuseStep 6625421 = 2484533) B2484533
theorem B4416947 : Blo 1961435 4416947 := bstep (se 1 (by rfl) ⟨3312710, by rfl⟩ : syracuseStep 4416947 = 6625421) B6625421
theorem B2944631 : Blo 1961435 2944631 := bstep (se 1 (by rfl) ⟨2208473, by rfl⟩ : syracuseStep 2944631 = 4416947) B4416947
theorem B1963087 : Blo 1961435 1963087 := bstep (se 1 (by rfl) ⟨1472315, by rfl⟩ : syracuseStep 1963087 = 2944631) B2944631
theorem B2944637 : Blo 1961435 2944637 := bbase (se 3 (by rfl) ⟨552119, by rfl⟩ : syracuseStep 2944637 = 1104239) (by norm_num)
theorem B1963091 : Blo 1961435 1963091 := bstep (se 1 (by rfl) ⟨1472318, by rfl⟩ : syracuseStep 1963091 = 2944637) B2944637
theorem B4416965 : Blo 1961435 4416965 := bbase (se 4 (by rfl) ⟨414090, by rfl⟩ : syracuseStep 4416965 = 828181) (by norm_num)
theorem B2944643 : Blo 1961435 2944643 := bstep (se 1 (by rfl) ⟨2208482, by rfl⟩ : syracuseStep 2944643 = 4416965) B4416965
theorem B1963095 : Blo 1961435 1963095 := bstep (se 1 (by rfl) ⟨1472321, by rfl⟩ : syracuseStep 1963095 = 2944643) B2944643
theorem B5306357 : Blo 1961435 5306357 := bbase (se 5 (by rfl) ⟨248735, by rfl⟩ : syracuseStep 5306357 = 497471) (by norm_num)
theorem B14150285 : Blo 1961435 14150285 := bstep (se 3 (by rfl) ⟨2653178, by rfl⟩ : syracuseStep 14150285 = 5306357) B5306357
theorem B9433523 : Blo 1961435 9433523 := bstep (se 1 (by rfl) ⟨7075142, by rfl⟩ : syracuseStep 9433523 = 14150285) B14150285
theorem B6289015 : Blo 1961435 6289015 := bstep (se 1 (by rfl) ⟨4716761, by rfl⟩ : syracuseStep 6289015 = 9433523) B9433523
theorem B8385353 : Blo 1961435 8385353 := bstep (se 2 (by rfl) ⟨3144507, by rfl⟩ : syracuseStep 8385353 = 6289015) B6289015
theorem B5590235 : Blo 1961435 5590235 := bstep (se 1 (by rfl) ⟨4192676, by rfl⟩ : syracuseStep 5590235 = 8385353) B8385353
theorem B3726823 : Blo 1961435 3726823 := bstep (se 1 (by rfl) ⟨2795117, by rfl⟩ : syracuseStep 3726823 = 5590235) B5590235
theorem B4969097 : Blo 1961435 4969097 := bstep (se 2 (by rfl) ⟨1863411, by rfl⟩ : syracuseStep 4969097 = 3726823) B3726823
theorem B3312731 : Blo 1961435 3312731 := bstep (se 1 (by rfl) ⟨2484548, by rfl⟩ : syracuseStep 3312731 = 4969097) B4969097
theorem B2208487 : Blo 1961435 2208487 := bstep (se 1 (by rfl) ⟨1656365, by rfl⟩ : syracuseStep 2208487 = 3312731) B3312731
theorem B2944649 : Blo 1961435 2944649 := bstep (se 2 (by rfl) ⟨1104243, by rfl⟩ : syracuseStep 2944649 = 2208487) B2208487
theorem B1963099 : Blo 1961435 1963099 := bstep (se 1 (by rfl) ⟨1472324, by rfl⟩ : syracuseStep 1963099 = 2944649) B2944649
theorem B9938213 : Blo 1961435 9938213 := bbase (se 4 (by rfl) ⟨931707, by rfl⟩ : syracuseStep 9938213 = 1863415) (by norm_num)
theorem B6625475 : Blo 1961435 6625475 := bstep (se 1 (by rfl) ⟨4969106, by rfl⟩ : syracuseStep 6625475 = 9938213) B9938213
theorem B4416983 : Blo 1961435 4416983 := bstep (se 1 (by rfl) ⟨3312737, by rfl⟩ : syracuseStep 4416983 = 6625475) B6625475
theorem B2944655 : Blo 1961435 2944655 := bstep (se 1 (by rfl) ⟨2208491, by rfl⟩ : syracuseStep 2944655 = 4416983) B4416983
theorem B1963103 : Blo 1961435 1963103 := bstep (se 1 (by rfl) ⟨1472327, by rfl⟩ : syracuseStep 1963103 = 2944655) B2944655
theorem B2944661 : Blo 1961435 2944661 := bbase (se 6 (by rfl) ⟨69015, by rfl⟩ : syracuseStep 2944661 = 138031) (by norm_num)
theorem B1963107 : Blo 1961435 1963107 := bstep (se 1 (by rfl) ⟨1472330, by rfl⟩ : syracuseStep 1963107 = 2944661) B2944661
theorem B2017045 : Blo 1961435 2017045 := bbase (se 6 (by rfl) ⟨47274, by rfl⟩ : syracuseStep 2017045 = 94549) (by norm_num)
theorem B2689393 : Blo 1961435 2689393 := bstep (se 2 (by rfl) ⟨1008522, by rfl⟩ : syracuseStep 2689393 = 2017045) B2017045
theorem B57373717 : Blo 1961435 57373717 := bstep (se 6 (by rfl) ⟨1344696, by rfl⟩ : syracuseStep 57373717 = 2689393) B2689393
theorem B76498289 : Blo 1961435 76498289 := bstep (se 2 (by rfl) ⟨28686858, by rfl⟩ : syracuseStep 76498289 = 57373717) B57373717
theorem B50998859 : Blo 1961435 50998859 := bstep (se 1 (by rfl) ⟨38249144, by rfl⟩ : syracuseStep 50998859 = 76498289) B76498289
theorem B33999239 : Blo 1961435 33999239 := bstep (se 1 (by rfl) ⟨25499429, by rfl⟩ : syracuseStep 33999239 = 50998859) B50998859
theorem B22666159 : Blo 1961435 22666159 := bstep (se 1 (by rfl) ⟨16999619, by rfl⟩ : syracuseStep 22666159 = 33999239) B33999239
theorem B30221545 : Blo 1961435 30221545 := bstep (se 2 (by rfl) ⟨11333079, by rfl⟩ : syracuseStep 30221545 = 22666159) B22666159
theorem B40295393 : Blo 1961435 40295393 := bstep (se 2 (by rfl) ⟨15110772, by rfl⟩ : syracuseStep 40295393 = 30221545) B30221545
theorem B26863595 : Blo 1961435 26863595 := bstep (se 1 (by rfl) ⟨20147696, by rfl⟩ : syracuseStep 26863595 = 40295393) B40295393
theorem B17909063 : Blo 1961435 17909063 := bstep (se 1 (by rfl) ⟨13431797, by rfl⟩ : syracuseStep 17909063 = 26863595) B26863595
theorem B11939375 : Blo 1961435 11939375 := bstep (se 1 (by rfl) ⟨8954531, by rfl⟩ : syracuseStep 11939375 = 17909063) B17909063
theorem B7959583 : Blo 1961435 7959583 := bstep (se 1 (by rfl) ⟨5969687, by rfl⟩ : syracuseStep 7959583 = 11939375) B11939375
theorem B10612777 : Blo 1961435 10612777 := bstep (se 2 (by rfl) ⟨3979791, by rfl⟩ : syracuseStep 10612777 = 7959583) B7959583
theorem B14150369 : Blo 1961435 14150369 := bstep (se 2 (by rfl) ⟨5306388, by rfl⟩ : syracuseStep 14150369 = 10612777) B10612777
theorem B9433579 : Blo 1961435 9433579 := bstep (se 1 (by rfl) ⟨7075184, by rfl⟩ : syracuseStep 9433579 = 14150369) B14150369
theorem B12578105 : Blo 1961435 12578105 := bstep (se 2 (by rfl) ⟨4716789, by rfl⟩ : syracuseStep 12578105 = 9433579) B9433579
theorem B8385403 : Blo 1961435 8385403 := bstep (se 1 (by rfl) ⟨6289052, by rfl⟩ : syracuseStep 8385403 = 12578105) B12578105
theorem B11180537 : Blo 1961435 11180537 := bstep (se 2 (by rfl) ⟨4192701, by rfl⟩ : syracuseStep 11180537 = 8385403) B8385403
theorem B7453691 : Blo 1961435 7453691 := bstep (se 1 (by rfl) ⟨5590268, by rfl⟩ : syracuseStep 7453691 = 11180537) B11180537
theorem B4969127 : Blo 1961435 4969127 := bstep (se 1 (by rfl) ⟨3726845, by rfl⟩ : syracuseStep 4969127 = 7453691) B7453691
theorem B3312751 : Blo 1961435 3312751 := bstep (se 1 (by rfl) ⟨2484563, by rfl⟩ : syracuseStep 3312751 = 4969127) B4969127
theorem B4417001 : Blo 1961435 4417001 := bstep (se 2 (by rfl) ⟨1656375, by rfl⟩ : syracuseStep 4417001 = 3312751) B3312751
theorem B2944667 : Blo 1961435 2944667 := bstep (se 1 (by rfl) ⟨2208500, by rfl⟩ : syracuseStep 2944667 = 4417001) B4417001
theorem B1963111 : Blo 1961435 1963111 := bstep (se 1 (by rfl) ⟨1472333, by rfl⟩ : syracuseStep 1963111 = 2944667) B2944667
theorem B2208505 : Blo 1961435 2208505 := bbase (se 2 (by rfl) ⟨828189, by rfl⟩ : syracuseStep 2208505 = 1656379) (by norm_num)
theorem B2944673 : Blo 1961435 2944673 := bstep (se 2 (by rfl) ⟨1104252, by rfl⟩ : syracuseStep 2944673 = 2208505) B2208505
theorem B1963115 : Blo 1961435 1963115 := bstep (se 1 (by rfl) ⟨1472336, by rfl⟩ : syracuseStep 1963115 = 2944673) B2944673
theorem B4477285 : Blo 1961435 4477285 := bbase (se 4 (by rfl) ⟨419745, by rfl⟩ : syracuseStep 4477285 = 839491) (by norm_num)
theorem B5969713 : Blo 1961435 5969713 := bstep (se 2 (by rfl) ⟨2238642, by rfl⟩ : syracuseStep 5969713 = 4477285) B4477285
theorem B7959617 : Blo 1961435 7959617 := bstep (se 2 (by rfl) ⟨2984856, by rfl⟩ : syracuseStep 7959617 = 5969713) B5969713
theorem B5306411 : Blo 1961435 5306411 := bstep (se 1 (by rfl) ⟨3979808, by rfl⟩ : syracuseStep 5306411 = 7959617) B7959617
theorem B3537607 : Blo 1961435 3537607 := bstep (se 1 (by rfl) ⟨2653205, by rfl⟩ : syracuseStep 3537607 = 5306411) B5306411
theorem B4716809 : Blo 1961435 4716809 := bstep (se 2 (by rfl) ⟨1768803, by rfl⟩ : syracuseStep 4716809 = 3537607) B3537607
theorem B3144539 : Blo 1961435 3144539 := bstep (se 1 (by rfl) ⟨2358404, by rfl⟩ : syracuseStep 3144539 = 4716809) B4716809
theorem B8385437 : Blo 1961435 8385437 := bstep (se 3 (by rfl) ⟨1572269, by rfl⟩ : syracuseStep 8385437 = 3144539) B3144539
theorem B5590291 : Blo 1961435 5590291 := bstep (se 1 (by rfl) ⟨4192718, by rfl⟩ : syracuseStep 5590291 = 8385437) B8385437
theorem B7453721 : Blo 1961435 7453721 := bstep (se 2 (by rfl) ⟨2795145, by rfl⟩ : syracuseStep 7453721 = 5590291) B5590291
theorem B4969147 : Blo 1961435 4969147 := bstep (se 1 (by rfl) ⟨3726860, by rfl⟩ : syracuseStep 4969147 = 7453721) B7453721
theorem B6625529 : Blo 1961435 6625529 := bstep (se 2 (by rfl) ⟨2484573, by rfl⟩ : syracuseStep 6625529 = 4969147) B4969147
theorem B4417019 : Blo 1961435 4417019 := bstep (se 1 (by rfl) ⟨3312764, by rfl⟩ : syracuseStep 4417019 = 6625529) B6625529
theorem B2944679 : Blo 1961435 2944679 := bstep (se 1 (by rfl) ⟨2208509, by rfl⟩ : syracuseStep 2944679 = 4417019) B4417019
theorem B1963119 : Blo 1961435 1963119 := bstep (se 1 (by rfl) ⟨1472339, by rfl⟩ : syracuseStep 1963119 = 2944679) B2944679
theorem B2944685 : Blo 1961435 2944685 := bbase (se 3 (by rfl) ⟨552128, by rfl⟩ : syracuseStep 2944685 = 1104257) (by norm_num)
theorem B1963123 : Blo 1961435 1963123 := bstep (se 1 (by rfl) ⟨1472342, by rfl⟩ : syracuseStep 1963123 = 2944685) B2944685
theorem B4417037 : Blo 1961435 4417037 := bbase (se 3 (by rfl) ⟨828194, by rfl⟩ : syracuseStep 4417037 = 1656389) (by norm_num)
theorem B2944691 : Blo 1961435 2944691 := bstep (se 1 (by rfl) ⟨2208518, by rfl⟩ : syracuseStep 2944691 = 4417037) B4417037
theorem B1963127 : Blo 1961435 1963127 := bstep (se 1 (by rfl) ⟨1472345, by rfl⟩ : syracuseStep 1963127 = 2944691) B2944691
theorem B2484589 : Blo 1961435 2484589 := bbase (se 3 (by rfl) ⟨465860, by rfl⟩ : syracuseStep 2484589 = 931721) (by norm_num)
theorem B3312785 : Blo 1961435 3312785 := bstep (se 2 (by rfl) ⟨1242294, by rfl⟩ : syracuseStep 3312785 = 2484589) B2484589
theorem B2208523 : Blo 1961435 2208523 := bstep (se 1 (by rfl) ⟨1656392, by rfl⟩ : syracuseStep 2208523 = 3312785) B3312785
theorem B2944697 : Blo 1961435 2944697 := bstep (se 2 (by rfl) ⟨1104261, by rfl⟩ : syracuseStep 2944697 = 2208523) B2208523
theorem B1963131 : Blo 1961435 1963131 := bstep (se 1 (by rfl) ⟨1472348, by rfl⟩ : syracuseStep 1963131 = 2944697) B2944697
theorem B5306453 : Blo 1961435 5306453 := bbase (se 8 (by rfl) ⟨31092, by rfl⟩ : syracuseStep 5306453 = 62185) (by norm_num)
theorem B3537635 : Blo 1961435 3537635 := bstep (se 1 (by rfl) ⟨2653226, by rfl⟩ : syracuseStep 3537635 = 5306453) B5306453
theorem B9433693 : Blo 1961435 9433693 := bstep (se 3 (by rfl) ⟨1768817, by rfl⟩ : syracuseStep 9433693 = 3537635) B3537635
theorem B12578257 : Blo 1961435 12578257 := bstep (se 2 (by rfl) ⟨4716846, by rfl⟩ : syracuseStep 12578257 = 9433693) B9433693
theorem B16771009 : Blo 1961435 16771009 := bstep (se 2 (by rfl) ⟨6289128, by rfl⟩ : syracuseStep 16771009 = 12578257) B12578257
theorem B22361345 : Blo 1961435 22361345 := bstep (se 2 (by rfl) ⟨8385504, by rfl⟩ : syracuseStep 22361345 = 16771009) B16771009
theorem B14907563 : Blo 1961435 14907563 := bstep (se 1 (by rfl) ⟨11180672, by rfl⟩ : syracuseStep 14907563 = 22361345) B22361345
theorem B9938375 : Blo 1961435 9938375 := bstep (se 1 (by rfl) ⟨7453781, by rfl⟩ : syracuseStep 9938375 = 14907563) B14907563
theorem B6625583 : Blo 1961435 6625583 := bstep (se 1 (by rfl) ⟨4969187, by rfl⟩ : syracuseStep 6625583 = 9938375) B9938375
theorem B4417055 : Blo 1961435 4417055 := bstep (se 1 (by rfl) ⟨3312791, by rfl⟩ : syracuseStep 4417055 = 6625583) B6625583
theorem B2944703 : Blo 1961435 2944703 := bstep (se 1 (by rfl) ⟨2208527, by rfl⟩ : syracuseStep 2944703 = 4417055) B4417055
theorem B1963135 : Blo 1961435 1963135 := bstep (se 1 (by rfl) ⟨1472351, by rfl⟩ : syracuseStep 1963135 = 2944703) B2944703
theorem B2944709 : Blo 1961435 2944709 := bbase (se 4 (by rfl) ⟨276066, by rfl⟩ : syracuseStep 2944709 = 552133) (by norm_num)
theorem B1963139 : Blo 1961435 1963139 := bstep (se 1 (by rfl) ⟨1472354, by rfl⟩ : syracuseStep 1963139 = 2944709) B2944709
theorem B3312805 : Blo 1961435 3312805 := bbase (se 4 (by rfl) ⟨310575, by rfl⟩ : syracuseStep 3312805 = 621151) (by norm_num)
theorem B4417073 : Blo 1961435 4417073 := bstep (se 2 (by rfl) ⟨1656402, by rfl⟩ : syracuseStep 4417073 = 3312805) B3312805
theorem B2944715 : Blo 1961435 2944715 := bstep (se 1 (by rfl) ⟨2208536, by rfl⟩ : syracuseStep 2944715 = 4417073) B4417073
theorem B1963143 : Blo 1961435 1963143 := bstep (se 1 (by rfl) ⟨1472357, by rfl⟩ : syracuseStep 1963143 = 2944715) B2944715
theorem B2208541 : Blo 1961435 2208541 := bbase (se 3 (by rfl) ⟨414101, by rfl⟩ : syracuseStep 2208541 = 828203) (by norm_num)
theorem B2944721 : Blo 1961435 2944721 := bstep (se 2 (by rfl) ⟨1104270, by rfl⟩ : syracuseStep 2944721 = 2208541) B2208541
theorem B1963147 : Blo 1961435 1963147 := bstep (se 1 (by rfl) ⟨1472360, by rfl⟩ : syracuseStep 1963147 = 2944721) B2944721
theorem B6625637 : Blo 1961435 6625637 := bbase (se 4 (by rfl) ⟨621153, by rfl⟩ : syracuseStep 6625637 = 1242307) (by norm_num)
theorem B4417091 : Blo 1961435 4417091 := bstep (se 1 (by rfl) ⟨3312818, by rfl⟩ : syracuseStep 4417091 = 6625637) B6625637
theorem B2944727 : Blo 1961435 2944727 := bstep (se 1 (by rfl) ⟨2208545, by rfl⟩ : syracuseStep 2944727 = 4417091) B4417091
theorem B1963151 : Blo 1961435 1963151 := bstep (se 1 (by rfl) ⟨1472363, by rfl⟩ : syracuseStep 1963151 = 2944727) B2944727
theorem B2944733 : Blo 1961435 2944733 := bbase (se 3 (by rfl) ⟨552137, by rfl⟩ : syracuseStep 2944733 = 1104275) (by norm_num)
theorem B1963155 : Blo 1961435 1963155 := bstep (se 1 (by rfl) ⟨1472366, by rfl⟩ : syracuseStep 1963155 = 2944733) B2944733
theorem B4417109 : Blo 1961435 4417109 := bbase (se 8 (by rfl) ⟨25881, by rfl⟩ : syracuseStep 4417109 = 51763) (by norm_num)
theorem B2944739 : Blo 1961435 2944739 := bstep (se 1 (by rfl) ⟨2208554, by rfl⟩ : syracuseStep 2944739 = 4417109) B4417109
theorem B1963159 : Blo 1961435 1963159 := bstep (se 1 (by rfl) ⟨1472369, by rfl⟩ : syracuseStep 1963159 = 2944739) B2944739
theorem B4192813 : Blo 1961435 4192813 := bbase (se 3 (by rfl) ⟨786152, by rfl⟩ : syracuseStep 4192813 = 1572305) (by norm_num)
theorem B5590417 : Blo 1961435 5590417 := bstep (se 2 (by rfl) ⟨2096406, by rfl⟩ : syracuseStep 5590417 = 4192813) B4192813
theorem B7453889 : Blo 1961435 7453889 := bstep (se 2 (by rfl) ⟨2795208, by rfl⟩ : syracuseStep 7453889 = 5590417) B5590417
theorem B4969259 : Blo 1961435 4969259 := bstep (se 1 (by rfl) ⟨3726944, by rfl⟩ : syracuseStep 4969259 = 7453889) B7453889
theorem B3312839 : Blo 1961435 3312839 := bstep (se 1 (by rfl) ⟨2484629, by rfl⟩ : syracuseStep 3312839 = 4969259) B4969259
theorem B2208559 : Blo 1961435 2208559 := bstep (se 1 (by rfl) ⟨1656419, by rfl⟩ : syracuseStep 2208559 = 3312839) B3312839
theorem B2944745 : Blo 1961435 2944745 := bstep (se 2 (by rfl) ⟨1104279, by rfl⟩ : syracuseStep 2944745 = 2208559) B2208559
theorem B1963163 : Blo 1961435 1963163 := bstep (se 1 (by rfl) ⟨1472372, by rfl⟩ : syracuseStep 1963163 = 2944745) B2944745
theorem B3358045 : Blo 1961435 3358045 := bbase (se 3 (by rfl) ⟨629633, by rfl⟩ : syracuseStep 3358045 = 1259267) (by norm_num)
theorem B4477393 : Blo 1961435 4477393 := bstep (se 2 (by rfl) ⟨1679022, by rfl⟩ : syracuseStep 4477393 = 3358045) B3358045
theorem B5969857 : Blo 1961435 5969857 := bstep (se 2 (by rfl) ⟨2238696, by rfl⟩ : syracuseStep 5969857 = 4477393) B4477393
theorem B7959809 : Blo 1961435 7959809 := bstep (se 2 (by rfl) ⟨2984928, by rfl⟩ : syracuseStep 7959809 = 5969857) B5969857
theorem B21226157 : Blo 1961435 21226157 := bstep (se 3 (by rfl) ⟨3979904, by rfl⟩ : syracuseStep 21226157 = 7959809) B7959809
theorem B14150771 : Blo 1961435 14150771 := bstep (se 1 (by rfl) ⟨10613078, by rfl⟩ : syracuseStep 14150771 = 21226157) B21226157
theorem B9433847 : Blo 1961435 9433847 := bstep (se 1 (by rfl) ⟨7075385, by rfl⟩ : syracuseStep 9433847 = 14150771) B14150771
theorem B25156925 : Blo 1961435 25156925 := bstep (se 3 (by rfl) ⟨4716923, by rfl⟩ : syracuseStep 25156925 = 9433847) B9433847
theorem B16771283 : Blo 1961435 16771283 := bstep (se 1 (by rfl) ⟨12578462, by rfl⟩ : syracuseStep 16771283 = 25156925) B25156925
theorem B11180855 : Blo 1961435 11180855 := bstep (se 1 (by rfl) ⟨8385641, by rfl⟩ : syracuseStep 11180855 = 16771283) B16771283
theorem B7453903 : Blo 1961435 7453903 := bstep (se 1 (by rfl) ⟨5590427, by rfl⟩ : syracuseStep 7453903 = 11180855) B11180855
theorem B9938537 : Blo 1961435 9938537 := bstep (se 2 (by rfl) ⟨3726951, by rfl⟩ : syracuseStep 9938537 = 7453903) B7453903
theorem B6625691 : Blo 1961435 6625691 := bstep (se 1 (by rfl) ⟨4969268, by rfl⟩ : syracuseStep 6625691 = 9938537) B9938537
theorem B4417127 : Blo 1961435 4417127 := bstep (se 1 (by rfl) ⟨3312845, by rfl⟩ : syracuseStep 4417127 = 6625691) B6625691
theorem B2944751 : Blo 1961435 2944751 := bstep (se 1 (by rfl) ⟨2208563, by rfl⟩ : syracuseStep 2944751 = 4417127) B4417127
theorem B1963167 : Blo 1961435 1963167 := bstep (se 1 (by rfl) ⟨1472375, by rfl⟩ : syracuseStep 1963167 = 2944751) B2944751
theorem B2944757 : Blo 1961435 2944757 := bbase (se 5 (by rfl) ⟨138035, by rfl⟩ : syracuseStep 2944757 = 276071) (by norm_num)
theorem B1963171 : Blo 1961435 1963171 := bstep (se 1 (by rfl) ⟨1472378, by rfl⟩ : syracuseStep 1963171 = 2944757) B2944757
theorem B3144629 : Blo 1961435 3144629 := bbase (se 5 (by rfl) ⟨147404, by rfl⟩ : syracuseStep 3144629 = 294809) (by norm_num)
theorem B8385677 : Blo 1961435 8385677 := bstep (se 3 (by rfl) ⟨1572314, by rfl⟩ : syracuseStep 8385677 = 3144629) B3144629
theorem B5590451 : Blo 1961435 5590451 := bstep (se 1 (by rfl) ⟨4192838, by rfl⟩ : syracuseStep 5590451 = 8385677) B8385677
theorem B3726967 : Blo 1961435 3726967 := bstep (se 1 (by rfl) ⟨2795225, by rfl⟩ : syracuseStep 3726967 = 5590451) B5590451
theorem B4969289 : Blo 1961435 4969289 := bstep (se 2 (by rfl) ⟨1863483, by rfl⟩ : syracuseStep 4969289 = 3726967) B3726967
theorem B3312859 : Blo 1961435 3312859 := bstep (se 1 (by rfl) ⟨2484644, by rfl⟩ : syracuseStep 3312859 = 4969289) B4969289
theorem B4417145 : Blo 1961435 4417145 := bstep (se 2 (by rfl) ⟨1656429, by rfl⟩ : syracuseStep 4417145 = 3312859) B3312859
theorem B2944763 : Blo 1961435 2944763 := bstep (se 1 (by rfl) ⟨2208572, by rfl⟩ : syracuseStep 2944763 = 4417145) B4417145
theorem B1963175 : Blo 1961435 1963175 := bstep (se 1 (by rfl) ⟨1472381, by rfl⟩ : syracuseStep 1963175 = 2944763) B2944763
theorem B2208577 : Blo 1961435 2208577 := bbase (se 2 (by rfl) ⟨828216, by rfl⟩ : syracuseStep 2208577 = 1656433) (by norm_num)
theorem B2944769 : Blo 1961435 2944769 := bstep (se 2 (by rfl) ⟨1104288, by rfl⟩ : syracuseStep 2944769 = 2208577) B2208577
theorem B1963179 : Blo 1961435 1963179 := bstep (se 1 (by rfl) ⟨1472384, by rfl⟩ : syracuseStep 1963179 = 2944769) B2944769
theorem B4969309 : Blo 1961435 4969309 := bbase (se 3 (by rfl) ⟨931745, by rfl⟩ : syracuseStep 4969309 = 1863491) (by norm_num)
theorem B6625745 : Blo 1961435 6625745 := bstep (se 2 (by rfl) ⟨2484654, by rfl⟩ : syracuseStep 6625745 = 4969309) B4969309
theorem B4417163 : Blo 1961435 4417163 := bstep (se 1 (by rfl) ⟨3312872, by rfl⟩ : syracuseStep 4417163 = 6625745) B6625745
theorem B2944775 : Blo 1961435 2944775 := bstep (se 1 (by rfl) ⟨2208581, by rfl⟩ : syracuseStep 2944775 = 4417163) B4417163
theorem B1963183 : Blo 1961435 1963183 := bstep (se 1 (by rfl) ⟨1472387, by rfl⟩ : syracuseStep 1963183 = 2944775) B2944775
theorem B2944781 : Blo 1961435 2944781 := bbase (se 3 (by rfl) ⟨552146, by rfl⟩ : syracuseStep 2944781 = 1104293) (by norm_num)
theorem B1963187 : Blo 1961435 1963187 := bstep (se 1 (by rfl) ⟨1472390, by rfl⟩ : syracuseStep 1963187 = 2944781) B2944781
theorem B4417181 : Blo 1961435 4417181 := bbase (se 3 (by rfl) ⟨828221, by rfl⟩ : syracuseStep 4417181 = 1656443) (by norm_num)
theorem B2944787 : Blo 1961435 2944787 := bstep (se 1 (by rfl) ⟨2208590, by rfl⟩ : syracuseStep 2944787 = 4417181) B4417181
theorem B1963191 : Blo 1961435 1963191 := bstep (se 1 (by rfl) ⟨1472393, by rfl⟩ : syracuseStep 1963191 = 2944787) B2944787
theorem B3312893 : Blo 1961435 3312893 := bbase (se 3 (by rfl) ⟨621167, by rfl⟩ : syracuseStep 3312893 = 1242335) (by norm_num)
theorem B2208595 : Blo 1961435 2208595 := bstep (se 1 (by rfl) ⟨1656446, by rfl⟩ : syracuseStep 2208595 = 3312893) B3312893
theorem B2944793 : Blo 1961435 2944793 := bstep (se 2 (by rfl) ⟨1104297, by rfl⟩ : syracuseStep 2944793 = 2208595) B2208595
theorem B1963195 : Blo 1961435 1963195 := bstep (se 1 (by rfl) ⟨1472396, by rfl⟩ : syracuseStep 1963195 = 2944793) B2944793
theorem B7959941 : Blo 1961435 7959941 := bbase (se 4 (by rfl) ⟨746244, by rfl⟩ : syracuseStep 7959941 = 1492489) (by norm_num)
theorem B5306627 : Blo 1961435 5306627 := bstep (se 1 (by rfl) ⟨3979970, by rfl⟩ : syracuseStep 5306627 = 7959941) B7959941
theorem B3537751 : Blo 1961435 3537751 := bstep (se 1 (by rfl) ⟨2653313, by rfl⟩ : syracuseStep 3537751 = 5306627) B5306627
theorem B4717001 : Blo 1961435 4717001 := bstep (se 2 (by rfl) ⟨1768875, by rfl⟩ : syracuseStep 4717001 = 3537751) B3537751
theorem B3144667 : Blo 1961435 3144667 := bstep (se 1 (by rfl) ⟨2358500, by rfl⟩ : syracuseStep 3144667 = 4717001) B4717001
theorem B4192889 : Blo 1961435 4192889 := bstep (se 2 (by rfl) ⟨1572333, by rfl⟩ : syracuseStep 4192889 = 3144667) B3144667
theorem B11181037 : Blo 1961435 11181037 := bstep (se 3 (by rfl) ⟨2096444, by rfl⟩ : syracuseStep 11181037 = 4192889) B4192889
theorem B14908049 : Blo 1961435 14908049 := bstep (se 2 (by rfl) ⟨5590518, by rfl⟩ : syracuseStep 14908049 = 11181037) B11181037
theorem B9938699 : Blo 1961435 9938699 := bstep (se 1 (by rfl) ⟨7454024, by rfl⟩ : syracuseStep 9938699 = 14908049) B14908049
theorem B6625799 : Blo 1961435 6625799 := bstep (se 1 (by rfl) ⟨4969349, by rfl⟩ : syracuseStep 6625799 = 9938699) B9938699
theorem B4417199 : Blo 1961435 4417199 := bstep (se 1 (by rfl) ⟨3312899, by rfl⟩ : syracuseStep 4417199 = 6625799) B6625799
theorem B2944799 : Blo 1961435 2944799 := bstep (se 1 (by rfl) ⟨2208599, by rfl⟩ : syracuseStep 2944799 = 4417199) B4417199
theorem B1963199 : Blo 1961435 1963199 := bstep (se 1 (by rfl) ⟨1472399, by rfl⟩ : syracuseStep 1963199 = 2944799) B2944799
theorem B2944805 : Blo 1961435 2944805 := bbase (se 4 (by rfl) ⟨276075, by rfl⟩ : syracuseStep 2944805 = 552151) (by norm_num)
theorem B1963203 : Blo 1961435 1963203 := bstep (se 1 (by rfl) ⟨1472402, by rfl⟩ : syracuseStep 1963203 = 2944805) B2944805
theorem B2484685 : Blo 1961435 2484685 := bbase (se 3 (by rfl) ⟨465878, by rfl⟩ : syracuseStep 2484685 = 931757) (by norm_num)
theorem B3312913 : Blo 1961435 3312913 := bstep (se 2 (by rfl) ⟨1242342, by rfl⟩ : syracuseStep 3312913 = 2484685) B2484685
theorem B4417217 : Blo 1961435 4417217 := bstep (se 2 (by rfl) ⟨1656456, by rfl⟩ : syracuseStep 4417217 = 3312913) B3312913
theorem B2944811 : Blo 1961435 2944811 := bstep (se 1 (by rfl) ⟨2208608, by rfl⟩ : syracuseStep 2944811 = 4417217) B4417217
theorem B1963207 : Blo 1961435 1963207 := bstep (se 1 (by rfl) ⟨1472405, by rfl⟩ : syracuseStep 1963207 = 2944811) B2944811
theorem B2208613 : Blo 1961435 2208613 := bbase (se 4 (by rfl) ⟨207057, by rfl⟩ : syracuseStep 2208613 = 414115) (by norm_num)
theorem B2944817 : Blo 1961435 2944817 := bstep (se 2 (by rfl) ⟨1104306, by rfl⟩ : syracuseStep 2944817 = 2208613) B2208613
theorem B1963211 : Blo 1961435 1963211 := bstep (se 1 (by rfl) ⟨1472408, by rfl⟩ : syracuseStep 1963211 = 2944817) B2944817
theorem B5590565 : Blo 1961435 5590565 := bbase (se 4 (by rfl) ⟨524115, by rfl⟩ : syracuseStep 5590565 = 1048231) (by norm_num)
theorem B3727043 : Blo 1961435 3727043 := bstep (se 1 (by rfl) ⟨2795282, by rfl⟩ : syracuseStep 3727043 = 5590565) B5590565
theorem B2484695 : Blo 1961435 2484695 := bstep (se 1 (by rfl) ⟨1863521, by rfl⟩ : syracuseStep 2484695 = 3727043) B3727043
theorem B6625853 : Blo 1961435 6625853 := bstep (se 3 (by rfl) ⟨1242347, by rfl⟩ : syracuseStep 6625853 = 2484695) B2484695
theorem B4417235 : Blo 1961435 4417235 := bstep (se 1 (by rfl) ⟨3312926, by rfl⟩ : syracuseStep 4417235 = 6625853) B6625853
theorem B2944823 : Blo 1961435 2944823 := bstep (se 1 (by rfl) ⟨2208617, by rfl⟩ : syracuseStep 2944823 = 4417235) B4417235
theorem B1963215 : Blo 1961435 1963215 := bstep (se 1 (by rfl) ⟨1472411, by rfl⟩ : syracuseStep 1963215 = 2944823) B2944823
theorem B2944829 : Blo 1961435 2944829 := bbase (se 3 (by rfl) ⟨552155, by rfl⟩ : syracuseStep 2944829 = 1104311) (by norm_num)
theorem B1963219 : Blo 1961435 1963219 := bstep (se 1 (by rfl) ⟨1472414, by rfl⟩ : syracuseStep 1963219 = 2944829) B2944829
theorem B4417253 : Blo 1961435 4417253 := bbase (se 4 (by rfl) ⟨414117, by rfl⟩ : syracuseStep 4417253 = 828235) (by norm_num)
theorem B2944835 : Blo 1961435 2944835 := bstep (se 1 (by rfl) ⟨2208626, by rfl⟩ : syracuseStep 2944835 = 4417253) B4417253
theorem B1963223 : Blo 1961435 1963223 := bstep (se 1 (by rfl) ⟨1472417, by rfl⟩ : syracuseStep 1963223 = 2944835) B2944835
theorem B4969421 : Blo 1961435 4969421 := bbase (se 3 (by rfl) ⟨931766, by rfl⟩ : syracuseStep 4969421 = 1863533) (by norm_num)
theorem B3312947 : Blo 1961435 3312947 := bstep (se 1 (by rfl) ⟨2484710, by rfl⟩ : syracuseStep 3312947 = 4969421) B4969421
theorem B2208631 : Blo 1961435 2208631 := bstep (se 1 (by rfl) ⟨1656473, by rfl⟩ : syracuseStep 2208631 = 3312947) B3312947
theorem B2944841 : Blo 1961435 2944841 := bstep (se 2 (by rfl) ⟨1104315, by rfl⟩ : syracuseStep 2944841 = 2208631) B2208631
theorem B1963227 : Blo 1961435 1963227 := bstep (se 1 (by rfl) ⟨1472420, by rfl⟩ : syracuseStep 1963227 = 2944841) B2944841
theorem B10613429 : Blo 1961435 10613429 := bbase (se 5 (by rfl) ⟨497504, by rfl⟩ : syracuseStep 10613429 = 995009) (by norm_num)
theorem B7075619 : Blo 1961435 7075619 := bstep (se 1 (by rfl) ⟨5306714, by rfl⟩ : syracuseStep 7075619 = 10613429) B10613429
theorem B4717079 : Blo 1961435 4717079 := bstep (se 1 (by rfl) ⟨3537809, by rfl⟩ : syracuseStep 4717079 = 7075619) B7075619
theorem B3144719 : Blo 1961435 3144719 := bstep (se 1 (by rfl) ⟨2358539, by rfl⟩ : syracuseStep 3144719 = 4717079) B4717079
theorem B2096479 : Blo 1961435 2096479 := bstep (se 1 (by rfl) ⟨1572359, by rfl⟩ : syracuseStep 2096479 = 3144719) B3144719
theorem B2795305 : Blo 1961435 2795305 := bstep (se 2 (by rfl) ⟨1048239, by rfl⟩ : syracuseStep 2795305 = 2096479) B2096479
theorem B3727073 : Blo 1961435 3727073 := bstep (se 2 (by rfl) ⟨1397652, by rfl⟩ : syracuseStep 3727073 = 2795305) B2795305
theorem B9938861 : Blo 1961435 9938861 := bstep (se 3 (by rfl) ⟨1863536, by rfl⟩ : syracuseStep 9938861 = 3727073) B3727073
theorem B6625907 : Blo 1961435 6625907 := bstep (se 1 (by rfl) ⟨4969430, by rfl⟩ : syracuseStep 6625907 = 9938861) B9938861
theorem B4417271 : Blo 1961435 4417271 := bstep (se 1 (by rfl) ⟨3312953, by rfl⟩ : syracuseStep 4417271 = 6625907) B6625907
theorem B2944847 : Blo 1961435 2944847 := bstep (se 1 (by rfl) ⟨2208635, by rfl⟩ : syracuseStep 2944847 = 4417271) B4417271
theorem B1963231 : Blo 1961435 1963231 := bstep (se 1 (by rfl) ⟨1472423, by rfl⟩ : syracuseStep 1963231 = 2944847) B2944847
theorem B2944853 : Blo 1961435 2944853 := bbase (se 9 (by rfl) ⟨8627, by rfl⟩ : syracuseStep 2944853 = 17255) (by norm_num)
theorem B1963235 : Blo 1961435 1963235 := bstep (se 1 (by rfl) ⟨1472426, by rfl⟩ : syracuseStep 1963235 = 2944853) B2944853
theorem B20149013 : Blo 1961435 20149013 := bbase (se 6 (by rfl) ⟨472242, by rfl⟩ : syracuseStep 20149013 = 944485) (by norm_num)
theorem B13432675 : Blo 1961435 13432675 := bstep (se 1 (by rfl) ⟨10074506, by rfl⟩ : syracuseStep 13432675 = 20149013) B20149013
theorem B17910233 : Blo 1961435 17910233 := bstep (se 2 (by rfl) ⟨6716337, by rfl⟩ : syracuseStep 17910233 = 13432675) B13432675
theorem B11940155 : Blo 1961435 11940155 := bstep (se 1 (by rfl) ⟨8955116, by rfl⟩ : syracuseStep 11940155 = 17910233) B17910233
theorem B7960103 : Blo 1961435 7960103 := bstep (se 1 (by rfl) ⟨5970077, by rfl⟩ : syracuseStep 7960103 = 11940155) B11940155
theorem B5306735 : Blo 1961435 5306735 := bstep (se 1 (by rfl) ⟨3980051, by rfl⟩ : syracuseStep 5306735 = 7960103) B7960103
theorem B14151293 : Blo 1961435 14151293 := bstep (se 3 (by rfl) ⟨2653367, by rfl⟩ : syracuseStep 14151293 = 5306735) B5306735
theorem B9434195 : Blo 1961435 9434195 := bstep (se 1 (by rfl) ⟨7075646, by rfl⟩ : syracuseStep 9434195 = 14151293) B14151293
theorem B6289463 : Blo 1961435 6289463 := bstep (se 1 (by rfl) ⟨4717097, by rfl⟩ : syracuseStep 6289463 = 9434195) B9434195
theorem B4192975 : Blo 1961435 4192975 := bstep (se 1 (by rfl) ⟨3144731, by rfl⟩ : syracuseStep 4192975 = 6289463) B6289463
theorem B5590633 : Blo 1961435 5590633 := bstep (se 2 (by rfl) ⟨2096487, by rfl⟩ : syracuseStep 5590633 = 4192975) B4192975
theorem B7454177 : Blo 1961435 7454177 := bstep (se 2 (by rfl) ⟨2795316, by rfl⟩ : syracuseStep 7454177 = 5590633) B5590633
theorem B4969451 : Blo 1961435 4969451 := bstep (se 1 (by rfl) ⟨3727088, by rfl⟩ : syracuseStep 4969451 = 7454177) B7454177
theorem B3312967 : Blo 1961435 3312967 := bstep (se 1 (by rfl) ⟨2484725, by rfl⟩ : syracuseStep 3312967 = 4969451) B4969451
theorem B4417289 : Blo 1961435 4417289 := bstep (se 2 (by rfl) ⟨1656483, by rfl⟩ : syracuseStep 4417289 = 3312967) B3312967
theorem B2944859 : Blo 1961435 2944859 := bstep (se 1 (by rfl) ⟨2208644, by rfl⟩ : syracuseStep 2944859 = 4417289) B4417289
theorem B1963239 : Blo 1961435 1963239 := bstep (se 1 (by rfl) ⟨1472429, by rfl⟩ : syracuseStep 1963239 = 2944859) B2944859
theorem B2208649 : Blo 1961435 2208649 := bbase (se 2 (by rfl) ⟨828243, by rfl⟩ : syracuseStep 2208649 = 1656487) (by norm_num)
theorem B2944865 : Blo 1961435 2944865 := bstep (se 2 (by rfl) ⟨1104324, by rfl⟩ : syracuseStep 2944865 = 2208649) B2208649
theorem B1963243 : Blo 1961435 1963243 := bstep (se 1 (by rfl) ⟨1472432, by rfl⟩ : syracuseStep 1963243 = 2944865) B2944865
theorem B25849109 : Blo 1961435 25849109 := bbase (se 6 (by rfl) ⟨605838, by rfl⟩ : syracuseStep 25849109 = 1211677) (by norm_num)
theorem B68930957 : Blo 1961435 68930957 := bstep (se 3 (by rfl) ⟨12924554, by rfl⟩ : syracuseStep 68930957 = 25849109) B25849109
theorem B183815885 : Blo 1961435 183815885 := bstep (se 3 (by rfl) ⟨34465478, by rfl⟩ : syracuseStep 183815885 = 68930957) B68930957
theorem B122543923 : Blo 1961435 122543923 := bstep (se 1 (by rfl) ⟨91907942, by rfl⟩ : syracuseStep 122543923 = 183815885) B183815885
theorem B163391897 : Blo 1961435 163391897 := bstep (se 2 (by rfl) ⟨61271961, by rfl⟩ : syracuseStep 163391897 = 122543923) B122543923
theorem B108927931 : Blo 1961435 108927931 := bstep (se 1 (by rfl) ⟨81695948, by rfl⟩ : syracuseStep 108927931 = 163391897) B163391897
theorem B145237241 : Blo 1961435 145237241 := bstep (se 2 (by rfl) ⟨54463965, by rfl⟩ : syracuseStep 145237241 = 108927931) B108927931
theorem B96824827 : Blo 1961435 96824827 := bstep (se 1 (by rfl) ⟨72618620, by rfl⟩ : syracuseStep 96824827 = 145237241) B145237241
theorem B516399077 : Blo 1961435 516399077 := bstep (se 4 (by rfl) ⟨48412413, by rfl⟩ : syracuseStep 516399077 = 96824827) B96824827
theorem B344266051 : Blo 1961435 344266051 := bstep (se 1 (by rfl) ⟨258199538, by rfl⟩ : syracuseStep 344266051 = 516399077) B516399077
theorem B459021401 : Blo 1961435 459021401 := bstep (se 2 (by rfl) ⟨172133025, by rfl⟩ : syracuseStep 459021401 = 344266051) B344266051
theorem B306014267 : Blo 1961435 306014267 := bstep (se 1 (by rfl) ⟨229510700, by rfl⟩ : syracuseStep 306014267 = 459021401) B459021401
theorem B204009511 : Blo 1961435 204009511 := bstep (se 1 (by rfl) ⟨153007133, by rfl⟩ : syracuseStep 204009511 = 306014267) B306014267
theorem B272012681 : Blo 1961435 272012681 := bstep (se 2 (by rfl) ⟨102004755, by rfl⟩ : syracuseStep 272012681 = 204009511) B204009511
theorem B181341787 : Blo 1961435 181341787 := bstep (se 1 (by rfl) ⟨136006340, by rfl⟩ : syracuseStep 181341787 = 272012681) B272012681
theorem B241789049 : Blo 1961435 241789049 := bstep (se 2 (by rfl) ⟨90670893, by rfl⟩ : syracuseStep 241789049 = 181341787) B181341787
theorem B161192699 : Blo 1961435 161192699 := bstep (se 1 (by rfl) ⟨120894524, by rfl⟩ : syracuseStep 161192699 = 241789049) B241789049
theorem B107461799 : Blo 1961435 107461799 := bstep (se 1 (by rfl) ⟨80596349, by rfl⟩ : syracuseStep 107461799 = 161192699) B161192699
theorem B71641199 : Blo 1961435 71641199 := bstep (se 1 (by rfl) ⟨53730899, by rfl⟩ : syracuseStep 71641199 = 107461799) B107461799
theorem B191043197 : Blo 1961435 191043197 := bstep (se 3 (by rfl) ⟨35820599, by rfl⟩ : syracuseStep 191043197 = 71641199) B71641199
theorem B127362131 : Blo 1961435 127362131 := bstep (se 1 (by rfl) ⟨95521598, by rfl⟩ : syracuseStep 127362131 = 191043197) B191043197
theorem B84908087 : Blo 1961435 84908087 := bstep (se 1 (by rfl) ⟨63681065, by rfl⟩ : syracuseStep 84908087 = 127362131) B127362131
theorem B56605391 : Blo 1961435 56605391 := bstep (se 1 (by rfl) ⟨42454043, by rfl⟩ : syracuseStep 56605391 = 84908087) B84908087
theorem B37736927 : Blo 1961435 37736927 := bstep (se 1 (by rfl) ⟨28302695, by rfl⟩ : syracuseStep 37736927 = 56605391) B56605391
theorem B25157951 : Blo 1961435 25157951 := bstep (se 1 (by rfl) ⟨18868463, by rfl⟩ : syracuseStep 25157951 = 37736927) B37736927
theorem B16771967 : Blo 1961435 16771967 := bstep (se 1 (by rfl) ⟨12578975, by rfl⟩ : syracuseStep 16771967 = 25157951) B25157951
theorem B11181311 : Blo 1961435 11181311 := bstep (se 1 (by rfl) ⟨8385983, by rfl⟩ : syracuseStep 11181311 = 16771967) B16771967
theorem B7454207 : Blo 1961435 7454207 := bstep (se 1 (by rfl) ⟨5590655, by rfl⟩ : syracuseStep 7454207 = 11181311) B11181311
theorem B4969471 : Blo 1961435 4969471 := bstep (se 1 (by rfl) ⟨3727103, by rfl⟩ : syracuseStep 4969471 = 7454207) B7454207
theorem B6625961 : Blo 1961435 6625961 := bstep (se 2 (by rfl) ⟨2484735, by rfl⟩ : syracuseStep 6625961 = 4969471) B4969471
theorem B4417307 : Blo 1961435 4417307 := bstep (se 1 (by rfl) ⟨3312980, by rfl⟩ : syracuseStep 4417307 = 6625961) B6625961
theorem B2944871 : Blo 1961435 2944871 := bstep (se 1 (by rfl) ⟨2208653, by rfl⟩ : syracuseStep 2944871 = 4417307) B4417307
theorem B1963247 : Blo 1961435 1963247 := bstep (se 1 (by rfl) ⟨1472435, by rfl⟩ : syracuseStep 1963247 = 2944871) B2944871
theorem B2944877 : Blo 1961435 2944877 := bbase (se 3 (by rfl) ⟨552164, by rfl⟩ : syracuseStep 2944877 = 1104329) (by norm_num)
theorem B1963251 : Blo 1961435 1963251 := bstep (se 1 (by rfl) ⟨1472438, by rfl⟩ : syracuseStep 1963251 = 2944877) B2944877
theorem B4417325 : Blo 1961435 4417325 := bbase (se 3 (by rfl) ⟨828248, by rfl⟩ : syracuseStep 4417325 = 1656497) (by norm_num)
theorem B2944883 : Blo 1961435 2944883 := bstep (se 1 (by rfl) ⟨2208662, by rfl⟩ : syracuseStep 2944883 = 4417325) B4417325
theorem B1963255 : Blo 1961435 1963255 := bstep (se 1 (by rfl) ⟨1472441, by rfl⟩ : syracuseStep 1963255 = 2944883) B2944883
theorem B8386037 : Blo 1961435 8386037 := bbase (se 5 (by rfl) ⟨393095, by rfl⟩ : syracuseStep 8386037 = 786191) (by norm_num)
theorem B5590691 : Blo 1961435 5590691 := bstep (se 1 (by rfl) ⟨4193018, by rfl⟩ : syracuseStep 5590691 = 8386037) B8386037
theorem B3727127 : Blo 1961435 3727127 := bstep (se 1 (by rfl) ⟨2795345, by rfl⟩ : syracuseStep 3727127 = 5590691) B5590691
theorem B2484751 : Blo 1961435 2484751 := bstep (se 1 (by rfl) ⟨1863563, by rfl⟩ : syracuseStep 2484751 = 3727127) B3727127
theorem B3313001 : Blo 1961435 3313001 := bstep (se 2 (by rfl) ⟨1242375, by rfl⟩ : syracuseStep 3313001 = 2484751) B2484751
theorem B2208667 : Blo 1961435 2208667 := bstep (se 1 (by rfl) ⟨1656500, by rfl⟩ : syracuseStep 2208667 = 3313001) B3313001
theorem B2944889 : Blo 1961435 2944889 := bstep (se 2 (by rfl) ⟨1104333, by rfl⟩ : syracuseStep 2944889 = 2208667) B2208667
theorem B1963259 : Blo 1961435 1963259 := bstep (se 1 (by rfl) ⟨1472444, by rfl⟩ : syracuseStep 1963259 = 2944889) B2944889
theorem B2358577 : Blo 1961435 2358577 := bbase (se 2 (by rfl) ⟨884466, by rfl⟩ : syracuseStep 2358577 = 1768933) (by norm_num)
theorem B12579077 : Blo 1961435 12579077 := bstep (se 4 (by rfl) ⟨1179288, by rfl⟩ : syracuseStep 12579077 = 2358577) B2358577
theorem B33544205 : Blo 1961435 33544205 := bstep (se 3 (by rfl) ⟨6289538, by rfl⟩ : syracuseStep 33544205 = 12579077) B12579077
theorem B22362803 : Blo 1961435 22362803 := bstep (se 1 (by rfl) ⟨16772102, by rfl⟩ : syracuseStep 22362803 = 33544205) B33544205
theorem B14908535 : Blo 1961435 14908535 := bstep (se 1 (by rfl) ⟨11181401, by rfl⟩ : syracuseStep 14908535 = 22362803) B22362803
theorem B9939023 : Blo 1961435 9939023 := bstep (se 1 (by rfl) ⟨7454267, by rfl⟩ : syracuseStep 9939023 = 14908535) B14908535
theorem B6626015 : Blo 1961435 6626015 := bstep (se 1 (by rfl) ⟨4969511, by rfl⟩ : syracuseStep 6626015 = 9939023) B9939023
theorem B4417343 : Blo 1961435 4417343 := bstep (se 1 (by rfl) ⟨3313007, by rfl⟩ : syracuseStep 4417343 = 6626015) B6626015
theorem B2944895 : Blo 1961435 2944895 := bstep (se 1 (by rfl) ⟨2208671, by rfl⟩ : syracuseStep 2944895 = 4417343) B4417343
theorem B1963263 : Blo 1961435 1963263 := bstep (se 1 (by rfl) ⟨1472447, by rfl⟩ : syracuseStep 1963263 = 2944895) B2944895
theorem B2944901 : Blo 1961435 2944901 := bbase (se 4 (by rfl) ⟨276084, by rfl⟩ : syracuseStep 2944901 = 552169) (by norm_num)
theorem B1963267 : Blo 1961435 1963267 := bstep (se 1 (by rfl) ⟨1472450, by rfl⟩ : syracuseStep 1963267 = 2944901) B2944901
theorem B3313021 : Blo 1961435 3313021 := bbase (se 3 (by rfl) ⟨621191, by rfl⟩ : syracuseStep 3313021 = 1242383) (by norm_num)
theorem B4417361 : Blo 1961435 4417361 := bstep (se 2 (by rfl) ⟨1656510, by rfl⟩ : syracuseStep 4417361 = 3313021) B3313021
theorem B2944907 : Blo 1961435 2944907 := bstep (se 1 (by rfl) ⟨2208680, by rfl⟩ : syracuseStep 2944907 = 4417361) B4417361
theorem B1963271 : Blo 1961435 1963271 := bstep (se 1 (by rfl) ⟨1472453, by rfl⟩ : syracuseStep 1963271 = 2944907) B2944907
theorem B2208685 : Blo 1961435 2208685 := bbase (se 3 (by rfl) ⟨414128, by rfl⟩ : syracuseStep 2208685 = 828257) (by norm_num)
theorem B2944913 : Blo 1961435 2944913 := bstep (se 2 (by rfl) ⟨1104342, by rfl⟩ : syracuseStep 2944913 = 2208685) B2208685
theorem B1963275 : Blo 1961435 1963275 := bstep (se 1 (by rfl) ⟨1472456, by rfl⟩ : syracuseStep 1963275 = 2944913) B2944913
theorem B6626069 : Blo 1961435 6626069 := bbase (se 6 (by rfl) ⟨155298, by rfl⟩ : syracuseStep 6626069 = 310597) (by norm_num)
theorem B4417379 : Blo 1961435 4417379 := bstep (se 1 (by rfl) ⟨3313034, by rfl⟩ : syracuseStep 4417379 = 6626069) B6626069
theorem B2944919 : Blo 1961435 2944919 := bstep (se 1 (by rfl) ⟨2208689, by rfl⟩ : syracuseStep 2944919 = 4417379) B4417379
theorem B1963279 : Blo 1961435 1963279 := bstep (se 1 (by rfl) ⟨1472459, by rfl⟩ : syracuseStep 1963279 = 2944919) B2944919
theorem B2944925 : Blo 1961435 2944925 := bbase (se 3 (by rfl) ⟨552173, by rfl⟩ : syracuseStep 2944925 = 1104347) (by norm_num)
theorem B1963283 : Blo 1961435 1963283 := bstep (se 1 (by rfl) ⟨1472462, by rfl⟩ : syracuseStep 1963283 = 2944925) B2944925
theorem B4417397 : Blo 1961435 4417397 := bbase (se 5 (by rfl) ⟨207065, by rfl⟩ : syracuseStep 4417397 = 414131) (by norm_num)
theorem B2944931 : Blo 1961435 2944931 := bstep (se 1 (by rfl) ⟨2208698, by rfl⟩ : syracuseStep 2944931 = 4417397) B4417397
theorem B1963287 : Blo 1961435 1963287 := bstep (se 1 (by rfl) ⟨1472465, by rfl⟩ : syracuseStep 1963287 = 2944931) B2944931
theorem B10074773 : Blo 1961435 10074773 := bbase (se 6 (by rfl) ⟨236127, by rfl⟩ : syracuseStep 10074773 = 472255) (by norm_num)
theorem B6716515 : Blo 1961435 6716515 := bstep (se 1 (by rfl) ⟨5037386, by rfl⟩ : syracuseStep 6716515 = 10074773) B10074773
theorem B8955353 : Blo 1961435 8955353 := bstep (se 2 (by rfl) ⟨3358257, by rfl⟩ : syracuseStep 8955353 = 6716515) B6716515
theorem B5970235 : Blo 1961435 5970235 := bstep (se 1 (by rfl) ⟨4477676, by rfl⟩ : syracuseStep 5970235 = 8955353) B8955353
theorem B7960313 : Blo 1961435 7960313 := bstep (se 2 (by rfl) ⟨2985117, by rfl⟩ : syracuseStep 7960313 = 5970235) B5970235
theorem B21227501 : Blo 1961435 21227501 := bstep (se 3 (by rfl) ⟨3980156, by rfl⟩ : syracuseStep 21227501 = 7960313) B7960313
theorem B14151667 : Blo 1961435 14151667 := bstep (se 1 (by rfl) ⟨10613750, by rfl⟩ : syracuseStep 14151667 = 21227501) B21227501
theorem B18868889 : Blo 1961435 18868889 := bstep (se 2 (by rfl) ⟨7075833, by rfl⟩ : syracuseStep 18868889 = 14151667) B14151667
theorem B12579259 : Blo 1961435 12579259 := bstep (se 1 (by rfl) ⟨9434444, by rfl⟩ : syracuseStep 12579259 = 18868889) B18868889
theorem B16772345 : Blo 1961435 16772345 := bstep (se 2 (by rfl) ⟨6289629, by rfl⟩ : syracuseStep 16772345 = 12579259) B12579259
theorem B11181563 : Blo 1961435 11181563 := bstep (se 1 (by rfl) ⟨8386172, by rfl⟩ : syracuseStep 11181563 = 16772345) B16772345
theorem B7454375 : Blo 1961435 7454375 := bstep (se 1 (by rfl) ⟨5590781, by rfl⟩ : syracuseStep 7454375 = 11181563) B11181563
theorem B4969583 : Blo 1961435 4969583 := bstep (se 1 (by rfl) ⟨3727187, by rfl⟩ : syracuseStep 4969583 = 7454375) B7454375
theorem B3313055 : Blo 1961435 3313055 := bstep (se 1 (by rfl) ⟨2484791, by rfl⟩ : syracuseStep 3313055 = 4969583) B4969583
theorem B2208703 : Blo 1961435 2208703 := bstep (se 1 (by rfl) ⟨1656527, by rfl⟩ : syracuseStep 2208703 = 3313055) B3313055
theorem B2944937 : Blo 1961435 2944937 := bstep (se 2 (by rfl) ⟨1104351, by rfl⟩ : syracuseStep 2944937 = 2208703) B2208703
theorem B1963291 : Blo 1961435 1963291 := bstep (se 1 (by rfl) ⟨1472468, by rfl⟩ : syracuseStep 1963291 = 2944937) B2944937
theorem B7454389 : Blo 1961435 7454389 := bbase (se 5 (by rfl) ⟨349424, by rfl⟩ : syracuseStep 7454389 = 698849) (by norm_num)
theorem B9939185 : Blo 1961435 9939185 := bstep (se 2 (by rfl) ⟨3727194, by rfl⟩ : syracuseStep 9939185 = 7454389) B7454389
theorem B6626123 : Blo 1961435 6626123 := bstep (se 1 (by rfl) ⟨4969592, by rfl⟩ : syracuseStep 6626123 = 9939185) B9939185
theorem B4417415 : Blo 1961435 4417415 := bstep (se 1 (by rfl) ⟨3313061, by rfl⟩ : syracuseStep 4417415 = 6626123) B6626123
theorem B2944943 : Blo 1961435 2944943 := bstep (se 1 (by rfl) ⟨2208707, by rfl⟩ : syracuseStep 2944943 = 4417415) B4417415
theorem B1963295 : Blo 1961435 1963295 := bstep (se 1 (by rfl) ⟨1472471, by rfl⟩ : syracuseStep 1963295 = 2944943) B2944943
theorem B2944949 : Blo 1961435 2944949 := bbase (se 5 (by rfl) ⟨138044, by rfl⟩ : syracuseStep 2944949 = 276089) (by norm_num)
theorem B1963299 : Blo 1961435 1963299 := bstep (se 1 (by rfl) ⟨1472474, by rfl⟩ : syracuseStep 1963299 = 2944949) B2944949
theorem B4969613 : Blo 1961435 4969613 := bbase (se 3 (by rfl) ⟨931802, by rfl⟩ : syracuseStep 4969613 = 1863605) (by norm_num)
theorem B3313075 : Blo 1961435 3313075 := bstep (se 1 (by rfl) ⟨2484806, by rfl⟩ : syracuseStep 3313075 = 4969613) B4969613
theorem B4417433 : Blo 1961435 4417433 := bstep (se 2 (by rfl) ⟨1656537, by rfl⟩ : syracuseStep 4417433 = 3313075) B3313075
theorem B2944955 : Blo 1961435 2944955 := bstep (se 1 (by rfl) ⟨2208716, by rfl⟩ : syracuseStep 2944955 = 4417433) B4417433
theorem B1963303 : Blo 1961435 1963303 := bstep (se 1 (by rfl) ⟨1472477, by rfl⟩ : syracuseStep 1963303 = 2944955) B2944955
theorem B2208721 : Blo 1961435 2208721 := bbase (se 2 (by rfl) ⟨828270, by rfl⟩ : syracuseStep 2208721 = 1656541) (by norm_num)
theorem B2944961 : Blo 1961435 2944961 := bstep (se 2 (by rfl) ⟨1104360, by rfl⟩ : syracuseStep 2944961 = 2208721) B2208721
theorem B1963307 : Blo 1961435 1963307 := bstep (se 1 (by rfl) ⟨1472480, by rfl⟩ : syracuseStep 1963307 = 2944961) B2944961
theorem B2985149 : Blo 1961435 2985149 := bbase (se 3 (by rfl) ⟨559715, by rfl⟩ : syracuseStep 2985149 = 1119431) (by norm_num)
theorem B1990099 : Blo 1961435 1990099 := bstep (se 1 (by rfl) ⟨1492574, by rfl⟩ : syracuseStep 1990099 = 2985149) B2985149
theorem B10613861 : Blo 1961435 10613861 := bstep (se 4 (by rfl) ⟨995049, by rfl⟩ : syracuseStep 10613861 = 1990099) B1990099
theorem B7075907 : Blo 1961435 7075907 := bstep (se 1 (by rfl) ⟨5306930, by rfl⟩ : syracuseStep 7075907 = 10613861) B10613861
theorem B4717271 : Blo 1961435 4717271 := bstep (se 1 (by rfl) ⟨3537953, by rfl⟩ : syracuseStep 4717271 = 7075907) B7075907
theorem B3144847 : Blo 1961435 3144847 := bstep (se 1 (by rfl) ⟨2358635, by rfl⟩ : syracuseStep 3144847 = 4717271) B4717271
theorem B4193129 : Blo 1961435 4193129 := bstep (se 2 (by rfl) ⟨1572423, by rfl⟩ : syracuseStep 4193129 = 3144847) B3144847
theorem B2795419 : Blo 1961435 2795419 := bstep (se 1 (by rfl) ⟨2096564, by rfl⟩ : syracuseStep 2795419 = 4193129) B4193129
theorem B3727225 : Blo 1961435 3727225 := bstep (se 2 (by rfl) ⟨1397709, by rfl⟩ : syracuseStep 3727225 = 2795419) B2795419
theorem B4969633 : Blo 1961435 4969633 := bstep (se 2 (by rfl) ⟨1863612, by rfl⟩ : syracuseStep 4969633 = 3727225) B3727225
theorem B6626177 : Blo 1961435 6626177 := bstep (se 2 (by rfl) ⟨2484816, by rfl⟩ : syracuseStep 6626177 = 4969633) B4969633
theorem B4417451 : Blo 1961435 4417451 := bstep (se 1 (by rfl) ⟨3313088, by rfl⟩ : syracuseStep 4417451 = 6626177) B6626177
theorem B2944967 : Blo 1961435 2944967 := bstep (se 1 (by rfl) ⟨2208725, by rfl⟩ : syracuseStep 2944967 = 4417451) B4417451
theorem B1963311 : Blo 1961435 1963311 := bstep (se 1 (by rfl) ⟨1472483, by rfl⟩ : syracuseStep 1963311 = 2944967) B2944967
theorem B2944973 : Blo 1961435 2944973 := bbase (se 3 (by rfl) ⟨552182, by rfl⟩ : syracuseStep 2944973 = 1104365) (by norm_num)
theorem B1963315 : Blo 1961435 1963315 := bstep (se 1 (by rfl) ⟨1472486, by rfl⟩ : syracuseStep 1963315 = 2944973) B2944973
theorem B4417469 : Blo 1961435 4417469 := bbase (se 3 (by rfl) ⟨828275, by rfl⟩ : syracuseStep 4417469 = 1656551) (by norm_num)
theorem B2944979 : Blo 1961435 2944979 := bstep (se 1 (by rfl) ⟨2208734, by rfl⟩ : syracuseStep 2944979 = 4417469) B4417469
theorem B1963319 : Blo 1961435 1963319 := bstep (se 1 (by rfl) ⟨1472489, by rfl⟩ : syracuseStep 1963319 = 2944979) B2944979
theorem B3313109 : Blo 1961435 3313109 := bbase (se 7 (by rfl) ⟨38825, by rfl⟩ : syracuseStep 3313109 = 77651) (by norm_num)
theorem B2208739 : Blo 1961435 2208739 := bstep (se 1 (by rfl) ⟨1656554, by rfl⟩ : syracuseStep 2208739 = 3313109) B3313109
theorem B2944985 : Blo 1961435 2944985 := bstep (se 2 (by rfl) ⟨1104369, by rfl⟩ : syracuseStep 2944985 = 2208739) B2208739
theorem B1963323 : Blo 1961435 1963323 := bstep (se 1 (by rfl) ⟨1472492, by rfl⟩ : syracuseStep 1963323 = 2944985) B2944985
theorem B8386325 : Blo 1961435 8386325 := bbase (se 6 (by rfl) ⟨196554, by rfl⟩ : syracuseStep 8386325 = 393109) (by norm_num)
theorem B5590883 : Blo 1961435 5590883 := bstep (se 1 (by rfl) ⟨4193162, by rfl⟩ : syracuseStep 5590883 = 8386325) B8386325
theorem B14909021 : Blo 1961435 14909021 := bstep (se 3 (by rfl) ⟨2795441, by rfl⟩ : syracuseStep 14909021 = 5590883) B5590883
theorem B9939347 : Blo 1961435 9939347 := bstep (se 1 (by rfl) ⟨7454510, by rfl⟩ : syracuseStep 9939347 = 14909021) B14909021
theorem B6626231 : Blo 1961435 6626231 := bstep (se 1 (by rfl) ⟨4969673, by rfl⟩ : syracuseStep 6626231 = 9939347) B9939347
theorem B4417487 : Blo 1961435 4417487 := bstep (se 1 (by rfl) ⟨3313115, by rfl⟩ : syracuseStep 4417487 = 6626231) B6626231
theorem B2944991 : Blo 1961435 2944991 := bstep (se 1 (by rfl) ⟨2208743, by rfl⟩ : syracuseStep 2944991 = 4417487) B4417487
theorem B1963327 : Blo 1961435 1963327 := bstep (se 1 (by rfl) ⟨1472495, by rfl⟩ : syracuseStep 1963327 = 2944991) B2944991
theorem B2944997 : Blo 1961435 2944997 := bbase (se 4 (by rfl) ⟨276093, by rfl⟩ : syracuseStep 2944997 = 552187) (by norm_num)
theorem B1963331 : Blo 1961435 1963331 := bstep (se 1 (by rfl) ⟨1472498, by rfl⟩ : syracuseStep 1963331 = 2944997) B2944997
theorem B2238889 : Blo 1961435 2238889 := bbase (se 2 (by rfl) ⟨839583, by rfl⟩ : syracuseStep 2238889 = 1679167) (by norm_num)
theorem B2985185 : Blo 1961435 2985185 := bstep (se 2 (by rfl) ⟨1119444, by rfl⟩ : syracuseStep 2985185 = 2238889) B2238889
theorem B7960493 : Blo 1961435 7960493 := bstep (se 3 (by rfl) ⟨1492592, by rfl⟩ : syracuseStep 7960493 = 2985185) B2985185
theorem B5306995 : Blo 1961435 5306995 := bstep (se 1 (by rfl) ⟨3980246, by rfl⟩ : syracuseStep 5306995 = 7960493) B7960493
theorem B7075993 : Blo 1961435 7075993 := bstep (se 2 (by rfl) ⟨2653497, by rfl⟩ : syracuseStep 7075993 = 5306995) B5306995
theorem B9434657 : Blo 1961435 9434657 := bstep (se 2 (by rfl) ⟨3537996, by rfl⟩ : syracuseStep 9434657 = 7075993) B7075993
theorem B6289771 : Blo 1961435 6289771 := bstep (se 1 (by rfl) ⟨4717328, by rfl⟩ : syracuseStep 6289771 = 9434657) B9434657
theorem B8386361 : Blo 1961435 8386361 := bstep (se 2 (by rfl) ⟨3144885, by rfl⟩ : syracuseStep 8386361 = 6289771) B6289771
theorem B5590907 : Blo 1961435 5590907 := bstep (se 1 (by rfl) ⟨4193180, by rfl⟩ : syracuseStep 5590907 = 8386361) B8386361
theorem B3727271 : Blo 1961435 3727271 := bstep (se 1 (by rfl) ⟨2795453, by rfl⟩ : syracuseStep 3727271 = 5590907) B5590907
theorem B2484847 : Blo 1961435 2484847 := bstep (se 1 (by rfl) ⟨1863635, by rfl⟩ : syracuseStep 2484847 = 3727271) B3727271
theorem B3313129 : Blo 1961435 3313129 := bstep (se 2 (by rfl) ⟨1242423, by rfl⟩ : syracuseStep 3313129 = 2484847) B2484847
theorem B4417505 : Blo 1961435 4417505 := bstep (se 2 (by rfl) ⟨1656564, by rfl⟩ : syracuseStep 4417505 = 3313129) B3313129
theorem B2945003 : Blo 1961435 2945003 := bstep (se 1 (by rfl) ⟨2208752, by rfl⟩ : syracuseStep 2945003 = 4417505) B4417505
theorem B1963335 : Blo 1961435 1963335 := bstep (se 1 (by rfl) ⟨1472501, by rfl⟩ : syracuseStep 1963335 = 2945003) B2945003
theorem B2208757 : Blo 1961435 2208757 := bbase (se 5 (by rfl) ⟨103535, by rfl⟩ : syracuseStep 2208757 = 207071) (by norm_num)
theorem B2945009 : Blo 1961435 2945009 := bstep (se 2 (by rfl) ⟨1104378, by rfl⟩ : syracuseStep 2945009 = 2208757) B2208757
theorem B1963339 : Blo 1961435 1963339 := bstep (se 1 (by rfl) ⟨1472504, by rfl⟩ : syracuseStep 1963339 = 2945009) B2945009
theorem B2484857 : Blo 1961435 2484857 := bbase (se 2 (by rfl) ⟨931821, by rfl⟩ : syracuseStep 2484857 = 1863643) (by norm_num)
theorem B6626285 : Blo 1961435 6626285 := bstep (se 3 (by rfl) ⟨1242428, by rfl⟩ : syracuseStep 6626285 = 2484857) B2484857
theorem B4417523 : Blo 1961435 4417523 := bstep (se 1 (by rfl) ⟨3313142, by rfl⟩ : syracuseStep 4417523 = 6626285) B6626285
theorem B2945015 : Blo 1961435 2945015 := bstep (se 1 (by rfl) ⟨2208761, by rfl⟩ : syracuseStep 2945015 = 4417523) B4417523
theorem B1963343 : Blo 1961435 1963343 := bstep (se 1 (by rfl) ⟨1472507, by rfl⟩ : syracuseStep 1963343 = 2945015) B2945015
theorem B2945021 : Blo 1961435 2945021 := bbase (se 3 (by rfl) ⟨552191, by rfl⟩ : syracuseStep 2945021 = 1104383) (by norm_num)
theorem B1963347 : Blo 1961435 1963347 := bstep (se 1 (by rfl) ⟨1472510, by rfl⟩ : syracuseStep 1963347 = 2945021) B2945021
theorem B4417541 : Blo 1961435 4417541 := bbase (se 4 (by rfl) ⟨414144, by rfl⟩ : syracuseStep 4417541 = 828289) (by norm_num)
theorem B2945027 : Blo 1961435 2945027 := bstep (se 1 (by rfl) ⟨2208770, by rfl⟩ : syracuseStep 2945027 = 4417541) B4417541
theorem B1963351 : Blo 1961435 1963351 := bstep (se 1 (by rfl) ⟨1472513, by rfl⟩ : syracuseStep 1963351 = 2945027) B2945027
theorem B3727309 : Blo 1961435 3727309 := bbase (se 3 (by rfl) ⟨698870, by rfl⟩ : syracuseStep 3727309 = 1397741) (by norm_num)
theorem B4969745 : Blo 1961435 4969745 := bstep (se 2 (by rfl) ⟨1863654, by rfl⟩ : syracuseStep 4969745 = 3727309) B3727309
theorem B3313163 : Blo 1961435 3313163 := bstep (se 1 (by rfl) ⟨2484872, by rfl⟩ : syracuseStep 3313163 = 4969745) B4969745
theorem B2208775 : Blo 1961435 2208775 := bstep (se 1 (by rfl) ⟨1656581, by rfl⟩ : syracuseStep 2208775 = 3313163) B3313163
theorem B2945033 : Blo 1961435 2945033 := bstep (se 2 (by rfl) ⟨1104387, by rfl⟩ : syracuseStep 2945033 = 2208775) B2208775
theorem B1963355 : Blo 1961435 1963355 := bstep (se 1 (by rfl) ⟨1472516, by rfl⟩ : syracuseStep 1963355 = 2945033) B2945033
theorem B9939509 : Blo 1961435 9939509 := bbase (se 5 (by rfl) ⟨465914, by rfl⟩ : syracuseStep 9939509 = 931829) (by norm_num)
theorem B6626339 : Blo 1961435 6626339 := bstep (se 1 (by rfl) ⟨4969754, by rfl⟩ : syracuseStep 6626339 = 9939509) B9939509
theorem B4417559 : Blo 1961435 4417559 := bstep (se 1 (by rfl) ⟨3313169, by rfl⟩ : syracuseStep 4417559 = 6626339) B6626339
theorem B2945039 : Blo 1961435 2945039 := bstep (se 1 (by rfl) ⟨2208779, by rfl⟩ : syracuseStep 2945039 = 4417559) B4417559
theorem B1963359 : Blo 1961435 1963359 := bstep (se 1 (by rfl) ⟨1472519, by rfl⟩ : syracuseStep 1963359 = 2945039) B2945039
theorem B2945045 : Blo 1961435 2945045 := bbase (se 6 (by rfl) ⟨69024, by rfl⟩ : syracuseStep 2945045 = 138049) (by norm_num)
theorem B1963363 : Blo 1961435 1963363 := bstep (se 1 (by rfl) ⟨1472522, by rfl⟩ : syracuseStep 1963363 = 2945045) B2945045
theorem B2238925 : Blo 1961435 2238925 := bbase (se 3 (by rfl) ⟨419798, by rfl⟩ : syracuseStep 2238925 = 839597) (by norm_num)
theorem B2985233 : Blo 1961435 2985233 := bstep (se 2 (by rfl) ⟨1119462, by rfl⟩ : syracuseStep 2985233 = 2238925) B2238925
theorem B7960621 : Blo 1961435 7960621 := bstep (se 3 (by rfl) ⟨1492616, by rfl⟩ : syracuseStep 7960621 = 2985233) B2985233
theorem B10614161 : Blo 1961435 10614161 := bstep (se 2 (by rfl) ⟨3980310, by rfl⟩ : syracuseStep 10614161 = 7960621) B7960621
theorem B7076107 : Blo 1961435 7076107 := bstep (se 1 (by rfl) ⟨5307080, by rfl⟩ : syracuseStep 7076107 = 10614161) B10614161
theorem B9434809 : Blo 1961435 9434809 := bstep (se 2 (by rfl) ⟨3538053, by rfl⟩ : syracuseStep 9434809 = 7076107) B7076107
theorem B12579745 : Blo 1961435 12579745 := bstep (se 2 (by rfl) ⟨4717404, by rfl⟩ : syracuseStep 12579745 = 9434809) B9434809
theorem B16772993 : Blo 1961435 16772993 := bstep (se 2 (by rfl) ⟨6289872, by rfl⟩ : syracuseStep 16772993 = 12579745) B12579745
theorem B11181995 : Blo 1961435 11181995 := bstep (se 1 (by rfl) ⟨8386496, by rfl⟩ : syracuseStep 11181995 = 16772993) B16772993
theorem B7454663 : Blo 1961435 7454663 := bstep (se 1 (by rfl) ⟨5590997, by rfl⟩ : syracuseStep 7454663 = 11181995) B11181995
theorem B4969775 : Blo 1961435 4969775 := bstep (se 1 (by rfl) ⟨3727331, by rfl⟩ : syracuseStep 4969775 = 7454663) B7454663
theorem B3313183 : Blo 1961435 3313183 := bstep (se 1 (by rfl) ⟨2484887, by rfl⟩ : syracuseStep 3313183 = 4969775) B4969775
theorem B4417577 : Blo 1961435 4417577 := bstep (se 2 (by rfl) ⟨1656591, by rfl⟩ : syracuseStep 4417577 = 3313183) B3313183
theorem B2945051 : Blo 1961435 2945051 := bstep (se 1 (by rfl) ⟨2208788, by rfl⟩ : syracuseStep 2945051 = 4417577) B4417577
theorem B1963367 : Blo 1961435 1963367 := bstep (se 1 (by rfl) ⟨1472525, by rfl⟩ : syracuseStep 1963367 = 2945051) B2945051
theorem B2208793 : Blo 1961435 2208793 := bbase (se 2 (by rfl) ⟨828297, by rfl⟩ : syracuseStep 2208793 = 1656595) (by norm_num)
theorem B2945057 : Blo 1961435 2945057 := bstep (se 2 (by rfl) ⟨1104396, by rfl⟩ : syracuseStep 2945057 = 2208793) B2208793
theorem B1963371 : Blo 1961435 1963371 := bstep (se 1 (by rfl) ⟨1472528, by rfl⟩ : syracuseStep 1963371 = 2945057) B2945057
theorem B7454693 : Blo 1961435 7454693 := bbase (se 4 (by rfl) ⟨698877, by rfl⟩ : syracuseStep 7454693 = 1397755) (by norm_num)
theorem B4969795 : Blo 1961435 4969795 := bstep (se 1 (by rfl) ⟨3727346, by rfl⟩ : syracuseStep 4969795 = 7454693) B7454693
theorem B6626393 : Blo 1961435 6626393 := bstep (se 2 (by rfl) ⟨2484897, by rfl⟩ : syracuseStep 6626393 = 4969795) B4969795
theorem B4417595 : Blo 1961435 4417595 := bstep (se 1 (by rfl) ⟨3313196, by rfl⟩ : syracuseStep 4417595 = 6626393) B6626393
theorem B2945063 : Blo 1961435 2945063 := bstep (se 1 (by rfl) ⟨2208797, by rfl⟩ : syracuseStep 2945063 = 4417595) B4417595
theorem B1963375 : Blo 1961435 1963375 := bstep (se 1 (by rfl) ⟨1472531, by rfl⟩ : syracuseStep 1963375 = 2945063) B2945063
theorem B2945069 : Blo 1961435 2945069 := bbase (se 3 (by rfl) ⟨552200, by rfl⟩ : syracuseStep 2945069 = 1104401) (by norm_num)
theorem B1963379 : Blo 1961435 1963379 := bstep (se 1 (by rfl) ⟨1472534, by rfl⟩ : syracuseStep 1963379 = 2945069) B2945069
theorem B4417613 : Blo 1961435 4417613 := bbase (se 3 (by rfl) ⟨828302, by rfl⟩ : syracuseStep 4417613 = 1656605) (by norm_num)
theorem B2945075 : Blo 1961435 2945075 := bstep (se 1 (by rfl) ⟨2208806, by rfl⟩ : syracuseStep 2945075 = 4417613) B4417613
theorem B1963383 : Blo 1961435 1963383 := bstep (se 1 (by rfl) ⟨1472537, by rfl⟩ : syracuseStep 1963383 = 2945075) B2945075
theorem B2484913 : Blo 1961435 2484913 := bbase (se 2 (by rfl) ⟨931842, by rfl⟩ : syracuseStep 2484913 = 1863685) (by norm_num)
theorem B3313217 : Blo 1961435 3313217 := bstep (se 2 (by rfl) ⟨1242456, by rfl⟩ : syracuseStep 3313217 = 2484913) B2484913
theorem B2208811 : Blo 1961435 2208811 := bstep (se 1 (by rfl) ⟨1656608, by rfl⟩ : syracuseStep 2208811 = 3313217) B3313217
theorem B2945081 : Blo 1961435 2945081 := bstep (se 2 (by rfl) ⟨1104405, by rfl⟩ : syracuseStep 2945081 = 2208811) B2208811
theorem B1963387 : Blo 1961435 1963387 := bstep (se 1 (by rfl) ⟨1472540, by rfl⟩ : syracuseStep 1963387 = 2945081) B2945081
theorem B2653573 : Blo 1961435 2653573 := bbase (se 4 (by rfl) ⟨248772, by rfl⟩ : syracuseStep 2653573 = 497545) (by norm_num)
theorem B3538097 : Blo 1961435 3538097 := bstep (se 2 (by rfl) ⟨1326786, by rfl⟩ : syracuseStep 3538097 = 2653573) B2653573
theorem B2358731 : Blo 1961435 2358731 := bstep (se 1 (by rfl) ⟨1769048, by rfl⟩ : syracuseStep 2358731 = 3538097) B3538097
theorem B6289949 : Blo 1961435 6289949 := bstep (se 3 (by rfl) ⟨1179365, by rfl⟩ : syracuseStep 6289949 = 2358731) B2358731
theorem B4193299 : Blo 1961435 4193299 := bstep (se 1 (by rfl) ⟨3144974, by rfl⟩ : syracuseStep 4193299 = 6289949) B6289949
theorem B22364261 : Blo 1961435 22364261 := bstep (se 4 (by rfl) ⟨2096649, by rfl⟩ : syracuseStep 22364261 = 4193299) B4193299
theorem B14909507 : Blo 1961435 14909507 := bstep (se 1 (by rfl) ⟨11182130, by rfl⟩ : syracuseStep 14909507 = 22364261) B22364261
theorem B9939671 : Blo 1961435 9939671 := bstep (se 1 (by rfl) ⟨7454753, by rfl⟩ : syracuseStep 9939671 = 14909507) B14909507
theorem B6626447 : Blo 1961435 6626447 := bstep (se 1 (by rfl) ⟨4969835, by rfl⟩ : syracuseStep 6626447 = 9939671) B9939671
theorem B4417631 : Blo 1961435 4417631 := bstep (se 1 (by rfl) ⟨3313223, by rfl⟩ : syracuseStep 4417631 = 6626447) B6626447
theorem B2945087 : Blo 1961435 2945087 := bstep (se 1 (by rfl) ⟨2208815, by rfl⟩ : syracuseStep 2945087 = 4417631) B4417631
theorem B1963391 : Blo 1961435 1963391 := bstep (se 1 (by rfl) ⟨1472543, by rfl⟩ : syracuseStep 1963391 = 2945087) B2945087
theorem B2945093 : Blo 1961435 2945093 := bbase (se 4 (by rfl) ⟨276102, by rfl⟩ : syracuseStep 2945093 = 552205) (by norm_num)
theorem B1963395 : Blo 1961435 1963395 := bstep (se 1 (by rfl) ⟨1472546, by rfl⟩ : syracuseStep 1963395 = 2945093) B2945093
theorem B3313237 : Blo 1961435 3313237 := bbase (se 8 (by rfl) ⟨19413, by rfl⟩ : syracuseStep 3313237 = 38827) (by norm_num)
theorem B4417649 : Blo 1961435 4417649 := bstep (se 2 (by rfl) ⟨1656618, by rfl⟩ : syracuseStep 4417649 = 3313237) B3313237
theorem B2945099 : Blo 1961435 2945099 := bstep (se 1 (by rfl) ⟨2208824, by rfl⟩ : syracuseStep 2945099 = 4417649) B4417649
theorem B1963399 : Blo 1961435 1963399 := bstep (se 1 (by rfl) ⟨1472549, by rfl⟩ : syracuseStep 1963399 = 2945099) B2945099
theorem B2208829 : Blo 1961435 2208829 := bbase (se 3 (by rfl) ⟨414155, by rfl⟩ : syracuseStep 2208829 = 828311) (by norm_num)
theorem B2945105 : Blo 1961435 2945105 := bstep (se 2 (by rfl) ⟨1104414, by rfl⟩ : syracuseStep 2945105 = 2208829) B2208829
theorem B1963403 : Blo 1961435 1963403 := bstep (se 1 (by rfl) ⟨1472552, by rfl⟩ : syracuseStep 1963403 = 2945105) B2945105
theorem B6626501 : Blo 1961435 6626501 := bbase (se 4 (by rfl) ⟨621234, by rfl⟩ : syracuseStep 6626501 = 1242469) (by norm_num)
theorem B4417667 : Blo 1961435 4417667 := bstep (se 1 (by rfl) ⟨3313250, by rfl⟩ : syracuseStep 4417667 = 6626501) B6626501
theorem B2945111 : Blo 1961435 2945111 := bstep (se 1 (by rfl) ⟨2208833, by rfl⟩ : syracuseStep 2945111 = 4417667) B4417667
theorem B1963407 : Blo 1961435 1963407 := bstep (se 1 (by rfl) ⟨1472555, by rfl⟩ : syracuseStep 1963407 = 2945111) B2945111
theorem B2945117 : Blo 1961435 2945117 := bbase (se 3 (by rfl) ⟨552209, by rfl⟩ : syracuseStep 2945117 = 1104419) (by norm_num)
theorem B1963411 : Blo 1961435 1963411 := bstep (se 1 (by rfl) ⟨1472558, by rfl⟩ : syracuseStep 1963411 = 2945117) B2945117
theorem B4417685 : Blo 1961435 4417685 := bbase (se 6 (by rfl) ⟨103539, by rfl⟩ : syracuseStep 4417685 = 207079) (by norm_num)
theorem B2945123 : Blo 1961435 2945123 := bstep (se 1 (by rfl) ⟨2208842, by rfl⟩ : syracuseStep 2945123 = 4417685) B4417685
theorem B1963415 : Blo 1961435 1963415 := bstep (se 1 (by rfl) ⟨1472561, by rfl⟩ : syracuseStep 1963415 = 2945123) B2945123
theorem B2795573 : Blo 1961435 2795573 := bbase (se 5 (by rfl) ⟨131042, by rfl⟩ : syracuseStep 2795573 = 262085) (by norm_num)
theorem B7454861 : Blo 1961435 7454861 := bstep (se 3 (by rfl) ⟨1397786, by rfl⟩ : syracuseStep 7454861 = 2795573) B2795573
theorem B4969907 : Blo 1961435 4969907 := bstep (se 1 (by rfl) ⟨3727430, by rfl⟩ : syracuseStep 4969907 = 7454861) B7454861
theorem B3313271 : Blo 1961435 3313271 := bstep (se 1 (by rfl) ⟨2484953, by rfl⟩ : syracuseStep 3313271 = 4969907) B4969907
theorem B2208847 : Blo 1961435 2208847 := bstep (se 1 (by rfl) ⟨1656635, by rfl⟩ : syracuseStep 2208847 = 3313271) B3313271
theorem B2945129 : Blo 1961435 2945129 := bstep (se 2 (by rfl) ⟨1104423, by rfl⟩ : syracuseStep 2945129 = 2208847) B2208847
theorem B1963419 : Blo 1961435 1963419 := bstep (se 1 (by rfl) ⟨1472564, by rfl⟩ : syracuseStep 1963419 = 2945129) B2945129
theorem B26867861 : Blo 1961435 26867861 := bbase (se 6 (by rfl) ⟨629715, by rfl⟩ : syracuseStep 26867861 = 1259431) (by norm_num)
theorem B17911907 : Blo 1961435 17911907 := bstep (se 1 (by rfl) ⟨13433930, by rfl⟩ : syracuseStep 17911907 = 26867861) B26867861
theorem B11941271 : Blo 1961435 11941271 := bstep (se 1 (by rfl) ⟨8955953, by rfl⟩ : syracuseStep 11941271 = 17911907) B17911907
theorem B7960847 : Blo 1961435 7960847 := bstep (se 1 (by rfl) ⟨5970635, by rfl⟩ : syracuseStep 7960847 = 11941271) B11941271
theorem B21228925 : Blo 1961435 21228925 := bstep (se 3 (by rfl) ⟨3980423, by rfl⟩ : syracuseStep 21228925 = 7960847) B7960847
theorem B28305233 : Blo 1961435 28305233 := bstep (se 2 (by rfl) ⟨10614462, by rfl⟩ : syracuseStep 28305233 = 21228925) B21228925
theorem B18870155 : Blo 1961435 18870155 := bstep (se 1 (by rfl) ⟨14152616, by rfl⟩ : syracuseStep 18870155 = 28305233) B28305233
theorem B12580103 : Blo 1961435 12580103 := bstep (se 1 (by rfl) ⟨9435077, by rfl⟩ : syracuseStep 12580103 = 18870155) B18870155
theorem B8386735 : Blo 1961435 8386735 := bstep (se 1 (by rfl) ⟨6290051, by rfl⟩ : syracuseStep 8386735 = 12580103) B12580103
theorem B11182313 : Blo 1961435 11182313 := bstep (se 2 (by rfl) ⟨4193367, by rfl⟩ : syracuseStep 11182313 = 8386735) B8386735
theorem B7454875 : Blo 1961435 7454875 := bstep (se 1 (by rfl) ⟨5591156, by rfl⟩ : syracuseStep 7454875 = 11182313) B11182313
theorem B9939833 : Blo 1961435 9939833 := bstep (se 2 (by rfl) ⟨3727437, by rfl⟩ : syracuseStep 9939833 = 7454875) B7454875
theorem B6626555 : Blo 1961435 6626555 := bstep (se 1 (by rfl) ⟨4969916, by rfl⟩ : syracuseStep 6626555 = 9939833) B9939833
theorem B4417703 : Blo 1961435 4417703 := bstep (se 1 (by rfl) ⟨3313277, by rfl⟩ : syracuseStep 4417703 = 6626555) B6626555
theorem B2945135 : Blo 1961435 2945135 := bstep (se 1 (by rfl) ⟨2208851, by rfl⟩ : syracuseStep 2945135 = 4417703) B4417703
theorem B1963423 : Blo 1961435 1963423 := bstep (se 1 (by rfl) ⟨1472567, by rfl⟩ : syracuseStep 1963423 = 2945135) B2945135
theorem B2945141 : Blo 1961435 2945141 := bbase (se 5 (by rfl) ⟨138053, by rfl⟩ : syracuseStep 2945141 = 276107) (by norm_num)
theorem B1963427 : Blo 1961435 1963427 := bstep (se 1 (by rfl) ⟨1472570, by rfl⟩ : syracuseStep 1963427 = 2945141) B2945141
theorem B3727453 : Blo 1961435 3727453 := bbase (se 3 (by rfl) ⟨698897, by rfl⟩ : syracuseStep 3727453 = 1397795) (by norm_num)
theorem B4969937 : Blo 1961435 4969937 := bstep (se 2 (by rfl) ⟨1863726, by rfl⟩ : syracuseStep 4969937 = 3727453) B3727453
theorem B3313291 : Blo 1961435 3313291 := bstep (se 1 (by rfl) ⟨2484968, by rfl⟩ : syracuseStep 3313291 = 4969937) B4969937
theorem B4417721 : Blo 1961435 4417721 := bstep (se 2 (by rfl) ⟨1656645, by rfl⟩ : syracuseStep 4417721 = 3313291) B3313291
theorem B2945147 : Blo 1961435 2945147 := bstep (se 1 (by rfl) ⟨2208860, by rfl⟩ : syracuseStep 2945147 = 4417721) B4417721
theorem B1963431 : Blo 1961435 1963431 := bstep (se 1 (by rfl) ⟨1472573, by rfl⟩ : syracuseStep 1963431 = 2945147) B2945147
theorem B2208865 : Blo 1961435 2208865 := bbase (se 2 (by rfl) ⟨828324, by rfl⟩ : syracuseStep 2208865 = 1656649) (by norm_num)
theorem B2945153 : Blo 1961435 2945153 := bstep (se 2 (by rfl) ⟨1104432, by rfl⟩ : syracuseStep 2945153 = 2208865) B2208865
theorem B1963435 : Blo 1961435 1963435 := bstep (se 1 (by rfl) ⟨1472576, by rfl⟩ : syracuseStep 1963435 = 2945153) B2945153
theorem C0 (j : ℕ) (h1 : 490358 ≤ j) (h2 : j ≤ 490858) : Blo 1961435 (4 * j + 3) := by
  interval_cases j
  · exact B1961435
  · exact B1961439
  · exact B1961443
  · exact B1961447
  · exact B1961451
  · exact B1961455
  · exact B1961459
  · exact B1961463
  · exact B1961467
  · exact B1961471
  · exact B1961475
  · exact B1961479
  · exact B1961483
  · exact B1961487
  · exact B1961491
  · exact B1961495
  · exact B1961499
  · exact B1961503
  · exact B1961507
  · exact B1961511
  · exact B1961515
  · exact B1961519
  · exact B1961523
  · exact B1961527
  · exact B1961531
  · exact B1961535
  · exact B1961539
  · exact B1961543
  · exact B1961547
  · exact B1961551
  · exact B1961555
  · exact B1961559
  · exact B1961563
  · exact B1961567
  · exact B1961571
  · exact B1961575
  · exact B1961579
  · exact B1961583
  · exact B1961587
  · exact B1961591
  · exact B1961595
  · exact B1961599
  · exact B1961603
  · exact B1961607
  · exact B1961611
  · exact B1961615
  · exact B1961619
  · exact B1961623
  · exact B1961627
  · exact B1961631
  · exact B1961635
  · exact B1961639
  · exact B1961643
  · exact B1961647
  · exact B1961651
  · exact B1961655
  · exact B1961659
  · exact B1961663
  · exact B1961667
  · exact B1961671
  · exact B1961675
  · exact B1961679
  · exact B1961683
  · exact B1961687
  · exact B1961691
  · exact B1961695
  · exact B1961699
  · exact B1961703
  · exact B1961707
  · exact B1961711
  · exact B1961715
  · exact B1961719
  · exact B1961723
  · exact B1961727
  · exact B1961731
  · exact B1961735
  · exact B1961739
  · exact B1961743
  · exact B1961747
  · exact B1961751
  · exact B1961755
  · exact B1961759
  · exact B1961763
  · exact B1961767
  · exact B1961771
  · exact B1961775
  · exact B1961779
  · exact B1961783
  · exact B1961787
  · exact B1961791
  · exact B1961795
  · exact B1961799
  · exact B1961803
  · exact B1961807
  · exact B1961811
  · exact B1961815
  · exact B1961819
  · exact B1961823
  · exact B1961827
  · exact B1961831
  · exact B1961835
  · exact B1961839
  · exact B1961843
  · exact B1961847
  · exact B1961851
  · exact B1961855
  · exact B1961859
  · exact B1961863
  · exact B1961867
  · exact B1961871
  · exact B1961875
  · exact B1961879
  · exact B1961883
  · exact B1961887
  · exact B1961891
  · exact B1961895
  · exact B1961899
  · exact B1961903
  · exact B1961907
  · exact B1961911
  · exact B1961915
  · exact B1961919
  · exact B1961923
  · exact B1961927
  · exact B1961931
  · exact B1961935
  · exact B1961939
  · exact B1961943
  · exact B1961947
  · exact B1961951
  · exact B1961955
  · exact B1961959
  · exact B1961963
  · exact B1961967
  · exact B1961971
  · exact B1961975
  · exact B1961979
  · exact B1961983
  · exact B1961987
  · exact B1961991
  · exact B1961995
  · exact B1961999
  · exact B1962003
  · exact B1962007
  · exact B1962011
  · exact B1962015
  · exact B1962019
  · exact B1962023
  · exact B1962027
  · exact B1962031
  · exact B1962035
  · exact B1962039
  · exact B1962043
  · exact B1962047
  · exact B1962051
  · exact B1962055
  · exact B1962059
  · exact B1962063
  · exact B1962067
  · exact B1962071
  · exact B1962075
  · exact B1962079
  · exact B1962083
  · exact B1962087
  · exact B1962091
  · exact B1962095
  · exact B1962099
  · exact B1962103
  · exact B1962107
  · exact B1962111
  · exact B1962115
  · exact B1962119
  · exact B1962123
  · exact B1962127
  · exact B1962131
  · exact B1962135
  · exact B1962139
  · exact B1962143
  · exact B1962147
  · exact B1962151
  · exact B1962155
  · exact B1962159
  · exact B1962163
  · exact B1962167
  · exact B1962171
  · exact B1962175
  · exact B1962179
  · exact B1962183
  · exact B1962187
  · exact B1962191
  · exact B1962195
  · exact B1962199
  · exact B1962203
  · exact B1962207
  · exact B1962211
  · exact B1962215
  · exact B1962219
  · exact B1962223
  · exact B1962227
  · exact B1962231
  · exact B1962235
  · exact B1962239
  · exact B1962243
  · exact B1962247
  · exact B1962251
  · exact B1962255
  · exact B1962259
  · exact B1962263
  · exact B1962267
  · exact B1962271
  · exact B1962275
  · exact B1962279
  · exact B1962283
  · exact B1962287
  · exact B1962291
  · exact B1962295
  · exact B1962299
  · exact B1962303
  · exact B1962307
  · exact B1962311
  · exact B1962315
  · exact B1962319
  · exact B1962323
  · exact B1962327
  · exact B1962331
  · exact B1962335
  · exact B1962339
  · exact B1962343
  · exact B1962347
  · exact B1962351
  · exact B1962355
  · exact B1962359
  · exact B1962363
  · exact B1962367
  · exact B1962371
  · exact B1962375
  · exact B1962379
  · exact B1962383
  · exact B1962387
  · exact B1962391
  · exact B1962395
  · exact B1962399
  · exact B1962403
  · exact B1962407
  · exact B1962411
  · exact B1962415
  · exact B1962419
  · exact B1962423
  · exact B1962427
  · exact B1962431
  · exact B1962435
  · exact B1962439
  · exact B1962443
  · exact B1962447
  · exact B1962451
  · exact B1962455
  · exact B1962459
  · exact B1962463
  · exact B1962467
  · exact B1962471
  · exact B1962475
  · exact B1962479
  · exact B1962483
  · exact B1962487
  · exact B1962491
  · exact B1962495
  · exact B1962499
  · exact B1962503
  · exact B1962507
  · exact B1962511
  · exact B1962515
  · exact B1962519
  · exact B1962523
  · exact B1962527
  · exact B1962531
  · exact B1962535
  · exact B1962539
  · exact B1962543
  · exact B1962547
  · exact B1962551
  · exact B1962555
  · exact B1962559
  · exact B1962563
  · exact B1962567
  · exact B1962571
  · exact B1962575
  · exact B1962579
  · exact B1962583
  · exact B1962587
  · exact B1962591
  · exact B1962595
  · exact B1962599
  · exact B1962603
  · exact B1962607
  · exact B1962611
  · exact B1962615
  · exact B1962619
  · exact B1962623
  · exact B1962627
  · exact B1962631
  · exact B1962635
  · exact B1962639
  · exact B1962643
  · exact B1962647
  · exact B1962651
  · exact B1962655
  · exact B1962659
  · exact B1962663
  · exact B1962667
  · exact B1962671
  · exact B1962675
  · exact B1962679
  · exact B1962683
  · exact B1962687
  · exact B1962691
  · exact B1962695
  · exact B1962699
  · exact B1962703
  · exact B1962707
  · exact B1962711
  · exact B1962715
  · exact B1962719
  · exact B1962723
  · exact B1962727
  · exact B1962731
  · exact B1962735
  · exact B1962739
  · exact B1962743
  · exact B1962747
  · exact B1962751
  · exact B1962755
  · exact B1962759
  · exact B1962763
  · exact B1962767
  · exact B1962771
  · exact B1962775
  · exact B1962779
  · exact B1962783
  · exact B1962787
  · exact B1962791
  · exact B1962795
  · exact B1962799
  · exact B1962803
  · exact B1962807
  · exact B1962811
  · exact B1962815
  · exact B1962819
  · exact B1962823
  · exact B1962827
  · exact B1962831
  · exact B1962835
  · exact B1962839
  · exact B1962843
  · exact B1962847
  · exact B1962851
  · exact B1962855
  · exact B1962859
  · exact B1962863
  · exact B1962867
  · exact B1962871
  · exact B1962875
  · exact B1962879
  · exact B1962883
  · exact B1962887
  · exact B1962891
  · exact B1962895
  · exact B1962899
  · exact B1962903
  · exact B1962907
  · exact B1962911
  · exact B1962915
  · exact B1962919
  · exact B1962923
  · exact B1962927
  · exact B1962931
  · exact B1962935
  · exact B1962939
  · exact B1962943
  · exact B1962947
  · exact B1962951
  · exact B1962955
  · exact B1962959
  · exact B1962963
  · exact B1962967
  · exact B1962971
  · exact B1962975
  · exact B1962979
  · exact B1962983
  · exact B1962987
  · exact B1962991
  · exact B1962995
  · exact B1962999
  · exact B1963003
  · exact B1963007
  · exact B1963011
  · exact B1963015
  · exact B1963019
  · exact B1963023
  · exact B1963027
  · exact B1963031
  · exact B1963035
  · exact B1963039
  · exact B1963043
  · exact B1963047
  · exact B1963051
  · exact B1963055
  · exact B1963059
  · exact B1963063
  · exact B1963067
  · exact B1963071
  · exact B1963075
  · exact B1963079
  · exact B1963083
  · exact B1963087
  · exact B1963091
  · exact B1963095
  · exact B1963099
  · exact B1963103
  · exact B1963107
  · exact B1963111
  · exact B1963115
  · exact B1963119
  · exact B1963123
  · exact B1963127
  · exact B1963131
  · exact B1963135
  · exact B1963139
  · exact B1963143
  · exact B1963147
  · exact B1963151
  · exact B1963155
  · exact B1963159
  · exact B1963163
  · exact B1963167
  · exact B1963171
  · exact B1963175
  · exact B1963179
  · exact B1963183
  · exact B1963187
  · exact B1963191
  · exact B1963195
  · exact B1963199
  · exact B1963203
  · exact B1963207
  · exact B1963211
  · exact B1963215
  · exact B1963219
  · exact B1963223
  · exact B1963227
  · exact B1963231
  · exact B1963235
  · exact B1963239
  · exact B1963243
  · exact B1963247
  · exact B1963251
  · exact B1963255
  · exact B1963259
  · exact B1963263
  · exact B1963267
  · exact B1963271
  · exact B1963275
  · exact B1963279
  · exact B1963283
  · exact B1963287
  · exact B1963291
  · exact B1963295
  · exact B1963299
  · exact B1963303
  · exact B1963307
  · exact B1963311
  · exact B1963315
  · exact B1963319
  · exact B1963323
  · exact B1963327
  · exact B1963331
  · exact B1963335
  · exact B1963339
  · exact B1963343
  · exact B1963347
  · exact B1963351
  · exact B1963355
  · exact B1963359
  · exact B1963363
  · exact B1963367
  · exact B1963371
  · exact B1963375
  · exact B1963379
  · exact B1963383
  · exact B1963387
  · exact B1963391
  · exact B1963395
  · exact B1963399
  · exact B1963403
  · exact B1963407
  · exact B1963411
  · exact B1963415
  · exact B1963419
  · exact B1963423
  · exact B1963427
  · exact B1963431
  · exact B1963435
theorem solution (m : ℕ) (hlo : 1961435 ≤ m) (hhi : m ≤ 1963435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 490358 ≤ j := by omega
    have hj2 : j ≤ 490858 := by omega
    have hb : Blo 1961435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
