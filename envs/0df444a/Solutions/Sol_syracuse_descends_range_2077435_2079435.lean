-- Prove2me | solution 1 for syracuse_descends_range_2077435_2079435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:16:12.434874+00:00
-- url     : https://prove2.me/submissions/7756b0a7-676c-4067-9afc-200129c37318

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

theorem B4436869 : Blo 2077435 4436869 := bbase (se 4 (by rfl) ⟨415956, by rfl⟩ : syracuseStep 4436869 = 831913) (by norm_num)
theorem B5915825 : Blo 2077435 5915825 := bstep (se 2 (by rfl) ⟨2218434, by rfl⟩ : syracuseStep 5915825 = 4436869) B4436869
theorem B3943883 : Blo 2077435 3943883 := bstep (se 1 (by rfl) ⟨2957912, by rfl⟩ : syracuseStep 3943883 = 5915825) B5915825
theorem B2629255 : Blo 2077435 2629255 := bstep (se 1 (by rfl) ⟨1971941, by rfl⟩ : syracuseStep 2629255 = 3943883) B3943883
theorem B3505673 : Blo 2077435 3505673 := bstep (se 2 (by rfl) ⟨1314627, by rfl⟩ : syracuseStep 3505673 = 2629255) B2629255
theorem B2337115 : Blo 2077435 2337115 := bstep (se 1 (by rfl) ⟨1752836, by rfl⟩ : syracuseStep 2337115 = 3505673) B3505673
theorem B3116153 : Blo 2077435 3116153 := bstep (se 2 (by rfl) ⟨1168557, by rfl⟩ : syracuseStep 3116153 = 2337115) B2337115
theorem B2077435 : Blo 2077435 2077435 := bstep (se 1 (by rfl) ⟨1558076, by rfl⟩ : syracuseStep 2077435 = 3116153) B3116153
theorem B14214037 : Blo 2077435 14214037 := bbase (se 6 (by rfl) ⟨333141, by rfl⟩ : syracuseStep 14214037 = 666283) (by norm_num)
theorem B18952049 : Blo 2077435 18952049 := bstep (se 2 (by rfl) ⟨7107018, by rfl⟩ : syracuseStep 18952049 = 14214037) B14214037
theorem B12634699 : Blo 2077435 12634699 := bstep (se 1 (by rfl) ⟨9476024, by rfl⟩ : syracuseStep 12634699 = 18952049) B18952049
theorem B16846265 : Blo 2077435 16846265 := bstep (se 2 (by rfl) ⟨6317349, by rfl⟩ : syracuseStep 16846265 = 12634699) B12634699
theorem B44923373 : Blo 2077435 44923373 := bstep (se 3 (by rfl) ⟨8423132, by rfl⟩ : syracuseStep 44923373 = 16846265) B16846265
theorem B29948915 : Blo 2077435 29948915 := bstep (se 1 (by rfl) ⟨22461686, by rfl⟩ : syracuseStep 29948915 = 44923373) B44923373
theorem B19965943 : Blo 2077435 19965943 := bstep (se 1 (by rfl) ⟨14974457, by rfl⟩ : syracuseStep 19965943 = 29948915) B29948915
theorem B26621257 : Blo 2077435 26621257 := bstep (se 2 (by rfl) ⟨9982971, by rfl⟩ : syracuseStep 26621257 = 19965943) B19965943
theorem B35495009 : Blo 2077435 35495009 := bstep (se 2 (by rfl) ⟨13310628, by rfl⟩ : syracuseStep 35495009 = 26621257) B26621257
theorem B23663339 : Blo 2077435 23663339 := bstep (se 1 (by rfl) ⟨17747504, by rfl⟩ : syracuseStep 23663339 = 35495009) B35495009
theorem B15775559 : Blo 2077435 15775559 := bstep (se 1 (by rfl) ⟨11831669, by rfl⟩ : syracuseStep 15775559 = 23663339) B23663339
theorem B10517039 : Blo 2077435 10517039 := bstep (se 1 (by rfl) ⟨7887779, by rfl⟩ : syracuseStep 10517039 = 15775559) B15775559
theorem B7011359 : Blo 2077435 7011359 := bstep (se 1 (by rfl) ⟨5258519, by rfl⟩ : syracuseStep 7011359 = 10517039) B10517039
theorem B4674239 : Blo 2077435 4674239 := bstep (se 1 (by rfl) ⟨3505679, by rfl⟩ : syracuseStep 4674239 = 7011359) B7011359
theorem B3116159 : Blo 2077435 3116159 := bstep (se 1 (by rfl) ⟨2337119, by rfl⟩ : syracuseStep 3116159 = 4674239) B4674239
theorem B2077439 : Blo 2077435 2077439 := bstep (se 1 (by rfl) ⟨1558079, by rfl⟩ : syracuseStep 2077439 = 3116159) B3116159
theorem B3116165 : Blo 2077435 3116165 := bbase (se 4 (by rfl) ⟨292140, by rfl⟩ : syracuseStep 3116165 = 584281) (by norm_num)
theorem B2077443 : Blo 2077435 2077443 := bstep (se 1 (by rfl) ⟨1558082, by rfl⟩ : syracuseStep 2077443 = 3116165) B3116165
theorem B3505693 : Blo 2077435 3505693 := bbase (se 3 (by rfl) ⟨657317, by rfl⟩ : syracuseStep 3505693 = 1314635) (by norm_num)
theorem B4674257 : Blo 2077435 4674257 := bstep (se 2 (by rfl) ⟨1752846, by rfl⟩ : syracuseStep 4674257 = 3505693) B3505693
theorem B3116171 : Blo 2077435 3116171 := bstep (se 1 (by rfl) ⟨2337128, by rfl⟩ : syracuseStep 3116171 = 4674257) B4674257
theorem B2077447 : Blo 2077435 2077447 := bstep (se 1 (by rfl) ⟨1558085, by rfl⟩ : syracuseStep 2077447 = 3116171) B3116171
theorem B2337133 : Blo 2077435 2337133 := bbase (se 3 (by rfl) ⟨438212, by rfl⟩ : syracuseStep 2337133 = 876425) (by norm_num)
theorem B3116177 : Blo 2077435 3116177 := bstep (se 2 (by rfl) ⟨1168566, by rfl⟩ : syracuseStep 3116177 = 2337133) B2337133
theorem B2077451 : Blo 2077435 2077451 := bstep (se 1 (by rfl) ⟨1558088, by rfl⟩ : syracuseStep 2077451 = 3116177) B3116177
theorem B7011413 : Blo 2077435 7011413 := bbase (se 8 (by rfl) ⟨41082, by rfl⟩ : syracuseStep 7011413 = 82165) (by norm_num)
theorem B4674275 : Blo 2077435 4674275 := bstep (se 1 (by rfl) ⟨3505706, by rfl⟩ : syracuseStep 4674275 = 7011413) B7011413
theorem B3116183 : Blo 2077435 3116183 := bstep (se 1 (by rfl) ⟨2337137, by rfl⟩ : syracuseStep 3116183 = 4674275) B4674275
theorem B2077455 : Blo 2077435 2077455 := bstep (se 1 (by rfl) ⟨1558091, by rfl⟩ : syracuseStep 2077455 = 3116183) B3116183
theorem B3116189 : Blo 2077435 3116189 := bbase (se 3 (by rfl) ⟨584285, by rfl⟩ : syracuseStep 3116189 = 1168571) (by norm_num)
theorem B2077459 : Blo 2077435 2077459 := bstep (se 1 (by rfl) ⟨1558094, by rfl⟩ : syracuseStep 2077459 = 3116189) B3116189
theorem B4674293 : Blo 2077435 4674293 := bbase (se 5 (by rfl) ⟨219107, by rfl⟩ : syracuseStep 4674293 = 438215) (by norm_num)
theorem B3116195 : Blo 2077435 3116195 := bstep (se 1 (by rfl) ⟨2337146, by rfl⟩ : syracuseStep 3116195 = 4674293) B4674293
theorem B2077463 : Blo 2077435 2077463 := bstep (se 1 (by rfl) ⟨1558097, by rfl⟩ : syracuseStep 2077463 = 3116195) B3116195
theorem B2495777 : Blo 2077435 2495777 := bbase (se 2 (by rfl) ⟨935916, by rfl⟩ : syracuseStep 2495777 = 1871833) (by norm_num)
theorem B26621621 : Blo 2077435 26621621 := bstep (se 5 (by rfl) ⟨1247888, by rfl⟩ : syracuseStep 26621621 = 2495777) B2495777
theorem B17747747 : Blo 2077435 17747747 := bstep (se 1 (by rfl) ⟨13310810, by rfl⟩ : syracuseStep 17747747 = 26621621) B26621621
theorem B11831831 : Blo 2077435 11831831 := bstep (se 1 (by rfl) ⟨8873873, by rfl⟩ : syracuseStep 11831831 = 17747747) B17747747
theorem B7887887 : Blo 2077435 7887887 := bstep (se 1 (by rfl) ⟨5915915, by rfl⟩ : syracuseStep 7887887 = 11831831) B11831831
theorem B5258591 : Blo 2077435 5258591 := bstep (se 1 (by rfl) ⟨3943943, by rfl⟩ : syracuseStep 5258591 = 7887887) B7887887
theorem B3505727 : Blo 2077435 3505727 := bstep (se 1 (by rfl) ⟨2629295, by rfl⟩ : syracuseStep 3505727 = 5258591) B5258591
theorem B2337151 : Blo 2077435 2337151 := bstep (se 1 (by rfl) ⟨1752863, by rfl⟩ : syracuseStep 2337151 = 3505727) B3505727
theorem B3116201 : Blo 2077435 3116201 := bstep (se 2 (by rfl) ⟨1168575, by rfl⟩ : syracuseStep 3116201 = 2337151) B2337151
theorem B2077467 : Blo 2077435 2077467 := bstep (se 1 (by rfl) ⟨1558100, by rfl⟩ : syracuseStep 2077467 = 3116201) B3116201
theorem B3327709 : Blo 2077435 3327709 := bbase (se 3 (by rfl) ⟨623945, by rfl⟩ : syracuseStep 3327709 = 1247891) (by norm_num)
theorem B4436945 : Blo 2077435 4436945 := bstep (se 2 (by rfl) ⟨1663854, by rfl⟩ : syracuseStep 4436945 = 3327709) B3327709
theorem B2957963 : Blo 2077435 2957963 := bstep (se 1 (by rfl) ⟨2218472, by rfl⟩ : syracuseStep 2957963 = 4436945) B4436945
theorem B7887901 : Blo 2077435 7887901 := bstep (se 3 (by rfl) ⟨1478981, by rfl⟩ : syracuseStep 7887901 = 2957963) B2957963
theorem B10517201 : Blo 2077435 10517201 := bstep (se 2 (by rfl) ⟨3943950, by rfl⟩ : syracuseStep 10517201 = 7887901) B7887901
theorem B7011467 : Blo 2077435 7011467 := bstep (se 1 (by rfl) ⟨5258600, by rfl⟩ : syracuseStep 7011467 = 10517201) B10517201
theorem B4674311 : Blo 2077435 4674311 := bstep (se 1 (by rfl) ⟨3505733, by rfl⟩ : syracuseStep 4674311 = 7011467) B7011467
theorem B3116207 : Blo 2077435 3116207 := bstep (se 1 (by rfl) ⟨2337155, by rfl⟩ : syracuseStep 3116207 = 4674311) B4674311
theorem B2077471 : Blo 2077435 2077471 := bstep (se 1 (by rfl) ⟨1558103, by rfl⟩ : syracuseStep 2077471 = 3116207) B3116207
theorem B3116213 : Blo 2077435 3116213 := bbase (se 5 (by rfl) ⟨146072, by rfl⟩ : syracuseStep 3116213 = 292145) (by norm_num)
theorem B2077475 : Blo 2077435 2077475 := bstep (se 1 (by rfl) ⟨1558106, by rfl⟩ : syracuseStep 2077475 = 3116213) B3116213
theorem B5258621 : Blo 2077435 5258621 := bbase (se 3 (by rfl) ⟨985991, by rfl⟩ : syracuseStep 5258621 = 1971983) (by norm_num)
theorem B3505747 : Blo 2077435 3505747 := bstep (se 1 (by rfl) ⟨2629310, by rfl⟩ : syracuseStep 3505747 = 5258621) B5258621
theorem B4674329 : Blo 2077435 4674329 := bstep (se 2 (by rfl) ⟨1752873, by rfl⟩ : syracuseStep 4674329 = 3505747) B3505747
theorem B3116219 : Blo 2077435 3116219 := bstep (se 1 (by rfl) ⟨2337164, by rfl⟩ : syracuseStep 3116219 = 4674329) B4674329
theorem B2077479 : Blo 2077435 2077479 := bstep (se 1 (by rfl) ⟨1558109, by rfl⟩ : syracuseStep 2077479 = 3116219) B3116219
theorem B2337169 : Blo 2077435 2337169 := bbase (se 2 (by rfl) ⟨876438, by rfl⟩ : syracuseStep 2337169 = 1752877) (by norm_num)
theorem B3116225 : Blo 2077435 3116225 := bstep (se 2 (by rfl) ⟨1168584, by rfl⟩ : syracuseStep 3116225 = 2337169) B2337169
theorem B2077483 : Blo 2077435 2077483 := bstep (se 1 (by rfl) ⟨1558112, by rfl⟩ : syracuseStep 2077483 = 3116225) B3116225
theorem B3943981 : Blo 2077435 3943981 := bbase (se 3 (by rfl) ⟨739496, by rfl⟩ : syracuseStep 3943981 = 1478993) (by norm_num)
theorem B5258641 : Blo 2077435 5258641 := bstep (se 2 (by rfl) ⟨1971990, by rfl⟩ : syracuseStep 5258641 = 3943981) B3943981
theorem B7011521 : Blo 2077435 7011521 := bstep (se 2 (by rfl) ⟨2629320, by rfl⟩ : syracuseStep 7011521 = 5258641) B5258641
theorem B4674347 : Blo 2077435 4674347 := bstep (se 1 (by rfl) ⟨3505760, by rfl⟩ : syracuseStep 4674347 = 7011521) B7011521
theorem B3116231 : Blo 2077435 3116231 := bstep (se 1 (by rfl) ⟨2337173, by rfl⟩ : syracuseStep 3116231 = 4674347) B4674347
theorem B2077487 : Blo 2077435 2077487 := bstep (se 1 (by rfl) ⟨1558115, by rfl⟩ : syracuseStep 2077487 = 3116231) B3116231
theorem B3116237 : Blo 2077435 3116237 := bbase (se 3 (by rfl) ⟨584294, by rfl⟩ : syracuseStep 3116237 = 1168589) (by norm_num)
theorem B2077491 : Blo 2077435 2077491 := bstep (se 1 (by rfl) ⟨1558118, by rfl⟩ : syracuseStep 2077491 = 3116237) B3116237
theorem B4674365 : Blo 2077435 4674365 := bbase (se 3 (by rfl) ⟨876443, by rfl⟩ : syracuseStep 4674365 = 1752887) (by norm_num)
theorem B3116243 : Blo 2077435 3116243 := bstep (se 1 (by rfl) ⟨2337182, by rfl⟩ : syracuseStep 3116243 = 4674365) B4674365
theorem B2077495 : Blo 2077435 2077495 := bstep (se 1 (by rfl) ⟨1558121, by rfl⟩ : syracuseStep 2077495 = 3116243) B3116243
theorem B3505781 : Blo 2077435 3505781 := bbase (se 5 (by rfl) ⟨164333, by rfl⟩ : syracuseStep 3505781 = 328667) (by norm_num)
theorem B2337187 : Blo 2077435 2337187 := bstep (se 1 (by rfl) ⟨1752890, by rfl⟩ : syracuseStep 2337187 = 3505781) B3505781
theorem B3116249 : Blo 2077435 3116249 := bstep (se 2 (by rfl) ⟨1168593, by rfl⟩ : syracuseStep 3116249 = 2337187) B2337187
theorem B2077499 : Blo 2077435 2077499 := bstep (se 1 (by rfl) ⟨1558124, by rfl⟩ : syracuseStep 2077499 = 3116249) B3116249
theorem B4437013 : Blo 2077435 4437013 := bbase (se 6 (by rfl) ⟨103992, by rfl⟩ : syracuseStep 4437013 = 207985) (by norm_num)
theorem B5916017 : Blo 2077435 5916017 := bstep (se 2 (by rfl) ⟨2218506, by rfl⟩ : syracuseStep 5916017 = 4437013) B4437013
theorem B15776045 : Blo 2077435 15776045 := bstep (se 3 (by rfl) ⟨2958008, by rfl⟩ : syracuseStep 15776045 = 5916017) B5916017
theorem B10517363 : Blo 2077435 10517363 := bstep (se 1 (by rfl) ⟨7888022, by rfl⟩ : syracuseStep 10517363 = 15776045) B15776045
theorem B7011575 : Blo 2077435 7011575 := bstep (se 1 (by rfl) ⟨5258681, by rfl⟩ : syracuseStep 7011575 = 10517363) B10517363
theorem B4674383 : Blo 2077435 4674383 := bstep (se 1 (by rfl) ⟨3505787, by rfl⟩ : syracuseStep 4674383 = 7011575) B7011575
theorem B3116255 : Blo 2077435 3116255 := bstep (se 1 (by rfl) ⟨2337191, by rfl⟩ : syracuseStep 3116255 = 4674383) B4674383
theorem B2077503 : Blo 2077435 2077503 := bstep (se 1 (by rfl) ⟨1558127, by rfl⟩ : syracuseStep 2077503 = 3116255) B3116255
theorem B3116261 : Blo 2077435 3116261 := bbase (se 4 (by rfl) ⟨292149, by rfl⟩ : syracuseStep 3116261 = 584299) (by norm_num)
theorem B2077507 : Blo 2077435 2077507 := bstep (se 1 (by rfl) ⟨1558130, by rfl⟩ : syracuseStep 2077507 = 3116261) B3116261
theorem B2105857 : Blo 2077435 2105857 := bbase (se 2 (by rfl) ⟨789696, by rfl⟩ : syracuseStep 2105857 = 1579393) (by norm_num)
theorem B11231237 : Blo 2077435 11231237 := bstep (se 4 (by rfl) ⟨1052928, by rfl⟩ : syracuseStep 11231237 = 2105857) B2105857
theorem B7487491 : Blo 2077435 7487491 := bstep (se 1 (by rfl) ⟨5615618, by rfl⟩ : syracuseStep 7487491 = 11231237) B11231237
theorem B9983321 : Blo 2077435 9983321 := bstep (se 2 (by rfl) ⟨3743745, by rfl⟩ : syracuseStep 9983321 = 7487491) B7487491
theorem B6655547 : Blo 2077435 6655547 := bstep (se 1 (by rfl) ⟨4991660, by rfl⟩ : syracuseStep 6655547 = 9983321) B9983321
theorem B4437031 : Blo 2077435 4437031 := bstep (se 1 (by rfl) ⟨3327773, by rfl⟩ : syracuseStep 4437031 = 6655547) B6655547
theorem B5916041 : Blo 2077435 5916041 := bstep (se 2 (by rfl) ⟨2218515, by rfl⟩ : syracuseStep 5916041 = 4437031) B4437031
theorem B3944027 : Blo 2077435 3944027 := bstep (se 1 (by rfl) ⟨2958020, by rfl⟩ : syracuseStep 3944027 = 5916041) B5916041
theorem B2629351 : Blo 2077435 2629351 := bstep (se 1 (by rfl) ⟨1972013, by rfl⟩ : syracuseStep 2629351 = 3944027) B3944027
theorem B3505801 : Blo 2077435 3505801 := bstep (se 2 (by rfl) ⟨1314675, by rfl⟩ : syracuseStep 3505801 = 2629351) B2629351
theorem B4674401 : Blo 2077435 4674401 := bstep (se 2 (by rfl) ⟨1752900, by rfl⟩ : syracuseStep 4674401 = 3505801) B3505801
theorem B3116267 : Blo 2077435 3116267 := bstep (se 1 (by rfl) ⟨2337200, by rfl⟩ : syracuseStep 3116267 = 4674401) B4674401
theorem B2077511 : Blo 2077435 2077511 := bstep (se 1 (by rfl) ⟨1558133, by rfl⟩ : syracuseStep 2077511 = 3116267) B3116267
theorem B2337205 : Blo 2077435 2337205 := bbase (se 5 (by rfl) ⟨109556, by rfl⟩ : syracuseStep 2337205 = 219113) (by norm_num)
theorem B3116273 : Blo 2077435 3116273 := bstep (se 2 (by rfl) ⟨1168602, by rfl⟩ : syracuseStep 3116273 = 2337205) B2337205
theorem B2077515 : Blo 2077435 2077515 := bstep (se 1 (by rfl) ⟨1558136, by rfl⟩ : syracuseStep 2077515 = 3116273) B3116273
theorem B2629361 : Blo 2077435 2629361 := bbase (se 2 (by rfl) ⟨986010, by rfl⟩ : syracuseStep 2629361 = 1972021) (by norm_num)
theorem B7011629 : Blo 2077435 7011629 := bstep (se 3 (by rfl) ⟨1314680, by rfl⟩ : syracuseStep 7011629 = 2629361) B2629361
theorem B4674419 : Blo 2077435 4674419 := bstep (se 1 (by rfl) ⟨3505814, by rfl⟩ : syracuseStep 4674419 = 7011629) B7011629
theorem B3116279 : Blo 2077435 3116279 := bstep (se 1 (by rfl) ⟨2337209, by rfl⟩ : syracuseStep 3116279 = 4674419) B4674419
theorem B2077519 : Blo 2077435 2077519 := bstep (se 1 (by rfl) ⟨1558139, by rfl⟩ : syracuseStep 2077519 = 3116279) B3116279
theorem B3116285 : Blo 2077435 3116285 := bbase (se 3 (by rfl) ⟨584303, by rfl⟩ : syracuseStep 3116285 = 1168607) (by norm_num)
theorem B2077523 : Blo 2077435 2077523 := bstep (se 1 (by rfl) ⟨1558142, by rfl⟩ : syracuseStep 2077523 = 3116285) B3116285
theorem B4674437 : Blo 2077435 4674437 := bbase (se 4 (by rfl) ⟨438228, by rfl⟩ : syracuseStep 4674437 = 876457) (by norm_num)
theorem B3116291 : Blo 2077435 3116291 := bstep (se 1 (by rfl) ⟨2337218, by rfl⟩ : syracuseStep 3116291 = 4674437) B4674437
theorem B2077527 : Blo 2077435 2077527 := bstep (se 1 (by rfl) ⟨1558145, by rfl⟩ : syracuseStep 2077527 = 3116291) B3116291
theorem B2218537 : Blo 2077435 2218537 := bbase (se 2 (by rfl) ⟨831951, by rfl⟩ : syracuseStep 2218537 = 1663903) (by norm_num)
theorem B2958049 : Blo 2077435 2958049 := bstep (se 2 (by rfl) ⟨1109268, by rfl⟩ : syracuseStep 2958049 = 2218537) B2218537
theorem B3944065 : Blo 2077435 3944065 := bstep (se 2 (by rfl) ⟨1479024, by rfl⟩ : syracuseStep 3944065 = 2958049) B2958049
theorem B5258753 : Blo 2077435 5258753 := bstep (se 2 (by rfl) ⟨1972032, by rfl⟩ : syracuseStep 5258753 = 3944065) B3944065
theorem B3505835 : Blo 2077435 3505835 := bstep (se 1 (by rfl) ⟨2629376, by rfl⟩ : syracuseStep 3505835 = 5258753) B5258753
theorem B2337223 : Blo 2077435 2337223 := bstep (se 1 (by rfl) ⟨1752917, by rfl⟩ : syracuseStep 2337223 = 3505835) B3505835
theorem B3116297 : Blo 2077435 3116297 := bstep (se 2 (by rfl) ⟨1168611, by rfl⟩ : syracuseStep 3116297 = 2337223) B2337223
theorem B2077531 : Blo 2077435 2077531 := bstep (se 1 (by rfl) ⟨1558148, by rfl⟩ : syracuseStep 2077531 = 3116297) B3116297
theorem B10517525 : Blo 2077435 10517525 := bbase (se 6 (by rfl) ⟨246504, by rfl⟩ : syracuseStep 10517525 = 493009) (by norm_num)
theorem B7011683 : Blo 2077435 7011683 := bstep (se 1 (by rfl) ⟨5258762, by rfl⟩ : syracuseStep 7011683 = 10517525) B10517525
theorem B4674455 : Blo 2077435 4674455 := bstep (se 1 (by rfl) ⟨3505841, by rfl⟩ : syracuseStep 4674455 = 7011683) B7011683
theorem B3116303 : Blo 2077435 3116303 := bstep (se 1 (by rfl) ⟨2337227, by rfl⟩ : syracuseStep 3116303 = 4674455) B4674455
theorem B2077535 : Blo 2077435 2077535 := bstep (se 1 (by rfl) ⟨1558151, by rfl⟩ : syracuseStep 2077535 = 3116303) B3116303
theorem B3116309 : Blo 2077435 3116309 := bbase (se 6 (by rfl) ⟨73038, by rfl⟩ : syracuseStep 3116309 = 146077) (by norm_num)
theorem B2077539 : Blo 2077435 2077539 := bstep (se 1 (by rfl) ⟨1558154, by rfl⟩ : syracuseStep 2077539 = 3116309) B3116309
theorem B2134621 : Blo 2077435 2134621 := bbase (se 3 (by rfl) ⟨400241, by rfl⟩ : syracuseStep 2134621 = 800483) (by norm_num)
theorem B2846161 : Blo 2077435 2846161 := bstep (se 2 (by rfl) ⟨1067310, by rfl⟩ : syracuseStep 2846161 = 2134621) B2134621
theorem B3794881 : Blo 2077435 3794881 := bstep (se 2 (by rfl) ⟨1423080, by rfl⟩ : syracuseStep 3794881 = 2846161) B2846161
theorem B5059841 : Blo 2077435 5059841 := bstep (se 2 (by rfl) ⟨1897440, by rfl⟩ : syracuseStep 5059841 = 3794881) B3794881
theorem B13492909 : Blo 2077435 13492909 := bstep (se 3 (by rfl) ⟨2529920, by rfl⟩ : syracuseStep 13492909 = 5059841) B5059841
theorem B17990545 : Blo 2077435 17990545 := bstep (se 2 (by rfl) ⟨6746454, by rfl⟩ : syracuseStep 17990545 = 13492909) B13492909
theorem B23987393 : Blo 2077435 23987393 := bstep (se 2 (by rfl) ⟨8995272, by rfl⟩ : syracuseStep 23987393 = 17990545) B17990545
theorem B15991595 : Blo 2077435 15991595 := bstep (se 1 (by rfl) ⟨11993696, by rfl⟩ : syracuseStep 15991595 = 23987393) B23987393
theorem B10661063 : Blo 2077435 10661063 := bstep (se 1 (by rfl) ⟨7995797, by rfl⟩ : syracuseStep 10661063 = 15991595) B15991595
theorem B28429501 : Blo 2077435 28429501 := bstep (se 3 (by rfl) ⟨5330531, by rfl⟩ : syracuseStep 28429501 = 10661063) B10661063
theorem B37906001 : Blo 2077435 37906001 := bstep (se 2 (by rfl) ⟨14214750, by rfl⟩ : syracuseStep 37906001 = 28429501) B28429501
theorem B25270667 : Blo 2077435 25270667 := bstep (se 1 (by rfl) ⟨18953000, by rfl⟩ : syracuseStep 25270667 = 37906001) B37906001
theorem B16847111 : Blo 2077435 16847111 := bstep (se 1 (by rfl) ⟨12635333, by rfl⟩ : syracuseStep 16847111 = 25270667) B25270667
theorem B11231407 : Blo 2077435 11231407 := bstep (se 1 (by rfl) ⟨8423555, by rfl⟩ : syracuseStep 11231407 = 16847111) B16847111
theorem B14975209 : Blo 2077435 14975209 := bstep (se 2 (by rfl) ⟨5615703, by rfl⟩ : syracuseStep 14975209 = 11231407) B11231407
theorem B19966945 : Blo 2077435 19966945 := bstep (se 2 (by rfl) ⟨7487604, by rfl⟩ : syracuseStep 19966945 = 14975209) B14975209
theorem B26622593 : Blo 2077435 26622593 := bstep (se 2 (by rfl) ⟨9983472, by rfl⟩ : syracuseStep 26622593 = 19966945) B19966945
theorem B17748395 : Blo 2077435 17748395 := bstep (se 1 (by rfl) ⟨13311296, by rfl⟩ : syracuseStep 17748395 = 26622593) B26622593
theorem B11832263 : Blo 2077435 11832263 := bstep (se 1 (by rfl) ⟨8874197, by rfl⟩ : syracuseStep 11832263 = 17748395) B17748395
theorem B7888175 : Blo 2077435 7888175 := bstep (se 1 (by rfl) ⟨5916131, by rfl⟩ : syracuseStep 7888175 = 11832263) B11832263
theorem B5258783 : Blo 2077435 5258783 := bstep (se 1 (by rfl) ⟨3944087, by rfl⟩ : syracuseStep 5258783 = 7888175) B7888175
theorem B3505855 : Blo 2077435 3505855 := bstep (se 1 (by rfl) ⟨2629391, by rfl⟩ : syracuseStep 3505855 = 5258783) B5258783
theorem B4674473 : Blo 2077435 4674473 := bstep (se 2 (by rfl) ⟨1752927, by rfl⟩ : syracuseStep 4674473 = 3505855) B3505855
theorem B3116315 : Blo 2077435 3116315 := bstep (se 1 (by rfl) ⟨2337236, by rfl⟩ : syracuseStep 3116315 = 4674473) B4674473
theorem B2077543 : Blo 2077435 2077543 := bstep (se 1 (by rfl) ⟨1558157, by rfl⟩ : syracuseStep 2077543 = 3116315) B3116315
theorem B2337241 : Blo 2077435 2337241 := bbase (se 2 (by rfl) ⟨876465, by rfl⟩ : syracuseStep 2337241 = 1752931) (by norm_num)
theorem B3116321 : Blo 2077435 3116321 := bstep (se 2 (by rfl) ⟨1168620, by rfl⟩ : syracuseStep 3116321 = 2337241) B2337241
theorem B2077547 : Blo 2077435 2077547 := bstep (se 1 (by rfl) ⟨1558160, by rfl⟩ : syracuseStep 2077547 = 3116321) B3116321
theorem B2958077 : Blo 2077435 2958077 := bbase (se 3 (by rfl) ⟨554639, by rfl⟩ : syracuseStep 2958077 = 1109279) (by norm_num)
theorem B7888205 : Blo 2077435 7888205 := bstep (se 3 (by rfl) ⟨1479038, by rfl⟩ : syracuseStep 7888205 = 2958077) B2958077
theorem B5258803 : Blo 2077435 5258803 := bstep (se 1 (by rfl) ⟨3944102, by rfl⟩ : syracuseStep 5258803 = 7888205) B7888205
theorem B7011737 : Blo 2077435 7011737 := bstep (se 2 (by rfl) ⟨2629401, by rfl⟩ : syracuseStep 7011737 = 5258803) B5258803
theorem B4674491 : Blo 2077435 4674491 := bstep (se 1 (by rfl) ⟨3505868, by rfl⟩ : syracuseStep 4674491 = 7011737) B7011737
theorem B3116327 : Blo 2077435 3116327 := bstep (se 1 (by rfl) ⟨2337245, by rfl⟩ : syracuseStep 3116327 = 4674491) B4674491
theorem B2077551 : Blo 2077435 2077551 := bstep (se 1 (by rfl) ⟨1558163, by rfl⟩ : syracuseStep 2077551 = 3116327) B3116327
theorem B3116333 : Blo 2077435 3116333 := bbase (se 3 (by rfl) ⟨584312, by rfl⟩ : syracuseStep 3116333 = 1168625) (by norm_num)
theorem B2077555 : Blo 2077435 2077555 := bstep (se 1 (by rfl) ⟨1558166, by rfl⟩ : syracuseStep 2077555 = 3116333) B3116333
theorem B4674509 : Blo 2077435 4674509 := bbase (se 3 (by rfl) ⟨876470, by rfl⟩ : syracuseStep 4674509 = 1752941) (by norm_num)
theorem B3116339 : Blo 2077435 3116339 := bstep (se 1 (by rfl) ⟨2337254, by rfl⟩ : syracuseStep 3116339 = 4674509) B4674509
theorem B2077559 : Blo 2077435 2077559 := bstep (se 1 (by rfl) ⟨1558169, by rfl⟩ : syracuseStep 2077559 = 3116339) B3116339
theorem B2629417 : Blo 2077435 2629417 := bbase (se 2 (by rfl) ⟨986031, by rfl⟩ : syracuseStep 2629417 = 1972063) (by norm_num)
theorem B3505889 : Blo 2077435 3505889 := bstep (se 2 (by rfl) ⟨1314708, by rfl⟩ : syracuseStep 3505889 = 2629417) B2629417
theorem B2337259 : Blo 2077435 2337259 := bstep (se 1 (by rfl) ⟨1752944, by rfl⟩ : syracuseStep 2337259 = 3505889) B3505889
theorem B3116345 : Blo 2077435 3116345 := bstep (se 2 (by rfl) ⟨1168629, by rfl⟩ : syracuseStep 3116345 = 2337259) B2337259
theorem B2077563 : Blo 2077435 2077563 := bstep (se 1 (by rfl) ⟨1558172, by rfl⟩ : syracuseStep 2077563 = 3116345) B3116345
theorem B14975381 : Blo 2077435 14975381 := bbase (se 6 (by rfl) ⟨350985, by rfl⟩ : syracuseStep 14975381 = 701971) (by norm_num)
theorem B9983587 : Blo 2077435 9983587 := bstep (se 1 (by rfl) ⟨7487690, by rfl⟩ : syracuseStep 9983587 = 14975381) B14975381
theorem B13311449 : Blo 2077435 13311449 := bstep (se 2 (by rfl) ⟨4991793, by rfl⟩ : syracuseStep 13311449 = 9983587) B9983587
theorem B8874299 : Blo 2077435 8874299 := bstep (se 1 (by rfl) ⟨6655724, by rfl⟩ : syracuseStep 8874299 = 13311449) B13311449
theorem B23664797 : Blo 2077435 23664797 := bstep (se 3 (by rfl) ⟨4437149, by rfl⟩ : syracuseStep 23664797 = 8874299) B8874299
theorem B15776531 : Blo 2077435 15776531 := bstep (se 1 (by rfl) ⟨11832398, by rfl⟩ : syracuseStep 15776531 = 23664797) B23664797
theorem B10517687 : Blo 2077435 10517687 := bstep (se 1 (by rfl) ⟨7888265, by rfl⟩ : syracuseStep 10517687 = 15776531) B15776531
theorem B7011791 : Blo 2077435 7011791 := bstep (se 1 (by rfl) ⟨5258843, by rfl⟩ : syracuseStep 7011791 = 10517687) B10517687
theorem B4674527 : Blo 2077435 4674527 := bstep (se 1 (by rfl) ⟨3505895, by rfl⟩ : syracuseStep 4674527 = 7011791) B7011791
theorem B3116351 : Blo 2077435 3116351 := bstep (se 1 (by rfl) ⟨2337263, by rfl⟩ : syracuseStep 3116351 = 4674527) B4674527
theorem B2077567 : Blo 2077435 2077567 := bstep (se 1 (by rfl) ⟨1558175, by rfl⟩ : syracuseStep 2077567 = 3116351) B3116351
theorem B3116357 : Blo 2077435 3116357 := bbase (se 4 (by rfl) ⟨292158, by rfl⟩ : syracuseStep 3116357 = 584317) (by norm_num)
theorem B2077571 : Blo 2077435 2077571 := bstep (se 1 (by rfl) ⟨1558178, by rfl⟩ : syracuseStep 2077571 = 3116357) B3116357
theorem B3505909 : Blo 2077435 3505909 := bbase (se 5 (by rfl) ⟨164339, by rfl⟩ : syracuseStep 3505909 = 328679) (by norm_num)
theorem B4674545 : Blo 2077435 4674545 := bstep (se 2 (by rfl) ⟨1752954, by rfl⟩ : syracuseStep 4674545 = 3505909) B3505909
theorem B3116363 : Blo 2077435 3116363 := bstep (se 1 (by rfl) ⟨2337272, by rfl⟩ : syracuseStep 3116363 = 4674545) B4674545
theorem B2077575 : Blo 2077435 2077575 := bstep (se 1 (by rfl) ⟨1558181, by rfl⟩ : syracuseStep 2077575 = 3116363) B3116363
theorem B2337277 : Blo 2077435 2337277 := bbase (se 3 (by rfl) ⟨438239, by rfl⟩ : syracuseStep 2337277 = 876479) (by norm_num)
theorem B3116369 : Blo 2077435 3116369 := bstep (se 2 (by rfl) ⟨1168638, by rfl⟩ : syracuseStep 3116369 = 2337277) B2337277
theorem B2077579 : Blo 2077435 2077579 := bstep (se 1 (by rfl) ⟨1558184, by rfl⟩ : syracuseStep 2077579 = 3116369) B3116369
theorem B7011845 : Blo 2077435 7011845 := bbase (se 4 (by rfl) ⟨657360, by rfl⟩ : syracuseStep 7011845 = 1314721) (by norm_num)
theorem B4674563 : Blo 2077435 4674563 := bstep (se 1 (by rfl) ⟨3505922, by rfl⟩ : syracuseStep 4674563 = 7011845) B7011845
theorem B3116375 : Blo 2077435 3116375 := bstep (se 1 (by rfl) ⟨2337281, by rfl⟩ : syracuseStep 3116375 = 4674563) B4674563
theorem B2077583 : Blo 2077435 2077583 := bstep (se 1 (by rfl) ⟨1558187, by rfl⟩ : syracuseStep 2077583 = 3116375) B3116375
theorem B3116381 : Blo 2077435 3116381 := bbase (se 3 (by rfl) ⟨584321, by rfl⟩ : syracuseStep 3116381 = 1168643) (by norm_num)
theorem B2077587 : Blo 2077435 2077587 := bstep (se 1 (by rfl) ⟨1558190, by rfl⟩ : syracuseStep 2077587 = 3116381) B3116381
theorem B4674581 : Blo 2077435 4674581 := bbase (se 6 (by rfl) ⟨109560, by rfl⟩ : syracuseStep 4674581 = 219121) (by norm_num)
theorem B3116387 : Blo 2077435 3116387 := bstep (se 1 (by rfl) ⟨2337290, by rfl⟩ : syracuseStep 3116387 = 4674581) B4674581
theorem B2077591 : Blo 2077435 2077591 := bstep (se 1 (by rfl) ⟨1558193, by rfl⟩ : syracuseStep 2077591 = 3116387) B3116387
theorem B7888373 : Blo 2077435 7888373 := bbase (se 5 (by rfl) ⟨369767, by rfl⟩ : syracuseStep 7888373 = 739535) (by norm_num)
theorem B5258915 : Blo 2077435 5258915 := bstep (se 1 (by rfl) ⟨3944186, by rfl⟩ : syracuseStep 5258915 = 7888373) B7888373
theorem B3505943 : Blo 2077435 3505943 := bstep (se 1 (by rfl) ⟨2629457, by rfl⟩ : syracuseStep 3505943 = 5258915) B5258915
theorem B2337295 : Blo 2077435 2337295 := bstep (se 1 (by rfl) ⟨1752971, by rfl⟩ : syracuseStep 2337295 = 3505943) B3505943
theorem B3116393 : Blo 2077435 3116393 := bstep (se 2 (by rfl) ⟨1168647, by rfl⟩ : syracuseStep 3116393 = 2337295) B2337295
theorem B2077595 : Blo 2077435 2077595 := bstep (se 1 (by rfl) ⟨1558196, by rfl⟩ : syracuseStep 2077595 = 3116393) B3116393
theorem B2218609 : Blo 2077435 2218609 := bbase (se 2 (by rfl) ⟨831978, by rfl⟩ : syracuseStep 2218609 = 1663957) (by norm_num)
theorem B11832581 : Blo 2077435 11832581 := bstep (se 4 (by rfl) ⟨1109304, by rfl⟩ : syracuseStep 11832581 = 2218609) B2218609
theorem B7888387 : Blo 2077435 7888387 := bstep (se 1 (by rfl) ⟨5916290, by rfl⟩ : syracuseStep 7888387 = 11832581) B11832581
theorem B10517849 : Blo 2077435 10517849 := bstep (se 2 (by rfl) ⟨3944193, by rfl⟩ : syracuseStep 10517849 = 7888387) B7888387
theorem B7011899 : Blo 2077435 7011899 := bstep (se 1 (by rfl) ⟨5258924, by rfl⟩ : syracuseStep 7011899 = 10517849) B10517849
theorem B4674599 : Blo 2077435 4674599 := bstep (se 1 (by rfl) ⟨3505949, by rfl⟩ : syracuseStep 4674599 = 7011899) B7011899
theorem B3116399 : Blo 2077435 3116399 := bstep (se 1 (by rfl) ⟨2337299, by rfl⟩ : syracuseStep 3116399 = 4674599) B4674599
theorem B2077599 : Blo 2077435 2077599 := bstep (se 1 (by rfl) ⟨1558199, by rfl⟩ : syracuseStep 2077599 = 3116399) B3116399
theorem B3116405 : Blo 2077435 3116405 := bbase (se 5 (by rfl) ⟨146081, by rfl⟩ : syracuseStep 3116405 = 292163) (by norm_num)
theorem B2077603 : Blo 2077435 2077603 := bstep (se 1 (by rfl) ⟨1558202, by rfl⟩ : syracuseStep 2077603 = 3116405) B3116405
theorem B2958157 : Blo 2077435 2958157 := bbase (se 3 (by rfl) ⟨554654, by rfl⟩ : syracuseStep 2958157 = 1109309) (by norm_num)
theorem B3944209 : Blo 2077435 3944209 := bstep (se 2 (by rfl) ⟨1479078, by rfl⟩ : syracuseStep 3944209 = 2958157) B2958157
theorem B5258945 : Blo 2077435 5258945 := bstep (se 2 (by rfl) ⟨1972104, by rfl⟩ : syracuseStep 5258945 = 3944209) B3944209
theorem B3505963 : Blo 2077435 3505963 := bstep (se 1 (by rfl) ⟨2629472, by rfl⟩ : syracuseStep 3505963 = 5258945) B5258945
theorem B4674617 : Blo 2077435 4674617 := bstep (se 2 (by rfl) ⟨1752981, by rfl⟩ : syracuseStep 4674617 = 3505963) B3505963
theorem B3116411 : Blo 2077435 3116411 := bstep (se 1 (by rfl) ⟨2337308, by rfl⟩ : syracuseStep 3116411 = 4674617) B4674617
theorem B2077607 : Blo 2077435 2077607 := bstep (se 1 (by rfl) ⟨1558205, by rfl⟩ : syracuseStep 2077607 = 3116411) B3116411
theorem B2337313 : Blo 2077435 2337313 := bbase (se 2 (by rfl) ⟨876492, by rfl⟩ : syracuseStep 2337313 = 1752985) (by norm_num)
theorem B3116417 : Blo 2077435 3116417 := bstep (se 2 (by rfl) ⟨1168656, by rfl⟩ : syracuseStep 3116417 = 2337313) B2337313
theorem B2077611 : Blo 2077435 2077611 := bstep (se 1 (by rfl) ⟨1558208, by rfl⟩ : syracuseStep 2077611 = 3116417) B3116417
theorem B5258965 : Blo 2077435 5258965 := bbase (se 7 (by rfl) ⟨61628, by rfl⟩ : syracuseStep 5258965 = 123257) (by norm_num)
theorem B7011953 : Blo 2077435 7011953 := bstep (se 2 (by rfl) ⟨2629482, by rfl⟩ : syracuseStep 7011953 = 5258965) B5258965
theorem B4674635 : Blo 2077435 4674635 := bstep (se 1 (by rfl) ⟨3505976, by rfl⟩ : syracuseStep 4674635 = 7011953) B7011953
theorem B3116423 : Blo 2077435 3116423 := bstep (se 1 (by rfl) ⟨2337317, by rfl⟩ : syracuseStep 3116423 = 4674635) B4674635
theorem B2077615 : Blo 2077435 2077615 := bstep (se 1 (by rfl) ⟨1558211, by rfl⟩ : syracuseStep 2077615 = 3116423) B3116423
theorem B3116429 : Blo 2077435 3116429 := bbase (se 3 (by rfl) ⟨584330, by rfl⟩ : syracuseStep 3116429 = 1168661) (by norm_num)
theorem B2077619 : Blo 2077435 2077619 := bstep (se 1 (by rfl) ⟨1558214, by rfl⟩ : syracuseStep 2077619 = 3116429) B3116429
theorem B4674653 : Blo 2077435 4674653 := bbase (se 3 (by rfl) ⟨876497, by rfl⟩ : syracuseStep 4674653 = 1752995) (by norm_num)
theorem B3116435 : Blo 2077435 3116435 := bstep (se 1 (by rfl) ⟨2337326, by rfl⟩ : syracuseStep 3116435 = 4674653) B4674653
theorem B2077623 : Blo 2077435 2077623 := bstep (se 1 (by rfl) ⟨1558217, by rfl⟩ : syracuseStep 2077623 = 3116435) B3116435
theorem B3505997 : Blo 2077435 3505997 := bbase (se 3 (by rfl) ⟨657374, by rfl⟩ : syracuseStep 3505997 = 1314749) (by norm_num)
theorem B2337331 : Blo 2077435 2337331 := bstep (se 1 (by rfl) ⟨1752998, by rfl⟩ : syracuseStep 2337331 = 3505997) B3505997
theorem B3116441 : Blo 2077435 3116441 := bstep (se 2 (by rfl) ⟨1168665, by rfl⟩ : syracuseStep 3116441 = 2337331) B2337331
theorem B2077627 : Blo 2077435 2077627 := bstep (se 1 (by rfl) ⟨1558220, by rfl⟩ : syracuseStep 2077627 = 3116441) B3116441
theorem B5615941 : Blo 2077435 5615941 := bbase (se 4 (by rfl) ⟨526494, by rfl⟩ : syracuseStep 5615941 = 1052989) (by norm_num)
theorem B7487921 : Blo 2077435 7487921 := bstep (se 2 (by rfl) ⟨2807970, by rfl⟩ : syracuseStep 7487921 = 5615941) B5615941
theorem B19967789 : Blo 2077435 19967789 := bstep (se 3 (by rfl) ⟨3743960, by rfl⟩ : syracuseStep 19967789 = 7487921) B7487921
theorem B13311859 : Blo 2077435 13311859 := bstep (se 1 (by rfl) ⟨9983894, by rfl⟩ : syracuseStep 13311859 = 19967789) B19967789
theorem B17749145 : Blo 2077435 17749145 := bstep (se 2 (by rfl) ⟨6655929, by rfl⟩ : syracuseStep 17749145 = 13311859) B13311859
theorem B11832763 : Blo 2077435 11832763 := bstep (se 1 (by rfl) ⟨8874572, by rfl⟩ : syracuseStep 11832763 = 17749145) B17749145
theorem B15777017 : Blo 2077435 15777017 := bstep (se 2 (by rfl) ⟨5916381, by rfl⟩ : syracuseStep 15777017 = 11832763) B11832763
theorem B10518011 : Blo 2077435 10518011 := bstep (se 1 (by rfl) ⟨7888508, by rfl⟩ : syracuseStep 10518011 = 15777017) B15777017
theorem B7012007 : Blo 2077435 7012007 := bstep (se 1 (by rfl) ⟨5259005, by rfl⟩ : syracuseStep 7012007 = 10518011) B10518011
theorem B4674671 : Blo 2077435 4674671 := bstep (se 1 (by rfl) ⟨3506003, by rfl⟩ : syracuseStep 4674671 = 7012007) B7012007
theorem B3116447 : Blo 2077435 3116447 := bstep (se 1 (by rfl) ⟨2337335, by rfl⟩ : syracuseStep 3116447 = 4674671) B4674671
theorem B2077631 : Blo 2077435 2077631 := bstep (se 1 (by rfl) ⟨1558223, by rfl⟩ : syracuseStep 2077631 = 3116447) B3116447
theorem B3116453 : Blo 2077435 3116453 := bbase (se 4 (by rfl) ⟨292167, by rfl⟩ : syracuseStep 3116453 = 584335) (by norm_num)
theorem B2077635 : Blo 2077435 2077635 := bstep (se 1 (by rfl) ⟨1558226, by rfl⟩ : syracuseStep 2077635 = 3116453) B3116453
theorem B2629513 : Blo 2077435 2629513 := bbase (se 2 (by rfl) ⟨986067, by rfl⟩ : syracuseStep 2629513 = 1972135) (by norm_num)
theorem B3506017 : Blo 2077435 3506017 := bstep (se 2 (by rfl) ⟨1314756, by rfl⟩ : syracuseStep 3506017 = 2629513) B2629513
theorem B4674689 : Blo 2077435 4674689 := bstep (se 2 (by rfl) ⟨1753008, by rfl⟩ : syracuseStep 4674689 = 3506017) B3506017
theorem B3116459 : Blo 2077435 3116459 := bstep (se 1 (by rfl) ⟨2337344, by rfl⟩ : syracuseStep 3116459 = 4674689) B4674689
theorem B2077639 : Blo 2077435 2077639 := bstep (se 1 (by rfl) ⟨1558229, by rfl⟩ : syracuseStep 2077639 = 3116459) B3116459
theorem B2337349 : Blo 2077435 2337349 := bbase (se 4 (by rfl) ⟨219126, by rfl⟩ : syracuseStep 2337349 = 438253) (by norm_num)
theorem B3116465 : Blo 2077435 3116465 := bstep (se 2 (by rfl) ⟨1168674, by rfl⟩ : syracuseStep 3116465 = 2337349) B2337349
theorem B2077643 : Blo 2077435 2077643 := bstep (se 1 (by rfl) ⟨1558232, by rfl⟩ : syracuseStep 2077643 = 3116465) B3116465
theorem B3944285 : Blo 2077435 3944285 := bbase (se 3 (by rfl) ⟨739553, by rfl⟩ : syracuseStep 3944285 = 1479107) (by norm_num)
theorem B2629523 : Blo 2077435 2629523 := bstep (se 1 (by rfl) ⟨1972142, by rfl⟩ : syracuseStep 2629523 = 3944285) B3944285
theorem B7012061 : Blo 2077435 7012061 := bstep (se 3 (by rfl) ⟨1314761, by rfl⟩ : syracuseStep 7012061 = 2629523) B2629523
theorem B4674707 : Blo 2077435 4674707 := bstep (se 1 (by rfl) ⟨3506030, by rfl⟩ : syracuseStep 4674707 = 7012061) B7012061
theorem B3116471 : Blo 2077435 3116471 := bstep (se 1 (by rfl) ⟨2337353, by rfl⟩ : syracuseStep 3116471 = 4674707) B4674707
theorem B2077647 : Blo 2077435 2077647 := bstep (se 1 (by rfl) ⟨1558235, by rfl⟩ : syracuseStep 2077647 = 3116471) B3116471
theorem B3116477 : Blo 2077435 3116477 := bbase (se 3 (by rfl) ⟨584339, by rfl⟩ : syracuseStep 3116477 = 1168679) (by norm_num)
theorem B2077651 : Blo 2077435 2077651 := bstep (se 1 (by rfl) ⟨1558238, by rfl⟩ : syracuseStep 2077651 = 3116477) B3116477
theorem B4674725 : Blo 2077435 4674725 := bbase (se 4 (by rfl) ⟨438255, by rfl⟩ : syracuseStep 4674725 = 876511) (by norm_num)
theorem B3116483 : Blo 2077435 3116483 := bstep (se 1 (by rfl) ⟨2337362, by rfl⟩ : syracuseStep 3116483 = 4674725) B4674725
theorem B2077655 : Blo 2077435 2077655 := bstep (se 1 (by rfl) ⟨1558241, by rfl⟩ : syracuseStep 2077655 = 3116483) B3116483
theorem B5259077 : Blo 2077435 5259077 := bbase (se 4 (by rfl) ⟨493038, by rfl⟩ : syracuseStep 5259077 = 986077) (by norm_num)
theorem B3506051 : Blo 2077435 3506051 := bstep (se 1 (by rfl) ⟨2629538, by rfl⟩ : syracuseStep 3506051 = 5259077) B5259077
theorem B2337367 : Blo 2077435 2337367 := bstep (se 1 (by rfl) ⟨1753025, by rfl⟩ : syracuseStep 2337367 = 3506051) B3506051
theorem B3116489 : Blo 2077435 3116489 := bstep (se 2 (by rfl) ⟨1168683, by rfl⟩ : syracuseStep 3116489 = 2337367) B2337367
theorem B2077659 : Blo 2077435 2077659 := bstep (se 1 (by rfl) ⟨1558244, by rfl⟩ : syracuseStep 2077659 = 3116489) B3116489
theorem B3651533 : Blo 2077435 3651533 := bbase (se 3 (by rfl) ⟨684662, by rfl⟩ : syracuseStep 3651533 = 1369325) (by norm_num)
theorem B2434355 : Blo 2077435 2434355 := bstep (se 1 (by rfl) ⟨1825766, by rfl⟩ : syracuseStep 2434355 = 3651533) B3651533
theorem B25966453 : Blo 2077435 25966453 := bstep (se 5 (by rfl) ⟨1217177, by rfl⟩ : syracuseStep 25966453 = 2434355) B2434355
theorem B34621937 : Blo 2077435 34621937 := bstep (se 2 (by rfl) ⟨12983226, by rfl⟩ : syracuseStep 34621937 = 25966453) B25966453
theorem B23081291 : Blo 2077435 23081291 := bstep (se 1 (by rfl) ⟨17310968, by rfl⟩ : syracuseStep 23081291 = 34621937) B34621937
theorem B15387527 : Blo 2077435 15387527 := bstep (se 1 (by rfl) ⟨11540645, by rfl⟩ : syracuseStep 15387527 = 23081291) B23081291
theorem B41033405 : Blo 2077435 41033405 := bstep (se 3 (by rfl) ⟨7693763, by rfl⟩ : syracuseStep 41033405 = 15387527) B15387527
theorem B109422413 : Blo 2077435 109422413 := bstep (se 3 (by rfl) ⟨20516702, by rfl⟩ : syracuseStep 109422413 = 41033405) B41033405
theorem B72948275 : Blo 2077435 72948275 := bstep (se 1 (by rfl) ⟨54711206, by rfl⟩ : syracuseStep 72948275 = 109422413) B109422413
theorem B48632183 : Blo 2077435 48632183 := bstep (se 1 (by rfl) ⟨36474137, by rfl⟩ : syracuseStep 48632183 = 72948275) B72948275
theorem B32421455 : Blo 2077435 32421455 := bstep (se 1 (by rfl) ⟨24316091, by rfl⟩ : syracuseStep 32421455 = 48632183) B48632183
theorem B21614303 : Blo 2077435 21614303 := bstep (se 1 (by rfl) ⟨16210727, by rfl⟩ : syracuseStep 21614303 = 32421455) B32421455
theorem B14409535 : Blo 2077435 14409535 := bstep (se 1 (by rfl) ⟨10807151, by rfl⟩ : syracuseStep 14409535 = 21614303) B21614303
theorem B19212713 : Blo 2077435 19212713 := bstep (se 2 (by rfl) ⟨7204767, by rfl⟩ : syracuseStep 19212713 = 14409535) B14409535
theorem B12808475 : Blo 2077435 12808475 := bstep (se 1 (by rfl) ⟨9606356, by rfl⟩ : syracuseStep 12808475 = 19212713) B19212713
theorem B8538983 : Blo 2077435 8538983 := bstep (se 1 (by rfl) ⟨6404237, by rfl⟩ : syracuseStep 8538983 = 12808475) B12808475
theorem B5692655 : Blo 2077435 5692655 := bstep (se 1 (by rfl) ⟨4269491, by rfl⟩ : syracuseStep 5692655 = 8538983) B8538983
theorem B3795103 : Blo 2077435 3795103 := bstep (se 1 (by rfl) ⟨2846327, by rfl⟩ : syracuseStep 3795103 = 5692655) B5692655
theorem B20240549 : Blo 2077435 20240549 := bstep (se 4 (by rfl) ⟨1897551, by rfl⟩ : syracuseStep 20240549 = 3795103) B3795103
theorem B13493699 : Blo 2077435 13493699 := bstep (se 1 (by rfl) ⟨10120274, by rfl⟩ : syracuseStep 13493699 = 20240549) B20240549
theorem B8995799 : Blo 2077435 8995799 := bstep (se 1 (by rfl) ⟨6746849, by rfl⟩ : syracuseStep 8995799 = 13493699) B13493699
theorem B5997199 : Blo 2077435 5997199 := bstep (se 1 (by rfl) ⟨4497899, by rfl⟩ : syracuseStep 5997199 = 8995799) B8995799
theorem B7996265 : Blo 2077435 7996265 := bstep (se 2 (by rfl) ⟨2998599, by rfl⟩ : syracuseStep 7996265 = 5997199) B5997199
theorem B5330843 : Blo 2077435 5330843 := bstep (se 1 (by rfl) ⟨3998132, by rfl⟩ : syracuseStep 5330843 = 7996265) B7996265
theorem B3553895 : Blo 2077435 3553895 := bstep (se 1 (by rfl) ⟨2665421, by rfl⟩ : syracuseStep 3553895 = 5330843) B5330843
theorem B2369263 : Blo 2077435 2369263 := bstep (se 1 (by rfl) ⟨1776947, by rfl⟩ : syracuseStep 2369263 = 3553895) B3553895
theorem B3159017 : Blo 2077435 3159017 := bstep (se 2 (by rfl) ⟨1184631, by rfl⟩ : syracuseStep 3159017 = 2369263) B2369263
theorem B2106011 : Blo 2077435 2106011 := bstep (se 1 (by rfl) ⟨1579508, by rfl⟩ : syracuseStep 2106011 = 3159017) B3159017
theorem B5616029 : Blo 2077435 5616029 := bstep (se 3 (by rfl) ⟨1053005, by rfl⟩ : syracuseStep 5616029 = 2106011) B2106011
theorem B3744019 : Blo 2077435 3744019 := bstep (se 1 (by rfl) ⟨2808014, by rfl⟩ : syracuseStep 3744019 = 5616029) B5616029
theorem B4992025 : Blo 2077435 4992025 := bstep (se 2 (by rfl) ⟨1872009, by rfl⟩ : syracuseStep 4992025 = 3744019) B3744019
theorem B6656033 : Blo 2077435 6656033 := bstep (se 2 (by rfl) ⟨2496012, by rfl⟩ : syracuseStep 6656033 = 4992025) B4992025
theorem B4437355 : Blo 2077435 4437355 := bstep (se 1 (by rfl) ⟨3328016, by rfl⟩ : syracuseStep 4437355 = 6656033) B6656033
theorem B5916473 : Blo 2077435 5916473 := bstep (se 2 (by rfl) ⟨2218677, by rfl⟩ : syracuseStep 5916473 = 4437355) B4437355
theorem B3944315 : Blo 2077435 3944315 := bstep (se 1 (by rfl) ⟨2958236, by rfl⟩ : syracuseStep 3944315 = 5916473) B5916473
theorem B10518173 : Blo 2077435 10518173 := bstep (se 3 (by rfl) ⟨1972157, by rfl⟩ : syracuseStep 10518173 = 3944315) B3944315
theorem B7012115 : Blo 2077435 7012115 := bstep (se 1 (by rfl) ⟨5259086, by rfl⟩ : syracuseStep 7012115 = 10518173) B10518173
theorem B4674743 : Blo 2077435 4674743 := bstep (se 1 (by rfl) ⟨3506057, by rfl⟩ : syracuseStep 4674743 = 7012115) B7012115
theorem B3116495 : Blo 2077435 3116495 := bstep (se 1 (by rfl) ⟨2337371, by rfl⟩ : syracuseStep 3116495 = 4674743) B4674743
theorem B2077663 : Blo 2077435 2077663 := bstep (se 1 (by rfl) ⟨1558247, by rfl⟩ : syracuseStep 2077663 = 3116495) B3116495
theorem B3116501 : Blo 2077435 3116501 := bbase (se 7 (by rfl) ⟨36521, by rfl⟩ : syracuseStep 3116501 = 73043) (by norm_num)
theorem B2077667 : Blo 2077435 2077667 := bstep (se 1 (by rfl) ⟨1558250, by rfl⟩ : syracuseStep 2077667 = 3116501) B3116501
theorem B7888661 : Blo 2077435 7888661 := bbase (se 6 (by rfl) ⟨184890, by rfl⟩ : syracuseStep 7888661 = 369781) (by norm_num)
theorem B5259107 : Blo 2077435 5259107 := bstep (se 1 (by rfl) ⟨3944330, by rfl⟩ : syracuseStep 5259107 = 7888661) B7888661
theorem B3506071 : Blo 2077435 3506071 := bstep (se 1 (by rfl) ⟨2629553, by rfl⟩ : syracuseStep 3506071 = 5259107) B5259107
theorem B4674761 : Blo 2077435 4674761 := bstep (se 2 (by rfl) ⟨1753035, by rfl⟩ : syracuseStep 4674761 = 3506071) B3506071
theorem B3116507 : Blo 2077435 3116507 := bstep (se 1 (by rfl) ⟨2337380, by rfl⟩ : syracuseStep 3116507 = 4674761) B4674761
theorem B2077671 : Blo 2077435 2077671 := bstep (se 1 (by rfl) ⟨1558253, by rfl⟩ : syracuseStep 2077671 = 3116507) B3116507
theorem B2337385 : Blo 2077435 2337385 := bbase (se 2 (by rfl) ⟨876519, by rfl⟩ : syracuseStep 2337385 = 1753039) (by norm_num)
theorem B3116513 : Blo 2077435 3116513 := bstep (se 2 (by rfl) ⟨1168692, by rfl⟩ : syracuseStep 3116513 = 2337385) B2337385
theorem B2077675 : Blo 2077435 2077675 := bstep (se 1 (by rfl) ⟨1558256, by rfl⟩ : syracuseStep 2077675 = 3116513) B3116513
theorem B4437389 : Blo 2077435 4437389 := bbase (se 3 (by rfl) ⟨832010, by rfl⟩ : syracuseStep 4437389 = 1664021) (by norm_num)
theorem B11833037 : Blo 2077435 11833037 := bstep (se 3 (by rfl) ⟨2218694, by rfl⟩ : syracuseStep 11833037 = 4437389) B4437389
theorem B7888691 : Blo 2077435 7888691 := bstep (se 1 (by rfl) ⟨5916518, by rfl⟩ : syracuseStep 7888691 = 11833037) B11833037
theorem B5259127 : Blo 2077435 5259127 := bstep (se 1 (by rfl) ⟨3944345, by rfl⟩ : syracuseStep 5259127 = 7888691) B7888691
theorem B7012169 : Blo 2077435 7012169 := bstep (se 2 (by rfl) ⟨2629563, by rfl⟩ : syracuseStep 7012169 = 5259127) B5259127
theorem B4674779 : Blo 2077435 4674779 := bstep (se 1 (by rfl) ⟨3506084, by rfl⟩ : syracuseStep 4674779 = 7012169) B7012169
theorem B3116519 : Blo 2077435 3116519 := bstep (se 1 (by rfl) ⟨2337389, by rfl⟩ : syracuseStep 3116519 = 4674779) B4674779
theorem B2077679 : Blo 2077435 2077679 := bstep (se 1 (by rfl) ⟨1558259, by rfl⟩ : syracuseStep 2077679 = 3116519) B3116519
theorem B3116525 : Blo 2077435 3116525 := bbase (se 3 (by rfl) ⟨584348, by rfl⟩ : syracuseStep 3116525 = 1168697) (by norm_num)
theorem B2077683 : Blo 2077435 2077683 := bstep (se 1 (by rfl) ⟨1558262, by rfl⟩ : syracuseStep 2077683 = 3116525) B3116525
theorem B4674797 : Blo 2077435 4674797 := bbase (se 3 (by rfl) ⟨876524, by rfl⟩ : syracuseStep 4674797 = 1753049) (by norm_num)
theorem B3116531 : Blo 2077435 3116531 := bstep (se 1 (by rfl) ⟨2337398, by rfl⟩ : syracuseStep 3116531 = 4674797) B4674797
theorem B2077687 : Blo 2077435 2077687 := bstep (se 1 (by rfl) ⟨1558265, by rfl⟩ : syracuseStep 2077687 = 3116531) B3116531
theorem B2958277 : Blo 2077435 2958277 := bbase (se 4 (by rfl) ⟨277338, by rfl⟩ : syracuseStep 2958277 = 554677) (by norm_num)
theorem B3944369 : Blo 2077435 3944369 := bstep (se 2 (by rfl) ⟨1479138, by rfl⟩ : syracuseStep 3944369 = 2958277) B2958277
theorem B2629579 : Blo 2077435 2629579 := bstep (se 1 (by rfl) ⟨1972184, by rfl⟩ : syracuseStep 2629579 = 3944369) B3944369
theorem B3506105 : Blo 2077435 3506105 := bstep (se 2 (by rfl) ⟨1314789, by rfl⟩ : syracuseStep 3506105 = 2629579) B2629579
theorem B2337403 : Blo 2077435 2337403 := bstep (se 1 (by rfl) ⟨1753052, by rfl⟩ : syracuseStep 2337403 = 3506105) B3506105
theorem B3116537 : Blo 2077435 3116537 := bstep (se 2 (by rfl) ⟨1168701, by rfl⟩ : syracuseStep 3116537 = 2337403) B2337403
theorem B2077691 : Blo 2077435 2077691 := bstep (se 1 (by rfl) ⟨1558268, by rfl⟩ : syracuseStep 2077691 = 3116537) B3116537
theorem B16848341 : Blo 2077435 16848341 := bbase (se 7 (by rfl) ⟨197441, by rfl⟩ : syracuseStep 16848341 = 394883) (by norm_num)
theorem B11232227 : Blo 2077435 11232227 := bstep (se 1 (by rfl) ⟨8424170, by rfl⟩ : syracuseStep 11232227 = 16848341) B16848341
theorem B29952605 : Blo 2077435 29952605 := bstep (se 3 (by rfl) ⟨5616113, by rfl⟩ : syracuseStep 29952605 = 11232227) B11232227
theorem B79873613 : Blo 2077435 79873613 := bstep (se 3 (by rfl) ⟨14976302, by rfl⟩ : syracuseStep 79873613 = 29952605) B29952605
theorem B53249075 : Blo 2077435 53249075 := bstep (se 1 (by rfl) ⟨39936806, by rfl⟩ : syracuseStep 53249075 = 79873613) B79873613
theorem B35499383 : Blo 2077435 35499383 := bstep (se 1 (by rfl) ⟨26624537, by rfl⟩ : syracuseStep 35499383 = 53249075) B53249075
theorem B23666255 : Blo 2077435 23666255 := bstep (se 1 (by rfl) ⟨17749691, by rfl⟩ : syracuseStep 23666255 = 35499383) B35499383
theorem B15777503 : Blo 2077435 15777503 := bstep (se 1 (by rfl) ⟨11833127, by rfl⟩ : syracuseStep 15777503 = 23666255) B23666255
theorem B10518335 : Blo 2077435 10518335 := bstep (se 1 (by rfl) ⟨7888751, by rfl⟩ : syracuseStep 10518335 = 15777503) B15777503
theorem B7012223 : Blo 2077435 7012223 := bstep (se 1 (by rfl) ⟨5259167, by rfl⟩ : syracuseStep 7012223 = 10518335) B10518335
theorem B4674815 : Blo 2077435 4674815 := bstep (se 1 (by rfl) ⟨3506111, by rfl⟩ : syracuseStep 4674815 = 7012223) B7012223
theorem B3116543 : Blo 2077435 3116543 := bstep (se 1 (by rfl) ⟨2337407, by rfl⟩ : syracuseStep 3116543 = 4674815) B4674815
theorem B2077695 : Blo 2077435 2077695 := bstep (se 1 (by rfl) ⟨1558271, by rfl⟩ : syracuseStep 2077695 = 3116543) B3116543
theorem B3116549 : Blo 2077435 3116549 := bbase (se 4 (by rfl) ⟨292176, by rfl⟩ : syracuseStep 3116549 = 584353) (by norm_num)
theorem B2077699 : Blo 2077435 2077699 := bstep (se 1 (by rfl) ⟨1558274, by rfl⟩ : syracuseStep 2077699 = 3116549) B3116549
theorem B3506125 : Blo 2077435 3506125 := bbase (se 3 (by rfl) ⟨657398, by rfl⟩ : syracuseStep 3506125 = 1314797) (by norm_num)
theorem B4674833 : Blo 2077435 4674833 := bstep (se 2 (by rfl) ⟨1753062, by rfl⟩ : syracuseStep 4674833 = 3506125) B3506125
theorem B3116555 : Blo 2077435 3116555 := bstep (se 1 (by rfl) ⟨2337416, by rfl⟩ : syracuseStep 3116555 = 4674833) B4674833
theorem B2077703 : Blo 2077435 2077703 := bstep (se 1 (by rfl) ⟨1558277, by rfl⟩ : syracuseStep 2077703 = 3116555) B3116555
theorem B2337421 : Blo 2077435 2337421 := bbase (se 3 (by rfl) ⟨438266, by rfl⟩ : syracuseStep 2337421 = 876533) (by norm_num)
theorem B3116561 : Blo 2077435 3116561 := bstep (se 2 (by rfl) ⟨1168710, by rfl⟩ : syracuseStep 3116561 = 2337421) B2337421
theorem B2077707 : Blo 2077435 2077707 := bstep (se 1 (by rfl) ⟨1558280, by rfl⟩ : syracuseStep 2077707 = 3116561) B3116561
theorem B7012277 : Blo 2077435 7012277 := bbase (se 5 (by rfl) ⟨328700, by rfl⟩ : syracuseStep 7012277 = 657401) (by norm_num)
theorem B4674851 : Blo 2077435 4674851 := bstep (se 1 (by rfl) ⟨3506138, by rfl⟩ : syracuseStep 4674851 = 7012277) B7012277
theorem B3116567 : Blo 2077435 3116567 := bstep (se 1 (by rfl) ⟨2337425, by rfl⟩ : syracuseStep 3116567 = 4674851) B4674851
theorem B2077711 : Blo 2077435 2077711 := bstep (se 1 (by rfl) ⟨1558283, by rfl⟩ : syracuseStep 2077711 = 3116567) B3116567
theorem B3116573 : Blo 2077435 3116573 := bbase (se 3 (by rfl) ⟨584357, by rfl⟩ : syracuseStep 3116573 = 1168715) (by norm_num)
theorem B2077715 : Blo 2077435 2077715 := bstep (se 1 (by rfl) ⟨1558286, by rfl⟩ : syracuseStep 2077715 = 3116573) B3116573
theorem B4674869 : Blo 2077435 4674869 := bbase (se 5 (by rfl) ⟨219134, by rfl⟩ : syracuseStep 4674869 = 438269) (by norm_num)
theorem B3116579 : Blo 2077435 3116579 := bstep (se 1 (by rfl) ⟨2337434, by rfl⟩ : syracuseStep 3116579 = 4674869) B4674869
theorem B2077719 : Blo 2077435 2077719 := bstep (se 1 (by rfl) ⟨1558289, by rfl⟩ : syracuseStep 2077719 = 3116579) B3116579
theorem B42647957 : Blo 2077435 42647957 := bbase (se 6 (by rfl) ⟨999561, by rfl⟩ : syracuseStep 42647957 = 1999123) (by norm_num)
theorem B28431971 : Blo 2077435 28431971 := bstep (se 1 (by rfl) ⟨21323978, by rfl⟩ : syracuseStep 28431971 = 42647957) B42647957
theorem B18954647 : Blo 2077435 18954647 := bstep (se 1 (by rfl) ⟨14215985, by rfl⟩ : syracuseStep 18954647 = 28431971) B28431971
theorem B12636431 : Blo 2077435 12636431 := bstep (se 1 (by rfl) ⟨9477323, by rfl⟩ : syracuseStep 12636431 = 18954647) B18954647
theorem B8424287 : Blo 2077435 8424287 := bstep (se 1 (by rfl) ⟨6318215, by rfl⟩ : syracuseStep 8424287 = 12636431) B12636431
theorem B5616191 : Blo 2077435 5616191 := bstep (se 1 (by rfl) ⟨4212143, by rfl⟩ : syracuseStep 5616191 = 8424287) B8424287
theorem B3744127 : Blo 2077435 3744127 := bstep (se 1 (by rfl) ⟨2808095, by rfl⟩ : syracuseStep 3744127 = 5616191) B5616191
theorem B19968677 : Blo 2077435 19968677 := bstep (se 4 (by rfl) ⟨1872063, by rfl⟩ : syracuseStep 19968677 = 3744127) B3744127
theorem B13312451 : Blo 2077435 13312451 := bstep (se 1 (by rfl) ⟨9984338, by rfl⟩ : syracuseStep 13312451 = 19968677) B19968677
theorem B8874967 : Blo 2077435 8874967 := bstep (se 1 (by rfl) ⟨6656225, by rfl⟩ : syracuseStep 8874967 = 13312451) B13312451
theorem B11833289 : Blo 2077435 11833289 := bstep (se 2 (by rfl) ⟨4437483, by rfl⟩ : syracuseStep 11833289 = 8874967) B8874967
theorem B7888859 : Blo 2077435 7888859 := bstep (se 1 (by rfl) ⟨5916644, by rfl⟩ : syracuseStep 7888859 = 11833289) B11833289
theorem B5259239 : Blo 2077435 5259239 := bstep (se 1 (by rfl) ⟨3944429, by rfl⟩ : syracuseStep 5259239 = 7888859) B7888859
theorem B3506159 : Blo 2077435 3506159 := bstep (se 1 (by rfl) ⟨2629619, by rfl⟩ : syracuseStep 3506159 = 5259239) B5259239
theorem B2337439 : Blo 2077435 2337439 := bstep (se 1 (by rfl) ⟨1753079, by rfl⟩ : syracuseStep 2337439 = 3506159) B3506159
theorem B3116585 : Blo 2077435 3116585 := bstep (se 2 (by rfl) ⟨1168719, by rfl⟩ : syracuseStep 3116585 = 2337439) B2337439
theorem B2077723 : Blo 2077435 2077723 := bstep (se 1 (by rfl) ⟨1558292, by rfl⟩ : syracuseStep 2077723 = 3116585) B3116585
theorem B5331005 : Blo 2077435 5331005 := bbase (se 3 (by rfl) ⟨999563, by rfl⟩ : syracuseStep 5331005 = 1999127) (by norm_num)
theorem B3554003 : Blo 2077435 3554003 := bstep (se 1 (by rfl) ⟨2665502, by rfl⟩ : syracuseStep 3554003 = 5331005) B5331005
theorem B2369335 : Blo 2077435 2369335 := bstep (se 1 (by rfl) ⟨1777001, by rfl⟩ : syracuseStep 2369335 = 3554003) B3554003
theorem B3159113 : Blo 2077435 3159113 := bstep (se 2 (by rfl) ⟨1184667, by rfl⟩ : syracuseStep 3159113 = 2369335) B2369335
theorem B33697205 : Blo 2077435 33697205 := bstep (se 5 (by rfl) ⟨1579556, by rfl⟩ : syracuseStep 33697205 = 3159113) B3159113
theorem B22464803 : Blo 2077435 22464803 := bstep (se 1 (by rfl) ⟨16848602, by rfl⟩ : syracuseStep 22464803 = 33697205) B33697205
theorem B14976535 : Blo 2077435 14976535 := bstep (se 1 (by rfl) ⟨11232401, by rfl⟩ : syracuseStep 14976535 = 22464803) B22464803
theorem B19968713 : Blo 2077435 19968713 := bstep (se 2 (by rfl) ⟨7488267, by rfl⟩ : syracuseStep 19968713 = 14976535) B14976535
theorem B13312475 : Blo 2077435 13312475 := bstep (se 1 (by rfl) ⟨9984356, by rfl⟩ : syracuseStep 13312475 = 19968713) B19968713
theorem B8874983 : Blo 2077435 8874983 := bstep (se 1 (by rfl) ⟨6656237, by rfl⟩ : syracuseStep 8874983 = 13312475) B13312475
theorem B5916655 : Blo 2077435 5916655 := bstep (se 1 (by rfl) ⟨4437491, by rfl⟩ : syracuseStep 5916655 = 8874983) B8874983
theorem B7888873 : Blo 2077435 7888873 := bstep (se 2 (by rfl) ⟨2958327, by rfl⟩ : syracuseStep 7888873 = 5916655) B5916655
theorem B10518497 : Blo 2077435 10518497 := bstep (se 2 (by rfl) ⟨3944436, by rfl⟩ : syracuseStep 10518497 = 7888873) B7888873
theorem B7012331 : Blo 2077435 7012331 := bstep (se 1 (by rfl) ⟨5259248, by rfl⟩ : syracuseStep 7012331 = 10518497) B10518497
theorem B4674887 : Blo 2077435 4674887 := bstep (se 1 (by rfl) ⟨3506165, by rfl⟩ : syracuseStep 4674887 = 7012331) B7012331
theorem B3116591 : Blo 2077435 3116591 := bstep (se 1 (by rfl) ⟨2337443, by rfl⟩ : syracuseStep 3116591 = 4674887) B4674887
theorem B2077727 : Blo 2077435 2077727 := bstep (se 1 (by rfl) ⟨1558295, by rfl⟩ : syracuseStep 2077727 = 3116591) B3116591
theorem B3116597 : Blo 2077435 3116597 := bbase (se 5 (by rfl) ⟨146090, by rfl⟩ : syracuseStep 3116597 = 292181) (by norm_num)
theorem B2077731 : Blo 2077435 2077731 := bstep (se 1 (by rfl) ⟨1558298, by rfl⟩ : syracuseStep 2077731 = 3116597) B3116597
theorem B5259269 : Blo 2077435 5259269 := bbase (se 4 (by rfl) ⟨493056, by rfl⟩ : syracuseStep 5259269 = 986113) (by norm_num)
theorem B3506179 : Blo 2077435 3506179 := bstep (se 1 (by rfl) ⟨2629634, by rfl⟩ : syracuseStep 3506179 = 5259269) B5259269
theorem B4674905 : Blo 2077435 4674905 := bstep (se 2 (by rfl) ⟨1753089, by rfl⟩ : syracuseStep 4674905 = 3506179) B3506179
theorem B3116603 : Blo 2077435 3116603 := bstep (se 1 (by rfl) ⟨2337452, by rfl⟩ : syracuseStep 3116603 = 4674905) B4674905
theorem B2077735 : Blo 2077435 2077735 := bstep (se 1 (by rfl) ⟨1558301, by rfl⟩ : syracuseStep 2077735 = 3116603) B3116603
theorem B2337457 : Blo 2077435 2337457 := bbase (se 2 (by rfl) ⟨876546, by rfl⟩ : syracuseStep 2337457 = 1753093) (by norm_num)
theorem B3116609 : Blo 2077435 3116609 := bstep (se 2 (by rfl) ⟨1168728, by rfl⟩ : syracuseStep 3116609 = 2337457) B2337457
theorem B2077739 : Blo 2077435 2077739 := bstep (se 1 (by rfl) ⟨1558304, by rfl⟩ : syracuseStep 2077739 = 3116609) B3116609
theorem B2496109 : Blo 2077435 2496109 := bbase (se 3 (by rfl) ⟨468020, by rfl⟩ : syracuseStep 2496109 = 936041) (by norm_num)
theorem B3328145 : Blo 2077435 3328145 := bstep (se 2 (by rfl) ⟨1248054, by rfl⟩ : syracuseStep 3328145 = 2496109) B2496109
theorem B2218763 : Blo 2077435 2218763 := bstep (se 1 (by rfl) ⟨1664072, by rfl⟩ : syracuseStep 2218763 = 3328145) B3328145
theorem B5916701 : Blo 2077435 5916701 := bstep (se 3 (by rfl) ⟨1109381, by rfl⟩ : syracuseStep 5916701 = 2218763) B2218763
theorem B3944467 : Blo 2077435 3944467 := bstep (se 1 (by rfl) ⟨2958350, by rfl⟩ : syracuseStep 3944467 = 5916701) B5916701
theorem B5259289 : Blo 2077435 5259289 := bstep (se 2 (by rfl) ⟨1972233, by rfl⟩ : syracuseStep 5259289 = 3944467) B3944467
theorem B7012385 : Blo 2077435 7012385 := bstep (se 2 (by rfl) ⟨2629644, by rfl⟩ : syracuseStep 7012385 = 5259289) B5259289
theorem B4674923 : Blo 2077435 4674923 := bstep (se 1 (by rfl) ⟨3506192, by rfl⟩ : syracuseStep 4674923 = 7012385) B7012385
theorem B3116615 : Blo 2077435 3116615 := bstep (se 1 (by rfl) ⟨2337461, by rfl⟩ : syracuseStep 3116615 = 4674923) B4674923
theorem B2077743 : Blo 2077435 2077743 := bstep (se 1 (by rfl) ⟨1558307, by rfl⟩ : syracuseStep 2077743 = 3116615) B3116615
theorem B3116621 : Blo 2077435 3116621 := bbase (se 3 (by rfl) ⟨584366, by rfl⟩ : syracuseStep 3116621 = 1168733) (by norm_num)
theorem B2077747 : Blo 2077435 2077747 := bstep (se 1 (by rfl) ⟨1558310, by rfl⟩ : syracuseStep 2077747 = 3116621) B3116621
theorem B4674941 : Blo 2077435 4674941 := bbase (se 3 (by rfl) ⟨876551, by rfl⟩ : syracuseStep 4674941 = 1753103) (by norm_num)
theorem B3116627 : Blo 2077435 3116627 := bstep (se 1 (by rfl) ⟨2337470, by rfl⟩ : syracuseStep 3116627 = 4674941) B4674941
theorem B2077751 : Blo 2077435 2077751 := bstep (se 1 (by rfl) ⟨1558313, by rfl⟩ : syracuseStep 2077751 = 3116627) B3116627
theorem B3506213 : Blo 2077435 3506213 := bbase (se 4 (by rfl) ⟨328707, by rfl⟩ : syracuseStep 3506213 = 657415) (by norm_num)
theorem B2337475 : Blo 2077435 2337475 := bstep (se 1 (by rfl) ⟨1753106, by rfl⟩ : syracuseStep 2337475 = 3506213) B3506213
theorem B3116633 : Blo 2077435 3116633 := bstep (se 2 (by rfl) ⟨1168737, by rfl⟩ : syracuseStep 3116633 = 2337475) B2337475
theorem B2077755 : Blo 2077435 2077755 := bstep (se 1 (by rfl) ⟨1558316, by rfl⟩ : syracuseStep 2077755 = 3116633) B3116633
theorem B2958373 : Blo 2077435 2958373 := bbase (se 4 (by rfl) ⟨277347, by rfl⟩ : syracuseStep 2958373 = 554695) (by norm_num)
theorem B15777989 : Blo 2077435 15777989 := bstep (se 4 (by rfl) ⟨1479186, by rfl⟩ : syracuseStep 15777989 = 2958373) B2958373
theorem B10518659 : Blo 2077435 10518659 := bstep (se 1 (by rfl) ⟨7888994, by rfl⟩ : syracuseStep 10518659 = 15777989) B15777989
theorem B7012439 : Blo 2077435 7012439 := bstep (se 1 (by rfl) ⟨5259329, by rfl⟩ : syracuseStep 7012439 = 10518659) B10518659
theorem B4674959 : Blo 2077435 4674959 := bstep (se 1 (by rfl) ⟨3506219, by rfl⟩ : syracuseStep 4674959 = 7012439) B7012439
theorem B3116639 : Blo 2077435 3116639 := bstep (se 1 (by rfl) ⟨2337479, by rfl⟩ : syracuseStep 3116639 = 4674959) B4674959
theorem B2077759 : Blo 2077435 2077759 := bstep (se 1 (by rfl) ⟨1558319, by rfl⟩ : syracuseStep 2077759 = 3116639) B3116639
theorem B3116645 : Blo 2077435 3116645 := bbase (se 4 (by rfl) ⟨292185, by rfl⟩ : syracuseStep 3116645 = 584371) (by norm_num)
theorem B2077763 : Blo 2077435 2077763 := bstep (se 1 (by rfl) ⟨1558322, by rfl⟩ : syracuseStep 2077763 = 3116645) B3116645
theorem B2218789 : Blo 2077435 2218789 := bbase (se 4 (by rfl) ⟨208011, by rfl⟩ : syracuseStep 2218789 = 416023) (by norm_num)
theorem B2958385 : Blo 2077435 2958385 := bstep (se 2 (by rfl) ⟨1109394, by rfl⟩ : syracuseStep 2958385 = 2218789) B2218789
theorem B3944513 : Blo 2077435 3944513 := bstep (se 2 (by rfl) ⟨1479192, by rfl⟩ : syracuseStep 3944513 = 2958385) B2958385
theorem B2629675 : Blo 2077435 2629675 := bstep (se 1 (by rfl) ⟨1972256, by rfl⟩ : syracuseStep 2629675 = 3944513) B3944513
theorem B3506233 : Blo 2077435 3506233 := bstep (se 2 (by rfl) ⟨1314837, by rfl⟩ : syracuseStep 3506233 = 2629675) B2629675
theorem B4674977 : Blo 2077435 4674977 := bstep (se 2 (by rfl) ⟨1753116, by rfl⟩ : syracuseStep 4674977 = 3506233) B3506233
theorem B3116651 : Blo 2077435 3116651 := bstep (se 1 (by rfl) ⟨2337488, by rfl⟩ : syracuseStep 3116651 = 4674977) B4674977
theorem B2077767 : Blo 2077435 2077767 := bstep (se 1 (by rfl) ⟨1558325, by rfl⟩ : syracuseStep 2077767 = 3116651) B3116651
theorem B2337493 : Blo 2077435 2337493 := bbase (se 7 (by rfl) ⟨27392, by rfl⟩ : syracuseStep 2337493 = 54785) (by norm_num)
theorem B3116657 : Blo 2077435 3116657 := bstep (se 2 (by rfl) ⟨1168746, by rfl⟩ : syracuseStep 3116657 = 2337493) B2337493
theorem B2077771 : Blo 2077435 2077771 := bstep (se 1 (by rfl) ⟨1558328, by rfl⟩ : syracuseStep 2077771 = 3116657) B3116657
theorem B2629685 : Blo 2077435 2629685 := bbase (se 5 (by rfl) ⟨123266, by rfl⟩ : syracuseStep 2629685 = 246533) (by norm_num)
theorem B7012493 : Blo 2077435 7012493 := bstep (se 3 (by rfl) ⟨1314842, by rfl⟩ : syracuseStep 7012493 = 2629685) B2629685
theorem B4674995 : Blo 2077435 4674995 := bstep (se 1 (by rfl) ⟨3506246, by rfl⟩ : syracuseStep 4674995 = 7012493) B7012493
theorem B3116663 : Blo 2077435 3116663 := bstep (se 1 (by rfl) ⟨2337497, by rfl⟩ : syracuseStep 3116663 = 4674995) B4674995
theorem B2077775 : Blo 2077435 2077775 := bstep (se 1 (by rfl) ⟨1558331, by rfl⟩ : syracuseStep 2077775 = 3116663) B3116663
theorem B3116669 : Blo 2077435 3116669 := bbase (se 3 (by rfl) ⟨584375, by rfl⟩ : syracuseStep 3116669 = 1168751) (by norm_num)
theorem B2077779 : Blo 2077435 2077779 := bstep (se 1 (by rfl) ⟨1558334, by rfl⟩ : syracuseStep 2077779 = 3116669) B3116669
theorem B4675013 : Blo 2077435 4675013 := bbase (se 4 (by rfl) ⟨438282, by rfl⟩ : syracuseStep 4675013 = 876565) (by norm_num)
theorem B3116675 : Blo 2077435 3116675 := bstep (se 1 (by rfl) ⟨2337506, by rfl⟩ : syracuseStep 3116675 = 4675013) B4675013
theorem B2077783 : Blo 2077435 2077783 := bstep (se 1 (by rfl) ⟨1558337, by rfl⟩ : syracuseStep 2077783 = 3116675) B3116675
theorem B3159205 : Blo 2077435 3159205 := bbase (se 4 (by rfl) ⟨296175, by rfl⟩ : syracuseStep 3159205 = 592351) (by norm_num)
theorem B16849093 : Blo 2077435 16849093 := bstep (se 4 (by rfl) ⟨1579602, by rfl⟩ : syracuseStep 16849093 = 3159205) B3159205
theorem B22465457 : Blo 2077435 22465457 := bstep (se 2 (by rfl) ⟨8424546, by rfl⟩ : syracuseStep 22465457 = 16849093) B16849093
theorem B14976971 : Blo 2077435 14976971 := bstep (se 1 (by rfl) ⟨11232728, by rfl⟩ : syracuseStep 14976971 = 22465457) B22465457
theorem B9984647 : Blo 2077435 9984647 := bstep (se 1 (by rfl) ⟨7488485, by rfl⟩ : syracuseStep 9984647 = 14976971) B14976971
theorem B6656431 : Blo 2077435 6656431 := bstep (se 1 (by rfl) ⟨4992323, by rfl⟩ : syracuseStep 6656431 = 9984647) B9984647
theorem B8875241 : Blo 2077435 8875241 := bstep (se 2 (by rfl) ⟨3328215, by rfl⟩ : syracuseStep 8875241 = 6656431) B6656431
theorem B5916827 : Blo 2077435 5916827 := bstep (se 1 (by rfl) ⟨4437620, by rfl⟩ : syracuseStep 5916827 = 8875241) B8875241
theorem B3944551 : Blo 2077435 3944551 := bstep (se 1 (by rfl) ⟨2958413, by rfl⟩ : syracuseStep 3944551 = 5916827) B5916827
theorem B5259401 : Blo 2077435 5259401 := bstep (se 2 (by rfl) ⟨1972275, by rfl⟩ : syracuseStep 5259401 = 3944551) B3944551
theorem B3506267 : Blo 2077435 3506267 := bstep (se 1 (by rfl) ⟨2629700, by rfl⟩ : syracuseStep 3506267 = 5259401) B5259401
theorem B2337511 : Blo 2077435 2337511 := bstep (se 1 (by rfl) ⟨1753133, by rfl⟩ : syracuseStep 2337511 = 3506267) B3506267
theorem B3116681 : Blo 2077435 3116681 := bstep (se 2 (by rfl) ⟨1168755, by rfl⟩ : syracuseStep 3116681 = 2337511) B2337511
theorem B2077787 : Blo 2077435 2077787 := bstep (se 1 (by rfl) ⟨1558340, by rfl⟩ : syracuseStep 2077787 = 3116681) B3116681
theorem B10518821 : Blo 2077435 10518821 := bbase (se 4 (by rfl) ⟨986139, by rfl⟩ : syracuseStep 10518821 = 1972279) (by norm_num)
theorem B7012547 : Blo 2077435 7012547 := bstep (se 1 (by rfl) ⟨5259410, by rfl⟩ : syracuseStep 7012547 = 10518821) B10518821
theorem B4675031 : Blo 2077435 4675031 := bstep (se 1 (by rfl) ⟨3506273, by rfl⟩ : syracuseStep 4675031 = 7012547) B7012547
theorem B3116687 : Blo 2077435 3116687 := bstep (se 1 (by rfl) ⟨2337515, by rfl⟩ : syracuseStep 3116687 = 4675031) B4675031
theorem B2077791 : Blo 2077435 2077791 := bstep (se 1 (by rfl) ⟨1558343, by rfl⟩ : syracuseStep 2077791 = 3116687) B3116687
theorem B3116693 : Blo 2077435 3116693 := bbase (se 6 (by rfl) ⟨73047, by rfl⟩ : syracuseStep 3116693 = 146095) (by norm_num)
theorem B2077795 : Blo 2077435 2077795 := bstep (se 1 (by rfl) ⟨1558346, by rfl⟩ : syracuseStep 2077795 = 3116693) B3116693
theorem B3795349 : Blo 2077435 3795349 := bbase (se 6 (by rfl) ⟨88953, by rfl⟩ : syracuseStep 3795349 = 177907) (by norm_num)
theorem B5060465 : Blo 2077435 5060465 := bstep (se 2 (by rfl) ⟨1897674, by rfl⟩ : syracuseStep 5060465 = 3795349) B3795349
theorem B3373643 : Blo 2077435 3373643 := bstep (se 1 (by rfl) ⟨2530232, by rfl⟩ : syracuseStep 3373643 = 5060465) B5060465
theorem B8996381 : Blo 2077435 8996381 := bstep (se 3 (by rfl) ⟨1686821, by rfl⟩ : syracuseStep 8996381 = 3373643) B3373643
theorem B5997587 : Blo 2077435 5997587 := bstep (se 1 (by rfl) ⟨4498190, by rfl⟩ : syracuseStep 5997587 = 8996381) B8996381
theorem B63974261 : Blo 2077435 63974261 := bstep (se 5 (by rfl) ⟨2998793, by rfl⟩ : syracuseStep 63974261 = 5997587) B5997587
theorem B42649507 : Blo 2077435 42649507 := bstep (se 1 (by rfl) ⟨31987130, by rfl⟩ : syracuseStep 42649507 = 63974261) B63974261
theorem B56866009 : Blo 2077435 56866009 := bstep (se 2 (by rfl) ⟨21324753, by rfl⟩ : syracuseStep 56866009 = 42649507) B42649507
theorem B75821345 : Blo 2077435 75821345 := bstep (se 2 (by rfl) ⟨28433004, by rfl⟩ : syracuseStep 75821345 = 56866009) B56866009
theorem B50547563 : Blo 2077435 50547563 := bstep (se 1 (by rfl) ⟨37910672, by rfl⟩ : syracuseStep 50547563 = 75821345) B75821345
theorem B33698375 : Blo 2077435 33698375 := bstep (se 1 (by rfl) ⟨25273781, by rfl⟩ : syracuseStep 33698375 = 50547563) B50547563
theorem B22465583 : Blo 2077435 22465583 := bstep (se 1 (by rfl) ⟨16849187, by rfl⟩ : syracuseStep 22465583 = 33698375) B33698375
theorem B14977055 : Blo 2077435 14977055 := bstep (se 1 (by rfl) ⟨11232791, by rfl⟩ : syracuseStep 14977055 = 22465583) B22465583
theorem B9984703 : Blo 2077435 9984703 := bstep (se 1 (by rfl) ⟨7488527, by rfl⟩ : syracuseStep 9984703 = 14977055) B14977055
theorem B13312937 : Blo 2077435 13312937 := bstep (se 2 (by rfl) ⟨4992351, by rfl⟩ : syracuseStep 13312937 = 9984703) B9984703
theorem B8875291 : Blo 2077435 8875291 := bstep (se 1 (by rfl) ⟨6656468, by rfl⟩ : syracuseStep 8875291 = 13312937) B13312937
theorem B11833721 : Blo 2077435 11833721 := bstep (se 2 (by rfl) ⟨4437645, by rfl⟩ : syracuseStep 11833721 = 8875291) B8875291
theorem B7889147 : Blo 2077435 7889147 := bstep (se 1 (by rfl) ⟨5916860, by rfl⟩ : syracuseStep 7889147 = 11833721) B11833721
theorem B5259431 : Blo 2077435 5259431 := bstep (se 1 (by rfl) ⟨3944573, by rfl⟩ : syracuseStep 5259431 = 7889147) B7889147
theorem B3506287 : Blo 2077435 3506287 := bstep (se 1 (by rfl) ⟨2629715, by rfl⟩ : syracuseStep 3506287 = 5259431) B5259431
theorem B4675049 : Blo 2077435 4675049 := bstep (se 2 (by rfl) ⟨1753143, by rfl⟩ : syracuseStep 4675049 = 3506287) B3506287
theorem B3116699 : Blo 2077435 3116699 := bstep (se 1 (by rfl) ⟨2337524, by rfl⟩ : syracuseStep 3116699 = 4675049) B4675049
theorem B2077799 : Blo 2077435 2077799 := bstep (se 1 (by rfl) ⟨1558349, by rfl⟩ : syracuseStep 2077799 = 3116699) B3116699
theorem B2337529 : Blo 2077435 2337529 := bbase (se 2 (by rfl) ⟨876573, by rfl⟩ : syracuseStep 2337529 = 1753147) (by norm_num)
theorem B3116705 : Blo 2077435 3116705 := bstep (se 2 (by rfl) ⟨1168764, by rfl⟩ : syracuseStep 3116705 = 2337529) B2337529
theorem B2077803 : Blo 2077435 2077803 := bstep (se 1 (by rfl) ⟨1558352, by rfl⟩ : syracuseStep 2077803 = 3116705) B3116705
theorem B2106157 : Blo 2077435 2106157 := bbase (se 3 (by rfl) ⟨394904, by rfl⟩ : syracuseStep 2106157 = 789809) (by norm_num)
theorem B2808209 : Blo 2077435 2808209 := bstep (se 2 (by rfl) ⟨1053078, by rfl⟩ : syracuseStep 2808209 = 2106157) B2106157
theorem B7488557 : Blo 2077435 7488557 := bstep (se 3 (by rfl) ⟨1404104, by rfl⟩ : syracuseStep 7488557 = 2808209) B2808209
theorem B4992371 : Blo 2077435 4992371 := bstep (se 1 (by rfl) ⟨3744278, by rfl⟩ : syracuseStep 4992371 = 7488557) B7488557
theorem B3328247 : Blo 2077435 3328247 := bstep (se 1 (by rfl) ⟨2496185, by rfl⟩ : syracuseStep 3328247 = 4992371) B4992371
theorem B8875325 : Blo 2077435 8875325 := bstep (se 3 (by rfl) ⟨1664123, by rfl⟩ : syracuseStep 8875325 = 3328247) B3328247
theorem B5916883 : Blo 2077435 5916883 := bstep (se 1 (by rfl) ⟨4437662, by rfl⟩ : syracuseStep 5916883 = 8875325) B8875325
theorem B7889177 : Blo 2077435 7889177 := bstep (se 2 (by rfl) ⟨2958441, by rfl⟩ : syracuseStep 7889177 = 5916883) B5916883
theorem B5259451 : Blo 2077435 5259451 := bstep (se 1 (by rfl) ⟨3944588, by rfl⟩ : syracuseStep 5259451 = 7889177) B7889177
theorem B7012601 : Blo 2077435 7012601 := bstep (se 2 (by rfl) ⟨2629725, by rfl⟩ : syracuseStep 7012601 = 5259451) B5259451
theorem B4675067 : Blo 2077435 4675067 := bstep (se 1 (by rfl) ⟨3506300, by rfl⟩ : syracuseStep 4675067 = 7012601) B7012601
theorem B3116711 : Blo 2077435 3116711 := bstep (se 1 (by rfl) ⟨2337533, by rfl⟩ : syracuseStep 3116711 = 4675067) B4675067
theorem B2077807 : Blo 2077435 2077807 := bstep (se 1 (by rfl) ⟨1558355, by rfl⟩ : syracuseStep 2077807 = 3116711) B3116711
theorem B3116717 : Blo 2077435 3116717 := bbase (se 3 (by rfl) ⟨584384, by rfl⟩ : syracuseStep 3116717 = 1168769) (by norm_num)
theorem B2077811 : Blo 2077435 2077811 := bstep (se 1 (by rfl) ⟨1558358, by rfl⟩ : syracuseStep 2077811 = 3116717) B3116717
theorem B4675085 : Blo 2077435 4675085 := bbase (se 3 (by rfl) ⟨876578, by rfl⟩ : syracuseStep 4675085 = 1753157) (by norm_num)
theorem B3116723 : Blo 2077435 3116723 := bstep (se 1 (by rfl) ⟨2337542, by rfl⟩ : syracuseStep 3116723 = 4675085) B4675085
theorem B2077815 : Blo 2077435 2077815 := bstep (se 1 (by rfl) ⟨1558361, by rfl⟩ : syracuseStep 2077815 = 3116723) B3116723
theorem B2629741 : Blo 2077435 2629741 := bbase (se 3 (by rfl) ⟨493076, by rfl⟩ : syracuseStep 2629741 = 986153) (by norm_num)
theorem B3506321 : Blo 2077435 3506321 := bstep (se 2 (by rfl) ⟨1314870, by rfl⟩ : syracuseStep 3506321 = 2629741) B2629741
theorem B2337547 : Blo 2077435 2337547 := bstep (se 1 (by rfl) ⟨1753160, by rfl⟩ : syracuseStep 2337547 = 3506321) B3506321
theorem B3116729 : Blo 2077435 3116729 := bstep (se 2 (by rfl) ⟨1168773, by rfl⟩ : syracuseStep 3116729 = 2337547) B2337547
theorem B2077819 : Blo 2077435 2077819 := bstep (se 1 (by rfl) ⟨1558364, by rfl⟩ : syracuseStep 2077819 = 3116729) B3116729
theorem B7488613 : Blo 2077435 7488613 := bbase (se 4 (by rfl) ⟨702057, by rfl⟩ : syracuseStep 7488613 = 1404115) (by norm_num)
theorem B9984817 : Blo 2077435 9984817 := bstep (se 2 (by rfl) ⟨3744306, by rfl⟩ : syracuseStep 9984817 = 7488613) B7488613
theorem B13313089 : Blo 2077435 13313089 := bstep (se 2 (by rfl) ⟨4992408, by rfl⟩ : syracuseStep 13313089 = 9984817) B9984817
theorem B17750785 : Blo 2077435 17750785 := bstep (se 2 (by rfl) ⟨6656544, by rfl⟩ : syracuseStep 17750785 = 13313089) B13313089
theorem B23667713 : Blo 2077435 23667713 := bstep (se 2 (by rfl) ⟨8875392, by rfl⟩ : syracuseStep 23667713 = 17750785) B17750785
theorem B15778475 : Blo 2077435 15778475 := bstep (se 1 (by rfl) ⟨11833856, by rfl⟩ : syracuseStep 15778475 = 23667713) B23667713
theorem B10518983 : Blo 2077435 10518983 := bstep (se 1 (by rfl) ⟨7889237, by rfl⟩ : syracuseStep 10518983 = 15778475) B15778475
theorem B7012655 : Blo 2077435 7012655 := bstep (se 1 (by rfl) ⟨5259491, by rfl⟩ : syracuseStep 7012655 = 10518983) B10518983
theorem B4675103 : Blo 2077435 4675103 := bstep (se 1 (by rfl) ⟨3506327, by rfl⟩ : syracuseStep 4675103 = 7012655) B7012655
theorem B3116735 : Blo 2077435 3116735 := bstep (se 1 (by rfl) ⟨2337551, by rfl⟩ : syracuseStep 3116735 = 4675103) B4675103
theorem B2077823 : Blo 2077435 2077823 := bstep (se 1 (by rfl) ⟨1558367, by rfl⟩ : syracuseStep 2077823 = 3116735) B3116735
theorem B3116741 : Blo 2077435 3116741 := bbase (se 4 (by rfl) ⟨292194, by rfl⟩ : syracuseStep 3116741 = 584389) (by norm_num)
theorem B2077827 : Blo 2077435 2077827 := bstep (se 1 (by rfl) ⟨1558370, by rfl⟩ : syracuseStep 2077827 = 3116741) B3116741
theorem B3506341 : Blo 2077435 3506341 := bbase (se 4 (by rfl) ⟨328719, by rfl⟩ : syracuseStep 3506341 = 657439) (by norm_num)
theorem B4675121 : Blo 2077435 4675121 := bstep (se 2 (by rfl) ⟨1753170, by rfl⟩ : syracuseStep 4675121 = 3506341) B3506341
theorem B3116747 : Blo 2077435 3116747 := bstep (se 1 (by rfl) ⟨2337560, by rfl⟩ : syracuseStep 3116747 = 4675121) B4675121
theorem B2077831 : Blo 2077435 2077831 := bstep (se 1 (by rfl) ⟨1558373, by rfl⟩ : syracuseStep 2077831 = 3116747) B3116747
theorem B2337565 : Blo 2077435 2337565 := bbase (se 3 (by rfl) ⟨438293, by rfl⟩ : syracuseStep 2337565 = 876587) (by norm_num)
theorem B3116753 : Blo 2077435 3116753 := bstep (se 2 (by rfl) ⟨1168782, by rfl⟩ : syracuseStep 3116753 = 2337565) B2337565
theorem B2077835 : Blo 2077435 2077835 := bstep (se 1 (by rfl) ⟨1558376, by rfl⟩ : syracuseStep 2077835 = 3116753) B3116753
theorem B7012709 : Blo 2077435 7012709 := bbase (se 4 (by rfl) ⟨657441, by rfl⟩ : syracuseStep 7012709 = 1314883) (by norm_num)
theorem B4675139 : Blo 2077435 4675139 := bstep (se 1 (by rfl) ⟨3506354, by rfl⟩ : syracuseStep 4675139 = 7012709) B7012709
theorem B3116759 : Blo 2077435 3116759 := bstep (se 1 (by rfl) ⟨2337569, by rfl⟩ : syracuseStep 3116759 = 4675139) B4675139
theorem B2077839 : Blo 2077435 2077839 := bstep (se 1 (by rfl) ⟨1558379, by rfl⟩ : syracuseStep 2077839 = 3116759) B3116759
theorem B3116765 : Blo 2077435 3116765 := bbase (se 3 (by rfl) ⟨584393, by rfl⟩ : syracuseStep 3116765 = 1168787) (by norm_num)
theorem B2077843 : Blo 2077435 2077843 := bstep (se 1 (by rfl) ⟨1558382, by rfl⟩ : syracuseStep 2077843 = 3116765) B3116765
theorem B4675157 : Blo 2077435 4675157 := bbase (se 8 (by rfl) ⟨27393, by rfl⟩ : syracuseStep 4675157 = 54787) (by norm_num)
theorem B3116771 : Blo 2077435 3116771 := bstep (se 1 (by rfl) ⟨2337578, by rfl⟩ : syracuseStep 3116771 = 4675157) B4675157
theorem B2077847 : Blo 2077435 2077847 := bstep (se 1 (by rfl) ⟨1558385, by rfl⟩ : syracuseStep 2077847 = 3116771) B3116771
theorem B4437757 : Blo 2077435 4437757 := bbase (se 3 (by rfl) ⟨832079, by rfl⟩ : syracuseStep 4437757 = 1664159) (by norm_num)
theorem B5917009 : Blo 2077435 5917009 := bstep (se 2 (by rfl) ⟨2218878, by rfl⟩ : syracuseStep 5917009 = 4437757) B4437757
theorem B7889345 : Blo 2077435 7889345 := bstep (se 2 (by rfl) ⟨2958504, by rfl⟩ : syracuseStep 7889345 = 5917009) B5917009
theorem B5259563 : Blo 2077435 5259563 := bstep (se 1 (by rfl) ⟨3944672, by rfl⟩ : syracuseStep 5259563 = 7889345) B7889345
theorem B3506375 : Blo 2077435 3506375 := bstep (se 1 (by rfl) ⟨2629781, by rfl⟩ : syracuseStep 3506375 = 5259563) B5259563
theorem B2337583 : Blo 2077435 2337583 := bstep (se 1 (by rfl) ⟨1753187, by rfl⟩ : syracuseStep 2337583 = 3506375) B3506375
theorem B3116777 : Blo 2077435 3116777 := bstep (se 2 (by rfl) ⟨1168791, by rfl⟩ : syracuseStep 3116777 = 2337583) B2337583
theorem B2077851 : Blo 2077435 2077851 := bstep (se 1 (by rfl) ⟨1558388, by rfl⟩ : syracuseStep 2077851 = 3116777) B3116777
theorem B2106205 : Blo 2077435 2106205 := bbase (se 3 (by rfl) ⟨394913, by rfl⟩ : syracuseStep 2106205 = 789827) (by norm_num)
theorem B11233093 : Blo 2077435 11233093 := bstep (se 4 (by rfl) ⟨1053102, by rfl⟩ : syracuseStep 11233093 = 2106205) B2106205
theorem B14977457 : Blo 2077435 14977457 := bstep (se 2 (by rfl) ⟨5616546, by rfl⟩ : syracuseStep 14977457 = 11233093) B11233093
theorem B9984971 : Blo 2077435 9984971 := bstep (se 1 (by rfl) ⟨7488728, by rfl⟩ : syracuseStep 9984971 = 14977457) B14977457
theorem B26626589 : Blo 2077435 26626589 := bstep (se 3 (by rfl) ⟨4992485, by rfl⟩ : syracuseStep 26626589 = 9984971) B9984971
theorem B17751059 : Blo 2077435 17751059 := bstep (se 1 (by rfl) ⟨13313294, by rfl⟩ : syracuseStep 17751059 = 26626589) B26626589
theorem B11834039 : Blo 2077435 11834039 := bstep (se 1 (by rfl) ⟨8875529, by rfl⟩ : syracuseStep 11834039 = 17751059) B17751059
theorem B7889359 : Blo 2077435 7889359 := bstep (se 1 (by rfl) ⟨5917019, by rfl⟩ : syracuseStep 7889359 = 11834039) B11834039
theorem B10519145 : Blo 2077435 10519145 := bstep (se 2 (by rfl) ⟨3944679, by rfl⟩ : syracuseStep 10519145 = 7889359) B7889359
theorem B7012763 : Blo 2077435 7012763 := bstep (se 1 (by rfl) ⟨5259572, by rfl⟩ : syracuseStep 7012763 = 10519145) B10519145
theorem B4675175 : Blo 2077435 4675175 := bstep (se 1 (by rfl) ⟨3506381, by rfl⟩ : syracuseStep 4675175 = 7012763) B7012763
theorem B3116783 : Blo 2077435 3116783 := bstep (se 1 (by rfl) ⟨2337587, by rfl⟩ : syracuseStep 3116783 = 4675175) B4675175
theorem B2077855 : Blo 2077435 2077855 := bstep (se 1 (by rfl) ⟨1558391, by rfl⟩ : syracuseStep 2077855 = 3116783) B3116783
theorem B3116789 : Blo 2077435 3116789 := bbase (se 5 (by rfl) ⟨146099, by rfl⟩ : syracuseStep 3116789 = 292199) (by norm_num)
theorem B2077859 : Blo 2077435 2077859 := bstep (se 1 (by rfl) ⟨1558394, by rfl⟩ : syracuseStep 2077859 = 3116789) B3116789
theorem B2496253 : Blo 2077435 2496253 := bbase (se 3 (by rfl) ⟨468047, by rfl⟩ : syracuseStep 2496253 = 936095) (by norm_num)
theorem B3328337 : Blo 2077435 3328337 := bstep (se 2 (by rfl) ⟨1248126, by rfl⟩ : syracuseStep 3328337 = 2496253) B2496253
theorem B8875565 : Blo 2077435 8875565 := bstep (se 3 (by rfl) ⟨1664168, by rfl⟩ : syracuseStep 8875565 = 3328337) B3328337
theorem B5917043 : Blo 2077435 5917043 := bstep (se 1 (by rfl) ⟨4437782, by rfl⟩ : syracuseStep 5917043 = 8875565) B8875565
theorem B3944695 : Blo 2077435 3944695 := bstep (se 1 (by rfl) ⟨2958521, by rfl⟩ : syracuseStep 3944695 = 5917043) B5917043
theorem B5259593 : Blo 2077435 5259593 := bstep (se 2 (by rfl) ⟨1972347, by rfl⟩ : syracuseStep 5259593 = 3944695) B3944695
theorem B3506395 : Blo 2077435 3506395 := bstep (se 1 (by rfl) ⟨2629796, by rfl⟩ : syracuseStep 3506395 = 5259593) B5259593
theorem B4675193 : Blo 2077435 4675193 := bstep (se 2 (by rfl) ⟨1753197, by rfl⟩ : syracuseStep 4675193 = 3506395) B3506395
theorem B3116795 : Blo 2077435 3116795 := bstep (se 1 (by rfl) ⟨2337596, by rfl⟩ : syracuseStep 3116795 = 4675193) B4675193
theorem B2077863 : Blo 2077435 2077863 := bstep (se 1 (by rfl) ⟨1558397, by rfl⟩ : syracuseStep 2077863 = 3116795) B3116795
theorem B2337601 : Blo 2077435 2337601 := bbase (se 2 (by rfl) ⟨876600, by rfl⟩ : syracuseStep 2337601 = 1753201) (by norm_num)
theorem B3116801 : Blo 2077435 3116801 := bstep (se 2 (by rfl) ⟨1168800, by rfl⟩ : syracuseStep 3116801 = 2337601) B2337601
theorem B2077867 : Blo 2077435 2077867 := bstep (se 1 (by rfl) ⟨1558400, by rfl⟩ : syracuseStep 2077867 = 3116801) B3116801
theorem B5259613 : Blo 2077435 5259613 := bbase (se 3 (by rfl) ⟨986177, by rfl⟩ : syracuseStep 5259613 = 1972355) (by norm_num)
theorem B7012817 : Blo 2077435 7012817 := bstep (se 2 (by rfl) ⟨2629806, by rfl⟩ : syracuseStep 7012817 = 5259613) B5259613
theorem B4675211 : Blo 2077435 4675211 := bstep (se 1 (by rfl) ⟨3506408, by rfl⟩ : syracuseStep 4675211 = 7012817) B7012817
theorem B3116807 : Blo 2077435 3116807 := bstep (se 1 (by rfl) ⟨2337605, by rfl⟩ : syracuseStep 3116807 = 4675211) B4675211
theorem B2077871 : Blo 2077435 2077871 := bstep (se 1 (by rfl) ⟨1558403, by rfl⟩ : syracuseStep 2077871 = 3116807) B3116807
theorem B3116813 : Blo 2077435 3116813 := bbase (se 3 (by rfl) ⟨584402, by rfl⟩ : syracuseStep 3116813 = 1168805) (by norm_num)
theorem B2077875 : Blo 2077435 2077875 := bstep (se 1 (by rfl) ⟨1558406, by rfl⟩ : syracuseStep 2077875 = 3116813) B3116813
theorem B4675229 : Blo 2077435 4675229 := bbase (se 3 (by rfl) ⟨876605, by rfl⟩ : syracuseStep 4675229 = 1753211) (by norm_num)
theorem B3116819 : Blo 2077435 3116819 := bstep (se 1 (by rfl) ⟨2337614, by rfl⟩ : syracuseStep 3116819 = 4675229) B4675229
theorem B2077879 : Blo 2077435 2077879 := bstep (se 1 (by rfl) ⟨1558409, by rfl⟩ : syracuseStep 2077879 = 3116819) B3116819
theorem B3506429 : Blo 2077435 3506429 := bbase (se 3 (by rfl) ⟨657455, by rfl⟩ : syracuseStep 3506429 = 1314911) (by norm_num)
theorem B2337619 : Blo 2077435 2337619 := bstep (se 1 (by rfl) ⟨1753214, by rfl⟩ : syracuseStep 2337619 = 3506429) B3506429
theorem B3116825 : Blo 2077435 3116825 := bstep (se 2 (by rfl) ⟨1168809, by rfl⟩ : syracuseStep 3116825 = 2337619) B2337619
theorem B2077883 : Blo 2077435 2077883 := bstep (se 1 (by rfl) ⟨1558412, by rfl⟩ : syracuseStep 2077883 = 3116825) B3116825
theorem B2808317 : Blo 2077435 2808317 := bbase (se 3 (by rfl) ⟨526559, by rfl⟩ : syracuseStep 2808317 = 1053119) (by norm_num)
theorem B7488845 : Blo 2077435 7488845 := bstep (se 3 (by rfl) ⟨1404158, by rfl⟩ : syracuseStep 7488845 = 2808317) B2808317
theorem B4992563 : Blo 2077435 4992563 := bstep (se 1 (by rfl) ⟨3744422, by rfl⟩ : syracuseStep 4992563 = 7488845) B7488845
theorem B3328375 : Blo 2077435 3328375 := bstep (se 1 (by rfl) ⟨2496281, by rfl⟩ : syracuseStep 3328375 = 4992563) B4992563
theorem B4437833 : Blo 2077435 4437833 := bstep (se 2 (by rfl) ⟨1664187, by rfl⟩ : syracuseStep 4437833 = 3328375) B3328375
theorem B11834221 : Blo 2077435 11834221 := bstep (se 3 (by rfl) ⟨2218916, by rfl⟩ : syracuseStep 11834221 = 4437833) B4437833
theorem B15778961 : Blo 2077435 15778961 := bstep (se 2 (by rfl) ⟨5917110, by rfl⟩ : syracuseStep 15778961 = 11834221) B11834221
theorem B10519307 : Blo 2077435 10519307 := bstep (se 1 (by rfl) ⟨7889480, by rfl⟩ : syracuseStep 10519307 = 15778961) B15778961
theorem B7012871 : Blo 2077435 7012871 := bstep (se 1 (by rfl) ⟨5259653, by rfl⟩ : syracuseStep 7012871 = 10519307) B10519307
theorem B4675247 : Blo 2077435 4675247 := bstep (se 1 (by rfl) ⟨3506435, by rfl⟩ : syracuseStep 4675247 = 7012871) B7012871
theorem B3116831 : Blo 2077435 3116831 := bstep (se 1 (by rfl) ⟨2337623, by rfl⟩ : syracuseStep 3116831 = 4675247) B4675247
theorem B2077887 : Blo 2077435 2077887 := bstep (se 1 (by rfl) ⟨1558415, by rfl⟩ : syracuseStep 2077887 = 3116831) B3116831
theorem B3116837 : Blo 2077435 3116837 := bbase (se 4 (by rfl) ⟨292203, by rfl⟩ : syracuseStep 3116837 = 584407) (by norm_num)
theorem B2077891 : Blo 2077435 2077891 := bstep (se 1 (by rfl) ⟨1558418, by rfl⟩ : syracuseStep 2077891 = 3116837) B3116837
theorem B2629837 : Blo 2077435 2629837 := bbase (se 3 (by rfl) ⟨493094, by rfl⟩ : syracuseStep 2629837 = 986189) (by norm_num)
theorem B3506449 : Blo 2077435 3506449 := bstep (se 2 (by rfl) ⟨1314918, by rfl⟩ : syracuseStep 3506449 = 2629837) B2629837
theorem B4675265 : Blo 2077435 4675265 := bstep (se 2 (by rfl) ⟨1753224, by rfl⟩ : syracuseStep 4675265 = 3506449) B3506449
theorem B3116843 : Blo 2077435 3116843 := bstep (se 1 (by rfl) ⟨2337632, by rfl⟩ : syracuseStep 3116843 = 4675265) B4675265
theorem B2077895 : Blo 2077435 2077895 := bstep (se 1 (by rfl) ⟨1558421, by rfl⟩ : syracuseStep 2077895 = 3116843) B3116843
theorem B2337637 : Blo 2077435 2337637 := bbase (se 4 (by rfl) ⟨219153, by rfl⟩ : syracuseStep 2337637 = 438307) (by norm_num)
theorem B3116849 : Blo 2077435 3116849 := bstep (se 2 (by rfl) ⟨1168818, by rfl⟩ : syracuseStep 3116849 = 2337637) B2337637
theorem B2077899 : Blo 2077435 2077899 := bstep (se 1 (by rfl) ⟨1558424, by rfl⟩ : syracuseStep 2077899 = 3116849) B3116849
theorem B5917157 : Blo 2077435 5917157 := bbase (se 4 (by rfl) ⟨554733, by rfl⟩ : syracuseStep 5917157 = 1109467) (by norm_num)
theorem B3944771 : Blo 2077435 3944771 := bstep (se 1 (by rfl) ⟨2958578, by rfl⟩ : syracuseStep 3944771 = 5917157) B5917157
theorem B2629847 : Blo 2077435 2629847 := bstep (se 1 (by rfl) ⟨1972385, by rfl⟩ : syracuseStep 2629847 = 3944771) B3944771
theorem B7012925 : Blo 2077435 7012925 := bstep (se 3 (by rfl) ⟨1314923, by rfl⟩ : syracuseStep 7012925 = 2629847) B2629847
theorem B4675283 : Blo 2077435 4675283 := bstep (se 1 (by rfl) ⟨3506462, by rfl⟩ : syracuseStep 4675283 = 7012925) B7012925
theorem B3116855 : Blo 2077435 3116855 := bstep (se 1 (by rfl) ⟨2337641, by rfl⟩ : syracuseStep 3116855 = 4675283) B4675283
theorem B2077903 : Blo 2077435 2077903 := bstep (se 1 (by rfl) ⟨1558427, by rfl⟩ : syracuseStep 2077903 = 3116855) B3116855
theorem B3116861 : Blo 2077435 3116861 := bbase (se 3 (by rfl) ⟨584411, by rfl⟩ : syracuseStep 3116861 = 1168823) (by norm_num)
theorem B2077907 : Blo 2077435 2077907 := bstep (se 1 (by rfl) ⟨1558430, by rfl⟩ : syracuseStep 2077907 = 3116861) B3116861
theorem B4675301 : Blo 2077435 4675301 := bbase (se 4 (by rfl) ⟨438309, by rfl⟩ : syracuseStep 4675301 = 876619) (by norm_num)
theorem B3116867 : Blo 2077435 3116867 := bstep (se 1 (by rfl) ⟨2337650, by rfl⟩ : syracuseStep 3116867 = 4675301) B4675301
theorem B2077911 : Blo 2077435 2077911 := bstep (se 1 (by rfl) ⟨1558433, by rfl⟩ : syracuseStep 2077911 = 3116867) B3116867
theorem B5259725 : Blo 2077435 5259725 := bbase (se 3 (by rfl) ⟨986198, by rfl⟩ : syracuseStep 5259725 = 1972397) (by norm_num)
theorem B3506483 : Blo 2077435 3506483 := bstep (se 1 (by rfl) ⟨2629862, by rfl⟩ : syracuseStep 3506483 = 5259725) B5259725
theorem B2337655 : Blo 2077435 2337655 := bstep (se 1 (by rfl) ⟨1753241, by rfl⟩ : syracuseStep 2337655 = 3506483) B3506483
theorem B3116873 : Blo 2077435 3116873 := bstep (se 2 (by rfl) ⟨1168827, by rfl⟩ : syracuseStep 3116873 = 2337655) B2337655
theorem B2077915 : Blo 2077435 2077915 := bstep (se 1 (by rfl) ⟨1558436, by rfl⟩ : syracuseStep 2077915 = 3116873) B3116873
theorem B2530381 : Blo 2077435 2530381 := bbase (se 3 (by rfl) ⟨474446, by rfl⟩ : syracuseStep 2530381 = 948893) (by norm_num)
theorem B3373841 : Blo 2077435 3373841 := bstep (se 2 (by rfl) ⟨1265190, by rfl⟩ : syracuseStep 3373841 = 2530381) B2530381
theorem B2249227 : Blo 2077435 2249227 := bstep (se 1 (by rfl) ⟨1686920, by rfl⟩ : syracuseStep 2249227 = 3373841) B3373841
theorem B11995877 : Blo 2077435 11995877 := bstep (se 4 (by rfl) ⟨1124613, by rfl⟩ : syracuseStep 11995877 = 2249227) B2249227
theorem B7997251 : Blo 2077435 7997251 := bstep (se 1 (by rfl) ⟨5997938, by rfl⟩ : syracuseStep 7997251 = 11995877) B11995877
theorem B10663001 : Blo 2077435 10663001 := bstep (se 2 (by rfl) ⟨3998625, by rfl⟩ : syracuseStep 10663001 = 7997251) B7997251
theorem B7108667 : Blo 2077435 7108667 := bstep (se 1 (by rfl) ⟨5331500, by rfl⟩ : syracuseStep 7108667 = 10663001) B10663001
theorem B4739111 : Blo 2077435 4739111 := bstep (se 1 (by rfl) ⟨3554333, by rfl⟩ : syracuseStep 4739111 = 7108667) B7108667
theorem B3159407 : Blo 2077435 3159407 := bstep (se 1 (by rfl) ⟨2369555, by rfl⟩ : syracuseStep 3159407 = 4739111) B4739111
theorem B2106271 : Blo 2077435 2106271 := bstep (se 1 (by rfl) ⟨1579703, by rfl⟩ : syracuseStep 2106271 = 3159407) B3159407
theorem B2808361 : Blo 2077435 2808361 := bstep (se 2 (by rfl) ⟨1053135, by rfl⟩ : syracuseStep 2808361 = 2106271) B2106271
theorem B3744481 : Blo 2077435 3744481 := bstep (se 2 (by rfl) ⟨1404180, by rfl⟩ : syracuseStep 3744481 = 2808361) B2808361
theorem B4992641 : Blo 2077435 4992641 := bstep (se 2 (by rfl) ⟨1872240, by rfl⟩ : syracuseStep 4992641 = 3744481) B3744481
theorem B3328427 : Blo 2077435 3328427 := bstep (se 1 (by rfl) ⟨2496320, by rfl⟩ : syracuseStep 3328427 = 4992641) B4992641
theorem B2218951 : Blo 2077435 2218951 := bstep (se 1 (by rfl) ⟨1664213, by rfl⟩ : syracuseStep 2218951 = 3328427) B3328427
theorem B2958601 : Blo 2077435 2958601 := bstep (se 2 (by rfl) ⟨1109475, by rfl⟩ : syracuseStep 2958601 = 2218951) B2218951
theorem B3944801 : Blo 2077435 3944801 := bstep (se 2 (by rfl) ⟨1479300, by rfl⟩ : syracuseStep 3944801 = 2958601) B2958601
theorem B10519469 : Blo 2077435 10519469 := bstep (se 3 (by rfl) ⟨1972400, by rfl⟩ : syracuseStep 10519469 = 3944801) B3944801
theorem B7012979 : Blo 2077435 7012979 := bstep (se 1 (by rfl) ⟨5259734, by rfl⟩ : syracuseStep 7012979 = 10519469) B10519469
theorem B4675319 : Blo 2077435 4675319 := bstep (se 1 (by rfl) ⟨3506489, by rfl⟩ : syracuseStep 4675319 = 7012979) B7012979
theorem B3116879 : Blo 2077435 3116879 := bstep (se 1 (by rfl) ⟨2337659, by rfl⟩ : syracuseStep 3116879 = 4675319) B4675319
theorem B2077919 : Blo 2077435 2077919 := bstep (se 1 (by rfl) ⟨1558439, by rfl⟩ : syracuseStep 2077919 = 3116879) B3116879
theorem B3116885 : Blo 2077435 3116885 := bbase (se 9 (by rfl) ⟨9131, by rfl⟩ : syracuseStep 3116885 = 18263) (by norm_num)
theorem B2077923 : Blo 2077435 2077923 := bstep (se 1 (by rfl) ⟨1558442, by rfl⟩ : syracuseStep 2077923 = 3116885) B3116885
theorem B10121557 : Blo 2077435 10121557 := bbase (se 10 (by rfl) ⟨14826, by rfl⟩ : syracuseStep 10121557 = 29653) (by norm_num)
theorem B13495409 : Blo 2077435 13495409 := bstep (se 2 (by rfl) ⟨5060778, by rfl⟩ : syracuseStep 13495409 = 10121557) B10121557
theorem B8996939 : Blo 2077435 8996939 := bstep (se 1 (by rfl) ⟨6747704, by rfl⟩ : syracuseStep 8996939 = 13495409) B13495409
theorem B5997959 : Blo 2077435 5997959 := bstep (se 1 (by rfl) ⟨4498469, by rfl⟩ : syracuseStep 5997959 = 8996939) B8996939
theorem B3998639 : Blo 2077435 3998639 := bstep (se 1 (by rfl) ⟨2998979, by rfl⟩ : syracuseStep 3998639 = 5997959) B5997959
theorem B2665759 : Blo 2077435 2665759 := bstep (se 1 (by rfl) ⟨1999319, by rfl⟩ : syracuseStep 2665759 = 3998639) B3998639
theorem B3554345 : Blo 2077435 3554345 := bstep (se 2 (by rfl) ⟨1332879, by rfl⟩ : syracuseStep 3554345 = 2665759) B2665759
theorem B9478253 : Blo 2077435 9478253 := bstep (se 3 (by rfl) ⟨1777172, by rfl⟩ : syracuseStep 9478253 = 3554345) B3554345
theorem B25275341 : Blo 2077435 25275341 := bstep (se 3 (by rfl) ⟨4739126, by rfl⟩ : syracuseStep 25275341 = 9478253) B9478253
theorem B16850227 : Blo 2077435 16850227 := bstep (se 1 (by rfl) ⟨12637670, by rfl⟩ : syracuseStep 16850227 = 25275341) B25275341
theorem B22466969 : Blo 2077435 22466969 := bstep (se 2 (by rfl) ⟨8425113, by rfl⟩ : syracuseStep 22466969 = 16850227) B16850227
theorem B14977979 : Blo 2077435 14977979 := bstep (se 1 (by rfl) ⟨11233484, by rfl⟩ : syracuseStep 14977979 = 22466969) B22466969
theorem B9985319 : Blo 2077435 9985319 := bstep (se 1 (by rfl) ⟨7488989, by rfl⟩ : syracuseStep 9985319 = 14977979) B14977979
theorem B6656879 : Blo 2077435 6656879 := bstep (se 1 (by rfl) ⟨4992659, by rfl⟩ : syracuseStep 6656879 = 9985319) B9985319
theorem B4437919 : Blo 2077435 4437919 := bstep (se 1 (by rfl) ⟨3328439, by rfl⟩ : syracuseStep 4437919 = 6656879) B6656879
theorem B5917225 : Blo 2077435 5917225 := bstep (se 2 (by rfl) ⟨2218959, by rfl⟩ : syracuseStep 5917225 = 4437919) B4437919
theorem B7889633 : Blo 2077435 7889633 := bstep (se 2 (by rfl) ⟨2958612, by rfl⟩ : syracuseStep 7889633 = 5917225) B5917225
theorem B5259755 : Blo 2077435 5259755 := bstep (se 1 (by rfl) ⟨3944816, by rfl⟩ : syracuseStep 5259755 = 7889633) B7889633
theorem B3506503 : Blo 2077435 3506503 := bstep (se 1 (by rfl) ⟨2629877, by rfl⟩ : syracuseStep 3506503 = 5259755) B5259755
theorem B4675337 : Blo 2077435 4675337 := bstep (se 2 (by rfl) ⟨1753251, by rfl⟩ : syracuseStep 4675337 = 3506503) B3506503
theorem B3116891 : Blo 2077435 3116891 := bstep (se 1 (by rfl) ⟨2337668, by rfl⟩ : syracuseStep 3116891 = 4675337) B4675337
theorem B2077927 : Blo 2077435 2077927 := bstep (se 1 (by rfl) ⟨1558445, by rfl⟩ : syracuseStep 2077927 = 3116891) B3116891
theorem B2337673 : Blo 2077435 2337673 := bbase (se 2 (by rfl) ⟨876627, by rfl⟩ : syracuseStep 2337673 = 1753255) (by norm_num)
theorem B3116897 : Blo 2077435 3116897 := bstep (se 2 (by rfl) ⟨1168836, by rfl⟩ : syracuseStep 3116897 = 2337673) B2337673
theorem B2077931 : Blo 2077435 2077931 := bstep (se 1 (by rfl) ⟨1558448, by rfl⟩ : syracuseStep 2077931 = 3116897) B3116897
theorem B9119717 : Blo 2077435 9119717 := bbase (se 4 (by rfl) ⟨854973, by rfl⟩ : syracuseStep 9119717 = 1709947) (by norm_num)
theorem B6079811 : Blo 2077435 6079811 := bstep (se 1 (by rfl) ⟨4559858, by rfl⟩ : syracuseStep 6079811 = 9119717) B9119717
theorem B16212829 : Blo 2077435 16212829 := bstep (se 3 (by rfl) ⟨3039905, by rfl⟩ : syracuseStep 16212829 = 6079811) B6079811
theorem B345873685 : Blo 2077435 345873685 := bstep (se 6 (by rfl) ⟨8106414, by rfl⟩ : syracuseStep 345873685 = 16212829) B16212829
theorem B461164913 : Blo 2077435 461164913 := bstep (se 2 (by rfl) ⟨172936842, by rfl⟩ : syracuseStep 461164913 = 345873685) B345873685
theorem B307443275 : Blo 2077435 307443275 := bstep (se 1 (by rfl) ⟨230582456, by rfl⟩ : syracuseStep 307443275 = 461164913) B461164913
theorem B204962183 : Blo 2077435 204962183 := bstep (se 1 (by rfl) ⟨153721637, by rfl⟩ : syracuseStep 204962183 = 307443275) B307443275
theorem B136641455 : Blo 2077435 136641455 := bstep (se 1 (by rfl) ⟨102481091, by rfl⟩ : syracuseStep 136641455 = 204962183) B204962183
theorem B91094303 : Blo 2077435 91094303 := bstep (se 1 (by rfl) ⟨68320727, by rfl⟩ : syracuseStep 91094303 = 136641455) B136641455
theorem B60729535 : Blo 2077435 60729535 := bstep (se 1 (by rfl) ⟨45547151, by rfl⟩ : syracuseStep 60729535 = 91094303) B91094303
theorem B80972713 : Blo 2077435 80972713 := bstep (se 2 (by rfl) ⟨30364767, by rfl⟩ : syracuseStep 80972713 = 60729535) B60729535
theorem B107963617 : Blo 2077435 107963617 := bstep (se 2 (by rfl) ⟨40486356, by rfl⟩ : syracuseStep 107963617 = 80972713) B80972713
theorem B143951489 : Blo 2077435 143951489 := bstep (se 2 (by rfl) ⟨53981808, by rfl⟩ : syracuseStep 143951489 = 107963617) B107963617
theorem B95967659 : Blo 2077435 95967659 := bstep (se 1 (by rfl) ⟨71975744, by rfl⟩ : syracuseStep 95967659 = 143951489) B143951489
theorem B63978439 : Blo 2077435 63978439 := bstep (se 1 (by rfl) ⟨47983829, by rfl⟩ : syracuseStep 63978439 = 95967659) B95967659
theorem B85304585 : Blo 2077435 85304585 := bstep (se 2 (by rfl) ⟨31989219, by rfl⟩ : syracuseStep 85304585 = 63978439) B63978439
theorem B56869723 : Blo 2077435 56869723 := bstep (se 1 (by rfl) ⟨42652292, by rfl⟩ : syracuseStep 56869723 = 85304585) B85304585
theorem B75826297 : Blo 2077435 75826297 := bstep (se 2 (by rfl) ⟨28434861, by rfl⟩ : syracuseStep 75826297 = 56869723) B56869723
theorem B101101729 : Blo 2077435 101101729 := bstep (se 2 (by rfl) ⟨37913148, by rfl⟩ : syracuseStep 101101729 = 75826297) B75826297
theorem B134802305 : Blo 2077435 134802305 := bstep (se 2 (by rfl) ⟨50550864, by rfl⟩ : syracuseStep 134802305 = 101101729) B101101729
theorem B89868203 : Blo 2077435 89868203 := bstep (se 1 (by rfl) ⟨67401152, by rfl⟩ : syracuseStep 89868203 = 134802305) B134802305
theorem B59912135 : Blo 2077435 59912135 := bstep (se 1 (by rfl) ⟨44934101, by rfl⟩ : syracuseStep 59912135 = 89868203) B89868203
theorem B39941423 : Blo 2077435 39941423 := bstep (se 1 (by rfl) ⟨29956067, by rfl⟩ : syracuseStep 39941423 = 59912135) B59912135
theorem B26627615 : Blo 2077435 26627615 := bstep (se 1 (by rfl) ⟨19970711, by rfl⟩ : syracuseStep 26627615 = 39941423) B39941423
theorem B17751743 : Blo 2077435 17751743 := bstep (se 1 (by rfl) ⟨13313807, by rfl⟩ : syracuseStep 17751743 = 26627615) B26627615
theorem B11834495 : Blo 2077435 11834495 := bstep (se 1 (by rfl) ⟨8875871, by rfl⟩ : syracuseStep 11834495 = 17751743) B17751743
theorem B7889663 : Blo 2077435 7889663 := bstep (se 1 (by rfl) ⟨5917247, by rfl⟩ : syracuseStep 7889663 = 11834495) B11834495
theorem B5259775 : Blo 2077435 5259775 := bstep (se 1 (by rfl) ⟨3944831, by rfl⟩ : syracuseStep 5259775 = 7889663) B7889663
theorem B7013033 : Blo 2077435 7013033 := bstep (se 2 (by rfl) ⟨2629887, by rfl⟩ : syracuseStep 7013033 = 5259775) B5259775
theorem B4675355 : Blo 2077435 4675355 := bstep (se 1 (by rfl) ⟨3506516, by rfl⟩ : syracuseStep 4675355 = 7013033) B7013033
theorem B3116903 : Blo 2077435 3116903 := bstep (se 1 (by rfl) ⟨2337677, by rfl⟩ : syracuseStep 3116903 = 4675355) B4675355
theorem B2077935 : Blo 2077435 2077935 := bstep (se 1 (by rfl) ⟨1558451, by rfl⟩ : syracuseStep 2077935 = 3116903) B3116903
theorem B3116909 : Blo 2077435 3116909 := bbase (se 3 (by rfl) ⟨584420, by rfl⟩ : syracuseStep 3116909 = 1168841) (by norm_num)
theorem B2077939 : Blo 2077435 2077939 := bstep (se 1 (by rfl) ⟨1558454, by rfl⟩ : syracuseStep 2077939 = 3116909) B3116909
theorem B4675373 : Blo 2077435 4675373 := bbase (se 3 (by rfl) ⟨876632, by rfl⟩ : syracuseStep 4675373 = 1753265) (by norm_num)
theorem B3116915 : Blo 2077435 3116915 := bstep (se 1 (by rfl) ⟨2337686, by rfl⟩ : syracuseStep 3116915 = 4675373) B4675373
theorem B2077943 : Blo 2077435 2077943 := bstep (se 1 (by rfl) ⟨1558457, by rfl⟩ : syracuseStep 2077943 = 3116915) B3116915
theorem B8875925 : Blo 2077435 8875925 := bbase (se 6 (by rfl) ⟨208029, by rfl⟩ : syracuseStep 8875925 = 416059) (by norm_num)
theorem B5917283 : Blo 2077435 5917283 := bstep (se 1 (by rfl) ⟨4437962, by rfl⟩ : syracuseStep 5917283 = 8875925) B8875925
theorem B3944855 : Blo 2077435 3944855 := bstep (se 1 (by rfl) ⟨2958641, by rfl⟩ : syracuseStep 3944855 = 5917283) B5917283
theorem B2629903 : Blo 2077435 2629903 := bstep (se 1 (by rfl) ⟨1972427, by rfl⟩ : syracuseStep 2629903 = 3944855) B3944855
theorem B3506537 : Blo 2077435 3506537 := bstep (se 2 (by rfl) ⟨1314951, by rfl⟩ : syracuseStep 3506537 = 2629903) B2629903
theorem B2337691 : Blo 2077435 2337691 := bstep (se 1 (by rfl) ⟨1753268, by rfl⟩ : syracuseStep 2337691 = 3506537) B3506537
theorem B3116921 : Blo 2077435 3116921 := bstep (se 2 (by rfl) ⟨1168845, by rfl⟩ : syracuseStep 3116921 = 2337691) B2337691
theorem B2077947 : Blo 2077435 2077947 := bstep (se 1 (by rfl) ⟨1558460, by rfl⟩ : syracuseStep 2077947 = 3116921) B3116921
theorem B13313909 : Blo 2077435 13313909 := bbase (se 5 (by rfl) ⟨624089, by rfl⟩ : syracuseStep 13313909 = 1248179) (by norm_num)
theorem B35503757 : Blo 2077435 35503757 := bstep (se 3 (by rfl) ⟨6656954, by rfl⟩ : syracuseStep 35503757 = 13313909) B13313909
theorem B23669171 : Blo 2077435 23669171 := bstep (se 1 (by rfl) ⟨17751878, by rfl⟩ : syracuseStep 23669171 = 35503757) B35503757
theorem B15779447 : Blo 2077435 15779447 := bstep (se 1 (by rfl) ⟨11834585, by rfl⟩ : syracuseStep 15779447 = 23669171) B23669171
theorem B10519631 : Blo 2077435 10519631 := bstep (se 1 (by rfl) ⟨7889723, by rfl⟩ : syracuseStep 10519631 = 15779447) B15779447
theorem B7013087 : Blo 2077435 7013087 := bstep (se 1 (by rfl) ⟨5259815, by rfl⟩ : syracuseStep 7013087 = 10519631) B10519631
theorem B4675391 : Blo 2077435 4675391 := bstep (se 1 (by rfl) ⟨3506543, by rfl⟩ : syracuseStep 4675391 = 7013087) B7013087
theorem B3116927 : Blo 2077435 3116927 := bstep (se 1 (by rfl) ⟨2337695, by rfl⟩ : syracuseStep 3116927 = 4675391) B4675391
theorem B2077951 : Blo 2077435 2077951 := bstep (se 1 (by rfl) ⟨1558463, by rfl⟩ : syracuseStep 2077951 = 3116927) B3116927
theorem B3116933 : Blo 2077435 3116933 := bbase (se 4 (by rfl) ⟨292212, by rfl⟩ : syracuseStep 3116933 = 584425) (by norm_num)
theorem B2077955 : Blo 2077435 2077955 := bstep (se 1 (by rfl) ⟨1558466, by rfl⟩ : syracuseStep 2077955 = 3116933) B3116933
theorem B3506557 : Blo 2077435 3506557 := bbase (se 3 (by rfl) ⟨657479, by rfl⟩ : syracuseStep 3506557 = 1314959) (by norm_num)
theorem B4675409 : Blo 2077435 4675409 := bstep (se 2 (by rfl) ⟨1753278, by rfl⟩ : syracuseStep 4675409 = 3506557) B3506557
theorem B3116939 : Blo 2077435 3116939 := bstep (se 1 (by rfl) ⟨2337704, by rfl⟩ : syracuseStep 3116939 = 4675409) B4675409
theorem B2077959 : Blo 2077435 2077959 := bstep (se 1 (by rfl) ⟨1558469, by rfl⟩ : syracuseStep 2077959 = 3116939) B3116939
theorem B2337709 : Blo 2077435 2337709 := bbase (se 3 (by rfl) ⟨438320, by rfl⟩ : syracuseStep 2337709 = 876641) (by norm_num)
theorem B3116945 : Blo 2077435 3116945 := bstep (se 2 (by rfl) ⟨1168854, by rfl⟩ : syracuseStep 3116945 = 2337709) B2337709
theorem B2077963 : Blo 2077435 2077963 := bstep (se 1 (by rfl) ⟨1558472, by rfl⟩ : syracuseStep 2077963 = 3116945) B3116945
theorem B7013141 : Blo 2077435 7013141 := bbase (se 6 (by rfl) ⟨164370, by rfl⟩ : syracuseStep 7013141 = 328741) (by norm_num)
theorem B4675427 : Blo 2077435 4675427 := bstep (se 1 (by rfl) ⟨3506570, by rfl⟩ : syracuseStep 4675427 = 7013141) B7013141
theorem B3116951 : Blo 2077435 3116951 := bstep (se 1 (by rfl) ⟨2337713, by rfl⟩ : syracuseStep 3116951 = 4675427) B4675427
theorem B2077967 : Blo 2077435 2077967 := bstep (se 1 (by rfl) ⟨1558475, by rfl⟩ : syracuseStep 2077967 = 3116951) B3116951
theorem B3116957 : Blo 2077435 3116957 := bbase (se 3 (by rfl) ⟨584429, by rfl⟩ : syracuseStep 3116957 = 1168859) (by norm_num)
theorem B2077971 : Blo 2077435 2077971 := bstep (se 1 (by rfl) ⟨1558478, by rfl⟩ : syracuseStep 2077971 = 3116957) B3116957
theorem B4675445 : Blo 2077435 4675445 := bbase (se 5 (by rfl) ⟨219161, by rfl⟩ : syracuseStep 4675445 = 438323) (by norm_num)
theorem B3116963 : Blo 2077435 3116963 := bstep (se 1 (by rfl) ⟨2337722, by rfl⟩ : syracuseStep 3116963 = 4675445) B4675445
theorem B2077975 : Blo 2077435 2077975 := bstep (se 1 (by rfl) ⟨1558481, by rfl⟩ : syracuseStep 2077975 = 3116963) B3116963
theorem B5331653 : Blo 2077435 5331653 := bbase (se 4 (by rfl) ⟨499842, by rfl⟩ : syracuseStep 5331653 = 999685) (by norm_num)
theorem B3554435 : Blo 2077435 3554435 := bstep (se 1 (by rfl) ⟨2665826, by rfl⟩ : syracuseStep 3554435 = 5331653) B5331653
theorem B2369623 : Blo 2077435 2369623 := bstep (se 1 (by rfl) ⟨1777217, by rfl⟩ : syracuseStep 2369623 = 3554435) B3554435
theorem B3159497 : Blo 2077435 3159497 := bstep (se 2 (by rfl) ⟨1184811, by rfl⟩ : syracuseStep 3159497 = 2369623) B2369623
theorem B2106331 : Blo 2077435 2106331 := bstep (se 1 (by rfl) ⟨1579748, by rfl⟩ : syracuseStep 2106331 = 3159497) B3159497
theorem B11233765 : Blo 2077435 11233765 := bstep (se 4 (by rfl) ⟨1053165, by rfl⟩ : syracuseStep 11233765 = 2106331) B2106331
theorem B14978353 : Blo 2077435 14978353 := bstep (se 2 (by rfl) ⟨5616882, by rfl⟩ : syracuseStep 14978353 = 11233765) B11233765
theorem B19971137 : Blo 2077435 19971137 := bstep (se 2 (by rfl) ⟨7489176, by rfl⟩ : syracuseStep 19971137 = 14978353) B14978353
theorem B13314091 : Blo 2077435 13314091 := bstep (se 1 (by rfl) ⟨9985568, by rfl⟩ : syracuseStep 13314091 = 19971137) B19971137
theorem B17752121 : Blo 2077435 17752121 := bstep (se 2 (by rfl) ⟨6657045, by rfl⟩ : syracuseStep 17752121 = 13314091) B13314091
theorem B11834747 : Blo 2077435 11834747 := bstep (se 1 (by rfl) ⟨8876060, by rfl⟩ : syracuseStep 11834747 = 17752121) B17752121
theorem B7889831 : Blo 2077435 7889831 := bstep (se 1 (by rfl) ⟨5917373, by rfl⟩ : syracuseStep 7889831 = 11834747) B11834747
theorem B5259887 : Blo 2077435 5259887 := bstep (se 1 (by rfl) ⟨3944915, by rfl⟩ : syracuseStep 5259887 = 7889831) B7889831
theorem B3506591 : Blo 2077435 3506591 := bstep (se 1 (by rfl) ⟨2629943, by rfl⟩ : syracuseStep 3506591 = 5259887) B5259887
theorem B2337727 : Blo 2077435 2337727 := bstep (se 1 (by rfl) ⟨1753295, by rfl⟩ : syracuseStep 2337727 = 3506591) B3506591
theorem B3116969 : Blo 2077435 3116969 := bstep (se 2 (by rfl) ⟨1168863, by rfl⟩ : syracuseStep 3116969 = 2337727) B2337727
theorem B2077979 : Blo 2077435 2077979 := bstep (se 1 (by rfl) ⟨1558484, by rfl⟩ : syracuseStep 2077979 = 3116969) B3116969
theorem B7889845 : Blo 2077435 7889845 := bbase (se 5 (by rfl) ⟨369836, by rfl⟩ : syracuseStep 7889845 = 739673) (by norm_num)
theorem B10519793 : Blo 2077435 10519793 := bstep (se 2 (by rfl) ⟨3944922, by rfl⟩ : syracuseStep 10519793 = 7889845) B7889845
theorem B7013195 : Blo 2077435 7013195 := bstep (se 1 (by rfl) ⟨5259896, by rfl⟩ : syracuseStep 7013195 = 10519793) B10519793
theorem B4675463 : Blo 2077435 4675463 := bstep (se 1 (by rfl) ⟨3506597, by rfl⟩ : syracuseStep 4675463 = 7013195) B7013195
theorem B3116975 : Blo 2077435 3116975 := bstep (se 1 (by rfl) ⟨2337731, by rfl⟩ : syracuseStep 3116975 = 4675463) B4675463
theorem B2077983 : Blo 2077435 2077983 := bstep (se 1 (by rfl) ⟨1558487, by rfl⟩ : syracuseStep 2077983 = 3116975) B3116975
theorem B3116981 : Blo 2077435 3116981 := bbase (se 5 (by rfl) ⟨146108, by rfl⟩ : syracuseStep 3116981 = 292217) (by norm_num)
theorem B2077987 : Blo 2077435 2077987 := bstep (se 1 (by rfl) ⟨1558490, by rfl⟩ : syracuseStep 2077987 = 3116981) B3116981
theorem B5259917 : Blo 2077435 5259917 := bbase (se 3 (by rfl) ⟨986234, by rfl⟩ : syracuseStep 5259917 = 1972469) (by norm_num)
theorem B3506611 : Blo 2077435 3506611 := bstep (se 1 (by rfl) ⟨2629958, by rfl⟩ : syracuseStep 3506611 = 5259917) B5259917
theorem B4675481 : Blo 2077435 4675481 := bstep (se 2 (by rfl) ⟨1753305, by rfl⟩ : syracuseStep 4675481 = 3506611) B3506611
theorem B3116987 : Blo 2077435 3116987 := bstep (se 1 (by rfl) ⟨2337740, by rfl⟩ : syracuseStep 3116987 = 4675481) B4675481
theorem B2077991 : Blo 2077435 2077991 := bstep (se 1 (by rfl) ⟨1558493, by rfl⟩ : syracuseStep 2077991 = 3116987) B3116987
theorem B2337745 : Blo 2077435 2337745 := bbase (se 2 (by rfl) ⟨876654, by rfl⟩ : syracuseStep 2337745 = 1753309) (by norm_num)
theorem B3116993 : Blo 2077435 3116993 := bstep (se 2 (by rfl) ⟨1168872, by rfl⟩ : syracuseStep 3116993 = 2337745) B2337745
theorem B2077995 : Blo 2077435 2077995 := bstep (se 1 (by rfl) ⟨1558496, by rfl⟩ : syracuseStep 2077995 = 3116993) B3116993
theorem B2808469 : Blo 2077435 2808469 := bbase (se 6 (by rfl) ⟨65823, by rfl⟩ : syracuseStep 2808469 = 131647) (by norm_num)
theorem B3744625 : Blo 2077435 3744625 := bstep (se 2 (by rfl) ⟨1404234, by rfl⟩ : syracuseStep 3744625 = 2808469) B2808469
theorem B4992833 : Blo 2077435 4992833 := bstep (se 2 (by rfl) ⟨1872312, by rfl⟩ : syracuseStep 4992833 = 3744625) B3744625
theorem B3328555 : Blo 2077435 3328555 := bstep (se 1 (by rfl) ⟨2496416, by rfl⟩ : syracuseStep 3328555 = 4992833) B4992833
theorem B4438073 : Blo 2077435 4438073 := bstep (se 2 (by rfl) ⟨1664277, by rfl⟩ : syracuseStep 4438073 = 3328555) B3328555
theorem B2958715 : Blo 2077435 2958715 := bstep (se 1 (by rfl) ⟨2219036, by rfl⟩ : syracuseStep 2958715 = 4438073) B4438073
theorem B3944953 : Blo 2077435 3944953 := bstep (se 2 (by rfl) ⟨1479357, by rfl⟩ : syracuseStep 3944953 = 2958715) B2958715
theorem B5259937 : Blo 2077435 5259937 := bstep (se 2 (by rfl) ⟨1972476, by rfl⟩ : syracuseStep 5259937 = 3944953) B3944953
theorem B7013249 : Blo 2077435 7013249 := bstep (se 2 (by rfl) ⟨2629968, by rfl⟩ : syracuseStep 7013249 = 5259937) B5259937
theorem B4675499 : Blo 2077435 4675499 := bstep (se 1 (by rfl) ⟨3506624, by rfl⟩ : syracuseStep 4675499 = 7013249) B7013249
theorem B3116999 : Blo 2077435 3116999 := bstep (se 1 (by rfl) ⟨2337749, by rfl⟩ : syracuseStep 3116999 = 4675499) B4675499
theorem B2077999 : Blo 2077435 2077999 := bstep (se 1 (by rfl) ⟨1558499, by rfl⟩ : syracuseStep 2077999 = 3116999) B3116999
theorem B3117005 : Blo 2077435 3117005 := bbase (se 3 (by rfl) ⟨584438, by rfl⟩ : syracuseStep 3117005 = 1168877) (by norm_num)
theorem B2078003 : Blo 2077435 2078003 := bstep (se 1 (by rfl) ⟨1558502, by rfl⟩ : syracuseStep 2078003 = 3117005) B3117005
theorem B4675517 : Blo 2077435 4675517 := bbase (se 3 (by rfl) ⟨876659, by rfl⟩ : syracuseStep 4675517 = 1753319) (by norm_num)
theorem B3117011 : Blo 2077435 3117011 := bstep (se 1 (by rfl) ⟨2337758, by rfl⟩ : syracuseStep 3117011 = 4675517) B4675517
theorem B2078007 : Blo 2077435 2078007 := bstep (se 1 (by rfl) ⟨1558505, by rfl⟩ : syracuseStep 2078007 = 3117011) B3117011
theorem B3506645 : Blo 2077435 3506645 := bbase (se 7 (by rfl) ⟨41093, by rfl⟩ : syracuseStep 3506645 = 82187) (by norm_num)
theorem B2337763 : Blo 2077435 2337763 := bstep (se 1 (by rfl) ⟨1753322, by rfl⟩ : syracuseStep 2337763 = 3506645) B3506645
theorem B3117017 : Blo 2077435 3117017 := bstep (se 2 (by rfl) ⟨1168881, by rfl⟩ : syracuseStep 3117017 = 2337763) B2337763
theorem B2078011 : Blo 2077435 2078011 := bstep (se 1 (by rfl) ⟨1558508, by rfl⟩ : syracuseStep 2078011 = 3117017) B3117017
theorem B8876213 : Blo 2077435 8876213 := bbase (se 5 (by rfl) ⟨416072, by rfl⟩ : syracuseStep 8876213 = 832145) (by norm_num)
theorem B5917475 : Blo 2077435 5917475 := bstep (se 1 (by rfl) ⟨4438106, by rfl⟩ : syracuseStep 5917475 = 8876213) B8876213
theorem B15779933 : Blo 2077435 15779933 := bstep (se 3 (by rfl) ⟨2958737, by rfl⟩ : syracuseStep 15779933 = 5917475) B5917475
theorem B10519955 : Blo 2077435 10519955 := bstep (se 1 (by rfl) ⟨7889966, by rfl⟩ : syracuseStep 10519955 = 15779933) B15779933
theorem B7013303 : Blo 2077435 7013303 := bstep (se 1 (by rfl) ⟨5259977, by rfl⟩ : syracuseStep 7013303 = 10519955) B10519955
theorem B4675535 : Blo 2077435 4675535 := bstep (se 1 (by rfl) ⟨3506651, by rfl⟩ : syracuseStep 4675535 = 7013303) B7013303
theorem B3117023 : Blo 2077435 3117023 := bstep (se 1 (by rfl) ⟨2337767, by rfl⟩ : syracuseStep 3117023 = 4675535) B4675535
theorem B2078015 : Blo 2077435 2078015 := bstep (se 1 (by rfl) ⟨1558511, by rfl⟩ : syracuseStep 2078015 = 3117023) B3117023
theorem B3117029 : Blo 2077435 3117029 := bbase (se 4 (by rfl) ⟨292221, by rfl⟩ : syracuseStep 3117029 = 584443) (by norm_num)
theorem B2078019 : Blo 2077435 2078019 := bstep (se 1 (by rfl) ⟨1558514, by rfl⟩ : syracuseStep 2078019 = 3117029) B3117029
theorem B9985781 : Blo 2077435 9985781 := bbase (se 5 (by rfl) ⟨468083, by rfl⟩ : syracuseStep 9985781 = 936167) (by norm_num)
theorem B6657187 : Blo 2077435 6657187 := bstep (se 1 (by rfl) ⟨4992890, by rfl⟩ : syracuseStep 6657187 = 9985781) B9985781
theorem B8876249 : Blo 2077435 8876249 := bstep (se 2 (by rfl) ⟨3328593, by rfl⟩ : syracuseStep 8876249 = 6657187) B6657187
theorem B5917499 : Blo 2077435 5917499 := bstep (se 1 (by rfl) ⟨4438124, by rfl⟩ : syracuseStep 5917499 = 8876249) B8876249
theorem B3944999 : Blo 2077435 3944999 := bstep (se 1 (by rfl) ⟨2958749, by rfl⟩ : syracuseStep 3944999 = 5917499) B5917499
theorem B2629999 : Blo 2077435 2629999 := bstep (se 1 (by rfl) ⟨1972499, by rfl⟩ : syracuseStep 2629999 = 3944999) B3944999
theorem B3506665 : Blo 2077435 3506665 := bstep (se 2 (by rfl) ⟨1314999, by rfl⟩ : syracuseStep 3506665 = 2629999) B2629999
theorem B4675553 : Blo 2077435 4675553 := bstep (se 2 (by rfl) ⟨1753332, by rfl⟩ : syracuseStep 4675553 = 3506665) B3506665
theorem B3117035 : Blo 2077435 3117035 := bstep (se 1 (by rfl) ⟨2337776, by rfl⟩ : syracuseStep 3117035 = 4675553) B4675553
theorem B2078023 : Blo 2077435 2078023 := bstep (se 1 (by rfl) ⟨1558517, by rfl⟩ : syracuseStep 2078023 = 3117035) B3117035
theorem B2337781 : Blo 2077435 2337781 := bbase (se 5 (by rfl) ⟨109583, by rfl⟩ : syracuseStep 2337781 = 219167) (by norm_num)
theorem B3117041 : Blo 2077435 3117041 := bstep (se 2 (by rfl) ⟨1168890, by rfl⟩ : syracuseStep 3117041 = 2337781) B2337781
theorem B2078027 : Blo 2077435 2078027 := bstep (se 1 (by rfl) ⟨1558520, by rfl⟩ : syracuseStep 2078027 = 3117041) B3117041
theorem B2630009 : Blo 2077435 2630009 := bbase (se 2 (by rfl) ⟨986253, by rfl⟩ : syracuseStep 2630009 = 1972507) (by norm_num)
theorem B7013357 : Blo 2077435 7013357 := bstep (se 3 (by rfl) ⟨1315004, by rfl⟩ : syracuseStep 7013357 = 2630009) B2630009
theorem B4675571 : Blo 2077435 4675571 := bstep (se 1 (by rfl) ⟨3506678, by rfl⟩ : syracuseStep 4675571 = 7013357) B7013357
theorem B3117047 : Blo 2077435 3117047 := bstep (se 1 (by rfl) ⟨2337785, by rfl⟩ : syracuseStep 3117047 = 4675571) B4675571
theorem B2078031 : Blo 2077435 2078031 := bstep (se 1 (by rfl) ⟨1558523, by rfl⟩ : syracuseStep 2078031 = 3117047) B3117047
theorem B3117053 : Blo 2077435 3117053 := bbase (se 3 (by rfl) ⟨584447, by rfl⟩ : syracuseStep 3117053 = 1168895) (by norm_num)
theorem B2078035 : Blo 2077435 2078035 := bstep (se 1 (by rfl) ⟨1558526, by rfl⟩ : syracuseStep 2078035 = 3117053) B3117053
theorem B4675589 : Blo 2077435 4675589 := bbase (se 4 (by rfl) ⟨438336, by rfl⟩ : syracuseStep 4675589 = 876673) (by norm_num)
theorem B3117059 : Blo 2077435 3117059 := bstep (se 1 (by rfl) ⟨2337794, by rfl⟩ : syracuseStep 3117059 = 4675589) B4675589
theorem B2078039 : Blo 2077435 2078039 := bstep (se 1 (by rfl) ⟨1558529, by rfl⟩ : syracuseStep 2078039 = 3117059) B3117059
theorem B3945037 : Blo 2077435 3945037 := bbase (se 3 (by rfl) ⟨739694, by rfl⟩ : syracuseStep 3945037 = 1479389) (by norm_num)
theorem B5260049 : Blo 2077435 5260049 := bstep (se 2 (by rfl) ⟨1972518, by rfl⟩ : syracuseStep 5260049 = 3945037) B3945037
theorem B3506699 : Blo 2077435 3506699 := bstep (se 1 (by rfl) ⟨2630024, by rfl⟩ : syracuseStep 3506699 = 5260049) B5260049
theorem B2337799 : Blo 2077435 2337799 := bstep (se 1 (by rfl) ⟨1753349, by rfl⟩ : syracuseStep 2337799 = 3506699) B3506699
theorem B3117065 : Blo 2077435 3117065 := bstep (se 2 (by rfl) ⟨1168899, by rfl⟩ : syracuseStep 3117065 = 2337799) B2337799
theorem B2078043 : Blo 2077435 2078043 := bstep (se 1 (by rfl) ⟨1558532, by rfl⟩ : syracuseStep 2078043 = 3117065) B3117065
theorem B10520117 : Blo 2077435 10520117 := bbase (se 5 (by rfl) ⟨493130, by rfl⟩ : syracuseStep 10520117 = 986261) (by norm_num)
theorem B7013411 : Blo 2077435 7013411 := bstep (se 1 (by rfl) ⟨5260058, by rfl⟩ : syracuseStep 7013411 = 10520117) B10520117
theorem B4675607 : Blo 2077435 4675607 := bstep (se 1 (by rfl) ⟨3506705, by rfl⟩ : syracuseStep 4675607 = 7013411) B7013411
theorem B3117071 : Blo 2077435 3117071 := bstep (se 1 (by rfl) ⟨2337803, by rfl⟩ : syracuseStep 3117071 = 4675607) B4675607
theorem B2078047 : Blo 2077435 2078047 := bstep (se 1 (by rfl) ⟨1558535, by rfl⟩ : syracuseStep 2078047 = 3117071) B3117071
theorem B3117077 : Blo 2077435 3117077 := bbase (se 6 (by rfl) ⟨73056, by rfl⟩ : syracuseStep 3117077 = 146113) (by norm_num)
theorem B2078051 : Blo 2077435 2078051 := bstep (se 1 (by rfl) ⟨1558538, by rfl⟩ : syracuseStep 2078051 = 3117077) B3117077
theorem B3744725 : Blo 2077435 3744725 := bbase (se 7 (by rfl) ⟨43883, by rfl⟩ : syracuseStep 3744725 = 87767) (by norm_num)
theorem B9985933 : Blo 2077435 9985933 := bstep (se 3 (by rfl) ⟨1872362, by rfl⟩ : syracuseStep 9985933 = 3744725) B3744725
theorem B13314577 : Blo 2077435 13314577 := bstep (se 2 (by rfl) ⟨4992966, by rfl⟩ : syracuseStep 13314577 = 9985933) B9985933
theorem B17752769 : Blo 2077435 17752769 := bstep (se 2 (by rfl) ⟨6657288, by rfl⟩ : syracuseStep 17752769 = 13314577) B13314577
theorem B11835179 : Blo 2077435 11835179 := bstep (se 1 (by rfl) ⟨8876384, by rfl⟩ : syracuseStep 11835179 = 17752769) B17752769
theorem B7890119 : Blo 2077435 7890119 := bstep (se 1 (by rfl) ⟨5917589, by rfl⟩ : syracuseStep 7890119 = 11835179) B11835179
theorem B5260079 : Blo 2077435 5260079 := bstep (se 1 (by rfl) ⟨3945059, by rfl⟩ : syracuseStep 5260079 = 7890119) B7890119
theorem B3506719 : Blo 2077435 3506719 := bstep (se 1 (by rfl) ⟨2630039, by rfl⟩ : syracuseStep 3506719 = 5260079) B5260079
theorem B4675625 : Blo 2077435 4675625 := bstep (se 2 (by rfl) ⟨1753359, by rfl⟩ : syracuseStep 4675625 = 3506719) B3506719
theorem B3117083 : Blo 2077435 3117083 := bstep (se 1 (by rfl) ⟨2337812, by rfl⟩ : syracuseStep 3117083 = 4675625) B4675625
theorem B2078055 : Blo 2077435 2078055 := bstep (se 1 (by rfl) ⟨1558541, by rfl⟩ : syracuseStep 2078055 = 3117083) B3117083
theorem B2337817 : Blo 2077435 2337817 := bbase (se 2 (by rfl) ⟨876681, by rfl⟩ : syracuseStep 2337817 = 1753363) (by norm_num)
theorem B3117089 : Blo 2077435 3117089 := bstep (se 2 (by rfl) ⟨1168908, by rfl⟩ : syracuseStep 3117089 = 2337817) B2337817
theorem B2078059 : Blo 2077435 2078059 := bstep (se 1 (by rfl) ⟨1558544, by rfl⟩ : syracuseStep 2078059 = 3117089) B3117089
theorem B7890149 : Blo 2077435 7890149 := bbase (se 4 (by rfl) ⟨739701, by rfl⟩ : syracuseStep 7890149 = 1479403) (by norm_num)
theorem B5260099 : Blo 2077435 5260099 := bstep (se 1 (by rfl) ⟨3945074, by rfl⟩ : syracuseStep 5260099 = 7890149) B7890149
theorem B7013465 : Blo 2077435 7013465 := bstep (se 2 (by rfl) ⟨2630049, by rfl⟩ : syracuseStep 7013465 = 5260099) B5260099
theorem B4675643 : Blo 2077435 4675643 := bstep (se 1 (by rfl) ⟨3506732, by rfl⟩ : syracuseStep 4675643 = 7013465) B7013465
theorem B3117095 : Blo 2077435 3117095 := bstep (se 1 (by rfl) ⟨2337821, by rfl⟩ : syracuseStep 3117095 = 4675643) B4675643
theorem B2078063 : Blo 2077435 2078063 := bstep (se 1 (by rfl) ⟨1558547, by rfl⟩ : syracuseStep 2078063 = 3117095) B3117095
theorem B3117101 : Blo 2077435 3117101 := bbase (se 3 (by rfl) ⟨584456, by rfl⟩ : syracuseStep 3117101 = 1168913) (by norm_num)
theorem B2078067 : Blo 2077435 2078067 := bstep (se 1 (by rfl) ⟨1558550, by rfl⟩ : syracuseStep 2078067 = 3117101) B3117101
theorem B4675661 : Blo 2077435 4675661 := bbase (se 3 (by rfl) ⟨876686, by rfl⟩ : syracuseStep 4675661 = 1753373) (by norm_num)
theorem B3117107 : Blo 2077435 3117107 := bstep (se 1 (by rfl) ⟨2337830, by rfl⟩ : syracuseStep 3117107 = 4675661) B4675661
theorem B2078071 : Blo 2077435 2078071 := bstep (se 1 (by rfl) ⟨1558553, by rfl⟩ : syracuseStep 2078071 = 3117107) B3117107
theorem B2630065 : Blo 2077435 2630065 := bbase (se 2 (by rfl) ⟨986274, by rfl⟩ : syracuseStep 2630065 = 1972549) (by norm_num)
theorem B3506753 : Blo 2077435 3506753 := bstep (se 2 (by rfl) ⟨1315032, by rfl⟩ : syracuseStep 3506753 = 2630065) B2630065
theorem B2337835 : Blo 2077435 2337835 := bstep (se 1 (by rfl) ⟨1753376, by rfl⟩ : syracuseStep 2337835 = 3506753) B3506753
theorem B3117113 : Blo 2077435 3117113 := bstep (se 2 (by rfl) ⟨1168917, by rfl⟩ : syracuseStep 3117113 = 2337835) B2337835
theorem B2078075 : Blo 2077435 2078075 := bstep (se 1 (by rfl) ⟨1558556, by rfl⟩ : syracuseStep 2078075 = 3117113) B3117113
theorem B6657365 : Blo 2077435 6657365 := bbase (se 14 (by rfl) ⟨609, by rfl⟩ : syracuseStep 6657365 = 1219) (by norm_num)
theorem B4438243 : Blo 2077435 4438243 := bstep (se 1 (by rfl) ⟨3328682, by rfl⟩ : syracuseStep 4438243 = 6657365) B6657365
theorem B23670629 : Blo 2077435 23670629 := bstep (se 4 (by rfl) ⟨2219121, by rfl⟩ : syracuseStep 23670629 = 4438243) B4438243
theorem B15780419 : Blo 2077435 15780419 := bstep (se 1 (by rfl) ⟨11835314, by rfl⟩ : syracuseStep 15780419 = 23670629) B23670629
theorem B10520279 : Blo 2077435 10520279 := bstep (se 1 (by rfl) ⟨7890209, by rfl⟩ : syracuseStep 10520279 = 15780419) B15780419
theorem B7013519 : Blo 2077435 7013519 := bstep (se 1 (by rfl) ⟨5260139, by rfl⟩ : syracuseStep 7013519 = 10520279) B10520279
theorem B4675679 : Blo 2077435 4675679 := bstep (se 1 (by rfl) ⟨3506759, by rfl⟩ : syracuseStep 4675679 = 7013519) B7013519
theorem B3117119 : Blo 2077435 3117119 := bstep (se 1 (by rfl) ⟨2337839, by rfl⟩ : syracuseStep 3117119 = 4675679) B4675679
theorem B2078079 : Blo 2077435 2078079 := bstep (se 1 (by rfl) ⟨1558559, by rfl⟩ : syracuseStep 2078079 = 3117119) B3117119
theorem B3117125 : Blo 2077435 3117125 := bbase (se 4 (by rfl) ⟨292230, by rfl⟩ : syracuseStep 3117125 = 584461) (by norm_num)
theorem B2078083 : Blo 2077435 2078083 := bstep (se 1 (by rfl) ⟨1558562, by rfl⟩ : syracuseStep 2078083 = 3117125) B3117125
theorem B3506773 : Blo 2077435 3506773 := bbase (se 8 (by rfl) ⟨20547, by rfl⟩ : syracuseStep 3506773 = 41095) (by norm_num)
theorem B4675697 : Blo 2077435 4675697 := bstep (se 2 (by rfl) ⟨1753386, by rfl⟩ : syracuseStep 4675697 = 3506773) B3506773
theorem B3117131 : Blo 2077435 3117131 := bstep (se 1 (by rfl) ⟨2337848, by rfl⟩ : syracuseStep 3117131 = 4675697) B4675697
theorem B2078087 : Blo 2077435 2078087 := bstep (se 1 (by rfl) ⟨1558565, by rfl⟩ : syracuseStep 2078087 = 3117131) B3117131
theorem B2337853 : Blo 2077435 2337853 := bbase (se 3 (by rfl) ⟨438347, by rfl⟩ : syracuseStep 2337853 = 876695) (by norm_num)
theorem B3117137 : Blo 2077435 3117137 := bstep (se 2 (by rfl) ⟨1168926, by rfl⟩ : syracuseStep 3117137 = 2337853) B2337853
theorem B2078091 : Blo 2077435 2078091 := bstep (se 1 (by rfl) ⟨1558568, by rfl⟩ : syracuseStep 2078091 = 3117137) B3117137
theorem B7013573 : Blo 2077435 7013573 := bbase (se 4 (by rfl) ⟨657522, by rfl⟩ : syracuseStep 7013573 = 1315045) (by norm_num)
theorem B4675715 : Blo 2077435 4675715 := bstep (se 1 (by rfl) ⟨3506786, by rfl⟩ : syracuseStep 4675715 = 7013573) B7013573
theorem B3117143 : Blo 2077435 3117143 := bstep (se 1 (by rfl) ⟨2337857, by rfl⟩ : syracuseStep 3117143 = 4675715) B4675715
theorem B2078095 : Blo 2077435 2078095 := bstep (se 1 (by rfl) ⟨1558571, by rfl⟩ : syracuseStep 2078095 = 3117143) B3117143
theorem B3117149 : Blo 2077435 3117149 := bbase (se 3 (by rfl) ⟨584465, by rfl⟩ : syracuseStep 3117149 = 1168931) (by norm_num)
theorem B2078099 : Blo 2077435 2078099 := bstep (se 1 (by rfl) ⟨1558574, by rfl⟩ : syracuseStep 2078099 = 3117149) B3117149
theorem B4675733 : Blo 2077435 4675733 := bbase (se 6 (by rfl) ⟨109587, by rfl⟩ : syracuseStep 4675733 = 219175) (by norm_num)
theorem B3117155 : Blo 2077435 3117155 := bstep (se 1 (by rfl) ⟨2337866, by rfl⟩ : syracuseStep 3117155 = 4675733) B4675733
theorem B2078103 : Blo 2077435 2078103 := bstep (se 1 (by rfl) ⟨1558577, by rfl⟩ : syracuseStep 2078103 = 3117155) B3117155
theorem B2958869 : Blo 2077435 2958869 := bbase (se 6 (by rfl) ⟨69348, by rfl⟩ : syracuseStep 2958869 = 138697) (by norm_num)
theorem B7890317 : Blo 2077435 7890317 := bstep (se 3 (by rfl) ⟨1479434, by rfl⟩ : syracuseStep 7890317 = 2958869) B2958869
theorem B5260211 : Blo 2077435 5260211 := bstep (se 1 (by rfl) ⟨3945158, by rfl⟩ : syracuseStep 5260211 = 7890317) B7890317
theorem B3506807 : Blo 2077435 3506807 := bstep (se 1 (by rfl) ⟨2630105, by rfl⟩ : syracuseStep 3506807 = 5260211) B5260211
theorem B2337871 : Blo 2077435 2337871 := bstep (se 1 (by rfl) ⟨1753403, by rfl⟩ : syracuseStep 2337871 = 3506807) B3506807
theorem B3117161 : Blo 2077435 3117161 := bstep (se 2 (by rfl) ⟨1168935, by rfl⟩ : syracuseStep 3117161 = 2337871) B2337871
theorem B2078107 : Blo 2077435 2078107 := bstep (se 1 (by rfl) ⟨1558580, by rfl⟩ : syracuseStep 2078107 = 3117161) B3117161
theorem B2369773 : Blo 2077435 2369773 := bbase (se 3 (by rfl) ⟨444332, by rfl⟩ : syracuseStep 2369773 = 888665) (by norm_num)
theorem B3159697 : Blo 2077435 3159697 := bstep (se 2 (by rfl) ⟨1184886, by rfl⟩ : syracuseStep 3159697 = 2369773) B2369773
theorem B4212929 : Blo 2077435 4212929 := bstep (se 2 (by rfl) ⟨1579848, by rfl⟩ : syracuseStep 4212929 = 3159697) B3159697
theorem B11234477 : Blo 2077435 11234477 := bstep (se 3 (by rfl) ⟨2106464, by rfl⟩ : syracuseStep 11234477 = 4212929) B4212929
theorem B29958605 : Blo 2077435 29958605 := bstep (se 3 (by rfl) ⟨5617238, by rfl⟩ : syracuseStep 29958605 = 11234477) B11234477
theorem B19972403 : Blo 2077435 19972403 := bstep (se 1 (by rfl) ⟨14979302, by rfl⟩ : syracuseStep 19972403 = 29958605) B29958605
theorem B13314935 : Blo 2077435 13314935 := bstep (se 1 (by rfl) ⟨9986201, by rfl⟩ : syracuseStep 13314935 = 19972403) B19972403
theorem B8876623 : Blo 2077435 8876623 := bstep (se 1 (by rfl) ⟨6657467, by rfl⟩ : syracuseStep 8876623 = 13314935) B13314935
theorem B11835497 : Blo 2077435 11835497 := bstep (se 2 (by rfl) ⟨4438311, by rfl⟩ : syracuseStep 11835497 = 8876623) B8876623
theorem B7890331 : Blo 2077435 7890331 := bstep (se 1 (by rfl) ⟨5917748, by rfl⟩ : syracuseStep 7890331 = 11835497) B11835497
theorem B10520441 : Blo 2077435 10520441 := bstep (se 2 (by rfl) ⟨3945165, by rfl⟩ : syracuseStep 10520441 = 7890331) B7890331
theorem B7013627 : Blo 2077435 7013627 := bstep (se 1 (by rfl) ⟨5260220, by rfl⟩ : syracuseStep 7013627 = 10520441) B10520441
theorem B4675751 : Blo 2077435 4675751 := bstep (se 1 (by rfl) ⟨3506813, by rfl⟩ : syracuseStep 4675751 = 7013627) B7013627
theorem B3117167 : Blo 2077435 3117167 := bstep (se 1 (by rfl) ⟨2337875, by rfl⟩ : syracuseStep 3117167 = 4675751) B4675751
theorem B2078111 : Blo 2077435 2078111 := bstep (se 1 (by rfl) ⟨1558583, by rfl⟩ : syracuseStep 2078111 = 3117167) B3117167
theorem B3117173 : Blo 2077435 3117173 := bbase (se 5 (by rfl) ⟨146117, by rfl⟩ : syracuseStep 3117173 = 292235) (by norm_num)
theorem B2078115 : Blo 2077435 2078115 := bstep (se 1 (by rfl) ⟨1558586, by rfl⟩ : syracuseStep 2078115 = 3117173) B3117173
theorem B3945181 : Blo 2077435 3945181 := bbase (se 3 (by rfl) ⟨739721, by rfl⟩ : syracuseStep 3945181 = 1479443) (by norm_num)
theorem B5260241 : Blo 2077435 5260241 := bstep (se 2 (by rfl) ⟨1972590, by rfl⟩ : syracuseStep 5260241 = 3945181) B3945181
theorem B3506827 : Blo 2077435 3506827 := bstep (se 1 (by rfl) ⟨2630120, by rfl⟩ : syracuseStep 3506827 = 5260241) B5260241
theorem B4675769 : Blo 2077435 4675769 := bstep (se 2 (by rfl) ⟨1753413, by rfl⟩ : syracuseStep 4675769 = 3506827) B3506827
theorem B3117179 : Blo 2077435 3117179 := bstep (se 1 (by rfl) ⟨2337884, by rfl⟩ : syracuseStep 3117179 = 4675769) B4675769
theorem B2078119 : Blo 2077435 2078119 := bstep (se 1 (by rfl) ⟨1558589, by rfl⟩ : syracuseStep 2078119 = 3117179) B3117179
theorem B2337889 : Blo 2077435 2337889 := bbase (se 2 (by rfl) ⟨876708, by rfl⟩ : syracuseStep 2337889 = 1753417) (by norm_num)
theorem B3117185 : Blo 2077435 3117185 := bstep (se 2 (by rfl) ⟨1168944, by rfl⟩ : syracuseStep 3117185 = 2337889) B2337889
theorem B2078123 : Blo 2077435 2078123 := bstep (se 1 (by rfl) ⟨1558592, by rfl⟩ : syracuseStep 2078123 = 3117185) B3117185
theorem B5260261 : Blo 2077435 5260261 := bbase (se 4 (by rfl) ⟨493149, by rfl⟩ : syracuseStep 5260261 = 986299) (by norm_num)
theorem B7013681 : Blo 2077435 7013681 := bstep (se 2 (by rfl) ⟨2630130, by rfl⟩ : syracuseStep 7013681 = 5260261) B5260261
theorem B4675787 : Blo 2077435 4675787 := bstep (se 1 (by rfl) ⟨3506840, by rfl⟩ : syracuseStep 4675787 = 7013681) B7013681
theorem B3117191 : Blo 2077435 3117191 := bstep (se 1 (by rfl) ⟨2337893, by rfl⟩ : syracuseStep 3117191 = 4675787) B4675787
theorem B2078127 : Blo 2077435 2078127 := bstep (se 1 (by rfl) ⟨1558595, by rfl⟩ : syracuseStep 2078127 = 3117191) B3117191
theorem B3117197 : Blo 2077435 3117197 := bbase (se 3 (by rfl) ⟨584474, by rfl⟩ : syracuseStep 3117197 = 1168949) (by norm_num)
theorem B2078131 : Blo 2077435 2078131 := bstep (se 1 (by rfl) ⟨1558598, by rfl⟩ : syracuseStep 2078131 = 3117197) B3117197
theorem B4675805 : Blo 2077435 4675805 := bbase (se 3 (by rfl) ⟨876713, by rfl⟩ : syracuseStep 4675805 = 1753427) (by norm_num)
theorem B3117203 : Blo 2077435 3117203 := bstep (se 1 (by rfl) ⟨2337902, by rfl⟩ : syracuseStep 3117203 = 4675805) B4675805
theorem B2078135 : Blo 2077435 2078135 := bstep (se 1 (by rfl) ⟨1558601, by rfl⟩ : syracuseStep 2078135 = 3117203) B3117203
theorem B3506861 : Blo 2077435 3506861 := bbase (se 3 (by rfl) ⟨657536, by rfl⟩ : syracuseStep 3506861 = 1315073) (by norm_num)
theorem B2337907 : Blo 2077435 2337907 := bstep (se 1 (by rfl) ⟨1753430, by rfl⟩ : syracuseStep 2337907 = 3506861) B3506861
theorem B3117209 : Blo 2077435 3117209 := bstep (se 2 (by rfl) ⟨1168953, by rfl⟩ : syracuseStep 3117209 = 2337907) B2337907
theorem B2078139 : Blo 2077435 2078139 := bstep (se 1 (by rfl) ⟨1558604, by rfl⟩ : syracuseStep 2078139 = 3117209) B3117209
theorem B2369809 : Blo 2077435 2369809 := bbase (se 2 (by rfl) ⟨888678, by rfl⟩ : syracuseStep 2369809 = 1777357) (by norm_num)
theorem B12638981 : Blo 2077435 12638981 := bstep (se 4 (by rfl) ⟨1184904, by rfl⟩ : syracuseStep 12638981 = 2369809) B2369809
theorem B8425987 : Blo 2077435 8425987 := bstep (se 1 (by rfl) ⟨6319490, by rfl⟩ : syracuseStep 8425987 = 12638981) B12638981
theorem B44938597 : Blo 2077435 44938597 := bstep (se 4 (by rfl) ⟨4212993, by rfl⟩ : syracuseStep 44938597 = 8425987) B8425987
theorem B59918129 : Blo 2077435 59918129 := bstep (se 2 (by rfl) ⟨22469298, by rfl⟩ : syracuseStep 59918129 = 44938597) B44938597
theorem B39945419 : Blo 2077435 39945419 := bstep (se 1 (by rfl) ⟨29959064, by rfl⟩ : syracuseStep 39945419 = 59918129) B59918129
theorem B26630279 : Blo 2077435 26630279 := bstep (se 1 (by rfl) ⟨19972709, by rfl⟩ : syracuseStep 26630279 = 39945419) B39945419
theorem B17753519 : Blo 2077435 17753519 := bstep (se 1 (by rfl) ⟨13315139, by rfl⟩ : syracuseStep 17753519 = 26630279) B26630279
theorem B11835679 : Blo 2077435 11835679 := bstep (se 1 (by rfl) ⟨8876759, by rfl⟩ : syracuseStep 11835679 = 17753519) B17753519
theorem B15780905 : Blo 2077435 15780905 := bstep (se 2 (by rfl) ⟨5917839, by rfl⟩ : syracuseStep 15780905 = 11835679) B11835679
theorem B10520603 : Blo 2077435 10520603 := bstep (se 1 (by rfl) ⟨7890452, by rfl⟩ : syracuseStep 10520603 = 15780905) B15780905
theorem B7013735 : Blo 2077435 7013735 := bstep (se 1 (by rfl) ⟨5260301, by rfl⟩ : syracuseStep 7013735 = 10520603) B10520603
theorem B4675823 : Blo 2077435 4675823 := bstep (se 1 (by rfl) ⟨3506867, by rfl⟩ : syracuseStep 4675823 = 7013735) B7013735
theorem B3117215 : Blo 2077435 3117215 := bstep (se 1 (by rfl) ⟨2337911, by rfl⟩ : syracuseStep 3117215 = 4675823) B4675823
theorem B2078143 : Blo 2077435 2078143 := bstep (se 1 (by rfl) ⟨1558607, by rfl⟩ : syracuseStep 2078143 = 3117215) B3117215
theorem B3117221 : Blo 2077435 3117221 := bbase (se 4 (by rfl) ⟨292239, by rfl⟩ : syracuseStep 3117221 = 584479) (by norm_num)
theorem B2078147 : Blo 2077435 2078147 := bstep (se 1 (by rfl) ⟨1558610, by rfl⟩ : syracuseStep 2078147 = 3117221) B3117221
theorem B2630161 : Blo 2077435 2630161 := bbase (se 2 (by rfl) ⟨986310, by rfl⟩ : syracuseStep 2630161 = 1972621) (by norm_num)
theorem B3506881 : Blo 2077435 3506881 := bstep (se 2 (by rfl) ⟨1315080, by rfl⟩ : syracuseStep 3506881 = 2630161) B2630161
theorem B4675841 : Blo 2077435 4675841 := bstep (se 2 (by rfl) ⟨1753440, by rfl⟩ : syracuseStep 4675841 = 3506881) B3506881
theorem B3117227 : Blo 2077435 3117227 := bstep (se 1 (by rfl) ⟨2337920, by rfl⟩ : syracuseStep 3117227 = 4675841) B4675841
theorem B2078151 : Blo 2077435 2078151 := bstep (se 1 (by rfl) ⟨1558613, by rfl⟩ : syracuseStep 2078151 = 3117227) B3117227
theorem B2337925 : Blo 2077435 2337925 := bbase (se 4 (by rfl) ⟨219180, by rfl⟩ : syracuseStep 2337925 = 438361) (by norm_num)
theorem B3117233 : Blo 2077435 3117233 := bstep (se 2 (by rfl) ⟨1168962, by rfl⟩ : syracuseStep 3117233 = 2337925) B2337925
theorem B2078155 : Blo 2077435 2078155 := bstep (se 1 (by rfl) ⟨1558616, by rfl⟩ : syracuseStep 2078155 = 3117233) B3117233
theorem B2808685 : Blo 2077435 2808685 := bbase (se 3 (by rfl) ⟨526628, by rfl⟩ : syracuseStep 2808685 = 1053257) (by norm_num)
theorem B14979653 : Blo 2077435 14979653 := bstep (se 4 (by rfl) ⟨1404342, by rfl⟩ : syracuseStep 14979653 = 2808685) B2808685
theorem B9986435 : Blo 2077435 9986435 := bstep (se 1 (by rfl) ⟨7489826, by rfl⟩ : syracuseStep 9986435 = 14979653) B14979653
theorem B6657623 : Blo 2077435 6657623 := bstep (se 1 (by rfl) ⟨4993217, by rfl⟩ : syracuseStep 6657623 = 9986435) B9986435
theorem B4438415 : Blo 2077435 4438415 := bstep (se 1 (by rfl) ⟨3328811, by rfl⟩ : syracuseStep 4438415 = 6657623) B6657623
theorem B2958943 : Blo 2077435 2958943 := bstep (se 1 (by rfl) ⟨2219207, by rfl⟩ : syracuseStep 2958943 = 4438415) B4438415
theorem B3945257 : Blo 2077435 3945257 := bstep (se 2 (by rfl) ⟨1479471, by rfl⟩ : syracuseStep 3945257 = 2958943) B2958943
theorem B2630171 : Blo 2077435 2630171 := bstep (se 1 (by rfl) ⟨1972628, by rfl⟩ : syracuseStep 2630171 = 3945257) B3945257
theorem B7013789 : Blo 2077435 7013789 := bstep (se 3 (by rfl) ⟨1315085, by rfl⟩ : syracuseStep 7013789 = 2630171) B2630171
theorem B4675859 : Blo 2077435 4675859 := bstep (se 1 (by rfl) ⟨3506894, by rfl⟩ : syracuseStep 4675859 = 7013789) B7013789
theorem B3117239 : Blo 2077435 3117239 := bstep (se 1 (by rfl) ⟨2337929, by rfl⟩ : syracuseStep 3117239 = 4675859) B4675859
theorem B2078159 : Blo 2077435 2078159 := bstep (se 1 (by rfl) ⟨1558619, by rfl⟩ : syracuseStep 2078159 = 3117239) B3117239
theorem B3117245 : Blo 2077435 3117245 := bbase (se 3 (by rfl) ⟨584483, by rfl⟩ : syracuseStep 3117245 = 1168967) (by norm_num)
theorem B2078163 : Blo 2077435 2078163 := bstep (se 1 (by rfl) ⟨1558622, by rfl⟩ : syracuseStep 2078163 = 3117245) B3117245
theorem B4675877 : Blo 2077435 4675877 := bbase (se 4 (by rfl) ⟨438363, by rfl⟩ : syracuseStep 4675877 = 876727) (by norm_num)
theorem B3117251 : Blo 2077435 3117251 := bstep (se 1 (by rfl) ⟨2337938, by rfl⟩ : syracuseStep 3117251 = 4675877) B4675877
theorem B2078167 : Blo 2077435 2078167 := bstep (se 1 (by rfl) ⟨1558625, by rfl⟩ : syracuseStep 2078167 = 3117251) B3117251
theorem B5260373 : Blo 2077435 5260373 := bbase (se 8 (by rfl) ⟨30822, by rfl⟩ : syracuseStep 5260373 = 61645) (by norm_num)
theorem B3506915 : Blo 2077435 3506915 := bstep (se 1 (by rfl) ⟨2630186, by rfl⟩ : syracuseStep 3506915 = 5260373) B5260373
theorem B2337943 : Blo 2077435 2337943 := bstep (se 1 (by rfl) ⟨1753457, by rfl⟩ : syracuseStep 2337943 = 3506915) B3506915
theorem B3117257 : Blo 2077435 3117257 := bstep (se 2 (by rfl) ⟨1168971, by rfl⟩ : syracuseStep 3117257 = 2337943) B2337943
theorem B2078171 : Blo 2077435 2078171 := bstep (se 1 (by rfl) ⟨1558628, by rfl⟩ : syracuseStep 2078171 = 3117257) B3117257
theorem B2666077 : Blo 2077435 2666077 := bbase (se 3 (by rfl) ⟨499889, by rfl⟩ : syracuseStep 2666077 = 999779) (by norm_num)
theorem B14219077 : Blo 2077435 14219077 := bstep (se 4 (by rfl) ⟨1333038, by rfl⟩ : syracuseStep 14219077 = 2666077) B2666077
theorem B18958769 : Blo 2077435 18958769 := bstep (se 2 (by rfl) ⟨7109538, by rfl⟩ : syracuseStep 18958769 = 14219077) B14219077
theorem B12639179 : Blo 2077435 12639179 := bstep (se 1 (by rfl) ⟨9479384, by rfl⟩ : syracuseStep 12639179 = 18958769) B18958769
theorem B8426119 : Blo 2077435 8426119 := bstep (se 1 (by rfl) ⟨6319589, by rfl⟩ : syracuseStep 8426119 = 12639179) B12639179
theorem B11234825 : Blo 2077435 11234825 := bstep (se 2 (by rfl) ⟨4213059, by rfl⟩ : syracuseStep 11234825 = 8426119) B8426119
theorem B7489883 : Blo 2077435 7489883 := bstep (se 1 (by rfl) ⟨5617412, by rfl⟩ : syracuseStep 7489883 = 11234825) B11234825
theorem B4993255 : Blo 2077435 4993255 := bstep (se 1 (by rfl) ⟨3744941, by rfl⟩ : syracuseStep 4993255 = 7489883) B7489883
theorem B6657673 : Blo 2077435 6657673 := bstep (se 2 (by rfl) ⟨2496627, by rfl⟩ : syracuseStep 6657673 = 4993255) B4993255
theorem B8876897 : Blo 2077435 8876897 := bstep (se 2 (by rfl) ⟨3328836, by rfl⟩ : syracuseStep 8876897 = 6657673) B6657673
theorem B5917931 : Blo 2077435 5917931 := bstep (se 1 (by rfl) ⟨4438448, by rfl⟩ : syracuseStep 5917931 = 8876897) B8876897
theorem B3945287 : Blo 2077435 3945287 := bstep (se 1 (by rfl) ⟨2958965, by rfl⟩ : syracuseStep 3945287 = 5917931) B5917931
theorem B10520765 : Blo 2077435 10520765 := bstep (se 3 (by rfl) ⟨1972643, by rfl⟩ : syracuseStep 10520765 = 3945287) B3945287
theorem B7013843 : Blo 2077435 7013843 := bstep (se 1 (by rfl) ⟨5260382, by rfl⟩ : syracuseStep 7013843 = 10520765) B10520765
theorem B4675895 : Blo 2077435 4675895 := bstep (se 1 (by rfl) ⟨3506921, by rfl⟩ : syracuseStep 4675895 = 7013843) B7013843
theorem B3117263 : Blo 2077435 3117263 := bstep (se 1 (by rfl) ⟨2337947, by rfl⟩ : syracuseStep 3117263 = 4675895) B4675895
theorem B2078175 : Blo 2077435 2078175 := bstep (se 1 (by rfl) ⟨1558631, by rfl⟩ : syracuseStep 2078175 = 3117263) B3117263
theorem B3117269 : Blo 2077435 3117269 := bbase (se 7 (by rfl) ⟨36530, by rfl⟩ : syracuseStep 3117269 = 73061) (by norm_num)
theorem B2078179 : Blo 2077435 2078179 := bstep (se 1 (by rfl) ⟨1558634, by rfl⟩ : syracuseStep 2078179 = 3117269) B3117269
theorem B2219233 : Blo 2077435 2219233 := bbase (se 2 (by rfl) ⟨832212, by rfl⟩ : syracuseStep 2219233 = 1664425) (by norm_num)
theorem B2958977 : Blo 2077435 2958977 := bstep (se 2 (by rfl) ⟨1109616, by rfl⟩ : syracuseStep 2958977 = 2219233) B2219233
theorem B7890605 : Blo 2077435 7890605 := bstep (se 3 (by rfl) ⟨1479488, by rfl⟩ : syracuseStep 7890605 = 2958977) B2958977
theorem B5260403 : Blo 2077435 5260403 := bstep (se 1 (by rfl) ⟨3945302, by rfl⟩ : syracuseStep 5260403 = 7890605) B7890605
theorem B3506935 : Blo 2077435 3506935 := bstep (se 1 (by rfl) ⟨2630201, by rfl⟩ : syracuseStep 3506935 = 5260403) B5260403
theorem B4675913 : Blo 2077435 4675913 := bstep (se 2 (by rfl) ⟨1753467, by rfl⟩ : syracuseStep 4675913 = 3506935) B3506935
theorem B3117275 : Blo 2077435 3117275 := bstep (se 1 (by rfl) ⟨2337956, by rfl⟩ : syracuseStep 3117275 = 4675913) B4675913
theorem B2078183 : Blo 2077435 2078183 := bstep (se 1 (by rfl) ⟨1558637, by rfl⟩ : syracuseStep 2078183 = 3117275) B3117275
theorem B2337961 : Blo 2077435 2337961 := bbase (se 2 (by rfl) ⟨876735, by rfl⟩ : syracuseStep 2337961 = 1753471) (by norm_num)
theorem B3117281 : Blo 2077435 3117281 := bstep (se 2 (by rfl) ⟨1168980, by rfl⟩ : syracuseStep 3117281 = 2337961) B2337961
theorem B2078187 : Blo 2077435 2078187 := bstep (se 1 (by rfl) ⟨1558640, by rfl⟩ : syracuseStep 2078187 = 3117281) B3117281
theorem B8876965 : Blo 2077435 8876965 := bbase (se 4 (by rfl) ⟨832215, by rfl⟩ : syracuseStep 8876965 = 1664431) (by norm_num)
theorem B11835953 : Blo 2077435 11835953 := bstep (se 2 (by rfl) ⟨4438482, by rfl⟩ : syracuseStep 11835953 = 8876965) B8876965
theorem B7890635 : Blo 2077435 7890635 := bstep (se 1 (by rfl) ⟨5917976, by rfl⟩ : syracuseStep 7890635 = 11835953) B11835953
theorem B5260423 : Blo 2077435 5260423 := bstep (se 1 (by rfl) ⟨3945317, by rfl⟩ : syracuseStep 5260423 = 7890635) B7890635
theorem B7013897 : Blo 2077435 7013897 := bstep (se 2 (by rfl) ⟨2630211, by rfl⟩ : syracuseStep 7013897 = 5260423) B5260423
theorem B4675931 : Blo 2077435 4675931 := bstep (se 1 (by rfl) ⟨3506948, by rfl⟩ : syracuseStep 4675931 = 7013897) B7013897
theorem B3117287 : Blo 2077435 3117287 := bstep (se 1 (by rfl) ⟨2337965, by rfl⟩ : syracuseStep 3117287 = 4675931) B4675931
theorem B2078191 : Blo 2077435 2078191 := bstep (se 1 (by rfl) ⟨1558643, by rfl⟩ : syracuseStep 2078191 = 3117287) B3117287
theorem B3117293 : Blo 2077435 3117293 := bbase (se 3 (by rfl) ⟨584492, by rfl⟩ : syracuseStep 3117293 = 1168985) (by norm_num)
theorem B2078195 : Blo 2077435 2078195 := bstep (se 1 (by rfl) ⟨1558646, by rfl⟩ : syracuseStep 2078195 = 3117293) B3117293
theorem B4675949 : Blo 2077435 4675949 := bbase (se 3 (by rfl) ⟨876740, by rfl⟩ : syracuseStep 4675949 = 1753481) (by norm_num)
theorem B3117299 : Blo 2077435 3117299 := bstep (se 1 (by rfl) ⟨2337974, by rfl⟩ : syracuseStep 3117299 = 4675949) B4675949
theorem B2078199 : Blo 2077435 2078199 := bstep (se 1 (by rfl) ⟨1558649, by rfl⟩ : syracuseStep 2078199 = 3117299) B3117299
theorem B3945341 : Blo 2077435 3945341 := bbase (se 3 (by rfl) ⟨739751, by rfl⟩ : syracuseStep 3945341 = 1479503) (by norm_num)
theorem B2630227 : Blo 2077435 2630227 := bstep (se 1 (by rfl) ⟨1972670, by rfl⟩ : syracuseStep 2630227 = 3945341) B3945341
theorem B3506969 : Blo 2077435 3506969 := bstep (se 2 (by rfl) ⟨1315113, by rfl⟩ : syracuseStep 3506969 = 2630227) B2630227
theorem B2337979 : Blo 2077435 2337979 := bstep (se 1 (by rfl) ⟨1753484, by rfl⟩ : syracuseStep 2337979 = 3506969) B3506969
theorem B3117305 : Blo 2077435 3117305 := bstep (se 2 (by rfl) ⟨1168989, by rfl⟩ : syracuseStep 3117305 = 2337979) B2337979
theorem B2078203 : Blo 2077435 2078203 := bstep (se 1 (by rfl) ⟨1558652, by rfl⟩ : syracuseStep 2078203 = 3117305) B3117305
theorem B2808749 : Blo 2077435 2808749 := bbase (se 3 (by rfl) ⟨526640, by rfl⟩ : syracuseStep 2808749 = 1053281) (by norm_num)
theorem B7489997 : Blo 2077435 7489997 := bstep (se 3 (by rfl) ⟨1404374, by rfl⟩ : syracuseStep 7489997 = 2808749) B2808749
theorem B4993331 : Blo 2077435 4993331 := bstep (se 1 (by rfl) ⟨3744998, by rfl⟩ : syracuseStep 4993331 = 7489997) B7489997
theorem B53262197 : Blo 2077435 53262197 := bstep (se 5 (by rfl) ⟨2496665, by rfl⟩ : syracuseStep 53262197 = 4993331) B4993331
theorem B35508131 : Blo 2077435 35508131 := bstep (se 1 (by rfl) ⟨26631098, by rfl⟩ : syracuseStep 35508131 = 53262197) B53262197
theorem B23672087 : Blo 2077435 23672087 := bstep (se 1 (by rfl) ⟨17754065, by rfl⟩ : syracuseStep 23672087 = 35508131) B35508131
theorem B15781391 : Blo 2077435 15781391 := bstep (se 1 (by rfl) ⟨11836043, by rfl⟩ : syracuseStep 15781391 = 23672087) B23672087
theorem B10520927 : Blo 2077435 10520927 := bstep (se 1 (by rfl) ⟨7890695, by rfl⟩ : syracuseStep 10520927 = 15781391) B15781391
theorem B7013951 : Blo 2077435 7013951 := bstep (se 1 (by rfl) ⟨5260463, by rfl⟩ : syracuseStep 7013951 = 10520927) B10520927
theorem B4675967 : Blo 2077435 4675967 := bstep (se 1 (by rfl) ⟨3506975, by rfl⟩ : syracuseStep 4675967 = 7013951) B7013951
theorem B3117311 : Blo 2077435 3117311 := bstep (se 1 (by rfl) ⟨2337983, by rfl⟩ : syracuseStep 3117311 = 4675967) B4675967
theorem B2078207 : Blo 2077435 2078207 := bstep (se 1 (by rfl) ⟨1558655, by rfl⟩ : syracuseStep 2078207 = 3117311) B3117311
theorem B3117317 : Blo 2077435 3117317 := bbase (se 4 (by rfl) ⟨292248, by rfl⟩ : syracuseStep 3117317 = 584497) (by norm_num)
theorem B2078211 : Blo 2077435 2078211 := bstep (se 1 (by rfl) ⟨1558658, by rfl⟩ : syracuseStep 2078211 = 3117317) B3117317
theorem B3506989 : Blo 2077435 3506989 := bbase (se 3 (by rfl) ⟨657560, by rfl⟩ : syracuseStep 3506989 = 1315121) (by norm_num)
theorem B4675985 : Blo 2077435 4675985 := bstep (se 2 (by rfl) ⟨1753494, by rfl⟩ : syracuseStep 4675985 = 3506989) B3506989
theorem B3117323 : Blo 2077435 3117323 := bstep (se 1 (by rfl) ⟨2337992, by rfl⟩ : syracuseStep 3117323 = 4675985) B4675985
theorem B2078215 : Blo 2077435 2078215 := bstep (se 1 (by rfl) ⟨1558661, by rfl⟩ : syracuseStep 2078215 = 3117323) B3117323
theorem B2337997 : Blo 2077435 2337997 := bbase (se 3 (by rfl) ⟨438374, by rfl⟩ : syracuseStep 2337997 = 876749) (by norm_num)
theorem B3117329 : Blo 2077435 3117329 := bstep (se 2 (by rfl) ⟨1168998, by rfl⟩ : syracuseStep 3117329 = 2337997) B2337997
theorem B2078219 : Blo 2077435 2078219 := bstep (se 1 (by rfl) ⟨1558664, by rfl⟩ : syracuseStep 2078219 = 3117329) B3117329
theorem B7014005 : Blo 2077435 7014005 := bbase (se 5 (by rfl) ⟨328781, by rfl⟩ : syracuseStep 7014005 = 657563) (by norm_num)
theorem B4676003 : Blo 2077435 4676003 := bstep (se 1 (by rfl) ⟨3507002, by rfl⟩ : syracuseStep 4676003 = 7014005) B7014005
theorem B3117335 : Blo 2077435 3117335 := bstep (se 1 (by rfl) ⟨2338001, by rfl⟩ : syracuseStep 3117335 = 4676003) B4676003
theorem B2078223 : Blo 2077435 2078223 := bstep (se 1 (by rfl) ⟨1558667, by rfl⟩ : syracuseStep 2078223 = 3117335) B3117335
theorem B3117341 : Blo 2077435 3117341 := bbase (se 3 (by rfl) ⟨584501, by rfl⟩ : syracuseStep 3117341 = 1169003) (by norm_num)
theorem B2078227 : Blo 2077435 2078227 := bstep (se 1 (by rfl) ⟨1558670, by rfl⟩ : syracuseStep 2078227 = 3117341) B3117341
theorem B4676021 : Blo 2077435 4676021 := bbase (se 5 (by rfl) ⟨219188, by rfl⟩ : syracuseStep 4676021 = 438377) (by norm_num)
theorem B3117347 : Blo 2077435 3117347 := bstep (se 1 (by rfl) ⟨2338010, by rfl⟩ : syracuseStep 3117347 = 4676021) B4676021
theorem B2078231 : Blo 2077435 2078231 := bstep (se 1 (by rfl) ⟨1558673, by rfl⟩ : syracuseStep 2078231 = 3117347) B3117347
theorem B3328933 : Blo 2077435 3328933 := bbase (se 4 (by rfl) ⟨312087, by rfl⟩ : syracuseStep 3328933 = 624175) (by norm_num)
theorem B4438577 : Blo 2077435 4438577 := bstep (se 2 (by rfl) ⟨1664466, by rfl⟩ : syracuseStep 4438577 = 3328933) B3328933
theorem B11836205 : Blo 2077435 11836205 := bstep (se 3 (by rfl) ⟨2219288, by rfl⟩ : syracuseStep 11836205 = 4438577) B4438577
theorem B7890803 : Blo 2077435 7890803 := bstep (se 1 (by rfl) ⟨5918102, by rfl⟩ : syracuseStep 7890803 = 11836205) B11836205
theorem B5260535 : Blo 2077435 5260535 := bstep (se 1 (by rfl) ⟨3945401, by rfl⟩ : syracuseStep 5260535 = 7890803) B7890803
theorem B3507023 : Blo 2077435 3507023 := bstep (se 1 (by rfl) ⟨2630267, by rfl⟩ : syracuseStep 3507023 = 5260535) B5260535
theorem B2338015 : Blo 2077435 2338015 := bstep (se 1 (by rfl) ⟨1753511, by rfl⟩ : syracuseStep 2338015 = 3507023) B3507023
theorem B3117353 : Blo 2077435 3117353 := bstep (se 2 (by rfl) ⟨1169007, by rfl⟩ : syracuseStep 3117353 = 2338015) B2338015
theorem B2078235 : Blo 2077435 2078235 := bstep (se 1 (by rfl) ⟨1558676, by rfl⟩ : syracuseStep 2078235 = 3117353) B3117353
theorem B3159893 : Blo 2077435 3159893 := bbase (se 9 (by rfl) ⟨9257, by rfl⟩ : syracuseStep 3159893 = 18515) (by norm_num)
theorem B2106595 : Blo 2077435 2106595 := bstep (se 1 (by rfl) ⟨1579946, by rfl⟩ : syracuseStep 2106595 = 3159893) B3159893
theorem B2808793 : Blo 2077435 2808793 := bstep (se 2 (by rfl) ⟨1053297, by rfl⟩ : syracuseStep 2808793 = 2106595) B2106595
theorem B3745057 : Blo 2077435 3745057 := bstep (se 2 (by rfl) ⟨1404396, by rfl⟩ : syracuseStep 3745057 = 2808793) B2808793
theorem B4993409 : Blo 2077435 4993409 := bstep (se 2 (by rfl) ⟨1872528, by rfl⟩ : syracuseStep 4993409 = 3745057) B3745057
theorem B3328939 : Blo 2077435 3328939 := bstep (se 1 (by rfl) ⟨2496704, by rfl⟩ : syracuseStep 3328939 = 4993409) B4993409
theorem B4438585 : Blo 2077435 4438585 := bstep (se 2 (by rfl) ⟨1664469, by rfl⟩ : syracuseStep 4438585 = 3328939) B3328939
theorem B5918113 : Blo 2077435 5918113 := bstep (se 2 (by rfl) ⟨2219292, by rfl⟩ : syracuseStep 5918113 = 4438585) B4438585
theorem B7890817 : Blo 2077435 7890817 := bstep (se 2 (by rfl) ⟨2959056, by rfl⟩ : syracuseStep 7890817 = 5918113) B5918113
theorem B10521089 : Blo 2077435 10521089 := bstep (se 2 (by rfl) ⟨3945408, by rfl⟩ : syracuseStep 10521089 = 7890817) B7890817
theorem B7014059 : Blo 2077435 7014059 := bstep (se 1 (by rfl) ⟨5260544, by rfl⟩ : syracuseStep 7014059 = 10521089) B10521089
theorem B4676039 : Blo 2077435 4676039 := bstep (se 1 (by rfl) ⟨3507029, by rfl⟩ : syracuseStep 4676039 = 7014059) B7014059
theorem B3117359 : Blo 2077435 3117359 := bstep (se 1 (by rfl) ⟨2338019, by rfl⟩ : syracuseStep 3117359 = 4676039) B4676039
theorem B2078239 : Blo 2077435 2078239 := bstep (se 1 (by rfl) ⟨1558679, by rfl⟩ : syracuseStep 2078239 = 3117359) B3117359
theorem B3117365 : Blo 2077435 3117365 := bbase (se 5 (by rfl) ⟨146126, by rfl⟩ : syracuseStep 3117365 = 292253) (by norm_num)
theorem B2078243 : Blo 2077435 2078243 := bstep (se 1 (by rfl) ⟨1558682, by rfl⟩ : syracuseStep 2078243 = 3117365) B3117365
theorem B5260565 : Blo 2077435 5260565 := bbase (se 6 (by rfl) ⟨123294, by rfl⟩ : syracuseStep 5260565 = 246589) (by norm_num)
theorem B3507043 : Blo 2077435 3507043 := bstep (se 1 (by rfl) ⟨2630282, by rfl⟩ : syracuseStep 3507043 = 5260565) B5260565
theorem B4676057 : Blo 2077435 4676057 := bstep (se 2 (by rfl) ⟨1753521, by rfl⟩ : syracuseStep 4676057 = 3507043) B3507043
theorem B3117371 : Blo 2077435 3117371 := bstep (se 1 (by rfl) ⟨2338028, by rfl⟩ : syracuseStep 3117371 = 4676057) B4676057
theorem B2078247 : Blo 2077435 2078247 := bstep (se 1 (by rfl) ⟨1558685, by rfl⟩ : syracuseStep 2078247 = 3117371) B3117371
theorem B2338033 : Blo 2077435 2338033 := bbase (se 2 (by rfl) ⟨876762, by rfl⟩ : syracuseStep 2338033 = 1753525) (by norm_num)
theorem B3117377 : Blo 2077435 3117377 := bstep (se 2 (by rfl) ⟨1169016, by rfl⟩ : syracuseStep 3117377 = 2338033) B2338033
theorem B2078251 : Blo 2077435 2078251 := bstep (se 1 (by rfl) ⟨1558688, by rfl⟩ : syracuseStep 2078251 = 3117377) B3117377
theorem B9479749 : Blo 2077435 9479749 := bbase (se 4 (by rfl) ⟨888726, by rfl⟩ : syracuseStep 9479749 = 1777453) (by norm_num)
theorem B12639665 : Blo 2077435 12639665 := bstep (se 2 (by rfl) ⟨4739874, by rfl⟩ : syracuseStep 12639665 = 9479749) B9479749
theorem B8426443 : Blo 2077435 8426443 := bstep (se 1 (by rfl) ⟨6319832, by rfl⟩ : syracuseStep 8426443 = 12639665) B12639665
theorem B11235257 : Blo 2077435 11235257 := bstep (se 2 (by rfl) ⟨4213221, by rfl⟩ : syracuseStep 11235257 = 8426443) B8426443
theorem B7490171 : Blo 2077435 7490171 := bstep (se 1 (by rfl) ⟨5617628, by rfl⟩ : syracuseStep 7490171 = 11235257) B11235257
theorem B19973789 : Blo 2077435 19973789 := bstep (se 3 (by rfl) ⟨3745085, by rfl⟩ : syracuseStep 19973789 = 7490171) B7490171
theorem B13315859 : Blo 2077435 13315859 := bstep (se 1 (by rfl) ⟨9986894, by rfl⟩ : syracuseStep 13315859 = 19973789) B19973789
theorem B8877239 : Blo 2077435 8877239 := bstep (se 1 (by rfl) ⟨6657929, by rfl⟩ : syracuseStep 8877239 = 13315859) B13315859
theorem B5918159 : Blo 2077435 5918159 := bstep (se 1 (by rfl) ⟨4438619, by rfl⟩ : syracuseStep 5918159 = 8877239) B8877239
theorem B3945439 : Blo 2077435 3945439 := bstep (se 1 (by rfl) ⟨2959079, by rfl⟩ : syracuseStep 3945439 = 5918159) B5918159
theorem B5260585 : Blo 2077435 5260585 := bstep (se 2 (by rfl) ⟨1972719, by rfl⟩ : syracuseStep 5260585 = 3945439) B3945439
theorem B7014113 : Blo 2077435 7014113 := bstep (se 2 (by rfl) ⟨2630292, by rfl⟩ : syracuseStep 7014113 = 5260585) B5260585
theorem B4676075 : Blo 2077435 4676075 := bstep (se 1 (by rfl) ⟨3507056, by rfl⟩ : syracuseStep 4676075 = 7014113) B7014113
theorem B3117383 : Blo 2077435 3117383 := bstep (se 1 (by rfl) ⟨2338037, by rfl⟩ : syracuseStep 3117383 = 4676075) B4676075
theorem B2078255 : Blo 2077435 2078255 := bstep (se 1 (by rfl) ⟨1558691, by rfl⟩ : syracuseStep 2078255 = 3117383) B3117383
theorem B3117389 : Blo 2077435 3117389 := bbase (se 3 (by rfl) ⟨584510, by rfl⟩ : syracuseStep 3117389 = 1169021) (by norm_num)
theorem B2078259 : Blo 2077435 2078259 := bstep (se 1 (by rfl) ⟨1558694, by rfl⟩ : syracuseStep 2078259 = 3117389) B3117389
theorem B4676093 : Blo 2077435 4676093 := bbase (se 3 (by rfl) ⟨876767, by rfl⟩ : syracuseStep 4676093 = 1753535) (by norm_num)
theorem B3117395 : Blo 2077435 3117395 := bstep (se 1 (by rfl) ⟨2338046, by rfl⟩ : syracuseStep 3117395 = 4676093) B4676093
theorem B2078263 : Blo 2077435 2078263 := bstep (se 1 (by rfl) ⟨1558697, by rfl⟩ : syracuseStep 2078263 = 3117395) B3117395
theorem B3507077 : Blo 2077435 3507077 := bbase (se 4 (by rfl) ⟨328788, by rfl⟩ : syracuseStep 3507077 = 657577) (by norm_num)
theorem B2338051 : Blo 2077435 2338051 := bstep (se 1 (by rfl) ⟨1753538, by rfl⟩ : syracuseStep 2338051 = 3507077) B3507077
theorem B3117401 : Blo 2077435 3117401 := bstep (se 2 (by rfl) ⟨1169025, by rfl⟩ : syracuseStep 3117401 = 2338051) B2338051
theorem B2078267 : Blo 2077435 2078267 := bstep (se 1 (by rfl) ⟨1558700, by rfl⟩ : syracuseStep 2078267 = 3117401) B3117401
theorem B15781877 : Blo 2077435 15781877 := bbase (se 5 (by rfl) ⟨739775, by rfl⟩ : syracuseStep 15781877 = 1479551) (by norm_num)
theorem B10521251 : Blo 2077435 10521251 := bstep (se 1 (by rfl) ⟨7890938, by rfl⟩ : syracuseStep 10521251 = 15781877) B15781877
theorem B7014167 : Blo 2077435 7014167 := bstep (se 1 (by rfl) ⟨5260625, by rfl⟩ : syracuseStep 7014167 = 10521251) B10521251
theorem B4676111 : Blo 2077435 4676111 := bstep (se 1 (by rfl) ⟨3507083, by rfl⟩ : syracuseStep 4676111 = 7014167) B7014167
theorem B3117407 : Blo 2077435 3117407 := bstep (se 1 (by rfl) ⟨2338055, by rfl⟩ : syracuseStep 3117407 = 4676111) B4676111
theorem B2078271 : Blo 2077435 2078271 := bstep (se 1 (by rfl) ⟨1558703, by rfl⟩ : syracuseStep 2078271 = 3117407) B3117407
theorem B3117413 : Blo 2077435 3117413 := bbase (se 4 (by rfl) ⟨292257, by rfl⟩ : syracuseStep 3117413 = 584515) (by norm_num)
theorem B2078275 : Blo 2077435 2078275 := bstep (se 1 (by rfl) ⟨1558706, by rfl⟩ : syracuseStep 2078275 = 3117413) B3117413
theorem B3945485 : Blo 2077435 3945485 := bbase (se 3 (by rfl) ⟨739778, by rfl⟩ : syracuseStep 3945485 = 1479557) (by norm_num)
theorem B2630323 : Blo 2077435 2630323 := bstep (se 1 (by rfl) ⟨1972742, by rfl⟩ : syracuseStep 2630323 = 3945485) B3945485
theorem B3507097 : Blo 2077435 3507097 := bstep (se 2 (by rfl) ⟨1315161, by rfl⟩ : syracuseStep 3507097 = 2630323) B2630323
theorem B4676129 : Blo 2077435 4676129 := bstep (se 2 (by rfl) ⟨1753548, by rfl⟩ : syracuseStep 4676129 = 3507097) B3507097
theorem B3117419 : Blo 2077435 3117419 := bstep (se 1 (by rfl) ⟨2338064, by rfl⟩ : syracuseStep 3117419 = 4676129) B4676129
theorem B2078279 : Blo 2077435 2078279 := bstep (se 1 (by rfl) ⟨1558709, by rfl⟩ : syracuseStep 2078279 = 3117419) B3117419
theorem B2338069 : Blo 2077435 2338069 := bbase (se 6 (by rfl) ⟨54798, by rfl⟩ : syracuseStep 2338069 = 109597) (by norm_num)
theorem B3117425 : Blo 2077435 3117425 := bstep (se 2 (by rfl) ⟨1169034, by rfl⟩ : syracuseStep 3117425 = 2338069) B2338069
theorem B2078283 : Blo 2077435 2078283 := bstep (se 1 (by rfl) ⟨1558712, by rfl⟩ : syracuseStep 2078283 = 3117425) B3117425
theorem B2630333 : Blo 2077435 2630333 := bbase (se 3 (by rfl) ⟨493187, by rfl⟩ : syracuseStep 2630333 = 986375) (by norm_num)
theorem B7014221 : Blo 2077435 7014221 := bstep (se 3 (by rfl) ⟨1315166, by rfl⟩ : syracuseStep 7014221 = 2630333) B2630333
theorem B4676147 : Blo 2077435 4676147 := bstep (se 1 (by rfl) ⟨3507110, by rfl⟩ : syracuseStep 4676147 = 7014221) B7014221
theorem B3117431 : Blo 2077435 3117431 := bstep (se 1 (by rfl) ⟨2338073, by rfl⟩ : syracuseStep 3117431 = 4676147) B4676147
theorem B2078287 : Blo 2077435 2078287 := bstep (se 1 (by rfl) ⟨1558715, by rfl⟩ : syracuseStep 2078287 = 3117431) B3117431
theorem B3117437 : Blo 2077435 3117437 := bbase (se 3 (by rfl) ⟨584519, by rfl⟩ : syracuseStep 3117437 = 1169039) (by norm_num)
theorem B2078291 : Blo 2077435 2078291 := bstep (se 1 (by rfl) ⟨1558718, by rfl⟩ : syracuseStep 2078291 = 3117437) B3117437
theorem B4676165 : Blo 2077435 4676165 := bbase (se 4 (by rfl) ⟨438390, by rfl⟩ : syracuseStep 4676165 = 876781) (by norm_num)
theorem B3117443 : Blo 2077435 3117443 := bstep (se 1 (by rfl) ⟨2338082, by rfl⟩ : syracuseStep 3117443 = 4676165) B4676165
theorem B2078295 : Blo 2077435 2078295 := bstep (se 1 (by rfl) ⟨1558721, by rfl⟩ : syracuseStep 2078295 = 3117443) B3117443
theorem B2219357 : Blo 2077435 2219357 := bbase (se 3 (by rfl) ⟨416129, by rfl⟩ : syracuseStep 2219357 = 832259) (by norm_num)
theorem B5918285 : Blo 2077435 5918285 := bstep (se 3 (by rfl) ⟨1109678, by rfl⟩ : syracuseStep 5918285 = 2219357) B2219357
theorem B3945523 : Blo 2077435 3945523 := bstep (se 1 (by rfl) ⟨2959142, by rfl⟩ : syracuseStep 3945523 = 5918285) B5918285
theorem B5260697 : Blo 2077435 5260697 := bstep (se 2 (by rfl) ⟨1972761, by rfl⟩ : syracuseStep 5260697 = 3945523) B3945523
theorem B3507131 : Blo 2077435 3507131 := bstep (se 1 (by rfl) ⟨2630348, by rfl⟩ : syracuseStep 3507131 = 5260697) B5260697
theorem B2338087 : Blo 2077435 2338087 := bstep (se 1 (by rfl) ⟨1753565, by rfl⟩ : syracuseStep 2338087 = 3507131) B3507131
theorem B3117449 : Blo 2077435 3117449 := bstep (se 2 (by rfl) ⟨1169043, by rfl⟩ : syracuseStep 3117449 = 2338087) B2338087
theorem B2078299 : Blo 2077435 2078299 := bstep (se 1 (by rfl) ⟨1558724, by rfl⟩ : syracuseStep 2078299 = 3117449) B3117449
theorem B10521413 : Blo 2077435 10521413 := bbase (se 4 (by rfl) ⟨986382, by rfl⟩ : syracuseStep 10521413 = 1972765) (by norm_num)
theorem B7014275 : Blo 2077435 7014275 := bstep (se 1 (by rfl) ⟨5260706, by rfl⟩ : syracuseStep 7014275 = 10521413) B10521413
theorem B4676183 : Blo 2077435 4676183 := bstep (se 1 (by rfl) ⟨3507137, by rfl⟩ : syracuseStep 4676183 = 7014275) B7014275
theorem B3117455 : Blo 2077435 3117455 := bstep (se 1 (by rfl) ⟨2338091, by rfl⟩ : syracuseStep 3117455 = 4676183) B4676183
theorem B2078303 : Blo 2077435 2078303 := bstep (se 1 (by rfl) ⟨1558727, by rfl⟩ : syracuseStep 2078303 = 3117455) B3117455
theorem B3117461 : Blo 2077435 3117461 := bbase (se 6 (by rfl) ⟨73065, by rfl⟩ : syracuseStep 3117461 = 146131) (by norm_num)
theorem B2078307 : Blo 2077435 2078307 := bstep (se 1 (by rfl) ⟨1558730, by rfl⟩ : syracuseStep 2078307 = 3117461) B3117461
theorem B5617781 : Blo 2077435 5617781 := bbase (se 5 (by rfl) ⟨263333, by rfl⟩ : syracuseStep 5617781 = 526667) (by norm_num)
theorem B3745187 : Blo 2077435 3745187 := bstep (se 1 (by rfl) ⟨2808890, by rfl⟩ : syracuseStep 3745187 = 5617781) B5617781
theorem B2496791 : Blo 2077435 2496791 := bstep (se 1 (by rfl) ⟨1872593, by rfl⟩ : syracuseStep 2496791 = 3745187) B3745187
theorem B6658109 : Blo 2077435 6658109 := bstep (se 3 (by rfl) ⟨1248395, by rfl⟩ : syracuseStep 6658109 = 2496791) B2496791
theorem B4438739 : Blo 2077435 4438739 := bstep (se 1 (by rfl) ⟨3329054, by rfl⟩ : syracuseStep 4438739 = 6658109) B6658109
theorem B11836637 : Blo 2077435 11836637 := bstep (se 3 (by rfl) ⟨2219369, by rfl⟩ : syracuseStep 11836637 = 4438739) B4438739
theorem B7891091 : Blo 2077435 7891091 := bstep (se 1 (by rfl) ⟨5918318, by rfl⟩ : syracuseStep 7891091 = 11836637) B11836637
theorem B5260727 : Blo 2077435 5260727 := bstep (se 1 (by rfl) ⟨3945545, by rfl⟩ : syracuseStep 5260727 = 7891091) B7891091
theorem B3507151 : Blo 2077435 3507151 := bstep (se 1 (by rfl) ⟨2630363, by rfl⟩ : syracuseStep 3507151 = 5260727) B5260727
theorem B4676201 : Blo 2077435 4676201 := bstep (se 2 (by rfl) ⟨1753575, by rfl⟩ : syracuseStep 4676201 = 3507151) B3507151
theorem B3117467 : Blo 2077435 3117467 := bstep (se 1 (by rfl) ⟨2338100, by rfl⟩ : syracuseStep 3117467 = 4676201) B4676201
theorem B2078311 : Blo 2077435 2078311 := bstep (se 1 (by rfl) ⟨1558733, by rfl⟩ : syracuseStep 2078311 = 3117467) B3117467
theorem B2338105 : Blo 2077435 2338105 := bbase (se 2 (by rfl) ⟨876789, by rfl⟩ : syracuseStep 2338105 = 1753579) (by norm_num)
theorem B3117473 : Blo 2077435 3117473 := bstep (se 2 (by rfl) ⟨1169052, by rfl⟩ : syracuseStep 3117473 = 2338105) B2338105
theorem B2078315 : Blo 2077435 2078315 := bstep (se 1 (by rfl) ⟨1558736, by rfl⟩ : syracuseStep 2078315 = 3117473) B3117473
theorem B5918341 : Blo 2077435 5918341 := bbase (se 4 (by rfl) ⟨554844, by rfl⟩ : syracuseStep 5918341 = 1109689) (by norm_num)
theorem B7891121 : Blo 2077435 7891121 := bstep (se 2 (by rfl) ⟨2959170, by rfl⟩ : syracuseStep 7891121 = 5918341) B5918341
theorem B5260747 : Blo 2077435 5260747 := bstep (se 1 (by rfl) ⟨3945560, by rfl⟩ : syracuseStep 5260747 = 7891121) B7891121
theorem B7014329 : Blo 2077435 7014329 := bstep (se 2 (by rfl) ⟨2630373, by rfl⟩ : syracuseStep 7014329 = 5260747) B5260747
theorem B4676219 : Blo 2077435 4676219 := bstep (se 1 (by rfl) ⟨3507164, by rfl⟩ : syracuseStep 4676219 = 7014329) B7014329
theorem B3117479 : Blo 2077435 3117479 := bstep (se 1 (by rfl) ⟨2338109, by rfl⟩ : syracuseStep 3117479 = 4676219) B4676219
theorem B2078319 : Blo 2077435 2078319 := bstep (se 1 (by rfl) ⟨1558739, by rfl⟩ : syracuseStep 2078319 = 3117479) B3117479
theorem B3117485 : Blo 2077435 3117485 := bbase (se 3 (by rfl) ⟨584528, by rfl⟩ : syracuseStep 3117485 = 1169057) (by norm_num)
theorem B2078323 : Blo 2077435 2078323 := bstep (se 1 (by rfl) ⟨1558742, by rfl⟩ : syracuseStep 2078323 = 3117485) B3117485
theorem B4676237 : Blo 2077435 4676237 := bbase (se 3 (by rfl) ⟨876794, by rfl⟩ : syracuseStep 4676237 = 1753589) (by norm_num)
theorem B3117491 : Blo 2077435 3117491 := bstep (se 1 (by rfl) ⟨2338118, by rfl⟩ : syracuseStep 3117491 = 4676237) B4676237
theorem B2078327 : Blo 2077435 2078327 := bstep (se 1 (by rfl) ⟨1558745, by rfl⟩ : syracuseStep 2078327 = 3117491) B3117491
theorem B2630389 : Blo 2077435 2630389 := bbase (se 5 (by rfl) ⟨123299, by rfl⟩ : syracuseStep 2630389 = 246599) (by norm_num)
theorem B3507185 : Blo 2077435 3507185 := bstep (se 2 (by rfl) ⟨1315194, by rfl⟩ : syracuseStep 3507185 = 2630389) B2630389
theorem B2338123 : Blo 2077435 2338123 := bstep (se 1 (by rfl) ⟨1753592, by rfl⟩ : syracuseStep 2338123 = 3507185) B3507185
theorem B3117497 : Blo 2077435 3117497 := bstep (se 2 (by rfl) ⟨1169061, by rfl⟩ : syracuseStep 3117497 = 2338123) B2338123
theorem B2078331 : Blo 2077435 2078331 := bstep (se 1 (by rfl) ⟨1558748, by rfl⟩ : syracuseStep 2078331 = 3117497) B3117497
theorem B3745229 : Blo 2077435 3745229 := bbase (se 3 (by rfl) ⟨702230, by rfl⟩ : syracuseStep 3745229 = 1404461) (by norm_num)
theorem B39949109 : Blo 2077435 39949109 := bstep (se 5 (by rfl) ⟨1872614, by rfl⟩ : syracuseStep 39949109 = 3745229) B3745229
theorem B26632739 : Blo 2077435 26632739 := bstep (se 1 (by rfl) ⟨19974554, by rfl⟩ : syracuseStep 26632739 = 39949109) B39949109
theorem B17755159 : Blo 2077435 17755159 := bstep (se 1 (by rfl) ⟨13316369, by rfl⟩ : syracuseStep 17755159 = 26632739) B26632739
theorem B23673545 : Blo 2077435 23673545 := bstep (se 2 (by rfl) ⟨8877579, by rfl⟩ : syracuseStep 23673545 = 17755159) B17755159
theorem B15782363 : Blo 2077435 15782363 := bstep (se 1 (by rfl) ⟨11836772, by rfl⟩ : syracuseStep 15782363 = 23673545) B23673545
theorem B10521575 : Blo 2077435 10521575 := bstep (se 1 (by rfl) ⟨7891181, by rfl⟩ : syracuseStep 10521575 = 15782363) B15782363
theorem B7014383 : Blo 2077435 7014383 := bstep (se 1 (by rfl) ⟨5260787, by rfl⟩ : syracuseStep 7014383 = 10521575) B10521575
theorem B4676255 : Blo 2077435 4676255 := bstep (se 1 (by rfl) ⟨3507191, by rfl⟩ : syracuseStep 4676255 = 7014383) B7014383
theorem B3117503 : Blo 2077435 3117503 := bstep (se 1 (by rfl) ⟨2338127, by rfl⟩ : syracuseStep 3117503 = 4676255) B4676255
theorem B2078335 : Blo 2077435 2078335 := bstep (se 1 (by rfl) ⟨1558751, by rfl⟩ : syracuseStep 2078335 = 3117503) B3117503
theorem B3117509 : Blo 2077435 3117509 := bbase (se 4 (by rfl) ⟨292266, by rfl⟩ : syracuseStep 3117509 = 584533) (by norm_num)
theorem B2078339 : Blo 2077435 2078339 := bstep (se 1 (by rfl) ⟨1558754, by rfl⟩ : syracuseStep 2078339 = 3117509) B3117509
theorem B3507205 : Blo 2077435 3507205 := bbase (se 4 (by rfl) ⟨328800, by rfl⟩ : syracuseStep 3507205 = 657601) (by norm_num)
theorem B4676273 : Blo 2077435 4676273 := bstep (se 2 (by rfl) ⟨1753602, by rfl⟩ : syracuseStep 4676273 = 3507205) B3507205
theorem B3117515 : Blo 2077435 3117515 := bstep (se 1 (by rfl) ⟨2338136, by rfl⟩ : syracuseStep 3117515 = 4676273) B4676273
theorem B2078343 : Blo 2077435 2078343 := bstep (se 1 (by rfl) ⟨1558757, by rfl⟩ : syracuseStep 2078343 = 3117515) B3117515
theorem B2338141 : Blo 2077435 2338141 := bbase (se 3 (by rfl) ⟨438401, by rfl⟩ : syracuseStep 2338141 = 876803) (by norm_num)
theorem B3117521 : Blo 2077435 3117521 := bstep (se 2 (by rfl) ⟨1169070, by rfl⟩ : syracuseStep 3117521 = 2338141) B2338141
theorem B2078347 : Blo 2077435 2078347 := bstep (se 1 (by rfl) ⟨1558760, by rfl⟩ : syracuseStep 2078347 = 3117521) B3117521
theorem B7014437 : Blo 2077435 7014437 := bbase (se 4 (by rfl) ⟨657603, by rfl⟩ : syracuseStep 7014437 = 1315207) (by norm_num)
theorem B4676291 : Blo 2077435 4676291 := bstep (se 1 (by rfl) ⟨3507218, by rfl⟩ : syracuseStep 4676291 = 7014437) B7014437
theorem B3117527 : Blo 2077435 3117527 := bstep (se 1 (by rfl) ⟨2338145, by rfl⟩ : syracuseStep 3117527 = 4676291) B4676291
theorem B2078351 : Blo 2077435 2078351 := bstep (se 1 (by rfl) ⟨1558763, by rfl⟩ : syracuseStep 2078351 = 3117527) B3117527
theorem B3117533 : Blo 2077435 3117533 := bbase (se 3 (by rfl) ⟨584537, by rfl⟩ : syracuseStep 3117533 = 1169075) (by norm_num)
theorem B2078355 : Blo 2077435 2078355 := bstep (se 1 (by rfl) ⟨1558766, by rfl⟩ : syracuseStep 2078355 = 3117533) B3117533
theorem B4676309 : Blo 2077435 4676309 := bbase (se 7 (by rfl) ⟨54800, by rfl⟩ : syracuseStep 4676309 = 109601) (by norm_num)
theorem B3117539 : Blo 2077435 3117539 := bstep (se 1 (by rfl) ⟨2338154, by rfl⟩ : syracuseStep 3117539 = 4676309) B4676309
theorem B2078359 : Blo 2077435 2078359 := bstep (se 1 (by rfl) ⟨1558769, by rfl⟩ : syracuseStep 2078359 = 3117539) B3117539
theorem B8877701 : Blo 2077435 8877701 := bbase (se 4 (by rfl) ⟨832284, by rfl⟩ : syracuseStep 8877701 = 1664569) (by norm_num)
theorem B5918467 : Blo 2077435 5918467 := bstep (se 1 (by rfl) ⟨4438850, by rfl⟩ : syracuseStep 5918467 = 8877701) B8877701
theorem B7891289 : Blo 2077435 7891289 := bstep (se 2 (by rfl) ⟨2959233, by rfl⟩ : syracuseStep 7891289 = 5918467) B5918467
theorem B5260859 : Blo 2077435 5260859 := bstep (se 1 (by rfl) ⟨3945644, by rfl⟩ : syracuseStep 5260859 = 7891289) B7891289
theorem B3507239 : Blo 2077435 3507239 := bstep (se 1 (by rfl) ⟨2630429, by rfl⟩ : syracuseStep 3507239 = 5260859) B5260859
theorem B2338159 : Blo 2077435 2338159 := bstep (se 1 (by rfl) ⟨1753619, by rfl⟩ : syracuseStep 2338159 = 3507239) B3507239
theorem B3117545 : Blo 2077435 3117545 := bstep (se 2 (by rfl) ⟨1169079, by rfl⟩ : syracuseStep 3117545 = 2338159) B2338159
theorem B2078363 : Blo 2077435 2078363 := bstep (se 1 (by rfl) ⟨1558772, by rfl⟩ : syracuseStep 2078363 = 3117545) B3117545
theorem B3082021 : Blo 2077435 3082021 := bbase (se 4 (by rfl) ⟨288939, by rfl⟩ : syracuseStep 3082021 = 577879) (by norm_num)
theorem B65749781 : Blo 2077435 65749781 := bstep (se 6 (by rfl) ⟨1541010, by rfl⟩ : syracuseStep 65749781 = 3082021) B3082021
theorem B43833187 : Blo 2077435 43833187 := bstep (se 1 (by rfl) ⟨32874890, by rfl⟩ : syracuseStep 43833187 = 65749781) B65749781
theorem B58444249 : Blo 2077435 58444249 := bstep (se 2 (by rfl) ⟨21916593, by rfl⟩ : syracuseStep 58444249 = 43833187) B43833187
theorem B77925665 : Blo 2077435 77925665 := bstep (se 2 (by rfl) ⟨29222124, by rfl⟩ : syracuseStep 77925665 = 58444249) B58444249
theorem B51950443 : Blo 2077435 51950443 := bstep (se 1 (by rfl) ⟨38962832, by rfl⟩ : syracuseStep 51950443 = 77925665) B77925665
theorem B69267257 : Blo 2077435 69267257 := bstep (se 2 (by rfl) ⟨25975221, by rfl⟩ : syracuseStep 69267257 = 51950443) B51950443
theorem B46178171 : Blo 2077435 46178171 := bstep (se 1 (by rfl) ⟨34633628, by rfl⟩ : syracuseStep 46178171 = 69267257) B69267257
theorem B30785447 : Blo 2077435 30785447 := bstep (se 1 (by rfl) ⟨23089085, by rfl⟩ : syracuseStep 30785447 = 46178171) B46178171
theorem B20523631 : Blo 2077435 20523631 := bstep (se 1 (by rfl) ⟨15392723, by rfl⟩ : syracuseStep 20523631 = 30785447) B30785447
theorem B27364841 : Blo 2077435 27364841 := bstep (se 2 (by rfl) ⟨10261815, by rfl⟩ : syracuseStep 27364841 = 20523631) B20523631
theorem B18243227 : Blo 2077435 18243227 := bstep (se 1 (by rfl) ⟨13682420, by rfl⟩ : syracuseStep 18243227 = 27364841) B27364841
theorem B12162151 : Blo 2077435 12162151 := bstep (se 1 (by rfl) ⟨9121613, by rfl⟩ : syracuseStep 12162151 = 18243227) B18243227
theorem B16216201 : Blo 2077435 16216201 := bstep (se 2 (by rfl) ⟨6081075, by rfl⟩ : syracuseStep 16216201 = 12162151) B12162151
theorem B21621601 : Blo 2077435 21621601 := bstep (se 2 (by rfl) ⟨8108100, by rfl⟩ : syracuseStep 21621601 = 16216201) B16216201
theorem B28828801 : Blo 2077435 28828801 := bstep (se 2 (by rfl) ⟨10810800, by rfl⟩ : syracuseStep 28828801 = 21621601) B21621601
theorem B38438401 : Blo 2077435 38438401 := bstep (se 2 (by rfl) ⟨14414400, by rfl⟩ : syracuseStep 38438401 = 28828801) B28828801
theorem B51251201 : Blo 2077435 51251201 := bstep (se 2 (by rfl) ⟨19219200, by rfl⟩ : syracuseStep 51251201 = 38438401) B38438401
theorem B34167467 : Blo 2077435 34167467 := bstep (se 1 (by rfl) ⟨25625600, by rfl⟩ : syracuseStep 34167467 = 51251201) B51251201
theorem B91113245 : Blo 2077435 91113245 := bstep (se 3 (by rfl) ⟨17083733, by rfl⟩ : syracuseStep 91113245 = 34167467) B34167467
theorem B60742163 : Blo 2077435 60742163 := bstep (se 1 (by rfl) ⟨45556622, by rfl⟩ : syracuseStep 60742163 = 91113245) B91113245
theorem B40494775 : Blo 2077435 40494775 := bstep (se 1 (by rfl) ⟨30371081, by rfl⟩ : syracuseStep 40494775 = 60742163) B60742163
theorem B53993033 : Blo 2077435 53993033 := bstep (se 2 (by rfl) ⟨20247387, by rfl⟩ : syracuseStep 53993033 = 40494775) B40494775
theorem B35995355 : Blo 2077435 35995355 := bstep (se 1 (by rfl) ⟨26996516, by rfl⟩ : syracuseStep 35995355 = 53993033) B53993033
theorem B23996903 : Blo 2077435 23996903 := bstep (se 1 (by rfl) ⟨17997677, by rfl⟩ : syracuseStep 23996903 = 35995355) B35995355
theorem B63991741 : Blo 2077435 63991741 := bstep (se 3 (by rfl) ⟨11998451, by rfl⟩ : syracuseStep 63991741 = 23996903) B23996903
theorem B85322321 : Blo 2077435 85322321 := bstep (se 2 (by rfl) ⟨31995870, by rfl⟩ : syracuseStep 85322321 = 63991741) B63991741
theorem B56881547 : Blo 2077435 56881547 := bstep (se 1 (by rfl) ⟨42661160, by rfl⟩ : syracuseStep 56881547 = 85322321) B85322321
theorem B37921031 : Blo 2077435 37921031 := bstep (se 1 (by rfl) ⟨28440773, by rfl⟩ : syracuseStep 37921031 = 56881547) B56881547
theorem B25280687 : Blo 2077435 25280687 := bstep (se 1 (by rfl) ⟨18960515, by rfl⟩ : syracuseStep 25280687 = 37921031) B37921031
theorem B67415165 : Blo 2077435 67415165 := bstep (se 3 (by rfl) ⟨12640343, by rfl⟩ : syracuseStep 67415165 = 25280687) B25280687
theorem B44943443 : Blo 2077435 44943443 := bstep (se 1 (by rfl) ⟨33707582, by rfl⟩ : syracuseStep 44943443 = 67415165) B67415165
theorem B29962295 : Blo 2077435 29962295 := bstep (se 1 (by rfl) ⟨22471721, by rfl⟩ : syracuseStep 29962295 = 44943443) B44943443
theorem B19974863 : Blo 2077435 19974863 := bstep (se 1 (by rfl) ⟨14981147, by rfl⟩ : syracuseStep 19974863 = 29962295) B29962295
theorem B13316575 : Blo 2077435 13316575 := bstep (se 1 (by rfl) ⟨9987431, by rfl⟩ : syracuseStep 13316575 = 19974863) B19974863
theorem B17755433 : Blo 2077435 17755433 := bstep (se 2 (by rfl) ⟨6658287, by rfl⟩ : syracuseStep 17755433 = 13316575) B13316575
theorem B11836955 : Blo 2077435 11836955 := bstep (se 1 (by rfl) ⟨8877716, by rfl⟩ : syracuseStep 11836955 = 17755433) B17755433
theorem B7891303 : Blo 2077435 7891303 := bstep (se 1 (by rfl) ⟨5918477, by rfl⟩ : syracuseStep 7891303 = 11836955) B11836955
theorem B10521737 : Blo 2077435 10521737 := bstep (se 2 (by rfl) ⟨3945651, by rfl⟩ : syracuseStep 10521737 = 7891303) B7891303
theorem B7014491 : Blo 2077435 7014491 := bstep (se 1 (by rfl) ⟨5260868, by rfl⟩ : syracuseStep 7014491 = 10521737) B10521737
theorem B4676327 : Blo 2077435 4676327 := bstep (se 1 (by rfl) ⟨3507245, by rfl⟩ : syracuseStep 4676327 = 7014491) B7014491
theorem B3117551 : Blo 2077435 3117551 := bstep (se 1 (by rfl) ⟨2338163, by rfl⟩ : syracuseStep 3117551 = 4676327) B4676327
theorem B2078367 : Blo 2077435 2078367 := bstep (se 1 (by rfl) ⟨1558775, by rfl⟩ : syracuseStep 2078367 = 3117551) B3117551
theorem B3117557 : Blo 2077435 3117557 := bbase (se 5 (by rfl) ⟨146135, by rfl⟩ : syracuseStep 3117557 = 292271) (by norm_num)
theorem B2078371 : Blo 2077435 2078371 := bstep (se 1 (by rfl) ⟨1558778, by rfl⟩ : syracuseStep 2078371 = 3117557) B3117557
theorem B5918501 : Blo 2077435 5918501 := bbase (se 4 (by rfl) ⟨554859, by rfl⟩ : syracuseStep 5918501 = 1109719) (by norm_num)
theorem B3945667 : Blo 2077435 3945667 := bstep (se 1 (by rfl) ⟨2959250, by rfl⟩ : syracuseStep 3945667 = 5918501) B5918501
theorem B5260889 : Blo 2077435 5260889 := bstep (se 2 (by rfl) ⟨1972833, by rfl⟩ : syracuseStep 5260889 = 3945667) B3945667
theorem B3507259 : Blo 2077435 3507259 := bstep (se 1 (by rfl) ⟨2630444, by rfl⟩ : syracuseStep 3507259 = 5260889) B5260889
theorem B4676345 : Blo 2077435 4676345 := bstep (se 2 (by rfl) ⟨1753629, by rfl⟩ : syracuseStep 4676345 = 3507259) B3507259
theorem B3117563 : Blo 2077435 3117563 := bstep (se 1 (by rfl) ⟨2338172, by rfl⟩ : syracuseStep 3117563 = 4676345) B4676345
theorem B2078375 : Blo 2077435 2078375 := bstep (se 1 (by rfl) ⟨1558781, by rfl⟩ : syracuseStep 2078375 = 3117563) B3117563
theorem B2338177 : Blo 2077435 2338177 := bbase (se 2 (by rfl) ⟨876816, by rfl⟩ : syracuseStep 2338177 = 1753633) (by norm_num)
theorem B3117569 : Blo 2077435 3117569 := bstep (se 2 (by rfl) ⟨1169088, by rfl⟩ : syracuseStep 3117569 = 2338177) B2338177
theorem B2078379 : Blo 2077435 2078379 := bstep (se 1 (by rfl) ⟨1558784, by rfl⟩ : syracuseStep 2078379 = 3117569) B3117569
theorem B5260909 : Blo 2077435 5260909 := bbase (se 3 (by rfl) ⟨986420, by rfl⟩ : syracuseStep 5260909 = 1972841) (by norm_num)
theorem B7014545 : Blo 2077435 7014545 := bstep (se 2 (by rfl) ⟨2630454, by rfl⟩ : syracuseStep 7014545 = 5260909) B5260909
theorem B4676363 : Blo 2077435 4676363 := bstep (se 1 (by rfl) ⟨3507272, by rfl⟩ : syracuseStep 4676363 = 7014545) B7014545
theorem B3117575 : Blo 2077435 3117575 := bstep (se 1 (by rfl) ⟨2338181, by rfl⟩ : syracuseStep 3117575 = 4676363) B4676363
theorem B2078383 : Blo 2077435 2078383 := bstep (se 1 (by rfl) ⟨1558787, by rfl⟩ : syracuseStep 2078383 = 3117575) B3117575
theorem B3117581 : Blo 2077435 3117581 := bbase (se 3 (by rfl) ⟨584546, by rfl⟩ : syracuseStep 3117581 = 1169093) (by norm_num)
theorem B2078387 : Blo 2077435 2078387 := bstep (se 1 (by rfl) ⟨1558790, by rfl⟩ : syracuseStep 2078387 = 3117581) B3117581
theorem B4676381 : Blo 2077435 4676381 := bbase (se 3 (by rfl) ⟨876821, by rfl⟩ : syracuseStep 4676381 = 1753643) (by norm_num)
theorem B3117587 : Blo 2077435 3117587 := bstep (se 1 (by rfl) ⟨2338190, by rfl⟩ : syracuseStep 3117587 = 4676381) B4676381
theorem B2078391 : Blo 2077435 2078391 := bstep (se 1 (by rfl) ⟨1558793, by rfl⟩ : syracuseStep 2078391 = 3117587) B3117587
theorem B3507293 : Blo 2077435 3507293 := bbase (se 3 (by rfl) ⟨657617, by rfl⟩ : syracuseStep 3507293 = 1315235) (by norm_num)
theorem B2338195 : Blo 2077435 2338195 := bstep (se 1 (by rfl) ⟨1753646, by rfl⟩ : syracuseStep 2338195 = 3507293) B3507293
theorem B3117593 : Blo 2077435 3117593 := bstep (se 2 (by rfl) ⟨1169097, by rfl⟩ : syracuseStep 3117593 = 2338195) B2338195
theorem B2078395 : Blo 2077435 2078395 := bstep (se 1 (by rfl) ⟨1558796, by rfl⟩ : syracuseStep 2078395 = 3117593) B3117593
theorem B2106757 : Blo 2077435 2106757 := bbase (se 4 (by rfl) ⟨197508, by rfl⟩ : syracuseStep 2106757 = 395017) (by norm_num)
theorem B2809009 : Blo 2077435 2809009 := bstep (se 2 (by rfl) ⟨1053378, by rfl⟩ : syracuseStep 2809009 = 2106757) B2106757
theorem B3745345 : Blo 2077435 3745345 := bstep (se 2 (by rfl) ⟨1404504, by rfl⟩ : syracuseStep 3745345 = 2809009) B2809009
theorem B4993793 : Blo 2077435 4993793 := bstep (se 2 (by rfl) ⟨1872672, by rfl⟩ : syracuseStep 4993793 = 3745345) B3745345
theorem B3329195 : Blo 2077435 3329195 := bstep (se 1 (by rfl) ⟨2496896, by rfl⟩ : syracuseStep 3329195 = 4993793) B4993793
theorem B8877853 : Blo 2077435 8877853 := bstep (se 3 (by rfl) ⟨1664597, by rfl⟩ : syracuseStep 8877853 = 3329195) B3329195
theorem B11837137 : Blo 2077435 11837137 := bstep (se 2 (by rfl) ⟨4438926, by rfl⟩ : syracuseStep 11837137 = 8877853) B8877853
theorem B15782849 : Blo 2077435 15782849 := bstep (se 2 (by rfl) ⟨5918568, by rfl⟩ : syracuseStep 15782849 = 11837137) B11837137
theorem B10521899 : Blo 2077435 10521899 := bstep (se 1 (by rfl) ⟨7891424, by rfl⟩ : syracuseStep 10521899 = 15782849) B15782849
theorem B7014599 : Blo 2077435 7014599 := bstep (se 1 (by rfl) ⟨5260949, by rfl⟩ : syracuseStep 7014599 = 10521899) B10521899
theorem B4676399 : Blo 2077435 4676399 := bstep (se 1 (by rfl) ⟨3507299, by rfl⟩ : syracuseStep 4676399 = 7014599) B7014599
theorem B3117599 : Blo 2077435 3117599 := bstep (se 1 (by rfl) ⟨2338199, by rfl⟩ : syracuseStep 3117599 = 4676399) B4676399
theorem B2078399 : Blo 2077435 2078399 := bstep (se 1 (by rfl) ⟨1558799, by rfl⟩ : syracuseStep 2078399 = 3117599) B3117599
theorem B3117605 : Blo 2077435 3117605 := bbase (se 4 (by rfl) ⟨292275, by rfl⟩ : syracuseStep 3117605 = 584551) (by norm_num)
theorem B2078403 : Blo 2077435 2078403 := bstep (se 1 (by rfl) ⟨1558802, by rfl⟩ : syracuseStep 2078403 = 3117605) B3117605
theorem B2630485 : Blo 2077435 2630485 := bbase (se 9 (by rfl) ⟨7706, by rfl⟩ : syracuseStep 2630485 = 15413) (by norm_num)
theorem B3507313 : Blo 2077435 3507313 := bstep (se 2 (by rfl) ⟨1315242, by rfl⟩ : syracuseStep 3507313 = 2630485) B2630485
theorem B4676417 : Blo 2077435 4676417 := bstep (se 2 (by rfl) ⟨1753656, by rfl⟩ : syracuseStep 4676417 = 3507313) B3507313
theorem B3117611 : Blo 2077435 3117611 := bstep (se 1 (by rfl) ⟨2338208, by rfl⟩ : syracuseStep 3117611 = 4676417) B4676417
theorem B2078407 : Blo 2077435 2078407 := bstep (se 1 (by rfl) ⟨1558805, by rfl⟩ : syracuseStep 2078407 = 3117611) B3117611
theorem B2338213 : Blo 2077435 2338213 := bbase (se 4 (by rfl) ⟨219207, by rfl⟩ : syracuseStep 2338213 = 438415) (by norm_num)
theorem B3117617 : Blo 2077435 3117617 := bstep (se 2 (by rfl) ⟨1169106, by rfl⟩ : syracuseStep 3117617 = 2338213) B2338213
theorem B2078411 : Blo 2077435 2078411 := bstep (se 1 (by rfl) ⟨1558808, by rfl⟩ : syracuseStep 2078411 = 3117617) B3117617
theorem B13316885 : Blo 2077435 13316885 := bbase (se 6 (by rfl) ⟨312114, by rfl⟩ : syracuseStep 13316885 = 624229) (by norm_num)
theorem B8877923 : Blo 2077435 8877923 := bstep (se 1 (by rfl) ⟨6658442, by rfl⟩ : syracuseStep 8877923 = 13316885) B13316885
theorem B5918615 : Blo 2077435 5918615 := bstep (se 1 (by rfl) ⟨4438961, by rfl⟩ : syracuseStep 5918615 = 8877923) B8877923
theorem B3945743 : Blo 2077435 3945743 := bstep (se 1 (by rfl) ⟨2959307, by rfl⟩ : syracuseStep 3945743 = 5918615) B5918615
theorem B2630495 : Blo 2077435 2630495 := bstep (se 1 (by rfl) ⟨1972871, by rfl⟩ : syracuseStep 2630495 = 3945743) B3945743
theorem B7014653 : Blo 2077435 7014653 := bstep (se 3 (by rfl) ⟨1315247, by rfl⟩ : syracuseStep 7014653 = 2630495) B2630495
theorem B4676435 : Blo 2077435 4676435 := bstep (se 1 (by rfl) ⟨3507326, by rfl⟩ : syracuseStep 4676435 = 7014653) B7014653
theorem B3117623 : Blo 2077435 3117623 := bstep (se 1 (by rfl) ⟨2338217, by rfl⟩ : syracuseStep 3117623 = 4676435) B4676435
theorem B2078415 : Blo 2077435 2078415 := bstep (se 1 (by rfl) ⟨1558811, by rfl⟩ : syracuseStep 2078415 = 3117623) B3117623
theorem B3117629 : Blo 2077435 3117629 := bbase (se 3 (by rfl) ⟨584555, by rfl⟩ : syracuseStep 3117629 = 1169111) (by norm_num)
theorem B2078419 : Blo 2077435 2078419 := bstep (se 1 (by rfl) ⟨1558814, by rfl⟩ : syracuseStep 2078419 = 3117629) B3117629
theorem B4676453 : Blo 2077435 4676453 := bbase (se 4 (by rfl) ⟨438417, by rfl⟩ : syracuseStep 4676453 = 876835) (by norm_num)
theorem B3117635 : Blo 2077435 3117635 := bstep (se 1 (by rfl) ⟨2338226, by rfl⟩ : syracuseStep 3117635 = 4676453) B4676453
theorem B2078423 : Blo 2077435 2078423 := bstep (se 1 (by rfl) ⟨1558817, by rfl⟩ : syracuseStep 2078423 = 3117635) B3117635
theorem B5261021 : Blo 2077435 5261021 := bbase (se 3 (by rfl) ⟨986441, by rfl⟩ : syracuseStep 5261021 = 1972883) (by norm_num)
theorem B3507347 : Blo 2077435 3507347 := bstep (se 1 (by rfl) ⟨2630510, by rfl⟩ : syracuseStep 3507347 = 5261021) B5261021
theorem B2338231 : Blo 2077435 2338231 := bstep (se 1 (by rfl) ⟨1753673, by rfl⟩ : syracuseStep 2338231 = 3507347) B3507347
theorem B3117641 : Blo 2077435 3117641 := bstep (se 2 (by rfl) ⟨1169115, by rfl⟩ : syracuseStep 3117641 = 2338231) B2338231
theorem B2078427 : Blo 2077435 2078427 := bstep (se 1 (by rfl) ⟨1558820, by rfl⟩ : syracuseStep 2078427 = 3117641) B3117641
theorem B3945773 : Blo 2077435 3945773 := bbase (se 3 (by rfl) ⟨739832, by rfl⟩ : syracuseStep 3945773 = 1479665) (by norm_num)
theorem B10522061 : Blo 2077435 10522061 := bstep (se 3 (by rfl) ⟨1972886, by rfl⟩ : syracuseStep 10522061 = 3945773) B3945773
theorem B7014707 : Blo 2077435 7014707 := bstep (se 1 (by rfl) ⟨5261030, by rfl⟩ : syracuseStep 7014707 = 10522061) B10522061
theorem B4676471 : Blo 2077435 4676471 := bstep (se 1 (by rfl) ⟨3507353, by rfl⟩ : syracuseStep 4676471 = 7014707) B7014707
theorem B3117647 : Blo 2077435 3117647 := bstep (se 1 (by rfl) ⟨2338235, by rfl⟩ : syracuseStep 3117647 = 4676471) B4676471
theorem B2078431 : Blo 2077435 2078431 := bstep (se 1 (by rfl) ⟨1558823, by rfl⟩ : syracuseStep 2078431 = 3117647) B3117647
theorem B3117653 : Blo 2077435 3117653 := bbase (se 8 (by rfl) ⟨18267, by rfl⟩ : syracuseStep 3117653 = 36535) (by norm_num)
theorem B2078435 : Blo 2077435 2078435 := bstep (se 1 (by rfl) ⟨1558826, by rfl⟩ : syracuseStep 2078435 = 3117653) B3117653
theorem B2249789 : Blo 2077435 2249789 := bbase (se 3 (by rfl) ⟨421835, by rfl⟩ : syracuseStep 2249789 = 843671) (by norm_num)
theorem B5999437 : Blo 2077435 5999437 := bstep (se 3 (by rfl) ⟨1124894, by rfl⟩ : syracuseStep 5999437 = 2249789) B2249789
theorem B7999249 : Blo 2077435 7999249 := bstep (se 2 (by rfl) ⟨2999718, by rfl⟩ : syracuseStep 7999249 = 5999437) B5999437
theorem B10665665 : Blo 2077435 10665665 := bstep (se 2 (by rfl) ⟨3999624, by rfl⟩ : syracuseStep 10665665 = 7999249) B7999249
theorem B7110443 : Blo 2077435 7110443 := bstep (se 1 (by rfl) ⟨5332832, by rfl⟩ : syracuseStep 7110443 = 10665665) B10665665
theorem B4740295 : Blo 2077435 4740295 := bstep (se 1 (by rfl) ⟨3555221, by rfl⟩ : syracuseStep 4740295 = 7110443) B7110443
theorem B6320393 : Blo 2077435 6320393 := bstep (se 2 (by rfl) ⟨2370147, by rfl⟩ : syracuseStep 6320393 = 4740295) B4740295
theorem B4213595 : Blo 2077435 4213595 := bstep (se 1 (by rfl) ⟨3160196, by rfl⟩ : syracuseStep 4213595 = 6320393) B6320393
theorem B2809063 : Blo 2077435 2809063 := bstep (se 1 (by rfl) ⟨2106797, by rfl⟩ : syracuseStep 2809063 = 4213595) B4213595
theorem B14981669 : Blo 2077435 14981669 := bstep (se 4 (by rfl) ⟨1404531, by rfl⟩ : syracuseStep 14981669 = 2809063) B2809063
theorem B9987779 : Blo 2077435 9987779 := bstep (se 1 (by rfl) ⟨7490834, by rfl⟩ : syracuseStep 9987779 = 14981669) B14981669
theorem B6658519 : Blo 2077435 6658519 := bstep (se 1 (by rfl) ⟨4993889, by rfl⟩ : syracuseStep 6658519 = 9987779) B9987779
theorem B8878025 : Blo 2077435 8878025 := bstep (se 2 (by rfl) ⟨3329259, by rfl⟩ : syracuseStep 8878025 = 6658519) B6658519
theorem B5918683 : Blo 2077435 5918683 := bstep (se 1 (by rfl) ⟨4439012, by rfl⟩ : syracuseStep 5918683 = 8878025) B8878025
theorem B7891577 : Blo 2077435 7891577 := bstep (se 2 (by rfl) ⟨2959341, by rfl⟩ : syracuseStep 7891577 = 5918683) B5918683
theorem B5261051 : Blo 2077435 5261051 := bstep (se 1 (by rfl) ⟨3945788, by rfl⟩ : syracuseStep 5261051 = 7891577) B7891577
theorem B3507367 : Blo 2077435 3507367 := bstep (se 1 (by rfl) ⟨2630525, by rfl⟩ : syracuseStep 3507367 = 5261051) B5261051
theorem B4676489 : Blo 2077435 4676489 := bstep (se 2 (by rfl) ⟨1753683, by rfl⟩ : syracuseStep 4676489 = 3507367) B3507367
theorem B3117659 : Blo 2077435 3117659 := bstep (se 1 (by rfl) ⟨2338244, by rfl⟩ : syracuseStep 3117659 = 4676489) B4676489
theorem B2078439 : Blo 2077435 2078439 := bstep (se 1 (by rfl) ⟨1558829, by rfl⟩ : syracuseStep 2078439 = 3117659) B3117659
theorem B2338249 : Blo 2077435 2338249 := bbase (se 2 (by rfl) ⟨876843, by rfl⟩ : syracuseStep 2338249 = 1753687) (by norm_num)
theorem B3117665 : Blo 2077435 3117665 := bstep (se 2 (by rfl) ⟨1169124, by rfl⟩ : syracuseStep 3117665 = 2338249) B2338249
theorem B2078443 : Blo 2077435 2078443 := bstep (se 1 (by rfl) ⟨1558832, by rfl⟩ : syracuseStep 2078443 = 3117665) B3117665
theorem B17756117 : Blo 2077435 17756117 := bbase (se 7 (by rfl) ⟨208079, by rfl⟩ : syracuseStep 17756117 = 416159) (by norm_num)
theorem B11837411 : Blo 2077435 11837411 := bstep (se 1 (by rfl) ⟨8878058, by rfl⟩ : syracuseStep 11837411 = 17756117) B17756117
theorem B7891607 : Blo 2077435 7891607 := bstep (se 1 (by rfl) ⟨5918705, by rfl⟩ : syracuseStep 7891607 = 11837411) B11837411
theorem B5261071 : Blo 2077435 5261071 := bstep (se 1 (by rfl) ⟨3945803, by rfl⟩ : syracuseStep 5261071 = 7891607) B7891607
theorem B7014761 : Blo 2077435 7014761 := bstep (se 2 (by rfl) ⟨2630535, by rfl⟩ : syracuseStep 7014761 = 5261071) B5261071
theorem B4676507 : Blo 2077435 4676507 := bstep (se 1 (by rfl) ⟨3507380, by rfl⟩ : syracuseStep 4676507 = 7014761) B7014761
theorem B3117671 : Blo 2077435 3117671 := bstep (se 1 (by rfl) ⟨2338253, by rfl⟩ : syracuseStep 3117671 = 4676507) B4676507
theorem B2078447 : Blo 2077435 2078447 := bstep (se 1 (by rfl) ⟨1558835, by rfl⟩ : syracuseStep 2078447 = 3117671) B3117671
theorem B3117677 : Blo 2077435 3117677 := bbase (se 3 (by rfl) ⟨584564, by rfl⟩ : syracuseStep 3117677 = 1169129) (by norm_num)
theorem B2078451 : Blo 2077435 2078451 := bstep (se 1 (by rfl) ⟨1558838, by rfl⟩ : syracuseStep 2078451 = 3117677) B3117677
theorem B4676525 : Blo 2077435 4676525 := bbase (se 3 (by rfl) ⟨876848, by rfl⟩ : syracuseStep 4676525 = 1753697) (by norm_num)
theorem B3117683 : Blo 2077435 3117683 := bstep (se 1 (by rfl) ⟨2338262, by rfl⟩ : syracuseStep 3117683 = 4676525) B4676525
theorem B2078455 : Blo 2077435 2078455 := bstep (se 1 (by rfl) ⟨1558841, by rfl⟩ : syracuseStep 2078455 = 3117683) B3117683
theorem B5918741 : Blo 2077435 5918741 := bbase (se 6 (by rfl) ⟨138720, by rfl⟩ : syracuseStep 5918741 = 277441) (by norm_num)
theorem B3945827 : Blo 2077435 3945827 := bstep (se 1 (by rfl) ⟨2959370, by rfl⟩ : syracuseStep 3945827 = 5918741) B5918741
theorem B2630551 : Blo 2077435 2630551 := bstep (se 1 (by rfl) ⟨1972913, by rfl⟩ : syracuseStep 2630551 = 3945827) B3945827
theorem B3507401 : Blo 2077435 3507401 := bstep (se 2 (by rfl) ⟨1315275, by rfl⟩ : syracuseStep 3507401 = 2630551) B2630551
theorem B2338267 : Blo 2077435 2338267 := bstep (se 1 (by rfl) ⟨1753700, by rfl⟩ : syracuseStep 2338267 = 3507401) B3507401
theorem B3117689 : Blo 2077435 3117689 := bstep (se 2 (by rfl) ⟨1169133, by rfl⟩ : syracuseStep 3117689 = 2338267) B2338267
theorem B2078459 : Blo 2077435 2078459 := bstep (se 1 (by rfl) ⟨1558844, by rfl⟩ : syracuseStep 2078459 = 3117689) B3117689
theorem B2194237 : Blo 2077435 2194237 := bbase (se 3 (by rfl) ⟨411419, by rfl⟩ : syracuseStep 2194237 = 822839) (by norm_num)
theorem B2925649 : Blo 2077435 2925649 := bstep (se 2 (by rfl) ⟨1097118, by rfl⟩ : syracuseStep 2925649 = 2194237) B2194237
theorem B3900865 : Blo 2077435 3900865 := bstep (se 2 (by rfl) ⟨1462824, by rfl⟩ : syracuseStep 3900865 = 2925649) B2925649
theorem B5201153 : Blo 2077435 5201153 := bstep (se 2 (by rfl) ⟨1950432, by rfl⟩ : syracuseStep 5201153 = 3900865) B3900865
theorem B3467435 : Blo 2077435 3467435 := bstep (se 1 (by rfl) ⟨2600576, by rfl⟩ : syracuseStep 3467435 = 5201153) B5201153
theorem B9246493 : Blo 2077435 9246493 := bstep (se 3 (by rfl) ⟨1733717, by rfl⟩ : syracuseStep 9246493 = 3467435) B3467435
theorem B49314629 : Blo 2077435 49314629 := bstep (se 4 (by rfl) ⟨4623246, by rfl⟩ : syracuseStep 49314629 = 9246493) B9246493
theorem B131505677 : Blo 2077435 131505677 := bstep (se 3 (by rfl) ⟨24657314, by rfl⟩ : syracuseStep 131505677 = 49314629) B49314629
theorem B87670451 : Blo 2077435 87670451 := bstep (se 1 (by rfl) ⟨65752838, by rfl⟩ : syracuseStep 87670451 = 131505677) B131505677
theorem B58446967 : Blo 2077435 58446967 := bstep (se 1 (by rfl) ⟨43835225, by rfl⟩ : syracuseStep 58446967 = 87670451) B87670451
theorem B77929289 : Blo 2077435 77929289 := bstep (se 2 (by rfl) ⟨29223483, by rfl⟩ : syracuseStep 77929289 = 58446967) B58446967
theorem B51952859 : Blo 2077435 51952859 := bstep (se 1 (by rfl) ⟨38964644, by rfl⟩ : syracuseStep 51952859 = 77929289) B77929289
theorem B34635239 : Blo 2077435 34635239 := bstep (se 1 (by rfl) ⟨25976429, by rfl⟩ : syracuseStep 34635239 = 51952859) B51952859
theorem B23090159 : Blo 2077435 23090159 := bstep (se 1 (by rfl) ⟨17317619, by rfl⟩ : syracuseStep 23090159 = 34635239) B34635239
theorem B15393439 : Blo 2077435 15393439 := bstep (se 1 (by rfl) ⟨11545079, by rfl⟩ : syracuseStep 15393439 = 23090159) B23090159
theorem B20524585 : Blo 2077435 20524585 := bstep (se 2 (by rfl) ⟨7696719, by rfl⟩ : syracuseStep 20524585 = 15393439) B15393439
theorem B27366113 : Blo 2077435 27366113 := bstep (se 2 (by rfl) ⟨10262292, by rfl⟩ : syracuseStep 27366113 = 20524585) B20524585
theorem B18244075 : Blo 2077435 18244075 := bstep (se 1 (by rfl) ⟨13683056, by rfl⟩ : syracuseStep 18244075 = 27366113) B27366113
theorem B24325433 : Blo 2077435 24325433 := bstep (se 2 (by rfl) ⟨9122037, by rfl⟩ : syracuseStep 24325433 = 18244075) B18244075
theorem B16216955 : Blo 2077435 16216955 := bstep (se 1 (by rfl) ⟨12162716, by rfl⟩ : syracuseStep 16216955 = 24325433) B24325433
theorem B10811303 : Blo 2077435 10811303 := bstep (se 1 (by rfl) ⟨8108477, by rfl⟩ : syracuseStep 10811303 = 16216955) B16216955
theorem B7207535 : Blo 2077435 7207535 := bstep (se 1 (by rfl) ⟨5405651, by rfl⟩ : syracuseStep 7207535 = 10811303) B10811303
theorem B4805023 : Blo 2077435 4805023 := bstep (se 1 (by rfl) ⟨3603767, by rfl⟩ : syracuseStep 4805023 = 7207535) B7207535
theorem B6406697 : Blo 2077435 6406697 := bstep (se 2 (by rfl) ⟨2402511, by rfl⟩ : syracuseStep 6406697 = 4805023) B4805023
theorem B4271131 : Blo 2077435 4271131 := bstep (se 1 (by rfl) ⟨3203348, by rfl⟩ : syracuseStep 4271131 = 6406697) B6406697
theorem B5694841 : Blo 2077435 5694841 := bstep (se 2 (by rfl) ⟨2135565, by rfl⟩ : syracuseStep 5694841 = 4271131) B4271131
theorem B7593121 : Blo 2077435 7593121 := bstep (se 2 (by rfl) ⟨2847420, by rfl⟩ : syracuseStep 7593121 = 5694841) B5694841
theorem B40496645 : Blo 2077435 40496645 := bstep (se 4 (by rfl) ⟨3796560, by rfl⟩ : syracuseStep 40496645 = 7593121) B7593121
theorem B107991053 : Blo 2077435 107991053 := bstep (se 3 (by rfl) ⟨20248322, by rfl⟩ : syracuseStep 107991053 = 40496645) B40496645
theorem B71994035 : Blo 2077435 71994035 := bstep (se 1 (by rfl) ⟨53995526, by rfl⟩ : syracuseStep 71994035 = 107991053) B107991053
theorem B47996023 : Blo 2077435 47996023 := bstep (se 1 (by rfl) ⟨35997017, by rfl⟩ : syracuseStep 47996023 = 71994035) B71994035
theorem B63994697 : Blo 2077435 63994697 := bstep (se 2 (by rfl) ⟨23998011, by rfl⟩ : syracuseStep 63994697 = 47996023) B47996023
theorem B42663131 : Blo 2077435 42663131 := bstep (se 1 (by rfl) ⟨31997348, by rfl⟩ : syracuseStep 42663131 = 63994697) B63994697
theorem B28442087 : Blo 2077435 28442087 := bstep (se 1 (by rfl) ⟨21331565, by rfl⟩ : syracuseStep 28442087 = 42663131) B42663131
theorem B18961391 : Blo 2077435 18961391 := bstep (se 1 (by rfl) ⟨14221043, by rfl⟩ : syracuseStep 18961391 = 28442087) B28442087
theorem B12640927 : Blo 2077435 12640927 := bstep (se 1 (by rfl) ⟨9480695, by rfl⟩ : syracuseStep 12640927 = 18961391) B18961391
theorem B16854569 : Blo 2077435 16854569 := bstep (se 2 (by rfl) ⟨6320463, by rfl⟩ : syracuseStep 16854569 = 12640927) B12640927
theorem B11236379 : Blo 2077435 11236379 := bstep (se 1 (by rfl) ⟨8427284, by rfl⟩ : syracuseStep 11236379 = 16854569) B16854569
theorem B29963677 : Blo 2077435 29963677 := bstep (se 3 (by rfl) ⟨5618189, by rfl⟩ : syracuseStep 29963677 = 11236379) B11236379
theorem B39951569 : Blo 2077435 39951569 := bstep (se 2 (by rfl) ⟨14981838, by rfl⟩ : syracuseStep 39951569 = 29963677) B29963677
theorem B26634379 : Blo 2077435 26634379 := bstep (se 1 (by rfl) ⟨19975784, by rfl⟩ : syracuseStep 26634379 = 39951569) B39951569
theorem B35512505 : Blo 2077435 35512505 := bstep (se 2 (by rfl) ⟨13317189, by rfl⟩ : syracuseStep 35512505 = 26634379) B26634379
theorem B23675003 : Blo 2077435 23675003 := bstep (se 1 (by rfl) ⟨17756252, by rfl⟩ : syracuseStep 23675003 = 35512505) B35512505
theorem B15783335 : Blo 2077435 15783335 := bstep (se 1 (by rfl) ⟨11837501, by rfl⟩ : syracuseStep 15783335 = 23675003) B23675003
theorem B10522223 : Blo 2077435 10522223 := bstep (se 1 (by rfl) ⟨7891667, by rfl⟩ : syracuseStep 10522223 = 15783335) B15783335
theorem B7014815 : Blo 2077435 7014815 := bstep (se 1 (by rfl) ⟨5261111, by rfl⟩ : syracuseStep 7014815 = 10522223) B10522223
theorem B4676543 : Blo 2077435 4676543 := bstep (se 1 (by rfl) ⟨3507407, by rfl⟩ : syracuseStep 4676543 = 7014815) B7014815
theorem B3117695 : Blo 2077435 3117695 := bstep (se 1 (by rfl) ⟨2338271, by rfl⟩ : syracuseStep 3117695 = 4676543) B4676543
theorem B2078463 : Blo 2077435 2078463 := bstep (se 1 (by rfl) ⟨1558847, by rfl⟩ : syracuseStep 2078463 = 3117695) B3117695
theorem B3117701 : Blo 2077435 3117701 := bbase (se 4 (by rfl) ⟨292284, by rfl⟩ : syracuseStep 3117701 = 584569) (by norm_num)
theorem B2078467 : Blo 2077435 2078467 := bstep (se 1 (by rfl) ⟨1558850, by rfl⟩ : syracuseStep 2078467 = 3117701) B3117701
theorem B3507421 : Blo 2077435 3507421 := bbase (se 3 (by rfl) ⟨657641, by rfl⟩ : syracuseStep 3507421 = 1315283) (by norm_num)
theorem B4676561 : Blo 2077435 4676561 := bstep (se 2 (by rfl) ⟨1753710, by rfl⟩ : syracuseStep 4676561 = 3507421) B3507421
theorem B3117707 : Blo 2077435 3117707 := bstep (se 1 (by rfl) ⟨2338280, by rfl⟩ : syracuseStep 3117707 = 4676561) B4676561
theorem B2078471 : Blo 2077435 2078471 := bstep (se 1 (by rfl) ⟨1558853, by rfl⟩ : syracuseStep 2078471 = 3117707) B3117707
theorem B2338285 : Blo 2077435 2338285 := bbase (se 3 (by rfl) ⟨438428, by rfl⟩ : syracuseStep 2338285 = 876857) (by norm_num)
theorem B3117713 : Blo 2077435 3117713 := bstep (se 2 (by rfl) ⟨1169142, by rfl⟩ : syracuseStep 3117713 = 2338285) B2338285
theorem B2078475 : Blo 2077435 2078475 := bstep (se 1 (by rfl) ⟨1558856, by rfl⟩ : syracuseStep 2078475 = 3117713) B3117713
theorem B7014869 : Blo 2077435 7014869 := bbase (se 7 (by rfl) ⟨82205, by rfl⟩ : syracuseStep 7014869 = 164411) (by norm_num)
theorem B4676579 : Blo 2077435 4676579 := bstep (se 1 (by rfl) ⟨3507434, by rfl⟩ : syracuseStep 4676579 = 7014869) B7014869
theorem B3117719 : Blo 2077435 3117719 := bstep (se 1 (by rfl) ⟨2338289, by rfl⟩ : syracuseStep 3117719 = 4676579) B4676579
theorem B2078479 : Blo 2077435 2078479 := bstep (se 1 (by rfl) ⟨1558859, by rfl⟩ : syracuseStep 2078479 = 3117719) B3117719
theorem B3117725 : Blo 2077435 3117725 := bbase (se 3 (by rfl) ⟨584573, by rfl⟩ : syracuseStep 3117725 = 1169147) (by norm_num)
theorem B2078483 : Blo 2077435 2078483 := bstep (se 1 (by rfl) ⟨1558862, by rfl⟩ : syracuseStep 2078483 = 3117725) B3117725
theorem B4676597 : Blo 2077435 4676597 := bbase (se 5 (by rfl) ⟨219215, by rfl⟩ : syracuseStep 4676597 = 438431) (by norm_num)
theorem B3117731 : Blo 2077435 3117731 := bstep (se 1 (by rfl) ⟨2338298, by rfl⟩ : syracuseStep 3117731 = 4676597) B4676597
theorem B2078487 : Blo 2077435 2078487 := bstep (se 1 (by rfl) ⟨1558865, by rfl⟩ : syracuseStep 2078487 = 3117731) B3117731
theorem B56884949 : Blo 2077435 56884949 := bbase (se 7 (by rfl) ⟨666620, by rfl⟩ : syracuseStep 56884949 = 1333241) (by norm_num)
theorem B37923299 : Blo 2077435 37923299 := bstep (se 1 (by rfl) ⟨28442474, by rfl⟩ : syracuseStep 37923299 = 56884949) B56884949
theorem B25282199 : Blo 2077435 25282199 := bstep (se 1 (by rfl) ⟨18961649, by rfl⟩ : syracuseStep 25282199 = 37923299) B37923299
theorem B16854799 : Blo 2077435 16854799 := bstep (se 1 (by rfl) ⟨12641099, by rfl⟩ : syracuseStep 16854799 = 25282199) B25282199
theorem B22473065 : Blo 2077435 22473065 := bstep (se 2 (by rfl) ⟨8427399, by rfl⟩ : syracuseStep 22473065 = 16854799) B16854799
theorem B59928173 : Blo 2077435 59928173 := bstep (se 3 (by rfl) ⟨11236532, by rfl⟩ : syracuseStep 59928173 = 22473065) B22473065
theorem B39952115 : Blo 2077435 39952115 := bstep (se 1 (by rfl) ⟨29964086, by rfl⟩ : syracuseStep 39952115 = 59928173) B59928173
theorem B26634743 : Blo 2077435 26634743 := bstep (se 1 (by rfl) ⟨19976057, by rfl⟩ : syracuseStep 26634743 = 39952115) B39952115
theorem B17756495 : Blo 2077435 17756495 := bstep (se 1 (by rfl) ⟨13317371, by rfl⟩ : syracuseStep 17756495 = 26634743) B26634743
theorem B11837663 : Blo 2077435 11837663 := bstep (se 1 (by rfl) ⟨8878247, by rfl⟩ : syracuseStep 11837663 = 17756495) B17756495
theorem B7891775 : Blo 2077435 7891775 := bstep (se 1 (by rfl) ⟨5918831, by rfl⟩ : syracuseStep 7891775 = 11837663) B11837663
theorem B5261183 : Blo 2077435 5261183 := bstep (se 1 (by rfl) ⟨3945887, by rfl⟩ : syracuseStep 5261183 = 7891775) B7891775
theorem B3507455 : Blo 2077435 3507455 := bstep (se 1 (by rfl) ⟨2630591, by rfl⟩ : syracuseStep 3507455 = 5261183) B5261183
theorem B2338303 : Blo 2077435 2338303 := bstep (se 1 (by rfl) ⟨1753727, by rfl⟩ : syracuseStep 2338303 = 3507455) B3507455
theorem B3117737 : Blo 2077435 3117737 := bstep (se 2 (by rfl) ⟨1169151, by rfl⟩ : syracuseStep 3117737 = 2338303) B2338303
theorem B2078491 : Blo 2077435 2078491 := bstep (se 1 (by rfl) ⟨1558868, by rfl⟩ : syracuseStep 2078491 = 3117737) B3117737
theorem B2959421 : Blo 2077435 2959421 := bbase (se 3 (by rfl) ⟨554891, by rfl⟩ : syracuseStep 2959421 = 1109783) (by norm_num)
theorem B7891789 : Blo 2077435 7891789 := bstep (se 3 (by rfl) ⟨1479710, by rfl⟩ : syracuseStep 7891789 = 2959421) B2959421
theorem B10522385 : Blo 2077435 10522385 := bstep (se 2 (by rfl) ⟨3945894, by rfl⟩ : syracuseStep 10522385 = 7891789) B7891789
theorem B7014923 : Blo 2077435 7014923 := bstep (se 1 (by rfl) ⟨5261192, by rfl⟩ : syracuseStep 7014923 = 10522385) B10522385
theorem B4676615 : Blo 2077435 4676615 := bstep (se 1 (by rfl) ⟨3507461, by rfl⟩ : syracuseStep 4676615 = 7014923) B7014923
theorem B3117743 : Blo 2077435 3117743 := bstep (se 1 (by rfl) ⟨2338307, by rfl⟩ : syracuseStep 3117743 = 4676615) B4676615
theorem B2078495 : Blo 2077435 2078495 := bstep (se 1 (by rfl) ⟨1558871, by rfl⟩ : syracuseStep 2078495 = 3117743) B3117743
theorem B3117749 : Blo 2077435 3117749 := bbase (se 5 (by rfl) ⟨146144, by rfl⟩ : syracuseStep 3117749 = 292289) (by norm_num)
theorem B2078499 : Blo 2077435 2078499 := bstep (se 1 (by rfl) ⟨1558874, by rfl⟩ : syracuseStep 2078499 = 3117749) B3117749
theorem B5261213 : Blo 2077435 5261213 := bbase (se 3 (by rfl) ⟨986477, by rfl⟩ : syracuseStep 5261213 = 1972955) (by norm_num)
theorem B3507475 : Blo 2077435 3507475 := bstep (se 1 (by rfl) ⟨2630606, by rfl⟩ : syracuseStep 3507475 = 5261213) B5261213
theorem B4676633 : Blo 2077435 4676633 := bstep (se 2 (by rfl) ⟨1753737, by rfl⟩ : syracuseStep 4676633 = 3507475) B3507475
theorem B3117755 : Blo 2077435 3117755 := bstep (se 1 (by rfl) ⟨2338316, by rfl⟩ : syracuseStep 3117755 = 4676633) B4676633
theorem B2078503 : Blo 2077435 2078503 := bstep (se 1 (by rfl) ⟨1558877, by rfl⟩ : syracuseStep 2078503 = 3117755) B3117755
theorem B2338321 : Blo 2077435 2338321 := bbase (se 2 (by rfl) ⟨876870, by rfl⟩ : syracuseStep 2338321 = 1753741) (by norm_num)
theorem B3117761 : Blo 2077435 3117761 := bstep (se 2 (by rfl) ⟨1169160, by rfl⟩ : syracuseStep 3117761 = 2338321) B2338321
theorem B2078507 : Blo 2077435 2078507 := bstep (se 1 (by rfl) ⟨1558880, by rfl⟩ : syracuseStep 2078507 = 3117761) B3117761
theorem B3945925 : Blo 2077435 3945925 := bbase (se 4 (by rfl) ⟨369930, by rfl⟩ : syracuseStep 3945925 = 739861) (by norm_num)
theorem B5261233 : Blo 2077435 5261233 := bstep (se 2 (by rfl) ⟨1972962, by rfl⟩ : syracuseStep 5261233 = 3945925) B3945925
theorem B7014977 : Blo 2077435 7014977 := bstep (se 2 (by rfl) ⟨2630616, by rfl⟩ : syracuseStep 7014977 = 5261233) B5261233
theorem B4676651 : Blo 2077435 4676651 := bstep (se 1 (by rfl) ⟨3507488, by rfl⟩ : syracuseStep 4676651 = 7014977) B7014977
theorem B3117767 : Blo 2077435 3117767 := bstep (se 1 (by rfl) ⟨2338325, by rfl⟩ : syracuseStep 3117767 = 4676651) B4676651
theorem B2078511 : Blo 2077435 2078511 := bstep (se 1 (by rfl) ⟨1558883, by rfl⟩ : syracuseStep 2078511 = 3117767) B3117767
theorem B3117773 : Blo 2077435 3117773 := bbase (se 3 (by rfl) ⟨584582, by rfl⟩ : syracuseStep 3117773 = 1169165) (by norm_num)
theorem B2078515 : Blo 2077435 2078515 := bstep (se 1 (by rfl) ⟨1558886, by rfl⟩ : syracuseStep 2078515 = 3117773) B3117773
theorem B4676669 : Blo 2077435 4676669 := bbase (se 3 (by rfl) ⟨876875, by rfl⟩ : syracuseStep 4676669 = 1753751) (by norm_num)
theorem B3117779 : Blo 2077435 3117779 := bstep (se 1 (by rfl) ⟨2338334, by rfl⟩ : syracuseStep 3117779 = 4676669) B4676669
theorem B2078519 : Blo 2077435 2078519 := bstep (se 1 (by rfl) ⟨1558889, by rfl⟩ : syracuseStep 2078519 = 3117779) B3117779
theorem B3507509 : Blo 2077435 3507509 := bbase (se 5 (by rfl) ⟨164414, by rfl⟩ : syracuseStep 3507509 = 328829) (by norm_num)
theorem B2338339 : Blo 2077435 2338339 := bstep (se 1 (by rfl) ⟨1753754, by rfl⟩ : syracuseStep 2338339 = 3507509) B3507509
theorem B3117785 : Blo 2077435 3117785 := bstep (se 2 (by rfl) ⟨1169169, by rfl⟩ : syracuseStep 3117785 = 2338339) B2338339
theorem B2078523 : Blo 2077435 2078523 := bstep (se 1 (by rfl) ⟨1558892, by rfl⟩ : syracuseStep 2078523 = 3117785) B3117785
theorem B5918933 : Blo 2077435 5918933 := bbase (se 7 (by rfl) ⟨69362, by rfl⟩ : syracuseStep 5918933 = 138725) (by norm_num)
theorem B15783821 : Blo 2077435 15783821 := bstep (se 3 (by rfl) ⟨2959466, by rfl⟩ : syracuseStep 15783821 = 5918933) B5918933
theorem B10522547 : Blo 2077435 10522547 := bstep (se 1 (by rfl) ⟨7891910, by rfl⟩ : syracuseStep 10522547 = 15783821) B15783821
theorem B7015031 : Blo 2077435 7015031 := bstep (se 1 (by rfl) ⟨5261273, by rfl⟩ : syracuseStep 7015031 = 10522547) B10522547
theorem B4676687 : Blo 2077435 4676687 := bstep (se 1 (by rfl) ⟨3507515, by rfl⟩ : syracuseStep 4676687 = 7015031) B7015031
theorem B3117791 : Blo 2077435 3117791 := bstep (se 1 (by rfl) ⟨2338343, by rfl⟩ : syracuseStep 3117791 = 4676687) B4676687
theorem B2078527 : Blo 2077435 2078527 := bstep (se 1 (by rfl) ⟨1558895, by rfl⟩ : syracuseStep 2078527 = 3117791) B3117791
theorem B3117797 : Blo 2077435 3117797 := bbase (se 4 (by rfl) ⟨292293, by rfl⟩ : syracuseStep 3117797 = 584587) (by norm_num)
theorem B2078531 : Blo 2077435 2078531 := bstep (se 1 (by rfl) ⟨1558898, by rfl⟩ : syracuseStep 2078531 = 3117797) B3117797
theorem B2219609 : Blo 2077435 2219609 := bbase (se 2 (by rfl) ⟨832353, by rfl⟩ : syracuseStep 2219609 = 1664707) (by norm_num)
theorem B5918957 : Blo 2077435 5918957 := bstep (se 3 (by rfl) ⟨1109804, by rfl⟩ : syracuseStep 5918957 = 2219609) B2219609
theorem B3945971 : Blo 2077435 3945971 := bstep (se 1 (by rfl) ⟨2959478, by rfl⟩ : syracuseStep 3945971 = 5918957) B5918957
theorem B2630647 : Blo 2077435 2630647 := bstep (se 1 (by rfl) ⟨1972985, by rfl⟩ : syracuseStep 2630647 = 3945971) B3945971
theorem B3507529 : Blo 2077435 3507529 := bstep (se 2 (by rfl) ⟨1315323, by rfl⟩ : syracuseStep 3507529 = 2630647) B2630647
theorem B4676705 : Blo 2077435 4676705 := bstep (se 2 (by rfl) ⟨1753764, by rfl⟩ : syracuseStep 4676705 = 3507529) B3507529
theorem B3117803 : Blo 2077435 3117803 := bstep (se 1 (by rfl) ⟨2338352, by rfl⟩ : syracuseStep 3117803 = 4676705) B4676705
theorem B2078535 : Blo 2077435 2078535 := bstep (se 1 (by rfl) ⟨1558901, by rfl⟩ : syracuseStep 2078535 = 3117803) B3117803
theorem B2338357 : Blo 2077435 2338357 := bbase (se 5 (by rfl) ⟨109610, by rfl⟩ : syracuseStep 2338357 = 219221) (by norm_num)
theorem B3117809 : Blo 2077435 3117809 := bstep (se 2 (by rfl) ⟨1169178, by rfl⟩ : syracuseStep 3117809 = 2338357) B2338357
theorem B2078539 : Blo 2077435 2078539 := bstep (se 1 (by rfl) ⟨1558904, by rfl⟩ : syracuseStep 2078539 = 3117809) B3117809
theorem B2630657 : Blo 2077435 2630657 := bbase (se 2 (by rfl) ⟨986496, by rfl⟩ : syracuseStep 2630657 = 1972993) (by norm_num)
theorem B7015085 : Blo 2077435 7015085 := bstep (se 3 (by rfl) ⟨1315328, by rfl⟩ : syracuseStep 7015085 = 2630657) B2630657
theorem B4676723 : Blo 2077435 4676723 := bstep (se 1 (by rfl) ⟨3507542, by rfl⟩ : syracuseStep 4676723 = 7015085) B7015085
theorem B3117815 : Blo 2077435 3117815 := bstep (se 1 (by rfl) ⟨2338361, by rfl⟩ : syracuseStep 3117815 = 4676723) B4676723
theorem B2078543 : Blo 2077435 2078543 := bstep (se 1 (by rfl) ⟨1558907, by rfl⟩ : syracuseStep 2078543 = 3117815) B3117815
theorem B3117821 : Blo 2077435 3117821 := bbase (se 3 (by rfl) ⟨584591, by rfl⟩ : syracuseStep 3117821 = 1169183) (by norm_num)
theorem B2078547 : Blo 2077435 2078547 := bstep (se 1 (by rfl) ⟨1558910, by rfl⟩ : syracuseStep 2078547 = 3117821) B3117821
theorem B4676741 : Blo 2077435 4676741 := bbase (se 4 (by rfl) ⟨438444, by rfl⟩ : syracuseStep 4676741 = 876889) (by norm_num)
theorem B3117827 : Blo 2077435 3117827 := bstep (se 1 (by rfl) ⟨2338370, by rfl⟩ : syracuseStep 3117827 = 4676741) B4676741
theorem B2078551 : Blo 2077435 2078551 := bstep (se 1 (by rfl) ⟨1558913, by rfl⟩ : syracuseStep 2078551 = 3117827) B3117827
theorem B4439261 : Blo 2077435 4439261 := bbase (se 3 (by rfl) ⟨832361, by rfl⟩ : syracuseStep 4439261 = 1664723) (by norm_num)
theorem B2959507 : Blo 2077435 2959507 := bstep (se 1 (by rfl) ⟨2219630, by rfl⟩ : syracuseStep 2959507 = 4439261) B4439261
theorem B3946009 : Blo 2077435 3946009 := bstep (se 2 (by rfl) ⟨1479753, by rfl⟩ : syracuseStep 3946009 = 2959507) B2959507
theorem B5261345 : Blo 2077435 5261345 := bstep (se 2 (by rfl) ⟨1973004, by rfl⟩ : syracuseStep 5261345 = 3946009) B3946009
theorem B3507563 : Blo 2077435 3507563 := bstep (se 1 (by rfl) ⟨2630672, by rfl⟩ : syracuseStep 3507563 = 5261345) B5261345
theorem B2338375 : Blo 2077435 2338375 := bstep (se 1 (by rfl) ⟨1753781, by rfl⟩ : syracuseStep 2338375 = 3507563) B3507563
theorem B3117833 : Blo 2077435 3117833 := bstep (se 2 (by rfl) ⟨1169187, by rfl⟩ : syracuseStep 3117833 = 2338375) B2338375
theorem B2078555 : Blo 2077435 2078555 := bstep (se 1 (by rfl) ⟨1558916, by rfl⟩ : syracuseStep 2078555 = 3117833) B3117833
theorem B10522709 : Blo 2077435 10522709 := bbase (se 8 (by rfl) ⟨61656, by rfl⟩ : syracuseStep 10522709 = 123313) (by norm_num)
theorem B7015139 : Blo 2077435 7015139 := bstep (se 1 (by rfl) ⟨5261354, by rfl⟩ : syracuseStep 7015139 = 10522709) B10522709
theorem B4676759 : Blo 2077435 4676759 := bstep (se 1 (by rfl) ⟨3507569, by rfl⟩ : syracuseStep 4676759 = 7015139) B7015139
theorem B3117839 : Blo 2077435 3117839 := bstep (se 1 (by rfl) ⟨2338379, by rfl⟩ : syracuseStep 3117839 = 4676759) B4676759
theorem B2078559 : Blo 2077435 2078559 := bstep (se 1 (by rfl) ⟨1558919, by rfl⟩ : syracuseStep 2078559 = 3117839) B3117839
theorem B3117845 : Blo 2077435 3117845 := bbase (se 6 (by rfl) ⟨73074, by rfl⟩ : syracuseStep 3117845 = 146149) (by norm_num)
theorem B2078563 : Blo 2077435 2078563 := bstep (se 1 (by rfl) ⟨1558922, by rfl⟩ : syracuseStep 2078563 = 3117845) B3117845
theorem B3124373 : Blo 2077435 3124373 := bbase (se 6 (by rfl) ⟨73227, by rfl⟩ : syracuseStep 3124373 = 146455) (by norm_num)
theorem B33326645 : Blo 2077435 33326645 := bstep (se 5 (by rfl) ⟨1562186, by rfl⟩ : syracuseStep 33326645 = 3124373) B3124373
theorem B88871053 : Blo 2077435 88871053 := bstep (se 3 (by rfl) ⟨16663322, by rfl⟩ : syracuseStep 88871053 = 33326645) B33326645
theorem B118494737 : Blo 2077435 118494737 := bstep (se 2 (by rfl) ⟨44435526, by rfl⟩ : syracuseStep 118494737 = 88871053) B88871053
theorem B78996491 : Blo 2077435 78996491 := bstep (se 1 (by rfl) ⟨59247368, by rfl⟩ : syracuseStep 78996491 = 118494737) B118494737
theorem B52664327 : Blo 2077435 52664327 := bstep (se 1 (by rfl) ⟨39498245, by rfl⟩ : syracuseStep 52664327 = 78996491) B78996491
theorem B35109551 : Blo 2077435 35109551 := bstep (se 1 (by rfl) ⟨26332163, by rfl⟩ : syracuseStep 35109551 = 52664327) B52664327
theorem B23406367 : Blo 2077435 23406367 := bstep (se 1 (by rfl) ⟨17554775, by rfl⟩ : syracuseStep 23406367 = 35109551) B35109551
theorem B31208489 : Blo 2077435 31208489 := bstep (se 2 (by rfl) ⟨11703183, by rfl⟩ : syracuseStep 31208489 = 23406367) B23406367
theorem B20805659 : Blo 2077435 20805659 := bstep (se 1 (by rfl) ⟨15604244, by rfl⟩ : syracuseStep 20805659 = 31208489) B31208489
theorem B13870439 : Blo 2077435 13870439 := bstep (se 1 (by rfl) ⟨10402829, by rfl⟩ : syracuseStep 13870439 = 20805659) B20805659
theorem B9246959 : Blo 2077435 9246959 := bstep (se 1 (by rfl) ⟨6935219, by rfl⟩ : syracuseStep 9246959 = 13870439) B13870439
theorem B6164639 : Blo 2077435 6164639 := bstep (se 1 (by rfl) ⟨4623479, by rfl⟩ : syracuseStep 6164639 = 9246959) B9246959
theorem B4109759 : Blo 2077435 4109759 := bstep (se 1 (by rfl) ⟨3082319, by rfl⟩ : syracuseStep 4109759 = 6164639) B6164639
theorem B2739839 : Blo 2077435 2739839 := bstep (se 1 (by rfl) ⟨2054879, by rfl⟩ : syracuseStep 2739839 = 4109759) B4109759
theorem B7306237 : Blo 2077435 7306237 := bstep (se 3 (by rfl) ⟨1369919, by rfl⟩ : syracuseStep 7306237 = 2739839) B2739839
theorem B9741649 : Blo 2077435 9741649 := bstep (se 2 (by rfl) ⟨3653118, by rfl⟩ : syracuseStep 9741649 = 7306237) B7306237
theorem B12988865 : Blo 2077435 12988865 := bstep (se 2 (by rfl) ⟨4870824, by rfl⟩ : syracuseStep 12988865 = 9741649) B9741649
theorem B8659243 : Blo 2077435 8659243 := bstep (se 1 (by rfl) ⟨6494432, by rfl⟩ : syracuseStep 8659243 = 12988865) B12988865
theorem B46182629 : Blo 2077435 46182629 := bstep (se 4 (by rfl) ⟨4329621, by rfl⟩ : syracuseStep 46182629 = 8659243) B8659243
theorem B30788419 : Blo 2077435 30788419 := bstep (se 1 (by rfl) ⟨23091314, by rfl⟩ : syracuseStep 30788419 = 46182629) B46182629
theorem B41051225 : Blo 2077435 41051225 := bstep (se 2 (by rfl) ⟨15394209, by rfl⟩ : syracuseStep 41051225 = 30788419) B30788419
theorem B27367483 : Blo 2077435 27367483 := bstep (se 1 (by rfl) ⟨20525612, by rfl⟩ : syracuseStep 27367483 = 41051225) B41051225
theorem B36489977 : Blo 2077435 36489977 := bstep (se 2 (by rfl) ⟨13683741, by rfl⟩ : syracuseStep 36489977 = 27367483) B27367483
theorem B24326651 : Blo 2077435 24326651 := bstep (se 1 (by rfl) ⟨18244988, by rfl⟩ : syracuseStep 24326651 = 36489977) B36489977
theorem B16217767 : Blo 2077435 16217767 := bstep (se 1 (by rfl) ⟨12163325, by rfl⟩ : syracuseStep 16217767 = 24326651) B24326651
theorem B21623689 : Blo 2077435 21623689 := bstep (se 2 (by rfl) ⟨8108883, by rfl⟩ : syracuseStep 21623689 = 16217767) B16217767
theorem B115326341 : Blo 2077435 115326341 := bstep (se 4 (by rfl) ⟨10811844, by rfl⟩ : syracuseStep 115326341 = 21623689) B21623689
theorem B76884227 : Blo 2077435 76884227 := bstep (se 1 (by rfl) ⟨57663170, by rfl⟩ : syracuseStep 76884227 = 115326341) B115326341
theorem B51256151 : Blo 2077435 51256151 := bstep (se 1 (by rfl) ⟨38442113, by rfl⟩ : syracuseStep 51256151 = 76884227) B76884227
theorem B34170767 : Blo 2077435 34170767 := bstep (se 1 (by rfl) ⟨25628075, by rfl⟩ : syracuseStep 34170767 = 51256151) B51256151
theorem B22780511 : Blo 2077435 22780511 := bstep (se 1 (by rfl) ⟨17085383, by rfl⟩ : syracuseStep 22780511 = 34170767) B34170767
theorem B15187007 : Blo 2077435 15187007 := bstep (se 1 (by rfl) ⟨11390255, by rfl⟩ : syracuseStep 15187007 = 22780511) B22780511
theorem B10124671 : Blo 2077435 10124671 := bstep (se 1 (by rfl) ⟨7593503, by rfl⟩ : syracuseStep 10124671 = 15187007) B15187007
theorem B13499561 : Blo 2077435 13499561 := bstep (se 2 (by rfl) ⟨5062335, by rfl⟩ : syracuseStep 13499561 = 10124671) B10124671
theorem B8999707 : Blo 2077435 8999707 := bstep (se 1 (by rfl) ⟨6749780, by rfl⟩ : syracuseStep 8999707 = 13499561) B13499561
theorem B11999609 : Blo 2077435 11999609 := bstep (se 2 (by rfl) ⟨4499853, by rfl⟩ : syracuseStep 11999609 = 8999707) B8999707
theorem B7999739 : Blo 2077435 7999739 := bstep (se 1 (by rfl) ⟨5999804, by rfl⟩ : syracuseStep 7999739 = 11999609) B11999609
theorem B5333159 : Blo 2077435 5333159 := bstep (se 1 (by rfl) ⟨3999869, by rfl⟩ : syracuseStep 5333159 = 7999739) B7999739
theorem B14221757 : Blo 2077435 14221757 := bstep (se 3 (by rfl) ⟨2666579, by rfl⟩ : syracuseStep 14221757 = 5333159) B5333159
theorem B37924685 : Blo 2077435 37924685 := bstep (se 3 (by rfl) ⟨7110878, by rfl⟩ : syracuseStep 37924685 = 14221757) B14221757
theorem B25283123 : Blo 2077435 25283123 := bstep (se 1 (by rfl) ⟨18962342, by rfl⟩ : syracuseStep 25283123 = 37924685) B37924685
theorem B16855415 : Blo 2077435 16855415 := bstep (se 1 (by rfl) ⟨12641561, by rfl⟩ : syracuseStep 16855415 = 25283123) B25283123
theorem B11236943 : Blo 2077435 11236943 := bstep (se 1 (by rfl) ⟨8427707, by rfl⟩ : syracuseStep 11236943 = 16855415) B16855415
theorem B7491295 : Blo 2077435 7491295 := bstep (se 1 (by rfl) ⟨5618471, by rfl⟩ : syracuseStep 7491295 = 11236943) B11236943
theorem B39953573 : Blo 2077435 39953573 := bstep (se 4 (by rfl) ⟨3745647, by rfl⟩ : syracuseStep 39953573 = 7491295) B7491295
theorem B26635715 : Blo 2077435 26635715 := bstep (se 1 (by rfl) ⟨19976786, by rfl⟩ : syracuseStep 26635715 = 39953573) B39953573
theorem B17757143 : Blo 2077435 17757143 := bstep (se 1 (by rfl) ⟨13317857, by rfl⟩ : syracuseStep 17757143 = 26635715) B26635715
theorem B11838095 : Blo 2077435 11838095 := bstep (se 1 (by rfl) ⟨8878571, by rfl⟩ : syracuseStep 11838095 = 17757143) B17757143
theorem B7892063 : Blo 2077435 7892063 := bstep (se 1 (by rfl) ⟨5919047, by rfl⟩ : syracuseStep 7892063 = 11838095) B11838095
theorem B5261375 : Blo 2077435 5261375 := bstep (se 1 (by rfl) ⟨3946031, by rfl⟩ : syracuseStep 5261375 = 7892063) B7892063
theorem B3507583 : Blo 2077435 3507583 := bstep (se 1 (by rfl) ⟨2630687, by rfl⟩ : syracuseStep 3507583 = 5261375) B5261375
theorem B4676777 : Blo 2077435 4676777 := bstep (se 2 (by rfl) ⟨1753791, by rfl⟩ : syracuseStep 4676777 = 3507583) B3507583
theorem B3117851 : Blo 2077435 3117851 := bstep (se 1 (by rfl) ⟨2338388, by rfl⟩ : syracuseStep 3117851 = 4676777) B4676777
theorem B2078567 : Blo 2077435 2078567 := bstep (se 1 (by rfl) ⟨1558925, by rfl⟩ : syracuseStep 2078567 = 3117851) B3117851
theorem B2338393 : Blo 2077435 2338393 := bbase (se 2 (by rfl) ⟨876897, by rfl⟩ : syracuseStep 2338393 = 1753795) (by norm_num)
theorem B3117857 : Blo 2077435 3117857 := bstep (se 2 (by rfl) ⟨1169196, by rfl⟩ : syracuseStep 3117857 = 2338393) B2338393
theorem B2078571 : Blo 2077435 2078571 := bstep (se 1 (by rfl) ⟨1558928, by rfl⟩ : syracuseStep 2078571 = 3117857) B3117857
theorem B2565713 : Blo 2077435 2565713 := bbase (se 2 (by rfl) ⟨962142, by rfl⟩ : syracuseStep 2565713 = 1924285) (by norm_num)
theorem B6841901 : Blo 2077435 6841901 := bstep (se 3 (by rfl) ⟨1282856, by rfl⟩ : syracuseStep 6841901 = 2565713) B2565713
theorem B4561267 : Blo 2077435 4561267 := bstep (se 1 (by rfl) ⟨3420950, by rfl⟩ : syracuseStep 4561267 = 6841901) B6841901
theorem B6081689 : Blo 2077435 6081689 := bstep (se 2 (by rfl) ⟨2280633, by rfl⟩ : syracuseStep 6081689 = 4561267) B4561267
theorem B4054459 : Blo 2077435 4054459 := bstep (se 1 (by rfl) ⟨3040844, by rfl⟩ : syracuseStep 4054459 = 6081689) B6081689
theorem B5405945 : Blo 2077435 5405945 := bstep (se 2 (by rfl) ⟨2027229, by rfl⟩ : syracuseStep 5405945 = 4054459) B4054459
theorem B57663413 : Blo 2077435 57663413 := bstep (se 5 (by rfl) ⟨2702972, by rfl⟩ : syracuseStep 57663413 = 5405945) B5405945
theorem B38442275 : Blo 2077435 38442275 := bstep (se 1 (by rfl) ⟨28831706, by rfl⟩ : syracuseStep 38442275 = 57663413) B57663413
theorem B25628183 : Blo 2077435 25628183 := bstep (se 1 (by rfl) ⟨19221137, by rfl⟩ : syracuseStep 25628183 = 38442275) B38442275
theorem B17085455 : Blo 2077435 17085455 := bstep (se 1 (by rfl) ⟨12814091, by rfl⟩ : syracuseStep 17085455 = 25628183) B25628183
theorem B11390303 : Blo 2077435 11390303 := bstep (se 1 (by rfl) ⟨8542727, by rfl⟩ : syracuseStep 11390303 = 17085455) B17085455
theorem B7593535 : Blo 2077435 7593535 := bstep (se 1 (by rfl) ⟨5695151, by rfl⟩ : syracuseStep 7593535 = 11390303) B11390303
theorem B10124713 : Blo 2077435 10124713 := bstep (se 2 (by rfl) ⟨3796767, by rfl⟩ : syracuseStep 10124713 = 7593535) B7593535
theorem B13499617 : Blo 2077435 13499617 := bstep (se 2 (by rfl) ⟨5062356, by rfl⟩ : syracuseStep 13499617 = 10124713) B10124713
theorem B17999489 : Blo 2077435 17999489 := bstep (se 2 (by rfl) ⟨6749808, by rfl⟩ : syracuseStep 17999489 = 13499617) B13499617
theorem B11999659 : Blo 2077435 11999659 := bstep (se 1 (by rfl) ⟨8999744, by rfl⟩ : syracuseStep 11999659 = 17999489) B17999489
theorem B15999545 : Blo 2077435 15999545 := bstep (se 2 (by rfl) ⟨5999829, by rfl⟩ : syracuseStep 15999545 = 11999659) B11999659
theorem B10666363 : Blo 2077435 10666363 := bstep (se 1 (by rfl) ⟨7999772, by rfl⟩ : syracuseStep 10666363 = 15999545) B15999545
theorem B14221817 : Blo 2077435 14221817 := bstep (se 2 (by rfl) ⟨5333181, by rfl⟩ : syracuseStep 14221817 = 10666363) B10666363
theorem B9481211 : Blo 2077435 9481211 := bstep (se 1 (by rfl) ⟨7110908, by rfl⟩ : syracuseStep 9481211 = 14221817) B14221817
theorem B6320807 : Blo 2077435 6320807 := bstep (se 1 (by rfl) ⟨4740605, by rfl⟩ : syracuseStep 6320807 = 9481211) B9481211
theorem B4213871 : Blo 2077435 4213871 := bstep (se 1 (by rfl) ⟨3160403, by rfl⟩ : syracuseStep 4213871 = 6320807) B6320807
theorem B2809247 : Blo 2077435 2809247 := bstep (se 1 (by rfl) ⟨2106935, by rfl⟩ : syracuseStep 2809247 = 4213871) B4213871
theorem B7491325 : Blo 2077435 7491325 := bstep (se 3 (by rfl) ⟨1404623, by rfl⟩ : syracuseStep 7491325 = 2809247) B2809247
theorem B9988433 : Blo 2077435 9988433 := bstep (se 2 (by rfl) ⟨3745662, by rfl⟩ : syracuseStep 9988433 = 7491325) B7491325
theorem B6658955 : Blo 2077435 6658955 := bstep (se 1 (by rfl) ⟨4994216, by rfl⟩ : syracuseStep 6658955 = 9988433) B9988433
theorem B4439303 : Blo 2077435 4439303 := bstep (se 1 (by rfl) ⟨3329477, by rfl⟩ : syracuseStep 4439303 = 6658955) B6658955
theorem B2959535 : Blo 2077435 2959535 := bstep (se 1 (by rfl) ⟨2219651, by rfl⟩ : syracuseStep 2959535 = 4439303) B4439303
theorem B7892093 : Blo 2077435 7892093 := bstep (se 3 (by rfl) ⟨1479767, by rfl⟩ : syracuseStep 7892093 = 2959535) B2959535
theorem B5261395 : Blo 2077435 5261395 := bstep (se 1 (by rfl) ⟨3946046, by rfl⟩ : syracuseStep 5261395 = 7892093) B7892093
theorem B7015193 : Blo 2077435 7015193 := bstep (se 2 (by rfl) ⟨2630697, by rfl⟩ : syracuseStep 7015193 = 5261395) B5261395
theorem B4676795 : Blo 2077435 4676795 := bstep (se 1 (by rfl) ⟨3507596, by rfl⟩ : syracuseStep 4676795 = 7015193) B7015193
theorem B3117863 : Blo 2077435 3117863 := bstep (se 1 (by rfl) ⟨2338397, by rfl⟩ : syracuseStep 3117863 = 4676795) B4676795
theorem B2078575 : Blo 2077435 2078575 := bstep (se 1 (by rfl) ⟨1558931, by rfl⟩ : syracuseStep 2078575 = 3117863) B3117863
theorem B3117869 : Blo 2077435 3117869 := bbase (se 3 (by rfl) ⟨584600, by rfl⟩ : syracuseStep 3117869 = 1169201) (by norm_num)
theorem B2078579 : Blo 2077435 2078579 := bstep (se 1 (by rfl) ⟨1558934, by rfl⟩ : syracuseStep 2078579 = 3117869) B3117869
theorem B4676813 : Blo 2077435 4676813 := bbase (se 3 (by rfl) ⟨876902, by rfl⟩ : syracuseStep 4676813 = 1753805) (by norm_num)
theorem B3117875 : Blo 2077435 3117875 := bstep (se 1 (by rfl) ⟨2338406, by rfl⟩ : syracuseStep 3117875 = 4676813) B4676813
theorem B2078583 : Blo 2077435 2078583 := bstep (se 1 (by rfl) ⟨1558937, by rfl⟩ : syracuseStep 2078583 = 3117875) B3117875
theorem B2630713 : Blo 2077435 2630713 := bbase (se 2 (by rfl) ⟨986517, by rfl⟩ : syracuseStep 2630713 = 1973035) (by norm_num)
theorem B3507617 : Blo 2077435 3507617 := bstep (se 2 (by rfl) ⟨1315356, by rfl⟩ : syracuseStep 3507617 = 2630713) B2630713
theorem B2338411 : Blo 2077435 2338411 := bstep (se 1 (by rfl) ⟨1753808, by rfl⟩ : syracuseStep 2338411 = 3507617) B3507617
theorem B3117881 : Blo 2077435 3117881 := bstep (se 2 (by rfl) ⟨1169205, by rfl⟩ : syracuseStep 3117881 = 2338411) B2338411
theorem B2078587 : Blo 2077435 2078587 := bstep (se 1 (by rfl) ⟨1558940, by rfl⟩ : syracuseStep 2078587 = 3117881) B3117881
theorem B3999917 : Blo 2077435 3999917 := bbase (se 3 (by rfl) ⟨749984, by rfl⟩ : syracuseStep 3999917 = 1499969) (by norm_num)
theorem B2666611 : Blo 2077435 2666611 := bstep (se 1 (by rfl) ⟨1999958, by rfl⟩ : syracuseStep 2666611 = 3999917) B3999917
theorem B14221925 : Blo 2077435 14221925 := bstep (se 4 (by rfl) ⟨1333305, by rfl⟩ : syracuseStep 14221925 = 2666611) B2666611
theorem B9481283 : Blo 2077435 9481283 := bstep (se 1 (by rfl) ⟨7110962, by rfl⟩ : syracuseStep 9481283 = 14221925) B14221925
theorem B6320855 : Blo 2077435 6320855 := bstep (se 1 (by rfl) ⟨4740641, by rfl⟩ : syracuseStep 6320855 = 9481283) B9481283
theorem B4213903 : Blo 2077435 4213903 := bstep (se 1 (by rfl) ⟨3160427, by rfl⟩ : syracuseStep 4213903 = 6320855) B6320855
theorem B5618537 : Blo 2077435 5618537 := bstep (se 2 (by rfl) ⟨2106951, by rfl⟩ : syracuseStep 5618537 = 4213903) B4213903
theorem B3745691 : Blo 2077435 3745691 := bstep (se 1 (by rfl) ⟨2809268, by rfl⟩ : syracuseStep 3745691 = 5618537) B5618537
theorem B2497127 : Blo 2077435 2497127 := bstep (se 1 (by rfl) ⟨1872845, by rfl⟩ : syracuseStep 2497127 = 3745691) B3745691
theorem B6659005 : Blo 2077435 6659005 := bstep (se 3 (by rfl) ⟨1248563, by rfl⟩ : syracuseStep 6659005 = 2497127) B2497127
theorem B8878673 : Blo 2077435 8878673 := bstep (se 2 (by rfl) ⟨3329502, by rfl⟩ : syracuseStep 8878673 = 6659005) B6659005
theorem B23676461 : Blo 2077435 23676461 := bstep (se 3 (by rfl) ⟨4439336, by rfl⟩ : syracuseStep 23676461 = 8878673) B8878673
theorem B15784307 : Blo 2077435 15784307 := bstep (se 1 (by rfl) ⟨11838230, by rfl⟩ : syracuseStep 15784307 = 23676461) B23676461
theorem B10522871 : Blo 2077435 10522871 := bstep (se 1 (by rfl) ⟨7892153, by rfl⟩ : syracuseStep 10522871 = 15784307) B15784307
theorem B7015247 : Blo 2077435 7015247 := bstep (se 1 (by rfl) ⟨5261435, by rfl⟩ : syracuseStep 7015247 = 10522871) B10522871
theorem B4676831 : Blo 2077435 4676831 := bstep (se 1 (by rfl) ⟨3507623, by rfl⟩ : syracuseStep 4676831 = 7015247) B7015247
theorem B3117887 : Blo 2077435 3117887 := bstep (se 1 (by rfl) ⟨2338415, by rfl⟩ : syracuseStep 3117887 = 4676831) B4676831
theorem B2078591 : Blo 2077435 2078591 := bstep (se 1 (by rfl) ⟨1558943, by rfl⟩ : syracuseStep 2078591 = 3117887) B3117887
theorem B3117893 : Blo 2077435 3117893 := bbase (se 4 (by rfl) ⟨292302, by rfl⟩ : syracuseStep 3117893 = 584605) (by norm_num)
theorem B2078595 : Blo 2077435 2078595 := bstep (se 1 (by rfl) ⟨1558946, by rfl⟩ : syracuseStep 2078595 = 3117893) B3117893
theorem B3507637 : Blo 2077435 3507637 := bbase (se 5 (by rfl) ⟨164420, by rfl⟩ : syracuseStep 3507637 = 328841) (by norm_num)
theorem B4676849 : Blo 2077435 4676849 := bstep (se 2 (by rfl) ⟨1753818, by rfl⟩ : syracuseStep 4676849 = 3507637) B3507637
theorem B3117899 : Blo 2077435 3117899 := bstep (se 1 (by rfl) ⟨2338424, by rfl⟩ : syracuseStep 3117899 = 4676849) B4676849
theorem B2078599 : Blo 2077435 2078599 := bstep (se 1 (by rfl) ⟨1558949, by rfl⟩ : syracuseStep 2078599 = 3117899) B3117899
theorem B2338429 : Blo 2077435 2338429 := bbase (se 3 (by rfl) ⟨438455, by rfl⟩ : syracuseStep 2338429 = 876911) (by norm_num)
theorem B3117905 : Blo 2077435 3117905 := bstep (se 2 (by rfl) ⟨1169214, by rfl⟩ : syracuseStep 3117905 = 2338429) B2338429
theorem B2078603 : Blo 2077435 2078603 := bstep (se 1 (by rfl) ⟨1558952, by rfl⟩ : syracuseStep 2078603 = 3117905) B3117905
theorem B7015301 : Blo 2077435 7015301 := bbase (se 4 (by rfl) ⟨657684, by rfl⟩ : syracuseStep 7015301 = 1315369) (by norm_num)
theorem B4676867 : Blo 2077435 4676867 := bstep (se 1 (by rfl) ⟨3507650, by rfl⟩ : syracuseStep 4676867 = 7015301) B7015301
theorem B3117911 : Blo 2077435 3117911 := bstep (se 1 (by rfl) ⟨2338433, by rfl⟩ : syracuseStep 3117911 = 4676867) B4676867
theorem B2078607 : Blo 2077435 2078607 := bstep (se 1 (by rfl) ⟨1558955, by rfl⟩ : syracuseStep 2078607 = 3117911) B3117911
theorem B3117917 : Blo 2077435 3117917 := bbase (se 3 (by rfl) ⟨584609, by rfl⟩ : syracuseStep 3117917 = 1169219) (by norm_num)
theorem B2078611 : Blo 2077435 2078611 := bstep (se 1 (by rfl) ⟨1558958, by rfl⟩ : syracuseStep 2078611 = 3117917) B3117917
theorem B4676885 : Blo 2077435 4676885 := bbase (se 6 (by rfl) ⟨109614, by rfl⟩ : syracuseStep 4676885 = 219229) (by norm_num)
theorem B3117923 : Blo 2077435 3117923 := bstep (se 1 (by rfl) ⟨2338442, by rfl⟩ : syracuseStep 3117923 = 4676885) B4676885
theorem B2078615 : Blo 2077435 2078615 := bstep (se 1 (by rfl) ⟨1558961, by rfl⟩ : syracuseStep 2078615 = 3117923) B3117923
theorem B7892261 : Blo 2077435 7892261 := bbase (se 4 (by rfl) ⟨739899, by rfl⟩ : syracuseStep 7892261 = 1479799) (by norm_num)
theorem B5261507 : Blo 2077435 5261507 := bstep (se 1 (by rfl) ⟨3946130, by rfl⟩ : syracuseStep 5261507 = 7892261) B7892261
theorem B3507671 : Blo 2077435 3507671 := bstep (se 1 (by rfl) ⟨2630753, by rfl⟩ : syracuseStep 3507671 = 5261507) B5261507
theorem B2338447 : Blo 2077435 2338447 := bstep (se 1 (by rfl) ⟨1753835, by rfl⟩ : syracuseStep 2338447 = 3507671) B3507671
theorem B3117929 : Blo 2077435 3117929 := bstep (se 2 (by rfl) ⟨1169223, by rfl⟩ : syracuseStep 3117929 = 2338447) B2338447
theorem B2078619 : Blo 2077435 2078619 := bstep (se 1 (by rfl) ⟨1558964, by rfl⟩ : syracuseStep 2078619 = 3117929) B3117929
theorem B4439405 : Blo 2077435 4439405 := bbase (se 3 (by rfl) ⟨832388, by rfl⟩ : syracuseStep 4439405 = 1664777) (by norm_num)
theorem B11838413 : Blo 2077435 11838413 := bstep (se 3 (by rfl) ⟨2219702, by rfl⟩ : syracuseStep 11838413 = 4439405) B4439405
theorem B7892275 : Blo 2077435 7892275 := bstep (se 1 (by rfl) ⟨5919206, by rfl⟩ : syracuseStep 7892275 = 11838413) B11838413
theorem B10523033 : Blo 2077435 10523033 := bstep (se 2 (by rfl) ⟨3946137, by rfl⟩ : syracuseStep 10523033 = 7892275) B7892275
theorem B7015355 : Blo 2077435 7015355 := bstep (se 1 (by rfl) ⟨5261516, by rfl⟩ : syracuseStep 7015355 = 10523033) B10523033
theorem B4676903 : Blo 2077435 4676903 := bstep (se 1 (by rfl) ⟨3507677, by rfl⟩ : syracuseStep 4676903 = 7015355) B7015355
theorem B3117935 : Blo 2077435 3117935 := bstep (se 1 (by rfl) ⟨2338451, by rfl⟩ : syracuseStep 3117935 = 4676903) B4676903
theorem B2078623 : Blo 2077435 2078623 := bstep (se 1 (by rfl) ⟨1558967, by rfl⟩ : syracuseStep 2078623 = 3117935) B3117935
theorem B3117941 : Blo 2077435 3117941 := bbase (se 5 (by rfl) ⟨146153, by rfl⟩ : syracuseStep 3117941 = 292307) (by norm_num)
theorem B2078627 : Blo 2077435 2078627 := bstep (se 1 (by rfl) ⟨1558970, by rfl⟩ : syracuseStep 2078627 = 3117941) B3117941
theorem B5062493 : Blo 2077435 5062493 := bbase (se 3 (by rfl) ⟨949217, by rfl⟩ : syracuseStep 5062493 = 1898435) (by norm_num)
theorem B3374995 : Blo 2077435 3374995 := bstep (se 1 (by rfl) ⟨2531246, by rfl⟩ : syracuseStep 3374995 = 5062493) B5062493
theorem B4499993 : Blo 2077435 4499993 := bstep (se 2 (by rfl) ⟨1687497, by rfl⟩ : syracuseStep 4499993 = 3374995) B3374995
theorem B11999981 : Blo 2077435 11999981 := bstep (se 3 (by rfl) ⟨2249996, by rfl⟩ : syracuseStep 11999981 = 4499993) B4499993
theorem B7999987 : Blo 2077435 7999987 := bstep (se 1 (by rfl) ⟨5999990, by rfl⟩ : syracuseStep 7999987 = 11999981) B11999981
theorem B10666649 : Blo 2077435 10666649 := bstep (se 2 (by rfl) ⟨3999993, by rfl⟩ : syracuseStep 10666649 = 7999987) B7999987
theorem B7111099 : Blo 2077435 7111099 := bstep (se 1 (by rfl) ⟨5333324, by rfl⟩ : syracuseStep 7111099 = 10666649) B10666649
theorem B9481465 : Blo 2077435 9481465 := bstep (se 2 (by rfl) ⟨3555549, by rfl⟩ : syracuseStep 9481465 = 7111099) B7111099
theorem B50567813 : Blo 2077435 50567813 := bstep (se 4 (by rfl) ⟨4740732, by rfl⟩ : syracuseStep 50567813 = 9481465) B9481465
theorem B33711875 : Blo 2077435 33711875 := bstep (se 1 (by rfl) ⟨25283906, by rfl⟩ : syracuseStep 33711875 = 50567813) B50567813
theorem B22474583 : Blo 2077435 22474583 := bstep (se 1 (by rfl) ⟨16855937, by rfl⟩ : syracuseStep 22474583 = 33711875) B33711875
theorem B14983055 : Blo 2077435 14983055 := bstep (se 1 (by rfl) ⟨11237291, by rfl⟩ : syracuseStep 14983055 = 22474583) B22474583
theorem B9988703 : Blo 2077435 9988703 := bstep (se 1 (by rfl) ⟨7491527, by rfl⟩ : syracuseStep 9988703 = 14983055) B14983055
theorem B6659135 : Blo 2077435 6659135 := bstep (se 1 (by rfl) ⟨4994351, by rfl⟩ : syracuseStep 6659135 = 9988703) B9988703
theorem B4439423 : Blo 2077435 4439423 := bstep (se 1 (by rfl) ⟨3329567, by rfl⟩ : syracuseStep 4439423 = 6659135) B6659135
theorem B2959615 : Blo 2077435 2959615 := bstep (se 1 (by rfl) ⟨2219711, by rfl⟩ : syracuseStep 2959615 = 4439423) B4439423
theorem B3946153 : Blo 2077435 3946153 := bstep (se 2 (by rfl) ⟨1479807, by rfl⟩ : syracuseStep 3946153 = 2959615) B2959615
theorem B5261537 : Blo 2077435 5261537 := bstep (se 2 (by rfl) ⟨1973076, by rfl⟩ : syracuseStep 5261537 = 3946153) B3946153
theorem B3507691 : Blo 2077435 3507691 := bstep (se 1 (by rfl) ⟨2630768, by rfl⟩ : syracuseStep 3507691 = 5261537) B5261537
theorem B4676921 : Blo 2077435 4676921 := bstep (se 2 (by rfl) ⟨1753845, by rfl⟩ : syracuseStep 4676921 = 3507691) B3507691
theorem B3117947 : Blo 2077435 3117947 := bstep (se 1 (by rfl) ⟨2338460, by rfl⟩ : syracuseStep 3117947 = 4676921) B4676921
theorem B2078631 : Blo 2077435 2078631 := bstep (se 1 (by rfl) ⟨1558973, by rfl⟩ : syracuseStep 2078631 = 3117947) B3117947
theorem B2338465 : Blo 2077435 2338465 := bbase (se 2 (by rfl) ⟨876924, by rfl⟩ : syracuseStep 2338465 = 1753849) (by norm_num)
theorem B3117953 : Blo 2077435 3117953 := bstep (se 2 (by rfl) ⟨1169232, by rfl⟩ : syracuseStep 3117953 = 2338465) B2338465
theorem B2078635 : Blo 2077435 2078635 := bstep (se 1 (by rfl) ⟨1558976, by rfl⟩ : syracuseStep 2078635 = 3117953) B3117953
theorem B5261557 : Blo 2077435 5261557 := bbase (se 5 (by rfl) ⟨246635, by rfl⟩ : syracuseStep 5261557 = 493271) (by norm_num)
theorem B7015409 : Blo 2077435 7015409 := bstep (se 2 (by rfl) ⟨2630778, by rfl⟩ : syracuseStep 7015409 = 5261557) B5261557
theorem B4676939 : Blo 2077435 4676939 := bstep (se 1 (by rfl) ⟨3507704, by rfl⟩ : syracuseStep 4676939 = 7015409) B7015409
theorem B3117959 : Blo 2077435 3117959 := bstep (se 1 (by rfl) ⟨2338469, by rfl⟩ : syracuseStep 3117959 = 4676939) B4676939
theorem B2078639 : Blo 2077435 2078639 := bstep (se 1 (by rfl) ⟨1558979, by rfl⟩ : syracuseStep 2078639 = 3117959) B3117959
theorem B3117965 : Blo 2077435 3117965 := bbase (se 3 (by rfl) ⟨584618, by rfl⟩ : syracuseStep 3117965 = 1169237) (by norm_num)
theorem B2078643 : Blo 2077435 2078643 := bstep (se 1 (by rfl) ⟨1558982, by rfl⟩ : syracuseStep 2078643 = 3117965) B3117965
theorem B4676957 : Blo 2077435 4676957 := bbase (se 3 (by rfl) ⟨876929, by rfl⟩ : syracuseStep 4676957 = 1753859) (by norm_num)
theorem B3117971 : Blo 2077435 3117971 := bstep (se 1 (by rfl) ⟨2338478, by rfl⟩ : syracuseStep 3117971 = 4676957) B4676957
theorem B2078647 : Blo 2077435 2078647 := bstep (se 1 (by rfl) ⟨1558985, by rfl⟩ : syracuseStep 2078647 = 3117971) B3117971
theorem B3507725 : Blo 2077435 3507725 := bbase (se 3 (by rfl) ⟨657698, by rfl⟩ : syracuseStep 3507725 = 1315397) (by norm_num)
theorem B2338483 : Blo 2077435 2338483 := bstep (se 1 (by rfl) ⟨1753862, by rfl⟩ : syracuseStep 2338483 = 3507725) B3507725
theorem B3117977 : Blo 2077435 3117977 := bstep (se 2 (by rfl) ⟨1169241, by rfl⟩ : syracuseStep 3117977 = 2338483) B2338483
theorem B2078651 : Blo 2077435 2078651 := bstep (se 1 (by rfl) ⟨1558988, by rfl⟩ : syracuseStep 2078651 = 3117977) B3117977
theorem B3329605 : Blo 2077435 3329605 := bbase (se 4 (by rfl) ⟨312150, by rfl⟩ : syracuseStep 3329605 = 624301) (by norm_num)
theorem B17757893 : Blo 2077435 17757893 := bstep (se 4 (by rfl) ⟨1664802, by rfl⟩ : syracuseStep 17757893 = 3329605) B3329605
theorem B11838595 : Blo 2077435 11838595 := bstep (se 1 (by rfl) ⟨8878946, by rfl⟩ : syracuseStep 11838595 = 17757893) B17757893
theorem B15784793 : Blo 2077435 15784793 := bstep (se 2 (by rfl) ⟨5919297, by rfl⟩ : syracuseStep 15784793 = 11838595) B11838595
theorem B10523195 : Blo 2077435 10523195 := bstep (se 1 (by rfl) ⟨7892396, by rfl⟩ : syracuseStep 10523195 = 15784793) B15784793
theorem B7015463 : Blo 2077435 7015463 := bstep (se 1 (by rfl) ⟨5261597, by rfl⟩ : syracuseStep 7015463 = 10523195) B10523195
theorem B4676975 : Blo 2077435 4676975 := bstep (se 1 (by rfl) ⟨3507731, by rfl⟩ : syracuseStep 4676975 = 7015463) B7015463
theorem B3117983 : Blo 2077435 3117983 := bstep (se 1 (by rfl) ⟨2338487, by rfl⟩ : syracuseStep 3117983 = 4676975) B4676975
theorem B2078655 : Blo 2077435 2078655 := bstep (se 1 (by rfl) ⟨1558991, by rfl⟩ : syracuseStep 2078655 = 3117983) B3117983
theorem B3117989 : Blo 2077435 3117989 := bbase (se 4 (by rfl) ⟨292311, by rfl⟩ : syracuseStep 3117989 = 584623) (by norm_num)
theorem B2078659 : Blo 2077435 2078659 := bstep (se 1 (by rfl) ⟨1558994, by rfl⟩ : syracuseStep 2078659 = 3117989) B3117989
theorem B2630809 : Blo 2077435 2630809 := bbase (se 2 (by rfl) ⟨986553, by rfl⟩ : syracuseStep 2630809 = 1973107) (by norm_num)
theorem B3507745 : Blo 2077435 3507745 := bstep (se 2 (by rfl) ⟨1315404, by rfl⟩ : syracuseStep 3507745 = 2630809) B2630809
theorem B4676993 : Blo 2077435 4676993 := bstep (se 2 (by rfl) ⟨1753872, by rfl⟩ : syracuseStep 4676993 = 3507745) B3507745
theorem B3117995 : Blo 2077435 3117995 := bstep (se 1 (by rfl) ⟨2338496, by rfl⟩ : syracuseStep 3117995 = 4676993) B4676993
theorem B2078663 : Blo 2077435 2078663 := bstep (se 1 (by rfl) ⟨1558997, by rfl⟩ : syracuseStep 2078663 = 3117995) B3117995
theorem B2338501 : Blo 2077435 2338501 := bbase (se 4 (by rfl) ⟨219234, by rfl⟩ : syracuseStep 2338501 = 438469) (by norm_num)
theorem B3118001 : Blo 2077435 3118001 := bstep (se 2 (by rfl) ⟨1169250, by rfl⟩ : syracuseStep 3118001 = 2338501) B2338501
theorem B2078667 : Blo 2077435 2078667 := bstep (se 1 (by rfl) ⟨1559000, by rfl⟩ : syracuseStep 2078667 = 3118001) B3118001
theorem B3946229 : Blo 2077435 3946229 := bbase (se 5 (by rfl) ⟨184979, by rfl⟩ : syracuseStep 3946229 = 369959) (by norm_num)
theorem B2630819 : Blo 2077435 2630819 := bstep (se 1 (by rfl) ⟨1973114, by rfl⟩ : syracuseStep 2630819 = 3946229) B3946229
theorem B7015517 : Blo 2077435 7015517 := bstep (se 3 (by rfl) ⟨1315409, by rfl⟩ : syracuseStep 7015517 = 2630819) B2630819
theorem B4677011 : Blo 2077435 4677011 := bstep (se 1 (by rfl) ⟨3507758, by rfl⟩ : syracuseStep 4677011 = 7015517) B7015517
theorem B3118007 : Blo 2077435 3118007 := bstep (se 1 (by rfl) ⟨2338505, by rfl⟩ : syracuseStep 3118007 = 4677011) B4677011
theorem B2078671 : Blo 2077435 2078671 := bstep (se 1 (by rfl) ⟨1559003, by rfl⟩ : syracuseStep 2078671 = 3118007) B3118007
theorem B3118013 : Blo 2077435 3118013 := bbase (se 3 (by rfl) ⟨584627, by rfl⟩ : syracuseStep 3118013 = 1169255) (by norm_num)
theorem B2078675 : Blo 2077435 2078675 := bstep (se 1 (by rfl) ⟨1559006, by rfl⟩ : syracuseStep 2078675 = 3118013) B3118013
theorem B4677029 : Blo 2077435 4677029 := bbase (se 4 (by rfl) ⟨438471, by rfl⟩ : syracuseStep 4677029 = 876943) (by norm_num)
theorem B3118019 : Blo 2077435 3118019 := bstep (se 1 (by rfl) ⟨2338514, by rfl⟩ : syracuseStep 3118019 = 4677029) B4677029
theorem B2078679 : Blo 2077435 2078679 := bstep (se 1 (by rfl) ⟨1559009, by rfl⟩ : syracuseStep 2078679 = 3118019) B3118019
theorem B5261669 : Blo 2077435 5261669 := bbase (se 4 (by rfl) ⟨493281, by rfl⟩ : syracuseStep 5261669 = 986563) (by norm_num)
theorem B3507779 : Blo 2077435 3507779 := bstep (se 1 (by rfl) ⟨2630834, by rfl⟩ : syracuseStep 3507779 = 5261669) B5261669
theorem B2338519 : Blo 2077435 2338519 := bstep (se 1 (by rfl) ⟨1753889, by rfl⟩ : syracuseStep 2338519 = 3507779) B3507779
theorem B3118025 : Blo 2077435 3118025 := bstep (se 2 (by rfl) ⟨1169259, by rfl⟩ : syracuseStep 3118025 = 2338519) B2338519
theorem B2078683 : Blo 2077435 2078683 := bstep (se 1 (by rfl) ⟨1559012, by rfl⟩ : syracuseStep 2078683 = 3118025) B3118025
theorem B9875141 : Blo 2077435 9875141 := bbase (se 4 (by rfl) ⟨925794, by rfl⟩ : syracuseStep 9875141 = 1851589) (by norm_num)
theorem B6583427 : Blo 2077435 6583427 := bstep (se 1 (by rfl) ⟨4937570, by rfl⟩ : syracuseStep 6583427 = 9875141) B9875141
theorem B4388951 : Blo 2077435 4388951 := bstep (se 1 (by rfl) ⟨3291713, by rfl⟩ : syracuseStep 4388951 = 6583427) B6583427
theorem B2925967 : Blo 2077435 2925967 := bstep (se 1 (by rfl) ⟨2194475, by rfl⟩ : syracuseStep 2925967 = 4388951) B4388951
theorem B3901289 : Blo 2077435 3901289 := bstep (se 2 (by rfl) ⟨1462983, by rfl⟩ : syracuseStep 3901289 = 2925967) B2925967
theorem B41613749 : Blo 2077435 41613749 := bstep (se 5 (by rfl) ⟨1950644, by rfl⟩ : syracuseStep 41613749 = 3901289) B3901289
theorem B27742499 : Blo 2077435 27742499 := bstep (se 1 (by rfl) ⟨20806874, by rfl⟩ : syracuseStep 27742499 = 41613749) B41613749
theorem B18494999 : Blo 2077435 18494999 := bstep (se 1 (by rfl) ⟨13871249, by rfl⟩ : syracuseStep 18494999 = 27742499) B27742499
theorem B12329999 : Blo 2077435 12329999 := bstep (se 1 (by rfl) ⟨9247499, by rfl⟩ : syracuseStep 12329999 = 18494999) B18494999
theorem B8219999 : Blo 2077435 8219999 := bstep (se 1 (by rfl) ⟨6164999, by rfl⟩ : syracuseStep 8219999 = 12329999) B12329999
theorem B21919997 : Blo 2077435 21919997 := bstep (se 3 (by rfl) ⟨4109999, by rfl⟩ : syracuseStep 21919997 = 8219999) B8219999
theorem B58453325 : Blo 2077435 58453325 := bstep (se 3 (by rfl) ⟨10959998, by rfl⟩ : syracuseStep 58453325 = 21919997) B21919997
theorem B38968883 : Blo 2077435 38968883 := bstep (se 1 (by rfl) ⟨29226662, by rfl⟩ : syracuseStep 38968883 = 58453325) B58453325
theorem B25979255 : Blo 2077435 25979255 := bstep (se 1 (by rfl) ⟨19484441, by rfl⟩ : syracuseStep 25979255 = 38968883) B38968883
theorem B17319503 : Blo 2077435 17319503 := bstep (se 1 (by rfl) ⟨12989627, by rfl⟩ : syracuseStep 17319503 = 25979255) B25979255
theorem B11546335 : Blo 2077435 11546335 := bstep (se 1 (by rfl) ⟨8659751, by rfl⟩ : syracuseStep 11546335 = 17319503) B17319503
theorem B15395113 : Blo 2077435 15395113 := bstep (se 2 (by rfl) ⟨5773167, by rfl⟩ : syracuseStep 15395113 = 11546335) B11546335
theorem B20526817 : Blo 2077435 20526817 := bstep (se 2 (by rfl) ⟨7697556, by rfl⟩ : syracuseStep 20526817 = 15395113) B15395113
theorem B27369089 : Blo 2077435 27369089 := bstep (se 2 (by rfl) ⟨10263408, by rfl⟩ : syracuseStep 27369089 = 20526817) B20526817
theorem B18246059 : Blo 2077435 18246059 := bstep (se 1 (by rfl) ⟨13684544, by rfl⟩ : syracuseStep 18246059 = 27369089) B27369089
theorem B12164039 : Blo 2077435 12164039 := bstep (se 1 (by rfl) ⟨9123029, by rfl⟩ : syracuseStep 12164039 = 18246059) B18246059
theorem B8109359 : Blo 2077435 8109359 := bstep (se 1 (by rfl) ⟨6082019, by rfl⟩ : syracuseStep 8109359 = 12164039) B12164039
theorem B5406239 : Blo 2077435 5406239 := bstep (se 1 (by rfl) ⟨4054679, by rfl⟩ : syracuseStep 5406239 = 8109359) B8109359
theorem B3604159 : Blo 2077435 3604159 := bstep (se 1 (by rfl) ⟨2703119, by rfl⟩ : syracuseStep 3604159 = 5406239) B5406239
theorem B19222181 : Blo 2077435 19222181 := bstep (se 4 (by rfl) ⟨1802079, by rfl⟩ : syracuseStep 19222181 = 3604159) B3604159
theorem B12814787 : Blo 2077435 12814787 := bstep (se 1 (by rfl) ⟨9611090, by rfl⟩ : syracuseStep 12814787 = 19222181) B19222181
theorem B34172765 : Blo 2077435 34172765 := bstep (se 3 (by rfl) ⟨6407393, by rfl⟩ : syracuseStep 34172765 = 12814787) B12814787
theorem B22781843 : Blo 2077435 22781843 := bstep (se 1 (by rfl) ⟨17086382, by rfl⟩ : syracuseStep 22781843 = 34172765) B34172765
theorem B15187895 : Blo 2077435 15187895 := bstep (se 1 (by rfl) ⟨11390921, by rfl⟩ : syracuseStep 15187895 = 22781843) B22781843
theorem B10125263 : Blo 2077435 10125263 := bstep (se 1 (by rfl) ⟨7593947, by rfl⟩ : syracuseStep 10125263 = 15187895) B15187895
theorem B27000701 : Blo 2077435 27000701 := bstep (se 3 (by rfl) ⟨5062631, by rfl⟩ : syracuseStep 27000701 = 10125263) B10125263
theorem B18000467 : Blo 2077435 18000467 := bstep (se 1 (by rfl) ⟨13500350, by rfl⟩ : syracuseStep 18000467 = 27000701) B27000701
theorem B12000311 : Blo 2077435 12000311 := bstep (se 1 (by rfl) ⟨9000233, by rfl⟩ : syracuseStep 12000311 = 18000467) B18000467
theorem B8000207 : Blo 2077435 8000207 := bstep (se 1 (by rfl) ⟨6000155, by rfl⟩ : syracuseStep 8000207 = 12000311) B12000311
theorem B5333471 : Blo 2077435 5333471 := bstep (se 1 (by rfl) ⟨4000103, by rfl⟩ : syracuseStep 5333471 = 8000207) B8000207
theorem B3555647 : Blo 2077435 3555647 := bstep (se 1 (by rfl) ⟨2666735, by rfl⟩ : syracuseStep 3555647 = 5333471) B5333471
theorem B2370431 : Blo 2077435 2370431 := bstep (se 1 (by rfl) ⟨1777823, by rfl⟩ : syracuseStep 2370431 = 3555647) B3555647
theorem B6321149 : Blo 2077435 6321149 := bstep (se 3 (by rfl) ⟨1185215, by rfl⟩ : syracuseStep 6321149 = 2370431) B2370431
theorem B4214099 : Blo 2077435 4214099 := bstep (se 1 (by rfl) ⟨3160574, by rfl⟩ : syracuseStep 4214099 = 6321149) B6321149
theorem B2809399 : Blo 2077435 2809399 := bstep (se 1 (by rfl) ⟨2107049, by rfl⟩ : syracuseStep 2809399 = 4214099) B4214099
theorem B3745865 : Blo 2077435 3745865 := bstep (se 2 (by rfl) ⟨1404699, by rfl⟩ : syracuseStep 3745865 = 2809399) B2809399
theorem B2497243 : Blo 2077435 2497243 := bstep (se 1 (by rfl) ⟨1872932, by rfl⟩ : syracuseStep 2497243 = 3745865) B3745865
theorem B3329657 : Blo 2077435 3329657 := bstep (se 2 (by rfl) ⟨1248621, by rfl⟩ : syracuseStep 3329657 = 2497243) B2497243
theorem B2219771 : Blo 2077435 2219771 := bstep (se 1 (by rfl) ⟨1664828, by rfl⟩ : syracuseStep 2219771 = 3329657) B3329657
theorem B5919389 : Blo 2077435 5919389 := bstep (se 3 (by rfl) ⟨1109885, by rfl⟩ : syracuseStep 5919389 = 2219771) B2219771
theorem B3946259 : Blo 2077435 3946259 := bstep (se 1 (by rfl) ⟨2959694, by rfl⟩ : syracuseStep 3946259 = 5919389) B5919389
theorem B10523357 : Blo 2077435 10523357 := bstep (se 3 (by rfl) ⟨1973129, by rfl⟩ : syracuseStep 10523357 = 3946259) B3946259
theorem B7015571 : Blo 2077435 7015571 := bstep (se 1 (by rfl) ⟨5261678, by rfl⟩ : syracuseStep 7015571 = 10523357) B10523357
theorem B4677047 : Blo 2077435 4677047 := bstep (se 1 (by rfl) ⟨3507785, by rfl⟩ : syracuseStep 4677047 = 7015571) B7015571
theorem B3118031 : Blo 2077435 3118031 := bstep (se 1 (by rfl) ⟨2338523, by rfl⟩ : syracuseStep 3118031 = 4677047) B4677047
theorem B2078687 : Blo 2077435 2078687 := bstep (se 1 (by rfl) ⟨1559015, by rfl⟩ : syracuseStep 2078687 = 3118031) B3118031
theorem B3118037 : Blo 2077435 3118037 := bbase (se 7 (by rfl) ⟨36539, by rfl⟩ : syracuseStep 3118037 = 73079) (by norm_num)
theorem B2078691 : Blo 2077435 2078691 := bstep (se 1 (by rfl) ⟨1559018, by rfl⟩ : syracuseStep 2078691 = 3118037) B3118037
theorem B7892549 : Blo 2077435 7892549 := bbase (se 4 (by rfl) ⟨739926, by rfl⟩ : syracuseStep 7892549 = 1479853) (by norm_num)
theorem B5261699 : Blo 2077435 5261699 := bstep (se 1 (by rfl) ⟨3946274, by rfl⟩ : syracuseStep 5261699 = 7892549) B7892549
theorem B3507799 : Blo 2077435 3507799 := bstep (se 1 (by rfl) ⟨2630849, by rfl⟩ : syracuseStep 3507799 = 5261699) B5261699
theorem B4677065 : Blo 2077435 4677065 := bstep (se 2 (by rfl) ⟨1753899, by rfl⟩ : syracuseStep 4677065 = 3507799) B3507799
theorem B3118043 : Blo 2077435 3118043 := bstep (se 1 (by rfl) ⟨2338532, by rfl⟩ : syracuseStep 3118043 = 4677065) B4677065
theorem B2078695 : Blo 2077435 2078695 := bstep (se 1 (by rfl) ⟨1559021, by rfl⟩ : syracuseStep 2078695 = 3118043) B3118043
theorem B2338537 : Blo 2077435 2338537 := bbase (se 2 (by rfl) ⟨876951, by rfl⟩ : syracuseStep 2338537 = 1753903) (by norm_num)
theorem B3118049 : Blo 2077435 3118049 := bstep (se 2 (by rfl) ⟨1169268, by rfl⟩ : syracuseStep 3118049 = 2338537) B2338537
theorem B2078699 : Blo 2077435 2078699 := bstep (se 1 (by rfl) ⟨1559024, by rfl⟩ : syracuseStep 2078699 = 3118049) B3118049
theorem B11838869 : Blo 2077435 11838869 := bbase (se 6 (by rfl) ⟨277473, by rfl⟩ : syracuseStep 11838869 = 554947) (by norm_num)
theorem B7892579 : Blo 2077435 7892579 := bstep (se 1 (by rfl) ⟨5919434, by rfl⟩ : syracuseStep 7892579 = 11838869) B11838869
theorem B5261719 : Blo 2077435 5261719 := bstep (se 1 (by rfl) ⟨3946289, by rfl⟩ : syracuseStep 5261719 = 7892579) B7892579
theorem B7015625 : Blo 2077435 7015625 := bstep (se 2 (by rfl) ⟨2630859, by rfl⟩ : syracuseStep 7015625 = 5261719) B5261719
theorem B4677083 : Blo 2077435 4677083 := bstep (se 1 (by rfl) ⟨3507812, by rfl⟩ : syracuseStep 4677083 = 7015625) B7015625
theorem B3118055 : Blo 2077435 3118055 := bstep (se 1 (by rfl) ⟨2338541, by rfl⟩ : syracuseStep 3118055 = 4677083) B4677083
theorem B2078703 : Blo 2077435 2078703 := bstep (se 1 (by rfl) ⟨1559027, by rfl⟩ : syracuseStep 2078703 = 3118055) B3118055
theorem B3118061 : Blo 2077435 3118061 := bbase (se 3 (by rfl) ⟨584636, by rfl⟩ : syracuseStep 3118061 = 1169273) (by norm_num)
theorem B2078707 : Blo 2077435 2078707 := bstep (se 1 (by rfl) ⟨1559030, by rfl⟩ : syracuseStep 2078707 = 3118061) B3118061
theorem B4677101 : Blo 2077435 4677101 := bbase (se 3 (by rfl) ⟨876956, by rfl⟩ : syracuseStep 4677101 = 1753913) (by norm_num)
theorem B3118067 : Blo 2077435 3118067 := bstep (se 1 (by rfl) ⟨2338550, by rfl⟩ : syracuseStep 3118067 = 4677101) B4677101
theorem B2078711 : Blo 2077435 2078711 := bstep (se 1 (by rfl) ⟨1559033, by rfl⟩ : syracuseStep 2078711 = 3118067) B3118067
theorem B2497277 : Blo 2077435 2497277 := bbase (se 3 (by rfl) ⟨468239, by rfl⟩ : syracuseStep 2497277 = 936479) (by norm_num)
theorem B6659405 : Blo 2077435 6659405 := bstep (se 3 (by rfl) ⟨1248638, by rfl⟩ : syracuseStep 6659405 = 2497277) B2497277
theorem B4439603 : Blo 2077435 4439603 := bstep (se 1 (by rfl) ⟨3329702, by rfl⟩ : syracuseStep 4439603 = 6659405) B6659405
theorem B2959735 : Blo 2077435 2959735 := bstep (se 1 (by rfl) ⟨2219801, by rfl⟩ : syracuseStep 2959735 = 4439603) B4439603
theorem B3946313 : Blo 2077435 3946313 := bstep (se 2 (by rfl) ⟨1479867, by rfl⟩ : syracuseStep 3946313 = 2959735) B2959735
theorem B2630875 : Blo 2077435 2630875 := bstep (se 1 (by rfl) ⟨1973156, by rfl⟩ : syracuseStep 2630875 = 3946313) B3946313
theorem B3507833 : Blo 2077435 3507833 := bstep (se 2 (by rfl) ⟨1315437, by rfl⟩ : syracuseStep 3507833 = 2630875) B2630875
theorem B2338555 : Blo 2077435 2338555 := bstep (se 1 (by rfl) ⟨1753916, by rfl⟩ : syracuseStep 2338555 = 3507833) B3507833
theorem B3118073 : Blo 2077435 3118073 := bstep (se 2 (by rfl) ⟨1169277, by rfl⟩ : syracuseStep 3118073 = 2338555) B2338555
theorem B2078715 : Blo 2077435 2078715 := bstep (se 1 (by rfl) ⟨1559036, by rfl⟩ : syracuseStep 2078715 = 3118073) B3118073
theorem B7111397 : Blo 2077435 7111397 := bbase (se 4 (by rfl) ⟨666693, by rfl⟩ : syracuseStep 7111397 = 1333387) (by norm_num)
theorem B18963725 : Blo 2077435 18963725 := bstep (se 3 (by rfl) ⟨3555698, by rfl⟩ : syracuseStep 18963725 = 7111397) B7111397
theorem B50569933 : Blo 2077435 50569933 := bstep (se 3 (by rfl) ⟨9481862, by rfl⟩ : syracuseStep 50569933 = 18963725) B18963725
theorem B67426577 : Blo 2077435 67426577 := bstep (se 2 (by rfl) ⟨25284966, by rfl⟩ : syracuseStep 67426577 = 50569933) B50569933
theorem B44951051 : Blo 2077435 44951051 := bstep (se 1 (by rfl) ⟨33713288, by rfl⟩ : syracuseStep 44951051 = 67426577) B67426577
theorem B119869469 : Blo 2077435 119869469 := bstep (se 3 (by rfl) ⟨22475525, by rfl⟩ : syracuseStep 119869469 = 44951051) B44951051
theorem B79912979 : Blo 2077435 79912979 := bstep (se 1 (by rfl) ⟨59934734, by rfl⟩ : syracuseStep 79912979 = 119869469) B119869469
theorem B53275319 : Blo 2077435 53275319 := bstep (se 1 (by rfl) ⟨39956489, by rfl⟩ : syracuseStep 53275319 = 79912979) B79912979
theorem B35516879 : Blo 2077435 35516879 := bstep (se 1 (by rfl) ⟨26637659, by rfl⟩ : syracuseStep 35516879 = 53275319) B53275319
theorem B23677919 : Blo 2077435 23677919 := bstep (se 1 (by rfl) ⟨17758439, by rfl⟩ : syracuseStep 23677919 = 35516879) B35516879
theorem B15785279 : Blo 2077435 15785279 := bstep (se 1 (by rfl) ⟨11838959, by rfl⟩ : syracuseStep 15785279 = 23677919) B23677919
theorem B10523519 : Blo 2077435 10523519 := bstep (se 1 (by rfl) ⟨7892639, by rfl⟩ : syracuseStep 10523519 = 15785279) B15785279
theorem B7015679 : Blo 2077435 7015679 := bstep (se 1 (by rfl) ⟨5261759, by rfl⟩ : syracuseStep 7015679 = 10523519) B10523519
theorem B4677119 : Blo 2077435 4677119 := bstep (se 1 (by rfl) ⟨3507839, by rfl⟩ : syracuseStep 4677119 = 7015679) B7015679
theorem B3118079 : Blo 2077435 3118079 := bstep (se 1 (by rfl) ⟨2338559, by rfl⟩ : syracuseStep 3118079 = 4677119) B4677119
theorem B2078719 : Blo 2077435 2078719 := bstep (se 1 (by rfl) ⟨1559039, by rfl⟩ : syracuseStep 2078719 = 3118079) B3118079
theorem B3118085 : Blo 2077435 3118085 := bbase (se 4 (by rfl) ⟨292320, by rfl⟩ : syracuseStep 3118085 = 584641) (by norm_num)
theorem B2078723 : Blo 2077435 2078723 := bstep (se 1 (by rfl) ⟨1559042, by rfl⟩ : syracuseStep 2078723 = 3118085) B3118085
theorem B3507853 : Blo 2077435 3507853 := bbase (se 3 (by rfl) ⟨657722, by rfl⟩ : syracuseStep 3507853 = 1315445) (by norm_num)
theorem B4677137 : Blo 2077435 4677137 := bstep (se 2 (by rfl) ⟨1753926, by rfl⟩ : syracuseStep 4677137 = 3507853) B3507853
theorem B3118091 : Blo 2077435 3118091 := bstep (se 1 (by rfl) ⟨2338568, by rfl⟩ : syracuseStep 3118091 = 4677137) B4677137
theorem B2078727 : Blo 2077435 2078727 := bstep (se 1 (by rfl) ⟨1559045, by rfl⟩ : syracuseStep 2078727 = 3118091) B3118091
theorem B2338573 : Blo 2077435 2338573 := bbase (se 3 (by rfl) ⟨438482, by rfl⟩ : syracuseStep 2338573 = 876965) (by norm_num)
theorem B3118097 : Blo 2077435 3118097 := bstep (se 2 (by rfl) ⟨1169286, by rfl⟩ : syracuseStep 3118097 = 2338573) B2338573
theorem B2078731 : Blo 2077435 2078731 := bstep (se 1 (by rfl) ⟨1559048, by rfl⟩ : syracuseStep 2078731 = 3118097) B3118097
theorem B7015733 : Blo 2077435 7015733 := bbase (se 5 (by rfl) ⟨328862, by rfl⟩ : syracuseStep 7015733 = 657725) (by norm_num)
theorem B4677155 : Blo 2077435 4677155 := bstep (se 1 (by rfl) ⟨3507866, by rfl⟩ : syracuseStep 4677155 = 7015733) B7015733
theorem B3118103 : Blo 2077435 3118103 := bstep (se 1 (by rfl) ⟨2338577, by rfl⟩ : syracuseStep 3118103 = 4677155) B4677155
theorem B2078735 : Blo 2077435 2078735 := bstep (se 1 (by rfl) ⟨1559051, by rfl⟩ : syracuseStep 2078735 = 3118103) B3118103
theorem B3118109 : Blo 2077435 3118109 := bbase (se 3 (by rfl) ⟨584645, by rfl⟩ : syracuseStep 3118109 = 1169291) (by norm_num)
theorem B2078739 : Blo 2077435 2078739 := bstep (se 1 (by rfl) ⟨1559054, by rfl⟩ : syracuseStep 2078739 = 3118109) B3118109
theorem B4677173 : Blo 2077435 4677173 := bbase (se 5 (by rfl) ⟨219242, by rfl⟩ : syracuseStep 4677173 = 438485) (by norm_num)
theorem B3118115 : Blo 2077435 3118115 := bstep (se 1 (by rfl) ⟨2338586, by rfl⟩ : syracuseStep 3118115 = 4677173) B4677173
theorem B2078743 : Blo 2077435 2078743 := bstep (se 1 (by rfl) ⟨1559057, by rfl⟩ : syracuseStep 2078743 = 3118115) B3118115
theorem B3745973 : Blo 2077435 3745973 := bbase (se 5 (by rfl) ⟨175592, by rfl⟩ : syracuseStep 3745973 = 351185) (by norm_num)
theorem B2497315 : Blo 2077435 2497315 := bstep (se 1 (by rfl) ⟨1872986, by rfl⟩ : syracuseStep 2497315 = 3745973) B3745973
theorem B3329753 : Blo 2077435 3329753 := bstep (se 2 (by rfl) ⟨1248657, by rfl⟩ : syracuseStep 3329753 = 2497315) B2497315
theorem B8879341 : Blo 2077435 8879341 := bstep (se 3 (by rfl) ⟨1664876, by rfl⟩ : syracuseStep 8879341 = 3329753) B3329753
theorem B11839121 : Blo 2077435 11839121 := bstep (se 2 (by rfl) ⟨4439670, by rfl⟩ : syracuseStep 11839121 = 8879341) B8879341
theorem B7892747 : Blo 2077435 7892747 := bstep (se 1 (by rfl) ⟨5919560, by rfl⟩ : syracuseStep 7892747 = 11839121) B11839121
theorem B5261831 : Blo 2077435 5261831 := bstep (se 1 (by rfl) ⟨3946373, by rfl⟩ : syracuseStep 5261831 = 7892747) B7892747
theorem B3507887 : Blo 2077435 3507887 := bstep (se 1 (by rfl) ⟨2630915, by rfl⟩ : syracuseStep 3507887 = 5261831) B5261831
theorem B2338591 : Blo 2077435 2338591 := bstep (se 1 (by rfl) ⟨1753943, by rfl⟩ : syracuseStep 2338591 = 3507887) B3507887
theorem B3118121 : Blo 2077435 3118121 := bstep (se 2 (by rfl) ⟨1169295, by rfl⟩ : syracuseStep 3118121 = 2338591) B2338591
theorem B2078747 : Blo 2077435 2078747 := bstep (se 1 (by rfl) ⟨1559060, by rfl⟩ : syracuseStep 2078747 = 3118121) B3118121
theorem B7594181 : Blo 2077435 7594181 := bbase (se 4 (by rfl) ⟨711954, by rfl⟩ : syracuseStep 7594181 = 1423909) (by norm_num)
theorem B5062787 : Blo 2077435 5062787 := bstep (se 1 (by rfl) ⟨3797090, by rfl⟩ : syracuseStep 5062787 = 7594181) B7594181
theorem B3375191 : Blo 2077435 3375191 := bstep (se 1 (by rfl) ⟨2531393, by rfl⟩ : syracuseStep 3375191 = 5062787) B5062787
theorem B2250127 : Blo 2077435 2250127 := bstep (se 1 (by rfl) ⟨1687595, by rfl⟩ : syracuseStep 2250127 = 3375191) B3375191
theorem B3000169 : Blo 2077435 3000169 := bstep (se 2 (by rfl) ⟨1125063, by rfl⟩ : syracuseStep 3000169 = 2250127) B2250127
theorem B4000225 : Blo 2077435 4000225 := bstep (se 2 (by rfl) ⟨1500084, by rfl⟩ : syracuseStep 4000225 = 3000169) B3000169
theorem B5333633 : Blo 2077435 5333633 := bstep (se 2 (by rfl) ⟨2000112, by rfl⟩ : syracuseStep 5333633 = 4000225) B4000225
theorem B3555755 : Blo 2077435 3555755 := bstep (se 1 (by rfl) ⟨2666816, by rfl⟩ : syracuseStep 3555755 = 5333633) B5333633
theorem B2370503 : Blo 2077435 2370503 := bstep (se 1 (by rfl) ⟨1777877, by rfl⟩ : syracuseStep 2370503 = 3555755) B3555755
theorem B6321341 : Blo 2077435 6321341 := bstep (se 3 (by rfl) ⟨1185251, by rfl⟩ : syracuseStep 6321341 = 2370503) B2370503
theorem B16856909 : Blo 2077435 16856909 := bstep (se 3 (by rfl) ⟨3160670, by rfl⟩ : syracuseStep 16856909 = 6321341) B6321341
theorem B11237939 : Blo 2077435 11237939 := bstep (se 1 (by rfl) ⟨8428454, by rfl⟩ : syracuseStep 11237939 = 16856909) B16856909
theorem B7491959 : Blo 2077435 7491959 := bstep (se 1 (by rfl) ⟨5618969, by rfl⟩ : syracuseStep 7491959 = 11237939) B11237939
theorem B4994639 : Blo 2077435 4994639 := bstep (se 1 (by rfl) ⟨3745979, by rfl⟩ : syracuseStep 4994639 = 7491959) B7491959
theorem B3329759 : Blo 2077435 3329759 := bstep (se 1 (by rfl) ⟨2497319, by rfl⟩ : syracuseStep 3329759 = 4994639) B4994639
theorem B8879357 : Blo 2077435 8879357 := bstep (se 3 (by rfl) ⟨1664879, by rfl⟩ : syracuseStep 8879357 = 3329759) B3329759
theorem B5919571 : Blo 2077435 5919571 := bstep (se 1 (by rfl) ⟨4439678, by rfl⟩ : syracuseStep 5919571 = 8879357) B8879357
theorem B7892761 : Blo 2077435 7892761 := bstep (se 2 (by rfl) ⟨2959785, by rfl⟩ : syracuseStep 7892761 = 5919571) B5919571
theorem B10523681 : Blo 2077435 10523681 := bstep (se 2 (by rfl) ⟨3946380, by rfl⟩ : syracuseStep 10523681 = 7892761) B7892761
theorem B7015787 : Blo 2077435 7015787 := bstep (se 1 (by rfl) ⟨5261840, by rfl⟩ : syracuseStep 7015787 = 10523681) B10523681
theorem B4677191 : Blo 2077435 4677191 := bstep (se 1 (by rfl) ⟨3507893, by rfl⟩ : syracuseStep 4677191 = 7015787) B7015787
theorem B3118127 : Blo 2077435 3118127 := bstep (se 1 (by rfl) ⟨2338595, by rfl⟩ : syracuseStep 3118127 = 4677191) B4677191
theorem B2078751 : Blo 2077435 2078751 := bstep (se 1 (by rfl) ⟨1559063, by rfl⟩ : syracuseStep 2078751 = 3118127) B3118127
theorem B3118133 : Blo 2077435 3118133 := bbase (se 5 (by rfl) ⟨146162, by rfl⟩ : syracuseStep 3118133 = 292325) (by norm_num)
theorem B2078755 : Blo 2077435 2078755 := bstep (se 1 (by rfl) ⟨1559066, by rfl⟩ : syracuseStep 2078755 = 3118133) B3118133
theorem B5261861 : Blo 2077435 5261861 := bbase (se 4 (by rfl) ⟨493299, by rfl⟩ : syracuseStep 5261861 = 986599) (by norm_num)
theorem B3507907 : Blo 2077435 3507907 := bstep (se 1 (by rfl) ⟨2630930, by rfl⟩ : syracuseStep 3507907 = 5261861) B5261861
theorem B4677209 : Blo 2077435 4677209 := bstep (se 2 (by rfl) ⟨1753953, by rfl⟩ : syracuseStep 4677209 = 3507907) B3507907
theorem B3118139 : Blo 2077435 3118139 := bstep (se 1 (by rfl) ⟨2338604, by rfl⟩ : syracuseStep 3118139 = 4677209) B4677209
theorem B2078759 : Blo 2077435 2078759 := bstep (se 1 (by rfl) ⟨1559069, by rfl⟩ : syracuseStep 2078759 = 3118139) B3118139
theorem B2338609 : Blo 2077435 2338609 := bbase (se 2 (by rfl) ⟨876978, by rfl⟩ : syracuseStep 2338609 = 1753957) (by norm_num)
theorem B3118145 : Blo 2077435 3118145 := bstep (se 2 (by rfl) ⟨1169304, by rfl⟩ : syracuseStep 3118145 = 2338609) B2338609
theorem B2078763 : Blo 2077435 2078763 := bstep (se 1 (by rfl) ⟨1559072, by rfl⟩ : syracuseStep 2078763 = 3118145) B3118145
theorem B4214261 : Blo 2077435 4214261 := bbase (se 5 (by rfl) ⟨197543, by rfl⟩ : syracuseStep 4214261 = 395087) (by norm_num)
theorem B2809507 : Blo 2077435 2809507 := bstep (se 1 (by rfl) ⟨2107130, by rfl⟩ : syracuseStep 2809507 = 4214261) B4214261
theorem B3746009 : Blo 2077435 3746009 := bstep (se 2 (by rfl) ⟨1404753, by rfl⟩ : syracuseStep 3746009 = 2809507) B2809507
theorem B2497339 : Blo 2077435 2497339 := bstep (se 1 (by rfl) ⟨1873004, by rfl⟩ : syracuseStep 2497339 = 3746009) B3746009
theorem B3329785 : Blo 2077435 3329785 := bstep (se 2 (by rfl) ⟨1248669, by rfl⟩ : syracuseStep 3329785 = 2497339) B2497339
theorem B4439713 : Blo 2077435 4439713 := bstep (se 2 (by rfl) ⟨1664892, by rfl⟩ : syracuseStep 4439713 = 3329785) B3329785
theorem B5919617 : Blo 2077435 5919617 := bstep (se 2 (by rfl) ⟨2219856, by rfl⟩ : syracuseStep 5919617 = 4439713) B4439713
theorem B3946411 : Blo 2077435 3946411 := bstep (se 1 (by rfl) ⟨2959808, by rfl⟩ : syracuseStep 3946411 = 5919617) B5919617
theorem B5261881 : Blo 2077435 5261881 := bstep (se 2 (by rfl) ⟨1973205, by rfl⟩ : syracuseStep 5261881 = 3946411) B3946411
theorem B7015841 : Blo 2077435 7015841 := bstep (se 2 (by rfl) ⟨2630940, by rfl⟩ : syracuseStep 7015841 = 5261881) B5261881
theorem B4677227 : Blo 2077435 4677227 := bstep (se 1 (by rfl) ⟨3507920, by rfl⟩ : syracuseStep 4677227 = 7015841) B7015841
theorem B3118151 : Blo 2077435 3118151 := bstep (se 1 (by rfl) ⟨2338613, by rfl⟩ : syracuseStep 3118151 = 4677227) B4677227
theorem B2078767 : Blo 2077435 2078767 := bstep (se 1 (by rfl) ⟨1559075, by rfl⟩ : syracuseStep 2078767 = 3118151) B3118151
theorem B3118157 : Blo 2077435 3118157 := bbase (se 3 (by rfl) ⟨584654, by rfl⟩ : syracuseStep 3118157 = 1169309) (by norm_num)
theorem B2078771 : Blo 2077435 2078771 := bstep (se 1 (by rfl) ⟨1559078, by rfl⟩ : syracuseStep 2078771 = 3118157) B3118157
theorem B4677245 : Blo 2077435 4677245 := bbase (se 3 (by rfl) ⟨876983, by rfl⟩ : syracuseStep 4677245 = 1753967) (by norm_num)
theorem B3118163 : Blo 2077435 3118163 := bstep (se 1 (by rfl) ⟨2338622, by rfl⟩ : syracuseStep 3118163 = 4677245) B4677245
theorem B2078775 : Blo 2077435 2078775 := bstep (se 1 (by rfl) ⟨1559081, by rfl⟩ : syracuseStep 2078775 = 3118163) B3118163
theorem B3507941 : Blo 2077435 3507941 := bbase (se 4 (by rfl) ⟨328869, by rfl⟩ : syracuseStep 3507941 = 657739) (by norm_num)
theorem B2338627 : Blo 2077435 2338627 := bstep (se 1 (by rfl) ⟨1753970, by rfl⟩ : syracuseStep 2338627 = 3507941) B3507941
theorem B3118169 : Blo 2077435 3118169 := bstep (se 2 (by rfl) ⟨1169313, by rfl⟩ : syracuseStep 3118169 = 2338627) B2338627
theorem B2078779 : Blo 2077435 2078779 := bstep (se 1 (by rfl) ⟨1559084, by rfl⟩ : syracuseStep 2078779 = 3118169) B3118169
theorem B6659621 : Blo 2077435 6659621 := bbase (se 4 (by rfl) ⟨624339, by rfl⟩ : syracuseStep 6659621 = 1248679) (by norm_num)
theorem B4439747 : Blo 2077435 4439747 := bstep (se 1 (by rfl) ⟨3329810, by rfl⟩ : syracuseStep 4439747 = 6659621) B6659621
theorem B2959831 : Blo 2077435 2959831 := bstep (se 1 (by rfl) ⟨2219873, by rfl⟩ : syracuseStep 2959831 = 4439747) B4439747
theorem B15785765 : Blo 2077435 15785765 := bstep (se 4 (by rfl) ⟨1479915, by rfl⟩ : syracuseStep 15785765 = 2959831) B2959831
theorem B10523843 : Blo 2077435 10523843 := bstep (se 1 (by rfl) ⟨7892882, by rfl⟩ : syracuseStep 10523843 = 15785765) B15785765
theorem B7015895 : Blo 2077435 7015895 := bstep (se 1 (by rfl) ⟨5261921, by rfl⟩ : syracuseStep 7015895 = 10523843) B10523843
theorem B4677263 : Blo 2077435 4677263 := bstep (se 1 (by rfl) ⟨3507947, by rfl⟩ : syracuseStep 4677263 = 7015895) B7015895
theorem B3118175 : Blo 2077435 3118175 := bstep (se 1 (by rfl) ⟨2338631, by rfl⟩ : syracuseStep 3118175 = 4677263) B4677263
theorem B2078783 : Blo 2077435 2078783 := bstep (se 1 (by rfl) ⟨1559087, by rfl⟩ : syracuseStep 2078783 = 3118175) B3118175
theorem B3118181 : Blo 2077435 3118181 := bbase (se 4 (by rfl) ⟨292329, by rfl⟩ : syracuseStep 3118181 = 584659) (by norm_num)
theorem B2078787 : Blo 2077435 2078787 := bstep (se 1 (by rfl) ⟨1559090, by rfl⟩ : syracuseStep 2078787 = 3118181) B3118181
theorem B4439765 : Blo 2077435 4439765 := bbase (se 7 (by rfl) ⟨52028, by rfl⟩ : syracuseStep 4439765 = 104057) (by norm_num)
theorem B2959843 : Blo 2077435 2959843 := bstep (se 1 (by rfl) ⟨2219882, by rfl⟩ : syracuseStep 2959843 = 4439765) B4439765
theorem B3946457 : Blo 2077435 3946457 := bstep (se 2 (by rfl) ⟨1479921, by rfl⟩ : syracuseStep 3946457 = 2959843) B2959843
theorem B2630971 : Blo 2077435 2630971 := bstep (se 1 (by rfl) ⟨1973228, by rfl⟩ : syracuseStep 2630971 = 3946457) B3946457
theorem B3507961 : Blo 2077435 3507961 := bstep (se 2 (by rfl) ⟨1315485, by rfl⟩ : syracuseStep 3507961 = 2630971) B2630971
theorem B4677281 : Blo 2077435 4677281 := bstep (se 2 (by rfl) ⟨1753980, by rfl⟩ : syracuseStep 4677281 = 3507961) B3507961
theorem B3118187 : Blo 2077435 3118187 := bstep (se 1 (by rfl) ⟨2338640, by rfl⟩ : syracuseStep 3118187 = 4677281) B4677281
theorem B2078791 : Blo 2077435 2078791 := bstep (se 1 (by rfl) ⟨1559093, by rfl⟩ : syracuseStep 2078791 = 3118187) B3118187
theorem B2338645 : Blo 2077435 2338645 := bbase (se 9 (by rfl) ⟨6851, by rfl⟩ : syracuseStep 2338645 = 13703) (by norm_num)
theorem B3118193 : Blo 2077435 3118193 := bstep (se 2 (by rfl) ⟨1169322, by rfl⟩ : syracuseStep 3118193 = 2338645) B2338645
theorem B2078795 : Blo 2077435 2078795 := bstep (se 1 (by rfl) ⟨1559096, by rfl⟩ : syracuseStep 2078795 = 3118193) B3118193
theorem B2630981 : Blo 2077435 2630981 := bbase (se 4 (by rfl) ⟨246654, by rfl⟩ : syracuseStep 2630981 = 493309) (by norm_num)
theorem B7015949 : Blo 2077435 7015949 := bstep (se 3 (by rfl) ⟨1315490, by rfl⟩ : syracuseStep 7015949 = 2630981) B2630981
theorem B4677299 : Blo 2077435 4677299 := bstep (se 1 (by rfl) ⟨3507974, by rfl⟩ : syracuseStep 4677299 = 7015949) B7015949
theorem B3118199 : Blo 2077435 3118199 := bstep (se 1 (by rfl) ⟨2338649, by rfl⟩ : syracuseStep 3118199 = 4677299) B4677299
theorem B2078799 : Blo 2077435 2078799 := bstep (se 1 (by rfl) ⟨1559099, by rfl⟩ : syracuseStep 2078799 = 3118199) B3118199
theorem B3118205 : Blo 2077435 3118205 := bbase (se 3 (by rfl) ⟨584663, by rfl⟩ : syracuseStep 3118205 = 1169327) (by norm_num)
theorem B2078803 : Blo 2077435 2078803 := bstep (se 1 (by rfl) ⟨1559102, by rfl⟩ : syracuseStep 2078803 = 3118205) B3118205
theorem B4677317 : Blo 2077435 4677317 := bbase (se 4 (by rfl) ⟨438498, by rfl⟩ : syracuseStep 4677317 = 876997) (by norm_num)
theorem B3118211 : Blo 2077435 3118211 := bstep (se 1 (by rfl) ⟨2338658, by rfl⟩ : syracuseStep 3118211 = 4677317) B4677317
theorem B2078807 : Blo 2077435 2078807 := bstep (se 1 (by rfl) ⟨1559105, by rfl⟩ : syracuseStep 2078807 = 3118211) B3118211
theorem B15188789 : Blo 2077435 15188789 := bbase (se 5 (by rfl) ⟨711974, by rfl⟩ : syracuseStep 15188789 = 1423949) (by norm_num)
theorem B10125859 : Blo 2077435 10125859 := bstep (se 1 (by rfl) ⟨7594394, by rfl⟩ : syracuseStep 10125859 = 15188789) B15188789
theorem B13501145 : Blo 2077435 13501145 := bstep (se 2 (by rfl) ⟨5062929, by rfl⟩ : syracuseStep 13501145 = 10125859) B10125859
theorem B9000763 : Blo 2077435 9000763 := bstep (se 1 (by rfl) ⟨6750572, by rfl⟩ : syracuseStep 9000763 = 13501145) B13501145
theorem B192016277 : Blo 2077435 192016277 := bstep (se 6 (by rfl) ⟨4500381, by rfl⟩ : syracuseStep 192016277 = 9000763) B9000763
theorem B128010851 : Blo 2077435 128010851 := bstep (se 1 (by rfl) ⟨96008138, by rfl⟩ : syracuseStep 128010851 = 192016277) B192016277
theorem B85340567 : Blo 2077435 85340567 := bstep (se 1 (by rfl) ⟨64005425, by rfl⟩ : syracuseStep 85340567 = 128010851) B128010851
theorem B227574845 : Blo 2077435 227574845 := bstep (se 3 (by rfl) ⟨42670283, by rfl⟩ : syracuseStep 227574845 = 85340567) B85340567
theorem B151716563 : Blo 2077435 151716563 := bstep (se 1 (by rfl) ⟨113787422, by rfl⟩ : syracuseStep 151716563 = 227574845) B227574845
theorem B101144375 : Blo 2077435 101144375 := bstep (se 1 (by rfl) ⟨75858281, by rfl⟩ : syracuseStep 101144375 = 151716563) B151716563
theorem B67429583 : Blo 2077435 67429583 := bstep (se 1 (by rfl) ⟨50572187, by rfl⟩ : syracuseStep 67429583 = 101144375) B101144375
theorem B44953055 : Blo 2077435 44953055 := bstep (se 1 (by rfl) ⟨33714791, by rfl⟩ : syracuseStep 44953055 = 67429583) B67429583
theorem B29968703 : Blo 2077435 29968703 := bstep (se 1 (by rfl) ⟨22476527, by rfl⟩ : syracuseStep 29968703 = 44953055) B44953055
theorem B19979135 : Blo 2077435 19979135 := bstep (se 1 (by rfl) ⟨14984351, by rfl⟩ : syracuseStep 19979135 = 29968703) B29968703
theorem B13319423 : Blo 2077435 13319423 := bstep (se 1 (by rfl) ⟨9989567, by rfl⟩ : syracuseStep 13319423 = 19979135) B19979135
theorem B8879615 : Blo 2077435 8879615 := bstep (se 1 (by rfl) ⟨6659711, by rfl⟩ : syracuseStep 8879615 = 13319423) B13319423
theorem B5919743 : Blo 2077435 5919743 := bstep (se 1 (by rfl) ⟨4439807, by rfl⟩ : syracuseStep 5919743 = 8879615) B8879615
theorem B3946495 : Blo 2077435 3946495 := bstep (se 1 (by rfl) ⟨2959871, by rfl⟩ : syracuseStep 3946495 = 5919743) B5919743
theorem B5261993 : Blo 2077435 5261993 := bstep (se 2 (by rfl) ⟨1973247, by rfl⟩ : syracuseStep 5261993 = 3946495) B3946495
theorem B3507995 : Blo 2077435 3507995 := bstep (se 1 (by rfl) ⟨2630996, by rfl⟩ : syracuseStep 3507995 = 5261993) B5261993
theorem B2338663 : Blo 2077435 2338663 := bstep (se 1 (by rfl) ⟨1753997, by rfl⟩ : syracuseStep 2338663 = 3507995) B3507995
theorem B3118217 : Blo 2077435 3118217 := bstep (se 2 (by rfl) ⟨1169331, by rfl⟩ : syracuseStep 3118217 = 2338663) B2338663
theorem B2078811 : Blo 2077435 2078811 := bstep (se 1 (by rfl) ⟨1559108, by rfl⟩ : syracuseStep 2078811 = 3118217) B3118217
theorem B10524005 : Blo 2077435 10524005 := bbase (se 4 (by rfl) ⟨986625, by rfl⟩ : syracuseStep 10524005 = 1973251) (by norm_num)
theorem B7016003 : Blo 2077435 7016003 := bstep (se 1 (by rfl) ⟨5262002, by rfl⟩ : syracuseStep 7016003 = 10524005) B10524005
theorem B4677335 : Blo 2077435 4677335 := bstep (se 1 (by rfl) ⟨3508001, by rfl⟩ : syracuseStep 4677335 = 7016003) B7016003
theorem B3118223 : Blo 2077435 3118223 := bstep (se 1 (by rfl) ⟨2338667, by rfl⟩ : syracuseStep 3118223 = 4677335) B4677335
theorem B2078815 : Blo 2077435 2078815 := bstep (se 1 (by rfl) ⟨1559111, by rfl⟩ : syracuseStep 2078815 = 3118223) B3118223
theorem B3118229 : Blo 2077435 3118229 := bbase (se 6 (by rfl) ⟨73083, by rfl⟩ : syracuseStep 3118229 = 146167) (by norm_num)
theorem B2078819 : Blo 2077435 2078819 := bstep (se 1 (by rfl) ⟨1559114, by rfl⟩ : syracuseStep 2078819 = 3118229) B3118229
theorem B6659749 : Blo 2077435 6659749 := bbase (se 4 (by rfl) ⟨624351, by rfl⟩ : syracuseStep 6659749 = 1248703) (by norm_num)
theorem B8879665 : Blo 2077435 8879665 := bstep (se 2 (by rfl) ⟨3329874, by rfl⟩ : syracuseStep 8879665 = 6659749) B6659749
theorem B11839553 : Blo 2077435 11839553 := bstep (se 2 (by rfl) ⟨4439832, by rfl⟩ : syracuseStep 11839553 = 8879665) B8879665
theorem B7893035 : Blo 2077435 7893035 := bstep (se 1 (by rfl) ⟨5919776, by rfl⟩ : syracuseStep 7893035 = 11839553) B11839553
theorem B5262023 : Blo 2077435 5262023 := bstep (se 1 (by rfl) ⟨3946517, by rfl⟩ : syracuseStep 5262023 = 7893035) B7893035
theorem B3508015 : Blo 2077435 3508015 := bstep (se 1 (by rfl) ⟨2631011, by rfl⟩ : syracuseStep 3508015 = 5262023) B5262023
theorem B4677353 : Blo 2077435 4677353 := bstep (se 2 (by rfl) ⟨1754007, by rfl⟩ : syracuseStep 4677353 = 3508015) B3508015
theorem B3118235 : Blo 2077435 3118235 := bstep (se 1 (by rfl) ⟨2338676, by rfl⟩ : syracuseStep 3118235 = 4677353) B4677353
theorem B2078823 : Blo 2077435 2078823 := bstep (se 1 (by rfl) ⟨1559117, by rfl⟩ : syracuseStep 2078823 = 3118235) B3118235
theorem B2338681 : Blo 2077435 2338681 := bbase (se 2 (by rfl) ⟨877005, by rfl⟩ : syracuseStep 2338681 = 1754011) (by norm_num)
theorem B3118241 : Blo 2077435 3118241 := bstep (se 2 (by rfl) ⟨1169340, by rfl⟩ : syracuseStep 3118241 = 2338681) B2338681
theorem B2078827 : Blo 2077435 2078827 := bstep (se 1 (by rfl) ⟨1559120, by rfl⟩ : syracuseStep 2078827 = 3118241) B3118241
theorem B16857557 : Blo 2077435 16857557 := bbase (se 7 (by rfl) ⟨197549, by rfl⟩ : syracuseStep 16857557 = 395099) (by norm_num)
theorem B11238371 : Blo 2077435 11238371 := bstep (se 1 (by rfl) ⟨8428778, by rfl⟩ : syracuseStep 11238371 = 16857557) B16857557
theorem B7492247 : Blo 2077435 7492247 := bstep (se 1 (by rfl) ⟨5619185, by rfl⟩ : syracuseStep 7492247 = 11238371) B11238371
theorem B4994831 : Blo 2077435 4994831 := bstep (se 1 (by rfl) ⟨3746123, by rfl⟩ : syracuseStep 4994831 = 7492247) B7492247
theorem B13319549 : Blo 2077435 13319549 := bstep (se 3 (by rfl) ⟨2497415, by rfl⟩ : syracuseStep 13319549 = 4994831) B4994831
theorem B8879699 : Blo 2077435 8879699 := bstep (se 1 (by rfl) ⟨6659774, by rfl⟩ : syracuseStep 8879699 = 13319549) B13319549
theorem B5919799 : Blo 2077435 5919799 := bstep (se 1 (by rfl) ⟨4439849, by rfl⟩ : syracuseStep 5919799 = 8879699) B8879699
theorem B7893065 : Blo 2077435 7893065 := bstep (se 2 (by rfl) ⟨2959899, by rfl⟩ : syracuseStep 7893065 = 5919799) B5919799
theorem B5262043 : Blo 2077435 5262043 := bstep (se 1 (by rfl) ⟨3946532, by rfl⟩ : syracuseStep 5262043 = 7893065) B7893065
theorem B7016057 : Blo 2077435 7016057 := bstep (se 2 (by rfl) ⟨2631021, by rfl⟩ : syracuseStep 7016057 = 5262043) B5262043
theorem B4677371 : Blo 2077435 4677371 := bstep (se 1 (by rfl) ⟨3508028, by rfl⟩ : syracuseStep 4677371 = 7016057) B7016057
theorem B3118247 : Blo 2077435 3118247 := bstep (se 1 (by rfl) ⟨2338685, by rfl⟩ : syracuseStep 3118247 = 4677371) B4677371
theorem B2078831 : Blo 2077435 2078831 := bstep (se 1 (by rfl) ⟨1559123, by rfl⟩ : syracuseStep 2078831 = 3118247) B3118247
theorem B3118253 : Blo 2077435 3118253 := bbase (se 3 (by rfl) ⟨584672, by rfl⟩ : syracuseStep 3118253 = 1169345) (by norm_num)
theorem B2078835 : Blo 2077435 2078835 := bstep (se 1 (by rfl) ⟨1559126, by rfl⟩ : syracuseStep 2078835 = 3118253) B3118253
theorem B4677389 : Blo 2077435 4677389 := bbase (se 3 (by rfl) ⟨877010, by rfl⟩ : syracuseStep 4677389 = 1754021) (by norm_num)
theorem B3118259 : Blo 2077435 3118259 := bstep (se 1 (by rfl) ⟨2338694, by rfl⟩ : syracuseStep 3118259 = 4677389) B4677389
theorem B2078839 : Blo 2077435 2078839 := bstep (se 1 (by rfl) ⟨1559129, by rfl⟩ : syracuseStep 2078839 = 3118259) B3118259
theorem B2631037 : Blo 2077435 2631037 := bbase (se 3 (by rfl) ⟨493319, by rfl⟩ : syracuseStep 2631037 = 986639) (by norm_num)
theorem B3508049 : Blo 2077435 3508049 := bstep (se 2 (by rfl) ⟨1315518, by rfl⟩ : syracuseStep 3508049 = 2631037) B2631037
theorem B2338699 : Blo 2077435 2338699 := bstep (se 1 (by rfl) ⟨1754024, by rfl⟩ : syracuseStep 2338699 = 3508049) B3508049
theorem B3118265 : Blo 2077435 3118265 := bstep (se 2 (by rfl) ⟨1169349, by rfl⟩ : syracuseStep 3118265 = 2338699) B2338699
theorem B2078843 : Blo 2077435 2078843 := bstep (se 1 (by rfl) ⟨1559132, by rfl⟩ : syracuseStep 2078843 = 3118265) B3118265
theorem B4994869 : Blo 2077435 4994869 := bbase (se 5 (by rfl) ⟨234134, by rfl⟩ : syracuseStep 4994869 = 468269) (by norm_num)
theorem B6659825 : Blo 2077435 6659825 := bstep (se 2 (by rfl) ⟨2497434, by rfl⟩ : syracuseStep 6659825 = 4994869) B4994869
theorem B17759533 : Blo 2077435 17759533 := bstep (se 3 (by rfl) ⟨3329912, by rfl⟩ : syracuseStep 17759533 = 6659825) B6659825
theorem B23679377 : Blo 2077435 23679377 := bstep (se 2 (by rfl) ⟨8879766, by rfl⟩ : syracuseStep 23679377 = 17759533) B17759533
theorem B15786251 : Blo 2077435 15786251 := bstep (se 1 (by rfl) ⟨11839688, by rfl⟩ : syracuseStep 15786251 = 23679377) B23679377
theorem B10524167 : Blo 2077435 10524167 := bstep (se 1 (by rfl) ⟨7893125, by rfl⟩ : syracuseStep 10524167 = 15786251) B15786251
theorem B7016111 : Blo 2077435 7016111 := bstep (se 1 (by rfl) ⟨5262083, by rfl⟩ : syracuseStep 7016111 = 10524167) B10524167
theorem B4677407 : Blo 2077435 4677407 := bstep (se 1 (by rfl) ⟨3508055, by rfl⟩ : syracuseStep 4677407 = 7016111) B7016111
theorem B3118271 : Blo 2077435 3118271 := bstep (se 1 (by rfl) ⟨2338703, by rfl⟩ : syracuseStep 3118271 = 4677407) B4677407
theorem B2078847 : Blo 2077435 2078847 := bstep (se 1 (by rfl) ⟨1559135, by rfl⟩ : syracuseStep 2078847 = 3118271) B3118271
theorem B3118277 : Blo 2077435 3118277 := bbase (se 4 (by rfl) ⟨292338, by rfl⟩ : syracuseStep 3118277 = 584677) (by norm_num)
theorem B2078851 : Blo 2077435 2078851 := bstep (se 1 (by rfl) ⟨1559138, by rfl⟩ : syracuseStep 2078851 = 3118277) B3118277
theorem B3508069 : Blo 2077435 3508069 := bbase (se 4 (by rfl) ⟨328881, by rfl⟩ : syracuseStep 3508069 = 657763) (by norm_num)
theorem B4677425 : Blo 2077435 4677425 := bstep (se 2 (by rfl) ⟨1754034, by rfl⟩ : syracuseStep 4677425 = 3508069) B3508069
theorem B3118283 : Blo 2077435 3118283 := bstep (se 1 (by rfl) ⟨2338712, by rfl⟩ : syracuseStep 3118283 = 4677425) B4677425
theorem B2078855 : Blo 2077435 2078855 := bstep (se 1 (by rfl) ⟨1559141, by rfl⟩ : syracuseStep 2078855 = 3118283) B3118283
theorem B2338717 : Blo 2077435 2338717 := bbase (se 3 (by rfl) ⟨438509, by rfl⟩ : syracuseStep 2338717 = 877019) (by norm_num)
theorem B3118289 : Blo 2077435 3118289 := bstep (se 2 (by rfl) ⟨1169358, by rfl⟩ : syracuseStep 3118289 = 2338717) B2338717
theorem B2078859 : Blo 2077435 2078859 := bstep (se 1 (by rfl) ⟨1559144, by rfl⟩ : syracuseStep 2078859 = 3118289) B3118289
theorem B7016165 : Blo 2077435 7016165 := bbase (se 4 (by rfl) ⟨657765, by rfl⟩ : syracuseStep 7016165 = 1315531) (by norm_num)
theorem B4677443 : Blo 2077435 4677443 := bstep (se 1 (by rfl) ⟨3508082, by rfl⟩ : syracuseStep 4677443 = 7016165) B7016165
theorem B3118295 : Blo 2077435 3118295 := bstep (se 1 (by rfl) ⟨2338721, by rfl⟩ : syracuseStep 3118295 = 4677443) B4677443
theorem B2078863 : Blo 2077435 2078863 := bstep (se 1 (by rfl) ⟨1559147, by rfl⟩ : syracuseStep 2078863 = 3118295) B3118295
theorem B3118301 : Blo 2077435 3118301 := bbase (se 3 (by rfl) ⟨584681, by rfl⟩ : syracuseStep 3118301 = 1169363) (by norm_num)
theorem B2078867 : Blo 2077435 2078867 := bstep (se 1 (by rfl) ⟨1559150, by rfl⟩ : syracuseStep 2078867 = 3118301) B3118301
theorem B4677461 : Blo 2077435 4677461 := bbase (se 9 (by rfl) ⟨13703, by rfl⟩ : syracuseStep 4677461 = 27407) (by norm_num)
theorem B3118307 : Blo 2077435 3118307 := bstep (se 1 (by rfl) ⟨2338730, by rfl⟩ : syracuseStep 3118307 = 4677461) B4677461
theorem B2078871 : Blo 2077435 2078871 := bstep (se 1 (by rfl) ⟨1559153, by rfl⟩ : syracuseStep 2078871 = 3118307) B3118307
theorem B5919925 : Blo 2077435 5919925 := bbase (se 5 (by rfl) ⟨277496, by rfl⟩ : syracuseStep 5919925 = 554993) (by norm_num)
theorem B7893233 : Blo 2077435 7893233 := bstep (se 2 (by rfl) ⟨2959962, by rfl⟩ : syracuseStep 7893233 = 5919925) B5919925
theorem B5262155 : Blo 2077435 5262155 := bstep (se 1 (by rfl) ⟨3946616, by rfl⟩ : syracuseStep 5262155 = 7893233) B7893233
theorem B3508103 : Blo 2077435 3508103 := bstep (se 1 (by rfl) ⟨2631077, by rfl⟩ : syracuseStep 3508103 = 5262155) B5262155
theorem B2338735 : Blo 2077435 2338735 := bstep (se 1 (by rfl) ⟨1754051, by rfl⟩ : syracuseStep 2338735 = 3508103) B3508103
theorem B3118313 : Blo 2077435 3118313 := bstep (se 2 (by rfl) ⟨1169367, by rfl⟩ : syracuseStep 3118313 = 2338735) B2338735
theorem B2078875 : Blo 2077435 2078875 := bstep (se 1 (by rfl) ⟨1559156, by rfl⟩ : syracuseStep 2078875 = 3118313) B3118313
theorem B2402993 : Blo 2077435 2402993 := bbase (se 2 (by rfl) ⟨901122, by rfl⟩ : syracuseStep 2402993 = 1802245) (by norm_num)
theorem B6407981 : Blo 2077435 6407981 := bstep (se 3 (by rfl) ⟨1201496, by rfl⟩ : syracuseStep 6407981 = 2402993) B2402993
theorem B4271987 : Blo 2077435 4271987 := bstep (se 1 (by rfl) ⟨3203990, by rfl⟩ : syracuseStep 4271987 = 6407981) B6407981
theorem B11391965 : Blo 2077435 11391965 := bstep (se 3 (by rfl) ⟨2135993, by rfl⟩ : syracuseStep 11391965 = 4271987) B4271987
theorem B7594643 : Blo 2077435 7594643 := bstep (se 1 (by rfl) ⟨5695982, by rfl⟩ : syracuseStep 7594643 = 11391965) B11391965
theorem B5063095 : Blo 2077435 5063095 := bstep (se 1 (by rfl) ⟨3797321, by rfl⟩ : syracuseStep 5063095 = 7594643) B7594643
theorem B6750793 : Blo 2077435 6750793 := bstep (se 2 (by rfl) ⟨2531547, by rfl⟩ : syracuseStep 6750793 = 5063095) B5063095
theorem B9001057 : Blo 2077435 9001057 := bstep (se 2 (by rfl) ⟨3375396, by rfl⟩ : syracuseStep 9001057 = 6750793) B6750793
theorem B12001409 : Blo 2077435 12001409 := bstep (se 2 (by rfl) ⟨4500528, by rfl⟩ : syracuseStep 12001409 = 9001057) B9001057
theorem B8000939 : Blo 2077435 8000939 := bstep (se 1 (by rfl) ⟨6000704, by rfl⟩ : syracuseStep 8000939 = 12001409) B12001409
theorem B5333959 : Blo 2077435 5333959 := bstep (se 1 (by rfl) ⟨4000469, by rfl⟩ : syracuseStep 5333959 = 8000939) B8000939
theorem B7111945 : Blo 2077435 7111945 := bstep (se 2 (by rfl) ⟨2666979, by rfl⟩ : syracuseStep 7111945 = 5333959) B5333959
theorem B9482593 : Blo 2077435 9482593 := bstep (se 2 (by rfl) ⟨3555972, by rfl⟩ : syracuseStep 9482593 = 7111945) B7111945
theorem B12643457 : Blo 2077435 12643457 := bstep (se 2 (by rfl) ⟨4741296, by rfl⟩ : syracuseStep 12643457 = 9482593) B9482593
theorem B134863541 : Blo 2077435 134863541 := bstep (se 5 (by rfl) ⟨6321728, by rfl⟩ : syracuseStep 134863541 = 12643457) B12643457
theorem B89909027 : Blo 2077435 89909027 := bstep (se 1 (by rfl) ⟨67431770, by rfl⟩ : syracuseStep 89909027 = 134863541) B134863541
theorem B59939351 : Blo 2077435 59939351 := bstep (se 1 (by rfl) ⟨44954513, by rfl⟩ : syracuseStep 59939351 = 89909027) B89909027
theorem B39959567 : Blo 2077435 39959567 := bstep (se 1 (by rfl) ⟨29969675, by rfl⟩ : syracuseStep 39959567 = 59939351) B59939351
theorem B26639711 : Blo 2077435 26639711 := bstep (se 1 (by rfl) ⟨19979783, by rfl⟩ : syracuseStep 26639711 = 39959567) B39959567
theorem B17759807 : Blo 2077435 17759807 := bstep (se 1 (by rfl) ⟨13319855, by rfl⟩ : syracuseStep 17759807 = 26639711) B26639711
theorem B11839871 : Blo 2077435 11839871 := bstep (se 1 (by rfl) ⟨8879903, by rfl⟩ : syracuseStep 11839871 = 17759807) B17759807
theorem B7893247 : Blo 2077435 7893247 := bstep (se 1 (by rfl) ⟨5919935, by rfl⟩ : syracuseStep 7893247 = 11839871) B11839871
theorem B10524329 : Blo 2077435 10524329 := bstep (se 2 (by rfl) ⟨3946623, by rfl⟩ : syracuseStep 10524329 = 7893247) B7893247
theorem B7016219 : Blo 2077435 7016219 := bstep (se 1 (by rfl) ⟨5262164, by rfl⟩ : syracuseStep 7016219 = 10524329) B10524329
theorem B4677479 : Blo 2077435 4677479 := bstep (se 1 (by rfl) ⟨3508109, by rfl⟩ : syracuseStep 4677479 = 7016219) B7016219
theorem B3118319 : Blo 2077435 3118319 := bstep (se 1 (by rfl) ⟨2338739, by rfl⟩ : syracuseStep 3118319 = 4677479) B4677479
theorem B2078879 : Blo 2077435 2078879 := bstep (se 1 (by rfl) ⟨1559159, by rfl⟩ : syracuseStep 2078879 = 3118319) B3118319
theorem B3118325 : Blo 2077435 3118325 := bbase (se 5 (by rfl) ⟨146171, by rfl⟩ : syracuseStep 3118325 = 292343) (by norm_num)
theorem B2078883 : Blo 2077435 2078883 := bstep (se 1 (by rfl) ⟨1559162, by rfl⟩ : syracuseStep 2078883 = 3118325) B3118325
theorem B2809669 : Blo 2077435 2809669 := bbase (se 4 (by rfl) ⟨263406, by rfl⟩ : syracuseStep 2809669 = 526813) (by norm_num)
theorem B3746225 : Blo 2077435 3746225 := bstep (se 2 (by rfl) ⟨1404834, by rfl⟩ : syracuseStep 3746225 = 2809669) B2809669
theorem B2497483 : Blo 2077435 2497483 := bstep (se 1 (by rfl) ⟨1873112, by rfl⟩ : syracuseStep 2497483 = 3746225) B3746225
theorem B13319909 : Blo 2077435 13319909 := bstep (se 4 (by rfl) ⟨1248741, by rfl⟩ : syracuseStep 13319909 = 2497483) B2497483
theorem B8879939 : Blo 2077435 8879939 := bstep (se 1 (by rfl) ⟨6659954, by rfl⟩ : syracuseStep 8879939 = 13319909) B13319909
theorem B5919959 : Blo 2077435 5919959 := bstep (se 1 (by rfl) ⟨4439969, by rfl⟩ : syracuseStep 5919959 = 8879939) B8879939
theorem B3946639 : Blo 2077435 3946639 := bstep (se 1 (by rfl) ⟨2959979, by rfl⟩ : syracuseStep 3946639 = 5919959) B5919959
theorem B5262185 : Blo 2077435 5262185 := bstep (se 2 (by rfl) ⟨1973319, by rfl⟩ : syracuseStep 5262185 = 3946639) B3946639
theorem B3508123 : Blo 2077435 3508123 := bstep (se 1 (by rfl) ⟨2631092, by rfl⟩ : syracuseStep 3508123 = 5262185) B5262185
theorem B4677497 : Blo 2077435 4677497 := bstep (se 2 (by rfl) ⟨1754061, by rfl⟩ : syracuseStep 4677497 = 3508123) B3508123
theorem B3118331 : Blo 2077435 3118331 := bstep (se 1 (by rfl) ⟨2338748, by rfl⟩ : syracuseStep 3118331 = 4677497) B4677497
theorem B2078887 : Blo 2077435 2078887 := bstep (se 1 (by rfl) ⟨1559165, by rfl⟩ : syracuseStep 2078887 = 3118331) B3118331
theorem B2338753 : Blo 2077435 2338753 := bbase (se 2 (by rfl) ⟨877032, by rfl⟩ : syracuseStep 2338753 = 1754065) (by norm_num)
theorem B3118337 : Blo 2077435 3118337 := bstep (se 2 (by rfl) ⟨1169376, by rfl⟩ : syracuseStep 3118337 = 2338753) B2338753
theorem B2078891 : Blo 2077435 2078891 := bstep (se 1 (by rfl) ⟨1559168, by rfl⟩ : syracuseStep 2078891 = 3118337) B3118337
theorem B5262205 : Blo 2077435 5262205 := bbase (se 3 (by rfl) ⟨986663, by rfl⟩ : syracuseStep 5262205 = 1973327) (by norm_num)
theorem B7016273 : Blo 2077435 7016273 := bstep (se 2 (by rfl) ⟨2631102, by rfl⟩ : syracuseStep 7016273 = 5262205) B5262205
theorem B4677515 : Blo 2077435 4677515 := bstep (se 1 (by rfl) ⟨3508136, by rfl⟩ : syracuseStep 4677515 = 7016273) B7016273
theorem B3118343 : Blo 2077435 3118343 := bstep (se 1 (by rfl) ⟨2338757, by rfl⟩ : syracuseStep 3118343 = 4677515) B4677515
theorem B2078895 : Blo 2077435 2078895 := bstep (se 1 (by rfl) ⟨1559171, by rfl⟩ : syracuseStep 2078895 = 3118343) B3118343
theorem B3118349 : Blo 2077435 3118349 := bbase (se 3 (by rfl) ⟨584690, by rfl⟩ : syracuseStep 3118349 = 1169381) (by norm_num)
theorem B2078899 : Blo 2077435 2078899 := bstep (se 1 (by rfl) ⟨1559174, by rfl⟩ : syracuseStep 2078899 = 3118349) B3118349
theorem B4677533 : Blo 2077435 4677533 := bbase (se 3 (by rfl) ⟨877037, by rfl⟩ : syracuseStep 4677533 = 1754075) (by norm_num)
theorem B3118355 : Blo 2077435 3118355 := bstep (se 1 (by rfl) ⟨2338766, by rfl⟩ : syracuseStep 3118355 = 4677533) B4677533
theorem B2078903 : Blo 2077435 2078903 := bstep (se 1 (by rfl) ⟨1559177, by rfl⟩ : syracuseStep 2078903 = 3118355) B3118355
theorem B3508157 : Blo 2077435 3508157 := bbase (se 3 (by rfl) ⟨657779, by rfl⟩ : syracuseStep 3508157 = 1315559) (by norm_num)
theorem B2338771 : Blo 2077435 2338771 := bstep (se 1 (by rfl) ⟨1754078, by rfl⟩ : syracuseStep 2338771 = 3508157) B3508157
theorem B3118361 : Blo 2077435 3118361 := bstep (se 2 (by rfl) ⟨1169385, by rfl⟩ : syracuseStep 3118361 = 2338771) B2338771
theorem B2078907 : Blo 2077435 2078907 := bstep (se 1 (by rfl) ⟨1559180, by rfl⟩ : syracuseStep 2078907 = 3118361) B3118361
theorem B11840053 : Blo 2077435 11840053 := bbase (se 5 (by rfl) ⟨555002, by rfl⟩ : syracuseStep 11840053 = 1110005) (by norm_num)
theorem B15786737 : Blo 2077435 15786737 := bstep (se 2 (by rfl) ⟨5920026, by rfl⟩ : syracuseStep 15786737 = 11840053) B11840053
theorem B10524491 : Blo 2077435 10524491 := bstep (se 1 (by rfl) ⟨7893368, by rfl⟩ : syracuseStep 10524491 = 15786737) B15786737
theorem B7016327 : Blo 2077435 7016327 := bstep (se 1 (by rfl) ⟨5262245, by rfl⟩ : syracuseStep 7016327 = 10524491) B10524491
theorem B4677551 : Blo 2077435 4677551 := bstep (se 1 (by rfl) ⟨3508163, by rfl⟩ : syracuseStep 4677551 = 7016327) B7016327
theorem B3118367 : Blo 2077435 3118367 := bstep (se 1 (by rfl) ⟨2338775, by rfl⟩ : syracuseStep 3118367 = 4677551) B4677551
theorem B2078911 : Blo 2077435 2078911 := bstep (se 1 (by rfl) ⟨1559183, by rfl⟩ : syracuseStep 2078911 = 3118367) B3118367
theorem B3118373 : Blo 2077435 3118373 := bbase (se 4 (by rfl) ⟨292347, by rfl⟩ : syracuseStep 3118373 = 584695) (by norm_num)
theorem B2078915 : Blo 2077435 2078915 := bstep (se 1 (by rfl) ⟨1559186, by rfl⟩ : syracuseStep 2078915 = 3118373) B3118373
theorem B2631133 : Blo 2077435 2631133 := bbase (se 3 (by rfl) ⟨493337, by rfl⟩ : syracuseStep 2631133 = 986675) (by norm_num)
theorem B3508177 : Blo 2077435 3508177 := bstep (se 2 (by rfl) ⟨1315566, by rfl⟩ : syracuseStep 3508177 = 2631133) B2631133
theorem B4677569 : Blo 2077435 4677569 := bstep (se 2 (by rfl) ⟨1754088, by rfl⟩ : syracuseStep 4677569 = 3508177) B3508177
theorem B3118379 : Blo 2077435 3118379 := bstep (se 1 (by rfl) ⟨2338784, by rfl⟩ : syracuseStep 3118379 = 4677569) B4677569
theorem B2078919 : Blo 2077435 2078919 := bstep (se 1 (by rfl) ⟨1559189, by rfl⟩ : syracuseStep 2078919 = 3118379) B3118379
theorem B2338789 : Blo 2077435 2338789 := bbase (se 4 (by rfl) ⟨219261, by rfl⟩ : syracuseStep 2338789 = 438523) (by norm_num)
theorem B3118385 : Blo 2077435 3118385 := bstep (se 2 (by rfl) ⟨1169394, by rfl⟩ : syracuseStep 3118385 = 2338789) B2338789
theorem B2078923 : Blo 2077435 2078923 := bstep (se 1 (by rfl) ⟨1559192, by rfl⟩ : syracuseStep 2078923 = 3118385) B3118385
theorem B4000565 : Blo 2077435 4000565 := bbase (se 5 (by rfl) ⟨187526, by rfl⟩ : syracuseStep 4000565 = 375053) (by norm_num)
theorem B2667043 : Blo 2077435 2667043 := bstep (se 1 (by rfl) ⟨2000282, by rfl⟩ : syracuseStep 2667043 = 4000565) B4000565
theorem B3556057 : Blo 2077435 3556057 := bstep (se 2 (by rfl) ⟨1333521, by rfl⟩ : syracuseStep 3556057 = 2667043) B2667043
theorem B4741409 : Blo 2077435 4741409 := bstep (se 2 (by rfl) ⟨1778028, by rfl⟩ : syracuseStep 4741409 = 3556057) B3556057
theorem B3160939 : Blo 2077435 3160939 := bstep (se 1 (by rfl) ⟨2370704, by rfl⟩ : syracuseStep 3160939 = 4741409) B4741409
theorem B4214585 : Blo 2077435 4214585 := bstep (se 2 (by rfl) ⟨1580469, by rfl⟩ : syracuseStep 4214585 = 3160939) B3160939
theorem B2809723 : Blo 2077435 2809723 := bstep (se 1 (by rfl) ⟨2107292, by rfl⟩ : syracuseStep 2809723 = 4214585) B4214585
theorem B3746297 : Blo 2077435 3746297 := bstep (se 2 (by rfl) ⟨1404861, by rfl⟩ : syracuseStep 3746297 = 2809723) B2809723
theorem B9990125 : Blo 2077435 9990125 := bstep (se 3 (by rfl) ⟨1873148, by rfl⟩ : syracuseStep 9990125 = 3746297) B3746297
theorem B6660083 : Blo 2077435 6660083 := bstep (se 1 (by rfl) ⟨4995062, by rfl⟩ : syracuseStep 6660083 = 9990125) B9990125
theorem B4440055 : Blo 2077435 4440055 := bstep (se 1 (by rfl) ⟨3330041, by rfl⟩ : syracuseStep 4440055 = 6660083) B6660083
theorem B5920073 : Blo 2077435 5920073 := bstep (se 2 (by rfl) ⟨2220027, by rfl⟩ : syracuseStep 5920073 = 4440055) B4440055
theorem B3946715 : Blo 2077435 3946715 := bstep (se 1 (by rfl) ⟨2960036, by rfl⟩ : syracuseStep 3946715 = 5920073) B5920073
theorem B2631143 : Blo 2077435 2631143 := bstep (se 1 (by rfl) ⟨1973357, by rfl⟩ : syracuseStep 2631143 = 3946715) B3946715
theorem B7016381 : Blo 2077435 7016381 := bstep (se 3 (by rfl) ⟨1315571, by rfl⟩ : syracuseStep 7016381 = 2631143) B2631143
theorem B4677587 : Blo 2077435 4677587 := bstep (se 1 (by rfl) ⟨3508190, by rfl⟩ : syracuseStep 4677587 = 7016381) B7016381
theorem B3118391 : Blo 2077435 3118391 := bstep (se 1 (by rfl) ⟨2338793, by rfl⟩ : syracuseStep 3118391 = 4677587) B4677587
theorem B2078927 : Blo 2077435 2078927 := bstep (se 1 (by rfl) ⟨1559195, by rfl⟩ : syracuseStep 2078927 = 3118391) B3118391
theorem B3118397 : Blo 2077435 3118397 := bbase (se 3 (by rfl) ⟨584699, by rfl⟩ : syracuseStep 3118397 = 1169399) (by norm_num)
theorem B2078931 : Blo 2077435 2078931 := bstep (se 1 (by rfl) ⟨1559198, by rfl⟩ : syracuseStep 2078931 = 3118397) B3118397
theorem B4677605 : Blo 2077435 4677605 := bbase (se 4 (by rfl) ⟨438525, by rfl⟩ : syracuseStep 4677605 = 877051) (by norm_num)
theorem B3118403 : Blo 2077435 3118403 := bstep (se 1 (by rfl) ⟨2338802, by rfl⟩ : syracuseStep 3118403 = 4677605) B4677605
theorem B2078935 : Blo 2077435 2078935 := bstep (se 1 (by rfl) ⟨1559201, by rfl⟩ : syracuseStep 2078935 = 3118403) B3118403
theorem B5262317 : Blo 2077435 5262317 := bbase (se 3 (by rfl) ⟨986684, by rfl⟩ : syracuseStep 5262317 = 1973369) (by norm_num)
theorem B3508211 : Blo 2077435 3508211 := bstep (se 1 (by rfl) ⟨2631158, by rfl⟩ : syracuseStep 3508211 = 5262317) B5262317
theorem B2338807 : Blo 2077435 2338807 := bstep (se 1 (by rfl) ⟨1754105, by rfl⟩ : syracuseStep 2338807 = 3508211) B3508211
theorem B3118409 : Blo 2077435 3118409 := bstep (se 2 (by rfl) ⟨1169403, by rfl⟩ : syracuseStep 3118409 = 2338807) B2338807
theorem B2078939 : Blo 2077435 2078939 := bstep (se 1 (by rfl) ⟨1559204, by rfl⟩ : syracuseStep 2078939 = 3118409) B3118409
theorem B4995101 : Blo 2077435 4995101 := bbase (se 3 (by rfl) ⟨936581, by rfl⟩ : syracuseStep 4995101 = 1873163) (by norm_num)
theorem B3330067 : Blo 2077435 3330067 := bstep (se 1 (by rfl) ⟨2497550, by rfl⟩ : syracuseStep 3330067 = 4995101) B4995101
theorem B4440089 : Blo 2077435 4440089 := bstep (se 2 (by rfl) ⟨1665033, by rfl⟩ : syracuseStep 4440089 = 3330067) B3330067
theorem B2960059 : Blo 2077435 2960059 := bstep (se 1 (by rfl) ⟨2220044, by rfl⟩ : syracuseStep 2960059 = 4440089) B4440089
theorem B3946745 : Blo 2077435 3946745 := bstep (se 2 (by rfl) ⟨1480029, by rfl⟩ : syracuseStep 3946745 = 2960059) B2960059
theorem B10524653 : Blo 2077435 10524653 := bstep (se 3 (by rfl) ⟨1973372, by rfl⟩ : syracuseStep 10524653 = 3946745) B3946745
theorem B7016435 : Blo 2077435 7016435 := bstep (se 1 (by rfl) ⟨5262326, by rfl⟩ : syracuseStep 7016435 = 10524653) B10524653
theorem B4677623 : Blo 2077435 4677623 := bstep (se 1 (by rfl) ⟨3508217, by rfl⟩ : syracuseStep 4677623 = 7016435) B7016435
theorem B3118415 : Blo 2077435 3118415 := bstep (se 1 (by rfl) ⟨2338811, by rfl⟩ : syracuseStep 3118415 = 4677623) B4677623
theorem B2078943 : Blo 2077435 2078943 := bstep (se 1 (by rfl) ⟨1559207, by rfl⟩ : syracuseStep 2078943 = 3118415) B3118415
theorem B3118421 : Blo 2077435 3118421 := bbase (se 14 (by rfl) ⟨285, by rfl⟩ : syracuseStep 3118421 = 571) (by norm_num)
theorem B2078947 : Blo 2077435 2078947 := bstep (se 1 (by rfl) ⟨1559210, by rfl⟩ : syracuseStep 2078947 = 3118421) B3118421
theorem B2220053 : Blo 2077435 2220053 := bbase (se 6 (by rfl) ⟨52032, by rfl⟩ : syracuseStep 2220053 = 104065) (by norm_num)
theorem B5920141 : Blo 2077435 5920141 := bstep (se 3 (by rfl) ⟨1110026, by rfl⟩ : syracuseStep 5920141 = 2220053) B2220053
theorem B7893521 : Blo 2077435 7893521 := bstep (se 2 (by rfl) ⟨2960070, by rfl⟩ : syracuseStep 7893521 = 5920141) B5920141
theorem B5262347 : Blo 2077435 5262347 := bstep (se 1 (by rfl) ⟨3946760, by rfl⟩ : syracuseStep 5262347 = 7893521) B7893521
theorem B3508231 : Blo 2077435 3508231 := bstep (se 1 (by rfl) ⟨2631173, by rfl⟩ : syracuseStep 3508231 = 5262347) B5262347
theorem B4677641 : Blo 2077435 4677641 := bstep (se 2 (by rfl) ⟨1754115, by rfl⟩ : syracuseStep 4677641 = 3508231) B3508231
theorem B3118427 : Blo 2077435 3118427 := bstep (se 1 (by rfl) ⟨2338820, by rfl⟩ : syracuseStep 3118427 = 4677641) B4677641
theorem B2078951 : Blo 2077435 2078951 := bstep (se 1 (by rfl) ⟨1559213, by rfl⟩ : syracuseStep 2078951 = 3118427) B3118427
theorem B2338825 : Blo 2077435 2338825 := bbase (se 2 (by rfl) ⟨877059, by rfl⟩ : syracuseStep 2338825 = 1754119) (by norm_num)
theorem B3118433 : Blo 2077435 3118433 := bstep (se 2 (by rfl) ⟨1169412, by rfl⟩ : syracuseStep 3118433 = 2338825) B2338825
theorem B2078955 : Blo 2077435 2078955 := bstep (se 1 (by rfl) ⟨1559216, by rfl⟩ : syracuseStep 2078955 = 3118433) B3118433
theorem B9612341 : Blo 2077435 9612341 := bbase (se 5 (by rfl) ⟨450578, by rfl⟩ : syracuseStep 9612341 = 901157) (by norm_num)
theorem B6408227 : Blo 2077435 6408227 := bstep (se 1 (by rfl) ⟨4806170, by rfl⟩ : syracuseStep 6408227 = 9612341) B9612341
theorem B4272151 : Blo 2077435 4272151 := bstep (se 1 (by rfl) ⟨3204113, by rfl⟩ : syracuseStep 4272151 = 6408227) B6408227
theorem B5696201 : Blo 2077435 5696201 := bstep (se 2 (by rfl) ⟨2136075, by rfl⟩ : syracuseStep 5696201 = 4272151) B4272151
theorem B15189869 : Blo 2077435 15189869 := bstep (se 3 (by rfl) ⟨2848100, by rfl⟩ : syracuseStep 15189869 = 5696201) B5696201
theorem B40506317 : Blo 2077435 40506317 := bstep (se 3 (by rfl) ⟨7594934, by rfl⟩ : syracuseStep 40506317 = 15189869) B15189869
theorem B27004211 : Blo 2077435 27004211 := bstep (se 1 (by rfl) ⟨20253158, by rfl⟩ : syracuseStep 27004211 = 40506317) B40506317
theorem B18002807 : Blo 2077435 18002807 := bstep (se 1 (by rfl) ⟨13502105, by rfl⟩ : syracuseStep 18002807 = 27004211) B27004211
theorem B12001871 : Blo 2077435 12001871 := bstep (se 1 (by rfl) ⟨9001403, by rfl⟩ : syracuseStep 12001871 = 18002807) B18002807
theorem B8001247 : Blo 2077435 8001247 := bstep (se 1 (by rfl) ⟨6000935, by rfl⟩ : syracuseStep 8001247 = 12001871) B12001871
theorem B10668329 : Blo 2077435 10668329 := bstep (se 2 (by rfl) ⟨4000623, by rfl⟩ : syracuseStep 10668329 = 8001247) B8001247
theorem B7112219 : Blo 2077435 7112219 := bstep (se 1 (by rfl) ⟨5334164, by rfl⟩ : syracuseStep 7112219 = 10668329) B10668329
theorem B18965917 : Blo 2077435 18965917 := bstep (se 3 (by rfl) ⟨3556109, by rfl⟩ : syracuseStep 18965917 = 7112219) B7112219
theorem B25287889 : Blo 2077435 25287889 := bstep (se 2 (by rfl) ⟨9482958, by rfl⟩ : syracuseStep 25287889 = 18965917) B18965917
theorem B33717185 : Blo 2077435 33717185 := bstep (se 2 (by rfl) ⟨12643944, by rfl⟩ : syracuseStep 33717185 = 25287889) B25287889
theorem B22478123 : Blo 2077435 22478123 := bstep (se 1 (by rfl) ⟨16858592, by rfl⟩ : syracuseStep 22478123 = 33717185) B33717185
theorem B14985415 : Blo 2077435 14985415 := bstep (se 1 (by rfl) ⟨11239061, by rfl⟩ : syracuseStep 14985415 = 22478123) B22478123
theorem B19980553 : Blo 2077435 19980553 := bstep (se 2 (by rfl) ⟨7492707, by rfl⟩ : syracuseStep 19980553 = 14985415) B14985415
theorem B26640737 : Blo 2077435 26640737 := bstep (se 2 (by rfl) ⟨9990276, by rfl⟩ : syracuseStep 26640737 = 19980553) B19980553
theorem B17760491 : Blo 2077435 17760491 := bstep (se 1 (by rfl) ⟨13320368, by rfl⟩ : syracuseStep 17760491 = 26640737) B26640737
theorem B11840327 : Blo 2077435 11840327 := bstep (se 1 (by rfl) ⟨8880245, by rfl⟩ : syracuseStep 11840327 = 17760491) B17760491
theorem B7893551 : Blo 2077435 7893551 := bstep (se 1 (by rfl) ⟨5920163, by rfl⟩ : syracuseStep 7893551 = 11840327) B11840327
theorem B5262367 : Blo 2077435 5262367 := bstep (se 1 (by rfl) ⟨3946775, by rfl⟩ : syracuseStep 5262367 = 7893551) B7893551
theorem B7016489 : Blo 2077435 7016489 := bstep (se 2 (by rfl) ⟨2631183, by rfl⟩ : syracuseStep 7016489 = 5262367) B5262367
theorem B4677659 : Blo 2077435 4677659 := bstep (se 1 (by rfl) ⟨3508244, by rfl⟩ : syracuseStep 4677659 = 7016489) B7016489
theorem B3118439 : Blo 2077435 3118439 := bstep (se 1 (by rfl) ⟨2338829, by rfl⟩ : syracuseStep 3118439 = 4677659) B4677659
theorem B2078959 : Blo 2077435 2078959 := bstep (se 1 (by rfl) ⟨1559219, by rfl⟩ : syracuseStep 2078959 = 3118439) B3118439
theorem B3118445 : Blo 2077435 3118445 := bbase (se 3 (by rfl) ⟨584708, by rfl⟩ : syracuseStep 3118445 = 1169417) (by norm_num)
theorem B2078963 : Blo 2077435 2078963 := bstep (se 1 (by rfl) ⟨1559222, by rfl⟩ : syracuseStep 2078963 = 3118445) B3118445
theorem B4677677 : Blo 2077435 4677677 := bbase (se 3 (by rfl) ⟨877064, by rfl⟩ : syracuseStep 4677677 = 1754129) (by norm_num)
theorem B3118451 : Blo 2077435 3118451 := bstep (se 1 (by rfl) ⟨2338838, by rfl⟩ : syracuseStep 3118451 = 4677677) B4677677
theorem B2078967 : Blo 2077435 2078967 := bstep (se 1 (by rfl) ⟨1559225, by rfl⟩ : syracuseStep 2078967 = 3118451) B3118451
theorem B2107337 : Blo 2077435 2107337 := bbase (se 2 (by rfl) ⟨790251, by rfl⟩ : syracuseStep 2107337 = 1580503) (by norm_num)
theorem B5619565 : Blo 2077435 5619565 := bstep (se 3 (by rfl) ⟨1053668, by rfl⟩ : syracuseStep 5619565 = 2107337) B2107337
theorem B7492753 : Blo 2077435 7492753 := bstep (se 2 (by rfl) ⟨2809782, by rfl⟩ : syracuseStep 7492753 = 5619565) B5619565
theorem B9990337 : Blo 2077435 9990337 := bstep (se 2 (by rfl) ⟨3746376, by rfl⟩ : syracuseStep 9990337 = 7492753) B7492753
theorem B13320449 : Blo 2077435 13320449 := bstep (se 2 (by rfl) ⟨4995168, by rfl⟩ : syracuseStep 13320449 = 9990337) B9990337
theorem B8880299 : Blo 2077435 8880299 := bstep (se 1 (by rfl) ⟨6660224, by rfl⟩ : syracuseStep 8880299 = 13320449) B13320449
theorem B5920199 : Blo 2077435 5920199 := bstep (se 1 (by rfl) ⟨4440149, by rfl⟩ : syracuseStep 5920199 = 8880299) B8880299
theorem B3946799 : Blo 2077435 3946799 := bstep (se 1 (by rfl) ⟨2960099, by rfl⟩ : syracuseStep 3946799 = 5920199) B5920199
theorem B2631199 : Blo 2077435 2631199 := bstep (se 1 (by rfl) ⟨1973399, by rfl⟩ : syracuseStep 2631199 = 3946799) B3946799
theorem B3508265 : Blo 2077435 3508265 := bstep (se 2 (by rfl) ⟨1315599, by rfl⟩ : syracuseStep 3508265 = 2631199) B2631199
theorem B2338843 : Blo 2077435 2338843 := bstep (se 1 (by rfl) ⟨1754132, by rfl⟩ : syracuseStep 2338843 = 3508265) B3508265
theorem B3118457 : Blo 2077435 3118457 := bstep (se 2 (by rfl) ⟨1169421, by rfl⟩ : syracuseStep 3118457 = 2338843) B2338843
theorem B2078971 : Blo 2077435 2078971 := bstep (se 1 (by rfl) ⟨1559228, by rfl⟩ : syracuseStep 2078971 = 3118457) B3118457
theorem B4741517 : Blo 2077435 4741517 := bbase (se 3 (by rfl) ⟨889034, by rfl⟩ : syracuseStep 4741517 = 1778069) (by norm_num)
theorem B3161011 : Blo 2077435 3161011 := bstep (se 1 (by rfl) ⟨2370758, by rfl⟩ : syracuseStep 3161011 = 4741517) B4741517
theorem B4214681 : Blo 2077435 4214681 := bstep (se 2 (by rfl) ⟨1580505, by rfl⟩ : syracuseStep 4214681 = 3161011) B3161011
theorem B2809787 : Blo 2077435 2809787 := bstep (se 1 (by rfl) ⟨2107340, by rfl⟩ : syracuseStep 2809787 = 4214681) B4214681
theorem B7492765 : Blo 2077435 7492765 := bstep (se 3 (by rfl) ⟨1404893, by rfl⟩ : syracuseStep 7492765 = 2809787) B2809787
theorem B9990353 : Blo 2077435 9990353 := bstep (se 2 (by rfl) ⟨3746382, by rfl⟩ : syracuseStep 9990353 = 7492765) B7492765
theorem B6660235 : Blo 2077435 6660235 := bstep (se 1 (by rfl) ⟨4995176, by rfl⟩ : syracuseStep 6660235 = 9990353) B9990353
theorem B35521253 : Blo 2077435 35521253 := bstep (se 4 (by rfl) ⟨3330117, by rfl⟩ : syracuseStep 35521253 = 6660235) B6660235
theorem B23680835 : Blo 2077435 23680835 := bstep (se 1 (by rfl) ⟨17760626, by rfl⟩ : syracuseStep 23680835 = 35521253) B35521253
theorem B15787223 : Blo 2077435 15787223 := bstep (se 1 (by rfl) ⟨11840417, by rfl⟩ : syracuseStep 15787223 = 23680835) B23680835
theorem B10524815 : Blo 2077435 10524815 := bstep (se 1 (by rfl) ⟨7893611, by rfl⟩ : syracuseStep 10524815 = 15787223) B15787223
theorem B7016543 : Blo 2077435 7016543 := bstep (se 1 (by rfl) ⟨5262407, by rfl⟩ : syracuseStep 7016543 = 10524815) B10524815
theorem B4677695 : Blo 2077435 4677695 := bstep (se 1 (by rfl) ⟨3508271, by rfl⟩ : syracuseStep 4677695 = 7016543) B7016543
theorem B3118463 : Blo 2077435 3118463 := bstep (se 1 (by rfl) ⟨2338847, by rfl⟩ : syracuseStep 3118463 = 4677695) B4677695
theorem B2078975 : Blo 2077435 2078975 := bstep (se 1 (by rfl) ⟨1559231, by rfl⟩ : syracuseStep 2078975 = 3118463) B3118463
theorem B3118469 : Blo 2077435 3118469 := bbase (se 4 (by rfl) ⟨292356, by rfl⟩ : syracuseStep 3118469 = 584713) (by norm_num)
theorem B2078979 : Blo 2077435 2078979 := bstep (se 1 (by rfl) ⟨1559234, by rfl⟩ : syracuseStep 2078979 = 3118469) B3118469
theorem B3508285 : Blo 2077435 3508285 := bbase (se 3 (by rfl) ⟨657803, by rfl⟩ : syracuseStep 3508285 = 1315607) (by norm_num)
theorem B4677713 : Blo 2077435 4677713 := bstep (se 2 (by rfl) ⟨1754142, by rfl⟩ : syracuseStep 4677713 = 3508285) B3508285
theorem B3118475 : Blo 2077435 3118475 := bstep (se 1 (by rfl) ⟨2338856, by rfl⟩ : syracuseStep 3118475 = 4677713) B4677713
theorem B2078983 : Blo 2077435 2078983 := bstep (se 1 (by rfl) ⟨1559237, by rfl⟩ : syracuseStep 2078983 = 3118475) B3118475
theorem B2338861 : Blo 2077435 2338861 := bbase (se 3 (by rfl) ⟨438536, by rfl⟩ : syracuseStep 2338861 = 877073) (by norm_num)
theorem B3118481 : Blo 2077435 3118481 := bstep (se 2 (by rfl) ⟨1169430, by rfl⟩ : syracuseStep 3118481 = 2338861) B2338861
theorem B2078987 : Blo 2077435 2078987 := bstep (se 1 (by rfl) ⟨1559240, by rfl⟩ : syracuseStep 2078987 = 3118481) B3118481
theorem B7016597 : Blo 2077435 7016597 := bbase (se 6 (by rfl) ⟨164451, by rfl⟩ : syracuseStep 7016597 = 328903) (by norm_num)
theorem B4677731 : Blo 2077435 4677731 := bstep (se 1 (by rfl) ⟨3508298, by rfl⟩ : syracuseStep 4677731 = 7016597) B7016597
theorem B3118487 : Blo 2077435 3118487 := bstep (se 1 (by rfl) ⟨2338865, by rfl⟩ : syracuseStep 3118487 = 4677731) B4677731
theorem B2078991 : Blo 2077435 2078991 := bstep (se 1 (by rfl) ⟨1559243, by rfl⟩ : syracuseStep 2078991 = 3118487) B3118487
theorem B3118493 : Blo 2077435 3118493 := bbase (se 3 (by rfl) ⟨584717, by rfl⟩ : syracuseStep 3118493 = 1169435) (by norm_num)
theorem B2078995 : Blo 2077435 2078995 := bstep (se 1 (by rfl) ⟨1559246, by rfl⟩ : syracuseStep 2078995 = 3118493) B3118493
theorem B4677749 : Blo 2077435 4677749 := bbase (se 5 (by rfl) ⟨219269, by rfl⟩ : syracuseStep 4677749 = 438539) (by norm_num)
theorem B3118499 : Blo 2077435 3118499 := bstep (se 1 (by rfl) ⟨2338874, by rfl⟩ : syracuseStep 3118499 = 4677749) B4677749
theorem B2078999 : Blo 2077435 2078999 := bstep (se 1 (by rfl) ⟨1559249, by rfl⟩ : syracuseStep 2078999 = 3118499) B3118499
theorem B4995245 : Blo 2077435 4995245 := bbase (se 3 (by rfl) ⟨936608, by rfl⟩ : syracuseStep 4995245 = 1873217) (by norm_num)
theorem B3330163 : Blo 2077435 3330163 := bstep (se 1 (by rfl) ⟨2497622, by rfl⟩ : syracuseStep 3330163 = 4995245) B4995245
theorem B17760869 : Blo 2077435 17760869 := bstep (se 4 (by rfl) ⟨1665081, by rfl⟩ : syracuseStep 17760869 = 3330163) B3330163
theorem B11840579 : Blo 2077435 11840579 := bstep (se 1 (by rfl) ⟨8880434, by rfl⟩ : syracuseStep 11840579 = 17760869) B17760869
theorem B7893719 : Blo 2077435 7893719 := bstep (se 1 (by rfl) ⟨5920289, by rfl⟩ : syracuseStep 7893719 = 11840579) B11840579
theorem B5262479 : Blo 2077435 5262479 := bstep (se 1 (by rfl) ⟨3946859, by rfl⟩ : syracuseStep 5262479 = 7893719) B7893719
theorem B3508319 : Blo 2077435 3508319 := bstep (se 1 (by rfl) ⟨2631239, by rfl⟩ : syracuseStep 3508319 = 5262479) B5262479
theorem B2338879 : Blo 2077435 2338879 := bstep (se 1 (by rfl) ⟨1754159, by rfl⟩ : syracuseStep 2338879 = 3508319) B3508319
theorem B3118505 : Blo 2077435 3118505 := bstep (se 2 (by rfl) ⟨1169439, by rfl⟩ : syracuseStep 3118505 = 2338879) B2338879
theorem B2079003 : Blo 2077435 2079003 := bstep (se 1 (by rfl) ⟨1559252, by rfl⟩ : syracuseStep 2079003 = 3118505) B3118505
theorem B7893733 : Blo 2077435 7893733 := bbase (se 4 (by rfl) ⟨740037, by rfl⟩ : syracuseStep 7893733 = 1480075) (by norm_num)
theorem B10524977 : Blo 2077435 10524977 := bstep (se 2 (by rfl) ⟨3946866, by rfl⟩ : syracuseStep 10524977 = 7893733) B7893733
theorem B7016651 : Blo 2077435 7016651 := bstep (se 1 (by rfl) ⟨5262488, by rfl⟩ : syracuseStep 7016651 = 10524977) B10524977
theorem B4677767 : Blo 2077435 4677767 := bstep (se 1 (by rfl) ⟨3508325, by rfl⟩ : syracuseStep 4677767 = 7016651) B7016651
theorem B3118511 : Blo 2077435 3118511 := bstep (se 1 (by rfl) ⟨2338883, by rfl⟩ : syracuseStep 3118511 = 4677767) B4677767
theorem B2079007 : Blo 2077435 2079007 := bstep (se 1 (by rfl) ⟨1559255, by rfl⟩ : syracuseStep 2079007 = 3118511) B3118511
theorem B3118517 : Blo 2077435 3118517 := bbase (se 5 (by rfl) ⟨146180, by rfl⟩ : syracuseStep 3118517 = 292361) (by norm_num)
theorem B2079011 : Blo 2077435 2079011 := bstep (se 1 (by rfl) ⟨1559258, by rfl⟩ : syracuseStep 2079011 = 3118517) B3118517
theorem B5262509 : Blo 2077435 5262509 := bbase (se 3 (by rfl) ⟨986720, by rfl⟩ : syracuseStep 5262509 = 1973441) (by norm_num)
theorem B3508339 : Blo 2077435 3508339 := bstep (se 1 (by rfl) ⟨2631254, by rfl⟩ : syracuseStep 3508339 = 5262509) B5262509
theorem B4677785 : Blo 2077435 4677785 := bstep (se 2 (by rfl) ⟨1754169, by rfl⟩ : syracuseStep 4677785 = 3508339) B3508339
theorem B3118523 : Blo 2077435 3118523 := bstep (se 1 (by rfl) ⟨2338892, by rfl⟩ : syracuseStep 3118523 = 4677785) B4677785
theorem B2079015 : Blo 2077435 2079015 := bstep (se 1 (by rfl) ⟨1559261, by rfl⟩ : syracuseStep 2079015 = 3118523) B3118523
theorem B2338897 : Blo 2077435 2338897 := bbase (se 2 (by rfl) ⟨877086, by rfl⟩ : syracuseStep 2338897 = 1754173) (by norm_num)
theorem B3118529 : Blo 2077435 3118529 := bstep (se 2 (by rfl) ⟨1169448, by rfl⟩ : syracuseStep 3118529 = 2338897) B2338897
theorem B2079019 : Blo 2077435 2079019 := bstep (se 1 (by rfl) ⟨1559264, by rfl⟩ : syracuseStep 2079019 = 3118529) B3118529
theorem B2960173 : Blo 2077435 2960173 := bbase (se 3 (by rfl) ⟨555032, by rfl⟩ : syracuseStep 2960173 = 1110065) (by norm_num)
theorem B3946897 : Blo 2077435 3946897 := bstep (se 2 (by rfl) ⟨1480086, by rfl⟩ : syracuseStep 3946897 = 2960173) B2960173
theorem B5262529 : Blo 2077435 5262529 := bstep (se 2 (by rfl) ⟨1973448, by rfl⟩ : syracuseStep 5262529 = 3946897) B3946897
theorem B7016705 : Blo 2077435 7016705 := bstep (se 2 (by rfl) ⟨2631264, by rfl⟩ : syracuseStep 7016705 = 5262529) B5262529
theorem B4677803 : Blo 2077435 4677803 := bstep (se 1 (by rfl) ⟨3508352, by rfl⟩ : syracuseStep 4677803 = 7016705) B7016705
theorem B3118535 : Blo 2077435 3118535 := bstep (se 1 (by rfl) ⟨2338901, by rfl⟩ : syracuseStep 3118535 = 4677803) B4677803
theorem B2079023 : Blo 2077435 2079023 := bstep (se 1 (by rfl) ⟨1559267, by rfl⟩ : syracuseStep 2079023 = 3118535) B3118535
theorem B3118541 : Blo 2077435 3118541 := bbase (se 3 (by rfl) ⟨584726, by rfl⟩ : syracuseStep 3118541 = 1169453) (by norm_num)
theorem B2079027 : Blo 2077435 2079027 := bstep (se 1 (by rfl) ⟨1559270, by rfl⟩ : syracuseStep 2079027 = 3118541) B3118541
theorem B4677821 : Blo 2077435 4677821 := bbase (se 3 (by rfl) ⟨877091, by rfl⟩ : syracuseStep 4677821 = 1754183) (by norm_num)
theorem B3118547 : Blo 2077435 3118547 := bstep (se 1 (by rfl) ⟨2338910, by rfl⟩ : syracuseStep 3118547 = 4677821) B4677821
theorem B2079031 : Blo 2077435 2079031 := bstep (se 1 (by rfl) ⟨1559273, by rfl⟩ : syracuseStep 2079031 = 3118547) B3118547
theorem B3508373 : Blo 2077435 3508373 := bbase (se 6 (by rfl) ⟨82227, by rfl⟩ : syracuseStep 3508373 = 164455) (by norm_num)
theorem B2338915 : Blo 2077435 2338915 := bstep (se 1 (by rfl) ⟨1754186, by rfl⟩ : syracuseStep 2338915 = 3508373) B3508373
theorem B3118553 : Blo 2077435 3118553 := bstep (se 2 (by rfl) ⟨1169457, by rfl⟩ : syracuseStep 3118553 = 2338915) B2338915
theorem B2079035 : Blo 2077435 2079035 := bstep (se 1 (by rfl) ⟨1559276, by rfl⟩ : syracuseStep 2079035 = 3118553) B3118553
theorem B9990661 : Blo 2077435 9990661 := bbase (se 4 (by rfl) ⟨936624, by rfl⟩ : syracuseStep 9990661 = 1873249) (by norm_num)
theorem B13320881 : Blo 2077435 13320881 := bstep (se 2 (by rfl) ⟨4995330, by rfl⟩ : syracuseStep 13320881 = 9990661) B9990661
theorem B8880587 : Blo 2077435 8880587 := bstep (se 1 (by rfl) ⟨6660440, by rfl⟩ : syracuseStep 8880587 = 13320881) B13320881
theorem B5920391 : Blo 2077435 5920391 := bstep (se 1 (by rfl) ⟨4440293, by rfl⟩ : syracuseStep 5920391 = 8880587) B8880587
theorem B15787709 : Blo 2077435 15787709 := bstep (se 3 (by rfl) ⟨2960195, by rfl⟩ : syracuseStep 15787709 = 5920391) B5920391
theorem B10525139 : Blo 2077435 10525139 := bstep (se 1 (by rfl) ⟨7893854, by rfl⟩ : syracuseStep 10525139 = 15787709) B15787709
theorem B7016759 : Blo 2077435 7016759 := bstep (se 1 (by rfl) ⟨5262569, by rfl⟩ : syracuseStep 7016759 = 10525139) B10525139
theorem B4677839 : Blo 2077435 4677839 := bstep (se 1 (by rfl) ⟨3508379, by rfl⟩ : syracuseStep 4677839 = 7016759) B7016759
theorem B3118559 : Blo 2077435 3118559 := bstep (se 1 (by rfl) ⟨2338919, by rfl⟩ : syracuseStep 3118559 = 4677839) B4677839
theorem B2079039 : Blo 2077435 2079039 := bstep (se 1 (by rfl) ⟨1559279, by rfl⟩ : syracuseStep 2079039 = 3118559) B3118559
theorem B3118565 : Blo 2077435 3118565 := bbase (se 4 (by rfl) ⟨292365, by rfl⟩ : syracuseStep 3118565 = 584731) (by norm_num)
theorem B2079043 : Blo 2077435 2079043 := bstep (se 1 (by rfl) ⟨1559282, by rfl⟩ : syracuseStep 2079043 = 3118565) B3118565
theorem B4500893 : Blo 2077435 4500893 := bbase (se 3 (by rfl) ⟨843917, by rfl⟩ : syracuseStep 4500893 = 1687835) (by norm_num)
theorem B3000595 : Blo 2077435 3000595 := bstep (se 1 (by rfl) ⟨2250446, by rfl⟩ : syracuseStep 3000595 = 4500893) B4500893
theorem B64012693 : Blo 2077435 64012693 := bstep (se 6 (by rfl) ⟨1500297, by rfl⟩ : syracuseStep 64012693 = 3000595) B3000595
theorem B85350257 : Blo 2077435 85350257 := bstep (se 2 (by rfl) ⟨32006346, by rfl⟩ : syracuseStep 85350257 = 64012693) B64012693
theorem B56900171 : Blo 2077435 56900171 := bstep (se 1 (by rfl) ⟨42675128, by rfl⟩ : syracuseStep 56900171 = 85350257) B85350257
theorem B37933447 : Blo 2077435 37933447 := bstep (se 1 (by rfl) ⟨28450085, by rfl⟩ : syracuseStep 37933447 = 56900171) B56900171
theorem B50577929 : Blo 2077435 50577929 := bstep (se 2 (by rfl) ⟨18966723, by rfl⟩ : syracuseStep 50577929 = 37933447) B37933447
theorem B33718619 : Blo 2077435 33718619 := bstep (se 1 (by rfl) ⟨25288964, by rfl⟩ : syracuseStep 33718619 = 50577929) B50577929
theorem B22479079 : Blo 2077435 22479079 := bstep (se 1 (by rfl) ⟨16859309, by rfl⟩ : syracuseStep 22479079 = 33718619) B33718619
theorem B29972105 : Blo 2077435 29972105 := bstep (se 2 (by rfl) ⟨11239539, by rfl⟩ : syracuseStep 29972105 = 22479079) B22479079
theorem B19981403 : Blo 2077435 19981403 := bstep (se 1 (by rfl) ⟨14986052, by rfl⟩ : syracuseStep 19981403 = 29972105) B29972105
theorem B13320935 : Blo 2077435 13320935 := bstep (se 1 (by rfl) ⟨9990701, by rfl⟩ : syracuseStep 13320935 = 19981403) B19981403
theorem B8880623 : Blo 2077435 8880623 := bstep (se 1 (by rfl) ⟨6660467, by rfl⟩ : syracuseStep 8880623 = 13320935) B13320935
theorem B5920415 : Blo 2077435 5920415 := bstep (se 1 (by rfl) ⟨4440311, by rfl⟩ : syracuseStep 5920415 = 8880623) B8880623
theorem B3946943 : Blo 2077435 3946943 := bstep (se 1 (by rfl) ⟨2960207, by rfl⟩ : syracuseStep 3946943 = 5920415) B5920415
theorem B2631295 : Blo 2077435 2631295 := bstep (se 1 (by rfl) ⟨1973471, by rfl⟩ : syracuseStep 2631295 = 3946943) B3946943
theorem B3508393 : Blo 2077435 3508393 := bstep (se 2 (by rfl) ⟨1315647, by rfl⟩ : syracuseStep 3508393 = 2631295) B2631295
theorem B4677857 : Blo 2077435 4677857 := bstep (se 2 (by rfl) ⟨1754196, by rfl⟩ : syracuseStep 4677857 = 3508393) B3508393
theorem B3118571 : Blo 2077435 3118571 := bstep (se 1 (by rfl) ⟨2338928, by rfl⟩ : syracuseStep 3118571 = 4677857) B4677857
theorem B2079047 : Blo 2077435 2079047 := bstep (se 1 (by rfl) ⟨1559285, by rfl⟩ : syracuseStep 2079047 = 3118571) B3118571
theorem B2338933 : Blo 2077435 2338933 := bbase (se 5 (by rfl) ⟨109637, by rfl⟩ : syracuseStep 2338933 = 219275) (by norm_num)
theorem B3118577 : Blo 2077435 3118577 := bstep (se 2 (by rfl) ⟨1169466, by rfl⟩ : syracuseStep 3118577 = 2338933) B2338933
theorem B2079051 : Blo 2077435 2079051 := bstep (se 1 (by rfl) ⟨1559288, by rfl⟩ : syracuseStep 2079051 = 3118577) B3118577
theorem B2631305 : Blo 2077435 2631305 := bbase (se 2 (by rfl) ⟨986739, by rfl⟩ : syracuseStep 2631305 = 1973479) (by norm_num)
theorem B7016813 : Blo 2077435 7016813 := bstep (se 3 (by rfl) ⟨1315652, by rfl⟩ : syracuseStep 7016813 = 2631305) B2631305
theorem B4677875 : Blo 2077435 4677875 := bstep (se 1 (by rfl) ⟨3508406, by rfl⟩ : syracuseStep 4677875 = 7016813) B7016813
theorem B3118583 : Blo 2077435 3118583 := bstep (se 1 (by rfl) ⟨2338937, by rfl⟩ : syracuseStep 3118583 = 4677875) B4677875
theorem B2079055 : Blo 2077435 2079055 := bstep (se 1 (by rfl) ⟨1559291, by rfl⟩ : syracuseStep 2079055 = 3118583) B3118583
theorem B3118589 : Blo 2077435 3118589 := bbase (se 3 (by rfl) ⟨584735, by rfl⟩ : syracuseStep 3118589 = 1169471) (by norm_num)
theorem B2079059 : Blo 2077435 2079059 := bstep (se 1 (by rfl) ⟨1559294, by rfl⟩ : syracuseStep 2079059 = 3118589) B3118589
theorem B4677893 : Blo 2077435 4677893 := bbase (se 4 (by rfl) ⟨438552, by rfl⟩ : syracuseStep 4677893 = 877105) (by norm_num)
theorem B3118595 : Blo 2077435 3118595 := bstep (se 1 (by rfl) ⟨2338946, by rfl⟩ : syracuseStep 3118595 = 4677893) B4677893
theorem B2079063 : Blo 2077435 2079063 := bstep (se 1 (by rfl) ⟨1559297, by rfl⟩ : syracuseStep 2079063 = 3118595) B3118595
theorem B3946981 : Blo 2077435 3946981 := bbase (se 4 (by rfl) ⟨370029, by rfl⟩ : syracuseStep 3946981 = 740059) (by norm_num)
theorem B5262641 : Blo 2077435 5262641 := bstep (se 2 (by rfl) ⟨1973490, by rfl⟩ : syracuseStep 5262641 = 3946981) B3946981
theorem B3508427 : Blo 2077435 3508427 := bstep (se 1 (by rfl) ⟨2631320, by rfl⟩ : syracuseStep 3508427 = 5262641) B5262641
theorem B2338951 : Blo 2077435 2338951 := bstep (se 1 (by rfl) ⟨1754213, by rfl⟩ : syracuseStep 2338951 = 3508427) B3508427
theorem B3118601 : Blo 2077435 3118601 := bstep (se 2 (by rfl) ⟨1169475, by rfl⟩ : syracuseStep 3118601 = 2338951) B2338951
theorem B2079067 : Blo 2077435 2079067 := bstep (se 1 (by rfl) ⟨1559300, by rfl⟩ : syracuseStep 2079067 = 3118601) B3118601
theorem B10525301 : Blo 2077435 10525301 := bbase (se 5 (by rfl) ⟨493373, by rfl⟩ : syracuseStep 10525301 = 986747) (by norm_num)
theorem B7016867 : Blo 2077435 7016867 := bstep (se 1 (by rfl) ⟨5262650, by rfl⟩ : syracuseStep 7016867 = 10525301) B10525301
theorem B4677911 : Blo 2077435 4677911 := bstep (se 1 (by rfl) ⟨3508433, by rfl⟩ : syracuseStep 4677911 = 7016867) B7016867
theorem B3118607 : Blo 2077435 3118607 := bstep (se 1 (by rfl) ⟨2338955, by rfl⟩ : syracuseStep 3118607 = 4677911) B4677911
theorem B2079071 : Blo 2077435 2079071 := bstep (se 1 (by rfl) ⟨1559303, by rfl⟩ : syracuseStep 2079071 = 3118607) B3118607
theorem B3118613 : Blo 2077435 3118613 := bbase (se 6 (by rfl) ⟨73092, by rfl⟩ : syracuseStep 3118613 = 146185) (by norm_num)
theorem B2079075 : Blo 2077435 2079075 := bstep (se 1 (by rfl) ⟨1559306, by rfl⟩ : syracuseStep 2079075 = 3118613) B3118613
theorem B7493141 : Blo 2077435 7493141 := bbase (se 6 (by rfl) ⟨175620, by rfl⟩ : syracuseStep 7493141 = 351241) (by norm_num)
theorem B4995427 : Blo 2077435 4995427 := bstep (se 1 (by rfl) ⟨3746570, by rfl⟩ : syracuseStep 4995427 = 7493141) B7493141
theorem B6660569 : Blo 2077435 6660569 := bstep (se 2 (by rfl) ⟨2497713, by rfl⟩ : syracuseStep 6660569 = 4995427) B4995427
theorem B17761517 : Blo 2077435 17761517 := bstep (se 3 (by rfl) ⟨3330284, by rfl⟩ : syracuseStep 17761517 = 6660569) B6660569
theorem B11841011 : Blo 2077435 11841011 := bstep (se 1 (by rfl) ⟨8880758, by rfl⟩ : syracuseStep 11841011 = 17761517) B17761517
theorem B7894007 : Blo 2077435 7894007 := bstep (se 1 (by rfl) ⟨5920505, by rfl⟩ : syracuseStep 7894007 = 11841011) B11841011
theorem B5262671 : Blo 2077435 5262671 := bstep (se 1 (by rfl) ⟨3947003, by rfl⟩ : syracuseStep 5262671 = 7894007) B7894007
theorem B3508447 : Blo 2077435 3508447 := bstep (se 1 (by rfl) ⟨2631335, by rfl⟩ : syracuseStep 3508447 = 5262671) B5262671
theorem B4677929 : Blo 2077435 4677929 := bstep (se 2 (by rfl) ⟨1754223, by rfl⟩ : syracuseStep 4677929 = 3508447) B3508447
theorem B3118619 : Blo 2077435 3118619 := bstep (se 1 (by rfl) ⟨2338964, by rfl⟩ : syracuseStep 3118619 = 4677929) B4677929
theorem B2079079 : Blo 2077435 2079079 := bstep (se 1 (by rfl) ⟨1559309, by rfl⟩ : syracuseStep 2079079 = 3118619) B3118619
theorem B2338969 : Blo 2077435 2338969 := bbase (se 2 (by rfl) ⟨877113, by rfl⟩ : syracuseStep 2338969 = 1754227) (by norm_num)
theorem B3118625 : Blo 2077435 3118625 := bstep (se 2 (by rfl) ⟨1169484, by rfl⟩ : syracuseStep 3118625 = 2338969) B2338969
theorem B2079083 : Blo 2077435 2079083 := bstep (se 1 (by rfl) ⟨1559312, by rfl⟩ : syracuseStep 2079083 = 3118625) B3118625
theorem B7894037 : Blo 2077435 7894037 := bbase (se 6 (by rfl) ⟨185016, by rfl⟩ : syracuseStep 7894037 = 370033) (by norm_num)
theorem B5262691 : Blo 2077435 5262691 := bstep (se 1 (by rfl) ⟨3947018, by rfl⟩ : syracuseStep 5262691 = 7894037) B7894037
theorem B7016921 : Blo 2077435 7016921 := bstep (se 2 (by rfl) ⟨2631345, by rfl⟩ : syracuseStep 7016921 = 5262691) B5262691
theorem B4677947 : Blo 2077435 4677947 := bstep (se 1 (by rfl) ⟨3508460, by rfl⟩ : syracuseStep 4677947 = 7016921) B7016921
theorem B3118631 : Blo 2077435 3118631 := bstep (se 1 (by rfl) ⟨2338973, by rfl⟩ : syracuseStep 3118631 = 4677947) B4677947
theorem B2079087 : Blo 2077435 2079087 := bstep (se 1 (by rfl) ⟨1559315, by rfl⟩ : syracuseStep 2079087 = 3118631) B3118631
theorem B3118637 : Blo 2077435 3118637 := bbase (se 3 (by rfl) ⟨584744, by rfl⟩ : syracuseStep 3118637 = 1169489) (by norm_num)
theorem B2079091 : Blo 2077435 2079091 := bstep (se 1 (by rfl) ⟨1559318, by rfl⟩ : syracuseStep 2079091 = 3118637) B3118637
theorem B4677965 : Blo 2077435 4677965 := bbase (se 3 (by rfl) ⟨877118, by rfl⟩ : syracuseStep 4677965 = 1754237) (by norm_num)
theorem B3118643 : Blo 2077435 3118643 := bstep (se 1 (by rfl) ⟨2338982, by rfl⟩ : syracuseStep 3118643 = 4677965) B4677965
theorem B2079095 : Blo 2077435 2079095 := bstep (se 1 (by rfl) ⟨1559321, by rfl⟩ : syracuseStep 2079095 = 3118643) B3118643
theorem B2631361 : Blo 2077435 2631361 := bbase (se 2 (by rfl) ⟨986760, by rfl⟩ : syracuseStep 2631361 = 1973521) (by norm_num)
theorem B3508481 : Blo 2077435 3508481 := bstep (se 2 (by rfl) ⟨1315680, by rfl⟩ : syracuseStep 3508481 = 2631361) B2631361
theorem B2338987 : Blo 2077435 2338987 := bstep (se 1 (by rfl) ⟨1754240, by rfl⟩ : syracuseStep 2338987 = 3508481) B3508481
theorem B3118649 : Blo 2077435 3118649 := bstep (se 2 (by rfl) ⟨1169493, by rfl⟩ : syracuseStep 3118649 = 2338987) B2338987
theorem B2079099 : Blo 2077435 2079099 := bstep (se 1 (by rfl) ⟨1559324, by rfl⟩ : syracuseStep 2079099 = 3118649) B3118649
theorem B4995485 : Blo 2077435 4995485 := bbase (se 3 (by rfl) ⟨936653, by rfl⟩ : syracuseStep 4995485 = 1873307) (by norm_num)
theorem B3330323 : Blo 2077435 3330323 := bstep (se 1 (by rfl) ⟨2497742, by rfl⟩ : syracuseStep 3330323 = 4995485) B4995485
theorem B2220215 : Blo 2077435 2220215 := bstep (se 1 (by rfl) ⟨1665161, by rfl⟩ : syracuseStep 2220215 = 3330323) B3330323
theorem B23682293 : Blo 2077435 23682293 := bstep (se 5 (by rfl) ⟨1110107, by rfl⟩ : syracuseStep 23682293 = 2220215) B2220215
theorem B15788195 : Blo 2077435 15788195 := bstep (se 1 (by rfl) ⟨11841146, by rfl⟩ : syracuseStep 15788195 = 23682293) B23682293
theorem B10525463 : Blo 2077435 10525463 := bstep (se 1 (by rfl) ⟨7894097, by rfl⟩ : syracuseStep 10525463 = 15788195) B15788195
theorem B7016975 : Blo 2077435 7016975 := bstep (se 1 (by rfl) ⟨5262731, by rfl⟩ : syracuseStep 7016975 = 10525463) B10525463
theorem B4677983 : Blo 2077435 4677983 := bstep (se 1 (by rfl) ⟨3508487, by rfl⟩ : syracuseStep 4677983 = 7016975) B7016975
theorem B3118655 : Blo 2077435 3118655 := bstep (se 1 (by rfl) ⟨2338991, by rfl⟩ : syracuseStep 3118655 = 4677983) B4677983
theorem B2079103 : Blo 2077435 2079103 := bstep (se 1 (by rfl) ⟨1559327, by rfl⟩ : syracuseStep 2079103 = 3118655) B3118655
theorem B3118661 : Blo 2077435 3118661 := bbase (se 4 (by rfl) ⟨292374, by rfl⟩ : syracuseStep 3118661 = 584749) (by norm_num)
theorem B2079107 : Blo 2077435 2079107 := bstep (se 1 (by rfl) ⟨1559330, by rfl⟩ : syracuseStep 2079107 = 3118661) B3118661
theorem B3508501 : Blo 2077435 3508501 := bbase (se 6 (by rfl) ⟨82230, by rfl⟩ : syracuseStep 3508501 = 164461) (by norm_num)
theorem B4678001 : Blo 2077435 4678001 := bstep (se 2 (by rfl) ⟨1754250, by rfl⟩ : syracuseStep 4678001 = 3508501) B3508501
theorem B3118667 : Blo 2077435 3118667 := bstep (se 1 (by rfl) ⟨2339000, by rfl⟩ : syracuseStep 3118667 = 4678001) B4678001
theorem B2079111 : Blo 2077435 2079111 := bstep (se 1 (by rfl) ⟨1559333, by rfl⟩ : syracuseStep 2079111 = 3118667) B3118667
theorem B2339005 : Blo 2077435 2339005 := bbase (se 3 (by rfl) ⟨438563, by rfl⟩ : syracuseStep 2339005 = 877127) (by norm_num)
theorem B3118673 : Blo 2077435 3118673 := bstep (se 2 (by rfl) ⟨1169502, by rfl⟩ : syracuseStep 3118673 = 2339005) B2339005
theorem B2079115 : Blo 2077435 2079115 := bstep (se 1 (by rfl) ⟨1559336, by rfl⟩ : syracuseStep 2079115 = 3118673) B3118673
theorem B7017029 : Blo 2077435 7017029 := bbase (se 4 (by rfl) ⟨657846, by rfl⟩ : syracuseStep 7017029 = 1315693) (by norm_num)
theorem B4678019 : Blo 2077435 4678019 := bstep (se 1 (by rfl) ⟨3508514, by rfl⟩ : syracuseStep 4678019 = 7017029) B7017029
theorem B3118679 : Blo 2077435 3118679 := bstep (se 1 (by rfl) ⟨2339009, by rfl⟩ : syracuseStep 3118679 = 4678019) B4678019
theorem B2079119 : Blo 2077435 2079119 := bstep (se 1 (by rfl) ⟨1559339, by rfl⟩ : syracuseStep 2079119 = 3118679) B3118679
theorem B3118685 : Blo 2077435 3118685 := bbase (se 3 (by rfl) ⟨584753, by rfl⟩ : syracuseStep 3118685 = 1169507) (by norm_num)
theorem B2079123 : Blo 2077435 2079123 := bstep (se 1 (by rfl) ⟨1559342, by rfl⟩ : syracuseStep 2079123 = 3118685) B3118685
theorem B4678037 : Blo 2077435 4678037 := bbase (se 6 (by rfl) ⟨109641, by rfl⟩ : syracuseStep 4678037 = 219283) (by norm_num)
theorem B3118691 : Blo 2077435 3118691 := bstep (se 1 (by rfl) ⟨2339018, by rfl⟩ : syracuseStep 3118691 = 4678037) B4678037
theorem B2079127 : Blo 2077435 2079127 := bstep (se 1 (by rfl) ⟨1559345, by rfl⟩ : syracuseStep 2079127 = 3118691) B3118691
theorem B9483749 : Blo 2077435 9483749 := bbase (se 4 (by rfl) ⟨889101, by rfl⟩ : syracuseStep 9483749 = 1778203) (by norm_num)
theorem B6322499 : Blo 2077435 6322499 := bstep (se 1 (by rfl) ⟨4741874, by rfl⟩ : syracuseStep 6322499 = 9483749) B9483749
theorem B4214999 : Blo 2077435 4214999 := bstep (se 1 (by rfl) ⟨3161249, by rfl⟩ : syracuseStep 4214999 = 6322499) B6322499
theorem B2809999 : Blo 2077435 2809999 := bstep (se 1 (by rfl) ⟨2107499, by rfl⟩ : syracuseStep 2809999 = 4214999) B4214999
theorem B3746665 : Blo 2077435 3746665 := bstep (se 2 (by rfl) ⟨1404999, by rfl⟩ : syracuseStep 3746665 = 2809999) B2809999
theorem B4995553 : Blo 2077435 4995553 := bstep (se 2 (by rfl) ⟨1873332, by rfl⟩ : syracuseStep 4995553 = 3746665) B3746665
theorem B6660737 : Blo 2077435 6660737 := bstep (se 2 (by rfl) ⟨2497776, by rfl⟩ : syracuseStep 6660737 = 4995553) B4995553
theorem B4440491 : Blo 2077435 4440491 := bstep (se 1 (by rfl) ⟨3330368, by rfl⟩ : syracuseStep 4440491 = 6660737) B6660737
theorem B2960327 : Blo 2077435 2960327 := bstep (se 1 (by rfl) ⟨2220245, by rfl⟩ : syracuseStep 2960327 = 4440491) B4440491
theorem B7894205 : Blo 2077435 7894205 := bstep (se 3 (by rfl) ⟨1480163, by rfl⟩ : syracuseStep 7894205 = 2960327) B2960327
theorem B5262803 : Blo 2077435 5262803 := bstep (se 1 (by rfl) ⟨3947102, by rfl⟩ : syracuseStep 5262803 = 7894205) B7894205
theorem B3508535 : Blo 2077435 3508535 := bstep (se 1 (by rfl) ⟨2631401, by rfl⟩ : syracuseStep 3508535 = 5262803) B5262803
theorem B2339023 : Blo 2077435 2339023 := bstep (se 1 (by rfl) ⟨1754267, by rfl⟩ : syracuseStep 2339023 = 3508535) B3508535
theorem B3118697 : Blo 2077435 3118697 := bstep (se 2 (by rfl) ⟨1169511, by rfl⟩ : syracuseStep 3118697 = 2339023) B2339023
theorem B2079131 : Blo 2077435 2079131 := bstep (se 1 (by rfl) ⟨1559348, by rfl⟩ : syracuseStep 2079131 = 3118697) B3118697
theorem B8880997 : Blo 2077435 8880997 := bbase (se 4 (by rfl) ⟨832593, by rfl⟩ : syracuseStep 8880997 = 1665187) (by norm_num)
theorem B11841329 : Blo 2077435 11841329 := bstep (se 2 (by rfl) ⟨4440498, by rfl⟩ : syracuseStep 11841329 = 8880997) B8880997
theorem B7894219 : Blo 2077435 7894219 := bstep (se 1 (by rfl) ⟨5920664, by rfl⟩ : syracuseStep 7894219 = 11841329) B11841329
theorem B10525625 : Blo 2077435 10525625 := bstep (se 2 (by rfl) ⟨3947109, by rfl⟩ : syracuseStep 10525625 = 7894219) B7894219
theorem B7017083 : Blo 2077435 7017083 := bstep (se 1 (by rfl) ⟨5262812, by rfl⟩ : syracuseStep 7017083 = 10525625) B10525625
theorem B4678055 : Blo 2077435 4678055 := bstep (se 1 (by rfl) ⟨3508541, by rfl⟩ : syracuseStep 4678055 = 7017083) B7017083
theorem B3118703 : Blo 2077435 3118703 := bstep (se 1 (by rfl) ⟨2339027, by rfl⟩ : syracuseStep 3118703 = 4678055) B4678055
theorem B2079135 : Blo 2077435 2079135 := bstep (se 1 (by rfl) ⟨1559351, by rfl⟩ : syracuseStep 2079135 = 3118703) B3118703
theorem B3118709 : Blo 2077435 3118709 := bbase (se 5 (by rfl) ⟨146189, by rfl⟩ : syracuseStep 3118709 = 292379) (by norm_num)
theorem B2079139 : Blo 2077435 2079139 := bstep (se 1 (by rfl) ⟨1559354, by rfl⟩ : syracuseStep 2079139 = 3118709) B3118709
theorem B3947125 : Blo 2077435 3947125 := bbase (se 5 (by rfl) ⟨185021, by rfl⟩ : syracuseStep 3947125 = 370043) (by norm_num)
theorem B5262833 : Blo 2077435 5262833 := bstep (se 2 (by rfl) ⟨1973562, by rfl⟩ : syracuseStep 5262833 = 3947125) B3947125
theorem B3508555 : Blo 2077435 3508555 := bstep (se 1 (by rfl) ⟨2631416, by rfl⟩ : syracuseStep 3508555 = 5262833) B5262833
theorem B4678073 : Blo 2077435 4678073 := bstep (se 2 (by rfl) ⟨1754277, by rfl⟩ : syracuseStep 4678073 = 3508555) B3508555
theorem B3118715 : Blo 2077435 3118715 := bstep (se 1 (by rfl) ⟨2339036, by rfl⟩ : syracuseStep 3118715 = 4678073) B4678073
theorem B2079143 : Blo 2077435 2079143 := bstep (se 1 (by rfl) ⟨1559357, by rfl⟩ : syracuseStep 2079143 = 3118715) B3118715
theorem B2339041 : Blo 2077435 2339041 := bbase (se 2 (by rfl) ⟨877140, by rfl⟩ : syracuseStep 2339041 = 1754281) (by norm_num)
theorem B3118721 : Blo 2077435 3118721 := bstep (se 2 (by rfl) ⟨1169520, by rfl⟩ : syracuseStep 3118721 = 2339041) B2339041
theorem B2079147 : Blo 2077435 2079147 := bstep (se 1 (by rfl) ⟨1559360, by rfl⟩ : syracuseStep 2079147 = 3118721) B3118721
theorem B5262853 : Blo 2077435 5262853 := bbase (se 4 (by rfl) ⟨493392, by rfl⟩ : syracuseStep 5262853 = 986785) (by norm_num)
theorem B7017137 : Blo 2077435 7017137 := bstep (se 2 (by rfl) ⟨2631426, by rfl⟩ : syracuseStep 7017137 = 5262853) B5262853
theorem B4678091 : Blo 2077435 4678091 := bstep (se 1 (by rfl) ⟨3508568, by rfl⟩ : syracuseStep 4678091 = 7017137) B7017137
theorem B3118727 : Blo 2077435 3118727 := bstep (se 1 (by rfl) ⟨2339045, by rfl⟩ : syracuseStep 3118727 = 4678091) B4678091
theorem B2079151 : Blo 2077435 2079151 := bstep (se 1 (by rfl) ⟨1559363, by rfl⟩ : syracuseStep 2079151 = 3118727) B3118727
theorem B3118733 : Blo 2077435 3118733 := bbase (se 3 (by rfl) ⟨584762, by rfl⟩ : syracuseStep 3118733 = 1169525) (by norm_num)
theorem B2079155 : Blo 2077435 2079155 := bstep (se 1 (by rfl) ⟨1559366, by rfl⟩ : syracuseStep 2079155 = 3118733) B3118733
theorem B4678109 : Blo 2077435 4678109 := bbase (se 3 (by rfl) ⟨877145, by rfl⟩ : syracuseStep 4678109 = 1754291) (by norm_num)
theorem B3118739 : Blo 2077435 3118739 := bstep (se 1 (by rfl) ⟨2339054, by rfl⟩ : syracuseStep 3118739 = 4678109) B4678109
theorem B2079159 : Blo 2077435 2079159 := bstep (se 1 (by rfl) ⟨1559369, by rfl⟩ : syracuseStep 2079159 = 3118739) B3118739
theorem B3508589 : Blo 2077435 3508589 := bbase (se 3 (by rfl) ⟨657860, by rfl⟩ : syracuseStep 3508589 = 1315721) (by norm_num)
theorem B2339059 : Blo 2077435 2339059 := bstep (se 1 (by rfl) ⟨1754294, by rfl⟩ : syracuseStep 2339059 = 3508589) B3508589
theorem B3118745 : Blo 2077435 3118745 := bstep (se 2 (by rfl) ⟨1169529, by rfl⟩ : syracuseStep 3118745 = 2339059) B2339059
theorem B2079163 : Blo 2077435 2079163 := bstep (se 1 (by rfl) ⟨1559372, by rfl⟩ : syracuseStep 2079163 = 3118745) B3118745
theorem B2667349 : Blo 2077435 2667349 := bbase (se 9 (by rfl) ⟨7814, by rfl⟩ : syracuseStep 2667349 = 15629) (by norm_num)
theorem B14225861 : Blo 2077435 14225861 := bstep (se 4 (by rfl) ⟨1333674, by rfl⟩ : syracuseStep 14225861 = 2667349) B2667349
theorem B9483907 : Blo 2077435 9483907 := bstep (se 1 (by rfl) ⟨7112930, by rfl⟩ : syracuseStep 9483907 = 14225861) B14225861
theorem B12645209 : Blo 2077435 12645209 := bstep (se 2 (by rfl) ⟨4741953, by rfl⟩ : syracuseStep 12645209 = 9483907) B9483907
theorem B8430139 : Blo 2077435 8430139 := bstep (se 1 (by rfl) ⟨6322604, by rfl⟩ : syracuseStep 8430139 = 12645209) B12645209
theorem B44960741 : Blo 2077435 44960741 := bstep (se 4 (by rfl) ⟨4215069, by rfl⟩ : syracuseStep 44960741 = 8430139) B8430139
theorem B29973827 : Blo 2077435 29973827 := bstep (se 1 (by rfl) ⟨22480370, by rfl⟩ : syracuseStep 29973827 = 44960741) B44960741
theorem B19982551 : Blo 2077435 19982551 := bstep (se 1 (by rfl) ⟨14986913, by rfl⟩ : syracuseStep 19982551 = 29973827) B29973827
theorem B26643401 : Blo 2077435 26643401 := bstep (se 2 (by rfl) ⟨9991275, by rfl⟩ : syracuseStep 26643401 = 19982551) B19982551
theorem B17762267 : Blo 2077435 17762267 := bstep (se 1 (by rfl) ⟨13321700, by rfl⟩ : syracuseStep 17762267 = 26643401) B26643401
theorem B11841511 : Blo 2077435 11841511 := bstep (se 1 (by rfl) ⟨8881133, by rfl⟩ : syracuseStep 11841511 = 17762267) B17762267
theorem B15788681 : Blo 2077435 15788681 := bstep (se 2 (by rfl) ⟨5920755, by rfl⟩ : syracuseStep 15788681 = 11841511) B11841511
theorem B10525787 : Blo 2077435 10525787 := bstep (se 1 (by rfl) ⟨7894340, by rfl⟩ : syracuseStep 10525787 = 15788681) B15788681
theorem B7017191 : Blo 2077435 7017191 := bstep (se 1 (by rfl) ⟨5262893, by rfl⟩ : syracuseStep 7017191 = 10525787) B10525787
theorem B4678127 : Blo 2077435 4678127 := bstep (se 1 (by rfl) ⟨3508595, by rfl⟩ : syracuseStep 4678127 = 7017191) B7017191
theorem B3118751 : Blo 2077435 3118751 := bstep (se 1 (by rfl) ⟨2339063, by rfl⟩ : syracuseStep 3118751 = 4678127) B4678127
theorem B2079167 : Blo 2077435 2079167 := bstep (se 1 (by rfl) ⟨1559375, by rfl⟩ : syracuseStep 2079167 = 3118751) B3118751
theorem B3118757 : Blo 2077435 3118757 := bbase (se 4 (by rfl) ⟨292383, by rfl⟩ : syracuseStep 3118757 = 584767) (by norm_num)
theorem B2079171 : Blo 2077435 2079171 := bstep (se 1 (by rfl) ⟨1559378, by rfl⟩ : syracuseStep 2079171 = 3118757) B3118757
theorem B2631457 : Blo 2077435 2631457 := bbase (se 2 (by rfl) ⟨986796, by rfl⟩ : syracuseStep 2631457 = 1973593) (by norm_num)
theorem B3508609 : Blo 2077435 3508609 := bstep (se 2 (by rfl) ⟨1315728, by rfl⟩ : syracuseStep 3508609 = 2631457) B2631457
theorem B4678145 : Blo 2077435 4678145 := bstep (se 2 (by rfl) ⟨1754304, by rfl⟩ : syracuseStep 4678145 = 3508609) B3508609
theorem B3118763 : Blo 2077435 3118763 := bstep (se 1 (by rfl) ⟨2339072, by rfl⟩ : syracuseStep 3118763 = 4678145) B4678145
theorem B2079175 : Blo 2077435 2079175 := bstep (se 1 (by rfl) ⟨1559381, by rfl⟩ : syracuseStep 2079175 = 3118763) B3118763
theorem B2339077 : Blo 2077435 2339077 := bbase (se 4 (by rfl) ⟨219288, by rfl⟩ : syracuseStep 2339077 = 438577) (by norm_num)
theorem B3118769 : Blo 2077435 3118769 := bstep (se 2 (by rfl) ⟨1169538, by rfl⟩ : syracuseStep 3118769 = 2339077) B2339077
theorem B2079179 : Blo 2077435 2079179 := bstep (se 1 (by rfl) ⟨1559384, by rfl⟩ : syracuseStep 2079179 = 3118769) B3118769
theorem B2220301 : Blo 2077435 2220301 := bbase (se 3 (by rfl) ⟨416306, by rfl⟩ : syracuseStep 2220301 = 832613) (by norm_num)
theorem B2960401 : Blo 2077435 2960401 := bstep (se 2 (by rfl) ⟨1110150, by rfl⟩ : syracuseStep 2960401 = 2220301) B2220301
theorem B3947201 : Blo 2077435 3947201 := bstep (se 2 (by rfl) ⟨1480200, by rfl⟩ : syracuseStep 3947201 = 2960401) B2960401
theorem B2631467 : Blo 2077435 2631467 := bstep (se 1 (by rfl) ⟨1973600, by rfl⟩ : syracuseStep 2631467 = 3947201) B3947201
theorem B7017245 : Blo 2077435 7017245 := bstep (se 3 (by rfl) ⟨1315733, by rfl⟩ : syracuseStep 7017245 = 2631467) B2631467
theorem B4678163 : Blo 2077435 4678163 := bstep (se 1 (by rfl) ⟨3508622, by rfl⟩ : syracuseStep 4678163 = 7017245) B7017245
theorem B3118775 : Blo 2077435 3118775 := bstep (se 1 (by rfl) ⟨2339081, by rfl⟩ : syracuseStep 3118775 = 4678163) B4678163
theorem B2079183 : Blo 2077435 2079183 := bstep (se 1 (by rfl) ⟨1559387, by rfl⟩ : syracuseStep 2079183 = 3118775) B3118775
theorem B3118781 : Blo 2077435 3118781 := bbase (se 3 (by rfl) ⟨584771, by rfl⟩ : syracuseStep 3118781 = 1169543) (by norm_num)
theorem B2079187 : Blo 2077435 2079187 := bstep (se 1 (by rfl) ⟨1559390, by rfl⟩ : syracuseStep 2079187 = 3118781) B3118781
theorem B4678181 : Blo 2077435 4678181 := bbase (se 4 (by rfl) ⟨438579, by rfl⟩ : syracuseStep 4678181 = 877159) (by norm_num)
theorem B3118787 : Blo 2077435 3118787 := bstep (se 1 (by rfl) ⟨2339090, by rfl⟩ : syracuseStep 3118787 = 4678181) B4678181
theorem B2079191 : Blo 2077435 2079191 := bstep (se 1 (by rfl) ⟨1559393, by rfl⟩ : syracuseStep 2079191 = 3118787) B3118787
theorem B5262965 : Blo 2077435 5262965 := bbase (se 5 (by rfl) ⟨246701, by rfl⟩ : syracuseStep 5262965 = 493403) (by norm_num)
theorem B3508643 : Blo 2077435 3508643 := bstep (se 1 (by rfl) ⟨2631482, by rfl⟩ : syracuseStep 3508643 = 5262965) B5262965
theorem B2339095 : Blo 2077435 2339095 := bstep (se 1 (by rfl) ⟨1754321, by rfl⟩ : syracuseStep 2339095 = 3508643) B3508643
theorem B3118793 : Blo 2077435 3118793 := bstep (se 2 (by rfl) ⟨1169547, by rfl⟩ : syracuseStep 3118793 = 2339095) B2339095
theorem B2079195 : Blo 2077435 2079195 := bstep (se 1 (by rfl) ⟨1559396, by rfl⟩ : syracuseStep 2079195 = 3118793) B3118793
theorem B7493573 : Blo 2077435 7493573 := bbase (se 4 (by rfl) ⟨702522, by rfl⟩ : syracuseStep 7493573 = 1405045) (by norm_num)
theorem B19982861 : Blo 2077435 19982861 := bstep (se 3 (by rfl) ⟨3746786, by rfl⟩ : syracuseStep 19982861 = 7493573) B7493573
theorem B13321907 : Blo 2077435 13321907 := bstep (se 1 (by rfl) ⟨9991430, by rfl⟩ : syracuseStep 13321907 = 19982861) B19982861
theorem B8881271 : Blo 2077435 8881271 := bstep (se 1 (by rfl) ⟨6660953, by rfl⟩ : syracuseStep 8881271 = 13321907) B13321907
theorem B5920847 : Blo 2077435 5920847 := bstep (se 1 (by rfl) ⟨4440635, by rfl⟩ : syracuseStep 5920847 = 8881271) B8881271
theorem B3947231 : Blo 2077435 3947231 := bstep (se 1 (by rfl) ⟨2960423, by rfl⟩ : syracuseStep 3947231 = 5920847) B5920847
theorem B10525949 : Blo 2077435 10525949 := bstep (se 3 (by rfl) ⟨1973615, by rfl⟩ : syracuseStep 10525949 = 3947231) B3947231
theorem B7017299 : Blo 2077435 7017299 := bstep (se 1 (by rfl) ⟨5262974, by rfl⟩ : syracuseStep 7017299 = 10525949) B10525949
theorem B4678199 : Blo 2077435 4678199 := bstep (se 1 (by rfl) ⟨3508649, by rfl⟩ : syracuseStep 4678199 = 7017299) B7017299
theorem B3118799 : Blo 2077435 3118799 := bstep (se 1 (by rfl) ⟨2339099, by rfl⟩ : syracuseStep 3118799 = 4678199) B4678199
theorem B2079199 : Blo 2077435 2079199 := bstep (se 1 (by rfl) ⟨1559399, by rfl⟩ : syracuseStep 2079199 = 3118799) B3118799
theorem B3118805 : Blo 2077435 3118805 := bbase (se 7 (by rfl) ⟨36548, by rfl⟩ : syracuseStep 3118805 = 73097) (by norm_num)
theorem B2079203 : Blo 2077435 2079203 := bstep (se 1 (by rfl) ⟨1559402, by rfl⟩ : syracuseStep 2079203 = 3118805) B3118805
theorem B4440653 : Blo 2077435 4440653 := bbase (se 3 (by rfl) ⟨832622, by rfl⟩ : syracuseStep 4440653 = 1665245) (by norm_num)
theorem B2960435 : Blo 2077435 2960435 := bstep (se 1 (by rfl) ⟨2220326, by rfl⟩ : syracuseStep 2960435 = 4440653) B4440653
theorem B7894493 : Blo 2077435 7894493 := bstep (se 3 (by rfl) ⟨1480217, by rfl⟩ : syracuseStep 7894493 = 2960435) B2960435
theorem B5262995 : Blo 2077435 5262995 := bstep (se 1 (by rfl) ⟨3947246, by rfl⟩ : syracuseStep 5262995 = 7894493) B7894493
theorem B3508663 : Blo 2077435 3508663 := bstep (se 1 (by rfl) ⟨2631497, by rfl⟩ : syracuseStep 3508663 = 5262995) B5262995
theorem B4678217 : Blo 2077435 4678217 := bstep (se 2 (by rfl) ⟨1754331, by rfl⟩ : syracuseStep 4678217 = 3508663) B3508663
theorem B3118811 : Blo 2077435 3118811 := bstep (se 1 (by rfl) ⟨2339108, by rfl⟩ : syracuseStep 3118811 = 4678217) B4678217
theorem B2079207 : Blo 2077435 2079207 := bstep (se 1 (by rfl) ⟨1559405, by rfl⟩ : syracuseStep 2079207 = 3118811) B3118811
theorem B2339113 : Blo 2077435 2339113 := bbase (se 2 (by rfl) ⟨877167, by rfl⟩ : syracuseStep 2339113 = 1754335) (by norm_num)
theorem B3118817 : Blo 2077435 3118817 := bstep (se 2 (by rfl) ⟨1169556, by rfl⟩ : syracuseStep 3118817 = 2339113) B2339113
theorem B2079211 : Blo 2077435 2079211 := bstep (se 1 (by rfl) ⟨1559408, by rfl⟩ : syracuseStep 2079211 = 3118817) B3118817
theorem B4562669 : Blo 2077435 4562669 := bbase (se 3 (by rfl) ⟨855500, by rfl⟩ : syracuseStep 4562669 = 1711001) (by norm_num)
theorem B12167117 : Blo 2077435 12167117 := bstep (se 3 (by rfl) ⟨2281334, by rfl⟩ : syracuseStep 12167117 = 4562669) B4562669
theorem B8111411 : Blo 2077435 8111411 := bstep (se 1 (by rfl) ⟨6083558, by rfl⟩ : syracuseStep 8111411 = 12167117) B12167117
theorem B5407607 : Blo 2077435 5407607 := bstep (se 1 (by rfl) ⟨4055705, by rfl⟩ : syracuseStep 5407607 = 8111411) B8111411
theorem B14420285 : Blo 2077435 14420285 := bstep (se 3 (by rfl) ⟨2703803, by rfl⟩ : syracuseStep 14420285 = 5407607) B5407607
theorem B9613523 : Blo 2077435 9613523 := bstep (se 1 (by rfl) ⟨7210142, by rfl⟩ : syracuseStep 9613523 = 14420285) B14420285
theorem B25636061 : Blo 2077435 25636061 := bstep (se 3 (by rfl) ⟨4806761, by rfl⟩ : syracuseStep 25636061 = 9613523) B9613523
theorem B17090707 : Blo 2077435 17090707 := bstep (se 1 (by rfl) ⟨12818030, by rfl⟩ : syracuseStep 17090707 = 25636061) B25636061
theorem B22787609 : Blo 2077435 22787609 := bstep (se 2 (by rfl) ⟨8545353, by rfl⟩ : syracuseStep 22787609 = 17090707) B17090707
theorem B60766957 : Blo 2077435 60766957 := bstep (se 3 (by rfl) ⟨11393804, by rfl⟩ : syracuseStep 60766957 = 22787609) B22787609
theorem B81022609 : Blo 2077435 81022609 := bstep (se 2 (by rfl) ⟨30383478, by rfl⟩ : syracuseStep 81022609 = 60766957) B60766957
theorem B108030145 : Blo 2077435 108030145 := bstep (se 2 (by rfl) ⟨40511304, by rfl⟩ : syracuseStep 108030145 = 81022609) B81022609
theorem B144040193 : Blo 2077435 144040193 := bstep (se 2 (by rfl) ⟨54015072, by rfl⟩ : syracuseStep 144040193 = 108030145) B108030145
theorem B96026795 : Blo 2077435 96026795 := bstep (se 1 (by rfl) ⟨72020096, by rfl⟩ : syracuseStep 96026795 = 144040193) B144040193
theorem B64017863 : Blo 2077435 64017863 := bstep (se 1 (by rfl) ⟨48013397, by rfl⟩ : syracuseStep 64017863 = 96026795) B96026795
theorem B42678575 : Blo 2077435 42678575 := bstep (se 1 (by rfl) ⟨32008931, by rfl⟩ : syracuseStep 42678575 = 64017863) B64017863
theorem B28452383 : Blo 2077435 28452383 := bstep (se 1 (by rfl) ⟨21339287, by rfl⟩ : syracuseStep 28452383 = 42678575) B42678575
theorem B18968255 : Blo 2077435 18968255 := bstep (se 1 (by rfl) ⟨14226191, by rfl⟩ : syracuseStep 18968255 = 28452383) B28452383
theorem B12645503 : Blo 2077435 12645503 := bstep (se 1 (by rfl) ⟨9484127, by rfl⟩ : syracuseStep 12645503 = 18968255) B18968255
theorem B8430335 : Blo 2077435 8430335 := bstep (se 1 (by rfl) ⟨6322751, by rfl⟩ : syracuseStep 8430335 = 12645503) B12645503
theorem B5620223 : Blo 2077435 5620223 := bstep (se 1 (by rfl) ⟨4215167, by rfl⟩ : syracuseStep 5620223 = 8430335) B8430335
theorem B14987261 : Blo 2077435 14987261 := bstep (se 3 (by rfl) ⟨2810111, by rfl⟩ : syracuseStep 14987261 = 5620223) B5620223
theorem B9991507 : Blo 2077435 9991507 := bstep (se 1 (by rfl) ⟨7493630, by rfl⟩ : syracuseStep 9991507 = 14987261) B14987261
theorem B13322009 : Blo 2077435 13322009 := bstep (se 2 (by rfl) ⟨4995753, by rfl⟩ : syracuseStep 13322009 = 9991507) B9991507
theorem B8881339 : Blo 2077435 8881339 := bstep (se 1 (by rfl) ⟨6661004, by rfl⟩ : syracuseStep 8881339 = 13322009) B13322009
theorem B11841785 : Blo 2077435 11841785 := bstep (se 2 (by rfl) ⟨4440669, by rfl⟩ : syracuseStep 11841785 = 8881339) B8881339
theorem B7894523 : Blo 2077435 7894523 := bstep (se 1 (by rfl) ⟨5920892, by rfl⟩ : syracuseStep 7894523 = 11841785) B11841785
theorem B5263015 : Blo 2077435 5263015 := bstep (se 1 (by rfl) ⟨3947261, by rfl⟩ : syracuseStep 5263015 = 7894523) B7894523
theorem B7017353 : Blo 2077435 7017353 := bstep (se 2 (by rfl) ⟨2631507, by rfl⟩ : syracuseStep 7017353 = 5263015) B5263015
theorem B4678235 : Blo 2077435 4678235 := bstep (se 1 (by rfl) ⟨3508676, by rfl⟩ : syracuseStep 4678235 = 7017353) B7017353
theorem B3118823 : Blo 2077435 3118823 := bstep (se 1 (by rfl) ⟨2339117, by rfl⟩ : syracuseStep 3118823 = 4678235) B4678235
theorem B2079215 : Blo 2077435 2079215 := bstep (se 1 (by rfl) ⟨1559411, by rfl⟩ : syracuseStep 2079215 = 3118823) B3118823
theorem B3118829 : Blo 2077435 3118829 := bbase (se 3 (by rfl) ⟨584780, by rfl⟩ : syracuseStep 3118829 = 1169561) (by norm_num)
theorem B2079219 : Blo 2077435 2079219 := bstep (se 1 (by rfl) ⟨1559414, by rfl⟩ : syracuseStep 2079219 = 3118829) B3118829
theorem B4678253 : Blo 2077435 4678253 := bbase (se 3 (by rfl) ⟨877172, by rfl⟩ : syracuseStep 4678253 = 1754345) (by norm_num)
theorem B3118835 : Blo 2077435 3118835 := bstep (se 1 (by rfl) ⟨2339126, by rfl⟩ : syracuseStep 3118835 = 4678253) B4678253
theorem B2079223 : Blo 2077435 2079223 := bstep (se 1 (by rfl) ⟨1559417, by rfl⟩ : syracuseStep 2079223 = 3118835) B3118835
theorem B3947285 : Blo 2077435 3947285 := bbase (se 6 (by rfl) ⟨92514, by rfl⟩ : syracuseStep 3947285 = 185029) (by norm_num)
theorem B2631523 : Blo 2077435 2631523 := bstep (se 1 (by rfl) ⟨1973642, by rfl⟩ : syracuseStep 2631523 = 3947285) B3947285
theorem B3508697 : Blo 2077435 3508697 := bstep (se 2 (by rfl) ⟨1315761, by rfl⟩ : syracuseStep 3508697 = 2631523) B2631523
theorem B2339131 : Blo 2077435 2339131 := bstep (se 1 (by rfl) ⟨1754348, by rfl⟩ : syracuseStep 2339131 = 3508697) B3508697
theorem B3118841 : Blo 2077435 3118841 := bstep (se 2 (by rfl) ⟨1169565, by rfl⟩ : syracuseStep 3118841 = 2339131) B2339131
theorem B2079227 : Blo 2077435 2079227 := bstep (se 1 (by rfl) ⟨1559420, by rfl⟩ : syracuseStep 2079227 = 3118841) B3118841
theorem B3797965 : Blo 2077435 3797965 := bbase (se 3 (by rfl) ⟨712118, by rfl⟩ : syracuseStep 3797965 = 1424237) (by norm_num)
theorem B5063953 : Blo 2077435 5063953 := bstep (se 2 (by rfl) ⟨1898982, by rfl⟩ : syracuseStep 5063953 = 3797965) B3797965
theorem B6751937 : Blo 2077435 6751937 := bstep (se 2 (by rfl) ⟨2531976, by rfl⟩ : syracuseStep 6751937 = 5063953) B5063953
theorem B4501291 : Blo 2077435 4501291 := bstep (se 1 (by rfl) ⟨3375968, by rfl⟩ : syracuseStep 4501291 = 6751937) B6751937
theorem B6001721 : Blo 2077435 6001721 := bstep (se 2 (by rfl) ⟨2250645, by rfl⟩ : syracuseStep 6001721 = 4501291) B4501291
theorem B4001147 : Blo 2077435 4001147 := bstep (se 1 (by rfl) ⟨3000860, by rfl⟩ : syracuseStep 4001147 = 6001721) B6001721
theorem B2667431 : Blo 2077435 2667431 := bstep (se 1 (by rfl) ⟨2000573, by rfl⟩ : syracuseStep 2667431 = 4001147) B4001147
theorem B7113149 : Blo 2077435 7113149 := bstep (se 3 (by rfl) ⟨1333715, by rfl⟩ : syracuseStep 7113149 = 2667431) B2667431
theorem B4742099 : Blo 2077435 4742099 := bstep (se 1 (by rfl) ⟨3556574, by rfl⟩ : syracuseStep 4742099 = 7113149) B7113149
theorem B50582389 : Blo 2077435 50582389 := bstep (se 5 (by rfl) ⟨2371049, by rfl⟩ : syracuseStep 50582389 = 4742099) B4742099
theorem B67443185 : Blo 2077435 67443185 := bstep (se 2 (by rfl) ⟨25291194, by rfl⟩ : syracuseStep 67443185 = 50582389) B50582389
theorem B44962123 : Blo 2077435 44962123 := bstep (se 1 (by rfl) ⟨33721592, by rfl⟩ : syracuseStep 44962123 = 67443185) B67443185
theorem B59949497 : Blo 2077435 59949497 := bstep (se 2 (by rfl) ⟨22481061, by rfl⟩ : syracuseStep 59949497 = 44962123) B44962123
theorem B39966331 : Blo 2077435 39966331 := bstep (se 1 (by rfl) ⟨29974748, by rfl⟩ : syracuseStep 39966331 = 59949497) B59949497
theorem B53288441 : Blo 2077435 53288441 := bstep (se 2 (by rfl) ⟨19983165, by rfl⟩ : syracuseStep 53288441 = 39966331) B39966331
theorem B35525627 : Blo 2077435 35525627 := bstep (se 1 (by rfl) ⟨26644220, by rfl⟩ : syracuseStep 35525627 = 53288441) B53288441
theorem B23683751 : Blo 2077435 23683751 := bstep (se 1 (by rfl) ⟨17762813, by rfl⟩ : syracuseStep 23683751 = 35525627) B35525627
theorem B15789167 : Blo 2077435 15789167 := bstep (se 1 (by rfl) ⟨11841875, by rfl⟩ : syracuseStep 15789167 = 23683751) B23683751
theorem B10526111 : Blo 2077435 10526111 := bstep (se 1 (by rfl) ⟨7894583, by rfl⟩ : syracuseStep 10526111 = 15789167) B15789167
theorem B7017407 : Blo 2077435 7017407 := bstep (se 1 (by rfl) ⟨5263055, by rfl⟩ : syracuseStep 7017407 = 10526111) B10526111
theorem B4678271 : Blo 2077435 4678271 := bstep (se 1 (by rfl) ⟨3508703, by rfl⟩ : syracuseStep 4678271 = 7017407) B7017407
theorem B3118847 : Blo 2077435 3118847 := bstep (se 1 (by rfl) ⟨2339135, by rfl⟩ : syracuseStep 3118847 = 4678271) B4678271
theorem B2079231 : Blo 2077435 2079231 := bstep (se 1 (by rfl) ⟨1559423, by rfl⟩ : syracuseStep 2079231 = 3118847) B3118847
theorem B3118853 : Blo 2077435 3118853 := bbase (se 4 (by rfl) ⟨292392, by rfl⟩ : syracuseStep 3118853 = 584785) (by norm_num)
theorem B2079235 : Blo 2077435 2079235 := bstep (se 1 (by rfl) ⟨1559426, by rfl⟩ : syracuseStep 2079235 = 3118853) B3118853
theorem B3508717 : Blo 2077435 3508717 := bbase (se 3 (by rfl) ⟨657884, by rfl⟩ : syracuseStep 3508717 = 1315769) (by norm_num)
theorem B4678289 : Blo 2077435 4678289 := bstep (se 2 (by rfl) ⟨1754358, by rfl⟩ : syracuseStep 4678289 = 3508717) B3508717
theorem B3118859 : Blo 2077435 3118859 := bstep (se 1 (by rfl) ⟨2339144, by rfl⟩ : syracuseStep 3118859 = 4678289) B4678289
theorem B2079239 : Blo 2077435 2079239 := bstep (se 1 (by rfl) ⟨1559429, by rfl⟩ : syracuseStep 2079239 = 3118859) B3118859
theorem B2339149 : Blo 2077435 2339149 := bbase (se 3 (by rfl) ⟨438590, by rfl⟩ : syracuseStep 2339149 = 877181) (by norm_num)
theorem B3118865 : Blo 2077435 3118865 := bstep (se 2 (by rfl) ⟨1169574, by rfl⟩ : syracuseStep 3118865 = 2339149) B2339149
theorem B2079243 : Blo 2077435 2079243 := bstep (se 1 (by rfl) ⟨1559432, by rfl⟩ : syracuseStep 2079243 = 3118865) B3118865
theorem B7017461 : Blo 2077435 7017461 := bbase (se 5 (by rfl) ⟨328943, by rfl⟩ : syracuseStep 7017461 = 657887) (by norm_num)
theorem B4678307 : Blo 2077435 4678307 := bstep (se 1 (by rfl) ⟨3508730, by rfl⟩ : syracuseStep 4678307 = 7017461) B7017461
theorem B3118871 : Blo 2077435 3118871 := bstep (se 1 (by rfl) ⟨2339153, by rfl⟩ : syracuseStep 3118871 = 4678307) B4678307
theorem B2079247 : Blo 2077435 2079247 := bstep (se 1 (by rfl) ⟨1559435, by rfl⟩ : syracuseStep 2079247 = 3118871) B3118871
theorem B3118877 : Blo 2077435 3118877 := bbase (se 3 (by rfl) ⟨584789, by rfl⟩ : syracuseStep 3118877 = 1169579) (by norm_num)
theorem B2079251 : Blo 2077435 2079251 := bstep (se 1 (by rfl) ⟨1559438, by rfl⟩ : syracuseStep 2079251 = 3118877) B3118877
theorem B4678325 : Blo 2077435 4678325 := bbase (se 5 (by rfl) ⟨219296, by rfl⟩ : syracuseStep 4678325 = 438593) (by norm_num)
theorem B3118883 : Blo 2077435 3118883 := bstep (se 1 (by rfl) ⟨2339162, by rfl⟩ : syracuseStep 3118883 = 4678325) B4678325
theorem B2079255 : Blo 2077435 2079255 := bstep (se 1 (by rfl) ⟨1559441, by rfl⟩ : syracuseStep 2079255 = 3118883) B3118883
theorem B11842037 : Blo 2077435 11842037 := bbase (se 5 (by rfl) ⟨555095, by rfl⟩ : syracuseStep 11842037 = 1110191) (by norm_num)
theorem B7894691 : Blo 2077435 7894691 := bstep (se 1 (by rfl) ⟨5921018, by rfl⟩ : syracuseStep 7894691 = 11842037) B11842037
theorem B5263127 : Blo 2077435 5263127 := bstep (se 1 (by rfl) ⟨3947345, by rfl⟩ : syracuseStep 5263127 = 7894691) B7894691
theorem B3508751 : Blo 2077435 3508751 := bstep (se 1 (by rfl) ⟨2631563, by rfl⟩ : syracuseStep 3508751 = 5263127) B5263127
theorem B2339167 : Blo 2077435 2339167 := bstep (se 1 (by rfl) ⟨1754375, by rfl⟩ : syracuseStep 2339167 = 3508751) B3508751
theorem B3118889 : Blo 2077435 3118889 := bstep (se 2 (by rfl) ⟨1169583, by rfl⟩ : syracuseStep 3118889 = 2339167) B2339167
theorem B2079259 : Blo 2077435 2079259 := bstep (se 1 (by rfl) ⟨1559444, by rfl⟩ : syracuseStep 2079259 = 3118889) B3118889
theorem B5921029 : Blo 2077435 5921029 := bbase (se 4 (by rfl) ⟨555096, by rfl⟩ : syracuseStep 5921029 = 1110193) (by norm_num)
theorem B7894705 : Blo 2077435 7894705 := bstep (se 2 (by rfl) ⟨2960514, by rfl⟩ : syracuseStep 7894705 = 5921029) B5921029
theorem B10526273 : Blo 2077435 10526273 := bstep (se 2 (by rfl) ⟨3947352, by rfl⟩ : syracuseStep 10526273 = 7894705) B7894705
theorem B7017515 : Blo 2077435 7017515 := bstep (se 1 (by rfl) ⟨5263136, by rfl⟩ : syracuseStep 7017515 = 10526273) B10526273
theorem B4678343 : Blo 2077435 4678343 := bstep (se 1 (by rfl) ⟨3508757, by rfl⟩ : syracuseStep 4678343 = 7017515) B7017515
theorem B3118895 : Blo 2077435 3118895 := bstep (se 1 (by rfl) ⟨2339171, by rfl⟩ : syracuseStep 3118895 = 4678343) B4678343
theorem B2079263 : Blo 2077435 2079263 := bstep (se 1 (by rfl) ⟨1559447, by rfl⟩ : syracuseStep 2079263 = 3118895) B3118895
theorem B3118901 : Blo 2077435 3118901 := bbase (se 5 (by rfl) ⟨146198, by rfl⟩ : syracuseStep 3118901 = 292397) (by norm_num)
theorem B2079267 : Blo 2077435 2079267 := bstep (se 1 (by rfl) ⟨1559450, by rfl⟩ : syracuseStep 2079267 = 3118901) B3118901
theorem B5263157 : Blo 2077435 5263157 := bbase (se 5 (by rfl) ⟨246710, by rfl⟩ : syracuseStep 5263157 = 493421) (by norm_num)
theorem B3508771 : Blo 2077435 3508771 := bstep (se 1 (by rfl) ⟨2631578, by rfl⟩ : syracuseStep 3508771 = 5263157) B5263157
theorem B4678361 : Blo 2077435 4678361 := bstep (se 2 (by rfl) ⟨1754385, by rfl⟩ : syracuseStep 4678361 = 3508771) B3508771
theorem B3118907 : Blo 2077435 3118907 := bstep (se 1 (by rfl) ⟨2339180, by rfl⟩ : syracuseStep 3118907 = 4678361) B4678361
theorem B2079271 : Blo 2077435 2079271 := bstep (se 1 (by rfl) ⟨1559453, by rfl⟩ : syracuseStep 2079271 = 3118907) B3118907
theorem B2339185 : Blo 2077435 2339185 := bbase (se 2 (by rfl) ⟨877194, by rfl⟩ : syracuseStep 2339185 = 1754389) (by norm_num)
theorem B3118913 : Blo 2077435 3118913 := bstep (se 2 (by rfl) ⟨1169592, by rfl⟩ : syracuseStep 3118913 = 2339185) B2339185
theorem B2079275 : Blo 2077435 2079275 := bstep (se 1 (by rfl) ⟨1559456, by rfl⟩ : syracuseStep 2079275 = 3118913) B3118913
theorem B3330605 : Blo 2077435 3330605 := bbase (se 3 (by rfl) ⟨624488, by rfl⟩ : syracuseStep 3330605 = 1248977) (by norm_num)
theorem B8881613 : Blo 2077435 8881613 := bstep (se 3 (by rfl) ⟨1665302, by rfl⟩ : syracuseStep 8881613 = 3330605) B3330605
theorem B5921075 : Blo 2077435 5921075 := bstep (se 1 (by rfl) ⟨4440806, by rfl⟩ : syracuseStep 5921075 = 8881613) B8881613
theorem B3947383 : Blo 2077435 3947383 := bstep (se 1 (by rfl) ⟨2960537, by rfl⟩ : syracuseStep 3947383 = 5921075) B5921075
theorem B5263177 : Blo 2077435 5263177 := bstep (se 2 (by rfl) ⟨1973691, by rfl⟩ : syracuseStep 5263177 = 3947383) B3947383
theorem B7017569 : Blo 2077435 7017569 := bstep (se 2 (by rfl) ⟨2631588, by rfl⟩ : syracuseStep 7017569 = 5263177) B5263177
theorem B4678379 : Blo 2077435 4678379 := bstep (se 1 (by rfl) ⟨3508784, by rfl⟩ : syracuseStep 4678379 = 7017569) B7017569
theorem B3118919 : Blo 2077435 3118919 := bstep (se 1 (by rfl) ⟨2339189, by rfl⟩ : syracuseStep 3118919 = 4678379) B4678379
theorem B2079279 : Blo 2077435 2079279 := bstep (se 1 (by rfl) ⟨1559459, by rfl⟩ : syracuseStep 2079279 = 3118919) B3118919
theorem B3118925 : Blo 2077435 3118925 := bbase (se 3 (by rfl) ⟨584798, by rfl⟩ : syracuseStep 3118925 = 1169597) (by norm_num)
theorem B2079283 : Blo 2077435 2079283 := bstep (se 1 (by rfl) ⟨1559462, by rfl⟩ : syracuseStep 2079283 = 3118925) B3118925
theorem B4678397 : Blo 2077435 4678397 := bbase (se 3 (by rfl) ⟨877199, by rfl⟩ : syracuseStep 4678397 = 1754399) (by norm_num)
theorem B3118931 : Blo 2077435 3118931 := bstep (se 1 (by rfl) ⟨2339198, by rfl⟩ : syracuseStep 3118931 = 4678397) B4678397
theorem B2079287 : Blo 2077435 2079287 := bstep (se 1 (by rfl) ⟨1559465, by rfl⟩ : syracuseStep 2079287 = 3118931) B3118931
theorem B3508805 : Blo 2077435 3508805 := bbase (se 4 (by rfl) ⟨328950, by rfl⟩ : syracuseStep 3508805 = 657901) (by norm_num)
theorem B2339203 : Blo 2077435 2339203 := bstep (se 1 (by rfl) ⟨1754402, by rfl⟩ : syracuseStep 2339203 = 3508805) B3508805
theorem B3118937 : Blo 2077435 3118937 := bstep (se 2 (by rfl) ⟨1169601, by rfl⟩ : syracuseStep 3118937 = 2339203) B2339203
theorem B2079291 : Blo 2077435 2079291 := bstep (se 1 (by rfl) ⟨1559468, by rfl⟩ : syracuseStep 2079291 = 3118937) B3118937
theorem B15789653 : Blo 2077435 15789653 := bbase (se 8 (by rfl) ⟨92517, by rfl⟩ : syracuseStep 15789653 = 185035) (by norm_num)
theorem B10526435 : Blo 2077435 10526435 := bstep (se 1 (by rfl) ⟨7894826, by rfl⟩ : syracuseStep 10526435 = 15789653) B15789653
theorem B7017623 : Blo 2077435 7017623 := bstep (se 1 (by rfl) ⟨5263217, by rfl⟩ : syracuseStep 7017623 = 10526435) B10526435
theorem B4678415 : Blo 2077435 4678415 := bstep (se 1 (by rfl) ⟨3508811, by rfl⟩ : syracuseStep 4678415 = 7017623) B7017623
theorem B3118943 : Blo 2077435 3118943 := bstep (se 1 (by rfl) ⟨2339207, by rfl⟩ : syracuseStep 3118943 = 4678415) B4678415
theorem B2079295 : Blo 2077435 2079295 := bstep (se 1 (by rfl) ⟨1559471, by rfl⟩ : syracuseStep 2079295 = 3118943) B3118943
theorem B3118949 : Blo 2077435 3118949 := bbase (se 4 (by rfl) ⟨292401, by rfl⟩ : syracuseStep 3118949 = 584803) (by norm_num)
theorem B2079299 : Blo 2077435 2079299 := bstep (se 1 (by rfl) ⟨1559474, by rfl⟩ : syracuseStep 2079299 = 3118949) B3118949
theorem B3947429 : Blo 2077435 3947429 := bbase (se 4 (by rfl) ⟨370071, by rfl⟩ : syracuseStep 3947429 = 740143) (by norm_num)
theorem B2631619 : Blo 2077435 2631619 := bstep (se 1 (by rfl) ⟨1973714, by rfl⟩ : syracuseStep 2631619 = 3947429) B3947429
theorem B3508825 : Blo 2077435 3508825 := bstep (se 2 (by rfl) ⟨1315809, by rfl⟩ : syracuseStep 3508825 = 2631619) B2631619
theorem B4678433 : Blo 2077435 4678433 := bstep (se 2 (by rfl) ⟨1754412, by rfl⟩ : syracuseStep 4678433 = 3508825) B3508825
theorem B3118955 : Blo 2077435 3118955 := bstep (se 1 (by rfl) ⟨2339216, by rfl⟩ : syracuseStep 3118955 = 4678433) B4678433
theorem B2079303 : Blo 2077435 2079303 := bstep (se 1 (by rfl) ⟨1559477, by rfl⟩ : syracuseStep 2079303 = 3118955) B3118955
theorem B2339221 : Blo 2077435 2339221 := bbase (se 6 (by rfl) ⟨54825, by rfl⟩ : syracuseStep 2339221 = 109651) (by norm_num)
theorem B3118961 : Blo 2077435 3118961 := bstep (se 2 (by rfl) ⟨1169610, by rfl⟩ : syracuseStep 3118961 = 2339221) B2339221
theorem B2079307 : Blo 2077435 2079307 := bstep (se 1 (by rfl) ⟨1559480, by rfl⟩ : syracuseStep 2079307 = 3118961) B3118961
theorem B2631629 : Blo 2077435 2631629 := bbase (se 3 (by rfl) ⟨493430, by rfl⟩ : syracuseStep 2631629 = 986861) (by norm_num)
theorem B7017677 : Blo 2077435 7017677 := bstep (se 3 (by rfl) ⟨1315814, by rfl⟩ : syracuseStep 7017677 = 2631629) B2631629
theorem B4678451 : Blo 2077435 4678451 := bstep (se 1 (by rfl) ⟨3508838, by rfl⟩ : syracuseStep 4678451 = 7017677) B7017677
theorem B3118967 : Blo 2077435 3118967 := bstep (se 1 (by rfl) ⟨2339225, by rfl⟩ : syracuseStep 3118967 = 4678451) B4678451
theorem B2079311 : Blo 2077435 2079311 := bstep (se 1 (by rfl) ⟨1559483, by rfl⟩ : syracuseStep 2079311 = 3118967) B3118967
theorem B3118973 : Blo 2077435 3118973 := bbase (se 3 (by rfl) ⟨584807, by rfl⟩ : syracuseStep 3118973 = 1169615) (by norm_num)
theorem B2079315 : Blo 2077435 2079315 := bstep (se 1 (by rfl) ⟨1559486, by rfl⟩ : syracuseStep 2079315 = 3118973) B3118973
theorem B4678469 : Blo 2077435 4678469 := bbase (se 4 (by rfl) ⟨438606, by rfl⟩ : syracuseStep 4678469 = 877213) (by norm_num)
theorem B3118979 : Blo 2077435 3118979 := bstep (se 1 (by rfl) ⟨2339234, by rfl⟩ : syracuseStep 3118979 = 4678469) B4678469
theorem B2079319 : Blo 2077435 2079319 := bstep (se 1 (by rfl) ⟨1559489, by rfl⟩ : syracuseStep 2079319 = 3118979) B3118979
theorem B4440901 : Blo 2077435 4440901 := bbase (se 4 (by rfl) ⟨416334, by rfl⟩ : syracuseStep 4440901 = 832669) (by norm_num)
theorem B5921201 : Blo 2077435 5921201 := bstep (se 2 (by rfl) ⟨2220450, by rfl⟩ : syracuseStep 5921201 = 4440901) B4440901
theorem B3947467 : Blo 2077435 3947467 := bstep (se 1 (by rfl) ⟨2960600, by rfl⟩ : syracuseStep 3947467 = 5921201) B5921201
theorem B5263289 : Blo 2077435 5263289 := bstep (se 2 (by rfl) ⟨1973733, by rfl⟩ : syracuseStep 5263289 = 3947467) B3947467
theorem B3508859 : Blo 2077435 3508859 := bstep (se 1 (by rfl) ⟨2631644, by rfl⟩ : syracuseStep 3508859 = 5263289) B5263289
theorem B2339239 : Blo 2077435 2339239 := bstep (se 1 (by rfl) ⟨1754429, by rfl⟩ : syracuseStep 2339239 = 3508859) B3508859
theorem B3118985 : Blo 2077435 3118985 := bstep (se 2 (by rfl) ⟨1169619, by rfl⟩ : syracuseStep 3118985 = 2339239) B2339239
theorem B2079323 : Blo 2077435 2079323 := bstep (se 1 (by rfl) ⟨1559492, by rfl⟩ : syracuseStep 2079323 = 3118985) B3118985
theorem B10526597 : Blo 2077435 10526597 := bbase (se 4 (by rfl) ⟨986868, by rfl⟩ : syracuseStep 10526597 = 1973737) (by norm_num)
theorem B7017731 : Blo 2077435 7017731 := bstep (se 1 (by rfl) ⟨5263298, by rfl⟩ : syracuseStep 7017731 = 10526597) B10526597
theorem B4678487 : Blo 2077435 4678487 := bstep (se 1 (by rfl) ⟨3508865, by rfl⟩ : syracuseStep 4678487 = 7017731) B7017731
theorem B3118991 : Blo 2077435 3118991 := bstep (se 1 (by rfl) ⟨2339243, by rfl⟩ : syracuseStep 3118991 = 4678487) B4678487
theorem B2079327 : Blo 2077435 2079327 := bstep (se 1 (by rfl) ⟨1559495, by rfl⟩ : syracuseStep 2079327 = 3118991) B3118991
theorem B3118997 : Blo 2077435 3118997 := bbase (se 6 (by rfl) ⟨73101, by rfl⟩ : syracuseStep 3118997 = 146203) (by norm_num)
theorem B2079331 : Blo 2077435 2079331 := bstep (se 1 (by rfl) ⟨1559498, by rfl⟩ : syracuseStep 2079331 = 3118997) B3118997
theorem B5620549 : Blo 2077435 5620549 := bbase (se 4 (by rfl) ⟨526926, by rfl⟩ : syracuseStep 5620549 = 1053853) (by norm_num)
theorem B7494065 : Blo 2077435 7494065 := bstep (se 2 (by rfl) ⟨2810274, by rfl⟩ : syracuseStep 7494065 = 5620549) B5620549
theorem B4996043 : Blo 2077435 4996043 := bstep (se 1 (by rfl) ⟨3747032, by rfl⟩ : syracuseStep 4996043 = 7494065) B7494065
theorem B3330695 : Blo 2077435 3330695 := bstep (se 1 (by rfl) ⟨2498021, by rfl⟩ : syracuseStep 3330695 = 4996043) B4996043
theorem B2220463 : Blo 2077435 2220463 := bstep (se 1 (by rfl) ⟨1665347, by rfl⟩ : syracuseStep 2220463 = 3330695) B3330695
theorem B11842469 : Blo 2077435 11842469 := bstep (se 4 (by rfl) ⟨1110231, by rfl⟩ : syracuseStep 11842469 = 2220463) B2220463
theorem B7894979 : Blo 2077435 7894979 := bstep (se 1 (by rfl) ⟨5921234, by rfl⟩ : syracuseStep 7894979 = 11842469) B11842469
theorem B5263319 : Blo 2077435 5263319 := bstep (se 1 (by rfl) ⟨3947489, by rfl⟩ : syracuseStep 5263319 = 7894979) B7894979
theorem B3508879 : Blo 2077435 3508879 := bstep (se 1 (by rfl) ⟨2631659, by rfl⟩ : syracuseStep 3508879 = 5263319) B5263319
theorem B4678505 : Blo 2077435 4678505 := bstep (se 2 (by rfl) ⟨1754439, by rfl⟩ : syracuseStep 4678505 = 3508879) B3508879
theorem B3119003 : Blo 2077435 3119003 := bstep (se 1 (by rfl) ⟨2339252, by rfl⟩ : syracuseStep 3119003 = 4678505) B4678505
theorem B2079335 : Blo 2077435 2079335 := bstep (se 1 (by rfl) ⟨1559501, by rfl⟩ : syracuseStep 2079335 = 3119003) B3119003
theorem B2339257 : Blo 2077435 2339257 := bbase (se 2 (by rfl) ⟨877221, by rfl⟩ : syracuseStep 2339257 = 1754443) (by norm_num)
theorem B3119009 : Blo 2077435 3119009 := bstep (se 2 (by rfl) ⟨1169628, by rfl⟩ : syracuseStep 3119009 = 2339257) B2339257
theorem B2079339 : Blo 2077435 2079339 := bstep (se 1 (by rfl) ⟨1559504, by rfl⟩ : syracuseStep 2079339 = 3119009) B3119009
theorem B6323141 : Blo 2077435 6323141 := bbase (se 4 (by rfl) ⟨592794, by rfl⟩ : syracuseStep 6323141 = 1185589) (by norm_num)
theorem B16861709 : Blo 2077435 16861709 := bstep (se 3 (by rfl) ⟨3161570, by rfl⟩ : syracuseStep 16861709 = 6323141) B6323141
theorem B11241139 : Blo 2077435 11241139 := bstep (se 1 (by rfl) ⟨8430854, by rfl⟩ : syracuseStep 11241139 = 16861709) B16861709
theorem B14988185 : Blo 2077435 14988185 := bstep (se 2 (by rfl) ⟨5620569, by rfl⟩ : syracuseStep 14988185 = 11241139) B11241139
theorem B9992123 : Blo 2077435 9992123 := bstep (se 1 (by rfl) ⟨7494092, by rfl⟩ : syracuseStep 9992123 = 14988185) B14988185
theorem B6661415 : Blo 2077435 6661415 := bstep (se 1 (by rfl) ⟨4996061, by rfl⟩ : syracuseStep 6661415 = 9992123) B9992123
theorem B4440943 : Blo 2077435 4440943 := bstep (se 1 (by rfl) ⟨3330707, by rfl⟩ : syracuseStep 4440943 = 6661415) B6661415
theorem B5921257 : Blo 2077435 5921257 := bstep (se 2 (by rfl) ⟨2220471, by rfl⟩ : syracuseStep 5921257 = 4440943) B4440943
theorem B7895009 : Blo 2077435 7895009 := bstep (se 2 (by rfl) ⟨2960628, by rfl⟩ : syracuseStep 7895009 = 5921257) B5921257
theorem B5263339 : Blo 2077435 5263339 := bstep (se 1 (by rfl) ⟨3947504, by rfl⟩ : syracuseStep 5263339 = 7895009) B7895009
theorem B7017785 : Blo 2077435 7017785 := bstep (se 2 (by rfl) ⟨2631669, by rfl⟩ : syracuseStep 7017785 = 5263339) B5263339
theorem B4678523 : Blo 2077435 4678523 := bstep (se 1 (by rfl) ⟨3508892, by rfl⟩ : syracuseStep 4678523 = 7017785) B7017785
theorem B3119015 : Blo 2077435 3119015 := bstep (se 1 (by rfl) ⟨2339261, by rfl⟩ : syracuseStep 3119015 = 4678523) B4678523
theorem B2079343 : Blo 2077435 2079343 := bstep (se 1 (by rfl) ⟨1559507, by rfl⟩ : syracuseStep 2079343 = 3119015) B3119015
theorem B3119021 : Blo 2077435 3119021 := bbase (se 3 (by rfl) ⟨584816, by rfl⟩ : syracuseStep 3119021 = 1169633) (by norm_num)
theorem B2079347 : Blo 2077435 2079347 := bstep (se 1 (by rfl) ⟨1559510, by rfl⟩ : syracuseStep 2079347 = 3119021) B3119021
theorem B4678541 : Blo 2077435 4678541 := bbase (se 3 (by rfl) ⟨877226, by rfl⟩ : syracuseStep 4678541 = 1754453) (by norm_num)
theorem B3119027 : Blo 2077435 3119027 := bstep (se 1 (by rfl) ⟨2339270, by rfl⟩ : syracuseStep 3119027 = 4678541) B4678541
theorem B2079351 : Blo 2077435 2079351 := bstep (se 1 (by rfl) ⟨1559513, by rfl⟩ : syracuseStep 2079351 = 3119027) B3119027
theorem B2631685 : Blo 2077435 2631685 := bbase (se 4 (by rfl) ⟨246720, by rfl⟩ : syracuseStep 2631685 = 493441) (by norm_num)
theorem B3508913 : Blo 2077435 3508913 := bstep (se 2 (by rfl) ⟨1315842, by rfl⟩ : syracuseStep 3508913 = 2631685) B2631685
theorem B2339275 : Blo 2077435 2339275 := bstep (se 1 (by rfl) ⟨1754456, by rfl⟩ : syracuseStep 2339275 = 3508913) B3508913
theorem B3119033 : Blo 2077435 3119033 := bstep (se 2 (by rfl) ⟨1169637, by rfl⟩ : syracuseStep 3119033 = 2339275) B2339275
theorem B2079355 : Blo 2077435 2079355 := bstep (se 1 (by rfl) ⟨1559516, by rfl⟩ : syracuseStep 2079355 = 3119033) B3119033
theorem B7494149 : Blo 2077435 7494149 := bbase (se 4 (by rfl) ⟨702576, by rfl⟩ : syracuseStep 7494149 = 1405153) (by norm_num)
theorem B4996099 : Blo 2077435 4996099 := bstep (se 1 (by rfl) ⟨3747074, by rfl⟩ : syracuseStep 4996099 = 7494149) B7494149
theorem B26645861 : Blo 2077435 26645861 := bstep (se 4 (by rfl) ⟨2498049, by rfl⟩ : syracuseStep 26645861 = 4996099) B4996099
theorem B17763907 : Blo 2077435 17763907 := bstep (se 1 (by rfl) ⟨13322930, by rfl⟩ : syracuseStep 17763907 = 26645861) B26645861
theorem B23685209 : Blo 2077435 23685209 := bstep (se 2 (by rfl) ⟨8881953, by rfl⟩ : syracuseStep 23685209 = 17763907) B17763907
theorem B15790139 : Blo 2077435 15790139 := bstep (se 1 (by rfl) ⟨11842604, by rfl⟩ : syracuseStep 15790139 = 23685209) B23685209
theorem B10526759 : Blo 2077435 10526759 := bstep (se 1 (by rfl) ⟨7895069, by rfl⟩ : syracuseStep 10526759 = 15790139) B15790139
theorem B7017839 : Blo 2077435 7017839 := bstep (se 1 (by rfl) ⟨5263379, by rfl⟩ : syracuseStep 7017839 = 10526759) B10526759
theorem B4678559 : Blo 2077435 4678559 := bstep (se 1 (by rfl) ⟨3508919, by rfl⟩ : syracuseStep 4678559 = 7017839) B7017839
theorem B3119039 : Blo 2077435 3119039 := bstep (se 1 (by rfl) ⟨2339279, by rfl⟩ : syracuseStep 3119039 = 4678559) B4678559
theorem B2079359 : Blo 2077435 2079359 := bstep (se 1 (by rfl) ⟨1559519, by rfl⟩ : syracuseStep 2079359 = 3119039) B3119039
theorem B3119045 : Blo 2077435 3119045 := bbase (se 4 (by rfl) ⟨292410, by rfl⟩ : syracuseStep 3119045 = 584821) (by norm_num)
theorem B2079363 : Blo 2077435 2079363 := bstep (se 1 (by rfl) ⟨1559522, by rfl⟩ : syracuseStep 2079363 = 3119045) B3119045
theorem B3508933 : Blo 2077435 3508933 := bbase (se 4 (by rfl) ⟨328962, by rfl⟩ : syracuseStep 3508933 = 657925) (by norm_num)
theorem B4678577 : Blo 2077435 4678577 := bstep (se 2 (by rfl) ⟨1754466, by rfl⟩ : syracuseStep 4678577 = 3508933) B3508933
theorem B3119051 : Blo 2077435 3119051 := bstep (se 1 (by rfl) ⟨2339288, by rfl⟩ : syracuseStep 3119051 = 4678577) B4678577
theorem B2079367 : Blo 2077435 2079367 := bstep (se 1 (by rfl) ⟨1559525, by rfl⟩ : syracuseStep 2079367 = 3119051) B3119051
theorem B2339293 : Blo 2077435 2339293 := bbase (se 3 (by rfl) ⟨438617, by rfl⟩ : syracuseStep 2339293 = 877235) (by norm_num)
theorem B3119057 : Blo 2077435 3119057 := bstep (se 2 (by rfl) ⟨1169646, by rfl⟩ : syracuseStep 3119057 = 2339293) B2339293
theorem B2079371 : Blo 2077435 2079371 := bstep (se 1 (by rfl) ⟨1559528, by rfl⟩ : syracuseStep 2079371 = 3119057) B3119057
theorem B7017893 : Blo 2077435 7017893 := bbase (se 4 (by rfl) ⟨657927, by rfl⟩ : syracuseStep 7017893 = 1315855) (by norm_num)
theorem B4678595 : Blo 2077435 4678595 := bstep (se 1 (by rfl) ⟨3508946, by rfl⟩ : syracuseStep 4678595 = 7017893) B7017893
theorem B3119063 : Blo 2077435 3119063 := bstep (se 1 (by rfl) ⟨2339297, by rfl⟩ : syracuseStep 3119063 = 4678595) B4678595
theorem B2079375 : Blo 2077435 2079375 := bstep (se 1 (by rfl) ⟨1559531, by rfl⟩ : syracuseStep 2079375 = 3119063) B3119063
theorem B3119069 : Blo 2077435 3119069 := bbase (se 3 (by rfl) ⟨584825, by rfl⟩ : syracuseStep 3119069 = 1169651) (by norm_num)
theorem B2079379 : Blo 2077435 2079379 := bstep (se 1 (by rfl) ⟨1559534, by rfl⟩ : syracuseStep 2079379 = 3119069) B3119069
theorem B4678613 : Blo 2077435 4678613 := bbase (se 7 (by rfl) ⟨54827, by rfl⟩ : syracuseStep 4678613 = 109655) (by norm_num)
theorem B3119075 : Blo 2077435 3119075 := bstep (se 1 (by rfl) ⟨2339306, by rfl⟩ : syracuseStep 3119075 = 4678613) B4678613
theorem B2079383 : Blo 2077435 2079383 := bstep (se 1 (by rfl) ⟨1559537, by rfl⟩ : syracuseStep 2079383 = 3119075) B3119075
theorem B7113685 : Blo 2077435 7113685 := bbase (se 7 (by rfl) ⟨83363, by rfl⟩ : syracuseStep 7113685 = 166727) (by norm_num)
theorem B9484913 : Blo 2077435 9484913 := bstep (se 2 (by rfl) ⟨3556842, by rfl⟩ : syracuseStep 9484913 = 7113685) B7113685
theorem B6323275 : Blo 2077435 6323275 := bstep (se 1 (by rfl) ⟨4742456, by rfl⟩ : syracuseStep 6323275 = 9484913) B9484913
theorem B33724133 : Blo 2077435 33724133 := bstep (se 4 (by rfl) ⟨3161637, by rfl⟩ : syracuseStep 33724133 = 6323275) B6323275
theorem B22482755 : Blo 2077435 22482755 := bstep (se 1 (by rfl) ⟨16862066, by rfl⟩ : syracuseStep 22482755 = 33724133) B33724133
theorem B14988503 : Blo 2077435 14988503 := bstep (se 1 (by rfl) ⟨11241377, by rfl⟩ : syracuseStep 14988503 = 22482755) B22482755
theorem B9992335 : Blo 2077435 9992335 := bstep (se 1 (by rfl) ⟨7494251, by rfl⟩ : syracuseStep 9992335 = 14988503) B14988503
theorem B13323113 : Blo 2077435 13323113 := bstep (se 2 (by rfl) ⟨4996167, by rfl⟩ : syracuseStep 13323113 = 9992335) B9992335
theorem B8882075 : Blo 2077435 8882075 := bstep (se 1 (by rfl) ⟨6661556, by rfl⟩ : syracuseStep 8882075 = 13323113) B13323113
theorem B5921383 : Blo 2077435 5921383 := bstep (se 1 (by rfl) ⟨4441037, by rfl⟩ : syracuseStep 5921383 = 8882075) B8882075
theorem B7895177 : Blo 2077435 7895177 := bstep (se 2 (by rfl) ⟨2960691, by rfl⟩ : syracuseStep 7895177 = 5921383) B5921383
theorem B5263451 : Blo 2077435 5263451 := bstep (se 1 (by rfl) ⟨3947588, by rfl⟩ : syracuseStep 5263451 = 7895177) B7895177
theorem B3508967 : Blo 2077435 3508967 := bstep (se 1 (by rfl) ⟨2631725, by rfl⟩ : syracuseStep 3508967 = 5263451) B5263451
theorem B2339311 : Blo 2077435 2339311 := bstep (se 1 (by rfl) ⟨1754483, by rfl⟩ : syracuseStep 2339311 = 3508967) B3508967
theorem B3119081 : Blo 2077435 3119081 := bstep (se 2 (by rfl) ⟨1169655, by rfl⟩ : syracuseStep 3119081 = 2339311) B2339311
theorem B2079387 : Blo 2077435 2079387 := bstep (se 1 (by rfl) ⟨1559540, by rfl⟩ : syracuseStep 2079387 = 3119081) B3119081
theorem B17764181 : Blo 2077435 17764181 := bbase (se 9 (by rfl) ⟨52043, by rfl⟩ : syracuseStep 17764181 = 104087) (by norm_num)
theorem B11842787 : Blo 2077435 11842787 := bstep (se 1 (by rfl) ⟨8882090, by rfl⟩ : syracuseStep 11842787 = 17764181) B17764181
theorem B7895191 : Blo 2077435 7895191 := bstep (se 1 (by rfl) ⟨5921393, by rfl⟩ : syracuseStep 7895191 = 11842787) B11842787
theorem B10526921 : Blo 2077435 10526921 := bstep (se 2 (by rfl) ⟨3947595, by rfl⟩ : syracuseStep 10526921 = 7895191) B7895191
theorem B7017947 : Blo 2077435 7017947 := bstep (se 1 (by rfl) ⟨5263460, by rfl⟩ : syracuseStep 7017947 = 10526921) B10526921
theorem B4678631 : Blo 2077435 4678631 := bstep (se 1 (by rfl) ⟨3508973, by rfl⟩ : syracuseStep 4678631 = 7017947) B7017947
theorem B3119087 : Blo 2077435 3119087 := bstep (se 1 (by rfl) ⟨2339315, by rfl⟩ : syracuseStep 3119087 = 4678631) B4678631
theorem B2079391 : Blo 2077435 2079391 := bstep (se 1 (by rfl) ⟨1559543, by rfl⟩ : syracuseStep 2079391 = 3119087) B3119087
theorem B3119093 : Blo 2077435 3119093 := bbase (se 5 (by rfl) ⟨146207, by rfl⟩ : syracuseStep 3119093 = 292415) (by norm_num)
theorem B2079395 : Blo 2077435 2079395 := bstep (se 1 (by rfl) ⟨1559546, by rfl⟩ : syracuseStep 2079395 = 3119093) B3119093
theorem B16862165 : Blo 2077435 16862165 := bbase (se 7 (by rfl) ⟨197603, by rfl⟩ : syracuseStep 16862165 = 395207) (by norm_num)
theorem B11241443 : Blo 2077435 11241443 := bstep (se 1 (by rfl) ⟨8431082, by rfl⟩ : syracuseStep 11241443 = 16862165) B16862165
theorem B7494295 : Blo 2077435 7494295 := bstep (se 1 (by rfl) ⟨5620721, by rfl⟩ : syracuseStep 7494295 = 11241443) B11241443
theorem B9992393 : Blo 2077435 9992393 := bstep (se 2 (by rfl) ⟨3747147, by rfl⟩ : syracuseStep 9992393 = 7494295) B7494295
theorem B6661595 : Blo 2077435 6661595 := bstep (se 1 (by rfl) ⟨4996196, by rfl⟩ : syracuseStep 6661595 = 9992393) B9992393
theorem B4441063 : Blo 2077435 4441063 := bstep (se 1 (by rfl) ⟨3330797, by rfl⟩ : syracuseStep 4441063 = 6661595) B6661595
theorem B5921417 : Blo 2077435 5921417 := bstep (se 2 (by rfl) ⟨2220531, by rfl⟩ : syracuseStep 5921417 = 4441063) B4441063
theorem B3947611 : Blo 2077435 3947611 := bstep (se 1 (by rfl) ⟨2960708, by rfl⟩ : syracuseStep 3947611 = 5921417) B5921417
theorem B5263481 : Blo 2077435 5263481 := bstep (se 2 (by rfl) ⟨1973805, by rfl⟩ : syracuseStep 5263481 = 3947611) B3947611
theorem B3508987 : Blo 2077435 3508987 := bstep (se 1 (by rfl) ⟨2631740, by rfl⟩ : syracuseStep 3508987 = 5263481) B5263481
theorem B4678649 : Blo 2077435 4678649 := bstep (se 2 (by rfl) ⟨1754493, by rfl⟩ : syracuseStep 4678649 = 3508987) B3508987
theorem B3119099 : Blo 2077435 3119099 := bstep (se 1 (by rfl) ⟨2339324, by rfl⟩ : syracuseStep 3119099 = 4678649) B4678649
theorem B2079399 : Blo 2077435 2079399 := bstep (se 1 (by rfl) ⟨1559549, by rfl⟩ : syracuseStep 2079399 = 3119099) B3119099
theorem B2339329 : Blo 2077435 2339329 := bbase (se 2 (by rfl) ⟨877248, by rfl⟩ : syracuseStep 2339329 = 1754497) (by norm_num)
theorem B3119105 : Blo 2077435 3119105 := bstep (se 2 (by rfl) ⟨1169664, by rfl⟩ : syracuseStep 3119105 = 2339329) B2339329
theorem B2079403 : Blo 2077435 2079403 := bstep (se 1 (by rfl) ⟨1559552, by rfl⟩ : syracuseStep 2079403 = 3119105) B3119105
theorem B5263501 : Blo 2077435 5263501 := bbase (se 3 (by rfl) ⟨986906, by rfl⟩ : syracuseStep 5263501 = 1973813) (by norm_num)
theorem B7018001 : Blo 2077435 7018001 := bstep (se 2 (by rfl) ⟨2631750, by rfl⟩ : syracuseStep 7018001 = 5263501) B5263501
theorem B4678667 : Blo 2077435 4678667 := bstep (se 1 (by rfl) ⟨3509000, by rfl⟩ : syracuseStep 4678667 = 7018001) B7018001
theorem B3119111 : Blo 2077435 3119111 := bstep (se 1 (by rfl) ⟨2339333, by rfl⟩ : syracuseStep 3119111 = 4678667) B4678667
theorem B2079407 : Blo 2077435 2079407 := bstep (se 1 (by rfl) ⟨1559555, by rfl⟩ : syracuseStep 2079407 = 3119111) B3119111
theorem B3119117 : Blo 2077435 3119117 := bbase (se 3 (by rfl) ⟨584834, by rfl⟩ : syracuseStep 3119117 = 1169669) (by norm_num)
theorem B2079411 : Blo 2077435 2079411 := bstep (se 1 (by rfl) ⟨1559558, by rfl⟩ : syracuseStep 2079411 = 3119117) B3119117
theorem B4678685 : Blo 2077435 4678685 := bbase (se 3 (by rfl) ⟨877253, by rfl⟩ : syracuseStep 4678685 = 1754507) (by norm_num)
theorem B3119123 : Blo 2077435 3119123 := bstep (se 1 (by rfl) ⟨2339342, by rfl⟩ : syracuseStep 3119123 = 4678685) B4678685
theorem B2079415 : Blo 2077435 2079415 := bstep (se 1 (by rfl) ⟨1559561, by rfl⟩ : syracuseStep 2079415 = 3119123) B3119123
theorem B3509021 : Blo 2077435 3509021 := bbase (se 3 (by rfl) ⟨657941, by rfl⟩ : syracuseStep 3509021 = 1315883) (by norm_num)
theorem B2339347 : Blo 2077435 2339347 := bstep (se 1 (by rfl) ⟨1754510, by rfl⟩ : syracuseStep 2339347 = 3509021) B3509021
theorem B3119129 : Blo 2077435 3119129 := bstep (se 2 (by rfl) ⟨1169673, by rfl⟩ : syracuseStep 3119129 = 2339347) B2339347
theorem B2079419 : Blo 2077435 2079419 := bstep (se 1 (by rfl) ⟨1559564, by rfl⟩ : syracuseStep 2079419 = 3119129) B3119129
theorem B4996253 : Blo 2077435 4996253 := bbase (se 3 (by rfl) ⟨936797, by rfl⟩ : syracuseStep 4996253 = 1873595) (by norm_num)
theorem B13323341 : Blo 2077435 13323341 := bstep (se 3 (by rfl) ⟨2498126, by rfl⟩ : syracuseStep 13323341 = 4996253) B4996253
theorem B8882227 : Blo 2077435 8882227 := bstep (se 1 (by rfl) ⟨6661670, by rfl⟩ : syracuseStep 8882227 = 13323341) B13323341
theorem B11842969 : Blo 2077435 11842969 := bstep (se 2 (by rfl) ⟨4441113, by rfl⟩ : syracuseStep 11842969 = 8882227) B8882227
theorem B15790625 : Blo 2077435 15790625 := bstep (se 2 (by rfl) ⟨5921484, by rfl⟩ : syracuseStep 15790625 = 11842969) B11842969
theorem B10527083 : Blo 2077435 10527083 := bstep (se 1 (by rfl) ⟨7895312, by rfl⟩ : syracuseStep 10527083 = 15790625) B15790625
theorem B7018055 : Blo 2077435 7018055 := bstep (se 1 (by rfl) ⟨5263541, by rfl⟩ : syracuseStep 7018055 = 10527083) B10527083
theorem B4678703 : Blo 2077435 4678703 := bstep (se 1 (by rfl) ⟨3509027, by rfl⟩ : syracuseStep 4678703 = 7018055) B7018055
theorem B3119135 : Blo 2077435 3119135 := bstep (se 1 (by rfl) ⟨2339351, by rfl⟩ : syracuseStep 3119135 = 4678703) B4678703
theorem B2079423 : Blo 2077435 2079423 := bstep (se 1 (by rfl) ⟨1559567, by rfl⟩ : syracuseStep 2079423 = 3119135) B3119135
theorem B3119141 : Blo 2077435 3119141 := bbase (se 4 (by rfl) ⟨292419, by rfl⟩ : syracuseStep 3119141 = 584839) (by norm_num)
theorem B2079427 : Blo 2077435 2079427 := bstep (se 1 (by rfl) ⟨1559570, by rfl⟩ : syracuseStep 2079427 = 3119141) B3119141
theorem B2631781 : Blo 2077435 2631781 := bbase (se 4 (by rfl) ⟨246729, by rfl⟩ : syracuseStep 2631781 = 493459) (by norm_num)
theorem B3509041 : Blo 2077435 3509041 := bstep (se 2 (by rfl) ⟨1315890, by rfl⟩ : syracuseStep 3509041 = 2631781) B2631781
theorem B4678721 : Blo 2077435 4678721 := bstep (se 2 (by rfl) ⟨1754520, by rfl⟩ : syracuseStep 4678721 = 3509041) B3509041
theorem B3119147 : Blo 2077435 3119147 := bstep (se 1 (by rfl) ⟨2339360, by rfl⟩ : syracuseStep 3119147 = 4678721) B4678721
theorem B2079431 : Blo 2077435 2079431 := bstep (se 1 (by rfl) ⟨1559573, by rfl⟩ : syracuseStep 2079431 = 3119147) B3119147
theorem B2339365 : Blo 2077435 2339365 := bbase (se 4 (by rfl) ⟨219315, by rfl⟩ : syracuseStep 2339365 = 438631) (by norm_num)
theorem B3119153 : Blo 2077435 3119153 := bstep (se 2 (by rfl) ⟨1169682, by rfl⟩ : syracuseStep 3119153 = 2339365) B2339365
theorem B2079435 : Blo 2077435 2079435 := bstep (se 1 (by rfl) ⟨1559576, by rfl⟩ : syracuseStep 2079435 = 3119153) B3119153
theorem C0 (j : ℕ) (h1 : 519358 ≤ j) (h2 : j ≤ 519858) : Blo 2077435 (4 * j + 3) := by
  interval_cases j
  · exact B2077435
  · exact B2077439
  · exact B2077443
  · exact B2077447
  · exact B2077451
  · exact B2077455
  · exact B2077459
  · exact B2077463
  · exact B2077467
  · exact B2077471
  · exact B2077475
  · exact B2077479
  · exact B2077483
  · exact B2077487
  · exact B2077491
  · exact B2077495
  · exact B2077499
  · exact B2077503
  · exact B2077507
  · exact B2077511
  · exact B2077515
  · exact B2077519
  · exact B2077523
  · exact B2077527
  · exact B2077531
  · exact B2077535
  · exact B2077539
  · exact B2077543
  · exact B2077547
  · exact B2077551
  · exact B2077555
  · exact B2077559
  · exact B2077563
  · exact B2077567
  · exact B2077571
  · exact B2077575
  · exact B2077579
  · exact B2077583
  · exact B2077587
  · exact B2077591
  · exact B2077595
  · exact B2077599
  · exact B2077603
  · exact B2077607
  · exact B2077611
  · exact B2077615
  · exact B2077619
  · exact B2077623
  · exact B2077627
  · exact B2077631
  · exact B2077635
  · exact B2077639
  · exact B2077643
  · exact B2077647
  · exact B2077651
  · exact B2077655
  · exact B2077659
  · exact B2077663
  · exact B2077667
  · exact B2077671
  · exact B2077675
  · exact B2077679
  · exact B2077683
  · exact B2077687
  · exact B2077691
  · exact B2077695
  · exact B2077699
  · exact B2077703
  · exact B2077707
  · exact B2077711
  · exact B2077715
  · exact B2077719
  · exact B2077723
  · exact B2077727
  · exact B2077731
  · exact B2077735
  · exact B2077739
  · exact B2077743
  · exact B2077747
  · exact B2077751
  · exact B2077755
  · exact B2077759
  · exact B2077763
  · exact B2077767
  · exact B2077771
  · exact B2077775
  · exact B2077779
  · exact B2077783
  · exact B2077787
  · exact B2077791
  · exact B2077795
  · exact B2077799
  · exact B2077803
  · exact B2077807
  · exact B2077811
  · exact B2077815
  · exact B2077819
  · exact B2077823
  · exact B2077827
  · exact B2077831
  · exact B2077835
  · exact B2077839
  · exact B2077843
  · exact B2077847
  · exact B2077851
  · exact B2077855
  · exact B2077859
  · exact B2077863
  · exact B2077867
  · exact B2077871
  · exact B2077875
  · exact B2077879
  · exact B2077883
  · exact B2077887
  · exact B2077891
  · exact B2077895
  · exact B2077899
  · exact B2077903
  · exact B2077907
  · exact B2077911
  · exact B2077915
  · exact B2077919
  · exact B2077923
  · exact B2077927
  · exact B2077931
  · exact B2077935
  · exact B2077939
  · exact B2077943
  · exact B2077947
  · exact B2077951
  · exact B2077955
  · exact B2077959
  · exact B2077963
  · exact B2077967
  · exact B2077971
  · exact B2077975
  · exact B2077979
  · exact B2077983
  · exact B2077987
  · exact B2077991
  · exact B2077995
  · exact B2077999
  · exact B2078003
  · exact B2078007
  · exact B2078011
  · exact B2078015
  · exact B2078019
  · exact B2078023
  · exact B2078027
  · exact B2078031
  · exact B2078035
  · exact B2078039
  · exact B2078043
  · exact B2078047
  · exact B2078051
  · exact B2078055
  · exact B2078059
  · exact B2078063
  · exact B2078067
  · exact B2078071
  · exact B2078075
  · exact B2078079
  · exact B2078083
  · exact B2078087
  · exact B2078091
  · exact B2078095
  · exact B2078099
  · exact B2078103
  · exact B2078107
  · exact B2078111
  · exact B2078115
  · exact B2078119
  · exact B2078123
  · exact B2078127
  · exact B2078131
  · exact B2078135
  · exact B2078139
  · exact B2078143
  · exact B2078147
  · exact B2078151
  · exact B2078155
  · exact B2078159
  · exact B2078163
  · exact B2078167
  · exact B2078171
  · exact B2078175
  · exact B2078179
  · exact B2078183
  · exact B2078187
  · exact B2078191
  · exact B2078195
  · exact B2078199
  · exact B2078203
  · exact B2078207
  · exact B2078211
  · exact B2078215
  · exact B2078219
  · exact B2078223
  · exact B2078227
  · exact B2078231
  · exact B2078235
  · exact B2078239
  · exact B2078243
  · exact B2078247
  · exact B2078251
  · exact B2078255
  · exact B2078259
  · exact B2078263
  · exact B2078267
  · exact B2078271
  · exact B2078275
  · exact B2078279
  · exact B2078283
  · exact B2078287
  · exact B2078291
  · exact B2078295
  · exact B2078299
  · exact B2078303
  · exact B2078307
  · exact B2078311
  · exact B2078315
  · exact B2078319
  · exact B2078323
  · exact B2078327
  · exact B2078331
  · exact B2078335
  · exact B2078339
  · exact B2078343
  · exact B2078347
  · exact B2078351
  · exact B2078355
  · exact B2078359
  · exact B2078363
  · exact B2078367
  · exact B2078371
  · exact B2078375
  · exact B2078379
  · exact B2078383
  · exact B2078387
  · exact B2078391
  · exact B2078395
  · exact B2078399
  · exact B2078403
  · exact B2078407
  · exact B2078411
  · exact B2078415
  · exact B2078419
  · exact B2078423
  · exact B2078427
  · exact B2078431
  · exact B2078435
  · exact B2078439
  · exact B2078443
  · exact B2078447
  · exact B2078451
  · exact B2078455
  · exact B2078459
  · exact B2078463
  · exact B2078467
  · exact B2078471
  · exact B2078475
  · exact B2078479
  · exact B2078483
  · exact B2078487
  · exact B2078491
  · exact B2078495
  · exact B2078499
  · exact B2078503
  · exact B2078507
  · exact B2078511
  · exact B2078515
  · exact B2078519
  · exact B2078523
  · exact B2078527
  · exact B2078531
  · exact B2078535
  · exact B2078539
  · exact B2078543
  · exact B2078547
  · exact B2078551
  · exact B2078555
  · exact B2078559
  · exact B2078563
  · exact B2078567
  · exact B2078571
  · exact B2078575
  · exact B2078579
  · exact B2078583
  · exact B2078587
  · exact B2078591
  · exact B2078595
  · exact B2078599
  · exact B2078603
  · exact B2078607
  · exact B2078611
  · exact B2078615
  · exact B2078619
  · exact B2078623
  · exact B2078627
  · exact B2078631
  · exact B2078635
  · exact B2078639
  · exact B2078643
  · exact B2078647
  · exact B2078651
  · exact B2078655
  · exact B2078659
  · exact B2078663
  · exact B2078667
  · exact B2078671
  · exact B2078675
  · exact B2078679
  · exact B2078683
  · exact B2078687
  · exact B2078691
  · exact B2078695
  · exact B2078699
  · exact B2078703
  · exact B2078707
  · exact B2078711
  · exact B2078715
  · exact B2078719
  · exact B2078723
  · exact B2078727
  · exact B2078731
  · exact B2078735
  · exact B2078739
  · exact B2078743
  · exact B2078747
  · exact B2078751
  · exact B2078755
  · exact B2078759
  · exact B2078763
  · exact B2078767
  · exact B2078771
  · exact B2078775
  · exact B2078779
  · exact B2078783
  · exact B2078787
  · exact B2078791
  · exact B2078795
  · exact B2078799
  · exact B2078803
  · exact B2078807
  · exact B2078811
  · exact B2078815
  · exact B2078819
  · exact B2078823
  · exact B2078827
  · exact B2078831
  · exact B2078835
  · exact B2078839
  · exact B2078843
  · exact B2078847
  · exact B2078851
  · exact B2078855
  · exact B2078859
  · exact B2078863
  · exact B2078867
  · exact B2078871
  · exact B2078875
  · exact B2078879
  · exact B2078883
  · exact B2078887
  · exact B2078891
  · exact B2078895
  · exact B2078899
  · exact B2078903
  · exact B2078907
  · exact B2078911
  · exact B2078915
  · exact B2078919
  · exact B2078923
  · exact B2078927
  · exact B2078931
  · exact B2078935
  · exact B2078939
  · exact B2078943
  · exact B2078947
  · exact B2078951
  · exact B2078955
  · exact B2078959
  · exact B2078963
  · exact B2078967
  · exact B2078971
  · exact B2078975
  · exact B2078979
  · exact B2078983
  · exact B2078987
  · exact B2078991
  · exact B2078995
  · exact B2078999
  · exact B2079003
  · exact B2079007
  · exact B2079011
  · exact B2079015
  · exact B2079019
  · exact B2079023
  · exact B2079027
  · exact B2079031
  · exact B2079035
  · exact B2079039
  · exact B2079043
  · exact B2079047
  · exact B2079051
  · exact B2079055
  · exact B2079059
  · exact B2079063
  · exact B2079067
  · exact B2079071
  · exact B2079075
  · exact B2079079
  · exact B2079083
  · exact B2079087
  · exact B2079091
  · exact B2079095
  · exact B2079099
  · exact B2079103
  · exact B2079107
  · exact B2079111
  · exact B2079115
  · exact B2079119
  · exact B2079123
  · exact B2079127
  · exact B2079131
  · exact B2079135
  · exact B2079139
  · exact B2079143
  · exact B2079147
  · exact B2079151
  · exact B2079155
  · exact B2079159
  · exact B2079163
  · exact B2079167
  · exact B2079171
  · exact B2079175
  · exact B2079179
  · exact B2079183
  · exact B2079187
  · exact B2079191
  · exact B2079195
  · exact B2079199
  · exact B2079203
  · exact B2079207
  · exact B2079211
  · exact B2079215
  · exact B2079219
  · exact B2079223
  · exact B2079227
  · exact B2079231
  · exact B2079235
  · exact B2079239
  · exact B2079243
  · exact B2079247
  · exact B2079251
  · exact B2079255
  · exact B2079259
  · exact B2079263
  · exact B2079267
  · exact B2079271
  · exact B2079275
  · exact B2079279
  · exact B2079283
  · exact B2079287
  · exact B2079291
  · exact B2079295
  · exact B2079299
  · exact B2079303
  · exact B2079307
  · exact B2079311
  · exact B2079315
  · exact B2079319
  · exact B2079323
  · exact B2079327
  · exact B2079331
  · exact B2079335
  · exact B2079339
  · exact B2079343
  · exact B2079347
  · exact B2079351
  · exact B2079355
  · exact B2079359
  · exact B2079363
  · exact B2079367
  · exact B2079371
  · exact B2079375
  · exact B2079379
  · exact B2079383
  · exact B2079387
  · exact B2079391
  · exact B2079395
  · exact B2079399
  · exact B2079403
  · exact B2079407
  · exact B2079411
  · exact B2079415
  · exact B2079419
  · exact B2079423
  · exact B2079427
  · exact B2079431
  · exact B2079435
theorem solution (m : ℕ) (hlo : 2077435 ≤ m) (hhi : m ≤ 2079435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 519358 ≤ j := by omega
    have hj2 : j ≤ 519858 := by omega
    have hb : Blo 2077435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
