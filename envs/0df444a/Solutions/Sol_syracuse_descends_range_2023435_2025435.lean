-- Prove2me | solution 1 for syracuse_descends_range_2023435_2025435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:48:54.405076+00:00
-- url     : https://prove2.me/submissions/5c1a6d6d-2ad6-496e-b3eb-d244e928fa5e

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

theorem B2276365 : Blo 2023435 2276365 := bbase (se 3 (by rfl) ⟨426818, by rfl⟩ : syracuseStep 2276365 = 853637) (by norm_num)
theorem B3035153 : Blo 2023435 3035153 := bstep (se 2 (by rfl) ⟨1138182, by rfl⟩ : syracuseStep 3035153 = 2276365) B2276365
theorem B2023435 : Blo 2023435 2023435 := bstep (se 1 (by rfl) ⟨1517576, by rfl⟩ : syracuseStep 2023435 = 3035153) B3035153
theorem B6829109 : Blo 2023435 6829109 := bbase (se 5 (by rfl) ⟨320114, by rfl⟩ : syracuseStep 6829109 = 640229) (by norm_num)
theorem B4552739 : Blo 2023435 4552739 := bstep (se 1 (by rfl) ⟨3414554, by rfl⟩ : syracuseStep 4552739 = 6829109) B6829109
theorem B3035159 : Blo 2023435 3035159 := bstep (se 1 (by rfl) ⟨2276369, by rfl⟩ : syracuseStep 3035159 = 4552739) B4552739
theorem B2023439 : Blo 2023435 2023439 := bstep (se 1 (by rfl) ⟨1517579, by rfl⟩ : syracuseStep 2023439 = 3035159) B3035159
theorem B3035165 : Blo 2023435 3035165 := bbase (se 3 (by rfl) ⟨569093, by rfl⟩ : syracuseStep 3035165 = 1138187) (by norm_num)
theorem B2023443 : Blo 2023435 2023443 := bstep (se 1 (by rfl) ⟨1517582, by rfl⟩ : syracuseStep 2023443 = 3035165) B3035165
theorem B4552757 : Blo 2023435 4552757 := bbase (se 5 (by rfl) ⟨213410, by rfl⟩ : syracuseStep 4552757 = 426821) (by norm_num)
theorem B3035171 : Blo 2023435 3035171 := bstep (se 1 (by rfl) ⟨2276378, by rfl⟩ : syracuseStep 3035171 = 4552757) B4552757
theorem B2023447 : Blo 2023435 2023447 := bstep (se 1 (by rfl) ⟨1517585, by rfl⟩ : syracuseStep 2023447 = 3035171) B3035171
theorem B3076589 : Blo 2023435 3076589 := bbase (se 3 (by rfl) ⟨576860, by rfl⟩ : syracuseStep 3076589 = 1153721) (by norm_num)
theorem B8204237 : Blo 2023435 8204237 := bstep (se 3 (by rfl) ⟨1538294, by rfl⟩ : syracuseStep 8204237 = 3076589) B3076589
theorem B5469491 : Blo 2023435 5469491 := bstep (se 1 (by rfl) ⟨4102118, by rfl⟩ : syracuseStep 5469491 = 8204237) B8204237
theorem B14585309 : Blo 2023435 14585309 := bstep (se 3 (by rfl) ⟨2734745, by rfl⟩ : syracuseStep 14585309 = 5469491) B5469491
theorem B9723539 : Blo 2023435 9723539 := bstep (se 1 (by rfl) ⟨7292654, by rfl⟩ : syracuseStep 9723539 = 14585309) B14585309
theorem B6482359 : Blo 2023435 6482359 := bstep (se 1 (by rfl) ⟨4861769, by rfl⟩ : syracuseStep 6482359 = 9723539) B9723539
theorem B8643145 : Blo 2023435 8643145 := bstep (se 2 (by rfl) ⟨3241179, by rfl⟩ : syracuseStep 8643145 = 6482359) B6482359
theorem B11524193 : Blo 2023435 11524193 := bstep (se 2 (by rfl) ⟨4321572, by rfl⟩ : syracuseStep 11524193 = 8643145) B8643145
theorem B7682795 : Blo 2023435 7682795 := bstep (se 1 (by rfl) ⟨5762096, by rfl⟩ : syracuseStep 7682795 = 11524193) B11524193
theorem B5121863 : Blo 2023435 5121863 := bstep (se 1 (by rfl) ⟨3841397, by rfl⟩ : syracuseStep 5121863 = 7682795) B7682795
theorem B3414575 : Blo 2023435 3414575 := bstep (se 1 (by rfl) ⟨2560931, by rfl⟩ : syracuseStep 3414575 = 5121863) B5121863
theorem B2276383 : Blo 2023435 2276383 := bstep (se 1 (by rfl) ⟨1707287, by rfl⟩ : syracuseStep 2276383 = 3414575) B3414575
theorem B3035177 : Blo 2023435 3035177 := bstep (se 2 (by rfl) ⟨1138191, by rfl⟩ : syracuseStep 3035177 = 2276383) B2276383
theorem B2023451 : Blo 2023435 2023451 := bstep (se 1 (by rfl) ⟨1517588, by rfl⟩ : syracuseStep 2023451 = 3035177) B3035177
theorem B9723557 : Blo 2023435 9723557 := bbase (se 4 (by rfl) ⟨911583, by rfl⟩ : syracuseStep 9723557 = 1823167) (by norm_num)
theorem B6482371 : Blo 2023435 6482371 := bstep (se 1 (by rfl) ⟨4861778, by rfl⟩ : syracuseStep 6482371 = 9723557) B9723557
theorem B8643161 : Blo 2023435 8643161 := bstep (se 2 (by rfl) ⟨3241185, by rfl⟩ : syracuseStep 8643161 = 6482371) B6482371
theorem B5762107 : Blo 2023435 5762107 := bstep (se 1 (by rfl) ⟨4321580, by rfl⟩ : syracuseStep 5762107 = 8643161) B8643161
theorem B7682809 : Blo 2023435 7682809 := bstep (se 2 (by rfl) ⟨2881053, by rfl⟩ : syracuseStep 7682809 = 5762107) B5762107
theorem B10243745 : Blo 2023435 10243745 := bstep (se 2 (by rfl) ⟨3841404, by rfl⟩ : syracuseStep 10243745 = 7682809) B7682809
theorem B6829163 : Blo 2023435 6829163 := bstep (se 1 (by rfl) ⟨5121872, by rfl⟩ : syracuseStep 6829163 = 10243745) B10243745
theorem B4552775 : Blo 2023435 4552775 := bstep (se 1 (by rfl) ⟨3414581, by rfl⟩ : syracuseStep 4552775 = 6829163) B6829163
theorem B3035183 : Blo 2023435 3035183 := bstep (se 1 (by rfl) ⟨2276387, by rfl⟩ : syracuseStep 3035183 = 4552775) B4552775
theorem B2023455 : Blo 2023435 2023455 := bstep (se 1 (by rfl) ⟨1517591, by rfl⟩ : syracuseStep 2023455 = 3035183) B3035183
theorem B3035189 : Blo 2023435 3035189 := bbase (se 5 (by rfl) ⟨142274, by rfl⟩ : syracuseStep 3035189 = 284549) (by norm_num)
theorem B2023459 : Blo 2023435 2023459 := bstep (se 1 (by rfl) ⟨1517594, by rfl⟩ : syracuseStep 2023459 = 3035189) B3035189
theorem B5121893 : Blo 2023435 5121893 := bbase (se 4 (by rfl) ⟨480177, by rfl⟩ : syracuseStep 5121893 = 960355) (by norm_num)
theorem B3414595 : Blo 2023435 3414595 := bstep (se 1 (by rfl) ⟨2560946, by rfl⟩ : syracuseStep 3414595 = 5121893) B5121893
theorem B4552793 : Blo 2023435 4552793 := bstep (se 2 (by rfl) ⟨1707297, by rfl⟩ : syracuseStep 4552793 = 3414595) B3414595
theorem B3035195 : Blo 2023435 3035195 := bstep (se 1 (by rfl) ⟨2276396, by rfl⟩ : syracuseStep 3035195 = 4552793) B4552793
theorem B2023463 : Blo 2023435 2023463 := bstep (se 1 (by rfl) ⟨1517597, by rfl⟩ : syracuseStep 2023463 = 3035195) B3035195
theorem B2276401 : Blo 2023435 2276401 := bbase (se 2 (by rfl) ⟨853650, by rfl⟩ : syracuseStep 2276401 = 1707301) (by norm_num)
theorem B3035201 : Blo 2023435 3035201 := bstep (se 2 (by rfl) ⟨1138200, by rfl⟩ : syracuseStep 3035201 = 2276401) B2276401
theorem B2023467 : Blo 2023435 2023467 := bstep (se 1 (by rfl) ⟨1517600, by rfl⟩ : syracuseStep 2023467 = 3035201) B3035201
theorem B13844789 : Blo 2023435 13844789 := bbase (se 5 (by rfl) ⟨648974, by rfl⟩ : syracuseStep 13844789 = 1297949) (by norm_num)
theorem B9229859 : Blo 2023435 9229859 := bstep (se 1 (by rfl) ⟨6922394, by rfl⟩ : syracuseStep 9229859 = 13844789) B13844789
theorem B6153239 : Blo 2023435 6153239 := bstep (se 1 (by rfl) ⟨4614929, by rfl⟩ : syracuseStep 6153239 = 9229859) B9229859
theorem B4102159 : Blo 2023435 4102159 := bstep (se 1 (by rfl) ⟨3076619, by rfl⟩ : syracuseStep 4102159 = 6153239) B6153239
theorem B5469545 : Blo 2023435 5469545 := bstep (se 2 (by rfl) ⟨2051079, by rfl⟩ : syracuseStep 5469545 = 4102159) B4102159
theorem B14585453 : Blo 2023435 14585453 := bstep (se 3 (by rfl) ⟨2734772, by rfl⟩ : syracuseStep 14585453 = 5469545) B5469545
theorem B9723635 : Blo 2023435 9723635 := bstep (se 1 (by rfl) ⟨7292726, by rfl⟩ : syracuseStep 9723635 = 14585453) B14585453
theorem B6482423 : Blo 2023435 6482423 := bstep (se 1 (by rfl) ⟨4861817, by rfl⟩ : syracuseStep 6482423 = 9723635) B9723635
theorem B4321615 : Blo 2023435 4321615 := bstep (se 1 (by rfl) ⟨3241211, by rfl⟩ : syracuseStep 4321615 = 6482423) B6482423
theorem B5762153 : Blo 2023435 5762153 := bstep (se 2 (by rfl) ⟨2160807, by rfl⟩ : syracuseStep 5762153 = 4321615) B4321615
theorem B3841435 : Blo 2023435 3841435 := bstep (se 1 (by rfl) ⟨2881076, by rfl⟩ : syracuseStep 3841435 = 5762153) B5762153
theorem B5121913 : Blo 2023435 5121913 := bstep (se 2 (by rfl) ⟨1920717, by rfl⟩ : syracuseStep 5121913 = 3841435) B3841435
theorem B6829217 : Blo 2023435 6829217 := bstep (se 2 (by rfl) ⟨2560956, by rfl⟩ : syracuseStep 6829217 = 5121913) B5121913
theorem B4552811 : Blo 2023435 4552811 := bstep (se 1 (by rfl) ⟨3414608, by rfl⟩ : syracuseStep 4552811 = 6829217) B6829217
theorem B3035207 : Blo 2023435 3035207 := bstep (se 1 (by rfl) ⟨2276405, by rfl⟩ : syracuseStep 3035207 = 4552811) B4552811
theorem B2023471 : Blo 2023435 2023471 := bstep (se 1 (by rfl) ⟨1517603, by rfl⟩ : syracuseStep 2023471 = 3035207) B3035207
theorem B3035213 : Blo 2023435 3035213 := bbase (se 3 (by rfl) ⟨569102, by rfl⟩ : syracuseStep 3035213 = 1138205) (by norm_num)
theorem B2023475 : Blo 2023435 2023475 := bstep (se 1 (by rfl) ⟨1517606, by rfl⟩ : syracuseStep 2023475 = 3035213) B3035213
theorem B4552829 : Blo 2023435 4552829 := bbase (se 3 (by rfl) ⟨853655, by rfl⟩ : syracuseStep 4552829 = 1707311) (by norm_num)
theorem B3035219 : Blo 2023435 3035219 := bstep (se 1 (by rfl) ⟨2276414, by rfl⟩ : syracuseStep 3035219 = 4552829) B4552829
theorem B2023479 : Blo 2023435 2023479 := bstep (se 1 (by rfl) ⟨1517609, by rfl⟩ : syracuseStep 2023479 = 3035219) B3035219
theorem B3414629 : Blo 2023435 3414629 := bbase (se 4 (by rfl) ⟨320121, by rfl⟩ : syracuseStep 3414629 = 640243) (by norm_num)
theorem B2276419 : Blo 2023435 2276419 := bstep (se 1 (by rfl) ⟨1707314, by rfl⟩ : syracuseStep 2276419 = 3414629) B3414629
theorem B3035225 : Blo 2023435 3035225 := bstep (se 2 (by rfl) ⟨1138209, by rfl⟩ : syracuseStep 3035225 = 2276419) B2276419
theorem B2023483 : Blo 2023435 2023483 := bstep (se 1 (by rfl) ⟨1517612, by rfl⟩ : syracuseStep 2023483 = 3035225) B3035225
theorem B3241237 : Blo 2023435 3241237 := bbase (se 6 (by rfl) ⟨75966, by rfl⟩ : syracuseStep 3241237 = 151933) (by norm_num)
theorem B4321649 : Blo 2023435 4321649 := bstep (se 2 (by rfl) ⟨1620618, by rfl⟩ : syracuseStep 4321649 = 3241237) B3241237
theorem B2881099 : Blo 2023435 2881099 := bstep (se 1 (by rfl) ⟨2160824, by rfl⟩ : syracuseStep 2881099 = 4321649) B4321649
theorem B15365861 : Blo 2023435 15365861 := bstep (se 4 (by rfl) ⟨1440549, by rfl⟩ : syracuseStep 15365861 = 2881099) B2881099
theorem B10243907 : Blo 2023435 10243907 := bstep (se 1 (by rfl) ⟨7682930, by rfl⟩ : syracuseStep 10243907 = 15365861) B15365861
theorem B6829271 : Blo 2023435 6829271 := bstep (se 1 (by rfl) ⟨5121953, by rfl⟩ : syracuseStep 6829271 = 10243907) B10243907
theorem B4552847 : Blo 2023435 4552847 := bstep (se 1 (by rfl) ⟨3414635, by rfl⟩ : syracuseStep 4552847 = 6829271) B6829271
theorem B3035231 : Blo 2023435 3035231 := bstep (se 1 (by rfl) ⟨2276423, by rfl⟩ : syracuseStep 3035231 = 4552847) B4552847
theorem B2023487 : Blo 2023435 2023487 := bstep (se 1 (by rfl) ⟨1517615, by rfl⟩ : syracuseStep 2023487 = 3035231) B3035231
theorem B3035237 : Blo 2023435 3035237 := bbase (se 4 (by rfl) ⟨284553, by rfl⟩ : syracuseStep 3035237 = 569107) (by norm_num)
theorem B2023491 : Blo 2023435 2023491 := bstep (se 1 (by rfl) ⟨1517618, by rfl⟩ : syracuseStep 2023491 = 3035237) B3035237
theorem B6482501 : Blo 2023435 6482501 := bbase (se 4 (by rfl) ⟨607734, by rfl⟩ : syracuseStep 6482501 = 1215469) (by norm_num)
theorem B4321667 : Blo 2023435 4321667 := bstep (se 1 (by rfl) ⟨3241250, by rfl⟩ : syracuseStep 4321667 = 6482501) B6482501
theorem B2881111 : Blo 2023435 2881111 := bstep (se 1 (by rfl) ⟨2160833, by rfl⟩ : syracuseStep 2881111 = 4321667) B4321667
theorem B3841481 : Blo 2023435 3841481 := bstep (se 2 (by rfl) ⟨1440555, by rfl⟩ : syracuseStep 3841481 = 2881111) B2881111
theorem B2560987 : Blo 2023435 2560987 := bstep (se 1 (by rfl) ⟨1920740, by rfl⟩ : syracuseStep 2560987 = 3841481) B3841481
theorem B3414649 : Blo 2023435 3414649 := bstep (se 2 (by rfl) ⟨1280493, by rfl⟩ : syracuseStep 3414649 = 2560987) B2560987
theorem B4552865 : Blo 2023435 4552865 := bstep (se 2 (by rfl) ⟨1707324, by rfl⟩ : syracuseStep 4552865 = 3414649) B3414649
theorem B3035243 : Blo 2023435 3035243 := bstep (se 1 (by rfl) ⟨2276432, by rfl⟩ : syracuseStep 3035243 = 4552865) B4552865
theorem B2023495 : Blo 2023435 2023495 := bstep (se 1 (by rfl) ⟨1517621, by rfl⟩ : syracuseStep 2023495 = 3035243) B3035243
theorem B2276437 : Blo 2023435 2276437 := bbase (se 8 (by rfl) ⟨13338, by rfl⟩ : syracuseStep 2276437 = 26677) (by norm_num)
theorem B3035249 : Blo 2023435 3035249 := bstep (se 2 (by rfl) ⟨1138218, by rfl⟩ : syracuseStep 3035249 = 2276437) B2276437
theorem B2023499 : Blo 2023435 2023499 := bstep (se 1 (by rfl) ⟨1517624, by rfl⟩ : syracuseStep 2023499 = 3035249) B3035249
theorem B2560997 : Blo 2023435 2560997 := bbase (se 4 (by rfl) ⟨240093, by rfl⟩ : syracuseStep 2560997 = 480187) (by norm_num)
theorem B6829325 : Blo 2023435 6829325 := bstep (se 3 (by rfl) ⟨1280498, by rfl⟩ : syracuseStep 6829325 = 2560997) B2560997
theorem B4552883 : Blo 2023435 4552883 := bstep (se 1 (by rfl) ⟨3414662, by rfl⟩ : syracuseStep 4552883 = 6829325) B6829325
theorem B3035255 : Blo 2023435 3035255 := bstep (se 1 (by rfl) ⟨2276441, by rfl⟩ : syracuseStep 3035255 = 4552883) B4552883
theorem B2023503 : Blo 2023435 2023503 := bstep (se 1 (by rfl) ⟨1517627, by rfl⟩ : syracuseStep 2023503 = 3035255) B3035255
theorem B3035261 : Blo 2023435 3035261 := bbase (se 3 (by rfl) ⟨569111, by rfl⟩ : syracuseStep 3035261 = 1138223) (by norm_num)
theorem B2023507 : Blo 2023435 2023507 := bstep (se 1 (by rfl) ⟨1517630, by rfl⟩ : syracuseStep 2023507 = 3035261) B3035261
theorem B4552901 : Blo 2023435 4552901 := bbase (se 4 (by rfl) ⟨426834, by rfl⟩ : syracuseStep 4552901 = 853669) (by norm_num)
theorem B3035267 : Blo 2023435 3035267 := bstep (se 1 (by rfl) ⟨2276450, by rfl⟩ : syracuseStep 3035267 = 4552901) B4552901
theorem B2023511 : Blo 2023435 2023511 := bstep (se 1 (by rfl) ⟨1517633, by rfl⟩ : syracuseStep 2023511 = 3035267) B3035267
theorem B2464129 : Blo 2023435 2464129 := bbase (se 2 (by rfl) ⟨924048, by rfl⟩ : syracuseStep 2464129 = 1848097) (by norm_num)
theorem B3285505 : Blo 2023435 3285505 := bstep (se 2 (by rfl) ⟨1232064, by rfl⟩ : syracuseStep 3285505 = 2464129) B2464129
theorem B17522693 : Blo 2023435 17522693 := bstep (se 4 (by rfl) ⟨1642752, by rfl⟩ : syracuseStep 17522693 = 3285505) B3285505
theorem B11681795 : Blo 2023435 11681795 := bstep (se 1 (by rfl) ⟨8761346, by rfl⟩ : syracuseStep 11681795 = 17522693) B17522693
theorem B7787863 : Blo 2023435 7787863 := bstep (se 1 (by rfl) ⟨5840897, by rfl⟩ : syracuseStep 7787863 = 11681795) B11681795
theorem B10383817 : Blo 2023435 10383817 := bstep (se 2 (by rfl) ⟨3893931, by rfl⟩ : syracuseStep 10383817 = 7787863) B7787863
theorem B13845089 : Blo 2023435 13845089 := bstep (se 2 (by rfl) ⟨5191908, by rfl⟩ : syracuseStep 13845089 = 10383817) B10383817
theorem B9230059 : Blo 2023435 9230059 := bstep (se 1 (by rfl) ⟨6922544, by rfl⟩ : syracuseStep 9230059 = 13845089) B13845089
theorem B12306745 : Blo 2023435 12306745 := bstep (se 2 (by rfl) ⟨4615029, by rfl⟩ : syracuseStep 12306745 = 9230059) B9230059
theorem B16408993 : Blo 2023435 16408993 := bstep (se 2 (by rfl) ⟨6153372, by rfl⟩ : syracuseStep 16408993 = 12306745) B12306745
theorem B21878657 : Blo 2023435 21878657 := bstep (se 2 (by rfl) ⟨8204496, by rfl⟩ : syracuseStep 21878657 = 16408993) B16408993
theorem B14585771 : Blo 2023435 14585771 := bstep (se 1 (by rfl) ⟨10939328, by rfl⟩ : syracuseStep 14585771 = 21878657) B21878657
theorem B9723847 : Blo 2023435 9723847 := bstep (se 1 (by rfl) ⟨7292885, by rfl⟩ : syracuseStep 9723847 = 14585771) B14585771
theorem B12965129 : Blo 2023435 12965129 := bstep (se 2 (by rfl) ⟨4861923, by rfl⟩ : syracuseStep 12965129 = 9723847) B9723847
theorem B8643419 : Blo 2023435 8643419 := bstep (se 1 (by rfl) ⟨6482564, by rfl⟩ : syracuseStep 8643419 = 12965129) B12965129
theorem B5762279 : Blo 2023435 5762279 := bstep (se 1 (by rfl) ⟨4321709, by rfl⟩ : syracuseStep 5762279 = 8643419) B8643419
theorem B3841519 : Blo 2023435 3841519 := bstep (se 1 (by rfl) ⟨2881139, by rfl⟩ : syracuseStep 3841519 = 5762279) B5762279
theorem B5122025 : Blo 2023435 5122025 := bstep (se 2 (by rfl) ⟨1920759, by rfl⟩ : syracuseStep 5122025 = 3841519) B3841519
theorem B3414683 : Blo 2023435 3414683 := bstep (se 1 (by rfl) ⟨2561012, by rfl⟩ : syracuseStep 3414683 = 5122025) B5122025
theorem B2276455 : Blo 2023435 2276455 := bstep (se 1 (by rfl) ⟨1707341, by rfl⟩ : syracuseStep 2276455 = 3414683) B3414683
theorem B3035273 : Blo 2023435 3035273 := bstep (se 2 (by rfl) ⟨1138227, by rfl⟩ : syracuseStep 3035273 = 2276455) B2276455
theorem B2023515 : Blo 2023435 2023515 := bstep (se 1 (by rfl) ⟨1517636, by rfl⟩ : syracuseStep 2023515 = 3035273) B3035273
theorem B10244069 : Blo 2023435 10244069 := bbase (se 4 (by rfl) ⟨960381, by rfl⟩ : syracuseStep 10244069 = 1920763) (by norm_num)
theorem B6829379 : Blo 2023435 6829379 := bstep (se 1 (by rfl) ⟨5122034, by rfl⟩ : syracuseStep 6829379 = 10244069) B10244069
theorem B4552919 : Blo 2023435 4552919 := bstep (se 1 (by rfl) ⟨3414689, by rfl⟩ : syracuseStep 4552919 = 6829379) B6829379
theorem B3035279 : Blo 2023435 3035279 := bstep (se 1 (by rfl) ⟨2276459, by rfl⟩ : syracuseStep 3035279 = 4552919) B4552919
theorem B2023519 : Blo 2023435 2023519 := bstep (se 1 (by rfl) ⟨1517639, by rfl⟩ : syracuseStep 2023519 = 3035279) B3035279
theorem B3035285 : Blo 2023435 3035285 := bbase (se 6 (by rfl) ⟨71139, by rfl⟩ : syracuseStep 3035285 = 142279) (by norm_num)
theorem B2023523 : Blo 2023435 2023523 := bstep (se 1 (by rfl) ⟨1517642, by rfl⟩ : syracuseStep 2023523 = 3035285) B3035285
theorem B3241301 : Blo 2023435 3241301 := bbase (se 13 (by rfl) ⟨593, by rfl⟩ : syracuseStep 3241301 = 1187) (by norm_num)
theorem B8643469 : Blo 2023435 8643469 := bstep (se 3 (by rfl) ⟨1620650, by rfl⟩ : syracuseStep 8643469 = 3241301) B3241301
theorem B11524625 : Blo 2023435 11524625 := bstep (se 2 (by rfl) ⟨4321734, by rfl⟩ : syracuseStep 11524625 = 8643469) B8643469
theorem B7683083 : Blo 2023435 7683083 := bstep (se 1 (by rfl) ⟨5762312, by rfl⟩ : syracuseStep 7683083 = 11524625) B11524625
theorem B5122055 : Blo 2023435 5122055 := bstep (se 1 (by rfl) ⟨3841541, by rfl⟩ : syracuseStep 5122055 = 7683083) B7683083
theorem B3414703 : Blo 2023435 3414703 := bstep (se 1 (by rfl) ⟨2561027, by rfl⟩ : syracuseStep 3414703 = 5122055) B5122055
theorem B4552937 : Blo 2023435 4552937 := bstep (se 2 (by rfl) ⟨1707351, by rfl⟩ : syracuseStep 4552937 = 3414703) B3414703
theorem B3035291 : Blo 2023435 3035291 := bstep (se 1 (by rfl) ⟨2276468, by rfl⟩ : syracuseStep 3035291 = 4552937) B4552937
theorem B2023527 : Blo 2023435 2023527 := bstep (se 1 (by rfl) ⟨1517645, by rfl⟩ : syracuseStep 2023527 = 3035291) B3035291
theorem B2276473 : Blo 2023435 2276473 := bbase (se 2 (by rfl) ⟨853677, by rfl⟩ : syracuseStep 2276473 = 1707355) (by norm_num)
theorem B3035297 : Blo 2023435 3035297 := bstep (se 2 (by rfl) ⟨1138236, by rfl⟩ : syracuseStep 3035297 = 2276473) B2276473
theorem B2023531 : Blo 2023435 2023531 := bstep (se 1 (by rfl) ⟨1517648, by rfl⟩ : syracuseStep 2023531 = 3035297) B3035297
theorem B21878869 : Blo 2023435 21878869 := bbase (se 8 (by rfl) ⟨128196, by rfl⟩ : syracuseStep 21878869 = 256393) (by norm_num)
theorem B29171825 : Blo 2023435 29171825 := bstep (se 2 (by rfl) ⟨10939434, by rfl⟩ : syracuseStep 29171825 = 21878869) B21878869
theorem B19447883 : Blo 2023435 19447883 := bstep (se 1 (by rfl) ⟨14585912, by rfl⟩ : syracuseStep 19447883 = 29171825) B29171825
theorem B12965255 : Blo 2023435 12965255 := bstep (se 1 (by rfl) ⟨9723941, by rfl⟩ : syracuseStep 12965255 = 19447883) B19447883
theorem B8643503 : Blo 2023435 8643503 := bstep (se 1 (by rfl) ⟨6482627, by rfl⟩ : syracuseStep 8643503 = 12965255) B12965255
theorem B5762335 : Blo 2023435 5762335 := bstep (se 1 (by rfl) ⟨4321751, by rfl⟩ : syracuseStep 5762335 = 8643503) B8643503
theorem B7683113 : Blo 2023435 7683113 := bstep (se 2 (by rfl) ⟨2881167, by rfl⟩ : syracuseStep 7683113 = 5762335) B5762335
theorem B5122075 : Blo 2023435 5122075 := bstep (se 1 (by rfl) ⟨3841556, by rfl⟩ : syracuseStep 5122075 = 7683113) B7683113
theorem B6829433 : Blo 2023435 6829433 := bstep (se 2 (by rfl) ⟨2561037, by rfl⟩ : syracuseStep 6829433 = 5122075) B5122075
theorem B4552955 : Blo 2023435 4552955 := bstep (se 1 (by rfl) ⟨3414716, by rfl⟩ : syracuseStep 4552955 = 6829433) B6829433
theorem B3035303 : Blo 2023435 3035303 := bstep (se 1 (by rfl) ⟨2276477, by rfl⟩ : syracuseStep 3035303 = 4552955) B4552955
theorem B2023535 : Blo 2023435 2023535 := bstep (se 1 (by rfl) ⟨1517651, by rfl⟩ : syracuseStep 2023535 = 3035303) B3035303
theorem B3035309 : Blo 2023435 3035309 := bbase (se 3 (by rfl) ⟨569120, by rfl⟩ : syracuseStep 3035309 = 1138241) (by norm_num)
theorem B2023539 : Blo 2023435 2023539 := bstep (se 1 (by rfl) ⟨1517654, by rfl⟩ : syracuseStep 2023539 = 3035309) B3035309
theorem B4552973 : Blo 2023435 4552973 := bbase (se 3 (by rfl) ⟨853682, by rfl⟩ : syracuseStep 4552973 = 1707365) (by norm_num)
theorem B3035315 : Blo 2023435 3035315 := bstep (se 1 (by rfl) ⟨2276486, by rfl⟩ : syracuseStep 3035315 = 4552973) B4552973
theorem B2023543 : Blo 2023435 2023543 := bstep (se 1 (by rfl) ⟨1517657, by rfl⟩ : syracuseStep 2023543 = 3035315) B3035315
theorem B2561053 : Blo 2023435 2561053 := bbase (se 3 (by rfl) ⟨480197, by rfl⟩ : syracuseStep 2561053 = 960395) (by norm_num)
theorem B3414737 : Blo 2023435 3414737 := bstep (se 2 (by rfl) ⟨1280526, by rfl⟩ : syracuseStep 3414737 = 2561053) B2561053
theorem B2276491 : Blo 2023435 2276491 := bstep (se 1 (by rfl) ⟨1707368, by rfl⟩ : syracuseStep 2276491 = 3414737) B3414737
theorem B3035321 : Blo 2023435 3035321 := bstep (se 2 (by rfl) ⟨1138245, by rfl⟩ : syracuseStep 3035321 = 2276491) B2276491
theorem B2023547 : Blo 2023435 2023547 := bstep (se 1 (by rfl) ⟨1517660, by rfl⟩ : syracuseStep 2023547 = 3035321) B3035321
theorem B3076741 : Blo 2023435 3076741 := bbase (se 4 (by rfl) ⟨288444, by rfl⟩ : syracuseStep 3076741 = 576889) (by norm_num)
theorem B4102321 : Blo 2023435 4102321 := bstep (se 2 (by rfl) ⟨1538370, by rfl⟩ : syracuseStep 4102321 = 3076741) B3076741
theorem B5469761 : Blo 2023435 5469761 := bstep (se 2 (by rfl) ⟨2051160, by rfl⟩ : syracuseStep 5469761 = 4102321) B4102321
theorem B3646507 : Blo 2023435 3646507 := bstep (se 1 (by rfl) ⟨2734880, by rfl⟩ : syracuseStep 3646507 = 5469761) B5469761
theorem B4862009 : Blo 2023435 4862009 := bstep (se 2 (by rfl) ⟨1823253, by rfl⟩ : syracuseStep 4862009 = 3646507) B3646507
theorem B3241339 : Blo 2023435 3241339 := bstep (se 1 (by rfl) ⟨2431004, by rfl⟩ : syracuseStep 3241339 = 4862009) B4862009
theorem B17287141 : Blo 2023435 17287141 := bstep (se 4 (by rfl) ⟨1620669, by rfl⟩ : syracuseStep 17287141 = 3241339) B3241339
theorem B23049521 : Blo 2023435 23049521 := bstep (se 2 (by rfl) ⟨8643570, by rfl⟩ : syracuseStep 23049521 = 17287141) B17287141
theorem B15366347 : Blo 2023435 15366347 := bstep (se 1 (by rfl) ⟨11524760, by rfl⟩ : syracuseStep 15366347 = 23049521) B23049521
theorem B10244231 : Blo 2023435 10244231 := bstep (se 1 (by rfl) ⟨7683173, by rfl⟩ : syracuseStep 10244231 = 15366347) B15366347
theorem B6829487 : Blo 2023435 6829487 := bstep (se 1 (by rfl) ⟨5122115, by rfl⟩ : syracuseStep 6829487 = 10244231) B10244231
theorem B4552991 : Blo 2023435 4552991 := bstep (se 1 (by rfl) ⟨3414743, by rfl⟩ : syracuseStep 4552991 = 6829487) B6829487
theorem B3035327 : Blo 2023435 3035327 := bstep (se 1 (by rfl) ⟨2276495, by rfl⟩ : syracuseStep 3035327 = 4552991) B4552991
theorem B2023551 : Blo 2023435 2023551 := bstep (se 1 (by rfl) ⟨1517663, by rfl⟩ : syracuseStep 2023551 = 3035327) B3035327
theorem B3035333 : Blo 2023435 3035333 := bbase (se 4 (by rfl) ⟨284562, by rfl⟩ : syracuseStep 3035333 = 569125) (by norm_num)
theorem B2023555 : Blo 2023435 2023555 := bstep (se 1 (by rfl) ⟨1517666, by rfl⟩ : syracuseStep 2023555 = 3035333) B3035333
theorem B3414757 : Blo 2023435 3414757 := bbase (se 4 (by rfl) ⟨320133, by rfl⟩ : syracuseStep 3414757 = 640267) (by norm_num)
theorem B4553009 : Blo 2023435 4553009 := bstep (se 2 (by rfl) ⟨1707378, by rfl⟩ : syracuseStep 4553009 = 3414757) B3414757
theorem B3035339 : Blo 2023435 3035339 := bstep (se 1 (by rfl) ⟨2276504, by rfl⟩ : syracuseStep 3035339 = 4553009) B4553009
theorem B2023559 : Blo 2023435 2023559 := bstep (se 1 (by rfl) ⟨1517669, by rfl⟩ : syracuseStep 2023559 = 3035339) B3035339
theorem B2276509 : Blo 2023435 2276509 := bbase (se 3 (by rfl) ⟨426845, by rfl⟩ : syracuseStep 2276509 = 853691) (by norm_num)
theorem B3035345 : Blo 2023435 3035345 := bstep (se 2 (by rfl) ⟨1138254, by rfl⟩ : syracuseStep 3035345 = 2276509) B2276509
theorem B2023563 : Blo 2023435 2023563 := bstep (se 1 (by rfl) ⟨1517672, by rfl⟩ : syracuseStep 2023563 = 3035345) B3035345
theorem B6829541 : Blo 2023435 6829541 := bbase (se 4 (by rfl) ⟨640269, by rfl⟩ : syracuseStep 6829541 = 1280539) (by norm_num)
theorem B4553027 : Blo 2023435 4553027 := bstep (se 1 (by rfl) ⟨3414770, by rfl⟩ : syracuseStep 4553027 = 6829541) B6829541
theorem B3035351 : Blo 2023435 3035351 := bstep (se 1 (by rfl) ⟨2276513, by rfl⟩ : syracuseStep 3035351 = 4553027) B4553027
theorem B2023567 : Blo 2023435 2023567 := bstep (se 1 (by rfl) ⟨1517675, by rfl⟩ : syracuseStep 2023567 = 3035351) B3035351
theorem B3035357 : Blo 2023435 3035357 := bbase (se 3 (by rfl) ⟨569129, by rfl⟩ : syracuseStep 3035357 = 1138259) (by norm_num)
theorem B2023571 : Blo 2023435 2023571 := bstep (se 1 (by rfl) ⟨1517678, by rfl⟩ : syracuseStep 2023571 = 3035357) B3035357
theorem B4553045 : Blo 2023435 4553045 := bbase (se 10 (by rfl) ⟨6669, by rfl⟩ : syracuseStep 4553045 = 13339) (by norm_num)
theorem B3035363 : Blo 2023435 3035363 := bstep (se 1 (by rfl) ⟨2276522, by rfl⟩ : syracuseStep 3035363 = 4553045) B4553045
theorem B2023575 : Blo 2023435 2023575 := bstep (se 1 (by rfl) ⟨1517681, by rfl⟩ : syracuseStep 2023575 = 3035363) B3035363
theorem B3118765 : Blo 2023435 3118765 := bbase (se 3 (by rfl) ⟨584768, by rfl⟩ : syracuseStep 3118765 = 1169537) (by norm_num)
theorem B4158353 : Blo 2023435 4158353 := bstep (se 2 (by rfl) ⟨1559382, by rfl⟩ : syracuseStep 4158353 = 3118765) B3118765
theorem B2772235 : Blo 2023435 2772235 := bstep (se 1 (by rfl) ⟨2079176, by rfl⟩ : syracuseStep 2772235 = 4158353) B4158353
theorem B3696313 : Blo 2023435 3696313 := bstep (se 2 (by rfl) ⟨1386117, by rfl⟩ : syracuseStep 3696313 = 2772235) B2772235
theorem B4928417 : Blo 2023435 4928417 := bstep (se 2 (by rfl) ⟨1848156, by rfl⟩ : syracuseStep 4928417 = 3696313) B3696313
theorem B3285611 : Blo 2023435 3285611 := bstep (se 1 (by rfl) ⟨2464208, by rfl⟩ : syracuseStep 3285611 = 4928417) B4928417
theorem B2190407 : Blo 2023435 2190407 := bstep (se 1 (by rfl) ⟨1642805, by rfl⟩ : syracuseStep 2190407 = 3285611) B3285611
theorem B5841085 : Blo 2023435 5841085 := bstep (se 3 (by rfl) ⟨1095203, by rfl⟩ : syracuseStep 5841085 = 2190407) B2190407
theorem B7788113 : Blo 2023435 7788113 := bstep (se 2 (by rfl) ⟨2920542, by rfl⟩ : syracuseStep 7788113 = 5841085) B5841085
theorem B5192075 : Blo 2023435 5192075 := bstep (se 1 (by rfl) ⟨3894056, by rfl⟩ : syracuseStep 5192075 = 7788113) B7788113
theorem B3461383 : Blo 2023435 3461383 := bstep (se 1 (by rfl) ⟨2596037, by rfl⟩ : syracuseStep 3461383 = 5192075) B5192075
theorem B18460709 : Blo 2023435 18460709 := bstep (se 4 (by rfl) ⟨1730691, by rfl⟩ : syracuseStep 18460709 = 3461383) B3461383
theorem B12307139 : Blo 2023435 12307139 := bstep (se 1 (by rfl) ⟨9230354, by rfl⟩ : syracuseStep 12307139 = 18460709) B18460709
theorem B8204759 : Blo 2023435 8204759 := bstep (se 1 (by rfl) ⟨6153569, by rfl⟩ : syracuseStep 8204759 = 12307139) B12307139
theorem B5469839 : Blo 2023435 5469839 := bstep (se 1 (by rfl) ⟨4102379, by rfl⟩ : syracuseStep 5469839 = 8204759) B8204759
theorem B3646559 : Blo 2023435 3646559 := bstep (se 1 (by rfl) ⟨2734919, by rfl⟩ : syracuseStep 3646559 = 5469839) B5469839
theorem B2431039 : Blo 2023435 2431039 := bstep (se 1 (by rfl) ⟨1823279, by rfl⟩ : syracuseStep 2431039 = 3646559) B3646559
theorem B3241385 : Blo 2023435 3241385 := bstep (se 2 (by rfl) ⟨1215519, by rfl⟩ : syracuseStep 3241385 = 2431039) B2431039
theorem B2160923 : Blo 2023435 2160923 := bstep (se 1 (by rfl) ⟨1620692, by rfl⟩ : syracuseStep 2160923 = 3241385) B3241385
theorem B5762461 : Blo 2023435 5762461 := bstep (se 3 (by rfl) ⟨1080461, by rfl⟩ : syracuseStep 5762461 = 2160923) B2160923
theorem B7683281 : Blo 2023435 7683281 := bstep (se 2 (by rfl) ⟨2881230, by rfl⟩ : syracuseStep 7683281 = 5762461) B5762461
theorem B5122187 : Blo 2023435 5122187 := bstep (se 1 (by rfl) ⟨3841640, by rfl⟩ : syracuseStep 5122187 = 7683281) B7683281
theorem B3414791 : Blo 2023435 3414791 := bstep (se 1 (by rfl) ⟨2561093, by rfl⟩ : syracuseStep 3414791 = 5122187) B5122187
theorem B2276527 : Blo 2023435 2276527 := bstep (se 1 (by rfl) ⟨1707395, by rfl⟩ : syracuseStep 2276527 = 3414791) B3414791
theorem B3035369 : Blo 2023435 3035369 := bstep (se 2 (by rfl) ⟨1138263, by rfl⟩ : syracuseStep 3035369 = 2276527) B2276527
theorem B2023579 : Blo 2023435 2023579 := bstep (se 1 (by rfl) ⟨1517684, by rfl⟩ : syracuseStep 2023579 = 3035369) B3035369
theorem B3076789 : Blo 2023435 3076789 := bbase (se 5 (by rfl) ⟨144224, by rfl⟩ : syracuseStep 3076789 = 288449) (by norm_num)
theorem B4102385 : Blo 2023435 4102385 := bstep (se 2 (by rfl) ⟨1538394, by rfl⟩ : syracuseStep 4102385 = 3076789) B3076789
theorem B10939693 : Blo 2023435 10939693 := bstep (se 3 (by rfl) ⟨2051192, by rfl⟩ : syracuseStep 10939693 = 4102385) B4102385
theorem B14586257 : Blo 2023435 14586257 := bstep (se 2 (by rfl) ⟨5469846, by rfl⟩ : syracuseStep 14586257 = 10939693) B10939693
theorem B38896685 : Blo 2023435 38896685 := bstep (se 3 (by rfl) ⟨7293128, by rfl⟩ : syracuseStep 38896685 = 14586257) B14586257
theorem B25931123 : Blo 2023435 25931123 := bstep (se 1 (by rfl) ⟨19448342, by rfl⟩ : syracuseStep 25931123 = 38896685) B38896685
theorem B17287415 : Blo 2023435 17287415 := bstep (se 1 (by rfl) ⟨12965561, by rfl⟩ : syracuseStep 17287415 = 25931123) B25931123
theorem B11524943 : Blo 2023435 11524943 := bstep (se 1 (by rfl) ⟨8643707, by rfl⟩ : syracuseStep 11524943 = 17287415) B17287415
theorem B7683295 : Blo 2023435 7683295 := bstep (se 1 (by rfl) ⟨5762471, by rfl⟩ : syracuseStep 7683295 = 11524943) B11524943
theorem B10244393 : Blo 2023435 10244393 := bstep (se 2 (by rfl) ⟨3841647, by rfl⟩ : syracuseStep 10244393 = 7683295) B7683295
theorem B6829595 : Blo 2023435 6829595 := bstep (se 1 (by rfl) ⟨5122196, by rfl⟩ : syracuseStep 6829595 = 10244393) B10244393
theorem B4553063 : Blo 2023435 4553063 := bstep (se 1 (by rfl) ⟨3414797, by rfl⟩ : syracuseStep 4553063 = 6829595) B6829595
theorem B3035375 : Blo 2023435 3035375 := bstep (se 1 (by rfl) ⟨2276531, by rfl⟩ : syracuseStep 3035375 = 4553063) B4553063
theorem B2023583 : Blo 2023435 2023583 := bstep (se 1 (by rfl) ⟨1517687, by rfl⟩ : syracuseStep 2023583 = 3035375) B3035375
theorem B3035381 : Blo 2023435 3035381 := bbase (se 5 (by rfl) ⟨142283, by rfl⟩ : syracuseStep 3035381 = 284567) (by norm_num)
theorem B2023587 : Blo 2023435 2023587 := bstep (se 1 (by rfl) ⟨1517690, by rfl⟩ : syracuseStep 2023587 = 3035381) B3035381
theorem B3894077 : Blo 2023435 3894077 := bbase (se 3 (by rfl) ⟨730139, by rfl⟩ : syracuseStep 3894077 = 1460279) (by norm_num)
theorem B10384205 : Blo 2023435 10384205 := bstep (se 3 (by rfl) ⟨1947038, by rfl⟩ : syracuseStep 10384205 = 3894077) B3894077
theorem B110764853 : Blo 2023435 110764853 := bstep (se 5 (by rfl) ⟨5192102, by rfl⟩ : syracuseStep 110764853 = 10384205) B10384205
theorem B73843235 : Blo 2023435 73843235 := bstep (se 1 (by rfl) ⟨55382426, by rfl⟩ : syracuseStep 73843235 = 110764853) B110764853
theorem B49228823 : Blo 2023435 49228823 := bstep (se 1 (by rfl) ⟨36921617, by rfl⟩ : syracuseStep 49228823 = 73843235) B73843235
theorem B32819215 : Blo 2023435 32819215 := bstep (se 1 (by rfl) ⟨24614411, by rfl⟩ : syracuseStep 32819215 = 49228823) B49228823
theorem B43758953 : Blo 2023435 43758953 := bstep (se 2 (by rfl) ⟨16409607, by rfl⟩ : syracuseStep 43758953 = 32819215) B32819215
theorem B29172635 : Blo 2023435 29172635 := bstep (se 1 (by rfl) ⟨21879476, by rfl⟩ : syracuseStep 29172635 = 43758953) B43758953
theorem B19448423 : Blo 2023435 19448423 := bstep (se 1 (by rfl) ⟨14586317, by rfl⟩ : syracuseStep 19448423 = 29172635) B29172635
theorem B12965615 : Blo 2023435 12965615 := bstep (se 1 (by rfl) ⟨9724211, by rfl⟩ : syracuseStep 12965615 = 19448423) B19448423
theorem B8643743 : Blo 2023435 8643743 := bstep (se 1 (by rfl) ⟨6482807, by rfl⟩ : syracuseStep 8643743 = 12965615) B12965615
theorem B5762495 : Blo 2023435 5762495 := bstep (se 1 (by rfl) ⟨4321871, by rfl⟩ : syracuseStep 5762495 = 8643743) B8643743
theorem B3841663 : Blo 2023435 3841663 := bstep (se 1 (by rfl) ⟨2881247, by rfl⟩ : syracuseStep 3841663 = 5762495) B5762495
theorem B5122217 : Blo 2023435 5122217 := bstep (se 2 (by rfl) ⟨1920831, by rfl⟩ : syracuseStep 5122217 = 3841663) B3841663
theorem B3414811 : Blo 2023435 3414811 := bstep (se 1 (by rfl) ⟨2561108, by rfl⟩ : syracuseStep 3414811 = 5122217) B5122217
theorem B4553081 : Blo 2023435 4553081 := bstep (se 2 (by rfl) ⟨1707405, by rfl⟩ : syracuseStep 4553081 = 3414811) B3414811
theorem B3035387 : Blo 2023435 3035387 := bstep (se 1 (by rfl) ⟨2276540, by rfl⟩ : syracuseStep 3035387 = 4553081) B4553081
theorem B2023591 : Blo 2023435 2023591 := bstep (se 1 (by rfl) ⟨1517693, by rfl⟩ : syracuseStep 2023591 = 3035387) B3035387
theorem B2276545 : Blo 2023435 2276545 := bbase (se 2 (by rfl) ⟨853704, by rfl⟩ : syracuseStep 2276545 = 1707409) (by norm_num)
theorem B3035393 : Blo 2023435 3035393 := bstep (se 2 (by rfl) ⟨1138272, by rfl⟩ : syracuseStep 3035393 = 2276545) B2276545
theorem B2023595 : Blo 2023435 2023595 := bstep (se 1 (by rfl) ⟨1517696, by rfl⟩ : syracuseStep 2023595 = 3035393) B3035393
theorem B5122237 : Blo 2023435 5122237 := bbase (se 3 (by rfl) ⟨960419, by rfl⟩ : syracuseStep 5122237 = 1920839) (by norm_num)
theorem B6829649 : Blo 2023435 6829649 := bstep (se 2 (by rfl) ⟨2561118, by rfl⟩ : syracuseStep 6829649 = 5122237) B5122237
theorem B4553099 : Blo 2023435 4553099 := bstep (se 1 (by rfl) ⟨3414824, by rfl⟩ : syracuseStep 4553099 = 6829649) B6829649
theorem B3035399 : Blo 2023435 3035399 := bstep (se 1 (by rfl) ⟨2276549, by rfl⟩ : syracuseStep 3035399 = 4553099) B4553099
theorem B2023599 : Blo 2023435 2023599 := bstep (se 1 (by rfl) ⟨1517699, by rfl⟩ : syracuseStep 2023599 = 3035399) B3035399
theorem B3035405 : Blo 2023435 3035405 := bbase (se 3 (by rfl) ⟨569138, by rfl⟩ : syracuseStep 3035405 = 1138277) (by norm_num)
theorem B2023603 : Blo 2023435 2023603 := bstep (se 1 (by rfl) ⟨1517702, by rfl⟩ : syracuseStep 2023603 = 3035405) B3035405
theorem B4553117 : Blo 2023435 4553117 := bbase (se 3 (by rfl) ⟨853709, by rfl⟩ : syracuseStep 4553117 = 1707419) (by norm_num)
theorem B3035411 : Blo 2023435 3035411 := bstep (se 1 (by rfl) ⟨2276558, by rfl⟩ : syracuseStep 3035411 = 4553117) B4553117
theorem B2023607 : Blo 2023435 2023607 := bstep (se 1 (by rfl) ⟨1517705, by rfl⟩ : syracuseStep 2023607 = 3035411) B3035411
theorem B3414845 : Blo 2023435 3414845 := bbase (se 3 (by rfl) ⟨640283, by rfl⟩ : syracuseStep 3414845 = 1280567) (by norm_num)
theorem B2276563 : Blo 2023435 2276563 := bstep (se 1 (by rfl) ⟨1707422, by rfl⟩ : syracuseStep 2276563 = 3414845) B3414845
theorem B3035417 : Blo 2023435 3035417 := bstep (se 2 (by rfl) ⟨1138281, by rfl⟩ : syracuseStep 3035417 = 2276563) B2276563
theorem B2023611 : Blo 2023435 2023611 := bstep (se 1 (by rfl) ⟨1517708, by rfl⟩ : syracuseStep 2023611 = 3035417) B3035417
theorem B2160961 : Blo 2023435 2160961 := bbase (se 2 (by rfl) ⟨810360, by rfl⟩ : syracuseStep 2160961 = 1620721) (by norm_num)
theorem B11525125 : Blo 2023435 11525125 := bstep (se 4 (by rfl) ⟨1080480, by rfl⟩ : syracuseStep 11525125 = 2160961) B2160961
theorem B15366833 : Blo 2023435 15366833 := bstep (se 2 (by rfl) ⟨5762562, by rfl⟩ : syracuseStep 15366833 = 11525125) B11525125
theorem B10244555 : Blo 2023435 10244555 := bstep (se 1 (by rfl) ⟨7683416, by rfl⟩ : syracuseStep 10244555 = 15366833) B15366833
theorem B6829703 : Blo 2023435 6829703 := bstep (se 1 (by rfl) ⟨5122277, by rfl⟩ : syracuseStep 6829703 = 10244555) B10244555
theorem B4553135 : Blo 2023435 4553135 := bstep (se 1 (by rfl) ⟨3414851, by rfl⟩ : syracuseStep 4553135 = 6829703) B6829703
theorem B3035423 : Blo 2023435 3035423 := bstep (se 1 (by rfl) ⟨2276567, by rfl⟩ : syracuseStep 3035423 = 4553135) B4553135
theorem B2023615 : Blo 2023435 2023615 := bstep (se 1 (by rfl) ⟨1517711, by rfl⟩ : syracuseStep 2023615 = 3035423) B3035423
theorem B3035429 : Blo 2023435 3035429 := bbase (se 4 (by rfl) ⟨284571, by rfl⟩ : syracuseStep 3035429 = 569143) (by norm_num)
theorem B2023619 : Blo 2023435 2023619 := bstep (se 1 (by rfl) ⟨1517714, by rfl⟩ : syracuseStep 2023619 = 3035429) B3035429
theorem B2561149 : Blo 2023435 2561149 := bbase (se 3 (by rfl) ⟨480215, by rfl⟩ : syracuseStep 2561149 = 960431) (by norm_num)
theorem B3414865 : Blo 2023435 3414865 := bstep (se 2 (by rfl) ⟨1280574, by rfl⟩ : syracuseStep 3414865 = 2561149) B2561149
theorem B4553153 : Blo 2023435 4553153 := bstep (se 2 (by rfl) ⟨1707432, by rfl⟩ : syracuseStep 4553153 = 3414865) B3414865
theorem B3035435 : Blo 2023435 3035435 := bstep (se 1 (by rfl) ⟨2276576, by rfl⟩ : syracuseStep 3035435 = 4553153) B4553153
theorem B2023623 : Blo 2023435 2023623 := bstep (se 1 (by rfl) ⟨1517717, by rfl⟩ : syracuseStep 2023623 = 3035435) B3035435
theorem B2276581 : Blo 2023435 2276581 := bbase (se 4 (by rfl) ⟨213429, by rfl⟩ : syracuseStep 2276581 = 426859) (by norm_num)
theorem B3035441 : Blo 2023435 3035441 := bstep (se 2 (by rfl) ⟨1138290, by rfl⟩ : syracuseStep 3035441 = 2276581) B2276581
theorem B2023627 : Blo 2023435 2023627 := bstep (se 1 (by rfl) ⟨1517720, by rfl⟩ : syracuseStep 2023627 = 3035441) B3035441
theorem B4321957 : Blo 2023435 4321957 := bbase (se 4 (by rfl) ⟨405183, by rfl⟩ : syracuseStep 4321957 = 810367) (by norm_num)
theorem B5762609 : Blo 2023435 5762609 := bstep (se 2 (by rfl) ⟨2160978, by rfl⟩ : syracuseStep 5762609 = 4321957) B4321957
theorem B3841739 : Blo 2023435 3841739 := bstep (se 1 (by rfl) ⟨2881304, by rfl⟩ : syracuseStep 3841739 = 5762609) B5762609
theorem B2561159 : Blo 2023435 2561159 := bstep (se 1 (by rfl) ⟨1920869, by rfl⟩ : syracuseStep 2561159 = 3841739) B3841739
theorem B6829757 : Blo 2023435 6829757 := bstep (se 3 (by rfl) ⟨1280579, by rfl⟩ : syracuseStep 6829757 = 2561159) B2561159
theorem B4553171 : Blo 2023435 4553171 := bstep (se 1 (by rfl) ⟨3414878, by rfl⟩ : syracuseStep 4553171 = 6829757) B6829757
theorem B3035447 : Blo 2023435 3035447 := bstep (se 1 (by rfl) ⟨2276585, by rfl⟩ : syracuseStep 3035447 = 4553171) B4553171
theorem B2023631 : Blo 2023435 2023631 := bstep (se 1 (by rfl) ⟨1517723, by rfl⟩ : syracuseStep 2023631 = 3035447) B3035447
theorem B3035453 : Blo 2023435 3035453 := bbase (se 3 (by rfl) ⟨569147, by rfl⟩ : syracuseStep 3035453 = 1138295) (by norm_num)
theorem B2023635 : Blo 2023435 2023635 := bstep (se 1 (by rfl) ⟨1517726, by rfl⟩ : syracuseStep 2023635 = 3035453) B3035453
theorem B4553189 : Blo 2023435 4553189 := bbase (se 4 (by rfl) ⟨426861, by rfl⟩ : syracuseStep 4553189 = 853723) (by norm_num)
theorem B3035459 : Blo 2023435 3035459 := bstep (se 1 (by rfl) ⟨2276594, by rfl⟩ : syracuseStep 3035459 = 4553189) B4553189
theorem B2023639 : Blo 2023435 2023639 := bstep (se 1 (by rfl) ⟨1517729, by rfl⟩ : syracuseStep 2023639 = 3035459) B3035459
theorem B5122349 : Blo 2023435 5122349 := bbase (se 3 (by rfl) ⟨960440, by rfl⟩ : syracuseStep 5122349 = 1920881) (by norm_num)
theorem B3414899 : Blo 2023435 3414899 := bstep (se 1 (by rfl) ⟨2561174, by rfl⟩ : syracuseStep 3414899 = 5122349) B5122349
theorem B2276599 : Blo 2023435 2276599 := bstep (se 1 (by rfl) ⟨1707449, by rfl⟩ : syracuseStep 2276599 = 3414899) B3414899
theorem B3035465 : Blo 2023435 3035465 := bstep (se 2 (by rfl) ⟨1138299, by rfl⟩ : syracuseStep 3035465 = 2276599) B2276599
theorem B2023643 : Blo 2023435 2023643 := bstep (se 1 (by rfl) ⟨1517732, by rfl⟩ : syracuseStep 2023643 = 3035465) B3035465
theorem B5470021 : Blo 2023435 5470021 := bbase (se 4 (by rfl) ⟨512814, by rfl⟩ : syracuseStep 5470021 = 1025629) (by norm_num)
theorem B7293361 : Blo 2023435 7293361 := bstep (se 2 (by rfl) ⟨2735010, by rfl⟩ : syracuseStep 7293361 = 5470021) B5470021
theorem B9724481 : Blo 2023435 9724481 := bstep (se 2 (by rfl) ⟨3646680, by rfl⟩ : syracuseStep 9724481 = 7293361) B7293361
theorem B6482987 : Blo 2023435 6482987 := bstep (se 1 (by rfl) ⟨4862240, by rfl⟩ : syracuseStep 6482987 = 9724481) B9724481
theorem B4321991 : Blo 2023435 4321991 := bstep (se 1 (by rfl) ⟨3241493, by rfl⟩ : syracuseStep 4321991 = 6482987) B6482987
theorem B2881327 : Blo 2023435 2881327 := bstep (se 1 (by rfl) ⟨2160995, by rfl⟩ : syracuseStep 2881327 = 4321991) B4321991
theorem B3841769 : Blo 2023435 3841769 := bstep (se 2 (by rfl) ⟨1440663, by rfl⟩ : syracuseStep 3841769 = 2881327) B2881327
theorem B10244717 : Blo 2023435 10244717 := bstep (se 3 (by rfl) ⟨1920884, by rfl⟩ : syracuseStep 10244717 = 3841769) B3841769
theorem B6829811 : Blo 2023435 6829811 := bstep (se 1 (by rfl) ⟨5122358, by rfl⟩ : syracuseStep 6829811 = 10244717) B10244717
theorem B4553207 : Blo 2023435 4553207 := bstep (se 1 (by rfl) ⟨3414905, by rfl⟩ : syracuseStep 4553207 = 6829811) B6829811
theorem B3035471 : Blo 2023435 3035471 := bstep (se 1 (by rfl) ⟨2276603, by rfl⟩ : syracuseStep 3035471 = 4553207) B4553207
theorem B2023647 : Blo 2023435 2023647 := bstep (se 1 (by rfl) ⟨1517735, by rfl⟩ : syracuseStep 2023647 = 3035471) B3035471
theorem B3035477 : Blo 2023435 3035477 := bbase (se 10 (by rfl) ⟨4446, by rfl⟩ : syracuseStep 3035477 = 8893) (by norm_num)
theorem B2023651 : Blo 2023435 2023651 := bstep (se 1 (by rfl) ⟨1517738, by rfl⟩ : syracuseStep 2023651 = 3035477) B3035477
theorem B5762677 : Blo 2023435 5762677 := bbase (se 5 (by rfl) ⟨270125, by rfl⟩ : syracuseStep 5762677 = 540251) (by norm_num)
theorem B7683569 : Blo 2023435 7683569 := bstep (se 2 (by rfl) ⟨2881338, by rfl⟩ : syracuseStep 7683569 = 5762677) B5762677
theorem B5122379 : Blo 2023435 5122379 := bstep (se 1 (by rfl) ⟨3841784, by rfl⟩ : syracuseStep 5122379 = 7683569) B7683569
theorem B3414919 : Blo 2023435 3414919 := bstep (se 1 (by rfl) ⟨2561189, by rfl⟩ : syracuseStep 3414919 = 5122379) B5122379
theorem B4553225 : Blo 2023435 4553225 := bstep (se 2 (by rfl) ⟨1707459, by rfl⟩ : syracuseStep 4553225 = 3414919) B3414919
theorem B3035483 : Blo 2023435 3035483 := bstep (se 1 (by rfl) ⟨2276612, by rfl⟩ : syracuseStep 3035483 = 4553225) B4553225
theorem B2023655 : Blo 2023435 2023655 := bstep (se 1 (by rfl) ⟨1517741, by rfl⟩ : syracuseStep 2023655 = 3035483) B3035483
theorem B2276617 : Blo 2023435 2276617 := bbase (se 2 (by rfl) ⟨853731, by rfl⟩ : syracuseStep 2276617 = 1707463) (by norm_num)
theorem B3035489 : Blo 2023435 3035489 := bstep (se 2 (by rfl) ⟨1138308, by rfl⟩ : syracuseStep 3035489 = 2276617) B2276617
theorem B2023659 : Blo 2023435 2023659 := bstep (se 1 (by rfl) ⟨1517744, by rfl⟩ : syracuseStep 2023659 = 3035489) B3035489
theorem B3646709 : Blo 2023435 3646709 := bbase (se 5 (by rfl) ⟨170939, by rfl⟩ : syracuseStep 3646709 = 341879) (by norm_num)
theorem B2431139 : Blo 2023435 2431139 := bstep (se 1 (by rfl) ⟨1823354, by rfl⟩ : syracuseStep 2431139 = 3646709) B3646709
theorem B25932149 : Blo 2023435 25932149 := bstep (se 5 (by rfl) ⟨1215569, by rfl⟩ : syracuseStep 25932149 = 2431139) B2431139
theorem B17288099 : Blo 2023435 17288099 := bstep (se 1 (by rfl) ⟨12966074, by rfl⟩ : syracuseStep 17288099 = 25932149) B25932149
theorem B11525399 : Blo 2023435 11525399 := bstep (se 1 (by rfl) ⟨8644049, by rfl⟩ : syracuseStep 11525399 = 17288099) B17288099
theorem B7683599 : Blo 2023435 7683599 := bstep (se 1 (by rfl) ⟨5762699, by rfl⟩ : syracuseStep 7683599 = 11525399) B11525399
theorem B5122399 : Blo 2023435 5122399 := bstep (se 1 (by rfl) ⟨3841799, by rfl⟩ : syracuseStep 5122399 = 7683599) B7683599
theorem B6829865 : Blo 2023435 6829865 := bstep (se 2 (by rfl) ⟨2561199, by rfl⟩ : syracuseStep 6829865 = 5122399) B5122399
theorem B4553243 : Blo 2023435 4553243 := bstep (se 1 (by rfl) ⟨3414932, by rfl⟩ : syracuseStep 4553243 = 6829865) B6829865
theorem B3035495 : Blo 2023435 3035495 := bstep (se 1 (by rfl) ⟨2276621, by rfl⟩ : syracuseStep 3035495 = 4553243) B4553243
theorem B2023663 : Blo 2023435 2023663 := bstep (se 1 (by rfl) ⟨1517747, by rfl⟩ : syracuseStep 2023663 = 3035495) B3035495
theorem B3035501 : Blo 2023435 3035501 := bbase (se 3 (by rfl) ⟨569156, by rfl⟩ : syracuseStep 3035501 = 1138313) (by norm_num)
theorem B2023667 : Blo 2023435 2023667 := bstep (se 1 (by rfl) ⟨1517750, by rfl⟩ : syracuseStep 2023667 = 3035501) B3035501
theorem B4553261 : Blo 2023435 4553261 := bbase (se 3 (by rfl) ⟨853736, by rfl⟩ : syracuseStep 4553261 = 1707473) (by norm_num)
theorem B3035507 : Blo 2023435 3035507 := bstep (se 1 (by rfl) ⟨2276630, by rfl⟩ : syracuseStep 3035507 = 4553261) B4553261
theorem B2023671 : Blo 2023435 2023671 := bstep (se 1 (by rfl) ⟨1517753, by rfl⟩ : syracuseStep 2023671 = 3035507) B3035507
theorem B4102573 : Blo 2023435 4102573 := bbase (se 3 (by rfl) ⟨769232, by rfl⟩ : syracuseStep 4102573 = 1538465) (by norm_num)
theorem B5470097 : Blo 2023435 5470097 := bstep (se 2 (by rfl) ⟨2051286, by rfl⟩ : syracuseStep 5470097 = 4102573) B4102573
theorem B14586925 : Blo 2023435 14586925 := bstep (se 3 (by rfl) ⟨2735048, by rfl⟩ : syracuseStep 14586925 = 5470097) B5470097
theorem B19449233 : Blo 2023435 19449233 := bstep (se 2 (by rfl) ⟨7293462, by rfl⟩ : syracuseStep 19449233 = 14586925) B14586925
theorem B12966155 : Blo 2023435 12966155 := bstep (se 1 (by rfl) ⟨9724616, by rfl⟩ : syracuseStep 12966155 = 19449233) B19449233
theorem B8644103 : Blo 2023435 8644103 := bstep (se 1 (by rfl) ⟨6483077, by rfl⟩ : syracuseStep 8644103 = 12966155) B12966155
theorem B5762735 : Blo 2023435 5762735 := bstep (se 1 (by rfl) ⟨4322051, by rfl⟩ : syracuseStep 5762735 = 8644103) B8644103
theorem B3841823 : Blo 2023435 3841823 := bstep (se 1 (by rfl) ⟨2881367, by rfl⟩ : syracuseStep 3841823 = 5762735) B5762735
theorem B2561215 : Blo 2023435 2561215 := bstep (se 1 (by rfl) ⟨1920911, by rfl⟩ : syracuseStep 2561215 = 3841823) B3841823
theorem B3414953 : Blo 2023435 3414953 := bstep (se 2 (by rfl) ⟨1280607, by rfl⟩ : syracuseStep 3414953 = 2561215) B2561215
theorem B2276635 : Blo 2023435 2276635 := bstep (se 1 (by rfl) ⟨1707476, by rfl⟩ : syracuseStep 2276635 = 3414953) B3414953
theorem B3035513 : Blo 2023435 3035513 := bstep (se 2 (by rfl) ⟨1138317, by rfl⟩ : syracuseStep 3035513 = 2276635) B2276635
theorem B2023675 : Blo 2023435 2023675 := bstep (se 1 (by rfl) ⟨1517756, by rfl⟩ : syracuseStep 2023675 = 3035513) B3035513
theorem B34576469 : Blo 2023435 34576469 := bbase (se 8 (by rfl) ⟨202596, by rfl⟩ : syracuseStep 34576469 = 405193) (by norm_num)
theorem B23050979 : Blo 2023435 23050979 := bstep (se 1 (by rfl) ⟨17288234, by rfl⟩ : syracuseStep 23050979 = 34576469) B34576469
theorem B15367319 : Blo 2023435 15367319 := bstep (se 1 (by rfl) ⟨11525489, by rfl⟩ : syracuseStep 15367319 = 23050979) B23050979
theorem B10244879 : Blo 2023435 10244879 := bstep (se 1 (by rfl) ⟨7683659, by rfl⟩ : syracuseStep 10244879 = 15367319) B15367319
theorem B6829919 : Blo 2023435 6829919 := bstep (se 1 (by rfl) ⟨5122439, by rfl⟩ : syracuseStep 6829919 = 10244879) B10244879
theorem B4553279 : Blo 2023435 4553279 := bstep (se 1 (by rfl) ⟨3414959, by rfl⟩ : syracuseStep 4553279 = 6829919) B6829919
theorem B3035519 : Blo 2023435 3035519 := bstep (se 1 (by rfl) ⟨2276639, by rfl⟩ : syracuseStep 3035519 = 4553279) B4553279
theorem B2023679 : Blo 2023435 2023679 := bstep (se 1 (by rfl) ⟨1517759, by rfl⟩ : syracuseStep 2023679 = 3035519) B3035519
theorem B3035525 : Blo 2023435 3035525 := bbase (se 4 (by rfl) ⟨284580, by rfl⟩ : syracuseStep 3035525 = 569161) (by norm_num)
theorem B2023683 : Blo 2023435 2023683 := bstep (se 1 (by rfl) ⟨1517762, by rfl⟩ : syracuseStep 2023683 = 3035525) B3035525
theorem B3414973 : Blo 2023435 3414973 := bbase (se 3 (by rfl) ⟨640307, by rfl⟩ : syracuseStep 3414973 = 1280615) (by norm_num)
theorem B4553297 : Blo 2023435 4553297 := bstep (se 2 (by rfl) ⟨1707486, by rfl⟩ : syracuseStep 4553297 = 3414973) B3414973
theorem B3035531 : Blo 2023435 3035531 := bstep (se 1 (by rfl) ⟨2276648, by rfl⟩ : syracuseStep 3035531 = 4553297) B4553297
theorem B2023687 : Blo 2023435 2023687 := bstep (se 1 (by rfl) ⟨1517765, by rfl⟩ : syracuseStep 2023687 = 3035531) B3035531
theorem B2276653 : Blo 2023435 2276653 := bbase (se 3 (by rfl) ⟨426872, by rfl⟩ : syracuseStep 2276653 = 853745) (by norm_num)
theorem B3035537 : Blo 2023435 3035537 := bstep (se 2 (by rfl) ⟨1138326, by rfl⟩ : syracuseStep 3035537 = 2276653) B2276653
theorem B2023691 : Blo 2023435 2023691 := bstep (se 1 (by rfl) ⟨1517768, by rfl⟩ : syracuseStep 2023691 = 3035537) B3035537
theorem B6829973 : Blo 2023435 6829973 := bbase (se 6 (by rfl) ⟨160077, by rfl⟩ : syracuseStep 6829973 = 320155) (by norm_num)
theorem B4553315 : Blo 2023435 4553315 := bstep (se 1 (by rfl) ⟨3414986, by rfl⟩ : syracuseStep 4553315 = 6829973) B6829973
theorem B3035543 : Blo 2023435 3035543 := bstep (se 1 (by rfl) ⟨2276657, by rfl⟩ : syracuseStep 3035543 = 4553315) B4553315
theorem B2023695 : Blo 2023435 2023695 := bstep (se 1 (by rfl) ⟨1517771, by rfl⟩ : syracuseStep 2023695 = 3035543) B3035543
theorem B3035549 : Blo 2023435 3035549 := bbase (se 3 (by rfl) ⟨569165, by rfl⟩ : syracuseStep 3035549 = 1138331) (by norm_num)
theorem B2023699 : Blo 2023435 2023699 := bstep (se 1 (by rfl) ⟨1517774, by rfl⟩ : syracuseStep 2023699 = 3035549) B3035549
theorem B4553333 : Blo 2023435 4553333 := bbase (se 5 (by rfl) ⟨213437, by rfl⟩ : syracuseStep 4553333 = 426875) (by norm_num)
theorem B3035555 : Blo 2023435 3035555 := bstep (se 1 (by rfl) ⟨2276666, by rfl⟩ : syracuseStep 3035555 = 4553333) B4553333
theorem B2023703 : Blo 2023435 2023703 := bstep (se 1 (by rfl) ⟨1517777, by rfl⟩ : syracuseStep 2023703 = 3035555) B3035555
theorem B3894301 : Blo 2023435 3894301 := bbase (se 3 (by rfl) ⟨730181, by rfl⟩ : syracuseStep 3894301 = 1460363) (by norm_num)
theorem B20769605 : Blo 2023435 20769605 := bstep (se 4 (by rfl) ⟨1947150, by rfl⟩ : syracuseStep 20769605 = 3894301) B3894301
theorem B13846403 : Blo 2023435 13846403 := bstep (se 1 (by rfl) ⟨10384802, by rfl⟩ : syracuseStep 13846403 = 20769605) B20769605
theorem B9230935 : Blo 2023435 9230935 := bstep (se 1 (by rfl) ⟨6923201, by rfl⟩ : syracuseStep 9230935 = 13846403) B13846403
theorem B12307913 : Blo 2023435 12307913 := bstep (se 2 (by rfl) ⟨4615467, by rfl⟩ : syracuseStep 12307913 = 9230935) B9230935
theorem B8205275 : Blo 2023435 8205275 := bstep (se 1 (by rfl) ⟨6153956, by rfl⟩ : syracuseStep 8205275 = 12307913) B12307913
theorem B5470183 : Blo 2023435 5470183 := bstep (se 1 (by rfl) ⟨4102637, by rfl⟩ : syracuseStep 5470183 = 8205275) B8205275
theorem B7293577 : Blo 2023435 7293577 := bstep (se 2 (by rfl) ⟨2735091, by rfl⟩ : syracuseStep 7293577 = 5470183) B5470183
theorem B9724769 : Blo 2023435 9724769 := bstep (se 2 (by rfl) ⟨3646788, by rfl⟩ : syracuseStep 9724769 = 7293577) B7293577
theorem B6483179 : Blo 2023435 6483179 := bstep (se 1 (by rfl) ⟨4862384, by rfl⟩ : syracuseStep 6483179 = 9724769) B9724769
theorem B17288477 : Blo 2023435 17288477 := bstep (se 3 (by rfl) ⟨3241589, by rfl⟩ : syracuseStep 17288477 = 6483179) B6483179
theorem B11525651 : Blo 2023435 11525651 := bstep (se 1 (by rfl) ⟨8644238, by rfl⟩ : syracuseStep 11525651 = 17288477) B17288477
theorem B7683767 : Blo 2023435 7683767 := bstep (se 1 (by rfl) ⟨5762825, by rfl⟩ : syracuseStep 7683767 = 11525651) B11525651
theorem B5122511 : Blo 2023435 5122511 := bstep (se 1 (by rfl) ⟨3841883, by rfl⟩ : syracuseStep 5122511 = 7683767) B7683767
theorem B3415007 : Blo 2023435 3415007 := bstep (se 1 (by rfl) ⟨2561255, by rfl⟩ : syracuseStep 3415007 = 5122511) B5122511
theorem B2276671 : Blo 2023435 2276671 := bstep (se 1 (by rfl) ⟨1707503, by rfl⟩ : syracuseStep 2276671 = 3415007) B3415007
theorem B3035561 : Blo 2023435 3035561 := bstep (se 2 (by rfl) ⟨1138335, by rfl⟩ : syracuseStep 3035561 = 2276671) B2276671
theorem B2023707 : Blo 2023435 2023707 := bstep (se 1 (by rfl) ⟨1517780, by rfl⟩ : syracuseStep 2023707 = 3035561) B3035561
theorem B7683781 : Blo 2023435 7683781 := bbase (se 4 (by rfl) ⟨720354, by rfl⟩ : syracuseStep 7683781 = 1440709) (by norm_num)
theorem B10245041 : Blo 2023435 10245041 := bstep (se 2 (by rfl) ⟨3841890, by rfl⟩ : syracuseStep 10245041 = 7683781) B7683781
theorem B6830027 : Blo 2023435 6830027 := bstep (se 1 (by rfl) ⟨5122520, by rfl⟩ : syracuseStep 6830027 = 10245041) B10245041
theorem B4553351 : Blo 2023435 4553351 := bstep (se 1 (by rfl) ⟨3415013, by rfl⟩ : syracuseStep 4553351 = 6830027) B6830027
theorem B3035567 : Blo 2023435 3035567 := bstep (se 1 (by rfl) ⟨2276675, by rfl⟩ : syracuseStep 3035567 = 4553351) B4553351
theorem B2023711 : Blo 2023435 2023711 := bstep (se 1 (by rfl) ⟨1517783, by rfl⟩ : syracuseStep 2023711 = 3035567) B3035567
theorem B3035573 : Blo 2023435 3035573 := bbase (se 5 (by rfl) ⟨142292, by rfl⟩ : syracuseStep 3035573 = 284585) (by norm_num)
theorem B2023715 : Blo 2023435 2023715 := bstep (se 1 (by rfl) ⟨1517786, by rfl⟩ : syracuseStep 2023715 = 3035573) B3035573
theorem B5122541 : Blo 2023435 5122541 := bbase (se 3 (by rfl) ⟨960476, by rfl⟩ : syracuseStep 5122541 = 1920953) (by norm_num)
theorem B3415027 : Blo 2023435 3415027 := bstep (se 1 (by rfl) ⟨2561270, by rfl⟩ : syracuseStep 3415027 = 5122541) B5122541
theorem B4553369 : Blo 2023435 4553369 := bstep (se 2 (by rfl) ⟨1707513, by rfl⟩ : syracuseStep 4553369 = 3415027) B3415027
theorem B3035579 : Blo 2023435 3035579 := bstep (se 1 (by rfl) ⟨2276684, by rfl⟩ : syracuseStep 3035579 = 4553369) B4553369
theorem B2023719 : Blo 2023435 2023719 := bstep (se 1 (by rfl) ⟨1517789, by rfl⟩ : syracuseStep 2023719 = 3035579) B3035579
theorem B2276689 : Blo 2023435 2276689 := bbase (se 2 (by rfl) ⟨853758, by rfl⟩ : syracuseStep 2276689 = 1707517) (by norm_num)
theorem B3035585 : Blo 2023435 3035585 := bstep (se 2 (by rfl) ⟨1138344, by rfl⟩ : syracuseStep 3035585 = 2276689) B2276689
theorem B2023723 : Blo 2023435 2023723 := bstep (se 1 (by rfl) ⟨1517792, by rfl⟩ : syracuseStep 2023723 = 3035585) B3035585
theorem B2161081 : Blo 2023435 2161081 := bbase (se 2 (by rfl) ⟨810405, by rfl⟩ : syracuseStep 2161081 = 1620811) (by norm_num)
theorem B2881441 : Blo 2023435 2881441 := bstep (se 2 (by rfl) ⟨1080540, by rfl⟩ : syracuseStep 2881441 = 2161081) B2161081
theorem B3841921 : Blo 2023435 3841921 := bstep (se 2 (by rfl) ⟨1440720, by rfl⟩ : syracuseStep 3841921 = 2881441) B2881441
theorem B5122561 : Blo 2023435 5122561 := bstep (se 2 (by rfl) ⟨1920960, by rfl⟩ : syracuseStep 5122561 = 3841921) B3841921
theorem B6830081 : Blo 2023435 6830081 := bstep (se 2 (by rfl) ⟨2561280, by rfl⟩ : syracuseStep 6830081 = 5122561) B5122561
theorem B4553387 : Blo 2023435 4553387 := bstep (se 1 (by rfl) ⟨3415040, by rfl⟩ : syracuseStep 4553387 = 6830081) B6830081
theorem B3035591 : Blo 2023435 3035591 := bstep (se 1 (by rfl) ⟨2276693, by rfl⟩ : syracuseStep 3035591 = 4553387) B4553387
theorem B2023727 : Blo 2023435 2023727 := bstep (se 1 (by rfl) ⟨1517795, by rfl⟩ : syracuseStep 2023727 = 3035591) B3035591
theorem B3035597 : Blo 2023435 3035597 := bbase (se 3 (by rfl) ⟨569174, by rfl⟩ : syracuseStep 3035597 = 1138349) (by norm_num)
theorem B2023731 : Blo 2023435 2023731 := bstep (se 1 (by rfl) ⟨1517798, by rfl⟩ : syracuseStep 2023731 = 3035597) B3035597
theorem B4553405 : Blo 2023435 4553405 := bbase (se 3 (by rfl) ⟨853763, by rfl⟩ : syracuseStep 4553405 = 1707527) (by norm_num)
theorem B3035603 : Blo 2023435 3035603 := bstep (se 1 (by rfl) ⟨2276702, by rfl⟩ : syracuseStep 3035603 = 4553405) B4553405
theorem B2023735 : Blo 2023435 2023735 := bstep (se 1 (by rfl) ⟨1517801, by rfl⟩ : syracuseStep 2023735 = 3035603) B3035603
theorem B3415061 : Blo 2023435 3415061 := bbase (se 6 (by rfl) ⟨80040, by rfl⟩ : syracuseStep 3415061 = 160081) (by norm_num)
theorem B2276707 : Blo 2023435 2276707 := bstep (se 1 (by rfl) ⟨1707530, by rfl⟩ : syracuseStep 2276707 = 3415061) B3415061
theorem B3035609 : Blo 2023435 3035609 := bstep (se 2 (by rfl) ⟨1138353, by rfl⟩ : syracuseStep 3035609 = 2276707) B2276707
theorem B2023739 : Blo 2023435 2023739 := bstep (se 1 (by rfl) ⟨1517804, by rfl⟩ : syracuseStep 2023739 = 3035609) B3035609
theorem B4928813 : Blo 2023435 4928813 := bbase (se 3 (by rfl) ⟨924152, by rfl⟩ : syracuseStep 4928813 = 1848305) (by norm_num)
theorem B3285875 : Blo 2023435 3285875 := bstep (se 1 (by rfl) ⟨2464406, by rfl⟩ : syracuseStep 3285875 = 4928813) B4928813
theorem B2190583 : Blo 2023435 2190583 := bstep (se 1 (by rfl) ⟨1642937, by rfl⟩ : syracuseStep 2190583 = 3285875) B3285875
theorem B11683109 : Blo 2023435 11683109 := bstep (se 4 (by rfl) ⟨1095291, by rfl⟩ : syracuseStep 11683109 = 2190583) B2190583
theorem B7788739 : Blo 2023435 7788739 := bstep (se 1 (by rfl) ⟨5841554, by rfl⟩ : syracuseStep 7788739 = 11683109) B11683109
theorem B10384985 : Blo 2023435 10384985 := bstep (se 2 (by rfl) ⟨3894369, by rfl⟩ : syracuseStep 10384985 = 7788739) B7788739
theorem B6923323 : Blo 2023435 6923323 := bstep (se 1 (by rfl) ⟨5192492, by rfl⟩ : syracuseStep 6923323 = 10384985) B10384985
theorem B9231097 : Blo 2023435 9231097 := bstep (se 2 (by rfl) ⟨3461661, by rfl⟩ : syracuseStep 9231097 = 6923323) B6923323
theorem B12308129 : Blo 2023435 12308129 := bstep (se 2 (by rfl) ⟨4615548, by rfl⟩ : syracuseStep 12308129 = 9231097) B9231097
theorem B8205419 : Blo 2023435 8205419 := bstep (se 1 (by rfl) ⟨6154064, by rfl⟩ : syracuseStep 8205419 = 12308129) B12308129
theorem B21881117 : Blo 2023435 21881117 := bstep (se 3 (by rfl) ⟨4102709, by rfl⟩ : syracuseStep 21881117 = 8205419) B8205419
theorem B14587411 : Blo 2023435 14587411 := bstep (se 1 (by rfl) ⟨10940558, by rfl⟩ : syracuseStep 14587411 = 21881117) B21881117
theorem B19449881 : Blo 2023435 19449881 := bstep (se 2 (by rfl) ⟨7293705, by rfl⟩ : syracuseStep 19449881 = 14587411) B14587411
theorem B12966587 : Blo 2023435 12966587 := bstep (se 1 (by rfl) ⟨9724940, by rfl⟩ : syracuseStep 12966587 = 19449881) B19449881
theorem B8644391 : Blo 2023435 8644391 := bstep (se 1 (by rfl) ⟨6483293, by rfl⟩ : syracuseStep 8644391 = 12966587) B12966587
theorem B5762927 : Blo 2023435 5762927 := bstep (se 1 (by rfl) ⟨4322195, by rfl⟩ : syracuseStep 5762927 = 8644391) B8644391
theorem B15367805 : Blo 2023435 15367805 := bstep (se 3 (by rfl) ⟨2881463, by rfl⟩ : syracuseStep 15367805 = 5762927) B5762927
theorem B10245203 : Blo 2023435 10245203 := bstep (se 1 (by rfl) ⟨7683902, by rfl⟩ : syracuseStep 10245203 = 15367805) B15367805
theorem B6830135 : Blo 2023435 6830135 := bstep (se 1 (by rfl) ⟨5122601, by rfl⟩ : syracuseStep 6830135 = 10245203) B10245203
theorem B4553423 : Blo 2023435 4553423 := bstep (se 1 (by rfl) ⟨3415067, by rfl⟩ : syracuseStep 4553423 = 6830135) B6830135
theorem B3035615 : Blo 2023435 3035615 := bstep (se 1 (by rfl) ⟨2276711, by rfl⟩ : syracuseStep 3035615 = 4553423) B4553423
theorem B2023743 : Blo 2023435 2023743 := bstep (se 1 (by rfl) ⟨1517807, by rfl⟩ : syracuseStep 2023743 = 3035615) B3035615
theorem B3035621 : Blo 2023435 3035621 := bbase (se 4 (by rfl) ⟨284589, by rfl⟩ : syracuseStep 3035621 = 569179) (by norm_num)
theorem B2023747 : Blo 2023435 2023747 := bstep (se 1 (by rfl) ⟨1517810, by rfl⟩ : syracuseStep 2023747 = 3035621) B3035621
theorem B9724981 : Blo 2023435 9724981 := bbase (se 5 (by rfl) ⟨455858, by rfl⟩ : syracuseStep 9724981 = 911717) (by norm_num)
theorem B12966641 : Blo 2023435 12966641 := bstep (se 2 (by rfl) ⟨4862490, by rfl⟩ : syracuseStep 12966641 = 9724981) B9724981
theorem B8644427 : Blo 2023435 8644427 := bstep (se 1 (by rfl) ⟨6483320, by rfl⟩ : syracuseStep 8644427 = 12966641) B12966641
theorem B5762951 : Blo 2023435 5762951 := bstep (se 1 (by rfl) ⟨4322213, by rfl⟩ : syracuseStep 5762951 = 8644427) B8644427
theorem B3841967 : Blo 2023435 3841967 := bstep (se 1 (by rfl) ⟨2881475, by rfl⟩ : syracuseStep 3841967 = 5762951) B5762951
theorem B2561311 : Blo 2023435 2561311 := bstep (se 1 (by rfl) ⟨1920983, by rfl⟩ : syracuseStep 2561311 = 3841967) B3841967
theorem B3415081 : Blo 2023435 3415081 := bstep (se 2 (by rfl) ⟨1280655, by rfl⟩ : syracuseStep 3415081 = 2561311) B2561311
theorem B4553441 : Blo 2023435 4553441 := bstep (se 2 (by rfl) ⟨1707540, by rfl⟩ : syracuseStep 4553441 = 3415081) B3415081
theorem B3035627 : Blo 2023435 3035627 := bstep (se 1 (by rfl) ⟨2276720, by rfl⟩ : syracuseStep 3035627 = 4553441) B4553441
theorem B2023751 : Blo 2023435 2023751 := bstep (se 1 (by rfl) ⟨1517813, by rfl⟩ : syracuseStep 2023751 = 3035627) B3035627
theorem B2276725 : Blo 2023435 2276725 := bbase (se 5 (by rfl) ⟨106721, by rfl⟩ : syracuseStep 2276725 = 213443) (by norm_num)
theorem B3035633 : Blo 2023435 3035633 := bstep (se 2 (by rfl) ⟨1138362, by rfl⟩ : syracuseStep 3035633 = 2276725) B2276725
theorem B2023755 : Blo 2023435 2023755 := bstep (se 1 (by rfl) ⟨1517816, by rfl⟩ : syracuseStep 2023755 = 3035633) B3035633
theorem B2561321 : Blo 2023435 2561321 := bbase (se 2 (by rfl) ⟨960495, by rfl⟩ : syracuseStep 2561321 = 1920991) (by norm_num)
theorem B6830189 : Blo 2023435 6830189 := bstep (se 3 (by rfl) ⟨1280660, by rfl⟩ : syracuseStep 6830189 = 2561321) B2561321
theorem B4553459 : Blo 2023435 4553459 := bstep (se 1 (by rfl) ⟨3415094, by rfl⟩ : syracuseStep 4553459 = 6830189) B6830189
theorem B3035639 : Blo 2023435 3035639 := bstep (se 1 (by rfl) ⟨2276729, by rfl⟩ : syracuseStep 3035639 = 4553459) B4553459
theorem B2023759 : Blo 2023435 2023759 := bstep (se 1 (by rfl) ⟨1517819, by rfl⟩ : syracuseStep 2023759 = 3035639) B3035639
theorem B3035645 : Blo 2023435 3035645 := bbase (se 3 (by rfl) ⟨569183, by rfl⟩ : syracuseStep 3035645 = 1138367) (by norm_num)
theorem B2023763 : Blo 2023435 2023763 := bstep (se 1 (by rfl) ⟨1517822, by rfl⟩ : syracuseStep 2023763 = 3035645) B3035645
theorem B4553477 : Blo 2023435 4553477 := bbase (se 4 (by rfl) ⟨426888, by rfl⟩ : syracuseStep 4553477 = 853777) (by norm_num)
theorem B3035651 : Blo 2023435 3035651 := bstep (se 1 (by rfl) ⟨2276738, by rfl⟩ : syracuseStep 3035651 = 4553477) B4553477
theorem B2023767 : Blo 2023435 2023767 := bstep (se 1 (by rfl) ⟨1517825, by rfl⟩ : syracuseStep 2023767 = 3035651) B3035651
theorem B3842005 : Blo 2023435 3842005 := bbase (se 7 (by rfl) ⟨45023, by rfl⟩ : syracuseStep 3842005 = 90047) (by norm_num)
theorem B5122673 : Blo 2023435 5122673 := bstep (se 2 (by rfl) ⟨1921002, by rfl⟩ : syracuseStep 5122673 = 3842005) B3842005
theorem B3415115 : Blo 2023435 3415115 := bstep (se 1 (by rfl) ⟨2561336, by rfl⟩ : syracuseStep 3415115 = 5122673) B5122673
theorem B2276743 : Blo 2023435 2276743 := bstep (se 1 (by rfl) ⟨1707557, by rfl⟩ : syracuseStep 2276743 = 3415115) B3415115
theorem B3035657 : Blo 2023435 3035657 := bstep (se 2 (by rfl) ⟨1138371, by rfl⟩ : syracuseStep 3035657 = 2276743) B2276743
theorem B2023771 : Blo 2023435 2023771 := bstep (se 1 (by rfl) ⟨1517828, by rfl⟩ : syracuseStep 2023771 = 3035657) B3035657
theorem B10245365 : Blo 2023435 10245365 := bbase (se 5 (by rfl) ⟨480251, by rfl⟩ : syracuseStep 10245365 = 960503) (by norm_num)
theorem B6830243 : Blo 2023435 6830243 := bstep (se 1 (by rfl) ⟨5122682, by rfl⟩ : syracuseStep 6830243 = 10245365) B10245365
theorem B4553495 : Blo 2023435 4553495 := bstep (se 1 (by rfl) ⟨3415121, by rfl⟩ : syracuseStep 4553495 = 6830243) B6830243
theorem B3035663 : Blo 2023435 3035663 := bstep (se 1 (by rfl) ⟨2276747, by rfl⟩ : syracuseStep 3035663 = 4553495) B4553495
theorem B2023775 : Blo 2023435 2023775 := bstep (se 1 (by rfl) ⟨1517831, by rfl⟩ : syracuseStep 2023775 = 3035663) B3035663
theorem B3035669 : Blo 2023435 3035669 := bbase (se 6 (by rfl) ⟨71148, by rfl⟩ : syracuseStep 3035669 = 142297) (by norm_num)
theorem B2023779 : Blo 2023435 2023779 := bstep (se 1 (by rfl) ⟨1517834, by rfl⟩ : syracuseStep 2023779 = 3035669) B3035669
theorem B27693845 : Blo 2023435 27693845 := bbase (se 6 (by rfl) ⟨649074, by rfl⟩ : syracuseStep 27693845 = 1298149) (by norm_num)
theorem B18462563 : Blo 2023435 18462563 := bstep (se 1 (by rfl) ⟨13846922, by rfl⟩ : syracuseStep 18462563 = 27693845) B27693845
theorem B12308375 : Blo 2023435 12308375 := bstep (se 1 (by rfl) ⟨9231281, by rfl⟩ : syracuseStep 12308375 = 18462563) B18462563
theorem B8205583 : Blo 2023435 8205583 := bstep (se 1 (by rfl) ⟨6154187, by rfl⟩ : syracuseStep 8205583 = 12308375) B12308375
theorem B10940777 : Blo 2023435 10940777 := bstep (se 2 (by rfl) ⟨4102791, by rfl⟩ : syracuseStep 10940777 = 8205583) B8205583
theorem B7293851 : Blo 2023435 7293851 := bstep (se 1 (by rfl) ⟨5470388, by rfl⟩ : syracuseStep 7293851 = 10940777) B10940777
theorem B4862567 : Blo 2023435 4862567 := bstep (se 1 (by rfl) ⟨3646925, by rfl⟩ : syracuseStep 4862567 = 7293851) B7293851
theorem B3241711 : Blo 2023435 3241711 := bstep (se 1 (by rfl) ⟨2431283, by rfl⟩ : syracuseStep 3241711 = 4862567) B4862567
theorem B17289125 : Blo 2023435 17289125 := bstep (se 4 (by rfl) ⟨1620855, by rfl⟩ : syracuseStep 17289125 = 3241711) B3241711
theorem B11526083 : Blo 2023435 11526083 := bstep (se 1 (by rfl) ⟨8644562, by rfl⟩ : syracuseStep 11526083 = 17289125) B17289125
theorem B7684055 : Blo 2023435 7684055 := bstep (se 1 (by rfl) ⟨5763041, by rfl⟩ : syracuseStep 7684055 = 11526083) B11526083
theorem B5122703 : Blo 2023435 5122703 := bstep (se 1 (by rfl) ⟨3842027, by rfl⟩ : syracuseStep 5122703 = 7684055) B7684055
theorem B3415135 : Blo 2023435 3415135 := bstep (se 1 (by rfl) ⟨2561351, by rfl⟩ : syracuseStep 3415135 = 5122703) B5122703
theorem B4553513 : Blo 2023435 4553513 := bstep (se 2 (by rfl) ⟨1707567, by rfl⟩ : syracuseStep 4553513 = 3415135) B3415135
theorem B3035675 : Blo 2023435 3035675 := bstep (se 1 (by rfl) ⟨2276756, by rfl⟩ : syracuseStep 3035675 = 4553513) B4553513
theorem B2023783 : Blo 2023435 2023783 := bstep (se 1 (by rfl) ⟨1517837, by rfl⟩ : syracuseStep 2023783 = 3035675) B3035675
theorem B2276761 : Blo 2023435 2276761 := bbase (se 2 (by rfl) ⟨853785, by rfl⟩ : syracuseStep 2276761 = 1707571) (by norm_num)
theorem B3035681 : Blo 2023435 3035681 := bstep (se 2 (by rfl) ⟨1138380, by rfl⟩ : syracuseStep 3035681 = 2276761) B2276761
theorem B2023787 : Blo 2023435 2023787 := bstep (se 1 (by rfl) ⟨1517840, by rfl⟩ : syracuseStep 2023787 = 3035681) B3035681
theorem B7684085 : Blo 2023435 7684085 := bbase (se 5 (by rfl) ⟨360191, by rfl⟩ : syracuseStep 7684085 = 720383) (by norm_num)
theorem B5122723 : Blo 2023435 5122723 := bstep (se 1 (by rfl) ⟨3842042, by rfl⟩ : syracuseStep 5122723 = 7684085) B7684085
theorem B6830297 : Blo 2023435 6830297 := bstep (se 2 (by rfl) ⟨2561361, by rfl⟩ : syracuseStep 6830297 = 5122723) B5122723
theorem B4553531 : Blo 2023435 4553531 := bstep (se 1 (by rfl) ⟨3415148, by rfl⟩ : syracuseStep 4553531 = 6830297) B6830297
theorem B3035687 : Blo 2023435 3035687 := bstep (se 1 (by rfl) ⟨2276765, by rfl⟩ : syracuseStep 3035687 = 4553531) B4553531
theorem B2023791 : Blo 2023435 2023791 := bstep (se 1 (by rfl) ⟨1517843, by rfl⟩ : syracuseStep 2023791 = 3035687) B3035687
theorem B3035693 : Blo 2023435 3035693 := bbase (se 3 (by rfl) ⟨569192, by rfl⟩ : syracuseStep 3035693 = 1138385) (by norm_num)
theorem B2023795 : Blo 2023435 2023795 := bstep (se 1 (by rfl) ⟨1517846, by rfl⟩ : syracuseStep 2023795 = 3035693) B3035693
theorem B4553549 : Blo 2023435 4553549 := bbase (se 3 (by rfl) ⟨853790, by rfl⟩ : syracuseStep 4553549 = 1707581) (by norm_num)
theorem B3035699 : Blo 2023435 3035699 := bstep (se 1 (by rfl) ⟨2276774, by rfl⟩ : syracuseStep 3035699 = 4553549) B4553549
theorem B2023799 : Blo 2023435 2023799 := bstep (se 1 (by rfl) ⟨1517849, by rfl⟩ : syracuseStep 2023799 = 3035699) B3035699
theorem B2561377 : Blo 2023435 2561377 := bbase (se 2 (by rfl) ⟨960516, by rfl⟩ : syracuseStep 2561377 = 1921033) (by norm_num)
theorem B3415169 : Blo 2023435 3415169 := bstep (se 2 (by rfl) ⟨1280688, by rfl⟩ : syracuseStep 3415169 = 2561377) B2561377
theorem B2276779 : Blo 2023435 2276779 := bstep (se 1 (by rfl) ⟨1707584, by rfl⟩ : syracuseStep 2276779 = 3415169) B3415169
theorem B3035705 : Blo 2023435 3035705 := bstep (se 2 (by rfl) ⟨1138389, by rfl⟩ : syracuseStep 3035705 = 2276779) B2276779
theorem B2023803 : Blo 2023435 2023803 := bstep (se 1 (by rfl) ⟨1517852, by rfl⟩ : syracuseStep 2023803 = 3035705) B3035705
theorem B23052437 : Blo 2023435 23052437 := bbase (se 6 (by rfl) ⟨540291, by rfl⟩ : syracuseStep 23052437 = 1080583) (by norm_num)
theorem B15368291 : Blo 2023435 15368291 := bstep (se 1 (by rfl) ⟨11526218, by rfl⟩ : syracuseStep 15368291 = 23052437) B23052437
theorem B10245527 : Blo 2023435 10245527 := bstep (se 1 (by rfl) ⟨7684145, by rfl⟩ : syracuseStep 10245527 = 15368291) B15368291
theorem B6830351 : Blo 2023435 6830351 := bstep (se 1 (by rfl) ⟨5122763, by rfl⟩ : syracuseStep 6830351 = 10245527) B10245527
theorem B4553567 : Blo 2023435 4553567 := bstep (se 1 (by rfl) ⟨3415175, by rfl⟩ : syracuseStep 4553567 = 6830351) B6830351
theorem B3035711 : Blo 2023435 3035711 := bstep (se 1 (by rfl) ⟨2276783, by rfl⟩ : syracuseStep 3035711 = 4553567) B4553567
theorem B2023807 : Blo 2023435 2023807 := bstep (se 1 (by rfl) ⟨1517855, by rfl⟩ : syracuseStep 2023807 = 3035711) B3035711
theorem B3035717 : Blo 2023435 3035717 := bbase (se 4 (by rfl) ⟨284598, by rfl⟩ : syracuseStep 3035717 = 569197) (by norm_num)
theorem B2023811 : Blo 2023435 2023811 := bstep (se 1 (by rfl) ⟨1517858, by rfl⟩ : syracuseStep 2023811 = 3035717) B3035717
theorem B3415189 : Blo 2023435 3415189 := bbase (se 6 (by rfl) ⟨80043, by rfl⟩ : syracuseStep 3415189 = 160087) (by norm_num)
theorem B4553585 : Blo 2023435 4553585 := bstep (se 2 (by rfl) ⟨1707594, by rfl⟩ : syracuseStep 4553585 = 3415189) B3415189
theorem B3035723 : Blo 2023435 3035723 := bstep (se 1 (by rfl) ⟨2276792, by rfl⟩ : syracuseStep 3035723 = 4553585) B4553585
theorem B2023815 : Blo 2023435 2023815 := bstep (se 1 (by rfl) ⟨1517861, by rfl⟩ : syracuseStep 2023815 = 3035723) B3035723
theorem B2276797 : Blo 2023435 2276797 := bbase (se 3 (by rfl) ⟨426899, by rfl⟩ : syracuseStep 2276797 = 853799) (by norm_num)
theorem B3035729 : Blo 2023435 3035729 := bstep (se 2 (by rfl) ⟨1138398, by rfl⟩ : syracuseStep 3035729 = 2276797) B2276797
theorem B2023819 : Blo 2023435 2023819 := bstep (se 1 (by rfl) ⟨1517864, by rfl⟩ : syracuseStep 2023819 = 3035729) B3035729
theorem B6830405 : Blo 2023435 6830405 := bbase (se 4 (by rfl) ⟨640350, by rfl⟩ : syracuseStep 6830405 = 1280701) (by norm_num)
theorem B4553603 : Blo 2023435 4553603 := bstep (se 1 (by rfl) ⟨3415202, by rfl⟩ : syracuseStep 4553603 = 6830405) B6830405
theorem B3035735 : Blo 2023435 3035735 := bstep (se 1 (by rfl) ⟨2276801, by rfl⟩ : syracuseStep 3035735 = 4553603) B4553603
theorem B2023823 : Blo 2023435 2023823 := bstep (se 1 (by rfl) ⟨1517867, by rfl⟩ : syracuseStep 2023823 = 3035735) B3035735
theorem B3035741 : Blo 2023435 3035741 := bbase (se 3 (by rfl) ⟨569201, by rfl⟩ : syracuseStep 3035741 = 1138403) (by norm_num)
theorem B2023827 : Blo 2023435 2023827 := bstep (se 1 (by rfl) ⟨1517870, by rfl⟩ : syracuseStep 2023827 = 3035741) B3035741
theorem B4553621 : Blo 2023435 4553621 := bbase (se 6 (by rfl) ⟨106725, by rfl⟩ : syracuseStep 4553621 = 213451) (by norm_num)
theorem B3035747 : Blo 2023435 3035747 := bstep (se 1 (by rfl) ⟨2276810, by rfl⟩ : syracuseStep 3035747 = 4553621) B4553621
theorem B2023831 : Blo 2023435 2023831 := bstep (se 1 (by rfl) ⟨1517873, by rfl⟩ : syracuseStep 2023831 = 3035747) B3035747
theorem B4862693 : Blo 2023435 4862693 := bbase (se 4 (by rfl) ⟨455877, by rfl⟩ : syracuseStep 4862693 = 911755) (by norm_num)
theorem B3241795 : Blo 2023435 3241795 := bstep (se 1 (by rfl) ⟨2431346, by rfl⟩ : syracuseStep 3241795 = 4862693) B4862693
theorem B4322393 : Blo 2023435 4322393 := bstep (se 2 (by rfl) ⟨1620897, by rfl⟩ : syracuseStep 4322393 = 3241795) B3241795
theorem B2881595 : Blo 2023435 2881595 := bstep (se 1 (by rfl) ⟨2161196, by rfl⟩ : syracuseStep 2881595 = 4322393) B4322393
theorem B7684253 : Blo 2023435 7684253 := bstep (se 3 (by rfl) ⟨1440797, by rfl⟩ : syracuseStep 7684253 = 2881595) B2881595
theorem B5122835 : Blo 2023435 5122835 := bstep (se 1 (by rfl) ⟨3842126, by rfl⟩ : syracuseStep 5122835 = 7684253) B7684253
theorem B3415223 : Blo 2023435 3415223 := bstep (se 1 (by rfl) ⟨2561417, by rfl⟩ : syracuseStep 3415223 = 5122835) B5122835
theorem B2276815 : Blo 2023435 2276815 := bstep (se 1 (by rfl) ⟨1707611, by rfl⟩ : syracuseStep 2276815 = 3415223) B3415223
theorem B3035753 : Blo 2023435 3035753 := bstep (se 2 (by rfl) ⟨1138407, by rfl⟩ : syracuseStep 3035753 = 2276815) B2276815
theorem B2023835 : Blo 2023435 2023835 := bstep (se 1 (by rfl) ⟨1517876, by rfl⟩ : syracuseStep 2023835 = 3035753) B3035753
theorem B4862701 : Blo 2023435 4862701 := bbase (se 3 (by rfl) ⟨911756, by rfl⟩ : syracuseStep 4862701 = 1823513) (by norm_num)
theorem B6483601 : Blo 2023435 6483601 := bstep (se 2 (by rfl) ⟨2431350, by rfl⟩ : syracuseStep 6483601 = 4862701) B4862701
theorem B8644801 : Blo 2023435 8644801 := bstep (se 2 (by rfl) ⟨3241800, by rfl⟩ : syracuseStep 8644801 = 6483601) B6483601
theorem B11526401 : Blo 2023435 11526401 := bstep (se 2 (by rfl) ⟨4322400, by rfl⟩ : syracuseStep 11526401 = 8644801) B8644801
theorem B7684267 : Blo 2023435 7684267 := bstep (se 1 (by rfl) ⟨5763200, by rfl⟩ : syracuseStep 7684267 = 11526401) B11526401
theorem B10245689 : Blo 2023435 10245689 := bstep (se 2 (by rfl) ⟨3842133, by rfl⟩ : syracuseStep 10245689 = 7684267) B7684267
theorem B6830459 : Blo 2023435 6830459 := bstep (se 1 (by rfl) ⟨5122844, by rfl⟩ : syracuseStep 6830459 = 10245689) B10245689
theorem B4553639 : Blo 2023435 4553639 := bstep (se 1 (by rfl) ⟨3415229, by rfl⟩ : syracuseStep 4553639 = 6830459) B6830459
theorem B3035759 : Blo 2023435 3035759 := bstep (se 1 (by rfl) ⟨2276819, by rfl⟩ : syracuseStep 3035759 = 4553639) B4553639
theorem B2023839 : Blo 2023435 2023839 := bstep (se 1 (by rfl) ⟨1517879, by rfl⟩ : syracuseStep 2023839 = 3035759) B3035759
theorem B3035765 : Blo 2023435 3035765 := bbase (se 5 (by rfl) ⟨142301, by rfl⟩ : syracuseStep 3035765 = 284603) (by norm_num)
theorem B2023843 : Blo 2023435 2023843 := bstep (se 1 (by rfl) ⟨1517882, by rfl⟩ : syracuseStep 2023843 = 3035765) B3035765
theorem B3842149 : Blo 2023435 3842149 := bbase (se 4 (by rfl) ⟨360201, by rfl⟩ : syracuseStep 3842149 = 720403) (by norm_num)
theorem B5122865 : Blo 2023435 5122865 := bstep (se 2 (by rfl) ⟨1921074, by rfl⟩ : syracuseStep 5122865 = 3842149) B3842149
theorem B3415243 : Blo 2023435 3415243 := bstep (se 1 (by rfl) ⟨2561432, by rfl⟩ : syracuseStep 3415243 = 5122865) B5122865
theorem B4553657 : Blo 2023435 4553657 := bstep (se 2 (by rfl) ⟨1707621, by rfl⟩ : syracuseStep 4553657 = 3415243) B3415243
theorem B3035771 : Blo 2023435 3035771 := bstep (se 1 (by rfl) ⟨2276828, by rfl⟩ : syracuseStep 3035771 = 4553657) B4553657
theorem B2023847 : Blo 2023435 2023847 := bstep (se 1 (by rfl) ⟨1517885, by rfl⟩ : syracuseStep 2023847 = 3035771) B3035771
theorem B2276833 : Blo 2023435 2276833 := bbase (se 2 (by rfl) ⟨853812, by rfl⟩ : syracuseStep 2276833 = 1707625) (by norm_num)
theorem B3035777 : Blo 2023435 3035777 := bstep (se 2 (by rfl) ⟨1138416, by rfl⟩ : syracuseStep 3035777 = 2276833) B2276833
theorem B2023851 : Blo 2023435 2023851 := bstep (se 1 (by rfl) ⟨1517888, by rfl⟩ : syracuseStep 2023851 = 3035777) B3035777
theorem B5122885 : Blo 2023435 5122885 := bbase (se 4 (by rfl) ⟨480270, by rfl⟩ : syracuseStep 5122885 = 960541) (by norm_num)
theorem B6830513 : Blo 2023435 6830513 := bstep (se 2 (by rfl) ⟨2561442, by rfl⟩ : syracuseStep 6830513 = 5122885) B5122885
theorem B4553675 : Blo 2023435 4553675 := bstep (se 1 (by rfl) ⟨3415256, by rfl⟩ : syracuseStep 4553675 = 6830513) B6830513
theorem B3035783 : Blo 2023435 3035783 := bstep (se 1 (by rfl) ⟨2276837, by rfl⟩ : syracuseStep 3035783 = 4553675) B4553675
theorem B2023855 : Blo 2023435 2023855 := bstep (se 1 (by rfl) ⟨1517891, by rfl⟩ : syracuseStep 2023855 = 3035783) B3035783
theorem B3035789 : Blo 2023435 3035789 := bbase (se 3 (by rfl) ⟨569210, by rfl⟩ : syracuseStep 3035789 = 1138421) (by norm_num)
theorem B2023859 : Blo 2023435 2023859 := bstep (se 1 (by rfl) ⟨1517894, by rfl⟩ : syracuseStep 2023859 = 3035789) B3035789
theorem B4553693 : Blo 2023435 4553693 := bbase (se 3 (by rfl) ⟨853817, by rfl⟩ : syracuseStep 4553693 = 1707635) (by norm_num)
theorem B3035795 : Blo 2023435 3035795 := bstep (se 1 (by rfl) ⟨2276846, by rfl⟩ : syracuseStep 3035795 = 4553693) B4553693
theorem B2023863 : Blo 2023435 2023863 := bstep (se 1 (by rfl) ⟨1517897, by rfl⟩ : syracuseStep 2023863 = 3035795) B3035795
theorem B3415277 : Blo 2023435 3415277 := bbase (se 3 (by rfl) ⟨640364, by rfl⟩ : syracuseStep 3415277 = 1280729) (by norm_num)
theorem B2276851 : Blo 2023435 2276851 := bstep (se 1 (by rfl) ⟨1707638, by rfl⟩ : syracuseStep 2276851 = 3415277) B3415277
theorem B3035801 : Blo 2023435 3035801 := bstep (se 2 (by rfl) ⟨1138425, by rfl⟩ : syracuseStep 3035801 = 2276851) B2276851
theorem B2023867 : Blo 2023435 2023867 := bstep (se 1 (by rfl) ⟨1517900, by rfl⟩ : syracuseStep 2023867 = 3035801) B3035801
theorem B4381445 : Blo 2023435 4381445 := bbase (se 4 (by rfl) ⟨410760, by rfl⟩ : syracuseStep 4381445 = 821521) (by norm_num)
theorem B2920963 : Blo 2023435 2920963 := bstep (se 1 (by rfl) ⟨2190722, by rfl⟩ : syracuseStep 2920963 = 4381445) B4381445
theorem B3894617 : Blo 2023435 3894617 := bstep (se 2 (by rfl) ⟨1460481, by rfl⟩ : syracuseStep 3894617 = 2920963) B2920963
theorem B2596411 : Blo 2023435 2596411 := bstep (se 1 (by rfl) ⟨1947308, by rfl⟩ : syracuseStep 2596411 = 3894617) B3894617
theorem B3461881 : Blo 2023435 3461881 := bstep (se 2 (by rfl) ⟨1298205, by rfl⟩ : syracuseStep 3461881 = 2596411) B2596411
theorem B4615841 : Blo 2023435 4615841 := bstep (se 2 (by rfl) ⟨1730940, by rfl⟩ : syracuseStep 4615841 = 3461881) B3461881
theorem B3077227 : Blo 2023435 3077227 := bstep (se 1 (by rfl) ⟨2307920, by rfl⟩ : syracuseStep 3077227 = 4615841) B4615841
theorem B4102969 : Blo 2023435 4102969 := bstep (se 2 (by rfl) ⟨1538613, by rfl⟩ : syracuseStep 4102969 = 3077227) B3077227
theorem B5470625 : Blo 2023435 5470625 := bstep (se 2 (by rfl) ⟨2051484, by rfl⟩ : syracuseStep 5470625 = 4102969) B4102969
theorem B14588333 : Blo 2023435 14588333 := bstep (se 3 (by rfl) ⟨2735312, by rfl⟩ : syracuseStep 14588333 = 5470625) B5470625
theorem B9725555 : Blo 2023435 9725555 := bstep (se 1 (by rfl) ⟨7294166, by rfl⟩ : syracuseStep 9725555 = 14588333) B14588333
theorem B25934813 : Blo 2023435 25934813 := bstep (se 3 (by rfl) ⟨4862777, by rfl⟩ : syracuseStep 25934813 = 9725555) B9725555
theorem B17289875 : Blo 2023435 17289875 := bstep (se 1 (by rfl) ⟨12967406, by rfl⟩ : syracuseStep 17289875 = 25934813) B25934813
theorem B11526583 : Blo 2023435 11526583 := bstep (se 1 (by rfl) ⟨8644937, by rfl⟩ : syracuseStep 11526583 = 17289875) B17289875
theorem B15368777 : Blo 2023435 15368777 := bstep (se 2 (by rfl) ⟨5763291, by rfl⟩ : syracuseStep 15368777 = 11526583) B11526583
theorem B10245851 : Blo 2023435 10245851 := bstep (se 1 (by rfl) ⟨7684388, by rfl⟩ : syracuseStep 10245851 = 15368777) B15368777
theorem B6830567 : Blo 2023435 6830567 := bstep (se 1 (by rfl) ⟨5122925, by rfl⟩ : syracuseStep 6830567 = 10245851) B10245851
theorem B4553711 : Blo 2023435 4553711 := bstep (se 1 (by rfl) ⟨3415283, by rfl⟩ : syracuseStep 4553711 = 6830567) B6830567
theorem B3035807 : Blo 2023435 3035807 := bstep (se 1 (by rfl) ⟨2276855, by rfl⟩ : syracuseStep 3035807 = 4553711) B4553711
theorem B2023871 : Blo 2023435 2023871 := bstep (se 1 (by rfl) ⟨1517903, by rfl⟩ : syracuseStep 2023871 = 3035807) B3035807
theorem B3035813 : Blo 2023435 3035813 := bbase (se 4 (by rfl) ⟨284607, by rfl⟩ : syracuseStep 3035813 = 569215) (by norm_num)
theorem B2023875 : Blo 2023435 2023875 := bstep (se 1 (by rfl) ⟨1517906, by rfl⟩ : syracuseStep 2023875 = 3035813) B3035813
theorem B2561473 : Blo 2023435 2561473 := bbase (se 2 (by rfl) ⟨960552, by rfl⟩ : syracuseStep 2561473 = 1921105) (by norm_num)
theorem B3415297 : Blo 2023435 3415297 := bstep (se 2 (by rfl) ⟨1280736, by rfl⟩ : syracuseStep 3415297 = 2561473) B2561473
theorem B4553729 : Blo 2023435 4553729 := bstep (se 2 (by rfl) ⟨1707648, by rfl⟩ : syracuseStep 4553729 = 3415297) B3415297
theorem B3035819 : Blo 2023435 3035819 := bstep (se 1 (by rfl) ⟨2276864, by rfl⟩ : syracuseStep 3035819 = 4553729) B4553729
theorem B2023879 : Blo 2023435 2023879 := bstep (se 1 (by rfl) ⟨1517909, by rfl⟩ : syracuseStep 2023879 = 3035819) B3035819
theorem B2276869 : Blo 2023435 2276869 := bbase (se 4 (by rfl) ⟨213456, by rfl⟩ : syracuseStep 2276869 = 426913) (by norm_num)
theorem B3035825 : Blo 2023435 3035825 := bstep (se 2 (by rfl) ⟨1138434, by rfl⟩ : syracuseStep 3035825 = 2276869) B2276869
theorem B2023883 : Blo 2023435 2023883 := bstep (se 1 (by rfl) ⟨1517912, by rfl⟩ : syracuseStep 2023883 = 3035825) B3035825
theorem B2881669 : Blo 2023435 2881669 := bbase (se 4 (by rfl) ⟨270156, by rfl⟩ : syracuseStep 2881669 = 540313) (by norm_num)
theorem B3842225 : Blo 2023435 3842225 := bstep (se 2 (by rfl) ⟨1440834, by rfl⟩ : syracuseStep 3842225 = 2881669) B2881669
theorem B2561483 : Blo 2023435 2561483 := bstep (se 1 (by rfl) ⟨1921112, by rfl⟩ : syracuseStep 2561483 = 3842225) B3842225
theorem B6830621 : Blo 2023435 6830621 := bstep (se 3 (by rfl) ⟨1280741, by rfl⟩ : syracuseStep 6830621 = 2561483) B2561483
theorem B4553747 : Blo 2023435 4553747 := bstep (se 1 (by rfl) ⟨3415310, by rfl⟩ : syracuseStep 4553747 = 6830621) B6830621
theorem B3035831 : Blo 2023435 3035831 := bstep (se 1 (by rfl) ⟨2276873, by rfl⟩ : syracuseStep 3035831 = 4553747) B4553747
theorem B2023887 : Blo 2023435 2023887 := bstep (se 1 (by rfl) ⟨1517915, by rfl⟩ : syracuseStep 2023887 = 3035831) B3035831
theorem B3035837 : Blo 2023435 3035837 := bbase (se 3 (by rfl) ⟨569219, by rfl⟩ : syracuseStep 3035837 = 1138439) (by norm_num)
theorem B2023891 : Blo 2023435 2023891 := bstep (se 1 (by rfl) ⟨1517918, by rfl⟩ : syracuseStep 2023891 = 3035837) B3035837
theorem B4553765 : Blo 2023435 4553765 := bbase (se 4 (by rfl) ⟨426915, by rfl⟩ : syracuseStep 4553765 = 853831) (by norm_num)
theorem B3035843 : Blo 2023435 3035843 := bstep (se 1 (by rfl) ⟨2276882, by rfl⟩ : syracuseStep 3035843 = 4553765) B4553765
theorem B2023895 : Blo 2023435 2023895 := bstep (se 1 (by rfl) ⟨1517921, by rfl⟩ : syracuseStep 2023895 = 3035843) B3035843
theorem B5122997 : Blo 2023435 5122997 := bbase (se 5 (by rfl) ⟨240140, by rfl⟩ : syracuseStep 5122997 = 480281) (by norm_num)
theorem B3415331 : Blo 2023435 3415331 := bstep (se 1 (by rfl) ⟨2561498, by rfl⟩ : syracuseStep 3415331 = 5122997) B5122997
theorem B2276887 : Blo 2023435 2276887 := bstep (se 1 (by rfl) ⟨1707665, by rfl⟩ : syracuseStep 2276887 = 3415331) B3415331
theorem B3035849 : Blo 2023435 3035849 := bstep (se 2 (by rfl) ⟨1138443, by rfl⟩ : syracuseStep 3035849 = 2276887) B2276887
theorem B2023899 : Blo 2023435 2023899 := bstep (se 1 (by rfl) ⟨1517924, by rfl⟩ : syracuseStep 2023899 = 3035849) B3035849
theorem B8206069 : Blo 2023435 8206069 := bbase (se 5 (by rfl) ⟨384659, by rfl⟩ : syracuseStep 8206069 = 769319) (by norm_num)
theorem B10941425 : Blo 2023435 10941425 := bstep (se 2 (by rfl) ⟨4103034, by rfl⟩ : syracuseStep 10941425 = 8206069) B8206069
theorem B7294283 : Blo 2023435 7294283 := bstep (se 1 (by rfl) ⟨5470712, by rfl⟩ : syracuseStep 7294283 = 10941425) B10941425
theorem B4862855 : Blo 2023435 4862855 := bstep (se 1 (by rfl) ⟨3647141, by rfl⟩ : syracuseStep 4862855 = 7294283) B7294283
theorem B12967613 : Blo 2023435 12967613 := bstep (se 3 (by rfl) ⟨2431427, by rfl⟩ : syracuseStep 12967613 = 4862855) B4862855
theorem B8645075 : Blo 2023435 8645075 := bstep (se 1 (by rfl) ⟨6483806, by rfl⟩ : syracuseStep 8645075 = 12967613) B12967613
theorem B5763383 : Blo 2023435 5763383 := bstep (se 1 (by rfl) ⟨4322537, by rfl⟩ : syracuseStep 5763383 = 8645075) B8645075
theorem B3842255 : Blo 2023435 3842255 := bstep (se 1 (by rfl) ⟨2881691, by rfl⟩ : syracuseStep 3842255 = 5763383) B5763383
theorem B10246013 : Blo 2023435 10246013 := bstep (se 3 (by rfl) ⟨1921127, by rfl⟩ : syracuseStep 10246013 = 3842255) B3842255
theorem B6830675 : Blo 2023435 6830675 := bstep (se 1 (by rfl) ⟨5123006, by rfl⟩ : syracuseStep 6830675 = 10246013) B10246013
theorem B4553783 : Blo 2023435 4553783 := bstep (se 1 (by rfl) ⟨3415337, by rfl⟩ : syracuseStep 4553783 = 6830675) B6830675
theorem B3035855 : Blo 2023435 3035855 := bstep (se 1 (by rfl) ⟨2276891, by rfl⟩ : syracuseStep 3035855 = 4553783) B4553783
theorem B2023903 : Blo 2023435 2023903 := bstep (se 1 (by rfl) ⟨1517927, by rfl⟩ : syracuseStep 2023903 = 3035855) B3035855
theorem B3035861 : Blo 2023435 3035861 := bbase (se 7 (by rfl) ⟨35576, by rfl⟩ : syracuseStep 3035861 = 71153) (by norm_num)
theorem B2023907 : Blo 2023435 2023907 := bstep (se 1 (by rfl) ⟨1517930, by rfl⟩ : syracuseStep 2023907 = 3035861) B3035861
theorem B18463733 : Blo 2023435 18463733 := bbase (se 5 (by rfl) ⟨865487, by rfl⟩ : syracuseStep 18463733 = 1730975) (by norm_num)
theorem B12309155 : Blo 2023435 12309155 := bstep (se 1 (by rfl) ⟨9231866, by rfl⟩ : syracuseStep 12309155 = 18463733) B18463733
theorem B8206103 : Blo 2023435 8206103 := bstep (se 1 (by rfl) ⟨6154577, by rfl⟩ : syracuseStep 8206103 = 12309155) B12309155
theorem B5470735 : Blo 2023435 5470735 := bstep (se 1 (by rfl) ⟨4103051, by rfl⟩ : syracuseStep 5470735 = 8206103) B8206103
theorem B7294313 : Blo 2023435 7294313 := bstep (se 2 (by rfl) ⟨2735367, by rfl⟩ : syracuseStep 7294313 = 5470735) B5470735
theorem B4862875 : Blo 2023435 4862875 := bstep (se 1 (by rfl) ⟨3647156, by rfl⟩ : syracuseStep 4862875 = 7294313) B7294313
theorem B6483833 : Blo 2023435 6483833 := bstep (se 2 (by rfl) ⟨2431437, by rfl⟩ : syracuseStep 6483833 = 4862875) B4862875
theorem B4322555 : Blo 2023435 4322555 := bstep (se 1 (by rfl) ⟨3241916, by rfl⟩ : syracuseStep 4322555 = 6483833) B6483833
theorem B2881703 : Blo 2023435 2881703 := bstep (se 1 (by rfl) ⟨2161277, by rfl⟩ : syracuseStep 2881703 = 4322555) B4322555
theorem B7684541 : Blo 2023435 7684541 := bstep (se 3 (by rfl) ⟨1440851, by rfl⟩ : syracuseStep 7684541 = 2881703) B2881703
theorem B5123027 : Blo 2023435 5123027 := bstep (se 1 (by rfl) ⟨3842270, by rfl⟩ : syracuseStep 5123027 = 7684541) B7684541
theorem B3415351 : Blo 2023435 3415351 := bstep (se 1 (by rfl) ⟨2561513, by rfl⟩ : syracuseStep 3415351 = 5123027) B5123027
theorem B4553801 : Blo 2023435 4553801 := bstep (se 2 (by rfl) ⟨1707675, by rfl⟩ : syracuseStep 4553801 = 3415351) B3415351
theorem B3035867 : Blo 2023435 3035867 := bstep (se 1 (by rfl) ⟨2276900, by rfl⟩ : syracuseStep 3035867 = 4553801) B4553801
theorem B2023911 : Blo 2023435 2023911 := bstep (se 1 (by rfl) ⟨1517933, by rfl⟩ : syracuseStep 2023911 = 3035867) B3035867
theorem B2276905 : Blo 2023435 2276905 := bbase (se 2 (by rfl) ⟨853839, by rfl⟩ : syracuseStep 2276905 = 1707679) (by norm_num)
theorem B3035873 : Blo 2023435 3035873 := bstep (se 2 (by rfl) ⟨1138452, by rfl⟩ : syracuseStep 3035873 = 2276905) B2276905
theorem B2023915 : Blo 2023435 2023915 := bstep (se 1 (by rfl) ⟨1517936, by rfl⟩ : syracuseStep 2023915 = 3035873) B3035873
theorem B19451573 : Blo 2023435 19451573 := bbase (se 5 (by rfl) ⟨911792, by rfl⟩ : syracuseStep 19451573 = 1823585) (by norm_num)
theorem B12967715 : Blo 2023435 12967715 := bstep (se 1 (by rfl) ⟨9725786, by rfl⟩ : syracuseStep 12967715 = 19451573) B19451573
theorem B8645143 : Blo 2023435 8645143 := bstep (se 1 (by rfl) ⟨6483857, by rfl⟩ : syracuseStep 8645143 = 12967715) B12967715
theorem B11526857 : Blo 2023435 11526857 := bstep (se 2 (by rfl) ⟨4322571, by rfl⟩ : syracuseStep 11526857 = 8645143) B8645143
theorem B7684571 : Blo 2023435 7684571 := bstep (se 1 (by rfl) ⟨5763428, by rfl⟩ : syracuseStep 7684571 = 11526857) B11526857
theorem B5123047 : Blo 2023435 5123047 := bstep (se 1 (by rfl) ⟨3842285, by rfl⟩ : syracuseStep 5123047 = 7684571) B7684571
theorem B6830729 : Blo 2023435 6830729 := bstep (se 2 (by rfl) ⟨2561523, by rfl⟩ : syracuseStep 6830729 = 5123047) B5123047
theorem B4553819 : Blo 2023435 4553819 := bstep (se 1 (by rfl) ⟨3415364, by rfl⟩ : syracuseStep 4553819 = 6830729) B6830729
theorem B3035879 : Blo 2023435 3035879 := bstep (se 1 (by rfl) ⟨2276909, by rfl⟩ : syracuseStep 3035879 = 4553819) B4553819
theorem B2023919 : Blo 2023435 2023919 := bstep (se 1 (by rfl) ⟨1517939, by rfl⟩ : syracuseStep 2023919 = 3035879) B3035879
theorem B3035885 : Blo 2023435 3035885 := bbase (se 3 (by rfl) ⟨569228, by rfl⟩ : syracuseStep 3035885 = 1138457) (by norm_num)
theorem B2023923 : Blo 2023435 2023923 := bstep (se 1 (by rfl) ⟨1517942, by rfl⟩ : syracuseStep 2023923 = 3035885) B3035885
theorem B4553837 : Blo 2023435 4553837 := bbase (se 3 (by rfl) ⟨853844, by rfl⟩ : syracuseStep 4553837 = 1707689) (by norm_num)
theorem B3035891 : Blo 2023435 3035891 := bstep (se 1 (by rfl) ⟨2276918, by rfl⟩ : syracuseStep 3035891 = 4553837) B4553837
theorem B2023927 : Blo 2023435 2023927 := bstep (se 1 (by rfl) ⟨1517945, by rfl⟩ : syracuseStep 2023927 = 3035891) B3035891
theorem B3842309 : Blo 2023435 3842309 := bbase (se 4 (by rfl) ⟨360216, by rfl⟩ : syracuseStep 3842309 = 720433) (by norm_num)
theorem B2561539 : Blo 2023435 2561539 := bstep (se 1 (by rfl) ⟨1921154, by rfl⟩ : syracuseStep 2561539 = 3842309) B3842309
theorem B3415385 : Blo 2023435 3415385 := bstep (se 2 (by rfl) ⟨1280769, by rfl⟩ : syracuseStep 3415385 = 2561539) B2561539
theorem B2276923 : Blo 2023435 2276923 := bstep (se 1 (by rfl) ⟨1707692, by rfl⟩ : syracuseStep 2276923 = 3415385) B3415385
theorem B3035897 : Blo 2023435 3035897 := bstep (se 2 (by rfl) ⟨1138461, by rfl⟩ : syracuseStep 3035897 = 2276923) B2276923
theorem B2023931 : Blo 2023435 2023931 := bstep (se 1 (by rfl) ⟨1517948, by rfl⟩ : syracuseStep 2023931 = 3035897) B3035897
theorem B13324085 : Blo 2023435 13324085 := bbase (se 5 (by rfl) ⟨624566, by rfl⟩ : syracuseStep 13324085 = 1249133) (by norm_num)
theorem B8882723 : Blo 2023435 8882723 := bstep (se 1 (by rfl) ⟨6662042, by rfl⟩ : syracuseStep 8882723 = 13324085) B13324085
theorem B23687261 : Blo 2023435 23687261 := bstep (se 3 (by rfl) ⟨4441361, by rfl⟩ : syracuseStep 23687261 = 8882723) B8882723
theorem B15791507 : Blo 2023435 15791507 := bstep (se 1 (by rfl) ⟨11843630, by rfl⟩ : syracuseStep 15791507 = 23687261) B23687261
theorem B10527671 : Blo 2023435 10527671 := bstep (se 1 (by rfl) ⟨7895753, by rfl⟩ : syracuseStep 10527671 = 15791507) B15791507
theorem B28073789 : Blo 2023435 28073789 := bstep (se 3 (by rfl) ⟨5263835, by rfl⟩ : syracuseStep 28073789 = 10527671) B10527671
theorem B18715859 : Blo 2023435 18715859 := bstep (se 1 (by rfl) ⟨14036894, by rfl⟩ : syracuseStep 18715859 = 28073789) B28073789
theorem B12477239 : Blo 2023435 12477239 := bstep (se 1 (by rfl) ⟨9357929, by rfl⟩ : syracuseStep 12477239 = 18715859) B18715859
theorem B8318159 : Blo 2023435 8318159 := bstep (se 1 (by rfl) ⟨6238619, by rfl⟩ : syracuseStep 8318159 = 12477239) B12477239
theorem B5545439 : Blo 2023435 5545439 := bstep (se 1 (by rfl) ⟨4159079, by rfl⟩ : syracuseStep 5545439 = 8318159) B8318159
theorem B3696959 : Blo 2023435 3696959 := bstep (se 1 (by rfl) ⟨2772719, by rfl⟩ : syracuseStep 3696959 = 5545439) B5545439
theorem B9858557 : Blo 2023435 9858557 := bstep (se 3 (by rfl) ⟨1848479, by rfl⟩ : syracuseStep 9858557 = 3696959) B3696959
theorem B6572371 : Blo 2023435 6572371 := bstep (se 1 (by rfl) ⟨4929278, by rfl⟩ : syracuseStep 6572371 = 9858557) B9858557
theorem B8763161 : Blo 2023435 8763161 := bstep (se 2 (by rfl) ⟨3286185, by rfl⟩ : syracuseStep 8763161 = 6572371) B6572371
theorem B23368429 : Blo 2023435 23368429 := bstep (se 3 (by rfl) ⟨4381580, by rfl⟩ : syracuseStep 23368429 = 8763161) B8763161
theorem B31157905 : Blo 2023435 31157905 := bstep (se 2 (by rfl) ⟨11684214, by rfl⟩ : syracuseStep 31157905 = 23368429) B23368429
theorem B41543873 : Blo 2023435 41543873 := bstep (se 2 (by rfl) ⟨15578952, by rfl⟩ : syracuseStep 41543873 = 31157905) B31157905
theorem B27695915 : Blo 2023435 27695915 := bstep (se 1 (by rfl) ⟨20771936, by rfl⟩ : syracuseStep 27695915 = 41543873) B41543873
theorem B18463943 : Blo 2023435 18463943 := bstep (se 1 (by rfl) ⟨13847957, by rfl⟩ : syracuseStep 18463943 = 27695915) B27695915
theorem B12309295 : Blo 2023435 12309295 := bstep (se 1 (by rfl) ⟨9231971, by rfl⟩ : syracuseStep 12309295 = 18463943) B18463943
theorem B16412393 : Blo 2023435 16412393 := bstep (se 2 (by rfl) ⟨6154647, by rfl⟩ : syracuseStep 16412393 = 12309295) B12309295
theorem B43766381 : Blo 2023435 43766381 := bstep (se 3 (by rfl) ⟨8206196, by rfl⟩ : syracuseStep 43766381 = 16412393) B16412393
theorem B29177587 : Blo 2023435 29177587 := bstep (se 1 (by rfl) ⟨21883190, by rfl⟩ : syracuseStep 29177587 = 43766381) B43766381
theorem B38903449 : Blo 2023435 38903449 := bstep (se 2 (by rfl) ⟨14588793, by rfl⟩ : syracuseStep 38903449 = 29177587) B29177587
theorem B51871265 : Blo 2023435 51871265 := bstep (se 2 (by rfl) ⟨19451724, by rfl⟩ : syracuseStep 51871265 = 38903449) B38903449
theorem B34580843 : Blo 2023435 34580843 := bstep (se 1 (by rfl) ⟨25935632, by rfl⟩ : syracuseStep 34580843 = 51871265) B51871265
theorem B23053895 : Blo 2023435 23053895 := bstep (se 1 (by rfl) ⟨17290421, by rfl⟩ : syracuseStep 23053895 = 34580843) B34580843
theorem B15369263 : Blo 2023435 15369263 := bstep (se 1 (by rfl) ⟨11526947, by rfl⟩ : syracuseStep 15369263 = 23053895) B23053895
theorem B10246175 : Blo 2023435 10246175 := bstep (se 1 (by rfl) ⟨7684631, by rfl⟩ : syracuseStep 10246175 = 15369263) B15369263
theorem B6830783 : Blo 2023435 6830783 := bstep (se 1 (by rfl) ⟨5123087, by rfl⟩ : syracuseStep 6830783 = 10246175) B10246175
theorem B4553855 : Blo 2023435 4553855 := bstep (se 1 (by rfl) ⟨3415391, by rfl⟩ : syracuseStep 4553855 = 6830783) B6830783
theorem B3035903 : Blo 2023435 3035903 := bstep (se 1 (by rfl) ⟨2276927, by rfl⟩ : syracuseStep 3035903 = 4553855) B4553855
theorem B2023935 : Blo 2023435 2023935 := bstep (se 1 (by rfl) ⟨1517951, by rfl⟩ : syracuseStep 2023935 = 3035903) B3035903
theorem B3035909 : Blo 2023435 3035909 := bbase (se 4 (by rfl) ⟨284616, by rfl⟩ : syracuseStep 3035909 = 569233) (by norm_num)
theorem B2023939 : Blo 2023435 2023939 := bstep (se 1 (by rfl) ⟨1517954, by rfl⟩ : syracuseStep 2023939 = 3035909) B3035909
theorem B3415405 : Blo 2023435 3415405 := bbase (se 3 (by rfl) ⟨640388, by rfl⟩ : syracuseStep 3415405 = 1280777) (by norm_num)
theorem B4553873 : Blo 2023435 4553873 := bstep (se 2 (by rfl) ⟨1707702, by rfl⟩ : syracuseStep 4553873 = 3415405) B3415405
theorem B3035915 : Blo 2023435 3035915 := bstep (se 1 (by rfl) ⟨2276936, by rfl⟩ : syracuseStep 3035915 = 4553873) B4553873
theorem B2023943 : Blo 2023435 2023943 := bstep (se 1 (by rfl) ⟨1517957, by rfl⟩ : syracuseStep 2023943 = 3035915) B3035915
theorem B2276941 : Blo 2023435 2276941 := bbase (se 3 (by rfl) ⟨426926, by rfl⟩ : syracuseStep 2276941 = 853853) (by norm_num)
theorem B3035921 : Blo 2023435 3035921 := bstep (se 2 (by rfl) ⟨1138470, by rfl⟩ : syracuseStep 3035921 = 2276941) B2276941
theorem B2023947 : Blo 2023435 2023947 := bstep (se 1 (by rfl) ⟨1517960, by rfl⟩ : syracuseStep 2023947 = 3035921) B3035921
theorem B6830837 : Blo 2023435 6830837 := bbase (se 5 (by rfl) ⟨320195, by rfl⟩ : syracuseStep 6830837 = 640391) (by norm_num)
theorem B4553891 : Blo 2023435 4553891 := bstep (se 1 (by rfl) ⟨3415418, by rfl⟩ : syracuseStep 4553891 = 6830837) B6830837
theorem B3035927 : Blo 2023435 3035927 := bstep (se 1 (by rfl) ⟨2276945, by rfl⟩ : syracuseStep 3035927 = 4553891) B4553891
theorem B2023951 : Blo 2023435 2023951 := bstep (se 1 (by rfl) ⟨1517963, by rfl⟩ : syracuseStep 2023951 = 3035927) B3035927
theorem B3035933 : Blo 2023435 3035933 := bbase (se 3 (by rfl) ⟨569237, by rfl⟩ : syracuseStep 3035933 = 1138475) (by norm_num)
theorem B2023955 : Blo 2023435 2023955 := bstep (se 1 (by rfl) ⟨1517966, by rfl⟩ : syracuseStep 2023955 = 3035933) B3035933
theorem B4553909 : Blo 2023435 4553909 := bbase (se 5 (by rfl) ⟨213464, by rfl⟩ : syracuseStep 4553909 = 426929) (by norm_num)
theorem B3035939 : Blo 2023435 3035939 := bstep (se 1 (by rfl) ⟨2276954, by rfl⟩ : syracuseStep 3035939 = 4553909) B4553909
theorem B2023959 : Blo 2023435 2023959 := bstep (se 1 (by rfl) ⟨1517969, by rfl⟩ : syracuseStep 2023959 = 3035939) B3035939
theorem B2161333 : Blo 2023435 2161333 := bbase (se 5 (by rfl) ⟨101312, by rfl⟩ : syracuseStep 2161333 = 202625) (by norm_num)
theorem B11527109 : Blo 2023435 11527109 := bstep (se 4 (by rfl) ⟨1080666, by rfl⟩ : syracuseStep 11527109 = 2161333) B2161333
theorem B7684739 : Blo 2023435 7684739 := bstep (se 1 (by rfl) ⟨5763554, by rfl⟩ : syracuseStep 7684739 = 11527109) B11527109
theorem B5123159 : Blo 2023435 5123159 := bstep (se 1 (by rfl) ⟨3842369, by rfl⟩ : syracuseStep 5123159 = 7684739) B7684739
theorem B3415439 : Blo 2023435 3415439 := bstep (se 1 (by rfl) ⟨2561579, by rfl⟩ : syracuseStep 3415439 = 5123159) B5123159
theorem B2276959 : Blo 2023435 2276959 := bstep (se 1 (by rfl) ⟨1707719, by rfl⟩ : syracuseStep 2276959 = 3415439) B3415439
theorem B3035945 : Blo 2023435 3035945 := bstep (se 2 (by rfl) ⟨1138479, by rfl⟩ : syracuseStep 3035945 = 2276959) B2276959
theorem B2023963 : Blo 2023435 2023963 := bstep (se 1 (by rfl) ⟨1517972, by rfl⟩ : syracuseStep 2023963 = 3035945) B3035945
theorem B2161337 : Blo 2023435 2161337 := bbase (se 2 (by rfl) ⟨810501, by rfl⟩ : syracuseStep 2161337 = 1621003) (by norm_num)
theorem B5763565 : Blo 2023435 5763565 := bstep (se 3 (by rfl) ⟨1080668, by rfl⟩ : syracuseStep 5763565 = 2161337) B2161337
theorem B7684753 : Blo 2023435 7684753 := bstep (se 2 (by rfl) ⟨2881782, by rfl⟩ : syracuseStep 7684753 = 5763565) B5763565
theorem B10246337 : Blo 2023435 10246337 := bstep (se 2 (by rfl) ⟨3842376, by rfl⟩ : syracuseStep 10246337 = 7684753) B7684753
theorem B6830891 : Blo 2023435 6830891 := bstep (se 1 (by rfl) ⟨5123168, by rfl⟩ : syracuseStep 6830891 = 10246337) B10246337
theorem B4553927 : Blo 2023435 4553927 := bstep (se 1 (by rfl) ⟨3415445, by rfl⟩ : syracuseStep 4553927 = 6830891) B6830891
theorem B3035951 : Blo 2023435 3035951 := bstep (se 1 (by rfl) ⟨2276963, by rfl⟩ : syracuseStep 3035951 = 4553927) B4553927
theorem B2023967 : Blo 2023435 2023967 := bstep (se 1 (by rfl) ⟨1517975, by rfl⟩ : syracuseStep 2023967 = 3035951) B3035951
theorem B3035957 : Blo 2023435 3035957 := bbase (se 5 (by rfl) ⟨142310, by rfl⟩ : syracuseStep 3035957 = 284621) (by norm_num)
theorem B2023971 : Blo 2023435 2023971 := bstep (se 1 (by rfl) ⟨1517978, by rfl⟩ : syracuseStep 2023971 = 3035957) B3035957
theorem B5123189 : Blo 2023435 5123189 := bbase (se 5 (by rfl) ⟨240149, by rfl⟩ : syracuseStep 5123189 = 480299) (by norm_num)
theorem B3415459 : Blo 2023435 3415459 := bstep (se 1 (by rfl) ⟨2561594, by rfl⟩ : syracuseStep 3415459 = 5123189) B5123189
theorem B4553945 : Blo 2023435 4553945 := bstep (se 2 (by rfl) ⟨1707729, by rfl⟩ : syracuseStep 4553945 = 3415459) B3415459
theorem B3035963 : Blo 2023435 3035963 := bstep (se 1 (by rfl) ⟨2276972, by rfl⟩ : syracuseStep 3035963 = 4553945) B4553945
theorem B2023975 : Blo 2023435 2023975 := bstep (se 1 (by rfl) ⟨1517981, by rfl⟩ : syracuseStep 2023975 = 3035963) B3035963
theorem B2276977 : Blo 2023435 2276977 := bbase (se 2 (by rfl) ⟨853866, by rfl⟩ : syracuseStep 2276977 = 1707733) (by norm_num)
theorem B3035969 : Blo 2023435 3035969 := bstep (se 2 (by rfl) ⟨1138488, by rfl⟩ : syracuseStep 3035969 = 2276977) B2276977
theorem B2023979 : Blo 2023435 2023979 := bstep (se 1 (by rfl) ⟨1517984, by rfl⟩ : syracuseStep 2023979 = 3035969) B3035969
theorem B5193109 : Blo 2023435 5193109 := bbase (se 6 (by rfl) ⟨121713, by rfl⟩ : syracuseStep 5193109 = 243427) (by norm_num)
theorem B6924145 : Blo 2023435 6924145 := bstep (se 2 (by rfl) ⟨2596554, by rfl⟩ : syracuseStep 6924145 = 5193109) B5193109
theorem B9232193 : Blo 2023435 9232193 := bstep (se 2 (by rfl) ⟨3462072, by rfl⟩ : syracuseStep 9232193 = 6924145) B6924145
theorem B6154795 : Blo 2023435 6154795 := bstep (se 1 (by rfl) ⟨4616096, by rfl⟩ : syracuseStep 6154795 = 9232193) B9232193
theorem B32825573 : Blo 2023435 32825573 := bstep (se 4 (by rfl) ⟨3077397, by rfl⟩ : syracuseStep 32825573 = 6154795) B6154795
theorem B21883715 : Blo 2023435 21883715 := bstep (se 1 (by rfl) ⟨16412786, by rfl⟩ : syracuseStep 21883715 = 32825573) B32825573
theorem B14589143 : Blo 2023435 14589143 := bstep (se 1 (by rfl) ⟨10941857, by rfl⟩ : syracuseStep 14589143 = 21883715) B21883715
theorem B9726095 : Blo 2023435 9726095 := bstep (se 1 (by rfl) ⟨7294571, by rfl⟩ : syracuseStep 9726095 = 14589143) B14589143
theorem B6484063 : Blo 2023435 6484063 := bstep (se 1 (by rfl) ⟨4863047, by rfl⟩ : syracuseStep 6484063 = 9726095) B9726095
theorem B8645417 : Blo 2023435 8645417 := bstep (se 2 (by rfl) ⟨3242031, by rfl⟩ : syracuseStep 8645417 = 6484063) B6484063
theorem B5763611 : Blo 2023435 5763611 := bstep (se 1 (by rfl) ⟨4322708, by rfl⟩ : syracuseStep 5763611 = 8645417) B8645417
theorem B3842407 : Blo 2023435 3842407 := bstep (se 1 (by rfl) ⟨2881805, by rfl⟩ : syracuseStep 3842407 = 5763611) B5763611
theorem B5123209 : Blo 2023435 5123209 := bstep (se 2 (by rfl) ⟨1921203, by rfl⟩ : syracuseStep 5123209 = 3842407) B3842407
theorem B6830945 : Blo 2023435 6830945 := bstep (se 2 (by rfl) ⟨2561604, by rfl⟩ : syracuseStep 6830945 = 5123209) B5123209
theorem B4553963 : Blo 2023435 4553963 := bstep (se 1 (by rfl) ⟨3415472, by rfl⟩ : syracuseStep 4553963 = 6830945) B6830945
theorem B3035975 : Blo 2023435 3035975 := bstep (se 1 (by rfl) ⟨2276981, by rfl⟩ : syracuseStep 3035975 = 4553963) B4553963
theorem B2023983 : Blo 2023435 2023983 := bstep (se 1 (by rfl) ⟨1517987, by rfl⟩ : syracuseStep 2023983 = 3035975) B3035975
theorem B3035981 : Blo 2023435 3035981 := bbase (se 3 (by rfl) ⟨569246, by rfl⟩ : syracuseStep 3035981 = 1138493) (by norm_num)
theorem B2023987 : Blo 2023435 2023987 := bstep (se 1 (by rfl) ⟨1517990, by rfl⟩ : syracuseStep 2023987 = 3035981) B3035981
theorem B4553981 : Blo 2023435 4553981 := bbase (se 3 (by rfl) ⟨853871, by rfl⟩ : syracuseStep 4553981 = 1707743) (by norm_num)
theorem B3035987 : Blo 2023435 3035987 := bstep (se 1 (by rfl) ⟨2276990, by rfl⟩ : syracuseStep 3035987 = 4553981) B4553981
theorem B2023991 : Blo 2023435 2023991 := bstep (se 1 (by rfl) ⟨1517993, by rfl⟩ : syracuseStep 2023991 = 3035987) B3035987
theorem B3415493 : Blo 2023435 3415493 := bbase (se 4 (by rfl) ⟨320202, by rfl⟩ : syracuseStep 3415493 = 640405) (by norm_num)
theorem B2276995 : Blo 2023435 2276995 := bstep (se 1 (by rfl) ⟨1707746, by rfl⟩ : syracuseStep 2276995 = 3415493) B3415493
theorem B3035993 : Blo 2023435 3035993 := bstep (se 2 (by rfl) ⟨1138497, by rfl⟩ : syracuseStep 3035993 = 2276995) B2276995
theorem B2023995 : Blo 2023435 2023995 := bstep (se 1 (by rfl) ⟨1517996, by rfl⟩ : syracuseStep 2023995 = 3035993) B3035993
theorem B15369749 : Blo 2023435 15369749 := bbase (se 6 (by rfl) ⟨360228, by rfl⟩ : syracuseStep 15369749 = 720457) (by norm_num)
theorem B10246499 : Blo 2023435 10246499 := bstep (se 1 (by rfl) ⟨7684874, by rfl⟩ : syracuseStep 10246499 = 15369749) B15369749
theorem B6830999 : Blo 2023435 6830999 := bstep (se 1 (by rfl) ⟨5123249, by rfl⟩ : syracuseStep 6830999 = 10246499) B10246499
theorem B4553999 : Blo 2023435 4553999 := bstep (se 1 (by rfl) ⟨3415499, by rfl⟩ : syracuseStep 4553999 = 6830999) B6830999
theorem B3035999 : Blo 2023435 3035999 := bstep (se 1 (by rfl) ⟨2276999, by rfl⟩ : syracuseStep 3035999 = 4553999) B4553999
theorem B2023999 : Blo 2023435 2023999 := bstep (se 1 (by rfl) ⟨1517999, by rfl⟩ : syracuseStep 2023999 = 3035999) B3035999
theorem B3036005 : Blo 2023435 3036005 := bbase (se 4 (by rfl) ⟨284625, by rfl⟩ : syracuseStep 3036005 = 569251) (by norm_num)
theorem B2024003 : Blo 2023435 2024003 := bstep (se 1 (by rfl) ⟨1518002, by rfl⟩ : syracuseStep 2024003 = 3036005) B3036005
theorem B3842453 : Blo 2023435 3842453 := bbase (se 6 (by rfl) ⟨90057, by rfl⟩ : syracuseStep 3842453 = 180115) (by norm_num)
theorem B2561635 : Blo 2023435 2561635 := bstep (se 1 (by rfl) ⟨1921226, by rfl⟩ : syracuseStep 2561635 = 3842453) B3842453
theorem B3415513 : Blo 2023435 3415513 := bstep (se 2 (by rfl) ⟨1280817, by rfl⟩ : syracuseStep 3415513 = 2561635) B2561635
theorem B4554017 : Blo 2023435 4554017 := bstep (se 2 (by rfl) ⟨1707756, by rfl⟩ : syracuseStep 4554017 = 3415513) B3415513
theorem B3036011 : Blo 2023435 3036011 := bstep (se 1 (by rfl) ⟨2277008, by rfl⟩ : syracuseStep 3036011 = 4554017) B4554017
theorem B2024007 : Blo 2023435 2024007 := bstep (se 1 (by rfl) ⟨1518005, by rfl⟩ : syracuseStep 2024007 = 3036011) B3036011
theorem B2277013 : Blo 2023435 2277013 := bbase (se 6 (by rfl) ⟨53367, by rfl⟩ : syracuseStep 2277013 = 106735) (by norm_num)
theorem B3036017 : Blo 2023435 3036017 := bstep (se 2 (by rfl) ⟨1138506, by rfl⟩ : syracuseStep 3036017 = 2277013) B2277013
theorem B2024011 : Blo 2023435 2024011 := bstep (se 1 (by rfl) ⟨1518008, by rfl⟩ : syracuseStep 2024011 = 3036017) B3036017
theorem B2561645 : Blo 2023435 2561645 := bbase (se 3 (by rfl) ⟨480308, by rfl⟩ : syracuseStep 2561645 = 960617) (by norm_num)
theorem B6831053 : Blo 2023435 6831053 := bstep (se 3 (by rfl) ⟨1280822, by rfl⟩ : syracuseStep 6831053 = 2561645) B2561645
theorem B4554035 : Blo 2023435 4554035 := bstep (se 1 (by rfl) ⟨3415526, by rfl⟩ : syracuseStep 4554035 = 6831053) B6831053
theorem B3036023 : Blo 2023435 3036023 := bstep (se 1 (by rfl) ⟨2277017, by rfl⟩ : syracuseStep 3036023 = 4554035) B4554035
theorem B2024015 : Blo 2023435 2024015 := bstep (se 1 (by rfl) ⟨1518011, by rfl⟩ : syracuseStep 2024015 = 3036023) B3036023
theorem B3036029 : Blo 2023435 3036029 := bbase (se 3 (by rfl) ⟨569255, by rfl⟩ : syracuseStep 3036029 = 1138511) (by norm_num)
theorem B2024019 : Blo 2023435 2024019 := bstep (se 1 (by rfl) ⟨1518014, by rfl⟩ : syracuseStep 2024019 = 3036029) B3036029
theorem B4554053 : Blo 2023435 4554053 := bbase (se 4 (by rfl) ⟨426942, by rfl⟩ : syracuseStep 4554053 = 853885) (by norm_num)
theorem B3036035 : Blo 2023435 3036035 := bstep (se 1 (by rfl) ⟨2277026, by rfl⟩ : syracuseStep 3036035 = 4554053) B4554053
theorem B2024023 : Blo 2023435 2024023 := bstep (se 1 (by rfl) ⟨1518017, by rfl⟩ : syracuseStep 2024023 = 3036035) B3036035
theorem B2431577 : Blo 2023435 2431577 := bbase (se 2 (by rfl) ⟨911841, by rfl⟩ : syracuseStep 2431577 = 1823683) (by norm_num)
theorem B6484205 : Blo 2023435 6484205 := bstep (se 3 (by rfl) ⟨1215788, by rfl⟩ : syracuseStep 6484205 = 2431577) B2431577
theorem B4322803 : Blo 2023435 4322803 := bstep (se 1 (by rfl) ⟨3242102, by rfl⟩ : syracuseStep 4322803 = 6484205) B6484205
theorem B5763737 : Blo 2023435 5763737 := bstep (se 2 (by rfl) ⟨2161401, by rfl⟩ : syracuseStep 5763737 = 4322803) B4322803
theorem B3842491 : Blo 2023435 3842491 := bstep (se 1 (by rfl) ⟨2881868, by rfl⟩ : syracuseStep 3842491 = 5763737) B5763737
theorem B5123321 : Blo 2023435 5123321 := bstep (se 2 (by rfl) ⟨1921245, by rfl⟩ : syracuseStep 5123321 = 3842491) B3842491
theorem B3415547 : Blo 2023435 3415547 := bstep (se 1 (by rfl) ⟨2561660, by rfl⟩ : syracuseStep 3415547 = 5123321) B5123321
theorem B2277031 : Blo 2023435 2277031 := bstep (se 1 (by rfl) ⟨1707773, by rfl⟩ : syracuseStep 2277031 = 3415547) B3415547
theorem B3036041 : Blo 2023435 3036041 := bstep (se 2 (by rfl) ⟨1138515, by rfl⟩ : syracuseStep 3036041 = 2277031) B2277031
theorem B2024027 : Blo 2023435 2024027 := bstep (se 1 (by rfl) ⟨1518020, by rfl⟩ : syracuseStep 2024027 = 3036041) B3036041
theorem B10246661 : Blo 2023435 10246661 := bbase (se 4 (by rfl) ⟨960624, by rfl⟩ : syracuseStep 10246661 = 1921249) (by norm_num)
theorem B6831107 : Blo 2023435 6831107 := bstep (se 1 (by rfl) ⟨5123330, by rfl⟩ : syracuseStep 6831107 = 10246661) B10246661
theorem B4554071 : Blo 2023435 4554071 := bstep (se 1 (by rfl) ⟨3415553, by rfl⟩ : syracuseStep 4554071 = 6831107) B6831107
theorem B3036047 : Blo 2023435 3036047 := bstep (se 1 (by rfl) ⟨2277035, by rfl⟩ : syracuseStep 3036047 = 4554071) B4554071
theorem B2024031 : Blo 2023435 2024031 := bstep (se 1 (by rfl) ⟨1518023, by rfl⟩ : syracuseStep 2024031 = 3036047) B3036047
theorem B3036053 : Blo 2023435 3036053 := bbase (se 6 (by rfl) ⟨71157, by rfl⟩ : syracuseStep 3036053 = 142315) (by norm_num)
theorem B2024035 : Blo 2023435 2024035 := bstep (se 1 (by rfl) ⟨1518026, by rfl⟩ : syracuseStep 2024035 = 3036053) B3036053
theorem B11527541 : Blo 2023435 11527541 := bbase (se 5 (by rfl) ⟨540353, by rfl⟩ : syracuseStep 11527541 = 1080707) (by norm_num)
theorem B7685027 : Blo 2023435 7685027 := bstep (se 1 (by rfl) ⟨5763770, by rfl⟩ : syracuseStep 7685027 = 11527541) B11527541
theorem B5123351 : Blo 2023435 5123351 := bstep (se 1 (by rfl) ⟨3842513, by rfl⟩ : syracuseStep 5123351 = 7685027) B7685027
theorem B3415567 : Blo 2023435 3415567 := bstep (se 1 (by rfl) ⟨2561675, by rfl⟩ : syracuseStep 3415567 = 5123351) B5123351
theorem B4554089 : Blo 2023435 4554089 := bstep (se 2 (by rfl) ⟨1707783, by rfl⟩ : syracuseStep 4554089 = 3415567) B3415567
theorem B3036059 : Blo 2023435 3036059 := bstep (se 1 (by rfl) ⟨2277044, by rfl⟩ : syracuseStep 3036059 = 4554089) B4554089
theorem B2024039 : Blo 2023435 2024039 := bstep (se 1 (by rfl) ⟨1518029, by rfl⟩ : syracuseStep 2024039 = 3036059) B3036059
theorem B2277049 : Blo 2023435 2277049 := bbase (se 2 (by rfl) ⟨853893, by rfl⟩ : syracuseStep 2277049 = 1707787) (by norm_num)
theorem B3036065 : Blo 2023435 3036065 := bstep (se 2 (by rfl) ⟨1138524, by rfl⟩ : syracuseStep 3036065 = 2277049) B2277049
theorem B2024043 : Blo 2023435 2024043 := bstep (se 1 (by rfl) ⟨1518032, by rfl⟩ : syracuseStep 2024043 = 3036065) B3036065
theorem B4322845 : Blo 2023435 4322845 := bbase (se 3 (by rfl) ⟨810533, by rfl⟩ : syracuseStep 4322845 = 1621067) (by norm_num)
theorem B5763793 : Blo 2023435 5763793 := bstep (se 2 (by rfl) ⟨2161422, by rfl⟩ : syracuseStep 5763793 = 4322845) B4322845
theorem B7685057 : Blo 2023435 7685057 := bstep (se 2 (by rfl) ⟨2881896, by rfl⟩ : syracuseStep 7685057 = 5763793) B5763793
theorem B5123371 : Blo 2023435 5123371 := bstep (se 1 (by rfl) ⟨3842528, by rfl⟩ : syracuseStep 5123371 = 7685057) B7685057
theorem B6831161 : Blo 2023435 6831161 := bstep (se 2 (by rfl) ⟨2561685, by rfl⟩ : syracuseStep 6831161 = 5123371) B5123371
theorem B4554107 : Blo 2023435 4554107 := bstep (se 1 (by rfl) ⟨3415580, by rfl⟩ : syracuseStep 4554107 = 6831161) B6831161
theorem B3036071 : Blo 2023435 3036071 := bstep (se 1 (by rfl) ⟨2277053, by rfl⟩ : syracuseStep 3036071 = 4554107) B4554107
theorem B2024047 : Blo 2023435 2024047 := bstep (se 1 (by rfl) ⟨1518035, by rfl⟩ : syracuseStep 2024047 = 3036071) B3036071
theorem B3036077 : Blo 2023435 3036077 := bbase (se 3 (by rfl) ⟨569264, by rfl⟩ : syracuseStep 3036077 = 1138529) (by norm_num)
theorem B2024051 : Blo 2023435 2024051 := bstep (se 1 (by rfl) ⟨1518038, by rfl⟩ : syracuseStep 2024051 = 3036077) B3036077
theorem B4554125 : Blo 2023435 4554125 := bbase (se 3 (by rfl) ⟨853898, by rfl⟩ : syracuseStep 4554125 = 1707797) (by norm_num)
theorem B3036083 : Blo 2023435 3036083 := bstep (se 1 (by rfl) ⟨2277062, by rfl⟩ : syracuseStep 3036083 = 4554125) B4554125
theorem B2024055 : Blo 2023435 2024055 := bstep (se 1 (by rfl) ⟨1518041, by rfl⟩ : syracuseStep 2024055 = 3036083) B3036083
theorem B2561701 : Blo 2023435 2561701 := bbase (se 4 (by rfl) ⟨240159, by rfl⟩ : syracuseStep 2561701 = 480319) (by norm_num)
theorem B3415601 : Blo 2023435 3415601 := bstep (se 2 (by rfl) ⟨1280850, by rfl⟩ : syracuseStep 3415601 = 2561701) B2561701
theorem B2277067 : Blo 2023435 2277067 := bstep (se 1 (by rfl) ⟨1707800, by rfl⟩ : syracuseStep 2277067 = 3415601) B3415601
theorem B3036089 : Blo 2023435 3036089 := bstep (se 2 (by rfl) ⟨1138533, by rfl⟩ : syracuseStep 3036089 = 2277067) B2277067
theorem B2024059 : Blo 2023435 2024059 := bstep (se 1 (by rfl) ⟨1518044, by rfl⟩ : syracuseStep 2024059 = 3036089) B3036089
theorem B32452757 : Blo 2023435 32452757 := bbase (se 6 (by rfl) ⟨760611, by rfl⟩ : syracuseStep 32452757 = 1521223) (by norm_num)
theorem B21635171 : Blo 2023435 21635171 := bstep (se 1 (by rfl) ⟨16226378, by rfl⟩ : syracuseStep 21635171 = 32452757) B32452757
theorem B14423447 : Blo 2023435 14423447 := bstep (se 1 (by rfl) ⟨10817585, by rfl⟩ : syracuseStep 14423447 = 21635171) B21635171
theorem B9615631 : Blo 2023435 9615631 := bstep (se 1 (by rfl) ⟨7211723, by rfl⟩ : syracuseStep 9615631 = 14423447) B14423447
theorem B12820841 : Blo 2023435 12820841 := bstep (se 2 (by rfl) ⟨4807815, by rfl⟩ : syracuseStep 12820841 = 9615631) B9615631
theorem B8547227 : Blo 2023435 8547227 := bstep (se 1 (by rfl) ⟨6410420, by rfl⟩ : syracuseStep 8547227 = 12820841) B12820841
theorem B5698151 : Blo 2023435 5698151 := bstep (se 1 (by rfl) ⟨4273613, by rfl⟩ : syracuseStep 5698151 = 8547227) B8547227
theorem B3798767 : Blo 2023435 3798767 := bstep (se 1 (by rfl) ⟨2849075, by rfl⟩ : syracuseStep 3798767 = 5698151) B5698151
theorem B2532511 : Blo 2023435 2532511 := bstep (se 1 (by rfl) ⟨1899383, by rfl⟩ : syracuseStep 2532511 = 3798767) B3798767
theorem B13506725 : Blo 2023435 13506725 := bstep (se 4 (by rfl) ⟨1266255, by rfl⟩ : syracuseStep 13506725 = 2532511) B2532511
theorem B9004483 : Blo 2023435 9004483 := bstep (se 1 (by rfl) ⟨6753362, by rfl⟩ : syracuseStep 9004483 = 13506725) B13506725
theorem B12005977 : Blo 2023435 12005977 := bstep (se 2 (by rfl) ⟨4502241, by rfl⟩ : syracuseStep 12005977 = 9004483) B9004483
theorem B16007969 : Blo 2023435 16007969 := bstep (se 2 (by rfl) ⟨6002988, by rfl⟩ : syracuseStep 16007969 = 12005977) B12005977
theorem B42687917 : Blo 2023435 42687917 := bstep (se 3 (by rfl) ⟨8003984, by rfl⟩ : syracuseStep 42687917 = 16007969) B16007969
theorem B28458611 : Blo 2023435 28458611 := bstep (se 1 (by rfl) ⟨21343958, by rfl⟩ : syracuseStep 28458611 = 42687917) B42687917
theorem B18972407 : Blo 2023435 18972407 := bstep (se 1 (by rfl) ⟨14229305, by rfl⟩ : syracuseStep 18972407 = 28458611) B28458611
theorem B12648271 : Blo 2023435 12648271 := bstep (se 1 (by rfl) ⟨9486203, by rfl⟩ : syracuseStep 12648271 = 18972407) B18972407
theorem B16864361 : Blo 2023435 16864361 := bstep (se 2 (by rfl) ⟨6324135, by rfl⟩ : syracuseStep 16864361 = 12648271) B12648271
theorem B11242907 : Blo 2023435 11242907 := bstep (se 1 (by rfl) ⟨8432180, by rfl⟩ : syracuseStep 11242907 = 16864361) B16864361
theorem B7495271 : Blo 2023435 7495271 := bstep (se 1 (by rfl) ⟨5621453, by rfl⟩ : syracuseStep 7495271 = 11242907) B11242907
theorem B4996847 : Blo 2023435 4996847 := bstep (se 1 (by rfl) ⟨3747635, by rfl⟩ : syracuseStep 4996847 = 7495271) B7495271
theorem B13324925 : Blo 2023435 13324925 := bstep (se 3 (by rfl) ⟨2498423, by rfl⟩ : syracuseStep 13324925 = 4996847) B4996847
theorem B8883283 : Blo 2023435 8883283 := bstep (se 1 (by rfl) ⟨6662462, by rfl⟩ : syracuseStep 8883283 = 13324925) B13324925
theorem B11844377 : Blo 2023435 11844377 := bstep (se 2 (by rfl) ⟨4441641, by rfl⟩ : syracuseStep 11844377 = 8883283) B8883283
theorem B7896251 : Blo 2023435 7896251 := bstep (se 1 (by rfl) ⟨5922188, by rfl⟩ : syracuseStep 7896251 = 11844377) B11844377
theorem B21056669 : Blo 2023435 21056669 := bstep (se 3 (by rfl) ⟨3948125, by rfl⟩ : syracuseStep 21056669 = 7896251) B7896251
theorem B14037779 : Blo 2023435 14037779 := bstep (se 1 (by rfl) ⟨10528334, by rfl⟩ : syracuseStep 14037779 = 21056669) B21056669
theorem B9358519 : Blo 2023435 9358519 := bstep (se 1 (by rfl) ⟨7018889, by rfl⟩ : syracuseStep 9358519 = 14037779) B14037779
theorem B12478025 : Blo 2023435 12478025 := bstep (se 2 (by rfl) ⟨4679259, by rfl⟩ : syracuseStep 12478025 = 9358519) B9358519
theorem B8318683 : Blo 2023435 8318683 := bstep (se 1 (by rfl) ⟨6239012, by rfl⟩ : syracuseStep 8318683 = 12478025) B12478025
theorem B11091577 : Blo 2023435 11091577 := bstep (se 2 (by rfl) ⟨4159341, by rfl⟩ : syracuseStep 11091577 = 8318683) B8318683
theorem B14788769 : Blo 2023435 14788769 := bstep (se 2 (by rfl) ⟨5545788, by rfl⟩ : syracuseStep 14788769 = 11091577) B11091577
theorem B39436717 : Blo 2023435 39436717 := bstep (se 3 (by rfl) ⟨7394384, by rfl⟩ : syracuseStep 39436717 = 14788769) B14788769
theorem B52582289 : Blo 2023435 52582289 := bstep (se 2 (by rfl) ⟨19718358, by rfl⟩ : syracuseStep 52582289 = 39436717) B39436717
theorem B140219437 : Blo 2023435 140219437 := bstep (se 3 (by rfl) ⟨26291144, by rfl⟩ : syracuseStep 140219437 = 52582289) B52582289
theorem B186959249 : Blo 2023435 186959249 := bstep (se 2 (by rfl) ⟨70109718, by rfl⟩ : syracuseStep 186959249 = 140219437) B140219437
theorem B124639499 : Blo 2023435 124639499 := bstep (se 1 (by rfl) ⟨93479624, by rfl⟩ : syracuseStep 124639499 = 186959249) B186959249
theorem B83092999 : Blo 2023435 83092999 := bstep (se 1 (by rfl) ⟨62319749, by rfl⟩ : syracuseStep 83092999 = 124639499) B124639499
theorem B110790665 : Blo 2023435 110790665 := bstep (se 2 (by rfl) ⟨41546499, by rfl⟩ : syracuseStep 110790665 = 83092999) B83092999
theorem B73860443 : Blo 2023435 73860443 := bstep (se 1 (by rfl) ⟨55395332, by rfl⟩ : syracuseStep 73860443 = 110790665) B110790665
theorem B49240295 : Blo 2023435 49240295 := bstep (se 1 (by rfl) ⟨36930221, by rfl⟩ : syracuseStep 49240295 = 73860443) B73860443
theorem B32826863 : Blo 2023435 32826863 := bstep (se 1 (by rfl) ⟨24620147, by rfl⟩ : syracuseStep 32826863 = 49240295) B49240295
theorem B21884575 : Blo 2023435 21884575 := bstep (se 1 (by rfl) ⟨16413431, by rfl⟩ : syracuseStep 21884575 = 32826863) B32826863
theorem B29179433 : Blo 2023435 29179433 := bstep (se 2 (by rfl) ⟨10942287, by rfl⟩ : syracuseStep 29179433 = 21884575) B21884575
theorem B19452955 : Blo 2023435 19452955 := bstep (se 1 (by rfl) ⟨14589716, by rfl⟩ : syracuseStep 19452955 = 29179433) B29179433
theorem B25937273 : Blo 2023435 25937273 := bstep (se 2 (by rfl) ⟨9726477, by rfl⟩ : syracuseStep 25937273 = 19452955) B19452955
theorem B17291515 : Blo 2023435 17291515 := bstep (se 1 (by rfl) ⟨12968636, by rfl⟩ : syracuseStep 17291515 = 25937273) B25937273
theorem B23055353 : Blo 2023435 23055353 := bstep (se 2 (by rfl) ⟨8645757, by rfl⟩ : syracuseStep 23055353 = 17291515) B17291515
theorem B15370235 : Blo 2023435 15370235 := bstep (se 1 (by rfl) ⟨11527676, by rfl⟩ : syracuseStep 15370235 = 23055353) B23055353
theorem B10246823 : Blo 2023435 10246823 := bstep (se 1 (by rfl) ⟨7685117, by rfl⟩ : syracuseStep 10246823 = 15370235) B15370235
theorem B6831215 : Blo 2023435 6831215 := bstep (se 1 (by rfl) ⟨5123411, by rfl⟩ : syracuseStep 6831215 = 10246823) B10246823
theorem B4554143 : Blo 2023435 4554143 := bstep (se 1 (by rfl) ⟨3415607, by rfl⟩ : syracuseStep 4554143 = 6831215) B6831215
theorem B3036095 : Blo 2023435 3036095 := bstep (se 1 (by rfl) ⟨2277071, by rfl⟩ : syracuseStep 3036095 = 4554143) B4554143
theorem B2024063 : Blo 2023435 2024063 := bstep (se 1 (by rfl) ⟨1518047, by rfl⟩ : syracuseStep 2024063 = 3036095) B3036095
theorem B3036101 : Blo 2023435 3036101 := bbase (se 4 (by rfl) ⟨284634, by rfl⟩ : syracuseStep 3036101 = 569269) (by norm_num)
theorem B2024067 : Blo 2023435 2024067 := bstep (se 1 (by rfl) ⟨1518050, by rfl⟩ : syracuseStep 2024067 = 3036101) B3036101
theorem B3415621 : Blo 2023435 3415621 := bbase (se 4 (by rfl) ⟨320214, by rfl⟩ : syracuseStep 3415621 = 640429) (by norm_num)
theorem B4554161 : Blo 2023435 4554161 := bstep (se 2 (by rfl) ⟨1707810, by rfl⟩ : syracuseStep 4554161 = 3415621) B3415621
theorem B3036107 : Blo 2023435 3036107 := bstep (se 1 (by rfl) ⟨2277080, by rfl⟩ : syracuseStep 3036107 = 4554161) B4554161
theorem B2024071 : Blo 2023435 2024071 := bstep (se 1 (by rfl) ⟨1518053, by rfl⟩ : syracuseStep 2024071 = 3036107) B3036107
theorem B2277085 : Blo 2023435 2277085 := bbase (se 3 (by rfl) ⟨426953, by rfl⟩ : syracuseStep 2277085 = 853907) (by norm_num)
theorem B3036113 : Blo 2023435 3036113 := bstep (se 2 (by rfl) ⟨1138542, by rfl⟩ : syracuseStep 3036113 = 2277085) B2277085
theorem B2024075 : Blo 2023435 2024075 := bstep (se 1 (by rfl) ⟨1518056, by rfl⟩ : syracuseStep 2024075 = 3036113) B3036113
theorem B6831269 : Blo 2023435 6831269 := bbase (se 4 (by rfl) ⟨640431, by rfl⟩ : syracuseStep 6831269 = 1280863) (by norm_num)
theorem B4554179 : Blo 2023435 4554179 := bstep (se 1 (by rfl) ⟨3415634, by rfl⟩ : syracuseStep 4554179 = 6831269) B6831269
theorem B3036119 : Blo 2023435 3036119 := bstep (se 1 (by rfl) ⟨2277089, by rfl⟩ : syracuseStep 3036119 = 4554179) B4554179
theorem B2024079 : Blo 2023435 2024079 := bstep (se 1 (by rfl) ⟨1518059, by rfl⟩ : syracuseStep 2024079 = 3036119) B3036119
theorem B3036125 : Blo 2023435 3036125 := bbase (se 3 (by rfl) ⟨569273, by rfl⟩ : syracuseStep 3036125 = 1138547) (by norm_num)
theorem B2024083 : Blo 2023435 2024083 := bstep (se 1 (by rfl) ⟨1518062, by rfl⟩ : syracuseStep 2024083 = 3036125) B3036125
theorem B4554197 : Blo 2023435 4554197 := bbase (se 7 (by rfl) ⟨53369, by rfl⟩ : syracuseStep 4554197 = 106739) (by norm_num)
theorem B3036131 : Blo 2023435 3036131 := bstep (se 1 (by rfl) ⟨2277098, by rfl⟩ : syracuseStep 3036131 = 4554197) B4554197
theorem B2024087 : Blo 2023435 2024087 := bstep (se 1 (by rfl) ⟨1518065, by rfl⟩ : syracuseStep 2024087 = 3036131) B3036131
theorem B5471221 : Blo 2023435 5471221 := bbase (se 5 (by rfl) ⟨256463, by rfl⟩ : syracuseStep 5471221 = 512927) (by norm_num)
theorem B7294961 : Blo 2023435 7294961 := bstep (se 2 (by rfl) ⟨2735610, by rfl⟩ : syracuseStep 7294961 = 5471221) B5471221
theorem B19453229 : Blo 2023435 19453229 := bstep (se 3 (by rfl) ⟨3647480, by rfl⟩ : syracuseStep 19453229 = 7294961) B7294961
theorem B12968819 : Blo 2023435 12968819 := bstep (se 1 (by rfl) ⟨9726614, by rfl⟩ : syracuseStep 12968819 = 19453229) B19453229
theorem B8645879 : Blo 2023435 8645879 := bstep (se 1 (by rfl) ⟨6484409, by rfl⟩ : syracuseStep 8645879 = 12968819) B12968819
theorem B5763919 : Blo 2023435 5763919 := bstep (se 1 (by rfl) ⟨4322939, by rfl⟩ : syracuseStep 5763919 = 8645879) B8645879
theorem B7685225 : Blo 2023435 7685225 := bstep (se 2 (by rfl) ⟨2881959, by rfl⟩ : syracuseStep 7685225 = 5763919) B5763919
theorem B5123483 : Blo 2023435 5123483 := bstep (se 1 (by rfl) ⟨3842612, by rfl⟩ : syracuseStep 5123483 = 7685225) B7685225
theorem B3415655 : Blo 2023435 3415655 := bstep (se 1 (by rfl) ⟨2561741, by rfl⟩ : syracuseStep 3415655 = 5123483) B5123483
theorem B2277103 : Blo 2023435 2277103 := bstep (se 1 (by rfl) ⟨1707827, by rfl⟩ : syracuseStep 2277103 = 3415655) B3415655
theorem B3036137 : Blo 2023435 3036137 := bstep (se 2 (by rfl) ⟨1138551, by rfl⟩ : syracuseStep 3036137 = 2277103) B2277103
theorem B2024091 : Blo 2023435 2024091 := bstep (se 1 (by rfl) ⟨1518068, by rfl⟩ : syracuseStep 2024091 = 3036137) B3036137
theorem B6484421 : Blo 2023435 6484421 := bbase (se 4 (by rfl) ⟨607914, by rfl⟩ : syracuseStep 6484421 = 1215829) (by norm_num)
theorem B17291789 : Blo 2023435 17291789 := bstep (se 3 (by rfl) ⟨3242210, by rfl⟩ : syracuseStep 17291789 = 6484421) B6484421
theorem B11527859 : Blo 2023435 11527859 := bstep (se 1 (by rfl) ⟨8645894, by rfl⟩ : syracuseStep 11527859 = 17291789) B17291789
theorem B7685239 : Blo 2023435 7685239 := bstep (se 1 (by rfl) ⟨5763929, by rfl⟩ : syracuseStep 7685239 = 11527859) B11527859
theorem B10246985 : Blo 2023435 10246985 := bstep (se 2 (by rfl) ⟨3842619, by rfl⟩ : syracuseStep 10246985 = 7685239) B7685239
theorem B6831323 : Blo 2023435 6831323 := bstep (se 1 (by rfl) ⟨5123492, by rfl⟩ : syracuseStep 6831323 = 10246985) B10246985
theorem B4554215 : Blo 2023435 4554215 := bstep (se 1 (by rfl) ⟨3415661, by rfl⟩ : syracuseStep 4554215 = 6831323) B6831323
theorem B3036143 : Blo 2023435 3036143 := bstep (se 1 (by rfl) ⟨2277107, by rfl⟩ : syracuseStep 3036143 = 4554215) B4554215
theorem B2024095 : Blo 2023435 2024095 := bstep (se 1 (by rfl) ⟨1518071, by rfl⟩ : syracuseStep 2024095 = 3036143) B3036143
theorem B3036149 : Blo 2023435 3036149 := bbase (se 5 (by rfl) ⟨142319, by rfl⟩ : syracuseStep 3036149 = 284639) (by norm_num)
theorem B2024099 : Blo 2023435 2024099 := bstep (se 1 (by rfl) ⟨1518074, by rfl⟩ : syracuseStep 2024099 = 3036149) B3036149
theorem B4322965 : Blo 2023435 4322965 := bbase (se 6 (by rfl) ⟨101319, by rfl⟩ : syracuseStep 4322965 = 202639) (by norm_num)
theorem B5763953 : Blo 2023435 5763953 := bstep (se 2 (by rfl) ⟨2161482, by rfl⟩ : syracuseStep 5763953 = 4322965) B4322965
theorem B3842635 : Blo 2023435 3842635 := bstep (se 1 (by rfl) ⟨2881976, by rfl⟩ : syracuseStep 3842635 = 5763953) B5763953
theorem B5123513 : Blo 2023435 5123513 := bstep (se 2 (by rfl) ⟨1921317, by rfl⟩ : syracuseStep 5123513 = 3842635) B3842635
theorem B3415675 : Blo 2023435 3415675 := bstep (se 1 (by rfl) ⟨2561756, by rfl⟩ : syracuseStep 3415675 = 5123513) B5123513
theorem B4554233 : Blo 2023435 4554233 := bstep (se 2 (by rfl) ⟨1707837, by rfl⟩ : syracuseStep 4554233 = 3415675) B3415675
theorem B3036155 : Blo 2023435 3036155 := bstep (se 1 (by rfl) ⟨2277116, by rfl⟩ : syracuseStep 3036155 = 4554233) B4554233
theorem B2024103 : Blo 2023435 2024103 := bstep (se 1 (by rfl) ⟨1518077, by rfl⟩ : syracuseStep 2024103 = 3036155) B3036155
theorem B2277121 : Blo 2023435 2277121 := bbase (se 2 (by rfl) ⟨853920, by rfl⟩ : syracuseStep 2277121 = 1707841) (by norm_num)
theorem B3036161 : Blo 2023435 3036161 := bstep (se 2 (by rfl) ⟨1138560, by rfl⟩ : syracuseStep 3036161 = 2277121) B2277121
theorem B2024107 : Blo 2023435 2024107 := bstep (se 1 (by rfl) ⟨1518080, by rfl⟩ : syracuseStep 2024107 = 3036161) B3036161
theorem B5123533 : Blo 2023435 5123533 := bbase (se 3 (by rfl) ⟨960662, by rfl⟩ : syracuseStep 5123533 = 1921325) (by norm_num)
theorem B6831377 : Blo 2023435 6831377 := bstep (se 2 (by rfl) ⟨2561766, by rfl⟩ : syracuseStep 6831377 = 5123533) B5123533
theorem B4554251 : Blo 2023435 4554251 := bstep (se 1 (by rfl) ⟨3415688, by rfl⟩ : syracuseStep 4554251 = 6831377) B6831377
theorem B3036167 : Blo 2023435 3036167 := bstep (se 1 (by rfl) ⟨2277125, by rfl⟩ : syracuseStep 3036167 = 4554251) B4554251
theorem B2024111 : Blo 2023435 2024111 := bstep (se 1 (by rfl) ⟨1518083, by rfl⟩ : syracuseStep 2024111 = 3036167) B3036167
theorem B3036173 : Blo 2023435 3036173 := bbase (se 3 (by rfl) ⟨569282, by rfl⟩ : syracuseStep 3036173 = 1138565) (by norm_num)
theorem B2024115 : Blo 2023435 2024115 := bstep (se 1 (by rfl) ⟨1518086, by rfl⟩ : syracuseStep 2024115 = 3036173) B3036173
theorem B4554269 : Blo 2023435 4554269 := bbase (se 3 (by rfl) ⟨853925, by rfl⟩ : syracuseStep 4554269 = 1707851) (by norm_num)
theorem B3036179 : Blo 2023435 3036179 := bstep (se 1 (by rfl) ⟨2277134, by rfl⟩ : syracuseStep 3036179 = 4554269) B4554269
theorem B2024119 : Blo 2023435 2024119 := bstep (se 1 (by rfl) ⟨1518089, by rfl⟩ : syracuseStep 2024119 = 3036179) B3036179
theorem B3415709 : Blo 2023435 3415709 := bbase (se 3 (by rfl) ⟨640445, by rfl⟩ : syracuseStep 3415709 = 1280891) (by norm_num)
theorem B2277139 : Blo 2023435 2277139 := bstep (se 1 (by rfl) ⟨1707854, by rfl⟩ : syracuseStep 2277139 = 3415709) B3415709
theorem B3036185 : Blo 2023435 3036185 := bstep (se 2 (by rfl) ⟨1138569, by rfl⟩ : syracuseStep 3036185 = 2277139) B2277139
theorem B2024123 : Blo 2023435 2024123 := bstep (se 1 (by rfl) ⟨1518092, by rfl⟩ : syracuseStep 2024123 = 3036185) B3036185
theorem B5471317 : Blo 2023435 5471317 := bbase (se 8 (by rfl) ⟨32058, by rfl⟩ : syracuseStep 5471317 = 64117) (by norm_num)
theorem B29180357 : Blo 2023435 29180357 := bstep (se 4 (by rfl) ⟨2735658, by rfl⟩ : syracuseStep 29180357 = 5471317) B5471317
theorem B19453571 : Blo 2023435 19453571 := bstep (se 1 (by rfl) ⟨14590178, by rfl⟩ : syracuseStep 19453571 = 29180357) B29180357
theorem B12969047 : Blo 2023435 12969047 := bstep (se 1 (by rfl) ⟨9726785, by rfl⟩ : syracuseStep 12969047 = 19453571) B19453571
theorem B8646031 : Blo 2023435 8646031 := bstep (se 1 (by rfl) ⟨6484523, by rfl⟩ : syracuseStep 8646031 = 12969047) B12969047
theorem B11528041 : Blo 2023435 11528041 := bstep (se 2 (by rfl) ⟨4323015, by rfl⟩ : syracuseStep 11528041 = 8646031) B8646031
theorem B15370721 : Blo 2023435 15370721 := bstep (se 2 (by rfl) ⟨5764020, by rfl⟩ : syracuseStep 15370721 = 11528041) B11528041
theorem B10247147 : Blo 2023435 10247147 := bstep (se 1 (by rfl) ⟨7685360, by rfl⟩ : syracuseStep 10247147 = 15370721) B15370721
theorem B6831431 : Blo 2023435 6831431 := bstep (se 1 (by rfl) ⟨5123573, by rfl⟩ : syracuseStep 6831431 = 10247147) B10247147
theorem B4554287 : Blo 2023435 4554287 := bstep (se 1 (by rfl) ⟨3415715, by rfl⟩ : syracuseStep 4554287 = 6831431) B6831431
theorem B3036191 : Blo 2023435 3036191 := bstep (se 1 (by rfl) ⟨2277143, by rfl⟩ : syracuseStep 3036191 = 4554287) B4554287
theorem B2024127 : Blo 2023435 2024127 := bstep (se 1 (by rfl) ⟨1518095, by rfl⟩ : syracuseStep 2024127 = 3036191) B3036191
theorem B3036197 : Blo 2023435 3036197 := bbase (se 4 (by rfl) ⟨284643, by rfl⟩ : syracuseStep 3036197 = 569287) (by norm_num)
theorem B2024131 : Blo 2023435 2024131 := bstep (se 1 (by rfl) ⟨1518098, by rfl⟩ : syracuseStep 2024131 = 3036197) B3036197
theorem B2561797 : Blo 2023435 2561797 := bbase (se 4 (by rfl) ⟨240168, by rfl⟩ : syracuseStep 2561797 = 480337) (by norm_num)
theorem B3415729 : Blo 2023435 3415729 := bstep (se 2 (by rfl) ⟨1280898, by rfl⟩ : syracuseStep 3415729 = 2561797) B2561797
theorem B4554305 : Blo 2023435 4554305 := bstep (se 2 (by rfl) ⟨1707864, by rfl⟩ : syracuseStep 4554305 = 3415729) B3415729
theorem B3036203 : Blo 2023435 3036203 := bstep (se 1 (by rfl) ⟨2277152, by rfl⟩ : syracuseStep 3036203 = 4554305) B4554305
theorem B2024135 : Blo 2023435 2024135 := bstep (se 1 (by rfl) ⟨1518101, by rfl⟩ : syracuseStep 2024135 = 3036203) B3036203
theorem B2277157 : Blo 2023435 2277157 := bbase (se 4 (by rfl) ⟨213483, by rfl⟩ : syracuseStep 2277157 = 426967) (by norm_num)
theorem B3036209 : Blo 2023435 3036209 := bstep (se 2 (by rfl) ⟨1138578, by rfl⟩ : syracuseStep 3036209 = 2277157) B2277157
theorem B2024139 : Blo 2023435 2024139 := bstep (se 1 (by rfl) ⟨1518104, by rfl⟩ : syracuseStep 2024139 = 3036209) B3036209
theorem B8646101 : Blo 2023435 8646101 := bbase (se 7 (by rfl) ⟨101321, by rfl⟩ : syracuseStep 8646101 = 202643) (by norm_num)
theorem B5764067 : Blo 2023435 5764067 := bstep (se 1 (by rfl) ⟨4323050, by rfl⟩ : syracuseStep 5764067 = 8646101) B8646101
theorem B3842711 : Blo 2023435 3842711 := bstep (se 1 (by rfl) ⟨2882033, by rfl⟩ : syracuseStep 3842711 = 5764067) B5764067
theorem B2561807 : Blo 2023435 2561807 := bstep (se 1 (by rfl) ⟨1921355, by rfl⟩ : syracuseStep 2561807 = 3842711) B3842711
theorem B6831485 : Blo 2023435 6831485 := bstep (se 3 (by rfl) ⟨1280903, by rfl⟩ : syracuseStep 6831485 = 2561807) B2561807
theorem B4554323 : Blo 2023435 4554323 := bstep (se 1 (by rfl) ⟨3415742, by rfl⟩ : syracuseStep 4554323 = 6831485) B6831485
theorem B3036215 : Blo 2023435 3036215 := bstep (se 1 (by rfl) ⟨2277161, by rfl⟩ : syracuseStep 3036215 = 4554323) B4554323
theorem B2024143 : Blo 2023435 2024143 := bstep (se 1 (by rfl) ⟨1518107, by rfl⟩ : syracuseStep 2024143 = 3036215) B3036215
theorem B3036221 : Blo 2023435 3036221 := bbase (se 3 (by rfl) ⟨569291, by rfl⟩ : syracuseStep 3036221 = 1138583) (by norm_num)
theorem B2024147 : Blo 2023435 2024147 := bstep (se 1 (by rfl) ⟨1518110, by rfl⟩ : syracuseStep 2024147 = 3036221) B3036221
theorem B4554341 : Blo 2023435 4554341 := bbase (se 4 (by rfl) ⟨426969, by rfl⟩ : syracuseStep 4554341 = 853939) (by norm_num)
theorem B3036227 : Blo 2023435 3036227 := bstep (se 1 (by rfl) ⟨2277170, by rfl⟩ : syracuseStep 3036227 = 4554341) B4554341
theorem B2024151 : Blo 2023435 2024151 := bstep (se 1 (by rfl) ⟨1518113, by rfl⟩ : syracuseStep 2024151 = 3036227) B3036227
theorem B5123645 : Blo 2023435 5123645 := bbase (se 3 (by rfl) ⟨960683, by rfl⟩ : syracuseStep 5123645 = 1921367) (by norm_num)
theorem B3415763 : Blo 2023435 3415763 := bstep (se 1 (by rfl) ⟨2561822, by rfl⟩ : syracuseStep 3415763 = 5123645) B5123645
theorem B2277175 : Blo 2023435 2277175 := bstep (se 1 (by rfl) ⟨1707881, by rfl⟩ : syracuseStep 2277175 = 3415763) B3415763
theorem B3036233 : Blo 2023435 3036233 := bstep (se 2 (by rfl) ⟨1138587, by rfl⟩ : syracuseStep 3036233 = 2277175) B2277175
theorem B2024155 : Blo 2023435 2024155 := bstep (se 1 (by rfl) ⟨1518116, by rfl⟩ : syracuseStep 2024155 = 3036233) B3036233
theorem B3842741 : Blo 2023435 3842741 := bbase (se 5 (by rfl) ⟨180128, by rfl⟩ : syracuseStep 3842741 = 360257) (by norm_num)
theorem B10247309 : Blo 2023435 10247309 := bstep (se 3 (by rfl) ⟨1921370, by rfl⟩ : syracuseStep 10247309 = 3842741) B3842741
theorem B6831539 : Blo 2023435 6831539 := bstep (se 1 (by rfl) ⟨5123654, by rfl⟩ : syracuseStep 6831539 = 10247309) B10247309
theorem B4554359 : Blo 2023435 4554359 := bstep (se 1 (by rfl) ⟨3415769, by rfl⟩ : syracuseStep 4554359 = 6831539) B6831539
theorem B3036239 : Blo 2023435 3036239 := bstep (se 1 (by rfl) ⟨2277179, by rfl⟩ : syracuseStep 3036239 = 4554359) B4554359
theorem B2024159 : Blo 2023435 2024159 := bstep (se 1 (by rfl) ⟨1518119, by rfl⟩ : syracuseStep 2024159 = 3036239) B3036239
theorem B3036245 : Blo 2023435 3036245 := bbase (se 8 (by rfl) ⟨17790, by rfl⟩ : syracuseStep 3036245 = 35581) (by norm_num)
theorem B2024163 : Blo 2023435 2024163 := bstep (se 1 (by rfl) ⟨1518122, by rfl⟩ : syracuseStep 2024163 = 3036245) B3036245
theorem B2051785 : Blo 2023435 2051785 := bbase (se 2 (by rfl) ⟨769419, by rfl⟩ : syracuseStep 2051785 = 1538839) (by norm_num)
theorem B2735713 : Blo 2023435 2735713 := bstep (se 2 (by rfl) ⟨1025892, by rfl⟩ : syracuseStep 2735713 = 2051785) B2051785
theorem B14590469 : Blo 2023435 14590469 := bstep (se 4 (by rfl) ⟨1367856, by rfl⟩ : syracuseStep 14590469 = 2735713) B2735713
theorem B9726979 : Blo 2023435 9726979 := bstep (se 1 (by rfl) ⟨7295234, by rfl⟩ : syracuseStep 9726979 = 14590469) B14590469
theorem B12969305 : Blo 2023435 12969305 := bstep (se 2 (by rfl) ⟨4863489, by rfl⟩ : syracuseStep 12969305 = 9726979) B9726979
theorem B8646203 : Blo 2023435 8646203 := bstep (se 1 (by rfl) ⟨6484652, by rfl⟩ : syracuseStep 8646203 = 12969305) B12969305
theorem B5764135 : Blo 2023435 5764135 := bstep (se 1 (by rfl) ⟨4323101, by rfl⟩ : syracuseStep 5764135 = 8646203) B8646203
theorem B7685513 : Blo 2023435 7685513 := bstep (se 2 (by rfl) ⟨2882067, by rfl⟩ : syracuseStep 7685513 = 5764135) B5764135
theorem B5123675 : Blo 2023435 5123675 := bstep (se 1 (by rfl) ⟨3842756, by rfl⟩ : syracuseStep 5123675 = 7685513) B7685513
theorem B3415783 : Blo 2023435 3415783 := bstep (se 1 (by rfl) ⟨2561837, by rfl⟩ : syracuseStep 3415783 = 5123675) B5123675
theorem B4554377 : Blo 2023435 4554377 := bstep (se 2 (by rfl) ⟨1707891, by rfl⟩ : syracuseStep 4554377 = 3415783) B3415783
theorem B3036251 : Blo 2023435 3036251 := bstep (se 1 (by rfl) ⟨2277188, by rfl⟩ : syracuseStep 3036251 = 4554377) B4554377
theorem B2024167 : Blo 2023435 2024167 := bstep (se 1 (by rfl) ⟨1518125, by rfl⟩ : syracuseStep 2024167 = 3036251) B3036251
theorem B2277193 : Blo 2023435 2277193 := bbase (se 2 (by rfl) ⟨853947, by rfl⟩ : syracuseStep 2277193 = 1707895) (by norm_num)
theorem B3036257 : Blo 2023435 3036257 := bstep (se 2 (by rfl) ⟨1138596, by rfl⟩ : syracuseStep 3036257 = 2277193) B2277193
theorem B2024171 : Blo 2023435 2024171 := bstep (se 1 (by rfl) ⟨1518128, by rfl⟩ : syracuseStep 2024171 = 3036257) B3036257
theorem B2596801 : Blo 2023435 2596801 := bbase (se 2 (by rfl) ⟨973800, by rfl⟩ : syracuseStep 2596801 = 1947601) (by norm_num)
theorem B3462401 : Blo 2023435 3462401 := bstep (se 2 (by rfl) ⟨1298400, by rfl⟩ : syracuseStep 3462401 = 2596801) B2596801
theorem B2308267 : Blo 2023435 2308267 := bstep (se 1 (by rfl) ⟨1731200, by rfl⟩ : syracuseStep 2308267 = 3462401) B3462401
theorem B12310757 : Blo 2023435 12310757 := bstep (se 4 (by rfl) ⟨1154133, by rfl⟩ : syracuseStep 12310757 = 2308267) B2308267
theorem B8207171 : Blo 2023435 8207171 := bstep (se 1 (by rfl) ⟨6155378, by rfl⟩ : syracuseStep 8207171 = 12310757) B12310757
theorem B5471447 : Blo 2023435 5471447 := bstep (se 1 (by rfl) ⟨4103585, by rfl⟩ : syracuseStep 5471447 = 8207171) B8207171
theorem B14590525 : Blo 2023435 14590525 := bstep (se 3 (by rfl) ⟨2735723, by rfl⟩ : syracuseStep 14590525 = 5471447) B5471447
theorem B19454033 : Blo 2023435 19454033 := bstep (se 2 (by rfl) ⟨7295262, by rfl⟩ : syracuseStep 19454033 = 14590525) B14590525
theorem B12969355 : Blo 2023435 12969355 := bstep (se 1 (by rfl) ⟨9727016, by rfl⟩ : syracuseStep 12969355 = 19454033) B19454033
theorem B17292473 : Blo 2023435 17292473 := bstep (se 2 (by rfl) ⟨6484677, by rfl⟩ : syracuseStep 17292473 = 12969355) B12969355
theorem B11528315 : Blo 2023435 11528315 := bstep (se 1 (by rfl) ⟨8646236, by rfl⟩ : syracuseStep 11528315 = 17292473) B17292473
theorem B7685543 : Blo 2023435 7685543 := bstep (se 1 (by rfl) ⟨5764157, by rfl⟩ : syracuseStep 7685543 = 11528315) B11528315
theorem B5123695 : Blo 2023435 5123695 := bstep (se 1 (by rfl) ⟨3842771, by rfl⟩ : syracuseStep 5123695 = 7685543) B7685543
theorem B6831593 : Blo 2023435 6831593 := bstep (se 2 (by rfl) ⟨2561847, by rfl⟩ : syracuseStep 6831593 = 5123695) B5123695
theorem B4554395 : Blo 2023435 4554395 := bstep (se 1 (by rfl) ⟨3415796, by rfl⟩ : syracuseStep 4554395 = 6831593) B6831593
theorem B3036263 : Blo 2023435 3036263 := bstep (se 1 (by rfl) ⟨2277197, by rfl⟩ : syracuseStep 3036263 = 4554395) B4554395
theorem B2024175 : Blo 2023435 2024175 := bstep (se 1 (by rfl) ⟨1518131, by rfl⟩ : syracuseStep 2024175 = 3036263) B3036263
theorem B3036269 : Blo 2023435 3036269 := bbase (se 3 (by rfl) ⟨569300, by rfl⟩ : syracuseStep 3036269 = 1138601) (by norm_num)
theorem B2024179 : Blo 2023435 2024179 := bstep (se 1 (by rfl) ⟨1518134, by rfl⟩ : syracuseStep 2024179 = 3036269) B3036269
theorem B4554413 : Blo 2023435 4554413 := bbase (se 3 (by rfl) ⟨853952, by rfl⟩ : syracuseStep 4554413 = 1707905) (by norm_num)
theorem B3036275 : Blo 2023435 3036275 := bstep (se 1 (by rfl) ⟨2277206, by rfl⟩ : syracuseStep 3036275 = 4554413) B4554413
theorem B2024183 : Blo 2023435 2024183 := bstep (se 1 (by rfl) ⟨1518137, by rfl⟩ : syracuseStep 2024183 = 3036275) B3036275
theorem B2735741 : Blo 2023435 2735741 := bbase (se 3 (by rfl) ⟨512951, by rfl⟩ : syracuseStep 2735741 = 1025903) (by norm_num)
theorem B7295309 : Blo 2023435 7295309 := bstep (se 3 (by rfl) ⟨1367870, by rfl⟩ : syracuseStep 7295309 = 2735741) B2735741
theorem B4863539 : Blo 2023435 4863539 := bstep (se 1 (by rfl) ⟨3647654, by rfl⟩ : syracuseStep 4863539 = 7295309) B7295309
theorem B3242359 : Blo 2023435 3242359 := bstep (se 1 (by rfl) ⟨2431769, by rfl⟩ : syracuseStep 3242359 = 4863539) B4863539
theorem B4323145 : Blo 2023435 4323145 := bstep (se 2 (by rfl) ⟨1621179, by rfl⟩ : syracuseStep 4323145 = 3242359) B3242359
theorem B5764193 : Blo 2023435 5764193 := bstep (se 2 (by rfl) ⟨2161572, by rfl⟩ : syracuseStep 5764193 = 4323145) B4323145
theorem B3842795 : Blo 2023435 3842795 := bstep (se 1 (by rfl) ⟨2882096, by rfl⟩ : syracuseStep 3842795 = 5764193) B5764193
theorem B2561863 : Blo 2023435 2561863 := bstep (se 1 (by rfl) ⟨1921397, by rfl⟩ : syracuseStep 2561863 = 3842795) B3842795
theorem B3415817 : Blo 2023435 3415817 := bstep (se 2 (by rfl) ⟨1280931, by rfl⟩ : syracuseStep 3415817 = 2561863) B2561863
theorem B2277211 : Blo 2023435 2277211 := bstep (se 1 (by rfl) ⟨1707908, by rfl⟩ : syracuseStep 2277211 = 3415817) B3415817
theorem B3036281 : Blo 2023435 3036281 := bstep (se 2 (by rfl) ⟨1138605, by rfl⟩ : syracuseStep 3036281 = 2277211) B2277211
theorem B2024187 : Blo 2023435 2024187 := bstep (se 1 (by rfl) ⟨1518140, by rfl⟩ : syracuseStep 2024187 = 3036281) B3036281
theorem B3162269 : Blo 2023435 3162269 := bbase (se 3 (by rfl) ⟨592925, by rfl⟩ : syracuseStep 3162269 = 1185851) (by norm_num)
theorem B2108179 : Blo 2023435 2108179 := bstep (se 1 (by rfl) ⟨1581134, by rfl⟩ : syracuseStep 2108179 = 3162269) B3162269
theorem B2810905 : Blo 2023435 2810905 := bstep (se 2 (by rfl) ⟨1054089, by rfl⟩ : syracuseStep 2810905 = 2108179) B2108179
theorem B14991493 : Blo 2023435 14991493 := bstep (se 4 (by rfl) ⟨1405452, by rfl⟩ : syracuseStep 14991493 = 2810905) B2810905
theorem B19988657 : Blo 2023435 19988657 := bstep (se 2 (by rfl) ⟨7495746, by rfl⟩ : syracuseStep 19988657 = 14991493) B14991493
theorem B13325771 : Blo 2023435 13325771 := bstep (se 1 (by rfl) ⟨9994328, by rfl⟩ : syracuseStep 13325771 = 19988657) B19988657
theorem B8883847 : Blo 2023435 8883847 := bstep (se 1 (by rfl) ⟨6662885, by rfl⟩ : syracuseStep 8883847 = 13325771) B13325771
theorem B11845129 : Blo 2023435 11845129 := bstep (se 2 (by rfl) ⟨4441923, by rfl⟩ : syracuseStep 11845129 = 8883847) B8883847
theorem B15793505 : Blo 2023435 15793505 := bstep (se 2 (by rfl) ⟨5922564, by rfl⟩ : syracuseStep 15793505 = 11845129) B11845129
theorem B10529003 : Blo 2023435 10529003 := bstep (se 1 (by rfl) ⟨7896752, by rfl⟩ : syracuseStep 10529003 = 15793505) B15793505
theorem B7019335 : Blo 2023435 7019335 := bstep (se 1 (by rfl) ⟨5264501, by rfl⟩ : syracuseStep 7019335 = 10529003) B10529003
theorem B9359113 : Blo 2023435 9359113 := bstep (se 2 (by rfl) ⟨3509667, by rfl⟩ : syracuseStep 9359113 = 7019335) B7019335
theorem B12478817 : Blo 2023435 12478817 := bstep (se 2 (by rfl) ⟨4679556, by rfl⟩ : syracuseStep 12478817 = 9359113) B9359113
theorem B33276845 : Blo 2023435 33276845 := bstep (se 3 (by rfl) ⟨6239408, by rfl⟩ : syracuseStep 33276845 = 12478817) B12478817
theorem B22184563 : Blo 2023435 22184563 := bstep (se 1 (by rfl) ⟨16638422, by rfl⟩ : syracuseStep 22184563 = 33276845) B33276845
theorem B29579417 : Blo 2023435 29579417 := bstep (se 2 (by rfl) ⟨11092281, by rfl⟩ : syracuseStep 29579417 = 22184563) B22184563
theorem B19719611 : Blo 2023435 19719611 := bstep (se 1 (by rfl) ⟨14789708, by rfl⟩ : syracuseStep 19719611 = 29579417) B29579417
theorem B13146407 : Blo 2023435 13146407 := bstep (se 1 (by rfl) ⟨9859805, by rfl⟩ : syracuseStep 13146407 = 19719611) B19719611
theorem B8764271 : Blo 2023435 8764271 := bstep (se 1 (by rfl) ⟨6573203, by rfl⟩ : syracuseStep 8764271 = 13146407) B13146407
theorem B5842847 : Blo 2023435 5842847 := bstep (se 1 (by rfl) ⟨4382135, by rfl⟩ : syracuseStep 5842847 = 8764271) B8764271
theorem B3895231 : Blo 2023435 3895231 := bstep (se 1 (by rfl) ⟨2921423, by rfl⟩ : syracuseStep 3895231 = 5842847) B5842847
theorem B5193641 : Blo 2023435 5193641 := bstep (se 2 (by rfl) ⟨1947615, by rfl⟩ : syracuseStep 5193641 = 3895231) B3895231
theorem B13849709 : Blo 2023435 13849709 := bstep (se 3 (by rfl) ⟨2596820, by rfl⟩ : syracuseStep 13849709 = 5193641) B5193641
theorem B36932557 : Blo 2023435 36932557 := bstep (se 3 (by rfl) ⟨6924854, by rfl⟩ : syracuseStep 36932557 = 13849709) B13849709
theorem B49243409 : Blo 2023435 49243409 := bstep (se 2 (by rfl) ⟨18466278, by rfl⟩ : syracuseStep 49243409 = 36932557) B36932557
theorem B32828939 : Blo 2023435 32828939 := bstep (se 1 (by rfl) ⟨24621704, by rfl⟩ : syracuseStep 32828939 = 49243409) B49243409
theorem B21885959 : Blo 2023435 21885959 := bstep (se 1 (by rfl) ⟨16414469, by rfl⟩ : syracuseStep 21885959 = 32828939) B32828939
theorem B14590639 : Blo 2023435 14590639 := bstep (se 1 (by rfl) ⟨10942979, by rfl⟩ : syracuseStep 14590639 = 21885959) B21885959
theorem B19454185 : Blo 2023435 19454185 := bstep (se 2 (by rfl) ⟨7295319, by rfl⟩ : syracuseStep 19454185 = 14590639) B14590639
theorem B25938913 : Blo 2023435 25938913 := bstep (se 2 (by rfl) ⟨9727092, by rfl⟩ : syracuseStep 25938913 = 19454185) B19454185
theorem B34585217 : Blo 2023435 34585217 := bstep (se 2 (by rfl) ⟨12969456, by rfl⟩ : syracuseStep 34585217 = 25938913) B25938913
theorem B23056811 : Blo 2023435 23056811 := bstep (se 1 (by rfl) ⟨17292608, by rfl⟩ : syracuseStep 23056811 = 34585217) B34585217
theorem B15371207 : Blo 2023435 15371207 := bstep (se 1 (by rfl) ⟨11528405, by rfl⟩ : syracuseStep 15371207 = 23056811) B23056811
theorem B10247471 : Blo 2023435 10247471 := bstep (se 1 (by rfl) ⟨7685603, by rfl⟩ : syracuseStep 10247471 = 15371207) B15371207
theorem B6831647 : Blo 2023435 6831647 := bstep (se 1 (by rfl) ⟨5123735, by rfl⟩ : syracuseStep 6831647 = 10247471) B10247471
theorem B4554431 : Blo 2023435 4554431 := bstep (se 1 (by rfl) ⟨3415823, by rfl⟩ : syracuseStep 4554431 = 6831647) B6831647
theorem B3036287 : Blo 2023435 3036287 := bstep (se 1 (by rfl) ⟨2277215, by rfl⟩ : syracuseStep 3036287 = 4554431) B4554431
theorem B2024191 : Blo 2023435 2024191 := bstep (se 1 (by rfl) ⟨1518143, by rfl⟩ : syracuseStep 2024191 = 3036287) B3036287
theorem B3036293 : Blo 2023435 3036293 := bbase (se 4 (by rfl) ⟨284652, by rfl⟩ : syracuseStep 3036293 = 569305) (by norm_num)
theorem B2024195 : Blo 2023435 2024195 := bstep (se 1 (by rfl) ⟨1518146, by rfl⟩ : syracuseStep 2024195 = 3036293) B3036293
theorem B3415837 : Blo 2023435 3415837 := bbase (se 3 (by rfl) ⟨640469, by rfl⟩ : syracuseStep 3415837 = 1280939) (by norm_num)
theorem B4554449 : Blo 2023435 4554449 := bstep (se 2 (by rfl) ⟨1707918, by rfl⟩ : syracuseStep 4554449 = 3415837) B3415837
theorem B3036299 : Blo 2023435 3036299 := bstep (se 1 (by rfl) ⟨2277224, by rfl⟩ : syracuseStep 3036299 = 4554449) B4554449
theorem B2024199 : Blo 2023435 2024199 := bstep (se 1 (by rfl) ⟨1518149, by rfl⟩ : syracuseStep 2024199 = 3036299) B3036299
theorem B2277229 : Blo 2023435 2277229 := bbase (se 3 (by rfl) ⟨426980, by rfl⟩ : syracuseStep 2277229 = 853961) (by norm_num)
theorem B3036305 : Blo 2023435 3036305 := bstep (se 2 (by rfl) ⟨1138614, by rfl⟩ : syracuseStep 3036305 = 2277229) B2277229
theorem B2024203 : Blo 2023435 2024203 := bstep (se 1 (by rfl) ⟨1518152, by rfl⟩ : syracuseStep 2024203 = 3036305) B3036305
theorem B6831701 : Blo 2023435 6831701 := bbase (se 8 (by rfl) ⟨40029, by rfl⟩ : syracuseStep 6831701 = 80059) (by norm_num)
theorem B4554467 : Blo 2023435 4554467 := bstep (se 1 (by rfl) ⟨3415850, by rfl⟩ : syracuseStep 4554467 = 6831701) B6831701
theorem B3036311 : Blo 2023435 3036311 := bstep (se 1 (by rfl) ⟨2277233, by rfl⟩ : syracuseStep 3036311 = 4554467) B4554467
theorem B2024207 : Blo 2023435 2024207 := bstep (se 1 (by rfl) ⟨1518155, by rfl⟩ : syracuseStep 2024207 = 3036311) B3036311
theorem B3036317 : Blo 2023435 3036317 := bbase (se 3 (by rfl) ⟨569309, by rfl⟩ : syracuseStep 3036317 = 1138619) (by norm_num)
theorem B2024211 : Blo 2023435 2024211 := bstep (se 1 (by rfl) ⟨1518158, by rfl⟩ : syracuseStep 2024211 = 3036317) B3036317
theorem B4554485 : Blo 2023435 4554485 := bbase (se 5 (by rfl) ⟨213491, by rfl⟩ : syracuseStep 4554485 = 426983) (by norm_num)
theorem B3036323 : Blo 2023435 3036323 := bstep (se 1 (by rfl) ⟨2277242, by rfl⟩ : syracuseStep 3036323 = 4554485) B4554485
theorem B2024215 : Blo 2023435 2024215 := bstep (se 1 (by rfl) ⟨1518161, by rfl⟩ : syracuseStep 2024215 = 3036323) B3036323
theorem B2339813 : Blo 2023435 2339813 := bbase (se 4 (by rfl) ⟨219357, by rfl⟩ : syracuseStep 2339813 = 438715) (by norm_num)
theorem B6239501 : Blo 2023435 6239501 := bstep (se 3 (by rfl) ⟨1169906, by rfl⟩ : syracuseStep 6239501 = 2339813) B2339813
theorem B4159667 : Blo 2023435 4159667 := bstep (se 1 (by rfl) ⟨3119750, by rfl⟩ : syracuseStep 4159667 = 6239501) B6239501
theorem B2773111 : Blo 2023435 2773111 := bstep (se 1 (by rfl) ⟨2079833, by rfl⟩ : syracuseStep 2773111 = 4159667) B4159667
theorem B3697481 : Blo 2023435 3697481 := bstep (se 2 (by rfl) ⟨1386555, by rfl⟩ : syracuseStep 3697481 = 2773111) B2773111
theorem B2464987 : Blo 2023435 2464987 := bstep (se 1 (by rfl) ⟨1848740, by rfl⟩ : syracuseStep 2464987 = 3697481) B3697481
theorem B3286649 : Blo 2023435 3286649 := bstep (se 2 (by rfl) ⟨1232493, by rfl⟩ : syracuseStep 3286649 = 2464987) B2464987
theorem B2191099 : Blo 2023435 2191099 := bstep (se 1 (by rfl) ⟨1643324, by rfl⟩ : syracuseStep 2191099 = 3286649) B3286649
theorem B2921465 : Blo 2023435 2921465 := bstep (se 2 (by rfl) ⟨1095549, by rfl⟩ : syracuseStep 2921465 = 2191099) B2191099
theorem B7790573 : Blo 2023435 7790573 := bstep (se 3 (by rfl) ⟨1460732, by rfl⟩ : syracuseStep 7790573 = 2921465) B2921465
theorem B5193715 : Blo 2023435 5193715 := bstep (se 1 (by rfl) ⟨3895286, by rfl⟩ : syracuseStep 5193715 = 7790573) B7790573
theorem B6924953 : Blo 2023435 6924953 := bstep (se 2 (by rfl) ⟨2596857, by rfl⟩ : syracuseStep 6924953 = 5193715) B5193715
theorem B18466541 : Blo 2023435 18466541 := bstep (se 3 (by rfl) ⟨3462476, by rfl⟩ : syracuseStep 18466541 = 6924953) B6924953
theorem B12311027 : Blo 2023435 12311027 := bstep (se 1 (by rfl) ⟨9233270, by rfl⟩ : syracuseStep 12311027 = 18466541) B18466541
theorem B8207351 : Blo 2023435 8207351 := bstep (se 1 (by rfl) ⟨6155513, by rfl⟩ : syracuseStep 8207351 = 12311027) B12311027
theorem B5471567 : Blo 2023435 5471567 := bstep (se 1 (by rfl) ⟨4103675, by rfl⟩ : syracuseStep 5471567 = 8207351) B8207351
theorem B3647711 : Blo 2023435 3647711 := bstep (se 1 (by rfl) ⟨2735783, by rfl⟩ : syracuseStep 3647711 = 5471567) B5471567
theorem B9727229 : Blo 2023435 9727229 := bstep (se 3 (by rfl) ⟨1823855, by rfl⟩ : syracuseStep 9727229 = 3647711) B3647711
theorem B25939277 : Blo 2023435 25939277 := bstep (se 3 (by rfl) ⟨4863614, by rfl⟩ : syracuseStep 25939277 = 9727229) B9727229
theorem B17292851 : Blo 2023435 17292851 := bstep (se 1 (by rfl) ⟨12969638, by rfl⟩ : syracuseStep 17292851 = 25939277) B25939277
theorem B11528567 : Blo 2023435 11528567 := bstep (se 1 (by rfl) ⟨8646425, by rfl⟩ : syracuseStep 11528567 = 17292851) B17292851
theorem B7685711 : Blo 2023435 7685711 := bstep (se 1 (by rfl) ⟨5764283, by rfl⟩ : syracuseStep 7685711 = 11528567) B11528567
theorem B5123807 : Blo 2023435 5123807 := bstep (se 1 (by rfl) ⟨3842855, by rfl⟩ : syracuseStep 5123807 = 7685711) B7685711
theorem B3415871 : Blo 2023435 3415871 := bstep (se 1 (by rfl) ⟨2561903, by rfl⟩ : syracuseStep 3415871 = 5123807) B5123807
theorem B2277247 : Blo 2023435 2277247 := bstep (se 1 (by rfl) ⟨1707935, by rfl⟩ : syracuseStep 2277247 = 3415871) B3415871
theorem B3036329 : Blo 2023435 3036329 := bstep (se 2 (by rfl) ⟨1138623, by rfl⟩ : syracuseStep 3036329 = 2277247) B2277247
theorem B2024219 : Blo 2023435 2024219 := bstep (se 1 (by rfl) ⟨1518164, by rfl⟩ : syracuseStep 2024219 = 3036329) B3036329
theorem B4323221 : Blo 2023435 4323221 := bbase (se 6 (by rfl) ⟨101325, by rfl⟩ : syracuseStep 4323221 = 202651) (by norm_num)
theorem B2882147 : Blo 2023435 2882147 := bstep (se 1 (by rfl) ⟨2161610, by rfl⟩ : syracuseStep 2882147 = 4323221) B4323221
theorem B7685725 : Blo 2023435 7685725 := bstep (se 3 (by rfl) ⟨1441073, by rfl⟩ : syracuseStep 7685725 = 2882147) B2882147
theorem B10247633 : Blo 2023435 10247633 := bstep (se 2 (by rfl) ⟨3842862, by rfl⟩ : syracuseStep 10247633 = 7685725) B7685725
theorem B6831755 : Blo 2023435 6831755 := bstep (se 1 (by rfl) ⟨5123816, by rfl⟩ : syracuseStep 6831755 = 10247633) B10247633
theorem B4554503 : Blo 2023435 4554503 := bstep (se 1 (by rfl) ⟨3415877, by rfl⟩ : syracuseStep 4554503 = 6831755) B6831755
theorem B3036335 : Blo 2023435 3036335 := bstep (se 1 (by rfl) ⟨2277251, by rfl⟩ : syracuseStep 3036335 = 4554503) B4554503
theorem B2024223 : Blo 2023435 2024223 := bstep (se 1 (by rfl) ⟨1518167, by rfl⟩ : syracuseStep 2024223 = 3036335) B3036335
theorem B3036341 : Blo 2023435 3036341 := bbase (se 5 (by rfl) ⟨142328, by rfl⟩ : syracuseStep 3036341 = 284657) (by norm_num)
theorem B2024227 : Blo 2023435 2024227 := bstep (se 1 (by rfl) ⟨1518170, by rfl⟩ : syracuseStep 2024227 = 3036341) B3036341
theorem B5123837 : Blo 2023435 5123837 := bbase (se 3 (by rfl) ⟨960719, by rfl⟩ : syracuseStep 5123837 = 1921439) (by norm_num)
theorem B3415891 : Blo 2023435 3415891 := bstep (se 1 (by rfl) ⟨2561918, by rfl⟩ : syracuseStep 3415891 = 5123837) B5123837
theorem B4554521 : Blo 2023435 4554521 := bstep (se 2 (by rfl) ⟨1707945, by rfl⟩ : syracuseStep 4554521 = 3415891) B3415891
theorem B3036347 : Blo 2023435 3036347 := bstep (se 1 (by rfl) ⟨2277260, by rfl⟩ : syracuseStep 3036347 = 4554521) B4554521
theorem B2024231 : Blo 2023435 2024231 := bstep (se 1 (by rfl) ⟨1518173, by rfl⟩ : syracuseStep 2024231 = 3036347) B3036347
theorem B2277265 : Blo 2023435 2277265 := bbase (se 2 (by rfl) ⟨853974, by rfl⟩ : syracuseStep 2277265 = 1707949) (by norm_num)
theorem B3036353 : Blo 2023435 3036353 := bstep (se 2 (by rfl) ⟨1138632, by rfl⟩ : syracuseStep 3036353 = 2277265) B2277265
theorem B2024235 : Blo 2023435 2024235 := bstep (se 1 (by rfl) ⟨1518176, by rfl⟩ : syracuseStep 2024235 = 3036353) B3036353
theorem B3842893 : Blo 2023435 3842893 := bbase (se 3 (by rfl) ⟨720542, by rfl⟩ : syracuseStep 3842893 = 1441085) (by norm_num)
theorem B5123857 : Blo 2023435 5123857 := bstep (se 2 (by rfl) ⟨1921446, by rfl⟩ : syracuseStep 5123857 = 3842893) B3842893
theorem B6831809 : Blo 2023435 6831809 := bstep (se 2 (by rfl) ⟨2561928, by rfl⟩ : syracuseStep 6831809 = 5123857) B5123857
theorem B4554539 : Blo 2023435 4554539 := bstep (se 1 (by rfl) ⟨3415904, by rfl⟩ : syracuseStep 4554539 = 6831809) B6831809
theorem B3036359 : Blo 2023435 3036359 := bstep (se 1 (by rfl) ⟨2277269, by rfl⟩ : syracuseStep 3036359 = 4554539) B4554539
theorem B2024239 : Blo 2023435 2024239 := bstep (se 1 (by rfl) ⟨1518179, by rfl⟩ : syracuseStep 2024239 = 3036359) B3036359
theorem B3036365 : Blo 2023435 3036365 := bbase (se 3 (by rfl) ⟨569318, by rfl⟩ : syracuseStep 3036365 = 1138637) (by norm_num)
theorem B2024243 : Blo 2023435 2024243 := bstep (se 1 (by rfl) ⟨1518182, by rfl⟩ : syracuseStep 2024243 = 3036365) B3036365
theorem B4554557 : Blo 2023435 4554557 := bbase (se 3 (by rfl) ⟨853979, by rfl⟩ : syracuseStep 4554557 = 1707959) (by norm_num)
theorem B3036371 : Blo 2023435 3036371 := bstep (se 1 (by rfl) ⟨2277278, by rfl⟩ : syracuseStep 3036371 = 4554557) B4554557
theorem B2024247 : Blo 2023435 2024247 := bstep (se 1 (by rfl) ⟨1518185, by rfl⟩ : syracuseStep 2024247 = 3036371) B3036371
theorem B3415925 : Blo 2023435 3415925 := bbase (se 5 (by rfl) ⟨160121, by rfl⟩ : syracuseStep 3415925 = 320243) (by norm_num)
theorem B2277283 : Blo 2023435 2277283 := bstep (se 1 (by rfl) ⟨1707962, by rfl⟩ : syracuseStep 2277283 = 3415925) B3415925
theorem B3036377 : Blo 2023435 3036377 := bstep (se 2 (by rfl) ⟨1138641, by rfl⟩ : syracuseStep 3036377 = 2277283) B2277283
theorem B2024251 : Blo 2023435 2024251 := bstep (se 1 (by rfl) ⟨1518188, by rfl⟩ : syracuseStep 2024251 = 3036377) B3036377
theorem B4863701 : Blo 2023435 4863701 := bbase (se 7 (by rfl) ⟨56996, by rfl⟩ : syracuseStep 4863701 = 113993) (by norm_num)
theorem B3242467 : Blo 2023435 3242467 := bstep (se 1 (by rfl) ⟨2431850, by rfl⟩ : syracuseStep 3242467 = 4863701) B4863701
theorem B4323289 : Blo 2023435 4323289 := bstep (se 2 (by rfl) ⟨1621233, by rfl⟩ : syracuseStep 4323289 = 3242467) B3242467
theorem B5764385 : Blo 2023435 5764385 := bstep (se 2 (by rfl) ⟨2161644, by rfl⟩ : syracuseStep 5764385 = 4323289) B4323289
theorem B15371693 : Blo 2023435 15371693 := bstep (se 3 (by rfl) ⟨2882192, by rfl⟩ : syracuseStep 15371693 = 5764385) B5764385
theorem B10247795 : Blo 2023435 10247795 := bstep (se 1 (by rfl) ⟨7685846, by rfl⟩ : syracuseStep 10247795 = 15371693) B15371693
theorem B6831863 : Blo 2023435 6831863 := bstep (se 1 (by rfl) ⟨5123897, by rfl⟩ : syracuseStep 6831863 = 10247795) B10247795
theorem B4554575 : Blo 2023435 4554575 := bstep (se 1 (by rfl) ⟨3415931, by rfl⟩ : syracuseStep 4554575 = 6831863) B6831863
theorem B3036383 : Blo 2023435 3036383 := bstep (se 1 (by rfl) ⟨2277287, by rfl⟩ : syracuseStep 3036383 = 4554575) B4554575
theorem B2024255 : Blo 2023435 2024255 := bstep (se 1 (by rfl) ⟨1518191, by rfl⟩ : syracuseStep 2024255 = 3036383) B3036383
theorem B3036389 : Blo 2023435 3036389 := bbase (se 4 (by rfl) ⟨284661, by rfl⟩ : syracuseStep 3036389 = 569323) (by norm_num)
theorem B2024259 : Blo 2023435 2024259 := bstep (se 1 (by rfl) ⟨1518194, by rfl⟩ : syracuseStep 2024259 = 3036389) B3036389
theorem B5193829 : Blo 2023435 5193829 := bbase (se 4 (by rfl) ⟨486921, by rfl⟩ : syracuseStep 5193829 = 973843) (by norm_num)
theorem B6925105 : Blo 2023435 6925105 := bstep (se 2 (by rfl) ⟨2596914, by rfl⟩ : syracuseStep 6925105 = 5193829) B5193829
theorem B9233473 : Blo 2023435 9233473 := bstep (se 2 (by rfl) ⟨3462552, by rfl⟩ : syracuseStep 9233473 = 6925105) B6925105
theorem B12311297 : Blo 2023435 12311297 := bstep (se 2 (by rfl) ⟨4616736, by rfl⟩ : syracuseStep 12311297 = 9233473) B9233473
theorem B8207531 : Blo 2023435 8207531 := bstep (se 1 (by rfl) ⟨6155648, by rfl⟩ : syracuseStep 8207531 = 12311297) B12311297
theorem B5471687 : Blo 2023435 5471687 := bstep (se 1 (by rfl) ⟨4103765, by rfl⟩ : syracuseStep 5471687 = 8207531) B8207531
theorem B3647791 : Blo 2023435 3647791 := bstep (se 1 (by rfl) ⟨2735843, by rfl⟩ : syracuseStep 3647791 = 5471687) B5471687
theorem B4863721 : Blo 2023435 4863721 := bstep (se 2 (by rfl) ⟨1823895, by rfl⟩ : syracuseStep 4863721 = 3647791) B3647791
theorem B6484961 : Blo 2023435 6484961 := bstep (se 2 (by rfl) ⟨2431860, by rfl⟩ : syracuseStep 6484961 = 4863721) B4863721
theorem B4323307 : Blo 2023435 4323307 := bstep (se 1 (by rfl) ⟨3242480, by rfl⟩ : syracuseStep 4323307 = 6484961) B6484961
theorem B5764409 : Blo 2023435 5764409 := bstep (se 2 (by rfl) ⟨2161653, by rfl⟩ : syracuseStep 5764409 = 4323307) B4323307
theorem B3842939 : Blo 2023435 3842939 := bstep (se 1 (by rfl) ⟨2882204, by rfl⟩ : syracuseStep 3842939 = 5764409) B5764409
theorem B2561959 : Blo 2023435 2561959 := bstep (se 1 (by rfl) ⟨1921469, by rfl⟩ : syracuseStep 2561959 = 3842939) B3842939
theorem B3415945 : Blo 2023435 3415945 := bstep (se 2 (by rfl) ⟨1280979, by rfl⟩ : syracuseStep 3415945 = 2561959) B2561959
theorem B4554593 : Blo 2023435 4554593 := bstep (se 2 (by rfl) ⟨1707972, by rfl⟩ : syracuseStep 4554593 = 3415945) B3415945
theorem B3036395 : Blo 2023435 3036395 := bstep (se 1 (by rfl) ⟨2277296, by rfl⟩ : syracuseStep 3036395 = 4554593) B4554593
theorem B2024263 : Blo 2023435 2024263 := bstep (se 1 (by rfl) ⟨1518197, by rfl⟩ : syracuseStep 2024263 = 3036395) B3036395
theorem B2277301 : Blo 2023435 2277301 := bbase (se 5 (by rfl) ⟨106748, by rfl⟩ : syracuseStep 2277301 = 213497) (by norm_num)
theorem B3036401 : Blo 2023435 3036401 := bstep (se 2 (by rfl) ⟨1138650, by rfl⟩ : syracuseStep 3036401 = 2277301) B2277301
theorem B2024267 : Blo 2023435 2024267 := bstep (se 1 (by rfl) ⟨1518200, by rfl⟩ : syracuseStep 2024267 = 3036401) B3036401
theorem B2561969 : Blo 2023435 2561969 := bbase (se 2 (by rfl) ⟨960738, by rfl⟩ : syracuseStep 2561969 = 1921477) (by norm_num)
theorem B6831917 : Blo 2023435 6831917 := bstep (se 3 (by rfl) ⟨1280984, by rfl⟩ : syracuseStep 6831917 = 2561969) B2561969
theorem B4554611 : Blo 2023435 4554611 := bstep (se 1 (by rfl) ⟨3415958, by rfl⟩ : syracuseStep 4554611 = 6831917) B6831917
theorem B3036407 : Blo 2023435 3036407 := bstep (se 1 (by rfl) ⟨2277305, by rfl⟩ : syracuseStep 3036407 = 4554611) B4554611
theorem B2024271 : Blo 2023435 2024271 := bstep (se 1 (by rfl) ⟨1518203, by rfl⟩ : syracuseStep 2024271 = 3036407) B3036407
theorem B3036413 : Blo 2023435 3036413 := bbase (se 3 (by rfl) ⟨569327, by rfl⟩ : syracuseStep 3036413 = 1138655) (by norm_num)
theorem B2024275 : Blo 2023435 2024275 := bstep (se 1 (by rfl) ⟨1518206, by rfl⟩ : syracuseStep 2024275 = 3036413) B3036413
theorem B4554629 : Blo 2023435 4554629 := bbase (se 4 (by rfl) ⟨426996, by rfl⟩ : syracuseStep 4554629 = 853993) (by norm_num)
theorem B3036419 : Blo 2023435 3036419 := bstep (se 1 (by rfl) ⟨2277314, by rfl⟩ : syracuseStep 3036419 = 4554629) B4554629
theorem B2024279 : Blo 2023435 2024279 := bstep (se 1 (by rfl) ⟨1518209, by rfl⟩ : syracuseStep 2024279 = 3036419) B3036419
theorem B2431885 : Blo 2023435 2431885 := bbase (se 3 (by rfl) ⟨455978, by rfl⟩ : syracuseStep 2431885 = 911957) (by norm_num)
theorem B3242513 : Blo 2023435 3242513 := bstep (se 2 (by rfl) ⟨1215942, by rfl⟩ : syracuseStep 3242513 = 2431885) B2431885
theorem B2161675 : Blo 2023435 2161675 := bstep (se 1 (by rfl) ⟨1621256, by rfl⟩ : syracuseStep 2161675 = 3242513) B3242513
theorem B2882233 : Blo 2023435 2882233 := bstep (se 2 (by rfl) ⟨1080837, by rfl⟩ : syracuseStep 2882233 = 2161675) B2161675
theorem B3842977 : Blo 2023435 3842977 := bstep (se 2 (by rfl) ⟨1441116, by rfl⟩ : syracuseStep 3842977 = 2882233) B2882233
theorem B5123969 : Blo 2023435 5123969 := bstep (se 2 (by rfl) ⟨1921488, by rfl⟩ : syracuseStep 5123969 = 3842977) B3842977
theorem B3415979 : Blo 2023435 3415979 := bstep (se 1 (by rfl) ⟨2561984, by rfl⟩ : syracuseStep 3415979 = 5123969) B5123969
theorem B2277319 : Blo 2023435 2277319 := bstep (se 1 (by rfl) ⟨1707989, by rfl⟩ : syracuseStep 2277319 = 3415979) B3415979
theorem B3036425 : Blo 2023435 3036425 := bstep (se 2 (by rfl) ⟨1138659, by rfl⟩ : syracuseStep 3036425 = 2277319) B2277319
theorem B2024283 : Blo 2023435 2024283 := bstep (se 1 (by rfl) ⟨1518212, by rfl⟩ : syracuseStep 2024283 = 3036425) B3036425
theorem B10247957 : Blo 2023435 10247957 := bbase (se 6 (by rfl) ⟨240186, by rfl⟩ : syracuseStep 10247957 = 480373) (by norm_num)
theorem B6831971 : Blo 2023435 6831971 := bstep (se 1 (by rfl) ⟨5123978, by rfl⟩ : syracuseStep 6831971 = 10247957) B10247957
theorem B4554647 : Blo 2023435 4554647 := bstep (se 1 (by rfl) ⟨3415985, by rfl⟩ : syracuseStep 4554647 = 6831971) B6831971
theorem B3036431 : Blo 2023435 3036431 := bstep (se 1 (by rfl) ⟨2277323, by rfl⟩ : syracuseStep 3036431 = 4554647) B4554647
theorem B2024287 : Blo 2023435 2024287 := bstep (se 1 (by rfl) ⟨1518215, by rfl⟩ : syracuseStep 2024287 = 3036431) B3036431
theorem B3036437 : Blo 2023435 3036437 := bbase (se 6 (by rfl) ⟨71166, by rfl⟩ : syracuseStep 3036437 = 142333) (by norm_num)
theorem B2024291 : Blo 2023435 2024291 := bstep (se 1 (by rfl) ⟨1518218, by rfl⟩ : syracuseStep 2024291 = 3036437) B3036437
theorem B26294165 : Blo 2023435 26294165 := bbase (se 6 (by rfl) ⟨616269, by rfl⟩ : syracuseStep 26294165 = 1232539) (by norm_num)
theorem B17529443 : Blo 2023435 17529443 := bstep (se 1 (by rfl) ⟨13147082, by rfl⟩ : syracuseStep 17529443 = 26294165) B26294165
theorem B11686295 : Blo 2023435 11686295 := bstep (se 1 (by rfl) ⟨8764721, by rfl⟩ : syracuseStep 11686295 = 17529443) B17529443
theorem B31163453 : Blo 2023435 31163453 := bstep (se 3 (by rfl) ⟨5843147, by rfl⟩ : syracuseStep 31163453 = 11686295) B11686295
theorem B20775635 : Blo 2023435 20775635 := bstep (se 1 (by rfl) ⟨15581726, by rfl⟩ : syracuseStep 20775635 = 31163453) B31163453
theorem B13850423 : Blo 2023435 13850423 := bstep (se 1 (by rfl) ⟨10387817, by rfl⟩ : syracuseStep 13850423 = 20775635) B20775635
theorem B9233615 : Blo 2023435 9233615 := bstep (se 1 (by rfl) ⟨6925211, by rfl⟩ : syracuseStep 9233615 = 13850423) B13850423
theorem B24622973 : Blo 2023435 24622973 := bstep (se 3 (by rfl) ⟨4616807, by rfl⟩ : syracuseStep 24622973 = 9233615) B9233615
theorem B16415315 : Blo 2023435 16415315 := bstep (se 1 (by rfl) ⟨12311486, by rfl⟩ : syracuseStep 16415315 = 24622973) B24622973
theorem B10943543 : Blo 2023435 10943543 := bstep (se 1 (by rfl) ⟨8207657, by rfl⟩ : syracuseStep 10943543 = 16415315) B16415315
theorem B29182781 : Blo 2023435 29182781 := bstep (se 3 (by rfl) ⟨5471771, by rfl⟩ : syracuseStep 29182781 = 10943543) B10943543
theorem B19455187 : Blo 2023435 19455187 := bstep (se 1 (by rfl) ⟨14591390, by rfl⟩ : syracuseStep 19455187 = 29182781) B29182781
theorem B25940249 : Blo 2023435 25940249 := bstep (se 2 (by rfl) ⟨9727593, by rfl⟩ : syracuseStep 25940249 = 19455187) B19455187
theorem B17293499 : Blo 2023435 17293499 := bstep (se 1 (by rfl) ⟨12970124, by rfl⟩ : syracuseStep 17293499 = 25940249) B25940249
theorem B11528999 : Blo 2023435 11528999 := bstep (se 1 (by rfl) ⟨8646749, by rfl⟩ : syracuseStep 11528999 = 17293499) B17293499
theorem B7685999 : Blo 2023435 7685999 := bstep (se 1 (by rfl) ⟨5764499, by rfl⟩ : syracuseStep 7685999 = 11528999) B11528999
theorem B5123999 : Blo 2023435 5123999 := bstep (se 1 (by rfl) ⟨3842999, by rfl⟩ : syracuseStep 5123999 = 7685999) B7685999
theorem B3415999 : Blo 2023435 3415999 := bstep (se 1 (by rfl) ⟨2561999, by rfl⟩ : syracuseStep 3415999 = 5123999) B5123999
theorem B4554665 : Blo 2023435 4554665 := bstep (se 2 (by rfl) ⟨1707999, by rfl⟩ : syracuseStep 4554665 = 3415999) B3415999
theorem B3036443 : Blo 2023435 3036443 := bstep (se 1 (by rfl) ⟨2277332, by rfl⟩ : syracuseStep 3036443 = 4554665) B4554665
theorem B2024295 : Blo 2023435 2024295 := bstep (se 1 (by rfl) ⟨1518221, by rfl⟩ : syracuseStep 2024295 = 3036443) B3036443
theorem B2277337 : Blo 2023435 2277337 := bbase (se 2 (by rfl) ⟨854001, by rfl⟩ : syracuseStep 2277337 = 1708003) (by norm_num)
theorem B3036449 : Blo 2023435 3036449 := bstep (se 2 (by rfl) ⟨1138668, by rfl⟩ : syracuseStep 3036449 = 2277337) B2277337
theorem B2024299 : Blo 2023435 2024299 := bstep (se 1 (by rfl) ⟨1518224, by rfl⟩ : syracuseStep 2024299 = 3036449) B3036449
theorem B2882261 : Blo 2023435 2882261 := bbase (se 7 (by rfl) ⟨33776, by rfl⟩ : syracuseStep 2882261 = 67553) (by norm_num)
theorem B7686029 : Blo 2023435 7686029 := bstep (se 3 (by rfl) ⟨1441130, by rfl⟩ : syracuseStep 7686029 = 2882261) B2882261
theorem B5124019 : Blo 2023435 5124019 := bstep (se 1 (by rfl) ⟨3843014, by rfl⟩ : syracuseStep 5124019 = 7686029) B7686029
theorem B6832025 : Blo 2023435 6832025 := bstep (se 2 (by rfl) ⟨2562009, by rfl⟩ : syracuseStep 6832025 = 5124019) B5124019
theorem B4554683 : Blo 2023435 4554683 := bstep (se 1 (by rfl) ⟨3416012, by rfl⟩ : syracuseStep 4554683 = 6832025) B6832025
theorem B3036455 : Blo 2023435 3036455 := bstep (se 1 (by rfl) ⟨2277341, by rfl⟩ : syracuseStep 3036455 = 4554683) B4554683
theorem B2024303 : Blo 2023435 2024303 := bstep (se 1 (by rfl) ⟨1518227, by rfl⟩ : syracuseStep 2024303 = 3036455) B3036455
theorem B3036461 : Blo 2023435 3036461 := bbase (se 3 (by rfl) ⟨569336, by rfl⟩ : syracuseStep 3036461 = 1138673) (by norm_num)
theorem B2024307 : Blo 2023435 2024307 := bstep (se 1 (by rfl) ⟨1518230, by rfl⟩ : syracuseStep 2024307 = 3036461) B3036461
theorem B4554701 : Blo 2023435 4554701 := bbase (se 3 (by rfl) ⟨854006, by rfl⟩ : syracuseStep 4554701 = 1708013) (by norm_num)
theorem B3036467 : Blo 2023435 3036467 := bstep (se 1 (by rfl) ⟨2277350, by rfl⟩ : syracuseStep 3036467 = 4554701) B4554701
theorem B2024311 : Blo 2023435 2024311 := bstep (se 1 (by rfl) ⟨1518233, by rfl⟩ : syracuseStep 2024311 = 3036467) B3036467
theorem B2562025 : Blo 2023435 2562025 := bbase (se 2 (by rfl) ⟨960759, by rfl⟩ : syracuseStep 2562025 = 1921519) (by norm_num)
theorem B3416033 : Blo 2023435 3416033 := bstep (se 2 (by rfl) ⟨1281012, by rfl⟩ : syracuseStep 3416033 = 2562025) B2562025
theorem B2277355 : Blo 2023435 2277355 := bstep (se 1 (by rfl) ⟨1708016, by rfl⟩ : syracuseStep 2277355 = 3416033) B3416033
theorem B3036473 : Blo 2023435 3036473 := bstep (se 2 (by rfl) ⟨1138677, by rfl⟩ : syracuseStep 3036473 = 2277355) B2277355
theorem B2024315 : Blo 2023435 2024315 := bstep (se 1 (by rfl) ⟨1518236, by rfl⟩ : syracuseStep 2024315 = 3036473) B3036473
theorem B3077909 : Blo 2023435 3077909 := bbase (se 6 (by rfl) ⟨72138, by rfl⟩ : syracuseStep 3077909 = 144277) (by norm_num)
theorem B2051939 : Blo 2023435 2051939 := bstep (se 1 (by rfl) ⟨1538954, by rfl⟩ : syracuseStep 2051939 = 3077909) B3077909
theorem B5471837 : Blo 2023435 5471837 := bstep (se 3 (by rfl) ⟨1025969, by rfl⟩ : syracuseStep 5471837 = 2051939) B2051939
theorem B3647891 : Blo 2023435 3647891 := bstep (se 1 (by rfl) ⟨2735918, by rfl⟩ : syracuseStep 3647891 = 5471837) B5471837
theorem B2431927 : Blo 2023435 2431927 := bstep (se 1 (by rfl) ⟨1823945, by rfl⟩ : syracuseStep 2431927 = 3647891) B3647891
theorem B12970277 : Blo 2023435 12970277 := bstep (se 4 (by rfl) ⟨1215963, by rfl⟩ : syracuseStep 12970277 = 2431927) B2431927
theorem B8646851 : Blo 2023435 8646851 := bstep (se 1 (by rfl) ⟨6485138, by rfl⟩ : syracuseStep 8646851 = 12970277) B12970277
theorem B23058269 : Blo 2023435 23058269 := bstep (se 3 (by rfl) ⟨4323425, by rfl⟩ : syracuseStep 23058269 = 8646851) B8646851
theorem B15372179 : Blo 2023435 15372179 := bstep (se 1 (by rfl) ⟨11529134, by rfl⟩ : syracuseStep 15372179 = 23058269) B23058269
theorem B10248119 : Blo 2023435 10248119 := bstep (se 1 (by rfl) ⟨7686089, by rfl⟩ : syracuseStep 10248119 = 15372179) B15372179
theorem B6832079 : Blo 2023435 6832079 := bstep (se 1 (by rfl) ⟨5124059, by rfl⟩ : syracuseStep 6832079 = 10248119) B10248119
theorem B4554719 : Blo 2023435 4554719 := bstep (se 1 (by rfl) ⟨3416039, by rfl⟩ : syracuseStep 4554719 = 6832079) B6832079
theorem B3036479 : Blo 2023435 3036479 := bstep (se 1 (by rfl) ⟨2277359, by rfl⟩ : syracuseStep 3036479 = 4554719) B4554719
theorem B2024319 : Blo 2023435 2024319 := bstep (se 1 (by rfl) ⟨1518239, by rfl⟩ : syracuseStep 2024319 = 3036479) B3036479
theorem B3036485 : Blo 2023435 3036485 := bbase (se 4 (by rfl) ⟨284670, by rfl⟩ : syracuseStep 3036485 = 569341) (by norm_num)
theorem B2024323 : Blo 2023435 2024323 := bstep (se 1 (by rfl) ⟨1518242, by rfl⟩ : syracuseStep 2024323 = 3036485) B3036485
theorem B3416053 : Blo 2023435 3416053 := bbase (se 5 (by rfl) ⟨160127, by rfl⟩ : syracuseStep 3416053 = 320255) (by norm_num)
theorem B4554737 : Blo 2023435 4554737 := bstep (se 2 (by rfl) ⟨1708026, by rfl⟩ : syracuseStep 4554737 = 3416053) B3416053
theorem B3036491 : Blo 2023435 3036491 := bstep (se 1 (by rfl) ⟨2277368, by rfl⟩ : syracuseStep 3036491 = 4554737) B4554737
theorem B2024327 : Blo 2023435 2024327 := bstep (se 1 (by rfl) ⟨1518245, by rfl⟩ : syracuseStep 2024327 = 3036491) B3036491
theorem B2277373 : Blo 2023435 2277373 := bbase (se 3 (by rfl) ⟨427007, by rfl⟩ : syracuseStep 2277373 = 854015) (by norm_num)
theorem B3036497 : Blo 2023435 3036497 := bstep (se 2 (by rfl) ⟨1138686, by rfl⟩ : syracuseStep 3036497 = 2277373) B2277373
theorem B2024331 : Blo 2023435 2024331 := bstep (se 1 (by rfl) ⟨1518248, by rfl⟩ : syracuseStep 2024331 = 3036497) B3036497
theorem B6832133 : Blo 2023435 6832133 := bbase (se 4 (by rfl) ⟨640512, by rfl⟩ : syracuseStep 6832133 = 1281025) (by norm_num)
theorem B4554755 : Blo 2023435 4554755 := bstep (se 1 (by rfl) ⟨3416066, by rfl⟩ : syracuseStep 4554755 = 6832133) B6832133
theorem B3036503 : Blo 2023435 3036503 := bstep (se 1 (by rfl) ⟨2277377, by rfl⟩ : syracuseStep 3036503 = 4554755) B4554755
theorem B2024335 : Blo 2023435 2024335 := bstep (se 1 (by rfl) ⟨1518251, by rfl⟩ : syracuseStep 2024335 = 3036503) B3036503
theorem B3036509 : Blo 2023435 3036509 := bbase (se 3 (by rfl) ⟨569345, by rfl⟩ : syracuseStep 3036509 = 1138691) (by norm_num)
theorem B2024339 : Blo 2023435 2024339 := bstep (se 1 (by rfl) ⟨1518254, by rfl⟩ : syracuseStep 2024339 = 3036509) B3036509
theorem B4554773 : Blo 2023435 4554773 := bbase (se 6 (by rfl) ⟨106752, by rfl⟩ : syracuseStep 4554773 = 213505) (by norm_num)
theorem B3036515 : Blo 2023435 3036515 := bstep (se 1 (by rfl) ⟨2277386, by rfl⟩ : syracuseStep 3036515 = 4554773) B4554773
theorem B2024343 : Blo 2023435 2024343 := bstep (se 1 (by rfl) ⟨1518257, by rfl⟩ : syracuseStep 2024343 = 3036515) B3036515
theorem B7686197 : Blo 2023435 7686197 := bbase (se 5 (by rfl) ⟨360290, by rfl⟩ : syracuseStep 7686197 = 720581) (by norm_num)
theorem B5124131 : Blo 2023435 5124131 := bstep (se 1 (by rfl) ⟨3843098, by rfl⟩ : syracuseStep 5124131 = 7686197) B7686197
theorem B3416087 : Blo 2023435 3416087 := bstep (se 1 (by rfl) ⟨2562065, by rfl⟩ : syracuseStep 3416087 = 5124131) B5124131
theorem B2277391 : Blo 2023435 2277391 := bstep (se 1 (by rfl) ⟨1708043, by rfl⟩ : syracuseStep 2277391 = 3416087) B3416087
theorem B3036521 : Blo 2023435 3036521 := bstep (se 2 (by rfl) ⟨1138695, by rfl⟩ : syracuseStep 3036521 = 2277391) B2277391
theorem B2024347 : Blo 2023435 2024347 := bstep (se 1 (by rfl) ⟨1518260, by rfl⟩ : syracuseStep 2024347 = 3036521) B3036521
theorem B3242621 : Blo 2023435 3242621 := bbase (se 3 (by rfl) ⟨607991, by rfl⟩ : syracuseStep 3242621 = 1215983) (by norm_num)
theorem B2161747 : Blo 2023435 2161747 := bstep (se 1 (by rfl) ⟨1621310, by rfl⟩ : syracuseStep 2161747 = 3242621) B3242621
theorem B11529317 : Blo 2023435 11529317 := bstep (se 4 (by rfl) ⟨1080873, by rfl⟩ : syracuseStep 11529317 = 2161747) B2161747
theorem B7686211 : Blo 2023435 7686211 := bstep (se 1 (by rfl) ⟨5764658, by rfl⟩ : syracuseStep 7686211 = 11529317) B11529317
theorem B10248281 : Blo 2023435 10248281 := bstep (se 2 (by rfl) ⟨3843105, by rfl⟩ : syracuseStep 10248281 = 7686211) B7686211
theorem B6832187 : Blo 2023435 6832187 := bstep (se 1 (by rfl) ⟨5124140, by rfl⟩ : syracuseStep 6832187 = 10248281) B10248281
theorem B4554791 : Blo 2023435 4554791 := bstep (se 1 (by rfl) ⟨3416093, by rfl⟩ : syracuseStep 4554791 = 6832187) B6832187
theorem B3036527 : Blo 2023435 3036527 := bstep (se 1 (by rfl) ⟨2277395, by rfl⟩ : syracuseStep 3036527 = 4554791) B4554791
theorem B2024351 : Blo 2023435 2024351 := bstep (se 1 (by rfl) ⟨1518263, by rfl⟩ : syracuseStep 2024351 = 3036527) B3036527
theorem B3036533 : Blo 2023435 3036533 := bbase (se 5 (by rfl) ⟨142337, by rfl⟩ : syracuseStep 3036533 = 284675) (by norm_num)
theorem B2024355 : Blo 2023435 2024355 := bstep (se 1 (by rfl) ⟨1518266, by rfl⟩ : syracuseStep 2024355 = 3036533) B3036533
theorem B2882341 : Blo 2023435 2882341 := bbase (se 4 (by rfl) ⟨270219, by rfl⟩ : syracuseStep 2882341 = 540439) (by norm_num)
theorem B3843121 : Blo 2023435 3843121 := bstep (se 2 (by rfl) ⟨1441170, by rfl⟩ : syracuseStep 3843121 = 2882341) B2882341
theorem B5124161 : Blo 2023435 5124161 := bstep (se 2 (by rfl) ⟨1921560, by rfl⟩ : syracuseStep 5124161 = 3843121) B3843121
theorem B3416107 : Blo 2023435 3416107 := bstep (se 1 (by rfl) ⟨2562080, by rfl⟩ : syracuseStep 3416107 = 5124161) B5124161
theorem B4554809 : Blo 2023435 4554809 := bstep (se 2 (by rfl) ⟨1708053, by rfl⟩ : syracuseStep 4554809 = 3416107) B3416107
theorem B3036539 : Blo 2023435 3036539 := bstep (se 1 (by rfl) ⟨2277404, by rfl⟩ : syracuseStep 3036539 = 4554809) B4554809
theorem B2024359 : Blo 2023435 2024359 := bstep (se 1 (by rfl) ⟨1518269, by rfl⟩ : syracuseStep 2024359 = 3036539) B3036539
theorem B2277409 : Blo 2023435 2277409 := bbase (se 2 (by rfl) ⟨854028, by rfl⟩ : syracuseStep 2277409 = 1708057) (by norm_num)
theorem B3036545 : Blo 2023435 3036545 := bstep (se 2 (by rfl) ⟨1138704, by rfl⟩ : syracuseStep 3036545 = 2277409) B2277409
theorem B2024363 : Blo 2023435 2024363 := bstep (se 1 (by rfl) ⟨1518272, by rfl⟩ : syracuseStep 2024363 = 3036545) B3036545
theorem B5124181 : Blo 2023435 5124181 := bbase (se 8 (by rfl) ⟨30024, by rfl⟩ : syracuseStep 5124181 = 60049) (by norm_num)
theorem B6832241 : Blo 2023435 6832241 := bstep (se 2 (by rfl) ⟨2562090, by rfl⟩ : syracuseStep 6832241 = 5124181) B5124181
theorem B4554827 : Blo 2023435 4554827 := bstep (se 1 (by rfl) ⟨3416120, by rfl⟩ : syracuseStep 4554827 = 6832241) B6832241
theorem B3036551 : Blo 2023435 3036551 := bstep (se 1 (by rfl) ⟨2277413, by rfl⟩ : syracuseStep 3036551 = 4554827) B4554827
theorem B2024367 : Blo 2023435 2024367 := bstep (se 1 (by rfl) ⟨1518275, by rfl⟩ : syracuseStep 2024367 = 3036551) B3036551
theorem B3036557 : Blo 2023435 3036557 := bbase (se 3 (by rfl) ⟨569354, by rfl⟩ : syracuseStep 3036557 = 1138709) (by norm_num)
theorem B2024371 : Blo 2023435 2024371 := bstep (se 1 (by rfl) ⟨1518278, by rfl⟩ : syracuseStep 2024371 = 3036557) B3036557
theorem B4554845 : Blo 2023435 4554845 := bbase (se 3 (by rfl) ⟨854033, by rfl⟩ : syracuseStep 4554845 = 1708067) (by norm_num)
theorem B3036563 : Blo 2023435 3036563 := bstep (se 1 (by rfl) ⟨2277422, by rfl⟩ : syracuseStep 3036563 = 4554845) B4554845
theorem B2024375 : Blo 2023435 2024375 := bstep (se 1 (by rfl) ⟨1518281, by rfl⟩ : syracuseStep 2024375 = 3036563) B3036563
theorem B3416141 : Blo 2023435 3416141 := bbase (se 3 (by rfl) ⟨640526, by rfl⟩ : syracuseStep 3416141 = 1281053) (by norm_num)
theorem B2277427 : Blo 2023435 2277427 := bstep (se 1 (by rfl) ⟨1708070, by rfl⟩ : syracuseStep 2277427 = 3416141) B3416141
theorem B3036569 : Blo 2023435 3036569 := bstep (se 2 (by rfl) ⟨1138713, by rfl⟩ : syracuseStep 3036569 = 2277427) B2277427
theorem B2024379 : Blo 2023435 2024379 := bstep (se 1 (by rfl) ⟨1518284, by rfl⟩ : syracuseStep 2024379 = 3036569) B3036569
theorem B2773333 : Blo 2023435 2773333 := bbase (se 10 (by rfl) ⟨4062, by rfl⟩ : syracuseStep 2773333 = 8125) (by norm_num)
theorem B3697777 : Blo 2023435 3697777 := bstep (se 2 (by rfl) ⟨1386666, by rfl⟩ : syracuseStep 3697777 = 2773333) B2773333
theorem B19721477 : Blo 2023435 19721477 := bstep (se 4 (by rfl) ⟨1848888, by rfl⟩ : syracuseStep 19721477 = 3697777) B3697777
theorem B13147651 : Blo 2023435 13147651 := bstep (se 1 (by rfl) ⟨9860738, by rfl⟩ : syracuseStep 13147651 = 19721477) B19721477
theorem B17530201 : Blo 2023435 17530201 := bstep (se 2 (by rfl) ⟨6573825, by rfl⟩ : syracuseStep 17530201 = 13147651) B13147651
theorem B93494405 : Blo 2023435 93494405 := bstep (se 4 (by rfl) ⟨8765100, by rfl⟩ : syracuseStep 93494405 = 17530201) B17530201
theorem B62329603 : Blo 2023435 62329603 := bstep (se 1 (by rfl) ⟨46747202, by rfl⟩ : syracuseStep 62329603 = 93494405) B93494405
theorem B83106137 : Blo 2023435 83106137 := bstep (se 2 (by rfl) ⟨31164801, by rfl⟩ : syracuseStep 83106137 = 62329603) B62329603
theorem B55404091 : Blo 2023435 55404091 := bstep (se 1 (by rfl) ⟨41553068, by rfl⟩ : syracuseStep 55404091 = 83106137) B83106137
theorem B73872121 : Blo 2023435 73872121 := bstep (se 2 (by rfl) ⟨27702045, by rfl⟩ : syracuseStep 73872121 = 55404091) B55404091
theorem B98496161 : Blo 2023435 98496161 := bstep (se 2 (by rfl) ⟨36936060, by rfl⟩ : syracuseStep 98496161 = 73872121) B73872121
theorem B65664107 : Blo 2023435 65664107 := bstep (se 1 (by rfl) ⟨49248080, by rfl⟩ : syracuseStep 65664107 = 98496161) B98496161
theorem B43776071 : Blo 2023435 43776071 := bstep (se 1 (by rfl) ⟨32832053, by rfl⟩ : syracuseStep 43776071 = 65664107) B65664107
theorem B29184047 : Blo 2023435 29184047 := bstep (se 1 (by rfl) ⟨21888035, by rfl⟩ : syracuseStep 29184047 = 43776071) B43776071
theorem B19456031 : Blo 2023435 19456031 := bstep (se 1 (by rfl) ⟨14592023, by rfl⟩ : syracuseStep 19456031 = 29184047) B29184047
theorem B12970687 : Blo 2023435 12970687 := bstep (se 1 (by rfl) ⟨9728015, by rfl⟩ : syracuseStep 12970687 = 19456031) B19456031
theorem B17294249 : Blo 2023435 17294249 := bstep (se 2 (by rfl) ⟨6485343, by rfl⟩ : syracuseStep 17294249 = 12970687) B12970687
theorem B11529499 : Blo 2023435 11529499 := bstep (se 1 (by rfl) ⟨8647124, by rfl⟩ : syracuseStep 11529499 = 17294249) B17294249
theorem B15372665 : Blo 2023435 15372665 := bstep (se 2 (by rfl) ⟨5764749, by rfl⟩ : syracuseStep 15372665 = 11529499) B11529499
theorem B10248443 : Blo 2023435 10248443 := bstep (se 1 (by rfl) ⟨7686332, by rfl⟩ : syracuseStep 10248443 = 15372665) B15372665
theorem B6832295 : Blo 2023435 6832295 := bstep (se 1 (by rfl) ⟨5124221, by rfl⟩ : syracuseStep 6832295 = 10248443) B10248443
theorem B4554863 : Blo 2023435 4554863 := bstep (se 1 (by rfl) ⟨3416147, by rfl⟩ : syracuseStep 4554863 = 6832295) B6832295
theorem B3036575 : Blo 2023435 3036575 := bstep (se 1 (by rfl) ⟨2277431, by rfl⟩ : syracuseStep 3036575 = 4554863) B4554863
theorem B2024383 : Blo 2023435 2024383 := bstep (se 1 (by rfl) ⟨1518287, by rfl⟩ : syracuseStep 2024383 = 3036575) B3036575
theorem B3036581 : Blo 2023435 3036581 := bbase (se 4 (by rfl) ⟨284679, by rfl⟩ : syracuseStep 3036581 = 569359) (by norm_num)
theorem B2024387 : Blo 2023435 2024387 := bstep (se 1 (by rfl) ⟨1518290, by rfl⟩ : syracuseStep 2024387 = 3036581) B3036581
theorem B2562121 : Blo 2023435 2562121 := bbase (se 2 (by rfl) ⟨960795, by rfl⟩ : syracuseStep 2562121 = 1921591) (by norm_num)
theorem B3416161 : Blo 2023435 3416161 := bstep (se 2 (by rfl) ⟨1281060, by rfl⟩ : syracuseStep 3416161 = 2562121) B2562121
theorem B4554881 : Blo 2023435 4554881 := bstep (se 2 (by rfl) ⟨1708080, by rfl⟩ : syracuseStep 4554881 = 3416161) B3416161
theorem B3036587 : Blo 2023435 3036587 := bstep (se 1 (by rfl) ⟨2277440, by rfl⟩ : syracuseStep 3036587 = 4554881) B4554881
theorem B2024391 : Blo 2023435 2024391 := bstep (se 1 (by rfl) ⟨1518293, by rfl⟩ : syracuseStep 2024391 = 3036587) B3036587
theorem B2277445 : Blo 2023435 2277445 := bbase (se 4 (by rfl) ⟨213510, by rfl⟩ : syracuseStep 2277445 = 427021) (by norm_num)
theorem B3036593 : Blo 2023435 3036593 := bstep (se 2 (by rfl) ⟨1138722, by rfl⟩ : syracuseStep 3036593 = 2277445) B2277445
theorem B2024395 : Blo 2023435 2024395 := bstep (se 1 (by rfl) ⟨1518296, by rfl⟩ : syracuseStep 2024395 = 3036593) B3036593
theorem B3843197 : Blo 2023435 3843197 := bbase (se 3 (by rfl) ⟨720599, by rfl⟩ : syracuseStep 3843197 = 1441199) (by norm_num)
theorem B2562131 : Blo 2023435 2562131 := bstep (se 1 (by rfl) ⟨1921598, by rfl⟩ : syracuseStep 2562131 = 3843197) B3843197
theorem B6832349 : Blo 2023435 6832349 := bstep (se 3 (by rfl) ⟨1281065, by rfl⟩ : syracuseStep 6832349 = 2562131) B2562131
theorem B4554899 : Blo 2023435 4554899 := bstep (se 1 (by rfl) ⟨3416174, by rfl⟩ : syracuseStep 4554899 = 6832349) B6832349
theorem B3036599 : Blo 2023435 3036599 := bstep (se 1 (by rfl) ⟨2277449, by rfl⟩ : syracuseStep 3036599 = 4554899) B4554899
theorem B2024399 : Blo 2023435 2024399 := bstep (se 1 (by rfl) ⟨1518299, by rfl⟩ : syracuseStep 2024399 = 3036599) B3036599
theorem B3036605 : Blo 2023435 3036605 := bbase (se 3 (by rfl) ⟨569363, by rfl⟩ : syracuseStep 3036605 = 1138727) (by norm_num)
theorem B2024403 : Blo 2023435 2024403 := bstep (se 1 (by rfl) ⟨1518302, by rfl⟩ : syracuseStep 2024403 = 3036605) B3036605
theorem B4554917 : Blo 2023435 4554917 := bbase (se 4 (by rfl) ⟨427023, by rfl⟩ : syracuseStep 4554917 = 854047) (by norm_num)
theorem B3036611 : Blo 2023435 3036611 := bstep (se 1 (by rfl) ⟨2277458, by rfl⟩ : syracuseStep 3036611 = 4554917) B4554917
theorem B2024407 : Blo 2023435 2024407 := bstep (se 1 (by rfl) ⟨1518305, by rfl⟩ : syracuseStep 2024407 = 3036611) B3036611
theorem B5124293 : Blo 2023435 5124293 := bbase (se 4 (by rfl) ⟨480402, by rfl⟩ : syracuseStep 5124293 = 960805) (by norm_num)
theorem B3416195 : Blo 2023435 3416195 := bstep (se 1 (by rfl) ⟨2562146, by rfl⟩ : syracuseStep 3416195 = 5124293) B5124293
theorem B2277463 : Blo 2023435 2277463 := bstep (se 1 (by rfl) ⟨1708097, by rfl⟩ : syracuseStep 2277463 = 3416195) B3416195
theorem B3036617 : Blo 2023435 3036617 := bstep (se 2 (by rfl) ⟨1138731, by rfl⟩ : syracuseStep 3036617 = 2277463) B2277463
theorem B2024411 : Blo 2023435 2024411 := bstep (se 1 (by rfl) ⟨1518308, by rfl⟩ : syracuseStep 2024411 = 3036617) B3036617
theorem B2308541 : Blo 2023435 2308541 := bbase (se 3 (by rfl) ⟨432851, by rfl⟩ : syracuseStep 2308541 = 865703) (by norm_num)
theorem B6156109 : Blo 2023435 6156109 := bstep (se 3 (by rfl) ⟨1154270, by rfl⟩ : syracuseStep 6156109 = 2308541) B2308541
theorem B8208145 : Blo 2023435 8208145 := bstep (se 2 (by rfl) ⟨3078054, by rfl⟩ : syracuseStep 8208145 = 6156109) B6156109
theorem B10944193 : Blo 2023435 10944193 := bstep (se 2 (by rfl) ⟨4104072, by rfl⟩ : syracuseStep 10944193 = 8208145) B8208145
theorem B14592257 : Blo 2023435 14592257 := bstep (se 2 (by rfl) ⟨5472096, by rfl⟩ : syracuseStep 14592257 = 10944193) B10944193
theorem B9728171 : Blo 2023435 9728171 := bstep (se 1 (by rfl) ⟨7296128, by rfl⟩ : syracuseStep 9728171 = 14592257) B14592257
theorem B6485447 : Blo 2023435 6485447 := bstep (se 1 (by rfl) ⟨4864085, by rfl⟩ : syracuseStep 6485447 = 9728171) B9728171
theorem B4323631 : Blo 2023435 4323631 := bstep (se 1 (by rfl) ⟨3242723, by rfl⟩ : syracuseStep 4323631 = 6485447) B6485447
theorem B5764841 : Blo 2023435 5764841 := bstep (se 2 (by rfl) ⟨2161815, by rfl⟩ : syracuseStep 5764841 = 4323631) B4323631
theorem B3843227 : Blo 2023435 3843227 := bstep (se 1 (by rfl) ⟨2882420, by rfl⟩ : syracuseStep 3843227 = 5764841) B5764841
theorem B10248605 : Blo 2023435 10248605 := bstep (se 3 (by rfl) ⟨1921613, by rfl⟩ : syracuseStep 10248605 = 3843227) B3843227
theorem B6832403 : Blo 2023435 6832403 := bstep (se 1 (by rfl) ⟨5124302, by rfl⟩ : syracuseStep 6832403 = 10248605) B10248605
theorem B4554935 : Blo 2023435 4554935 := bstep (se 1 (by rfl) ⟨3416201, by rfl⟩ : syracuseStep 4554935 = 6832403) B6832403
theorem B3036623 : Blo 2023435 3036623 := bstep (se 1 (by rfl) ⟨2277467, by rfl⟩ : syracuseStep 3036623 = 4554935) B4554935
theorem B2024415 : Blo 2023435 2024415 := bstep (se 1 (by rfl) ⟨1518311, by rfl⟩ : syracuseStep 2024415 = 3036623) B3036623
theorem B3036629 : Blo 2023435 3036629 := bbase (se 7 (by rfl) ⟨35585, by rfl⟩ : syracuseStep 3036629 = 71171) (by norm_num)
theorem B2024419 : Blo 2023435 2024419 := bstep (se 1 (by rfl) ⟨1518314, by rfl⟩ : syracuseStep 2024419 = 3036629) B3036629
theorem B7686485 : Blo 2023435 7686485 := bbase (se 10 (by rfl) ⟨11259, by rfl⟩ : syracuseStep 7686485 = 22519) (by norm_num)
theorem B5124323 : Blo 2023435 5124323 := bstep (se 1 (by rfl) ⟨3843242, by rfl⟩ : syracuseStep 5124323 = 7686485) B7686485
theorem B3416215 : Blo 2023435 3416215 := bstep (se 1 (by rfl) ⟨2562161, by rfl⟩ : syracuseStep 3416215 = 5124323) B5124323
theorem B4554953 : Blo 2023435 4554953 := bstep (se 2 (by rfl) ⟨1708107, by rfl⟩ : syracuseStep 4554953 = 3416215) B3416215
theorem B3036635 : Blo 2023435 3036635 := bstep (se 1 (by rfl) ⟨2277476, by rfl⟩ : syracuseStep 3036635 = 4554953) B4554953
theorem B2024423 : Blo 2023435 2024423 := bstep (se 1 (by rfl) ⟨1518317, by rfl⟩ : syracuseStep 2024423 = 3036635) B3036635
theorem B2277481 : Blo 2023435 2277481 := bbase (se 2 (by rfl) ⟨854055, by rfl⟩ : syracuseStep 2277481 = 1708111) (by norm_num)
theorem B3036641 : Blo 2023435 3036641 := bstep (se 2 (by rfl) ⟨1138740, by rfl⟩ : syracuseStep 3036641 = 2277481) B2277481
theorem B2024427 : Blo 2023435 2024427 := bstep (se 1 (by rfl) ⟨1518320, by rfl⟩ : syracuseStep 2024427 = 3036641) B3036641
theorem B3242749 : Blo 2023435 3242749 := bbase (se 3 (by rfl) ⟨608015, by rfl⟩ : syracuseStep 3242749 = 1216031) (by norm_num)
theorem B4323665 : Blo 2023435 4323665 := bstep (se 2 (by rfl) ⟨1621374, by rfl⟩ : syracuseStep 4323665 = 3242749) B3242749
theorem B11529773 : Blo 2023435 11529773 := bstep (se 3 (by rfl) ⟨2161832, by rfl⟩ : syracuseStep 11529773 = 4323665) B4323665
theorem B7686515 : Blo 2023435 7686515 := bstep (se 1 (by rfl) ⟨5764886, by rfl⟩ : syracuseStep 7686515 = 11529773) B11529773
theorem B5124343 : Blo 2023435 5124343 := bstep (se 1 (by rfl) ⟨3843257, by rfl⟩ : syracuseStep 5124343 = 7686515) B7686515
theorem B6832457 : Blo 2023435 6832457 := bstep (se 2 (by rfl) ⟨2562171, by rfl⟩ : syracuseStep 6832457 = 5124343) B5124343
theorem B4554971 : Blo 2023435 4554971 := bstep (se 1 (by rfl) ⟨3416228, by rfl⟩ : syracuseStep 4554971 = 6832457) B6832457
theorem B3036647 : Blo 2023435 3036647 := bstep (se 1 (by rfl) ⟨2277485, by rfl⟩ : syracuseStep 3036647 = 4554971) B4554971
theorem B2024431 : Blo 2023435 2024431 := bstep (se 1 (by rfl) ⟨1518323, by rfl⟩ : syracuseStep 2024431 = 3036647) B3036647
theorem B3036653 : Blo 2023435 3036653 := bbase (se 3 (by rfl) ⟨569372, by rfl⟩ : syracuseStep 3036653 = 1138745) (by norm_num)
theorem B2024435 : Blo 2023435 2024435 := bstep (se 1 (by rfl) ⟨1518326, by rfl⟩ : syracuseStep 2024435 = 3036653) B3036653
theorem B4554989 : Blo 2023435 4554989 := bbase (se 3 (by rfl) ⟨854060, by rfl⟩ : syracuseStep 4554989 = 1708121) (by norm_num)
theorem B3036659 : Blo 2023435 3036659 := bstep (se 1 (by rfl) ⟨2277494, by rfl⟩ : syracuseStep 3036659 = 4554989) B4554989
theorem B2024439 : Blo 2023435 2024439 := bstep (se 1 (by rfl) ⟨1518329, by rfl⟩ : syracuseStep 2024439 = 3036659) B3036659
theorem B2882461 : Blo 2023435 2882461 := bbase (se 3 (by rfl) ⟨540461, by rfl⟩ : syracuseStep 2882461 = 1080923) (by norm_num)
theorem B3843281 : Blo 2023435 3843281 := bstep (se 2 (by rfl) ⟨1441230, by rfl⟩ : syracuseStep 3843281 = 2882461) B2882461
theorem B2562187 : Blo 2023435 2562187 := bstep (se 1 (by rfl) ⟨1921640, by rfl⟩ : syracuseStep 2562187 = 3843281) B3843281
theorem B3416249 : Blo 2023435 3416249 := bstep (se 2 (by rfl) ⟨1281093, by rfl⟩ : syracuseStep 3416249 = 2562187) B2562187
theorem B2277499 : Blo 2023435 2277499 := bstep (se 1 (by rfl) ⟨1708124, by rfl⟩ : syracuseStep 2277499 = 3416249) B3416249
theorem B3036665 : Blo 2023435 3036665 := bstep (se 2 (by rfl) ⟨1138749, by rfl⟩ : syracuseStep 3036665 = 2277499) B2277499
theorem B2024443 : Blo 2023435 2024443 := bstep (se 1 (by rfl) ⟨1518332, by rfl⟩ : syracuseStep 2024443 = 3036665) B3036665
theorem B6925733 : Blo 2023435 6925733 := bbase (se 4 (by rfl) ⟨649287, by rfl⟩ : syracuseStep 6925733 = 1298575) (by norm_num)
theorem B4617155 : Blo 2023435 4617155 := bstep (se 1 (by rfl) ⟨3462866, by rfl⟩ : syracuseStep 4617155 = 6925733) B6925733
theorem B3078103 : Blo 2023435 3078103 := bstep (se 1 (by rfl) ⟨2308577, by rfl⟩ : syracuseStep 3078103 = 4617155) B4617155
theorem B4104137 : Blo 2023435 4104137 := bstep (se 2 (by rfl) ⟨1539051, by rfl⟩ : syracuseStep 4104137 = 3078103) B3078103
theorem B2736091 : Blo 2023435 2736091 := bstep (se 1 (by rfl) ⟨2052068, by rfl⟩ : syracuseStep 2736091 = 4104137) B4104137
theorem B3648121 : Blo 2023435 3648121 := bstep (se 2 (by rfl) ⟨1368045, by rfl⟩ : syracuseStep 3648121 = 2736091) B2736091
theorem B77826581 : Blo 2023435 77826581 := bstep (se 6 (by rfl) ⟨1824060, by rfl⟩ : syracuseStep 77826581 = 3648121) B3648121
theorem B51884387 : Blo 2023435 51884387 := bstep (se 1 (by rfl) ⟨38913290, by rfl⟩ : syracuseStep 51884387 = 77826581) B77826581
theorem B34589591 : Blo 2023435 34589591 := bstep (se 1 (by rfl) ⟨25942193, by rfl⟩ : syracuseStep 34589591 = 51884387) B51884387
theorem B23059727 : Blo 2023435 23059727 := bstep (se 1 (by rfl) ⟨17294795, by rfl⟩ : syracuseStep 23059727 = 34589591) B34589591
theorem B15373151 : Blo 2023435 15373151 := bstep (se 1 (by rfl) ⟨11529863, by rfl⟩ : syracuseStep 15373151 = 23059727) B23059727
theorem B10248767 : Blo 2023435 10248767 := bstep (se 1 (by rfl) ⟨7686575, by rfl⟩ : syracuseStep 10248767 = 15373151) B15373151
theorem B6832511 : Blo 2023435 6832511 := bstep (se 1 (by rfl) ⟨5124383, by rfl⟩ : syracuseStep 6832511 = 10248767) B10248767
theorem B4555007 : Blo 2023435 4555007 := bstep (se 1 (by rfl) ⟨3416255, by rfl⟩ : syracuseStep 4555007 = 6832511) B6832511
theorem B3036671 : Blo 2023435 3036671 := bstep (se 1 (by rfl) ⟨2277503, by rfl⟩ : syracuseStep 3036671 = 4555007) B4555007
theorem B2024447 : Blo 2023435 2024447 := bstep (se 1 (by rfl) ⟨1518335, by rfl⟩ : syracuseStep 2024447 = 3036671) B3036671
theorem B3036677 : Blo 2023435 3036677 := bbase (se 4 (by rfl) ⟨284688, by rfl⟩ : syracuseStep 3036677 = 569377) (by norm_num)
theorem B2024451 : Blo 2023435 2024451 := bstep (se 1 (by rfl) ⟨1518338, by rfl⟩ : syracuseStep 2024451 = 3036677) B3036677
theorem B3416269 : Blo 2023435 3416269 := bbase (se 3 (by rfl) ⟨640550, by rfl⟩ : syracuseStep 3416269 = 1281101) (by norm_num)
theorem B4555025 : Blo 2023435 4555025 := bstep (se 2 (by rfl) ⟨1708134, by rfl⟩ : syracuseStep 4555025 = 3416269) B3416269
theorem B3036683 : Blo 2023435 3036683 := bstep (se 1 (by rfl) ⟨2277512, by rfl⟩ : syracuseStep 3036683 = 4555025) B4555025
theorem B2024455 : Blo 2023435 2024455 := bstep (se 1 (by rfl) ⟨1518341, by rfl⟩ : syracuseStep 2024455 = 3036683) B3036683
theorem B2277517 : Blo 2023435 2277517 := bbase (se 3 (by rfl) ⟨427034, by rfl⟩ : syracuseStep 2277517 = 854069) (by norm_num)
theorem B3036689 : Blo 2023435 3036689 := bstep (se 2 (by rfl) ⟨1138758, by rfl⟩ : syracuseStep 3036689 = 2277517) B2277517
theorem B2024459 : Blo 2023435 2024459 := bstep (se 1 (by rfl) ⟨1518344, by rfl⟩ : syracuseStep 2024459 = 3036689) B3036689
theorem B6832565 : Blo 2023435 6832565 := bbase (se 5 (by rfl) ⟨320276, by rfl⟩ : syracuseStep 6832565 = 640553) (by norm_num)
theorem B4555043 : Blo 2023435 4555043 := bstep (se 1 (by rfl) ⟨3416282, by rfl⟩ : syracuseStep 4555043 = 6832565) B6832565
theorem B3036695 : Blo 2023435 3036695 := bstep (se 1 (by rfl) ⟨2277521, by rfl⟩ : syracuseStep 3036695 = 4555043) B4555043
theorem B2024463 : Blo 2023435 2024463 := bstep (se 1 (by rfl) ⟨1518347, by rfl⟩ : syracuseStep 2024463 = 3036695) B3036695
theorem B3036701 : Blo 2023435 3036701 := bbase (se 3 (by rfl) ⟨569381, by rfl⟩ : syracuseStep 3036701 = 1138763) (by norm_num)
theorem B2024467 : Blo 2023435 2024467 := bstep (se 1 (by rfl) ⟨1518350, by rfl⟩ : syracuseStep 2024467 = 3036701) B3036701
theorem B4555061 : Blo 2023435 4555061 := bbase (se 5 (by rfl) ⟨213518, by rfl⟩ : syracuseStep 4555061 = 427037) (by norm_num)
theorem B3036707 : Blo 2023435 3036707 := bstep (se 1 (by rfl) ⟨2277530, by rfl⟩ : syracuseStep 3036707 = 4555061) B4555061
theorem B2024471 : Blo 2023435 2024471 := bstep (se 1 (by rfl) ⟨1518353, by rfl⟩ : syracuseStep 2024471 = 3036707) B3036707
theorem B2052097 : Blo 2023435 2052097 := bbase (se 2 (by rfl) ⟨769536, by rfl⟩ : syracuseStep 2052097 = 1539073) (by norm_num)
theorem B43778069 : Blo 2023435 43778069 := bstep (se 6 (by rfl) ⟨1026048, by rfl⟩ : syracuseStep 43778069 = 2052097) B2052097
theorem B29185379 : Blo 2023435 29185379 := bstep (se 1 (by rfl) ⟨21889034, by rfl⟩ : syracuseStep 29185379 = 43778069) B43778069
theorem B19456919 : Blo 2023435 19456919 := bstep (se 1 (by rfl) ⟨14592689, by rfl⟩ : syracuseStep 19456919 = 29185379) B29185379
theorem B12971279 : Blo 2023435 12971279 := bstep (se 1 (by rfl) ⟨9728459, by rfl⟩ : syracuseStep 12971279 = 19456919) B19456919
theorem B8647519 : Blo 2023435 8647519 := bstep (se 1 (by rfl) ⟨6485639, by rfl⟩ : syracuseStep 8647519 = 12971279) B12971279
theorem B11530025 : Blo 2023435 11530025 := bstep (se 2 (by rfl) ⟨4323759, by rfl⟩ : syracuseStep 11530025 = 8647519) B8647519
theorem B7686683 : Blo 2023435 7686683 := bstep (se 1 (by rfl) ⟨5765012, by rfl⟩ : syracuseStep 7686683 = 11530025) B11530025
theorem B5124455 : Blo 2023435 5124455 := bstep (se 1 (by rfl) ⟨3843341, by rfl⟩ : syracuseStep 5124455 = 7686683) B7686683
theorem B3416303 : Blo 2023435 3416303 := bstep (se 1 (by rfl) ⟨2562227, by rfl⟩ : syracuseStep 3416303 = 5124455) B5124455
theorem B2277535 : Blo 2023435 2277535 := bstep (se 1 (by rfl) ⟨1708151, by rfl⟩ : syracuseStep 2277535 = 3416303) B3416303
theorem B3036713 : Blo 2023435 3036713 := bstep (se 2 (by rfl) ⟨1138767, by rfl⟩ : syracuseStep 3036713 = 2277535) B2277535
theorem B2024475 : Blo 2023435 2024475 := bstep (se 1 (by rfl) ⟨1518356, by rfl⟩ : syracuseStep 2024475 = 3036713) B3036713
theorem B5194381 : Blo 2023435 5194381 := bbase (se 3 (by rfl) ⟨973946, by rfl⟩ : syracuseStep 5194381 = 1947893) (by norm_num)
theorem B6925841 : Blo 2023435 6925841 := bstep (se 2 (by rfl) ⟨2597190, by rfl⟩ : syracuseStep 6925841 = 5194381) B5194381
theorem B4617227 : Blo 2023435 4617227 := bstep (se 1 (by rfl) ⟨3462920, by rfl⟩ : syracuseStep 4617227 = 6925841) B6925841
theorem B12312605 : Blo 2023435 12312605 := bstep (se 3 (by rfl) ⟨2308613, by rfl⟩ : syracuseStep 12312605 = 4617227) B4617227
theorem B32833613 : Blo 2023435 32833613 := bstep (se 3 (by rfl) ⟨6156302, by rfl⟩ : syracuseStep 32833613 = 12312605) B12312605
theorem B21889075 : Blo 2023435 21889075 := bstep (se 1 (by rfl) ⟨16416806, by rfl⟩ : syracuseStep 21889075 = 32833613) B32833613
theorem B29185433 : Blo 2023435 29185433 := bstep (se 2 (by rfl) ⟨10944537, by rfl⟩ : syracuseStep 29185433 = 21889075) B21889075
theorem B19456955 : Blo 2023435 19456955 := bstep (se 1 (by rfl) ⟨14592716, by rfl⟩ : syracuseStep 19456955 = 29185433) B29185433
theorem B12971303 : Blo 2023435 12971303 := bstep (se 1 (by rfl) ⟨9728477, by rfl⟩ : syracuseStep 12971303 = 19456955) B19456955
theorem B8647535 : Blo 2023435 8647535 := bstep (se 1 (by rfl) ⟨6485651, by rfl⟩ : syracuseStep 8647535 = 12971303) B12971303
theorem B5765023 : Blo 2023435 5765023 := bstep (se 1 (by rfl) ⟨4323767, by rfl⟩ : syracuseStep 5765023 = 8647535) B8647535
theorem B7686697 : Blo 2023435 7686697 := bstep (se 2 (by rfl) ⟨2882511, by rfl⟩ : syracuseStep 7686697 = 5765023) B5765023
theorem B10248929 : Blo 2023435 10248929 := bstep (se 2 (by rfl) ⟨3843348, by rfl⟩ : syracuseStep 10248929 = 7686697) B7686697
theorem B6832619 : Blo 2023435 6832619 := bstep (se 1 (by rfl) ⟨5124464, by rfl⟩ : syracuseStep 6832619 = 10248929) B10248929
theorem B4555079 : Blo 2023435 4555079 := bstep (se 1 (by rfl) ⟨3416309, by rfl⟩ : syracuseStep 4555079 = 6832619) B6832619
theorem B3036719 : Blo 2023435 3036719 := bstep (se 1 (by rfl) ⟨2277539, by rfl⟩ : syracuseStep 3036719 = 4555079) B4555079
theorem B2024479 : Blo 2023435 2024479 := bstep (se 1 (by rfl) ⟨1518359, by rfl⟩ : syracuseStep 2024479 = 3036719) B3036719
theorem B3036725 : Blo 2023435 3036725 := bbase (se 5 (by rfl) ⟨142346, by rfl⟩ : syracuseStep 3036725 = 284693) (by norm_num)
theorem B2024483 : Blo 2023435 2024483 := bstep (se 1 (by rfl) ⟨1518362, by rfl⟩ : syracuseStep 2024483 = 3036725) B3036725
theorem B5124485 : Blo 2023435 5124485 := bbase (se 4 (by rfl) ⟨480420, by rfl⟩ : syracuseStep 5124485 = 960841) (by norm_num)
theorem B3416323 : Blo 2023435 3416323 := bstep (se 1 (by rfl) ⟨2562242, by rfl⟩ : syracuseStep 3416323 = 5124485) B5124485
theorem B4555097 : Blo 2023435 4555097 := bstep (se 2 (by rfl) ⟨1708161, by rfl⟩ : syracuseStep 4555097 = 3416323) B3416323
theorem B3036731 : Blo 2023435 3036731 := bstep (se 1 (by rfl) ⟨2277548, by rfl⟩ : syracuseStep 3036731 = 4555097) B4555097
theorem B2024487 : Blo 2023435 2024487 := bstep (se 1 (by rfl) ⟨1518365, by rfl⟩ : syracuseStep 2024487 = 3036731) B3036731
theorem B2277553 : Blo 2023435 2277553 := bbase (se 2 (by rfl) ⟨854082, by rfl⟩ : syracuseStep 2277553 = 1708165) (by norm_num)
theorem B3036737 : Blo 2023435 3036737 := bstep (se 2 (by rfl) ⟨1138776, by rfl⟩ : syracuseStep 3036737 = 2277553) B2277553
theorem B2024491 : Blo 2023435 2024491 := bstep (se 1 (by rfl) ⟨1518368, by rfl⟩ : syracuseStep 2024491 = 3036737) B3036737
theorem B2161901 : Blo 2023435 2161901 := bbase (se 3 (by rfl) ⟨405356, by rfl⟩ : syracuseStep 2161901 = 810713) (by norm_num)
theorem B5765069 : Blo 2023435 5765069 := bstep (se 3 (by rfl) ⟨1080950, by rfl⟩ : syracuseStep 5765069 = 2161901) B2161901
theorem B3843379 : Blo 2023435 3843379 := bstep (se 1 (by rfl) ⟨2882534, by rfl⟩ : syracuseStep 3843379 = 5765069) B5765069
theorem B5124505 : Blo 2023435 5124505 := bstep (se 2 (by rfl) ⟨1921689, by rfl⟩ : syracuseStep 5124505 = 3843379) B3843379
theorem B6832673 : Blo 2023435 6832673 := bstep (se 2 (by rfl) ⟨2562252, by rfl⟩ : syracuseStep 6832673 = 5124505) B5124505
theorem B4555115 : Blo 2023435 4555115 := bstep (se 1 (by rfl) ⟨3416336, by rfl⟩ : syracuseStep 4555115 = 6832673) B6832673
theorem B3036743 : Blo 2023435 3036743 := bstep (se 1 (by rfl) ⟨2277557, by rfl⟩ : syracuseStep 3036743 = 4555115) B4555115
theorem B2024495 : Blo 2023435 2024495 := bstep (se 1 (by rfl) ⟨1518371, by rfl⟩ : syracuseStep 2024495 = 3036743) B3036743
theorem B3036749 : Blo 2023435 3036749 := bbase (se 3 (by rfl) ⟨569390, by rfl⟩ : syracuseStep 3036749 = 1138781) (by norm_num)
theorem B2024499 : Blo 2023435 2024499 := bstep (se 1 (by rfl) ⟨1518374, by rfl⟩ : syracuseStep 2024499 = 3036749) B3036749
theorem B4555133 : Blo 2023435 4555133 := bbase (se 3 (by rfl) ⟨854087, by rfl⟩ : syracuseStep 4555133 = 1708175) (by norm_num)
theorem B3036755 : Blo 2023435 3036755 := bstep (se 1 (by rfl) ⟨2277566, by rfl⟩ : syracuseStep 3036755 = 4555133) B4555133
theorem B2024503 : Blo 2023435 2024503 := bstep (se 1 (by rfl) ⟨1518377, by rfl⟩ : syracuseStep 2024503 = 3036755) B3036755
theorem B3416357 : Blo 2023435 3416357 := bbase (se 4 (by rfl) ⟨320283, by rfl⟩ : syracuseStep 3416357 = 640567) (by norm_num)
theorem B2277571 : Blo 2023435 2277571 := bstep (se 1 (by rfl) ⟨1708178, by rfl⟩ : syracuseStep 2277571 = 3416357) B3416357
theorem B3036761 : Blo 2023435 3036761 := bstep (se 2 (by rfl) ⟨1138785, by rfl⟩ : syracuseStep 3036761 = 2277571) B2277571
theorem B2024507 : Blo 2023435 2024507 := bstep (se 1 (by rfl) ⟨1518380, by rfl⟩ : syracuseStep 2024507 = 3036761) B3036761
theorem B2882557 : Blo 2023435 2882557 := bbase (se 3 (by rfl) ⟨540479, by rfl⟩ : syracuseStep 2882557 = 1080959) (by norm_num)
theorem B15373637 : Blo 2023435 15373637 := bstep (se 4 (by rfl) ⟨1441278, by rfl⟩ : syracuseStep 15373637 = 2882557) B2882557
theorem B10249091 : Blo 2023435 10249091 := bstep (se 1 (by rfl) ⟨7686818, by rfl⟩ : syracuseStep 10249091 = 15373637) B15373637
theorem B6832727 : Blo 2023435 6832727 := bstep (se 1 (by rfl) ⟨5124545, by rfl⟩ : syracuseStep 6832727 = 10249091) B10249091
theorem B4555151 : Blo 2023435 4555151 := bstep (se 1 (by rfl) ⟨3416363, by rfl⟩ : syracuseStep 4555151 = 6832727) B6832727
theorem B3036767 : Blo 2023435 3036767 := bstep (se 1 (by rfl) ⟨2277575, by rfl⟩ : syracuseStep 3036767 = 4555151) B4555151
theorem B2024511 : Blo 2023435 2024511 := bstep (se 1 (by rfl) ⟨1518383, by rfl⟩ : syracuseStep 2024511 = 3036767) B3036767
theorem B3036773 : Blo 2023435 3036773 := bbase (se 4 (by rfl) ⟨284697, by rfl⟩ : syracuseStep 3036773 = 569395) (by norm_num)
theorem B2024515 : Blo 2023435 2024515 := bstep (se 1 (by rfl) ⟨1518386, by rfl⟩ : syracuseStep 2024515 = 3036773) B3036773
theorem B3648253 : Blo 2023435 3648253 := bbase (se 3 (by rfl) ⟨684047, by rfl⟩ : syracuseStep 3648253 = 1368095) (by norm_num)
theorem B4864337 : Blo 2023435 4864337 := bstep (se 2 (by rfl) ⟨1824126, by rfl⟩ : syracuseStep 4864337 = 3648253) B3648253
theorem B3242891 : Blo 2023435 3242891 := bstep (se 1 (by rfl) ⟨2432168, by rfl⟩ : syracuseStep 3242891 = 4864337) B4864337
theorem B2161927 : Blo 2023435 2161927 := bstep (se 1 (by rfl) ⟨1621445, by rfl⟩ : syracuseStep 2161927 = 3242891) B3242891
theorem B2882569 : Blo 2023435 2882569 := bstep (se 2 (by rfl) ⟨1080963, by rfl⟩ : syracuseStep 2882569 = 2161927) B2161927
theorem B3843425 : Blo 2023435 3843425 := bstep (se 2 (by rfl) ⟨1441284, by rfl⟩ : syracuseStep 3843425 = 2882569) B2882569
theorem B2562283 : Blo 2023435 2562283 := bstep (se 1 (by rfl) ⟨1921712, by rfl⟩ : syracuseStep 2562283 = 3843425) B3843425
theorem B3416377 : Blo 2023435 3416377 := bstep (se 2 (by rfl) ⟨1281141, by rfl⟩ : syracuseStep 3416377 = 2562283) B2562283
theorem B4555169 : Blo 2023435 4555169 := bstep (se 2 (by rfl) ⟨1708188, by rfl⟩ : syracuseStep 4555169 = 3416377) B3416377
theorem B3036779 : Blo 2023435 3036779 := bstep (se 1 (by rfl) ⟨2277584, by rfl⟩ : syracuseStep 3036779 = 4555169) B4555169
theorem B2024519 : Blo 2023435 2024519 := bstep (se 1 (by rfl) ⟨1518389, by rfl⟩ : syracuseStep 2024519 = 3036779) B3036779
theorem B2277589 : Blo 2023435 2277589 := bbase (se 7 (by rfl) ⟨26690, by rfl⟩ : syracuseStep 2277589 = 53381) (by norm_num)
theorem B3036785 : Blo 2023435 3036785 := bstep (se 2 (by rfl) ⟨1138794, by rfl⟩ : syracuseStep 3036785 = 2277589) B2277589
theorem B2024523 : Blo 2023435 2024523 := bstep (se 1 (by rfl) ⟨1518392, by rfl⟩ : syracuseStep 2024523 = 3036785) B3036785
theorem B2562293 : Blo 2023435 2562293 := bbase (se 5 (by rfl) ⟨120107, by rfl⟩ : syracuseStep 2562293 = 240215) (by norm_num)
theorem B6832781 : Blo 2023435 6832781 := bstep (se 3 (by rfl) ⟨1281146, by rfl⟩ : syracuseStep 6832781 = 2562293) B2562293
theorem B4555187 : Blo 2023435 4555187 := bstep (se 1 (by rfl) ⟨3416390, by rfl⟩ : syracuseStep 4555187 = 6832781) B6832781
theorem B3036791 : Blo 2023435 3036791 := bstep (se 1 (by rfl) ⟨2277593, by rfl⟩ : syracuseStep 3036791 = 4555187) B4555187
theorem B2024527 : Blo 2023435 2024527 := bstep (se 1 (by rfl) ⟨1518395, by rfl⟩ : syracuseStep 2024527 = 3036791) B3036791
theorem B3036797 : Blo 2023435 3036797 := bbase (se 3 (by rfl) ⟨569399, by rfl⟩ : syracuseStep 3036797 = 1138799) (by norm_num)
theorem B2024531 : Blo 2023435 2024531 := bstep (se 1 (by rfl) ⟨1518398, by rfl⟩ : syracuseStep 2024531 = 3036797) B3036797
theorem B4555205 : Blo 2023435 4555205 := bbase (se 4 (by rfl) ⟨427050, by rfl⟩ : syracuseStep 4555205 = 854101) (by norm_num)
theorem B3036803 : Blo 2023435 3036803 := bstep (se 1 (by rfl) ⟨2277602, by rfl⟩ : syracuseStep 3036803 = 4555205) B4555205
theorem B2024535 : Blo 2023435 2024535 := bstep (se 1 (by rfl) ⟨1518401, by rfl⟩ : syracuseStep 2024535 = 3036803) B3036803
theorem B6485845 : Blo 2023435 6485845 := bbase (se 9 (by rfl) ⟨19001, by rfl⟩ : syracuseStep 6485845 = 38003) (by norm_num)
theorem B8647793 : Blo 2023435 8647793 := bstep (se 2 (by rfl) ⟨3242922, by rfl⟩ : syracuseStep 8647793 = 6485845) B6485845
theorem B5765195 : Blo 2023435 5765195 := bstep (se 1 (by rfl) ⟨4323896, by rfl⟩ : syracuseStep 5765195 = 8647793) B8647793
theorem B3843463 : Blo 2023435 3843463 := bstep (se 1 (by rfl) ⟨2882597, by rfl⟩ : syracuseStep 3843463 = 5765195) B5765195
theorem B5124617 : Blo 2023435 5124617 := bstep (se 2 (by rfl) ⟨1921731, by rfl⟩ : syracuseStep 5124617 = 3843463) B3843463
theorem B3416411 : Blo 2023435 3416411 := bstep (se 1 (by rfl) ⟨2562308, by rfl⟩ : syracuseStep 3416411 = 5124617) B5124617
theorem B2277607 : Blo 2023435 2277607 := bstep (se 1 (by rfl) ⟨1708205, by rfl⟩ : syracuseStep 2277607 = 3416411) B3416411
theorem B3036809 : Blo 2023435 3036809 := bstep (se 2 (by rfl) ⟨1138803, by rfl⟩ : syracuseStep 3036809 = 2277607) B2277607
theorem B2024539 : Blo 2023435 2024539 := bstep (se 1 (by rfl) ⟨1518404, by rfl⟩ : syracuseStep 2024539 = 3036809) B3036809
theorem B10249253 : Blo 2023435 10249253 := bbase (se 4 (by rfl) ⟨960867, by rfl⟩ : syracuseStep 10249253 = 1921735) (by norm_num)
theorem B6832835 : Blo 2023435 6832835 := bstep (se 1 (by rfl) ⟨5124626, by rfl⟩ : syracuseStep 6832835 = 10249253) B10249253
theorem B4555223 : Blo 2023435 4555223 := bstep (se 1 (by rfl) ⟨3416417, by rfl⟩ : syracuseStep 4555223 = 6832835) B6832835
theorem B3036815 : Blo 2023435 3036815 := bstep (se 1 (by rfl) ⟨2277611, by rfl⟩ : syracuseStep 3036815 = 4555223) B4555223
theorem B2024543 : Blo 2023435 2024543 := bstep (se 1 (by rfl) ⟨1518407, by rfl⟩ : syracuseStep 2024543 = 3036815) B3036815
theorem B3036821 : Blo 2023435 3036821 := bbase (se 6 (by rfl) ⟨71175, by rfl⟩ : syracuseStep 3036821 = 142351) (by norm_num)
theorem B2024547 : Blo 2023435 2024547 := bstep (se 1 (by rfl) ⟨1518410, by rfl⟩ : syracuseStep 2024547 = 3036821) B3036821
theorem B12971765 : Blo 2023435 12971765 := bbase (se 5 (by rfl) ⟨608051, by rfl⟩ : syracuseStep 12971765 = 1216103) (by norm_num)
theorem B8647843 : Blo 2023435 8647843 := bstep (se 1 (by rfl) ⟨6485882, by rfl⟩ : syracuseStep 8647843 = 12971765) B12971765
theorem B11530457 : Blo 2023435 11530457 := bstep (se 2 (by rfl) ⟨4323921, by rfl⟩ : syracuseStep 11530457 = 8647843) B8647843
theorem B7686971 : Blo 2023435 7686971 := bstep (se 1 (by rfl) ⟨5765228, by rfl⟩ : syracuseStep 7686971 = 11530457) B11530457
theorem B5124647 : Blo 2023435 5124647 := bstep (se 1 (by rfl) ⟨3843485, by rfl⟩ : syracuseStep 5124647 = 7686971) B7686971
theorem B3416431 : Blo 2023435 3416431 := bstep (se 1 (by rfl) ⟨2562323, by rfl⟩ : syracuseStep 3416431 = 5124647) B5124647
theorem B4555241 : Blo 2023435 4555241 := bstep (se 2 (by rfl) ⟨1708215, by rfl⟩ : syracuseStep 4555241 = 3416431) B3416431
theorem B3036827 : Blo 2023435 3036827 := bstep (se 1 (by rfl) ⟨2277620, by rfl⟩ : syracuseStep 3036827 = 4555241) B4555241
theorem B2024551 : Blo 2023435 2024551 := bstep (se 1 (by rfl) ⟨1518413, by rfl⟩ : syracuseStep 2024551 = 3036827) B3036827
theorem B2277625 : Blo 2023435 2277625 := bbase (se 2 (by rfl) ⟨854109, by rfl⟩ : syracuseStep 2277625 = 1708219) (by norm_num)
theorem B3036833 : Blo 2023435 3036833 := bstep (se 2 (by rfl) ⟨1138812, by rfl⟩ : syracuseStep 3036833 = 2277625) B2277625
theorem B2024555 : Blo 2023435 2024555 := bstep (se 1 (by rfl) ⟨1518416, by rfl⟩ : syracuseStep 2024555 = 3036833) B3036833
theorem B8647877 : Blo 2023435 8647877 := bbase (se 4 (by rfl) ⟨810738, by rfl⟩ : syracuseStep 8647877 = 1621477) (by norm_num)
theorem B5765251 : Blo 2023435 5765251 := bstep (se 1 (by rfl) ⟨4323938, by rfl⟩ : syracuseStep 5765251 = 8647877) B8647877
theorem B7687001 : Blo 2023435 7687001 := bstep (se 2 (by rfl) ⟨2882625, by rfl⟩ : syracuseStep 7687001 = 5765251) B5765251
theorem B5124667 : Blo 2023435 5124667 := bstep (se 1 (by rfl) ⟨3843500, by rfl⟩ : syracuseStep 5124667 = 7687001) B7687001
theorem B6832889 : Blo 2023435 6832889 := bstep (se 2 (by rfl) ⟨2562333, by rfl⟩ : syracuseStep 6832889 = 5124667) B5124667
theorem B4555259 : Blo 2023435 4555259 := bstep (se 1 (by rfl) ⟨3416444, by rfl⟩ : syracuseStep 4555259 = 6832889) B6832889
theorem B3036839 : Blo 2023435 3036839 := bstep (se 1 (by rfl) ⟨2277629, by rfl⟩ : syracuseStep 3036839 = 4555259) B4555259
theorem B2024559 : Blo 2023435 2024559 := bstep (se 1 (by rfl) ⟨1518419, by rfl⟩ : syracuseStep 2024559 = 3036839) B3036839
theorem B3036845 : Blo 2023435 3036845 := bbase (se 3 (by rfl) ⟨569408, by rfl⟩ : syracuseStep 3036845 = 1138817) (by norm_num)
theorem B2024563 : Blo 2023435 2024563 := bstep (se 1 (by rfl) ⟨1518422, by rfl⟩ : syracuseStep 2024563 = 3036845) B3036845
theorem B4555277 : Blo 2023435 4555277 := bbase (se 3 (by rfl) ⟨854114, by rfl⟩ : syracuseStep 4555277 = 1708229) (by norm_num)
theorem B3036851 : Blo 2023435 3036851 := bstep (se 1 (by rfl) ⟨2277638, by rfl⟩ : syracuseStep 3036851 = 4555277) B4555277
theorem B2024567 : Blo 2023435 2024567 := bstep (se 1 (by rfl) ⟨1518425, by rfl⟩ : syracuseStep 2024567 = 3036851) B3036851
theorem B2562349 : Blo 2023435 2562349 := bbase (se 3 (by rfl) ⟨480440, by rfl⟩ : syracuseStep 2562349 = 960881) (by norm_num)
theorem B3416465 : Blo 2023435 3416465 := bstep (se 2 (by rfl) ⟨1281174, by rfl⟩ : syracuseStep 3416465 = 2562349) B2562349
theorem B2277643 : Blo 2023435 2277643 := bstep (se 1 (by rfl) ⟨1708232, by rfl⟩ : syracuseStep 2277643 = 3416465) B3416465
theorem B3036857 : Blo 2023435 3036857 := bstep (se 2 (by rfl) ⟨1138821, by rfl⟩ : syracuseStep 3036857 = 2277643) B2277643
theorem B2024571 : Blo 2023435 2024571 := bstep (se 1 (by rfl) ⟨1518428, by rfl⟩ : syracuseStep 2024571 = 3036857) B3036857
theorem B4864469 : Blo 2023435 4864469 := bbase (se 7 (by rfl) ⟨57005, by rfl⟩ : syracuseStep 4864469 = 114011) (by norm_num)
theorem B12971917 : Blo 2023435 12971917 := bstep (se 3 (by rfl) ⟨2432234, by rfl⟩ : syracuseStep 12971917 = 4864469) B4864469
theorem B17295889 : Blo 2023435 17295889 := bstep (se 2 (by rfl) ⟨6485958, by rfl⟩ : syracuseStep 17295889 = 12971917) B12971917
theorem B23061185 : Blo 2023435 23061185 := bstep (se 2 (by rfl) ⟨8647944, by rfl⟩ : syracuseStep 23061185 = 17295889) B17295889
theorem B15374123 : Blo 2023435 15374123 := bstep (se 1 (by rfl) ⟨11530592, by rfl⟩ : syracuseStep 15374123 = 23061185) B23061185
theorem B10249415 : Blo 2023435 10249415 := bstep (se 1 (by rfl) ⟨7687061, by rfl⟩ : syracuseStep 10249415 = 15374123) B15374123
theorem B6832943 : Blo 2023435 6832943 := bstep (se 1 (by rfl) ⟨5124707, by rfl⟩ : syracuseStep 6832943 = 10249415) B10249415
theorem B4555295 : Blo 2023435 4555295 := bstep (se 1 (by rfl) ⟨3416471, by rfl⟩ : syracuseStep 4555295 = 6832943) B6832943
theorem B3036863 : Blo 2023435 3036863 := bstep (se 1 (by rfl) ⟨2277647, by rfl⟩ : syracuseStep 3036863 = 4555295) B4555295
theorem B2024575 : Blo 2023435 2024575 := bstep (se 1 (by rfl) ⟨1518431, by rfl⟩ : syracuseStep 2024575 = 3036863) B3036863
theorem B3036869 : Blo 2023435 3036869 := bbase (se 4 (by rfl) ⟨284706, by rfl⟩ : syracuseStep 3036869 = 569413) (by norm_num)
theorem B2024579 : Blo 2023435 2024579 := bstep (se 1 (by rfl) ⟨1518434, by rfl⟩ : syracuseStep 2024579 = 3036869) B3036869
theorem B3416485 : Blo 2023435 3416485 := bbase (se 4 (by rfl) ⟨320295, by rfl⟩ : syracuseStep 3416485 = 640591) (by norm_num)
theorem B4555313 : Blo 2023435 4555313 := bstep (se 2 (by rfl) ⟨1708242, by rfl⟩ : syracuseStep 4555313 = 3416485) B3416485
theorem B3036875 : Blo 2023435 3036875 := bstep (se 1 (by rfl) ⟨2277656, by rfl⟩ : syracuseStep 3036875 = 4555313) B4555313
theorem B2024583 : Blo 2023435 2024583 := bstep (se 1 (by rfl) ⟨1518437, by rfl⟩ : syracuseStep 2024583 = 3036875) B3036875
theorem B2277661 : Blo 2023435 2277661 := bbase (se 3 (by rfl) ⟨427061, by rfl⟩ : syracuseStep 2277661 = 854123) (by norm_num)
theorem B3036881 : Blo 2023435 3036881 := bstep (se 2 (by rfl) ⟨1138830, by rfl⟩ : syracuseStep 3036881 = 2277661) B2277661
theorem B2024587 : Blo 2023435 2024587 := bstep (se 1 (by rfl) ⟨1518440, by rfl⟩ : syracuseStep 2024587 = 3036881) B3036881
theorem B6832997 : Blo 2023435 6832997 := bbase (se 4 (by rfl) ⟨640593, by rfl⟩ : syracuseStep 6832997 = 1281187) (by norm_num)
theorem B4555331 : Blo 2023435 4555331 := bstep (se 1 (by rfl) ⟨3416498, by rfl⟩ : syracuseStep 4555331 = 6832997) B6832997
theorem B3036887 : Blo 2023435 3036887 := bstep (se 1 (by rfl) ⟨2277665, by rfl⟩ : syracuseStep 3036887 = 4555331) B4555331
theorem B2024591 : Blo 2023435 2024591 := bstep (se 1 (by rfl) ⟨1518443, by rfl⟩ : syracuseStep 2024591 = 3036887) B3036887
theorem B3036893 : Blo 2023435 3036893 := bbase (se 3 (by rfl) ⟨569417, by rfl⟩ : syracuseStep 3036893 = 1138835) (by norm_num)
theorem B2024595 : Blo 2023435 2024595 := bstep (se 1 (by rfl) ⟨1518446, by rfl⟩ : syracuseStep 2024595 = 3036893) B3036893
theorem B4555349 : Blo 2023435 4555349 := bbase (se 8 (by rfl) ⟨26691, by rfl⟩ : syracuseStep 4555349 = 53383) (by norm_num)
theorem B3036899 : Blo 2023435 3036899 := bstep (se 1 (by rfl) ⟨2277674, by rfl⟩ : syracuseStep 3036899 = 4555349) B4555349
theorem B2024599 : Blo 2023435 2024599 := bstep (se 1 (by rfl) ⟨1518449, by rfl⟩ : syracuseStep 2024599 = 3036899) B3036899
theorem B2432269 : Blo 2023435 2432269 := bbase (se 3 (by rfl) ⟨456050, by rfl⟩ : syracuseStep 2432269 = 912101) (by norm_num)
theorem B3243025 : Blo 2023435 3243025 := bstep (se 2 (by rfl) ⟨1216134, by rfl⟩ : syracuseStep 3243025 = 2432269) B2432269
theorem B4324033 : Blo 2023435 4324033 := bstep (se 2 (by rfl) ⟨1621512, by rfl⟩ : syracuseStep 4324033 = 3243025) B3243025
theorem B5765377 : Blo 2023435 5765377 := bstep (se 2 (by rfl) ⟨2162016, by rfl⟩ : syracuseStep 5765377 = 4324033) B4324033
theorem B7687169 : Blo 2023435 7687169 := bstep (se 2 (by rfl) ⟨2882688, by rfl⟩ : syracuseStep 7687169 = 5765377) B5765377
theorem B5124779 : Blo 2023435 5124779 := bstep (se 1 (by rfl) ⟨3843584, by rfl⟩ : syracuseStep 5124779 = 7687169) B7687169
theorem B3416519 : Blo 2023435 3416519 := bstep (se 1 (by rfl) ⟨2562389, by rfl⟩ : syracuseStep 3416519 = 5124779) B5124779
theorem B2277679 : Blo 2023435 2277679 := bstep (se 1 (by rfl) ⟨1708259, by rfl⟩ : syracuseStep 2277679 = 3416519) B3416519
theorem B3036905 : Blo 2023435 3036905 := bstep (se 2 (by rfl) ⟨1138839, by rfl⟩ : syracuseStep 3036905 = 2277679) B2277679
theorem B2024603 : Blo 2023435 2024603 := bstep (se 1 (by rfl) ⟨1518452, by rfl⟩ : syracuseStep 2024603 = 3036905) B3036905
theorem B2432273 : Blo 2023435 2432273 := bbase (se 2 (by rfl) ⟨912102, by rfl⟩ : syracuseStep 2432273 = 1824205) (by norm_num)
theorem B25944245 : Blo 2023435 25944245 := bstep (se 5 (by rfl) ⟨1216136, by rfl⟩ : syracuseStep 25944245 = 2432273) B2432273
theorem B17296163 : Blo 2023435 17296163 := bstep (se 1 (by rfl) ⟨12972122, by rfl⟩ : syracuseStep 17296163 = 25944245) B25944245
theorem B11530775 : Blo 2023435 11530775 := bstep (se 1 (by rfl) ⟨8648081, by rfl⟩ : syracuseStep 11530775 = 17296163) B17296163
theorem B7687183 : Blo 2023435 7687183 := bstep (se 1 (by rfl) ⟨5765387, by rfl⟩ : syracuseStep 7687183 = 11530775) B11530775
theorem B10249577 : Blo 2023435 10249577 := bstep (se 2 (by rfl) ⟨3843591, by rfl⟩ : syracuseStep 10249577 = 7687183) B7687183
theorem B6833051 : Blo 2023435 6833051 := bstep (se 1 (by rfl) ⟨5124788, by rfl⟩ : syracuseStep 6833051 = 10249577) B10249577
theorem B4555367 : Blo 2023435 4555367 := bstep (se 1 (by rfl) ⟨3416525, by rfl⟩ : syracuseStep 4555367 = 6833051) B6833051
theorem B3036911 : Blo 2023435 3036911 := bstep (se 1 (by rfl) ⟨2277683, by rfl⟩ : syracuseStep 3036911 = 4555367) B4555367
theorem B2024607 : Blo 2023435 2024607 := bstep (se 1 (by rfl) ⟨1518455, by rfl⟩ : syracuseStep 2024607 = 3036911) B3036911
theorem B3036917 : Blo 2023435 3036917 := bbase (se 5 (by rfl) ⟨142355, by rfl⟩ : syracuseStep 3036917 = 284711) (by norm_num)
theorem B2024611 : Blo 2023435 2024611 := bstep (se 1 (by rfl) ⟨1518458, by rfl⟩ : syracuseStep 2024611 = 3036917) B3036917
theorem B8648117 : Blo 2023435 8648117 := bbase (se 5 (by rfl) ⟨405380, by rfl⟩ : syracuseStep 8648117 = 810761) (by norm_num)
theorem B5765411 : Blo 2023435 5765411 := bstep (se 1 (by rfl) ⟨4324058, by rfl⟩ : syracuseStep 5765411 = 8648117) B8648117
theorem B3843607 : Blo 2023435 3843607 := bstep (se 1 (by rfl) ⟨2882705, by rfl⟩ : syracuseStep 3843607 = 5765411) B5765411
theorem B5124809 : Blo 2023435 5124809 := bstep (se 2 (by rfl) ⟨1921803, by rfl⟩ : syracuseStep 5124809 = 3843607) B3843607
theorem B3416539 : Blo 2023435 3416539 := bstep (se 1 (by rfl) ⟨2562404, by rfl⟩ : syracuseStep 3416539 = 5124809) B5124809
theorem B4555385 : Blo 2023435 4555385 := bstep (se 2 (by rfl) ⟨1708269, by rfl⟩ : syracuseStep 4555385 = 3416539) B3416539
theorem B3036923 : Blo 2023435 3036923 := bstep (se 1 (by rfl) ⟨2277692, by rfl⟩ : syracuseStep 3036923 = 4555385) B4555385
theorem B2024615 : Blo 2023435 2024615 := bstep (se 1 (by rfl) ⟨1518461, by rfl⟩ : syracuseStep 2024615 = 3036923) B3036923
theorem B2277697 : Blo 2023435 2277697 := bbase (se 2 (by rfl) ⟨854136, by rfl⟩ : syracuseStep 2277697 = 1708273) (by norm_num)
theorem B3036929 : Blo 2023435 3036929 := bstep (se 2 (by rfl) ⟨1138848, by rfl⟩ : syracuseStep 3036929 = 2277697) B2277697
theorem B2024619 : Blo 2023435 2024619 := bstep (se 1 (by rfl) ⟨1518464, by rfl⟩ : syracuseStep 2024619 = 3036929) B3036929
theorem B5124829 : Blo 2023435 5124829 := bbase (se 3 (by rfl) ⟨960905, by rfl⟩ : syracuseStep 5124829 = 1921811) (by norm_num)
theorem B6833105 : Blo 2023435 6833105 := bstep (se 2 (by rfl) ⟨2562414, by rfl⟩ : syracuseStep 6833105 = 5124829) B5124829
theorem B4555403 : Blo 2023435 4555403 := bstep (se 1 (by rfl) ⟨3416552, by rfl⟩ : syracuseStep 4555403 = 6833105) B6833105
theorem B3036935 : Blo 2023435 3036935 := bstep (se 1 (by rfl) ⟨2277701, by rfl⟩ : syracuseStep 3036935 = 4555403) B4555403
theorem B2024623 : Blo 2023435 2024623 := bstep (se 1 (by rfl) ⟨1518467, by rfl⟩ : syracuseStep 2024623 = 3036935) B3036935
theorem B3036941 : Blo 2023435 3036941 := bbase (se 3 (by rfl) ⟨569426, by rfl⟩ : syracuseStep 3036941 = 1138853) (by norm_num)
theorem B2024627 : Blo 2023435 2024627 := bstep (se 1 (by rfl) ⟨1518470, by rfl⟩ : syracuseStep 2024627 = 3036941) B3036941
theorem B4555421 : Blo 2023435 4555421 := bbase (se 3 (by rfl) ⟨854141, by rfl⟩ : syracuseStep 4555421 = 1708283) (by norm_num)
theorem B3036947 : Blo 2023435 3036947 := bstep (se 1 (by rfl) ⟨2277710, by rfl⟩ : syracuseStep 3036947 = 4555421) B4555421
theorem B2024631 : Blo 2023435 2024631 := bstep (se 1 (by rfl) ⟨1518473, by rfl⟩ : syracuseStep 2024631 = 3036947) B3036947
theorem B3416573 : Blo 2023435 3416573 := bbase (se 3 (by rfl) ⟨640607, by rfl⟩ : syracuseStep 3416573 = 1281215) (by norm_num)
theorem B2277715 : Blo 2023435 2277715 := bstep (se 1 (by rfl) ⟨1708286, by rfl⟩ : syracuseStep 2277715 = 3416573) B3416573
theorem B3036953 : Blo 2023435 3036953 := bstep (se 2 (by rfl) ⟨1138857, by rfl⟩ : syracuseStep 3036953 = 2277715) B2277715
theorem B2024635 : Blo 2023435 2024635 := bstep (se 1 (by rfl) ⟨1518476, by rfl⟩ : syracuseStep 2024635 = 3036953) B3036953
theorem B4324109 : Blo 2023435 4324109 := bbase (se 3 (by rfl) ⟨810770, by rfl⟩ : syracuseStep 4324109 = 1621541) (by norm_num)
theorem B11530957 : Blo 2023435 11530957 := bstep (se 3 (by rfl) ⟨2162054, by rfl⟩ : syracuseStep 11530957 = 4324109) B4324109
theorem B15374609 : Blo 2023435 15374609 := bstep (se 2 (by rfl) ⟨5765478, by rfl⟩ : syracuseStep 15374609 = 11530957) B11530957
theorem B10249739 : Blo 2023435 10249739 := bstep (se 1 (by rfl) ⟨7687304, by rfl⟩ : syracuseStep 10249739 = 15374609) B15374609
theorem B6833159 : Blo 2023435 6833159 := bstep (se 1 (by rfl) ⟨5124869, by rfl⟩ : syracuseStep 6833159 = 10249739) B10249739
theorem B4555439 : Blo 2023435 4555439 := bstep (se 1 (by rfl) ⟨3416579, by rfl⟩ : syracuseStep 4555439 = 6833159) B6833159
theorem B3036959 : Blo 2023435 3036959 := bstep (se 1 (by rfl) ⟨2277719, by rfl⟩ : syracuseStep 3036959 = 4555439) B4555439
theorem B2024639 : Blo 2023435 2024639 := bstep (se 1 (by rfl) ⟨1518479, by rfl⟩ : syracuseStep 2024639 = 3036959) B3036959
theorem B3036965 : Blo 2023435 3036965 := bbase (se 4 (by rfl) ⟨284715, by rfl⟩ : syracuseStep 3036965 = 569431) (by norm_num)
theorem B2024643 : Blo 2023435 2024643 := bstep (se 1 (by rfl) ⟨1518482, by rfl⟩ : syracuseStep 2024643 = 3036965) B3036965
theorem B2562445 : Blo 2023435 2562445 := bbase (se 3 (by rfl) ⟨480458, by rfl⟩ : syracuseStep 2562445 = 960917) (by norm_num)
theorem B3416593 : Blo 2023435 3416593 := bstep (se 2 (by rfl) ⟨1281222, by rfl⟩ : syracuseStep 3416593 = 2562445) B2562445
theorem B4555457 : Blo 2023435 4555457 := bstep (se 2 (by rfl) ⟨1708296, by rfl⟩ : syracuseStep 4555457 = 3416593) B3416593
theorem B3036971 : Blo 2023435 3036971 := bstep (se 1 (by rfl) ⟨2277728, by rfl⟩ : syracuseStep 3036971 = 4555457) B4555457
theorem B2024647 : Blo 2023435 2024647 := bstep (se 1 (by rfl) ⟨1518485, by rfl⟩ : syracuseStep 2024647 = 3036971) B3036971
theorem B2277733 : Blo 2023435 2277733 := bbase (se 4 (by rfl) ⟨213537, by rfl⟩ : syracuseStep 2277733 = 427075) (by norm_num)
theorem B3036977 : Blo 2023435 3036977 := bstep (se 2 (by rfl) ⟨1138866, by rfl⟩ : syracuseStep 3036977 = 2277733) B2277733
theorem B2024651 : Blo 2023435 2024651 := bstep (se 1 (by rfl) ⟨1518488, by rfl⟩ : syracuseStep 2024651 = 3036977) B3036977
theorem B5765525 : Blo 2023435 5765525 := bbase (se 6 (by rfl) ⟨135129, by rfl⟩ : syracuseStep 5765525 = 270259) (by norm_num)
theorem B3843683 : Blo 2023435 3843683 := bstep (se 1 (by rfl) ⟨2882762, by rfl⟩ : syracuseStep 3843683 = 5765525) B5765525
theorem B2562455 : Blo 2023435 2562455 := bstep (se 1 (by rfl) ⟨1921841, by rfl⟩ : syracuseStep 2562455 = 3843683) B3843683
theorem B6833213 : Blo 2023435 6833213 := bstep (se 3 (by rfl) ⟨1281227, by rfl⟩ : syracuseStep 6833213 = 2562455) B2562455
theorem B4555475 : Blo 2023435 4555475 := bstep (se 1 (by rfl) ⟨3416606, by rfl⟩ : syracuseStep 4555475 = 6833213) B6833213
theorem B3036983 : Blo 2023435 3036983 := bstep (se 1 (by rfl) ⟨2277737, by rfl⟩ : syracuseStep 3036983 = 4555475) B4555475
theorem B2024655 : Blo 2023435 2024655 := bstep (se 1 (by rfl) ⟨1518491, by rfl⟩ : syracuseStep 2024655 = 3036983) B3036983
theorem B3036989 : Blo 2023435 3036989 := bbase (se 3 (by rfl) ⟨569435, by rfl⟩ : syracuseStep 3036989 = 1138871) (by norm_num)
theorem B2024659 : Blo 2023435 2024659 := bstep (se 1 (by rfl) ⟨1518494, by rfl⟩ : syracuseStep 2024659 = 3036989) B3036989
theorem B4555493 : Blo 2023435 4555493 := bbase (se 4 (by rfl) ⟨427077, by rfl⟩ : syracuseStep 4555493 = 854155) (by norm_num)
theorem B3036995 : Blo 2023435 3036995 := bstep (se 1 (by rfl) ⟨2277746, by rfl⟩ : syracuseStep 3036995 = 4555493) B4555493
theorem B2024663 : Blo 2023435 2024663 := bstep (se 1 (by rfl) ⟨1518497, by rfl⟩ : syracuseStep 2024663 = 3036995) B3036995
theorem B5124941 : Blo 2023435 5124941 := bbase (se 3 (by rfl) ⟨960926, by rfl⟩ : syracuseStep 5124941 = 1921853) (by norm_num)
theorem B3416627 : Blo 2023435 3416627 := bstep (se 1 (by rfl) ⟨2562470, by rfl⟩ : syracuseStep 3416627 = 5124941) B5124941
theorem B2277751 : Blo 2023435 2277751 := bstep (se 1 (by rfl) ⟨1708313, by rfl⟩ : syracuseStep 2277751 = 3416627) B3416627
theorem B3037001 : Blo 2023435 3037001 := bstep (se 2 (by rfl) ⟨1138875, by rfl⟩ : syracuseStep 3037001 = 2277751) B2277751
theorem B2024667 : Blo 2023435 2024667 := bstep (se 1 (by rfl) ⟨1518500, by rfl⟩ : syracuseStep 2024667 = 3037001) B3037001
theorem B2162089 : Blo 2023435 2162089 := bbase (se 2 (by rfl) ⟨810783, by rfl⟩ : syracuseStep 2162089 = 1621567) (by norm_num)
theorem B2882785 : Blo 2023435 2882785 := bstep (se 2 (by rfl) ⟨1081044, by rfl⟩ : syracuseStep 2882785 = 2162089) B2162089
theorem B3843713 : Blo 2023435 3843713 := bstep (se 2 (by rfl) ⟨1441392, by rfl⟩ : syracuseStep 3843713 = 2882785) B2882785
theorem B10249901 : Blo 2023435 10249901 := bstep (se 3 (by rfl) ⟨1921856, by rfl⟩ : syracuseStep 10249901 = 3843713) B3843713
theorem B6833267 : Blo 2023435 6833267 := bstep (se 1 (by rfl) ⟨5124950, by rfl⟩ : syracuseStep 6833267 = 10249901) B10249901
theorem B4555511 : Blo 2023435 4555511 := bstep (se 1 (by rfl) ⟨3416633, by rfl⟩ : syracuseStep 4555511 = 6833267) B6833267
theorem B3037007 : Blo 2023435 3037007 := bstep (se 1 (by rfl) ⟨2277755, by rfl⟩ : syracuseStep 3037007 = 4555511) B4555511
theorem B2024671 : Blo 2023435 2024671 := bstep (se 1 (by rfl) ⟨1518503, by rfl⟩ : syracuseStep 2024671 = 3037007) B3037007
theorem B3037013 : Blo 2023435 3037013 := bbase (se 9 (by rfl) ⟨8897, by rfl⟩ : syracuseStep 3037013 = 17795) (by norm_num)
theorem B2024675 : Blo 2023435 2024675 := bstep (se 1 (by rfl) ⟨1518506, by rfl⟩ : syracuseStep 2024675 = 3037013) B3037013
theorem B6486293 : Blo 2023435 6486293 := bbase (se 6 (by rfl) ⟨152022, by rfl⟩ : syracuseStep 6486293 = 304045) (by norm_num)
theorem B4324195 : Blo 2023435 4324195 := bstep (se 1 (by rfl) ⟨3243146, by rfl⟩ : syracuseStep 4324195 = 6486293) B6486293
theorem B5765593 : Blo 2023435 5765593 := bstep (se 2 (by rfl) ⟨2162097, by rfl⟩ : syracuseStep 5765593 = 4324195) B4324195
theorem B7687457 : Blo 2023435 7687457 := bstep (se 2 (by rfl) ⟨2882796, by rfl⟩ : syracuseStep 7687457 = 5765593) B5765593
theorem B5124971 : Blo 2023435 5124971 := bstep (se 1 (by rfl) ⟨3843728, by rfl⟩ : syracuseStep 5124971 = 7687457) B7687457
theorem B3416647 : Blo 2023435 3416647 := bstep (se 1 (by rfl) ⟨2562485, by rfl⟩ : syracuseStep 3416647 = 5124971) B5124971
theorem B4555529 : Blo 2023435 4555529 := bstep (se 2 (by rfl) ⟨1708323, by rfl⟩ : syracuseStep 4555529 = 3416647) B3416647
theorem B3037019 : Blo 2023435 3037019 := bstep (se 1 (by rfl) ⟨2277764, by rfl⟩ : syracuseStep 3037019 = 4555529) B4555529
theorem B2024679 : Blo 2023435 2024679 := bstep (se 1 (by rfl) ⟨1518509, by rfl⟩ : syracuseStep 2024679 = 3037019) B3037019
theorem B2277769 : Blo 2023435 2277769 := bbase (se 2 (by rfl) ⟨854163, by rfl⟩ : syracuseStep 2277769 = 1708327) (by norm_num)
theorem B3037025 : Blo 2023435 3037025 := bstep (se 2 (by rfl) ⟨1138884, by rfl⟩ : syracuseStep 3037025 = 2277769) B2277769
theorem B2024683 : Blo 2023435 2024683 := bstep (se 1 (by rfl) ⟨1518512, by rfl⟩ : syracuseStep 2024683 = 3037025) B3037025
theorem B3698333 : Blo 2023435 3698333 := bbase (se 3 (by rfl) ⟨693437, by rfl⟩ : syracuseStep 3698333 = 1386875) (by norm_num)
theorem B2465555 : Blo 2023435 2465555 := bstep (se 1 (by rfl) ⟨1849166, by rfl⟩ : syracuseStep 2465555 = 3698333) B3698333
theorem B6574813 : Blo 2023435 6574813 := bstep (se 3 (by rfl) ⟨1232777, by rfl⟩ : syracuseStep 6574813 = 2465555) B2465555
theorem B140262677 : Blo 2023435 140262677 := bstep (se 6 (by rfl) ⟨3287406, by rfl⟩ : syracuseStep 140262677 = 6574813) B6574813
theorem B93508451 : Blo 2023435 93508451 := bstep (se 1 (by rfl) ⟨70131338, by rfl⟩ : syracuseStep 93508451 = 140262677) B140262677
theorem B62338967 : Blo 2023435 62338967 := bstep (se 1 (by rfl) ⟨46754225, by rfl⟩ : syracuseStep 62338967 = 93508451) B93508451
theorem B41559311 : Blo 2023435 41559311 := bstep (se 1 (by rfl) ⟨31169483, by rfl⟩ : syracuseStep 41559311 = 62338967) B62338967
theorem B27706207 : Blo 2023435 27706207 := bstep (se 1 (by rfl) ⟨20779655, by rfl⟩ : syracuseStep 27706207 = 41559311) B41559311
theorem B36941609 : Blo 2023435 36941609 := bstep (se 2 (by rfl) ⟨13853103, by rfl⟩ : syracuseStep 36941609 = 27706207) B27706207
theorem B24627739 : Blo 2023435 24627739 := bstep (se 1 (by rfl) ⟨18470804, by rfl⟩ : syracuseStep 24627739 = 36941609) B36941609
theorem B32836985 : Blo 2023435 32836985 := bstep (se 2 (by rfl) ⟨12313869, by rfl⟩ : syracuseStep 32836985 = 24627739) B24627739
theorem B21891323 : Blo 2023435 21891323 := bstep (se 1 (by rfl) ⟨16418492, by rfl⟩ : syracuseStep 21891323 = 32836985) B32836985
theorem B58376861 : Blo 2023435 58376861 := bstep (se 3 (by rfl) ⟨10945661, by rfl⟩ : syracuseStep 58376861 = 21891323) B21891323
theorem B38917907 : Blo 2023435 38917907 := bstep (se 1 (by rfl) ⟨29188430, by rfl⟩ : syracuseStep 38917907 = 58376861) B58376861
theorem B25945271 : Blo 2023435 25945271 := bstep (se 1 (by rfl) ⟨19458953, by rfl⟩ : syracuseStep 25945271 = 38917907) B38917907
theorem B17296847 : Blo 2023435 17296847 := bstep (se 1 (by rfl) ⟨12972635, by rfl⟩ : syracuseStep 17296847 = 25945271) B25945271
theorem B11531231 : Blo 2023435 11531231 := bstep (se 1 (by rfl) ⟨8648423, by rfl⟩ : syracuseStep 11531231 = 17296847) B17296847
theorem B7687487 : Blo 2023435 7687487 := bstep (se 1 (by rfl) ⟨5765615, by rfl⟩ : syracuseStep 7687487 = 11531231) B11531231
theorem B5124991 : Blo 2023435 5124991 := bstep (se 1 (by rfl) ⟨3843743, by rfl⟩ : syracuseStep 5124991 = 7687487) B7687487
theorem B6833321 : Blo 2023435 6833321 := bstep (se 2 (by rfl) ⟨2562495, by rfl⟩ : syracuseStep 6833321 = 5124991) B5124991
theorem B4555547 : Blo 2023435 4555547 := bstep (se 1 (by rfl) ⟨3416660, by rfl⟩ : syracuseStep 4555547 = 6833321) B6833321
theorem B3037031 : Blo 2023435 3037031 := bstep (se 1 (by rfl) ⟨2277773, by rfl⟩ : syracuseStep 3037031 = 4555547) B4555547
theorem B2024687 : Blo 2023435 2024687 := bstep (se 1 (by rfl) ⟨1518515, by rfl⟩ : syracuseStep 2024687 = 3037031) B3037031
theorem B3037037 : Blo 2023435 3037037 := bbase (se 3 (by rfl) ⟨569444, by rfl⟩ : syracuseStep 3037037 = 1138889) (by norm_num)
theorem B2024691 : Blo 2023435 2024691 := bstep (se 1 (by rfl) ⟨1518518, by rfl⟩ : syracuseStep 2024691 = 3037037) B3037037
theorem B4555565 : Blo 2023435 4555565 := bbase (se 3 (by rfl) ⟨854168, by rfl⟩ : syracuseStep 4555565 = 1708337) (by norm_num)
theorem B3037043 : Blo 2023435 3037043 := bstep (se 1 (by rfl) ⟨2277782, by rfl⟩ : syracuseStep 3037043 = 4555565) B4555565
theorem B2024695 : Blo 2023435 2024695 := bstep (se 1 (by rfl) ⟨1518521, by rfl⟩ : syracuseStep 2024695 = 3037043) B3037043
theorem B2052325 : Blo 2023435 2052325 := bbase (se 4 (by rfl) ⟨192405, by rfl⟩ : syracuseStep 2052325 = 384811) (by norm_num)
theorem B2736433 : Blo 2023435 2736433 := bstep (se 2 (by rfl) ⟨1026162, by rfl⟩ : syracuseStep 2736433 = 2052325) B2052325
theorem B3648577 : Blo 2023435 3648577 := bstep (se 2 (by rfl) ⟨1368216, by rfl⟩ : syracuseStep 3648577 = 2736433) B2736433
theorem B4864769 : Blo 2023435 4864769 := bstep (se 2 (by rfl) ⟨1824288, by rfl⟩ : syracuseStep 4864769 = 3648577) B3648577
theorem B3243179 : Blo 2023435 3243179 := bstep (se 1 (by rfl) ⟨2432384, by rfl⟩ : syracuseStep 3243179 = 4864769) B4864769
theorem B8648477 : Blo 2023435 8648477 := bstep (se 3 (by rfl) ⟨1621589, by rfl⟩ : syracuseStep 8648477 = 3243179) B3243179
theorem B5765651 : Blo 2023435 5765651 := bstep (se 1 (by rfl) ⟨4324238, by rfl⟩ : syracuseStep 5765651 = 8648477) B8648477
theorem B3843767 : Blo 2023435 3843767 := bstep (se 1 (by rfl) ⟨2882825, by rfl⟩ : syracuseStep 3843767 = 5765651) B5765651
theorem B2562511 : Blo 2023435 2562511 := bstep (se 1 (by rfl) ⟨1921883, by rfl⟩ : syracuseStep 2562511 = 3843767) B3843767
theorem B3416681 : Blo 2023435 3416681 := bstep (se 2 (by rfl) ⟨1281255, by rfl⟩ : syracuseStep 3416681 = 2562511) B2562511
theorem B2277787 : Blo 2023435 2277787 := bstep (se 1 (by rfl) ⟨1708340, by rfl⟩ : syracuseStep 2277787 = 3416681) B3416681
theorem B3037049 : Blo 2023435 3037049 := bstep (se 2 (by rfl) ⟨1138893, by rfl⟩ : syracuseStep 3037049 = 2277787) B2277787
theorem B2024699 : Blo 2023435 2024699 := bstep (se 1 (by rfl) ⟨1518524, by rfl⟩ : syracuseStep 2024699 = 3037049) B3037049
theorem B2736437 : Blo 2023435 2736437 := bbase (se 5 (by rfl) ⟨128270, by rfl⟩ : syracuseStep 2736437 = 256541) (by norm_num)
theorem B7297165 : Blo 2023435 7297165 := bstep (se 3 (by rfl) ⟨1368218, by rfl⟩ : syracuseStep 7297165 = 2736437) B2736437
theorem B9729553 : Blo 2023435 9729553 := bstep (se 2 (by rfl) ⟨3648582, by rfl⟩ : syracuseStep 9729553 = 7297165) B7297165
theorem B12972737 : Blo 2023435 12972737 := bstep (se 2 (by rfl) ⟨4864776, by rfl⟩ : syracuseStep 12972737 = 9729553) B9729553
theorem B34593965 : Blo 2023435 34593965 := bstep (se 3 (by rfl) ⟨6486368, by rfl⟩ : syracuseStep 34593965 = 12972737) B12972737
theorem B23062643 : Blo 2023435 23062643 := bstep (se 1 (by rfl) ⟨17296982, by rfl⟩ : syracuseStep 23062643 = 34593965) B34593965
theorem B15375095 : Blo 2023435 15375095 := bstep (se 1 (by rfl) ⟨11531321, by rfl⟩ : syracuseStep 15375095 = 23062643) B23062643
theorem B10250063 : Blo 2023435 10250063 := bstep (se 1 (by rfl) ⟨7687547, by rfl⟩ : syracuseStep 10250063 = 15375095) B15375095
theorem B6833375 : Blo 2023435 6833375 := bstep (se 1 (by rfl) ⟨5125031, by rfl⟩ : syracuseStep 6833375 = 10250063) B10250063
theorem B4555583 : Blo 2023435 4555583 := bstep (se 1 (by rfl) ⟨3416687, by rfl⟩ : syracuseStep 4555583 = 6833375) B6833375
theorem B3037055 : Blo 2023435 3037055 := bstep (se 1 (by rfl) ⟨2277791, by rfl⟩ : syracuseStep 3037055 = 4555583) B4555583
theorem B2024703 : Blo 2023435 2024703 := bstep (se 1 (by rfl) ⟨1518527, by rfl⟩ : syracuseStep 2024703 = 3037055) B3037055
theorem B3037061 : Blo 2023435 3037061 := bbase (se 4 (by rfl) ⟨284724, by rfl⟩ : syracuseStep 3037061 = 569449) (by norm_num)
theorem B2024707 : Blo 2023435 2024707 := bstep (se 1 (by rfl) ⟨1518530, by rfl⟩ : syracuseStep 2024707 = 3037061) B3037061
theorem B3416701 : Blo 2023435 3416701 := bbase (se 3 (by rfl) ⟨640631, by rfl⟩ : syracuseStep 3416701 = 1281263) (by norm_num)
theorem B4555601 : Blo 2023435 4555601 := bstep (se 2 (by rfl) ⟨1708350, by rfl⟩ : syracuseStep 4555601 = 3416701) B3416701
theorem B3037067 : Blo 2023435 3037067 := bstep (se 1 (by rfl) ⟨2277800, by rfl⟩ : syracuseStep 3037067 = 4555601) B4555601
theorem B2024711 : Blo 2023435 2024711 := bstep (se 1 (by rfl) ⟨1518533, by rfl⟩ : syracuseStep 2024711 = 3037067) B3037067
theorem B2277805 : Blo 2023435 2277805 := bbase (se 3 (by rfl) ⟨427088, by rfl⟩ : syracuseStep 2277805 = 854177) (by norm_num)
theorem B3037073 : Blo 2023435 3037073 := bstep (se 2 (by rfl) ⟨1138902, by rfl⟩ : syracuseStep 3037073 = 2277805) B2277805
theorem B2024715 : Blo 2023435 2024715 := bstep (se 1 (by rfl) ⟨1518536, by rfl⟩ : syracuseStep 2024715 = 3037073) B3037073
theorem B6833429 : Blo 2023435 6833429 := bbase (se 6 (by rfl) ⟨160158, by rfl⟩ : syracuseStep 6833429 = 320317) (by norm_num)
theorem B4555619 : Blo 2023435 4555619 := bstep (se 1 (by rfl) ⟨3416714, by rfl⟩ : syracuseStep 4555619 = 6833429) B6833429
theorem B3037079 : Blo 2023435 3037079 := bstep (se 1 (by rfl) ⟨2277809, by rfl⟩ : syracuseStep 3037079 = 4555619) B4555619
theorem B2024719 : Blo 2023435 2024719 := bstep (se 1 (by rfl) ⟨1518539, by rfl⟩ : syracuseStep 2024719 = 3037079) B3037079
theorem B3037085 : Blo 2023435 3037085 := bbase (se 3 (by rfl) ⟨569453, by rfl⟩ : syracuseStep 3037085 = 1138907) (by norm_num)
theorem B2024723 : Blo 2023435 2024723 := bstep (se 1 (by rfl) ⟨1518542, by rfl⟩ : syracuseStep 2024723 = 3037085) B3037085
theorem B4555637 : Blo 2023435 4555637 := bbase (se 5 (by rfl) ⟨213545, by rfl⟩ : syracuseStep 4555637 = 427091) (by norm_num)
theorem B3037091 : Blo 2023435 3037091 := bstep (se 1 (by rfl) ⟨2277818, by rfl⟩ : syracuseStep 3037091 = 4555637) B4555637
theorem B2024727 : Blo 2023435 2024727 := bstep (se 1 (by rfl) ⟨1518545, by rfl⟩ : syracuseStep 2024727 = 3037091) B3037091
theorem B5195029 : Blo 2023435 5195029 := bbase (se 6 (by rfl) ⟨121758, by rfl⟩ : syracuseStep 5195029 = 243517) (by norm_num)
theorem B6926705 : Blo 2023435 6926705 := bstep (se 2 (by rfl) ⟨2597514, by rfl⟩ : syracuseStep 6926705 = 5195029) B5195029
theorem B4617803 : Blo 2023435 4617803 := bstep (se 1 (by rfl) ⟨3463352, by rfl⟩ : syracuseStep 4617803 = 6926705) B6926705
theorem B3078535 : Blo 2023435 3078535 := bstep (se 1 (by rfl) ⟨2308901, by rfl⟩ : syracuseStep 3078535 = 4617803) B4617803
theorem B4104713 : Blo 2023435 4104713 := bstep (se 2 (by rfl) ⟨1539267, by rfl⟩ : syracuseStep 4104713 = 3078535) B3078535
theorem B10945901 : Blo 2023435 10945901 := bstep (se 3 (by rfl) ⟨2052356, by rfl⟩ : syracuseStep 10945901 = 4104713) B4104713
theorem B29189069 : Blo 2023435 29189069 := bstep (se 3 (by rfl) ⟨5472950, by rfl⟩ : syracuseStep 29189069 = 10945901) B10945901
theorem B19459379 : Blo 2023435 19459379 := bstep (se 1 (by rfl) ⟨14594534, by rfl⟩ : syracuseStep 19459379 = 29189069) B29189069
theorem B12972919 : Blo 2023435 12972919 := bstep (se 1 (by rfl) ⟨9729689, by rfl⟩ : syracuseStep 12972919 = 19459379) B19459379
theorem B17297225 : Blo 2023435 17297225 := bstep (se 2 (by rfl) ⟨6486459, by rfl⟩ : syracuseStep 17297225 = 12972919) B12972919
theorem B11531483 : Blo 2023435 11531483 := bstep (se 1 (by rfl) ⟨8648612, by rfl⟩ : syracuseStep 11531483 = 17297225) B17297225
theorem B7687655 : Blo 2023435 7687655 := bstep (se 1 (by rfl) ⟨5765741, by rfl⟩ : syracuseStep 7687655 = 11531483) B11531483
theorem B5125103 : Blo 2023435 5125103 := bstep (se 1 (by rfl) ⟨3843827, by rfl⟩ : syracuseStep 5125103 = 7687655) B7687655
theorem B3416735 : Blo 2023435 3416735 := bstep (se 1 (by rfl) ⟨2562551, by rfl⟩ : syracuseStep 3416735 = 5125103) B5125103
theorem B2277823 : Blo 2023435 2277823 := bstep (se 1 (by rfl) ⟨1708367, by rfl⟩ : syracuseStep 2277823 = 3416735) B3416735
theorem B3037097 : Blo 2023435 3037097 := bstep (se 2 (by rfl) ⟨1138911, by rfl⟩ : syracuseStep 3037097 = 2277823) B2277823
theorem B2024731 : Blo 2023435 2024731 := bstep (se 1 (by rfl) ⟨1518548, by rfl⟩ : syracuseStep 2024731 = 3037097) B3037097
theorem B7687669 : Blo 2023435 7687669 := bbase (se 5 (by rfl) ⟨360359, by rfl⟩ : syracuseStep 7687669 = 720719) (by norm_num)
theorem B10250225 : Blo 2023435 10250225 := bstep (se 2 (by rfl) ⟨3843834, by rfl⟩ : syracuseStep 10250225 = 7687669) B7687669
theorem B6833483 : Blo 2023435 6833483 := bstep (se 1 (by rfl) ⟨5125112, by rfl⟩ : syracuseStep 6833483 = 10250225) B10250225
theorem B4555655 : Blo 2023435 4555655 := bstep (se 1 (by rfl) ⟨3416741, by rfl⟩ : syracuseStep 4555655 = 6833483) B6833483
theorem B3037103 : Blo 2023435 3037103 := bstep (se 1 (by rfl) ⟨2277827, by rfl⟩ : syracuseStep 3037103 = 4555655) B4555655
theorem B2024735 : Blo 2023435 2024735 := bstep (se 1 (by rfl) ⟨1518551, by rfl⟩ : syracuseStep 2024735 = 3037103) B3037103
theorem B3037109 : Blo 2023435 3037109 := bbase (se 5 (by rfl) ⟨142364, by rfl⟩ : syracuseStep 3037109 = 284729) (by norm_num)
theorem B2024739 : Blo 2023435 2024739 := bstep (se 1 (by rfl) ⟨1518554, by rfl⟩ : syracuseStep 2024739 = 3037109) B3037109
theorem B5125133 : Blo 2023435 5125133 := bbase (se 3 (by rfl) ⟨960962, by rfl⟩ : syracuseStep 5125133 = 1921925) (by norm_num)
theorem B3416755 : Blo 2023435 3416755 := bstep (se 1 (by rfl) ⟨2562566, by rfl⟩ : syracuseStep 3416755 = 5125133) B5125133
theorem B4555673 : Blo 2023435 4555673 := bstep (se 2 (by rfl) ⟨1708377, by rfl⟩ : syracuseStep 4555673 = 3416755) B3416755
theorem B3037115 : Blo 2023435 3037115 := bstep (se 1 (by rfl) ⟨2277836, by rfl⟩ : syracuseStep 3037115 = 4555673) B4555673
theorem B2024743 : Blo 2023435 2024743 := bstep (se 1 (by rfl) ⟨1518557, by rfl⟩ : syracuseStep 2024743 = 3037115) B3037115
theorem B2277841 : Blo 2023435 2277841 := bbase (se 2 (by rfl) ⟨854190, by rfl⟩ : syracuseStep 2277841 = 1708381) (by norm_num)
theorem B3037121 : Blo 2023435 3037121 := bstep (se 2 (by rfl) ⟨1138920, by rfl⟩ : syracuseStep 3037121 = 2277841) B2277841
theorem B2024747 : Blo 2023435 2024747 := bstep (se 1 (by rfl) ⟨1518560, by rfl⟩ : syracuseStep 2024747 = 3037121) B3037121
theorem B4324349 : Blo 2023435 4324349 := bbase (se 3 (by rfl) ⟨810815, by rfl⟩ : syracuseStep 4324349 = 1621631) (by norm_num)
theorem B2882899 : Blo 2023435 2882899 := bstep (se 1 (by rfl) ⟨2162174, by rfl⟩ : syracuseStep 2882899 = 4324349) B4324349
theorem B3843865 : Blo 2023435 3843865 := bstep (se 2 (by rfl) ⟨1441449, by rfl⟩ : syracuseStep 3843865 = 2882899) B2882899
theorem B5125153 : Blo 2023435 5125153 := bstep (se 2 (by rfl) ⟨1921932, by rfl⟩ : syracuseStep 5125153 = 3843865) B3843865
theorem B6833537 : Blo 2023435 6833537 := bstep (se 2 (by rfl) ⟨2562576, by rfl⟩ : syracuseStep 6833537 = 5125153) B5125153
theorem B4555691 : Blo 2023435 4555691 := bstep (se 1 (by rfl) ⟨3416768, by rfl⟩ : syracuseStep 4555691 = 6833537) B6833537
theorem B3037127 : Blo 2023435 3037127 := bstep (se 1 (by rfl) ⟨2277845, by rfl⟩ : syracuseStep 3037127 = 4555691) B4555691
theorem B2024751 : Blo 2023435 2024751 := bstep (se 1 (by rfl) ⟨1518563, by rfl⟩ : syracuseStep 2024751 = 3037127) B3037127
theorem B3037133 : Blo 2023435 3037133 := bbase (se 3 (by rfl) ⟨569462, by rfl⟩ : syracuseStep 3037133 = 1138925) (by norm_num)
theorem B2024755 : Blo 2023435 2024755 := bstep (se 1 (by rfl) ⟨1518566, by rfl⟩ : syracuseStep 2024755 = 3037133) B3037133
theorem B4555709 : Blo 2023435 4555709 := bbase (se 3 (by rfl) ⟨854195, by rfl⟩ : syracuseStep 4555709 = 1708391) (by norm_num)
theorem B3037139 : Blo 2023435 3037139 := bstep (se 1 (by rfl) ⟨2277854, by rfl⟩ : syracuseStep 3037139 = 4555709) B4555709
theorem B2024759 : Blo 2023435 2024759 := bstep (se 1 (by rfl) ⟨1518569, by rfl⟩ : syracuseStep 2024759 = 3037139) B3037139
theorem B3416789 : Blo 2023435 3416789 := bbase (se 7 (by rfl) ⟨40040, by rfl⟩ : syracuseStep 3416789 = 80081) (by norm_num)
theorem B2277859 : Blo 2023435 2277859 := bstep (se 1 (by rfl) ⟨1708394, by rfl⟩ : syracuseStep 2277859 = 3416789) B3416789
theorem B3037145 : Blo 2023435 3037145 := bstep (se 2 (by rfl) ⟨1138929, by rfl⟩ : syracuseStep 3037145 = 2277859) B2277859
theorem B2024763 : Blo 2023435 2024763 := bstep (se 1 (by rfl) ⟨1518572, by rfl⟩ : syracuseStep 2024763 = 3037145) B3037145
theorem B7297397 : Blo 2023435 7297397 := bbase (se 5 (by rfl) ⟨342065, by rfl⟩ : syracuseStep 7297397 = 684131) (by norm_num)
theorem B4864931 : Blo 2023435 4864931 := bstep (se 1 (by rfl) ⟨3648698, by rfl⟩ : syracuseStep 4864931 = 7297397) B7297397
theorem B3243287 : Blo 2023435 3243287 := bstep (se 1 (by rfl) ⟨2432465, by rfl⟩ : syracuseStep 3243287 = 4864931) B4864931
theorem B8648765 : Blo 2023435 8648765 := bstep (se 3 (by rfl) ⟨1621643, by rfl⟩ : syracuseStep 8648765 = 3243287) B3243287
theorem B5765843 : Blo 2023435 5765843 := bstep (se 1 (by rfl) ⟨4324382, by rfl⟩ : syracuseStep 5765843 = 8648765) B8648765
theorem B15375581 : Blo 2023435 15375581 := bstep (se 3 (by rfl) ⟨2882921, by rfl⟩ : syracuseStep 15375581 = 5765843) B5765843
theorem B10250387 : Blo 2023435 10250387 := bstep (se 1 (by rfl) ⟨7687790, by rfl⟩ : syracuseStep 10250387 = 15375581) B15375581
theorem B6833591 : Blo 2023435 6833591 := bstep (se 1 (by rfl) ⟨5125193, by rfl⟩ : syracuseStep 6833591 = 10250387) B10250387
theorem B4555727 : Blo 2023435 4555727 := bstep (se 1 (by rfl) ⟨3416795, by rfl⟩ : syracuseStep 4555727 = 6833591) B6833591
theorem B3037151 : Blo 2023435 3037151 := bstep (se 1 (by rfl) ⟨2277863, by rfl⟩ : syracuseStep 3037151 = 4555727) B4555727
theorem B2024767 : Blo 2023435 2024767 := bstep (se 1 (by rfl) ⟨1518575, by rfl⟩ : syracuseStep 2024767 = 3037151) B3037151
theorem B3037157 : Blo 2023435 3037157 := bbase (se 4 (by rfl) ⟨284733, by rfl⟩ : syracuseStep 3037157 = 569467) (by norm_num)
theorem B2024771 : Blo 2023435 2024771 := bstep (se 1 (by rfl) ⟨1518578, by rfl⟩ : syracuseStep 2024771 = 3037157) B3037157
theorem B6157205 : Blo 2023435 6157205 := bbase (se 6 (by rfl) ⟨144309, by rfl⟩ : syracuseStep 6157205 = 288619) (by norm_num)
theorem B4104803 : Blo 2023435 4104803 := bstep (se 1 (by rfl) ⟨3078602, by rfl⟩ : syracuseStep 4104803 = 6157205) B6157205
theorem B10946141 : Blo 2023435 10946141 := bstep (se 3 (by rfl) ⟨2052401, by rfl⟩ : syracuseStep 10946141 = 4104803) B4104803
theorem B7297427 : Blo 2023435 7297427 := bstep (se 1 (by rfl) ⟨5473070, by rfl⟩ : syracuseStep 7297427 = 10946141) B10946141
theorem B4864951 : Blo 2023435 4864951 := bstep (se 1 (by rfl) ⟨3648713, by rfl⟩ : syracuseStep 4864951 = 7297427) B7297427
theorem B6486601 : Blo 2023435 6486601 := bstep (se 2 (by rfl) ⟨2432475, by rfl⟩ : syracuseStep 6486601 = 4864951) B4864951
theorem B8648801 : Blo 2023435 8648801 := bstep (se 2 (by rfl) ⟨3243300, by rfl⟩ : syracuseStep 8648801 = 6486601) B6486601
theorem B5765867 : Blo 2023435 5765867 := bstep (se 1 (by rfl) ⟨4324400, by rfl⟩ : syracuseStep 5765867 = 8648801) B8648801
theorem B3843911 : Blo 2023435 3843911 := bstep (se 1 (by rfl) ⟨2882933, by rfl⟩ : syracuseStep 3843911 = 5765867) B5765867
theorem B2562607 : Blo 2023435 2562607 := bstep (se 1 (by rfl) ⟨1921955, by rfl⟩ : syracuseStep 2562607 = 3843911) B3843911
theorem B3416809 : Blo 2023435 3416809 := bstep (se 2 (by rfl) ⟨1281303, by rfl⟩ : syracuseStep 3416809 = 2562607) B2562607
theorem B4555745 : Blo 2023435 4555745 := bstep (se 2 (by rfl) ⟨1708404, by rfl⟩ : syracuseStep 4555745 = 3416809) B3416809
theorem B3037163 : Blo 2023435 3037163 := bstep (se 1 (by rfl) ⟨2277872, by rfl⟩ : syracuseStep 3037163 = 4555745) B4555745
theorem B2024775 : Blo 2023435 2024775 := bstep (se 1 (by rfl) ⟨1518581, by rfl⟩ : syracuseStep 2024775 = 3037163) B3037163
theorem B2277877 : Blo 2023435 2277877 := bbase (se 5 (by rfl) ⟨106775, by rfl⟩ : syracuseStep 2277877 = 213551) (by norm_num)
theorem B3037169 : Blo 2023435 3037169 := bstep (se 2 (by rfl) ⟨1138938, by rfl⟩ : syracuseStep 3037169 = 2277877) B2277877
theorem B2024779 : Blo 2023435 2024779 := bstep (se 1 (by rfl) ⟨1518584, by rfl⟩ : syracuseStep 2024779 = 3037169) B3037169
theorem B2562617 : Blo 2023435 2562617 := bbase (se 2 (by rfl) ⟨960981, by rfl⟩ : syracuseStep 2562617 = 1921963) (by norm_num)
theorem B6833645 : Blo 2023435 6833645 := bstep (se 3 (by rfl) ⟨1281308, by rfl⟩ : syracuseStep 6833645 = 2562617) B2562617
theorem B4555763 : Blo 2023435 4555763 := bstep (se 1 (by rfl) ⟨3416822, by rfl⟩ : syracuseStep 4555763 = 6833645) B6833645
theorem B3037175 : Blo 2023435 3037175 := bstep (se 1 (by rfl) ⟨2277881, by rfl⟩ : syracuseStep 3037175 = 4555763) B4555763
theorem B2024783 : Blo 2023435 2024783 := bstep (se 1 (by rfl) ⟨1518587, by rfl⟩ : syracuseStep 2024783 = 3037175) B3037175
theorem B3037181 : Blo 2023435 3037181 := bbase (se 3 (by rfl) ⟨569471, by rfl⟩ : syracuseStep 3037181 = 1138943) (by norm_num)
theorem B2024787 : Blo 2023435 2024787 := bstep (se 1 (by rfl) ⟨1518590, by rfl⟩ : syracuseStep 2024787 = 3037181) B3037181
theorem B4555781 : Blo 2023435 4555781 := bbase (se 4 (by rfl) ⟨427104, by rfl⟩ : syracuseStep 4555781 = 854209) (by norm_num)
theorem B3037187 : Blo 2023435 3037187 := bstep (se 1 (by rfl) ⟨2277890, by rfl⟩ : syracuseStep 3037187 = 4555781) B4555781
theorem B2024791 : Blo 2023435 2024791 := bstep (se 1 (by rfl) ⟨1518593, by rfl⟩ : syracuseStep 2024791 = 3037187) B3037187
theorem B3843949 : Blo 2023435 3843949 := bbase (se 3 (by rfl) ⟨720740, by rfl⟩ : syracuseStep 3843949 = 1441481) (by norm_num)
theorem B5125265 : Blo 2023435 5125265 := bstep (se 2 (by rfl) ⟨1921974, by rfl⟩ : syracuseStep 5125265 = 3843949) B3843949
theorem B3416843 : Blo 2023435 3416843 := bstep (se 1 (by rfl) ⟨2562632, by rfl⟩ : syracuseStep 3416843 = 5125265) B5125265
theorem B2277895 : Blo 2023435 2277895 := bstep (se 1 (by rfl) ⟨1708421, by rfl⟩ : syracuseStep 2277895 = 3416843) B3416843
theorem B3037193 : Blo 2023435 3037193 := bstep (se 2 (by rfl) ⟨1138947, by rfl⟩ : syracuseStep 3037193 = 2277895) B2277895
theorem B2024795 : Blo 2023435 2024795 := bstep (se 1 (by rfl) ⟨1518596, by rfl⟩ : syracuseStep 2024795 = 3037193) B3037193
theorem B10250549 : Blo 2023435 10250549 := bbase (se 5 (by rfl) ⟨480494, by rfl⟩ : syracuseStep 10250549 = 960989) (by norm_num)
theorem B6833699 : Blo 2023435 6833699 := bstep (se 1 (by rfl) ⟨5125274, by rfl⟩ : syracuseStep 6833699 = 10250549) B10250549
theorem B4555799 : Blo 2023435 4555799 := bstep (se 1 (by rfl) ⟨3416849, by rfl⟩ : syracuseStep 4555799 = 6833699) B6833699
theorem B3037199 : Blo 2023435 3037199 := bstep (se 1 (by rfl) ⟨2277899, by rfl⟩ : syracuseStep 3037199 = 4555799) B4555799
theorem B2024799 : Blo 2023435 2024799 := bstep (se 1 (by rfl) ⟨1518599, by rfl⟩ : syracuseStep 2024799 = 3037199) B3037199
theorem B3037205 : Blo 2023435 3037205 := bbase (se 6 (by rfl) ⟨71184, by rfl⟩ : syracuseStep 3037205 = 142369) (by norm_num)
theorem B2024803 : Blo 2023435 2024803 := bstep (se 1 (by rfl) ⟨1518602, by rfl⟩ : syracuseStep 2024803 = 3037205) B3037205
theorem B7297541 : Blo 2023435 7297541 := bbase (se 4 (by rfl) ⟨684144, by rfl⟩ : syracuseStep 7297541 = 1368289) (by norm_num)
theorem B4865027 : Blo 2023435 4865027 := bstep (se 1 (by rfl) ⟨3648770, by rfl⟩ : syracuseStep 4865027 = 7297541) B7297541
theorem B12973405 : Blo 2023435 12973405 := bstep (se 3 (by rfl) ⟨2432513, by rfl⟩ : syracuseStep 12973405 = 4865027) B4865027
theorem B17297873 : Blo 2023435 17297873 := bstep (se 2 (by rfl) ⟨6486702, by rfl⟩ : syracuseStep 17297873 = 12973405) B12973405
theorem B11531915 : Blo 2023435 11531915 := bstep (se 1 (by rfl) ⟨8648936, by rfl⟩ : syracuseStep 11531915 = 17297873) B17297873
theorem B7687943 : Blo 2023435 7687943 := bstep (se 1 (by rfl) ⟨5765957, by rfl⟩ : syracuseStep 7687943 = 11531915) B11531915
theorem B5125295 : Blo 2023435 5125295 := bstep (se 1 (by rfl) ⟨3843971, by rfl⟩ : syracuseStep 5125295 = 7687943) B7687943
theorem B3416863 : Blo 2023435 3416863 := bstep (se 1 (by rfl) ⟨2562647, by rfl⟩ : syracuseStep 3416863 = 5125295) B5125295
theorem B4555817 : Blo 2023435 4555817 := bstep (se 2 (by rfl) ⟨1708431, by rfl⟩ : syracuseStep 4555817 = 3416863) B3416863
theorem B3037211 : Blo 2023435 3037211 := bstep (se 1 (by rfl) ⟨2277908, by rfl⟩ : syracuseStep 3037211 = 4555817) B4555817
theorem B2024807 : Blo 2023435 2024807 := bstep (se 1 (by rfl) ⟨1518605, by rfl⟩ : syracuseStep 2024807 = 3037211) B3037211
theorem B2277913 : Blo 2023435 2277913 := bbase (se 2 (by rfl) ⟨854217, by rfl⟩ : syracuseStep 2277913 = 1708435) (by norm_num)
theorem B3037217 : Blo 2023435 3037217 := bstep (se 2 (by rfl) ⟨1138956, by rfl⟩ : syracuseStep 3037217 = 2277913) B2277913
theorem B2024811 : Blo 2023435 2024811 := bstep (se 1 (by rfl) ⟨1518608, by rfl⟩ : syracuseStep 2024811 = 3037217) B3037217
theorem B7687973 : Blo 2023435 7687973 := bbase (se 4 (by rfl) ⟨720747, by rfl⟩ : syracuseStep 7687973 = 1441495) (by norm_num)
theorem B5125315 : Blo 2023435 5125315 := bstep (se 1 (by rfl) ⟨3843986, by rfl⟩ : syracuseStep 5125315 = 7687973) B7687973
theorem B6833753 : Blo 2023435 6833753 := bstep (se 2 (by rfl) ⟨2562657, by rfl⟩ : syracuseStep 6833753 = 5125315) B5125315
theorem B4555835 : Blo 2023435 4555835 := bstep (se 1 (by rfl) ⟨3416876, by rfl⟩ : syracuseStep 4555835 = 6833753) B6833753
theorem B3037223 : Blo 2023435 3037223 := bstep (se 1 (by rfl) ⟨2277917, by rfl⟩ : syracuseStep 3037223 = 4555835) B4555835
theorem B2024815 : Blo 2023435 2024815 := bstep (se 1 (by rfl) ⟨1518611, by rfl⟩ : syracuseStep 2024815 = 3037223) B3037223
theorem B3037229 : Blo 2023435 3037229 := bbase (se 3 (by rfl) ⟨569480, by rfl⟩ : syracuseStep 3037229 = 1138961) (by norm_num)
theorem B2024819 : Blo 2023435 2024819 := bstep (se 1 (by rfl) ⟨1518614, by rfl⟩ : syracuseStep 2024819 = 3037229) B3037229
theorem B4555853 : Blo 2023435 4555853 := bbase (se 3 (by rfl) ⟨854222, by rfl⟩ : syracuseStep 4555853 = 1708445) (by norm_num)
theorem B3037235 : Blo 2023435 3037235 := bstep (se 1 (by rfl) ⟨2277926, by rfl⟩ : syracuseStep 3037235 = 4555853) B4555853
theorem B2024823 : Blo 2023435 2024823 := bstep (se 1 (by rfl) ⟨1518617, by rfl⟩ : syracuseStep 2024823 = 3037235) B3037235
theorem B2562673 : Blo 2023435 2562673 := bbase (se 2 (by rfl) ⟨961002, by rfl⟩ : syracuseStep 2562673 = 1922005) (by norm_num)
theorem B3416897 : Blo 2023435 3416897 := bstep (se 2 (by rfl) ⟨1281336, by rfl⟩ : syracuseStep 3416897 = 2562673) B2562673
theorem B2277931 : Blo 2023435 2277931 := bstep (se 1 (by rfl) ⟨1708448, by rfl⟩ : syracuseStep 2277931 = 3416897) B3416897
theorem B3037241 : Blo 2023435 3037241 := bstep (se 2 (by rfl) ⟨1138965, by rfl⟩ : syracuseStep 3037241 = 2277931) B2277931
theorem B2024827 : Blo 2023435 2024827 := bstep (se 1 (by rfl) ⟨1518620, by rfl⟩ : syracuseStep 2024827 = 3037241) B3037241
theorem B3698597 : Blo 2023435 3698597 := bbase (se 4 (by rfl) ⟨346743, by rfl⟩ : syracuseStep 3698597 = 693487) (by norm_num)
theorem B2465731 : Blo 2023435 2465731 := bstep (se 1 (by rfl) ⟨1849298, by rfl⟩ : syracuseStep 2465731 = 3698597) B3698597
theorem B13150565 : Blo 2023435 13150565 := bstep (se 4 (by rfl) ⟨1232865, by rfl⟩ : syracuseStep 13150565 = 2465731) B2465731
theorem B8767043 : Blo 2023435 8767043 := bstep (se 1 (by rfl) ⟨6575282, by rfl⟩ : syracuseStep 8767043 = 13150565) B13150565
theorem B5844695 : Blo 2023435 5844695 := bstep (se 1 (by rfl) ⟨4383521, by rfl⟩ : syracuseStep 5844695 = 8767043) B8767043
theorem B15585853 : Blo 2023435 15585853 := bstep (se 3 (by rfl) ⟨2922347, by rfl⟩ : syracuseStep 15585853 = 5844695) B5844695
theorem B20781137 : Blo 2023435 20781137 := bstep (se 2 (by rfl) ⟨7792926, by rfl⟩ : syracuseStep 20781137 = 15585853) B15585853
theorem B13854091 : Blo 2023435 13854091 := bstep (se 1 (by rfl) ⟨10390568, by rfl⟩ : syracuseStep 13854091 = 20781137) B20781137
theorem B18472121 : Blo 2023435 18472121 := bstep (se 2 (by rfl) ⟨6927045, by rfl⟩ : syracuseStep 18472121 = 13854091) B13854091
theorem B12314747 : Blo 2023435 12314747 := bstep (se 1 (by rfl) ⟨9236060, by rfl⟩ : syracuseStep 12314747 = 18472121) B18472121
theorem B8209831 : Blo 2023435 8209831 := bstep (se 1 (by rfl) ⟨6157373, by rfl⟩ : syracuseStep 8209831 = 12314747) B12314747
theorem B10946441 : Blo 2023435 10946441 := bstep (se 2 (by rfl) ⟨4104915, by rfl⟩ : syracuseStep 10946441 = 8209831) B8209831
theorem B7297627 : Blo 2023435 7297627 := bstep (se 1 (by rfl) ⟨5473220, by rfl⟩ : syracuseStep 7297627 = 10946441) B10946441
theorem B9730169 : Blo 2023435 9730169 := bstep (se 2 (by rfl) ⟨3648813, by rfl⟩ : syracuseStep 9730169 = 7297627) B7297627
theorem B6486779 : Blo 2023435 6486779 := bstep (se 1 (by rfl) ⟨4865084, by rfl⟩ : syracuseStep 6486779 = 9730169) B9730169
theorem B4324519 : Blo 2023435 4324519 := bstep (se 1 (by rfl) ⟨3243389, by rfl⟩ : syracuseStep 4324519 = 6486779) B6486779
theorem B23064101 : Blo 2023435 23064101 := bstep (se 4 (by rfl) ⟨2162259, by rfl⟩ : syracuseStep 23064101 = 4324519) B4324519
theorem B15376067 : Blo 2023435 15376067 := bstep (se 1 (by rfl) ⟨11532050, by rfl⟩ : syracuseStep 15376067 = 23064101) B23064101
theorem B10250711 : Blo 2023435 10250711 := bstep (se 1 (by rfl) ⟨7688033, by rfl⟩ : syracuseStep 10250711 = 15376067) B15376067
theorem B6833807 : Blo 2023435 6833807 := bstep (se 1 (by rfl) ⟨5125355, by rfl⟩ : syracuseStep 6833807 = 10250711) B10250711
theorem B4555871 : Blo 2023435 4555871 := bstep (se 1 (by rfl) ⟨3416903, by rfl⟩ : syracuseStep 4555871 = 6833807) B6833807
theorem B3037247 : Blo 2023435 3037247 := bstep (se 1 (by rfl) ⟨2277935, by rfl⟩ : syracuseStep 3037247 = 4555871) B4555871
theorem B2024831 : Blo 2023435 2024831 := bstep (se 1 (by rfl) ⟨1518623, by rfl⟩ : syracuseStep 2024831 = 3037247) B3037247
theorem B3037253 : Blo 2023435 3037253 := bbase (se 4 (by rfl) ⟨284742, by rfl⟩ : syracuseStep 3037253 = 569485) (by norm_num)
theorem B2024835 : Blo 2023435 2024835 := bstep (se 1 (by rfl) ⟨1518626, by rfl⟩ : syracuseStep 2024835 = 3037253) B3037253
theorem B3416917 : Blo 2023435 3416917 := bbase (se 9 (by rfl) ⟨10010, by rfl⟩ : syracuseStep 3416917 = 20021) (by norm_num)
theorem B4555889 : Blo 2023435 4555889 := bstep (se 2 (by rfl) ⟨1708458, by rfl⟩ : syracuseStep 4555889 = 3416917) B3416917
theorem B3037259 : Blo 2023435 3037259 := bstep (se 1 (by rfl) ⟨2277944, by rfl⟩ : syracuseStep 3037259 = 4555889) B4555889
theorem B2024839 : Blo 2023435 2024839 := bstep (se 1 (by rfl) ⟨1518629, by rfl⟩ : syracuseStep 2024839 = 3037259) B3037259
theorem B2277949 : Blo 2023435 2277949 := bbase (se 3 (by rfl) ⟨427115, by rfl⟩ : syracuseStep 2277949 = 854231) (by norm_num)
theorem B3037265 : Blo 2023435 3037265 := bstep (se 2 (by rfl) ⟨1138974, by rfl⟩ : syracuseStep 3037265 = 2277949) B2277949
theorem B2024843 : Blo 2023435 2024843 := bstep (se 1 (by rfl) ⟨1518632, by rfl⟩ : syracuseStep 2024843 = 3037265) B3037265
theorem B6833861 : Blo 2023435 6833861 := bbase (se 4 (by rfl) ⟨640674, by rfl⟩ : syracuseStep 6833861 = 1281349) (by norm_num)
theorem B4555907 : Blo 2023435 4555907 := bstep (se 1 (by rfl) ⟨3416930, by rfl⟩ : syracuseStep 4555907 = 6833861) B6833861
theorem B3037271 : Blo 2023435 3037271 := bstep (se 1 (by rfl) ⟨2277953, by rfl⟩ : syracuseStep 3037271 = 4555907) B4555907
theorem B2024847 : Blo 2023435 2024847 := bstep (se 1 (by rfl) ⟨1518635, by rfl⟩ : syracuseStep 2024847 = 3037271) B3037271
theorem B3037277 : Blo 2023435 3037277 := bbase (se 3 (by rfl) ⟨569489, by rfl⟩ : syracuseStep 3037277 = 1138979) (by norm_num)
theorem B2024851 : Blo 2023435 2024851 := bstep (se 1 (by rfl) ⟨1518638, by rfl⟩ : syracuseStep 2024851 = 3037277) B3037277
theorem B4555925 : Blo 2023435 4555925 := bbase (se 6 (by rfl) ⟨106779, by rfl⟩ : syracuseStep 4555925 = 213559) (by norm_num)
theorem B3037283 : Blo 2023435 3037283 := bstep (se 1 (by rfl) ⟨2277962, by rfl⟩ : syracuseStep 3037283 = 4555925) B4555925
theorem B2024855 : Blo 2023435 2024855 := bstep (se 1 (by rfl) ⟨1518641, by rfl⟩ : syracuseStep 2024855 = 3037283) B3037283
theorem B2883053 : Blo 2023435 2883053 := bbase (se 3 (by rfl) ⟨540572, by rfl⟩ : syracuseStep 2883053 = 1081145) (by norm_num)
theorem B7688141 : Blo 2023435 7688141 := bstep (se 3 (by rfl) ⟨1441526, by rfl⟩ : syracuseStep 7688141 = 2883053) B2883053
theorem B5125427 : Blo 2023435 5125427 := bstep (se 1 (by rfl) ⟨3844070, by rfl⟩ : syracuseStep 5125427 = 7688141) B7688141
theorem B3416951 : Blo 2023435 3416951 := bstep (se 1 (by rfl) ⟨2562713, by rfl⟩ : syracuseStep 3416951 = 5125427) B5125427
theorem B2277967 : Blo 2023435 2277967 := bstep (se 1 (by rfl) ⟨1708475, by rfl⟩ : syracuseStep 2277967 = 3416951) B3416951
theorem B3037289 : Blo 2023435 3037289 := bstep (se 2 (by rfl) ⟨1138983, by rfl⟩ : syracuseStep 3037289 = 2277967) B2277967
theorem B2024859 : Blo 2023435 2024859 := bstep (se 1 (by rfl) ⟨1518644, by rfl⟩ : syracuseStep 2024859 = 3037289) B3037289
theorem B3332549 : Blo 2023435 3332549 := bbase (se 4 (by rfl) ⟨312426, by rfl⟩ : syracuseStep 3332549 = 624853) (by norm_num)
theorem B8886797 : Blo 2023435 8886797 := bstep (se 3 (by rfl) ⟨1666274, by rfl⟩ : syracuseStep 8886797 = 3332549) B3332549
theorem B5924531 : Blo 2023435 5924531 := bstep (se 1 (by rfl) ⟨4443398, by rfl⟩ : syracuseStep 5924531 = 8886797) B8886797
theorem B3949687 : Blo 2023435 3949687 := bstep (se 1 (by rfl) ⟨2962265, by rfl⟩ : syracuseStep 3949687 = 5924531) B5924531
theorem B21064997 : Blo 2023435 21064997 := bstep (se 4 (by rfl) ⟨1974843, by rfl⟩ : syracuseStep 21064997 = 3949687) B3949687
theorem B14043331 : Blo 2023435 14043331 := bstep (se 1 (by rfl) ⟨10532498, by rfl⟩ : syracuseStep 14043331 = 21064997) B21064997
theorem B18724441 : Blo 2023435 18724441 := bstep (se 2 (by rfl) ⟨7021665, by rfl⟩ : syracuseStep 18724441 = 14043331) B14043331
theorem B24965921 : Blo 2023435 24965921 := bstep (se 2 (by rfl) ⟨9362220, by rfl⟩ : syracuseStep 24965921 = 18724441) B18724441
theorem B66575789 : Blo 2023435 66575789 := bstep (se 3 (by rfl) ⟨12482960, by rfl⟩ : syracuseStep 66575789 = 24965921) B24965921
theorem B44383859 : Blo 2023435 44383859 := bstep (se 1 (by rfl) ⟨33287894, by rfl⟩ : syracuseStep 44383859 = 66575789) B66575789
theorem B29589239 : Blo 2023435 29589239 := bstep (se 1 (by rfl) ⟨22191929, by rfl⟩ : syracuseStep 29589239 = 44383859) B44383859
theorem B78904637 : Blo 2023435 78904637 := bstep (se 3 (by rfl) ⟨14794619, by rfl⟩ : syracuseStep 78904637 = 29589239) B29589239
theorem B52603091 : Blo 2023435 52603091 := bstep (se 1 (by rfl) ⟨39452318, by rfl⟩ : syracuseStep 52603091 = 78904637) B78904637
theorem B35068727 : Blo 2023435 35068727 := bstep (se 1 (by rfl) ⟨26301545, by rfl⟩ : syracuseStep 35068727 = 52603091) B52603091
theorem B23379151 : Blo 2023435 23379151 := bstep (se 1 (by rfl) ⟨17534363, by rfl⟩ : syracuseStep 23379151 = 35068727) B35068727
theorem B31172201 : Blo 2023435 31172201 := bstep (se 2 (by rfl) ⟨11689575, by rfl⟩ : syracuseStep 31172201 = 23379151) B23379151
theorem B20781467 : Blo 2023435 20781467 := bstep (se 1 (by rfl) ⟨15586100, by rfl⟩ : syracuseStep 20781467 = 31172201) B31172201
theorem B13854311 : Blo 2023435 13854311 := bstep (se 1 (by rfl) ⟨10390733, by rfl⟩ : syracuseStep 13854311 = 20781467) B20781467
theorem B9236207 : Blo 2023435 9236207 := bstep (se 1 (by rfl) ⟨6927155, by rfl⟩ : syracuseStep 9236207 = 13854311) B13854311
theorem B6157471 : Blo 2023435 6157471 := bstep (se 1 (by rfl) ⟨4618103, by rfl⟩ : syracuseStep 6157471 = 9236207) B9236207
theorem B8209961 : Blo 2023435 8209961 := bstep (se 2 (by rfl) ⟨3078735, by rfl⟩ : syracuseStep 8209961 = 6157471) B6157471
theorem B5473307 : Blo 2023435 5473307 := bstep (se 1 (by rfl) ⟨4104980, by rfl⟩ : syracuseStep 5473307 = 8209961) B8209961
theorem B3648871 : Blo 2023435 3648871 := bstep (se 1 (by rfl) ⟨2736653, by rfl⟩ : syracuseStep 3648871 = 5473307) B5473307
theorem B19460645 : Blo 2023435 19460645 := bstep (se 4 (by rfl) ⟨1824435, by rfl⟩ : syracuseStep 19460645 = 3648871) B3648871
theorem B12973763 : Blo 2023435 12973763 := bstep (se 1 (by rfl) ⟨9730322, by rfl⟩ : syracuseStep 12973763 = 19460645) B19460645
theorem B8649175 : Blo 2023435 8649175 := bstep (se 1 (by rfl) ⟨6486881, by rfl⟩ : syracuseStep 8649175 = 12973763) B12973763
theorem B11532233 : Blo 2023435 11532233 := bstep (se 2 (by rfl) ⟨4324587, by rfl⟩ : syracuseStep 11532233 = 8649175) B8649175
theorem B7688155 : Blo 2023435 7688155 := bstep (se 1 (by rfl) ⟨5766116, by rfl⟩ : syracuseStep 7688155 = 11532233) B11532233
theorem B10250873 : Blo 2023435 10250873 := bstep (se 2 (by rfl) ⟨3844077, by rfl⟩ : syracuseStep 10250873 = 7688155) B7688155
theorem B6833915 : Blo 2023435 6833915 := bstep (se 1 (by rfl) ⟨5125436, by rfl⟩ : syracuseStep 6833915 = 10250873) B10250873
theorem B4555943 : Blo 2023435 4555943 := bstep (se 1 (by rfl) ⟨3416957, by rfl⟩ : syracuseStep 4555943 = 6833915) B6833915
theorem B3037295 : Blo 2023435 3037295 := bstep (se 1 (by rfl) ⟨2277971, by rfl⟩ : syracuseStep 3037295 = 4555943) B4555943
theorem B2024863 : Blo 2023435 2024863 := bstep (se 1 (by rfl) ⟨1518647, by rfl⟩ : syracuseStep 2024863 = 3037295) B3037295
theorem B3037301 : Blo 2023435 3037301 := bbase (se 5 (by rfl) ⟨142373, by rfl⟩ : syracuseStep 3037301 = 284747) (by norm_num)
theorem B2024867 : Blo 2023435 2024867 := bstep (se 1 (by rfl) ⟨1518650, by rfl⟩ : syracuseStep 2024867 = 3037301) B3037301
theorem B3844093 : Blo 2023435 3844093 := bbase (se 3 (by rfl) ⟨720767, by rfl⟩ : syracuseStep 3844093 = 1441535) (by norm_num)
theorem B5125457 : Blo 2023435 5125457 := bstep (se 2 (by rfl) ⟨1922046, by rfl⟩ : syracuseStep 5125457 = 3844093) B3844093
theorem B3416971 : Blo 2023435 3416971 := bstep (se 1 (by rfl) ⟨2562728, by rfl⟩ : syracuseStep 3416971 = 5125457) B5125457
theorem B4555961 : Blo 2023435 4555961 := bstep (se 2 (by rfl) ⟨1708485, by rfl⟩ : syracuseStep 4555961 = 3416971) B3416971
theorem B3037307 : Blo 2023435 3037307 := bstep (se 1 (by rfl) ⟨2277980, by rfl⟩ : syracuseStep 3037307 = 4555961) B4555961
theorem B2024871 : Blo 2023435 2024871 := bstep (se 1 (by rfl) ⟨1518653, by rfl⟩ : syracuseStep 2024871 = 3037307) B3037307
theorem B2277985 : Blo 2023435 2277985 := bbase (se 2 (by rfl) ⟨854244, by rfl⟩ : syracuseStep 2277985 = 1708489) (by norm_num)
theorem B3037313 : Blo 2023435 3037313 := bstep (se 2 (by rfl) ⟨1138992, by rfl⟩ : syracuseStep 3037313 = 2277985) B2277985
theorem B2024875 : Blo 2023435 2024875 := bstep (se 1 (by rfl) ⟨1518656, by rfl⟩ : syracuseStep 2024875 = 3037313) B3037313
theorem B5125477 : Blo 2023435 5125477 := bbase (se 4 (by rfl) ⟨480513, by rfl⟩ : syracuseStep 5125477 = 961027) (by norm_num)
theorem B6833969 : Blo 2023435 6833969 := bstep (se 2 (by rfl) ⟨2562738, by rfl⟩ : syracuseStep 6833969 = 5125477) B5125477
theorem B4555979 : Blo 2023435 4555979 := bstep (se 1 (by rfl) ⟨3416984, by rfl⟩ : syracuseStep 4555979 = 6833969) B6833969
theorem B3037319 : Blo 2023435 3037319 := bstep (se 1 (by rfl) ⟨2277989, by rfl⟩ : syracuseStep 3037319 = 4555979) B4555979
theorem B2024879 : Blo 2023435 2024879 := bstep (se 1 (by rfl) ⟨1518659, by rfl⟩ : syracuseStep 2024879 = 3037319) B3037319
theorem B3037325 : Blo 2023435 3037325 := bbase (se 3 (by rfl) ⟨569498, by rfl⟩ : syracuseStep 3037325 = 1138997) (by norm_num)
theorem B2024883 : Blo 2023435 2024883 := bstep (se 1 (by rfl) ⟨1518662, by rfl⟩ : syracuseStep 2024883 = 3037325) B3037325
theorem B4555997 : Blo 2023435 4555997 := bbase (se 3 (by rfl) ⟨854249, by rfl⟩ : syracuseStep 4555997 = 1708499) (by norm_num)
theorem B3037331 : Blo 2023435 3037331 := bstep (se 1 (by rfl) ⟨2277998, by rfl⟩ : syracuseStep 3037331 = 4555997) B4555997
theorem B2024887 : Blo 2023435 2024887 := bstep (se 1 (by rfl) ⟨1518665, by rfl⟩ : syracuseStep 2024887 = 3037331) B3037331
theorem B3417005 : Blo 2023435 3417005 := bbase (se 3 (by rfl) ⟨640688, by rfl⟩ : syracuseStep 3417005 = 1281377) (by norm_num)
theorem B2278003 : Blo 2023435 2278003 := bstep (se 1 (by rfl) ⟨1708502, by rfl⟩ : syracuseStep 2278003 = 3417005) B3417005
theorem B3037337 : Blo 2023435 3037337 := bstep (se 2 (by rfl) ⟨1139001, by rfl⟩ : syracuseStep 3037337 = 2278003) B2278003
theorem B2024891 : Blo 2023435 2024891 := bstep (se 1 (by rfl) ⟨1518668, by rfl⟩ : syracuseStep 2024891 = 3037337) B3037337
theorem B35069269 : Blo 2023435 35069269 := bbase (se 11 (by rfl) ⟨25685, by rfl⟩ : syracuseStep 35069269 = 51371) (by norm_num)
theorem B46759025 : Blo 2023435 46759025 := bstep (se 2 (by rfl) ⟨17534634, by rfl⟩ : syracuseStep 46759025 = 35069269) B35069269
theorem B31172683 : Blo 2023435 31172683 := bstep (se 1 (by rfl) ⟨23379512, by rfl⟩ : syracuseStep 31172683 = 46759025) B46759025
theorem B41563577 : Blo 2023435 41563577 := bstep (se 2 (by rfl) ⟨15586341, by rfl⟩ : syracuseStep 41563577 = 31172683) B31172683
theorem B27709051 : Blo 2023435 27709051 := bstep (se 1 (by rfl) ⟨20781788, by rfl⟩ : syracuseStep 27709051 = 41563577) B41563577
theorem B36945401 : Blo 2023435 36945401 := bstep (se 2 (by rfl) ⟨13854525, by rfl⟩ : syracuseStep 36945401 = 27709051) B27709051
theorem B98521069 : Blo 2023435 98521069 := bstep (se 3 (by rfl) ⟨18472700, by rfl⟩ : syracuseStep 98521069 = 36945401) B36945401
theorem B131361425 : Blo 2023435 131361425 := bstep (se 2 (by rfl) ⟨49260534, by rfl⟩ : syracuseStep 131361425 = 98521069) B98521069
theorem B87574283 : Blo 2023435 87574283 := bstep (se 1 (by rfl) ⟨65680712, by rfl⟩ : syracuseStep 87574283 = 131361425) B131361425
theorem B58382855 : Blo 2023435 58382855 := bstep (se 1 (by rfl) ⟨43787141, by rfl⟩ : syracuseStep 58382855 = 87574283) B87574283
theorem B38921903 : Blo 2023435 38921903 := bstep (se 1 (by rfl) ⟨29191427, by rfl⟩ : syracuseStep 38921903 = 58382855) B58382855
theorem B25947935 : Blo 2023435 25947935 := bstep (se 1 (by rfl) ⟨19460951, by rfl⟩ : syracuseStep 25947935 = 38921903) B38921903
theorem B17298623 : Blo 2023435 17298623 := bstep (se 1 (by rfl) ⟨12973967, by rfl⟩ : syracuseStep 17298623 = 25947935) B25947935
theorem B11532415 : Blo 2023435 11532415 := bstep (se 1 (by rfl) ⟨8649311, by rfl⟩ : syracuseStep 11532415 = 17298623) B17298623
theorem B15376553 : Blo 2023435 15376553 := bstep (se 2 (by rfl) ⟨5766207, by rfl⟩ : syracuseStep 15376553 = 11532415) B11532415
theorem B10251035 : Blo 2023435 10251035 := bstep (se 1 (by rfl) ⟨7688276, by rfl⟩ : syracuseStep 10251035 = 15376553) B15376553
theorem B6834023 : Blo 2023435 6834023 := bstep (se 1 (by rfl) ⟨5125517, by rfl⟩ : syracuseStep 6834023 = 10251035) B10251035
theorem B4556015 : Blo 2023435 4556015 := bstep (se 1 (by rfl) ⟨3417011, by rfl⟩ : syracuseStep 4556015 = 6834023) B6834023
theorem B3037343 : Blo 2023435 3037343 := bstep (se 1 (by rfl) ⟨2278007, by rfl⟩ : syracuseStep 3037343 = 4556015) B4556015
theorem B2024895 : Blo 2023435 2024895 := bstep (se 1 (by rfl) ⟨1518671, by rfl⟩ : syracuseStep 2024895 = 3037343) B3037343
theorem B3037349 : Blo 2023435 3037349 := bbase (se 4 (by rfl) ⟨284751, by rfl⟩ : syracuseStep 3037349 = 569503) (by norm_num)
theorem B2024899 : Blo 2023435 2024899 := bstep (se 1 (by rfl) ⟨1518674, by rfl⟩ : syracuseStep 2024899 = 3037349) B3037349
theorem B2562769 : Blo 2023435 2562769 := bbase (se 2 (by rfl) ⟨961038, by rfl⟩ : syracuseStep 2562769 = 1922077) (by norm_num)
theorem B3417025 : Blo 2023435 3417025 := bstep (se 2 (by rfl) ⟨1281384, by rfl⟩ : syracuseStep 3417025 = 2562769) B2562769
theorem B4556033 : Blo 2023435 4556033 := bstep (se 2 (by rfl) ⟨1708512, by rfl⟩ : syracuseStep 4556033 = 3417025) B3417025
theorem B3037355 : Blo 2023435 3037355 := bstep (se 1 (by rfl) ⟨2278016, by rfl⟩ : syracuseStep 3037355 = 4556033) B4556033
theorem B2024903 : Blo 2023435 2024903 := bstep (se 1 (by rfl) ⟨1518677, by rfl⟩ : syracuseStep 2024903 = 3037355) B3037355
theorem B2278021 : Blo 2023435 2278021 := bbase (se 4 (by rfl) ⟨213564, by rfl⟩ : syracuseStep 2278021 = 427129) (by norm_num)
theorem B3037361 : Blo 2023435 3037361 := bstep (se 2 (by rfl) ⟨1139010, by rfl⟩ : syracuseStep 3037361 = 2278021) B2278021
theorem B2024907 : Blo 2023435 2024907 := bstep (se 1 (by rfl) ⟨1518680, by rfl⟩ : syracuseStep 2024907 = 3037361) B3037361
theorem B9863317 : Blo 2023435 9863317 := bbase (se 6 (by rfl) ⟨231171, by rfl⟩ : syracuseStep 9863317 = 462343) (by norm_num)
theorem B13151089 : Blo 2023435 13151089 := bstep (se 2 (by rfl) ⟨4931658, by rfl⟩ : syracuseStep 13151089 = 9863317) B9863317
theorem B70139141 : Blo 2023435 70139141 := bstep (se 4 (by rfl) ⟨6575544, by rfl⟩ : syracuseStep 70139141 = 13151089) B13151089
theorem B46759427 : Blo 2023435 46759427 := bstep (se 1 (by rfl) ⟨35069570, by rfl⟩ : syracuseStep 46759427 = 70139141) B70139141
theorem B31172951 : Blo 2023435 31172951 := bstep (se 1 (by rfl) ⟨23379713, by rfl⟩ : syracuseStep 31172951 = 46759427) B46759427
theorem B20781967 : Blo 2023435 20781967 := bstep (se 1 (by rfl) ⟨15586475, by rfl⟩ : syracuseStep 20781967 = 31172951) B31172951
theorem B27709289 : Blo 2023435 27709289 := bstep (se 2 (by rfl) ⟨10390983, by rfl⟩ : syracuseStep 27709289 = 20781967) B20781967
theorem B18472859 : Blo 2023435 18472859 := bstep (se 1 (by rfl) ⟨13854644, by rfl⟩ : syracuseStep 18472859 = 27709289) B27709289
theorem B12315239 : Blo 2023435 12315239 := bstep (se 1 (by rfl) ⟨9236429, by rfl⟩ : syracuseStep 12315239 = 18472859) B18472859
theorem B8210159 : Blo 2023435 8210159 := bstep (se 1 (by rfl) ⟨6157619, by rfl⟩ : syracuseStep 8210159 = 12315239) B12315239
theorem B5473439 : Blo 2023435 5473439 := bstep (se 1 (by rfl) ⟨4105079, by rfl⟩ : syracuseStep 5473439 = 8210159) B8210159
theorem B3648959 : Blo 2023435 3648959 := bstep (se 1 (by rfl) ⟨2736719, by rfl⟩ : syracuseStep 3648959 = 5473439) B5473439
theorem B2432639 : Blo 2023435 2432639 := bstep (se 1 (by rfl) ⟨1824479, by rfl⟩ : syracuseStep 2432639 = 3648959) B3648959
theorem B6487037 : Blo 2023435 6487037 := bstep (se 3 (by rfl) ⟨1216319, by rfl⟩ : syracuseStep 6487037 = 2432639) B2432639
theorem B4324691 : Blo 2023435 4324691 := bstep (se 1 (by rfl) ⟨3243518, by rfl⟩ : syracuseStep 4324691 = 6487037) B6487037
theorem B2883127 : Blo 2023435 2883127 := bstep (se 1 (by rfl) ⟨2162345, by rfl⟩ : syracuseStep 2883127 = 4324691) B4324691
theorem B3844169 : Blo 2023435 3844169 := bstep (se 2 (by rfl) ⟨1441563, by rfl⟩ : syracuseStep 3844169 = 2883127) B2883127
theorem B2562779 : Blo 2023435 2562779 := bstep (se 1 (by rfl) ⟨1922084, by rfl⟩ : syracuseStep 2562779 = 3844169) B3844169
theorem B6834077 : Blo 2023435 6834077 := bstep (se 3 (by rfl) ⟨1281389, by rfl⟩ : syracuseStep 6834077 = 2562779) B2562779
theorem B4556051 : Blo 2023435 4556051 := bstep (se 1 (by rfl) ⟨3417038, by rfl⟩ : syracuseStep 4556051 = 6834077) B6834077
theorem B3037367 : Blo 2023435 3037367 := bstep (se 1 (by rfl) ⟨2278025, by rfl⟩ : syracuseStep 3037367 = 4556051) B4556051
theorem B2024911 : Blo 2023435 2024911 := bstep (se 1 (by rfl) ⟨1518683, by rfl⟩ : syracuseStep 2024911 = 3037367) B3037367
theorem B3037373 : Blo 2023435 3037373 := bbase (se 3 (by rfl) ⟨569507, by rfl⟩ : syracuseStep 3037373 = 1139015) (by norm_num)
theorem B2024915 : Blo 2023435 2024915 := bstep (se 1 (by rfl) ⟨1518686, by rfl⟩ : syracuseStep 2024915 = 3037373) B3037373
theorem B4556069 : Blo 2023435 4556069 := bbase (se 4 (by rfl) ⟨427131, by rfl⟩ : syracuseStep 4556069 = 854263) (by norm_num)
theorem B3037379 : Blo 2023435 3037379 := bstep (se 1 (by rfl) ⟨2278034, by rfl⟩ : syracuseStep 3037379 = 4556069) B4556069
theorem B2024919 : Blo 2023435 2024919 := bstep (se 1 (by rfl) ⟨1518689, by rfl⟩ : syracuseStep 2024919 = 3037379) B3037379
theorem B5125589 : Blo 2023435 5125589 := bbase (se 7 (by rfl) ⟨60065, by rfl⟩ : syracuseStep 5125589 = 120131) (by norm_num)
theorem B3417059 : Blo 2023435 3417059 := bstep (se 1 (by rfl) ⟨2562794, by rfl⟩ : syracuseStep 3417059 = 5125589) B5125589
theorem B2278039 : Blo 2023435 2278039 := bstep (se 1 (by rfl) ⟨1708529, by rfl⟩ : syracuseStep 2278039 = 3417059) B3417059
theorem B3037385 : Blo 2023435 3037385 := bstep (se 2 (by rfl) ⟨1139019, by rfl⟩ : syracuseStep 3037385 = 2278039) B2278039
theorem B2024923 : Blo 2023435 2024923 := bstep (se 1 (by rfl) ⟨1518692, by rfl⟩ : syracuseStep 2024923 = 3037385) B3037385
theorem B2191865 : Blo 2023435 2191865 := bbase (se 2 (by rfl) ⟨821949, by rfl⟩ : syracuseStep 2191865 = 1643899) (by norm_num)
theorem B5844973 : Blo 2023435 5844973 := bstep (se 3 (by rfl) ⟨1095932, by rfl⟩ : syracuseStep 5844973 = 2191865) B2191865
theorem B7793297 : Blo 2023435 7793297 := bstep (se 2 (by rfl) ⟨2922486, by rfl⟩ : syracuseStep 7793297 = 5844973) B5844973
theorem B5195531 : Blo 2023435 5195531 := bstep (se 1 (by rfl) ⟨3896648, by rfl⟩ : syracuseStep 5195531 = 7793297) B7793297
theorem B3463687 : Blo 2023435 3463687 := bstep (se 1 (by rfl) ⟨2597765, by rfl⟩ : syracuseStep 3463687 = 5195531) B5195531
theorem B18472997 : Blo 2023435 18472997 := bstep (se 4 (by rfl) ⟨1731843, by rfl⟩ : syracuseStep 18472997 = 3463687) B3463687
theorem B12315331 : Blo 2023435 12315331 := bstep (se 1 (by rfl) ⟨9236498, by rfl⟩ : syracuseStep 12315331 = 18472997) B18472997
theorem B16420441 : Blo 2023435 16420441 := bstep (se 2 (by rfl) ⟨6157665, by rfl⟩ : syracuseStep 16420441 = 12315331) B12315331
theorem B21893921 : Blo 2023435 21893921 := bstep (se 2 (by rfl) ⟨8210220, by rfl⟩ : syracuseStep 21893921 = 16420441) B16420441
theorem B14595947 : Blo 2023435 14595947 := bstep (se 1 (by rfl) ⟨10946960, by rfl⟩ : syracuseStep 14595947 = 21893921) B21893921
theorem B9730631 : Blo 2023435 9730631 := bstep (se 1 (by rfl) ⟨7297973, by rfl⟩ : syracuseStep 9730631 = 14595947) B14595947
theorem B6487087 : Blo 2023435 6487087 := bstep (se 1 (by rfl) ⟨4865315, by rfl⟩ : syracuseStep 6487087 = 9730631) B9730631
theorem B8649449 : Blo 2023435 8649449 := bstep (se 2 (by rfl) ⟨3243543, by rfl⟩ : syracuseStep 8649449 = 6487087) B6487087
theorem B5766299 : Blo 2023435 5766299 := bstep (se 1 (by rfl) ⟨4324724, by rfl⟩ : syracuseStep 5766299 = 8649449) B8649449
theorem B3844199 : Blo 2023435 3844199 := bstep (se 1 (by rfl) ⟨2883149, by rfl⟩ : syracuseStep 3844199 = 5766299) B5766299
theorem B10251197 : Blo 2023435 10251197 := bstep (se 3 (by rfl) ⟨1922099, by rfl⟩ : syracuseStep 10251197 = 3844199) B3844199
theorem B6834131 : Blo 2023435 6834131 := bstep (se 1 (by rfl) ⟨5125598, by rfl⟩ : syracuseStep 6834131 = 10251197) B10251197
theorem B4556087 : Blo 2023435 4556087 := bstep (se 1 (by rfl) ⟨3417065, by rfl⟩ : syracuseStep 4556087 = 6834131) B6834131
theorem B3037391 : Blo 2023435 3037391 := bstep (se 1 (by rfl) ⟨2278043, by rfl⟩ : syracuseStep 3037391 = 4556087) B4556087
theorem B2024927 : Blo 2023435 2024927 := bstep (se 1 (by rfl) ⟨1518695, by rfl⟩ : syracuseStep 2024927 = 3037391) B3037391
theorem B3037397 : Blo 2023435 3037397 := bbase (se 7 (by rfl) ⟨35594, by rfl⟩ : syracuseStep 3037397 = 71189) (by norm_num)
theorem B2024931 : Blo 2023435 2024931 := bstep (se 1 (by rfl) ⟨1518698, by rfl⟩ : syracuseStep 2024931 = 3037397) B3037397
theorem B3243557 : Blo 2023435 3243557 := bbase (se 4 (by rfl) ⟨304083, by rfl⟩ : syracuseStep 3243557 = 608167) (by norm_num)
theorem B2162371 : Blo 2023435 2162371 := bstep (se 1 (by rfl) ⟨1621778, by rfl⟩ : syracuseStep 2162371 = 3243557) B3243557
theorem B2883161 : Blo 2023435 2883161 := bstep (se 2 (by rfl) ⟨1081185, by rfl⟩ : syracuseStep 2883161 = 2162371) B2162371
theorem B7688429 : Blo 2023435 7688429 := bstep (se 3 (by rfl) ⟨1441580, by rfl⟩ : syracuseStep 7688429 = 2883161) B2883161
theorem B5125619 : Blo 2023435 5125619 := bstep (se 1 (by rfl) ⟨3844214, by rfl⟩ : syracuseStep 5125619 = 7688429) B7688429
theorem B3417079 : Blo 2023435 3417079 := bstep (se 1 (by rfl) ⟨2562809, by rfl⟩ : syracuseStep 3417079 = 5125619) B5125619
theorem B4556105 : Blo 2023435 4556105 := bstep (se 2 (by rfl) ⟨1708539, by rfl⟩ : syracuseStep 4556105 = 3417079) B3417079
theorem B3037403 : Blo 2023435 3037403 := bstep (se 1 (by rfl) ⟨2278052, by rfl⟩ : syracuseStep 3037403 = 4556105) B4556105
theorem B2024935 : Blo 2023435 2024935 := bstep (se 1 (by rfl) ⟨1518701, by rfl⟩ : syracuseStep 2024935 = 3037403) B3037403
theorem B2278057 : Blo 2023435 2278057 := bbase (se 2 (by rfl) ⟨854271, by rfl⟩ : syracuseStep 2278057 = 1708543) (by norm_num)
theorem B3037409 : Blo 2023435 3037409 := bstep (se 2 (by rfl) ⟨1139028, by rfl⟩ : syracuseStep 3037409 = 2278057) B2278057
theorem B2024939 : Blo 2023435 2024939 := bstep (se 1 (by rfl) ⟨1518704, by rfl⟩ : syracuseStep 2024939 = 3037409) B3037409
theorem B2432677 : Blo 2023435 2432677 := bbase (se 4 (by rfl) ⟨228063, by rfl⟩ : syracuseStep 2432677 = 456127) (by norm_num)
theorem B3243569 : Blo 2023435 3243569 := bstep (se 2 (by rfl) ⟨1216338, by rfl⟩ : syracuseStep 3243569 = 2432677) B2432677
theorem B8649517 : Blo 2023435 8649517 := bstep (se 3 (by rfl) ⟨1621784, by rfl⟩ : syracuseStep 8649517 = 3243569) B3243569
theorem B11532689 : Blo 2023435 11532689 := bstep (se 2 (by rfl) ⟨4324758, by rfl⟩ : syracuseStep 11532689 = 8649517) B8649517
theorem B7688459 : Blo 2023435 7688459 := bstep (se 1 (by rfl) ⟨5766344, by rfl⟩ : syracuseStep 7688459 = 11532689) B11532689
theorem B5125639 : Blo 2023435 5125639 := bstep (se 1 (by rfl) ⟨3844229, by rfl⟩ : syracuseStep 5125639 = 7688459) B7688459
theorem B6834185 : Blo 2023435 6834185 := bstep (se 2 (by rfl) ⟨2562819, by rfl⟩ : syracuseStep 6834185 = 5125639) B5125639
theorem B4556123 : Blo 2023435 4556123 := bstep (se 1 (by rfl) ⟨3417092, by rfl⟩ : syracuseStep 4556123 = 6834185) B6834185
theorem B3037415 : Blo 2023435 3037415 := bstep (se 1 (by rfl) ⟨2278061, by rfl⟩ : syracuseStep 3037415 = 4556123) B4556123
theorem B2024943 : Blo 2023435 2024943 := bstep (se 1 (by rfl) ⟨1518707, by rfl⟩ : syracuseStep 2024943 = 3037415) B3037415
theorem B3037421 : Blo 2023435 3037421 := bbase (se 3 (by rfl) ⟨569516, by rfl⟩ : syracuseStep 3037421 = 1139033) (by norm_num)
theorem B2024947 : Blo 2023435 2024947 := bstep (se 1 (by rfl) ⟨1518710, by rfl⟩ : syracuseStep 2024947 = 3037421) B3037421
theorem B4556141 : Blo 2023435 4556141 := bbase (se 3 (by rfl) ⟨854276, by rfl⟩ : syracuseStep 4556141 = 1708553) (by norm_num)
theorem B3037427 : Blo 2023435 3037427 := bstep (se 1 (by rfl) ⟨2278070, by rfl⟩ : syracuseStep 3037427 = 4556141) B4556141
theorem B2024951 : Blo 2023435 2024951 := bstep (se 1 (by rfl) ⟨1518713, by rfl⟩ : syracuseStep 2024951 = 3037427) B3037427
theorem B3844253 : Blo 2023435 3844253 := bbase (se 3 (by rfl) ⟨720797, by rfl⟩ : syracuseStep 3844253 = 1441595) (by norm_num)
theorem B2562835 : Blo 2023435 2562835 := bstep (se 1 (by rfl) ⟨1922126, by rfl⟩ : syracuseStep 2562835 = 3844253) B3844253
theorem B3417113 : Blo 2023435 3417113 := bstep (se 2 (by rfl) ⟨1281417, by rfl⟩ : syracuseStep 3417113 = 2562835) B2562835
theorem B2278075 : Blo 2023435 2278075 := bstep (se 1 (by rfl) ⟨1708556, by rfl⟩ : syracuseStep 2278075 = 3417113) B3417113
theorem B3037433 : Blo 2023435 3037433 := bstep (se 2 (by rfl) ⟨1139037, by rfl⟩ : syracuseStep 3037433 = 2278075) B2278075
theorem B2024955 : Blo 2023435 2024955 := bstep (se 1 (by rfl) ⟨1518716, by rfl⟩ : syracuseStep 2024955 = 3037433) B3037433
theorem B3463741 : Blo 2023435 3463741 := bbase (se 3 (by rfl) ⟨649451, by rfl⟩ : syracuseStep 3463741 = 1298903) (by norm_num)
theorem B18473285 : Blo 2023435 18473285 := bstep (se 4 (by rfl) ⟨1731870, by rfl⟩ : syracuseStep 18473285 = 3463741) B3463741
theorem B49262093 : Blo 2023435 49262093 := bstep (se 3 (by rfl) ⟨9236642, by rfl⟩ : syracuseStep 49262093 = 18473285) B18473285
theorem B32841395 : Blo 2023435 32841395 := bstep (se 1 (by rfl) ⟨24631046, by rfl⟩ : syracuseStep 32841395 = 49262093) B49262093
theorem B21894263 : Blo 2023435 21894263 := bstep (se 1 (by rfl) ⟨16420697, by rfl⟩ : syracuseStep 21894263 = 32841395) B32841395
theorem B14596175 : Blo 2023435 14596175 := bstep (se 1 (by rfl) ⟨10947131, by rfl⟩ : syracuseStep 14596175 = 21894263) B21894263
theorem B9730783 : Blo 2023435 9730783 := bstep (se 1 (by rfl) ⟨7298087, by rfl⟩ : syracuseStep 9730783 = 14596175) B14596175
theorem B51897509 : Blo 2023435 51897509 := bstep (se 4 (by rfl) ⟨4865391, by rfl⟩ : syracuseStep 51897509 = 9730783) B9730783
theorem B34598339 : Blo 2023435 34598339 := bstep (se 1 (by rfl) ⟨25948754, by rfl⟩ : syracuseStep 34598339 = 51897509) B51897509
theorem B23065559 : Blo 2023435 23065559 := bstep (se 1 (by rfl) ⟨17299169, by rfl⟩ : syracuseStep 23065559 = 34598339) B34598339
theorem B15377039 : Blo 2023435 15377039 := bstep (se 1 (by rfl) ⟨11532779, by rfl⟩ : syracuseStep 15377039 = 23065559) B23065559
theorem B10251359 : Blo 2023435 10251359 := bstep (se 1 (by rfl) ⟨7688519, by rfl⟩ : syracuseStep 10251359 = 15377039) B15377039
theorem B6834239 : Blo 2023435 6834239 := bstep (se 1 (by rfl) ⟨5125679, by rfl⟩ : syracuseStep 6834239 = 10251359) B10251359
theorem B4556159 : Blo 2023435 4556159 := bstep (se 1 (by rfl) ⟨3417119, by rfl⟩ : syracuseStep 4556159 = 6834239) B6834239
theorem B3037439 : Blo 2023435 3037439 := bstep (se 1 (by rfl) ⟨2278079, by rfl⟩ : syracuseStep 3037439 = 4556159) B4556159
theorem B2024959 : Blo 2023435 2024959 := bstep (se 1 (by rfl) ⟨1518719, by rfl⟩ : syracuseStep 2024959 = 3037439) B3037439
theorem B3037445 : Blo 2023435 3037445 := bbase (se 4 (by rfl) ⟨284760, by rfl⟩ : syracuseStep 3037445 = 569521) (by norm_num)
theorem B2024963 : Blo 2023435 2024963 := bstep (se 1 (by rfl) ⟨1518722, by rfl⟩ : syracuseStep 2024963 = 3037445) B3037445
theorem B3417133 : Blo 2023435 3417133 := bbase (se 3 (by rfl) ⟨640712, by rfl⟩ : syracuseStep 3417133 = 1281425) (by norm_num)
theorem B4556177 : Blo 2023435 4556177 := bstep (se 2 (by rfl) ⟨1708566, by rfl⟩ : syracuseStep 4556177 = 3417133) B3417133
theorem B3037451 : Blo 2023435 3037451 := bstep (se 1 (by rfl) ⟨2278088, by rfl⟩ : syracuseStep 3037451 = 4556177) B4556177
theorem B2024967 : Blo 2023435 2024967 := bstep (se 1 (by rfl) ⟨1518725, by rfl⟩ : syracuseStep 2024967 = 3037451) B3037451
theorem B2278093 : Blo 2023435 2278093 := bbase (se 3 (by rfl) ⟨427142, by rfl⟩ : syracuseStep 2278093 = 854285) (by norm_num)
theorem B3037457 : Blo 2023435 3037457 := bstep (se 2 (by rfl) ⟨1139046, by rfl⟩ : syracuseStep 3037457 = 2278093) B2278093
theorem B2024971 : Blo 2023435 2024971 := bstep (se 1 (by rfl) ⟨1518728, by rfl⟩ : syracuseStep 2024971 = 3037457) B3037457
theorem B6834293 : Blo 2023435 6834293 := bbase (se 5 (by rfl) ⟨320357, by rfl⟩ : syracuseStep 6834293 = 640715) (by norm_num)
theorem B4556195 : Blo 2023435 4556195 := bstep (se 1 (by rfl) ⟨3417146, by rfl⟩ : syracuseStep 4556195 = 6834293) B6834293
theorem B3037463 : Blo 2023435 3037463 := bstep (se 1 (by rfl) ⟨2278097, by rfl⟩ : syracuseStep 3037463 = 4556195) B4556195
theorem B2024975 : Blo 2023435 2024975 := bstep (se 1 (by rfl) ⟨1518731, by rfl⟩ : syracuseStep 2024975 = 3037463) B3037463
theorem B3037469 : Blo 2023435 3037469 := bbase (se 3 (by rfl) ⟨569525, by rfl⟩ : syracuseStep 3037469 = 1139051) (by norm_num)
theorem B2024979 : Blo 2023435 2024979 := bstep (se 1 (by rfl) ⟨1518734, by rfl⟩ : syracuseStep 2024979 = 3037469) B3037469
theorem B4556213 : Blo 2023435 4556213 := bbase (se 5 (by rfl) ⟨213572, by rfl⟩ : syracuseStep 4556213 = 427145) (by norm_num)
theorem B3037475 : Blo 2023435 3037475 := bstep (se 1 (by rfl) ⟨2278106, by rfl⟩ : syracuseStep 3037475 = 4556213) B4556213
theorem B2024983 : Blo 2023435 2024983 := bstep (se 1 (by rfl) ⟨1518737, by rfl⟩ : syracuseStep 2024983 = 3037475) B3037475
theorem B4324853 : Blo 2023435 4324853 := bbase (se 5 (by rfl) ⟨202727, by rfl⟩ : syracuseStep 4324853 = 405455) (by norm_num)
theorem B11532941 : Blo 2023435 11532941 := bstep (se 3 (by rfl) ⟨2162426, by rfl⟩ : syracuseStep 11532941 = 4324853) B4324853
theorem B7688627 : Blo 2023435 7688627 := bstep (se 1 (by rfl) ⟨5766470, by rfl⟩ : syracuseStep 7688627 = 11532941) B11532941
theorem B5125751 : Blo 2023435 5125751 := bstep (se 1 (by rfl) ⟨3844313, by rfl⟩ : syracuseStep 5125751 = 7688627) B7688627
theorem B3417167 : Blo 2023435 3417167 := bstep (se 1 (by rfl) ⟨2562875, by rfl⟩ : syracuseStep 3417167 = 5125751) B5125751
theorem B2278111 : Blo 2023435 2278111 := bstep (se 1 (by rfl) ⟨1708583, by rfl⟩ : syracuseStep 2278111 = 3417167) B3417167
theorem B3037481 : Blo 2023435 3037481 := bstep (se 2 (by rfl) ⟨1139055, by rfl⟩ : syracuseStep 3037481 = 2278111) B2278111
theorem B2024987 : Blo 2023435 2024987 := bstep (se 1 (by rfl) ⟨1518740, by rfl⟩ : syracuseStep 2024987 = 3037481) B3037481
theorem B4324861 : Blo 2023435 4324861 := bbase (se 3 (by rfl) ⟨810911, by rfl⟩ : syracuseStep 4324861 = 1621823) (by norm_num)
theorem B5766481 : Blo 2023435 5766481 := bstep (se 2 (by rfl) ⟨2162430, by rfl⟩ : syracuseStep 5766481 = 4324861) B4324861
theorem B7688641 : Blo 2023435 7688641 := bstep (se 2 (by rfl) ⟨2883240, by rfl⟩ : syracuseStep 7688641 = 5766481) B5766481
theorem B10251521 : Blo 2023435 10251521 := bstep (se 2 (by rfl) ⟨3844320, by rfl⟩ : syracuseStep 10251521 = 7688641) B7688641
theorem B6834347 : Blo 2023435 6834347 := bstep (se 1 (by rfl) ⟨5125760, by rfl⟩ : syracuseStep 6834347 = 10251521) B10251521
theorem B4556231 : Blo 2023435 4556231 := bstep (se 1 (by rfl) ⟨3417173, by rfl⟩ : syracuseStep 4556231 = 6834347) B6834347
theorem B3037487 : Blo 2023435 3037487 := bstep (se 1 (by rfl) ⟨2278115, by rfl⟩ : syracuseStep 3037487 = 4556231) B4556231
theorem B2024991 : Blo 2023435 2024991 := bstep (se 1 (by rfl) ⟨1518743, by rfl⟩ : syracuseStep 2024991 = 3037487) B3037487
theorem B3037493 : Blo 2023435 3037493 := bbase (se 5 (by rfl) ⟨142382, by rfl⟩ : syracuseStep 3037493 = 284765) (by norm_num)
theorem B2024995 : Blo 2023435 2024995 := bstep (se 1 (by rfl) ⟨1518746, by rfl⟩ : syracuseStep 2024995 = 3037493) B3037493
theorem B5125781 : Blo 2023435 5125781 := bbase (se 6 (by rfl) ⟨120135, by rfl⟩ : syracuseStep 5125781 = 240271) (by norm_num)
theorem B3417187 : Blo 2023435 3417187 := bstep (se 1 (by rfl) ⟨2562890, by rfl⟩ : syracuseStep 3417187 = 5125781) B5125781
theorem B4556249 : Blo 2023435 4556249 := bstep (se 2 (by rfl) ⟨1708593, by rfl⟩ : syracuseStep 4556249 = 3417187) B3417187
theorem B3037499 : Blo 2023435 3037499 := bstep (se 1 (by rfl) ⟨2278124, by rfl⟩ : syracuseStep 3037499 = 4556249) B4556249
theorem B2024999 : Blo 2023435 2024999 := bstep (se 1 (by rfl) ⟨1518749, by rfl⟩ : syracuseStep 2024999 = 3037499) B3037499
theorem B2278129 : Blo 2023435 2278129 := bbase (se 2 (by rfl) ⟨854298, by rfl⟩ : syracuseStep 2278129 = 1708597) (by norm_num)
theorem B3037505 : Blo 2023435 3037505 := bstep (se 2 (by rfl) ⟨1139064, by rfl⟩ : syracuseStep 3037505 = 2278129) B2278129
theorem B2025003 : Blo 2023435 2025003 := bstep (se 1 (by rfl) ⟨1518752, by rfl⟩ : syracuseStep 2025003 = 3037505) B3037505
theorem B2465945 : Blo 2023435 2465945 := bbase (se 2 (by rfl) ⟨924729, by rfl⟩ : syracuseStep 2465945 = 1849459) (by norm_num)
theorem B105213653 : Blo 2023435 105213653 := bstep (se 7 (by rfl) ⟨1232972, by rfl⟩ : syracuseStep 105213653 = 2465945) B2465945
theorem B70142435 : Blo 2023435 70142435 := bstep (se 1 (by rfl) ⟨52606826, by rfl⟩ : syracuseStep 70142435 = 105213653) B105213653
theorem B46761623 : Blo 2023435 46761623 := bstep (se 1 (by rfl) ⟨35071217, by rfl⟩ : syracuseStep 46761623 = 70142435) B70142435
theorem B31174415 : Blo 2023435 31174415 := bstep (se 1 (by rfl) ⟨23380811, by rfl⟩ : syracuseStep 31174415 = 46761623) B46761623
theorem B20782943 : Blo 2023435 20782943 := bstep (se 1 (by rfl) ⟨15587207, by rfl⟩ : syracuseStep 20782943 = 31174415) B31174415
theorem B13855295 : Blo 2023435 13855295 := bstep (se 1 (by rfl) ⟨10391471, by rfl⟩ : syracuseStep 13855295 = 20782943) B20782943
theorem B9236863 : Blo 2023435 9236863 := bstep (se 1 (by rfl) ⟨6927647, by rfl⟩ : syracuseStep 9236863 = 13855295) B13855295
theorem B12315817 : Blo 2023435 12315817 := bstep (se 2 (by rfl) ⟨4618431, by rfl⟩ : syracuseStep 12315817 = 9236863) B9236863
theorem B65684357 : Blo 2023435 65684357 := bstep (se 4 (by rfl) ⟨6157908, by rfl⟩ : syracuseStep 65684357 = 12315817) B12315817
theorem B43789571 : Blo 2023435 43789571 := bstep (se 1 (by rfl) ⟨32842178, by rfl⟩ : syracuseStep 43789571 = 65684357) B65684357
theorem B29193047 : Blo 2023435 29193047 := bstep (se 1 (by rfl) ⟨21894785, by rfl⟩ : syracuseStep 29193047 = 43789571) B43789571
theorem B19462031 : Blo 2023435 19462031 := bstep (se 1 (by rfl) ⟨14596523, by rfl⟩ : syracuseStep 19462031 = 29193047) B29193047
theorem B12974687 : Blo 2023435 12974687 := bstep (se 1 (by rfl) ⟨9731015, by rfl⟩ : syracuseStep 12974687 = 19462031) B19462031
theorem B8649791 : Blo 2023435 8649791 := bstep (se 1 (by rfl) ⟨6487343, by rfl⟩ : syracuseStep 8649791 = 12974687) B12974687
theorem B5766527 : Blo 2023435 5766527 := bstep (se 1 (by rfl) ⟨4324895, by rfl⟩ : syracuseStep 5766527 = 8649791) B8649791
theorem B3844351 : Blo 2023435 3844351 := bstep (se 1 (by rfl) ⟨2883263, by rfl⟩ : syracuseStep 3844351 = 5766527) B5766527
theorem B5125801 : Blo 2023435 5125801 := bstep (se 2 (by rfl) ⟨1922175, by rfl⟩ : syracuseStep 5125801 = 3844351) B3844351
theorem B6834401 : Blo 2023435 6834401 := bstep (se 2 (by rfl) ⟨2562900, by rfl⟩ : syracuseStep 6834401 = 5125801) B5125801
theorem B4556267 : Blo 2023435 4556267 := bstep (se 1 (by rfl) ⟨3417200, by rfl⟩ : syracuseStep 4556267 = 6834401) B6834401
theorem B3037511 : Blo 2023435 3037511 := bstep (se 1 (by rfl) ⟨2278133, by rfl⟩ : syracuseStep 3037511 = 4556267) B4556267
theorem B2025007 : Blo 2023435 2025007 := bstep (se 1 (by rfl) ⟨1518755, by rfl⟩ : syracuseStep 2025007 = 3037511) B3037511
theorem B3037517 : Blo 2023435 3037517 := bbase (se 3 (by rfl) ⟨569534, by rfl⟩ : syracuseStep 3037517 = 1139069) (by norm_num)
theorem B2025011 : Blo 2023435 2025011 := bstep (se 1 (by rfl) ⟨1518758, by rfl⟩ : syracuseStep 2025011 = 3037517) B3037517
theorem B4556285 : Blo 2023435 4556285 := bbase (se 3 (by rfl) ⟨854303, by rfl⟩ : syracuseStep 4556285 = 1708607) (by norm_num)
theorem B3037523 : Blo 2023435 3037523 := bstep (se 1 (by rfl) ⟨2278142, by rfl⟩ : syracuseStep 3037523 = 4556285) B4556285
theorem B2025015 : Blo 2023435 2025015 := bstep (se 1 (by rfl) ⟨1518761, by rfl⟩ : syracuseStep 2025015 = 3037523) B3037523
theorem B3417221 : Blo 2023435 3417221 := bbase (se 4 (by rfl) ⟨320364, by rfl⟩ : syracuseStep 3417221 = 640729) (by norm_num)
theorem B2278147 : Blo 2023435 2278147 := bstep (se 1 (by rfl) ⟨1708610, by rfl⟩ : syracuseStep 2278147 = 3417221) B3417221
theorem B3037529 : Blo 2023435 3037529 := bstep (se 2 (by rfl) ⟨1139073, by rfl⟩ : syracuseStep 3037529 = 2278147) B2278147
theorem B2025019 : Blo 2023435 2025019 := bstep (se 1 (by rfl) ⟨1518764, by rfl⟩ : syracuseStep 2025019 = 3037529) B3037529
theorem B15377525 : Blo 2023435 15377525 := bbase (se 5 (by rfl) ⟨720821, by rfl⟩ : syracuseStep 15377525 = 1441643) (by norm_num)
theorem B10251683 : Blo 2023435 10251683 := bstep (se 1 (by rfl) ⟨7688762, by rfl⟩ : syracuseStep 10251683 = 15377525) B15377525
theorem B6834455 : Blo 2023435 6834455 := bstep (se 1 (by rfl) ⟨5125841, by rfl⟩ : syracuseStep 6834455 = 10251683) B10251683
theorem B4556303 : Blo 2023435 4556303 := bstep (se 1 (by rfl) ⟨3417227, by rfl⟩ : syracuseStep 4556303 = 6834455) B6834455
theorem B3037535 : Blo 2023435 3037535 := bstep (se 1 (by rfl) ⟨2278151, by rfl⟩ : syracuseStep 3037535 = 4556303) B4556303
theorem B2025023 : Blo 2023435 2025023 := bstep (se 1 (by rfl) ⟨1518767, by rfl⟩ : syracuseStep 2025023 = 3037535) B3037535
theorem B3037541 : Blo 2023435 3037541 := bbase (se 4 (by rfl) ⟨284769, by rfl⟩ : syracuseStep 3037541 = 569539) (by norm_num)
theorem B2025027 : Blo 2023435 2025027 := bstep (se 1 (by rfl) ⟨1518770, by rfl⟩ : syracuseStep 2025027 = 3037541) B3037541
theorem B3844397 : Blo 2023435 3844397 := bbase (se 3 (by rfl) ⟨720824, by rfl⟩ : syracuseStep 3844397 = 1441649) (by norm_num)
theorem B2562931 : Blo 2023435 2562931 := bstep (se 1 (by rfl) ⟨1922198, by rfl⟩ : syracuseStep 2562931 = 3844397) B3844397
theorem B3417241 : Blo 2023435 3417241 := bstep (se 2 (by rfl) ⟨1281465, by rfl⟩ : syracuseStep 3417241 = 2562931) B2562931
theorem B4556321 : Blo 2023435 4556321 := bstep (se 2 (by rfl) ⟨1708620, by rfl⟩ : syracuseStep 4556321 = 3417241) B3417241
theorem B3037547 : Blo 2023435 3037547 := bstep (se 1 (by rfl) ⟨2278160, by rfl⟩ : syracuseStep 3037547 = 4556321) B4556321
theorem B2025031 : Blo 2023435 2025031 := bstep (se 1 (by rfl) ⟨1518773, by rfl⟩ : syracuseStep 2025031 = 3037547) B3037547
theorem B2278165 : Blo 2023435 2278165 := bbase (se 6 (by rfl) ⟨53394, by rfl⟩ : syracuseStep 2278165 = 106789) (by norm_num)
theorem B3037553 : Blo 2023435 3037553 := bstep (se 2 (by rfl) ⟨1139082, by rfl⟩ : syracuseStep 3037553 = 2278165) B2278165
theorem B2025035 : Blo 2023435 2025035 := bstep (se 1 (by rfl) ⟨1518776, by rfl⟩ : syracuseStep 2025035 = 3037553) B3037553
theorem B2562941 : Blo 2023435 2562941 := bbase (se 3 (by rfl) ⟨480551, by rfl⟩ : syracuseStep 2562941 = 961103) (by norm_num)
theorem B6834509 : Blo 2023435 6834509 := bstep (se 3 (by rfl) ⟨1281470, by rfl⟩ : syracuseStep 6834509 = 2562941) B2562941
theorem B4556339 : Blo 2023435 4556339 := bstep (se 1 (by rfl) ⟨3417254, by rfl⟩ : syracuseStep 4556339 = 6834509) B6834509
theorem B3037559 : Blo 2023435 3037559 := bstep (se 1 (by rfl) ⟨2278169, by rfl⟩ : syracuseStep 3037559 = 4556339) B4556339
theorem B2025039 : Blo 2023435 2025039 := bstep (se 1 (by rfl) ⟨1518779, by rfl⟩ : syracuseStep 2025039 = 3037559) B3037559
theorem B3037565 : Blo 2023435 3037565 := bbase (se 3 (by rfl) ⟨569543, by rfl⟩ : syracuseStep 3037565 = 1139087) (by norm_num)
theorem B2025043 : Blo 2023435 2025043 := bstep (se 1 (by rfl) ⟨1518782, by rfl⟩ : syracuseStep 2025043 = 3037565) B3037565
theorem B4556357 : Blo 2023435 4556357 := bbase (se 4 (by rfl) ⟨427158, by rfl⟩ : syracuseStep 4556357 = 854317) (by norm_num)
theorem B3037571 : Blo 2023435 3037571 := bstep (se 1 (by rfl) ⟨2278178, by rfl⟩ : syracuseStep 3037571 = 4556357) B4556357
theorem B2025047 : Blo 2023435 2025047 := bstep (se 1 (by rfl) ⟨1518785, by rfl⟩ : syracuseStep 2025047 = 3037571) B3037571
theorem B3463901 : Blo 2023435 3463901 := bbase (se 3 (by rfl) ⟨649481, by rfl⟩ : syracuseStep 3463901 = 1298963) (by norm_num)
theorem B2309267 : Blo 2023435 2309267 := bstep (se 1 (by rfl) ⟨1731950, by rfl⟩ : syracuseStep 2309267 = 3463901) B3463901
theorem B6158045 : Blo 2023435 6158045 := bstep (se 3 (by rfl) ⟨1154633, by rfl⟩ : syracuseStep 6158045 = 2309267) B2309267
theorem B16421453 : Blo 2023435 16421453 := bstep (se 3 (by rfl) ⟨3079022, by rfl⟩ : syracuseStep 16421453 = 6158045) B6158045
theorem B10947635 : Blo 2023435 10947635 := bstep (se 1 (by rfl) ⟨8210726, by rfl⟩ : syracuseStep 10947635 = 16421453) B16421453
theorem B7298423 : Blo 2023435 7298423 := bstep (se 1 (by rfl) ⟨5473817, by rfl⟩ : syracuseStep 7298423 = 10947635) B10947635
theorem B4865615 : Blo 2023435 4865615 := bstep (se 1 (by rfl) ⟨3649211, by rfl⟩ : syracuseStep 4865615 = 7298423) B7298423
theorem B3243743 : Blo 2023435 3243743 := bstep (se 1 (by rfl) ⟨2432807, by rfl⟩ : syracuseStep 3243743 = 4865615) B4865615
theorem B2162495 : Blo 2023435 2162495 := bstep (se 1 (by rfl) ⟨1621871, by rfl⟩ : syracuseStep 2162495 = 3243743) B3243743
theorem B5766653 : Blo 2023435 5766653 := bstep (se 3 (by rfl) ⟨1081247, by rfl⟩ : syracuseStep 5766653 = 2162495) B2162495
theorem B3844435 : Blo 2023435 3844435 := bstep (se 1 (by rfl) ⟨2883326, by rfl⟩ : syracuseStep 3844435 = 5766653) B5766653
theorem B5125913 : Blo 2023435 5125913 := bstep (se 2 (by rfl) ⟨1922217, by rfl⟩ : syracuseStep 5125913 = 3844435) B3844435
theorem B3417275 : Blo 2023435 3417275 := bstep (se 1 (by rfl) ⟨2562956, by rfl⟩ : syracuseStep 3417275 = 5125913) B5125913
theorem B2278183 : Blo 2023435 2278183 := bstep (se 1 (by rfl) ⟨1708637, by rfl⟩ : syracuseStep 2278183 = 3417275) B3417275
theorem B3037577 : Blo 2023435 3037577 := bstep (se 2 (by rfl) ⟨1139091, by rfl⟩ : syracuseStep 3037577 = 2278183) B2278183
theorem B2025051 : Blo 2023435 2025051 := bstep (se 1 (by rfl) ⟨1518788, by rfl⟩ : syracuseStep 2025051 = 3037577) B3037577
theorem B10251845 : Blo 2023435 10251845 := bbase (se 4 (by rfl) ⟨961110, by rfl⟩ : syracuseStep 10251845 = 1922221) (by norm_num)
theorem B6834563 : Blo 2023435 6834563 := bstep (se 1 (by rfl) ⟨5125922, by rfl⟩ : syracuseStep 6834563 = 10251845) B10251845
theorem B4556375 : Blo 2023435 4556375 := bstep (se 1 (by rfl) ⟨3417281, by rfl⟩ : syracuseStep 4556375 = 6834563) B6834563
theorem B3037583 : Blo 2023435 3037583 := bstep (se 1 (by rfl) ⟨2278187, by rfl⟩ : syracuseStep 3037583 = 4556375) B4556375
theorem B2025055 : Blo 2023435 2025055 := bstep (se 1 (by rfl) ⟨1518791, by rfl⟩ : syracuseStep 2025055 = 3037583) B3037583
theorem B3037589 : Blo 2023435 3037589 := bbase (se 6 (by rfl) ⟨71193, by rfl⟩ : syracuseStep 3037589 = 142387) (by norm_num)
theorem B2025059 : Blo 2023435 2025059 := bstep (se 1 (by rfl) ⟨1518794, by rfl⟩ : syracuseStep 2025059 = 3037589) B3037589
theorem B9731285 : Blo 2023435 9731285 := bbase (se 7 (by rfl) ⟨114038, by rfl⟩ : syracuseStep 9731285 = 228077) (by norm_num)
theorem B6487523 : Blo 2023435 6487523 := bstep (se 1 (by rfl) ⟨4865642, by rfl⟩ : syracuseStep 6487523 = 9731285) B9731285
theorem B4325015 : Blo 2023435 4325015 := bstep (se 1 (by rfl) ⟨3243761, by rfl⟩ : syracuseStep 4325015 = 6487523) B6487523
theorem B11533373 : Blo 2023435 11533373 := bstep (se 3 (by rfl) ⟨2162507, by rfl⟩ : syracuseStep 11533373 = 4325015) B4325015
theorem B7688915 : Blo 2023435 7688915 := bstep (se 1 (by rfl) ⟨5766686, by rfl⟩ : syracuseStep 7688915 = 11533373) B11533373
theorem B5125943 : Blo 2023435 5125943 := bstep (se 1 (by rfl) ⟨3844457, by rfl⟩ : syracuseStep 5125943 = 7688915) B7688915
theorem B3417295 : Blo 2023435 3417295 := bstep (se 1 (by rfl) ⟨2562971, by rfl⟩ : syracuseStep 3417295 = 5125943) B5125943
theorem B4556393 : Blo 2023435 4556393 := bstep (se 2 (by rfl) ⟨1708647, by rfl⟩ : syracuseStep 4556393 = 3417295) B3417295
theorem B3037595 : Blo 2023435 3037595 := bstep (se 1 (by rfl) ⟨2278196, by rfl⟩ : syracuseStep 3037595 = 4556393) B4556393
theorem B2025063 : Blo 2023435 2025063 := bstep (se 1 (by rfl) ⟨1518797, by rfl⟩ : syracuseStep 2025063 = 3037595) B3037595
theorem B2278201 : Blo 2023435 2278201 := bbase (se 2 (by rfl) ⟨854325, by rfl⟩ : syracuseStep 2278201 = 1708651) (by norm_num)
theorem B3037601 : Blo 2023435 3037601 := bstep (se 2 (by rfl) ⟨1139100, by rfl⟩ : syracuseStep 3037601 = 2278201) B2278201
theorem B2025067 : Blo 2023435 2025067 := bstep (se 1 (by rfl) ⟨1518800, by rfl⟩ : syracuseStep 2025067 = 3037601) B3037601
theorem B5766709 : Blo 2023435 5766709 := bbase (se 5 (by rfl) ⟨270314, by rfl⟩ : syracuseStep 5766709 = 540629) (by norm_num)
theorem B7688945 : Blo 2023435 7688945 := bstep (se 2 (by rfl) ⟨2883354, by rfl⟩ : syracuseStep 7688945 = 5766709) B5766709
theorem B5125963 : Blo 2023435 5125963 := bstep (se 1 (by rfl) ⟨3844472, by rfl⟩ : syracuseStep 5125963 = 7688945) B7688945
theorem B6834617 : Blo 2023435 6834617 := bstep (se 2 (by rfl) ⟨2562981, by rfl⟩ : syracuseStep 6834617 = 5125963) B5125963
theorem B4556411 : Blo 2023435 4556411 := bstep (se 1 (by rfl) ⟨3417308, by rfl⟩ : syracuseStep 4556411 = 6834617) B6834617
theorem B3037607 : Blo 2023435 3037607 := bstep (se 1 (by rfl) ⟨2278205, by rfl⟩ : syracuseStep 3037607 = 4556411) B4556411
theorem B2025071 : Blo 2023435 2025071 := bstep (se 1 (by rfl) ⟨1518803, by rfl⟩ : syracuseStep 2025071 = 3037607) B3037607
theorem B3037613 : Blo 2023435 3037613 := bbase (se 3 (by rfl) ⟨569552, by rfl⟩ : syracuseStep 3037613 = 1139105) (by norm_num)
theorem B2025075 : Blo 2023435 2025075 := bstep (se 1 (by rfl) ⟨1518806, by rfl⟩ : syracuseStep 2025075 = 3037613) B3037613
theorem B4556429 : Blo 2023435 4556429 := bbase (se 3 (by rfl) ⟨854330, by rfl⟩ : syracuseStep 4556429 = 1708661) (by norm_num)
theorem B3037619 : Blo 2023435 3037619 := bstep (se 1 (by rfl) ⟨2278214, by rfl⟩ : syracuseStep 3037619 = 4556429) B4556429
theorem B2025079 : Blo 2023435 2025079 := bstep (se 1 (by rfl) ⟨1518809, by rfl⟩ : syracuseStep 2025079 = 3037619) B3037619
theorem B2562997 : Blo 2023435 2562997 := bbase (se 5 (by rfl) ⟨120140, by rfl⟩ : syracuseStep 2562997 = 240281) (by norm_num)
theorem B3417329 : Blo 2023435 3417329 := bstep (se 2 (by rfl) ⟨1281498, by rfl⟩ : syracuseStep 3417329 = 2562997) B2562997
theorem B2278219 : Blo 2023435 2278219 := bstep (se 1 (by rfl) ⟨1708664, by rfl⟩ : syracuseStep 2278219 = 3417329) B3417329
theorem B3037625 : Blo 2023435 3037625 := bstep (se 2 (by rfl) ⟨1139109, by rfl⟩ : syracuseStep 3037625 = 2278219) B2278219
theorem B2025083 : Blo 2023435 2025083 := bstep (se 1 (by rfl) ⟨1518812, by rfl⟩ : syracuseStep 2025083 = 3037625) B3037625
theorem B37453013 : Blo 2023435 37453013 := bbase (se 7 (by rfl) ⟨438902, by rfl⟩ : syracuseStep 37453013 = 877805) (by norm_num)
theorem B24968675 : Blo 2023435 24968675 := bstep (se 1 (by rfl) ⟨18726506, by rfl⟩ : syracuseStep 24968675 = 37453013) B37453013
theorem B16645783 : Blo 2023435 16645783 := bstep (se 1 (by rfl) ⟨12484337, by rfl⟩ : syracuseStep 16645783 = 24968675) B24968675
theorem B22194377 : Blo 2023435 22194377 := bstep (se 2 (by rfl) ⟨8322891, by rfl⟩ : syracuseStep 22194377 = 16645783) B16645783
theorem B14796251 : Blo 2023435 14796251 := bstep (se 1 (by rfl) ⟨11097188, by rfl⟩ : syracuseStep 14796251 = 22194377) B22194377
theorem B157826677 : Blo 2023435 157826677 := bstep (se 5 (by rfl) ⟨7398125, by rfl⟩ : syracuseStep 157826677 = 14796251) B14796251
theorem B210435569 : Blo 2023435 210435569 := bstep (se 2 (by rfl) ⟨78913338, by rfl⟩ : syracuseStep 210435569 = 157826677) B157826677
theorem B140290379 : Blo 2023435 140290379 := bstep (se 1 (by rfl) ⟨105217784, by rfl⟩ : syracuseStep 140290379 = 210435569) B210435569
theorem B93526919 : Blo 2023435 93526919 := bstep (se 1 (by rfl) ⟨70145189, by rfl⟩ : syracuseStep 93526919 = 140290379) B140290379
theorem B62351279 : Blo 2023435 62351279 := bstep (se 1 (by rfl) ⟨46763459, by rfl⟩ : syracuseStep 62351279 = 93526919) B93526919
theorem B41567519 : Blo 2023435 41567519 := bstep (se 1 (by rfl) ⟨31175639, by rfl⟩ : syracuseStep 41567519 = 62351279) B62351279
theorem B27711679 : Blo 2023435 27711679 := bstep (se 1 (by rfl) ⟨20783759, by rfl⟩ : syracuseStep 27711679 = 41567519) B41567519
theorem B36948905 : Blo 2023435 36948905 := bstep (se 2 (by rfl) ⟨13855839, by rfl⟩ : syracuseStep 36948905 = 27711679) B27711679
theorem B24632603 : Blo 2023435 24632603 := bstep (se 1 (by rfl) ⟨18474452, by rfl⟩ : syracuseStep 24632603 = 36948905) B36948905
theorem B16421735 : Blo 2023435 16421735 := bstep (se 1 (by rfl) ⟨12316301, by rfl⟩ : syracuseStep 16421735 = 24632603) B24632603
theorem B43791293 : Blo 2023435 43791293 := bstep (se 3 (by rfl) ⟨8210867, by rfl⟩ : syracuseStep 43791293 = 16421735) B16421735
theorem B29194195 : Blo 2023435 29194195 := bstep (se 1 (by rfl) ⟨21895646, by rfl⟩ : syracuseStep 29194195 = 43791293) B43791293
theorem B38925593 : Blo 2023435 38925593 := bstep (se 2 (by rfl) ⟨14597097, by rfl⟩ : syracuseStep 38925593 = 29194195) B29194195
theorem B25950395 : Blo 2023435 25950395 := bstep (se 1 (by rfl) ⟨19462796, by rfl⟩ : syracuseStep 25950395 = 38925593) B38925593
theorem B17300263 : Blo 2023435 17300263 := bstep (se 1 (by rfl) ⟨12975197, by rfl⟩ : syracuseStep 17300263 = 25950395) B25950395
theorem B23067017 : Blo 2023435 23067017 := bstep (se 2 (by rfl) ⟨8650131, by rfl⟩ : syracuseStep 23067017 = 17300263) B17300263
theorem B15378011 : Blo 2023435 15378011 := bstep (se 1 (by rfl) ⟨11533508, by rfl⟩ : syracuseStep 15378011 = 23067017) B23067017
theorem B10252007 : Blo 2023435 10252007 := bstep (se 1 (by rfl) ⟨7689005, by rfl⟩ : syracuseStep 10252007 = 15378011) B15378011
theorem B6834671 : Blo 2023435 6834671 := bstep (se 1 (by rfl) ⟨5126003, by rfl⟩ : syracuseStep 6834671 = 10252007) B10252007
theorem B4556447 : Blo 2023435 4556447 := bstep (se 1 (by rfl) ⟨3417335, by rfl⟩ : syracuseStep 4556447 = 6834671) B6834671
theorem B3037631 : Blo 2023435 3037631 := bstep (se 1 (by rfl) ⟨2278223, by rfl⟩ : syracuseStep 3037631 = 4556447) B4556447
theorem B2025087 : Blo 2023435 2025087 := bstep (se 1 (by rfl) ⟨1518815, by rfl⟩ : syracuseStep 2025087 = 3037631) B3037631
theorem B3037637 : Blo 2023435 3037637 := bbase (se 4 (by rfl) ⟨284778, by rfl⟩ : syracuseStep 3037637 = 569557) (by norm_num)
theorem B2025091 : Blo 2023435 2025091 := bstep (se 1 (by rfl) ⟨1518818, by rfl⟩ : syracuseStep 2025091 = 3037637) B3037637
theorem B3417349 : Blo 2023435 3417349 := bbase (se 4 (by rfl) ⟨320376, by rfl⟩ : syracuseStep 3417349 = 640753) (by norm_num)
theorem B4556465 : Blo 2023435 4556465 := bstep (se 2 (by rfl) ⟨1708674, by rfl⟩ : syracuseStep 4556465 = 3417349) B3417349
theorem B3037643 : Blo 2023435 3037643 := bstep (se 1 (by rfl) ⟨2278232, by rfl⟩ : syracuseStep 3037643 = 4556465) B4556465
theorem B2025095 : Blo 2023435 2025095 := bstep (se 1 (by rfl) ⟨1518821, by rfl⟩ : syracuseStep 2025095 = 3037643) B3037643
theorem B2278237 : Blo 2023435 2278237 := bbase (se 3 (by rfl) ⟨427169, by rfl⟩ : syracuseStep 2278237 = 854339) (by norm_num)
theorem B3037649 : Blo 2023435 3037649 := bstep (se 2 (by rfl) ⟨1139118, by rfl⟩ : syracuseStep 3037649 = 2278237) B2278237
theorem B2025099 : Blo 2023435 2025099 := bstep (se 1 (by rfl) ⟨1518824, by rfl⟩ : syracuseStep 2025099 = 3037649) B3037649
theorem B6834725 : Blo 2023435 6834725 := bbase (se 4 (by rfl) ⟨640755, by rfl⟩ : syracuseStep 6834725 = 1281511) (by norm_num)
theorem B4556483 : Blo 2023435 4556483 := bstep (se 1 (by rfl) ⟨3417362, by rfl⟩ : syracuseStep 4556483 = 6834725) B6834725
theorem B3037655 : Blo 2023435 3037655 := bstep (se 1 (by rfl) ⟨2278241, by rfl⟩ : syracuseStep 3037655 = 4556483) B4556483
theorem B2025103 : Blo 2023435 2025103 := bstep (se 1 (by rfl) ⟨1518827, by rfl⟩ : syracuseStep 2025103 = 3037655) B3037655
theorem B3037661 : Blo 2023435 3037661 := bbase (se 3 (by rfl) ⟨569561, by rfl⟩ : syracuseStep 3037661 = 1139123) (by norm_num)
theorem B2025107 : Blo 2023435 2025107 := bstep (se 1 (by rfl) ⟨1518830, by rfl⟩ : syracuseStep 2025107 = 3037661) B3037661
theorem B4556501 : Blo 2023435 4556501 := bbase (se 7 (by rfl) ⟨53396, by rfl⟩ : syracuseStep 4556501 = 106793) (by norm_num)
theorem B3037667 : Blo 2023435 3037667 := bstep (se 1 (by rfl) ⟨2278250, by rfl⟩ : syracuseStep 3037667 = 4556501) B4556501
theorem B2025111 : Blo 2023435 2025111 := bstep (se 1 (by rfl) ⟨1518833, by rfl⟩ : syracuseStep 2025111 = 3037667) B3037667
theorem B3243845 : Blo 2023435 3243845 := bbase (se 4 (by rfl) ⟨304110, by rfl⟩ : syracuseStep 3243845 = 608221) (by norm_num)
theorem B8650253 : Blo 2023435 8650253 := bstep (se 3 (by rfl) ⟨1621922, by rfl⟩ : syracuseStep 8650253 = 3243845) B3243845
theorem B5766835 : Blo 2023435 5766835 := bstep (se 1 (by rfl) ⟨4325126, by rfl⟩ : syracuseStep 5766835 = 8650253) B8650253
theorem B7689113 : Blo 2023435 7689113 := bstep (se 2 (by rfl) ⟨2883417, by rfl⟩ : syracuseStep 7689113 = 5766835) B5766835
theorem B5126075 : Blo 2023435 5126075 := bstep (se 1 (by rfl) ⟨3844556, by rfl⟩ : syracuseStep 5126075 = 7689113) B7689113
theorem B3417383 : Blo 2023435 3417383 := bstep (se 1 (by rfl) ⟨2563037, by rfl⟩ : syracuseStep 3417383 = 5126075) B5126075
theorem B2278255 : Blo 2023435 2278255 := bstep (se 1 (by rfl) ⟨1708691, by rfl⟩ : syracuseStep 2278255 = 3417383) B3417383
theorem B3037673 : Blo 2023435 3037673 := bstep (se 2 (by rfl) ⟨1139127, by rfl⟩ : syracuseStep 3037673 = 2278255) B2278255
theorem B2025115 : Blo 2023435 2025115 := bstep (se 1 (by rfl) ⟨1518836, by rfl⟩ : syracuseStep 2025115 = 3037673) B3037673
theorem B3003061 : Blo 2023435 3003061 := bbase (se 5 (by rfl) ⟨140768, by rfl⟩ : syracuseStep 3003061 = 281537) (by norm_num)
theorem B4004081 : Blo 2023435 4004081 := bstep (se 2 (by rfl) ⟨1501530, by rfl⟩ : syracuseStep 4004081 = 3003061) B3003061
theorem B2669387 : Blo 2023435 2669387 := bstep (se 1 (by rfl) ⟨2002040, by rfl⟩ : syracuseStep 2669387 = 4004081) B4004081
theorem B7118365 : Blo 2023435 7118365 := bstep (se 3 (by rfl) ⟨1334693, by rfl⟩ : syracuseStep 7118365 = 2669387) B2669387
theorem B9491153 : Blo 2023435 9491153 := bstep (se 2 (by rfl) ⟨3559182, by rfl⟩ : syracuseStep 9491153 = 7118365) B7118365
theorem B25309741 : Blo 2023435 25309741 := bstep (se 3 (by rfl) ⟨4745576, by rfl⟩ : syracuseStep 25309741 = 9491153) B9491153
theorem B33746321 : Blo 2023435 33746321 := bstep (se 2 (by rfl) ⟨12654870, by rfl⟩ : syracuseStep 33746321 = 25309741) B25309741
theorem B22497547 : Blo 2023435 22497547 := bstep (se 1 (by rfl) ⟨16873160, by rfl⟩ : syracuseStep 22497547 = 33746321) B33746321
theorem B29996729 : Blo 2023435 29996729 := bstep (se 2 (by rfl) ⟨11248773, by rfl⟩ : syracuseStep 29996729 = 22497547) B22497547
theorem B19997819 : Blo 2023435 19997819 := bstep (se 1 (by rfl) ⟨14998364, by rfl⟩ : syracuseStep 19997819 = 29996729) B29996729
theorem B13331879 : Blo 2023435 13331879 := bstep (se 1 (by rfl) ⟨9998909, by rfl⟩ : syracuseStep 13331879 = 19997819) B19997819
theorem B8887919 : Blo 2023435 8887919 := bstep (se 1 (by rfl) ⟨6665939, by rfl⟩ : syracuseStep 8887919 = 13331879) B13331879
theorem B94804469 : Blo 2023435 94804469 := bstep (se 5 (by rfl) ⟨4443959, by rfl⟩ : syracuseStep 94804469 = 8887919) B8887919
theorem B63202979 : Blo 2023435 63202979 := bstep (se 1 (by rfl) ⟨47402234, by rfl⟩ : syracuseStep 63202979 = 94804469) B94804469
theorem B42135319 : Blo 2023435 42135319 := bstep (se 1 (by rfl) ⟨31601489, by rfl⟩ : syracuseStep 42135319 = 63202979) B63202979
theorem B224721701 : Blo 2023435 224721701 := bstep (se 4 (by rfl) ⟨21067659, by rfl⟩ : syracuseStep 224721701 = 42135319) B42135319
theorem B149814467 : Blo 2023435 149814467 := bstep (se 1 (by rfl) ⟨112360850, by rfl⟩ : syracuseStep 149814467 = 224721701) B224721701
theorem B99876311 : Blo 2023435 99876311 := bstep (se 1 (by rfl) ⟨74907233, by rfl⟩ : syracuseStep 99876311 = 149814467) B149814467
theorem B66584207 : Blo 2023435 66584207 := bstep (se 1 (by rfl) ⟨49938155, by rfl⟩ : syracuseStep 66584207 = 99876311) B99876311
theorem B44389471 : Blo 2023435 44389471 := bstep (se 1 (by rfl) ⟨33292103, by rfl⟩ : syracuseStep 44389471 = 66584207) B66584207
theorem B59185961 : Blo 2023435 59185961 := bstep (se 2 (by rfl) ⟨22194735, by rfl⟩ : syracuseStep 59185961 = 44389471) B44389471
theorem B39457307 : Blo 2023435 39457307 := bstep (se 1 (by rfl) ⟨29592980, by rfl⟩ : syracuseStep 39457307 = 59185961) B59185961
theorem B26304871 : Blo 2023435 26304871 := bstep (se 1 (by rfl) ⟨19728653, by rfl⟩ : syracuseStep 26304871 = 39457307) B39457307
theorem B35073161 : Blo 2023435 35073161 := bstep (se 2 (by rfl) ⟨13152435, by rfl⟩ : syracuseStep 35073161 = 26304871) B26304871
theorem B23382107 : Blo 2023435 23382107 := bstep (se 1 (by rfl) ⟨17536580, by rfl⟩ : syracuseStep 23382107 = 35073161) B35073161
theorem B15588071 : Blo 2023435 15588071 := bstep (se 1 (by rfl) ⟨11691053, by rfl⟩ : syracuseStep 15588071 = 23382107) B23382107
theorem B10392047 : Blo 2023435 10392047 := bstep (se 1 (by rfl) ⟨7794035, by rfl⟩ : syracuseStep 10392047 = 15588071) B15588071
theorem B6928031 : Blo 2023435 6928031 := bstep (se 1 (by rfl) ⟨5196023, by rfl⟩ : syracuseStep 6928031 = 10392047) B10392047
theorem B4618687 : Blo 2023435 4618687 := bstep (se 1 (by rfl) ⟨3464015, by rfl⟩ : syracuseStep 4618687 = 6928031) B6928031
theorem B6158249 : Blo 2023435 6158249 := bstep (se 2 (by rfl) ⟨2309343, by rfl⟩ : syracuseStep 6158249 = 4618687) B4618687
theorem B4105499 : Blo 2023435 4105499 := bstep (se 1 (by rfl) ⟨3079124, by rfl⟩ : syracuseStep 4105499 = 6158249) B6158249
theorem B10947997 : Blo 2023435 10947997 := bstep (se 3 (by rfl) ⟨2052749, by rfl⟩ : syracuseStep 10947997 = 4105499) B4105499
theorem B14597329 : Blo 2023435 14597329 := bstep (se 2 (by rfl) ⟨5473998, by rfl⟩ : syracuseStep 14597329 = 10947997) B10947997
theorem B19463105 : Blo 2023435 19463105 := bstep (se 2 (by rfl) ⟨7298664, by rfl⟩ : syracuseStep 19463105 = 14597329) B14597329
theorem B12975403 : Blo 2023435 12975403 := bstep (se 1 (by rfl) ⟨9731552, by rfl⟩ : syracuseStep 12975403 = 19463105) B19463105
theorem B17300537 : Blo 2023435 17300537 := bstep (se 2 (by rfl) ⟨6487701, by rfl⟩ : syracuseStep 17300537 = 12975403) B12975403
theorem B11533691 : Blo 2023435 11533691 := bstep (se 1 (by rfl) ⟨8650268, by rfl⟩ : syracuseStep 11533691 = 17300537) B17300537
theorem B7689127 : Blo 2023435 7689127 := bstep (se 1 (by rfl) ⟨5766845, by rfl⟩ : syracuseStep 7689127 = 11533691) B11533691
theorem B10252169 : Blo 2023435 10252169 := bstep (se 2 (by rfl) ⟨3844563, by rfl⟩ : syracuseStep 10252169 = 7689127) B7689127
theorem B6834779 : Blo 2023435 6834779 := bstep (se 1 (by rfl) ⟨5126084, by rfl⟩ : syracuseStep 6834779 = 10252169) B10252169
theorem B4556519 : Blo 2023435 4556519 := bstep (se 1 (by rfl) ⟨3417389, by rfl⟩ : syracuseStep 4556519 = 6834779) B6834779
theorem B3037679 : Blo 2023435 3037679 := bstep (se 1 (by rfl) ⟨2278259, by rfl⟩ : syracuseStep 3037679 = 4556519) B4556519
theorem B2025119 : Blo 2023435 2025119 := bstep (se 1 (by rfl) ⟨1518839, by rfl⟩ : syracuseStep 2025119 = 3037679) B3037679
theorem B3037685 : Blo 2023435 3037685 := bbase (se 5 (by rfl) ⟨142391, by rfl⟩ : syracuseStep 3037685 = 284783) (by norm_num)
theorem B2025123 : Blo 2023435 2025123 := bstep (se 1 (by rfl) ⟨1518842, by rfl⟩ : syracuseStep 2025123 = 3037685) B3037685
theorem B5766869 : Blo 2023435 5766869 := bbase (se 7 (by rfl) ⟨67580, by rfl⟩ : syracuseStep 5766869 = 135161) (by norm_num)
theorem B3844579 : Blo 2023435 3844579 := bstep (se 1 (by rfl) ⟨2883434, by rfl⟩ : syracuseStep 3844579 = 5766869) B5766869
theorem B5126105 : Blo 2023435 5126105 := bstep (se 2 (by rfl) ⟨1922289, by rfl⟩ : syracuseStep 5126105 = 3844579) B3844579
theorem B3417403 : Blo 2023435 3417403 := bstep (se 1 (by rfl) ⟨2563052, by rfl⟩ : syracuseStep 3417403 = 5126105) B5126105
theorem B4556537 : Blo 2023435 4556537 := bstep (se 2 (by rfl) ⟨1708701, by rfl⟩ : syracuseStep 4556537 = 3417403) B3417403
theorem B3037691 : Blo 2023435 3037691 := bstep (se 1 (by rfl) ⟨2278268, by rfl⟩ : syracuseStep 3037691 = 4556537) B4556537
theorem B2025127 : Blo 2023435 2025127 := bstep (se 1 (by rfl) ⟨1518845, by rfl⟩ : syracuseStep 2025127 = 3037691) B3037691
theorem B2278273 : Blo 2023435 2278273 := bbase (se 2 (by rfl) ⟨854352, by rfl⟩ : syracuseStep 2278273 = 1708705) (by norm_num)
theorem B3037697 : Blo 2023435 3037697 := bstep (se 2 (by rfl) ⟨1139136, by rfl⟩ : syracuseStep 3037697 = 2278273) B2278273
theorem B2025131 : Blo 2023435 2025131 := bstep (se 1 (by rfl) ⟨1518848, by rfl⟩ : syracuseStep 2025131 = 3037697) B3037697
theorem B5126125 : Blo 2023435 5126125 := bbase (se 3 (by rfl) ⟨961148, by rfl⟩ : syracuseStep 5126125 = 1922297) (by norm_num)
theorem B6834833 : Blo 2023435 6834833 := bstep (se 2 (by rfl) ⟨2563062, by rfl⟩ : syracuseStep 6834833 = 5126125) B5126125
theorem B4556555 : Blo 2023435 4556555 := bstep (se 1 (by rfl) ⟨3417416, by rfl⟩ : syracuseStep 4556555 = 6834833) B6834833
theorem B3037703 : Blo 2023435 3037703 := bstep (se 1 (by rfl) ⟨2278277, by rfl⟩ : syracuseStep 3037703 = 4556555) B4556555
theorem B2025135 : Blo 2023435 2025135 := bstep (se 1 (by rfl) ⟨1518851, by rfl⟩ : syracuseStep 2025135 = 3037703) B3037703
theorem B3037709 : Blo 2023435 3037709 := bbase (se 3 (by rfl) ⟨569570, by rfl⟩ : syracuseStep 3037709 = 1139141) (by norm_num)
theorem B2025139 : Blo 2023435 2025139 := bstep (se 1 (by rfl) ⟨1518854, by rfl⟩ : syracuseStep 2025139 = 3037709) B3037709
theorem B4556573 : Blo 2023435 4556573 := bbase (se 3 (by rfl) ⟨854357, by rfl⟩ : syracuseStep 4556573 = 1708715) (by norm_num)
theorem B3037715 : Blo 2023435 3037715 := bstep (se 1 (by rfl) ⟨2278286, by rfl⟩ : syracuseStep 3037715 = 4556573) B4556573
theorem B2025143 : Blo 2023435 2025143 := bstep (se 1 (by rfl) ⟨1518857, by rfl⟩ : syracuseStep 2025143 = 3037715) B3037715
theorem B3417437 : Blo 2023435 3417437 := bbase (se 3 (by rfl) ⟨640769, by rfl⟩ : syracuseStep 3417437 = 1281539) (by norm_num)
theorem B2278291 : Blo 2023435 2278291 := bstep (se 1 (by rfl) ⟨1708718, by rfl⟩ : syracuseStep 2278291 = 3417437) B3417437
theorem B3037721 : Blo 2023435 3037721 := bstep (se 2 (by rfl) ⟨1139145, by rfl⟩ : syracuseStep 3037721 = 2278291) B2278291
theorem B2025147 : Blo 2023435 2025147 := bstep (se 1 (by rfl) ⟨1518860, by rfl⟩ : syracuseStep 2025147 = 3037721) B3037721
theorem B8650405 : Blo 2023435 8650405 := bbase (se 4 (by rfl) ⟨810975, by rfl⟩ : syracuseStep 8650405 = 1621951) (by norm_num)
theorem B11533873 : Blo 2023435 11533873 := bstep (se 2 (by rfl) ⟨4325202, by rfl⟩ : syracuseStep 11533873 = 8650405) B8650405
theorem B15378497 : Blo 2023435 15378497 := bstep (se 2 (by rfl) ⟨5766936, by rfl⟩ : syracuseStep 15378497 = 11533873) B11533873
theorem B10252331 : Blo 2023435 10252331 := bstep (se 1 (by rfl) ⟨7689248, by rfl⟩ : syracuseStep 10252331 = 15378497) B15378497
theorem B6834887 : Blo 2023435 6834887 := bstep (se 1 (by rfl) ⟨5126165, by rfl⟩ : syracuseStep 6834887 = 10252331) B10252331
theorem B4556591 : Blo 2023435 4556591 := bstep (se 1 (by rfl) ⟨3417443, by rfl⟩ : syracuseStep 4556591 = 6834887) B6834887
theorem B3037727 : Blo 2023435 3037727 := bstep (se 1 (by rfl) ⟨2278295, by rfl⟩ : syracuseStep 3037727 = 4556591) B4556591
theorem B2025151 : Blo 2023435 2025151 := bstep (se 1 (by rfl) ⟨1518863, by rfl⟩ : syracuseStep 2025151 = 3037727) B3037727
theorem B3037733 : Blo 2023435 3037733 := bbase (se 4 (by rfl) ⟨284787, by rfl⟩ : syracuseStep 3037733 = 569575) (by norm_num)
theorem B2025155 : Blo 2023435 2025155 := bstep (se 1 (by rfl) ⟨1518866, by rfl⟩ : syracuseStep 2025155 = 3037733) B3037733
theorem B2563093 : Blo 2023435 2563093 := bbase (se 6 (by rfl) ⟨60072, by rfl⟩ : syracuseStep 2563093 = 120145) (by norm_num)
theorem B3417457 : Blo 2023435 3417457 := bstep (se 2 (by rfl) ⟨1281546, by rfl⟩ : syracuseStep 3417457 = 2563093) B2563093
theorem B4556609 : Blo 2023435 4556609 := bstep (se 2 (by rfl) ⟨1708728, by rfl⟩ : syracuseStep 4556609 = 3417457) B3417457
theorem B3037739 : Blo 2023435 3037739 := bstep (se 1 (by rfl) ⟨2278304, by rfl⟩ : syracuseStep 3037739 = 4556609) B4556609
theorem B2025159 : Blo 2023435 2025159 := bstep (se 1 (by rfl) ⟨1518869, by rfl⟩ : syracuseStep 2025159 = 3037739) B3037739
theorem B2278309 : Blo 2023435 2278309 := bbase (se 4 (by rfl) ⟨213591, by rfl⟩ : syracuseStep 2278309 = 427183) (by norm_num)
theorem B3037745 : Blo 2023435 3037745 := bstep (se 2 (by rfl) ⟨1139154, by rfl⟩ : syracuseStep 3037745 = 2278309) B2278309
theorem B2025163 : Blo 2023435 2025163 := bstep (se 1 (by rfl) ⟨1518872, by rfl⟩ : syracuseStep 2025163 = 3037745) B3037745
theorem B16422389 : Blo 2023435 16422389 := bbase (se 5 (by rfl) ⟨769799, by rfl⟩ : syracuseStep 16422389 = 1539599) (by norm_num)
theorem B10948259 : Blo 2023435 10948259 := bstep (se 1 (by rfl) ⟨8211194, by rfl⟩ : syracuseStep 10948259 = 16422389) B16422389
theorem B7298839 : Blo 2023435 7298839 := bstep (se 1 (by rfl) ⟨5474129, by rfl⟩ : syracuseStep 7298839 = 10948259) B10948259
theorem B9731785 : Blo 2023435 9731785 := bstep (se 2 (by rfl) ⟨3649419, by rfl⟩ : syracuseStep 9731785 = 7298839) B7298839
theorem B12975713 : Blo 2023435 12975713 := bstep (se 2 (by rfl) ⟨4865892, by rfl⟩ : syracuseStep 12975713 = 9731785) B9731785
theorem B8650475 : Blo 2023435 8650475 := bstep (se 1 (by rfl) ⟨6487856, by rfl⟩ : syracuseStep 8650475 = 12975713) B12975713
theorem B5766983 : Blo 2023435 5766983 := bstep (se 1 (by rfl) ⟨4325237, by rfl⟩ : syracuseStep 5766983 = 8650475) B8650475
theorem B3844655 : Blo 2023435 3844655 := bstep (se 1 (by rfl) ⟨2883491, by rfl⟩ : syracuseStep 3844655 = 5766983) B5766983
theorem B2563103 : Blo 2023435 2563103 := bstep (se 1 (by rfl) ⟨1922327, by rfl⟩ : syracuseStep 2563103 = 3844655) B3844655
theorem B6834941 : Blo 2023435 6834941 := bstep (se 3 (by rfl) ⟨1281551, by rfl⟩ : syracuseStep 6834941 = 2563103) B2563103
theorem B4556627 : Blo 2023435 4556627 := bstep (se 1 (by rfl) ⟨3417470, by rfl⟩ : syracuseStep 4556627 = 6834941) B6834941
theorem B3037751 : Blo 2023435 3037751 := bstep (se 1 (by rfl) ⟨2278313, by rfl⟩ : syracuseStep 3037751 = 4556627) B4556627
theorem B2025167 : Blo 2023435 2025167 := bstep (se 1 (by rfl) ⟨1518875, by rfl⟩ : syracuseStep 2025167 = 3037751) B3037751
theorem B3037757 : Blo 2023435 3037757 := bbase (se 3 (by rfl) ⟨569579, by rfl⟩ : syracuseStep 3037757 = 1139159) (by norm_num)
theorem B2025171 : Blo 2023435 2025171 := bstep (se 1 (by rfl) ⟨1518878, by rfl⟩ : syracuseStep 2025171 = 3037757) B3037757
theorem B4556645 : Blo 2023435 4556645 := bbase (se 4 (by rfl) ⟨427185, by rfl⟩ : syracuseStep 4556645 = 854371) (by norm_num)
theorem B3037763 : Blo 2023435 3037763 := bstep (se 1 (by rfl) ⟨2278322, by rfl⟩ : syracuseStep 3037763 = 4556645) B4556645
theorem B2025175 : Blo 2023435 2025175 := bstep (se 1 (by rfl) ⟨1518881, by rfl⟩ : syracuseStep 2025175 = 3037763) B3037763
theorem B5126237 : Blo 2023435 5126237 := bbase (se 3 (by rfl) ⟨961169, by rfl⟩ : syracuseStep 5126237 = 1922339) (by norm_num)
theorem B3417491 : Blo 2023435 3417491 := bstep (se 1 (by rfl) ⟨2563118, by rfl⟩ : syracuseStep 3417491 = 5126237) B5126237
theorem B2278327 : Blo 2023435 2278327 := bstep (se 1 (by rfl) ⟨1708745, by rfl⟩ : syracuseStep 2278327 = 3417491) B3417491
theorem B3037769 : Blo 2023435 3037769 := bstep (se 2 (by rfl) ⟨1139163, by rfl⟩ : syracuseStep 3037769 = 2278327) B2278327
theorem B2025179 : Blo 2023435 2025179 := bstep (se 1 (by rfl) ⟨1518884, by rfl⟩ : syracuseStep 2025179 = 3037769) B3037769
theorem B3844685 : Blo 2023435 3844685 := bbase (se 3 (by rfl) ⟨720878, by rfl⟩ : syracuseStep 3844685 = 1441757) (by norm_num)
theorem B10252493 : Blo 2023435 10252493 := bstep (se 3 (by rfl) ⟨1922342, by rfl⟩ : syracuseStep 10252493 = 3844685) B3844685
theorem B6834995 : Blo 2023435 6834995 := bstep (se 1 (by rfl) ⟨5126246, by rfl⟩ : syracuseStep 6834995 = 10252493) B10252493
theorem B4556663 : Blo 2023435 4556663 := bstep (se 1 (by rfl) ⟨3417497, by rfl⟩ : syracuseStep 4556663 = 6834995) B6834995
theorem B3037775 : Blo 2023435 3037775 := bstep (se 1 (by rfl) ⟨2278331, by rfl⟩ : syracuseStep 3037775 = 4556663) B4556663
theorem B2025183 : Blo 2023435 2025183 := bstep (se 1 (by rfl) ⟨1518887, by rfl⟩ : syracuseStep 2025183 = 3037775) B3037775
theorem B3037781 : Blo 2023435 3037781 := bbase (se 8 (by rfl) ⟨17799, by rfl⟩ : syracuseStep 3037781 = 35599) (by norm_num)
theorem B2025187 : Blo 2023435 2025187 := bstep (se 1 (by rfl) ⟨1518890, by rfl⟩ : syracuseStep 2025187 = 3037781) B3037781
theorem B4618853 : Blo 2023435 4618853 := bbase (se 4 (by rfl) ⟨433017, by rfl⟩ : syracuseStep 4618853 = 866035) (by norm_num)
theorem B3079235 : Blo 2023435 3079235 := bstep (se 1 (by rfl) ⟨2309426, by rfl⟩ : syracuseStep 3079235 = 4618853) B4618853
theorem B8211293 : Blo 2023435 8211293 := bstep (se 3 (by rfl) ⟨1539617, by rfl⟩ : syracuseStep 8211293 = 3079235) B3079235
theorem B5474195 : Blo 2023435 5474195 := bstep (se 1 (by rfl) ⟨4105646, by rfl⟩ : syracuseStep 5474195 = 8211293) B8211293
theorem B3649463 : Blo 2023435 3649463 := bstep (se 1 (by rfl) ⟨2737097, by rfl⟩ : syracuseStep 3649463 = 5474195) B5474195
theorem B2432975 : Blo 2023435 2432975 := bstep (se 1 (by rfl) ⟨1824731, by rfl⟩ : syracuseStep 2432975 = 3649463) B3649463
theorem B6487933 : Blo 2023435 6487933 := bstep (se 3 (by rfl) ⟨1216487, by rfl⟩ : syracuseStep 6487933 = 2432975) B2432975
theorem B8650577 : Blo 2023435 8650577 := bstep (se 2 (by rfl) ⟨3243966, by rfl⟩ : syracuseStep 8650577 = 6487933) B6487933
theorem B5767051 : Blo 2023435 5767051 := bstep (se 1 (by rfl) ⟨4325288, by rfl⟩ : syracuseStep 5767051 = 8650577) B8650577
theorem B7689401 : Blo 2023435 7689401 := bstep (se 2 (by rfl) ⟨2883525, by rfl⟩ : syracuseStep 7689401 = 5767051) B5767051
theorem B5126267 : Blo 2023435 5126267 := bstep (se 1 (by rfl) ⟨3844700, by rfl⟩ : syracuseStep 5126267 = 7689401) B7689401
theorem B3417511 : Blo 2023435 3417511 := bstep (se 1 (by rfl) ⟨2563133, by rfl⟩ : syracuseStep 3417511 = 5126267) B5126267
theorem B4556681 : Blo 2023435 4556681 := bstep (se 2 (by rfl) ⟨1708755, by rfl⟩ : syracuseStep 4556681 = 3417511) B3417511
theorem B3037787 : Blo 2023435 3037787 := bstep (se 1 (by rfl) ⟨2278340, by rfl⟩ : syracuseStep 3037787 = 4556681) B4556681
theorem B2025191 : Blo 2023435 2025191 := bstep (se 1 (by rfl) ⟨1518893, by rfl⟩ : syracuseStep 2025191 = 3037787) B3037787
theorem B2278345 : Blo 2023435 2278345 := bbase (se 2 (by rfl) ⟨854379, by rfl⟩ : syracuseStep 2278345 = 1708759) (by norm_num)
theorem B3037793 : Blo 2023435 3037793 := bstep (se 2 (by rfl) ⟨1139172, by rfl⟩ : syracuseStep 3037793 = 2278345) B2278345
theorem B2025195 : Blo 2023435 2025195 := bstep (se 1 (by rfl) ⟨1518896, by rfl⟩ : syracuseStep 2025195 = 3037793) B3037793
theorem B3649477 : Blo 2023435 3649477 := bbase (se 4 (by rfl) ⟨342138, by rfl⟩ : syracuseStep 3649477 = 684277) (by norm_num)
theorem B4865969 : Blo 2023435 4865969 := bstep (se 2 (by rfl) ⟨1824738, by rfl⟩ : syracuseStep 4865969 = 3649477) B3649477
theorem B3243979 : Blo 2023435 3243979 := bstep (se 1 (by rfl) ⟨2432984, by rfl⟩ : syracuseStep 3243979 = 4865969) B4865969
theorem B17301221 : Blo 2023435 17301221 := bstep (se 4 (by rfl) ⟨1621989, by rfl⟩ : syracuseStep 17301221 = 3243979) B3243979
theorem B11534147 : Blo 2023435 11534147 := bstep (se 1 (by rfl) ⟨8650610, by rfl⟩ : syracuseStep 11534147 = 17301221) B17301221
theorem B7689431 : Blo 2023435 7689431 := bstep (se 1 (by rfl) ⟨5767073, by rfl⟩ : syracuseStep 7689431 = 11534147) B11534147
theorem B5126287 : Blo 2023435 5126287 := bstep (se 1 (by rfl) ⟨3844715, by rfl⟩ : syracuseStep 5126287 = 7689431) B7689431
theorem B6835049 : Blo 2023435 6835049 := bstep (se 2 (by rfl) ⟨2563143, by rfl⟩ : syracuseStep 6835049 = 5126287) B5126287
theorem B4556699 : Blo 2023435 4556699 := bstep (se 1 (by rfl) ⟨3417524, by rfl⟩ : syracuseStep 4556699 = 6835049) B6835049
theorem B3037799 : Blo 2023435 3037799 := bstep (se 1 (by rfl) ⟨2278349, by rfl⟩ : syracuseStep 3037799 = 4556699) B4556699
theorem B2025199 : Blo 2023435 2025199 := bstep (se 1 (by rfl) ⟨1518899, by rfl⟩ : syracuseStep 2025199 = 3037799) B3037799
theorem B3037805 : Blo 2023435 3037805 := bbase (se 3 (by rfl) ⟨569588, by rfl⟩ : syracuseStep 3037805 = 1139177) (by norm_num)
theorem B2025203 : Blo 2023435 2025203 := bstep (se 1 (by rfl) ⟨1518902, by rfl⟩ : syracuseStep 2025203 = 3037805) B3037805
theorem B4556717 : Blo 2023435 4556717 := bbase (se 3 (by rfl) ⟨854384, by rfl⟩ : syracuseStep 4556717 = 1708769) (by norm_num)
theorem B3037811 : Blo 2023435 3037811 := bstep (se 1 (by rfl) ⟨2278358, by rfl⟩ : syracuseStep 3037811 = 4556717) B4556717
theorem B2025207 : Blo 2023435 2025207 := bstep (se 1 (by rfl) ⟨1518905, by rfl⟩ : syracuseStep 2025207 = 3037811) B3037811
theorem B5767109 : Blo 2023435 5767109 := bbase (se 4 (by rfl) ⟨540666, by rfl⟩ : syracuseStep 5767109 = 1081333) (by norm_num)
theorem B3844739 : Blo 2023435 3844739 := bstep (se 1 (by rfl) ⟨2883554, by rfl⟩ : syracuseStep 3844739 = 5767109) B5767109
theorem B2563159 : Blo 2023435 2563159 := bstep (se 1 (by rfl) ⟨1922369, by rfl⟩ : syracuseStep 2563159 = 3844739) B3844739
theorem B3417545 : Blo 2023435 3417545 := bstep (se 2 (by rfl) ⟨1281579, by rfl⟩ : syracuseStep 3417545 = 2563159) B2563159
theorem B2278363 : Blo 2023435 2278363 := bstep (se 1 (by rfl) ⟨1708772, by rfl⟩ : syracuseStep 2278363 = 3417545) B3417545
theorem B3037817 : Blo 2023435 3037817 := bstep (se 2 (by rfl) ⟨1139181, by rfl⟩ : syracuseStep 3037817 = 2278363) B2278363
theorem B2025211 : Blo 2023435 2025211 := bstep (se 1 (by rfl) ⟨1518908, by rfl⟩ : syracuseStep 2025211 = 3037817) B3037817
theorem B4218493 : Blo 2023435 4218493 := bbase (se 3 (by rfl) ⟨790967, by rfl⟩ : syracuseStep 4218493 = 1581935) (by norm_num)
theorem B5624657 : Blo 2023435 5624657 := bstep (se 2 (by rfl) ⟨2109246, by rfl⟩ : syracuseStep 5624657 = 4218493) B4218493
theorem B3749771 : Blo 2023435 3749771 := bstep (se 1 (by rfl) ⟨2812328, by rfl⟩ : syracuseStep 3749771 = 5624657) B5624657
theorem B9999389 : Blo 2023435 9999389 := bstep (se 3 (by rfl) ⟨1874885, by rfl⟩ : syracuseStep 9999389 = 3749771) B3749771
theorem B6666259 : Blo 2023435 6666259 := bstep (se 1 (by rfl) ⟨4999694, by rfl⟩ : syracuseStep 6666259 = 9999389) B9999389
theorem B8888345 : Blo 2023435 8888345 := bstep (se 2 (by rfl) ⟨3333129, by rfl⟩ : syracuseStep 8888345 = 6666259) B6666259
theorem B5925563 : Blo 2023435 5925563 := bstep (se 1 (by rfl) ⟨4444172, by rfl⟩ : syracuseStep 5925563 = 8888345) B8888345
theorem B3950375 : Blo 2023435 3950375 := bstep (se 1 (by rfl) ⟨2962781, by rfl⟩ : syracuseStep 3950375 = 5925563) B5925563
theorem B42137333 : Blo 2023435 42137333 := bstep (se 5 (by rfl) ⟨1975187, by rfl⟩ : syracuseStep 42137333 = 3950375) B3950375
theorem B28091555 : Blo 2023435 28091555 := bstep (se 1 (by rfl) ⟨21068666, by rfl⟩ : syracuseStep 28091555 = 42137333) B42137333
theorem B18727703 : Blo 2023435 18727703 := bstep (se 1 (by rfl) ⟨14045777, by rfl⟩ : syracuseStep 18727703 = 28091555) B28091555
theorem B12485135 : Blo 2023435 12485135 := bstep (se 1 (by rfl) ⟨9363851, by rfl⟩ : syracuseStep 12485135 = 18727703) B18727703
theorem B33293693 : Blo 2023435 33293693 := bstep (se 3 (by rfl) ⟨6242567, by rfl⟩ : syracuseStep 33293693 = 12485135) B12485135
theorem B22195795 : Blo 2023435 22195795 := bstep (se 1 (by rfl) ⟨16646846, by rfl⟩ : syracuseStep 22195795 = 33293693) B33293693
theorem B29594393 : Blo 2023435 29594393 := bstep (se 2 (by rfl) ⟨11097897, by rfl⟩ : syracuseStep 29594393 = 22195795) B22195795
theorem B19729595 : Blo 2023435 19729595 := bstep (se 1 (by rfl) ⟨14797196, by rfl⟩ : syracuseStep 19729595 = 29594393) B29594393
theorem B13153063 : Blo 2023435 13153063 := bstep (se 1 (by rfl) ⟨9864797, by rfl⟩ : syracuseStep 13153063 = 19729595) B19729595
theorem B17537417 : Blo 2023435 17537417 := bstep (se 2 (by rfl) ⟨6576531, by rfl⟩ : syracuseStep 17537417 = 13153063) B13153063
theorem B11691611 : Blo 2023435 11691611 := bstep (se 1 (by rfl) ⟨8768708, by rfl⟩ : syracuseStep 11691611 = 17537417) B17537417
theorem B7794407 : Blo 2023435 7794407 := bstep (se 1 (by rfl) ⟨5845805, by rfl⟩ : syracuseStep 7794407 = 11691611) B11691611
theorem B5196271 : Blo 2023435 5196271 := bstep (se 1 (by rfl) ⟨3897203, by rfl⟩ : syracuseStep 5196271 = 7794407) B7794407
theorem B6928361 : Blo 2023435 6928361 := bstep (se 2 (by rfl) ⟨2598135, by rfl⟩ : syracuseStep 6928361 = 5196271) B5196271
theorem B4618907 : Blo 2023435 4618907 := bstep (se 1 (by rfl) ⟨3464180, by rfl⟩ : syracuseStep 4618907 = 6928361) B6928361
theorem B3079271 : Blo 2023435 3079271 := bstep (se 1 (by rfl) ⟨2309453, by rfl⟩ : syracuseStep 3079271 = 4618907) B4618907
theorem B2052847 : Blo 2023435 2052847 := bstep (se 1 (by rfl) ⟨1539635, by rfl⟩ : syracuseStep 2052847 = 3079271) B3079271
theorem B2737129 : Blo 2023435 2737129 := bstep (se 2 (by rfl) ⟨1026423, by rfl⟩ : syracuseStep 2737129 = 2052847) B2052847
theorem B3649505 : Blo 2023435 3649505 := bstep (se 2 (by rfl) ⟨1368564, by rfl⟩ : syracuseStep 3649505 = 2737129) B2737129
theorem B38928053 : Blo 2023435 38928053 := bstep (se 5 (by rfl) ⟨1824752, by rfl⟩ : syracuseStep 38928053 = 3649505) B3649505
theorem B25952035 : Blo 2023435 25952035 := bstep (se 1 (by rfl) ⟨19464026, by rfl⟩ : syracuseStep 25952035 = 38928053) B38928053
theorem B34602713 : Blo 2023435 34602713 := bstep (se 2 (by rfl) ⟨12976017, by rfl⟩ : syracuseStep 34602713 = 25952035) B25952035
theorem B23068475 : Blo 2023435 23068475 := bstep (se 1 (by rfl) ⟨17301356, by rfl⟩ : syracuseStep 23068475 = 34602713) B34602713
theorem B15378983 : Blo 2023435 15378983 := bstep (se 1 (by rfl) ⟨11534237, by rfl⟩ : syracuseStep 15378983 = 23068475) B23068475
theorem B10252655 : Blo 2023435 10252655 := bstep (se 1 (by rfl) ⟨7689491, by rfl⟩ : syracuseStep 10252655 = 15378983) B15378983
theorem B6835103 : Blo 2023435 6835103 := bstep (se 1 (by rfl) ⟨5126327, by rfl⟩ : syracuseStep 6835103 = 10252655) B10252655
theorem B4556735 : Blo 2023435 4556735 := bstep (se 1 (by rfl) ⟨3417551, by rfl⟩ : syracuseStep 4556735 = 6835103) B6835103
theorem B3037823 : Blo 2023435 3037823 := bstep (se 1 (by rfl) ⟨2278367, by rfl⟩ : syracuseStep 3037823 = 4556735) B4556735
theorem B2025215 : Blo 2023435 2025215 := bstep (se 1 (by rfl) ⟨1518911, by rfl⟩ : syracuseStep 2025215 = 3037823) B3037823
theorem B3037829 : Blo 2023435 3037829 := bbase (se 4 (by rfl) ⟨284796, by rfl⟩ : syracuseStep 3037829 = 569593) (by norm_num)
theorem B2025219 : Blo 2023435 2025219 := bstep (se 1 (by rfl) ⟨1518914, by rfl⟩ : syracuseStep 2025219 = 3037829) B3037829
theorem B3417565 : Blo 2023435 3417565 := bbase (se 3 (by rfl) ⟨640793, by rfl⟩ : syracuseStep 3417565 = 1281587) (by norm_num)
theorem B4556753 : Blo 2023435 4556753 := bstep (se 2 (by rfl) ⟨1708782, by rfl⟩ : syracuseStep 4556753 = 3417565) B3417565
theorem B3037835 : Blo 2023435 3037835 := bstep (se 1 (by rfl) ⟨2278376, by rfl⟩ : syracuseStep 3037835 = 4556753) B4556753
theorem B2025223 : Blo 2023435 2025223 := bstep (se 1 (by rfl) ⟨1518917, by rfl⟩ : syracuseStep 2025223 = 3037835) B3037835
theorem B2278381 : Blo 2023435 2278381 := bbase (se 3 (by rfl) ⟨427196, by rfl⟩ : syracuseStep 2278381 = 854393) (by norm_num)
theorem B3037841 : Blo 2023435 3037841 := bstep (se 2 (by rfl) ⟨1139190, by rfl⟩ : syracuseStep 3037841 = 2278381) B2278381
theorem B2025227 : Blo 2023435 2025227 := bstep (se 1 (by rfl) ⟨1518920, by rfl⟩ : syracuseStep 2025227 = 3037841) B3037841
theorem B6835157 : Blo 2023435 6835157 := bbase (se 7 (by rfl) ⟨80099, by rfl⟩ : syracuseStep 6835157 = 160199) (by norm_num)
theorem B4556771 : Blo 2023435 4556771 := bstep (se 1 (by rfl) ⟨3417578, by rfl⟩ : syracuseStep 4556771 = 6835157) B6835157
theorem B3037847 : Blo 2023435 3037847 := bstep (se 1 (by rfl) ⟨2278385, by rfl⟩ : syracuseStep 3037847 = 4556771) B4556771
theorem B2025231 : Blo 2023435 2025231 := bstep (se 1 (by rfl) ⟨1518923, by rfl⟩ : syracuseStep 2025231 = 3037847) B3037847
theorem B3037853 : Blo 2023435 3037853 := bbase (se 3 (by rfl) ⟨569597, by rfl⟩ : syracuseStep 3037853 = 1139195) (by norm_num)
theorem B2025235 : Blo 2023435 2025235 := bstep (se 1 (by rfl) ⟨1518926, by rfl⟩ : syracuseStep 2025235 = 3037853) B3037853
theorem B4556789 : Blo 2023435 4556789 := bbase (se 5 (by rfl) ⟨213599, by rfl⟩ : syracuseStep 4556789 = 427199) (by norm_num)
theorem B3037859 : Blo 2023435 3037859 := bstep (se 1 (by rfl) ⟨2278394, by rfl⟩ : syracuseStep 3037859 = 4556789) B4556789
theorem B2025239 : Blo 2023435 2025239 := bstep (se 1 (by rfl) ⟨1518929, by rfl⟩ : syracuseStep 2025239 = 3037859) B3037859
theorem B3800981 : Blo 2023435 3800981 := bbase (se 6 (by rfl) ⟨89085, by rfl⟩ : syracuseStep 3800981 = 178171) (by norm_num)
theorem B2533987 : Blo 2023435 2533987 := bstep (se 1 (by rfl) ⟨1900490, by rfl⟩ : syracuseStep 2533987 = 3800981) B3800981
theorem B3378649 : Blo 2023435 3378649 := bstep (se 2 (by rfl) ⟨1266993, by rfl⟩ : syracuseStep 3378649 = 2533987) B2533987
theorem B4504865 : Blo 2023435 4504865 := bstep (se 2 (by rfl) ⟨1689324, by rfl⟩ : syracuseStep 4504865 = 3378649) B3378649
theorem B48051893 : Blo 2023435 48051893 := bstep (se 5 (by rfl) ⟨2252432, by rfl⟩ : syracuseStep 48051893 = 4504865) B4504865
theorem B128138381 : Blo 2023435 128138381 := bstep (se 3 (by rfl) ⟨24025946, by rfl⟩ : syracuseStep 128138381 = 48051893) B48051893
theorem B85425587 : Blo 2023435 85425587 := bstep (se 1 (by rfl) ⟨64069190, by rfl⟩ : syracuseStep 85425587 = 128138381) B128138381
theorem B56950391 : Blo 2023435 56950391 := bstep (se 1 (by rfl) ⟨42712793, by rfl⟩ : syracuseStep 56950391 = 85425587) B85425587
theorem B37966927 : Blo 2023435 37966927 := bstep (se 1 (by rfl) ⟨28475195, by rfl⟩ : syracuseStep 37966927 = 56950391) B56950391
theorem B50622569 : Blo 2023435 50622569 := bstep (se 2 (by rfl) ⟨18983463, by rfl⟩ : syracuseStep 50622569 = 37966927) B37966927
theorem B33748379 : Blo 2023435 33748379 := bstep (se 1 (by rfl) ⟨25311284, by rfl⟩ : syracuseStep 33748379 = 50622569) B50622569
theorem B22498919 : Blo 2023435 22498919 := bstep (se 1 (by rfl) ⟨16874189, by rfl⟩ : syracuseStep 22498919 = 33748379) B33748379
theorem B14999279 : Blo 2023435 14999279 := bstep (se 1 (by rfl) ⟨11249459, by rfl⟩ : syracuseStep 14999279 = 22498919) B22498919
theorem B159992309 : Blo 2023435 159992309 := bstep (se 5 (by rfl) ⟨7499639, by rfl⟩ : syracuseStep 159992309 = 14999279) B14999279
theorem B106661539 : Blo 2023435 106661539 := bstep (se 1 (by rfl) ⟨79996154, by rfl⟩ : syracuseStep 106661539 = 159992309) B159992309
theorem B568861541 : Blo 2023435 568861541 := bstep (se 4 (by rfl) ⟨53330769, by rfl⟩ : syracuseStep 568861541 = 106661539) B106661539
theorem B379241027 : Blo 2023435 379241027 := bstep (se 1 (by rfl) ⟨284430770, by rfl⟩ : syracuseStep 379241027 = 568861541) B568861541
theorem B252827351 : Blo 2023435 252827351 := bstep (se 1 (by rfl) ⟨189620513, by rfl⟩ : syracuseStep 252827351 = 379241027) B379241027
theorem B168551567 : Blo 2023435 168551567 := bstep (se 1 (by rfl) ⟨126413675, by rfl⟩ : syracuseStep 168551567 = 252827351) B252827351
theorem B112367711 : Blo 2023435 112367711 := bstep (se 1 (by rfl) ⟨84275783, by rfl⟩ : syracuseStep 112367711 = 168551567) B168551567
theorem B74911807 : Blo 2023435 74911807 := bstep (se 1 (by rfl) ⟨56183855, by rfl⟩ : syracuseStep 74911807 = 112367711) B112367711
theorem B99882409 : Blo 2023435 99882409 := bstep (se 2 (by rfl) ⟨37455903, by rfl⟩ : syracuseStep 99882409 = 74911807) B74911807
theorem B133176545 : Blo 2023435 133176545 := bstep (se 2 (by rfl) ⟨49941204, by rfl⟩ : syracuseStep 133176545 = 99882409) B99882409
theorem B88784363 : Blo 2023435 88784363 := bstep (se 1 (by rfl) ⟨66588272, by rfl⟩ : syracuseStep 88784363 = 133176545) B133176545
theorem B236758301 : Blo 2023435 236758301 := bstep (se 3 (by rfl) ⟨44392181, by rfl⟩ : syracuseStep 236758301 = 88784363) B88784363
theorem B157838867 : Blo 2023435 157838867 := bstep (se 1 (by rfl) ⟨118379150, by rfl⟩ : syracuseStep 157838867 = 236758301) B236758301
theorem B105225911 : Blo 2023435 105225911 := bstep (se 1 (by rfl) ⟨78919433, by rfl⟩ : syracuseStep 105225911 = 157838867) B157838867
theorem B70150607 : Blo 2023435 70150607 := bstep (se 1 (by rfl) ⟨52612955, by rfl⟩ : syracuseStep 70150607 = 105225911) B105225911
theorem B46767071 : Blo 2023435 46767071 := bstep (se 1 (by rfl) ⟨35075303, by rfl⟩ : syracuseStep 46767071 = 70150607) B70150607
theorem B31178047 : Blo 2023435 31178047 := bstep (se 1 (by rfl) ⟨23383535, by rfl⟩ : syracuseStep 31178047 = 46767071) B46767071
theorem B41570729 : Blo 2023435 41570729 := bstep (se 2 (by rfl) ⟨15589023, by rfl⟩ : syracuseStep 41570729 = 31178047) B31178047
theorem B27713819 : Blo 2023435 27713819 := bstep (se 1 (by rfl) ⟨20785364, by rfl⟩ : syracuseStep 27713819 = 41570729) B41570729
theorem B18475879 : Blo 2023435 18475879 := bstep (se 1 (by rfl) ⟨13856909, by rfl⟩ : syracuseStep 18475879 = 27713819) B27713819
theorem B24634505 : Blo 2023435 24634505 := bstep (se 2 (by rfl) ⟨9237939, by rfl⟩ : syracuseStep 24634505 = 18475879) B18475879
theorem B16423003 : Blo 2023435 16423003 := bstep (se 1 (by rfl) ⟨12317252, by rfl⟩ : syracuseStep 16423003 = 24634505) B24634505
theorem B87589349 : Blo 2023435 87589349 := bstep (se 4 (by rfl) ⟨8211501, by rfl⟩ : syracuseStep 87589349 = 16423003) B16423003
theorem B58392899 : Blo 2023435 58392899 := bstep (se 1 (by rfl) ⟨43794674, by rfl⟩ : syracuseStep 58392899 = 87589349) B87589349
theorem B38928599 : Blo 2023435 38928599 := bstep (se 1 (by rfl) ⟨29196449, by rfl⟩ : syracuseStep 38928599 = 58392899) B58392899
theorem B25952399 : Blo 2023435 25952399 := bstep (se 1 (by rfl) ⟨19464299, by rfl⟩ : syracuseStep 25952399 = 38928599) B38928599
theorem B17301599 : Blo 2023435 17301599 := bstep (se 1 (by rfl) ⟨12976199, by rfl⟩ : syracuseStep 17301599 = 25952399) B25952399
theorem B11534399 : Blo 2023435 11534399 := bstep (se 1 (by rfl) ⟨8650799, by rfl⟩ : syracuseStep 11534399 = 17301599) B17301599
theorem B7689599 : Blo 2023435 7689599 := bstep (se 1 (by rfl) ⟨5767199, by rfl⟩ : syracuseStep 7689599 = 11534399) B11534399
theorem B5126399 : Blo 2023435 5126399 := bstep (se 1 (by rfl) ⟨3844799, by rfl⟩ : syracuseStep 5126399 = 7689599) B7689599
theorem B3417599 : Blo 2023435 3417599 := bstep (se 1 (by rfl) ⟨2563199, by rfl⟩ : syracuseStep 3417599 = 5126399) B5126399
theorem B2278399 : Blo 2023435 2278399 := bstep (se 1 (by rfl) ⟨1708799, by rfl⟩ : syracuseStep 2278399 = 3417599) B3417599
theorem B3037865 : Blo 2023435 3037865 := bstep (se 2 (by rfl) ⟨1139199, by rfl⟩ : syracuseStep 3037865 = 2278399) B2278399
theorem B2025243 : Blo 2023435 2025243 := bstep (se 1 (by rfl) ⟨1518932, by rfl⟩ : syracuseStep 2025243 = 3037865) B3037865
theorem B2883605 : Blo 2023435 2883605 := bbase (se 6 (by rfl) ⟨67584, by rfl⟩ : syracuseStep 2883605 = 135169) (by norm_num)
theorem B7689613 : Blo 2023435 7689613 := bstep (se 3 (by rfl) ⟨1441802, by rfl⟩ : syracuseStep 7689613 = 2883605) B2883605
theorem B10252817 : Blo 2023435 10252817 := bstep (se 2 (by rfl) ⟨3844806, by rfl⟩ : syracuseStep 10252817 = 7689613) B7689613
theorem B6835211 : Blo 2023435 6835211 := bstep (se 1 (by rfl) ⟨5126408, by rfl⟩ : syracuseStep 6835211 = 10252817) B10252817
theorem B4556807 : Blo 2023435 4556807 := bstep (se 1 (by rfl) ⟨3417605, by rfl⟩ : syracuseStep 4556807 = 6835211) B6835211
theorem B3037871 : Blo 2023435 3037871 := bstep (se 1 (by rfl) ⟨2278403, by rfl⟩ : syracuseStep 3037871 = 4556807) B4556807
theorem B2025247 : Blo 2023435 2025247 := bstep (se 1 (by rfl) ⟨1518935, by rfl⟩ : syracuseStep 2025247 = 3037871) B3037871
theorem B3037877 : Blo 2023435 3037877 := bbase (se 5 (by rfl) ⟨142400, by rfl⟩ : syracuseStep 3037877 = 284801) (by norm_num)
theorem B2025251 : Blo 2023435 2025251 := bstep (se 1 (by rfl) ⟨1518938, by rfl⟩ : syracuseStep 2025251 = 3037877) B3037877
theorem B5126429 : Blo 2023435 5126429 := bbase (se 3 (by rfl) ⟨961205, by rfl⟩ : syracuseStep 5126429 = 1922411) (by norm_num)
theorem B3417619 : Blo 2023435 3417619 := bstep (se 1 (by rfl) ⟨2563214, by rfl⟩ : syracuseStep 3417619 = 5126429) B5126429
theorem B4556825 : Blo 2023435 4556825 := bstep (se 2 (by rfl) ⟨1708809, by rfl⟩ : syracuseStep 4556825 = 3417619) B3417619
theorem B3037883 : Blo 2023435 3037883 := bstep (se 1 (by rfl) ⟨2278412, by rfl⟩ : syracuseStep 3037883 = 4556825) B4556825
theorem B2025255 : Blo 2023435 2025255 := bstep (se 1 (by rfl) ⟨1518941, by rfl⟩ : syracuseStep 2025255 = 3037883) B3037883
theorem B2278417 : Blo 2023435 2278417 := bbase (se 2 (by rfl) ⟨854406, by rfl⟩ : syracuseStep 2278417 = 1708813) (by norm_num)
theorem B3037889 : Blo 2023435 3037889 := bstep (se 2 (by rfl) ⟨1139208, by rfl⟩ : syracuseStep 3037889 = 2278417) B2278417
theorem B2025259 : Blo 2023435 2025259 := bstep (se 1 (by rfl) ⟨1518944, by rfl⟩ : syracuseStep 2025259 = 3037889) B3037889
theorem B3844837 : Blo 2023435 3844837 := bbase (se 4 (by rfl) ⟨360453, by rfl⟩ : syracuseStep 3844837 = 720907) (by norm_num)
theorem B5126449 : Blo 2023435 5126449 := bstep (se 2 (by rfl) ⟨1922418, by rfl⟩ : syracuseStep 5126449 = 3844837) B3844837
theorem B6835265 : Blo 2023435 6835265 := bstep (se 2 (by rfl) ⟨2563224, by rfl⟩ : syracuseStep 6835265 = 5126449) B5126449
theorem B4556843 : Blo 2023435 4556843 := bstep (se 1 (by rfl) ⟨3417632, by rfl⟩ : syracuseStep 4556843 = 6835265) B6835265
theorem B3037895 : Blo 2023435 3037895 := bstep (se 1 (by rfl) ⟨2278421, by rfl⟩ : syracuseStep 3037895 = 4556843) B4556843
theorem B2025263 : Blo 2023435 2025263 := bstep (se 1 (by rfl) ⟨1518947, by rfl⟩ : syracuseStep 2025263 = 3037895) B3037895
theorem B3037901 : Blo 2023435 3037901 := bbase (se 3 (by rfl) ⟨569606, by rfl⟩ : syracuseStep 3037901 = 1139213) (by norm_num)
theorem B2025267 : Blo 2023435 2025267 := bstep (se 1 (by rfl) ⟨1518950, by rfl⟩ : syracuseStep 2025267 = 3037901) B3037901
theorem B4556861 : Blo 2023435 4556861 := bbase (se 3 (by rfl) ⟨854411, by rfl⟩ : syracuseStep 4556861 = 1708823) (by norm_num)
theorem B3037907 : Blo 2023435 3037907 := bstep (se 1 (by rfl) ⟨2278430, by rfl⟩ : syracuseStep 3037907 = 4556861) B4556861
theorem B2025271 : Blo 2023435 2025271 := bstep (se 1 (by rfl) ⟨1518953, by rfl⟩ : syracuseStep 2025271 = 3037907) B3037907
theorem B3417653 : Blo 2023435 3417653 := bbase (se 5 (by rfl) ⟨160202, by rfl⟩ : syracuseStep 3417653 = 320405) (by norm_num)
theorem B2278435 : Blo 2023435 2278435 := bstep (se 1 (by rfl) ⟨1708826, by rfl⟩ : syracuseStep 2278435 = 3417653) B3417653
theorem B3037913 : Blo 2023435 3037913 := bstep (se 2 (by rfl) ⟨1139217, by rfl⟩ : syracuseStep 3037913 = 2278435) B2278435
theorem B2025275 : Blo 2023435 2025275 := bstep (se 1 (by rfl) ⟨1518956, by rfl⟩ : syracuseStep 2025275 = 3037913) B3037913
theorem B5767301 : Blo 2023435 5767301 := bbase (se 4 (by rfl) ⟨540684, by rfl⟩ : syracuseStep 5767301 = 1081369) (by norm_num)
theorem B15379469 : Blo 2023435 15379469 := bstep (se 3 (by rfl) ⟨2883650, by rfl⟩ : syracuseStep 15379469 = 5767301) B5767301
theorem B10252979 : Blo 2023435 10252979 := bstep (se 1 (by rfl) ⟨7689734, by rfl⟩ : syracuseStep 10252979 = 15379469) B15379469
theorem B6835319 : Blo 2023435 6835319 := bstep (se 1 (by rfl) ⟨5126489, by rfl⟩ : syracuseStep 6835319 = 10252979) B10252979
theorem B4556879 : Blo 2023435 4556879 := bstep (se 1 (by rfl) ⟨3417659, by rfl⟩ : syracuseStep 4556879 = 6835319) B6835319
theorem B3037919 : Blo 2023435 3037919 := bstep (se 1 (by rfl) ⟨2278439, by rfl⟩ : syracuseStep 3037919 = 4556879) B4556879
theorem B2025279 : Blo 2023435 2025279 := bstep (se 1 (by rfl) ⟨1518959, by rfl⟩ : syracuseStep 2025279 = 3037919) B3037919
theorem B3037925 : Blo 2023435 3037925 := bbase (se 4 (by rfl) ⟨284805, by rfl⟩ : syracuseStep 3037925 = 569611) (by norm_num)
theorem B2025283 : Blo 2023435 2025283 := bstep (se 1 (by rfl) ⟨1518962, by rfl⟩ : syracuseStep 2025283 = 3037925) B3037925
theorem B3649637 : Blo 2023435 3649637 := bbase (se 4 (by rfl) ⟨342153, by rfl⟩ : syracuseStep 3649637 = 684307) (by norm_num)
theorem B2433091 : Blo 2023435 2433091 := bstep (se 1 (by rfl) ⟨1824818, by rfl⟩ : syracuseStep 2433091 = 3649637) B3649637
theorem B3244121 : Blo 2023435 3244121 := bstep (se 2 (by rfl) ⟨1216545, by rfl⟩ : syracuseStep 3244121 = 2433091) B2433091
theorem B2162747 : Blo 2023435 2162747 := bstep (se 1 (by rfl) ⟨1622060, by rfl⟩ : syracuseStep 2162747 = 3244121) B3244121
theorem B5767325 : Blo 2023435 5767325 := bstep (se 3 (by rfl) ⟨1081373, by rfl⟩ : syracuseStep 5767325 = 2162747) B2162747
theorem B3844883 : Blo 2023435 3844883 := bstep (se 1 (by rfl) ⟨2883662, by rfl⟩ : syracuseStep 3844883 = 5767325) B5767325
theorem B2563255 : Blo 2023435 2563255 := bstep (se 1 (by rfl) ⟨1922441, by rfl⟩ : syracuseStep 2563255 = 3844883) B3844883
theorem B3417673 : Blo 2023435 3417673 := bstep (se 2 (by rfl) ⟨1281627, by rfl⟩ : syracuseStep 3417673 = 2563255) B2563255
theorem B4556897 : Blo 2023435 4556897 := bstep (se 2 (by rfl) ⟨1708836, by rfl⟩ : syracuseStep 4556897 = 3417673) B3417673
theorem B3037931 : Blo 2023435 3037931 := bstep (se 1 (by rfl) ⟨2278448, by rfl⟩ : syracuseStep 3037931 = 4556897) B4556897
theorem B2025287 : Blo 2023435 2025287 := bstep (se 1 (by rfl) ⟨1518965, by rfl⟩ : syracuseStep 2025287 = 3037931) B3037931
theorem B2278453 : Blo 2023435 2278453 := bbase (se 5 (by rfl) ⟨106802, by rfl⟩ : syracuseStep 2278453 = 213605) (by norm_num)
theorem B3037937 : Blo 2023435 3037937 := bstep (se 2 (by rfl) ⟨1139226, by rfl⟩ : syracuseStep 3037937 = 2278453) B2278453
theorem B2025291 : Blo 2023435 2025291 := bstep (se 1 (by rfl) ⟨1518968, by rfl⟩ : syracuseStep 2025291 = 3037937) B3037937
theorem B2563265 : Blo 2023435 2563265 := bbase (se 2 (by rfl) ⟨961224, by rfl⟩ : syracuseStep 2563265 = 1922449) (by norm_num)
theorem B6835373 : Blo 2023435 6835373 := bstep (se 3 (by rfl) ⟨1281632, by rfl⟩ : syracuseStep 6835373 = 2563265) B2563265
theorem B4556915 : Blo 2023435 4556915 := bstep (se 1 (by rfl) ⟨3417686, by rfl⟩ : syracuseStep 4556915 = 6835373) B6835373
theorem B3037943 : Blo 2023435 3037943 := bstep (se 1 (by rfl) ⟨2278457, by rfl⟩ : syracuseStep 3037943 = 4556915) B4556915
theorem B2025295 : Blo 2023435 2025295 := bstep (se 1 (by rfl) ⟨1518971, by rfl⟩ : syracuseStep 2025295 = 3037943) B3037943
theorem B3037949 : Blo 2023435 3037949 := bbase (se 3 (by rfl) ⟨569615, by rfl⟩ : syracuseStep 3037949 = 1139231) (by norm_num)
theorem B2025299 : Blo 2023435 2025299 := bstep (se 1 (by rfl) ⟨1518974, by rfl⟩ : syracuseStep 2025299 = 3037949) B3037949
theorem B4556933 : Blo 2023435 4556933 := bbase (se 4 (by rfl) ⟨427212, by rfl⟩ : syracuseStep 4556933 = 854425) (by norm_num)
theorem B3037955 : Blo 2023435 3037955 := bstep (se 1 (by rfl) ⟨2278466, by rfl⟩ : syracuseStep 3037955 = 4556933) B4556933
theorem B2025303 : Blo 2023435 2025303 := bstep (se 1 (by rfl) ⟨1518977, by rfl⟩ : syracuseStep 2025303 = 3037955) B3037955
theorem B3699469 : Blo 2023435 3699469 := bbase (se 3 (by rfl) ⟨693650, by rfl⟩ : syracuseStep 3699469 = 1387301) (by norm_num)
theorem B4932625 : Blo 2023435 4932625 := bstep (se 2 (by rfl) ⟨1849734, by rfl⟩ : syracuseStep 4932625 = 3699469) B3699469
theorem B6576833 : Blo 2023435 6576833 := bstep (se 2 (by rfl) ⟨2466312, by rfl⟩ : syracuseStep 6576833 = 4932625) B4932625
theorem B17538221 : Blo 2023435 17538221 := bstep (se 3 (by rfl) ⟨3288416, by rfl⟩ : syracuseStep 17538221 = 6576833) B6576833
theorem B11692147 : Blo 2023435 11692147 := bstep (se 1 (by rfl) ⟨8769110, by rfl⟩ : syracuseStep 11692147 = 17538221) B17538221
theorem B15589529 : Blo 2023435 15589529 := bstep (se 2 (by rfl) ⟨5846073, by rfl⟩ : syracuseStep 15589529 = 11692147) B11692147
theorem B10393019 : Blo 2023435 10393019 := bstep (se 1 (by rfl) ⟨7794764, by rfl⟩ : syracuseStep 10393019 = 15589529) B15589529
theorem B6928679 : Blo 2023435 6928679 := bstep (se 1 (by rfl) ⟨5196509, by rfl⟩ : syracuseStep 6928679 = 10393019) B10393019
theorem B4619119 : Blo 2023435 4619119 := bstep (se 1 (by rfl) ⟨3464339, by rfl⟩ : syracuseStep 4619119 = 6928679) B6928679
theorem B6158825 : Blo 2023435 6158825 := bstep (se 2 (by rfl) ⟨2309559, by rfl⟩ : syracuseStep 6158825 = 4619119) B4619119
theorem B4105883 : Blo 2023435 4105883 := bstep (se 1 (by rfl) ⟨3079412, by rfl⟩ : syracuseStep 4105883 = 6158825) B6158825
theorem B2737255 : Blo 2023435 2737255 := bstep (se 1 (by rfl) ⟨2052941, by rfl⟩ : syracuseStep 2737255 = 4105883) B4105883
theorem B3649673 : Blo 2023435 3649673 := bstep (se 2 (by rfl) ⟨1368627, by rfl⟩ : syracuseStep 3649673 = 2737255) B2737255
theorem B2433115 : Blo 2023435 2433115 := bstep (se 1 (by rfl) ⟨1824836, by rfl⟩ : syracuseStep 2433115 = 3649673) B3649673
theorem B3244153 : Blo 2023435 3244153 := bstep (se 2 (by rfl) ⟨1216557, by rfl⟩ : syracuseStep 3244153 = 2433115) B2433115
theorem B4325537 : Blo 2023435 4325537 := bstep (se 2 (by rfl) ⟨1622076, by rfl⟩ : syracuseStep 4325537 = 3244153) B3244153
theorem B2883691 : Blo 2023435 2883691 := bstep (se 1 (by rfl) ⟨2162768, by rfl⟩ : syracuseStep 2883691 = 4325537) B4325537
theorem B3844921 : Blo 2023435 3844921 := bstep (se 2 (by rfl) ⟨1441845, by rfl⟩ : syracuseStep 3844921 = 2883691) B2883691
theorem B5126561 : Blo 2023435 5126561 := bstep (se 2 (by rfl) ⟨1922460, by rfl⟩ : syracuseStep 5126561 = 3844921) B3844921
theorem B3417707 : Blo 2023435 3417707 := bstep (se 1 (by rfl) ⟨2563280, by rfl⟩ : syracuseStep 3417707 = 5126561) B5126561
theorem B2278471 : Blo 2023435 2278471 := bstep (se 1 (by rfl) ⟨1708853, by rfl⟩ : syracuseStep 2278471 = 3417707) B3417707
theorem B3037961 : Blo 2023435 3037961 := bstep (se 2 (by rfl) ⟨1139235, by rfl⟩ : syracuseStep 3037961 = 2278471) B2278471
theorem B2025307 : Blo 2023435 2025307 := bstep (se 1 (by rfl) ⟨1518980, by rfl⟩ : syracuseStep 2025307 = 3037961) B3037961
theorem B10253141 : Blo 2023435 10253141 := bbase (se 9 (by rfl) ⟨30038, by rfl⟩ : syracuseStep 10253141 = 60077) (by norm_num)
theorem B6835427 : Blo 2023435 6835427 := bstep (se 1 (by rfl) ⟨5126570, by rfl⟩ : syracuseStep 6835427 = 10253141) B10253141
theorem B4556951 : Blo 2023435 4556951 := bstep (se 1 (by rfl) ⟨3417713, by rfl⟩ : syracuseStep 4556951 = 6835427) B6835427
theorem B3037967 : Blo 2023435 3037967 := bstep (se 1 (by rfl) ⟨2278475, by rfl⟩ : syracuseStep 3037967 = 4556951) B4556951
theorem B2025311 : Blo 2023435 2025311 := bstep (se 1 (by rfl) ⟨1518983, by rfl⟩ : syracuseStep 2025311 = 3037967) B3037967
theorem B3037973 : Blo 2023435 3037973 := bbase (se 6 (by rfl) ⟨71202, by rfl⟩ : syracuseStep 3037973 = 142405) (by norm_num)
theorem B2025315 : Blo 2023435 2025315 := bstep (se 1 (by rfl) ⟨1518986, by rfl⟩ : syracuseStep 2025315 = 3037973) B3037973
theorem B2633717 : Blo 2023435 2633717 := bbase (se 5 (by rfl) ⟨123455, by rfl⟩ : syracuseStep 2633717 = 246911) (by norm_num)
theorem B7023245 : Blo 2023435 7023245 := bstep (se 3 (by rfl) ⟨1316858, by rfl⟩ : syracuseStep 7023245 = 2633717) B2633717
theorem B18728653 : Blo 2023435 18728653 := bstep (se 3 (by rfl) ⟨3511622, by rfl⟩ : syracuseStep 18728653 = 7023245) B7023245
theorem B24971537 : Blo 2023435 24971537 := bstep (se 2 (by rfl) ⟨9364326, by rfl⟩ : syracuseStep 24971537 = 18728653) B18728653
theorem B16647691 : Blo 2023435 16647691 := bstep (se 1 (by rfl) ⟨12485768, by rfl⟩ : syracuseStep 16647691 = 24971537) B24971537
theorem B22196921 : Blo 2023435 22196921 := bstep (se 2 (by rfl) ⟨8323845, by rfl⟩ : syracuseStep 22196921 = 16647691) B16647691
theorem B236767157 : Blo 2023435 236767157 := bstep (se 5 (by rfl) ⟨11098460, by rfl⟩ : syracuseStep 236767157 = 22196921) B22196921
theorem B157844771 : Blo 2023435 157844771 := bstep (se 1 (by rfl) ⟨118383578, by rfl⟩ : syracuseStep 157844771 = 236767157) B236767157
theorem B105229847 : Blo 2023435 105229847 := bstep (se 1 (by rfl) ⟨78922385, by rfl⟩ : syracuseStep 105229847 = 157844771) B157844771
theorem B70153231 : Blo 2023435 70153231 := bstep (se 1 (by rfl) ⟨52614923, by rfl⟩ : syracuseStep 70153231 = 105229847) B105229847
theorem B93537641 : Blo 2023435 93537641 := bstep (se 2 (by rfl) ⟨35076615, by rfl⟩ : syracuseStep 93537641 = 70153231) B70153231
theorem B62358427 : Blo 2023435 62358427 := bstep (se 1 (by rfl) ⟨46768820, by rfl⟩ : syracuseStep 62358427 = 93537641) B93537641
theorem B83144569 : Blo 2023435 83144569 := bstep (se 2 (by rfl) ⟨31179213, by rfl⟩ : syracuseStep 83144569 = 62358427) B62358427
theorem B110859425 : Blo 2023435 110859425 := bstep (se 2 (by rfl) ⟨41572284, by rfl⟩ : syracuseStep 110859425 = 83144569) B83144569
theorem B73906283 : Blo 2023435 73906283 := bstep (se 1 (by rfl) ⟨55429712, by rfl⟩ : syracuseStep 73906283 = 110859425) B110859425
theorem B49270855 : Blo 2023435 49270855 := bstep (se 1 (by rfl) ⟨36953141, by rfl⟩ : syracuseStep 49270855 = 73906283) B73906283
theorem B65694473 : Blo 2023435 65694473 := bstep (se 2 (by rfl) ⟨24635427, by rfl⟩ : syracuseStep 65694473 = 49270855) B49270855
theorem B43796315 : Blo 2023435 43796315 := bstep (se 1 (by rfl) ⟨32847236, by rfl⟩ : syracuseStep 43796315 = 65694473) B65694473
theorem B29197543 : Blo 2023435 29197543 := bstep (se 1 (by rfl) ⟨21898157, by rfl⟩ : syracuseStep 29197543 = 43796315) B43796315
theorem B38930057 : Blo 2023435 38930057 := bstep (se 2 (by rfl) ⟨14598771, by rfl⟩ : syracuseStep 38930057 = 29197543) B29197543
theorem B25953371 : Blo 2023435 25953371 := bstep (se 1 (by rfl) ⟨19465028, by rfl⟩ : syracuseStep 25953371 = 38930057) B38930057
theorem B17302247 : Blo 2023435 17302247 := bstep (se 1 (by rfl) ⟨12976685, by rfl⟩ : syracuseStep 17302247 = 25953371) B25953371
theorem B11534831 : Blo 2023435 11534831 := bstep (se 1 (by rfl) ⟨8651123, by rfl⟩ : syracuseStep 11534831 = 17302247) B17302247
theorem B7689887 : Blo 2023435 7689887 := bstep (se 1 (by rfl) ⟨5767415, by rfl⟩ : syracuseStep 7689887 = 11534831) B11534831
theorem B5126591 : Blo 2023435 5126591 := bstep (se 1 (by rfl) ⟨3844943, by rfl⟩ : syracuseStep 5126591 = 7689887) B7689887
theorem B3417727 : Blo 2023435 3417727 := bstep (se 1 (by rfl) ⟨2563295, by rfl⟩ : syracuseStep 3417727 = 5126591) B5126591
theorem B4556969 : Blo 2023435 4556969 := bstep (se 2 (by rfl) ⟨1708863, by rfl⟩ : syracuseStep 4556969 = 3417727) B3417727
theorem B3037979 : Blo 2023435 3037979 := bstep (se 1 (by rfl) ⟨2278484, by rfl⟩ : syracuseStep 3037979 = 4556969) B4556969
theorem B2025319 : Blo 2023435 2025319 := bstep (se 1 (by rfl) ⟨1518989, by rfl⟩ : syracuseStep 2025319 = 3037979) B3037979
theorem B2278489 : Blo 2023435 2278489 := bbase (se 2 (by rfl) ⟨854433, by rfl⟩ : syracuseStep 2278489 = 1708867) (by norm_num)
theorem B3037985 : Blo 2023435 3037985 := bstep (se 2 (by rfl) ⟨1139244, by rfl⟩ : syracuseStep 3037985 = 2278489) B2278489
theorem B2025323 : Blo 2023435 2025323 := bstep (se 1 (by rfl) ⟨1518992, by rfl⟩ : syracuseStep 2025323 = 3037985) B3037985
theorem B4866277 : Blo 2023435 4866277 := bbase (se 4 (by rfl) ⟨456213, by rfl⟩ : syracuseStep 4866277 = 912427) (by norm_num)
theorem B6488369 : Blo 2023435 6488369 := bstep (se 2 (by rfl) ⟨2433138, by rfl⟩ : syracuseStep 6488369 = 4866277) B4866277
theorem B4325579 : Blo 2023435 4325579 := bstep (se 1 (by rfl) ⟨3244184, by rfl⟩ : syracuseStep 4325579 = 6488369) B6488369
theorem B2883719 : Blo 2023435 2883719 := bstep (se 1 (by rfl) ⟨2162789, by rfl⟩ : syracuseStep 2883719 = 4325579) B4325579
theorem B7689917 : Blo 2023435 7689917 := bstep (se 3 (by rfl) ⟨1441859, by rfl⟩ : syracuseStep 7689917 = 2883719) B2883719
theorem B5126611 : Blo 2023435 5126611 := bstep (se 1 (by rfl) ⟨3844958, by rfl⟩ : syracuseStep 5126611 = 7689917) B7689917
theorem B6835481 : Blo 2023435 6835481 := bstep (se 2 (by rfl) ⟨2563305, by rfl⟩ : syracuseStep 6835481 = 5126611) B5126611
theorem B4556987 : Blo 2023435 4556987 := bstep (se 1 (by rfl) ⟨3417740, by rfl⟩ : syracuseStep 4556987 = 6835481) B6835481
theorem B3037991 : Blo 2023435 3037991 := bstep (se 1 (by rfl) ⟨2278493, by rfl⟩ : syracuseStep 3037991 = 4556987) B4556987
theorem B2025327 : Blo 2023435 2025327 := bstep (se 1 (by rfl) ⟨1518995, by rfl⟩ : syracuseStep 2025327 = 3037991) B3037991
theorem B3037997 : Blo 2023435 3037997 := bbase (se 3 (by rfl) ⟨569624, by rfl⟩ : syracuseStep 3037997 = 1139249) (by norm_num)
theorem B2025331 : Blo 2023435 2025331 := bstep (se 1 (by rfl) ⟨1518998, by rfl⟩ : syracuseStep 2025331 = 3037997) B3037997
theorem B4557005 : Blo 2023435 4557005 := bbase (se 3 (by rfl) ⟨854438, by rfl⟩ : syracuseStep 4557005 = 1708877) (by norm_num)
theorem B3038003 : Blo 2023435 3038003 := bstep (se 1 (by rfl) ⟨2278502, by rfl⟩ : syracuseStep 3038003 = 4557005) B4557005
theorem B2025335 : Blo 2023435 2025335 := bstep (se 1 (by rfl) ⟨1519001, by rfl⟩ : syracuseStep 2025335 = 3038003) B3038003
theorem B2563321 : Blo 2023435 2563321 := bbase (se 2 (by rfl) ⟨961245, by rfl⟩ : syracuseStep 2563321 = 1922491) (by norm_num)
theorem B3417761 : Blo 2023435 3417761 := bstep (se 2 (by rfl) ⟨1281660, by rfl⟩ : syracuseStep 3417761 = 2563321) B2563321
theorem B2278507 : Blo 2023435 2278507 := bstep (se 1 (by rfl) ⟨1708880, by rfl⟩ : syracuseStep 2278507 = 3417761) B3417761
theorem B3038009 : Blo 2023435 3038009 := bstep (se 2 (by rfl) ⟨1139253, by rfl⟩ : syracuseStep 3038009 = 2278507) B2278507
theorem B2025339 : Blo 2023435 2025339 := bstep (se 1 (by rfl) ⟨1519004, by rfl⟩ : syracuseStep 2025339 = 3038009) B3038009
theorem B9732629 : Blo 2023435 9732629 := bbase (se 6 (by rfl) ⟨228108, by rfl⟩ : syracuseStep 9732629 = 456217) (by norm_num)
theorem B6488419 : Blo 2023435 6488419 := bstep (se 1 (by rfl) ⟨4866314, by rfl⟩ : syracuseStep 6488419 = 9732629) B9732629
theorem B8651225 : Blo 2023435 8651225 := bstep (se 2 (by rfl) ⟨3244209, by rfl⟩ : syracuseStep 8651225 = 6488419) B6488419
theorem B23069933 : Blo 2023435 23069933 := bstep (se 3 (by rfl) ⟨4325612, by rfl⟩ : syracuseStep 23069933 = 8651225) B8651225
theorem B15379955 : Blo 2023435 15379955 := bstep (se 1 (by rfl) ⟨11534966, by rfl⟩ : syracuseStep 15379955 = 23069933) B23069933
theorem B10253303 : Blo 2023435 10253303 := bstep (se 1 (by rfl) ⟨7689977, by rfl⟩ : syracuseStep 10253303 = 15379955) B15379955
theorem B6835535 : Blo 2023435 6835535 := bstep (se 1 (by rfl) ⟨5126651, by rfl⟩ : syracuseStep 6835535 = 10253303) B10253303
theorem B4557023 : Blo 2023435 4557023 := bstep (se 1 (by rfl) ⟨3417767, by rfl⟩ : syracuseStep 4557023 = 6835535) B6835535
theorem B3038015 : Blo 2023435 3038015 := bstep (se 1 (by rfl) ⟨2278511, by rfl⟩ : syracuseStep 3038015 = 4557023) B4557023
theorem B2025343 : Blo 2023435 2025343 := bstep (se 1 (by rfl) ⟨1519007, by rfl⟩ : syracuseStep 2025343 = 3038015) B3038015
theorem B3038021 : Blo 2023435 3038021 := bbase (se 4 (by rfl) ⟨284814, by rfl⟩ : syracuseStep 3038021 = 569629) (by norm_num)
theorem B2025347 : Blo 2023435 2025347 := bstep (se 1 (by rfl) ⟨1519010, by rfl⟩ : syracuseStep 2025347 = 3038021) B3038021
theorem B3417781 : Blo 2023435 3417781 := bbase (se 5 (by rfl) ⟨160208, by rfl⟩ : syracuseStep 3417781 = 320417) (by norm_num)
theorem B4557041 : Blo 2023435 4557041 := bstep (se 2 (by rfl) ⟨1708890, by rfl⟩ : syracuseStep 4557041 = 3417781) B3417781
theorem B3038027 : Blo 2023435 3038027 := bstep (se 1 (by rfl) ⟨2278520, by rfl⟩ : syracuseStep 3038027 = 4557041) B4557041
theorem B2025351 : Blo 2023435 2025351 := bstep (se 1 (by rfl) ⟨1519013, by rfl⟩ : syracuseStep 2025351 = 3038027) B3038027
theorem B2278525 : Blo 2023435 2278525 := bbase (se 3 (by rfl) ⟨427223, by rfl⟩ : syracuseStep 2278525 = 854447) (by norm_num)
theorem B3038033 : Blo 2023435 3038033 := bstep (se 2 (by rfl) ⟨1139262, by rfl⟩ : syracuseStep 3038033 = 2278525) B2278525
theorem B2025355 : Blo 2023435 2025355 := bstep (se 1 (by rfl) ⟨1519016, by rfl⟩ : syracuseStep 2025355 = 3038033) B3038033
theorem B6835589 : Blo 2023435 6835589 := bbase (se 4 (by rfl) ⟨640836, by rfl⟩ : syracuseStep 6835589 = 1281673) (by norm_num)
theorem B4557059 : Blo 2023435 4557059 := bstep (se 1 (by rfl) ⟨3417794, by rfl⟩ : syracuseStep 4557059 = 6835589) B6835589
theorem B3038039 : Blo 2023435 3038039 := bstep (se 1 (by rfl) ⟨2278529, by rfl⟩ : syracuseStep 3038039 = 4557059) B4557059
theorem B2025359 : Blo 2023435 2025359 := bstep (se 1 (by rfl) ⟨1519019, by rfl⟩ : syracuseStep 2025359 = 3038039) B3038039
theorem B3038045 : Blo 2023435 3038045 := bbase (se 3 (by rfl) ⟨569633, by rfl⟩ : syracuseStep 3038045 = 1139267) (by norm_num)
theorem B2025363 : Blo 2023435 2025363 := bstep (se 1 (by rfl) ⟨1519022, by rfl⟩ : syracuseStep 2025363 = 3038045) B3038045
theorem B4557077 : Blo 2023435 4557077 := bbase (se 6 (by rfl) ⟨106806, by rfl⟩ : syracuseStep 4557077 = 213613) (by norm_num)
theorem B3038051 : Blo 2023435 3038051 := bstep (se 1 (by rfl) ⟨2278538, by rfl⟩ : syracuseStep 3038051 = 4557077) B4557077
theorem B2025367 : Blo 2023435 2025367 := bstep (se 1 (by rfl) ⟨1519025, by rfl⟩ : syracuseStep 2025367 = 3038051) B3038051
theorem B7690085 : Blo 2023435 7690085 := bbase (se 4 (by rfl) ⟨720945, by rfl⟩ : syracuseStep 7690085 = 1441891) (by norm_num)
theorem B5126723 : Blo 2023435 5126723 := bstep (se 1 (by rfl) ⟨3845042, by rfl⟩ : syracuseStep 5126723 = 7690085) B7690085
theorem B3417815 : Blo 2023435 3417815 := bstep (se 1 (by rfl) ⟨2563361, by rfl⟩ : syracuseStep 3417815 = 5126723) B5126723
theorem B2278543 : Blo 2023435 2278543 := bstep (se 1 (by rfl) ⟨1708907, by rfl⟩ : syracuseStep 2278543 = 3417815) B3417815
theorem B3038057 : Blo 2023435 3038057 := bstep (se 2 (by rfl) ⟨1139271, by rfl⟩ : syracuseStep 3038057 = 2278543) B2278543
theorem B2025371 : Blo 2023435 2025371 := bstep (se 1 (by rfl) ⟨1519028, by rfl⟩ : syracuseStep 2025371 = 3038057) B3038057
theorem B3244261 : Blo 2023435 3244261 := bbase (se 4 (by rfl) ⟨304149, by rfl⟩ : syracuseStep 3244261 = 608299) (by norm_num)
theorem B4325681 : Blo 2023435 4325681 := bstep (se 2 (by rfl) ⟨1622130, by rfl⟩ : syracuseStep 4325681 = 3244261) B3244261
theorem B11535149 : Blo 2023435 11535149 := bstep (se 3 (by rfl) ⟨2162840, by rfl⟩ : syracuseStep 11535149 = 4325681) B4325681
theorem B7690099 : Blo 2023435 7690099 := bstep (se 1 (by rfl) ⟨5767574, by rfl⟩ : syracuseStep 7690099 = 11535149) B11535149
theorem B10253465 : Blo 2023435 10253465 := bstep (se 2 (by rfl) ⟨3845049, by rfl⟩ : syracuseStep 10253465 = 7690099) B7690099
theorem B6835643 : Blo 2023435 6835643 := bstep (se 1 (by rfl) ⟨5126732, by rfl⟩ : syracuseStep 6835643 = 10253465) B10253465
theorem B4557095 : Blo 2023435 4557095 := bstep (se 1 (by rfl) ⟨3417821, by rfl⟩ : syracuseStep 4557095 = 6835643) B6835643
theorem B3038063 : Blo 2023435 3038063 := bstep (se 1 (by rfl) ⟨2278547, by rfl⟩ : syracuseStep 3038063 = 4557095) B4557095
theorem B2025375 : Blo 2023435 2025375 := bstep (se 1 (by rfl) ⟨1519031, by rfl⟩ : syracuseStep 2025375 = 3038063) B3038063
theorem B3038069 : Blo 2023435 3038069 := bbase (se 5 (by rfl) ⟨142409, by rfl⟩ : syracuseStep 3038069 = 284819) (by norm_num)
theorem B2025379 : Blo 2023435 2025379 := bstep (se 1 (by rfl) ⟨1519034, by rfl⟩ : syracuseStep 2025379 = 3038069) B3038069
theorem B6488549 : Blo 2023435 6488549 := bbase (se 4 (by rfl) ⟨608301, by rfl⟩ : syracuseStep 6488549 = 1216603) (by norm_num)
theorem B4325699 : Blo 2023435 4325699 := bstep (se 1 (by rfl) ⟨3244274, by rfl⟩ : syracuseStep 4325699 = 6488549) B6488549
theorem B2883799 : Blo 2023435 2883799 := bstep (se 1 (by rfl) ⟨2162849, by rfl⟩ : syracuseStep 2883799 = 4325699) B4325699
theorem B3845065 : Blo 2023435 3845065 := bstep (se 2 (by rfl) ⟨1441899, by rfl⟩ : syracuseStep 3845065 = 2883799) B2883799
theorem B5126753 : Blo 2023435 5126753 := bstep (se 2 (by rfl) ⟨1922532, by rfl⟩ : syracuseStep 5126753 = 3845065) B3845065
theorem B3417835 : Blo 2023435 3417835 := bstep (se 1 (by rfl) ⟨2563376, by rfl⟩ : syracuseStep 3417835 = 5126753) B5126753
theorem B4557113 : Blo 2023435 4557113 := bstep (se 2 (by rfl) ⟨1708917, by rfl⟩ : syracuseStep 4557113 = 3417835) B3417835
theorem B3038075 : Blo 2023435 3038075 := bstep (se 1 (by rfl) ⟨2278556, by rfl⟩ : syracuseStep 3038075 = 4557113) B4557113
theorem B2025383 : Blo 2023435 2025383 := bstep (se 1 (by rfl) ⟨1519037, by rfl⟩ : syracuseStep 2025383 = 3038075) B3038075
theorem B2278561 : Blo 2023435 2278561 := bbase (se 2 (by rfl) ⟨854460, by rfl⟩ : syracuseStep 2278561 = 1708921) (by norm_num)
theorem B3038081 : Blo 2023435 3038081 := bstep (se 2 (by rfl) ⟨1139280, by rfl⟩ : syracuseStep 3038081 = 2278561) B2278561
theorem B2025387 : Blo 2023435 2025387 := bstep (se 1 (by rfl) ⟨1519040, by rfl⟩ : syracuseStep 2025387 = 3038081) B3038081
theorem B5126773 : Blo 2023435 5126773 := bbase (se 5 (by rfl) ⟨240317, by rfl⟩ : syracuseStep 5126773 = 480635) (by norm_num)
theorem B6835697 : Blo 2023435 6835697 := bstep (se 2 (by rfl) ⟨2563386, by rfl⟩ : syracuseStep 6835697 = 5126773) B5126773
theorem B4557131 : Blo 2023435 4557131 := bstep (se 1 (by rfl) ⟨3417848, by rfl⟩ : syracuseStep 4557131 = 6835697) B6835697
theorem B3038087 : Blo 2023435 3038087 := bstep (se 1 (by rfl) ⟨2278565, by rfl⟩ : syracuseStep 3038087 = 4557131) B4557131
theorem B2025391 : Blo 2023435 2025391 := bstep (se 1 (by rfl) ⟨1519043, by rfl⟩ : syracuseStep 2025391 = 3038087) B3038087
theorem B3038093 : Blo 2023435 3038093 := bbase (se 3 (by rfl) ⟨569642, by rfl⟩ : syracuseStep 3038093 = 1139285) (by norm_num)
theorem B2025395 : Blo 2023435 2025395 := bstep (se 1 (by rfl) ⟨1519046, by rfl⟩ : syracuseStep 2025395 = 3038093) B3038093
theorem B4557149 : Blo 2023435 4557149 := bbase (se 3 (by rfl) ⟨854465, by rfl⟩ : syracuseStep 4557149 = 1708931) (by norm_num)
theorem B3038099 : Blo 2023435 3038099 := bstep (se 1 (by rfl) ⟨2278574, by rfl⟩ : syracuseStep 3038099 = 4557149) B4557149
theorem B2025399 : Blo 2023435 2025399 := bstep (se 1 (by rfl) ⟨1519049, by rfl⟩ : syracuseStep 2025399 = 3038099) B3038099
theorem B3417869 : Blo 2023435 3417869 := bbase (se 3 (by rfl) ⟨640850, by rfl⟩ : syracuseStep 3417869 = 1281701) (by norm_num)
theorem B2278579 : Blo 2023435 2278579 := bstep (se 1 (by rfl) ⟨1708934, by rfl⟩ : syracuseStep 2278579 = 3417869) B3417869
theorem B3038105 : Blo 2023435 3038105 := bstep (se 2 (by rfl) ⟨1139289, by rfl⟩ : syracuseStep 3038105 = 2278579) B2278579
theorem B2025403 : Blo 2023435 2025403 := bstep (se 1 (by rfl) ⟨1519052, by rfl⟩ : syracuseStep 2025403 = 3038105) B3038105
theorem B17302997 : Blo 2023435 17302997 := bbase (se 7 (by rfl) ⟨202769, by rfl⟩ : syracuseStep 17302997 = 405539) (by norm_num)
theorem B11535331 : Blo 2023435 11535331 := bstep (se 1 (by rfl) ⟨8651498, by rfl⟩ : syracuseStep 11535331 = 17302997) B17302997
theorem B15380441 : Blo 2023435 15380441 := bstep (se 2 (by rfl) ⟨5767665, by rfl⟩ : syracuseStep 15380441 = 11535331) B11535331
theorem B10253627 : Blo 2023435 10253627 := bstep (se 1 (by rfl) ⟨7690220, by rfl⟩ : syracuseStep 10253627 = 15380441) B15380441
theorem B6835751 : Blo 2023435 6835751 := bstep (se 1 (by rfl) ⟨5126813, by rfl⟩ : syracuseStep 6835751 = 10253627) B10253627
theorem B4557167 : Blo 2023435 4557167 := bstep (se 1 (by rfl) ⟨3417875, by rfl⟩ : syracuseStep 4557167 = 6835751) B6835751
theorem B3038111 : Blo 2023435 3038111 := bstep (se 1 (by rfl) ⟨2278583, by rfl⟩ : syracuseStep 3038111 = 4557167) B4557167
theorem B2025407 : Blo 2023435 2025407 := bstep (se 1 (by rfl) ⟨1519055, by rfl⟩ : syracuseStep 2025407 = 3038111) B3038111
theorem B3038117 : Blo 2023435 3038117 := bbase (se 4 (by rfl) ⟨284823, by rfl⟩ : syracuseStep 3038117 = 569647) (by norm_num)
theorem B2025411 : Blo 2023435 2025411 := bstep (se 1 (by rfl) ⟨1519058, by rfl⟩ : syracuseStep 2025411 = 3038117) B3038117
theorem B2563417 : Blo 2023435 2563417 := bbase (se 2 (by rfl) ⟨961281, by rfl⟩ : syracuseStep 2563417 = 1922563) (by norm_num)
theorem B3417889 : Blo 2023435 3417889 := bstep (se 2 (by rfl) ⟨1281708, by rfl⟩ : syracuseStep 3417889 = 2563417) B2563417
theorem B4557185 : Blo 2023435 4557185 := bstep (se 2 (by rfl) ⟨1708944, by rfl⟩ : syracuseStep 4557185 = 3417889) B3417889
theorem B3038123 : Blo 2023435 3038123 := bstep (se 1 (by rfl) ⟨2278592, by rfl⟩ : syracuseStep 3038123 = 4557185) B4557185
theorem B2025415 : Blo 2023435 2025415 := bstep (se 1 (by rfl) ⟨1519061, by rfl⟩ : syracuseStep 2025415 = 3038123) B3038123
theorem B2278597 : Blo 2023435 2278597 := bbase (se 4 (by rfl) ⟨213618, by rfl⟩ : syracuseStep 2278597 = 427237) (by norm_num)
theorem B3038129 : Blo 2023435 3038129 := bstep (se 2 (by rfl) ⟨1139298, by rfl⟩ : syracuseStep 3038129 = 2278597) B2278597
theorem B2025419 : Blo 2023435 2025419 := bstep (se 1 (by rfl) ⟨1519064, by rfl⟩ : syracuseStep 2025419 = 3038129) B3038129
theorem B3845141 : Blo 2023435 3845141 := bbase (se 6 (by rfl) ⟨90120, by rfl⟩ : syracuseStep 3845141 = 180241) (by norm_num)
theorem B2563427 : Blo 2023435 2563427 := bstep (se 1 (by rfl) ⟨1922570, by rfl⟩ : syracuseStep 2563427 = 3845141) B3845141
theorem B6835805 : Blo 2023435 6835805 := bstep (se 3 (by rfl) ⟨1281713, by rfl⟩ : syracuseStep 6835805 = 2563427) B2563427
theorem B4557203 : Blo 2023435 4557203 := bstep (se 1 (by rfl) ⟨3417902, by rfl⟩ : syracuseStep 4557203 = 6835805) B6835805
theorem B3038135 : Blo 2023435 3038135 := bstep (se 1 (by rfl) ⟨2278601, by rfl⟩ : syracuseStep 3038135 = 4557203) B4557203
theorem B2025423 : Blo 2023435 2025423 := bstep (se 1 (by rfl) ⟨1519067, by rfl⟩ : syracuseStep 2025423 = 3038135) B3038135
theorem B3038141 : Blo 2023435 3038141 := bbase (se 3 (by rfl) ⟨569651, by rfl⟩ : syracuseStep 3038141 = 1139303) (by norm_num)
theorem B2025427 : Blo 2023435 2025427 := bstep (se 1 (by rfl) ⟨1519070, by rfl⟩ : syracuseStep 2025427 = 3038141) B3038141
theorem B4557221 : Blo 2023435 4557221 := bbase (se 4 (by rfl) ⟨427239, by rfl⟩ : syracuseStep 4557221 = 854479) (by norm_num)
theorem B3038147 : Blo 2023435 3038147 := bstep (se 1 (by rfl) ⟨2278610, by rfl⟩ : syracuseStep 3038147 = 4557221) B4557221
theorem B2025431 : Blo 2023435 2025431 := bstep (se 1 (by rfl) ⟨1519073, by rfl⟩ : syracuseStep 2025431 = 3038147) B3038147
theorem B5126885 : Blo 2023435 5126885 := bbase (se 4 (by rfl) ⟨480645, by rfl⟩ : syracuseStep 5126885 = 961291) (by norm_num)
theorem B3417923 : Blo 2023435 3417923 := bstep (se 1 (by rfl) ⟨2563442, by rfl⟩ : syracuseStep 3417923 = 5126885) B5126885
theorem B2278615 : Blo 2023435 2278615 := bstep (se 1 (by rfl) ⟨1708961, by rfl⟩ : syracuseStep 2278615 = 3417923) B3417923
theorem B3038153 : Blo 2023435 3038153 := bstep (se 2 (by rfl) ⟨1139307, by rfl⟩ : syracuseStep 3038153 = 2278615) B2278615
theorem B2025435 : Blo 2023435 2025435 := bstep (se 1 (by rfl) ⟨1519076, by rfl⟩ : syracuseStep 2025435 = 3038153) B3038153
theorem C0 (j : ℕ) (h1 : 505858 ≤ j) (h2 : j ≤ 506358) : Blo 2023435 (4 * j + 3) := by
  interval_cases j
  · exact B2023435
  · exact B2023439
  · exact B2023443
  · exact B2023447
  · exact B2023451
  · exact B2023455
  · exact B2023459
  · exact B2023463
  · exact B2023467
  · exact B2023471
  · exact B2023475
  · exact B2023479
  · exact B2023483
  · exact B2023487
  · exact B2023491
  · exact B2023495
  · exact B2023499
  · exact B2023503
  · exact B2023507
  · exact B2023511
  · exact B2023515
  · exact B2023519
  · exact B2023523
  · exact B2023527
  · exact B2023531
  · exact B2023535
  · exact B2023539
  · exact B2023543
  · exact B2023547
  · exact B2023551
  · exact B2023555
  · exact B2023559
  · exact B2023563
  · exact B2023567
  · exact B2023571
  · exact B2023575
  · exact B2023579
  · exact B2023583
  · exact B2023587
  · exact B2023591
  · exact B2023595
  · exact B2023599
  · exact B2023603
  · exact B2023607
  · exact B2023611
  · exact B2023615
  · exact B2023619
  · exact B2023623
  · exact B2023627
  · exact B2023631
  · exact B2023635
  · exact B2023639
  · exact B2023643
  · exact B2023647
  · exact B2023651
  · exact B2023655
  · exact B2023659
  · exact B2023663
  · exact B2023667
  · exact B2023671
  · exact B2023675
  · exact B2023679
  · exact B2023683
  · exact B2023687
  · exact B2023691
  · exact B2023695
  · exact B2023699
  · exact B2023703
  · exact B2023707
  · exact B2023711
  · exact B2023715
  · exact B2023719
  · exact B2023723
  · exact B2023727
  · exact B2023731
  · exact B2023735
  · exact B2023739
  · exact B2023743
  · exact B2023747
  · exact B2023751
  · exact B2023755
  · exact B2023759
  · exact B2023763
  · exact B2023767
  · exact B2023771
  · exact B2023775
  · exact B2023779
  · exact B2023783
  · exact B2023787
  · exact B2023791
  · exact B2023795
  · exact B2023799
  · exact B2023803
  · exact B2023807
  · exact B2023811
  · exact B2023815
  · exact B2023819
  · exact B2023823
  · exact B2023827
  · exact B2023831
  · exact B2023835
  · exact B2023839
  · exact B2023843
  · exact B2023847
  · exact B2023851
  · exact B2023855
  · exact B2023859
  · exact B2023863
  · exact B2023867
  · exact B2023871
  · exact B2023875
  · exact B2023879
  · exact B2023883
  · exact B2023887
  · exact B2023891
  · exact B2023895
  · exact B2023899
  · exact B2023903
  · exact B2023907
  · exact B2023911
  · exact B2023915
  · exact B2023919
  · exact B2023923
  · exact B2023927
  · exact B2023931
  · exact B2023935
  · exact B2023939
  · exact B2023943
  · exact B2023947
  · exact B2023951
  · exact B2023955
  · exact B2023959
  · exact B2023963
  · exact B2023967
  · exact B2023971
  · exact B2023975
  · exact B2023979
  · exact B2023983
  · exact B2023987
  · exact B2023991
  · exact B2023995
  · exact B2023999
  · exact B2024003
  · exact B2024007
  · exact B2024011
  · exact B2024015
  · exact B2024019
  · exact B2024023
  · exact B2024027
  · exact B2024031
  · exact B2024035
  · exact B2024039
  · exact B2024043
  · exact B2024047
  · exact B2024051
  · exact B2024055
  · exact B2024059
  · exact B2024063
  · exact B2024067
  · exact B2024071
  · exact B2024075
  · exact B2024079
  · exact B2024083
  · exact B2024087
  · exact B2024091
  · exact B2024095
  · exact B2024099
  · exact B2024103
  · exact B2024107
  · exact B2024111
  · exact B2024115
  · exact B2024119
  · exact B2024123
  · exact B2024127
  · exact B2024131
  · exact B2024135
  · exact B2024139
  · exact B2024143
  · exact B2024147
  · exact B2024151
  · exact B2024155
  · exact B2024159
  · exact B2024163
  · exact B2024167
  · exact B2024171
  · exact B2024175
  · exact B2024179
  · exact B2024183
  · exact B2024187
  · exact B2024191
  · exact B2024195
  · exact B2024199
  · exact B2024203
  · exact B2024207
  · exact B2024211
  · exact B2024215
  · exact B2024219
  · exact B2024223
  · exact B2024227
  · exact B2024231
  · exact B2024235
  · exact B2024239
  · exact B2024243
  · exact B2024247
  · exact B2024251
  · exact B2024255
  · exact B2024259
  · exact B2024263
  · exact B2024267
  · exact B2024271
  · exact B2024275
  · exact B2024279
  · exact B2024283
  · exact B2024287
  · exact B2024291
  · exact B2024295
  · exact B2024299
  · exact B2024303
  · exact B2024307
  · exact B2024311
  · exact B2024315
  · exact B2024319
  · exact B2024323
  · exact B2024327
  · exact B2024331
  · exact B2024335
  · exact B2024339
  · exact B2024343
  · exact B2024347
  · exact B2024351
  · exact B2024355
  · exact B2024359
  · exact B2024363
  · exact B2024367
  · exact B2024371
  · exact B2024375
  · exact B2024379
  · exact B2024383
  · exact B2024387
  · exact B2024391
  · exact B2024395
  · exact B2024399
  · exact B2024403
  · exact B2024407
  · exact B2024411
  · exact B2024415
  · exact B2024419
  · exact B2024423
  · exact B2024427
  · exact B2024431
  · exact B2024435
  · exact B2024439
  · exact B2024443
  · exact B2024447
  · exact B2024451
  · exact B2024455
  · exact B2024459
  · exact B2024463
  · exact B2024467
  · exact B2024471
  · exact B2024475
  · exact B2024479
  · exact B2024483
  · exact B2024487
  · exact B2024491
  · exact B2024495
  · exact B2024499
  · exact B2024503
  · exact B2024507
  · exact B2024511
  · exact B2024515
  · exact B2024519
  · exact B2024523
  · exact B2024527
  · exact B2024531
  · exact B2024535
  · exact B2024539
  · exact B2024543
  · exact B2024547
  · exact B2024551
  · exact B2024555
  · exact B2024559
  · exact B2024563
  · exact B2024567
  · exact B2024571
  · exact B2024575
  · exact B2024579
  · exact B2024583
  · exact B2024587
  · exact B2024591
  · exact B2024595
  · exact B2024599
  · exact B2024603
  · exact B2024607
  · exact B2024611
  · exact B2024615
  · exact B2024619
  · exact B2024623
  · exact B2024627
  · exact B2024631
  · exact B2024635
  · exact B2024639
  · exact B2024643
  · exact B2024647
  · exact B2024651
  · exact B2024655
  · exact B2024659
  · exact B2024663
  · exact B2024667
  · exact B2024671
  · exact B2024675
  · exact B2024679
  · exact B2024683
  · exact B2024687
  · exact B2024691
  · exact B2024695
  · exact B2024699
  · exact B2024703
  · exact B2024707
  · exact B2024711
  · exact B2024715
  · exact B2024719
  · exact B2024723
  · exact B2024727
  · exact B2024731
  · exact B2024735
  · exact B2024739
  · exact B2024743
  · exact B2024747
  · exact B2024751
  · exact B2024755
  · exact B2024759
  · exact B2024763
  · exact B2024767
  · exact B2024771
  · exact B2024775
  · exact B2024779
  · exact B2024783
  · exact B2024787
  · exact B2024791
  · exact B2024795
  · exact B2024799
  · exact B2024803
  · exact B2024807
  · exact B2024811
  · exact B2024815
  · exact B2024819
  · exact B2024823
  · exact B2024827
  · exact B2024831
  · exact B2024835
  · exact B2024839
  · exact B2024843
  · exact B2024847
  · exact B2024851
  · exact B2024855
  · exact B2024859
  · exact B2024863
  · exact B2024867
  · exact B2024871
  · exact B2024875
  · exact B2024879
  · exact B2024883
  · exact B2024887
  · exact B2024891
  · exact B2024895
  · exact B2024899
  · exact B2024903
  · exact B2024907
  · exact B2024911
  · exact B2024915
  · exact B2024919
  · exact B2024923
  · exact B2024927
  · exact B2024931
  · exact B2024935
  · exact B2024939
  · exact B2024943
  · exact B2024947
  · exact B2024951
  · exact B2024955
  · exact B2024959
  · exact B2024963
  · exact B2024967
  · exact B2024971
  · exact B2024975
  · exact B2024979
  · exact B2024983
  · exact B2024987
  · exact B2024991
  · exact B2024995
  · exact B2024999
  · exact B2025003
  · exact B2025007
  · exact B2025011
  · exact B2025015
  · exact B2025019
  · exact B2025023
  · exact B2025027
  · exact B2025031
  · exact B2025035
  · exact B2025039
  · exact B2025043
  · exact B2025047
  · exact B2025051
  · exact B2025055
  · exact B2025059
  · exact B2025063
  · exact B2025067
  · exact B2025071
  · exact B2025075
  · exact B2025079
  · exact B2025083
  · exact B2025087
  · exact B2025091
  · exact B2025095
  · exact B2025099
  · exact B2025103
  · exact B2025107
  · exact B2025111
  · exact B2025115
  · exact B2025119
  · exact B2025123
  · exact B2025127
  · exact B2025131
  · exact B2025135
  · exact B2025139
  · exact B2025143
  · exact B2025147
  · exact B2025151
  · exact B2025155
  · exact B2025159
  · exact B2025163
  · exact B2025167
  · exact B2025171
  · exact B2025175
  · exact B2025179
  · exact B2025183
  · exact B2025187
  · exact B2025191
  · exact B2025195
  · exact B2025199
  · exact B2025203
  · exact B2025207
  · exact B2025211
  · exact B2025215
  · exact B2025219
  · exact B2025223
  · exact B2025227
  · exact B2025231
  · exact B2025235
  · exact B2025239
  · exact B2025243
  · exact B2025247
  · exact B2025251
  · exact B2025255
  · exact B2025259
  · exact B2025263
  · exact B2025267
  · exact B2025271
  · exact B2025275
  · exact B2025279
  · exact B2025283
  · exact B2025287
  · exact B2025291
  · exact B2025295
  · exact B2025299
  · exact B2025303
  · exact B2025307
  · exact B2025311
  · exact B2025315
  · exact B2025319
  · exact B2025323
  · exact B2025327
  · exact B2025331
  · exact B2025335
  · exact B2025339
  · exact B2025343
  · exact B2025347
  · exact B2025351
  · exact B2025355
  · exact B2025359
  · exact B2025363
  · exact B2025367
  · exact B2025371
  · exact B2025375
  · exact B2025379
  · exact B2025383
  · exact B2025387
  · exact B2025391
  · exact B2025395
  · exact B2025399
  · exact B2025403
  · exact B2025407
  · exact B2025411
  · exact B2025415
  · exact B2025419
  · exact B2025423
  · exact B2025427
  · exact B2025431
  · exact B2025435
theorem solution (m : ℕ) (hlo : 2023435 ≤ m) (hhi : m ≤ 2025435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 505858 ≤ j := by omega
    have hj2 : j ≤ 506358 := by omega
    have hb : Blo 2023435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
