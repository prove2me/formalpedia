-- Prove2me | solution 1 for syracuse_descends_range_2039435_2041435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:49:14.773176+00:00
-- url     : https://prove2.me/submissions/f4dd5446-bf24-464d-ad8f-d19ed09f9eaa

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

theorem B2294365 : Blo 2039435 2294365 := bbase (se 3 (by rfl) ⟨430193, by rfl⟩ : syracuseStep 2294365 = 860387) (by norm_num)
theorem B3059153 : Blo 2039435 3059153 := bstep (se 2 (by rfl) ⟨1147182, by rfl⟩ : syracuseStep 3059153 = 2294365) B2294365
theorem B2039435 : Blo 2039435 2039435 := bstep (se 1 (by rfl) ⟨1529576, by rfl⟩ : syracuseStep 2039435 = 3059153) B3059153
theorem B6883109 : Blo 2039435 6883109 := bbase (se 4 (by rfl) ⟨645291, by rfl⟩ : syracuseStep 6883109 = 1290583) (by norm_num)
theorem B4588739 : Blo 2039435 4588739 := bstep (se 1 (by rfl) ⟨3441554, by rfl⟩ : syracuseStep 4588739 = 6883109) B6883109
theorem B3059159 : Blo 2039435 3059159 := bstep (se 1 (by rfl) ⟨2294369, by rfl⟩ : syracuseStep 3059159 = 4588739) B4588739
theorem B2039439 : Blo 2039435 2039439 := bstep (se 1 (by rfl) ⟨1529579, by rfl⟩ : syracuseStep 2039439 = 3059159) B3059159
theorem B3059165 : Blo 2039435 3059165 := bbase (se 3 (by rfl) ⟨573593, by rfl⟩ : syracuseStep 3059165 = 1147187) (by norm_num)
theorem B2039443 : Blo 2039435 2039443 := bstep (se 1 (by rfl) ⟨1529582, by rfl⟩ : syracuseStep 2039443 = 3059165) B3059165
theorem B4588757 : Blo 2039435 4588757 := bbase (se 7 (by rfl) ⟨53774, by rfl⟩ : syracuseStep 4588757 = 107549) (by norm_num)
theorem B3059171 : Blo 2039435 3059171 := bstep (se 1 (by rfl) ⟨2294378, by rfl⟩ : syracuseStep 3059171 = 4588757) B4588757
theorem B2039447 : Blo 2039435 2039447 := bstep (se 1 (by rfl) ⟨1529585, by rfl⟩ : syracuseStep 2039447 = 3059171) B3059171
theorem B4900213 : Blo 2039435 4900213 := bbase (se 5 (by rfl) ⟨229697, by rfl⟩ : syracuseStep 4900213 = 459395) (by norm_num)
theorem B6533617 : Blo 2039435 6533617 := bstep (se 2 (by rfl) ⟨2450106, by rfl⟩ : syracuseStep 6533617 = 4900213) B4900213
theorem B8711489 : Blo 2039435 8711489 := bstep (se 2 (by rfl) ⟨3266808, by rfl⟩ : syracuseStep 8711489 = 6533617) B6533617
theorem B5807659 : Blo 2039435 5807659 := bstep (se 1 (by rfl) ⟨4355744, by rfl⟩ : syracuseStep 5807659 = 8711489) B8711489
theorem B7743545 : Blo 2039435 7743545 := bstep (se 2 (by rfl) ⟨2903829, by rfl⟩ : syracuseStep 7743545 = 5807659) B5807659
theorem B5162363 : Blo 2039435 5162363 := bstep (se 1 (by rfl) ⟨3871772, by rfl⟩ : syracuseStep 5162363 = 7743545) B7743545
theorem B3441575 : Blo 2039435 3441575 := bstep (se 1 (by rfl) ⟨2581181, by rfl⟩ : syracuseStep 3441575 = 5162363) B5162363
theorem B2294383 : Blo 2039435 2294383 := bstep (se 1 (by rfl) ⟨1720787, by rfl⟩ : syracuseStep 2294383 = 3441575) B3441575
theorem B3059177 : Blo 2039435 3059177 := bstep (se 2 (by rfl) ⟨1147191, by rfl⟩ : syracuseStep 3059177 = 2294383) B2294383
theorem B2039451 : Blo 2039435 2039451 := bstep (se 1 (by rfl) ⟨1529588, by rfl⟩ : syracuseStep 2039451 = 3059177) B3059177
theorem B47095253 : Blo 2039435 47095253 := bbase (se 7 (by rfl) ⟨551897, by rfl⟩ : syracuseStep 47095253 = 1103795) (by norm_num)
theorem B31396835 : Blo 2039435 31396835 := bstep (se 1 (by rfl) ⟨23547626, by rfl⟩ : syracuseStep 31396835 = 47095253) B47095253
theorem B20931223 : Blo 2039435 20931223 := bstep (se 1 (by rfl) ⟨15698417, by rfl⟩ : syracuseStep 20931223 = 31396835) B31396835
theorem B27908297 : Blo 2039435 27908297 := bstep (se 2 (by rfl) ⟨10465611, by rfl⟩ : syracuseStep 27908297 = 20931223) B20931223
theorem B18605531 : Blo 2039435 18605531 := bstep (se 1 (by rfl) ⟨13954148, by rfl⟩ : syracuseStep 18605531 = 27908297) B27908297
theorem B12403687 : Blo 2039435 12403687 := bstep (se 1 (by rfl) ⟨9302765, by rfl⟩ : syracuseStep 12403687 = 18605531) B18605531
theorem B16538249 : Blo 2039435 16538249 := bstep (se 2 (by rfl) ⟨6201843, by rfl⟩ : syracuseStep 16538249 = 12403687) B12403687
theorem B11025499 : Blo 2039435 11025499 := bstep (se 1 (by rfl) ⟨8269124, by rfl⟩ : syracuseStep 11025499 = 16538249) B16538249
theorem B14700665 : Blo 2039435 14700665 := bstep (se 2 (by rfl) ⟨5512749, by rfl⟩ : syracuseStep 14700665 = 11025499) B11025499
theorem B9800443 : Blo 2039435 9800443 := bstep (se 1 (by rfl) ⟨7350332, by rfl⟩ : syracuseStep 9800443 = 14700665) B14700665
theorem B13067257 : Blo 2039435 13067257 := bstep (se 2 (by rfl) ⟨4900221, by rfl⟩ : syracuseStep 13067257 = 9800443) B9800443
theorem B17423009 : Blo 2039435 17423009 := bstep (se 2 (by rfl) ⟨6533628, by rfl⟩ : syracuseStep 17423009 = 13067257) B13067257
theorem B11615339 : Blo 2039435 11615339 := bstep (se 1 (by rfl) ⟨8711504, by rfl⟩ : syracuseStep 11615339 = 17423009) B17423009
theorem B7743559 : Blo 2039435 7743559 := bstep (se 1 (by rfl) ⟨5807669, by rfl⟩ : syracuseStep 7743559 = 11615339) B11615339
theorem B10324745 : Blo 2039435 10324745 := bstep (se 2 (by rfl) ⟨3871779, by rfl⟩ : syracuseStep 10324745 = 7743559) B7743559
theorem B6883163 : Blo 2039435 6883163 := bstep (se 1 (by rfl) ⟨5162372, by rfl⟩ : syracuseStep 6883163 = 10324745) B10324745
theorem B4588775 : Blo 2039435 4588775 := bstep (se 1 (by rfl) ⟨3441581, by rfl⟩ : syracuseStep 4588775 = 6883163) B6883163
theorem B3059183 : Blo 2039435 3059183 := bstep (se 1 (by rfl) ⟨2294387, by rfl⟩ : syracuseStep 3059183 = 4588775) B4588775
theorem B2039455 : Blo 2039435 2039455 := bstep (se 1 (by rfl) ⟨1529591, by rfl⟩ : syracuseStep 2039455 = 3059183) B3059183
theorem B3059189 : Blo 2039435 3059189 := bbase (se 5 (by rfl) ⟨143399, by rfl⟩ : syracuseStep 3059189 = 286799) (by norm_num)
theorem B2039459 : Blo 2039435 2039459 := bstep (se 1 (by rfl) ⟨1529594, by rfl⟩ : syracuseStep 2039459 = 3059189) B3059189
theorem B2177885 : Blo 2039435 2177885 := bbase (se 3 (by rfl) ⟨408353, by rfl⟩ : syracuseStep 2177885 = 816707) (by norm_num)
theorem B5807693 : Blo 2039435 5807693 := bstep (se 3 (by rfl) ⟨1088942, by rfl⟩ : syracuseStep 5807693 = 2177885) B2177885
theorem B3871795 : Blo 2039435 3871795 := bstep (se 1 (by rfl) ⟨2903846, by rfl⟩ : syracuseStep 3871795 = 5807693) B5807693
theorem B5162393 : Blo 2039435 5162393 := bstep (se 2 (by rfl) ⟨1935897, by rfl⟩ : syracuseStep 5162393 = 3871795) B3871795
theorem B3441595 : Blo 2039435 3441595 := bstep (se 1 (by rfl) ⟨2581196, by rfl⟩ : syracuseStep 3441595 = 5162393) B5162393
theorem B4588793 : Blo 2039435 4588793 := bstep (se 2 (by rfl) ⟨1720797, by rfl⟩ : syracuseStep 4588793 = 3441595) B3441595
theorem B3059195 : Blo 2039435 3059195 := bstep (se 1 (by rfl) ⟨2294396, by rfl⟩ : syracuseStep 3059195 = 4588793) B4588793
theorem B2039463 : Blo 2039435 2039463 := bstep (se 1 (by rfl) ⟨1529597, by rfl⟩ : syracuseStep 2039463 = 3059195) B3059195
theorem B2294401 : Blo 2039435 2294401 := bbase (se 2 (by rfl) ⟨860400, by rfl⟩ : syracuseStep 2294401 = 1720801) (by norm_num)
theorem B3059201 : Blo 2039435 3059201 := bstep (se 2 (by rfl) ⟨1147200, by rfl⟩ : syracuseStep 3059201 = 2294401) B2294401
theorem B2039467 : Blo 2039435 2039467 := bstep (se 1 (by rfl) ⟨1529600, by rfl⟩ : syracuseStep 2039467 = 3059201) B3059201
theorem B5162413 : Blo 2039435 5162413 := bbase (se 3 (by rfl) ⟨967952, by rfl⟩ : syracuseStep 5162413 = 1935905) (by norm_num)
theorem B6883217 : Blo 2039435 6883217 := bstep (se 2 (by rfl) ⟨2581206, by rfl⟩ : syracuseStep 6883217 = 5162413) B5162413
theorem B4588811 : Blo 2039435 4588811 := bstep (se 1 (by rfl) ⟨3441608, by rfl⟩ : syracuseStep 4588811 = 6883217) B6883217
theorem B3059207 : Blo 2039435 3059207 := bstep (se 1 (by rfl) ⟨2294405, by rfl⟩ : syracuseStep 3059207 = 4588811) B4588811
theorem B2039471 : Blo 2039435 2039471 := bstep (se 1 (by rfl) ⟨1529603, by rfl⟩ : syracuseStep 2039471 = 3059207) B3059207
theorem B3059213 : Blo 2039435 3059213 := bbase (se 3 (by rfl) ⟨573602, by rfl⟩ : syracuseStep 3059213 = 1147205) (by norm_num)
theorem B2039475 : Blo 2039435 2039475 := bstep (se 1 (by rfl) ⟨1529606, by rfl⟩ : syracuseStep 2039475 = 3059213) B3059213
theorem B4588829 : Blo 2039435 4588829 := bbase (se 3 (by rfl) ⟨860405, by rfl⟩ : syracuseStep 4588829 = 1720811) (by norm_num)
theorem B3059219 : Blo 2039435 3059219 := bstep (se 1 (by rfl) ⟨2294414, by rfl⟩ : syracuseStep 3059219 = 4588829) B4588829
theorem B2039479 : Blo 2039435 2039479 := bstep (se 1 (by rfl) ⟨1529609, by rfl⟩ : syracuseStep 2039479 = 3059219) B3059219
theorem B3441629 : Blo 2039435 3441629 := bbase (se 3 (by rfl) ⟨645305, by rfl⟩ : syracuseStep 3441629 = 1290611) (by norm_num)
theorem B2294419 : Blo 2039435 2294419 := bstep (se 1 (by rfl) ⟨1720814, by rfl⟩ : syracuseStep 2294419 = 3441629) B3441629
theorem B3059225 : Blo 2039435 3059225 := bstep (se 2 (by rfl) ⟨1147209, by rfl⟩ : syracuseStep 3059225 = 2294419) B2294419
theorem B2039483 : Blo 2039435 2039483 := bstep (se 1 (by rfl) ⟨1529612, by rfl⟩ : syracuseStep 2039483 = 3059225) B3059225
theorem B9800597 : Blo 2039435 9800597 := bbase (se 6 (by rfl) ⟨229701, by rfl⟩ : syracuseStep 9800597 = 459403) (by norm_num)
theorem B6533731 : Blo 2039435 6533731 := bstep (se 1 (by rfl) ⟨4900298, by rfl⟩ : syracuseStep 6533731 = 9800597) B9800597
theorem B8711641 : Blo 2039435 8711641 := bstep (se 2 (by rfl) ⟨3266865, by rfl⟩ : syracuseStep 8711641 = 6533731) B6533731
theorem B11615521 : Blo 2039435 11615521 := bstep (se 2 (by rfl) ⟨4355820, by rfl⟩ : syracuseStep 11615521 = 8711641) B8711641
theorem B15487361 : Blo 2039435 15487361 := bstep (se 2 (by rfl) ⟨5807760, by rfl⟩ : syracuseStep 15487361 = 11615521) B11615521
theorem B10324907 : Blo 2039435 10324907 := bstep (se 1 (by rfl) ⟨7743680, by rfl⟩ : syracuseStep 10324907 = 15487361) B15487361
theorem B6883271 : Blo 2039435 6883271 := bstep (se 1 (by rfl) ⟨5162453, by rfl⟩ : syracuseStep 6883271 = 10324907) B10324907
theorem B4588847 : Blo 2039435 4588847 := bstep (se 1 (by rfl) ⟨3441635, by rfl⟩ : syracuseStep 4588847 = 6883271) B6883271
theorem B3059231 : Blo 2039435 3059231 := bstep (se 1 (by rfl) ⟨2294423, by rfl⟩ : syracuseStep 3059231 = 4588847) B4588847
theorem B2039487 : Blo 2039435 2039487 := bstep (se 1 (by rfl) ⟨1529615, by rfl⟩ : syracuseStep 2039487 = 3059231) B3059231
theorem B3059237 : Blo 2039435 3059237 := bbase (se 4 (by rfl) ⟨286803, by rfl⟩ : syracuseStep 3059237 = 573607) (by norm_num)
theorem B2039491 : Blo 2039435 2039491 := bstep (se 1 (by rfl) ⟨1529618, by rfl⟩ : syracuseStep 2039491 = 3059237) B3059237
theorem B2581237 : Blo 2039435 2581237 := bbase (se 5 (by rfl) ⟨120995, by rfl⟩ : syracuseStep 2581237 = 241991) (by norm_num)
theorem B3441649 : Blo 2039435 3441649 := bstep (se 2 (by rfl) ⟨1290618, by rfl⟩ : syracuseStep 3441649 = 2581237) B2581237
theorem B4588865 : Blo 2039435 4588865 := bstep (se 2 (by rfl) ⟨1720824, by rfl⟩ : syracuseStep 4588865 = 3441649) B3441649
theorem B3059243 : Blo 2039435 3059243 := bstep (se 1 (by rfl) ⟨2294432, by rfl⟩ : syracuseStep 3059243 = 4588865) B4588865
theorem B2039495 : Blo 2039435 2039495 := bstep (se 1 (by rfl) ⟨1529621, by rfl⟩ : syracuseStep 2039495 = 3059243) B3059243
theorem B2294437 : Blo 2039435 2294437 := bbase (se 4 (by rfl) ⟨215103, by rfl⟩ : syracuseStep 2294437 = 430207) (by norm_num)
theorem B3059249 : Blo 2039435 3059249 := bstep (se 2 (by rfl) ⟨1147218, by rfl⟩ : syracuseStep 3059249 = 2294437) B2294437
theorem B2039499 : Blo 2039435 2039499 := bstep (se 1 (by rfl) ⟨1529624, by rfl⟩ : syracuseStep 2039499 = 3059249) B3059249
theorem B4415285 : Blo 2039435 4415285 := bbase (se 5 (by rfl) ⟨206966, by rfl⟩ : syracuseStep 4415285 = 413933) (by norm_num)
theorem B2943523 : Blo 2039435 2943523 := bstep (se 1 (by rfl) ⟨2207642, by rfl⟩ : syracuseStep 2943523 = 4415285) B4415285
theorem B15698789 : Blo 2039435 15698789 := bstep (se 4 (by rfl) ⟨1471761, by rfl⟩ : syracuseStep 15698789 = 2943523) B2943523
theorem B10465859 : Blo 2039435 10465859 := bstep (se 1 (by rfl) ⟨7849394, by rfl⟩ : syracuseStep 10465859 = 15698789) B15698789
theorem B27908957 : Blo 2039435 27908957 := bstep (se 3 (by rfl) ⟨5232929, by rfl⟩ : syracuseStep 27908957 = 10465859) B10465859
theorem B18605971 : Blo 2039435 18605971 := bstep (se 1 (by rfl) ⟨13954478, by rfl⟩ : syracuseStep 18605971 = 27908957) B27908957
theorem B24807961 : Blo 2039435 24807961 := bstep (se 2 (by rfl) ⟨9302985, by rfl⟩ : syracuseStep 24807961 = 18605971) B18605971
theorem B33077281 : Blo 2039435 33077281 := bstep (se 2 (by rfl) ⟨12403980, by rfl⟩ : syracuseStep 33077281 = 24807961) B24807961
theorem B44103041 : Blo 2039435 44103041 := bstep (se 2 (by rfl) ⟨16538640, by rfl⟩ : syracuseStep 44103041 = 33077281) B33077281
theorem B29402027 : Blo 2039435 29402027 := bstep (se 1 (by rfl) ⟨22051520, by rfl⟩ : syracuseStep 29402027 = 44103041) B44103041
theorem B19601351 : Blo 2039435 19601351 := bstep (se 1 (by rfl) ⟨14701013, by rfl⟩ : syracuseStep 19601351 = 29402027) B29402027
theorem B13067567 : Blo 2039435 13067567 := bstep (se 1 (by rfl) ⟨9800675, by rfl⟩ : syracuseStep 13067567 = 19601351) B19601351
theorem B8711711 : Blo 2039435 8711711 := bstep (se 1 (by rfl) ⟨6533783, by rfl⟩ : syracuseStep 8711711 = 13067567) B13067567
theorem B5807807 : Blo 2039435 5807807 := bstep (se 1 (by rfl) ⟨4355855, by rfl⟩ : syracuseStep 5807807 = 8711711) B8711711
theorem B3871871 : Blo 2039435 3871871 := bstep (se 1 (by rfl) ⟨2903903, by rfl⟩ : syracuseStep 3871871 = 5807807) B5807807
theorem B2581247 : Blo 2039435 2581247 := bstep (se 1 (by rfl) ⟨1935935, by rfl⟩ : syracuseStep 2581247 = 3871871) B3871871
theorem B6883325 : Blo 2039435 6883325 := bstep (se 3 (by rfl) ⟨1290623, by rfl⟩ : syracuseStep 6883325 = 2581247) B2581247
theorem B4588883 : Blo 2039435 4588883 := bstep (se 1 (by rfl) ⟨3441662, by rfl⟩ : syracuseStep 4588883 = 6883325) B6883325
theorem B3059255 : Blo 2039435 3059255 := bstep (se 1 (by rfl) ⟨2294441, by rfl⟩ : syracuseStep 3059255 = 4588883) B4588883
theorem B2039503 : Blo 2039435 2039503 := bstep (se 1 (by rfl) ⟨1529627, by rfl⟩ : syracuseStep 2039503 = 3059255) B3059255
theorem B3059261 : Blo 2039435 3059261 := bbase (se 3 (by rfl) ⟨573611, by rfl⟩ : syracuseStep 3059261 = 1147223) (by norm_num)
theorem B2039507 : Blo 2039435 2039507 := bstep (se 1 (by rfl) ⟨1529630, by rfl⟩ : syracuseStep 2039507 = 3059261) B3059261
theorem B4588901 : Blo 2039435 4588901 := bbase (se 4 (by rfl) ⟨430209, by rfl⟩ : syracuseStep 4588901 = 860419) (by norm_num)
theorem B3059267 : Blo 2039435 3059267 := bstep (se 1 (by rfl) ⟨2294450, by rfl⟩ : syracuseStep 3059267 = 4588901) B4588901
theorem B2039511 : Blo 2039435 2039511 := bstep (se 1 (by rfl) ⟨1529633, by rfl⟩ : syracuseStep 2039511 = 3059267) B3059267
theorem B5162525 : Blo 2039435 5162525 := bbase (se 3 (by rfl) ⟨967973, by rfl⟩ : syracuseStep 5162525 = 1935947) (by norm_num)
theorem B3441683 : Blo 2039435 3441683 := bstep (se 1 (by rfl) ⟨2581262, by rfl⟩ : syracuseStep 3441683 = 5162525) B5162525
theorem B2294455 : Blo 2039435 2294455 := bstep (se 1 (by rfl) ⟨1720841, by rfl⟩ : syracuseStep 2294455 = 3441683) B3441683
theorem B3059273 : Blo 2039435 3059273 := bstep (se 2 (by rfl) ⟨1147227, by rfl⟩ : syracuseStep 3059273 = 2294455) B2294455
theorem B2039515 : Blo 2039435 2039515 := bstep (se 1 (by rfl) ⟨1529636, by rfl⟩ : syracuseStep 2039515 = 3059273) B3059273
theorem B3871901 : Blo 2039435 3871901 := bbase (se 3 (by rfl) ⟨725981, by rfl⟩ : syracuseStep 3871901 = 1451963) (by norm_num)
theorem B10325069 : Blo 2039435 10325069 := bstep (se 3 (by rfl) ⟨1935950, by rfl⟩ : syracuseStep 10325069 = 3871901) B3871901
theorem B6883379 : Blo 2039435 6883379 := bstep (se 1 (by rfl) ⟨5162534, by rfl⟩ : syracuseStep 6883379 = 10325069) B10325069
theorem B4588919 : Blo 2039435 4588919 := bstep (se 1 (by rfl) ⟨3441689, by rfl⟩ : syracuseStep 4588919 = 6883379) B6883379
theorem B3059279 : Blo 2039435 3059279 := bstep (se 1 (by rfl) ⟨2294459, by rfl⟩ : syracuseStep 3059279 = 4588919) B4588919
theorem B2039519 : Blo 2039435 2039519 := bstep (se 1 (by rfl) ⟨1529639, by rfl⟩ : syracuseStep 2039519 = 3059279) B3059279
theorem B3059285 : Blo 2039435 3059285 := bbase (se 8 (by rfl) ⟨17925, by rfl⟩ : syracuseStep 3059285 = 35851) (by norm_num)
theorem B2039523 : Blo 2039435 2039523 := bstep (se 1 (by rfl) ⟨1529642, by rfl⟩ : syracuseStep 2039523 = 3059285) B3059285
theorem B8711813 : Blo 2039435 8711813 := bbase (se 4 (by rfl) ⟨816732, by rfl⟩ : syracuseStep 8711813 = 1633465) (by norm_num)
theorem B5807875 : Blo 2039435 5807875 := bstep (se 1 (by rfl) ⟨4355906, by rfl⟩ : syracuseStep 5807875 = 8711813) B8711813
theorem B7743833 : Blo 2039435 7743833 := bstep (se 2 (by rfl) ⟨2903937, by rfl⟩ : syracuseStep 7743833 = 5807875) B5807875
theorem B5162555 : Blo 2039435 5162555 := bstep (se 1 (by rfl) ⟨3871916, by rfl⟩ : syracuseStep 5162555 = 7743833) B7743833
theorem B3441703 : Blo 2039435 3441703 := bstep (se 1 (by rfl) ⟨2581277, by rfl⟩ : syracuseStep 3441703 = 5162555) B5162555
theorem B4588937 : Blo 2039435 4588937 := bstep (se 2 (by rfl) ⟨1720851, by rfl⟩ : syracuseStep 4588937 = 3441703) B3441703
theorem B3059291 : Blo 2039435 3059291 := bstep (se 1 (by rfl) ⟨2294468, by rfl⟩ : syracuseStep 3059291 = 4588937) B4588937
theorem B2039527 : Blo 2039435 2039527 := bstep (se 1 (by rfl) ⟨1529645, by rfl⟩ : syracuseStep 2039527 = 3059291) B3059291
theorem B2294473 : Blo 2039435 2294473 := bbase (se 2 (by rfl) ⟨860427, by rfl⟩ : syracuseStep 2294473 = 1720855) (by norm_num)
theorem B3059297 : Blo 2039435 3059297 := bstep (se 2 (by rfl) ⟨1147236, by rfl⟩ : syracuseStep 3059297 = 2294473) B2294473
theorem B2039531 : Blo 2039435 2039531 := bstep (se 1 (by rfl) ⟨1529648, by rfl⟩ : syracuseStep 2039531 = 3059297) B3059297
theorem B5233013 : Blo 2039435 5233013 := bbase (se 5 (by rfl) ⟨245297, by rfl⟩ : syracuseStep 5233013 = 490595) (by norm_num)
theorem B3488675 : Blo 2039435 3488675 := bstep (se 1 (by rfl) ⟨2616506, by rfl⟩ : syracuseStep 3488675 = 5233013) B5233013
theorem B9303133 : Blo 2039435 9303133 := bstep (se 3 (by rfl) ⟨1744337, by rfl⟩ : syracuseStep 9303133 = 3488675) B3488675
theorem B12404177 : Blo 2039435 12404177 := bstep (se 2 (by rfl) ⟨4651566, by rfl⟩ : syracuseStep 12404177 = 9303133) B9303133
theorem B8269451 : Blo 2039435 8269451 := bstep (se 1 (by rfl) ⟨6202088, by rfl⟩ : syracuseStep 8269451 = 12404177) B12404177
theorem B5512967 : Blo 2039435 5512967 := bstep (se 1 (by rfl) ⟨4134725, by rfl⟩ : syracuseStep 5512967 = 8269451) B8269451
theorem B3675311 : Blo 2039435 3675311 := bstep (se 1 (by rfl) ⟨2756483, by rfl⟩ : syracuseStep 3675311 = 5512967) B5512967
theorem B2450207 : Blo 2039435 2450207 := bstep (se 1 (by rfl) ⟨1837655, by rfl⟩ : syracuseStep 2450207 = 3675311) B3675311
theorem B6533885 : Blo 2039435 6533885 := bstep (se 3 (by rfl) ⟨1225103, by rfl⟩ : syracuseStep 6533885 = 2450207) B2450207
theorem B17423693 : Blo 2039435 17423693 := bstep (se 3 (by rfl) ⟨3266942, by rfl⟩ : syracuseStep 17423693 = 6533885) B6533885
theorem B11615795 : Blo 2039435 11615795 := bstep (se 1 (by rfl) ⟨8711846, by rfl⟩ : syracuseStep 11615795 = 17423693) B17423693
theorem B7743863 : Blo 2039435 7743863 := bstep (se 1 (by rfl) ⟨5807897, by rfl⟩ : syracuseStep 7743863 = 11615795) B11615795
theorem B5162575 : Blo 2039435 5162575 := bstep (se 1 (by rfl) ⟨3871931, by rfl⟩ : syracuseStep 5162575 = 7743863) B7743863
theorem B6883433 : Blo 2039435 6883433 := bstep (se 2 (by rfl) ⟨2581287, by rfl⟩ : syracuseStep 6883433 = 5162575) B5162575
theorem B4588955 : Blo 2039435 4588955 := bstep (se 1 (by rfl) ⟨3441716, by rfl⟩ : syracuseStep 4588955 = 6883433) B6883433
theorem B3059303 : Blo 2039435 3059303 := bstep (se 1 (by rfl) ⟨2294477, by rfl⟩ : syracuseStep 3059303 = 4588955) B4588955
theorem B2039535 : Blo 2039435 2039535 := bstep (se 1 (by rfl) ⟨1529651, by rfl⟩ : syracuseStep 2039535 = 3059303) B3059303
theorem B3059309 : Blo 2039435 3059309 := bbase (se 3 (by rfl) ⟨573620, by rfl⟩ : syracuseStep 3059309 = 1147241) (by norm_num)
theorem B2039539 : Blo 2039435 2039539 := bstep (se 1 (by rfl) ⟨1529654, by rfl⟩ : syracuseStep 2039539 = 3059309) B3059309
theorem B4588973 : Blo 2039435 4588973 := bbase (se 3 (by rfl) ⟨860432, by rfl⟩ : syracuseStep 4588973 = 1720865) (by norm_num)
theorem B3059315 : Blo 2039435 3059315 := bstep (se 1 (by rfl) ⟨2294486, by rfl⟩ : syracuseStep 3059315 = 4588973) B4588973
theorem B2039543 : Blo 2039435 2039543 := bstep (se 1 (by rfl) ⟨1529657, by rfl⟩ : syracuseStep 2039543 = 3059315) B3059315
theorem B4900445 : Blo 2039435 4900445 := bbase (se 3 (by rfl) ⟨918833, by rfl⟩ : syracuseStep 4900445 = 1837667) (by norm_num)
theorem B3266963 : Blo 2039435 3266963 := bstep (se 1 (by rfl) ⟨2450222, by rfl⟩ : syracuseStep 3266963 = 4900445) B4900445
theorem B2177975 : Blo 2039435 2177975 := bstep (se 1 (by rfl) ⟨1633481, by rfl⟩ : syracuseStep 2177975 = 3266963) B3266963
theorem B5807933 : Blo 2039435 5807933 := bstep (se 3 (by rfl) ⟨1088987, by rfl⟩ : syracuseStep 5807933 = 2177975) B2177975
theorem B3871955 : Blo 2039435 3871955 := bstep (se 1 (by rfl) ⟨2903966, by rfl⟩ : syracuseStep 3871955 = 5807933) B5807933
theorem B2581303 : Blo 2039435 2581303 := bstep (se 1 (by rfl) ⟨1935977, by rfl⟩ : syracuseStep 2581303 = 3871955) B3871955
theorem B3441737 : Blo 2039435 3441737 := bstep (se 2 (by rfl) ⟨1290651, by rfl⟩ : syracuseStep 3441737 = 2581303) B2581303
theorem B2294491 : Blo 2039435 2294491 := bstep (se 1 (by rfl) ⟨1720868, by rfl⟩ : syracuseStep 2294491 = 3441737) B3441737
theorem B3059321 : Blo 2039435 3059321 := bstep (se 2 (by rfl) ⟨1147245, by rfl⟩ : syracuseStep 3059321 = 2294491) B2294491
theorem B2039547 : Blo 2039435 2039547 := bstep (se 1 (by rfl) ⟨1529660, by rfl⟩ : syracuseStep 2039547 = 3059321) B3059321
theorem B2357533 : Blo 2039435 2357533 := bbase (se 3 (by rfl) ⟨442037, by rfl⟩ : syracuseStep 2357533 = 884075) (by norm_num)
theorem B3143377 : Blo 2039435 3143377 := bstep (se 2 (by rfl) ⟨1178766, by rfl⟩ : syracuseStep 3143377 = 2357533) B2357533
theorem B16764677 : Blo 2039435 16764677 := bstep (se 4 (by rfl) ⟨1571688, by rfl⟩ : syracuseStep 16764677 = 3143377) B3143377
theorem B11176451 : Blo 2039435 11176451 := bstep (se 1 (by rfl) ⟨8382338, by rfl⟩ : syracuseStep 11176451 = 16764677) B16764677
theorem B7450967 : Blo 2039435 7450967 := bstep (se 1 (by rfl) ⟨5588225, by rfl⟩ : syracuseStep 7450967 = 11176451) B11176451
theorem B4967311 : Blo 2039435 4967311 := bstep (se 1 (by rfl) ⟨3725483, by rfl⟩ : syracuseStep 4967311 = 7450967) B7450967
theorem B6623081 : Blo 2039435 6623081 := bstep (se 2 (by rfl) ⟨2483655, by rfl⟩ : syracuseStep 6623081 = 4967311) B4967311
theorem B4415387 : Blo 2039435 4415387 := bstep (se 1 (by rfl) ⟨3311540, by rfl⟩ : syracuseStep 4415387 = 6623081) B6623081
theorem B11774365 : Blo 2039435 11774365 := bstep (se 3 (by rfl) ⟨2207693, by rfl⟩ : syracuseStep 11774365 = 4415387) B4415387
theorem B62796613 : Blo 2039435 62796613 := bstep (se 4 (by rfl) ⟨5887182, by rfl⟩ : syracuseStep 62796613 = 11774365) B11774365
theorem B83728817 : Blo 2039435 83728817 := bstep (se 2 (by rfl) ⟨31398306, by rfl⟩ : syracuseStep 83728817 = 62796613) B62796613
theorem B55819211 : Blo 2039435 55819211 := bstep (se 1 (by rfl) ⟨41864408, by rfl⟩ : syracuseStep 55819211 = 83728817) B83728817
theorem B148851229 : Blo 2039435 148851229 := bstep (se 3 (by rfl) ⟨27909605, by rfl⟩ : syracuseStep 148851229 = 55819211) B55819211
theorem B198468305 : Blo 2039435 198468305 := bstep (se 2 (by rfl) ⟨74425614, by rfl⟩ : syracuseStep 198468305 = 148851229) B148851229
theorem B132312203 : Blo 2039435 132312203 := bstep (se 1 (by rfl) ⟨99234152, by rfl⟩ : syracuseStep 132312203 = 198468305) B198468305
theorem B88208135 : Blo 2039435 88208135 := bstep (se 1 (by rfl) ⟨66156101, by rfl⟩ : syracuseStep 88208135 = 132312203) B132312203
theorem B58805423 : Blo 2039435 58805423 := bstep (se 1 (by rfl) ⟨44104067, by rfl⟩ : syracuseStep 58805423 = 88208135) B88208135
theorem B39203615 : Blo 2039435 39203615 := bstep (se 1 (by rfl) ⟨29402711, by rfl⟩ : syracuseStep 39203615 = 58805423) B58805423
theorem B26135743 : Blo 2039435 26135743 := bstep (se 1 (by rfl) ⟨19601807, by rfl⟩ : syracuseStep 26135743 = 39203615) B39203615
theorem B34847657 : Blo 2039435 34847657 := bstep (se 2 (by rfl) ⟨13067871, by rfl⟩ : syracuseStep 34847657 = 26135743) B26135743
theorem B23231771 : Blo 2039435 23231771 := bstep (se 1 (by rfl) ⟨17423828, by rfl⟩ : syracuseStep 23231771 = 34847657) B34847657
theorem B15487847 : Blo 2039435 15487847 := bstep (se 1 (by rfl) ⟨11615885, by rfl⟩ : syracuseStep 15487847 = 23231771) B23231771
theorem B10325231 : Blo 2039435 10325231 := bstep (se 1 (by rfl) ⟨7743923, by rfl⟩ : syracuseStep 10325231 = 15487847) B15487847
theorem B6883487 : Blo 2039435 6883487 := bstep (se 1 (by rfl) ⟨5162615, by rfl⟩ : syracuseStep 6883487 = 10325231) B10325231
theorem B4588991 : Blo 2039435 4588991 := bstep (se 1 (by rfl) ⟨3441743, by rfl⟩ : syracuseStep 4588991 = 6883487) B6883487
theorem B3059327 : Blo 2039435 3059327 := bstep (se 1 (by rfl) ⟨2294495, by rfl⟩ : syracuseStep 3059327 = 4588991) B4588991
theorem B2039551 : Blo 2039435 2039551 := bstep (se 1 (by rfl) ⟨1529663, by rfl⟩ : syracuseStep 2039551 = 3059327) B3059327
theorem B3059333 : Blo 2039435 3059333 := bbase (se 4 (by rfl) ⟨286812, by rfl⟩ : syracuseStep 3059333 = 573625) (by norm_num)
theorem B2039555 : Blo 2039435 2039555 := bstep (se 1 (by rfl) ⟨1529666, by rfl⟩ : syracuseStep 2039555 = 3059333) B3059333
theorem B3441757 : Blo 2039435 3441757 := bbase (se 3 (by rfl) ⟨645329, by rfl⟩ : syracuseStep 3441757 = 1290659) (by norm_num)
theorem B4589009 : Blo 2039435 4589009 := bstep (se 2 (by rfl) ⟨1720878, by rfl⟩ : syracuseStep 4589009 = 3441757) B3441757
theorem B3059339 : Blo 2039435 3059339 := bstep (se 1 (by rfl) ⟨2294504, by rfl⟩ : syracuseStep 3059339 = 4589009) B4589009
theorem B2039559 : Blo 2039435 2039559 := bstep (se 1 (by rfl) ⟨1529669, by rfl⟩ : syracuseStep 2039559 = 3059339) B3059339
theorem B2294509 : Blo 2039435 2294509 := bbase (se 3 (by rfl) ⟨430220, by rfl⟩ : syracuseStep 2294509 = 860441) (by norm_num)
theorem B3059345 : Blo 2039435 3059345 := bstep (se 2 (by rfl) ⟨1147254, by rfl⟩ : syracuseStep 3059345 = 2294509) B2294509
theorem B2039563 : Blo 2039435 2039563 := bstep (se 1 (by rfl) ⟨1529672, by rfl⟩ : syracuseStep 2039563 = 3059345) B3059345
theorem B6883541 : Blo 2039435 6883541 := bbase (se 7 (by rfl) ⟨80666, by rfl⟩ : syracuseStep 6883541 = 161333) (by norm_num)
theorem B4589027 : Blo 2039435 4589027 := bstep (se 1 (by rfl) ⟨3441770, by rfl⟩ : syracuseStep 4589027 = 6883541) B6883541
theorem B3059351 : Blo 2039435 3059351 := bstep (se 1 (by rfl) ⟨2294513, by rfl⟩ : syracuseStep 3059351 = 4589027) B4589027
theorem B2039567 : Blo 2039435 2039567 := bstep (se 1 (by rfl) ⟨1529675, by rfl⟩ : syracuseStep 2039567 = 3059351) B3059351
theorem B3059357 : Blo 2039435 3059357 := bbase (se 3 (by rfl) ⟨573629, by rfl⟩ : syracuseStep 3059357 = 1147259) (by norm_num)
theorem B2039571 : Blo 2039435 2039571 := bstep (se 1 (by rfl) ⟨1529678, by rfl⟩ : syracuseStep 2039571 = 3059357) B3059357
theorem B4589045 : Blo 2039435 4589045 := bbase (se 5 (by rfl) ⟨215111, by rfl⟩ : syracuseStep 4589045 = 430223) (by norm_num)
theorem B3059363 : Blo 2039435 3059363 := bstep (se 1 (by rfl) ⟨2294522, by rfl⟩ : syracuseStep 3059363 = 4589045) B4589045
theorem B2039575 : Blo 2039435 2039575 := bstep (se 1 (by rfl) ⟨1529681, by rfl⟩ : syracuseStep 2039575 = 3059363) B3059363
theorem B3924845 : Blo 2039435 3924845 := bbase (se 3 (by rfl) ⟨735908, by rfl⟩ : syracuseStep 3924845 = 1471817) (by norm_num)
theorem B2616563 : Blo 2039435 2616563 := bstep (se 1 (by rfl) ⟨1962422, by rfl⟩ : syracuseStep 2616563 = 3924845) B3924845
theorem B6977501 : Blo 2039435 6977501 := bstep (se 3 (by rfl) ⟨1308281, by rfl⟩ : syracuseStep 6977501 = 2616563) B2616563
theorem B4651667 : Blo 2039435 4651667 := bstep (se 1 (by rfl) ⟨3488750, by rfl⟩ : syracuseStep 4651667 = 6977501) B6977501
theorem B3101111 : Blo 2039435 3101111 := bstep (se 1 (by rfl) ⟨2325833, by rfl⟩ : syracuseStep 3101111 = 4651667) B4651667
theorem B2067407 : Blo 2039435 2067407 := bstep (se 1 (by rfl) ⟨1550555, by rfl⟩ : syracuseStep 2067407 = 3101111) B3101111
theorem B22052341 : Blo 2039435 22052341 := bstep (se 5 (by rfl) ⟨1033703, by rfl⟩ : syracuseStep 22052341 = 2067407) B2067407
theorem B29403121 : Blo 2039435 29403121 := bstep (se 2 (by rfl) ⟨11026170, by rfl⟩ : syracuseStep 29403121 = 22052341) B22052341
theorem B39204161 : Blo 2039435 39204161 := bstep (se 2 (by rfl) ⟨14701560, by rfl⟩ : syracuseStep 39204161 = 29403121) B29403121
theorem B26136107 : Blo 2039435 26136107 := bstep (se 1 (by rfl) ⟨19602080, by rfl⟩ : syracuseStep 26136107 = 39204161) B39204161
theorem B17424071 : Blo 2039435 17424071 := bstep (se 1 (by rfl) ⟨13068053, by rfl⟩ : syracuseStep 17424071 = 26136107) B26136107
theorem B11616047 : Blo 2039435 11616047 := bstep (se 1 (by rfl) ⟨8712035, by rfl⟩ : syracuseStep 11616047 = 17424071) B17424071
theorem B7744031 : Blo 2039435 7744031 := bstep (se 1 (by rfl) ⟨5808023, by rfl⟩ : syracuseStep 7744031 = 11616047) B11616047
theorem B5162687 : Blo 2039435 5162687 := bstep (se 1 (by rfl) ⟨3872015, by rfl⟩ : syracuseStep 5162687 = 7744031) B7744031
theorem B3441791 : Blo 2039435 3441791 := bstep (se 1 (by rfl) ⟨2581343, by rfl⟩ : syracuseStep 3441791 = 5162687) B5162687
theorem B2294527 : Blo 2039435 2294527 := bstep (se 1 (by rfl) ⟨1720895, by rfl⟩ : syracuseStep 2294527 = 3441791) B3441791
theorem B3059369 : Blo 2039435 3059369 := bstep (se 2 (by rfl) ⟨1147263, by rfl⟩ : syracuseStep 3059369 = 2294527) B2294527
theorem B2039579 : Blo 2039435 2039579 := bstep (se 1 (by rfl) ⟨1529684, by rfl⟩ : syracuseStep 2039579 = 3059369) B3059369
theorem B2178013 : Blo 2039435 2178013 := bbase (se 3 (by rfl) ⟨408377, by rfl⟩ : syracuseStep 2178013 = 816755) (by norm_num)
theorem B2904017 : Blo 2039435 2904017 := bstep (se 2 (by rfl) ⟨1089006, by rfl⟩ : syracuseStep 2904017 = 2178013) B2178013
theorem B7744045 : Blo 2039435 7744045 := bstep (se 3 (by rfl) ⟨1452008, by rfl⟩ : syracuseStep 7744045 = 2904017) B2904017
theorem B10325393 : Blo 2039435 10325393 := bstep (se 2 (by rfl) ⟨3872022, by rfl⟩ : syracuseStep 10325393 = 7744045) B7744045
theorem B6883595 : Blo 2039435 6883595 := bstep (se 1 (by rfl) ⟨5162696, by rfl⟩ : syracuseStep 6883595 = 10325393) B10325393
theorem B4589063 : Blo 2039435 4589063 := bstep (se 1 (by rfl) ⟨3441797, by rfl⟩ : syracuseStep 4589063 = 6883595) B6883595
theorem B3059375 : Blo 2039435 3059375 := bstep (se 1 (by rfl) ⟨2294531, by rfl⟩ : syracuseStep 3059375 = 4589063) B4589063
theorem B2039583 : Blo 2039435 2039583 := bstep (se 1 (by rfl) ⟨1529687, by rfl⟩ : syracuseStep 2039583 = 3059375) B3059375
theorem B3059381 : Blo 2039435 3059381 := bbase (se 5 (by rfl) ⟨143408, by rfl⟩ : syracuseStep 3059381 = 286817) (by norm_num)
theorem B2039587 : Blo 2039435 2039587 := bstep (se 1 (by rfl) ⟨1529690, by rfl⟩ : syracuseStep 2039587 = 3059381) B3059381
theorem B5162717 : Blo 2039435 5162717 := bbase (se 3 (by rfl) ⟨968009, by rfl⟩ : syracuseStep 5162717 = 1936019) (by norm_num)
theorem B3441811 : Blo 2039435 3441811 := bstep (se 1 (by rfl) ⟨2581358, by rfl⟩ : syracuseStep 3441811 = 5162717) B5162717
theorem B4589081 : Blo 2039435 4589081 := bstep (se 2 (by rfl) ⟨1720905, by rfl⟩ : syracuseStep 4589081 = 3441811) B3441811
theorem B3059387 : Blo 2039435 3059387 := bstep (se 1 (by rfl) ⟨2294540, by rfl⟩ : syracuseStep 3059387 = 4589081) B4589081
theorem B2039591 : Blo 2039435 2039591 := bstep (se 1 (by rfl) ⟨1529693, by rfl⟩ : syracuseStep 2039591 = 3059387) B3059387
theorem B2294545 : Blo 2039435 2294545 := bbase (se 2 (by rfl) ⟨860454, by rfl⟩ : syracuseStep 2294545 = 1720909) (by norm_num)
theorem B3059393 : Blo 2039435 3059393 := bstep (se 2 (by rfl) ⟨1147272, by rfl⟩ : syracuseStep 3059393 = 2294545) B2294545
theorem B2039595 : Blo 2039435 2039595 := bstep (se 1 (by rfl) ⟨1529696, by rfl⟩ : syracuseStep 2039595 = 3059393) B3059393
theorem B3872053 : Blo 2039435 3872053 := bbase (se 5 (by rfl) ⟨181502, by rfl⟩ : syracuseStep 3872053 = 363005) (by norm_num)
theorem B5162737 : Blo 2039435 5162737 := bstep (se 2 (by rfl) ⟨1936026, by rfl⟩ : syracuseStep 5162737 = 3872053) B3872053
theorem B6883649 : Blo 2039435 6883649 := bstep (se 2 (by rfl) ⟨2581368, by rfl⟩ : syracuseStep 6883649 = 5162737) B5162737
theorem B4589099 : Blo 2039435 4589099 := bstep (se 1 (by rfl) ⟨3441824, by rfl⟩ : syracuseStep 4589099 = 6883649) B6883649
theorem B3059399 : Blo 2039435 3059399 := bstep (se 1 (by rfl) ⟨2294549, by rfl⟩ : syracuseStep 3059399 = 4589099) B4589099
theorem B2039599 : Blo 2039435 2039599 := bstep (se 1 (by rfl) ⟨1529699, by rfl⟩ : syracuseStep 2039599 = 3059399) B3059399
theorem B3059405 : Blo 2039435 3059405 := bbase (se 3 (by rfl) ⟨573638, by rfl⟩ : syracuseStep 3059405 = 1147277) (by norm_num)
theorem B2039603 : Blo 2039435 2039603 := bstep (se 1 (by rfl) ⟨1529702, by rfl⟩ : syracuseStep 2039603 = 3059405) B3059405
theorem B4589117 : Blo 2039435 4589117 := bbase (se 3 (by rfl) ⟨860459, by rfl⟩ : syracuseStep 4589117 = 1720919) (by norm_num)
theorem B3059411 : Blo 2039435 3059411 := bstep (se 1 (by rfl) ⟨2294558, by rfl⟩ : syracuseStep 3059411 = 4589117) B4589117
theorem B2039607 : Blo 2039435 2039607 := bstep (se 1 (by rfl) ⟨1529705, by rfl⟩ : syracuseStep 2039607 = 3059411) B3059411
theorem B3441845 : Blo 2039435 3441845 := bbase (se 5 (by rfl) ⟨161336, by rfl⟩ : syracuseStep 3441845 = 322673) (by norm_num)
theorem B2294563 : Blo 2039435 2294563 := bstep (se 1 (by rfl) ⟨1720922, by rfl⟩ : syracuseStep 2294563 = 3441845) B3441845
theorem B3059417 : Blo 2039435 3059417 := bstep (se 2 (by rfl) ⟨1147281, by rfl⟩ : syracuseStep 3059417 = 2294563) B2294563
theorem B2039611 : Blo 2039435 2039611 := bstep (se 1 (by rfl) ⟨1529708, by rfl⟩ : syracuseStep 2039611 = 3059417) B3059417
theorem B3143477 : Blo 2039435 3143477 := bbase (se 5 (by rfl) ⟨147350, by rfl⟩ : syracuseStep 3143477 = 294701) (by norm_num)
theorem B2095651 : Blo 2039435 2095651 := bstep (se 1 (by rfl) ⟨1571738, by rfl⟩ : syracuseStep 2095651 = 3143477) B3143477
theorem B2794201 : Blo 2039435 2794201 := bstep (se 2 (by rfl) ⟨1047825, by rfl⟩ : syracuseStep 2794201 = 2095651) B2095651
theorem B59609621 : Blo 2039435 59609621 := bstep (se 6 (by rfl) ⟨1397100, by rfl⟩ : syracuseStep 59609621 = 2794201) B2794201
theorem B39739747 : Blo 2039435 39739747 := bstep (se 1 (by rfl) ⟨29804810, by rfl⟩ : syracuseStep 39739747 = 59609621) B59609621
theorem B52986329 : Blo 2039435 52986329 := bstep (se 2 (by rfl) ⟨19869873, by rfl⟩ : syracuseStep 52986329 = 39739747) B39739747
theorem B35324219 : Blo 2039435 35324219 := bstep (se 1 (by rfl) ⟨26493164, by rfl⟩ : syracuseStep 35324219 = 52986329) B52986329
theorem B94197917 : Blo 2039435 94197917 := bstep (se 3 (by rfl) ⟨17662109, by rfl⟩ : syracuseStep 94197917 = 35324219) B35324219
theorem B62798611 : Blo 2039435 62798611 := bstep (se 1 (by rfl) ⟨47098958, by rfl⟩ : syracuseStep 62798611 = 94197917) B94197917
theorem B83731481 : Blo 2039435 83731481 := bstep (se 2 (by rfl) ⟨31399305, by rfl⟩ : syracuseStep 83731481 = 62798611) B62798611
theorem B55820987 : Blo 2039435 55820987 := bstep (se 1 (by rfl) ⟨41865740, by rfl⟩ : syracuseStep 55820987 = 83731481) B83731481
theorem B37213991 : Blo 2039435 37213991 := bstep (se 1 (by rfl) ⟨27910493, by rfl⟩ : syracuseStep 37213991 = 55820987) B55820987
theorem B24809327 : Blo 2039435 24809327 := bstep (se 1 (by rfl) ⟨18606995, by rfl⟩ : syracuseStep 24809327 = 37213991) B37213991
theorem B16539551 : Blo 2039435 16539551 := bstep (se 1 (by rfl) ⟨12404663, by rfl⟩ : syracuseStep 16539551 = 24809327) B24809327
theorem B11026367 : Blo 2039435 11026367 := bstep (se 1 (by rfl) ⟨8269775, by rfl⟩ : syracuseStep 11026367 = 16539551) B16539551
theorem B7350911 : Blo 2039435 7350911 := bstep (se 1 (by rfl) ⟨5513183, by rfl⟩ : syracuseStep 7350911 = 11026367) B11026367
theorem B4900607 : Blo 2039435 4900607 := bstep (se 1 (by rfl) ⟨3675455, by rfl⟩ : syracuseStep 4900607 = 7350911) B7350911
theorem B3267071 : Blo 2039435 3267071 := bstep (se 1 (by rfl) ⟨2450303, by rfl⟩ : syracuseStep 3267071 = 4900607) B4900607
theorem B2178047 : Blo 2039435 2178047 := bstep (se 1 (by rfl) ⟨1633535, by rfl⟩ : syracuseStep 2178047 = 3267071) B3267071
theorem B5808125 : Blo 2039435 5808125 := bstep (se 3 (by rfl) ⟨1089023, by rfl⟩ : syracuseStep 5808125 = 2178047) B2178047
theorem B15488333 : Blo 2039435 15488333 := bstep (se 3 (by rfl) ⟨2904062, by rfl⟩ : syracuseStep 15488333 = 5808125) B5808125
theorem B10325555 : Blo 2039435 10325555 := bstep (se 1 (by rfl) ⟨7744166, by rfl⟩ : syracuseStep 10325555 = 15488333) B15488333
theorem B6883703 : Blo 2039435 6883703 := bstep (se 1 (by rfl) ⟨5162777, by rfl⟩ : syracuseStep 6883703 = 10325555) B10325555
theorem B4589135 : Blo 2039435 4589135 := bstep (se 1 (by rfl) ⟨3441851, by rfl⟩ : syracuseStep 4589135 = 6883703) B6883703
theorem B3059423 : Blo 2039435 3059423 := bstep (se 1 (by rfl) ⟨2294567, by rfl⟩ : syracuseStep 3059423 = 4589135) B4589135
theorem B2039615 : Blo 2039435 2039615 := bstep (se 1 (by rfl) ⟨1529711, by rfl⟩ : syracuseStep 2039615 = 3059423) B3059423
theorem B3059429 : Blo 2039435 3059429 := bbase (se 4 (by rfl) ⟨286821, by rfl⟩ : syracuseStep 3059429 = 573643) (by norm_num)
theorem B2039619 : Blo 2039435 2039619 := bstep (se 1 (by rfl) ⟨1529714, by rfl⟩ : syracuseStep 2039619 = 3059429) B3059429
theorem B5808149 : Blo 2039435 5808149 := bbase (se 6 (by rfl) ⟨136128, by rfl⟩ : syracuseStep 5808149 = 272257) (by norm_num)
theorem B3872099 : Blo 2039435 3872099 := bstep (se 1 (by rfl) ⟨2904074, by rfl⟩ : syracuseStep 3872099 = 5808149) B5808149
theorem B2581399 : Blo 2039435 2581399 := bstep (se 1 (by rfl) ⟨1936049, by rfl⟩ : syracuseStep 2581399 = 3872099) B3872099
theorem B3441865 : Blo 2039435 3441865 := bstep (se 2 (by rfl) ⟨1290699, by rfl⟩ : syracuseStep 3441865 = 2581399) B2581399
theorem B4589153 : Blo 2039435 4589153 := bstep (se 2 (by rfl) ⟨1720932, by rfl⟩ : syracuseStep 4589153 = 3441865) B3441865
theorem B3059435 : Blo 2039435 3059435 := bstep (se 1 (by rfl) ⟨2294576, by rfl⟩ : syracuseStep 3059435 = 4589153) B4589153
theorem B2039623 : Blo 2039435 2039623 := bstep (se 1 (by rfl) ⟨1529717, by rfl⟩ : syracuseStep 2039623 = 3059435) B3059435
theorem B2294581 : Blo 2039435 2294581 := bbase (se 5 (by rfl) ⟨107558, by rfl⟩ : syracuseStep 2294581 = 215117) (by norm_num)
theorem B3059441 : Blo 2039435 3059441 := bstep (se 2 (by rfl) ⟨1147290, by rfl⟩ : syracuseStep 3059441 = 2294581) B2294581
theorem B2039627 : Blo 2039435 2039627 := bstep (se 1 (by rfl) ⟨1529720, by rfl⟩ : syracuseStep 2039627 = 3059441) B3059441
theorem B2581409 : Blo 2039435 2581409 := bbase (se 2 (by rfl) ⟨968028, by rfl⟩ : syracuseStep 2581409 = 1936057) (by norm_num)
theorem B6883757 : Blo 2039435 6883757 := bstep (se 3 (by rfl) ⟨1290704, by rfl⟩ : syracuseStep 6883757 = 2581409) B2581409
theorem B4589171 : Blo 2039435 4589171 := bstep (se 1 (by rfl) ⟨3441878, by rfl⟩ : syracuseStep 4589171 = 6883757) B6883757
theorem B3059447 : Blo 2039435 3059447 := bstep (se 1 (by rfl) ⟨2294585, by rfl⟩ : syracuseStep 3059447 = 4589171) B4589171
theorem B2039631 : Blo 2039435 2039631 := bstep (se 1 (by rfl) ⟨1529723, by rfl⟩ : syracuseStep 2039631 = 3059447) B3059447
theorem B3059453 : Blo 2039435 3059453 := bbase (se 3 (by rfl) ⟨573647, by rfl⟩ : syracuseStep 3059453 = 1147295) (by norm_num)
theorem B2039635 : Blo 2039435 2039635 := bstep (se 1 (by rfl) ⟨1529726, by rfl⟩ : syracuseStep 2039635 = 3059453) B3059453
theorem B4589189 : Blo 2039435 4589189 := bbase (se 4 (by rfl) ⟨430236, by rfl⟩ : syracuseStep 4589189 = 860473) (by norm_num)
theorem B3059459 : Blo 2039435 3059459 := bstep (se 1 (by rfl) ⟨2294594, by rfl⟩ : syracuseStep 3059459 = 4589189) B4589189
theorem B2039639 : Blo 2039435 2039639 := bstep (se 1 (by rfl) ⟨1529729, by rfl⟩ : syracuseStep 2039639 = 3059459) B3059459
theorem B7351013 : Blo 2039435 7351013 := bbase (se 4 (by rfl) ⟨689157, by rfl⟩ : syracuseStep 7351013 = 1378315) (by norm_num)
theorem B4900675 : Blo 2039435 4900675 := bstep (se 1 (by rfl) ⟨3675506, by rfl⟩ : syracuseStep 4900675 = 7351013) B7351013
theorem B6534233 : Blo 2039435 6534233 := bstep (se 2 (by rfl) ⟨2450337, by rfl⟩ : syracuseStep 6534233 = 4900675) B4900675
theorem B4356155 : Blo 2039435 4356155 := bstep (se 1 (by rfl) ⟨3267116, by rfl⟩ : syracuseStep 4356155 = 6534233) B6534233
theorem B2904103 : Blo 2039435 2904103 := bstep (se 1 (by rfl) ⟨2178077, by rfl⟩ : syracuseStep 2904103 = 4356155) B4356155
theorem B3872137 : Blo 2039435 3872137 := bstep (se 2 (by rfl) ⟨1452051, by rfl⟩ : syracuseStep 3872137 = 2904103) B2904103
theorem B5162849 : Blo 2039435 5162849 := bstep (se 2 (by rfl) ⟨1936068, by rfl⟩ : syracuseStep 5162849 = 3872137) B3872137
theorem B3441899 : Blo 2039435 3441899 := bstep (se 1 (by rfl) ⟨2581424, by rfl⟩ : syracuseStep 3441899 = 5162849) B5162849
theorem B2294599 : Blo 2039435 2294599 := bstep (se 1 (by rfl) ⟨1720949, by rfl⟩ : syracuseStep 2294599 = 3441899) B3441899
theorem B3059465 : Blo 2039435 3059465 := bstep (se 2 (by rfl) ⟨1147299, by rfl⟩ : syracuseStep 3059465 = 2294599) B2294599
theorem B2039643 : Blo 2039435 2039643 := bstep (se 1 (by rfl) ⟨1529732, by rfl⟩ : syracuseStep 2039643 = 3059465) B3059465
theorem B10325717 : Blo 2039435 10325717 := bbase (se 7 (by rfl) ⟨121004, by rfl⟩ : syracuseStep 10325717 = 242009) (by norm_num)
theorem B6883811 : Blo 2039435 6883811 := bstep (se 1 (by rfl) ⟨5162858, by rfl⟩ : syracuseStep 6883811 = 10325717) B10325717
theorem B4589207 : Blo 2039435 4589207 := bstep (se 1 (by rfl) ⟨3441905, by rfl⟩ : syracuseStep 4589207 = 6883811) B6883811
theorem B3059471 : Blo 2039435 3059471 := bstep (se 1 (by rfl) ⟨2294603, by rfl⟩ : syracuseStep 3059471 = 4589207) B4589207
theorem B2039647 : Blo 2039435 2039647 := bstep (se 1 (by rfl) ⟨1529735, by rfl⟩ : syracuseStep 2039647 = 3059471) B3059471
theorem B3059477 : Blo 2039435 3059477 := bbase (se 6 (by rfl) ⟨71706, by rfl⟩ : syracuseStep 3059477 = 143413) (by norm_num)
theorem B2039651 : Blo 2039435 2039651 := bstep (se 1 (by rfl) ⟨1529738, by rfl⟩ : syracuseStep 2039651 = 3059477) B3059477
theorem B2357653 : Blo 2039435 2357653 := bbase (se 6 (by rfl) ⟨55257, by rfl⟩ : syracuseStep 2357653 = 110515) (by norm_num)
theorem B3143537 : Blo 2039435 3143537 := bstep (se 2 (by rfl) ⟨1178826, by rfl⟩ : syracuseStep 3143537 = 2357653) B2357653
theorem B134124245 : Blo 2039435 134124245 := bstep (se 7 (by rfl) ⟨1571768, by rfl⟩ : syracuseStep 134124245 = 3143537) B3143537
theorem B89416163 : Blo 2039435 89416163 := bstep (se 1 (by rfl) ⟨67062122, by rfl⟩ : syracuseStep 89416163 = 134124245) B134124245
theorem B59610775 : Blo 2039435 59610775 := bstep (se 1 (by rfl) ⟨44708081, by rfl⟩ : syracuseStep 59610775 = 89416163) B89416163
theorem B79481033 : Blo 2039435 79481033 := bstep (se 2 (by rfl) ⟨29805387, by rfl⟩ : syracuseStep 79481033 = 59610775) B59610775
theorem B52987355 : Blo 2039435 52987355 := bstep (se 1 (by rfl) ⟨39740516, by rfl⟩ : syracuseStep 52987355 = 79481033) B79481033
theorem B35324903 : Blo 2039435 35324903 := bstep (se 1 (by rfl) ⟨26493677, by rfl⟩ : syracuseStep 35324903 = 52987355) B52987355
theorem B23549935 : Blo 2039435 23549935 := bstep (se 1 (by rfl) ⟨17662451, by rfl⟩ : syracuseStep 23549935 = 35324903) B35324903
theorem B31399913 : Blo 2039435 31399913 := bstep (se 2 (by rfl) ⟨11774967, by rfl⟩ : syracuseStep 31399913 = 23549935) B23549935
theorem B83733101 : Blo 2039435 83733101 := bstep (se 3 (by rfl) ⟨15699956, by rfl⟩ : syracuseStep 83733101 = 31399913) B31399913
theorem B55822067 : Blo 2039435 55822067 := bstep (se 1 (by rfl) ⟨41866550, by rfl⟩ : syracuseStep 55822067 = 83733101) B83733101
theorem B37214711 : Blo 2039435 37214711 := bstep (se 1 (by rfl) ⟨27911033, by rfl⟩ : syracuseStep 37214711 = 55822067) B55822067
theorem B24809807 : Blo 2039435 24809807 := bstep (se 1 (by rfl) ⟨18607355, by rfl⟩ : syracuseStep 24809807 = 37214711) B37214711
theorem B16539871 : Blo 2039435 16539871 := bstep (se 1 (by rfl) ⟨12404903, by rfl⟩ : syracuseStep 16539871 = 24809807) B24809807
theorem B22053161 : Blo 2039435 22053161 := bstep (se 2 (by rfl) ⟨8269935, by rfl⟩ : syracuseStep 22053161 = 16539871) B16539871
theorem B58808429 : Blo 2039435 58808429 := bstep (se 3 (by rfl) ⟨11026580, by rfl⟩ : syracuseStep 58808429 = 22053161) B22053161
theorem B39205619 : Blo 2039435 39205619 := bstep (se 1 (by rfl) ⟨29404214, by rfl⟩ : syracuseStep 39205619 = 58808429) B58808429
theorem B26137079 : Blo 2039435 26137079 := bstep (se 1 (by rfl) ⟨19602809, by rfl⟩ : syracuseStep 26137079 = 39205619) B39205619
theorem B17424719 : Blo 2039435 17424719 := bstep (se 1 (by rfl) ⟨13068539, by rfl⟩ : syracuseStep 17424719 = 26137079) B26137079
theorem B11616479 : Blo 2039435 11616479 := bstep (se 1 (by rfl) ⟨8712359, by rfl⟩ : syracuseStep 11616479 = 17424719) B17424719
theorem B7744319 : Blo 2039435 7744319 := bstep (se 1 (by rfl) ⟨5808239, by rfl⟩ : syracuseStep 7744319 = 11616479) B11616479
theorem B5162879 : Blo 2039435 5162879 := bstep (se 1 (by rfl) ⟨3872159, by rfl⟩ : syracuseStep 5162879 = 7744319) B7744319
theorem B3441919 : Blo 2039435 3441919 := bstep (se 1 (by rfl) ⟨2581439, by rfl⟩ : syracuseStep 3441919 = 5162879) B5162879
theorem B4589225 : Blo 2039435 4589225 := bstep (se 2 (by rfl) ⟨1720959, by rfl⟩ : syracuseStep 4589225 = 3441919) B3441919
theorem B3059483 : Blo 2039435 3059483 := bstep (se 1 (by rfl) ⟨2294612, by rfl⟩ : syracuseStep 3059483 = 4589225) B4589225
theorem B2039655 : Blo 2039435 2039655 := bstep (se 1 (by rfl) ⟨1529741, by rfl⟩ : syracuseStep 2039655 = 3059483) B3059483
theorem B2294617 : Blo 2039435 2294617 := bbase (se 2 (by rfl) ⟨860481, by rfl⟩ : syracuseStep 2294617 = 1720963) (by norm_num)
theorem B3059489 : Blo 2039435 3059489 := bstep (se 2 (by rfl) ⟨1147308, by rfl⟩ : syracuseStep 3059489 = 2294617) B2294617
theorem B2039659 : Blo 2039435 2039659 := bstep (se 1 (by rfl) ⟨1529744, by rfl⟩ : syracuseStep 2039659 = 3059489) B3059489
theorem B4356197 : Blo 2039435 4356197 := bbase (se 4 (by rfl) ⟨408393, by rfl⟩ : syracuseStep 4356197 = 816787) (by norm_num)
theorem B2904131 : Blo 2039435 2904131 := bstep (se 1 (by rfl) ⟨2178098, by rfl⟩ : syracuseStep 2904131 = 4356197) B4356197
theorem B7744349 : Blo 2039435 7744349 := bstep (se 3 (by rfl) ⟨1452065, by rfl⟩ : syracuseStep 7744349 = 2904131) B2904131
theorem B5162899 : Blo 2039435 5162899 := bstep (se 1 (by rfl) ⟨3872174, by rfl⟩ : syracuseStep 5162899 = 7744349) B7744349
theorem B6883865 : Blo 2039435 6883865 := bstep (se 2 (by rfl) ⟨2581449, by rfl⟩ : syracuseStep 6883865 = 5162899) B5162899
theorem B4589243 : Blo 2039435 4589243 := bstep (se 1 (by rfl) ⟨3441932, by rfl⟩ : syracuseStep 4589243 = 6883865) B6883865
theorem B3059495 : Blo 2039435 3059495 := bstep (se 1 (by rfl) ⟨2294621, by rfl⟩ : syracuseStep 3059495 = 4589243) B4589243
theorem B2039663 : Blo 2039435 2039663 := bstep (se 1 (by rfl) ⟨1529747, by rfl⟩ : syracuseStep 2039663 = 3059495) B3059495
theorem B3059501 : Blo 2039435 3059501 := bbase (se 3 (by rfl) ⟨573656, by rfl⟩ : syracuseStep 3059501 = 1147313) (by norm_num)
theorem B2039667 : Blo 2039435 2039667 := bstep (se 1 (by rfl) ⟨1529750, by rfl⟩ : syracuseStep 2039667 = 3059501) B3059501
theorem B4589261 : Blo 2039435 4589261 := bbase (se 3 (by rfl) ⟨860486, by rfl⟩ : syracuseStep 4589261 = 1720973) (by norm_num)
theorem B3059507 : Blo 2039435 3059507 := bstep (se 1 (by rfl) ⟨2294630, by rfl⟩ : syracuseStep 3059507 = 4589261) B4589261
theorem B2039671 : Blo 2039435 2039671 := bstep (se 1 (by rfl) ⟨1529753, by rfl⟩ : syracuseStep 2039671 = 3059507) B3059507
theorem B2581465 : Blo 2039435 2581465 := bbase (se 2 (by rfl) ⟨968049, by rfl⟩ : syracuseStep 2581465 = 1936099) (by norm_num)
theorem B3441953 : Blo 2039435 3441953 := bstep (se 2 (by rfl) ⟨1290732, by rfl⟩ : syracuseStep 3441953 = 2581465) B2581465
theorem B2294635 : Blo 2039435 2294635 := bstep (se 1 (by rfl) ⟨1720976, by rfl⟩ : syracuseStep 2294635 = 3441953) B3441953
theorem B3059513 : Blo 2039435 3059513 := bstep (se 2 (by rfl) ⟨1147317, by rfl⟩ : syracuseStep 3059513 = 2294635) B2294635
theorem B2039675 : Blo 2039435 2039675 := bstep (se 1 (by rfl) ⟨1529756, by rfl⟩ : syracuseStep 2039675 = 3059513) B3059513
theorem B3267173 : Blo 2039435 3267173 := bbase (se 4 (by rfl) ⟨306297, by rfl⟩ : syracuseStep 3267173 = 612595) (by norm_num)
theorem B8712461 : Blo 2039435 8712461 := bstep (se 3 (by rfl) ⟨1633586, by rfl⟩ : syracuseStep 8712461 = 3267173) B3267173
theorem B23233229 : Blo 2039435 23233229 := bstep (se 3 (by rfl) ⟨4356230, by rfl⟩ : syracuseStep 23233229 = 8712461) B8712461
theorem B15488819 : Blo 2039435 15488819 := bstep (se 1 (by rfl) ⟨11616614, by rfl⟩ : syracuseStep 15488819 = 23233229) B23233229
theorem B10325879 : Blo 2039435 10325879 := bstep (se 1 (by rfl) ⟨7744409, by rfl⟩ : syracuseStep 10325879 = 15488819) B15488819
theorem B6883919 : Blo 2039435 6883919 := bstep (se 1 (by rfl) ⟨5162939, by rfl⟩ : syracuseStep 6883919 = 10325879) B10325879
theorem B4589279 : Blo 2039435 4589279 := bstep (se 1 (by rfl) ⟨3441959, by rfl⟩ : syracuseStep 4589279 = 6883919) B6883919
theorem B3059519 : Blo 2039435 3059519 := bstep (se 1 (by rfl) ⟨2294639, by rfl⟩ : syracuseStep 3059519 = 4589279) B4589279
theorem B2039679 : Blo 2039435 2039679 := bstep (se 1 (by rfl) ⟨1529759, by rfl⟩ : syracuseStep 2039679 = 3059519) B3059519
theorem B3059525 : Blo 2039435 3059525 := bbase (se 4 (by rfl) ⟨286830, by rfl⟩ : syracuseStep 3059525 = 573661) (by norm_num)
theorem B2039683 : Blo 2039435 2039683 := bstep (se 1 (by rfl) ⟨1529762, by rfl⟩ : syracuseStep 2039683 = 3059525) B3059525
theorem B3441973 : Blo 2039435 3441973 := bbase (se 5 (by rfl) ⟨161342, by rfl⟩ : syracuseStep 3441973 = 322685) (by norm_num)
theorem B4589297 : Blo 2039435 4589297 := bstep (se 2 (by rfl) ⟨1720986, by rfl⟩ : syracuseStep 4589297 = 3441973) B3441973
theorem B3059531 : Blo 2039435 3059531 := bstep (se 1 (by rfl) ⟨2294648, by rfl⟩ : syracuseStep 3059531 = 4589297) B4589297
theorem B2039687 : Blo 2039435 2039687 := bstep (se 1 (by rfl) ⟨1529765, by rfl⟩ : syracuseStep 2039687 = 3059531) B3059531
theorem B2294653 : Blo 2039435 2294653 := bbase (se 3 (by rfl) ⟨430247, by rfl⟩ : syracuseStep 2294653 = 860495) (by norm_num)
theorem B3059537 : Blo 2039435 3059537 := bstep (se 2 (by rfl) ⟨1147326, by rfl⟩ : syracuseStep 3059537 = 2294653) B2294653
theorem B2039691 : Blo 2039435 2039691 := bstep (se 1 (by rfl) ⟨1529768, by rfl⟩ : syracuseStep 2039691 = 3059537) B3059537
theorem B6883973 : Blo 2039435 6883973 := bbase (se 4 (by rfl) ⟨645372, by rfl⟩ : syracuseStep 6883973 = 1290745) (by norm_num)
theorem B4589315 : Blo 2039435 4589315 := bstep (se 1 (by rfl) ⟨3441986, by rfl⟩ : syracuseStep 4589315 = 6883973) B6883973
theorem B3059543 : Blo 2039435 3059543 := bstep (se 1 (by rfl) ⟨2294657, by rfl⟩ : syracuseStep 3059543 = 4589315) B4589315
theorem B2039695 : Blo 2039435 2039695 := bstep (se 1 (by rfl) ⟨1529771, by rfl⟩ : syracuseStep 2039695 = 3059543) B3059543
theorem B3059549 : Blo 2039435 3059549 := bbase (se 3 (by rfl) ⟨573665, by rfl⟩ : syracuseStep 3059549 = 1147331) (by norm_num)
theorem B2039699 : Blo 2039435 2039699 := bstep (se 1 (by rfl) ⟨1529774, by rfl⟩ : syracuseStep 2039699 = 3059549) B3059549
theorem B4589333 : Blo 2039435 4589333 := bbase (se 6 (by rfl) ⟨107562, by rfl⟩ : syracuseStep 4589333 = 215125) (by norm_num)
theorem B3059555 : Blo 2039435 3059555 := bstep (se 1 (by rfl) ⟨2294666, by rfl⟩ : syracuseStep 3059555 = 4589333) B4589333
theorem B2039703 : Blo 2039435 2039703 := bstep (se 1 (by rfl) ⟨1529777, by rfl⟩ : syracuseStep 2039703 = 3059555) B3059555
theorem B7744517 : Blo 2039435 7744517 := bbase (se 4 (by rfl) ⟨726048, by rfl⟩ : syracuseStep 7744517 = 1452097) (by norm_num)
theorem B5163011 : Blo 2039435 5163011 := bstep (se 1 (by rfl) ⟨3872258, by rfl⟩ : syracuseStep 5163011 = 7744517) B7744517
theorem B3442007 : Blo 2039435 3442007 := bstep (se 1 (by rfl) ⟨2581505, by rfl⟩ : syracuseStep 3442007 = 5163011) B5163011
theorem B2294671 : Blo 2039435 2294671 := bstep (se 1 (by rfl) ⟨1721003, by rfl⟩ : syracuseStep 2294671 = 3442007) B3442007
theorem B3059561 : Blo 2039435 3059561 := bstep (se 2 (by rfl) ⟨1147335, by rfl⟩ : syracuseStep 3059561 = 2294671) B2294671
theorem B2039707 : Blo 2039435 2039707 := bstep (se 1 (by rfl) ⟨1529780, by rfl⟩ : syracuseStep 2039707 = 3059561) B3059561
theorem B4900837 : Blo 2039435 4900837 := bbase (se 4 (by rfl) ⟨459453, by rfl⟩ : syracuseStep 4900837 = 918907) (by norm_num)
theorem B6534449 : Blo 2039435 6534449 := bstep (se 2 (by rfl) ⟨2450418, by rfl⟩ : syracuseStep 6534449 = 4900837) B4900837
theorem B4356299 : Blo 2039435 4356299 := bstep (se 1 (by rfl) ⟨3267224, by rfl⟩ : syracuseStep 4356299 = 6534449) B6534449
theorem B11616797 : Blo 2039435 11616797 := bstep (se 3 (by rfl) ⟨2178149, by rfl⟩ : syracuseStep 11616797 = 4356299) B4356299
theorem B7744531 : Blo 2039435 7744531 := bstep (se 1 (by rfl) ⟨5808398, by rfl⟩ : syracuseStep 7744531 = 11616797) B11616797
theorem B10326041 : Blo 2039435 10326041 := bstep (se 2 (by rfl) ⟨3872265, by rfl⟩ : syracuseStep 10326041 = 7744531) B7744531
theorem B6884027 : Blo 2039435 6884027 := bstep (se 1 (by rfl) ⟨5163020, by rfl⟩ : syracuseStep 6884027 = 10326041) B10326041
theorem B4589351 : Blo 2039435 4589351 := bstep (se 1 (by rfl) ⟨3442013, by rfl⟩ : syracuseStep 4589351 = 6884027) B6884027
theorem B3059567 : Blo 2039435 3059567 := bstep (se 1 (by rfl) ⟨2294675, by rfl⟩ : syracuseStep 3059567 = 4589351) B4589351
theorem B2039711 : Blo 2039435 2039711 := bstep (se 1 (by rfl) ⟨1529783, by rfl⟩ : syracuseStep 2039711 = 3059567) B3059567
theorem B3059573 : Blo 2039435 3059573 := bbase (se 5 (by rfl) ⟨143417, by rfl⟩ : syracuseStep 3059573 = 286835) (by norm_num)
theorem B2039715 : Blo 2039435 2039715 := bstep (se 1 (by rfl) ⟨1529786, by rfl⟩ : syracuseStep 2039715 = 3059573) B3059573
theorem B4356317 : Blo 2039435 4356317 := bbase (se 3 (by rfl) ⟨816809, by rfl⟩ : syracuseStep 4356317 = 1633619) (by norm_num)
theorem B2904211 : Blo 2039435 2904211 := bstep (se 1 (by rfl) ⟨2178158, by rfl⟩ : syracuseStep 2904211 = 4356317) B4356317
theorem B3872281 : Blo 2039435 3872281 := bstep (se 2 (by rfl) ⟨1452105, by rfl⟩ : syracuseStep 3872281 = 2904211) B2904211
theorem B5163041 : Blo 2039435 5163041 := bstep (se 2 (by rfl) ⟨1936140, by rfl⟩ : syracuseStep 5163041 = 3872281) B3872281
theorem B3442027 : Blo 2039435 3442027 := bstep (se 1 (by rfl) ⟨2581520, by rfl⟩ : syracuseStep 3442027 = 5163041) B5163041
theorem B4589369 : Blo 2039435 4589369 := bstep (se 2 (by rfl) ⟨1721013, by rfl⟩ : syracuseStep 4589369 = 3442027) B3442027
theorem B3059579 : Blo 2039435 3059579 := bstep (se 1 (by rfl) ⟨2294684, by rfl⟩ : syracuseStep 3059579 = 4589369) B4589369
theorem B2039719 : Blo 2039435 2039719 := bstep (se 1 (by rfl) ⟨1529789, by rfl⟩ : syracuseStep 2039719 = 3059579) B3059579
theorem B2294689 : Blo 2039435 2294689 := bbase (se 2 (by rfl) ⟨860508, by rfl⟩ : syracuseStep 2294689 = 1721017) (by norm_num)
theorem B3059585 : Blo 2039435 3059585 := bstep (se 2 (by rfl) ⟨1147344, by rfl⟩ : syracuseStep 3059585 = 2294689) B2294689
theorem B2039723 : Blo 2039435 2039723 := bstep (se 1 (by rfl) ⟨1529792, by rfl⟩ : syracuseStep 2039723 = 3059585) B3059585
theorem B5163061 : Blo 2039435 5163061 := bbase (se 5 (by rfl) ⟨242018, by rfl⟩ : syracuseStep 5163061 = 484037) (by norm_num)
theorem B6884081 : Blo 2039435 6884081 := bstep (se 2 (by rfl) ⟨2581530, by rfl⟩ : syracuseStep 6884081 = 5163061) B5163061
theorem B4589387 : Blo 2039435 4589387 := bstep (se 1 (by rfl) ⟨3442040, by rfl⟩ : syracuseStep 4589387 = 6884081) B6884081
theorem B3059591 : Blo 2039435 3059591 := bstep (se 1 (by rfl) ⟨2294693, by rfl⟩ : syracuseStep 3059591 = 4589387) B4589387
theorem B2039727 : Blo 2039435 2039727 := bstep (se 1 (by rfl) ⟨1529795, by rfl⟩ : syracuseStep 2039727 = 3059591) B3059591
theorem B3059597 : Blo 2039435 3059597 := bbase (se 3 (by rfl) ⟨573674, by rfl⟩ : syracuseStep 3059597 = 1147349) (by norm_num)
theorem B2039731 : Blo 2039435 2039731 := bstep (se 1 (by rfl) ⟨1529798, by rfl⟩ : syracuseStep 2039731 = 3059597) B3059597
theorem B4589405 : Blo 2039435 4589405 := bbase (se 3 (by rfl) ⟨860513, by rfl⟩ : syracuseStep 4589405 = 1721027) (by norm_num)
theorem B3059603 : Blo 2039435 3059603 := bstep (se 1 (by rfl) ⟨2294702, by rfl⟩ : syracuseStep 3059603 = 4589405) B4589405
theorem B2039735 : Blo 2039435 2039735 := bstep (se 1 (by rfl) ⟨1529801, by rfl⟩ : syracuseStep 2039735 = 3059603) B3059603
theorem B3442061 : Blo 2039435 3442061 := bbase (se 3 (by rfl) ⟨645386, by rfl⟩ : syracuseStep 3442061 = 1290773) (by norm_num)
theorem B2294707 : Blo 2039435 2294707 := bstep (se 1 (by rfl) ⟨1721030, by rfl⟩ : syracuseStep 2294707 = 3442061) B3442061
theorem B3059609 : Blo 2039435 3059609 := bstep (se 2 (by rfl) ⟨1147353, by rfl⟩ : syracuseStep 3059609 = 2294707) B2294707
theorem B2039739 : Blo 2039435 2039739 := bstep (se 1 (by rfl) ⟨1529804, by rfl⟩ : syracuseStep 2039739 = 3059609) B3059609
theorem B14702741 : Blo 2039435 14702741 := bbase (se 6 (by rfl) ⟨344595, by rfl⟩ : syracuseStep 14702741 = 689191) (by norm_num)
theorem B9801827 : Blo 2039435 9801827 := bstep (se 1 (by rfl) ⟨7351370, by rfl⟩ : syracuseStep 9801827 = 14702741) B14702741
theorem B6534551 : Blo 2039435 6534551 := bstep (se 1 (by rfl) ⟨4900913, by rfl⟩ : syracuseStep 6534551 = 9801827) B9801827
theorem B17425469 : Blo 2039435 17425469 := bstep (se 3 (by rfl) ⟨3267275, by rfl⟩ : syracuseStep 17425469 = 6534551) B6534551
theorem B11616979 : Blo 2039435 11616979 := bstep (se 1 (by rfl) ⟨8712734, by rfl⟩ : syracuseStep 11616979 = 17425469) B17425469
theorem B15489305 : Blo 2039435 15489305 := bstep (se 2 (by rfl) ⟨5808489, by rfl⟩ : syracuseStep 15489305 = 11616979) B11616979
theorem B10326203 : Blo 2039435 10326203 := bstep (se 1 (by rfl) ⟨7744652, by rfl⟩ : syracuseStep 10326203 = 15489305) B15489305
theorem B6884135 : Blo 2039435 6884135 := bstep (se 1 (by rfl) ⟨5163101, by rfl⟩ : syracuseStep 6884135 = 10326203) B10326203
theorem B4589423 : Blo 2039435 4589423 := bstep (se 1 (by rfl) ⟨3442067, by rfl⟩ : syracuseStep 4589423 = 6884135) B6884135
theorem B3059615 : Blo 2039435 3059615 := bstep (se 1 (by rfl) ⟨2294711, by rfl⟩ : syracuseStep 3059615 = 4589423) B4589423
theorem B2039743 : Blo 2039435 2039743 := bstep (se 1 (by rfl) ⟨1529807, by rfl⟩ : syracuseStep 2039743 = 3059615) B3059615
theorem B3059621 : Blo 2039435 3059621 := bbase (se 4 (by rfl) ⟨286839, by rfl⟩ : syracuseStep 3059621 = 573679) (by norm_num)
theorem B2039747 : Blo 2039435 2039747 := bstep (se 1 (by rfl) ⟨1529810, by rfl⟩ : syracuseStep 2039747 = 3059621) B3059621
theorem B2581561 : Blo 2039435 2581561 := bbase (se 2 (by rfl) ⟨968085, by rfl⟩ : syracuseStep 2581561 = 1936171) (by norm_num)
theorem B3442081 : Blo 2039435 3442081 := bstep (se 2 (by rfl) ⟨1290780, by rfl⟩ : syracuseStep 3442081 = 2581561) B2581561
theorem B4589441 : Blo 2039435 4589441 := bstep (se 2 (by rfl) ⟨1721040, by rfl⟩ : syracuseStep 4589441 = 3442081) B3442081
theorem B3059627 : Blo 2039435 3059627 := bstep (se 1 (by rfl) ⟨2294720, by rfl⟩ : syracuseStep 3059627 = 4589441) B4589441
theorem B2039751 : Blo 2039435 2039751 := bstep (se 1 (by rfl) ⟨1529813, by rfl⟩ : syracuseStep 2039751 = 3059627) B3059627
theorem B2294725 : Blo 2039435 2294725 := bbase (se 4 (by rfl) ⟨215130, by rfl⟩ : syracuseStep 2294725 = 430261) (by norm_num)
theorem B3059633 : Blo 2039435 3059633 := bstep (se 2 (by rfl) ⟨1147362, by rfl⟩ : syracuseStep 3059633 = 2294725) B2294725
theorem B2039755 : Blo 2039435 2039755 := bstep (se 1 (by rfl) ⟨1529816, by rfl⟩ : syracuseStep 2039755 = 3059633) B3059633
theorem B3872357 : Blo 2039435 3872357 := bbase (se 4 (by rfl) ⟨363033, by rfl⟩ : syracuseStep 3872357 = 726067) (by norm_num)
theorem B2581571 : Blo 2039435 2581571 := bstep (se 1 (by rfl) ⟨1936178, by rfl⟩ : syracuseStep 2581571 = 3872357) B3872357
theorem B6884189 : Blo 2039435 6884189 := bstep (se 3 (by rfl) ⟨1290785, by rfl⟩ : syracuseStep 6884189 = 2581571) B2581571
theorem B4589459 : Blo 2039435 4589459 := bstep (se 1 (by rfl) ⟨3442094, by rfl⟩ : syracuseStep 4589459 = 6884189) B6884189
theorem B3059639 : Blo 2039435 3059639 := bstep (se 1 (by rfl) ⟨2294729, by rfl⟩ : syracuseStep 3059639 = 4589459) B4589459
theorem B2039759 : Blo 2039435 2039759 := bstep (se 1 (by rfl) ⟨1529819, by rfl⟩ : syracuseStep 2039759 = 3059639) B3059639
theorem B3059645 : Blo 2039435 3059645 := bbase (se 3 (by rfl) ⟨573683, by rfl⟩ : syracuseStep 3059645 = 1147367) (by norm_num)
theorem B2039763 : Blo 2039435 2039763 := bstep (se 1 (by rfl) ⟨1529822, by rfl⟩ : syracuseStep 2039763 = 3059645) B3059645
theorem B4589477 : Blo 2039435 4589477 := bbase (se 4 (by rfl) ⟨430263, by rfl⟩ : syracuseStep 4589477 = 860527) (by norm_num)
theorem B3059651 : Blo 2039435 3059651 := bstep (se 1 (by rfl) ⟨2294738, by rfl⟩ : syracuseStep 3059651 = 4589477) B4589477
theorem B2039767 : Blo 2039435 2039767 := bstep (se 1 (by rfl) ⟨1529825, by rfl⟩ : syracuseStep 2039767 = 3059651) B3059651
theorem B5163173 : Blo 2039435 5163173 := bbase (se 4 (by rfl) ⟨484047, by rfl⟩ : syracuseStep 5163173 = 968095) (by norm_num)
theorem B3442115 : Blo 2039435 3442115 := bstep (se 1 (by rfl) ⟨2581586, by rfl⟩ : syracuseStep 3442115 = 5163173) B5163173
theorem B2294743 : Blo 2039435 2294743 := bstep (se 1 (by rfl) ⟨1721057, by rfl⟩ : syracuseStep 2294743 = 3442115) B3442115
theorem B3059657 : Blo 2039435 3059657 := bstep (se 2 (by rfl) ⟨1147371, by rfl⟩ : syracuseStep 3059657 = 2294743) B2294743
theorem B2039771 : Blo 2039435 2039771 := bstep (se 1 (by rfl) ⟨1529828, by rfl⟩ : syracuseStep 2039771 = 3059657) B3059657
theorem B5808581 : Blo 2039435 5808581 := bbase (se 4 (by rfl) ⟨544554, by rfl⟩ : syracuseStep 5808581 = 1089109) (by norm_num)
theorem B3872387 : Blo 2039435 3872387 := bstep (se 1 (by rfl) ⟨2904290, by rfl⟩ : syracuseStep 3872387 = 5808581) B5808581
theorem B10326365 : Blo 2039435 10326365 := bstep (se 3 (by rfl) ⟨1936193, by rfl⟩ : syracuseStep 10326365 = 3872387) B3872387
theorem B6884243 : Blo 2039435 6884243 := bstep (se 1 (by rfl) ⟨5163182, by rfl⟩ : syracuseStep 6884243 = 10326365) B10326365
theorem B4589495 : Blo 2039435 4589495 := bstep (se 1 (by rfl) ⟨3442121, by rfl⟩ : syracuseStep 4589495 = 6884243) B6884243
theorem B3059663 : Blo 2039435 3059663 := bstep (se 1 (by rfl) ⟨2294747, by rfl⟩ : syracuseStep 3059663 = 4589495) B4589495
theorem B2039775 : Blo 2039435 2039775 := bstep (se 1 (by rfl) ⟨1529831, by rfl⟩ : syracuseStep 2039775 = 3059663) B3059663
theorem B3059669 : Blo 2039435 3059669 := bbase (se 7 (by rfl) ⟨35855, by rfl⟩ : syracuseStep 3059669 = 71711) (by norm_num)
theorem B2039779 : Blo 2039435 2039779 := bstep (se 1 (by rfl) ⟨1529834, by rfl⟩ : syracuseStep 2039779 = 3059669) B3059669
theorem B7744805 : Blo 2039435 7744805 := bbase (se 4 (by rfl) ⟨726075, by rfl⟩ : syracuseStep 7744805 = 1452151) (by norm_num)
theorem B5163203 : Blo 2039435 5163203 := bstep (se 1 (by rfl) ⟨3872402, by rfl⟩ : syracuseStep 5163203 = 7744805) B7744805
theorem B3442135 : Blo 2039435 3442135 := bstep (se 1 (by rfl) ⟨2581601, by rfl⟩ : syracuseStep 3442135 = 5163203) B5163203
theorem B4589513 : Blo 2039435 4589513 := bstep (se 2 (by rfl) ⟨1721067, by rfl⟩ : syracuseStep 4589513 = 3442135) B3442135
theorem B3059675 : Blo 2039435 3059675 := bstep (se 1 (by rfl) ⟨2294756, by rfl⟩ : syracuseStep 3059675 = 4589513) B4589513
theorem B2039783 : Blo 2039435 2039783 := bstep (se 1 (by rfl) ⟨1529837, by rfl⟩ : syracuseStep 2039783 = 3059675) B3059675
theorem B2294761 : Blo 2039435 2294761 := bbase (se 2 (by rfl) ⟨860535, by rfl⟩ : syracuseStep 2294761 = 1721071) (by norm_num)
theorem B3059681 : Blo 2039435 3059681 := bstep (se 2 (by rfl) ⟨1147380, by rfl⟩ : syracuseStep 3059681 = 2294761) B2294761
theorem B2039787 : Blo 2039435 2039787 := bstep (se 1 (by rfl) ⟨1529840, by rfl⟩ : syracuseStep 2039787 = 3059681) B3059681
theorem B3675773 : Blo 2039435 3675773 := bbase (se 3 (by rfl) ⟨689207, by rfl⟩ : syracuseStep 3675773 = 1378415) (by norm_num)
theorem B2450515 : Blo 2039435 2450515 := bstep (se 1 (by rfl) ⟨1837886, by rfl⟩ : syracuseStep 2450515 = 3675773) B3675773
theorem B3267353 : Blo 2039435 3267353 := bstep (se 2 (by rfl) ⟨1225257, by rfl⟩ : syracuseStep 3267353 = 2450515) B2450515
theorem B2178235 : Blo 2039435 2178235 := bstep (se 1 (by rfl) ⟨1633676, by rfl⟩ : syracuseStep 2178235 = 3267353) B3267353
theorem B11617253 : Blo 2039435 11617253 := bstep (se 4 (by rfl) ⟨1089117, by rfl⟩ : syracuseStep 11617253 = 2178235) B2178235
theorem B7744835 : Blo 2039435 7744835 := bstep (se 1 (by rfl) ⟨5808626, by rfl⟩ : syracuseStep 7744835 = 11617253) B11617253
theorem B5163223 : Blo 2039435 5163223 := bstep (se 1 (by rfl) ⟨3872417, by rfl⟩ : syracuseStep 5163223 = 7744835) B7744835
theorem B6884297 : Blo 2039435 6884297 := bstep (se 2 (by rfl) ⟨2581611, by rfl⟩ : syracuseStep 6884297 = 5163223) B5163223
theorem B4589531 : Blo 2039435 4589531 := bstep (se 1 (by rfl) ⟨3442148, by rfl⟩ : syracuseStep 4589531 = 6884297) B6884297
theorem B3059687 : Blo 2039435 3059687 := bstep (se 1 (by rfl) ⟨2294765, by rfl⟩ : syracuseStep 3059687 = 4589531) B4589531
theorem B2039791 : Blo 2039435 2039791 := bstep (se 1 (by rfl) ⟨1529843, by rfl⟩ : syracuseStep 2039791 = 3059687) B3059687
theorem B3059693 : Blo 2039435 3059693 := bbase (se 3 (by rfl) ⟨573692, by rfl⟩ : syracuseStep 3059693 = 1147385) (by norm_num)
theorem B2039795 : Blo 2039435 2039795 := bstep (se 1 (by rfl) ⟨1529846, by rfl⟩ : syracuseStep 2039795 = 3059693) B3059693
theorem B4589549 : Blo 2039435 4589549 := bbase (se 3 (by rfl) ⟨860540, by rfl⟩ : syracuseStep 4589549 = 1721081) (by norm_num)
theorem B3059699 : Blo 2039435 3059699 := bstep (se 1 (by rfl) ⟨2294774, by rfl⟩ : syracuseStep 3059699 = 4589549) B4589549
theorem B2039799 : Blo 2039435 2039799 := bstep (se 1 (by rfl) ⟨1529849, by rfl⟩ : syracuseStep 2039799 = 3059699) B3059699
theorem B3267373 : Blo 2039435 3267373 := bbase (se 3 (by rfl) ⟨612632, by rfl⟩ : syracuseStep 3267373 = 1225265) (by norm_num)
theorem B4356497 : Blo 2039435 4356497 := bstep (se 2 (by rfl) ⟨1633686, by rfl⟩ : syracuseStep 4356497 = 3267373) B3267373
theorem B2904331 : Blo 2039435 2904331 := bstep (se 1 (by rfl) ⟨2178248, by rfl⟩ : syracuseStep 2904331 = 4356497) B4356497
theorem B3872441 : Blo 2039435 3872441 := bstep (se 2 (by rfl) ⟨1452165, by rfl⟩ : syracuseStep 3872441 = 2904331) B2904331
theorem B2581627 : Blo 2039435 2581627 := bstep (se 1 (by rfl) ⟨1936220, by rfl⟩ : syracuseStep 2581627 = 3872441) B3872441
theorem B3442169 : Blo 2039435 3442169 := bstep (se 2 (by rfl) ⟨1290813, by rfl⟩ : syracuseStep 3442169 = 2581627) B2581627
theorem B2294779 : Blo 2039435 2294779 := bstep (se 1 (by rfl) ⟨1721084, by rfl⟩ : syracuseStep 2294779 = 3442169) B3442169
theorem B3059705 : Blo 2039435 3059705 := bstep (se 2 (by rfl) ⟨1147389, by rfl⟩ : syracuseStep 3059705 = 2294779) B2294779
theorem B2039803 : Blo 2039435 2039803 := bstep (se 1 (by rfl) ⟨1529852, by rfl⟩ : syracuseStep 2039803 = 3059705) B3059705
theorem B7553573 : Blo 2039435 7553573 := bbase (se 4 (by rfl) ⟨708147, by rfl⟩ : syracuseStep 7553573 = 1416295) (by norm_num)
theorem B5035715 : Blo 2039435 5035715 := bstep (se 1 (by rfl) ⟨3776786, by rfl⟩ : syracuseStep 5035715 = 7553573) B7553573
theorem B3357143 : Blo 2039435 3357143 := bstep (se 1 (by rfl) ⟨2517857, by rfl⟩ : syracuseStep 3357143 = 5035715) B5035715
theorem B2238095 : Blo 2039435 2238095 := bstep (se 1 (by rfl) ⟨1678571, by rfl⟩ : syracuseStep 2238095 = 3357143) B3357143
theorem B5968253 : Blo 2039435 5968253 := bstep (se 3 (by rfl) ⟨1119047, by rfl⟩ : syracuseStep 5968253 = 2238095) B2238095
theorem B15915341 : Blo 2039435 15915341 := bstep (se 3 (by rfl) ⟨2984126, by rfl⟩ : syracuseStep 15915341 = 5968253) B5968253
theorem B10610227 : Blo 2039435 10610227 := bstep (se 1 (by rfl) ⟨7957670, by rfl⟩ : syracuseStep 10610227 = 15915341) B15915341
theorem B14146969 : Blo 2039435 14146969 := bstep (se 2 (by rfl) ⟨5305113, by rfl⟩ : syracuseStep 14146969 = 10610227) B10610227
theorem B18862625 : Blo 2039435 18862625 := bstep (se 2 (by rfl) ⟨7073484, by rfl⟩ : syracuseStep 18862625 = 14146969) B14146969
theorem B12575083 : Blo 2039435 12575083 := bstep (se 1 (by rfl) ⟨9431312, by rfl⟩ : syracuseStep 12575083 = 18862625) B18862625
theorem B16766777 : Blo 2039435 16766777 := bstep (se 2 (by rfl) ⟨6287541, by rfl⟩ : syracuseStep 16766777 = 12575083) B12575083
theorem B44711405 : Blo 2039435 44711405 := bstep (se 3 (by rfl) ⟨8383388, by rfl⟩ : syracuseStep 44711405 = 16766777) B16766777
theorem B29807603 : Blo 2039435 29807603 := bstep (se 1 (by rfl) ⟨22355702, by rfl⟩ : syracuseStep 29807603 = 44711405) B44711405
theorem B19871735 : Blo 2039435 19871735 := bstep (se 1 (by rfl) ⟨14903801, by rfl⟩ : syracuseStep 19871735 = 29807603) B29807603
theorem B52991293 : Blo 2039435 52991293 := bstep (se 3 (by rfl) ⟨9935867, by rfl⟩ : syracuseStep 52991293 = 19871735) B19871735
theorem B70655057 : Blo 2039435 70655057 := bstep (se 2 (by rfl) ⟨26495646, by rfl⟩ : syracuseStep 70655057 = 52991293) B52991293
theorem B47103371 : Blo 2039435 47103371 := bstep (se 1 (by rfl) ⟨35327528, by rfl⟩ : syracuseStep 47103371 = 70655057) B70655057
theorem B31402247 : Blo 2039435 31402247 := bstep (se 1 (by rfl) ⟨23551685, by rfl⟩ : syracuseStep 31402247 = 47103371) B47103371
theorem B83739325 : Blo 2039435 83739325 := bstep (se 3 (by rfl) ⟨15701123, by rfl⟩ : syracuseStep 83739325 = 31402247) B31402247
theorem B111652433 : Blo 2039435 111652433 := bstep (se 2 (by rfl) ⟨41869662, by rfl⟩ : syracuseStep 111652433 = 83739325) B83739325
theorem B74434955 : Blo 2039435 74434955 := bstep (se 1 (by rfl) ⟨55826216, by rfl⟩ : syracuseStep 74434955 = 111652433) B111652433
theorem B198493213 : Blo 2039435 198493213 := bstep (se 3 (by rfl) ⟨37217477, by rfl⟩ : syracuseStep 198493213 = 74434955) B74434955
theorem B264657617 : Blo 2039435 264657617 := bstep (se 2 (by rfl) ⟨99246606, by rfl⟩ : syracuseStep 264657617 = 198493213) B198493213
theorem B176438411 : Blo 2039435 176438411 := bstep (se 1 (by rfl) ⟨132328808, by rfl⟩ : syracuseStep 176438411 = 264657617) B264657617
theorem B117625607 : Blo 2039435 117625607 := bstep (se 1 (by rfl) ⟨88219205, by rfl⟩ : syracuseStep 117625607 = 176438411) B176438411
theorem B78417071 : Blo 2039435 78417071 := bstep (se 1 (by rfl) ⟨58812803, by rfl⟩ : syracuseStep 78417071 = 117625607) B117625607
theorem B52278047 : Blo 2039435 52278047 := bstep (se 1 (by rfl) ⟨39208535, by rfl⟩ : syracuseStep 52278047 = 78417071) B78417071
theorem B34852031 : Blo 2039435 34852031 := bstep (se 1 (by rfl) ⟨26139023, by rfl⟩ : syracuseStep 34852031 = 52278047) B52278047
theorem B23234687 : Blo 2039435 23234687 := bstep (se 1 (by rfl) ⟨17426015, by rfl⟩ : syracuseStep 23234687 = 34852031) B34852031
theorem B15489791 : Blo 2039435 15489791 := bstep (se 1 (by rfl) ⟨11617343, by rfl⟩ : syracuseStep 15489791 = 23234687) B23234687
theorem B10326527 : Blo 2039435 10326527 := bstep (se 1 (by rfl) ⟨7744895, by rfl⟩ : syracuseStep 10326527 = 15489791) B15489791
theorem B6884351 : Blo 2039435 6884351 := bstep (se 1 (by rfl) ⟨5163263, by rfl⟩ : syracuseStep 6884351 = 10326527) B10326527
theorem B4589567 : Blo 2039435 4589567 := bstep (se 1 (by rfl) ⟨3442175, by rfl⟩ : syracuseStep 4589567 = 6884351) B6884351
theorem B3059711 : Blo 2039435 3059711 := bstep (se 1 (by rfl) ⟨2294783, by rfl⟩ : syracuseStep 3059711 = 4589567) B4589567
theorem B2039807 : Blo 2039435 2039807 := bstep (se 1 (by rfl) ⟨1529855, by rfl⟩ : syracuseStep 2039807 = 3059711) B3059711
theorem B3059717 : Blo 2039435 3059717 := bbase (se 4 (by rfl) ⟨286848, by rfl⟩ : syracuseStep 3059717 = 573697) (by norm_num)
theorem B2039811 : Blo 2039435 2039811 := bstep (se 1 (by rfl) ⟨1529858, by rfl⟩ : syracuseStep 2039811 = 3059717) B3059717
theorem B3442189 : Blo 2039435 3442189 := bbase (se 3 (by rfl) ⟨645410, by rfl⟩ : syracuseStep 3442189 = 1290821) (by norm_num)
theorem B4589585 : Blo 2039435 4589585 := bstep (se 2 (by rfl) ⟨1721094, by rfl⟩ : syracuseStep 4589585 = 3442189) B3442189
theorem B3059723 : Blo 2039435 3059723 := bstep (se 1 (by rfl) ⟨2294792, by rfl⟩ : syracuseStep 3059723 = 4589585) B4589585
theorem B2039815 : Blo 2039435 2039815 := bstep (se 1 (by rfl) ⟨1529861, by rfl⟩ : syracuseStep 2039815 = 3059723) B3059723
theorem B2294797 : Blo 2039435 2294797 := bbase (se 3 (by rfl) ⟨430274, by rfl⟩ : syracuseStep 2294797 = 860549) (by norm_num)
theorem B3059729 : Blo 2039435 3059729 := bstep (se 2 (by rfl) ⟨1147398, by rfl⟩ : syracuseStep 3059729 = 2294797) B2294797
theorem B2039819 : Blo 2039435 2039819 := bstep (se 1 (by rfl) ⟨1529864, by rfl⟩ : syracuseStep 2039819 = 3059729) B3059729
theorem B6884405 : Blo 2039435 6884405 := bbase (se 5 (by rfl) ⟨322706, by rfl⟩ : syracuseStep 6884405 = 645413) (by norm_num)
theorem B4589603 : Blo 2039435 4589603 := bstep (se 1 (by rfl) ⟨3442202, by rfl⟩ : syracuseStep 4589603 = 6884405) B6884405
theorem B3059735 : Blo 2039435 3059735 := bstep (se 1 (by rfl) ⟨2294801, by rfl⟩ : syracuseStep 3059735 = 4589603) B4589603
theorem B2039823 : Blo 2039435 2039823 := bstep (se 1 (by rfl) ⟨1529867, by rfl⟩ : syracuseStep 2039823 = 3059735) B3059735
theorem B3059741 : Blo 2039435 3059741 := bbase (se 3 (by rfl) ⟨573701, by rfl⟩ : syracuseStep 3059741 = 1147403) (by norm_num)
theorem B2039827 : Blo 2039435 2039827 := bstep (se 1 (by rfl) ⟨1529870, by rfl⟩ : syracuseStep 2039827 = 3059741) B3059741
theorem B4589621 : Blo 2039435 4589621 := bbase (se 5 (by rfl) ⟨215138, by rfl⟩ : syracuseStep 4589621 = 430277) (by norm_num)
theorem B3059747 : Blo 2039435 3059747 := bstep (se 1 (by rfl) ⟨2294810, by rfl⟩ : syracuseStep 3059747 = 4589621) B4589621
theorem B2039831 : Blo 2039435 2039831 := bstep (se 1 (by rfl) ⟨1529873, by rfl⟩ : syracuseStep 2039831 = 3059747) B3059747
theorem B2095877 : Blo 2039435 2095877 := bbase (se 4 (by rfl) ⟨196488, by rfl⟩ : syracuseStep 2095877 = 392977) (by norm_num)
theorem B5589005 : Blo 2039435 5589005 := bstep (se 3 (by rfl) ⟨1047938, by rfl⟩ : syracuseStep 5589005 = 2095877) B2095877
theorem B14904013 : Blo 2039435 14904013 := bstep (se 3 (by rfl) ⟨2794502, by rfl⟩ : syracuseStep 14904013 = 5589005) B5589005
theorem B19872017 : Blo 2039435 19872017 := bstep (se 2 (by rfl) ⟨7452006, by rfl⟩ : syracuseStep 19872017 = 14904013) B14904013
theorem B13248011 : Blo 2039435 13248011 := bstep (se 1 (by rfl) ⟨9936008, by rfl⟩ : syracuseStep 13248011 = 19872017) B19872017
theorem B8832007 : Blo 2039435 8832007 := bstep (se 1 (by rfl) ⟨6624005, by rfl⟩ : syracuseStep 8832007 = 13248011) B13248011
theorem B11776009 : Blo 2039435 11776009 := bstep (se 2 (by rfl) ⟨4416003, by rfl⟩ : syracuseStep 11776009 = 8832007) B8832007
theorem B15701345 : Blo 2039435 15701345 := bstep (se 2 (by rfl) ⟨5888004, by rfl⟩ : syracuseStep 15701345 = 11776009) B11776009
theorem B10467563 : Blo 2039435 10467563 := bstep (se 1 (by rfl) ⟨7850672, by rfl⟩ : syracuseStep 10467563 = 15701345) B15701345
theorem B27913501 : Blo 2039435 27913501 := bstep (se 3 (by rfl) ⟨5233781, by rfl⟩ : syracuseStep 27913501 = 10467563) B10467563
theorem B37218001 : Blo 2039435 37218001 := bstep (se 2 (by rfl) ⟨13956750, by rfl⟩ : syracuseStep 37218001 = 27913501) B27913501
theorem B49624001 : Blo 2039435 49624001 := bstep (se 2 (by rfl) ⟨18609000, by rfl⟩ : syracuseStep 49624001 = 37218001) B37218001
theorem B33082667 : Blo 2039435 33082667 := bstep (se 1 (by rfl) ⟨24812000, by rfl⟩ : syracuseStep 33082667 = 49624001) B49624001
theorem B22055111 : Blo 2039435 22055111 := bstep (se 1 (by rfl) ⟨16541333, by rfl⟩ : syracuseStep 22055111 = 33082667) B33082667
theorem B14703407 : Blo 2039435 14703407 := bstep (se 1 (by rfl) ⟨11027555, by rfl⟩ : syracuseStep 14703407 = 22055111) B22055111
theorem B9802271 : Blo 2039435 9802271 := bstep (se 1 (by rfl) ⟨7351703, by rfl⟩ : syracuseStep 9802271 = 14703407) B14703407
theorem B6534847 : Blo 2039435 6534847 := bstep (se 1 (by rfl) ⟨4901135, by rfl⟩ : syracuseStep 6534847 = 9802271) B9802271
theorem B8713129 : Blo 2039435 8713129 := bstep (se 2 (by rfl) ⟨3267423, by rfl⟩ : syracuseStep 8713129 = 6534847) B6534847
theorem B11617505 : Blo 2039435 11617505 := bstep (se 2 (by rfl) ⟨4356564, by rfl⟩ : syracuseStep 11617505 = 8713129) B8713129
theorem B7745003 : Blo 2039435 7745003 := bstep (se 1 (by rfl) ⟨5808752, by rfl⟩ : syracuseStep 7745003 = 11617505) B11617505
theorem B5163335 : Blo 2039435 5163335 := bstep (se 1 (by rfl) ⟨3872501, by rfl⟩ : syracuseStep 5163335 = 7745003) B7745003
theorem B3442223 : Blo 2039435 3442223 := bstep (se 1 (by rfl) ⟨2581667, by rfl⟩ : syracuseStep 3442223 = 5163335) B5163335
theorem B2294815 : Blo 2039435 2294815 := bstep (se 1 (by rfl) ⟨1721111, by rfl⟩ : syracuseStep 2294815 = 3442223) B3442223
theorem B3059753 : Blo 2039435 3059753 := bstep (se 2 (by rfl) ⟨1147407, by rfl⟩ : syracuseStep 3059753 = 2294815) B2294815
theorem B2039835 : Blo 2039435 2039835 := bstep (se 1 (by rfl) ⟨1529876, by rfl⟩ : syracuseStep 2039835 = 3059753) B3059753
theorem B7351717 : Blo 2039435 7351717 := bbase (se 4 (by rfl) ⟨689223, by rfl⟩ : syracuseStep 7351717 = 1378447) (by norm_num)
theorem B9802289 : Blo 2039435 9802289 := bstep (se 2 (by rfl) ⟨3675858, by rfl⟩ : syracuseStep 9802289 = 7351717) B7351717
theorem B6534859 : Blo 2039435 6534859 := bstep (se 1 (by rfl) ⟨4901144, by rfl⟩ : syracuseStep 6534859 = 9802289) B9802289
theorem B8713145 : Blo 2039435 8713145 := bstep (se 2 (by rfl) ⟨3267429, by rfl⟩ : syracuseStep 8713145 = 6534859) B6534859
theorem B5808763 : Blo 2039435 5808763 := bstep (se 1 (by rfl) ⟨4356572, by rfl⟩ : syracuseStep 5808763 = 8713145) B8713145
theorem B7745017 : Blo 2039435 7745017 := bstep (se 2 (by rfl) ⟨2904381, by rfl⟩ : syracuseStep 7745017 = 5808763) B5808763
theorem B10326689 : Blo 2039435 10326689 := bstep (se 2 (by rfl) ⟨3872508, by rfl⟩ : syracuseStep 10326689 = 7745017) B7745017
theorem B6884459 : Blo 2039435 6884459 := bstep (se 1 (by rfl) ⟨5163344, by rfl⟩ : syracuseStep 6884459 = 10326689) B10326689
theorem B4589639 : Blo 2039435 4589639 := bstep (se 1 (by rfl) ⟨3442229, by rfl⟩ : syracuseStep 4589639 = 6884459) B6884459
theorem B3059759 : Blo 2039435 3059759 := bstep (se 1 (by rfl) ⟨2294819, by rfl⟩ : syracuseStep 3059759 = 4589639) B4589639
theorem B2039839 : Blo 2039435 2039839 := bstep (se 1 (by rfl) ⟨1529879, by rfl⟩ : syracuseStep 2039839 = 3059759) B3059759
theorem B3059765 : Blo 2039435 3059765 := bbase (se 5 (by rfl) ⟨143426, by rfl⟩ : syracuseStep 3059765 = 286853) (by norm_num)
theorem B2039843 : Blo 2039435 2039843 := bstep (se 1 (by rfl) ⟨1529882, by rfl⟩ : syracuseStep 2039843 = 3059765) B3059765
theorem B5163365 : Blo 2039435 5163365 := bbase (se 4 (by rfl) ⟨484065, by rfl⟩ : syracuseStep 5163365 = 968131) (by norm_num)
theorem B3442243 : Blo 2039435 3442243 := bstep (se 1 (by rfl) ⟨2581682, by rfl⟩ : syracuseStep 3442243 = 5163365) B5163365
theorem B4589657 : Blo 2039435 4589657 := bstep (se 2 (by rfl) ⟨1721121, by rfl⟩ : syracuseStep 4589657 = 3442243) B3442243
theorem B3059771 : Blo 2039435 3059771 := bstep (se 1 (by rfl) ⟨2294828, by rfl⟩ : syracuseStep 3059771 = 4589657) B4589657
theorem B2039847 : Blo 2039435 2039847 := bstep (se 1 (by rfl) ⟨1529885, by rfl⟩ : syracuseStep 2039847 = 3059771) B3059771
theorem B2294833 : Blo 2039435 2294833 := bbase (se 2 (by rfl) ⟨860562, by rfl⟩ : syracuseStep 2294833 = 1721125) (by norm_num)
theorem B3059777 : Blo 2039435 3059777 := bstep (se 2 (by rfl) ⟨1147416, by rfl⟩ : syracuseStep 3059777 = 2294833) B2294833
theorem B2039851 : Blo 2039435 2039851 := bstep (se 1 (by rfl) ⟨1529888, by rfl⟩ : syracuseStep 2039851 = 3059777) B3059777
theorem B8383589 : Blo 2039435 8383589 := bbase (se 4 (by rfl) ⟨785961, by rfl⟩ : syracuseStep 8383589 = 1571923) (by norm_num)
theorem B5589059 : Blo 2039435 5589059 := bstep (se 1 (by rfl) ⟨4191794, by rfl⟩ : syracuseStep 5589059 = 8383589) B8383589
theorem B14904157 : Blo 2039435 14904157 := bstep (se 3 (by rfl) ⟨2794529, by rfl⟩ : syracuseStep 14904157 = 5589059) B5589059
theorem B19872209 : Blo 2039435 19872209 := bstep (se 2 (by rfl) ⟨7452078, by rfl⟩ : syracuseStep 19872209 = 14904157) B14904157
theorem B52992557 : Blo 2039435 52992557 := bstep (se 3 (by rfl) ⟨9936104, by rfl⟩ : syracuseStep 52992557 = 19872209) B19872209
theorem B35328371 : Blo 2039435 35328371 := bstep (se 1 (by rfl) ⟨26496278, by rfl⟩ : syracuseStep 35328371 = 52992557) B52992557
theorem B94208989 : Blo 2039435 94208989 := bstep (se 3 (by rfl) ⟨17664185, by rfl⟩ : syracuseStep 94208989 = 35328371) B35328371
theorem B125611985 : Blo 2039435 125611985 := bstep (se 2 (by rfl) ⟨47104494, by rfl⟩ : syracuseStep 125611985 = 94208989) B94208989
theorem B83741323 : Blo 2039435 83741323 := bstep (se 1 (by rfl) ⟨62805992, by rfl⟩ : syracuseStep 83741323 = 125611985) B125611985
theorem B111655097 : Blo 2039435 111655097 := bstep (se 2 (by rfl) ⟨41870661, by rfl⟩ : syracuseStep 111655097 = 83741323) B83741323
theorem B74436731 : Blo 2039435 74436731 := bstep (se 1 (by rfl) ⟨55827548, by rfl⟩ : syracuseStep 74436731 = 111655097) B111655097
theorem B49624487 : Blo 2039435 49624487 := bstep (se 1 (by rfl) ⟨37218365, by rfl⟩ : syracuseStep 49624487 = 74436731) B74436731
theorem B33082991 : Blo 2039435 33082991 := bstep (se 1 (by rfl) ⟨24812243, by rfl⟩ : syracuseStep 33082991 = 49624487) B49624487
theorem B22055327 : Blo 2039435 22055327 := bstep (se 1 (by rfl) ⟨16541495, by rfl⟩ : syracuseStep 22055327 = 33082991) B33082991
theorem B14703551 : Blo 2039435 14703551 := bstep (se 1 (by rfl) ⟨11027663, by rfl⟩ : syracuseStep 14703551 = 22055327) B22055327
theorem B9802367 : Blo 2039435 9802367 := bstep (se 1 (by rfl) ⟨7351775, by rfl⟩ : syracuseStep 9802367 = 14703551) B14703551
theorem B6534911 : Blo 2039435 6534911 := bstep (se 1 (by rfl) ⟨4901183, by rfl⟩ : syracuseStep 6534911 = 9802367) B9802367
theorem B4356607 : Blo 2039435 4356607 := bstep (se 1 (by rfl) ⟨3267455, by rfl⟩ : syracuseStep 4356607 = 6534911) B6534911
theorem B5808809 : Blo 2039435 5808809 := bstep (se 2 (by rfl) ⟨2178303, by rfl⟩ : syracuseStep 5808809 = 4356607) B4356607
theorem B3872539 : Blo 2039435 3872539 := bstep (se 1 (by rfl) ⟨2904404, by rfl⟩ : syracuseStep 3872539 = 5808809) B5808809
theorem B5163385 : Blo 2039435 5163385 := bstep (se 2 (by rfl) ⟨1936269, by rfl⟩ : syracuseStep 5163385 = 3872539) B3872539
theorem B6884513 : Blo 2039435 6884513 := bstep (se 2 (by rfl) ⟨2581692, by rfl⟩ : syracuseStep 6884513 = 5163385) B5163385
theorem B4589675 : Blo 2039435 4589675 := bstep (se 1 (by rfl) ⟨3442256, by rfl⟩ : syracuseStep 4589675 = 6884513) B6884513
theorem B3059783 : Blo 2039435 3059783 := bstep (se 1 (by rfl) ⟨2294837, by rfl⟩ : syracuseStep 3059783 = 4589675) B4589675
theorem B2039855 : Blo 2039435 2039855 := bstep (se 1 (by rfl) ⟨1529891, by rfl⟩ : syracuseStep 2039855 = 3059783) B3059783
theorem B3059789 : Blo 2039435 3059789 := bbase (se 3 (by rfl) ⟨573710, by rfl⟩ : syracuseStep 3059789 = 1147421) (by norm_num)
theorem B2039859 : Blo 2039435 2039859 := bstep (se 1 (by rfl) ⟨1529894, by rfl⟩ : syracuseStep 2039859 = 3059789) B3059789
theorem B4589693 : Blo 2039435 4589693 := bbase (se 3 (by rfl) ⟨860567, by rfl⟩ : syracuseStep 4589693 = 1721135) (by norm_num)
theorem B3059795 : Blo 2039435 3059795 := bstep (se 1 (by rfl) ⟨2294846, by rfl⟩ : syracuseStep 3059795 = 4589693) B4589693
theorem B2039863 : Blo 2039435 2039863 := bstep (se 1 (by rfl) ⟨1529897, by rfl⟩ : syracuseStep 2039863 = 3059795) B3059795
theorem B3442277 : Blo 2039435 3442277 := bbase (se 4 (by rfl) ⟨322713, by rfl⟩ : syracuseStep 3442277 = 645427) (by norm_num)
theorem B2294851 : Blo 2039435 2294851 := bstep (se 1 (by rfl) ⟨1721138, by rfl⟩ : syracuseStep 2294851 = 3442277) B3442277
theorem B3059801 : Blo 2039435 3059801 := bstep (se 2 (by rfl) ⟨1147425, by rfl⟩ : syracuseStep 3059801 = 2294851) B2294851
theorem B2039867 : Blo 2039435 2039867 := bstep (se 1 (by rfl) ⟨1529900, by rfl⟩ : syracuseStep 2039867 = 3059801) B3059801
theorem B3675917 : Blo 2039435 3675917 := bbase (se 3 (by rfl) ⟨689234, by rfl⟩ : syracuseStep 3675917 = 1378469) (by norm_num)
theorem B2450611 : Blo 2039435 2450611 := bstep (se 1 (by rfl) ⟨1837958, by rfl⟩ : syracuseStep 2450611 = 3675917) B3675917
theorem B3267481 : Blo 2039435 3267481 := bstep (se 2 (by rfl) ⟨1225305, by rfl⟩ : syracuseStep 3267481 = 2450611) B2450611
theorem B4356641 : Blo 2039435 4356641 := bstep (se 2 (by rfl) ⟨1633740, by rfl⟩ : syracuseStep 4356641 = 3267481) B3267481
theorem B2904427 : Blo 2039435 2904427 := bstep (se 1 (by rfl) ⟨2178320, by rfl⟩ : syracuseStep 2904427 = 4356641) B4356641
theorem B15490277 : Blo 2039435 15490277 := bstep (se 4 (by rfl) ⟨1452213, by rfl⟩ : syracuseStep 15490277 = 2904427) B2904427
theorem B10326851 : Blo 2039435 10326851 := bstep (se 1 (by rfl) ⟨7745138, by rfl⟩ : syracuseStep 10326851 = 15490277) B15490277
theorem B6884567 : Blo 2039435 6884567 := bstep (se 1 (by rfl) ⟨5163425, by rfl⟩ : syracuseStep 6884567 = 10326851) B10326851
theorem B4589711 : Blo 2039435 4589711 := bstep (se 1 (by rfl) ⟨3442283, by rfl⟩ : syracuseStep 4589711 = 6884567) B6884567
theorem B3059807 : Blo 2039435 3059807 := bstep (se 1 (by rfl) ⟨2294855, by rfl⟩ : syracuseStep 3059807 = 4589711) B4589711
theorem B2039871 : Blo 2039435 2039871 := bstep (se 1 (by rfl) ⟨1529903, by rfl⟩ : syracuseStep 2039871 = 3059807) B3059807
theorem B3059813 : Blo 2039435 3059813 := bbase (se 4 (by rfl) ⟨286857, by rfl⟩ : syracuseStep 3059813 = 573715) (by norm_num)
theorem B2039875 : Blo 2039435 2039875 := bstep (se 1 (by rfl) ⟨1529906, by rfl⟩ : syracuseStep 2039875 = 3059813) B3059813
theorem B2450621 : Blo 2039435 2450621 := bbase (se 3 (by rfl) ⟨459491, by rfl⟩ : syracuseStep 2450621 = 918983) (by norm_num)
theorem B6534989 : Blo 2039435 6534989 := bstep (se 3 (by rfl) ⟨1225310, by rfl⟩ : syracuseStep 6534989 = 2450621) B2450621
theorem B4356659 : Blo 2039435 4356659 := bstep (se 1 (by rfl) ⟨3267494, by rfl⟩ : syracuseStep 4356659 = 6534989) B6534989
theorem B2904439 : Blo 2039435 2904439 := bstep (se 1 (by rfl) ⟨2178329, by rfl⟩ : syracuseStep 2904439 = 4356659) B4356659
theorem B3872585 : Blo 2039435 3872585 := bstep (se 2 (by rfl) ⟨1452219, by rfl⟩ : syracuseStep 3872585 = 2904439) B2904439
theorem B2581723 : Blo 2039435 2581723 := bstep (se 1 (by rfl) ⟨1936292, by rfl⟩ : syracuseStep 2581723 = 3872585) B3872585
theorem B3442297 : Blo 2039435 3442297 := bstep (se 2 (by rfl) ⟨1290861, by rfl⟩ : syracuseStep 3442297 = 2581723) B2581723
theorem B4589729 : Blo 2039435 4589729 := bstep (se 2 (by rfl) ⟨1721148, by rfl⟩ : syracuseStep 4589729 = 3442297) B3442297
theorem B3059819 : Blo 2039435 3059819 := bstep (se 1 (by rfl) ⟨2294864, by rfl⟩ : syracuseStep 3059819 = 4589729) B4589729
theorem B2039879 : Blo 2039435 2039879 := bstep (se 1 (by rfl) ⟨1529909, by rfl⟩ : syracuseStep 2039879 = 3059819) B3059819
theorem B2294869 : Blo 2039435 2294869 := bbase (se 8 (by rfl) ⟨13446, by rfl⟩ : syracuseStep 2294869 = 26893) (by norm_num)
theorem B3059825 : Blo 2039435 3059825 := bstep (se 2 (by rfl) ⟨1147434, by rfl⟩ : syracuseStep 3059825 = 2294869) B2294869
theorem B2039883 : Blo 2039435 2039883 := bstep (se 1 (by rfl) ⟨1529912, by rfl⟩ : syracuseStep 2039883 = 3059825) B3059825
theorem B2581733 : Blo 2039435 2581733 := bbase (se 4 (by rfl) ⟨242037, by rfl⟩ : syracuseStep 2581733 = 484075) (by norm_num)
theorem B6884621 : Blo 2039435 6884621 := bstep (se 3 (by rfl) ⟨1290866, by rfl⟩ : syracuseStep 6884621 = 2581733) B2581733
theorem B4589747 : Blo 2039435 4589747 := bstep (se 1 (by rfl) ⟨3442310, by rfl⟩ : syracuseStep 4589747 = 6884621) B6884621
theorem B3059831 : Blo 2039435 3059831 := bstep (se 1 (by rfl) ⟨2294873, by rfl⟩ : syracuseStep 3059831 = 4589747) B4589747
theorem B2039887 : Blo 2039435 2039887 := bstep (se 1 (by rfl) ⟨1529915, by rfl⟩ : syracuseStep 2039887 = 3059831) B3059831
theorem B3059837 : Blo 2039435 3059837 := bbase (se 3 (by rfl) ⟨573719, by rfl⟩ : syracuseStep 3059837 = 1147439) (by norm_num)
theorem B2039891 : Blo 2039435 2039891 := bstep (se 1 (by rfl) ⟨1529918, by rfl⟩ : syracuseStep 2039891 = 3059837) B3059837
theorem B4589765 : Blo 2039435 4589765 := bbase (se 4 (by rfl) ⟨430290, by rfl⟩ : syracuseStep 4589765 = 860581) (by norm_num)
theorem B3059843 : Blo 2039435 3059843 := bstep (se 1 (by rfl) ⟨2294882, by rfl⟩ : syracuseStep 3059843 = 4589765) B4589765
theorem B2039895 : Blo 2039435 2039895 := bstep (se 1 (by rfl) ⟨1529921, by rfl⟩ : syracuseStep 2039895 = 3059843) B3059843
theorem B10467893 : Blo 2039435 10467893 := bbase (se 5 (by rfl) ⟨490682, by rfl⟩ : syracuseStep 10467893 = 981365) (by norm_num)
theorem B27914381 : Blo 2039435 27914381 := bstep (se 3 (by rfl) ⟨5233946, by rfl⟩ : syracuseStep 27914381 = 10467893) B10467893
theorem B18609587 : Blo 2039435 18609587 := bstep (se 1 (by rfl) ⟨13957190, by rfl⟩ : syracuseStep 18609587 = 27914381) B27914381
theorem B12406391 : Blo 2039435 12406391 := bstep (se 1 (by rfl) ⟨9304793, by rfl⟩ : syracuseStep 12406391 = 18609587) B18609587
theorem B8270927 : Blo 2039435 8270927 := bstep (se 1 (by rfl) ⟨6203195, by rfl⟩ : syracuseStep 8270927 = 12406391) B12406391
theorem B5513951 : Blo 2039435 5513951 := bstep (se 1 (by rfl) ⟨4135463, by rfl⟩ : syracuseStep 5513951 = 8270927) B8270927
theorem B14703869 : Blo 2039435 14703869 := bstep (se 3 (by rfl) ⟨2756975, by rfl⟩ : syracuseStep 14703869 = 5513951) B5513951
theorem B9802579 : Blo 2039435 9802579 := bstep (se 1 (by rfl) ⟨7351934, by rfl⟩ : syracuseStep 9802579 = 14703869) B14703869
theorem B13070105 : Blo 2039435 13070105 := bstep (se 2 (by rfl) ⟨4901289, by rfl⟩ : syracuseStep 13070105 = 9802579) B9802579
theorem B8713403 : Blo 2039435 8713403 := bstep (se 1 (by rfl) ⟨6535052, by rfl⟩ : syracuseStep 8713403 = 13070105) B13070105
theorem B5808935 : Blo 2039435 5808935 := bstep (se 1 (by rfl) ⟨4356701, by rfl⟩ : syracuseStep 5808935 = 8713403) B8713403
theorem B3872623 : Blo 2039435 3872623 := bstep (se 1 (by rfl) ⟨2904467, by rfl⟩ : syracuseStep 3872623 = 5808935) B5808935
theorem B5163497 : Blo 2039435 5163497 := bstep (se 2 (by rfl) ⟨1936311, by rfl⟩ : syracuseStep 5163497 = 3872623) B3872623
theorem B3442331 : Blo 2039435 3442331 := bstep (se 1 (by rfl) ⟨2581748, by rfl⟩ : syracuseStep 3442331 = 5163497) B5163497
theorem B2294887 : Blo 2039435 2294887 := bstep (se 1 (by rfl) ⟨1721165, by rfl⟩ : syracuseStep 2294887 = 3442331) B3442331
theorem B3059849 : Blo 2039435 3059849 := bstep (se 2 (by rfl) ⟨1147443, by rfl⟩ : syracuseStep 3059849 = 2294887) B2294887
theorem B2039899 : Blo 2039435 2039899 := bstep (se 1 (by rfl) ⟨1529924, by rfl⟩ : syracuseStep 2039899 = 3059849) B3059849
theorem B10327013 : Blo 2039435 10327013 := bbase (se 4 (by rfl) ⟨968157, by rfl⟩ : syracuseStep 10327013 = 1936315) (by norm_num)
theorem B6884675 : Blo 2039435 6884675 := bstep (se 1 (by rfl) ⟨5163506, by rfl⟩ : syracuseStep 6884675 = 10327013) B10327013
theorem B4589783 : Blo 2039435 4589783 := bstep (se 1 (by rfl) ⟨3442337, by rfl⟩ : syracuseStep 4589783 = 6884675) B6884675
theorem B3059855 : Blo 2039435 3059855 := bstep (se 1 (by rfl) ⟨2294891, by rfl⟩ : syracuseStep 3059855 = 4589783) B4589783
theorem B2039903 : Blo 2039435 2039903 := bstep (se 1 (by rfl) ⟨1529927, by rfl⟩ : syracuseStep 2039903 = 3059855) B3059855
theorem B3059861 : Blo 2039435 3059861 := bbase (se 6 (by rfl) ⟨71715, by rfl⟩ : syracuseStep 3059861 = 143431) (by norm_num)
theorem B2039907 : Blo 2039435 2039907 := bstep (se 1 (by rfl) ⟨1529930, by rfl⟩ : syracuseStep 2039907 = 3059861) B3059861
theorem B3675989 : Blo 2039435 3675989 := bbase (se 9 (by rfl) ⟨10769, by rfl⟩ : syracuseStep 3675989 = 21539) (by norm_num)
theorem B2450659 : Blo 2039435 2450659 := bstep (se 1 (by rfl) ⟨1837994, by rfl⟩ : syracuseStep 2450659 = 3675989) B3675989
theorem B3267545 : Blo 2039435 3267545 := bstep (se 2 (by rfl) ⟨1225329, by rfl⟩ : syracuseStep 3267545 = 2450659) B2450659
theorem B8713453 : Blo 2039435 8713453 := bstep (se 3 (by rfl) ⟨1633772, by rfl⟩ : syracuseStep 8713453 = 3267545) B3267545
theorem B11617937 : Blo 2039435 11617937 := bstep (se 2 (by rfl) ⟨4356726, by rfl⟩ : syracuseStep 11617937 = 8713453) B8713453
theorem B7745291 : Blo 2039435 7745291 := bstep (se 1 (by rfl) ⟨5808968, by rfl⟩ : syracuseStep 7745291 = 11617937) B11617937
theorem B5163527 : Blo 2039435 5163527 := bstep (se 1 (by rfl) ⟨3872645, by rfl⟩ : syracuseStep 5163527 = 7745291) B7745291
theorem B3442351 : Blo 2039435 3442351 := bstep (se 1 (by rfl) ⟨2581763, by rfl⟩ : syracuseStep 3442351 = 5163527) B5163527
theorem B4589801 : Blo 2039435 4589801 := bstep (se 2 (by rfl) ⟨1721175, by rfl⟩ : syracuseStep 4589801 = 3442351) B3442351
theorem B3059867 : Blo 2039435 3059867 := bstep (se 1 (by rfl) ⟨2294900, by rfl⟩ : syracuseStep 3059867 = 4589801) B4589801
theorem B2039911 : Blo 2039435 2039911 := bstep (se 1 (by rfl) ⟨1529933, by rfl⟩ : syracuseStep 2039911 = 3059867) B3059867
theorem B2294905 : Blo 2039435 2294905 := bbase (se 2 (by rfl) ⟨860589, by rfl⟩ : syracuseStep 2294905 = 1721179) (by norm_num)
theorem B3059873 : Blo 2039435 3059873 := bstep (se 2 (by rfl) ⟨1147452, by rfl⟩ : syracuseStep 3059873 = 2294905) B2294905
theorem B2039915 : Blo 2039435 2039915 := bstep (se 1 (by rfl) ⟨1529936, by rfl⟩ : syracuseStep 2039915 = 3059873) B3059873
theorem B29408021 : Blo 2039435 29408021 := bbase (se 6 (by rfl) ⟨689250, by rfl⟩ : syracuseStep 29408021 = 1378501) (by norm_num)
theorem B19605347 : Blo 2039435 19605347 := bstep (se 1 (by rfl) ⟨14704010, by rfl⟩ : syracuseStep 19605347 = 29408021) B29408021
theorem B13070231 : Blo 2039435 13070231 := bstep (se 1 (by rfl) ⟨9802673, by rfl⟩ : syracuseStep 13070231 = 19605347) B19605347
theorem B8713487 : Blo 2039435 8713487 := bstep (se 1 (by rfl) ⟨6535115, by rfl⟩ : syracuseStep 8713487 = 13070231) B13070231
theorem B5808991 : Blo 2039435 5808991 := bstep (se 1 (by rfl) ⟨4356743, by rfl⟩ : syracuseStep 5808991 = 8713487) B8713487
theorem B7745321 : Blo 2039435 7745321 := bstep (se 2 (by rfl) ⟨2904495, by rfl⟩ : syracuseStep 7745321 = 5808991) B5808991
theorem B5163547 : Blo 2039435 5163547 := bstep (se 1 (by rfl) ⟨3872660, by rfl⟩ : syracuseStep 5163547 = 7745321) B7745321
theorem B6884729 : Blo 2039435 6884729 := bstep (se 2 (by rfl) ⟨2581773, by rfl⟩ : syracuseStep 6884729 = 5163547) B5163547
theorem B4589819 : Blo 2039435 4589819 := bstep (se 1 (by rfl) ⟨3442364, by rfl⟩ : syracuseStep 4589819 = 6884729) B6884729
theorem B3059879 : Blo 2039435 3059879 := bstep (se 1 (by rfl) ⟨2294909, by rfl⟩ : syracuseStep 3059879 = 4589819) B4589819
theorem B2039919 : Blo 2039435 2039919 := bstep (se 1 (by rfl) ⟨1529939, by rfl⟩ : syracuseStep 2039919 = 3059879) B3059879
theorem B3059885 : Blo 2039435 3059885 := bbase (se 3 (by rfl) ⟨573728, by rfl⟩ : syracuseStep 3059885 = 1147457) (by norm_num)
theorem B2039923 : Blo 2039435 2039923 := bstep (se 1 (by rfl) ⟨1529942, by rfl⟩ : syracuseStep 2039923 = 3059885) B3059885
theorem B4589837 : Blo 2039435 4589837 := bbase (se 3 (by rfl) ⟨860594, by rfl⟩ : syracuseStep 4589837 = 1721189) (by norm_num)
theorem B3059891 : Blo 2039435 3059891 := bstep (se 1 (by rfl) ⟨2294918, by rfl⟩ : syracuseStep 3059891 = 4589837) B4589837
theorem B2039927 : Blo 2039435 2039927 := bstep (se 1 (by rfl) ⟨1529945, by rfl⟩ : syracuseStep 2039927 = 3059891) B3059891
theorem B2581789 : Blo 2039435 2581789 := bbase (se 3 (by rfl) ⟨484085, by rfl⟩ : syracuseStep 2581789 = 968171) (by norm_num)
theorem B3442385 : Blo 2039435 3442385 := bstep (se 2 (by rfl) ⟨1290894, by rfl⟩ : syracuseStep 3442385 = 2581789) B2581789
theorem B2294923 : Blo 2039435 2294923 := bstep (se 1 (by rfl) ⟨1721192, by rfl⟩ : syracuseStep 2294923 = 3442385) B3442385
theorem B3059897 : Blo 2039435 3059897 := bstep (se 2 (by rfl) ⟨1147461, by rfl⟩ : syracuseStep 3059897 = 2294923) B2294923
theorem B2039931 : Blo 2039435 2039931 := bstep (se 1 (by rfl) ⟨1529948, by rfl⟩ : syracuseStep 2039931 = 3059897) B3059897
theorem B3536965 : Blo 2039435 3536965 := bbase (se 4 (by rfl) ⟨331590, by rfl⟩ : syracuseStep 3536965 = 663181) (by norm_num)
theorem B18863813 : Blo 2039435 18863813 := bstep (se 4 (by rfl) ⟨1768482, by rfl⟩ : syracuseStep 18863813 = 3536965) B3536965
theorem B12575875 : Blo 2039435 12575875 := bstep (se 1 (by rfl) ⟨9431906, by rfl⟩ : syracuseStep 12575875 = 18863813) B18863813
theorem B16767833 : Blo 2039435 16767833 := bstep (se 2 (by rfl) ⟨6287937, by rfl⟩ : syracuseStep 16767833 = 12575875) B12575875
theorem B178856885 : Blo 2039435 178856885 := bstep (se 5 (by rfl) ⟨8383916, by rfl⟩ : syracuseStep 178856885 = 16767833) B16767833
theorem B119237923 : Blo 2039435 119237923 := bstep (se 1 (by rfl) ⟨89428442, by rfl⟩ : syracuseStep 119237923 = 178856885) B178856885
theorem B158983897 : Blo 2039435 158983897 := bstep (se 2 (by rfl) ⟨59618961, by rfl⟩ : syracuseStep 158983897 = 119237923) B119237923
theorem B211978529 : Blo 2039435 211978529 := bstep (se 2 (by rfl) ⟨79491948, by rfl⟩ : syracuseStep 211978529 = 158983897) B158983897
theorem B141319019 : Blo 2039435 141319019 := bstep (se 1 (by rfl) ⟨105989264, by rfl⟩ : syracuseStep 141319019 = 211978529) B211978529
theorem B94212679 : Blo 2039435 94212679 := bstep (se 1 (by rfl) ⟨70659509, by rfl⟩ : syracuseStep 94212679 = 141319019) B141319019
theorem B125616905 : Blo 2039435 125616905 := bstep (se 2 (by rfl) ⟨47106339, by rfl⟩ : syracuseStep 125616905 = 94212679) B94212679
theorem B83744603 : Blo 2039435 83744603 := bstep (se 1 (by rfl) ⟨62808452, by rfl⟩ : syracuseStep 83744603 = 125616905) B125616905
theorem B55829735 : Blo 2039435 55829735 := bstep (se 1 (by rfl) ⟨41872301, by rfl⟩ : syracuseStep 55829735 = 83744603) B83744603
theorem B37219823 : Blo 2039435 37219823 := bstep (se 1 (by rfl) ⟨27914867, by rfl⟩ : syracuseStep 37219823 = 55829735) B55829735
theorem B24813215 : Blo 2039435 24813215 := bstep (se 1 (by rfl) ⟨18609911, by rfl⟩ : syracuseStep 24813215 = 37219823) B37219823
theorem B16542143 : Blo 2039435 16542143 := bstep (se 1 (by rfl) ⟨12406607, by rfl⟩ : syracuseStep 16542143 = 24813215) B24813215
theorem B11028095 : Blo 2039435 11028095 := bstep (se 1 (by rfl) ⟨8271071, by rfl⟩ : syracuseStep 11028095 = 16542143) B16542143
theorem B7352063 : Blo 2039435 7352063 := bstep (se 1 (by rfl) ⟨5514047, by rfl⟩ : syracuseStep 7352063 = 11028095) B11028095
theorem B4901375 : Blo 2039435 4901375 := bstep (se 1 (by rfl) ⟨3676031, by rfl⟩ : syracuseStep 4901375 = 7352063) B7352063
theorem B3267583 : Blo 2039435 3267583 := bstep (se 1 (by rfl) ⟨2450687, by rfl⟩ : syracuseStep 3267583 = 4901375) B4901375
theorem B17427109 : Blo 2039435 17427109 := bstep (se 4 (by rfl) ⟨1633791, by rfl⟩ : syracuseStep 17427109 = 3267583) B3267583
theorem B23236145 : Blo 2039435 23236145 := bstep (se 2 (by rfl) ⟨8713554, by rfl⟩ : syracuseStep 23236145 = 17427109) B17427109
theorem B15490763 : Blo 2039435 15490763 := bstep (se 1 (by rfl) ⟨11618072, by rfl⟩ : syracuseStep 15490763 = 23236145) B23236145
theorem B10327175 : Blo 2039435 10327175 := bstep (se 1 (by rfl) ⟨7745381, by rfl⟩ : syracuseStep 10327175 = 15490763) B15490763
theorem B6884783 : Blo 2039435 6884783 := bstep (se 1 (by rfl) ⟨5163587, by rfl⟩ : syracuseStep 6884783 = 10327175) B10327175
theorem B4589855 : Blo 2039435 4589855 := bstep (se 1 (by rfl) ⟨3442391, by rfl⟩ : syracuseStep 4589855 = 6884783) B6884783
theorem B3059903 : Blo 2039435 3059903 := bstep (se 1 (by rfl) ⟨2294927, by rfl⟩ : syracuseStep 3059903 = 4589855) B4589855
theorem B2039935 : Blo 2039435 2039935 := bstep (se 1 (by rfl) ⟨1529951, by rfl⟩ : syracuseStep 2039935 = 3059903) B3059903
theorem B3059909 : Blo 2039435 3059909 := bbase (se 4 (by rfl) ⟨286866, by rfl⟩ : syracuseStep 3059909 = 573733) (by norm_num)
theorem B2039939 : Blo 2039435 2039939 := bstep (se 1 (by rfl) ⟨1529954, by rfl⟩ : syracuseStep 2039939 = 3059909) B3059909
theorem B3442405 : Blo 2039435 3442405 := bbase (se 4 (by rfl) ⟨322725, by rfl⟩ : syracuseStep 3442405 = 645451) (by norm_num)
theorem B4589873 : Blo 2039435 4589873 := bstep (se 2 (by rfl) ⟨1721202, by rfl⟩ : syracuseStep 4589873 = 3442405) B3442405
theorem B3059915 : Blo 2039435 3059915 := bstep (se 1 (by rfl) ⟨2294936, by rfl⟩ : syracuseStep 3059915 = 4589873) B4589873
theorem B2039943 : Blo 2039435 2039943 := bstep (se 1 (by rfl) ⟨1529957, by rfl⟩ : syracuseStep 2039943 = 3059915) B3059915
theorem B2294941 : Blo 2039435 2294941 := bbase (se 3 (by rfl) ⟨430301, by rfl⟩ : syracuseStep 2294941 = 860603) (by norm_num)
theorem B3059921 : Blo 2039435 3059921 := bstep (se 2 (by rfl) ⟨1147470, by rfl⟩ : syracuseStep 3059921 = 2294941) B2294941
theorem B2039947 : Blo 2039435 2039947 := bstep (se 1 (by rfl) ⟨1529960, by rfl⟩ : syracuseStep 2039947 = 3059921) B3059921
theorem B6884837 : Blo 2039435 6884837 := bbase (se 4 (by rfl) ⟨645453, by rfl⟩ : syracuseStep 6884837 = 1290907) (by norm_num)
theorem B4589891 : Blo 2039435 4589891 := bstep (se 1 (by rfl) ⟨3442418, by rfl⟩ : syracuseStep 4589891 = 6884837) B6884837
theorem B3059927 : Blo 2039435 3059927 := bstep (se 1 (by rfl) ⟨2294945, by rfl⟩ : syracuseStep 3059927 = 4589891) B4589891
theorem B2039951 : Blo 2039435 2039951 := bstep (se 1 (by rfl) ⟨1529963, by rfl⟩ : syracuseStep 2039951 = 3059927) B3059927
theorem B3059933 : Blo 2039435 3059933 := bbase (se 3 (by rfl) ⟨573737, by rfl⟩ : syracuseStep 3059933 = 1147475) (by norm_num)
theorem B2039955 : Blo 2039435 2039955 := bstep (se 1 (by rfl) ⟨1529966, by rfl⟩ : syracuseStep 2039955 = 3059933) B3059933
theorem B4589909 : Blo 2039435 4589909 := bbase (se 10 (by rfl) ⟨6723, by rfl⟩ : syracuseStep 4589909 = 13447) (by norm_num)
theorem B3059939 : Blo 2039435 3059939 := bstep (se 1 (by rfl) ⟨2294954, by rfl⟩ : syracuseStep 3059939 = 4589909) B4589909
theorem B2039959 : Blo 2039435 2039959 := bstep (se 1 (by rfl) ⟨1529969, by rfl⟩ : syracuseStep 2039959 = 3059939) B3059939
theorem B3267629 : Blo 2039435 3267629 := bbase (se 3 (by rfl) ⟨612680, by rfl⟩ : syracuseStep 3267629 = 1225361) (by norm_num)
theorem B2178419 : Blo 2039435 2178419 := bstep (se 1 (by rfl) ⟨1633814, by rfl⟩ : syracuseStep 2178419 = 3267629) B3267629
theorem B5809117 : Blo 2039435 5809117 := bstep (se 3 (by rfl) ⟨1089209, by rfl⟩ : syracuseStep 5809117 = 2178419) B2178419
theorem B7745489 : Blo 2039435 7745489 := bstep (se 2 (by rfl) ⟨2904558, by rfl⟩ : syracuseStep 7745489 = 5809117) B5809117
theorem B5163659 : Blo 2039435 5163659 := bstep (se 1 (by rfl) ⟨3872744, by rfl⟩ : syracuseStep 5163659 = 7745489) B7745489
theorem B3442439 : Blo 2039435 3442439 := bstep (se 1 (by rfl) ⟨2581829, by rfl⟩ : syracuseStep 3442439 = 5163659) B5163659
theorem B2294959 : Blo 2039435 2294959 := bstep (se 1 (by rfl) ⟨1721219, by rfl⟩ : syracuseStep 2294959 = 3442439) B3442439
theorem B3059945 : Blo 2039435 3059945 := bstep (se 2 (by rfl) ⟨1147479, by rfl⟩ : syracuseStep 3059945 = 2294959) B2294959
theorem B2039963 : Blo 2039435 2039963 := bstep (se 1 (by rfl) ⟨1529972, by rfl⟩ : syracuseStep 2039963 = 3059945) B3059945
theorem B22056533 : Blo 2039435 22056533 := bbase (se 8 (by rfl) ⟨129237, by rfl⟩ : syracuseStep 22056533 = 258475) (by norm_num)
theorem B14704355 : Blo 2039435 14704355 := bstep (se 1 (by rfl) ⟨11028266, by rfl⟩ : syracuseStep 14704355 = 22056533) B22056533
theorem B39211613 : Blo 2039435 39211613 := bstep (se 3 (by rfl) ⟨7352177, by rfl⟩ : syracuseStep 39211613 = 14704355) B14704355
theorem B26141075 : Blo 2039435 26141075 := bstep (se 1 (by rfl) ⟨19605806, by rfl⟩ : syracuseStep 26141075 = 39211613) B39211613
theorem B17427383 : Blo 2039435 17427383 := bstep (se 1 (by rfl) ⟨13070537, by rfl⟩ : syracuseStep 17427383 = 26141075) B26141075
theorem B11618255 : Blo 2039435 11618255 := bstep (se 1 (by rfl) ⟨8713691, by rfl⟩ : syracuseStep 11618255 = 17427383) B17427383
theorem B7745503 : Blo 2039435 7745503 := bstep (se 1 (by rfl) ⟨5809127, by rfl⟩ : syracuseStep 7745503 = 11618255) B11618255
theorem B10327337 : Blo 2039435 10327337 := bstep (se 2 (by rfl) ⟨3872751, by rfl⟩ : syracuseStep 10327337 = 7745503) B7745503
theorem B6884891 : Blo 2039435 6884891 := bstep (se 1 (by rfl) ⟨5163668, by rfl⟩ : syracuseStep 6884891 = 10327337) B10327337
theorem B4589927 : Blo 2039435 4589927 := bstep (se 1 (by rfl) ⟨3442445, by rfl⟩ : syracuseStep 4589927 = 6884891) B6884891
theorem B3059951 : Blo 2039435 3059951 := bstep (se 1 (by rfl) ⟨2294963, by rfl⟩ : syracuseStep 3059951 = 4589927) B4589927
theorem B2039967 : Blo 2039435 2039967 := bstep (se 1 (by rfl) ⟨1529975, by rfl⟩ : syracuseStep 2039967 = 3059951) B3059951
theorem B3059957 : Blo 2039435 3059957 := bbase (se 5 (by rfl) ⟨143435, by rfl⟩ : syracuseStep 3059957 = 286871) (by norm_num)
theorem B2039971 : Blo 2039435 2039971 := bstep (se 1 (by rfl) ⟨1529978, by rfl⟩ : syracuseStep 2039971 = 3059957) B3059957
theorem B15702421 : Blo 2039435 15702421 := bbase (se 6 (by rfl) ⟨368025, by rfl⟩ : syracuseStep 15702421 = 736051) (by norm_num)
theorem B20936561 : Blo 2039435 20936561 := bstep (se 2 (by rfl) ⟨7851210, by rfl⟩ : syracuseStep 20936561 = 15702421) B15702421
theorem B223323317 : Blo 2039435 223323317 := bstep (se 5 (by rfl) ⟨10468280, by rfl⟩ : syracuseStep 223323317 = 20936561) B20936561
theorem B148882211 : Blo 2039435 148882211 := bstep (se 1 (by rfl) ⟨111661658, by rfl⟩ : syracuseStep 148882211 = 223323317) B223323317
theorem B99254807 : Blo 2039435 99254807 := bstep (se 1 (by rfl) ⟨74441105, by rfl⟩ : syracuseStep 99254807 = 148882211) B148882211
theorem B66169871 : Blo 2039435 66169871 := bstep (se 1 (by rfl) ⟨49627403, by rfl⟩ : syracuseStep 66169871 = 99254807) B99254807
theorem B44113247 : Blo 2039435 44113247 := bstep (se 1 (by rfl) ⟨33084935, by rfl⟩ : syracuseStep 44113247 = 66169871) B66169871
theorem B29408831 : Blo 2039435 29408831 := bstep (se 1 (by rfl) ⟨22056623, by rfl⟩ : syracuseStep 29408831 = 44113247) B44113247
theorem B19605887 : Blo 2039435 19605887 := bstep (se 1 (by rfl) ⟨14704415, by rfl⟩ : syracuseStep 19605887 = 29408831) B29408831
theorem B13070591 : Blo 2039435 13070591 := bstep (se 1 (by rfl) ⟨9802943, by rfl⟩ : syracuseStep 13070591 = 19605887) B19605887
theorem B8713727 : Blo 2039435 8713727 := bstep (se 1 (by rfl) ⟨6535295, by rfl⟩ : syracuseStep 8713727 = 13070591) B13070591
theorem B5809151 : Blo 2039435 5809151 := bstep (se 1 (by rfl) ⟨4356863, by rfl⟩ : syracuseStep 5809151 = 8713727) B8713727
theorem B3872767 : Blo 2039435 3872767 := bstep (se 1 (by rfl) ⟨2904575, by rfl⟩ : syracuseStep 3872767 = 5809151) B5809151
theorem B5163689 : Blo 2039435 5163689 := bstep (se 2 (by rfl) ⟨1936383, by rfl⟩ : syracuseStep 5163689 = 3872767) B3872767
theorem B3442459 : Blo 2039435 3442459 := bstep (se 1 (by rfl) ⟨2581844, by rfl⟩ : syracuseStep 3442459 = 5163689) B5163689
theorem B4589945 : Blo 2039435 4589945 := bstep (se 2 (by rfl) ⟨1721229, by rfl⟩ : syracuseStep 4589945 = 3442459) B3442459
theorem B3059963 : Blo 2039435 3059963 := bstep (se 1 (by rfl) ⟨2294972, by rfl⟩ : syracuseStep 3059963 = 4589945) B4589945
theorem B2039975 : Blo 2039435 2039975 := bstep (se 1 (by rfl) ⟨1529981, by rfl⟩ : syracuseStep 2039975 = 3059963) B3059963
theorem B2294977 : Blo 2039435 2294977 := bbase (se 2 (by rfl) ⟨860616, by rfl⟩ : syracuseStep 2294977 = 1721233) (by norm_num)
theorem B3059969 : Blo 2039435 3059969 := bstep (se 2 (by rfl) ⟨1147488, by rfl⟩ : syracuseStep 3059969 = 2294977) B2294977
theorem B2039979 : Blo 2039435 2039979 := bstep (se 1 (by rfl) ⟨1529984, by rfl⟩ : syracuseStep 2039979 = 3059969) B3059969
theorem B5163709 : Blo 2039435 5163709 := bbase (se 3 (by rfl) ⟨968195, by rfl⟩ : syracuseStep 5163709 = 1936391) (by norm_num)
theorem B6884945 : Blo 2039435 6884945 := bstep (se 2 (by rfl) ⟨2581854, by rfl⟩ : syracuseStep 6884945 = 5163709) B5163709
theorem B4589963 : Blo 2039435 4589963 := bstep (se 1 (by rfl) ⟨3442472, by rfl⟩ : syracuseStep 4589963 = 6884945) B6884945
theorem B3059975 : Blo 2039435 3059975 := bstep (se 1 (by rfl) ⟨2294981, by rfl⟩ : syracuseStep 3059975 = 4589963) B4589963
theorem B2039983 : Blo 2039435 2039983 := bstep (se 1 (by rfl) ⟨1529987, by rfl⟩ : syracuseStep 2039983 = 3059975) B3059975
theorem B3059981 : Blo 2039435 3059981 := bbase (se 3 (by rfl) ⟨573746, by rfl⟩ : syracuseStep 3059981 = 1147493) (by norm_num)
theorem B2039987 : Blo 2039435 2039987 := bstep (se 1 (by rfl) ⟨1529990, by rfl⟩ : syracuseStep 2039987 = 3059981) B3059981
theorem B4589981 : Blo 2039435 4589981 := bbase (se 3 (by rfl) ⟨860621, by rfl⟩ : syracuseStep 4589981 = 1721243) (by norm_num)
theorem B3059987 : Blo 2039435 3059987 := bstep (se 1 (by rfl) ⟨2294990, by rfl⟩ : syracuseStep 3059987 = 4589981) B4589981
theorem B2039991 : Blo 2039435 2039991 := bstep (se 1 (by rfl) ⟨1529993, by rfl⟩ : syracuseStep 2039991 = 3059987) B3059987
theorem B3442493 : Blo 2039435 3442493 := bbase (se 3 (by rfl) ⟨645467, by rfl⟩ : syracuseStep 3442493 = 1290935) (by norm_num)
theorem B2294995 : Blo 2039435 2294995 := bstep (se 1 (by rfl) ⟨1721246, by rfl⟩ : syracuseStep 2294995 = 3442493) B3442493
theorem B3059993 : Blo 2039435 3059993 := bstep (se 2 (by rfl) ⟨1147497, by rfl⟩ : syracuseStep 3059993 = 2294995) B2294995
theorem B2039995 : Blo 2039435 2039995 := bstep (se 1 (by rfl) ⟨1529996, by rfl⟩ : syracuseStep 2039995 = 3059993) B3059993
theorem B2178457 : Blo 2039435 2178457 := bbase (se 2 (by rfl) ⟨816921, by rfl⟩ : syracuseStep 2178457 = 1633843) (by norm_num)
theorem B11618437 : Blo 2039435 11618437 := bstep (se 4 (by rfl) ⟨1089228, by rfl⟩ : syracuseStep 11618437 = 2178457) B2178457
theorem B15491249 : Blo 2039435 15491249 := bstep (se 2 (by rfl) ⟨5809218, by rfl⟩ : syracuseStep 15491249 = 11618437) B11618437
theorem B10327499 : Blo 2039435 10327499 := bstep (se 1 (by rfl) ⟨7745624, by rfl⟩ : syracuseStep 10327499 = 15491249) B15491249
theorem B6884999 : Blo 2039435 6884999 := bstep (se 1 (by rfl) ⟨5163749, by rfl⟩ : syracuseStep 6884999 = 10327499) B10327499
theorem B4589999 : Blo 2039435 4589999 := bstep (se 1 (by rfl) ⟨3442499, by rfl⟩ : syracuseStep 4589999 = 6884999) B6884999
theorem B3059999 : Blo 2039435 3059999 := bstep (se 1 (by rfl) ⟨2294999, by rfl⟩ : syracuseStep 3059999 = 4589999) B4589999
theorem B2039999 : Blo 2039435 2039999 := bstep (se 1 (by rfl) ⟨1529999, by rfl⟩ : syracuseStep 2039999 = 3059999) B3059999
theorem B3060005 : Blo 2039435 3060005 := bbase (se 4 (by rfl) ⟨286875, by rfl⟩ : syracuseStep 3060005 = 573751) (by norm_num)
theorem B2040003 : Blo 2039435 2040003 := bstep (se 1 (by rfl) ⟨1530002, by rfl⟩ : syracuseStep 2040003 = 3060005) B3060005
theorem B2581885 : Blo 2039435 2581885 := bbase (se 3 (by rfl) ⟨484103, by rfl⟩ : syracuseStep 2581885 = 968207) (by norm_num)
theorem B3442513 : Blo 2039435 3442513 := bstep (se 2 (by rfl) ⟨1290942, by rfl⟩ : syracuseStep 3442513 = 2581885) B2581885
theorem B4590017 : Blo 2039435 4590017 := bstep (se 2 (by rfl) ⟨1721256, by rfl⟩ : syracuseStep 4590017 = 3442513) B3442513
theorem B3060011 : Blo 2039435 3060011 := bstep (se 1 (by rfl) ⟨2295008, by rfl⟩ : syracuseStep 3060011 = 4590017) B4590017
theorem B2040007 : Blo 2039435 2040007 := bstep (se 1 (by rfl) ⟨1530005, by rfl⟩ : syracuseStep 2040007 = 3060011) B3060011
theorem B2295013 : Blo 2039435 2295013 := bbase (se 4 (by rfl) ⟨215157, by rfl⟩ : syracuseStep 2295013 = 430315) (by norm_num)
theorem B3060017 : Blo 2039435 3060017 := bstep (se 2 (by rfl) ⟨1147506, by rfl⟩ : syracuseStep 3060017 = 2295013) B2295013
theorem B2040011 : Blo 2039435 2040011 := bstep (se 1 (by rfl) ⟨1530008, by rfl⟩ : syracuseStep 2040011 = 3060017) B3060017
theorem B4356949 : Blo 2039435 4356949 := bbase (se 9 (by rfl) ⟨12764, by rfl⟩ : syracuseStep 4356949 = 25529) (by norm_num)
theorem B5809265 : Blo 2039435 5809265 := bstep (se 2 (by rfl) ⟨2178474, by rfl⟩ : syracuseStep 5809265 = 4356949) B4356949
theorem B3872843 : Blo 2039435 3872843 := bstep (se 1 (by rfl) ⟨2904632, by rfl⟩ : syracuseStep 3872843 = 5809265) B5809265
theorem B2581895 : Blo 2039435 2581895 := bstep (se 1 (by rfl) ⟨1936421, by rfl⟩ : syracuseStep 2581895 = 3872843) B3872843
theorem B6885053 : Blo 2039435 6885053 := bstep (se 3 (by rfl) ⟨1290947, by rfl⟩ : syracuseStep 6885053 = 2581895) B2581895
theorem B4590035 : Blo 2039435 4590035 := bstep (se 1 (by rfl) ⟨3442526, by rfl⟩ : syracuseStep 4590035 = 6885053) B6885053
theorem B3060023 : Blo 2039435 3060023 := bstep (se 1 (by rfl) ⟨2295017, by rfl⟩ : syracuseStep 3060023 = 4590035) B4590035
theorem B2040015 : Blo 2039435 2040015 := bstep (se 1 (by rfl) ⟨1530011, by rfl⟩ : syracuseStep 2040015 = 3060023) B3060023
theorem B3060029 : Blo 2039435 3060029 := bbase (se 3 (by rfl) ⟨573755, by rfl⟩ : syracuseStep 3060029 = 1147511) (by norm_num)
theorem B2040019 : Blo 2039435 2040019 := bstep (se 1 (by rfl) ⟨1530014, by rfl⟩ : syracuseStep 2040019 = 3060029) B3060029
theorem B4590053 : Blo 2039435 4590053 := bbase (se 4 (by rfl) ⟨430317, by rfl⟩ : syracuseStep 4590053 = 860635) (by norm_num)
theorem B3060035 : Blo 2039435 3060035 := bstep (se 1 (by rfl) ⟨2295026, by rfl⟩ : syracuseStep 3060035 = 4590053) B4590053
theorem B2040023 : Blo 2039435 2040023 := bstep (se 1 (by rfl) ⟨1530017, by rfl⟩ : syracuseStep 2040023 = 3060035) B3060035
theorem B5163821 : Blo 2039435 5163821 := bbase (se 3 (by rfl) ⟨968216, by rfl⟩ : syracuseStep 5163821 = 1936433) (by norm_num)
theorem B3442547 : Blo 2039435 3442547 := bstep (se 1 (by rfl) ⟨2581910, by rfl⟩ : syracuseStep 3442547 = 5163821) B5163821
theorem B2295031 : Blo 2039435 2295031 := bstep (se 1 (by rfl) ⟨1721273, by rfl⟩ : syracuseStep 2295031 = 3442547) B3442547
theorem B3060041 : Blo 2039435 3060041 := bstep (se 2 (by rfl) ⟨1147515, by rfl⟩ : syracuseStep 3060041 = 2295031) B2295031
theorem B2040027 : Blo 2039435 2040027 := bstep (se 1 (by rfl) ⟨1530020, by rfl⟩ : syracuseStep 2040027 = 3060041) B3060041
theorem B3676205 : Blo 2039435 3676205 := bbase (se 3 (by rfl) ⟨689288, by rfl⟩ : syracuseStep 3676205 = 1378577) (by norm_num)
theorem B9803213 : Blo 2039435 9803213 := bstep (se 3 (by rfl) ⟨1838102, by rfl⟩ : syracuseStep 9803213 = 3676205) B3676205
theorem B6535475 : Blo 2039435 6535475 := bstep (se 1 (by rfl) ⟨4901606, by rfl⟩ : syracuseStep 6535475 = 9803213) B9803213
theorem B4356983 : Blo 2039435 4356983 := bstep (se 1 (by rfl) ⟨3267737, by rfl⟩ : syracuseStep 4356983 = 6535475) B6535475
theorem B2904655 : Blo 2039435 2904655 := bstep (se 1 (by rfl) ⟨2178491, by rfl⟩ : syracuseStep 2904655 = 4356983) B4356983
theorem B3872873 : Blo 2039435 3872873 := bstep (se 2 (by rfl) ⟨1452327, by rfl⟩ : syracuseStep 3872873 = 2904655) B2904655
theorem B10327661 : Blo 2039435 10327661 := bstep (se 3 (by rfl) ⟨1936436, by rfl⟩ : syracuseStep 10327661 = 3872873) B3872873
theorem B6885107 : Blo 2039435 6885107 := bstep (se 1 (by rfl) ⟨5163830, by rfl⟩ : syracuseStep 6885107 = 10327661) B10327661
theorem B4590071 : Blo 2039435 4590071 := bstep (se 1 (by rfl) ⟨3442553, by rfl⟩ : syracuseStep 4590071 = 6885107) B6885107
theorem B3060047 : Blo 2039435 3060047 := bstep (se 1 (by rfl) ⟨2295035, by rfl⟩ : syracuseStep 3060047 = 4590071) B4590071
theorem B2040031 : Blo 2039435 2040031 := bstep (se 1 (by rfl) ⟨1530023, by rfl⟩ : syracuseStep 2040031 = 3060047) B3060047
theorem B3060053 : Blo 2039435 3060053 := bbase (se 10 (by rfl) ⟨4482, by rfl⟩ : syracuseStep 3060053 = 8965) (by norm_num)
theorem B2040035 : Blo 2039435 2040035 := bstep (se 1 (by rfl) ⟨1530026, by rfl⟩ : syracuseStep 2040035 = 3060053) B3060053
theorem B5809333 : Blo 2039435 5809333 := bbase (se 5 (by rfl) ⟨272312, by rfl⟩ : syracuseStep 5809333 = 544625) (by norm_num)
theorem B7745777 : Blo 2039435 7745777 := bstep (se 2 (by rfl) ⟨2904666, by rfl⟩ : syracuseStep 7745777 = 5809333) B5809333
theorem B5163851 : Blo 2039435 5163851 := bstep (se 1 (by rfl) ⟨3872888, by rfl⟩ : syracuseStep 5163851 = 7745777) B7745777
theorem B3442567 : Blo 2039435 3442567 := bstep (se 1 (by rfl) ⟨2581925, by rfl⟩ : syracuseStep 3442567 = 5163851) B5163851
theorem B4590089 : Blo 2039435 4590089 := bstep (se 2 (by rfl) ⟨1721283, by rfl⟩ : syracuseStep 4590089 = 3442567) B3442567
theorem B3060059 : Blo 2039435 3060059 := bstep (se 1 (by rfl) ⟨2295044, by rfl⟩ : syracuseStep 3060059 = 4590089) B4590089
theorem B2040039 : Blo 2039435 2040039 := bstep (se 1 (by rfl) ⟨1530029, by rfl⟩ : syracuseStep 2040039 = 3060059) B3060059
theorem B2295049 : Blo 2039435 2295049 := bbase (se 2 (by rfl) ⟨860643, by rfl⟩ : syracuseStep 2295049 = 1721287) (by norm_num)
theorem B3060065 : Blo 2039435 3060065 := bstep (se 2 (by rfl) ⟨1147524, by rfl⟩ : syracuseStep 3060065 = 2295049) B2295049
theorem B2040043 : Blo 2039435 2040043 := bstep (se 1 (by rfl) ⟨1530032, by rfl⟩ : syracuseStep 2040043 = 3060065) B3060065
theorem B26142101 : Blo 2039435 26142101 := bbase (se 6 (by rfl) ⟨612705, by rfl⟩ : syracuseStep 26142101 = 1225411) (by norm_num)
theorem B17428067 : Blo 2039435 17428067 := bstep (se 1 (by rfl) ⟨13071050, by rfl⟩ : syracuseStep 17428067 = 26142101) B26142101
theorem B11618711 : Blo 2039435 11618711 := bstep (se 1 (by rfl) ⟨8714033, by rfl⟩ : syracuseStep 11618711 = 17428067) B17428067
theorem B7745807 : Blo 2039435 7745807 := bstep (se 1 (by rfl) ⟨5809355, by rfl⟩ : syracuseStep 7745807 = 11618711) B11618711
theorem B5163871 : Blo 2039435 5163871 := bstep (se 1 (by rfl) ⟨3872903, by rfl⟩ : syracuseStep 5163871 = 7745807) B7745807
theorem B6885161 : Blo 2039435 6885161 := bstep (se 2 (by rfl) ⟨2581935, by rfl⟩ : syracuseStep 6885161 = 5163871) B5163871
theorem B4590107 : Blo 2039435 4590107 := bstep (se 1 (by rfl) ⟨3442580, by rfl⟩ : syracuseStep 4590107 = 6885161) B6885161
theorem B3060071 : Blo 2039435 3060071 := bstep (se 1 (by rfl) ⟨2295053, by rfl⟩ : syracuseStep 3060071 = 4590107) B4590107
theorem B2040047 : Blo 2039435 2040047 := bstep (se 1 (by rfl) ⟨1530035, by rfl⟩ : syracuseStep 2040047 = 3060071) B3060071
theorem B3060077 : Blo 2039435 3060077 := bbase (se 3 (by rfl) ⟨573764, by rfl⟩ : syracuseStep 3060077 = 1147529) (by norm_num)
theorem B2040051 : Blo 2039435 2040051 := bstep (se 1 (by rfl) ⟨1530038, by rfl⟩ : syracuseStep 2040051 = 3060077) B3060077
theorem B4590125 : Blo 2039435 4590125 := bbase (se 3 (by rfl) ⟨860648, by rfl⟩ : syracuseStep 4590125 = 1721297) (by norm_num)
theorem B3060083 : Blo 2039435 3060083 := bstep (se 1 (by rfl) ⟨2295062, by rfl⟩ : syracuseStep 3060083 = 4590125) B4590125
theorem B2040055 : Blo 2039435 2040055 := bstep (se 1 (by rfl) ⟨1530041, by rfl⟩ : syracuseStep 2040055 = 3060083) B3060083
theorem B3726413 : Blo 2039435 3726413 := bbase (se 3 (by rfl) ⟨698702, by rfl⟩ : syracuseStep 3726413 = 1397405) (by norm_num)
theorem B2484275 : Blo 2039435 2484275 := bstep (se 1 (by rfl) ⟨1863206, by rfl⟩ : syracuseStep 2484275 = 3726413) B3726413
theorem B26498933 : Blo 2039435 26498933 := bstep (se 5 (by rfl) ⟨1242137, by rfl⟩ : syracuseStep 26498933 = 2484275) B2484275
theorem B17665955 : Blo 2039435 17665955 := bstep (se 1 (by rfl) ⟨13249466, by rfl⟩ : syracuseStep 17665955 = 26498933) B26498933
theorem B11777303 : Blo 2039435 11777303 := bstep (se 1 (by rfl) ⟨8832977, by rfl⟩ : syracuseStep 11777303 = 17665955) B17665955
theorem B7851535 : Blo 2039435 7851535 := bstep (se 1 (by rfl) ⟨5888651, by rfl⟩ : syracuseStep 7851535 = 11777303) B11777303
theorem B167499413 : Blo 2039435 167499413 := bstep (se 6 (by rfl) ⟨3925767, by rfl⟩ : syracuseStep 167499413 = 7851535) B7851535
theorem B111666275 : Blo 2039435 111666275 := bstep (se 1 (by rfl) ⟨83749706, by rfl⟩ : syracuseStep 111666275 = 167499413) B167499413
theorem B74444183 : Blo 2039435 74444183 := bstep (se 1 (by rfl) ⟨55833137, by rfl⟩ : syracuseStep 74444183 = 111666275) B111666275
theorem B49629455 : Blo 2039435 49629455 := bstep (se 1 (by rfl) ⟨37222091, by rfl⟩ : syracuseStep 49629455 = 74444183) B74444183
theorem B33086303 : Blo 2039435 33086303 := bstep (se 1 (by rfl) ⟨24814727, by rfl⟩ : syracuseStep 33086303 = 49629455) B49629455
theorem B22057535 : Blo 2039435 22057535 := bstep (se 1 (by rfl) ⟨16543151, by rfl⟩ : syracuseStep 22057535 = 33086303) B33086303
theorem B14705023 : Blo 2039435 14705023 := bstep (se 1 (by rfl) ⟨11028767, by rfl⟩ : syracuseStep 14705023 = 22057535) B22057535
theorem B19606697 : Blo 2039435 19606697 := bstep (se 2 (by rfl) ⟨7352511, by rfl⟩ : syracuseStep 19606697 = 14705023) B14705023
theorem B13071131 : Blo 2039435 13071131 := bstep (se 1 (by rfl) ⟨9803348, by rfl⟩ : syracuseStep 13071131 = 19606697) B19606697
theorem B8714087 : Blo 2039435 8714087 := bstep (se 1 (by rfl) ⟨6535565, by rfl⟩ : syracuseStep 8714087 = 13071131) B13071131
theorem B5809391 : Blo 2039435 5809391 := bstep (se 1 (by rfl) ⟨4357043, by rfl⟩ : syracuseStep 5809391 = 8714087) B8714087
theorem B3872927 : Blo 2039435 3872927 := bstep (se 1 (by rfl) ⟨2904695, by rfl⟩ : syracuseStep 3872927 = 5809391) B5809391
theorem B2581951 : Blo 2039435 2581951 := bstep (se 1 (by rfl) ⟨1936463, by rfl⟩ : syracuseStep 2581951 = 3872927) B3872927
theorem B3442601 : Blo 2039435 3442601 := bstep (se 2 (by rfl) ⟨1290975, by rfl⟩ : syracuseStep 3442601 = 2581951) B2581951
theorem B2295067 : Blo 2039435 2295067 := bstep (se 1 (by rfl) ⟨1721300, by rfl⟩ : syracuseStep 2295067 = 3442601) B3442601
theorem B3060089 : Blo 2039435 3060089 := bstep (se 2 (by rfl) ⟨1147533, by rfl⟩ : syracuseStep 3060089 = 2295067) B2295067
theorem B2040059 : Blo 2039435 2040059 := bstep (se 1 (by rfl) ⟨1530044, by rfl⟩ : syracuseStep 2040059 = 3060089) B3060089
theorem B34856405 : Blo 2039435 34856405 := bbase (se 7 (by rfl) ⟨408473, by rfl⟩ : syracuseStep 34856405 = 816947) (by norm_num)
theorem B23237603 : Blo 2039435 23237603 := bstep (se 1 (by rfl) ⟨17428202, by rfl⟩ : syracuseStep 23237603 = 34856405) B34856405
theorem B15491735 : Blo 2039435 15491735 := bstep (se 1 (by rfl) ⟨11618801, by rfl⟩ : syracuseStep 15491735 = 23237603) B23237603
theorem B10327823 : Blo 2039435 10327823 := bstep (se 1 (by rfl) ⟨7745867, by rfl⟩ : syracuseStep 10327823 = 15491735) B15491735
theorem B6885215 : Blo 2039435 6885215 := bstep (se 1 (by rfl) ⟨5163911, by rfl⟩ : syracuseStep 6885215 = 10327823) B10327823
theorem B4590143 : Blo 2039435 4590143 := bstep (se 1 (by rfl) ⟨3442607, by rfl⟩ : syracuseStep 4590143 = 6885215) B6885215
theorem B3060095 : Blo 2039435 3060095 := bstep (se 1 (by rfl) ⟨2295071, by rfl⟩ : syracuseStep 3060095 = 4590143) B4590143
theorem B2040063 : Blo 2039435 2040063 := bstep (se 1 (by rfl) ⟨1530047, by rfl⟩ : syracuseStep 2040063 = 3060095) B3060095
theorem B3060101 : Blo 2039435 3060101 := bbase (se 4 (by rfl) ⟨286884, by rfl⟩ : syracuseStep 3060101 = 573769) (by norm_num)
theorem B2040067 : Blo 2039435 2040067 := bstep (se 1 (by rfl) ⟨1530050, by rfl⟩ : syracuseStep 2040067 = 3060101) B3060101
theorem B3442621 : Blo 2039435 3442621 := bbase (se 3 (by rfl) ⟨645491, by rfl⟩ : syracuseStep 3442621 = 1290983) (by norm_num)
theorem B4590161 : Blo 2039435 4590161 := bstep (se 2 (by rfl) ⟨1721310, by rfl⟩ : syracuseStep 4590161 = 3442621) B3442621
theorem B3060107 : Blo 2039435 3060107 := bstep (se 1 (by rfl) ⟨2295080, by rfl⟩ : syracuseStep 3060107 = 4590161) B4590161
theorem B2040071 : Blo 2039435 2040071 := bstep (se 1 (by rfl) ⟨1530053, by rfl⟩ : syracuseStep 2040071 = 3060107) B3060107
theorem B2295085 : Blo 2039435 2295085 := bbase (se 3 (by rfl) ⟨430328, by rfl⟩ : syracuseStep 2295085 = 860657) (by norm_num)
theorem B3060113 : Blo 2039435 3060113 := bstep (se 2 (by rfl) ⟨1147542, by rfl⟩ : syracuseStep 3060113 = 2295085) B2295085
theorem B2040075 : Blo 2039435 2040075 := bstep (se 1 (by rfl) ⟨1530056, by rfl⟩ : syracuseStep 2040075 = 3060113) B3060113
theorem B6885269 : Blo 2039435 6885269 := bbase (se 6 (by rfl) ⟨161373, by rfl⟩ : syracuseStep 6885269 = 322747) (by norm_num)
theorem B4590179 : Blo 2039435 4590179 := bstep (se 1 (by rfl) ⟨3442634, by rfl⟩ : syracuseStep 4590179 = 6885269) B6885269
theorem B3060119 : Blo 2039435 3060119 := bstep (se 1 (by rfl) ⟨2295089, by rfl⟩ : syracuseStep 3060119 = 4590179) B4590179
theorem B2040079 : Blo 2039435 2040079 := bstep (se 1 (by rfl) ⟨1530059, by rfl⟩ : syracuseStep 2040079 = 3060119) B3060119
theorem B3060125 : Blo 2039435 3060125 := bbase (se 3 (by rfl) ⟨573773, by rfl⟩ : syracuseStep 3060125 = 1147547) (by norm_num)
theorem B2040083 : Blo 2039435 2040083 := bstep (se 1 (by rfl) ⟨1530062, by rfl⟩ : syracuseStep 2040083 = 3060125) B3060125
theorem B4590197 : Blo 2039435 4590197 := bbase (se 5 (by rfl) ⟨215165, by rfl⟩ : syracuseStep 4590197 = 430331) (by norm_num)
theorem B3060131 : Blo 2039435 3060131 := bstep (se 1 (by rfl) ⟨2295098, by rfl⟩ : syracuseStep 3060131 = 4590197) B4590197
theorem B2040087 : Blo 2039435 2040087 := bstep (se 1 (by rfl) ⟨1530065, by rfl⟩ : syracuseStep 2040087 = 3060131) B3060131
theorem B4135853 : Blo 2039435 4135853 := bbase (se 3 (by rfl) ⟨775472, by rfl⟩ : syracuseStep 4135853 = 1550945) (by norm_num)
theorem B2757235 : Blo 2039435 2757235 := bstep (se 1 (by rfl) ⟨2067926, by rfl⟩ : syracuseStep 2757235 = 4135853) B4135853
theorem B3676313 : Blo 2039435 3676313 := bstep (se 2 (by rfl) ⟨1378617, by rfl⟩ : syracuseStep 3676313 = 2757235) B2757235
theorem B9803501 : Blo 2039435 9803501 := bstep (se 3 (by rfl) ⟨1838156, by rfl⟩ : syracuseStep 9803501 = 3676313) B3676313
theorem B6535667 : Blo 2039435 6535667 := bstep (se 1 (by rfl) ⟨4901750, by rfl⟩ : syracuseStep 6535667 = 9803501) B9803501
theorem B17428445 : Blo 2039435 17428445 := bstep (se 3 (by rfl) ⟨3267833, by rfl⟩ : syracuseStep 17428445 = 6535667) B6535667
theorem B11618963 : Blo 2039435 11618963 := bstep (se 1 (by rfl) ⟨8714222, by rfl⟩ : syracuseStep 11618963 = 17428445) B17428445
theorem B7745975 : Blo 2039435 7745975 := bstep (se 1 (by rfl) ⟨5809481, by rfl⟩ : syracuseStep 7745975 = 11618963) B11618963
theorem B5163983 : Blo 2039435 5163983 := bstep (se 1 (by rfl) ⟨3872987, by rfl⟩ : syracuseStep 5163983 = 7745975) B7745975
theorem B3442655 : Blo 2039435 3442655 := bstep (se 1 (by rfl) ⟨2581991, by rfl⟩ : syracuseStep 3442655 = 5163983) B5163983
theorem B2295103 : Blo 2039435 2295103 := bstep (se 1 (by rfl) ⟨1721327, by rfl⟩ : syracuseStep 2295103 = 3442655) B3442655
theorem B3060137 : Blo 2039435 3060137 := bstep (se 2 (by rfl) ⟨1147551, by rfl⟩ : syracuseStep 3060137 = 2295103) B2295103
theorem B2040091 : Blo 2039435 2040091 := bstep (se 1 (by rfl) ⟨1530068, by rfl⟩ : syracuseStep 2040091 = 3060137) B3060137
theorem B7745989 : Blo 2039435 7745989 := bbase (se 4 (by rfl) ⟨726186, by rfl⟩ : syracuseStep 7745989 = 1452373) (by norm_num)
theorem B10327985 : Blo 2039435 10327985 := bstep (se 2 (by rfl) ⟨3872994, by rfl⟩ : syracuseStep 10327985 = 7745989) B7745989
theorem B6885323 : Blo 2039435 6885323 := bstep (se 1 (by rfl) ⟨5163992, by rfl⟩ : syracuseStep 6885323 = 10327985) B10327985
theorem B4590215 : Blo 2039435 4590215 := bstep (se 1 (by rfl) ⟨3442661, by rfl⟩ : syracuseStep 4590215 = 6885323) B6885323
theorem B3060143 : Blo 2039435 3060143 := bstep (se 1 (by rfl) ⟨2295107, by rfl⟩ : syracuseStep 3060143 = 4590215) B4590215
theorem B2040095 : Blo 2039435 2040095 := bstep (se 1 (by rfl) ⟨1530071, by rfl⟩ : syracuseStep 2040095 = 3060143) B3060143
theorem B3060149 : Blo 2039435 3060149 := bbase (se 5 (by rfl) ⟨143444, by rfl⟩ : syracuseStep 3060149 = 286889) (by norm_num)
theorem B2040099 : Blo 2039435 2040099 := bstep (se 1 (by rfl) ⟨1530074, by rfl⟩ : syracuseStep 2040099 = 3060149) B3060149
theorem B5164013 : Blo 2039435 5164013 := bbase (se 3 (by rfl) ⟨968252, by rfl⟩ : syracuseStep 5164013 = 1936505) (by norm_num)
theorem B3442675 : Blo 2039435 3442675 := bstep (se 1 (by rfl) ⟨2582006, by rfl⟩ : syracuseStep 3442675 = 5164013) B5164013
theorem B4590233 : Blo 2039435 4590233 := bstep (se 2 (by rfl) ⟨1721337, by rfl⟩ : syracuseStep 4590233 = 3442675) B3442675
theorem B3060155 : Blo 2039435 3060155 := bstep (se 1 (by rfl) ⟨2295116, by rfl⟩ : syracuseStep 3060155 = 4590233) B4590233
theorem B2040103 : Blo 2039435 2040103 := bstep (se 1 (by rfl) ⟨1530077, by rfl⟩ : syracuseStep 2040103 = 3060155) B3060155
theorem B2295121 : Blo 2039435 2295121 := bbase (se 2 (by rfl) ⟨860670, by rfl⟩ : syracuseStep 2295121 = 1721341) (by norm_num)
theorem B3060161 : Blo 2039435 3060161 := bstep (se 2 (by rfl) ⟨1147560, by rfl⟩ : syracuseStep 3060161 = 2295121) B2295121
theorem B2040107 : Blo 2039435 2040107 := bstep (se 1 (by rfl) ⟨1530080, by rfl⟩ : syracuseStep 2040107 = 3060161) B3060161
theorem B2178577 : Blo 2039435 2178577 := bbase (se 2 (by rfl) ⟨816966, by rfl⟩ : syracuseStep 2178577 = 1633933) (by norm_num)
theorem B2904769 : Blo 2039435 2904769 := bstep (se 2 (by rfl) ⟨1089288, by rfl⟩ : syracuseStep 2904769 = 2178577) B2178577
theorem B3873025 : Blo 2039435 3873025 := bstep (se 2 (by rfl) ⟨1452384, by rfl⟩ : syracuseStep 3873025 = 2904769) B2904769
theorem B5164033 : Blo 2039435 5164033 := bstep (se 2 (by rfl) ⟨1936512, by rfl⟩ : syracuseStep 5164033 = 3873025) B3873025
theorem B6885377 : Blo 2039435 6885377 := bstep (se 2 (by rfl) ⟨2582016, by rfl⟩ : syracuseStep 6885377 = 5164033) B5164033
theorem B4590251 : Blo 2039435 4590251 := bstep (se 1 (by rfl) ⟨3442688, by rfl⟩ : syracuseStep 4590251 = 6885377) B6885377
theorem B3060167 : Blo 2039435 3060167 := bstep (se 1 (by rfl) ⟨2295125, by rfl⟩ : syracuseStep 3060167 = 4590251) B4590251
theorem B2040111 : Blo 2039435 2040111 := bstep (se 1 (by rfl) ⟨1530083, by rfl⟩ : syracuseStep 2040111 = 3060167) B3060167
theorem B3060173 : Blo 2039435 3060173 := bbase (se 3 (by rfl) ⟨573782, by rfl⟩ : syracuseStep 3060173 = 1147565) (by norm_num)
theorem B2040115 : Blo 2039435 2040115 := bstep (se 1 (by rfl) ⟨1530086, by rfl⟩ : syracuseStep 2040115 = 3060173) B3060173
theorem B4590269 : Blo 2039435 4590269 := bbase (se 3 (by rfl) ⟨860675, by rfl⟩ : syracuseStep 4590269 = 1721351) (by norm_num)
theorem B3060179 : Blo 2039435 3060179 := bstep (se 1 (by rfl) ⟨2295134, by rfl⟩ : syracuseStep 3060179 = 4590269) B4590269
theorem B2040119 : Blo 2039435 2040119 := bstep (se 1 (by rfl) ⟨1530089, by rfl⟩ : syracuseStep 2040119 = 3060179) B3060179
theorem B3442709 : Blo 2039435 3442709 := bbase (se 6 (by rfl) ⟨80688, by rfl⟩ : syracuseStep 3442709 = 161377) (by norm_num)
theorem B2295139 : Blo 2039435 2295139 := bstep (se 1 (by rfl) ⟨1721354, by rfl⟩ : syracuseStep 2295139 = 3442709) B3442709
theorem B3060185 : Blo 2039435 3060185 := bstep (se 2 (by rfl) ⟨1147569, by rfl⟩ : syracuseStep 3060185 = 2295139) B2295139
theorem B2040123 : Blo 2039435 2040123 := bstep (se 1 (by rfl) ⟨1530092, by rfl⟩ : syracuseStep 2040123 = 3060185) B3060185
theorem B4135925 : Blo 2039435 4135925 := bbase (se 5 (by rfl) ⟨193871, by rfl⟩ : syracuseStep 4135925 = 387743) (by norm_num)
theorem B2757283 : Blo 2039435 2757283 := bstep (se 1 (by rfl) ⟨2067962, by rfl⟩ : syracuseStep 2757283 = 4135925) B4135925
theorem B14705509 : Blo 2039435 14705509 := bstep (se 4 (by rfl) ⟨1378641, by rfl⟩ : syracuseStep 14705509 = 2757283) B2757283
theorem B19607345 : Blo 2039435 19607345 := bstep (se 2 (by rfl) ⟨7352754, by rfl⟩ : syracuseStep 19607345 = 14705509) B14705509
theorem B13071563 : Blo 2039435 13071563 := bstep (se 1 (by rfl) ⟨9803672, by rfl⟩ : syracuseStep 13071563 = 19607345) B19607345
theorem B8714375 : Blo 2039435 8714375 := bstep (se 1 (by rfl) ⟨6535781, by rfl⟩ : syracuseStep 8714375 = 13071563) B13071563
theorem B5809583 : Blo 2039435 5809583 := bstep (se 1 (by rfl) ⟨4357187, by rfl⟩ : syracuseStep 5809583 = 8714375) B8714375
theorem B15492221 : Blo 2039435 15492221 := bstep (se 3 (by rfl) ⟨2904791, by rfl⟩ : syracuseStep 15492221 = 5809583) B5809583
theorem B10328147 : Blo 2039435 10328147 := bstep (se 1 (by rfl) ⟨7746110, by rfl⟩ : syracuseStep 10328147 = 15492221) B15492221
theorem B6885431 : Blo 2039435 6885431 := bstep (se 1 (by rfl) ⟨5164073, by rfl⟩ : syracuseStep 6885431 = 10328147) B10328147
theorem B4590287 : Blo 2039435 4590287 := bstep (se 1 (by rfl) ⟨3442715, by rfl⟩ : syracuseStep 4590287 = 6885431) B6885431
theorem B3060191 : Blo 2039435 3060191 := bstep (se 1 (by rfl) ⟨2295143, by rfl⟩ : syracuseStep 3060191 = 4590287) B4590287
theorem B2040127 : Blo 2039435 2040127 := bstep (se 1 (by rfl) ⟨1530095, by rfl⟩ : syracuseStep 2040127 = 3060191) B3060191
theorem B3060197 : Blo 2039435 3060197 := bbase (se 4 (by rfl) ⟨286893, by rfl⟩ : syracuseStep 3060197 = 573787) (by norm_num)
theorem B2040131 : Blo 2039435 2040131 := bstep (se 1 (by rfl) ⟨1530098, by rfl⟩ : syracuseStep 2040131 = 3060197) B3060197
theorem B3101957 : Blo 2039435 3101957 := bbase (se 4 (by rfl) ⟨290808, by rfl⟩ : syracuseStep 3101957 = 581617) (by norm_num)
theorem B2067971 : Blo 2039435 2067971 := bstep (se 1 (by rfl) ⟨1550978, by rfl⟩ : syracuseStep 2067971 = 3101957) B3101957
theorem B5514589 : Blo 2039435 5514589 := bstep (se 3 (by rfl) ⟨1033985, by rfl⟩ : syracuseStep 5514589 = 2067971) B2067971
theorem B7352785 : Blo 2039435 7352785 := bstep (se 2 (by rfl) ⟨2757294, by rfl⟩ : syracuseStep 7352785 = 5514589) B5514589
theorem B9803713 : Blo 2039435 9803713 := bstep (se 2 (by rfl) ⟨3676392, by rfl⟩ : syracuseStep 9803713 = 7352785) B7352785
theorem B13071617 : Blo 2039435 13071617 := bstep (se 2 (by rfl) ⟨4901856, by rfl⟩ : syracuseStep 13071617 = 9803713) B9803713
theorem B8714411 : Blo 2039435 8714411 := bstep (se 1 (by rfl) ⟨6535808, by rfl⟩ : syracuseStep 8714411 = 13071617) B13071617
theorem B5809607 : Blo 2039435 5809607 := bstep (se 1 (by rfl) ⟨4357205, by rfl⟩ : syracuseStep 5809607 = 8714411) B8714411
theorem B3873071 : Blo 2039435 3873071 := bstep (se 1 (by rfl) ⟨2904803, by rfl⟩ : syracuseStep 3873071 = 5809607) B5809607
theorem B2582047 : Blo 2039435 2582047 := bstep (se 1 (by rfl) ⟨1936535, by rfl⟩ : syracuseStep 2582047 = 3873071) B3873071
theorem B3442729 : Blo 2039435 3442729 := bstep (se 2 (by rfl) ⟨1291023, by rfl⟩ : syracuseStep 3442729 = 2582047) B2582047
theorem B4590305 : Blo 2039435 4590305 := bstep (se 2 (by rfl) ⟨1721364, by rfl⟩ : syracuseStep 4590305 = 3442729) B3442729
theorem B3060203 : Blo 2039435 3060203 := bstep (se 1 (by rfl) ⟨2295152, by rfl⟩ : syracuseStep 3060203 = 4590305) B4590305
theorem B2040135 : Blo 2039435 2040135 := bstep (se 1 (by rfl) ⟨1530101, by rfl⟩ : syracuseStep 2040135 = 3060203) B3060203
theorem B2295157 : Blo 2039435 2295157 := bbase (se 5 (by rfl) ⟨107585, by rfl⟩ : syracuseStep 2295157 = 215171) (by norm_num)
theorem B3060209 : Blo 2039435 3060209 := bstep (se 2 (by rfl) ⟨1147578, by rfl⟩ : syracuseStep 3060209 = 2295157) B2295157
theorem B2040139 : Blo 2039435 2040139 := bstep (se 1 (by rfl) ⟨1530104, by rfl⟩ : syracuseStep 2040139 = 3060209) B3060209
theorem B2582057 : Blo 2039435 2582057 := bbase (se 2 (by rfl) ⟨968271, by rfl⟩ : syracuseStep 2582057 = 1936543) (by norm_num)
theorem B6885485 : Blo 2039435 6885485 := bstep (se 3 (by rfl) ⟨1291028, by rfl⟩ : syracuseStep 6885485 = 2582057) B2582057
theorem B4590323 : Blo 2039435 4590323 := bstep (se 1 (by rfl) ⟨3442742, by rfl⟩ : syracuseStep 4590323 = 6885485) B6885485
theorem B3060215 : Blo 2039435 3060215 := bstep (se 1 (by rfl) ⟨2295161, by rfl⟩ : syracuseStep 3060215 = 4590323) B4590323
theorem B2040143 : Blo 2039435 2040143 := bstep (se 1 (by rfl) ⟨1530107, by rfl⟩ : syracuseStep 2040143 = 3060215) B3060215
theorem B3060221 : Blo 2039435 3060221 := bbase (se 3 (by rfl) ⟨573791, by rfl⟩ : syracuseStep 3060221 = 1147583) (by norm_num)
theorem B2040147 : Blo 2039435 2040147 := bstep (se 1 (by rfl) ⟨1530110, by rfl⟩ : syracuseStep 2040147 = 3060221) B3060221
theorem B4590341 : Blo 2039435 4590341 := bbase (se 4 (by rfl) ⟨430344, by rfl⟩ : syracuseStep 4590341 = 860689) (by norm_num)
theorem B3060227 : Blo 2039435 3060227 := bstep (se 1 (by rfl) ⟨2295170, by rfl⟩ : syracuseStep 3060227 = 4590341) B4590341
theorem B2040151 : Blo 2039435 2040151 := bstep (se 1 (by rfl) ⟨1530113, by rfl⟩ : syracuseStep 2040151 = 3060227) B3060227
theorem B3873109 : Blo 2039435 3873109 := bbase (se 10 (by rfl) ⟨5673, by rfl⟩ : syracuseStep 3873109 = 11347) (by norm_num)
theorem B5164145 : Blo 2039435 5164145 := bstep (se 2 (by rfl) ⟨1936554, by rfl⟩ : syracuseStep 5164145 = 3873109) B3873109
theorem B3442763 : Blo 2039435 3442763 := bstep (se 1 (by rfl) ⟨2582072, by rfl⟩ : syracuseStep 3442763 = 5164145) B5164145
theorem B2295175 : Blo 2039435 2295175 := bstep (se 1 (by rfl) ⟨1721381, by rfl⟩ : syracuseStep 2295175 = 3442763) B3442763
theorem B3060233 : Blo 2039435 3060233 := bstep (se 2 (by rfl) ⟨1147587, by rfl⟩ : syracuseStep 3060233 = 2295175) B2295175
theorem B2040155 : Blo 2039435 2040155 := bstep (se 1 (by rfl) ⟨1530116, by rfl⟩ : syracuseStep 2040155 = 3060233) B3060233
theorem B10328309 : Blo 2039435 10328309 := bbase (se 5 (by rfl) ⟨484139, by rfl⟩ : syracuseStep 10328309 = 968279) (by norm_num)
theorem B6885539 : Blo 2039435 6885539 := bstep (se 1 (by rfl) ⟨5164154, by rfl⟩ : syracuseStep 6885539 = 10328309) B10328309
theorem B4590359 : Blo 2039435 4590359 := bstep (se 1 (by rfl) ⟨3442769, by rfl⟩ : syracuseStep 4590359 = 6885539) B6885539
theorem B3060239 : Blo 2039435 3060239 := bstep (se 1 (by rfl) ⟨2295179, by rfl⟩ : syracuseStep 3060239 = 4590359) B4590359
theorem B2040159 : Blo 2039435 2040159 := bstep (se 1 (by rfl) ⟨1530119, by rfl⟩ : syracuseStep 2040159 = 3060239) B3060239
theorem B3060245 : Blo 2039435 3060245 := bbase (se 6 (by rfl) ⟨71724, by rfl⟩ : syracuseStep 3060245 = 143449) (by norm_num)
theorem B2040163 : Blo 2039435 2040163 := bstep (se 1 (by rfl) ⟨1530122, by rfl⟩ : syracuseStep 2040163 = 3060245) B3060245
theorem B4901933 : Blo 2039435 4901933 := bbase (se 3 (by rfl) ⟨919112, by rfl⟩ : syracuseStep 4901933 = 1838225) (by norm_num)
theorem B3267955 : Blo 2039435 3267955 := bstep (se 1 (by rfl) ⟨2450966, by rfl⟩ : syracuseStep 3267955 = 4901933) B4901933
theorem B17429093 : Blo 2039435 17429093 := bstep (se 4 (by rfl) ⟨1633977, by rfl⟩ : syracuseStep 17429093 = 3267955) B3267955
theorem B11619395 : Blo 2039435 11619395 := bstep (se 1 (by rfl) ⟨8714546, by rfl⟩ : syracuseStep 11619395 = 17429093) B17429093
theorem B7746263 : Blo 2039435 7746263 := bstep (se 1 (by rfl) ⟨5809697, by rfl⟩ : syracuseStep 7746263 = 11619395) B11619395
theorem B5164175 : Blo 2039435 5164175 := bstep (se 1 (by rfl) ⟨3873131, by rfl⟩ : syracuseStep 5164175 = 7746263) B7746263
theorem B3442783 : Blo 2039435 3442783 := bstep (se 1 (by rfl) ⟨2582087, by rfl⟩ : syracuseStep 3442783 = 5164175) B5164175
theorem B4590377 : Blo 2039435 4590377 := bstep (se 2 (by rfl) ⟨1721391, by rfl⟩ : syracuseStep 4590377 = 3442783) B3442783
theorem B3060251 : Blo 2039435 3060251 := bstep (se 1 (by rfl) ⟨2295188, by rfl⟩ : syracuseStep 3060251 = 4590377) B4590377
theorem B2040167 : Blo 2039435 2040167 := bstep (se 1 (by rfl) ⟨1530125, by rfl⟩ : syracuseStep 2040167 = 3060251) B3060251
theorem B2295193 : Blo 2039435 2295193 := bbase (se 2 (by rfl) ⟨860697, by rfl⟩ : syracuseStep 2295193 = 1721395) (by norm_num)
theorem B3060257 : Blo 2039435 3060257 := bstep (se 2 (by rfl) ⟨1147596, by rfl⟩ : syracuseStep 3060257 = 2295193) B2295193
theorem B2040171 : Blo 2039435 2040171 := bstep (se 1 (by rfl) ⟨1530128, by rfl⟩ : syracuseStep 2040171 = 3060257) B3060257
theorem B7746293 : Blo 2039435 7746293 := bbase (se 5 (by rfl) ⟨363107, by rfl⟩ : syracuseStep 7746293 = 726215) (by norm_num)
theorem B5164195 : Blo 2039435 5164195 := bstep (se 1 (by rfl) ⟨3873146, by rfl⟩ : syracuseStep 5164195 = 7746293) B7746293
theorem B6885593 : Blo 2039435 6885593 := bstep (se 2 (by rfl) ⟨2582097, by rfl⟩ : syracuseStep 6885593 = 5164195) B5164195
theorem B4590395 : Blo 2039435 4590395 := bstep (se 1 (by rfl) ⟨3442796, by rfl⟩ : syracuseStep 4590395 = 6885593) B6885593
theorem B3060263 : Blo 2039435 3060263 := bstep (se 1 (by rfl) ⟨2295197, by rfl⟩ : syracuseStep 3060263 = 4590395) B4590395
theorem B2040175 : Blo 2039435 2040175 := bstep (se 1 (by rfl) ⟨1530131, by rfl⟩ : syracuseStep 2040175 = 3060263) B3060263
theorem B3060269 : Blo 2039435 3060269 := bbase (se 3 (by rfl) ⟨573800, by rfl⟩ : syracuseStep 3060269 = 1147601) (by norm_num)
theorem B2040179 : Blo 2039435 2040179 := bstep (se 1 (by rfl) ⟨1530134, by rfl⟩ : syracuseStep 2040179 = 3060269) B3060269
theorem B4590413 : Blo 2039435 4590413 := bbase (se 3 (by rfl) ⟨860702, by rfl⟩ : syracuseStep 4590413 = 1721405) (by norm_num)
theorem B3060275 : Blo 2039435 3060275 := bstep (se 1 (by rfl) ⟨2295206, by rfl⟩ : syracuseStep 3060275 = 4590413) B4590413
theorem B2040183 : Blo 2039435 2040183 := bstep (se 1 (by rfl) ⟨1530137, by rfl⟩ : syracuseStep 2040183 = 3060275) B3060275
theorem B2582113 : Blo 2039435 2582113 := bbase (se 2 (by rfl) ⟨968292, by rfl⟩ : syracuseStep 2582113 = 1936585) (by norm_num)
theorem B3442817 : Blo 2039435 3442817 := bstep (se 2 (by rfl) ⟨1291056, by rfl⟩ : syracuseStep 3442817 = 2582113) B2582113
theorem B2295211 : Blo 2039435 2295211 := bstep (se 1 (by rfl) ⟨1721408, by rfl⟩ : syracuseStep 2295211 = 3442817) B3442817
theorem B3060281 : Blo 2039435 3060281 := bstep (se 2 (by rfl) ⟨1147605, by rfl⟩ : syracuseStep 3060281 = 2295211) B2295211
theorem B2040187 : Blo 2039435 2040187 := bstep (se 1 (by rfl) ⟨1530140, by rfl⟩ : syracuseStep 2040187 = 3060281) B3060281
theorem B23239061 : Blo 2039435 23239061 := bbase (se 6 (by rfl) ⟨544665, by rfl⟩ : syracuseStep 23239061 = 1089331) (by norm_num)
theorem B15492707 : Blo 2039435 15492707 := bstep (se 1 (by rfl) ⟨11619530, by rfl⟩ : syracuseStep 15492707 = 23239061) B23239061
theorem B10328471 : Blo 2039435 10328471 := bstep (se 1 (by rfl) ⟨7746353, by rfl⟩ : syracuseStep 10328471 = 15492707) B15492707
theorem B6885647 : Blo 2039435 6885647 := bstep (se 1 (by rfl) ⟨5164235, by rfl⟩ : syracuseStep 6885647 = 10328471) B10328471
theorem B4590431 : Blo 2039435 4590431 := bstep (se 1 (by rfl) ⟨3442823, by rfl⟩ : syracuseStep 4590431 = 6885647) B6885647
theorem B3060287 : Blo 2039435 3060287 := bstep (se 1 (by rfl) ⟨2295215, by rfl⟩ : syracuseStep 3060287 = 4590431) B4590431
theorem B2040191 : Blo 2039435 2040191 := bstep (se 1 (by rfl) ⟨1530143, by rfl⟩ : syracuseStep 2040191 = 3060287) B3060287
theorem B3060293 : Blo 2039435 3060293 := bbase (se 4 (by rfl) ⟨286902, by rfl⟩ : syracuseStep 3060293 = 573805) (by norm_num)
theorem B2040195 : Blo 2039435 2040195 := bstep (se 1 (by rfl) ⟨1530146, by rfl⟩ : syracuseStep 2040195 = 3060293) B3060293
theorem B3442837 : Blo 2039435 3442837 := bbase (se 6 (by rfl) ⟨80691, by rfl⟩ : syracuseStep 3442837 = 161383) (by norm_num)
theorem B4590449 : Blo 2039435 4590449 := bstep (se 2 (by rfl) ⟨1721418, by rfl⟩ : syracuseStep 4590449 = 3442837) B3442837
theorem B3060299 : Blo 2039435 3060299 := bstep (se 1 (by rfl) ⟨2295224, by rfl⟩ : syracuseStep 3060299 = 4590449) B4590449
theorem B2040199 : Blo 2039435 2040199 := bstep (se 1 (by rfl) ⟨1530149, by rfl⟩ : syracuseStep 2040199 = 3060299) B3060299
theorem B2295229 : Blo 2039435 2295229 := bbase (se 3 (by rfl) ⟨430355, by rfl⟩ : syracuseStep 2295229 = 860711) (by norm_num)
theorem B3060305 : Blo 2039435 3060305 := bstep (se 2 (by rfl) ⟨1147614, by rfl⟩ : syracuseStep 3060305 = 2295229) B2295229
theorem B2040203 : Blo 2039435 2040203 := bstep (se 1 (by rfl) ⟨1530152, by rfl⟩ : syracuseStep 2040203 = 3060305) B3060305
theorem B6885701 : Blo 2039435 6885701 := bbase (se 4 (by rfl) ⟨645534, by rfl⟩ : syracuseStep 6885701 = 1291069) (by norm_num)
theorem B4590467 : Blo 2039435 4590467 := bstep (se 1 (by rfl) ⟨3442850, by rfl⟩ : syracuseStep 4590467 = 6885701) B6885701
theorem B3060311 : Blo 2039435 3060311 := bstep (se 1 (by rfl) ⟨2295233, by rfl⟩ : syracuseStep 3060311 = 4590467) B4590467
theorem B2040207 : Blo 2039435 2040207 := bstep (se 1 (by rfl) ⟨1530155, by rfl⟩ : syracuseStep 2040207 = 3060311) B3060311
theorem B3060317 : Blo 2039435 3060317 := bbase (se 3 (by rfl) ⟨573809, by rfl⟩ : syracuseStep 3060317 = 1147619) (by norm_num)
theorem B2040211 : Blo 2039435 2040211 := bstep (se 1 (by rfl) ⟨1530158, by rfl⟩ : syracuseStep 2040211 = 3060317) B3060317
theorem B4590485 : Blo 2039435 4590485 := bbase (se 6 (by rfl) ⟨107589, by rfl⟩ : syracuseStep 4590485 = 215179) (by norm_num)
theorem B3060323 : Blo 2039435 3060323 := bstep (se 1 (by rfl) ⟨2295242, by rfl⟩ : syracuseStep 3060323 = 4590485) B4590485
theorem B2040215 : Blo 2039435 2040215 := bstep (se 1 (by rfl) ⟨1530161, by rfl⟩ : syracuseStep 2040215 = 3060323) B3060323
theorem B3102085 : Blo 2039435 3102085 := bbase (se 4 (by rfl) ⟨290820, by rfl⟩ : syracuseStep 3102085 = 581641) (by norm_num)
theorem B4136113 : Blo 2039435 4136113 := bstep (se 2 (by rfl) ⟨1551042, by rfl⟩ : syracuseStep 4136113 = 3102085) B3102085
theorem B5514817 : Blo 2039435 5514817 := bstep (se 2 (by rfl) ⟨2068056, by rfl⟩ : syracuseStep 5514817 = 4136113) B4136113
theorem B7353089 : Blo 2039435 7353089 := bstep (se 2 (by rfl) ⟨2757408, by rfl⟩ : syracuseStep 7353089 = 5514817) B5514817
theorem B4902059 : Blo 2039435 4902059 := bstep (se 1 (by rfl) ⟨3676544, by rfl⟩ : syracuseStep 4902059 = 7353089) B7353089
theorem B3268039 : Blo 2039435 3268039 := bstep (se 1 (by rfl) ⟨2451029, by rfl⟩ : syracuseStep 3268039 = 4902059) B4902059
theorem B4357385 : Blo 2039435 4357385 := bstep (se 2 (by rfl) ⟨1634019, by rfl⟩ : syracuseStep 4357385 = 3268039) B3268039
theorem B2904923 : Blo 2039435 2904923 := bstep (se 1 (by rfl) ⟨2178692, by rfl⟩ : syracuseStep 2904923 = 4357385) B4357385
theorem B7746461 : Blo 2039435 7746461 := bstep (se 3 (by rfl) ⟨1452461, by rfl⟩ : syracuseStep 7746461 = 2904923) B2904923
theorem B5164307 : Blo 2039435 5164307 := bstep (se 1 (by rfl) ⟨3873230, by rfl⟩ : syracuseStep 5164307 = 7746461) B7746461
theorem B3442871 : Blo 2039435 3442871 := bstep (se 1 (by rfl) ⟨2582153, by rfl⟩ : syracuseStep 3442871 = 5164307) B5164307
theorem B2295247 : Blo 2039435 2295247 := bstep (se 1 (by rfl) ⟨1721435, by rfl⟩ : syracuseStep 2295247 = 3442871) B3442871
theorem B3060329 : Blo 2039435 3060329 := bstep (se 2 (by rfl) ⟨1147623, by rfl⟩ : syracuseStep 3060329 = 2295247) B2295247
theorem B2040219 : Blo 2039435 2040219 := bstep (se 1 (by rfl) ⟨1530164, by rfl⟩ : syracuseStep 2040219 = 3060329) B3060329
theorem B2757413 : Blo 2039435 2757413 := bbase (se 4 (by rfl) ⟨258507, by rfl⟩ : syracuseStep 2757413 = 517015) (by norm_num)
theorem B7353101 : Blo 2039435 7353101 := bstep (se 3 (by rfl) ⟨1378706, by rfl⟩ : syracuseStep 7353101 = 2757413) B2757413
theorem B4902067 : Blo 2039435 4902067 := bstep (se 1 (by rfl) ⟨3676550, by rfl⟩ : syracuseStep 4902067 = 7353101) B7353101
theorem B6536089 : Blo 2039435 6536089 := bstep (se 2 (by rfl) ⟨2451033, by rfl⟩ : syracuseStep 6536089 = 4902067) B4902067
theorem B8714785 : Blo 2039435 8714785 := bstep (se 2 (by rfl) ⟨3268044, by rfl⟩ : syracuseStep 8714785 = 6536089) B6536089
theorem B11619713 : Blo 2039435 11619713 := bstep (se 2 (by rfl) ⟨4357392, by rfl⟩ : syracuseStep 11619713 = 8714785) B8714785
theorem B7746475 : Blo 2039435 7746475 := bstep (se 1 (by rfl) ⟨5809856, by rfl⟩ : syracuseStep 7746475 = 11619713) B11619713
theorem B10328633 : Blo 2039435 10328633 := bstep (se 2 (by rfl) ⟨3873237, by rfl⟩ : syracuseStep 10328633 = 7746475) B7746475
theorem B6885755 : Blo 2039435 6885755 := bstep (se 1 (by rfl) ⟨5164316, by rfl⟩ : syracuseStep 6885755 = 10328633) B10328633
theorem B4590503 : Blo 2039435 4590503 := bstep (se 1 (by rfl) ⟨3442877, by rfl⟩ : syracuseStep 4590503 = 6885755) B6885755
theorem B3060335 : Blo 2039435 3060335 := bstep (se 1 (by rfl) ⟨2295251, by rfl⟩ : syracuseStep 3060335 = 4590503) B4590503
theorem B2040223 : Blo 2039435 2040223 := bstep (se 1 (by rfl) ⟨1530167, by rfl⟩ : syracuseStep 2040223 = 3060335) B3060335
theorem B3060341 : Blo 2039435 3060341 := bbase (se 5 (by rfl) ⟨143453, by rfl⟩ : syracuseStep 3060341 = 286907) (by norm_num)
theorem B2040227 : Blo 2039435 2040227 := bstep (se 1 (by rfl) ⟨1530170, by rfl⟩ : syracuseStep 2040227 = 3060341) B3060341
theorem B3873253 : Blo 2039435 3873253 := bbase (se 4 (by rfl) ⟨363117, by rfl⟩ : syracuseStep 3873253 = 726235) (by norm_num)
theorem B5164337 : Blo 2039435 5164337 := bstep (se 2 (by rfl) ⟨1936626, by rfl⟩ : syracuseStep 5164337 = 3873253) B3873253
theorem B3442891 : Blo 2039435 3442891 := bstep (se 1 (by rfl) ⟨2582168, by rfl⟩ : syracuseStep 3442891 = 5164337) B5164337
theorem B4590521 : Blo 2039435 4590521 := bstep (se 2 (by rfl) ⟨1721445, by rfl⟩ : syracuseStep 4590521 = 3442891) B3442891
theorem B3060347 : Blo 2039435 3060347 := bstep (se 1 (by rfl) ⟨2295260, by rfl⟩ : syracuseStep 3060347 = 4590521) B4590521
theorem B2040231 : Blo 2039435 2040231 := bstep (se 1 (by rfl) ⟨1530173, by rfl⟩ : syracuseStep 2040231 = 3060347) B3060347
theorem B2295265 : Blo 2039435 2295265 := bbase (se 2 (by rfl) ⟨860724, by rfl⟩ : syracuseStep 2295265 = 1721449) (by norm_num)
theorem B3060353 : Blo 2039435 3060353 := bstep (se 2 (by rfl) ⟨1147632, by rfl⟩ : syracuseStep 3060353 = 2295265) B2295265
theorem B2040235 : Blo 2039435 2040235 := bstep (se 1 (by rfl) ⟨1530176, by rfl⟩ : syracuseStep 2040235 = 3060353) B3060353
theorem B5164357 : Blo 2039435 5164357 := bbase (se 4 (by rfl) ⟨484158, by rfl⟩ : syracuseStep 5164357 = 968317) (by norm_num)
theorem B6885809 : Blo 2039435 6885809 := bstep (se 2 (by rfl) ⟨2582178, by rfl⟩ : syracuseStep 6885809 = 5164357) B5164357
theorem B4590539 : Blo 2039435 4590539 := bstep (se 1 (by rfl) ⟨3442904, by rfl⟩ : syracuseStep 4590539 = 6885809) B6885809
theorem B3060359 : Blo 2039435 3060359 := bstep (se 1 (by rfl) ⟨2295269, by rfl⟩ : syracuseStep 3060359 = 4590539) B4590539
theorem B2040239 : Blo 2039435 2040239 := bstep (se 1 (by rfl) ⟨1530179, by rfl⟩ : syracuseStep 2040239 = 3060359) B3060359
theorem B3060365 : Blo 2039435 3060365 := bbase (se 3 (by rfl) ⟨573818, by rfl⟩ : syracuseStep 3060365 = 1147637) (by norm_num)
theorem B2040243 : Blo 2039435 2040243 := bstep (se 1 (by rfl) ⟨1530182, by rfl⟩ : syracuseStep 2040243 = 3060365) B3060365
theorem B4590557 : Blo 2039435 4590557 := bbase (se 3 (by rfl) ⟨860729, by rfl⟩ : syracuseStep 4590557 = 1721459) (by norm_num)
theorem B3060371 : Blo 2039435 3060371 := bstep (se 1 (by rfl) ⟨2295278, by rfl⟩ : syracuseStep 3060371 = 4590557) B4590557
theorem B2040247 : Blo 2039435 2040247 := bstep (se 1 (by rfl) ⟨1530185, by rfl⟩ : syracuseStep 2040247 = 3060371) B3060371
theorem B3442925 : Blo 2039435 3442925 := bbase (se 3 (by rfl) ⟨645548, by rfl⟩ : syracuseStep 3442925 = 1291097) (by norm_num)
theorem B2295283 : Blo 2039435 2295283 := bstep (se 1 (by rfl) ⟨1721462, by rfl⟩ : syracuseStep 2295283 = 3442925) B3442925
theorem B3060377 : Blo 2039435 3060377 := bstep (se 2 (by rfl) ⟨1147641, by rfl⟩ : syracuseStep 3060377 = 2295283) B2295283
theorem B2040251 : Blo 2039435 2040251 := bstep (se 1 (by rfl) ⟨1530188, by rfl⟩ : syracuseStep 2040251 = 3060377) B3060377
theorem B2795077 : Blo 2039435 2795077 := bbase (se 4 (by rfl) ⟨262038, by rfl⟩ : syracuseStep 2795077 = 524077) (by norm_num)
theorem B14907077 : Blo 2039435 14907077 := bstep (se 4 (by rfl) ⟨1397538, by rfl⟩ : syracuseStep 14907077 = 2795077) B2795077
theorem B9938051 : Blo 2039435 9938051 := bstep (se 1 (by rfl) ⟨7453538, by rfl⟩ : syracuseStep 9938051 = 14907077) B14907077
theorem B6625367 : Blo 2039435 6625367 := bstep (se 1 (by rfl) ⟨4969025, by rfl⟩ : syracuseStep 6625367 = 9938051) B9938051
theorem B282682325 : Blo 2039435 282682325 := bstep (se 7 (by rfl) ⟨3312683, by rfl⟩ : syracuseStep 282682325 = 6625367) B6625367
theorem B188454883 : Blo 2039435 188454883 := bstep (se 1 (by rfl) ⟨141341162, by rfl⟩ : syracuseStep 188454883 = 282682325) B282682325
theorem B251273177 : Blo 2039435 251273177 := bstep (se 2 (by rfl) ⟨94227441, by rfl⟩ : syracuseStep 251273177 = 188454883) B188454883
theorem B167515451 : Blo 2039435 167515451 := bstep (se 1 (by rfl) ⟨125636588, by rfl⟩ : syracuseStep 167515451 = 251273177) B251273177
theorem B111676967 : Blo 2039435 111676967 := bstep (se 1 (by rfl) ⟨83757725, by rfl⟩ : syracuseStep 111676967 = 167515451) B167515451
theorem B74451311 : Blo 2039435 74451311 := bstep (se 1 (by rfl) ⟨55838483, by rfl⟩ : syracuseStep 74451311 = 111676967) B111676967
theorem B49634207 : Blo 2039435 49634207 := bstep (se 1 (by rfl) ⟨37225655, by rfl⟩ : syracuseStep 49634207 = 74451311) B74451311
theorem B33089471 : Blo 2039435 33089471 := bstep (se 1 (by rfl) ⟨24817103, by rfl⟩ : syracuseStep 33089471 = 49634207) B49634207
theorem B22059647 : Blo 2039435 22059647 := bstep (se 1 (by rfl) ⟨16544735, by rfl⟩ : syracuseStep 22059647 = 33089471) B33089471
theorem B14706431 : Blo 2039435 14706431 := bstep (se 1 (by rfl) ⟨11029823, by rfl⟩ : syracuseStep 14706431 = 22059647) B22059647
theorem B9804287 : Blo 2039435 9804287 := bstep (se 1 (by rfl) ⟨7353215, by rfl⟩ : syracuseStep 9804287 = 14706431) B14706431
theorem B26144765 : Blo 2039435 26144765 := bstep (se 3 (by rfl) ⟨4902143, by rfl⟩ : syracuseStep 26144765 = 9804287) B9804287
theorem B17429843 : Blo 2039435 17429843 := bstep (se 1 (by rfl) ⟨13072382, by rfl⟩ : syracuseStep 17429843 = 26144765) B26144765
theorem B11619895 : Blo 2039435 11619895 := bstep (se 1 (by rfl) ⟨8714921, by rfl⟩ : syracuseStep 11619895 = 17429843) B17429843
theorem B15493193 : Blo 2039435 15493193 := bstep (se 2 (by rfl) ⟨5809947, by rfl⟩ : syracuseStep 15493193 = 11619895) B11619895
theorem B10328795 : Blo 2039435 10328795 := bstep (se 1 (by rfl) ⟨7746596, by rfl⟩ : syracuseStep 10328795 = 15493193) B15493193
theorem B6885863 : Blo 2039435 6885863 := bstep (se 1 (by rfl) ⟨5164397, by rfl⟩ : syracuseStep 6885863 = 10328795) B10328795
theorem B4590575 : Blo 2039435 4590575 := bstep (se 1 (by rfl) ⟨3442931, by rfl⟩ : syracuseStep 4590575 = 6885863) B6885863
theorem B3060383 : Blo 2039435 3060383 := bstep (se 1 (by rfl) ⟨2295287, by rfl⟩ : syracuseStep 3060383 = 4590575) B4590575
theorem B2040255 : Blo 2039435 2040255 := bstep (se 1 (by rfl) ⟨1530191, by rfl⟩ : syracuseStep 2040255 = 3060383) B3060383
theorem B3060389 : Blo 2039435 3060389 := bbase (se 4 (by rfl) ⟨286911, by rfl⟩ : syracuseStep 3060389 = 573823) (by norm_num)
theorem B2040259 : Blo 2039435 2040259 := bstep (se 1 (by rfl) ⟨1530194, by rfl⟩ : syracuseStep 2040259 = 3060389) B3060389
theorem B2582209 : Blo 2039435 2582209 := bbase (se 2 (by rfl) ⟨968328, by rfl⟩ : syracuseStep 2582209 = 1936657) (by norm_num)
theorem B3442945 : Blo 2039435 3442945 := bstep (se 2 (by rfl) ⟨1291104, by rfl⟩ : syracuseStep 3442945 = 2582209) B2582209
theorem B4590593 : Blo 2039435 4590593 := bstep (se 2 (by rfl) ⟨1721472, by rfl⟩ : syracuseStep 4590593 = 3442945) B3442945
theorem B3060395 : Blo 2039435 3060395 := bstep (se 1 (by rfl) ⟨2295296, by rfl⟩ : syracuseStep 3060395 = 4590593) B4590593
theorem B2040263 : Blo 2039435 2040263 := bstep (se 1 (by rfl) ⟨1530197, by rfl⟩ : syracuseStep 2040263 = 3060395) B3060395
theorem B2295301 : Blo 2039435 2295301 := bbase (se 4 (by rfl) ⟨215184, by rfl⟩ : syracuseStep 2295301 = 430369) (by norm_num)
theorem B3060401 : Blo 2039435 3060401 := bstep (se 2 (by rfl) ⟨1147650, by rfl⟩ : syracuseStep 3060401 = 2295301) B2295301
theorem B2040267 : Blo 2039435 2040267 := bstep (se 1 (by rfl) ⟨1530200, by rfl⟩ : syracuseStep 2040267 = 3060401) B3060401
theorem B2904997 : Blo 2039435 2904997 := bbase (se 4 (by rfl) ⟨272343, by rfl⟩ : syracuseStep 2904997 = 544687) (by norm_num)
theorem B3873329 : Blo 2039435 3873329 := bstep (se 2 (by rfl) ⟨1452498, by rfl⟩ : syracuseStep 3873329 = 2904997) B2904997
theorem B2582219 : Blo 2039435 2582219 := bstep (se 1 (by rfl) ⟨1936664, by rfl⟩ : syracuseStep 2582219 = 3873329) B3873329
theorem B6885917 : Blo 2039435 6885917 := bstep (se 3 (by rfl) ⟨1291109, by rfl⟩ : syracuseStep 6885917 = 2582219) B2582219
theorem B4590611 : Blo 2039435 4590611 := bstep (se 1 (by rfl) ⟨3442958, by rfl⟩ : syracuseStep 4590611 = 6885917) B6885917
theorem B3060407 : Blo 2039435 3060407 := bstep (se 1 (by rfl) ⟨2295305, by rfl⟩ : syracuseStep 3060407 = 4590611) B4590611
theorem B2040271 : Blo 2039435 2040271 := bstep (se 1 (by rfl) ⟨1530203, by rfl⟩ : syracuseStep 2040271 = 3060407) B3060407
theorem B3060413 : Blo 2039435 3060413 := bbase (se 3 (by rfl) ⟨573827, by rfl⟩ : syracuseStep 3060413 = 1147655) (by norm_num)
theorem B2040275 : Blo 2039435 2040275 := bstep (se 1 (by rfl) ⟨1530206, by rfl⟩ : syracuseStep 2040275 = 3060413) B3060413
theorem B4590629 : Blo 2039435 4590629 := bbase (se 4 (by rfl) ⟨430371, by rfl⟩ : syracuseStep 4590629 = 860743) (by norm_num)
theorem B3060419 : Blo 2039435 3060419 := bstep (se 1 (by rfl) ⟨2295314, by rfl⟩ : syracuseStep 3060419 = 4590629) B4590629
theorem B2040279 : Blo 2039435 2040279 := bstep (se 1 (by rfl) ⟨1530209, by rfl⟩ : syracuseStep 2040279 = 3060419) B3060419
theorem B5164469 : Blo 2039435 5164469 := bbase (se 5 (by rfl) ⟨242084, by rfl⟩ : syracuseStep 5164469 = 484169) (by norm_num)
theorem B3442979 : Blo 2039435 3442979 := bstep (se 1 (by rfl) ⟨2582234, by rfl⟩ : syracuseStep 3442979 = 5164469) B5164469
theorem B2295319 : Blo 2039435 2295319 := bstep (se 1 (by rfl) ⟨1721489, by rfl⟩ : syracuseStep 2295319 = 3442979) B3442979
theorem B3060425 : Blo 2039435 3060425 := bstep (se 2 (by rfl) ⟨1147659, by rfl⟩ : syracuseStep 3060425 = 2295319) B2295319
theorem B2040283 : Blo 2039435 2040283 := bstep (se 1 (by rfl) ⟨1530212, by rfl⟩ : syracuseStep 2040283 = 3060425) B3060425
theorem B4902221 : Blo 2039435 4902221 := bbase (se 3 (by rfl) ⟨919166, by rfl⟩ : syracuseStep 4902221 = 1838333) (by norm_num)
theorem B13072589 : Blo 2039435 13072589 := bstep (se 3 (by rfl) ⟨2451110, by rfl⟩ : syracuseStep 13072589 = 4902221) B4902221
theorem B8715059 : Blo 2039435 8715059 := bstep (se 1 (by rfl) ⟨6536294, by rfl⟩ : syracuseStep 8715059 = 13072589) B13072589
theorem B5810039 : Blo 2039435 5810039 := bstep (se 1 (by rfl) ⟨4357529, by rfl⟩ : syracuseStep 5810039 = 8715059) B8715059
theorem B3873359 : Blo 2039435 3873359 := bstep (se 1 (by rfl) ⟨2905019, by rfl⟩ : syracuseStep 3873359 = 5810039) B5810039
theorem B10328957 : Blo 2039435 10328957 := bstep (se 3 (by rfl) ⟨1936679, by rfl⟩ : syracuseStep 10328957 = 3873359) B3873359
theorem B6885971 : Blo 2039435 6885971 := bstep (se 1 (by rfl) ⟨5164478, by rfl⟩ : syracuseStep 6885971 = 10328957) B10328957
theorem B4590647 : Blo 2039435 4590647 := bstep (se 1 (by rfl) ⟨3442985, by rfl⟩ : syracuseStep 4590647 = 6885971) B6885971
theorem B3060431 : Blo 2039435 3060431 := bstep (se 1 (by rfl) ⟨2295323, by rfl⟩ : syracuseStep 3060431 = 4590647) B4590647
theorem B2040287 : Blo 2039435 2040287 := bstep (se 1 (by rfl) ⟨1530215, by rfl⟩ : syracuseStep 2040287 = 3060431) B3060431
theorem B3060437 : Blo 2039435 3060437 := bbase (se 7 (by rfl) ⟨35864, by rfl⟩ : syracuseStep 3060437 = 71729) (by norm_num)
theorem B2040291 : Blo 2039435 2040291 := bstep (se 1 (by rfl) ⟨1530218, by rfl⟩ : syracuseStep 2040291 = 3060437) B3060437
theorem B4653301 : Blo 2039435 4653301 := bbase (se 5 (by rfl) ⟨218123, by rfl⟩ : syracuseStep 4653301 = 436247) (by norm_num)
theorem B6204401 : Blo 2039435 6204401 := bstep (se 2 (by rfl) ⟨2326650, by rfl⟩ : syracuseStep 6204401 = 4653301) B4653301
theorem B4136267 : Blo 2039435 4136267 := bstep (se 1 (by rfl) ⟨3102200, by rfl⟩ : syracuseStep 4136267 = 6204401) B6204401
theorem B2757511 : Blo 2039435 2757511 := bstep (se 1 (by rfl) ⟨2068133, by rfl⟩ : syracuseStep 2757511 = 4136267) B4136267
theorem B3676681 : Blo 2039435 3676681 := bstep (se 2 (by rfl) ⟨1378755, by rfl⟩ : syracuseStep 3676681 = 2757511) B2757511
theorem B4902241 : Blo 2039435 4902241 := bstep (se 2 (by rfl) ⟨1838340, by rfl⟩ : syracuseStep 4902241 = 3676681) B3676681
theorem B6536321 : Blo 2039435 6536321 := bstep (se 2 (by rfl) ⟨2451120, by rfl⟩ : syracuseStep 6536321 = 4902241) B4902241
theorem B4357547 : Blo 2039435 4357547 := bstep (se 1 (by rfl) ⟨3268160, by rfl⟩ : syracuseStep 4357547 = 6536321) B6536321
theorem B2905031 : Blo 2039435 2905031 := bstep (se 1 (by rfl) ⟨2178773, by rfl⟩ : syracuseStep 2905031 = 4357547) B4357547
theorem B7746749 : Blo 2039435 7746749 := bstep (se 3 (by rfl) ⟨1452515, by rfl⟩ : syracuseStep 7746749 = 2905031) B2905031
theorem B5164499 : Blo 2039435 5164499 := bstep (se 1 (by rfl) ⟨3873374, by rfl⟩ : syracuseStep 5164499 = 7746749) B7746749
theorem B3442999 : Blo 2039435 3442999 := bstep (se 1 (by rfl) ⟨2582249, by rfl⟩ : syracuseStep 3442999 = 5164499) B5164499
theorem B4590665 : Blo 2039435 4590665 := bstep (se 2 (by rfl) ⟨1721499, by rfl⟩ : syracuseStep 4590665 = 3442999) B3442999
theorem B3060443 : Blo 2039435 3060443 := bstep (se 1 (by rfl) ⟨2295332, by rfl⟩ : syracuseStep 3060443 = 4590665) B4590665
theorem B2040295 : Blo 2039435 2040295 := bstep (se 1 (by rfl) ⟨1530221, by rfl⟩ : syracuseStep 2040295 = 3060443) B3060443
theorem B2295337 : Blo 2039435 2295337 := bbase (se 2 (by rfl) ⟨860751, by rfl⟩ : syracuseStep 2295337 = 1721503) (by norm_num)
theorem B3060449 : Blo 2039435 3060449 := bstep (se 2 (by rfl) ⟨1147668, by rfl⟩ : syracuseStep 3060449 = 2295337) B2295337
theorem B2040299 : Blo 2039435 2040299 := bstep (se 1 (by rfl) ⟨1530224, by rfl⟩ : syracuseStep 2040299 = 3060449) B3060449
theorem B2068141 : Blo 2039435 2068141 := bbase (se 3 (by rfl) ⟨387776, by rfl⟩ : syracuseStep 2068141 = 775553) (by norm_num)
theorem B2757521 : Blo 2039435 2757521 := bstep (se 2 (by rfl) ⟨1034070, by rfl⟩ : syracuseStep 2757521 = 2068141) B2068141
theorem B7353389 : Blo 2039435 7353389 := bstep (se 3 (by rfl) ⟨1378760, by rfl⟩ : syracuseStep 7353389 = 2757521) B2757521
theorem B19609037 : Blo 2039435 19609037 := bstep (se 3 (by rfl) ⟨3676694, by rfl⟩ : syracuseStep 19609037 = 7353389) B7353389
theorem B13072691 : Blo 2039435 13072691 := bstep (se 1 (by rfl) ⟨9804518, by rfl⟩ : syracuseStep 13072691 = 19609037) B19609037
theorem B8715127 : Blo 2039435 8715127 := bstep (se 1 (by rfl) ⟨6536345, by rfl⟩ : syracuseStep 8715127 = 13072691) B13072691
theorem B11620169 : Blo 2039435 11620169 := bstep (se 2 (by rfl) ⟨4357563, by rfl⟩ : syracuseStep 11620169 = 8715127) B8715127
theorem B7746779 : Blo 2039435 7746779 := bstep (se 1 (by rfl) ⟨5810084, by rfl⟩ : syracuseStep 7746779 = 11620169) B11620169
theorem B5164519 : Blo 2039435 5164519 := bstep (se 1 (by rfl) ⟨3873389, by rfl⟩ : syracuseStep 5164519 = 7746779) B7746779
theorem B6886025 : Blo 2039435 6886025 := bstep (se 2 (by rfl) ⟨2582259, by rfl⟩ : syracuseStep 6886025 = 5164519) B5164519
theorem B4590683 : Blo 2039435 4590683 := bstep (se 1 (by rfl) ⟨3443012, by rfl⟩ : syracuseStep 4590683 = 6886025) B6886025
theorem B3060455 : Blo 2039435 3060455 := bstep (se 1 (by rfl) ⟨2295341, by rfl⟩ : syracuseStep 3060455 = 4590683) B4590683
theorem B2040303 : Blo 2039435 2040303 := bstep (se 1 (by rfl) ⟨1530227, by rfl⟩ : syracuseStep 2040303 = 3060455) B3060455
theorem B3060461 : Blo 2039435 3060461 := bbase (se 3 (by rfl) ⟨573836, by rfl⟩ : syracuseStep 3060461 = 1147673) (by norm_num)
theorem B2040307 : Blo 2039435 2040307 := bstep (se 1 (by rfl) ⟨1530230, by rfl⟩ : syracuseStep 2040307 = 3060461) B3060461
theorem B4590701 : Blo 2039435 4590701 := bbase (se 3 (by rfl) ⟨860756, by rfl⟩ : syracuseStep 4590701 = 1721513) (by norm_num)
theorem B3060467 : Blo 2039435 3060467 := bstep (se 1 (by rfl) ⟨2295350, by rfl⟩ : syracuseStep 3060467 = 4590701) B4590701
theorem B2040311 : Blo 2039435 2040311 := bstep (se 1 (by rfl) ⟨1530233, by rfl⟩ : syracuseStep 2040311 = 3060467) B3060467
theorem B3873413 : Blo 2039435 3873413 := bbase (se 4 (by rfl) ⟨363132, by rfl⟩ : syracuseStep 3873413 = 726265) (by norm_num)
theorem B2582275 : Blo 2039435 2582275 := bstep (se 1 (by rfl) ⟨1936706, by rfl⟩ : syracuseStep 2582275 = 3873413) B3873413
theorem B3443033 : Blo 2039435 3443033 := bstep (se 2 (by rfl) ⟨1291137, by rfl⟩ : syracuseStep 3443033 = 2582275) B2582275
theorem B2295355 : Blo 2039435 2295355 := bstep (se 1 (by rfl) ⟨1721516, by rfl⟩ : syracuseStep 2295355 = 3443033) B3443033
theorem B3060473 : Blo 2039435 3060473 := bstep (se 2 (by rfl) ⟨1147677, by rfl⟩ : syracuseStep 3060473 = 2295355) B2295355
theorem B2040315 : Blo 2039435 2040315 := bstep (se 1 (by rfl) ⟨1530236, by rfl⟩ : syracuseStep 2040315 = 3060473) B3060473
theorem B9433685 : Blo 2039435 9433685 := bbase (se 8 (by rfl) ⟨55275, by rfl⟩ : syracuseStep 9433685 = 110551) (by norm_num)
theorem B25156493 : Blo 2039435 25156493 := bstep (se 3 (by rfl) ⟨4716842, by rfl⟩ : syracuseStep 25156493 = 9433685) B9433685
theorem B16770995 : Blo 2039435 16770995 := bstep (se 1 (by rfl) ⟨12578246, by rfl⟩ : syracuseStep 16770995 = 25156493) B25156493
theorem B11180663 : Blo 2039435 11180663 := bstep (se 1 (by rfl) ⟨8385497, by rfl⟩ : syracuseStep 11180663 = 16770995) B16770995
theorem B7453775 : Blo 2039435 7453775 := bstep (se 1 (by rfl) ⟨5590331, by rfl⟩ : syracuseStep 7453775 = 11180663) B11180663
theorem B4969183 : Blo 2039435 4969183 := bstep (se 1 (by rfl) ⟨3726887, by rfl⟩ : syracuseStep 4969183 = 7453775) B7453775
theorem B6625577 : Blo 2039435 6625577 := bstep (se 2 (by rfl) ⟨2484591, by rfl⟩ : syracuseStep 6625577 = 4969183) B4969183
theorem B17668205 : Blo 2039435 17668205 := bstep (se 3 (by rfl) ⟨3312788, by rfl⟩ : syracuseStep 17668205 = 6625577) B6625577
theorem B11778803 : Blo 2039435 11778803 := bstep (se 1 (by rfl) ⟨8834102, by rfl⟩ : syracuseStep 11778803 = 17668205) B17668205
theorem B7852535 : Blo 2039435 7852535 := bstep (se 1 (by rfl) ⟨5889401, by rfl⟩ : syracuseStep 7852535 = 11778803) B11778803
theorem B5235023 : Blo 2039435 5235023 := bstep (se 1 (by rfl) ⟨3926267, by rfl⟩ : syracuseStep 5235023 = 7852535) B7852535
theorem B3490015 : Blo 2039435 3490015 := bstep (se 1 (by rfl) ⟨2617511, by rfl⟩ : syracuseStep 3490015 = 5235023) B5235023
theorem B4653353 : Blo 2039435 4653353 := bstep (se 2 (by rfl) ⟨1745007, by rfl⟩ : syracuseStep 4653353 = 3490015) B3490015
theorem B3102235 : Blo 2039435 3102235 := bstep (se 1 (by rfl) ⟨2326676, by rfl⟩ : syracuseStep 3102235 = 4653353) B4653353
theorem B66181013 : Blo 2039435 66181013 := bstep (se 6 (by rfl) ⟨1551117, by rfl⟩ : syracuseStep 66181013 = 3102235) B3102235
theorem B44120675 : Blo 2039435 44120675 := bstep (se 1 (by rfl) ⟨33090506, by rfl⟩ : syracuseStep 44120675 = 66181013) B66181013
theorem B29413783 : Blo 2039435 29413783 := bstep (se 1 (by rfl) ⟨22060337, by rfl⟩ : syracuseStep 29413783 = 44120675) B44120675
theorem B39218377 : Blo 2039435 39218377 := bstep (se 2 (by rfl) ⟨14706891, by rfl⟩ : syracuseStep 39218377 = 29413783) B29413783
theorem B52291169 : Blo 2039435 52291169 := bstep (se 2 (by rfl) ⟨19609188, by rfl⟩ : syracuseStep 52291169 = 39218377) B39218377
theorem B34860779 : Blo 2039435 34860779 := bstep (se 1 (by rfl) ⟨26145584, by rfl⟩ : syracuseStep 34860779 = 52291169) B52291169
theorem B23240519 : Blo 2039435 23240519 := bstep (se 1 (by rfl) ⟨17430389, by rfl⟩ : syracuseStep 23240519 = 34860779) B34860779
theorem B15493679 : Blo 2039435 15493679 := bstep (se 1 (by rfl) ⟨11620259, by rfl⟩ : syracuseStep 15493679 = 23240519) B23240519
theorem B10329119 : Blo 2039435 10329119 := bstep (se 1 (by rfl) ⟨7746839, by rfl⟩ : syracuseStep 10329119 = 15493679) B15493679
theorem B6886079 : Blo 2039435 6886079 := bstep (se 1 (by rfl) ⟨5164559, by rfl⟩ : syracuseStep 6886079 = 10329119) B10329119
theorem B4590719 : Blo 2039435 4590719 := bstep (se 1 (by rfl) ⟨3443039, by rfl⟩ : syracuseStep 4590719 = 6886079) B6886079
theorem B3060479 : Blo 2039435 3060479 := bstep (se 1 (by rfl) ⟨2295359, by rfl⟩ : syracuseStep 3060479 = 4590719) B4590719
theorem B2040319 : Blo 2039435 2040319 := bstep (se 1 (by rfl) ⟨1530239, by rfl⟩ : syracuseStep 2040319 = 3060479) B3060479
theorem B3060485 : Blo 2039435 3060485 := bbase (se 4 (by rfl) ⟨286920, by rfl⟩ : syracuseStep 3060485 = 573841) (by norm_num)
theorem B2040323 : Blo 2039435 2040323 := bstep (se 1 (by rfl) ⟨1530242, by rfl⟩ : syracuseStep 2040323 = 3060485) B3060485
theorem B3443053 : Blo 2039435 3443053 := bbase (se 3 (by rfl) ⟨645572, by rfl⟩ : syracuseStep 3443053 = 1291145) (by norm_num)
theorem B4590737 : Blo 2039435 4590737 := bstep (se 2 (by rfl) ⟨1721526, by rfl⟩ : syracuseStep 4590737 = 3443053) B3443053
theorem B3060491 : Blo 2039435 3060491 := bstep (se 1 (by rfl) ⟨2295368, by rfl⟩ : syracuseStep 3060491 = 4590737) B4590737
theorem B2040327 : Blo 2039435 2040327 := bstep (se 1 (by rfl) ⟨1530245, by rfl⟩ : syracuseStep 2040327 = 3060491) B3060491
theorem B2295373 : Blo 2039435 2295373 := bbase (se 3 (by rfl) ⟨430382, by rfl⟩ : syracuseStep 2295373 = 860765) (by norm_num)
theorem B3060497 : Blo 2039435 3060497 := bstep (se 2 (by rfl) ⟨1147686, by rfl⟩ : syracuseStep 3060497 = 2295373) B2295373
theorem B2040331 : Blo 2039435 2040331 := bstep (se 1 (by rfl) ⟨1530248, by rfl⟩ : syracuseStep 2040331 = 3060497) B3060497
theorem B6886133 : Blo 2039435 6886133 := bbase (se 5 (by rfl) ⟨322787, by rfl⟩ : syracuseStep 6886133 = 645575) (by norm_num)
theorem B4590755 : Blo 2039435 4590755 := bstep (se 1 (by rfl) ⟨3443066, by rfl⟩ : syracuseStep 4590755 = 6886133) B6886133
theorem B3060503 : Blo 2039435 3060503 := bstep (se 1 (by rfl) ⟨2295377, by rfl⟩ : syracuseStep 3060503 = 4590755) B4590755
theorem B2040335 : Blo 2039435 2040335 := bstep (se 1 (by rfl) ⟨1530251, by rfl⟩ : syracuseStep 2040335 = 3060503) B3060503
theorem B3060509 : Blo 2039435 3060509 := bbase (se 3 (by rfl) ⟨573845, by rfl⟩ : syracuseStep 3060509 = 1147691) (by norm_num)
theorem B2040339 : Blo 2039435 2040339 := bstep (se 1 (by rfl) ⟨1530254, by rfl⟩ : syracuseStep 2040339 = 3060509) B3060509
theorem B4590773 : Blo 2039435 4590773 := bbase (se 5 (by rfl) ⟨215192, by rfl⟩ : syracuseStep 4590773 = 430385) (by norm_num)
theorem B3060515 : Blo 2039435 3060515 := bstep (se 1 (by rfl) ⟨2295386, by rfl⟩ : syracuseStep 3060515 = 4590773) B4590773
theorem B2040343 : Blo 2039435 2040343 := bstep (se 1 (by rfl) ⟨1530257, by rfl⟩ : syracuseStep 2040343 = 3060515) B3060515
theorem B2178829 : Blo 2039435 2178829 := bbase (se 3 (by rfl) ⟨408530, by rfl⟩ : syracuseStep 2178829 = 817061) (by norm_num)
theorem B11620421 : Blo 2039435 11620421 := bstep (se 4 (by rfl) ⟨1089414, by rfl⟩ : syracuseStep 11620421 = 2178829) B2178829
theorem B7746947 : Blo 2039435 7746947 := bstep (se 1 (by rfl) ⟨5810210, by rfl⟩ : syracuseStep 7746947 = 11620421) B11620421
theorem B5164631 : Blo 2039435 5164631 := bstep (se 1 (by rfl) ⟨3873473, by rfl⟩ : syracuseStep 5164631 = 7746947) B7746947
theorem B3443087 : Blo 2039435 3443087 := bstep (se 1 (by rfl) ⟨2582315, by rfl⟩ : syracuseStep 3443087 = 5164631) B5164631
theorem B2295391 : Blo 2039435 2295391 := bstep (se 1 (by rfl) ⟨1721543, by rfl⟩ : syracuseStep 2295391 = 3443087) B3443087
theorem B3060521 : Blo 2039435 3060521 := bstep (se 2 (by rfl) ⟨1147695, by rfl⟩ : syracuseStep 3060521 = 2295391) B2295391
theorem B2040347 : Blo 2039435 2040347 := bstep (se 1 (by rfl) ⟨1530260, by rfl⟩ : syracuseStep 2040347 = 3060521) B3060521
theorem B2178833 : Blo 2039435 2178833 := bbase (se 2 (by rfl) ⟨817062, by rfl⟩ : syracuseStep 2178833 = 1634125) (by norm_num)
theorem B5810221 : Blo 2039435 5810221 := bstep (se 3 (by rfl) ⟨1089416, by rfl⟩ : syracuseStep 5810221 = 2178833) B2178833
theorem B7746961 : Blo 2039435 7746961 := bstep (se 2 (by rfl) ⟨2905110, by rfl⟩ : syracuseStep 7746961 = 5810221) B5810221
theorem B10329281 : Blo 2039435 10329281 := bstep (se 2 (by rfl) ⟨3873480, by rfl⟩ : syracuseStep 10329281 = 7746961) B7746961
theorem B6886187 : Blo 2039435 6886187 := bstep (se 1 (by rfl) ⟨5164640, by rfl⟩ : syracuseStep 6886187 = 10329281) B10329281
theorem B4590791 : Blo 2039435 4590791 := bstep (se 1 (by rfl) ⟨3443093, by rfl⟩ : syracuseStep 4590791 = 6886187) B6886187
theorem B3060527 : Blo 2039435 3060527 := bstep (se 1 (by rfl) ⟨2295395, by rfl⟩ : syracuseStep 3060527 = 4590791) B4590791
theorem B2040351 : Blo 2039435 2040351 := bstep (se 1 (by rfl) ⟨1530263, by rfl⟩ : syracuseStep 2040351 = 3060527) B3060527
theorem B3060533 : Blo 2039435 3060533 := bbase (se 5 (by rfl) ⟨143462, by rfl⟩ : syracuseStep 3060533 = 286925) (by norm_num)
theorem B2040355 : Blo 2039435 2040355 := bstep (se 1 (by rfl) ⟨1530266, by rfl⟩ : syracuseStep 2040355 = 3060533) B3060533
theorem B5164661 : Blo 2039435 5164661 := bbase (se 5 (by rfl) ⟨242093, by rfl⟩ : syracuseStep 5164661 = 484187) (by norm_num)
theorem B3443107 : Blo 2039435 3443107 := bstep (se 1 (by rfl) ⟨2582330, by rfl⟩ : syracuseStep 3443107 = 5164661) B5164661
theorem B4590809 : Blo 2039435 4590809 := bstep (se 2 (by rfl) ⟨1721553, by rfl⟩ : syracuseStep 4590809 = 3443107) B3443107
theorem B3060539 : Blo 2039435 3060539 := bstep (se 1 (by rfl) ⟨2295404, by rfl⟩ : syracuseStep 3060539 = 4590809) B4590809
theorem B2040359 : Blo 2039435 2040359 := bstep (se 1 (by rfl) ⟨1530269, by rfl⟩ : syracuseStep 2040359 = 3060539) B3060539
theorem B2295409 : Blo 2039435 2295409 := bbase (se 2 (by rfl) ⟨860778, by rfl⟩ : syracuseStep 2295409 = 1721557) (by norm_num)
theorem B3060545 : Blo 2039435 3060545 := bstep (se 2 (by rfl) ⟨1147704, by rfl⟩ : syracuseStep 3060545 = 2295409) B2295409
theorem B2040363 : Blo 2039435 2040363 := bstep (se 1 (by rfl) ⟨1530272, by rfl⟩ : syracuseStep 2040363 = 3060545) B3060545
theorem B5306573 : Blo 2039435 5306573 := bbase (se 3 (by rfl) ⟨994982, by rfl⟩ : syracuseStep 5306573 = 1989965) (by norm_num)
theorem B14150861 : Blo 2039435 14150861 := bstep (se 3 (by rfl) ⟨2653286, by rfl⟩ : syracuseStep 14150861 = 5306573) B5306573
theorem B9433907 : Blo 2039435 9433907 := bstep (se 1 (by rfl) ⟨7075430, by rfl⟩ : syracuseStep 9433907 = 14150861) B14150861
theorem B6289271 : Blo 2039435 6289271 := bstep (se 1 (by rfl) ⟨4716953, by rfl⟩ : syracuseStep 6289271 = 9433907) B9433907
theorem B4192847 : Blo 2039435 4192847 := bstep (se 1 (by rfl) ⟨3144635, by rfl⟩ : syracuseStep 4192847 = 6289271) B6289271
theorem B2795231 : Blo 2039435 2795231 := bstep (se 1 (by rfl) ⟨2096423, by rfl⟩ : syracuseStep 2795231 = 4192847) B4192847
theorem B7453949 : Blo 2039435 7453949 := bstep (se 3 (by rfl) ⟨1397615, by rfl⟩ : syracuseStep 7453949 = 2795231) B2795231
theorem B79508789 : Blo 2039435 79508789 := bstep (se 5 (by rfl) ⟨3726974, by rfl⟩ : syracuseStep 79508789 = 7453949) B7453949
theorem B53005859 : Blo 2039435 53005859 := bstep (se 1 (by rfl) ⟨39754394, by rfl⟩ : syracuseStep 53005859 = 79508789) B79508789
theorem B35337239 : Blo 2039435 35337239 := bstep (se 1 (by rfl) ⟨26502929, by rfl⟩ : syracuseStep 35337239 = 53005859) B53005859
theorem B23558159 : Blo 2039435 23558159 := bstep (se 1 (by rfl) ⟨17668619, by rfl⟩ : syracuseStep 23558159 = 35337239) B35337239
theorem B62821757 : Blo 2039435 62821757 := bstep (se 3 (by rfl) ⟨11779079, by rfl⟩ : syracuseStep 62821757 = 23558159) B23558159
theorem B41881171 : Blo 2039435 41881171 := bstep (se 1 (by rfl) ⟨31410878, by rfl⟩ : syracuseStep 41881171 = 62821757) B62821757
theorem B55841561 : Blo 2039435 55841561 := bstep (se 2 (by rfl) ⟨20940585, by rfl⟩ : syracuseStep 55841561 = 41881171) B41881171
theorem B37227707 : Blo 2039435 37227707 := bstep (se 1 (by rfl) ⟨27920780, by rfl⟩ : syracuseStep 37227707 = 55841561) B55841561
theorem B24818471 : Blo 2039435 24818471 := bstep (se 1 (by rfl) ⟨18613853, by rfl⟩ : syracuseStep 24818471 = 37227707) B37227707
theorem B16545647 : Blo 2039435 16545647 := bstep (se 1 (by rfl) ⟨12409235, by rfl⟩ : syracuseStep 16545647 = 24818471) B24818471
theorem B11030431 : Blo 2039435 11030431 := bstep (se 1 (by rfl) ⟨8272823, by rfl⟩ : syracuseStep 11030431 = 16545647) B16545647
theorem B14707241 : Blo 2039435 14707241 := bstep (se 2 (by rfl) ⟨5515215, by rfl⟩ : syracuseStep 14707241 = 11030431) B11030431
theorem B9804827 : Blo 2039435 9804827 := bstep (se 1 (by rfl) ⟨7353620, by rfl⟩ : syracuseStep 9804827 = 14707241) B14707241
theorem B6536551 : Blo 2039435 6536551 := bstep (se 1 (by rfl) ⟨4902413, by rfl⟩ : syracuseStep 6536551 = 9804827) B9804827
theorem B8715401 : Blo 2039435 8715401 := bstep (se 2 (by rfl) ⟨3268275, by rfl⟩ : syracuseStep 8715401 = 6536551) B6536551
theorem B5810267 : Blo 2039435 5810267 := bstep (se 1 (by rfl) ⟨4357700, by rfl⟩ : syracuseStep 5810267 = 8715401) B8715401
theorem B3873511 : Blo 2039435 3873511 := bstep (se 1 (by rfl) ⟨2905133, by rfl⟩ : syracuseStep 3873511 = 5810267) B5810267
theorem B5164681 : Blo 2039435 5164681 := bstep (se 2 (by rfl) ⟨1936755, by rfl⟩ : syracuseStep 5164681 = 3873511) B3873511
theorem B6886241 : Blo 2039435 6886241 := bstep (se 2 (by rfl) ⟨2582340, by rfl⟩ : syracuseStep 6886241 = 5164681) B5164681
theorem B4590827 : Blo 2039435 4590827 := bstep (se 1 (by rfl) ⟨3443120, by rfl⟩ : syracuseStep 4590827 = 6886241) B6886241
theorem B3060551 : Blo 2039435 3060551 := bstep (se 1 (by rfl) ⟨2295413, by rfl⟩ : syracuseStep 3060551 = 4590827) B4590827
theorem B2040367 : Blo 2039435 2040367 := bstep (se 1 (by rfl) ⟨1530275, by rfl⟩ : syracuseStep 2040367 = 3060551) B3060551
theorem B3060557 : Blo 2039435 3060557 := bbase (se 3 (by rfl) ⟨573854, by rfl⟩ : syracuseStep 3060557 = 1147709) (by norm_num)
theorem B2040371 : Blo 2039435 2040371 := bstep (se 1 (by rfl) ⟨1530278, by rfl⟩ : syracuseStep 2040371 = 3060557) B3060557
theorem B4590845 : Blo 2039435 4590845 := bbase (se 3 (by rfl) ⟨860783, by rfl⟩ : syracuseStep 4590845 = 1721567) (by norm_num)
theorem B3060563 : Blo 2039435 3060563 := bstep (se 1 (by rfl) ⟨2295422, by rfl⟩ : syracuseStep 3060563 = 4590845) B4590845
theorem B2040375 : Blo 2039435 2040375 := bstep (se 1 (by rfl) ⟨1530281, by rfl⟩ : syracuseStep 2040375 = 3060563) B3060563
theorem B3443141 : Blo 2039435 3443141 := bbase (se 4 (by rfl) ⟨322794, by rfl⟩ : syracuseStep 3443141 = 645589) (by norm_num)
theorem B2295427 : Blo 2039435 2295427 := bstep (se 1 (by rfl) ⟨1721570, by rfl⟩ : syracuseStep 2295427 = 3443141) B3443141
theorem B3060569 : Blo 2039435 3060569 := bstep (se 2 (by rfl) ⟨1147713, by rfl⟩ : syracuseStep 3060569 = 2295427) B2295427
theorem B2040379 : Blo 2039435 2040379 := bstep (se 1 (by rfl) ⟨1530284, by rfl⟩ : syracuseStep 2040379 = 3060569) B3060569
theorem B15494165 : Blo 2039435 15494165 := bbase (se 6 (by rfl) ⟨363144, by rfl⟩ : syracuseStep 15494165 = 726289) (by norm_num)
theorem B10329443 : Blo 2039435 10329443 := bstep (se 1 (by rfl) ⟨7747082, by rfl⟩ : syracuseStep 10329443 = 15494165) B15494165
theorem B6886295 : Blo 2039435 6886295 := bstep (se 1 (by rfl) ⟨5164721, by rfl⟩ : syracuseStep 6886295 = 10329443) B10329443
theorem B4590863 : Blo 2039435 4590863 := bstep (se 1 (by rfl) ⟨3443147, by rfl⟩ : syracuseStep 4590863 = 6886295) B6886295
theorem B3060575 : Blo 2039435 3060575 := bstep (se 1 (by rfl) ⟨2295431, by rfl⟩ : syracuseStep 3060575 = 4590863) B4590863
theorem B2040383 : Blo 2039435 2040383 := bstep (se 1 (by rfl) ⟨1530287, by rfl⟩ : syracuseStep 2040383 = 3060575) B3060575
theorem B3060581 : Blo 2039435 3060581 := bbase (se 4 (by rfl) ⟨286929, by rfl⟩ : syracuseStep 3060581 = 573859) (by norm_num)
theorem B2040387 : Blo 2039435 2040387 := bstep (se 1 (by rfl) ⟨1530290, by rfl⟩ : syracuseStep 2040387 = 3060581) B3060581
theorem B3873557 : Blo 2039435 3873557 := bbase (se 6 (by rfl) ⟨90786, by rfl⟩ : syracuseStep 3873557 = 181573) (by norm_num)
theorem B2582371 : Blo 2039435 2582371 := bstep (se 1 (by rfl) ⟨1936778, by rfl⟩ : syracuseStep 2582371 = 3873557) B3873557
theorem B3443161 : Blo 2039435 3443161 := bstep (se 2 (by rfl) ⟨1291185, by rfl⟩ : syracuseStep 3443161 = 2582371) B2582371
theorem B4590881 : Blo 2039435 4590881 := bstep (se 2 (by rfl) ⟨1721580, by rfl⟩ : syracuseStep 4590881 = 3443161) B3443161
theorem B3060587 : Blo 2039435 3060587 := bstep (se 1 (by rfl) ⟨2295440, by rfl⟩ : syracuseStep 3060587 = 4590881) B4590881
theorem B2040391 : Blo 2039435 2040391 := bstep (se 1 (by rfl) ⟨1530293, by rfl⟩ : syracuseStep 2040391 = 3060587) B3060587
theorem B2295445 : Blo 2039435 2295445 := bbase (se 6 (by rfl) ⟨53799, by rfl⟩ : syracuseStep 2295445 = 107599) (by norm_num)
theorem B3060593 : Blo 2039435 3060593 := bstep (se 2 (by rfl) ⟨1147722, by rfl⟩ : syracuseStep 3060593 = 2295445) B2295445
theorem B2040395 : Blo 2039435 2040395 := bstep (se 1 (by rfl) ⟨1530296, by rfl⟩ : syracuseStep 2040395 = 3060593) B3060593
theorem B2582381 : Blo 2039435 2582381 := bbase (se 3 (by rfl) ⟨484196, by rfl⟩ : syracuseStep 2582381 = 968393) (by norm_num)
theorem B6886349 : Blo 2039435 6886349 := bstep (se 3 (by rfl) ⟨1291190, by rfl⟩ : syracuseStep 6886349 = 2582381) B2582381
theorem B4590899 : Blo 2039435 4590899 := bstep (se 1 (by rfl) ⟨3443174, by rfl⟩ : syracuseStep 4590899 = 6886349) B6886349
theorem B3060599 : Blo 2039435 3060599 := bstep (se 1 (by rfl) ⟨2295449, by rfl⟩ : syracuseStep 3060599 = 4590899) B4590899
theorem B2040399 : Blo 2039435 2040399 := bstep (se 1 (by rfl) ⟨1530299, by rfl⟩ : syracuseStep 2040399 = 3060599) B3060599
theorem B3060605 : Blo 2039435 3060605 := bbase (se 3 (by rfl) ⟨573863, by rfl⟩ : syracuseStep 3060605 = 1147727) (by norm_num)
theorem B2040403 : Blo 2039435 2040403 := bstep (se 1 (by rfl) ⟨1530302, by rfl⟩ : syracuseStep 2040403 = 3060605) B3060605
theorem B4590917 : Blo 2039435 4590917 := bbase (se 4 (by rfl) ⟨430398, by rfl⟩ : syracuseStep 4590917 = 860797) (by norm_num)
theorem B3060611 : Blo 2039435 3060611 := bstep (se 1 (by rfl) ⟨2295458, by rfl⟩ : syracuseStep 3060611 = 4590917) B4590917
theorem B2040407 : Blo 2039435 2040407 := bstep (se 1 (by rfl) ⟨1530305, by rfl⟩ : syracuseStep 2040407 = 3060611) B3060611
theorem B6536693 : Blo 2039435 6536693 := bbase (se 5 (by rfl) ⟨306407, by rfl⟩ : syracuseStep 6536693 = 612815) (by norm_num)
theorem B4357795 : Blo 2039435 4357795 := bstep (se 1 (by rfl) ⟨3268346, by rfl⟩ : syracuseStep 4357795 = 6536693) B6536693
theorem B5810393 : Blo 2039435 5810393 := bstep (se 2 (by rfl) ⟨2178897, by rfl⟩ : syracuseStep 5810393 = 4357795) B4357795
theorem B3873595 : Blo 2039435 3873595 := bstep (se 1 (by rfl) ⟨2905196, by rfl⟩ : syracuseStep 3873595 = 5810393) B5810393
theorem B5164793 : Blo 2039435 5164793 := bstep (se 2 (by rfl) ⟨1936797, by rfl⟩ : syracuseStep 5164793 = 3873595) B3873595
theorem B3443195 : Blo 2039435 3443195 := bstep (se 1 (by rfl) ⟨2582396, by rfl⟩ : syracuseStep 3443195 = 5164793) B5164793
theorem B2295463 : Blo 2039435 2295463 := bstep (se 1 (by rfl) ⟨1721597, by rfl⟩ : syracuseStep 2295463 = 3443195) B3443195
theorem B3060617 : Blo 2039435 3060617 := bstep (se 2 (by rfl) ⟨1147731, by rfl⟩ : syracuseStep 3060617 = 2295463) B2295463
theorem B2040411 : Blo 2039435 2040411 := bstep (se 1 (by rfl) ⟨1530308, by rfl⟩ : syracuseStep 2040411 = 3060617) B3060617
theorem B10329605 : Blo 2039435 10329605 := bbase (se 4 (by rfl) ⟨968400, by rfl⟩ : syracuseStep 10329605 = 1936801) (by norm_num)
theorem B6886403 : Blo 2039435 6886403 := bstep (se 1 (by rfl) ⟨5164802, by rfl⟩ : syracuseStep 6886403 = 10329605) B10329605
theorem B4590935 : Blo 2039435 4590935 := bstep (se 1 (by rfl) ⟨3443201, by rfl⟩ : syracuseStep 4590935 = 6886403) B6886403
theorem B3060623 : Blo 2039435 3060623 := bstep (se 1 (by rfl) ⟨2295467, by rfl⟩ : syracuseStep 3060623 = 4590935) B4590935
theorem B2040415 : Blo 2039435 2040415 := bstep (se 1 (by rfl) ⟨1530311, by rfl⟩ : syracuseStep 2040415 = 3060623) B3060623
theorem B3060629 : Blo 2039435 3060629 := bbase (se 6 (by rfl) ⟨71733, by rfl⟩ : syracuseStep 3060629 = 143467) (by norm_num)
theorem B2040419 : Blo 2039435 2040419 := bstep (se 1 (by rfl) ⟨1530314, by rfl⟩ : syracuseStep 2040419 = 3060629) B3060629
theorem B11620853 : Blo 2039435 11620853 := bbase (se 5 (by rfl) ⟨544727, by rfl⟩ : syracuseStep 11620853 = 1089455) (by norm_num)
theorem B7747235 : Blo 2039435 7747235 := bstep (se 1 (by rfl) ⟨5810426, by rfl⟩ : syracuseStep 7747235 = 11620853) B11620853
theorem B5164823 : Blo 2039435 5164823 := bstep (se 1 (by rfl) ⟨3873617, by rfl⟩ : syracuseStep 5164823 = 7747235) B7747235
theorem B3443215 : Blo 2039435 3443215 := bstep (se 1 (by rfl) ⟨2582411, by rfl⟩ : syracuseStep 3443215 = 5164823) B5164823
theorem B4590953 : Blo 2039435 4590953 := bstep (se 2 (by rfl) ⟨1721607, by rfl⟩ : syracuseStep 4590953 = 3443215) B3443215
theorem B3060635 : Blo 2039435 3060635 := bstep (se 1 (by rfl) ⟨2295476, by rfl⟩ : syracuseStep 3060635 = 4590953) B4590953
theorem B2040423 : Blo 2039435 2040423 := bstep (se 1 (by rfl) ⟨1530317, by rfl⟩ : syracuseStep 2040423 = 3060635) B3060635
theorem B2295481 : Blo 2039435 2295481 := bbase (se 2 (by rfl) ⟨860805, by rfl⟩ : syracuseStep 2295481 = 1721611) (by norm_num)
theorem B3060641 : Blo 2039435 3060641 := bstep (se 2 (by rfl) ⟨1147740, by rfl⟩ : syracuseStep 3060641 = 2295481) B2295481
theorem B2040427 : Blo 2039435 2040427 := bstep (se 1 (by rfl) ⟨1530320, by rfl⟩ : syracuseStep 2040427 = 3060641) B3060641
theorem B4357837 : Blo 2039435 4357837 := bbase (se 3 (by rfl) ⟨817094, by rfl⟩ : syracuseStep 4357837 = 1634189) (by norm_num)
theorem B5810449 : Blo 2039435 5810449 := bstep (se 2 (by rfl) ⟨2178918, by rfl⟩ : syracuseStep 5810449 = 4357837) B4357837
theorem B7747265 : Blo 2039435 7747265 := bstep (se 2 (by rfl) ⟨2905224, by rfl⟩ : syracuseStep 7747265 = 5810449) B5810449
theorem B5164843 : Blo 2039435 5164843 := bstep (se 1 (by rfl) ⟨3873632, by rfl⟩ : syracuseStep 5164843 = 7747265) B7747265
theorem B6886457 : Blo 2039435 6886457 := bstep (se 2 (by rfl) ⟨2582421, by rfl⟩ : syracuseStep 6886457 = 5164843) B5164843
theorem B4590971 : Blo 2039435 4590971 := bstep (se 1 (by rfl) ⟨3443228, by rfl⟩ : syracuseStep 4590971 = 6886457) B6886457
theorem B3060647 : Blo 2039435 3060647 := bstep (se 1 (by rfl) ⟨2295485, by rfl⟩ : syracuseStep 3060647 = 4590971) B4590971
theorem B2040431 : Blo 2039435 2040431 := bstep (se 1 (by rfl) ⟨1530323, by rfl⟩ : syracuseStep 2040431 = 3060647) B3060647
theorem B3060653 : Blo 2039435 3060653 := bbase (se 3 (by rfl) ⟨573872, by rfl⟩ : syracuseStep 3060653 = 1147745) (by norm_num)
theorem B2040435 : Blo 2039435 2040435 := bstep (se 1 (by rfl) ⟨1530326, by rfl⟩ : syracuseStep 2040435 = 3060653) B3060653
theorem B4590989 : Blo 2039435 4590989 := bbase (se 3 (by rfl) ⟨860810, by rfl⟩ : syracuseStep 4590989 = 1721621) (by norm_num)
theorem B3060659 : Blo 2039435 3060659 := bstep (se 1 (by rfl) ⟨2295494, by rfl⟩ : syracuseStep 3060659 = 4590989) B4590989
theorem B2040439 : Blo 2039435 2040439 := bstep (se 1 (by rfl) ⟨1530329, by rfl⟩ : syracuseStep 2040439 = 3060659) B3060659
theorem B2582437 : Blo 2039435 2582437 := bbase (se 4 (by rfl) ⟨242103, by rfl⟩ : syracuseStep 2582437 = 484207) (by norm_num)
theorem B3443249 : Blo 2039435 3443249 := bstep (se 2 (by rfl) ⟨1291218, by rfl⟩ : syracuseStep 3443249 = 2582437) B2582437
theorem B2295499 : Blo 2039435 2295499 := bstep (se 1 (by rfl) ⟨1721624, by rfl⟩ : syracuseStep 2295499 = 3443249) B3443249
theorem B3060665 : Blo 2039435 3060665 := bstep (se 2 (by rfl) ⟨1147749, by rfl⟩ : syracuseStep 3060665 = 2295499) B2295499
theorem B2040443 : Blo 2039435 2040443 := bstep (se 1 (by rfl) ⟨1530332, by rfl⟩ : syracuseStep 2040443 = 3060665) B3060665
theorem B4136573 : Blo 2039435 4136573 := bbase (se 3 (by rfl) ⟨775607, by rfl⟩ : syracuseStep 4136573 = 1551215) (by norm_num)
theorem B11030861 : Blo 2039435 11030861 := bstep (se 3 (by rfl) ⟨2068286, by rfl⟩ : syracuseStep 11030861 = 4136573) B4136573
theorem B29415629 : Blo 2039435 29415629 := bstep (se 3 (by rfl) ⟨5515430, by rfl⟩ : syracuseStep 29415629 = 11030861) B11030861
theorem B19610419 : Blo 2039435 19610419 := bstep (se 1 (by rfl) ⟨14707814, by rfl⟩ : syracuseStep 19610419 = 29415629) B29415629
theorem B26147225 : Blo 2039435 26147225 := bstep (se 2 (by rfl) ⟨9805209, by rfl⟩ : syracuseStep 26147225 = 19610419) B19610419
theorem B17431483 : Blo 2039435 17431483 := bstep (se 1 (by rfl) ⟨13073612, by rfl⟩ : syracuseStep 17431483 = 26147225) B26147225
theorem B23241977 : Blo 2039435 23241977 := bstep (se 2 (by rfl) ⟨8715741, by rfl⟩ : syracuseStep 23241977 = 17431483) B17431483
theorem B15494651 : Blo 2039435 15494651 := bstep (se 1 (by rfl) ⟨11620988, by rfl⟩ : syracuseStep 15494651 = 23241977) B23241977
theorem B10329767 : Blo 2039435 10329767 := bstep (se 1 (by rfl) ⟨7747325, by rfl⟩ : syracuseStep 10329767 = 15494651) B15494651
theorem B6886511 : Blo 2039435 6886511 := bstep (se 1 (by rfl) ⟨5164883, by rfl⟩ : syracuseStep 6886511 = 10329767) B10329767
theorem B4591007 : Blo 2039435 4591007 := bstep (se 1 (by rfl) ⟨3443255, by rfl⟩ : syracuseStep 4591007 = 6886511) B6886511
theorem B3060671 : Blo 2039435 3060671 := bstep (se 1 (by rfl) ⟨2295503, by rfl⟩ : syracuseStep 3060671 = 4591007) B4591007
theorem B2040447 : Blo 2039435 2040447 := bstep (se 1 (by rfl) ⟨1530335, by rfl⟩ : syracuseStep 2040447 = 3060671) B3060671
theorem B3060677 : Blo 2039435 3060677 := bbase (se 4 (by rfl) ⟨286938, by rfl⟩ : syracuseStep 3060677 = 573877) (by norm_num)
theorem B2040451 : Blo 2039435 2040451 := bstep (se 1 (by rfl) ⟨1530338, by rfl⟩ : syracuseStep 2040451 = 3060677) B3060677
theorem B3443269 : Blo 2039435 3443269 := bbase (se 4 (by rfl) ⟨322806, by rfl⟩ : syracuseStep 3443269 = 645613) (by norm_num)
theorem B4591025 : Blo 2039435 4591025 := bstep (se 2 (by rfl) ⟨1721634, by rfl⟩ : syracuseStep 4591025 = 3443269) B3443269
theorem B3060683 : Blo 2039435 3060683 := bstep (se 1 (by rfl) ⟨2295512, by rfl⟩ : syracuseStep 3060683 = 4591025) B4591025
theorem B2040455 : Blo 2039435 2040455 := bstep (se 1 (by rfl) ⟨1530341, by rfl⟩ : syracuseStep 2040455 = 3060683) B3060683
theorem B2295517 : Blo 2039435 2295517 := bbase (se 3 (by rfl) ⟨430409, by rfl⟩ : syracuseStep 2295517 = 860819) (by norm_num)
theorem B3060689 : Blo 2039435 3060689 := bstep (se 2 (by rfl) ⟨1147758, by rfl⟩ : syracuseStep 3060689 = 2295517) B2295517
theorem B2040459 : Blo 2039435 2040459 := bstep (se 1 (by rfl) ⟨1530344, by rfl⟩ : syracuseStep 2040459 = 3060689) B3060689
theorem B6886565 : Blo 2039435 6886565 := bbase (se 4 (by rfl) ⟨645615, by rfl⟩ : syracuseStep 6886565 = 1291231) (by norm_num)
theorem B4591043 : Blo 2039435 4591043 := bstep (se 1 (by rfl) ⟨3443282, by rfl⟩ : syracuseStep 4591043 = 6886565) B6886565
theorem B3060695 : Blo 2039435 3060695 := bstep (se 1 (by rfl) ⟨2295521, by rfl⟩ : syracuseStep 3060695 = 4591043) B4591043
theorem B2040463 : Blo 2039435 2040463 := bstep (se 1 (by rfl) ⟨1530347, by rfl⟩ : syracuseStep 2040463 = 3060695) B3060695
theorem B3060701 : Blo 2039435 3060701 := bbase (se 3 (by rfl) ⟨573881, by rfl⟩ : syracuseStep 3060701 = 1147763) (by norm_num)
theorem B2040467 : Blo 2039435 2040467 := bstep (se 1 (by rfl) ⟨1530350, by rfl⟩ : syracuseStep 2040467 = 3060701) B3060701
theorem B4591061 : Blo 2039435 4591061 := bbase (se 7 (by rfl) ⟨53801, by rfl⟩ : syracuseStep 4591061 = 107603) (by norm_num)
theorem B3060707 : Blo 2039435 3060707 := bstep (se 1 (by rfl) ⟨2295530, by rfl⟩ : syracuseStep 3060707 = 4591061) B4591061
theorem B2040471 : Blo 2039435 2040471 := bstep (se 1 (by rfl) ⟨1530353, by rfl⟩ : syracuseStep 2040471 = 3060707) B3060707
theorem B3677005 : Blo 2039435 3677005 := bbase (se 3 (by rfl) ⟨689438, by rfl⟩ : syracuseStep 3677005 = 1378877) (by norm_num)
theorem B19610693 : Blo 2039435 19610693 := bstep (se 4 (by rfl) ⟨1838502, by rfl⟩ : syracuseStep 19610693 = 3677005) B3677005
theorem B13073795 : Blo 2039435 13073795 := bstep (se 1 (by rfl) ⟨9805346, by rfl⟩ : syracuseStep 13073795 = 19610693) B19610693
theorem B8715863 : Blo 2039435 8715863 := bstep (se 1 (by rfl) ⟨6536897, by rfl⟩ : syracuseStep 8715863 = 13073795) B13073795
theorem B5810575 : Blo 2039435 5810575 := bstep (se 1 (by rfl) ⟨4357931, by rfl⟩ : syracuseStep 5810575 = 8715863) B8715863
theorem B7747433 : Blo 2039435 7747433 := bstep (se 2 (by rfl) ⟨2905287, by rfl⟩ : syracuseStep 7747433 = 5810575) B5810575
theorem B5164955 : Blo 2039435 5164955 := bstep (se 1 (by rfl) ⟨3873716, by rfl⟩ : syracuseStep 5164955 = 7747433) B7747433
theorem B3443303 : Blo 2039435 3443303 := bstep (se 1 (by rfl) ⟨2582477, by rfl⟩ : syracuseStep 3443303 = 5164955) B5164955
theorem B2295535 : Blo 2039435 2295535 := bstep (se 1 (by rfl) ⟨1721651, by rfl⟩ : syracuseStep 2295535 = 3443303) B3443303
theorem B3060713 : Blo 2039435 3060713 := bstep (se 2 (by rfl) ⟨1147767, by rfl⟩ : syracuseStep 3060713 = 2295535) B2295535
theorem B2040475 : Blo 2039435 2040475 := bstep (se 1 (by rfl) ⟨1530356, by rfl⟩ : syracuseStep 2040475 = 3060713) B3060713
theorem B2451341 : Blo 2039435 2451341 := bbase (se 3 (by rfl) ⟨459626, by rfl⟩ : syracuseStep 2451341 = 919253) (by norm_num)
theorem B6536909 : Blo 2039435 6536909 := bstep (se 3 (by rfl) ⟨1225670, by rfl⟩ : syracuseStep 6536909 = 2451341) B2451341
theorem B17431757 : Blo 2039435 17431757 := bstep (se 3 (by rfl) ⟨3268454, by rfl⟩ : syracuseStep 17431757 = 6536909) B6536909
theorem B11621171 : Blo 2039435 11621171 := bstep (se 1 (by rfl) ⟨8715878, by rfl⟩ : syracuseStep 11621171 = 17431757) B17431757
theorem B7747447 : Blo 2039435 7747447 := bstep (se 1 (by rfl) ⟨5810585, by rfl⟩ : syracuseStep 7747447 = 11621171) B11621171
theorem B10329929 : Blo 2039435 10329929 := bstep (se 2 (by rfl) ⟨3873723, by rfl⟩ : syracuseStep 10329929 = 7747447) B7747447
theorem B6886619 : Blo 2039435 6886619 := bstep (se 1 (by rfl) ⟨5164964, by rfl⟩ : syracuseStep 6886619 = 10329929) B10329929
theorem B4591079 : Blo 2039435 4591079 := bstep (se 1 (by rfl) ⟨3443309, by rfl⟩ : syracuseStep 4591079 = 6886619) B6886619
theorem B3060719 : Blo 2039435 3060719 := bstep (se 1 (by rfl) ⟨2295539, by rfl⟩ : syracuseStep 3060719 = 4591079) B4591079
theorem B2040479 : Blo 2039435 2040479 := bstep (se 1 (by rfl) ⟨1530359, by rfl⟩ : syracuseStep 2040479 = 3060719) B3060719
theorem B3060725 : Blo 2039435 3060725 := bbase (se 5 (by rfl) ⟨143471, by rfl⟩ : syracuseStep 3060725 = 286943) (by norm_num)
theorem B2040483 : Blo 2039435 2040483 := bstep (se 1 (by rfl) ⟨1530362, by rfl⟩ : syracuseStep 2040483 = 3060725) B3060725
theorem B4357957 : Blo 2039435 4357957 := bbase (se 4 (by rfl) ⟨408558, by rfl⟩ : syracuseStep 4357957 = 817117) (by norm_num)
theorem B5810609 : Blo 2039435 5810609 := bstep (se 2 (by rfl) ⟨2178978, by rfl⟩ : syracuseStep 5810609 = 4357957) B4357957
theorem B3873739 : Blo 2039435 3873739 := bstep (se 1 (by rfl) ⟨2905304, by rfl⟩ : syracuseStep 3873739 = 5810609) B5810609
theorem B5164985 : Blo 2039435 5164985 := bstep (se 2 (by rfl) ⟨1936869, by rfl⟩ : syracuseStep 5164985 = 3873739) B3873739
theorem B3443323 : Blo 2039435 3443323 := bstep (se 1 (by rfl) ⟨2582492, by rfl⟩ : syracuseStep 3443323 = 5164985) B5164985
theorem B4591097 : Blo 2039435 4591097 := bstep (se 2 (by rfl) ⟨1721661, by rfl⟩ : syracuseStep 4591097 = 3443323) B3443323
theorem B3060731 : Blo 2039435 3060731 := bstep (se 1 (by rfl) ⟨2295548, by rfl⟩ : syracuseStep 3060731 = 4591097) B4591097
theorem B2040487 : Blo 2039435 2040487 := bstep (se 1 (by rfl) ⟨1530365, by rfl⟩ : syracuseStep 2040487 = 3060731) B3060731
theorem B2295553 : Blo 2039435 2295553 := bbase (se 2 (by rfl) ⟨860832, by rfl⟩ : syracuseStep 2295553 = 1721665) (by norm_num)
theorem B3060737 : Blo 2039435 3060737 := bstep (se 2 (by rfl) ⟨1147776, by rfl⟩ : syracuseStep 3060737 = 2295553) B2295553
theorem B2040491 : Blo 2039435 2040491 := bstep (se 1 (by rfl) ⟨1530368, by rfl⟩ : syracuseStep 2040491 = 3060737) B3060737
theorem B5165005 : Blo 2039435 5165005 := bbase (se 3 (by rfl) ⟨968438, by rfl⟩ : syracuseStep 5165005 = 1936877) (by norm_num)
theorem B6886673 : Blo 2039435 6886673 := bstep (se 2 (by rfl) ⟨2582502, by rfl⟩ : syracuseStep 6886673 = 5165005) B5165005
theorem B4591115 : Blo 2039435 4591115 := bstep (se 1 (by rfl) ⟨3443336, by rfl⟩ : syracuseStep 4591115 = 6886673) B6886673
theorem B3060743 : Blo 2039435 3060743 := bstep (se 1 (by rfl) ⟨2295557, by rfl⟩ : syracuseStep 3060743 = 4591115) B4591115
theorem B2040495 : Blo 2039435 2040495 := bstep (se 1 (by rfl) ⟨1530371, by rfl⟩ : syracuseStep 2040495 = 3060743) B3060743
theorem B3060749 : Blo 2039435 3060749 := bbase (se 3 (by rfl) ⟨573890, by rfl⟩ : syracuseStep 3060749 = 1147781) (by norm_num)
theorem B2040499 : Blo 2039435 2040499 := bstep (se 1 (by rfl) ⟨1530374, by rfl⟩ : syracuseStep 2040499 = 3060749) B3060749
theorem B4591133 : Blo 2039435 4591133 := bbase (se 3 (by rfl) ⟨860837, by rfl⟩ : syracuseStep 4591133 = 1721675) (by norm_num)
theorem B3060755 : Blo 2039435 3060755 := bstep (se 1 (by rfl) ⟨2295566, by rfl⟩ : syracuseStep 3060755 = 4591133) B4591133
theorem B2040503 : Blo 2039435 2040503 := bstep (se 1 (by rfl) ⟨1530377, by rfl⟩ : syracuseStep 2040503 = 3060755) B3060755
theorem B3443357 : Blo 2039435 3443357 := bbase (se 3 (by rfl) ⟨645629, by rfl⟩ : syracuseStep 3443357 = 1291259) (by norm_num)
theorem B2295571 : Blo 2039435 2295571 := bstep (se 1 (by rfl) ⟨1721678, by rfl⟩ : syracuseStep 2295571 = 3443357) B3443357
theorem B3060761 : Blo 2039435 3060761 := bstep (se 2 (by rfl) ⟨1147785, by rfl⟩ : syracuseStep 3060761 = 2295571) B2295571
theorem B2040507 : Blo 2039435 2040507 := bstep (se 1 (by rfl) ⟨1530380, by rfl⟩ : syracuseStep 2040507 = 3060761) B3060761
theorem B2985157 : Blo 2039435 2985157 := bbase (se 4 (by rfl) ⟨279858, by rfl⟩ : syracuseStep 2985157 = 559717) (by norm_num)
theorem B3980209 : Blo 2039435 3980209 := bstep (se 2 (by rfl) ⟨1492578, by rfl⟩ : syracuseStep 3980209 = 2985157) B2985157
theorem B5306945 : Blo 2039435 5306945 := bstep (se 2 (by rfl) ⟨1990104, by rfl⟩ : syracuseStep 5306945 = 3980209) B3980209
theorem B14151853 : Blo 2039435 14151853 := bstep (se 3 (by rfl) ⟨2653472, by rfl⟩ : syracuseStep 14151853 = 5306945) B5306945
theorem B75476549 : Blo 2039435 75476549 := bstep (se 4 (by rfl) ⟨7075926, by rfl⟩ : syracuseStep 75476549 = 14151853) B14151853
theorem B50317699 : Blo 2039435 50317699 := bstep (se 1 (by rfl) ⟨37738274, by rfl⟩ : syracuseStep 50317699 = 75476549) B75476549
theorem B67090265 : Blo 2039435 67090265 := bstep (se 2 (by rfl) ⟨25158849, by rfl⟩ : syracuseStep 67090265 = 50317699) B50317699
theorem B44726843 : Blo 2039435 44726843 := bstep (se 1 (by rfl) ⟨33545132, by rfl⟩ : syracuseStep 44726843 = 67090265) B67090265
theorem B29817895 : Blo 2039435 29817895 := bstep (se 1 (by rfl) ⟨22363421, by rfl⟩ : syracuseStep 29817895 = 44726843) B44726843
theorem B39757193 : Blo 2039435 39757193 := bstep (se 2 (by rfl) ⟨14908947, by rfl⟩ : syracuseStep 39757193 = 29817895) B29817895
theorem B26504795 : Blo 2039435 26504795 := bstep (se 1 (by rfl) ⟨19878596, by rfl⟩ : syracuseStep 26504795 = 39757193) B39757193
theorem B17669863 : Blo 2039435 17669863 := bstep (se 1 (by rfl) ⟨13252397, by rfl⟩ : syracuseStep 17669863 = 26504795) B26504795
theorem B23559817 : Blo 2039435 23559817 := bstep (se 2 (by rfl) ⟨8834931, by rfl⟩ : syracuseStep 23559817 = 17669863) B17669863
theorem B31413089 : Blo 2039435 31413089 := bstep (se 2 (by rfl) ⟨11779908, by rfl⟩ : syracuseStep 31413089 = 23559817) B23559817
theorem B20942059 : Blo 2039435 20942059 := bstep (se 1 (by rfl) ⟨15706544, by rfl⟩ : syracuseStep 20942059 = 31413089) B31413089
theorem B27922745 : Blo 2039435 27922745 := bstep (se 2 (by rfl) ⟨10471029, by rfl⟩ : syracuseStep 27922745 = 20942059) B20942059
theorem B74460653 : Blo 2039435 74460653 := bstep (se 3 (by rfl) ⟨13961372, by rfl⟩ : syracuseStep 74460653 = 27922745) B27922745
theorem B49640435 : Blo 2039435 49640435 := bstep (se 1 (by rfl) ⟨37230326, by rfl⟩ : syracuseStep 49640435 = 74460653) B74460653
theorem B33093623 : Blo 2039435 33093623 := bstep (se 1 (by rfl) ⟨24820217, by rfl⟩ : syracuseStep 33093623 = 49640435) B49640435
theorem B22062415 : Blo 2039435 22062415 := bstep (se 1 (by rfl) ⟨16546811, by rfl⟩ : syracuseStep 22062415 = 33093623) B33093623
theorem B29416553 : Blo 2039435 29416553 := bstep (se 2 (by rfl) ⟨11031207, by rfl⟩ : syracuseStep 29416553 = 22062415) B22062415
theorem B19611035 : Blo 2039435 19611035 := bstep (se 1 (by rfl) ⟨14708276, by rfl⟩ : syracuseStep 19611035 = 29416553) B29416553
theorem B13074023 : Blo 2039435 13074023 := bstep (se 1 (by rfl) ⟨9805517, by rfl⟩ : syracuseStep 13074023 = 19611035) B19611035
theorem B8716015 : Blo 2039435 8716015 := bstep (se 1 (by rfl) ⟨6537011, by rfl⟩ : syracuseStep 8716015 = 13074023) B13074023
theorem B11621353 : Blo 2039435 11621353 := bstep (se 2 (by rfl) ⟨4358007, by rfl⟩ : syracuseStep 11621353 = 8716015) B8716015
theorem B15495137 : Blo 2039435 15495137 := bstep (se 2 (by rfl) ⟨5810676, by rfl⟩ : syracuseStep 15495137 = 11621353) B11621353
theorem B10330091 : Blo 2039435 10330091 := bstep (se 1 (by rfl) ⟨7747568, by rfl⟩ : syracuseStep 10330091 = 15495137) B15495137
theorem B6886727 : Blo 2039435 6886727 := bstep (se 1 (by rfl) ⟨5165045, by rfl⟩ : syracuseStep 6886727 = 10330091) B10330091
theorem B4591151 : Blo 2039435 4591151 := bstep (se 1 (by rfl) ⟨3443363, by rfl⟩ : syracuseStep 4591151 = 6886727) B6886727
theorem B3060767 : Blo 2039435 3060767 := bstep (se 1 (by rfl) ⟨2295575, by rfl⟩ : syracuseStep 3060767 = 4591151) B4591151
theorem B2040511 : Blo 2039435 2040511 := bstep (se 1 (by rfl) ⟨1530383, by rfl⟩ : syracuseStep 2040511 = 3060767) B3060767
theorem B3060773 : Blo 2039435 3060773 := bbase (se 4 (by rfl) ⟨286947, by rfl⟩ : syracuseStep 3060773 = 573895) (by norm_num)
theorem B2040515 : Blo 2039435 2040515 := bstep (se 1 (by rfl) ⟨1530386, by rfl⟩ : syracuseStep 2040515 = 3060773) B3060773
theorem B2582533 : Blo 2039435 2582533 := bbase (se 4 (by rfl) ⟨242112, by rfl⟩ : syracuseStep 2582533 = 484225) (by norm_num)
theorem B3443377 : Blo 2039435 3443377 := bstep (se 2 (by rfl) ⟨1291266, by rfl⟩ : syracuseStep 3443377 = 2582533) B2582533
theorem B4591169 : Blo 2039435 4591169 := bstep (se 2 (by rfl) ⟨1721688, by rfl⟩ : syracuseStep 4591169 = 3443377) B3443377
theorem B3060779 : Blo 2039435 3060779 := bstep (se 1 (by rfl) ⟨2295584, by rfl⟩ : syracuseStep 3060779 = 4591169) B4591169
theorem B2040519 : Blo 2039435 2040519 := bstep (se 1 (by rfl) ⟨1530389, by rfl⟩ : syracuseStep 2040519 = 3060779) B3060779
theorem B2295589 : Blo 2039435 2295589 := bbase (se 4 (by rfl) ⟨215211, by rfl⟩ : syracuseStep 2295589 = 430423) (by norm_num)
theorem B3060785 : Blo 2039435 3060785 := bstep (se 2 (by rfl) ⟨1147794, by rfl⟩ : syracuseStep 3060785 = 2295589) B2295589
theorem B2040523 : Blo 2039435 2040523 := bstep (se 1 (by rfl) ⟨1530392, by rfl⟩ : syracuseStep 2040523 = 3060785) B3060785
theorem B8716085 : Blo 2039435 8716085 := bbase (se 5 (by rfl) ⟨408566, by rfl⟩ : syracuseStep 8716085 = 817133) (by norm_num)
theorem B5810723 : Blo 2039435 5810723 := bstep (se 1 (by rfl) ⟨4358042, by rfl⟩ : syracuseStep 5810723 = 8716085) B8716085
theorem B3873815 : Blo 2039435 3873815 := bstep (se 1 (by rfl) ⟨2905361, by rfl⟩ : syracuseStep 3873815 = 5810723) B5810723
theorem B2582543 : Blo 2039435 2582543 := bstep (se 1 (by rfl) ⟨1936907, by rfl⟩ : syracuseStep 2582543 = 3873815) B3873815
theorem B6886781 : Blo 2039435 6886781 := bstep (se 3 (by rfl) ⟨1291271, by rfl⟩ : syracuseStep 6886781 = 2582543) B2582543
theorem B4591187 : Blo 2039435 4591187 := bstep (se 1 (by rfl) ⟨3443390, by rfl⟩ : syracuseStep 4591187 = 6886781) B6886781
theorem B3060791 : Blo 2039435 3060791 := bstep (se 1 (by rfl) ⟨2295593, by rfl⟩ : syracuseStep 3060791 = 4591187) B4591187
theorem B2040527 : Blo 2039435 2040527 := bstep (se 1 (by rfl) ⟨1530395, by rfl⟩ : syracuseStep 2040527 = 3060791) B3060791
theorem B3060797 : Blo 2039435 3060797 := bbase (se 3 (by rfl) ⟨573899, by rfl⟩ : syracuseStep 3060797 = 1147799) (by norm_num)
theorem B2040531 : Blo 2039435 2040531 := bstep (se 1 (by rfl) ⟨1530398, by rfl⟩ : syracuseStep 2040531 = 3060797) B3060797
theorem B4591205 : Blo 2039435 4591205 := bbase (se 4 (by rfl) ⟨430425, by rfl⟩ : syracuseStep 4591205 = 860851) (by norm_num)
theorem B3060803 : Blo 2039435 3060803 := bstep (se 1 (by rfl) ⟨2295602, by rfl⟩ : syracuseStep 3060803 = 4591205) B4591205
theorem B2040535 : Blo 2039435 2040535 := bstep (se 1 (by rfl) ⟨1530401, by rfl⟩ : syracuseStep 2040535 = 3060803) B3060803
theorem B5165117 : Blo 2039435 5165117 := bbase (se 3 (by rfl) ⟨968459, by rfl⟩ : syracuseStep 5165117 = 1936919) (by norm_num)
theorem B3443411 : Blo 2039435 3443411 := bstep (se 1 (by rfl) ⟨2582558, by rfl⟩ : syracuseStep 3443411 = 5165117) B5165117
theorem B2295607 : Blo 2039435 2295607 := bstep (se 1 (by rfl) ⟨1721705, by rfl⟩ : syracuseStep 2295607 = 3443411) B3443411
theorem B3060809 : Blo 2039435 3060809 := bstep (se 2 (by rfl) ⟨1147803, by rfl⟩ : syracuseStep 3060809 = 2295607) B2295607
theorem B2040539 : Blo 2039435 2040539 := bstep (se 1 (by rfl) ⟨1530404, by rfl⟩ : syracuseStep 2040539 = 3060809) B3060809
theorem B3873845 : Blo 2039435 3873845 := bbase (se 5 (by rfl) ⟨181586, by rfl⟩ : syracuseStep 3873845 = 363173) (by norm_num)
theorem B10330253 : Blo 2039435 10330253 := bstep (se 3 (by rfl) ⟨1936922, by rfl⟩ : syracuseStep 10330253 = 3873845) B3873845
theorem B6886835 : Blo 2039435 6886835 := bstep (se 1 (by rfl) ⟨5165126, by rfl⟩ : syracuseStep 6886835 = 10330253) B10330253
theorem B4591223 : Blo 2039435 4591223 := bstep (se 1 (by rfl) ⟨3443417, by rfl⟩ : syracuseStep 4591223 = 6886835) B6886835
theorem B3060815 : Blo 2039435 3060815 := bstep (se 1 (by rfl) ⟨2295611, by rfl⟩ : syracuseStep 3060815 = 4591223) B4591223
theorem B2040543 : Blo 2039435 2040543 := bstep (se 1 (by rfl) ⟨1530407, by rfl⟩ : syracuseStep 2040543 = 3060815) B3060815
theorem B3060821 : Blo 2039435 3060821 := bbase (se 8 (by rfl) ⟨17934, by rfl⟩ : syracuseStep 3060821 = 35869) (by norm_num)
theorem B2040547 : Blo 2039435 2040547 := bstep (se 1 (by rfl) ⟨1530410, by rfl⟩ : syracuseStep 2040547 = 3060821) B3060821
theorem B7853429 : Blo 2039435 7853429 := bbase (se 5 (by rfl) ⟨368129, by rfl⟩ : syracuseStep 7853429 = 736259) (by norm_num)
theorem B5235619 : Blo 2039435 5235619 := bstep (se 1 (by rfl) ⟨3926714, by rfl⟩ : syracuseStep 5235619 = 7853429) B7853429
theorem B6980825 : Blo 2039435 6980825 := bstep (se 2 (by rfl) ⟨2617809, by rfl⟩ : syracuseStep 6980825 = 5235619) B5235619
theorem B4653883 : Blo 2039435 4653883 := bstep (se 1 (by rfl) ⟨3490412, by rfl⟩ : syracuseStep 4653883 = 6980825) B6980825
theorem B6205177 : Blo 2039435 6205177 := bstep (se 2 (by rfl) ⟨2326941, by rfl⟩ : syracuseStep 6205177 = 4653883) B4653883
theorem B33094277 : Blo 2039435 33094277 := bstep (se 4 (by rfl) ⟨3102588, by rfl⟩ : syracuseStep 33094277 = 6205177) B6205177
theorem B22062851 : Blo 2039435 22062851 := bstep (se 1 (by rfl) ⟨16547138, by rfl⟩ : syracuseStep 22062851 = 33094277) B33094277
theorem B14708567 : Blo 2039435 14708567 := bstep (se 1 (by rfl) ⟨11031425, by rfl⟩ : syracuseStep 14708567 = 22062851) B22062851
theorem B9805711 : Blo 2039435 9805711 := bstep (se 1 (by rfl) ⟨7354283, by rfl⟩ : syracuseStep 9805711 = 14708567) B14708567
theorem B13074281 : Blo 2039435 13074281 := bstep (se 2 (by rfl) ⟨4902855, by rfl⟩ : syracuseStep 13074281 = 9805711) B9805711
theorem B8716187 : Blo 2039435 8716187 := bstep (se 1 (by rfl) ⟨6537140, by rfl⟩ : syracuseStep 8716187 = 13074281) B13074281
theorem B5810791 : Blo 2039435 5810791 := bstep (se 1 (by rfl) ⟨4358093, by rfl⟩ : syracuseStep 5810791 = 8716187) B8716187
theorem B7747721 : Blo 2039435 7747721 := bstep (se 2 (by rfl) ⟨2905395, by rfl⟩ : syracuseStep 7747721 = 5810791) B5810791
theorem B5165147 : Blo 2039435 5165147 := bstep (se 1 (by rfl) ⟨3873860, by rfl⟩ : syracuseStep 5165147 = 7747721) B7747721
theorem B3443431 : Blo 2039435 3443431 := bstep (se 1 (by rfl) ⟨2582573, by rfl⟩ : syracuseStep 3443431 = 5165147) B5165147
theorem B4591241 : Blo 2039435 4591241 := bstep (se 2 (by rfl) ⟨1721715, by rfl⟩ : syracuseStep 4591241 = 3443431) B3443431
theorem B3060827 : Blo 2039435 3060827 := bstep (se 1 (by rfl) ⟨2295620, by rfl⟩ : syracuseStep 3060827 = 4591241) B4591241
theorem B2040551 : Blo 2039435 2040551 := bstep (se 1 (by rfl) ⟨1530413, by rfl⟩ : syracuseStep 2040551 = 3060827) B3060827
theorem B2295625 : Blo 2039435 2295625 := bbase (se 2 (by rfl) ⟨860859, by rfl⟩ : syracuseStep 2295625 = 1721719) (by norm_num)
theorem B3060833 : Blo 2039435 3060833 := bstep (se 2 (by rfl) ⟨1147812, by rfl⟩ : syracuseStep 3060833 = 2295625) B2295625
theorem B2040555 : Blo 2039435 2040555 := bstep (se 1 (by rfl) ⟨1530416, by rfl⟩ : syracuseStep 2040555 = 3060833) B3060833
theorem B6626357 : Blo 2039435 6626357 := bbase (se 5 (by rfl) ⟨310610, by rfl⟩ : syracuseStep 6626357 = 621221) (by norm_num)
theorem B4417571 : Blo 2039435 4417571 := bstep (se 1 (by rfl) ⟨3313178, by rfl⟩ : syracuseStep 4417571 = 6626357) B6626357
theorem B2945047 : Blo 2039435 2945047 := bstep (se 1 (by rfl) ⟨2208785, by rfl⟩ : syracuseStep 2945047 = 4417571) B4417571
theorem B3926729 : Blo 2039435 3926729 := bstep (se 2 (by rfl) ⟨1472523, by rfl⟩ : syracuseStep 3926729 = 2945047) B2945047
theorem B10471277 : Blo 2039435 10471277 := bstep (se 3 (by rfl) ⟨1963364, by rfl⟩ : syracuseStep 10471277 = 3926729) B3926729
theorem B6980851 : Blo 2039435 6980851 := bstep (se 1 (by rfl) ⟨5235638, by rfl⟩ : syracuseStep 6980851 = 10471277) B10471277
theorem B9307801 : Blo 2039435 9307801 := bstep (se 2 (by rfl) ⟨3490425, by rfl⟩ : syracuseStep 9307801 = 6980851) B6980851
theorem B49641605 : Blo 2039435 49641605 := bstep (se 4 (by rfl) ⟨4653900, by rfl⟩ : syracuseStep 49641605 = 9307801) B9307801
theorem B33094403 : Blo 2039435 33094403 := bstep (se 1 (by rfl) ⟨24820802, by rfl⟩ : syracuseStep 33094403 = 49641605) B49641605
theorem B22062935 : Blo 2039435 22062935 := bstep (se 1 (by rfl) ⟨16547201, by rfl⟩ : syracuseStep 22062935 = 33094403) B33094403
theorem B14708623 : Blo 2039435 14708623 := bstep (se 1 (by rfl) ⟨11031467, by rfl⟩ : syracuseStep 14708623 = 22062935) B22062935
theorem B19611497 : Blo 2039435 19611497 := bstep (se 2 (by rfl) ⟨7354311, by rfl⟩ : syracuseStep 19611497 = 14708623) B14708623
theorem B13074331 : Blo 2039435 13074331 := bstep (se 1 (by rfl) ⟨9805748, by rfl⟩ : syracuseStep 13074331 = 19611497) B19611497
theorem B17432441 : Blo 2039435 17432441 := bstep (se 2 (by rfl) ⟨6537165, by rfl⟩ : syracuseStep 17432441 = 13074331) B13074331
theorem B11621627 : Blo 2039435 11621627 := bstep (se 1 (by rfl) ⟨8716220, by rfl⟩ : syracuseStep 11621627 = 17432441) B17432441
theorem B7747751 : Blo 2039435 7747751 := bstep (se 1 (by rfl) ⟨5810813, by rfl⟩ : syracuseStep 7747751 = 11621627) B11621627
theorem B5165167 : Blo 2039435 5165167 := bstep (se 1 (by rfl) ⟨3873875, by rfl⟩ : syracuseStep 5165167 = 7747751) B7747751
theorem B6886889 : Blo 2039435 6886889 := bstep (se 2 (by rfl) ⟨2582583, by rfl⟩ : syracuseStep 6886889 = 5165167) B5165167
theorem B4591259 : Blo 2039435 4591259 := bstep (se 1 (by rfl) ⟨3443444, by rfl⟩ : syracuseStep 4591259 = 6886889) B6886889
theorem B3060839 : Blo 2039435 3060839 := bstep (se 1 (by rfl) ⟨2295629, by rfl⟩ : syracuseStep 3060839 = 4591259) B4591259
theorem B2040559 : Blo 2039435 2040559 := bstep (se 1 (by rfl) ⟨1530419, by rfl⟩ : syracuseStep 2040559 = 3060839) B3060839
theorem B3060845 : Blo 2039435 3060845 := bbase (se 3 (by rfl) ⟨573908, by rfl⟩ : syracuseStep 3060845 = 1147817) (by norm_num)
theorem B2040563 : Blo 2039435 2040563 := bstep (se 1 (by rfl) ⟨1530422, by rfl⟩ : syracuseStep 2040563 = 3060845) B3060845
theorem B4591277 : Blo 2039435 4591277 := bbase (se 3 (by rfl) ⟨860864, by rfl⟩ : syracuseStep 4591277 = 1721729) (by norm_num)
theorem B3060851 : Blo 2039435 3060851 := bstep (se 1 (by rfl) ⟨2295638, by rfl⟩ : syracuseStep 3060851 = 4591277) B4591277
theorem B2040567 : Blo 2039435 2040567 := bstep (se 1 (by rfl) ⟨1530425, by rfl⟩ : syracuseStep 2040567 = 3060851) B3060851
theorem B5890133 : Blo 2039435 5890133 := bbase (se 8 (by rfl) ⟨34512, by rfl⟩ : syracuseStep 5890133 = 69025) (by norm_num)
theorem B3926755 : Blo 2039435 3926755 := bstep (se 1 (by rfl) ⟨2945066, by rfl⟩ : syracuseStep 3926755 = 5890133) B5890133
theorem B5235673 : Blo 2039435 5235673 := bstep (se 2 (by rfl) ⟨1963377, by rfl⟩ : syracuseStep 5235673 = 3926755) B3926755
theorem B6980897 : Blo 2039435 6980897 := bstep (se 2 (by rfl) ⟨2617836, by rfl⟩ : syracuseStep 6980897 = 5235673) B5235673
theorem B4653931 : Blo 2039435 4653931 := bstep (se 1 (by rfl) ⟨3490448, by rfl⟩ : syracuseStep 4653931 = 6980897) B6980897
theorem B6205241 : Blo 2039435 6205241 := bstep (se 2 (by rfl) ⟨2326965, by rfl⟩ : syracuseStep 6205241 = 4653931) B4653931
theorem B4136827 : Blo 2039435 4136827 := bstep (se 1 (by rfl) ⟨3102620, by rfl⟩ : syracuseStep 4136827 = 6205241) B6205241
theorem B5515769 : Blo 2039435 5515769 := bstep (se 2 (by rfl) ⟨2068413, by rfl⟩ : syracuseStep 5515769 = 4136827) B4136827
theorem B3677179 : Blo 2039435 3677179 := bstep (se 1 (by rfl) ⟨2757884, by rfl⟩ : syracuseStep 3677179 = 5515769) B5515769
theorem B4902905 : Blo 2039435 4902905 := bstep (se 2 (by rfl) ⟨1838589, by rfl⟩ : syracuseStep 4902905 = 3677179) B3677179
theorem B3268603 : Blo 2039435 3268603 := bstep (se 1 (by rfl) ⟨2451452, by rfl⟩ : syracuseStep 3268603 = 4902905) B4902905
theorem B4358137 : Blo 2039435 4358137 := bstep (se 2 (by rfl) ⟨1634301, by rfl⟩ : syracuseStep 4358137 = 3268603) B3268603
theorem B5810849 : Blo 2039435 5810849 := bstep (se 2 (by rfl) ⟨2179068, by rfl⟩ : syracuseStep 5810849 = 4358137) B4358137
theorem B3873899 : Blo 2039435 3873899 := bstep (se 1 (by rfl) ⟨2905424, by rfl⟩ : syracuseStep 3873899 = 5810849) B5810849
theorem B2582599 : Blo 2039435 2582599 := bstep (se 1 (by rfl) ⟨1936949, by rfl⟩ : syracuseStep 2582599 = 3873899) B3873899
theorem B3443465 : Blo 2039435 3443465 := bstep (se 2 (by rfl) ⟨1291299, by rfl⟩ : syracuseStep 3443465 = 2582599) B2582599
theorem B2295643 : Blo 2039435 2295643 := bstep (se 1 (by rfl) ⟨1721732, by rfl⟩ : syracuseStep 2295643 = 3443465) B3443465
theorem B3060857 : Blo 2039435 3060857 := bstep (se 2 (by rfl) ⟨1147821, by rfl⟩ : syracuseStep 3060857 = 2295643) B2295643
theorem B2040571 : Blo 2039435 2040571 := bstep (se 1 (by rfl) ⟨1530428, by rfl⟩ : syracuseStep 2040571 = 3060857) B3060857
theorem B3490453 : Blo 2039435 3490453 := bbase (se 6 (by rfl) ⟨81807, by rfl⟩ : syracuseStep 3490453 = 163615) (by norm_num)
theorem B4653937 : Blo 2039435 4653937 := bstep (se 2 (by rfl) ⟨1745226, by rfl⟩ : syracuseStep 4653937 = 3490453) B3490453
theorem B6205249 : Blo 2039435 6205249 := bstep (se 2 (by rfl) ⟨2326968, by rfl⟩ : syracuseStep 6205249 = 4653937) B4653937
theorem B8273665 : Blo 2039435 8273665 := bstep (se 2 (by rfl) ⟨3102624, by rfl⟩ : syracuseStep 8273665 = 6205249) B6205249
theorem B11031553 : Blo 2039435 11031553 := bstep (se 2 (by rfl) ⟨4136832, by rfl⟩ : syracuseStep 11031553 = 8273665) B8273665
theorem B14708737 : Blo 2039435 14708737 := bstep (se 2 (by rfl) ⟨5515776, by rfl⟩ : syracuseStep 14708737 = 11031553) B11031553
theorem B19611649 : Blo 2039435 19611649 := bstep (se 2 (by rfl) ⟨7354368, by rfl⟩ : syracuseStep 19611649 = 14708737) B14708737
theorem B26148865 : Blo 2039435 26148865 := bstep (se 2 (by rfl) ⟨9805824, by rfl⟩ : syracuseStep 26148865 = 19611649) B19611649
theorem B34865153 : Blo 2039435 34865153 := bstep (se 2 (by rfl) ⟨13074432, by rfl⟩ : syracuseStep 34865153 = 26148865) B26148865
theorem B23243435 : Blo 2039435 23243435 := bstep (se 1 (by rfl) ⟨17432576, by rfl⟩ : syracuseStep 23243435 = 34865153) B34865153
theorem B15495623 : Blo 2039435 15495623 := bstep (se 1 (by rfl) ⟨11621717, by rfl⟩ : syracuseStep 15495623 = 23243435) B23243435
theorem B10330415 : Blo 2039435 10330415 := bstep (se 1 (by rfl) ⟨7747811, by rfl⟩ : syracuseStep 10330415 = 15495623) B15495623
theorem B6886943 : Blo 2039435 6886943 := bstep (se 1 (by rfl) ⟨5165207, by rfl⟩ : syracuseStep 6886943 = 10330415) B10330415
theorem B4591295 : Blo 2039435 4591295 := bstep (se 1 (by rfl) ⟨3443471, by rfl⟩ : syracuseStep 4591295 = 6886943) B6886943
theorem B3060863 : Blo 2039435 3060863 := bstep (se 1 (by rfl) ⟨2295647, by rfl⟩ : syracuseStep 3060863 = 4591295) B4591295
theorem B2040575 : Blo 2039435 2040575 := bstep (se 1 (by rfl) ⟨1530431, by rfl⟩ : syracuseStep 2040575 = 3060863) B3060863
theorem B3060869 : Blo 2039435 3060869 := bbase (se 4 (by rfl) ⟨286956, by rfl⟩ : syracuseStep 3060869 = 573913) (by norm_num)
theorem B2040579 : Blo 2039435 2040579 := bstep (se 1 (by rfl) ⟨1530434, by rfl⟩ : syracuseStep 2040579 = 3060869) B3060869
theorem B3443485 : Blo 2039435 3443485 := bbase (se 3 (by rfl) ⟨645653, by rfl⟩ : syracuseStep 3443485 = 1291307) (by norm_num)
theorem B4591313 : Blo 2039435 4591313 := bstep (se 2 (by rfl) ⟨1721742, by rfl⟩ : syracuseStep 4591313 = 3443485) B3443485
theorem B3060875 : Blo 2039435 3060875 := bstep (se 1 (by rfl) ⟨2295656, by rfl⟩ : syracuseStep 3060875 = 4591313) B4591313
theorem B2040583 : Blo 2039435 2040583 := bstep (se 1 (by rfl) ⟨1530437, by rfl⟩ : syracuseStep 2040583 = 3060875) B3060875
theorem B2295661 : Blo 2039435 2295661 := bbase (se 3 (by rfl) ⟨430436, by rfl⟩ : syracuseStep 2295661 = 860873) (by norm_num)
theorem B3060881 : Blo 2039435 3060881 := bstep (se 2 (by rfl) ⟨1147830, by rfl⟩ : syracuseStep 3060881 = 2295661) B2295661
theorem B2040587 : Blo 2039435 2040587 := bstep (se 1 (by rfl) ⟨1530440, by rfl⟩ : syracuseStep 2040587 = 3060881) B3060881
theorem B6886997 : Blo 2039435 6886997 := bbase (se 8 (by rfl) ⟨40353, by rfl⟩ : syracuseStep 6886997 = 80707) (by norm_num)
theorem B4591331 : Blo 2039435 4591331 := bstep (se 1 (by rfl) ⟨3443498, by rfl⟩ : syracuseStep 4591331 = 6886997) B6886997
theorem B3060887 : Blo 2039435 3060887 := bstep (se 1 (by rfl) ⟨2295665, by rfl⟩ : syracuseStep 3060887 = 4591331) B4591331
theorem B2040591 : Blo 2039435 2040591 := bstep (se 1 (by rfl) ⟨1530443, by rfl⟩ : syracuseStep 2040591 = 3060887) B3060887
theorem B3060893 : Blo 2039435 3060893 := bbase (se 3 (by rfl) ⟨573917, by rfl⟩ : syracuseStep 3060893 = 1147835) (by norm_num)
theorem B2040595 : Blo 2039435 2040595 := bstep (se 1 (by rfl) ⟨1530446, by rfl⟩ : syracuseStep 2040595 = 3060893) B3060893
theorem B4591349 : Blo 2039435 4591349 := bbase (se 5 (by rfl) ⟨215219, by rfl⟩ : syracuseStep 4591349 = 430439) (by norm_num)
theorem B3060899 : Blo 2039435 3060899 := bstep (se 1 (by rfl) ⟨2295674, by rfl⟩ : syracuseStep 3060899 = 4591349) B4591349
theorem B2040599 : Blo 2039435 2040599 := bstep (se 1 (by rfl) ⟨1530449, by rfl⟩ : syracuseStep 2040599 = 3060899) B3060899
theorem B2208833 : Blo 2039435 2208833 := bbase (se 2 (by rfl) ⟨828312, by rfl⟩ : syracuseStep 2208833 = 1656625) (by norm_num)
theorem B23560885 : Blo 2039435 23560885 := bstep (se 5 (by rfl) ⟨1104416, by rfl⟩ : syracuseStep 23560885 = 2208833) B2208833
theorem B31414513 : Blo 2039435 31414513 := bstep (se 2 (by rfl) ⟨11780442, by rfl⟩ : syracuseStep 31414513 = 23560885) B23560885
theorem B41886017 : Blo 2039435 41886017 := bstep (se 2 (by rfl) ⟨15707256, by rfl⟩ : syracuseStep 41886017 = 31414513) B31414513
theorem B27924011 : Blo 2039435 27924011 := bstep (se 1 (by rfl) ⟨20943008, by rfl⟩ : syracuseStep 27924011 = 41886017) B41886017
theorem B18616007 : Blo 2039435 18616007 := bstep (se 1 (by rfl) ⟨13962005, by rfl⟩ : syracuseStep 18616007 = 27924011) B27924011
theorem B12410671 : Blo 2039435 12410671 := bstep (se 1 (by rfl) ⟨9308003, by rfl⟩ : syracuseStep 12410671 = 18616007) B18616007
theorem B16547561 : Blo 2039435 16547561 := bstep (se 2 (by rfl) ⟨6205335, by rfl⟩ : syracuseStep 16547561 = 12410671) B12410671
theorem B11031707 : Blo 2039435 11031707 := bstep (se 1 (by rfl) ⟨8273780, by rfl⟩ : syracuseStep 11031707 = 16547561) B16547561
theorem B7354471 : Blo 2039435 7354471 := bstep (se 1 (by rfl) ⟨5515853, by rfl⟩ : syracuseStep 7354471 = 11031707) B11031707
theorem B9805961 : Blo 2039435 9805961 := bstep (se 2 (by rfl) ⟨3677235, by rfl⟩ : syracuseStep 9805961 = 7354471) B7354471
theorem B26149229 : Blo 2039435 26149229 := bstep (se 3 (by rfl) ⟨4902980, by rfl⟩ : syracuseStep 26149229 = 9805961) B9805961
theorem B17432819 : Blo 2039435 17432819 := bstep (se 1 (by rfl) ⟨13074614, by rfl⟩ : syracuseStep 17432819 = 26149229) B26149229
theorem B11621879 : Blo 2039435 11621879 := bstep (se 1 (by rfl) ⟨8716409, by rfl⟩ : syracuseStep 11621879 = 17432819) B17432819
theorem B7747919 : Blo 2039435 7747919 := bstep (se 1 (by rfl) ⟨5810939, by rfl⟩ : syracuseStep 7747919 = 11621879) B11621879
theorem B5165279 : Blo 2039435 5165279 := bstep (se 1 (by rfl) ⟨3873959, by rfl⟩ : syracuseStep 5165279 = 7747919) B7747919
theorem B3443519 : Blo 2039435 3443519 := bstep (se 1 (by rfl) ⟨2582639, by rfl⟩ : syracuseStep 3443519 = 5165279) B5165279
theorem B2295679 : Blo 2039435 2295679 := bstep (se 1 (by rfl) ⟨1721759, by rfl⟩ : syracuseStep 2295679 = 3443519) B3443519
theorem B3060905 : Blo 2039435 3060905 := bstep (se 2 (by rfl) ⟨1147839, by rfl⟩ : syracuseStep 3060905 = 2295679) B2295679
theorem B2040603 : Blo 2039435 2040603 := bstep (se 1 (by rfl) ⟨1530452, by rfl⟩ : syracuseStep 2040603 = 3060905) B3060905
theorem B4358213 : Blo 2039435 4358213 := bbase (se 4 (by rfl) ⟨408582, by rfl⟩ : syracuseStep 4358213 = 817165) (by norm_num)
theorem B2905475 : Blo 2039435 2905475 := bstep (se 1 (by rfl) ⟨2179106, by rfl⟩ : syracuseStep 2905475 = 4358213) B4358213
theorem B7747933 : Blo 2039435 7747933 := bstep (se 3 (by rfl) ⟨1452737, by rfl⟩ : syracuseStep 7747933 = 2905475) B2905475
theorem B10330577 : Blo 2039435 10330577 := bstep (se 2 (by rfl) ⟨3873966, by rfl⟩ : syracuseStep 10330577 = 7747933) B7747933
theorem B6887051 : Blo 2039435 6887051 := bstep (se 1 (by rfl) ⟨5165288, by rfl⟩ : syracuseStep 6887051 = 10330577) B10330577
theorem B4591367 : Blo 2039435 4591367 := bstep (se 1 (by rfl) ⟨3443525, by rfl⟩ : syracuseStep 4591367 = 6887051) B6887051
theorem B3060911 : Blo 2039435 3060911 := bstep (se 1 (by rfl) ⟨2295683, by rfl⟩ : syracuseStep 3060911 = 4591367) B4591367
theorem B2040607 : Blo 2039435 2040607 := bstep (se 1 (by rfl) ⟨1530455, by rfl⟩ : syracuseStep 2040607 = 3060911) B3060911
theorem B3060917 : Blo 2039435 3060917 := bbase (se 5 (by rfl) ⟨143480, by rfl⟩ : syracuseStep 3060917 = 286961) (by norm_num)
theorem B2040611 : Blo 2039435 2040611 := bstep (se 1 (by rfl) ⟨1530458, by rfl⟩ : syracuseStep 2040611 = 3060917) B3060917
theorem B5165309 : Blo 2039435 5165309 := bbase (se 3 (by rfl) ⟨968495, by rfl⟩ : syracuseStep 5165309 = 1936991) (by norm_num)
theorem B3443539 : Blo 2039435 3443539 := bstep (se 1 (by rfl) ⟨2582654, by rfl⟩ : syracuseStep 3443539 = 5165309) B5165309
theorem B4591385 : Blo 2039435 4591385 := bstep (se 2 (by rfl) ⟨1721769, by rfl⟩ : syracuseStep 4591385 = 3443539) B3443539
theorem B3060923 : Blo 2039435 3060923 := bstep (se 1 (by rfl) ⟨2295692, by rfl⟩ : syracuseStep 3060923 = 4591385) B4591385
theorem B2040615 : Blo 2039435 2040615 := bstep (se 1 (by rfl) ⟨1530461, by rfl⟩ : syracuseStep 2040615 = 3060923) B3060923
theorem B2295697 : Blo 2039435 2295697 := bbase (se 2 (by rfl) ⟨860886, by rfl⟩ : syracuseStep 2295697 = 1721773) (by norm_num)
theorem B3060929 : Blo 2039435 3060929 := bstep (se 2 (by rfl) ⟨1147848, by rfl⟩ : syracuseStep 3060929 = 2295697) B2295697
theorem B2040619 : Blo 2039435 2040619 := bstep (se 1 (by rfl) ⟨1530464, by rfl⟩ : syracuseStep 2040619 = 3060929) B3060929
theorem B3873997 : Blo 2039435 3873997 := bbase (se 3 (by rfl) ⟨726374, by rfl⟩ : syracuseStep 3873997 = 1452749) (by norm_num)
theorem B5165329 : Blo 2039435 5165329 := bstep (se 2 (by rfl) ⟨1936998, by rfl⟩ : syracuseStep 5165329 = 3873997) B3873997
theorem B6887105 : Blo 2039435 6887105 := bstep (se 2 (by rfl) ⟨2582664, by rfl⟩ : syracuseStep 6887105 = 5165329) B5165329
theorem B4591403 : Blo 2039435 4591403 := bstep (se 1 (by rfl) ⟨3443552, by rfl⟩ : syracuseStep 4591403 = 6887105) B6887105
theorem B3060935 : Blo 2039435 3060935 := bstep (se 1 (by rfl) ⟨2295701, by rfl⟩ : syracuseStep 3060935 = 4591403) B4591403
theorem B2040623 : Blo 2039435 2040623 := bstep (se 1 (by rfl) ⟨1530467, by rfl⟩ : syracuseStep 2040623 = 3060935) B3060935
theorem B3060941 : Blo 2039435 3060941 := bbase (se 3 (by rfl) ⟨573926, by rfl⟩ : syracuseStep 3060941 = 1147853) (by norm_num)
theorem B2040627 : Blo 2039435 2040627 := bstep (se 1 (by rfl) ⟨1530470, by rfl⟩ : syracuseStep 2040627 = 3060941) B3060941
theorem B4591421 : Blo 2039435 4591421 := bbase (se 3 (by rfl) ⟨860891, by rfl⟩ : syracuseStep 4591421 = 1721783) (by norm_num)
theorem B3060947 : Blo 2039435 3060947 := bstep (se 1 (by rfl) ⟨2295710, by rfl⟩ : syracuseStep 3060947 = 4591421) B4591421
theorem B2040631 : Blo 2039435 2040631 := bstep (se 1 (by rfl) ⟨1530473, by rfl⟩ : syracuseStep 2040631 = 3060947) B3060947
theorem B3443573 : Blo 2039435 3443573 := bbase (se 5 (by rfl) ⟨161417, by rfl⟩ : syracuseStep 3443573 = 322835) (by norm_num)
theorem B2295715 : Blo 2039435 2295715 := bstep (se 1 (by rfl) ⟨1721786, by rfl⟩ : syracuseStep 2295715 = 3443573) B3443573
theorem B3060953 : Blo 2039435 3060953 := bstep (se 2 (by rfl) ⟨1147857, by rfl⟩ : syracuseStep 3060953 = 2295715) B2295715
theorem B2040635 : Blo 2039435 2040635 := bstep (se 1 (by rfl) ⟨1530476, by rfl⟩ : syracuseStep 2040635 = 3060953) B3060953
theorem B5235845 : Blo 2039435 5235845 := bbase (se 4 (by rfl) ⟨490860, by rfl⟩ : syracuseStep 5235845 = 981721) (by norm_num)
theorem B13962253 : Blo 2039435 13962253 := bstep (se 3 (by rfl) ⟨2617922, by rfl⟩ : syracuseStep 13962253 = 5235845) B5235845
theorem B18616337 : Blo 2039435 18616337 := bstep (se 2 (by rfl) ⟨6981126, by rfl⟩ : syracuseStep 18616337 = 13962253) B13962253
theorem B12410891 : Blo 2039435 12410891 := bstep (se 1 (by rfl) ⟨9308168, by rfl⟩ : syracuseStep 12410891 = 18616337) B18616337
theorem B8273927 : Blo 2039435 8273927 := bstep (se 1 (by rfl) ⟨6205445, by rfl⟩ : syracuseStep 8273927 = 12410891) B12410891
theorem B5515951 : Blo 2039435 5515951 := bstep (se 1 (by rfl) ⟨4136963, by rfl⟩ : syracuseStep 5515951 = 8273927) B8273927
theorem B7354601 : Blo 2039435 7354601 := bstep (se 2 (by rfl) ⟨2757975, by rfl⟩ : syracuseStep 7354601 = 5515951) B5515951
theorem B4903067 : Blo 2039435 4903067 := bstep (se 1 (by rfl) ⟨3677300, by rfl⟩ : syracuseStep 4903067 = 7354601) B7354601
theorem B3268711 : Blo 2039435 3268711 := bstep (se 1 (by rfl) ⟨2451533, by rfl⟩ : syracuseStep 3268711 = 4903067) B4903067
theorem B4358281 : Blo 2039435 4358281 := bstep (se 2 (by rfl) ⟨1634355, by rfl⟩ : syracuseStep 4358281 = 3268711) B3268711
theorem B5811041 : Blo 2039435 5811041 := bstep (se 2 (by rfl) ⟨2179140, by rfl⟩ : syracuseStep 5811041 = 4358281) B4358281
theorem B15496109 : Blo 2039435 15496109 := bstep (se 3 (by rfl) ⟨2905520, by rfl⟩ : syracuseStep 15496109 = 5811041) B5811041
theorem B10330739 : Blo 2039435 10330739 := bstep (se 1 (by rfl) ⟨7748054, by rfl⟩ : syracuseStep 10330739 = 15496109) B15496109
theorem B6887159 : Blo 2039435 6887159 := bstep (se 1 (by rfl) ⟨5165369, by rfl⟩ : syracuseStep 6887159 = 10330739) B10330739
theorem B4591439 : Blo 2039435 4591439 := bstep (se 1 (by rfl) ⟨3443579, by rfl⟩ : syracuseStep 4591439 = 6887159) B6887159
theorem B3060959 : Blo 2039435 3060959 := bstep (se 1 (by rfl) ⟨2295719, by rfl⟩ : syracuseStep 3060959 = 4591439) B4591439
theorem B2040639 : Blo 2039435 2040639 := bstep (se 1 (by rfl) ⟨1530479, by rfl⟩ : syracuseStep 2040639 = 3060959) B3060959
theorem B3060965 : Blo 2039435 3060965 := bbase (se 4 (by rfl) ⟨286965, by rfl⟩ : syracuseStep 3060965 = 573931) (by norm_num)
theorem B2040643 : Blo 2039435 2040643 := bstep (se 1 (by rfl) ⟨1530482, by rfl⟩ : syracuseStep 2040643 = 3060965) B3060965
theorem B10471733 : Blo 2039435 10471733 := bbase (se 5 (by rfl) ⟨490862, by rfl⟩ : syracuseStep 10471733 = 981725) (by norm_num)
theorem B6981155 : Blo 2039435 6981155 := bstep (se 1 (by rfl) ⟨5235866, by rfl⟩ : syracuseStep 6981155 = 10471733) B10471733
theorem B4654103 : Blo 2039435 4654103 := bstep (se 1 (by rfl) ⟨3490577, by rfl⟩ : syracuseStep 4654103 = 6981155) B6981155
theorem B12410941 : Blo 2039435 12410941 := bstep (se 3 (by rfl) ⟨2327051, by rfl⟩ : syracuseStep 12410941 = 4654103) B4654103
theorem B16547921 : Blo 2039435 16547921 := bstep (se 2 (by rfl) ⟨6205470, by rfl⟩ : syracuseStep 16547921 = 12410941) B12410941
theorem B11031947 : Blo 2039435 11031947 := bstep (se 1 (by rfl) ⟨8273960, by rfl⟩ : syracuseStep 11031947 = 16547921) B16547921
theorem B7354631 : Blo 2039435 7354631 := bstep (se 1 (by rfl) ⟨5515973, by rfl⟩ : syracuseStep 7354631 = 11031947) B11031947
theorem B4903087 : Blo 2039435 4903087 := bstep (se 1 (by rfl) ⟨3677315, by rfl⟩ : syracuseStep 4903087 = 7354631) B7354631
theorem B6537449 : Blo 2039435 6537449 := bstep (se 2 (by rfl) ⟨2451543, by rfl⟩ : syracuseStep 6537449 = 4903087) B4903087
theorem B4358299 : Blo 2039435 4358299 := bstep (se 1 (by rfl) ⟨3268724, by rfl⟩ : syracuseStep 4358299 = 6537449) B6537449
theorem B5811065 : Blo 2039435 5811065 := bstep (se 2 (by rfl) ⟨2179149, by rfl⟩ : syracuseStep 5811065 = 4358299) B4358299
theorem B3874043 : Blo 2039435 3874043 := bstep (se 1 (by rfl) ⟨2905532, by rfl⟩ : syracuseStep 3874043 = 5811065) B5811065
theorem B2582695 : Blo 2039435 2582695 := bstep (se 1 (by rfl) ⟨1937021, by rfl⟩ : syracuseStep 2582695 = 3874043) B3874043
theorem B3443593 : Blo 2039435 3443593 := bstep (se 2 (by rfl) ⟨1291347, by rfl⟩ : syracuseStep 3443593 = 2582695) B2582695
theorem B4591457 : Blo 2039435 4591457 := bstep (se 2 (by rfl) ⟨1721796, by rfl⟩ : syracuseStep 4591457 = 3443593) B3443593
theorem B3060971 : Blo 2039435 3060971 := bstep (se 1 (by rfl) ⟨2295728, by rfl⟩ : syracuseStep 3060971 = 4591457) B4591457
theorem B2040647 : Blo 2039435 2040647 := bstep (se 1 (by rfl) ⟨1530485, by rfl⟩ : syracuseStep 2040647 = 3060971) B3060971
theorem B2295733 : Blo 2039435 2295733 := bbase (se 5 (by rfl) ⟨107612, by rfl⟩ : syracuseStep 2295733 = 215225) (by norm_num)
theorem B3060977 : Blo 2039435 3060977 := bstep (se 2 (by rfl) ⟨1147866, by rfl⟩ : syracuseStep 3060977 = 2295733) B2295733
theorem B2040651 : Blo 2039435 2040651 := bstep (se 1 (by rfl) ⟨1530488, by rfl⟩ : syracuseStep 2040651 = 3060977) B3060977
theorem B2582705 : Blo 2039435 2582705 := bbase (se 2 (by rfl) ⟨968514, by rfl⟩ : syracuseStep 2582705 = 1937029) (by norm_num)
theorem B6887213 : Blo 2039435 6887213 := bstep (se 3 (by rfl) ⟨1291352, by rfl⟩ : syracuseStep 6887213 = 2582705) B2582705
theorem B4591475 : Blo 2039435 4591475 := bstep (se 1 (by rfl) ⟨3443606, by rfl⟩ : syracuseStep 4591475 = 6887213) B6887213
theorem B3060983 : Blo 2039435 3060983 := bstep (se 1 (by rfl) ⟨2295737, by rfl⟩ : syracuseStep 3060983 = 4591475) B4591475
theorem B2040655 : Blo 2039435 2040655 := bstep (se 1 (by rfl) ⟨1530491, by rfl⟩ : syracuseStep 2040655 = 3060983) B3060983
theorem B3060989 : Blo 2039435 3060989 := bbase (se 3 (by rfl) ⟨573935, by rfl⟩ : syracuseStep 3060989 = 1147871) (by norm_num)
theorem B2040659 : Blo 2039435 2040659 := bstep (se 1 (by rfl) ⟨1530494, by rfl⟩ : syracuseStep 2040659 = 3060989) B3060989
theorem B4591493 : Blo 2039435 4591493 := bbase (se 4 (by rfl) ⟨430452, by rfl⟩ : syracuseStep 4591493 = 860905) (by norm_num)
theorem B3060995 : Blo 2039435 3060995 := bstep (se 1 (by rfl) ⟨2295746, by rfl⟩ : syracuseStep 3060995 = 4591493) B4591493
theorem B2040663 : Blo 2039435 2040663 := bstep (se 1 (by rfl) ⟨1530497, by rfl⟩ : syracuseStep 2040663 = 3060995) B3060995
theorem B3268757 : Blo 2039435 3268757 := bbase (se 6 (by rfl) ⟨76611, by rfl⟩ : syracuseStep 3268757 = 153223) (by norm_num)
theorem B2179171 : Blo 2039435 2179171 := bstep (se 1 (by rfl) ⟨1634378, by rfl⟩ : syracuseStep 2179171 = 3268757) B3268757
theorem B2905561 : Blo 2039435 2905561 := bstep (se 2 (by rfl) ⟨1089585, by rfl⟩ : syracuseStep 2905561 = 2179171) B2179171
theorem B3874081 : Blo 2039435 3874081 := bstep (se 2 (by rfl) ⟨1452780, by rfl⟩ : syracuseStep 3874081 = 2905561) B2905561
theorem B5165441 : Blo 2039435 5165441 := bstep (se 2 (by rfl) ⟨1937040, by rfl⟩ : syracuseStep 5165441 = 3874081) B3874081
theorem B3443627 : Blo 2039435 3443627 := bstep (se 1 (by rfl) ⟨2582720, by rfl⟩ : syracuseStep 3443627 = 5165441) B5165441
theorem B2295751 : Blo 2039435 2295751 := bstep (se 1 (by rfl) ⟨1721813, by rfl⟩ : syracuseStep 2295751 = 3443627) B3443627
theorem B3061001 : Blo 2039435 3061001 := bstep (se 2 (by rfl) ⟨1147875, by rfl⟩ : syracuseStep 3061001 = 2295751) B2295751
theorem B2040667 : Blo 2039435 2040667 := bstep (se 1 (by rfl) ⟨1530500, by rfl⟩ : syracuseStep 2040667 = 3061001) B3061001
theorem B10330901 : Blo 2039435 10330901 := bbase (se 6 (by rfl) ⟨242130, by rfl⟩ : syracuseStep 10330901 = 484261) (by norm_num)
theorem B6887267 : Blo 2039435 6887267 := bstep (se 1 (by rfl) ⟨5165450, by rfl⟩ : syracuseStep 6887267 = 10330901) B10330901
theorem B4591511 : Blo 2039435 4591511 := bstep (se 1 (by rfl) ⟨3443633, by rfl⟩ : syracuseStep 4591511 = 6887267) B6887267
theorem B3061007 : Blo 2039435 3061007 := bstep (se 1 (by rfl) ⟨2295755, by rfl⟩ : syracuseStep 3061007 = 4591511) B4591511
theorem B2040671 : Blo 2039435 2040671 := bstep (se 1 (by rfl) ⟨1530503, by rfl⟩ : syracuseStep 2040671 = 3061007) B3061007
theorem B3061013 : Blo 2039435 3061013 := bbase (se 6 (by rfl) ⟨71742, by rfl⟩ : syracuseStep 3061013 = 143485) (by norm_num)
theorem B2040675 : Blo 2039435 2040675 := bstep (se 1 (by rfl) ⟨1530506, by rfl⟩ : syracuseStep 2040675 = 3061013) B3061013
theorem B5037869 : Blo 2039435 5037869 := bbase (se 3 (by rfl) ⟨944600, by rfl⟩ : syracuseStep 5037869 = 1889201) (by norm_num)
theorem B3358579 : Blo 2039435 3358579 := bstep (se 1 (by rfl) ⟨2518934, by rfl⟩ : syracuseStep 3358579 = 5037869) B5037869
theorem B4478105 : Blo 2039435 4478105 := bstep (se 2 (by rfl) ⟨1679289, by rfl⟩ : syracuseStep 4478105 = 3358579) B3358579
theorem B11941613 : Blo 2039435 11941613 := bstep (se 3 (by rfl) ⟨2239052, by rfl⟩ : syracuseStep 11941613 = 4478105) B4478105
theorem B7961075 : Blo 2039435 7961075 := bstep (se 1 (by rfl) ⟨5970806, by rfl⟩ : syracuseStep 7961075 = 11941613) B11941613
theorem B5307383 : Blo 2039435 5307383 := bstep (se 1 (by rfl) ⟨3980537, by rfl⟩ : syracuseStep 5307383 = 7961075) B7961075
theorem B3538255 : Blo 2039435 3538255 := bstep (se 1 (by rfl) ⟨2653691, by rfl⟩ : syracuseStep 3538255 = 5307383) B5307383
theorem B4717673 : Blo 2039435 4717673 := bstep (se 2 (by rfl) ⟨1769127, by rfl⟩ : syracuseStep 4717673 = 3538255) B3538255
theorem B50321845 : Blo 2039435 50321845 := bstep (se 5 (by rfl) ⟨2358836, by rfl⟩ : syracuseStep 50321845 = 4717673) B4717673
theorem B67095793 : Blo 2039435 67095793 := bstep (se 2 (by rfl) ⟨25160922, by rfl⟩ : syracuseStep 67095793 = 50321845) B50321845
theorem B89461057 : Blo 2039435 89461057 := bstep (se 2 (by rfl) ⟨33547896, by rfl⟩ : syracuseStep 89461057 = 67095793) B67095793
theorem B119281409 : Blo 2039435 119281409 := bstep (se 2 (by rfl) ⟨44730528, by rfl⟩ : syracuseStep 119281409 = 89461057) B89461057
theorem B79520939 : Blo 2039435 79520939 := bstep (se 1 (by rfl) ⟨59640704, by rfl⟩ : syracuseStep 79520939 = 119281409) B119281409
theorem B53013959 : Blo 2039435 53013959 := bstep (se 1 (by rfl) ⟨39760469, by rfl⟩ : syracuseStep 53013959 = 79520939) B79520939
theorem B35342639 : Blo 2039435 35342639 := bstep (se 1 (by rfl) ⟨26506979, by rfl⟩ : syracuseStep 35342639 = 53013959) B53013959
theorem B23561759 : Blo 2039435 23561759 := bstep (se 1 (by rfl) ⟨17671319, by rfl⟩ : syracuseStep 23561759 = 35342639) B35342639
theorem B15707839 : Blo 2039435 15707839 := bstep (se 1 (by rfl) ⟨11780879, by rfl⟩ : syracuseStep 15707839 = 23561759) B23561759
theorem B20943785 : Blo 2039435 20943785 := bstep (se 2 (by rfl) ⟨7853919, by rfl⟩ : syracuseStep 20943785 = 15707839) B15707839
theorem B55850093 : Blo 2039435 55850093 := bstep (se 3 (by rfl) ⟨10471892, by rfl⟩ : syracuseStep 55850093 = 20943785) B20943785
theorem B37233395 : Blo 2039435 37233395 := bstep (se 1 (by rfl) ⟨27925046, by rfl⟩ : syracuseStep 37233395 = 55850093) B55850093
theorem B24822263 : Blo 2039435 24822263 := bstep (se 1 (by rfl) ⟨18616697, by rfl⟩ : syracuseStep 24822263 = 37233395) B37233395
theorem B16548175 : Blo 2039435 16548175 := bstep (se 1 (by rfl) ⟨12411131, by rfl⟩ : syracuseStep 16548175 = 24822263) B24822263
theorem B22064233 : Blo 2039435 22064233 := bstep (se 2 (by rfl) ⟨8274087, by rfl⟩ : syracuseStep 22064233 = 16548175) B16548175
theorem B29418977 : Blo 2039435 29418977 := bstep (se 2 (by rfl) ⟨11032116, by rfl⟩ : syracuseStep 29418977 = 22064233) B22064233
theorem B19612651 : Blo 2039435 19612651 := bstep (se 1 (by rfl) ⟨14709488, by rfl⟩ : syracuseStep 19612651 = 29418977) B29418977
theorem B26150201 : Blo 2039435 26150201 := bstep (se 2 (by rfl) ⟨9806325, by rfl⟩ : syracuseStep 26150201 = 19612651) B19612651
theorem B17433467 : Blo 2039435 17433467 := bstep (se 1 (by rfl) ⟨13075100, by rfl⟩ : syracuseStep 17433467 = 26150201) B26150201
theorem B11622311 : Blo 2039435 11622311 := bstep (se 1 (by rfl) ⟨8716733, by rfl⟩ : syracuseStep 11622311 = 17433467) B17433467
theorem B7748207 : Blo 2039435 7748207 := bstep (se 1 (by rfl) ⟨5811155, by rfl⟩ : syracuseStep 7748207 = 11622311) B11622311
theorem B5165471 : Blo 2039435 5165471 := bstep (se 1 (by rfl) ⟨3874103, by rfl⟩ : syracuseStep 5165471 = 7748207) B7748207
theorem B3443647 : Blo 2039435 3443647 := bstep (se 1 (by rfl) ⟨2582735, by rfl⟩ : syracuseStep 3443647 = 5165471) B5165471
theorem B4591529 : Blo 2039435 4591529 := bstep (se 2 (by rfl) ⟨1721823, by rfl⟩ : syracuseStep 4591529 = 3443647) B3443647
theorem B3061019 : Blo 2039435 3061019 := bstep (se 1 (by rfl) ⟨2295764, by rfl⟩ : syracuseStep 3061019 = 4591529) B4591529
theorem B2040679 : Blo 2039435 2040679 := bstep (se 1 (by rfl) ⟨1530509, by rfl⟩ : syracuseStep 2040679 = 3061019) B3061019
theorem B2295769 : Blo 2039435 2295769 := bbase (se 2 (by rfl) ⟨860913, by rfl⟩ : syracuseStep 2295769 = 1721827) (by norm_num)
theorem B3061025 : Blo 2039435 3061025 := bstep (se 2 (by rfl) ⟨1147884, by rfl⟩ : syracuseStep 3061025 = 2295769) B2295769
theorem B2040683 : Blo 2039435 2040683 := bstep (se 1 (by rfl) ⟨1530512, by rfl⟩ : syracuseStep 2040683 = 3061025) B3061025
theorem B2905589 : Blo 2039435 2905589 := bbase (se 5 (by rfl) ⟨136199, by rfl⟩ : syracuseStep 2905589 = 272399) (by norm_num)
theorem B7748237 : Blo 2039435 7748237 := bstep (se 3 (by rfl) ⟨1452794, by rfl⟩ : syracuseStep 7748237 = 2905589) B2905589
theorem B5165491 : Blo 2039435 5165491 := bstep (se 1 (by rfl) ⟨3874118, by rfl⟩ : syracuseStep 5165491 = 7748237) B7748237
theorem B6887321 : Blo 2039435 6887321 := bstep (se 2 (by rfl) ⟨2582745, by rfl⟩ : syracuseStep 6887321 = 5165491) B5165491
theorem B4591547 : Blo 2039435 4591547 := bstep (se 1 (by rfl) ⟨3443660, by rfl⟩ : syracuseStep 4591547 = 6887321) B6887321
theorem B3061031 : Blo 2039435 3061031 := bstep (se 1 (by rfl) ⟨2295773, by rfl⟩ : syracuseStep 3061031 = 4591547) B4591547
theorem B2040687 : Blo 2039435 2040687 := bstep (se 1 (by rfl) ⟨1530515, by rfl⟩ : syracuseStep 2040687 = 3061031) B3061031
theorem B3061037 : Blo 2039435 3061037 := bbase (se 3 (by rfl) ⟨573944, by rfl⟩ : syracuseStep 3061037 = 1147889) (by norm_num)
theorem B2040691 : Blo 2039435 2040691 := bstep (se 1 (by rfl) ⟨1530518, by rfl⟩ : syracuseStep 2040691 = 3061037) B3061037
theorem B4591565 : Blo 2039435 4591565 := bbase (se 3 (by rfl) ⟨860918, by rfl⟩ : syracuseStep 4591565 = 1721837) (by norm_num)
theorem B3061043 : Blo 2039435 3061043 := bstep (se 1 (by rfl) ⟨2295782, by rfl⟩ : syracuseStep 3061043 = 4591565) B4591565
theorem B2040695 : Blo 2039435 2040695 := bstep (se 1 (by rfl) ⟨1530521, by rfl⟩ : syracuseStep 2040695 = 3061043) B3061043
theorem B2582761 : Blo 2039435 2582761 := bbase (se 2 (by rfl) ⟨968535, by rfl⟩ : syracuseStep 2582761 = 1937071) (by norm_num)
theorem B3443681 : Blo 2039435 3443681 := bstep (se 2 (by rfl) ⟨1291380, by rfl⟩ : syracuseStep 3443681 = 2582761) B2582761
theorem B2295787 : Blo 2039435 2295787 := bstep (se 1 (by rfl) ⟨1721840, by rfl⟩ : syracuseStep 2295787 = 3443681) B3443681
theorem B3061049 : Blo 2039435 3061049 := bstep (se 2 (by rfl) ⟨1147893, by rfl⟩ : syracuseStep 3061049 = 2295787) B2295787
theorem B2040699 : Blo 2039435 2040699 := bstep (se 1 (by rfl) ⟨1530524, by rfl⟩ : syracuseStep 2040699 = 3061049) B3061049
theorem B13075253 : Blo 2039435 13075253 := bbase (se 5 (by rfl) ⟨612902, by rfl⟩ : syracuseStep 13075253 = 1225805) (by norm_num)
theorem B8716835 : Blo 2039435 8716835 := bstep (se 1 (by rfl) ⟨6537626, by rfl⟩ : syracuseStep 8716835 = 13075253) B13075253
theorem B23244893 : Blo 2039435 23244893 := bstep (se 3 (by rfl) ⟨4358417, by rfl⟩ : syracuseStep 23244893 = 8716835) B8716835
theorem B15496595 : Blo 2039435 15496595 := bstep (se 1 (by rfl) ⟨11622446, by rfl⟩ : syracuseStep 15496595 = 23244893) B23244893
theorem B10331063 : Blo 2039435 10331063 := bstep (se 1 (by rfl) ⟨7748297, by rfl⟩ : syracuseStep 10331063 = 15496595) B15496595
theorem B6887375 : Blo 2039435 6887375 := bstep (se 1 (by rfl) ⟨5165531, by rfl⟩ : syracuseStep 6887375 = 10331063) B10331063
theorem B4591583 : Blo 2039435 4591583 := bstep (se 1 (by rfl) ⟨3443687, by rfl⟩ : syracuseStep 4591583 = 6887375) B6887375
theorem B3061055 : Blo 2039435 3061055 := bstep (se 1 (by rfl) ⟨2295791, by rfl⟩ : syracuseStep 3061055 = 4591583) B4591583
theorem B2040703 : Blo 2039435 2040703 := bstep (se 1 (by rfl) ⟨1530527, by rfl⟩ : syracuseStep 2040703 = 3061055) B3061055
theorem B3061061 : Blo 2039435 3061061 := bbase (se 4 (by rfl) ⟨286974, by rfl⟩ : syracuseStep 3061061 = 573949) (by norm_num)
theorem B2040707 : Blo 2039435 2040707 := bstep (se 1 (by rfl) ⟨1530530, by rfl⟩ : syracuseStep 2040707 = 3061061) B3061061
theorem B3443701 : Blo 2039435 3443701 := bbase (se 5 (by rfl) ⟨161423, by rfl⟩ : syracuseStep 3443701 = 322847) (by norm_num)
theorem B4591601 : Blo 2039435 4591601 := bstep (se 2 (by rfl) ⟨1721850, by rfl⟩ : syracuseStep 4591601 = 3443701) B3443701
theorem B3061067 : Blo 2039435 3061067 := bstep (se 1 (by rfl) ⟨2295800, by rfl⟩ : syracuseStep 3061067 = 4591601) B4591601
theorem B2040711 : Blo 2039435 2040711 := bstep (se 1 (by rfl) ⟨1530533, by rfl⟩ : syracuseStep 2040711 = 3061067) B3061067
theorem B2295805 : Blo 2039435 2295805 := bbase (se 3 (by rfl) ⟨430463, by rfl⟩ : syracuseStep 2295805 = 860927) (by norm_num)
theorem B3061073 : Blo 2039435 3061073 := bstep (se 2 (by rfl) ⟨1147902, by rfl⟩ : syracuseStep 3061073 = 2295805) B2295805
theorem B2040715 : Blo 2039435 2040715 := bstep (se 1 (by rfl) ⟨1530536, by rfl⟩ : syracuseStep 2040715 = 3061073) B3061073
theorem B6887429 : Blo 2039435 6887429 := bbase (se 4 (by rfl) ⟨645696, by rfl⟩ : syracuseStep 6887429 = 1291393) (by norm_num)
theorem B4591619 : Blo 2039435 4591619 := bstep (se 1 (by rfl) ⟨3443714, by rfl⟩ : syracuseStep 4591619 = 6887429) B6887429
theorem B3061079 : Blo 2039435 3061079 := bstep (se 1 (by rfl) ⟨2295809, by rfl⟩ : syracuseStep 3061079 = 4591619) B4591619
theorem B2040719 : Blo 2039435 2040719 := bstep (se 1 (by rfl) ⟨1530539, by rfl⟩ : syracuseStep 2040719 = 3061079) B3061079
theorem B3061085 : Blo 2039435 3061085 := bbase (se 3 (by rfl) ⟨573953, by rfl⟩ : syracuseStep 3061085 = 1147907) (by norm_num)
theorem B2040723 : Blo 2039435 2040723 := bstep (se 1 (by rfl) ⟨1530542, by rfl⟩ : syracuseStep 2040723 = 3061085) B3061085
theorem B4591637 : Blo 2039435 4591637 := bbase (se 6 (by rfl) ⟨107616, by rfl⟩ : syracuseStep 4591637 = 215233) (by norm_num)
theorem B3061091 : Blo 2039435 3061091 := bstep (se 1 (by rfl) ⟨2295818, by rfl⟩ : syracuseStep 3061091 = 4591637) B4591637
theorem B2040727 : Blo 2039435 2040727 := bstep (se 1 (by rfl) ⟨1530545, by rfl⟩ : syracuseStep 2040727 = 3061091) B3061091
theorem B7748405 : Blo 2039435 7748405 := bbase (se 5 (by rfl) ⟨363206, by rfl⟩ : syracuseStep 7748405 = 726413) (by norm_num)
theorem B5165603 : Blo 2039435 5165603 := bstep (se 1 (by rfl) ⟨3874202, by rfl⟩ : syracuseStep 5165603 = 7748405) B7748405
theorem B3443735 : Blo 2039435 3443735 := bstep (se 1 (by rfl) ⟨2582801, by rfl⟩ : syracuseStep 3443735 = 5165603) B5165603
theorem B2295823 : Blo 2039435 2295823 := bstep (se 1 (by rfl) ⟨1721867, by rfl⟩ : syracuseStep 2295823 = 3443735) B3443735
theorem B3061097 : Blo 2039435 3061097 := bstep (se 2 (by rfl) ⟨1147911, by rfl⟩ : syracuseStep 3061097 = 2295823) B2295823
theorem B2040731 : Blo 2039435 2040731 := bstep (se 1 (by rfl) ⟨1530548, by rfl⟩ : syracuseStep 2040731 = 3061097) B3061097
theorem B2451649 : Blo 2039435 2451649 := bbase (se 2 (by rfl) ⟨919368, by rfl⟩ : syracuseStep 2451649 = 1838737) (by norm_num)
theorem B3268865 : Blo 2039435 3268865 := bstep (se 2 (by rfl) ⟨1225824, by rfl⟩ : syracuseStep 3268865 = 2451649) B2451649
theorem B2179243 : Blo 2039435 2179243 := bstep (se 1 (by rfl) ⟨1634432, by rfl⟩ : syracuseStep 2179243 = 3268865) B3268865
theorem B11622629 : Blo 2039435 11622629 := bstep (se 4 (by rfl) ⟨1089621, by rfl⟩ : syracuseStep 11622629 = 2179243) B2179243
theorem B7748419 : Blo 2039435 7748419 := bstep (se 1 (by rfl) ⟨5811314, by rfl⟩ : syracuseStep 7748419 = 11622629) B11622629
theorem B10331225 : Blo 2039435 10331225 := bstep (se 2 (by rfl) ⟨3874209, by rfl⟩ : syracuseStep 10331225 = 7748419) B7748419
theorem B6887483 : Blo 2039435 6887483 := bstep (se 1 (by rfl) ⟨5165612, by rfl⟩ : syracuseStep 6887483 = 10331225) B10331225
theorem B4591655 : Blo 2039435 4591655 := bstep (se 1 (by rfl) ⟨3443741, by rfl⟩ : syracuseStep 4591655 = 6887483) B6887483
theorem B3061103 : Blo 2039435 3061103 := bstep (se 1 (by rfl) ⟨2295827, by rfl⟩ : syracuseStep 3061103 = 4591655) B4591655
theorem B2040735 : Blo 2039435 2040735 := bstep (se 1 (by rfl) ⟨1530551, by rfl⟩ : syracuseStep 2040735 = 3061103) B3061103
theorem B3061109 : Blo 2039435 3061109 := bbase (se 5 (by rfl) ⟨143489, by rfl⟩ : syracuseStep 3061109 = 286979) (by norm_num)
theorem B2040739 : Blo 2039435 2040739 := bstep (se 1 (by rfl) ⟨1530554, by rfl⟩ : syracuseStep 2040739 = 3061109) B3061109
theorem B2905669 : Blo 2039435 2905669 := bbase (se 4 (by rfl) ⟨272406, by rfl⟩ : syracuseStep 2905669 = 544813) (by norm_num)
theorem B3874225 : Blo 2039435 3874225 := bstep (se 2 (by rfl) ⟨1452834, by rfl⟩ : syracuseStep 3874225 = 2905669) B2905669
theorem B5165633 : Blo 2039435 5165633 := bstep (se 2 (by rfl) ⟨1937112, by rfl⟩ : syracuseStep 5165633 = 3874225) B3874225
theorem B3443755 : Blo 2039435 3443755 := bstep (se 1 (by rfl) ⟨2582816, by rfl⟩ : syracuseStep 3443755 = 5165633) B5165633
theorem B4591673 : Blo 2039435 4591673 := bstep (se 2 (by rfl) ⟨1721877, by rfl⟩ : syracuseStep 4591673 = 3443755) B3443755
theorem B3061115 : Blo 2039435 3061115 := bstep (se 1 (by rfl) ⟨2295836, by rfl⟩ : syracuseStep 3061115 = 4591673) B4591673
theorem B2040743 : Blo 2039435 2040743 := bstep (se 1 (by rfl) ⟨1530557, by rfl⟩ : syracuseStep 2040743 = 3061115) B3061115
theorem B2295841 : Blo 2039435 2295841 := bbase (se 2 (by rfl) ⟨860940, by rfl⟩ : syracuseStep 2295841 = 1721881) (by norm_num)
theorem B3061121 : Blo 2039435 3061121 := bstep (se 2 (by rfl) ⟨1147920, by rfl⟩ : syracuseStep 3061121 = 2295841) B2295841
theorem B2040747 : Blo 2039435 2040747 := bstep (se 1 (by rfl) ⟨1530560, by rfl⟩ : syracuseStep 2040747 = 3061121) B3061121
theorem B5165653 : Blo 2039435 5165653 := bbase (se 8 (by rfl) ⟨30267, by rfl⟩ : syracuseStep 5165653 = 60535) (by norm_num)
theorem B6887537 : Blo 2039435 6887537 := bstep (se 2 (by rfl) ⟨2582826, by rfl⟩ : syracuseStep 6887537 = 5165653) B5165653
theorem B4591691 : Blo 2039435 4591691 := bstep (se 1 (by rfl) ⟨3443768, by rfl⟩ : syracuseStep 4591691 = 6887537) B6887537
theorem B3061127 : Blo 2039435 3061127 := bstep (se 1 (by rfl) ⟨2295845, by rfl⟩ : syracuseStep 3061127 = 4591691) B4591691
theorem B2040751 : Blo 2039435 2040751 := bstep (se 1 (by rfl) ⟨1530563, by rfl⟩ : syracuseStep 2040751 = 3061127) B3061127
theorem B3061133 : Blo 2039435 3061133 := bbase (se 3 (by rfl) ⟨573962, by rfl⟩ : syracuseStep 3061133 = 1147925) (by norm_num)
theorem B2040755 : Blo 2039435 2040755 := bstep (se 1 (by rfl) ⟨1530566, by rfl⟩ : syracuseStep 2040755 = 3061133) B3061133
theorem B4591709 : Blo 2039435 4591709 := bbase (se 3 (by rfl) ⟨860945, by rfl⟩ : syracuseStep 4591709 = 1721891) (by norm_num)
theorem B3061139 : Blo 2039435 3061139 := bstep (se 1 (by rfl) ⟨2295854, by rfl⟩ : syracuseStep 3061139 = 4591709) B4591709
theorem B2040759 : Blo 2039435 2040759 := bstep (se 1 (by rfl) ⟨1530569, by rfl⟩ : syracuseStep 2040759 = 3061139) B3061139
theorem B3443789 : Blo 2039435 3443789 := bbase (se 3 (by rfl) ⟨645710, by rfl⟩ : syracuseStep 3443789 = 1291421) (by norm_num)
theorem B2295859 : Blo 2039435 2295859 := bstep (se 1 (by rfl) ⟨1721894, by rfl⟩ : syracuseStep 2295859 = 3443789) B3443789
theorem B3061145 : Blo 2039435 3061145 := bstep (se 2 (by rfl) ⟨1147929, by rfl⟩ : syracuseStep 3061145 = 2295859) B2295859
theorem B2040763 : Blo 2039435 2040763 := bstep (se 1 (by rfl) ⟨1530572, by rfl⟩ : syracuseStep 2040763 = 3061145) B3061145
theorem B3490781 : Blo 2039435 3490781 := bbase (se 3 (by rfl) ⟨654521, by rfl⟩ : syracuseStep 3490781 = 1309043) (by norm_num)
theorem B37234997 : Blo 2039435 37234997 := bstep (se 5 (by rfl) ⟨1745390, by rfl⟩ : syracuseStep 37234997 = 3490781) B3490781
theorem B24823331 : Blo 2039435 24823331 := bstep (se 1 (by rfl) ⟨18617498, by rfl⟩ : syracuseStep 24823331 = 37234997) B37234997
theorem B16548887 : Blo 2039435 16548887 := bstep (se 1 (by rfl) ⟨12411665, by rfl⟩ : syracuseStep 16548887 = 24823331) B24823331
theorem B44130365 : Blo 2039435 44130365 := bstep (se 3 (by rfl) ⟨8274443, by rfl⟩ : syracuseStep 44130365 = 16548887) B16548887
theorem B29420243 : Blo 2039435 29420243 := bstep (se 1 (by rfl) ⟨22065182, by rfl⟩ : syracuseStep 29420243 = 44130365) B44130365
theorem B19613495 : Blo 2039435 19613495 := bstep (se 1 (by rfl) ⟨14710121, by rfl⟩ : syracuseStep 19613495 = 29420243) B29420243
theorem B13075663 : Blo 2039435 13075663 := bstep (se 1 (by rfl) ⟨9806747, by rfl⟩ : syracuseStep 13075663 = 19613495) B19613495
theorem B17434217 : Blo 2039435 17434217 := bstep (se 2 (by rfl) ⟨6537831, by rfl⟩ : syracuseStep 17434217 = 13075663) B13075663
theorem B11622811 : Blo 2039435 11622811 := bstep (se 1 (by rfl) ⟨8717108, by rfl⟩ : syracuseStep 11622811 = 17434217) B17434217
theorem B15497081 : Blo 2039435 15497081 := bstep (se 2 (by rfl) ⟨5811405, by rfl⟩ : syracuseStep 15497081 = 11622811) B11622811
theorem B10331387 : Blo 2039435 10331387 := bstep (se 1 (by rfl) ⟨7748540, by rfl⟩ : syracuseStep 10331387 = 15497081) B15497081
theorem B6887591 : Blo 2039435 6887591 := bstep (se 1 (by rfl) ⟨5165693, by rfl⟩ : syracuseStep 6887591 = 10331387) B10331387
theorem B4591727 : Blo 2039435 4591727 := bstep (se 1 (by rfl) ⟨3443795, by rfl⟩ : syracuseStep 4591727 = 6887591) B6887591
theorem B3061151 : Blo 2039435 3061151 := bstep (se 1 (by rfl) ⟨2295863, by rfl⟩ : syracuseStep 3061151 = 4591727) B4591727
theorem B2040767 : Blo 2039435 2040767 := bstep (se 1 (by rfl) ⟨1530575, by rfl⟩ : syracuseStep 2040767 = 3061151) B3061151
theorem B3061157 : Blo 2039435 3061157 := bbase (se 4 (by rfl) ⟨286983, by rfl⟩ : syracuseStep 3061157 = 573967) (by norm_num)
theorem B2040771 : Blo 2039435 2040771 := bstep (se 1 (by rfl) ⟨1530578, by rfl⟩ : syracuseStep 2040771 = 3061157) B3061157
theorem B2582857 : Blo 2039435 2582857 := bbase (se 2 (by rfl) ⟨968571, by rfl⟩ : syracuseStep 2582857 = 1937143) (by norm_num)
theorem B3443809 : Blo 2039435 3443809 := bstep (se 2 (by rfl) ⟨1291428, by rfl⟩ : syracuseStep 3443809 = 2582857) B2582857
theorem B4591745 : Blo 2039435 4591745 := bstep (se 2 (by rfl) ⟨1721904, by rfl⟩ : syracuseStep 4591745 = 3443809) B3443809
theorem B3061163 : Blo 2039435 3061163 := bstep (se 1 (by rfl) ⟨2295872, by rfl⟩ : syracuseStep 3061163 = 4591745) B4591745
theorem B2040775 : Blo 2039435 2040775 := bstep (se 1 (by rfl) ⟨1530581, by rfl⟩ : syracuseStep 2040775 = 3061163) B3061163
theorem B2295877 : Blo 2039435 2295877 := bbase (se 4 (by rfl) ⟨215238, by rfl⟩ : syracuseStep 2295877 = 430477) (by norm_num)
theorem B3061169 : Blo 2039435 3061169 := bstep (se 2 (by rfl) ⟨1147938, by rfl⟩ : syracuseStep 3061169 = 2295877) B2295877
theorem B2040779 : Blo 2039435 2040779 := bstep (se 1 (by rfl) ⟨1530584, by rfl⟩ : syracuseStep 2040779 = 3061169) B3061169
theorem B3874301 : Blo 2039435 3874301 := bbase (se 3 (by rfl) ⟨726431, by rfl⟩ : syracuseStep 3874301 = 1452863) (by norm_num)
theorem B2582867 : Blo 2039435 2582867 := bstep (se 1 (by rfl) ⟨1937150, by rfl⟩ : syracuseStep 2582867 = 3874301) B3874301
theorem B6887645 : Blo 2039435 6887645 := bstep (se 3 (by rfl) ⟨1291433, by rfl⟩ : syracuseStep 6887645 = 2582867) B2582867
theorem B4591763 : Blo 2039435 4591763 := bstep (se 1 (by rfl) ⟨3443822, by rfl⟩ : syracuseStep 4591763 = 6887645) B6887645
theorem B3061175 : Blo 2039435 3061175 := bstep (se 1 (by rfl) ⟨2295881, by rfl⟩ : syracuseStep 3061175 = 4591763) B4591763
theorem B2040783 : Blo 2039435 2040783 := bstep (se 1 (by rfl) ⟨1530587, by rfl⟩ : syracuseStep 2040783 = 3061175) B3061175
theorem B3061181 : Blo 2039435 3061181 := bbase (se 3 (by rfl) ⟨573971, by rfl⟩ : syracuseStep 3061181 = 1147943) (by norm_num)
theorem B2040787 : Blo 2039435 2040787 := bstep (se 1 (by rfl) ⟨1530590, by rfl⟩ : syracuseStep 2040787 = 3061181) B3061181
theorem B4591781 : Blo 2039435 4591781 := bbase (se 4 (by rfl) ⟨430479, by rfl⟩ : syracuseStep 4591781 = 860959) (by norm_num)
theorem B3061187 : Blo 2039435 3061187 := bstep (se 1 (by rfl) ⟨2295890, by rfl⟩ : syracuseStep 3061187 = 4591781) B4591781
theorem B2040791 : Blo 2039435 2040791 := bstep (se 1 (by rfl) ⟨1530593, by rfl⟩ : syracuseStep 2040791 = 3061187) B3061187
theorem B5165765 : Blo 2039435 5165765 := bbase (se 4 (by rfl) ⟨484290, by rfl⟩ : syracuseStep 5165765 = 968581) (by norm_num)
theorem B3443843 : Blo 2039435 3443843 := bstep (se 1 (by rfl) ⟨2582882, by rfl⟩ : syracuseStep 3443843 = 5165765) B5165765
theorem B2295895 : Blo 2039435 2295895 := bstep (se 1 (by rfl) ⟨1721921, by rfl⟩ : syracuseStep 2295895 = 3443843) B3443843
theorem B3061193 : Blo 2039435 3061193 := bstep (se 2 (by rfl) ⟨1147947, by rfl⟩ : syracuseStep 3061193 = 2295895) B2295895
theorem B2040795 : Blo 2039435 2040795 := bstep (se 1 (by rfl) ⟨1530596, by rfl⟩ : syracuseStep 2040795 = 3061193) B3061193
theorem B3980773 : Blo 2039435 3980773 := bbase (se 4 (by rfl) ⟨373197, by rfl⟩ : syracuseStep 3980773 = 746395) (by norm_num)
theorem B5307697 : Blo 2039435 5307697 := bstep (se 2 (by rfl) ⟨1990386, by rfl⟩ : syracuseStep 5307697 = 3980773) B3980773
theorem B7076929 : Blo 2039435 7076929 := bstep (se 2 (by rfl) ⟨2653848, by rfl⟩ : syracuseStep 7076929 = 5307697) B5307697
theorem B9435905 : Blo 2039435 9435905 := bstep (se 2 (by rfl) ⟨3538464, by rfl⟩ : syracuseStep 9435905 = 7076929) B7076929
theorem B6290603 : Blo 2039435 6290603 := bstep (se 1 (by rfl) ⟨4717952, by rfl⟩ : syracuseStep 6290603 = 9435905) B9435905
theorem B4193735 : Blo 2039435 4193735 := bstep (se 1 (by rfl) ⟨3145301, by rfl⟩ : syracuseStep 4193735 = 6290603) B6290603
theorem B11183293 : Blo 2039435 11183293 := bstep (se 3 (by rfl) ⟨2096867, by rfl⟩ : syracuseStep 11183293 = 4193735) B4193735
theorem B14911057 : Blo 2039435 14911057 := bstep (se 2 (by rfl) ⟨5591646, by rfl⟩ : syracuseStep 14911057 = 11183293) B11183293
theorem B19881409 : Blo 2039435 19881409 := bstep (se 2 (by rfl) ⟨7455528, by rfl⟩ : syracuseStep 19881409 = 14911057) B14911057
theorem B26508545 : Blo 2039435 26508545 := bstep (se 2 (by rfl) ⟨9940704, by rfl⟩ : syracuseStep 26508545 = 19881409) B19881409
theorem B17672363 : Blo 2039435 17672363 := bstep (se 1 (by rfl) ⟨13254272, by rfl⟩ : syracuseStep 17672363 = 26508545) B26508545
theorem B11781575 : Blo 2039435 11781575 := bstep (se 1 (by rfl) ⟨8836181, by rfl⟩ : syracuseStep 11781575 = 17672363) B17672363
theorem B7854383 : Blo 2039435 7854383 := bstep (se 1 (by rfl) ⟨5890787, by rfl⟩ : syracuseStep 7854383 = 11781575) B11781575
theorem B5236255 : Blo 2039435 5236255 := bstep (se 1 (by rfl) ⟨3927191, by rfl⟩ : syracuseStep 5236255 = 7854383) B7854383
theorem B27926693 : Blo 2039435 27926693 := bstep (se 4 (by rfl) ⟨2618127, by rfl⟩ : syracuseStep 27926693 = 5236255) B5236255
theorem B18617795 : Blo 2039435 18617795 := bstep (se 1 (by rfl) ⟨13963346, by rfl⟩ : syracuseStep 18617795 = 27926693) B27926693
theorem B12411863 : Blo 2039435 12411863 := bstep (se 1 (by rfl) ⟨9308897, by rfl⟩ : syracuseStep 12411863 = 18617795) B18617795
theorem B8274575 : Blo 2039435 8274575 := bstep (se 1 (by rfl) ⟨6205931, by rfl⟩ : syracuseStep 8274575 = 12411863) B12411863
theorem B22065533 : Blo 2039435 22065533 := bstep (se 3 (by rfl) ⟨4137287, by rfl⟩ : syracuseStep 22065533 = 8274575) B8274575
theorem B14710355 : Blo 2039435 14710355 := bstep (se 1 (by rfl) ⟨11032766, by rfl⟩ : syracuseStep 14710355 = 22065533) B22065533
theorem B9806903 : Blo 2039435 9806903 := bstep (se 1 (by rfl) ⟨7355177, by rfl⟩ : syracuseStep 9806903 = 14710355) B14710355
theorem B6537935 : Blo 2039435 6537935 := bstep (se 1 (by rfl) ⟨4903451, by rfl⟩ : syracuseStep 6537935 = 9806903) B9806903
theorem B4358623 : Blo 2039435 4358623 := bstep (se 1 (by rfl) ⟨3268967, by rfl⟩ : syracuseStep 4358623 = 6537935) B6537935
theorem B5811497 : Blo 2039435 5811497 := bstep (se 2 (by rfl) ⟨2179311, by rfl⟩ : syracuseStep 5811497 = 4358623) B4358623
theorem B3874331 : Blo 2039435 3874331 := bstep (se 1 (by rfl) ⟨2905748, by rfl⟩ : syracuseStep 3874331 = 5811497) B5811497
theorem B10331549 : Blo 2039435 10331549 := bstep (se 3 (by rfl) ⟨1937165, by rfl⟩ : syracuseStep 10331549 = 3874331) B3874331
theorem B6887699 : Blo 2039435 6887699 := bstep (se 1 (by rfl) ⟨5165774, by rfl⟩ : syracuseStep 6887699 = 10331549) B10331549
theorem B4591799 : Blo 2039435 4591799 := bstep (se 1 (by rfl) ⟨3443849, by rfl⟩ : syracuseStep 4591799 = 6887699) B6887699
theorem B3061199 : Blo 2039435 3061199 := bstep (se 1 (by rfl) ⟨2295899, by rfl⟩ : syracuseStep 3061199 = 4591799) B4591799
theorem B2040799 : Blo 2039435 2040799 := bstep (se 1 (by rfl) ⟨1530599, by rfl⟩ : syracuseStep 2040799 = 3061199) B3061199
theorem B3061205 : Blo 2039435 3061205 := bbase (se 7 (by rfl) ⟨35873, by rfl⟩ : syracuseStep 3061205 = 71747) (by norm_num)
theorem B2040803 : Blo 2039435 2040803 := bstep (se 1 (by rfl) ⟨1530602, by rfl⟩ : syracuseStep 2040803 = 3061205) B3061205
theorem B7748693 : Blo 2039435 7748693 := bbase (se 8 (by rfl) ⟨45402, by rfl⟩ : syracuseStep 7748693 = 90805) (by norm_num)
theorem B5165795 : Blo 2039435 5165795 := bstep (se 1 (by rfl) ⟨3874346, by rfl⟩ : syracuseStep 5165795 = 7748693) B7748693
theorem B3443863 : Blo 2039435 3443863 := bstep (se 1 (by rfl) ⟨2582897, by rfl⟩ : syracuseStep 3443863 = 5165795) B5165795
theorem B4591817 : Blo 2039435 4591817 := bstep (se 2 (by rfl) ⟨1721931, by rfl⟩ : syracuseStep 4591817 = 3443863) B3443863
theorem B3061211 : Blo 2039435 3061211 := bstep (se 1 (by rfl) ⟨2295908, by rfl⟩ : syracuseStep 3061211 = 4591817) B4591817
theorem B2040807 : Blo 2039435 2040807 := bstep (se 1 (by rfl) ⟨1530605, by rfl⟩ : syracuseStep 2040807 = 3061211) B3061211
theorem B2295913 : Blo 2039435 2295913 := bbase (se 2 (by rfl) ⟨860967, by rfl⟩ : syracuseStep 2295913 = 1721935) (by norm_num)
theorem B3061217 : Blo 2039435 3061217 := bstep (se 2 (by rfl) ⟨1147956, by rfl⟩ : syracuseStep 3061217 = 2295913) B2295913
theorem B2040811 : Blo 2039435 2040811 := bstep (se 1 (by rfl) ⟨1530608, by rfl⟩ : syracuseStep 2040811 = 3061217) B3061217
theorem B2451745 : Blo 2039435 2451745 := bbase (se 2 (by rfl) ⟨919404, by rfl⟩ : syracuseStep 2451745 = 1838809) (by norm_num)
theorem B3268993 : Blo 2039435 3268993 := bstep (se 2 (by rfl) ⟨1225872, by rfl⟩ : syracuseStep 3268993 = 2451745) B2451745
theorem B4358657 : Blo 2039435 4358657 := bstep (se 2 (by rfl) ⟨1634496, by rfl⟩ : syracuseStep 4358657 = 3268993) B3268993
theorem B11623085 : Blo 2039435 11623085 := bstep (se 3 (by rfl) ⟨2179328, by rfl⟩ : syracuseStep 11623085 = 4358657) B4358657
theorem B7748723 : Blo 2039435 7748723 := bstep (se 1 (by rfl) ⟨5811542, by rfl⟩ : syracuseStep 7748723 = 11623085) B11623085
theorem B5165815 : Blo 2039435 5165815 := bstep (se 1 (by rfl) ⟨3874361, by rfl⟩ : syracuseStep 5165815 = 7748723) B7748723
theorem B6887753 : Blo 2039435 6887753 := bstep (se 2 (by rfl) ⟨2582907, by rfl⟩ : syracuseStep 6887753 = 5165815) B5165815
theorem B4591835 : Blo 2039435 4591835 := bstep (se 1 (by rfl) ⟨3443876, by rfl⟩ : syracuseStep 4591835 = 6887753) B6887753
theorem B3061223 : Blo 2039435 3061223 := bstep (se 1 (by rfl) ⟨2295917, by rfl⟩ : syracuseStep 3061223 = 4591835) B4591835
theorem B2040815 : Blo 2039435 2040815 := bstep (se 1 (by rfl) ⟨1530611, by rfl⟩ : syracuseStep 2040815 = 3061223) B3061223
theorem B3061229 : Blo 2039435 3061229 := bbase (se 3 (by rfl) ⟨573980, by rfl⟩ : syracuseStep 3061229 = 1147961) (by norm_num)
theorem B2040819 : Blo 2039435 2040819 := bstep (se 1 (by rfl) ⟨1530614, by rfl⟩ : syracuseStep 2040819 = 3061229) B3061229
theorem B4591853 : Blo 2039435 4591853 := bbase (se 3 (by rfl) ⟨860972, by rfl⟩ : syracuseStep 4591853 = 1721945) (by norm_num)
theorem B3061235 : Blo 2039435 3061235 := bstep (se 1 (by rfl) ⟨2295926, by rfl⟩ : syracuseStep 3061235 = 4591853) B4591853
theorem B2040823 : Blo 2039435 2040823 := bstep (se 1 (by rfl) ⟨1530617, by rfl⟩ : syracuseStep 2040823 = 3061235) B3061235
theorem B2905789 : Blo 2039435 2905789 := bbase (se 3 (by rfl) ⟨544835, by rfl⟩ : syracuseStep 2905789 = 1089671) (by norm_num)
theorem B3874385 : Blo 2039435 3874385 := bstep (se 2 (by rfl) ⟨1452894, by rfl⟩ : syracuseStep 3874385 = 2905789) B2905789
theorem B2582923 : Blo 2039435 2582923 := bstep (se 1 (by rfl) ⟨1937192, by rfl⟩ : syracuseStep 2582923 = 3874385) B3874385
theorem B3443897 : Blo 2039435 3443897 := bstep (se 2 (by rfl) ⟨1291461, by rfl⟩ : syracuseStep 3443897 = 2582923) B2582923
theorem B2295931 : Blo 2039435 2295931 := bstep (se 1 (by rfl) ⟨1721948, by rfl⟩ : syracuseStep 2295931 = 3443897) B3443897
theorem B3061241 : Blo 2039435 3061241 := bstep (se 2 (by rfl) ⟨1147965, by rfl⟩ : syracuseStep 3061241 = 2295931) B2295931
theorem B2040827 : Blo 2039435 2040827 := bstep (se 1 (by rfl) ⟨1530620, by rfl⟩ : syracuseStep 2040827 = 3061241) B3061241
theorem B27927125 : Blo 2039435 27927125 := bbase (se 8 (by rfl) ⟨163635, by rfl⟩ : syracuseStep 27927125 = 327271) (by norm_num)
theorem B18618083 : Blo 2039435 18618083 := bstep (se 1 (by rfl) ⟨13963562, by rfl⟩ : syracuseStep 18618083 = 27927125) B27927125
theorem B12412055 : Blo 2039435 12412055 := bstep (se 1 (by rfl) ⟨9309041, by rfl⟩ : syracuseStep 12412055 = 18618083) B18618083
theorem B8274703 : Blo 2039435 8274703 := bstep (se 1 (by rfl) ⟨6206027, by rfl⟩ : syracuseStep 8274703 = 12412055) B12412055
theorem B11032937 : Blo 2039435 11032937 := bstep (se 2 (by rfl) ⟨4137351, by rfl⟩ : syracuseStep 11032937 = 8274703) B8274703
theorem B7355291 : Blo 2039435 7355291 := bstep (se 1 (by rfl) ⟨5516468, by rfl⟩ : syracuseStep 7355291 = 11032937) B11032937
theorem B78456437 : Blo 2039435 78456437 := bstep (se 5 (by rfl) ⟨3677645, by rfl⟩ : syracuseStep 78456437 = 7355291) B7355291
theorem B52304291 : Blo 2039435 52304291 := bstep (se 1 (by rfl) ⟨39228218, by rfl⟩ : syracuseStep 52304291 = 78456437) B78456437
theorem B34869527 : Blo 2039435 34869527 := bstep (se 1 (by rfl) ⟨26152145, by rfl⟩ : syracuseStep 34869527 = 52304291) B52304291
theorem B23246351 : Blo 2039435 23246351 := bstep (se 1 (by rfl) ⟨17434763, by rfl⟩ : syracuseStep 23246351 = 34869527) B34869527
theorem B15497567 : Blo 2039435 15497567 := bstep (se 1 (by rfl) ⟨11623175, by rfl⟩ : syracuseStep 15497567 = 23246351) B23246351
theorem B10331711 : Blo 2039435 10331711 := bstep (se 1 (by rfl) ⟨7748783, by rfl⟩ : syracuseStep 10331711 = 15497567) B15497567
theorem B6887807 : Blo 2039435 6887807 := bstep (se 1 (by rfl) ⟨5165855, by rfl⟩ : syracuseStep 6887807 = 10331711) B10331711
theorem B4591871 : Blo 2039435 4591871 := bstep (se 1 (by rfl) ⟨3443903, by rfl⟩ : syracuseStep 4591871 = 6887807) B6887807
theorem B3061247 : Blo 2039435 3061247 := bstep (se 1 (by rfl) ⟨2295935, by rfl⟩ : syracuseStep 3061247 = 4591871) B4591871
theorem B2040831 : Blo 2039435 2040831 := bstep (se 1 (by rfl) ⟨1530623, by rfl⟩ : syracuseStep 2040831 = 3061247) B3061247
theorem B3061253 : Blo 2039435 3061253 := bbase (se 4 (by rfl) ⟨286992, by rfl⟩ : syracuseStep 3061253 = 573985) (by norm_num)
theorem B2040835 : Blo 2039435 2040835 := bstep (se 1 (by rfl) ⟨1530626, by rfl⟩ : syracuseStep 2040835 = 3061253) B3061253
theorem B3443917 : Blo 2039435 3443917 := bbase (se 3 (by rfl) ⟨645734, by rfl⟩ : syracuseStep 3443917 = 1291469) (by norm_num)
theorem B4591889 : Blo 2039435 4591889 := bstep (se 2 (by rfl) ⟨1721958, by rfl⟩ : syracuseStep 4591889 = 3443917) B3443917
theorem B3061259 : Blo 2039435 3061259 := bstep (se 1 (by rfl) ⟨2295944, by rfl⟩ : syracuseStep 3061259 = 4591889) B4591889
theorem B2040839 : Blo 2039435 2040839 := bstep (se 1 (by rfl) ⟨1530629, by rfl⟩ : syracuseStep 2040839 = 3061259) B3061259
theorem B2295949 : Blo 2039435 2295949 := bbase (se 3 (by rfl) ⟨430490, by rfl⟩ : syracuseStep 2295949 = 860981) (by norm_num)
theorem B3061265 : Blo 2039435 3061265 := bstep (se 2 (by rfl) ⟨1147974, by rfl⟩ : syracuseStep 3061265 = 2295949) B2295949
theorem B2040843 : Blo 2039435 2040843 := bstep (se 1 (by rfl) ⟨1530632, by rfl⟩ : syracuseStep 2040843 = 3061265) B3061265
theorem B6887861 : Blo 2039435 6887861 := bbase (se 5 (by rfl) ⟨322868, by rfl⟩ : syracuseStep 6887861 = 645737) (by norm_num)
theorem B4591907 : Blo 2039435 4591907 := bstep (se 1 (by rfl) ⟨3443930, by rfl⟩ : syracuseStep 4591907 = 6887861) B6887861
theorem B3061271 : Blo 2039435 3061271 := bstep (se 1 (by rfl) ⟨2295953, by rfl⟩ : syracuseStep 3061271 = 4591907) B4591907
theorem B2040847 : Blo 2039435 2040847 := bstep (se 1 (by rfl) ⟨1530635, by rfl⟩ : syracuseStep 2040847 = 3061271) B3061271
theorem B3061277 : Blo 2039435 3061277 := bbase (se 3 (by rfl) ⟨573989, by rfl⟩ : syracuseStep 3061277 = 1147979) (by norm_num)
theorem B2040851 : Blo 2039435 2040851 := bstep (se 1 (by rfl) ⟨1530638, by rfl⟩ : syracuseStep 2040851 = 3061277) B3061277
theorem B4591925 : Blo 2039435 4591925 := bbase (se 5 (by rfl) ⟨215246, by rfl⟩ : syracuseStep 4591925 = 430493) (by norm_num)
theorem B3061283 : Blo 2039435 3061283 := bstep (se 1 (by rfl) ⟨2295962, by rfl⟩ : syracuseStep 3061283 = 4591925) B4591925
theorem B2040855 : Blo 2039435 2040855 := bstep (se 1 (by rfl) ⟨1530641, by rfl⟩ : syracuseStep 2040855 = 3061283) B3061283
theorem B4418221 : Blo 2039435 4418221 := bbase (se 3 (by rfl) ⟨828416, by rfl⟩ : syracuseStep 4418221 = 1656833) (by norm_num)
theorem B5890961 : Blo 2039435 5890961 := bstep (se 2 (by rfl) ⟨2209110, by rfl⟩ : syracuseStep 5890961 = 4418221) B4418221
theorem B3927307 : Blo 2039435 3927307 := bstep (se 1 (by rfl) ⟨2945480, by rfl⟩ : syracuseStep 3927307 = 5890961) B5890961
theorem B5236409 : Blo 2039435 5236409 := bstep (se 2 (by rfl) ⟨1963653, by rfl⟩ : syracuseStep 5236409 = 3927307) B3927307
theorem B3490939 : Blo 2039435 3490939 := bstep (se 1 (by rfl) ⟨2618204, by rfl⟩ : syracuseStep 3490939 = 5236409) B5236409
theorem B18618341 : Blo 2039435 18618341 := bstep (se 4 (by rfl) ⟨1745469, by rfl⟩ : syracuseStep 18618341 = 3490939) B3490939
theorem B49648909 : Blo 2039435 49648909 := bstep (se 3 (by rfl) ⟨9309170, by rfl⟩ : syracuseStep 49648909 = 18618341) B18618341
theorem B66198545 : Blo 2039435 66198545 := bstep (se 2 (by rfl) ⟨24824454, by rfl⟩ : syracuseStep 66198545 = 49648909) B49648909
theorem B44132363 : Blo 2039435 44132363 := bstep (se 1 (by rfl) ⟨33099272, by rfl⟩ : syracuseStep 44132363 = 66198545) B66198545
theorem B29421575 : Blo 2039435 29421575 := bstep (se 1 (by rfl) ⟨22066181, by rfl⟩ : syracuseStep 29421575 = 44132363) B44132363
theorem B19614383 : Blo 2039435 19614383 := bstep (se 1 (by rfl) ⟨14710787, by rfl⟩ : syracuseStep 19614383 = 29421575) B29421575
theorem B13076255 : Blo 2039435 13076255 := bstep (se 1 (by rfl) ⟨9807191, by rfl⟩ : syracuseStep 13076255 = 19614383) B19614383
theorem B8717503 : Blo 2039435 8717503 := bstep (se 1 (by rfl) ⟨6538127, by rfl⟩ : syracuseStep 8717503 = 13076255) B13076255
theorem B11623337 : Blo 2039435 11623337 := bstep (se 2 (by rfl) ⟨4358751, by rfl⟩ : syracuseStep 11623337 = 8717503) B8717503
theorem B7748891 : Blo 2039435 7748891 := bstep (se 1 (by rfl) ⟨5811668, by rfl⟩ : syracuseStep 7748891 = 11623337) B11623337
theorem B5165927 : Blo 2039435 5165927 := bstep (se 1 (by rfl) ⟨3874445, by rfl⟩ : syracuseStep 5165927 = 7748891) B7748891
theorem B3443951 : Blo 2039435 3443951 := bstep (se 1 (by rfl) ⟨2582963, by rfl⟩ : syracuseStep 3443951 = 5165927) B5165927
theorem B2295967 : Blo 2039435 2295967 := bstep (se 1 (by rfl) ⟨1721975, by rfl⟩ : syracuseStep 2295967 = 3443951) B3443951
theorem B3061289 : Blo 2039435 3061289 := bstep (se 2 (by rfl) ⟨1147983, by rfl⟩ : syracuseStep 3061289 = 2295967) B2295967
theorem B2040859 : Blo 2039435 2040859 := bstep (se 1 (by rfl) ⟨1530644, by rfl⟩ : syracuseStep 2040859 = 3061289) B3061289
theorem B2327297 : Blo 2039435 2327297 := bbase (se 2 (by rfl) ⟨872736, by rfl⟩ : syracuseStep 2327297 = 1745473) (by norm_num)
theorem B24824501 : Blo 2039435 24824501 := bstep (se 5 (by rfl) ⟨1163648, by rfl⟩ : syracuseStep 24824501 = 2327297) B2327297
theorem B16549667 : Blo 2039435 16549667 := bstep (se 1 (by rfl) ⟨12412250, by rfl⟩ : syracuseStep 16549667 = 24824501) B24824501
theorem B11033111 : Blo 2039435 11033111 := bstep (se 1 (by rfl) ⟨8274833, by rfl⟩ : syracuseStep 11033111 = 16549667) B16549667
theorem B29421629 : Blo 2039435 29421629 := bstep (se 3 (by rfl) ⟨5516555, by rfl⟩ : syracuseStep 29421629 = 11033111) B11033111
theorem B19614419 : Blo 2039435 19614419 := bstep (se 1 (by rfl) ⟨14710814, by rfl⟩ : syracuseStep 19614419 = 29421629) B29421629
theorem B13076279 : Blo 2039435 13076279 := bstep (se 1 (by rfl) ⟨9807209, by rfl⟩ : syracuseStep 13076279 = 19614419) B19614419
theorem B8717519 : Blo 2039435 8717519 := bstep (se 1 (by rfl) ⟨6538139, by rfl⟩ : syracuseStep 8717519 = 13076279) B13076279
theorem B5811679 : Blo 2039435 5811679 := bstep (se 1 (by rfl) ⟨4358759, by rfl⟩ : syracuseStep 5811679 = 8717519) B8717519
theorem B7748905 : Blo 2039435 7748905 := bstep (se 2 (by rfl) ⟨2905839, by rfl⟩ : syracuseStep 7748905 = 5811679) B5811679
theorem B10331873 : Blo 2039435 10331873 := bstep (se 2 (by rfl) ⟨3874452, by rfl⟩ : syracuseStep 10331873 = 7748905) B7748905
theorem B6887915 : Blo 2039435 6887915 := bstep (se 1 (by rfl) ⟨5165936, by rfl⟩ : syracuseStep 6887915 = 10331873) B10331873
theorem B4591943 : Blo 2039435 4591943 := bstep (se 1 (by rfl) ⟨3443957, by rfl⟩ : syracuseStep 4591943 = 6887915) B6887915
theorem B3061295 : Blo 2039435 3061295 := bstep (se 1 (by rfl) ⟨2295971, by rfl⟩ : syracuseStep 3061295 = 4591943) B4591943
theorem B2040863 : Blo 2039435 2040863 := bstep (se 1 (by rfl) ⟨1530647, by rfl⟩ : syracuseStep 2040863 = 3061295) B3061295
theorem B3061301 : Blo 2039435 3061301 := bbase (se 5 (by rfl) ⟨143498, by rfl⟩ : syracuseStep 3061301 = 286997) (by norm_num)
theorem B2040867 : Blo 2039435 2040867 := bstep (se 1 (by rfl) ⟨1530650, by rfl⟩ : syracuseStep 2040867 = 3061301) B3061301
theorem B5165957 : Blo 2039435 5165957 := bbase (se 4 (by rfl) ⟨484308, by rfl⟩ : syracuseStep 5165957 = 968617) (by norm_num)
theorem B3443971 : Blo 2039435 3443971 := bstep (se 1 (by rfl) ⟨2582978, by rfl⟩ : syracuseStep 3443971 = 5165957) B5165957
theorem B4591961 : Blo 2039435 4591961 := bstep (se 2 (by rfl) ⟨1721985, by rfl⟩ : syracuseStep 4591961 = 3443971) B3443971
theorem B3061307 : Blo 2039435 3061307 := bstep (se 1 (by rfl) ⟨2295980, by rfl⟩ : syracuseStep 3061307 = 4591961) B4591961
theorem B2040871 : Blo 2039435 2040871 := bstep (se 1 (by rfl) ⟨1530653, by rfl⟩ : syracuseStep 2040871 = 3061307) B3061307
theorem B2295985 : Blo 2039435 2295985 := bbase (se 2 (by rfl) ⟨860994, by rfl⟩ : syracuseStep 2295985 = 1721989) (by norm_num)
theorem B3061313 : Blo 2039435 3061313 := bstep (se 2 (by rfl) ⟨1147992, by rfl⟩ : syracuseStep 3061313 = 2295985) B2295985
theorem B2040875 : Blo 2039435 2040875 := bstep (se 1 (by rfl) ⟨1530656, by rfl⟩ : syracuseStep 2040875 = 3061313) B3061313
theorem B2179397 : Blo 2039435 2179397 := bbase (se 4 (by rfl) ⟨204318, by rfl⟩ : syracuseStep 2179397 = 408637) (by norm_num)
theorem B5811725 : Blo 2039435 5811725 := bstep (se 3 (by rfl) ⟨1089698, by rfl⟩ : syracuseStep 5811725 = 2179397) B2179397
theorem B3874483 : Blo 2039435 3874483 := bstep (se 1 (by rfl) ⟨2905862, by rfl⟩ : syracuseStep 3874483 = 5811725) B5811725
theorem B5165977 : Blo 2039435 5165977 := bstep (se 2 (by rfl) ⟨1937241, by rfl⟩ : syracuseStep 5165977 = 3874483) B3874483
theorem B6887969 : Blo 2039435 6887969 := bstep (se 2 (by rfl) ⟨2582988, by rfl⟩ : syracuseStep 6887969 = 5165977) B5165977
theorem B4591979 : Blo 2039435 4591979 := bstep (se 1 (by rfl) ⟨3443984, by rfl⟩ : syracuseStep 4591979 = 6887969) B6887969
theorem B3061319 : Blo 2039435 3061319 := bstep (se 1 (by rfl) ⟨2295989, by rfl⟩ : syracuseStep 3061319 = 4591979) B4591979
theorem B2040879 : Blo 2039435 2040879 := bstep (se 1 (by rfl) ⟨1530659, by rfl⟩ : syracuseStep 2040879 = 3061319) B3061319
theorem B3061325 : Blo 2039435 3061325 := bbase (se 3 (by rfl) ⟨573998, by rfl⟩ : syracuseStep 3061325 = 1147997) (by norm_num)
theorem B2040883 : Blo 2039435 2040883 := bstep (se 1 (by rfl) ⟨1530662, by rfl⟩ : syracuseStep 2040883 = 3061325) B3061325
theorem B4591997 : Blo 2039435 4591997 := bbase (se 3 (by rfl) ⟨860999, by rfl⟩ : syracuseStep 4591997 = 1721999) (by norm_num)
theorem B3061331 : Blo 2039435 3061331 := bstep (se 1 (by rfl) ⟨2295998, by rfl⟩ : syracuseStep 3061331 = 4591997) B4591997
theorem B2040887 : Blo 2039435 2040887 := bstep (se 1 (by rfl) ⟨1530665, by rfl⟩ : syracuseStep 2040887 = 3061331) B3061331
theorem B3444005 : Blo 2039435 3444005 := bbase (se 4 (by rfl) ⟨322875, by rfl⟩ : syracuseStep 3444005 = 645751) (by norm_num)
theorem B2296003 : Blo 2039435 2296003 := bstep (se 1 (by rfl) ⟨1722002, by rfl⟩ : syracuseStep 2296003 = 3444005) B3444005
theorem B3061337 : Blo 2039435 3061337 := bstep (se 2 (by rfl) ⟨1148001, by rfl⟩ : syracuseStep 3061337 = 2296003) B2296003
theorem B2040891 : Blo 2039435 2040891 := bstep (se 1 (by rfl) ⟨1530668, by rfl⟩ : syracuseStep 2040891 = 3061337) B3061337
theorem B2905885 : Blo 2039435 2905885 := bbase (se 3 (by rfl) ⟨544853, by rfl⟩ : syracuseStep 2905885 = 1089707) (by norm_num)
theorem B15498053 : Blo 2039435 15498053 := bstep (se 4 (by rfl) ⟨1452942, by rfl⟩ : syracuseStep 15498053 = 2905885) B2905885
theorem B10332035 : Blo 2039435 10332035 := bstep (se 1 (by rfl) ⟨7749026, by rfl⟩ : syracuseStep 10332035 = 15498053) B15498053
theorem B6888023 : Blo 2039435 6888023 := bstep (se 1 (by rfl) ⟨5166017, by rfl⟩ : syracuseStep 6888023 = 10332035) B10332035
theorem B4592015 : Blo 2039435 4592015 := bstep (se 1 (by rfl) ⟨3444011, by rfl⟩ : syracuseStep 4592015 = 6888023) B6888023
theorem B3061343 : Blo 2039435 3061343 := bstep (se 1 (by rfl) ⟨2296007, by rfl⟩ : syracuseStep 3061343 = 4592015) B4592015
theorem B2040895 : Blo 2039435 2040895 := bstep (se 1 (by rfl) ⟨1530671, by rfl⟩ : syracuseStep 2040895 = 3061343) B3061343
theorem B3061349 : Blo 2039435 3061349 := bbase (se 4 (by rfl) ⟨287001, by rfl⟩ : syracuseStep 3061349 = 574003) (by norm_num)
theorem B2040899 : Blo 2039435 2040899 := bstep (se 1 (by rfl) ⟨1530674, by rfl⟩ : syracuseStep 2040899 = 3061349) B3061349
theorem B11033333 : Blo 2039435 11033333 := bbase (se 5 (by rfl) ⟨517187, by rfl⟩ : syracuseStep 11033333 = 1034375) (by norm_num)
theorem B7355555 : Blo 2039435 7355555 := bstep (se 1 (by rfl) ⟨5516666, by rfl⟩ : syracuseStep 7355555 = 11033333) B11033333
theorem B4903703 : Blo 2039435 4903703 := bstep (se 1 (by rfl) ⟨3677777, by rfl⟩ : syracuseStep 4903703 = 7355555) B7355555
theorem B3269135 : Blo 2039435 3269135 := bstep (se 1 (by rfl) ⟨2451851, by rfl⟩ : syracuseStep 3269135 = 4903703) B4903703
theorem B2179423 : Blo 2039435 2179423 := bstep (se 1 (by rfl) ⟨1634567, by rfl⟩ : syracuseStep 2179423 = 3269135) B3269135
theorem B2905897 : Blo 2039435 2905897 := bstep (se 2 (by rfl) ⟨1089711, by rfl⟩ : syracuseStep 2905897 = 2179423) B2179423
theorem B3874529 : Blo 2039435 3874529 := bstep (se 2 (by rfl) ⟨1452948, by rfl⟩ : syracuseStep 3874529 = 2905897) B2905897
theorem B2583019 : Blo 2039435 2583019 := bstep (se 1 (by rfl) ⟨1937264, by rfl⟩ : syracuseStep 2583019 = 3874529) B3874529
theorem B3444025 : Blo 2039435 3444025 := bstep (se 2 (by rfl) ⟨1291509, by rfl⟩ : syracuseStep 3444025 = 2583019) B2583019
theorem B4592033 : Blo 2039435 4592033 := bstep (se 2 (by rfl) ⟨1722012, by rfl⟩ : syracuseStep 4592033 = 3444025) B3444025
theorem B3061355 : Blo 2039435 3061355 := bstep (se 1 (by rfl) ⟨2296016, by rfl⟩ : syracuseStep 3061355 = 4592033) B4592033
theorem B2040903 : Blo 2039435 2040903 := bstep (se 1 (by rfl) ⟨1530677, by rfl⟩ : syracuseStep 2040903 = 3061355) B3061355
theorem B2296021 : Blo 2039435 2296021 := bbase (se 7 (by rfl) ⟨26906, by rfl⟩ : syracuseStep 2296021 = 53813) (by norm_num)
theorem B3061361 : Blo 2039435 3061361 := bstep (se 2 (by rfl) ⟨1148010, by rfl⟩ : syracuseStep 3061361 = 2296021) B2296021
theorem B2040907 : Blo 2039435 2040907 := bstep (se 1 (by rfl) ⟨1530680, by rfl⟩ : syracuseStep 2040907 = 3061361) B3061361
theorem B2583029 : Blo 2039435 2583029 := bbase (se 5 (by rfl) ⟨121079, by rfl⟩ : syracuseStep 2583029 = 242159) (by norm_num)
theorem B6888077 : Blo 2039435 6888077 := bstep (se 3 (by rfl) ⟨1291514, by rfl⟩ : syracuseStep 6888077 = 2583029) B2583029
theorem B4592051 : Blo 2039435 4592051 := bstep (se 1 (by rfl) ⟨3444038, by rfl⟩ : syracuseStep 4592051 = 6888077) B6888077
theorem B3061367 : Blo 2039435 3061367 := bstep (se 1 (by rfl) ⟨2296025, by rfl⟩ : syracuseStep 3061367 = 4592051) B4592051
theorem B2040911 : Blo 2039435 2040911 := bstep (se 1 (by rfl) ⟨1530683, by rfl⟩ : syracuseStep 2040911 = 3061367) B3061367
theorem B3061373 : Blo 2039435 3061373 := bbase (se 3 (by rfl) ⟨574007, by rfl⟩ : syracuseStep 3061373 = 1148015) (by norm_num)
theorem B2040915 : Blo 2039435 2040915 := bstep (se 1 (by rfl) ⟨1530686, by rfl⟩ : syracuseStep 2040915 = 3061373) B3061373
theorem B4592069 : Blo 2039435 4592069 := bbase (se 4 (by rfl) ⟨430506, by rfl⟩ : syracuseStep 4592069 = 861013) (by norm_num)
theorem B3061379 : Blo 2039435 3061379 := bstep (se 1 (by rfl) ⟨2296034, by rfl⟩ : syracuseStep 3061379 = 4592069) B4592069
theorem B2040919 : Blo 2039435 2040919 := bstep (se 1 (by rfl) ⟨1530689, by rfl⟩ : syracuseStep 2040919 = 3061379) B3061379
theorem B3677813 : Blo 2039435 3677813 := bbase (se 5 (by rfl) ⟨172397, by rfl⟩ : syracuseStep 3677813 = 344795) (by norm_num)
theorem B2451875 : Blo 2039435 2451875 := bstep (se 1 (by rfl) ⟨1838906, by rfl⟩ : syracuseStep 2451875 = 3677813) B3677813
theorem B6538333 : Blo 2039435 6538333 := bstep (se 3 (by rfl) ⟨1225937, by rfl⟩ : syracuseStep 6538333 = 2451875) B2451875
theorem B8717777 : Blo 2039435 8717777 := bstep (se 2 (by rfl) ⟨3269166, by rfl⟩ : syracuseStep 8717777 = 6538333) B6538333
theorem B5811851 : Blo 2039435 5811851 := bstep (se 1 (by rfl) ⟨4358888, by rfl⟩ : syracuseStep 5811851 = 8717777) B8717777
theorem B3874567 : Blo 2039435 3874567 := bstep (se 1 (by rfl) ⟨2905925, by rfl⟩ : syracuseStep 3874567 = 5811851) B5811851
theorem B5166089 : Blo 2039435 5166089 := bstep (se 2 (by rfl) ⟨1937283, by rfl⟩ : syracuseStep 5166089 = 3874567) B3874567
theorem B3444059 : Blo 2039435 3444059 := bstep (se 1 (by rfl) ⟨2583044, by rfl⟩ : syracuseStep 3444059 = 5166089) B5166089
theorem B2296039 : Blo 2039435 2296039 := bstep (se 1 (by rfl) ⟨1722029, by rfl⟩ : syracuseStep 2296039 = 3444059) B3444059
theorem B3061385 : Blo 2039435 3061385 := bstep (se 2 (by rfl) ⟨1148019, by rfl⟩ : syracuseStep 3061385 = 2296039) B2296039
theorem B2040923 : Blo 2039435 2040923 := bstep (se 1 (by rfl) ⟨1530692, by rfl⟩ : syracuseStep 2040923 = 3061385) B3061385
theorem B10332197 : Blo 2039435 10332197 := bbase (se 4 (by rfl) ⟨968643, by rfl⟩ : syracuseStep 10332197 = 1937287) (by norm_num)
theorem B6888131 : Blo 2039435 6888131 := bstep (se 1 (by rfl) ⟨5166098, by rfl⟩ : syracuseStep 6888131 = 10332197) B10332197
theorem B4592087 : Blo 2039435 4592087 := bstep (se 1 (by rfl) ⟨3444065, by rfl⟩ : syracuseStep 4592087 = 6888131) B6888131
theorem B3061391 : Blo 2039435 3061391 := bstep (se 1 (by rfl) ⟨2296043, by rfl⟩ : syracuseStep 3061391 = 4592087) B4592087
theorem B2040927 : Blo 2039435 2040927 := bstep (se 1 (by rfl) ⟨1530695, by rfl⟩ : syracuseStep 2040927 = 3061391) B3061391
theorem B3061397 : Blo 2039435 3061397 := bbase (se 6 (by rfl) ⟨71751, by rfl⟩ : syracuseStep 3061397 = 143503) (by norm_num)
theorem B2040931 : Blo 2039435 2040931 := bstep (se 1 (by rfl) ⟨1530698, by rfl⟩ : syracuseStep 2040931 = 3061397) B3061397
theorem B2451889 : Blo 2039435 2451889 := bbase (se 2 (by rfl) ⟨919458, by rfl⟩ : syracuseStep 2451889 = 1838917) (by norm_num)
theorem B13076741 : Blo 2039435 13076741 := bstep (se 4 (by rfl) ⟨1225944, by rfl⟩ : syracuseStep 13076741 = 2451889) B2451889
theorem B8717827 : Blo 2039435 8717827 := bstep (se 1 (by rfl) ⟨6538370, by rfl⟩ : syracuseStep 8717827 = 13076741) B13076741
theorem B11623769 : Blo 2039435 11623769 := bstep (se 2 (by rfl) ⟨4358913, by rfl⟩ : syracuseStep 11623769 = 8717827) B8717827
theorem B7749179 : Blo 2039435 7749179 := bstep (se 1 (by rfl) ⟨5811884, by rfl⟩ : syracuseStep 7749179 = 11623769) B11623769
theorem B5166119 : Blo 2039435 5166119 := bstep (se 1 (by rfl) ⟨3874589, by rfl⟩ : syracuseStep 5166119 = 7749179) B7749179
theorem B3444079 : Blo 2039435 3444079 := bstep (se 1 (by rfl) ⟨2583059, by rfl⟩ : syracuseStep 3444079 = 5166119) B5166119
theorem B4592105 : Blo 2039435 4592105 := bstep (se 2 (by rfl) ⟨1722039, by rfl⟩ : syracuseStep 4592105 = 3444079) B3444079
theorem B3061403 : Blo 2039435 3061403 := bstep (se 1 (by rfl) ⟨2296052, by rfl⟩ : syracuseStep 3061403 = 4592105) B4592105
theorem B2040935 : Blo 2039435 2040935 := bstep (se 1 (by rfl) ⟨1530701, by rfl⟩ : syracuseStep 2040935 = 3061403) B3061403
theorem B2296057 : Blo 2039435 2296057 := bbase (se 2 (by rfl) ⟨861021, by rfl⟩ : syracuseStep 2296057 = 1722043) (by norm_num)
theorem B3061409 : Blo 2039435 3061409 := bstep (se 2 (by rfl) ⟨1148028, by rfl⟩ : syracuseStep 3061409 = 2296057) B2296057
theorem B2040939 : Blo 2039435 2040939 := bstep (se 1 (by rfl) ⟨1530704, by rfl⟩ : syracuseStep 2040939 = 3061409) B3061409
theorem B8717861 : Blo 2039435 8717861 := bbase (se 4 (by rfl) ⟨817299, by rfl⟩ : syracuseStep 8717861 = 1634599) (by norm_num)
theorem B5811907 : Blo 2039435 5811907 := bstep (se 1 (by rfl) ⟨4358930, by rfl⟩ : syracuseStep 5811907 = 8717861) B8717861
theorem B7749209 : Blo 2039435 7749209 := bstep (se 2 (by rfl) ⟨2905953, by rfl⟩ : syracuseStep 7749209 = 5811907) B5811907
theorem B5166139 : Blo 2039435 5166139 := bstep (se 1 (by rfl) ⟨3874604, by rfl⟩ : syracuseStep 5166139 = 7749209) B7749209
theorem B6888185 : Blo 2039435 6888185 := bstep (se 2 (by rfl) ⟨2583069, by rfl⟩ : syracuseStep 6888185 = 5166139) B5166139
theorem B4592123 : Blo 2039435 4592123 := bstep (se 1 (by rfl) ⟨3444092, by rfl⟩ : syracuseStep 4592123 = 6888185) B6888185
theorem B3061415 : Blo 2039435 3061415 := bstep (se 1 (by rfl) ⟨2296061, by rfl⟩ : syracuseStep 3061415 = 4592123) B4592123
theorem B2040943 : Blo 2039435 2040943 := bstep (se 1 (by rfl) ⟨1530707, by rfl⟩ : syracuseStep 2040943 = 3061415) B3061415
theorem B3061421 : Blo 2039435 3061421 := bbase (se 3 (by rfl) ⟨574016, by rfl⟩ : syracuseStep 3061421 = 1148033) (by norm_num)
theorem B2040947 : Blo 2039435 2040947 := bstep (se 1 (by rfl) ⟨1530710, by rfl⟩ : syracuseStep 2040947 = 3061421) B3061421
theorem B4592141 : Blo 2039435 4592141 := bbase (se 3 (by rfl) ⟨861026, by rfl⟩ : syracuseStep 4592141 = 1722053) (by norm_num)
theorem B3061427 : Blo 2039435 3061427 := bstep (se 1 (by rfl) ⟨2296070, by rfl⟩ : syracuseStep 3061427 = 4592141) B4592141
theorem B2040951 : Blo 2039435 2040951 := bstep (se 1 (by rfl) ⟨1530713, by rfl⟩ : syracuseStep 2040951 = 3061427) B3061427
theorem B2583085 : Blo 2039435 2583085 := bbase (se 3 (by rfl) ⟨484328, by rfl⟩ : syracuseStep 2583085 = 968657) (by norm_num)
theorem B3444113 : Blo 2039435 3444113 := bstep (se 2 (by rfl) ⟨1291542, by rfl⟩ : syracuseStep 3444113 = 2583085) B2583085
theorem B2296075 : Blo 2039435 2296075 := bstep (se 1 (by rfl) ⟨1722056, by rfl⟩ : syracuseStep 2296075 = 3444113) B3444113
theorem B3061433 : Blo 2039435 3061433 := bstep (se 2 (by rfl) ⟨1148037, by rfl⟩ : syracuseStep 3061433 = 2296075) B2296075
theorem B2040955 : Blo 2039435 2040955 := bstep (se 1 (by rfl) ⟨1530716, by rfl⟩ : syracuseStep 2040955 = 3061433) B3061433
theorem B18619253 : Blo 2039435 18619253 := bbase (se 5 (by rfl) ⟨872777, by rfl⟩ : syracuseStep 18619253 = 1745555) (by norm_num)
theorem B12412835 : Blo 2039435 12412835 := bstep (se 1 (by rfl) ⟨9309626, by rfl⟩ : syracuseStep 12412835 = 18619253) B18619253
theorem B8275223 : Blo 2039435 8275223 := bstep (se 1 (by rfl) ⟨6206417, by rfl⟩ : syracuseStep 8275223 = 12412835) B12412835
theorem B5516815 : Blo 2039435 5516815 := bstep (se 1 (by rfl) ⟨4137611, by rfl⟩ : syracuseStep 5516815 = 8275223) B8275223
theorem B7355753 : Blo 2039435 7355753 := bstep (se 2 (by rfl) ⟨2758407, by rfl⟩ : syracuseStep 7355753 = 5516815) B5516815
theorem B4903835 : Blo 2039435 4903835 := bstep (se 1 (by rfl) ⟨3677876, by rfl⟩ : syracuseStep 4903835 = 7355753) B7355753
theorem B13076893 : Blo 2039435 13076893 := bstep (se 3 (by rfl) ⟨2451917, by rfl⟩ : syracuseStep 13076893 = 4903835) B4903835
theorem B17435857 : Blo 2039435 17435857 := bstep (se 2 (by rfl) ⟨6538446, by rfl⟩ : syracuseStep 17435857 = 13076893) B13076893
theorem B23247809 : Blo 2039435 23247809 := bstep (se 2 (by rfl) ⟨8717928, by rfl⟩ : syracuseStep 23247809 = 17435857) B17435857
theorem B15498539 : Blo 2039435 15498539 := bstep (se 1 (by rfl) ⟨11623904, by rfl⟩ : syracuseStep 15498539 = 23247809) B23247809
theorem B10332359 : Blo 2039435 10332359 := bstep (se 1 (by rfl) ⟨7749269, by rfl⟩ : syracuseStep 10332359 = 15498539) B15498539
theorem B6888239 : Blo 2039435 6888239 := bstep (se 1 (by rfl) ⟨5166179, by rfl⟩ : syracuseStep 6888239 = 10332359) B10332359
theorem B4592159 : Blo 2039435 4592159 := bstep (se 1 (by rfl) ⟨3444119, by rfl⟩ : syracuseStep 4592159 = 6888239) B6888239
theorem B3061439 : Blo 2039435 3061439 := bstep (se 1 (by rfl) ⟨2296079, by rfl⟩ : syracuseStep 3061439 = 4592159) B4592159
theorem B2040959 : Blo 2039435 2040959 := bstep (se 1 (by rfl) ⟨1530719, by rfl⟩ : syracuseStep 2040959 = 3061439) B3061439
theorem B3061445 : Blo 2039435 3061445 := bbase (se 4 (by rfl) ⟨287010, by rfl⟩ : syracuseStep 3061445 = 574021) (by norm_num)
theorem B2040963 : Blo 2039435 2040963 := bstep (se 1 (by rfl) ⟨1530722, by rfl⟩ : syracuseStep 2040963 = 3061445) B3061445
theorem B3444133 : Blo 2039435 3444133 := bbase (se 4 (by rfl) ⟨322887, by rfl⟩ : syracuseStep 3444133 = 645775) (by norm_num)
theorem B4592177 : Blo 2039435 4592177 := bstep (se 2 (by rfl) ⟨1722066, by rfl⟩ : syracuseStep 4592177 = 3444133) B3444133
theorem B3061451 : Blo 2039435 3061451 := bstep (se 1 (by rfl) ⟨2296088, by rfl⟩ : syracuseStep 3061451 = 4592177) B4592177
theorem B2040967 : Blo 2039435 2040967 := bstep (se 1 (by rfl) ⟨1530725, by rfl⟩ : syracuseStep 2040967 = 3061451) B3061451
theorem B2296093 : Blo 2039435 2296093 := bbase (se 3 (by rfl) ⟨430517, by rfl⟩ : syracuseStep 2296093 = 861035) (by norm_num)
theorem B3061457 : Blo 2039435 3061457 := bstep (se 2 (by rfl) ⟨1148046, by rfl⟩ : syracuseStep 3061457 = 2296093) B2296093
theorem B2040971 : Blo 2039435 2040971 := bstep (se 1 (by rfl) ⟨1530728, by rfl⟩ : syracuseStep 2040971 = 3061457) B3061457
theorem B6888293 : Blo 2039435 6888293 := bbase (se 4 (by rfl) ⟨645777, by rfl⟩ : syracuseStep 6888293 = 1291555) (by norm_num)
theorem B4592195 : Blo 2039435 4592195 := bstep (se 1 (by rfl) ⟨3444146, by rfl⟩ : syracuseStep 4592195 = 6888293) B6888293
theorem B3061463 : Blo 2039435 3061463 := bstep (se 1 (by rfl) ⟨2296097, by rfl⟩ : syracuseStep 3061463 = 4592195) B4592195
theorem B2040975 : Blo 2039435 2040975 := bstep (se 1 (by rfl) ⟨1530731, by rfl⟩ : syracuseStep 2040975 = 3061463) B3061463
theorem B3061469 : Blo 2039435 3061469 := bbase (se 3 (by rfl) ⟨574025, by rfl⟩ : syracuseStep 3061469 = 1148051) (by norm_num)
theorem B2040979 : Blo 2039435 2040979 := bstep (se 1 (by rfl) ⟨1530734, by rfl⟩ : syracuseStep 2040979 = 3061469) B3061469
theorem B4592213 : Blo 2039435 4592213 := bbase (se 8 (by rfl) ⟨26907, by rfl⟩ : syracuseStep 4592213 = 53815) (by norm_num)
theorem B3061475 : Blo 2039435 3061475 := bstep (se 1 (by rfl) ⟨2296106, by rfl⟩ : syracuseStep 3061475 = 4592213) B4592213
theorem B2040983 : Blo 2039435 2040983 := bstep (se 1 (by rfl) ⟨1530737, by rfl⟩ : syracuseStep 2040983 = 3061475) B3061475
theorem B3269269 : Blo 2039435 3269269 := bbase (se 6 (by rfl) ⟨76623, by rfl⟩ : syracuseStep 3269269 = 153247) (by norm_num)
theorem B4359025 : Blo 2039435 4359025 := bstep (se 2 (by rfl) ⟨1634634, by rfl⟩ : syracuseStep 4359025 = 3269269) B3269269
theorem B5812033 : Blo 2039435 5812033 := bstep (se 2 (by rfl) ⟨2179512, by rfl⟩ : syracuseStep 5812033 = 4359025) B4359025
theorem B7749377 : Blo 2039435 7749377 := bstep (se 2 (by rfl) ⟨2906016, by rfl⟩ : syracuseStep 7749377 = 5812033) B5812033
theorem B5166251 : Blo 2039435 5166251 := bstep (se 1 (by rfl) ⟨3874688, by rfl⟩ : syracuseStep 5166251 = 7749377) B7749377
theorem B3444167 : Blo 2039435 3444167 := bstep (se 1 (by rfl) ⟨2583125, by rfl⟩ : syracuseStep 3444167 = 5166251) B5166251
theorem B2296111 : Blo 2039435 2296111 := bstep (se 1 (by rfl) ⟨1722083, by rfl⟩ : syracuseStep 2296111 = 3444167) B3444167
theorem B3061481 : Blo 2039435 3061481 := bstep (se 2 (by rfl) ⟨1148055, by rfl⟩ : syracuseStep 3061481 = 2296111) B2296111
theorem B2040987 : Blo 2039435 2040987 := bstep (se 1 (by rfl) ⟨1530740, by rfl⟩ : syracuseStep 2040987 = 3061481) B3061481
theorem B26154197 : Blo 2039435 26154197 := bbase (se 7 (by rfl) ⟨306494, by rfl⟩ : syracuseStep 26154197 = 612989) (by norm_num)
theorem B17436131 : Blo 2039435 17436131 := bstep (se 1 (by rfl) ⟨13077098, by rfl⟩ : syracuseStep 17436131 = 26154197) B26154197
theorem B11624087 : Blo 2039435 11624087 := bstep (se 1 (by rfl) ⟨8718065, by rfl⟩ : syracuseStep 11624087 = 17436131) B17436131
theorem B7749391 : Blo 2039435 7749391 := bstep (se 1 (by rfl) ⟨5812043, by rfl⟩ : syracuseStep 7749391 = 11624087) B11624087
theorem B10332521 : Blo 2039435 10332521 := bstep (se 2 (by rfl) ⟨3874695, by rfl⟩ : syracuseStep 10332521 = 7749391) B7749391
theorem B6888347 : Blo 2039435 6888347 := bstep (se 1 (by rfl) ⟨5166260, by rfl⟩ : syracuseStep 6888347 = 10332521) B10332521
theorem B4592231 : Blo 2039435 4592231 := bstep (se 1 (by rfl) ⟨3444173, by rfl⟩ : syracuseStep 4592231 = 6888347) B6888347
theorem B3061487 : Blo 2039435 3061487 := bstep (se 1 (by rfl) ⟨2296115, by rfl⟩ : syracuseStep 3061487 = 4592231) B4592231
theorem B2040991 : Blo 2039435 2040991 := bstep (se 1 (by rfl) ⟨1530743, by rfl⟩ : syracuseStep 2040991 = 3061487) B3061487
theorem B3061493 : Blo 2039435 3061493 := bbase (se 5 (by rfl) ⟨143507, by rfl⟩ : syracuseStep 3061493 = 287015) (by norm_num)
theorem B2040995 : Blo 2039435 2040995 := bstep (se 1 (by rfl) ⟨1530746, by rfl⟩ : syracuseStep 2040995 = 3061493) B3061493
theorem B8718101 : Blo 2039435 8718101 := bbase (se 6 (by rfl) ⟨204330, by rfl⟩ : syracuseStep 8718101 = 408661) (by norm_num)
theorem B5812067 : Blo 2039435 5812067 := bstep (se 1 (by rfl) ⟨4359050, by rfl⟩ : syracuseStep 5812067 = 8718101) B8718101
theorem B3874711 : Blo 2039435 3874711 := bstep (se 1 (by rfl) ⟨2906033, by rfl⟩ : syracuseStep 3874711 = 5812067) B5812067
theorem B5166281 : Blo 2039435 5166281 := bstep (se 2 (by rfl) ⟨1937355, by rfl⟩ : syracuseStep 5166281 = 3874711) B3874711
theorem B3444187 : Blo 2039435 3444187 := bstep (se 1 (by rfl) ⟨2583140, by rfl⟩ : syracuseStep 3444187 = 5166281) B5166281
theorem B4592249 : Blo 2039435 4592249 := bstep (se 2 (by rfl) ⟨1722093, by rfl⟩ : syracuseStep 4592249 = 3444187) B3444187
theorem B3061499 : Blo 2039435 3061499 := bstep (se 1 (by rfl) ⟨2296124, by rfl⟩ : syracuseStep 3061499 = 4592249) B4592249
theorem B2040999 : Blo 2039435 2040999 := bstep (se 1 (by rfl) ⟨1530749, by rfl⟩ : syracuseStep 2040999 = 3061499) B3061499
theorem B2296129 : Blo 2039435 2296129 := bbase (se 2 (by rfl) ⟨861048, by rfl⟩ : syracuseStep 2296129 = 1722097) (by norm_num)
theorem B3061505 : Blo 2039435 3061505 := bstep (se 2 (by rfl) ⟨1148064, by rfl⟩ : syracuseStep 3061505 = 2296129) B2296129
theorem B2041003 : Blo 2039435 2041003 := bstep (se 1 (by rfl) ⟨1530752, by rfl⟩ : syracuseStep 2041003 = 3061505) B3061505
theorem B5166301 : Blo 2039435 5166301 := bbase (se 3 (by rfl) ⟨968681, by rfl⟩ : syracuseStep 5166301 = 1937363) (by norm_num)
theorem B6888401 : Blo 2039435 6888401 := bstep (se 2 (by rfl) ⟨2583150, by rfl⟩ : syracuseStep 6888401 = 5166301) B5166301
theorem B4592267 : Blo 2039435 4592267 := bstep (se 1 (by rfl) ⟨3444200, by rfl⟩ : syracuseStep 4592267 = 6888401) B6888401
theorem B3061511 : Blo 2039435 3061511 := bstep (se 1 (by rfl) ⟨2296133, by rfl⟩ : syracuseStep 3061511 = 4592267) B4592267
theorem B2041007 : Blo 2039435 2041007 := bstep (se 1 (by rfl) ⟨1530755, by rfl⟩ : syracuseStep 2041007 = 3061511) B3061511
theorem B3061517 : Blo 2039435 3061517 := bbase (se 3 (by rfl) ⟨574034, by rfl⟩ : syracuseStep 3061517 = 1148069) (by norm_num)
theorem B2041011 : Blo 2039435 2041011 := bstep (se 1 (by rfl) ⟨1530758, by rfl⟩ : syracuseStep 2041011 = 3061517) B3061517
theorem B4592285 : Blo 2039435 4592285 := bbase (se 3 (by rfl) ⟨861053, by rfl⟩ : syracuseStep 4592285 = 1722107) (by norm_num)
theorem B3061523 : Blo 2039435 3061523 := bstep (se 1 (by rfl) ⟨2296142, by rfl⟩ : syracuseStep 3061523 = 4592285) B4592285
theorem B2041015 : Blo 2039435 2041015 := bstep (se 1 (by rfl) ⟨1530761, by rfl⟩ : syracuseStep 2041015 = 3061523) B3061523
theorem B3444221 : Blo 2039435 3444221 := bbase (se 3 (by rfl) ⟨645791, by rfl⟩ : syracuseStep 3444221 = 1291583) (by norm_num)
theorem B2296147 : Blo 2039435 2296147 := bstep (se 1 (by rfl) ⟨1722110, by rfl⟩ : syracuseStep 2296147 = 3444221) B3444221
theorem B3061529 : Blo 2039435 3061529 := bstep (se 2 (by rfl) ⟨1148073, by rfl⟩ : syracuseStep 3061529 = 2296147) B2296147
theorem B2041019 : Blo 2039435 2041019 := bstep (se 1 (by rfl) ⟨1530764, by rfl⟩ : syracuseStep 2041019 = 3061529) B3061529
theorem B4359101 : Blo 2039435 4359101 := bbase (se 3 (by rfl) ⟨817331, by rfl⟩ : syracuseStep 4359101 = 1634663) (by norm_num)
theorem B11624269 : Blo 2039435 11624269 := bstep (se 3 (by rfl) ⟨2179550, by rfl⟩ : syracuseStep 11624269 = 4359101) B4359101
theorem B15499025 : Blo 2039435 15499025 := bstep (se 2 (by rfl) ⟨5812134, by rfl⟩ : syracuseStep 15499025 = 11624269) B11624269
theorem B10332683 : Blo 2039435 10332683 := bstep (se 1 (by rfl) ⟨7749512, by rfl⟩ : syracuseStep 10332683 = 15499025) B15499025
theorem B6888455 : Blo 2039435 6888455 := bstep (se 1 (by rfl) ⟨5166341, by rfl⟩ : syracuseStep 6888455 = 10332683) B10332683
theorem B4592303 : Blo 2039435 4592303 := bstep (se 1 (by rfl) ⟨3444227, by rfl⟩ : syracuseStep 4592303 = 6888455) B6888455
theorem B3061535 : Blo 2039435 3061535 := bstep (se 1 (by rfl) ⟨2296151, by rfl⟩ : syracuseStep 3061535 = 4592303) B4592303
theorem B2041023 : Blo 2039435 2041023 := bstep (se 1 (by rfl) ⟨1530767, by rfl⟩ : syracuseStep 2041023 = 3061535) B3061535
theorem B3061541 : Blo 2039435 3061541 := bbase (se 4 (by rfl) ⟨287019, by rfl⟩ : syracuseStep 3061541 = 574039) (by norm_num)
theorem B2041027 : Blo 2039435 2041027 := bstep (se 1 (by rfl) ⟨1530770, by rfl⟩ : syracuseStep 2041027 = 3061541) B3061541
theorem B2583181 : Blo 2039435 2583181 := bbase (se 3 (by rfl) ⟨484346, by rfl⟩ : syracuseStep 2583181 = 968693) (by norm_num)
theorem B3444241 : Blo 2039435 3444241 := bstep (se 2 (by rfl) ⟨1291590, by rfl⟩ : syracuseStep 3444241 = 2583181) B2583181
theorem B4592321 : Blo 2039435 4592321 := bstep (se 2 (by rfl) ⟨1722120, by rfl⟩ : syracuseStep 4592321 = 3444241) B3444241
theorem B3061547 : Blo 2039435 3061547 := bstep (se 1 (by rfl) ⟨2296160, by rfl⟩ : syracuseStep 3061547 = 4592321) B4592321
theorem B2041031 : Blo 2039435 2041031 := bstep (se 1 (by rfl) ⟨1530773, by rfl⟩ : syracuseStep 2041031 = 3061547) B3061547
theorem B2296165 : Blo 2039435 2296165 := bbase (se 4 (by rfl) ⟨215265, by rfl⟩ : syracuseStep 2296165 = 430531) (by norm_num)
theorem B3061553 : Blo 2039435 3061553 := bstep (se 2 (by rfl) ⟨1148082, by rfl⟩ : syracuseStep 3061553 = 2296165) B2296165
theorem B2041035 : Blo 2039435 2041035 := bstep (se 1 (by rfl) ⟨1530776, by rfl⟩ : syracuseStep 2041035 = 3061553) B3061553
theorem B5812181 : Blo 2039435 5812181 := bbase (se 7 (by rfl) ⟨68111, by rfl⟩ : syracuseStep 5812181 = 136223) (by norm_num)
theorem B3874787 : Blo 2039435 3874787 := bstep (se 1 (by rfl) ⟨2906090, by rfl⟩ : syracuseStep 3874787 = 5812181) B5812181
theorem B2583191 : Blo 2039435 2583191 := bstep (se 1 (by rfl) ⟨1937393, by rfl⟩ : syracuseStep 2583191 = 3874787) B3874787
theorem B6888509 : Blo 2039435 6888509 := bstep (se 3 (by rfl) ⟨1291595, by rfl⟩ : syracuseStep 6888509 = 2583191) B2583191
theorem B4592339 : Blo 2039435 4592339 := bstep (se 1 (by rfl) ⟨3444254, by rfl⟩ : syracuseStep 4592339 = 6888509) B6888509
theorem B3061559 : Blo 2039435 3061559 := bstep (se 1 (by rfl) ⟨2296169, by rfl⟩ : syracuseStep 3061559 = 4592339) B4592339
theorem B2041039 : Blo 2039435 2041039 := bstep (se 1 (by rfl) ⟨1530779, by rfl⟩ : syracuseStep 2041039 = 3061559) B3061559
theorem B3061565 : Blo 2039435 3061565 := bbase (se 3 (by rfl) ⟨574043, by rfl⟩ : syracuseStep 3061565 = 1148087) (by norm_num)
theorem B2041043 : Blo 2039435 2041043 := bstep (se 1 (by rfl) ⟨1530782, by rfl⟩ : syracuseStep 2041043 = 3061565) B3061565
theorem B4592357 : Blo 2039435 4592357 := bbase (se 4 (by rfl) ⟨430533, by rfl⟩ : syracuseStep 4592357 = 861067) (by norm_num)
theorem B3061571 : Blo 2039435 3061571 := bstep (se 1 (by rfl) ⟨2296178, by rfl⟩ : syracuseStep 3061571 = 4592357) B4592357
theorem B2041047 : Blo 2039435 2041047 := bstep (se 1 (by rfl) ⟨1530785, by rfl⟩ : syracuseStep 2041047 = 3061571) B3061571
theorem B5166413 : Blo 2039435 5166413 := bbase (se 3 (by rfl) ⟨968702, by rfl⟩ : syracuseStep 5166413 = 1937405) (by norm_num)
theorem B3444275 : Blo 2039435 3444275 := bstep (se 1 (by rfl) ⟨2583206, by rfl⟩ : syracuseStep 3444275 = 5166413) B5166413
theorem B2296183 : Blo 2039435 2296183 := bstep (se 1 (by rfl) ⟨1722137, by rfl⟩ : syracuseStep 2296183 = 3444275) B3444275
theorem B3061577 : Blo 2039435 3061577 := bstep (se 2 (by rfl) ⟨1148091, by rfl⟩ : syracuseStep 3061577 = 2296183) B2296183
theorem B2041051 : Blo 2039435 2041051 := bstep (se 1 (by rfl) ⟨1530788, by rfl⟩ : syracuseStep 2041051 = 3061577) B3061577
theorem B2179585 : Blo 2039435 2179585 := bbase (se 2 (by rfl) ⟨817344, by rfl⟩ : syracuseStep 2179585 = 1634689) (by norm_num)
theorem B2906113 : Blo 2039435 2906113 := bstep (se 2 (by rfl) ⟨1089792, by rfl⟩ : syracuseStep 2906113 = 2179585) B2179585
theorem B3874817 : Blo 2039435 3874817 := bstep (se 2 (by rfl) ⟨1453056, by rfl⟩ : syracuseStep 3874817 = 2906113) B2906113
theorem B10332845 : Blo 2039435 10332845 := bstep (se 3 (by rfl) ⟨1937408, by rfl⟩ : syracuseStep 10332845 = 3874817) B3874817
theorem B6888563 : Blo 2039435 6888563 := bstep (se 1 (by rfl) ⟨5166422, by rfl⟩ : syracuseStep 6888563 = 10332845) B10332845
theorem B4592375 : Blo 2039435 4592375 := bstep (se 1 (by rfl) ⟨3444281, by rfl⟩ : syracuseStep 4592375 = 6888563) B6888563
theorem B3061583 : Blo 2039435 3061583 := bstep (se 1 (by rfl) ⟨2296187, by rfl⟩ : syracuseStep 3061583 = 4592375) B4592375
theorem B2041055 : Blo 2039435 2041055 := bstep (se 1 (by rfl) ⟨1530791, by rfl⟩ : syracuseStep 2041055 = 3061583) B3061583
theorem B3061589 : Blo 2039435 3061589 := bbase (se 9 (by rfl) ⟨8969, by rfl⟩ : syracuseStep 3061589 = 17939) (by norm_num)
theorem B2041059 : Blo 2039435 2041059 := bstep (se 1 (by rfl) ⟨1530794, by rfl⟩ : syracuseStep 2041059 = 3061589) B3061589
theorem B2758549 : Blo 2039435 2758549 := bbase (se 6 (by rfl) ⟨64653, by rfl⟩ : syracuseStep 2758549 = 129307) (by norm_num)
theorem B3678065 : Blo 2039435 3678065 := bstep (se 2 (by rfl) ⟨1379274, by rfl⟩ : syracuseStep 3678065 = 2758549) B2758549
theorem B2452043 : Blo 2039435 2452043 := bstep (se 1 (by rfl) ⟨1839032, by rfl⟩ : syracuseStep 2452043 = 3678065) B3678065
theorem B6538781 : Blo 2039435 6538781 := bstep (se 3 (by rfl) ⟨1226021, by rfl⟩ : syracuseStep 6538781 = 2452043) B2452043
theorem B4359187 : Blo 2039435 4359187 := bstep (se 1 (by rfl) ⟨3269390, by rfl⟩ : syracuseStep 4359187 = 6538781) B6538781
theorem B5812249 : Blo 2039435 5812249 := bstep (se 2 (by rfl) ⟨2179593, by rfl⟩ : syracuseStep 5812249 = 4359187) B4359187
theorem B7749665 : Blo 2039435 7749665 := bstep (se 2 (by rfl) ⟨2906124, by rfl⟩ : syracuseStep 7749665 = 5812249) B5812249
theorem B5166443 : Blo 2039435 5166443 := bstep (se 1 (by rfl) ⟨3874832, by rfl⟩ : syracuseStep 5166443 = 7749665) B7749665
theorem B3444295 : Blo 2039435 3444295 := bstep (se 1 (by rfl) ⟨2583221, by rfl⟩ : syracuseStep 3444295 = 5166443) B5166443
theorem B4592393 : Blo 2039435 4592393 := bstep (se 2 (by rfl) ⟨1722147, by rfl⟩ : syracuseStep 4592393 = 3444295) B3444295
theorem B3061595 : Blo 2039435 3061595 := bstep (se 1 (by rfl) ⟨2296196, by rfl⟩ : syracuseStep 3061595 = 4592393) B4592393
theorem B2041063 : Blo 2039435 2041063 := bstep (se 1 (by rfl) ⟨1530797, by rfl⟩ : syracuseStep 2041063 = 3061595) B3061595
theorem B2296201 : Blo 2039435 2296201 := bbase (se 2 (by rfl) ⟨861075, by rfl⟩ : syracuseStep 2296201 = 1722151) (by norm_num)
theorem B3061601 : Blo 2039435 3061601 := bstep (se 2 (by rfl) ⟨1148100, by rfl⟩ : syracuseStep 3061601 = 2296201) B2296201
theorem B2041067 : Blo 2039435 2041067 := bstep (se 1 (by rfl) ⟨1530800, by rfl⟩ : syracuseStep 2041067 = 3061601) B3061601
theorem B13965205 : Blo 2039435 13965205 := bbase (se 6 (by rfl) ⟨327309, by rfl⟩ : syracuseStep 13965205 = 654619) (by norm_num)
theorem B18620273 : Blo 2039435 18620273 := bstep (se 2 (by rfl) ⟨6982602, by rfl⟩ : syracuseStep 18620273 = 13965205) B13965205
theorem B12413515 : Blo 2039435 12413515 := bstep (se 1 (by rfl) ⟨9310136, by rfl⟩ : syracuseStep 12413515 = 18620273) B18620273
theorem B16551353 : Blo 2039435 16551353 := bstep (se 2 (by rfl) ⟨6206757, by rfl⟩ : syracuseStep 16551353 = 12413515) B12413515
theorem B11034235 : Blo 2039435 11034235 := bstep (se 1 (by rfl) ⟨8275676, by rfl⟩ : syracuseStep 11034235 = 16551353) B16551353
theorem B58849253 : Blo 2039435 58849253 := bstep (se 4 (by rfl) ⟨5517117, by rfl⟩ : syracuseStep 58849253 = 11034235) B11034235
theorem B39232835 : Blo 2039435 39232835 := bstep (se 1 (by rfl) ⟨29424626, by rfl⟩ : syracuseStep 39232835 = 58849253) B58849253
theorem B26155223 : Blo 2039435 26155223 := bstep (se 1 (by rfl) ⟨19616417, by rfl⟩ : syracuseStep 26155223 = 39232835) B39232835
theorem B17436815 : Blo 2039435 17436815 := bstep (se 1 (by rfl) ⟨13077611, by rfl⟩ : syracuseStep 17436815 = 26155223) B26155223
theorem B11624543 : Blo 2039435 11624543 := bstep (se 1 (by rfl) ⟨8718407, by rfl⟩ : syracuseStep 11624543 = 17436815) B17436815
theorem B7749695 : Blo 2039435 7749695 := bstep (se 1 (by rfl) ⟨5812271, by rfl⟩ : syracuseStep 7749695 = 11624543) B11624543
theorem B5166463 : Blo 2039435 5166463 := bstep (se 1 (by rfl) ⟨3874847, by rfl⟩ : syracuseStep 5166463 = 7749695) B7749695
theorem B6888617 : Blo 2039435 6888617 := bstep (se 2 (by rfl) ⟨2583231, by rfl⟩ : syracuseStep 6888617 = 5166463) B5166463
theorem B4592411 : Blo 2039435 4592411 := bstep (se 1 (by rfl) ⟨3444308, by rfl⟩ : syracuseStep 4592411 = 6888617) B6888617
theorem B3061607 : Blo 2039435 3061607 := bstep (se 1 (by rfl) ⟨2296205, by rfl⟩ : syracuseStep 3061607 = 4592411) B4592411
theorem B2041071 : Blo 2039435 2041071 := bstep (se 1 (by rfl) ⟨1530803, by rfl⟩ : syracuseStep 2041071 = 3061607) B3061607
theorem B3061613 : Blo 2039435 3061613 := bbase (se 3 (by rfl) ⟨574052, by rfl⟩ : syracuseStep 3061613 = 1148105) (by norm_num)
theorem B2041075 : Blo 2039435 2041075 := bstep (se 1 (by rfl) ⟨1530806, by rfl⟩ : syracuseStep 2041075 = 3061613) B3061613
theorem B4592429 : Blo 2039435 4592429 := bbase (se 3 (by rfl) ⟨861080, by rfl⟩ : syracuseStep 4592429 = 1722161) (by norm_num)
theorem B3061619 : Blo 2039435 3061619 := bstep (se 1 (by rfl) ⟨2296214, by rfl⟩ : syracuseStep 3061619 = 4592429) B4592429
theorem B2041079 : Blo 2039435 2041079 := bstep (se 1 (by rfl) ⟨1530809, by rfl⟩ : syracuseStep 2041079 = 3061619) B3061619
theorem B2327549 : Blo 2039435 2327549 := bbase (se 3 (by rfl) ⟨436415, by rfl⟩ : syracuseStep 2327549 = 872831) (by norm_num)
theorem B6206797 : Blo 2039435 6206797 := bstep (se 3 (by rfl) ⟨1163774, by rfl⟩ : syracuseStep 6206797 = 2327549) B2327549
theorem B8275729 : Blo 2039435 8275729 := bstep (se 2 (by rfl) ⟨3103398, by rfl⟩ : syracuseStep 8275729 = 6206797) B6206797
theorem B11034305 : Blo 2039435 11034305 := bstep (se 2 (by rfl) ⟨4137864, by rfl⟩ : syracuseStep 11034305 = 8275729) B8275729
theorem B7356203 : Blo 2039435 7356203 := bstep (se 1 (by rfl) ⟨5517152, by rfl⟩ : syracuseStep 7356203 = 11034305) B11034305
theorem B4904135 : Blo 2039435 4904135 := bstep (se 1 (by rfl) ⟨3678101, by rfl⟩ : syracuseStep 4904135 = 7356203) B7356203
theorem B3269423 : Blo 2039435 3269423 := bstep (se 1 (by rfl) ⟨2452067, by rfl⟩ : syracuseStep 3269423 = 4904135) B4904135
theorem B8718461 : Blo 2039435 8718461 := bstep (se 3 (by rfl) ⟨1634711, by rfl⟩ : syracuseStep 8718461 = 3269423) B3269423
theorem B5812307 : Blo 2039435 5812307 := bstep (se 1 (by rfl) ⟨4359230, by rfl⟩ : syracuseStep 5812307 = 8718461) B8718461
theorem B3874871 : Blo 2039435 3874871 := bstep (se 1 (by rfl) ⟨2906153, by rfl⟩ : syracuseStep 3874871 = 5812307) B5812307
theorem B2583247 : Blo 2039435 2583247 := bstep (se 1 (by rfl) ⟨1937435, by rfl⟩ : syracuseStep 2583247 = 3874871) B3874871
theorem B3444329 : Blo 2039435 3444329 := bstep (se 2 (by rfl) ⟨1291623, by rfl⟩ : syracuseStep 3444329 = 2583247) B2583247
theorem B2296219 : Blo 2039435 2296219 := bstep (se 1 (by rfl) ⟨1722164, by rfl⟩ : syracuseStep 2296219 = 3444329) B3444329
theorem B3061625 : Blo 2039435 3061625 := bstep (se 2 (by rfl) ⟨1148109, by rfl⟩ : syracuseStep 3061625 = 2296219) B2296219
theorem B2041083 : Blo 2039435 2041083 := bstep (se 1 (by rfl) ⟨1530812, by rfl⟩ : syracuseStep 2041083 = 3061625) B3061625
theorem B2618497 : Blo 2039435 2618497 := bbase (se 2 (by rfl) ⟨981936, by rfl⟩ : syracuseStep 2618497 = 1963873) (by norm_num)
theorem B13965317 : Blo 2039435 13965317 := bstep (se 4 (by rfl) ⟨1309248, by rfl⟩ : syracuseStep 13965317 = 2618497) B2618497
theorem B9310211 : Blo 2039435 9310211 := bstep (se 1 (by rfl) ⟨6982658, by rfl⟩ : syracuseStep 9310211 = 13965317) B13965317
theorem B6206807 : Blo 2039435 6206807 := bstep (se 1 (by rfl) ⟨4655105, by rfl⟩ : syracuseStep 6206807 = 9310211) B9310211
theorem B4137871 : Blo 2039435 4137871 := bstep (se 1 (by rfl) ⟨3103403, by rfl⟩ : syracuseStep 4137871 = 6206807) B6206807
theorem B5517161 : Blo 2039435 5517161 := bstep (se 2 (by rfl) ⟨2068935, by rfl⟩ : syracuseStep 5517161 = 4137871) B4137871
theorem B3678107 : Blo 2039435 3678107 := bstep (se 1 (by rfl) ⟨2758580, by rfl⟩ : syracuseStep 3678107 = 5517161) B5517161
theorem B9808285 : Blo 2039435 9808285 := bstep (se 3 (by rfl) ⟨1839053, by rfl⟩ : syracuseStep 9808285 = 3678107) B3678107
theorem B13077713 : Blo 2039435 13077713 := bstep (se 2 (by rfl) ⟨4904142, by rfl⟩ : syracuseStep 13077713 = 9808285) B9808285
theorem B34873901 : Blo 2039435 34873901 := bstep (se 3 (by rfl) ⟨6538856, by rfl⟩ : syracuseStep 34873901 = 13077713) B13077713
theorem B23249267 : Blo 2039435 23249267 := bstep (se 1 (by rfl) ⟨17436950, by rfl⟩ : syracuseStep 23249267 = 34873901) B34873901
theorem B15499511 : Blo 2039435 15499511 := bstep (se 1 (by rfl) ⟨11624633, by rfl⟩ : syracuseStep 15499511 = 23249267) B23249267
theorem B10333007 : Blo 2039435 10333007 := bstep (se 1 (by rfl) ⟨7749755, by rfl⟩ : syracuseStep 10333007 = 15499511) B15499511
theorem B6888671 : Blo 2039435 6888671 := bstep (se 1 (by rfl) ⟨5166503, by rfl⟩ : syracuseStep 6888671 = 10333007) B10333007
theorem B4592447 : Blo 2039435 4592447 := bstep (se 1 (by rfl) ⟨3444335, by rfl⟩ : syracuseStep 4592447 = 6888671) B6888671
theorem B3061631 : Blo 2039435 3061631 := bstep (se 1 (by rfl) ⟨2296223, by rfl⟩ : syracuseStep 3061631 = 4592447) B4592447
theorem B2041087 : Blo 2039435 2041087 := bstep (se 1 (by rfl) ⟨1530815, by rfl⟩ : syracuseStep 2041087 = 3061631) B3061631
theorem B3061637 : Blo 2039435 3061637 := bbase (se 4 (by rfl) ⟨287028, by rfl⟩ : syracuseStep 3061637 = 574057) (by norm_num)
theorem B2041091 : Blo 2039435 2041091 := bstep (se 1 (by rfl) ⟨1530818, by rfl⟩ : syracuseStep 2041091 = 3061637) B3061637
theorem B3444349 : Blo 2039435 3444349 := bbase (se 3 (by rfl) ⟨645815, by rfl⟩ : syracuseStep 3444349 = 1291631) (by norm_num)
theorem B4592465 : Blo 2039435 4592465 := bstep (se 2 (by rfl) ⟨1722174, by rfl⟩ : syracuseStep 4592465 = 3444349) B3444349
theorem B3061643 : Blo 2039435 3061643 := bstep (se 1 (by rfl) ⟨2296232, by rfl⟩ : syracuseStep 3061643 = 4592465) B4592465
theorem B2041095 : Blo 2039435 2041095 := bstep (se 1 (by rfl) ⟨1530821, by rfl⟩ : syracuseStep 2041095 = 3061643) B3061643
theorem B2296237 : Blo 2039435 2296237 := bbase (se 3 (by rfl) ⟨430544, by rfl⟩ : syracuseStep 2296237 = 861089) (by norm_num)
theorem B3061649 : Blo 2039435 3061649 := bstep (se 2 (by rfl) ⟨1148118, by rfl⟩ : syracuseStep 3061649 = 2296237) B2296237
theorem B2041099 : Blo 2039435 2041099 := bstep (se 1 (by rfl) ⟨1530824, by rfl⟩ : syracuseStep 2041099 = 3061649) B3061649
theorem B6888725 : Blo 2039435 6888725 := bbase (se 6 (by rfl) ⟨161454, by rfl⟩ : syracuseStep 6888725 = 322909) (by norm_num)
theorem B4592483 : Blo 2039435 4592483 := bstep (se 1 (by rfl) ⟨3444362, by rfl⟩ : syracuseStep 4592483 = 6888725) B6888725
theorem B3061655 : Blo 2039435 3061655 := bstep (se 1 (by rfl) ⟨2296241, by rfl⟩ : syracuseStep 3061655 = 4592483) B4592483
theorem B2041103 : Blo 2039435 2041103 := bstep (se 1 (by rfl) ⟨1530827, by rfl⟩ : syracuseStep 2041103 = 3061655) B3061655
theorem B3061661 : Blo 2039435 3061661 := bbase (se 3 (by rfl) ⟨574061, by rfl⟩ : syracuseStep 3061661 = 1148123) (by norm_num)
theorem B2041107 : Blo 2039435 2041107 := bstep (se 1 (by rfl) ⟨1530830, by rfl⟩ : syracuseStep 2041107 = 3061661) B3061661
theorem B4592501 : Blo 2039435 4592501 := bbase (se 5 (by rfl) ⟨215273, by rfl⟩ : syracuseStep 4592501 = 430547) (by norm_num)
theorem B3061667 : Blo 2039435 3061667 := bstep (se 1 (by rfl) ⟨2296250, by rfl⟩ : syracuseStep 3061667 = 4592501) B4592501
theorem B2041111 : Blo 2039435 2041111 := bstep (se 1 (by rfl) ⟨1530833, by rfl⟩ : syracuseStep 2041111 = 3061667) B3061667
theorem B22068949 : Blo 2039435 22068949 := bbase (se 7 (by rfl) ⟨258620, by rfl⟩ : syracuseStep 22068949 = 517241) (by norm_num)
theorem B29425265 : Blo 2039435 29425265 := bstep (se 2 (by rfl) ⟨11034474, by rfl⟩ : syracuseStep 29425265 = 22068949) B22068949
theorem B19616843 : Blo 2039435 19616843 := bstep (se 1 (by rfl) ⟨14712632, by rfl⟩ : syracuseStep 19616843 = 29425265) B29425265
theorem B13077895 : Blo 2039435 13077895 := bstep (se 1 (by rfl) ⟨9808421, by rfl⟩ : syracuseStep 13077895 = 19616843) B19616843
theorem B17437193 : Blo 2039435 17437193 := bstep (se 2 (by rfl) ⟨6538947, by rfl⟩ : syracuseStep 17437193 = 13077895) B13077895
theorem B11624795 : Blo 2039435 11624795 := bstep (se 1 (by rfl) ⟨8718596, by rfl⟩ : syracuseStep 11624795 = 17437193) B17437193
theorem B7749863 : Blo 2039435 7749863 := bstep (se 1 (by rfl) ⟨5812397, by rfl⟩ : syracuseStep 7749863 = 11624795) B11624795
theorem B5166575 : Blo 2039435 5166575 := bstep (se 1 (by rfl) ⟨3874931, by rfl⟩ : syracuseStep 5166575 = 7749863) B7749863
theorem B3444383 : Blo 2039435 3444383 := bstep (se 1 (by rfl) ⟨2583287, by rfl⟩ : syracuseStep 3444383 = 5166575) B5166575
theorem B2296255 : Blo 2039435 2296255 := bstep (se 1 (by rfl) ⟨1722191, by rfl⟩ : syracuseStep 2296255 = 3444383) B3444383
theorem B3061673 : Blo 2039435 3061673 := bstep (se 2 (by rfl) ⟨1148127, by rfl⟩ : syracuseStep 3061673 = 2296255) B2296255
theorem B2041115 : Blo 2039435 2041115 := bstep (se 1 (by rfl) ⟨1530836, by rfl⟩ : syracuseStep 2041115 = 3061673) B3061673
theorem B7749877 : Blo 2039435 7749877 := bbase (se 5 (by rfl) ⟨363275, by rfl⟩ : syracuseStep 7749877 = 726551) (by norm_num)
theorem B10333169 : Blo 2039435 10333169 := bstep (se 2 (by rfl) ⟨3874938, by rfl⟩ : syracuseStep 10333169 = 7749877) B7749877
theorem B6888779 : Blo 2039435 6888779 := bstep (se 1 (by rfl) ⟨5166584, by rfl⟩ : syracuseStep 6888779 = 10333169) B10333169
theorem B4592519 : Blo 2039435 4592519 := bstep (se 1 (by rfl) ⟨3444389, by rfl⟩ : syracuseStep 4592519 = 6888779) B6888779
theorem B3061679 : Blo 2039435 3061679 := bstep (se 1 (by rfl) ⟨2296259, by rfl⟩ : syracuseStep 3061679 = 4592519) B4592519
theorem B2041119 : Blo 2039435 2041119 := bstep (se 1 (by rfl) ⟨1530839, by rfl⟩ : syracuseStep 2041119 = 3061679) B3061679
theorem B3061685 : Blo 2039435 3061685 := bbase (se 5 (by rfl) ⟨143516, by rfl⟩ : syracuseStep 3061685 = 287033) (by norm_num)
theorem B2041123 : Blo 2039435 2041123 := bstep (se 1 (by rfl) ⟨1530842, by rfl⟩ : syracuseStep 2041123 = 3061685) B3061685
theorem B5166605 : Blo 2039435 5166605 := bbase (se 3 (by rfl) ⟨968738, by rfl⟩ : syracuseStep 5166605 = 1937477) (by norm_num)
theorem B3444403 : Blo 2039435 3444403 := bstep (se 1 (by rfl) ⟨2583302, by rfl⟩ : syracuseStep 3444403 = 5166605) B5166605
theorem B4592537 : Blo 2039435 4592537 := bstep (se 2 (by rfl) ⟨1722201, by rfl⟩ : syracuseStep 4592537 = 3444403) B3444403
theorem B3061691 : Blo 2039435 3061691 := bstep (se 1 (by rfl) ⟨2296268, by rfl⟩ : syracuseStep 3061691 = 4592537) B4592537
theorem B2041127 : Blo 2039435 2041127 := bstep (se 1 (by rfl) ⟨1530845, by rfl⟩ : syracuseStep 2041127 = 3061691) B3061691
theorem B2296273 : Blo 2039435 2296273 := bbase (se 2 (by rfl) ⟨861102, by rfl⟩ : syracuseStep 2296273 = 1722205) (by norm_num)
theorem B3061697 : Blo 2039435 3061697 := bstep (se 2 (by rfl) ⟨1148136, by rfl⟩ : syracuseStep 3061697 = 2296273) B2296273
theorem B2041131 : Blo 2039435 2041131 := bstep (se 1 (by rfl) ⟨1530848, by rfl⟩ : syracuseStep 2041131 = 3061697) B3061697
theorem B4359341 : Blo 2039435 4359341 := bbase (se 3 (by rfl) ⟨817376, by rfl⟩ : syracuseStep 4359341 = 1634753) (by norm_num)
theorem B2906227 : Blo 2039435 2906227 := bstep (se 1 (by rfl) ⟨2179670, by rfl⟩ : syracuseStep 2906227 = 4359341) B4359341
theorem B3874969 : Blo 2039435 3874969 := bstep (se 2 (by rfl) ⟨1453113, by rfl⟩ : syracuseStep 3874969 = 2906227) B2906227
theorem B5166625 : Blo 2039435 5166625 := bstep (se 2 (by rfl) ⟨1937484, by rfl⟩ : syracuseStep 5166625 = 3874969) B3874969
theorem B6888833 : Blo 2039435 6888833 := bstep (se 2 (by rfl) ⟨2583312, by rfl⟩ : syracuseStep 6888833 = 5166625) B5166625
theorem B4592555 : Blo 2039435 4592555 := bstep (se 1 (by rfl) ⟨3444416, by rfl⟩ : syracuseStep 4592555 = 6888833) B6888833
theorem B3061703 : Blo 2039435 3061703 := bstep (se 1 (by rfl) ⟨2296277, by rfl⟩ : syracuseStep 3061703 = 4592555) B4592555
theorem B2041135 : Blo 2039435 2041135 := bstep (se 1 (by rfl) ⟨1530851, by rfl⟩ : syracuseStep 2041135 = 3061703) B3061703
theorem B3061709 : Blo 2039435 3061709 := bbase (se 3 (by rfl) ⟨574070, by rfl⟩ : syracuseStep 3061709 = 1148141) (by norm_num)
theorem B2041139 : Blo 2039435 2041139 := bstep (se 1 (by rfl) ⟨1530854, by rfl⟩ : syracuseStep 2041139 = 3061709) B3061709
theorem B4592573 : Blo 2039435 4592573 := bbase (se 3 (by rfl) ⟨861107, by rfl⟩ : syracuseStep 4592573 = 1722215) (by norm_num)
theorem B3061715 : Blo 2039435 3061715 := bstep (se 1 (by rfl) ⟨2296286, by rfl⟩ : syracuseStep 3061715 = 4592573) B4592573
theorem B2041143 : Blo 2039435 2041143 := bstep (se 1 (by rfl) ⟨1530857, by rfl⟩ : syracuseStep 2041143 = 3061715) B3061715
theorem B3444437 : Blo 2039435 3444437 := bbase (se 7 (by rfl) ⟨40364, by rfl⟩ : syracuseStep 3444437 = 80729) (by norm_num)
theorem B2296291 : Blo 2039435 2296291 := bstep (se 1 (by rfl) ⟨1722218, by rfl⟩ : syracuseStep 2296291 = 3444437) B3444437
theorem B3061721 : Blo 2039435 3061721 := bstep (se 2 (by rfl) ⟨1148145, by rfl⟩ : syracuseStep 3061721 = 2296291) B2296291
theorem B2041147 : Blo 2039435 2041147 := bstep (se 1 (by rfl) ⟨1530860, by rfl⟩ : syracuseStep 2041147 = 3061721) B3061721
theorem B12414005 : Blo 2039435 12414005 := bbase (se 5 (by rfl) ⟨581906, by rfl⟩ : syracuseStep 12414005 = 1163813) (by norm_num)
theorem B8276003 : Blo 2039435 8276003 := bstep (se 1 (by rfl) ⟨6207002, by rfl⟩ : syracuseStep 8276003 = 12414005) B12414005
theorem B5517335 : Blo 2039435 5517335 := bstep (se 1 (by rfl) ⟨4138001, by rfl⟩ : syracuseStep 5517335 = 8276003) B8276003
theorem B3678223 : Blo 2039435 3678223 := bstep (se 1 (by rfl) ⟨2758667, by rfl⟩ : syracuseStep 3678223 = 5517335) B5517335
theorem B4904297 : Blo 2039435 4904297 := bstep (se 2 (by rfl) ⟨1839111, by rfl⟩ : syracuseStep 4904297 = 3678223) B3678223
theorem B3269531 : Blo 2039435 3269531 := bstep (se 1 (by rfl) ⟨2452148, by rfl⟩ : syracuseStep 3269531 = 4904297) B4904297
theorem B8718749 : Blo 2039435 8718749 := bstep (se 3 (by rfl) ⟨1634765, by rfl⟩ : syracuseStep 8718749 = 3269531) B3269531
theorem B5812499 : Blo 2039435 5812499 := bstep (se 1 (by rfl) ⟨4359374, by rfl⟩ : syracuseStep 5812499 = 8718749) B8718749
theorem B15499997 : Blo 2039435 15499997 := bstep (se 3 (by rfl) ⟨2906249, by rfl⟩ : syracuseStep 15499997 = 5812499) B5812499
theorem B10333331 : Blo 2039435 10333331 := bstep (se 1 (by rfl) ⟨7749998, by rfl⟩ : syracuseStep 10333331 = 15499997) B15499997
theorem B6888887 : Blo 2039435 6888887 := bstep (se 1 (by rfl) ⟨5166665, by rfl⟩ : syracuseStep 6888887 = 10333331) B10333331
theorem B4592591 : Blo 2039435 4592591 := bstep (se 1 (by rfl) ⟨3444443, by rfl⟩ : syracuseStep 4592591 = 6888887) B6888887
theorem B3061727 : Blo 2039435 3061727 := bstep (se 1 (by rfl) ⟨2296295, by rfl⟩ : syracuseStep 3061727 = 4592591) B4592591
theorem B2041151 : Blo 2039435 2041151 := bstep (se 1 (by rfl) ⟨1530863, by rfl⟩ : syracuseStep 2041151 = 3061727) B3061727
theorem B3061733 : Blo 2039435 3061733 := bbase (se 4 (by rfl) ⟨287037, by rfl⟩ : syracuseStep 3061733 = 574075) (by norm_num)
theorem B2041155 : Blo 2039435 2041155 := bstep (se 1 (by rfl) ⟨1530866, by rfl⟩ : syracuseStep 2041155 = 3061733) B3061733
theorem B4904317 : Blo 2039435 4904317 := bbase (se 3 (by rfl) ⟨919559, by rfl⟩ : syracuseStep 4904317 = 1839119) (by norm_num)
theorem B6539089 : Blo 2039435 6539089 := bstep (se 2 (by rfl) ⟨2452158, by rfl⟩ : syracuseStep 6539089 = 4904317) B4904317
theorem B8718785 : Blo 2039435 8718785 := bstep (se 2 (by rfl) ⟨3269544, by rfl⟩ : syracuseStep 8718785 = 6539089) B6539089
theorem B5812523 : Blo 2039435 5812523 := bstep (se 1 (by rfl) ⟨4359392, by rfl⟩ : syracuseStep 5812523 = 8718785) B8718785
theorem B3875015 : Blo 2039435 3875015 := bstep (se 1 (by rfl) ⟨2906261, by rfl⟩ : syracuseStep 3875015 = 5812523) B5812523
theorem B2583343 : Blo 2039435 2583343 := bstep (se 1 (by rfl) ⟨1937507, by rfl⟩ : syracuseStep 2583343 = 3875015) B3875015
theorem B3444457 : Blo 2039435 3444457 := bstep (se 2 (by rfl) ⟨1291671, by rfl⟩ : syracuseStep 3444457 = 2583343) B2583343
theorem B4592609 : Blo 2039435 4592609 := bstep (se 2 (by rfl) ⟨1722228, by rfl⟩ : syracuseStep 4592609 = 3444457) B3444457
theorem B3061739 : Blo 2039435 3061739 := bstep (se 1 (by rfl) ⟨2296304, by rfl⟩ : syracuseStep 3061739 = 4592609) B4592609
theorem B2041159 : Blo 2039435 2041159 := bstep (se 1 (by rfl) ⟨1530869, by rfl⟩ : syracuseStep 2041159 = 3061739) B3061739
theorem B2296309 : Blo 2039435 2296309 := bbase (se 5 (by rfl) ⟨107639, by rfl⟩ : syracuseStep 2296309 = 215279) (by norm_num)
theorem B3061745 : Blo 2039435 3061745 := bstep (se 2 (by rfl) ⟨1148154, by rfl⟩ : syracuseStep 3061745 = 2296309) B2296309
theorem B2041163 : Blo 2039435 2041163 := bstep (se 1 (by rfl) ⟨1530872, by rfl⟩ : syracuseStep 2041163 = 3061745) B3061745
theorem B2583353 : Blo 2039435 2583353 := bbase (se 2 (by rfl) ⟨968757, by rfl⟩ : syracuseStep 2583353 = 1937515) (by norm_num)
theorem B6888941 : Blo 2039435 6888941 := bstep (se 3 (by rfl) ⟨1291676, by rfl⟩ : syracuseStep 6888941 = 2583353) B2583353
theorem B4592627 : Blo 2039435 4592627 := bstep (se 1 (by rfl) ⟨3444470, by rfl⟩ : syracuseStep 4592627 = 6888941) B6888941
theorem B3061751 : Blo 2039435 3061751 := bstep (se 1 (by rfl) ⟨2296313, by rfl⟩ : syracuseStep 3061751 = 4592627) B4592627
theorem B2041167 : Blo 2039435 2041167 := bstep (se 1 (by rfl) ⟨1530875, by rfl⟩ : syracuseStep 2041167 = 3061751) B3061751
theorem B3061757 : Blo 2039435 3061757 := bbase (se 3 (by rfl) ⟨574079, by rfl⟩ : syracuseStep 3061757 = 1148159) (by norm_num)
theorem B2041171 : Blo 2039435 2041171 := bstep (se 1 (by rfl) ⟨1530878, by rfl⟩ : syracuseStep 2041171 = 3061757) B3061757
theorem B4592645 : Blo 2039435 4592645 := bbase (se 4 (by rfl) ⟨430560, by rfl⟩ : syracuseStep 4592645 = 861121) (by norm_num)
theorem B3061763 : Blo 2039435 3061763 := bstep (se 1 (by rfl) ⟨2296322, by rfl⟩ : syracuseStep 3061763 = 4592645) B4592645
theorem B2041175 : Blo 2039435 2041175 := bstep (se 1 (by rfl) ⟨1530881, by rfl⟩ : syracuseStep 2041175 = 3061763) B3061763
theorem B3875053 : Blo 2039435 3875053 := bbase (se 3 (by rfl) ⟨726572, by rfl⟩ : syracuseStep 3875053 = 1453145) (by norm_num)
theorem B5166737 : Blo 2039435 5166737 := bstep (se 2 (by rfl) ⟨1937526, by rfl⟩ : syracuseStep 5166737 = 3875053) B3875053
theorem B3444491 : Blo 2039435 3444491 := bstep (se 1 (by rfl) ⟨2583368, by rfl⟩ : syracuseStep 3444491 = 5166737) B5166737
theorem B2296327 : Blo 2039435 2296327 := bstep (se 1 (by rfl) ⟨1722245, by rfl⟩ : syracuseStep 2296327 = 3444491) B3444491
theorem B3061769 : Blo 2039435 3061769 := bstep (se 2 (by rfl) ⟨1148163, by rfl⟩ : syracuseStep 3061769 = 2296327) B2296327
theorem B2041179 : Blo 2039435 2041179 := bstep (se 1 (by rfl) ⟨1530884, by rfl⟩ : syracuseStep 2041179 = 3061769) B3061769
theorem B10333493 : Blo 2039435 10333493 := bbase (se 5 (by rfl) ⟨484382, by rfl⟩ : syracuseStep 10333493 = 968765) (by norm_num)
theorem B6888995 : Blo 2039435 6888995 := bstep (se 1 (by rfl) ⟨5166746, by rfl⟩ : syracuseStep 6888995 = 10333493) B10333493
theorem B4592663 : Blo 2039435 4592663 := bstep (se 1 (by rfl) ⟨3444497, by rfl⟩ : syracuseStep 4592663 = 6888995) B6888995
theorem B3061775 : Blo 2039435 3061775 := bstep (se 1 (by rfl) ⟨2296331, by rfl⟩ : syracuseStep 3061775 = 4592663) B4592663
theorem B2041183 : Blo 2039435 2041183 := bstep (se 1 (by rfl) ⟨1530887, by rfl⟩ : syracuseStep 2041183 = 3061775) B3061775
theorem B3061781 : Blo 2039435 3061781 := bbase (se 6 (by rfl) ⟨71760, by rfl⟩ : syracuseStep 3061781 = 143521) (by norm_num)
theorem B2041187 : Blo 2039435 2041187 := bstep (se 1 (by rfl) ⟨1530890, by rfl⟩ : syracuseStep 2041187 = 3061781) B3061781
theorem B8276165 : Blo 2039435 8276165 := bbase (se 4 (by rfl) ⟨775890, by rfl⟩ : syracuseStep 8276165 = 1551781) (by norm_num)
theorem B5517443 : Blo 2039435 5517443 := bstep (se 1 (by rfl) ⟨4138082, by rfl⟩ : syracuseStep 5517443 = 8276165) B8276165
theorem B3678295 : Blo 2039435 3678295 := bstep (se 1 (by rfl) ⟨2758721, by rfl⟩ : syracuseStep 3678295 = 5517443) B5517443
theorem B4904393 : Blo 2039435 4904393 := bstep (se 2 (by rfl) ⟨1839147, by rfl⟩ : syracuseStep 4904393 = 3678295) B3678295
theorem B13078381 : Blo 2039435 13078381 := bstep (se 3 (by rfl) ⟨2452196, by rfl⟩ : syracuseStep 13078381 = 4904393) B4904393
theorem B17437841 : Blo 2039435 17437841 := bstep (se 2 (by rfl) ⟨6539190, by rfl⟩ : syracuseStep 17437841 = 13078381) B13078381
theorem B11625227 : Blo 2039435 11625227 := bstep (se 1 (by rfl) ⟨8718920, by rfl⟩ : syracuseStep 11625227 = 17437841) B17437841
theorem B7750151 : Blo 2039435 7750151 := bstep (se 1 (by rfl) ⟨5812613, by rfl⟩ : syracuseStep 7750151 = 11625227) B11625227
theorem B5166767 : Blo 2039435 5166767 := bstep (se 1 (by rfl) ⟨3875075, by rfl⟩ : syracuseStep 5166767 = 7750151) B7750151
theorem B3444511 : Blo 2039435 3444511 := bstep (se 1 (by rfl) ⟨2583383, by rfl⟩ : syracuseStep 3444511 = 5166767) B5166767
theorem B4592681 : Blo 2039435 4592681 := bstep (se 2 (by rfl) ⟨1722255, by rfl⟩ : syracuseStep 4592681 = 3444511) B3444511
theorem B3061787 : Blo 2039435 3061787 := bstep (se 1 (by rfl) ⟨2296340, by rfl⟩ : syracuseStep 3061787 = 4592681) B4592681
theorem B2041191 : Blo 2039435 2041191 := bstep (se 1 (by rfl) ⟨1530893, by rfl⟩ : syracuseStep 2041191 = 3061787) B3061787
theorem B2296345 : Blo 2039435 2296345 := bbase (se 2 (by rfl) ⟨861129, by rfl⟩ : syracuseStep 2296345 = 1722259) (by norm_num)
theorem B3061793 : Blo 2039435 3061793 := bstep (se 2 (by rfl) ⟨1148172, by rfl⟩ : syracuseStep 3061793 = 2296345) B2296345
theorem B2041195 : Blo 2039435 2041195 := bstep (se 1 (by rfl) ⟨1530896, by rfl⟩ : syracuseStep 2041195 = 3061793) B3061793
theorem B7750181 : Blo 2039435 7750181 := bbase (se 4 (by rfl) ⟨726579, by rfl⟩ : syracuseStep 7750181 = 1453159) (by norm_num)
theorem B5166787 : Blo 2039435 5166787 := bstep (se 1 (by rfl) ⟨3875090, by rfl⟩ : syracuseStep 5166787 = 7750181) B7750181
theorem B6889049 : Blo 2039435 6889049 := bstep (se 2 (by rfl) ⟨2583393, by rfl⟩ : syracuseStep 6889049 = 5166787) B5166787
theorem B4592699 : Blo 2039435 4592699 := bstep (se 1 (by rfl) ⟨3444524, by rfl⟩ : syracuseStep 4592699 = 6889049) B6889049
theorem B3061799 : Blo 2039435 3061799 := bstep (se 1 (by rfl) ⟨2296349, by rfl⟩ : syracuseStep 3061799 = 4592699) B4592699
theorem B2041199 : Blo 2039435 2041199 := bstep (se 1 (by rfl) ⟨1530899, by rfl⟩ : syracuseStep 2041199 = 3061799) B3061799
theorem B3061805 : Blo 2039435 3061805 := bbase (se 3 (by rfl) ⟨574088, by rfl⟩ : syracuseStep 3061805 = 1148177) (by norm_num)
theorem B2041203 : Blo 2039435 2041203 := bstep (se 1 (by rfl) ⟨1530902, by rfl⟩ : syracuseStep 2041203 = 3061805) B3061805
theorem B4592717 : Blo 2039435 4592717 := bbase (se 3 (by rfl) ⟨861134, by rfl⟩ : syracuseStep 4592717 = 1722269) (by norm_num)
theorem B3061811 : Blo 2039435 3061811 := bstep (se 1 (by rfl) ⟨2296358, by rfl⟩ : syracuseStep 3061811 = 4592717) B4592717
theorem B2041207 : Blo 2039435 2041207 := bstep (se 1 (by rfl) ⟨1530905, by rfl⟩ : syracuseStep 2041207 = 3061811) B3061811
theorem B2583409 : Blo 2039435 2583409 := bbase (se 2 (by rfl) ⟨968778, by rfl⟩ : syracuseStep 2583409 = 1937557) (by norm_num)
theorem B3444545 : Blo 2039435 3444545 := bstep (se 2 (by rfl) ⟨1291704, by rfl⟩ : syracuseStep 3444545 = 2583409) B2583409
theorem B2296363 : Blo 2039435 2296363 := bstep (se 1 (by rfl) ⟨1722272, by rfl⟩ : syracuseStep 2296363 = 3444545) B3444545
theorem B3061817 : Blo 2039435 3061817 := bstep (se 2 (by rfl) ⟨1148181, by rfl⟩ : syracuseStep 3061817 = 2296363) B2296363
theorem B2041211 : Blo 2039435 2041211 := bstep (se 1 (by rfl) ⟨1530908, by rfl⟩ : syracuseStep 2041211 = 3061817) B3061817
theorem B9808901 : Blo 2039435 9808901 := bbase (se 4 (by rfl) ⟨919584, by rfl⟩ : syracuseStep 9808901 = 1839169) (by norm_num)
theorem B6539267 : Blo 2039435 6539267 := bstep (se 1 (by rfl) ⟨4904450, by rfl⟩ : syracuseStep 6539267 = 9808901) B9808901
theorem B4359511 : Blo 2039435 4359511 := bstep (se 1 (by rfl) ⟨3269633, by rfl⟩ : syracuseStep 4359511 = 6539267) B6539267
theorem B23250725 : Blo 2039435 23250725 := bstep (se 4 (by rfl) ⟨2179755, by rfl⟩ : syracuseStep 23250725 = 4359511) B4359511
theorem B15500483 : Blo 2039435 15500483 := bstep (se 1 (by rfl) ⟨11625362, by rfl⟩ : syracuseStep 15500483 = 23250725) B23250725
theorem B10333655 : Blo 2039435 10333655 := bstep (se 1 (by rfl) ⟨7750241, by rfl⟩ : syracuseStep 10333655 = 15500483) B15500483
theorem B6889103 : Blo 2039435 6889103 := bstep (se 1 (by rfl) ⟨5166827, by rfl⟩ : syracuseStep 6889103 = 10333655) B10333655
theorem B4592735 : Blo 2039435 4592735 := bstep (se 1 (by rfl) ⟨3444551, by rfl⟩ : syracuseStep 4592735 = 6889103) B6889103
theorem B3061823 : Blo 2039435 3061823 := bstep (se 1 (by rfl) ⟨2296367, by rfl⟩ : syracuseStep 3061823 = 4592735) B4592735
theorem B2041215 : Blo 2039435 2041215 := bstep (se 1 (by rfl) ⟨1530911, by rfl⟩ : syracuseStep 2041215 = 3061823) B3061823
theorem B3061829 : Blo 2039435 3061829 := bbase (se 4 (by rfl) ⟨287046, by rfl⟩ : syracuseStep 3061829 = 574093) (by norm_num)
theorem B2041219 : Blo 2039435 2041219 := bstep (se 1 (by rfl) ⟨1530914, by rfl⟩ : syracuseStep 2041219 = 3061829) B3061829
theorem B3444565 : Blo 2039435 3444565 := bbase (se 9 (by rfl) ⟨10091, by rfl⟩ : syracuseStep 3444565 = 20183) (by norm_num)
theorem B4592753 : Blo 2039435 4592753 := bstep (se 2 (by rfl) ⟨1722282, by rfl⟩ : syracuseStep 4592753 = 3444565) B3444565
theorem B3061835 : Blo 2039435 3061835 := bstep (se 1 (by rfl) ⟨2296376, by rfl⟩ : syracuseStep 3061835 = 4592753) B4592753
theorem B2041223 : Blo 2039435 2041223 := bstep (se 1 (by rfl) ⟨1530917, by rfl⟩ : syracuseStep 2041223 = 3061835) B3061835
theorem B2296381 : Blo 2039435 2296381 := bbase (se 3 (by rfl) ⟨430571, by rfl⟩ : syracuseStep 2296381 = 861143) (by norm_num)
theorem B3061841 : Blo 2039435 3061841 := bstep (se 2 (by rfl) ⟨1148190, by rfl⟩ : syracuseStep 3061841 = 2296381) B2296381
theorem B2041227 : Blo 2039435 2041227 := bstep (se 1 (by rfl) ⟨1530920, by rfl⟩ : syracuseStep 2041227 = 3061841) B3061841
theorem B6889157 : Blo 2039435 6889157 := bbase (se 4 (by rfl) ⟨645858, by rfl⟩ : syracuseStep 6889157 = 1291717) (by norm_num)
theorem B4592771 : Blo 2039435 4592771 := bstep (se 1 (by rfl) ⟨3444578, by rfl⟩ : syracuseStep 4592771 = 6889157) B6889157
theorem B3061847 : Blo 2039435 3061847 := bstep (se 1 (by rfl) ⟨2296385, by rfl⟩ : syracuseStep 3061847 = 4592771) B4592771
theorem B2041231 : Blo 2039435 2041231 := bstep (se 1 (by rfl) ⟨1530923, by rfl⟩ : syracuseStep 2041231 = 3061847) B3061847
theorem B3061853 : Blo 2039435 3061853 := bbase (se 3 (by rfl) ⟨574097, by rfl⟩ : syracuseStep 3061853 = 1148195) (by norm_num)
theorem B2041235 : Blo 2039435 2041235 := bstep (se 1 (by rfl) ⟨1530926, by rfl⟩ : syracuseStep 2041235 = 3061853) B3061853
theorem B4592789 : Blo 2039435 4592789 := bbase (se 6 (by rfl) ⟨107643, by rfl⟩ : syracuseStep 4592789 = 215287) (by norm_num)
theorem B3061859 : Blo 2039435 3061859 := bstep (se 1 (by rfl) ⟨2296394, by rfl⟩ : syracuseStep 3061859 = 4592789) B4592789
theorem B2041239 : Blo 2039435 2041239 := bstep (se 1 (by rfl) ⟨1530929, by rfl⟩ : syracuseStep 2041239 = 3061859) B3061859
theorem B2906381 : Blo 2039435 2906381 := bbase (se 3 (by rfl) ⟨544946, by rfl⟩ : syracuseStep 2906381 = 1089893) (by norm_num)
theorem B7750349 : Blo 2039435 7750349 := bstep (se 3 (by rfl) ⟨1453190, by rfl⟩ : syracuseStep 7750349 = 2906381) B2906381
theorem B5166899 : Blo 2039435 5166899 := bstep (se 1 (by rfl) ⟨3875174, by rfl⟩ : syracuseStep 5166899 = 7750349) B7750349
theorem B3444599 : Blo 2039435 3444599 := bstep (se 1 (by rfl) ⟨2583449, by rfl⟩ : syracuseStep 3444599 = 5166899) B5166899
theorem B2296399 : Blo 2039435 2296399 := bstep (se 1 (by rfl) ⟨1722299, by rfl⟩ : syracuseStep 2296399 = 3444599) B3444599
theorem B3061865 : Blo 2039435 3061865 := bstep (se 2 (by rfl) ⟨1148199, by rfl⟩ : syracuseStep 3061865 = 2296399) B2296399
theorem B2041243 : Blo 2039435 2041243 := bstep (se 1 (by rfl) ⟨1530932, by rfl⟩ : syracuseStep 2041243 = 3061865) B3061865
theorem B5237405 : Blo 2039435 5237405 := bbase (se 3 (by rfl) ⟨982013, by rfl⟩ : syracuseStep 5237405 = 1964027) (by norm_num)
theorem B3491603 : Blo 2039435 3491603 := bstep (se 1 (by rfl) ⟨2618702, by rfl⟩ : syracuseStep 3491603 = 5237405) B5237405
theorem B2327735 : Blo 2039435 2327735 := bstep (se 1 (by rfl) ⟨1745801, by rfl⟩ : syracuseStep 2327735 = 3491603) B3491603
theorem B6207293 : Blo 2039435 6207293 := bstep (se 3 (by rfl) ⟨1163867, by rfl⟩ : syracuseStep 6207293 = 2327735) B2327735
theorem B16552781 : Blo 2039435 16552781 := bstep (se 3 (by rfl) ⟨3103646, by rfl⟩ : syracuseStep 16552781 = 6207293) B6207293
theorem B11035187 : Blo 2039435 11035187 := bstep (se 1 (by rfl) ⟨8276390, by rfl⟩ : syracuseStep 11035187 = 16552781) B16552781
theorem B7356791 : Blo 2039435 7356791 := bstep (se 1 (by rfl) ⟨5517593, by rfl⟩ : syracuseStep 7356791 = 11035187) B11035187
theorem B19618109 : Blo 2039435 19618109 := bstep (se 3 (by rfl) ⟨3678395, by rfl⟩ : syracuseStep 19618109 = 7356791) B7356791
theorem B13078739 : Blo 2039435 13078739 := bstep (se 1 (by rfl) ⟨9809054, by rfl⟩ : syracuseStep 13078739 = 19618109) B19618109
theorem B8719159 : Blo 2039435 8719159 := bstep (se 1 (by rfl) ⟨6539369, by rfl⟩ : syracuseStep 8719159 = 13078739) B13078739
theorem B11625545 : Blo 2039435 11625545 := bstep (se 2 (by rfl) ⟨4359579, by rfl⟩ : syracuseStep 11625545 = 8719159) B8719159
theorem B7750363 : Blo 2039435 7750363 := bstep (se 1 (by rfl) ⟨5812772, by rfl⟩ : syracuseStep 7750363 = 11625545) B11625545
theorem B10333817 : Blo 2039435 10333817 := bstep (se 2 (by rfl) ⟨3875181, by rfl⟩ : syracuseStep 10333817 = 7750363) B7750363
theorem B6889211 : Blo 2039435 6889211 := bstep (se 1 (by rfl) ⟨5166908, by rfl⟩ : syracuseStep 6889211 = 10333817) B10333817
theorem B4592807 : Blo 2039435 4592807 := bstep (se 1 (by rfl) ⟨3444605, by rfl⟩ : syracuseStep 4592807 = 6889211) B6889211
theorem B3061871 : Blo 2039435 3061871 := bstep (se 1 (by rfl) ⟨2296403, by rfl⟩ : syracuseStep 3061871 = 4592807) B4592807
theorem B2041247 : Blo 2039435 2041247 := bstep (se 1 (by rfl) ⟨1530935, by rfl⟩ : syracuseStep 2041247 = 3061871) B3061871
theorem B3061877 : Blo 2039435 3061877 := bbase (se 5 (by rfl) ⟨143525, by rfl⟩ : syracuseStep 3061877 = 287051) (by norm_num)
theorem B2041251 : Blo 2039435 2041251 := bstep (se 1 (by rfl) ⟨1530938, by rfl⟩ : syracuseStep 2041251 = 3061877) B3061877
theorem B3875197 : Blo 2039435 3875197 := bbase (se 3 (by rfl) ⟨726599, by rfl⟩ : syracuseStep 3875197 = 1453199) (by norm_num)
theorem B5166929 : Blo 2039435 5166929 := bstep (se 2 (by rfl) ⟨1937598, by rfl⟩ : syracuseStep 5166929 = 3875197) B3875197
theorem B3444619 : Blo 2039435 3444619 := bstep (se 1 (by rfl) ⟨2583464, by rfl⟩ : syracuseStep 3444619 = 5166929) B5166929
theorem B4592825 : Blo 2039435 4592825 := bstep (se 2 (by rfl) ⟨1722309, by rfl⟩ : syracuseStep 4592825 = 3444619) B3444619
theorem B3061883 : Blo 2039435 3061883 := bstep (se 1 (by rfl) ⟨2296412, by rfl⟩ : syracuseStep 3061883 = 4592825) B4592825
theorem B2041255 : Blo 2039435 2041255 := bstep (se 1 (by rfl) ⟨1530941, by rfl⟩ : syracuseStep 2041255 = 3061883) B3061883
theorem B2296417 : Blo 2039435 2296417 := bbase (se 2 (by rfl) ⟨861156, by rfl⟩ : syracuseStep 2296417 = 1722313) (by norm_num)
theorem B3061889 : Blo 2039435 3061889 := bstep (se 2 (by rfl) ⟨1148208, by rfl⟩ : syracuseStep 3061889 = 2296417) B2296417
theorem B2041259 : Blo 2039435 2041259 := bstep (se 1 (by rfl) ⟨1530944, by rfl⟩ : syracuseStep 2041259 = 3061889) B3061889
theorem B5166949 : Blo 2039435 5166949 := bbase (se 4 (by rfl) ⟨484401, by rfl⟩ : syracuseStep 5166949 = 968803) (by norm_num)
theorem B6889265 : Blo 2039435 6889265 := bstep (se 2 (by rfl) ⟨2583474, by rfl⟩ : syracuseStep 6889265 = 5166949) B5166949
theorem B4592843 : Blo 2039435 4592843 := bstep (se 1 (by rfl) ⟨3444632, by rfl⟩ : syracuseStep 4592843 = 6889265) B6889265
theorem B3061895 : Blo 2039435 3061895 := bstep (se 1 (by rfl) ⟨2296421, by rfl⟩ : syracuseStep 3061895 = 4592843) B4592843
theorem B2041263 : Blo 2039435 2041263 := bstep (se 1 (by rfl) ⟨1530947, by rfl⟩ : syracuseStep 2041263 = 3061895) B3061895
theorem B3061901 : Blo 2039435 3061901 := bbase (se 3 (by rfl) ⟨574106, by rfl⟩ : syracuseStep 3061901 = 1148213) (by norm_num)
theorem B2041267 : Blo 2039435 2041267 := bstep (se 1 (by rfl) ⟨1530950, by rfl⟩ : syracuseStep 2041267 = 3061901) B3061901
theorem B4592861 : Blo 2039435 4592861 := bbase (se 3 (by rfl) ⟨861161, by rfl⟩ : syracuseStep 4592861 = 1722323) (by norm_num)
theorem B3061907 : Blo 2039435 3061907 := bstep (se 1 (by rfl) ⟨2296430, by rfl⟩ : syracuseStep 3061907 = 4592861) B4592861
theorem B2041271 : Blo 2039435 2041271 := bstep (se 1 (by rfl) ⟨1530953, by rfl⟩ : syracuseStep 2041271 = 3061907) B3061907
theorem B3444653 : Blo 2039435 3444653 := bbase (se 3 (by rfl) ⟨645872, by rfl⟩ : syracuseStep 3444653 = 1291745) (by norm_num)
theorem B2296435 : Blo 2039435 2296435 := bstep (se 1 (by rfl) ⟨1722326, by rfl⟩ : syracuseStep 2296435 = 3444653) B3444653
theorem B3061913 : Blo 2039435 3061913 := bstep (se 2 (by rfl) ⟨1148217, by rfl⟩ : syracuseStep 3061913 = 2296435) B2296435
theorem B2041275 : Blo 2039435 2041275 := bstep (se 1 (by rfl) ⟨1530956, by rfl⟩ : syracuseStep 2041275 = 3061913) B3061913
theorem B4251949 : Blo 2039435 4251949 := bbase (se 3 (by rfl) ⟨797240, by rfl⟩ : syracuseStep 4251949 = 1594481) (by norm_num)
theorem B90708245 : Blo 2039435 90708245 := bstep (se 6 (by rfl) ⟨2125974, by rfl⟩ : syracuseStep 90708245 = 4251949) B4251949
theorem B60472163 : Blo 2039435 60472163 := bstep (se 1 (by rfl) ⟨45354122, by rfl⟩ : syracuseStep 60472163 = 90708245) B90708245
theorem B40314775 : Blo 2039435 40314775 := bstep (se 1 (by rfl) ⟨30236081, by rfl⟩ : syracuseStep 40314775 = 60472163) B60472163
theorem B53753033 : Blo 2039435 53753033 := bstep (se 2 (by rfl) ⟨20157387, by rfl⟩ : syracuseStep 53753033 = 40314775) B40314775
theorem B35835355 : Blo 2039435 35835355 := bstep (se 1 (by rfl) ⟨26876516, by rfl⟩ : syracuseStep 35835355 = 53753033) B53753033
theorem B191121893 : Blo 2039435 191121893 := bstep (se 4 (by rfl) ⟨17917677, by rfl⟩ : syracuseStep 191121893 = 35835355) B35835355
theorem B127414595 : Blo 2039435 127414595 := bstep (se 1 (by rfl) ⟨95560946, by rfl⟩ : syracuseStep 127414595 = 191121893) B191121893
theorem B84943063 : Blo 2039435 84943063 := bstep (se 1 (by rfl) ⟨63707297, by rfl⟩ : syracuseStep 84943063 = 127414595) B127414595
theorem B453029669 : Blo 2039435 453029669 := bstep (se 4 (by rfl) ⟨42471531, by rfl⟩ : syracuseStep 453029669 = 84943063) B84943063
theorem B302019779 : Blo 2039435 302019779 := bstep (se 1 (by rfl) ⟨226514834, by rfl⟩ : syracuseStep 302019779 = 453029669) B453029669
theorem B805386077 : Blo 2039435 805386077 := bstep (se 3 (by rfl) ⟨151009889, by rfl⟩ : syracuseStep 805386077 = 302019779) B302019779
theorem B536924051 : Blo 2039435 536924051 := bstep (se 1 (by rfl) ⟨402693038, by rfl⟩ : syracuseStep 536924051 = 805386077) B805386077
theorem B357949367 : Blo 2039435 357949367 := bstep (se 1 (by rfl) ⟨268462025, by rfl⟩ : syracuseStep 357949367 = 536924051) B536924051
theorem B238632911 : Blo 2039435 238632911 := bstep (se 1 (by rfl) ⟨178974683, by rfl⟩ : syracuseStep 238632911 = 357949367) B357949367
theorem B159088607 : Blo 2039435 159088607 := bstep (se 1 (by rfl) ⟨119316455, by rfl⟩ : syracuseStep 159088607 = 238632911) B238632911
theorem B106059071 : Blo 2039435 106059071 := bstep (se 1 (by rfl) ⟨79544303, by rfl⟩ : syracuseStep 106059071 = 159088607) B159088607
theorem B70706047 : Blo 2039435 70706047 := bstep (se 1 (by rfl) ⟨53029535, by rfl⟩ : syracuseStep 70706047 = 106059071) B106059071
theorem B94274729 : Blo 2039435 94274729 := bstep (se 2 (by rfl) ⟨35353023, by rfl⟩ : syracuseStep 94274729 = 70706047) B70706047
theorem B62849819 : Blo 2039435 62849819 := bstep (se 1 (by rfl) ⟨47137364, by rfl⟩ : syracuseStep 62849819 = 94274729) B94274729
theorem B41899879 : Blo 2039435 41899879 := bstep (se 1 (by rfl) ⟨31424909, by rfl⟩ : syracuseStep 41899879 = 62849819) B62849819
theorem B55866505 : Blo 2039435 55866505 := bstep (se 2 (by rfl) ⟨20949939, by rfl⟩ : syracuseStep 55866505 = 41899879) B41899879
theorem B74488673 : Blo 2039435 74488673 := bstep (se 2 (by rfl) ⟨27933252, by rfl⟩ : syracuseStep 74488673 = 55866505) B55866505
theorem B198636461 : Blo 2039435 198636461 := bstep (se 3 (by rfl) ⟨37244336, by rfl⟩ : syracuseStep 198636461 = 74488673) B74488673
theorem B132424307 : Blo 2039435 132424307 := bstep (se 1 (by rfl) ⟨99318230, by rfl⟩ : syracuseStep 132424307 = 198636461) B198636461
theorem B88282871 : Blo 2039435 88282871 := bstep (se 1 (by rfl) ⟨66212153, by rfl⟩ : syracuseStep 88282871 = 132424307) B132424307
theorem B58855247 : Blo 2039435 58855247 := bstep (se 1 (by rfl) ⟨44141435, by rfl⟩ : syracuseStep 58855247 = 88282871) B88282871
theorem B39236831 : Blo 2039435 39236831 := bstep (se 1 (by rfl) ⟨29427623, by rfl⟩ : syracuseStep 39236831 = 58855247) B58855247
theorem B26157887 : Blo 2039435 26157887 := bstep (se 1 (by rfl) ⟨19618415, by rfl⟩ : syracuseStep 26157887 = 39236831) B39236831
theorem B17438591 : Blo 2039435 17438591 := bstep (se 1 (by rfl) ⟨13078943, by rfl⟩ : syracuseStep 17438591 = 26157887) B26157887
theorem B11625727 : Blo 2039435 11625727 := bstep (se 1 (by rfl) ⟨8719295, by rfl⟩ : syracuseStep 11625727 = 17438591) B17438591
theorem B15500969 : Blo 2039435 15500969 := bstep (se 2 (by rfl) ⟨5812863, by rfl⟩ : syracuseStep 15500969 = 11625727) B11625727
theorem B10333979 : Blo 2039435 10333979 := bstep (se 1 (by rfl) ⟨7750484, by rfl⟩ : syracuseStep 10333979 = 15500969) B15500969
theorem B6889319 : Blo 2039435 6889319 := bstep (se 1 (by rfl) ⟨5166989, by rfl⟩ : syracuseStep 6889319 = 10333979) B10333979
theorem B4592879 : Blo 2039435 4592879 := bstep (se 1 (by rfl) ⟨3444659, by rfl⟩ : syracuseStep 4592879 = 6889319) B6889319
theorem B3061919 : Blo 2039435 3061919 := bstep (se 1 (by rfl) ⟨2296439, by rfl⟩ : syracuseStep 3061919 = 4592879) B4592879
theorem B2041279 : Blo 2039435 2041279 := bstep (se 1 (by rfl) ⟨1530959, by rfl⟩ : syracuseStep 2041279 = 3061919) B3061919
theorem B3061925 : Blo 2039435 3061925 := bbase (se 4 (by rfl) ⟨287055, by rfl⟩ : syracuseStep 3061925 = 574111) (by norm_num)
theorem B2041283 : Blo 2039435 2041283 := bstep (se 1 (by rfl) ⟨1530962, by rfl⟩ : syracuseStep 2041283 = 3061925) B3061925
theorem B2583505 : Blo 2039435 2583505 := bbase (se 2 (by rfl) ⟨968814, by rfl⟩ : syracuseStep 2583505 = 1937629) (by norm_num)
theorem B3444673 : Blo 2039435 3444673 := bstep (se 2 (by rfl) ⟨1291752, by rfl⟩ : syracuseStep 3444673 = 2583505) B2583505
theorem B4592897 : Blo 2039435 4592897 := bstep (se 2 (by rfl) ⟨1722336, by rfl⟩ : syracuseStep 4592897 = 3444673) B3444673
theorem B3061931 : Blo 2039435 3061931 := bstep (se 1 (by rfl) ⟨2296448, by rfl⟩ : syracuseStep 3061931 = 4592897) B4592897
theorem B2041287 : Blo 2039435 2041287 := bstep (se 1 (by rfl) ⟨1530965, by rfl⟩ : syracuseStep 2041287 = 3061931) B3061931
theorem B2296453 : Blo 2039435 2296453 := bbase (se 4 (by rfl) ⟨215292, by rfl⟩ : syracuseStep 2296453 = 430585) (by norm_num)
theorem B3061937 : Blo 2039435 3061937 := bstep (se 2 (by rfl) ⟨1148226, by rfl⟩ : syracuseStep 3061937 = 2296453) B2296453
theorem B2041291 : Blo 2039435 2041291 := bstep (se 1 (by rfl) ⟨1530968, by rfl⟩ : syracuseStep 2041291 = 3061937) B3061937
theorem B6539525 : Blo 2039435 6539525 := bbase (se 4 (by rfl) ⟨613080, by rfl⟩ : syracuseStep 6539525 = 1226161) (by norm_num)
theorem B4359683 : Blo 2039435 4359683 := bstep (se 1 (by rfl) ⟨3269762, by rfl⟩ : syracuseStep 4359683 = 6539525) B6539525
theorem B2906455 : Blo 2039435 2906455 := bstep (se 1 (by rfl) ⟨2179841, by rfl⟩ : syracuseStep 2906455 = 4359683) B4359683
theorem B3875273 : Blo 2039435 3875273 := bstep (se 2 (by rfl) ⟨1453227, by rfl⟩ : syracuseStep 3875273 = 2906455) B2906455
theorem B2583515 : Blo 2039435 2583515 := bstep (se 1 (by rfl) ⟨1937636, by rfl⟩ : syracuseStep 2583515 = 3875273) B3875273
theorem B6889373 : Blo 2039435 6889373 := bstep (se 3 (by rfl) ⟨1291757, by rfl⟩ : syracuseStep 6889373 = 2583515) B2583515
theorem B4592915 : Blo 2039435 4592915 := bstep (se 1 (by rfl) ⟨3444686, by rfl⟩ : syracuseStep 4592915 = 6889373) B6889373
theorem B3061943 : Blo 2039435 3061943 := bstep (se 1 (by rfl) ⟨2296457, by rfl⟩ : syracuseStep 3061943 = 4592915) B4592915
theorem B2041295 : Blo 2039435 2041295 := bstep (se 1 (by rfl) ⟨1530971, by rfl⟩ : syracuseStep 2041295 = 3061943) B3061943
theorem B3061949 : Blo 2039435 3061949 := bbase (se 3 (by rfl) ⟨574115, by rfl⟩ : syracuseStep 3061949 = 1148231) (by norm_num)
theorem B2041299 : Blo 2039435 2041299 := bstep (se 1 (by rfl) ⟨1530974, by rfl⟩ : syracuseStep 2041299 = 3061949) B3061949
theorem B4592933 : Blo 2039435 4592933 := bbase (se 4 (by rfl) ⟨430587, by rfl⟩ : syracuseStep 4592933 = 861175) (by norm_num)
theorem B3061955 : Blo 2039435 3061955 := bstep (se 1 (by rfl) ⟨2296466, by rfl⟩ : syracuseStep 3061955 = 4592933) B4592933
theorem B2041303 : Blo 2039435 2041303 := bstep (se 1 (by rfl) ⟨1530977, by rfl⟩ : syracuseStep 2041303 = 3061955) B3061955
theorem B5167061 : Blo 2039435 5167061 := bbase (se 7 (by rfl) ⟨60551, by rfl⟩ : syracuseStep 5167061 = 121103) (by norm_num)
theorem B3444707 : Blo 2039435 3444707 := bstep (se 1 (by rfl) ⟨2583530, by rfl⟩ : syracuseStep 3444707 = 5167061) B5167061
theorem B2296471 : Blo 2039435 2296471 := bstep (se 1 (by rfl) ⟨1722353, by rfl⟩ : syracuseStep 2296471 = 3444707) B3444707
theorem B3061961 : Blo 2039435 3061961 := bstep (se 2 (by rfl) ⟨1148235, by rfl⟩ : syracuseStep 3061961 = 2296471) B2296471
theorem B2041307 : Blo 2039435 2041307 := bstep (se 1 (by rfl) ⟨1530980, by rfl⟩ : syracuseStep 2041307 = 3061961) B3061961
theorem B2946133 : Blo 2039435 2946133 := bbase (se 8 (by rfl) ⟨17262, by rfl⟩ : syracuseStep 2946133 = 34525) (by norm_num)
theorem B3928177 : Blo 2039435 3928177 := bstep (se 2 (by rfl) ⟨1473066, by rfl⟩ : syracuseStep 3928177 = 2946133) B2946133
theorem B5237569 : Blo 2039435 5237569 := bstep (se 2 (by rfl) ⟨1964088, by rfl⟩ : syracuseStep 5237569 = 3928177) B3928177
theorem B6983425 : Blo 2039435 6983425 := bstep (se 2 (by rfl) ⟨2618784, by rfl⟩ : syracuseStep 6983425 = 5237569) B5237569
theorem B9311233 : Blo 2039435 9311233 := bstep (se 2 (by rfl) ⟨3491712, by rfl⟩ : syracuseStep 9311233 = 6983425) B6983425
theorem B12414977 : Blo 2039435 12414977 := bstep (se 2 (by rfl) ⟨4655616, by rfl⟩ : syracuseStep 12414977 = 9311233) B9311233
theorem B8276651 : Blo 2039435 8276651 := bstep (se 1 (by rfl) ⟨6207488, by rfl⟩ : syracuseStep 8276651 = 12414977) B12414977
theorem B5517767 : Blo 2039435 5517767 := bstep (se 1 (by rfl) ⟨4138325, by rfl⟩ : syracuseStep 5517767 = 8276651) B8276651
theorem B14714045 : Blo 2039435 14714045 := bstep (se 3 (by rfl) ⟨2758883, by rfl⟩ : syracuseStep 14714045 = 5517767) B5517767
theorem B9809363 : Blo 2039435 9809363 := bstep (se 1 (by rfl) ⟨7357022, by rfl⟩ : syracuseStep 9809363 = 14714045) B14714045
theorem B6539575 : Blo 2039435 6539575 := bstep (se 1 (by rfl) ⟨4904681, by rfl⟩ : syracuseStep 6539575 = 9809363) B9809363
theorem B8719433 : Blo 2039435 8719433 := bstep (se 2 (by rfl) ⟨3269787, by rfl⟩ : syracuseStep 8719433 = 6539575) B6539575
theorem B5812955 : Blo 2039435 5812955 := bstep (se 1 (by rfl) ⟨4359716, by rfl⟩ : syracuseStep 5812955 = 8719433) B8719433
theorem B3875303 : Blo 2039435 3875303 := bstep (se 1 (by rfl) ⟨2906477, by rfl⟩ : syracuseStep 3875303 = 5812955) B5812955
theorem B10334141 : Blo 2039435 10334141 := bstep (se 3 (by rfl) ⟨1937651, by rfl⟩ : syracuseStep 10334141 = 3875303) B3875303
theorem B6889427 : Blo 2039435 6889427 := bstep (se 1 (by rfl) ⟨5167070, by rfl⟩ : syracuseStep 6889427 = 10334141) B10334141
theorem B4592951 : Blo 2039435 4592951 := bstep (se 1 (by rfl) ⟨3444713, by rfl⟩ : syracuseStep 4592951 = 6889427) B6889427
theorem B3061967 : Blo 2039435 3061967 := bstep (se 1 (by rfl) ⟨2296475, by rfl⟩ : syracuseStep 3061967 = 4592951) B4592951
theorem B2041311 : Blo 2039435 2041311 := bstep (se 1 (by rfl) ⟨1530983, by rfl⟩ : syracuseStep 2041311 = 3061967) B3061967
theorem B3061973 : Blo 2039435 3061973 := bbase (se 7 (by rfl) ⟨35882, by rfl⟩ : syracuseStep 3061973 = 71765) (by norm_num)
theorem B2041315 : Blo 2039435 2041315 := bstep (se 1 (by rfl) ⟨1530986, by rfl⟩ : syracuseStep 2041315 = 3061973) B3061973
theorem B16779221 : Blo 2039435 16779221 := bbase (se 7 (by rfl) ⟨196631, by rfl⟩ : syracuseStep 16779221 = 393263) (by norm_num)
theorem B11186147 : Blo 2039435 11186147 := bstep (se 1 (by rfl) ⟨8389610, by rfl⟩ : syracuseStep 11186147 = 16779221) B16779221
theorem B7457431 : Blo 2039435 7457431 := bstep (se 1 (by rfl) ⟨5593073, by rfl⟩ : syracuseStep 7457431 = 11186147) B11186147
theorem B9943241 : Blo 2039435 9943241 := bstep (se 2 (by rfl) ⟨3728715, by rfl⟩ : syracuseStep 9943241 = 7457431) B7457431
theorem B26515309 : Blo 2039435 26515309 := bstep (se 3 (by rfl) ⟨4971620, by rfl⟩ : syracuseStep 26515309 = 9943241) B9943241
theorem B35353745 : Blo 2039435 35353745 := bstep (se 2 (by rfl) ⟨13257654, by rfl⟩ : syracuseStep 35353745 = 26515309) B26515309
theorem B23569163 : Blo 2039435 23569163 := bstep (se 1 (by rfl) ⟨17676872, by rfl⟩ : syracuseStep 23569163 = 35353745) B35353745
theorem B15712775 : Blo 2039435 15712775 := bstep (se 1 (by rfl) ⟨11784581, by rfl⟩ : syracuseStep 15712775 = 23569163) B23569163
theorem B10475183 : Blo 2039435 10475183 := bstep (se 1 (by rfl) ⟨7856387, by rfl⟩ : syracuseStep 10475183 = 15712775) B15712775
theorem B27933821 : Blo 2039435 27933821 := bstep (se 3 (by rfl) ⟨5237591, by rfl⟩ : syracuseStep 27933821 = 10475183) B10475183
theorem B18622547 : Blo 2039435 18622547 := bstep (se 1 (by rfl) ⟨13966910, by rfl⟩ : syracuseStep 18622547 = 27933821) B27933821
theorem B12415031 : Blo 2039435 12415031 := bstep (se 1 (by rfl) ⟨9311273, by rfl⟩ : syracuseStep 12415031 = 18622547) B18622547
theorem B8276687 : Blo 2039435 8276687 := bstep (se 1 (by rfl) ⟨6207515, by rfl⟩ : syracuseStep 8276687 = 12415031) B12415031
theorem B5517791 : Blo 2039435 5517791 := bstep (se 1 (by rfl) ⟨4138343, by rfl⟩ : syracuseStep 5517791 = 8276687) B8276687
theorem B3678527 : Blo 2039435 3678527 := bstep (se 1 (by rfl) ⟨2758895, by rfl⟩ : syracuseStep 3678527 = 5517791) B5517791
theorem B2452351 : Blo 2039435 2452351 := bstep (se 1 (by rfl) ⟨1839263, by rfl⟩ : syracuseStep 2452351 = 3678527) B3678527
theorem B3269801 : Blo 2039435 3269801 := bstep (se 2 (by rfl) ⟨1226175, by rfl⟩ : syracuseStep 3269801 = 2452351) B2452351
theorem B2179867 : Blo 2039435 2179867 := bstep (se 1 (by rfl) ⟨1634900, by rfl⟩ : syracuseStep 2179867 = 3269801) B3269801
theorem B2906489 : Blo 2039435 2906489 := bstep (se 2 (by rfl) ⟨1089933, by rfl⟩ : syracuseStep 2906489 = 2179867) B2179867
theorem B7750637 : Blo 2039435 7750637 := bstep (se 3 (by rfl) ⟨1453244, by rfl⟩ : syracuseStep 7750637 = 2906489) B2906489
theorem B5167091 : Blo 2039435 5167091 := bstep (se 1 (by rfl) ⟨3875318, by rfl⟩ : syracuseStep 5167091 = 7750637) B7750637
theorem B3444727 : Blo 2039435 3444727 := bstep (se 1 (by rfl) ⟨2583545, by rfl⟩ : syracuseStep 3444727 = 5167091) B5167091
theorem B4592969 : Blo 2039435 4592969 := bstep (se 2 (by rfl) ⟨1722363, by rfl⟩ : syracuseStep 4592969 = 3444727) B3444727
theorem B3061979 : Blo 2039435 3061979 := bstep (se 1 (by rfl) ⟨2296484, by rfl⟩ : syracuseStep 3061979 = 4592969) B4592969
theorem B2041319 : Blo 2039435 2041319 := bstep (se 1 (by rfl) ⟨1530989, by rfl⟩ : syracuseStep 2041319 = 3061979) B3061979
theorem B2296489 : Blo 2039435 2296489 := bbase (se 2 (by rfl) ⟨861183, by rfl⟩ : syracuseStep 2296489 = 1722367) (by norm_num)
theorem B3061985 : Blo 2039435 3061985 := bstep (se 2 (by rfl) ⟨1148244, by rfl⟩ : syracuseStep 3061985 = 2296489) B2296489
theorem B2041323 : Blo 2039435 2041323 := bstep (se 1 (by rfl) ⟨1530992, by rfl⟩ : syracuseStep 2041323 = 3061985) B3061985
theorem B3269813 : Blo 2039435 3269813 := bbase (se 5 (by rfl) ⟨153272, by rfl⟩ : syracuseStep 3269813 = 306545) (by norm_num)
theorem B8719501 : Blo 2039435 8719501 := bstep (se 3 (by rfl) ⟨1634906, by rfl⟩ : syracuseStep 8719501 = 3269813) B3269813
theorem B11626001 : Blo 2039435 11626001 := bstep (se 2 (by rfl) ⟨4359750, by rfl⟩ : syracuseStep 11626001 = 8719501) B8719501
theorem B7750667 : Blo 2039435 7750667 := bstep (se 1 (by rfl) ⟨5813000, by rfl⟩ : syracuseStep 7750667 = 11626001) B11626001
theorem B5167111 : Blo 2039435 5167111 := bstep (se 1 (by rfl) ⟨3875333, by rfl⟩ : syracuseStep 5167111 = 7750667) B7750667
theorem B6889481 : Blo 2039435 6889481 := bstep (se 2 (by rfl) ⟨2583555, by rfl⟩ : syracuseStep 6889481 = 5167111) B5167111
theorem B4592987 : Blo 2039435 4592987 := bstep (se 1 (by rfl) ⟨3444740, by rfl⟩ : syracuseStep 4592987 = 6889481) B6889481
theorem B3061991 : Blo 2039435 3061991 := bstep (se 1 (by rfl) ⟨2296493, by rfl⟩ : syracuseStep 3061991 = 4592987) B4592987
theorem B2041327 : Blo 2039435 2041327 := bstep (se 1 (by rfl) ⟨1530995, by rfl⟩ : syracuseStep 2041327 = 3061991) B3061991
theorem B3061997 : Blo 2039435 3061997 := bbase (se 3 (by rfl) ⟨574124, by rfl⟩ : syracuseStep 3061997 = 1148249) (by norm_num)
theorem B2041331 : Blo 2039435 2041331 := bstep (se 1 (by rfl) ⟨1530998, by rfl⟩ : syracuseStep 2041331 = 3061997) B3061997
theorem B4593005 : Blo 2039435 4593005 := bbase (se 3 (by rfl) ⟨861188, by rfl⟩ : syracuseStep 4593005 = 1722377) (by norm_num)
theorem B3062003 : Blo 2039435 3062003 := bstep (se 1 (by rfl) ⟨2296502, by rfl⟩ : syracuseStep 3062003 = 4593005) B4593005
theorem B2041335 : Blo 2039435 2041335 := bstep (se 1 (by rfl) ⟨1531001, by rfl⟩ : syracuseStep 2041335 = 3062003) B3062003
theorem B3875357 : Blo 2039435 3875357 := bbase (se 3 (by rfl) ⟨726629, by rfl⟩ : syracuseStep 3875357 = 1453259) (by norm_num)
theorem B2583571 : Blo 2039435 2583571 := bstep (se 1 (by rfl) ⟨1937678, by rfl⟩ : syracuseStep 2583571 = 3875357) B3875357
theorem B3444761 : Blo 2039435 3444761 := bstep (se 2 (by rfl) ⟨1291785, by rfl⟩ : syracuseStep 3444761 = 2583571) B2583571
theorem B2296507 : Blo 2039435 2296507 := bstep (se 1 (by rfl) ⟨1722380, by rfl⟩ : syracuseStep 2296507 = 3444761) B3444761
theorem B3062009 : Blo 2039435 3062009 := bstep (se 2 (by rfl) ⟨1148253, by rfl⟩ : syracuseStep 3062009 = 2296507) B2296507
theorem B2041339 : Blo 2039435 2041339 := bstep (se 1 (by rfl) ⟨1531004, by rfl⟩ : syracuseStep 2041339 = 3062009) B3062009
theorem B2618825 : Blo 2039435 2618825 := bbase (se 2 (by rfl) ⟨982059, by rfl⟩ : syracuseStep 2618825 = 1964119) (by norm_num)
theorem B6983533 : Blo 2039435 6983533 := bstep (se 3 (by rfl) ⟨1309412, by rfl⟩ : syracuseStep 6983533 = 2618825) B2618825
theorem B9311377 : Blo 2039435 9311377 := bstep (se 2 (by rfl) ⟨3491766, by rfl⟩ : syracuseStep 9311377 = 6983533) B6983533
theorem B12415169 : Blo 2039435 12415169 := bstep (se 2 (by rfl) ⟨4655688, by rfl⟩ : syracuseStep 12415169 = 9311377) B9311377
theorem B8276779 : Blo 2039435 8276779 := bstep (se 1 (by rfl) ⟨6207584, by rfl⟩ : syracuseStep 8276779 = 12415169) B12415169
theorem B11035705 : Blo 2039435 11035705 := bstep (se 2 (by rfl) ⟨4138389, by rfl⟩ : syracuseStep 11035705 = 8276779) B8276779
theorem B14714273 : Blo 2039435 14714273 := bstep (se 2 (by rfl) ⟨5517852, by rfl⟩ : syracuseStep 14714273 = 11035705) B11035705
theorem B9809515 : Blo 2039435 9809515 := bstep (se 1 (by rfl) ⟨7357136, by rfl⟩ : syracuseStep 9809515 = 14714273) B14714273
theorem B52317413 : Blo 2039435 52317413 := bstep (se 4 (by rfl) ⟨4904757, by rfl⟩ : syracuseStep 52317413 = 9809515) B9809515
theorem B34878275 : Blo 2039435 34878275 := bstep (se 1 (by rfl) ⟨26158706, by rfl⟩ : syracuseStep 34878275 = 52317413) B52317413
theorem B23252183 : Blo 2039435 23252183 := bstep (se 1 (by rfl) ⟨17439137, by rfl⟩ : syracuseStep 23252183 = 34878275) B34878275
theorem B15501455 : Blo 2039435 15501455 := bstep (se 1 (by rfl) ⟨11626091, by rfl⟩ : syracuseStep 15501455 = 23252183) B23252183
theorem B10334303 : Blo 2039435 10334303 := bstep (se 1 (by rfl) ⟨7750727, by rfl⟩ : syracuseStep 10334303 = 15501455) B15501455
theorem B6889535 : Blo 2039435 6889535 := bstep (se 1 (by rfl) ⟨5167151, by rfl⟩ : syracuseStep 6889535 = 10334303) B10334303
theorem B4593023 : Blo 2039435 4593023 := bstep (se 1 (by rfl) ⟨3444767, by rfl⟩ : syracuseStep 4593023 = 6889535) B6889535
theorem B3062015 : Blo 2039435 3062015 := bstep (se 1 (by rfl) ⟨2296511, by rfl⟩ : syracuseStep 3062015 = 4593023) B4593023
theorem B2041343 : Blo 2039435 2041343 := bstep (se 1 (by rfl) ⟨1531007, by rfl⟩ : syracuseStep 2041343 = 3062015) B3062015
theorem B3062021 : Blo 2039435 3062021 := bbase (se 4 (by rfl) ⟨287064, by rfl⟩ : syracuseStep 3062021 = 574129) (by norm_num)
theorem B2041347 : Blo 2039435 2041347 := bstep (se 1 (by rfl) ⟨1531010, by rfl⟩ : syracuseStep 2041347 = 3062021) B3062021
theorem B3444781 : Blo 2039435 3444781 := bbase (se 3 (by rfl) ⟨645896, by rfl⟩ : syracuseStep 3444781 = 1291793) (by norm_num)
theorem B4593041 : Blo 2039435 4593041 := bstep (se 2 (by rfl) ⟨1722390, by rfl⟩ : syracuseStep 4593041 = 3444781) B3444781
theorem B3062027 : Blo 2039435 3062027 := bstep (se 1 (by rfl) ⟨2296520, by rfl⟩ : syracuseStep 3062027 = 4593041) B4593041
theorem B2041351 : Blo 2039435 2041351 := bstep (se 1 (by rfl) ⟨1531013, by rfl⟩ : syracuseStep 2041351 = 3062027) B3062027
theorem B2296525 : Blo 2039435 2296525 := bbase (se 3 (by rfl) ⟨430598, by rfl⟩ : syracuseStep 2296525 = 861197) (by norm_num)
theorem B3062033 : Blo 2039435 3062033 := bstep (se 2 (by rfl) ⟨1148262, by rfl⟩ : syracuseStep 3062033 = 2296525) B2296525
theorem B2041355 : Blo 2039435 2041355 := bstep (se 1 (by rfl) ⟨1531016, by rfl⟩ : syracuseStep 2041355 = 3062033) B3062033
theorem B6889589 : Blo 2039435 6889589 := bbase (se 5 (by rfl) ⟨322949, by rfl⟩ : syracuseStep 6889589 = 645899) (by norm_num)
theorem B4593059 : Blo 2039435 4593059 := bstep (se 1 (by rfl) ⟨3444794, by rfl⟩ : syracuseStep 4593059 = 6889589) B6889589
theorem B3062039 : Blo 2039435 3062039 := bstep (se 1 (by rfl) ⟨2296529, by rfl⟩ : syracuseStep 3062039 = 4593059) B4593059
theorem B2041359 : Blo 2039435 2041359 := bstep (se 1 (by rfl) ⟨1531019, by rfl⟩ : syracuseStep 2041359 = 3062039) B3062039
theorem B3062045 : Blo 2039435 3062045 := bbase (se 3 (by rfl) ⟨574133, by rfl⟩ : syracuseStep 3062045 = 1148267) (by norm_num)
theorem B2041363 : Blo 2039435 2041363 := bstep (se 1 (by rfl) ⟨1531022, by rfl⟩ : syracuseStep 2041363 = 3062045) B3062045
theorem B4593077 : Blo 2039435 4593077 := bbase (se 5 (by rfl) ⟨215300, by rfl⟩ : syracuseStep 4593077 = 430601) (by norm_num)
theorem B3062051 : Blo 2039435 3062051 := bstep (se 1 (by rfl) ⟨2296538, by rfl⟩ : syracuseStep 3062051 = 4593077) B4593077
theorem B2041367 : Blo 2039435 2041367 := bstep (se 1 (by rfl) ⟨1531025, by rfl⟩ : syracuseStep 2041367 = 3062051) B3062051
theorem B4359845 : Blo 2039435 4359845 := bbase (se 4 (by rfl) ⟨408735, by rfl⟩ : syracuseStep 4359845 = 817471) (by norm_num)
theorem B11626253 : Blo 2039435 11626253 := bstep (se 3 (by rfl) ⟨2179922, by rfl⟩ : syracuseStep 11626253 = 4359845) B4359845
theorem B7750835 : Blo 2039435 7750835 := bstep (se 1 (by rfl) ⟨5813126, by rfl⟩ : syracuseStep 7750835 = 11626253) B11626253
theorem B5167223 : Blo 2039435 5167223 := bstep (se 1 (by rfl) ⟨3875417, by rfl⟩ : syracuseStep 5167223 = 7750835) B7750835
theorem B3444815 : Blo 2039435 3444815 := bstep (se 1 (by rfl) ⟨2583611, by rfl⟩ : syracuseStep 3444815 = 5167223) B5167223
theorem B2296543 : Blo 2039435 2296543 := bstep (se 1 (by rfl) ⟨1722407, by rfl⟩ : syracuseStep 2296543 = 3444815) B3444815
theorem B3062057 : Blo 2039435 3062057 := bstep (se 2 (by rfl) ⟨1148271, by rfl⟩ : syracuseStep 3062057 = 2296543) B2296543
theorem B2041371 : Blo 2039435 2041371 := bstep (se 1 (by rfl) ⟨1531028, by rfl⟩ : syracuseStep 2041371 = 3062057) B3062057
theorem B4359853 : Blo 2039435 4359853 := bbase (se 3 (by rfl) ⟨817472, by rfl⟩ : syracuseStep 4359853 = 1634945) (by norm_num)
theorem B5813137 : Blo 2039435 5813137 := bstep (se 2 (by rfl) ⟨2179926, by rfl⟩ : syracuseStep 5813137 = 4359853) B4359853
theorem B7750849 : Blo 2039435 7750849 := bstep (se 2 (by rfl) ⟨2906568, by rfl⟩ : syracuseStep 7750849 = 5813137) B5813137
theorem B10334465 : Blo 2039435 10334465 := bstep (se 2 (by rfl) ⟨3875424, by rfl⟩ : syracuseStep 10334465 = 7750849) B7750849
theorem B6889643 : Blo 2039435 6889643 := bstep (se 1 (by rfl) ⟨5167232, by rfl⟩ : syracuseStep 6889643 = 10334465) B10334465
theorem B4593095 : Blo 2039435 4593095 := bstep (se 1 (by rfl) ⟨3444821, by rfl⟩ : syracuseStep 4593095 = 6889643) B6889643
theorem B3062063 : Blo 2039435 3062063 := bstep (se 1 (by rfl) ⟨2296547, by rfl⟩ : syracuseStep 3062063 = 4593095) B4593095
theorem B2041375 : Blo 2039435 2041375 := bstep (se 1 (by rfl) ⟨1531031, by rfl⟩ : syracuseStep 2041375 = 3062063) B3062063
theorem B3062069 : Blo 2039435 3062069 := bbase (se 5 (by rfl) ⟨143534, by rfl⟩ : syracuseStep 3062069 = 287069) (by norm_num)
theorem B2041379 : Blo 2039435 2041379 := bstep (se 1 (by rfl) ⟨1531034, by rfl⟩ : syracuseStep 2041379 = 3062069) B3062069
theorem B5167253 : Blo 2039435 5167253 := bbase (se 6 (by rfl) ⟨121107, by rfl⟩ : syracuseStep 5167253 = 242215) (by norm_num)
theorem B3444835 : Blo 2039435 3444835 := bstep (se 1 (by rfl) ⟨2583626, by rfl⟩ : syracuseStep 3444835 = 5167253) B5167253
theorem B4593113 : Blo 2039435 4593113 := bstep (se 2 (by rfl) ⟨1722417, by rfl⟩ : syracuseStep 4593113 = 3444835) B3444835
theorem B3062075 : Blo 2039435 3062075 := bstep (se 1 (by rfl) ⟨2296556, by rfl⟩ : syracuseStep 3062075 = 4593113) B4593113
theorem B2041383 : Blo 2039435 2041383 := bstep (se 1 (by rfl) ⟨1531037, by rfl⟩ : syracuseStep 2041383 = 3062075) B3062075
theorem B2296561 : Blo 2039435 2296561 := bbase (se 2 (by rfl) ⟨861210, by rfl⟩ : syracuseStep 2296561 = 1722421) (by norm_num)
theorem B3062081 : Blo 2039435 3062081 := bstep (se 2 (by rfl) ⟨1148280, by rfl⟩ : syracuseStep 3062081 = 2296561) B2296561
theorem B2041387 : Blo 2039435 2041387 := bstep (se 1 (by rfl) ⟨1531040, by rfl⟩ : syracuseStep 2041387 = 3062081) B3062081
theorem B20951093 : Blo 2039435 20951093 := bbase (se 5 (by rfl) ⟨982082, by rfl⟩ : syracuseStep 20951093 = 1964165) (by norm_num)
theorem B55869581 : Blo 2039435 55869581 := bstep (se 3 (by rfl) ⟨10475546, by rfl⟩ : syracuseStep 55869581 = 20951093) B20951093
theorem B37246387 : Blo 2039435 37246387 := bstep (se 1 (by rfl) ⟨27934790, by rfl⟩ : syracuseStep 37246387 = 55869581) B55869581
theorem B49661849 : Blo 2039435 49661849 := bstep (se 2 (by rfl) ⟨18623193, by rfl⟩ : syracuseStep 49661849 = 37246387) B37246387
theorem B33107899 : Blo 2039435 33107899 := bstep (se 1 (by rfl) ⟨24830924, by rfl⟩ : syracuseStep 33107899 = 49661849) B49661849
theorem B44143865 : Blo 2039435 44143865 := bstep (se 2 (by rfl) ⟨16553949, by rfl⟩ : syracuseStep 44143865 = 33107899) B33107899
theorem B29429243 : Blo 2039435 29429243 := bstep (se 1 (by rfl) ⟨22071932, by rfl⟩ : syracuseStep 29429243 = 44143865) B44143865
theorem B19619495 : Blo 2039435 19619495 := bstep (se 1 (by rfl) ⟨14714621, by rfl⟩ : syracuseStep 19619495 = 29429243) B29429243
theorem B13079663 : Blo 2039435 13079663 := bstep (se 1 (by rfl) ⟨9809747, by rfl⟩ : syracuseStep 13079663 = 19619495) B19619495
theorem B8719775 : Blo 2039435 8719775 := bstep (se 1 (by rfl) ⟨6539831, by rfl⟩ : syracuseStep 8719775 = 13079663) B13079663
theorem B5813183 : Blo 2039435 5813183 := bstep (se 1 (by rfl) ⟨4359887, by rfl⟩ : syracuseStep 5813183 = 8719775) B8719775
theorem B3875455 : Blo 2039435 3875455 := bstep (se 1 (by rfl) ⟨2906591, by rfl⟩ : syracuseStep 3875455 = 5813183) B5813183
theorem B5167273 : Blo 2039435 5167273 := bstep (se 2 (by rfl) ⟨1937727, by rfl⟩ : syracuseStep 5167273 = 3875455) B3875455
theorem B6889697 : Blo 2039435 6889697 := bstep (se 2 (by rfl) ⟨2583636, by rfl⟩ : syracuseStep 6889697 = 5167273) B5167273
theorem B4593131 : Blo 2039435 4593131 := bstep (se 1 (by rfl) ⟨3444848, by rfl⟩ : syracuseStep 4593131 = 6889697) B6889697
theorem B3062087 : Blo 2039435 3062087 := bstep (se 1 (by rfl) ⟨2296565, by rfl⟩ : syracuseStep 3062087 = 4593131) B4593131
theorem B2041391 : Blo 2039435 2041391 := bstep (se 1 (by rfl) ⟨1531043, by rfl⟩ : syracuseStep 2041391 = 3062087) B3062087
theorem B3062093 : Blo 2039435 3062093 := bbase (se 3 (by rfl) ⟨574142, by rfl⟩ : syracuseStep 3062093 = 1148285) (by norm_num)
theorem B2041395 : Blo 2039435 2041395 := bstep (se 1 (by rfl) ⟨1531046, by rfl⟩ : syracuseStep 2041395 = 3062093) B3062093
theorem B4593149 : Blo 2039435 4593149 := bbase (se 3 (by rfl) ⟨861215, by rfl⟩ : syracuseStep 4593149 = 1722431) (by norm_num)
theorem B3062099 : Blo 2039435 3062099 := bstep (se 1 (by rfl) ⟨2296574, by rfl⟩ : syracuseStep 3062099 = 4593149) B4593149
theorem B2041399 : Blo 2039435 2041399 := bstep (se 1 (by rfl) ⟨1531049, by rfl⟩ : syracuseStep 2041399 = 3062099) B3062099
theorem B3444869 : Blo 2039435 3444869 := bbase (se 4 (by rfl) ⟨322956, by rfl⟩ : syracuseStep 3444869 = 645913) (by norm_num)
theorem B2296579 : Blo 2039435 2296579 := bstep (se 1 (by rfl) ⟨1722434, by rfl⟩ : syracuseStep 2296579 = 3444869) B3444869
theorem B3062105 : Blo 2039435 3062105 := bstep (se 2 (by rfl) ⟨1148289, by rfl⟩ : syracuseStep 3062105 = 2296579) B2296579
theorem B2041403 : Blo 2039435 2041403 := bstep (se 1 (by rfl) ⟨1531052, by rfl⟩ : syracuseStep 2041403 = 3062105) B3062105
theorem B15501941 : Blo 2039435 15501941 := bbase (se 5 (by rfl) ⟨726653, by rfl⟩ : syracuseStep 15501941 = 1453307) (by norm_num)
theorem B10334627 : Blo 2039435 10334627 := bstep (se 1 (by rfl) ⟨7750970, by rfl⟩ : syracuseStep 10334627 = 15501941) B15501941
theorem B6889751 : Blo 2039435 6889751 := bstep (se 1 (by rfl) ⟨5167313, by rfl⟩ : syracuseStep 6889751 = 10334627) B10334627
theorem B4593167 : Blo 2039435 4593167 := bstep (se 1 (by rfl) ⟨3444875, by rfl⟩ : syracuseStep 4593167 = 6889751) B6889751
theorem B3062111 : Blo 2039435 3062111 := bstep (se 1 (by rfl) ⟨2296583, by rfl⟩ : syracuseStep 3062111 = 4593167) B4593167
theorem B2041407 : Blo 2039435 2041407 := bstep (se 1 (by rfl) ⟨1531055, by rfl⟩ : syracuseStep 2041407 = 3062111) B3062111
theorem B3062117 : Blo 2039435 3062117 := bbase (se 4 (by rfl) ⟨287073, by rfl⟩ : syracuseStep 3062117 = 574147) (by norm_num)
theorem B2041411 : Blo 2039435 2041411 := bstep (se 1 (by rfl) ⟨1531058, by rfl⟩ : syracuseStep 2041411 = 3062117) B3062117
theorem B3875501 : Blo 2039435 3875501 := bbase (se 3 (by rfl) ⟨726656, by rfl⟩ : syracuseStep 3875501 = 1453313) (by norm_num)
theorem B2583667 : Blo 2039435 2583667 := bstep (se 1 (by rfl) ⟨1937750, by rfl⟩ : syracuseStep 2583667 = 3875501) B3875501
theorem B3444889 : Blo 2039435 3444889 := bstep (se 2 (by rfl) ⟨1291833, by rfl⟩ : syracuseStep 3444889 = 2583667) B2583667
theorem B4593185 : Blo 2039435 4593185 := bstep (se 2 (by rfl) ⟨1722444, by rfl⟩ : syracuseStep 4593185 = 3444889) B3444889
theorem B3062123 : Blo 2039435 3062123 := bstep (se 1 (by rfl) ⟨2296592, by rfl⟩ : syracuseStep 3062123 = 4593185) B4593185
theorem B2041415 : Blo 2039435 2041415 := bstep (se 1 (by rfl) ⟨1531061, by rfl⟩ : syracuseStep 2041415 = 3062123) B3062123
theorem B2296597 : Blo 2039435 2296597 := bbase (se 6 (by rfl) ⟨53826, by rfl⟩ : syracuseStep 2296597 = 107653) (by norm_num)
theorem B3062129 : Blo 2039435 3062129 := bstep (se 2 (by rfl) ⟨1148298, by rfl⟩ : syracuseStep 3062129 = 2296597) B2296597
theorem B2041419 : Blo 2039435 2041419 := bstep (se 1 (by rfl) ⟨1531064, by rfl⟩ : syracuseStep 2041419 = 3062129) B3062129
theorem B2583677 : Blo 2039435 2583677 := bbase (se 3 (by rfl) ⟨484439, by rfl⟩ : syracuseStep 2583677 = 968879) (by norm_num)
theorem B6889805 : Blo 2039435 6889805 := bstep (se 3 (by rfl) ⟨1291838, by rfl⟩ : syracuseStep 6889805 = 2583677) B2583677
theorem B4593203 : Blo 2039435 4593203 := bstep (se 1 (by rfl) ⟨3444902, by rfl⟩ : syracuseStep 4593203 = 6889805) B6889805
theorem B3062135 : Blo 2039435 3062135 := bstep (se 1 (by rfl) ⟨2296601, by rfl⟩ : syracuseStep 3062135 = 4593203) B4593203
theorem B2041423 : Blo 2039435 2041423 := bstep (se 1 (by rfl) ⟨1531067, by rfl⟩ : syracuseStep 2041423 = 3062135) B3062135
theorem B3062141 : Blo 2039435 3062141 := bbase (se 3 (by rfl) ⟨574151, by rfl⟩ : syracuseStep 3062141 = 1148303) (by norm_num)
theorem B2041427 : Blo 2039435 2041427 := bstep (se 1 (by rfl) ⟨1531070, by rfl⟩ : syracuseStep 2041427 = 3062141) B3062141
theorem B4593221 : Blo 2039435 4593221 := bbase (se 4 (by rfl) ⟨430614, by rfl⟩ : syracuseStep 4593221 = 861229) (by norm_num)
theorem B3062147 : Blo 2039435 3062147 := bstep (se 1 (by rfl) ⟨2296610, by rfl⟩ : syracuseStep 3062147 = 4593221) B4593221
theorem B2041431 : Blo 2039435 2041431 := bstep (se 1 (by rfl) ⟨1531073, by rfl⟩ : syracuseStep 2041431 = 3062147) B3062147
theorem B4904981 : Blo 2039435 4904981 := bbase (se 6 (by rfl) ⟨114960, by rfl⟩ : syracuseStep 4904981 = 229921) (by norm_num)
theorem B3269987 : Blo 2039435 3269987 := bstep (se 1 (by rfl) ⟨2452490, by rfl⟩ : syracuseStep 3269987 = 4904981) B4904981
theorem B2179991 : Blo 2039435 2179991 := bstep (se 1 (by rfl) ⟨1634993, by rfl⟩ : syracuseStep 2179991 = 3269987) B3269987
theorem B5813309 : Blo 2039435 5813309 := bstep (se 3 (by rfl) ⟨1089995, by rfl⟩ : syracuseStep 5813309 = 2179991) B2179991
theorem B3875539 : Blo 2039435 3875539 := bstep (se 1 (by rfl) ⟨2906654, by rfl⟩ : syracuseStep 3875539 = 5813309) B5813309
theorem B5167385 : Blo 2039435 5167385 := bstep (se 2 (by rfl) ⟨1937769, by rfl⟩ : syracuseStep 5167385 = 3875539) B3875539
theorem B3444923 : Blo 2039435 3444923 := bstep (se 1 (by rfl) ⟨2583692, by rfl⟩ : syracuseStep 3444923 = 5167385) B5167385
theorem B2296615 : Blo 2039435 2296615 := bstep (se 1 (by rfl) ⟨1722461, by rfl⟩ : syracuseStep 2296615 = 3444923) B3444923
theorem B3062153 : Blo 2039435 3062153 := bstep (se 2 (by rfl) ⟨1148307, by rfl⟩ : syracuseStep 3062153 = 2296615) B2296615
theorem B2041435 : Blo 2039435 2041435 := bstep (se 1 (by rfl) ⟨1531076, by rfl⟩ : syracuseStep 2041435 = 3062153) B3062153
theorem C0 (j : ℕ) (h1 : 509858 ≤ j) (h2 : j ≤ 510358) : Blo 2039435 (4 * j + 3) := by
  interval_cases j
  · exact B2039435
  · exact B2039439
  · exact B2039443
  · exact B2039447
  · exact B2039451
  · exact B2039455
  · exact B2039459
  · exact B2039463
  · exact B2039467
  · exact B2039471
  · exact B2039475
  · exact B2039479
  · exact B2039483
  · exact B2039487
  · exact B2039491
  · exact B2039495
  · exact B2039499
  · exact B2039503
  · exact B2039507
  · exact B2039511
  · exact B2039515
  · exact B2039519
  · exact B2039523
  · exact B2039527
  · exact B2039531
  · exact B2039535
  · exact B2039539
  · exact B2039543
  · exact B2039547
  · exact B2039551
  · exact B2039555
  · exact B2039559
  · exact B2039563
  · exact B2039567
  · exact B2039571
  · exact B2039575
  · exact B2039579
  · exact B2039583
  · exact B2039587
  · exact B2039591
  · exact B2039595
  · exact B2039599
  · exact B2039603
  · exact B2039607
  · exact B2039611
  · exact B2039615
  · exact B2039619
  · exact B2039623
  · exact B2039627
  · exact B2039631
  · exact B2039635
  · exact B2039639
  · exact B2039643
  · exact B2039647
  · exact B2039651
  · exact B2039655
  · exact B2039659
  · exact B2039663
  · exact B2039667
  · exact B2039671
  · exact B2039675
  · exact B2039679
  · exact B2039683
  · exact B2039687
  · exact B2039691
  · exact B2039695
  · exact B2039699
  · exact B2039703
  · exact B2039707
  · exact B2039711
  · exact B2039715
  · exact B2039719
  · exact B2039723
  · exact B2039727
  · exact B2039731
  · exact B2039735
  · exact B2039739
  · exact B2039743
  · exact B2039747
  · exact B2039751
  · exact B2039755
  · exact B2039759
  · exact B2039763
  · exact B2039767
  · exact B2039771
  · exact B2039775
  · exact B2039779
  · exact B2039783
  · exact B2039787
  · exact B2039791
  · exact B2039795
  · exact B2039799
  · exact B2039803
  · exact B2039807
  · exact B2039811
  · exact B2039815
  · exact B2039819
  · exact B2039823
  · exact B2039827
  · exact B2039831
  · exact B2039835
  · exact B2039839
  · exact B2039843
  · exact B2039847
  · exact B2039851
  · exact B2039855
  · exact B2039859
  · exact B2039863
  · exact B2039867
  · exact B2039871
  · exact B2039875
  · exact B2039879
  · exact B2039883
  · exact B2039887
  · exact B2039891
  · exact B2039895
  · exact B2039899
  · exact B2039903
  · exact B2039907
  · exact B2039911
  · exact B2039915
  · exact B2039919
  · exact B2039923
  · exact B2039927
  · exact B2039931
  · exact B2039935
  · exact B2039939
  · exact B2039943
  · exact B2039947
  · exact B2039951
  · exact B2039955
  · exact B2039959
  · exact B2039963
  · exact B2039967
  · exact B2039971
  · exact B2039975
  · exact B2039979
  · exact B2039983
  · exact B2039987
  · exact B2039991
  · exact B2039995
  · exact B2039999
  · exact B2040003
  · exact B2040007
  · exact B2040011
  · exact B2040015
  · exact B2040019
  · exact B2040023
  · exact B2040027
  · exact B2040031
  · exact B2040035
  · exact B2040039
  · exact B2040043
  · exact B2040047
  · exact B2040051
  · exact B2040055
  · exact B2040059
  · exact B2040063
  · exact B2040067
  · exact B2040071
  · exact B2040075
  · exact B2040079
  · exact B2040083
  · exact B2040087
  · exact B2040091
  · exact B2040095
  · exact B2040099
  · exact B2040103
  · exact B2040107
  · exact B2040111
  · exact B2040115
  · exact B2040119
  · exact B2040123
  · exact B2040127
  · exact B2040131
  · exact B2040135
  · exact B2040139
  · exact B2040143
  · exact B2040147
  · exact B2040151
  · exact B2040155
  · exact B2040159
  · exact B2040163
  · exact B2040167
  · exact B2040171
  · exact B2040175
  · exact B2040179
  · exact B2040183
  · exact B2040187
  · exact B2040191
  · exact B2040195
  · exact B2040199
  · exact B2040203
  · exact B2040207
  · exact B2040211
  · exact B2040215
  · exact B2040219
  · exact B2040223
  · exact B2040227
  · exact B2040231
  · exact B2040235
  · exact B2040239
  · exact B2040243
  · exact B2040247
  · exact B2040251
  · exact B2040255
  · exact B2040259
  · exact B2040263
  · exact B2040267
  · exact B2040271
  · exact B2040275
  · exact B2040279
  · exact B2040283
  · exact B2040287
  · exact B2040291
  · exact B2040295
  · exact B2040299
  · exact B2040303
  · exact B2040307
  · exact B2040311
  · exact B2040315
  · exact B2040319
  · exact B2040323
  · exact B2040327
  · exact B2040331
  · exact B2040335
  · exact B2040339
  · exact B2040343
  · exact B2040347
  · exact B2040351
  · exact B2040355
  · exact B2040359
  · exact B2040363
  · exact B2040367
  · exact B2040371
  · exact B2040375
  · exact B2040379
  · exact B2040383
  · exact B2040387
  · exact B2040391
  · exact B2040395
  · exact B2040399
  · exact B2040403
  · exact B2040407
  · exact B2040411
  · exact B2040415
  · exact B2040419
  · exact B2040423
  · exact B2040427
  · exact B2040431
  · exact B2040435
  · exact B2040439
  · exact B2040443
  · exact B2040447
  · exact B2040451
  · exact B2040455
  · exact B2040459
  · exact B2040463
  · exact B2040467
  · exact B2040471
  · exact B2040475
  · exact B2040479
  · exact B2040483
  · exact B2040487
  · exact B2040491
  · exact B2040495
  · exact B2040499
  · exact B2040503
  · exact B2040507
  · exact B2040511
  · exact B2040515
  · exact B2040519
  · exact B2040523
  · exact B2040527
  · exact B2040531
  · exact B2040535
  · exact B2040539
  · exact B2040543
  · exact B2040547
  · exact B2040551
  · exact B2040555
  · exact B2040559
  · exact B2040563
  · exact B2040567
  · exact B2040571
  · exact B2040575
  · exact B2040579
  · exact B2040583
  · exact B2040587
  · exact B2040591
  · exact B2040595
  · exact B2040599
  · exact B2040603
  · exact B2040607
  · exact B2040611
  · exact B2040615
  · exact B2040619
  · exact B2040623
  · exact B2040627
  · exact B2040631
  · exact B2040635
  · exact B2040639
  · exact B2040643
  · exact B2040647
  · exact B2040651
  · exact B2040655
  · exact B2040659
  · exact B2040663
  · exact B2040667
  · exact B2040671
  · exact B2040675
  · exact B2040679
  · exact B2040683
  · exact B2040687
  · exact B2040691
  · exact B2040695
  · exact B2040699
  · exact B2040703
  · exact B2040707
  · exact B2040711
  · exact B2040715
  · exact B2040719
  · exact B2040723
  · exact B2040727
  · exact B2040731
  · exact B2040735
  · exact B2040739
  · exact B2040743
  · exact B2040747
  · exact B2040751
  · exact B2040755
  · exact B2040759
  · exact B2040763
  · exact B2040767
  · exact B2040771
  · exact B2040775
  · exact B2040779
  · exact B2040783
  · exact B2040787
  · exact B2040791
  · exact B2040795
  · exact B2040799
  · exact B2040803
  · exact B2040807
  · exact B2040811
  · exact B2040815
  · exact B2040819
  · exact B2040823
  · exact B2040827
  · exact B2040831
  · exact B2040835
  · exact B2040839
  · exact B2040843
  · exact B2040847
  · exact B2040851
  · exact B2040855
  · exact B2040859
  · exact B2040863
  · exact B2040867
  · exact B2040871
  · exact B2040875
  · exact B2040879
  · exact B2040883
  · exact B2040887
  · exact B2040891
  · exact B2040895
  · exact B2040899
  · exact B2040903
  · exact B2040907
  · exact B2040911
  · exact B2040915
  · exact B2040919
  · exact B2040923
  · exact B2040927
  · exact B2040931
  · exact B2040935
  · exact B2040939
  · exact B2040943
  · exact B2040947
  · exact B2040951
  · exact B2040955
  · exact B2040959
  · exact B2040963
  · exact B2040967
  · exact B2040971
  · exact B2040975
  · exact B2040979
  · exact B2040983
  · exact B2040987
  · exact B2040991
  · exact B2040995
  · exact B2040999
  · exact B2041003
  · exact B2041007
  · exact B2041011
  · exact B2041015
  · exact B2041019
  · exact B2041023
  · exact B2041027
  · exact B2041031
  · exact B2041035
  · exact B2041039
  · exact B2041043
  · exact B2041047
  · exact B2041051
  · exact B2041055
  · exact B2041059
  · exact B2041063
  · exact B2041067
  · exact B2041071
  · exact B2041075
  · exact B2041079
  · exact B2041083
  · exact B2041087
  · exact B2041091
  · exact B2041095
  · exact B2041099
  · exact B2041103
  · exact B2041107
  · exact B2041111
  · exact B2041115
  · exact B2041119
  · exact B2041123
  · exact B2041127
  · exact B2041131
  · exact B2041135
  · exact B2041139
  · exact B2041143
  · exact B2041147
  · exact B2041151
  · exact B2041155
  · exact B2041159
  · exact B2041163
  · exact B2041167
  · exact B2041171
  · exact B2041175
  · exact B2041179
  · exact B2041183
  · exact B2041187
  · exact B2041191
  · exact B2041195
  · exact B2041199
  · exact B2041203
  · exact B2041207
  · exact B2041211
  · exact B2041215
  · exact B2041219
  · exact B2041223
  · exact B2041227
  · exact B2041231
  · exact B2041235
  · exact B2041239
  · exact B2041243
  · exact B2041247
  · exact B2041251
  · exact B2041255
  · exact B2041259
  · exact B2041263
  · exact B2041267
  · exact B2041271
  · exact B2041275
  · exact B2041279
  · exact B2041283
  · exact B2041287
  · exact B2041291
  · exact B2041295
  · exact B2041299
  · exact B2041303
  · exact B2041307
  · exact B2041311
  · exact B2041315
  · exact B2041319
  · exact B2041323
  · exact B2041327
  · exact B2041331
  · exact B2041335
  · exact B2041339
  · exact B2041343
  · exact B2041347
  · exact B2041351
  · exact B2041355
  · exact B2041359
  · exact B2041363
  · exact B2041367
  · exact B2041371
  · exact B2041375
  · exact B2041379
  · exact B2041383
  · exact B2041387
  · exact B2041391
  · exact B2041395
  · exact B2041399
  · exact B2041403
  · exact B2041407
  · exact B2041411
  · exact B2041415
  · exact B2041419
  · exact B2041423
  · exact B2041427
  · exact B2041431
  · exact B2041435
theorem solution (m : ℕ) (hlo : 2039435 ≤ m) (hhi : m ≤ 2041435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 509858 ≤ j := by omega
    have hj2 : j ≤ 510358 := by omega
    have hb : Blo 2039435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
