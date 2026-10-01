-- Prove2me | solution 1 for syracuse_descends_range_1997435_1999435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:48:30.422363+00:00
-- url     : https://prove2.me/submissions/a1b8ec99-ee55-4b7c-ab10-1d8cf94d33d3

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

theorem B2528005 : Blo 1997435 2528005 := bbase (se 4 (by rfl) ⟨237000, by rfl⟩ : syracuseStep 2528005 = 474001) (by norm_num)
theorem B3370673 : Blo 1997435 3370673 := bstep (se 2 (by rfl) ⟨1264002, by rfl⟩ : syracuseStep 3370673 = 2528005) B2528005
theorem B2247115 : Blo 1997435 2247115 := bstep (se 1 (by rfl) ⟨1685336, by rfl⟩ : syracuseStep 2247115 = 3370673) B3370673
theorem B2996153 : Blo 1997435 2996153 := bstep (se 2 (by rfl) ⟨1123557, by rfl⟩ : syracuseStep 2996153 = 2247115) B2247115
theorem B1997435 : Blo 1997435 1997435 := bstep (se 1 (by rfl) ⟨1498076, by rfl⟩ : syracuseStep 1997435 = 2996153) B2996153
theorem B4799269 : Blo 1997435 4799269 := bbase (se 4 (by rfl) ⟨449931, by rfl⟩ : syracuseStep 4799269 = 899863) (by norm_num)
theorem B25596101 : Blo 1997435 25596101 := bstep (se 4 (by rfl) ⟨2399634, by rfl⟩ : syracuseStep 25596101 = 4799269) B4799269
theorem B17064067 : Blo 1997435 17064067 := bstep (se 1 (by rfl) ⟨12798050, by rfl⟩ : syracuseStep 17064067 = 25596101) B25596101
theorem B22752089 : Blo 1997435 22752089 := bstep (se 2 (by rfl) ⟨8532033, by rfl⟩ : syracuseStep 22752089 = 17064067) B17064067
theorem B15168059 : Blo 1997435 15168059 := bstep (se 1 (by rfl) ⟨11376044, by rfl⟩ : syracuseStep 15168059 = 22752089) B22752089
theorem B10112039 : Blo 1997435 10112039 := bstep (se 1 (by rfl) ⟨7584029, by rfl⟩ : syracuseStep 10112039 = 15168059) B15168059
theorem B6741359 : Blo 1997435 6741359 := bstep (se 1 (by rfl) ⟨5056019, by rfl⟩ : syracuseStep 6741359 = 10112039) B10112039
theorem B4494239 : Blo 1997435 4494239 := bstep (se 1 (by rfl) ⟨3370679, by rfl⟩ : syracuseStep 4494239 = 6741359) B6741359
theorem B2996159 : Blo 1997435 2996159 := bstep (se 1 (by rfl) ⟨2247119, by rfl⟩ : syracuseStep 2996159 = 4494239) B4494239
theorem B1997439 : Blo 1997435 1997439 := bstep (se 1 (by rfl) ⟨1498079, by rfl⟩ : syracuseStep 1997439 = 2996159) B2996159
theorem B2996165 : Blo 1997435 2996165 := bbase (se 4 (by rfl) ⟨280890, by rfl⟩ : syracuseStep 2996165 = 561781) (by norm_num)
theorem B1997443 : Blo 1997435 1997443 := bstep (se 1 (by rfl) ⟨1498082, by rfl⟩ : syracuseStep 1997443 = 2996165) B2996165
theorem B3370693 : Blo 1997435 3370693 := bbase (se 4 (by rfl) ⟨316002, by rfl⟩ : syracuseStep 3370693 = 632005) (by norm_num)
theorem B4494257 : Blo 1997435 4494257 := bstep (se 2 (by rfl) ⟨1685346, by rfl⟩ : syracuseStep 4494257 = 3370693) B3370693
theorem B2996171 : Blo 1997435 2996171 := bstep (se 1 (by rfl) ⟨2247128, by rfl⟩ : syracuseStep 2996171 = 4494257) B4494257
theorem B1997447 : Blo 1997435 1997447 := bstep (se 1 (by rfl) ⟨1498085, by rfl⟩ : syracuseStep 1997447 = 2996171) B2996171
theorem B2247133 : Blo 1997435 2247133 := bbase (se 3 (by rfl) ⟨421337, by rfl⟩ : syracuseStep 2247133 = 842675) (by norm_num)
theorem B2996177 : Blo 1997435 2996177 := bstep (se 2 (by rfl) ⟨1123566, by rfl⟩ : syracuseStep 2996177 = 2247133) B2247133
theorem B1997451 : Blo 1997435 1997451 := bstep (se 1 (by rfl) ⟨1498088, by rfl⟩ : syracuseStep 1997451 = 2996177) B2996177
theorem B6741413 : Blo 1997435 6741413 := bbase (se 4 (by rfl) ⟨632007, by rfl⟩ : syracuseStep 6741413 = 1264015) (by norm_num)
theorem B4494275 : Blo 1997435 4494275 := bstep (se 1 (by rfl) ⟨3370706, by rfl⟩ : syracuseStep 4494275 = 6741413) B6741413
theorem B2996183 : Blo 1997435 2996183 := bstep (se 1 (by rfl) ⟨2247137, by rfl⟩ : syracuseStep 2996183 = 4494275) B4494275
theorem B1997455 : Blo 1997435 1997455 := bstep (se 1 (by rfl) ⟨1498091, by rfl⟩ : syracuseStep 1997455 = 2996183) B2996183
theorem B2996189 : Blo 1997435 2996189 := bbase (se 3 (by rfl) ⟨561785, by rfl⟩ : syracuseStep 2996189 = 1123571) (by norm_num)
theorem B1997459 : Blo 1997435 1997459 := bstep (se 1 (by rfl) ⟨1498094, by rfl⟩ : syracuseStep 1997459 = 2996189) B2996189
theorem B4494293 : Blo 1997435 4494293 := bbase (se 7 (by rfl) ⟨52667, by rfl⟩ : syracuseStep 4494293 = 105335) (by norm_num)
theorem B2996195 : Blo 1997435 2996195 := bstep (se 1 (by rfl) ⟨2247146, by rfl⟩ : syracuseStep 2996195 = 4494293) B4494293
theorem B1997463 : Blo 1997435 1997463 := bstep (se 1 (by rfl) ⟨1498097, by rfl⟩ : syracuseStep 1997463 = 2996195) B2996195
theorem B3416717 : Blo 1997435 3416717 := bbase (se 3 (by rfl) ⟨640634, by rfl⟩ : syracuseStep 3416717 = 1281269) (by norm_num)
theorem B2277811 : Blo 1997435 2277811 := bstep (se 1 (by rfl) ⟨1708358, by rfl⟩ : syracuseStep 2277811 = 3416717) B3416717
theorem B12148325 : Blo 1997435 12148325 := bstep (se 4 (by rfl) ⟨1138905, by rfl⟩ : syracuseStep 12148325 = 2277811) B2277811
theorem B8098883 : Blo 1997435 8098883 := bstep (se 1 (by rfl) ⟨6074162, by rfl⟩ : syracuseStep 8098883 = 12148325) B12148325
theorem B5399255 : Blo 1997435 5399255 := bstep (se 1 (by rfl) ⟨4049441, by rfl⟩ : syracuseStep 5399255 = 8098883) B8098883
theorem B14398013 : Blo 1997435 14398013 := bstep (se 3 (by rfl) ⟨2699627, by rfl⟩ : syracuseStep 14398013 = 5399255) B5399255
theorem B9598675 : Blo 1997435 9598675 := bstep (se 1 (by rfl) ⟨7199006, by rfl⟩ : syracuseStep 9598675 = 14398013) B14398013
theorem B12798233 : Blo 1997435 12798233 := bstep (se 2 (by rfl) ⟨4799337, by rfl⟩ : syracuseStep 12798233 = 9598675) B9598675
theorem B8532155 : Blo 1997435 8532155 := bstep (se 1 (by rfl) ⟨6399116, by rfl⟩ : syracuseStep 8532155 = 12798233) B12798233
theorem B5688103 : Blo 1997435 5688103 := bstep (se 1 (by rfl) ⟨4266077, by rfl⟩ : syracuseStep 5688103 = 8532155) B8532155
theorem B7584137 : Blo 1997435 7584137 := bstep (se 2 (by rfl) ⟨2844051, by rfl⟩ : syracuseStep 7584137 = 5688103) B5688103
theorem B5056091 : Blo 1997435 5056091 := bstep (se 1 (by rfl) ⟨3792068, by rfl⟩ : syracuseStep 5056091 = 7584137) B7584137
theorem B3370727 : Blo 1997435 3370727 := bstep (se 1 (by rfl) ⟨2528045, by rfl⟩ : syracuseStep 3370727 = 5056091) B5056091
theorem B2247151 : Blo 1997435 2247151 := bstep (se 1 (by rfl) ⟨1685363, by rfl⟩ : syracuseStep 2247151 = 3370727) B3370727
theorem B2996201 : Blo 1997435 2996201 := bstep (se 2 (by rfl) ⟨1123575, by rfl⟩ : syracuseStep 2996201 = 2247151) B2247151
theorem B1997467 : Blo 1997435 1997467 := bstep (se 1 (by rfl) ⟨1498100, by rfl⟩ : syracuseStep 1997467 = 2996201) B2996201
theorem B17064341 : Blo 1997435 17064341 := bbase (se 6 (by rfl) ⟨399945, by rfl⟩ : syracuseStep 17064341 = 799891) (by norm_num)
theorem B11376227 : Blo 1997435 11376227 := bstep (se 1 (by rfl) ⟨8532170, by rfl⟩ : syracuseStep 11376227 = 17064341) B17064341
theorem B7584151 : Blo 1997435 7584151 := bstep (se 1 (by rfl) ⟨5688113, by rfl⟩ : syracuseStep 7584151 = 11376227) B11376227
theorem B10112201 : Blo 1997435 10112201 := bstep (se 2 (by rfl) ⟨3792075, by rfl⟩ : syracuseStep 10112201 = 7584151) B7584151
theorem B6741467 : Blo 1997435 6741467 := bstep (se 1 (by rfl) ⟨5056100, by rfl⟩ : syracuseStep 6741467 = 10112201) B10112201
theorem B4494311 : Blo 1997435 4494311 := bstep (se 1 (by rfl) ⟨3370733, by rfl⟩ : syracuseStep 4494311 = 6741467) B6741467
theorem B2996207 : Blo 1997435 2996207 := bstep (se 1 (by rfl) ⟨2247155, by rfl⟩ : syracuseStep 2996207 = 4494311) B4494311
theorem B1997471 : Blo 1997435 1997471 := bstep (se 1 (by rfl) ⟨1498103, by rfl⟩ : syracuseStep 1997471 = 2996207) B2996207
theorem B2996213 : Blo 1997435 2996213 := bbase (se 5 (by rfl) ⟨140447, by rfl⟩ : syracuseStep 2996213 = 280895) (by norm_num)
theorem B1997475 : Blo 1997435 1997475 := bstep (se 1 (by rfl) ⟨1498106, by rfl⟩ : syracuseStep 1997475 = 2996213) B2996213
theorem B3599525 : Blo 1997435 3599525 := bbase (se 4 (by rfl) ⟨337455, by rfl⟩ : syracuseStep 3599525 = 674911) (by norm_num)
theorem B9598733 : Blo 1997435 9598733 := bstep (se 3 (by rfl) ⟨1799762, by rfl⟩ : syracuseStep 9598733 = 3599525) B3599525
theorem B6399155 : Blo 1997435 6399155 := bstep (se 1 (by rfl) ⟨4799366, by rfl⟩ : syracuseStep 6399155 = 9598733) B9598733
theorem B4266103 : Blo 1997435 4266103 := bstep (se 1 (by rfl) ⟨3199577, by rfl⟩ : syracuseStep 4266103 = 6399155) B6399155
theorem B5688137 : Blo 1997435 5688137 := bstep (se 2 (by rfl) ⟨2133051, by rfl⟩ : syracuseStep 5688137 = 4266103) B4266103
theorem B3792091 : Blo 1997435 3792091 := bstep (se 1 (by rfl) ⟨2844068, by rfl⟩ : syracuseStep 3792091 = 5688137) B5688137
theorem B5056121 : Blo 1997435 5056121 := bstep (se 2 (by rfl) ⟨1896045, by rfl⟩ : syracuseStep 5056121 = 3792091) B3792091
theorem B3370747 : Blo 1997435 3370747 := bstep (se 1 (by rfl) ⟨2528060, by rfl⟩ : syracuseStep 3370747 = 5056121) B5056121
theorem B4494329 : Blo 1997435 4494329 := bstep (se 2 (by rfl) ⟨1685373, by rfl⟩ : syracuseStep 4494329 = 3370747) B3370747
theorem B2996219 : Blo 1997435 2996219 := bstep (se 1 (by rfl) ⟨2247164, by rfl⟩ : syracuseStep 2996219 = 4494329) B4494329
theorem B1997479 : Blo 1997435 1997479 := bstep (se 1 (by rfl) ⟨1498109, by rfl⟩ : syracuseStep 1997479 = 2996219) B2996219
theorem B2247169 : Blo 1997435 2247169 := bbase (se 2 (by rfl) ⟨842688, by rfl⟩ : syracuseStep 2247169 = 1685377) (by norm_num)
theorem B2996225 : Blo 1997435 2996225 := bstep (se 2 (by rfl) ⟨1123584, by rfl⟩ : syracuseStep 2996225 = 2247169) B2247169
theorem B1997483 : Blo 1997435 1997483 := bstep (se 1 (by rfl) ⟨1498112, by rfl⟩ : syracuseStep 1997483 = 2996225) B2996225
theorem B5056141 : Blo 1997435 5056141 := bbase (se 3 (by rfl) ⟨948026, by rfl⟩ : syracuseStep 5056141 = 1896053) (by norm_num)
theorem B6741521 : Blo 1997435 6741521 := bstep (se 2 (by rfl) ⟨2528070, by rfl⟩ : syracuseStep 6741521 = 5056141) B5056141
theorem B4494347 : Blo 1997435 4494347 := bstep (se 1 (by rfl) ⟨3370760, by rfl⟩ : syracuseStep 4494347 = 6741521) B6741521
theorem B2996231 : Blo 1997435 2996231 := bstep (se 1 (by rfl) ⟨2247173, by rfl⟩ : syracuseStep 2996231 = 4494347) B4494347
theorem B1997487 : Blo 1997435 1997487 := bstep (se 1 (by rfl) ⟨1498115, by rfl⟩ : syracuseStep 1997487 = 2996231) B2996231
theorem B2996237 : Blo 1997435 2996237 := bbase (se 3 (by rfl) ⟨561794, by rfl⟩ : syracuseStep 2996237 = 1123589) (by norm_num)
theorem B1997491 : Blo 1997435 1997491 := bstep (se 1 (by rfl) ⟨1498118, by rfl⟩ : syracuseStep 1997491 = 2996237) B2996237
theorem B4494365 : Blo 1997435 4494365 := bbase (se 3 (by rfl) ⟨842693, by rfl⟩ : syracuseStep 4494365 = 1685387) (by norm_num)
theorem B2996243 : Blo 1997435 2996243 := bstep (se 1 (by rfl) ⟨2247182, by rfl⟩ : syracuseStep 2996243 = 4494365) B4494365
theorem B1997495 : Blo 1997435 1997495 := bstep (se 1 (by rfl) ⟨1498121, by rfl⟩ : syracuseStep 1997495 = 2996243) B2996243
theorem B3370781 : Blo 1997435 3370781 := bbase (se 3 (by rfl) ⟨632021, by rfl⟩ : syracuseStep 3370781 = 1264043) (by norm_num)
theorem B2247187 : Blo 1997435 2247187 := bstep (se 1 (by rfl) ⟨1685390, by rfl⟩ : syracuseStep 2247187 = 3370781) B3370781
theorem B2996249 : Blo 1997435 2996249 := bstep (se 2 (by rfl) ⟨1123593, by rfl⟩ : syracuseStep 2996249 = 2247187) B2247187
theorem B1997499 : Blo 1997435 1997499 := bstep (se 1 (by rfl) ⟨1498124, by rfl⟩ : syracuseStep 1997499 = 2996249) B2996249
theorem B30750997 : Blo 1997435 30750997 := bbase (se 6 (by rfl) ⟨720726, by rfl⟩ : syracuseStep 30750997 = 1441453) (by norm_num)
theorem B41001329 : Blo 1997435 41001329 := bstep (se 2 (by rfl) ⟨15375498, by rfl⟩ : syracuseStep 41001329 = 30750997) B30750997
theorem B27334219 : Blo 1997435 27334219 := bstep (se 1 (by rfl) ⟨20500664, by rfl⟩ : syracuseStep 27334219 = 41001329) B41001329
theorem B36445625 : Blo 1997435 36445625 := bstep (se 2 (by rfl) ⟨13667109, by rfl⟩ : syracuseStep 36445625 = 27334219) B27334219
theorem B24297083 : Blo 1997435 24297083 := bstep (se 1 (by rfl) ⟨18222812, by rfl⟩ : syracuseStep 24297083 = 36445625) B36445625
theorem B16198055 : Blo 1997435 16198055 := bstep (se 1 (by rfl) ⟨12148541, by rfl⟩ : syracuseStep 16198055 = 24297083) B24297083
theorem B10798703 : Blo 1997435 10798703 := bstep (se 1 (by rfl) ⟨8099027, by rfl⟩ : syracuseStep 10798703 = 16198055) B16198055
theorem B7199135 : Blo 1997435 7199135 := bstep (se 1 (by rfl) ⟨5399351, by rfl⟩ : syracuseStep 7199135 = 10798703) B10798703
theorem B4799423 : Blo 1997435 4799423 := bstep (se 1 (by rfl) ⟨3599567, by rfl⟩ : syracuseStep 4799423 = 7199135) B7199135
theorem B12798461 : Blo 1997435 12798461 := bstep (se 3 (by rfl) ⟨2399711, by rfl⟩ : syracuseStep 12798461 = 4799423) B4799423
theorem B8532307 : Blo 1997435 8532307 := bstep (se 1 (by rfl) ⟨6399230, by rfl⟩ : syracuseStep 8532307 = 12798461) B12798461
theorem B11376409 : Blo 1997435 11376409 := bstep (se 2 (by rfl) ⟨4266153, by rfl⟩ : syracuseStep 11376409 = 8532307) B8532307
theorem B15168545 : Blo 1997435 15168545 := bstep (se 2 (by rfl) ⟨5688204, by rfl⟩ : syracuseStep 15168545 = 11376409) B11376409
theorem B10112363 : Blo 1997435 10112363 := bstep (se 1 (by rfl) ⟨7584272, by rfl⟩ : syracuseStep 10112363 = 15168545) B15168545
theorem B6741575 : Blo 1997435 6741575 := bstep (se 1 (by rfl) ⟨5056181, by rfl⟩ : syracuseStep 6741575 = 10112363) B10112363
theorem B4494383 : Blo 1997435 4494383 := bstep (se 1 (by rfl) ⟨3370787, by rfl⟩ : syracuseStep 4494383 = 6741575) B6741575
theorem B2996255 : Blo 1997435 2996255 := bstep (se 1 (by rfl) ⟨2247191, by rfl⟩ : syracuseStep 2996255 = 4494383) B4494383
theorem B1997503 : Blo 1997435 1997503 := bstep (se 1 (by rfl) ⟨1498127, by rfl⟩ : syracuseStep 1997503 = 2996255) B2996255
theorem B2996261 : Blo 1997435 2996261 := bbase (se 4 (by rfl) ⟨280899, by rfl⟩ : syracuseStep 2996261 = 561799) (by norm_num)
theorem B1997507 : Blo 1997435 1997507 := bstep (se 1 (by rfl) ⟨1498130, by rfl⟩ : syracuseStep 1997507 = 2996261) B2996261
theorem B2528101 : Blo 1997435 2528101 := bbase (se 4 (by rfl) ⟨237009, by rfl⟩ : syracuseStep 2528101 = 474019) (by norm_num)
theorem B3370801 : Blo 1997435 3370801 := bstep (se 2 (by rfl) ⟨1264050, by rfl⟩ : syracuseStep 3370801 = 2528101) B2528101
theorem B4494401 : Blo 1997435 4494401 := bstep (se 2 (by rfl) ⟨1685400, by rfl⟩ : syracuseStep 4494401 = 3370801) B3370801
theorem B2996267 : Blo 1997435 2996267 := bstep (se 1 (by rfl) ⟨2247200, by rfl⟩ : syracuseStep 2996267 = 4494401) B4494401
theorem B1997511 : Blo 1997435 1997511 := bstep (se 1 (by rfl) ⟨1498133, by rfl⟩ : syracuseStep 1997511 = 2996267) B2996267
theorem B2247205 : Blo 1997435 2247205 := bbase (se 4 (by rfl) ⟨210675, by rfl⟩ : syracuseStep 2247205 = 421351) (by norm_num)
theorem B2996273 : Blo 1997435 2996273 := bstep (se 2 (by rfl) ⟨1123602, by rfl⟩ : syracuseStep 2996273 = 2247205) B2247205
theorem B1997515 : Blo 1997435 1997515 := bstep (se 1 (by rfl) ⟨1498136, by rfl⟩ : syracuseStep 1997515 = 2996273) B2996273
theorem B3599597 : Blo 1997435 3599597 := bbase (se 3 (by rfl) ⟨674924, by rfl⟩ : syracuseStep 3599597 = 1349849) (by norm_num)
theorem B9598925 : Blo 1997435 9598925 := bstep (se 3 (by rfl) ⟨1799798, by rfl⟩ : syracuseStep 9598925 = 3599597) B3599597
theorem B6399283 : Blo 1997435 6399283 := bstep (se 1 (by rfl) ⟨4799462, by rfl⟩ : syracuseStep 6399283 = 9598925) B9598925
theorem B8532377 : Blo 1997435 8532377 := bstep (se 2 (by rfl) ⟨3199641, by rfl⟩ : syracuseStep 8532377 = 6399283) B6399283
theorem B5688251 : Blo 1997435 5688251 := bstep (se 1 (by rfl) ⟨4266188, by rfl⟩ : syracuseStep 5688251 = 8532377) B8532377
theorem B3792167 : Blo 1997435 3792167 := bstep (se 1 (by rfl) ⟨2844125, by rfl⟩ : syracuseStep 3792167 = 5688251) B5688251
theorem B2528111 : Blo 1997435 2528111 := bstep (se 1 (by rfl) ⟨1896083, by rfl⟩ : syracuseStep 2528111 = 3792167) B3792167
theorem B6741629 : Blo 1997435 6741629 := bstep (se 3 (by rfl) ⟨1264055, by rfl⟩ : syracuseStep 6741629 = 2528111) B2528111
theorem B4494419 : Blo 1997435 4494419 := bstep (se 1 (by rfl) ⟨3370814, by rfl⟩ : syracuseStep 4494419 = 6741629) B6741629
theorem B2996279 : Blo 1997435 2996279 := bstep (se 1 (by rfl) ⟨2247209, by rfl⟩ : syracuseStep 2996279 = 4494419) B4494419
theorem B1997519 : Blo 1997435 1997519 := bstep (se 1 (by rfl) ⟨1498139, by rfl⟩ : syracuseStep 1997519 = 2996279) B2996279
theorem B2996285 : Blo 1997435 2996285 := bbase (se 3 (by rfl) ⟨561803, by rfl⟩ : syracuseStep 2996285 = 1123607) (by norm_num)
theorem B1997523 : Blo 1997435 1997523 := bstep (se 1 (by rfl) ⟨1498142, by rfl⟩ : syracuseStep 1997523 = 2996285) B2996285
theorem B4494437 : Blo 1997435 4494437 := bbase (se 4 (by rfl) ⟨421353, by rfl⟩ : syracuseStep 4494437 = 842707) (by norm_num)
theorem B2996291 : Blo 1997435 2996291 := bstep (se 1 (by rfl) ⟨2247218, by rfl⟩ : syracuseStep 2996291 = 4494437) B4494437
theorem B1997527 : Blo 1997435 1997527 := bstep (se 1 (by rfl) ⟨1498145, by rfl⟩ : syracuseStep 1997527 = 2996291) B2996291
theorem B5056253 : Blo 1997435 5056253 := bbase (se 3 (by rfl) ⟨948047, by rfl⟩ : syracuseStep 5056253 = 1896095) (by norm_num)
theorem B3370835 : Blo 1997435 3370835 := bstep (se 1 (by rfl) ⟨2528126, by rfl⟩ : syracuseStep 3370835 = 5056253) B5056253
theorem B2247223 : Blo 1997435 2247223 := bstep (se 1 (by rfl) ⟨1685417, by rfl⟩ : syracuseStep 2247223 = 3370835) B3370835
theorem B2996297 : Blo 1997435 2996297 := bstep (se 2 (by rfl) ⟨1123611, by rfl⟩ : syracuseStep 2996297 = 2247223) B2247223
theorem B1997531 : Blo 1997435 1997531 := bstep (se 1 (by rfl) ⟨1498148, by rfl⟩ : syracuseStep 1997531 = 2996297) B2996297
theorem B3792197 : Blo 1997435 3792197 := bbase (se 4 (by rfl) ⟨355518, by rfl⟩ : syracuseStep 3792197 = 711037) (by norm_num)
theorem B10112525 : Blo 1997435 10112525 := bstep (se 3 (by rfl) ⟨1896098, by rfl⟩ : syracuseStep 10112525 = 3792197) B3792197
theorem B6741683 : Blo 1997435 6741683 := bstep (se 1 (by rfl) ⟨5056262, by rfl⟩ : syracuseStep 6741683 = 10112525) B10112525
theorem B4494455 : Blo 1997435 4494455 := bstep (se 1 (by rfl) ⟨3370841, by rfl⟩ : syracuseStep 4494455 = 6741683) B6741683
theorem B2996303 : Blo 1997435 2996303 := bstep (se 1 (by rfl) ⟨2247227, by rfl⟩ : syracuseStep 2996303 = 4494455) B4494455
theorem B1997535 : Blo 1997435 1997535 := bstep (se 1 (by rfl) ⟨1498151, by rfl⟩ : syracuseStep 1997535 = 2996303) B2996303
theorem B2996309 : Blo 1997435 2996309 := bbase (se 8 (by rfl) ⟨17556, by rfl⟩ : syracuseStep 2996309 = 35113) (by norm_num)
theorem B1997539 : Blo 1997435 1997539 := bstep (se 1 (by rfl) ⟨1498154, by rfl⟩ : syracuseStep 1997539 = 2996309) B2996309
theorem B4809557 : Blo 1997435 4809557 := bbase (se 9 (by rfl) ⟨14090, by rfl⟩ : syracuseStep 4809557 = 28181) (by norm_num)
theorem B12825485 : Blo 1997435 12825485 := bstep (se 3 (by rfl) ⟨2404778, by rfl⟩ : syracuseStep 12825485 = 4809557) B4809557
theorem B8550323 : Blo 1997435 8550323 := bstep (se 1 (by rfl) ⟨6412742, by rfl⟩ : syracuseStep 8550323 = 12825485) B12825485
theorem B5700215 : Blo 1997435 5700215 := bstep (se 1 (by rfl) ⟨4275161, by rfl⟩ : syracuseStep 5700215 = 8550323) B8550323
theorem B3800143 : Blo 1997435 3800143 := bstep (se 1 (by rfl) ⟨2850107, by rfl⟩ : syracuseStep 3800143 = 5700215) B5700215
theorem B5066857 : Blo 1997435 5066857 := bstep (se 2 (by rfl) ⟨1900071, by rfl⟩ : syracuseStep 5066857 = 3800143) B3800143
theorem B6755809 : Blo 1997435 6755809 := bstep (se 2 (by rfl) ⟨2533428, by rfl⟩ : syracuseStep 6755809 = 5066857) B5066857
theorem B9007745 : Blo 1997435 9007745 := bstep (se 2 (by rfl) ⟨3377904, by rfl⟩ : syracuseStep 9007745 = 6755809) B6755809
theorem B24020653 : Blo 1997435 24020653 := bstep (se 3 (by rfl) ⟨4503872, by rfl⟩ : syracuseStep 24020653 = 9007745) B9007745
theorem B32027537 : Blo 1997435 32027537 := bstep (se 2 (by rfl) ⟨12010326, by rfl⟩ : syracuseStep 32027537 = 24020653) B24020653
theorem B21351691 : Blo 1997435 21351691 := bstep (se 1 (by rfl) ⟨16013768, by rfl⟩ : syracuseStep 21351691 = 32027537) B32027537
theorem B28468921 : Blo 1997435 28468921 := bstep (se 2 (by rfl) ⟨10675845, by rfl⟩ : syracuseStep 28468921 = 21351691) B21351691
theorem B37958561 : Blo 1997435 37958561 := bstep (se 2 (by rfl) ⟨14234460, by rfl⟩ : syracuseStep 37958561 = 28468921) B28468921
theorem B25305707 : Blo 1997435 25305707 := bstep (se 1 (by rfl) ⟨18979280, by rfl⟩ : syracuseStep 25305707 = 37958561) B37958561
theorem B67481885 : Blo 1997435 67481885 := bstep (se 3 (by rfl) ⟨12652853, by rfl⟩ : syracuseStep 67481885 = 25305707) B25305707
theorem B44987923 : Blo 1997435 44987923 := bstep (se 1 (by rfl) ⟨33740942, by rfl⟩ : syracuseStep 44987923 = 67481885) B67481885
theorem B59983897 : Blo 1997435 59983897 := bstep (se 2 (by rfl) ⟨22493961, by rfl⟩ : syracuseStep 59983897 = 44987923) B44987923
theorem B79978529 : Blo 1997435 79978529 := bstep (se 2 (by rfl) ⟨29991948, by rfl⟩ : syracuseStep 79978529 = 59983897) B59983897
theorem B53319019 : Blo 1997435 53319019 := bstep (se 1 (by rfl) ⟨39989264, by rfl⟩ : syracuseStep 53319019 = 79978529) B79978529
theorem B71092025 : Blo 1997435 71092025 := bstep (se 2 (by rfl) ⟨26659509, by rfl⟩ : syracuseStep 71092025 = 53319019) B53319019
theorem B47394683 : Blo 1997435 47394683 := bstep (se 1 (by rfl) ⟨35546012, by rfl⟩ : syracuseStep 47394683 = 71092025) B71092025
theorem B31596455 : Blo 1997435 31596455 := bstep (se 1 (by rfl) ⟨23697341, by rfl⟩ : syracuseStep 31596455 = 47394683) B47394683
theorem B21064303 : Blo 1997435 21064303 := bstep (se 1 (by rfl) ⟨15798227, by rfl⟩ : syracuseStep 21064303 = 31596455) B31596455
theorem B28085737 : Blo 1997435 28085737 := bstep (se 2 (by rfl) ⟨10532151, by rfl⟩ : syracuseStep 28085737 = 21064303) B21064303
theorem B37447649 : Blo 1997435 37447649 := bstep (se 2 (by rfl) ⟨14042868, by rfl⟩ : syracuseStep 37447649 = 28085737) B28085737
theorem B24965099 : Blo 1997435 24965099 := bstep (se 1 (by rfl) ⟨18723824, by rfl⟩ : syracuseStep 24965099 = 37447649) B37447649
theorem B16643399 : Blo 1997435 16643399 := bstep (se 1 (by rfl) ⟨12482549, by rfl⟩ : syracuseStep 16643399 = 24965099) B24965099
theorem B177529589 : Blo 1997435 177529589 := bstep (se 5 (by rfl) ⟨8321699, by rfl⟩ : syracuseStep 177529589 = 16643399) B16643399
theorem B118353059 : Blo 1997435 118353059 := bstep (se 1 (by rfl) ⟨88764794, by rfl⟩ : syracuseStep 118353059 = 177529589) B177529589
theorem B78902039 : Blo 1997435 78902039 := bstep (se 1 (by rfl) ⟨59176529, by rfl⟩ : syracuseStep 78902039 = 118353059) B118353059
theorem B52601359 : Blo 1997435 52601359 := bstep (se 1 (by rfl) ⟨39451019, by rfl⟩ : syracuseStep 52601359 = 78902039) B78902039
theorem B70135145 : Blo 1997435 70135145 := bstep (se 2 (by rfl) ⟨26300679, by rfl⟩ : syracuseStep 70135145 = 52601359) B52601359
theorem B46756763 : Blo 1997435 46756763 := bstep (se 1 (by rfl) ⟨35067572, by rfl⟩ : syracuseStep 46756763 = 70135145) B70135145
theorem B31171175 : Blo 1997435 31171175 := bstep (se 1 (by rfl) ⟨23378381, by rfl⟩ : syracuseStep 31171175 = 46756763) B46756763
theorem B20780783 : Blo 1997435 20780783 := bstep (se 1 (by rfl) ⟨15585587, by rfl⟩ : syracuseStep 20780783 = 31171175) B31171175
theorem B13853855 : Blo 1997435 13853855 := bstep (se 1 (by rfl) ⟨10390391, by rfl⟩ : syracuseStep 13853855 = 20780783) B20780783
theorem B9235903 : Blo 1997435 9235903 := bstep (se 1 (by rfl) ⟨6926927, by rfl⟩ : syracuseStep 9235903 = 13853855) B13853855
theorem B12314537 : Blo 1997435 12314537 := bstep (se 2 (by rfl) ⟨4617951, by rfl⟩ : syracuseStep 12314537 = 9235903) B9235903
theorem B8209691 : Blo 1997435 8209691 := bstep (se 1 (by rfl) ⟨6157268, by rfl⟩ : syracuseStep 8209691 = 12314537) B12314537
theorem B5473127 : Blo 1997435 5473127 := bstep (se 1 (by rfl) ⟨4104845, by rfl⟩ : syracuseStep 5473127 = 8209691) B8209691
theorem B14595005 : Blo 1997435 14595005 := bstep (se 3 (by rfl) ⟨2736563, by rfl⟩ : syracuseStep 14595005 = 5473127) B5473127
theorem B38920013 : Blo 1997435 38920013 := bstep (se 3 (by rfl) ⟨7297502, by rfl⟩ : syracuseStep 38920013 = 14595005) B14595005
theorem B25946675 : Blo 1997435 25946675 := bstep (se 1 (by rfl) ⟨19460006, by rfl⟩ : syracuseStep 25946675 = 38920013) B38920013
theorem B17297783 : Blo 1997435 17297783 := bstep (se 1 (by rfl) ⟨12973337, by rfl⟩ : syracuseStep 17297783 = 25946675) B25946675
theorem B11531855 : Blo 1997435 11531855 := bstep (se 1 (by rfl) ⟨8648891, by rfl⟩ : syracuseStep 11531855 = 17297783) B17297783
theorem B7687903 : Blo 1997435 7687903 := bstep (se 1 (by rfl) ⟨5765927, by rfl⟩ : syracuseStep 7687903 = 11531855) B11531855
theorem B164008597 : Blo 1997435 164008597 := bstep (se 6 (by rfl) ⟨3843951, by rfl⟩ : syracuseStep 164008597 = 7687903) B7687903
theorem B218678129 : Blo 1997435 218678129 := bstep (se 2 (by rfl) ⟨82004298, by rfl⟩ : syracuseStep 218678129 = 164008597) B164008597
theorem B145785419 : Blo 1997435 145785419 := bstep (se 1 (by rfl) ⟨109339064, by rfl⟩ : syracuseStep 145785419 = 218678129) B218678129
theorem B97190279 : Blo 1997435 97190279 := bstep (se 1 (by rfl) ⟨72892709, by rfl⟩ : syracuseStep 97190279 = 145785419) B145785419
theorem B64793519 : Blo 1997435 64793519 := bstep (se 1 (by rfl) ⟨48595139, by rfl⟩ : syracuseStep 64793519 = 97190279) B97190279
theorem B43195679 : Blo 1997435 43195679 := bstep (se 1 (by rfl) ⟨32396759, by rfl⟩ : syracuseStep 43195679 = 64793519) B64793519
theorem B28797119 : Blo 1997435 28797119 := bstep (se 1 (by rfl) ⟨21597839, by rfl⟩ : syracuseStep 28797119 = 43195679) B43195679
theorem B19198079 : Blo 1997435 19198079 := bstep (se 1 (by rfl) ⟨14398559, by rfl⟩ : syracuseStep 19198079 = 28797119) B28797119
theorem B12798719 : Blo 1997435 12798719 := bstep (se 1 (by rfl) ⟨9599039, by rfl⟩ : syracuseStep 12798719 = 19198079) B19198079
theorem B8532479 : Blo 1997435 8532479 := bstep (se 1 (by rfl) ⟨6399359, by rfl⟩ : syracuseStep 8532479 = 12798719) B12798719
theorem B5688319 : Blo 1997435 5688319 := bstep (se 1 (by rfl) ⟨4266239, by rfl⟩ : syracuseStep 5688319 = 8532479) B8532479
theorem B7584425 : Blo 1997435 7584425 := bstep (se 2 (by rfl) ⟨2844159, by rfl⟩ : syracuseStep 7584425 = 5688319) B5688319
theorem B5056283 : Blo 1997435 5056283 := bstep (se 1 (by rfl) ⟨3792212, by rfl⟩ : syracuseStep 5056283 = 7584425) B7584425
theorem B3370855 : Blo 1997435 3370855 := bstep (se 1 (by rfl) ⟨2528141, by rfl⟩ : syracuseStep 3370855 = 5056283) B5056283
theorem B4494473 : Blo 1997435 4494473 := bstep (se 2 (by rfl) ⟨1685427, by rfl⟩ : syracuseStep 4494473 = 3370855) B3370855
theorem B2996315 : Blo 1997435 2996315 := bstep (se 1 (by rfl) ⟨2247236, by rfl⟩ : syracuseStep 2996315 = 4494473) B4494473
theorem B1997543 : Blo 1997435 1997543 := bstep (se 1 (by rfl) ⟨1498157, by rfl⟩ : syracuseStep 1997543 = 2996315) B2996315
theorem B2247241 : Blo 1997435 2247241 := bbase (se 2 (by rfl) ⟨842715, by rfl⟩ : syracuseStep 2247241 = 1685431) (by norm_num)
theorem B2996321 : Blo 1997435 2996321 := bstep (se 2 (by rfl) ⟨1123620, by rfl⟩ : syracuseStep 2996321 = 2247241) B2247241
theorem B1997547 : Blo 1997435 1997547 := bstep (se 1 (by rfl) ⟨1498160, by rfl⟩ : syracuseStep 1997547 = 2996321) B2996321
theorem B9599077 : Blo 1997435 9599077 := bbase (se 4 (by rfl) ⟨899913, by rfl⟩ : syracuseStep 9599077 = 1799827) (by norm_num)
theorem B12798769 : Blo 1997435 12798769 := bstep (se 2 (by rfl) ⟨4799538, by rfl⟩ : syracuseStep 12798769 = 9599077) B9599077
theorem B17065025 : Blo 1997435 17065025 := bstep (se 2 (by rfl) ⟨6399384, by rfl⟩ : syracuseStep 17065025 = 12798769) B12798769
theorem B11376683 : Blo 1997435 11376683 := bstep (se 1 (by rfl) ⟨8532512, by rfl⟩ : syracuseStep 11376683 = 17065025) B17065025
theorem B7584455 : Blo 1997435 7584455 := bstep (se 1 (by rfl) ⟨5688341, by rfl⟩ : syracuseStep 7584455 = 11376683) B11376683
theorem B5056303 : Blo 1997435 5056303 := bstep (se 1 (by rfl) ⟨3792227, by rfl⟩ : syracuseStep 5056303 = 7584455) B7584455
theorem B6741737 : Blo 1997435 6741737 := bstep (se 2 (by rfl) ⟨2528151, by rfl⟩ : syracuseStep 6741737 = 5056303) B5056303
theorem B4494491 : Blo 1997435 4494491 := bstep (se 1 (by rfl) ⟨3370868, by rfl⟩ : syracuseStep 4494491 = 6741737) B6741737
theorem B2996327 : Blo 1997435 2996327 := bstep (se 1 (by rfl) ⟨2247245, by rfl⟩ : syracuseStep 2996327 = 4494491) B4494491
theorem B1997551 : Blo 1997435 1997551 := bstep (se 1 (by rfl) ⟨1498163, by rfl⟩ : syracuseStep 1997551 = 2996327) B2996327
theorem B2996333 : Blo 1997435 2996333 := bbase (se 3 (by rfl) ⟨561812, by rfl⟩ : syracuseStep 2996333 = 1123625) (by norm_num)
theorem B1997555 : Blo 1997435 1997555 := bstep (se 1 (by rfl) ⟨1498166, by rfl⟩ : syracuseStep 1997555 = 2996333) B2996333
theorem B4494509 : Blo 1997435 4494509 := bbase (se 3 (by rfl) ⟨842720, by rfl⟩ : syracuseStep 4494509 = 1685441) (by norm_num)
theorem B2996339 : Blo 1997435 2996339 := bstep (se 1 (by rfl) ⟨2247254, by rfl⟩ : syracuseStep 2996339 = 4494509) B4494509
theorem B1997559 : Blo 1997435 1997559 := bstep (se 1 (by rfl) ⟨1498169, by rfl⟩ : syracuseStep 1997559 = 2996339) B2996339
theorem B3599677 : Blo 1997435 3599677 := bbase (se 3 (by rfl) ⟨674939, by rfl⟩ : syracuseStep 3599677 = 1349879) (by norm_num)
theorem B4799569 : Blo 1997435 4799569 := bstep (se 2 (by rfl) ⟨1799838, by rfl⟩ : syracuseStep 4799569 = 3599677) B3599677
theorem B6399425 : Blo 1997435 6399425 := bstep (se 2 (by rfl) ⟨2399784, by rfl⟩ : syracuseStep 6399425 = 4799569) B4799569
theorem B4266283 : Blo 1997435 4266283 := bstep (se 1 (by rfl) ⟨3199712, by rfl⟩ : syracuseStep 4266283 = 6399425) B6399425
theorem B5688377 : Blo 1997435 5688377 := bstep (se 2 (by rfl) ⟨2133141, by rfl⟩ : syracuseStep 5688377 = 4266283) B4266283
theorem B3792251 : Blo 1997435 3792251 := bstep (se 1 (by rfl) ⟨2844188, by rfl⟩ : syracuseStep 3792251 = 5688377) B5688377
theorem B2528167 : Blo 1997435 2528167 := bstep (se 1 (by rfl) ⟨1896125, by rfl⟩ : syracuseStep 2528167 = 3792251) B3792251
theorem B3370889 : Blo 1997435 3370889 := bstep (se 2 (by rfl) ⟨1264083, by rfl⟩ : syracuseStep 3370889 = 2528167) B2528167
theorem B2247259 : Blo 1997435 2247259 := bstep (se 1 (by rfl) ⟨1685444, by rfl⟩ : syracuseStep 2247259 = 3370889) B3370889
theorem B2996345 : Blo 1997435 2996345 := bstep (se 2 (by rfl) ⟨1123629, by rfl⟩ : syracuseStep 2996345 = 2247259) B2247259
theorem B1997563 : Blo 1997435 1997563 := bstep (se 1 (by rfl) ⟨1498172, by rfl⟩ : syracuseStep 1997563 = 2996345) B2996345
theorem B7199365 : Blo 1997435 7199365 := bbase (se 4 (by rfl) ⟨674940, by rfl⟩ : syracuseStep 7199365 = 1349881) (by norm_num)
theorem B9599153 : Blo 1997435 9599153 := bstep (se 2 (by rfl) ⟨3599682, by rfl⟩ : syracuseStep 9599153 = 7199365) B7199365
theorem B25597741 : Blo 1997435 25597741 := bstep (se 3 (by rfl) ⟨4799576, by rfl⟩ : syracuseStep 25597741 = 9599153) B9599153
theorem B34130321 : Blo 1997435 34130321 := bstep (se 2 (by rfl) ⟨12798870, by rfl⟩ : syracuseStep 34130321 = 25597741) B25597741
theorem B22753547 : Blo 1997435 22753547 := bstep (se 1 (by rfl) ⟨17065160, by rfl⟩ : syracuseStep 22753547 = 34130321) B34130321
theorem B15169031 : Blo 1997435 15169031 := bstep (se 1 (by rfl) ⟨11376773, by rfl⟩ : syracuseStep 15169031 = 22753547) B22753547
theorem B10112687 : Blo 1997435 10112687 := bstep (se 1 (by rfl) ⟨7584515, by rfl⟩ : syracuseStep 10112687 = 15169031) B15169031
theorem B6741791 : Blo 1997435 6741791 := bstep (se 1 (by rfl) ⟨5056343, by rfl⟩ : syracuseStep 6741791 = 10112687) B10112687
theorem B4494527 : Blo 1997435 4494527 := bstep (se 1 (by rfl) ⟨3370895, by rfl⟩ : syracuseStep 4494527 = 6741791) B6741791
theorem B2996351 : Blo 1997435 2996351 := bstep (se 1 (by rfl) ⟨2247263, by rfl⟩ : syracuseStep 2996351 = 4494527) B4494527
theorem B1997567 : Blo 1997435 1997567 := bstep (se 1 (by rfl) ⟨1498175, by rfl⟩ : syracuseStep 1997567 = 2996351) B2996351
theorem B2996357 : Blo 1997435 2996357 := bbase (se 4 (by rfl) ⟨280908, by rfl⟩ : syracuseStep 2996357 = 561817) (by norm_num)
theorem B1997571 : Blo 1997435 1997571 := bstep (se 1 (by rfl) ⟨1498178, by rfl⟩ : syracuseStep 1997571 = 2996357) B2996357
theorem B3370909 : Blo 1997435 3370909 := bbase (se 3 (by rfl) ⟨632045, by rfl⟩ : syracuseStep 3370909 = 1264091) (by norm_num)
theorem B4494545 : Blo 1997435 4494545 := bstep (se 2 (by rfl) ⟨1685454, by rfl⟩ : syracuseStep 4494545 = 3370909) B3370909
theorem B2996363 : Blo 1997435 2996363 := bstep (se 1 (by rfl) ⟨2247272, by rfl⟩ : syracuseStep 2996363 = 4494545) B4494545
theorem B1997575 : Blo 1997435 1997575 := bstep (se 1 (by rfl) ⟨1498181, by rfl⟩ : syracuseStep 1997575 = 2996363) B2996363
theorem B2247277 : Blo 1997435 2247277 := bbase (se 3 (by rfl) ⟨421364, by rfl⟩ : syracuseStep 2247277 = 842729) (by norm_num)
theorem B2996369 : Blo 1997435 2996369 := bstep (se 2 (by rfl) ⟨1123638, by rfl⟩ : syracuseStep 2996369 = 2247277) B2247277
theorem B1997579 : Blo 1997435 1997579 := bstep (se 1 (by rfl) ⟨1498184, by rfl⟩ : syracuseStep 1997579 = 2996369) B2996369
theorem B6741845 : Blo 1997435 6741845 := bbase (se 9 (by rfl) ⟨19751, by rfl⟩ : syracuseStep 6741845 = 39503) (by norm_num)
theorem B4494563 : Blo 1997435 4494563 := bstep (se 1 (by rfl) ⟨3370922, by rfl⟩ : syracuseStep 4494563 = 6741845) B6741845
theorem B2996375 : Blo 1997435 2996375 := bstep (se 1 (by rfl) ⟨2247281, by rfl⟩ : syracuseStep 2996375 = 4494563) B4494563
theorem B1997583 : Blo 1997435 1997583 := bstep (se 1 (by rfl) ⟨1498187, by rfl⟩ : syracuseStep 1997583 = 2996375) B2996375
theorem B2996381 : Blo 1997435 2996381 := bbase (se 3 (by rfl) ⟨561821, by rfl⟩ : syracuseStep 2996381 = 1123643) (by norm_num)
theorem B1997587 : Blo 1997435 1997587 := bstep (se 1 (by rfl) ⟨1498190, by rfl⟩ : syracuseStep 1997587 = 2996381) B2996381
theorem B4494581 : Blo 1997435 4494581 := bbase (se 5 (by rfl) ⟨210683, by rfl⟩ : syracuseStep 4494581 = 421367) (by norm_num)
theorem B2996387 : Blo 1997435 2996387 := bstep (se 1 (by rfl) ⟨2247290, by rfl⟩ : syracuseStep 2996387 = 4494581) B4494581
theorem B1997591 : Blo 1997435 1997591 := bstep (se 1 (by rfl) ⟨1498193, by rfl⟩ : syracuseStep 1997591 = 2996387) B2996387
theorem B6927109 : Blo 1997435 6927109 := bbase (se 4 (by rfl) ⟨649416, by rfl⟩ : syracuseStep 6927109 = 1298833) (by norm_num)
theorem B36944581 : Blo 1997435 36944581 := bstep (se 4 (by rfl) ⟨3463554, by rfl⟩ : syracuseStep 36944581 = 6927109) B6927109
theorem B49259441 : Blo 1997435 49259441 := bstep (se 2 (by rfl) ⟨18472290, by rfl⟩ : syracuseStep 49259441 = 36944581) B36944581
theorem B32839627 : Blo 1997435 32839627 := bstep (se 1 (by rfl) ⟨24629720, by rfl⟩ : syracuseStep 32839627 = 49259441) B49259441
theorem B43786169 : Blo 1997435 43786169 := bstep (se 2 (by rfl) ⟨16419813, by rfl⟩ : syracuseStep 43786169 = 32839627) B32839627
theorem B29190779 : Blo 1997435 29190779 := bstep (se 1 (by rfl) ⟨21893084, by rfl⟩ : syracuseStep 29190779 = 43786169) B43786169
theorem B19460519 : Blo 1997435 19460519 := bstep (se 1 (by rfl) ⟨14595389, by rfl⟩ : syracuseStep 19460519 = 29190779) B29190779
theorem B12973679 : Blo 1997435 12973679 := bstep (se 1 (by rfl) ⟨9730259, by rfl⟩ : syracuseStep 12973679 = 19460519) B19460519
theorem B8649119 : Blo 1997435 8649119 := bstep (se 1 (by rfl) ⟨6486839, by rfl⟩ : syracuseStep 8649119 = 12973679) B12973679
theorem B5766079 : Blo 1997435 5766079 := bstep (se 1 (by rfl) ⟨4324559, by rfl⟩ : syracuseStep 5766079 = 8649119) B8649119
theorem B7688105 : Blo 1997435 7688105 := bstep (se 2 (by rfl) ⟨2883039, by rfl⟩ : syracuseStep 7688105 = 5766079) B5766079
theorem B5125403 : Blo 1997435 5125403 := bstep (se 1 (by rfl) ⟨3844052, by rfl⟩ : syracuseStep 5125403 = 7688105) B7688105
theorem B13667741 : Blo 1997435 13667741 := bstep (se 3 (by rfl) ⟨2562701, by rfl⟩ : syracuseStep 13667741 = 5125403) B5125403
theorem B9111827 : Blo 1997435 9111827 := bstep (se 1 (by rfl) ⟨6833870, by rfl⟩ : syracuseStep 9111827 = 13667741) B13667741
theorem B6074551 : Blo 1997435 6074551 := bstep (se 1 (by rfl) ⟨4555913, by rfl⟩ : syracuseStep 6074551 = 9111827) B9111827
theorem B8099401 : Blo 1997435 8099401 := bstep (se 2 (by rfl) ⟨3037275, by rfl⟩ : syracuseStep 8099401 = 6074551) B6074551
theorem B10799201 : Blo 1997435 10799201 := bstep (se 2 (by rfl) ⟨4049700, by rfl⟩ : syracuseStep 10799201 = 8099401) B8099401
theorem B28797869 : Blo 1997435 28797869 := bstep (se 3 (by rfl) ⟨5399600, by rfl⟩ : syracuseStep 28797869 = 10799201) B10799201
theorem B19198579 : Blo 1997435 19198579 := bstep (se 1 (by rfl) ⟨14398934, by rfl⟩ : syracuseStep 19198579 = 28797869) B28797869
theorem B25598105 : Blo 1997435 25598105 := bstep (se 2 (by rfl) ⟨9599289, by rfl⟩ : syracuseStep 25598105 = 19198579) B19198579
theorem B17065403 : Blo 1997435 17065403 := bstep (se 1 (by rfl) ⟨12799052, by rfl⟩ : syracuseStep 17065403 = 25598105) B25598105
theorem B11376935 : Blo 1997435 11376935 := bstep (se 1 (by rfl) ⟨8532701, by rfl⟩ : syracuseStep 11376935 = 17065403) B17065403
theorem B7584623 : Blo 1997435 7584623 := bstep (se 1 (by rfl) ⟨5688467, by rfl⟩ : syracuseStep 7584623 = 11376935) B11376935
theorem B5056415 : Blo 1997435 5056415 := bstep (se 1 (by rfl) ⟨3792311, by rfl⟩ : syracuseStep 5056415 = 7584623) B7584623
theorem B3370943 : Blo 1997435 3370943 := bstep (se 1 (by rfl) ⟨2528207, by rfl⟩ : syracuseStep 3370943 = 5056415) B5056415
theorem B2247295 : Blo 1997435 2247295 := bstep (se 1 (by rfl) ⟨1685471, by rfl⟩ : syracuseStep 2247295 = 3370943) B3370943
theorem B2996393 : Blo 1997435 2996393 := bstep (se 2 (by rfl) ⟨1123647, by rfl⟩ : syracuseStep 2996393 = 2247295) B2247295
theorem B1997595 : Blo 1997435 1997595 := bstep (se 1 (by rfl) ⟨1498196, by rfl⟩ : syracuseStep 1997595 = 2996393) B2996393
theorem B3599741 : Blo 1997435 3599741 := bbase (se 3 (by rfl) ⟨674951, by rfl⟩ : syracuseStep 3599741 = 1349903) (by norm_num)
theorem B9599309 : Blo 1997435 9599309 := bstep (se 3 (by rfl) ⟨1799870, by rfl⟩ : syracuseStep 9599309 = 3599741) B3599741
theorem B6399539 : Blo 1997435 6399539 := bstep (se 1 (by rfl) ⟨4799654, by rfl⟩ : syracuseStep 6399539 = 9599309) B9599309
theorem B4266359 : Blo 1997435 4266359 := bstep (se 1 (by rfl) ⟨3199769, by rfl⟩ : syracuseStep 4266359 = 6399539) B6399539
theorem B2844239 : Blo 1997435 2844239 := bstep (se 1 (by rfl) ⟨2133179, by rfl⟩ : syracuseStep 2844239 = 4266359) B4266359
theorem B7584637 : Blo 1997435 7584637 := bstep (se 3 (by rfl) ⟨1422119, by rfl⟩ : syracuseStep 7584637 = 2844239) B2844239
theorem B10112849 : Blo 1997435 10112849 := bstep (se 2 (by rfl) ⟨3792318, by rfl⟩ : syracuseStep 10112849 = 7584637) B7584637
theorem B6741899 : Blo 1997435 6741899 := bstep (se 1 (by rfl) ⟨5056424, by rfl⟩ : syracuseStep 6741899 = 10112849) B10112849
theorem B4494599 : Blo 1997435 4494599 := bstep (se 1 (by rfl) ⟨3370949, by rfl⟩ : syracuseStep 4494599 = 6741899) B6741899
theorem B2996399 : Blo 1997435 2996399 := bstep (se 1 (by rfl) ⟨2247299, by rfl⟩ : syracuseStep 2996399 = 4494599) B4494599
theorem B1997599 : Blo 1997435 1997599 := bstep (se 1 (by rfl) ⟨1498199, by rfl⟩ : syracuseStep 1997599 = 2996399) B2996399
theorem B2996405 : Blo 1997435 2996405 := bbase (se 5 (by rfl) ⟨140456, by rfl⟩ : syracuseStep 2996405 = 280913) (by norm_num)
theorem B1997603 : Blo 1997435 1997603 := bstep (se 1 (by rfl) ⟨1498202, by rfl⟩ : syracuseStep 1997603 = 2996405) B2996405
theorem B5056445 : Blo 1997435 5056445 := bbase (se 3 (by rfl) ⟨948083, by rfl⟩ : syracuseStep 5056445 = 1896167) (by norm_num)
theorem B3370963 : Blo 1997435 3370963 := bstep (se 1 (by rfl) ⟨2528222, by rfl⟩ : syracuseStep 3370963 = 5056445) B5056445
theorem B4494617 : Blo 1997435 4494617 := bstep (se 2 (by rfl) ⟨1685481, by rfl⟩ : syracuseStep 4494617 = 3370963) B3370963
theorem B2996411 : Blo 1997435 2996411 := bstep (se 1 (by rfl) ⟨2247308, by rfl⟩ : syracuseStep 2996411 = 4494617) B4494617
theorem B1997607 : Blo 1997435 1997607 := bstep (se 1 (by rfl) ⟨1498205, by rfl⟩ : syracuseStep 1997607 = 2996411) B2996411
theorem B2247313 : Blo 1997435 2247313 := bbase (se 2 (by rfl) ⟨842742, by rfl⟩ : syracuseStep 2247313 = 1685485) (by norm_num)
theorem B2996417 : Blo 1997435 2996417 := bstep (se 2 (by rfl) ⟨1123656, by rfl⟩ : syracuseStep 2996417 = 2247313) B2247313
theorem B1997611 : Blo 1997435 1997611 := bstep (se 1 (by rfl) ⟨1498208, by rfl⟩ : syracuseStep 1997611 = 2996417) B2996417
theorem B3792349 : Blo 1997435 3792349 := bbase (se 3 (by rfl) ⟨711065, by rfl⟩ : syracuseStep 3792349 = 1422131) (by norm_num)
theorem B5056465 : Blo 1997435 5056465 := bstep (se 2 (by rfl) ⟨1896174, by rfl⟩ : syracuseStep 5056465 = 3792349) B3792349
theorem B6741953 : Blo 1997435 6741953 := bstep (se 2 (by rfl) ⟨2528232, by rfl⟩ : syracuseStep 6741953 = 5056465) B5056465
theorem B4494635 : Blo 1997435 4494635 := bstep (se 1 (by rfl) ⟨3370976, by rfl⟩ : syracuseStep 4494635 = 6741953) B6741953
theorem B2996423 : Blo 1997435 2996423 := bstep (se 1 (by rfl) ⟨2247317, by rfl⟩ : syracuseStep 2996423 = 4494635) B4494635
theorem B1997615 : Blo 1997435 1997615 := bstep (se 1 (by rfl) ⟨1498211, by rfl⟩ : syracuseStep 1997615 = 2996423) B2996423
theorem B2996429 : Blo 1997435 2996429 := bbase (se 3 (by rfl) ⟨561830, by rfl⟩ : syracuseStep 2996429 = 1123661) (by norm_num)
theorem B1997619 : Blo 1997435 1997619 := bstep (se 1 (by rfl) ⟨1498214, by rfl⟩ : syracuseStep 1997619 = 2996429) B2996429
theorem B4494653 : Blo 1997435 4494653 := bbase (se 3 (by rfl) ⟨842747, by rfl⟩ : syracuseStep 4494653 = 1685495) (by norm_num)
theorem B2996435 : Blo 1997435 2996435 := bstep (se 1 (by rfl) ⟨2247326, by rfl⟩ : syracuseStep 2996435 = 4494653) B4494653
theorem B1997623 : Blo 1997435 1997623 := bstep (se 1 (by rfl) ⟨1498217, by rfl⟩ : syracuseStep 1997623 = 2996435) B2996435
theorem B3370997 : Blo 1997435 3370997 := bbase (se 5 (by rfl) ⟨158015, by rfl⟩ : syracuseStep 3370997 = 316031) (by norm_num)
theorem B2247331 : Blo 1997435 2247331 := bstep (se 1 (by rfl) ⟨1685498, by rfl⟩ : syracuseStep 2247331 = 3370997) B3370997
theorem B2996441 : Blo 1997435 2996441 := bstep (se 2 (by rfl) ⟨1123665, by rfl⟩ : syracuseStep 2996441 = 2247331) B2247331
theorem B1997627 : Blo 1997435 1997627 := bstep (se 1 (by rfl) ⟨1498220, by rfl⟩ : syracuseStep 1997627 = 2996441) B2996441
theorem B4555997 : Blo 1997435 4555997 := bbase (se 3 (by rfl) ⟨854249, by rfl⟩ : syracuseStep 4555997 = 1708499) (by norm_num)
theorem B3037331 : Blo 1997435 3037331 := bstep (se 1 (by rfl) ⟨2277998, by rfl⟩ : syracuseStep 3037331 = 4555997) B4555997
theorem B2024887 : Blo 1997435 2024887 := bstep (se 1 (by rfl) ⟨1518665, by rfl⟩ : syracuseStep 2024887 = 3037331) B3037331
theorem B2699849 : Blo 1997435 2699849 := bstep (se 2 (by rfl) ⟨1012443, by rfl⟩ : syracuseStep 2699849 = 2024887) B2024887
theorem B7199597 : Blo 1997435 7199597 := bstep (se 3 (by rfl) ⟨1349924, by rfl⟩ : syracuseStep 7199597 = 2699849) B2699849
theorem B4799731 : Blo 1997435 4799731 := bstep (se 1 (by rfl) ⟨3599798, by rfl⟩ : syracuseStep 4799731 = 7199597) B7199597
theorem B6399641 : Blo 1997435 6399641 := bstep (se 2 (by rfl) ⟨2399865, by rfl⟩ : syracuseStep 6399641 = 4799731) B4799731
theorem B4266427 : Blo 1997435 4266427 := bstep (se 1 (by rfl) ⟨3199820, by rfl⟩ : syracuseStep 4266427 = 6399641) B6399641
theorem B5688569 : Blo 1997435 5688569 := bstep (se 2 (by rfl) ⟨2133213, by rfl⟩ : syracuseStep 5688569 = 4266427) B4266427
theorem B15169517 : Blo 1997435 15169517 := bstep (se 3 (by rfl) ⟨2844284, by rfl⟩ : syracuseStep 15169517 = 5688569) B5688569
theorem B10113011 : Blo 1997435 10113011 := bstep (se 1 (by rfl) ⟨7584758, by rfl⟩ : syracuseStep 10113011 = 15169517) B15169517
theorem B6742007 : Blo 1997435 6742007 := bstep (se 1 (by rfl) ⟨5056505, by rfl⟩ : syracuseStep 6742007 = 10113011) B10113011
theorem B4494671 : Blo 1997435 4494671 := bstep (se 1 (by rfl) ⟨3371003, by rfl⟩ : syracuseStep 4494671 = 6742007) B6742007
theorem B2996447 : Blo 1997435 2996447 := bstep (se 1 (by rfl) ⟨2247335, by rfl⟩ : syracuseStep 2996447 = 4494671) B4494671
theorem B1997631 : Blo 1997435 1997631 := bstep (se 1 (by rfl) ⟨1498223, by rfl⟩ : syracuseStep 1997631 = 2996447) B2996447
theorem B2996453 : Blo 1997435 2996453 := bbase (se 4 (by rfl) ⟨280917, by rfl⟩ : syracuseStep 2996453 = 561835) (by norm_num)
theorem B1997635 : Blo 1997435 1997635 := bstep (se 1 (by rfl) ⟨1498226, by rfl⟩ : syracuseStep 1997635 = 2996453) B2996453
theorem B4266445 : Blo 1997435 4266445 := bbase (se 3 (by rfl) ⟨799958, by rfl⟩ : syracuseStep 4266445 = 1599917) (by norm_num)
theorem B5688593 : Blo 1997435 5688593 := bstep (se 2 (by rfl) ⟨2133222, by rfl⟩ : syracuseStep 5688593 = 4266445) B4266445
theorem B3792395 : Blo 1997435 3792395 := bstep (se 1 (by rfl) ⟨2844296, by rfl⟩ : syracuseStep 3792395 = 5688593) B5688593
theorem B2528263 : Blo 1997435 2528263 := bstep (se 1 (by rfl) ⟨1896197, by rfl⟩ : syracuseStep 2528263 = 3792395) B3792395
theorem B3371017 : Blo 1997435 3371017 := bstep (se 2 (by rfl) ⟨1264131, by rfl⟩ : syracuseStep 3371017 = 2528263) B2528263
theorem B4494689 : Blo 1997435 4494689 := bstep (se 2 (by rfl) ⟨1685508, by rfl⟩ : syracuseStep 4494689 = 3371017) B3371017
theorem B2996459 : Blo 1997435 2996459 := bstep (se 1 (by rfl) ⟨2247344, by rfl⟩ : syracuseStep 2996459 = 4494689) B4494689
theorem B1997639 : Blo 1997435 1997639 := bstep (se 1 (by rfl) ⟨1498229, by rfl⟩ : syracuseStep 1997639 = 2996459) B2996459
theorem B2247349 : Blo 1997435 2247349 := bbase (se 5 (by rfl) ⟨105344, by rfl⟩ : syracuseStep 2247349 = 210689) (by norm_num)
theorem B2996465 : Blo 1997435 2996465 := bstep (se 2 (by rfl) ⟨1123674, by rfl⟩ : syracuseStep 2996465 = 2247349) B2247349
theorem B1997643 : Blo 1997435 1997643 := bstep (se 1 (by rfl) ⟨1498232, by rfl⟩ : syracuseStep 1997643 = 2996465) B2996465
theorem B2528273 : Blo 1997435 2528273 := bbase (se 2 (by rfl) ⟨948102, by rfl⟩ : syracuseStep 2528273 = 1896205) (by norm_num)
theorem B6742061 : Blo 1997435 6742061 := bstep (se 3 (by rfl) ⟨1264136, by rfl⟩ : syracuseStep 6742061 = 2528273) B2528273
theorem B4494707 : Blo 1997435 4494707 := bstep (se 1 (by rfl) ⟨3371030, by rfl⟩ : syracuseStep 4494707 = 6742061) B6742061
theorem B2996471 : Blo 1997435 2996471 := bstep (se 1 (by rfl) ⟨2247353, by rfl⟩ : syracuseStep 2996471 = 4494707) B4494707
theorem B1997647 : Blo 1997435 1997647 := bstep (se 1 (by rfl) ⟨1498235, by rfl⟩ : syracuseStep 1997647 = 2996471) B2996471
theorem B2996477 : Blo 1997435 2996477 := bbase (se 3 (by rfl) ⟨561839, by rfl⟩ : syracuseStep 2996477 = 1123679) (by norm_num)
theorem B1997651 : Blo 1997435 1997651 := bstep (se 1 (by rfl) ⟨1498238, by rfl⟩ : syracuseStep 1997651 = 2996477) B2996477
theorem B4494725 : Blo 1997435 4494725 := bbase (se 4 (by rfl) ⟨421380, by rfl⟩ : syracuseStep 4494725 = 842761) (by norm_num)
theorem B2996483 : Blo 1997435 2996483 := bstep (se 1 (by rfl) ⟨2247362, by rfl⟩ : syracuseStep 2996483 = 4494725) B4494725
theorem B1997655 : Blo 1997435 1997655 := bstep (se 1 (by rfl) ⟨1498241, by rfl⟩ : syracuseStep 1997655 = 2996483) B2996483
theorem B2844325 : Blo 1997435 2844325 := bbase (se 4 (by rfl) ⟨266655, by rfl⟩ : syracuseStep 2844325 = 533311) (by norm_num)
theorem B3792433 : Blo 1997435 3792433 := bstep (se 2 (by rfl) ⟨1422162, by rfl⟩ : syracuseStep 3792433 = 2844325) B2844325
theorem B5056577 : Blo 1997435 5056577 := bstep (se 2 (by rfl) ⟨1896216, by rfl⟩ : syracuseStep 5056577 = 3792433) B3792433
theorem B3371051 : Blo 1997435 3371051 := bstep (se 1 (by rfl) ⟨2528288, by rfl⟩ : syracuseStep 3371051 = 5056577) B5056577
theorem B2247367 : Blo 1997435 2247367 := bstep (se 1 (by rfl) ⟨1685525, by rfl⟩ : syracuseStep 2247367 = 3371051) B3371051
theorem B2996489 : Blo 1997435 2996489 := bstep (se 2 (by rfl) ⟨1123683, by rfl⟩ : syracuseStep 2996489 = 2247367) B2247367
theorem B1997659 : Blo 1997435 1997659 := bstep (se 1 (by rfl) ⟨1498244, by rfl⟩ : syracuseStep 1997659 = 2996489) B2996489
theorem B10113173 : Blo 1997435 10113173 := bbase (se 6 (by rfl) ⟨237027, by rfl⟩ : syracuseStep 10113173 = 474055) (by norm_num)
theorem B6742115 : Blo 1997435 6742115 := bstep (se 1 (by rfl) ⟨5056586, by rfl⟩ : syracuseStep 6742115 = 10113173) B10113173
theorem B4494743 : Blo 1997435 4494743 := bstep (se 1 (by rfl) ⟨3371057, by rfl⟩ : syracuseStep 4494743 = 6742115) B6742115
theorem B2996495 : Blo 1997435 2996495 := bstep (se 1 (by rfl) ⟨2247371, by rfl⟩ : syracuseStep 2996495 = 4494743) B4494743
theorem B1997663 : Blo 1997435 1997663 := bstep (se 1 (by rfl) ⟨1498247, by rfl⟩ : syracuseStep 1997663 = 2996495) B2996495
theorem B2996501 : Blo 1997435 2996501 := bbase (se 6 (by rfl) ⟨70230, by rfl⟩ : syracuseStep 2996501 = 140461) (by norm_num)
theorem B1997667 : Blo 1997435 1997667 := bstep (se 1 (by rfl) ⟨1498250, by rfl⟩ : syracuseStep 1997667 = 2996501) B2996501
theorem B2597765 : Blo 1997435 2597765 := bbase (se 4 (by rfl) ⟨243540, by rfl⟩ : syracuseStep 2597765 = 487081) (by norm_num)
theorem B6927373 : Blo 1997435 6927373 := bstep (se 3 (by rfl) ⟨1298882, by rfl⟩ : syracuseStep 6927373 = 2597765) B2597765
theorem B9236497 : Blo 1997435 9236497 := bstep (se 2 (by rfl) ⟨3463686, by rfl⟩ : syracuseStep 9236497 = 6927373) B6927373
theorem B12315329 : Blo 1997435 12315329 := bstep (se 2 (by rfl) ⟨4618248, by rfl⟩ : syracuseStep 12315329 = 9236497) B9236497
theorem B8210219 : Blo 1997435 8210219 := bstep (se 1 (by rfl) ⟨6157664, by rfl⟩ : syracuseStep 8210219 = 12315329) B12315329
theorem B21893917 : Blo 1997435 21893917 := bstep (se 3 (by rfl) ⟨4105109, by rfl⟩ : syracuseStep 21893917 = 8210219) B8210219
theorem B29191889 : Blo 1997435 29191889 := bstep (se 2 (by rfl) ⟨10946958, by rfl⟩ : syracuseStep 29191889 = 21893917) B21893917
theorem B19461259 : Blo 1997435 19461259 := bstep (se 1 (by rfl) ⟨14595944, by rfl⟩ : syracuseStep 19461259 = 29191889) B29191889
theorem B25948345 : Blo 1997435 25948345 := bstep (se 2 (by rfl) ⟨9730629, by rfl⟩ : syracuseStep 25948345 = 19461259) B19461259
theorem B34597793 : Blo 1997435 34597793 := bstep (se 2 (by rfl) ⟨12974172, by rfl⟩ : syracuseStep 34597793 = 25948345) B25948345
theorem B23065195 : Blo 1997435 23065195 := bstep (se 1 (by rfl) ⟨17298896, by rfl⟩ : syracuseStep 23065195 = 34597793) B34597793
theorem B30753593 : Blo 1997435 30753593 := bstep (se 2 (by rfl) ⟨11532597, by rfl⟩ : syracuseStep 30753593 = 23065195) B23065195
theorem B20502395 : Blo 1997435 20502395 := bstep (se 1 (by rfl) ⟨15376796, by rfl⟩ : syracuseStep 20502395 = 30753593) B30753593
theorem B13668263 : Blo 1997435 13668263 := bstep (se 1 (by rfl) ⟨10251197, by rfl⟩ : syracuseStep 13668263 = 20502395) B20502395
theorem B9112175 : Blo 1997435 9112175 := bstep (se 1 (by rfl) ⟨6834131, by rfl⟩ : syracuseStep 9112175 = 13668263) B13668263
theorem B6074783 : Blo 1997435 6074783 := bstep (se 1 (by rfl) ⟨4556087, by rfl⟩ : syracuseStep 6074783 = 9112175) B9112175
theorem B4049855 : Blo 1997435 4049855 := bstep (se 1 (by rfl) ⟨3037391, by rfl⟩ : syracuseStep 4049855 = 6074783) B6074783
theorem B2699903 : Blo 1997435 2699903 := bstep (se 1 (by rfl) ⟨2024927, by rfl⟩ : syracuseStep 2699903 = 4049855) B4049855
theorem B7199741 : Blo 1997435 7199741 := bstep (se 3 (by rfl) ⟨1349951, by rfl⟩ : syracuseStep 7199741 = 2699903) B2699903
theorem B4799827 : Blo 1997435 4799827 := bstep (se 1 (by rfl) ⟨3599870, by rfl⟩ : syracuseStep 4799827 = 7199741) B7199741
theorem B25599077 : Blo 1997435 25599077 := bstep (se 4 (by rfl) ⟨2399913, by rfl⟩ : syracuseStep 25599077 = 4799827) B4799827
theorem B17066051 : Blo 1997435 17066051 := bstep (se 1 (by rfl) ⟨12799538, by rfl⟩ : syracuseStep 17066051 = 25599077) B25599077
theorem B11377367 : Blo 1997435 11377367 := bstep (se 1 (by rfl) ⟨8533025, by rfl⟩ : syracuseStep 11377367 = 17066051) B17066051
theorem B7584911 : Blo 1997435 7584911 := bstep (se 1 (by rfl) ⟨5688683, by rfl⟩ : syracuseStep 7584911 = 11377367) B11377367
theorem B5056607 : Blo 1997435 5056607 := bstep (se 1 (by rfl) ⟨3792455, by rfl⟩ : syracuseStep 5056607 = 7584911) B7584911
theorem B3371071 : Blo 1997435 3371071 := bstep (se 1 (by rfl) ⟨2528303, by rfl⟩ : syracuseStep 3371071 = 5056607) B5056607
theorem B4494761 : Blo 1997435 4494761 := bstep (se 2 (by rfl) ⟨1685535, by rfl⟩ : syracuseStep 4494761 = 3371071) B3371071
theorem B2996507 : Blo 1997435 2996507 := bstep (se 1 (by rfl) ⟨2247380, by rfl⟩ : syracuseStep 2996507 = 4494761) B4494761
theorem B1997671 : Blo 1997435 1997671 := bstep (se 1 (by rfl) ⟨1498253, by rfl⟩ : syracuseStep 1997671 = 2996507) B2996507
theorem B2247385 : Blo 1997435 2247385 := bbase (se 2 (by rfl) ⟨842769, by rfl⟩ : syracuseStep 2247385 = 1685539) (by norm_num)
theorem B2996513 : Blo 1997435 2996513 := bstep (se 2 (by rfl) ⟨1123692, by rfl⟩ : syracuseStep 2996513 = 2247385) B2247385
theorem B1997675 : Blo 1997435 1997675 := bstep (se 1 (by rfl) ⟨1498256, by rfl⟩ : syracuseStep 1997675 = 2996513) B2996513
theorem B2133265 : Blo 1997435 2133265 := bbase (se 2 (by rfl) ⟨799974, by rfl⟩ : syracuseStep 2133265 = 1599949) (by norm_num)
theorem B2844353 : Blo 1997435 2844353 := bstep (se 2 (by rfl) ⟨1066632, by rfl⟩ : syracuseStep 2844353 = 2133265) B2133265
theorem B7584941 : Blo 1997435 7584941 := bstep (se 3 (by rfl) ⟨1422176, by rfl⟩ : syracuseStep 7584941 = 2844353) B2844353
theorem B5056627 : Blo 1997435 5056627 := bstep (se 1 (by rfl) ⟨3792470, by rfl⟩ : syracuseStep 5056627 = 7584941) B7584941
theorem B6742169 : Blo 1997435 6742169 := bstep (se 2 (by rfl) ⟨2528313, by rfl⟩ : syracuseStep 6742169 = 5056627) B5056627
theorem B4494779 : Blo 1997435 4494779 := bstep (se 1 (by rfl) ⟨3371084, by rfl⟩ : syracuseStep 4494779 = 6742169) B6742169
theorem B2996519 : Blo 1997435 2996519 := bstep (se 1 (by rfl) ⟨2247389, by rfl⟩ : syracuseStep 2996519 = 4494779) B4494779
theorem B1997679 : Blo 1997435 1997679 := bstep (se 1 (by rfl) ⟨1498259, by rfl⟩ : syracuseStep 1997679 = 2996519) B2996519
theorem B2996525 : Blo 1997435 2996525 := bbase (se 3 (by rfl) ⟨561848, by rfl⟩ : syracuseStep 2996525 = 1123697) (by norm_num)
theorem B1997683 : Blo 1997435 1997683 := bstep (se 1 (by rfl) ⟨1498262, by rfl⟩ : syracuseStep 1997683 = 2996525) B2996525
theorem B4494797 : Blo 1997435 4494797 := bbase (se 3 (by rfl) ⟨842774, by rfl⟩ : syracuseStep 4494797 = 1685549) (by norm_num)
theorem B2996531 : Blo 1997435 2996531 := bstep (se 1 (by rfl) ⟨2247398, by rfl⟩ : syracuseStep 2996531 = 4494797) B4494797
theorem B1997687 : Blo 1997435 1997687 := bstep (se 1 (by rfl) ⟨1498265, by rfl⟩ : syracuseStep 1997687 = 2996531) B2996531
theorem B2528329 : Blo 1997435 2528329 := bbase (se 2 (by rfl) ⟨948123, by rfl⟩ : syracuseStep 2528329 = 1896247) (by norm_num)
theorem B3371105 : Blo 1997435 3371105 := bstep (se 2 (by rfl) ⟨1264164, by rfl⟩ : syracuseStep 3371105 = 2528329) B2528329
theorem B2247403 : Blo 1997435 2247403 := bstep (se 1 (by rfl) ⟨1685552, by rfl⟩ : syracuseStep 2247403 = 3371105) B3371105
theorem B2996537 : Blo 1997435 2996537 := bstep (se 2 (by rfl) ⟨1123701, by rfl⟩ : syracuseStep 2996537 = 2247403) B2247403
theorem B1997691 : Blo 1997435 1997691 := bstep (se 1 (by rfl) ⟨1498268, by rfl⟩ : syracuseStep 1997691 = 2996537) B2996537
theorem B3078869 : Blo 1997435 3078869 := bbase (se 7 (by rfl) ⟨36080, by rfl⟩ : syracuseStep 3078869 = 72161) (by norm_num)
theorem B8210317 : Blo 1997435 8210317 := bstep (se 3 (by rfl) ⟨1539434, by rfl⟩ : syracuseStep 8210317 = 3078869) B3078869
theorem B10947089 : Blo 1997435 10947089 := bstep (se 2 (by rfl) ⟨4105158, by rfl⟩ : syracuseStep 10947089 = 8210317) B8210317
theorem B29192237 : Blo 1997435 29192237 := bstep (se 3 (by rfl) ⟨5473544, by rfl⟩ : syracuseStep 29192237 = 10947089) B10947089
theorem B19461491 : Blo 1997435 19461491 := bstep (se 1 (by rfl) ⟨14596118, by rfl⟩ : syracuseStep 19461491 = 29192237) B29192237
theorem B12974327 : Blo 1997435 12974327 := bstep (se 1 (by rfl) ⟨9730745, by rfl⟩ : syracuseStep 12974327 = 19461491) B19461491
theorem B8649551 : Blo 1997435 8649551 := bstep (se 1 (by rfl) ⟨6487163, by rfl⟩ : syracuseStep 8649551 = 12974327) B12974327
theorem B23065469 : Blo 1997435 23065469 := bstep (se 3 (by rfl) ⟨4324775, by rfl⟩ : syracuseStep 23065469 = 8649551) B8649551
theorem B15376979 : Blo 1997435 15376979 := bstep (se 1 (by rfl) ⟨11532734, by rfl⟩ : syracuseStep 15376979 = 23065469) B23065469
theorem B10251319 : Blo 1997435 10251319 := bstep (se 1 (by rfl) ⟨7688489, by rfl⟩ : syracuseStep 10251319 = 15376979) B15376979
theorem B13668425 : Blo 1997435 13668425 := bstep (se 2 (by rfl) ⟨5125659, by rfl⟩ : syracuseStep 13668425 = 10251319) B10251319
theorem B9112283 : Blo 1997435 9112283 := bstep (se 1 (by rfl) ⟨6834212, by rfl⟩ : syracuseStep 9112283 = 13668425) B13668425
theorem B6074855 : Blo 1997435 6074855 := bstep (se 1 (by rfl) ⟨4556141, by rfl⟩ : syracuseStep 6074855 = 9112283) B9112283
theorem B4049903 : Blo 1997435 4049903 := bstep (se 1 (by rfl) ⟨3037427, by rfl⟩ : syracuseStep 4049903 = 6074855) B6074855
theorem B2699935 : Blo 1997435 2699935 := bstep (se 1 (by rfl) ⟨2024951, by rfl⟩ : syracuseStep 2699935 = 4049903) B4049903
theorem B14399653 : Blo 1997435 14399653 := bstep (se 4 (by rfl) ⟨1349967, by rfl⟩ : syracuseStep 14399653 = 2699935) B2699935
theorem B19199537 : Blo 1997435 19199537 := bstep (se 2 (by rfl) ⟨7199826, by rfl⟩ : syracuseStep 19199537 = 14399653) B14399653
theorem B12799691 : Blo 1997435 12799691 := bstep (se 1 (by rfl) ⟨9599768, by rfl⟩ : syracuseStep 12799691 = 19199537) B19199537
theorem B8533127 : Blo 1997435 8533127 := bstep (se 1 (by rfl) ⟨6399845, by rfl⟩ : syracuseStep 8533127 = 12799691) B12799691
theorem B22755005 : Blo 1997435 22755005 := bstep (se 3 (by rfl) ⟨4266563, by rfl⟩ : syracuseStep 22755005 = 8533127) B8533127
theorem B15170003 : Blo 1997435 15170003 := bstep (se 1 (by rfl) ⟨11377502, by rfl⟩ : syracuseStep 15170003 = 22755005) B22755005
theorem B10113335 : Blo 1997435 10113335 := bstep (se 1 (by rfl) ⟨7585001, by rfl⟩ : syracuseStep 10113335 = 15170003) B15170003
theorem B6742223 : Blo 1997435 6742223 := bstep (se 1 (by rfl) ⟨5056667, by rfl⟩ : syracuseStep 6742223 = 10113335) B10113335
theorem B4494815 : Blo 1997435 4494815 := bstep (se 1 (by rfl) ⟨3371111, by rfl⟩ : syracuseStep 4494815 = 6742223) B6742223
theorem B2996543 : Blo 1997435 2996543 := bstep (se 1 (by rfl) ⟨2247407, by rfl⟩ : syracuseStep 2996543 = 4494815) B4494815
theorem B1997695 : Blo 1997435 1997695 := bstep (se 1 (by rfl) ⟨1498271, by rfl⟩ : syracuseStep 1997695 = 2996543) B2996543
theorem B2996549 : Blo 1997435 2996549 := bbase (se 4 (by rfl) ⟨280926, by rfl⟩ : syracuseStep 2996549 = 561853) (by norm_num)
theorem B1997699 : Blo 1997435 1997699 := bstep (se 1 (by rfl) ⟨1498274, by rfl⟩ : syracuseStep 1997699 = 2996549) B2996549
theorem B3371125 : Blo 1997435 3371125 := bbase (se 5 (by rfl) ⟨158021, by rfl⟩ : syracuseStep 3371125 = 316043) (by norm_num)
theorem B4494833 : Blo 1997435 4494833 := bstep (se 2 (by rfl) ⟨1685562, by rfl⟩ : syracuseStep 4494833 = 3371125) B3371125
theorem B2996555 : Blo 1997435 2996555 := bstep (se 1 (by rfl) ⟨2247416, by rfl⟩ : syracuseStep 2996555 = 4494833) B4494833
theorem B1997703 : Blo 1997435 1997703 := bstep (se 1 (by rfl) ⟨1498277, by rfl⟩ : syracuseStep 1997703 = 2996555) B2996555
theorem B2247421 : Blo 1997435 2247421 := bbase (se 3 (by rfl) ⟨421391, by rfl⟩ : syracuseStep 2247421 = 842783) (by norm_num)
theorem B2996561 : Blo 1997435 2996561 := bstep (se 2 (by rfl) ⟨1123710, by rfl⟩ : syracuseStep 2996561 = 2247421) B2247421
theorem B1997707 : Blo 1997435 1997707 := bstep (se 1 (by rfl) ⟨1498280, by rfl⟩ : syracuseStep 1997707 = 2996561) B2996561
theorem B6742277 : Blo 1997435 6742277 := bbase (se 4 (by rfl) ⟨632088, by rfl⟩ : syracuseStep 6742277 = 1264177) (by norm_num)
theorem B4494851 : Blo 1997435 4494851 := bstep (se 1 (by rfl) ⟨3371138, by rfl⟩ : syracuseStep 4494851 = 6742277) B6742277
theorem B2996567 : Blo 1997435 2996567 := bstep (se 1 (by rfl) ⟨2247425, by rfl⟩ : syracuseStep 2996567 = 4494851) B4494851
theorem B1997711 : Blo 1997435 1997711 := bstep (se 1 (by rfl) ⟨1498283, by rfl⟩ : syracuseStep 1997711 = 2996567) B2996567
theorem B2996573 : Blo 1997435 2996573 := bbase (se 3 (by rfl) ⟨561857, by rfl⟩ : syracuseStep 2996573 = 1123715) (by norm_num)
theorem B1997715 : Blo 1997435 1997715 := bstep (se 1 (by rfl) ⟨1498286, by rfl⟩ : syracuseStep 1997715 = 2996573) B2996573
theorem B4494869 : Blo 1997435 4494869 := bbase (se 6 (by rfl) ⟨105348, by rfl⟩ : syracuseStep 4494869 = 210697) (by norm_num)
theorem B2996579 : Blo 1997435 2996579 := bstep (se 1 (by rfl) ⟨2247434, by rfl⟩ : syracuseStep 2996579 = 4494869) B4494869
theorem B1997719 : Blo 1997435 1997719 := bstep (se 1 (by rfl) ⟨1498289, by rfl⟩ : syracuseStep 1997719 = 2996579) B2996579
theorem B7585109 : Blo 1997435 7585109 := bbase (se 11 (by rfl) ⟨5555, by rfl⟩ : syracuseStep 7585109 = 11111) (by norm_num)
theorem B5056739 : Blo 1997435 5056739 := bstep (se 1 (by rfl) ⟨3792554, by rfl⟩ : syracuseStep 5056739 = 7585109) B7585109
theorem B3371159 : Blo 1997435 3371159 := bstep (se 1 (by rfl) ⟨2528369, by rfl⟩ : syracuseStep 3371159 = 5056739) B5056739
theorem B2247439 : Blo 1997435 2247439 := bstep (se 1 (by rfl) ⟨1685579, by rfl⟩ : syracuseStep 2247439 = 3371159) B3371159
theorem B2996585 : Blo 1997435 2996585 := bstep (se 2 (by rfl) ⟨1123719, by rfl⟩ : syracuseStep 2996585 = 2247439) B2247439
theorem B1997723 : Blo 1997435 1997723 := bstep (se 1 (by rfl) ⟨1498292, by rfl⟩ : syracuseStep 1997723 = 2996585) B2996585
theorem B11377685 : Blo 1997435 11377685 := bbase (se 6 (by rfl) ⟨266664, by rfl⟩ : syracuseStep 11377685 = 533329) (by norm_num)
theorem B7585123 : Blo 1997435 7585123 := bstep (se 1 (by rfl) ⟨5688842, by rfl⟩ : syracuseStep 7585123 = 11377685) B11377685
theorem B10113497 : Blo 1997435 10113497 := bstep (se 2 (by rfl) ⟨3792561, by rfl⟩ : syracuseStep 10113497 = 7585123) B7585123
theorem B6742331 : Blo 1997435 6742331 := bstep (se 1 (by rfl) ⟨5056748, by rfl⟩ : syracuseStep 6742331 = 10113497) B10113497
theorem B4494887 : Blo 1997435 4494887 := bstep (se 1 (by rfl) ⟨3371165, by rfl⟩ : syracuseStep 4494887 = 6742331) B6742331
theorem B2996591 : Blo 1997435 2996591 := bstep (se 1 (by rfl) ⟨2247443, by rfl⟩ : syracuseStep 2996591 = 4494887) B4494887
theorem B1997727 : Blo 1997435 1997727 := bstep (se 1 (by rfl) ⟨1498295, by rfl⟩ : syracuseStep 1997727 = 2996591) B2996591
theorem B2996597 : Blo 1997435 2996597 := bbase (se 5 (by rfl) ⟨140465, by rfl⟩ : syracuseStep 2996597 = 280931) (by norm_num)
theorem B1997731 : Blo 1997435 1997731 := bstep (se 1 (by rfl) ⟨1498298, by rfl⟩ : syracuseStep 1997731 = 2996597) B2996597
theorem B2133325 : Blo 1997435 2133325 := bbase (se 3 (by rfl) ⟨399998, by rfl⟩ : syracuseStep 2133325 = 799997) (by norm_num)
theorem B2844433 : Blo 1997435 2844433 := bstep (se 2 (by rfl) ⟨1066662, by rfl⟩ : syracuseStep 2844433 = 2133325) B2133325
theorem B3792577 : Blo 1997435 3792577 := bstep (se 2 (by rfl) ⟨1422216, by rfl⟩ : syracuseStep 3792577 = 2844433) B2844433
theorem B5056769 : Blo 1997435 5056769 := bstep (se 2 (by rfl) ⟨1896288, by rfl⟩ : syracuseStep 5056769 = 3792577) B3792577
theorem B3371179 : Blo 1997435 3371179 := bstep (se 1 (by rfl) ⟨2528384, by rfl⟩ : syracuseStep 3371179 = 5056769) B5056769
theorem B4494905 : Blo 1997435 4494905 := bstep (se 2 (by rfl) ⟨1685589, by rfl⟩ : syracuseStep 4494905 = 3371179) B3371179
theorem B2996603 : Blo 1997435 2996603 := bstep (se 1 (by rfl) ⟨2247452, by rfl⟩ : syracuseStep 2996603 = 4494905) B4494905
theorem B1997735 : Blo 1997435 1997735 := bstep (se 1 (by rfl) ⟨1498301, by rfl⟩ : syracuseStep 1997735 = 2996603) B2996603
theorem B2247457 : Blo 1997435 2247457 := bbase (se 2 (by rfl) ⟨842796, by rfl⟩ : syracuseStep 2247457 = 1685593) (by norm_num)
theorem B2996609 : Blo 1997435 2996609 := bstep (se 2 (by rfl) ⟨1123728, by rfl⟩ : syracuseStep 2996609 = 2247457) B2247457
theorem B1997739 : Blo 1997435 1997739 := bstep (se 1 (by rfl) ⟨1498304, by rfl⟩ : syracuseStep 1997739 = 2996609) B2996609
theorem B5056789 : Blo 1997435 5056789 := bbase (se 6 (by rfl) ⟨118518, by rfl⟩ : syracuseStep 5056789 = 237037) (by norm_num)
theorem B6742385 : Blo 1997435 6742385 := bstep (se 2 (by rfl) ⟨2528394, by rfl⟩ : syracuseStep 6742385 = 5056789) B5056789
theorem B4494923 : Blo 1997435 4494923 := bstep (se 1 (by rfl) ⟨3371192, by rfl⟩ : syracuseStep 4494923 = 6742385) B6742385
theorem B2996615 : Blo 1997435 2996615 := bstep (se 1 (by rfl) ⟨2247461, by rfl⟩ : syracuseStep 2996615 = 4494923) B4494923
theorem B1997743 : Blo 1997435 1997743 := bstep (se 1 (by rfl) ⟨1498307, by rfl⟩ : syracuseStep 1997743 = 2996615) B2996615
theorem B2996621 : Blo 1997435 2996621 := bbase (se 3 (by rfl) ⟨561866, by rfl⟩ : syracuseStep 2996621 = 1123733) (by norm_num)
theorem B1997747 : Blo 1997435 1997747 := bstep (se 1 (by rfl) ⟨1498310, by rfl⟩ : syracuseStep 1997747 = 2996621) B2996621
theorem B4494941 : Blo 1997435 4494941 := bbase (se 3 (by rfl) ⟨842801, by rfl⟩ : syracuseStep 4494941 = 1685603) (by norm_num)
theorem B2996627 : Blo 1997435 2996627 := bstep (se 1 (by rfl) ⟨2247470, by rfl⟩ : syracuseStep 2996627 = 4494941) B4494941
theorem B1997751 : Blo 1997435 1997751 := bstep (se 1 (by rfl) ⟨1498313, by rfl⟩ : syracuseStep 1997751 = 2996627) B2996627
theorem B3371213 : Blo 1997435 3371213 := bbase (se 3 (by rfl) ⟨632102, by rfl⟩ : syracuseStep 3371213 = 1264205) (by norm_num)
theorem B2247475 : Blo 1997435 2247475 := bstep (se 1 (by rfl) ⟨1685606, by rfl⟩ : syracuseStep 2247475 = 3371213) B3371213
theorem B2996633 : Blo 1997435 2996633 := bstep (se 2 (by rfl) ⟨1123737, by rfl⟩ : syracuseStep 2996633 = 2247475) B2247475
theorem B1997755 : Blo 1997435 1997755 := bstep (se 1 (by rfl) ⟨1498316, by rfl⟩ : syracuseStep 1997755 = 2996633) B2996633
theorem B3600029 : Blo 1997435 3600029 := bbase (se 3 (by rfl) ⟨675005, by rfl⟩ : syracuseStep 3600029 = 1350011) (by norm_num)
theorem B2400019 : Blo 1997435 2400019 := bstep (se 1 (by rfl) ⟨1800014, by rfl⟩ : syracuseStep 2400019 = 3600029) B3600029
theorem B12800101 : Blo 1997435 12800101 := bstep (se 4 (by rfl) ⟨1200009, by rfl⟩ : syracuseStep 12800101 = 2400019) B2400019
theorem B17066801 : Blo 1997435 17066801 := bstep (se 2 (by rfl) ⟨6400050, by rfl⟩ : syracuseStep 17066801 = 12800101) B12800101
theorem B11377867 : Blo 1997435 11377867 := bstep (se 1 (by rfl) ⟨8533400, by rfl⟩ : syracuseStep 11377867 = 17066801) B17066801
theorem B15170489 : Blo 1997435 15170489 := bstep (se 2 (by rfl) ⟨5688933, by rfl⟩ : syracuseStep 15170489 = 11377867) B11377867
theorem B10113659 : Blo 1997435 10113659 := bstep (se 1 (by rfl) ⟨7585244, by rfl⟩ : syracuseStep 10113659 = 15170489) B15170489
theorem B6742439 : Blo 1997435 6742439 := bstep (se 1 (by rfl) ⟨5056829, by rfl⟩ : syracuseStep 6742439 = 10113659) B10113659
theorem B4494959 : Blo 1997435 4494959 := bstep (se 1 (by rfl) ⟨3371219, by rfl⟩ : syracuseStep 4494959 = 6742439) B6742439
theorem B2996639 : Blo 1997435 2996639 := bstep (se 1 (by rfl) ⟨2247479, by rfl⟩ : syracuseStep 2996639 = 4494959) B4494959
theorem B1997759 : Blo 1997435 1997759 := bstep (se 1 (by rfl) ⟨1498319, by rfl⟩ : syracuseStep 1997759 = 2996639) B2996639
theorem B2996645 : Blo 1997435 2996645 := bbase (se 4 (by rfl) ⟨280935, by rfl⟩ : syracuseStep 2996645 = 561871) (by norm_num)
theorem B1997763 : Blo 1997435 1997763 := bstep (se 1 (by rfl) ⟨1498322, by rfl⟩ : syracuseStep 1997763 = 2996645) B2996645
theorem B2528425 : Blo 1997435 2528425 := bbase (se 2 (by rfl) ⟨948159, by rfl⟩ : syracuseStep 2528425 = 1896319) (by norm_num)
theorem B3371233 : Blo 1997435 3371233 := bstep (se 2 (by rfl) ⟨1264212, by rfl⟩ : syracuseStep 3371233 = 2528425) B2528425
theorem B4494977 : Blo 1997435 4494977 := bstep (se 2 (by rfl) ⟨1685616, by rfl⟩ : syracuseStep 4494977 = 3371233) B3371233
theorem B2996651 : Blo 1997435 2996651 := bstep (se 1 (by rfl) ⟨2247488, by rfl⟩ : syracuseStep 2996651 = 4494977) B4494977
theorem B1997767 : Blo 1997435 1997767 := bstep (se 1 (by rfl) ⟨1498325, by rfl⟩ : syracuseStep 1997767 = 2996651) B2996651
theorem B2247493 : Blo 1997435 2247493 := bbase (se 4 (by rfl) ⟨210702, by rfl⟩ : syracuseStep 2247493 = 421405) (by norm_num)
theorem B2996657 : Blo 1997435 2996657 := bstep (se 2 (by rfl) ⟨1123746, by rfl⟩ : syracuseStep 2996657 = 2247493) B2247493
theorem B1997771 : Blo 1997435 1997771 := bstep (se 1 (by rfl) ⟨1498328, by rfl⟩ : syracuseStep 1997771 = 2996657) B2996657
theorem B3792653 : Blo 1997435 3792653 := bbase (se 3 (by rfl) ⟨711122, by rfl⟩ : syracuseStep 3792653 = 1422245) (by norm_num)
theorem B2528435 : Blo 1997435 2528435 := bstep (se 1 (by rfl) ⟨1896326, by rfl⟩ : syracuseStep 2528435 = 3792653) B3792653
theorem B6742493 : Blo 1997435 6742493 := bstep (se 3 (by rfl) ⟨1264217, by rfl⟩ : syracuseStep 6742493 = 2528435) B2528435
theorem B4494995 : Blo 1997435 4494995 := bstep (se 1 (by rfl) ⟨3371246, by rfl⟩ : syracuseStep 4494995 = 6742493) B6742493
theorem B2996663 : Blo 1997435 2996663 := bstep (se 1 (by rfl) ⟨2247497, by rfl⟩ : syracuseStep 2996663 = 4494995) B4494995
theorem B1997775 : Blo 1997435 1997775 := bstep (se 1 (by rfl) ⟨1498331, by rfl⟩ : syracuseStep 1997775 = 2996663) B2996663
theorem B2996669 : Blo 1997435 2996669 := bbase (se 3 (by rfl) ⟨561875, by rfl⟩ : syracuseStep 2996669 = 1123751) (by norm_num)
theorem B1997779 : Blo 1997435 1997779 := bstep (se 1 (by rfl) ⟨1498334, by rfl⟩ : syracuseStep 1997779 = 2996669) B2996669
theorem B4495013 : Blo 1997435 4495013 := bbase (se 4 (by rfl) ⟨421407, by rfl⟩ : syracuseStep 4495013 = 842815) (by norm_num)
theorem B2996675 : Blo 1997435 2996675 := bstep (se 1 (by rfl) ⟨2247506, by rfl⟩ : syracuseStep 2996675 = 4495013) B4495013
theorem B1997783 : Blo 1997435 1997783 := bstep (se 1 (by rfl) ⟨1498337, by rfl⟩ : syracuseStep 1997783 = 2996675) B2996675
theorem B5056901 : Blo 1997435 5056901 := bbase (se 4 (by rfl) ⟨474084, by rfl⟩ : syracuseStep 5056901 = 948169) (by norm_num)
theorem B3371267 : Blo 1997435 3371267 := bstep (se 1 (by rfl) ⟨2528450, by rfl⟩ : syracuseStep 3371267 = 5056901) B5056901
theorem B2247511 : Blo 1997435 2247511 := bstep (se 1 (by rfl) ⟨1685633, by rfl⟩ : syracuseStep 2247511 = 3371267) B3371267
theorem B2996681 : Blo 1997435 2996681 := bstep (se 2 (by rfl) ⟨1123755, by rfl⟩ : syracuseStep 2996681 = 2247511) B2247511
theorem B1997787 : Blo 1997435 1997787 := bstep (se 1 (by rfl) ⟨1498340, by rfl⟩ : syracuseStep 1997787 = 2996681) B2996681
theorem B3200077 : Blo 1997435 3200077 := bbase (se 3 (by rfl) ⟨600014, by rfl⟩ : syracuseStep 3200077 = 1200029) (by norm_num)
theorem B4266769 : Blo 1997435 4266769 := bstep (se 2 (by rfl) ⟨1600038, by rfl⟩ : syracuseStep 4266769 = 3200077) B3200077
theorem B5689025 : Blo 1997435 5689025 := bstep (se 2 (by rfl) ⟨2133384, by rfl⟩ : syracuseStep 5689025 = 4266769) B4266769
theorem B3792683 : Blo 1997435 3792683 := bstep (se 1 (by rfl) ⟨2844512, by rfl⟩ : syracuseStep 3792683 = 5689025) B5689025
theorem B10113821 : Blo 1997435 10113821 := bstep (se 3 (by rfl) ⟨1896341, by rfl⟩ : syracuseStep 10113821 = 3792683) B3792683
theorem B6742547 : Blo 1997435 6742547 := bstep (se 1 (by rfl) ⟨5056910, by rfl⟩ : syracuseStep 6742547 = 10113821) B10113821
theorem B4495031 : Blo 1997435 4495031 := bstep (se 1 (by rfl) ⟨3371273, by rfl⟩ : syracuseStep 4495031 = 6742547) B6742547
theorem B2996687 : Blo 1997435 2996687 := bstep (se 1 (by rfl) ⟨2247515, by rfl⟩ : syracuseStep 2996687 = 4495031) B4495031
theorem B1997791 : Blo 1997435 1997791 := bstep (se 1 (by rfl) ⟨1498343, by rfl⟩ : syracuseStep 1997791 = 2996687) B2996687
theorem B2996693 : Blo 1997435 2996693 := bbase (se 7 (by rfl) ⟨35117, by rfl⟩ : syracuseStep 2996693 = 70235) (by norm_num)
theorem B1997795 : Blo 1997435 1997795 := bstep (se 1 (by rfl) ⟨1498346, by rfl⟩ : syracuseStep 1997795 = 2996693) B2996693
theorem B7585397 : Blo 1997435 7585397 := bbase (se 5 (by rfl) ⟨355565, by rfl⟩ : syracuseStep 7585397 = 711131) (by norm_num)
theorem B5056931 : Blo 1997435 5056931 := bstep (se 1 (by rfl) ⟨3792698, by rfl⟩ : syracuseStep 5056931 = 7585397) B7585397
theorem B3371287 : Blo 1997435 3371287 := bstep (se 1 (by rfl) ⟨2528465, by rfl⟩ : syracuseStep 3371287 = 5056931) B5056931
theorem B4495049 : Blo 1997435 4495049 := bstep (se 2 (by rfl) ⟨1685643, by rfl⟩ : syracuseStep 4495049 = 3371287) B3371287
theorem B2996699 : Blo 1997435 2996699 := bstep (se 1 (by rfl) ⟨2247524, by rfl⟩ : syracuseStep 2996699 = 4495049) B4495049
theorem B1997799 : Blo 1997435 1997799 := bstep (se 1 (by rfl) ⟨1498349, by rfl⟩ : syracuseStep 1997799 = 2996699) B2996699
theorem B2247529 : Blo 1997435 2247529 := bbase (se 2 (by rfl) ⟨842823, by rfl⟩ : syracuseStep 2247529 = 1685647) (by norm_num)
theorem B2996705 : Blo 1997435 2996705 := bstep (se 2 (by rfl) ⟨1123764, by rfl⟩ : syracuseStep 2996705 = 2247529) B2247529
theorem B1997803 : Blo 1997435 1997803 := bstep (se 1 (by rfl) ⟨1498352, by rfl⟩ : syracuseStep 1997803 = 2996705) B2996705
theorem B2400077 : Blo 1997435 2400077 := bbase (se 3 (by rfl) ⟨450014, by rfl⟩ : syracuseStep 2400077 = 900029) (by norm_num)
theorem B6400205 : Blo 1997435 6400205 := bstep (se 3 (by rfl) ⟨1200038, by rfl⟩ : syracuseStep 6400205 = 2400077) B2400077
theorem B4266803 : Blo 1997435 4266803 := bstep (se 1 (by rfl) ⟨3200102, by rfl⟩ : syracuseStep 4266803 = 6400205) B6400205
theorem B11378141 : Blo 1997435 11378141 := bstep (se 3 (by rfl) ⟨2133401, by rfl⟩ : syracuseStep 11378141 = 4266803) B4266803
theorem B7585427 : Blo 1997435 7585427 := bstep (se 1 (by rfl) ⟨5689070, by rfl⟩ : syracuseStep 7585427 = 11378141) B11378141
theorem B5056951 : Blo 1997435 5056951 := bstep (se 1 (by rfl) ⟨3792713, by rfl⟩ : syracuseStep 5056951 = 7585427) B7585427
theorem B6742601 : Blo 1997435 6742601 := bstep (se 2 (by rfl) ⟨2528475, by rfl⟩ : syracuseStep 6742601 = 5056951) B5056951
theorem B4495067 : Blo 1997435 4495067 := bstep (se 1 (by rfl) ⟨3371300, by rfl⟩ : syracuseStep 4495067 = 6742601) B6742601
theorem B2996711 : Blo 1997435 2996711 := bstep (se 1 (by rfl) ⟨2247533, by rfl⟩ : syracuseStep 2996711 = 4495067) B4495067
theorem B1997807 : Blo 1997435 1997807 := bstep (se 1 (by rfl) ⟨1498355, by rfl⟩ : syracuseStep 1997807 = 2996711) B2996711
theorem B2996717 : Blo 1997435 2996717 := bbase (se 3 (by rfl) ⟨561884, by rfl⟩ : syracuseStep 2996717 = 1123769) (by norm_num)
theorem B1997811 : Blo 1997435 1997811 := bstep (se 1 (by rfl) ⟨1498358, by rfl⟩ : syracuseStep 1997811 = 2996717) B2996717
theorem B4495085 : Blo 1997435 4495085 := bbase (se 3 (by rfl) ⟨842828, by rfl⟩ : syracuseStep 4495085 = 1685657) (by norm_num)
theorem B2996723 : Blo 1997435 2996723 := bstep (se 1 (by rfl) ⟨2247542, by rfl⟩ : syracuseStep 2996723 = 4495085) B4495085
theorem B1997815 : Blo 1997435 1997815 := bstep (se 1 (by rfl) ⟨1498361, by rfl⟩ : syracuseStep 1997815 = 2996723) B2996723
theorem B4050157 : Blo 1997435 4050157 := bbase (se 3 (by rfl) ⟨759404, by rfl⟩ : syracuseStep 4050157 = 1518809) (by norm_num)
theorem B5400209 : Blo 1997435 5400209 := bstep (se 2 (by rfl) ⟨2025078, by rfl⟩ : syracuseStep 5400209 = 4050157) B4050157
theorem B3600139 : Blo 1997435 3600139 := bstep (se 1 (by rfl) ⟨2700104, by rfl⟩ : syracuseStep 3600139 = 5400209) B5400209
theorem B4800185 : Blo 1997435 4800185 := bstep (se 2 (by rfl) ⟨1800069, by rfl⟩ : syracuseStep 4800185 = 3600139) B3600139
theorem B3200123 : Blo 1997435 3200123 := bstep (se 1 (by rfl) ⟨2400092, by rfl⟩ : syracuseStep 3200123 = 4800185) B4800185
theorem B2133415 : Blo 1997435 2133415 := bstep (se 1 (by rfl) ⟨1600061, by rfl⟩ : syracuseStep 2133415 = 3200123) B3200123
theorem B2844553 : Blo 1997435 2844553 := bstep (se 2 (by rfl) ⟨1066707, by rfl⟩ : syracuseStep 2844553 = 2133415) B2133415
theorem B3792737 : Blo 1997435 3792737 := bstep (se 2 (by rfl) ⟨1422276, by rfl⟩ : syracuseStep 3792737 = 2844553) B2844553
theorem B2528491 : Blo 1997435 2528491 := bstep (se 1 (by rfl) ⟨1896368, by rfl⟩ : syracuseStep 2528491 = 3792737) B3792737
theorem B3371321 : Blo 1997435 3371321 := bstep (se 2 (by rfl) ⟨1264245, by rfl⟩ : syracuseStep 3371321 = 2528491) B2528491
theorem B2247547 : Blo 1997435 2247547 := bstep (se 1 (by rfl) ⟨1685660, by rfl⟩ : syracuseStep 2247547 = 3371321) B3371321
theorem B2996729 : Blo 1997435 2996729 := bstep (se 2 (by rfl) ⟨1123773, by rfl⟩ : syracuseStep 2996729 = 2247547) B2247547
theorem B1997819 : Blo 1997435 1997819 := bstep (se 1 (by rfl) ⟨1498364, by rfl⟩ : syracuseStep 1997819 = 2996729) B2996729
theorem B2340805 : Blo 1997435 2340805 := bbase (se 4 (by rfl) ⟨219450, by rfl⟩ : syracuseStep 2340805 = 438901) (by norm_num)
theorem B3121073 : Blo 1997435 3121073 := bstep (se 2 (by rfl) ⟨1170402, by rfl⟩ : syracuseStep 3121073 = 2340805) B2340805
theorem B133165781 : Blo 1997435 133165781 := bstep (se 7 (by rfl) ⟨1560536, by rfl⟩ : syracuseStep 133165781 = 3121073) B3121073
theorem B88777187 : Blo 1997435 88777187 := bstep (se 1 (by rfl) ⟨66582890, by rfl⟩ : syracuseStep 88777187 = 133165781) B133165781
theorem B59184791 : Blo 1997435 59184791 := bstep (se 1 (by rfl) ⟨44388593, by rfl⟩ : syracuseStep 59184791 = 88777187) B88777187
theorem B39456527 : Blo 1997435 39456527 := bstep (se 1 (by rfl) ⟨29592395, by rfl⟩ : syracuseStep 39456527 = 59184791) B59184791
theorem B420869621 : Blo 1997435 420869621 := bstep (se 5 (by rfl) ⟨19728263, by rfl⟩ : syracuseStep 420869621 = 39456527) B39456527
theorem B1122318989 : Blo 1997435 1122318989 := bstep (se 3 (by rfl) ⟨210434810, by rfl⟩ : syracuseStep 1122318989 = 420869621) B420869621
theorem B748212659 : Blo 1997435 748212659 := bstep (se 1 (by rfl) ⟨561159494, by rfl⟩ : syracuseStep 748212659 = 1122318989) B1122318989
theorem B498808439 : Blo 1997435 498808439 := bstep (se 1 (by rfl) ⟨374106329, by rfl⟩ : syracuseStep 498808439 = 748212659) B748212659
theorem B332538959 : Blo 1997435 332538959 := bstep (se 1 (by rfl) ⟨249404219, by rfl⟩ : syracuseStep 332538959 = 498808439) B498808439
theorem B221692639 : Blo 1997435 221692639 := bstep (se 1 (by rfl) ⟨166269479, by rfl⟩ : syracuseStep 221692639 = 332538959) B332538959
theorem B295590185 : Blo 1997435 295590185 := bstep (se 2 (by rfl) ⟨110846319, by rfl⟩ : syracuseStep 295590185 = 221692639) B221692639
theorem B197060123 : Blo 1997435 197060123 := bstep (se 1 (by rfl) ⟨147795092, by rfl⟩ : syracuseStep 197060123 = 295590185) B295590185
theorem B131373415 : Blo 1997435 131373415 := bstep (se 1 (by rfl) ⟨98530061, by rfl⟩ : syracuseStep 131373415 = 197060123) B197060123
theorem B175164553 : Blo 1997435 175164553 := bstep (se 2 (by rfl) ⟨65686707, by rfl⟩ : syracuseStep 175164553 = 131373415) B131373415
theorem B233552737 : Blo 1997435 233552737 := bstep (se 2 (by rfl) ⟨87582276, by rfl⟩ : syracuseStep 233552737 = 175164553) B175164553
theorem B1245614597 : Blo 1997435 1245614597 := bstep (se 4 (by rfl) ⟨116776368, by rfl⟩ : syracuseStep 1245614597 = 233552737) B233552737
theorem B830409731 : Blo 1997435 830409731 := bstep (se 1 (by rfl) ⟨622807298, by rfl⟩ : syracuseStep 830409731 = 1245614597) B1245614597
theorem B553606487 : Blo 1997435 553606487 := bstep (se 1 (by rfl) ⟨415204865, by rfl⟩ : syracuseStep 553606487 = 830409731) B830409731
theorem B369070991 : Blo 1997435 369070991 := bstep (se 1 (by rfl) ⟨276803243, by rfl⟩ : syracuseStep 369070991 = 553606487) B553606487
theorem B246047327 : Blo 1997435 246047327 := bstep (se 1 (by rfl) ⟨184535495, by rfl⟩ : syracuseStep 246047327 = 369070991) B369070991
theorem B164031551 : Blo 1997435 164031551 := bstep (se 1 (by rfl) ⟨123023663, by rfl⟩ : syracuseStep 164031551 = 246047327) B246047327
theorem B109354367 : Blo 1997435 109354367 := bstep (se 1 (by rfl) ⟨82015775, by rfl⟩ : syracuseStep 109354367 = 164031551) B164031551
theorem B72902911 : Blo 1997435 72902911 := bstep (se 1 (by rfl) ⟨54677183, by rfl⟩ : syracuseStep 72902911 = 109354367) B109354367
theorem B97203881 : Blo 1997435 97203881 := bstep (se 2 (by rfl) ⟨36451455, by rfl⟩ : syracuseStep 97203881 = 72902911) B72902911
theorem B64802587 : Blo 1997435 64802587 := bstep (se 1 (by rfl) ⟨48601940, by rfl⟩ : syracuseStep 64802587 = 97203881) B97203881
theorem B86403449 : Blo 1997435 86403449 := bstep (se 2 (by rfl) ⟨32401293, by rfl⟩ : syracuseStep 86403449 = 64802587) B64802587
theorem B57602299 : Blo 1997435 57602299 := bstep (se 1 (by rfl) ⟨43201724, by rfl⟩ : syracuseStep 57602299 = 86403449) B86403449
theorem B76803065 : Blo 1997435 76803065 := bstep (se 2 (by rfl) ⟨28801149, by rfl⟩ : syracuseStep 76803065 = 57602299) B57602299
theorem B51202043 : Blo 1997435 51202043 := bstep (se 1 (by rfl) ⟨38401532, by rfl⟩ : syracuseStep 51202043 = 76803065) B76803065
theorem B34134695 : Blo 1997435 34134695 := bstep (se 1 (by rfl) ⟨25601021, by rfl⟩ : syracuseStep 34134695 = 51202043) B51202043
theorem B22756463 : Blo 1997435 22756463 := bstep (se 1 (by rfl) ⟨17067347, by rfl⟩ : syracuseStep 22756463 = 34134695) B34134695
theorem B15170975 : Blo 1997435 15170975 := bstep (se 1 (by rfl) ⟨11378231, by rfl⟩ : syracuseStep 15170975 = 22756463) B22756463
theorem B10113983 : Blo 1997435 10113983 := bstep (se 1 (by rfl) ⟨7585487, by rfl⟩ : syracuseStep 10113983 = 15170975) B15170975
theorem B6742655 : Blo 1997435 6742655 := bstep (se 1 (by rfl) ⟨5056991, by rfl⟩ : syracuseStep 6742655 = 10113983) B10113983
theorem B4495103 : Blo 1997435 4495103 := bstep (se 1 (by rfl) ⟨3371327, by rfl⟩ : syracuseStep 4495103 = 6742655) B6742655
theorem B2996735 : Blo 1997435 2996735 := bstep (se 1 (by rfl) ⟨2247551, by rfl⟩ : syracuseStep 2996735 = 4495103) B4495103
theorem B1997823 : Blo 1997435 1997823 := bstep (se 1 (by rfl) ⟨1498367, by rfl⟩ : syracuseStep 1997823 = 2996735) B2996735
theorem B2996741 : Blo 1997435 2996741 := bbase (se 4 (by rfl) ⟨280944, by rfl⟩ : syracuseStep 2996741 = 561889) (by norm_num)
theorem B1997827 : Blo 1997435 1997827 := bstep (se 1 (by rfl) ⟨1498370, by rfl⟩ : syracuseStep 1997827 = 2996741) B2996741
theorem B3371341 : Blo 1997435 3371341 := bbase (se 3 (by rfl) ⟨632126, by rfl⟩ : syracuseStep 3371341 = 1264253) (by norm_num)
theorem B4495121 : Blo 1997435 4495121 := bstep (se 2 (by rfl) ⟨1685670, by rfl⟩ : syracuseStep 4495121 = 3371341) B3371341
theorem B2996747 : Blo 1997435 2996747 := bstep (se 1 (by rfl) ⟨2247560, by rfl⟩ : syracuseStep 2996747 = 4495121) B4495121
theorem B1997831 : Blo 1997435 1997831 := bstep (se 1 (by rfl) ⟨1498373, by rfl⟩ : syracuseStep 1997831 = 2996747) B2996747
theorem B2247565 : Blo 1997435 2247565 := bbase (se 3 (by rfl) ⟨421418, by rfl⟩ : syracuseStep 2247565 = 842837) (by norm_num)
theorem B2996753 : Blo 1997435 2996753 := bstep (se 2 (by rfl) ⟨1123782, by rfl⟩ : syracuseStep 2996753 = 2247565) B2247565
theorem B1997835 : Blo 1997435 1997835 := bstep (se 1 (by rfl) ⟨1498376, by rfl⟩ : syracuseStep 1997835 = 2996753) B2996753
theorem B6742709 : Blo 1997435 6742709 := bbase (se 5 (by rfl) ⟨316064, by rfl⟩ : syracuseStep 6742709 = 632129) (by norm_num)
theorem B4495139 : Blo 1997435 4495139 := bstep (se 1 (by rfl) ⟨3371354, by rfl⟩ : syracuseStep 4495139 = 6742709) B6742709
theorem B2996759 : Blo 1997435 2996759 := bstep (se 1 (by rfl) ⟨2247569, by rfl⟩ : syracuseStep 2996759 = 4495139) B4495139
theorem B1997839 : Blo 1997435 1997839 := bstep (se 1 (by rfl) ⟨1498379, by rfl⟩ : syracuseStep 1997839 = 2996759) B2996759
theorem B2996765 : Blo 1997435 2996765 := bbase (se 3 (by rfl) ⟨561893, by rfl⟩ : syracuseStep 2996765 = 1123787) (by norm_num)
theorem B1997843 : Blo 1997435 1997843 := bstep (se 1 (by rfl) ⟨1498382, by rfl⟩ : syracuseStep 1997843 = 2996765) B2996765
theorem B4495157 : Blo 1997435 4495157 := bbase (se 5 (by rfl) ⟨210710, by rfl⟩ : syracuseStep 4495157 = 421421) (by norm_num)
theorem B2996771 : Blo 1997435 2996771 := bstep (se 1 (by rfl) ⟨2247578, by rfl⟩ : syracuseStep 2996771 = 4495157) B4495157
theorem B1997847 : Blo 1997435 1997847 := bstep (se 1 (by rfl) ⟨1498385, by rfl⟩ : syracuseStep 1997847 = 2996771) B2996771
theorem B12800693 : Blo 1997435 12800693 := bbase (se 5 (by rfl) ⟨600032, by rfl⟩ : syracuseStep 12800693 = 1200065) (by norm_num)
theorem B8533795 : Blo 1997435 8533795 := bstep (se 1 (by rfl) ⟨6400346, by rfl⟩ : syracuseStep 8533795 = 12800693) B12800693
theorem B11378393 : Blo 1997435 11378393 := bstep (se 2 (by rfl) ⟨4266897, by rfl⟩ : syracuseStep 11378393 = 8533795) B8533795
theorem B7585595 : Blo 1997435 7585595 := bstep (se 1 (by rfl) ⟨5689196, by rfl⟩ : syracuseStep 7585595 = 11378393) B11378393
theorem B5057063 : Blo 1997435 5057063 := bstep (se 1 (by rfl) ⟨3792797, by rfl⟩ : syracuseStep 5057063 = 7585595) B7585595
theorem B3371375 : Blo 1997435 3371375 := bstep (se 1 (by rfl) ⟨2528531, by rfl⟩ : syracuseStep 3371375 = 5057063) B5057063
theorem B2247583 : Blo 1997435 2247583 := bstep (se 1 (by rfl) ⟨1685687, by rfl⟩ : syracuseStep 2247583 = 3371375) B3371375
theorem B2996777 : Blo 1997435 2996777 := bstep (se 2 (by rfl) ⟨1123791, by rfl⟩ : syracuseStep 2996777 = 2247583) B2247583
theorem B1997851 : Blo 1997435 1997851 := bstep (se 1 (by rfl) ⟨1498388, by rfl⟩ : syracuseStep 1997851 = 2996777) B2996777
theorem B4800269 : Blo 1997435 4800269 := bbase (se 3 (by rfl) ⟨900050, by rfl⟩ : syracuseStep 4800269 = 1800101) (by norm_num)
theorem B12800717 : Blo 1997435 12800717 := bstep (se 3 (by rfl) ⟨2400134, by rfl⟩ : syracuseStep 12800717 = 4800269) B4800269
theorem B8533811 : Blo 1997435 8533811 := bstep (se 1 (by rfl) ⟨6400358, by rfl⟩ : syracuseStep 8533811 = 12800717) B12800717
theorem B5689207 : Blo 1997435 5689207 := bstep (se 1 (by rfl) ⟨4266905, by rfl⟩ : syracuseStep 5689207 = 8533811) B8533811
theorem B7585609 : Blo 1997435 7585609 := bstep (se 2 (by rfl) ⟨2844603, by rfl⟩ : syracuseStep 7585609 = 5689207) B5689207
theorem B10114145 : Blo 1997435 10114145 := bstep (se 2 (by rfl) ⟨3792804, by rfl⟩ : syracuseStep 10114145 = 7585609) B7585609
theorem B6742763 : Blo 1997435 6742763 := bstep (se 1 (by rfl) ⟨5057072, by rfl⟩ : syracuseStep 6742763 = 10114145) B10114145
theorem B4495175 : Blo 1997435 4495175 := bstep (se 1 (by rfl) ⟨3371381, by rfl⟩ : syracuseStep 4495175 = 6742763) B6742763
theorem B2996783 : Blo 1997435 2996783 := bstep (se 1 (by rfl) ⟨2247587, by rfl⟩ : syracuseStep 2996783 = 4495175) B4495175
theorem B1997855 : Blo 1997435 1997855 := bstep (se 1 (by rfl) ⟨1498391, by rfl⟩ : syracuseStep 1997855 = 2996783) B2996783
theorem B2996789 : Blo 1997435 2996789 := bbase (se 5 (by rfl) ⟨140474, by rfl⟩ : syracuseStep 2996789 = 280949) (by norm_num)
theorem B1997859 : Blo 1997435 1997859 := bstep (se 1 (by rfl) ⟨1498394, by rfl⟩ : syracuseStep 1997859 = 2996789) B2996789
theorem B5057093 : Blo 1997435 5057093 := bbase (se 4 (by rfl) ⟨474102, by rfl⟩ : syracuseStep 5057093 = 948205) (by norm_num)
theorem B3371395 : Blo 1997435 3371395 := bstep (se 1 (by rfl) ⟨2528546, by rfl⟩ : syracuseStep 3371395 = 5057093) B5057093
theorem B4495193 : Blo 1997435 4495193 := bstep (se 2 (by rfl) ⟨1685697, by rfl⟩ : syracuseStep 4495193 = 3371395) B3371395
theorem B2996795 : Blo 1997435 2996795 := bstep (se 1 (by rfl) ⟨2247596, by rfl⟩ : syracuseStep 2996795 = 4495193) B4495193
theorem B1997863 : Blo 1997435 1997863 := bstep (se 1 (by rfl) ⟨1498397, by rfl⟩ : syracuseStep 1997863 = 2996795) B2996795
theorem B2247601 : Blo 1997435 2247601 := bbase (se 2 (by rfl) ⟨842850, by rfl⟩ : syracuseStep 2247601 = 1685701) (by norm_num)
theorem B2996801 : Blo 1997435 2996801 := bstep (se 2 (by rfl) ⟨1123800, by rfl⟩ : syracuseStep 2996801 = 2247601) B2247601
theorem B1997867 : Blo 1997435 1997867 := bstep (se 1 (by rfl) ⟨1498400, by rfl⟩ : syracuseStep 1997867 = 2996801) B2996801
theorem B5689253 : Blo 1997435 5689253 := bbase (se 4 (by rfl) ⟨533367, by rfl⟩ : syracuseStep 5689253 = 1066735) (by norm_num)
theorem B3792835 : Blo 1997435 3792835 := bstep (se 1 (by rfl) ⟨2844626, by rfl⟩ : syracuseStep 3792835 = 5689253) B5689253
theorem B5057113 : Blo 1997435 5057113 := bstep (se 2 (by rfl) ⟨1896417, by rfl⟩ : syracuseStep 5057113 = 3792835) B3792835
theorem B6742817 : Blo 1997435 6742817 := bstep (se 2 (by rfl) ⟨2528556, by rfl⟩ : syracuseStep 6742817 = 5057113) B5057113
theorem B4495211 : Blo 1997435 4495211 := bstep (se 1 (by rfl) ⟨3371408, by rfl⟩ : syracuseStep 4495211 = 6742817) B6742817
theorem B2996807 : Blo 1997435 2996807 := bstep (se 1 (by rfl) ⟨2247605, by rfl⟩ : syracuseStep 2996807 = 4495211) B4495211
theorem B1997871 : Blo 1997435 1997871 := bstep (se 1 (by rfl) ⟨1498403, by rfl⟩ : syracuseStep 1997871 = 2996807) B2996807
theorem B2996813 : Blo 1997435 2996813 := bbase (se 3 (by rfl) ⟨561902, by rfl⟩ : syracuseStep 2996813 = 1123805) (by norm_num)
theorem B1997875 : Blo 1997435 1997875 := bstep (se 1 (by rfl) ⟨1498406, by rfl⟩ : syracuseStep 1997875 = 2996813) B2996813
theorem B4495229 : Blo 1997435 4495229 := bbase (se 3 (by rfl) ⟨842855, by rfl⟩ : syracuseStep 4495229 = 1685711) (by norm_num)
theorem B2996819 : Blo 1997435 2996819 := bstep (se 1 (by rfl) ⟨2247614, by rfl⟩ : syracuseStep 2996819 = 4495229) B4495229
theorem B1997879 : Blo 1997435 1997879 := bstep (se 1 (by rfl) ⟨1498409, by rfl⟩ : syracuseStep 1997879 = 2996819) B2996819
theorem B3371429 : Blo 1997435 3371429 := bbase (se 4 (by rfl) ⟨316071, by rfl⟩ : syracuseStep 3371429 = 632143) (by norm_num)
theorem B2247619 : Blo 1997435 2247619 := bstep (se 1 (by rfl) ⟨1685714, by rfl⟩ : syracuseStep 2247619 = 3371429) B3371429
theorem B2996825 : Blo 1997435 2996825 := bstep (se 2 (by rfl) ⟨1123809, by rfl⟩ : syracuseStep 2996825 = 2247619) B2247619
theorem B1997883 : Blo 1997435 1997883 := bstep (se 1 (by rfl) ⟨1498412, by rfl⟩ : syracuseStep 1997883 = 2996825) B2996825
theorem B2432921 : Blo 1997435 2432921 := bbase (se 2 (by rfl) ⟨912345, by rfl⟩ : syracuseStep 2432921 = 1824691) (by norm_num)
theorem B6487789 : Blo 1997435 6487789 := bstep (se 3 (by rfl) ⟨1216460, by rfl⟩ : syracuseStep 6487789 = 2432921) B2432921
theorem B8650385 : Blo 1997435 8650385 := bstep (se 2 (by rfl) ⟨3243894, by rfl⟩ : syracuseStep 8650385 = 6487789) B6487789
theorem B5766923 : Blo 1997435 5766923 := bstep (se 1 (by rfl) ⟨4325192, by rfl⟩ : syracuseStep 5766923 = 8650385) B8650385
theorem B15378461 : Blo 1997435 15378461 := bstep (se 3 (by rfl) ⟨2883461, by rfl⟩ : syracuseStep 15378461 = 5766923) B5766923
theorem B10252307 : Blo 1997435 10252307 := bstep (se 1 (by rfl) ⟨7689230, by rfl⟩ : syracuseStep 10252307 = 15378461) B15378461
theorem B6834871 : Blo 1997435 6834871 := bstep (se 1 (by rfl) ⟨5126153, by rfl⟩ : syracuseStep 6834871 = 10252307) B10252307
theorem B9113161 : Blo 1997435 9113161 := bstep (se 2 (by rfl) ⟨3417435, by rfl⟩ : syracuseStep 9113161 = 6834871) B6834871
theorem B12150881 : Blo 1997435 12150881 := bstep (se 2 (by rfl) ⟨4556580, by rfl⟩ : syracuseStep 12150881 = 9113161) B9113161
theorem B8100587 : Blo 1997435 8100587 := bstep (se 1 (by rfl) ⟨6075440, by rfl⟩ : syracuseStep 8100587 = 12150881) B12150881
theorem B5400391 : Blo 1997435 5400391 := bstep (se 1 (by rfl) ⟨4050293, by rfl⟩ : syracuseStep 5400391 = 8100587) B8100587
theorem B7200521 : Blo 1997435 7200521 := bstep (se 2 (by rfl) ⟨2700195, by rfl⟩ : syracuseStep 7200521 = 5400391) B5400391
theorem B4800347 : Blo 1997435 4800347 := bstep (se 1 (by rfl) ⟨3600260, by rfl⟩ : syracuseStep 4800347 = 7200521) B7200521
theorem B3200231 : Blo 1997435 3200231 := bstep (se 1 (by rfl) ⟨2400173, by rfl⟩ : syracuseStep 3200231 = 4800347) B4800347
theorem B2133487 : Blo 1997435 2133487 := bstep (se 1 (by rfl) ⟨1600115, by rfl⟩ : syracuseStep 2133487 = 3200231) B3200231
theorem B2844649 : Blo 1997435 2844649 := bstep (se 2 (by rfl) ⟨1066743, by rfl⟩ : syracuseStep 2844649 = 2133487) B2133487
theorem B15171461 : Blo 1997435 15171461 := bstep (se 4 (by rfl) ⟨1422324, by rfl⟩ : syracuseStep 15171461 = 2844649) B2844649
theorem B10114307 : Blo 1997435 10114307 := bstep (se 1 (by rfl) ⟨7585730, by rfl⟩ : syracuseStep 10114307 = 15171461) B15171461
theorem B6742871 : Blo 1997435 6742871 := bstep (se 1 (by rfl) ⟨5057153, by rfl⟩ : syracuseStep 6742871 = 10114307) B10114307
theorem B4495247 : Blo 1997435 4495247 := bstep (se 1 (by rfl) ⟨3371435, by rfl⟩ : syracuseStep 4495247 = 6742871) B6742871
theorem B2996831 : Blo 1997435 2996831 := bstep (se 1 (by rfl) ⟨2247623, by rfl⟩ : syracuseStep 2996831 = 4495247) B4495247
theorem B1997887 : Blo 1997435 1997887 := bstep (se 1 (by rfl) ⟨1498415, by rfl⟩ : syracuseStep 1997887 = 2996831) B2996831
theorem B2996837 : Blo 1997435 2996837 := bbase (se 4 (by rfl) ⟨280953, by rfl⟩ : syracuseStep 2996837 = 561907) (by norm_num)
theorem B1997891 : Blo 1997435 1997891 := bstep (se 1 (by rfl) ⟨1498418, by rfl⟩ : syracuseStep 1997891 = 2996837) B2996837
theorem B2844661 : Blo 1997435 2844661 := bbase (se 5 (by rfl) ⟨133343, by rfl⟩ : syracuseStep 2844661 = 266687) (by norm_num)
theorem B3792881 : Blo 1997435 3792881 := bstep (se 2 (by rfl) ⟨1422330, by rfl⟩ : syracuseStep 3792881 = 2844661) B2844661
theorem B2528587 : Blo 1997435 2528587 := bstep (se 1 (by rfl) ⟨1896440, by rfl⟩ : syracuseStep 2528587 = 3792881) B3792881
theorem B3371449 : Blo 1997435 3371449 := bstep (se 2 (by rfl) ⟨1264293, by rfl⟩ : syracuseStep 3371449 = 2528587) B2528587
theorem B4495265 : Blo 1997435 4495265 := bstep (se 2 (by rfl) ⟨1685724, by rfl⟩ : syracuseStep 4495265 = 3371449) B3371449
theorem B2996843 : Blo 1997435 2996843 := bstep (se 1 (by rfl) ⟨2247632, by rfl⟩ : syracuseStep 2996843 = 4495265) B4495265
theorem B1997895 : Blo 1997435 1997895 := bstep (se 1 (by rfl) ⟨1498421, by rfl⟩ : syracuseStep 1997895 = 2996843) B2996843
theorem B2247637 : Blo 1997435 2247637 := bbase (se 7 (by rfl) ⟨26339, by rfl⟩ : syracuseStep 2247637 = 52679) (by norm_num)
theorem B2996849 : Blo 1997435 2996849 := bstep (se 2 (by rfl) ⟨1123818, by rfl⟩ : syracuseStep 2996849 = 2247637) B2247637
theorem B1997899 : Blo 1997435 1997899 := bstep (se 1 (by rfl) ⟨1498424, by rfl⟩ : syracuseStep 1997899 = 2996849) B2996849
theorem B2528597 : Blo 1997435 2528597 := bbase (se 14 (by rfl) ⟨231, by rfl⟩ : syracuseStep 2528597 = 463) (by norm_num)
theorem B6742925 : Blo 1997435 6742925 := bstep (se 3 (by rfl) ⟨1264298, by rfl⟩ : syracuseStep 6742925 = 2528597) B2528597
theorem B4495283 : Blo 1997435 4495283 := bstep (se 1 (by rfl) ⟨3371462, by rfl⟩ : syracuseStep 4495283 = 6742925) B6742925
theorem B2996855 : Blo 1997435 2996855 := bstep (se 1 (by rfl) ⟨2247641, by rfl⟩ : syracuseStep 2996855 = 4495283) B4495283
theorem B1997903 : Blo 1997435 1997903 := bstep (se 1 (by rfl) ⟨1498427, by rfl⟩ : syracuseStep 1997903 = 2996855) B2996855
theorem B2996861 : Blo 1997435 2996861 := bbase (se 3 (by rfl) ⟨561911, by rfl⟩ : syracuseStep 2996861 = 1123823) (by norm_num)
theorem B1997907 : Blo 1997435 1997907 := bstep (se 1 (by rfl) ⟨1498430, by rfl⟩ : syracuseStep 1997907 = 2996861) B2996861
theorem B4495301 : Blo 1997435 4495301 := bbase (se 4 (by rfl) ⟨421434, by rfl⟩ : syracuseStep 4495301 = 842869) (by norm_num)
theorem B2996867 : Blo 1997435 2996867 := bstep (se 1 (by rfl) ⟨2247650, by rfl⟩ : syracuseStep 2996867 = 4495301) B4495301
theorem B1997911 : Blo 1997435 1997911 := bstep (se 1 (by rfl) ⟨1498433, by rfl⟩ : syracuseStep 1997911 = 2996867) B2996867
theorem B8534069 : Blo 1997435 8534069 := bbase (se 5 (by rfl) ⟨400034, by rfl⟩ : syracuseStep 8534069 = 800069) (by norm_num)
theorem B5689379 : Blo 1997435 5689379 := bstep (se 1 (by rfl) ⟨4267034, by rfl⟩ : syracuseStep 5689379 = 8534069) B8534069
theorem B3792919 : Blo 1997435 3792919 := bstep (se 1 (by rfl) ⟨2844689, by rfl⟩ : syracuseStep 3792919 = 5689379) B5689379
theorem B5057225 : Blo 1997435 5057225 := bstep (se 2 (by rfl) ⟨1896459, by rfl⟩ : syracuseStep 5057225 = 3792919) B3792919
theorem B3371483 : Blo 1997435 3371483 := bstep (se 1 (by rfl) ⟨2528612, by rfl⟩ : syracuseStep 3371483 = 5057225) B5057225
theorem B2247655 : Blo 1997435 2247655 := bstep (se 1 (by rfl) ⟨1685741, by rfl⟩ : syracuseStep 2247655 = 3371483) B3371483
theorem B2996873 : Blo 1997435 2996873 := bstep (se 2 (by rfl) ⟨1123827, by rfl⟩ : syracuseStep 2996873 = 2247655) B2247655
theorem B1997915 : Blo 1997435 1997915 := bstep (se 1 (by rfl) ⟨1498436, by rfl⟩ : syracuseStep 1997915 = 2996873) B2996873
theorem B10114469 : Blo 1997435 10114469 := bbase (se 4 (by rfl) ⟨948231, by rfl⟩ : syracuseStep 10114469 = 1896463) (by norm_num)
theorem B6742979 : Blo 1997435 6742979 := bstep (se 1 (by rfl) ⟨5057234, by rfl⟩ : syracuseStep 6742979 = 10114469) B10114469
theorem B4495319 : Blo 1997435 4495319 := bstep (se 1 (by rfl) ⟨3371489, by rfl⟩ : syracuseStep 4495319 = 6742979) B6742979
theorem B2996879 : Blo 1997435 2996879 := bstep (se 1 (by rfl) ⟨2247659, by rfl⟩ : syracuseStep 2996879 = 4495319) B4495319
theorem B1997919 : Blo 1997435 1997919 := bstep (se 1 (by rfl) ⟨1498439, by rfl⟩ : syracuseStep 1997919 = 2996879) B2996879
theorem B2996885 : Blo 1997435 2996885 := bbase (se 6 (by rfl) ⟨70239, by rfl⟩ : syracuseStep 2996885 = 140479) (by norm_num)
theorem B1997923 : Blo 1997435 1997923 := bstep (se 1 (by rfl) ⟨1498442, by rfl⟩ : syracuseStep 1997923 = 2996885) B2996885
theorem B4105637 : Blo 1997435 4105637 := bbase (se 4 (by rfl) ⟨384903, by rfl⟩ : syracuseStep 4105637 = 769807) (by norm_num)
theorem B2737091 : Blo 1997435 2737091 := bstep (se 1 (by rfl) ⟨2052818, by rfl⟩ : syracuseStep 2737091 = 4105637) B4105637
theorem B7298909 : Blo 1997435 7298909 := bstep (se 3 (by rfl) ⟨1368545, by rfl⟩ : syracuseStep 7298909 = 2737091) B2737091
theorem B4865939 : Blo 1997435 4865939 := bstep (se 1 (by rfl) ⟨3649454, by rfl⟩ : syracuseStep 4865939 = 7298909) B7298909
theorem B3243959 : Blo 1997435 3243959 := bstep (se 1 (by rfl) ⟨2432969, by rfl⟩ : syracuseStep 3243959 = 4865939) B4865939
theorem B2162639 : Blo 1997435 2162639 := bstep (se 1 (by rfl) ⟨1621979, by rfl⟩ : syracuseStep 2162639 = 3243959) B3243959
theorem B5767037 : Blo 1997435 5767037 := bstep (se 3 (by rfl) ⟨1081319, by rfl⟩ : syracuseStep 5767037 = 2162639) B2162639
theorem B3844691 : Blo 1997435 3844691 := bstep (se 1 (by rfl) ⟨2883518, by rfl⟩ : syracuseStep 3844691 = 5767037) B5767037
theorem B2563127 : Blo 1997435 2563127 := bstep (se 1 (by rfl) ⟨1922345, by rfl⟩ : syracuseStep 2563127 = 3844691) B3844691
theorem B27340021 : Blo 1997435 27340021 := bstep (se 5 (by rfl) ⟨1281563, by rfl⟩ : syracuseStep 27340021 = 2563127) B2563127
theorem B36453361 : Blo 1997435 36453361 := bstep (se 2 (by rfl) ⟨13670010, by rfl⟩ : syracuseStep 36453361 = 27340021) B27340021
theorem B48604481 : Blo 1997435 48604481 := bstep (se 2 (by rfl) ⟨18226680, by rfl⟩ : syracuseStep 48604481 = 36453361) B36453361
theorem B32402987 : Blo 1997435 32402987 := bstep (se 1 (by rfl) ⟨24302240, by rfl⟩ : syracuseStep 32402987 = 48604481) B48604481
theorem B21601991 : Blo 1997435 21601991 := bstep (se 1 (by rfl) ⟨16201493, by rfl⟩ : syracuseStep 21601991 = 32402987) B32402987
theorem B14401327 : Blo 1997435 14401327 := bstep (se 1 (by rfl) ⟨10800995, by rfl⟩ : syracuseStep 14401327 = 21601991) B21601991
theorem B19201769 : Blo 1997435 19201769 := bstep (se 2 (by rfl) ⟨7200663, by rfl⟩ : syracuseStep 19201769 = 14401327) B14401327
theorem B12801179 : Blo 1997435 12801179 := bstep (se 1 (by rfl) ⟨9600884, by rfl⟩ : syracuseStep 12801179 = 19201769) B19201769
theorem B8534119 : Blo 1997435 8534119 := bstep (se 1 (by rfl) ⟨6400589, by rfl⟩ : syracuseStep 8534119 = 12801179) B12801179
theorem B11378825 : Blo 1997435 11378825 := bstep (se 2 (by rfl) ⟨4267059, by rfl⟩ : syracuseStep 11378825 = 8534119) B8534119
theorem B7585883 : Blo 1997435 7585883 := bstep (se 1 (by rfl) ⟨5689412, by rfl⟩ : syracuseStep 7585883 = 11378825) B11378825
theorem B5057255 : Blo 1997435 5057255 := bstep (se 1 (by rfl) ⟨3792941, by rfl⟩ : syracuseStep 5057255 = 7585883) B7585883
theorem B3371503 : Blo 1997435 3371503 := bstep (se 1 (by rfl) ⟨2528627, by rfl⟩ : syracuseStep 3371503 = 5057255) B5057255
theorem B4495337 : Blo 1997435 4495337 := bstep (se 2 (by rfl) ⟨1685751, by rfl⟩ : syracuseStep 4495337 = 3371503) B3371503
theorem B2996891 : Blo 1997435 2996891 := bstep (se 1 (by rfl) ⟨2247668, by rfl⟩ : syracuseStep 2996891 = 4495337) B4495337
theorem B1997927 : Blo 1997435 1997927 := bstep (se 1 (by rfl) ⟨1498445, by rfl⟩ : syracuseStep 1997927 = 2996891) B2996891
theorem B2247673 : Blo 1997435 2247673 := bbase (se 2 (by rfl) ⟨842877, by rfl⟩ : syracuseStep 2247673 = 1685755) (by norm_num)
theorem B2996897 : Blo 1997435 2996897 := bstep (se 2 (by rfl) ⟨1123836, by rfl⟩ : syracuseStep 2996897 = 2247673) B2247673
theorem B1997931 : Blo 1997435 1997931 := bstep (se 1 (by rfl) ⟨1498448, by rfl⟩ : syracuseStep 1997931 = 2996897) B2996897
theorem B7689413 : Blo 1997435 7689413 := bbase (se 4 (by rfl) ⟨720882, by rfl⟩ : syracuseStep 7689413 = 1441765) (by norm_num)
theorem B5126275 : Blo 1997435 5126275 := bstep (se 1 (by rfl) ⟨3844706, by rfl⟩ : syracuseStep 5126275 = 7689413) B7689413
theorem B6835033 : Blo 1997435 6835033 := bstep (se 2 (by rfl) ⟨2563137, by rfl⟩ : syracuseStep 6835033 = 5126275) B5126275
theorem B36453509 : Blo 1997435 36453509 := bstep (se 4 (by rfl) ⟨3417516, by rfl⟩ : syracuseStep 36453509 = 6835033) B6835033
theorem B24302339 : Blo 1997435 24302339 := bstep (se 1 (by rfl) ⟨18226754, by rfl⟩ : syracuseStep 24302339 = 36453509) B36453509
theorem B16201559 : Blo 1997435 16201559 := bstep (se 1 (by rfl) ⟨12151169, by rfl⟩ : syracuseStep 16201559 = 24302339) B24302339
theorem B10801039 : Blo 1997435 10801039 := bstep (se 1 (by rfl) ⟨8100779, by rfl⟩ : syracuseStep 10801039 = 16201559) B16201559
theorem B14401385 : Blo 1997435 14401385 := bstep (se 2 (by rfl) ⟨5400519, by rfl⟩ : syracuseStep 14401385 = 10801039) B10801039
theorem B9600923 : Blo 1997435 9600923 := bstep (se 1 (by rfl) ⟨7200692, by rfl⟩ : syracuseStep 9600923 = 14401385) B14401385
theorem B6400615 : Blo 1997435 6400615 := bstep (se 1 (by rfl) ⟨4800461, by rfl⟩ : syracuseStep 6400615 = 9600923) B9600923
theorem B8534153 : Blo 1997435 8534153 := bstep (se 2 (by rfl) ⟨3200307, by rfl⟩ : syracuseStep 8534153 = 6400615) B6400615
theorem B5689435 : Blo 1997435 5689435 := bstep (se 1 (by rfl) ⟨4267076, by rfl⟩ : syracuseStep 5689435 = 8534153) B8534153
theorem B7585913 : Blo 1997435 7585913 := bstep (se 2 (by rfl) ⟨2844717, by rfl⟩ : syracuseStep 7585913 = 5689435) B5689435
theorem B5057275 : Blo 1997435 5057275 := bstep (se 1 (by rfl) ⟨3792956, by rfl⟩ : syracuseStep 5057275 = 7585913) B7585913
theorem B6743033 : Blo 1997435 6743033 := bstep (se 2 (by rfl) ⟨2528637, by rfl⟩ : syracuseStep 6743033 = 5057275) B5057275
theorem B4495355 : Blo 1997435 4495355 := bstep (se 1 (by rfl) ⟨3371516, by rfl⟩ : syracuseStep 4495355 = 6743033) B6743033
theorem B2996903 : Blo 1997435 2996903 := bstep (se 1 (by rfl) ⟨2247677, by rfl⟩ : syracuseStep 2996903 = 4495355) B4495355
theorem B1997935 : Blo 1997435 1997935 := bstep (se 1 (by rfl) ⟨1498451, by rfl⟩ : syracuseStep 1997935 = 2996903) B2996903
theorem B2996909 : Blo 1997435 2996909 := bbase (se 3 (by rfl) ⟨561920, by rfl⟩ : syracuseStep 2996909 = 1123841) (by norm_num)
theorem B1997939 : Blo 1997435 1997939 := bstep (se 1 (by rfl) ⟨1498454, by rfl⟩ : syracuseStep 1997939 = 2996909) B2996909
theorem B4495373 : Blo 1997435 4495373 := bbase (se 3 (by rfl) ⟨842882, by rfl⟩ : syracuseStep 4495373 = 1685765) (by norm_num)
theorem B2996915 : Blo 1997435 2996915 := bstep (se 1 (by rfl) ⟨2247686, by rfl⟩ : syracuseStep 2996915 = 4495373) B4495373
theorem B1997943 : Blo 1997435 1997943 := bstep (se 1 (by rfl) ⟨1498457, by rfl⟩ : syracuseStep 1997943 = 2996915) B2996915
theorem B2528653 : Blo 1997435 2528653 := bbase (se 3 (by rfl) ⟨474122, by rfl⟩ : syracuseStep 2528653 = 948245) (by norm_num)
theorem B3371537 : Blo 1997435 3371537 := bstep (se 2 (by rfl) ⟨1264326, by rfl⟩ : syracuseStep 3371537 = 2528653) B2528653
theorem B2247691 : Blo 1997435 2247691 := bstep (se 1 (by rfl) ⟨1685768, by rfl⟩ : syracuseStep 2247691 = 3371537) B3371537
theorem B2996921 : Blo 1997435 2996921 := bstep (se 2 (by rfl) ⟨1123845, by rfl⟩ : syracuseStep 2996921 = 2247691) B2247691
theorem B1997947 : Blo 1997435 1997947 := bstep (se 1 (by rfl) ⟨1498460, by rfl⟩ : syracuseStep 1997947 = 2996921) B2996921
theorem B5767109 : Blo 1997435 5767109 := bbase (se 4 (by rfl) ⟨540666, by rfl⟩ : syracuseStep 5767109 = 1081333) (by norm_num)
theorem B3844739 : Blo 1997435 3844739 := bstep (se 1 (by rfl) ⟨2883554, by rfl⟩ : syracuseStep 3844739 = 5767109) B5767109
theorem B2563159 : Blo 1997435 2563159 := bstep (se 1 (by rfl) ⟨1922369, by rfl⟩ : syracuseStep 2563159 = 3844739) B3844739
theorem B3417545 : Blo 1997435 3417545 := bstep (se 2 (by rfl) ⟨1281579, by rfl⟩ : syracuseStep 3417545 = 2563159) B2563159
theorem B2278363 : Blo 1997435 2278363 := bstep (se 1 (by rfl) ⟨1708772, by rfl⟩ : syracuseStep 2278363 = 3417545) B3417545
theorem B3037817 : Blo 1997435 3037817 := bstep (se 2 (by rfl) ⟨1139181, by rfl⟩ : syracuseStep 3037817 = 2278363) B2278363
theorem B2025211 : Blo 1997435 2025211 := bstep (se 1 (by rfl) ⟨1518908, by rfl⟩ : syracuseStep 2025211 = 3037817) B3037817
theorem B2700281 : Blo 1997435 2700281 := bstep (se 2 (by rfl) ⟨1012605, by rfl⟩ : syracuseStep 2700281 = 2025211) B2025211
theorem B7200749 : Blo 1997435 7200749 := bstep (se 3 (by rfl) ⟨1350140, by rfl⟩ : syracuseStep 7200749 = 2700281) B2700281
theorem B19201997 : Blo 1997435 19201997 := bstep (se 3 (by rfl) ⟨3600374, by rfl⟩ : syracuseStep 19201997 = 7200749) B7200749
theorem B12801331 : Blo 1997435 12801331 := bstep (se 1 (by rfl) ⟨9600998, by rfl⟩ : syracuseStep 12801331 = 19201997) B19201997
theorem B17068441 : Blo 1997435 17068441 := bstep (se 2 (by rfl) ⟨6400665, by rfl⟩ : syracuseStep 17068441 = 12801331) B12801331
theorem B22757921 : Blo 1997435 22757921 := bstep (se 2 (by rfl) ⟨8534220, by rfl⟩ : syracuseStep 22757921 = 17068441) B17068441
theorem B15171947 : Blo 1997435 15171947 := bstep (se 1 (by rfl) ⟨11378960, by rfl⟩ : syracuseStep 15171947 = 22757921) B22757921
theorem B10114631 : Blo 1997435 10114631 := bstep (se 1 (by rfl) ⟨7585973, by rfl⟩ : syracuseStep 10114631 = 15171947) B15171947
theorem B6743087 : Blo 1997435 6743087 := bstep (se 1 (by rfl) ⟨5057315, by rfl⟩ : syracuseStep 6743087 = 10114631) B10114631
theorem B4495391 : Blo 1997435 4495391 := bstep (se 1 (by rfl) ⟨3371543, by rfl⟩ : syracuseStep 4495391 = 6743087) B6743087
theorem B2996927 : Blo 1997435 2996927 := bstep (se 1 (by rfl) ⟨2247695, by rfl⟩ : syracuseStep 2996927 = 4495391) B4495391
theorem B1997951 : Blo 1997435 1997951 := bstep (se 1 (by rfl) ⟨1498463, by rfl⟩ : syracuseStep 1997951 = 2996927) B2996927
theorem B2996933 : Blo 1997435 2996933 := bbase (se 4 (by rfl) ⟨280962, by rfl⟩ : syracuseStep 2996933 = 561925) (by norm_num)
theorem B1997955 : Blo 1997435 1997955 := bstep (se 1 (by rfl) ⟨1498466, by rfl⟩ : syracuseStep 1997955 = 2996933) B2996933
theorem B3371557 : Blo 1997435 3371557 := bbase (se 4 (by rfl) ⟨316083, by rfl⟩ : syracuseStep 3371557 = 632167) (by norm_num)
theorem B4495409 : Blo 1997435 4495409 := bstep (se 2 (by rfl) ⟨1685778, by rfl⟩ : syracuseStep 4495409 = 3371557) B3371557
theorem B2996939 : Blo 1997435 2996939 := bstep (se 1 (by rfl) ⟨2247704, by rfl⟩ : syracuseStep 2996939 = 4495409) B4495409
theorem B1997959 : Blo 1997435 1997959 := bstep (se 1 (by rfl) ⟨1498469, by rfl⟩ : syracuseStep 1997959 = 2996939) B2996939
theorem B2247709 : Blo 1997435 2247709 := bbase (se 3 (by rfl) ⟨421445, by rfl⟩ : syracuseStep 2247709 = 842891) (by norm_num)
theorem B2996945 : Blo 1997435 2996945 := bstep (se 2 (by rfl) ⟨1123854, by rfl⟩ : syracuseStep 2996945 = 2247709) B2247709
theorem B1997963 : Blo 1997435 1997963 := bstep (se 1 (by rfl) ⟨1498472, by rfl⟩ : syracuseStep 1997963 = 2996945) B2996945
theorem B6743141 : Blo 1997435 6743141 := bbase (se 4 (by rfl) ⟨632169, by rfl⟩ : syracuseStep 6743141 = 1264339) (by norm_num)
theorem B4495427 : Blo 1997435 4495427 := bstep (se 1 (by rfl) ⟨3371570, by rfl⟩ : syracuseStep 4495427 = 6743141) B6743141
theorem B2996951 : Blo 1997435 2996951 := bstep (se 1 (by rfl) ⟨2247713, by rfl⟩ : syracuseStep 2996951 = 4495427) B4495427
theorem B1997967 : Blo 1997435 1997967 := bstep (se 1 (by rfl) ⟨1498475, by rfl⟩ : syracuseStep 1997967 = 2996951) B2996951
theorem B2996957 : Blo 1997435 2996957 := bbase (se 3 (by rfl) ⟨561929, by rfl⟩ : syracuseStep 2996957 = 1123859) (by norm_num)
theorem B1997971 : Blo 1997435 1997971 := bstep (se 1 (by rfl) ⟨1498478, by rfl⟩ : syracuseStep 1997971 = 2996957) B2996957
theorem B4495445 : Blo 1997435 4495445 := bbase (se 8 (by rfl) ⟨26340, by rfl⟩ : syracuseStep 4495445 = 52681) (by norm_num)
theorem B2996963 : Blo 1997435 2996963 := bstep (se 1 (by rfl) ⟨2247722, by rfl⟩ : syracuseStep 2996963 = 4495445) B4495445
theorem B1997975 : Blo 1997435 1997975 := bstep (se 1 (by rfl) ⟨1498481, by rfl⟩ : syracuseStep 1997975 = 2996963) B2996963
theorem B6400757 : Blo 1997435 6400757 := bbase (se 5 (by rfl) ⟨300035, by rfl⟩ : syracuseStep 6400757 = 600071) (by norm_num)
theorem B4267171 : Blo 1997435 4267171 := bstep (se 1 (by rfl) ⟨3200378, by rfl⟩ : syracuseStep 4267171 = 6400757) B6400757
theorem B5689561 : Blo 1997435 5689561 := bstep (se 2 (by rfl) ⟨2133585, by rfl⟩ : syracuseStep 5689561 = 4267171) B4267171
theorem B7586081 : Blo 1997435 7586081 := bstep (se 2 (by rfl) ⟨2844780, by rfl⟩ : syracuseStep 7586081 = 5689561) B5689561
theorem B5057387 : Blo 1997435 5057387 := bstep (se 1 (by rfl) ⟨3793040, by rfl⟩ : syracuseStep 5057387 = 7586081) B7586081
theorem B3371591 : Blo 1997435 3371591 := bstep (se 1 (by rfl) ⟨2528693, by rfl⟩ : syracuseStep 3371591 = 5057387) B5057387
theorem B2247727 : Blo 1997435 2247727 := bstep (se 1 (by rfl) ⟨1685795, by rfl⟩ : syracuseStep 2247727 = 3371591) B3371591
theorem B2996969 : Blo 1997435 2996969 := bstep (se 2 (by rfl) ⟨1123863, by rfl⟩ : syracuseStep 2996969 = 2247727) B2247727
theorem B1997979 : Blo 1997435 1997979 := bstep (se 1 (by rfl) ⟨1498484, by rfl⟩ : syracuseStep 1997979 = 2996969) B2996969
theorem B3800981 : Blo 1997435 3800981 := bbase (se 6 (by rfl) ⟨89085, by rfl⟩ : syracuseStep 3800981 = 178171) (by norm_num)
theorem B2533987 : Blo 1997435 2533987 := bstep (se 1 (by rfl) ⟨1900490, by rfl⟩ : syracuseStep 2533987 = 3800981) B3800981
theorem B3378649 : Blo 1997435 3378649 := bstep (se 2 (by rfl) ⟨1266993, by rfl⟩ : syracuseStep 3378649 = 2533987) B2533987
theorem B4504865 : Blo 1997435 4504865 := bstep (se 2 (by rfl) ⟨1689324, by rfl⟩ : syracuseStep 4504865 = 3378649) B3378649
theorem B48051893 : Blo 1997435 48051893 := bstep (se 5 (by rfl) ⟨2252432, by rfl⟩ : syracuseStep 48051893 = 4504865) B4504865
theorem B128138381 : Blo 1997435 128138381 := bstep (se 3 (by rfl) ⟨24025946, by rfl⟩ : syracuseStep 128138381 = 48051893) B48051893
theorem B85425587 : Blo 1997435 85425587 := bstep (se 1 (by rfl) ⟨64069190, by rfl⟩ : syracuseStep 85425587 = 128138381) B128138381
theorem B56950391 : Blo 1997435 56950391 := bstep (se 1 (by rfl) ⟨42712793, by rfl⟩ : syracuseStep 56950391 = 85425587) B85425587
theorem B37966927 : Blo 1997435 37966927 := bstep (se 1 (by rfl) ⟨28475195, by rfl⟩ : syracuseStep 37966927 = 56950391) B56950391
theorem B50622569 : Blo 1997435 50622569 := bstep (se 2 (by rfl) ⟨18983463, by rfl⟩ : syracuseStep 50622569 = 37966927) B37966927
theorem B33748379 : Blo 1997435 33748379 := bstep (se 1 (by rfl) ⟨25311284, by rfl⟩ : syracuseStep 33748379 = 50622569) B50622569
theorem B22498919 : Blo 1997435 22498919 := bstep (se 1 (by rfl) ⟨16874189, by rfl⟩ : syracuseStep 22498919 = 33748379) B33748379
theorem B14999279 : Blo 1997435 14999279 := bstep (se 1 (by rfl) ⟨11249459, by rfl⟩ : syracuseStep 14999279 = 22498919) B22498919
theorem B159992309 : Blo 1997435 159992309 := bstep (se 5 (by rfl) ⟨7499639, by rfl⟩ : syracuseStep 159992309 = 14999279) B14999279
theorem B106661539 : Blo 1997435 106661539 := bstep (se 1 (by rfl) ⟨79996154, by rfl⟩ : syracuseStep 106661539 = 159992309) B159992309
theorem B568861541 : Blo 1997435 568861541 := bstep (se 4 (by rfl) ⟨53330769, by rfl⟩ : syracuseStep 568861541 = 106661539) B106661539
theorem B379241027 : Blo 1997435 379241027 := bstep (se 1 (by rfl) ⟨284430770, by rfl⟩ : syracuseStep 379241027 = 568861541) B568861541
theorem B252827351 : Blo 1997435 252827351 := bstep (se 1 (by rfl) ⟨189620513, by rfl⟩ : syracuseStep 252827351 = 379241027) B379241027
theorem B168551567 : Blo 1997435 168551567 := bstep (se 1 (by rfl) ⟨126413675, by rfl⟩ : syracuseStep 168551567 = 252827351) B252827351
theorem B112367711 : Blo 1997435 112367711 := bstep (se 1 (by rfl) ⟨84275783, by rfl⟩ : syracuseStep 112367711 = 168551567) B168551567
theorem B74911807 : Blo 1997435 74911807 := bstep (se 1 (by rfl) ⟨56183855, by rfl⟩ : syracuseStep 74911807 = 112367711) B112367711
theorem B99882409 : Blo 1997435 99882409 := bstep (se 2 (by rfl) ⟨37455903, by rfl⟩ : syracuseStep 99882409 = 74911807) B74911807
theorem B133176545 : Blo 1997435 133176545 := bstep (se 2 (by rfl) ⟨49941204, by rfl⟩ : syracuseStep 133176545 = 99882409) B99882409
theorem B88784363 : Blo 1997435 88784363 := bstep (se 1 (by rfl) ⟨66588272, by rfl⟩ : syracuseStep 88784363 = 133176545) B133176545
theorem B236758301 : Blo 1997435 236758301 := bstep (se 3 (by rfl) ⟨44392181, by rfl⟩ : syracuseStep 236758301 = 88784363) B88784363
theorem B157838867 : Blo 1997435 157838867 := bstep (se 1 (by rfl) ⟨118379150, by rfl⟩ : syracuseStep 157838867 = 236758301) B236758301
theorem B105225911 : Blo 1997435 105225911 := bstep (se 1 (by rfl) ⟨78919433, by rfl⟩ : syracuseStep 105225911 = 157838867) B157838867
theorem B70150607 : Blo 1997435 70150607 := bstep (se 1 (by rfl) ⟨52612955, by rfl⟩ : syracuseStep 70150607 = 105225911) B105225911
theorem B46767071 : Blo 1997435 46767071 := bstep (se 1 (by rfl) ⟨35075303, by rfl⟩ : syracuseStep 46767071 = 70150607) B70150607
theorem B31178047 : Blo 1997435 31178047 := bstep (se 1 (by rfl) ⟨23383535, by rfl⟩ : syracuseStep 31178047 = 46767071) B46767071
theorem B41570729 : Blo 1997435 41570729 := bstep (se 2 (by rfl) ⟨15589023, by rfl⟩ : syracuseStep 41570729 = 31178047) B31178047
theorem B27713819 : Blo 1997435 27713819 := bstep (se 1 (by rfl) ⟨20785364, by rfl⟩ : syracuseStep 27713819 = 41570729) B41570729
theorem B18475879 : Blo 1997435 18475879 := bstep (se 1 (by rfl) ⟨13856909, by rfl⟩ : syracuseStep 18475879 = 27713819) B27713819
theorem B24634505 : Blo 1997435 24634505 := bstep (se 2 (by rfl) ⟨9237939, by rfl⟩ : syracuseStep 24634505 = 18475879) B18475879
theorem B16423003 : Blo 1997435 16423003 := bstep (se 1 (by rfl) ⟨12317252, by rfl⟩ : syracuseStep 16423003 = 24634505) B24634505
theorem B87589349 : Blo 1997435 87589349 := bstep (se 4 (by rfl) ⟨8211501, by rfl⟩ : syracuseStep 87589349 = 16423003) B16423003
theorem B58392899 : Blo 1997435 58392899 := bstep (se 1 (by rfl) ⟨43794674, by rfl⟩ : syracuseStep 58392899 = 87589349) B87589349
theorem B38928599 : Blo 1997435 38928599 := bstep (se 1 (by rfl) ⟨29196449, by rfl⟩ : syracuseStep 38928599 = 58392899) B58392899
theorem B25952399 : Blo 1997435 25952399 := bstep (se 1 (by rfl) ⟨19464299, by rfl⟩ : syracuseStep 25952399 = 38928599) B38928599
theorem B17301599 : Blo 1997435 17301599 := bstep (se 1 (by rfl) ⟨12976199, by rfl⟩ : syracuseStep 17301599 = 25952399) B25952399
theorem B11534399 : Blo 1997435 11534399 := bstep (se 1 (by rfl) ⟨8650799, by rfl⟩ : syracuseStep 11534399 = 17301599) B17301599
theorem B7689599 : Blo 1997435 7689599 := bstep (se 1 (by rfl) ⟨5767199, by rfl⟩ : syracuseStep 7689599 = 11534399) B11534399
theorem B5126399 : Blo 1997435 5126399 := bstep (se 1 (by rfl) ⟨3844799, by rfl⟩ : syracuseStep 5126399 = 7689599) B7689599
theorem B3417599 : Blo 1997435 3417599 := bstep (se 1 (by rfl) ⟨2563199, by rfl⟩ : syracuseStep 3417599 = 5126399) B5126399
theorem B2278399 : Blo 1997435 2278399 := bstep (se 1 (by rfl) ⟨1708799, by rfl⟩ : syracuseStep 2278399 = 3417599) B3417599
theorem B3037865 : Blo 1997435 3037865 := bstep (se 2 (by rfl) ⟨1139199, by rfl⟩ : syracuseStep 3037865 = 2278399) B2278399
theorem B8100973 : Blo 1997435 8100973 := bstep (se 3 (by rfl) ⟨1518932, by rfl⟩ : syracuseStep 8100973 = 3037865) B3037865
theorem B10801297 : Blo 1997435 10801297 := bstep (se 2 (by rfl) ⟨4050486, by rfl⟩ : syracuseStep 10801297 = 8100973) B8100973
theorem B14401729 : Blo 1997435 14401729 := bstep (se 2 (by rfl) ⟨5400648, by rfl⟩ : syracuseStep 14401729 = 10801297) B10801297
theorem B19202305 : Blo 1997435 19202305 := bstep (se 2 (by rfl) ⟨7200864, by rfl⟩ : syracuseStep 19202305 = 14401729) B14401729
theorem B25603073 : Blo 1997435 25603073 := bstep (se 2 (by rfl) ⟨9601152, by rfl⟩ : syracuseStep 25603073 = 19202305) B19202305
theorem B17068715 : Blo 1997435 17068715 := bstep (se 1 (by rfl) ⟨12801536, by rfl⟩ : syracuseStep 17068715 = 25603073) B25603073
theorem B11379143 : Blo 1997435 11379143 := bstep (se 1 (by rfl) ⟨8534357, by rfl⟩ : syracuseStep 11379143 = 17068715) B17068715
theorem B7586095 : Blo 1997435 7586095 := bstep (se 1 (by rfl) ⟨5689571, by rfl⟩ : syracuseStep 7586095 = 11379143) B11379143
theorem B10114793 : Blo 1997435 10114793 := bstep (se 2 (by rfl) ⟨3793047, by rfl⟩ : syracuseStep 10114793 = 7586095) B7586095
theorem B6743195 : Blo 1997435 6743195 := bstep (se 1 (by rfl) ⟨5057396, by rfl⟩ : syracuseStep 6743195 = 10114793) B10114793
theorem B4495463 : Blo 1997435 4495463 := bstep (se 1 (by rfl) ⟨3371597, by rfl⟩ : syracuseStep 4495463 = 6743195) B6743195
theorem B2996975 : Blo 1997435 2996975 := bstep (se 1 (by rfl) ⟨2247731, by rfl⟩ : syracuseStep 2996975 = 4495463) B4495463
theorem B1997983 : Blo 1997435 1997983 := bstep (se 1 (by rfl) ⟨1498487, by rfl⟩ : syracuseStep 1997983 = 2996975) B2996975
theorem B2996981 : Blo 1997435 2996981 := bbase (se 5 (by rfl) ⟨140483, by rfl⟩ : syracuseStep 2996981 = 280967) (by norm_num)
theorem B1997987 : Blo 1997435 1997987 := bstep (se 1 (by rfl) ⟨1498490, by rfl⟩ : syracuseStep 1997987 = 2996981) B2996981
theorem B4932485 : Blo 1997435 4932485 := bbase (se 4 (by rfl) ⟨462420, by rfl⟩ : syracuseStep 4932485 = 924841) (by norm_num)
theorem B3288323 : Blo 1997435 3288323 := bstep (se 1 (by rfl) ⟨2466242, by rfl⟩ : syracuseStep 3288323 = 4932485) B4932485
theorem B2192215 : Blo 1997435 2192215 := bstep (se 1 (by rfl) ⟨1644161, by rfl⟩ : syracuseStep 2192215 = 3288323) B3288323
theorem B46767253 : Blo 1997435 46767253 := bstep (se 6 (by rfl) ⟨1096107, by rfl⟩ : syracuseStep 46767253 = 2192215) B2192215
theorem B62356337 : Blo 1997435 62356337 := bstep (se 2 (by rfl) ⟨23383626, by rfl⟩ : syracuseStep 62356337 = 46767253) B46767253
theorem B41570891 : Blo 1997435 41570891 := bstep (se 1 (by rfl) ⟨31178168, by rfl⟩ : syracuseStep 41570891 = 62356337) B62356337
theorem B27713927 : Blo 1997435 27713927 := bstep (se 1 (by rfl) ⟨20785445, by rfl⟩ : syracuseStep 27713927 = 41570891) B41570891
theorem B18475951 : Blo 1997435 18475951 := bstep (se 1 (by rfl) ⟨13856963, by rfl⟩ : syracuseStep 18475951 = 27713927) B27713927
theorem B24634601 : Blo 1997435 24634601 := bstep (se 2 (by rfl) ⟨9237975, by rfl⟩ : syracuseStep 24634601 = 18475951) B18475951
theorem B16423067 : Blo 1997435 16423067 := bstep (se 1 (by rfl) ⟨12317300, by rfl⟩ : syracuseStep 16423067 = 24634601) B24634601
theorem B10948711 : Blo 1997435 10948711 := bstep (se 1 (by rfl) ⟨8211533, by rfl⟩ : syracuseStep 10948711 = 16423067) B16423067
theorem B14598281 : Blo 1997435 14598281 := bstep (se 2 (by rfl) ⟨5474355, by rfl⟩ : syracuseStep 14598281 = 10948711) B10948711
theorem B9732187 : Blo 1997435 9732187 := bstep (se 1 (by rfl) ⟨7299140, by rfl⟩ : syracuseStep 9732187 = 14598281) B14598281
theorem B12976249 : Blo 1997435 12976249 := bstep (se 2 (by rfl) ⟨4866093, by rfl⟩ : syracuseStep 12976249 = 9732187) B9732187
theorem B17301665 : Blo 1997435 17301665 := bstep (se 2 (by rfl) ⟨6488124, by rfl⟩ : syracuseStep 17301665 = 12976249) B12976249
theorem B11534443 : Blo 1997435 11534443 := bstep (se 1 (by rfl) ⟨8650832, by rfl⟩ : syracuseStep 11534443 = 17301665) B17301665
theorem B61517029 : Blo 1997435 61517029 := bstep (se 4 (by rfl) ⟨5767221, by rfl⟩ : syracuseStep 61517029 = 11534443) B11534443
theorem B82022705 : Blo 1997435 82022705 := bstep (se 2 (by rfl) ⟨30758514, by rfl⟩ : syracuseStep 82022705 = 61517029) B61517029
theorem B54681803 : Blo 1997435 54681803 := bstep (se 1 (by rfl) ⟨41011352, by rfl⟩ : syracuseStep 54681803 = 82022705) B82022705
theorem B36454535 : Blo 1997435 36454535 := bstep (se 1 (by rfl) ⟨27340901, by rfl⟩ : syracuseStep 36454535 = 54681803) B54681803
theorem B24303023 : Blo 1997435 24303023 := bstep (se 1 (by rfl) ⟨18227267, by rfl⟩ : syracuseStep 24303023 = 36454535) B36454535
theorem B16202015 : Blo 1997435 16202015 := bstep (se 1 (by rfl) ⟨12151511, by rfl⟩ : syracuseStep 16202015 = 24303023) B24303023
theorem B10801343 : Blo 1997435 10801343 := bstep (se 1 (by rfl) ⟨8101007, by rfl⟩ : syracuseStep 10801343 = 16202015) B16202015
theorem B7200895 : Blo 1997435 7200895 := bstep (se 1 (by rfl) ⟨5400671, by rfl⟩ : syracuseStep 7200895 = 10801343) B10801343
theorem B9601193 : Blo 1997435 9601193 := bstep (se 2 (by rfl) ⟨3600447, by rfl⟩ : syracuseStep 9601193 = 7200895) B7200895
theorem B6400795 : Blo 1997435 6400795 := bstep (se 1 (by rfl) ⟨4800596, by rfl⟩ : syracuseStep 6400795 = 9601193) B9601193
theorem B8534393 : Blo 1997435 8534393 := bstep (se 2 (by rfl) ⟨3200397, by rfl⟩ : syracuseStep 8534393 = 6400795) B6400795
theorem B5689595 : Blo 1997435 5689595 := bstep (se 1 (by rfl) ⟨4267196, by rfl⟩ : syracuseStep 5689595 = 8534393) B8534393
theorem B3793063 : Blo 1997435 3793063 := bstep (se 1 (by rfl) ⟨2844797, by rfl⟩ : syracuseStep 3793063 = 5689595) B5689595
theorem B5057417 : Blo 1997435 5057417 := bstep (se 2 (by rfl) ⟨1896531, by rfl⟩ : syracuseStep 5057417 = 3793063) B3793063
theorem B3371611 : Blo 1997435 3371611 := bstep (se 1 (by rfl) ⟨2528708, by rfl⟩ : syracuseStep 3371611 = 5057417) B5057417
theorem B4495481 : Blo 1997435 4495481 := bstep (se 2 (by rfl) ⟨1685805, by rfl⟩ : syracuseStep 4495481 = 3371611) B3371611
theorem B2996987 : Blo 1997435 2996987 := bstep (se 1 (by rfl) ⟨2247740, by rfl⟩ : syracuseStep 2996987 = 4495481) B4495481
theorem B1997991 : Blo 1997435 1997991 := bstep (se 1 (by rfl) ⟨1498493, by rfl⟩ : syracuseStep 1997991 = 2996987) B2996987
theorem B2247745 : Blo 1997435 2247745 := bbase (se 2 (by rfl) ⟨842904, by rfl⟩ : syracuseStep 2247745 = 1685809) (by norm_num)
theorem B2996993 : Blo 1997435 2996993 := bstep (se 2 (by rfl) ⟨1123872, by rfl⟩ : syracuseStep 2996993 = 2247745) B2247745
theorem B1997995 : Blo 1997435 1997995 := bstep (se 1 (by rfl) ⟨1498496, by rfl⟩ : syracuseStep 1997995 = 2996993) B2996993
theorem B5057437 : Blo 1997435 5057437 := bbase (se 3 (by rfl) ⟨948269, by rfl⟩ : syracuseStep 5057437 = 1896539) (by norm_num)
theorem B6743249 : Blo 1997435 6743249 := bstep (se 2 (by rfl) ⟨2528718, by rfl⟩ : syracuseStep 6743249 = 5057437) B5057437
theorem B4495499 : Blo 1997435 4495499 := bstep (se 1 (by rfl) ⟨3371624, by rfl⟩ : syracuseStep 4495499 = 6743249) B6743249
theorem B2996999 : Blo 1997435 2996999 := bstep (se 1 (by rfl) ⟨2247749, by rfl⟩ : syracuseStep 2996999 = 4495499) B4495499
theorem B1997999 : Blo 1997435 1997999 := bstep (se 1 (by rfl) ⟨1498499, by rfl⟩ : syracuseStep 1997999 = 2996999) B2996999
theorem B2997005 : Blo 1997435 2997005 := bbase (se 3 (by rfl) ⟨561938, by rfl⟩ : syracuseStep 2997005 = 1123877) (by norm_num)
theorem B1998003 : Blo 1997435 1998003 := bstep (se 1 (by rfl) ⟨1498502, by rfl⟩ : syracuseStep 1998003 = 2997005) B2997005
theorem B4495517 : Blo 1997435 4495517 := bbase (se 3 (by rfl) ⟨842909, by rfl⟩ : syracuseStep 4495517 = 1685819) (by norm_num)
theorem B2997011 : Blo 1997435 2997011 := bstep (se 1 (by rfl) ⟨2247758, by rfl⟩ : syracuseStep 2997011 = 4495517) B4495517
theorem B1998007 : Blo 1997435 1998007 := bstep (se 1 (by rfl) ⟨1498505, by rfl⟩ : syracuseStep 1998007 = 2997011) B2997011
theorem B3371645 : Blo 1997435 3371645 := bbase (se 3 (by rfl) ⟨632183, by rfl⟩ : syracuseStep 3371645 = 1264367) (by norm_num)
theorem B2247763 : Blo 1997435 2247763 := bstep (se 1 (by rfl) ⟨1685822, by rfl⟩ : syracuseStep 2247763 = 3371645) B3371645
theorem B2997017 : Blo 1997435 2997017 := bstep (se 2 (by rfl) ⟨1123881, by rfl⟩ : syracuseStep 2997017 = 2247763) B2247763
theorem B1998011 : Blo 1997435 1998011 := bstep (se 1 (by rfl) ⟨1498508, by rfl⟩ : syracuseStep 1998011 = 2997017) B2997017
theorem B5339189 : Blo 1997435 5339189 := bbase (se 5 (by rfl) ⟨250274, by rfl⟩ : syracuseStep 5339189 = 500549) (by norm_num)
theorem B3559459 : Blo 1997435 3559459 := bstep (se 1 (by rfl) ⟨2669594, by rfl⟩ : syracuseStep 3559459 = 5339189) B5339189
theorem B4745945 : Blo 1997435 4745945 := bstep (se 2 (by rfl) ⟨1779729, by rfl⟩ : syracuseStep 4745945 = 3559459) B3559459
theorem B3163963 : Blo 1997435 3163963 := bstep (se 1 (by rfl) ⟨2372972, by rfl⟩ : syracuseStep 3163963 = 4745945) B4745945
theorem B4218617 : Blo 1997435 4218617 := bstep (se 2 (by rfl) ⟨1581981, by rfl⟩ : syracuseStep 4218617 = 3163963) B3163963
theorem B2812411 : Blo 1997435 2812411 := bstep (se 1 (by rfl) ⟨2109308, by rfl⟩ : syracuseStep 2812411 = 4218617) B4218617
theorem B14999525 : Blo 1997435 14999525 := bstep (se 4 (by rfl) ⟨1406205, by rfl⟩ : syracuseStep 14999525 = 2812411) B2812411
theorem B9999683 : Blo 1997435 9999683 := bstep (se 1 (by rfl) ⟨7499762, by rfl⟩ : syracuseStep 9999683 = 14999525) B14999525
theorem B6666455 : Blo 1997435 6666455 := bstep (se 1 (by rfl) ⟨4999841, by rfl⟩ : syracuseStep 6666455 = 9999683) B9999683
theorem B4444303 : Blo 1997435 4444303 := bstep (se 1 (by rfl) ⟨3333227, by rfl⟩ : syracuseStep 4444303 = 6666455) B6666455
theorem B5925737 : Blo 1997435 5925737 := bstep (se 2 (by rfl) ⟨2222151, by rfl⟩ : syracuseStep 5925737 = 4444303) B4444303
theorem B15801965 : Blo 1997435 15801965 := bstep (se 3 (by rfl) ⟨2962868, by rfl⟩ : syracuseStep 15801965 = 5925737) B5925737
theorem B10534643 : Blo 1997435 10534643 := bstep (se 1 (by rfl) ⟨7900982, by rfl⟩ : syracuseStep 10534643 = 15801965) B15801965
theorem B7023095 : Blo 1997435 7023095 := bstep (se 1 (by rfl) ⟨5267321, by rfl⟩ : syracuseStep 7023095 = 10534643) B10534643
theorem B4682063 : Blo 1997435 4682063 := bstep (se 1 (by rfl) ⟨3511547, by rfl⟩ : syracuseStep 4682063 = 7023095) B7023095
theorem B12485501 : Blo 1997435 12485501 := bstep (se 3 (by rfl) ⟨2341031, by rfl⟩ : syracuseStep 12485501 = 4682063) B4682063
theorem B8323667 : Blo 1997435 8323667 := bstep (se 1 (by rfl) ⟨6242750, by rfl⟩ : syracuseStep 8323667 = 12485501) B12485501
theorem B5549111 : Blo 1997435 5549111 := bstep (se 1 (by rfl) ⟨4161833, by rfl⟩ : syracuseStep 5549111 = 8323667) B8323667
theorem B3699407 : Blo 1997435 3699407 := bstep (se 1 (by rfl) ⟨2774555, by rfl⟩ : syracuseStep 3699407 = 5549111) B5549111
theorem B2466271 : Blo 1997435 2466271 := bstep (se 1 (by rfl) ⟨1849703, by rfl⟩ : syracuseStep 2466271 = 3699407) B3699407
theorem B13153445 : Blo 1997435 13153445 := bstep (se 4 (by rfl) ⟨1233135, by rfl⟩ : syracuseStep 13153445 = 2466271) B2466271
theorem B8768963 : Blo 1997435 8768963 := bstep (se 1 (by rfl) ⟨6576722, by rfl⟩ : syracuseStep 8768963 = 13153445) B13153445
theorem B5845975 : Blo 1997435 5845975 := bstep (se 1 (by rfl) ⟨4384481, by rfl⟩ : syracuseStep 5845975 = 8768963) B8768963
theorem B31178533 : Blo 1997435 31178533 := bstep (se 4 (by rfl) ⟨2922987, by rfl⟩ : syracuseStep 31178533 = 5845975) B5845975
theorem B41571377 : Blo 1997435 41571377 := bstep (se 2 (by rfl) ⟨15589266, by rfl⟩ : syracuseStep 41571377 = 31178533) B31178533
theorem B27714251 : Blo 1997435 27714251 := bstep (se 1 (by rfl) ⟨20785688, by rfl⟩ : syracuseStep 27714251 = 41571377) B41571377
theorem B73904669 : Blo 1997435 73904669 := bstep (se 3 (by rfl) ⟨13857125, by rfl⟩ : syracuseStep 73904669 = 27714251) B27714251
theorem B49269779 : Blo 1997435 49269779 := bstep (se 1 (by rfl) ⟨36952334, by rfl⟩ : syracuseStep 49269779 = 73904669) B73904669
theorem B32846519 : Blo 1997435 32846519 := bstep (se 1 (by rfl) ⟨24634889, by rfl⟩ : syracuseStep 32846519 = 49269779) B49269779
theorem B87590717 : Blo 1997435 87590717 := bstep (se 3 (by rfl) ⟨16423259, by rfl⟩ : syracuseStep 87590717 = 32846519) B32846519
theorem B58393811 : Blo 1997435 58393811 := bstep (se 1 (by rfl) ⟨43795358, by rfl⟩ : syracuseStep 58393811 = 87590717) B87590717
theorem B155716829 : Blo 1997435 155716829 := bstep (se 3 (by rfl) ⟨29196905, by rfl⟩ : syracuseStep 155716829 = 58393811) B58393811
theorem B103811219 : Blo 1997435 103811219 := bstep (se 1 (by rfl) ⟨77858414, by rfl⟩ : syracuseStep 103811219 = 155716829) B155716829
theorem B69207479 : Blo 1997435 69207479 := bstep (se 1 (by rfl) ⟨51905609, by rfl⟩ : syracuseStep 69207479 = 103811219) B103811219
theorem B46138319 : Blo 1997435 46138319 := bstep (se 1 (by rfl) ⟨34603739, by rfl⟩ : syracuseStep 46138319 = 69207479) B69207479
theorem B30758879 : Blo 1997435 30758879 := bstep (se 1 (by rfl) ⟨23069159, by rfl⟩ : syracuseStep 30758879 = 46138319) B46138319
theorem B82023677 : Blo 1997435 82023677 := bstep (se 3 (by rfl) ⟨15379439, by rfl⟩ : syracuseStep 82023677 = 30758879) B30758879
theorem B54682451 : Blo 1997435 54682451 := bstep (se 1 (by rfl) ⟨41011838, by rfl⟩ : syracuseStep 54682451 = 82023677) B82023677
theorem B36454967 : Blo 1997435 36454967 := bstep (se 1 (by rfl) ⟨27341225, by rfl⟩ : syracuseStep 36454967 = 54682451) B54682451
theorem B24303311 : Blo 1997435 24303311 := bstep (se 1 (by rfl) ⟨18227483, by rfl⟩ : syracuseStep 24303311 = 36454967) B36454967
theorem B16202207 : Blo 1997435 16202207 := bstep (se 1 (by rfl) ⟨12151655, by rfl⟩ : syracuseStep 16202207 = 24303311) B24303311
theorem B10801471 : Blo 1997435 10801471 := bstep (se 1 (by rfl) ⟨8101103, by rfl⟩ : syracuseStep 10801471 = 16202207) B16202207
theorem B14401961 : Blo 1997435 14401961 := bstep (se 2 (by rfl) ⟨5400735, by rfl⟩ : syracuseStep 14401961 = 10801471) B10801471
theorem B9601307 : Blo 1997435 9601307 := bstep (se 1 (by rfl) ⟨7200980, by rfl⟩ : syracuseStep 9601307 = 14401961) B14401961
theorem B6400871 : Blo 1997435 6400871 := bstep (se 1 (by rfl) ⟨4800653, by rfl⟩ : syracuseStep 6400871 = 9601307) B9601307
theorem B4267247 : Blo 1997435 4267247 := bstep (se 1 (by rfl) ⟨3200435, by rfl⟩ : syracuseStep 4267247 = 6400871) B6400871
theorem B11379325 : Blo 1997435 11379325 := bstep (se 3 (by rfl) ⟨2133623, by rfl⟩ : syracuseStep 11379325 = 4267247) B4267247
theorem B15172433 : Blo 1997435 15172433 := bstep (se 2 (by rfl) ⟨5689662, by rfl⟩ : syracuseStep 15172433 = 11379325) B11379325
theorem B10114955 : Blo 1997435 10114955 := bstep (se 1 (by rfl) ⟨7586216, by rfl⟩ : syracuseStep 10114955 = 15172433) B15172433
theorem B6743303 : Blo 1997435 6743303 := bstep (se 1 (by rfl) ⟨5057477, by rfl⟩ : syracuseStep 6743303 = 10114955) B10114955
theorem B4495535 : Blo 1997435 4495535 := bstep (se 1 (by rfl) ⟨3371651, by rfl⟩ : syracuseStep 4495535 = 6743303) B6743303
theorem B2997023 : Blo 1997435 2997023 := bstep (se 1 (by rfl) ⟨2247767, by rfl⟩ : syracuseStep 2997023 = 4495535) B4495535
theorem B1998015 : Blo 1997435 1998015 := bstep (se 1 (by rfl) ⟨1498511, by rfl⟩ : syracuseStep 1998015 = 2997023) B2997023
theorem B2997029 : Blo 1997435 2997029 := bbase (se 4 (by rfl) ⟨280971, by rfl⟩ : syracuseStep 2997029 = 561943) (by norm_num)
theorem B1998019 : Blo 1997435 1998019 := bstep (se 1 (by rfl) ⟨1498514, by rfl⟩ : syracuseStep 1998019 = 2997029) B2997029
theorem B2528749 : Blo 1997435 2528749 := bbase (se 3 (by rfl) ⟨474140, by rfl⟩ : syracuseStep 2528749 = 948281) (by norm_num)
theorem B3371665 : Blo 1997435 3371665 := bstep (se 2 (by rfl) ⟨1264374, by rfl⟩ : syracuseStep 3371665 = 2528749) B2528749
theorem B4495553 : Blo 1997435 4495553 := bstep (se 2 (by rfl) ⟨1685832, by rfl⟩ : syracuseStep 4495553 = 3371665) B3371665
theorem B2997035 : Blo 1997435 2997035 := bstep (se 1 (by rfl) ⟨2247776, by rfl⟩ : syracuseStep 2997035 = 4495553) B4495553
theorem B1998023 : Blo 1997435 1998023 := bstep (se 1 (by rfl) ⟨1498517, by rfl⟩ : syracuseStep 1998023 = 2997035) B2997035
theorem B2247781 : Blo 1997435 2247781 := bbase (se 4 (by rfl) ⟨210729, by rfl⟩ : syracuseStep 2247781 = 421459) (by norm_num)
theorem B2997041 : Blo 1997435 2997041 := bstep (se 2 (by rfl) ⟨1123890, by rfl⟩ : syracuseStep 2997041 = 2247781) B2247781
theorem B1998027 : Blo 1997435 1998027 := bstep (se 1 (by rfl) ⟨1498520, by rfl⟩ : syracuseStep 1998027 = 2997041) B2997041
theorem B2133641 : Blo 1997435 2133641 := bbase (se 2 (by rfl) ⟨800115, by rfl⟩ : syracuseStep 2133641 = 1600231) (by norm_num)
theorem B5689709 : Blo 1997435 5689709 := bstep (se 3 (by rfl) ⟨1066820, by rfl⟩ : syracuseStep 5689709 = 2133641) B2133641
theorem B3793139 : Blo 1997435 3793139 := bstep (se 1 (by rfl) ⟨2844854, by rfl⟩ : syracuseStep 3793139 = 5689709) B5689709
theorem B2528759 : Blo 1997435 2528759 := bstep (se 1 (by rfl) ⟨1896569, by rfl⟩ : syracuseStep 2528759 = 3793139) B3793139
theorem B6743357 : Blo 1997435 6743357 := bstep (se 3 (by rfl) ⟨1264379, by rfl⟩ : syracuseStep 6743357 = 2528759) B2528759
theorem B4495571 : Blo 1997435 4495571 := bstep (se 1 (by rfl) ⟨3371678, by rfl⟩ : syracuseStep 4495571 = 6743357) B6743357
theorem B2997047 : Blo 1997435 2997047 := bstep (se 1 (by rfl) ⟨2247785, by rfl⟩ : syracuseStep 2997047 = 4495571) B4495571
theorem B1998031 : Blo 1997435 1998031 := bstep (se 1 (by rfl) ⟨1498523, by rfl⟩ : syracuseStep 1998031 = 2997047) B2997047
theorem B2997053 : Blo 1997435 2997053 := bbase (se 3 (by rfl) ⟨561947, by rfl⟩ : syracuseStep 2997053 = 1123895) (by norm_num)
theorem B1998035 : Blo 1997435 1998035 := bstep (se 1 (by rfl) ⟨1498526, by rfl⟩ : syracuseStep 1998035 = 2997053) B2997053
theorem B4495589 : Blo 1997435 4495589 := bbase (se 4 (by rfl) ⟨421461, by rfl⟩ : syracuseStep 4495589 = 842923) (by norm_num)
theorem B2997059 : Blo 1997435 2997059 := bstep (se 1 (by rfl) ⟨2247794, by rfl⟩ : syracuseStep 2997059 = 4495589) B4495589
theorem B1998039 : Blo 1997435 1998039 := bstep (se 1 (by rfl) ⟨1498529, by rfl⟩ : syracuseStep 1998039 = 2997059) B2997059
theorem B5057549 : Blo 1997435 5057549 := bbase (se 3 (by rfl) ⟨948290, by rfl⟩ : syracuseStep 5057549 = 1896581) (by norm_num)
theorem B3371699 : Blo 1997435 3371699 := bstep (se 1 (by rfl) ⟨2528774, by rfl⟩ : syracuseStep 3371699 = 5057549) B5057549
theorem B2247799 : Blo 1997435 2247799 := bstep (se 1 (by rfl) ⟨1685849, by rfl⟩ : syracuseStep 2247799 = 3371699) B3371699
theorem B2997065 : Blo 1997435 2997065 := bstep (se 2 (by rfl) ⟨1123899, by rfl⟩ : syracuseStep 2997065 = 2247799) B2247799
theorem B1998043 : Blo 1997435 1998043 := bstep (se 1 (by rfl) ⟨1498532, by rfl⟩ : syracuseStep 1998043 = 2997065) B2997065
theorem B2844877 : Blo 1997435 2844877 := bbase (se 3 (by rfl) ⟨533414, by rfl⟩ : syracuseStep 2844877 = 1066829) (by norm_num)
theorem B3793169 : Blo 1997435 3793169 := bstep (se 2 (by rfl) ⟨1422438, by rfl⟩ : syracuseStep 3793169 = 2844877) B2844877
theorem B10115117 : Blo 1997435 10115117 := bstep (se 3 (by rfl) ⟨1896584, by rfl⟩ : syracuseStep 10115117 = 3793169) B3793169
theorem B6743411 : Blo 1997435 6743411 := bstep (se 1 (by rfl) ⟨5057558, by rfl⟩ : syracuseStep 6743411 = 10115117) B10115117
theorem B4495607 : Blo 1997435 4495607 := bstep (se 1 (by rfl) ⟨3371705, by rfl⟩ : syracuseStep 4495607 = 6743411) B6743411
theorem B2997071 : Blo 1997435 2997071 := bstep (se 1 (by rfl) ⟨2247803, by rfl⟩ : syracuseStep 2997071 = 4495607) B4495607
theorem B1998047 : Blo 1997435 1998047 := bstep (se 1 (by rfl) ⟨1498535, by rfl⟩ : syracuseStep 1998047 = 2997071) B2997071
theorem B2997077 : Blo 1997435 2997077 := bbase (se 9 (by rfl) ⟨8780, by rfl⟩ : syracuseStep 2997077 = 17561) (by norm_num)
theorem B1998051 : Blo 1997435 1998051 := bstep (se 1 (by rfl) ⟨1498538, by rfl⟩ : syracuseStep 1998051 = 2997077) B2997077
theorem B4267333 : Blo 1997435 4267333 := bbase (se 4 (by rfl) ⟨400062, by rfl⟩ : syracuseStep 4267333 = 800125) (by norm_num)
theorem B5689777 : Blo 1997435 5689777 := bstep (se 2 (by rfl) ⟨2133666, by rfl⟩ : syracuseStep 5689777 = 4267333) B4267333
theorem B7586369 : Blo 1997435 7586369 := bstep (se 2 (by rfl) ⟨2844888, by rfl⟩ : syracuseStep 7586369 = 5689777) B5689777
theorem B5057579 : Blo 1997435 5057579 := bstep (se 1 (by rfl) ⟨3793184, by rfl⟩ : syracuseStep 5057579 = 7586369) B7586369
theorem B3371719 : Blo 1997435 3371719 := bstep (se 1 (by rfl) ⟨2528789, by rfl⟩ : syracuseStep 3371719 = 5057579) B5057579
theorem B4495625 : Blo 1997435 4495625 := bstep (se 2 (by rfl) ⟨1685859, by rfl⟩ : syracuseStep 4495625 = 3371719) B3371719
theorem B2997083 : Blo 1997435 2997083 := bstep (se 1 (by rfl) ⟨2247812, by rfl⟩ : syracuseStep 2997083 = 4495625) B4495625
theorem B1998055 : Blo 1997435 1998055 := bstep (se 1 (by rfl) ⟨1498541, by rfl⟩ : syracuseStep 1998055 = 2997083) B2997083
theorem B2247817 : Blo 1997435 2247817 := bbase (se 2 (by rfl) ⟨842931, by rfl⟩ : syracuseStep 2247817 = 1685863) (by norm_num)
theorem B2997089 : Blo 1997435 2997089 := bstep (se 2 (by rfl) ⟨1123908, by rfl⟩ : syracuseStep 2997089 = 2247817) B2247817
theorem B1998059 : Blo 1997435 1998059 := bstep (se 1 (by rfl) ⟨1498544, by rfl⟩ : syracuseStep 1998059 = 2997089) B2997089
theorem B4556981 : Blo 1997435 4556981 := bbase (se 5 (by rfl) ⟨213608, by rfl⟩ : syracuseStep 4556981 = 427217) (by norm_num)
theorem B3037987 : Blo 1997435 3037987 := bstep (se 1 (by rfl) ⟨2278490, by rfl⟩ : syracuseStep 3037987 = 4556981) B4556981
theorem B4050649 : Blo 1997435 4050649 := bstep (se 2 (by rfl) ⟨1518993, by rfl⟩ : syracuseStep 4050649 = 3037987) B3037987
theorem B5400865 : Blo 1997435 5400865 := bstep (se 2 (by rfl) ⟨2025324, by rfl⟩ : syracuseStep 5400865 = 4050649) B4050649
theorem B7201153 : Blo 1997435 7201153 := bstep (se 2 (by rfl) ⟨2700432, by rfl⟩ : syracuseStep 7201153 = 5400865) B5400865
theorem B38406149 : Blo 1997435 38406149 := bstep (se 4 (by rfl) ⟨3600576, by rfl⟩ : syracuseStep 38406149 = 7201153) B7201153
theorem B25604099 : Blo 1997435 25604099 := bstep (se 1 (by rfl) ⟨19203074, by rfl⟩ : syracuseStep 25604099 = 38406149) B38406149
theorem B17069399 : Blo 1997435 17069399 := bstep (se 1 (by rfl) ⟨12802049, by rfl⟩ : syracuseStep 17069399 = 25604099) B25604099
theorem B11379599 : Blo 1997435 11379599 := bstep (se 1 (by rfl) ⟨8534699, by rfl⟩ : syracuseStep 11379599 = 17069399) B17069399
theorem B7586399 : Blo 1997435 7586399 := bstep (se 1 (by rfl) ⟨5689799, by rfl⟩ : syracuseStep 7586399 = 11379599) B11379599
theorem B5057599 : Blo 1997435 5057599 := bstep (se 1 (by rfl) ⟨3793199, by rfl⟩ : syracuseStep 5057599 = 7586399) B7586399
theorem B6743465 : Blo 1997435 6743465 := bstep (se 2 (by rfl) ⟨2528799, by rfl⟩ : syracuseStep 6743465 = 5057599) B5057599
theorem B4495643 : Blo 1997435 4495643 := bstep (se 1 (by rfl) ⟨3371732, by rfl⟩ : syracuseStep 4495643 = 6743465) B6743465
theorem B2997095 : Blo 1997435 2997095 := bstep (se 1 (by rfl) ⟨2247821, by rfl⟩ : syracuseStep 2997095 = 4495643) B4495643
theorem B1998063 : Blo 1997435 1998063 := bstep (se 1 (by rfl) ⟨1498547, by rfl⟩ : syracuseStep 1998063 = 2997095) B2997095
theorem B2997101 : Blo 1997435 2997101 := bbase (se 3 (by rfl) ⟨561956, by rfl⟩ : syracuseStep 2997101 = 1123913) (by norm_num)
theorem B1998067 : Blo 1997435 1998067 := bstep (se 1 (by rfl) ⟨1498550, by rfl⟩ : syracuseStep 1998067 = 2997101) B2997101
theorem B4495661 : Blo 1997435 4495661 := bbase (se 3 (by rfl) ⟨842936, by rfl⟩ : syracuseStep 4495661 = 1685873) (by norm_num)
theorem B2997107 : Blo 1997435 2997107 := bstep (se 1 (by rfl) ⟨2247830, by rfl⟩ : syracuseStep 2997107 = 4495661) B4495661
theorem B1998071 : Blo 1997435 1998071 := bstep (se 1 (by rfl) ⟨1498553, by rfl⟩ : syracuseStep 1998071 = 2997107) B2997107
theorem B3417757 : Blo 1997435 3417757 := bbase (se 3 (by rfl) ⟨640829, by rfl⟩ : syracuseStep 3417757 = 1281659) (by norm_num)
theorem B18228037 : Blo 1997435 18228037 := bstep (se 4 (by rfl) ⟨1708878, by rfl⟩ : syracuseStep 18228037 = 3417757) B3417757
theorem B24304049 : Blo 1997435 24304049 := bstep (se 2 (by rfl) ⟨9114018, by rfl⟩ : syracuseStep 24304049 = 18228037) B18228037
theorem B16202699 : Blo 1997435 16202699 := bstep (se 1 (by rfl) ⟨12152024, by rfl⟩ : syracuseStep 16202699 = 24304049) B24304049
theorem B10801799 : Blo 1997435 10801799 := bstep (se 1 (by rfl) ⟨8101349, by rfl⟩ : syracuseStep 10801799 = 16202699) B16202699
theorem B7201199 : Blo 1997435 7201199 := bstep (se 1 (by rfl) ⟨5400899, by rfl⟩ : syracuseStep 7201199 = 10801799) B10801799
theorem B4800799 : Blo 1997435 4800799 := bstep (se 1 (by rfl) ⟨3600599, by rfl⟩ : syracuseStep 4800799 = 7201199) B7201199
theorem B6401065 : Blo 1997435 6401065 := bstep (se 2 (by rfl) ⟨2400399, by rfl⟩ : syracuseStep 6401065 = 4800799) B4800799
theorem B8534753 : Blo 1997435 8534753 := bstep (se 2 (by rfl) ⟨3200532, by rfl⟩ : syracuseStep 8534753 = 6401065) B6401065
theorem B5689835 : Blo 1997435 5689835 := bstep (se 1 (by rfl) ⟨4267376, by rfl⟩ : syracuseStep 5689835 = 8534753) B8534753
theorem B3793223 : Blo 1997435 3793223 := bstep (se 1 (by rfl) ⟨2844917, by rfl⟩ : syracuseStep 3793223 = 5689835) B5689835
theorem B2528815 : Blo 1997435 2528815 := bstep (se 1 (by rfl) ⟨1896611, by rfl⟩ : syracuseStep 2528815 = 3793223) B3793223
theorem B3371753 : Blo 1997435 3371753 := bstep (se 2 (by rfl) ⟨1264407, by rfl⟩ : syracuseStep 3371753 = 2528815) B2528815
theorem B2247835 : Blo 1997435 2247835 := bstep (se 1 (by rfl) ⟨1685876, by rfl⟩ : syracuseStep 2247835 = 3371753) B3371753
theorem B2997113 : Blo 1997435 2997113 := bstep (se 2 (by rfl) ⟨1123917, by rfl⟩ : syracuseStep 2997113 = 2247835) B2247835
theorem B1998075 : Blo 1997435 1998075 := bstep (se 1 (by rfl) ⟨1498556, by rfl⟩ : syracuseStep 1998075 = 2997113) B2997113
theorem B17302421 : Blo 1997435 17302421 := bbase (se 6 (by rfl) ⟨405525, by rfl⟩ : syracuseStep 17302421 = 811051) (by norm_num)
theorem B46139789 : Blo 1997435 46139789 := bstep (se 3 (by rfl) ⟨8651210, by rfl⟩ : syracuseStep 46139789 = 17302421) B17302421
theorem B30759859 : Blo 1997435 30759859 := bstep (se 1 (by rfl) ⟨23069894, by rfl⟩ : syracuseStep 30759859 = 46139789) B46139789
theorem B41013145 : Blo 1997435 41013145 := bstep (se 2 (by rfl) ⟨15379929, by rfl⟩ : syracuseStep 41013145 = 30759859) B30759859
theorem B54684193 : Blo 1997435 54684193 := bstep (se 2 (by rfl) ⟨20506572, by rfl⟩ : syracuseStep 54684193 = 41013145) B41013145
theorem B72912257 : Blo 1997435 72912257 := bstep (se 2 (by rfl) ⟨27342096, by rfl⟩ : syracuseStep 72912257 = 54684193) B54684193
theorem B48608171 : Blo 1997435 48608171 := bstep (se 1 (by rfl) ⟨36456128, by rfl⟩ : syracuseStep 48608171 = 72912257) B72912257
theorem B32405447 : Blo 1997435 32405447 := bstep (se 1 (by rfl) ⟨24304085, by rfl⟩ : syracuseStep 32405447 = 48608171) B48608171
theorem B21603631 : Blo 1997435 21603631 := bstep (se 1 (by rfl) ⟨16202723, by rfl⟩ : syracuseStep 21603631 = 32405447) B32405447
theorem B28804841 : Blo 1997435 28804841 := bstep (se 2 (by rfl) ⟨10801815, by rfl⟩ : syracuseStep 28804841 = 21603631) B21603631
theorem B19203227 : Blo 1997435 19203227 := bstep (se 1 (by rfl) ⟨14402420, by rfl⟩ : syracuseStep 19203227 = 28804841) B28804841
theorem B12802151 : Blo 1997435 12802151 := bstep (se 1 (by rfl) ⟨9601613, by rfl⟩ : syracuseStep 12802151 = 19203227) B19203227
theorem B34139069 : Blo 1997435 34139069 := bstep (se 3 (by rfl) ⟨6401075, by rfl⟩ : syracuseStep 34139069 = 12802151) B12802151
theorem B22759379 : Blo 1997435 22759379 := bstep (se 1 (by rfl) ⟨17069534, by rfl⟩ : syracuseStep 22759379 = 34139069) B34139069
theorem B15172919 : Blo 1997435 15172919 := bstep (se 1 (by rfl) ⟨11379689, by rfl⟩ : syracuseStep 15172919 = 22759379) B22759379
theorem B10115279 : Blo 1997435 10115279 := bstep (se 1 (by rfl) ⟨7586459, by rfl⟩ : syracuseStep 10115279 = 15172919) B15172919
theorem B6743519 : Blo 1997435 6743519 := bstep (se 1 (by rfl) ⟨5057639, by rfl⟩ : syracuseStep 6743519 = 10115279) B10115279
theorem B4495679 : Blo 1997435 4495679 := bstep (se 1 (by rfl) ⟨3371759, by rfl⟩ : syracuseStep 4495679 = 6743519) B6743519
theorem B2997119 : Blo 1997435 2997119 := bstep (se 1 (by rfl) ⟨2247839, by rfl⟩ : syracuseStep 2997119 = 4495679) B4495679
theorem B1998079 : Blo 1997435 1998079 := bstep (se 1 (by rfl) ⟨1498559, by rfl⟩ : syracuseStep 1998079 = 2997119) B2997119
theorem B2997125 : Blo 1997435 2997125 := bbase (se 4 (by rfl) ⟨280980, by rfl⟩ : syracuseStep 2997125 = 561961) (by norm_num)
theorem B1998083 : Blo 1997435 1998083 := bstep (se 1 (by rfl) ⟨1498562, by rfl⟩ : syracuseStep 1998083 = 2997125) B2997125
theorem B3371773 : Blo 1997435 3371773 := bbase (se 3 (by rfl) ⟨632207, by rfl⟩ : syracuseStep 3371773 = 1264415) (by norm_num)
theorem B4495697 : Blo 1997435 4495697 := bstep (se 2 (by rfl) ⟨1685886, by rfl⟩ : syracuseStep 4495697 = 3371773) B3371773
theorem B2997131 : Blo 1997435 2997131 := bstep (se 1 (by rfl) ⟨2247848, by rfl⟩ : syracuseStep 2997131 = 4495697) B4495697
theorem B1998087 : Blo 1997435 1998087 := bstep (se 1 (by rfl) ⟨1498565, by rfl⟩ : syracuseStep 1998087 = 2997131) B2997131
theorem B2247853 : Blo 1997435 2247853 := bbase (se 3 (by rfl) ⟨421472, by rfl⟩ : syracuseStep 2247853 = 842945) (by norm_num)
theorem B2997137 : Blo 1997435 2997137 := bstep (se 2 (by rfl) ⟨1123926, by rfl⟩ : syracuseStep 2997137 = 2247853) B2247853
theorem B1998091 : Blo 1997435 1998091 := bstep (se 1 (by rfl) ⟨1498568, by rfl⟩ : syracuseStep 1998091 = 2997137) B2997137
theorem B6743573 : Blo 1997435 6743573 := bbase (se 6 (by rfl) ⟨158052, by rfl⟩ : syracuseStep 6743573 = 316105) (by norm_num)
theorem B4495715 : Blo 1997435 4495715 := bstep (se 1 (by rfl) ⟨3371786, by rfl⟩ : syracuseStep 4495715 = 6743573) B6743573
theorem B2997143 : Blo 1997435 2997143 := bstep (se 1 (by rfl) ⟨2247857, by rfl⟩ : syracuseStep 2997143 = 4495715) B4495715
theorem B1998095 : Blo 1997435 1998095 := bstep (se 1 (by rfl) ⟨1498571, by rfl⟩ : syracuseStep 1998095 = 2997143) B2997143
theorem B2997149 : Blo 1997435 2997149 := bbase (se 3 (by rfl) ⟨561965, by rfl⟩ : syracuseStep 2997149 = 1123931) (by norm_num)
theorem B1998099 : Blo 1997435 1998099 := bstep (se 1 (by rfl) ⟨1498574, by rfl⟩ : syracuseStep 1998099 = 2997149) B2997149
theorem B4495733 : Blo 1997435 4495733 := bbase (se 5 (by rfl) ⟨210737, by rfl⟩ : syracuseStep 4495733 = 421475) (by norm_num)
theorem B2997155 : Blo 1997435 2997155 := bstep (se 1 (by rfl) ⟨2247866, by rfl⟩ : syracuseStep 2997155 = 4495733) B4495733
theorem B1998103 : Blo 1997435 1998103 := bstep (se 1 (by rfl) ⟨1498577, by rfl⟩ : syracuseStep 1998103 = 2997155) B2997155
theorem B2278541 : Blo 1997435 2278541 := bbase (se 3 (by rfl) ⟨427226, by rfl⟩ : syracuseStep 2278541 = 854453) (by norm_num)
theorem B6076109 : Blo 1997435 6076109 := bstep (se 3 (by rfl) ⟨1139270, by rfl⟩ : syracuseStep 6076109 = 2278541) B2278541
theorem B4050739 : Blo 1997435 4050739 := bstep (se 1 (by rfl) ⟨3038054, by rfl⟩ : syracuseStep 4050739 = 6076109) B6076109
theorem B5400985 : Blo 1997435 5400985 := bstep (se 2 (by rfl) ⟨2025369, by rfl⟩ : syracuseStep 5400985 = 4050739) B4050739
theorem B7201313 : Blo 1997435 7201313 := bstep (se 2 (by rfl) ⟨2700492, by rfl⟩ : syracuseStep 7201313 = 5400985) B5400985
theorem B4800875 : Blo 1997435 4800875 := bstep (se 1 (by rfl) ⟨3600656, by rfl⟩ : syracuseStep 4800875 = 7201313) B7201313
theorem B12802333 : Blo 1997435 12802333 := bstep (se 3 (by rfl) ⟨2400437, by rfl⟩ : syracuseStep 12802333 = 4800875) B4800875
theorem B17069777 : Blo 1997435 17069777 := bstep (se 2 (by rfl) ⟨6401166, by rfl⟩ : syracuseStep 17069777 = 12802333) B12802333
theorem B11379851 : Blo 1997435 11379851 := bstep (se 1 (by rfl) ⟨8534888, by rfl⟩ : syracuseStep 11379851 = 17069777) B17069777
theorem B7586567 : Blo 1997435 7586567 := bstep (se 1 (by rfl) ⟨5689925, by rfl⟩ : syracuseStep 7586567 = 11379851) B11379851
theorem B5057711 : Blo 1997435 5057711 := bstep (se 1 (by rfl) ⟨3793283, by rfl⟩ : syracuseStep 5057711 = 7586567) B7586567
theorem B3371807 : Blo 1997435 3371807 := bstep (se 1 (by rfl) ⟨2528855, by rfl⟩ : syracuseStep 3371807 = 5057711) B5057711
theorem B2247871 : Blo 1997435 2247871 := bstep (se 1 (by rfl) ⟨1685903, by rfl⟩ : syracuseStep 2247871 = 3371807) B3371807
theorem B2997161 : Blo 1997435 2997161 := bstep (se 2 (by rfl) ⟨1123935, by rfl⟩ : syracuseStep 2997161 = 2247871) B2247871
theorem B1998107 : Blo 1997435 1998107 := bstep (se 1 (by rfl) ⟨1498580, by rfl⟩ : syracuseStep 1998107 = 2997161) B2997161
theorem B7586581 : Blo 1997435 7586581 := bbase (se 6 (by rfl) ⟨177810, by rfl⟩ : syracuseStep 7586581 = 355621) (by norm_num)
theorem B10115441 : Blo 1997435 10115441 := bstep (se 2 (by rfl) ⟨3793290, by rfl⟩ : syracuseStep 10115441 = 7586581) B7586581
theorem B6743627 : Blo 1997435 6743627 := bstep (se 1 (by rfl) ⟨5057720, by rfl⟩ : syracuseStep 6743627 = 10115441) B10115441
theorem B4495751 : Blo 1997435 4495751 := bstep (se 1 (by rfl) ⟨3371813, by rfl⟩ : syracuseStep 4495751 = 6743627) B6743627
theorem B2997167 : Blo 1997435 2997167 := bstep (se 1 (by rfl) ⟨2247875, by rfl⟩ : syracuseStep 2997167 = 4495751) B4495751
theorem B1998111 : Blo 1997435 1998111 := bstep (se 1 (by rfl) ⟨1498583, by rfl⟩ : syracuseStep 1998111 = 2997167) B2997167
theorem B2997173 : Blo 1997435 2997173 := bbase (se 5 (by rfl) ⟨140492, by rfl⟩ : syracuseStep 2997173 = 280985) (by norm_num)
theorem B1998115 : Blo 1997435 1998115 := bstep (se 1 (by rfl) ⟨1498586, by rfl⟩ : syracuseStep 1998115 = 2997173) B2997173
theorem B5057741 : Blo 1997435 5057741 := bbase (se 3 (by rfl) ⟨948326, by rfl⟩ : syracuseStep 5057741 = 1896653) (by norm_num)
theorem B3371827 : Blo 1997435 3371827 := bstep (se 1 (by rfl) ⟨2528870, by rfl⟩ : syracuseStep 3371827 = 5057741) B5057741
theorem B4495769 : Blo 1997435 4495769 := bstep (se 2 (by rfl) ⟨1685913, by rfl⟩ : syracuseStep 4495769 = 3371827) B3371827
theorem B2997179 : Blo 1997435 2997179 := bstep (se 1 (by rfl) ⟨2247884, by rfl⟩ : syracuseStep 2997179 = 4495769) B4495769
theorem B1998119 : Blo 1997435 1998119 := bstep (se 1 (by rfl) ⟨1498589, by rfl⟩ : syracuseStep 1998119 = 2997179) B2997179
theorem B2247889 : Blo 1997435 2247889 := bbase (se 2 (by rfl) ⟨842958, by rfl⟩ : syracuseStep 2247889 = 1685917) (by norm_num)
theorem B2997185 : Blo 1997435 2997185 := bstep (se 2 (by rfl) ⟨1123944, by rfl⟩ : syracuseStep 2997185 = 2247889) B2247889
theorem B1998123 : Blo 1997435 1998123 := bstep (se 1 (by rfl) ⟨1498592, by rfl⟩ : syracuseStep 1998123 = 2997185) B2997185
theorem B3164141 : Blo 1997435 3164141 := bbase (se 3 (by rfl) ⟨593276, by rfl⟩ : syracuseStep 3164141 = 1186553) (by norm_num)
theorem B8437709 : Blo 1997435 8437709 := bstep (se 3 (by rfl) ⟨1582070, by rfl⟩ : syracuseStep 8437709 = 3164141) B3164141
theorem B5625139 : Blo 1997435 5625139 := bstep (se 1 (by rfl) ⟨4218854, by rfl⟩ : syracuseStep 5625139 = 8437709) B8437709
theorem B7500185 : Blo 1997435 7500185 := bstep (se 2 (by rfl) ⟨2812569, by rfl⟩ : syracuseStep 7500185 = 5625139) B5625139
theorem B5000123 : Blo 1997435 5000123 := bstep (se 1 (by rfl) ⟨3750092, by rfl⟩ : syracuseStep 5000123 = 7500185) B7500185
theorem B3333415 : Blo 1997435 3333415 := bstep (se 1 (by rfl) ⟨2500061, by rfl⟩ : syracuseStep 3333415 = 5000123) B5000123
theorem B4444553 : Blo 1997435 4444553 := bstep (se 2 (by rfl) ⟨1666707, by rfl⟩ : syracuseStep 4444553 = 3333415) B3333415
theorem B2963035 : Blo 1997435 2963035 := bstep (se 1 (by rfl) ⟨2222276, by rfl⟩ : syracuseStep 2963035 = 4444553) B4444553
theorem B3950713 : Blo 1997435 3950713 := bstep (se 2 (by rfl) ⟨1481517, by rfl⟩ : syracuseStep 3950713 = 2963035) B2963035
theorem B21070469 : Blo 1997435 21070469 := bstep (se 4 (by rfl) ⟨1975356, by rfl⟩ : syracuseStep 21070469 = 3950713) B3950713
theorem B14046979 : Blo 1997435 14046979 := bstep (se 1 (by rfl) ⟨10535234, by rfl⟩ : syracuseStep 14046979 = 21070469) B21070469
theorem B18729305 : Blo 1997435 18729305 := bstep (se 2 (by rfl) ⟨7023489, by rfl⟩ : syracuseStep 18729305 = 14046979) B14046979
theorem B12486203 : Blo 1997435 12486203 := bstep (se 1 (by rfl) ⟨9364652, by rfl⟩ : syracuseStep 12486203 = 18729305) B18729305
theorem B8324135 : Blo 1997435 8324135 := bstep (se 1 (by rfl) ⟨6243101, by rfl⟩ : syracuseStep 8324135 = 12486203) B12486203
theorem B5549423 : Blo 1997435 5549423 := bstep (se 1 (by rfl) ⟨4162067, by rfl⟩ : syracuseStep 5549423 = 8324135) B8324135
theorem B14798461 : Blo 1997435 14798461 := bstep (se 3 (by rfl) ⟨2774711, by rfl⟩ : syracuseStep 14798461 = 5549423) B5549423
theorem B19731281 : Blo 1997435 19731281 := bstep (se 2 (by rfl) ⟨7399230, by rfl⟩ : syracuseStep 19731281 = 14798461) B14798461
theorem B52616749 : Blo 1997435 52616749 := bstep (se 3 (by rfl) ⟨9865640, by rfl⟩ : syracuseStep 52616749 = 19731281) B19731281
theorem B70155665 : Blo 1997435 70155665 := bstep (se 2 (by rfl) ⟨26308374, by rfl⟩ : syracuseStep 70155665 = 52616749) B52616749
theorem B46770443 : Blo 1997435 46770443 := bstep (se 1 (by rfl) ⟨35077832, by rfl⟩ : syracuseStep 46770443 = 70155665) B70155665
theorem B31180295 : Blo 1997435 31180295 := bstep (se 1 (by rfl) ⟨23385221, by rfl⟩ : syracuseStep 31180295 = 46770443) B46770443
theorem B20786863 : Blo 1997435 20786863 := bstep (se 1 (by rfl) ⟨15590147, by rfl⟩ : syracuseStep 20786863 = 31180295) B31180295
theorem B27715817 : Blo 1997435 27715817 := bstep (se 2 (by rfl) ⟨10393431, by rfl⟩ : syracuseStep 27715817 = 20786863) B20786863
theorem B73908845 : Blo 1997435 73908845 := bstep (se 3 (by rfl) ⟨13857908, by rfl⟩ : syracuseStep 73908845 = 27715817) B27715817
theorem B49272563 : Blo 1997435 49272563 := bstep (se 1 (by rfl) ⟨36954422, by rfl⟩ : syracuseStep 49272563 = 73908845) B73908845
theorem B32848375 : Blo 1997435 32848375 := bstep (se 1 (by rfl) ⟨24636281, by rfl⟩ : syracuseStep 32848375 = 49272563) B49272563
theorem B43797833 : Blo 1997435 43797833 := bstep (se 2 (by rfl) ⟨16424187, by rfl⟩ : syracuseStep 43797833 = 32848375) B32848375
theorem B29198555 : Blo 1997435 29198555 := bstep (se 1 (by rfl) ⟨21898916, by rfl⟩ : syracuseStep 29198555 = 43797833) B43797833
theorem B19465703 : Blo 1997435 19465703 := bstep (se 1 (by rfl) ⟨14599277, by rfl⟩ : syracuseStep 19465703 = 29198555) B29198555
theorem B12977135 : Blo 1997435 12977135 := bstep (se 1 (by rfl) ⟨9732851, by rfl⟩ : syracuseStep 12977135 = 19465703) B19465703
theorem B8651423 : Blo 1997435 8651423 := bstep (se 1 (by rfl) ⟨6488567, by rfl⟩ : syracuseStep 8651423 = 12977135) B12977135
theorem B5767615 : Blo 1997435 5767615 := bstep (se 1 (by rfl) ⟨4325711, by rfl⟩ : syracuseStep 5767615 = 8651423) B8651423
theorem B7690153 : Blo 1997435 7690153 := bstep (se 2 (by rfl) ⟨2883807, by rfl⟩ : syracuseStep 7690153 = 5767615) B5767615
theorem B10253537 : Blo 1997435 10253537 := bstep (se 2 (by rfl) ⟨3845076, by rfl⟩ : syracuseStep 10253537 = 7690153) B7690153
theorem B6835691 : Blo 1997435 6835691 := bstep (se 1 (by rfl) ⟨5126768, by rfl⟩ : syracuseStep 6835691 = 10253537) B10253537
theorem B18228509 : Blo 1997435 18228509 := bstep (se 3 (by rfl) ⟨3417845, by rfl⟩ : syracuseStep 18228509 = 6835691) B6835691
theorem B12152339 : Blo 1997435 12152339 := bstep (se 1 (by rfl) ⟨9114254, by rfl⟩ : syracuseStep 12152339 = 18228509) B18228509
theorem B8101559 : Blo 1997435 8101559 := bstep (se 1 (by rfl) ⟨6076169, by rfl⟩ : syracuseStep 8101559 = 12152339) B12152339
theorem B21604157 : Blo 1997435 21604157 := bstep (se 3 (by rfl) ⟨4050779, by rfl⟩ : syracuseStep 21604157 = 8101559) B8101559
theorem B14402771 : Blo 1997435 14402771 := bstep (se 1 (by rfl) ⟨10802078, by rfl⟩ : syracuseStep 14402771 = 21604157) B21604157
theorem B9601847 : Blo 1997435 9601847 := bstep (se 1 (by rfl) ⟨7201385, by rfl⟩ : syracuseStep 9601847 = 14402771) B14402771
theorem B6401231 : Blo 1997435 6401231 := bstep (se 1 (by rfl) ⟨4800923, by rfl⟩ : syracuseStep 6401231 = 9601847) B9601847
theorem B4267487 : Blo 1997435 4267487 := bstep (se 1 (by rfl) ⟨3200615, by rfl⟩ : syracuseStep 4267487 = 6401231) B6401231
theorem B2844991 : Blo 1997435 2844991 := bstep (se 1 (by rfl) ⟨2133743, by rfl⟩ : syracuseStep 2844991 = 4267487) B4267487
theorem B3793321 : Blo 1997435 3793321 := bstep (se 2 (by rfl) ⟨1422495, by rfl⟩ : syracuseStep 3793321 = 2844991) B2844991
theorem B5057761 : Blo 1997435 5057761 := bstep (se 2 (by rfl) ⟨1896660, by rfl⟩ : syracuseStep 5057761 = 3793321) B3793321
theorem B6743681 : Blo 1997435 6743681 := bstep (se 2 (by rfl) ⟨2528880, by rfl⟩ : syracuseStep 6743681 = 5057761) B5057761
theorem B4495787 : Blo 1997435 4495787 := bstep (se 1 (by rfl) ⟨3371840, by rfl⟩ : syracuseStep 4495787 = 6743681) B6743681
theorem B2997191 : Blo 1997435 2997191 := bstep (se 1 (by rfl) ⟨2247893, by rfl⟩ : syracuseStep 2997191 = 4495787) B4495787
theorem B1998127 : Blo 1997435 1998127 := bstep (se 1 (by rfl) ⟨1498595, by rfl⟩ : syracuseStep 1998127 = 2997191) B2997191
theorem B2997197 : Blo 1997435 2997197 := bbase (se 3 (by rfl) ⟨561974, by rfl⟩ : syracuseStep 2997197 = 1123949) (by norm_num)
theorem B1998131 : Blo 1997435 1998131 := bstep (se 1 (by rfl) ⟨1498598, by rfl⟩ : syracuseStep 1998131 = 2997197) B2997197
theorem B4495805 : Blo 1997435 4495805 := bbase (se 3 (by rfl) ⟨842963, by rfl⟩ : syracuseStep 4495805 = 1685927) (by norm_num)
theorem B2997203 : Blo 1997435 2997203 := bstep (se 1 (by rfl) ⟨2247902, by rfl⟩ : syracuseStep 2997203 = 4495805) B4495805
theorem B1998135 : Blo 1997435 1998135 := bstep (se 1 (by rfl) ⟨1498601, by rfl⟩ : syracuseStep 1998135 = 2997203) B2997203
theorem B3371861 : Blo 1997435 3371861 := bbase (se 9 (by rfl) ⟨9878, by rfl⟩ : syracuseStep 3371861 = 19757) (by norm_num)
theorem B2247907 : Blo 1997435 2247907 := bstep (se 1 (by rfl) ⟨1685930, by rfl⟩ : syracuseStep 2247907 = 3371861) B3371861
theorem B2997209 : Blo 1997435 2997209 := bstep (se 2 (by rfl) ⟨1123953, by rfl⟩ : syracuseStep 2997209 = 2247907) B2247907
theorem B1998139 : Blo 1997435 1998139 := bstep (se 1 (by rfl) ⟨1498604, by rfl⟩ : syracuseStep 1998139 = 2997209) B2997209
theorem B2700541 : Blo 1997435 2700541 := bbase (se 3 (by rfl) ⟨506351, by rfl⟩ : syracuseStep 2700541 = 1012703) (by norm_num)
theorem B3600721 : Blo 1997435 3600721 := bstep (se 2 (by rfl) ⟨1350270, by rfl⟩ : syracuseStep 3600721 = 2700541) B2700541
theorem B4800961 : Blo 1997435 4800961 := bstep (se 2 (by rfl) ⟨1800360, by rfl⟩ : syracuseStep 4800961 = 3600721) B3600721
theorem B6401281 : Blo 1997435 6401281 := bstep (se 2 (by rfl) ⟨2400480, by rfl⟩ : syracuseStep 6401281 = 4800961) B4800961
theorem B8535041 : Blo 1997435 8535041 := bstep (se 2 (by rfl) ⟨3200640, by rfl⟩ : syracuseStep 8535041 = 6401281) B6401281
theorem B5690027 : Blo 1997435 5690027 := bstep (se 1 (by rfl) ⟨4267520, by rfl⟩ : syracuseStep 5690027 = 8535041) B8535041
theorem B15173405 : Blo 1997435 15173405 := bstep (se 3 (by rfl) ⟨2845013, by rfl⟩ : syracuseStep 15173405 = 5690027) B5690027
theorem B10115603 : Blo 1997435 10115603 := bstep (se 1 (by rfl) ⟨7586702, by rfl⟩ : syracuseStep 10115603 = 15173405) B15173405
theorem B6743735 : Blo 1997435 6743735 := bstep (se 1 (by rfl) ⟨5057801, by rfl⟩ : syracuseStep 6743735 = 10115603) B10115603
theorem B4495823 : Blo 1997435 4495823 := bstep (se 1 (by rfl) ⟨3371867, by rfl⟩ : syracuseStep 4495823 = 6743735) B6743735
theorem B2997215 : Blo 1997435 2997215 := bstep (se 1 (by rfl) ⟨2247911, by rfl⟩ : syracuseStep 2997215 = 4495823) B4495823
theorem B1998143 : Blo 1997435 1998143 := bstep (se 1 (by rfl) ⟨1498607, by rfl⟩ : syracuseStep 1998143 = 2997215) B2997215
theorem B2997221 : Blo 1997435 2997221 := bbase (se 4 (by rfl) ⟨280989, by rfl⟩ : syracuseStep 2997221 = 561979) (by norm_num)
theorem B1998147 : Blo 1997435 1998147 := bstep (se 1 (by rfl) ⟨1498610, by rfl⟩ : syracuseStep 1998147 = 2997221) B2997221
theorem B8535077 : Blo 1997435 8535077 := bbase (se 4 (by rfl) ⟨800163, by rfl⟩ : syracuseStep 8535077 = 1600327) (by norm_num)
theorem B5690051 : Blo 1997435 5690051 := bstep (se 1 (by rfl) ⟨4267538, by rfl⟩ : syracuseStep 5690051 = 8535077) B8535077
theorem B3793367 : Blo 1997435 3793367 := bstep (se 1 (by rfl) ⟨2845025, by rfl⟩ : syracuseStep 3793367 = 5690051) B5690051
theorem B2528911 : Blo 1997435 2528911 := bstep (se 1 (by rfl) ⟨1896683, by rfl⟩ : syracuseStep 2528911 = 3793367) B3793367
theorem B3371881 : Blo 1997435 3371881 := bstep (se 2 (by rfl) ⟨1264455, by rfl⟩ : syracuseStep 3371881 = 2528911) B2528911
theorem B4495841 : Blo 1997435 4495841 := bstep (se 2 (by rfl) ⟨1685940, by rfl⟩ : syracuseStep 4495841 = 3371881) B3371881
theorem B2997227 : Blo 1997435 2997227 := bstep (se 1 (by rfl) ⟨2247920, by rfl⟩ : syracuseStep 2997227 = 4495841) B4495841
theorem B1998151 : Blo 1997435 1998151 := bstep (se 1 (by rfl) ⟨1498613, by rfl⟩ : syracuseStep 1998151 = 2997227) B2997227
theorem B2247925 : Blo 1997435 2247925 := bbase (se 5 (by rfl) ⟨105371, by rfl⟩ : syracuseStep 2247925 = 210743) (by norm_num)
theorem B2997233 : Blo 1997435 2997233 := bstep (se 2 (by rfl) ⟨1123962, by rfl⟩ : syracuseStep 2997233 = 2247925) B2247925
theorem B1998155 : Blo 1997435 1998155 := bstep (se 1 (by rfl) ⟨1498616, by rfl⟩ : syracuseStep 1998155 = 2997233) B2997233
theorem B2528921 : Blo 1997435 2528921 := bbase (se 2 (by rfl) ⟨948345, by rfl⟩ : syracuseStep 2528921 = 1896691) (by norm_num)
theorem B6743789 : Blo 1997435 6743789 := bstep (se 3 (by rfl) ⟨1264460, by rfl⟩ : syracuseStep 6743789 = 2528921) B2528921
theorem B4495859 : Blo 1997435 4495859 := bstep (se 1 (by rfl) ⟨3371894, by rfl⟩ : syracuseStep 4495859 = 6743789) B6743789
theorem B2997239 : Blo 1997435 2997239 := bstep (se 1 (by rfl) ⟨2247929, by rfl⟩ : syracuseStep 2997239 = 4495859) B4495859
theorem B1998159 : Blo 1997435 1998159 := bstep (se 1 (by rfl) ⟨1498619, by rfl⟩ : syracuseStep 1998159 = 2997239) B2997239
theorem B2997245 : Blo 1997435 2997245 := bbase (se 3 (by rfl) ⟨561983, by rfl⟩ : syracuseStep 2997245 = 1123967) (by norm_num)
theorem B1998163 : Blo 1997435 1998163 := bstep (se 1 (by rfl) ⟨1498622, by rfl⟩ : syracuseStep 1998163 = 2997245) B2997245
theorem B4495877 : Blo 1997435 4495877 := bbase (se 4 (by rfl) ⟨421488, by rfl⟩ : syracuseStep 4495877 = 842977) (by norm_num)
theorem B2997251 : Blo 1997435 2997251 := bstep (se 1 (by rfl) ⟨2247938, by rfl⟩ : syracuseStep 2997251 = 4495877) B4495877
theorem B1998167 : Blo 1997435 1998167 := bstep (se 1 (by rfl) ⟨1498625, by rfl⟩ : syracuseStep 1998167 = 2997251) B2997251
theorem B3793405 : Blo 1997435 3793405 := bbase (se 3 (by rfl) ⟨711263, by rfl⟩ : syracuseStep 3793405 = 1422527) (by norm_num)
theorem B5057873 : Blo 1997435 5057873 := bstep (se 2 (by rfl) ⟨1896702, by rfl⟩ : syracuseStep 5057873 = 3793405) B3793405
theorem B3371915 : Blo 1997435 3371915 := bstep (se 1 (by rfl) ⟨2528936, by rfl⟩ : syracuseStep 3371915 = 5057873) B5057873
theorem B2247943 : Blo 1997435 2247943 := bstep (se 1 (by rfl) ⟨1685957, by rfl⟩ : syracuseStep 2247943 = 3371915) B3371915
theorem B2997257 : Blo 1997435 2997257 := bstep (se 2 (by rfl) ⟨1123971, by rfl⟩ : syracuseStep 2997257 = 2247943) B2247943
theorem B1998171 : Blo 1997435 1998171 := bstep (se 1 (by rfl) ⟨1498628, by rfl⟩ : syracuseStep 1998171 = 2997257) B2997257
theorem B10115765 : Blo 1997435 10115765 := bbase (se 5 (by rfl) ⟨474176, by rfl⟩ : syracuseStep 10115765 = 948353) (by norm_num)
theorem B6743843 : Blo 1997435 6743843 := bstep (se 1 (by rfl) ⟨5057882, by rfl⟩ : syracuseStep 6743843 = 10115765) B10115765
theorem B4495895 : Blo 1997435 4495895 := bstep (se 1 (by rfl) ⟨3371921, by rfl⟩ : syracuseStep 4495895 = 6743843) B6743843
theorem B2997263 : Blo 1997435 2997263 := bstep (se 1 (by rfl) ⟨2247947, by rfl⟩ : syracuseStep 2997263 = 4495895) B4495895
theorem B1998175 : Blo 1997435 1998175 := bstep (se 1 (by rfl) ⟨1498631, by rfl⟩ : syracuseStep 1998175 = 2997263) B2997263
theorem B2997269 : Blo 1997435 2997269 := bbase (se 6 (by rfl) ⟨70248, by rfl⟩ : syracuseStep 2997269 = 140497) (by norm_num)
theorem B1998179 : Blo 1997435 1998179 := bstep (se 1 (by rfl) ⟨1498634, by rfl⟩ : syracuseStep 1998179 = 2997269) B2997269
theorem B4050893 : Blo 1997435 4050893 := bbase (se 3 (by rfl) ⟨759542, by rfl⟩ : syracuseStep 4050893 = 1519085) (by norm_num)
theorem B2700595 : Blo 1997435 2700595 := bstep (se 1 (by rfl) ⟨2025446, by rfl⟩ : syracuseStep 2700595 = 4050893) B4050893
theorem B3600793 : Blo 1997435 3600793 := bstep (se 2 (by rfl) ⟨1350297, by rfl⟩ : syracuseStep 3600793 = 2700595) B2700595
theorem B19204229 : Blo 1997435 19204229 := bstep (se 4 (by rfl) ⟨1800396, by rfl⟩ : syracuseStep 19204229 = 3600793) B3600793
theorem B12802819 : Blo 1997435 12802819 := bstep (se 1 (by rfl) ⟨9602114, by rfl⟩ : syracuseStep 12802819 = 19204229) B19204229
theorem B17070425 : Blo 1997435 17070425 := bstep (se 2 (by rfl) ⟨6401409, by rfl⟩ : syracuseStep 17070425 = 12802819) B12802819
theorem B11380283 : Blo 1997435 11380283 := bstep (se 1 (by rfl) ⟨8535212, by rfl⟩ : syracuseStep 11380283 = 17070425) B17070425
theorem B7586855 : Blo 1997435 7586855 := bstep (se 1 (by rfl) ⟨5690141, by rfl⟩ : syracuseStep 7586855 = 11380283) B11380283
theorem B5057903 : Blo 1997435 5057903 := bstep (se 1 (by rfl) ⟨3793427, by rfl⟩ : syracuseStep 5057903 = 7586855) B7586855
theorem B3371935 : Blo 1997435 3371935 := bstep (se 1 (by rfl) ⟨2528951, by rfl⟩ : syracuseStep 3371935 = 5057903) B5057903
theorem B4495913 : Blo 1997435 4495913 := bstep (se 2 (by rfl) ⟨1685967, by rfl⟩ : syracuseStep 4495913 = 3371935) B3371935
theorem B2997275 : Blo 1997435 2997275 := bstep (se 1 (by rfl) ⟨2247956, by rfl⟩ : syracuseStep 2997275 = 4495913) B4495913
theorem B1998183 : Blo 1997435 1998183 := bstep (se 1 (by rfl) ⟨1498637, by rfl⟩ : syracuseStep 1998183 = 2997275) B2997275
theorem B2247961 : Blo 1997435 2247961 := bbase (se 2 (by rfl) ⟨842985, by rfl⟩ : syracuseStep 2247961 = 1685971) (by norm_num)
theorem B2997281 : Blo 1997435 2997281 := bstep (se 2 (by rfl) ⟨1123980, by rfl⟩ : syracuseStep 2997281 = 2247961) B2247961
theorem B1998187 : Blo 1997435 1998187 := bstep (se 1 (by rfl) ⟨1498640, by rfl⟩ : syracuseStep 1998187 = 2997281) B2997281
theorem B7586885 : Blo 1997435 7586885 := bbase (se 4 (by rfl) ⟨711270, by rfl⟩ : syracuseStep 7586885 = 1422541) (by norm_num)
theorem B5057923 : Blo 1997435 5057923 := bstep (se 1 (by rfl) ⟨3793442, by rfl⟩ : syracuseStep 5057923 = 7586885) B7586885
theorem B6743897 : Blo 1997435 6743897 := bstep (se 2 (by rfl) ⟨2528961, by rfl⟩ : syracuseStep 6743897 = 5057923) B5057923
theorem B4495931 : Blo 1997435 4495931 := bstep (se 1 (by rfl) ⟨3371948, by rfl⟩ : syracuseStep 4495931 = 6743897) B6743897
theorem B2997287 : Blo 1997435 2997287 := bstep (se 1 (by rfl) ⟨2247965, by rfl⟩ : syracuseStep 2997287 = 4495931) B4495931
theorem B1998191 : Blo 1997435 1998191 := bstep (se 1 (by rfl) ⟨1498643, by rfl⟩ : syracuseStep 1998191 = 2997287) B2997287
theorem B2997293 : Blo 1997435 2997293 := bbase (se 3 (by rfl) ⟨561992, by rfl⟩ : syracuseStep 2997293 = 1123985) (by norm_num)
theorem B1998195 : Blo 1997435 1998195 := bstep (se 1 (by rfl) ⟨1498646, by rfl⟩ : syracuseStep 1998195 = 2997293) B2997293
theorem B4495949 : Blo 1997435 4495949 := bbase (se 3 (by rfl) ⟨842990, by rfl⟩ : syracuseStep 4495949 = 1685981) (by norm_num)
theorem B2997299 : Blo 1997435 2997299 := bstep (se 1 (by rfl) ⟨2247974, by rfl⟩ : syracuseStep 2997299 = 4495949) B4495949
theorem B1998199 : Blo 1997435 1998199 := bstep (se 1 (by rfl) ⟨1498649, by rfl⟩ : syracuseStep 1998199 = 2997299) B2997299
theorem B2528977 : Blo 1997435 2528977 := bbase (se 2 (by rfl) ⟨948366, by rfl⟩ : syracuseStep 2528977 = 1896733) (by norm_num)
theorem B3371969 : Blo 1997435 3371969 := bstep (se 2 (by rfl) ⟨1264488, by rfl⟩ : syracuseStep 3371969 = 2528977) B2528977
theorem B2247979 : Blo 1997435 2247979 := bstep (se 1 (by rfl) ⟨1685984, by rfl⟩ : syracuseStep 2247979 = 3371969) B3371969
theorem B2997305 : Blo 1997435 2997305 := bstep (se 2 (by rfl) ⟨1123989, by rfl⟩ : syracuseStep 2997305 = 2247979) B2247979
theorem B1998203 : Blo 1997435 1998203 := bstep (se 1 (by rfl) ⟨1498652, by rfl⟩ : syracuseStep 1998203 = 2997305) B2997305
theorem B12977653 : Blo 1997435 12977653 := bbase (se 5 (by rfl) ⟨608327, by rfl⟩ : syracuseStep 12977653 = 1216655) (by norm_num)
theorem B17303537 : Blo 1997435 17303537 := bstep (se 2 (by rfl) ⟨6488826, by rfl⟩ : syracuseStep 17303537 = 12977653) B12977653
theorem B11535691 : Blo 1997435 11535691 := bstep (se 1 (by rfl) ⟨8651768, by rfl⟩ : syracuseStep 11535691 = 17303537) B17303537
theorem B15380921 : Blo 1997435 15380921 := bstep (se 2 (by rfl) ⟨5767845, by rfl⟩ : syracuseStep 15380921 = 11535691) B11535691
theorem B10253947 : Blo 1997435 10253947 := bstep (se 1 (by rfl) ⟨7690460, by rfl⟩ : syracuseStep 10253947 = 15380921) B15380921
theorem B13671929 : Blo 1997435 13671929 := bstep (se 2 (by rfl) ⟨5126973, by rfl⟩ : syracuseStep 13671929 = 10253947) B10253947
theorem B9114619 : Blo 1997435 9114619 := bstep (se 1 (by rfl) ⟨6835964, by rfl⟩ : syracuseStep 9114619 = 13671929) B13671929
theorem B12152825 : Blo 1997435 12152825 := bstep (se 2 (by rfl) ⟨4557309, by rfl⟩ : syracuseStep 12152825 = 9114619) B9114619
theorem B8101883 : Blo 1997435 8101883 := bstep (se 1 (by rfl) ⟨6076412, by rfl⟩ : syracuseStep 8101883 = 12152825) B12152825
theorem B5401255 : Blo 1997435 5401255 := bstep (se 1 (by rfl) ⟨4050941, by rfl⟩ : syracuseStep 5401255 = 8101883) B8101883
theorem B7201673 : Blo 1997435 7201673 := bstep (se 2 (by rfl) ⟨2700627, by rfl⟩ : syracuseStep 7201673 = 5401255) B5401255
theorem B4801115 : Blo 1997435 4801115 := bstep (se 1 (by rfl) ⟨3600836, by rfl⟩ : syracuseStep 4801115 = 7201673) B7201673
theorem B3200743 : Blo 1997435 3200743 := bstep (se 1 (by rfl) ⟨2400557, by rfl⟩ : syracuseStep 3200743 = 4801115) B4801115
theorem B4267657 : Blo 1997435 4267657 := bstep (se 2 (by rfl) ⟨1600371, by rfl⟩ : syracuseStep 4267657 = 3200743) B3200743
theorem B22760837 : Blo 1997435 22760837 := bstep (se 4 (by rfl) ⟨2133828, by rfl⟩ : syracuseStep 22760837 = 4267657) B4267657
theorem B15173891 : Blo 1997435 15173891 := bstep (se 1 (by rfl) ⟨11380418, by rfl⟩ : syracuseStep 15173891 = 22760837) B22760837
theorem B10115927 : Blo 1997435 10115927 := bstep (se 1 (by rfl) ⟨7586945, by rfl⟩ : syracuseStep 10115927 = 15173891) B15173891
theorem B6743951 : Blo 1997435 6743951 := bstep (se 1 (by rfl) ⟨5057963, by rfl⟩ : syracuseStep 6743951 = 10115927) B10115927
theorem B4495967 : Blo 1997435 4495967 := bstep (se 1 (by rfl) ⟨3371975, by rfl⟩ : syracuseStep 4495967 = 6743951) B6743951
theorem B2997311 : Blo 1997435 2997311 := bstep (se 1 (by rfl) ⟨2247983, by rfl⟩ : syracuseStep 2997311 = 4495967) B4495967
theorem B1998207 : Blo 1997435 1998207 := bstep (se 1 (by rfl) ⟨1498655, by rfl⟩ : syracuseStep 1998207 = 2997311) B2997311
theorem B2997317 : Blo 1997435 2997317 := bbase (se 4 (by rfl) ⟨280998, by rfl⟩ : syracuseStep 2997317 = 561997) (by norm_num)
theorem B1998211 : Blo 1997435 1998211 := bstep (se 1 (by rfl) ⟨1498658, by rfl⟩ : syracuseStep 1998211 = 2997317) B2997317
theorem B3371989 : Blo 1997435 3371989 := bbase (se 7 (by rfl) ⟨39515, by rfl⟩ : syracuseStep 3371989 = 79031) (by norm_num)
theorem B4495985 : Blo 1997435 4495985 := bstep (se 2 (by rfl) ⟨1685994, by rfl⟩ : syracuseStep 4495985 = 3371989) B3371989
theorem B2997323 : Blo 1997435 2997323 := bstep (se 1 (by rfl) ⟨2247992, by rfl⟩ : syracuseStep 2997323 = 4495985) B4495985
theorem B1998215 : Blo 1997435 1998215 := bstep (se 1 (by rfl) ⟨1498661, by rfl⟩ : syracuseStep 1998215 = 2997323) B2997323
theorem B2247997 : Blo 1997435 2247997 := bbase (se 3 (by rfl) ⟨421499, by rfl⟩ : syracuseStep 2247997 = 842999) (by norm_num)
theorem B2997329 : Blo 1997435 2997329 := bstep (se 2 (by rfl) ⟨1123998, by rfl⟩ : syracuseStep 2997329 = 2247997) B2247997
theorem B1998219 : Blo 1997435 1998219 := bstep (se 1 (by rfl) ⟨1498664, by rfl⟩ : syracuseStep 1998219 = 2997329) B2997329
theorem B6744005 : Blo 1997435 6744005 := bbase (se 4 (by rfl) ⟨632250, by rfl⟩ : syracuseStep 6744005 = 1264501) (by norm_num)
theorem B4496003 : Blo 1997435 4496003 := bstep (se 1 (by rfl) ⟨3372002, by rfl⟩ : syracuseStep 4496003 = 6744005) B6744005
theorem B2997335 : Blo 1997435 2997335 := bstep (se 1 (by rfl) ⟨2248001, by rfl⟩ : syracuseStep 2997335 = 4496003) B4496003
theorem B1998223 : Blo 1997435 1998223 := bstep (se 1 (by rfl) ⟨1498667, by rfl⟩ : syracuseStep 1998223 = 2997335) B2997335
theorem B2997341 : Blo 1997435 2997341 := bbase (se 3 (by rfl) ⟨562001, by rfl⟩ : syracuseStep 2997341 = 1124003) (by norm_num)
theorem B1998227 : Blo 1997435 1998227 := bstep (se 1 (by rfl) ⟨1498670, by rfl⟩ : syracuseStep 1998227 = 2997341) B2997341
theorem B4496021 : Blo 1997435 4496021 := bbase (se 6 (by rfl) ⟨105375, by rfl⟩ : syracuseStep 4496021 = 210751) (by norm_num)
theorem B2997347 : Blo 1997435 2997347 := bstep (se 1 (by rfl) ⟨2248010, by rfl⟩ : syracuseStep 2997347 = 4496021) B4496021
theorem B1998231 : Blo 1997435 1998231 := bstep (se 1 (by rfl) ⟨1498673, by rfl⟩ : syracuseStep 1998231 = 2997347) B2997347
theorem B3200789 : Blo 1997435 3200789 := bbase (se 6 (by rfl) ⟨75018, by rfl⟩ : syracuseStep 3200789 = 150037) (by norm_num)
theorem B2133859 : Blo 1997435 2133859 := bstep (se 1 (by rfl) ⟨1600394, by rfl⟩ : syracuseStep 2133859 = 3200789) B3200789
theorem B2845145 : Blo 1997435 2845145 := bstep (se 2 (by rfl) ⟨1066929, by rfl⟩ : syracuseStep 2845145 = 2133859) B2133859
theorem B7587053 : Blo 1997435 7587053 := bstep (se 3 (by rfl) ⟨1422572, by rfl⟩ : syracuseStep 7587053 = 2845145) B2845145
theorem B5058035 : Blo 1997435 5058035 := bstep (se 1 (by rfl) ⟨3793526, by rfl⟩ : syracuseStep 5058035 = 7587053) B7587053
theorem B3372023 : Blo 1997435 3372023 := bstep (se 1 (by rfl) ⟨2529017, by rfl⟩ : syracuseStep 3372023 = 5058035) B5058035
theorem B2248015 : Blo 1997435 2248015 := bstep (se 1 (by rfl) ⟨1686011, by rfl⟩ : syracuseStep 2248015 = 3372023) B3372023
theorem B2997353 : Blo 1997435 2997353 := bstep (se 2 (by rfl) ⟨1124007, by rfl⟩ : syracuseStep 2997353 = 2248015) B2248015
theorem B1998235 : Blo 1997435 1998235 := bstep (se 1 (by rfl) ⟨1498676, by rfl⟩ : syracuseStep 1998235 = 2997353) B2997353
theorem B2433349 : Blo 1997435 2433349 := bbase (se 4 (by rfl) ⟨228126, by rfl⟩ : syracuseStep 2433349 = 456253) (by norm_num)
theorem B3244465 : Blo 1997435 3244465 := bstep (se 2 (by rfl) ⟨1216674, by rfl⟩ : syracuseStep 3244465 = 2433349) B2433349
theorem B4325953 : Blo 1997435 4325953 := bstep (se 2 (by rfl) ⟨1622232, by rfl⟩ : syracuseStep 4325953 = 3244465) B3244465
theorem B5767937 : Blo 1997435 5767937 := bstep (se 2 (by rfl) ⟨2162976, by rfl⟩ : syracuseStep 5767937 = 4325953) B4325953
theorem B3845291 : Blo 1997435 3845291 := bstep (se 1 (by rfl) ⟨2883968, by rfl⟩ : syracuseStep 3845291 = 5767937) B5767937
theorem B10254109 : Blo 1997435 10254109 := bstep (se 3 (by rfl) ⟨1922645, by rfl⟩ : syracuseStep 10254109 = 3845291) B3845291
theorem B13672145 : Blo 1997435 13672145 := bstep (se 2 (by rfl) ⟨5127054, by rfl⟩ : syracuseStep 13672145 = 10254109) B10254109
theorem B9114763 : Blo 1997435 9114763 := bstep (se 1 (by rfl) ⟨6836072, by rfl⟩ : syracuseStep 9114763 = 13672145) B13672145
theorem B12153017 : Blo 1997435 12153017 := bstep (se 2 (by rfl) ⟨4557381, by rfl⟩ : syracuseStep 12153017 = 9114763) B9114763
theorem B32408045 : Blo 1997435 32408045 := bstep (se 3 (by rfl) ⟨6076508, by rfl⟩ : syracuseStep 32408045 = 12153017) B12153017
theorem B21605363 : Blo 1997435 21605363 := bstep (se 1 (by rfl) ⟨16204022, by rfl⟩ : syracuseStep 21605363 = 32408045) B32408045
theorem B14403575 : Blo 1997435 14403575 := bstep (se 1 (by rfl) ⟨10802681, by rfl⟩ : syracuseStep 14403575 = 21605363) B21605363
theorem B9602383 : Blo 1997435 9602383 := bstep (se 1 (by rfl) ⟨7201787, by rfl⟩ : syracuseStep 9602383 = 14403575) B14403575
theorem B12803177 : Blo 1997435 12803177 := bstep (se 2 (by rfl) ⟨4801191, by rfl⟩ : syracuseStep 12803177 = 9602383) B9602383
theorem B8535451 : Blo 1997435 8535451 := bstep (se 1 (by rfl) ⟨6401588, by rfl⟩ : syracuseStep 8535451 = 12803177) B12803177
theorem B11380601 : Blo 1997435 11380601 := bstep (se 2 (by rfl) ⟨4267725, by rfl⟩ : syracuseStep 11380601 = 8535451) B8535451
theorem B7587067 : Blo 1997435 7587067 := bstep (se 1 (by rfl) ⟨5690300, by rfl⟩ : syracuseStep 7587067 = 11380601) B11380601
theorem B10116089 : Blo 1997435 10116089 := bstep (se 2 (by rfl) ⟨3793533, by rfl⟩ : syracuseStep 10116089 = 7587067) B7587067
theorem B6744059 : Blo 1997435 6744059 := bstep (se 1 (by rfl) ⟨5058044, by rfl⟩ : syracuseStep 6744059 = 10116089) B10116089
theorem B4496039 : Blo 1997435 4496039 := bstep (se 1 (by rfl) ⟨3372029, by rfl⟩ : syracuseStep 4496039 = 6744059) B6744059
theorem B2997359 : Blo 1997435 2997359 := bstep (se 1 (by rfl) ⟨2248019, by rfl⟩ : syracuseStep 2997359 = 4496039) B4496039
theorem B1998239 : Blo 1997435 1998239 := bstep (se 1 (by rfl) ⟨1498679, by rfl⟩ : syracuseStep 1998239 = 2997359) B2997359
theorem B2997365 : Blo 1997435 2997365 := bbase (se 5 (by rfl) ⟨140501, by rfl⟩ : syracuseStep 2997365 = 281003) (by norm_num)
theorem B1998243 : Blo 1997435 1998243 := bstep (se 1 (by rfl) ⟨1498682, by rfl⟩ : syracuseStep 1998243 = 2997365) B2997365
theorem B3793549 : Blo 1997435 3793549 := bbase (se 3 (by rfl) ⟨711290, by rfl⟩ : syracuseStep 3793549 = 1422581) (by norm_num)
theorem B5058065 : Blo 1997435 5058065 := bstep (se 2 (by rfl) ⟨1896774, by rfl⟩ : syracuseStep 5058065 = 3793549) B3793549
theorem B3372043 : Blo 1997435 3372043 := bstep (se 1 (by rfl) ⟨2529032, by rfl⟩ : syracuseStep 3372043 = 5058065) B5058065
theorem B4496057 : Blo 1997435 4496057 := bstep (se 2 (by rfl) ⟨1686021, by rfl⟩ : syracuseStep 4496057 = 3372043) B3372043
theorem B2997371 : Blo 1997435 2997371 := bstep (se 1 (by rfl) ⟨2248028, by rfl⟩ : syracuseStep 2997371 = 4496057) B4496057
theorem B1998247 : Blo 1997435 1998247 := bstep (se 1 (by rfl) ⟨1498685, by rfl⟩ : syracuseStep 1998247 = 2997371) B2997371
theorem B2248033 : Blo 1997435 2248033 := bbase (se 2 (by rfl) ⟨843012, by rfl⟩ : syracuseStep 2248033 = 1686025) (by norm_num)
theorem B2997377 : Blo 1997435 2997377 := bstep (se 2 (by rfl) ⟨1124016, by rfl⟩ : syracuseStep 2997377 = 2248033) B2248033
theorem B1998251 : Blo 1997435 1998251 := bstep (se 1 (by rfl) ⟨1498688, by rfl⟩ : syracuseStep 1998251 = 2997377) B2997377
theorem B5058085 : Blo 1997435 5058085 := bbase (se 4 (by rfl) ⟨474195, by rfl⟩ : syracuseStep 5058085 = 948391) (by norm_num)
theorem B6744113 : Blo 1997435 6744113 := bstep (se 2 (by rfl) ⟨2529042, by rfl⟩ : syracuseStep 6744113 = 5058085) B5058085
theorem B4496075 : Blo 1997435 4496075 := bstep (se 1 (by rfl) ⟨3372056, by rfl⟩ : syracuseStep 4496075 = 6744113) B6744113
theorem B2997383 : Blo 1997435 2997383 := bstep (se 1 (by rfl) ⟨2248037, by rfl⟩ : syracuseStep 2997383 = 4496075) B4496075
theorem B1998255 : Blo 1997435 1998255 := bstep (se 1 (by rfl) ⟨1498691, by rfl⟩ : syracuseStep 1998255 = 2997383) B2997383
theorem B2997389 : Blo 1997435 2997389 := bbase (se 3 (by rfl) ⟨562010, by rfl⟩ : syracuseStep 2997389 = 1124021) (by norm_num)
theorem B1998259 : Blo 1997435 1998259 := bstep (se 1 (by rfl) ⟨1498694, by rfl⟩ : syracuseStep 1998259 = 2997389) B2997389
theorem B4496093 : Blo 1997435 4496093 := bbase (se 3 (by rfl) ⟨843017, by rfl⟩ : syracuseStep 4496093 = 1686035) (by norm_num)
theorem B2997395 : Blo 1997435 2997395 := bstep (se 1 (by rfl) ⟨2248046, by rfl⟩ : syracuseStep 2997395 = 4496093) B4496093
theorem B1998263 : Blo 1997435 1998263 := bstep (se 1 (by rfl) ⟨1498697, by rfl⟩ : syracuseStep 1998263 = 2997395) B2997395
theorem B3372077 : Blo 1997435 3372077 := bbase (se 3 (by rfl) ⟨632264, by rfl⟩ : syracuseStep 3372077 = 1264529) (by norm_num)
theorem B2248051 : Blo 1997435 2248051 := bstep (se 1 (by rfl) ⟨1686038, by rfl⟩ : syracuseStep 2248051 = 3372077) B3372077
theorem B2997401 : Blo 1997435 2997401 := bstep (se 2 (by rfl) ⟨1124025, by rfl⟩ : syracuseStep 2997401 = 2248051) B2248051
theorem B1998267 : Blo 1997435 1998267 := bstep (se 1 (by rfl) ⟨1498700, by rfl⟩ : syracuseStep 1998267 = 2997401) B2997401
theorem B7300165 : Blo 1997435 7300165 := bbase (se 4 (by rfl) ⟨684390, by rfl⟩ : syracuseStep 7300165 = 1368781) (by norm_num)
theorem B9733553 : Blo 1997435 9733553 := bstep (se 2 (by rfl) ⟨3650082, by rfl⟩ : syracuseStep 9733553 = 7300165) B7300165
theorem B6489035 : Blo 1997435 6489035 := bstep (se 1 (by rfl) ⟨4866776, by rfl⟩ : syracuseStep 6489035 = 9733553) B9733553
theorem B4326023 : Blo 1997435 4326023 := bstep (se 1 (by rfl) ⟨3244517, by rfl⟩ : syracuseStep 4326023 = 6489035) B6489035
theorem B2884015 : Blo 1997435 2884015 := bstep (se 1 (by rfl) ⟨2163011, by rfl⟩ : syracuseStep 2884015 = 4326023) B4326023
theorem B3845353 : Blo 1997435 3845353 := bstep (se 2 (by rfl) ⟨1442007, by rfl⟩ : syracuseStep 3845353 = 2884015) B2884015
theorem B5127137 : Blo 1997435 5127137 := bstep (se 2 (by rfl) ⟨1922676, by rfl⟩ : syracuseStep 5127137 = 3845353) B3845353
theorem B3418091 : Blo 1997435 3418091 := bstep (se 1 (by rfl) ⟨2563568, by rfl⟩ : syracuseStep 3418091 = 5127137) B5127137
theorem B2278727 : Blo 1997435 2278727 := bstep (se 1 (by rfl) ⟨1709045, by rfl⟩ : syracuseStep 2278727 = 3418091) B3418091
theorem B24306421 : Blo 1997435 24306421 := bstep (se 5 (by rfl) ⟨1139363, by rfl⟩ : syracuseStep 24306421 = 2278727) B2278727
theorem B32408561 : Blo 1997435 32408561 := bstep (se 2 (by rfl) ⟨12153210, by rfl⟩ : syracuseStep 32408561 = 24306421) B24306421
theorem B21605707 : Blo 1997435 21605707 := bstep (se 1 (by rfl) ⟨16204280, by rfl⟩ : syracuseStep 21605707 = 32408561) B32408561
theorem B28807609 : Blo 1997435 28807609 := bstep (se 2 (by rfl) ⟨10802853, by rfl⟩ : syracuseStep 28807609 = 21605707) B21605707
theorem B38410145 : Blo 1997435 38410145 := bstep (se 2 (by rfl) ⟨14403804, by rfl⟩ : syracuseStep 38410145 = 28807609) B28807609
theorem B25606763 : Blo 1997435 25606763 := bstep (se 1 (by rfl) ⟨19205072, by rfl⟩ : syracuseStep 25606763 = 38410145) B38410145
theorem B17071175 : Blo 1997435 17071175 := bstep (se 1 (by rfl) ⟨12803381, by rfl⟩ : syracuseStep 17071175 = 25606763) B25606763
theorem B11380783 : Blo 1997435 11380783 := bstep (se 1 (by rfl) ⟨8535587, by rfl⟩ : syracuseStep 11380783 = 17071175) B17071175
theorem B15174377 : Blo 1997435 15174377 := bstep (se 2 (by rfl) ⟨5690391, by rfl⟩ : syracuseStep 15174377 = 11380783) B11380783
theorem B10116251 : Blo 1997435 10116251 := bstep (se 1 (by rfl) ⟨7587188, by rfl⟩ : syracuseStep 10116251 = 15174377) B15174377
theorem B6744167 : Blo 1997435 6744167 := bstep (se 1 (by rfl) ⟨5058125, by rfl⟩ : syracuseStep 6744167 = 10116251) B10116251
theorem B4496111 : Blo 1997435 4496111 := bstep (se 1 (by rfl) ⟨3372083, by rfl⟩ : syracuseStep 4496111 = 6744167) B6744167
theorem B2997407 : Blo 1997435 2997407 := bstep (se 1 (by rfl) ⟨2248055, by rfl⟩ : syracuseStep 2997407 = 4496111) B4496111
theorem B1998271 : Blo 1997435 1998271 := bstep (se 1 (by rfl) ⟨1498703, by rfl⟩ : syracuseStep 1998271 = 2997407) B2997407
theorem B2997413 : Blo 1997435 2997413 := bbase (se 4 (by rfl) ⟨281007, by rfl⟩ : syracuseStep 2997413 = 562015) (by norm_num)
theorem B1998275 : Blo 1997435 1998275 := bstep (se 1 (by rfl) ⟨1498706, by rfl⟩ : syracuseStep 1998275 = 2997413) B2997413
theorem B2529073 : Blo 1997435 2529073 := bbase (se 2 (by rfl) ⟨948402, by rfl⟩ : syracuseStep 2529073 = 1896805) (by norm_num)
theorem B3372097 : Blo 1997435 3372097 := bstep (se 2 (by rfl) ⟨1264536, by rfl⟩ : syracuseStep 3372097 = 2529073) B2529073
theorem B4496129 : Blo 1997435 4496129 := bstep (se 2 (by rfl) ⟨1686048, by rfl⟩ : syracuseStep 4496129 = 3372097) B3372097
theorem B2997419 : Blo 1997435 2997419 := bstep (se 1 (by rfl) ⟨2248064, by rfl⟩ : syracuseStep 2997419 = 4496129) B4496129
theorem B1998279 : Blo 1997435 1998279 := bstep (se 1 (by rfl) ⟨1498709, by rfl⟩ : syracuseStep 1998279 = 2997419) B2997419
theorem B2248069 : Blo 1997435 2248069 := bbase (se 4 (by rfl) ⟨210756, by rfl⟩ : syracuseStep 2248069 = 421513) (by norm_num)
theorem B2997425 : Blo 1997435 2997425 := bstep (se 2 (by rfl) ⟨1124034, by rfl⟩ : syracuseStep 2997425 = 2248069) B2248069
theorem B1998283 : Blo 1997435 1998283 := bstep (se 1 (by rfl) ⟨1498712, by rfl⟩ : syracuseStep 1998283 = 2997425) B2997425
theorem B4267829 : Blo 1997435 4267829 := bbase (se 5 (by rfl) ⟨200054, by rfl⟩ : syracuseStep 4267829 = 400109) (by norm_num)
theorem B2845219 : Blo 1997435 2845219 := bstep (se 1 (by rfl) ⟨2133914, by rfl⟩ : syracuseStep 2845219 = 4267829) B4267829
theorem B3793625 : Blo 1997435 3793625 := bstep (se 2 (by rfl) ⟨1422609, by rfl⟩ : syracuseStep 3793625 = 2845219) B2845219
theorem B2529083 : Blo 1997435 2529083 := bstep (se 1 (by rfl) ⟨1896812, by rfl⟩ : syracuseStep 2529083 = 3793625) B3793625
theorem B6744221 : Blo 1997435 6744221 := bstep (se 3 (by rfl) ⟨1264541, by rfl⟩ : syracuseStep 6744221 = 2529083) B2529083
theorem B4496147 : Blo 1997435 4496147 := bstep (se 1 (by rfl) ⟨3372110, by rfl⟩ : syracuseStep 4496147 = 6744221) B6744221
theorem B2997431 : Blo 1997435 2997431 := bstep (se 1 (by rfl) ⟨2248073, by rfl⟩ : syracuseStep 2997431 = 4496147) B4496147
theorem B1998287 : Blo 1997435 1998287 := bstep (se 1 (by rfl) ⟨1498715, by rfl⟩ : syracuseStep 1998287 = 2997431) B2997431
theorem B2997437 : Blo 1997435 2997437 := bbase (se 3 (by rfl) ⟨562019, by rfl⟩ : syracuseStep 2997437 = 1124039) (by norm_num)
theorem B1998291 : Blo 1997435 1998291 := bstep (se 1 (by rfl) ⟨1498718, by rfl⟩ : syracuseStep 1998291 = 2997437) B2997437
theorem B4496165 : Blo 1997435 4496165 := bbase (se 4 (by rfl) ⟨421515, by rfl⟩ : syracuseStep 4496165 = 843031) (by norm_num)
theorem B2997443 : Blo 1997435 2997443 := bstep (se 1 (by rfl) ⟨2248082, by rfl⟩ : syracuseStep 2997443 = 4496165) B4496165
theorem B1998295 : Blo 1997435 1998295 := bstep (se 1 (by rfl) ⟨1498721, by rfl⟩ : syracuseStep 1998295 = 2997443) B2997443
theorem B5058197 : Blo 1997435 5058197 := bbase (se 6 (by rfl) ⟨118551, by rfl⟩ : syracuseStep 5058197 = 237103) (by norm_num)
theorem B3372131 : Blo 1997435 3372131 := bstep (se 1 (by rfl) ⟨2529098, by rfl⟩ : syracuseStep 3372131 = 5058197) B5058197
theorem B2248087 : Blo 1997435 2248087 := bstep (se 1 (by rfl) ⟨1686065, by rfl⟩ : syracuseStep 2248087 = 3372131) B3372131
theorem B2997449 : Blo 1997435 2997449 := bstep (se 2 (by rfl) ⟨1124043, by rfl⟩ : syracuseStep 2997449 = 2248087) B2248087
theorem B1998299 : Blo 1997435 1998299 := bstep (se 1 (by rfl) ⟨1498724, by rfl⟩ : syracuseStep 1998299 = 2997449) B2997449
theorem B2400673 : Blo 1997435 2400673 := bbase (se 2 (by rfl) ⟨900252, by rfl⟩ : syracuseStep 2400673 = 1800505) (by norm_num)
theorem B3200897 : Blo 1997435 3200897 := bstep (se 2 (by rfl) ⟨1200336, by rfl⟩ : syracuseStep 3200897 = 2400673) B2400673
theorem B8535725 : Blo 1997435 8535725 := bstep (se 3 (by rfl) ⟨1600448, by rfl⟩ : syracuseStep 8535725 = 3200897) B3200897
theorem B5690483 : Blo 1997435 5690483 := bstep (se 1 (by rfl) ⟨4267862, by rfl⟩ : syracuseStep 5690483 = 8535725) B8535725
theorem B3793655 : Blo 1997435 3793655 := bstep (se 1 (by rfl) ⟨2845241, by rfl⟩ : syracuseStep 3793655 = 5690483) B5690483
theorem B10116413 : Blo 1997435 10116413 := bstep (se 3 (by rfl) ⟨1896827, by rfl⟩ : syracuseStep 10116413 = 3793655) B3793655
theorem B6744275 : Blo 1997435 6744275 := bstep (se 1 (by rfl) ⟨5058206, by rfl⟩ : syracuseStep 6744275 = 10116413) B10116413
theorem B4496183 : Blo 1997435 4496183 := bstep (se 1 (by rfl) ⟨3372137, by rfl⟩ : syracuseStep 4496183 = 6744275) B6744275
theorem B2997455 : Blo 1997435 2997455 := bstep (se 1 (by rfl) ⟨2248091, by rfl⟩ : syracuseStep 2997455 = 4496183) B4496183
theorem B1998303 : Blo 1997435 1998303 := bstep (se 1 (by rfl) ⟨1498727, by rfl⟩ : syracuseStep 1998303 = 2997455) B2997455
theorem B2997461 : Blo 1997435 2997461 := bbase (se 7 (by rfl) ⟨35126, by rfl⟩ : syracuseStep 2997461 = 70253) (by norm_num)
theorem B1998307 : Blo 1997435 1998307 := bstep (se 1 (by rfl) ⟨1498730, by rfl⟩ : syracuseStep 1998307 = 2997461) B2997461
theorem B2845253 : Blo 1997435 2845253 := bbase (se 4 (by rfl) ⟨266742, by rfl⟩ : syracuseStep 2845253 = 533485) (by norm_num)
theorem B7587341 : Blo 1997435 7587341 := bstep (se 3 (by rfl) ⟨1422626, by rfl⟩ : syracuseStep 7587341 = 2845253) B2845253
theorem B5058227 : Blo 1997435 5058227 := bstep (se 1 (by rfl) ⟨3793670, by rfl⟩ : syracuseStep 5058227 = 7587341) B7587341
theorem B3372151 : Blo 1997435 3372151 := bstep (se 1 (by rfl) ⟨2529113, by rfl⟩ : syracuseStep 3372151 = 5058227) B5058227
theorem B4496201 : Blo 1997435 4496201 := bstep (se 2 (by rfl) ⟨1686075, by rfl⟩ : syracuseStep 4496201 = 3372151) B3372151
theorem B2997467 : Blo 1997435 2997467 := bstep (se 1 (by rfl) ⟨2248100, by rfl⟩ : syracuseStep 2997467 = 4496201) B4496201
theorem B1998311 : Blo 1997435 1998311 := bstep (se 1 (by rfl) ⟨1498733, by rfl⟩ : syracuseStep 1998311 = 2997467) B2997467
theorem B2248105 : Blo 1997435 2248105 := bbase (se 2 (by rfl) ⟨843039, by rfl⟩ : syracuseStep 2248105 = 1686079) (by norm_num)
theorem B2997473 : Blo 1997435 2997473 := bstep (se 2 (by rfl) ⟨1124052, by rfl⟩ : syracuseStep 2997473 = 2248105) B2248105
theorem B1998315 : Blo 1997435 1998315 := bstep (se 1 (by rfl) ⟨1498736, by rfl⟩ : syracuseStep 1998315 = 2997473) B2997473
theorem B6401845 : Blo 1997435 6401845 := bbase (se 5 (by rfl) ⟨300086, by rfl⟩ : syracuseStep 6401845 = 600173) (by norm_num)
theorem B8535793 : Blo 1997435 8535793 := bstep (se 2 (by rfl) ⟨3200922, by rfl⟩ : syracuseStep 8535793 = 6401845) B6401845
theorem B11381057 : Blo 1997435 11381057 := bstep (se 2 (by rfl) ⟨4267896, by rfl⟩ : syracuseStep 11381057 = 8535793) B8535793
theorem B7587371 : Blo 1997435 7587371 := bstep (se 1 (by rfl) ⟨5690528, by rfl⟩ : syracuseStep 7587371 = 11381057) B11381057
theorem B5058247 : Blo 1997435 5058247 := bstep (se 1 (by rfl) ⟨3793685, by rfl⟩ : syracuseStep 5058247 = 7587371) B7587371
theorem B6744329 : Blo 1997435 6744329 := bstep (se 2 (by rfl) ⟨2529123, by rfl⟩ : syracuseStep 6744329 = 5058247) B5058247
theorem B4496219 : Blo 1997435 4496219 := bstep (se 1 (by rfl) ⟨3372164, by rfl⟩ : syracuseStep 4496219 = 6744329) B6744329
theorem B2997479 : Blo 1997435 2997479 := bstep (se 1 (by rfl) ⟨2248109, by rfl⟩ : syracuseStep 2997479 = 4496219) B4496219
theorem B1998319 : Blo 1997435 1998319 := bstep (se 1 (by rfl) ⟨1498739, by rfl⟩ : syracuseStep 1998319 = 2997479) B2997479
theorem B2997485 : Blo 1997435 2997485 := bbase (se 3 (by rfl) ⟨562028, by rfl⟩ : syracuseStep 2997485 = 1124057) (by norm_num)
theorem B1998323 : Blo 1997435 1998323 := bstep (se 1 (by rfl) ⟨1498742, by rfl⟩ : syracuseStep 1998323 = 2997485) B2997485
theorem B4496237 : Blo 1997435 4496237 := bbase (se 3 (by rfl) ⟨843044, by rfl⟩ : syracuseStep 4496237 = 1686089) (by norm_num)
theorem B2997491 : Blo 1997435 2997491 := bstep (se 1 (by rfl) ⟨2248118, by rfl⟩ : syracuseStep 2997491 = 4496237) B4496237
theorem B1998327 : Blo 1997435 1998327 := bstep (se 1 (by rfl) ⟨1498745, by rfl⟩ : syracuseStep 1998327 = 2997491) B2997491
theorem B3793709 : Blo 1997435 3793709 := bbase (se 3 (by rfl) ⟨711320, by rfl⟩ : syracuseStep 3793709 = 1422641) (by norm_num)
theorem B2529139 : Blo 1997435 2529139 := bstep (se 1 (by rfl) ⟨1896854, by rfl⟩ : syracuseStep 2529139 = 3793709) B3793709
theorem B3372185 : Blo 1997435 3372185 := bstep (se 2 (by rfl) ⟨1264569, by rfl⟩ : syracuseStep 3372185 = 2529139) B2529139
theorem B2248123 : Blo 1997435 2248123 := bstep (se 1 (by rfl) ⟨1686092, by rfl⟩ : syracuseStep 2248123 = 3372185) B3372185
theorem B2997497 : Blo 1997435 2997497 := bstep (se 2 (by rfl) ⟨1124061, by rfl⟩ : syracuseStep 2997497 = 2248123) B2248123
theorem B1998331 : Blo 1997435 1998331 := bstep (se 1 (by rfl) ⟨1498748, by rfl⟩ : syracuseStep 1998331 = 2997497) B2997497
theorem B2341405 : Blo 1997435 2341405 := bbase (se 3 (by rfl) ⟨439013, by rfl⟩ : syracuseStep 2341405 = 878027) (by norm_num)
theorem B12487493 : Blo 1997435 12487493 := bstep (se 4 (by rfl) ⟨1170702, by rfl⟩ : syracuseStep 12487493 = 2341405) B2341405
theorem B8324995 : Blo 1997435 8324995 := bstep (se 1 (by rfl) ⟨6243746, by rfl⟩ : syracuseStep 8324995 = 12487493) B12487493
theorem B11099993 : Blo 1997435 11099993 := bstep (se 2 (by rfl) ⟨4162497, by rfl⟩ : syracuseStep 11099993 = 8324995) B8324995
theorem B29599981 : Blo 1997435 29599981 := bstep (se 3 (by rfl) ⟨5549996, by rfl⟩ : syracuseStep 29599981 = 11099993) B11099993
theorem B157866565 : Blo 1997435 157866565 := bstep (se 4 (by rfl) ⟨14799990, by rfl⟩ : syracuseStep 157866565 = 29599981) B29599981
theorem B210488753 : Blo 1997435 210488753 := bstep (se 2 (by rfl) ⟨78933282, by rfl⟩ : syracuseStep 210488753 = 157866565) B157866565
theorem B561303341 : Blo 1997435 561303341 := bstep (se 3 (by rfl) ⟨105244376, by rfl⟩ : syracuseStep 561303341 = 210488753) B210488753
theorem B374202227 : Blo 1997435 374202227 := bstep (se 1 (by rfl) ⟨280651670, by rfl⟩ : syracuseStep 374202227 = 561303341) B561303341
theorem B997872605 : Blo 1997435 997872605 := bstep (se 3 (by rfl) ⟨187101113, by rfl⟩ : syracuseStep 997872605 = 374202227) B374202227
theorem B665248403 : Blo 1997435 665248403 := bstep (se 1 (by rfl) ⟨498936302, by rfl⟩ : syracuseStep 665248403 = 997872605) B997872605
theorem B443498935 : Blo 1997435 443498935 := bstep (se 1 (by rfl) ⟨332624201, by rfl⟩ : syracuseStep 443498935 = 665248403) B665248403
theorem B591331913 : Blo 1997435 591331913 := bstep (se 2 (by rfl) ⟨221749467, by rfl⟩ : syracuseStep 591331913 = 443498935) B443498935
theorem B394221275 : Blo 1997435 394221275 := bstep (se 1 (by rfl) ⟨295665956, by rfl⟩ : syracuseStep 394221275 = 591331913) B591331913
theorem B262814183 : Blo 1997435 262814183 := bstep (se 1 (by rfl) ⟨197110637, by rfl⟩ : syracuseStep 262814183 = 394221275) B394221275
theorem B175209455 : Blo 1997435 175209455 := bstep (se 1 (by rfl) ⟨131407091, by rfl⟩ : syracuseStep 175209455 = 262814183) B262814183
theorem B116806303 : Blo 1997435 116806303 := bstep (se 1 (by rfl) ⟨87604727, by rfl⟩ : syracuseStep 116806303 = 175209455) B175209455
theorem B622966949 : Blo 1997435 622966949 := bstep (se 4 (by rfl) ⟨58403151, by rfl⟩ : syracuseStep 622966949 = 116806303) B116806303
theorem B415311299 : Blo 1997435 415311299 := bstep (se 1 (by rfl) ⟨311483474, by rfl⟩ : syracuseStep 415311299 = 622966949) B622966949
theorem B276874199 : Blo 1997435 276874199 := bstep (se 1 (by rfl) ⟨207655649, by rfl⟩ : syracuseStep 276874199 = 415311299) B415311299
theorem B184582799 : Blo 1997435 184582799 := bstep (se 1 (by rfl) ⟨138437099, by rfl⟩ : syracuseStep 184582799 = 276874199) B276874199
theorem B123055199 : Blo 1997435 123055199 := bstep (se 1 (by rfl) ⟨92291399, by rfl⟩ : syracuseStep 123055199 = 184582799) B184582799
theorem B82036799 : Blo 1997435 82036799 := bstep (se 1 (by rfl) ⟨61527599, by rfl⟩ : syracuseStep 82036799 = 123055199) B123055199
theorem B54691199 : Blo 1997435 54691199 := bstep (se 1 (by rfl) ⟨41018399, by rfl⟩ : syracuseStep 54691199 = 82036799) B82036799
theorem B36460799 : Blo 1997435 36460799 := bstep (se 1 (by rfl) ⟨27345599, by rfl⟩ : syracuseStep 36460799 = 54691199) B54691199
theorem B24307199 : Blo 1997435 24307199 := bstep (se 1 (by rfl) ⟨18230399, by rfl⟩ : syracuseStep 24307199 = 36460799) B36460799
theorem B16204799 : Blo 1997435 16204799 := bstep (se 1 (by rfl) ⟨12153599, by rfl⟩ : syracuseStep 16204799 = 24307199) B24307199
theorem B43212797 : Blo 1997435 43212797 := bstep (se 3 (by rfl) ⟨8102399, by rfl⟩ : syracuseStep 43212797 = 16204799) B16204799
theorem B28808531 : Blo 1997435 28808531 := bstep (se 1 (by rfl) ⟨21606398, by rfl⟩ : syracuseStep 28808531 = 43212797) B43212797
theorem B19205687 : Blo 1997435 19205687 := bstep (se 1 (by rfl) ⟨14404265, by rfl⟩ : syracuseStep 19205687 = 28808531) B28808531
theorem B51215165 : Blo 1997435 51215165 := bstep (se 3 (by rfl) ⟨9602843, by rfl⟩ : syracuseStep 51215165 = 19205687) B19205687
theorem B34143443 : Blo 1997435 34143443 := bstep (se 1 (by rfl) ⟨25607582, by rfl⟩ : syracuseStep 34143443 = 51215165) B51215165
theorem B22762295 : Blo 1997435 22762295 := bstep (se 1 (by rfl) ⟨17071721, by rfl⟩ : syracuseStep 22762295 = 34143443) B34143443
theorem B15174863 : Blo 1997435 15174863 := bstep (se 1 (by rfl) ⟨11381147, by rfl⟩ : syracuseStep 15174863 = 22762295) B22762295
theorem B10116575 : Blo 1997435 10116575 := bstep (se 1 (by rfl) ⟨7587431, by rfl⟩ : syracuseStep 10116575 = 15174863) B15174863
theorem B6744383 : Blo 1997435 6744383 := bstep (se 1 (by rfl) ⟨5058287, by rfl⟩ : syracuseStep 6744383 = 10116575) B10116575
theorem B4496255 : Blo 1997435 4496255 := bstep (se 1 (by rfl) ⟨3372191, by rfl⟩ : syracuseStep 4496255 = 6744383) B6744383
theorem B2997503 : Blo 1997435 2997503 := bstep (se 1 (by rfl) ⟨2248127, by rfl⟩ : syracuseStep 2997503 = 4496255) B4496255
theorem B1998335 : Blo 1997435 1998335 := bstep (se 1 (by rfl) ⟨1498751, by rfl⟩ : syracuseStep 1998335 = 2997503) B2997503
theorem B2997509 : Blo 1997435 2997509 := bbase (se 4 (by rfl) ⟨281016, by rfl⟩ : syracuseStep 2997509 = 562033) (by norm_num)
theorem B1998339 : Blo 1997435 1998339 := bstep (se 1 (by rfl) ⟨1498754, by rfl⟩ : syracuseStep 1998339 = 2997509) B2997509
theorem B3372205 : Blo 1997435 3372205 := bbase (se 3 (by rfl) ⟨632288, by rfl⟩ : syracuseStep 3372205 = 1264577) (by norm_num)
theorem B4496273 : Blo 1997435 4496273 := bstep (se 2 (by rfl) ⟨1686102, by rfl⟩ : syracuseStep 4496273 = 3372205) B3372205
theorem B2997515 : Blo 1997435 2997515 := bstep (se 1 (by rfl) ⟨2248136, by rfl⟩ : syracuseStep 2997515 = 4496273) B4496273
theorem B1998343 : Blo 1997435 1998343 := bstep (se 1 (by rfl) ⟨1498757, by rfl⟩ : syracuseStep 1998343 = 2997515) B2997515
theorem B2248141 : Blo 1997435 2248141 := bbase (se 3 (by rfl) ⟨421526, by rfl⟩ : syracuseStep 2248141 = 843053) (by norm_num)
theorem B2997521 : Blo 1997435 2997521 := bstep (se 2 (by rfl) ⟨1124070, by rfl⟩ : syracuseStep 2997521 = 2248141) B2248141
theorem B1998347 : Blo 1997435 1998347 := bstep (se 1 (by rfl) ⟨1498760, by rfl⟩ : syracuseStep 1998347 = 2997521) B2997521
theorem B6744437 : Blo 1997435 6744437 := bbase (se 5 (by rfl) ⟨316145, by rfl⟩ : syracuseStep 6744437 = 632291) (by norm_num)
theorem B4496291 : Blo 1997435 4496291 := bstep (se 1 (by rfl) ⟨3372218, by rfl⟩ : syracuseStep 4496291 = 6744437) B6744437
theorem B2997527 : Blo 1997435 2997527 := bstep (se 1 (by rfl) ⟨2248145, by rfl⟩ : syracuseStep 2997527 = 4496291) B4496291
theorem B1998351 : Blo 1997435 1998351 := bstep (se 1 (by rfl) ⟨1498763, by rfl⟩ : syracuseStep 1998351 = 2997527) B2997527
theorem B2997533 : Blo 1997435 2997533 := bbase (se 3 (by rfl) ⟨562037, by rfl⟩ : syracuseStep 2997533 = 1124075) (by norm_num)
theorem B1998355 : Blo 1997435 1998355 := bstep (se 1 (by rfl) ⟨1498766, by rfl⟩ : syracuseStep 1998355 = 2997533) B2997533
theorem B4496309 : Blo 1997435 4496309 := bbase (se 5 (by rfl) ⟨210764, by rfl⟩ : syracuseStep 4496309 = 421529) (by norm_num)
theorem B2997539 : Blo 1997435 2997539 := bstep (se 1 (by rfl) ⟨2248154, by rfl⟩ : syracuseStep 2997539 = 4496309) B4496309
theorem B1998359 : Blo 1997435 1998359 := bstep (se 1 (by rfl) ⟨1498769, by rfl⟩ : syracuseStep 1998359 = 2997539) B2997539
theorem B9602981 : Blo 1997435 9602981 := bbase (se 4 (by rfl) ⟨900279, by rfl⟩ : syracuseStep 9602981 = 1800559) (by norm_num)
theorem B6401987 : Blo 1997435 6401987 := bstep (se 1 (by rfl) ⟨4801490, by rfl⟩ : syracuseStep 6401987 = 9602981) B9602981
theorem B4267991 : Blo 1997435 4267991 := bstep (se 1 (by rfl) ⟨3200993, by rfl⟩ : syracuseStep 4267991 = 6401987) B6401987
theorem B11381309 : Blo 1997435 11381309 := bstep (se 3 (by rfl) ⟨2133995, by rfl⟩ : syracuseStep 11381309 = 4267991) B4267991
theorem B7587539 : Blo 1997435 7587539 := bstep (se 1 (by rfl) ⟨5690654, by rfl⟩ : syracuseStep 7587539 = 11381309) B11381309
theorem B5058359 : Blo 1997435 5058359 := bstep (se 1 (by rfl) ⟨3793769, by rfl⟩ : syracuseStep 5058359 = 7587539) B7587539
theorem B3372239 : Blo 1997435 3372239 := bstep (se 1 (by rfl) ⟨2529179, by rfl⟩ : syracuseStep 3372239 = 5058359) B5058359
theorem B2248159 : Blo 1997435 2248159 := bstep (se 1 (by rfl) ⟨1686119, by rfl⟩ : syracuseStep 2248159 = 3372239) B3372239
theorem B2997545 : Blo 1997435 2997545 := bstep (se 2 (by rfl) ⟨1124079, by rfl⟩ : syracuseStep 2997545 = 2248159) B2248159
theorem B1998363 : Blo 1997435 1998363 := bstep (se 1 (by rfl) ⟨1498772, by rfl⟩ : syracuseStep 1998363 = 2997545) B2997545
theorem B2278837 : Blo 1997435 2278837 := bbase (se 5 (by rfl) ⟨106820, by rfl⟩ : syracuseStep 2278837 = 213641) (by norm_num)
theorem B12153797 : Blo 1997435 12153797 := bstep (se 4 (by rfl) ⟨1139418, by rfl⟩ : syracuseStep 12153797 = 2278837) B2278837
theorem B8102531 : Blo 1997435 8102531 := bstep (se 1 (by rfl) ⟨6076898, by rfl⟩ : syracuseStep 8102531 = 12153797) B12153797
theorem B21606749 : Blo 1997435 21606749 := bstep (se 3 (by rfl) ⟨4051265, by rfl⟩ : syracuseStep 21606749 = 8102531) B8102531
theorem B14404499 : Blo 1997435 14404499 := bstep (se 1 (by rfl) ⟨10803374, by rfl⟩ : syracuseStep 14404499 = 21606749) B21606749
theorem B9602999 : Blo 1997435 9602999 := bstep (se 1 (by rfl) ⟨7202249, by rfl⟩ : syracuseStep 9602999 = 14404499) B14404499
theorem B6401999 : Blo 1997435 6401999 := bstep (se 1 (by rfl) ⟨4801499, by rfl⟩ : syracuseStep 6401999 = 9602999) B9602999
theorem B4267999 : Blo 1997435 4267999 := bstep (se 1 (by rfl) ⟨3200999, by rfl⟩ : syracuseStep 4267999 = 6401999) B6401999
theorem B5690665 : Blo 1997435 5690665 := bstep (se 2 (by rfl) ⟨2133999, by rfl⟩ : syracuseStep 5690665 = 4267999) B4267999
theorem B7587553 : Blo 1997435 7587553 := bstep (se 2 (by rfl) ⟨2845332, by rfl⟩ : syracuseStep 7587553 = 5690665) B5690665
theorem B10116737 : Blo 1997435 10116737 := bstep (se 2 (by rfl) ⟨3793776, by rfl⟩ : syracuseStep 10116737 = 7587553) B7587553
theorem B6744491 : Blo 1997435 6744491 := bstep (se 1 (by rfl) ⟨5058368, by rfl⟩ : syracuseStep 6744491 = 10116737) B10116737
theorem B4496327 : Blo 1997435 4496327 := bstep (se 1 (by rfl) ⟨3372245, by rfl⟩ : syracuseStep 4496327 = 6744491) B6744491
theorem B2997551 : Blo 1997435 2997551 := bstep (se 1 (by rfl) ⟨2248163, by rfl⟩ : syracuseStep 2997551 = 4496327) B4496327
theorem B1998367 : Blo 1997435 1998367 := bstep (se 1 (by rfl) ⟨1498775, by rfl⟩ : syracuseStep 1998367 = 2997551) B2997551
theorem B2997557 : Blo 1997435 2997557 := bbase (se 5 (by rfl) ⟨140510, by rfl⟩ : syracuseStep 2997557 = 281021) (by norm_num)
theorem B1998371 : Blo 1997435 1998371 := bstep (se 1 (by rfl) ⟨1498778, by rfl⟩ : syracuseStep 1998371 = 2997557) B2997557
theorem B5058389 : Blo 1997435 5058389 := bbase (se 9 (by rfl) ⟨14819, by rfl⟩ : syracuseStep 5058389 = 29639) (by norm_num)
theorem B3372259 : Blo 1997435 3372259 := bstep (se 1 (by rfl) ⟨2529194, by rfl⟩ : syracuseStep 3372259 = 5058389) B5058389
theorem B4496345 : Blo 1997435 4496345 := bstep (se 2 (by rfl) ⟨1686129, by rfl⟩ : syracuseStep 4496345 = 3372259) B3372259
theorem B2997563 : Blo 1997435 2997563 := bstep (se 1 (by rfl) ⟨2248172, by rfl⟩ : syracuseStep 2997563 = 4496345) B4496345
theorem B1998375 : Blo 1997435 1998375 := bstep (se 1 (by rfl) ⟨1498781, by rfl⟩ : syracuseStep 1998375 = 2997563) B2997563
theorem B2248177 : Blo 1997435 2248177 := bbase (se 2 (by rfl) ⟨843066, by rfl⟩ : syracuseStep 2248177 = 1686133) (by norm_num)
theorem B2997569 : Blo 1997435 2997569 := bstep (se 2 (by rfl) ⟨1124088, by rfl⟩ : syracuseStep 2997569 = 2248177) B2248177
theorem B1998379 : Blo 1997435 1998379 := bstep (se 1 (by rfl) ⟨1498784, by rfl⟩ : syracuseStep 1998379 = 2997569) B2997569
theorem B2400769 : Blo 1997435 2400769 := bbase (se 2 (by rfl) ⟨900288, by rfl⟩ : syracuseStep 2400769 = 1800577) (by norm_num)
theorem B12804101 : Blo 1997435 12804101 := bstep (se 4 (by rfl) ⟨1200384, by rfl⟩ : syracuseStep 12804101 = 2400769) B2400769
theorem B8536067 : Blo 1997435 8536067 := bstep (se 1 (by rfl) ⟨6402050, by rfl⟩ : syracuseStep 8536067 = 12804101) B12804101
theorem B5690711 : Blo 1997435 5690711 := bstep (se 1 (by rfl) ⟨4268033, by rfl⟩ : syracuseStep 5690711 = 8536067) B8536067
theorem B3793807 : Blo 1997435 3793807 := bstep (se 1 (by rfl) ⟨2845355, by rfl⟩ : syracuseStep 3793807 = 5690711) B5690711
theorem B5058409 : Blo 1997435 5058409 := bstep (se 2 (by rfl) ⟨1896903, by rfl⟩ : syracuseStep 5058409 = 3793807) B3793807
theorem B6744545 : Blo 1997435 6744545 := bstep (se 2 (by rfl) ⟨2529204, by rfl⟩ : syracuseStep 6744545 = 5058409) B5058409
theorem B4496363 : Blo 1997435 4496363 := bstep (se 1 (by rfl) ⟨3372272, by rfl⟩ : syracuseStep 4496363 = 6744545) B6744545
theorem B2997575 : Blo 1997435 2997575 := bstep (se 1 (by rfl) ⟨2248181, by rfl⟩ : syracuseStep 2997575 = 4496363) B4496363
theorem B1998383 : Blo 1997435 1998383 := bstep (se 1 (by rfl) ⟨1498787, by rfl⟩ : syracuseStep 1998383 = 2997575) B2997575
theorem B2997581 : Blo 1997435 2997581 := bbase (se 3 (by rfl) ⟨562046, by rfl⟩ : syracuseStep 2997581 = 1124093) (by norm_num)
theorem B1998387 : Blo 1997435 1998387 := bstep (se 1 (by rfl) ⟨1498790, by rfl⟩ : syracuseStep 1998387 = 2997581) B2997581
theorem B4496381 : Blo 1997435 4496381 := bbase (se 3 (by rfl) ⟨843071, by rfl⟩ : syracuseStep 4496381 = 1686143) (by norm_num)
theorem B2997587 : Blo 1997435 2997587 := bstep (se 1 (by rfl) ⟨2248190, by rfl⟩ : syracuseStep 2997587 = 4496381) B4496381
theorem B1998391 : Blo 1997435 1998391 := bstep (se 1 (by rfl) ⟨1498793, by rfl⟩ : syracuseStep 1998391 = 2997587) B2997587
theorem B3372293 : Blo 1997435 3372293 := bbase (se 4 (by rfl) ⟨316152, by rfl⟩ : syracuseStep 3372293 = 632305) (by norm_num)
theorem B2248195 : Blo 1997435 2248195 := bstep (se 1 (by rfl) ⟨1686146, by rfl⟩ : syracuseStep 2248195 = 3372293) B3372293
theorem B2997593 : Blo 1997435 2997593 := bstep (se 2 (by rfl) ⟨1124097, by rfl⟩ : syracuseStep 2997593 = 2248195) B2248195
theorem B1998395 : Blo 1997435 1998395 := bstep (se 1 (by rfl) ⟨1498796, by rfl⟩ : syracuseStep 1998395 = 2997593) B2997593
theorem B15175349 : Blo 1997435 15175349 := bbase (se 5 (by rfl) ⟨711344, by rfl⟩ : syracuseStep 15175349 = 1422689) (by norm_num)
theorem B10116899 : Blo 1997435 10116899 := bstep (se 1 (by rfl) ⟨7587674, by rfl⟩ : syracuseStep 10116899 = 15175349) B15175349
theorem B6744599 : Blo 1997435 6744599 := bstep (se 1 (by rfl) ⟨5058449, by rfl⟩ : syracuseStep 6744599 = 10116899) B10116899
theorem B4496399 : Blo 1997435 4496399 := bstep (se 1 (by rfl) ⟨3372299, by rfl⟩ : syracuseStep 4496399 = 6744599) B6744599
theorem B2997599 : Blo 1997435 2997599 := bstep (se 1 (by rfl) ⟨2248199, by rfl⟩ : syracuseStep 2997599 = 4496399) B4496399
theorem B1998399 : Blo 1997435 1998399 := bstep (se 1 (by rfl) ⟨1498799, by rfl⟩ : syracuseStep 1998399 = 2997599) B2997599
theorem B2997605 : Blo 1997435 2997605 := bbase (se 4 (by rfl) ⟨281025, by rfl⟩ : syracuseStep 2997605 = 562051) (by norm_num)
theorem B1998403 : Blo 1997435 1998403 := bstep (se 1 (by rfl) ⟨1498802, by rfl⟩ : syracuseStep 1998403 = 2997605) B2997605
theorem B3793853 : Blo 1997435 3793853 := bbase (se 3 (by rfl) ⟨711347, by rfl⟩ : syracuseStep 3793853 = 1422695) (by norm_num)
theorem B2529235 : Blo 1997435 2529235 := bstep (se 1 (by rfl) ⟨1896926, by rfl⟩ : syracuseStep 2529235 = 3793853) B3793853
theorem B3372313 : Blo 1997435 3372313 := bstep (se 2 (by rfl) ⟨1264617, by rfl⟩ : syracuseStep 3372313 = 2529235) B2529235
theorem B4496417 : Blo 1997435 4496417 := bstep (se 2 (by rfl) ⟨1686156, by rfl⟩ : syracuseStep 4496417 = 3372313) B3372313
theorem B2997611 : Blo 1997435 2997611 := bstep (se 1 (by rfl) ⟨2248208, by rfl⟩ : syracuseStep 2997611 = 4496417) B4496417
theorem B1998407 : Blo 1997435 1998407 := bstep (se 1 (by rfl) ⟨1498805, by rfl⟩ : syracuseStep 1998407 = 2997611) B2997611
theorem B2248213 : Blo 1997435 2248213 := bbase (se 6 (by rfl) ⟨52692, by rfl⟩ : syracuseStep 2248213 = 105385) (by norm_num)
theorem B2997617 : Blo 1997435 2997617 := bstep (se 2 (by rfl) ⟨1124106, by rfl⟩ : syracuseStep 2997617 = 2248213) B2248213
theorem B1998411 : Blo 1997435 1998411 := bstep (se 1 (by rfl) ⟨1498808, by rfl⟩ : syracuseStep 1998411 = 2997617) B2997617
theorem B2529245 : Blo 1997435 2529245 := bbase (se 3 (by rfl) ⟨474233, by rfl⟩ : syracuseStep 2529245 = 948467) (by norm_num)
theorem B6744653 : Blo 1997435 6744653 := bstep (se 3 (by rfl) ⟨1264622, by rfl⟩ : syracuseStep 6744653 = 2529245) B2529245
theorem B4496435 : Blo 1997435 4496435 := bstep (se 1 (by rfl) ⟨3372326, by rfl⟩ : syracuseStep 4496435 = 6744653) B6744653
theorem B2997623 : Blo 1997435 2997623 := bstep (se 1 (by rfl) ⟨2248217, by rfl⟩ : syracuseStep 2997623 = 4496435) B4496435
theorem B1998415 : Blo 1997435 1998415 := bstep (se 1 (by rfl) ⟨1498811, by rfl⟩ : syracuseStep 1998415 = 2997623) B2997623
theorem B2997629 : Blo 1997435 2997629 := bbase (se 3 (by rfl) ⟨562055, by rfl⟩ : syracuseStep 2997629 = 1124111) (by norm_num)
theorem B1998419 : Blo 1997435 1998419 := bstep (se 1 (by rfl) ⟨1498814, by rfl⟩ : syracuseStep 1998419 = 2997629) B2997629
theorem B4496453 : Blo 1997435 4496453 := bbase (se 4 (by rfl) ⟨421542, by rfl⟩ : syracuseStep 4496453 = 843085) (by norm_num)
theorem B2997635 : Blo 1997435 2997635 := bstep (se 1 (by rfl) ⟨2248226, by rfl⟩ : syracuseStep 2997635 = 4496453) B4496453
theorem B1998423 : Blo 1997435 1998423 := bstep (se 1 (by rfl) ⟨1498817, by rfl⟩ : syracuseStep 1998423 = 2997635) B2997635
theorem B5690837 : Blo 1997435 5690837 := bbase (se 7 (by rfl) ⟨66689, by rfl⟩ : syracuseStep 5690837 = 133379) (by norm_num)
theorem B3793891 : Blo 1997435 3793891 := bstep (se 1 (by rfl) ⟨2845418, by rfl⟩ : syracuseStep 3793891 = 5690837) B5690837
theorem B5058521 : Blo 1997435 5058521 := bstep (se 2 (by rfl) ⟨1896945, by rfl⟩ : syracuseStep 5058521 = 3793891) B3793891
theorem B3372347 : Blo 1997435 3372347 := bstep (se 1 (by rfl) ⟨2529260, by rfl⟩ : syracuseStep 3372347 = 5058521) B5058521
theorem B2248231 : Blo 1997435 2248231 := bstep (se 1 (by rfl) ⟨1686173, by rfl⟩ : syracuseStep 2248231 = 3372347) B3372347
theorem B2997641 : Blo 1997435 2997641 := bstep (se 2 (by rfl) ⟨1124115, by rfl⟩ : syracuseStep 2997641 = 2248231) B2248231
theorem B1998427 : Blo 1997435 1998427 := bstep (se 1 (by rfl) ⟨1498820, by rfl⟩ : syracuseStep 1998427 = 2997641) B2997641
theorem B10117061 : Blo 1997435 10117061 := bbase (se 4 (by rfl) ⟨948474, by rfl⟩ : syracuseStep 10117061 = 1896949) (by norm_num)
theorem B6744707 : Blo 1997435 6744707 := bstep (se 1 (by rfl) ⟨5058530, by rfl⟩ : syracuseStep 6744707 = 10117061) B10117061
theorem B4496471 : Blo 1997435 4496471 := bstep (se 1 (by rfl) ⟨3372353, by rfl⟩ : syracuseStep 4496471 = 6744707) B6744707
theorem B2997647 : Blo 1997435 2997647 := bstep (se 1 (by rfl) ⟨2248235, by rfl⟩ : syracuseStep 2997647 = 4496471) B4496471
theorem B1998431 : Blo 1997435 1998431 := bstep (se 1 (by rfl) ⟨1498823, by rfl⟩ : syracuseStep 1998431 = 2997647) B2997647
theorem B2997653 : Blo 1997435 2997653 := bbase (se 6 (by rfl) ⟨70257, by rfl⟩ : syracuseStep 2997653 = 140515) (by norm_num)
theorem B1998435 : Blo 1997435 1998435 := bstep (se 1 (by rfl) ⟨1498826, by rfl⟩ : syracuseStep 1998435 = 2997653) B2997653
theorem B14601557 : Blo 1997435 14601557 := bbase (se 11 (by rfl) ⟨10694, by rfl⟩ : syracuseStep 14601557 = 21389) (by norm_num)
theorem B38937485 : Blo 1997435 38937485 := bstep (se 3 (by rfl) ⟨7300778, by rfl⟩ : syracuseStep 38937485 = 14601557) B14601557
theorem B25958323 : Blo 1997435 25958323 := bstep (se 1 (by rfl) ⟨19468742, by rfl⟩ : syracuseStep 25958323 = 38937485) B38937485
theorem B34611097 : Blo 1997435 34611097 := bstep (se 2 (by rfl) ⟨12979161, by rfl⟩ : syracuseStep 34611097 = 25958323) B25958323
theorem B46148129 : Blo 1997435 46148129 := bstep (se 2 (by rfl) ⟨17305548, by rfl⟩ : syracuseStep 46148129 = 34611097) B34611097
theorem B30765419 : Blo 1997435 30765419 := bstep (se 1 (by rfl) ⟨23074064, by rfl⟩ : syracuseStep 30765419 = 46148129) B46148129
theorem B20510279 : Blo 1997435 20510279 := bstep (se 1 (by rfl) ⟨15382709, by rfl⟩ : syracuseStep 20510279 = 30765419) B30765419
theorem B13673519 : Blo 1997435 13673519 := bstep (se 1 (by rfl) ⟨10255139, by rfl⟩ : syracuseStep 13673519 = 20510279) B20510279
theorem B9115679 : Blo 1997435 9115679 := bstep (se 1 (by rfl) ⟨6836759, by rfl⟩ : syracuseStep 9115679 = 13673519) B13673519
theorem B6077119 : Blo 1997435 6077119 := bstep (se 1 (by rfl) ⟨4557839, by rfl⟩ : syracuseStep 6077119 = 9115679) B9115679
theorem B8102825 : Blo 1997435 8102825 := bstep (se 2 (by rfl) ⟨3038559, by rfl⟩ : syracuseStep 8102825 = 6077119) B6077119
theorem B5401883 : Blo 1997435 5401883 := bstep (se 1 (by rfl) ⟨4051412, by rfl⟩ : syracuseStep 5401883 = 8102825) B8102825
theorem B3601255 : Blo 1997435 3601255 := bstep (se 1 (by rfl) ⟨2700941, by rfl⟩ : syracuseStep 3601255 = 5401883) B5401883
theorem B4801673 : Blo 1997435 4801673 := bstep (se 2 (by rfl) ⟨1800627, by rfl⟩ : syracuseStep 4801673 = 3601255) B3601255
theorem B3201115 : Blo 1997435 3201115 := bstep (se 1 (by rfl) ⟨2400836, by rfl⟩ : syracuseStep 3201115 = 4801673) B4801673
theorem B4268153 : Blo 1997435 4268153 := bstep (se 2 (by rfl) ⟨1600557, by rfl⟩ : syracuseStep 4268153 = 3201115) B3201115
theorem B11381741 : Blo 1997435 11381741 := bstep (se 3 (by rfl) ⟨2134076, by rfl⟩ : syracuseStep 11381741 = 4268153) B4268153
theorem B7587827 : Blo 1997435 7587827 := bstep (se 1 (by rfl) ⟨5690870, by rfl⟩ : syracuseStep 7587827 = 11381741) B11381741
theorem B5058551 : Blo 1997435 5058551 := bstep (se 1 (by rfl) ⟨3793913, by rfl⟩ : syracuseStep 5058551 = 7587827) B7587827
theorem B3372367 : Blo 1997435 3372367 := bstep (se 1 (by rfl) ⟨2529275, by rfl⟩ : syracuseStep 3372367 = 5058551) B5058551
theorem B4496489 : Blo 1997435 4496489 := bstep (se 2 (by rfl) ⟨1686183, by rfl⟩ : syracuseStep 4496489 = 3372367) B3372367
theorem B2997659 : Blo 1997435 2997659 := bstep (se 1 (by rfl) ⟨2248244, by rfl⟩ : syracuseStep 2997659 = 4496489) B4496489
theorem B1998439 : Blo 1997435 1998439 := bstep (se 1 (by rfl) ⟨1498829, by rfl⟩ : syracuseStep 1998439 = 2997659) B2997659
theorem B2248249 : Blo 1997435 2248249 := bbase (se 2 (by rfl) ⟨843093, by rfl⟩ : syracuseStep 2248249 = 1686187) (by norm_num)
theorem B2997665 : Blo 1997435 2997665 := bstep (se 2 (by rfl) ⟨1124124, by rfl⟩ : syracuseStep 2997665 = 2248249) B2248249
theorem B1998443 : Blo 1997435 1998443 := bstep (se 1 (by rfl) ⟨1498832, by rfl⟩ : syracuseStep 1998443 = 2997665) B2997665
theorem B2134085 : Blo 1997435 2134085 := bbase (se 4 (by rfl) ⟨200070, by rfl⟩ : syracuseStep 2134085 = 400141) (by norm_num)
theorem B5690893 : Blo 1997435 5690893 := bstep (se 3 (by rfl) ⟨1067042, by rfl⟩ : syracuseStep 5690893 = 2134085) B2134085
theorem B7587857 : Blo 1997435 7587857 := bstep (se 2 (by rfl) ⟨2845446, by rfl⟩ : syracuseStep 7587857 = 5690893) B5690893
theorem B5058571 : Blo 1997435 5058571 := bstep (se 1 (by rfl) ⟨3793928, by rfl⟩ : syracuseStep 5058571 = 7587857) B7587857
theorem B6744761 : Blo 1997435 6744761 := bstep (se 2 (by rfl) ⟨2529285, by rfl⟩ : syracuseStep 6744761 = 5058571) B5058571
theorem B4496507 : Blo 1997435 4496507 := bstep (se 1 (by rfl) ⟨3372380, by rfl⟩ : syracuseStep 4496507 = 6744761) B6744761
theorem B2997671 : Blo 1997435 2997671 := bstep (se 1 (by rfl) ⟨2248253, by rfl⟩ : syracuseStep 2997671 = 4496507) B4496507
theorem B1998447 : Blo 1997435 1998447 := bstep (se 1 (by rfl) ⟨1498835, by rfl⟩ : syracuseStep 1998447 = 2997671) B2997671
theorem B2997677 : Blo 1997435 2997677 := bbase (se 3 (by rfl) ⟨562064, by rfl⟩ : syracuseStep 2997677 = 1124129) (by norm_num)
theorem B1998451 : Blo 1997435 1998451 := bstep (se 1 (by rfl) ⟨1498838, by rfl⟩ : syracuseStep 1998451 = 2997677) B2997677
theorem B4496525 : Blo 1997435 4496525 := bbase (se 3 (by rfl) ⟨843098, by rfl⟩ : syracuseStep 4496525 = 1686197) (by norm_num)
theorem B2997683 : Blo 1997435 2997683 := bstep (se 1 (by rfl) ⟨2248262, by rfl⟩ : syracuseStep 2997683 = 4496525) B4496525
theorem B1998455 : Blo 1997435 1998455 := bstep (se 1 (by rfl) ⟨1498841, by rfl⟩ : syracuseStep 1998455 = 2997683) B2997683
theorem B2529301 : Blo 1997435 2529301 := bbase (se 6 (by rfl) ⟨59280, by rfl⟩ : syracuseStep 2529301 = 118561) (by norm_num)
theorem B3372401 : Blo 1997435 3372401 := bstep (se 2 (by rfl) ⟨1264650, by rfl⟩ : syracuseStep 3372401 = 2529301) B2529301
theorem B2248267 : Blo 1997435 2248267 := bstep (se 1 (by rfl) ⟨1686200, by rfl⟩ : syracuseStep 2248267 = 3372401) B3372401
theorem B2997689 : Blo 1997435 2997689 := bstep (se 2 (by rfl) ⟨1124133, by rfl⟩ : syracuseStep 2997689 = 2248267) B2248267
theorem B1998459 : Blo 1997435 1998459 := bstep (se 1 (by rfl) ⟨1498844, by rfl⟩ : syracuseStep 1998459 = 2997689) B2997689
theorem B6077189 : Blo 1997435 6077189 := bbase (se 4 (by rfl) ⟨569736, by rfl⟩ : syracuseStep 6077189 = 1139473) (by norm_num)
theorem B16205837 : Blo 1997435 16205837 := bstep (se 3 (by rfl) ⟨3038594, by rfl⟩ : syracuseStep 16205837 = 6077189) B6077189
theorem B43215565 : Blo 1997435 43215565 := bstep (se 3 (by rfl) ⟨8102918, by rfl⟩ : syracuseStep 43215565 = 16205837) B16205837
theorem B57620753 : Blo 1997435 57620753 := bstep (se 2 (by rfl) ⟨21607782, by rfl⟩ : syracuseStep 57620753 = 43215565) B43215565
theorem B38413835 : Blo 1997435 38413835 := bstep (se 1 (by rfl) ⟨28810376, by rfl⟩ : syracuseStep 38413835 = 57620753) B57620753
theorem B25609223 : Blo 1997435 25609223 := bstep (se 1 (by rfl) ⟨19206917, by rfl⟩ : syracuseStep 25609223 = 38413835) B38413835
theorem B17072815 : Blo 1997435 17072815 := bstep (se 1 (by rfl) ⟨12804611, by rfl⟩ : syracuseStep 17072815 = 25609223) B25609223
theorem B22763753 : Blo 1997435 22763753 := bstep (se 2 (by rfl) ⟨8536407, by rfl⟩ : syracuseStep 22763753 = 17072815) B17072815
theorem B15175835 : Blo 1997435 15175835 := bstep (se 1 (by rfl) ⟨11381876, by rfl⟩ : syracuseStep 15175835 = 22763753) B22763753
theorem B10117223 : Blo 1997435 10117223 := bstep (se 1 (by rfl) ⟨7587917, by rfl⟩ : syracuseStep 10117223 = 15175835) B15175835
theorem B6744815 : Blo 1997435 6744815 := bstep (se 1 (by rfl) ⟨5058611, by rfl⟩ : syracuseStep 6744815 = 10117223) B10117223
theorem B4496543 : Blo 1997435 4496543 := bstep (se 1 (by rfl) ⟨3372407, by rfl⟩ : syracuseStep 4496543 = 6744815) B6744815
theorem B2997695 : Blo 1997435 2997695 := bstep (se 1 (by rfl) ⟨2248271, by rfl⟩ : syracuseStep 2997695 = 4496543) B4496543
theorem B1998463 : Blo 1997435 1998463 := bstep (se 1 (by rfl) ⟨1498847, by rfl⟩ : syracuseStep 1998463 = 2997695) B2997695
theorem B2997701 : Blo 1997435 2997701 := bbase (se 4 (by rfl) ⟨281034, by rfl⟩ : syracuseStep 2997701 = 562069) (by norm_num)
theorem B1998467 : Blo 1997435 1998467 := bstep (se 1 (by rfl) ⟨1498850, by rfl⟩ : syracuseStep 1998467 = 2997701) B2997701
theorem B3372421 : Blo 1997435 3372421 := bbase (se 4 (by rfl) ⟨316164, by rfl⟩ : syracuseStep 3372421 = 632329) (by norm_num)
theorem B4496561 : Blo 1997435 4496561 := bstep (se 2 (by rfl) ⟨1686210, by rfl⟩ : syracuseStep 4496561 = 3372421) B3372421
theorem B2997707 : Blo 1997435 2997707 := bstep (se 1 (by rfl) ⟨2248280, by rfl⟩ : syracuseStep 2997707 = 4496561) B4496561
theorem B1998471 : Blo 1997435 1998471 := bstep (se 1 (by rfl) ⟨1498853, by rfl⟩ : syracuseStep 1998471 = 2997707) B2997707
theorem B2248285 : Blo 1997435 2248285 := bbase (se 3 (by rfl) ⟨421553, by rfl⟩ : syracuseStep 2248285 = 843107) (by norm_num)
theorem B2997713 : Blo 1997435 2997713 := bstep (se 2 (by rfl) ⟨1124142, by rfl⟩ : syracuseStep 2997713 = 2248285) B2248285
theorem B1998475 : Blo 1997435 1998475 := bstep (se 1 (by rfl) ⟨1498856, by rfl⟩ : syracuseStep 1998475 = 2997713) B2997713
theorem B6744869 : Blo 1997435 6744869 := bbase (se 4 (by rfl) ⟨632331, by rfl⟩ : syracuseStep 6744869 = 1264663) (by norm_num)
theorem B4496579 : Blo 1997435 4496579 := bstep (se 1 (by rfl) ⟨3372434, by rfl⟩ : syracuseStep 4496579 = 6744869) B6744869
theorem B2997719 : Blo 1997435 2997719 := bstep (se 1 (by rfl) ⟨2248289, by rfl⟩ : syracuseStep 2997719 = 4496579) B4496579
theorem B1998479 : Blo 1997435 1998479 := bstep (se 1 (by rfl) ⟨1498859, by rfl⟩ : syracuseStep 1998479 = 2997719) B2997719
theorem B2997725 : Blo 1997435 2997725 := bbase (se 3 (by rfl) ⟨562073, by rfl⟩ : syracuseStep 2997725 = 1124147) (by norm_num)
theorem B1998483 : Blo 1997435 1998483 := bstep (se 1 (by rfl) ⟨1498862, by rfl⟩ : syracuseStep 1998483 = 2997725) B2997725
theorem B4496597 : Blo 1997435 4496597 := bbase (se 7 (by rfl) ⟨52694, by rfl⟩ : syracuseStep 4496597 = 105389) (by norm_num)
theorem B2997731 : Blo 1997435 2997731 := bstep (se 1 (by rfl) ⟨2248298, by rfl⟩ : syracuseStep 2997731 = 4496597) B4496597
theorem B1998487 : Blo 1997435 1998487 := bstep (se 1 (by rfl) ⟨1498865, by rfl⟩ : syracuseStep 1998487 = 2997731) B2997731
theorem B3601349 : Blo 1997435 3601349 := bbase (se 4 (by rfl) ⟨337626, by rfl⟩ : syracuseStep 3601349 = 675253) (by norm_num)
theorem B2400899 : Blo 1997435 2400899 := bstep (se 1 (by rfl) ⟨1800674, by rfl⟩ : syracuseStep 2400899 = 3601349) B3601349
theorem B6402397 : Blo 1997435 6402397 := bstep (se 3 (by rfl) ⟨1200449, by rfl⟩ : syracuseStep 6402397 = 2400899) B2400899
theorem B8536529 : Blo 1997435 8536529 := bstep (se 2 (by rfl) ⟨3201198, by rfl⟩ : syracuseStep 8536529 = 6402397) B6402397
theorem B5691019 : Blo 1997435 5691019 := bstep (se 1 (by rfl) ⟨4268264, by rfl⟩ : syracuseStep 5691019 = 8536529) B8536529
theorem B7588025 : Blo 1997435 7588025 := bstep (se 2 (by rfl) ⟨2845509, by rfl⟩ : syracuseStep 7588025 = 5691019) B5691019
theorem B5058683 : Blo 1997435 5058683 := bstep (se 1 (by rfl) ⟨3794012, by rfl⟩ : syracuseStep 5058683 = 7588025) B7588025
theorem B3372455 : Blo 1997435 3372455 := bstep (se 1 (by rfl) ⟨2529341, by rfl⟩ : syracuseStep 3372455 = 5058683) B5058683
theorem B2248303 : Blo 1997435 2248303 := bstep (se 1 (by rfl) ⟨1686227, by rfl⟩ : syracuseStep 2248303 = 3372455) B3372455
theorem B2997737 : Blo 1997435 2997737 := bstep (se 2 (by rfl) ⟨1124151, by rfl⟩ : syracuseStep 2997737 = 2248303) B2248303
theorem B1998491 : Blo 1997435 1998491 := bstep (se 1 (by rfl) ⟨1498868, by rfl⟩ : syracuseStep 1998491 = 2997737) B2997737
theorem B4051525 : Blo 1997435 4051525 := bbase (se 4 (by rfl) ⟨379830, by rfl⟩ : syracuseStep 4051525 = 759661) (by norm_num)
theorem B5402033 : Blo 1997435 5402033 := bstep (se 2 (by rfl) ⟨2025762, by rfl⟩ : syracuseStep 5402033 = 4051525) B4051525
theorem B3601355 : Blo 1997435 3601355 := bstep (se 1 (by rfl) ⟨2701016, by rfl⟩ : syracuseStep 3601355 = 5402033) B5402033
theorem B9603613 : Blo 1997435 9603613 := bstep (se 3 (by rfl) ⟨1800677, by rfl⟩ : syracuseStep 9603613 = 3601355) B3601355
theorem B12804817 : Blo 1997435 12804817 := bstep (se 2 (by rfl) ⟨4801806, by rfl⟩ : syracuseStep 12804817 = 9603613) B9603613
theorem B17073089 : Blo 1997435 17073089 := bstep (se 2 (by rfl) ⟨6402408, by rfl⟩ : syracuseStep 17073089 = 12804817) B12804817
theorem B11382059 : Blo 1997435 11382059 := bstep (se 1 (by rfl) ⟨8536544, by rfl⟩ : syracuseStep 11382059 = 17073089) B17073089
theorem B7588039 : Blo 1997435 7588039 := bstep (se 1 (by rfl) ⟨5691029, by rfl⟩ : syracuseStep 7588039 = 11382059) B11382059
theorem B10117385 : Blo 1997435 10117385 := bstep (se 2 (by rfl) ⟨3794019, by rfl⟩ : syracuseStep 10117385 = 7588039) B7588039
theorem B6744923 : Blo 1997435 6744923 := bstep (se 1 (by rfl) ⟨5058692, by rfl⟩ : syracuseStep 6744923 = 10117385) B10117385
theorem B4496615 : Blo 1997435 4496615 := bstep (se 1 (by rfl) ⟨3372461, by rfl⟩ : syracuseStep 4496615 = 6744923) B6744923
theorem B2997743 : Blo 1997435 2997743 := bstep (se 1 (by rfl) ⟨2248307, by rfl⟩ : syracuseStep 2997743 = 4496615) B4496615
theorem B1998495 : Blo 1997435 1998495 := bstep (se 1 (by rfl) ⟨1498871, by rfl⟩ : syracuseStep 1998495 = 2997743) B2997743
theorem B2997749 : Blo 1997435 2997749 := bbase (se 5 (by rfl) ⟨140519, by rfl⟩ : syracuseStep 2997749 = 281039) (by norm_num)
theorem B1998499 : Blo 1997435 1998499 := bstep (se 1 (by rfl) ⟨1498874, by rfl⟩ : syracuseStep 1998499 = 2997749) B2997749
theorem B2134145 : Blo 1997435 2134145 := bbase (se 2 (by rfl) ⟨800304, by rfl⟩ : syracuseStep 2134145 = 1600609) (by norm_num)
theorem B5691053 : Blo 1997435 5691053 := bstep (se 3 (by rfl) ⟨1067072, by rfl⟩ : syracuseStep 5691053 = 2134145) B2134145
theorem B3794035 : Blo 1997435 3794035 := bstep (se 1 (by rfl) ⟨2845526, by rfl⟩ : syracuseStep 3794035 = 5691053) B5691053
theorem B5058713 : Blo 1997435 5058713 := bstep (se 2 (by rfl) ⟨1897017, by rfl⟩ : syracuseStep 5058713 = 3794035) B3794035
theorem B3372475 : Blo 1997435 3372475 := bstep (se 1 (by rfl) ⟨2529356, by rfl⟩ : syracuseStep 3372475 = 5058713) B5058713
theorem B4496633 : Blo 1997435 4496633 := bstep (se 2 (by rfl) ⟨1686237, by rfl⟩ : syracuseStep 4496633 = 3372475) B3372475
theorem B2997755 : Blo 1997435 2997755 := bstep (se 1 (by rfl) ⟨2248316, by rfl⟩ : syracuseStep 2997755 = 4496633) B4496633
theorem B1998503 : Blo 1997435 1998503 := bstep (se 1 (by rfl) ⟨1498877, by rfl⟩ : syracuseStep 1998503 = 2997755) B2997755
theorem B2248321 : Blo 1997435 2248321 := bbase (se 2 (by rfl) ⟨843120, by rfl⟩ : syracuseStep 2248321 = 1686241) (by norm_num)
theorem B2997761 : Blo 1997435 2997761 := bstep (se 2 (by rfl) ⟨1124160, by rfl⟩ : syracuseStep 2997761 = 2248321) B2248321
theorem B1998507 : Blo 1997435 1998507 := bstep (se 1 (by rfl) ⟨1498880, by rfl⟩ : syracuseStep 1998507 = 2997761) B2997761
theorem B5058733 : Blo 1997435 5058733 := bbase (se 3 (by rfl) ⟨948512, by rfl⟩ : syracuseStep 5058733 = 1897025) (by norm_num)
theorem B6744977 : Blo 1997435 6744977 := bstep (se 2 (by rfl) ⟨2529366, by rfl⟩ : syracuseStep 6744977 = 5058733) B5058733
theorem B4496651 : Blo 1997435 4496651 := bstep (se 1 (by rfl) ⟨3372488, by rfl⟩ : syracuseStep 4496651 = 6744977) B6744977
theorem B2997767 : Blo 1997435 2997767 := bstep (se 1 (by rfl) ⟨2248325, by rfl⟩ : syracuseStep 2997767 = 4496651) B4496651
theorem B1998511 : Blo 1997435 1998511 := bstep (se 1 (by rfl) ⟨1498883, by rfl⟩ : syracuseStep 1998511 = 2997767) B2997767
theorem B2997773 : Blo 1997435 2997773 := bbase (se 3 (by rfl) ⟨562082, by rfl⟩ : syracuseStep 2997773 = 1124165) (by norm_num)
theorem B1998515 : Blo 1997435 1998515 := bstep (se 1 (by rfl) ⟨1498886, by rfl⟩ : syracuseStep 1998515 = 2997773) B2997773
theorem B4496669 : Blo 1997435 4496669 := bbase (se 3 (by rfl) ⟨843125, by rfl⟩ : syracuseStep 4496669 = 1686251) (by norm_num)
theorem B2997779 : Blo 1997435 2997779 := bstep (se 1 (by rfl) ⟨2248334, by rfl⟩ : syracuseStep 2997779 = 4496669) B4496669
theorem B1998519 : Blo 1997435 1998519 := bstep (se 1 (by rfl) ⟨1498889, by rfl⟩ : syracuseStep 1998519 = 2997779) B2997779
theorem B3372509 : Blo 1997435 3372509 := bbase (se 3 (by rfl) ⟨632345, by rfl⟩ : syracuseStep 3372509 = 1264691) (by norm_num)
theorem B2248339 : Blo 1997435 2248339 := bstep (se 1 (by rfl) ⟨1686254, by rfl⟩ : syracuseStep 2248339 = 3372509) B3372509
theorem B2997785 : Blo 1997435 2997785 := bstep (se 2 (by rfl) ⟨1124169, by rfl⟩ : syracuseStep 2997785 = 2248339) B2248339
theorem B1998523 : Blo 1997435 1998523 := bstep (se 1 (by rfl) ⟨1498892, by rfl⟩ : syracuseStep 1998523 = 2997785) B2997785
theorem B2563897 : Blo 1997435 2563897 := bbase (se 2 (by rfl) ⟨961461, by rfl⟩ : syracuseStep 2563897 = 1922923) (by norm_num)
theorem B3418529 : Blo 1997435 3418529 := bstep (se 2 (by rfl) ⟨1281948, by rfl⟩ : syracuseStep 3418529 = 2563897) B2563897
theorem B9116077 : Blo 1997435 9116077 := bstep (se 3 (by rfl) ⟨1709264, by rfl⟩ : syracuseStep 9116077 = 3418529) B3418529
theorem B12154769 : Blo 1997435 12154769 := bstep (se 2 (by rfl) ⟨4558038, by rfl⟩ : syracuseStep 12154769 = 9116077) B9116077
theorem B8103179 : Blo 1997435 8103179 := bstep (se 1 (by rfl) ⟨6077384, by rfl⟩ : syracuseStep 8103179 = 12154769) B12154769
theorem B21608477 : Blo 1997435 21608477 := bstep (se 3 (by rfl) ⟨4051589, by rfl⟩ : syracuseStep 21608477 = 8103179) B8103179
theorem B14405651 : Blo 1997435 14405651 := bstep (se 1 (by rfl) ⟨10804238, by rfl⟩ : syracuseStep 14405651 = 21608477) B21608477
theorem B9603767 : Blo 1997435 9603767 := bstep (se 1 (by rfl) ⟨7202825, by rfl⟩ : syracuseStep 9603767 = 14405651) B14405651
theorem B6402511 : Blo 1997435 6402511 := bstep (se 1 (by rfl) ⟨4801883, by rfl⟩ : syracuseStep 6402511 = 9603767) B9603767
theorem B8536681 : Blo 1997435 8536681 := bstep (se 2 (by rfl) ⟨3201255, by rfl⟩ : syracuseStep 8536681 = 6402511) B6402511
theorem B11382241 : Blo 1997435 11382241 := bstep (se 2 (by rfl) ⟨4268340, by rfl⟩ : syracuseStep 11382241 = 8536681) B8536681
theorem B15176321 : Blo 1997435 15176321 := bstep (se 2 (by rfl) ⟨5691120, by rfl⟩ : syracuseStep 15176321 = 11382241) B11382241
theorem B10117547 : Blo 1997435 10117547 := bstep (se 1 (by rfl) ⟨7588160, by rfl⟩ : syracuseStep 10117547 = 15176321) B15176321
theorem B6745031 : Blo 1997435 6745031 := bstep (se 1 (by rfl) ⟨5058773, by rfl⟩ : syracuseStep 6745031 = 10117547) B10117547
theorem B4496687 : Blo 1997435 4496687 := bstep (se 1 (by rfl) ⟨3372515, by rfl⟩ : syracuseStep 4496687 = 6745031) B6745031
theorem B2997791 : Blo 1997435 2997791 := bstep (se 1 (by rfl) ⟨2248343, by rfl⟩ : syracuseStep 2997791 = 4496687) B4496687
theorem B1998527 : Blo 1997435 1998527 := bstep (se 1 (by rfl) ⟨1498895, by rfl⟩ : syracuseStep 1998527 = 2997791) B2997791
theorem B2997797 : Blo 1997435 2997797 := bbase (se 4 (by rfl) ⟨281043, by rfl⟩ : syracuseStep 2997797 = 562087) (by norm_num)
theorem B1998531 : Blo 1997435 1998531 := bstep (se 1 (by rfl) ⟨1498898, by rfl⟩ : syracuseStep 1998531 = 2997797) B2997797
theorem B2529397 : Blo 1997435 2529397 := bbase (se 5 (by rfl) ⟨118565, by rfl⟩ : syracuseStep 2529397 = 237131) (by norm_num)
theorem B3372529 : Blo 1997435 3372529 := bstep (se 2 (by rfl) ⟨1264698, by rfl⟩ : syracuseStep 3372529 = 2529397) B2529397
theorem B4496705 : Blo 1997435 4496705 := bstep (se 2 (by rfl) ⟨1686264, by rfl⟩ : syracuseStep 4496705 = 3372529) B3372529
theorem B2997803 : Blo 1997435 2997803 := bstep (se 1 (by rfl) ⟨2248352, by rfl⟩ : syracuseStep 2997803 = 4496705) B4496705
theorem B1998535 : Blo 1997435 1998535 := bstep (se 1 (by rfl) ⟨1498901, by rfl⟩ : syracuseStep 1998535 = 2997803) B2997803
theorem B2248357 : Blo 1997435 2248357 := bbase (se 4 (by rfl) ⟨210783, by rfl⟩ : syracuseStep 2248357 = 421567) (by norm_num)
theorem B2997809 : Blo 1997435 2997809 := bstep (se 2 (by rfl) ⟨1124178, by rfl⟩ : syracuseStep 2997809 = 2248357) B2248357
theorem B1998539 : Blo 1997435 1998539 := bstep (se 1 (by rfl) ⟨1498904, by rfl⟩ : syracuseStep 1998539 = 2997809) B2997809
theorem B3038717 : Blo 1997435 3038717 := bbase (se 3 (by rfl) ⟨569759, by rfl⟩ : syracuseStep 3038717 = 1139519) (by norm_num)
theorem B8103245 : Blo 1997435 8103245 := bstep (se 3 (by rfl) ⟨1519358, by rfl⟩ : syracuseStep 8103245 = 3038717) B3038717
theorem B21608653 : Blo 1997435 21608653 := bstep (se 3 (by rfl) ⟨4051622, by rfl⟩ : syracuseStep 21608653 = 8103245) B8103245
theorem B28811537 : Blo 1997435 28811537 := bstep (se 2 (by rfl) ⟨10804326, by rfl⟩ : syracuseStep 28811537 = 21608653) B21608653
theorem B19207691 : Blo 1997435 19207691 := bstep (se 1 (by rfl) ⟨14405768, by rfl⟩ : syracuseStep 19207691 = 28811537) B28811537
theorem B12805127 : Blo 1997435 12805127 := bstep (se 1 (by rfl) ⟨9603845, by rfl⟩ : syracuseStep 12805127 = 19207691) B19207691
theorem B8536751 : Blo 1997435 8536751 := bstep (se 1 (by rfl) ⟨6402563, by rfl⟩ : syracuseStep 8536751 = 12805127) B12805127
theorem B5691167 : Blo 1997435 5691167 := bstep (se 1 (by rfl) ⟨4268375, by rfl⟩ : syracuseStep 5691167 = 8536751) B8536751
theorem B3794111 : Blo 1997435 3794111 := bstep (se 1 (by rfl) ⟨2845583, by rfl⟩ : syracuseStep 3794111 = 5691167) B5691167
theorem B2529407 : Blo 1997435 2529407 := bstep (se 1 (by rfl) ⟨1897055, by rfl⟩ : syracuseStep 2529407 = 3794111) B3794111
theorem B6745085 : Blo 1997435 6745085 := bstep (se 3 (by rfl) ⟨1264703, by rfl⟩ : syracuseStep 6745085 = 2529407) B2529407
theorem B4496723 : Blo 1997435 4496723 := bstep (se 1 (by rfl) ⟨3372542, by rfl⟩ : syracuseStep 4496723 = 6745085) B6745085
theorem B2997815 : Blo 1997435 2997815 := bstep (se 1 (by rfl) ⟨2248361, by rfl⟩ : syracuseStep 2997815 = 4496723) B4496723
theorem B1998543 : Blo 1997435 1998543 := bstep (se 1 (by rfl) ⟨1498907, by rfl⟩ : syracuseStep 1998543 = 2997815) B2997815
theorem B2997821 : Blo 1997435 2997821 := bbase (se 3 (by rfl) ⟨562091, by rfl⟩ : syracuseStep 2997821 = 1124183) (by norm_num)
theorem B1998547 : Blo 1997435 1998547 := bstep (se 1 (by rfl) ⟨1498910, by rfl⟩ : syracuseStep 1998547 = 2997821) B2997821
theorem B4496741 : Blo 1997435 4496741 := bbase (se 4 (by rfl) ⟨421569, by rfl⟩ : syracuseStep 4496741 = 843139) (by norm_num)
theorem B2997827 : Blo 1997435 2997827 := bstep (se 1 (by rfl) ⟨2248370, by rfl⟩ : syracuseStep 2997827 = 4496741) B4496741
theorem B1998551 : Blo 1997435 1998551 := bstep (se 1 (by rfl) ⟨1498913, by rfl⟩ : syracuseStep 1998551 = 2997827) B2997827
theorem B5058845 : Blo 1997435 5058845 := bbase (se 3 (by rfl) ⟨948533, by rfl⟩ : syracuseStep 5058845 = 1897067) (by norm_num)
theorem B3372563 : Blo 1997435 3372563 := bstep (se 1 (by rfl) ⟨2529422, by rfl⟩ : syracuseStep 3372563 = 5058845) B5058845
theorem B2248375 : Blo 1997435 2248375 := bstep (se 1 (by rfl) ⟨1686281, by rfl⟩ : syracuseStep 2248375 = 3372563) B3372563
theorem B2997833 : Blo 1997435 2997833 := bstep (se 2 (by rfl) ⟨1124187, by rfl⟩ : syracuseStep 2997833 = 2248375) B2248375
theorem B1998555 : Blo 1997435 1998555 := bstep (se 1 (by rfl) ⟨1498916, by rfl⟩ : syracuseStep 1998555 = 2997833) B2997833
theorem B3794141 : Blo 1997435 3794141 := bbase (se 3 (by rfl) ⟨711401, by rfl⟩ : syracuseStep 3794141 = 1422803) (by norm_num)
theorem B10117709 : Blo 1997435 10117709 := bstep (se 3 (by rfl) ⟨1897070, by rfl⟩ : syracuseStep 10117709 = 3794141) B3794141
theorem B6745139 : Blo 1997435 6745139 := bstep (se 1 (by rfl) ⟨5058854, by rfl⟩ : syracuseStep 6745139 = 10117709) B10117709
theorem B4496759 : Blo 1997435 4496759 := bstep (se 1 (by rfl) ⟨3372569, by rfl⟩ : syracuseStep 4496759 = 6745139) B6745139
theorem B2997839 : Blo 1997435 2997839 := bstep (se 1 (by rfl) ⟨2248379, by rfl⟩ : syracuseStep 2997839 = 4496759) B4496759
theorem B1998559 : Blo 1997435 1998559 := bstep (se 1 (by rfl) ⟨1498919, by rfl⟩ : syracuseStep 1998559 = 2997839) B2997839
theorem B2997845 : Blo 1997435 2997845 := bbase (se 8 (by rfl) ⟨17565, by rfl⟩ : syracuseStep 2997845 = 35131) (by norm_num)
theorem B1998563 : Blo 1997435 1998563 := bstep (se 1 (by rfl) ⟨1498922, by rfl⟩ : syracuseStep 1998563 = 2997845) B2997845
theorem B8536853 : Blo 1997435 8536853 := bbase (se 6 (by rfl) ⟨200082, by rfl⟩ : syracuseStep 8536853 = 400165) (by norm_num)
theorem B5691235 : Blo 1997435 5691235 := bstep (se 1 (by rfl) ⟨4268426, by rfl⟩ : syracuseStep 5691235 = 8536853) B8536853
theorem B7588313 : Blo 1997435 7588313 := bstep (se 2 (by rfl) ⟨2845617, by rfl⟩ : syracuseStep 7588313 = 5691235) B5691235
theorem B5058875 : Blo 1997435 5058875 := bstep (se 1 (by rfl) ⟨3794156, by rfl⟩ : syracuseStep 5058875 = 7588313) B7588313
theorem B3372583 : Blo 1997435 3372583 := bstep (se 1 (by rfl) ⟨2529437, by rfl⟩ : syracuseStep 3372583 = 5058875) B5058875
theorem B4496777 : Blo 1997435 4496777 := bstep (se 2 (by rfl) ⟨1686291, by rfl⟩ : syracuseStep 4496777 = 3372583) B3372583
theorem B2997851 : Blo 1997435 2997851 := bstep (se 1 (by rfl) ⟨2248388, by rfl⟩ : syracuseStep 2997851 = 4496777) B4496777
theorem B1998567 : Blo 1997435 1998567 := bstep (se 1 (by rfl) ⟨1498925, by rfl⟩ : syracuseStep 1998567 = 2997851) B2997851
theorem B2248393 : Blo 1997435 2248393 := bbase (se 2 (by rfl) ⟨843147, by rfl⟩ : syracuseStep 2248393 = 1686295) (by norm_num)
theorem B2997857 : Blo 1997435 2997857 := bstep (se 2 (by rfl) ⟨1124196, by rfl⟩ : syracuseStep 2997857 = 2248393) B2248393
theorem B1998571 : Blo 1997435 1998571 := bstep (se 1 (by rfl) ⟨1498928, by rfl⟩ : syracuseStep 1998571 = 2997857) B2997857
theorem B25960085 : Blo 1997435 25960085 := bbase (se 6 (by rfl) ⟨608439, by rfl⟩ : syracuseStep 25960085 = 1216879) (by norm_num)
theorem B17306723 : Blo 1997435 17306723 := bstep (se 1 (by rfl) ⟨12980042, by rfl⟩ : syracuseStep 17306723 = 25960085) B25960085
theorem B11537815 : Blo 1997435 11537815 := bstep (se 1 (by rfl) ⟨8653361, by rfl⟩ : syracuseStep 11537815 = 17306723) B17306723
theorem B15383753 : Blo 1997435 15383753 := bstep (se 2 (by rfl) ⟨5768907, by rfl⟩ : syracuseStep 15383753 = 11537815) B11537815
theorem B10255835 : Blo 1997435 10255835 := bstep (se 1 (by rfl) ⟨7691876, by rfl⟩ : syracuseStep 10255835 = 15383753) B15383753
theorem B6837223 : Blo 1997435 6837223 := bstep (se 1 (by rfl) ⟨5127917, by rfl⟩ : syracuseStep 6837223 = 10255835) B10255835
theorem B9116297 : Blo 1997435 9116297 := bstep (se 2 (by rfl) ⟨3418611, by rfl⟩ : syracuseStep 9116297 = 6837223) B6837223
theorem B6077531 : Blo 1997435 6077531 := bstep (se 1 (by rfl) ⟨4558148, by rfl⟩ : syracuseStep 6077531 = 9116297) B9116297
theorem B16206749 : Blo 1997435 16206749 := bstep (se 3 (by rfl) ⟨3038765, by rfl⟩ : syracuseStep 16206749 = 6077531) B6077531
theorem B10804499 : Blo 1997435 10804499 := bstep (se 1 (by rfl) ⟨8103374, by rfl⟩ : syracuseStep 10804499 = 16206749) B16206749
theorem B7202999 : Blo 1997435 7202999 := bstep (se 1 (by rfl) ⟨5402249, by rfl⟩ : syracuseStep 7202999 = 10804499) B10804499
theorem B4801999 : Blo 1997435 4801999 := bstep (se 1 (by rfl) ⟨3601499, by rfl⟩ : syracuseStep 4801999 = 7202999) B7202999
theorem B6402665 : Blo 1997435 6402665 := bstep (se 2 (by rfl) ⟨2400999, by rfl⟩ : syracuseStep 6402665 = 4801999) B4801999
theorem B17073773 : Blo 1997435 17073773 := bstep (se 3 (by rfl) ⟨3201332, by rfl⟩ : syracuseStep 17073773 = 6402665) B6402665
theorem B11382515 : Blo 1997435 11382515 := bstep (se 1 (by rfl) ⟨8536886, by rfl⟩ : syracuseStep 11382515 = 17073773) B17073773
theorem B7588343 : Blo 1997435 7588343 := bstep (se 1 (by rfl) ⟨5691257, by rfl⟩ : syracuseStep 7588343 = 11382515) B11382515
theorem B5058895 : Blo 1997435 5058895 := bstep (se 1 (by rfl) ⟨3794171, by rfl⟩ : syracuseStep 5058895 = 7588343) B7588343
theorem B6745193 : Blo 1997435 6745193 := bstep (se 2 (by rfl) ⟨2529447, by rfl⟩ : syracuseStep 6745193 = 5058895) B5058895
theorem B4496795 : Blo 1997435 4496795 := bstep (se 1 (by rfl) ⟨3372596, by rfl⟩ : syracuseStep 4496795 = 6745193) B6745193
theorem B2997863 : Blo 1997435 2997863 := bstep (se 1 (by rfl) ⟨2248397, by rfl⟩ : syracuseStep 2997863 = 4496795) B4496795
theorem B1998575 : Blo 1997435 1998575 := bstep (se 1 (by rfl) ⟨1498931, by rfl⟩ : syracuseStep 1998575 = 2997863) B2997863
theorem B2997869 : Blo 1997435 2997869 := bbase (se 3 (by rfl) ⟨562100, by rfl⟩ : syracuseStep 2997869 = 1124201) (by norm_num)
theorem B1998579 : Blo 1997435 1998579 := bstep (se 1 (by rfl) ⟨1498934, by rfl⟩ : syracuseStep 1998579 = 2997869) B2997869
theorem B4496813 : Blo 1997435 4496813 := bbase (se 3 (by rfl) ⟨843152, by rfl⟩ : syracuseStep 4496813 = 1686305) (by norm_num)
theorem B2997875 : Blo 1997435 2997875 := bstep (se 1 (by rfl) ⟨2248406, by rfl⟩ : syracuseStep 2997875 = 4496813) B4496813
theorem B1998583 : Blo 1997435 1998583 := bstep (se 1 (by rfl) ⟨1498937, by rfl⟩ : syracuseStep 1998583 = 2997875) B2997875
theorem B2025857 : Blo 1997435 2025857 := bbase (se 2 (by rfl) ⟨759696, by rfl⟩ : syracuseStep 2025857 = 1519393) (by norm_num)
theorem B5402285 : Blo 1997435 5402285 := bstep (se 3 (by rfl) ⟨1012928, by rfl⟩ : syracuseStep 5402285 = 2025857) B2025857
theorem B3601523 : Blo 1997435 3601523 := bstep (se 1 (by rfl) ⟨2701142, by rfl⟩ : syracuseStep 3601523 = 5402285) B5402285
theorem B2401015 : Blo 1997435 2401015 := bstep (se 1 (by rfl) ⟨1800761, by rfl⟩ : syracuseStep 2401015 = 3601523) B3601523
theorem B3201353 : Blo 1997435 3201353 := bstep (se 2 (by rfl) ⟨1200507, by rfl⟩ : syracuseStep 3201353 = 2401015) B2401015
theorem B2134235 : Blo 1997435 2134235 := bstep (se 1 (by rfl) ⟨1600676, by rfl⟩ : syracuseStep 2134235 = 3201353) B3201353
theorem B5691293 : Blo 1997435 5691293 := bstep (se 3 (by rfl) ⟨1067117, by rfl⟩ : syracuseStep 5691293 = 2134235) B2134235
theorem B3794195 : Blo 1997435 3794195 := bstep (se 1 (by rfl) ⟨2845646, by rfl⟩ : syracuseStep 3794195 = 5691293) B5691293
theorem B2529463 : Blo 1997435 2529463 := bstep (se 1 (by rfl) ⟨1897097, by rfl⟩ : syracuseStep 2529463 = 3794195) B3794195
theorem B3372617 : Blo 1997435 3372617 := bstep (se 2 (by rfl) ⟨1264731, by rfl⟩ : syracuseStep 3372617 = 2529463) B2529463
theorem B2248411 : Blo 1997435 2248411 := bstep (se 1 (by rfl) ⟨1686308, by rfl⟩ : syracuseStep 2248411 = 3372617) B3372617
theorem B2997881 : Blo 1997435 2997881 := bstep (se 2 (by rfl) ⟨1124205, by rfl⟩ : syracuseStep 2997881 = 2248411) B2248411
theorem B1998587 : Blo 1997435 1998587 := bstep (se 1 (by rfl) ⟨1498940, by rfl⟩ : syracuseStep 1998587 = 2997881) B2997881
theorem B2598961 : Blo 1997435 2598961 := bbase (se 2 (by rfl) ⟨974610, by rfl⟩ : syracuseStep 2598961 = 1949221) (by norm_num)
theorem B3465281 : Blo 1997435 3465281 := bstep (se 2 (by rfl) ⟨1299480, by rfl⟩ : syracuseStep 3465281 = 2598961) B2598961
theorem B2310187 : Blo 1997435 2310187 := bstep (se 1 (by rfl) ⟨1732640, by rfl⟩ : syracuseStep 2310187 = 3465281) B3465281
theorem B3080249 : Blo 1997435 3080249 := bstep (se 2 (by rfl) ⟨1155093, by rfl⟩ : syracuseStep 3080249 = 2310187) B2310187
theorem B2053499 : Blo 1997435 2053499 := bstep (se 1 (by rfl) ⟨1540124, by rfl⟩ : syracuseStep 2053499 = 3080249) B3080249
theorem B5475997 : Blo 1997435 5475997 := bstep (se 3 (by rfl) ⟨1026749, by rfl⟩ : syracuseStep 5475997 = 2053499) B2053499
theorem B7301329 : Blo 1997435 7301329 := bstep (se 2 (by rfl) ⟨2737998, by rfl⟩ : syracuseStep 7301329 = 5475997) B5475997
theorem B38940421 : Blo 1997435 38940421 := bstep (se 4 (by rfl) ⟨3650664, by rfl⟩ : syracuseStep 38940421 = 7301329) B7301329
theorem B51920561 : Blo 1997435 51920561 := bstep (se 2 (by rfl) ⟨19470210, by rfl⟩ : syracuseStep 51920561 = 38940421) B38940421
theorem B138454829 : Blo 1997435 138454829 := bstep (se 3 (by rfl) ⟨25960280, by rfl⟩ : syracuseStep 138454829 = 51920561) B51920561
theorem B92303219 : Blo 1997435 92303219 := bstep (se 1 (by rfl) ⟨69227414, by rfl⟩ : syracuseStep 92303219 = 138454829) B138454829
theorem B61535479 : Blo 1997435 61535479 := bstep (se 1 (by rfl) ⟨46151609, by rfl⟩ : syracuseStep 61535479 = 92303219) B92303219
theorem B82047305 : Blo 1997435 82047305 := bstep (se 2 (by rfl) ⟨30767739, by rfl⟩ : syracuseStep 82047305 = 61535479) B61535479
theorem B54698203 : Blo 1997435 54698203 := bstep (se 1 (by rfl) ⟨41023652, by rfl⟩ : syracuseStep 54698203 = 82047305) B82047305
theorem B72930937 : Blo 1997435 72930937 := bstep (se 2 (by rfl) ⟨27349101, by rfl⟩ : syracuseStep 72930937 = 54698203) B54698203
theorem B97241249 : Blo 1997435 97241249 := bstep (se 2 (by rfl) ⟨36465468, by rfl⟩ : syracuseStep 97241249 = 72930937) B72930937
theorem B64827499 : Blo 1997435 64827499 := bstep (se 1 (by rfl) ⟨48620624, by rfl⟩ : syracuseStep 64827499 = 97241249) B97241249
theorem B86436665 : Blo 1997435 86436665 := bstep (se 2 (by rfl) ⟨32413749, by rfl⟩ : syracuseStep 86436665 = 64827499) B64827499
theorem B57624443 : Blo 1997435 57624443 := bstep (se 1 (by rfl) ⟨43218332, by rfl⟩ : syracuseStep 57624443 = 86436665) B86436665
theorem B38416295 : Blo 1997435 38416295 := bstep (se 1 (by rfl) ⟨28812221, by rfl⟩ : syracuseStep 38416295 = 57624443) B57624443
theorem B25610863 : Blo 1997435 25610863 := bstep (se 1 (by rfl) ⟨19208147, by rfl⟩ : syracuseStep 25610863 = 38416295) B38416295
theorem B34147817 : Blo 1997435 34147817 := bstep (se 2 (by rfl) ⟨12805431, by rfl⟩ : syracuseStep 34147817 = 25610863) B25610863
theorem B22765211 : Blo 1997435 22765211 := bstep (se 1 (by rfl) ⟨17073908, by rfl⟩ : syracuseStep 22765211 = 34147817) B34147817
theorem B15176807 : Blo 1997435 15176807 := bstep (se 1 (by rfl) ⟨11382605, by rfl⟩ : syracuseStep 15176807 = 22765211) B22765211
theorem B10117871 : Blo 1997435 10117871 := bstep (se 1 (by rfl) ⟨7588403, by rfl⟩ : syracuseStep 10117871 = 15176807) B15176807
theorem B6745247 : Blo 1997435 6745247 := bstep (se 1 (by rfl) ⟨5058935, by rfl⟩ : syracuseStep 6745247 = 10117871) B10117871
theorem B4496831 : Blo 1997435 4496831 := bstep (se 1 (by rfl) ⟨3372623, by rfl⟩ : syracuseStep 4496831 = 6745247) B6745247
theorem B2997887 : Blo 1997435 2997887 := bstep (se 1 (by rfl) ⟨2248415, by rfl⟩ : syracuseStep 2997887 = 4496831) B4496831
theorem B1998591 : Blo 1997435 1998591 := bstep (se 1 (by rfl) ⟨1498943, by rfl⟩ : syracuseStep 1998591 = 2997887) B2997887
theorem B2997893 : Blo 1997435 2997893 := bbase (se 4 (by rfl) ⟨281052, by rfl⟩ : syracuseStep 2997893 = 562105) (by norm_num)
theorem B1998595 : Blo 1997435 1998595 := bstep (se 1 (by rfl) ⟨1498946, by rfl⟩ : syracuseStep 1998595 = 2997893) B2997893
theorem B3372637 : Blo 1997435 3372637 := bbase (se 3 (by rfl) ⟨632369, by rfl⟩ : syracuseStep 3372637 = 1264739) (by norm_num)
theorem B4496849 : Blo 1997435 4496849 := bstep (se 2 (by rfl) ⟨1686318, by rfl⟩ : syracuseStep 4496849 = 3372637) B3372637
theorem B2997899 : Blo 1997435 2997899 := bstep (se 1 (by rfl) ⟨2248424, by rfl⟩ : syracuseStep 2997899 = 4496849) B4496849
theorem B1998599 : Blo 1997435 1998599 := bstep (se 1 (by rfl) ⟨1498949, by rfl⟩ : syracuseStep 1998599 = 2997899) B2997899
theorem B2248429 : Blo 1997435 2248429 := bbase (se 3 (by rfl) ⟨421580, by rfl⟩ : syracuseStep 2248429 = 843161) (by norm_num)
theorem B2997905 : Blo 1997435 2997905 := bstep (se 2 (by rfl) ⟨1124214, by rfl⟩ : syracuseStep 2997905 = 2248429) B2248429
theorem B1998603 : Blo 1997435 1998603 := bstep (se 1 (by rfl) ⟨1498952, by rfl⟩ : syracuseStep 1998603 = 2997905) B2997905
theorem B6745301 : Blo 1997435 6745301 := bbase (se 7 (by rfl) ⟨79046, by rfl⟩ : syracuseStep 6745301 = 158093) (by norm_num)
theorem B4496867 : Blo 1997435 4496867 := bstep (se 1 (by rfl) ⟨3372650, by rfl⟩ : syracuseStep 4496867 = 6745301) B6745301
theorem B2997911 : Blo 1997435 2997911 := bstep (se 1 (by rfl) ⟨2248433, by rfl⟩ : syracuseStep 2997911 = 4496867) B4496867
theorem B1998607 : Blo 1997435 1998607 := bstep (se 1 (by rfl) ⟨1498955, by rfl⟩ : syracuseStep 1998607 = 2997911) B2997911
theorem B2997917 : Blo 1997435 2997917 := bbase (se 3 (by rfl) ⟨562109, by rfl⟩ : syracuseStep 2997917 = 1124219) (by norm_num)
theorem B1998611 : Blo 1997435 1998611 := bstep (se 1 (by rfl) ⟨1498958, by rfl⟩ : syracuseStep 1998611 = 2997917) B2997917
theorem B4496885 : Blo 1997435 4496885 := bbase (se 5 (by rfl) ⟨210791, by rfl⟩ : syracuseStep 4496885 = 421583) (by norm_num)
theorem B2997923 : Blo 1997435 2997923 := bstep (se 1 (by rfl) ⟨2248442, by rfl⟩ : syracuseStep 2997923 = 4496885) B4496885
theorem B1998615 : Blo 1997435 1998615 := bstep (se 1 (by rfl) ⟨1498961, by rfl⟩ : syracuseStep 1998615 = 2997923) B2997923
theorem B6490165 : Blo 1997435 6490165 := bbase (se 5 (by rfl) ⟨304226, by rfl⟩ : syracuseStep 6490165 = 608453) (by norm_num)
theorem B8653553 : Blo 1997435 8653553 := bstep (se 2 (by rfl) ⟨3245082, by rfl⟩ : syracuseStep 8653553 = 6490165) B6490165
theorem B5769035 : Blo 1997435 5769035 := bstep (se 1 (by rfl) ⟨4326776, by rfl⟩ : syracuseStep 5769035 = 8653553) B8653553
theorem B3846023 : Blo 1997435 3846023 := bstep (se 1 (by rfl) ⟨2884517, by rfl⟩ : syracuseStep 3846023 = 5769035) B5769035
theorem B2564015 : Blo 1997435 2564015 := bstep (se 1 (by rfl) ⟨1923011, by rfl⟩ : syracuseStep 2564015 = 3846023) B3846023
theorem B6837373 : Blo 1997435 6837373 := bstep (se 3 (by rfl) ⟨1282007, by rfl⟩ : syracuseStep 6837373 = 2564015) B2564015
theorem B9116497 : Blo 1997435 9116497 := bstep (se 2 (by rfl) ⟨3418686, by rfl⟩ : syracuseStep 9116497 = 6837373) B6837373
theorem B12155329 : Blo 1997435 12155329 := bstep (se 2 (by rfl) ⟨4558248, by rfl⟩ : syracuseStep 12155329 = 9116497) B9116497
theorem B64828421 : Blo 1997435 64828421 := bstep (se 4 (by rfl) ⟨6077664, by rfl⟩ : syracuseStep 64828421 = 12155329) B12155329
theorem B43218947 : Blo 1997435 43218947 := bstep (se 1 (by rfl) ⟨32414210, by rfl⟩ : syracuseStep 43218947 = 64828421) B64828421
theorem B28812631 : Blo 1997435 28812631 := bstep (se 1 (by rfl) ⟨21609473, by rfl⟩ : syracuseStep 28812631 = 43218947) B43218947
theorem B38416841 : Blo 1997435 38416841 := bstep (se 2 (by rfl) ⟨14406315, by rfl⟩ : syracuseStep 38416841 = 28812631) B28812631
theorem B25611227 : Blo 1997435 25611227 := bstep (se 1 (by rfl) ⟨19208420, by rfl⟩ : syracuseStep 25611227 = 38416841) B38416841
theorem B17074151 : Blo 1997435 17074151 := bstep (se 1 (by rfl) ⟨12805613, by rfl⟩ : syracuseStep 17074151 = 25611227) B25611227
theorem B11382767 : Blo 1997435 11382767 := bstep (se 1 (by rfl) ⟨8537075, by rfl⟩ : syracuseStep 11382767 = 17074151) B17074151
theorem B7588511 : Blo 1997435 7588511 := bstep (se 1 (by rfl) ⟨5691383, by rfl⟩ : syracuseStep 7588511 = 11382767) B11382767
theorem B5059007 : Blo 1997435 5059007 := bstep (se 1 (by rfl) ⟨3794255, by rfl⟩ : syracuseStep 5059007 = 7588511) B7588511
theorem B3372671 : Blo 1997435 3372671 := bstep (se 1 (by rfl) ⟨2529503, by rfl⟩ : syracuseStep 3372671 = 5059007) B5059007
theorem B2248447 : Blo 1997435 2248447 := bstep (se 1 (by rfl) ⟨1686335, by rfl⟩ : syracuseStep 2248447 = 3372671) B3372671
theorem B2997929 : Blo 1997435 2997929 := bstep (se 2 (by rfl) ⟨1124223, by rfl⟩ : syracuseStep 2997929 = 2248447) B2248447
theorem B1998619 : Blo 1997435 1998619 := bstep (se 1 (by rfl) ⟨1498964, by rfl⟩ : syracuseStep 1998619 = 2997929) B2997929
theorem B2134273 : Blo 1997435 2134273 := bbase (se 2 (by rfl) ⟨800352, by rfl⟩ : syracuseStep 2134273 = 1600705) (by norm_num)
theorem B2845697 : Blo 1997435 2845697 := bstep (se 2 (by rfl) ⟨1067136, by rfl⟩ : syracuseStep 2845697 = 2134273) B2134273
theorem B7588525 : Blo 1997435 7588525 := bstep (se 3 (by rfl) ⟨1422848, by rfl⟩ : syracuseStep 7588525 = 2845697) B2845697
theorem B10118033 : Blo 1997435 10118033 := bstep (se 2 (by rfl) ⟨3794262, by rfl⟩ : syracuseStep 10118033 = 7588525) B7588525
theorem B6745355 : Blo 1997435 6745355 := bstep (se 1 (by rfl) ⟨5059016, by rfl⟩ : syracuseStep 6745355 = 10118033) B10118033
theorem B4496903 : Blo 1997435 4496903 := bstep (se 1 (by rfl) ⟨3372677, by rfl⟩ : syracuseStep 4496903 = 6745355) B6745355
theorem B2997935 : Blo 1997435 2997935 := bstep (se 1 (by rfl) ⟨2248451, by rfl⟩ : syracuseStep 2997935 = 4496903) B4496903
theorem B1998623 : Blo 1997435 1998623 := bstep (se 1 (by rfl) ⟨1498967, by rfl⟩ : syracuseStep 1998623 = 2997935) B2997935
theorem B2997941 : Blo 1997435 2997941 := bbase (se 5 (by rfl) ⟨140528, by rfl⟩ : syracuseStep 2997941 = 281057) (by norm_num)
theorem B1998627 : Blo 1997435 1998627 := bstep (se 1 (by rfl) ⟨1498970, by rfl⟩ : syracuseStep 1998627 = 2997941) B2997941
theorem B5059037 : Blo 1997435 5059037 := bbase (se 3 (by rfl) ⟨948569, by rfl⟩ : syracuseStep 5059037 = 1897139) (by norm_num)
theorem B3372691 : Blo 1997435 3372691 := bstep (se 1 (by rfl) ⟨2529518, by rfl⟩ : syracuseStep 3372691 = 5059037) B5059037
theorem B4496921 : Blo 1997435 4496921 := bstep (se 2 (by rfl) ⟨1686345, by rfl⟩ : syracuseStep 4496921 = 3372691) B3372691
theorem B2997947 : Blo 1997435 2997947 := bstep (se 1 (by rfl) ⟨2248460, by rfl⟩ : syracuseStep 2997947 = 4496921) B4496921
theorem B1998631 : Blo 1997435 1998631 := bstep (se 1 (by rfl) ⟨1498973, by rfl⟩ : syracuseStep 1998631 = 2997947) B2997947
theorem B2248465 : Blo 1997435 2248465 := bbase (se 2 (by rfl) ⟨843174, by rfl⟩ : syracuseStep 2248465 = 1686349) (by norm_num)
theorem B2997953 : Blo 1997435 2997953 := bstep (se 2 (by rfl) ⟨1124232, by rfl⟩ : syracuseStep 2997953 = 2248465) B2248465
theorem B1998635 : Blo 1997435 1998635 := bstep (se 1 (by rfl) ⟨1498976, by rfl⟩ : syracuseStep 1998635 = 2997953) B2997953
theorem B3794293 : Blo 1997435 3794293 := bbase (se 5 (by rfl) ⟨177857, by rfl⟩ : syracuseStep 3794293 = 355715) (by norm_num)
theorem B5059057 : Blo 1997435 5059057 := bstep (se 2 (by rfl) ⟨1897146, by rfl⟩ : syracuseStep 5059057 = 3794293) B3794293
theorem B6745409 : Blo 1997435 6745409 := bstep (se 2 (by rfl) ⟨2529528, by rfl⟩ : syracuseStep 6745409 = 5059057) B5059057
theorem B4496939 : Blo 1997435 4496939 := bstep (se 1 (by rfl) ⟨3372704, by rfl⟩ : syracuseStep 4496939 = 6745409) B6745409
theorem B2997959 : Blo 1997435 2997959 := bstep (se 1 (by rfl) ⟨2248469, by rfl⟩ : syracuseStep 2997959 = 4496939) B4496939
theorem B1998639 : Blo 1997435 1998639 := bstep (se 1 (by rfl) ⟨1498979, by rfl⟩ : syracuseStep 1998639 = 2997959) B2997959
theorem B2997965 : Blo 1997435 2997965 := bbase (se 3 (by rfl) ⟨562118, by rfl⟩ : syracuseStep 2997965 = 1124237) (by norm_num)
theorem B1998643 : Blo 1997435 1998643 := bstep (se 1 (by rfl) ⟨1498982, by rfl⟩ : syracuseStep 1998643 = 2997965) B2997965
theorem B4496957 : Blo 1997435 4496957 := bbase (se 3 (by rfl) ⟨843179, by rfl⟩ : syracuseStep 4496957 = 1686359) (by norm_num)
theorem B2997971 : Blo 1997435 2997971 := bstep (se 1 (by rfl) ⟨2248478, by rfl⟩ : syracuseStep 2997971 = 4496957) B4496957
theorem B1998647 : Blo 1997435 1998647 := bstep (se 1 (by rfl) ⟨1498985, by rfl⟩ : syracuseStep 1998647 = 2997971) B2997971
theorem B3372725 : Blo 1997435 3372725 := bbase (se 5 (by rfl) ⟨158096, by rfl⟩ : syracuseStep 3372725 = 316193) (by norm_num)
theorem B2248483 : Blo 1997435 2248483 := bstep (se 1 (by rfl) ⟨1686362, by rfl⟩ : syracuseStep 2248483 = 3372725) B3372725
theorem B2997977 : Blo 1997435 2997977 := bstep (se 2 (by rfl) ⟨1124241, by rfl⟩ : syracuseStep 2997977 = 2248483) B2248483
theorem B1998651 : Blo 1997435 1998651 := bstep (se 1 (by rfl) ⟨1498988, by rfl⟩ : syracuseStep 1998651 = 2997977) B2997977
theorem B3201461 : Blo 1997435 3201461 := bbase (se 5 (by rfl) ⟨150068, by rfl⟩ : syracuseStep 3201461 = 300137) (by norm_num)
theorem B2134307 : Blo 1997435 2134307 := bstep (se 1 (by rfl) ⟨1600730, by rfl⟩ : syracuseStep 2134307 = 3201461) B3201461
theorem B5691485 : Blo 1997435 5691485 := bstep (se 3 (by rfl) ⟨1067153, by rfl⟩ : syracuseStep 5691485 = 2134307) B2134307
theorem B15177293 : Blo 1997435 15177293 := bstep (se 3 (by rfl) ⟨2845742, by rfl⟩ : syracuseStep 15177293 = 5691485) B5691485
theorem B10118195 : Blo 1997435 10118195 := bstep (se 1 (by rfl) ⟨7588646, by rfl⟩ : syracuseStep 10118195 = 15177293) B15177293
theorem B6745463 : Blo 1997435 6745463 := bstep (se 1 (by rfl) ⟨5059097, by rfl⟩ : syracuseStep 6745463 = 10118195) B10118195
theorem B4496975 : Blo 1997435 4496975 := bstep (se 1 (by rfl) ⟨3372731, by rfl⟩ : syracuseStep 4496975 = 6745463) B6745463
theorem B2997983 : Blo 1997435 2997983 := bstep (se 1 (by rfl) ⟨2248487, by rfl⟩ : syracuseStep 2997983 = 4496975) B4496975
theorem B1998655 : Blo 1997435 1998655 := bstep (se 1 (by rfl) ⟨1498991, by rfl⟩ : syracuseStep 1998655 = 2997983) B2997983
theorem B2997989 : Blo 1997435 2997989 := bbase (se 4 (by rfl) ⟨281061, by rfl⟩ : syracuseStep 2997989 = 562123) (by norm_num)
theorem B1998659 : Blo 1997435 1998659 := bstep (se 1 (by rfl) ⟨1498994, by rfl⟩ : syracuseStep 1998659 = 2997989) B2997989
theorem B5691509 : Blo 1997435 5691509 := bbase (se 5 (by rfl) ⟨266789, by rfl⟩ : syracuseStep 5691509 = 533579) (by norm_num)
theorem B3794339 : Blo 1997435 3794339 := bstep (se 1 (by rfl) ⟨2845754, by rfl⟩ : syracuseStep 3794339 = 5691509) B5691509
theorem B2529559 : Blo 1997435 2529559 := bstep (se 1 (by rfl) ⟨1897169, by rfl⟩ : syracuseStep 2529559 = 3794339) B3794339
theorem B3372745 : Blo 1997435 3372745 := bstep (se 2 (by rfl) ⟨1264779, by rfl⟩ : syracuseStep 3372745 = 2529559) B2529559
theorem B4496993 : Blo 1997435 4496993 := bstep (se 2 (by rfl) ⟨1686372, by rfl⟩ : syracuseStep 4496993 = 3372745) B3372745
theorem B2997995 : Blo 1997435 2997995 := bstep (se 1 (by rfl) ⟨2248496, by rfl⟩ : syracuseStep 2997995 = 4496993) B4496993
theorem B1998663 : Blo 1997435 1998663 := bstep (se 1 (by rfl) ⟨1498997, by rfl⟩ : syracuseStep 1998663 = 2997995) B2997995
theorem B2248501 : Blo 1997435 2248501 := bbase (se 5 (by rfl) ⟨105398, by rfl⟩ : syracuseStep 2248501 = 210797) (by norm_num)
theorem B2998001 : Blo 1997435 2998001 := bstep (se 2 (by rfl) ⟨1124250, by rfl⟩ : syracuseStep 2998001 = 2248501) B2248501
theorem B1998667 : Blo 1997435 1998667 := bstep (se 1 (by rfl) ⟨1499000, by rfl⟩ : syracuseStep 1998667 = 2998001) B2998001
theorem B2529569 : Blo 1997435 2529569 := bbase (se 2 (by rfl) ⟨948588, by rfl⟩ : syracuseStep 2529569 = 1897177) (by norm_num)
theorem B6745517 : Blo 1997435 6745517 := bstep (se 3 (by rfl) ⟨1264784, by rfl⟩ : syracuseStep 6745517 = 2529569) B2529569
theorem B4497011 : Blo 1997435 4497011 := bstep (se 1 (by rfl) ⟨3372758, by rfl⟩ : syracuseStep 4497011 = 6745517) B6745517
theorem B2998007 : Blo 1997435 2998007 := bstep (se 1 (by rfl) ⟨2248505, by rfl⟩ : syracuseStep 2998007 = 4497011) B4497011
theorem B1998671 : Blo 1997435 1998671 := bstep (se 1 (by rfl) ⟨1499003, by rfl⟩ : syracuseStep 1998671 = 2998007) B2998007
theorem B2998013 : Blo 1997435 2998013 := bbase (se 3 (by rfl) ⟨562127, by rfl⟩ : syracuseStep 2998013 = 1124255) (by norm_num)
theorem B1998675 : Blo 1997435 1998675 := bstep (se 1 (by rfl) ⟨1499006, by rfl⟩ : syracuseStep 1998675 = 2998013) B2998013
theorem B4497029 : Blo 1997435 4497029 := bbase (se 4 (by rfl) ⟨421596, by rfl⟩ : syracuseStep 4497029 = 843193) (by norm_num)
theorem B2998019 : Blo 1997435 2998019 := bstep (se 1 (by rfl) ⟨2248514, by rfl⟩ : syracuseStep 2998019 = 4497029) B4497029
theorem B1998679 : Blo 1997435 1998679 := bstep (se 1 (by rfl) ⟨1499009, by rfl⟩ : syracuseStep 1998679 = 2998019) B2998019
theorem B6403013 : Blo 1997435 6403013 := bbase (se 4 (by rfl) ⟨600282, by rfl⟩ : syracuseStep 6403013 = 1200565) (by norm_num)
theorem B4268675 : Blo 1997435 4268675 := bstep (se 1 (by rfl) ⟨3201506, by rfl⟩ : syracuseStep 4268675 = 6403013) B6403013
theorem B2845783 : Blo 1997435 2845783 := bstep (se 1 (by rfl) ⟨2134337, by rfl⟩ : syracuseStep 2845783 = 4268675) B4268675
theorem B3794377 : Blo 1997435 3794377 := bstep (se 2 (by rfl) ⟨1422891, by rfl⟩ : syracuseStep 3794377 = 2845783) B2845783
theorem B5059169 : Blo 1997435 5059169 := bstep (se 2 (by rfl) ⟨1897188, by rfl⟩ : syracuseStep 5059169 = 3794377) B3794377
theorem B3372779 : Blo 1997435 3372779 := bstep (se 1 (by rfl) ⟨2529584, by rfl⟩ : syracuseStep 3372779 = 5059169) B5059169
theorem B2248519 : Blo 1997435 2248519 := bstep (se 1 (by rfl) ⟨1686389, by rfl⟩ : syracuseStep 2248519 = 3372779) B3372779
theorem B2998025 : Blo 1997435 2998025 := bstep (se 2 (by rfl) ⟨1124259, by rfl⟩ : syracuseStep 2998025 = 2248519) B2248519
theorem B1998683 : Blo 1997435 1998683 := bstep (se 1 (by rfl) ⟨1499012, by rfl⟩ : syracuseStep 1998683 = 2998025) B2998025
theorem B10118357 : Blo 1997435 10118357 := bbase (se 7 (by rfl) ⟨118574, by rfl⟩ : syracuseStep 10118357 = 237149) (by norm_num)
theorem B6745571 : Blo 1997435 6745571 := bstep (se 1 (by rfl) ⟨5059178, by rfl⟩ : syracuseStep 6745571 = 10118357) B10118357
theorem B4497047 : Blo 1997435 4497047 := bstep (se 1 (by rfl) ⟨3372785, by rfl⟩ : syracuseStep 4497047 = 6745571) B6745571
theorem B2998031 : Blo 1997435 2998031 := bstep (se 1 (by rfl) ⟨2248523, by rfl⟩ : syracuseStep 2998031 = 4497047) B4497047
theorem B1998687 : Blo 1997435 1998687 := bstep (se 1 (by rfl) ⟨1499015, by rfl⟩ : syracuseStep 1998687 = 2998031) B2998031
theorem B2998037 : Blo 1997435 2998037 := bbase (se 6 (by rfl) ⟨70266, by rfl⟩ : syracuseStep 2998037 = 140533) (by norm_num)
theorem B1998691 : Blo 1997435 1998691 := bstep (se 1 (by rfl) ⟨1499018, by rfl⟩ : syracuseStep 1998691 = 2998037) B2998037
theorem B3465461 : Blo 1997435 3465461 := bbase (se 5 (by rfl) ⟨162443, by rfl⟩ : syracuseStep 3465461 = 324887) (by norm_num)
theorem B9241229 : Blo 1997435 9241229 := bstep (se 3 (by rfl) ⟨1732730, by rfl⟩ : syracuseStep 9241229 = 3465461) B3465461
theorem B24643277 : Blo 1997435 24643277 := bstep (se 3 (by rfl) ⟨4620614, by rfl⟩ : syracuseStep 24643277 = 9241229) B9241229
theorem B16428851 : Blo 1997435 16428851 := bstep (se 1 (by rfl) ⟨12321638, by rfl⟩ : syracuseStep 16428851 = 24643277) B24643277
theorem B10952567 : Blo 1997435 10952567 := bstep (se 1 (by rfl) ⟨8214425, by rfl⟩ : syracuseStep 10952567 = 16428851) B16428851
theorem B7301711 : Blo 1997435 7301711 := bstep (se 1 (by rfl) ⟨5476283, by rfl⟩ : syracuseStep 7301711 = 10952567) B10952567
theorem B4867807 : Blo 1997435 4867807 := bstep (se 1 (by rfl) ⟨3650855, by rfl⟩ : syracuseStep 4867807 = 7301711) B7301711
theorem B6490409 : Blo 1997435 6490409 := bstep (se 2 (by rfl) ⟨2433903, by rfl⟩ : syracuseStep 6490409 = 4867807) B4867807
theorem B17307757 : Blo 1997435 17307757 := bstep (se 3 (by rfl) ⟨3245204, by rfl⟩ : syracuseStep 17307757 = 6490409) B6490409
theorem B23077009 : Blo 1997435 23077009 := bstep (se 2 (by rfl) ⟨8653878, by rfl⟩ : syracuseStep 23077009 = 17307757) B17307757
theorem B30769345 : Blo 1997435 30769345 := bstep (se 2 (by rfl) ⟨11538504, by rfl⟩ : syracuseStep 30769345 = 23077009) B23077009
theorem B41025793 : Blo 1997435 41025793 := bstep (se 2 (by rfl) ⟨15384672, by rfl⟩ : syracuseStep 41025793 = 30769345) B30769345
theorem B54701057 : Blo 1997435 54701057 := bstep (se 2 (by rfl) ⟨20512896, by rfl⟩ : syracuseStep 54701057 = 41025793) B41025793
theorem B36467371 : Blo 1997435 36467371 := bstep (se 1 (by rfl) ⟨27350528, by rfl⟩ : syracuseStep 36467371 = 54701057) B54701057
theorem B48623161 : Blo 1997435 48623161 := bstep (se 2 (by rfl) ⟨18233685, by rfl⟩ : syracuseStep 48623161 = 36467371) B36467371
theorem B64830881 : Blo 1997435 64830881 := bstep (se 2 (by rfl) ⟨24311580, by rfl⟩ : syracuseStep 64830881 = 48623161) B48623161
theorem B43220587 : Blo 1997435 43220587 := bstep (se 1 (by rfl) ⟨32415440, by rfl⟩ : syracuseStep 43220587 = 64830881) B64830881
theorem B57627449 : Blo 1997435 57627449 := bstep (se 2 (by rfl) ⟨21610293, by rfl⟩ : syracuseStep 57627449 = 43220587) B43220587
theorem B38418299 : Blo 1997435 38418299 := bstep (se 1 (by rfl) ⟨28813724, by rfl⟩ : syracuseStep 38418299 = 57627449) B57627449
theorem B25612199 : Blo 1997435 25612199 := bstep (se 1 (by rfl) ⟨19209149, by rfl⟩ : syracuseStep 25612199 = 38418299) B38418299
theorem B17074799 : Blo 1997435 17074799 := bstep (se 1 (by rfl) ⟨12806099, by rfl⟩ : syracuseStep 17074799 = 25612199) B25612199
theorem B11383199 : Blo 1997435 11383199 := bstep (se 1 (by rfl) ⟨8537399, by rfl⟩ : syracuseStep 11383199 = 17074799) B17074799
theorem B7588799 : Blo 1997435 7588799 := bstep (se 1 (by rfl) ⟨5691599, by rfl⟩ : syracuseStep 7588799 = 11383199) B11383199
theorem B5059199 : Blo 1997435 5059199 := bstep (se 1 (by rfl) ⟨3794399, by rfl⟩ : syracuseStep 5059199 = 7588799) B7588799
theorem B3372799 : Blo 1997435 3372799 := bstep (se 1 (by rfl) ⟨2529599, by rfl⟩ : syracuseStep 3372799 = 5059199) B5059199
theorem B4497065 : Blo 1997435 4497065 := bstep (se 2 (by rfl) ⟨1686399, by rfl⟩ : syracuseStep 4497065 = 3372799) B3372799
theorem B2998043 : Blo 1997435 2998043 := bstep (se 1 (by rfl) ⟨2248532, by rfl⟩ : syracuseStep 2998043 = 4497065) B4497065
theorem B1998695 : Blo 1997435 1998695 := bstep (se 1 (by rfl) ⟨1499021, by rfl⟩ : syracuseStep 1998695 = 2998043) B2998043
theorem B2248537 : Blo 1997435 2248537 := bbase (se 2 (by rfl) ⟨843201, by rfl⟩ : syracuseStep 2248537 = 1686403) (by norm_num)
theorem B2998049 : Blo 1997435 2998049 := bstep (se 2 (by rfl) ⟨1124268, by rfl⟩ : syracuseStep 2998049 = 2248537) B2248537
theorem B1998699 : Blo 1997435 1998699 := bstep (se 1 (by rfl) ⟨1499024, by rfl⟩ : syracuseStep 1998699 = 2998049) B2998049
theorem B4268717 : Blo 1997435 4268717 := bbase (se 3 (by rfl) ⟨800384, by rfl⟩ : syracuseStep 4268717 = 1600769) (by norm_num)
theorem B2845811 : Blo 1997435 2845811 := bstep (se 1 (by rfl) ⟨2134358, by rfl⟩ : syracuseStep 2845811 = 4268717) B4268717
theorem B7588829 : Blo 1997435 7588829 := bstep (se 3 (by rfl) ⟨1422905, by rfl⟩ : syracuseStep 7588829 = 2845811) B2845811
theorem B5059219 : Blo 1997435 5059219 := bstep (se 1 (by rfl) ⟨3794414, by rfl⟩ : syracuseStep 5059219 = 7588829) B7588829
theorem B6745625 : Blo 1997435 6745625 := bstep (se 2 (by rfl) ⟨2529609, by rfl⟩ : syracuseStep 6745625 = 5059219) B5059219
theorem B4497083 : Blo 1997435 4497083 := bstep (se 1 (by rfl) ⟨3372812, by rfl⟩ : syracuseStep 4497083 = 6745625) B6745625
theorem B2998055 : Blo 1997435 2998055 := bstep (se 1 (by rfl) ⟨2248541, by rfl⟩ : syracuseStep 2998055 = 4497083) B4497083
theorem B1998703 : Blo 1997435 1998703 := bstep (se 1 (by rfl) ⟨1499027, by rfl⟩ : syracuseStep 1998703 = 2998055) B2998055
theorem B2998061 : Blo 1997435 2998061 := bbase (se 3 (by rfl) ⟨562136, by rfl⟩ : syracuseStep 2998061 = 1124273) (by norm_num)
theorem B1998707 : Blo 1997435 1998707 := bstep (se 1 (by rfl) ⟨1499030, by rfl⟩ : syracuseStep 1998707 = 2998061) B2998061
theorem B4497101 : Blo 1997435 4497101 := bbase (se 3 (by rfl) ⟨843206, by rfl⟩ : syracuseStep 4497101 = 1686413) (by norm_num)
theorem B2998067 : Blo 1997435 2998067 := bstep (se 1 (by rfl) ⟨2248550, by rfl⟩ : syracuseStep 2998067 = 4497101) B4497101
theorem B1998711 : Blo 1997435 1998711 := bstep (se 1 (by rfl) ⟨1499033, by rfl⟩ : syracuseStep 1998711 = 2998067) B2998067
theorem B2529625 : Blo 1997435 2529625 := bbase (se 2 (by rfl) ⟨948609, by rfl⟩ : syracuseStep 2529625 = 1897219) (by norm_num)
theorem B3372833 : Blo 1997435 3372833 := bstep (se 2 (by rfl) ⟨1264812, by rfl⟩ : syracuseStep 3372833 = 2529625) B2529625
theorem B2248555 : Blo 1997435 2248555 := bstep (se 1 (by rfl) ⟨1686416, by rfl⟩ : syracuseStep 2248555 = 3372833) B3372833
theorem B2998073 : Blo 1997435 2998073 := bstep (se 2 (by rfl) ⟨1124277, by rfl⟩ : syracuseStep 2998073 = 2248555) B2248555
theorem B1998715 : Blo 1997435 1998715 := bstep (se 1 (by rfl) ⟨1499036, by rfl⟩ : syracuseStep 1998715 = 2998073) B2998073
theorem B18233909 : Blo 1997435 18233909 := bbase (se 5 (by rfl) ⟨854714, by rfl⟩ : syracuseStep 18233909 = 1709429) (by norm_num)
theorem B12155939 : Blo 1997435 12155939 := bstep (se 1 (by rfl) ⟨9116954, by rfl⟩ : syracuseStep 12155939 = 18233909) B18233909
theorem B8103959 : Blo 1997435 8103959 := bstep (se 1 (by rfl) ⟨6077969, by rfl⟩ : syracuseStep 8103959 = 12155939) B12155939
theorem B5402639 : Blo 1997435 5402639 := bstep (se 1 (by rfl) ⟨4051979, by rfl⟩ : syracuseStep 5402639 = 8103959) B8103959
theorem B3601759 : Blo 1997435 3601759 := bstep (se 1 (by rfl) ⟨2701319, by rfl⟩ : syracuseStep 3601759 = 5402639) B5402639
theorem B4802345 : Blo 1997435 4802345 := bstep (se 2 (by rfl) ⟨1800879, by rfl⟩ : syracuseStep 4802345 = 3601759) B3601759
theorem B3201563 : Blo 1997435 3201563 := bstep (se 1 (by rfl) ⟨2401172, by rfl⟩ : syracuseStep 3201563 = 4802345) B4802345
theorem B8537501 : Blo 1997435 8537501 := bstep (se 3 (by rfl) ⟨1600781, by rfl⟩ : syracuseStep 8537501 = 3201563) B3201563
theorem B22766669 : Blo 1997435 22766669 := bstep (se 3 (by rfl) ⟨4268750, by rfl⟩ : syracuseStep 22766669 = 8537501) B8537501
theorem B15177779 : Blo 1997435 15177779 := bstep (se 1 (by rfl) ⟨11383334, by rfl⟩ : syracuseStep 15177779 = 22766669) B22766669
theorem B10118519 : Blo 1997435 10118519 := bstep (se 1 (by rfl) ⟨7588889, by rfl⟩ : syracuseStep 10118519 = 15177779) B15177779
theorem B6745679 : Blo 1997435 6745679 := bstep (se 1 (by rfl) ⟨5059259, by rfl⟩ : syracuseStep 6745679 = 10118519) B10118519
theorem B4497119 : Blo 1997435 4497119 := bstep (se 1 (by rfl) ⟨3372839, by rfl⟩ : syracuseStep 4497119 = 6745679) B6745679
theorem B2998079 : Blo 1997435 2998079 := bstep (se 1 (by rfl) ⟨2248559, by rfl⟩ : syracuseStep 2998079 = 4497119) B4497119
theorem B1998719 : Blo 1997435 1998719 := bstep (se 1 (by rfl) ⟨1499039, by rfl⟩ : syracuseStep 1998719 = 2998079) B2998079
theorem B2998085 : Blo 1997435 2998085 := bbase (se 4 (by rfl) ⟨281070, by rfl⟩ : syracuseStep 2998085 = 562141) (by norm_num)
theorem B1998723 : Blo 1997435 1998723 := bstep (se 1 (by rfl) ⟨1499042, by rfl⟩ : syracuseStep 1998723 = 2998085) B2998085
theorem B3372853 : Blo 1997435 3372853 := bbase (se 5 (by rfl) ⟨158102, by rfl⟩ : syracuseStep 3372853 = 316205) (by norm_num)
theorem B4497137 : Blo 1997435 4497137 := bstep (se 2 (by rfl) ⟨1686426, by rfl⟩ : syracuseStep 4497137 = 3372853) B3372853
theorem B2998091 : Blo 1997435 2998091 := bstep (se 1 (by rfl) ⟨2248568, by rfl⟩ : syracuseStep 2998091 = 4497137) B4497137
theorem B1998727 : Blo 1997435 1998727 := bstep (se 1 (by rfl) ⟨1499045, by rfl⟩ : syracuseStep 1998727 = 2998091) B2998091
theorem B2248573 : Blo 1997435 2248573 := bbase (se 3 (by rfl) ⟨421607, by rfl⟩ : syracuseStep 2248573 = 843215) (by norm_num)
theorem B2998097 : Blo 1997435 2998097 := bstep (se 2 (by rfl) ⟨1124286, by rfl⟩ : syracuseStep 2998097 = 2248573) B2248573
theorem B1998731 : Blo 1997435 1998731 := bstep (se 1 (by rfl) ⟨1499048, by rfl⟩ : syracuseStep 1998731 = 2998097) B2998097
theorem B6745733 : Blo 1997435 6745733 := bbase (se 4 (by rfl) ⟨632412, by rfl⟩ : syracuseStep 6745733 = 1264825) (by norm_num)
theorem B4497155 : Blo 1997435 4497155 := bstep (se 1 (by rfl) ⟨3372866, by rfl⟩ : syracuseStep 4497155 = 6745733) B6745733
theorem B2998103 : Blo 1997435 2998103 := bstep (se 1 (by rfl) ⟨2248577, by rfl⟩ : syracuseStep 2998103 = 4497155) B4497155
theorem B1998735 : Blo 1997435 1998735 := bstep (se 1 (by rfl) ⟨1499051, by rfl⟩ : syracuseStep 1998735 = 2998103) B2998103
theorem B2998109 : Blo 1997435 2998109 := bbase (se 3 (by rfl) ⟨562145, by rfl⟩ : syracuseStep 2998109 = 1124291) (by norm_num)
theorem B1998739 : Blo 1997435 1998739 := bstep (se 1 (by rfl) ⟨1499054, by rfl⟩ : syracuseStep 1998739 = 2998109) B2998109
theorem B4497173 : Blo 1997435 4497173 := bbase (se 6 (by rfl) ⟨105402, by rfl⟩ : syracuseStep 4497173 = 210805) (by norm_num)
theorem B2998115 : Blo 1997435 2998115 := bstep (se 1 (by rfl) ⟨2248586, by rfl⟩ : syracuseStep 2998115 = 4497173) B4497173
theorem B1998743 : Blo 1997435 1998743 := bstep (se 1 (by rfl) ⟨1499057, by rfl⟩ : syracuseStep 1998743 = 2998115) B2998115
theorem B7588997 : Blo 1997435 7588997 := bbase (se 4 (by rfl) ⟨711468, by rfl⟩ : syracuseStep 7588997 = 1422937) (by norm_num)
theorem B5059331 : Blo 1997435 5059331 := bstep (se 1 (by rfl) ⟨3794498, by rfl⟩ : syracuseStep 5059331 = 7588997) B7588997
theorem B3372887 : Blo 1997435 3372887 := bstep (se 1 (by rfl) ⟨2529665, by rfl⟩ : syracuseStep 3372887 = 5059331) B5059331
theorem B2248591 : Blo 1997435 2248591 := bstep (se 1 (by rfl) ⟨1686443, by rfl⟩ : syracuseStep 2248591 = 3372887) B3372887
theorem B2998121 : Blo 1997435 2998121 := bstep (se 2 (by rfl) ⟨1124295, by rfl⟩ : syracuseStep 2998121 = 2248591) B2248591
theorem B1998747 : Blo 1997435 1998747 := bstep (se 1 (by rfl) ⟨1499060, by rfl⟩ : syracuseStep 1998747 = 2998121) B2998121
theorem B4052045 : Blo 1997435 4052045 := bbase (se 3 (by rfl) ⟨759758, by rfl⟩ : syracuseStep 4052045 = 1519517) (by norm_num)
theorem B2701363 : Blo 1997435 2701363 := bstep (se 1 (by rfl) ⟨2026022, by rfl⟩ : syracuseStep 2701363 = 4052045) B4052045
theorem B3601817 : Blo 1997435 3601817 := bstep (se 2 (by rfl) ⟨1350681, by rfl⟩ : syracuseStep 3601817 = 2701363) B2701363
theorem B2401211 : Blo 1997435 2401211 := bstep (se 1 (by rfl) ⟨1800908, by rfl⟩ : syracuseStep 2401211 = 3601817) B3601817
theorem B6403229 : Blo 1997435 6403229 := bstep (se 3 (by rfl) ⟨1200605, by rfl⟩ : syracuseStep 6403229 = 2401211) B2401211
theorem B4268819 : Blo 1997435 4268819 := bstep (se 1 (by rfl) ⟨3201614, by rfl⟩ : syracuseStep 4268819 = 6403229) B6403229
theorem B11383517 : Blo 1997435 11383517 := bstep (se 3 (by rfl) ⟨2134409, by rfl⟩ : syracuseStep 11383517 = 4268819) B4268819
theorem B7589011 : Blo 1997435 7589011 := bstep (se 1 (by rfl) ⟨5691758, by rfl⟩ : syracuseStep 7589011 = 11383517) B11383517
theorem B10118681 : Blo 1997435 10118681 := bstep (se 2 (by rfl) ⟨3794505, by rfl⟩ : syracuseStep 10118681 = 7589011) B7589011
theorem B6745787 : Blo 1997435 6745787 := bstep (se 1 (by rfl) ⟨5059340, by rfl⟩ : syracuseStep 6745787 = 10118681) B10118681
theorem B4497191 : Blo 1997435 4497191 := bstep (se 1 (by rfl) ⟨3372893, by rfl⟩ : syracuseStep 4497191 = 6745787) B6745787
theorem B2998127 : Blo 1997435 2998127 := bstep (se 1 (by rfl) ⟨2248595, by rfl⟩ : syracuseStep 2998127 = 4497191) B4497191
theorem B1998751 : Blo 1997435 1998751 := bstep (se 1 (by rfl) ⟨1499063, by rfl⟩ : syracuseStep 1998751 = 2998127) B2998127
theorem B2998133 : Blo 1997435 2998133 := bbase (se 5 (by rfl) ⟨140537, by rfl⟩ : syracuseStep 2998133 = 281075) (by norm_num)
theorem B1998755 : Blo 1997435 1998755 := bstep (se 1 (by rfl) ⟨1499066, by rfl⟩ : syracuseStep 1998755 = 2998133) B2998133
theorem B4268837 : Blo 1997435 4268837 := bbase (se 4 (by rfl) ⟨400203, by rfl⟩ : syracuseStep 4268837 = 800407) (by norm_num)
theorem B2845891 : Blo 1997435 2845891 := bstep (se 1 (by rfl) ⟨2134418, by rfl⟩ : syracuseStep 2845891 = 4268837) B4268837
theorem B3794521 : Blo 1997435 3794521 := bstep (se 2 (by rfl) ⟨1422945, by rfl⟩ : syracuseStep 3794521 = 2845891) B2845891
theorem B5059361 : Blo 1997435 5059361 := bstep (se 2 (by rfl) ⟨1897260, by rfl⟩ : syracuseStep 5059361 = 3794521) B3794521
theorem B3372907 : Blo 1997435 3372907 := bstep (se 1 (by rfl) ⟨2529680, by rfl⟩ : syracuseStep 3372907 = 5059361) B5059361
theorem B4497209 : Blo 1997435 4497209 := bstep (se 2 (by rfl) ⟨1686453, by rfl⟩ : syracuseStep 4497209 = 3372907) B3372907
theorem B2998139 : Blo 1997435 2998139 := bstep (se 1 (by rfl) ⟨2248604, by rfl⟩ : syracuseStep 2998139 = 4497209) B4497209
theorem B1998759 : Blo 1997435 1998759 := bstep (se 1 (by rfl) ⟨1499069, by rfl⟩ : syracuseStep 1998759 = 2998139) B2998139
theorem B2248609 : Blo 1997435 2248609 := bbase (se 2 (by rfl) ⟨843228, by rfl⟩ : syracuseStep 2248609 = 1686457) (by norm_num)
theorem B2998145 : Blo 1997435 2998145 := bstep (se 2 (by rfl) ⟨1124304, by rfl⟩ : syracuseStep 2998145 = 2248609) B2248609
theorem B1998763 : Blo 1997435 1998763 := bstep (se 1 (by rfl) ⟨1499072, by rfl⟩ : syracuseStep 1998763 = 2998145) B2998145
theorem B5059381 : Blo 1997435 5059381 := bbase (se 5 (by rfl) ⟨237158, by rfl⟩ : syracuseStep 5059381 = 474317) (by norm_num)
theorem B6745841 : Blo 1997435 6745841 := bstep (se 2 (by rfl) ⟨2529690, by rfl⟩ : syracuseStep 6745841 = 5059381) B5059381
theorem B4497227 : Blo 1997435 4497227 := bstep (se 1 (by rfl) ⟨3372920, by rfl⟩ : syracuseStep 4497227 = 6745841) B6745841
theorem B2998151 : Blo 1997435 2998151 := bstep (se 1 (by rfl) ⟨2248613, by rfl⟩ : syracuseStep 2998151 = 4497227) B4497227
theorem B1998767 : Blo 1997435 1998767 := bstep (se 1 (by rfl) ⟨1499075, by rfl⟩ : syracuseStep 1998767 = 2998151) B2998151
theorem B2998157 : Blo 1997435 2998157 := bbase (se 3 (by rfl) ⟨562154, by rfl⟩ : syracuseStep 2998157 = 1124309) (by norm_num)
theorem B1998771 : Blo 1997435 1998771 := bstep (se 1 (by rfl) ⟨1499078, by rfl⟩ : syracuseStep 1998771 = 2998157) B2998157
theorem B4497245 : Blo 1997435 4497245 := bbase (se 3 (by rfl) ⟨843233, by rfl⟩ : syracuseStep 4497245 = 1686467) (by norm_num)
theorem B2998163 : Blo 1997435 2998163 := bstep (se 1 (by rfl) ⟨2248622, by rfl⟩ : syracuseStep 2998163 = 4497245) B4497245
theorem B1998775 : Blo 1997435 1998775 := bstep (se 1 (by rfl) ⟨1499081, by rfl⟩ : syracuseStep 1998775 = 2998163) B2998163
theorem B3372941 : Blo 1997435 3372941 := bbase (se 3 (by rfl) ⟨632426, by rfl⟩ : syracuseStep 3372941 = 1264853) (by norm_num)
theorem B2248627 : Blo 1997435 2248627 := bstep (se 1 (by rfl) ⟨1686470, by rfl⟩ : syracuseStep 2248627 = 3372941) B3372941
theorem B2998169 : Blo 1997435 2998169 := bstep (se 2 (by rfl) ⟨1124313, by rfl⟩ : syracuseStep 2998169 = 2248627) B2248627
theorem B1998779 : Blo 1997435 1998779 := bstep (se 1 (by rfl) ⟨1499084, by rfl⟩ : syracuseStep 1998779 = 2998169) B2998169
theorem B9604997 : Blo 1997435 9604997 := bbase (se 4 (by rfl) ⟨900468, by rfl⟩ : syracuseStep 9604997 = 1800937) (by norm_num)
theorem B6403331 : Blo 1997435 6403331 := bstep (se 1 (by rfl) ⟨4802498, by rfl⟩ : syracuseStep 6403331 = 9604997) B9604997
theorem B17075549 : Blo 1997435 17075549 := bstep (se 3 (by rfl) ⟨3201665, by rfl⟩ : syracuseStep 17075549 = 6403331) B6403331
theorem B11383699 : Blo 1997435 11383699 := bstep (se 1 (by rfl) ⟨8537774, by rfl⟩ : syracuseStep 11383699 = 17075549) B17075549
theorem B15178265 : Blo 1997435 15178265 := bstep (se 2 (by rfl) ⟨5691849, by rfl⟩ : syracuseStep 15178265 = 11383699) B11383699
theorem B10118843 : Blo 1997435 10118843 := bstep (se 1 (by rfl) ⟨7589132, by rfl⟩ : syracuseStep 10118843 = 15178265) B15178265
theorem B6745895 : Blo 1997435 6745895 := bstep (se 1 (by rfl) ⟨5059421, by rfl⟩ : syracuseStep 6745895 = 10118843) B10118843
theorem B4497263 : Blo 1997435 4497263 := bstep (se 1 (by rfl) ⟨3372947, by rfl⟩ : syracuseStep 4497263 = 6745895) B6745895
theorem B2998175 : Blo 1997435 2998175 := bstep (se 1 (by rfl) ⟨2248631, by rfl⟩ : syracuseStep 2998175 = 4497263) B4497263
theorem B1998783 : Blo 1997435 1998783 := bstep (se 1 (by rfl) ⟨1499087, by rfl⟩ : syracuseStep 1998783 = 2998175) B2998175
theorem B2998181 : Blo 1997435 2998181 := bbase (se 4 (by rfl) ⟨281079, by rfl⟩ : syracuseStep 2998181 = 562159) (by norm_num)
theorem B1998787 : Blo 1997435 1998787 := bstep (se 1 (by rfl) ⟨1499090, by rfl⟩ : syracuseStep 1998787 = 2998181) B2998181
theorem B2529721 : Blo 1997435 2529721 := bbase (se 2 (by rfl) ⟨948645, by rfl⟩ : syracuseStep 2529721 = 1897291) (by norm_num)
theorem B3372961 : Blo 1997435 3372961 := bstep (se 2 (by rfl) ⟨1264860, by rfl⟩ : syracuseStep 3372961 = 2529721) B2529721
theorem B4497281 : Blo 1997435 4497281 := bstep (se 2 (by rfl) ⟨1686480, by rfl⟩ : syracuseStep 4497281 = 3372961) B3372961
theorem B2998187 : Blo 1997435 2998187 := bstep (se 1 (by rfl) ⟨2248640, by rfl⟩ : syracuseStep 2998187 = 4497281) B4497281
theorem B1998791 : Blo 1997435 1998791 := bstep (se 1 (by rfl) ⟨1499093, by rfl⟩ : syracuseStep 1998791 = 2998187) B2998187
theorem B2248645 : Blo 1997435 2248645 := bbase (se 4 (by rfl) ⟨210810, by rfl⟩ : syracuseStep 2248645 = 421621) (by norm_num)
theorem B2998193 : Blo 1997435 2998193 := bstep (se 2 (by rfl) ⟨1124322, by rfl⟩ : syracuseStep 2998193 = 2248645) B2248645
theorem B1998795 : Blo 1997435 1998795 := bstep (se 1 (by rfl) ⟨1499096, by rfl⟩ : syracuseStep 1998795 = 2998193) B2998193
theorem B3794597 : Blo 1997435 3794597 := bbase (se 4 (by rfl) ⟨355743, by rfl⟩ : syracuseStep 3794597 = 711487) (by norm_num)
theorem B2529731 : Blo 1997435 2529731 := bstep (se 1 (by rfl) ⟨1897298, by rfl⟩ : syracuseStep 2529731 = 3794597) B3794597
theorem B6745949 : Blo 1997435 6745949 := bstep (se 3 (by rfl) ⟨1264865, by rfl⟩ : syracuseStep 6745949 = 2529731) B2529731
theorem B4497299 : Blo 1997435 4497299 := bstep (se 1 (by rfl) ⟨3372974, by rfl⟩ : syracuseStep 4497299 = 6745949) B6745949
theorem B2998199 : Blo 1997435 2998199 := bstep (se 1 (by rfl) ⟨2248649, by rfl⟩ : syracuseStep 2998199 = 4497299) B4497299
theorem B1998799 : Blo 1997435 1998799 := bstep (se 1 (by rfl) ⟨1499099, by rfl⟩ : syracuseStep 1998799 = 2998199) B2998199
theorem B2998205 : Blo 1997435 2998205 := bbase (se 3 (by rfl) ⟨562163, by rfl⟩ : syracuseStep 2998205 = 1124327) (by norm_num)
theorem B1998803 : Blo 1997435 1998803 := bstep (se 1 (by rfl) ⟨1499102, by rfl⟩ : syracuseStep 1998803 = 2998205) B2998205
theorem B4497317 : Blo 1997435 4497317 := bbase (se 4 (by rfl) ⟨421623, by rfl⟩ : syracuseStep 4497317 = 843247) (by norm_num)
theorem B2998211 : Blo 1997435 2998211 := bstep (se 1 (by rfl) ⟨2248658, by rfl⟩ : syracuseStep 2998211 = 4497317) B4497317
theorem B1998807 : Blo 1997435 1998807 := bstep (se 1 (by rfl) ⟨1499105, by rfl⟩ : syracuseStep 1998807 = 2998211) B2998211
theorem B5059493 : Blo 1997435 5059493 := bbase (se 4 (by rfl) ⟨474327, by rfl⟩ : syracuseStep 5059493 = 948655) (by norm_num)
theorem B3372995 : Blo 1997435 3372995 := bstep (se 1 (by rfl) ⟨2529746, by rfl⟩ : syracuseStep 3372995 = 5059493) B5059493
theorem B2248663 : Blo 1997435 2248663 := bstep (se 1 (by rfl) ⟨1686497, by rfl⟩ : syracuseStep 2248663 = 3372995) B3372995
theorem B2998217 : Blo 1997435 2998217 := bstep (se 2 (by rfl) ⟨1124331, by rfl⟩ : syracuseStep 2998217 = 2248663) B2248663
theorem B1998811 : Blo 1997435 1998811 := bstep (se 1 (by rfl) ⟨1499108, by rfl⟩ : syracuseStep 1998811 = 2998217) B2998217
theorem B5691941 : Blo 1997435 5691941 := bbase (se 4 (by rfl) ⟨533619, by rfl⟩ : syracuseStep 5691941 = 1067239) (by norm_num)
theorem B3794627 : Blo 1997435 3794627 := bstep (se 1 (by rfl) ⟨2845970, by rfl⟩ : syracuseStep 3794627 = 5691941) B5691941
theorem B10119005 : Blo 1997435 10119005 := bstep (se 3 (by rfl) ⟨1897313, by rfl⟩ : syracuseStep 10119005 = 3794627) B3794627
theorem B6746003 : Blo 1997435 6746003 := bstep (se 1 (by rfl) ⟨5059502, by rfl⟩ : syracuseStep 6746003 = 10119005) B10119005
theorem B4497335 : Blo 1997435 4497335 := bstep (se 1 (by rfl) ⟨3373001, by rfl⟩ : syracuseStep 4497335 = 6746003) B6746003
theorem B2998223 : Blo 1997435 2998223 := bstep (se 1 (by rfl) ⟨2248667, by rfl⟩ : syracuseStep 2998223 = 4497335) B4497335
theorem B1998815 : Blo 1997435 1998815 := bstep (se 1 (by rfl) ⟨1499111, by rfl⟩ : syracuseStep 1998815 = 2998223) B2998223
theorem B2998229 : Blo 1997435 2998229 := bbase (se 7 (by rfl) ⟨35135, by rfl⟩ : syracuseStep 2998229 = 70271) (by norm_num)
theorem B1998819 : Blo 1997435 1998819 := bstep (se 1 (by rfl) ⟨1499114, by rfl⟩ : syracuseStep 1998819 = 2998229) B2998229
theorem B7589285 : Blo 1997435 7589285 := bbase (se 4 (by rfl) ⟨711495, by rfl⟩ : syracuseStep 7589285 = 1422991) (by norm_num)
theorem B5059523 : Blo 1997435 5059523 := bstep (se 1 (by rfl) ⟨3794642, by rfl⟩ : syracuseStep 5059523 = 7589285) B7589285
theorem B3373015 : Blo 1997435 3373015 := bstep (se 1 (by rfl) ⟨2529761, by rfl⟩ : syracuseStep 3373015 = 5059523) B5059523
theorem B4497353 : Blo 1997435 4497353 := bstep (se 2 (by rfl) ⟨1686507, by rfl⟩ : syracuseStep 4497353 = 3373015) B3373015
theorem B2998235 : Blo 1997435 2998235 := bstep (se 1 (by rfl) ⟨2248676, by rfl⟩ : syracuseStep 2998235 = 4497353) B4497353
theorem B1998823 : Blo 1997435 1998823 := bstep (se 1 (by rfl) ⟨1499117, by rfl⟩ : syracuseStep 1998823 = 2998235) B2998235
theorem B2248681 : Blo 1997435 2248681 := bbase (se 2 (by rfl) ⟨843255, by rfl⟩ : syracuseStep 2248681 = 1686511) (by norm_num)
theorem B2998241 : Blo 1997435 2998241 := bstep (se 2 (by rfl) ⟨1124340, by rfl⟩ : syracuseStep 2998241 = 2248681) B2248681
theorem B1998827 : Blo 1997435 1998827 := bstep (se 1 (by rfl) ⟨1499120, by rfl⟩ : syracuseStep 1998827 = 2998241) B2998241
theorem B2193137 : Blo 1997435 2193137 := bbase (se 2 (by rfl) ⟨822426, by rfl⟩ : syracuseStep 2193137 = 1644853) (by norm_num)
theorem B23393461 : Blo 1997435 23393461 := bstep (se 5 (by rfl) ⟨1096568, by rfl⟩ : syracuseStep 23393461 = 2193137) B2193137
theorem B31191281 : Blo 1997435 31191281 := bstep (se 2 (by rfl) ⟨11696730, by rfl⟩ : syracuseStep 31191281 = 23393461) B23393461
theorem B20794187 : Blo 1997435 20794187 := bstep (se 1 (by rfl) ⟨15595640, by rfl⟩ : syracuseStep 20794187 = 31191281) B31191281
theorem B13862791 : Blo 1997435 13862791 := bstep (se 1 (by rfl) ⟨10397093, by rfl⟩ : syracuseStep 13862791 = 20794187) B20794187
theorem B18483721 : Blo 1997435 18483721 := bstep (se 2 (by rfl) ⟨6931395, by rfl⟩ : syracuseStep 18483721 = 13862791) B13862791
theorem B98579845 : Blo 1997435 98579845 := bstep (se 4 (by rfl) ⟨9241860, by rfl⟩ : syracuseStep 98579845 = 18483721) B18483721
theorem B131439793 : Blo 1997435 131439793 := bstep (se 2 (by rfl) ⟨49289922, by rfl⟩ : syracuseStep 131439793 = 98579845) B98579845
theorem B175253057 : Blo 1997435 175253057 := bstep (se 2 (by rfl) ⟨65719896, by rfl⟩ : syracuseStep 175253057 = 131439793) B131439793
theorem B116835371 : Blo 1997435 116835371 := bstep (se 1 (by rfl) ⟨87626528, by rfl⟩ : syracuseStep 116835371 = 175253057) B175253057
theorem B77890247 : Blo 1997435 77890247 := bstep (se 1 (by rfl) ⟨58417685, by rfl⟩ : syracuseStep 77890247 = 116835371) B116835371
theorem B51926831 : Blo 1997435 51926831 := bstep (se 1 (by rfl) ⟨38945123, by rfl⟩ : syracuseStep 51926831 = 77890247) B77890247
theorem B34617887 : Blo 1997435 34617887 := bstep (se 1 (by rfl) ⟨25963415, by rfl⟩ : syracuseStep 34617887 = 51926831) B51926831
theorem B23078591 : Blo 1997435 23078591 := bstep (se 1 (by rfl) ⟨17308943, by rfl⟩ : syracuseStep 23078591 = 34617887) B34617887
theorem B15385727 : Blo 1997435 15385727 := bstep (se 1 (by rfl) ⟨11539295, by rfl⟩ : syracuseStep 15385727 = 23078591) B23078591
theorem B10257151 : Blo 1997435 10257151 := bstep (se 1 (by rfl) ⟨7692863, by rfl⟩ : syracuseStep 10257151 = 15385727) B15385727
theorem B13676201 : Blo 1997435 13676201 := bstep (se 2 (by rfl) ⟨5128575, by rfl⟩ : syracuseStep 13676201 = 10257151) B10257151
theorem B9117467 : Blo 1997435 9117467 := bstep (se 1 (by rfl) ⟨6838100, by rfl⟩ : syracuseStep 9117467 = 13676201) B13676201
theorem B6078311 : Blo 1997435 6078311 := bstep (se 1 (by rfl) ⟨4558733, by rfl⟩ : syracuseStep 6078311 = 9117467) B9117467
theorem B4052207 : Blo 1997435 4052207 := bstep (se 1 (by rfl) ⟨3039155, by rfl⟩ : syracuseStep 4052207 = 6078311) B6078311
theorem B10805885 : Blo 1997435 10805885 := bstep (se 3 (by rfl) ⟨2026103, by rfl⟩ : syracuseStep 10805885 = 4052207) B4052207
theorem B7203923 : Blo 1997435 7203923 := bstep (se 1 (by rfl) ⟨5402942, by rfl⟩ : syracuseStep 7203923 = 10805885) B10805885
theorem B4802615 : Blo 1997435 4802615 := bstep (se 1 (by rfl) ⟨3601961, by rfl⟩ : syracuseStep 4802615 = 7203923) B7203923
theorem B3201743 : Blo 1997435 3201743 := bstep (se 1 (by rfl) ⟨2401307, by rfl⟩ : syracuseStep 3201743 = 4802615) B4802615
theorem B2134495 : Blo 1997435 2134495 := bstep (se 1 (by rfl) ⟨1600871, by rfl⟩ : syracuseStep 2134495 = 3201743) B3201743
theorem B11383973 : Blo 1997435 11383973 := bstep (se 4 (by rfl) ⟨1067247, by rfl⟩ : syracuseStep 11383973 = 2134495) B2134495
theorem B7589315 : Blo 1997435 7589315 := bstep (se 1 (by rfl) ⟨5691986, by rfl⟩ : syracuseStep 7589315 = 11383973) B11383973
theorem B5059543 : Blo 1997435 5059543 := bstep (se 1 (by rfl) ⟨3794657, by rfl⟩ : syracuseStep 5059543 = 7589315) B7589315
theorem B6746057 : Blo 1997435 6746057 := bstep (se 2 (by rfl) ⟨2529771, by rfl⟩ : syracuseStep 6746057 = 5059543) B5059543
theorem B4497371 : Blo 1997435 4497371 := bstep (se 1 (by rfl) ⟨3373028, by rfl⟩ : syracuseStep 4497371 = 6746057) B6746057
theorem B2998247 : Blo 1997435 2998247 := bstep (se 1 (by rfl) ⟨2248685, by rfl⟩ : syracuseStep 2998247 = 4497371) B4497371
theorem B1998831 : Blo 1997435 1998831 := bstep (se 1 (by rfl) ⟨1499123, by rfl⟩ : syracuseStep 1998831 = 2998247) B2998247
theorem B2998253 : Blo 1997435 2998253 := bbase (se 3 (by rfl) ⟨562172, by rfl⟩ : syracuseStep 2998253 = 1124345) (by norm_num)
theorem B1998835 : Blo 1997435 1998835 := bstep (se 1 (by rfl) ⟨1499126, by rfl⟩ : syracuseStep 1998835 = 2998253) B2998253
theorem B4497389 : Blo 1997435 4497389 := bbase (se 3 (by rfl) ⟨843260, by rfl⟩ : syracuseStep 4497389 = 1686521) (by norm_num)
theorem B2998259 : Blo 1997435 2998259 := bstep (se 1 (by rfl) ⟨2248694, by rfl⟩ : syracuseStep 2998259 = 4497389) B4497389
theorem B1998839 : Blo 1997435 1998839 := bstep (se 1 (by rfl) ⟨1499129, by rfl⟩ : syracuseStep 1998839 = 2998259) B2998259
theorem B4802645 : Blo 1997435 4802645 := bbase (se 8 (by rfl) ⟨28140, by rfl⟩ : syracuseStep 4802645 = 56281) (by norm_num)
theorem B3201763 : Blo 1997435 3201763 := bstep (se 1 (by rfl) ⟨2401322, by rfl⟩ : syracuseStep 3201763 = 4802645) B4802645
theorem B4269017 : Blo 1997435 4269017 := bstep (se 2 (by rfl) ⟨1600881, by rfl⟩ : syracuseStep 4269017 = 3201763) B3201763
theorem B2846011 : Blo 1997435 2846011 := bstep (se 1 (by rfl) ⟨2134508, by rfl⟩ : syracuseStep 2846011 = 4269017) B4269017
theorem B3794681 : Blo 1997435 3794681 := bstep (se 2 (by rfl) ⟨1423005, by rfl⟩ : syracuseStep 3794681 = 2846011) B2846011
theorem B2529787 : Blo 1997435 2529787 := bstep (se 1 (by rfl) ⟨1897340, by rfl⟩ : syracuseStep 2529787 = 3794681) B3794681
theorem B3373049 : Blo 1997435 3373049 := bstep (se 2 (by rfl) ⟨1264893, by rfl⟩ : syracuseStep 3373049 = 2529787) B2529787
theorem B2248699 : Blo 1997435 2248699 := bstep (se 1 (by rfl) ⟨1686524, by rfl⟩ : syracuseStep 2248699 = 3373049) B3373049
theorem B2998265 : Blo 1997435 2998265 := bstep (se 2 (by rfl) ⟨1124349, by rfl⟩ : syracuseStep 2998265 = 2248699) B2248699
theorem B1998843 : Blo 1997435 1998843 := bstep (se 1 (by rfl) ⟨1499132, by rfl⟩ : syracuseStep 1998843 = 2998265) B2998265
theorem B3802621 : Blo 1997435 3802621 := bbase (se 3 (by rfl) ⟨712991, by rfl⟩ : syracuseStep 3802621 = 1425983) (by norm_num)
theorem B5070161 : Blo 1997435 5070161 := bstep (se 2 (by rfl) ⟨1901310, by rfl⟩ : syracuseStep 5070161 = 3802621) B3802621
theorem B13520429 : Blo 1997435 13520429 := bstep (se 3 (by rfl) ⟨2535080, by rfl⟩ : syracuseStep 13520429 = 5070161) B5070161
theorem B9013619 : Blo 1997435 9013619 := bstep (se 1 (by rfl) ⟨6760214, by rfl⟩ : syracuseStep 9013619 = 13520429) B13520429
theorem B24036317 : Blo 1997435 24036317 := bstep (se 3 (by rfl) ⟨4506809, by rfl⟩ : syracuseStep 24036317 = 9013619) B9013619
theorem B16024211 : Blo 1997435 16024211 := bstep (se 1 (by rfl) ⟨12018158, by rfl⟩ : syracuseStep 16024211 = 24036317) B24036317
theorem B10682807 : Blo 1997435 10682807 := bstep (se 1 (by rfl) ⟨8012105, by rfl⟩ : syracuseStep 10682807 = 16024211) B16024211
theorem B28487485 : Blo 1997435 28487485 := bstep (se 3 (by rfl) ⟨5341403, by rfl⟩ : syracuseStep 28487485 = 10682807) B10682807
theorem B37983313 : Blo 1997435 37983313 := bstep (se 2 (by rfl) ⟨14243742, by rfl⟩ : syracuseStep 37983313 = 28487485) B28487485
theorem B50644417 : Blo 1997435 50644417 := bstep (se 2 (by rfl) ⟨18991656, by rfl⟩ : syracuseStep 50644417 = 37983313) B37983313
theorem B67525889 : Blo 1997435 67525889 := bstep (se 2 (by rfl) ⟨25322208, by rfl⟩ : syracuseStep 67525889 = 50644417) B50644417
theorem B180069037 : Blo 1997435 180069037 := bstep (se 3 (by rfl) ⟨33762944, by rfl⟩ : syracuseStep 180069037 = 67525889) B67525889
theorem B960368197 : Blo 1997435 960368197 := bstep (se 4 (by rfl) ⟨90034518, by rfl⟩ : syracuseStep 960368197 = 180069037) B180069037
theorem B1280490929 : Blo 1997435 1280490929 := bstep (se 2 (by rfl) ⟨480184098, by rfl⟩ : syracuseStep 1280490929 = 960368197) B960368197
theorem B853660619 : Blo 1997435 853660619 := bstep (se 1 (by rfl) ⟨640245464, by rfl⟩ : syracuseStep 853660619 = 1280490929) B1280490929
theorem B569107079 : Blo 1997435 569107079 := bstep (se 1 (by rfl) ⟨426830309, by rfl⟩ : syracuseStep 569107079 = 853660619) B853660619
theorem B379404719 : Blo 1997435 379404719 := bstep (se 1 (by rfl) ⟨284553539, by rfl⟩ : syracuseStep 379404719 = 569107079) B569107079
theorem B252936479 : Blo 1997435 252936479 := bstep (se 1 (by rfl) ⟨189702359, by rfl⟩ : syracuseStep 252936479 = 379404719) B379404719
theorem B168624319 : Blo 1997435 168624319 := bstep (se 1 (by rfl) ⟨126468239, by rfl⟩ : syracuseStep 168624319 = 252936479) B252936479
theorem B224832425 : Blo 1997435 224832425 := bstep (se 2 (by rfl) ⟨84312159, by rfl⟩ : syracuseStep 224832425 = 168624319) B168624319
theorem B599553133 : Blo 1997435 599553133 := bstep (se 3 (by rfl) ⟨112416212, by rfl⟩ : syracuseStep 599553133 = 224832425) B224832425
theorem B3197616709 : Blo 1997435 3197616709 := bstep (se 4 (by rfl) ⟨299776566, by rfl⟩ : syracuseStep 3197616709 = 599553133) B599553133
theorem B4263488945 : Blo 1997435 4263488945 := bstep (se 2 (by rfl) ⟨1598808354, by rfl⟩ : syracuseStep 4263488945 = 3197616709) B3197616709
theorem B2842325963 : Blo 1997435 2842325963 := bstep (se 1 (by rfl) ⟨2131744472, by rfl⟩ : syracuseStep 2842325963 = 4263488945) B4263488945
theorem B1894883975 : Blo 1997435 1894883975 := bstep (se 1 (by rfl) ⟨1421162981, by rfl⟩ : syracuseStep 1894883975 = 2842325963) B2842325963
theorem B1263255983 : Blo 1997435 1263255983 := bstep (se 1 (by rfl) ⟨947441987, by rfl⟩ : syracuseStep 1263255983 = 1894883975) B1894883975
theorem B842170655 : Blo 1997435 842170655 := bstep (se 1 (by rfl) ⟨631627991, by rfl⟩ : syracuseStep 842170655 = 1263255983) B1263255983
theorem B2245788413 : Blo 1997435 2245788413 := bstep (se 3 (by rfl) ⟨421085327, by rfl⟩ : syracuseStep 2245788413 = 842170655) B842170655
theorem B1497192275 : Blo 1997435 1497192275 := bstep (se 1 (by rfl) ⟨1122894206, by rfl⟩ : syracuseStep 1497192275 = 2245788413) B2245788413
theorem B998128183 : Blo 1997435 998128183 := bstep (se 1 (by rfl) ⟨748596137, by rfl⟩ : syracuseStep 998128183 = 1497192275) B1497192275
theorem B1330837577 : Blo 1997435 1330837577 := bstep (se 2 (by rfl) ⟨499064091, by rfl⟩ : syracuseStep 1330837577 = 998128183) B998128183
theorem B887225051 : Blo 1997435 887225051 := bstep (se 1 (by rfl) ⟨665418788, by rfl⟩ : syracuseStep 887225051 = 1330837577) B1330837577
theorem B591483367 : Blo 1997435 591483367 := bstep (se 1 (by rfl) ⟨443612525, by rfl⟩ : syracuseStep 591483367 = 887225051) B887225051
theorem B3154577957 : Blo 1997435 3154577957 := bstep (se 4 (by rfl) ⟨295741683, by rfl⟩ : syracuseStep 3154577957 = 591483367) B591483367
theorem B2103051971 : Blo 1997435 2103051971 := bstep (se 1 (by rfl) ⟨1577288978, by rfl⟩ : syracuseStep 2103051971 = 3154577957) B3154577957
theorem B5608138589 : Blo 1997435 5608138589 := bstep (se 3 (by rfl) ⟨1051525985, by rfl⟩ : syracuseStep 5608138589 = 2103051971) B2103051971
theorem B3738759059 : Blo 1997435 3738759059 := bstep (se 1 (by rfl) ⟨2804069294, by rfl⟩ : syracuseStep 3738759059 = 5608138589) B5608138589
theorem B2492506039 : Blo 1997435 2492506039 := bstep (se 1 (by rfl) ⟨1869379529, by rfl⟩ : syracuseStep 2492506039 = 3738759059) B3738759059
theorem B3323341385 : Blo 1997435 3323341385 := bstep (se 2 (by rfl) ⟨1246253019, by rfl⟩ : syracuseStep 3323341385 = 2492506039) B2492506039
theorem B2215560923 : Blo 1997435 2215560923 := bstep (se 1 (by rfl) ⟨1661670692, by rfl⟩ : syracuseStep 2215560923 = 3323341385) B3323341385
theorem B1477040615 : Blo 1997435 1477040615 := bstep (se 1 (by rfl) ⟨1107780461, by rfl⟩ : syracuseStep 1477040615 = 2215560923) B2215560923
theorem B984693743 : Blo 1997435 984693743 := bstep (se 1 (by rfl) ⟨738520307, by rfl⟩ : syracuseStep 984693743 = 1477040615) B1477040615
theorem B656462495 : Blo 1997435 656462495 := bstep (se 1 (by rfl) ⟨492346871, by rfl⟩ : syracuseStep 656462495 = 984693743) B984693743
theorem B437641663 : Blo 1997435 437641663 := bstep (se 1 (by rfl) ⟨328231247, by rfl⟩ : syracuseStep 437641663 = 656462495) B656462495
theorem B583522217 : Blo 1997435 583522217 := bstep (se 2 (by rfl) ⟨218820831, by rfl⟩ : syracuseStep 583522217 = 437641663) B437641663
theorem B389014811 : Blo 1997435 389014811 := bstep (se 1 (by rfl) ⟨291761108, by rfl⟩ : syracuseStep 389014811 = 583522217) B583522217
theorem B259343207 : Blo 1997435 259343207 := bstep (se 1 (by rfl) ⟨194507405, by rfl⟩ : syracuseStep 259343207 = 389014811) B389014811
theorem B172895471 : Blo 1997435 172895471 := bstep (se 1 (by rfl) ⟨129671603, by rfl⟩ : syracuseStep 172895471 = 259343207) B259343207
theorem B115263647 : Blo 1997435 115263647 := bstep (se 1 (by rfl) ⟨86447735, by rfl⟩ : syracuseStep 115263647 = 172895471) B172895471
theorem B76842431 : Blo 1997435 76842431 := bstep (se 1 (by rfl) ⟨57631823, by rfl⟩ : syracuseStep 76842431 = 115263647) B115263647
theorem B51228287 : Blo 1997435 51228287 := bstep (se 1 (by rfl) ⟨38421215, by rfl⟩ : syracuseStep 51228287 = 76842431) B76842431
theorem B34152191 : Blo 1997435 34152191 := bstep (se 1 (by rfl) ⟨25614143, by rfl⟩ : syracuseStep 34152191 = 51228287) B51228287
theorem B22768127 : Blo 1997435 22768127 := bstep (se 1 (by rfl) ⟨17076095, by rfl⟩ : syracuseStep 22768127 = 34152191) B34152191
theorem B15178751 : Blo 1997435 15178751 := bstep (se 1 (by rfl) ⟨11384063, by rfl⟩ : syracuseStep 15178751 = 22768127) B22768127
theorem B10119167 : Blo 1997435 10119167 := bstep (se 1 (by rfl) ⟨7589375, by rfl⟩ : syracuseStep 10119167 = 15178751) B15178751
theorem B6746111 : Blo 1997435 6746111 := bstep (se 1 (by rfl) ⟨5059583, by rfl⟩ : syracuseStep 6746111 = 10119167) B10119167
theorem B4497407 : Blo 1997435 4497407 := bstep (se 1 (by rfl) ⟨3373055, by rfl⟩ : syracuseStep 4497407 = 6746111) B6746111
theorem B2998271 : Blo 1997435 2998271 := bstep (se 1 (by rfl) ⟨2248703, by rfl⟩ : syracuseStep 2998271 = 4497407) B4497407
theorem B1998847 : Blo 1997435 1998847 := bstep (se 1 (by rfl) ⟨1499135, by rfl⟩ : syracuseStep 1998847 = 2998271) B2998271
theorem B2998277 : Blo 1997435 2998277 := bbase (se 4 (by rfl) ⟨281088, by rfl⟩ : syracuseStep 2998277 = 562177) (by norm_num)
theorem B1998851 : Blo 1997435 1998851 := bstep (se 1 (by rfl) ⟨1499138, by rfl⟩ : syracuseStep 1998851 = 2998277) B2998277
theorem B3373069 : Blo 1997435 3373069 := bbase (se 3 (by rfl) ⟨632450, by rfl⟩ : syracuseStep 3373069 = 1264901) (by norm_num)
theorem B4497425 : Blo 1997435 4497425 := bstep (se 2 (by rfl) ⟨1686534, by rfl⟩ : syracuseStep 4497425 = 3373069) B3373069
theorem B2998283 : Blo 1997435 2998283 := bstep (se 1 (by rfl) ⟨2248712, by rfl⟩ : syracuseStep 2998283 = 4497425) B4497425
theorem B1998855 : Blo 1997435 1998855 := bstep (se 1 (by rfl) ⟨1499141, by rfl⟩ : syracuseStep 1998855 = 2998283) B2998283
theorem B2248717 : Blo 1997435 2248717 := bbase (se 3 (by rfl) ⟨421634, by rfl⟩ : syracuseStep 2248717 = 843269) (by norm_num)
theorem B2998289 : Blo 1997435 2998289 := bstep (se 2 (by rfl) ⟨1124358, by rfl⟩ : syracuseStep 2998289 = 2248717) B2248717
theorem B1998859 : Blo 1997435 1998859 := bstep (se 1 (by rfl) ⟨1499144, by rfl⟩ : syracuseStep 1998859 = 2998289) B2998289
theorem B6746165 : Blo 1997435 6746165 := bbase (se 5 (by rfl) ⟨316226, by rfl⟩ : syracuseStep 6746165 = 632453) (by norm_num)
theorem B4497443 : Blo 1997435 4497443 := bstep (se 1 (by rfl) ⟨3373082, by rfl⟩ : syracuseStep 4497443 = 6746165) B6746165
theorem B2998295 : Blo 1997435 2998295 := bstep (se 1 (by rfl) ⟨2248721, by rfl⟩ : syracuseStep 2998295 = 4497443) B4497443
theorem B1998863 : Blo 1997435 1998863 := bstep (se 1 (by rfl) ⟨1499147, by rfl⟩ : syracuseStep 1998863 = 2998295) B2998295
theorem B2998301 : Blo 1997435 2998301 := bbase (se 3 (by rfl) ⟨562181, by rfl⟩ : syracuseStep 2998301 = 1124363) (by norm_num)
theorem B1998867 : Blo 1997435 1998867 := bstep (se 1 (by rfl) ⟨1499150, by rfl⟩ : syracuseStep 1998867 = 2998301) B2998301
theorem B4497461 : Blo 1997435 4497461 := bbase (se 5 (by rfl) ⟨210818, by rfl⟩ : syracuseStep 4497461 = 421637) (by norm_num)
theorem B2998307 : Blo 1997435 2998307 := bstep (se 1 (by rfl) ⟨2248730, by rfl⟩ : syracuseStep 2998307 = 4497461) B4497461
theorem B1998871 : Blo 1997435 1998871 := bstep (se 1 (by rfl) ⟨1499153, by rfl⟩ : syracuseStep 1998871 = 2998307) B2998307
theorem B5403061 : Blo 1997435 5403061 := bbase (se 5 (by rfl) ⟨253268, by rfl⟩ : syracuseStep 5403061 = 506537) (by norm_num)
theorem B7204081 : Blo 1997435 7204081 := bstep (se 2 (by rfl) ⟨2701530, by rfl⟩ : syracuseStep 7204081 = 5403061) B5403061
theorem B9605441 : Blo 1997435 9605441 := bstep (se 2 (by rfl) ⟨3602040, by rfl⟩ : syracuseStep 9605441 = 7204081) B7204081
theorem B6403627 : Blo 1997435 6403627 := bstep (se 1 (by rfl) ⟨4802720, by rfl⟩ : syracuseStep 6403627 = 9605441) B9605441
theorem B8538169 : Blo 1997435 8538169 := bstep (se 2 (by rfl) ⟨3201813, by rfl⟩ : syracuseStep 8538169 = 6403627) B6403627
theorem B11384225 : Blo 1997435 11384225 := bstep (se 2 (by rfl) ⟨4269084, by rfl⟩ : syracuseStep 11384225 = 8538169) B8538169
theorem B7589483 : Blo 1997435 7589483 := bstep (se 1 (by rfl) ⟨5692112, by rfl⟩ : syracuseStep 7589483 = 11384225) B11384225
theorem B5059655 : Blo 1997435 5059655 := bstep (se 1 (by rfl) ⟨3794741, by rfl⟩ : syracuseStep 5059655 = 7589483) B7589483
theorem B3373103 : Blo 1997435 3373103 := bstep (se 1 (by rfl) ⟨2529827, by rfl⟩ : syracuseStep 3373103 = 5059655) B5059655
theorem B2248735 : Blo 1997435 2248735 := bstep (se 1 (by rfl) ⟨1686551, by rfl⟩ : syracuseStep 2248735 = 3373103) B3373103
theorem B2998313 : Blo 1997435 2998313 := bstep (se 2 (by rfl) ⟨1124367, by rfl⟩ : syracuseStep 2998313 = 2248735) B2248735
theorem B1998875 : Blo 1997435 1998875 := bstep (se 1 (by rfl) ⟨1499156, by rfl⟩ : syracuseStep 1998875 = 2998313) B2998313
theorem B3751501 : Blo 1997435 3751501 := bbase (se 3 (by rfl) ⟨703406, by rfl⟩ : syracuseStep 3751501 = 1406813) (by norm_num)
theorem B5002001 : Blo 1997435 5002001 := bstep (se 2 (by rfl) ⟨1875750, by rfl⟩ : syracuseStep 5002001 = 3751501) B3751501
theorem B3334667 : Blo 1997435 3334667 := bstep (se 1 (by rfl) ⟨2501000, by rfl⟩ : syracuseStep 3334667 = 5002001) B5002001
theorem B8892445 : Blo 1997435 8892445 := bstep (se 3 (by rfl) ⟨1667333, by rfl⟩ : syracuseStep 8892445 = 3334667) B3334667
theorem B11856593 : Blo 1997435 11856593 := bstep (se 2 (by rfl) ⟨4446222, by rfl⟩ : syracuseStep 11856593 = 8892445) B8892445
theorem B31617581 : Blo 1997435 31617581 := bstep (se 3 (by rfl) ⟨5928296, by rfl⟩ : syracuseStep 31617581 = 11856593) B11856593
theorem B84313549 : Blo 1997435 84313549 := bstep (se 3 (by rfl) ⟨15808790, by rfl⟩ : syracuseStep 84313549 = 31617581) B31617581
theorem B112418065 : Blo 1997435 112418065 := bstep (se 2 (by rfl) ⟨42156774, by rfl⟩ : syracuseStep 112418065 = 84313549) B84313549
theorem B149890753 : Blo 1997435 149890753 := bstep (se 2 (by rfl) ⟨56209032, by rfl⟩ : syracuseStep 149890753 = 112418065) B112418065
theorem B199854337 : Blo 1997435 199854337 := bstep (se 2 (by rfl) ⟨74945376, by rfl⟩ : syracuseStep 199854337 = 149890753) B149890753
theorem B266472449 : Blo 1997435 266472449 := bstep (se 2 (by rfl) ⟨99927168, by rfl⟩ : syracuseStep 266472449 = 199854337) B199854337
theorem B177648299 : Blo 1997435 177648299 := bstep (se 1 (by rfl) ⟨133236224, by rfl⟩ : syracuseStep 177648299 = 266472449) B266472449
theorem B118432199 : Blo 1997435 118432199 := bstep (se 1 (by rfl) ⟨88824149, by rfl⟩ : syracuseStep 118432199 = 177648299) B177648299
theorem B78954799 : Blo 1997435 78954799 := bstep (se 1 (by rfl) ⟨59216099, by rfl⟩ : syracuseStep 78954799 = 118432199) B118432199
theorem B105273065 : Blo 1997435 105273065 := bstep (se 2 (by rfl) ⟨39477399, by rfl⟩ : syracuseStep 105273065 = 78954799) B78954799
theorem B280728173 : Blo 1997435 280728173 := bstep (se 3 (by rfl) ⟨52636532, by rfl⟩ : syracuseStep 280728173 = 105273065) B105273065
theorem B187152115 : Blo 1997435 187152115 := bstep (se 1 (by rfl) ⟨140364086, by rfl⟩ : syracuseStep 187152115 = 280728173) B280728173
theorem B249536153 : Blo 1997435 249536153 := bstep (se 2 (by rfl) ⟨93576057, by rfl⟩ : syracuseStep 249536153 = 187152115) B187152115
theorem B166357435 : Blo 1997435 166357435 := bstep (se 1 (by rfl) ⟨124768076, by rfl⟩ : syracuseStep 166357435 = 249536153) B249536153
theorem B221809913 : Blo 1997435 221809913 := bstep (se 2 (by rfl) ⟨83178717, by rfl⟩ : syracuseStep 221809913 = 166357435) B166357435
theorem B147873275 : Blo 1997435 147873275 := bstep (se 1 (by rfl) ⟨110904956, by rfl⟩ : syracuseStep 147873275 = 221809913) B221809913
theorem B98582183 : Blo 1997435 98582183 := bstep (se 1 (by rfl) ⟨73936637, by rfl⟩ : syracuseStep 98582183 = 147873275) B147873275
theorem B65721455 : Blo 1997435 65721455 := bstep (se 1 (by rfl) ⟨49291091, by rfl⟩ : syracuseStep 65721455 = 98582183) B98582183
theorem B43814303 : Blo 1997435 43814303 := bstep (se 1 (by rfl) ⟨32860727, by rfl⟩ : syracuseStep 43814303 = 65721455) B65721455
theorem B29209535 : Blo 1997435 29209535 := bstep (se 1 (by rfl) ⟨21907151, by rfl⟩ : syracuseStep 29209535 = 43814303) B43814303
theorem B19473023 : Blo 1997435 19473023 := bstep (se 1 (by rfl) ⟨14604767, by rfl⟩ : syracuseStep 19473023 = 29209535) B29209535
theorem B12982015 : Blo 1997435 12982015 := bstep (se 1 (by rfl) ⟨9736511, by rfl⟩ : syracuseStep 12982015 = 19473023) B19473023
theorem B69237413 : Blo 1997435 69237413 := bstep (se 4 (by rfl) ⟨6491007, by rfl⟩ : syracuseStep 69237413 = 12982015) B12982015
theorem B46158275 : Blo 1997435 46158275 := bstep (se 1 (by rfl) ⟨34618706, by rfl⟩ : syracuseStep 46158275 = 69237413) B69237413
theorem B30772183 : Blo 1997435 30772183 := bstep (se 1 (by rfl) ⟨23079137, by rfl⟩ : syracuseStep 30772183 = 46158275) B46158275
theorem B41029577 : Blo 1997435 41029577 := bstep (se 2 (by rfl) ⟨15386091, by rfl⟩ : syracuseStep 41029577 = 30772183) B30772183
theorem B27353051 : Blo 1997435 27353051 := bstep (se 1 (by rfl) ⟨20514788, by rfl⟩ : syracuseStep 27353051 = 41029577) B41029577
theorem B18235367 : Blo 1997435 18235367 := bstep (se 1 (by rfl) ⟨13676525, by rfl⟩ : syracuseStep 18235367 = 27353051) B27353051
theorem B12156911 : Blo 1997435 12156911 := bstep (se 1 (by rfl) ⟨9117683, by rfl⟩ : syracuseStep 12156911 = 18235367) B18235367
theorem B8104607 : Blo 1997435 8104607 := bstep (se 1 (by rfl) ⟨6078455, by rfl⟩ : syracuseStep 8104607 = 12156911) B12156911
theorem B5403071 : Blo 1997435 5403071 := bstep (se 1 (by rfl) ⟨4052303, by rfl⟩ : syracuseStep 5403071 = 8104607) B8104607
theorem B14408189 : Blo 1997435 14408189 := bstep (se 3 (by rfl) ⟨2701535, by rfl⟩ : syracuseStep 14408189 = 5403071) B5403071
theorem B9605459 : Blo 1997435 9605459 := bstep (se 1 (by rfl) ⟨7204094, by rfl⟩ : syracuseStep 9605459 = 14408189) B14408189
theorem B6403639 : Blo 1997435 6403639 := bstep (se 1 (by rfl) ⟨4802729, by rfl⟩ : syracuseStep 6403639 = 9605459) B9605459
theorem B8538185 : Blo 1997435 8538185 := bstep (se 2 (by rfl) ⟨3201819, by rfl⟩ : syracuseStep 8538185 = 6403639) B6403639
theorem B5692123 : Blo 1997435 5692123 := bstep (se 1 (by rfl) ⟨4269092, by rfl⟩ : syracuseStep 5692123 = 8538185) B8538185
theorem B7589497 : Blo 1997435 7589497 := bstep (se 2 (by rfl) ⟨2846061, by rfl⟩ : syracuseStep 7589497 = 5692123) B5692123
theorem B10119329 : Blo 1997435 10119329 := bstep (se 2 (by rfl) ⟨3794748, by rfl⟩ : syracuseStep 10119329 = 7589497) B7589497
theorem B6746219 : Blo 1997435 6746219 := bstep (se 1 (by rfl) ⟨5059664, by rfl⟩ : syracuseStep 6746219 = 10119329) B10119329
theorem B4497479 : Blo 1997435 4497479 := bstep (se 1 (by rfl) ⟨3373109, by rfl⟩ : syracuseStep 4497479 = 6746219) B6746219
theorem B2998319 : Blo 1997435 2998319 := bstep (se 1 (by rfl) ⟨2248739, by rfl⟩ : syracuseStep 2998319 = 4497479) B4497479
theorem B1998879 : Blo 1997435 1998879 := bstep (se 1 (by rfl) ⟨1499159, by rfl⟩ : syracuseStep 1998879 = 2998319) B2998319
theorem B2998325 : Blo 1997435 2998325 := bbase (se 5 (by rfl) ⟨140546, by rfl⟩ : syracuseStep 2998325 = 281093) (by norm_num)
theorem B1998883 : Blo 1997435 1998883 := bstep (se 1 (by rfl) ⟨1499162, by rfl⟩ : syracuseStep 1998883 = 2998325) B2998325
theorem B5059685 : Blo 1997435 5059685 := bbase (se 4 (by rfl) ⟨474345, by rfl⟩ : syracuseStep 5059685 = 948691) (by norm_num)
theorem B3373123 : Blo 1997435 3373123 := bstep (se 1 (by rfl) ⟨2529842, by rfl⟩ : syracuseStep 3373123 = 5059685) B5059685
theorem B4497497 : Blo 1997435 4497497 := bstep (se 2 (by rfl) ⟨1686561, by rfl⟩ : syracuseStep 4497497 = 3373123) B3373123
theorem B2998331 : Blo 1997435 2998331 := bstep (se 1 (by rfl) ⟨2248748, by rfl⟩ : syracuseStep 2998331 = 4497497) B4497497
theorem B1998887 : Blo 1997435 1998887 := bstep (se 1 (by rfl) ⟨1499165, by rfl⟩ : syracuseStep 1998887 = 2998331) B2998331
theorem B2248753 : Blo 1997435 2248753 := bbase (se 2 (by rfl) ⟨843282, by rfl⟩ : syracuseStep 2248753 = 1686565) (by norm_num)
theorem B2998337 : Blo 1997435 2998337 := bstep (se 2 (by rfl) ⟨1124376, by rfl⟩ : syracuseStep 2998337 = 2248753) B2248753
theorem B1998891 : Blo 1997435 1998891 := bstep (se 1 (by rfl) ⟨1499168, by rfl⟩ : syracuseStep 1998891 = 2998337) B2998337
theorem B10397429 : Blo 1997435 10397429 := bbase (se 5 (by rfl) ⟨487379, by rfl⟩ : syracuseStep 10397429 = 974759) (by norm_num)
theorem B6931619 : Blo 1997435 6931619 := bstep (se 1 (by rfl) ⟨5198714, by rfl⟩ : syracuseStep 6931619 = 10397429) B10397429
theorem B4621079 : Blo 1997435 4621079 := bstep (se 1 (by rfl) ⟨3465809, by rfl⟩ : syracuseStep 4621079 = 6931619) B6931619
theorem B3080719 : Blo 1997435 3080719 := bstep (se 1 (by rfl) ⟨2310539, by rfl⟩ : syracuseStep 3080719 = 4621079) B4621079
theorem B16430501 : Blo 1997435 16430501 := bstep (se 4 (by rfl) ⟨1540359, by rfl⟩ : syracuseStep 16430501 = 3080719) B3080719
theorem B10953667 : Blo 1997435 10953667 := bstep (se 1 (by rfl) ⟨8215250, by rfl⟩ : syracuseStep 10953667 = 16430501) B16430501
theorem B14604889 : Blo 1997435 14604889 := bstep (se 2 (by rfl) ⟨5476833, by rfl⟩ : syracuseStep 14604889 = 10953667) B10953667
theorem B19473185 : Blo 1997435 19473185 := bstep (se 2 (by rfl) ⟨7302444, by rfl⟩ : syracuseStep 19473185 = 14604889) B14604889
theorem B12982123 : Blo 1997435 12982123 := bstep (se 1 (by rfl) ⟨9736592, by rfl⟩ : syracuseStep 12982123 = 19473185) B19473185
theorem B17309497 : Blo 1997435 17309497 := bstep (se 2 (by rfl) ⟨6491061, by rfl⟩ : syracuseStep 17309497 = 12982123) B12982123
theorem B23079329 : Blo 1997435 23079329 := bstep (se 2 (by rfl) ⟨8654748, by rfl⟩ : syracuseStep 23079329 = 17309497) B17309497
theorem B15386219 : Blo 1997435 15386219 := bstep (se 1 (by rfl) ⟨11539664, by rfl⟩ : syracuseStep 15386219 = 23079329) B23079329
theorem B10257479 : Blo 1997435 10257479 := bstep (se 1 (by rfl) ⟨7693109, by rfl⟩ : syracuseStep 10257479 = 15386219) B15386219
theorem B6838319 : Blo 1997435 6838319 := bstep (se 1 (by rfl) ⟨5128739, by rfl⟩ : syracuseStep 6838319 = 10257479) B10257479
theorem B4558879 : Blo 1997435 4558879 := bstep (se 1 (by rfl) ⟨3419159, by rfl⟩ : syracuseStep 4558879 = 6838319) B6838319
theorem B6078505 : Blo 1997435 6078505 := bstep (se 2 (by rfl) ⟨2279439, by rfl⟩ : syracuseStep 6078505 = 4558879) B4558879
theorem B8104673 : Blo 1997435 8104673 := bstep (se 2 (by rfl) ⟨3039252, by rfl⟩ : syracuseStep 8104673 = 6078505) B6078505
theorem B5403115 : Blo 1997435 5403115 := bstep (se 1 (by rfl) ⟨4052336, by rfl⟩ : syracuseStep 5403115 = 8104673) B8104673
theorem B7204153 : Blo 1997435 7204153 := bstep (se 2 (by rfl) ⟨2701557, by rfl⟩ : syracuseStep 7204153 = 5403115) B5403115
theorem B9605537 : Blo 1997435 9605537 := bstep (se 2 (by rfl) ⟨3602076, by rfl⟩ : syracuseStep 9605537 = 7204153) B7204153
theorem B6403691 : Blo 1997435 6403691 := bstep (se 1 (by rfl) ⟨4802768, by rfl⟩ : syracuseStep 6403691 = 9605537) B9605537
theorem B4269127 : Blo 1997435 4269127 := bstep (se 1 (by rfl) ⟨3201845, by rfl⟩ : syracuseStep 4269127 = 6403691) B6403691
theorem B5692169 : Blo 1997435 5692169 := bstep (se 2 (by rfl) ⟨2134563, by rfl⟩ : syracuseStep 5692169 = 4269127) B4269127
theorem B3794779 : Blo 1997435 3794779 := bstep (se 1 (by rfl) ⟨2846084, by rfl⟩ : syracuseStep 3794779 = 5692169) B5692169
theorem B5059705 : Blo 1997435 5059705 := bstep (se 2 (by rfl) ⟨1897389, by rfl⟩ : syracuseStep 5059705 = 3794779) B3794779
theorem B6746273 : Blo 1997435 6746273 := bstep (se 2 (by rfl) ⟨2529852, by rfl⟩ : syracuseStep 6746273 = 5059705) B5059705
theorem B4497515 : Blo 1997435 4497515 := bstep (se 1 (by rfl) ⟨3373136, by rfl⟩ : syracuseStep 4497515 = 6746273) B6746273
theorem B2998343 : Blo 1997435 2998343 := bstep (se 1 (by rfl) ⟨2248757, by rfl⟩ : syracuseStep 2998343 = 4497515) B4497515
theorem B1998895 : Blo 1997435 1998895 := bstep (se 1 (by rfl) ⟨1499171, by rfl⟩ : syracuseStep 1998895 = 2998343) B2998343
theorem B2998349 : Blo 1997435 2998349 := bbase (se 3 (by rfl) ⟨562190, by rfl⟩ : syracuseStep 2998349 = 1124381) (by norm_num)
theorem B1998899 : Blo 1997435 1998899 := bstep (se 1 (by rfl) ⟨1499174, by rfl⟩ : syracuseStep 1998899 = 2998349) B2998349
theorem B4497533 : Blo 1997435 4497533 := bbase (se 3 (by rfl) ⟨843287, by rfl⟩ : syracuseStep 4497533 = 1686575) (by norm_num)
theorem B2998355 : Blo 1997435 2998355 := bstep (se 1 (by rfl) ⟨2248766, by rfl⟩ : syracuseStep 2998355 = 4497533) B4497533
theorem B1998903 : Blo 1997435 1998903 := bstep (se 1 (by rfl) ⟨1499177, by rfl⟩ : syracuseStep 1998903 = 2998355) B2998355
theorem B3373157 : Blo 1997435 3373157 := bbase (se 4 (by rfl) ⟨316233, by rfl⟩ : syracuseStep 3373157 = 632467) (by norm_num)
theorem B2248771 : Blo 1997435 2248771 := bstep (se 1 (by rfl) ⟨1686578, by rfl⟩ : syracuseStep 2248771 = 3373157) B3373157
theorem B2998361 : Blo 1997435 2998361 := bstep (se 2 (by rfl) ⟨1124385, by rfl⟩ : syracuseStep 2998361 = 2248771) B2248771
theorem B1998907 : Blo 1997435 1998907 := bstep (se 1 (by rfl) ⟨1499180, by rfl⟩ : syracuseStep 1998907 = 2998361) B2998361
theorem B3039277 : Blo 1997435 3039277 := bbase (se 3 (by rfl) ⟨569864, by rfl⟩ : syracuseStep 3039277 = 1139729) (by norm_num)
theorem B4052369 : Blo 1997435 4052369 := bstep (se 2 (by rfl) ⟨1519638, by rfl⟩ : syracuseStep 4052369 = 3039277) B3039277
theorem B10806317 : Blo 1997435 10806317 := bstep (se 3 (by rfl) ⟨2026184, by rfl⟩ : syracuseStep 10806317 = 4052369) B4052369
theorem B7204211 : Blo 1997435 7204211 := bstep (se 1 (by rfl) ⟨5403158, by rfl⟩ : syracuseStep 7204211 = 10806317) B10806317
theorem B4802807 : Blo 1997435 4802807 := bstep (se 1 (by rfl) ⟨3602105, by rfl⟩ : syracuseStep 4802807 = 7204211) B7204211
theorem B3201871 : Blo 1997435 3201871 := bstep (se 1 (by rfl) ⟨2401403, by rfl⟩ : syracuseStep 3201871 = 4802807) B4802807
theorem B4269161 : Blo 1997435 4269161 := bstep (se 2 (by rfl) ⟨1600935, by rfl⟩ : syracuseStep 4269161 = 3201871) B3201871
theorem B2846107 : Blo 1997435 2846107 := bstep (se 1 (by rfl) ⟨2134580, by rfl⟩ : syracuseStep 2846107 = 4269161) B4269161
theorem B15179237 : Blo 1997435 15179237 := bstep (se 4 (by rfl) ⟨1423053, by rfl⟩ : syracuseStep 15179237 = 2846107) B2846107
theorem B10119491 : Blo 1997435 10119491 := bstep (se 1 (by rfl) ⟨7589618, by rfl⟩ : syracuseStep 10119491 = 15179237) B15179237
theorem B6746327 : Blo 1997435 6746327 := bstep (se 1 (by rfl) ⟨5059745, by rfl⟩ : syracuseStep 6746327 = 10119491) B10119491
theorem B4497551 : Blo 1997435 4497551 := bstep (se 1 (by rfl) ⟨3373163, by rfl⟩ : syracuseStep 4497551 = 6746327) B6746327
theorem B2998367 : Blo 1997435 2998367 := bstep (se 1 (by rfl) ⟨2248775, by rfl⟩ : syracuseStep 2998367 = 4497551) B4497551
theorem B1998911 : Blo 1997435 1998911 := bstep (se 1 (by rfl) ⟨1499183, by rfl⟩ : syracuseStep 1998911 = 2998367) B2998367
theorem B2998373 : Blo 1997435 2998373 := bbase (se 4 (by rfl) ⟨281097, by rfl⟩ : syracuseStep 2998373 = 562195) (by norm_num)
theorem B1998915 : Blo 1997435 1998915 := bstep (se 1 (by rfl) ⟨1499186, by rfl⟩ : syracuseStep 1998915 = 2998373) B2998373
theorem B2026193 : Blo 1997435 2026193 := bbase (se 2 (by rfl) ⟨759822, by rfl⟩ : syracuseStep 2026193 = 1519645) (by norm_num)
theorem B5403181 : Blo 1997435 5403181 := bstep (se 3 (by rfl) ⟨1013096, by rfl⟩ : syracuseStep 5403181 = 2026193) B2026193
theorem B7204241 : Blo 1997435 7204241 := bstep (se 2 (by rfl) ⟨2701590, by rfl⟩ : syracuseStep 7204241 = 5403181) B5403181
theorem B4802827 : Blo 1997435 4802827 := bstep (se 1 (by rfl) ⟨3602120, by rfl⟩ : syracuseStep 4802827 = 7204241) B7204241
theorem B6403769 : Blo 1997435 6403769 := bstep (se 2 (by rfl) ⟨2401413, by rfl⟩ : syracuseStep 6403769 = 4802827) B4802827
theorem B4269179 : Blo 1997435 4269179 := bstep (se 1 (by rfl) ⟨3201884, by rfl⟩ : syracuseStep 4269179 = 6403769) B6403769
theorem B2846119 : Blo 1997435 2846119 := bstep (se 1 (by rfl) ⟨2134589, by rfl⟩ : syracuseStep 2846119 = 4269179) B4269179
theorem B3794825 : Blo 1997435 3794825 := bstep (se 2 (by rfl) ⟨1423059, by rfl⟩ : syracuseStep 3794825 = 2846119) B2846119
theorem B2529883 : Blo 1997435 2529883 := bstep (se 1 (by rfl) ⟨1897412, by rfl⟩ : syracuseStep 2529883 = 3794825) B3794825
theorem B3373177 : Blo 1997435 3373177 := bstep (se 2 (by rfl) ⟨1264941, by rfl⟩ : syracuseStep 3373177 = 2529883) B2529883
theorem B4497569 : Blo 1997435 4497569 := bstep (se 2 (by rfl) ⟨1686588, by rfl⟩ : syracuseStep 4497569 = 3373177) B3373177
theorem B2998379 : Blo 1997435 2998379 := bstep (se 1 (by rfl) ⟨2248784, by rfl⟩ : syracuseStep 2998379 = 4497569) B4497569
theorem B1998919 : Blo 1997435 1998919 := bstep (se 1 (by rfl) ⟨1499189, by rfl⟩ : syracuseStep 1998919 = 2998379) B2998379
theorem B2248789 : Blo 1997435 2248789 := bbase (se 8 (by rfl) ⟨13176, by rfl⟩ : syracuseStep 2248789 = 26353) (by norm_num)
theorem B2998385 : Blo 1997435 2998385 := bstep (se 2 (by rfl) ⟨1124394, by rfl⟩ : syracuseStep 2998385 = 2248789) B2248789
theorem B1998923 : Blo 1997435 1998923 := bstep (se 1 (by rfl) ⟨1499192, by rfl⟩ : syracuseStep 1998923 = 2998385) B2998385
theorem B2529893 : Blo 1997435 2529893 := bbase (se 4 (by rfl) ⟨237177, by rfl⟩ : syracuseStep 2529893 = 474355) (by norm_num)
theorem B6746381 : Blo 1997435 6746381 := bstep (se 3 (by rfl) ⟨1264946, by rfl⟩ : syracuseStep 6746381 = 2529893) B2529893
theorem B4497587 : Blo 1997435 4497587 := bstep (se 1 (by rfl) ⟨3373190, by rfl⟩ : syracuseStep 4497587 = 6746381) B6746381
theorem B2998391 : Blo 1997435 2998391 := bstep (se 1 (by rfl) ⟨2248793, by rfl⟩ : syracuseStep 2998391 = 4497587) B4497587
theorem B1998927 : Blo 1997435 1998927 := bstep (se 1 (by rfl) ⟨1499195, by rfl⟩ : syracuseStep 1998927 = 2998391) B2998391
theorem B2998397 : Blo 1997435 2998397 := bbase (se 3 (by rfl) ⟨562199, by rfl⟩ : syracuseStep 2998397 = 1124399) (by norm_num)
theorem B1998931 : Blo 1997435 1998931 := bstep (se 1 (by rfl) ⟨1499198, by rfl⟩ : syracuseStep 1998931 = 2998397) B2998397
theorem B4497605 : Blo 1997435 4497605 := bbase (se 4 (by rfl) ⟨421650, by rfl⟩ : syracuseStep 4497605 = 843301) (by norm_num)
theorem B2998403 : Blo 1997435 2998403 := bstep (se 1 (by rfl) ⟨2248802, by rfl⟩ : syracuseStep 2998403 = 4497605) B4497605
theorem B1998935 : Blo 1997435 1998935 := bstep (se 1 (by rfl) ⟨1499201, by rfl⟩ : syracuseStep 1998935 = 2998403) B2998403
theorem B9605749 : Blo 1997435 9605749 := bbase (se 5 (by rfl) ⟨450269, by rfl⟩ : syracuseStep 9605749 = 900539) (by norm_num)
theorem B12807665 : Blo 1997435 12807665 := bstep (se 2 (by rfl) ⟨4802874, by rfl⟩ : syracuseStep 12807665 = 9605749) B9605749
theorem B8538443 : Blo 1997435 8538443 := bstep (se 1 (by rfl) ⟨6403832, by rfl⟩ : syracuseStep 8538443 = 12807665) B12807665
theorem B5692295 : Blo 1997435 5692295 := bstep (se 1 (by rfl) ⟨4269221, by rfl⟩ : syracuseStep 5692295 = 8538443) B8538443
theorem B3794863 : Blo 1997435 3794863 := bstep (se 1 (by rfl) ⟨2846147, by rfl⟩ : syracuseStep 3794863 = 5692295) B5692295
theorem B5059817 : Blo 1997435 5059817 := bstep (se 2 (by rfl) ⟨1897431, by rfl⟩ : syracuseStep 5059817 = 3794863) B3794863
theorem B3373211 : Blo 1997435 3373211 := bstep (se 1 (by rfl) ⟨2529908, by rfl⟩ : syracuseStep 3373211 = 5059817) B5059817
theorem B2248807 : Blo 1997435 2248807 := bstep (se 1 (by rfl) ⟨1686605, by rfl⟩ : syracuseStep 2248807 = 3373211) B3373211
theorem B2998409 : Blo 1997435 2998409 := bstep (se 2 (by rfl) ⟨1124403, by rfl⟩ : syracuseStep 2998409 = 2248807) B2248807
theorem B1998939 : Blo 1997435 1998939 := bstep (se 1 (by rfl) ⟨1499204, by rfl⟩ : syracuseStep 1998939 = 2998409) B2998409
theorem B10119653 : Blo 1997435 10119653 := bbase (se 4 (by rfl) ⟨948717, by rfl⟩ : syracuseStep 10119653 = 1897435) (by norm_num)
theorem B6746435 : Blo 1997435 6746435 := bstep (se 1 (by rfl) ⟨5059826, by rfl⟩ : syracuseStep 6746435 = 10119653) B10119653
theorem B4497623 : Blo 1997435 4497623 := bstep (se 1 (by rfl) ⟨3373217, by rfl⟩ : syracuseStep 4497623 = 6746435) B6746435
theorem B2998415 : Blo 1997435 2998415 := bstep (se 1 (by rfl) ⟨2248811, by rfl⟩ : syracuseStep 2998415 = 4497623) B4497623
theorem B1998943 : Blo 1997435 1998943 := bstep (se 1 (by rfl) ⟨1499207, by rfl⟩ : syracuseStep 1998943 = 2998415) B2998415
theorem B2998421 : Blo 1997435 2998421 := bbase (se 6 (by rfl) ⟨70275, by rfl⟩ : syracuseStep 2998421 = 140551) (by norm_num)
theorem B1998947 : Blo 1997435 1998947 := bstep (se 1 (by rfl) ⟨1499210, by rfl⟩ : syracuseStep 1998947 = 2998421) B2998421
theorem B2026225 : Blo 1997435 2026225 := bbase (se 2 (by rfl) ⟨759834, by rfl⟩ : syracuseStep 2026225 = 1519669) (by norm_num)
theorem B10806533 : Blo 1997435 10806533 := bstep (se 4 (by rfl) ⟨1013112, by rfl⟩ : syracuseStep 10806533 = 2026225) B2026225
theorem B7204355 : Blo 1997435 7204355 := bstep (se 1 (by rfl) ⟨5403266, by rfl⟩ : syracuseStep 7204355 = 10806533) B10806533
theorem B4802903 : Blo 1997435 4802903 := bstep (se 1 (by rfl) ⟨3602177, by rfl⟩ : syracuseStep 4802903 = 7204355) B7204355
theorem B3201935 : Blo 1997435 3201935 := bstep (se 1 (by rfl) ⟨2401451, by rfl⟩ : syracuseStep 3201935 = 4802903) B4802903
theorem B8538493 : Blo 1997435 8538493 := bstep (se 3 (by rfl) ⟨1600967, by rfl⟩ : syracuseStep 8538493 = 3201935) B3201935
theorem B11384657 : Blo 1997435 11384657 := bstep (se 2 (by rfl) ⟨4269246, by rfl⟩ : syracuseStep 11384657 = 8538493) B8538493
theorem B7589771 : Blo 1997435 7589771 := bstep (se 1 (by rfl) ⟨5692328, by rfl⟩ : syracuseStep 7589771 = 11384657) B11384657
theorem B5059847 : Blo 1997435 5059847 := bstep (se 1 (by rfl) ⟨3794885, by rfl⟩ : syracuseStep 5059847 = 7589771) B7589771
theorem B3373231 : Blo 1997435 3373231 := bstep (se 1 (by rfl) ⟨2529923, by rfl⟩ : syracuseStep 3373231 = 5059847) B5059847
theorem B4497641 : Blo 1997435 4497641 := bstep (se 2 (by rfl) ⟨1686615, by rfl⟩ : syracuseStep 4497641 = 3373231) B3373231
theorem B2998427 : Blo 1997435 2998427 := bstep (se 1 (by rfl) ⟨2248820, by rfl⟩ : syracuseStep 2998427 = 4497641) B4497641
theorem B1998951 : Blo 1997435 1998951 := bstep (se 1 (by rfl) ⟨1499213, by rfl⟩ : syracuseStep 1998951 = 2998427) B2998427
theorem B2248825 : Blo 1997435 2248825 := bbase (se 2 (by rfl) ⟨843309, by rfl⟩ : syracuseStep 2248825 = 1686619) (by norm_num)
theorem B2998433 : Blo 1997435 2998433 := bstep (se 2 (by rfl) ⟨1124412, by rfl⟩ : syracuseStep 2998433 = 2248825) B2248825
theorem B1998955 : Blo 1997435 1998955 := bstep (se 1 (by rfl) ⟨1499216, by rfl⟩ : syracuseStep 1998955 = 2998433) B2998433
theorem B9736901 : Blo 1997435 9736901 := bbase (se 4 (by rfl) ⟨912834, by rfl⟩ : syracuseStep 9736901 = 1825669) (by norm_num)
theorem B6491267 : Blo 1997435 6491267 := bstep (se 1 (by rfl) ⟨4868450, by rfl⟩ : syracuseStep 6491267 = 9736901) B9736901
theorem B4327511 : Blo 1997435 4327511 := bstep (se 1 (by rfl) ⟨3245633, by rfl⟩ : syracuseStep 4327511 = 6491267) B6491267
theorem B46160117 : Blo 1997435 46160117 := bstep (se 5 (by rfl) ⟨2163755, by rfl⟩ : syracuseStep 46160117 = 4327511) B4327511
theorem B30773411 : Blo 1997435 30773411 := bstep (se 1 (by rfl) ⟨23080058, by rfl⟩ : syracuseStep 30773411 = 46160117) B46160117
theorem B20515607 : Blo 1997435 20515607 := bstep (se 1 (by rfl) ⟨15386705, by rfl⟩ : syracuseStep 20515607 = 30773411) B30773411
theorem B13677071 : Blo 1997435 13677071 := bstep (se 1 (by rfl) ⟨10257803, by rfl⟩ : syracuseStep 13677071 = 20515607) B20515607
theorem B36472189 : Blo 1997435 36472189 := bstep (se 3 (by rfl) ⟨6838535, by rfl⟩ : syracuseStep 36472189 = 13677071) B13677071
theorem B48629585 : Blo 1997435 48629585 := bstep (se 2 (by rfl) ⟨18236094, by rfl⟩ : syracuseStep 48629585 = 36472189) B36472189
theorem B32419723 : Blo 1997435 32419723 := bstep (se 1 (by rfl) ⟨24314792, by rfl⟩ : syracuseStep 32419723 = 48629585) B48629585
theorem B43226297 : Blo 1997435 43226297 := bstep (se 2 (by rfl) ⟨16209861, by rfl⟩ : syracuseStep 43226297 = 32419723) B32419723
theorem B28817531 : Blo 1997435 28817531 := bstep (se 1 (by rfl) ⟨21613148, by rfl⟩ : syracuseStep 28817531 = 43226297) B43226297
theorem B19211687 : Blo 1997435 19211687 := bstep (se 1 (by rfl) ⟨14408765, by rfl⟩ : syracuseStep 19211687 = 28817531) B28817531
theorem B12807791 : Blo 1997435 12807791 := bstep (se 1 (by rfl) ⟨9605843, by rfl⟩ : syracuseStep 12807791 = 19211687) B19211687
theorem B8538527 : Blo 1997435 8538527 := bstep (se 1 (by rfl) ⟨6403895, by rfl⟩ : syracuseStep 8538527 = 12807791) B12807791
theorem B5692351 : Blo 1997435 5692351 := bstep (se 1 (by rfl) ⟨4269263, by rfl⟩ : syracuseStep 5692351 = 8538527) B8538527
theorem B7589801 : Blo 1997435 7589801 := bstep (se 2 (by rfl) ⟨2846175, by rfl⟩ : syracuseStep 7589801 = 5692351) B5692351
theorem B5059867 : Blo 1997435 5059867 := bstep (se 1 (by rfl) ⟨3794900, by rfl⟩ : syracuseStep 5059867 = 7589801) B7589801
theorem B6746489 : Blo 1997435 6746489 := bstep (se 2 (by rfl) ⟨2529933, by rfl⟩ : syracuseStep 6746489 = 5059867) B5059867
theorem B4497659 : Blo 1997435 4497659 := bstep (se 1 (by rfl) ⟨3373244, by rfl⟩ : syracuseStep 4497659 = 6746489) B6746489
theorem B2998439 : Blo 1997435 2998439 := bstep (se 1 (by rfl) ⟨2248829, by rfl⟩ : syracuseStep 2998439 = 4497659) B4497659
theorem B1998959 : Blo 1997435 1998959 := bstep (se 1 (by rfl) ⟨1499219, by rfl⟩ : syracuseStep 1998959 = 2998439) B2998439
theorem B2998445 : Blo 1997435 2998445 := bbase (se 3 (by rfl) ⟨562208, by rfl⟩ : syracuseStep 2998445 = 1124417) (by norm_num)
theorem B1998963 : Blo 1997435 1998963 := bstep (se 1 (by rfl) ⟨1499222, by rfl⟩ : syracuseStep 1998963 = 2998445) B2998445
theorem B4497677 : Blo 1997435 4497677 := bbase (se 3 (by rfl) ⟨843314, by rfl⟩ : syracuseStep 4497677 = 1686629) (by norm_num)
theorem B2998451 : Blo 1997435 2998451 := bstep (se 1 (by rfl) ⟨2248838, by rfl⟩ : syracuseStep 2998451 = 4497677) B4497677
theorem B1998967 : Blo 1997435 1998967 := bstep (se 1 (by rfl) ⟨1499225, by rfl⟩ : syracuseStep 1998967 = 2998451) B2998451
theorem B2529949 : Blo 1997435 2529949 := bbase (se 3 (by rfl) ⟨474365, by rfl⟩ : syracuseStep 2529949 = 948731) (by norm_num)
theorem B3373265 : Blo 1997435 3373265 := bstep (se 2 (by rfl) ⟨1264974, by rfl⟩ : syracuseStep 3373265 = 2529949) B2529949
theorem B2248843 : Blo 1997435 2248843 := bstep (se 1 (by rfl) ⟨1686632, by rfl⟩ : syracuseStep 2248843 = 3373265) B3373265
theorem B2998457 : Blo 1997435 2998457 := bstep (se 2 (by rfl) ⟨1124421, by rfl⟩ : syracuseStep 2998457 = 2248843) B2248843
theorem B1998971 : Blo 1997435 1998971 := bstep (se 1 (by rfl) ⟨1499228, by rfl⟩ : syracuseStep 1998971 = 2998457) B2998457
theorem B3201973 : Blo 1997435 3201973 := bbase (se 5 (by rfl) ⟨150092, by rfl⟩ : syracuseStep 3201973 = 300185) (by norm_num)
theorem B17077189 : Blo 1997435 17077189 := bstep (se 4 (by rfl) ⟨1600986, by rfl⟩ : syracuseStep 17077189 = 3201973) B3201973
theorem B22769585 : Blo 1997435 22769585 := bstep (se 2 (by rfl) ⟨8538594, by rfl⟩ : syracuseStep 22769585 = 17077189) B17077189
theorem B15179723 : Blo 1997435 15179723 := bstep (se 1 (by rfl) ⟨11384792, by rfl⟩ : syracuseStep 15179723 = 22769585) B22769585
theorem B10119815 : Blo 1997435 10119815 := bstep (se 1 (by rfl) ⟨7589861, by rfl⟩ : syracuseStep 10119815 = 15179723) B15179723
theorem B6746543 : Blo 1997435 6746543 := bstep (se 1 (by rfl) ⟨5059907, by rfl⟩ : syracuseStep 6746543 = 10119815) B10119815
theorem B4497695 : Blo 1997435 4497695 := bstep (se 1 (by rfl) ⟨3373271, by rfl⟩ : syracuseStep 4497695 = 6746543) B6746543
theorem B2998463 : Blo 1997435 2998463 := bstep (se 1 (by rfl) ⟨2248847, by rfl⟩ : syracuseStep 2998463 = 4497695) B4497695
theorem B1998975 : Blo 1997435 1998975 := bstep (se 1 (by rfl) ⟨1499231, by rfl⟩ : syracuseStep 1998975 = 2998463) B2998463
theorem B2998469 : Blo 1997435 2998469 := bbase (se 4 (by rfl) ⟨281106, by rfl⟩ : syracuseStep 2998469 = 562213) (by norm_num)
theorem B1998979 : Blo 1997435 1998979 := bstep (se 1 (by rfl) ⟨1499234, by rfl⟩ : syracuseStep 1998979 = 2998469) B2998469
theorem B3373285 : Blo 1997435 3373285 := bbase (se 4 (by rfl) ⟨316245, by rfl⟩ : syracuseStep 3373285 = 632491) (by norm_num)
theorem B4497713 : Blo 1997435 4497713 := bstep (se 2 (by rfl) ⟨1686642, by rfl⟩ : syracuseStep 4497713 = 3373285) B3373285
theorem B2998475 : Blo 1997435 2998475 := bstep (se 1 (by rfl) ⟨2248856, by rfl⟩ : syracuseStep 2998475 = 4497713) B4497713
theorem B1998983 : Blo 1997435 1998983 := bstep (se 1 (by rfl) ⟨1499237, by rfl⟩ : syracuseStep 1998983 = 2998475) B2998475
theorem B2248861 : Blo 1997435 2248861 := bbase (se 3 (by rfl) ⟨421661, by rfl⟩ : syracuseStep 2248861 = 843323) (by norm_num)
theorem B2998481 : Blo 1997435 2998481 := bstep (se 2 (by rfl) ⟨1124430, by rfl⟩ : syracuseStep 2998481 = 2248861) B2248861
theorem B1998987 : Blo 1997435 1998987 := bstep (se 1 (by rfl) ⟨1499240, by rfl⟩ : syracuseStep 1998987 = 2998481) B2998481
theorem B6746597 : Blo 1997435 6746597 := bbase (se 4 (by rfl) ⟨632493, by rfl⟩ : syracuseStep 6746597 = 1264987) (by norm_num)
theorem B4497731 : Blo 1997435 4497731 := bstep (se 1 (by rfl) ⟨3373298, by rfl⟩ : syracuseStep 4497731 = 6746597) B6746597
theorem B2998487 : Blo 1997435 2998487 := bstep (se 1 (by rfl) ⟨2248865, by rfl⟩ : syracuseStep 2998487 = 4497731) B4497731
theorem B1998991 : Blo 1997435 1998991 := bstep (se 1 (by rfl) ⟨1499243, by rfl⟩ : syracuseStep 1998991 = 2998487) B2998487
theorem B2998493 : Blo 1997435 2998493 := bbase (se 3 (by rfl) ⟨562217, by rfl⟩ : syracuseStep 2998493 = 1124435) (by norm_num)
theorem B1998995 : Blo 1997435 1998995 := bstep (se 1 (by rfl) ⟨1499246, by rfl⟩ : syracuseStep 1998995 = 2998493) B2998493
theorem B4497749 : Blo 1997435 4497749 := bbase (se 10 (by rfl) ⟨6588, by rfl⟩ : syracuseStep 4497749 = 13177) (by norm_num)
theorem B2998499 : Blo 1997435 2998499 := bstep (se 1 (by rfl) ⟨2248874, by rfl⟩ : syracuseStep 2998499 = 4497749) B4497749
theorem B1998999 : Blo 1997435 1998999 := bstep (se 1 (by rfl) ⟨1499249, by rfl⟩ : syracuseStep 1998999 = 2998499) B2998499
theorem B4803029 : Blo 1997435 4803029 := bbase (se 7 (by rfl) ⟨56285, by rfl⟩ : syracuseStep 4803029 = 112571) (by norm_num)
theorem B3202019 : Blo 1997435 3202019 := bstep (se 1 (by rfl) ⟨2401514, by rfl⟩ : syracuseStep 3202019 = 4803029) B4803029
theorem B2134679 : Blo 1997435 2134679 := bstep (se 1 (by rfl) ⟨1601009, by rfl⟩ : syracuseStep 2134679 = 3202019) B3202019
theorem B5692477 : Blo 1997435 5692477 := bstep (se 3 (by rfl) ⟨1067339, by rfl⟩ : syracuseStep 5692477 = 2134679) B2134679
theorem B7589969 : Blo 1997435 7589969 := bstep (se 2 (by rfl) ⟨2846238, by rfl⟩ : syracuseStep 7589969 = 5692477) B5692477
theorem B5059979 : Blo 1997435 5059979 := bstep (se 1 (by rfl) ⟨3794984, by rfl⟩ : syracuseStep 5059979 = 7589969) B7589969
theorem B3373319 : Blo 1997435 3373319 := bstep (se 1 (by rfl) ⟨2529989, by rfl⟩ : syracuseStep 3373319 = 5059979) B5059979
theorem B2248879 : Blo 1997435 2248879 := bstep (se 1 (by rfl) ⟨1686659, by rfl⟩ : syracuseStep 2248879 = 3373319) B3373319
theorem B2998505 : Blo 1997435 2998505 := bstep (se 2 (by rfl) ⟨1124439, by rfl⟩ : syracuseStep 2998505 = 2248879) B2248879
theorem B1999003 : Blo 1997435 1999003 := bstep (se 1 (by rfl) ⟨1499252, by rfl⟩ : syracuseStep 1999003 = 2998505) B2998505
theorem B8105125 : Blo 1997435 8105125 := bbase (se 4 (by rfl) ⟨759855, by rfl⟩ : syracuseStep 8105125 = 1519711) (by norm_num)
theorem B10806833 : Blo 1997435 10806833 := bstep (se 2 (by rfl) ⟨4052562, by rfl⟩ : syracuseStep 10806833 = 8105125) B8105125
theorem B7204555 : Blo 1997435 7204555 := bstep (se 1 (by rfl) ⟨5403416, by rfl⟩ : syracuseStep 7204555 = 10806833) B10806833
theorem B38424293 : Blo 1997435 38424293 := bstep (se 4 (by rfl) ⟨3602277, by rfl⟩ : syracuseStep 38424293 = 7204555) B7204555
theorem B25616195 : Blo 1997435 25616195 := bstep (se 1 (by rfl) ⟨19212146, by rfl⟩ : syracuseStep 25616195 = 38424293) B38424293
theorem B17077463 : Blo 1997435 17077463 := bstep (se 1 (by rfl) ⟨12808097, by rfl⟩ : syracuseStep 17077463 = 25616195) B25616195
theorem B11384975 : Blo 1997435 11384975 := bstep (se 1 (by rfl) ⟨8538731, by rfl⟩ : syracuseStep 11384975 = 17077463) B17077463
theorem B7589983 : Blo 1997435 7589983 := bstep (se 1 (by rfl) ⟨5692487, by rfl⟩ : syracuseStep 7589983 = 11384975) B11384975
theorem B10119977 : Blo 1997435 10119977 := bstep (se 2 (by rfl) ⟨3794991, by rfl⟩ : syracuseStep 10119977 = 7589983) B7589983
theorem B6746651 : Blo 1997435 6746651 := bstep (se 1 (by rfl) ⟨5059988, by rfl⟩ : syracuseStep 6746651 = 10119977) B10119977
theorem B4497767 : Blo 1997435 4497767 := bstep (se 1 (by rfl) ⟨3373325, by rfl⟩ : syracuseStep 4497767 = 6746651) B6746651
theorem B2998511 : Blo 1997435 2998511 := bstep (se 1 (by rfl) ⟨2248883, by rfl⟩ : syracuseStep 2998511 = 4497767) B4497767
theorem B1999007 : Blo 1997435 1999007 := bstep (se 1 (by rfl) ⟨1499255, by rfl⟩ : syracuseStep 1999007 = 2998511) B2998511
theorem B2998517 : Blo 1997435 2998517 := bbase (se 5 (by rfl) ⟨140555, by rfl⟩ : syracuseStep 2998517 = 281111) (by norm_num)
theorem B1999011 : Blo 1997435 1999011 := bstep (se 1 (by rfl) ⟨1499258, by rfl⟩ : syracuseStep 1999011 = 2998517) B2998517
theorem B2163817 : Blo 1997435 2163817 := bbase (se 2 (by rfl) ⟨811431, by rfl⟩ : syracuseStep 2163817 = 1622863) (by norm_num)
theorem B2885089 : Blo 1997435 2885089 := bstep (se 2 (by rfl) ⟨1081908, by rfl⟩ : syracuseStep 2885089 = 2163817) B2163817
theorem B3846785 : Blo 1997435 3846785 := bstep (se 2 (by rfl) ⟨1442544, by rfl⟩ : syracuseStep 3846785 = 2885089) B2885089
theorem B10258093 : Blo 1997435 10258093 := bstep (se 3 (by rfl) ⟨1923392, by rfl⟩ : syracuseStep 10258093 = 3846785) B3846785
theorem B13677457 : Blo 1997435 13677457 := bstep (se 2 (by rfl) ⟨5129046, by rfl⟩ : syracuseStep 13677457 = 10258093) B10258093
theorem B18236609 : Blo 1997435 18236609 := bstep (se 2 (by rfl) ⟨6838728, by rfl⟩ : syracuseStep 18236609 = 13677457) B13677457
theorem B12157739 : Blo 1997435 12157739 := bstep (se 1 (by rfl) ⟨9118304, by rfl⟩ : syracuseStep 12157739 = 18236609) B18236609
theorem B8105159 : Blo 1997435 8105159 := bstep (se 1 (by rfl) ⟨6078869, by rfl⟩ : syracuseStep 8105159 = 12157739) B12157739
theorem B5403439 : Blo 1997435 5403439 := bstep (se 1 (by rfl) ⟨4052579, by rfl⟩ : syracuseStep 5403439 = 8105159) B8105159
theorem B28818341 : Blo 1997435 28818341 := bstep (se 4 (by rfl) ⟨2701719, by rfl⟩ : syracuseStep 28818341 = 5403439) B5403439
theorem B19212227 : Blo 1997435 19212227 := bstep (se 1 (by rfl) ⟨14409170, by rfl⟩ : syracuseStep 19212227 = 28818341) B28818341
theorem B12808151 : Blo 1997435 12808151 := bstep (se 1 (by rfl) ⟨9606113, by rfl⟩ : syracuseStep 12808151 = 19212227) B19212227
theorem B8538767 : Blo 1997435 8538767 := bstep (se 1 (by rfl) ⟨6404075, by rfl⟩ : syracuseStep 8538767 = 12808151) B12808151
theorem B5692511 : Blo 1997435 5692511 := bstep (se 1 (by rfl) ⟨4269383, by rfl⟩ : syracuseStep 5692511 = 8538767) B8538767
theorem B3795007 : Blo 1997435 3795007 := bstep (se 1 (by rfl) ⟨2846255, by rfl⟩ : syracuseStep 3795007 = 5692511) B5692511
theorem B5060009 : Blo 1997435 5060009 := bstep (se 2 (by rfl) ⟨1897503, by rfl⟩ : syracuseStep 5060009 = 3795007) B3795007
theorem B3373339 : Blo 1997435 3373339 := bstep (se 1 (by rfl) ⟨2530004, by rfl⟩ : syracuseStep 3373339 = 5060009) B5060009
theorem B4497785 : Blo 1997435 4497785 := bstep (se 2 (by rfl) ⟨1686669, by rfl⟩ : syracuseStep 4497785 = 3373339) B3373339
theorem B2998523 : Blo 1997435 2998523 := bstep (se 1 (by rfl) ⟨2248892, by rfl⟩ : syracuseStep 2998523 = 4497785) B4497785
theorem B1999015 : Blo 1997435 1999015 := bstep (se 1 (by rfl) ⟨1499261, by rfl⟩ : syracuseStep 1999015 = 2998523) B2998523
theorem B2248897 : Blo 1997435 2248897 := bbase (se 2 (by rfl) ⟨843336, by rfl⟩ : syracuseStep 2248897 = 1686673) (by norm_num)
theorem B2998529 : Blo 1997435 2998529 := bstep (se 2 (by rfl) ⟨1124448, by rfl⟩ : syracuseStep 2998529 = 2248897) B2248897
theorem B1999019 : Blo 1997435 1999019 := bstep (se 1 (by rfl) ⟨1499264, by rfl⟩ : syracuseStep 1999019 = 2998529) B2998529
theorem B5060029 : Blo 1997435 5060029 := bbase (se 3 (by rfl) ⟨948755, by rfl⟩ : syracuseStep 5060029 = 1897511) (by norm_num)
theorem B6746705 : Blo 1997435 6746705 := bstep (se 2 (by rfl) ⟨2530014, by rfl⟩ : syracuseStep 6746705 = 5060029) B5060029
theorem B4497803 : Blo 1997435 4497803 := bstep (se 1 (by rfl) ⟨3373352, by rfl⟩ : syracuseStep 4497803 = 6746705) B6746705
theorem B2998535 : Blo 1997435 2998535 := bstep (se 1 (by rfl) ⟨2248901, by rfl⟩ : syracuseStep 2998535 = 4497803) B4497803
theorem B1999023 : Blo 1997435 1999023 := bstep (se 1 (by rfl) ⟨1499267, by rfl⟩ : syracuseStep 1999023 = 2998535) B2998535
theorem B2998541 : Blo 1997435 2998541 := bbase (se 3 (by rfl) ⟨562226, by rfl⟩ : syracuseStep 2998541 = 1124453) (by norm_num)
theorem B1999027 : Blo 1997435 1999027 := bstep (se 1 (by rfl) ⟨1499270, by rfl⟩ : syracuseStep 1999027 = 2998541) B2998541
theorem B4497821 : Blo 1997435 4497821 := bbase (se 3 (by rfl) ⟨843341, by rfl⟩ : syracuseStep 4497821 = 1686683) (by norm_num)
theorem B2998547 : Blo 1997435 2998547 := bstep (se 1 (by rfl) ⟨2248910, by rfl⟩ : syracuseStep 2998547 = 4497821) B4497821
theorem B1999031 : Blo 1997435 1999031 := bstep (se 1 (by rfl) ⟨1499273, by rfl⟩ : syracuseStep 1999031 = 2998547) B2998547
theorem B3373373 : Blo 1997435 3373373 := bbase (se 3 (by rfl) ⟨632507, by rfl⟩ : syracuseStep 3373373 = 1265015) (by norm_num)
theorem B2248915 : Blo 1997435 2248915 := bstep (se 1 (by rfl) ⟨1686686, by rfl⟩ : syracuseStep 2248915 = 3373373) B3373373
theorem B2998553 : Blo 1997435 2998553 := bstep (se 2 (by rfl) ⟨1124457, by rfl⟩ : syracuseStep 2998553 = 2248915) B2248915
theorem B1999035 : Blo 1997435 1999035 := bstep (se 1 (by rfl) ⟨1499276, by rfl⟩ : syracuseStep 1999035 = 2998553) B2998553
theorem B2134717 : Blo 1997435 2134717 := bbase (se 3 (by rfl) ⟨400259, by rfl⟩ : syracuseStep 2134717 = 800519) (by norm_num)
theorem B11385157 : Blo 1997435 11385157 := bstep (se 4 (by rfl) ⟨1067358, by rfl⟩ : syracuseStep 11385157 = 2134717) B2134717
theorem B15180209 : Blo 1997435 15180209 := bstep (se 2 (by rfl) ⟨5692578, by rfl⟩ : syracuseStep 15180209 = 11385157) B11385157
theorem B10120139 : Blo 1997435 10120139 := bstep (se 1 (by rfl) ⟨7590104, by rfl⟩ : syracuseStep 10120139 = 15180209) B15180209
theorem B6746759 : Blo 1997435 6746759 := bstep (se 1 (by rfl) ⟨5060069, by rfl⟩ : syracuseStep 6746759 = 10120139) B10120139
theorem B4497839 : Blo 1997435 4497839 := bstep (se 1 (by rfl) ⟨3373379, by rfl⟩ : syracuseStep 4497839 = 6746759) B6746759
theorem B2998559 : Blo 1997435 2998559 := bstep (se 1 (by rfl) ⟨2248919, by rfl⟩ : syracuseStep 2998559 = 4497839) B4497839
theorem B1999039 : Blo 1997435 1999039 := bstep (se 1 (by rfl) ⟨1499279, by rfl⟩ : syracuseStep 1999039 = 2998559) B2998559
theorem B2998565 : Blo 1997435 2998565 := bbase (se 4 (by rfl) ⟨281115, by rfl⟩ : syracuseStep 2998565 = 562231) (by norm_num)
theorem B1999043 : Blo 1997435 1999043 := bstep (se 1 (by rfl) ⟨1499282, by rfl⟩ : syracuseStep 1999043 = 2998565) B2998565
theorem B2530045 : Blo 1997435 2530045 := bbase (se 3 (by rfl) ⟨474383, by rfl⟩ : syracuseStep 2530045 = 948767) (by norm_num)
theorem B3373393 : Blo 1997435 3373393 := bstep (se 2 (by rfl) ⟨1265022, by rfl⟩ : syracuseStep 3373393 = 2530045) B2530045
theorem B4497857 : Blo 1997435 4497857 := bstep (se 2 (by rfl) ⟨1686696, by rfl⟩ : syracuseStep 4497857 = 3373393) B3373393
theorem B2998571 : Blo 1997435 2998571 := bstep (se 1 (by rfl) ⟨2248928, by rfl⟩ : syracuseStep 2998571 = 4497857) B4497857
theorem B1999047 : Blo 1997435 1999047 := bstep (se 1 (by rfl) ⟨1499285, by rfl⟩ : syracuseStep 1999047 = 2998571) B2998571
theorem B2248933 : Blo 1997435 2248933 := bbase (se 4 (by rfl) ⟨210837, by rfl⟩ : syracuseStep 2248933 = 421675) (by norm_num)
theorem B2998577 : Blo 1997435 2998577 := bstep (se 2 (by rfl) ⟨1124466, by rfl⟩ : syracuseStep 2998577 = 2248933) B2248933
theorem B1999051 : Blo 1997435 1999051 := bstep (se 1 (by rfl) ⟨1499288, by rfl⟩ : syracuseStep 1999051 = 2998577) B2998577
theorem B4269469 : Blo 1997435 4269469 := bbase (se 3 (by rfl) ⟨800525, by rfl⟩ : syracuseStep 4269469 = 1601051) (by norm_num)
theorem B5692625 : Blo 1997435 5692625 := bstep (se 2 (by rfl) ⟨2134734, by rfl⟩ : syracuseStep 5692625 = 4269469) B4269469
theorem B3795083 : Blo 1997435 3795083 := bstep (se 1 (by rfl) ⟨2846312, by rfl⟩ : syracuseStep 3795083 = 5692625) B5692625
theorem B2530055 : Blo 1997435 2530055 := bstep (se 1 (by rfl) ⟨1897541, by rfl⟩ : syracuseStep 2530055 = 3795083) B3795083
theorem B6746813 : Blo 1997435 6746813 := bstep (se 3 (by rfl) ⟨1265027, by rfl⟩ : syracuseStep 6746813 = 2530055) B2530055
theorem B4497875 : Blo 1997435 4497875 := bstep (se 1 (by rfl) ⟨3373406, by rfl⟩ : syracuseStep 4497875 = 6746813) B6746813
theorem B2998583 : Blo 1997435 2998583 := bstep (se 1 (by rfl) ⟨2248937, by rfl⟩ : syracuseStep 2998583 = 4497875) B4497875
theorem B1999055 : Blo 1997435 1999055 := bstep (se 1 (by rfl) ⟨1499291, by rfl⟩ : syracuseStep 1999055 = 2998583) B2998583
theorem B2998589 : Blo 1997435 2998589 := bbase (se 3 (by rfl) ⟨562235, by rfl⟩ : syracuseStep 2998589 = 1124471) (by norm_num)
theorem B1999059 : Blo 1997435 1999059 := bstep (se 1 (by rfl) ⟨1499294, by rfl⟩ : syracuseStep 1999059 = 2998589) B2998589
theorem B4497893 : Blo 1997435 4497893 := bbase (se 4 (by rfl) ⟨421677, by rfl⟩ : syracuseStep 4497893 = 843355) (by norm_num)
theorem B2998595 : Blo 1997435 2998595 := bstep (se 1 (by rfl) ⟨2248946, by rfl⟩ : syracuseStep 2998595 = 4497893) B4497893
theorem B1999063 : Blo 1997435 1999063 := bstep (se 1 (by rfl) ⟨1499297, by rfl⟩ : syracuseStep 1999063 = 2998595) B2998595
theorem B5060141 : Blo 1997435 5060141 := bbase (se 3 (by rfl) ⟨948776, by rfl⟩ : syracuseStep 5060141 = 1897553) (by norm_num)
theorem B3373427 : Blo 1997435 3373427 := bstep (se 1 (by rfl) ⟨2530070, by rfl⟩ : syracuseStep 3373427 = 5060141) B5060141
theorem B2248951 : Blo 1997435 2248951 := bstep (se 1 (by rfl) ⟨1686713, by rfl⟩ : syracuseStep 2248951 = 3373427) B3373427
theorem B2998601 : Blo 1997435 2998601 := bstep (se 2 (by rfl) ⟨1124475, by rfl⟩ : syracuseStep 2998601 = 2248951) B2248951
theorem B1999067 : Blo 1997435 1999067 := bstep (se 1 (by rfl) ⟨1499300, by rfl⟩ : syracuseStep 1999067 = 2998601) B2998601
theorem B2053993 : Blo 1997435 2053993 := bbase (se 2 (by rfl) ⟨770247, by rfl⟩ : syracuseStep 2053993 = 1540495) (by norm_num)
theorem B2738657 : Blo 1997435 2738657 := bstep (se 2 (by rfl) ⟨1026996, by rfl⟩ : syracuseStep 2738657 = 2053993) B2053993
theorem B7303085 : Blo 1997435 7303085 := bstep (se 3 (by rfl) ⟨1369328, by rfl⟩ : syracuseStep 7303085 = 2738657) B2738657
theorem B77899573 : Blo 1997435 77899573 := bstep (se 5 (by rfl) ⟨3651542, by rfl⟩ : syracuseStep 77899573 = 7303085) B7303085
theorem B415464389 : Blo 1997435 415464389 := bstep (se 4 (by rfl) ⟨38949786, by rfl⟩ : syracuseStep 415464389 = 77899573) B77899573
theorem B276976259 : Blo 1997435 276976259 := bstep (se 1 (by rfl) ⟨207732194, by rfl⟩ : syracuseStep 276976259 = 415464389) B415464389
theorem B184650839 : Blo 1997435 184650839 := bstep (se 1 (by rfl) ⟨138488129, by rfl⟩ : syracuseStep 184650839 = 276976259) B276976259
theorem B123100559 : Blo 1997435 123100559 := bstep (se 1 (by rfl) ⟨92325419, by rfl⟩ : syracuseStep 123100559 = 184650839) B184650839
theorem B82067039 : Blo 1997435 82067039 := bstep (se 1 (by rfl) ⟨61550279, by rfl⟩ : syracuseStep 82067039 = 123100559) B123100559
theorem B54711359 : Blo 1997435 54711359 := bstep (se 1 (by rfl) ⟨41033519, by rfl⟩ : syracuseStep 54711359 = 82067039) B82067039
theorem B36474239 : Blo 1997435 36474239 := bstep (se 1 (by rfl) ⟨27355679, by rfl⟩ : syracuseStep 36474239 = 54711359) B54711359
theorem B24316159 : Blo 1997435 24316159 := bstep (se 1 (by rfl) ⟨18237119, by rfl⟩ : syracuseStep 24316159 = 36474239) B36474239
theorem B32421545 : Blo 1997435 32421545 := bstep (se 2 (by rfl) ⟨12158079, by rfl⟩ : syracuseStep 32421545 = 24316159) B24316159
theorem B21614363 : Blo 1997435 21614363 := bstep (se 1 (by rfl) ⟨16210772, by rfl⟩ : syracuseStep 21614363 = 32421545) B32421545
theorem B14409575 : Blo 1997435 14409575 := bstep (se 1 (by rfl) ⟨10807181, by rfl⟩ : syracuseStep 14409575 = 21614363) B21614363
theorem B9606383 : Blo 1997435 9606383 := bstep (se 1 (by rfl) ⟨7204787, by rfl⟩ : syracuseStep 9606383 = 14409575) B14409575
theorem B6404255 : Blo 1997435 6404255 := bstep (se 1 (by rfl) ⟨4803191, by rfl⟩ : syracuseStep 6404255 = 9606383) B9606383
theorem B4269503 : Blo 1997435 4269503 := bstep (se 1 (by rfl) ⟨3202127, by rfl⟩ : syracuseStep 4269503 = 6404255) B6404255
theorem B2846335 : Blo 1997435 2846335 := bstep (se 1 (by rfl) ⟨2134751, by rfl⟩ : syracuseStep 2846335 = 4269503) B4269503
theorem B3795113 : Blo 1997435 3795113 := bstep (se 2 (by rfl) ⟨1423167, by rfl⟩ : syracuseStep 3795113 = 2846335) B2846335
theorem B10120301 : Blo 1997435 10120301 := bstep (se 3 (by rfl) ⟨1897556, by rfl⟩ : syracuseStep 10120301 = 3795113) B3795113
theorem B6746867 : Blo 1997435 6746867 := bstep (se 1 (by rfl) ⟨5060150, by rfl⟩ : syracuseStep 6746867 = 10120301) B10120301
theorem B4497911 : Blo 1997435 4497911 := bstep (se 1 (by rfl) ⟨3373433, by rfl⟩ : syracuseStep 4497911 = 6746867) B6746867
theorem B2998607 : Blo 1997435 2998607 := bstep (se 1 (by rfl) ⟨2248955, by rfl⟩ : syracuseStep 2998607 = 4497911) B4497911
theorem B1999071 : Blo 1997435 1999071 := bstep (se 1 (by rfl) ⟨1499303, by rfl⟩ : syracuseStep 1999071 = 2998607) B2998607
theorem B2998613 : Blo 1997435 2998613 := bbase (se 10 (by rfl) ⟨4392, by rfl⟩ : syracuseStep 2998613 = 8785) (by norm_num)
theorem B1999075 : Blo 1997435 1999075 := bstep (se 1 (by rfl) ⟨1499306, by rfl⟩ : syracuseStep 1999075 = 2998613) B2998613
theorem B5692693 : Blo 1997435 5692693 := bbase (se 6 (by rfl) ⟨133422, by rfl⟩ : syracuseStep 5692693 = 266845) (by norm_num)
theorem B7590257 : Blo 1997435 7590257 := bstep (se 2 (by rfl) ⟨2846346, by rfl⟩ : syracuseStep 7590257 = 5692693) B5692693
theorem B5060171 : Blo 1997435 5060171 := bstep (se 1 (by rfl) ⟨3795128, by rfl⟩ : syracuseStep 5060171 = 7590257) B7590257
theorem B3373447 : Blo 1997435 3373447 := bstep (se 1 (by rfl) ⟨2530085, by rfl⟩ : syracuseStep 3373447 = 5060171) B5060171
theorem B4497929 : Blo 1997435 4497929 := bstep (se 2 (by rfl) ⟨1686723, by rfl⟩ : syracuseStep 4497929 = 3373447) B3373447
theorem B2998619 : Blo 1997435 2998619 := bstep (se 1 (by rfl) ⟨2248964, by rfl⟩ : syracuseStep 2998619 = 4497929) B4497929
theorem B1999079 : Blo 1997435 1999079 := bstep (se 1 (by rfl) ⟨1499309, by rfl⟩ : syracuseStep 1999079 = 2998619) B2998619
theorem B2248969 : Blo 1997435 2248969 := bbase (se 2 (by rfl) ⟨843363, by rfl⟩ : syracuseStep 2248969 = 1686727) (by norm_num)
theorem B2998625 : Blo 1997435 2998625 := bstep (se 2 (by rfl) ⟨1124484, by rfl⟩ : syracuseStep 2998625 = 2248969) B2248969
theorem B1999083 : Blo 1997435 1999083 := bstep (se 1 (by rfl) ⟨1499312, by rfl⟩ : syracuseStep 1999083 = 2998625) B2998625
theorem B4803229 : Blo 1997435 4803229 := bbase (se 3 (by rfl) ⟨900605, by rfl⟩ : syracuseStep 4803229 = 1801211) (by norm_num)
theorem B25617221 : Blo 1997435 25617221 := bstep (se 4 (by rfl) ⟨2401614, by rfl⟩ : syracuseStep 25617221 = 4803229) B4803229
theorem B17078147 : Blo 1997435 17078147 := bstep (se 1 (by rfl) ⟨12808610, by rfl⟩ : syracuseStep 17078147 = 25617221) B25617221
theorem B11385431 : Blo 1997435 11385431 := bstep (se 1 (by rfl) ⟨8539073, by rfl⟩ : syracuseStep 11385431 = 17078147) B17078147
theorem B7590287 : Blo 1997435 7590287 := bstep (se 1 (by rfl) ⟨5692715, by rfl⟩ : syracuseStep 7590287 = 11385431) B11385431
theorem B5060191 : Blo 1997435 5060191 := bstep (se 1 (by rfl) ⟨3795143, by rfl⟩ : syracuseStep 5060191 = 7590287) B7590287
theorem B6746921 : Blo 1997435 6746921 := bstep (se 2 (by rfl) ⟨2530095, by rfl⟩ : syracuseStep 6746921 = 5060191) B5060191
theorem B4497947 : Blo 1997435 4497947 := bstep (se 1 (by rfl) ⟨3373460, by rfl⟩ : syracuseStep 4497947 = 6746921) B6746921
theorem B2998631 : Blo 1997435 2998631 := bstep (se 1 (by rfl) ⟨2248973, by rfl⟩ : syracuseStep 2998631 = 4497947) B4497947
theorem B1999087 : Blo 1997435 1999087 := bstep (se 1 (by rfl) ⟨1499315, by rfl⟩ : syracuseStep 1999087 = 2998631) B2998631
theorem B2998637 : Blo 1997435 2998637 := bbase (se 3 (by rfl) ⟨562244, by rfl⟩ : syracuseStep 2998637 = 1124489) (by norm_num)
theorem B1999091 : Blo 1997435 1999091 := bstep (se 1 (by rfl) ⟨1499318, by rfl⟩ : syracuseStep 1999091 = 2998637) B2998637
theorem B4497965 : Blo 1997435 4497965 := bbase (se 3 (by rfl) ⟨843368, by rfl⟩ : syracuseStep 4497965 = 1686737) (by norm_num)
theorem B2998643 : Blo 1997435 2998643 := bstep (se 1 (by rfl) ⟨2248982, by rfl⟩ : syracuseStep 2998643 = 4497965) B4497965
theorem B1999095 : Blo 1997435 1999095 := bstep (se 1 (by rfl) ⟨1499321, by rfl⟩ : syracuseStep 1999095 = 2998643) B2998643
theorem B3419509 : Blo 1997435 3419509 := bbase (se 5 (by rfl) ⟨160289, by rfl⟩ : syracuseStep 3419509 = 320579) (by norm_num)
theorem B4559345 : Blo 1997435 4559345 := bstep (se 2 (by rfl) ⟨1709754, by rfl⟩ : syracuseStep 4559345 = 3419509) B3419509
theorem B3039563 : Blo 1997435 3039563 := bstep (se 1 (by rfl) ⟨2279672, by rfl⟩ : syracuseStep 3039563 = 4559345) B4559345
theorem B8105501 : Blo 1997435 8105501 := bstep (se 3 (by rfl) ⟨1519781, by rfl⟩ : syracuseStep 8105501 = 3039563) B3039563
theorem B5403667 : Blo 1997435 5403667 := bstep (se 1 (by rfl) ⟨4052750, by rfl⟩ : syracuseStep 5403667 = 8105501) B8105501
theorem B7204889 : Blo 1997435 7204889 := bstep (se 2 (by rfl) ⟨2701833, by rfl⟩ : syracuseStep 7204889 = 5403667) B5403667
theorem B19213037 : Blo 1997435 19213037 := bstep (se 3 (by rfl) ⟨3602444, by rfl⟩ : syracuseStep 19213037 = 7204889) B7204889
theorem B12808691 : Blo 1997435 12808691 := bstep (se 1 (by rfl) ⟨9606518, by rfl⟩ : syracuseStep 12808691 = 19213037) B19213037
theorem B8539127 : Blo 1997435 8539127 := bstep (se 1 (by rfl) ⟨6404345, by rfl⟩ : syracuseStep 8539127 = 12808691) B12808691
theorem B5692751 : Blo 1997435 5692751 := bstep (se 1 (by rfl) ⟨4269563, by rfl⟩ : syracuseStep 5692751 = 8539127) B8539127
theorem B3795167 : Blo 1997435 3795167 := bstep (se 1 (by rfl) ⟨2846375, by rfl⟩ : syracuseStep 3795167 = 5692751) B5692751
theorem B2530111 : Blo 1997435 2530111 := bstep (se 1 (by rfl) ⟨1897583, by rfl⟩ : syracuseStep 2530111 = 3795167) B3795167
theorem B3373481 : Blo 1997435 3373481 := bstep (se 2 (by rfl) ⟨1265055, by rfl⟩ : syracuseStep 3373481 = 2530111) B2530111
theorem B2248987 : Blo 1997435 2248987 := bstep (se 1 (by rfl) ⟨1686740, by rfl⟩ : syracuseStep 2248987 = 3373481) B3373481
theorem B2998649 : Blo 1997435 2998649 := bstep (se 2 (by rfl) ⟨1124493, by rfl⟩ : syracuseStep 2998649 = 2248987) B2248987
theorem B1999099 : Blo 1997435 1999099 := bstep (se 1 (by rfl) ⟨1499324, by rfl⟩ : syracuseStep 1999099 = 2998649) B2998649
theorem B34156565 : Blo 1997435 34156565 := bbase (se 6 (by rfl) ⟨800544, by rfl⟩ : syracuseStep 34156565 = 1601089) (by norm_num)
theorem B22771043 : Blo 1997435 22771043 := bstep (se 1 (by rfl) ⟨17078282, by rfl⟩ : syracuseStep 22771043 = 34156565) B34156565
theorem B15180695 : Blo 1997435 15180695 := bstep (se 1 (by rfl) ⟨11385521, by rfl⟩ : syracuseStep 15180695 = 22771043) B22771043
theorem B10120463 : Blo 1997435 10120463 := bstep (se 1 (by rfl) ⟨7590347, by rfl⟩ : syracuseStep 10120463 = 15180695) B15180695
theorem B6746975 : Blo 1997435 6746975 := bstep (se 1 (by rfl) ⟨5060231, by rfl⟩ : syracuseStep 6746975 = 10120463) B10120463
theorem B4497983 : Blo 1997435 4497983 := bstep (se 1 (by rfl) ⟨3373487, by rfl⟩ : syracuseStep 4497983 = 6746975) B6746975
theorem B2998655 : Blo 1997435 2998655 := bstep (se 1 (by rfl) ⟨2248991, by rfl⟩ : syracuseStep 2998655 = 4497983) B4497983
theorem B1999103 : Blo 1997435 1999103 := bstep (se 1 (by rfl) ⟨1499327, by rfl⟩ : syracuseStep 1999103 = 2998655) B2998655
theorem B2998661 : Blo 1997435 2998661 := bbase (se 4 (by rfl) ⟨281124, by rfl⟩ : syracuseStep 2998661 = 562249) (by norm_num)
theorem B1999107 : Blo 1997435 1999107 := bstep (se 1 (by rfl) ⟨1499330, by rfl⟩ : syracuseStep 1999107 = 2998661) B2998661
theorem B3373501 : Blo 1997435 3373501 := bbase (se 3 (by rfl) ⟨632531, by rfl⟩ : syracuseStep 3373501 = 1265063) (by norm_num)
theorem B4498001 : Blo 1997435 4498001 := bstep (se 2 (by rfl) ⟨1686750, by rfl⟩ : syracuseStep 4498001 = 3373501) B3373501
theorem B2998667 : Blo 1997435 2998667 := bstep (se 1 (by rfl) ⟨2249000, by rfl⟩ : syracuseStep 2998667 = 4498001) B4498001
theorem B1999111 : Blo 1997435 1999111 := bstep (se 1 (by rfl) ⟨1499333, by rfl⟩ : syracuseStep 1999111 = 2998667) B2998667
theorem B2249005 : Blo 1997435 2249005 := bbase (se 3 (by rfl) ⟨421688, by rfl⟩ : syracuseStep 2249005 = 843377) (by norm_num)
theorem B2998673 : Blo 1997435 2998673 := bstep (se 2 (by rfl) ⟨1124502, by rfl⟩ : syracuseStep 2998673 = 2249005) B2249005
theorem B1999115 : Blo 1997435 1999115 := bstep (se 1 (by rfl) ⟨1499336, by rfl⟩ : syracuseStep 1999115 = 2998673) B2998673
theorem B6747029 : Blo 1997435 6747029 := bbase (se 6 (by rfl) ⟨158133, by rfl⟩ : syracuseStep 6747029 = 316267) (by norm_num)
theorem B4498019 : Blo 1997435 4498019 := bstep (se 1 (by rfl) ⟨3373514, by rfl⟩ : syracuseStep 4498019 = 6747029) B6747029
theorem B2998679 : Blo 1997435 2998679 := bstep (se 1 (by rfl) ⟨2249009, by rfl⟩ : syracuseStep 2998679 = 4498019) B4498019
theorem B1999119 : Blo 1997435 1999119 := bstep (se 1 (by rfl) ⟨1499339, by rfl⟩ : syracuseStep 1999119 = 2998679) B2998679
theorem B2998685 : Blo 1997435 2998685 := bbase (se 3 (by rfl) ⟨562253, by rfl⟩ : syracuseStep 2998685 = 1124507) (by norm_num)
theorem B1999123 : Blo 1997435 1999123 := bstep (se 1 (by rfl) ⟨1499342, by rfl⟩ : syracuseStep 1999123 = 2998685) B2998685
theorem B4498037 : Blo 1997435 4498037 := bbase (se 5 (by rfl) ⟨210845, by rfl⟩ : syracuseStep 4498037 = 421691) (by norm_num)
theorem B2998691 : Blo 1997435 2998691 := bstep (se 1 (by rfl) ⟨2249018, by rfl⟩ : syracuseStep 2998691 = 4498037) B4498037
theorem B1999127 : Blo 1997435 1999127 := bstep (se 1 (by rfl) ⟨1499345, by rfl⟩ : syracuseStep 1999127 = 2998691) B2998691
theorem B7798997 : Blo 1997435 7798997 := bbase (se 7 (by rfl) ⟨91394, by rfl⟩ : syracuseStep 7798997 = 182789) (by norm_num)
theorem B5199331 : Blo 1997435 5199331 := bstep (se 1 (by rfl) ⟨3899498, by rfl⟩ : syracuseStep 5199331 = 7798997) B7798997
theorem B6932441 : Blo 1997435 6932441 := bstep (se 2 (by rfl) ⟨2599665, by rfl⟩ : syracuseStep 6932441 = 5199331) B5199331
theorem B4621627 : Blo 1997435 4621627 := bstep (se 1 (by rfl) ⟨3466220, by rfl⟩ : syracuseStep 4621627 = 6932441) B6932441
theorem B6162169 : Blo 1997435 6162169 := bstep (se 2 (by rfl) ⟨2310813, by rfl⟩ : syracuseStep 6162169 = 4621627) B4621627
theorem B8216225 : Blo 1997435 8216225 := bstep (se 2 (by rfl) ⟨3081084, by rfl⟩ : syracuseStep 8216225 = 6162169) B6162169
theorem B5477483 : Blo 1997435 5477483 := bstep (se 1 (by rfl) ⟨4108112, by rfl⟩ : syracuseStep 5477483 = 8216225) B8216225
theorem B3651655 : Blo 1997435 3651655 := bstep (se 1 (by rfl) ⟨2738741, by rfl⟩ : syracuseStep 3651655 = 5477483) B5477483
theorem B4868873 : Blo 1997435 4868873 := bstep (se 2 (by rfl) ⟨1825827, by rfl⟩ : syracuseStep 4868873 = 3651655) B3651655
theorem B3245915 : Blo 1997435 3245915 := bstep (se 1 (by rfl) ⟨2434436, by rfl⟩ : syracuseStep 3245915 = 4868873) B4868873
theorem B2163943 : Blo 1997435 2163943 := bstep (se 1 (by rfl) ⟨1622957, by rfl⟩ : syracuseStep 2163943 = 3245915) B3245915
theorem B2885257 : Blo 1997435 2885257 := bstep (se 2 (by rfl) ⟨1081971, by rfl⟩ : syracuseStep 2885257 = 2163943) B2163943
theorem B3847009 : Blo 1997435 3847009 := bstep (se 2 (by rfl) ⟨1442628, by rfl⟩ : syracuseStep 3847009 = 2885257) B2885257
theorem B5129345 : Blo 1997435 5129345 := bstep (se 2 (by rfl) ⟨1923504, by rfl⟩ : syracuseStep 5129345 = 3847009) B3847009
theorem B3419563 : Blo 1997435 3419563 := bstep (se 1 (by rfl) ⟨2564672, by rfl⟩ : syracuseStep 3419563 = 5129345) B5129345
theorem B4559417 : Blo 1997435 4559417 := bstep (se 2 (by rfl) ⟨1709781, by rfl⟩ : syracuseStep 4559417 = 3419563) B3419563
theorem B3039611 : Blo 1997435 3039611 := bstep (se 1 (by rfl) ⟨2279708, by rfl⟩ : syracuseStep 3039611 = 4559417) B4559417
theorem B32422517 : Blo 1997435 32422517 := bstep (se 5 (by rfl) ⟨1519805, by rfl⟩ : syracuseStep 32422517 = 3039611) B3039611
theorem B21615011 : Blo 1997435 21615011 := bstep (se 1 (by rfl) ⟨16211258, by rfl⟩ : syracuseStep 21615011 = 32422517) B32422517
theorem B14410007 : Blo 1997435 14410007 := bstep (se 1 (by rfl) ⟨10807505, by rfl⟩ : syracuseStep 14410007 = 21615011) B21615011
theorem B9606671 : Blo 1997435 9606671 := bstep (se 1 (by rfl) ⟨7205003, by rfl⟩ : syracuseStep 9606671 = 14410007) B14410007
theorem B6404447 : Blo 1997435 6404447 := bstep (se 1 (by rfl) ⟨4803335, by rfl⟩ : syracuseStep 6404447 = 9606671) B9606671
theorem B17078525 : Blo 1997435 17078525 := bstep (se 3 (by rfl) ⟨3202223, by rfl⟩ : syracuseStep 17078525 = 6404447) B6404447
theorem B11385683 : Blo 1997435 11385683 := bstep (se 1 (by rfl) ⟨8539262, by rfl⟩ : syracuseStep 11385683 = 17078525) B17078525
theorem B7590455 : Blo 1997435 7590455 := bstep (se 1 (by rfl) ⟨5692841, by rfl⟩ : syracuseStep 7590455 = 11385683) B11385683
theorem B5060303 : Blo 1997435 5060303 := bstep (se 1 (by rfl) ⟨3795227, by rfl⟩ : syracuseStep 5060303 = 7590455) B7590455
theorem B3373535 : Blo 1997435 3373535 := bstep (se 1 (by rfl) ⟨2530151, by rfl⟩ : syracuseStep 3373535 = 5060303) B5060303
theorem B2249023 : Blo 1997435 2249023 := bstep (se 1 (by rfl) ⟨1686767, by rfl⟩ : syracuseStep 2249023 = 3373535) B3373535
theorem B2998697 : Blo 1997435 2998697 := bstep (se 2 (by rfl) ⟨1124511, by rfl⟩ : syracuseStep 2998697 = 2249023) B2249023
theorem B1999131 : Blo 1997435 1999131 := bstep (se 1 (by rfl) ⟨1499348, by rfl⟩ : syracuseStep 1999131 = 2998697) B2998697
theorem B7590469 : Blo 1997435 7590469 := bbase (se 4 (by rfl) ⟨711606, by rfl⟩ : syracuseStep 7590469 = 1423213) (by norm_num)
theorem B10120625 : Blo 1997435 10120625 := bstep (se 2 (by rfl) ⟨3795234, by rfl⟩ : syracuseStep 10120625 = 7590469) B7590469
theorem B6747083 : Blo 1997435 6747083 := bstep (se 1 (by rfl) ⟨5060312, by rfl⟩ : syracuseStep 6747083 = 10120625) B10120625
theorem B4498055 : Blo 1997435 4498055 := bstep (se 1 (by rfl) ⟨3373541, by rfl⟩ : syracuseStep 4498055 = 6747083) B6747083
theorem B2998703 : Blo 1997435 2998703 := bstep (se 1 (by rfl) ⟨2249027, by rfl⟩ : syracuseStep 2998703 = 4498055) B4498055
theorem B1999135 : Blo 1997435 1999135 := bstep (se 1 (by rfl) ⟨1499351, by rfl⟩ : syracuseStep 1999135 = 2998703) B2998703
theorem B2998709 : Blo 1997435 2998709 := bbase (se 5 (by rfl) ⟨140564, by rfl⟩ : syracuseStep 2998709 = 281129) (by norm_num)
theorem B1999139 : Blo 1997435 1999139 := bstep (se 1 (by rfl) ⟨1499354, by rfl⟩ : syracuseStep 1999139 = 2998709) B2998709
theorem B5060333 : Blo 1997435 5060333 := bbase (se 3 (by rfl) ⟨948812, by rfl⟩ : syracuseStep 5060333 = 1897625) (by norm_num)
theorem B3373555 : Blo 1997435 3373555 := bstep (se 1 (by rfl) ⟨2530166, by rfl⟩ : syracuseStep 3373555 = 5060333) B5060333
theorem B4498073 : Blo 1997435 4498073 := bstep (se 2 (by rfl) ⟨1686777, by rfl⟩ : syracuseStep 4498073 = 3373555) B3373555
theorem B2998715 : Blo 1997435 2998715 := bstep (se 1 (by rfl) ⟨2249036, by rfl⟩ : syracuseStep 2998715 = 4498073) B4498073
theorem B1999143 : Blo 1997435 1999143 := bstep (se 1 (by rfl) ⟨1499357, by rfl⟩ : syracuseStep 1999143 = 2998715) B2998715
theorem B2249041 : Blo 1997435 2249041 := bbase (se 2 (by rfl) ⟨843390, by rfl⟩ : syracuseStep 2249041 = 1686781) (by norm_num)
theorem B2998721 : Blo 1997435 2998721 := bstep (se 2 (by rfl) ⟨1124520, by rfl⟩ : syracuseStep 2998721 = 2249041) B2249041
theorem B1999147 : Blo 1997435 1999147 := bstep (se 1 (by rfl) ⟨1499360, by rfl⟩ : syracuseStep 1999147 = 2998721) B2998721
theorem B2134837 : Blo 1997435 2134837 := bbase (se 5 (by rfl) ⟨100070, by rfl⟩ : syracuseStep 2134837 = 200141) (by norm_num)
theorem B2846449 : Blo 1997435 2846449 := bstep (se 2 (by rfl) ⟨1067418, by rfl⟩ : syracuseStep 2846449 = 2134837) B2134837
theorem B3795265 : Blo 1997435 3795265 := bstep (se 2 (by rfl) ⟨1423224, by rfl⟩ : syracuseStep 3795265 = 2846449) B2846449
theorem B5060353 : Blo 1997435 5060353 := bstep (se 2 (by rfl) ⟨1897632, by rfl⟩ : syracuseStep 5060353 = 3795265) B3795265
theorem B6747137 : Blo 1997435 6747137 := bstep (se 2 (by rfl) ⟨2530176, by rfl⟩ : syracuseStep 6747137 = 5060353) B5060353
theorem B4498091 : Blo 1997435 4498091 := bstep (se 1 (by rfl) ⟨3373568, by rfl⟩ : syracuseStep 4498091 = 6747137) B6747137
theorem B2998727 : Blo 1997435 2998727 := bstep (se 1 (by rfl) ⟨2249045, by rfl⟩ : syracuseStep 2998727 = 4498091) B4498091
theorem B1999151 : Blo 1997435 1999151 := bstep (se 1 (by rfl) ⟨1499363, by rfl⟩ : syracuseStep 1999151 = 2998727) B2998727
theorem B2998733 : Blo 1997435 2998733 := bbase (se 3 (by rfl) ⟨562262, by rfl⟩ : syracuseStep 2998733 = 1124525) (by norm_num)
theorem B1999155 : Blo 1997435 1999155 := bstep (se 1 (by rfl) ⟨1499366, by rfl⟩ : syracuseStep 1999155 = 2998733) B2998733
theorem B4498109 : Blo 1997435 4498109 := bbase (se 3 (by rfl) ⟨843395, by rfl⟩ : syracuseStep 4498109 = 1686791) (by norm_num)
theorem B2998739 : Blo 1997435 2998739 := bstep (se 1 (by rfl) ⟨2249054, by rfl⟩ : syracuseStep 2998739 = 4498109) B4498109
theorem B1999159 : Blo 1997435 1999159 := bstep (se 1 (by rfl) ⟨1499369, by rfl⟩ : syracuseStep 1999159 = 2998739) B2998739
theorem B3373589 : Blo 1997435 3373589 := bbase (se 6 (by rfl) ⟨79068, by rfl⟩ : syracuseStep 3373589 = 158137) (by norm_num)
theorem B2249059 : Blo 1997435 2249059 := bstep (se 1 (by rfl) ⟨1686794, by rfl⟩ : syracuseStep 2249059 = 3373589) B3373589
theorem B2998745 : Blo 1997435 2998745 := bstep (se 2 (by rfl) ⟨1124529, by rfl⟩ : syracuseStep 2998745 = 2249059) B2249059
theorem B1999163 : Blo 1997435 1999163 := bstep (se 1 (by rfl) ⟨1499372, by rfl⟩ : syracuseStep 1999163 = 2998745) B2998745
theorem B19213685 : Blo 1997435 19213685 := bbase (se 5 (by rfl) ⟨900641, by rfl⟩ : syracuseStep 19213685 = 1801283) (by norm_num)
theorem B12809123 : Blo 1997435 12809123 := bstep (se 1 (by rfl) ⟨9606842, by rfl⟩ : syracuseStep 12809123 = 19213685) B19213685
theorem B8539415 : Blo 1997435 8539415 := bstep (se 1 (by rfl) ⟨6404561, by rfl⟩ : syracuseStep 8539415 = 12809123) B12809123
theorem B5692943 : Blo 1997435 5692943 := bstep (se 1 (by rfl) ⟨4269707, by rfl⟩ : syracuseStep 5692943 = 8539415) B8539415
theorem B15181181 : Blo 1997435 15181181 := bstep (se 3 (by rfl) ⟨2846471, by rfl⟩ : syracuseStep 15181181 = 5692943) B5692943
theorem B10120787 : Blo 1997435 10120787 := bstep (se 1 (by rfl) ⟨7590590, by rfl⟩ : syracuseStep 10120787 = 15181181) B15181181
theorem B6747191 : Blo 1997435 6747191 := bstep (se 1 (by rfl) ⟨5060393, by rfl⟩ : syracuseStep 6747191 = 10120787) B10120787
theorem B4498127 : Blo 1997435 4498127 := bstep (se 1 (by rfl) ⟨3373595, by rfl⟩ : syracuseStep 4498127 = 6747191) B6747191
theorem B2998751 : Blo 1997435 2998751 := bstep (se 1 (by rfl) ⟨2249063, by rfl⟩ : syracuseStep 2998751 = 4498127) B4498127
theorem B1999167 : Blo 1997435 1999167 := bstep (se 1 (by rfl) ⟨1499375, by rfl⟩ : syracuseStep 1999167 = 2998751) B2998751
theorem B2998757 : Blo 1997435 2998757 := bbase (se 4 (by rfl) ⟨281133, by rfl⟩ : syracuseStep 2998757 = 562267) (by norm_num)
theorem B1999171 : Blo 1997435 1999171 := bstep (se 1 (by rfl) ⟨1499378, by rfl⟩ : syracuseStep 1999171 = 2998757) B2998757
theorem B14410325 : Blo 1997435 14410325 := bbase (se 8 (by rfl) ⟨84435, by rfl⟩ : syracuseStep 14410325 = 168871) (by norm_num)
theorem B9606883 : Blo 1997435 9606883 := bstep (se 1 (by rfl) ⟨7205162, by rfl⟩ : syracuseStep 9606883 = 14410325) B14410325
theorem B12809177 : Blo 1997435 12809177 := bstep (se 2 (by rfl) ⟨4803441, by rfl⟩ : syracuseStep 12809177 = 9606883) B9606883
theorem B8539451 : Blo 1997435 8539451 := bstep (se 1 (by rfl) ⟨6404588, by rfl⟩ : syracuseStep 8539451 = 12809177) B12809177
theorem B5692967 : Blo 1997435 5692967 := bstep (se 1 (by rfl) ⟨4269725, by rfl⟩ : syracuseStep 5692967 = 8539451) B8539451
theorem B3795311 : Blo 1997435 3795311 := bstep (se 1 (by rfl) ⟨2846483, by rfl⟩ : syracuseStep 3795311 = 5692967) B5692967
theorem B2530207 : Blo 1997435 2530207 := bstep (se 1 (by rfl) ⟨1897655, by rfl⟩ : syracuseStep 2530207 = 3795311) B3795311
theorem B3373609 : Blo 1997435 3373609 := bstep (se 2 (by rfl) ⟨1265103, by rfl⟩ : syracuseStep 3373609 = 2530207) B2530207
theorem B4498145 : Blo 1997435 4498145 := bstep (se 2 (by rfl) ⟨1686804, by rfl⟩ : syracuseStep 4498145 = 3373609) B3373609
theorem B2998763 : Blo 1997435 2998763 := bstep (se 1 (by rfl) ⟨2249072, by rfl⟩ : syracuseStep 2998763 = 4498145) B4498145
theorem B1999175 : Blo 1997435 1999175 := bstep (se 1 (by rfl) ⟨1499381, by rfl⟩ : syracuseStep 1999175 = 2998763) B2998763
theorem B2249077 : Blo 1997435 2249077 := bbase (se 5 (by rfl) ⟨105425, by rfl⟩ : syracuseStep 2249077 = 210851) (by norm_num)
theorem B2998769 : Blo 1997435 2998769 := bstep (se 2 (by rfl) ⟨1124538, by rfl⟩ : syracuseStep 2998769 = 2249077) B2249077
theorem B1999179 : Blo 1997435 1999179 := bstep (se 1 (by rfl) ⟨1499384, by rfl⟩ : syracuseStep 1999179 = 2998769) B2998769
theorem B2530217 : Blo 1997435 2530217 := bbase (se 2 (by rfl) ⟨948831, by rfl⟩ : syracuseStep 2530217 = 1897663) (by norm_num)
theorem B6747245 : Blo 1997435 6747245 := bstep (se 3 (by rfl) ⟨1265108, by rfl⟩ : syracuseStep 6747245 = 2530217) B2530217
theorem B4498163 : Blo 1997435 4498163 := bstep (se 1 (by rfl) ⟨3373622, by rfl⟩ : syracuseStep 4498163 = 6747245) B6747245
theorem B2998775 : Blo 1997435 2998775 := bstep (se 1 (by rfl) ⟨2249081, by rfl⟩ : syracuseStep 2998775 = 4498163) B4498163
theorem B1999183 : Blo 1997435 1999183 := bstep (se 1 (by rfl) ⟨1499387, by rfl⟩ : syracuseStep 1999183 = 2998775) B2998775
theorem B2998781 : Blo 1997435 2998781 := bbase (se 3 (by rfl) ⟨562271, by rfl⟩ : syracuseStep 2998781 = 1124543) (by norm_num)
theorem B1999187 : Blo 1997435 1999187 := bstep (se 1 (by rfl) ⟨1499390, by rfl⟩ : syracuseStep 1999187 = 2998781) B2998781
theorem B4498181 : Blo 1997435 4498181 := bbase (se 4 (by rfl) ⟨421704, by rfl⟩ : syracuseStep 4498181 = 843409) (by norm_num)
theorem B2998787 : Blo 1997435 2998787 := bstep (se 1 (by rfl) ⟨2249090, by rfl⟩ : syracuseStep 2998787 = 4498181) B4498181
theorem B1999191 : Blo 1997435 1999191 := bstep (se 1 (by rfl) ⟨1499393, by rfl⟩ : syracuseStep 1999191 = 2998787) B2998787
theorem B3795349 : Blo 1997435 3795349 := bbase (se 6 (by rfl) ⟨88953, by rfl⟩ : syracuseStep 3795349 = 177907) (by norm_num)
theorem B5060465 : Blo 1997435 5060465 := bstep (se 2 (by rfl) ⟨1897674, by rfl⟩ : syracuseStep 5060465 = 3795349) B3795349
theorem B3373643 : Blo 1997435 3373643 := bstep (se 1 (by rfl) ⟨2530232, by rfl⟩ : syracuseStep 3373643 = 5060465) B5060465
theorem B2249095 : Blo 1997435 2249095 := bstep (se 1 (by rfl) ⟨1686821, by rfl⟩ : syracuseStep 2249095 = 3373643) B3373643
theorem B2998793 : Blo 1997435 2998793 := bstep (se 2 (by rfl) ⟨1124547, by rfl⟩ : syracuseStep 2998793 = 2249095) B2249095
theorem B1999195 : Blo 1997435 1999195 := bstep (se 1 (by rfl) ⟨1499396, by rfl⟩ : syracuseStep 1999195 = 2998793) B2998793
theorem B10120949 : Blo 1997435 10120949 := bbase (se 5 (by rfl) ⟨474419, by rfl⟩ : syracuseStep 10120949 = 948839) (by norm_num)
theorem B6747299 : Blo 1997435 6747299 := bstep (se 1 (by rfl) ⟨5060474, by rfl⟩ : syracuseStep 6747299 = 10120949) B10120949
theorem B4498199 : Blo 1997435 4498199 := bstep (se 1 (by rfl) ⟨3373649, by rfl⟩ : syracuseStep 4498199 = 6747299) B6747299
theorem B2998799 : Blo 1997435 2998799 := bstep (se 1 (by rfl) ⟨2249099, by rfl⟩ : syracuseStep 2998799 = 4498199) B4498199
theorem B1999199 : Blo 1997435 1999199 := bstep (se 1 (by rfl) ⟨1499399, by rfl⟩ : syracuseStep 1999199 = 2998799) B2998799
theorem B2998805 : Blo 1997435 2998805 := bbase (se 6 (by rfl) ⟨70284, by rfl⟩ : syracuseStep 2998805 = 140569) (by norm_num)
theorem B1999203 : Blo 1997435 1999203 := bstep (se 1 (by rfl) ⟨1499402, by rfl⟩ : syracuseStep 1999203 = 2998805) B2998805
theorem B2776213 : Blo 1997435 2776213 := bbase (se 6 (by rfl) ⟨65067, by rfl⟩ : syracuseStep 2776213 = 130135) (by norm_num)
theorem B14806469 : Blo 1997435 14806469 := bstep (se 4 (by rfl) ⟨1388106, by rfl⟩ : syracuseStep 14806469 = 2776213) B2776213
theorem B9870979 : Blo 1997435 9870979 := bstep (se 1 (by rfl) ⟨7403234, by rfl⟩ : syracuseStep 9870979 = 14806469) B14806469
theorem B13161305 : Blo 1997435 13161305 := bstep (se 2 (by rfl) ⟨4935489, by rfl⟩ : syracuseStep 13161305 = 9870979) B9870979
theorem B8774203 : Blo 1997435 8774203 := bstep (se 1 (by rfl) ⟨6580652, by rfl⟩ : syracuseStep 8774203 = 13161305) B13161305
theorem B11698937 : Blo 1997435 11698937 := bstep (se 2 (by rfl) ⟨4387101, by rfl⟩ : syracuseStep 11698937 = 8774203) B8774203
theorem B7799291 : Blo 1997435 7799291 := bstep (se 1 (by rfl) ⟨5849468, by rfl⟩ : syracuseStep 7799291 = 11698937) B11698937
theorem B5199527 : Blo 1997435 5199527 := bstep (se 1 (by rfl) ⟨3899645, by rfl⟩ : syracuseStep 5199527 = 7799291) B7799291
theorem B3466351 : Blo 1997435 3466351 := bstep (se 1 (by rfl) ⟨2599763, by rfl⟩ : syracuseStep 3466351 = 5199527) B5199527
theorem B4621801 : Blo 1997435 4621801 := bstep (se 2 (by rfl) ⟨1733175, by rfl⟩ : syracuseStep 4621801 = 3466351) B3466351
theorem B6162401 : Blo 1997435 6162401 := bstep (se 2 (by rfl) ⟨2310900, by rfl⟩ : syracuseStep 6162401 = 4621801) B4621801
theorem B4108267 : Blo 1997435 4108267 := bstep (se 1 (by rfl) ⟨3081200, by rfl⟩ : syracuseStep 4108267 = 6162401) B6162401
theorem B5477689 : Blo 1997435 5477689 := bstep (se 2 (by rfl) ⟨2054133, by rfl⟩ : syracuseStep 5477689 = 4108267) B4108267
theorem B29214341 : Blo 1997435 29214341 := bstep (se 4 (by rfl) ⟨2738844, by rfl⟩ : syracuseStep 29214341 = 5477689) B5477689
theorem B19476227 : Blo 1997435 19476227 := bstep (se 1 (by rfl) ⟨14607170, by rfl⟩ : syracuseStep 19476227 = 29214341) B29214341
theorem B12984151 : Blo 1997435 12984151 := bstep (se 1 (by rfl) ⟨9738113, by rfl⟩ : syracuseStep 12984151 = 19476227) B19476227
theorem B17312201 : Blo 1997435 17312201 := bstep (se 2 (by rfl) ⟨6492075, by rfl⟩ : syracuseStep 17312201 = 12984151) B12984151
theorem B11541467 : Blo 1997435 11541467 := bstep (se 1 (by rfl) ⟨8656100, by rfl⟩ : syracuseStep 11541467 = 17312201) B17312201
theorem B7694311 : Blo 1997435 7694311 := bstep (se 1 (by rfl) ⟨5770733, by rfl⟩ : syracuseStep 7694311 = 11541467) B11541467
theorem B10259081 : Blo 1997435 10259081 := bstep (se 2 (by rfl) ⟨3847155, by rfl⟩ : syracuseStep 10259081 = 7694311) B7694311
theorem B6839387 : Blo 1997435 6839387 := bstep (se 1 (by rfl) ⟨5129540, by rfl⟩ : syracuseStep 6839387 = 10259081) B10259081
theorem B4559591 : Blo 1997435 4559591 := bstep (se 1 (by rfl) ⟨3419693, by rfl⟩ : syracuseStep 4559591 = 6839387) B6839387
theorem B12158909 : Blo 1997435 12158909 := bstep (se 3 (by rfl) ⟨2279795, by rfl⟩ : syracuseStep 12158909 = 4559591) B4559591
theorem B8105939 : Blo 1997435 8105939 := bstep (se 1 (by rfl) ⟨6079454, by rfl⟩ : syracuseStep 8105939 = 12158909) B12158909
theorem B5403959 : Blo 1997435 5403959 := bstep (se 1 (by rfl) ⟨4052969, by rfl⟩ : syracuseStep 5403959 = 8105939) B8105939
theorem B3602639 : Blo 1997435 3602639 := bstep (se 1 (by rfl) ⟨2701979, by rfl⟩ : syracuseStep 3602639 = 5403959) B5403959
theorem B2401759 : Blo 1997435 2401759 := bstep (se 1 (by rfl) ⟨1801319, by rfl⟩ : syracuseStep 2401759 = 3602639) B3602639
theorem B3202345 : Blo 1997435 3202345 := bstep (se 2 (by rfl) ⟨1200879, by rfl⟩ : syracuseStep 3202345 = 2401759) B2401759
theorem B17079173 : Blo 1997435 17079173 := bstep (se 4 (by rfl) ⟨1601172, by rfl⟩ : syracuseStep 17079173 = 3202345) B3202345
theorem B11386115 : Blo 1997435 11386115 := bstep (se 1 (by rfl) ⟨8539586, by rfl⟩ : syracuseStep 11386115 = 17079173) B17079173
theorem B7590743 : Blo 1997435 7590743 := bstep (se 1 (by rfl) ⟨5693057, by rfl⟩ : syracuseStep 7590743 = 11386115) B11386115
theorem B5060495 : Blo 1997435 5060495 := bstep (se 1 (by rfl) ⟨3795371, by rfl⟩ : syracuseStep 5060495 = 7590743) B7590743
theorem B3373663 : Blo 1997435 3373663 := bstep (se 1 (by rfl) ⟨2530247, by rfl⟩ : syracuseStep 3373663 = 5060495) B5060495
theorem B4498217 : Blo 1997435 4498217 := bstep (se 2 (by rfl) ⟨1686831, by rfl⟩ : syracuseStep 4498217 = 3373663) B3373663
theorem B2998811 : Blo 1997435 2998811 := bstep (se 1 (by rfl) ⟨2249108, by rfl⟩ : syracuseStep 2998811 = 4498217) B4498217
theorem B1999207 : Blo 1997435 1999207 := bstep (se 1 (by rfl) ⟨1499405, by rfl⟩ : syracuseStep 1999207 = 2998811) B2998811
theorem B2249113 : Blo 1997435 2249113 := bbase (se 2 (by rfl) ⟨843417, by rfl⟩ : syracuseStep 2249113 = 1686835) (by norm_num)
theorem B2998817 : Blo 1997435 2998817 := bstep (se 2 (by rfl) ⟨1124556, by rfl⟩ : syracuseStep 2998817 = 2249113) B2249113
theorem B1999211 : Blo 1997435 1999211 := bstep (se 1 (by rfl) ⟨1499408, by rfl⟩ : syracuseStep 1999211 = 2998817) B2998817
theorem B7590773 : Blo 1997435 7590773 := bbase (se 5 (by rfl) ⟨355817, by rfl⟩ : syracuseStep 7590773 = 711635) (by norm_num)
theorem B5060515 : Blo 1997435 5060515 := bstep (se 1 (by rfl) ⟨3795386, by rfl⟩ : syracuseStep 5060515 = 7590773) B7590773
theorem B6747353 : Blo 1997435 6747353 := bstep (se 2 (by rfl) ⟨2530257, by rfl⟩ : syracuseStep 6747353 = 5060515) B5060515
theorem B4498235 : Blo 1997435 4498235 := bstep (se 1 (by rfl) ⟨3373676, by rfl⟩ : syracuseStep 4498235 = 6747353) B6747353
theorem B2998823 : Blo 1997435 2998823 := bstep (se 1 (by rfl) ⟨2249117, by rfl⟩ : syracuseStep 2998823 = 4498235) B4498235
theorem B1999215 : Blo 1997435 1999215 := bstep (se 1 (by rfl) ⟨1499411, by rfl⟩ : syracuseStep 1999215 = 2998823) B2998823
theorem B2998829 : Blo 1997435 2998829 := bbase (se 3 (by rfl) ⟨562280, by rfl⟩ : syracuseStep 2998829 = 1124561) (by norm_num)
theorem B1999219 : Blo 1997435 1999219 := bstep (se 1 (by rfl) ⟨1499414, by rfl⟩ : syracuseStep 1999219 = 2998829) B2998829
theorem B4498253 : Blo 1997435 4498253 := bbase (se 3 (by rfl) ⟨843422, by rfl⟩ : syracuseStep 4498253 = 1686845) (by norm_num)
theorem B2998835 : Blo 1997435 2998835 := bstep (se 1 (by rfl) ⟨2249126, by rfl⟩ : syracuseStep 2998835 = 4498253) B4498253
theorem B1999223 : Blo 1997435 1999223 := bstep (se 1 (by rfl) ⟨1499417, by rfl⟩ : syracuseStep 1999223 = 2998835) B2998835
theorem B2530273 : Blo 1997435 2530273 := bbase (se 2 (by rfl) ⟨948852, by rfl⟩ : syracuseStep 2530273 = 1897705) (by norm_num)
theorem B3373697 : Blo 1997435 3373697 := bstep (se 2 (by rfl) ⟨1265136, by rfl⟩ : syracuseStep 3373697 = 2530273) B2530273
theorem B2249131 : Blo 1997435 2249131 := bstep (se 1 (by rfl) ⟨1686848, by rfl⟩ : syracuseStep 2249131 = 3373697) B3373697
theorem B2998841 : Blo 1997435 2998841 := bstep (se 2 (by rfl) ⟨1124565, by rfl⟩ : syracuseStep 2998841 = 2249131) B2249131
theorem B1999227 : Blo 1997435 1999227 := bstep (se 1 (by rfl) ⟨1499420, by rfl⟩ : syracuseStep 1999227 = 2998841) B2998841
theorem B22772501 : Blo 1997435 22772501 := bbase (se 6 (by rfl) ⟨533730, by rfl⟩ : syracuseStep 22772501 = 1067461) (by norm_num)
theorem B15181667 : Blo 1997435 15181667 := bstep (se 1 (by rfl) ⟨11386250, by rfl⟩ : syracuseStep 15181667 = 22772501) B22772501
theorem B10121111 : Blo 1997435 10121111 := bstep (se 1 (by rfl) ⟨7590833, by rfl⟩ : syracuseStep 10121111 = 15181667) B15181667
theorem B6747407 : Blo 1997435 6747407 := bstep (se 1 (by rfl) ⟨5060555, by rfl⟩ : syracuseStep 6747407 = 10121111) B10121111
theorem B4498271 : Blo 1997435 4498271 := bstep (se 1 (by rfl) ⟨3373703, by rfl⟩ : syracuseStep 4498271 = 6747407) B6747407
theorem B2998847 : Blo 1997435 2998847 := bstep (se 1 (by rfl) ⟨2249135, by rfl⟩ : syracuseStep 2998847 = 4498271) B4498271
theorem B1999231 : Blo 1997435 1999231 := bstep (se 1 (by rfl) ⟨1499423, by rfl⟩ : syracuseStep 1999231 = 2998847) B2998847
theorem B2998853 : Blo 1997435 2998853 := bbase (se 4 (by rfl) ⟨281142, by rfl⟩ : syracuseStep 2998853 = 562285) (by norm_num)
theorem B1999235 : Blo 1997435 1999235 := bstep (se 1 (by rfl) ⟨1499426, by rfl⟩ : syracuseStep 1999235 = 2998853) B2998853
theorem B3373717 : Blo 1997435 3373717 := bbase (se 6 (by rfl) ⟨79071, by rfl⟩ : syracuseStep 3373717 = 158143) (by norm_num)
theorem B4498289 : Blo 1997435 4498289 := bstep (se 2 (by rfl) ⟨1686858, by rfl⟩ : syracuseStep 4498289 = 3373717) B3373717
theorem B2998859 : Blo 1997435 2998859 := bstep (se 1 (by rfl) ⟨2249144, by rfl⟩ : syracuseStep 2998859 = 4498289) B4498289
theorem B1999239 : Blo 1997435 1999239 := bstep (se 1 (by rfl) ⟨1499429, by rfl⟩ : syracuseStep 1999239 = 2998859) B2998859
theorem B2249149 : Blo 1997435 2249149 := bbase (se 3 (by rfl) ⟨421715, by rfl⟩ : syracuseStep 2249149 = 843431) (by norm_num)
theorem B2998865 : Blo 1997435 2998865 := bstep (se 2 (by rfl) ⟨1124574, by rfl⟩ : syracuseStep 2998865 = 2249149) B2249149
theorem B1999243 : Blo 1997435 1999243 := bstep (se 1 (by rfl) ⟨1499432, by rfl⟩ : syracuseStep 1999243 = 2998865) B2998865
theorem B6747461 : Blo 1997435 6747461 := bbase (se 4 (by rfl) ⟨632574, by rfl⟩ : syracuseStep 6747461 = 1265149) (by norm_num)
theorem B4498307 : Blo 1997435 4498307 := bstep (se 1 (by rfl) ⟨3373730, by rfl⟩ : syracuseStep 4498307 = 6747461) B6747461
theorem B2998871 : Blo 1997435 2998871 := bstep (se 1 (by rfl) ⟨2249153, by rfl⟩ : syracuseStep 2998871 = 4498307) B4498307
theorem B1999247 : Blo 1997435 1999247 := bstep (se 1 (by rfl) ⟨1499435, by rfl⟩ : syracuseStep 1999247 = 2998871) B2998871
theorem B2998877 : Blo 1997435 2998877 := bbase (se 3 (by rfl) ⟨562289, by rfl⟩ : syracuseStep 2998877 = 1124579) (by norm_num)
theorem B1999251 : Blo 1997435 1999251 := bstep (se 1 (by rfl) ⟨1499438, by rfl⟩ : syracuseStep 1999251 = 2998877) B2998877
theorem B4498325 : Blo 1997435 4498325 := bbase (se 6 (by rfl) ⟨105429, by rfl⟩ : syracuseStep 4498325 = 210859) (by norm_num)
theorem B2998883 : Blo 1997435 2998883 := bstep (se 1 (by rfl) ⟨2249162, by rfl⟩ : syracuseStep 2998883 = 4498325) B4498325
theorem B1999255 : Blo 1997435 1999255 := bstep (se 1 (by rfl) ⟨1499441, by rfl⟩ : syracuseStep 1999255 = 2998883) B2998883
theorem B3202429 : Blo 1997435 3202429 := bbase (se 3 (by rfl) ⟨600455, by rfl⟩ : syracuseStep 3202429 = 1200911) (by norm_num)
theorem B4269905 : Blo 1997435 4269905 := bstep (se 2 (by rfl) ⟨1601214, by rfl⟩ : syracuseStep 4269905 = 3202429) B3202429
theorem B2846603 : Blo 1997435 2846603 := bstep (se 1 (by rfl) ⟨2134952, by rfl⟩ : syracuseStep 2846603 = 4269905) B4269905
theorem B7590941 : Blo 1997435 7590941 := bstep (se 3 (by rfl) ⟨1423301, by rfl⟩ : syracuseStep 7590941 = 2846603) B2846603
theorem B5060627 : Blo 1997435 5060627 := bstep (se 1 (by rfl) ⟨3795470, by rfl⟩ : syracuseStep 5060627 = 7590941) B7590941
theorem B3373751 : Blo 1997435 3373751 := bstep (se 1 (by rfl) ⟨2530313, by rfl⟩ : syracuseStep 3373751 = 5060627) B5060627
theorem B2249167 : Blo 1997435 2249167 := bstep (se 1 (by rfl) ⟨1686875, by rfl⟩ : syracuseStep 2249167 = 3373751) B3373751
theorem B2998889 : Blo 1997435 2998889 := bstep (se 2 (by rfl) ⟨1124583, by rfl⟩ : syracuseStep 2998889 = 2249167) B2249167
theorem B1999259 : Blo 1997435 1999259 := bstep (se 1 (by rfl) ⟨1499444, by rfl⟩ : syracuseStep 1999259 = 2998889) B2998889
theorem B6404869 : Blo 1997435 6404869 := bbase (se 4 (by rfl) ⟨600456, by rfl⟩ : syracuseStep 6404869 = 1200913) (by norm_num)
theorem B8539825 : Blo 1997435 8539825 := bstep (se 2 (by rfl) ⟨3202434, by rfl⟩ : syracuseStep 8539825 = 6404869) B6404869
theorem B11386433 : Blo 1997435 11386433 := bstep (se 2 (by rfl) ⟨4269912, by rfl⟩ : syracuseStep 11386433 = 8539825) B8539825
theorem B7590955 : Blo 1997435 7590955 := bstep (se 1 (by rfl) ⟨5693216, by rfl⟩ : syracuseStep 7590955 = 11386433) B11386433
theorem B10121273 : Blo 1997435 10121273 := bstep (se 2 (by rfl) ⟨3795477, by rfl⟩ : syracuseStep 10121273 = 7590955) B7590955
theorem B6747515 : Blo 1997435 6747515 := bstep (se 1 (by rfl) ⟨5060636, by rfl⟩ : syracuseStep 6747515 = 10121273) B10121273
theorem B4498343 : Blo 1997435 4498343 := bstep (se 1 (by rfl) ⟨3373757, by rfl⟩ : syracuseStep 4498343 = 6747515) B6747515
theorem B2998895 : Blo 1997435 2998895 := bstep (se 1 (by rfl) ⟨2249171, by rfl⟩ : syracuseStep 2998895 = 4498343) B4498343
theorem B1999263 : Blo 1997435 1999263 := bstep (se 1 (by rfl) ⟨1499447, by rfl⟩ : syracuseStep 1999263 = 2998895) B2998895
theorem B2998901 : Blo 1997435 2998901 := bbase (se 5 (by rfl) ⟨140573, by rfl⟩ : syracuseStep 2998901 = 281147) (by norm_num)
theorem B1999267 : Blo 1997435 1999267 := bstep (se 1 (by rfl) ⟨1499450, by rfl⟩ : syracuseStep 1999267 = 2998901) B2998901
theorem B3795493 : Blo 1997435 3795493 := bbase (se 4 (by rfl) ⟨355827, by rfl⟩ : syracuseStep 3795493 = 711655) (by norm_num)
theorem B5060657 : Blo 1997435 5060657 := bstep (se 2 (by rfl) ⟨1897746, by rfl⟩ : syracuseStep 5060657 = 3795493) B3795493
theorem B3373771 : Blo 1997435 3373771 := bstep (se 1 (by rfl) ⟨2530328, by rfl⟩ : syracuseStep 3373771 = 5060657) B5060657
theorem B4498361 : Blo 1997435 4498361 := bstep (se 2 (by rfl) ⟨1686885, by rfl⟩ : syracuseStep 4498361 = 3373771) B3373771
theorem B2998907 : Blo 1997435 2998907 := bstep (se 1 (by rfl) ⟨2249180, by rfl⟩ : syracuseStep 2998907 = 4498361) B4498361
theorem B1999271 : Blo 1997435 1999271 := bstep (se 1 (by rfl) ⟨1499453, by rfl⟩ : syracuseStep 1999271 = 2998907) B2998907
theorem B2249185 : Blo 1997435 2249185 := bbase (se 2 (by rfl) ⟨843444, by rfl⟩ : syracuseStep 2249185 = 1686889) (by norm_num)
theorem B2998913 : Blo 1997435 2998913 := bstep (se 2 (by rfl) ⟨1124592, by rfl⟩ : syracuseStep 2998913 = 2249185) B2249185
theorem B1999275 : Blo 1997435 1999275 := bstep (se 1 (by rfl) ⟨1499456, by rfl⟩ : syracuseStep 1999275 = 2998913) B2998913
theorem B5060677 : Blo 1997435 5060677 := bbase (se 4 (by rfl) ⟨474438, by rfl⟩ : syracuseStep 5060677 = 948877) (by norm_num)
theorem B6747569 : Blo 1997435 6747569 := bstep (se 2 (by rfl) ⟨2530338, by rfl⟩ : syracuseStep 6747569 = 5060677) B5060677
theorem B4498379 : Blo 1997435 4498379 := bstep (se 1 (by rfl) ⟨3373784, by rfl⟩ : syracuseStep 4498379 = 6747569) B6747569
theorem B2998919 : Blo 1997435 2998919 := bstep (se 1 (by rfl) ⟨2249189, by rfl⟩ : syracuseStep 2998919 = 4498379) B4498379
theorem B1999279 : Blo 1997435 1999279 := bstep (se 1 (by rfl) ⟨1499459, by rfl⟩ : syracuseStep 1999279 = 2998919) B2998919
theorem B2998925 : Blo 1997435 2998925 := bbase (se 3 (by rfl) ⟨562298, by rfl⟩ : syracuseStep 2998925 = 1124597) (by norm_num)
theorem B1999283 : Blo 1997435 1999283 := bstep (se 1 (by rfl) ⟨1499462, by rfl⟩ : syracuseStep 1999283 = 2998925) B2998925
theorem B4498397 : Blo 1997435 4498397 := bbase (se 3 (by rfl) ⟨843449, by rfl⟩ : syracuseStep 4498397 = 1686899) (by norm_num)
theorem B2998931 : Blo 1997435 2998931 := bstep (se 1 (by rfl) ⟨2249198, by rfl⟩ : syracuseStep 2998931 = 4498397) B4498397
theorem B1999287 : Blo 1997435 1999287 := bstep (se 1 (by rfl) ⟨1499465, by rfl⟩ : syracuseStep 1999287 = 2998931) B2998931
theorem B3373805 : Blo 1997435 3373805 := bbase (se 3 (by rfl) ⟨632588, by rfl⟩ : syracuseStep 3373805 = 1265177) (by norm_num)
theorem B2249203 : Blo 1997435 2249203 := bstep (se 1 (by rfl) ⟨1686902, by rfl⟩ : syracuseStep 2249203 = 3373805) B3373805
theorem B2998937 : Blo 1997435 2998937 := bstep (se 2 (by rfl) ⟨1124601, by rfl⟩ : syracuseStep 2998937 = 2249203) B2249203
theorem B1999291 : Blo 1997435 1999291 := bstep (se 1 (by rfl) ⟨1499468, by rfl⟩ : syracuseStep 1999291 = 2998937) B2998937
theorem B8106293 : Blo 1997435 8106293 := bbase (se 5 (by rfl) ⟨379982, by rfl⟩ : syracuseStep 8106293 = 759965) (by norm_num)
theorem B5404195 : Blo 1997435 5404195 := bstep (se 1 (by rfl) ⟨4053146, by rfl⟩ : syracuseStep 5404195 = 8106293) B8106293
theorem B7205593 : Blo 1997435 7205593 := bstep (se 2 (by rfl) ⟨2702097, by rfl⟩ : syracuseStep 7205593 = 5404195) B5404195
theorem B9607457 : Blo 1997435 9607457 := bstep (se 2 (by rfl) ⟨3602796, by rfl⟩ : syracuseStep 9607457 = 7205593) B7205593
theorem B25619885 : Blo 1997435 25619885 := bstep (se 3 (by rfl) ⟨4803728, by rfl⟩ : syracuseStep 25619885 = 9607457) B9607457
theorem B17079923 : Blo 1997435 17079923 := bstep (se 1 (by rfl) ⟨12809942, by rfl⟩ : syracuseStep 17079923 = 25619885) B25619885
theorem B11386615 : Blo 1997435 11386615 := bstep (se 1 (by rfl) ⟨8539961, by rfl⟩ : syracuseStep 11386615 = 17079923) B17079923
theorem B15182153 : Blo 1997435 15182153 := bstep (se 2 (by rfl) ⟨5693307, by rfl⟩ : syracuseStep 15182153 = 11386615) B11386615
theorem B10121435 : Blo 1997435 10121435 := bstep (se 1 (by rfl) ⟨7591076, by rfl⟩ : syracuseStep 10121435 = 15182153) B15182153
theorem B6747623 : Blo 1997435 6747623 := bstep (se 1 (by rfl) ⟨5060717, by rfl⟩ : syracuseStep 6747623 = 10121435) B10121435
theorem B4498415 : Blo 1997435 4498415 := bstep (se 1 (by rfl) ⟨3373811, by rfl⟩ : syracuseStep 4498415 = 6747623) B6747623
theorem B2998943 : Blo 1997435 2998943 := bstep (se 1 (by rfl) ⟨2249207, by rfl⟩ : syracuseStep 2998943 = 4498415) B4498415
theorem B1999295 : Blo 1997435 1999295 := bstep (se 1 (by rfl) ⟨1499471, by rfl⟩ : syracuseStep 1999295 = 2998943) B2998943
theorem B2998949 : Blo 1997435 2998949 := bbase (se 4 (by rfl) ⟨281151, by rfl⟩ : syracuseStep 2998949 = 562303) (by norm_num)
theorem B1999299 : Blo 1997435 1999299 := bstep (se 1 (by rfl) ⟨1499474, by rfl⟩ : syracuseStep 1999299 = 2998949) B2998949
theorem B2530369 : Blo 1997435 2530369 := bbase (se 2 (by rfl) ⟨948888, by rfl⟩ : syracuseStep 2530369 = 1897777) (by norm_num)
theorem B3373825 : Blo 1997435 3373825 := bstep (se 2 (by rfl) ⟨1265184, by rfl⟩ : syracuseStep 3373825 = 2530369) B2530369
theorem B4498433 : Blo 1997435 4498433 := bstep (se 2 (by rfl) ⟨1686912, by rfl⟩ : syracuseStep 4498433 = 3373825) B3373825
theorem B2998955 : Blo 1997435 2998955 := bstep (se 1 (by rfl) ⟨2249216, by rfl⟩ : syracuseStep 2998955 = 4498433) B4498433
theorem B1999303 : Blo 1997435 1999303 := bstep (se 1 (by rfl) ⟨1499477, by rfl⟩ : syracuseStep 1999303 = 2998955) B2998955
theorem B2249221 : Blo 1997435 2249221 := bbase (se 4 (by rfl) ⟨210864, by rfl⟩ : syracuseStep 2249221 = 421729) (by norm_num)
theorem B2998961 : Blo 1997435 2998961 := bstep (se 2 (by rfl) ⟨1124610, by rfl⟩ : syracuseStep 2998961 = 2249221) B2249221
theorem B1999307 : Blo 1997435 1999307 := bstep (se 1 (by rfl) ⟨1499480, by rfl⟩ : syracuseStep 1999307 = 2998961) B2998961
theorem B2846677 : Blo 1997435 2846677 := bbase (se 7 (by rfl) ⟨33359, by rfl⟩ : syracuseStep 2846677 = 66719) (by norm_num)
theorem B3795569 : Blo 1997435 3795569 := bstep (se 2 (by rfl) ⟨1423338, by rfl⟩ : syracuseStep 3795569 = 2846677) B2846677
theorem B2530379 : Blo 1997435 2530379 := bstep (se 1 (by rfl) ⟨1897784, by rfl⟩ : syracuseStep 2530379 = 3795569) B3795569
theorem B6747677 : Blo 1997435 6747677 := bstep (se 3 (by rfl) ⟨1265189, by rfl⟩ : syracuseStep 6747677 = 2530379) B2530379
theorem B4498451 : Blo 1997435 4498451 := bstep (se 1 (by rfl) ⟨3373838, by rfl⟩ : syracuseStep 4498451 = 6747677) B6747677
theorem B2998967 : Blo 1997435 2998967 := bstep (se 1 (by rfl) ⟨2249225, by rfl⟩ : syracuseStep 2998967 = 4498451) B4498451
theorem B1999311 : Blo 1997435 1999311 := bstep (se 1 (by rfl) ⟨1499483, by rfl⟩ : syracuseStep 1999311 = 2998967) B2998967
theorem B2998973 : Blo 1997435 2998973 := bbase (se 3 (by rfl) ⟨562307, by rfl⟩ : syracuseStep 2998973 = 1124615) (by norm_num)
theorem B1999315 : Blo 1997435 1999315 := bstep (se 1 (by rfl) ⟨1499486, by rfl⟩ : syracuseStep 1999315 = 2998973) B2998973
theorem B4498469 : Blo 1997435 4498469 := bbase (se 4 (by rfl) ⟨421731, by rfl⟩ : syracuseStep 4498469 = 843463) (by norm_num)
theorem B2998979 : Blo 1997435 2998979 := bstep (se 1 (by rfl) ⟨2249234, by rfl⟩ : syracuseStep 2998979 = 4498469) B4498469
theorem B1999319 : Blo 1997435 1999319 := bstep (se 1 (by rfl) ⟨1499489, by rfl⟩ : syracuseStep 1999319 = 2998979) B2998979
theorem B5060789 : Blo 1997435 5060789 := bbase (se 5 (by rfl) ⟨237224, by rfl⟩ : syracuseStep 5060789 = 474449) (by norm_num)
theorem B3373859 : Blo 1997435 3373859 := bstep (se 1 (by rfl) ⟨2530394, by rfl⟩ : syracuseStep 3373859 = 5060789) B5060789
theorem B2249239 : Blo 1997435 2249239 := bstep (se 1 (by rfl) ⟨1686929, by rfl⟩ : syracuseStep 2249239 = 3373859) B3373859
theorem B2998985 : Blo 1997435 2998985 := bstep (se 2 (by rfl) ⟨1124619, by rfl⟩ : syracuseStep 2998985 = 2249239) B2249239
theorem B1999323 : Blo 1997435 1999323 := bstep (se 1 (by rfl) ⟨1499492, by rfl⟩ : syracuseStep 1999323 = 2998985) B2998985
theorem B6839797 : Blo 1997435 6839797 := bbase (se 5 (by rfl) ⟨320615, by rfl⟩ : syracuseStep 6839797 = 641231) (by norm_num)
theorem B9119729 : Blo 1997435 9119729 := bstep (se 2 (by rfl) ⟨3419898, by rfl⟩ : syracuseStep 9119729 = 6839797) B6839797
theorem B6079819 : Blo 1997435 6079819 := bstep (se 1 (by rfl) ⟨4559864, by rfl⟩ : syracuseStep 6079819 = 9119729) B9119729
theorem B8106425 : Blo 1997435 8106425 := bstep (se 2 (by rfl) ⟨3039909, by rfl⟩ : syracuseStep 8106425 = 6079819) B6079819
theorem B5404283 : Blo 1997435 5404283 := bstep (se 1 (by rfl) ⟨4053212, by rfl⟩ : syracuseStep 5404283 = 8106425) B8106425
theorem B3602855 : Blo 1997435 3602855 := bstep (se 1 (by rfl) ⟨2702141, by rfl⟩ : syracuseStep 3602855 = 5404283) B5404283
theorem B2401903 : Blo 1997435 2401903 := bstep (se 1 (by rfl) ⟨1801427, by rfl⟩ : syracuseStep 2401903 = 3602855) B3602855
theorem B12810149 : Blo 1997435 12810149 := bstep (se 4 (by rfl) ⟨1200951, by rfl⟩ : syracuseStep 12810149 = 2401903) B2401903
theorem B8540099 : Blo 1997435 8540099 := bstep (se 1 (by rfl) ⟨6405074, by rfl⟩ : syracuseStep 8540099 = 12810149) B12810149
theorem B5693399 : Blo 1997435 5693399 := bstep (se 1 (by rfl) ⟨4270049, by rfl⟩ : syracuseStep 5693399 = 8540099) B8540099
theorem B3795599 : Blo 1997435 3795599 := bstep (se 1 (by rfl) ⟨2846699, by rfl⟩ : syracuseStep 3795599 = 5693399) B5693399
theorem B10121597 : Blo 1997435 10121597 := bstep (se 3 (by rfl) ⟨1897799, by rfl⟩ : syracuseStep 10121597 = 3795599) B3795599
theorem B6747731 : Blo 1997435 6747731 := bstep (se 1 (by rfl) ⟨5060798, by rfl⟩ : syracuseStep 6747731 = 10121597) B10121597
theorem B4498487 : Blo 1997435 4498487 := bstep (se 1 (by rfl) ⟨3373865, by rfl⟩ : syracuseStep 4498487 = 6747731) B6747731
theorem B2998991 : Blo 1997435 2998991 := bstep (se 1 (by rfl) ⟨2249243, by rfl⟩ : syracuseStep 2998991 = 4498487) B4498487
theorem B1999327 : Blo 1997435 1999327 := bstep (se 1 (by rfl) ⟨1499495, by rfl⟩ : syracuseStep 1999327 = 2998991) B2998991
theorem B2998997 : Blo 1997435 2998997 := bbase (se 7 (by rfl) ⟨35144, by rfl⟩ : syracuseStep 2998997 = 70289) (by norm_num)
theorem B1999331 : Blo 1997435 1999331 := bstep (se 1 (by rfl) ⟨1499498, by rfl⟩ : syracuseStep 1999331 = 2998997) B2998997
theorem B2401913 : Blo 1997435 2401913 := bbase (se 2 (by rfl) ⟨900717, by rfl⟩ : syracuseStep 2401913 = 1801435) (by norm_num)
theorem B6405101 : Blo 1997435 6405101 := bstep (se 3 (by rfl) ⟨1200956, by rfl⟩ : syracuseStep 6405101 = 2401913) B2401913
theorem B4270067 : Blo 1997435 4270067 := bstep (se 1 (by rfl) ⟨3202550, by rfl⟩ : syracuseStep 4270067 = 6405101) B6405101
theorem B2846711 : Blo 1997435 2846711 := bstep (se 1 (by rfl) ⟨2135033, by rfl⟩ : syracuseStep 2846711 = 4270067) B4270067
theorem B7591229 : Blo 1997435 7591229 := bstep (se 3 (by rfl) ⟨1423355, by rfl⟩ : syracuseStep 7591229 = 2846711) B2846711
theorem B5060819 : Blo 1997435 5060819 := bstep (se 1 (by rfl) ⟨3795614, by rfl⟩ : syracuseStep 5060819 = 7591229) B7591229
theorem B3373879 : Blo 1997435 3373879 := bstep (se 1 (by rfl) ⟨2530409, by rfl⟩ : syracuseStep 3373879 = 5060819) B5060819
theorem B4498505 : Blo 1997435 4498505 := bstep (se 2 (by rfl) ⟨1686939, by rfl⟩ : syracuseStep 4498505 = 3373879) B3373879
theorem B2999003 : Blo 1997435 2999003 := bstep (se 1 (by rfl) ⟨2249252, by rfl⟩ : syracuseStep 2999003 = 4498505) B4498505
theorem B1999335 : Blo 1997435 1999335 := bstep (se 1 (by rfl) ⟨1499501, by rfl⟩ : syracuseStep 1999335 = 2999003) B2999003
theorem B2249257 : Blo 1997435 2249257 := bbase (se 2 (by rfl) ⟨843471, by rfl⟩ : syracuseStep 2249257 = 1686943) (by norm_num)
theorem B2999009 : Blo 1997435 2999009 := bstep (se 2 (by rfl) ⟨1124628, by rfl⟩ : syracuseStep 2999009 = 2249257) B2249257
theorem B1999339 : Blo 1997435 1999339 := bstep (se 1 (by rfl) ⟨1499504, by rfl⟩ : syracuseStep 1999339 = 2999009) B2999009
theorem B5404325 : Blo 1997435 5404325 := bbase (se 4 (by rfl) ⟨506655, by rfl⟩ : syracuseStep 5404325 = 1013311) (by norm_num)
theorem B14411533 : Blo 1997435 14411533 := bstep (se 3 (by rfl) ⟨2702162, by rfl⟩ : syracuseStep 14411533 = 5404325) B5404325
theorem B19215377 : Blo 1997435 19215377 := bstep (se 2 (by rfl) ⟨7205766, by rfl⟩ : syracuseStep 19215377 = 14411533) B14411533
theorem B12810251 : Blo 1997435 12810251 := bstep (se 1 (by rfl) ⟨9607688, by rfl⟩ : syracuseStep 12810251 = 19215377) B19215377
theorem B8540167 : Blo 1997435 8540167 := bstep (se 1 (by rfl) ⟨6405125, by rfl⟩ : syracuseStep 8540167 = 12810251) B12810251
theorem B11386889 : Blo 1997435 11386889 := bstep (se 2 (by rfl) ⟨4270083, by rfl⟩ : syracuseStep 11386889 = 8540167) B8540167
theorem B7591259 : Blo 1997435 7591259 := bstep (se 1 (by rfl) ⟨5693444, by rfl⟩ : syracuseStep 7591259 = 11386889) B11386889
theorem B5060839 : Blo 1997435 5060839 := bstep (se 1 (by rfl) ⟨3795629, by rfl⟩ : syracuseStep 5060839 = 7591259) B7591259
theorem B6747785 : Blo 1997435 6747785 := bstep (se 2 (by rfl) ⟨2530419, by rfl⟩ : syracuseStep 6747785 = 5060839) B5060839
theorem B4498523 : Blo 1997435 4498523 := bstep (se 1 (by rfl) ⟨3373892, by rfl⟩ : syracuseStep 4498523 = 6747785) B6747785
theorem B2999015 : Blo 1997435 2999015 := bstep (se 1 (by rfl) ⟨2249261, by rfl⟩ : syracuseStep 2999015 = 4498523) B4498523
theorem B1999343 : Blo 1997435 1999343 := bstep (se 1 (by rfl) ⟨1499507, by rfl⟩ : syracuseStep 1999343 = 2999015) B2999015
theorem B2999021 : Blo 1997435 2999021 := bbase (se 3 (by rfl) ⟨562316, by rfl⟩ : syracuseStep 2999021 = 1124633) (by norm_num)
theorem B1999347 : Blo 1997435 1999347 := bstep (se 1 (by rfl) ⟨1499510, by rfl⟩ : syracuseStep 1999347 = 2999021) B2999021
theorem B4498541 : Blo 1997435 4498541 := bbase (se 3 (by rfl) ⟨843476, by rfl⟩ : syracuseStep 4498541 = 1686953) (by norm_num)
theorem B2999027 : Blo 1997435 2999027 := bstep (se 1 (by rfl) ⟨2249270, by rfl⟩ : syracuseStep 2999027 = 4498541) B4498541
theorem B1999351 : Blo 1997435 1999351 := bstep (se 1 (by rfl) ⟨1499513, by rfl⟩ : syracuseStep 1999351 = 2999027) B2999027
theorem B3795653 : Blo 1997435 3795653 := bbase (se 4 (by rfl) ⟨355842, by rfl⟩ : syracuseStep 3795653 = 711685) (by norm_num)
theorem B2530435 : Blo 1997435 2530435 := bstep (se 1 (by rfl) ⟨1897826, by rfl⟩ : syracuseStep 2530435 = 3795653) B3795653
theorem B3373913 : Blo 1997435 3373913 := bstep (se 2 (by rfl) ⟨1265217, by rfl⟩ : syracuseStep 3373913 = 2530435) B2530435
theorem B2249275 : Blo 1997435 2249275 := bstep (se 1 (by rfl) ⟨1686956, by rfl⟩ : syracuseStep 2249275 = 3373913) B3373913
theorem B2999033 : Blo 1997435 2999033 := bstep (se 2 (by rfl) ⟨1124637, by rfl⟩ : syracuseStep 2999033 = 2249275) B2249275
theorem B1999355 : Blo 1997435 1999355 := bstep (se 1 (by rfl) ⟨1499516, by rfl⟩ : syracuseStep 1999355 = 2999033) B2999033
theorem B18996533 : Blo 1997435 18996533 := bbase (se 5 (by rfl) ⟨890462, by rfl⟩ : syracuseStep 18996533 = 1780925) (by norm_num)
theorem B12664355 : Blo 1997435 12664355 := bstep (se 1 (by rfl) ⟨9498266, by rfl⟩ : syracuseStep 12664355 = 18996533) B18996533
theorem B33771613 : Blo 1997435 33771613 := bstep (se 3 (by rfl) ⟨6332177, by rfl⟩ : syracuseStep 33771613 = 12664355) B12664355
theorem B45028817 : Blo 1997435 45028817 := bstep (se 2 (by rfl) ⟨16885806, by rfl⟩ : syracuseStep 45028817 = 33771613) B33771613
theorem B30019211 : Blo 1997435 30019211 := bstep (se 1 (by rfl) ⟨22514408, by rfl⟩ : syracuseStep 30019211 = 45028817) B45028817
theorem B20012807 : Blo 1997435 20012807 := bstep (se 1 (by rfl) ⟨15009605, by rfl⟩ : syracuseStep 20012807 = 30019211) B30019211
theorem B13341871 : Blo 1997435 13341871 := bstep (se 1 (by rfl) ⟨10006403, by rfl⟩ : syracuseStep 13341871 = 20012807) B20012807
theorem B17789161 : Blo 1997435 17789161 := bstep (se 2 (by rfl) ⟨6670935, by rfl⟩ : syracuseStep 17789161 = 13341871) B13341871
theorem B23718881 : Blo 1997435 23718881 := bstep (se 2 (by rfl) ⟨8894580, by rfl⟩ : syracuseStep 23718881 = 17789161) B17789161
theorem B15812587 : Blo 1997435 15812587 := bstep (se 1 (by rfl) ⟨11859440, by rfl⟩ : syracuseStep 15812587 = 23718881) B23718881
theorem B84333797 : Blo 1997435 84333797 := bstep (se 4 (by rfl) ⟨7906293, by rfl⟩ : syracuseStep 84333797 = 15812587) B15812587
theorem B56222531 : Blo 1997435 56222531 := bstep (se 1 (by rfl) ⟨42166898, by rfl⟩ : syracuseStep 56222531 = 84333797) B84333797
theorem B37481687 : Blo 1997435 37481687 := bstep (se 1 (by rfl) ⟨28111265, by rfl⟩ : syracuseStep 37481687 = 56222531) B56222531
theorem B24987791 : Blo 1997435 24987791 := bstep (se 1 (by rfl) ⟨18740843, by rfl⟩ : syracuseStep 24987791 = 37481687) B37481687
theorem B66634109 : Blo 1997435 66634109 := bstep (se 3 (by rfl) ⟨12493895, by rfl⟩ : syracuseStep 66634109 = 24987791) B24987791
theorem B44422739 : Blo 1997435 44422739 := bstep (se 1 (by rfl) ⟨33317054, by rfl⟩ : syracuseStep 44422739 = 66634109) B66634109
theorem B29615159 : Blo 1997435 29615159 := bstep (se 1 (by rfl) ⟨22211369, by rfl⟩ : syracuseStep 29615159 = 44422739) B44422739
theorem B19743439 : Blo 1997435 19743439 := bstep (se 1 (by rfl) ⟨14807579, by rfl⟩ : syracuseStep 19743439 = 29615159) B29615159
theorem B26324585 : Blo 1997435 26324585 := bstep (se 2 (by rfl) ⟨9871719, by rfl⟩ : syracuseStep 26324585 = 19743439) B19743439
theorem B17549723 : Blo 1997435 17549723 := bstep (se 1 (by rfl) ⟨13162292, by rfl⟩ : syracuseStep 17549723 = 26324585) B26324585
theorem B11699815 : Blo 1997435 11699815 := bstep (se 1 (by rfl) ⟨8774861, by rfl⟩ : syracuseStep 11699815 = 17549723) B17549723
theorem B15599753 : Blo 1997435 15599753 := bstep (se 2 (by rfl) ⟨5849907, by rfl⟩ : syracuseStep 15599753 = 11699815) B11699815
theorem B10399835 : Blo 1997435 10399835 := bstep (se 1 (by rfl) ⟨7799876, by rfl⟩ : syracuseStep 10399835 = 15599753) B15599753
theorem B6933223 : Blo 1997435 6933223 := bstep (se 1 (by rfl) ⟨5199917, by rfl⟩ : syracuseStep 6933223 = 10399835) B10399835
theorem B9244297 : Blo 1997435 9244297 := bstep (se 2 (by rfl) ⟨3466611, by rfl⟩ : syracuseStep 9244297 = 6933223) B6933223
theorem B49302917 : Blo 1997435 49302917 := bstep (se 4 (by rfl) ⟨4622148, by rfl⟩ : syracuseStep 49302917 = 9244297) B9244297
theorem B32868611 : Blo 1997435 32868611 := bstep (se 1 (by rfl) ⟨24651458, by rfl⟩ : syracuseStep 32868611 = 49302917) B49302917
theorem B21912407 : Blo 1997435 21912407 := bstep (se 1 (by rfl) ⟨16434305, by rfl⟩ : syracuseStep 21912407 = 32868611) B32868611
theorem B14608271 : Blo 1997435 14608271 := bstep (se 1 (by rfl) ⟨10956203, by rfl⟩ : syracuseStep 14608271 = 21912407) B21912407
theorem B9738847 : Blo 1997435 9738847 := bstep (se 1 (by rfl) ⟨7304135, by rfl⟩ : syracuseStep 9738847 = 14608271) B14608271
theorem B12985129 : Blo 1997435 12985129 := bstep (se 2 (by rfl) ⟨4869423, by rfl⟩ : syracuseStep 12985129 = 9738847) B9738847
theorem B69254021 : Blo 1997435 69254021 := bstep (se 4 (by rfl) ⟨6492564, by rfl⟩ : syracuseStep 69254021 = 12985129) B12985129
theorem B46169347 : Blo 1997435 46169347 := bstep (se 1 (by rfl) ⟨34627010, by rfl⟩ : syracuseStep 46169347 = 69254021) B69254021
theorem B61559129 : Blo 1997435 61559129 := bstep (se 2 (by rfl) ⟨23084673, by rfl⟩ : syracuseStep 61559129 = 46169347) B46169347
theorem B41039419 : Blo 1997435 41039419 := bstep (se 1 (by rfl) ⟨30779564, by rfl⟩ : syracuseStep 41039419 = 61559129) B61559129
theorem B54719225 : Blo 1997435 54719225 := bstep (se 2 (by rfl) ⟨20519709, by rfl⟩ : syracuseStep 54719225 = 41039419) B41039419
theorem B36479483 : Blo 1997435 36479483 := bstep (se 1 (by rfl) ⟨27359612, by rfl⟩ : syracuseStep 36479483 = 54719225) B54719225
theorem B24319655 : Blo 1997435 24319655 := bstep (se 1 (by rfl) ⟨18239741, by rfl⟩ : syracuseStep 24319655 = 36479483) B36479483
theorem B16213103 : Blo 1997435 16213103 := bstep (se 1 (by rfl) ⟨12159827, by rfl⟩ : syracuseStep 16213103 = 24319655) B24319655
theorem B10808735 : Blo 1997435 10808735 := bstep (se 1 (by rfl) ⟨8106551, by rfl⟩ : syracuseStep 10808735 = 16213103) B16213103
theorem B28823293 : Blo 1997435 28823293 := bstep (se 3 (by rfl) ⟨5404367, by rfl⟩ : syracuseStep 28823293 = 10808735) B10808735
theorem B38431057 : Blo 1997435 38431057 := bstep (se 2 (by rfl) ⟨14411646, by rfl⟩ : syracuseStep 38431057 = 28823293) B28823293
theorem B51241409 : Blo 1997435 51241409 := bstep (se 2 (by rfl) ⟨19215528, by rfl⟩ : syracuseStep 51241409 = 38431057) B38431057
theorem B34160939 : Blo 1997435 34160939 := bstep (se 1 (by rfl) ⟨25620704, by rfl⟩ : syracuseStep 34160939 = 51241409) B51241409
theorem B22773959 : Blo 1997435 22773959 := bstep (se 1 (by rfl) ⟨17080469, by rfl⟩ : syracuseStep 22773959 = 34160939) B34160939
theorem B15182639 : Blo 1997435 15182639 := bstep (se 1 (by rfl) ⟨11386979, by rfl⟩ : syracuseStep 15182639 = 22773959) B22773959
theorem B10121759 : Blo 1997435 10121759 := bstep (se 1 (by rfl) ⟨7591319, by rfl⟩ : syracuseStep 10121759 = 15182639) B15182639
theorem B6747839 : Blo 1997435 6747839 := bstep (se 1 (by rfl) ⟨5060879, by rfl⟩ : syracuseStep 6747839 = 10121759) B10121759
theorem B4498559 : Blo 1997435 4498559 := bstep (se 1 (by rfl) ⟨3373919, by rfl⟩ : syracuseStep 4498559 = 6747839) B6747839
theorem B2999039 : Blo 1997435 2999039 := bstep (se 1 (by rfl) ⟨2249279, by rfl⟩ : syracuseStep 2999039 = 4498559) B4498559
theorem B1999359 : Blo 1997435 1999359 := bstep (se 1 (by rfl) ⟨1499519, by rfl⟩ : syracuseStep 1999359 = 2999039) B2999039
theorem B2999045 : Blo 1997435 2999045 := bbase (se 4 (by rfl) ⟨281160, by rfl⟩ : syracuseStep 2999045 = 562321) (by norm_num)
theorem B1999363 : Blo 1997435 1999363 := bstep (se 1 (by rfl) ⟨1499522, by rfl⟩ : syracuseStep 1999363 = 2999045) B2999045
theorem B3373933 : Blo 1997435 3373933 := bbase (se 3 (by rfl) ⟨632612, by rfl⟩ : syracuseStep 3373933 = 1265225) (by norm_num)
theorem B4498577 : Blo 1997435 4498577 := bstep (se 2 (by rfl) ⟨1686966, by rfl⟩ : syracuseStep 4498577 = 3373933) B3373933
theorem B2999051 : Blo 1997435 2999051 := bstep (se 1 (by rfl) ⟨2249288, by rfl⟩ : syracuseStep 2999051 = 4498577) B4498577
theorem B1999367 : Blo 1997435 1999367 := bstep (se 1 (by rfl) ⟨1499525, by rfl⟩ : syracuseStep 1999367 = 2999051) B2999051
theorem B2249293 : Blo 1997435 2249293 := bbase (se 3 (by rfl) ⟨421742, by rfl⟩ : syracuseStep 2249293 = 843485) (by norm_num)
theorem B2999057 : Blo 1997435 2999057 := bstep (se 2 (by rfl) ⟨1124646, by rfl⟩ : syracuseStep 2999057 = 2249293) B2249293
theorem B1999371 : Blo 1997435 1999371 := bstep (se 1 (by rfl) ⟨1499528, by rfl⟩ : syracuseStep 1999371 = 2999057) B2999057
theorem B6747893 : Blo 1997435 6747893 := bbase (se 5 (by rfl) ⟨316307, by rfl⟩ : syracuseStep 6747893 = 632615) (by norm_num)
theorem B4498595 : Blo 1997435 4498595 := bstep (se 1 (by rfl) ⟨3373946, by rfl⟩ : syracuseStep 4498595 = 6747893) B6747893
theorem B2999063 : Blo 1997435 2999063 := bstep (se 1 (by rfl) ⟨2249297, by rfl⟩ : syracuseStep 2999063 = 4498595) B4498595
theorem B1999375 : Blo 1997435 1999375 := bstep (se 1 (by rfl) ⟨1499531, by rfl⟩ : syracuseStep 1999375 = 2999063) B2999063
theorem B2999069 : Blo 1997435 2999069 := bbase (se 3 (by rfl) ⟨562325, by rfl⟩ : syracuseStep 2999069 = 1124651) (by norm_num)
theorem B1999379 : Blo 1997435 1999379 := bstep (se 1 (by rfl) ⟨1499534, by rfl⟩ : syracuseStep 1999379 = 2999069) B2999069
theorem B4498613 : Blo 1997435 4498613 := bbase (se 5 (by rfl) ⟨210872, by rfl⟩ : syracuseStep 4498613 = 421745) (by norm_num)
theorem B2999075 : Blo 1997435 2999075 := bstep (se 1 (by rfl) ⟨2249306, by rfl⟩ : syracuseStep 2999075 = 4498613) B4498613
theorem B1999383 : Blo 1997435 1999383 := bstep (se 1 (by rfl) ⟨1499537, by rfl⟩ : syracuseStep 1999383 = 2999075) B2999075
theorem B2135089 : Blo 1997435 2135089 := bbase (se 2 (by rfl) ⟨800658, by rfl⟩ : syracuseStep 2135089 = 1601317) (by norm_num)
theorem B11387141 : Blo 1997435 11387141 := bstep (se 4 (by rfl) ⟨1067544, by rfl⟩ : syracuseStep 11387141 = 2135089) B2135089
theorem B7591427 : Blo 1997435 7591427 := bstep (se 1 (by rfl) ⟨5693570, by rfl⟩ : syracuseStep 7591427 = 11387141) B11387141
theorem B5060951 : Blo 1997435 5060951 := bstep (se 1 (by rfl) ⟨3795713, by rfl⟩ : syracuseStep 5060951 = 7591427) B7591427
theorem B3373967 : Blo 1997435 3373967 := bstep (se 1 (by rfl) ⟨2530475, by rfl⟩ : syracuseStep 3373967 = 5060951) B5060951
theorem B2249311 : Blo 1997435 2249311 := bstep (se 1 (by rfl) ⟨1686983, by rfl⟩ : syracuseStep 2249311 = 3373967) B3373967
theorem B2999081 : Blo 1997435 2999081 := bstep (se 2 (by rfl) ⟨1124655, by rfl⟩ : syracuseStep 2999081 = 2249311) B2249311
theorem B1999387 : Blo 1997435 1999387 := bstep (se 1 (by rfl) ⟨1499540, by rfl⟩ : syracuseStep 1999387 = 2999081) B2999081
theorem B2135093 : Blo 1997435 2135093 := bbase (se 5 (by rfl) ⟨100082, by rfl⟩ : syracuseStep 2135093 = 200165) (by norm_num)
theorem B5693581 : Blo 1997435 5693581 := bstep (se 3 (by rfl) ⟨1067546, by rfl⟩ : syracuseStep 5693581 = 2135093) B2135093
theorem B7591441 : Blo 1997435 7591441 := bstep (se 2 (by rfl) ⟨2846790, by rfl⟩ : syracuseStep 7591441 = 5693581) B5693581
theorem B10121921 : Blo 1997435 10121921 := bstep (se 2 (by rfl) ⟨3795720, by rfl⟩ : syracuseStep 10121921 = 7591441) B7591441
theorem B6747947 : Blo 1997435 6747947 := bstep (se 1 (by rfl) ⟨5060960, by rfl⟩ : syracuseStep 6747947 = 10121921) B10121921
theorem B4498631 : Blo 1997435 4498631 := bstep (se 1 (by rfl) ⟨3373973, by rfl⟩ : syracuseStep 4498631 = 6747947) B6747947
theorem B2999087 : Blo 1997435 2999087 := bstep (se 1 (by rfl) ⟨2249315, by rfl⟩ : syracuseStep 2999087 = 4498631) B4498631
theorem B1999391 : Blo 1997435 1999391 := bstep (se 1 (by rfl) ⟨1499543, by rfl⟩ : syracuseStep 1999391 = 2999087) B2999087
theorem B2999093 : Blo 1997435 2999093 := bbase (se 5 (by rfl) ⟨140582, by rfl⟩ : syracuseStep 2999093 = 281165) (by norm_num)
theorem B1999395 : Blo 1997435 1999395 := bstep (se 1 (by rfl) ⟨1499546, by rfl⟩ : syracuseStep 1999395 = 2999093) B2999093
theorem B5060981 : Blo 1997435 5060981 := bbase (se 5 (by rfl) ⟨237233, by rfl⟩ : syracuseStep 5060981 = 474467) (by norm_num)
theorem B3373987 : Blo 1997435 3373987 := bstep (se 1 (by rfl) ⟨2530490, by rfl⟩ : syracuseStep 3373987 = 5060981) B5060981
theorem B4498649 : Blo 1997435 4498649 := bstep (se 2 (by rfl) ⟨1686993, by rfl⟩ : syracuseStep 4498649 = 3373987) B3373987
theorem B2999099 : Blo 1997435 2999099 := bstep (se 1 (by rfl) ⟨2249324, by rfl⟩ : syracuseStep 2999099 = 4498649) B4498649
theorem B1999399 : Blo 1997435 1999399 := bstep (se 1 (by rfl) ⟨1499549, by rfl⟩ : syracuseStep 1999399 = 2999099) B2999099
theorem B2249329 : Blo 1997435 2249329 := bbase (se 2 (by rfl) ⟨843498, by rfl⟩ : syracuseStep 2249329 = 1686997) (by norm_num)
theorem B2999105 : Blo 1997435 2999105 := bstep (se 2 (by rfl) ⟨1124664, by rfl⟩ : syracuseStep 2999105 = 2249329) B2249329
theorem B1999403 : Blo 1997435 1999403 := bstep (se 1 (by rfl) ⟨1499552, by rfl⟩ : syracuseStep 1999403 = 2999105) B2999105
theorem B6492725 : Blo 1997435 6492725 := bbase (se 5 (by rfl) ⟨304346, by rfl⟩ : syracuseStep 6492725 = 608693) (by norm_num)
theorem B4328483 : Blo 1997435 4328483 := bstep (se 1 (by rfl) ⟨3246362, by rfl⟩ : syracuseStep 4328483 = 6492725) B6492725
theorem B11542621 : Blo 1997435 11542621 := bstep (se 3 (by rfl) ⟨2164241, by rfl⟩ : syracuseStep 11542621 = 4328483) B4328483
theorem B15390161 : Blo 1997435 15390161 := bstep (se 2 (by rfl) ⟨5771310, by rfl⟩ : syracuseStep 15390161 = 11542621) B11542621
theorem B10260107 : Blo 1997435 10260107 := bstep (se 1 (by rfl) ⟨7695080, by rfl⟩ : syracuseStep 10260107 = 15390161) B15390161
theorem B6840071 : Blo 1997435 6840071 := bstep (se 1 (by rfl) ⟨5130053, by rfl⟩ : syracuseStep 6840071 = 10260107) B10260107
theorem B4560047 : Blo 1997435 4560047 := bstep (se 1 (by rfl) ⟨3420035, by rfl⟩ : syracuseStep 4560047 = 6840071) B6840071
theorem B3040031 : Blo 1997435 3040031 := bstep (se 1 (by rfl) ⟨2280023, by rfl⟩ : syracuseStep 3040031 = 4560047) B4560047
theorem B8106749 : Blo 1997435 8106749 := bstep (se 3 (by rfl) ⟨1520015, by rfl⟩ : syracuseStep 8106749 = 3040031) B3040031
theorem B5404499 : Blo 1997435 5404499 := bstep (se 1 (by rfl) ⟨4053374, by rfl⟩ : syracuseStep 5404499 = 8106749) B8106749
theorem B3602999 : Blo 1997435 3602999 := bstep (se 1 (by rfl) ⟨2702249, by rfl⟩ : syracuseStep 3602999 = 5404499) B5404499
theorem B9607997 : Blo 1997435 9607997 := bstep (se 3 (by rfl) ⟨1801499, by rfl⟩ : syracuseStep 9607997 = 3602999) B3602999
theorem B6405331 : Blo 1997435 6405331 := bstep (se 1 (by rfl) ⟨4803998, by rfl⟩ : syracuseStep 6405331 = 9607997) B9607997
theorem B8540441 : Blo 1997435 8540441 := bstep (se 2 (by rfl) ⟨3202665, by rfl⟩ : syracuseStep 8540441 = 6405331) B6405331
theorem B5693627 : Blo 1997435 5693627 := bstep (se 1 (by rfl) ⟨4270220, by rfl⟩ : syracuseStep 5693627 = 8540441) B8540441
theorem B3795751 : Blo 1997435 3795751 := bstep (se 1 (by rfl) ⟨2846813, by rfl⟩ : syracuseStep 3795751 = 5693627) B5693627
theorem B5061001 : Blo 1997435 5061001 := bstep (se 2 (by rfl) ⟨1897875, by rfl⟩ : syracuseStep 5061001 = 3795751) B3795751
theorem B6748001 : Blo 1997435 6748001 := bstep (se 2 (by rfl) ⟨2530500, by rfl⟩ : syracuseStep 6748001 = 5061001) B5061001
theorem B4498667 : Blo 1997435 4498667 := bstep (se 1 (by rfl) ⟨3374000, by rfl⟩ : syracuseStep 4498667 = 6748001) B6748001
theorem B2999111 : Blo 1997435 2999111 := bstep (se 1 (by rfl) ⟨2249333, by rfl⟩ : syracuseStep 2999111 = 4498667) B4498667
theorem B1999407 : Blo 1997435 1999407 := bstep (se 1 (by rfl) ⟨1499555, by rfl⟩ : syracuseStep 1999407 = 2999111) B2999111
theorem B2999117 : Blo 1997435 2999117 := bbase (se 3 (by rfl) ⟨562334, by rfl⟩ : syracuseStep 2999117 = 1124669) (by norm_num)
theorem B1999411 : Blo 1997435 1999411 := bstep (se 1 (by rfl) ⟨1499558, by rfl⟩ : syracuseStep 1999411 = 2999117) B2999117
theorem B4498685 : Blo 1997435 4498685 := bbase (se 3 (by rfl) ⟨843503, by rfl⟩ : syracuseStep 4498685 = 1687007) (by norm_num)
theorem B2999123 : Blo 1997435 2999123 := bstep (se 1 (by rfl) ⟨2249342, by rfl⟩ : syracuseStep 2999123 = 4498685) B4498685
theorem B1999415 : Blo 1997435 1999415 := bstep (se 1 (by rfl) ⟨1499561, by rfl⟩ : syracuseStep 1999415 = 2999123) B2999123
theorem B3374021 : Blo 1997435 3374021 := bbase (se 4 (by rfl) ⟨316314, by rfl⟩ : syracuseStep 3374021 = 632629) (by norm_num)
theorem B2249347 : Blo 1997435 2249347 := bstep (se 1 (by rfl) ⟨1687010, by rfl⟩ : syracuseStep 2249347 = 3374021) B3374021
theorem B2999129 : Blo 1997435 2999129 := bstep (se 2 (by rfl) ⟨1124673, by rfl⟩ : syracuseStep 2999129 = 2249347) B2249347
theorem B1999419 : Blo 1997435 1999419 := bstep (se 1 (by rfl) ⟨1499564, by rfl⟩ : syracuseStep 1999419 = 2999129) B2999129
theorem B15183125 : Blo 1997435 15183125 := bbase (se 6 (by rfl) ⟨355854, by rfl⟩ : syracuseStep 15183125 = 711709) (by norm_num)
theorem B10122083 : Blo 1997435 10122083 := bstep (se 1 (by rfl) ⟨7591562, by rfl⟩ : syracuseStep 10122083 = 15183125) B15183125
theorem B6748055 : Blo 1997435 6748055 := bstep (se 1 (by rfl) ⟨5061041, by rfl⟩ : syracuseStep 6748055 = 10122083) B10122083
theorem B4498703 : Blo 1997435 4498703 := bstep (se 1 (by rfl) ⟨3374027, by rfl⟩ : syracuseStep 4498703 = 6748055) B6748055
theorem B2999135 : Blo 1997435 2999135 := bstep (se 1 (by rfl) ⟨2249351, by rfl⟩ : syracuseStep 2999135 = 4498703) B4498703
theorem B1999423 : Blo 1997435 1999423 := bstep (se 1 (by rfl) ⟨1499567, by rfl⟩ : syracuseStep 1999423 = 2999135) B2999135
theorem B2999141 : Blo 1997435 2999141 := bbase (se 4 (by rfl) ⟨281169, by rfl⟩ : syracuseStep 2999141 = 562339) (by norm_num)
theorem B1999427 : Blo 1997435 1999427 := bstep (se 1 (by rfl) ⟨1499570, by rfl⟩ : syracuseStep 1999427 = 2999141) B2999141
theorem B3795797 : Blo 1997435 3795797 := bbase (se 9 (by rfl) ⟨11120, by rfl⟩ : syracuseStep 3795797 = 22241) (by norm_num)
theorem B2530531 : Blo 1997435 2530531 := bstep (se 1 (by rfl) ⟨1897898, by rfl⟩ : syracuseStep 2530531 = 3795797) B3795797
theorem B3374041 : Blo 1997435 3374041 := bstep (se 2 (by rfl) ⟨1265265, by rfl⟩ : syracuseStep 3374041 = 2530531) B2530531
theorem B4498721 : Blo 1997435 4498721 := bstep (se 2 (by rfl) ⟨1687020, by rfl⟩ : syracuseStep 4498721 = 3374041) B3374041
theorem B2999147 : Blo 1997435 2999147 := bstep (se 1 (by rfl) ⟨2249360, by rfl⟩ : syracuseStep 2999147 = 4498721) B4498721
theorem B1999431 : Blo 1997435 1999431 := bstep (se 1 (by rfl) ⟨1499573, by rfl⟩ : syracuseStep 1999431 = 2999147) B2999147
theorem B2249365 : Blo 1997435 2249365 := bbase (se 6 (by rfl) ⟨52719, by rfl⟩ : syracuseStep 2249365 = 105439) (by norm_num)
theorem B2999153 : Blo 1997435 2999153 := bstep (se 2 (by rfl) ⟨1124682, by rfl⟩ : syracuseStep 2999153 = 2249365) B2249365
theorem B1999435 : Blo 1997435 1999435 := bstep (se 1 (by rfl) ⟨1499576, by rfl⟩ : syracuseStep 1999435 = 2999153) B2999153
theorem C0 (j : ℕ) (h1 : 499358 ≤ j) (h2 : j ≤ 499858) : Blo 1997435 (4 * j + 3) := by
  interval_cases j
  · exact B1997435
  · exact B1997439
  · exact B1997443
  · exact B1997447
  · exact B1997451
  · exact B1997455
  · exact B1997459
  · exact B1997463
  · exact B1997467
  · exact B1997471
  · exact B1997475
  · exact B1997479
  · exact B1997483
  · exact B1997487
  · exact B1997491
  · exact B1997495
  · exact B1997499
  · exact B1997503
  · exact B1997507
  · exact B1997511
  · exact B1997515
  · exact B1997519
  · exact B1997523
  · exact B1997527
  · exact B1997531
  · exact B1997535
  · exact B1997539
  · exact B1997543
  · exact B1997547
  · exact B1997551
  · exact B1997555
  · exact B1997559
  · exact B1997563
  · exact B1997567
  · exact B1997571
  · exact B1997575
  · exact B1997579
  · exact B1997583
  · exact B1997587
  · exact B1997591
  · exact B1997595
  · exact B1997599
  · exact B1997603
  · exact B1997607
  · exact B1997611
  · exact B1997615
  · exact B1997619
  · exact B1997623
  · exact B1997627
  · exact B1997631
  · exact B1997635
  · exact B1997639
  · exact B1997643
  · exact B1997647
  · exact B1997651
  · exact B1997655
  · exact B1997659
  · exact B1997663
  · exact B1997667
  · exact B1997671
  · exact B1997675
  · exact B1997679
  · exact B1997683
  · exact B1997687
  · exact B1997691
  · exact B1997695
  · exact B1997699
  · exact B1997703
  · exact B1997707
  · exact B1997711
  · exact B1997715
  · exact B1997719
  · exact B1997723
  · exact B1997727
  · exact B1997731
  · exact B1997735
  · exact B1997739
  · exact B1997743
  · exact B1997747
  · exact B1997751
  · exact B1997755
  · exact B1997759
  · exact B1997763
  · exact B1997767
  · exact B1997771
  · exact B1997775
  · exact B1997779
  · exact B1997783
  · exact B1997787
  · exact B1997791
  · exact B1997795
  · exact B1997799
  · exact B1997803
  · exact B1997807
  · exact B1997811
  · exact B1997815
  · exact B1997819
  · exact B1997823
  · exact B1997827
  · exact B1997831
  · exact B1997835
  · exact B1997839
  · exact B1997843
  · exact B1997847
  · exact B1997851
  · exact B1997855
  · exact B1997859
  · exact B1997863
  · exact B1997867
  · exact B1997871
  · exact B1997875
  · exact B1997879
  · exact B1997883
  · exact B1997887
  · exact B1997891
  · exact B1997895
  · exact B1997899
  · exact B1997903
  · exact B1997907
  · exact B1997911
  · exact B1997915
  · exact B1997919
  · exact B1997923
  · exact B1997927
  · exact B1997931
  · exact B1997935
  · exact B1997939
  · exact B1997943
  · exact B1997947
  · exact B1997951
  · exact B1997955
  · exact B1997959
  · exact B1997963
  · exact B1997967
  · exact B1997971
  · exact B1997975
  · exact B1997979
  · exact B1997983
  · exact B1997987
  · exact B1997991
  · exact B1997995
  · exact B1997999
  · exact B1998003
  · exact B1998007
  · exact B1998011
  · exact B1998015
  · exact B1998019
  · exact B1998023
  · exact B1998027
  · exact B1998031
  · exact B1998035
  · exact B1998039
  · exact B1998043
  · exact B1998047
  · exact B1998051
  · exact B1998055
  · exact B1998059
  · exact B1998063
  · exact B1998067
  · exact B1998071
  · exact B1998075
  · exact B1998079
  · exact B1998083
  · exact B1998087
  · exact B1998091
  · exact B1998095
  · exact B1998099
  · exact B1998103
  · exact B1998107
  · exact B1998111
  · exact B1998115
  · exact B1998119
  · exact B1998123
  · exact B1998127
  · exact B1998131
  · exact B1998135
  · exact B1998139
  · exact B1998143
  · exact B1998147
  · exact B1998151
  · exact B1998155
  · exact B1998159
  · exact B1998163
  · exact B1998167
  · exact B1998171
  · exact B1998175
  · exact B1998179
  · exact B1998183
  · exact B1998187
  · exact B1998191
  · exact B1998195
  · exact B1998199
  · exact B1998203
  · exact B1998207
  · exact B1998211
  · exact B1998215
  · exact B1998219
  · exact B1998223
  · exact B1998227
  · exact B1998231
  · exact B1998235
  · exact B1998239
  · exact B1998243
  · exact B1998247
  · exact B1998251
  · exact B1998255
  · exact B1998259
  · exact B1998263
  · exact B1998267
  · exact B1998271
  · exact B1998275
  · exact B1998279
  · exact B1998283
  · exact B1998287
  · exact B1998291
  · exact B1998295
  · exact B1998299
  · exact B1998303
  · exact B1998307
  · exact B1998311
  · exact B1998315
  · exact B1998319
  · exact B1998323
  · exact B1998327
  · exact B1998331
  · exact B1998335
  · exact B1998339
  · exact B1998343
  · exact B1998347
  · exact B1998351
  · exact B1998355
  · exact B1998359
  · exact B1998363
  · exact B1998367
  · exact B1998371
  · exact B1998375
  · exact B1998379
  · exact B1998383
  · exact B1998387
  · exact B1998391
  · exact B1998395
  · exact B1998399
  · exact B1998403
  · exact B1998407
  · exact B1998411
  · exact B1998415
  · exact B1998419
  · exact B1998423
  · exact B1998427
  · exact B1998431
  · exact B1998435
  · exact B1998439
  · exact B1998443
  · exact B1998447
  · exact B1998451
  · exact B1998455
  · exact B1998459
  · exact B1998463
  · exact B1998467
  · exact B1998471
  · exact B1998475
  · exact B1998479
  · exact B1998483
  · exact B1998487
  · exact B1998491
  · exact B1998495
  · exact B1998499
  · exact B1998503
  · exact B1998507
  · exact B1998511
  · exact B1998515
  · exact B1998519
  · exact B1998523
  · exact B1998527
  · exact B1998531
  · exact B1998535
  · exact B1998539
  · exact B1998543
  · exact B1998547
  · exact B1998551
  · exact B1998555
  · exact B1998559
  · exact B1998563
  · exact B1998567
  · exact B1998571
  · exact B1998575
  · exact B1998579
  · exact B1998583
  · exact B1998587
  · exact B1998591
  · exact B1998595
  · exact B1998599
  · exact B1998603
  · exact B1998607
  · exact B1998611
  · exact B1998615
  · exact B1998619
  · exact B1998623
  · exact B1998627
  · exact B1998631
  · exact B1998635
  · exact B1998639
  · exact B1998643
  · exact B1998647
  · exact B1998651
  · exact B1998655
  · exact B1998659
  · exact B1998663
  · exact B1998667
  · exact B1998671
  · exact B1998675
  · exact B1998679
  · exact B1998683
  · exact B1998687
  · exact B1998691
  · exact B1998695
  · exact B1998699
  · exact B1998703
  · exact B1998707
  · exact B1998711
  · exact B1998715
  · exact B1998719
  · exact B1998723
  · exact B1998727
  · exact B1998731
  · exact B1998735
  · exact B1998739
  · exact B1998743
  · exact B1998747
  · exact B1998751
  · exact B1998755
  · exact B1998759
  · exact B1998763
  · exact B1998767
  · exact B1998771
  · exact B1998775
  · exact B1998779
  · exact B1998783
  · exact B1998787
  · exact B1998791
  · exact B1998795
  · exact B1998799
  · exact B1998803
  · exact B1998807
  · exact B1998811
  · exact B1998815
  · exact B1998819
  · exact B1998823
  · exact B1998827
  · exact B1998831
  · exact B1998835
  · exact B1998839
  · exact B1998843
  · exact B1998847
  · exact B1998851
  · exact B1998855
  · exact B1998859
  · exact B1998863
  · exact B1998867
  · exact B1998871
  · exact B1998875
  · exact B1998879
  · exact B1998883
  · exact B1998887
  · exact B1998891
  · exact B1998895
  · exact B1998899
  · exact B1998903
  · exact B1998907
  · exact B1998911
  · exact B1998915
  · exact B1998919
  · exact B1998923
  · exact B1998927
  · exact B1998931
  · exact B1998935
  · exact B1998939
  · exact B1998943
  · exact B1998947
  · exact B1998951
  · exact B1998955
  · exact B1998959
  · exact B1998963
  · exact B1998967
  · exact B1998971
  · exact B1998975
  · exact B1998979
  · exact B1998983
  · exact B1998987
  · exact B1998991
  · exact B1998995
  · exact B1998999
  · exact B1999003
  · exact B1999007
  · exact B1999011
  · exact B1999015
  · exact B1999019
  · exact B1999023
  · exact B1999027
  · exact B1999031
  · exact B1999035
  · exact B1999039
  · exact B1999043
  · exact B1999047
  · exact B1999051
  · exact B1999055
  · exact B1999059
  · exact B1999063
  · exact B1999067
  · exact B1999071
  · exact B1999075
  · exact B1999079
  · exact B1999083
  · exact B1999087
  · exact B1999091
  · exact B1999095
  · exact B1999099
  · exact B1999103
  · exact B1999107
  · exact B1999111
  · exact B1999115
  · exact B1999119
  · exact B1999123
  · exact B1999127
  · exact B1999131
  · exact B1999135
  · exact B1999139
  · exact B1999143
  · exact B1999147
  · exact B1999151
  · exact B1999155
  · exact B1999159
  · exact B1999163
  · exact B1999167
  · exact B1999171
  · exact B1999175
  · exact B1999179
  · exact B1999183
  · exact B1999187
  · exact B1999191
  · exact B1999195
  · exact B1999199
  · exact B1999203
  · exact B1999207
  · exact B1999211
  · exact B1999215
  · exact B1999219
  · exact B1999223
  · exact B1999227
  · exact B1999231
  · exact B1999235
  · exact B1999239
  · exact B1999243
  · exact B1999247
  · exact B1999251
  · exact B1999255
  · exact B1999259
  · exact B1999263
  · exact B1999267
  · exact B1999271
  · exact B1999275
  · exact B1999279
  · exact B1999283
  · exact B1999287
  · exact B1999291
  · exact B1999295
  · exact B1999299
  · exact B1999303
  · exact B1999307
  · exact B1999311
  · exact B1999315
  · exact B1999319
  · exact B1999323
  · exact B1999327
  · exact B1999331
  · exact B1999335
  · exact B1999339
  · exact B1999343
  · exact B1999347
  · exact B1999351
  · exact B1999355
  · exact B1999359
  · exact B1999363
  · exact B1999367
  · exact B1999371
  · exact B1999375
  · exact B1999379
  · exact B1999383
  · exact B1999387
  · exact B1999391
  · exact B1999395
  · exact B1999399
  · exact B1999403
  · exact B1999407
  · exact B1999411
  · exact B1999415
  · exact B1999419
  · exact B1999423
  · exact B1999427
  · exact B1999431
  · exact B1999435
theorem solution (m : ℕ) (hlo : 1997435 ≤ m) (hhi : m ≤ 1999435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 499358 ≤ j := by omega
    have hj2 : j ≤ 499858 := by omega
    have hb : Blo 1997435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
