-- Prove2me | solution 1 for syracuse_descends_range_1973435_1975435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:48:05.214316+00:00
-- url     : https://prove2.me/submissions/3e385047-d442-4263-a4ce-1025b61831f1

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

theorem B3330173 : Blo 1973435 3330173 := bbase (se 3 (by rfl) ⟨624407, by rfl⟩ : syracuseStep 3330173 = 1248815) (by norm_num)
theorem B2220115 : Blo 1973435 2220115 := bstep (se 1 (by rfl) ⟨1665086, by rfl⟩ : syracuseStep 2220115 = 3330173) B3330173
theorem B2960153 : Blo 1973435 2960153 := bstep (se 2 (by rfl) ⟨1110057, by rfl⟩ : syracuseStep 2960153 = 2220115) B2220115
theorem B1973435 : Blo 1973435 1973435 := bstep (se 1 (by rfl) ⟨1480076, by rfl⟩ : syracuseStep 1973435 = 2960153) B2960153
theorem B4500821 : Blo 1973435 4500821 := bbase (se 11 (by rfl) ⟨3296, by rfl⟩ : syracuseStep 4500821 = 6593) (by norm_num)
theorem B3000547 : Blo 1973435 3000547 := bstep (se 1 (by rfl) ⟨2250410, by rfl⟩ : syracuseStep 3000547 = 4500821) B4500821
theorem B16002917 : Blo 1973435 16002917 := bstep (se 4 (by rfl) ⟨1500273, by rfl⟩ : syracuseStep 16002917 = 3000547) B3000547
theorem B10668611 : Blo 1973435 10668611 := bstep (se 1 (by rfl) ⟨8001458, by rfl⟩ : syracuseStep 10668611 = 16002917) B16002917
theorem B7112407 : Blo 1973435 7112407 := bstep (se 1 (by rfl) ⟨5334305, by rfl⟩ : syracuseStep 7112407 = 10668611) B10668611
theorem B9483209 : Blo 1973435 9483209 := bstep (se 2 (by rfl) ⟨3556203, by rfl⟩ : syracuseStep 9483209 = 7112407) B7112407
theorem B6322139 : Blo 1973435 6322139 := bstep (se 1 (by rfl) ⟨4741604, by rfl⟩ : syracuseStep 6322139 = 9483209) B9483209
theorem B4214759 : Blo 1973435 4214759 := bstep (se 1 (by rfl) ⟨3161069, by rfl⟩ : syracuseStep 4214759 = 6322139) B6322139
theorem B11239357 : Blo 1973435 11239357 := bstep (se 3 (by rfl) ⟨2107379, by rfl⟩ : syracuseStep 11239357 = 4214759) B4214759
theorem B14985809 : Blo 1973435 14985809 := bstep (se 2 (by rfl) ⟨5619678, by rfl⟩ : syracuseStep 14985809 = 11239357) B11239357
theorem B9990539 : Blo 1973435 9990539 := bstep (se 1 (by rfl) ⟨7492904, by rfl⟩ : syracuseStep 9990539 = 14985809) B14985809
theorem B6660359 : Blo 1973435 6660359 := bstep (se 1 (by rfl) ⟨4995269, by rfl⟩ : syracuseStep 6660359 = 9990539) B9990539
theorem B4440239 : Blo 1973435 4440239 := bstep (se 1 (by rfl) ⟨3330179, by rfl⟩ : syracuseStep 4440239 = 6660359) B6660359
theorem B2960159 : Blo 1973435 2960159 := bstep (se 1 (by rfl) ⟨2220119, by rfl⟩ : syracuseStep 2960159 = 4440239) B4440239
theorem B1973439 : Blo 1973435 1973439 := bstep (se 1 (by rfl) ⟨1480079, by rfl⟩ : syracuseStep 1973439 = 2960159) B2960159
theorem B2960165 : Blo 1973435 2960165 := bbase (se 4 (by rfl) ⟨277515, by rfl⟩ : syracuseStep 2960165 = 555031) (by norm_num)
theorem B1973443 : Blo 1973435 1973443 := bstep (se 1 (by rfl) ⟨1480082, by rfl⟩ : syracuseStep 1973443 = 2960165) B2960165
theorem B2497645 : Blo 1973435 2497645 := bbase (se 3 (by rfl) ⟨468308, by rfl⟩ : syracuseStep 2497645 = 936617) (by norm_num)
theorem B3330193 : Blo 1973435 3330193 := bstep (se 2 (by rfl) ⟨1248822, by rfl⟩ : syracuseStep 3330193 = 2497645) B2497645
theorem B4440257 : Blo 1973435 4440257 := bstep (se 2 (by rfl) ⟨1665096, by rfl⟩ : syracuseStep 4440257 = 3330193) B3330193
theorem B2960171 : Blo 1973435 2960171 := bstep (se 1 (by rfl) ⟨2220128, by rfl⟩ : syracuseStep 2960171 = 4440257) B4440257
theorem B1973447 : Blo 1973435 1973447 := bstep (se 1 (by rfl) ⟨1480085, by rfl⟩ : syracuseStep 1973447 = 2960171) B2960171
theorem B2220133 : Blo 1973435 2220133 := bbase (se 4 (by rfl) ⟨208137, by rfl⟩ : syracuseStep 2220133 = 416275) (by norm_num)
theorem B2960177 : Blo 1973435 2960177 := bstep (se 2 (by rfl) ⟨1110066, by rfl⟩ : syracuseStep 2960177 = 2220133) B2220133
theorem B1973451 : Blo 1973435 1973451 := bstep (se 1 (by rfl) ⟨1480088, by rfl⟩ : syracuseStep 1973451 = 2960177) B2960177
theorem B2107397 : Blo 1973435 2107397 := bbase (se 4 (by rfl) ⟨197568, by rfl⟩ : syracuseStep 2107397 = 395137) (by norm_num)
theorem B5619725 : Blo 1973435 5619725 := bstep (se 3 (by rfl) ⟨1053698, by rfl⟩ : syracuseStep 5619725 = 2107397) B2107397
theorem B3746483 : Blo 1973435 3746483 := bstep (se 1 (by rfl) ⟨2809862, by rfl⟩ : syracuseStep 3746483 = 5619725) B5619725
theorem B2497655 : Blo 1973435 2497655 := bstep (se 1 (by rfl) ⟨1873241, by rfl⟩ : syracuseStep 2497655 = 3746483) B3746483
theorem B6660413 : Blo 1973435 6660413 := bstep (se 3 (by rfl) ⟨1248827, by rfl⟩ : syracuseStep 6660413 = 2497655) B2497655
theorem B4440275 : Blo 1973435 4440275 := bstep (se 1 (by rfl) ⟨3330206, by rfl⟩ : syracuseStep 4440275 = 6660413) B6660413
theorem B2960183 : Blo 1973435 2960183 := bstep (se 1 (by rfl) ⟨2220137, by rfl⟩ : syracuseStep 2960183 = 4440275) B4440275
theorem B1973455 : Blo 1973435 1973455 := bstep (se 1 (by rfl) ⟨1480091, by rfl⟩ : syracuseStep 1973455 = 2960183) B2960183
theorem B2960189 : Blo 1973435 2960189 := bbase (se 3 (by rfl) ⟨555035, by rfl⟩ : syracuseStep 2960189 = 1110071) (by norm_num)
theorem B1973459 : Blo 1973435 1973459 := bstep (se 1 (by rfl) ⟨1480094, by rfl⟩ : syracuseStep 1973459 = 2960189) B2960189
theorem B4440293 : Blo 1973435 4440293 := bbase (se 4 (by rfl) ⟨416277, by rfl⟩ : syracuseStep 4440293 = 832555) (by norm_num)
theorem B2960195 : Blo 1973435 2960195 := bstep (se 1 (by rfl) ⟨2220146, by rfl⟩ : syracuseStep 2960195 = 4440293) B4440293
theorem B1973463 : Blo 1973435 1973463 := bstep (se 1 (by rfl) ⟨1480097, by rfl⟩ : syracuseStep 1973463 = 2960195) B2960195
theorem B4995341 : Blo 1973435 4995341 := bbase (se 3 (by rfl) ⟨936626, by rfl⟩ : syracuseStep 4995341 = 1873253) (by norm_num)
theorem B3330227 : Blo 1973435 3330227 := bstep (se 1 (by rfl) ⟨2497670, by rfl⟩ : syracuseStep 3330227 = 4995341) B4995341
theorem B2220151 : Blo 1973435 2220151 := bstep (se 1 (by rfl) ⟨1665113, by rfl⟩ : syracuseStep 2220151 = 3330227) B3330227
theorem B2960201 : Blo 1973435 2960201 := bstep (se 2 (by rfl) ⟨1110075, by rfl⟩ : syracuseStep 2960201 = 2220151) B2220151
theorem B1973467 : Blo 1973435 1973467 := bstep (se 1 (by rfl) ⟨1480100, by rfl⟩ : syracuseStep 1973467 = 2960201) B2960201
theorem B2809885 : Blo 1973435 2809885 := bbase (se 3 (by rfl) ⟨526853, by rfl⟩ : syracuseStep 2809885 = 1053707) (by norm_num)
theorem B3746513 : Blo 1973435 3746513 := bstep (se 2 (by rfl) ⟨1404942, by rfl⟩ : syracuseStep 3746513 = 2809885) B2809885
theorem B9990701 : Blo 1973435 9990701 := bstep (se 3 (by rfl) ⟨1873256, by rfl⟩ : syracuseStep 9990701 = 3746513) B3746513
theorem B6660467 : Blo 1973435 6660467 := bstep (se 1 (by rfl) ⟨4995350, by rfl⟩ : syracuseStep 6660467 = 9990701) B9990701
theorem B4440311 : Blo 1973435 4440311 := bstep (se 1 (by rfl) ⟨3330233, by rfl⟩ : syracuseStep 4440311 = 6660467) B6660467
theorem B2960207 : Blo 1973435 2960207 := bstep (se 1 (by rfl) ⟨2220155, by rfl⟩ : syracuseStep 2960207 = 4440311) B4440311
theorem B1973471 : Blo 1973435 1973471 := bstep (se 1 (by rfl) ⟨1480103, by rfl⟩ : syracuseStep 1973471 = 2960207) B2960207
theorem B2960213 : Blo 1973435 2960213 := bbase (se 9 (by rfl) ⟨8672, by rfl⟩ : syracuseStep 2960213 = 17345) (by norm_num)
theorem B1973475 : Blo 1973435 1973475 := bstep (se 1 (by rfl) ⟨1480106, by rfl⟩ : syracuseStep 1973475 = 2960213) B2960213
theorem B4214845 : Blo 1973435 4214845 := bbase (se 3 (by rfl) ⟨790283, by rfl⟩ : syracuseStep 4214845 = 1580567) (by norm_num)
theorem B5619793 : Blo 1973435 5619793 := bstep (se 2 (by rfl) ⟨2107422, by rfl⟩ : syracuseStep 5619793 = 4214845) B4214845
theorem B7493057 : Blo 1973435 7493057 := bstep (se 2 (by rfl) ⟨2809896, by rfl⟩ : syracuseStep 7493057 = 5619793) B5619793
theorem B4995371 : Blo 1973435 4995371 := bstep (se 1 (by rfl) ⟨3746528, by rfl⟩ : syracuseStep 4995371 = 7493057) B7493057
theorem B3330247 : Blo 1973435 3330247 := bstep (se 1 (by rfl) ⟨2497685, by rfl⟩ : syracuseStep 3330247 = 4995371) B4995371
theorem B4440329 : Blo 1973435 4440329 := bstep (se 2 (by rfl) ⟨1665123, by rfl⟩ : syracuseStep 4440329 = 3330247) B3330247
theorem B2960219 : Blo 1973435 2960219 := bstep (se 1 (by rfl) ⟨2220164, by rfl⟩ : syracuseStep 2960219 = 4440329) B4440329
theorem B1973479 : Blo 1973435 1973479 := bstep (se 1 (by rfl) ⟨1480109, by rfl⟩ : syracuseStep 1973479 = 2960219) B2960219
theorem B2220169 : Blo 1973435 2220169 := bbase (se 2 (by rfl) ⟨832563, by rfl⟩ : syracuseStep 2220169 = 1665127) (by norm_num)
theorem B2960225 : Blo 1973435 2960225 := bstep (se 2 (by rfl) ⟨1110084, by rfl⟩ : syracuseStep 2960225 = 2220169) B2220169
theorem B1973483 : Blo 1973435 1973483 := bstep (se 1 (by rfl) ⟨1480112, by rfl⟩ : syracuseStep 1973483 = 2960225) B2960225
theorem B2531773 : Blo 1973435 2531773 := bbase (se 3 (by rfl) ⟨474707, by rfl⟩ : syracuseStep 2531773 = 949415) (by norm_num)
theorem B13502789 : Blo 1973435 13502789 := bstep (se 4 (by rfl) ⟨1265886, by rfl⟩ : syracuseStep 13502789 = 2531773) B2531773
theorem B9001859 : Blo 1973435 9001859 := bstep (se 1 (by rfl) ⟨6751394, by rfl⟩ : syracuseStep 9001859 = 13502789) B13502789
theorem B24004957 : Blo 1973435 24004957 := bstep (se 3 (by rfl) ⟨4500929, by rfl⟩ : syracuseStep 24004957 = 9001859) B9001859
theorem B32006609 : Blo 1973435 32006609 := bstep (se 2 (by rfl) ⟨12002478, by rfl⟩ : syracuseStep 32006609 = 24004957) B24004957
theorem B21337739 : Blo 1973435 21337739 := bstep (se 1 (by rfl) ⟨16003304, by rfl⟩ : syracuseStep 21337739 = 32006609) B32006609
theorem B14225159 : Blo 1973435 14225159 := bstep (se 1 (by rfl) ⟨10668869, by rfl⟩ : syracuseStep 14225159 = 21337739) B21337739
theorem B37933757 : Blo 1973435 37933757 := bstep (se 3 (by rfl) ⟨7112579, by rfl⟩ : syracuseStep 37933757 = 14225159) B14225159
theorem B25289171 : Blo 1973435 25289171 := bstep (se 1 (by rfl) ⟨18966878, by rfl⟩ : syracuseStep 25289171 = 37933757) B37933757
theorem B16859447 : Blo 1973435 16859447 := bstep (se 1 (by rfl) ⟨12644585, by rfl⟩ : syracuseStep 16859447 = 25289171) B25289171
theorem B11239631 : Blo 1973435 11239631 := bstep (se 1 (by rfl) ⟨8429723, by rfl⟩ : syracuseStep 11239631 = 16859447) B16859447
theorem B7493087 : Blo 1973435 7493087 := bstep (se 1 (by rfl) ⟨5619815, by rfl⟩ : syracuseStep 7493087 = 11239631) B11239631
theorem B4995391 : Blo 1973435 4995391 := bstep (se 1 (by rfl) ⟨3746543, by rfl⟩ : syracuseStep 4995391 = 7493087) B7493087
theorem B6660521 : Blo 1973435 6660521 := bstep (se 2 (by rfl) ⟨2497695, by rfl⟩ : syracuseStep 6660521 = 4995391) B4995391
theorem B4440347 : Blo 1973435 4440347 := bstep (se 1 (by rfl) ⟨3330260, by rfl⟩ : syracuseStep 4440347 = 6660521) B6660521
theorem B2960231 : Blo 1973435 2960231 := bstep (se 1 (by rfl) ⟨2220173, by rfl⟩ : syracuseStep 2960231 = 4440347) B4440347
theorem B1973487 : Blo 1973435 1973487 := bstep (se 1 (by rfl) ⟨1480115, by rfl⟩ : syracuseStep 1973487 = 2960231) B2960231
theorem B2960237 : Blo 1973435 2960237 := bbase (se 3 (by rfl) ⟨555044, by rfl⟩ : syracuseStep 2960237 = 1110089) (by norm_num)
theorem B1973491 : Blo 1973435 1973491 := bstep (se 1 (by rfl) ⟨1480118, by rfl⟩ : syracuseStep 1973491 = 2960237) B2960237
theorem B4440365 : Blo 1973435 4440365 := bbase (se 3 (by rfl) ⟨832568, by rfl⟩ : syracuseStep 4440365 = 1665137) (by norm_num)
theorem B2960243 : Blo 1973435 2960243 := bstep (se 1 (by rfl) ⟨2220182, by rfl⟩ : syracuseStep 2960243 = 4440365) B4440365
theorem B1973495 : Blo 1973435 1973495 := bstep (se 1 (by rfl) ⟨1480121, by rfl⟩ : syracuseStep 1973495 = 2960243) B2960243
theorem B4000853 : Blo 1973435 4000853 := bbase (se 8 (by rfl) ⟨23442, by rfl⟩ : syracuseStep 4000853 = 46885) (by norm_num)
theorem B2667235 : Blo 1973435 2667235 := bstep (se 1 (by rfl) ⟨2000426, by rfl⟩ : syracuseStep 2667235 = 4000853) B4000853
theorem B3556313 : Blo 1973435 3556313 := bstep (se 2 (by rfl) ⟨1333617, by rfl⟩ : syracuseStep 3556313 = 2667235) B2667235
theorem B2370875 : Blo 1973435 2370875 := bstep (se 1 (by rfl) ⟨1778156, by rfl⟩ : syracuseStep 2370875 = 3556313) B3556313
theorem B6322333 : Blo 1973435 6322333 := bstep (se 3 (by rfl) ⟨1185437, by rfl⟩ : syracuseStep 6322333 = 2370875) B2370875
theorem B8429777 : Blo 1973435 8429777 := bstep (se 2 (by rfl) ⟨3161166, by rfl⟩ : syracuseStep 8429777 = 6322333) B6322333
theorem B5619851 : Blo 1973435 5619851 := bstep (se 1 (by rfl) ⟨4214888, by rfl⟩ : syracuseStep 5619851 = 8429777) B8429777
theorem B3746567 : Blo 1973435 3746567 := bstep (se 1 (by rfl) ⟨2809925, by rfl⟩ : syracuseStep 3746567 = 5619851) B5619851
theorem B2497711 : Blo 1973435 2497711 := bstep (se 1 (by rfl) ⟨1873283, by rfl⟩ : syracuseStep 2497711 = 3746567) B3746567
theorem B3330281 : Blo 1973435 3330281 := bstep (se 2 (by rfl) ⟨1248855, by rfl⟩ : syracuseStep 3330281 = 2497711) B2497711
theorem B2220187 : Blo 1973435 2220187 := bstep (se 1 (by rfl) ⟨1665140, by rfl⟩ : syracuseStep 2220187 = 3330281) B3330281
theorem B2960249 : Blo 1973435 2960249 := bstep (se 2 (by rfl) ⟨1110093, by rfl⟩ : syracuseStep 2960249 = 2220187) B2220187
theorem B1973499 : Blo 1973435 1973499 := bstep (se 1 (by rfl) ⟨1480124, by rfl⟩ : syracuseStep 1973499 = 2960249) B2960249
theorem B40508693 : Blo 1973435 40508693 := bbase (se 6 (by rfl) ⟨949422, by rfl⟩ : syracuseStep 40508693 = 1898845) (by norm_num)
theorem B27005795 : Blo 1973435 27005795 := bstep (se 1 (by rfl) ⟨20254346, by rfl⟩ : syracuseStep 27005795 = 40508693) B40508693
theorem B18003863 : Blo 1973435 18003863 := bstep (se 1 (by rfl) ⟨13502897, by rfl⟩ : syracuseStep 18003863 = 27005795) B27005795
theorem B12002575 : Blo 1973435 12002575 := bstep (se 1 (by rfl) ⟨9001931, by rfl⟩ : syracuseStep 12002575 = 18003863) B18003863
theorem B16003433 : Blo 1973435 16003433 := bstep (se 2 (by rfl) ⟨6001287, by rfl⟩ : syracuseStep 16003433 = 12002575) B12002575
theorem B42675821 : Blo 1973435 42675821 := bstep (se 3 (by rfl) ⟨8001716, by rfl⟩ : syracuseStep 42675821 = 16003433) B16003433
theorem B28450547 : Blo 1973435 28450547 := bstep (se 1 (by rfl) ⟨21337910, by rfl⟩ : syracuseStep 28450547 = 42675821) B42675821
theorem B18967031 : Blo 1973435 18967031 := bstep (se 1 (by rfl) ⟨14225273, by rfl⟩ : syracuseStep 18967031 = 28450547) B28450547
theorem B12644687 : Blo 1973435 12644687 := bstep (se 1 (by rfl) ⟨9483515, by rfl⟩ : syracuseStep 12644687 = 18967031) B18967031
theorem B33719165 : Blo 1973435 33719165 := bstep (se 3 (by rfl) ⟨6322343, by rfl⟩ : syracuseStep 33719165 = 12644687) B12644687
theorem B22479443 : Blo 1973435 22479443 := bstep (se 1 (by rfl) ⟨16859582, by rfl⟩ : syracuseStep 22479443 = 33719165) B33719165
theorem B14986295 : Blo 1973435 14986295 := bstep (se 1 (by rfl) ⟨11239721, by rfl⟩ : syracuseStep 14986295 = 22479443) B22479443
theorem B9990863 : Blo 1973435 9990863 := bstep (se 1 (by rfl) ⟨7493147, by rfl⟩ : syracuseStep 9990863 = 14986295) B14986295
theorem B6660575 : Blo 1973435 6660575 := bstep (se 1 (by rfl) ⟨4995431, by rfl⟩ : syracuseStep 6660575 = 9990863) B9990863
theorem B4440383 : Blo 1973435 4440383 := bstep (se 1 (by rfl) ⟨3330287, by rfl⟩ : syracuseStep 4440383 = 6660575) B6660575
theorem B2960255 : Blo 1973435 2960255 := bstep (se 1 (by rfl) ⟨2220191, by rfl⟩ : syracuseStep 2960255 = 4440383) B4440383
theorem B1973503 : Blo 1973435 1973503 := bstep (se 1 (by rfl) ⟨1480127, by rfl⟩ : syracuseStep 1973503 = 2960255) B2960255
theorem B2960261 : Blo 1973435 2960261 := bbase (se 4 (by rfl) ⟨277524, by rfl⟩ : syracuseStep 2960261 = 555049) (by norm_num)
theorem B1973507 : Blo 1973435 1973507 := bstep (se 1 (by rfl) ⟨1480130, by rfl⟩ : syracuseStep 1973507 = 2960261) B2960261
theorem B3330301 : Blo 1973435 3330301 := bbase (se 3 (by rfl) ⟨624431, by rfl⟩ : syracuseStep 3330301 = 1248863) (by norm_num)
theorem B4440401 : Blo 1973435 4440401 := bstep (se 2 (by rfl) ⟨1665150, by rfl⟩ : syracuseStep 4440401 = 3330301) B3330301
theorem B2960267 : Blo 1973435 2960267 := bstep (se 1 (by rfl) ⟨2220200, by rfl⟩ : syracuseStep 2960267 = 4440401) B4440401
theorem B1973511 : Blo 1973435 1973511 := bstep (se 1 (by rfl) ⟨1480133, by rfl⟩ : syracuseStep 1973511 = 2960267) B2960267
theorem B2220205 : Blo 1973435 2220205 := bbase (se 3 (by rfl) ⟨416288, by rfl⟩ : syracuseStep 2220205 = 832577) (by norm_num)
theorem B2960273 : Blo 1973435 2960273 := bstep (se 2 (by rfl) ⟨1110102, by rfl⟩ : syracuseStep 2960273 = 2220205) B2220205
theorem B1973515 : Blo 1973435 1973515 := bstep (se 1 (by rfl) ⟨1480136, by rfl⟩ : syracuseStep 1973515 = 2960273) B2960273
theorem B6660629 : Blo 1973435 6660629 := bbase (se 6 (by rfl) ⟨156108, by rfl⟩ : syracuseStep 6660629 = 312217) (by norm_num)
theorem B4440419 : Blo 1973435 4440419 := bstep (se 1 (by rfl) ⟨3330314, by rfl⟩ : syracuseStep 4440419 = 6660629) B6660629
theorem B2960279 : Blo 1973435 2960279 := bstep (se 1 (by rfl) ⟨2220209, by rfl⟩ : syracuseStep 2960279 = 4440419) B4440419
theorem B1973519 : Blo 1973435 1973519 := bstep (se 1 (by rfl) ⟨1480139, by rfl⟩ : syracuseStep 1973519 = 2960279) B2960279
theorem B2960285 : Blo 1973435 2960285 := bbase (se 3 (by rfl) ⟨555053, by rfl⟩ : syracuseStep 2960285 = 1110107) (by norm_num)
theorem B1973523 : Blo 1973435 1973523 := bstep (se 1 (by rfl) ⟨1480142, by rfl⟩ : syracuseStep 1973523 = 2960285) B2960285
theorem B4440437 : Blo 1973435 4440437 := bbase (se 5 (by rfl) ⟨208145, by rfl⟩ : syracuseStep 4440437 = 416291) (by norm_num)
theorem B2960291 : Blo 1973435 2960291 := bstep (se 1 (by rfl) ⟨2220218, by rfl⟩ : syracuseStep 2960291 = 4440437) B4440437
theorem B1973527 : Blo 1973435 1973527 := bstep (se 1 (by rfl) ⟨1480145, by rfl⟩ : syracuseStep 1973527 = 2960291) B2960291
theorem B2370913 : Blo 1973435 2370913 := bbase (se 2 (by rfl) ⟨889092, by rfl⟩ : syracuseStep 2370913 = 1778185) (by norm_num)
theorem B12644869 : Blo 1973435 12644869 := bstep (se 4 (by rfl) ⟨1185456, by rfl⟩ : syracuseStep 12644869 = 2370913) B2370913
theorem B16859825 : Blo 1973435 16859825 := bstep (se 2 (by rfl) ⟨6322434, by rfl⟩ : syracuseStep 16859825 = 12644869) B12644869
theorem B11239883 : Blo 1973435 11239883 := bstep (se 1 (by rfl) ⟨8429912, by rfl⟩ : syracuseStep 11239883 = 16859825) B16859825
theorem B7493255 : Blo 1973435 7493255 := bstep (se 1 (by rfl) ⟨5619941, by rfl⟩ : syracuseStep 7493255 = 11239883) B11239883
theorem B4995503 : Blo 1973435 4995503 := bstep (se 1 (by rfl) ⟨3746627, by rfl⟩ : syracuseStep 4995503 = 7493255) B7493255
theorem B3330335 : Blo 1973435 3330335 := bstep (se 1 (by rfl) ⟨2497751, by rfl⟩ : syracuseStep 3330335 = 4995503) B4995503
theorem B2220223 : Blo 1973435 2220223 := bstep (se 1 (by rfl) ⟨1665167, by rfl⟩ : syracuseStep 2220223 = 3330335) B3330335
theorem B2960297 : Blo 1973435 2960297 := bstep (se 2 (by rfl) ⟨1110111, by rfl⟩ : syracuseStep 2960297 = 2220223) B2220223
theorem B1973531 : Blo 1973435 1973531 := bstep (se 1 (by rfl) ⟨1480148, by rfl⟩ : syracuseStep 1973531 = 2960297) B2960297
theorem B7493269 : Blo 1973435 7493269 := bbase (se 6 (by rfl) ⟨175623, by rfl⟩ : syracuseStep 7493269 = 351247) (by norm_num)
theorem B9991025 : Blo 1973435 9991025 := bstep (se 2 (by rfl) ⟨3746634, by rfl⟩ : syracuseStep 9991025 = 7493269) B7493269
theorem B6660683 : Blo 1973435 6660683 := bstep (se 1 (by rfl) ⟨4995512, by rfl⟩ : syracuseStep 6660683 = 9991025) B9991025
theorem B4440455 : Blo 1973435 4440455 := bstep (se 1 (by rfl) ⟨3330341, by rfl⟩ : syracuseStep 4440455 = 6660683) B6660683
theorem B2960303 : Blo 1973435 2960303 := bstep (se 1 (by rfl) ⟨2220227, by rfl⟩ : syracuseStep 2960303 = 4440455) B4440455
theorem B1973535 : Blo 1973435 1973535 := bstep (se 1 (by rfl) ⟨1480151, by rfl⟩ : syracuseStep 1973535 = 2960303) B2960303
theorem B2960309 : Blo 1973435 2960309 := bbase (se 5 (by rfl) ⟨138764, by rfl⟩ : syracuseStep 2960309 = 277529) (by norm_num)
theorem B1973539 : Blo 1973435 1973539 := bstep (se 1 (by rfl) ⟨1480154, by rfl⟩ : syracuseStep 1973539 = 2960309) B2960309
theorem B4995533 : Blo 1973435 4995533 := bbase (se 3 (by rfl) ⟨936662, by rfl⟩ : syracuseStep 4995533 = 1873325) (by norm_num)
theorem B3330355 : Blo 1973435 3330355 := bstep (se 1 (by rfl) ⟨2497766, by rfl⟩ : syracuseStep 3330355 = 4995533) B4995533
theorem B4440473 : Blo 1973435 4440473 := bstep (se 2 (by rfl) ⟨1665177, by rfl⟩ : syracuseStep 4440473 = 3330355) B3330355
theorem B2960315 : Blo 1973435 2960315 := bstep (se 1 (by rfl) ⟨2220236, by rfl⟩ : syracuseStep 2960315 = 4440473) B4440473
theorem B1973543 : Blo 1973435 1973543 := bstep (se 1 (by rfl) ⟨1480157, by rfl⟩ : syracuseStep 1973543 = 2960315) B2960315
theorem B2220241 : Blo 1973435 2220241 := bbase (se 2 (by rfl) ⟨832590, by rfl⟩ : syracuseStep 2220241 = 1665181) (by norm_num)
theorem B2960321 : Blo 1973435 2960321 := bstep (se 2 (by rfl) ⟨1110120, by rfl⟩ : syracuseStep 2960321 = 2220241) B2220241
theorem B1973547 : Blo 1973435 1973547 := bstep (se 1 (by rfl) ⟨1480160, by rfl⟩ : syracuseStep 1973547 = 2960321) B2960321
theorem B9483749 : Blo 1973435 9483749 := bbase (se 4 (by rfl) ⟨889101, by rfl⟩ : syracuseStep 9483749 = 1778203) (by norm_num)
theorem B6322499 : Blo 1973435 6322499 := bstep (se 1 (by rfl) ⟨4741874, by rfl⟩ : syracuseStep 6322499 = 9483749) B9483749
theorem B4214999 : Blo 1973435 4214999 := bstep (se 1 (by rfl) ⟨3161249, by rfl⟩ : syracuseStep 4214999 = 6322499) B6322499
theorem B2809999 : Blo 1973435 2809999 := bstep (se 1 (by rfl) ⟨2107499, by rfl⟩ : syracuseStep 2809999 = 4214999) B4214999
theorem B3746665 : Blo 1973435 3746665 := bstep (se 2 (by rfl) ⟨1404999, by rfl⟩ : syracuseStep 3746665 = 2809999) B2809999
theorem B4995553 : Blo 1973435 4995553 := bstep (se 2 (by rfl) ⟨1873332, by rfl⟩ : syracuseStep 4995553 = 3746665) B3746665
theorem B6660737 : Blo 1973435 6660737 := bstep (se 2 (by rfl) ⟨2497776, by rfl⟩ : syracuseStep 6660737 = 4995553) B4995553
theorem B4440491 : Blo 1973435 4440491 := bstep (se 1 (by rfl) ⟨3330368, by rfl⟩ : syracuseStep 4440491 = 6660737) B6660737
theorem B2960327 : Blo 1973435 2960327 := bstep (se 1 (by rfl) ⟨2220245, by rfl⟩ : syracuseStep 2960327 = 4440491) B4440491
theorem B1973551 : Blo 1973435 1973551 := bstep (se 1 (by rfl) ⟨1480163, by rfl⟩ : syracuseStep 1973551 = 2960327) B2960327
theorem B2960333 : Blo 1973435 2960333 := bbase (se 3 (by rfl) ⟨555062, by rfl⟩ : syracuseStep 2960333 = 1110125) (by norm_num)
theorem B1973555 : Blo 1973435 1973555 := bstep (se 1 (by rfl) ⟨1480166, by rfl⟩ : syracuseStep 1973555 = 2960333) B2960333
theorem B4440509 : Blo 1973435 4440509 := bbase (se 3 (by rfl) ⟨832595, by rfl⟩ : syracuseStep 4440509 = 1665191) (by norm_num)
theorem B2960339 : Blo 1973435 2960339 := bstep (se 1 (by rfl) ⟨2220254, by rfl⟩ : syracuseStep 2960339 = 4440509) B4440509
theorem B1973559 : Blo 1973435 1973559 := bstep (se 1 (by rfl) ⟨1480169, by rfl⟩ : syracuseStep 1973559 = 2960339) B2960339
theorem B3330389 : Blo 1973435 3330389 := bbase (se 10 (by rfl) ⟨4878, by rfl⟩ : syracuseStep 3330389 = 9757) (by norm_num)
theorem B2220259 : Blo 1973435 2220259 := bstep (se 1 (by rfl) ⟨1665194, by rfl⟩ : syracuseStep 2220259 = 3330389) B3330389
theorem B2960345 : Blo 1973435 2960345 := bstep (se 2 (by rfl) ⟨1110129, by rfl⟩ : syracuseStep 2960345 = 2220259) B2220259
theorem B1973563 : Blo 1973435 1973563 := bstep (se 1 (by rfl) ⟨1480172, by rfl⟩ : syracuseStep 1973563 = 2960345) B2960345
theorem B6322549 : Blo 1973435 6322549 := bbase (se 5 (by rfl) ⟨296369, by rfl⟩ : syracuseStep 6322549 = 592739) (by norm_num)
theorem B8430065 : Blo 1973435 8430065 := bstep (se 2 (by rfl) ⟨3161274, by rfl⟩ : syracuseStep 8430065 = 6322549) B6322549
theorem B5620043 : Blo 1973435 5620043 := bstep (se 1 (by rfl) ⟨4215032, by rfl⟩ : syracuseStep 5620043 = 8430065) B8430065
theorem B14986781 : Blo 1973435 14986781 := bstep (se 3 (by rfl) ⟨2810021, by rfl⟩ : syracuseStep 14986781 = 5620043) B5620043
theorem B9991187 : Blo 1973435 9991187 := bstep (se 1 (by rfl) ⟨7493390, by rfl⟩ : syracuseStep 9991187 = 14986781) B14986781
theorem B6660791 : Blo 1973435 6660791 := bstep (se 1 (by rfl) ⟨4995593, by rfl⟩ : syracuseStep 6660791 = 9991187) B9991187
theorem B4440527 : Blo 1973435 4440527 := bstep (se 1 (by rfl) ⟨3330395, by rfl⟩ : syracuseStep 4440527 = 6660791) B6660791
theorem B2960351 : Blo 1973435 2960351 := bstep (se 1 (by rfl) ⟨2220263, by rfl⟩ : syracuseStep 2960351 = 4440527) B4440527
theorem B1973567 : Blo 1973435 1973567 := bstep (se 1 (by rfl) ⟨1480175, by rfl⟩ : syracuseStep 1973567 = 2960351) B2960351
theorem B2960357 : Blo 1973435 2960357 := bbase (se 4 (by rfl) ⟨277533, by rfl⟩ : syracuseStep 2960357 = 555067) (by norm_num)
theorem B1973571 : Blo 1973435 1973571 := bstep (se 1 (by rfl) ⟨1480178, by rfl⟩ : syracuseStep 1973571 = 2960357) B2960357
theorem B8430101 : Blo 1973435 8430101 := bbase (se 6 (by rfl) ⟨197580, by rfl⟩ : syracuseStep 8430101 = 395161) (by norm_num)
theorem B5620067 : Blo 1973435 5620067 := bstep (se 1 (by rfl) ⟨4215050, by rfl⟩ : syracuseStep 5620067 = 8430101) B8430101
theorem B3746711 : Blo 1973435 3746711 := bstep (se 1 (by rfl) ⟨2810033, by rfl⟩ : syracuseStep 3746711 = 5620067) B5620067
theorem B2497807 : Blo 1973435 2497807 := bstep (se 1 (by rfl) ⟨1873355, by rfl⟩ : syracuseStep 2497807 = 3746711) B3746711
theorem B3330409 : Blo 1973435 3330409 := bstep (se 2 (by rfl) ⟨1248903, by rfl⟩ : syracuseStep 3330409 = 2497807) B2497807
theorem B4440545 : Blo 1973435 4440545 := bstep (se 2 (by rfl) ⟨1665204, by rfl⟩ : syracuseStep 4440545 = 3330409) B3330409
theorem B2960363 : Blo 1973435 2960363 := bstep (se 1 (by rfl) ⟨2220272, by rfl⟩ : syracuseStep 2960363 = 4440545) B4440545
theorem B1973575 : Blo 1973435 1973575 := bstep (se 1 (by rfl) ⟨1480181, by rfl⟩ : syracuseStep 1973575 = 2960363) B2960363
theorem B2220277 : Blo 1973435 2220277 := bbase (se 5 (by rfl) ⟨104075, by rfl⟩ : syracuseStep 2220277 = 208151) (by norm_num)
theorem B2960369 : Blo 1973435 2960369 := bstep (se 2 (by rfl) ⟨1110138, by rfl⟩ : syracuseStep 2960369 = 2220277) B2220277
theorem B1973579 : Blo 1973435 1973579 := bstep (se 1 (by rfl) ⟨1480184, by rfl⟩ : syracuseStep 1973579 = 2960369) B2960369
theorem B2497817 : Blo 1973435 2497817 := bbase (se 2 (by rfl) ⟨936681, by rfl⟩ : syracuseStep 2497817 = 1873363) (by norm_num)
theorem B6660845 : Blo 1973435 6660845 := bstep (se 3 (by rfl) ⟨1248908, by rfl⟩ : syracuseStep 6660845 = 2497817) B2497817
theorem B4440563 : Blo 1973435 4440563 := bstep (se 1 (by rfl) ⟨3330422, by rfl⟩ : syracuseStep 4440563 = 6660845) B6660845
theorem B2960375 : Blo 1973435 2960375 := bstep (se 1 (by rfl) ⟨2220281, by rfl⟩ : syracuseStep 2960375 = 4440563) B4440563
theorem B1973583 : Blo 1973435 1973583 := bstep (se 1 (by rfl) ⟨1480187, by rfl⟩ : syracuseStep 1973583 = 2960375) B2960375
theorem B2960381 : Blo 1973435 2960381 := bbase (se 3 (by rfl) ⟨555071, by rfl⟩ : syracuseStep 2960381 = 1110143) (by norm_num)
theorem B1973587 : Blo 1973435 1973587 := bstep (se 1 (by rfl) ⟨1480190, by rfl⟩ : syracuseStep 1973587 = 2960381) B2960381
theorem B4440581 : Blo 1973435 4440581 := bbase (se 4 (by rfl) ⟨416304, by rfl⟩ : syracuseStep 4440581 = 832609) (by norm_num)
theorem B2960387 : Blo 1973435 2960387 := bstep (se 1 (by rfl) ⟨2220290, by rfl⟩ : syracuseStep 2960387 = 4440581) B4440581
theorem B1973591 : Blo 1973435 1973591 := bstep (se 1 (by rfl) ⟨1480193, by rfl⟩ : syracuseStep 1973591 = 2960387) B2960387
theorem B3746749 : Blo 1973435 3746749 := bbase (se 3 (by rfl) ⟨702515, by rfl⟩ : syracuseStep 3746749 = 1405031) (by norm_num)
theorem B4995665 : Blo 1973435 4995665 := bstep (se 2 (by rfl) ⟨1873374, by rfl⟩ : syracuseStep 4995665 = 3746749) B3746749
theorem B3330443 : Blo 1973435 3330443 := bstep (se 1 (by rfl) ⟨2497832, by rfl⟩ : syracuseStep 3330443 = 4995665) B4995665
theorem B2220295 : Blo 1973435 2220295 := bstep (se 1 (by rfl) ⟨1665221, by rfl⟩ : syracuseStep 2220295 = 3330443) B3330443
theorem B2960393 : Blo 1973435 2960393 := bstep (se 2 (by rfl) ⟨1110147, by rfl⟩ : syracuseStep 2960393 = 2220295) B2220295
theorem B1973595 : Blo 1973435 1973595 := bstep (se 1 (by rfl) ⟨1480196, by rfl⟩ : syracuseStep 1973595 = 2960393) B2960393
theorem B9991349 : Blo 1973435 9991349 := bbase (se 5 (by rfl) ⟨468344, by rfl⟩ : syracuseStep 9991349 = 936689) (by norm_num)
theorem B6660899 : Blo 1973435 6660899 := bstep (se 1 (by rfl) ⟨4995674, by rfl⟩ : syracuseStep 6660899 = 9991349) B9991349
theorem B4440599 : Blo 1973435 4440599 := bstep (se 1 (by rfl) ⟨3330449, by rfl⟩ : syracuseStep 4440599 = 6660899) B6660899
theorem B2960399 : Blo 1973435 2960399 := bstep (se 1 (by rfl) ⟨2220299, by rfl⟩ : syracuseStep 2960399 = 4440599) B4440599
theorem B1973599 : Blo 1973435 1973599 := bstep (se 1 (by rfl) ⟨1480199, by rfl⟩ : syracuseStep 1973599 = 2960399) B2960399
theorem B2960405 : Blo 1973435 2960405 := bbase (se 6 (by rfl) ⟨69384, by rfl⟩ : syracuseStep 2960405 = 138769) (by norm_num)
theorem B1973603 : Blo 1973435 1973603 := bstep (se 1 (by rfl) ⟨1480202, by rfl⟩ : syracuseStep 1973603 = 2960405) B2960405
theorem B2403353 : Blo 1973435 2403353 := bbase (se 2 (by rfl) ⟨901257, by rfl⟩ : syracuseStep 2403353 = 1802515) (by norm_num)
theorem B6408941 : Blo 1973435 6408941 := bstep (se 3 (by rfl) ⟨1201676, by rfl⟩ : syracuseStep 6408941 = 2403353) B2403353
theorem B17090509 : Blo 1973435 17090509 := bstep (se 3 (by rfl) ⟨3204470, by rfl⟩ : syracuseStep 17090509 = 6408941) B6408941
theorem B22787345 : Blo 1973435 22787345 := bstep (se 2 (by rfl) ⟨8545254, by rfl⟩ : syracuseStep 22787345 = 17090509) B17090509
theorem B15191563 : Blo 1973435 15191563 := bstep (se 1 (by rfl) ⟨11393672, by rfl⟩ : syracuseStep 15191563 = 22787345) B22787345
theorem B20255417 : Blo 1973435 20255417 := bstep (se 2 (by rfl) ⟨7595781, by rfl⟩ : syracuseStep 20255417 = 15191563) B15191563
theorem B13503611 : Blo 1973435 13503611 := bstep (se 1 (by rfl) ⟨10127708, by rfl⟩ : syracuseStep 13503611 = 20255417) B20255417
theorem B36009629 : Blo 1973435 36009629 := bstep (se 3 (by rfl) ⟨6751805, by rfl⟩ : syracuseStep 36009629 = 13503611) B13503611
theorem B24006419 : Blo 1973435 24006419 := bstep (se 1 (by rfl) ⟨18004814, by rfl⟩ : syracuseStep 24006419 = 36009629) B36009629
theorem B16004279 : Blo 1973435 16004279 := bstep (se 1 (by rfl) ⟨12003209, by rfl⟩ : syracuseStep 16004279 = 24006419) B24006419
theorem B10669519 : Blo 1973435 10669519 := bstep (se 1 (by rfl) ⟨8002139, by rfl⟩ : syracuseStep 10669519 = 16004279) B16004279
theorem B14226025 : Blo 1973435 14226025 := bstep (se 2 (by rfl) ⟨5334759, by rfl⟩ : syracuseStep 14226025 = 10669519) B10669519
theorem B18968033 : Blo 1973435 18968033 := bstep (se 2 (by rfl) ⟨7113012, by rfl⟩ : syracuseStep 18968033 = 14226025) B14226025
theorem B12645355 : Blo 1973435 12645355 := bstep (se 1 (by rfl) ⟨9484016, by rfl⟩ : syracuseStep 12645355 = 18968033) B18968033
theorem B16860473 : Blo 1973435 16860473 := bstep (se 2 (by rfl) ⟨6322677, by rfl⟩ : syracuseStep 16860473 = 12645355) B12645355
theorem B11240315 : Blo 1973435 11240315 := bstep (se 1 (by rfl) ⟨8430236, by rfl⟩ : syracuseStep 11240315 = 16860473) B16860473
theorem B7493543 : Blo 1973435 7493543 := bstep (se 1 (by rfl) ⟨5620157, by rfl⟩ : syracuseStep 7493543 = 11240315) B11240315
theorem B4995695 : Blo 1973435 4995695 := bstep (se 1 (by rfl) ⟨3746771, by rfl⟩ : syracuseStep 4995695 = 7493543) B7493543
theorem B3330463 : Blo 1973435 3330463 := bstep (se 1 (by rfl) ⟨2497847, by rfl⟩ : syracuseStep 3330463 = 4995695) B4995695
theorem B4440617 : Blo 1973435 4440617 := bstep (se 2 (by rfl) ⟨1665231, by rfl⟩ : syracuseStep 4440617 = 3330463) B3330463
theorem B2960411 : Blo 1973435 2960411 := bstep (se 1 (by rfl) ⟨2220308, by rfl⟩ : syracuseStep 2960411 = 4440617) B4440617
theorem B1973607 : Blo 1973435 1973607 := bstep (se 1 (by rfl) ⟨1480205, by rfl⟩ : syracuseStep 1973607 = 2960411) B2960411
theorem B2220313 : Blo 1973435 2220313 := bbase (se 2 (by rfl) ⟨832617, by rfl⟩ : syracuseStep 2220313 = 1665235) (by norm_num)
theorem B2960417 : Blo 1973435 2960417 := bstep (se 2 (by rfl) ⟨1110156, by rfl⟩ : syracuseStep 2960417 = 2220313) B2220313
theorem B1973611 : Blo 1973435 1973611 := bstep (se 1 (by rfl) ⟨1480208, by rfl⟩ : syracuseStep 1973611 = 2960417) B2960417
theorem B7493573 : Blo 1973435 7493573 := bbase (se 4 (by rfl) ⟨702522, by rfl⟩ : syracuseStep 7493573 = 1405045) (by norm_num)
theorem B4995715 : Blo 1973435 4995715 := bstep (se 1 (by rfl) ⟨3746786, by rfl⟩ : syracuseStep 4995715 = 7493573) B7493573
theorem B6660953 : Blo 1973435 6660953 := bstep (se 2 (by rfl) ⟨2497857, by rfl⟩ : syracuseStep 6660953 = 4995715) B4995715
theorem B4440635 : Blo 1973435 4440635 := bstep (se 1 (by rfl) ⟨3330476, by rfl⟩ : syracuseStep 4440635 = 6660953) B6660953
theorem B2960423 : Blo 1973435 2960423 := bstep (se 1 (by rfl) ⟨2220317, by rfl⟩ : syracuseStep 2960423 = 4440635) B4440635
theorem B1973615 : Blo 1973435 1973615 := bstep (se 1 (by rfl) ⟨1480211, by rfl⟩ : syracuseStep 1973615 = 2960423) B2960423
theorem B2960429 : Blo 1973435 2960429 := bbase (se 3 (by rfl) ⟨555080, by rfl⟩ : syracuseStep 2960429 = 1110161) (by norm_num)
theorem B1973619 : Blo 1973435 1973619 := bstep (se 1 (by rfl) ⟨1480214, by rfl⟩ : syracuseStep 1973619 = 2960429) B2960429
theorem B4440653 : Blo 1973435 4440653 := bbase (se 3 (by rfl) ⟨832622, by rfl⟩ : syracuseStep 4440653 = 1665245) (by norm_num)
theorem B2960435 : Blo 1973435 2960435 := bstep (se 1 (by rfl) ⟨2220326, by rfl⟩ : syracuseStep 2960435 = 4440653) B4440653
theorem B1973623 : Blo 1973435 1973623 := bstep (se 1 (by rfl) ⟨1480217, by rfl⟩ : syracuseStep 1973623 = 2960435) B2960435
theorem B2497873 : Blo 1973435 2497873 := bbase (se 2 (by rfl) ⟨936702, by rfl⟩ : syracuseStep 2497873 = 1873405) (by norm_num)
theorem B3330497 : Blo 1973435 3330497 := bstep (se 2 (by rfl) ⟨1248936, by rfl⟩ : syracuseStep 3330497 = 2497873) B2497873
theorem B2220331 : Blo 1973435 2220331 := bstep (se 1 (by rfl) ⟨1665248, by rfl⟩ : syracuseStep 2220331 = 3330497) B3330497
theorem B2960441 : Blo 1973435 2960441 := bstep (se 2 (by rfl) ⟨1110165, by rfl⟩ : syracuseStep 2960441 = 2220331) B2220331
theorem B1973627 : Blo 1973435 1973627 := bstep (se 1 (by rfl) ⟨1480220, by rfl⟩ : syracuseStep 1973627 = 2960441) B2960441
theorem B2371033 : Blo 1973435 2371033 := bbase (se 2 (by rfl) ⟨889137, by rfl⟩ : syracuseStep 2371033 = 1778275) (by norm_num)
theorem B3161377 : Blo 1973435 3161377 := bstep (se 2 (by rfl) ⟨1185516, by rfl⟩ : syracuseStep 3161377 = 2371033) B2371033
theorem B4215169 : Blo 1973435 4215169 := bstep (se 2 (by rfl) ⟨1580688, by rfl⟩ : syracuseStep 4215169 = 3161377) B3161377
theorem B22480901 : Blo 1973435 22480901 := bstep (se 4 (by rfl) ⟨2107584, by rfl⟩ : syracuseStep 22480901 = 4215169) B4215169
theorem B14987267 : Blo 1973435 14987267 := bstep (se 1 (by rfl) ⟨11240450, by rfl⟩ : syracuseStep 14987267 = 22480901) B22480901
theorem B9991511 : Blo 1973435 9991511 := bstep (se 1 (by rfl) ⟨7493633, by rfl⟩ : syracuseStep 9991511 = 14987267) B14987267
theorem B6661007 : Blo 1973435 6661007 := bstep (se 1 (by rfl) ⟨4995755, by rfl⟩ : syracuseStep 6661007 = 9991511) B9991511
theorem B4440671 : Blo 1973435 4440671 := bstep (se 1 (by rfl) ⟨3330503, by rfl⟩ : syracuseStep 4440671 = 6661007) B6661007
theorem B2960447 : Blo 1973435 2960447 := bstep (se 1 (by rfl) ⟨2220335, by rfl⟩ : syracuseStep 2960447 = 4440671) B4440671
theorem B1973631 : Blo 1973435 1973631 := bstep (se 1 (by rfl) ⟨1480223, by rfl⟩ : syracuseStep 1973631 = 2960447) B2960447
theorem B2960453 : Blo 1973435 2960453 := bbase (se 4 (by rfl) ⟨277542, by rfl⟩ : syracuseStep 2960453 = 555085) (by norm_num)
theorem B1973635 : Blo 1973435 1973635 := bstep (se 1 (by rfl) ⟨1480226, by rfl⟩ : syracuseStep 1973635 = 2960453) B2960453
theorem B3330517 : Blo 1973435 3330517 := bbase (se 7 (by rfl) ⟨39029, by rfl⟩ : syracuseStep 3330517 = 78059) (by norm_num)
theorem B4440689 : Blo 1973435 4440689 := bstep (se 2 (by rfl) ⟨1665258, by rfl⟩ : syracuseStep 4440689 = 3330517) B3330517
theorem B2960459 : Blo 1973435 2960459 := bstep (se 1 (by rfl) ⟨2220344, by rfl⟩ : syracuseStep 2960459 = 4440689) B4440689
theorem B1973639 : Blo 1973435 1973639 := bstep (se 1 (by rfl) ⟨1480229, by rfl⟩ : syracuseStep 1973639 = 2960459) B2960459
theorem B2220349 : Blo 1973435 2220349 := bbase (se 3 (by rfl) ⟨416315, by rfl⟩ : syracuseStep 2220349 = 832631) (by norm_num)
theorem B2960465 : Blo 1973435 2960465 := bstep (se 2 (by rfl) ⟨1110174, by rfl⟩ : syracuseStep 2960465 = 2220349) B2220349
theorem B1973643 : Blo 1973435 1973643 := bstep (se 1 (by rfl) ⟨1480232, by rfl⟩ : syracuseStep 1973643 = 2960465) B2960465
theorem B6661061 : Blo 1973435 6661061 := bbase (se 4 (by rfl) ⟨624474, by rfl⟩ : syracuseStep 6661061 = 1248949) (by norm_num)
theorem B4440707 : Blo 1973435 4440707 := bstep (se 1 (by rfl) ⟨3330530, by rfl⟩ : syracuseStep 4440707 = 6661061) B6661061
theorem B2960471 : Blo 1973435 2960471 := bstep (se 1 (by rfl) ⟨2220353, by rfl⟩ : syracuseStep 2960471 = 4440707) B4440707
theorem B1973647 : Blo 1973435 1973647 := bstep (se 1 (by rfl) ⟨1480235, by rfl⟩ : syracuseStep 1973647 = 2960471) B2960471
theorem B2960477 : Blo 1973435 2960477 := bbase (se 3 (by rfl) ⟨555089, by rfl⟩ : syracuseStep 2960477 = 1110179) (by norm_num)
theorem B1973651 : Blo 1973435 1973651 := bstep (se 1 (by rfl) ⟨1480238, by rfl⟩ : syracuseStep 1973651 = 2960477) B2960477
theorem B4440725 : Blo 1973435 4440725 := bbase (se 6 (by rfl) ⟨104079, by rfl⟩ : syracuseStep 4440725 = 208159) (by norm_num)
theorem B2960483 : Blo 1973435 2960483 := bstep (se 1 (by rfl) ⟨2220362, by rfl⟩ : syracuseStep 2960483 = 4440725) B4440725
theorem B1973655 : Blo 1973435 1973655 := bstep (se 1 (by rfl) ⟨1480241, by rfl⟩ : syracuseStep 1973655 = 2960483) B2960483
theorem B4501325 : Blo 1973435 4501325 := bbase (se 3 (by rfl) ⟨843998, by rfl⟩ : syracuseStep 4501325 = 1687997) (by norm_num)
theorem B3000883 : Blo 1973435 3000883 := bstep (se 1 (by rfl) ⟨2250662, by rfl⟩ : syracuseStep 3000883 = 4501325) B4501325
theorem B4001177 : Blo 1973435 4001177 := bstep (se 2 (by rfl) ⟨1500441, by rfl⟩ : syracuseStep 4001177 = 3000883) B3000883
theorem B10669805 : Blo 1973435 10669805 := bstep (se 3 (by rfl) ⟨2000588, by rfl⟩ : syracuseStep 10669805 = 4001177) B4001177
theorem B7113203 : Blo 1973435 7113203 := bstep (se 1 (by rfl) ⟨5334902, by rfl⟩ : syracuseStep 7113203 = 10669805) B10669805
theorem B4742135 : Blo 1973435 4742135 := bstep (se 1 (by rfl) ⟨3556601, by rfl⟩ : syracuseStep 4742135 = 7113203) B7113203
theorem B3161423 : Blo 1973435 3161423 := bstep (se 1 (by rfl) ⟨2371067, by rfl⟩ : syracuseStep 3161423 = 4742135) B4742135
theorem B2107615 : Blo 1973435 2107615 := bstep (se 1 (by rfl) ⟨1580711, by rfl⟩ : syracuseStep 2107615 = 3161423) B3161423
theorem B2810153 : Blo 1973435 2810153 := bstep (se 2 (by rfl) ⟨1053807, by rfl⟩ : syracuseStep 2810153 = 2107615) B2107615
theorem B7493741 : Blo 1973435 7493741 := bstep (se 3 (by rfl) ⟨1405076, by rfl⟩ : syracuseStep 7493741 = 2810153) B2810153
theorem B4995827 : Blo 1973435 4995827 := bstep (se 1 (by rfl) ⟨3746870, by rfl⟩ : syracuseStep 4995827 = 7493741) B7493741
theorem B3330551 : Blo 1973435 3330551 := bstep (se 1 (by rfl) ⟨2497913, by rfl⟩ : syracuseStep 3330551 = 4995827) B4995827
theorem B2220367 : Blo 1973435 2220367 := bstep (se 1 (by rfl) ⟨1665275, by rfl⟩ : syracuseStep 2220367 = 3330551) B3330551
theorem B2960489 : Blo 1973435 2960489 := bstep (se 2 (by rfl) ⟨1110183, by rfl⟩ : syracuseStep 2960489 = 2220367) B2220367
theorem B1973659 : Blo 1973435 1973659 := bstep (se 1 (by rfl) ⟨1480244, by rfl⟩ : syracuseStep 1973659 = 2960489) B2960489
theorem B9613685 : Blo 1973435 9613685 := bbase (se 5 (by rfl) ⟨450641, by rfl⟩ : syracuseStep 9613685 = 901283) (by norm_num)
theorem B25636493 : Blo 1973435 25636493 := bstep (se 3 (by rfl) ⟨4806842, by rfl⟩ : syracuseStep 25636493 = 9613685) B9613685
theorem B17090995 : Blo 1973435 17090995 := bstep (se 1 (by rfl) ⟨12818246, by rfl⟩ : syracuseStep 17090995 = 25636493) B25636493
theorem B22787993 : Blo 1973435 22787993 := bstep (se 2 (by rfl) ⟨8545497, by rfl⟩ : syracuseStep 22787993 = 17090995) B17090995
theorem B60767981 : Blo 1973435 60767981 := bstep (se 3 (by rfl) ⟨11393996, by rfl⟩ : syracuseStep 60767981 = 22787993) B22787993
theorem B40511987 : Blo 1973435 40511987 := bstep (se 1 (by rfl) ⟨30383990, by rfl⟩ : syracuseStep 40511987 = 60767981) B60767981
theorem B27007991 : Blo 1973435 27007991 := bstep (se 1 (by rfl) ⟨20255993, by rfl⟩ : syracuseStep 27007991 = 40511987) B40511987
theorem B18005327 : Blo 1973435 18005327 := bstep (se 1 (by rfl) ⟨13503995, by rfl⟩ : syracuseStep 18005327 = 27007991) B27007991
theorem B12003551 : Blo 1973435 12003551 := bstep (se 1 (by rfl) ⟨9002663, by rfl⟩ : syracuseStep 12003551 = 18005327) B18005327
theorem B8002367 : Blo 1973435 8002367 := bstep (se 1 (by rfl) ⟨6001775, by rfl⟩ : syracuseStep 8002367 = 12003551) B12003551
theorem B5334911 : Blo 1973435 5334911 := bstep (se 1 (by rfl) ⟨4001183, by rfl⟩ : syracuseStep 5334911 = 8002367) B8002367
theorem B3556607 : Blo 1973435 3556607 := bstep (se 1 (by rfl) ⟨2667455, by rfl⟩ : syracuseStep 3556607 = 5334911) B5334911
theorem B9484285 : Blo 1973435 9484285 := bstep (se 3 (by rfl) ⟨1778303, by rfl⟩ : syracuseStep 9484285 = 3556607) B3556607
theorem B12645713 : Blo 1973435 12645713 := bstep (se 2 (by rfl) ⟨4742142, by rfl⟩ : syracuseStep 12645713 = 9484285) B9484285
theorem B8430475 : Blo 1973435 8430475 := bstep (se 1 (by rfl) ⟨6322856, by rfl⟩ : syracuseStep 8430475 = 12645713) B12645713
theorem B11240633 : Blo 1973435 11240633 := bstep (se 2 (by rfl) ⟨4215237, by rfl⟩ : syracuseStep 11240633 = 8430475) B8430475
theorem B7493755 : Blo 1973435 7493755 := bstep (se 1 (by rfl) ⟨5620316, by rfl⟩ : syracuseStep 7493755 = 11240633) B11240633
theorem B9991673 : Blo 1973435 9991673 := bstep (se 2 (by rfl) ⟨3746877, by rfl⟩ : syracuseStep 9991673 = 7493755) B7493755
theorem B6661115 : Blo 1973435 6661115 := bstep (se 1 (by rfl) ⟨4995836, by rfl⟩ : syracuseStep 6661115 = 9991673) B9991673
theorem B4440743 : Blo 1973435 4440743 := bstep (se 1 (by rfl) ⟨3330557, by rfl⟩ : syracuseStep 4440743 = 6661115) B6661115
theorem B2960495 : Blo 1973435 2960495 := bstep (se 1 (by rfl) ⟨2220371, by rfl⟩ : syracuseStep 2960495 = 4440743) B4440743
theorem B1973663 : Blo 1973435 1973663 := bstep (se 1 (by rfl) ⟨1480247, by rfl⟩ : syracuseStep 1973663 = 2960495) B2960495
theorem B2960501 : Blo 1973435 2960501 := bbase (se 5 (by rfl) ⟨138773, by rfl⟩ : syracuseStep 2960501 = 277547) (by norm_num)
theorem B1973667 : Blo 1973435 1973667 := bstep (se 1 (by rfl) ⟨1480250, by rfl⟩ : syracuseStep 1973667 = 2960501) B2960501
theorem B3746893 : Blo 1973435 3746893 := bbase (se 3 (by rfl) ⟨702542, by rfl⟩ : syracuseStep 3746893 = 1405085) (by norm_num)
theorem B4995857 : Blo 1973435 4995857 := bstep (se 2 (by rfl) ⟨1873446, by rfl⟩ : syracuseStep 4995857 = 3746893) B3746893
theorem B3330571 : Blo 1973435 3330571 := bstep (se 1 (by rfl) ⟨2497928, by rfl⟩ : syracuseStep 3330571 = 4995857) B4995857
theorem B4440761 : Blo 1973435 4440761 := bstep (se 2 (by rfl) ⟨1665285, by rfl⟩ : syracuseStep 4440761 = 3330571) B3330571
theorem B2960507 : Blo 1973435 2960507 := bstep (se 1 (by rfl) ⟨2220380, by rfl⟩ : syracuseStep 2960507 = 4440761) B4440761
theorem B1973671 : Blo 1973435 1973671 := bstep (se 1 (by rfl) ⟨1480253, by rfl⟩ : syracuseStep 1973671 = 2960507) B2960507
theorem B2220385 : Blo 1973435 2220385 := bbase (se 2 (by rfl) ⟨832644, by rfl⟩ : syracuseStep 2220385 = 1665289) (by norm_num)
theorem B2960513 : Blo 1973435 2960513 := bstep (se 2 (by rfl) ⟨1110192, by rfl⟩ : syracuseStep 2960513 = 2220385) B2220385
theorem B1973675 : Blo 1973435 1973675 := bstep (se 1 (by rfl) ⟨1480256, by rfl⟩ : syracuseStep 1973675 = 2960513) B2960513
theorem B4995877 : Blo 1973435 4995877 := bbase (se 4 (by rfl) ⟨468363, by rfl⟩ : syracuseStep 4995877 = 936727) (by norm_num)
theorem B6661169 : Blo 1973435 6661169 := bstep (se 2 (by rfl) ⟨2497938, by rfl⟩ : syracuseStep 6661169 = 4995877) B4995877
theorem B4440779 : Blo 1973435 4440779 := bstep (se 1 (by rfl) ⟨3330584, by rfl⟩ : syracuseStep 4440779 = 6661169) B6661169
theorem B2960519 : Blo 1973435 2960519 := bstep (se 1 (by rfl) ⟨2220389, by rfl⟩ : syracuseStep 2960519 = 4440779) B4440779
theorem B1973679 : Blo 1973435 1973679 := bstep (se 1 (by rfl) ⟨1480259, by rfl⟩ : syracuseStep 1973679 = 2960519) B2960519
theorem B2960525 : Blo 1973435 2960525 := bbase (se 3 (by rfl) ⟨555098, by rfl⟩ : syracuseStep 2960525 = 1110197) (by norm_num)
theorem B1973683 : Blo 1973435 1973683 := bstep (se 1 (by rfl) ⟨1480262, by rfl⟩ : syracuseStep 1973683 = 2960525) B2960525
theorem B4440797 : Blo 1973435 4440797 := bbase (se 3 (by rfl) ⟨832649, by rfl⟩ : syracuseStep 4440797 = 1665299) (by norm_num)
theorem B2960531 : Blo 1973435 2960531 := bstep (se 1 (by rfl) ⟨2220398, by rfl⟩ : syracuseStep 2960531 = 4440797) B4440797
theorem B1973687 : Blo 1973435 1973687 := bstep (se 1 (by rfl) ⟨1480265, by rfl⟩ : syracuseStep 1973687 = 2960531) B2960531
theorem B3330605 : Blo 1973435 3330605 := bbase (se 3 (by rfl) ⟨624488, by rfl⟩ : syracuseStep 3330605 = 1248977) (by norm_num)
theorem B2220403 : Blo 1973435 2220403 := bstep (se 1 (by rfl) ⟨1665302, by rfl⟩ : syracuseStep 2220403 = 3330605) B3330605
theorem B2960537 : Blo 1973435 2960537 := bstep (se 2 (by rfl) ⟨1110201, by rfl⟩ : syracuseStep 2960537 = 2220403) B2220403
theorem B1973691 : Blo 1973435 1973691 := bstep (se 1 (by rfl) ⟨1480268, by rfl⟩ : syracuseStep 1973691 = 2960537) B2960537
theorem B6844229 : Blo 1973435 6844229 := bbase (se 4 (by rfl) ⟨641646, by rfl⟩ : syracuseStep 6844229 = 1283293) (by norm_num)
theorem B4562819 : Blo 1973435 4562819 := bstep (se 1 (by rfl) ⟨3422114, by rfl⟩ : syracuseStep 4562819 = 6844229) B6844229
theorem B3041879 : Blo 1973435 3041879 := bstep (se 1 (by rfl) ⟨2281409, by rfl⟩ : syracuseStep 3041879 = 4562819) B4562819
theorem B8111677 : Blo 1973435 8111677 := bstep (se 3 (by rfl) ⟨1520939, by rfl⟩ : syracuseStep 8111677 = 3041879) B3041879
theorem B10815569 : Blo 1973435 10815569 := bstep (se 2 (by rfl) ⟨4055838, by rfl⟩ : syracuseStep 10815569 = 8111677) B8111677
theorem B7210379 : Blo 1973435 7210379 := bstep (se 1 (by rfl) ⟨5407784, by rfl⟩ : syracuseStep 7210379 = 10815569) B10815569
theorem B19227677 : Blo 1973435 19227677 := bstep (se 3 (by rfl) ⟨3605189, by rfl⟩ : syracuseStep 19227677 = 7210379) B7210379
theorem B51273805 : Blo 1973435 51273805 := bstep (se 3 (by rfl) ⟨9613838, by rfl⟩ : syracuseStep 51273805 = 19227677) B19227677
theorem B68365073 : Blo 1973435 68365073 := bstep (se 2 (by rfl) ⟨25636902, by rfl⟩ : syracuseStep 68365073 = 51273805) B51273805
theorem B45576715 : Blo 1973435 45576715 := bstep (se 1 (by rfl) ⟨34182536, by rfl⟩ : syracuseStep 45576715 = 68365073) B68365073
theorem B60768953 : Blo 1973435 60768953 := bstep (se 2 (by rfl) ⟨22788357, by rfl⟩ : syracuseStep 60768953 = 45576715) B45576715
theorem B40512635 : Blo 1973435 40512635 := bstep (se 1 (by rfl) ⟨30384476, by rfl⟩ : syracuseStep 40512635 = 60768953) B60768953
theorem B27008423 : Blo 1973435 27008423 := bstep (se 1 (by rfl) ⟨20256317, by rfl⟩ : syracuseStep 27008423 = 40512635) B40512635
theorem B18005615 : Blo 1973435 18005615 := bstep (se 1 (by rfl) ⟨13504211, by rfl⟩ : syracuseStep 18005615 = 27008423) B27008423
theorem B12003743 : Blo 1973435 12003743 := bstep (se 1 (by rfl) ⟨9002807, by rfl⟩ : syracuseStep 12003743 = 18005615) B18005615
theorem B8002495 : Blo 1973435 8002495 := bstep (se 1 (by rfl) ⟨6001871, by rfl⟩ : syracuseStep 8002495 = 12003743) B12003743
theorem B42679973 : Blo 1973435 42679973 := bstep (se 4 (by rfl) ⟨4001247, by rfl⟩ : syracuseStep 42679973 = 8002495) B8002495
theorem B28453315 : Blo 1973435 28453315 := bstep (se 1 (by rfl) ⟨21339986, by rfl⟩ : syracuseStep 28453315 = 42679973) B42679973
theorem B37937753 : Blo 1973435 37937753 := bstep (se 2 (by rfl) ⟨14226657, by rfl⟩ : syracuseStep 37937753 = 28453315) B28453315
theorem B25291835 : Blo 1973435 25291835 := bstep (se 1 (by rfl) ⟨18968876, by rfl⟩ : syracuseStep 25291835 = 37937753) B37937753
theorem B16861223 : Blo 1973435 16861223 := bstep (se 1 (by rfl) ⟨12645917, by rfl⟩ : syracuseStep 16861223 = 25291835) B25291835
theorem B11240815 : Blo 1973435 11240815 := bstep (se 1 (by rfl) ⟨8430611, by rfl⟩ : syracuseStep 11240815 = 16861223) B16861223
theorem B14987753 : Blo 1973435 14987753 := bstep (se 2 (by rfl) ⟨5620407, by rfl⟩ : syracuseStep 14987753 = 11240815) B11240815
theorem B9991835 : Blo 1973435 9991835 := bstep (se 1 (by rfl) ⟨7493876, by rfl⟩ : syracuseStep 9991835 = 14987753) B14987753
theorem B6661223 : Blo 1973435 6661223 := bstep (se 1 (by rfl) ⟨4995917, by rfl⟩ : syracuseStep 6661223 = 9991835) B9991835
theorem B4440815 : Blo 1973435 4440815 := bstep (se 1 (by rfl) ⟨3330611, by rfl⟩ : syracuseStep 4440815 = 6661223) B6661223
theorem B2960543 : Blo 1973435 2960543 := bstep (se 1 (by rfl) ⟨2220407, by rfl⟩ : syracuseStep 2960543 = 4440815) B4440815
theorem B1973695 : Blo 1973435 1973695 := bstep (se 1 (by rfl) ⟨1480271, by rfl⟩ : syracuseStep 1973695 = 2960543) B2960543
theorem B2960549 : Blo 1973435 2960549 := bbase (se 4 (by rfl) ⟨277551, by rfl⟩ : syracuseStep 2960549 = 555103) (by norm_num)
theorem B1973699 : Blo 1973435 1973699 := bstep (se 1 (by rfl) ⟨1480274, by rfl⟩ : syracuseStep 1973699 = 2960549) B2960549
theorem B2497969 : Blo 1973435 2497969 := bbase (se 2 (by rfl) ⟨936738, by rfl⟩ : syracuseStep 2497969 = 1873477) (by norm_num)
theorem B3330625 : Blo 1973435 3330625 := bstep (se 2 (by rfl) ⟨1248984, by rfl⟩ : syracuseStep 3330625 = 2497969) B2497969
theorem B4440833 : Blo 1973435 4440833 := bstep (se 2 (by rfl) ⟨1665312, by rfl⟩ : syracuseStep 4440833 = 3330625) B3330625
theorem B2960555 : Blo 1973435 2960555 := bstep (se 1 (by rfl) ⟨2220416, by rfl⟩ : syracuseStep 2960555 = 4440833) B4440833
theorem B1973703 : Blo 1973435 1973703 := bstep (se 1 (by rfl) ⟨1480277, by rfl⟩ : syracuseStep 1973703 = 2960555) B2960555
theorem B2220421 : Blo 1973435 2220421 := bbase (se 4 (by rfl) ⟨208164, by rfl⟩ : syracuseStep 2220421 = 416329) (by norm_num)
theorem B2960561 : Blo 1973435 2960561 := bstep (se 2 (by rfl) ⟨1110210, by rfl⟩ : syracuseStep 2960561 = 2220421) B2220421
theorem B1973707 : Blo 1973435 1973707 := bstep (se 1 (by rfl) ⟨1480280, by rfl⟩ : syracuseStep 1973707 = 2960561) B2960561
theorem B4215341 : Blo 1973435 4215341 := bbase (se 3 (by rfl) ⟨790376, by rfl⟩ : syracuseStep 4215341 = 1580753) (by norm_num)
theorem B2810227 : Blo 1973435 2810227 := bstep (se 1 (by rfl) ⟨2107670, by rfl⟩ : syracuseStep 2810227 = 4215341) B4215341
theorem B3746969 : Blo 1973435 3746969 := bstep (se 2 (by rfl) ⟨1405113, by rfl⟩ : syracuseStep 3746969 = 2810227) B2810227
theorem B2497979 : Blo 1973435 2497979 := bstep (se 1 (by rfl) ⟨1873484, by rfl⟩ : syracuseStep 2497979 = 3746969) B3746969
theorem B6661277 : Blo 1973435 6661277 := bstep (se 3 (by rfl) ⟨1248989, by rfl⟩ : syracuseStep 6661277 = 2497979) B2497979
theorem B4440851 : Blo 1973435 4440851 := bstep (se 1 (by rfl) ⟨3330638, by rfl⟩ : syracuseStep 4440851 = 6661277) B6661277
theorem B2960567 : Blo 1973435 2960567 := bstep (se 1 (by rfl) ⟨2220425, by rfl⟩ : syracuseStep 2960567 = 4440851) B4440851
theorem B1973711 : Blo 1973435 1973711 := bstep (se 1 (by rfl) ⟨1480283, by rfl⟩ : syracuseStep 1973711 = 2960567) B2960567
theorem B2960573 : Blo 1973435 2960573 := bbase (se 3 (by rfl) ⟨555107, by rfl⟩ : syracuseStep 2960573 = 1110215) (by norm_num)
theorem B1973715 : Blo 1973435 1973715 := bstep (se 1 (by rfl) ⟨1480286, by rfl⟩ : syracuseStep 1973715 = 2960573) B2960573
theorem B4440869 : Blo 1973435 4440869 := bbase (se 4 (by rfl) ⟨416331, by rfl⟩ : syracuseStep 4440869 = 832663) (by norm_num)
theorem B2960579 : Blo 1973435 2960579 := bstep (se 1 (by rfl) ⟨2220434, by rfl⟩ : syracuseStep 2960579 = 4440869) B4440869
theorem B1973719 : Blo 1973435 1973719 := bstep (se 1 (by rfl) ⟨1480289, by rfl⟩ : syracuseStep 1973719 = 2960579) B2960579
theorem B4995989 : Blo 1973435 4995989 := bbase (se 6 (by rfl) ⟨117093, by rfl⟩ : syracuseStep 4995989 = 234187) (by norm_num)
theorem B3330659 : Blo 1973435 3330659 := bstep (se 1 (by rfl) ⟨2497994, by rfl⟩ : syracuseStep 3330659 = 4995989) B4995989
theorem B2220439 : Blo 1973435 2220439 := bstep (se 1 (by rfl) ⟨1665329, by rfl⟩ : syracuseStep 2220439 = 3330659) B3330659
theorem B2960585 : Blo 1973435 2960585 := bstep (se 2 (by rfl) ⟨1110219, by rfl⟩ : syracuseStep 2960585 = 2220439) B2220439
theorem B1973723 : Blo 1973435 1973723 := bstep (se 1 (by rfl) ⟨1480292, by rfl⟩ : syracuseStep 1973723 = 2960585) B2960585
theorem B2000657 : Blo 1973435 2000657 := bbase (se 2 (by rfl) ⟨750246, by rfl⟩ : syracuseStep 2000657 = 1500493) (by norm_num)
theorem B5335085 : Blo 1973435 5335085 := bstep (se 3 (by rfl) ⟨1000328, by rfl⟩ : syracuseStep 5335085 = 2000657) B2000657
theorem B3556723 : Blo 1973435 3556723 := bstep (se 1 (by rfl) ⟨2667542, by rfl⟩ : syracuseStep 3556723 = 5335085) B5335085
theorem B4742297 : Blo 1973435 4742297 := bstep (se 2 (by rfl) ⟨1778361, by rfl⟩ : syracuseStep 4742297 = 3556723) B3556723
theorem B3161531 : Blo 1973435 3161531 := bstep (se 1 (by rfl) ⟨2371148, by rfl⟩ : syracuseStep 3161531 = 4742297) B4742297
theorem B8430749 : Blo 1973435 8430749 := bstep (se 3 (by rfl) ⟨1580765, by rfl⟩ : syracuseStep 8430749 = 3161531) B3161531
theorem B5620499 : Blo 1973435 5620499 := bstep (se 1 (by rfl) ⟨4215374, by rfl⟩ : syracuseStep 5620499 = 8430749) B8430749
theorem B3746999 : Blo 1973435 3746999 := bstep (se 1 (by rfl) ⟨2810249, by rfl⟩ : syracuseStep 3746999 = 5620499) B5620499
theorem B9991997 : Blo 1973435 9991997 := bstep (se 3 (by rfl) ⟨1873499, by rfl⟩ : syracuseStep 9991997 = 3746999) B3746999
theorem B6661331 : Blo 1973435 6661331 := bstep (se 1 (by rfl) ⟨4995998, by rfl⟩ : syracuseStep 6661331 = 9991997) B9991997
theorem B4440887 : Blo 1973435 4440887 := bstep (se 1 (by rfl) ⟨3330665, by rfl⟩ : syracuseStep 4440887 = 6661331) B6661331
theorem B2960591 : Blo 1973435 2960591 := bstep (se 1 (by rfl) ⟨2220443, by rfl⟩ : syracuseStep 2960591 = 4440887) B4440887
theorem B1973727 : Blo 1973435 1973727 := bstep (se 1 (by rfl) ⟨1480295, by rfl⟩ : syracuseStep 1973727 = 2960591) B2960591
theorem B2960597 : Blo 1973435 2960597 := bbase (se 7 (by rfl) ⟨34694, by rfl⟩ : syracuseStep 2960597 = 69389) (by norm_num)
theorem B1973731 : Blo 1973435 1973731 := bstep (se 1 (by rfl) ⟨1480298, by rfl⟩ : syracuseStep 1973731 = 2960597) B2960597
theorem B2810261 : Blo 1973435 2810261 := bbase (se 6 (by rfl) ⟨65865, by rfl⟩ : syracuseStep 2810261 = 131731) (by norm_num)
theorem B7494029 : Blo 1973435 7494029 := bstep (se 3 (by rfl) ⟨1405130, by rfl⟩ : syracuseStep 7494029 = 2810261) B2810261
theorem B4996019 : Blo 1973435 4996019 := bstep (se 1 (by rfl) ⟨3747014, by rfl⟩ : syracuseStep 4996019 = 7494029) B7494029
theorem B3330679 : Blo 1973435 3330679 := bstep (se 1 (by rfl) ⟨2498009, by rfl⟩ : syracuseStep 3330679 = 4996019) B4996019
theorem B4440905 : Blo 1973435 4440905 := bstep (se 2 (by rfl) ⟨1665339, by rfl⟩ : syracuseStep 4440905 = 3330679) B3330679
theorem B2960603 : Blo 1973435 2960603 := bstep (se 1 (by rfl) ⟨2220452, by rfl⟩ : syracuseStep 2960603 = 4440905) B4440905
theorem B1973735 : Blo 1973435 1973735 := bstep (se 1 (by rfl) ⟨1480301, by rfl⟩ : syracuseStep 1973735 = 2960603) B2960603
theorem B2220457 : Blo 1973435 2220457 := bbase (se 2 (by rfl) ⟨832671, by rfl⟩ : syracuseStep 2220457 = 1665343) (by norm_num)
theorem B2960609 : Blo 1973435 2960609 := bstep (se 2 (by rfl) ⟨1110228, by rfl⟩ : syracuseStep 2960609 = 2220457) B2220457
theorem B1973739 : Blo 1973435 1973739 := bstep (se 1 (by rfl) ⟨1480304, by rfl⟩ : syracuseStep 1973739 = 2960609) B2960609
theorem B2136461 : Blo 1973435 2136461 := bbase (se 3 (by rfl) ⟨400586, by rfl⟩ : syracuseStep 2136461 = 801173) (by norm_num)
theorem B22788917 : Blo 1973435 22788917 := bstep (se 5 (by rfl) ⟨1068230, by rfl⟩ : syracuseStep 22788917 = 2136461) B2136461
theorem B15192611 : Blo 1973435 15192611 := bstep (se 1 (by rfl) ⟨11394458, by rfl⟩ : syracuseStep 15192611 = 22788917) B22788917
theorem B10128407 : Blo 1973435 10128407 := bstep (se 1 (by rfl) ⟨7596305, by rfl⟩ : syracuseStep 10128407 = 15192611) B15192611
theorem B27009085 : Blo 1973435 27009085 := bstep (se 3 (by rfl) ⟨5064203, by rfl⟩ : syracuseStep 27009085 = 10128407) B10128407
theorem B36012113 : Blo 1973435 36012113 := bstep (se 2 (by rfl) ⟨13504542, by rfl⟩ : syracuseStep 36012113 = 27009085) B27009085
theorem B24008075 : Blo 1973435 24008075 := bstep (se 1 (by rfl) ⟨18006056, by rfl⟩ : syracuseStep 24008075 = 36012113) B36012113
theorem B16005383 : Blo 1973435 16005383 := bstep (se 1 (by rfl) ⟨12004037, by rfl⟩ : syracuseStep 16005383 = 24008075) B24008075
theorem B10670255 : Blo 1973435 10670255 := bstep (se 1 (by rfl) ⟨8002691, by rfl⟩ : syracuseStep 10670255 = 16005383) B16005383
theorem B7113503 : Blo 1973435 7113503 := bstep (se 1 (by rfl) ⟨5335127, by rfl⟩ : syracuseStep 7113503 = 10670255) B10670255
theorem B4742335 : Blo 1973435 4742335 := bstep (se 1 (by rfl) ⟨3556751, by rfl⟩ : syracuseStep 4742335 = 7113503) B7113503
theorem B6323113 : Blo 1973435 6323113 := bstep (se 2 (by rfl) ⟨2371167, by rfl⟩ : syracuseStep 6323113 = 4742335) B4742335
theorem B8430817 : Blo 1973435 8430817 := bstep (se 2 (by rfl) ⟨3161556, by rfl⟩ : syracuseStep 8430817 = 6323113) B6323113
theorem B11241089 : Blo 1973435 11241089 := bstep (se 2 (by rfl) ⟨4215408, by rfl⟩ : syracuseStep 11241089 = 8430817) B8430817
theorem B7494059 : Blo 1973435 7494059 := bstep (se 1 (by rfl) ⟨5620544, by rfl⟩ : syracuseStep 7494059 = 11241089) B11241089
theorem B4996039 : Blo 1973435 4996039 := bstep (se 1 (by rfl) ⟨3747029, by rfl⟩ : syracuseStep 4996039 = 7494059) B7494059
theorem B6661385 : Blo 1973435 6661385 := bstep (se 2 (by rfl) ⟨2498019, by rfl⟩ : syracuseStep 6661385 = 4996039) B4996039
theorem B4440923 : Blo 1973435 4440923 := bstep (se 1 (by rfl) ⟨3330692, by rfl⟩ : syracuseStep 4440923 = 6661385) B6661385
theorem B2960615 : Blo 1973435 2960615 := bstep (se 1 (by rfl) ⟨2220461, by rfl⟩ : syracuseStep 2960615 = 4440923) B4440923
theorem B1973743 : Blo 1973435 1973743 := bstep (se 1 (by rfl) ⟨1480307, by rfl⟩ : syracuseStep 1973743 = 2960615) B2960615
theorem B2960621 : Blo 1973435 2960621 := bbase (se 3 (by rfl) ⟨555116, by rfl⟩ : syracuseStep 2960621 = 1110233) (by norm_num)
theorem B1973747 : Blo 1973435 1973747 := bstep (se 1 (by rfl) ⟨1480310, by rfl⟩ : syracuseStep 1973747 = 2960621) B2960621
theorem B4440941 : Blo 1973435 4440941 := bbase (se 3 (by rfl) ⟨832676, by rfl⟩ : syracuseStep 4440941 = 1665353) (by norm_num)
theorem B2960627 : Blo 1973435 2960627 := bstep (se 1 (by rfl) ⟨2220470, by rfl⟩ : syracuseStep 2960627 = 4440941) B4440941
theorem B1973751 : Blo 1973435 1973751 := bstep (se 1 (by rfl) ⟨1480313, by rfl⟩ : syracuseStep 1973751 = 2960627) B2960627
theorem B3747053 : Blo 1973435 3747053 := bbase (se 3 (by rfl) ⟨702572, by rfl⟩ : syracuseStep 3747053 = 1405145) (by norm_num)
theorem B2498035 : Blo 1973435 2498035 := bstep (se 1 (by rfl) ⟨1873526, by rfl⟩ : syracuseStep 2498035 = 3747053) B3747053
theorem B3330713 : Blo 1973435 3330713 := bstep (se 2 (by rfl) ⟨1249017, by rfl⟩ : syracuseStep 3330713 = 2498035) B2498035
theorem B2220475 : Blo 1973435 2220475 := bstep (se 1 (by rfl) ⟨1665356, by rfl⟩ : syracuseStep 2220475 = 3330713) B3330713
theorem B2960633 : Blo 1973435 2960633 := bstep (se 2 (by rfl) ⟨1110237, by rfl⟩ : syracuseStep 2960633 = 2220475) B2220475
theorem B1973755 : Blo 1973435 1973755 := bstep (se 1 (by rfl) ⟨1480316, by rfl⟩ : syracuseStep 1973755 = 2960633) B2960633
theorem B5064245 : Blo 1973435 5064245 := bbase (se 5 (by rfl) ⟨237386, by rfl⟩ : syracuseStep 5064245 = 474773) (by norm_num)
theorem B3376163 : Blo 1973435 3376163 := bstep (se 1 (by rfl) ⟨2532122, by rfl⟩ : syracuseStep 3376163 = 5064245) B5064245
theorem B2250775 : Blo 1973435 2250775 := bstep (se 1 (by rfl) ⟨1688081, by rfl⟩ : syracuseStep 2250775 = 3376163) B3376163
theorem B3001033 : Blo 1973435 3001033 := bstep (se 2 (by rfl) ⟨1125387, by rfl⟩ : syracuseStep 3001033 = 2250775) B2250775
theorem B16005509 : Blo 1973435 16005509 := bstep (se 4 (by rfl) ⟨1500516, by rfl⟩ : syracuseStep 16005509 = 3001033) B3001033
theorem B10670339 : Blo 1973435 10670339 := bstep (se 1 (by rfl) ⟨8002754, by rfl⟩ : syracuseStep 10670339 = 16005509) B16005509
theorem B28454237 : Blo 1973435 28454237 := bstep (se 3 (by rfl) ⟨5335169, by rfl⟩ : syracuseStep 28454237 = 10670339) B10670339
theorem B18969491 : Blo 1973435 18969491 := bstep (se 1 (by rfl) ⟨14227118, by rfl⟩ : syracuseStep 18969491 = 28454237) B28454237
theorem B50585309 : Blo 1973435 50585309 := bstep (se 3 (by rfl) ⟨9484745, by rfl⟩ : syracuseStep 50585309 = 18969491) B18969491
theorem B33723539 : Blo 1973435 33723539 := bstep (se 1 (by rfl) ⟨25292654, by rfl⟩ : syracuseStep 33723539 = 50585309) B50585309
theorem B22482359 : Blo 1973435 22482359 := bstep (se 1 (by rfl) ⟨16861769, by rfl⟩ : syracuseStep 22482359 = 33723539) B33723539
theorem B14988239 : Blo 1973435 14988239 := bstep (se 1 (by rfl) ⟨11241179, by rfl⟩ : syracuseStep 14988239 = 22482359) B22482359
theorem B9992159 : Blo 1973435 9992159 := bstep (se 1 (by rfl) ⟨7494119, by rfl⟩ : syracuseStep 9992159 = 14988239) B14988239
theorem B6661439 : Blo 1973435 6661439 := bstep (se 1 (by rfl) ⟨4996079, by rfl⟩ : syracuseStep 6661439 = 9992159) B9992159
theorem B4440959 : Blo 1973435 4440959 := bstep (se 1 (by rfl) ⟨3330719, by rfl⟩ : syracuseStep 4440959 = 6661439) B6661439
theorem B2960639 : Blo 1973435 2960639 := bstep (se 1 (by rfl) ⟨2220479, by rfl⟩ : syracuseStep 2960639 = 4440959) B4440959
theorem B1973759 : Blo 1973435 1973759 := bstep (se 1 (by rfl) ⟨1480319, by rfl⟩ : syracuseStep 1973759 = 2960639) B2960639
theorem B2960645 : Blo 1973435 2960645 := bbase (se 4 (by rfl) ⟨277560, by rfl⟩ : syracuseStep 2960645 = 555121) (by norm_num)
theorem B1973763 : Blo 1973435 1973763 := bstep (se 1 (by rfl) ⟨1480322, by rfl⟩ : syracuseStep 1973763 = 2960645) B2960645
theorem B3330733 : Blo 1973435 3330733 := bbase (se 3 (by rfl) ⟨624512, by rfl⟩ : syracuseStep 3330733 = 1249025) (by norm_num)
theorem B4440977 : Blo 1973435 4440977 := bstep (se 2 (by rfl) ⟨1665366, by rfl⟩ : syracuseStep 4440977 = 3330733) B3330733
theorem B2960651 : Blo 1973435 2960651 := bstep (se 1 (by rfl) ⟨2220488, by rfl⟩ : syracuseStep 2960651 = 4440977) B4440977
theorem B1973767 : Blo 1973435 1973767 := bstep (se 1 (by rfl) ⟨1480325, by rfl⟩ : syracuseStep 1973767 = 2960651) B2960651
theorem B2220493 : Blo 1973435 2220493 := bbase (se 3 (by rfl) ⟨416342, by rfl⟩ : syracuseStep 2220493 = 832685) (by norm_num)
theorem B2960657 : Blo 1973435 2960657 := bstep (se 2 (by rfl) ⟨1110246, by rfl⟩ : syracuseStep 2960657 = 2220493) B2220493
theorem B1973771 : Blo 1973435 1973771 := bstep (se 1 (by rfl) ⟨1480328, by rfl⟩ : syracuseStep 1973771 = 2960657) B2960657
theorem B6661493 : Blo 1973435 6661493 := bbase (se 5 (by rfl) ⟨312257, by rfl⟩ : syracuseStep 6661493 = 624515) (by norm_num)
theorem B4440995 : Blo 1973435 4440995 := bstep (se 1 (by rfl) ⟨3330746, by rfl⟩ : syracuseStep 4440995 = 6661493) B6661493
theorem B2960663 : Blo 1973435 2960663 := bstep (se 1 (by rfl) ⟨2220497, by rfl⟩ : syracuseStep 2960663 = 4440995) B4440995
theorem B1973775 : Blo 1973435 1973775 := bstep (se 1 (by rfl) ⟨1480331, by rfl⟩ : syracuseStep 1973775 = 2960663) B2960663
theorem B2960669 : Blo 1973435 2960669 := bbase (se 3 (by rfl) ⟨555125, by rfl⟩ : syracuseStep 2960669 = 1110251) (by norm_num)
theorem B1973779 : Blo 1973435 1973779 := bstep (se 1 (by rfl) ⟨1480334, by rfl⟩ : syracuseStep 1973779 = 2960669) B2960669
theorem B4441013 : Blo 1973435 4441013 := bbase (se 5 (by rfl) ⟨208172, by rfl⟩ : syracuseStep 4441013 = 416345) (by norm_num)
theorem B2960675 : Blo 1973435 2960675 := bstep (se 1 (by rfl) ⟨2220506, by rfl⟩ : syracuseStep 2960675 = 4441013) B4441013
theorem B1973783 : Blo 1973435 1973783 := bstep (se 1 (by rfl) ⟨1480337, by rfl⟩ : syracuseStep 1973783 = 2960675) B2960675
theorem B4331317 : Blo 1973435 4331317 := bbase (se 5 (by rfl) ⟨203030, by rfl⟩ : syracuseStep 4331317 = 406061) (by norm_num)
theorem B5775089 : Blo 1973435 5775089 := bstep (se 2 (by rfl) ⟨2165658, by rfl⟩ : syracuseStep 5775089 = 4331317) B4331317
theorem B61600949 : Blo 1973435 61600949 := bstep (se 5 (by rfl) ⟨2887544, by rfl⟩ : syracuseStep 61600949 = 5775089) B5775089
theorem B41067299 : Blo 1973435 41067299 := bstep (se 1 (by rfl) ⟨30800474, by rfl⟩ : syracuseStep 41067299 = 61600949) B61600949
theorem B27378199 : Blo 1973435 27378199 := bstep (se 1 (by rfl) ⟨20533649, by rfl⟩ : syracuseStep 27378199 = 41067299) B41067299
theorem B36504265 : Blo 1973435 36504265 := bstep (se 2 (by rfl) ⟨13689099, by rfl⟩ : syracuseStep 36504265 = 27378199) B27378199
theorem B48672353 : Blo 1973435 48672353 := bstep (se 2 (by rfl) ⟨18252132, by rfl⟩ : syracuseStep 48672353 = 36504265) B36504265
theorem B32448235 : Blo 1973435 32448235 := bstep (se 1 (by rfl) ⟨24336176, by rfl⟩ : syracuseStep 32448235 = 48672353) B48672353
theorem B43264313 : Blo 1973435 43264313 := bstep (se 2 (by rfl) ⟨16224117, by rfl⟩ : syracuseStep 43264313 = 32448235) B32448235
theorem B28842875 : Blo 1973435 28842875 := bstep (se 1 (by rfl) ⟨21632156, by rfl⟩ : syracuseStep 28842875 = 43264313) B43264313
theorem B19228583 : Blo 1973435 19228583 := bstep (se 1 (by rfl) ⟨14421437, by rfl⟩ : syracuseStep 19228583 = 28842875) B28842875
theorem B12819055 : Blo 1973435 12819055 := bstep (se 1 (by rfl) ⟨9614291, by rfl⟩ : syracuseStep 12819055 = 19228583) B19228583
theorem B17092073 : Blo 1973435 17092073 := bstep (se 2 (by rfl) ⟨6409527, by rfl⟩ : syracuseStep 17092073 = 12819055) B12819055
theorem B11394715 : Blo 1973435 11394715 := bstep (se 1 (by rfl) ⟨8546036, by rfl⟩ : syracuseStep 11394715 = 17092073) B17092073
theorem B15192953 : Blo 1973435 15192953 := bstep (se 2 (by rfl) ⟨5697357, by rfl⟩ : syracuseStep 15192953 = 11394715) B11394715
theorem B10128635 : Blo 1973435 10128635 := bstep (se 1 (by rfl) ⟨7596476, by rfl⟩ : syracuseStep 10128635 = 15192953) B15192953
theorem B6752423 : Blo 1973435 6752423 := bstep (se 1 (by rfl) ⟨5064317, by rfl⟩ : syracuseStep 6752423 = 10128635) B10128635
theorem B18006461 : Blo 1973435 18006461 := bstep (se 3 (by rfl) ⟨3376211, by rfl⟩ : syracuseStep 18006461 = 6752423) B6752423
theorem B12004307 : Blo 1973435 12004307 := bstep (se 1 (by rfl) ⟨9003230, by rfl⟩ : syracuseStep 12004307 = 18006461) B18006461
theorem B8002871 : Blo 1973435 8002871 := bstep (se 1 (by rfl) ⟨6002153, by rfl⟩ : syracuseStep 8002871 = 12004307) B12004307
theorem B5335247 : Blo 1973435 5335247 := bstep (se 1 (by rfl) ⟨4001435, by rfl⟩ : syracuseStep 5335247 = 8002871) B8002871
theorem B14227325 : Blo 1973435 14227325 := bstep (se 3 (by rfl) ⟨2667623, by rfl⟩ : syracuseStep 14227325 = 5335247) B5335247
theorem B9484883 : Blo 1973435 9484883 := bstep (se 1 (by rfl) ⟨7113662, by rfl⟩ : syracuseStep 9484883 = 14227325) B14227325
theorem B6323255 : Blo 1973435 6323255 := bstep (se 1 (by rfl) ⟨4742441, by rfl⟩ : syracuseStep 6323255 = 9484883) B9484883
theorem B4215503 : Blo 1973435 4215503 := bstep (se 1 (by rfl) ⟨3161627, by rfl⟩ : syracuseStep 4215503 = 6323255) B6323255
theorem B11241341 : Blo 1973435 11241341 := bstep (se 3 (by rfl) ⟨2107751, by rfl⟩ : syracuseStep 11241341 = 4215503) B4215503
theorem B7494227 : Blo 1973435 7494227 := bstep (se 1 (by rfl) ⟨5620670, by rfl⟩ : syracuseStep 7494227 = 11241341) B11241341
theorem B4996151 : Blo 1973435 4996151 := bstep (se 1 (by rfl) ⟨3747113, by rfl⟩ : syracuseStep 4996151 = 7494227) B7494227
theorem B3330767 : Blo 1973435 3330767 := bstep (se 1 (by rfl) ⟨2498075, by rfl⟩ : syracuseStep 3330767 = 4996151) B4996151
theorem B2220511 : Blo 1973435 2220511 := bstep (se 1 (by rfl) ⟨1665383, by rfl⟩ : syracuseStep 2220511 = 3330767) B3330767
theorem B2960681 : Blo 1973435 2960681 := bstep (se 2 (by rfl) ⟨1110255, by rfl⟩ : syracuseStep 2960681 = 2220511) B2220511
theorem B1973787 : Blo 1973435 1973787 := bstep (se 1 (by rfl) ⟨1480340, by rfl⟩ : syracuseStep 1973787 = 2960681) B2960681
theorem B9484901 : Blo 1973435 9484901 := bbase (se 4 (by rfl) ⟨889209, by rfl⟩ : syracuseStep 9484901 = 1778419) (by norm_num)
theorem B6323267 : Blo 1973435 6323267 := bstep (se 1 (by rfl) ⟨4742450, by rfl⟩ : syracuseStep 6323267 = 9484901) B9484901
theorem B4215511 : Blo 1973435 4215511 := bstep (se 1 (by rfl) ⟨3161633, by rfl⟩ : syracuseStep 4215511 = 6323267) B6323267
theorem B5620681 : Blo 1973435 5620681 := bstep (se 2 (by rfl) ⟨2107755, by rfl⟩ : syracuseStep 5620681 = 4215511) B4215511
theorem B7494241 : Blo 1973435 7494241 := bstep (se 2 (by rfl) ⟨2810340, by rfl⟩ : syracuseStep 7494241 = 5620681) B5620681
theorem B9992321 : Blo 1973435 9992321 := bstep (se 2 (by rfl) ⟨3747120, by rfl⟩ : syracuseStep 9992321 = 7494241) B7494241
theorem B6661547 : Blo 1973435 6661547 := bstep (se 1 (by rfl) ⟨4996160, by rfl⟩ : syracuseStep 6661547 = 9992321) B9992321
theorem B4441031 : Blo 1973435 4441031 := bstep (se 1 (by rfl) ⟨3330773, by rfl⟩ : syracuseStep 4441031 = 6661547) B6661547
theorem B2960687 : Blo 1973435 2960687 := bstep (se 1 (by rfl) ⟨2220515, by rfl⟩ : syracuseStep 2960687 = 4441031) B4441031
theorem B1973791 : Blo 1973435 1973791 := bstep (se 1 (by rfl) ⟨1480343, by rfl⟩ : syracuseStep 1973791 = 2960687) B2960687
theorem B2960693 : Blo 1973435 2960693 := bbase (se 5 (by rfl) ⟨138782, by rfl⟩ : syracuseStep 2960693 = 277565) (by norm_num)
theorem B1973795 : Blo 1973435 1973795 := bstep (se 1 (by rfl) ⟨1480346, by rfl⟩ : syracuseStep 1973795 = 2960693) B2960693
theorem B4996181 : Blo 1973435 4996181 := bbase (se 8 (by rfl) ⟨29274, by rfl⟩ : syracuseStep 4996181 = 58549) (by norm_num)
theorem B3330787 : Blo 1973435 3330787 := bstep (se 1 (by rfl) ⟨2498090, by rfl⟩ : syracuseStep 3330787 = 4996181) B4996181
theorem B4441049 : Blo 1973435 4441049 := bstep (se 2 (by rfl) ⟨1665393, by rfl⟩ : syracuseStep 4441049 = 3330787) B3330787
theorem B2960699 : Blo 1973435 2960699 := bstep (se 1 (by rfl) ⟨2220524, by rfl⟩ : syracuseStep 2960699 = 4441049) B4441049
theorem B1973799 : Blo 1973435 1973799 := bstep (se 1 (by rfl) ⟨1480349, by rfl⟩ : syracuseStep 1973799 = 2960699) B2960699
theorem B2220529 : Blo 1973435 2220529 := bbase (se 2 (by rfl) ⟨832698, by rfl⟩ : syracuseStep 2220529 = 1665397) (by norm_num)
theorem B2960705 : Blo 1973435 2960705 := bstep (se 2 (by rfl) ⟨1110264, by rfl⟩ : syracuseStep 2960705 = 2220529) B2220529
theorem B1973803 : Blo 1973435 1973803 := bstep (se 1 (by rfl) ⟨1480352, by rfl⟩ : syracuseStep 1973803 = 2960705) B2960705
theorem B5335301 : Blo 1973435 5335301 := bbase (se 4 (by rfl) ⟨500184, by rfl⟩ : syracuseStep 5335301 = 1000369) (by norm_num)
theorem B3556867 : Blo 1973435 3556867 := bstep (se 1 (by rfl) ⟨2667650, by rfl⟩ : syracuseStep 3556867 = 5335301) B5335301
theorem B4742489 : Blo 1973435 4742489 := bstep (se 2 (by rfl) ⟨1778433, by rfl⟩ : syracuseStep 4742489 = 3556867) B3556867
theorem B12646637 : Blo 1973435 12646637 := bstep (se 3 (by rfl) ⟨2371244, by rfl⟩ : syracuseStep 12646637 = 4742489) B4742489
theorem B8431091 : Blo 1973435 8431091 := bstep (se 1 (by rfl) ⟨6323318, by rfl⟩ : syracuseStep 8431091 = 12646637) B12646637
theorem B5620727 : Blo 1973435 5620727 := bstep (se 1 (by rfl) ⟨4215545, by rfl⟩ : syracuseStep 5620727 = 8431091) B8431091
theorem B3747151 : Blo 1973435 3747151 := bstep (se 1 (by rfl) ⟨2810363, by rfl⟩ : syracuseStep 3747151 = 5620727) B5620727
theorem B4996201 : Blo 1973435 4996201 := bstep (se 2 (by rfl) ⟨1873575, by rfl⟩ : syracuseStep 4996201 = 3747151) B3747151
theorem B6661601 : Blo 1973435 6661601 := bstep (se 2 (by rfl) ⟨2498100, by rfl⟩ : syracuseStep 6661601 = 4996201) B4996201
theorem B4441067 : Blo 1973435 4441067 := bstep (se 1 (by rfl) ⟨3330800, by rfl⟩ : syracuseStep 4441067 = 6661601) B6661601
theorem B2960711 : Blo 1973435 2960711 := bstep (se 1 (by rfl) ⟨2220533, by rfl⟩ : syracuseStep 2960711 = 4441067) B4441067
theorem B1973807 : Blo 1973435 1973807 := bstep (se 1 (by rfl) ⟨1480355, by rfl⟩ : syracuseStep 1973807 = 2960711) B2960711
theorem B2960717 : Blo 1973435 2960717 := bbase (se 3 (by rfl) ⟨555134, by rfl⟩ : syracuseStep 2960717 = 1110269) (by norm_num)
theorem B1973811 : Blo 1973435 1973811 := bstep (se 1 (by rfl) ⟨1480358, by rfl⟩ : syracuseStep 1973811 = 2960717) B2960717
theorem B4441085 : Blo 1973435 4441085 := bbase (se 3 (by rfl) ⟨832703, by rfl⟩ : syracuseStep 4441085 = 1665407) (by norm_num)
theorem B2960723 : Blo 1973435 2960723 := bstep (se 1 (by rfl) ⟨2220542, by rfl⟩ : syracuseStep 2960723 = 4441085) B4441085
theorem B1973815 : Blo 1973435 1973815 := bstep (se 1 (by rfl) ⟨1480361, by rfl⟩ : syracuseStep 1973815 = 2960723) B2960723
theorem B3330821 : Blo 1973435 3330821 := bbase (se 4 (by rfl) ⟨312264, by rfl⟩ : syracuseStep 3330821 = 624529) (by norm_num)
theorem B2220547 : Blo 1973435 2220547 := bstep (se 1 (by rfl) ⟨1665410, by rfl⟩ : syracuseStep 2220547 = 3330821) B3330821
theorem B2960729 : Blo 1973435 2960729 := bstep (se 2 (by rfl) ⟨1110273, by rfl⟩ : syracuseStep 2960729 = 2220547) B2220547
theorem B1973819 : Blo 1973435 1973819 := bstep (se 1 (by rfl) ⟨1480364, by rfl⟩ : syracuseStep 1973819 = 2960729) B2960729
theorem B14988725 : Blo 1973435 14988725 := bbase (se 5 (by rfl) ⟨702596, by rfl⟩ : syracuseStep 14988725 = 1405193) (by norm_num)
theorem B9992483 : Blo 1973435 9992483 := bstep (se 1 (by rfl) ⟨7494362, by rfl⟩ : syracuseStep 9992483 = 14988725) B14988725
theorem B6661655 : Blo 1973435 6661655 := bstep (se 1 (by rfl) ⟨4996241, by rfl⟩ : syracuseStep 6661655 = 9992483) B9992483
theorem B4441103 : Blo 1973435 4441103 := bstep (se 1 (by rfl) ⟨3330827, by rfl⟩ : syracuseStep 4441103 = 6661655) B6661655
theorem B2960735 : Blo 1973435 2960735 := bstep (se 1 (by rfl) ⟨2220551, by rfl⟩ : syracuseStep 2960735 = 4441103) B4441103
theorem B1973823 : Blo 1973435 1973823 := bstep (se 1 (by rfl) ⟨1480367, by rfl⟩ : syracuseStep 1973823 = 2960735) B2960735
theorem B2960741 : Blo 1973435 2960741 := bbase (se 4 (by rfl) ⟨277569, by rfl⟩ : syracuseStep 2960741 = 555139) (by norm_num)
theorem B1973827 : Blo 1973435 1973827 := bstep (se 1 (by rfl) ⟨1480370, by rfl⟩ : syracuseStep 1973827 = 2960741) B2960741
theorem B3747197 : Blo 1973435 3747197 := bbase (se 3 (by rfl) ⟨702599, by rfl⟩ : syracuseStep 3747197 = 1405199) (by norm_num)
theorem B2498131 : Blo 1973435 2498131 := bstep (se 1 (by rfl) ⟨1873598, by rfl⟩ : syracuseStep 2498131 = 3747197) B3747197
theorem B3330841 : Blo 1973435 3330841 := bstep (se 2 (by rfl) ⟨1249065, by rfl⟩ : syracuseStep 3330841 = 2498131) B2498131
theorem B4441121 : Blo 1973435 4441121 := bstep (se 2 (by rfl) ⟨1665420, by rfl⟩ : syracuseStep 4441121 = 3330841) B3330841
theorem B2960747 : Blo 1973435 2960747 := bstep (se 1 (by rfl) ⟨2220560, by rfl⟩ : syracuseStep 2960747 = 4441121) B4441121
theorem B1973831 : Blo 1973435 1973831 := bstep (se 1 (by rfl) ⟨1480373, by rfl⟩ : syracuseStep 1973831 = 2960747) B2960747
theorem B2220565 : Blo 1973435 2220565 := bbase (se 6 (by rfl) ⟨52044, by rfl⟩ : syracuseStep 2220565 = 104089) (by norm_num)
theorem B2960753 : Blo 1973435 2960753 := bstep (se 2 (by rfl) ⟨1110282, by rfl⟩ : syracuseStep 2960753 = 2220565) B2220565
theorem B1973835 : Blo 1973435 1973835 := bstep (se 1 (by rfl) ⟨1480376, by rfl⟩ : syracuseStep 1973835 = 2960753) B2960753
theorem B2498141 : Blo 1973435 2498141 := bbase (se 3 (by rfl) ⟨468401, by rfl⟩ : syracuseStep 2498141 = 936803) (by norm_num)
theorem B6661709 : Blo 1973435 6661709 := bstep (se 3 (by rfl) ⟨1249070, by rfl⟩ : syracuseStep 6661709 = 2498141) B2498141
theorem B4441139 : Blo 1973435 4441139 := bstep (se 1 (by rfl) ⟨3330854, by rfl⟩ : syracuseStep 4441139 = 6661709) B6661709
theorem B2960759 : Blo 1973435 2960759 := bstep (se 1 (by rfl) ⟨2220569, by rfl⟩ : syracuseStep 2960759 = 4441139) B4441139
theorem B1973839 : Blo 1973435 1973839 := bstep (se 1 (by rfl) ⟨1480379, by rfl⟩ : syracuseStep 1973839 = 2960759) B2960759
theorem B2960765 : Blo 1973435 2960765 := bbase (se 3 (by rfl) ⟨555143, by rfl⟩ : syracuseStep 2960765 = 1110287) (by norm_num)
theorem B1973843 : Blo 1973435 1973843 := bstep (se 1 (by rfl) ⟨1480382, by rfl⟩ : syracuseStep 1973843 = 2960765) B2960765
theorem B4441157 : Blo 1973435 4441157 := bbase (se 4 (by rfl) ⟨416358, by rfl⟩ : syracuseStep 4441157 = 832717) (by norm_num)
theorem B2960771 : Blo 1973435 2960771 := bstep (se 1 (by rfl) ⟨2220578, by rfl⟩ : syracuseStep 2960771 = 4441157) B4441157
theorem B1973847 : Blo 1973435 1973847 := bstep (se 1 (by rfl) ⟨1480385, by rfl⟩ : syracuseStep 1973847 = 2960771) B2960771
theorem B5620853 : Blo 1973435 5620853 := bbase (se 5 (by rfl) ⟨263477, by rfl⟩ : syracuseStep 5620853 = 526955) (by norm_num)
theorem B3747235 : Blo 1973435 3747235 := bstep (se 1 (by rfl) ⟨2810426, by rfl⟩ : syracuseStep 3747235 = 5620853) B5620853
theorem B4996313 : Blo 1973435 4996313 := bstep (se 2 (by rfl) ⟨1873617, by rfl⟩ : syracuseStep 4996313 = 3747235) B3747235
theorem B3330875 : Blo 1973435 3330875 := bstep (se 1 (by rfl) ⟨2498156, by rfl⟩ : syracuseStep 3330875 = 4996313) B4996313
theorem B2220583 : Blo 1973435 2220583 := bstep (se 1 (by rfl) ⟨1665437, by rfl⟩ : syracuseStep 2220583 = 3330875) B3330875
theorem B2960777 : Blo 1973435 2960777 := bstep (se 2 (by rfl) ⟨1110291, by rfl⟩ : syracuseStep 2960777 = 2220583) B2220583
theorem B1973851 : Blo 1973435 1973851 := bstep (se 1 (by rfl) ⟨1480388, by rfl⟩ : syracuseStep 1973851 = 2960777) B2960777
theorem B9992645 : Blo 1973435 9992645 := bbase (se 4 (by rfl) ⟨936810, by rfl⟩ : syracuseStep 9992645 = 1873621) (by norm_num)
theorem B6661763 : Blo 1973435 6661763 := bstep (se 1 (by rfl) ⟨4996322, by rfl⟩ : syracuseStep 6661763 = 9992645) B9992645
theorem B4441175 : Blo 1973435 4441175 := bstep (se 1 (by rfl) ⟨3330881, by rfl⟩ : syracuseStep 4441175 = 6661763) B6661763
theorem B2960783 : Blo 1973435 2960783 := bstep (se 1 (by rfl) ⟨2220587, by rfl⟩ : syracuseStep 2960783 = 4441175) B4441175
theorem B1973855 : Blo 1973435 1973855 := bstep (se 1 (by rfl) ⟨1480391, by rfl⟩ : syracuseStep 1973855 = 2960783) B2960783
theorem B2960789 : Blo 1973435 2960789 := bbase (se 6 (by rfl) ⟨69393, by rfl⟩ : syracuseStep 2960789 = 138787) (by norm_num)
theorem B1973859 : Blo 1973435 1973859 := bstep (se 1 (by rfl) ⟨1480394, by rfl⟩ : syracuseStep 1973859 = 2960789) B2960789
theorem B3161749 : Blo 1973435 3161749 := bbase (se 6 (by rfl) ⟨74103, by rfl⟩ : syracuseStep 3161749 = 148207) (by norm_num)
theorem B4215665 : Blo 1973435 4215665 := bstep (se 2 (by rfl) ⟨1580874, by rfl⟩ : syracuseStep 4215665 = 3161749) B3161749
theorem B11241773 : Blo 1973435 11241773 := bstep (se 3 (by rfl) ⟨2107832, by rfl⟩ : syracuseStep 11241773 = 4215665) B4215665
theorem B7494515 : Blo 1973435 7494515 := bstep (se 1 (by rfl) ⟨5620886, by rfl⟩ : syracuseStep 7494515 = 11241773) B11241773
theorem B4996343 : Blo 1973435 4996343 := bstep (se 1 (by rfl) ⟨3747257, by rfl⟩ : syracuseStep 4996343 = 7494515) B7494515
theorem B3330895 : Blo 1973435 3330895 := bstep (se 1 (by rfl) ⟨2498171, by rfl⟩ : syracuseStep 3330895 = 4996343) B4996343
theorem B4441193 : Blo 1973435 4441193 := bstep (se 2 (by rfl) ⟨1665447, by rfl⟩ : syracuseStep 4441193 = 3330895) B3330895
theorem B2960795 : Blo 1973435 2960795 := bstep (se 1 (by rfl) ⟨2220596, by rfl⟩ : syracuseStep 2960795 = 4441193) B4441193
theorem B1973863 : Blo 1973435 1973863 := bstep (se 1 (by rfl) ⟨1480397, by rfl⟩ : syracuseStep 1973863 = 2960795) B2960795
theorem B2220601 : Blo 1973435 2220601 := bbase (se 2 (by rfl) ⟨832725, by rfl⟩ : syracuseStep 2220601 = 1665451) (by norm_num)
theorem B2960801 : Blo 1973435 2960801 := bstep (se 2 (by rfl) ⟨1110300, by rfl⟩ : syracuseStep 2960801 = 2220601) B2220601
theorem B1973867 : Blo 1973435 1973867 := bstep (se 1 (by rfl) ⟨1480400, by rfl⟩ : syracuseStep 1973867 = 2960801) B2960801
theorem B2107841 : Blo 1973435 2107841 := bbase (se 2 (by rfl) ⟨790440, by rfl⟩ : syracuseStep 2107841 = 1580881) (by norm_num)
theorem B5620909 : Blo 1973435 5620909 := bstep (se 3 (by rfl) ⟨1053920, by rfl⟩ : syracuseStep 5620909 = 2107841) B2107841
theorem B7494545 : Blo 1973435 7494545 := bstep (se 2 (by rfl) ⟨2810454, by rfl⟩ : syracuseStep 7494545 = 5620909) B5620909
theorem B4996363 : Blo 1973435 4996363 := bstep (se 1 (by rfl) ⟨3747272, by rfl⟩ : syracuseStep 4996363 = 7494545) B7494545
theorem B6661817 : Blo 1973435 6661817 := bstep (se 2 (by rfl) ⟨2498181, by rfl⟩ : syracuseStep 6661817 = 4996363) B4996363
theorem B4441211 : Blo 1973435 4441211 := bstep (se 1 (by rfl) ⟨3330908, by rfl⟩ : syracuseStep 4441211 = 6661817) B6661817
theorem B2960807 : Blo 1973435 2960807 := bstep (se 1 (by rfl) ⟨2220605, by rfl⟩ : syracuseStep 2960807 = 4441211) B4441211
theorem B1973871 : Blo 1973435 1973871 := bstep (se 1 (by rfl) ⟨1480403, by rfl⟩ : syracuseStep 1973871 = 2960807) B2960807
theorem B2960813 : Blo 1973435 2960813 := bbase (se 3 (by rfl) ⟨555152, by rfl⟩ : syracuseStep 2960813 = 1110305) (by norm_num)
theorem B1973875 : Blo 1973435 1973875 := bstep (se 1 (by rfl) ⟨1480406, by rfl⟩ : syracuseStep 1973875 = 2960813) B2960813
theorem B4441229 : Blo 1973435 4441229 := bbase (se 3 (by rfl) ⟨832730, by rfl⟩ : syracuseStep 4441229 = 1665461) (by norm_num)
theorem B2960819 : Blo 1973435 2960819 := bstep (se 1 (by rfl) ⟨2220614, by rfl⟩ : syracuseStep 2960819 = 4441229) B4441229
theorem B1973879 : Blo 1973435 1973879 := bstep (se 1 (by rfl) ⟨1480409, by rfl⟩ : syracuseStep 1973879 = 2960819) B2960819
theorem B2498197 : Blo 1973435 2498197 := bbase (se 6 (by rfl) ⟨58551, by rfl⟩ : syracuseStep 2498197 = 117103) (by norm_num)
theorem B3330929 : Blo 1973435 3330929 := bstep (se 2 (by rfl) ⟨1249098, by rfl⟩ : syracuseStep 3330929 = 2498197) B2498197
theorem B2220619 : Blo 1973435 2220619 := bstep (se 1 (by rfl) ⟨1665464, by rfl⟩ : syracuseStep 2220619 = 3330929) B3330929
theorem B2960825 : Blo 1973435 2960825 := bstep (se 2 (by rfl) ⟨1110309, by rfl⟩ : syracuseStep 2960825 = 2220619) B2220619
theorem B1973883 : Blo 1973435 1973883 := bstep (se 1 (by rfl) ⟨1480412, by rfl⟩ : syracuseStep 1973883 = 2960825) B2960825
theorem B13505525 : Blo 1973435 13505525 := bbase (se 5 (by rfl) ⟨633071, by rfl⟩ : syracuseStep 13505525 = 1266143) (by norm_num)
theorem B9003683 : Blo 1973435 9003683 := bstep (se 1 (by rfl) ⟨6752762, by rfl⟩ : syracuseStep 9003683 = 13505525) B13505525
theorem B24009821 : Blo 1973435 24009821 := bstep (se 3 (by rfl) ⟨4501841, by rfl⟩ : syracuseStep 24009821 = 9003683) B9003683
theorem B16006547 : Blo 1973435 16006547 := bstep (se 1 (by rfl) ⟨12004910, by rfl⟩ : syracuseStep 16006547 = 24009821) B24009821
theorem B10671031 : Blo 1973435 10671031 := bstep (se 1 (by rfl) ⟨8003273, by rfl⟩ : syracuseStep 10671031 = 16006547) B16006547
theorem B56912165 : Blo 1973435 56912165 := bstep (se 4 (by rfl) ⟨5335515, by rfl⟩ : syracuseStep 56912165 = 10671031) B10671031
theorem B37941443 : Blo 1973435 37941443 := bstep (se 1 (by rfl) ⟨28456082, by rfl⟩ : syracuseStep 37941443 = 56912165) B56912165
theorem B25294295 : Blo 1973435 25294295 := bstep (se 1 (by rfl) ⟨18970721, by rfl⟩ : syracuseStep 25294295 = 37941443) B37941443
theorem B16862863 : Blo 1973435 16862863 := bstep (se 1 (by rfl) ⟨12647147, by rfl⟩ : syracuseStep 16862863 = 25294295) B25294295
theorem B22483817 : Blo 1973435 22483817 := bstep (se 2 (by rfl) ⟨8431431, by rfl⟩ : syracuseStep 22483817 = 16862863) B16862863
theorem B14989211 : Blo 1973435 14989211 := bstep (se 1 (by rfl) ⟨11241908, by rfl⟩ : syracuseStep 14989211 = 22483817) B22483817
theorem B9992807 : Blo 1973435 9992807 := bstep (se 1 (by rfl) ⟨7494605, by rfl⟩ : syracuseStep 9992807 = 14989211) B14989211
theorem B6661871 : Blo 1973435 6661871 := bstep (se 1 (by rfl) ⟨4996403, by rfl⟩ : syracuseStep 6661871 = 9992807) B9992807
theorem B4441247 : Blo 1973435 4441247 := bstep (se 1 (by rfl) ⟨3330935, by rfl⟩ : syracuseStep 4441247 = 6661871) B6661871
theorem B2960831 : Blo 1973435 2960831 := bstep (se 1 (by rfl) ⟨2220623, by rfl⟩ : syracuseStep 2960831 = 4441247) B4441247
theorem B1973887 : Blo 1973435 1973887 := bstep (se 1 (by rfl) ⟨1480415, by rfl⟩ : syracuseStep 1973887 = 2960831) B2960831
theorem B2960837 : Blo 1973435 2960837 := bbase (se 4 (by rfl) ⟨277578, by rfl⟩ : syracuseStep 2960837 = 555157) (by norm_num)
theorem B1973891 : Blo 1973435 1973891 := bstep (se 1 (by rfl) ⟨1480418, by rfl⟩ : syracuseStep 1973891 = 2960837) B2960837
theorem B3330949 : Blo 1973435 3330949 := bbase (se 4 (by rfl) ⟨312276, by rfl⟩ : syracuseStep 3330949 = 624553) (by norm_num)
theorem B4441265 : Blo 1973435 4441265 := bstep (se 2 (by rfl) ⟨1665474, by rfl⟩ : syracuseStep 4441265 = 3330949) B3330949
theorem B2960843 : Blo 1973435 2960843 := bstep (se 1 (by rfl) ⟨2220632, by rfl⟩ : syracuseStep 2960843 = 4441265) B4441265
theorem B1973895 : Blo 1973435 1973895 := bstep (se 1 (by rfl) ⟨1480421, by rfl⟩ : syracuseStep 1973895 = 2960843) B2960843
theorem B2220637 : Blo 1973435 2220637 := bbase (se 3 (by rfl) ⟨416369, by rfl⟩ : syracuseStep 2220637 = 832739) (by norm_num)
theorem B2960849 : Blo 1973435 2960849 := bstep (se 2 (by rfl) ⟨1110318, by rfl⟩ : syracuseStep 2960849 = 2220637) B2220637
theorem B1973899 : Blo 1973435 1973899 := bstep (se 1 (by rfl) ⟨1480424, by rfl⟩ : syracuseStep 1973899 = 2960849) B2960849
theorem B6661925 : Blo 1973435 6661925 := bbase (se 4 (by rfl) ⟨624555, by rfl⟩ : syracuseStep 6661925 = 1249111) (by norm_num)
theorem B4441283 : Blo 1973435 4441283 := bstep (se 1 (by rfl) ⟨3330962, by rfl⟩ : syracuseStep 4441283 = 6661925) B6661925
theorem B2960855 : Blo 1973435 2960855 := bstep (se 1 (by rfl) ⟨2220641, by rfl⟩ : syracuseStep 2960855 = 4441283) B4441283
theorem B1973903 : Blo 1973435 1973903 := bstep (se 1 (by rfl) ⟨1480427, by rfl⟩ : syracuseStep 1973903 = 2960855) B2960855
theorem B2960861 : Blo 1973435 2960861 := bbase (se 3 (by rfl) ⟨555161, by rfl⟩ : syracuseStep 2960861 = 1110323) (by norm_num)
theorem B1973907 : Blo 1973435 1973907 := bstep (se 1 (by rfl) ⟨1480430, by rfl⟩ : syracuseStep 1973907 = 2960861) B2960861
theorem B4441301 : Blo 1973435 4441301 := bbase (se 7 (by rfl) ⟨52046, by rfl⟩ : syracuseStep 4441301 = 104093) (by norm_num)
theorem B2960867 : Blo 1973435 2960867 := bstep (se 1 (by rfl) ⟨2220650, by rfl⟩ : syracuseStep 2960867 = 4441301) B4441301
theorem B1973911 : Blo 1973435 1973911 := bstep (se 1 (by rfl) ⟨1480433, by rfl⟩ : syracuseStep 1973911 = 2960867) B2960867
theorem B4742749 : Blo 1973435 4742749 := bbase (se 3 (by rfl) ⟨889265, by rfl⟩ : syracuseStep 4742749 = 1778531) (by norm_num)
theorem B6323665 : Blo 1973435 6323665 := bstep (se 2 (by rfl) ⟨2371374, by rfl⟩ : syracuseStep 6323665 = 4742749) B4742749
theorem B8431553 : Blo 1973435 8431553 := bstep (se 2 (by rfl) ⟨3161832, by rfl⟩ : syracuseStep 8431553 = 6323665) B6323665
theorem B5621035 : Blo 1973435 5621035 := bstep (se 1 (by rfl) ⟨4215776, by rfl⟩ : syracuseStep 5621035 = 8431553) B8431553
theorem B7494713 : Blo 1973435 7494713 := bstep (se 2 (by rfl) ⟨2810517, by rfl⟩ : syracuseStep 7494713 = 5621035) B5621035
theorem B4996475 : Blo 1973435 4996475 := bstep (se 1 (by rfl) ⟨3747356, by rfl⟩ : syracuseStep 4996475 = 7494713) B7494713
theorem B3330983 : Blo 1973435 3330983 := bstep (se 1 (by rfl) ⟨2498237, by rfl⟩ : syracuseStep 3330983 = 4996475) B4996475
theorem B2220655 : Blo 1973435 2220655 := bstep (se 1 (by rfl) ⟨1665491, by rfl⟩ : syracuseStep 2220655 = 3330983) B3330983
theorem B2960873 : Blo 1973435 2960873 := bstep (se 2 (by rfl) ⟨1110327, by rfl⟩ : syracuseStep 2960873 = 2220655) B2220655
theorem B1973915 : Blo 1973435 1973915 := bstep (se 1 (by rfl) ⟨1480436, by rfl⟩ : syracuseStep 1973915 = 2960873) B2960873
theorem B3001277 : Blo 1973435 3001277 := bbase (se 3 (by rfl) ⟨562739, by rfl⟩ : syracuseStep 3001277 = 1125479) (by norm_num)
theorem B2000851 : Blo 1973435 2000851 := bstep (se 1 (by rfl) ⟨1500638, by rfl⟩ : syracuseStep 2000851 = 3001277) B3001277
theorem B10671205 : Blo 1973435 10671205 := bstep (se 4 (by rfl) ⟨1000425, by rfl⟩ : syracuseStep 10671205 = 2000851) B2000851
theorem B14228273 : Blo 1973435 14228273 := bstep (se 2 (by rfl) ⟨5335602, by rfl⟩ : syracuseStep 14228273 = 10671205) B10671205
theorem B9485515 : Blo 1973435 9485515 := bstep (se 1 (by rfl) ⟨7114136, by rfl⟩ : syracuseStep 9485515 = 14228273) B14228273
theorem B12647353 : Blo 1973435 12647353 := bstep (se 2 (by rfl) ⟨4742757, by rfl⟩ : syracuseStep 12647353 = 9485515) B9485515
theorem B16863137 : Blo 1973435 16863137 := bstep (se 2 (by rfl) ⟨6323676, by rfl⟩ : syracuseStep 16863137 = 12647353) B12647353
theorem B11242091 : Blo 1973435 11242091 := bstep (se 1 (by rfl) ⟨8431568, by rfl⟩ : syracuseStep 11242091 = 16863137) B16863137
theorem B7494727 : Blo 1973435 7494727 := bstep (se 1 (by rfl) ⟨5621045, by rfl⟩ : syracuseStep 7494727 = 11242091) B11242091
theorem B9992969 : Blo 1973435 9992969 := bstep (se 2 (by rfl) ⟨3747363, by rfl⟩ : syracuseStep 9992969 = 7494727) B7494727
theorem B6661979 : Blo 1973435 6661979 := bstep (se 1 (by rfl) ⟨4996484, by rfl⟩ : syracuseStep 6661979 = 9992969) B9992969
theorem B4441319 : Blo 1973435 4441319 := bstep (se 1 (by rfl) ⟨3330989, by rfl⟩ : syracuseStep 4441319 = 6661979) B6661979
theorem B2960879 : Blo 1973435 2960879 := bstep (se 1 (by rfl) ⟨2220659, by rfl⟩ : syracuseStep 2960879 = 4441319) B4441319
theorem B1973919 : Blo 1973435 1973919 := bstep (se 1 (by rfl) ⟨1480439, by rfl⟩ : syracuseStep 1973919 = 2960879) B2960879
theorem B2960885 : Blo 1973435 2960885 := bbase (se 5 (by rfl) ⟨138791, by rfl⟩ : syracuseStep 2960885 = 277583) (by norm_num)
theorem B1973923 : Blo 1973435 1973923 := bstep (se 1 (by rfl) ⟨1480442, by rfl⟩ : syracuseStep 1973923 = 2960885) B2960885
theorem B2107901 : Blo 1973435 2107901 := bbase (se 3 (by rfl) ⟨395231, by rfl⟩ : syracuseStep 2107901 = 790463) (by norm_num)
theorem B5621069 : Blo 1973435 5621069 := bstep (se 3 (by rfl) ⟨1053950, by rfl⟩ : syracuseStep 5621069 = 2107901) B2107901
theorem B3747379 : Blo 1973435 3747379 := bstep (se 1 (by rfl) ⟨2810534, by rfl⟩ : syracuseStep 3747379 = 5621069) B5621069
theorem B4996505 : Blo 1973435 4996505 := bstep (se 2 (by rfl) ⟨1873689, by rfl⟩ : syracuseStep 4996505 = 3747379) B3747379
theorem B3331003 : Blo 1973435 3331003 := bstep (se 1 (by rfl) ⟨2498252, by rfl⟩ : syracuseStep 3331003 = 4996505) B4996505
theorem B4441337 : Blo 1973435 4441337 := bstep (se 2 (by rfl) ⟨1665501, by rfl⟩ : syracuseStep 4441337 = 3331003) B3331003
theorem B2960891 : Blo 1973435 2960891 := bstep (se 1 (by rfl) ⟨2220668, by rfl⟩ : syracuseStep 2960891 = 4441337) B4441337
theorem B1973927 : Blo 1973435 1973927 := bstep (se 1 (by rfl) ⟨1480445, by rfl⟩ : syracuseStep 1973927 = 2960891) B2960891
theorem B2220673 : Blo 1973435 2220673 := bbase (se 2 (by rfl) ⟨832752, by rfl⟩ : syracuseStep 2220673 = 1665505) (by norm_num)
theorem B2960897 : Blo 1973435 2960897 := bstep (se 2 (by rfl) ⟨1110336, by rfl⟩ : syracuseStep 2960897 = 2220673) B2220673
theorem B1973931 : Blo 1973435 1973931 := bstep (se 1 (by rfl) ⟨1480448, by rfl⟩ : syracuseStep 1973931 = 2960897) B2960897
theorem B4996525 : Blo 1973435 4996525 := bbase (se 3 (by rfl) ⟨936848, by rfl⟩ : syracuseStep 4996525 = 1873697) (by norm_num)
theorem B6662033 : Blo 1973435 6662033 := bstep (se 2 (by rfl) ⟨2498262, by rfl⟩ : syracuseStep 6662033 = 4996525) B4996525
theorem B4441355 : Blo 1973435 4441355 := bstep (se 1 (by rfl) ⟨3331016, by rfl⟩ : syracuseStep 4441355 = 6662033) B6662033
theorem B2960903 : Blo 1973435 2960903 := bstep (se 1 (by rfl) ⟨2220677, by rfl⟩ : syracuseStep 2960903 = 4441355) B4441355
theorem B1973935 : Blo 1973435 1973935 := bstep (se 1 (by rfl) ⟨1480451, by rfl⟩ : syracuseStep 1973935 = 2960903) B2960903
theorem B2960909 : Blo 1973435 2960909 := bbase (se 3 (by rfl) ⟨555170, by rfl⟩ : syracuseStep 2960909 = 1110341) (by norm_num)
theorem B1973939 : Blo 1973435 1973939 := bstep (se 1 (by rfl) ⟨1480454, by rfl⟩ : syracuseStep 1973939 = 2960909) B2960909
theorem B4441373 : Blo 1973435 4441373 := bbase (se 3 (by rfl) ⟨832757, by rfl⟩ : syracuseStep 4441373 = 1665515) (by norm_num)
theorem B2960915 : Blo 1973435 2960915 := bstep (se 1 (by rfl) ⟨2220686, by rfl⟩ : syracuseStep 2960915 = 4441373) B4441373
theorem B1973943 : Blo 1973435 1973943 := bstep (se 1 (by rfl) ⟨1480457, by rfl⟩ : syracuseStep 1973943 = 2960915) B2960915
theorem B3331037 : Blo 1973435 3331037 := bbase (se 3 (by rfl) ⟨624569, by rfl⟩ : syracuseStep 3331037 = 1249139) (by norm_num)
theorem B2220691 : Blo 1973435 2220691 := bstep (se 1 (by rfl) ⟨1665518, by rfl⟩ : syracuseStep 2220691 = 3331037) B3331037
theorem B2960921 : Blo 1973435 2960921 := bstep (se 2 (by rfl) ⟨1110345, by rfl⟩ : syracuseStep 2960921 = 2220691) B2220691
theorem B1973947 : Blo 1973435 1973947 := bstep (se 1 (by rfl) ⟨1480460, by rfl⟩ : syracuseStep 1973947 = 2960921) B2960921
theorem B9485669 : Blo 1973435 9485669 := bbase (se 4 (by rfl) ⟨889281, by rfl⟩ : syracuseStep 9485669 = 1778563) (by norm_num)
theorem B6323779 : Blo 1973435 6323779 := bstep (se 1 (by rfl) ⟨4742834, by rfl⟩ : syracuseStep 6323779 = 9485669) B9485669
theorem B8431705 : Blo 1973435 8431705 := bstep (se 2 (by rfl) ⟨3161889, by rfl⟩ : syracuseStep 8431705 = 6323779) B6323779
theorem B11242273 : Blo 1973435 11242273 := bstep (se 2 (by rfl) ⟨4215852, by rfl⟩ : syracuseStep 11242273 = 8431705) B8431705
theorem B14989697 : Blo 1973435 14989697 := bstep (se 2 (by rfl) ⟨5621136, by rfl⟩ : syracuseStep 14989697 = 11242273) B11242273
theorem B9993131 : Blo 1973435 9993131 := bstep (se 1 (by rfl) ⟨7494848, by rfl⟩ : syracuseStep 9993131 = 14989697) B14989697
theorem B6662087 : Blo 1973435 6662087 := bstep (se 1 (by rfl) ⟨4996565, by rfl⟩ : syracuseStep 6662087 = 9993131) B9993131
theorem B4441391 : Blo 1973435 4441391 := bstep (se 1 (by rfl) ⟨3331043, by rfl⟩ : syracuseStep 4441391 = 6662087) B6662087
theorem B2960927 : Blo 1973435 2960927 := bstep (se 1 (by rfl) ⟨2220695, by rfl⟩ : syracuseStep 2960927 = 4441391) B4441391
theorem B1973951 : Blo 1973435 1973951 := bstep (se 1 (by rfl) ⟨1480463, by rfl⟩ : syracuseStep 1973951 = 2960927) B2960927
theorem B2960933 : Blo 1973435 2960933 := bbase (se 4 (by rfl) ⟨277587, by rfl⟩ : syracuseStep 2960933 = 555175) (by norm_num)
theorem B1973955 : Blo 1973435 1973955 := bstep (se 1 (by rfl) ⟨1480466, by rfl⟩ : syracuseStep 1973955 = 2960933) B2960933
theorem B2498293 : Blo 1973435 2498293 := bbase (se 5 (by rfl) ⟨117107, by rfl⟩ : syracuseStep 2498293 = 234215) (by norm_num)
theorem B3331057 : Blo 1973435 3331057 := bstep (se 2 (by rfl) ⟨1249146, by rfl⟩ : syracuseStep 3331057 = 2498293) B2498293
theorem B4441409 : Blo 1973435 4441409 := bstep (se 2 (by rfl) ⟨1665528, by rfl⟩ : syracuseStep 4441409 = 3331057) B3331057
theorem B2960939 : Blo 1973435 2960939 := bstep (se 1 (by rfl) ⟨2220704, by rfl⟩ : syracuseStep 2960939 = 4441409) B4441409
theorem B1973959 : Blo 1973435 1973959 := bstep (se 1 (by rfl) ⟨1480469, by rfl⟩ : syracuseStep 1973959 = 2960939) B2960939
theorem B2220709 : Blo 1973435 2220709 := bbase (se 4 (by rfl) ⟨208191, by rfl⟩ : syracuseStep 2220709 = 416383) (by norm_num)
theorem B2960945 : Blo 1973435 2960945 := bstep (se 2 (by rfl) ⟨1110354, by rfl⟩ : syracuseStep 2960945 = 2220709) B2220709
theorem B1973963 : Blo 1973435 1973963 := bstep (se 1 (by rfl) ⟨1480472, by rfl⟩ : syracuseStep 1973963 = 2960945) B2960945
theorem B8335685 : Blo 1973435 8335685 := bbase (se 4 (by rfl) ⟨781470, by rfl⟩ : syracuseStep 8335685 = 1562941) (by norm_num)
theorem B5557123 : Blo 1973435 5557123 := bstep (se 1 (by rfl) ⟨4167842, by rfl⟩ : syracuseStep 5557123 = 8335685) B8335685
theorem B7409497 : Blo 1973435 7409497 := bstep (se 2 (by rfl) ⟨2778561, by rfl⟩ : syracuseStep 7409497 = 5557123) B5557123
theorem B9879329 : Blo 1973435 9879329 := bstep (se 2 (by rfl) ⟨3704748, by rfl⟩ : syracuseStep 9879329 = 7409497) B7409497
theorem B6586219 : Blo 1973435 6586219 := bstep (se 1 (by rfl) ⟨4939664, by rfl⟩ : syracuseStep 6586219 = 9879329) B9879329
theorem B8781625 : Blo 1973435 8781625 := bstep (se 2 (by rfl) ⟨3293109, by rfl⟩ : syracuseStep 8781625 = 6586219) B6586219
theorem B11708833 : Blo 1973435 11708833 := bstep (se 2 (by rfl) ⟨4390812, by rfl⟩ : syracuseStep 11708833 = 8781625) B8781625
theorem B15611777 : Blo 1973435 15611777 := bstep (se 2 (by rfl) ⟨5854416, by rfl⟩ : syracuseStep 15611777 = 11708833) B11708833
theorem B10407851 : Blo 1973435 10407851 := bstep (se 1 (by rfl) ⟨7805888, by rfl⟩ : syracuseStep 10407851 = 15611777) B15611777
theorem B6938567 : Blo 1973435 6938567 := bstep (se 1 (by rfl) ⟨5203925, by rfl⟩ : syracuseStep 6938567 = 10407851) B10407851
theorem B4625711 : Blo 1973435 4625711 := bstep (se 1 (by rfl) ⟨3469283, by rfl⟩ : syracuseStep 4625711 = 6938567) B6938567
theorem B3083807 : Blo 1973435 3083807 := bstep (se 1 (by rfl) ⟨2312855, by rfl⟩ : syracuseStep 3083807 = 4625711) B4625711
theorem B2055871 : Blo 1973435 2055871 := bstep (se 1 (by rfl) ⟨1541903, by rfl⟩ : syracuseStep 2055871 = 3083807) B3083807
theorem B10964645 : Blo 1973435 10964645 := bstep (se 4 (by rfl) ⟨1027935, by rfl⟩ : syracuseStep 10964645 = 2055871) B2055871
theorem B7309763 : Blo 1973435 7309763 := bstep (se 1 (by rfl) ⟨5482322, by rfl⟩ : syracuseStep 7309763 = 10964645) B10964645
theorem B4873175 : Blo 1973435 4873175 := bstep (se 1 (by rfl) ⟨3654881, by rfl⟩ : syracuseStep 4873175 = 7309763) B7309763
theorem B3248783 : Blo 1973435 3248783 := bstep (se 1 (by rfl) ⟨2436587, by rfl⟩ : syracuseStep 3248783 = 4873175) B4873175
theorem B2165855 : Blo 1973435 2165855 := bstep (se 1 (by rfl) ⟨1624391, by rfl⟩ : syracuseStep 2165855 = 3248783) B3248783
theorem B23102453 : Blo 1973435 23102453 := bstep (se 5 (by rfl) ⟨1082927, by rfl⟩ : syracuseStep 23102453 = 2165855) B2165855
theorem B61606541 : Blo 1973435 61606541 := bstep (se 3 (by rfl) ⟨11551226, by rfl⟩ : syracuseStep 61606541 = 23102453) B23102453
theorem B164284109 : Blo 1973435 164284109 := bstep (se 3 (by rfl) ⟨30803270, by rfl⟩ : syracuseStep 164284109 = 61606541) B61606541
theorem B109522739 : Blo 1973435 109522739 := bstep (se 1 (by rfl) ⟨82142054, by rfl⟩ : syracuseStep 109522739 = 164284109) B164284109
theorem B292060637 : Blo 1973435 292060637 := bstep (se 3 (by rfl) ⟨54761369, by rfl⟩ : syracuseStep 292060637 = 109522739) B109522739
theorem B194707091 : Blo 1973435 194707091 := bstep (se 1 (by rfl) ⟨146030318, by rfl⟩ : syracuseStep 194707091 = 292060637) B292060637
theorem B129804727 : Blo 1973435 129804727 := bstep (se 1 (by rfl) ⟨97353545, by rfl⟩ : syracuseStep 129804727 = 194707091) B194707091
theorem B173072969 : Blo 1973435 173072969 := bstep (se 2 (by rfl) ⟨64902363, by rfl⟩ : syracuseStep 173072969 = 129804727) B129804727
theorem B115381979 : Blo 1973435 115381979 := bstep (se 1 (by rfl) ⟨86536484, by rfl⟩ : syracuseStep 115381979 = 173072969) B173072969
theorem B76921319 : Blo 1973435 76921319 := bstep (se 1 (by rfl) ⟨57690989, by rfl⟩ : syracuseStep 76921319 = 115381979) B115381979
theorem B51280879 : Blo 1973435 51280879 := bstep (se 1 (by rfl) ⟨38460659, by rfl⟩ : syracuseStep 51280879 = 76921319) B76921319
theorem B68374505 : Blo 1973435 68374505 := bstep (se 2 (by rfl) ⟨25640439, by rfl⟩ : syracuseStep 68374505 = 51280879) B51280879
theorem B45583003 : Blo 1973435 45583003 := bstep (se 1 (by rfl) ⟨34187252, by rfl⟩ : syracuseStep 45583003 = 68374505) B68374505
theorem B243109349 : Blo 1973435 243109349 := bstep (se 4 (by rfl) ⟨22791501, by rfl⟩ : syracuseStep 243109349 = 45583003) B45583003
theorem B162072899 : Blo 1973435 162072899 := bstep (se 1 (by rfl) ⟨121554674, by rfl⟩ : syracuseStep 162072899 = 243109349) B243109349
theorem B108048599 : Blo 1973435 108048599 := bstep (se 1 (by rfl) ⟨81036449, by rfl⟩ : syracuseStep 108048599 = 162072899) B162072899
theorem B72032399 : Blo 1973435 72032399 := bstep (se 1 (by rfl) ⟨54024299, by rfl⟩ : syracuseStep 72032399 = 108048599) B108048599
theorem B48021599 : Blo 1973435 48021599 := bstep (se 1 (by rfl) ⟨36016199, by rfl⟩ : syracuseStep 48021599 = 72032399) B72032399
theorem B32014399 : Blo 1973435 32014399 := bstep (se 1 (by rfl) ⟨24010799, by rfl⟩ : syracuseStep 32014399 = 48021599) B48021599
theorem B42685865 : Blo 1973435 42685865 := bstep (se 2 (by rfl) ⟨16007199, by rfl⟩ : syracuseStep 42685865 = 32014399) B32014399
theorem B28457243 : Blo 1973435 28457243 := bstep (se 1 (by rfl) ⟨21342932, by rfl⟩ : syracuseStep 28457243 = 42685865) B42685865
theorem B18971495 : Blo 1973435 18971495 := bstep (se 1 (by rfl) ⟨14228621, by rfl⟩ : syracuseStep 18971495 = 28457243) B28457243
theorem B12647663 : Blo 1973435 12647663 := bstep (se 1 (by rfl) ⟨9485747, by rfl⟩ : syracuseStep 12647663 = 18971495) B18971495
theorem B8431775 : Blo 1973435 8431775 := bstep (se 1 (by rfl) ⟨6323831, by rfl⟩ : syracuseStep 8431775 = 12647663) B12647663
theorem B5621183 : Blo 1973435 5621183 := bstep (se 1 (by rfl) ⟨4215887, by rfl⟩ : syracuseStep 5621183 = 8431775) B8431775
theorem B3747455 : Blo 1973435 3747455 := bstep (se 1 (by rfl) ⟨2810591, by rfl⟩ : syracuseStep 3747455 = 5621183) B5621183
theorem B2498303 : Blo 1973435 2498303 := bstep (se 1 (by rfl) ⟨1873727, by rfl⟩ : syracuseStep 2498303 = 3747455) B3747455
theorem B6662141 : Blo 1973435 6662141 := bstep (se 3 (by rfl) ⟨1249151, by rfl⟩ : syracuseStep 6662141 = 2498303) B2498303
theorem B4441427 : Blo 1973435 4441427 := bstep (se 1 (by rfl) ⟨3331070, by rfl⟩ : syracuseStep 4441427 = 6662141) B6662141
theorem B2960951 : Blo 1973435 2960951 := bstep (se 1 (by rfl) ⟨2220713, by rfl⟩ : syracuseStep 2960951 = 4441427) B4441427
theorem B1973967 : Blo 1973435 1973967 := bstep (se 1 (by rfl) ⟨1480475, by rfl⟩ : syracuseStep 1973967 = 2960951) B2960951
theorem B2960957 : Blo 1973435 2960957 := bbase (se 3 (by rfl) ⟨555179, by rfl⟩ : syracuseStep 2960957 = 1110359) (by norm_num)
theorem B1973971 : Blo 1973435 1973971 := bstep (se 1 (by rfl) ⟨1480478, by rfl⟩ : syracuseStep 1973971 = 2960957) B2960957
theorem B4441445 : Blo 1973435 4441445 := bbase (se 4 (by rfl) ⟨416385, by rfl⟩ : syracuseStep 4441445 = 832771) (by norm_num)
theorem B2960963 : Blo 1973435 2960963 := bstep (se 1 (by rfl) ⟨2220722, by rfl⟩ : syracuseStep 2960963 = 4441445) B4441445
theorem B1973975 : Blo 1973435 1973975 := bstep (se 1 (by rfl) ⟨1480481, by rfl⟩ : syracuseStep 1973975 = 2960963) B2960963
theorem B4996637 : Blo 1973435 4996637 := bbase (se 3 (by rfl) ⟨936869, by rfl⟩ : syracuseStep 4996637 = 1873739) (by norm_num)
theorem B3331091 : Blo 1973435 3331091 := bstep (se 1 (by rfl) ⟨2498318, by rfl⟩ : syracuseStep 3331091 = 4996637) B4996637
theorem B2220727 : Blo 1973435 2220727 := bstep (se 1 (by rfl) ⟨1665545, by rfl⟩ : syracuseStep 2220727 = 3331091) B3331091
theorem B2960969 : Blo 1973435 2960969 := bstep (se 2 (by rfl) ⟨1110363, by rfl⟩ : syracuseStep 2960969 = 2220727) B2220727
theorem B1973979 : Blo 1973435 1973979 := bstep (se 1 (by rfl) ⟨1480484, by rfl⟩ : syracuseStep 1973979 = 2960969) B2960969
theorem B3747485 : Blo 1973435 3747485 := bbase (se 3 (by rfl) ⟨702653, by rfl⟩ : syracuseStep 3747485 = 1405307) (by norm_num)
theorem B9993293 : Blo 1973435 9993293 := bstep (se 3 (by rfl) ⟨1873742, by rfl⟩ : syracuseStep 9993293 = 3747485) B3747485
theorem B6662195 : Blo 1973435 6662195 := bstep (se 1 (by rfl) ⟨4996646, by rfl⟩ : syracuseStep 6662195 = 9993293) B9993293
theorem B4441463 : Blo 1973435 4441463 := bstep (se 1 (by rfl) ⟨3331097, by rfl⟩ : syracuseStep 4441463 = 6662195) B6662195
theorem B2960975 : Blo 1973435 2960975 := bstep (se 1 (by rfl) ⟨2220731, by rfl⟩ : syracuseStep 2960975 = 4441463) B4441463
theorem B1973983 : Blo 1973435 1973983 := bstep (se 1 (by rfl) ⟨1480487, by rfl⟩ : syracuseStep 1973983 = 2960975) B2960975
theorem B2960981 : Blo 1973435 2960981 := bbase (se 8 (by rfl) ⟨17349, by rfl⟩ : syracuseStep 2960981 = 34699) (by norm_num)
theorem B1973987 : Blo 1973435 1973987 := bstep (se 1 (by rfl) ⟨1480490, by rfl⟩ : syracuseStep 1973987 = 2960981) B2960981
theorem B8431877 : Blo 1973435 8431877 := bbase (se 4 (by rfl) ⟨790488, by rfl⟩ : syracuseStep 8431877 = 1580977) (by norm_num)
theorem B5621251 : Blo 1973435 5621251 := bstep (se 1 (by rfl) ⟨4215938, by rfl⟩ : syracuseStep 5621251 = 8431877) B8431877
theorem B7495001 : Blo 1973435 7495001 := bstep (se 2 (by rfl) ⟨2810625, by rfl⟩ : syracuseStep 7495001 = 5621251) B5621251
theorem B4996667 : Blo 1973435 4996667 := bstep (se 1 (by rfl) ⟨3747500, by rfl⟩ : syracuseStep 4996667 = 7495001) B7495001
theorem B3331111 : Blo 1973435 3331111 := bstep (se 1 (by rfl) ⟨2498333, by rfl⟩ : syracuseStep 3331111 = 4996667) B4996667
theorem B4441481 : Blo 1973435 4441481 := bstep (se 2 (by rfl) ⟨1665555, by rfl⟩ : syracuseStep 4441481 = 3331111) B3331111
theorem B2960987 : Blo 1973435 2960987 := bstep (se 1 (by rfl) ⟨2220740, by rfl⟩ : syracuseStep 2960987 = 4441481) B4441481
theorem B1973991 : Blo 1973435 1973991 := bstep (se 1 (by rfl) ⟨1480493, by rfl⟩ : syracuseStep 1973991 = 2960987) B2960987
theorem B2220745 : Blo 1973435 2220745 := bbase (se 2 (by rfl) ⟨832779, by rfl⟩ : syracuseStep 2220745 = 1665559) (by norm_num)
theorem B2960993 : Blo 1973435 2960993 := bstep (se 2 (by rfl) ⟨1110372, by rfl⟩ : syracuseStep 2960993 = 2220745) B2220745
theorem B1973995 : Blo 1973435 1973995 := bstep (se 1 (by rfl) ⟨1480496, by rfl⟩ : syracuseStep 1973995 = 2960993) B2960993
theorem B3557213 : Blo 1973435 3557213 := bbase (se 3 (by rfl) ⟨666977, by rfl⟩ : syracuseStep 3557213 = 1333955) (by norm_num)
theorem B2371475 : Blo 1973435 2371475 := bstep (se 1 (by rfl) ⟨1778606, by rfl⟩ : syracuseStep 2371475 = 3557213) B3557213
theorem B6323933 : Blo 1973435 6323933 := bstep (se 3 (by rfl) ⟨1185737, by rfl⟩ : syracuseStep 6323933 = 2371475) B2371475
theorem B16863821 : Blo 1973435 16863821 := bstep (se 3 (by rfl) ⟨3161966, by rfl⟩ : syracuseStep 16863821 = 6323933) B6323933
theorem B11242547 : Blo 1973435 11242547 := bstep (se 1 (by rfl) ⟨8431910, by rfl⟩ : syracuseStep 11242547 = 16863821) B16863821
theorem B7495031 : Blo 1973435 7495031 := bstep (se 1 (by rfl) ⟨5621273, by rfl⟩ : syracuseStep 7495031 = 11242547) B11242547
theorem B4996687 : Blo 1973435 4996687 := bstep (se 1 (by rfl) ⟨3747515, by rfl⟩ : syracuseStep 4996687 = 7495031) B7495031
theorem B6662249 : Blo 1973435 6662249 := bstep (se 2 (by rfl) ⟨2498343, by rfl⟩ : syracuseStep 6662249 = 4996687) B4996687
theorem B4441499 : Blo 1973435 4441499 := bstep (se 1 (by rfl) ⟨3331124, by rfl⟩ : syracuseStep 4441499 = 6662249) B6662249
theorem B2960999 : Blo 1973435 2960999 := bstep (se 1 (by rfl) ⟨2220749, by rfl⟩ : syracuseStep 2960999 = 4441499) B4441499
theorem B1973999 : Blo 1973435 1973999 := bstep (se 1 (by rfl) ⟨1480499, by rfl⟩ : syracuseStep 1973999 = 2960999) B2960999
theorem B2961005 : Blo 1973435 2961005 := bbase (se 3 (by rfl) ⟨555188, by rfl⟩ : syracuseStep 2961005 = 1110377) (by norm_num)
theorem B1974003 : Blo 1973435 1974003 := bstep (se 1 (by rfl) ⟨1480502, by rfl⟩ : syracuseStep 1974003 = 2961005) B2961005
theorem B4441517 : Blo 1973435 4441517 := bbase (se 3 (by rfl) ⟨832784, by rfl⟩ : syracuseStep 4441517 = 1665569) (by norm_num)
theorem B2961011 : Blo 1973435 2961011 := bstep (se 1 (by rfl) ⟨2220758, by rfl⟩ : syracuseStep 2961011 = 4441517) B4441517
theorem B1974007 : Blo 1973435 1974007 := bstep (se 1 (by rfl) ⟨1480505, by rfl⟩ : syracuseStep 1974007 = 2961011) B2961011
theorem B4742981 : Blo 1973435 4742981 := bbase (se 4 (by rfl) ⟨444654, by rfl⟩ : syracuseStep 4742981 = 889309) (by norm_num)
theorem B3161987 : Blo 1973435 3161987 := bstep (se 1 (by rfl) ⟨2371490, by rfl⟩ : syracuseStep 3161987 = 4742981) B4742981
theorem B2107991 : Blo 1973435 2107991 := bstep (se 1 (by rfl) ⟨1580993, by rfl⟩ : syracuseStep 2107991 = 3161987) B3161987
theorem B5621309 : Blo 1973435 5621309 := bstep (se 3 (by rfl) ⟨1053995, by rfl⟩ : syracuseStep 5621309 = 2107991) B2107991
theorem B3747539 : Blo 1973435 3747539 := bstep (se 1 (by rfl) ⟨2810654, by rfl⟩ : syracuseStep 3747539 = 5621309) B5621309
theorem B2498359 : Blo 1973435 2498359 := bstep (se 1 (by rfl) ⟨1873769, by rfl⟩ : syracuseStep 2498359 = 3747539) B3747539
theorem B3331145 : Blo 1973435 3331145 := bstep (se 2 (by rfl) ⟨1249179, by rfl⟩ : syracuseStep 3331145 = 2498359) B2498359
theorem B2220763 : Blo 1973435 2220763 := bstep (se 1 (by rfl) ⟨1665572, by rfl⟩ : syracuseStep 2220763 = 3331145) B3331145
theorem B2961017 : Blo 1973435 2961017 := bstep (se 2 (by rfl) ⟨1110381, by rfl⟩ : syracuseStep 2961017 = 2220763) B2220763
theorem B1974011 : Blo 1973435 1974011 := bstep (se 1 (by rfl) ⟨1480508, by rfl⟩ : syracuseStep 1974011 = 2961017) B2961017
theorem B10268005 : Blo 1973435 10268005 := bbase (se 4 (by rfl) ⟨962625, by rfl⟩ : syracuseStep 10268005 = 1925251) (by norm_num)
theorem B13690673 : Blo 1973435 13690673 := bstep (se 2 (by rfl) ⟨5134002, by rfl⟩ : syracuseStep 13690673 = 10268005) B10268005
theorem B9127115 : Blo 1973435 9127115 := bstep (se 1 (by rfl) ⟨6845336, by rfl⟩ : syracuseStep 9127115 = 13690673) B13690673
theorem B6084743 : Blo 1973435 6084743 := bstep (se 1 (by rfl) ⟨4563557, by rfl⟩ : syracuseStep 6084743 = 9127115) B9127115
theorem B16225981 : Blo 1973435 16225981 := bstep (se 3 (by rfl) ⟨3042371, by rfl⟩ : syracuseStep 16225981 = 6084743) B6084743
theorem B86538565 : Blo 1973435 86538565 := bstep (se 4 (by rfl) ⟨8112990, by rfl⟩ : syracuseStep 86538565 = 16225981) B16225981
theorem B115384753 : Blo 1973435 115384753 := bstep (se 2 (by rfl) ⟨43269282, by rfl⟩ : syracuseStep 115384753 = 86538565) B86538565
theorem B153846337 : Blo 1973435 153846337 := bstep (se 2 (by rfl) ⟨57692376, by rfl⟩ : syracuseStep 153846337 = 115384753) B115384753
theorem B205128449 : Blo 1973435 205128449 := bstep (se 2 (by rfl) ⟨76923168, by rfl⟩ : syracuseStep 205128449 = 153846337) B153846337
theorem B136752299 : Blo 1973435 136752299 := bstep (se 1 (by rfl) ⟨102564224, by rfl⟩ : syracuseStep 136752299 = 205128449) B205128449
theorem B91168199 : Blo 1973435 91168199 := bstep (se 1 (by rfl) ⟨68376149, by rfl⟩ : syracuseStep 91168199 = 136752299) B136752299
theorem B60778799 : Blo 1973435 60778799 := bstep (se 1 (by rfl) ⟨45584099, by rfl⟩ : syracuseStep 60778799 = 91168199) B91168199
theorem B40519199 : Blo 1973435 40519199 := bstep (se 1 (by rfl) ⟨30389399, by rfl⟩ : syracuseStep 40519199 = 60778799) B60778799
theorem B27012799 : Blo 1973435 27012799 := bstep (se 1 (by rfl) ⟨20259599, by rfl⟩ : syracuseStep 27012799 = 40519199) B40519199
theorem B36017065 : Blo 1973435 36017065 := bstep (se 2 (by rfl) ⟨13506399, by rfl⟩ : syracuseStep 36017065 = 27012799) B27012799
theorem B192091013 : Blo 1973435 192091013 := bstep (se 4 (by rfl) ⟨18008532, by rfl⟩ : syracuseStep 192091013 = 36017065) B36017065
theorem B128060675 : Blo 1973435 128060675 := bstep (se 1 (by rfl) ⟨96045506, by rfl⟩ : syracuseStep 128060675 = 192091013) B192091013
theorem B85373783 : Blo 1973435 85373783 := bstep (se 1 (by rfl) ⟨64030337, by rfl⟩ : syracuseStep 85373783 = 128060675) B128060675
theorem B56915855 : Blo 1973435 56915855 := bstep (se 1 (by rfl) ⟨42686891, by rfl⟩ : syracuseStep 56915855 = 85373783) B85373783
theorem B37943903 : Blo 1973435 37943903 := bstep (se 1 (by rfl) ⟨28457927, by rfl⟩ : syracuseStep 37943903 = 56915855) B56915855
theorem B25295935 : Blo 1973435 25295935 := bstep (se 1 (by rfl) ⟨18971951, by rfl⟩ : syracuseStep 25295935 = 37943903) B37943903
theorem B33727913 : Blo 1973435 33727913 := bstep (se 2 (by rfl) ⟨12647967, by rfl⟩ : syracuseStep 33727913 = 25295935) B25295935
theorem B22485275 : Blo 1973435 22485275 := bstep (se 1 (by rfl) ⟨16863956, by rfl⟩ : syracuseStep 22485275 = 33727913) B33727913
theorem B14990183 : Blo 1973435 14990183 := bstep (se 1 (by rfl) ⟨11242637, by rfl⟩ : syracuseStep 14990183 = 22485275) B22485275
theorem B9993455 : Blo 1973435 9993455 := bstep (se 1 (by rfl) ⟨7495091, by rfl⟩ : syracuseStep 9993455 = 14990183) B14990183
theorem B6662303 : Blo 1973435 6662303 := bstep (se 1 (by rfl) ⟨4996727, by rfl⟩ : syracuseStep 6662303 = 9993455) B9993455
theorem B4441535 : Blo 1973435 4441535 := bstep (se 1 (by rfl) ⟨3331151, by rfl⟩ : syracuseStep 4441535 = 6662303) B6662303
theorem B2961023 : Blo 1973435 2961023 := bstep (se 1 (by rfl) ⟨2220767, by rfl⟩ : syracuseStep 2961023 = 4441535) B4441535
theorem B1974015 : Blo 1973435 1974015 := bstep (se 1 (by rfl) ⟨1480511, by rfl⟩ : syracuseStep 1974015 = 2961023) B2961023
theorem B2961029 : Blo 1973435 2961029 := bbase (se 4 (by rfl) ⟨277596, by rfl⟩ : syracuseStep 2961029 = 555193) (by norm_num)
theorem B1974019 : Blo 1973435 1974019 := bstep (se 1 (by rfl) ⟨1480514, by rfl⟩ : syracuseStep 1974019 = 2961029) B2961029
theorem B3331165 : Blo 1973435 3331165 := bbase (se 3 (by rfl) ⟨624593, by rfl⟩ : syracuseStep 3331165 = 1249187) (by norm_num)
theorem B4441553 : Blo 1973435 4441553 := bstep (se 2 (by rfl) ⟨1665582, by rfl⟩ : syracuseStep 4441553 = 3331165) B3331165
theorem B2961035 : Blo 1973435 2961035 := bstep (se 1 (by rfl) ⟨2220776, by rfl⟩ : syracuseStep 2961035 = 4441553) B4441553
theorem B1974023 : Blo 1973435 1974023 := bstep (se 1 (by rfl) ⟨1480517, by rfl⟩ : syracuseStep 1974023 = 2961035) B2961035
theorem B2220781 : Blo 1973435 2220781 := bbase (se 3 (by rfl) ⟨416396, by rfl⟩ : syracuseStep 2220781 = 832793) (by norm_num)
theorem B2961041 : Blo 1973435 2961041 := bstep (se 2 (by rfl) ⟨1110390, by rfl⟩ : syracuseStep 2961041 = 2220781) B2220781
theorem B1974027 : Blo 1973435 1974027 := bstep (se 1 (by rfl) ⟨1480520, by rfl⟩ : syracuseStep 1974027 = 2961041) B2961041
theorem B6662357 : Blo 1973435 6662357 := bbase (se 7 (by rfl) ⟨78074, by rfl⟩ : syracuseStep 6662357 = 156149) (by norm_num)
theorem B4441571 : Blo 1973435 4441571 := bstep (se 1 (by rfl) ⟨3331178, by rfl⟩ : syracuseStep 4441571 = 6662357) B6662357
theorem B2961047 : Blo 1973435 2961047 := bstep (se 1 (by rfl) ⟨2220785, by rfl⟩ : syracuseStep 2961047 = 4441571) B4441571
theorem B1974031 : Blo 1973435 1974031 := bstep (se 1 (by rfl) ⟨1480523, by rfl⟩ : syracuseStep 1974031 = 2961047) B2961047
theorem B2961053 : Blo 1973435 2961053 := bbase (se 3 (by rfl) ⟨555197, by rfl⟩ : syracuseStep 2961053 = 1110395) (by norm_num)
theorem B1974035 : Blo 1973435 1974035 := bstep (se 1 (by rfl) ⟨1480526, by rfl⟩ : syracuseStep 1974035 = 2961053) B2961053
theorem B4441589 : Blo 1973435 4441589 := bbase (se 5 (by rfl) ⟨208199, by rfl⟩ : syracuseStep 4441589 = 416399) (by norm_num)
theorem B2961059 : Blo 1973435 2961059 := bstep (se 1 (by rfl) ⟨2220794, by rfl⟩ : syracuseStep 2961059 = 4441589) B4441589
theorem B1974039 : Blo 1973435 1974039 := bstep (se 1 (by rfl) ⟨1480529, by rfl⟩ : syracuseStep 1974039 = 2961059) B2961059
theorem B5064973 : Blo 1973435 5064973 := bbase (se 3 (by rfl) ⟨949682, by rfl⟩ : syracuseStep 5064973 = 1899365) (by norm_num)
theorem B27013189 : Blo 1973435 27013189 := bstep (se 4 (by rfl) ⟨2532486, by rfl⟩ : syracuseStep 27013189 = 5064973) B5064973
theorem B36017585 : Blo 1973435 36017585 := bstep (se 2 (by rfl) ⟨13506594, by rfl⟩ : syracuseStep 36017585 = 27013189) B27013189
theorem B24011723 : Blo 1973435 24011723 := bstep (se 1 (by rfl) ⟨18008792, by rfl⟩ : syracuseStep 24011723 = 36017585) B36017585
theorem B16007815 : Blo 1973435 16007815 := bstep (se 1 (by rfl) ⟨12005861, by rfl⟩ : syracuseStep 16007815 = 24011723) B24011723
theorem B21343753 : Blo 1973435 21343753 := bstep (se 2 (by rfl) ⟨8003907, by rfl⟩ : syracuseStep 21343753 = 16007815) B16007815
theorem B28458337 : Blo 1973435 28458337 := bstep (se 2 (by rfl) ⟨10671876, by rfl⟩ : syracuseStep 28458337 = 21343753) B21343753
theorem B37944449 : Blo 1973435 37944449 := bstep (se 2 (by rfl) ⟨14229168, by rfl⟩ : syracuseStep 37944449 = 28458337) B28458337
theorem B25296299 : Blo 1973435 25296299 := bstep (se 1 (by rfl) ⟨18972224, by rfl⟩ : syracuseStep 25296299 = 37944449) B37944449
theorem B16864199 : Blo 1973435 16864199 := bstep (se 1 (by rfl) ⟨12648149, by rfl⟩ : syracuseStep 16864199 = 25296299) B25296299
theorem B11242799 : Blo 1973435 11242799 := bstep (se 1 (by rfl) ⟨8432099, by rfl⟩ : syracuseStep 11242799 = 16864199) B16864199
theorem B7495199 : Blo 1973435 7495199 := bstep (se 1 (by rfl) ⟨5621399, by rfl⟩ : syracuseStep 7495199 = 11242799) B11242799
theorem B4996799 : Blo 1973435 4996799 := bstep (se 1 (by rfl) ⟨3747599, by rfl⟩ : syracuseStep 4996799 = 7495199) B7495199
theorem B3331199 : Blo 1973435 3331199 := bstep (se 1 (by rfl) ⟨2498399, by rfl⟩ : syracuseStep 3331199 = 4996799) B4996799
theorem B2220799 : Blo 1973435 2220799 := bstep (se 1 (by rfl) ⟨1665599, by rfl⟩ : syracuseStep 2220799 = 3331199) B3331199
theorem B2961065 : Blo 1973435 2961065 := bstep (se 2 (by rfl) ⟨1110399, by rfl⟩ : syracuseStep 2961065 = 2220799) B2220799
theorem B1974043 : Blo 1973435 1974043 := bstep (se 1 (by rfl) ⟨1480532, by rfl⟩ : syracuseStep 1974043 = 2961065) B2961065
theorem B2108029 : Blo 1973435 2108029 := bbase (se 3 (by rfl) ⟨395255, by rfl⟩ : syracuseStep 2108029 = 790511) (by norm_num)
theorem B2810705 : Blo 1973435 2810705 := bstep (se 2 (by rfl) ⟨1054014, by rfl⟩ : syracuseStep 2810705 = 2108029) B2108029
theorem B7495213 : Blo 1973435 7495213 := bstep (se 3 (by rfl) ⟨1405352, by rfl⟩ : syracuseStep 7495213 = 2810705) B2810705
theorem B9993617 : Blo 1973435 9993617 := bstep (se 2 (by rfl) ⟨3747606, by rfl⟩ : syracuseStep 9993617 = 7495213) B7495213
theorem B6662411 : Blo 1973435 6662411 := bstep (se 1 (by rfl) ⟨4996808, by rfl⟩ : syracuseStep 6662411 = 9993617) B9993617
theorem B4441607 : Blo 1973435 4441607 := bstep (se 1 (by rfl) ⟨3331205, by rfl⟩ : syracuseStep 4441607 = 6662411) B6662411
theorem B2961071 : Blo 1973435 2961071 := bstep (se 1 (by rfl) ⟨2220803, by rfl⟩ : syracuseStep 2961071 = 4441607) B4441607
theorem B1974047 : Blo 1973435 1974047 := bstep (se 1 (by rfl) ⟨1480535, by rfl⟩ : syracuseStep 1974047 = 2961071) B2961071
theorem B2961077 : Blo 1973435 2961077 := bbase (se 5 (by rfl) ⟨138800, by rfl⟩ : syracuseStep 2961077 = 277601) (by norm_num)
theorem B1974051 : Blo 1973435 1974051 := bstep (se 1 (by rfl) ⟨1480538, by rfl⟩ : syracuseStep 1974051 = 2961077) B2961077
theorem B4996829 : Blo 1973435 4996829 := bbase (se 3 (by rfl) ⟨936905, by rfl⟩ : syracuseStep 4996829 = 1873811) (by norm_num)
theorem B3331219 : Blo 1973435 3331219 := bstep (se 1 (by rfl) ⟨2498414, by rfl⟩ : syracuseStep 3331219 = 4996829) B4996829
theorem B4441625 : Blo 1973435 4441625 := bstep (se 2 (by rfl) ⟨1665609, by rfl⟩ : syracuseStep 4441625 = 3331219) B3331219
theorem B2961083 : Blo 1973435 2961083 := bstep (se 1 (by rfl) ⟨2220812, by rfl⟩ : syracuseStep 2961083 = 4441625) B4441625
theorem B1974055 : Blo 1973435 1974055 := bstep (se 1 (by rfl) ⟨1480541, by rfl⟩ : syracuseStep 1974055 = 2961083) B2961083
theorem B2220817 : Blo 1973435 2220817 := bbase (se 2 (by rfl) ⟨832806, by rfl⟩ : syracuseStep 2220817 = 1665613) (by norm_num)
theorem B2961089 : Blo 1973435 2961089 := bstep (se 2 (by rfl) ⟨1110408, by rfl⟩ : syracuseStep 2961089 = 2220817) B2220817
theorem B1974059 : Blo 1973435 1974059 := bstep (se 1 (by rfl) ⟨1480544, by rfl⟩ : syracuseStep 1974059 = 2961089) B2961089
theorem B3747637 : Blo 1973435 3747637 := bbase (se 5 (by rfl) ⟨175670, by rfl⟩ : syracuseStep 3747637 = 351341) (by norm_num)
theorem B4996849 : Blo 1973435 4996849 := bstep (se 2 (by rfl) ⟨1873818, by rfl⟩ : syracuseStep 4996849 = 3747637) B3747637
theorem B6662465 : Blo 1973435 6662465 := bstep (se 2 (by rfl) ⟨2498424, by rfl⟩ : syracuseStep 6662465 = 4996849) B4996849
theorem B4441643 : Blo 1973435 4441643 := bstep (se 1 (by rfl) ⟨3331232, by rfl⟩ : syracuseStep 4441643 = 6662465) B6662465
theorem B2961095 : Blo 1973435 2961095 := bstep (se 1 (by rfl) ⟨2220821, by rfl⟩ : syracuseStep 2961095 = 4441643) B4441643
theorem B1974063 : Blo 1973435 1974063 := bstep (se 1 (by rfl) ⟨1480547, by rfl⟩ : syracuseStep 1974063 = 2961095) B2961095
theorem B2961101 : Blo 1973435 2961101 := bbase (se 3 (by rfl) ⟨555206, by rfl⟩ : syracuseStep 2961101 = 1110413) (by norm_num)
theorem B1974067 : Blo 1973435 1974067 := bstep (se 1 (by rfl) ⟨1480550, by rfl⟩ : syracuseStep 1974067 = 2961101) B2961101
theorem B4441661 : Blo 1973435 4441661 := bbase (se 3 (by rfl) ⟨832811, by rfl⟩ : syracuseStep 4441661 = 1665623) (by norm_num)
theorem B2961107 : Blo 1973435 2961107 := bstep (se 1 (by rfl) ⟨2220830, by rfl⟩ : syracuseStep 2961107 = 4441661) B4441661
theorem B1974071 : Blo 1973435 1974071 := bstep (se 1 (by rfl) ⟨1480553, by rfl⟩ : syracuseStep 1974071 = 2961107) B2961107
theorem B3331253 : Blo 1973435 3331253 := bbase (se 5 (by rfl) ⟨156152, by rfl⟩ : syracuseStep 3331253 = 312305) (by norm_num)
theorem B2220835 : Blo 1973435 2220835 := bstep (se 1 (by rfl) ⟨1665626, by rfl⟩ : syracuseStep 2220835 = 3331253) B3331253
theorem B2961113 : Blo 1973435 2961113 := bstep (se 2 (by rfl) ⟨1110417, by rfl⟩ : syracuseStep 2961113 = 2220835) B2220835
theorem B1974075 : Blo 1973435 1974075 := bstep (se 1 (by rfl) ⟨1480556, by rfl⟩ : syracuseStep 1974075 = 2961113) B2961113
theorem B2403929 : Blo 1973435 2403929 := bbase (se 2 (by rfl) ⟨901473, by rfl⟩ : syracuseStep 2403929 = 1802947) (by norm_num)
theorem B6410477 : Blo 1973435 6410477 := bstep (se 3 (by rfl) ⟨1201964, by rfl⟩ : syracuseStep 6410477 = 2403929) B2403929
theorem B4273651 : Blo 1973435 4273651 := bstep (se 1 (by rfl) ⟨3205238, by rfl⟩ : syracuseStep 4273651 = 6410477) B6410477
theorem B5698201 : Blo 1973435 5698201 := bstep (se 2 (by rfl) ⟨2136825, by rfl⟩ : syracuseStep 5698201 = 4273651) B4273651
theorem B7597601 : Blo 1973435 7597601 := bstep (se 2 (by rfl) ⟨2849100, by rfl⟩ : syracuseStep 7597601 = 5698201) B5698201
theorem B5065067 : Blo 1973435 5065067 := bstep (se 1 (by rfl) ⟨3798800, by rfl⟩ : syracuseStep 5065067 = 7597601) B7597601
theorem B3376711 : Blo 1973435 3376711 := bstep (se 1 (by rfl) ⟨2532533, by rfl⟩ : syracuseStep 3376711 = 5065067) B5065067
theorem B18009125 : Blo 1973435 18009125 := bstep (se 4 (by rfl) ⟨1688355, by rfl⟩ : syracuseStep 18009125 = 3376711) B3376711
theorem B12006083 : Blo 1973435 12006083 := bstep (se 1 (by rfl) ⟨9004562, by rfl⟩ : syracuseStep 12006083 = 18009125) B18009125
theorem B8004055 : Blo 1973435 8004055 := bstep (se 1 (by rfl) ⟨6003041, by rfl⟩ : syracuseStep 8004055 = 12006083) B12006083
theorem B10672073 : Blo 1973435 10672073 := bstep (se 2 (by rfl) ⟨4002027, by rfl⟩ : syracuseStep 10672073 = 8004055) B8004055
theorem B7114715 : Blo 1973435 7114715 := bstep (se 1 (by rfl) ⟨5336036, by rfl⟩ : syracuseStep 7114715 = 10672073) B10672073
theorem B4743143 : Blo 1973435 4743143 := bstep (se 1 (by rfl) ⟨3557357, by rfl⟩ : syracuseStep 4743143 = 7114715) B7114715
theorem B3162095 : Blo 1973435 3162095 := bstep (se 1 (by rfl) ⟨2371571, by rfl⟩ : syracuseStep 3162095 = 4743143) B4743143
theorem B2108063 : Blo 1973435 2108063 := bstep (se 1 (by rfl) ⟨1581047, by rfl⟩ : syracuseStep 2108063 = 3162095) B3162095
theorem B5621501 : Blo 1973435 5621501 := bstep (se 3 (by rfl) ⟨1054031, by rfl⟩ : syracuseStep 5621501 = 2108063) B2108063
theorem B14990669 : Blo 1973435 14990669 := bstep (se 3 (by rfl) ⟨2810750, by rfl⟩ : syracuseStep 14990669 = 5621501) B5621501
theorem B9993779 : Blo 1973435 9993779 := bstep (se 1 (by rfl) ⟨7495334, by rfl⟩ : syracuseStep 9993779 = 14990669) B14990669
theorem B6662519 : Blo 1973435 6662519 := bstep (se 1 (by rfl) ⟨4996889, by rfl⟩ : syracuseStep 6662519 = 9993779) B9993779
theorem B4441679 : Blo 1973435 4441679 := bstep (se 1 (by rfl) ⟨3331259, by rfl⟩ : syracuseStep 4441679 = 6662519) B6662519
theorem B2961119 : Blo 1973435 2961119 := bstep (se 1 (by rfl) ⟨2220839, by rfl⟩ : syracuseStep 2961119 = 4441679) B4441679
theorem B1974079 : Blo 1973435 1974079 := bstep (se 1 (by rfl) ⟨1480559, by rfl⟩ : syracuseStep 1974079 = 2961119) B2961119
theorem B2961125 : Blo 1973435 2961125 := bbase (se 4 (by rfl) ⟨277605, by rfl⟩ : syracuseStep 2961125 = 555211) (by norm_num)
theorem B1974083 : Blo 1973435 1974083 := bstep (se 1 (by rfl) ⟨1480562, by rfl⟩ : syracuseStep 1974083 = 2961125) B2961125
theorem B5621525 : Blo 1973435 5621525 := bbase (se 6 (by rfl) ⟨131754, by rfl⟩ : syracuseStep 5621525 = 263509) (by norm_num)
theorem B3747683 : Blo 1973435 3747683 := bstep (se 1 (by rfl) ⟨2810762, by rfl⟩ : syracuseStep 3747683 = 5621525) B5621525
theorem B2498455 : Blo 1973435 2498455 := bstep (se 1 (by rfl) ⟨1873841, by rfl⟩ : syracuseStep 2498455 = 3747683) B3747683
theorem B3331273 : Blo 1973435 3331273 := bstep (se 2 (by rfl) ⟨1249227, by rfl⟩ : syracuseStep 3331273 = 2498455) B2498455
theorem B4441697 : Blo 1973435 4441697 := bstep (se 2 (by rfl) ⟨1665636, by rfl⟩ : syracuseStep 4441697 = 3331273) B3331273
theorem B2961131 : Blo 1973435 2961131 := bstep (se 1 (by rfl) ⟨2220848, by rfl⟩ : syracuseStep 2961131 = 4441697) B4441697
theorem B1974087 : Blo 1973435 1974087 := bstep (se 1 (by rfl) ⟨1480565, by rfl⟩ : syracuseStep 1974087 = 2961131) B2961131
theorem B2220853 : Blo 1973435 2220853 := bbase (se 5 (by rfl) ⟨104102, by rfl⟩ : syracuseStep 2220853 = 208205) (by norm_num)
theorem B2961137 : Blo 1973435 2961137 := bstep (se 2 (by rfl) ⟨1110426, by rfl⟩ : syracuseStep 2961137 = 2220853) B2220853
theorem B1974091 : Blo 1973435 1974091 := bstep (se 1 (by rfl) ⟨1480568, by rfl⟩ : syracuseStep 1974091 = 2961137) B2961137
theorem B2498465 : Blo 1973435 2498465 := bbase (se 2 (by rfl) ⟨936924, by rfl⟩ : syracuseStep 2498465 = 1873849) (by norm_num)
theorem B6662573 : Blo 1973435 6662573 := bstep (se 3 (by rfl) ⟨1249232, by rfl⟩ : syracuseStep 6662573 = 2498465) B2498465
theorem B4441715 : Blo 1973435 4441715 := bstep (se 1 (by rfl) ⟨3331286, by rfl⟩ : syracuseStep 4441715 = 6662573) B6662573
theorem B2961143 : Blo 1973435 2961143 := bstep (se 1 (by rfl) ⟨2220857, by rfl⟩ : syracuseStep 2961143 = 4441715) B4441715
theorem B1974095 : Blo 1973435 1974095 := bstep (se 1 (by rfl) ⟨1480571, by rfl⟩ : syracuseStep 1974095 = 2961143) B2961143
theorem B2961149 : Blo 1973435 2961149 := bbase (se 3 (by rfl) ⟨555215, by rfl⟩ : syracuseStep 2961149 = 1110431) (by norm_num)
theorem B1974099 : Blo 1973435 1974099 := bstep (se 1 (by rfl) ⟨1480574, by rfl⟩ : syracuseStep 1974099 = 2961149) B2961149
theorem B4441733 : Blo 1973435 4441733 := bbase (se 4 (by rfl) ⟨416412, by rfl⟩ : syracuseStep 4441733 = 832825) (by norm_num)
theorem B2961155 : Blo 1973435 2961155 := bstep (se 1 (by rfl) ⟨2220866, by rfl⟩ : syracuseStep 2961155 = 4441733) B4441733
theorem B1974103 : Blo 1973435 1974103 := bstep (se 1 (by rfl) ⟨1480577, by rfl⟩ : syracuseStep 1974103 = 2961155) B2961155
theorem B4002085 : Blo 1973435 4002085 := bbase (se 4 (by rfl) ⟨375195, by rfl⟩ : syracuseStep 4002085 = 750391) (by norm_num)
theorem B5336113 : Blo 1973435 5336113 := bstep (se 2 (by rfl) ⟨2001042, by rfl⟩ : syracuseStep 5336113 = 4002085) B4002085
theorem B7114817 : Blo 1973435 7114817 := bstep (se 2 (by rfl) ⟨2668056, by rfl⟩ : syracuseStep 7114817 = 5336113) B5336113
theorem B4743211 : Blo 1973435 4743211 := bstep (se 1 (by rfl) ⟨3557408, by rfl⟩ : syracuseStep 4743211 = 7114817) B7114817
theorem B6324281 : Blo 1973435 6324281 := bstep (se 2 (by rfl) ⟨2371605, by rfl⟩ : syracuseStep 6324281 = 4743211) B4743211
theorem B4216187 : Blo 1973435 4216187 := bstep (se 1 (by rfl) ⟨3162140, by rfl⟩ : syracuseStep 4216187 = 6324281) B6324281
theorem B2810791 : Blo 1973435 2810791 := bstep (se 1 (by rfl) ⟨2108093, by rfl⟩ : syracuseStep 2810791 = 4216187) B4216187
theorem B3747721 : Blo 1973435 3747721 := bstep (se 2 (by rfl) ⟨1405395, by rfl⟩ : syracuseStep 3747721 = 2810791) B2810791
theorem B4996961 : Blo 1973435 4996961 := bstep (se 2 (by rfl) ⟨1873860, by rfl⟩ : syracuseStep 4996961 = 3747721) B3747721
theorem B3331307 : Blo 1973435 3331307 := bstep (se 1 (by rfl) ⟨2498480, by rfl⟩ : syracuseStep 3331307 = 4996961) B4996961
theorem B2220871 : Blo 1973435 2220871 := bstep (se 1 (by rfl) ⟨1665653, by rfl⟩ : syracuseStep 2220871 = 3331307) B3331307
theorem B2961161 : Blo 1973435 2961161 := bstep (se 2 (by rfl) ⟨1110435, by rfl⟩ : syracuseStep 2961161 = 2220871) B2220871
theorem B1974107 : Blo 1973435 1974107 := bstep (se 1 (by rfl) ⟨1480580, by rfl⟩ : syracuseStep 1974107 = 2961161) B2961161
theorem B9993941 : Blo 1973435 9993941 := bbase (se 7 (by rfl) ⟨117116, by rfl⟩ : syracuseStep 9993941 = 234233) (by norm_num)
theorem B6662627 : Blo 1973435 6662627 := bstep (se 1 (by rfl) ⟨4996970, by rfl⟩ : syracuseStep 6662627 = 9993941) B9993941
theorem B4441751 : Blo 1973435 4441751 := bstep (se 1 (by rfl) ⟨3331313, by rfl⟩ : syracuseStep 4441751 = 6662627) B6662627
theorem B2961167 : Blo 1973435 2961167 := bstep (se 1 (by rfl) ⟨2220875, by rfl⟩ : syracuseStep 2961167 = 4441751) B4441751
theorem B1974111 : Blo 1973435 1974111 := bstep (se 1 (by rfl) ⟨1480583, by rfl⟩ : syracuseStep 1974111 = 2961167) B2961167
theorem B2961173 : Blo 1973435 2961173 := bbase (se 6 (by rfl) ⟨69402, by rfl⟩ : syracuseStep 2961173 = 138805) (by norm_num)
theorem B1974115 : Blo 1973435 1974115 := bstep (se 1 (by rfl) ⟨1480586, by rfl⟩ : syracuseStep 1974115 = 2961173) B2961173
theorem B6753557 : Blo 1973435 6753557 := bbase (se 6 (by rfl) ⟨158286, by rfl⟩ : syracuseStep 6753557 = 316573) (by norm_num)
theorem B18009485 : Blo 1973435 18009485 := bstep (se 3 (by rfl) ⟨3376778, by rfl⟩ : syracuseStep 18009485 = 6753557) B6753557
theorem B12006323 : Blo 1973435 12006323 := bstep (se 1 (by rfl) ⟨9004742, by rfl⟩ : syracuseStep 12006323 = 18009485) B18009485
theorem B8004215 : Blo 1973435 8004215 := bstep (se 1 (by rfl) ⟨6003161, by rfl⟩ : syracuseStep 8004215 = 12006323) B12006323
theorem B21344573 : Blo 1973435 21344573 := bstep (se 3 (by rfl) ⟨4002107, by rfl⟩ : syracuseStep 21344573 = 8004215) B8004215
theorem B56918861 : Blo 1973435 56918861 := bstep (se 3 (by rfl) ⟨10672286, by rfl⟩ : syracuseStep 56918861 = 21344573) B21344573
theorem B37945907 : Blo 1973435 37945907 := bstep (se 1 (by rfl) ⟨28459430, by rfl⟩ : syracuseStep 37945907 = 56918861) B56918861
theorem B25297271 : Blo 1973435 25297271 := bstep (se 1 (by rfl) ⟨18972953, by rfl⟩ : syracuseStep 25297271 = 37945907) B37945907
theorem B16864847 : Blo 1973435 16864847 := bstep (se 1 (by rfl) ⟨12648635, by rfl⟩ : syracuseStep 16864847 = 25297271) B25297271
theorem B11243231 : Blo 1973435 11243231 := bstep (se 1 (by rfl) ⟨8432423, by rfl⟩ : syracuseStep 11243231 = 16864847) B16864847
theorem B7495487 : Blo 1973435 7495487 := bstep (se 1 (by rfl) ⟨5621615, by rfl⟩ : syracuseStep 7495487 = 11243231) B11243231
theorem B4996991 : Blo 1973435 4996991 := bstep (se 1 (by rfl) ⟨3747743, by rfl⟩ : syracuseStep 4996991 = 7495487) B7495487
theorem B3331327 : Blo 1973435 3331327 := bstep (se 1 (by rfl) ⟨2498495, by rfl⟩ : syracuseStep 3331327 = 4996991) B4996991
theorem B4441769 : Blo 1973435 4441769 := bstep (se 2 (by rfl) ⟨1665663, by rfl⟩ : syracuseStep 4441769 = 3331327) B3331327
theorem B2961179 : Blo 1973435 2961179 := bstep (se 1 (by rfl) ⟨2220884, by rfl⟩ : syracuseStep 2961179 = 4441769) B4441769
theorem B1974119 : Blo 1973435 1974119 := bstep (se 1 (by rfl) ⟨1480589, by rfl⟩ : syracuseStep 1974119 = 2961179) B2961179
theorem B2220889 : Blo 1973435 2220889 := bbase (se 2 (by rfl) ⟨832833, by rfl⟩ : syracuseStep 2220889 = 1665667) (by norm_num)
theorem B2961185 : Blo 1973435 2961185 := bstep (se 2 (by rfl) ⟨1110444, by rfl⟩ : syracuseStep 2961185 = 2220889) B2220889
theorem B1974123 : Blo 1973435 1974123 := bstep (se 1 (by rfl) ⟨1480592, by rfl⟩ : syracuseStep 1974123 = 2961185) B2961185
theorem B4216229 : Blo 1973435 4216229 := bbase (se 4 (by rfl) ⟨395271, by rfl⟩ : syracuseStep 4216229 = 790543) (by norm_num)
theorem B2810819 : Blo 1973435 2810819 := bstep (se 1 (by rfl) ⟨2108114, by rfl⟩ : syracuseStep 2810819 = 4216229) B4216229
theorem B7495517 : Blo 1973435 7495517 := bstep (se 3 (by rfl) ⟨1405409, by rfl⟩ : syracuseStep 7495517 = 2810819) B2810819
theorem B4997011 : Blo 1973435 4997011 := bstep (se 1 (by rfl) ⟨3747758, by rfl⟩ : syracuseStep 4997011 = 7495517) B7495517
theorem B6662681 : Blo 1973435 6662681 := bstep (se 2 (by rfl) ⟨2498505, by rfl⟩ : syracuseStep 6662681 = 4997011) B4997011
theorem B4441787 : Blo 1973435 4441787 := bstep (se 1 (by rfl) ⟨3331340, by rfl⟩ : syracuseStep 4441787 = 6662681) B6662681
theorem B2961191 : Blo 1973435 2961191 := bstep (se 1 (by rfl) ⟨2220893, by rfl⟩ : syracuseStep 2961191 = 4441787) B4441787
theorem B1974127 : Blo 1973435 1974127 := bstep (se 1 (by rfl) ⟨1480595, by rfl⟩ : syracuseStep 1974127 = 2961191) B2961191
theorem B2961197 : Blo 1973435 2961197 := bbase (se 3 (by rfl) ⟨555224, by rfl⟩ : syracuseStep 2961197 = 1110449) (by norm_num)
theorem B1974131 : Blo 1973435 1974131 := bstep (se 1 (by rfl) ⟨1480598, by rfl⟩ : syracuseStep 1974131 = 2961197) B2961197
theorem B4441805 : Blo 1973435 4441805 := bbase (se 3 (by rfl) ⟨832838, by rfl⟩ : syracuseStep 4441805 = 1665677) (by norm_num)
theorem B2961203 : Blo 1973435 2961203 := bstep (se 1 (by rfl) ⟨2220902, by rfl⟩ : syracuseStep 2961203 = 4441805) B4441805
theorem B1974135 : Blo 1973435 1974135 := bstep (se 1 (by rfl) ⟨1480601, by rfl⟩ : syracuseStep 1974135 = 2961203) B2961203
theorem B2498521 : Blo 1973435 2498521 := bbase (se 2 (by rfl) ⟨936945, by rfl⟩ : syracuseStep 2498521 = 1873891) (by norm_num)
theorem B3331361 : Blo 1973435 3331361 := bstep (se 2 (by rfl) ⟨1249260, by rfl⟩ : syracuseStep 3331361 = 2498521) B2498521
theorem B2220907 : Blo 1973435 2220907 := bstep (se 1 (by rfl) ⟨1665680, by rfl⟩ : syracuseStep 2220907 = 3331361) B3331361
theorem B2961209 : Blo 1973435 2961209 := bstep (se 2 (by rfl) ⟨1110453, by rfl⟩ : syracuseStep 2961209 = 2220907) B2220907
theorem B1974139 : Blo 1973435 1974139 := bstep (se 1 (by rfl) ⟨1480604, by rfl⟩ : syracuseStep 1974139 = 2961209) B2961209
theorem B3162197 : Blo 1973435 3162197 := bbase (se 8 (by rfl) ⟨18528, by rfl⟩ : syracuseStep 3162197 = 37057) (by norm_num)
theorem B8432525 : Blo 1973435 8432525 := bstep (se 3 (by rfl) ⟨1581098, by rfl⟩ : syracuseStep 8432525 = 3162197) B3162197
theorem B22486733 : Blo 1973435 22486733 := bstep (se 3 (by rfl) ⟨4216262, by rfl⟩ : syracuseStep 22486733 = 8432525) B8432525
theorem B14991155 : Blo 1973435 14991155 := bstep (se 1 (by rfl) ⟨11243366, by rfl⟩ : syracuseStep 14991155 = 22486733) B22486733
theorem B9994103 : Blo 1973435 9994103 := bstep (se 1 (by rfl) ⟨7495577, by rfl⟩ : syracuseStep 9994103 = 14991155) B14991155
theorem B6662735 : Blo 1973435 6662735 := bstep (se 1 (by rfl) ⟨4997051, by rfl⟩ : syracuseStep 6662735 = 9994103) B9994103
theorem B4441823 : Blo 1973435 4441823 := bstep (se 1 (by rfl) ⟨3331367, by rfl⟩ : syracuseStep 4441823 = 6662735) B6662735
theorem B2961215 : Blo 1973435 2961215 := bstep (se 1 (by rfl) ⟨2220911, by rfl⟩ : syracuseStep 2961215 = 4441823) B4441823
theorem B1974143 : Blo 1973435 1974143 := bstep (se 1 (by rfl) ⟨1480607, by rfl⟩ : syracuseStep 1974143 = 2961215) B2961215
theorem B2961221 : Blo 1973435 2961221 := bbase (se 4 (by rfl) ⟨277614, by rfl⟩ : syracuseStep 2961221 = 555229) (by norm_num)
theorem B1974147 : Blo 1973435 1974147 := bstep (se 1 (by rfl) ⟨1480610, by rfl⟩ : syracuseStep 1974147 = 2961221) B2961221
theorem B3331381 : Blo 1973435 3331381 := bbase (se 5 (by rfl) ⟨156158, by rfl⟩ : syracuseStep 3331381 = 312317) (by norm_num)
theorem B4441841 : Blo 1973435 4441841 := bstep (se 2 (by rfl) ⟨1665690, by rfl⟩ : syracuseStep 4441841 = 3331381) B3331381
theorem B2961227 : Blo 1973435 2961227 := bstep (se 1 (by rfl) ⟨2220920, by rfl⟩ : syracuseStep 2961227 = 4441841) B4441841
theorem B1974151 : Blo 1973435 1974151 := bstep (se 1 (by rfl) ⟨1480613, by rfl⟩ : syracuseStep 1974151 = 2961227) B2961227
theorem B2220925 : Blo 1973435 2220925 := bbase (se 3 (by rfl) ⟨416423, by rfl⟩ : syracuseStep 2220925 = 832847) (by norm_num)
theorem B2961233 : Blo 1973435 2961233 := bstep (se 2 (by rfl) ⟨1110462, by rfl⟩ : syracuseStep 2961233 = 2220925) B2220925
theorem B1974155 : Blo 1973435 1974155 := bstep (se 1 (by rfl) ⟨1480616, by rfl⟩ : syracuseStep 1974155 = 2961233) B2961233
theorem B6662789 : Blo 1973435 6662789 := bbase (se 4 (by rfl) ⟨624636, by rfl⟩ : syracuseStep 6662789 = 1249273) (by norm_num)
theorem B4441859 : Blo 1973435 4441859 := bstep (se 1 (by rfl) ⟨3331394, by rfl⟩ : syracuseStep 4441859 = 6662789) B6662789
theorem B2961239 : Blo 1973435 2961239 := bstep (se 1 (by rfl) ⟨2220929, by rfl⟩ : syracuseStep 2961239 = 4441859) B4441859
theorem B1974159 : Blo 1973435 1974159 := bstep (se 1 (by rfl) ⟨1480619, by rfl⟩ : syracuseStep 1974159 = 2961239) B2961239
theorem B2961245 : Blo 1973435 2961245 := bbase (se 3 (by rfl) ⟨555233, by rfl⟩ : syracuseStep 2961245 = 1110467) (by norm_num)
theorem B1974163 : Blo 1973435 1974163 := bstep (se 1 (by rfl) ⟨1480622, by rfl⟩ : syracuseStep 1974163 = 2961245) B2961245
theorem B4441877 : Blo 1973435 4441877 := bbase (se 6 (by rfl) ⟨104106, by rfl⟩ : syracuseStep 4441877 = 208213) (by norm_num)
theorem B2961251 : Blo 1973435 2961251 := bstep (se 1 (by rfl) ⟨2220938, by rfl⟩ : syracuseStep 2961251 = 4441877) B4441877
theorem B1974167 : Blo 1973435 1974167 := bstep (se 1 (by rfl) ⟨1480625, by rfl⟩ : syracuseStep 1974167 = 2961251) B2961251
theorem B7495685 : Blo 1973435 7495685 := bbase (se 4 (by rfl) ⟨702720, by rfl⟩ : syracuseStep 7495685 = 1405441) (by norm_num)
theorem B4997123 : Blo 1973435 4997123 := bstep (se 1 (by rfl) ⟨3747842, by rfl⟩ : syracuseStep 4997123 = 7495685) B7495685
theorem B3331415 : Blo 1973435 3331415 := bstep (se 1 (by rfl) ⟨2498561, by rfl⟩ : syracuseStep 3331415 = 4997123) B4997123
theorem B2220943 : Blo 1973435 2220943 := bstep (se 1 (by rfl) ⟨1665707, by rfl⟩ : syracuseStep 2220943 = 3331415) B3331415
theorem B2961257 : Blo 1973435 2961257 := bstep (se 2 (by rfl) ⟨1110471, by rfl⟩ : syracuseStep 2961257 = 2220943) B2220943
theorem B1974171 : Blo 1973435 1974171 := bstep (se 1 (by rfl) ⟨1480628, by rfl⟩ : syracuseStep 1974171 = 2961257) B2961257
theorem B4743373 : Blo 1973435 4743373 := bbase (se 3 (by rfl) ⟨889382, by rfl⟩ : syracuseStep 4743373 = 1778765) (by norm_num)
theorem B6324497 : Blo 1973435 6324497 := bstep (se 2 (by rfl) ⟨2371686, by rfl⟩ : syracuseStep 6324497 = 4743373) B4743373
theorem B4216331 : Blo 1973435 4216331 := bstep (se 1 (by rfl) ⟨3162248, by rfl⟩ : syracuseStep 4216331 = 6324497) B6324497
theorem B11243549 : Blo 1973435 11243549 := bstep (se 3 (by rfl) ⟨2108165, by rfl⟩ : syracuseStep 11243549 = 4216331) B4216331
theorem B7495699 : Blo 1973435 7495699 := bstep (se 1 (by rfl) ⟨5621774, by rfl⟩ : syracuseStep 7495699 = 11243549) B11243549
theorem B9994265 : Blo 1973435 9994265 := bstep (se 2 (by rfl) ⟨3747849, by rfl⟩ : syracuseStep 9994265 = 7495699) B7495699
theorem B6662843 : Blo 1973435 6662843 := bstep (se 1 (by rfl) ⟨4997132, by rfl⟩ : syracuseStep 6662843 = 9994265) B9994265
theorem B4441895 : Blo 1973435 4441895 := bstep (se 1 (by rfl) ⟨3331421, by rfl⟩ : syracuseStep 4441895 = 6662843) B6662843
theorem B2961263 : Blo 1973435 2961263 := bstep (se 1 (by rfl) ⟨2220947, by rfl⟩ : syracuseStep 2961263 = 4441895) B4441895
theorem B1974175 : Blo 1973435 1974175 := bstep (se 1 (by rfl) ⟨1480631, by rfl⟩ : syracuseStep 1974175 = 2961263) B2961263
theorem B2961269 : Blo 1973435 2961269 := bbase (se 5 (by rfl) ⟨138809, by rfl⟩ : syracuseStep 2961269 = 277619) (by norm_num)
theorem B1974179 : Blo 1973435 1974179 := bstep (se 1 (by rfl) ⟨1480634, by rfl⟩ : syracuseStep 1974179 = 2961269) B2961269
theorem B4216349 : Blo 1973435 4216349 := bbase (se 3 (by rfl) ⟨790565, by rfl⟩ : syracuseStep 4216349 = 1581131) (by norm_num)
theorem B2810899 : Blo 1973435 2810899 := bstep (se 1 (by rfl) ⟨2108174, by rfl⟩ : syracuseStep 2810899 = 4216349) B4216349
theorem B3747865 : Blo 1973435 3747865 := bstep (se 2 (by rfl) ⟨1405449, by rfl⟩ : syracuseStep 3747865 = 2810899) B2810899
theorem B4997153 : Blo 1973435 4997153 := bstep (se 2 (by rfl) ⟨1873932, by rfl⟩ : syracuseStep 4997153 = 3747865) B3747865
theorem B3331435 : Blo 1973435 3331435 := bstep (se 1 (by rfl) ⟨2498576, by rfl⟩ : syracuseStep 3331435 = 4997153) B4997153
theorem B4441913 : Blo 1973435 4441913 := bstep (se 2 (by rfl) ⟨1665717, by rfl⟩ : syracuseStep 4441913 = 3331435) B3331435
theorem B2961275 : Blo 1973435 2961275 := bstep (se 1 (by rfl) ⟨2220956, by rfl⟩ : syracuseStep 2961275 = 4441913) B4441913
theorem B1974183 : Blo 1973435 1974183 := bstep (se 1 (by rfl) ⟨1480637, by rfl⟩ : syracuseStep 1974183 = 2961275) B2961275
theorem B2220961 : Blo 1973435 2220961 := bbase (se 2 (by rfl) ⟨832860, by rfl⟩ : syracuseStep 2220961 = 1665721) (by norm_num)
theorem B2961281 : Blo 1973435 2961281 := bstep (se 2 (by rfl) ⟨1110480, by rfl⟩ : syracuseStep 2961281 = 2220961) B2220961
theorem B1974187 : Blo 1973435 1974187 := bstep (se 1 (by rfl) ⟨1480640, by rfl⟩ : syracuseStep 1974187 = 2961281) B2961281
theorem B4997173 : Blo 1973435 4997173 := bbase (se 5 (by rfl) ⟨234242, by rfl⟩ : syracuseStep 4997173 = 468485) (by norm_num)
theorem B6662897 : Blo 1973435 6662897 := bstep (se 2 (by rfl) ⟨2498586, by rfl⟩ : syracuseStep 6662897 = 4997173) B4997173
theorem B4441931 : Blo 1973435 4441931 := bstep (se 1 (by rfl) ⟨3331448, by rfl⟩ : syracuseStep 4441931 = 6662897) B6662897
theorem B2961287 : Blo 1973435 2961287 := bstep (se 1 (by rfl) ⟨2220965, by rfl⟩ : syracuseStep 2961287 = 4441931) B4441931
theorem B1974191 : Blo 1973435 1974191 := bstep (se 1 (by rfl) ⟨1480643, by rfl⟩ : syracuseStep 1974191 = 2961287) B2961287
theorem B2961293 : Blo 1973435 2961293 := bbase (se 3 (by rfl) ⟨555242, by rfl⟩ : syracuseStep 2961293 = 1110485) (by norm_num)
theorem B1974195 : Blo 1973435 1974195 := bstep (se 1 (by rfl) ⟨1480646, by rfl⟩ : syracuseStep 1974195 = 2961293) B2961293
theorem B4441949 : Blo 1973435 4441949 := bbase (se 3 (by rfl) ⟨832865, by rfl⟩ : syracuseStep 4441949 = 1665731) (by norm_num)
theorem B2961299 : Blo 1973435 2961299 := bstep (se 1 (by rfl) ⟨2220974, by rfl⟩ : syracuseStep 2961299 = 4441949) B4441949
theorem B1974199 : Blo 1973435 1974199 := bstep (se 1 (by rfl) ⟨1480649, by rfl⟩ : syracuseStep 1974199 = 2961299) B2961299
theorem B3331469 : Blo 1973435 3331469 := bbase (se 3 (by rfl) ⟨624650, by rfl⟩ : syracuseStep 3331469 = 1249301) (by norm_num)
theorem B2220979 : Blo 1973435 2220979 := bstep (se 1 (by rfl) ⟨1665734, by rfl⟩ : syracuseStep 2220979 = 3331469) B3331469
theorem B2961305 : Blo 1973435 2961305 := bstep (se 2 (by rfl) ⟨1110489, by rfl⟩ : syracuseStep 2961305 = 2220979) B2220979
theorem B1974203 : Blo 1973435 1974203 := bstep (se 1 (by rfl) ⟨1480652, by rfl⟩ : syracuseStep 1974203 = 2961305) B2961305
theorem B4502573 : Blo 1973435 4502573 := bbase (se 3 (by rfl) ⟨844232, by rfl⟩ : syracuseStep 4502573 = 1688465) (by norm_num)
theorem B3001715 : Blo 1973435 3001715 := bstep (se 1 (by rfl) ⟨2251286, by rfl⟩ : syracuseStep 3001715 = 4502573) B4502573
theorem B2001143 : Blo 1973435 2001143 := bstep (se 1 (by rfl) ⟨1500857, by rfl⟩ : syracuseStep 2001143 = 3001715) B3001715
theorem B5336381 : Blo 1973435 5336381 := bstep (se 3 (by rfl) ⟨1000571, by rfl⟩ : syracuseStep 5336381 = 2001143) B2001143
theorem B14230349 : Blo 1973435 14230349 := bstep (se 3 (by rfl) ⟨2668190, by rfl⟩ : syracuseStep 14230349 = 5336381) B5336381
theorem B9486899 : Blo 1973435 9486899 := bstep (se 1 (by rfl) ⟨7115174, by rfl⟩ : syracuseStep 9486899 = 14230349) B14230349
theorem B6324599 : Blo 1973435 6324599 := bstep (se 1 (by rfl) ⟨4743449, by rfl⟩ : syracuseStep 6324599 = 9486899) B9486899
theorem B16865597 : Blo 1973435 16865597 := bstep (se 3 (by rfl) ⟨3162299, by rfl⟩ : syracuseStep 16865597 = 6324599) B6324599
theorem B11243731 : Blo 1973435 11243731 := bstep (se 1 (by rfl) ⟨8432798, by rfl⟩ : syracuseStep 11243731 = 16865597) B16865597
theorem B14991641 : Blo 1973435 14991641 := bstep (se 2 (by rfl) ⟨5621865, by rfl⟩ : syracuseStep 14991641 = 11243731) B11243731
theorem B9994427 : Blo 1973435 9994427 := bstep (se 1 (by rfl) ⟨7495820, by rfl⟩ : syracuseStep 9994427 = 14991641) B14991641
theorem B6662951 : Blo 1973435 6662951 := bstep (se 1 (by rfl) ⟨4997213, by rfl⟩ : syracuseStep 6662951 = 9994427) B9994427
theorem B4441967 : Blo 1973435 4441967 := bstep (se 1 (by rfl) ⟨3331475, by rfl⟩ : syracuseStep 4441967 = 6662951) B6662951
theorem B2961311 : Blo 1973435 2961311 := bstep (se 1 (by rfl) ⟨2220983, by rfl⟩ : syracuseStep 2961311 = 4441967) B4441967
theorem B1974207 : Blo 1973435 1974207 := bstep (se 1 (by rfl) ⟨1480655, by rfl⟩ : syracuseStep 1974207 = 2961311) B2961311
theorem B2961317 : Blo 1973435 2961317 := bbase (se 4 (by rfl) ⟨277623, by rfl⟩ : syracuseStep 2961317 = 555247) (by norm_num)
theorem B1974211 : Blo 1973435 1974211 := bstep (se 1 (by rfl) ⟨1480658, by rfl⟩ : syracuseStep 1974211 = 2961317) B2961317
theorem B2498617 : Blo 1973435 2498617 := bbase (se 2 (by rfl) ⟨936981, by rfl⟩ : syracuseStep 2498617 = 1873963) (by norm_num)
theorem B3331489 : Blo 1973435 3331489 := bstep (se 2 (by rfl) ⟨1249308, by rfl⟩ : syracuseStep 3331489 = 2498617) B2498617
theorem B4441985 : Blo 1973435 4441985 := bstep (se 2 (by rfl) ⟨1665744, by rfl⟩ : syracuseStep 4441985 = 3331489) B3331489
theorem B2961323 : Blo 1973435 2961323 := bstep (se 1 (by rfl) ⟨2220992, by rfl⟩ : syracuseStep 2961323 = 4441985) B4441985
theorem B1974215 : Blo 1973435 1974215 := bstep (se 1 (by rfl) ⟨1480661, by rfl⟩ : syracuseStep 1974215 = 2961323) B2961323
theorem B2220997 : Blo 1973435 2220997 := bbase (se 4 (by rfl) ⟨208218, by rfl⟩ : syracuseStep 2220997 = 416437) (by norm_num)
theorem B2961329 : Blo 1973435 2961329 := bstep (se 2 (by rfl) ⟨1110498, by rfl⟩ : syracuseStep 2961329 = 2220997) B2220997
theorem B1974219 : Blo 1973435 1974219 := bstep (se 1 (by rfl) ⟨1480664, by rfl⟩ : syracuseStep 1974219 = 2961329) B2961329
theorem B3747941 : Blo 1973435 3747941 := bbase (se 4 (by rfl) ⟨351369, by rfl⟩ : syracuseStep 3747941 = 702739) (by norm_num)
theorem B2498627 : Blo 1973435 2498627 := bstep (se 1 (by rfl) ⟨1873970, by rfl⟩ : syracuseStep 2498627 = 3747941) B3747941
theorem B6663005 : Blo 1973435 6663005 := bstep (se 3 (by rfl) ⟨1249313, by rfl⟩ : syracuseStep 6663005 = 2498627) B2498627
theorem B4442003 : Blo 1973435 4442003 := bstep (se 1 (by rfl) ⟨3331502, by rfl⟩ : syracuseStep 4442003 = 6663005) B6663005
theorem B2961335 : Blo 1973435 2961335 := bstep (se 1 (by rfl) ⟨2221001, by rfl⟩ : syracuseStep 2961335 = 4442003) B4442003
theorem B1974223 : Blo 1973435 1974223 := bstep (se 1 (by rfl) ⟨1480667, by rfl⟩ : syracuseStep 1974223 = 2961335) B2961335
theorem B2961341 : Blo 1973435 2961341 := bbase (se 3 (by rfl) ⟨555251, by rfl⟩ : syracuseStep 2961341 = 1110503) (by norm_num)
theorem B1974227 : Blo 1973435 1974227 := bstep (se 1 (by rfl) ⟨1480670, by rfl⟩ : syracuseStep 1974227 = 2961341) B2961341
theorem B4442021 : Blo 1973435 4442021 := bbase (se 4 (by rfl) ⟨416439, by rfl⟩ : syracuseStep 4442021 = 832879) (by norm_num)
theorem B2961347 : Blo 1973435 2961347 := bstep (se 1 (by rfl) ⟨2221010, by rfl⟩ : syracuseStep 2961347 = 4442021) B4442021
theorem B1974231 : Blo 1973435 1974231 := bstep (se 1 (by rfl) ⟨1480673, by rfl⟩ : syracuseStep 1974231 = 2961347) B2961347
theorem B4997285 : Blo 1973435 4997285 := bbase (se 4 (by rfl) ⟨468495, by rfl⟩ : syracuseStep 4997285 = 936991) (by norm_num)
theorem B3331523 : Blo 1973435 3331523 := bstep (se 1 (by rfl) ⟨2498642, by rfl⟩ : syracuseStep 3331523 = 4997285) B4997285
theorem B2221015 : Blo 1973435 2221015 := bstep (se 1 (by rfl) ⟨1665761, by rfl⟩ : syracuseStep 2221015 = 3331523) B3331523
theorem B2961353 : Blo 1973435 2961353 := bstep (se 2 (by rfl) ⟨1110507, by rfl⟩ : syracuseStep 2961353 = 2221015) B2221015
theorem B1974235 : Blo 1973435 1974235 := bstep (se 1 (by rfl) ⟨1480676, by rfl⟩ : syracuseStep 1974235 = 2961353) B2961353
theorem B5621957 : Blo 1973435 5621957 := bbase (se 4 (by rfl) ⟨527058, by rfl⟩ : syracuseStep 5621957 = 1054117) (by norm_num)
theorem B3747971 : Blo 1973435 3747971 := bstep (se 1 (by rfl) ⟨2810978, by rfl⟩ : syracuseStep 3747971 = 5621957) B5621957
theorem B9994589 : Blo 1973435 9994589 := bstep (se 3 (by rfl) ⟨1873985, by rfl⟩ : syracuseStep 9994589 = 3747971) B3747971
theorem B6663059 : Blo 1973435 6663059 := bstep (se 1 (by rfl) ⟨4997294, by rfl⟩ : syracuseStep 6663059 = 9994589) B9994589
theorem B4442039 : Blo 1973435 4442039 := bstep (se 1 (by rfl) ⟨3331529, by rfl⟩ : syracuseStep 4442039 = 6663059) B6663059
theorem B2961359 : Blo 1973435 2961359 := bstep (se 1 (by rfl) ⟨2221019, by rfl⟩ : syracuseStep 2961359 = 4442039) B4442039
theorem B1974239 : Blo 1973435 1974239 := bstep (se 1 (by rfl) ⟨1480679, by rfl⟩ : syracuseStep 1974239 = 2961359) B2961359
theorem B2961365 : Blo 1973435 2961365 := bbase (se 7 (by rfl) ⟨34703, by rfl⟩ : syracuseStep 2961365 = 69407) (by norm_num)
theorem B1974243 : Blo 1973435 1974243 := bstep (se 1 (by rfl) ⟨1480682, by rfl⟩ : syracuseStep 1974243 = 2961365) B2961365
theorem B7495973 : Blo 1973435 7495973 := bbase (se 4 (by rfl) ⟨702747, by rfl⟩ : syracuseStep 7495973 = 1405495) (by norm_num)
theorem B4997315 : Blo 1973435 4997315 := bstep (se 1 (by rfl) ⟨3747986, by rfl⟩ : syracuseStep 4997315 = 7495973) B7495973
theorem B3331543 : Blo 1973435 3331543 := bstep (se 1 (by rfl) ⟨2498657, by rfl⟩ : syracuseStep 3331543 = 4997315) B4997315
theorem B4442057 : Blo 1973435 4442057 := bstep (se 2 (by rfl) ⟨1665771, by rfl⟩ : syracuseStep 4442057 = 3331543) B3331543
theorem B2961371 : Blo 1973435 2961371 := bstep (se 1 (by rfl) ⟨2221028, by rfl⟩ : syracuseStep 2961371 = 4442057) B4442057
theorem B1974247 : Blo 1973435 1974247 := bstep (se 1 (by rfl) ⟨1480685, by rfl⟩ : syracuseStep 1974247 = 2961371) B2961371
theorem B2221033 : Blo 1973435 2221033 := bbase (se 2 (by rfl) ⟨832887, by rfl⟩ : syracuseStep 2221033 = 1665775) (by norm_num)
theorem B2961377 : Blo 1973435 2961377 := bstep (se 2 (by rfl) ⟨1110516, by rfl⟩ : syracuseStep 2961377 = 2221033) B2221033
theorem B1974251 : Blo 1973435 1974251 := bstep (se 1 (by rfl) ⟨1480688, by rfl⟩ : syracuseStep 1974251 = 2961377) B2961377
theorem B3001789 : Blo 1973435 3001789 := bbase (se 3 (by rfl) ⟨562835, by rfl⟩ : syracuseStep 3001789 = 1125671) (by norm_num)
theorem B4002385 : Blo 1973435 4002385 := bstep (se 2 (by rfl) ⟨1500894, by rfl⟩ : syracuseStep 4002385 = 3001789) B3001789
theorem B5336513 : Blo 1973435 5336513 := bstep (se 2 (by rfl) ⟨2001192, by rfl⟩ : syracuseStep 5336513 = 4002385) B4002385
theorem B3557675 : Blo 1973435 3557675 := bstep (se 1 (by rfl) ⟨2668256, by rfl⟩ : syracuseStep 3557675 = 5336513) B5336513
theorem B2371783 : Blo 1973435 2371783 := bstep (se 1 (by rfl) ⟨1778837, by rfl⟩ : syracuseStep 2371783 = 3557675) B3557675
theorem B3162377 : Blo 1973435 3162377 := bstep (se 2 (by rfl) ⟨1185891, by rfl⟩ : syracuseStep 3162377 = 2371783) B2371783
theorem B2108251 : Blo 1973435 2108251 := bstep (se 1 (by rfl) ⟨1581188, by rfl⟩ : syracuseStep 2108251 = 3162377) B3162377
theorem B11244005 : Blo 1973435 11244005 := bstep (se 4 (by rfl) ⟨1054125, by rfl⟩ : syracuseStep 11244005 = 2108251) B2108251
theorem B7496003 : Blo 1973435 7496003 := bstep (se 1 (by rfl) ⟨5622002, by rfl⟩ : syracuseStep 7496003 = 11244005) B11244005
theorem B4997335 : Blo 1973435 4997335 := bstep (se 1 (by rfl) ⟨3748001, by rfl⟩ : syracuseStep 4997335 = 7496003) B7496003
theorem B6663113 : Blo 1973435 6663113 := bstep (se 2 (by rfl) ⟨2498667, by rfl⟩ : syracuseStep 6663113 = 4997335) B4997335
theorem B4442075 : Blo 1973435 4442075 := bstep (se 1 (by rfl) ⟨3331556, by rfl⟩ : syracuseStep 4442075 = 6663113) B6663113
theorem B2961383 : Blo 1973435 2961383 := bstep (se 1 (by rfl) ⟨2221037, by rfl⟩ : syracuseStep 2961383 = 4442075) B4442075
theorem B1974255 : Blo 1973435 1974255 := bstep (se 1 (by rfl) ⟨1480691, by rfl⟩ : syracuseStep 1974255 = 2961383) B2961383
theorem B2961389 : Blo 1973435 2961389 := bbase (se 3 (by rfl) ⟨555260, by rfl⟩ : syracuseStep 2961389 = 1110521) (by norm_num)
theorem B1974259 : Blo 1973435 1974259 := bstep (se 1 (by rfl) ⟨1480694, by rfl⟩ : syracuseStep 1974259 = 2961389) B2961389
theorem B4442093 : Blo 1973435 4442093 := bbase (se 3 (by rfl) ⟨832892, by rfl⟩ : syracuseStep 4442093 = 1665785) (by norm_num)
theorem B2961395 : Blo 1973435 2961395 := bstep (se 1 (by rfl) ⟨2221046, by rfl⟩ : syracuseStep 2961395 = 4442093) B4442093
theorem B1974263 : Blo 1973435 1974263 := bstep (se 1 (by rfl) ⟨1480697, by rfl⟩ : syracuseStep 1974263 = 2961395) B2961395
theorem B3162397 : Blo 1973435 3162397 := bbase (se 3 (by rfl) ⟨592949, by rfl⟩ : syracuseStep 3162397 = 1185899) (by norm_num)
theorem B4216529 : Blo 1973435 4216529 := bstep (se 2 (by rfl) ⟨1581198, by rfl⟩ : syracuseStep 4216529 = 3162397) B3162397
theorem B2811019 : Blo 1973435 2811019 := bstep (se 1 (by rfl) ⟨2108264, by rfl⟩ : syracuseStep 2811019 = 4216529) B4216529
theorem B3748025 : Blo 1973435 3748025 := bstep (se 2 (by rfl) ⟨1405509, by rfl⟩ : syracuseStep 3748025 = 2811019) B2811019
theorem B2498683 : Blo 1973435 2498683 := bstep (se 1 (by rfl) ⟨1874012, by rfl⟩ : syracuseStep 2498683 = 3748025) B3748025
theorem B3331577 : Blo 1973435 3331577 := bstep (se 2 (by rfl) ⟨1249341, by rfl⟩ : syracuseStep 3331577 = 2498683) B2498683
theorem B2221051 : Blo 1973435 2221051 := bstep (se 1 (by rfl) ⟨1665788, by rfl⟩ : syracuseStep 2221051 = 3331577) B3331577
theorem B2961401 : Blo 1973435 2961401 := bstep (se 2 (by rfl) ⟨1110525, by rfl⟩ : syracuseStep 2961401 = 2221051) B2221051
theorem B1974267 : Blo 1973435 1974267 := bstep (se 1 (by rfl) ⟨1480700, by rfl⟩ : syracuseStep 1974267 = 2961401) B2961401
theorem B16228085 : Blo 1973435 16228085 := bbase (se 5 (by rfl) ⟨760691, by rfl⟩ : syracuseStep 16228085 = 1521383) (by norm_num)
theorem B43274893 : Blo 1973435 43274893 := bstep (se 3 (by rfl) ⟨8114042, by rfl⟩ : syracuseStep 43274893 = 16228085) B16228085
theorem B57699857 : Blo 1973435 57699857 := bstep (se 2 (by rfl) ⟨21637446, by rfl⟩ : syracuseStep 57699857 = 43274893) B43274893
theorem B38466571 : Blo 1973435 38466571 := bstep (se 1 (by rfl) ⟨28849928, by rfl⟩ : syracuseStep 38466571 = 57699857) B57699857
theorem B51288761 : Blo 1973435 51288761 := bstep (se 2 (by rfl) ⟨19233285, by rfl⟩ : syracuseStep 51288761 = 38466571) B38466571
theorem B136770029 : Blo 1973435 136770029 := bstep (se 3 (by rfl) ⟨25644380, by rfl⟩ : syracuseStep 136770029 = 51288761) B51288761
theorem B91180019 : Blo 1973435 91180019 := bstep (se 1 (by rfl) ⟨68385014, by rfl⟩ : syracuseStep 91180019 = 136770029) B136770029
theorem B60786679 : Blo 1973435 60786679 := bstep (se 1 (by rfl) ⟨45590009, by rfl⟩ : syracuseStep 60786679 = 91180019) B91180019
theorem B81048905 : Blo 1973435 81048905 := bstep (se 2 (by rfl) ⟨30393339, by rfl⟩ : syracuseStep 81048905 = 60786679) B60786679
theorem B54032603 : Blo 1973435 54032603 := bstep (se 1 (by rfl) ⟨40524452, by rfl⟩ : syracuseStep 54032603 = 81048905) B81048905
theorem B144086941 : Blo 1973435 144086941 := bstep (se 3 (by rfl) ⟨27016301, by rfl⟩ : syracuseStep 144086941 = 54032603) B54032603
theorem B192115921 : Blo 1973435 192115921 := bstep (se 2 (by rfl) ⟨72043470, by rfl⟩ : syracuseStep 192115921 = 144086941) B144086941
theorem B256154561 : Blo 1973435 256154561 := bstep (se 2 (by rfl) ⟨96057960, by rfl⟩ : syracuseStep 256154561 = 192115921) B192115921
theorem B170769707 : Blo 1973435 170769707 := bstep (se 1 (by rfl) ⟨128077280, by rfl⟩ : syracuseStep 170769707 = 256154561) B256154561
theorem B113846471 : Blo 1973435 113846471 := bstep (se 1 (by rfl) ⟨85384853, by rfl⟩ : syracuseStep 113846471 = 170769707) B170769707
theorem B75897647 : Blo 1973435 75897647 := bstep (se 1 (by rfl) ⟨56923235, by rfl⟩ : syracuseStep 75897647 = 113846471) B113846471
theorem B50598431 : Blo 1973435 50598431 := bstep (se 1 (by rfl) ⟨37948823, by rfl⟩ : syracuseStep 50598431 = 75897647) B75897647
theorem B33732287 : Blo 1973435 33732287 := bstep (se 1 (by rfl) ⟨25299215, by rfl⟩ : syracuseStep 33732287 = 50598431) B50598431
theorem B22488191 : Blo 1973435 22488191 := bstep (se 1 (by rfl) ⟨16866143, by rfl⟩ : syracuseStep 22488191 = 33732287) B33732287
theorem B14992127 : Blo 1973435 14992127 := bstep (se 1 (by rfl) ⟨11244095, by rfl⟩ : syracuseStep 14992127 = 22488191) B22488191
theorem B9994751 : Blo 1973435 9994751 := bstep (se 1 (by rfl) ⟨7496063, by rfl⟩ : syracuseStep 9994751 = 14992127) B14992127
theorem B6663167 : Blo 1973435 6663167 := bstep (se 1 (by rfl) ⟨4997375, by rfl⟩ : syracuseStep 6663167 = 9994751) B9994751
theorem B4442111 : Blo 1973435 4442111 := bstep (se 1 (by rfl) ⟨3331583, by rfl⟩ : syracuseStep 4442111 = 6663167) B6663167
theorem B2961407 : Blo 1973435 2961407 := bstep (se 1 (by rfl) ⟨2221055, by rfl⟩ : syracuseStep 2961407 = 4442111) B4442111
theorem B1974271 : Blo 1973435 1974271 := bstep (se 1 (by rfl) ⟨1480703, by rfl⟩ : syracuseStep 1974271 = 2961407) B2961407
theorem B2961413 : Blo 1973435 2961413 := bbase (se 4 (by rfl) ⟨277632, by rfl⟩ : syracuseStep 2961413 = 555265) (by norm_num)
theorem B1974275 : Blo 1973435 1974275 := bstep (se 1 (by rfl) ⟨1480706, by rfl⟩ : syracuseStep 1974275 = 2961413) B2961413
theorem B3331597 : Blo 1973435 3331597 := bbase (se 3 (by rfl) ⟨624674, by rfl⟩ : syracuseStep 3331597 = 1249349) (by norm_num)
theorem B4442129 : Blo 1973435 4442129 := bstep (se 2 (by rfl) ⟨1665798, by rfl⟩ : syracuseStep 4442129 = 3331597) B3331597
theorem B2961419 : Blo 1973435 2961419 := bstep (se 1 (by rfl) ⟨2221064, by rfl⟩ : syracuseStep 2961419 = 4442129) B4442129
theorem B1974279 : Blo 1973435 1974279 := bstep (se 1 (by rfl) ⟨1480709, by rfl⟩ : syracuseStep 1974279 = 2961419) B2961419
theorem B2221069 : Blo 1973435 2221069 := bbase (se 3 (by rfl) ⟨416450, by rfl⟩ : syracuseStep 2221069 = 832901) (by norm_num)
theorem B2961425 : Blo 1973435 2961425 := bstep (se 2 (by rfl) ⟨1110534, by rfl⟩ : syracuseStep 2961425 = 2221069) B2221069
theorem B1974283 : Blo 1973435 1974283 := bstep (se 1 (by rfl) ⟨1480712, by rfl⟩ : syracuseStep 1974283 = 2961425) B2961425
theorem B6663221 : Blo 1973435 6663221 := bbase (se 5 (by rfl) ⟨312338, by rfl⟩ : syracuseStep 6663221 = 624677) (by norm_num)
theorem B4442147 : Blo 1973435 4442147 := bstep (se 1 (by rfl) ⟨3331610, by rfl⟩ : syracuseStep 4442147 = 6663221) B6663221
theorem B2961431 : Blo 1973435 2961431 := bstep (se 1 (by rfl) ⟨2221073, by rfl⟩ : syracuseStep 2961431 = 4442147) B4442147
theorem B1974287 : Blo 1973435 1974287 := bstep (se 1 (by rfl) ⟨1480715, by rfl⟩ : syracuseStep 1974287 = 2961431) B2961431
theorem B2961437 : Blo 1973435 2961437 := bbase (se 3 (by rfl) ⟨555269, by rfl⟩ : syracuseStep 2961437 = 1110539) (by norm_num)
theorem B1974291 : Blo 1973435 1974291 := bstep (se 1 (by rfl) ⟨1480718, by rfl⟩ : syracuseStep 1974291 = 2961437) B2961437
theorem B4442165 : Blo 1973435 4442165 := bbase (se 5 (by rfl) ⟨208226, by rfl⟩ : syracuseStep 4442165 = 416453) (by norm_num)
theorem B2961443 : Blo 1973435 2961443 := bstep (se 1 (by rfl) ⟨2221082, by rfl⟩ : syracuseStep 2961443 = 4442165) B4442165
theorem B1974295 : Blo 1973435 1974295 := bstep (se 1 (by rfl) ⟨1480721, by rfl⟩ : syracuseStep 1974295 = 2961443) B2961443
theorem B6085621 : Blo 1973435 6085621 := bbase (se 5 (by rfl) ⟨285263, by rfl⟩ : syracuseStep 6085621 = 570527) (by norm_num)
theorem B32456645 : Blo 1973435 32456645 := bstep (se 4 (by rfl) ⟨3042810, by rfl⟩ : syracuseStep 32456645 = 6085621) B6085621
theorem B21637763 : Blo 1973435 21637763 := bstep (se 1 (by rfl) ⟨16228322, by rfl⟩ : syracuseStep 21637763 = 32456645) B32456645
theorem B14425175 : Blo 1973435 14425175 := bstep (se 1 (by rfl) ⟨10818881, by rfl⟩ : syracuseStep 14425175 = 21637763) B21637763
theorem B38467133 : Blo 1973435 38467133 := bstep (se 3 (by rfl) ⟨7212587, by rfl⟩ : syracuseStep 38467133 = 14425175) B14425175
theorem B25644755 : Blo 1973435 25644755 := bstep (se 1 (by rfl) ⟨19233566, by rfl⟩ : syracuseStep 25644755 = 38467133) B38467133
theorem B17096503 : Blo 1973435 17096503 := bstep (se 1 (by rfl) ⟨12822377, by rfl⟩ : syracuseStep 17096503 = 25644755) B25644755
theorem B22795337 : Blo 1973435 22795337 := bstep (se 2 (by rfl) ⟨8548251, by rfl⟩ : syracuseStep 22795337 = 17096503) B17096503
theorem B15196891 : Blo 1973435 15196891 := bstep (se 1 (by rfl) ⟨11397668, by rfl⟩ : syracuseStep 15196891 = 22795337) B22795337
theorem B20262521 : Blo 1973435 20262521 := bstep (se 2 (by rfl) ⟨7598445, by rfl⟩ : syracuseStep 20262521 = 15196891) B15196891
theorem B54033389 : Blo 1973435 54033389 := bstep (se 3 (by rfl) ⟨10131260, by rfl⟩ : syracuseStep 54033389 = 20262521) B20262521
theorem B36022259 : Blo 1973435 36022259 := bstep (se 1 (by rfl) ⟨27016694, by rfl⟩ : syracuseStep 36022259 = 54033389) B54033389
theorem B24014839 : Blo 1973435 24014839 := bstep (se 1 (by rfl) ⟨18011129, by rfl⟩ : syracuseStep 24014839 = 36022259) B36022259
theorem B32019785 : Blo 1973435 32019785 := bstep (se 2 (by rfl) ⟨12007419, by rfl⟩ : syracuseStep 32019785 = 24014839) B24014839
theorem B21346523 : Blo 1973435 21346523 := bstep (se 1 (by rfl) ⟨16009892, by rfl⟩ : syracuseStep 21346523 = 32019785) B32019785
theorem B14231015 : Blo 1973435 14231015 := bstep (se 1 (by rfl) ⟨10673261, by rfl⟩ : syracuseStep 14231015 = 21346523) B21346523
theorem B9487343 : Blo 1973435 9487343 := bstep (se 1 (by rfl) ⟨7115507, by rfl⟩ : syracuseStep 9487343 = 14231015) B14231015
theorem B6324895 : Blo 1973435 6324895 := bstep (se 1 (by rfl) ⟨4743671, by rfl⟩ : syracuseStep 6324895 = 9487343) B9487343
theorem B8433193 : Blo 1973435 8433193 := bstep (se 2 (by rfl) ⟨3162447, by rfl⟩ : syracuseStep 8433193 = 6324895) B6324895
theorem B11244257 : Blo 1973435 11244257 := bstep (se 2 (by rfl) ⟨4216596, by rfl⟩ : syracuseStep 11244257 = 8433193) B8433193
theorem B7496171 : Blo 1973435 7496171 := bstep (se 1 (by rfl) ⟨5622128, by rfl⟩ : syracuseStep 7496171 = 11244257) B11244257
theorem B4997447 : Blo 1973435 4997447 := bstep (se 1 (by rfl) ⟨3748085, by rfl⟩ : syracuseStep 4997447 = 7496171) B7496171
theorem B3331631 : Blo 1973435 3331631 := bstep (se 1 (by rfl) ⟨2498723, by rfl⟩ : syracuseStep 3331631 = 4997447) B4997447
theorem B2221087 : Blo 1973435 2221087 := bstep (se 1 (by rfl) ⟨1665815, by rfl⟩ : syracuseStep 2221087 = 3331631) B3331631
theorem B2961449 : Blo 1973435 2961449 := bstep (se 2 (by rfl) ⟨1110543, by rfl⟩ : syracuseStep 2961449 = 2221087) B2221087
theorem B1974299 : Blo 1973435 1974299 := bstep (se 1 (by rfl) ⟨1480724, by rfl⟩ : syracuseStep 1974299 = 2961449) B2961449
theorem B3001861 : Blo 1973435 3001861 := bbase (se 4 (by rfl) ⟨281424, by rfl⟩ : syracuseStep 3001861 = 562849) (by norm_num)
theorem B4002481 : Blo 1973435 4002481 := bstep (se 2 (by rfl) ⟨1500930, by rfl⟩ : syracuseStep 4002481 = 3001861) B3001861
theorem B5336641 : Blo 1973435 5336641 := bstep (se 2 (by rfl) ⟨2001240, by rfl⟩ : syracuseStep 5336641 = 4002481) B4002481
theorem B7115521 : Blo 1973435 7115521 := bstep (se 2 (by rfl) ⟨2668320, by rfl⟩ : syracuseStep 7115521 = 5336641) B5336641
theorem B9487361 : Blo 1973435 9487361 := bstep (se 2 (by rfl) ⟨3557760, by rfl⟩ : syracuseStep 9487361 = 7115521) B7115521
theorem B6324907 : Blo 1973435 6324907 := bstep (se 1 (by rfl) ⟨4743680, by rfl⟩ : syracuseStep 6324907 = 9487361) B9487361
theorem B8433209 : Blo 1973435 8433209 := bstep (se 2 (by rfl) ⟨3162453, by rfl⟩ : syracuseStep 8433209 = 6324907) B6324907
theorem B5622139 : Blo 1973435 5622139 := bstep (se 1 (by rfl) ⟨4216604, by rfl⟩ : syracuseStep 5622139 = 8433209) B8433209
theorem B7496185 : Blo 1973435 7496185 := bstep (se 2 (by rfl) ⟨2811069, by rfl⟩ : syracuseStep 7496185 = 5622139) B5622139
theorem B9994913 : Blo 1973435 9994913 := bstep (se 2 (by rfl) ⟨3748092, by rfl⟩ : syracuseStep 9994913 = 7496185) B7496185
theorem B6663275 : Blo 1973435 6663275 := bstep (se 1 (by rfl) ⟨4997456, by rfl⟩ : syracuseStep 6663275 = 9994913) B9994913
theorem B4442183 : Blo 1973435 4442183 := bstep (se 1 (by rfl) ⟨3331637, by rfl⟩ : syracuseStep 4442183 = 6663275) B6663275
theorem B2961455 : Blo 1973435 2961455 := bstep (se 1 (by rfl) ⟨2221091, by rfl⟩ : syracuseStep 2961455 = 4442183) B4442183
theorem B1974303 : Blo 1973435 1974303 := bstep (se 1 (by rfl) ⟨1480727, by rfl⟩ : syracuseStep 1974303 = 2961455) B2961455
theorem B2961461 : Blo 1973435 2961461 := bbase (se 5 (by rfl) ⟨138818, by rfl⟩ : syracuseStep 2961461 = 277637) (by norm_num)
theorem B1974307 : Blo 1973435 1974307 := bstep (se 1 (by rfl) ⟨1480730, by rfl⟩ : syracuseStep 1974307 = 2961461) B2961461
theorem B4997477 : Blo 1973435 4997477 := bbase (se 4 (by rfl) ⟨468513, by rfl⟩ : syracuseStep 4997477 = 937027) (by norm_num)
theorem B3331651 : Blo 1973435 3331651 := bstep (se 1 (by rfl) ⟨2498738, by rfl⟩ : syracuseStep 3331651 = 4997477) B4997477
theorem B4442201 : Blo 1973435 4442201 := bstep (se 2 (by rfl) ⟨1665825, by rfl⟩ : syracuseStep 4442201 = 3331651) B3331651
theorem B2961467 : Blo 1973435 2961467 := bstep (se 1 (by rfl) ⟨2221100, by rfl⟩ : syracuseStep 2961467 = 4442201) B4442201
theorem B1974311 : Blo 1973435 1974311 := bstep (se 1 (by rfl) ⟨1480733, by rfl⟩ : syracuseStep 1974311 = 2961467) B2961467
theorem B2221105 : Blo 1973435 2221105 := bbase (se 2 (by rfl) ⟨832914, by rfl⟩ : syracuseStep 2221105 = 1665829) (by norm_num)
theorem B2961473 : Blo 1973435 2961473 := bstep (se 2 (by rfl) ⟨1110552, by rfl⟩ : syracuseStep 2961473 = 2221105) B2221105
theorem B1974315 : Blo 1973435 1974315 := bstep (se 1 (by rfl) ⟨1480736, by rfl⟩ : syracuseStep 1974315 = 2961473) B2961473
theorem B12007541 : Blo 1973435 12007541 := bbase (se 5 (by rfl) ⟨562853, by rfl⟩ : syracuseStep 12007541 = 1125707) (by norm_num)
theorem B32020109 : Blo 1973435 32020109 := bstep (se 3 (by rfl) ⟨6003770, by rfl⟩ : syracuseStep 32020109 = 12007541) B12007541
theorem B21346739 : Blo 1973435 21346739 := bstep (se 1 (by rfl) ⟨16010054, by rfl⟩ : syracuseStep 21346739 = 32020109) B32020109
theorem B14231159 : Blo 1973435 14231159 := bstep (se 1 (by rfl) ⟨10673369, by rfl⟩ : syracuseStep 14231159 = 21346739) B21346739
theorem B9487439 : Blo 1973435 9487439 := bstep (se 1 (by rfl) ⟨7115579, by rfl⟩ : syracuseStep 9487439 = 14231159) B14231159
theorem B6324959 : Blo 1973435 6324959 := bstep (se 1 (by rfl) ⟨4743719, by rfl⟩ : syracuseStep 6324959 = 9487439) B9487439
theorem B4216639 : Blo 1973435 4216639 := bstep (se 1 (by rfl) ⟨3162479, by rfl⟩ : syracuseStep 4216639 = 6324959) B6324959
theorem B5622185 : Blo 1973435 5622185 := bstep (se 2 (by rfl) ⟨2108319, by rfl⟩ : syracuseStep 5622185 = 4216639) B4216639
theorem B3748123 : Blo 1973435 3748123 := bstep (se 1 (by rfl) ⟨2811092, by rfl⟩ : syracuseStep 3748123 = 5622185) B5622185
theorem B4997497 : Blo 1973435 4997497 := bstep (se 2 (by rfl) ⟨1874061, by rfl⟩ : syracuseStep 4997497 = 3748123) B3748123
theorem B6663329 : Blo 1973435 6663329 := bstep (se 2 (by rfl) ⟨2498748, by rfl⟩ : syracuseStep 6663329 = 4997497) B4997497
theorem B4442219 : Blo 1973435 4442219 := bstep (se 1 (by rfl) ⟨3331664, by rfl⟩ : syracuseStep 4442219 = 6663329) B6663329
theorem B2961479 : Blo 1973435 2961479 := bstep (se 1 (by rfl) ⟨2221109, by rfl⟩ : syracuseStep 2961479 = 4442219) B4442219
theorem B1974319 : Blo 1973435 1974319 := bstep (se 1 (by rfl) ⟨1480739, by rfl⟩ : syracuseStep 1974319 = 2961479) B2961479
theorem B2961485 : Blo 1973435 2961485 := bbase (se 3 (by rfl) ⟨555278, by rfl⟩ : syracuseStep 2961485 = 1110557) (by norm_num)
theorem B1974323 : Blo 1973435 1974323 := bstep (se 1 (by rfl) ⟨1480742, by rfl⟩ : syracuseStep 1974323 = 2961485) B2961485
theorem B4442237 : Blo 1973435 4442237 := bbase (se 3 (by rfl) ⟨832919, by rfl⟩ : syracuseStep 4442237 = 1665839) (by norm_num)
theorem B2961491 : Blo 1973435 2961491 := bstep (se 1 (by rfl) ⟨2221118, by rfl⟩ : syracuseStep 2961491 = 4442237) B4442237
theorem B1974327 : Blo 1973435 1974327 := bstep (se 1 (by rfl) ⟨1480745, by rfl⟩ : syracuseStep 1974327 = 2961491) B2961491
theorem B3331685 : Blo 1973435 3331685 := bbase (se 4 (by rfl) ⟨312345, by rfl⟩ : syracuseStep 3331685 = 624691) (by norm_num)
theorem B2221123 : Blo 1973435 2221123 := bstep (se 1 (by rfl) ⟨1665842, by rfl⟩ : syracuseStep 2221123 = 3331685) B3331685
theorem B2961497 : Blo 1973435 2961497 := bstep (se 2 (by rfl) ⟨1110561, by rfl⟩ : syracuseStep 2961497 = 2221123) B2221123
theorem B1974331 : Blo 1973435 1974331 := bstep (se 1 (by rfl) ⟨1480748, by rfl⟩ : syracuseStep 1974331 = 2961497) B2961497
theorem B2251433 : Blo 1973435 2251433 := bbase (se 2 (by rfl) ⟨844287, by rfl⟩ : syracuseStep 2251433 = 1688575) (by norm_num)
theorem B6003821 : Blo 1973435 6003821 := bstep (se 3 (by rfl) ⟨1125716, by rfl⟩ : syracuseStep 6003821 = 2251433) B2251433
theorem B4002547 : Blo 1973435 4002547 := bstep (se 1 (by rfl) ⟨3001910, by rfl⟩ : syracuseStep 4002547 = 6003821) B6003821
theorem B5336729 : Blo 1973435 5336729 := bstep (se 2 (by rfl) ⟨2001273, by rfl⟩ : syracuseStep 5336729 = 4002547) B4002547
theorem B3557819 : Blo 1973435 3557819 := bstep (se 1 (by rfl) ⟨2668364, by rfl⟩ : syracuseStep 3557819 = 5336729) B5336729
theorem B2371879 : Blo 1973435 2371879 := bstep (se 1 (by rfl) ⟨1778909, by rfl⟩ : syracuseStep 2371879 = 3557819) B3557819
theorem B3162505 : Blo 1973435 3162505 := bstep (se 2 (by rfl) ⟨1185939, by rfl⟩ : syracuseStep 3162505 = 2371879) B2371879
theorem B4216673 : Blo 1973435 4216673 := bstep (se 2 (by rfl) ⟨1581252, by rfl⟩ : syracuseStep 4216673 = 3162505) B3162505
theorem B2811115 : Blo 1973435 2811115 := bstep (se 1 (by rfl) ⟨2108336, by rfl⟩ : syracuseStep 2811115 = 4216673) B4216673
theorem B14992613 : Blo 1973435 14992613 := bstep (se 4 (by rfl) ⟨1405557, by rfl⟩ : syracuseStep 14992613 = 2811115) B2811115
theorem B9995075 : Blo 1973435 9995075 := bstep (se 1 (by rfl) ⟨7496306, by rfl⟩ : syracuseStep 9995075 = 14992613) B14992613
theorem B6663383 : Blo 1973435 6663383 := bstep (se 1 (by rfl) ⟨4997537, by rfl⟩ : syracuseStep 6663383 = 9995075) B9995075
theorem B4442255 : Blo 1973435 4442255 := bstep (se 1 (by rfl) ⟨3331691, by rfl⟩ : syracuseStep 4442255 = 6663383) B6663383
theorem B2961503 : Blo 1973435 2961503 := bstep (se 1 (by rfl) ⟨2221127, by rfl⟩ : syracuseStep 2961503 = 4442255) B4442255
theorem B1974335 : Blo 1973435 1974335 := bstep (se 1 (by rfl) ⟨1480751, by rfl⟩ : syracuseStep 1974335 = 2961503) B2961503
theorem B2961509 : Blo 1973435 2961509 := bbase (se 4 (by rfl) ⟨277641, by rfl⟩ : syracuseStep 2961509 = 555283) (by norm_num)
theorem B1974339 : Blo 1973435 1974339 := bstep (se 1 (by rfl) ⟨1480754, by rfl⟩ : syracuseStep 1974339 = 2961509) B2961509
theorem B2371889 : Blo 1973435 2371889 := bbase (se 2 (by rfl) ⟨889458, by rfl⟩ : syracuseStep 2371889 = 1778917) (by norm_num)
theorem B6325037 : Blo 1973435 6325037 := bstep (se 3 (by rfl) ⟨1185944, by rfl⟩ : syracuseStep 6325037 = 2371889) B2371889
theorem B4216691 : Blo 1973435 4216691 := bstep (se 1 (by rfl) ⟨3162518, by rfl⟩ : syracuseStep 4216691 = 6325037) B6325037
theorem B2811127 : Blo 1973435 2811127 := bstep (se 1 (by rfl) ⟨2108345, by rfl⟩ : syracuseStep 2811127 = 4216691) B4216691
theorem B3748169 : Blo 1973435 3748169 := bstep (se 2 (by rfl) ⟨1405563, by rfl⟩ : syracuseStep 3748169 = 2811127) B2811127
theorem B2498779 : Blo 1973435 2498779 := bstep (se 1 (by rfl) ⟨1874084, by rfl⟩ : syracuseStep 2498779 = 3748169) B3748169
theorem B3331705 : Blo 1973435 3331705 := bstep (se 2 (by rfl) ⟨1249389, by rfl⟩ : syracuseStep 3331705 = 2498779) B2498779
theorem B4442273 : Blo 1973435 4442273 := bstep (se 2 (by rfl) ⟨1665852, by rfl⟩ : syracuseStep 4442273 = 3331705) B3331705
theorem B2961515 : Blo 1973435 2961515 := bstep (se 1 (by rfl) ⟨2221136, by rfl⟩ : syracuseStep 2961515 = 4442273) B4442273
theorem B1974343 : Blo 1973435 1974343 := bstep (se 1 (by rfl) ⟨1480757, by rfl⟩ : syracuseStep 1974343 = 2961515) B2961515
theorem B2221141 : Blo 1973435 2221141 := bbase (se 8 (by rfl) ⟨13014, by rfl⟩ : syracuseStep 2221141 = 26029) (by norm_num)
theorem B2961521 : Blo 1973435 2961521 := bstep (se 2 (by rfl) ⟨1110570, by rfl⟩ : syracuseStep 2961521 = 2221141) B2221141
theorem B1974347 : Blo 1973435 1974347 := bstep (se 1 (by rfl) ⟨1480760, by rfl⟩ : syracuseStep 1974347 = 2961521) B2961521
theorem B2498789 : Blo 1973435 2498789 := bbase (se 4 (by rfl) ⟨234261, by rfl⟩ : syracuseStep 2498789 = 468523) (by norm_num)
theorem B6663437 : Blo 1973435 6663437 := bstep (se 3 (by rfl) ⟨1249394, by rfl⟩ : syracuseStep 6663437 = 2498789) B2498789
theorem B4442291 : Blo 1973435 4442291 := bstep (se 1 (by rfl) ⟨3331718, by rfl⟩ : syracuseStep 4442291 = 6663437) B6663437
theorem B2961527 : Blo 1973435 2961527 := bstep (se 1 (by rfl) ⟨2221145, by rfl⟩ : syracuseStep 2961527 = 4442291) B4442291
theorem B1974351 : Blo 1973435 1974351 := bstep (se 1 (by rfl) ⟨1480763, by rfl⟩ : syracuseStep 1974351 = 2961527) B2961527
theorem B2961533 : Blo 1973435 2961533 := bbase (se 3 (by rfl) ⟨555287, by rfl⟩ : syracuseStep 2961533 = 1110575) (by norm_num)
theorem B1974355 : Blo 1973435 1974355 := bstep (se 1 (by rfl) ⟨1480766, by rfl⟩ : syracuseStep 1974355 = 2961533) B2961533
theorem B4442309 : Blo 1973435 4442309 := bbase (se 4 (by rfl) ⟨416466, by rfl⟩ : syracuseStep 4442309 = 832933) (by norm_num)
theorem B2961539 : Blo 1973435 2961539 := bstep (se 1 (by rfl) ⟨2221154, by rfl⟩ : syracuseStep 2961539 = 4442309) B4442309
theorem B1974359 : Blo 1973435 1974359 := bstep (se 1 (by rfl) ⟨1480769, by rfl⟩ : syracuseStep 1974359 = 2961539) B2961539
theorem B14231477 : Blo 1973435 14231477 := bbase (se 5 (by rfl) ⟨667100, by rfl⟩ : syracuseStep 14231477 = 1334201) (by norm_num)
theorem B9487651 : Blo 1973435 9487651 := bstep (se 1 (by rfl) ⟨7115738, by rfl⟩ : syracuseStep 9487651 = 14231477) B14231477
theorem B12650201 : Blo 1973435 12650201 := bstep (se 2 (by rfl) ⟨4743825, by rfl⟩ : syracuseStep 12650201 = 9487651) B9487651
theorem B8433467 : Blo 1973435 8433467 := bstep (se 1 (by rfl) ⟨6325100, by rfl⟩ : syracuseStep 8433467 = 12650201) B12650201
theorem B5622311 : Blo 1973435 5622311 := bstep (se 1 (by rfl) ⟨4216733, by rfl⟩ : syracuseStep 5622311 = 8433467) B8433467
theorem B3748207 : Blo 1973435 3748207 := bstep (se 1 (by rfl) ⟨2811155, by rfl⟩ : syracuseStep 3748207 = 5622311) B5622311
theorem B4997609 : Blo 1973435 4997609 := bstep (se 2 (by rfl) ⟨1874103, by rfl⟩ : syracuseStep 4997609 = 3748207) B3748207
theorem B3331739 : Blo 1973435 3331739 := bstep (se 1 (by rfl) ⟨2498804, by rfl⟩ : syracuseStep 3331739 = 4997609) B4997609
theorem B2221159 : Blo 1973435 2221159 := bstep (se 1 (by rfl) ⟨1665869, by rfl⟩ : syracuseStep 2221159 = 3331739) B3331739
theorem B2961545 : Blo 1973435 2961545 := bstep (se 2 (by rfl) ⟨1110579, by rfl⟩ : syracuseStep 2961545 = 2221159) B2221159
theorem B1974363 : Blo 1973435 1974363 := bstep (se 1 (by rfl) ⟨1480772, by rfl⟩ : syracuseStep 1974363 = 2961545) B2961545
theorem B9995237 : Blo 1973435 9995237 := bbase (se 4 (by rfl) ⟨937053, by rfl⟩ : syracuseStep 9995237 = 1874107) (by norm_num)
theorem B6663491 : Blo 1973435 6663491 := bstep (se 1 (by rfl) ⟨4997618, by rfl⟩ : syracuseStep 6663491 = 9995237) B9995237
theorem B4442327 : Blo 1973435 4442327 := bstep (se 1 (by rfl) ⟨3331745, by rfl⟩ : syracuseStep 4442327 = 6663491) B6663491
theorem B2961551 : Blo 1973435 2961551 := bstep (se 1 (by rfl) ⟨2221163, by rfl⟩ : syracuseStep 2961551 = 4442327) B4442327
theorem B1974367 : Blo 1973435 1974367 := bstep (se 1 (by rfl) ⟨1480775, by rfl⟩ : syracuseStep 1974367 = 2961551) B2961551
theorem B2961557 : Blo 1973435 2961557 := bbase (se 6 (by rfl) ⟨69411, by rfl⟩ : syracuseStep 2961557 = 138823) (by norm_num)
theorem B1974371 : Blo 1973435 1974371 := bstep (se 1 (by rfl) ⟨1480778, by rfl⟩ : syracuseStep 1974371 = 2961557) B2961557
theorem B5336837 : Blo 1973435 5336837 := bbase (se 4 (by rfl) ⟨500328, by rfl⟩ : syracuseStep 5336837 = 1000657) (by norm_num)
theorem B3557891 : Blo 1973435 3557891 := bstep (se 1 (by rfl) ⟨2668418, by rfl⟩ : syracuseStep 3557891 = 5336837) B5336837
theorem B2371927 : Blo 1973435 2371927 := bstep (se 1 (by rfl) ⟨1778945, by rfl⟩ : syracuseStep 2371927 = 3557891) B3557891
theorem B3162569 : Blo 1973435 3162569 := bstep (se 2 (by rfl) ⟨1185963, by rfl⟩ : syracuseStep 3162569 = 2371927) B2371927
theorem B8433517 : Blo 1973435 8433517 := bstep (se 3 (by rfl) ⟨1581284, by rfl⟩ : syracuseStep 8433517 = 3162569) B3162569
theorem B11244689 : Blo 1973435 11244689 := bstep (se 2 (by rfl) ⟨4216758, by rfl⟩ : syracuseStep 11244689 = 8433517) B8433517
theorem B7496459 : Blo 1973435 7496459 := bstep (se 1 (by rfl) ⟨5622344, by rfl⟩ : syracuseStep 7496459 = 11244689) B11244689
theorem B4997639 : Blo 1973435 4997639 := bstep (se 1 (by rfl) ⟨3748229, by rfl⟩ : syracuseStep 4997639 = 7496459) B7496459
theorem B3331759 : Blo 1973435 3331759 := bstep (se 1 (by rfl) ⟨2498819, by rfl⟩ : syracuseStep 3331759 = 4997639) B4997639
theorem B4442345 : Blo 1973435 4442345 := bstep (se 2 (by rfl) ⟨1665879, by rfl⟩ : syracuseStep 4442345 = 3331759) B3331759
theorem B2961563 : Blo 1973435 2961563 := bstep (se 1 (by rfl) ⟨2221172, by rfl⟩ : syracuseStep 2961563 = 4442345) B4442345
theorem B1974375 : Blo 1973435 1974375 := bstep (se 1 (by rfl) ⟨1480781, by rfl⟩ : syracuseStep 1974375 = 2961563) B2961563
theorem B2221177 : Blo 1973435 2221177 := bbase (se 2 (by rfl) ⟨832941, by rfl⟩ : syracuseStep 2221177 = 1665883) (by norm_num)
theorem B2961569 : Blo 1973435 2961569 := bstep (se 2 (by rfl) ⟨1110588, by rfl⟩ : syracuseStep 2961569 = 2221177) B2221177
theorem B1974379 : Blo 1973435 1974379 := bstep (se 1 (by rfl) ⟨1480784, by rfl⟩ : syracuseStep 1974379 = 2961569) B2961569
theorem B4274309 : Blo 1973435 4274309 := bbase (se 4 (by rfl) ⟨400716, by rfl⟩ : syracuseStep 4274309 = 801433) (by norm_num)
theorem B11398157 : Blo 1973435 11398157 := bstep (se 3 (by rfl) ⟨2137154, by rfl⟩ : syracuseStep 11398157 = 4274309) B4274309
theorem B7598771 : Blo 1973435 7598771 := bstep (se 1 (by rfl) ⟨5699078, by rfl⟩ : syracuseStep 7598771 = 11398157) B11398157
theorem B5065847 : Blo 1973435 5065847 := bstep (se 1 (by rfl) ⟨3799385, by rfl⟩ : syracuseStep 5065847 = 7598771) B7598771
theorem B3377231 : Blo 1973435 3377231 := bstep (se 1 (by rfl) ⟨2532923, by rfl⟩ : syracuseStep 3377231 = 5065847) B5065847
theorem B2251487 : Blo 1973435 2251487 := bstep (se 1 (by rfl) ⟨1688615, by rfl⟩ : syracuseStep 2251487 = 3377231) B3377231
theorem B6003965 : Blo 1973435 6003965 := bstep (se 3 (by rfl) ⟨1125743, by rfl⟩ : syracuseStep 6003965 = 2251487) B2251487
theorem B4002643 : Blo 1973435 4002643 := bstep (se 1 (by rfl) ⟨3001982, by rfl⟩ : syracuseStep 4002643 = 6003965) B6003965
theorem B5336857 : Blo 1973435 5336857 := bstep (se 2 (by rfl) ⟨2001321, by rfl⟩ : syracuseStep 5336857 = 4002643) B4002643
theorem B28463237 : Blo 1973435 28463237 := bstep (se 4 (by rfl) ⟨2668428, by rfl⟩ : syracuseStep 28463237 = 5336857) B5336857
theorem B18975491 : Blo 1973435 18975491 := bstep (se 1 (by rfl) ⟨14231618, by rfl⟩ : syracuseStep 18975491 = 28463237) B28463237
theorem B12650327 : Blo 1973435 12650327 := bstep (se 1 (by rfl) ⟨9487745, by rfl⟩ : syracuseStep 12650327 = 18975491) B18975491
theorem B8433551 : Blo 1973435 8433551 := bstep (se 1 (by rfl) ⟨6325163, by rfl⟩ : syracuseStep 8433551 = 12650327) B12650327
theorem B5622367 : Blo 1973435 5622367 := bstep (se 1 (by rfl) ⟨4216775, by rfl⟩ : syracuseStep 5622367 = 8433551) B8433551
theorem B7496489 : Blo 1973435 7496489 := bstep (se 2 (by rfl) ⟨2811183, by rfl⟩ : syracuseStep 7496489 = 5622367) B5622367
theorem B4997659 : Blo 1973435 4997659 := bstep (se 1 (by rfl) ⟨3748244, by rfl⟩ : syracuseStep 4997659 = 7496489) B7496489
theorem B6663545 : Blo 1973435 6663545 := bstep (se 2 (by rfl) ⟨2498829, by rfl⟩ : syracuseStep 6663545 = 4997659) B4997659
theorem B4442363 : Blo 1973435 4442363 := bstep (se 1 (by rfl) ⟨3331772, by rfl⟩ : syracuseStep 4442363 = 6663545) B6663545
theorem B2961575 : Blo 1973435 2961575 := bstep (se 1 (by rfl) ⟨2221181, by rfl⟩ : syracuseStep 2961575 = 4442363) B4442363
theorem B1974383 : Blo 1973435 1974383 := bstep (se 1 (by rfl) ⟨1480787, by rfl⟩ : syracuseStep 1974383 = 2961575) B2961575
theorem B2961581 : Blo 1973435 2961581 := bbase (se 3 (by rfl) ⟨555296, by rfl⟩ : syracuseStep 2961581 = 1110593) (by norm_num)
theorem B1974387 : Blo 1973435 1974387 := bstep (se 1 (by rfl) ⟨1480790, by rfl⟩ : syracuseStep 1974387 = 2961581) B2961581
theorem B4442381 : Blo 1973435 4442381 := bbase (se 3 (by rfl) ⟨832946, by rfl⟩ : syracuseStep 4442381 = 1665893) (by norm_num)
theorem B2961587 : Blo 1973435 2961587 := bstep (se 1 (by rfl) ⟨2221190, by rfl⟩ : syracuseStep 2961587 = 4442381) B4442381
theorem B1974391 : Blo 1973435 1974391 := bstep (se 1 (by rfl) ⟨1480793, by rfl⟩ : syracuseStep 1974391 = 2961587) B2961587
theorem B2498845 : Blo 1973435 2498845 := bbase (se 3 (by rfl) ⟨468533, by rfl⟩ : syracuseStep 2498845 = 937067) (by norm_num)
theorem B3331793 : Blo 1973435 3331793 := bstep (se 2 (by rfl) ⟨1249422, by rfl⟩ : syracuseStep 3331793 = 2498845) B2498845
theorem B2221195 : Blo 1973435 2221195 := bstep (se 1 (by rfl) ⟨1665896, by rfl⟩ : syracuseStep 2221195 = 3331793) B3331793
theorem B2961593 : Blo 1973435 2961593 := bstep (se 2 (by rfl) ⟨1110597, by rfl⟩ : syracuseStep 2961593 = 2221195) B2221195
theorem B1974395 : Blo 1973435 1974395 := bstep (se 1 (by rfl) ⟨1480796, by rfl⟩ : syracuseStep 1974395 = 2961593) B2961593
theorem B3042965 : Blo 1973435 3042965 := bbase (se 6 (by rfl) ⟨71319, by rfl⟩ : syracuseStep 3042965 = 142639) (by norm_num)
theorem B8114573 : Blo 1973435 8114573 := bstep (se 3 (by rfl) ⟨1521482, by rfl⟩ : syracuseStep 8114573 = 3042965) B3042965
theorem B5409715 : Blo 1973435 5409715 := bstep (se 1 (by rfl) ⟨4057286, by rfl⟩ : syracuseStep 5409715 = 8114573) B8114573
theorem B7212953 : Blo 1973435 7212953 := bstep (se 2 (by rfl) ⟨2704857, by rfl⟩ : syracuseStep 7212953 = 5409715) B5409715
theorem B4808635 : Blo 1973435 4808635 := bstep (se 1 (by rfl) ⟨3606476, by rfl⟩ : syracuseStep 4808635 = 7212953) B7212953
theorem B25646053 : Blo 1973435 25646053 := bstep (se 4 (by rfl) ⟨2404317, by rfl⟩ : syracuseStep 25646053 = 4808635) B4808635
theorem B34194737 : Blo 1973435 34194737 := bstep (se 2 (by rfl) ⟨12823026, by rfl⟩ : syracuseStep 34194737 = 25646053) B25646053
theorem B22796491 : Blo 1973435 22796491 := bstep (se 1 (by rfl) ⟨17097368, by rfl⟩ : syracuseStep 22796491 = 34194737) B34194737
theorem B30395321 : Blo 1973435 30395321 := bstep (se 2 (by rfl) ⟨11398245, by rfl⟩ : syracuseStep 30395321 = 22796491) B22796491
theorem B20263547 : Blo 1973435 20263547 := bstep (se 1 (by rfl) ⟨15197660, by rfl⟩ : syracuseStep 20263547 = 30395321) B30395321
theorem B13509031 : Blo 1973435 13509031 := bstep (se 1 (by rfl) ⟨10131773, by rfl⟩ : syracuseStep 13509031 = 20263547) B20263547
theorem B18012041 : Blo 1973435 18012041 := bstep (se 2 (by rfl) ⟨6754515, by rfl⟩ : syracuseStep 18012041 = 13509031) B13509031
theorem B12008027 : Blo 1973435 12008027 := bstep (se 1 (by rfl) ⟨9006020, by rfl⟩ : syracuseStep 12008027 = 18012041) B18012041
theorem B8005351 : Blo 1973435 8005351 := bstep (se 1 (by rfl) ⟨6004013, by rfl⟩ : syracuseStep 8005351 = 12008027) B12008027
theorem B10673801 : Blo 1973435 10673801 := bstep (se 2 (by rfl) ⟨4002675, by rfl⟩ : syracuseStep 10673801 = 8005351) B8005351
theorem B7115867 : Blo 1973435 7115867 := bstep (se 1 (by rfl) ⟨5336900, by rfl⟩ : syracuseStep 7115867 = 10673801) B10673801
theorem B4743911 : Blo 1973435 4743911 := bstep (se 1 (by rfl) ⟨3557933, by rfl⟩ : syracuseStep 4743911 = 7115867) B7115867
theorem B3162607 : Blo 1973435 3162607 := bstep (se 1 (by rfl) ⟨2371955, by rfl⟩ : syracuseStep 3162607 = 4743911) B4743911
theorem B16867237 : Blo 1973435 16867237 := bstep (se 4 (by rfl) ⟨1581303, by rfl⟩ : syracuseStep 16867237 = 3162607) B3162607
theorem B22489649 : Blo 1973435 22489649 := bstep (se 2 (by rfl) ⟨8433618, by rfl⟩ : syracuseStep 22489649 = 16867237) B16867237
theorem B14993099 : Blo 1973435 14993099 := bstep (se 1 (by rfl) ⟨11244824, by rfl⟩ : syracuseStep 14993099 = 22489649) B22489649
theorem B9995399 : Blo 1973435 9995399 := bstep (se 1 (by rfl) ⟨7496549, by rfl⟩ : syracuseStep 9995399 = 14993099) B14993099
theorem B6663599 : Blo 1973435 6663599 := bstep (se 1 (by rfl) ⟨4997699, by rfl⟩ : syracuseStep 6663599 = 9995399) B9995399
theorem B4442399 : Blo 1973435 4442399 := bstep (se 1 (by rfl) ⟨3331799, by rfl⟩ : syracuseStep 4442399 = 6663599) B6663599
theorem B2961599 : Blo 1973435 2961599 := bstep (se 1 (by rfl) ⟨2221199, by rfl⟩ : syracuseStep 2961599 = 4442399) B4442399
theorem B1974399 : Blo 1973435 1974399 := bstep (se 1 (by rfl) ⟨1480799, by rfl⟩ : syracuseStep 1974399 = 2961599) B2961599
theorem B2961605 : Blo 1973435 2961605 := bbase (se 4 (by rfl) ⟨277650, by rfl⟩ : syracuseStep 2961605 = 555301) (by norm_num)
theorem B1974403 : Blo 1973435 1974403 := bstep (se 1 (by rfl) ⟨1480802, by rfl⟩ : syracuseStep 1974403 = 2961605) B2961605
theorem B3331813 : Blo 1973435 3331813 := bbase (se 4 (by rfl) ⟨312357, by rfl⟩ : syracuseStep 3331813 = 624715) (by norm_num)
theorem B4442417 : Blo 1973435 4442417 := bstep (se 2 (by rfl) ⟨1665906, by rfl⟩ : syracuseStep 4442417 = 3331813) B3331813
theorem B2961611 : Blo 1973435 2961611 := bstep (se 1 (by rfl) ⟨2221208, by rfl⟩ : syracuseStep 2961611 = 4442417) B4442417
theorem B1974407 : Blo 1973435 1974407 := bstep (se 1 (by rfl) ⟨1480805, by rfl⟩ : syracuseStep 1974407 = 2961611) B2961611
theorem B2221213 : Blo 1973435 2221213 := bbase (se 3 (by rfl) ⟨416477, by rfl⟩ : syracuseStep 2221213 = 832955) (by norm_num)
theorem B2961617 : Blo 1973435 2961617 := bstep (se 2 (by rfl) ⟨1110606, by rfl⟩ : syracuseStep 2961617 = 2221213) B2221213
theorem B1974411 : Blo 1973435 1974411 := bstep (se 1 (by rfl) ⟨1480808, by rfl⟩ : syracuseStep 1974411 = 2961617) B2961617
theorem B6663653 : Blo 1973435 6663653 := bbase (se 4 (by rfl) ⟨624717, by rfl⟩ : syracuseStep 6663653 = 1249435) (by norm_num)
theorem B4442435 : Blo 1973435 4442435 := bstep (se 1 (by rfl) ⟨3331826, by rfl⟩ : syracuseStep 4442435 = 6663653) B6663653
theorem B2961623 : Blo 1973435 2961623 := bstep (se 1 (by rfl) ⟨2221217, by rfl⟩ : syracuseStep 2961623 = 4442435) B4442435
theorem B1974415 : Blo 1973435 1974415 := bstep (se 1 (by rfl) ⟨1480811, by rfl⟩ : syracuseStep 1974415 = 2961623) B2961623
theorem B2961629 : Blo 1973435 2961629 := bbase (se 3 (by rfl) ⟨555305, by rfl⟩ : syracuseStep 2961629 = 1110611) (by norm_num)
theorem B1974419 : Blo 1973435 1974419 := bstep (se 1 (by rfl) ⟨1480814, by rfl⟩ : syracuseStep 1974419 = 2961629) B2961629
theorem B4442453 : Blo 1973435 4442453 := bbase (se 10 (by rfl) ⟨6507, by rfl⟩ : syracuseStep 4442453 = 13015) (by norm_num)
theorem B2961635 : Blo 1973435 2961635 := bstep (se 1 (by rfl) ⟨2221226, by rfl⟩ : syracuseStep 2961635 = 4442453) B4442453
theorem B1974423 : Blo 1973435 1974423 := bstep (se 1 (by rfl) ⟨1480817, by rfl⟩ : syracuseStep 1974423 = 2961635) B2961635
theorem B3162653 : Blo 1973435 3162653 := bbase (se 3 (by rfl) ⟨592997, by rfl⟩ : syracuseStep 3162653 = 1185995) (by norm_num)
theorem B2108435 : Blo 1973435 2108435 := bstep (se 1 (by rfl) ⟨1581326, by rfl⟩ : syracuseStep 2108435 = 3162653) B3162653
theorem B5622493 : Blo 1973435 5622493 := bstep (se 3 (by rfl) ⟨1054217, by rfl⟩ : syracuseStep 5622493 = 2108435) B2108435
theorem B7496657 : Blo 1973435 7496657 := bstep (se 2 (by rfl) ⟨2811246, by rfl⟩ : syracuseStep 7496657 = 5622493) B5622493
theorem B4997771 : Blo 1973435 4997771 := bstep (se 1 (by rfl) ⟨3748328, by rfl⟩ : syracuseStep 4997771 = 7496657) B7496657
theorem B3331847 : Blo 1973435 3331847 := bstep (se 1 (by rfl) ⟨2498885, by rfl⟩ : syracuseStep 3331847 = 4997771) B4997771
theorem B2221231 : Blo 1973435 2221231 := bstep (se 1 (by rfl) ⟨1665923, by rfl⟩ : syracuseStep 2221231 = 3331847) B3331847
theorem B2961641 : Blo 1973435 2961641 := bstep (se 2 (by rfl) ⟨1110615, by rfl⟩ : syracuseStep 2961641 = 2221231) B2221231
theorem B1974427 : Blo 1973435 1974427 := bstep (se 1 (by rfl) ⟨1480820, by rfl⟩ : syracuseStep 1974427 = 2961641) B2961641
theorem B2888485 : Blo 1973435 2888485 := bbase (se 4 (by rfl) ⟨270795, by rfl⟩ : syracuseStep 2888485 = 541591) (by norm_num)
theorem B61621013 : Blo 1973435 61621013 := bstep (se 6 (by rfl) ⟨1444242, by rfl⟩ : syracuseStep 61621013 = 2888485) B2888485
theorem B164322701 : Blo 1973435 164322701 := bstep (se 3 (by rfl) ⟨30810506, by rfl⟩ : syracuseStep 164322701 = 61621013) B61621013
theorem B109548467 : Blo 1973435 109548467 := bstep (se 1 (by rfl) ⟨82161350, by rfl⟩ : syracuseStep 109548467 = 164322701) B164322701
theorem B73032311 : Blo 1973435 73032311 := bstep (se 1 (by rfl) ⟨54774233, by rfl⟩ : syracuseStep 73032311 = 109548467) B109548467
theorem B194752829 : Blo 1973435 194752829 := bstep (se 3 (by rfl) ⟨36516155, by rfl⟩ : syracuseStep 194752829 = 73032311) B73032311
theorem B129835219 : Blo 1973435 129835219 := bstep (se 1 (by rfl) ⟨97376414, by rfl⟩ : syracuseStep 129835219 = 194752829) B194752829
theorem B173113625 : Blo 1973435 173113625 := bstep (se 2 (by rfl) ⟨64917609, by rfl⟩ : syracuseStep 173113625 = 129835219) B129835219
theorem B115409083 : Blo 1973435 115409083 := bstep (se 1 (by rfl) ⟨86556812, by rfl⟩ : syracuseStep 115409083 = 173113625) B173113625
theorem B153878777 : Blo 1973435 153878777 := bstep (se 2 (by rfl) ⟨57704541, by rfl⟩ : syracuseStep 153878777 = 115409083) B115409083
theorem B102585851 : Blo 1973435 102585851 := bstep (se 1 (by rfl) ⟨76939388, by rfl⟩ : syracuseStep 102585851 = 153878777) B153878777
theorem B68390567 : Blo 1973435 68390567 := bstep (se 1 (by rfl) ⟨51292925, by rfl⟩ : syracuseStep 68390567 = 102585851) B102585851
theorem B45593711 : Blo 1973435 45593711 := bstep (se 1 (by rfl) ⟨34195283, by rfl⟩ : syracuseStep 45593711 = 68390567) B68390567
theorem B30395807 : Blo 1973435 30395807 := bstep (se 1 (by rfl) ⟨22796855, by rfl⟩ : syracuseStep 30395807 = 45593711) B45593711
theorem B20263871 : Blo 1973435 20263871 := bstep (se 1 (by rfl) ⟨15197903, by rfl⟩ : syracuseStep 20263871 = 30395807) B30395807
theorem B54036989 : Blo 1973435 54036989 := bstep (se 3 (by rfl) ⟨10131935, by rfl⟩ : syracuseStep 54036989 = 20263871) B20263871
theorem B36024659 : Blo 1973435 36024659 := bstep (se 1 (by rfl) ⟨27018494, by rfl⟩ : syracuseStep 36024659 = 54036989) B54036989
theorem B24016439 : Blo 1973435 24016439 := bstep (se 1 (by rfl) ⟨18012329, by rfl⟩ : syracuseStep 24016439 = 36024659) B36024659
theorem B16010959 : Blo 1973435 16010959 := bstep (se 1 (by rfl) ⟨12008219, by rfl⟩ : syracuseStep 16010959 = 24016439) B24016439
theorem B21347945 : Blo 1973435 21347945 := bstep (se 2 (by rfl) ⟨8005479, by rfl⟩ : syracuseStep 21347945 = 16010959) B16010959
theorem B14231963 : Blo 1973435 14231963 := bstep (se 1 (by rfl) ⟨10673972, by rfl⟩ : syracuseStep 14231963 = 21347945) B21347945
theorem B37951901 : Blo 1973435 37951901 := bstep (se 3 (by rfl) ⟨7115981, by rfl⟩ : syracuseStep 37951901 = 14231963) B14231963
theorem B25301267 : Blo 1973435 25301267 := bstep (se 1 (by rfl) ⟨18975950, by rfl⟩ : syracuseStep 25301267 = 37951901) B37951901
theorem B16867511 : Blo 1973435 16867511 := bstep (se 1 (by rfl) ⟨12650633, by rfl⟩ : syracuseStep 16867511 = 25301267) B25301267
theorem B11245007 : Blo 1973435 11245007 := bstep (se 1 (by rfl) ⟨8433755, by rfl⟩ : syracuseStep 11245007 = 16867511) B16867511
theorem B7496671 : Blo 1973435 7496671 := bstep (se 1 (by rfl) ⟨5622503, by rfl⟩ : syracuseStep 7496671 = 11245007) B11245007
theorem B9995561 : Blo 1973435 9995561 := bstep (se 2 (by rfl) ⟨3748335, by rfl⟩ : syracuseStep 9995561 = 7496671) B7496671
theorem B6663707 : Blo 1973435 6663707 := bstep (se 1 (by rfl) ⟨4997780, by rfl⟩ : syracuseStep 6663707 = 9995561) B9995561
theorem B4442471 : Blo 1973435 4442471 := bstep (se 1 (by rfl) ⟨3331853, by rfl⟩ : syracuseStep 4442471 = 6663707) B6663707
theorem B2961647 : Blo 1973435 2961647 := bstep (se 1 (by rfl) ⟨2221235, by rfl⟩ : syracuseStep 2961647 = 4442471) B4442471
theorem B1974431 : Blo 1973435 1974431 := bstep (se 1 (by rfl) ⟨1480823, by rfl⟩ : syracuseStep 1974431 = 2961647) B2961647
theorem B2961653 : Blo 1973435 2961653 := bbase (se 5 (by rfl) ⟨138827, by rfl⟩ : syracuseStep 2961653 = 277655) (by norm_num)
theorem B1974435 : Blo 1973435 1974435 := bstep (se 1 (by rfl) ⟨1480826, by rfl⟩ : syracuseStep 1974435 = 2961653) B2961653
theorem B72049621 : Blo 1973435 72049621 := bbase (se 7 (by rfl) ⟨844331, by rfl⟩ : syracuseStep 72049621 = 1688663) (by norm_num)
theorem B96066161 : Blo 1973435 96066161 := bstep (se 2 (by rfl) ⟨36024810, by rfl⟩ : syracuseStep 96066161 = 72049621) B72049621
theorem B64044107 : Blo 1973435 64044107 := bstep (se 1 (by rfl) ⟨48033080, by rfl⟩ : syracuseStep 64044107 = 96066161) B96066161
theorem B42696071 : Blo 1973435 42696071 := bstep (se 1 (by rfl) ⟨32022053, by rfl⟩ : syracuseStep 42696071 = 64044107) B64044107
theorem B28464047 : Blo 1973435 28464047 := bstep (se 1 (by rfl) ⟨21348035, by rfl⟩ : syracuseStep 28464047 = 42696071) B42696071
theorem B18976031 : Blo 1973435 18976031 := bstep (se 1 (by rfl) ⟨14232023, by rfl⟩ : syracuseStep 18976031 = 28464047) B28464047
theorem B12650687 : Blo 1973435 12650687 := bstep (se 1 (by rfl) ⟨9488015, by rfl⟩ : syracuseStep 12650687 = 18976031) B18976031
theorem B8433791 : Blo 1973435 8433791 := bstep (se 1 (by rfl) ⟨6325343, by rfl⟩ : syracuseStep 8433791 = 12650687) B12650687
theorem B5622527 : Blo 1973435 5622527 := bstep (se 1 (by rfl) ⟨4216895, by rfl⟩ : syracuseStep 5622527 = 8433791) B8433791
theorem B3748351 : Blo 1973435 3748351 := bstep (se 1 (by rfl) ⟨2811263, by rfl⟩ : syracuseStep 3748351 = 5622527) B5622527
theorem B4997801 : Blo 1973435 4997801 := bstep (se 2 (by rfl) ⟨1874175, by rfl⟩ : syracuseStep 4997801 = 3748351) B3748351
theorem B3331867 : Blo 1973435 3331867 := bstep (se 1 (by rfl) ⟨2498900, by rfl⟩ : syracuseStep 3331867 = 4997801) B4997801
theorem B4442489 : Blo 1973435 4442489 := bstep (se 2 (by rfl) ⟨1665933, by rfl⟩ : syracuseStep 4442489 = 3331867) B3331867
theorem B2961659 : Blo 1973435 2961659 := bstep (se 1 (by rfl) ⟨2221244, by rfl⟩ : syracuseStep 2961659 = 4442489) B4442489
theorem B1974439 : Blo 1973435 1974439 := bstep (se 1 (by rfl) ⟨1480829, by rfl⟩ : syracuseStep 1974439 = 2961659) B2961659
theorem B2221249 : Blo 1973435 2221249 := bbase (se 2 (by rfl) ⟨832968, by rfl⟩ : syracuseStep 2221249 = 1665937) (by norm_num)
theorem B2961665 : Blo 1973435 2961665 := bstep (se 2 (by rfl) ⟨1110624, by rfl⟩ : syracuseStep 2961665 = 2221249) B2221249
theorem B1974443 : Blo 1973435 1974443 := bstep (se 1 (by rfl) ⟨1480832, by rfl⟩ : syracuseStep 1974443 = 2961665) B2961665
theorem B4997821 : Blo 1973435 4997821 := bbase (se 3 (by rfl) ⟨937091, by rfl⟩ : syracuseStep 4997821 = 1874183) (by norm_num)
theorem B6663761 : Blo 1973435 6663761 := bstep (se 2 (by rfl) ⟨2498910, by rfl⟩ : syracuseStep 6663761 = 4997821) B4997821
theorem B4442507 : Blo 1973435 4442507 := bstep (se 1 (by rfl) ⟨3331880, by rfl⟩ : syracuseStep 4442507 = 6663761) B6663761
theorem B2961671 : Blo 1973435 2961671 := bstep (se 1 (by rfl) ⟨2221253, by rfl⟩ : syracuseStep 2961671 = 4442507) B4442507
theorem B1974447 : Blo 1973435 1974447 := bstep (se 1 (by rfl) ⟨1480835, by rfl⟩ : syracuseStep 1974447 = 2961671) B2961671
theorem B2961677 : Blo 1973435 2961677 := bbase (se 3 (by rfl) ⟨555314, by rfl⟩ : syracuseStep 2961677 = 1110629) (by norm_num)
theorem B1974451 : Blo 1973435 1974451 := bstep (se 1 (by rfl) ⟨1480838, by rfl⟩ : syracuseStep 1974451 = 2961677) B2961677
theorem B4442525 : Blo 1973435 4442525 := bbase (se 3 (by rfl) ⟨832973, by rfl⟩ : syracuseStep 4442525 = 1665947) (by norm_num)
theorem B2961683 : Blo 1973435 2961683 := bstep (se 1 (by rfl) ⟨2221262, by rfl⟩ : syracuseStep 2961683 = 4442525) B4442525
theorem B1974455 : Blo 1973435 1974455 := bstep (se 1 (by rfl) ⟨1480841, by rfl⟩ : syracuseStep 1974455 = 2961683) B2961683
theorem B3331901 : Blo 1973435 3331901 := bbase (se 3 (by rfl) ⟨624731, by rfl⟩ : syracuseStep 3331901 = 1249463) (by norm_num)
theorem B2221267 : Blo 1973435 2221267 := bstep (se 1 (by rfl) ⟨1665950, by rfl⟩ : syracuseStep 2221267 = 3331901) B3331901
theorem B2961689 : Blo 1973435 2961689 := bstep (se 2 (by rfl) ⟨1110633, by rfl⟩ : syracuseStep 2961689 = 2221267) B2221267
theorem B1974459 : Blo 1973435 1974459 := bstep (se 1 (by rfl) ⟨1480844, by rfl⟩ : syracuseStep 1974459 = 2961689) B2961689
theorem B2108473 : Blo 1973435 2108473 := bbase (se 2 (by rfl) ⟨790677, by rfl⟩ : syracuseStep 2108473 = 1581355) (by norm_num)
theorem B11245189 : Blo 1973435 11245189 := bstep (se 4 (by rfl) ⟨1054236, by rfl⟩ : syracuseStep 11245189 = 2108473) B2108473
theorem B14993585 : Blo 1973435 14993585 := bstep (se 2 (by rfl) ⟨5622594, by rfl⟩ : syracuseStep 14993585 = 11245189) B11245189
theorem B9995723 : Blo 1973435 9995723 := bstep (se 1 (by rfl) ⟨7496792, by rfl⟩ : syracuseStep 9995723 = 14993585) B14993585
theorem B6663815 : Blo 1973435 6663815 := bstep (se 1 (by rfl) ⟨4997861, by rfl⟩ : syracuseStep 6663815 = 9995723) B9995723
theorem B4442543 : Blo 1973435 4442543 := bstep (se 1 (by rfl) ⟨3331907, by rfl⟩ : syracuseStep 4442543 = 6663815) B6663815
theorem B2961695 : Blo 1973435 2961695 := bstep (se 1 (by rfl) ⟨2221271, by rfl⟩ : syracuseStep 2961695 = 4442543) B4442543
theorem B1974463 : Blo 1973435 1974463 := bstep (se 1 (by rfl) ⟨1480847, by rfl⟩ : syracuseStep 1974463 = 2961695) B2961695
theorem B2961701 : Blo 1973435 2961701 := bbase (se 4 (by rfl) ⟨277659, by rfl⟩ : syracuseStep 2961701 = 555319) (by norm_num)
theorem B1974467 : Blo 1973435 1974467 := bstep (se 1 (by rfl) ⟨1480850, by rfl⟩ : syracuseStep 1974467 = 2961701) B2961701
theorem B2498941 : Blo 1973435 2498941 := bbase (se 3 (by rfl) ⟨468551, by rfl⟩ : syracuseStep 2498941 = 937103) (by norm_num)
theorem B3331921 : Blo 1973435 3331921 := bstep (se 2 (by rfl) ⟨1249470, by rfl⟩ : syracuseStep 3331921 = 2498941) B2498941
theorem B4442561 : Blo 1973435 4442561 := bstep (se 2 (by rfl) ⟨1665960, by rfl⟩ : syracuseStep 4442561 = 3331921) B3331921
theorem B2961707 : Blo 1973435 2961707 := bstep (se 1 (by rfl) ⟨2221280, by rfl⟩ : syracuseStep 2961707 = 4442561) B4442561
theorem B1974471 : Blo 1973435 1974471 := bstep (se 1 (by rfl) ⟨1480853, by rfl⟩ : syracuseStep 1974471 = 2961707) B2961707
theorem B2221285 : Blo 1973435 2221285 := bbase (se 4 (by rfl) ⟨208245, by rfl⟩ : syracuseStep 2221285 = 416491) (by norm_num)
theorem B2961713 : Blo 1973435 2961713 := bstep (se 2 (by rfl) ⟨1110642, by rfl⟩ : syracuseStep 2961713 = 2221285) B2221285
theorem B1974475 : Blo 1973435 1974475 := bstep (se 1 (by rfl) ⟨1480856, by rfl⟩ : syracuseStep 1974475 = 2961713) B2961713
theorem B4216981 : Blo 1973435 4216981 := bbase (se 6 (by rfl) ⟨98835, by rfl⟩ : syracuseStep 4216981 = 197671) (by norm_num)
theorem B5622641 : Blo 1973435 5622641 := bstep (se 2 (by rfl) ⟨2108490, by rfl⟩ : syracuseStep 5622641 = 4216981) B4216981
theorem B3748427 : Blo 1973435 3748427 := bstep (se 1 (by rfl) ⟨2811320, by rfl⟩ : syracuseStep 3748427 = 5622641) B5622641
theorem B2498951 : Blo 1973435 2498951 := bstep (se 1 (by rfl) ⟨1874213, by rfl⟩ : syracuseStep 2498951 = 3748427) B3748427
theorem B6663869 : Blo 1973435 6663869 := bstep (se 3 (by rfl) ⟨1249475, by rfl⟩ : syracuseStep 6663869 = 2498951) B2498951
theorem B4442579 : Blo 1973435 4442579 := bstep (se 1 (by rfl) ⟨3331934, by rfl⟩ : syracuseStep 4442579 = 6663869) B6663869
theorem B2961719 : Blo 1973435 2961719 := bstep (se 1 (by rfl) ⟨2221289, by rfl⟩ : syracuseStep 2961719 = 4442579) B4442579
theorem B1974479 : Blo 1973435 1974479 := bstep (se 1 (by rfl) ⟨1480859, by rfl⟩ : syracuseStep 1974479 = 2961719) B2961719
theorem B2961725 : Blo 1973435 2961725 := bbase (se 3 (by rfl) ⟨555323, by rfl⟩ : syracuseStep 2961725 = 1110647) (by norm_num)
theorem B1974483 : Blo 1973435 1974483 := bstep (se 1 (by rfl) ⟨1480862, by rfl⟩ : syracuseStep 1974483 = 2961725) B2961725
theorem B4442597 : Blo 1973435 4442597 := bbase (se 4 (by rfl) ⟨416493, by rfl⟩ : syracuseStep 4442597 = 832987) (by norm_num)
theorem B2961731 : Blo 1973435 2961731 := bstep (se 1 (by rfl) ⟨2221298, by rfl⟩ : syracuseStep 2961731 = 4442597) B4442597
theorem B1974487 : Blo 1973435 1974487 := bstep (se 1 (by rfl) ⟨1480865, by rfl⟩ : syracuseStep 1974487 = 2961731) B2961731
theorem B4997933 : Blo 1973435 4997933 := bbase (se 3 (by rfl) ⟨937112, by rfl⟩ : syracuseStep 4997933 = 1874225) (by norm_num)
theorem B3331955 : Blo 1973435 3331955 := bstep (se 1 (by rfl) ⟨2498966, by rfl⟩ : syracuseStep 3331955 = 4997933) B4997933
theorem B2221303 : Blo 1973435 2221303 := bstep (se 1 (by rfl) ⟨1665977, by rfl⟩ : syracuseStep 2221303 = 3331955) B3331955
theorem B2961737 : Blo 1973435 2961737 := bstep (se 2 (by rfl) ⟨1110651, by rfl⟩ : syracuseStep 2961737 = 2221303) B2221303
theorem B1974491 : Blo 1973435 1974491 := bstep (se 1 (by rfl) ⟨1480868, by rfl⟩ : syracuseStep 1974491 = 2961737) B2961737
theorem B11398805 : Blo 1973435 11398805 := bbase (se 6 (by rfl) ⟨267159, by rfl⟩ : syracuseStep 11398805 = 534319) (by norm_num)
theorem B7599203 : Blo 1973435 7599203 := bstep (se 1 (by rfl) ⟨5699402, by rfl⟩ : syracuseStep 7599203 = 11398805) B11398805
theorem B5066135 : Blo 1973435 5066135 := bstep (se 1 (by rfl) ⟨3799601, by rfl⟩ : syracuseStep 5066135 = 7599203) B7599203
theorem B3377423 : Blo 1973435 3377423 := bstep (se 1 (by rfl) ⟨2533067, by rfl⟩ : syracuseStep 3377423 = 5066135) B5066135
theorem B9006461 : Blo 1973435 9006461 := bstep (se 3 (by rfl) ⟨1688711, by rfl⟩ : syracuseStep 9006461 = 3377423) B3377423
theorem B6004307 : Blo 1973435 6004307 := bstep (se 1 (by rfl) ⟨4503230, by rfl⟩ : syracuseStep 6004307 = 9006461) B9006461
theorem B4002871 : Blo 1973435 4002871 := bstep (se 1 (by rfl) ⟨3002153, by rfl⟩ : syracuseStep 4002871 = 6004307) B6004307
theorem B5337161 : Blo 1973435 5337161 := bstep (se 2 (by rfl) ⟨2001435, by rfl⟩ : syracuseStep 5337161 = 4002871) B4002871
theorem B3558107 : Blo 1973435 3558107 := bstep (se 1 (by rfl) ⟨2668580, by rfl⟩ : syracuseStep 3558107 = 5337161) B5337161
theorem B9488285 : Blo 1973435 9488285 := bstep (se 3 (by rfl) ⟨1779053, by rfl⟩ : syracuseStep 9488285 = 3558107) B3558107
theorem B6325523 : Blo 1973435 6325523 := bstep (se 1 (by rfl) ⟨4744142, by rfl⟩ : syracuseStep 6325523 = 9488285) B9488285
theorem B4217015 : Blo 1973435 4217015 := bstep (se 1 (by rfl) ⟨3162761, by rfl⟩ : syracuseStep 4217015 = 6325523) B6325523
theorem B2811343 : Blo 1973435 2811343 := bstep (se 1 (by rfl) ⟨2108507, by rfl⟩ : syracuseStep 2811343 = 4217015) B4217015
theorem B3748457 : Blo 1973435 3748457 := bstep (se 2 (by rfl) ⟨1405671, by rfl⟩ : syracuseStep 3748457 = 2811343) B2811343
theorem B9995885 : Blo 1973435 9995885 := bstep (se 3 (by rfl) ⟨1874228, by rfl⟩ : syracuseStep 9995885 = 3748457) B3748457
theorem B6663923 : Blo 1973435 6663923 := bstep (se 1 (by rfl) ⟨4997942, by rfl⟩ : syracuseStep 6663923 = 9995885) B9995885
theorem B4442615 : Blo 1973435 4442615 := bstep (se 1 (by rfl) ⟨3331961, by rfl⟩ : syracuseStep 4442615 = 6663923) B6663923
theorem B2961743 : Blo 1973435 2961743 := bstep (se 1 (by rfl) ⟨2221307, by rfl⟩ : syracuseStep 2961743 = 4442615) B4442615
theorem B1974495 : Blo 1973435 1974495 := bstep (se 1 (by rfl) ⟨1480871, by rfl⟩ : syracuseStep 1974495 = 2961743) B2961743
theorem B2961749 : Blo 1973435 2961749 := bbase (se 10 (by rfl) ⟨4338, by rfl⟩ : syracuseStep 2961749 = 8677) (by norm_num)
theorem B1974499 : Blo 1973435 1974499 := bstep (se 1 (by rfl) ⟨1480874, by rfl⟩ : syracuseStep 1974499 = 2961749) B2961749
theorem B5622709 : Blo 1973435 5622709 := bbase (se 5 (by rfl) ⟨263564, by rfl⟩ : syracuseStep 5622709 = 527129) (by norm_num)
theorem B7496945 : Blo 1973435 7496945 := bstep (se 2 (by rfl) ⟨2811354, by rfl⟩ : syracuseStep 7496945 = 5622709) B5622709
theorem B4997963 : Blo 1973435 4997963 := bstep (se 1 (by rfl) ⟨3748472, by rfl⟩ : syracuseStep 4997963 = 7496945) B7496945
theorem B3331975 : Blo 1973435 3331975 := bstep (se 1 (by rfl) ⟨2498981, by rfl⟩ : syracuseStep 3331975 = 4997963) B4997963
theorem B4442633 : Blo 1973435 4442633 := bstep (se 2 (by rfl) ⟨1665987, by rfl⟩ : syracuseStep 4442633 = 3331975) B3331975
theorem B2961755 : Blo 1973435 2961755 := bstep (se 1 (by rfl) ⟨2221316, by rfl⟩ : syracuseStep 2961755 = 4442633) B4442633
theorem B1974503 : Blo 1973435 1974503 := bstep (se 1 (by rfl) ⟨1480877, by rfl⟩ : syracuseStep 1974503 = 2961755) B2961755
theorem B2221321 : Blo 1973435 2221321 := bbase (se 2 (by rfl) ⟨832995, by rfl⟩ : syracuseStep 2221321 = 1665991) (by norm_num)
theorem B2961761 : Blo 1973435 2961761 := bstep (se 2 (by rfl) ⟨1110660, by rfl⟩ : syracuseStep 2961761 = 2221321) B2221321
theorem B1974507 : Blo 1973435 1974507 := bstep (se 1 (by rfl) ⟨1480880, by rfl⟩ : syracuseStep 1974507 = 2961761) B2961761
theorem B25302293 : Blo 1973435 25302293 := bbase (se 6 (by rfl) ⟨593022, by rfl⟩ : syracuseStep 25302293 = 1186045) (by norm_num)
theorem B16868195 : Blo 1973435 16868195 := bstep (se 1 (by rfl) ⟨12651146, by rfl⟩ : syracuseStep 16868195 = 25302293) B25302293
theorem B11245463 : Blo 1973435 11245463 := bstep (se 1 (by rfl) ⟨8434097, by rfl⟩ : syracuseStep 11245463 = 16868195) B16868195
theorem B7496975 : Blo 1973435 7496975 := bstep (se 1 (by rfl) ⟨5622731, by rfl⟩ : syracuseStep 7496975 = 11245463) B11245463
theorem B4997983 : Blo 1973435 4997983 := bstep (se 1 (by rfl) ⟨3748487, by rfl⟩ : syracuseStep 4997983 = 7496975) B7496975
theorem B6663977 : Blo 1973435 6663977 := bstep (se 2 (by rfl) ⟨2498991, by rfl⟩ : syracuseStep 6663977 = 4997983) B4997983
theorem B4442651 : Blo 1973435 4442651 := bstep (se 1 (by rfl) ⟨3331988, by rfl⟩ : syracuseStep 4442651 = 6663977) B6663977
theorem B2961767 : Blo 1973435 2961767 := bstep (se 1 (by rfl) ⟨2221325, by rfl⟩ : syracuseStep 2961767 = 4442651) B4442651
theorem B1974511 : Blo 1973435 1974511 := bstep (se 1 (by rfl) ⟨1480883, by rfl⟩ : syracuseStep 1974511 = 2961767) B2961767
theorem B2961773 : Blo 1973435 2961773 := bbase (se 3 (by rfl) ⟨555332, by rfl⟩ : syracuseStep 2961773 = 1110665) (by norm_num)
theorem B1974515 : Blo 1973435 1974515 := bstep (se 1 (by rfl) ⟨1480886, by rfl⟩ : syracuseStep 1974515 = 2961773) B2961773
theorem B4442669 : Blo 1973435 4442669 := bbase (se 3 (by rfl) ⟨833000, by rfl⟩ : syracuseStep 4442669 = 1666001) (by norm_num)
theorem B2961779 : Blo 1973435 2961779 := bstep (se 1 (by rfl) ⟨2221334, by rfl⟩ : syracuseStep 2961779 = 4442669) B4442669
theorem B1974519 : Blo 1973435 1974519 := bstep (se 1 (by rfl) ⟨1480889, by rfl⟩ : syracuseStep 1974519 = 2961779) B2961779
theorem B2404469 : Blo 1973435 2404469 := bbase (se 5 (by rfl) ⟨112709, by rfl⟩ : syracuseStep 2404469 = 225419) (by norm_num)
theorem B6411917 : Blo 1973435 6411917 := bstep (se 3 (by rfl) ⟨1202234, by rfl⟩ : syracuseStep 6411917 = 2404469) B2404469
theorem B17098445 : Blo 1973435 17098445 := bstep (se 3 (by rfl) ⟨3205958, by rfl⟩ : syracuseStep 17098445 = 6411917) B6411917
theorem B11398963 : Blo 1973435 11398963 := bstep (se 1 (by rfl) ⟨8549222, by rfl⟩ : syracuseStep 11398963 = 17098445) B17098445
theorem B15198617 : Blo 1973435 15198617 := bstep (se 2 (by rfl) ⟨5699481, by rfl⟩ : syracuseStep 15198617 = 11398963) B11398963
theorem B40529645 : Blo 1973435 40529645 := bstep (se 3 (by rfl) ⟨7599308, by rfl⟩ : syracuseStep 40529645 = 15198617) B15198617
theorem B27019763 : Blo 1973435 27019763 := bstep (se 1 (by rfl) ⟨20264822, by rfl⟩ : syracuseStep 27019763 = 40529645) B40529645
theorem B18013175 : Blo 1973435 18013175 := bstep (se 1 (by rfl) ⟨13509881, by rfl⟩ : syracuseStep 18013175 = 27019763) B27019763
theorem B12008783 : Blo 1973435 12008783 := bstep (se 1 (by rfl) ⟨9006587, by rfl⟩ : syracuseStep 12008783 = 18013175) B18013175
theorem B32023421 : Blo 1973435 32023421 := bstep (se 3 (by rfl) ⟨6004391, by rfl⟩ : syracuseStep 32023421 = 12008783) B12008783
theorem B21348947 : Blo 1973435 21348947 := bstep (se 1 (by rfl) ⟨16011710, by rfl⟩ : syracuseStep 21348947 = 32023421) B32023421
theorem B14232631 : Blo 1973435 14232631 := bstep (se 1 (by rfl) ⟨10674473, by rfl⟩ : syracuseStep 14232631 = 21348947) B21348947
theorem B18976841 : Blo 1973435 18976841 := bstep (se 2 (by rfl) ⟨7116315, by rfl⟩ : syracuseStep 18976841 = 14232631) B14232631
theorem B12651227 : Blo 1973435 12651227 := bstep (se 1 (by rfl) ⟨9488420, by rfl⟩ : syracuseStep 12651227 = 18976841) B18976841
theorem B8434151 : Blo 1973435 8434151 := bstep (se 1 (by rfl) ⟨6325613, by rfl⟩ : syracuseStep 8434151 = 12651227) B12651227
theorem B5622767 : Blo 1973435 5622767 := bstep (se 1 (by rfl) ⟨4217075, by rfl⟩ : syracuseStep 5622767 = 8434151) B8434151
theorem B3748511 : Blo 1973435 3748511 := bstep (se 1 (by rfl) ⟨2811383, by rfl⟩ : syracuseStep 3748511 = 5622767) B5622767
theorem B2499007 : Blo 1973435 2499007 := bstep (se 1 (by rfl) ⟨1874255, by rfl⟩ : syracuseStep 2499007 = 3748511) B3748511
theorem B3332009 : Blo 1973435 3332009 := bstep (se 2 (by rfl) ⟨1249503, by rfl⟩ : syracuseStep 3332009 = 2499007) B2499007
theorem B2221339 : Blo 1973435 2221339 := bstep (se 1 (by rfl) ⟨1666004, by rfl⟩ : syracuseStep 2221339 = 3332009) B3332009
theorem B2961785 : Blo 1973435 2961785 := bstep (se 2 (by rfl) ⟨1110669, by rfl⟩ : syracuseStep 2961785 = 2221339) B2221339
theorem B1974523 : Blo 1973435 1974523 := bstep (se 1 (by rfl) ⟨1480892, by rfl⟩ : syracuseStep 1974523 = 2961785) B2961785
theorem B33736661 : Blo 1973435 33736661 := bbase (se 7 (by rfl) ⟨395351, by rfl⟩ : syracuseStep 33736661 = 790703) (by norm_num)
theorem B22491107 : Blo 1973435 22491107 := bstep (se 1 (by rfl) ⟨16868330, by rfl⟩ : syracuseStep 22491107 = 33736661) B33736661
theorem B14994071 : Blo 1973435 14994071 := bstep (se 1 (by rfl) ⟨11245553, by rfl⟩ : syracuseStep 14994071 = 22491107) B22491107
theorem B9996047 : Blo 1973435 9996047 := bstep (se 1 (by rfl) ⟨7497035, by rfl⟩ : syracuseStep 9996047 = 14994071) B14994071
theorem B6664031 : Blo 1973435 6664031 := bstep (se 1 (by rfl) ⟨4998023, by rfl⟩ : syracuseStep 6664031 = 9996047) B9996047
theorem B4442687 : Blo 1973435 4442687 := bstep (se 1 (by rfl) ⟨3332015, by rfl⟩ : syracuseStep 4442687 = 6664031) B6664031
theorem B2961791 : Blo 1973435 2961791 := bstep (se 1 (by rfl) ⟨2221343, by rfl⟩ : syracuseStep 2961791 = 4442687) B4442687
theorem B1974527 : Blo 1973435 1974527 := bstep (se 1 (by rfl) ⟨1480895, by rfl⟩ : syracuseStep 1974527 = 2961791) B2961791
theorem B2961797 : Blo 1973435 2961797 := bbase (se 4 (by rfl) ⟨277668, by rfl⟩ : syracuseStep 2961797 = 555337) (by norm_num)
theorem B1974531 : Blo 1973435 1974531 := bstep (se 1 (by rfl) ⟨1480898, by rfl⟩ : syracuseStep 1974531 = 2961797) B2961797
theorem B3332029 : Blo 1973435 3332029 := bbase (se 3 (by rfl) ⟨624755, by rfl⟩ : syracuseStep 3332029 = 1249511) (by norm_num)
theorem B4442705 : Blo 1973435 4442705 := bstep (se 2 (by rfl) ⟨1666014, by rfl⟩ : syracuseStep 4442705 = 3332029) B3332029
theorem B2961803 : Blo 1973435 2961803 := bstep (se 1 (by rfl) ⟨2221352, by rfl⟩ : syracuseStep 2961803 = 4442705) B4442705
theorem B1974535 : Blo 1973435 1974535 := bstep (se 1 (by rfl) ⟨1480901, by rfl⟩ : syracuseStep 1974535 = 2961803) B2961803
theorem B2221357 : Blo 1973435 2221357 := bbase (se 3 (by rfl) ⟨416504, by rfl⟩ : syracuseStep 2221357 = 833009) (by norm_num)
theorem B2961809 : Blo 1973435 2961809 := bstep (se 2 (by rfl) ⟨1110678, by rfl⟩ : syracuseStep 2961809 = 2221357) B2221357
theorem B1974539 : Blo 1973435 1974539 := bstep (se 1 (by rfl) ⟨1480904, by rfl⟩ : syracuseStep 1974539 = 2961809) B2961809
theorem B6664085 : Blo 1973435 6664085 := bbase (se 6 (by rfl) ⟨156189, by rfl⟩ : syracuseStep 6664085 = 312379) (by norm_num)
theorem B4442723 : Blo 1973435 4442723 := bstep (se 1 (by rfl) ⟨3332042, by rfl⟩ : syracuseStep 4442723 = 6664085) B6664085
theorem B2961815 : Blo 1973435 2961815 := bstep (se 1 (by rfl) ⟨2221361, by rfl⟩ : syracuseStep 2961815 = 4442723) B4442723
theorem B1974543 : Blo 1973435 1974543 := bstep (se 1 (by rfl) ⟨1480907, by rfl⟩ : syracuseStep 1974543 = 2961815) B2961815
theorem B2961821 : Blo 1973435 2961821 := bbase (se 3 (by rfl) ⟨555341, by rfl⟩ : syracuseStep 2961821 = 1110683) (by norm_num)
theorem B1974547 : Blo 1973435 1974547 := bstep (se 1 (by rfl) ⟨1480910, by rfl⟩ : syracuseStep 1974547 = 2961821) B2961821
theorem B4442741 : Blo 1973435 4442741 := bbase (se 5 (by rfl) ⟨208253, by rfl⟩ : syracuseStep 4442741 = 416507) (by norm_num)
theorem B2961827 : Blo 1973435 2961827 := bstep (se 1 (by rfl) ⟨2221370, by rfl⟩ : syracuseStep 2961827 = 4442741) B4442741
theorem B1974551 : Blo 1973435 1974551 := bstep (se 1 (by rfl) ⟨1480913, by rfl⟩ : syracuseStep 1974551 = 2961827) B2961827
theorem B5135413 : Blo 1973435 5135413 := bbase (se 5 (by rfl) ⟨240722, by rfl⟩ : syracuseStep 5135413 = 481445) (by norm_num)
theorem B6847217 : Blo 1973435 6847217 := bstep (se 2 (by rfl) ⟨2567706, by rfl⟩ : syracuseStep 6847217 = 5135413) B5135413
theorem B4564811 : Blo 1973435 4564811 := bstep (se 1 (by rfl) ⟨3423608, by rfl⟩ : syracuseStep 4564811 = 6847217) B6847217
theorem B3043207 : Blo 1973435 3043207 := bstep (se 1 (by rfl) ⟨2282405, by rfl⟩ : syracuseStep 3043207 = 4564811) B4564811
theorem B4057609 : Blo 1973435 4057609 := bstep (se 2 (by rfl) ⟨1521603, by rfl⟩ : syracuseStep 4057609 = 3043207) B3043207
theorem B5410145 : Blo 1973435 5410145 := bstep (se 2 (by rfl) ⟨2028804, by rfl⟩ : syracuseStep 5410145 = 4057609) B4057609
theorem B3606763 : Blo 1973435 3606763 := bstep (se 1 (by rfl) ⟨2705072, by rfl⟩ : syracuseStep 3606763 = 5410145) B5410145
theorem B4809017 : Blo 1973435 4809017 := bstep (se 2 (by rfl) ⟨1803381, by rfl⟩ : syracuseStep 4809017 = 3606763) B3606763
theorem B12824045 : Blo 1973435 12824045 := bstep (se 3 (by rfl) ⟨2404508, by rfl⟩ : syracuseStep 12824045 = 4809017) B4809017
theorem B8549363 : Blo 1973435 8549363 := bstep (se 1 (by rfl) ⟨6412022, by rfl⟩ : syracuseStep 8549363 = 12824045) B12824045
theorem B5699575 : Blo 1973435 5699575 := bstep (se 1 (by rfl) ⟨4274681, by rfl⟩ : syracuseStep 5699575 = 8549363) B8549363
theorem B7599433 : Blo 1973435 7599433 := bstep (se 2 (by rfl) ⟨2849787, by rfl⟩ : syracuseStep 7599433 = 5699575) B5699575
theorem B10132577 : Blo 1973435 10132577 := bstep (se 2 (by rfl) ⟨3799716, by rfl⟩ : syracuseStep 10132577 = 7599433) B7599433
theorem B6755051 : Blo 1973435 6755051 := bstep (se 1 (by rfl) ⟨5066288, by rfl⟩ : syracuseStep 6755051 = 10132577) B10132577
theorem B4503367 : Blo 1973435 4503367 := bstep (se 1 (by rfl) ⟨3377525, by rfl⟩ : syracuseStep 4503367 = 6755051) B6755051
theorem B6004489 : Blo 1973435 6004489 := bstep (se 2 (by rfl) ⟨2251683, by rfl⟩ : syracuseStep 6004489 = 4503367) B4503367
theorem B8005985 : Blo 1973435 8005985 := bstep (se 2 (by rfl) ⟨3002244, by rfl⟩ : syracuseStep 8005985 = 6004489) B6004489
theorem B5337323 : Blo 1973435 5337323 := bstep (se 1 (by rfl) ⟨4002992, by rfl⟩ : syracuseStep 5337323 = 8005985) B8005985
theorem B3558215 : Blo 1973435 3558215 := bstep (se 1 (by rfl) ⟨2668661, by rfl⟩ : syracuseStep 3558215 = 5337323) B5337323
theorem B9488573 : Blo 1973435 9488573 := bstep (se 3 (by rfl) ⟨1779107, by rfl⟩ : syracuseStep 9488573 = 3558215) B3558215
theorem B6325715 : Blo 1973435 6325715 := bstep (se 1 (by rfl) ⟨4744286, by rfl⟩ : syracuseStep 6325715 = 9488573) B9488573
theorem B16868573 : Blo 1973435 16868573 := bstep (se 3 (by rfl) ⟨3162857, by rfl⟩ : syracuseStep 16868573 = 6325715) B6325715
theorem B11245715 : Blo 1973435 11245715 := bstep (se 1 (by rfl) ⟨8434286, by rfl⟩ : syracuseStep 11245715 = 16868573) B16868573
theorem B7497143 : Blo 1973435 7497143 := bstep (se 1 (by rfl) ⟨5622857, by rfl⟩ : syracuseStep 7497143 = 11245715) B11245715
theorem B4998095 : Blo 1973435 4998095 := bstep (se 1 (by rfl) ⟨3748571, by rfl⟩ : syracuseStep 4998095 = 7497143) B7497143
theorem B3332063 : Blo 1973435 3332063 := bstep (se 1 (by rfl) ⟨2499047, by rfl⟩ : syracuseStep 3332063 = 4998095) B4998095
theorem B2221375 : Blo 1973435 2221375 := bstep (se 1 (by rfl) ⟨1666031, by rfl⟩ : syracuseStep 2221375 = 3332063) B3332063
theorem B2961833 : Blo 1973435 2961833 := bstep (se 2 (by rfl) ⟨1110687, by rfl⟩ : syracuseStep 2961833 = 2221375) B2221375
theorem B1974555 : Blo 1973435 1974555 := bstep (se 1 (by rfl) ⟨1480916, by rfl⟩ : syracuseStep 1974555 = 2961833) B2961833
theorem B7497157 : Blo 1973435 7497157 := bbase (se 4 (by rfl) ⟨702858, by rfl⟩ : syracuseStep 7497157 = 1405717) (by norm_num)
theorem B9996209 : Blo 1973435 9996209 := bstep (se 2 (by rfl) ⟨3748578, by rfl⟩ : syracuseStep 9996209 = 7497157) B7497157
theorem B6664139 : Blo 1973435 6664139 := bstep (se 1 (by rfl) ⟨4998104, by rfl⟩ : syracuseStep 6664139 = 9996209) B9996209
theorem B4442759 : Blo 1973435 4442759 := bstep (se 1 (by rfl) ⟨3332069, by rfl⟩ : syracuseStep 4442759 = 6664139) B6664139
theorem B2961839 : Blo 1973435 2961839 := bstep (se 1 (by rfl) ⟨2221379, by rfl⟩ : syracuseStep 2961839 = 4442759) B4442759
theorem B1974559 : Blo 1973435 1974559 := bstep (se 1 (by rfl) ⟨1480919, by rfl⟩ : syracuseStep 1974559 = 2961839) B2961839
theorem B2961845 : Blo 1973435 2961845 := bbase (se 5 (by rfl) ⟨138836, by rfl⟩ : syracuseStep 2961845 = 277673) (by norm_num)
theorem B1974563 : Blo 1973435 1974563 := bstep (se 1 (by rfl) ⟨1480922, by rfl⟩ : syracuseStep 1974563 = 2961845) B2961845
theorem B4998125 : Blo 1973435 4998125 := bbase (se 3 (by rfl) ⟨937148, by rfl⟩ : syracuseStep 4998125 = 1874297) (by norm_num)
theorem B3332083 : Blo 1973435 3332083 := bstep (se 1 (by rfl) ⟨2499062, by rfl⟩ : syracuseStep 3332083 = 4998125) B4998125
theorem B4442777 : Blo 1973435 4442777 := bstep (se 2 (by rfl) ⟨1666041, by rfl⟩ : syracuseStep 4442777 = 3332083) B3332083
theorem B2961851 : Blo 1973435 2961851 := bstep (se 1 (by rfl) ⟨2221388, by rfl⟩ : syracuseStep 2961851 = 4442777) B4442777
theorem B1974567 : Blo 1973435 1974567 := bstep (se 1 (by rfl) ⟨1480925, by rfl⟩ : syracuseStep 1974567 = 2961851) B2961851
theorem B2221393 : Blo 1973435 2221393 := bbase (se 2 (by rfl) ⟨833022, by rfl⟩ : syracuseStep 2221393 = 1666045) (by norm_num)
theorem B2961857 : Blo 1973435 2961857 := bstep (se 2 (by rfl) ⟨1110696, by rfl⟩ : syracuseStep 2961857 = 2221393) B2221393
theorem B1974571 : Blo 1973435 1974571 := bstep (se 1 (by rfl) ⟨1480928, by rfl⟩ : syracuseStep 1974571 = 2961857) B2961857
theorem B2108593 : Blo 1973435 2108593 := bbase (se 2 (by rfl) ⟨790722, by rfl⟩ : syracuseStep 2108593 = 1581445) (by norm_num)
theorem B2811457 : Blo 1973435 2811457 := bstep (se 2 (by rfl) ⟨1054296, by rfl⟩ : syracuseStep 2811457 = 2108593) B2108593
theorem B3748609 : Blo 1973435 3748609 := bstep (se 2 (by rfl) ⟨1405728, by rfl⟩ : syracuseStep 3748609 = 2811457) B2811457
theorem B4998145 : Blo 1973435 4998145 := bstep (se 2 (by rfl) ⟨1874304, by rfl⟩ : syracuseStep 4998145 = 3748609) B3748609
theorem B6664193 : Blo 1973435 6664193 := bstep (se 2 (by rfl) ⟨2499072, by rfl⟩ : syracuseStep 6664193 = 4998145) B4998145
theorem B4442795 : Blo 1973435 4442795 := bstep (se 1 (by rfl) ⟨3332096, by rfl⟩ : syracuseStep 4442795 = 6664193) B6664193
theorem B2961863 : Blo 1973435 2961863 := bstep (se 1 (by rfl) ⟨2221397, by rfl⟩ : syracuseStep 2961863 = 4442795) B4442795
theorem B1974575 : Blo 1973435 1974575 := bstep (se 1 (by rfl) ⟨1480931, by rfl⟩ : syracuseStep 1974575 = 2961863) B2961863
theorem B2961869 : Blo 1973435 2961869 := bbase (se 3 (by rfl) ⟨555350, by rfl⟩ : syracuseStep 2961869 = 1110701) (by norm_num)
theorem B1974579 : Blo 1973435 1974579 := bstep (se 1 (by rfl) ⟨1480934, by rfl⟩ : syracuseStep 1974579 = 2961869) B2961869
theorem B4442813 : Blo 1973435 4442813 := bbase (se 3 (by rfl) ⟨833027, by rfl⟩ : syracuseStep 4442813 = 1666055) (by norm_num)
theorem B2961875 : Blo 1973435 2961875 := bstep (se 1 (by rfl) ⟨2221406, by rfl⟩ : syracuseStep 2961875 = 4442813) B4442813
theorem B1974583 : Blo 1973435 1974583 := bstep (se 1 (by rfl) ⟨1480937, by rfl⟩ : syracuseStep 1974583 = 2961875) B2961875
theorem B3332117 : Blo 1973435 3332117 := bbase (se 6 (by rfl) ⟨78096, by rfl⟩ : syracuseStep 3332117 = 156193) (by norm_num)
theorem B2221411 : Blo 1973435 2221411 := bstep (se 1 (by rfl) ⟨1666058, by rfl⟩ : syracuseStep 2221411 = 3332117) B3332117
theorem B2961881 : Blo 1973435 2961881 := bstep (se 2 (by rfl) ⟨1110705, by rfl⟩ : syracuseStep 2961881 = 2221411) B2221411
theorem B1974587 : Blo 1973435 1974587 := bstep (se 1 (by rfl) ⟨1480940, by rfl⟩ : syracuseStep 1974587 = 2961881) B2961881
theorem B6004597 : Blo 1973435 6004597 := bbase (se 5 (by rfl) ⟨281465, by rfl⟩ : syracuseStep 6004597 = 562931) (by norm_num)
theorem B8006129 : Blo 1973435 8006129 := bstep (se 2 (by rfl) ⟨3002298, by rfl⟩ : syracuseStep 8006129 = 6004597) B6004597
theorem B5337419 : Blo 1973435 5337419 := bstep (se 1 (by rfl) ⟨4003064, by rfl⟩ : syracuseStep 5337419 = 8006129) B8006129
theorem B14233117 : Blo 1973435 14233117 := bstep (se 3 (by rfl) ⟨2668709, by rfl⟩ : syracuseStep 14233117 = 5337419) B5337419
theorem B18977489 : Blo 1973435 18977489 := bstep (se 2 (by rfl) ⟨7116558, by rfl⟩ : syracuseStep 18977489 = 14233117) B14233117
theorem B12651659 : Blo 1973435 12651659 := bstep (se 1 (by rfl) ⟨9488744, by rfl⟩ : syracuseStep 12651659 = 18977489) B18977489
theorem B8434439 : Blo 1973435 8434439 := bstep (se 1 (by rfl) ⟨6325829, by rfl⟩ : syracuseStep 8434439 = 12651659) B12651659
theorem B5622959 : Blo 1973435 5622959 := bstep (se 1 (by rfl) ⟨4217219, by rfl⟩ : syracuseStep 5622959 = 8434439) B8434439
theorem B14994557 : Blo 1973435 14994557 := bstep (se 3 (by rfl) ⟨2811479, by rfl⟩ : syracuseStep 14994557 = 5622959) B5622959
theorem B9996371 : Blo 1973435 9996371 := bstep (se 1 (by rfl) ⟨7497278, by rfl⟩ : syracuseStep 9996371 = 14994557) B14994557
theorem B6664247 : Blo 1973435 6664247 := bstep (se 1 (by rfl) ⟨4998185, by rfl⟩ : syracuseStep 6664247 = 9996371) B9996371
theorem B4442831 : Blo 1973435 4442831 := bstep (se 1 (by rfl) ⟨3332123, by rfl⟩ : syracuseStep 4442831 = 6664247) B6664247
theorem B2961887 : Blo 1973435 2961887 := bstep (se 1 (by rfl) ⟨2221415, by rfl⟩ : syracuseStep 2961887 = 4442831) B4442831
theorem B1974591 : Blo 1973435 1974591 := bstep (se 1 (by rfl) ⟨1480943, by rfl⟩ : syracuseStep 1974591 = 2961887) B2961887
theorem B2961893 : Blo 1973435 2961893 := bbase (se 4 (by rfl) ⟨277677, by rfl⟩ : syracuseStep 2961893 = 555355) (by norm_num)
theorem B1974595 : Blo 1973435 1974595 := bstep (se 1 (by rfl) ⟨1480946, by rfl⟩ : syracuseStep 1974595 = 2961893) B2961893
theorem B2001541 : Blo 1973435 2001541 := bbase (se 4 (by rfl) ⟨187644, by rfl⟩ : syracuseStep 2001541 = 375289) (by norm_num)
theorem B2668721 : Blo 1973435 2668721 := bstep (se 2 (by rfl) ⟨1000770, by rfl⟩ : syracuseStep 2668721 = 2001541) B2001541
theorem B7116589 : Blo 1973435 7116589 := bstep (se 3 (by rfl) ⟨1334360, by rfl⟩ : syracuseStep 7116589 = 2668721) B2668721
theorem B9488785 : Blo 1973435 9488785 := bstep (se 2 (by rfl) ⟨3558294, by rfl⟩ : syracuseStep 9488785 = 7116589) B7116589
theorem B12651713 : Blo 1973435 12651713 := bstep (se 2 (by rfl) ⟨4744392, by rfl⟩ : syracuseStep 12651713 = 9488785) B9488785
theorem B8434475 : Blo 1973435 8434475 := bstep (se 1 (by rfl) ⟨6325856, by rfl⟩ : syracuseStep 8434475 = 12651713) B12651713
theorem B5622983 : Blo 1973435 5622983 := bstep (se 1 (by rfl) ⟨4217237, by rfl⟩ : syracuseStep 5622983 = 8434475) B8434475
theorem B3748655 : Blo 1973435 3748655 := bstep (se 1 (by rfl) ⟨2811491, by rfl⟩ : syracuseStep 3748655 = 5622983) B5622983
theorem B2499103 : Blo 1973435 2499103 := bstep (se 1 (by rfl) ⟨1874327, by rfl⟩ : syracuseStep 2499103 = 3748655) B3748655
theorem B3332137 : Blo 1973435 3332137 := bstep (se 2 (by rfl) ⟨1249551, by rfl⟩ : syracuseStep 3332137 = 2499103) B2499103
theorem B4442849 : Blo 1973435 4442849 := bstep (se 2 (by rfl) ⟨1666068, by rfl⟩ : syracuseStep 4442849 = 3332137) B3332137
theorem B2961899 : Blo 1973435 2961899 := bstep (se 1 (by rfl) ⟨2221424, by rfl⟩ : syracuseStep 2961899 = 4442849) B4442849
theorem B1974599 : Blo 1973435 1974599 := bstep (se 1 (by rfl) ⟨1480949, by rfl⟩ : syracuseStep 1974599 = 2961899) B2961899
theorem B2221429 : Blo 1973435 2221429 := bbase (se 5 (by rfl) ⟨104129, by rfl⟩ : syracuseStep 2221429 = 208259) (by norm_num)
theorem B2961905 : Blo 1973435 2961905 := bstep (se 2 (by rfl) ⟨1110714, by rfl⟩ : syracuseStep 2961905 = 2221429) B2221429
theorem B1974603 : Blo 1973435 1974603 := bstep (se 1 (by rfl) ⟨1480952, by rfl⟩ : syracuseStep 1974603 = 2961905) B2961905
theorem B2499113 : Blo 1973435 2499113 := bbase (se 2 (by rfl) ⟨937167, by rfl⟩ : syracuseStep 2499113 = 1874335) (by norm_num)
theorem B6664301 : Blo 1973435 6664301 := bstep (se 3 (by rfl) ⟨1249556, by rfl⟩ : syracuseStep 6664301 = 2499113) B2499113
theorem B4442867 : Blo 1973435 4442867 := bstep (se 1 (by rfl) ⟨3332150, by rfl⟩ : syracuseStep 4442867 = 6664301) B6664301
theorem B2961911 : Blo 1973435 2961911 := bstep (se 1 (by rfl) ⟨2221433, by rfl⟩ : syracuseStep 2961911 = 4442867) B4442867
theorem B1974607 : Blo 1973435 1974607 := bstep (se 1 (by rfl) ⟨1480955, by rfl⟩ : syracuseStep 1974607 = 2961911) B2961911
theorem B2961917 : Blo 1973435 2961917 := bbase (se 3 (by rfl) ⟨555359, by rfl⟩ : syracuseStep 2961917 = 1110719) (by norm_num)
theorem B1974611 : Blo 1973435 1974611 := bstep (se 1 (by rfl) ⟨1480958, by rfl⟩ : syracuseStep 1974611 = 2961917) B2961917
theorem B4442885 : Blo 1973435 4442885 := bbase (se 4 (by rfl) ⟨416520, by rfl⟩ : syracuseStep 4442885 = 833041) (by norm_num)
theorem B2961923 : Blo 1973435 2961923 := bstep (se 1 (by rfl) ⟨2221442, by rfl⟩ : syracuseStep 2961923 = 4442885) B4442885
theorem B1974615 : Blo 1973435 1974615 := bstep (se 1 (by rfl) ⟨1480961, by rfl⟩ : syracuseStep 1974615 = 2961923) B2961923
theorem B3748693 : Blo 1973435 3748693 := bbase (se 9 (by rfl) ⟨10982, by rfl⟩ : syracuseStep 3748693 = 21965) (by norm_num)
theorem B4998257 : Blo 1973435 4998257 := bstep (se 2 (by rfl) ⟨1874346, by rfl⟩ : syracuseStep 4998257 = 3748693) B3748693
theorem B3332171 : Blo 1973435 3332171 := bstep (se 1 (by rfl) ⟨2499128, by rfl⟩ : syracuseStep 3332171 = 4998257) B4998257
theorem B2221447 : Blo 1973435 2221447 := bstep (se 1 (by rfl) ⟨1666085, by rfl⟩ : syracuseStep 2221447 = 3332171) B3332171
theorem B2961929 : Blo 1973435 2961929 := bstep (se 2 (by rfl) ⟨1110723, by rfl⟩ : syracuseStep 2961929 = 2221447) B2221447
theorem B1974619 : Blo 1973435 1974619 := bstep (se 1 (by rfl) ⟨1480964, by rfl⟩ : syracuseStep 1974619 = 2961929) B2961929
theorem B9996533 : Blo 1973435 9996533 := bbase (se 5 (by rfl) ⟨468587, by rfl⟩ : syracuseStep 9996533 = 937175) (by norm_num)
theorem B6664355 : Blo 1973435 6664355 := bstep (se 1 (by rfl) ⟨4998266, by rfl⟩ : syracuseStep 6664355 = 9996533) B9996533
theorem B4442903 : Blo 1973435 4442903 := bstep (se 1 (by rfl) ⟨3332177, by rfl⟩ : syracuseStep 4442903 = 6664355) B6664355
theorem B2961935 : Blo 1973435 2961935 := bstep (se 1 (by rfl) ⟨2221451, by rfl⟩ : syracuseStep 2961935 = 4442903) B4442903
theorem B1974623 : Blo 1973435 1974623 := bstep (se 1 (by rfl) ⟨1480967, by rfl⟩ : syracuseStep 1974623 = 2961935) B2961935
theorem B2961941 : Blo 1973435 2961941 := bbase (se 6 (by rfl) ⟨69420, by rfl⟩ : syracuseStep 2961941 = 138841) (by norm_num)
theorem B1974627 : Blo 1973435 1974627 := bstep (se 1 (by rfl) ⟨1480970, by rfl⟩ : syracuseStep 1974627 = 2961941) B2961941
theorem B4744469 : Blo 1973435 4744469 := bbase (se 6 (by rfl) ⟨111198, by rfl⟩ : syracuseStep 4744469 = 222397) (by norm_num)
theorem B3162979 : Blo 1973435 3162979 := bstep (se 1 (by rfl) ⟨2372234, by rfl⟩ : syracuseStep 3162979 = 4744469) B4744469
theorem B16869221 : Blo 1973435 16869221 := bstep (se 4 (by rfl) ⟨1581489, by rfl⟩ : syracuseStep 16869221 = 3162979) B3162979
theorem B11246147 : Blo 1973435 11246147 := bstep (se 1 (by rfl) ⟨8434610, by rfl⟩ : syracuseStep 11246147 = 16869221) B16869221
theorem B7497431 : Blo 1973435 7497431 := bstep (se 1 (by rfl) ⟨5623073, by rfl⟩ : syracuseStep 7497431 = 11246147) B11246147
theorem B4998287 : Blo 1973435 4998287 := bstep (se 1 (by rfl) ⟨3748715, by rfl⟩ : syracuseStep 4998287 = 7497431) B7497431
theorem B3332191 : Blo 1973435 3332191 := bstep (se 1 (by rfl) ⟨2499143, by rfl⟩ : syracuseStep 3332191 = 4998287) B4998287
theorem B4442921 : Blo 1973435 4442921 := bstep (se 2 (by rfl) ⟨1666095, by rfl⟩ : syracuseStep 4442921 = 3332191) B3332191
theorem B2961947 : Blo 1973435 2961947 := bstep (se 1 (by rfl) ⟨2221460, by rfl⟩ : syracuseStep 2961947 = 4442921) B4442921
theorem B1974631 : Blo 1973435 1974631 := bstep (se 1 (by rfl) ⟨1480973, by rfl⟩ : syracuseStep 1974631 = 2961947) B2961947
theorem B2221465 : Blo 1973435 2221465 := bbase (se 2 (by rfl) ⟨833049, by rfl⟩ : syracuseStep 2221465 = 1666099) (by norm_num)
theorem B2961953 : Blo 1973435 2961953 := bstep (se 2 (by rfl) ⟨1110732, by rfl⟩ : syracuseStep 2961953 = 2221465) B2221465
theorem B1974635 : Blo 1973435 1974635 := bstep (se 1 (by rfl) ⟨1480976, by rfl⟩ : syracuseStep 1974635 = 2961953) B2961953
theorem B7497461 : Blo 1973435 7497461 := bbase (se 5 (by rfl) ⟨351443, by rfl⟩ : syracuseStep 7497461 = 702887) (by norm_num)
theorem B4998307 : Blo 1973435 4998307 := bstep (se 1 (by rfl) ⟨3748730, by rfl⟩ : syracuseStep 4998307 = 7497461) B7497461
theorem B6664409 : Blo 1973435 6664409 := bstep (se 2 (by rfl) ⟨2499153, by rfl⟩ : syracuseStep 6664409 = 4998307) B4998307
theorem B4442939 : Blo 1973435 4442939 := bstep (se 1 (by rfl) ⟨3332204, by rfl⟩ : syracuseStep 4442939 = 6664409) B6664409
theorem B2961959 : Blo 1973435 2961959 := bstep (se 1 (by rfl) ⟨2221469, by rfl⟩ : syracuseStep 2961959 = 4442939) B4442939
theorem B1974639 : Blo 1973435 1974639 := bstep (se 1 (by rfl) ⟨1480979, by rfl⟩ : syracuseStep 1974639 = 2961959) B2961959
theorem B2961965 : Blo 1973435 2961965 := bbase (se 3 (by rfl) ⟨555368, by rfl⟩ : syracuseStep 2961965 = 1110737) (by norm_num)
theorem B1974643 : Blo 1973435 1974643 := bstep (se 1 (by rfl) ⟨1480982, by rfl⟩ : syracuseStep 1974643 = 2961965) B2961965
theorem B4442957 : Blo 1973435 4442957 := bbase (se 3 (by rfl) ⟨833054, by rfl⟩ : syracuseStep 4442957 = 1666109) (by norm_num)
theorem B2961971 : Blo 1973435 2961971 := bstep (se 1 (by rfl) ⟨2221478, by rfl⟩ : syracuseStep 2961971 = 4442957) B4442957
theorem B1974647 : Blo 1973435 1974647 := bstep (se 1 (by rfl) ⟨1480985, by rfl⟩ : syracuseStep 1974647 = 2961971) B2961971
theorem B2499169 : Blo 1973435 2499169 := bbase (se 2 (by rfl) ⟨937188, by rfl⟩ : syracuseStep 2499169 = 1874377) (by norm_num)
theorem B3332225 : Blo 1973435 3332225 := bstep (se 2 (by rfl) ⟨1249584, by rfl⟩ : syracuseStep 3332225 = 2499169) B2499169
theorem B2221483 : Blo 1973435 2221483 := bstep (se 1 (by rfl) ⟨1666112, by rfl⟩ : syracuseStep 2221483 = 3332225) B3332225
theorem B2961977 : Blo 1973435 2961977 := bstep (se 2 (by rfl) ⟨1110741, by rfl⟩ : syracuseStep 2961977 = 2221483) B2221483
theorem B1974651 : Blo 1973435 1974651 := bstep (se 1 (by rfl) ⟨1480988, by rfl⟩ : syracuseStep 1974651 = 2961977) B2961977
theorem B22492565 : Blo 1973435 22492565 := bbase (se 6 (by rfl) ⟨527169, by rfl⟩ : syracuseStep 22492565 = 1054339) (by norm_num)
theorem B14995043 : Blo 1973435 14995043 := bstep (se 1 (by rfl) ⟨11246282, by rfl⟩ : syracuseStep 14995043 = 22492565) B22492565
theorem B9996695 : Blo 1973435 9996695 := bstep (se 1 (by rfl) ⟨7497521, by rfl⟩ : syracuseStep 9996695 = 14995043) B14995043
theorem B6664463 : Blo 1973435 6664463 := bstep (se 1 (by rfl) ⟨4998347, by rfl⟩ : syracuseStep 6664463 = 9996695) B9996695
theorem B4442975 : Blo 1973435 4442975 := bstep (se 1 (by rfl) ⟨3332231, by rfl⟩ : syracuseStep 4442975 = 6664463) B6664463
theorem B2961983 : Blo 1973435 2961983 := bstep (se 1 (by rfl) ⟨2221487, by rfl⟩ : syracuseStep 2961983 = 4442975) B4442975
theorem B1974655 : Blo 1973435 1974655 := bstep (se 1 (by rfl) ⟨1480991, by rfl⟩ : syracuseStep 1974655 = 2961983) B2961983
theorem B2961989 : Blo 1973435 2961989 := bbase (se 4 (by rfl) ⟨277686, by rfl⟩ : syracuseStep 2961989 = 555373) (by norm_num)
theorem B1974659 : Blo 1973435 1974659 := bstep (se 1 (by rfl) ⟨1480994, by rfl⟩ : syracuseStep 1974659 = 2961989) B2961989
theorem B3332245 : Blo 1973435 3332245 := bbase (se 6 (by rfl) ⟨78099, by rfl⟩ : syracuseStep 3332245 = 156199) (by norm_num)
theorem B4442993 : Blo 1973435 4442993 := bstep (se 2 (by rfl) ⟨1666122, by rfl⟩ : syracuseStep 4442993 = 3332245) B3332245
theorem B2961995 : Blo 1973435 2961995 := bstep (se 1 (by rfl) ⟨2221496, by rfl⟩ : syracuseStep 2961995 = 4442993) B4442993
theorem B1974663 : Blo 1973435 1974663 := bstep (se 1 (by rfl) ⟨1480997, by rfl⟩ : syracuseStep 1974663 = 2961995) B2961995
theorem B2221501 : Blo 1973435 2221501 := bbase (se 3 (by rfl) ⟨416531, by rfl⟩ : syracuseStep 2221501 = 833063) (by norm_num)
theorem B2962001 : Blo 1973435 2962001 := bstep (se 2 (by rfl) ⟨1110750, by rfl⟩ : syracuseStep 2962001 = 2221501) B2221501
theorem B1974667 : Blo 1973435 1974667 := bstep (se 1 (by rfl) ⟨1481000, by rfl⟩ : syracuseStep 1974667 = 2962001) B2962001
theorem B6664517 : Blo 1973435 6664517 := bbase (se 4 (by rfl) ⟨624798, by rfl⟩ : syracuseStep 6664517 = 1249597) (by norm_num)
theorem B4443011 : Blo 1973435 4443011 := bstep (se 1 (by rfl) ⟨3332258, by rfl⟩ : syracuseStep 4443011 = 6664517) B6664517
theorem B2962007 : Blo 1973435 2962007 := bstep (se 1 (by rfl) ⟨2221505, by rfl⟩ : syracuseStep 2962007 = 4443011) B4443011
theorem B1974671 : Blo 1973435 1974671 := bstep (se 1 (by rfl) ⟨1481003, by rfl⟩ : syracuseStep 1974671 = 2962007) B2962007
theorem B2962013 : Blo 1973435 2962013 := bbase (se 3 (by rfl) ⟨555377, by rfl⟩ : syracuseStep 2962013 = 1110755) (by norm_num)
theorem B1974675 : Blo 1973435 1974675 := bstep (se 1 (by rfl) ⟨1481006, by rfl⟩ : syracuseStep 1974675 = 2962013) B2962013
theorem B4443029 : Blo 1973435 4443029 := bbase (se 6 (by rfl) ⟨104133, by rfl⟩ : syracuseStep 4443029 = 208267) (by norm_num)
theorem B2962019 : Blo 1973435 2962019 := bstep (se 1 (by rfl) ⟨2221514, by rfl⟩ : syracuseStep 2962019 = 4443029) B4443029
theorem B1974679 : Blo 1973435 1974679 := bstep (se 1 (by rfl) ⟨1481009, by rfl⟩ : syracuseStep 1974679 = 2962019) B2962019
theorem B4003253 : Blo 1973435 4003253 := bbase (se 5 (by rfl) ⟨187652, by rfl⟩ : syracuseStep 4003253 = 375305) (by norm_num)
theorem B2668835 : Blo 1973435 2668835 := bstep (se 1 (by rfl) ⟨2001626, by rfl⟩ : syracuseStep 2668835 = 4003253) B4003253
theorem B7116893 : Blo 1973435 7116893 := bstep (se 3 (by rfl) ⟨1334417, by rfl⟩ : syracuseStep 7116893 = 2668835) B2668835
theorem B4744595 : Blo 1973435 4744595 := bstep (se 1 (by rfl) ⟨3558446, by rfl⟩ : syracuseStep 4744595 = 7116893) B7116893
theorem B3163063 : Blo 1973435 3163063 := bstep (se 1 (by rfl) ⟨2372297, by rfl⟩ : syracuseStep 3163063 = 4744595) B4744595
theorem B4217417 : Blo 1973435 4217417 := bstep (se 2 (by rfl) ⟨1581531, by rfl⟩ : syracuseStep 4217417 = 3163063) B3163063
theorem B2811611 : Blo 1973435 2811611 := bstep (se 1 (by rfl) ⟨2108708, by rfl⟩ : syracuseStep 2811611 = 4217417) B4217417
theorem B7497629 : Blo 1973435 7497629 := bstep (se 3 (by rfl) ⟨1405805, by rfl⟩ : syracuseStep 7497629 = 2811611) B2811611
theorem B4998419 : Blo 1973435 4998419 := bstep (se 1 (by rfl) ⟨3748814, by rfl⟩ : syracuseStep 4998419 = 7497629) B7497629
theorem B3332279 : Blo 1973435 3332279 := bstep (se 1 (by rfl) ⟨2499209, by rfl⟩ : syracuseStep 3332279 = 4998419) B4998419
theorem B2221519 : Blo 1973435 2221519 := bstep (se 1 (by rfl) ⟨1666139, by rfl⟩ : syracuseStep 2221519 = 3332279) B3332279
theorem B2962025 : Blo 1973435 2962025 := bstep (se 2 (by rfl) ⟨1110759, by rfl⟩ : syracuseStep 2962025 = 2221519) B2221519
theorem B1974683 : Blo 1973435 1974683 := bstep (se 1 (by rfl) ⟨1481012, by rfl⟩ : syracuseStep 1974683 = 2962025) B2962025
theorem B2533313 : Blo 1973435 2533313 := bbase (se 2 (by rfl) ⟨949992, by rfl⟩ : syracuseStep 2533313 = 1899985) (by norm_num)
theorem B6755501 : Blo 1973435 6755501 := bstep (se 3 (by rfl) ⟨1266656, by rfl⟩ : syracuseStep 6755501 = 2533313) B2533313
theorem B18014669 : Blo 1973435 18014669 := bstep (se 3 (by rfl) ⟨3377750, by rfl⟩ : syracuseStep 18014669 = 6755501) B6755501
theorem B12009779 : Blo 1973435 12009779 := bstep (se 1 (by rfl) ⟨9007334, by rfl⟩ : syracuseStep 12009779 = 18014669) B18014669
theorem B8006519 : Blo 1973435 8006519 := bstep (se 1 (by rfl) ⟨6004889, by rfl⟩ : syracuseStep 8006519 = 12009779) B12009779
theorem B5337679 : Blo 1973435 5337679 := bstep (se 1 (by rfl) ⟨4003259, by rfl⟩ : syracuseStep 5337679 = 8006519) B8006519
theorem B7116905 : Blo 1973435 7116905 := bstep (se 2 (by rfl) ⟨2668839, by rfl⟩ : syracuseStep 7116905 = 5337679) B5337679
theorem B4744603 : Blo 1973435 4744603 := bstep (se 1 (by rfl) ⟨3558452, by rfl⟩ : syracuseStep 4744603 = 7116905) B7116905
theorem B6326137 : Blo 1973435 6326137 := bstep (se 2 (by rfl) ⟨2372301, by rfl⟩ : syracuseStep 6326137 = 4744603) B4744603
theorem B8434849 : Blo 1973435 8434849 := bstep (se 2 (by rfl) ⟨3163068, by rfl⟩ : syracuseStep 8434849 = 6326137) B6326137
theorem B11246465 : Blo 1973435 11246465 := bstep (se 2 (by rfl) ⟨4217424, by rfl⟩ : syracuseStep 11246465 = 8434849) B8434849
theorem B7497643 : Blo 1973435 7497643 := bstep (se 1 (by rfl) ⟨5623232, by rfl⟩ : syracuseStep 7497643 = 11246465) B11246465
theorem B9996857 : Blo 1973435 9996857 := bstep (se 2 (by rfl) ⟨3748821, by rfl⟩ : syracuseStep 9996857 = 7497643) B7497643
theorem B6664571 : Blo 1973435 6664571 := bstep (se 1 (by rfl) ⟨4998428, by rfl⟩ : syracuseStep 6664571 = 9996857) B9996857
theorem B4443047 : Blo 1973435 4443047 := bstep (se 1 (by rfl) ⟨3332285, by rfl⟩ : syracuseStep 4443047 = 6664571) B6664571
theorem B2962031 : Blo 1973435 2962031 := bstep (se 1 (by rfl) ⟨2221523, by rfl⟩ : syracuseStep 2962031 = 4443047) B4443047
theorem B1974687 : Blo 1973435 1974687 := bstep (se 1 (by rfl) ⟨1481015, by rfl⟩ : syracuseStep 1974687 = 2962031) B2962031
theorem B2962037 : Blo 1973435 2962037 := bbase (se 5 (by rfl) ⟨138845, by rfl⟩ : syracuseStep 2962037 = 277691) (by norm_num)
theorem B1974691 : Blo 1973435 1974691 := bstep (se 1 (by rfl) ⟨1481018, by rfl⟩ : syracuseStep 1974691 = 2962037) B2962037
theorem B3748837 : Blo 1973435 3748837 := bbase (se 4 (by rfl) ⟨351453, by rfl⟩ : syracuseStep 3748837 = 702907) (by norm_num)
theorem B4998449 : Blo 1973435 4998449 := bstep (se 2 (by rfl) ⟨1874418, by rfl⟩ : syracuseStep 4998449 = 3748837) B3748837
theorem B3332299 : Blo 1973435 3332299 := bstep (se 1 (by rfl) ⟨2499224, by rfl⟩ : syracuseStep 3332299 = 4998449) B4998449
theorem B4443065 : Blo 1973435 4443065 := bstep (se 2 (by rfl) ⟨1666149, by rfl⟩ : syracuseStep 4443065 = 3332299) B3332299
theorem B2962043 : Blo 1973435 2962043 := bstep (se 1 (by rfl) ⟨2221532, by rfl⟩ : syracuseStep 2962043 = 4443065) B4443065
theorem B1974695 : Blo 1973435 1974695 := bstep (se 1 (by rfl) ⟨1481021, by rfl⟩ : syracuseStep 1974695 = 2962043) B2962043
theorem B2221537 : Blo 1973435 2221537 := bbase (se 2 (by rfl) ⟨833076, by rfl⟩ : syracuseStep 2221537 = 1666153) (by norm_num)
theorem B2962049 : Blo 1973435 2962049 := bstep (se 2 (by rfl) ⟨1110768, by rfl⟩ : syracuseStep 2962049 = 2221537) B2221537
theorem B1974699 : Blo 1973435 1974699 := bstep (se 1 (by rfl) ⟨1481024, by rfl⟩ : syracuseStep 1974699 = 2962049) B2962049
theorem B4998469 : Blo 1973435 4998469 := bbase (se 4 (by rfl) ⟨468606, by rfl⟩ : syracuseStep 4998469 = 937213) (by norm_num)
theorem B6664625 : Blo 1973435 6664625 := bstep (se 2 (by rfl) ⟨2499234, by rfl⟩ : syracuseStep 6664625 = 4998469) B4998469
theorem B4443083 : Blo 1973435 4443083 := bstep (se 1 (by rfl) ⟨3332312, by rfl⟩ : syracuseStep 4443083 = 6664625) B6664625
theorem B2962055 : Blo 1973435 2962055 := bstep (se 1 (by rfl) ⟨2221541, by rfl⟩ : syracuseStep 2962055 = 4443083) B4443083
theorem B1974703 : Blo 1973435 1974703 := bstep (se 1 (by rfl) ⟨1481027, by rfl⟩ : syracuseStep 1974703 = 2962055) B2962055
theorem B2962061 : Blo 1973435 2962061 := bbase (se 3 (by rfl) ⟨555386, by rfl⟩ : syracuseStep 2962061 = 1110773) (by norm_num)
theorem B1974707 : Blo 1973435 1974707 := bstep (se 1 (by rfl) ⟨1481030, by rfl⟩ : syracuseStep 1974707 = 2962061) B2962061
theorem B4443101 : Blo 1973435 4443101 := bbase (se 3 (by rfl) ⟨833081, by rfl⟩ : syracuseStep 4443101 = 1666163) (by norm_num)
theorem B2962067 : Blo 1973435 2962067 := bstep (se 1 (by rfl) ⟨2221550, by rfl⟩ : syracuseStep 2962067 = 4443101) B4443101
theorem B1974711 : Blo 1973435 1974711 := bstep (se 1 (by rfl) ⟨1481033, by rfl⟩ : syracuseStep 1974711 = 2962067) B2962067
theorem B3332333 : Blo 1973435 3332333 := bbase (se 3 (by rfl) ⟨624812, by rfl⟩ : syracuseStep 3332333 = 1249625) (by norm_num)
theorem B2221555 : Blo 1973435 2221555 := bstep (se 1 (by rfl) ⟨1666166, by rfl⟩ : syracuseStep 2221555 = 3332333) B3332333
theorem B2962073 : Blo 1973435 2962073 := bstep (se 2 (by rfl) ⟨1110777, by rfl⟩ : syracuseStep 2962073 = 2221555) B2221555
theorem B1974715 : Blo 1973435 1974715 := bstep (se 1 (by rfl) ⟨1481036, by rfl⟩ : syracuseStep 1974715 = 2962073) B2962073
theorem B6086917 : Blo 1973435 6086917 := bbase (se 4 (by rfl) ⟨570648, by rfl⟩ : syracuseStep 6086917 = 1141297) (by norm_num)
theorem B8115889 : Blo 1973435 8115889 := bstep (se 2 (by rfl) ⟨3043458, by rfl⟩ : syracuseStep 8115889 = 6086917) B6086917
theorem B10821185 : Blo 1973435 10821185 := bstep (se 2 (by rfl) ⟨4057944, by rfl⟩ : syracuseStep 10821185 = 8115889) B8115889
theorem B7214123 : Blo 1973435 7214123 := bstep (se 1 (by rfl) ⟨5410592, by rfl⟩ : syracuseStep 7214123 = 10821185) B10821185
theorem B4809415 : Blo 1973435 4809415 := bstep (se 1 (by rfl) ⟨3607061, by rfl⟩ : syracuseStep 4809415 = 7214123) B7214123
theorem B6412553 : Blo 1973435 6412553 := bstep (se 2 (by rfl) ⟨2404707, by rfl⟩ : syracuseStep 6412553 = 4809415) B4809415
theorem B4275035 : Blo 1973435 4275035 := bstep (se 1 (by rfl) ⟨3206276, by rfl⟩ : syracuseStep 4275035 = 6412553) B6412553
theorem B2850023 : Blo 1973435 2850023 := bstep (se 1 (by rfl) ⟨2137517, by rfl⟩ : syracuseStep 2850023 = 4275035) B4275035
theorem B7600061 : Blo 1973435 7600061 := bstep (se 3 (by rfl) ⟨1425011, by rfl⟩ : syracuseStep 7600061 = 2850023) B2850023
theorem B5066707 : Blo 1973435 5066707 := bstep (se 1 (by rfl) ⟨3800030, by rfl⟩ : syracuseStep 5066707 = 7600061) B7600061
theorem B6755609 : Blo 1973435 6755609 := bstep (se 2 (by rfl) ⟨2533353, by rfl⟩ : syracuseStep 6755609 = 5066707) B5066707
theorem B18014957 : Blo 1973435 18014957 := bstep (se 3 (by rfl) ⟨3377804, by rfl⟩ : syracuseStep 18014957 = 6755609) B6755609
theorem B12009971 : Blo 1973435 12009971 := bstep (se 1 (by rfl) ⟨9007478, by rfl⟩ : syracuseStep 12009971 = 18014957) B18014957
theorem B32026589 : Blo 1973435 32026589 := bstep (se 3 (by rfl) ⟨6004985, by rfl⟩ : syracuseStep 32026589 = 12009971) B12009971
theorem B21351059 : Blo 1973435 21351059 := bstep (se 1 (by rfl) ⟨16013294, by rfl⟩ : syracuseStep 21351059 = 32026589) B32026589
theorem B14234039 : Blo 1973435 14234039 := bstep (se 1 (by rfl) ⟨10675529, by rfl⟩ : syracuseStep 14234039 = 21351059) B21351059
theorem B9489359 : Blo 1973435 9489359 := bstep (se 1 (by rfl) ⟨7117019, by rfl⟩ : syracuseStep 9489359 = 14234039) B14234039
theorem B25304957 : Blo 1973435 25304957 := bstep (se 3 (by rfl) ⟨4744679, by rfl⟩ : syracuseStep 25304957 = 9489359) B9489359
theorem B16869971 : Blo 1973435 16869971 := bstep (se 1 (by rfl) ⟨12652478, by rfl⟩ : syracuseStep 16869971 = 25304957) B25304957
theorem B11246647 : Blo 1973435 11246647 := bstep (se 1 (by rfl) ⟨8434985, by rfl⟩ : syracuseStep 11246647 = 16869971) B16869971
theorem B14995529 : Blo 1973435 14995529 := bstep (se 2 (by rfl) ⟨5623323, by rfl⟩ : syracuseStep 14995529 = 11246647) B11246647
theorem B9997019 : Blo 1973435 9997019 := bstep (se 1 (by rfl) ⟨7497764, by rfl⟩ : syracuseStep 9997019 = 14995529) B14995529
theorem B6664679 : Blo 1973435 6664679 := bstep (se 1 (by rfl) ⟨4998509, by rfl⟩ : syracuseStep 6664679 = 9997019) B9997019
theorem B4443119 : Blo 1973435 4443119 := bstep (se 1 (by rfl) ⟨3332339, by rfl⟩ : syracuseStep 4443119 = 6664679) B6664679
theorem B2962079 : Blo 1973435 2962079 := bstep (se 1 (by rfl) ⟨2221559, by rfl⟩ : syracuseStep 2962079 = 4443119) B4443119
theorem B1974719 : Blo 1973435 1974719 := bstep (se 1 (by rfl) ⟨1481039, by rfl⟩ : syracuseStep 1974719 = 2962079) B2962079
theorem B2962085 : Blo 1973435 2962085 := bbase (se 4 (by rfl) ⟨277695, by rfl⟩ : syracuseStep 2962085 = 555391) (by norm_num)
theorem B1974723 : Blo 1973435 1974723 := bstep (se 1 (by rfl) ⟨1481042, by rfl⟩ : syracuseStep 1974723 = 2962085) B2962085
theorem B2499265 : Blo 1973435 2499265 := bbase (se 2 (by rfl) ⟨937224, by rfl⟩ : syracuseStep 2499265 = 1874449) (by norm_num)
theorem B3332353 : Blo 1973435 3332353 := bstep (se 2 (by rfl) ⟨1249632, by rfl⟩ : syracuseStep 3332353 = 2499265) B2499265
theorem B4443137 : Blo 1973435 4443137 := bstep (se 2 (by rfl) ⟨1666176, by rfl⟩ : syracuseStep 4443137 = 3332353) B3332353
theorem B2962091 : Blo 1973435 2962091 := bstep (se 1 (by rfl) ⟨2221568, by rfl⟩ : syracuseStep 2962091 = 4443137) B4443137
theorem B1974727 : Blo 1973435 1974727 := bstep (se 1 (by rfl) ⟨1481045, by rfl⟩ : syracuseStep 1974727 = 2962091) B2962091
theorem B2221573 : Blo 1973435 2221573 := bbase (se 4 (by rfl) ⟨208272, by rfl⟩ : syracuseStep 2221573 = 416545) (by norm_num)
theorem B2962097 : Blo 1973435 2962097 := bstep (se 2 (by rfl) ⟨1110786, by rfl⟩ : syracuseStep 2962097 = 2221573) B2221573
theorem B1974731 : Blo 1973435 1974731 := bstep (se 1 (by rfl) ⟨1481048, by rfl⟩ : syracuseStep 1974731 = 2962097) B2962097
theorem B2811685 : Blo 1973435 2811685 := bbase (se 4 (by rfl) ⟨263595, by rfl⟩ : syracuseStep 2811685 = 527191) (by norm_num)
theorem B3748913 : Blo 1973435 3748913 := bstep (se 2 (by rfl) ⟨1405842, by rfl⟩ : syracuseStep 3748913 = 2811685) B2811685
theorem B2499275 : Blo 1973435 2499275 := bstep (se 1 (by rfl) ⟨1874456, by rfl⟩ : syracuseStep 2499275 = 3748913) B3748913
theorem B6664733 : Blo 1973435 6664733 := bstep (se 3 (by rfl) ⟨1249637, by rfl⟩ : syracuseStep 6664733 = 2499275) B2499275
theorem B4443155 : Blo 1973435 4443155 := bstep (se 1 (by rfl) ⟨3332366, by rfl⟩ : syracuseStep 4443155 = 6664733) B6664733
theorem B2962103 : Blo 1973435 2962103 := bstep (se 1 (by rfl) ⟨2221577, by rfl⟩ : syracuseStep 2962103 = 4443155) B4443155
theorem B1974735 : Blo 1973435 1974735 := bstep (se 1 (by rfl) ⟨1481051, by rfl⟩ : syracuseStep 1974735 = 2962103) B2962103
theorem B2962109 : Blo 1973435 2962109 := bbase (se 3 (by rfl) ⟨555395, by rfl⟩ : syracuseStep 2962109 = 1110791) (by norm_num)
theorem B1974739 : Blo 1973435 1974739 := bstep (se 1 (by rfl) ⟨1481054, by rfl⟩ : syracuseStep 1974739 = 2962109) B2962109
theorem B4443173 : Blo 1973435 4443173 := bbase (se 4 (by rfl) ⟨416547, by rfl⟩ : syracuseStep 4443173 = 833095) (by norm_num)
theorem B2962115 : Blo 1973435 2962115 := bstep (se 1 (by rfl) ⟨2221586, by rfl⟩ : syracuseStep 2962115 = 4443173) B4443173
theorem B1974743 : Blo 1973435 1974743 := bstep (se 1 (by rfl) ⟨1481057, by rfl⟩ : syracuseStep 1974743 = 2962115) B2962115
theorem B4998581 : Blo 1973435 4998581 := bbase (se 5 (by rfl) ⟨234308, by rfl⟩ : syracuseStep 4998581 = 468617) (by norm_num)
theorem B3332387 : Blo 1973435 3332387 := bstep (se 1 (by rfl) ⟨2499290, by rfl⟩ : syracuseStep 3332387 = 4998581) B4998581
theorem B2221591 : Blo 1973435 2221591 := bstep (se 1 (by rfl) ⟨1666193, by rfl⟩ : syracuseStep 2221591 = 3332387) B3332387
theorem B2962121 : Blo 1973435 2962121 := bstep (se 2 (by rfl) ⟨1110795, by rfl⟩ : syracuseStep 2962121 = 2221591) B2221591
theorem B1974747 : Blo 1973435 1974747 := bstep (se 1 (by rfl) ⟨1481060, by rfl⟩ : syracuseStep 1974747 = 2962121) B2962121
theorem B4744757 : Blo 1973435 4744757 := bbase (se 5 (by rfl) ⟨222410, by rfl⟩ : syracuseStep 4744757 = 444821) (by norm_num)
theorem B12652685 : Blo 1973435 12652685 := bstep (se 3 (by rfl) ⟨2372378, by rfl⟩ : syracuseStep 12652685 = 4744757) B4744757
theorem B8435123 : Blo 1973435 8435123 := bstep (se 1 (by rfl) ⟨6326342, by rfl⟩ : syracuseStep 8435123 = 12652685) B12652685
theorem B5623415 : Blo 1973435 5623415 := bstep (se 1 (by rfl) ⟨4217561, by rfl⟩ : syracuseStep 5623415 = 8435123) B8435123
theorem B3748943 : Blo 1973435 3748943 := bstep (se 1 (by rfl) ⟨2811707, by rfl⟩ : syracuseStep 3748943 = 5623415) B5623415
theorem B9997181 : Blo 1973435 9997181 := bstep (se 3 (by rfl) ⟨1874471, by rfl⟩ : syracuseStep 9997181 = 3748943) B3748943
theorem B6664787 : Blo 1973435 6664787 := bstep (se 1 (by rfl) ⟨4998590, by rfl⟩ : syracuseStep 6664787 = 9997181) B9997181
theorem B4443191 : Blo 1973435 4443191 := bstep (se 1 (by rfl) ⟨3332393, by rfl⟩ : syracuseStep 4443191 = 6664787) B6664787
theorem B2962127 : Blo 1973435 2962127 := bstep (se 1 (by rfl) ⟨2221595, by rfl⟩ : syracuseStep 2962127 = 4443191) B4443191
theorem B1974751 : Blo 1973435 1974751 := bstep (se 1 (by rfl) ⟨1481063, by rfl⟩ : syracuseStep 1974751 = 2962127) B2962127
theorem B2962133 : Blo 1973435 2962133 := bbase (se 7 (by rfl) ⟨34712, by rfl⟩ : syracuseStep 2962133 = 69425) (by norm_num)
theorem B1974755 : Blo 1973435 1974755 := bstep (se 1 (by rfl) ⟨1481066, by rfl⟩ : syracuseStep 1974755 = 2962133) B2962133
theorem B5066813 : Blo 1973435 5066813 := bbase (se 3 (by rfl) ⟨950027, by rfl⟩ : syracuseStep 5066813 = 1900055) (by norm_num)
theorem B3377875 : Blo 1973435 3377875 := bstep (se 1 (by rfl) ⟨2533406, by rfl⟩ : syracuseStep 3377875 = 5066813) B5066813
theorem B4503833 : Blo 1973435 4503833 := bstep (se 2 (by rfl) ⟨1688937, by rfl⟩ : syracuseStep 4503833 = 3377875) B3377875
theorem B3002555 : Blo 1973435 3002555 := bstep (se 1 (by rfl) ⟨2251916, by rfl⟩ : syracuseStep 3002555 = 4503833) B4503833
theorem B8006813 : Blo 1973435 8006813 := bstep (se 3 (by rfl) ⟨1501277, by rfl⟩ : syracuseStep 8006813 = 3002555) B3002555
theorem B5337875 : Blo 1973435 5337875 := bstep (se 1 (by rfl) ⟨4003406, by rfl⟩ : syracuseStep 5337875 = 8006813) B8006813
theorem B3558583 : Blo 1973435 3558583 := bstep (se 1 (by rfl) ⟨2668937, by rfl⟩ : syracuseStep 3558583 = 5337875) B5337875
theorem B4744777 : Blo 1973435 4744777 := bstep (se 2 (by rfl) ⟨1779291, by rfl⟩ : syracuseStep 4744777 = 3558583) B3558583
theorem B6326369 : Blo 1973435 6326369 := bstep (se 2 (by rfl) ⟨2372388, by rfl⟩ : syracuseStep 6326369 = 4744777) B4744777
theorem B4217579 : Blo 1973435 4217579 := bstep (se 1 (by rfl) ⟨3163184, by rfl⟩ : syracuseStep 4217579 = 6326369) B6326369
theorem B2811719 : Blo 1973435 2811719 := bstep (se 1 (by rfl) ⟨2108789, by rfl⟩ : syracuseStep 2811719 = 4217579) B4217579
theorem B7497917 : Blo 1973435 7497917 := bstep (se 3 (by rfl) ⟨1405859, by rfl⟩ : syracuseStep 7497917 = 2811719) B2811719
theorem B4998611 : Blo 1973435 4998611 := bstep (se 1 (by rfl) ⟨3748958, by rfl⟩ : syracuseStep 4998611 = 7497917) B7497917
theorem B3332407 : Blo 1973435 3332407 := bstep (se 1 (by rfl) ⟨2499305, by rfl⟩ : syracuseStep 3332407 = 4998611) B4998611
theorem B4443209 : Blo 1973435 4443209 := bstep (se 2 (by rfl) ⟨1666203, by rfl⟩ : syracuseStep 4443209 = 3332407) B3332407
theorem B2962139 : Blo 1973435 2962139 := bstep (se 1 (by rfl) ⟨2221604, by rfl⟩ : syracuseStep 2962139 = 4443209) B4443209
theorem B1974759 : Blo 1973435 1974759 := bstep (se 1 (by rfl) ⟨1481069, by rfl⟩ : syracuseStep 1974759 = 2962139) B2962139
theorem B2221609 : Blo 1973435 2221609 := bbase (se 2 (by rfl) ⟨833103, by rfl⟩ : syracuseStep 2221609 = 1666207) (by norm_num)
theorem B2962145 : Blo 1973435 2962145 := bstep (se 2 (by rfl) ⟨1110804, by rfl⟩ : syracuseStep 2962145 = 2221609) B2221609
theorem B1974763 : Blo 1973435 1974763 := bstep (se 1 (by rfl) ⟨1481072, by rfl⟩ : syracuseStep 1974763 = 2962145) B2962145
theorem B6412709 : Blo 1973435 6412709 := bbase (se 4 (by rfl) ⟨601191, by rfl⟩ : syracuseStep 6412709 = 1202383) (by norm_num)
theorem B17100557 : Blo 1973435 17100557 := bstep (se 3 (by rfl) ⟨3206354, by rfl⟩ : syracuseStep 17100557 = 6412709) B6412709
theorem B11400371 : Blo 1973435 11400371 := bstep (se 1 (by rfl) ⟨8550278, by rfl⟩ : syracuseStep 11400371 = 17100557) B17100557
theorem B7600247 : Blo 1973435 7600247 := bstep (se 1 (by rfl) ⟨5700185, by rfl⟩ : syracuseStep 7600247 = 11400371) B11400371
theorem B5066831 : Blo 1973435 5066831 := bstep (se 1 (by rfl) ⟨3800123, by rfl⟩ : syracuseStep 5066831 = 7600247) B7600247
theorem B13511549 : Blo 1973435 13511549 := bstep (se 3 (by rfl) ⟨2533415, by rfl⟩ : syracuseStep 13511549 = 5066831) B5066831
theorem B9007699 : Blo 1973435 9007699 := bstep (se 1 (by rfl) ⟨6755774, by rfl⟩ : syracuseStep 9007699 = 13511549) B13511549
theorem B12010265 : Blo 1973435 12010265 := bstep (se 2 (by rfl) ⟨4503849, by rfl⟩ : syracuseStep 12010265 = 9007699) B9007699
theorem B8006843 : Blo 1973435 8006843 := bstep (se 1 (by rfl) ⟨6005132, by rfl⟩ : syracuseStep 8006843 = 12010265) B12010265
theorem B5337895 : Blo 1973435 5337895 := bstep (se 1 (by rfl) ⟨4003421, by rfl⟩ : syracuseStep 5337895 = 8006843) B8006843
theorem B7117193 : Blo 1973435 7117193 := bstep (se 2 (by rfl) ⟨2668947, by rfl⟩ : syracuseStep 7117193 = 5337895) B5337895
theorem B18979181 : Blo 1973435 18979181 := bstep (se 3 (by rfl) ⟨3558596, by rfl⟩ : syracuseStep 18979181 = 7117193) B7117193
theorem B12652787 : Blo 1973435 12652787 := bstep (se 1 (by rfl) ⟨9489590, by rfl⟩ : syracuseStep 12652787 = 18979181) B18979181
theorem B8435191 : Blo 1973435 8435191 := bstep (se 1 (by rfl) ⟨6326393, by rfl⟩ : syracuseStep 8435191 = 12652787) B12652787
theorem B11246921 : Blo 1973435 11246921 := bstep (se 2 (by rfl) ⟨4217595, by rfl⟩ : syracuseStep 11246921 = 8435191) B8435191
theorem B7497947 : Blo 1973435 7497947 := bstep (se 1 (by rfl) ⟨5623460, by rfl⟩ : syracuseStep 7497947 = 11246921) B11246921
theorem B4998631 : Blo 1973435 4998631 := bstep (se 1 (by rfl) ⟨3748973, by rfl⟩ : syracuseStep 4998631 = 7497947) B7497947
theorem B6664841 : Blo 1973435 6664841 := bstep (se 2 (by rfl) ⟨2499315, by rfl⟩ : syracuseStep 6664841 = 4998631) B4998631
theorem B4443227 : Blo 1973435 4443227 := bstep (se 1 (by rfl) ⟨3332420, by rfl⟩ : syracuseStep 4443227 = 6664841) B6664841
theorem B2962151 : Blo 1973435 2962151 := bstep (se 1 (by rfl) ⟨2221613, by rfl⟩ : syracuseStep 2962151 = 4443227) B4443227
theorem B1974767 : Blo 1973435 1974767 := bstep (se 1 (by rfl) ⟨1481075, by rfl⟩ : syracuseStep 1974767 = 2962151) B2962151
theorem B2962157 : Blo 1973435 2962157 := bbase (se 3 (by rfl) ⟨555404, by rfl⟩ : syracuseStep 2962157 = 1110809) (by norm_num)
theorem B1974771 : Blo 1973435 1974771 := bstep (se 1 (by rfl) ⟨1481078, by rfl⟩ : syracuseStep 1974771 = 2962157) B2962157
theorem B4443245 : Blo 1973435 4443245 := bbase (se 3 (by rfl) ⟨833108, by rfl⟩ : syracuseStep 4443245 = 1666217) (by norm_num)
theorem B2962163 : Blo 1973435 2962163 := bstep (se 1 (by rfl) ⟨2221622, by rfl⟩ : syracuseStep 2962163 = 4443245) B4443245
theorem B1974775 : Blo 1973435 1974775 := bstep (se 1 (by rfl) ⟨1481081, by rfl⟩ : syracuseStep 1974775 = 2962163) B2962163
theorem B3748997 : Blo 1973435 3748997 := bbase (se 4 (by rfl) ⟨351468, by rfl⟩ : syracuseStep 3748997 = 702937) (by norm_num)
theorem B2499331 : Blo 1973435 2499331 := bstep (se 1 (by rfl) ⟨1874498, by rfl⟩ : syracuseStep 2499331 = 3748997) B3748997
theorem B3332441 : Blo 1973435 3332441 := bstep (se 2 (by rfl) ⟨1249665, by rfl⟩ : syracuseStep 3332441 = 2499331) B2499331
theorem B2221627 : Blo 1973435 2221627 := bstep (se 1 (by rfl) ⟨1666220, by rfl⟩ : syracuseStep 2221627 = 3332441) B3332441
theorem B2962169 : Blo 1973435 2962169 := bstep (se 2 (by rfl) ⟨1110813, by rfl⟩ : syracuseStep 2962169 = 2221627) B2221627
theorem B1974779 : Blo 1973435 1974779 := bstep (se 1 (by rfl) ⟨1481084, by rfl⟩ : syracuseStep 1974779 = 2962169) B2962169
theorem B4275173 : Blo 1973435 4275173 := bbase (se 4 (by rfl) ⟨400797, by rfl⟩ : syracuseStep 4275173 = 801595) (by norm_num)
theorem B2850115 : Blo 1973435 2850115 := bstep (se 1 (by rfl) ⟨2137586, by rfl⟩ : syracuseStep 2850115 = 4275173) B4275173
theorem B3800153 : Blo 1973435 3800153 := bstep (se 2 (by rfl) ⟨1425057, by rfl⟩ : syracuseStep 3800153 = 2850115) B2850115
theorem B10133741 : Blo 1973435 10133741 := bstep (se 3 (by rfl) ⟨1900076, by rfl⟩ : syracuseStep 10133741 = 3800153) B3800153
theorem B27023309 : Blo 1973435 27023309 := bstep (se 3 (by rfl) ⟨5066870, by rfl⟩ : syracuseStep 27023309 = 10133741) B10133741
theorem B18015539 : Blo 1973435 18015539 := bstep (se 1 (by rfl) ⟨13511654, by rfl⟩ : syracuseStep 18015539 = 27023309) B27023309
theorem B48041437 : Blo 1973435 48041437 := bstep (se 3 (by rfl) ⟨9007769, by rfl⟩ : syracuseStep 48041437 = 18015539) B18015539
theorem B64055249 : Blo 1973435 64055249 := bstep (se 2 (by rfl) ⟨24020718, by rfl⟩ : syracuseStep 64055249 = 48041437) B48041437
theorem B42703499 : Blo 1973435 42703499 := bstep (se 1 (by rfl) ⟨32027624, by rfl⟩ : syracuseStep 42703499 = 64055249) B64055249
theorem B28468999 : Blo 1973435 28468999 := bstep (se 1 (by rfl) ⟨21351749, by rfl⟩ : syracuseStep 28468999 = 42703499) B42703499
theorem B37958665 : Blo 1973435 37958665 := bstep (se 2 (by rfl) ⟨14234499, by rfl⟩ : syracuseStep 37958665 = 28468999) B28468999
theorem B50611553 : Blo 1973435 50611553 := bstep (se 2 (by rfl) ⟨18979332, by rfl⟩ : syracuseStep 50611553 = 37958665) B37958665
theorem B33741035 : Blo 1973435 33741035 := bstep (se 1 (by rfl) ⟨25305776, by rfl⟩ : syracuseStep 33741035 = 50611553) B50611553
theorem B22494023 : Blo 1973435 22494023 := bstep (se 1 (by rfl) ⟨16870517, by rfl⟩ : syracuseStep 22494023 = 33741035) B33741035
theorem B14996015 : Blo 1973435 14996015 := bstep (se 1 (by rfl) ⟨11247011, by rfl⟩ : syracuseStep 14996015 = 22494023) B22494023
theorem B9997343 : Blo 1973435 9997343 := bstep (se 1 (by rfl) ⟨7498007, by rfl⟩ : syracuseStep 9997343 = 14996015) B14996015
theorem B6664895 : Blo 1973435 6664895 := bstep (se 1 (by rfl) ⟨4998671, by rfl⟩ : syracuseStep 6664895 = 9997343) B9997343
theorem B4443263 : Blo 1973435 4443263 := bstep (se 1 (by rfl) ⟨3332447, by rfl⟩ : syracuseStep 4443263 = 6664895) B6664895
theorem B2962175 : Blo 1973435 2962175 := bstep (se 1 (by rfl) ⟨2221631, by rfl⟩ : syracuseStep 2962175 = 4443263) B4443263
theorem B1974783 : Blo 1973435 1974783 := bstep (se 1 (by rfl) ⟨1481087, by rfl⟩ : syracuseStep 1974783 = 2962175) B2962175
theorem B2962181 : Blo 1973435 2962181 := bbase (se 4 (by rfl) ⟨277704, by rfl⟩ : syracuseStep 2962181 = 555409) (by norm_num)
theorem B1974787 : Blo 1973435 1974787 := bstep (se 1 (by rfl) ⟨1481090, by rfl⟩ : syracuseStep 1974787 = 2962181) B2962181
theorem B3332461 : Blo 1973435 3332461 := bbase (se 3 (by rfl) ⟨624836, by rfl⟩ : syracuseStep 3332461 = 1249673) (by norm_num)
theorem B4443281 : Blo 1973435 4443281 := bstep (se 2 (by rfl) ⟨1666230, by rfl⟩ : syracuseStep 4443281 = 3332461) B3332461
theorem B2962187 : Blo 1973435 2962187 := bstep (se 1 (by rfl) ⟨2221640, by rfl⟩ : syracuseStep 2962187 = 4443281) B4443281
theorem B1974791 : Blo 1973435 1974791 := bstep (se 1 (by rfl) ⟨1481093, by rfl⟩ : syracuseStep 1974791 = 2962187) B2962187
theorem B2221645 : Blo 1973435 2221645 := bbase (se 3 (by rfl) ⟨416558, by rfl⟩ : syracuseStep 2221645 = 833117) (by norm_num)
theorem B2962193 : Blo 1973435 2962193 := bstep (se 2 (by rfl) ⟨1110822, by rfl⟩ : syracuseStep 2962193 = 2221645) B2221645
theorem B1974795 : Blo 1973435 1974795 := bstep (se 1 (by rfl) ⟨1481096, by rfl⟩ : syracuseStep 1974795 = 2962193) B2962193
theorem B6664949 : Blo 1973435 6664949 := bbase (se 5 (by rfl) ⟨312419, by rfl⟩ : syracuseStep 6664949 = 624839) (by norm_num)
theorem B4443299 : Blo 1973435 4443299 := bstep (se 1 (by rfl) ⟨3332474, by rfl⟩ : syracuseStep 4443299 = 6664949) B6664949
theorem B2962199 : Blo 1973435 2962199 := bstep (se 1 (by rfl) ⟨2221649, by rfl⟩ : syracuseStep 2962199 = 4443299) B4443299
theorem B1974799 : Blo 1973435 1974799 := bstep (se 1 (by rfl) ⟨1481099, by rfl⟩ : syracuseStep 1974799 = 2962199) B2962199
theorem B2962205 : Blo 1973435 2962205 := bbase (se 3 (by rfl) ⟨555413, by rfl⟩ : syracuseStep 2962205 = 1110827) (by norm_num)
theorem B1974803 : Blo 1973435 1974803 := bstep (se 1 (by rfl) ⟨1481102, by rfl⟩ : syracuseStep 1974803 = 2962205) B2962205
theorem B4443317 : Blo 1973435 4443317 := bbase (se 5 (by rfl) ⟨208280, by rfl⟩ : syracuseStep 4443317 = 416561) (by norm_num)
theorem B2962211 : Blo 1973435 2962211 := bstep (se 1 (by rfl) ⟨2221658, by rfl⟩ : syracuseStep 2962211 = 4443317) B4443317
theorem B1974807 : Blo 1973435 1974807 := bstep (se 1 (by rfl) ⟨1481105, by rfl⟩ : syracuseStep 1974807 = 2962211) B2962211
theorem B2108845 : Blo 1973435 2108845 := bbase (se 3 (by rfl) ⟨395408, by rfl⟩ : syracuseStep 2108845 = 790817) (by norm_num)
theorem B11247173 : Blo 1973435 11247173 := bstep (se 4 (by rfl) ⟨1054422, by rfl⟩ : syracuseStep 11247173 = 2108845) B2108845
theorem B7498115 : Blo 1973435 7498115 := bstep (se 1 (by rfl) ⟨5623586, by rfl⟩ : syracuseStep 7498115 = 11247173) B11247173
theorem B4998743 : Blo 1973435 4998743 := bstep (se 1 (by rfl) ⟨3749057, by rfl⟩ : syracuseStep 4998743 = 7498115) B7498115
theorem B3332495 : Blo 1973435 3332495 := bstep (se 1 (by rfl) ⟨2499371, by rfl⟩ : syracuseStep 3332495 = 4998743) B4998743
theorem B2221663 : Blo 1973435 2221663 := bstep (se 1 (by rfl) ⟨1666247, by rfl⟩ : syracuseStep 2221663 = 3332495) B3332495
theorem B2962217 : Blo 1973435 2962217 := bstep (se 2 (by rfl) ⟨1110831, by rfl⟩ : syracuseStep 2962217 = 2221663) B2221663
theorem B1974811 : Blo 1973435 1974811 := bstep (se 1 (by rfl) ⟨1481108, by rfl⟩ : syracuseStep 1974811 = 2962217) B2962217
theorem B2108849 : Blo 1973435 2108849 := bbase (se 2 (by rfl) ⟨790818, by rfl⟩ : syracuseStep 2108849 = 1581637) (by norm_num)
theorem B5623597 : Blo 1973435 5623597 := bstep (se 3 (by rfl) ⟨1054424, by rfl⟩ : syracuseStep 5623597 = 2108849) B2108849
theorem B7498129 : Blo 1973435 7498129 := bstep (se 2 (by rfl) ⟨2811798, by rfl⟩ : syracuseStep 7498129 = 5623597) B5623597
theorem B9997505 : Blo 1973435 9997505 := bstep (se 2 (by rfl) ⟨3749064, by rfl⟩ : syracuseStep 9997505 = 7498129) B7498129
theorem B6665003 : Blo 1973435 6665003 := bstep (se 1 (by rfl) ⟨4998752, by rfl⟩ : syracuseStep 6665003 = 9997505) B9997505
theorem B4443335 : Blo 1973435 4443335 := bstep (se 1 (by rfl) ⟨3332501, by rfl⟩ : syracuseStep 4443335 = 6665003) B6665003
theorem B2962223 : Blo 1973435 2962223 := bstep (se 1 (by rfl) ⟨2221667, by rfl⟩ : syracuseStep 2962223 = 4443335) B4443335
theorem B1974815 : Blo 1973435 1974815 := bstep (se 1 (by rfl) ⟨1481111, by rfl⟩ : syracuseStep 1974815 = 2962223) B2962223
theorem B2962229 : Blo 1973435 2962229 := bbase (se 5 (by rfl) ⟨138854, by rfl⟩ : syracuseStep 2962229 = 277709) (by norm_num)
theorem B1974819 : Blo 1973435 1974819 := bstep (se 1 (by rfl) ⟨1481114, by rfl⟩ : syracuseStep 1974819 = 2962229) B2962229
theorem B4998773 : Blo 1973435 4998773 := bbase (se 5 (by rfl) ⟨234317, by rfl⟩ : syracuseStep 4998773 = 468635) (by norm_num)
theorem B3332515 : Blo 1973435 3332515 := bstep (se 1 (by rfl) ⟨2499386, by rfl⟩ : syracuseStep 3332515 = 4998773) B4998773
theorem B4443353 : Blo 1973435 4443353 := bstep (se 2 (by rfl) ⟨1666257, by rfl⟩ : syracuseStep 4443353 = 3332515) B3332515
theorem B2962235 : Blo 1973435 2962235 := bstep (se 1 (by rfl) ⟨2221676, by rfl⟩ : syracuseStep 2962235 = 4443353) B4443353
theorem B1974823 : Blo 1973435 1974823 := bstep (se 1 (by rfl) ⟨1481117, by rfl⟩ : syracuseStep 1974823 = 2962235) B2962235
theorem B2221681 : Blo 1973435 2221681 := bbase (se 2 (by rfl) ⟨833130, by rfl⟩ : syracuseStep 2221681 = 1666261) (by norm_num)
theorem B2962241 : Blo 1973435 2962241 := bstep (se 2 (by rfl) ⟨1110840, by rfl⟩ : syracuseStep 2962241 = 2221681) B2221681
theorem B1974827 : Blo 1973435 1974827 := bstep (se 1 (by rfl) ⟨1481120, by rfl⟩ : syracuseStep 1974827 = 2962241) B2962241
theorem B3085157 : Blo 1973435 3085157 := bbase (se 4 (by rfl) ⟨289233, by rfl⟩ : syracuseStep 3085157 = 578467) (by norm_num)
theorem B2056771 : Blo 1973435 2056771 := bstep (se 1 (by rfl) ⟨1542578, by rfl⟩ : syracuseStep 2056771 = 3085157) B3085157
theorem B10969445 : Blo 1973435 10969445 := bstep (se 4 (by rfl) ⟨1028385, by rfl⟩ : syracuseStep 10969445 = 2056771) B2056771
theorem B29251853 : Blo 1973435 29251853 := bstep (se 3 (by rfl) ⟨5484722, by rfl⟩ : syracuseStep 29251853 = 10969445) B10969445
theorem B19501235 : Blo 1973435 19501235 := bstep (se 1 (by rfl) ⟨14625926, by rfl⟩ : syracuseStep 19501235 = 29251853) B29251853
theorem B13000823 : Blo 1973435 13000823 := bstep (se 1 (by rfl) ⟨9750617, by rfl⟩ : syracuseStep 13000823 = 19501235) B19501235
theorem B8667215 : Blo 1973435 8667215 := bstep (se 1 (by rfl) ⟨6500411, by rfl⟩ : syracuseStep 8667215 = 13000823) B13000823
theorem B5778143 : Blo 1973435 5778143 := bstep (se 1 (by rfl) ⟨4333607, by rfl⟩ : syracuseStep 5778143 = 8667215) B8667215
theorem B3852095 : Blo 1973435 3852095 := bstep (se 1 (by rfl) ⟨2889071, by rfl⟩ : syracuseStep 3852095 = 5778143) B5778143
theorem B10272253 : Blo 1973435 10272253 := bstep (se 3 (by rfl) ⟨1926047, by rfl⟩ : syracuseStep 10272253 = 3852095) B3852095
theorem B13696337 : Blo 1973435 13696337 := bstep (se 2 (by rfl) ⟨5136126, by rfl⟩ : syracuseStep 13696337 = 10272253) B10272253
theorem B9130891 : Blo 1973435 9130891 := bstep (se 1 (by rfl) ⟨6848168, by rfl⟩ : syracuseStep 9130891 = 13696337) B13696337
theorem B12174521 : Blo 1973435 12174521 := bstep (se 2 (by rfl) ⟨4565445, by rfl⟩ : syracuseStep 12174521 = 9130891) B9130891
theorem B32465389 : Blo 1973435 32465389 := bstep (se 3 (by rfl) ⟨6087260, by rfl⟩ : syracuseStep 32465389 = 12174521) B12174521
theorem B43287185 : Blo 1973435 43287185 := bstep (se 2 (by rfl) ⟨16232694, by rfl⟩ : syracuseStep 43287185 = 32465389) B32465389
theorem B28858123 : Blo 1973435 28858123 := bstep (se 1 (by rfl) ⟨21643592, by rfl⟩ : syracuseStep 28858123 = 43287185) B43287185
theorem B153909989 : Blo 1973435 153909989 := bstep (se 4 (by rfl) ⟨14429061, by rfl⟩ : syracuseStep 153909989 = 28858123) B28858123
theorem B102606659 : Blo 1973435 102606659 := bstep (se 1 (by rfl) ⟨76954994, by rfl⟩ : syracuseStep 102606659 = 153909989) B153909989
theorem B68404439 : Blo 1973435 68404439 := bstep (se 1 (by rfl) ⟨51303329, by rfl⟩ : syracuseStep 68404439 = 102606659) B102606659
theorem B45602959 : Blo 1973435 45602959 := bstep (se 1 (by rfl) ⟨34202219, by rfl⟩ : syracuseStep 45602959 = 68404439) B68404439
theorem B60803945 : Blo 1973435 60803945 := bstep (se 2 (by rfl) ⟨22801479, by rfl⟩ : syracuseStep 60803945 = 45602959) B45602959
theorem B40535963 : Blo 1973435 40535963 := bstep (se 1 (by rfl) ⟨30401972, by rfl⟩ : syracuseStep 40535963 = 60803945) B60803945
theorem B27023975 : Blo 1973435 27023975 := bstep (se 1 (by rfl) ⟨20267981, by rfl⟩ : syracuseStep 27023975 = 40535963) B40535963
theorem B18015983 : Blo 1973435 18015983 := bstep (se 1 (by rfl) ⟨13511987, by rfl⟩ : syracuseStep 18015983 = 27023975) B27023975
theorem B12010655 : Blo 1973435 12010655 := bstep (se 1 (by rfl) ⟨9007991, by rfl⟩ : syracuseStep 12010655 = 18015983) B18015983
theorem B8007103 : Blo 1973435 8007103 := bstep (se 1 (by rfl) ⟨6005327, by rfl⟩ : syracuseStep 8007103 = 12010655) B12010655
theorem B10676137 : Blo 1973435 10676137 := bstep (se 2 (by rfl) ⟨4003551, by rfl⟩ : syracuseStep 10676137 = 8007103) B8007103
theorem B14234849 : Blo 1973435 14234849 := bstep (se 2 (by rfl) ⟨5338068, by rfl⟩ : syracuseStep 14234849 = 10676137) B10676137
theorem B9489899 : Blo 1973435 9489899 := bstep (se 1 (by rfl) ⟨7117424, by rfl⟩ : syracuseStep 9489899 = 14234849) B14234849
theorem B6326599 : Blo 1973435 6326599 := bstep (se 1 (by rfl) ⟨4744949, by rfl⟩ : syracuseStep 6326599 = 9489899) B9489899
theorem B8435465 : Blo 1973435 8435465 := bstep (se 2 (by rfl) ⟨3163299, by rfl⟩ : syracuseStep 8435465 = 6326599) B6326599
theorem B5623643 : Blo 1973435 5623643 := bstep (se 1 (by rfl) ⟨4217732, by rfl⟩ : syracuseStep 5623643 = 8435465) B8435465
theorem B3749095 : Blo 1973435 3749095 := bstep (se 1 (by rfl) ⟨2811821, by rfl⟩ : syracuseStep 3749095 = 5623643) B5623643
theorem B4998793 : Blo 1973435 4998793 := bstep (se 2 (by rfl) ⟨1874547, by rfl⟩ : syracuseStep 4998793 = 3749095) B3749095
theorem B6665057 : Blo 1973435 6665057 := bstep (se 2 (by rfl) ⟨2499396, by rfl⟩ : syracuseStep 6665057 = 4998793) B4998793
theorem B4443371 : Blo 1973435 4443371 := bstep (se 1 (by rfl) ⟨3332528, by rfl⟩ : syracuseStep 4443371 = 6665057) B6665057
theorem B2962247 : Blo 1973435 2962247 := bstep (se 1 (by rfl) ⟨2221685, by rfl⟩ : syracuseStep 2962247 = 4443371) B4443371
theorem B1974831 : Blo 1973435 1974831 := bstep (se 1 (by rfl) ⟨1481123, by rfl⟩ : syracuseStep 1974831 = 2962247) B2962247
theorem B2962253 : Blo 1973435 2962253 := bbase (se 3 (by rfl) ⟨555422, by rfl⟩ : syracuseStep 2962253 = 1110845) (by norm_num)
theorem B1974835 : Blo 1973435 1974835 := bstep (se 1 (by rfl) ⟨1481126, by rfl⟩ : syracuseStep 1974835 = 2962253) B2962253
theorem B4443389 : Blo 1973435 4443389 := bbase (se 3 (by rfl) ⟨833135, by rfl⟩ : syracuseStep 4443389 = 1666271) (by norm_num)
theorem B2962259 : Blo 1973435 2962259 := bstep (se 1 (by rfl) ⟨2221694, by rfl⟩ : syracuseStep 2962259 = 4443389) B4443389
theorem B1974839 : Blo 1973435 1974839 := bstep (se 1 (by rfl) ⟨1481129, by rfl⟩ : syracuseStep 1974839 = 2962259) B2962259
theorem B3332549 : Blo 1973435 3332549 := bbase (se 4 (by rfl) ⟨312426, by rfl⟩ : syracuseStep 3332549 = 624853) (by norm_num)
theorem B2221699 : Blo 1973435 2221699 := bstep (se 1 (by rfl) ⟨1666274, by rfl⟩ : syracuseStep 2221699 = 3332549) B3332549
theorem B2962265 : Blo 1973435 2962265 := bstep (se 2 (by rfl) ⟨1110849, by rfl⟩ : syracuseStep 2962265 = 2221699) B2221699
theorem B1974843 : Blo 1973435 1974843 := bstep (se 1 (by rfl) ⟨1481132, by rfl⟩ : syracuseStep 1974843 = 2962265) B2962265
theorem B14996501 : Blo 1973435 14996501 := bbase (se 6 (by rfl) ⟨351480, by rfl⟩ : syracuseStep 14996501 = 702961) (by norm_num)
theorem B9997667 : Blo 1973435 9997667 := bstep (se 1 (by rfl) ⟨7498250, by rfl⟩ : syracuseStep 9997667 = 14996501) B14996501
theorem B6665111 : Blo 1973435 6665111 := bstep (se 1 (by rfl) ⟨4998833, by rfl⟩ : syracuseStep 6665111 = 9997667) B9997667
theorem B4443407 : Blo 1973435 4443407 := bstep (se 1 (by rfl) ⟨3332555, by rfl⟩ : syracuseStep 4443407 = 6665111) B6665111
theorem B2962271 : Blo 1973435 2962271 := bstep (se 1 (by rfl) ⟨2221703, by rfl⟩ : syracuseStep 2962271 = 4443407) B4443407
theorem B1974847 : Blo 1973435 1974847 := bstep (se 1 (by rfl) ⟨1481135, by rfl⟩ : syracuseStep 1974847 = 2962271) B2962271
theorem B2962277 : Blo 1973435 2962277 := bbase (se 4 (by rfl) ⟨277713, by rfl⟩ : syracuseStep 2962277 = 555427) (by norm_num)
theorem B1974851 : Blo 1973435 1974851 := bstep (se 1 (by rfl) ⟨1481138, by rfl⟩ : syracuseStep 1974851 = 2962277) B2962277
theorem B3749141 : Blo 1973435 3749141 := bbase (se 6 (by rfl) ⟨87870, by rfl⟩ : syracuseStep 3749141 = 175741) (by norm_num)
theorem B2499427 : Blo 1973435 2499427 := bstep (se 1 (by rfl) ⟨1874570, by rfl⟩ : syracuseStep 2499427 = 3749141) B3749141
theorem B3332569 : Blo 1973435 3332569 := bstep (se 2 (by rfl) ⟨1249713, by rfl⟩ : syracuseStep 3332569 = 2499427) B2499427
theorem B4443425 : Blo 1973435 4443425 := bstep (se 2 (by rfl) ⟨1666284, by rfl⟩ : syracuseStep 4443425 = 3332569) B3332569
theorem B2962283 : Blo 1973435 2962283 := bstep (se 1 (by rfl) ⟨2221712, by rfl⟩ : syracuseStep 2962283 = 4443425) B4443425
theorem B1974855 : Blo 1973435 1974855 := bstep (se 1 (by rfl) ⟨1481141, by rfl⟩ : syracuseStep 1974855 = 2962283) B2962283
theorem B2221717 : Blo 1973435 2221717 := bbase (se 6 (by rfl) ⟨52071, by rfl⟩ : syracuseStep 2221717 = 104143) (by norm_num)
theorem B2962289 : Blo 1973435 2962289 := bstep (se 2 (by rfl) ⟨1110858, by rfl⟩ : syracuseStep 2962289 = 2221717) B2221717
theorem B1974859 : Blo 1973435 1974859 := bstep (se 1 (by rfl) ⟨1481144, by rfl⟩ : syracuseStep 1974859 = 2962289) B2962289
theorem B2499437 : Blo 1973435 2499437 := bbase (se 3 (by rfl) ⟨468644, by rfl⟩ : syracuseStep 2499437 = 937289) (by norm_num)
theorem B6665165 : Blo 1973435 6665165 := bstep (se 3 (by rfl) ⟨1249718, by rfl⟩ : syracuseStep 6665165 = 2499437) B2499437
theorem B4443443 : Blo 1973435 4443443 := bstep (se 1 (by rfl) ⟨3332582, by rfl⟩ : syracuseStep 4443443 = 6665165) B6665165
theorem B2962295 : Blo 1973435 2962295 := bstep (se 1 (by rfl) ⟨2221721, by rfl⟩ : syracuseStep 2962295 = 4443443) B4443443
theorem B1974863 : Blo 1973435 1974863 := bstep (se 1 (by rfl) ⟨1481147, by rfl⟩ : syracuseStep 1974863 = 2962295) B2962295
theorem B2962301 : Blo 1973435 2962301 := bbase (se 3 (by rfl) ⟨555431, by rfl⟩ : syracuseStep 2962301 = 1110863) (by norm_num)
theorem B1974867 : Blo 1973435 1974867 := bstep (se 1 (by rfl) ⟨1481150, by rfl⟩ : syracuseStep 1974867 = 2962301) B2962301
theorem B4443461 : Blo 1973435 4443461 := bbase (se 4 (by rfl) ⟨416574, by rfl⟩ : syracuseStep 4443461 = 833149) (by norm_num)
theorem B2962307 : Blo 1973435 2962307 := bstep (se 1 (by rfl) ⟨2221730, by rfl⟩ : syracuseStep 2962307 = 4443461) B4443461
theorem B1974871 : Blo 1973435 1974871 := bstep (se 1 (by rfl) ⟨1481153, by rfl⟩ : syracuseStep 1974871 = 2962307) B2962307
theorem B6326741 : Blo 1973435 6326741 := bbase (se 7 (by rfl) ⟨74141, by rfl⟩ : syracuseStep 6326741 = 148283) (by norm_num)
theorem B4217827 : Blo 1973435 4217827 := bstep (se 1 (by rfl) ⟨3163370, by rfl⟩ : syracuseStep 4217827 = 6326741) B6326741
theorem B5623769 : Blo 1973435 5623769 := bstep (se 2 (by rfl) ⟨2108913, by rfl⟩ : syracuseStep 5623769 = 4217827) B4217827
theorem B3749179 : Blo 1973435 3749179 := bstep (se 1 (by rfl) ⟨2811884, by rfl⟩ : syracuseStep 3749179 = 5623769) B5623769
theorem B4998905 : Blo 1973435 4998905 := bstep (se 2 (by rfl) ⟨1874589, by rfl⟩ : syracuseStep 4998905 = 3749179) B3749179
theorem B3332603 : Blo 1973435 3332603 := bstep (se 1 (by rfl) ⟨2499452, by rfl⟩ : syracuseStep 3332603 = 4998905) B4998905
theorem B2221735 : Blo 1973435 2221735 := bstep (se 1 (by rfl) ⟨1666301, by rfl⟩ : syracuseStep 2221735 = 3332603) B3332603
theorem B2962313 : Blo 1973435 2962313 := bstep (se 2 (by rfl) ⟨1110867, by rfl⟩ : syracuseStep 2962313 = 2221735) B2221735
theorem B1974875 : Blo 1973435 1974875 := bstep (se 1 (by rfl) ⟨1481156, by rfl⟩ : syracuseStep 1974875 = 2962313) B2962313
theorem B9997829 : Blo 1973435 9997829 := bbase (se 4 (by rfl) ⟨937296, by rfl⟩ : syracuseStep 9997829 = 1874593) (by norm_num)
theorem B6665219 : Blo 1973435 6665219 := bstep (se 1 (by rfl) ⟨4998914, by rfl⟩ : syracuseStep 6665219 = 9997829) B9997829
theorem B4443479 : Blo 1973435 4443479 := bstep (se 1 (by rfl) ⟨3332609, by rfl⟩ : syracuseStep 4443479 = 6665219) B6665219
theorem B2962319 : Blo 1973435 2962319 := bstep (se 1 (by rfl) ⟨2221739, by rfl⟩ : syracuseStep 2962319 = 4443479) B4443479
theorem B1974879 : Blo 1973435 1974879 := bstep (se 1 (by rfl) ⟨1481159, by rfl⟩ : syracuseStep 1974879 = 2962319) B2962319
theorem B2962325 : Blo 1973435 2962325 := bbase (se 6 (by rfl) ⟨69429, by rfl⟩ : syracuseStep 2962325 = 138859) (by norm_num)
theorem B1974883 : Blo 1973435 1974883 := bstep (se 1 (by rfl) ⟨1481162, by rfl⟩ : syracuseStep 1974883 = 2962325) B2962325
theorem B11247605 : Blo 1973435 11247605 := bbase (se 5 (by rfl) ⟨527231, by rfl⟩ : syracuseStep 11247605 = 1054463) (by norm_num)
theorem B7498403 : Blo 1973435 7498403 := bstep (se 1 (by rfl) ⟨5623802, by rfl⟩ : syracuseStep 7498403 = 11247605) B11247605
theorem B4998935 : Blo 1973435 4998935 := bstep (se 1 (by rfl) ⟨3749201, by rfl⟩ : syracuseStep 4998935 = 7498403) B7498403
theorem B3332623 : Blo 1973435 3332623 := bstep (se 1 (by rfl) ⟨2499467, by rfl⟩ : syracuseStep 3332623 = 4998935) B4998935
theorem B4443497 : Blo 1973435 4443497 := bstep (se 2 (by rfl) ⟨1666311, by rfl⟩ : syracuseStep 4443497 = 3332623) B3332623
theorem B2962331 : Blo 1973435 2962331 := bstep (se 1 (by rfl) ⟨2221748, by rfl⟩ : syracuseStep 2962331 = 4443497) B4443497
theorem B1974887 : Blo 1973435 1974887 := bstep (se 1 (by rfl) ⟨1481165, by rfl⟩ : syracuseStep 1974887 = 2962331) B2962331
theorem B2221753 : Blo 1973435 2221753 := bbase (se 2 (by rfl) ⟨833157, by rfl⟩ : syracuseStep 2221753 = 1666315) (by norm_num)
theorem B2962337 : Blo 1973435 2962337 := bstep (se 2 (by rfl) ⟨1110876, by rfl⟩ : syracuseStep 2962337 = 2221753) B2221753
theorem B1974891 : Blo 1973435 1974891 := bstep (se 1 (by rfl) ⟨1481168, by rfl⟩ : syracuseStep 1974891 = 2962337) B2962337
theorem B4217869 : Blo 1973435 4217869 := bbase (se 3 (by rfl) ⟨790850, by rfl⟩ : syracuseStep 4217869 = 1581701) (by norm_num)
theorem B5623825 : Blo 1973435 5623825 := bstep (se 2 (by rfl) ⟨2108934, by rfl⟩ : syracuseStep 5623825 = 4217869) B4217869
theorem B7498433 : Blo 1973435 7498433 := bstep (se 2 (by rfl) ⟨2811912, by rfl⟩ : syracuseStep 7498433 = 5623825) B5623825
theorem B4998955 : Blo 1973435 4998955 := bstep (se 1 (by rfl) ⟨3749216, by rfl⟩ : syracuseStep 4998955 = 7498433) B7498433
theorem B6665273 : Blo 1973435 6665273 := bstep (se 2 (by rfl) ⟨2499477, by rfl⟩ : syracuseStep 6665273 = 4998955) B4998955
theorem B4443515 : Blo 1973435 4443515 := bstep (se 1 (by rfl) ⟨3332636, by rfl⟩ : syracuseStep 4443515 = 6665273) B6665273
theorem B2962343 : Blo 1973435 2962343 := bstep (se 1 (by rfl) ⟨2221757, by rfl⟩ : syracuseStep 2962343 = 4443515) B4443515
theorem B1974895 : Blo 1973435 1974895 := bstep (se 1 (by rfl) ⟨1481171, by rfl⟩ : syracuseStep 1974895 = 2962343) B2962343
theorem B2962349 : Blo 1973435 2962349 := bbase (se 3 (by rfl) ⟨555440, by rfl⟩ : syracuseStep 2962349 = 1110881) (by norm_num)
theorem B1974899 : Blo 1973435 1974899 := bstep (se 1 (by rfl) ⟨1481174, by rfl⟩ : syracuseStep 1974899 = 2962349) B2962349
theorem B4443533 : Blo 1973435 4443533 := bbase (se 3 (by rfl) ⟨833162, by rfl⟩ : syracuseStep 4443533 = 1666325) (by norm_num)
theorem B2962355 : Blo 1973435 2962355 := bstep (se 1 (by rfl) ⟨2221766, by rfl⟩ : syracuseStep 2962355 = 4443533) B4443533
theorem B1974903 : Blo 1973435 1974903 := bstep (se 1 (by rfl) ⟨1481177, by rfl⟩ : syracuseStep 1974903 = 2962355) B2962355
theorem B2499493 : Blo 1973435 2499493 := bbase (se 4 (by rfl) ⟨234327, by rfl⟩ : syracuseStep 2499493 = 468655) (by norm_num)
theorem B3332657 : Blo 1973435 3332657 := bstep (se 2 (by rfl) ⟨1249746, by rfl⟩ : syracuseStep 3332657 = 2499493) B2499493
theorem B2221771 : Blo 1973435 2221771 := bstep (se 1 (by rfl) ⟨1666328, by rfl⟩ : syracuseStep 2221771 = 3332657) B3332657
theorem B2962361 : Blo 1973435 2962361 := bstep (se 2 (by rfl) ⟨1110885, by rfl⟩ : syracuseStep 2962361 = 2221771) B2221771
theorem B1974907 : Blo 1973435 1974907 := bstep (se 1 (by rfl) ⟨1481180, by rfl⟩ : syracuseStep 1974907 = 2962361) B2962361
theorem B3378133 : Blo 1973435 3378133 := bbase (se 7 (by rfl) ⟨39587, by rfl⟩ : syracuseStep 3378133 = 79175) (by norm_num)
theorem B4504177 : Blo 1973435 4504177 := bstep (se 2 (by rfl) ⟨1689066, by rfl⟩ : syracuseStep 4504177 = 3378133) B3378133
theorem B24022277 : Blo 1973435 24022277 := bstep (se 4 (by rfl) ⟨2252088, by rfl⟩ : syracuseStep 24022277 = 4504177) B4504177
theorem B16014851 : Blo 1973435 16014851 := bstep (se 1 (by rfl) ⟨12011138, by rfl⟩ : syracuseStep 16014851 = 24022277) B24022277
theorem B10676567 : Blo 1973435 10676567 := bstep (se 1 (by rfl) ⟨8007425, by rfl⟩ : syracuseStep 10676567 = 16014851) B16014851
theorem B28470845 : Blo 1973435 28470845 := bstep (se 3 (by rfl) ⟨5338283, by rfl⟩ : syracuseStep 28470845 = 10676567) B10676567
theorem B18980563 : Blo 1973435 18980563 := bstep (se 1 (by rfl) ⟨14235422, by rfl⟩ : syracuseStep 18980563 = 28470845) B28470845
theorem B25307417 : Blo 1973435 25307417 := bstep (se 2 (by rfl) ⟨9490281, by rfl⟩ : syracuseStep 25307417 = 18980563) B18980563
theorem B16871611 : Blo 1973435 16871611 := bstep (se 1 (by rfl) ⟨12653708, by rfl⟩ : syracuseStep 16871611 = 25307417) B25307417
theorem B22495481 : Blo 1973435 22495481 := bstep (se 2 (by rfl) ⟨8435805, by rfl⟩ : syracuseStep 22495481 = 16871611) B16871611
theorem B14996987 : Blo 1973435 14996987 := bstep (se 1 (by rfl) ⟨11247740, by rfl⟩ : syracuseStep 14996987 = 22495481) B22495481
theorem B9997991 : Blo 1973435 9997991 := bstep (se 1 (by rfl) ⟨7498493, by rfl⟩ : syracuseStep 9997991 = 14996987) B14996987
theorem B6665327 : Blo 1973435 6665327 := bstep (se 1 (by rfl) ⟨4998995, by rfl⟩ : syracuseStep 6665327 = 9997991) B9997991
theorem B4443551 : Blo 1973435 4443551 := bstep (se 1 (by rfl) ⟨3332663, by rfl⟩ : syracuseStep 4443551 = 6665327) B6665327
theorem B2962367 : Blo 1973435 2962367 := bstep (se 1 (by rfl) ⟨2221775, by rfl⟩ : syracuseStep 2962367 = 4443551) B4443551
theorem B1974911 : Blo 1973435 1974911 := bstep (se 1 (by rfl) ⟨1481183, by rfl⟩ : syracuseStep 1974911 = 2962367) B2962367
theorem B2962373 : Blo 1973435 2962373 := bbase (se 4 (by rfl) ⟨277722, by rfl⟩ : syracuseStep 2962373 = 555445) (by norm_num)
theorem B1974915 : Blo 1973435 1974915 := bstep (se 1 (by rfl) ⟨1481186, by rfl⟩ : syracuseStep 1974915 = 2962373) B2962373
theorem B3332677 : Blo 1973435 3332677 := bbase (se 4 (by rfl) ⟨312438, by rfl⟩ : syracuseStep 3332677 = 624877) (by norm_num)
theorem B4443569 : Blo 1973435 4443569 := bstep (se 2 (by rfl) ⟨1666338, by rfl⟩ : syracuseStep 4443569 = 3332677) B3332677
theorem B2962379 : Blo 1973435 2962379 := bstep (se 1 (by rfl) ⟨2221784, by rfl⟩ : syracuseStep 2962379 = 4443569) B4443569
theorem B1974919 : Blo 1973435 1974919 := bstep (se 1 (by rfl) ⟨1481189, by rfl⟩ : syracuseStep 1974919 = 2962379) B2962379
theorem B2221789 : Blo 1973435 2221789 := bbase (se 3 (by rfl) ⟨416585, by rfl⟩ : syracuseStep 2221789 = 833171) (by norm_num)
theorem B2962385 : Blo 1973435 2962385 := bstep (se 2 (by rfl) ⟨1110894, by rfl⟩ : syracuseStep 2962385 = 2221789) B2221789
theorem B1974923 : Blo 1973435 1974923 := bstep (se 1 (by rfl) ⟨1481192, by rfl⟩ : syracuseStep 1974923 = 2962385) B2962385
theorem B6665381 : Blo 1973435 6665381 := bbase (se 4 (by rfl) ⟨624879, by rfl⟩ : syracuseStep 6665381 = 1249759) (by norm_num)
theorem B4443587 : Blo 1973435 4443587 := bstep (se 1 (by rfl) ⟨3332690, by rfl⟩ : syracuseStep 4443587 = 6665381) B6665381
theorem B2962391 : Blo 1973435 2962391 := bstep (se 1 (by rfl) ⟨2221793, by rfl⟩ : syracuseStep 2962391 = 4443587) B4443587
theorem B1974927 : Blo 1973435 1974927 := bstep (se 1 (by rfl) ⟨1481195, by rfl⟩ : syracuseStep 1974927 = 2962391) B2962391
theorem B2962397 : Blo 1973435 2962397 := bbase (se 3 (by rfl) ⟨555449, by rfl⟩ : syracuseStep 2962397 = 1110899) (by norm_num)
theorem B1974931 : Blo 1973435 1974931 := bstep (se 1 (by rfl) ⟨1481198, by rfl⟩ : syracuseStep 1974931 = 2962397) B2962397
theorem B4443605 : Blo 1973435 4443605 := bbase (se 7 (by rfl) ⟨52073, by rfl⟩ : syracuseStep 4443605 = 104147) (by norm_num)
theorem B2962403 : Blo 1973435 2962403 := bstep (se 1 (by rfl) ⟨2221802, by rfl⟩ : syracuseStep 2962403 = 4443605) B4443605
theorem B1974935 : Blo 1973435 1974935 := bstep (se 1 (by rfl) ⟨1481201, by rfl⟩ : syracuseStep 1974935 = 2962403) B2962403
theorem B2533637 : Blo 1973435 2533637 := bbase (se 4 (by rfl) ⟨237528, by rfl⟩ : syracuseStep 2533637 = 475057) (by norm_num)
theorem B6756365 : Blo 1973435 6756365 := bstep (se 3 (by rfl) ⟨1266818, by rfl⟩ : syracuseStep 6756365 = 2533637) B2533637
theorem B4504243 : Blo 1973435 4504243 := bstep (se 1 (by rfl) ⟨3378182, by rfl⟩ : syracuseStep 4504243 = 6756365) B6756365
theorem B6005657 : Blo 1973435 6005657 := bstep (se 2 (by rfl) ⟨2252121, by rfl⟩ : syracuseStep 6005657 = 4504243) B4504243
theorem B4003771 : Blo 1973435 4003771 := bstep (se 1 (by rfl) ⟨3002828, by rfl⟩ : syracuseStep 4003771 = 6005657) B6005657
theorem B5338361 : Blo 1973435 5338361 := bstep (se 2 (by rfl) ⟨2001885, by rfl⟩ : syracuseStep 5338361 = 4003771) B4003771
theorem B3558907 : Blo 1973435 3558907 := bstep (se 1 (by rfl) ⟨2669180, by rfl⟩ : syracuseStep 3558907 = 5338361) B5338361
theorem B18980837 : Blo 1973435 18980837 := bstep (se 4 (by rfl) ⟨1779453, by rfl⟩ : syracuseStep 18980837 = 3558907) B3558907
theorem B12653891 : Blo 1973435 12653891 := bstep (se 1 (by rfl) ⟨9490418, by rfl⟩ : syracuseStep 12653891 = 18980837) B18980837
theorem B8435927 : Blo 1973435 8435927 := bstep (se 1 (by rfl) ⟨6326945, by rfl⟩ : syracuseStep 8435927 = 12653891) B12653891
theorem B5623951 : Blo 1973435 5623951 := bstep (se 1 (by rfl) ⟨4217963, by rfl⟩ : syracuseStep 5623951 = 8435927) B8435927
theorem B7498601 : Blo 1973435 7498601 := bstep (se 2 (by rfl) ⟨2811975, by rfl⟩ : syracuseStep 7498601 = 5623951) B5623951
theorem B4999067 : Blo 1973435 4999067 := bstep (se 1 (by rfl) ⟨3749300, by rfl⟩ : syracuseStep 4999067 = 7498601) B7498601
theorem B3332711 : Blo 1973435 3332711 := bstep (se 1 (by rfl) ⟨2499533, by rfl⟩ : syracuseStep 3332711 = 4999067) B4999067
theorem B2221807 : Blo 1973435 2221807 := bstep (se 1 (by rfl) ⟨1666355, by rfl⟩ : syracuseStep 2221807 = 3332711) B3332711
theorem B2962409 : Blo 1973435 2962409 := bstep (se 2 (by rfl) ⟨1110903, by rfl⟩ : syracuseStep 2962409 = 2221807) B2221807
theorem B1974939 : Blo 1973435 1974939 := bstep (se 1 (by rfl) ⟨1481204, by rfl⟩ : syracuseStep 1974939 = 2962409) B2962409
theorem B2372609 : Blo 1973435 2372609 := bbase (se 2 (by rfl) ⟨889728, by rfl⟩ : syracuseStep 2372609 = 1779457) (by norm_num)
theorem B6326957 : Blo 1973435 6326957 := bstep (se 3 (by rfl) ⟨1186304, by rfl⟩ : syracuseStep 6326957 = 2372609) B2372609
theorem B16871885 : Blo 1973435 16871885 := bstep (se 3 (by rfl) ⟨3163478, by rfl⟩ : syracuseStep 16871885 = 6326957) B6326957
theorem B11247923 : Blo 1973435 11247923 := bstep (se 1 (by rfl) ⟨8435942, by rfl⟩ : syracuseStep 11247923 = 16871885) B16871885
theorem B7498615 : Blo 1973435 7498615 := bstep (se 1 (by rfl) ⟨5623961, by rfl⟩ : syracuseStep 7498615 = 11247923) B11247923
theorem B9998153 : Blo 1973435 9998153 := bstep (se 2 (by rfl) ⟨3749307, by rfl⟩ : syracuseStep 9998153 = 7498615) B7498615
theorem B6665435 : Blo 1973435 6665435 := bstep (se 1 (by rfl) ⟨4999076, by rfl⟩ : syracuseStep 6665435 = 9998153) B9998153
theorem B4443623 : Blo 1973435 4443623 := bstep (se 1 (by rfl) ⟨3332717, by rfl⟩ : syracuseStep 4443623 = 6665435) B6665435
theorem B2962415 : Blo 1973435 2962415 := bstep (se 1 (by rfl) ⟨2221811, by rfl⟩ : syracuseStep 2962415 = 4443623) B4443623
theorem B1974943 : Blo 1973435 1974943 := bstep (se 1 (by rfl) ⟨1481207, by rfl⟩ : syracuseStep 1974943 = 2962415) B2962415
theorem B2962421 : Blo 1973435 2962421 := bbase (se 5 (by rfl) ⟨138863, by rfl⟩ : syracuseStep 2962421 = 277727) (by norm_num)
theorem B1974947 : Blo 1973435 1974947 := bstep (se 1 (by rfl) ⟨1481210, by rfl⟩ : syracuseStep 1974947 = 2962421) B2962421
theorem B4217989 : Blo 1973435 4217989 := bbase (se 4 (by rfl) ⟨395436, by rfl⟩ : syracuseStep 4217989 = 790873) (by norm_num)
theorem B5623985 : Blo 1973435 5623985 := bstep (se 2 (by rfl) ⟨2108994, by rfl⟩ : syracuseStep 5623985 = 4217989) B4217989
theorem B3749323 : Blo 1973435 3749323 := bstep (se 1 (by rfl) ⟨2811992, by rfl⟩ : syracuseStep 3749323 = 5623985) B5623985
theorem B4999097 : Blo 1973435 4999097 := bstep (se 2 (by rfl) ⟨1874661, by rfl⟩ : syracuseStep 4999097 = 3749323) B3749323
theorem B3332731 : Blo 1973435 3332731 := bstep (se 1 (by rfl) ⟨2499548, by rfl⟩ : syracuseStep 3332731 = 4999097) B4999097
theorem B4443641 : Blo 1973435 4443641 := bstep (se 2 (by rfl) ⟨1666365, by rfl⟩ : syracuseStep 4443641 = 3332731) B3332731
theorem B2962427 : Blo 1973435 2962427 := bstep (se 1 (by rfl) ⟨2221820, by rfl⟩ : syracuseStep 2962427 = 4443641) B4443641
theorem B1974951 : Blo 1973435 1974951 := bstep (se 1 (by rfl) ⟨1481213, by rfl⟩ : syracuseStep 1974951 = 2962427) B2962427
theorem B2221825 : Blo 1973435 2221825 := bbase (se 2 (by rfl) ⟨833184, by rfl⟩ : syracuseStep 2221825 = 1666369) (by norm_num)
theorem B2962433 : Blo 1973435 2962433 := bstep (se 2 (by rfl) ⟨1110912, by rfl⟩ : syracuseStep 2962433 = 2221825) B2221825
theorem B1974955 : Blo 1973435 1974955 := bstep (se 1 (by rfl) ⟨1481216, by rfl⟩ : syracuseStep 1974955 = 2962433) B2962433
theorem B4999117 : Blo 1973435 4999117 := bbase (se 3 (by rfl) ⟨937334, by rfl⟩ : syracuseStep 4999117 = 1874669) (by norm_num)
theorem B6665489 : Blo 1973435 6665489 := bstep (se 2 (by rfl) ⟨2499558, by rfl⟩ : syracuseStep 6665489 = 4999117) B4999117
theorem B4443659 : Blo 1973435 4443659 := bstep (se 1 (by rfl) ⟨3332744, by rfl⟩ : syracuseStep 4443659 = 6665489) B6665489
theorem B2962439 : Blo 1973435 2962439 := bstep (se 1 (by rfl) ⟨2221829, by rfl⟩ : syracuseStep 2962439 = 4443659) B4443659
theorem B1974959 : Blo 1973435 1974959 := bstep (se 1 (by rfl) ⟨1481219, by rfl⟩ : syracuseStep 1974959 = 2962439) B2962439
theorem B2962445 : Blo 1973435 2962445 := bbase (se 3 (by rfl) ⟨555458, by rfl⟩ : syracuseStep 2962445 = 1110917) (by norm_num)
theorem B1974963 : Blo 1973435 1974963 := bstep (se 1 (by rfl) ⟨1481222, by rfl⟩ : syracuseStep 1974963 = 2962445) B2962445
theorem B4443677 : Blo 1973435 4443677 := bbase (se 3 (by rfl) ⟨833189, by rfl⟩ : syracuseStep 4443677 = 1666379) (by norm_num)
theorem B2962451 : Blo 1973435 2962451 := bstep (se 1 (by rfl) ⟨2221838, by rfl⟩ : syracuseStep 2962451 = 4443677) B4443677
theorem B1974967 : Blo 1973435 1974967 := bstep (se 1 (by rfl) ⟨1481225, by rfl⟩ : syracuseStep 1974967 = 2962451) B2962451
theorem B3332765 : Blo 1973435 3332765 := bbase (se 3 (by rfl) ⟨624893, by rfl⟩ : syracuseStep 3332765 = 1249787) (by norm_num)
theorem B2221843 : Blo 1973435 2221843 := bstep (se 1 (by rfl) ⟨1666382, by rfl⟩ : syracuseStep 2221843 = 3332765) B3332765
theorem B2962457 : Blo 1973435 2962457 := bstep (se 2 (by rfl) ⟨1110921, by rfl⟩ : syracuseStep 2962457 = 2221843) B2221843
theorem B1974971 : Blo 1973435 1974971 := bstep (se 1 (by rfl) ⟨1481228, by rfl⟩ : syracuseStep 1974971 = 2962457) B2962457
theorem B32030741 : Blo 1973435 32030741 := bbase (se 6 (by rfl) ⟨750720, by rfl⟩ : syracuseStep 32030741 = 1501441) (by norm_num)
theorem B21353827 : Blo 1973435 21353827 := bstep (se 1 (by rfl) ⟨16015370, by rfl⟩ : syracuseStep 21353827 = 32030741) B32030741
theorem B28471769 : Blo 1973435 28471769 := bstep (se 2 (by rfl) ⟨10676913, by rfl⟩ : syracuseStep 28471769 = 21353827) B21353827
theorem B18981179 : Blo 1973435 18981179 := bstep (se 1 (by rfl) ⟨14235884, by rfl⟩ : syracuseStep 18981179 = 28471769) B28471769
theorem B12654119 : Blo 1973435 12654119 := bstep (se 1 (by rfl) ⟨9490589, by rfl⟩ : syracuseStep 12654119 = 18981179) B18981179
theorem B8436079 : Blo 1973435 8436079 := bstep (se 1 (by rfl) ⟨6327059, by rfl⟩ : syracuseStep 8436079 = 12654119) B12654119
theorem B11248105 : Blo 1973435 11248105 := bstep (se 2 (by rfl) ⟨4218039, by rfl⟩ : syracuseStep 11248105 = 8436079) B8436079
theorem B14997473 : Blo 1973435 14997473 := bstep (se 2 (by rfl) ⟨5624052, by rfl⟩ : syracuseStep 14997473 = 11248105) B11248105
theorem B9998315 : Blo 1973435 9998315 := bstep (se 1 (by rfl) ⟨7498736, by rfl⟩ : syracuseStep 9998315 = 14997473) B14997473
theorem B6665543 : Blo 1973435 6665543 := bstep (se 1 (by rfl) ⟨4999157, by rfl⟩ : syracuseStep 6665543 = 9998315) B9998315
theorem B4443695 : Blo 1973435 4443695 := bstep (se 1 (by rfl) ⟨3332771, by rfl⟩ : syracuseStep 4443695 = 6665543) B6665543
theorem B2962463 : Blo 1973435 2962463 := bstep (se 1 (by rfl) ⟨2221847, by rfl⟩ : syracuseStep 2962463 = 4443695) B4443695
theorem B1974975 : Blo 1973435 1974975 := bstep (se 1 (by rfl) ⟨1481231, by rfl⟩ : syracuseStep 1974975 = 2962463) B2962463
theorem B2962469 : Blo 1973435 2962469 := bbase (se 4 (by rfl) ⟨277731, by rfl⟩ : syracuseStep 2962469 = 555463) (by norm_num)
theorem B1974979 : Blo 1973435 1974979 := bstep (se 1 (by rfl) ⟨1481234, by rfl⟩ : syracuseStep 1974979 = 2962469) B2962469
theorem B2499589 : Blo 1973435 2499589 := bbase (se 4 (by rfl) ⟨234336, by rfl⟩ : syracuseStep 2499589 = 468673) (by norm_num)
theorem B3332785 : Blo 1973435 3332785 := bstep (se 2 (by rfl) ⟨1249794, by rfl⟩ : syracuseStep 3332785 = 2499589) B2499589
theorem B4443713 : Blo 1973435 4443713 := bstep (se 2 (by rfl) ⟨1666392, by rfl⟩ : syracuseStep 4443713 = 3332785) B3332785
theorem B2962475 : Blo 1973435 2962475 := bstep (se 1 (by rfl) ⟨2221856, by rfl⟩ : syracuseStep 2962475 = 4443713) B4443713
theorem B1974983 : Blo 1973435 1974983 := bstep (se 1 (by rfl) ⟨1481237, by rfl⟩ : syracuseStep 1974983 = 2962475) B2962475
theorem B2221861 : Blo 1973435 2221861 := bbase (se 4 (by rfl) ⟨208299, by rfl⟩ : syracuseStep 2221861 = 416599) (by norm_num)
theorem B2962481 : Blo 1973435 2962481 := bstep (se 2 (by rfl) ⟨1110930, by rfl⟩ : syracuseStep 2962481 = 2221861) B2221861
theorem B1974987 : Blo 1973435 1974987 := bstep (se 1 (by rfl) ⟨1481240, by rfl⟩ : syracuseStep 1974987 = 2962481) B2962481
theorem B8436149 : Blo 1973435 8436149 := bbase (se 5 (by rfl) ⟨395444, by rfl⟩ : syracuseStep 8436149 = 790889) (by norm_num)
theorem B5624099 : Blo 1973435 5624099 := bstep (se 1 (by rfl) ⟨4218074, by rfl⟩ : syracuseStep 5624099 = 8436149) B8436149
theorem B3749399 : Blo 1973435 3749399 := bstep (se 1 (by rfl) ⟨2812049, by rfl⟩ : syracuseStep 3749399 = 5624099) B5624099
theorem B2499599 : Blo 1973435 2499599 := bstep (se 1 (by rfl) ⟨1874699, by rfl⟩ : syracuseStep 2499599 = 3749399) B3749399
theorem B6665597 : Blo 1973435 6665597 := bstep (se 3 (by rfl) ⟨1249799, by rfl⟩ : syracuseStep 6665597 = 2499599) B2499599
theorem B4443731 : Blo 1973435 4443731 := bstep (se 1 (by rfl) ⟨3332798, by rfl⟩ : syracuseStep 4443731 = 6665597) B6665597
theorem B2962487 : Blo 1973435 2962487 := bstep (se 1 (by rfl) ⟨2221865, by rfl⟩ : syracuseStep 2962487 = 4443731) B4443731
theorem B1974991 : Blo 1973435 1974991 := bstep (se 1 (by rfl) ⟨1481243, by rfl⟩ : syracuseStep 1974991 = 2962487) B2962487
theorem B2962493 : Blo 1973435 2962493 := bbase (se 3 (by rfl) ⟨555467, by rfl⟩ : syracuseStep 2962493 = 1110935) (by norm_num)
theorem B1974995 : Blo 1973435 1974995 := bstep (se 1 (by rfl) ⟨1481246, by rfl⟩ : syracuseStep 1974995 = 2962493) B2962493
theorem B4443749 : Blo 1973435 4443749 := bbase (se 4 (by rfl) ⟨416601, by rfl⟩ : syracuseStep 4443749 = 833203) (by norm_num)
theorem B2962499 : Blo 1973435 2962499 := bstep (se 1 (by rfl) ⟨2221874, by rfl⟩ : syracuseStep 2962499 = 4443749) B4443749
theorem B1974999 : Blo 1973435 1974999 := bstep (se 1 (by rfl) ⟨1481249, by rfl⟩ : syracuseStep 1974999 = 2962499) B2962499
theorem B4999229 : Blo 1973435 4999229 := bbase (se 3 (by rfl) ⟨937355, by rfl⟩ : syracuseStep 4999229 = 1874711) (by norm_num)
theorem B3332819 : Blo 1973435 3332819 := bstep (se 1 (by rfl) ⟨2499614, by rfl⟩ : syracuseStep 3332819 = 4999229) B4999229
theorem B2221879 : Blo 1973435 2221879 := bstep (se 1 (by rfl) ⟨1666409, by rfl⟩ : syracuseStep 2221879 = 3332819) B3332819
theorem B2962505 : Blo 1973435 2962505 := bstep (se 2 (by rfl) ⟨1110939, by rfl⟩ : syracuseStep 2962505 = 2221879) B2221879
theorem B1975003 : Blo 1973435 1975003 := bstep (se 1 (by rfl) ⟨1481252, by rfl⟩ : syracuseStep 1975003 = 2962505) B2962505
theorem B3749429 : Blo 1973435 3749429 := bbase (se 5 (by rfl) ⟨175754, by rfl⟩ : syracuseStep 3749429 = 351509) (by norm_num)
theorem B9998477 : Blo 1973435 9998477 := bstep (se 3 (by rfl) ⟨1874714, by rfl⟩ : syracuseStep 9998477 = 3749429) B3749429
theorem B6665651 : Blo 1973435 6665651 := bstep (se 1 (by rfl) ⟨4999238, by rfl⟩ : syracuseStep 6665651 = 9998477) B9998477
theorem B4443767 : Blo 1973435 4443767 := bstep (se 1 (by rfl) ⟨3332825, by rfl⟩ : syracuseStep 4443767 = 6665651) B6665651
theorem B2962511 : Blo 1973435 2962511 := bstep (se 1 (by rfl) ⟨2221883, by rfl⟩ : syracuseStep 2962511 = 4443767) B4443767
theorem B1975007 : Blo 1973435 1975007 := bstep (se 1 (by rfl) ⟨1481255, by rfl⟩ : syracuseStep 1975007 = 2962511) B2962511
theorem B2962517 : Blo 1973435 2962517 := bbase (se 8 (by rfl) ⟨17358, by rfl⟩ : syracuseStep 2962517 = 34717) (by norm_num)
theorem B1975011 : Blo 1973435 1975011 := bstep (se 1 (by rfl) ⟨1481258, by rfl⟩ : syracuseStep 1975011 = 2962517) B2962517
theorem B22803605 : Blo 1973435 22803605 := bbase (se 6 (by rfl) ⟨534459, by rfl⟩ : syracuseStep 22803605 = 1068919) (by norm_num)
theorem B15202403 : Blo 1973435 15202403 := bstep (se 1 (by rfl) ⟨11401802, by rfl⟩ : syracuseStep 15202403 = 22803605) B22803605
theorem B10134935 : Blo 1973435 10134935 := bstep (se 1 (by rfl) ⟨7601201, by rfl⟩ : syracuseStep 10134935 = 15202403) B15202403
theorem B6756623 : Blo 1973435 6756623 := bstep (se 1 (by rfl) ⟨5067467, by rfl⟩ : syracuseStep 6756623 = 10134935) B10134935
theorem B4504415 : Blo 1973435 4504415 := bstep (se 1 (by rfl) ⟨3378311, by rfl⟩ : syracuseStep 4504415 = 6756623) B6756623
theorem B48047093 : Blo 1973435 48047093 := bstep (se 5 (by rfl) ⟨2252207, by rfl⟩ : syracuseStep 48047093 = 4504415) B4504415
theorem B32031395 : Blo 1973435 32031395 := bstep (se 1 (by rfl) ⟨24023546, by rfl⟩ : syracuseStep 32031395 = 48047093) B48047093
theorem B21354263 : Blo 1973435 21354263 := bstep (se 1 (by rfl) ⟨16015697, by rfl⟩ : syracuseStep 21354263 = 32031395) B32031395
theorem B14236175 : Blo 1973435 14236175 := bstep (se 1 (by rfl) ⟨10677131, by rfl⟩ : syracuseStep 14236175 = 21354263) B21354263
theorem B9490783 : Blo 1973435 9490783 := bstep (se 1 (by rfl) ⟨7118087, by rfl⟩ : syracuseStep 9490783 = 14236175) B14236175
theorem B12654377 : Blo 1973435 12654377 := bstep (se 2 (by rfl) ⟨4745391, by rfl⟩ : syracuseStep 12654377 = 9490783) B9490783
theorem B8436251 : Blo 1973435 8436251 := bstep (se 1 (by rfl) ⟨6327188, by rfl⟩ : syracuseStep 8436251 = 12654377) B12654377
theorem B5624167 : Blo 1973435 5624167 := bstep (se 1 (by rfl) ⟨4218125, by rfl⟩ : syracuseStep 5624167 = 8436251) B8436251
theorem B7498889 : Blo 1973435 7498889 := bstep (se 2 (by rfl) ⟨2812083, by rfl⟩ : syracuseStep 7498889 = 5624167) B5624167
theorem B4999259 : Blo 1973435 4999259 := bstep (se 1 (by rfl) ⟨3749444, by rfl⟩ : syracuseStep 4999259 = 7498889) B7498889
theorem B3332839 : Blo 1973435 3332839 := bstep (se 1 (by rfl) ⟨2499629, by rfl⟩ : syracuseStep 3332839 = 4999259) B4999259
theorem B4443785 : Blo 1973435 4443785 := bstep (se 2 (by rfl) ⟨1666419, by rfl⟩ : syracuseStep 4443785 = 3332839) B3332839
theorem B2962523 : Blo 1973435 2962523 := bstep (se 1 (by rfl) ⟨2221892, by rfl⟩ : syracuseStep 2962523 = 4443785) B4443785
theorem B1975015 : Blo 1973435 1975015 := bstep (se 1 (by rfl) ⟨1481261, by rfl⟩ : syracuseStep 1975015 = 2962523) B2962523
theorem B2221897 : Blo 1973435 2221897 := bbase (se 2 (by rfl) ⟨833211, by rfl⟩ : syracuseStep 2221897 = 1666423) (by norm_num)
theorem B2962529 : Blo 1973435 2962529 := bstep (se 2 (by rfl) ⟨1110948, by rfl⟩ : syracuseStep 2962529 = 2221897) B2221897
theorem B1975019 : Blo 1973435 1975019 := bstep (se 1 (by rfl) ⟨1481264, by rfl⟩ : syracuseStep 1975019 = 2962529) B2962529
theorem B9620309 : Blo 1973435 9620309 := bbase (se 9 (by rfl) ⟨28184, by rfl⟩ : syracuseStep 9620309 = 56369) (by norm_num)
theorem B25654157 : Blo 1973435 25654157 := bstep (se 3 (by rfl) ⟨4810154, by rfl⟩ : syracuseStep 25654157 = 9620309) B9620309
theorem B17102771 : Blo 1973435 17102771 := bstep (se 1 (by rfl) ⟨12827078, by rfl⟩ : syracuseStep 17102771 = 25654157) B25654157
theorem B11401847 : Blo 1973435 11401847 := bstep (se 1 (by rfl) ⟨8551385, by rfl⟩ : syracuseStep 11401847 = 17102771) B17102771
theorem B7601231 : Blo 1973435 7601231 := bstep (se 1 (by rfl) ⟨5700923, by rfl⟩ : syracuseStep 7601231 = 11401847) B11401847
theorem B5067487 : Blo 1973435 5067487 := bstep (se 1 (by rfl) ⟨3800615, by rfl⟩ : syracuseStep 5067487 = 7601231) B7601231
theorem B27026597 : Blo 1973435 27026597 := bstep (se 4 (by rfl) ⟨2533743, by rfl⟩ : syracuseStep 27026597 = 5067487) B5067487
theorem B18017731 : Blo 1973435 18017731 := bstep (se 1 (by rfl) ⟨13513298, by rfl⟩ : syracuseStep 18017731 = 27026597) B27026597
theorem B24023641 : Blo 1973435 24023641 := bstep (se 2 (by rfl) ⟨9008865, by rfl⟩ : syracuseStep 24023641 = 18017731) B18017731
theorem B32031521 : Blo 1973435 32031521 := bstep (se 2 (by rfl) ⟨12011820, by rfl⟩ : syracuseStep 32031521 = 24023641) B24023641
theorem B21354347 : Blo 1973435 21354347 := bstep (se 1 (by rfl) ⟨16015760, by rfl⟩ : syracuseStep 21354347 = 32031521) B32031521
theorem B14236231 : Blo 1973435 14236231 := bstep (se 1 (by rfl) ⟨10677173, by rfl⟩ : syracuseStep 14236231 = 21354347) B21354347
theorem B18981641 : Blo 1973435 18981641 := bstep (se 2 (by rfl) ⟨7118115, by rfl⟩ : syracuseStep 18981641 = 14236231) B14236231
theorem B12654427 : Blo 1973435 12654427 := bstep (se 1 (by rfl) ⟨9490820, by rfl⟩ : syracuseStep 12654427 = 18981641) B18981641
theorem B16872569 : Blo 1973435 16872569 := bstep (se 2 (by rfl) ⟨6327213, by rfl⟩ : syracuseStep 16872569 = 12654427) B12654427
theorem B11248379 : Blo 1973435 11248379 := bstep (se 1 (by rfl) ⟨8436284, by rfl⟩ : syracuseStep 11248379 = 16872569) B16872569
theorem B7498919 : Blo 1973435 7498919 := bstep (se 1 (by rfl) ⟨5624189, by rfl⟩ : syracuseStep 7498919 = 11248379) B11248379
theorem B4999279 : Blo 1973435 4999279 := bstep (se 1 (by rfl) ⟨3749459, by rfl⟩ : syracuseStep 4999279 = 7498919) B7498919
theorem B6665705 : Blo 1973435 6665705 := bstep (se 2 (by rfl) ⟨2499639, by rfl⟩ : syracuseStep 6665705 = 4999279) B4999279
theorem B4443803 : Blo 1973435 4443803 := bstep (se 1 (by rfl) ⟨3332852, by rfl⟩ : syracuseStep 4443803 = 6665705) B6665705
theorem B2962535 : Blo 1973435 2962535 := bstep (se 1 (by rfl) ⟨2221901, by rfl⟩ : syracuseStep 2962535 = 4443803) B4443803
theorem B1975023 : Blo 1973435 1975023 := bstep (se 1 (by rfl) ⟨1481267, by rfl⟩ : syracuseStep 1975023 = 2962535) B2962535
theorem B2962541 : Blo 1973435 2962541 := bbase (se 3 (by rfl) ⟨555476, by rfl⟩ : syracuseStep 2962541 = 1110953) (by norm_num)
theorem B1975027 : Blo 1973435 1975027 := bstep (se 1 (by rfl) ⟨1481270, by rfl⟩ : syracuseStep 1975027 = 2962541) B2962541
theorem B4443821 : Blo 1973435 4443821 := bbase (se 3 (by rfl) ⟨833216, by rfl⟩ : syracuseStep 4443821 = 1666433) (by norm_num)
theorem B2962547 : Blo 1973435 2962547 := bstep (se 1 (by rfl) ⟨2221910, by rfl⟩ : syracuseStep 2962547 = 4443821) B4443821
theorem B1975031 : Blo 1973435 1975031 := bstep (se 1 (by rfl) ⟨1481273, by rfl⟩ : syracuseStep 1975031 = 2962547) B2962547
theorem B5411461 : Blo 1973435 5411461 := bbase (se 4 (by rfl) ⟨507324, by rfl⟩ : syracuseStep 5411461 = 1014649) (by norm_num)
theorem B7215281 : Blo 1973435 7215281 := bstep (se 2 (by rfl) ⟨2705730, by rfl⟩ : syracuseStep 7215281 = 5411461) B5411461
theorem B4810187 : Blo 1973435 4810187 := bstep (se 1 (by rfl) ⟨3607640, by rfl⟩ : syracuseStep 4810187 = 7215281) B7215281
theorem B12827165 : Blo 1973435 12827165 := bstep (se 3 (by rfl) ⟨2405093, by rfl⟩ : syracuseStep 12827165 = 4810187) B4810187
theorem B34205773 : Blo 1973435 34205773 := bstep (se 3 (by rfl) ⟨6413582, by rfl⟩ : syracuseStep 34205773 = 12827165) B12827165
theorem B45607697 : Blo 1973435 45607697 := bstep (se 2 (by rfl) ⟨17102886, by rfl⟩ : syracuseStep 45607697 = 34205773) B34205773
theorem B30405131 : Blo 1973435 30405131 := bstep (se 1 (by rfl) ⟨22803848, by rfl⟩ : syracuseStep 30405131 = 45607697) B45607697
theorem B20270087 : Blo 1973435 20270087 := bstep (se 1 (by rfl) ⟨15202565, by rfl⟩ : syracuseStep 20270087 = 30405131) B30405131
theorem B13513391 : Blo 1973435 13513391 := bstep (se 1 (by rfl) ⟨10135043, by rfl⟩ : syracuseStep 13513391 = 20270087) B20270087
theorem B9008927 : Blo 1973435 9008927 := bstep (se 1 (by rfl) ⟨6756695, by rfl⟩ : syracuseStep 9008927 = 13513391) B13513391
theorem B6005951 : Blo 1973435 6005951 := bstep (se 1 (by rfl) ⟨4504463, by rfl⟩ : syracuseStep 6005951 = 9008927) B9008927
theorem B4003967 : Blo 1973435 4003967 := bstep (se 1 (by rfl) ⟨3002975, by rfl⟩ : syracuseStep 4003967 = 6005951) B6005951
theorem B2669311 : Blo 1973435 2669311 := bstep (se 1 (by rfl) ⟨2001983, by rfl⟩ : syracuseStep 2669311 = 4003967) B4003967
theorem B3559081 : Blo 1973435 3559081 := bstep (se 2 (by rfl) ⟨1334655, by rfl⟩ : syracuseStep 3559081 = 2669311) B2669311
theorem B4745441 : Blo 1973435 4745441 := bstep (se 2 (by rfl) ⟨1779540, by rfl⟩ : syracuseStep 4745441 = 3559081) B3559081
theorem B3163627 : Blo 1973435 3163627 := bstep (se 1 (by rfl) ⟨2372720, by rfl⟩ : syracuseStep 3163627 = 4745441) B4745441
theorem B4218169 : Blo 1973435 4218169 := bstep (se 2 (by rfl) ⟨1581813, by rfl⟩ : syracuseStep 4218169 = 3163627) B3163627
theorem B5624225 : Blo 1973435 5624225 := bstep (se 2 (by rfl) ⟨2109084, by rfl⟩ : syracuseStep 5624225 = 4218169) B4218169
theorem B3749483 : Blo 1973435 3749483 := bstep (se 1 (by rfl) ⟨2812112, by rfl⟩ : syracuseStep 3749483 = 5624225) B5624225
theorem B2499655 : Blo 1973435 2499655 := bstep (se 1 (by rfl) ⟨1874741, by rfl⟩ : syracuseStep 2499655 = 3749483) B3749483
theorem B3332873 : Blo 1973435 3332873 := bstep (se 2 (by rfl) ⟨1249827, by rfl⟩ : syracuseStep 3332873 = 2499655) B2499655
theorem B2221915 : Blo 1973435 2221915 := bstep (se 1 (by rfl) ⟨1666436, by rfl⟩ : syracuseStep 2221915 = 3332873) B3332873
theorem B2962553 : Blo 1973435 2962553 := bstep (se 2 (by rfl) ⟨1110957, by rfl⟩ : syracuseStep 2962553 = 2221915) B2221915
theorem B1975035 : Blo 1973435 1975035 := bstep (se 1 (by rfl) ⟨1481276, by rfl⟩ : syracuseStep 1975035 = 2962553) B2962553
theorem B4504469 : Blo 1973435 4504469 := bbase (se 6 (by rfl) ⟨105573, by rfl⟩ : syracuseStep 4504469 = 211147) (by norm_num)
theorem B12011917 : Blo 1973435 12011917 := bstep (se 3 (by rfl) ⟨2252234, by rfl⟩ : syracuseStep 12011917 = 4504469) B4504469
theorem B16015889 : Blo 1973435 16015889 := bstep (se 2 (by rfl) ⟨6005958, by rfl⟩ : syracuseStep 16015889 = 12011917) B12011917
theorem B10677259 : Blo 1973435 10677259 := bstep (se 1 (by rfl) ⟨8007944, by rfl⟩ : syracuseStep 10677259 = 16015889) B16015889
theorem B14236345 : Blo 1973435 14236345 := bstep (se 2 (by rfl) ⟨5338629, by rfl⟩ : syracuseStep 14236345 = 10677259) B10677259
theorem B18981793 : Blo 1973435 18981793 := bstep (se 2 (by rfl) ⟨7118172, by rfl⟩ : syracuseStep 18981793 = 14236345) B14236345
theorem B25309057 : Blo 1973435 25309057 := bstep (se 2 (by rfl) ⟨9490896, by rfl⟩ : syracuseStep 25309057 = 18981793) B18981793
theorem B33745409 : Blo 1973435 33745409 := bstep (se 2 (by rfl) ⟨12654528, by rfl⟩ : syracuseStep 33745409 = 25309057) B25309057
theorem B22496939 : Blo 1973435 22496939 := bstep (se 1 (by rfl) ⟨16872704, by rfl⟩ : syracuseStep 22496939 = 33745409) B33745409
theorem B14997959 : Blo 1973435 14997959 := bstep (se 1 (by rfl) ⟨11248469, by rfl⟩ : syracuseStep 14997959 = 22496939) B22496939
theorem B9998639 : Blo 1973435 9998639 := bstep (se 1 (by rfl) ⟨7498979, by rfl⟩ : syracuseStep 9998639 = 14997959) B14997959
theorem B6665759 : Blo 1973435 6665759 := bstep (se 1 (by rfl) ⟨4999319, by rfl⟩ : syracuseStep 6665759 = 9998639) B9998639
theorem B4443839 : Blo 1973435 4443839 := bstep (se 1 (by rfl) ⟨3332879, by rfl⟩ : syracuseStep 4443839 = 6665759) B6665759
theorem B2962559 : Blo 1973435 2962559 := bstep (se 1 (by rfl) ⟨2221919, by rfl⟩ : syracuseStep 2962559 = 4443839) B4443839
theorem B1975039 : Blo 1973435 1975039 := bstep (se 1 (by rfl) ⟨1481279, by rfl⟩ : syracuseStep 1975039 = 2962559) B2962559
theorem B2962565 : Blo 1973435 2962565 := bbase (se 4 (by rfl) ⟨277740, by rfl⟩ : syracuseStep 2962565 = 555481) (by norm_num)
theorem B1975043 : Blo 1973435 1975043 := bstep (se 1 (by rfl) ⟨1481282, by rfl⟩ : syracuseStep 1975043 = 2962565) B2962565
theorem B3332893 : Blo 1973435 3332893 := bbase (se 3 (by rfl) ⟨624917, by rfl⟩ : syracuseStep 3332893 = 1249835) (by norm_num)
theorem B4443857 : Blo 1973435 4443857 := bstep (se 2 (by rfl) ⟨1666446, by rfl⟩ : syracuseStep 4443857 = 3332893) B3332893
theorem B2962571 : Blo 1973435 2962571 := bstep (se 1 (by rfl) ⟨2221928, by rfl⟩ : syracuseStep 2962571 = 4443857) B4443857
theorem B1975047 : Blo 1973435 1975047 := bstep (se 1 (by rfl) ⟨1481285, by rfl⟩ : syracuseStep 1975047 = 2962571) B2962571
theorem B2221933 : Blo 1973435 2221933 := bbase (se 3 (by rfl) ⟨416612, by rfl⟩ : syracuseStep 2221933 = 833225) (by norm_num)
theorem B2962577 : Blo 1973435 2962577 := bstep (se 2 (by rfl) ⟨1110966, by rfl⟩ : syracuseStep 2962577 = 2221933) B2221933
theorem B1975051 : Blo 1973435 1975051 := bstep (se 1 (by rfl) ⟨1481288, by rfl⟩ : syracuseStep 1975051 = 2962577) B2962577
theorem B6665813 : Blo 1973435 6665813 := bbase (se 8 (by rfl) ⟨39057, by rfl⟩ : syracuseStep 6665813 = 78115) (by norm_num)
theorem B4443875 : Blo 1973435 4443875 := bstep (se 1 (by rfl) ⟨3332906, by rfl⟩ : syracuseStep 4443875 = 6665813) B6665813
theorem B2962583 : Blo 1973435 2962583 := bstep (se 1 (by rfl) ⟨2221937, by rfl⟩ : syracuseStep 2962583 = 4443875) B4443875
theorem B1975055 : Blo 1973435 1975055 := bstep (se 1 (by rfl) ⟨1481291, by rfl⟩ : syracuseStep 1975055 = 2962583) B2962583
theorem B2962589 : Blo 1973435 2962589 := bbase (se 3 (by rfl) ⟨555485, by rfl⟩ : syracuseStep 2962589 = 1110971) (by norm_num)
theorem B1975059 : Blo 1973435 1975059 := bstep (se 1 (by rfl) ⟨1481294, by rfl⟩ : syracuseStep 1975059 = 2962589) B2962589
theorem B4443893 : Blo 1973435 4443893 := bbase (se 5 (by rfl) ⟨208307, by rfl⟩ : syracuseStep 4443893 = 416615) (by norm_num)
theorem B2962595 : Blo 1973435 2962595 := bstep (se 1 (by rfl) ⟨2221946, by rfl⟩ : syracuseStep 2962595 = 4443893) B4443893
theorem B1975063 : Blo 1973435 1975063 := bstep (se 1 (by rfl) ⟨1481297, by rfl⟩ : syracuseStep 1975063 = 2962595) B2962595
theorem B10135205 : Blo 1973435 10135205 := bbase (se 4 (by rfl) ⟨950175, by rfl⟩ : syracuseStep 10135205 = 1900351) (by norm_num)
theorem B6756803 : Blo 1973435 6756803 := bstep (se 1 (by rfl) ⟨5067602, by rfl⟩ : syracuseStep 6756803 = 10135205) B10135205
theorem B4504535 : Blo 1973435 4504535 := bstep (se 1 (by rfl) ⟨3378401, by rfl⟩ : syracuseStep 4504535 = 6756803) B6756803
theorem B3003023 : Blo 1973435 3003023 := bstep (se 1 (by rfl) ⟨2252267, by rfl⟩ : syracuseStep 3003023 = 4504535) B4504535
theorem B2002015 : Blo 1973435 2002015 := bstep (se 1 (by rfl) ⟨1501511, by rfl⟩ : syracuseStep 2002015 = 3003023) B3003023
theorem B10677413 : Blo 1973435 10677413 := bstep (se 4 (by rfl) ⟨1001007, by rfl⟩ : syracuseStep 10677413 = 2002015) B2002015
theorem B7118275 : Blo 1973435 7118275 := bstep (se 1 (by rfl) ⟨5338706, by rfl⟩ : syracuseStep 7118275 = 10677413) B10677413
theorem B9491033 : Blo 1973435 9491033 := bstep (se 2 (by rfl) ⟨3559137, by rfl⟩ : syracuseStep 9491033 = 7118275) B7118275
theorem B25309421 : Blo 1973435 25309421 := bstep (se 3 (by rfl) ⟨4745516, by rfl⟩ : syracuseStep 25309421 = 9491033) B9491033
theorem B16872947 : Blo 1973435 16872947 := bstep (se 1 (by rfl) ⟨12654710, by rfl⟩ : syracuseStep 16872947 = 25309421) B25309421
theorem B11248631 : Blo 1973435 11248631 := bstep (se 1 (by rfl) ⟨8436473, by rfl⟩ : syracuseStep 11248631 = 16872947) B16872947
theorem B7499087 : Blo 1973435 7499087 := bstep (se 1 (by rfl) ⟨5624315, by rfl⟩ : syracuseStep 7499087 = 11248631) B11248631
theorem B4999391 : Blo 1973435 4999391 := bstep (se 1 (by rfl) ⟨3749543, by rfl⟩ : syracuseStep 4999391 = 7499087) B7499087
theorem B3332927 : Blo 1973435 3332927 := bstep (se 1 (by rfl) ⟨2499695, by rfl⟩ : syracuseStep 3332927 = 4999391) B4999391
theorem B2221951 : Blo 1973435 2221951 := bstep (se 1 (by rfl) ⟨1666463, by rfl⟩ : syracuseStep 2221951 = 3332927) B3332927
theorem B2962601 : Blo 1973435 2962601 := bstep (se 2 (by rfl) ⟨1110975, by rfl⟩ : syracuseStep 2962601 = 2221951) B2221951
theorem B1975067 : Blo 1973435 1975067 := bstep (se 1 (by rfl) ⟨1481300, by rfl⟩ : syracuseStep 1975067 = 2962601) B2962601
theorem B4218245 : Blo 1973435 4218245 := bbase (se 4 (by rfl) ⟨395460, by rfl⟩ : syracuseStep 4218245 = 790921) (by norm_num)
theorem B2812163 : Blo 1973435 2812163 := bstep (se 1 (by rfl) ⟨2109122, by rfl⟩ : syracuseStep 2812163 = 4218245) B4218245
theorem B7499101 : Blo 1973435 7499101 := bstep (se 3 (by rfl) ⟨1406081, by rfl⟩ : syracuseStep 7499101 = 2812163) B2812163
theorem B9998801 : Blo 1973435 9998801 := bstep (se 2 (by rfl) ⟨3749550, by rfl⟩ : syracuseStep 9998801 = 7499101) B7499101
theorem B6665867 : Blo 1973435 6665867 := bstep (se 1 (by rfl) ⟨4999400, by rfl⟩ : syracuseStep 6665867 = 9998801) B9998801
theorem B4443911 : Blo 1973435 4443911 := bstep (se 1 (by rfl) ⟨3332933, by rfl⟩ : syracuseStep 4443911 = 6665867) B6665867
theorem B2962607 : Blo 1973435 2962607 := bstep (se 1 (by rfl) ⟨2221955, by rfl⟩ : syracuseStep 2962607 = 4443911) B4443911
theorem B1975071 : Blo 1973435 1975071 := bstep (se 1 (by rfl) ⟨1481303, by rfl⟩ : syracuseStep 1975071 = 2962607) B2962607
theorem B2962613 : Blo 1973435 2962613 := bbase (se 5 (by rfl) ⟨138872, by rfl⟩ : syracuseStep 2962613 = 277745) (by norm_num)
theorem B1975075 : Blo 1973435 1975075 := bstep (se 1 (by rfl) ⟨1481306, by rfl⟩ : syracuseStep 1975075 = 2962613) B2962613
theorem B4999421 : Blo 1973435 4999421 := bbase (se 3 (by rfl) ⟨937391, by rfl⟩ : syracuseStep 4999421 = 1874783) (by norm_num)
theorem B3332947 : Blo 1973435 3332947 := bstep (se 1 (by rfl) ⟨2499710, by rfl⟩ : syracuseStep 3332947 = 4999421) B4999421
theorem B4443929 : Blo 1973435 4443929 := bstep (se 2 (by rfl) ⟨1666473, by rfl⟩ : syracuseStep 4443929 = 3332947) B3332947
theorem B2962619 : Blo 1973435 2962619 := bstep (se 1 (by rfl) ⟨2221964, by rfl⟩ : syracuseStep 2962619 = 4443929) B4443929
theorem B1975079 : Blo 1973435 1975079 := bstep (se 1 (by rfl) ⟨1481309, by rfl⟩ : syracuseStep 1975079 = 2962619) B2962619
theorem B2221969 : Blo 1973435 2221969 := bbase (se 2 (by rfl) ⟨833238, by rfl⟩ : syracuseStep 2221969 = 1666477) (by norm_num)
theorem B2962625 : Blo 1973435 2962625 := bstep (se 2 (by rfl) ⟨1110984, by rfl⟩ : syracuseStep 2962625 = 2221969) B2221969
theorem B1975083 : Blo 1973435 1975083 := bstep (se 1 (by rfl) ⟨1481312, by rfl⟩ : syracuseStep 1975083 = 2962625) B2962625
theorem B3749581 : Blo 1973435 3749581 := bbase (se 3 (by rfl) ⟨703046, by rfl⟩ : syracuseStep 3749581 = 1406093) (by norm_num)
theorem B4999441 : Blo 1973435 4999441 := bstep (se 2 (by rfl) ⟨1874790, by rfl⟩ : syracuseStep 4999441 = 3749581) B3749581
theorem B6665921 : Blo 1973435 6665921 := bstep (se 2 (by rfl) ⟨2499720, by rfl⟩ : syracuseStep 6665921 = 4999441) B4999441
theorem B4443947 : Blo 1973435 4443947 := bstep (se 1 (by rfl) ⟨3332960, by rfl⟩ : syracuseStep 4443947 = 6665921) B6665921
theorem B2962631 : Blo 1973435 2962631 := bstep (se 1 (by rfl) ⟨2221973, by rfl⟩ : syracuseStep 2962631 = 4443947) B4443947
theorem B1975087 : Blo 1973435 1975087 := bstep (se 1 (by rfl) ⟨1481315, by rfl⟩ : syracuseStep 1975087 = 2962631) B2962631
theorem B2962637 : Blo 1973435 2962637 := bbase (se 3 (by rfl) ⟨555494, by rfl⟩ : syracuseStep 2962637 = 1110989) (by norm_num)
theorem B1975091 : Blo 1973435 1975091 := bstep (se 1 (by rfl) ⟨1481318, by rfl⟩ : syracuseStep 1975091 = 2962637) B2962637
theorem B4443965 : Blo 1973435 4443965 := bbase (se 3 (by rfl) ⟨833243, by rfl⟩ : syracuseStep 4443965 = 1666487) (by norm_num)
theorem B2962643 : Blo 1973435 2962643 := bstep (se 1 (by rfl) ⟨2221982, by rfl⟩ : syracuseStep 2962643 = 4443965) B4443965
theorem B1975095 : Blo 1973435 1975095 := bstep (se 1 (by rfl) ⟨1481321, by rfl⟩ : syracuseStep 1975095 = 2962643) B2962643
theorem B3332981 : Blo 1973435 3332981 := bbase (se 5 (by rfl) ⟨156233, by rfl⟩ : syracuseStep 3332981 = 312467) (by norm_num)
theorem B2221987 : Blo 1973435 2221987 := bstep (se 1 (by rfl) ⟨1666490, by rfl⟩ : syracuseStep 2221987 = 3332981) B3332981
theorem B2962649 : Blo 1973435 2962649 := bstep (se 2 (by rfl) ⟨1110993, by rfl⟩ : syracuseStep 2962649 = 2221987) B2221987
theorem B1975099 : Blo 1973435 1975099 := bstep (se 1 (by rfl) ⟨1481324, by rfl⟩ : syracuseStep 1975099 = 2962649) B2962649
theorem B7118405 : Blo 1973435 7118405 := bbase (se 4 (by rfl) ⟨667350, by rfl⟩ : syracuseStep 7118405 = 1334701) (by norm_num)
theorem B4745603 : Blo 1973435 4745603 := bstep (se 1 (by rfl) ⟨3559202, by rfl⟩ : syracuseStep 4745603 = 7118405) B7118405
theorem B3163735 : Blo 1973435 3163735 := bstep (se 1 (by rfl) ⟨2372801, by rfl⟩ : syracuseStep 3163735 = 4745603) B4745603
theorem B4218313 : Blo 1973435 4218313 := bstep (se 2 (by rfl) ⟨1581867, by rfl⟩ : syracuseStep 4218313 = 3163735) B3163735
theorem B5624417 : Blo 1973435 5624417 := bstep (se 2 (by rfl) ⟨2109156, by rfl⟩ : syracuseStep 5624417 = 4218313) B4218313
theorem B14998445 : Blo 1973435 14998445 := bstep (se 3 (by rfl) ⟨2812208, by rfl⟩ : syracuseStep 14998445 = 5624417) B5624417
theorem B9998963 : Blo 1973435 9998963 := bstep (se 1 (by rfl) ⟨7499222, by rfl⟩ : syracuseStep 9998963 = 14998445) B14998445
theorem B6665975 : Blo 1973435 6665975 := bstep (se 1 (by rfl) ⟨4999481, by rfl⟩ : syracuseStep 6665975 = 9998963) B9998963
theorem B4443983 : Blo 1973435 4443983 := bstep (se 1 (by rfl) ⟨3332987, by rfl⟩ : syracuseStep 4443983 = 6665975) B6665975
theorem B2962655 : Blo 1973435 2962655 := bstep (se 1 (by rfl) ⟨2221991, by rfl⟩ : syracuseStep 2962655 = 4443983) B4443983
theorem B1975103 : Blo 1973435 1975103 := bstep (se 1 (by rfl) ⟨1481327, by rfl⟩ : syracuseStep 1975103 = 2962655) B2962655
theorem B2962661 : Blo 1973435 2962661 := bbase (se 4 (by rfl) ⟨277749, by rfl⟩ : syracuseStep 2962661 = 555499) (by norm_num)
theorem B1975107 : Blo 1973435 1975107 := bstep (se 1 (by rfl) ⟨1481330, by rfl⟩ : syracuseStep 1975107 = 2962661) B2962661
theorem B10677653 : Blo 1973435 10677653 := bbase (se 6 (by rfl) ⟨250257, by rfl⟩ : syracuseStep 10677653 = 500515) (by norm_num)
theorem B7118435 : Blo 1973435 7118435 := bstep (se 1 (by rfl) ⟨5338826, by rfl⟩ : syracuseStep 7118435 = 10677653) B10677653
theorem B4745623 : Blo 1973435 4745623 := bstep (se 1 (by rfl) ⟨3559217, by rfl⟩ : syracuseStep 4745623 = 7118435) B7118435
theorem B6327497 : Blo 1973435 6327497 := bstep (se 2 (by rfl) ⟨2372811, by rfl⟩ : syracuseStep 6327497 = 4745623) B4745623
theorem B4218331 : Blo 1973435 4218331 := bstep (se 1 (by rfl) ⟨3163748, by rfl⟩ : syracuseStep 4218331 = 6327497) B6327497
theorem B5624441 : Blo 1973435 5624441 := bstep (se 2 (by rfl) ⟨2109165, by rfl⟩ : syracuseStep 5624441 = 4218331) B4218331
theorem B3749627 : Blo 1973435 3749627 := bstep (se 1 (by rfl) ⟨2812220, by rfl⟩ : syracuseStep 3749627 = 5624441) B5624441
theorem B2499751 : Blo 1973435 2499751 := bstep (se 1 (by rfl) ⟨1874813, by rfl⟩ : syracuseStep 2499751 = 3749627) B3749627
theorem B3333001 : Blo 1973435 3333001 := bstep (se 2 (by rfl) ⟨1249875, by rfl⟩ : syracuseStep 3333001 = 2499751) B2499751
theorem B4444001 : Blo 1973435 4444001 := bstep (se 2 (by rfl) ⟨1666500, by rfl⟩ : syracuseStep 4444001 = 3333001) B3333001
theorem B2962667 : Blo 1973435 2962667 := bstep (se 1 (by rfl) ⟨2222000, by rfl⟩ : syracuseStep 2962667 = 4444001) B4444001
theorem B1975111 : Blo 1973435 1975111 := bstep (se 1 (by rfl) ⟨1481333, by rfl⟩ : syracuseStep 1975111 = 2962667) B2962667
theorem B2222005 : Blo 1973435 2222005 := bbase (se 5 (by rfl) ⟨104156, by rfl⟩ : syracuseStep 2222005 = 208313) (by norm_num)
theorem B2962673 : Blo 1973435 2962673 := bstep (se 2 (by rfl) ⟨1111002, by rfl⟩ : syracuseStep 2962673 = 2222005) B2222005
theorem B1975115 : Blo 1973435 1975115 := bstep (se 1 (by rfl) ⟨1481336, by rfl⟩ : syracuseStep 1975115 = 2962673) B2962673
theorem B2499761 : Blo 1973435 2499761 := bbase (se 2 (by rfl) ⟨937410, by rfl⟩ : syracuseStep 2499761 = 1874821) (by norm_num)
theorem B6666029 : Blo 1973435 6666029 := bstep (se 3 (by rfl) ⟨1249880, by rfl⟩ : syracuseStep 6666029 = 2499761) B2499761
theorem B4444019 : Blo 1973435 4444019 := bstep (se 1 (by rfl) ⟨3333014, by rfl⟩ : syracuseStep 4444019 = 6666029) B6666029
theorem B2962679 : Blo 1973435 2962679 := bstep (se 1 (by rfl) ⟨2222009, by rfl⟩ : syracuseStep 2962679 = 4444019) B4444019
theorem B1975119 : Blo 1973435 1975119 := bstep (se 1 (by rfl) ⟨1481339, by rfl⟩ : syracuseStep 1975119 = 2962679) B2962679
theorem B2962685 : Blo 1973435 2962685 := bbase (se 3 (by rfl) ⟨555503, by rfl⟩ : syracuseStep 2962685 = 1111007) (by norm_num)
theorem B1975123 : Blo 1973435 1975123 := bstep (se 1 (by rfl) ⟨1481342, by rfl⟩ : syracuseStep 1975123 = 2962685) B2962685
theorem B4444037 : Blo 1973435 4444037 := bbase (se 4 (by rfl) ⟨416628, by rfl⟩ : syracuseStep 4444037 = 833257) (by norm_num)
theorem B2962691 : Blo 1973435 2962691 := bstep (se 1 (by rfl) ⟨2222018, by rfl⟩ : syracuseStep 2962691 = 4444037) B4444037
theorem B1975127 : Blo 1973435 1975127 := bstep (se 1 (by rfl) ⟨1481345, by rfl⟩ : syracuseStep 1975127 = 2962691) B2962691
theorem B3163781 : Blo 1973435 3163781 := bbase (se 4 (by rfl) ⟨296604, by rfl⟩ : syracuseStep 3163781 = 593209) (by norm_num)
theorem B2109187 : Blo 1973435 2109187 := bstep (se 1 (by rfl) ⟨1581890, by rfl⟩ : syracuseStep 2109187 = 3163781) B3163781
theorem B2812249 : Blo 1973435 2812249 := bstep (se 2 (by rfl) ⟨1054593, by rfl⟩ : syracuseStep 2812249 = 2109187) B2109187
theorem B3749665 : Blo 1973435 3749665 := bstep (se 2 (by rfl) ⟨1406124, by rfl⟩ : syracuseStep 3749665 = 2812249) B2812249
theorem B4999553 : Blo 1973435 4999553 := bstep (se 2 (by rfl) ⟨1874832, by rfl⟩ : syracuseStep 4999553 = 3749665) B3749665
theorem B3333035 : Blo 1973435 3333035 := bstep (se 1 (by rfl) ⟨2499776, by rfl⟩ : syracuseStep 3333035 = 4999553) B4999553
theorem B2222023 : Blo 1973435 2222023 := bstep (se 1 (by rfl) ⟨1666517, by rfl⟩ : syracuseStep 2222023 = 3333035) B3333035
theorem B2962697 : Blo 1973435 2962697 := bstep (se 2 (by rfl) ⟨1111011, by rfl⟩ : syracuseStep 2962697 = 2222023) B2222023
theorem B1975131 : Blo 1973435 1975131 := bstep (se 1 (by rfl) ⟨1481348, by rfl⟩ : syracuseStep 1975131 = 2962697) B2962697
theorem B9999125 : Blo 1973435 9999125 := bbase (se 6 (by rfl) ⟨234354, by rfl⟩ : syracuseStep 9999125 = 468709) (by norm_num)
theorem B6666083 : Blo 1973435 6666083 := bstep (se 1 (by rfl) ⟨4999562, by rfl⟩ : syracuseStep 6666083 = 9999125) B9999125
theorem B4444055 : Blo 1973435 4444055 := bstep (se 1 (by rfl) ⟨3333041, by rfl⟩ : syracuseStep 4444055 = 6666083) B6666083
theorem B2962703 : Blo 1973435 2962703 := bstep (se 1 (by rfl) ⟨2222027, by rfl⟩ : syracuseStep 2962703 = 4444055) B4444055
theorem B1975135 : Blo 1973435 1975135 := bstep (se 1 (by rfl) ⟨1481351, by rfl⟩ : syracuseStep 1975135 = 2962703) B2962703
theorem B2962709 : Blo 1973435 2962709 := bbase (se 6 (by rfl) ⟨69438, by rfl⟩ : syracuseStep 2962709 = 138877) (by norm_num)
theorem B1975139 : Blo 1973435 1975139 := bstep (se 1 (by rfl) ⟨1481354, by rfl⟩ : syracuseStep 1975139 = 2962709) B2962709
theorem B3206965 : Blo 1973435 3206965 := bbase (se 5 (by rfl) ⟨150326, by rfl⟩ : syracuseStep 3206965 = 300653) (by norm_num)
theorem B4275953 : Blo 1973435 4275953 := bstep (se 2 (by rfl) ⟨1603482, by rfl⟩ : syracuseStep 4275953 = 3206965) B3206965
theorem B2850635 : Blo 1973435 2850635 := bstep (se 1 (by rfl) ⟨2137976, by rfl⟩ : syracuseStep 2850635 = 4275953) B4275953
theorem B7601693 : Blo 1973435 7601693 := bstep (se 3 (by rfl) ⟨1425317, by rfl⟩ : syracuseStep 7601693 = 2850635) B2850635
theorem B20271181 : Blo 1973435 20271181 := bstep (se 3 (by rfl) ⟨3800846, by rfl⟩ : syracuseStep 20271181 = 7601693) B7601693
theorem B27028241 : Blo 1973435 27028241 := bstep (se 2 (by rfl) ⟨10135590, by rfl⟩ : syracuseStep 27028241 = 20271181) B20271181
theorem B18018827 : Blo 1973435 18018827 := bstep (se 1 (by rfl) ⟨13514120, by rfl⟩ : syracuseStep 18018827 = 27028241) B27028241
theorem B12012551 : Blo 1973435 12012551 := bstep (se 1 (by rfl) ⟨9009413, by rfl⟩ : syracuseStep 12012551 = 18018827) B18018827
theorem B8008367 : Blo 1973435 8008367 := bstep (se 1 (by rfl) ⟨6006275, by rfl⟩ : syracuseStep 8008367 = 12012551) B12012551
theorem B21355645 : Blo 1973435 21355645 := bstep (se 3 (by rfl) ⟨4004183, by rfl⟩ : syracuseStep 21355645 = 8008367) B8008367
theorem B28474193 : Blo 1973435 28474193 := bstep (se 2 (by rfl) ⟨10677822, by rfl⟩ : syracuseStep 28474193 = 21355645) B21355645
theorem B18982795 : Blo 1973435 18982795 := bstep (se 1 (by rfl) ⟨14237096, by rfl⟩ : syracuseStep 18982795 = 28474193) B28474193
theorem B25310393 : Blo 1973435 25310393 := bstep (se 2 (by rfl) ⟨9491397, by rfl⟩ : syracuseStep 25310393 = 18982795) B18982795
theorem B16873595 : Blo 1973435 16873595 := bstep (se 1 (by rfl) ⟨12655196, by rfl⟩ : syracuseStep 16873595 = 25310393) B25310393
theorem B11249063 : Blo 1973435 11249063 := bstep (se 1 (by rfl) ⟨8436797, by rfl⟩ : syracuseStep 11249063 = 16873595) B16873595
theorem B7499375 : Blo 1973435 7499375 := bstep (se 1 (by rfl) ⟨5624531, by rfl⟩ : syracuseStep 7499375 = 11249063) B11249063
theorem B4999583 : Blo 1973435 4999583 := bstep (se 1 (by rfl) ⟨3749687, by rfl⟩ : syracuseStep 4999583 = 7499375) B7499375
theorem B3333055 : Blo 1973435 3333055 := bstep (se 1 (by rfl) ⟨2499791, by rfl⟩ : syracuseStep 3333055 = 4999583) B4999583
theorem B4444073 : Blo 1973435 4444073 := bstep (se 2 (by rfl) ⟨1666527, by rfl⟩ : syracuseStep 4444073 = 3333055) B3333055
theorem B2962715 : Blo 1973435 2962715 := bstep (se 1 (by rfl) ⟨2222036, by rfl⟩ : syracuseStep 2962715 = 4444073) B4444073
theorem B1975143 : Blo 1973435 1975143 := bstep (se 1 (by rfl) ⟨1481357, by rfl⟩ : syracuseStep 1975143 = 2962715) B2962715
theorem B2222041 : Blo 1973435 2222041 := bbase (se 2 (by rfl) ⟨833265, by rfl⟩ : syracuseStep 2222041 = 1666531) (by norm_num)
theorem B2962721 : Blo 1973435 2962721 := bstep (se 2 (by rfl) ⟨1111020, by rfl⟩ : syracuseStep 2962721 = 2222041) B2222041
theorem B1975147 : Blo 1973435 1975147 := bstep (se 1 (by rfl) ⟨1481360, by rfl⟩ : syracuseStep 1975147 = 2962721) B2962721
theorem B2812277 : Blo 1973435 2812277 := bbase (se 5 (by rfl) ⟨131825, by rfl⟩ : syracuseStep 2812277 = 263651) (by norm_num)
theorem B7499405 : Blo 1973435 7499405 := bstep (se 3 (by rfl) ⟨1406138, by rfl⟩ : syracuseStep 7499405 = 2812277) B2812277
theorem B4999603 : Blo 1973435 4999603 := bstep (se 1 (by rfl) ⟨3749702, by rfl⟩ : syracuseStep 4999603 = 7499405) B7499405
theorem B6666137 : Blo 1973435 6666137 := bstep (se 2 (by rfl) ⟨2499801, by rfl⟩ : syracuseStep 6666137 = 4999603) B4999603
theorem B4444091 : Blo 1973435 4444091 := bstep (se 1 (by rfl) ⟨3333068, by rfl⟩ : syracuseStep 4444091 = 6666137) B6666137
theorem B2962727 : Blo 1973435 2962727 := bstep (se 1 (by rfl) ⟨2222045, by rfl⟩ : syracuseStep 2962727 = 4444091) B4444091
theorem B1975151 : Blo 1973435 1975151 := bstep (se 1 (by rfl) ⟨1481363, by rfl⟩ : syracuseStep 1975151 = 2962727) B2962727
theorem B2962733 : Blo 1973435 2962733 := bbase (se 3 (by rfl) ⟨555512, by rfl⟩ : syracuseStep 2962733 = 1111025) (by norm_num)
theorem B1975155 : Blo 1973435 1975155 := bstep (se 1 (by rfl) ⟨1481366, by rfl⟩ : syracuseStep 1975155 = 2962733) B2962733
theorem B4444109 : Blo 1973435 4444109 := bbase (se 3 (by rfl) ⟨833270, by rfl⟩ : syracuseStep 4444109 = 1666541) (by norm_num)
theorem B2962739 : Blo 1973435 2962739 := bstep (se 1 (by rfl) ⟨2222054, by rfl⟩ : syracuseStep 2962739 = 4444109) B4444109
theorem B1975159 : Blo 1973435 1975159 := bstep (se 1 (by rfl) ⟨1481369, by rfl⟩ : syracuseStep 1975159 = 2962739) B2962739
theorem B2499817 : Blo 1973435 2499817 := bbase (se 2 (by rfl) ⟨937431, by rfl⟩ : syracuseStep 2499817 = 1874863) (by norm_num)
theorem B3333089 : Blo 1973435 3333089 := bstep (se 2 (by rfl) ⟨1249908, by rfl⟩ : syracuseStep 3333089 = 2499817) B2499817
theorem B2222059 : Blo 1973435 2222059 := bstep (se 1 (by rfl) ⟨1666544, by rfl⟩ : syracuseStep 2222059 = 3333089) B3333089
theorem B2962745 : Blo 1973435 2962745 := bstep (se 2 (by rfl) ⟨1111029, by rfl⟩ : syracuseStep 2962745 = 2222059) B2222059
theorem B1975163 : Blo 1973435 1975163 := bstep (se 1 (by rfl) ⟨1481372, by rfl⟩ : syracuseStep 1975163 = 2962745) B2962745
theorem B12655349 : Blo 1973435 12655349 := bbase (se 5 (by rfl) ⟨593219, by rfl⟩ : syracuseStep 12655349 = 1186439) (by norm_num)
theorem B8436899 : Blo 1973435 8436899 := bstep (se 1 (by rfl) ⟨6327674, by rfl⟩ : syracuseStep 8436899 = 12655349) B12655349
theorem B22498397 : Blo 1973435 22498397 := bstep (se 3 (by rfl) ⟨4218449, by rfl⟩ : syracuseStep 22498397 = 8436899) B8436899
theorem B14998931 : Blo 1973435 14998931 := bstep (se 1 (by rfl) ⟨11249198, by rfl⟩ : syracuseStep 14998931 = 22498397) B22498397
theorem B9999287 : Blo 1973435 9999287 := bstep (se 1 (by rfl) ⟨7499465, by rfl⟩ : syracuseStep 9999287 = 14998931) B14998931
theorem B6666191 : Blo 1973435 6666191 := bstep (se 1 (by rfl) ⟨4999643, by rfl⟩ : syracuseStep 6666191 = 9999287) B9999287
theorem B4444127 : Blo 1973435 4444127 := bstep (se 1 (by rfl) ⟨3333095, by rfl⟩ : syracuseStep 4444127 = 6666191) B6666191
theorem B2962751 : Blo 1973435 2962751 := bstep (se 1 (by rfl) ⟨2222063, by rfl⟩ : syracuseStep 2962751 = 4444127) B4444127
theorem B1975167 : Blo 1973435 1975167 := bstep (se 1 (by rfl) ⟨1481375, by rfl⟩ : syracuseStep 1975167 = 2962751) B2962751
theorem B2962757 : Blo 1973435 2962757 := bbase (se 4 (by rfl) ⟨277758, by rfl⟩ : syracuseStep 2962757 = 555517) (by norm_num)
theorem B1975171 : Blo 1973435 1975171 := bstep (se 1 (by rfl) ⟨1481378, by rfl⟩ : syracuseStep 1975171 = 2962757) B2962757
theorem B3333109 : Blo 1973435 3333109 := bbase (se 5 (by rfl) ⟨156239, by rfl⟩ : syracuseStep 3333109 = 312479) (by norm_num)
theorem B4444145 : Blo 1973435 4444145 := bstep (se 2 (by rfl) ⟨1666554, by rfl⟩ : syracuseStep 4444145 = 3333109) B3333109
theorem B2962763 : Blo 1973435 2962763 := bstep (se 1 (by rfl) ⟨2222072, by rfl⟩ : syracuseStep 2962763 = 4444145) B4444145
theorem B1975175 : Blo 1973435 1975175 := bstep (se 1 (by rfl) ⟨1481381, by rfl⟩ : syracuseStep 1975175 = 2962763) B2962763
theorem B2222077 : Blo 1973435 2222077 := bbase (se 3 (by rfl) ⟨416639, by rfl⟩ : syracuseStep 2222077 = 833279) (by norm_num)
theorem B2962769 : Blo 1973435 2962769 := bstep (se 2 (by rfl) ⟨1111038, by rfl⟩ : syracuseStep 2962769 = 2222077) B2222077
theorem B1975179 : Blo 1973435 1975179 := bstep (se 1 (by rfl) ⟨1481384, by rfl⟩ : syracuseStep 1975179 = 2962769) B2962769
theorem B6666245 : Blo 1973435 6666245 := bbase (se 4 (by rfl) ⟨624960, by rfl⟩ : syracuseStep 6666245 = 1249921) (by norm_num)
theorem B4444163 : Blo 1973435 4444163 := bstep (se 1 (by rfl) ⟨3333122, by rfl⟩ : syracuseStep 4444163 = 6666245) B6666245
theorem B2962775 : Blo 1973435 2962775 := bstep (se 1 (by rfl) ⟨2222081, by rfl⟩ : syracuseStep 2962775 = 4444163) B4444163
theorem B1975183 : Blo 1973435 1975183 := bstep (se 1 (by rfl) ⟨1481387, by rfl⟩ : syracuseStep 1975183 = 2962775) B2962775
theorem B2962781 : Blo 1973435 2962781 := bbase (se 3 (by rfl) ⟨555521, by rfl⟩ : syracuseStep 2962781 = 1111043) (by norm_num)
theorem B1975187 : Blo 1973435 1975187 := bstep (se 1 (by rfl) ⟨1481390, by rfl⟩ : syracuseStep 1975187 = 2962781) B2962781
theorem B4444181 : Blo 1973435 4444181 := bbase (se 6 (by rfl) ⟨104160, by rfl⟩ : syracuseStep 4444181 = 208321) (by norm_num)
theorem B2962787 : Blo 1973435 2962787 := bstep (se 1 (by rfl) ⟨2222090, by rfl⟩ : syracuseStep 2962787 = 4444181) B4444181
theorem B1975191 : Blo 1973435 1975191 := bstep (se 1 (by rfl) ⟨1481393, by rfl⟩ : syracuseStep 1975191 = 2962787) B2962787
theorem B7499573 : Blo 1973435 7499573 := bbase (se 5 (by rfl) ⟨351542, by rfl⟩ : syracuseStep 7499573 = 703085) (by norm_num)
theorem B4999715 : Blo 1973435 4999715 := bstep (se 1 (by rfl) ⟨3749786, by rfl⟩ : syracuseStep 4999715 = 7499573) B7499573
theorem B3333143 : Blo 1973435 3333143 := bstep (se 1 (by rfl) ⟨2499857, by rfl⟩ : syracuseStep 3333143 = 4999715) B4999715
theorem B2222095 : Blo 1973435 2222095 := bstep (se 1 (by rfl) ⟨1666571, by rfl⟩ : syracuseStep 2222095 = 3333143) B3333143
theorem B2962793 : Blo 1973435 2962793 := bstep (se 2 (by rfl) ⟨1111047, by rfl⟩ : syracuseStep 2962793 = 2222095) B2222095
theorem B1975195 : Blo 1973435 1975195 := bstep (se 1 (by rfl) ⟨1481396, by rfl⟩ : syracuseStep 1975195 = 2962793) B2962793
theorem B2372917 : Blo 1973435 2372917 := bbase (se 5 (by rfl) ⟨111230, by rfl⟩ : syracuseStep 2372917 = 222461) (by norm_num)
theorem B3163889 : Blo 1973435 3163889 := bstep (se 2 (by rfl) ⟨1186458, by rfl⟩ : syracuseStep 3163889 = 2372917) B2372917
theorem B2109259 : Blo 1973435 2109259 := bstep (se 1 (by rfl) ⟨1581944, by rfl⟩ : syracuseStep 2109259 = 3163889) B3163889
theorem B11249381 : Blo 1973435 11249381 := bstep (se 4 (by rfl) ⟨1054629, by rfl⟩ : syracuseStep 11249381 = 2109259) B2109259
theorem B7499587 : Blo 1973435 7499587 := bstep (se 1 (by rfl) ⟨5624690, by rfl⟩ : syracuseStep 7499587 = 11249381) B11249381
theorem B9999449 : Blo 1973435 9999449 := bstep (se 2 (by rfl) ⟨3749793, by rfl⟩ : syracuseStep 9999449 = 7499587) B7499587
theorem B6666299 : Blo 1973435 6666299 := bstep (se 1 (by rfl) ⟨4999724, by rfl⟩ : syracuseStep 6666299 = 9999449) B9999449
theorem B4444199 : Blo 1973435 4444199 := bstep (se 1 (by rfl) ⟨3333149, by rfl⟩ : syracuseStep 4444199 = 6666299) B6666299
theorem B2962799 : Blo 1973435 2962799 := bstep (se 1 (by rfl) ⟨2222099, by rfl⟩ : syracuseStep 2962799 = 4444199) B4444199
theorem B1975199 : Blo 1973435 1975199 := bstep (se 1 (by rfl) ⟨1481399, by rfl⟩ : syracuseStep 1975199 = 2962799) B2962799
theorem B2962805 : Blo 1973435 2962805 := bbase (se 5 (by rfl) ⟨138881, by rfl⟩ : syracuseStep 2962805 = 277763) (by norm_num)
theorem B1975203 : Blo 1973435 1975203 := bstep (se 1 (by rfl) ⟨1481402, by rfl⟩ : syracuseStep 1975203 = 2962805) B2962805
theorem B2812357 : Blo 1973435 2812357 := bbase (se 4 (by rfl) ⟨263658, by rfl⟩ : syracuseStep 2812357 = 527317) (by norm_num)
theorem B3749809 : Blo 1973435 3749809 := bstep (se 2 (by rfl) ⟨1406178, by rfl⟩ : syracuseStep 3749809 = 2812357) B2812357
theorem B4999745 : Blo 1973435 4999745 := bstep (se 2 (by rfl) ⟨1874904, by rfl⟩ : syracuseStep 4999745 = 3749809) B3749809
theorem B3333163 : Blo 1973435 3333163 := bstep (se 1 (by rfl) ⟨2499872, by rfl⟩ : syracuseStep 3333163 = 4999745) B4999745
theorem B4444217 : Blo 1973435 4444217 := bstep (se 2 (by rfl) ⟨1666581, by rfl⟩ : syracuseStep 4444217 = 3333163) B3333163
theorem B2962811 : Blo 1973435 2962811 := bstep (se 1 (by rfl) ⟨2222108, by rfl⟩ : syracuseStep 2962811 = 4444217) B4444217
theorem B1975207 : Blo 1973435 1975207 := bstep (se 1 (by rfl) ⟨1481405, by rfl⟩ : syracuseStep 1975207 = 2962811) B2962811
theorem B2222113 : Blo 1973435 2222113 := bbase (se 2 (by rfl) ⟨833292, by rfl⟩ : syracuseStep 2222113 = 1666585) (by norm_num)
theorem B2962817 : Blo 1973435 2962817 := bstep (se 2 (by rfl) ⟨1111056, by rfl⟩ : syracuseStep 2962817 = 2222113) B2222113
theorem B1975211 : Blo 1973435 1975211 := bstep (se 1 (by rfl) ⟨1481408, by rfl⟩ : syracuseStep 1975211 = 2962817) B2962817
theorem B4999765 : Blo 1973435 4999765 := bbase (se 8 (by rfl) ⟨29295, by rfl⟩ : syracuseStep 4999765 = 58591) (by norm_num)
theorem B6666353 : Blo 1973435 6666353 := bstep (se 2 (by rfl) ⟨2499882, by rfl⟩ : syracuseStep 6666353 = 4999765) B4999765
theorem B4444235 : Blo 1973435 4444235 := bstep (se 1 (by rfl) ⟨3333176, by rfl⟩ : syracuseStep 4444235 = 6666353) B6666353
theorem B2962823 : Blo 1973435 2962823 := bstep (se 1 (by rfl) ⟨2222117, by rfl⟩ : syracuseStep 2962823 = 4444235) B4444235
theorem B1975215 : Blo 1973435 1975215 := bstep (se 1 (by rfl) ⟨1481411, by rfl⟩ : syracuseStep 1975215 = 2962823) B2962823
theorem B2962829 : Blo 1973435 2962829 := bbase (se 3 (by rfl) ⟨555530, by rfl⟩ : syracuseStep 2962829 = 1111061) (by norm_num)
theorem B1975219 : Blo 1973435 1975219 := bstep (se 1 (by rfl) ⟨1481414, by rfl⟩ : syracuseStep 1975219 = 2962829) B2962829
theorem B4444253 : Blo 1973435 4444253 := bbase (se 3 (by rfl) ⟨833297, by rfl⟩ : syracuseStep 4444253 = 1666595) (by norm_num)
theorem B2962835 : Blo 1973435 2962835 := bstep (se 1 (by rfl) ⟨2222126, by rfl⟩ : syracuseStep 2962835 = 4444253) B4444253
theorem B1975223 : Blo 1973435 1975223 := bstep (se 1 (by rfl) ⟨1481417, by rfl⟩ : syracuseStep 1975223 = 2962835) B2962835
theorem B3333197 : Blo 1973435 3333197 := bbase (se 3 (by rfl) ⟨624974, by rfl⟩ : syracuseStep 3333197 = 1249949) (by norm_num)
theorem B2222131 : Blo 1973435 2222131 := bstep (se 1 (by rfl) ⟨1666598, by rfl⟩ : syracuseStep 2222131 = 3333197) B3333197
theorem B2962841 : Blo 1973435 2962841 := bstep (se 2 (by rfl) ⟨1111065, by rfl⟩ : syracuseStep 2962841 = 2222131) B2222131
theorem B1975227 : Blo 1973435 1975227 := bstep (se 1 (by rfl) ⟨1481420, by rfl⟩ : syracuseStep 1975227 = 2962841) B2962841
theorem B5068021 : Blo 1973435 5068021 := bbase (se 5 (by rfl) ⟨237563, by rfl⟩ : syracuseStep 5068021 = 475127) (by norm_num)
theorem B6757361 : Blo 1973435 6757361 := bstep (se 2 (by rfl) ⟨2534010, by rfl⟩ : syracuseStep 6757361 = 5068021) B5068021
theorem B4504907 : Blo 1973435 4504907 := bstep (se 1 (by rfl) ⟨3378680, by rfl⟩ : syracuseStep 4504907 = 6757361) B6757361
theorem B12013085 : Blo 1973435 12013085 := bstep (se 3 (by rfl) ⟨2252453, by rfl⟩ : syracuseStep 12013085 = 4504907) B4504907
theorem B8008723 : Blo 1973435 8008723 := bstep (se 1 (by rfl) ⟨6006542, by rfl⟩ : syracuseStep 8008723 = 12013085) B12013085
theorem B42713189 : Blo 1973435 42713189 := bstep (se 4 (by rfl) ⟨4004361, by rfl⟩ : syracuseStep 42713189 = 8008723) B8008723
theorem B28475459 : Blo 1973435 28475459 := bstep (se 1 (by rfl) ⟨21356594, by rfl⟩ : syracuseStep 28475459 = 42713189) B42713189
theorem B18983639 : Blo 1973435 18983639 := bstep (se 1 (by rfl) ⟨14237729, by rfl⟩ : syracuseStep 18983639 = 28475459) B28475459
theorem B12655759 : Blo 1973435 12655759 := bstep (se 1 (by rfl) ⟨9491819, by rfl⟩ : syracuseStep 12655759 = 18983639) B18983639
theorem B16874345 : Blo 1973435 16874345 := bstep (se 2 (by rfl) ⟨6327879, by rfl⟩ : syracuseStep 16874345 = 12655759) B12655759
theorem B11249563 : Blo 1973435 11249563 := bstep (se 1 (by rfl) ⟨8437172, by rfl⟩ : syracuseStep 11249563 = 16874345) B16874345
theorem B14999417 : Blo 1973435 14999417 := bstep (se 2 (by rfl) ⟨5624781, by rfl⟩ : syracuseStep 14999417 = 11249563) B11249563
theorem B9999611 : Blo 1973435 9999611 := bstep (se 1 (by rfl) ⟨7499708, by rfl⟩ : syracuseStep 9999611 = 14999417) B14999417
theorem B6666407 : Blo 1973435 6666407 := bstep (se 1 (by rfl) ⟨4999805, by rfl⟩ : syracuseStep 6666407 = 9999611) B9999611
theorem B4444271 : Blo 1973435 4444271 := bstep (se 1 (by rfl) ⟨3333203, by rfl⟩ : syracuseStep 4444271 = 6666407) B6666407
theorem B2962847 : Blo 1973435 2962847 := bstep (se 1 (by rfl) ⟨2222135, by rfl⟩ : syracuseStep 2962847 = 4444271) B4444271
theorem B1975231 : Blo 1973435 1975231 := bstep (se 1 (by rfl) ⟨1481423, by rfl⟩ : syracuseStep 1975231 = 2962847) B2962847
theorem B2962853 : Blo 1973435 2962853 := bbase (se 4 (by rfl) ⟨277767, by rfl⟩ : syracuseStep 2962853 = 555535) (by norm_num)
theorem B1975235 : Blo 1973435 1975235 := bstep (se 1 (by rfl) ⟨1481426, by rfl⟩ : syracuseStep 1975235 = 2962853) B2962853
theorem B2499913 : Blo 1973435 2499913 := bbase (se 2 (by rfl) ⟨937467, by rfl⟩ : syracuseStep 2499913 = 1874935) (by norm_num)
theorem B3333217 : Blo 1973435 3333217 := bstep (se 2 (by rfl) ⟨1249956, by rfl⟩ : syracuseStep 3333217 = 2499913) B2499913
theorem B4444289 : Blo 1973435 4444289 := bstep (se 2 (by rfl) ⟨1666608, by rfl⟩ : syracuseStep 4444289 = 3333217) B3333217
theorem B2962859 : Blo 1973435 2962859 := bstep (se 1 (by rfl) ⟨2222144, by rfl⟩ : syracuseStep 2962859 = 4444289) B4444289
theorem B1975239 : Blo 1973435 1975239 := bstep (se 1 (by rfl) ⟨1481429, by rfl⟩ : syracuseStep 1975239 = 2962859) B2962859
theorem B2222149 : Blo 1973435 2222149 := bbase (se 4 (by rfl) ⟨208326, by rfl⟩ : syracuseStep 2222149 = 416653) (by norm_num)
theorem B2962865 : Blo 1973435 2962865 := bstep (se 2 (by rfl) ⟨1111074, by rfl⟩ : syracuseStep 2962865 = 2222149) B2222149
theorem B1975243 : Blo 1973435 1975243 := bstep (se 1 (by rfl) ⟨1481432, by rfl⟩ : syracuseStep 1975243 = 2962865) B2962865
theorem B3749885 : Blo 1973435 3749885 := bbase (se 3 (by rfl) ⟨703103, by rfl⟩ : syracuseStep 3749885 = 1406207) (by norm_num)
theorem B2499923 : Blo 1973435 2499923 := bstep (se 1 (by rfl) ⟨1874942, by rfl⟩ : syracuseStep 2499923 = 3749885) B3749885
theorem B6666461 : Blo 1973435 6666461 := bstep (se 3 (by rfl) ⟨1249961, by rfl⟩ : syracuseStep 6666461 = 2499923) B2499923
theorem B4444307 : Blo 1973435 4444307 := bstep (se 1 (by rfl) ⟨3333230, by rfl⟩ : syracuseStep 4444307 = 6666461) B6666461
theorem B2962871 : Blo 1973435 2962871 := bstep (se 1 (by rfl) ⟨2222153, by rfl⟩ : syracuseStep 2962871 = 4444307) B4444307
theorem B1975247 : Blo 1973435 1975247 := bstep (se 1 (by rfl) ⟨1481435, by rfl⟩ : syracuseStep 1975247 = 2962871) B2962871
theorem B2962877 : Blo 1973435 2962877 := bbase (se 3 (by rfl) ⟨555539, by rfl⟩ : syracuseStep 2962877 = 1111079) (by norm_num)
theorem B1975251 : Blo 1973435 1975251 := bstep (se 1 (by rfl) ⟨1481438, by rfl⟩ : syracuseStep 1975251 = 2962877) B2962877
theorem B4444325 : Blo 1973435 4444325 := bbase (se 4 (by rfl) ⟨416655, by rfl⟩ : syracuseStep 4444325 = 833311) (by norm_num)
theorem B2962883 : Blo 1973435 2962883 := bstep (se 1 (by rfl) ⟨2222162, by rfl⟩ : syracuseStep 2962883 = 4444325) B4444325
theorem B1975255 : Blo 1973435 1975255 := bstep (se 1 (by rfl) ⟨1481441, by rfl⟩ : syracuseStep 1975255 = 2962883) B2962883
theorem B4999877 : Blo 1973435 4999877 := bbase (se 4 (by rfl) ⟨468738, by rfl⟩ : syracuseStep 4999877 = 937477) (by norm_num)
theorem B3333251 : Blo 1973435 3333251 := bstep (se 1 (by rfl) ⟨2499938, by rfl⟩ : syracuseStep 3333251 = 4999877) B4999877
theorem B2222167 : Blo 1973435 2222167 := bstep (se 1 (by rfl) ⟨1666625, by rfl⟩ : syracuseStep 2222167 = 3333251) B3333251
theorem B2962889 : Blo 1973435 2962889 := bstep (se 2 (by rfl) ⟨1111083, by rfl⟩ : syracuseStep 2962889 = 2222167) B2222167
theorem B1975259 : Blo 1973435 1975259 := bstep (se 1 (by rfl) ⟨1481444, by rfl⟩ : syracuseStep 1975259 = 2962889) B2962889
theorem B4504981 : Blo 1973435 4504981 := bbase (se 6 (by rfl) ⟨105585, by rfl⟩ : syracuseStep 4504981 = 211171) (by norm_num)
theorem B6006641 : Blo 1973435 6006641 := bstep (se 2 (by rfl) ⟨2252490, by rfl⟩ : syracuseStep 6006641 = 4504981) B4504981
theorem B16017709 : Blo 1973435 16017709 := bstep (se 3 (by rfl) ⟨3003320, by rfl⟩ : syracuseStep 16017709 = 6006641) B6006641
theorem B21356945 : Blo 1973435 21356945 := bstep (se 2 (by rfl) ⟨8008854, by rfl⟩ : syracuseStep 21356945 = 16017709) B16017709
theorem B14237963 : Blo 1973435 14237963 := bstep (se 1 (by rfl) ⟨10678472, by rfl⟩ : syracuseStep 14237963 = 21356945) B21356945
theorem B9491975 : Blo 1973435 9491975 := bstep (se 1 (by rfl) ⟨7118981, by rfl⟩ : syracuseStep 9491975 = 14237963) B14237963
theorem B6327983 : Blo 1973435 6327983 := bstep (se 1 (by rfl) ⟨4745987, by rfl⟩ : syracuseStep 6327983 = 9491975) B9491975
theorem B4218655 : Blo 1973435 4218655 := bstep (se 1 (by rfl) ⟨3163991, by rfl⟩ : syracuseStep 4218655 = 6327983) B6327983
theorem B5624873 : Blo 1973435 5624873 := bstep (se 2 (by rfl) ⟨2109327, by rfl⟩ : syracuseStep 5624873 = 4218655) B4218655
theorem B3749915 : Blo 1973435 3749915 := bstep (se 1 (by rfl) ⟨2812436, by rfl⟩ : syracuseStep 3749915 = 5624873) B5624873
theorem B9999773 : Blo 1973435 9999773 := bstep (se 3 (by rfl) ⟨1874957, by rfl⟩ : syracuseStep 9999773 = 3749915) B3749915
theorem B6666515 : Blo 1973435 6666515 := bstep (se 1 (by rfl) ⟨4999886, by rfl⟩ : syracuseStep 6666515 = 9999773) B9999773
theorem B4444343 : Blo 1973435 4444343 := bstep (se 1 (by rfl) ⟨3333257, by rfl⟩ : syracuseStep 4444343 = 6666515) B6666515
theorem B2962895 : Blo 1973435 2962895 := bstep (se 1 (by rfl) ⟨2222171, by rfl⟩ : syracuseStep 2962895 = 4444343) B4444343
theorem B1975263 : Blo 1973435 1975263 := bstep (se 1 (by rfl) ⟨1481447, by rfl⟩ : syracuseStep 1975263 = 2962895) B2962895
theorem B2962901 : Blo 1973435 2962901 := bbase (se 7 (by rfl) ⟨34721, by rfl⟩ : syracuseStep 2962901 = 69443) (by norm_num)
theorem B1975267 : Blo 1973435 1975267 := bstep (se 1 (by rfl) ⟨1481450, by rfl⟩ : syracuseStep 1975267 = 2962901) B2962901
theorem B7499861 : Blo 1973435 7499861 := bbase (se 8 (by rfl) ⟨43944, by rfl⟩ : syracuseStep 7499861 = 87889) (by norm_num)
theorem B4999907 : Blo 1973435 4999907 := bstep (se 1 (by rfl) ⟨3749930, by rfl⟩ : syracuseStep 4999907 = 7499861) B7499861
theorem B3333271 : Blo 1973435 3333271 := bstep (se 1 (by rfl) ⟨2499953, by rfl⟩ : syracuseStep 3333271 = 4999907) B4999907
theorem B4444361 : Blo 1973435 4444361 := bstep (se 2 (by rfl) ⟨1666635, by rfl⟩ : syracuseStep 4444361 = 3333271) B3333271
theorem B2962907 : Blo 1973435 2962907 := bstep (se 1 (by rfl) ⟨2222180, by rfl⟩ : syracuseStep 2962907 = 4444361) B4444361
theorem B1975271 : Blo 1973435 1975271 := bstep (se 1 (by rfl) ⟨1481453, by rfl⟩ : syracuseStep 1975271 = 2962907) B2962907
theorem B2222185 : Blo 1973435 2222185 := bbase (se 2 (by rfl) ⟨833319, by rfl⟩ : syracuseStep 2222185 = 1666639) (by norm_num)
theorem B2962913 : Blo 1973435 2962913 := bstep (se 2 (by rfl) ⟨1111092, by rfl⟩ : syracuseStep 2962913 = 2222185) B2222185
theorem B1975275 : Blo 1973435 1975275 := bstep (se 1 (by rfl) ⟨1481456, by rfl⟩ : syracuseStep 1975275 = 2962913) B2962913
theorem B2373013 : Blo 1973435 2373013 := bbase (se 6 (by rfl) ⟨55617, by rfl⟩ : syracuseStep 2373013 = 111235) (by norm_num)
theorem B3164017 : Blo 1973435 3164017 := bstep (se 2 (by rfl) ⟨1186506, by rfl⟩ : syracuseStep 3164017 = 2373013) B2373013
theorem B4218689 : Blo 1973435 4218689 := bstep (se 2 (by rfl) ⟨1582008, by rfl⟩ : syracuseStep 4218689 = 3164017) B3164017
theorem B11249837 : Blo 1973435 11249837 := bstep (se 3 (by rfl) ⟨2109344, by rfl⟩ : syracuseStep 11249837 = 4218689) B4218689
theorem B7499891 : Blo 1973435 7499891 := bstep (se 1 (by rfl) ⟨5624918, by rfl⟩ : syracuseStep 7499891 = 11249837) B11249837
theorem B4999927 : Blo 1973435 4999927 := bstep (se 1 (by rfl) ⟨3749945, by rfl⟩ : syracuseStep 4999927 = 7499891) B7499891
theorem B6666569 : Blo 1973435 6666569 := bstep (se 2 (by rfl) ⟨2499963, by rfl⟩ : syracuseStep 6666569 = 4999927) B4999927
theorem B4444379 : Blo 1973435 4444379 := bstep (se 1 (by rfl) ⟨3333284, by rfl⟩ : syracuseStep 4444379 = 6666569) B6666569
theorem B2962919 : Blo 1973435 2962919 := bstep (se 1 (by rfl) ⟨2222189, by rfl⟩ : syracuseStep 2962919 = 4444379) B4444379
theorem B1975279 : Blo 1973435 1975279 := bstep (se 1 (by rfl) ⟨1481459, by rfl⟩ : syracuseStep 1975279 = 2962919) B2962919
theorem B2962925 : Blo 1973435 2962925 := bbase (se 3 (by rfl) ⟨555548, by rfl⟩ : syracuseStep 2962925 = 1111097) (by norm_num)
theorem B1975283 : Blo 1973435 1975283 := bstep (se 1 (by rfl) ⟨1481462, by rfl⟩ : syracuseStep 1975283 = 2962925) B2962925
theorem B4444397 : Blo 1973435 4444397 := bbase (se 3 (by rfl) ⟨833324, by rfl⟩ : syracuseStep 4444397 = 1666649) (by norm_num)
theorem B2962931 : Blo 1973435 2962931 := bstep (se 1 (by rfl) ⟨2222198, by rfl⟩ : syracuseStep 2962931 = 4444397) B4444397
theorem B1975287 : Blo 1973435 1975287 := bstep (se 1 (by rfl) ⟨1481465, by rfl⟩ : syracuseStep 1975287 = 2962931) B2962931
theorem B2812477 : Blo 1973435 2812477 := bbase (se 3 (by rfl) ⟨527339, by rfl⟩ : syracuseStep 2812477 = 1054679) (by norm_num)
theorem B3749969 : Blo 1973435 3749969 := bstep (se 2 (by rfl) ⟨1406238, by rfl⟩ : syracuseStep 3749969 = 2812477) B2812477
theorem B2499979 : Blo 1973435 2499979 := bstep (se 1 (by rfl) ⟨1874984, by rfl⟩ : syracuseStep 2499979 = 3749969) B3749969
theorem B3333305 : Blo 1973435 3333305 := bstep (se 2 (by rfl) ⟨1249989, by rfl⟩ : syracuseStep 3333305 = 2499979) B2499979
theorem B2222203 : Blo 1973435 2222203 := bstep (se 1 (by rfl) ⟨1666652, by rfl⟩ : syracuseStep 2222203 = 3333305) B3333305
theorem B2962937 : Blo 1973435 2962937 := bstep (se 2 (by rfl) ⟨1111101, by rfl⟩ : syracuseStep 2962937 = 2222203) B2222203
theorem B1975291 : Blo 1973435 1975291 := bstep (se 1 (by rfl) ⟨1481468, by rfl⟩ : syracuseStep 1975291 = 2962937) B2962937
theorem B4505053 : Blo 1973435 4505053 := bbase (se 3 (by rfl) ⟨844697, by rfl⟩ : syracuseStep 4505053 = 1689395) (by norm_num)
theorem B6006737 : Blo 1973435 6006737 := bstep (se 2 (by rfl) ⟨2252526, by rfl⟩ : syracuseStep 6006737 = 4505053) B4505053
theorem B16017965 : Blo 1973435 16017965 := bstep (se 3 (by rfl) ⟨3003368, by rfl⟩ : syracuseStep 16017965 = 6006737) B6006737
theorem B10678643 : Blo 1973435 10678643 := bstep (se 1 (by rfl) ⟨8008982, by rfl⟩ : syracuseStep 10678643 = 16017965) B16017965
theorem B7119095 : Blo 1973435 7119095 := bstep (se 1 (by rfl) ⟨5339321, by rfl⟩ : syracuseStep 7119095 = 10678643) B10678643
theorem B75937013 : Blo 1973435 75937013 := bstep (se 5 (by rfl) ⟨3559547, by rfl⟩ : syracuseStep 75937013 = 7119095) B7119095
theorem B50624675 : Blo 1973435 50624675 := bstep (se 1 (by rfl) ⟨37968506, by rfl⟩ : syracuseStep 50624675 = 75937013) B75937013
theorem B33749783 : Blo 1973435 33749783 := bstep (se 1 (by rfl) ⟨25312337, by rfl⟩ : syracuseStep 33749783 = 50624675) B50624675
theorem B22499855 : Blo 1973435 22499855 := bstep (se 1 (by rfl) ⟨16874891, by rfl⟩ : syracuseStep 22499855 = 33749783) B33749783
theorem B14999903 : Blo 1973435 14999903 := bstep (se 1 (by rfl) ⟨11249927, by rfl⟩ : syracuseStep 14999903 = 22499855) B22499855
theorem B9999935 : Blo 1973435 9999935 := bstep (se 1 (by rfl) ⟨7499951, by rfl⟩ : syracuseStep 9999935 = 14999903) B14999903
theorem B6666623 : Blo 1973435 6666623 := bstep (se 1 (by rfl) ⟨4999967, by rfl⟩ : syracuseStep 6666623 = 9999935) B9999935
theorem B4444415 : Blo 1973435 4444415 := bstep (se 1 (by rfl) ⟨3333311, by rfl⟩ : syracuseStep 4444415 = 6666623) B6666623
theorem B2962943 : Blo 1973435 2962943 := bstep (se 1 (by rfl) ⟨2222207, by rfl⟩ : syracuseStep 2962943 = 4444415) B4444415
theorem B1975295 : Blo 1973435 1975295 := bstep (se 1 (by rfl) ⟨1481471, by rfl⟩ : syracuseStep 1975295 = 2962943) B2962943
theorem B2962949 : Blo 1973435 2962949 := bbase (se 4 (by rfl) ⟨277776, by rfl⟩ : syracuseStep 2962949 = 555553) (by norm_num)
theorem B1975299 : Blo 1973435 1975299 := bstep (se 1 (by rfl) ⟨1481474, by rfl⟩ : syracuseStep 1975299 = 2962949) B2962949
theorem B3333325 : Blo 1973435 3333325 := bbase (se 3 (by rfl) ⟨624998, by rfl⟩ : syracuseStep 3333325 = 1249997) (by norm_num)
theorem B4444433 : Blo 1973435 4444433 := bstep (se 2 (by rfl) ⟨1666662, by rfl⟩ : syracuseStep 4444433 = 3333325) B3333325
theorem B2962955 : Blo 1973435 2962955 := bstep (se 1 (by rfl) ⟨2222216, by rfl⟩ : syracuseStep 2962955 = 4444433) B4444433
theorem B1975303 : Blo 1973435 1975303 := bstep (se 1 (by rfl) ⟨1481477, by rfl⟩ : syracuseStep 1975303 = 2962955) B2962955
theorem B2222221 : Blo 1973435 2222221 := bbase (se 3 (by rfl) ⟨416666, by rfl⟩ : syracuseStep 2222221 = 833333) (by norm_num)
theorem B2962961 : Blo 1973435 2962961 := bstep (se 2 (by rfl) ⟨1111110, by rfl⟩ : syracuseStep 2962961 = 2222221) B2222221
theorem B1975307 : Blo 1973435 1975307 := bstep (se 1 (by rfl) ⟨1481480, by rfl⟩ : syracuseStep 1975307 = 2962961) B2962961
theorem B6666677 : Blo 1973435 6666677 := bbase (se 5 (by rfl) ⟨312500, by rfl⟩ : syracuseStep 6666677 = 625001) (by norm_num)
theorem B4444451 : Blo 1973435 4444451 := bstep (se 1 (by rfl) ⟨3333338, by rfl⟩ : syracuseStep 4444451 = 6666677) B6666677
theorem B2962967 : Blo 1973435 2962967 := bstep (se 1 (by rfl) ⟨2222225, by rfl⟩ : syracuseStep 2962967 = 4444451) B4444451
theorem B1975311 : Blo 1973435 1975311 := bstep (se 1 (by rfl) ⟨1481483, by rfl⟩ : syracuseStep 1975311 = 2962967) B2962967
theorem B2962973 : Blo 1973435 2962973 := bbase (se 3 (by rfl) ⟨555557, by rfl⟩ : syracuseStep 2962973 = 1111115) (by norm_num)
theorem B1975315 : Blo 1973435 1975315 := bstep (se 1 (by rfl) ⟨1481486, by rfl⟩ : syracuseStep 1975315 = 2962973) B2962973
theorem B4444469 : Blo 1973435 4444469 := bbase (se 5 (by rfl) ⟨208334, by rfl⟩ : syracuseStep 4444469 = 416669) (by norm_num)
theorem B2962979 : Blo 1973435 2962979 := bstep (se 1 (by rfl) ⟨2222234, by rfl⟩ : syracuseStep 2962979 = 4444469) B4444469
theorem B1975319 : Blo 1973435 1975319 := bstep (se 1 (by rfl) ⟨1481489, by rfl⟩ : syracuseStep 1975319 = 2962979) B2962979
theorem B3608165 : Blo 1973435 3608165 := bbase (se 4 (by rfl) ⟨338265, by rfl⟩ : syracuseStep 3608165 = 676531) (by norm_num)
theorem B9621773 : Blo 1973435 9621773 := bstep (se 3 (by rfl) ⟨1804082, by rfl⟩ : syracuseStep 9621773 = 3608165) B3608165
theorem B6414515 : Blo 1973435 6414515 := bstep (se 1 (by rfl) ⟨4810886, by rfl⟩ : syracuseStep 6414515 = 9621773) B9621773
theorem B4276343 : Blo 1973435 4276343 := bstep (se 1 (by rfl) ⟨3207257, by rfl⟩ : syracuseStep 4276343 = 6414515) B6414515
theorem B2850895 : Blo 1973435 2850895 := bstep (se 1 (by rfl) ⟨2138171, by rfl⟩ : syracuseStep 2850895 = 4276343) B4276343
theorem B15204773 : Blo 1973435 15204773 := bstep (se 4 (by rfl) ⟨1425447, by rfl⟩ : syracuseStep 15204773 = 2850895) B2850895
theorem B10136515 : Blo 1973435 10136515 := bstep (se 1 (by rfl) ⟨7602386, by rfl⟩ : syracuseStep 10136515 = 15204773) B15204773
theorem B13515353 : Blo 1973435 13515353 := bstep (se 2 (by rfl) ⟨5068257, by rfl⟩ : syracuseStep 13515353 = 10136515) B10136515
theorem B9010235 : Blo 1973435 9010235 := bstep (se 1 (by rfl) ⟨6757676, by rfl⟩ : syracuseStep 9010235 = 13515353) B13515353
theorem B24027293 : Blo 1973435 24027293 := bstep (se 3 (by rfl) ⟨4505117, by rfl⟩ : syracuseStep 24027293 = 9010235) B9010235
theorem B64072781 : Blo 1973435 64072781 := bstep (se 3 (by rfl) ⟨12013646, by rfl⟩ : syracuseStep 64072781 = 24027293) B24027293
theorem B42715187 : Blo 1973435 42715187 := bstep (se 1 (by rfl) ⟨32036390, by rfl⟩ : syracuseStep 42715187 = 64072781) B64072781
theorem B28476791 : Blo 1973435 28476791 := bstep (se 1 (by rfl) ⟨21357593, by rfl⟩ : syracuseStep 28476791 = 42715187) B42715187
theorem B18984527 : Blo 1973435 18984527 := bstep (se 1 (by rfl) ⟨14238395, by rfl⟩ : syracuseStep 18984527 = 28476791) B28476791
theorem B12656351 : Blo 1973435 12656351 := bstep (se 1 (by rfl) ⟨9492263, by rfl⟩ : syracuseStep 12656351 = 18984527) B18984527
theorem B8437567 : Blo 1973435 8437567 := bstep (se 1 (by rfl) ⟨6328175, by rfl⟩ : syracuseStep 8437567 = 12656351) B12656351
theorem B11250089 : Blo 1973435 11250089 := bstep (se 2 (by rfl) ⟨4218783, by rfl⟩ : syracuseStep 11250089 = 8437567) B8437567
theorem B7500059 : Blo 1973435 7500059 := bstep (se 1 (by rfl) ⟨5625044, by rfl⟩ : syracuseStep 7500059 = 11250089) B11250089
theorem B5000039 : Blo 1973435 5000039 := bstep (se 1 (by rfl) ⟨3750029, by rfl⟩ : syracuseStep 5000039 = 7500059) B7500059
theorem B3333359 : Blo 1973435 3333359 := bstep (se 1 (by rfl) ⟨2500019, by rfl⟩ : syracuseStep 3333359 = 5000039) B5000039
theorem B2222239 : Blo 1973435 2222239 := bstep (se 1 (by rfl) ⟨1666679, by rfl⟩ : syracuseStep 2222239 = 3333359) B3333359
theorem B2962985 : Blo 1973435 2962985 := bstep (se 2 (by rfl) ⟨1111119, by rfl⟩ : syracuseStep 2962985 = 2222239) B2222239
theorem B1975323 : Blo 1973435 1975323 := bstep (se 1 (by rfl) ⟨1481492, by rfl⟩ : syracuseStep 1975323 = 2962985) B2962985
theorem B3378845 : Blo 1973435 3378845 := bbase (se 3 (by rfl) ⟨633533, by rfl⟩ : syracuseStep 3378845 = 1267067) (by norm_num)
theorem B9010253 : Blo 1973435 9010253 := bstep (se 3 (by rfl) ⟨1689422, by rfl⟩ : syracuseStep 9010253 = 3378845) B3378845
theorem B6006835 : Blo 1973435 6006835 := bstep (se 1 (by rfl) ⟨4505126, by rfl⟩ : syracuseStep 6006835 = 9010253) B9010253
theorem B8009113 : Blo 1973435 8009113 := bstep (se 2 (by rfl) ⟨3003417, by rfl⟩ : syracuseStep 8009113 = 6006835) B6006835
theorem B10678817 : Blo 1973435 10678817 := bstep (se 2 (by rfl) ⟨4004556, by rfl⟩ : syracuseStep 10678817 = 8009113) B8009113
theorem B28476845 : Blo 1973435 28476845 := bstep (se 3 (by rfl) ⟨5339408, by rfl⟩ : syracuseStep 28476845 = 10678817) B10678817
theorem B18984563 : Blo 1973435 18984563 := bstep (se 1 (by rfl) ⟨14238422, by rfl⟩ : syracuseStep 18984563 = 28476845) B28476845
theorem B12656375 : Blo 1973435 12656375 := bstep (se 1 (by rfl) ⟨9492281, by rfl⟩ : syracuseStep 12656375 = 18984563) B18984563
theorem B8437583 : Blo 1973435 8437583 := bstep (se 1 (by rfl) ⟨6328187, by rfl⟩ : syracuseStep 8437583 = 12656375) B12656375
theorem B5625055 : Blo 1973435 5625055 := bstep (se 1 (by rfl) ⟨4218791, by rfl⟩ : syracuseStep 5625055 = 8437583) B8437583
theorem B7500073 : Blo 1973435 7500073 := bstep (se 2 (by rfl) ⟨2812527, by rfl⟩ : syracuseStep 7500073 = 5625055) B5625055
theorem B10000097 : Blo 1973435 10000097 := bstep (se 2 (by rfl) ⟨3750036, by rfl⟩ : syracuseStep 10000097 = 7500073) B7500073
theorem B6666731 : Blo 1973435 6666731 := bstep (se 1 (by rfl) ⟨5000048, by rfl⟩ : syracuseStep 6666731 = 10000097) B10000097
theorem B4444487 : Blo 1973435 4444487 := bstep (se 1 (by rfl) ⟨3333365, by rfl⟩ : syracuseStep 4444487 = 6666731) B6666731
theorem B2962991 : Blo 1973435 2962991 := bstep (se 1 (by rfl) ⟨2222243, by rfl⟩ : syracuseStep 2962991 = 4444487) B4444487
theorem B1975327 : Blo 1973435 1975327 := bstep (se 1 (by rfl) ⟨1481495, by rfl⟩ : syracuseStep 1975327 = 2962991) B2962991
theorem B2962997 : Blo 1973435 2962997 := bbase (se 5 (by rfl) ⟨138890, by rfl⟩ : syracuseStep 2962997 = 277781) (by norm_num)
theorem B1975331 : Blo 1973435 1975331 := bstep (se 1 (by rfl) ⟨1481498, by rfl⟩ : syracuseStep 1975331 = 2962997) B2962997
theorem B5000069 : Blo 1973435 5000069 := bbase (se 4 (by rfl) ⟨468756, by rfl⟩ : syracuseStep 5000069 = 937513) (by norm_num)
theorem B3333379 : Blo 1973435 3333379 := bstep (se 1 (by rfl) ⟨2500034, by rfl⟩ : syracuseStep 3333379 = 5000069) B5000069
theorem B4444505 : Blo 1973435 4444505 := bstep (se 2 (by rfl) ⟨1666689, by rfl⟩ : syracuseStep 4444505 = 3333379) B3333379
theorem B2963003 : Blo 1973435 2963003 := bstep (se 1 (by rfl) ⟨2222252, by rfl⟩ : syracuseStep 2963003 = 4444505) B4444505
theorem B1975335 : Blo 1973435 1975335 := bstep (se 1 (by rfl) ⟨1481501, by rfl⟩ : syracuseStep 1975335 = 2963003) B2963003
theorem B2222257 : Blo 1973435 2222257 := bbase (se 2 (by rfl) ⟨833346, by rfl⟩ : syracuseStep 2222257 = 1666693) (by norm_num)
theorem B2963009 : Blo 1973435 2963009 := bstep (se 2 (by rfl) ⟨1111128, by rfl⟩ : syracuseStep 2963009 = 2222257) B2222257
theorem B1975339 : Blo 1973435 1975339 := bstep (se 1 (by rfl) ⟨1481504, by rfl⟩ : syracuseStep 1975339 = 2963009) B2963009
theorem B2109413 : Blo 1973435 2109413 := bbase (se 4 (by rfl) ⟨197757, by rfl⟩ : syracuseStep 2109413 = 395515) (by norm_num)
theorem B5625101 : Blo 1973435 5625101 := bstep (se 3 (by rfl) ⟨1054706, by rfl⟩ : syracuseStep 5625101 = 2109413) B2109413
theorem B3750067 : Blo 1973435 3750067 := bstep (se 1 (by rfl) ⟨2812550, by rfl⟩ : syracuseStep 3750067 = 5625101) B5625101
theorem B5000089 : Blo 1973435 5000089 := bstep (se 2 (by rfl) ⟨1875033, by rfl⟩ : syracuseStep 5000089 = 3750067) B3750067
theorem B6666785 : Blo 1973435 6666785 := bstep (se 2 (by rfl) ⟨2500044, by rfl⟩ : syracuseStep 6666785 = 5000089) B5000089
theorem B4444523 : Blo 1973435 4444523 := bstep (se 1 (by rfl) ⟨3333392, by rfl⟩ : syracuseStep 4444523 = 6666785) B6666785
theorem B2963015 : Blo 1973435 2963015 := bstep (se 1 (by rfl) ⟨2222261, by rfl⟩ : syracuseStep 2963015 = 4444523) B4444523
theorem B1975343 : Blo 1973435 1975343 := bstep (se 1 (by rfl) ⟨1481507, by rfl⟩ : syracuseStep 1975343 = 2963015) B2963015
theorem B2963021 : Blo 1973435 2963021 := bbase (se 3 (by rfl) ⟨555566, by rfl⟩ : syracuseStep 2963021 = 1111133) (by norm_num)
theorem B1975347 : Blo 1973435 1975347 := bstep (se 1 (by rfl) ⟨1481510, by rfl⟩ : syracuseStep 1975347 = 2963021) B2963021
theorem B4444541 : Blo 1973435 4444541 := bbase (se 3 (by rfl) ⟨833351, by rfl⟩ : syracuseStep 4444541 = 1666703) (by norm_num)
theorem B2963027 : Blo 1973435 2963027 := bstep (se 1 (by rfl) ⟨2222270, by rfl⟩ : syracuseStep 2963027 = 4444541) B4444541
theorem B1975351 : Blo 1973435 1975351 := bstep (se 1 (by rfl) ⟨1481513, by rfl⟩ : syracuseStep 1975351 = 2963027) B2963027
theorem B3333413 : Blo 1973435 3333413 := bbase (se 4 (by rfl) ⟨312507, by rfl⟩ : syracuseStep 3333413 = 625015) (by norm_num)
theorem B2222275 : Blo 1973435 2222275 := bstep (se 1 (by rfl) ⟨1666706, by rfl⟩ : syracuseStep 2222275 = 3333413) B3333413
theorem B2963033 : Blo 1973435 2963033 := bstep (se 2 (by rfl) ⟨1111137, by rfl⟩ : syracuseStep 2963033 = 2222275) B2222275
theorem B1975355 : Blo 1973435 1975355 := bstep (se 1 (by rfl) ⟨1481516, by rfl⟩ : syracuseStep 1975355 = 2963033) B2963033
theorem B2812573 : Blo 1973435 2812573 := bbase (se 3 (by rfl) ⟨527357, by rfl⟩ : syracuseStep 2812573 = 1054715) (by norm_num)
theorem B15000389 : Blo 1973435 15000389 := bstep (se 4 (by rfl) ⟨1406286, by rfl⟩ : syracuseStep 15000389 = 2812573) B2812573
theorem B10000259 : Blo 1973435 10000259 := bstep (se 1 (by rfl) ⟨7500194, by rfl⟩ : syracuseStep 10000259 = 15000389) B15000389
theorem B6666839 : Blo 1973435 6666839 := bstep (se 1 (by rfl) ⟨5000129, by rfl⟩ : syracuseStep 6666839 = 10000259) B10000259
theorem B4444559 : Blo 1973435 4444559 := bstep (se 1 (by rfl) ⟨3333419, by rfl⟩ : syracuseStep 4444559 = 6666839) B6666839
theorem B2963039 : Blo 1973435 2963039 := bstep (se 1 (by rfl) ⟨2222279, by rfl⟩ : syracuseStep 2963039 = 4444559) B4444559
theorem B1975359 : Blo 1973435 1975359 := bstep (se 1 (by rfl) ⟨1481519, by rfl⟩ : syracuseStep 1975359 = 2963039) B2963039
theorem B2963045 : Blo 1973435 2963045 := bbase (se 4 (by rfl) ⟨277785, by rfl⟩ : syracuseStep 2963045 = 555571) (by norm_num)
theorem B1975363 : Blo 1973435 1975363 := bstep (se 1 (by rfl) ⟨1481522, by rfl⟩ : syracuseStep 1975363 = 2963045) B2963045
theorem B30063637 : Blo 1973435 30063637 := bbase (se 6 (by rfl) ⟨704616, by rfl⟩ : syracuseStep 30063637 = 1409233) (by norm_num)
theorem B160339397 : Blo 1973435 160339397 := bstep (se 4 (by rfl) ⟨15031818, by rfl⟩ : syracuseStep 160339397 = 30063637) B30063637
theorem B427571725 : Blo 1973435 427571725 := bstep (se 3 (by rfl) ⟨80169698, by rfl⟩ : syracuseStep 427571725 = 160339397) B160339397
theorem B570095633 : Blo 1973435 570095633 := bstep (se 2 (by rfl) ⟨213785862, by rfl⟩ : syracuseStep 570095633 = 427571725) B427571725
theorem B380063755 : Blo 1973435 380063755 := bstep (se 1 (by rfl) ⟨285047816, by rfl⟩ : syracuseStep 380063755 = 570095633) B570095633
theorem B506751673 : Blo 1973435 506751673 := bstep (se 2 (by rfl) ⟨190031877, by rfl⟩ : syracuseStep 506751673 = 380063755) B380063755
theorem B675668897 : Blo 1973435 675668897 := bstep (se 2 (by rfl) ⟨253375836, by rfl⟩ : syracuseStep 675668897 = 506751673) B506751673
theorem B450445931 : Blo 1973435 450445931 := bstep (se 1 (by rfl) ⟨337834448, by rfl⟩ : syracuseStep 450445931 = 675668897) B675668897
theorem B300297287 : Blo 1973435 300297287 := bstep (se 1 (by rfl) ⟨225222965, by rfl⟩ : syracuseStep 300297287 = 450445931) B450445931
theorem B200198191 : Blo 1973435 200198191 := bstep (se 1 (by rfl) ⟨150148643, by rfl⟩ : syracuseStep 200198191 = 300297287) B300297287
theorem B266930921 : Blo 1973435 266930921 := bstep (se 2 (by rfl) ⟨100099095, by rfl⟩ : syracuseStep 266930921 = 200198191) B200198191
theorem B711815789 : Blo 1973435 711815789 := bstep (se 3 (by rfl) ⟨133465460, by rfl⟩ : syracuseStep 711815789 = 266930921) B266930921
theorem B474543859 : Blo 1973435 474543859 := bstep (se 1 (by rfl) ⟨355907894, by rfl⟩ : syracuseStep 474543859 = 711815789) B711815789
theorem B632725145 : Blo 1973435 632725145 := bstep (se 2 (by rfl) ⟨237271929, by rfl⟩ : syracuseStep 632725145 = 474543859) B474543859
theorem B421816763 : Blo 1973435 421816763 := bstep (se 1 (by rfl) ⟨316362572, by rfl⟩ : syracuseStep 421816763 = 632725145) B632725145
theorem B281211175 : Blo 1973435 281211175 := bstep (se 1 (by rfl) ⟨210908381, by rfl⟩ : syracuseStep 281211175 = 421816763) B421816763
theorem B374948233 : Blo 1973435 374948233 := bstep (se 2 (by rfl) ⟨140605587, by rfl⟩ : syracuseStep 374948233 = 281211175) B281211175
theorem B7998895637 : Blo 1973435 7998895637 := bstep (se 6 (by rfl) ⟨187474116, by rfl⟩ : syracuseStep 7998895637 = 374948233) B374948233
theorem B5332597091 : Blo 1973435 5332597091 := bstep (se 1 (by rfl) ⟨3999447818, by rfl⟩ : syracuseStep 5332597091 = 7998895637) B7998895637
theorem B3555064727 : Blo 1973435 3555064727 := bstep (se 1 (by rfl) ⟨2666298545, by rfl⟩ : syracuseStep 3555064727 = 5332597091) B5332597091
theorem B2370043151 : Blo 1973435 2370043151 := bstep (se 1 (by rfl) ⟨1777532363, by rfl⟩ : syracuseStep 2370043151 = 3555064727) B3555064727
theorem B1580028767 : Blo 1973435 1580028767 := bstep (se 1 (by rfl) ⟨1185021575, by rfl⟩ : syracuseStep 1580028767 = 2370043151) B2370043151
theorem B1053352511 : Blo 1973435 1053352511 := bstep (se 1 (by rfl) ⟨790014383, by rfl⟩ : syracuseStep 1053352511 = 1580028767) B1580028767
theorem B702235007 : Blo 1973435 702235007 := bstep (se 1 (by rfl) ⟨526676255, by rfl⟩ : syracuseStep 702235007 = 1053352511) B1053352511
theorem B468156671 : Blo 1973435 468156671 := bstep (se 1 (by rfl) ⟨351117503, by rfl⟩ : syracuseStep 468156671 = 702235007) B702235007
theorem B312104447 : Blo 1973435 312104447 := bstep (se 1 (by rfl) ⟨234078335, by rfl⟩ : syracuseStep 312104447 = 468156671) B468156671
theorem B208069631 : Blo 1973435 208069631 := bstep (se 1 (by rfl) ⟨156052223, by rfl⟩ : syracuseStep 208069631 = 312104447) B312104447
theorem B138713087 : Blo 1973435 138713087 := bstep (se 1 (by rfl) ⟨104034815, by rfl⟩ : syracuseStep 138713087 = 208069631) B208069631
theorem B369901565 : Blo 1973435 369901565 := bstep (se 3 (by rfl) ⟨69356543, by rfl⟩ : syracuseStep 369901565 = 138713087) B138713087
theorem B246601043 : Blo 1973435 246601043 := bstep (se 1 (by rfl) ⟨184950782, by rfl⟩ : syracuseStep 246601043 = 369901565) B369901565
theorem B164400695 : Blo 1973435 164400695 := bstep (se 1 (by rfl) ⟨123300521, by rfl⟩ : syracuseStep 164400695 = 246601043) B246601043
theorem B109600463 : Blo 1973435 109600463 := bstep (se 1 (by rfl) ⟨82200347, by rfl⟩ : syracuseStep 109600463 = 164400695) B164400695
theorem B292267901 : Blo 1973435 292267901 := bstep (se 3 (by rfl) ⟨54800231, by rfl⟩ : syracuseStep 292267901 = 109600463) B109600463
theorem B194845267 : Blo 1973435 194845267 := bstep (se 1 (by rfl) ⟨146133950, by rfl⟩ : syracuseStep 194845267 = 292267901) B292267901
theorem B259793689 : Blo 1973435 259793689 := bstep (se 2 (by rfl) ⟨97422633, by rfl⟩ : syracuseStep 259793689 = 194845267) B194845267
theorem B346391585 : Blo 1973435 346391585 := bstep (se 2 (by rfl) ⟨129896844, by rfl⟩ : syracuseStep 346391585 = 259793689) B259793689
theorem B230927723 : Blo 1973435 230927723 := bstep (se 1 (by rfl) ⟨173195792, by rfl⟩ : syracuseStep 230927723 = 346391585) B346391585
theorem B153951815 : Blo 1973435 153951815 := bstep (se 1 (by rfl) ⟨115463861, by rfl⟩ : syracuseStep 153951815 = 230927723) B230927723
theorem B102634543 : Blo 1973435 102634543 := bstep (se 1 (by rfl) ⟨76975907, by rfl⟩ : syracuseStep 102634543 = 153951815) B153951815
theorem B136846057 : Blo 1973435 136846057 := bstep (se 2 (by rfl) ⟨51317271, by rfl⟩ : syracuseStep 136846057 = 102634543) B102634543
theorem B182461409 : Blo 1973435 182461409 := bstep (se 2 (by rfl) ⟨68423028, by rfl⟩ : syracuseStep 182461409 = 136846057) B136846057
theorem B121640939 : Blo 1973435 121640939 := bstep (se 1 (by rfl) ⟨91230704, by rfl⟩ : syracuseStep 121640939 = 182461409) B182461409
theorem B81093959 : Blo 1973435 81093959 := bstep (se 1 (by rfl) ⟨60820469, by rfl⟩ : syracuseStep 81093959 = 121640939) B121640939
theorem B54062639 : Blo 1973435 54062639 := bstep (se 1 (by rfl) ⟨40546979, by rfl⟩ : syracuseStep 54062639 = 81093959) B81093959
theorem B36041759 : Blo 1973435 36041759 := bstep (se 1 (by rfl) ⟨27031319, by rfl⟩ : syracuseStep 36041759 = 54062639) B54062639
theorem B24027839 : Blo 1973435 24027839 := bstep (se 1 (by rfl) ⟨18020879, by rfl⟩ : syracuseStep 24027839 = 36041759) B36041759
theorem B16018559 : Blo 1973435 16018559 := bstep (se 1 (by rfl) ⟨12013919, by rfl⟩ : syracuseStep 16018559 = 24027839) B24027839
theorem B10679039 : Blo 1973435 10679039 := bstep (se 1 (by rfl) ⟨8009279, by rfl⟩ : syracuseStep 10679039 = 16018559) B16018559
theorem B7119359 : Blo 1973435 7119359 := bstep (se 1 (by rfl) ⟨5339519, by rfl⟩ : syracuseStep 7119359 = 10679039) B10679039
theorem B4746239 : Blo 1973435 4746239 := bstep (se 1 (by rfl) ⟨3559679, by rfl⟩ : syracuseStep 4746239 = 7119359) B7119359
theorem B3164159 : Blo 1973435 3164159 := bstep (se 1 (by rfl) ⟨2373119, by rfl⟩ : syracuseStep 3164159 = 4746239) B4746239
theorem B2109439 : Blo 1973435 2109439 := bstep (se 1 (by rfl) ⟨1582079, by rfl⟩ : syracuseStep 2109439 = 3164159) B3164159
theorem B2812585 : Blo 1973435 2812585 := bstep (se 2 (by rfl) ⟨1054719, by rfl⟩ : syracuseStep 2812585 = 2109439) B2109439
theorem B3750113 : Blo 1973435 3750113 := bstep (se 2 (by rfl) ⟨1406292, by rfl⟩ : syracuseStep 3750113 = 2812585) B2812585
theorem B2500075 : Blo 1973435 2500075 := bstep (se 1 (by rfl) ⟨1875056, by rfl⟩ : syracuseStep 2500075 = 3750113) B3750113
theorem B3333433 : Blo 1973435 3333433 := bstep (se 2 (by rfl) ⟨1250037, by rfl⟩ : syracuseStep 3333433 = 2500075) B2500075
theorem B4444577 : Blo 1973435 4444577 := bstep (se 2 (by rfl) ⟨1666716, by rfl⟩ : syracuseStep 4444577 = 3333433) B3333433
theorem B2963051 : Blo 1973435 2963051 := bstep (se 1 (by rfl) ⟨2222288, by rfl⟩ : syracuseStep 2963051 = 4444577) B4444577
theorem B1975367 : Blo 1973435 1975367 := bstep (se 1 (by rfl) ⟨1481525, by rfl⟩ : syracuseStep 1975367 = 2963051) B2963051
theorem B2222293 : Blo 1973435 2222293 := bbase (se 7 (by rfl) ⟨26042, by rfl⟩ : syracuseStep 2222293 = 52085) (by norm_num)
theorem B2963057 : Blo 1973435 2963057 := bstep (se 2 (by rfl) ⟨1111146, by rfl⟩ : syracuseStep 2963057 = 2222293) B2222293
theorem B1975371 : Blo 1973435 1975371 := bstep (se 1 (by rfl) ⟨1481528, by rfl⟩ : syracuseStep 1975371 = 2963057) B2963057
theorem B2500085 : Blo 1973435 2500085 := bbase (se 5 (by rfl) ⟨117191, by rfl⟩ : syracuseStep 2500085 = 234383) (by norm_num)
theorem B6666893 : Blo 1973435 6666893 := bstep (se 3 (by rfl) ⟨1250042, by rfl⟩ : syracuseStep 6666893 = 2500085) B2500085
theorem B4444595 : Blo 1973435 4444595 := bstep (se 1 (by rfl) ⟨3333446, by rfl⟩ : syracuseStep 4444595 = 6666893) B6666893
theorem B2963063 : Blo 1973435 2963063 := bstep (se 1 (by rfl) ⟨2222297, by rfl⟩ : syracuseStep 2963063 = 4444595) B4444595
theorem B1975375 : Blo 1973435 1975375 := bstep (se 1 (by rfl) ⟨1481531, by rfl⟩ : syracuseStep 1975375 = 2963063) B2963063
theorem B2963069 : Blo 1973435 2963069 := bbase (se 3 (by rfl) ⟨555575, by rfl⟩ : syracuseStep 2963069 = 1111151) (by norm_num)
theorem B1975379 : Blo 1973435 1975379 := bstep (se 1 (by rfl) ⟨1481534, by rfl⟩ : syracuseStep 1975379 = 2963069) B2963069
theorem B4444613 : Blo 1973435 4444613 := bbase (se 4 (by rfl) ⟨416682, by rfl⟩ : syracuseStep 4444613 = 833365) (by norm_num)
theorem B2963075 : Blo 1973435 2963075 := bstep (se 1 (by rfl) ⟨2222306, by rfl⟩ : syracuseStep 2963075 = 4444613) B4444613
theorem B1975383 : Blo 1973435 1975383 := bstep (se 1 (by rfl) ⟨1481537, by rfl⟩ : syracuseStep 1975383 = 2963075) B2963075
theorem B5339573 : Blo 1973435 5339573 := bbase (se 5 (by rfl) ⟨250292, by rfl⟩ : syracuseStep 5339573 = 500585) (by norm_num)
theorem B3559715 : Blo 1973435 3559715 := bstep (se 1 (by rfl) ⟨2669786, by rfl⟩ : syracuseStep 3559715 = 5339573) B5339573
theorem B2373143 : Blo 1973435 2373143 := bstep (se 1 (by rfl) ⟨1779857, by rfl⟩ : syracuseStep 2373143 = 3559715) B3559715
theorem B6328381 : Blo 1973435 6328381 := bstep (se 3 (by rfl) ⟨1186571, by rfl⟩ : syracuseStep 6328381 = 2373143) B2373143
theorem B8437841 : Blo 1973435 8437841 := bstep (se 2 (by rfl) ⟨3164190, by rfl⟩ : syracuseStep 8437841 = 6328381) B6328381
theorem B5625227 : Blo 1973435 5625227 := bstep (se 1 (by rfl) ⟨4218920, by rfl⟩ : syracuseStep 5625227 = 8437841) B8437841
theorem B3750151 : Blo 1973435 3750151 := bstep (se 1 (by rfl) ⟨2812613, by rfl⟩ : syracuseStep 3750151 = 5625227) B5625227
theorem B5000201 : Blo 1973435 5000201 := bstep (se 2 (by rfl) ⟨1875075, by rfl⟩ : syracuseStep 5000201 = 3750151) B3750151
theorem B3333467 : Blo 1973435 3333467 := bstep (se 1 (by rfl) ⟨2500100, by rfl⟩ : syracuseStep 3333467 = 5000201) B5000201
theorem B2222311 : Blo 1973435 2222311 := bstep (se 1 (by rfl) ⟨1666733, by rfl⟩ : syracuseStep 2222311 = 3333467) B3333467
theorem B2963081 : Blo 1973435 2963081 := bstep (se 2 (by rfl) ⟨1111155, by rfl⟩ : syracuseStep 2963081 = 2222311) B2222311
theorem B1975387 : Blo 1973435 1975387 := bstep (se 1 (by rfl) ⟨1481540, by rfl⟩ : syracuseStep 1975387 = 2963081) B2963081
theorem B10000421 : Blo 1973435 10000421 := bbase (se 4 (by rfl) ⟨937539, by rfl⟩ : syracuseStep 10000421 = 1875079) (by norm_num)
theorem B6666947 : Blo 1973435 6666947 := bstep (se 1 (by rfl) ⟨5000210, by rfl⟩ : syracuseStep 6666947 = 10000421) B10000421
theorem B4444631 : Blo 1973435 4444631 := bstep (se 1 (by rfl) ⟨3333473, by rfl⟩ : syracuseStep 4444631 = 6666947) B6666947
theorem B2963087 : Blo 1973435 2963087 := bstep (se 1 (by rfl) ⟨2222315, by rfl⟩ : syracuseStep 2963087 = 4444631) B4444631
theorem B1975391 : Blo 1973435 1975391 := bstep (se 1 (by rfl) ⟨1481543, by rfl⟩ : syracuseStep 1975391 = 2963087) B2963087
theorem B2963093 : Blo 1973435 2963093 := bbase (se 6 (by rfl) ⟨69447, by rfl⟩ : syracuseStep 2963093 = 138895) (by norm_num)
theorem B1975395 : Blo 1973435 1975395 := bstep (se 1 (by rfl) ⟨1481546, by rfl⟩ : syracuseStep 1975395 = 2963093) B2963093
theorem B2373157 : Blo 1973435 2373157 := bbase (se 4 (by rfl) ⟨222483, by rfl⟩ : syracuseStep 2373157 = 444967) (by norm_num)
theorem B12656837 : Blo 1973435 12656837 := bstep (se 4 (by rfl) ⟨1186578, by rfl⟩ : syracuseStep 12656837 = 2373157) B2373157
theorem B8437891 : Blo 1973435 8437891 := bstep (se 1 (by rfl) ⟨6328418, by rfl⟩ : syracuseStep 8437891 = 12656837) B12656837
theorem B11250521 : Blo 1973435 11250521 := bstep (se 2 (by rfl) ⟨4218945, by rfl⟩ : syracuseStep 11250521 = 8437891) B8437891
theorem B7500347 : Blo 1973435 7500347 := bstep (se 1 (by rfl) ⟨5625260, by rfl⟩ : syracuseStep 7500347 = 11250521) B11250521
theorem B5000231 : Blo 1973435 5000231 := bstep (se 1 (by rfl) ⟨3750173, by rfl⟩ : syracuseStep 5000231 = 7500347) B7500347
theorem B3333487 : Blo 1973435 3333487 := bstep (se 1 (by rfl) ⟨2500115, by rfl⟩ : syracuseStep 3333487 = 5000231) B5000231
theorem B4444649 : Blo 1973435 4444649 := bstep (se 2 (by rfl) ⟨1666743, by rfl⟩ : syracuseStep 4444649 = 3333487) B3333487
theorem B2963099 : Blo 1973435 2963099 := bstep (se 1 (by rfl) ⟨2222324, by rfl⟩ : syracuseStep 2963099 = 4444649) B4444649
theorem B1975399 : Blo 1973435 1975399 := bstep (se 1 (by rfl) ⟨1481549, by rfl⟩ : syracuseStep 1975399 = 2963099) B2963099
theorem B2222329 : Blo 1973435 2222329 := bbase (se 2 (by rfl) ⟨833373, by rfl⟩ : syracuseStep 2222329 = 1666747) (by norm_num)
theorem B2963105 : Blo 1973435 2963105 := bstep (se 2 (by rfl) ⟨1111164, by rfl⟩ : syracuseStep 2963105 = 2222329) B2222329
theorem B1975403 : Blo 1973435 1975403 := bstep (se 1 (by rfl) ⟨1481552, by rfl⟩ : syracuseStep 1975403 = 2963105) B2963105
theorem B8437925 : Blo 1973435 8437925 := bbase (se 4 (by rfl) ⟨791055, by rfl⟩ : syracuseStep 8437925 = 1582111) (by norm_num)
theorem B5625283 : Blo 1973435 5625283 := bstep (se 1 (by rfl) ⟨4218962, by rfl⟩ : syracuseStep 5625283 = 8437925) B8437925
theorem B7500377 : Blo 1973435 7500377 := bstep (se 2 (by rfl) ⟨2812641, by rfl⟩ : syracuseStep 7500377 = 5625283) B5625283
theorem B5000251 : Blo 1973435 5000251 := bstep (se 1 (by rfl) ⟨3750188, by rfl⟩ : syracuseStep 5000251 = 7500377) B7500377
theorem B6667001 : Blo 1973435 6667001 := bstep (se 2 (by rfl) ⟨2500125, by rfl⟩ : syracuseStep 6667001 = 5000251) B5000251
theorem B4444667 : Blo 1973435 4444667 := bstep (se 1 (by rfl) ⟨3333500, by rfl⟩ : syracuseStep 4444667 = 6667001) B6667001
theorem B2963111 : Blo 1973435 2963111 := bstep (se 1 (by rfl) ⟨2222333, by rfl⟩ : syracuseStep 2963111 = 4444667) B4444667
theorem B1975407 : Blo 1973435 1975407 := bstep (se 1 (by rfl) ⟨1481555, by rfl⟩ : syracuseStep 1975407 = 2963111) B2963111
theorem B2963117 : Blo 1973435 2963117 := bbase (se 3 (by rfl) ⟨555584, by rfl⟩ : syracuseStep 2963117 = 1111169) (by norm_num)
theorem B1975411 : Blo 1973435 1975411 := bstep (se 1 (by rfl) ⟨1481558, by rfl⟩ : syracuseStep 1975411 = 2963117) B2963117
theorem B4444685 : Blo 1973435 4444685 := bbase (se 3 (by rfl) ⟨833378, by rfl⟩ : syracuseStep 4444685 = 1666757) (by norm_num)
theorem B2963123 : Blo 1973435 2963123 := bstep (se 1 (by rfl) ⟨2222342, by rfl⟩ : syracuseStep 2963123 = 4444685) B4444685
theorem B1975415 : Blo 1973435 1975415 := bstep (se 1 (by rfl) ⟨1481561, by rfl⟩ : syracuseStep 1975415 = 2963123) B2963123
theorem B2500141 : Blo 1973435 2500141 := bbase (se 3 (by rfl) ⟨468776, by rfl⟩ : syracuseStep 2500141 = 937553) (by norm_num)
theorem B3333521 : Blo 1973435 3333521 := bstep (se 2 (by rfl) ⟨1250070, by rfl⟩ : syracuseStep 3333521 = 2500141) B2500141
theorem B2222347 : Blo 1973435 2222347 := bstep (se 1 (by rfl) ⟨1666760, by rfl⟩ : syracuseStep 2222347 = 3333521) B3333521
theorem B2963129 : Blo 1973435 2963129 := bstep (se 2 (by rfl) ⟨1111173, by rfl⟩ : syracuseStep 2963129 = 2222347) B2222347
theorem B1975419 : Blo 1973435 1975419 := bstep (se 1 (by rfl) ⟨1481564, by rfl⟩ : syracuseStep 1975419 = 2963129) B2963129
theorem B7119557 : Blo 1973435 7119557 := bbase (se 4 (by rfl) ⟨667458, by rfl⟩ : syracuseStep 7119557 = 1334917) (by norm_num)
theorem B4746371 : Blo 1973435 4746371 := bstep (se 1 (by rfl) ⟨3559778, by rfl⟩ : syracuseStep 4746371 = 7119557) B7119557
theorem B12656989 : Blo 1973435 12656989 := bstep (se 3 (by rfl) ⟨2373185, by rfl⟩ : syracuseStep 12656989 = 4746371) B4746371
theorem B16875985 : Blo 1973435 16875985 := bstep (se 2 (by rfl) ⟨6328494, by rfl⟩ : syracuseStep 16875985 = 12656989) B12656989
theorem B22501313 : Blo 1973435 22501313 := bstep (se 2 (by rfl) ⟨8437992, by rfl⟩ : syracuseStep 22501313 = 16875985) B16875985
theorem B15000875 : Blo 1973435 15000875 := bstep (se 1 (by rfl) ⟨11250656, by rfl⟩ : syracuseStep 15000875 = 22501313) B22501313
theorem B10000583 : Blo 1973435 10000583 := bstep (se 1 (by rfl) ⟨7500437, by rfl⟩ : syracuseStep 10000583 = 15000875) B15000875
theorem B6667055 : Blo 1973435 6667055 := bstep (se 1 (by rfl) ⟨5000291, by rfl⟩ : syracuseStep 6667055 = 10000583) B10000583
theorem B4444703 : Blo 1973435 4444703 := bstep (se 1 (by rfl) ⟨3333527, by rfl⟩ : syracuseStep 4444703 = 6667055) B6667055
theorem B2963135 : Blo 1973435 2963135 := bstep (se 1 (by rfl) ⟨2222351, by rfl⟩ : syracuseStep 2963135 = 4444703) B4444703
theorem B1975423 : Blo 1973435 1975423 := bstep (se 1 (by rfl) ⟨1481567, by rfl⟩ : syracuseStep 1975423 = 2963135) B2963135
theorem B2963141 : Blo 1973435 2963141 := bbase (se 4 (by rfl) ⟨277794, by rfl⟩ : syracuseStep 2963141 = 555589) (by norm_num)
theorem B1975427 : Blo 1973435 1975427 := bstep (se 1 (by rfl) ⟨1481570, by rfl⟩ : syracuseStep 1975427 = 2963141) B2963141
theorem B3333541 : Blo 1973435 3333541 := bbase (se 4 (by rfl) ⟨312519, by rfl⟩ : syracuseStep 3333541 = 625039) (by norm_num)
theorem B4444721 : Blo 1973435 4444721 := bstep (se 2 (by rfl) ⟨1666770, by rfl⟩ : syracuseStep 4444721 = 3333541) B3333541
theorem B2963147 : Blo 1973435 2963147 := bstep (se 1 (by rfl) ⟨2222360, by rfl⟩ : syracuseStep 2963147 = 4444721) B4444721
theorem B1975431 : Blo 1973435 1975431 := bstep (se 1 (by rfl) ⟨1481573, by rfl⟩ : syracuseStep 1975431 = 2963147) B2963147
theorem B2222365 : Blo 1973435 2222365 := bbase (se 3 (by rfl) ⟨416693, by rfl⟩ : syracuseStep 2222365 = 833387) (by norm_num)
theorem B2963153 : Blo 1973435 2963153 := bstep (se 2 (by rfl) ⟨1111182, by rfl⟩ : syracuseStep 2963153 = 2222365) B2222365
theorem B1975435 : Blo 1973435 1975435 := bstep (se 1 (by rfl) ⟨1481576, by rfl⟩ : syracuseStep 1975435 = 2963153) B2963153
theorem C0 (j : ℕ) (h1 : 493358 ≤ j) (h2 : j ≤ 493858) : Blo 1973435 (4 * j + 3) := by
  interval_cases j
  · exact B1973435
  · exact B1973439
  · exact B1973443
  · exact B1973447
  · exact B1973451
  · exact B1973455
  · exact B1973459
  · exact B1973463
  · exact B1973467
  · exact B1973471
  · exact B1973475
  · exact B1973479
  · exact B1973483
  · exact B1973487
  · exact B1973491
  · exact B1973495
  · exact B1973499
  · exact B1973503
  · exact B1973507
  · exact B1973511
  · exact B1973515
  · exact B1973519
  · exact B1973523
  · exact B1973527
  · exact B1973531
  · exact B1973535
  · exact B1973539
  · exact B1973543
  · exact B1973547
  · exact B1973551
  · exact B1973555
  · exact B1973559
  · exact B1973563
  · exact B1973567
  · exact B1973571
  · exact B1973575
  · exact B1973579
  · exact B1973583
  · exact B1973587
  · exact B1973591
  · exact B1973595
  · exact B1973599
  · exact B1973603
  · exact B1973607
  · exact B1973611
  · exact B1973615
  · exact B1973619
  · exact B1973623
  · exact B1973627
  · exact B1973631
  · exact B1973635
  · exact B1973639
  · exact B1973643
  · exact B1973647
  · exact B1973651
  · exact B1973655
  · exact B1973659
  · exact B1973663
  · exact B1973667
  · exact B1973671
  · exact B1973675
  · exact B1973679
  · exact B1973683
  · exact B1973687
  · exact B1973691
  · exact B1973695
  · exact B1973699
  · exact B1973703
  · exact B1973707
  · exact B1973711
  · exact B1973715
  · exact B1973719
  · exact B1973723
  · exact B1973727
  · exact B1973731
  · exact B1973735
  · exact B1973739
  · exact B1973743
  · exact B1973747
  · exact B1973751
  · exact B1973755
  · exact B1973759
  · exact B1973763
  · exact B1973767
  · exact B1973771
  · exact B1973775
  · exact B1973779
  · exact B1973783
  · exact B1973787
  · exact B1973791
  · exact B1973795
  · exact B1973799
  · exact B1973803
  · exact B1973807
  · exact B1973811
  · exact B1973815
  · exact B1973819
  · exact B1973823
  · exact B1973827
  · exact B1973831
  · exact B1973835
  · exact B1973839
  · exact B1973843
  · exact B1973847
  · exact B1973851
  · exact B1973855
  · exact B1973859
  · exact B1973863
  · exact B1973867
  · exact B1973871
  · exact B1973875
  · exact B1973879
  · exact B1973883
  · exact B1973887
  · exact B1973891
  · exact B1973895
  · exact B1973899
  · exact B1973903
  · exact B1973907
  · exact B1973911
  · exact B1973915
  · exact B1973919
  · exact B1973923
  · exact B1973927
  · exact B1973931
  · exact B1973935
  · exact B1973939
  · exact B1973943
  · exact B1973947
  · exact B1973951
  · exact B1973955
  · exact B1973959
  · exact B1973963
  · exact B1973967
  · exact B1973971
  · exact B1973975
  · exact B1973979
  · exact B1973983
  · exact B1973987
  · exact B1973991
  · exact B1973995
  · exact B1973999
  · exact B1974003
  · exact B1974007
  · exact B1974011
  · exact B1974015
  · exact B1974019
  · exact B1974023
  · exact B1974027
  · exact B1974031
  · exact B1974035
  · exact B1974039
  · exact B1974043
  · exact B1974047
  · exact B1974051
  · exact B1974055
  · exact B1974059
  · exact B1974063
  · exact B1974067
  · exact B1974071
  · exact B1974075
  · exact B1974079
  · exact B1974083
  · exact B1974087
  · exact B1974091
  · exact B1974095
  · exact B1974099
  · exact B1974103
  · exact B1974107
  · exact B1974111
  · exact B1974115
  · exact B1974119
  · exact B1974123
  · exact B1974127
  · exact B1974131
  · exact B1974135
  · exact B1974139
  · exact B1974143
  · exact B1974147
  · exact B1974151
  · exact B1974155
  · exact B1974159
  · exact B1974163
  · exact B1974167
  · exact B1974171
  · exact B1974175
  · exact B1974179
  · exact B1974183
  · exact B1974187
  · exact B1974191
  · exact B1974195
  · exact B1974199
  · exact B1974203
  · exact B1974207
  · exact B1974211
  · exact B1974215
  · exact B1974219
  · exact B1974223
  · exact B1974227
  · exact B1974231
  · exact B1974235
  · exact B1974239
  · exact B1974243
  · exact B1974247
  · exact B1974251
  · exact B1974255
  · exact B1974259
  · exact B1974263
  · exact B1974267
  · exact B1974271
  · exact B1974275
  · exact B1974279
  · exact B1974283
  · exact B1974287
  · exact B1974291
  · exact B1974295
  · exact B1974299
  · exact B1974303
  · exact B1974307
  · exact B1974311
  · exact B1974315
  · exact B1974319
  · exact B1974323
  · exact B1974327
  · exact B1974331
  · exact B1974335
  · exact B1974339
  · exact B1974343
  · exact B1974347
  · exact B1974351
  · exact B1974355
  · exact B1974359
  · exact B1974363
  · exact B1974367
  · exact B1974371
  · exact B1974375
  · exact B1974379
  · exact B1974383
  · exact B1974387
  · exact B1974391
  · exact B1974395
  · exact B1974399
  · exact B1974403
  · exact B1974407
  · exact B1974411
  · exact B1974415
  · exact B1974419
  · exact B1974423
  · exact B1974427
  · exact B1974431
  · exact B1974435
  · exact B1974439
  · exact B1974443
  · exact B1974447
  · exact B1974451
  · exact B1974455
  · exact B1974459
  · exact B1974463
  · exact B1974467
  · exact B1974471
  · exact B1974475
  · exact B1974479
  · exact B1974483
  · exact B1974487
  · exact B1974491
  · exact B1974495
  · exact B1974499
  · exact B1974503
  · exact B1974507
  · exact B1974511
  · exact B1974515
  · exact B1974519
  · exact B1974523
  · exact B1974527
  · exact B1974531
  · exact B1974535
  · exact B1974539
  · exact B1974543
  · exact B1974547
  · exact B1974551
  · exact B1974555
  · exact B1974559
  · exact B1974563
  · exact B1974567
  · exact B1974571
  · exact B1974575
  · exact B1974579
  · exact B1974583
  · exact B1974587
  · exact B1974591
  · exact B1974595
  · exact B1974599
  · exact B1974603
  · exact B1974607
  · exact B1974611
  · exact B1974615
  · exact B1974619
  · exact B1974623
  · exact B1974627
  · exact B1974631
  · exact B1974635
  · exact B1974639
  · exact B1974643
  · exact B1974647
  · exact B1974651
  · exact B1974655
  · exact B1974659
  · exact B1974663
  · exact B1974667
  · exact B1974671
  · exact B1974675
  · exact B1974679
  · exact B1974683
  · exact B1974687
  · exact B1974691
  · exact B1974695
  · exact B1974699
  · exact B1974703
  · exact B1974707
  · exact B1974711
  · exact B1974715
  · exact B1974719
  · exact B1974723
  · exact B1974727
  · exact B1974731
  · exact B1974735
  · exact B1974739
  · exact B1974743
  · exact B1974747
  · exact B1974751
  · exact B1974755
  · exact B1974759
  · exact B1974763
  · exact B1974767
  · exact B1974771
  · exact B1974775
  · exact B1974779
  · exact B1974783
  · exact B1974787
  · exact B1974791
  · exact B1974795
  · exact B1974799
  · exact B1974803
  · exact B1974807
  · exact B1974811
  · exact B1974815
  · exact B1974819
  · exact B1974823
  · exact B1974827
  · exact B1974831
  · exact B1974835
  · exact B1974839
  · exact B1974843
  · exact B1974847
  · exact B1974851
  · exact B1974855
  · exact B1974859
  · exact B1974863
  · exact B1974867
  · exact B1974871
  · exact B1974875
  · exact B1974879
  · exact B1974883
  · exact B1974887
  · exact B1974891
  · exact B1974895
  · exact B1974899
  · exact B1974903
  · exact B1974907
  · exact B1974911
  · exact B1974915
  · exact B1974919
  · exact B1974923
  · exact B1974927
  · exact B1974931
  · exact B1974935
  · exact B1974939
  · exact B1974943
  · exact B1974947
  · exact B1974951
  · exact B1974955
  · exact B1974959
  · exact B1974963
  · exact B1974967
  · exact B1974971
  · exact B1974975
  · exact B1974979
  · exact B1974983
  · exact B1974987
  · exact B1974991
  · exact B1974995
  · exact B1974999
  · exact B1975003
  · exact B1975007
  · exact B1975011
  · exact B1975015
  · exact B1975019
  · exact B1975023
  · exact B1975027
  · exact B1975031
  · exact B1975035
  · exact B1975039
  · exact B1975043
  · exact B1975047
  · exact B1975051
  · exact B1975055
  · exact B1975059
  · exact B1975063
  · exact B1975067
  · exact B1975071
  · exact B1975075
  · exact B1975079
  · exact B1975083
  · exact B1975087
  · exact B1975091
  · exact B1975095
  · exact B1975099
  · exact B1975103
  · exact B1975107
  · exact B1975111
  · exact B1975115
  · exact B1975119
  · exact B1975123
  · exact B1975127
  · exact B1975131
  · exact B1975135
  · exact B1975139
  · exact B1975143
  · exact B1975147
  · exact B1975151
  · exact B1975155
  · exact B1975159
  · exact B1975163
  · exact B1975167
  · exact B1975171
  · exact B1975175
  · exact B1975179
  · exact B1975183
  · exact B1975187
  · exact B1975191
  · exact B1975195
  · exact B1975199
  · exact B1975203
  · exact B1975207
  · exact B1975211
  · exact B1975215
  · exact B1975219
  · exact B1975223
  · exact B1975227
  · exact B1975231
  · exact B1975235
  · exact B1975239
  · exact B1975243
  · exact B1975247
  · exact B1975251
  · exact B1975255
  · exact B1975259
  · exact B1975263
  · exact B1975267
  · exact B1975271
  · exact B1975275
  · exact B1975279
  · exact B1975283
  · exact B1975287
  · exact B1975291
  · exact B1975295
  · exact B1975299
  · exact B1975303
  · exact B1975307
  · exact B1975311
  · exact B1975315
  · exact B1975319
  · exact B1975323
  · exact B1975327
  · exact B1975331
  · exact B1975335
  · exact B1975339
  · exact B1975343
  · exact B1975347
  · exact B1975351
  · exact B1975355
  · exact B1975359
  · exact B1975363
  · exact B1975367
  · exact B1975371
  · exact B1975375
  · exact B1975379
  · exact B1975383
  · exact B1975387
  · exact B1975391
  · exact B1975395
  · exact B1975399
  · exact B1975403
  · exact B1975407
  · exact B1975411
  · exact B1975415
  · exact B1975419
  · exact B1975423
  · exact B1975427
  · exact B1975431
  · exact B1975435
theorem solution (m : ℕ) (hlo : 1973435 ≤ m) (hhi : m ≤ 1975435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 493358 ≤ j := by omega
    have hj2 : j ≤ 493858 := by omega
    have hb : Blo 1973435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
