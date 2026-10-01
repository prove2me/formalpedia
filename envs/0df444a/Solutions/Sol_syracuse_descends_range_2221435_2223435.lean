-- Prove2me | solution 1 for syracuse_descends_range_2221435_2223435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:18:40.012416+00:00
-- url     : https://prove2.me/submissions/2e69d4ba-2f31-42d6-a31c-b38954baabaf

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

theorem B2811505 : Blo 2221435 2811505 := bbase (se 2 (by rfl) ⟨1054314, by rfl⟩ : syracuseStep 2811505 = 2108629) (by norm_num)
theorem B3748673 : Blo 2221435 3748673 := bstep (se 2 (by rfl) ⟨1405752, by rfl⟩ : syracuseStep 3748673 = 2811505) B2811505
theorem B2499115 : Blo 2221435 2499115 := bstep (se 1 (by rfl) ⟨1874336, by rfl⟩ : syracuseStep 2499115 = 3748673) B3748673
theorem B3332153 : Blo 2221435 3332153 := bstep (se 2 (by rfl) ⟨1249557, by rfl⟩ : syracuseStep 3332153 = 2499115) B2499115
theorem B2221435 : Blo 2221435 2221435 := bstep (se 1 (by rfl) ⟨1666076, by rfl⟩ : syracuseStep 2221435 = 3332153) B3332153
theorem B2849869 : Blo 2221435 2849869 := bbase (se 3 (by rfl) ⟨534350, by rfl⟩ : syracuseStep 2849869 = 1068701) (by norm_num)
theorem B15199301 : Blo 2221435 15199301 := bstep (se 4 (by rfl) ⟨1424934, by rfl⟩ : syracuseStep 15199301 = 2849869) B2849869
theorem B10132867 : Blo 2221435 10132867 := bstep (se 1 (by rfl) ⟨7599650, by rfl⟩ : syracuseStep 10132867 = 15199301) B15199301
theorem B13510489 : Blo 2221435 13510489 := bstep (se 2 (by rfl) ⟨5066433, by rfl⟩ : syracuseStep 13510489 = 10132867) B10132867
theorem B18013985 : Blo 2221435 18013985 := bstep (se 2 (by rfl) ⟨6755244, by rfl⟩ : syracuseStep 18013985 = 13510489) B13510489
theorem B12009323 : Blo 2221435 12009323 := bstep (se 1 (by rfl) ⟨9006992, by rfl⟩ : syracuseStep 12009323 = 18013985) B18013985
theorem B8006215 : Blo 2221435 8006215 := bstep (se 1 (by rfl) ⟨6004661, by rfl⟩ : syracuseStep 8006215 = 12009323) B12009323
theorem B10674953 : Blo 2221435 10674953 := bstep (se 2 (by rfl) ⟨4003107, by rfl⟩ : syracuseStep 10674953 = 8006215) B8006215
theorem B7116635 : Blo 2221435 7116635 := bstep (se 1 (by rfl) ⟨5337476, by rfl⟩ : syracuseStep 7116635 = 10674953) B10674953
theorem B4744423 : Blo 2221435 4744423 := bstep (se 1 (by rfl) ⟨3558317, by rfl⟩ : syracuseStep 4744423 = 7116635) B7116635
theorem B25303589 : Blo 2221435 25303589 := bstep (se 4 (by rfl) ⟨2372211, by rfl⟩ : syracuseStep 25303589 = 4744423) B4744423
theorem B16869059 : Blo 2221435 16869059 := bstep (se 1 (by rfl) ⟨12651794, by rfl⟩ : syracuseStep 16869059 = 25303589) B25303589
theorem B11246039 : Blo 2221435 11246039 := bstep (se 1 (by rfl) ⟨8434529, by rfl⟩ : syracuseStep 11246039 = 16869059) B16869059
theorem B7497359 : Blo 2221435 7497359 := bstep (se 1 (by rfl) ⟨5623019, by rfl⟩ : syracuseStep 7497359 = 11246039) B11246039
theorem B4998239 : Blo 2221435 4998239 := bstep (se 1 (by rfl) ⟨3748679, by rfl⟩ : syracuseStep 4998239 = 7497359) B7497359
theorem B3332159 : Blo 2221435 3332159 := bstep (se 1 (by rfl) ⟨2499119, by rfl⟩ : syracuseStep 3332159 = 4998239) B4998239
theorem B2221439 : Blo 2221435 2221439 := bstep (se 1 (by rfl) ⟨1666079, by rfl⟩ : syracuseStep 2221439 = 3332159) B3332159
theorem B3332165 : Blo 2221435 3332165 := bbase (se 4 (by rfl) ⟨312390, by rfl⟩ : syracuseStep 3332165 = 624781) (by norm_num)
theorem B2221443 : Blo 2221435 2221443 := bstep (se 1 (by rfl) ⟨1666082, by rfl⟩ : syracuseStep 2221443 = 3332165) B3332165
theorem B3748693 : Blo 2221435 3748693 := bbase (se 9 (by rfl) ⟨10982, by rfl⟩ : syracuseStep 3748693 = 21965) (by norm_num)
theorem B4998257 : Blo 2221435 4998257 := bstep (se 2 (by rfl) ⟨1874346, by rfl⟩ : syracuseStep 4998257 = 3748693) B3748693
theorem B3332171 : Blo 2221435 3332171 := bstep (se 1 (by rfl) ⟨2499128, by rfl⟩ : syracuseStep 3332171 = 4998257) B4998257
theorem B2221447 : Blo 2221435 2221447 := bstep (se 1 (by rfl) ⟨1666085, by rfl⟩ : syracuseStep 2221447 = 3332171) B3332171
theorem B2499133 : Blo 2221435 2499133 := bbase (se 3 (by rfl) ⟨468587, by rfl⟩ : syracuseStep 2499133 = 937175) (by norm_num)
theorem B3332177 : Blo 2221435 3332177 := bstep (se 2 (by rfl) ⟨1249566, by rfl⟩ : syracuseStep 3332177 = 2499133) B2499133
theorem B2221451 : Blo 2221435 2221451 := bstep (se 1 (by rfl) ⟨1666088, by rfl⟩ : syracuseStep 2221451 = 3332177) B3332177
theorem B7497413 : Blo 2221435 7497413 := bbase (se 4 (by rfl) ⟨702882, by rfl⟩ : syracuseStep 7497413 = 1405765) (by norm_num)
theorem B4998275 : Blo 2221435 4998275 := bstep (se 1 (by rfl) ⟨3748706, by rfl⟩ : syracuseStep 4998275 = 7497413) B7497413
theorem B3332183 : Blo 2221435 3332183 := bstep (se 1 (by rfl) ⟨2499137, by rfl⟩ : syracuseStep 3332183 = 4998275) B4998275
theorem B2221455 : Blo 2221435 2221455 := bstep (se 1 (by rfl) ⟨1666091, by rfl⟩ : syracuseStep 2221455 = 3332183) B3332183
theorem B3332189 : Blo 2221435 3332189 := bbase (se 3 (by rfl) ⟨624785, by rfl⟩ : syracuseStep 3332189 = 1249571) (by norm_num)
theorem B2221459 : Blo 2221435 2221459 := bstep (se 1 (by rfl) ⟨1666094, by rfl⟩ : syracuseStep 2221459 = 3332189) B3332189
theorem B4998293 : Blo 2221435 4998293 := bbase (se 6 (by rfl) ⟨117147, by rfl⟩ : syracuseStep 4998293 = 234295) (by norm_num)
theorem B3332195 : Blo 2221435 3332195 := bstep (se 1 (by rfl) ⟨2499146, by rfl⟩ : syracuseStep 3332195 = 4998293) B4998293
theorem B2221463 : Blo 2221435 2221463 := bstep (se 1 (by rfl) ⟨1666097, by rfl⟩ : syracuseStep 2221463 = 3332195) B3332195
theorem B3162989 : Blo 2221435 3162989 := bbase (se 3 (by rfl) ⟨593060, by rfl⟩ : syracuseStep 3162989 = 1186121) (by norm_num)
theorem B8434637 : Blo 2221435 8434637 := bstep (se 3 (by rfl) ⟨1581494, by rfl⟩ : syracuseStep 8434637 = 3162989) B3162989
theorem B5623091 : Blo 2221435 5623091 := bstep (se 1 (by rfl) ⟨4217318, by rfl⟩ : syracuseStep 5623091 = 8434637) B8434637
theorem B3748727 : Blo 2221435 3748727 := bstep (se 1 (by rfl) ⟨2811545, by rfl⟩ : syracuseStep 3748727 = 5623091) B5623091
theorem B2499151 : Blo 2221435 2499151 := bstep (se 1 (by rfl) ⟨1874363, by rfl⟩ : syracuseStep 2499151 = 3748727) B3748727
theorem B3332201 : Blo 2221435 3332201 := bstep (se 2 (by rfl) ⟨1249575, by rfl⟩ : syracuseStep 3332201 = 2499151) B2499151
theorem B2221467 : Blo 2221435 2221467 := bstep (se 1 (by rfl) ⟨1666100, by rfl⟩ : syracuseStep 2221467 = 3332201) B3332201
theorem B4003165 : Blo 2221435 4003165 := bbase (se 3 (by rfl) ⟨750593, by rfl⟩ : syracuseStep 4003165 = 1501187) (by norm_num)
theorem B21350213 : Blo 2221435 21350213 := bstep (se 4 (by rfl) ⟨2001582, by rfl⟩ : syracuseStep 21350213 = 4003165) B4003165
theorem B14233475 : Blo 2221435 14233475 := bstep (se 1 (by rfl) ⟨10675106, by rfl⟩ : syracuseStep 14233475 = 21350213) B21350213
theorem B9488983 : Blo 2221435 9488983 := bstep (se 1 (by rfl) ⟨7116737, by rfl⟩ : syracuseStep 9488983 = 14233475) B14233475
theorem B12651977 : Blo 2221435 12651977 := bstep (se 2 (by rfl) ⟨4744491, by rfl⟩ : syracuseStep 12651977 = 9488983) B9488983
theorem B8434651 : Blo 2221435 8434651 := bstep (se 1 (by rfl) ⟨6325988, by rfl⟩ : syracuseStep 8434651 = 12651977) B12651977
theorem B11246201 : Blo 2221435 11246201 := bstep (se 2 (by rfl) ⟨4217325, by rfl⟩ : syracuseStep 11246201 = 8434651) B8434651
theorem B7497467 : Blo 2221435 7497467 := bstep (se 1 (by rfl) ⟨5623100, by rfl⟩ : syracuseStep 7497467 = 11246201) B11246201
theorem B4998311 : Blo 2221435 4998311 := bstep (se 1 (by rfl) ⟨3748733, by rfl⟩ : syracuseStep 4998311 = 7497467) B7497467
theorem B3332207 : Blo 2221435 3332207 := bstep (se 1 (by rfl) ⟨2499155, by rfl⟩ : syracuseStep 3332207 = 4998311) B4998311
theorem B2221471 : Blo 2221435 2221471 := bstep (se 1 (by rfl) ⟨1666103, by rfl⟩ : syracuseStep 2221471 = 3332207) B3332207
theorem B3332213 : Blo 2221435 3332213 := bbase (se 5 (by rfl) ⟨156197, by rfl⟩ : syracuseStep 3332213 = 312395) (by norm_num)
theorem B2221475 : Blo 2221435 2221475 := bstep (se 1 (by rfl) ⟨1666106, by rfl⟩ : syracuseStep 2221475 = 3332213) B3332213
theorem B4217341 : Blo 2221435 4217341 := bbase (se 3 (by rfl) ⟨790751, by rfl⟩ : syracuseStep 4217341 = 1581503) (by norm_num)
theorem B5623121 : Blo 2221435 5623121 := bstep (se 2 (by rfl) ⟨2108670, by rfl⟩ : syracuseStep 5623121 = 4217341) B4217341
theorem B3748747 : Blo 2221435 3748747 := bstep (se 1 (by rfl) ⟨2811560, by rfl⟩ : syracuseStep 3748747 = 5623121) B5623121
theorem B4998329 : Blo 2221435 4998329 := bstep (se 2 (by rfl) ⟨1874373, by rfl⟩ : syracuseStep 4998329 = 3748747) B3748747
theorem B3332219 : Blo 2221435 3332219 := bstep (se 1 (by rfl) ⟨2499164, by rfl⟩ : syracuseStep 3332219 = 4998329) B4998329
theorem B2221479 : Blo 2221435 2221479 := bstep (se 1 (by rfl) ⟨1666109, by rfl⟩ : syracuseStep 2221479 = 3332219) B3332219
theorem B2499169 : Blo 2221435 2499169 := bbase (se 2 (by rfl) ⟨937188, by rfl⟩ : syracuseStep 2499169 = 1874377) (by norm_num)
theorem B3332225 : Blo 2221435 3332225 := bstep (se 2 (by rfl) ⟨1249584, by rfl⟩ : syracuseStep 3332225 = 2499169) B2499169
theorem B2221483 : Blo 2221435 2221483 := bstep (se 1 (by rfl) ⟨1666112, by rfl⟩ : syracuseStep 2221483 = 3332225) B3332225
theorem B5623141 : Blo 2221435 5623141 := bbase (se 4 (by rfl) ⟨527169, by rfl⟩ : syracuseStep 5623141 = 1054339) (by norm_num)
theorem B7497521 : Blo 2221435 7497521 := bstep (se 2 (by rfl) ⟨2811570, by rfl⟩ : syracuseStep 7497521 = 5623141) B5623141
theorem B4998347 : Blo 2221435 4998347 := bstep (se 1 (by rfl) ⟨3748760, by rfl⟩ : syracuseStep 4998347 = 7497521) B7497521
theorem B3332231 : Blo 2221435 3332231 := bstep (se 1 (by rfl) ⟨2499173, by rfl⟩ : syracuseStep 3332231 = 4998347) B4998347
theorem B2221487 : Blo 2221435 2221487 := bstep (se 1 (by rfl) ⟨1666115, by rfl⟩ : syracuseStep 2221487 = 3332231) B3332231
theorem B3332237 : Blo 2221435 3332237 := bbase (se 3 (by rfl) ⟨624794, by rfl⟩ : syracuseStep 3332237 = 1249589) (by norm_num)
theorem B2221491 : Blo 2221435 2221491 := bstep (se 1 (by rfl) ⟨1666118, by rfl⟩ : syracuseStep 2221491 = 3332237) B3332237
theorem B4998365 : Blo 2221435 4998365 := bbase (se 3 (by rfl) ⟨937193, by rfl⟩ : syracuseStep 4998365 = 1874387) (by norm_num)
theorem B3332243 : Blo 2221435 3332243 := bstep (se 1 (by rfl) ⟨2499182, by rfl⟩ : syracuseStep 3332243 = 4998365) B4998365
theorem B2221495 : Blo 2221435 2221495 := bstep (se 1 (by rfl) ⟨1666121, by rfl⟩ : syracuseStep 2221495 = 3332243) B3332243
theorem B3748781 : Blo 2221435 3748781 := bbase (se 3 (by rfl) ⟨702896, by rfl⟩ : syracuseStep 3748781 = 1405793) (by norm_num)
theorem B2499187 : Blo 2221435 2499187 := bstep (se 1 (by rfl) ⟨1874390, by rfl⟩ : syracuseStep 2499187 = 3748781) B3748781
theorem B3332249 : Blo 2221435 3332249 := bstep (se 2 (by rfl) ⟨1249593, by rfl⟩ : syracuseStep 3332249 = 2499187) B2499187
theorem B2221499 : Blo 2221435 2221499 := bstep (se 1 (by rfl) ⟨1666124, by rfl⟩ : syracuseStep 2221499 = 3332249) B3332249
theorem B5410453 : Blo 2221435 5410453 := bbase (se 6 (by rfl) ⟨126807, by rfl⟩ : syracuseStep 5410453 = 253615) (by norm_num)
theorem B7213937 : Blo 2221435 7213937 := bstep (se 2 (by rfl) ⟨2705226, by rfl⟩ : syracuseStep 7213937 = 5410453) B5410453
theorem B76948661 : Blo 2221435 76948661 := bstep (se 5 (by rfl) ⟨3606968, by rfl⟩ : syracuseStep 76948661 = 7213937) B7213937
theorem B205196429 : Blo 2221435 205196429 := bstep (se 3 (by rfl) ⟨38474330, by rfl⟩ : syracuseStep 205196429 = 76948661) B76948661
theorem B547190477 : Blo 2221435 547190477 := bstep (se 3 (by rfl) ⟨102598214, by rfl⟩ : syracuseStep 547190477 = 205196429) B205196429
theorem B364793651 : Blo 2221435 364793651 := bstep (se 1 (by rfl) ⟨273595238, by rfl⟩ : syracuseStep 364793651 = 547190477) B547190477
theorem B243195767 : Blo 2221435 243195767 := bstep (se 1 (by rfl) ⟨182396825, by rfl⟩ : syracuseStep 243195767 = 364793651) B364793651
theorem B162130511 : Blo 2221435 162130511 := bstep (se 1 (by rfl) ⟨121597883, by rfl⟩ : syracuseStep 162130511 = 243195767) B243195767
theorem B108087007 : Blo 2221435 108087007 := bstep (se 1 (by rfl) ⟨81065255, by rfl⟩ : syracuseStep 108087007 = 162130511) B162130511
theorem B144116009 : Blo 2221435 144116009 := bstep (se 2 (by rfl) ⟨54043503, by rfl⟩ : syracuseStep 144116009 = 108087007) B108087007
theorem B96077339 : Blo 2221435 96077339 := bstep (se 1 (by rfl) ⟨72058004, by rfl⟩ : syracuseStep 96077339 = 144116009) B144116009
theorem B64051559 : Blo 2221435 64051559 := bstep (se 1 (by rfl) ⟨48038669, by rfl⟩ : syracuseStep 64051559 = 96077339) B96077339
theorem B42701039 : Blo 2221435 42701039 := bstep (se 1 (by rfl) ⟨32025779, by rfl⟩ : syracuseStep 42701039 = 64051559) B64051559
theorem B28467359 : Blo 2221435 28467359 := bstep (se 1 (by rfl) ⟨21350519, by rfl⟩ : syracuseStep 28467359 = 42701039) B42701039
theorem B18978239 : Blo 2221435 18978239 := bstep (se 1 (by rfl) ⟨14233679, by rfl⟩ : syracuseStep 18978239 = 28467359) B28467359
theorem B12652159 : Blo 2221435 12652159 := bstep (se 1 (by rfl) ⟨9489119, by rfl⟩ : syracuseStep 12652159 = 18978239) B18978239
theorem B16869545 : Blo 2221435 16869545 := bstep (se 2 (by rfl) ⟨6326079, by rfl⟩ : syracuseStep 16869545 = 12652159) B12652159
theorem B11246363 : Blo 2221435 11246363 := bstep (se 1 (by rfl) ⟨8434772, by rfl⟩ : syracuseStep 11246363 = 16869545) B16869545
theorem B7497575 : Blo 2221435 7497575 := bstep (se 1 (by rfl) ⟨5623181, by rfl⟩ : syracuseStep 7497575 = 11246363) B11246363
theorem B4998383 : Blo 2221435 4998383 := bstep (se 1 (by rfl) ⟨3748787, by rfl⟩ : syracuseStep 4998383 = 7497575) B7497575
theorem B3332255 : Blo 2221435 3332255 := bstep (se 1 (by rfl) ⟨2499191, by rfl⟩ : syracuseStep 3332255 = 4998383) B4998383
theorem B2221503 : Blo 2221435 2221503 := bstep (se 1 (by rfl) ⟨1666127, by rfl⟩ : syracuseStep 2221503 = 3332255) B3332255
theorem B3332261 : Blo 2221435 3332261 := bbase (se 4 (by rfl) ⟨312399, by rfl⟩ : syracuseStep 3332261 = 624799) (by norm_num)
theorem B2221507 : Blo 2221435 2221507 := bstep (se 1 (by rfl) ⟨1666130, by rfl⟩ : syracuseStep 2221507 = 3332261) B3332261
theorem B2811601 : Blo 2221435 2811601 := bbase (se 2 (by rfl) ⟨1054350, by rfl⟩ : syracuseStep 2811601 = 2108701) (by norm_num)
theorem B3748801 : Blo 2221435 3748801 := bstep (se 2 (by rfl) ⟨1405800, by rfl⟩ : syracuseStep 3748801 = 2811601) B2811601
theorem B4998401 : Blo 2221435 4998401 := bstep (se 2 (by rfl) ⟨1874400, by rfl⟩ : syracuseStep 4998401 = 3748801) B3748801
theorem B3332267 : Blo 2221435 3332267 := bstep (se 1 (by rfl) ⟨2499200, by rfl⟩ : syracuseStep 3332267 = 4998401) B4998401
theorem B2221511 : Blo 2221435 2221511 := bstep (se 1 (by rfl) ⟨1666133, by rfl⟩ : syracuseStep 2221511 = 3332267) B3332267
theorem B2499205 : Blo 2221435 2499205 := bbase (se 4 (by rfl) ⟨234300, by rfl⟩ : syracuseStep 2499205 = 468601) (by norm_num)
theorem B3332273 : Blo 2221435 3332273 := bstep (se 2 (by rfl) ⟨1249602, by rfl⟩ : syracuseStep 3332273 = 2499205) B2499205
theorem B2221515 : Blo 2221435 2221515 := bstep (se 1 (by rfl) ⟨1666136, by rfl⟩ : syracuseStep 2221515 = 3332273) B3332273
theorem B4003253 : Blo 2221435 4003253 := bbase (se 5 (by rfl) ⟨187652, by rfl⟩ : syracuseStep 4003253 = 375305) (by norm_num)
theorem B2668835 : Blo 2221435 2668835 := bstep (se 1 (by rfl) ⟨2001626, by rfl⟩ : syracuseStep 2668835 = 4003253) B4003253
theorem B7116893 : Blo 2221435 7116893 := bstep (se 3 (by rfl) ⟨1334417, by rfl⟩ : syracuseStep 7116893 = 2668835) B2668835
theorem B4744595 : Blo 2221435 4744595 := bstep (se 1 (by rfl) ⟨3558446, by rfl⟩ : syracuseStep 4744595 = 7116893) B7116893
theorem B3163063 : Blo 2221435 3163063 := bstep (se 1 (by rfl) ⟨2372297, by rfl⟩ : syracuseStep 3163063 = 4744595) B4744595
theorem B4217417 : Blo 2221435 4217417 := bstep (se 2 (by rfl) ⟨1581531, by rfl⟩ : syracuseStep 4217417 = 3163063) B3163063
theorem B2811611 : Blo 2221435 2811611 := bstep (se 1 (by rfl) ⟨2108708, by rfl⟩ : syracuseStep 2811611 = 4217417) B4217417
theorem B7497629 : Blo 2221435 7497629 := bstep (se 3 (by rfl) ⟨1405805, by rfl⟩ : syracuseStep 7497629 = 2811611) B2811611
theorem B4998419 : Blo 2221435 4998419 := bstep (se 1 (by rfl) ⟨3748814, by rfl⟩ : syracuseStep 4998419 = 7497629) B7497629
theorem B3332279 : Blo 2221435 3332279 := bstep (se 1 (by rfl) ⟨2499209, by rfl⟩ : syracuseStep 3332279 = 4998419) B4998419
theorem B2221519 : Blo 2221435 2221519 := bstep (se 1 (by rfl) ⟨1666139, by rfl⟩ : syracuseStep 2221519 = 3332279) B3332279
theorem B3332285 : Blo 2221435 3332285 := bbase (se 3 (by rfl) ⟨624803, by rfl⟩ : syracuseStep 3332285 = 1249607) (by norm_num)
theorem B2221523 : Blo 2221435 2221523 := bstep (se 1 (by rfl) ⟨1666142, by rfl⟩ : syracuseStep 2221523 = 3332285) B3332285
theorem B4998437 : Blo 2221435 4998437 := bbase (se 4 (by rfl) ⟨468603, by rfl⟩ : syracuseStep 4998437 = 937207) (by norm_num)
theorem B3332291 : Blo 2221435 3332291 := bstep (se 1 (by rfl) ⟨2499218, by rfl⟩ : syracuseStep 3332291 = 4998437) B4998437
theorem B2221527 : Blo 2221435 2221527 := bstep (se 1 (by rfl) ⟨1666145, by rfl⟩ : syracuseStep 2221527 = 3332291) B3332291
theorem B5623253 : Blo 2221435 5623253 := bbase (se 7 (by rfl) ⟨65897, by rfl⟩ : syracuseStep 5623253 = 131795) (by norm_num)
theorem B3748835 : Blo 2221435 3748835 := bstep (se 1 (by rfl) ⟨2811626, by rfl⟩ : syracuseStep 3748835 = 5623253) B5623253
theorem B2499223 : Blo 2221435 2499223 := bstep (se 1 (by rfl) ⟨1874417, by rfl⟩ : syracuseStep 2499223 = 3748835) B3748835
theorem B3332297 : Blo 2221435 3332297 := bstep (se 2 (by rfl) ⟨1249611, by rfl⟩ : syracuseStep 3332297 = 2499223) B2499223
theorem B2221531 : Blo 2221435 2221531 := bstep (se 1 (by rfl) ⟨1666148, by rfl⟩ : syracuseStep 2221531 = 3332297) B3332297
theorem B5066653 : Blo 2221435 5066653 := bbase (se 3 (by rfl) ⟨949997, by rfl⟩ : syracuseStep 5066653 = 1899995) (by norm_num)
theorem B6755537 : Blo 2221435 6755537 := bstep (se 2 (by rfl) ⟨2533326, by rfl⟩ : syracuseStep 6755537 = 5066653) B5066653
theorem B4503691 : Blo 2221435 4503691 := bstep (se 1 (by rfl) ⟨3377768, by rfl⟩ : syracuseStep 4503691 = 6755537) B6755537
theorem B24019685 : Blo 2221435 24019685 := bstep (se 4 (by rfl) ⟨2251845, by rfl⟩ : syracuseStep 24019685 = 4503691) B4503691
theorem B16013123 : Blo 2221435 16013123 := bstep (se 1 (by rfl) ⟨12009842, by rfl⟩ : syracuseStep 16013123 = 24019685) B24019685
theorem B10675415 : Blo 2221435 10675415 := bstep (se 1 (by rfl) ⟨8006561, by rfl⟩ : syracuseStep 10675415 = 16013123) B16013123
theorem B7116943 : Blo 2221435 7116943 := bstep (se 1 (by rfl) ⟨5337707, by rfl⟩ : syracuseStep 7116943 = 10675415) B10675415
theorem B9489257 : Blo 2221435 9489257 := bstep (se 2 (by rfl) ⟨3558471, by rfl⟩ : syracuseStep 9489257 = 7116943) B7116943
theorem B6326171 : Blo 2221435 6326171 := bstep (se 1 (by rfl) ⟨4744628, by rfl⟩ : syracuseStep 6326171 = 9489257) B9489257
theorem B4217447 : Blo 2221435 4217447 := bstep (se 1 (by rfl) ⟨3163085, by rfl⟩ : syracuseStep 4217447 = 6326171) B6326171
theorem B11246525 : Blo 2221435 11246525 := bstep (se 3 (by rfl) ⟨2108723, by rfl⟩ : syracuseStep 11246525 = 4217447) B4217447
theorem B7497683 : Blo 2221435 7497683 := bstep (se 1 (by rfl) ⟨5623262, by rfl⟩ : syracuseStep 7497683 = 11246525) B11246525
theorem B4998455 : Blo 2221435 4998455 := bstep (se 1 (by rfl) ⟨3748841, by rfl⟩ : syracuseStep 4998455 = 7497683) B7497683
theorem B3332303 : Blo 2221435 3332303 := bstep (se 1 (by rfl) ⟨2499227, by rfl⟩ : syracuseStep 3332303 = 4998455) B4998455
theorem B2221535 : Blo 2221435 2221535 := bstep (se 1 (by rfl) ⟨1666151, by rfl⟩ : syracuseStep 2221535 = 3332303) B3332303
theorem B3332309 : Blo 2221435 3332309 := bbase (se 7 (by rfl) ⟨39050, by rfl⟩ : syracuseStep 3332309 = 78101) (by norm_num)
theorem B2221539 : Blo 2221435 2221539 := bstep (se 1 (by rfl) ⟨1666154, by rfl⟩ : syracuseStep 2221539 = 3332309) B3332309
theorem B3558485 : Blo 2221435 3558485 := bbase (se 8 (by rfl) ⟨20850, by rfl⟩ : syracuseStep 3558485 = 41701) (by norm_num)
theorem B2372323 : Blo 2221435 2372323 := bstep (se 1 (by rfl) ⟨1779242, by rfl⟩ : syracuseStep 2372323 = 3558485) B3558485
theorem B3163097 : Blo 2221435 3163097 := bstep (se 2 (by rfl) ⟨1186161, by rfl⟩ : syracuseStep 3163097 = 2372323) B2372323
theorem B8434925 : Blo 2221435 8434925 := bstep (se 3 (by rfl) ⟨1581548, by rfl⟩ : syracuseStep 8434925 = 3163097) B3163097
theorem B5623283 : Blo 2221435 5623283 := bstep (se 1 (by rfl) ⟨4217462, by rfl⟩ : syracuseStep 5623283 = 8434925) B8434925
theorem B3748855 : Blo 2221435 3748855 := bstep (se 1 (by rfl) ⟨2811641, by rfl⟩ : syracuseStep 3748855 = 5623283) B5623283
theorem B4998473 : Blo 2221435 4998473 := bstep (se 2 (by rfl) ⟨1874427, by rfl⟩ : syracuseStep 4998473 = 3748855) B3748855
theorem B3332315 : Blo 2221435 3332315 := bstep (se 1 (by rfl) ⟨2499236, by rfl⟩ : syracuseStep 3332315 = 4998473) B4998473
theorem B2221543 : Blo 2221435 2221543 := bstep (se 1 (by rfl) ⟨1666157, by rfl⟩ : syracuseStep 2221543 = 3332315) B3332315
theorem B2499241 : Blo 2221435 2499241 := bbase (se 2 (by rfl) ⟨937215, by rfl⟩ : syracuseStep 2499241 = 1874431) (by norm_num)
theorem B3332321 : Blo 2221435 3332321 := bstep (se 2 (by rfl) ⟨1249620, by rfl⟩ : syracuseStep 3332321 = 2499241) B2499241
theorem B2221547 : Blo 2221435 2221547 := bstep (se 1 (by rfl) ⟨1666160, by rfl⟩ : syracuseStep 2221547 = 3332321) B3332321
theorem B2668873 : Blo 2221435 2668873 := bbase (se 2 (by rfl) ⟨1000827, by rfl⟩ : syracuseStep 2668873 = 2001655) (by norm_num)
theorem B3558497 : Blo 2221435 3558497 := bstep (se 2 (by rfl) ⟨1334436, by rfl⟩ : syracuseStep 3558497 = 2668873) B2668873
theorem B9489325 : Blo 2221435 9489325 := bstep (se 3 (by rfl) ⟨1779248, by rfl⟩ : syracuseStep 9489325 = 3558497) B3558497
theorem B12652433 : Blo 2221435 12652433 := bstep (se 2 (by rfl) ⟨4744662, by rfl⟩ : syracuseStep 12652433 = 9489325) B9489325
theorem B8434955 : Blo 2221435 8434955 := bstep (se 1 (by rfl) ⟨6326216, by rfl⟩ : syracuseStep 8434955 = 12652433) B12652433
theorem B5623303 : Blo 2221435 5623303 := bstep (se 1 (by rfl) ⟨4217477, by rfl⟩ : syracuseStep 5623303 = 8434955) B8434955
theorem B7497737 : Blo 2221435 7497737 := bstep (se 2 (by rfl) ⟨2811651, by rfl⟩ : syracuseStep 7497737 = 5623303) B5623303
theorem B4998491 : Blo 2221435 4998491 := bstep (se 1 (by rfl) ⟨3748868, by rfl⟩ : syracuseStep 4998491 = 7497737) B7497737
theorem B3332327 : Blo 2221435 3332327 := bstep (se 1 (by rfl) ⟨2499245, by rfl⟩ : syracuseStep 3332327 = 4998491) B4998491
theorem B2221551 : Blo 2221435 2221551 := bstep (se 1 (by rfl) ⟨1666163, by rfl⟩ : syracuseStep 2221551 = 3332327) B3332327
theorem B3332333 : Blo 2221435 3332333 := bbase (se 3 (by rfl) ⟨624812, by rfl⟩ : syracuseStep 3332333 = 1249625) (by norm_num)
theorem B2221555 : Blo 2221435 2221555 := bstep (se 1 (by rfl) ⟨1666166, by rfl⟩ : syracuseStep 2221555 = 3332333) B3332333
theorem B4998509 : Blo 2221435 4998509 := bbase (se 3 (by rfl) ⟨937220, by rfl⟩ : syracuseStep 4998509 = 1874441) (by norm_num)
theorem B3332339 : Blo 2221435 3332339 := bstep (se 1 (by rfl) ⟨2499254, by rfl⟩ : syracuseStep 3332339 = 4998509) B4998509
theorem B2221559 : Blo 2221435 2221559 := bstep (se 1 (by rfl) ⟨1666169, by rfl⟩ : syracuseStep 2221559 = 3332339) B3332339
theorem B4217501 : Blo 2221435 4217501 := bbase (se 3 (by rfl) ⟨790781, by rfl⟩ : syracuseStep 4217501 = 1581563) (by norm_num)
theorem B2811667 : Blo 2221435 2811667 := bstep (se 1 (by rfl) ⟨2108750, by rfl⟩ : syracuseStep 2811667 = 4217501) B4217501
theorem B3748889 : Blo 2221435 3748889 := bstep (se 2 (by rfl) ⟨1405833, by rfl⟩ : syracuseStep 3748889 = 2811667) B2811667
theorem B2499259 : Blo 2221435 2499259 := bstep (se 1 (by rfl) ⟨1874444, by rfl⟩ : syracuseStep 2499259 = 3748889) B3748889
theorem B3332345 : Blo 2221435 3332345 := bstep (se 2 (by rfl) ⟨1249629, by rfl⟩ : syracuseStep 3332345 = 2499259) B2499259
theorem B2221563 : Blo 2221435 2221563 := bstep (se 1 (by rfl) ⟨1666172, by rfl⟩ : syracuseStep 2221563 = 3332345) B3332345
theorem B10821221 : Blo 2221435 10821221 := bbase (se 4 (by rfl) ⟨1014489, by rfl⟩ : syracuseStep 10821221 = 2028979) (by norm_num)
theorem B7214147 : Blo 2221435 7214147 := bstep (se 1 (by rfl) ⟨5410610, by rfl⟩ : syracuseStep 7214147 = 10821221) B10821221
theorem B4809431 : Blo 2221435 4809431 := bstep (se 1 (by rfl) ⟨3607073, by rfl⟩ : syracuseStep 4809431 = 7214147) B7214147
theorem B3206287 : Blo 2221435 3206287 := bstep (se 1 (by rfl) ⟨2404715, by rfl⟩ : syracuseStep 3206287 = 4809431) B4809431
theorem B17100197 : Blo 2221435 17100197 := bstep (se 4 (by rfl) ⟨1603143, by rfl⟩ : syracuseStep 17100197 = 3206287) B3206287
theorem B11400131 : Blo 2221435 11400131 := bstep (se 1 (by rfl) ⟨8550098, by rfl⟩ : syracuseStep 11400131 = 17100197) B17100197
theorem B7600087 : Blo 2221435 7600087 := bstep (se 1 (by rfl) ⟨5700065, by rfl⟩ : syracuseStep 7600087 = 11400131) B11400131
theorem B40533797 : Blo 2221435 40533797 := bstep (se 4 (by rfl) ⟨3800043, by rfl⟩ : syracuseStep 40533797 = 7600087) B7600087
theorem B27022531 : Blo 2221435 27022531 := bstep (se 1 (by rfl) ⟨20266898, by rfl⟩ : syracuseStep 27022531 = 40533797) B40533797
theorem B36030041 : Blo 2221435 36030041 := bstep (se 2 (by rfl) ⟨13511265, by rfl⟩ : syracuseStep 36030041 = 27022531) B27022531
theorem B24020027 : Blo 2221435 24020027 := bstep (se 1 (by rfl) ⟨18015020, by rfl⟩ : syracuseStep 24020027 = 36030041) B36030041
theorem B16013351 : Blo 2221435 16013351 := bstep (se 1 (by rfl) ⟨12010013, by rfl⟩ : syracuseStep 16013351 = 24020027) B24020027
theorem B10675567 : Blo 2221435 10675567 := bstep (se 1 (by rfl) ⟨8006675, by rfl⟩ : syracuseStep 10675567 = 16013351) B16013351
theorem B56936357 : Blo 2221435 56936357 := bstep (se 4 (by rfl) ⟨5337783, by rfl⟩ : syracuseStep 56936357 = 10675567) B10675567
theorem B37957571 : Blo 2221435 37957571 := bstep (se 1 (by rfl) ⟨28468178, by rfl⟩ : syracuseStep 37957571 = 56936357) B56936357
theorem B25305047 : Blo 2221435 25305047 := bstep (se 1 (by rfl) ⟨18978785, by rfl⟩ : syracuseStep 25305047 = 37957571) B37957571
theorem B16870031 : Blo 2221435 16870031 := bstep (se 1 (by rfl) ⟨12652523, by rfl⟩ : syracuseStep 16870031 = 25305047) B25305047
theorem B11246687 : Blo 2221435 11246687 := bstep (se 1 (by rfl) ⟨8435015, by rfl⟩ : syracuseStep 11246687 = 16870031) B16870031
theorem B7497791 : Blo 2221435 7497791 := bstep (se 1 (by rfl) ⟨5623343, by rfl⟩ : syracuseStep 7497791 = 11246687) B11246687
theorem B4998527 : Blo 2221435 4998527 := bstep (se 1 (by rfl) ⟨3748895, by rfl⟩ : syracuseStep 4998527 = 7497791) B7497791
theorem B3332351 : Blo 2221435 3332351 := bstep (se 1 (by rfl) ⟨2499263, by rfl⟩ : syracuseStep 3332351 = 4998527) B4998527
theorem B2221567 : Blo 2221435 2221567 := bstep (se 1 (by rfl) ⟨1666175, by rfl⟩ : syracuseStep 2221567 = 3332351) B3332351
theorem B3332357 : Blo 2221435 3332357 := bbase (se 4 (by rfl) ⟨312408, by rfl⟩ : syracuseStep 3332357 = 624817) (by norm_num)
theorem B2221571 : Blo 2221435 2221571 := bstep (se 1 (by rfl) ⟨1666178, by rfl⟩ : syracuseStep 2221571 = 3332357) B3332357
theorem B3748909 : Blo 2221435 3748909 := bbase (se 3 (by rfl) ⟨702920, by rfl⟩ : syracuseStep 3748909 = 1405841) (by norm_num)
theorem B4998545 : Blo 2221435 4998545 := bstep (se 2 (by rfl) ⟨1874454, by rfl⟩ : syracuseStep 4998545 = 3748909) B3748909
theorem B3332363 : Blo 2221435 3332363 := bstep (se 1 (by rfl) ⟨2499272, by rfl⟩ : syracuseStep 3332363 = 4998545) B4998545
theorem B2221575 : Blo 2221435 2221575 := bstep (se 1 (by rfl) ⟨1666181, by rfl⟩ : syracuseStep 2221575 = 3332363) B3332363
theorem B2499277 : Blo 2221435 2499277 := bbase (se 3 (by rfl) ⟨468614, by rfl⟩ : syracuseStep 2499277 = 937229) (by norm_num)
theorem B3332369 : Blo 2221435 3332369 := bstep (se 2 (by rfl) ⟨1249638, by rfl⟩ : syracuseStep 3332369 = 2499277) B2499277
theorem B2221579 : Blo 2221435 2221579 := bstep (se 1 (by rfl) ⟨1666184, by rfl⟩ : syracuseStep 2221579 = 3332369) B3332369
theorem B7497845 : Blo 2221435 7497845 := bbase (se 5 (by rfl) ⟨351461, by rfl⟩ : syracuseStep 7497845 = 702923) (by norm_num)
theorem B4998563 : Blo 2221435 4998563 := bstep (se 1 (by rfl) ⟨3748922, by rfl⟩ : syracuseStep 4998563 = 7497845) B7497845
theorem B3332375 : Blo 2221435 3332375 := bstep (se 1 (by rfl) ⟨2499281, by rfl⟩ : syracuseStep 3332375 = 4998563) B4998563
theorem B2221583 : Blo 2221435 2221583 := bstep (se 1 (by rfl) ⟨1666187, by rfl⟩ : syracuseStep 2221583 = 3332375) B3332375
theorem B3332381 : Blo 2221435 3332381 := bbase (se 3 (by rfl) ⟨624821, by rfl⟩ : syracuseStep 3332381 = 1249643) (by norm_num)
theorem B2221587 : Blo 2221435 2221587 := bstep (se 1 (by rfl) ⟨1666190, by rfl⟩ : syracuseStep 2221587 = 3332381) B3332381
theorem B4998581 : Blo 2221435 4998581 := bbase (se 5 (by rfl) ⟨234308, by rfl⟩ : syracuseStep 4998581 = 468617) (by norm_num)
theorem B3332387 : Blo 2221435 3332387 := bstep (se 1 (by rfl) ⟨2499290, by rfl⟩ : syracuseStep 3332387 = 4998581) B4998581
theorem B2221591 : Blo 2221435 2221591 := bstep (se 1 (by rfl) ⟨1666193, by rfl⟩ : syracuseStep 2221591 = 3332387) B3332387
theorem B4744757 : Blo 2221435 4744757 := bbase (se 5 (by rfl) ⟨222410, by rfl⟩ : syracuseStep 4744757 = 444821) (by norm_num)
theorem B12652685 : Blo 2221435 12652685 := bstep (se 3 (by rfl) ⟨2372378, by rfl⟩ : syracuseStep 12652685 = 4744757) B4744757
theorem B8435123 : Blo 2221435 8435123 := bstep (se 1 (by rfl) ⟨6326342, by rfl⟩ : syracuseStep 8435123 = 12652685) B12652685
theorem B5623415 : Blo 2221435 5623415 := bstep (se 1 (by rfl) ⟨4217561, by rfl⟩ : syracuseStep 5623415 = 8435123) B8435123
theorem B3748943 : Blo 2221435 3748943 := bstep (se 1 (by rfl) ⟨2811707, by rfl⟩ : syracuseStep 3748943 = 5623415) B5623415
theorem B2499295 : Blo 2221435 2499295 := bstep (se 1 (by rfl) ⟨1874471, by rfl⟩ : syracuseStep 2499295 = 3748943) B3748943
theorem B3332393 : Blo 2221435 3332393 := bstep (se 2 (by rfl) ⟨1249647, by rfl⟩ : syracuseStep 3332393 = 2499295) B2499295
theorem B2221595 : Blo 2221435 2221595 := bstep (se 1 (by rfl) ⟨1666196, by rfl⟩ : syracuseStep 2221595 = 3332393) B3332393
theorem B4744765 : Blo 2221435 4744765 := bbase (se 3 (by rfl) ⟨889643, by rfl⟩ : syracuseStep 4744765 = 1779287) (by norm_num)
theorem B6326353 : Blo 2221435 6326353 := bstep (se 2 (by rfl) ⟨2372382, by rfl⟩ : syracuseStep 6326353 = 4744765) B4744765
theorem B8435137 : Blo 2221435 8435137 := bstep (se 2 (by rfl) ⟨3163176, by rfl⟩ : syracuseStep 8435137 = 6326353) B6326353
theorem B11246849 : Blo 2221435 11246849 := bstep (se 2 (by rfl) ⟨4217568, by rfl⟩ : syracuseStep 11246849 = 8435137) B8435137
theorem B7497899 : Blo 2221435 7497899 := bstep (se 1 (by rfl) ⟨5623424, by rfl⟩ : syracuseStep 7497899 = 11246849) B11246849
theorem B4998599 : Blo 2221435 4998599 := bstep (se 1 (by rfl) ⟨3748949, by rfl⟩ : syracuseStep 4998599 = 7497899) B7497899
theorem B3332399 : Blo 2221435 3332399 := bstep (se 1 (by rfl) ⟨2499299, by rfl⟩ : syracuseStep 3332399 = 4998599) B4998599
theorem B2221599 : Blo 2221435 2221599 := bstep (se 1 (by rfl) ⟨1666199, by rfl⟩ : syracuseStep 2221599 = 3332399) B3332399
theorem B3332405 : Blo 2221435 3332405 := bbase (se 5 (by rfl) ⟨156206, by rfl⟩ : syracuseStep 3332405 = 312413) (by norm_num)
theorem B2221603 : Blo 2221435 2221603 := bstep (se 1 (by rfl) ⟨1666202, by rfl⟩ : syracuseStep 2221603 = 3332405) B3332405
theorem B5623445 : Blo 2221435 5623445 := bbase (se 6 (by rfl) ⟨131799, by rfl⟩ : syracuseStep 5623445 = 263599) (by norm_num)
theorem B3748963 : Blo 2221435 3748963 := bstep (se 1 (by rfl) ⟨2811722, by rfl⟩ : syracuseStep 3748963 = 5623445) B5623445
theorem B4998617 : Blo 2221435 4998617 := bstep (se 2 (by rfl) ⟨1874481, by rfl⟩ : syracuseStep 4998617 = 3748963) B3748963
theorem B3332411 : Blo 2221435 3332411 := bstep (se 1 (by rfl) ⟨2499308, by rfl⟩ : syracuseStep 3332411 = 4998617) B4998617
theorem B2221607 : Blo 2221435 2221607 := bstep (se 1 (by rfl) ⟨1666205, by rfl⟩ : syracuseStep 2221607 = 3332411) B3332411
theorem B2499313 : Blo 2221435 2499313 := bbase (se 2 (by rfl) ⟨937242, by rfl⟩ : syracuseStep 2499313 = 1874485) (by norm_num)
theorem B3332417 : Blo 2221435 3332417 := bstep (se 2 (by rfl) ⟨1249656, by rfl⟩ : syracuseStep 3332417 = 2499313) B2499313
theorem B2221611 : Blo 2221435 2221611 := bstep (se 1 (by rfl) ⟨1666208, by rfl⟩ : syracuseStep 2221611 = 3332417) B3332417
theorem B22800757 : Blo 2221435 22800757 := bbase (se 5 (by rfl) ⟨1068785, by rfl⟩ : syracuseStep 22800757 = 2137571) (by norm_num)
theorem B30401009 : Blo 2221435 30401009 := bstep (se 2 (by rfl) ⟨11400378, by rfl⟩ : syracuseStep 30401009 = 22800757) B22800757
theorem B20267339 : Blo 2221435 20267339 := bstep (se 1 (by rfl) ⟨15200504, by rfl⟩ : syracuseStep 20267339 = 30401009) B30401009
theorem B54046237 : Blo 2221435 54046237 := bstep (se 3 (by rfl) ⟨10133669, by rfl⟩ : syracuseStep 54046237 = 20267339) B20267339
theorem B72061649 : Blo 2221435 72061649 := bstep (se 2 (by rfl) ⟨27023118, by rfl⟩ : syracuseStep 72061649 = 54046237) B54046237
theorem B48041099 : Blo 2221435 48041099 := bstep (se 1 (by rfl) ⟨36030824, by rfl⟩ : syracuseStep 48041099 = 72061649) B72061649
theorem B32027399 : Blo 2221435 32027399 := bstep (se 1 (by rfl) ⟨24020549, by rfl⟩ : syracuseStep 32027399 = 48041099) B48041099
theorem B21351599 : Blo 2221435 21351599 := bstep (se 1 (by rfl) ⟨16013699, by rfl⟩ : syracuseStep 21351599 = 32027399) B32027399
theorem B14234399 : Blo 2221435 14234399 := bstep (se 1 (by rfl) ⟨10675799, by rfl⟩ : syracuseStep 14234399 = 21351599) B21351599
theorem B9489599 : Blo 2221435 9489599 := bstep (se 1 (by rfl) ⟨7117199, by rfl⟩ : syracuseStep 9489599 = 14234399) B14234399
theorem B6326399 : Blo 2221435 6326399 := bstep (se 1 (by rfl) ⟨4744799, by rfl⟩ : syracuseStep 6326399 = 9489599) B9489599
theorem B4217599 : Blo 2221435 4217599 := bstep (se 1 (by rfl) ⟨3163199, by rfl⟩ : syracuseStep 4217599 = 6326399) B6326399
theorem B5623465 : Blo 2221435 5623465 := bstep (se 2 (by rfl) ⟨2108799, by rfl⟩ : syracuseStep 5623465 = 4217599) B4217599
theorem B7497953 : Blo 2221435 7497953 := bstep (se 2 (by rfl) ⟨2811732, by rfl⟩ : syracuseStep 7497953 = 5623465) B5623465
theorem B4998635 : Blo 2221435 4998635 := bstep (se 1 (by rfl) ⟨3748976, by rfl⟩ : syracuseStep 4998635 = 7497953) B7497953
theorem B3332423 : Blo 2221435 3332423 := bstep (se 1 (by rfl) ⟨2499317, by rfl⟩ : syracuseStep 3332423 = 4998635) B4998635
theorem B2221615 : Blo 2221435 2221615 := bstep (se 1 (by rfl) ⟨1666211, by rfl⟩ : syracuseStep 2221615 = 3332423) B3332423
theorem B3332429 : Blo 2221435 3332429 := bbase (se 3 (by rfl) ⟨624830, by rfl⟩ : syracuseStep 3332429 = 1249661) (by norm_num)
theorem B2221619 : Blo 2221435 2221619 := bstep (se 1 (by rfl) ⟨1666214, by rfl⟩ : syracuseStep 2221619 = 3332429) B3332429
theorem B4998653 : Blo 2221435 4998653 := bbase (se 3 (by rfl) ⟨937247, by rfl⟩ : syracuseStep 4998653 = 1874495) (by norm_num)
theorem B3332435 : Blo 2221435 3332435 := bstep (se 1 (by rfl) ⟨2499326, by rfl⟩ : syracuseStep 3332435 = 4998653) B4998653
theorem B2221623 : Blo 2221435 2221623 := bstep (se 1 (by rfl) ⟨1666217, by rfl⟩ : syracuseStep 2221623 = 3332435) B3332435
theorem B3748997 : Blo 2221435 3748997 := bbase (se 4 (by rfl) ⟨351468, by rfl⟩ : syracuseStep 3748997 = 702937) (by norm_num)
theorem B2499331 : Blo 2221435 2499331 := bstep (se 1 (by rfl) ⟨1874498, by rfl⟩ : syracuseStep 2499331 = 3748997) B3748997
theorem B3332441 : Blo 2221435 3332441 := bstep (se 2 (by rfl) ⟨1249665, by rfl⟩ : syracuseStep 3332441 = 2499331) B2499331
theorem B2221627 : Blo 2221435 2221627 := bstep (se 1 (by rfl) ⟨1666220, by rfl⟩ : syracuseStep 2221627 = 3332441) B3332441
theorem B16870517 : Blo 2221435 16870517 := bbase (se 5 (by rfl) ⟨790805, by rfl⟩ : syracuseStep 16870517 = 1581611) (by norm_num)
theorem B11247011 : Blo 2221435 11247011 := bstep (se 1 (by rfl) ⟨8435258, by rfl⟩ : syracuseStep 11247011 = 16870517) B16870517
theorem B7498007 : Blo 2221435 7498007 := bstep (se 1 (by rfl) ⟨5623505, by rfl⟩ : syracuseStep 7498007 = 11247011) B11247011
theorem B4998671 : Blo 2221435 4998671 := bstep (se 1 (by rfl) ⟨3749003, by rfl⟩ : syracuseStep 4998671 = 7498007) B7498007
theorem B3332447 : Blo 2221435 3332447 := bstep (se 1 (by rfl) ⟨2499335, by rfl⟩ : syracuseStep 3332447 = 4998671) B4998671
theorem B2221631 : Blo 2221435 2221631 := bstep (se 1 (by rfl) ⟨1666223, by rfl⟩ : syracuseStep 2221631 = 3332447) B3332447
theorem B3332453 : Blo 2221435 3332453 := bbase (se 4 (by rfl) ⟨312417, by rfl⟩ : syracuseStep 3332453 = 624835) (by norm_num)
theorem B2221635 : Blo 2221435 2221635 := bstep (se 1 (by rfl) ⟨1666226, by rfl⟩ : syracuseStep 2221635 = 3332453) B3332453
theorem B4217645 : Blo 2221435 4217645 := bbase (se 3 (by rfl) ⟨790808, by rfl⟩ : syracuseStep 4217645 = 1581617) (by norm_num)
theorem B2811763 : Blo 2221435 2811763 := bstep (se 1 (by rfl) ⟨2108822, by rfl⟩ : syracuseStep 2811763 = 4217645) B4217645
theorem B3749017 : Blo 2221435 3749017 := bstep (se 2 (by rfl) ⟨1405881, by rfl⟩ : syracuseStep 3749017 = 2811763) B2811763
theorem B4998689 : Blo 2221435 4998689 := bstep (se 2 (by rfl) ⟨1874508, by rfl⟩ : syracuseStep 4998689 = 3749017) B3749017
theorem B3332459 : Blo 2221435 3332459 := bstep (se 1 (by rfl) ⟨2499344, by rfl⟩ : syracuseStep 3332459 = 4998689) B4998689
theorem B2221639 : Blo 2221435 2221639 := bstep (se 1 (by rfl) ⟨1666229, by rfl⟩ : syracuseStep 2221639 = 3332459) B3332459
theorem B2499349 : Blo 2221435 2499349 := bbase (se 6 (by rfl) ⟨58578, by rfl⟩ : syracuseStep 2499349 = 117157) (by norm_num)
theorem B3332465 : Blo 2221435 3332465 := bstep (se 2 (by rfl) ⟨1249674, by rfl⟩ : syracuseStep 3332465 = 2499349) B2499349
theorem B2221643 : Blo 2221435 2221643 := bstep (se 1 (by rfl) ⟨1666232, by rfl⟩ : syracuseStep 2221643 = 3332465) B3332465
theorem B2811773 : Blo 2221435 2811773 := bbase (se 3 (by rfl) ⟨527207, by rfl⟩ : syracuseStep 2811773 = 1054415) (by norm_num)
theorem B7498061 : Blo 2221435 7498061 := bstep (se 3 (by rfl) ⟨1405886, by rfl⟩ : syracuseStep 7498061 = 2811773) B2811773
theorem B4998707 : Blo 2221435 4998707 := bstep (se 1 (by rfl) ⟨3749030, by rfl⟩ : syracuseStep 4998707 = 7498061) B7498061
theorem B3332471 : Blo 2221435 3332471 := bstep (se 1 (by rfl) ⟨2499353, by rfl⟩ : syracuseStep 3332471 = 4998707) B4998707
theorem B2221647 : Blo 2221435 2221647 := bstep (se 1 (by rfl) ⟨1666235, by rfl⟩ : syracuseStep 2221647 = 3332471) B3332471
theorem B3332477 : Blo 2221435 3332477 := bbase (se 3 (by rfl) ⟨624839, by rfl⟩ : syracuseStep 3332477 = 1249679) (by norm_num)
theorem B2221651 : Blo 2221435 2221651 := bstep (se 1 (by rfl) ⟨1666238, by rfl⟩ : syracuseStep 2221651 = 3332477) B3332477
theorem B4998725 : Blo 2221435 4998725 := bbase (se 4 (by rfl) ⟨468630, by rfl⟩ : syracuseStep 4998725 = 937261) (by norm_num)
theorem B3332483 : Blo 2221435 3332483 := bstep (se 1 (by rfl) ⟨2499362, by rfl⟩ : syracuseStep 3332483 = 4998725) B4998725
theorem B2221655 : Blo 2221435 2221655 := bstep (se 1 (by rfl) ⟨1666241, by rfl⟩ : syracuseStep 2221655 = 3332483) B3332483
theorem B12010517 : Blo 2221435 12010517 := bbase (se 6 (by rfl) ⟨281496, by rfl⟩ : syracuseStep 12010517 = 562993) (by norm_num)
theorem B8007011 : Blo 2221435 8007011 := bstep (se 1 (by rfl) ⟨6005258, by rfl⟩ : syracuseStep 8007011 = 12010517) B12010517
theorem B5338007 : Blo 2221435 5338007 := bstep (se 1 (by rfl) ⟨4003505, by rfl⟩ : syracuseStep 5338007 = 8007011) B8007011
theorem B3558671 : Blo 2221435 3558671 := bstep (se 1 (by rfl) ⟨2669003, by rfl⟩ : syracuseStep 3558671 = 5338007) B5338007
theorem B2372447 : Blo 2221435 2372447 := bstep (se 1 (by rfl) ⟨1779335, by rfl⟩ : syracuseStep 2372447 = 3558671) B3558671
theorem B6326525 : Blo 2221435 6326525 := bstep (se 3 (by rfl) ⟨1186223, by rfl⟩ : syracuseStep 6326525 = 2372447) B2372447
theorem B4217683 : Blo 2221435 4217683 := bstep (se 1 (by rfl) ⟨3163262, by rfl⟩ : syracuseStep 4217683 = 6326525) B6326525
theorem B5623577 : Blo 2221435 5623577 := bstep (se 2 (by rfl) ⟨2108841, by rfl⟩ : syracuseStep 5623577 = 4217683) B4217683
theorem B3749051 : Blo 2221435 3749051 := bstep (se 1 (by rfl) ⟨2811788, by rfl⟩ : syracuseStep 3749051 = 5623577) B5623577
theorem B2499367 : Blo 2221435 2499367 := bstep (se 1 (by rfl) ⟨1874525, by rfl⟩ : syracuseStep 2499367 = 3749051) B3749051
theorem B3332489 : Blo 2221435 3332489 := bstep (se 2 (by rfl) ⟨1249683, by rfl⟩ : syracuseStep 3332489 = 2499367) B2499367
theorem B2221659 : Blo 2221435 2221659 := bstep (se 1 (by rfl) ⟨1666244, by rfl⟩ : syracuseStep 2221659 = 3332489) B3332489
theorem B11247173 : Blo 2221435 11247173 := bbase (se 4 (by rfl) ⟨1054422, by rfl⟩ : syracuseStep 11247173 = 2108845) (by norm_num)
theorem B7498115 : Blo 2221435 7498115 := bstep (se 1 (by rfl) ⟨5623586, by rfl⟩ : syracuseStep 7498115 = 11247173) B11247173
theorem B4998743 : Blo 2221435 4998743 := bstep (se 1 (by rfl) ⟨3749057, by rfl⟩ : syracuseStep 4998743 = 7498115) B7498115
theorem B3332495 : Blo 2221435 3332495 := bstep (se 1 (by rfl) ⟨2499371, by rfl⟩ : syracuseStep 3332495 = 4998743) B4998743
theorem B2221663 : Blo 2221435 2221663 := bstep (se 1 (by rfl) ⟨1666247, by rfl⟩ : syracuseStep 2221663 = 3332495) B3332495
theorem B3332501 : Blo 2221435 3332501 := bbase (se 6 (by rfl) ⟨78105, by rfl⟩ : syracuseStep 3332501 = 156211) (by norm_num)
theorem B2221667 : Blo 2221435 2221667 := bstep (se 1 (by rfl) ⟨1666250, by rfl⟩ : syracuseStep 2221667 = 3332501) B3332501
theorem B10676069 : Blo 2221435 10676069 := bbase (se 4 (by rfl) ⟨1000881, by rfl⟩ : syracuseStep 10676069 = 2001763) (by norm_num)
theorem B7117379 : Blo 2221435 7117379 := bstep (se 1 (by rfl) ⟨5338034, by rfl⟩ : syracuseStep 7117379 = 10676069) B10676069
theorem B4744919 : Blo 2221435 4744919 := bstep (se 1 (by rfl) ⟨3558689, by rfl⟩ : syracuseStep 4744919 = 7117379) B7117379
theorem B12653117 : Blo 2221435 12653117 := bstep (se 3 (by rfl) ⟨2372459, by rfl⟩ : syracuseStep 12653117 = 4744919) B4744919
theorem B8435411 : Blo 2221435 8435411 := bstep (se 1 (by rfl) ⟨6326558, by rfl⟩ : syracuseStep 8435411 = 12653117) B12653117
theorem B5623607 : Blo 2221435 5623607 := bstep (se 1 (by rfl) ⟨4217705, by rfl⟩ : syracuseStep 5623607 = 8435411) B8435411
theorem B3749071 : Blo 2221435 3749071 := bstep (se 1 (by rfl) ⟨2811803, by rfl⟩ : syracuseStep 3749071 = 5623607) B5623607
theorem B4998761 : Blo 2221435 4998761 := bstep (se 2 (by rfl) ⟨1874535, by rfl⟩ : syracuseStep 4998761 = 3749071) B3749071
theorem B3332507 : Blo 2221435 3332507 := bstep (se 1 (by rfl) ⟨2499380, by rfl⟩ : syracuseStep 3332507 = 4998761) B4998761
theorem B2221671 : Blo 2221435 2221671 := bstep (se 1 (by rfl) ⟨1666253, by rfl⟩ : syracuseStep 2221671 = 3332507) B3332507
theorem B2499385 : Blo 2221435 2499385 := bbase (se 2 (by rfl) ⟨937269, by rfl⟩ : syracuseStep 2499385 = 1874539) (by norm_num)
theorem B3332513 : Blo 2221435 3332513 := bstep (se 2 (by rfl) ⟨1249692, by rfl⟩ : syracuseStep 3332513 = 2499385) B2499385
theorem B2221675 : Blo 2221435 2221675 := bstep (se 1 (by rfl) ⟨1666256, by rfl⟩ : syracuseStep 2221675 = 3332513) B3332513
theorem B6326581 : Blo 2221435 6326581 := bbase (se 5 (by rfl) ⟨296558, by rfl⟩ : syracuseStep 6326581 = 593117) (by norm_num)
theorem B8435441 : Blo 2221435 8435441 := bstep (se 2 (by rfl) ⟨3163290, by rfl⟩ : syracuseStep 8435441 = 6326581) B6326581
theorem B5623627 : Blo 2221435 5623627 := bstep (se 1 (by rfl) ⟨4217720, by rfl⟩ : syracuseStep 5623627 = 8435441) B8435441
theorem B7498169 : Blo 2221435 7498169 := bstep (se 2 (by rfl) ⟨2811813, by rfl⟩ : syracuseStep 7498169 = 5623627) B5623627
theorem B4998779 : Blo 2221435 4998779 := bstep (se 1 (by rfl) ⟨3749084, by rfl⟩ : syracuseStep 4998779 = 7498169) B7498169
theorem B3332519 : Blo 2221435 3332519 := bstep (se 1 (by rfl) ⟨2499389, by rfl⟩ : syracuseStep 3332519 = 4998779) B4998779
theorem B2221679 : Blo 2221435 2221679 := bstep (se 1 (by rfl) ⟨1666259, by rfl⟩ : syracuseStep 2221679 = 3332519) B3332519
theorem B3332525 : Blo 2221435 3332525 := bbase (se 3 (by rfl) ⟨624848, by rfl⟩ : syracuseStep 3332525 = 1249697) (by norm_num)
theorem B2221683 : Blo 2221435 2221683 := bstep (se 1 (by rfl) ⟨1666262, by rfl⟩ : syracuseStep 2221683 = 3332525) B3332525
theorem B4998797 : Blo 2221435 4998797 := bbase (se 3 (by rfl) ⟨937274, by rfl⟩ : syracuseStep 4998797 = 1874549) (by norm_num)
theorem B3332531 : Blo 2221435 3332531 := bstep (se 1 (by rfl) ⟨2499398, by rfl⟩ : syracuseStep 3332531 = 4998797) B4998797
theorem B2221687 : Blo 2221435 2221687 := bstep (se 1 (by rfl) ⟨1666265, by rfl⟩ : syracuseStep 2221687 = 3332531) B3332531
theorem B2811829 : Blo 2221435 2811829 := bbase (se 5 (by rfl) ⟨131804, by rfl⟩ : syracuseStep 2811829 = 263609) (by norm_num)
theorem B3749105 : Blo 2221435 3749105 := bstep (se 2 (by rfl) ⟨1405914, by rfl⟩ : syracuseStep 3749105 = 2811829) B2811829
theorem B2499403 : Blo 2221435 2499403 := bstep (se 1 (by rfl) ⟨1874552, by rfl⟩ : syracuseStep 2499403 = 3749105) B3749105
theorem B3332537 : Blo 2221435 3332537 := bstep (se 2 (by rfl) ⟨1249701, by rfl⟩ : syracuseStep 3332537 = 2499403) B2499403
theorem B2221691 : Blo 2221435 2221691 := bstep (se 1 (by rfl) ⟨1666268, by rfl⟩ : syracuseStep 2221691 = 3332537) B3332537
theorem B4809709 : Blo 2221435 4809709 := bbase (se 3 (by rfl) ⟨901820, by rfl⟩ : syracuseStep 4809709 = 1803641) (by norm_num)
theorem B6412945 : Blo 2221435 6412945 := bstep (se 2 (by rfl) ⟨2404854, by rfl⟩ : syracuseStep 6412945 = 4809709) B4809709
theorem B8550593 : Blo 2221435 8550593 := bstep (se 2 (by rfl) ⟨3206472, by rfl⟩ : syracuseStep 8550593 = 6412945) B6412945
theorem B5700395 : Blo 2221435 5700395 := bstep (se 1 (by rfl) ⟨4275296, by rfl⟩ : syracuseStep 5700395 = 8550593) B8550593
theorem B3800263 : Blo 2221435 3800263 := bstep (se 1 (by rfl) ⟨2850197, by rfl⟩ : syracuseStep 3800263 = 5700395) B5700395
theorem B5067017 : Blo 2221435 5067017 := bstep (se 2 (by rfl) ⟨1900131, by rfl⟩ : syracuseStep 5067017 = 3800263) B3800263
theorem B3378011 : Blo 2221435 3378011 := bstep (se 1 (by rfl) ⟨2533508, by rfl⟩ : syracuseStep 3378011 = 5067017) B5067017
theorem B9008029 : Blo 2221435 9008029 := bstep (se 3 (by rfl) ⟨1689005, by rfl⟩ : syracuseStep 9008029 = 3378011) B3378011
theorem B48042821 : Blo 2221435 48042821 := bstep (se 4 (by rfl) ⟨4504014, by rfl⟩ : syracuseStep 48042821 = 9008029) B9008029
theorem B32028547 : Blo 2221435 32028547 := bstep (se 1 (by rfl) ⟨24021410, by rfl⟩ : syracuseStep 32028547 = 48042821) B48042821
theorem B42704729 : Blo 2221435 42704729 := bstep (se 2 (by rfl) ⟨16014273, by rfl⟩ : syracuseStep 42704729 = 32028547) B32028547
theorem B28469819 : Blo 2221435 28469819 := bstep (se 1 (by rfl) ⟨21352364, by rfl⟩ : syracuseStep 28469819 = 42704729) B42704729
theorem B18979879 : Blo 2221435 18979879 := bstep (se 1 (by rfl) ⟨14234909, by rfl⟩ : syracuseStep 18979879 = 28469819) B28469819
theorem B25306505 : Blo 2221435 25306505 := bstep (se 2 (by rfl) ⟨9489939, by rfl⟩ : syracuseStep 25306505 = 18979879) B18979879
theorem B16871003 : Blo 2221435 16871003 := bstep (se 1 (by rfl) ⟨12653252, by rfl⟩ : syracuseStep 16871003 = 25306505) B25306505
theorem B11247335 : Blo 2221435 11247335 := bstep (se 1 (by rfl) ⟨8435501, by rfl⟩ : syracuseStep 11247335 = 16871003) B16871003
theorem B7498223 : Blo 2221435 7498223 := bstep (se 1 (by rfl) ⟨5623667, by rfl⟩ : syracuseStep 7498223 = 11247335) B11247335
theorem B4998815 : Blo 2221435 4998815 := bstep (se 1 (by rfl) ⟨3749111, by rfl⟩ : syracuseStep 4998815 = 7498223) B7498223
theorem B3332543 : Blo 2221435 3332543 := bstep (se 1 (by rfl) ⟨2499407, by rfl⟩ : syracuseStep 3332543 = 4998815) B4998815
theorem B2221695 : Blo 2221435 2221695 := bstep (se 1 (by rfl) ⟨1666271, by rfl⟩ : syracuseStep 2221695 = 3332543) B3332543
theorem B3332549 : Blo 2221435 3332549 := bbase (se 4 (by rfl) ⟨312426, by rfl⟩ : syracuseStep 3332549 = 624853) (by norm_num)
theorem B2221699 : Blo 2221435 2221699 := bstep (se 1 (by rfl) ⟨1666274, by rfl⟩ : syracuseStep 2221699 = 3332549) B3332549
theorem B3749125 : Blo 2221435 3749125 := bbase (se 4 (by rfl) ⟨351480, by rfl⟩ : syracuseStep 3749125 = 702961) (by norm_num)
theorem B4998833 : Blo 2221435 4998833 := bstep (se 2 (by rfl) ⟨1874562, by rfl⟩ : syracuseStep 4998833 = 3749125) B3749125
theorem B3332555 : Blo 2221435 3332555 := bstep (se 1 (by rfl) ⟨2499416, by rfl⟩ : syracuseStep 3332555 = 4998833) B4998833
theorem B2221703 : Blo 2221435 2221703 := bstep (se 1 (by rfl) ⟨1666277, by rfl⟩ : syracuseStep 2221703 = 3332555) B3332555
theorem B2499421 : Blo 2221435 2499421 := bbase (se 3 (by rfl) ⟨468641, by rfl⟩ : syracuseStep 2499421 = 937283) (by norm_num)
theorem B3332561 : Blo 2221435 3332561 := bstep (se 2 (by rfl) ⟨1249710, by rfl⟩ : syracuseStep 3332561 = 2499421) B2499421
theorem B2221707 : Blo 2221435 2221707 := bstep (se 1 (by rfl) ⟨1666280, by rfl⟩ : syracuseStep 2221707 = 3332561) B3332561
theorem B7498277 : Blo 2221435 7498277 := bbase (se 4 (by rfl) ⟨702963, by rfl⟩ : syracuseStep 7498277 = 1405927) (by norm_num)
theorem B4998851 : Blo 2221435 4998851 := bstep (se 1 (by rfl) ⟨3749138, by rfl⟩ : syracuseStep 4998851 = 7498277) B7498277
theorem B3332567 : Blo 2221435 3332567 := bstep (se 1 (by rfl) ⟨2499425, by rfl⟩ : syracuseStep 3332567 = 4998851) B4998851
theorem B2221711 : Blo 2221435 2221711 := bstep (se 1 (by rfl) ⟨1666283, by rfl⟩ : syracuseStep 2221711 = 3332567) B3332567
theorem B3332573 : Blo 2221435 3332573 := bbase (se 3 (by rfl) ⟨624857, by rfl⟩ : syracuseStep 3332573 = 1249715) (by norm_num)
theorem B2221715 : Blo 2221435 2221715 := bstep (se 1 (by rfl) ⟨1666286, by rfl⟩ : syracuseStep 2221715 = 3332573) B3332573
theorem B4998869 : Blo 2221435 4998869 := bbase (se 7 (by rfl) ⟨58580, by rfl⟩ : syracuseStep 4998869 = 117161) (by norm_num)
theorem B3332579 : Blo 2221435 3332579 := bstep (se 1 (by rfl) ⟨2499434, by rfl⟩ : syracuseStep 3332579 = 4998869) B4998869
theorem B2221719 : Blo 2221435 2221719 := bstep (se 1 (by rfl) ⟨1666289, by rfl⟩ : syracuseStep 2221719 = 3332579) B3332579
theorem B3558773 : Blo 2221435 3558773 := bbase (se 5 (by rfl) ⟨166817, by rfl⟩ : syracuseStep 3558773 = 333635) (by norm_num)
theorem B9490061 : Blo 2221435 9490061 := bstep (se 3 (by rfl) ⟨1779386, by rfl⟩ : syracuseStep 9490061 = 3558773) B3558773
theorem B6326707 : Blo 2221435 6326707 := bstep (se 1 (by rfl) ⟨4745030, by rfl⟩ : syracuseStep 6326707 = 9490061) B9490061
theorem B8435609 : Blo 2221435 8435609 := bstep (se 2 (by rfl) ⟨3163353, by rfl⟩ : syracuseStep 8435609 = 6326707) B6326707
theorem B5623739 : Blo 2221435 5623739 := bstep (se 1 (by rfl) ⟨4217804, by rfl⟩ : syracuseStep 5623739 = 8435609) B8435609
theorem B3749159 : Blo 2221435 3749159 := bstep (se 1 (by rfl) ⟨2811869, by rfl⟩ : syracuseStep 3749159 = 5623739) B5623739
theorem B2499439 : Blo 2221435 2499439 := bstep (se 1 (by rfl) ⟨1874579, by rfl⟩ : syracuseStep 2499439 = 3749159) B3749159
theorem B3332585 : Blo 2221435 3332585 := bstep (se 2 (by rfl) ⟨1249719, by rfl⟩ : syracuseStep 3332585 = 2499439) B2499439
theorem B2221723 : Blo 2221435 2221723 := bstep (se 1 (by rfl) ⟨1666292, by rfl⟩ : syracuseStep 2221723 = 3332585) B3332585
theorem B26002133 : Blo 2221435 26002133 := bbase (se 7 (by rfl) ⟨304712, by rfl⟩ : syracuseStep 26002133 = 609425) (by norm_num)
theorem B17334755 : Blo 2221435 17334755 := bstep (se 1 (by rfl) ⟨13001066, by rfl⟩ : syracuseStep 17334755 = 26002133) B26002133
theorem B11556503 : Blo 2221435 11556503 := bstep (se 1 (by rfl) ⟨8667377, by rfl⟩ : syracuseStep 11556503 = 17334755) B17334755
theorem B7704335 : Blo 2221435 7704335 := bstep (se 1 (by rfl) ⟨5778251, by rfl⟩ : syracuseStep 7704335 = 11556503) B11556503
theorem B5136223 : Blo 2221435 5136223 := bstep (se 1 (by rfl) ⟨3852167, by rfl⟩ : syracuseStep 5136223 = 7704335) B7704335
theorem B6848297 : Blo 2221435 6848297 := bstep (se 2 (by rfl) ⟨2568111, by rfl⟩ : syracuseStep 6848297 = 5136223) B5136223
theorem B4565531 : Blo 2221435 4565531 := bstep (se 1 (by rfl) ⟨3424148, by rfl⟩ : syracuseStep 4565531 = 6848297) B6848297
theorem B3043687 : Blo 2221435 3043687 := bstep (se 1 (by rfl) ⟨2282765, by rfl⟩ : syracuseStep 3043687 = 4565531) B4565531
theorem B64931989 : Blo 2221435 64931989 := bstep (se 6 (by rfl) ⟨1521843, by rfl⟩ : syracuseStep 64931989 = 3043687) B3043687
theorem B86575985 : Blo 2221435 86575985 := bstep (se 2 (by rfl) ⟨32465994, by rfl⟩ : syracuseStep 86575985 = 64931989) B64931989
theorem B57717323 : Blo 2221435 57717323 := bstep (se 1 (by rfl) ⟨43287992, by rfl⟩ : syracuseStep 57717323 = 86575985) B86575985
theorem B38478215 : Blo 2221435 38478215 := bstep (se 1 (by rfl) ⟨28858661, by rfl⟩ : syracuseStep 38478215 = 57717323) B57717323
theorem B25652143 : Blo 2221435 25652143 := bstep (se 1 (by rfl) ⟨19239107, by rfl⟩ : syracuseStep 25652143 = 38478215) B38478215
theorem B136811429 : Blo 2221435 136811429 := bstep (se 4 (by rfl) ⟨12826071, by rfl⟩ : syracuseStep 136811429 = 25652143) B25652143
theorem B91207619 : Blo 2221435 91207619 := bstep (se 1 (by rfl) ⟨68405714, by rfl⟩ : syracuseStep 91207619 = 136811429) B136811429
theorem B60805079 : Blo 2221435 60805079 := bstep (se 1 (by rfl) ⟨45603809, by rfl⟩ : syracuseStep 60805079 = 91207619) B91207619
theorem B40536719 : Blo 2221435 40536719 := bstep (se 1 (by rfl) ⟨30402539, by rfl⟩ : syracuseStep 40536719 = 60805079) B60805079
theorem B27024479 : Blo 2221435 27024479 := bstep (se 1 (by rfl) ⟨20268359, by rfl⟩ : syracuseStep 27024479 = 40536719) B40536719
theorem B18016319 : Blo 2221435 18016319 := bstep (se 1 (by rfl) ⟨13512239, by rfl⟩ : syracuseStep 18016319 = 27024479) B27024479
theorem B12010879 : Blo 2221435 12010879 := bstep (se 1 (by rfl) ⟨9008159, by rfl⟩ : syracuseStep 12010879 = 18016319) B18016319
theorem B16014505 : Blo 2221435 16014505 := bstep (se 2 (by rfl) ⟨6005439, by rfl⟩ : syracuseStep 16014505 = 12010879) B12010879
theorem B21352673 : Blo 2221435 21352673 := bstep (se 2 (by rfl) ⟨8007252, by rfl⟩ : syracuseStep 21352673 = 16014505) B16014505
theorem B14235115 : Blo 2221435 14235115 := bstep (se 1 (by rfl) ⟨10676336, by rfl⟩ : syracuseStep 14235115 = 21352673) B21352673
theorem B18980153 : Blo 2221435 18980153 := bstep (se 2 (by rfl) ⟨7117557, by rfl⟩ : syracuseStep 18980153 = 14235115) B14235115
theorem B12653435 : Blo 2221435 12653435 := bstep (se 1 (by rfl) ⟨9490076, by rfl⟩ : syracuseStep 12653435 = 18980153) B18980153
theorem B8435623 : Blo 2221435 8435623 := bstep (se 1 (by rfl) ⟨6326717, by rfl⟩ : syracuseStep 8435623 = 12653435) B12653435
theorem B11247497 : Blo 2221435 11247497 := bstep (se 2 (by rfl) ⟨4217811, by rfl⟩ : syracuseStep 11247497 = 8435623) B8435623
theorem B7498331 : Blo 2221435 7498331 := bstep (se 1 (by rfl) ⟨5623748, by rfl⟩ : syracuseStep 7498331 = 11247497) B11247497
theorem B4998887 : Blo 2221435 4998887 := bstep (se 1 (by rfl) ⟨3749165, by rfl⟩ : syracuseStep 4998887 = 7498331) B7498331
theorem B3332591 : Blo 2221435 3332591 := bstep (se 1 (by rfl) ⟨2499443, by rfl⟩ : syracuseStep 3332591 = 4998887) B4998887
theorem B2221727 : Blo 2221435 2221727 := bstep (se 1 (by rfl) ⟨1666295, by rfl⟩ : syracuseStep 2221727 = 3332591) B3332591
theorem B3332597 : Blo 2221435 3332597 := bbase (se 5 (by rfl) ⟨156215, by rfl⟩ : syracuseStep 3332597 = 312431) (by norm_num)
theorem B2221731 : Blo 2221435 2221731 := bstep (se 1 (by rfl) ⟨1666298, by rfl⟩ : syracuseStep 2221731 = 3332597) B3332597
theorem B6326741 : Blo 2221435 6326741 := bbase (se 7 (by rfl) ⟨74141, by rfl⟩ : syracuseStep 6326741 = 148283) (by norm_num)
theorem B4217827 : Blo 2221435 4217827 := bstep (se 1 (by rfl) ⟨3163370, by rfl⟩ : syracuseStep 4217827 = 6326741) B6326741
theorem B5623769 : Blo 2221435 5623769 := bstep (se 2 (by rfl) ⟨2108913, by rfl⟩ : syracuseStep 5623769 = 4217827) B4217827
theorem B3749179 : Blo 2221435 3749179 := bstep (se 1 (by rfl) ⟨2811884, by rfl⟩ : syracuseStep 3749179 = 5623769) B5623769
theorem B4998905 : Blo 2221435 4998905 := bstep (se 2 (by rfl) ⟨1874589, by rfl⟩ : syracuseStep 4998905 = 3749179) B3749179
theorem B3332603 : Blo 2221435 3332603 := bstep (se 1 (by rfl) ⟨2499452, by rfl⟩ : syracuseStep 3332603 = 4998905) B4998905
theorem B2221735 : Blo 2221435 2221735 := bstep (se 1 (by rfl) ⟨1666301, by rfl⟩ : syracuseStep 2221735 = 3332603) B3332603
theorem B2499457 : Blo 2221435 2499457 := bbase (se 2 (by rfl) ⟨937296, by rfl⟩ : syracuseStep 2499457 = 1874593) (by norm_num)
theorem B3332609 : Blo 2221435 3332609 := bstep (se 2 (by rfl) ⟨1249728, by rfl⟩ : syracuseStep 3332609 = 2499457) B2499457
theorem B2221739 : Blo 2221435 2221739 := bstep (se 1 (by rfl) ⟨1666304, by rfl⟩ : syracuseStep 2221739 = 3332609) B3332609
theorem B5623789 : Blo 2221435 5623789 := bbase (se 3 (by rfl) ⟨1054460, by rfl⟩ : syracuseStep 5623789 = 2108921) (by norm_num)
theorem B7498385 : Blo 2221435 7498385 := bstep (se 2 (by rfl) ⟨2811894, by rfl⟩ : syracuseStep 7498385 = 5623789) B5623789
theorem B4998923 : Blo 2221435 4998923 := bstep (se 1 (by rfl) ⟨3749192, by rfl⟩ : syracuseStep 4998923 = 7498385) B7498385
theorem B3332615 : Blo 2221435 3332615 := bstep (se 1 (by rfl) ⟨2499461, by rfl⟩ : syracuseStep 3332615 = 4998923) B4998923
theorem B2221743 : Blo 2221435 2221743 := bstep (se 1 (by rfl) ⟨1666307, by rfl⟩ : syracuseStep 2221743 = 3332615) B3332615
theorem B3332621 : Blo 2221435 3332621 := bbase (se 3 (by rfl) ⟨624866, by rfl⟩ : syracuseStep 3332621 = 1249733) (by norm_num)
theorem B2221747 : Blo 2221435 2221747 := bstep (se 1 (by rfl) ⟨1666310, by rfl⟩ : syracuseStep 2221747 = 3332621) B3332621
theorem B4998941 : Blo 2221435 4998941 := bbase (se 3 (by rfl) ⟨937301, by rfl⟩ : syracuseStep 4998941 = 1874603) (by norm_num)
theorem B3332627 : Blo 2221435 3332627 := bstep (se 1 (by rfl) ⟨2499470, by rfl⟩ : syracuseStep 3332627 = 4998941) B4998941
theorem B2221751 : Blo 2221435 2221751 := bstep (se 1 (by rfl) ⟨1666313, by rfl⟩ : syracuseStep 2221751 = 3332627) B3332627
theorem B3749213 : Blo 2221435 3749213 := bbase (se 3 (by rfl) ⟨702977, by rfl⟩ : syracuseStep 3749213 = 1405955) (by norm_num)
theorem B2499475 : Blo 2221435 2499475 := bstep (se 1 (by rfl) ⟨1874606, by rfl⟩ : syracuseStep 2499475 = 3749213) B3749213
theorem B3332633 : Blo 2221435 3332633 := bstep (se 2 (by rfl) ⟨1249737, by rfl⟩ : syracuseStep 3332633 = 2499475) B2499475
theorem B2221755 : Blo 2221435 2221755 := bstep (se 1 (by rfl) ⟨1666316, by rfl⟩ : syracuseStep 2221755 = 3332633) B3332633
theorem B9490213 : Blo 2221435 9490213 := bbase (se 4 (by rfl) ⟨889707, by rfl⟩ : syracuseStep 9490213 = 1779415) (by norm_num)
theorem B12653617 : Blo 2221435 12653617 := bstep (se 2 (by rfl) ⟨4745106, by rfl⟩ : syracuseStep 12653617 = 9490213) B9490213
theorem B16871489 : Blo 2221435 16871489 := bstep (se 2 (by rfl) ⟨6326808, by rfl⟩ : syracuseStep 16871489 = 12653617) B12653617
theorem B11247659 : Blo 2221435 11247659 := bstep (se 1 (by rfl) ⟨8435744, by rfl⟩ : syracuseStep 11247659 = 16871489) B16871489
theorem B7498439 : Blo 2221435 7498439 := bstep (se 1 (by rfl) ⟨5623829, by rfl⟩ : syracuseStep 7498439 = 11247659) B11247659
theorem B4998959 : Blo 2221435 4998959 := bstep (se 1 (by rfl) ⟨3749219, by rfl⟩ : syracuseStep 4998959 = 7498439) B7498439
theorem B3332639 : Blo 2221435 3332639 := bstep (se 1 (by rfl) ⟨2499479, by rfl⟩ : syracuseStep 3332639 = 4998959) B4998959
theorem B2221759 : Blo 2221435 2221759 := bstep (se 1 (by rfl) ⟨1666319, by rfl⟩ : syracuseStep 2221759 = 3332639) B3332639
theorem B3332645 : Blo 2221435 3332645 := bbase (se 4 (by rfl) ⟨312435, by rfl⟩ : syracuseStep 3332645 = 624871) (by norm_num)
theorem B2221763 : Blo 2221435 2221763 := bstep (se 1 (by rfl) ⟨1666322, by rfl⟩ : syracuseStep 2221763 = 3332645) B3332645
theorem B2811925 : Blo 2221435 2811925 := bbase (se 6 (by rfl) ⟨65904, by rfl⟩ : syracuseStep 2811925 = 131809) (by norm_num)
theorem B3749233 : Blo 2221435 3749233 := bstep (se 2 (by rfl) ⟨1405962, by rfl⟩ : syracuseStep 3749233 = 2811925) B2811925
theorem B4998977 : Blo 2221435 4998977 := bstep (se 2 (by rfl) ⟨1874616, by rfl⟩ : syracuseStep 4998977 = 3749233) B3749233
theorem B3332651 : Blo 2221435 3332651 := bstep (se 1 (by rfl) ⟨2499488, by rfl⟩ : syracuseStep 3332651 = 4998977) B4998977
theorem B2221767 : Blo 2221435 2221767 := bstep (se 1 (by rfl) ⟨1666325, by rfl⟩ : syracuseStep 2221767 = 3332651) B3332651
theorem B2499493 : Blo 2221435 2499493 := bbase (se 4 (by rfl) ⟨234327, by rfl⟩ : syracuseStep 2499493 = 468655) (by norm_num)
theorem B3332657 : Blo 2221435 3332657 := bstep (se 2 (by rfl) ⟨1249746, by rfl⟩ : syracuseStep 3332657 = 2499493) B2499493
theorem B2221771 : Blo 2221435 2221771 := bstep (se 1 (by rfl) ⟨1666328, by rfl⟩ : syracuseStep 2221771 = 3332657) B3332657
theorem B2252089 : Blo 2221435 2252089 := bbase (se 2 (by rfl) ⟨844533, by rfl⟩ : syracuseStep 2252089 = 1689067) (by norm_num)
theorem B12011141 : Blo 2221435 12011141 := bstep (se 4 (by rfl) ⟨1126044, by rfl⟩ : syracuseStep 12011141 = 2252089) B2252089
theorem B8007427 : Blo 2221435 8007427 := bstep (se 1 (by rfl) ⟨6005570, by rfl⟩ : syracuseStep 8007427 = 12011141) B12011141
theorem B10676569 : Blo 2221435 10676569 := bstep (se 2 (by rfl) ⟨4003713, by rfl⟩ : syracuseStep 10676569 = 8007427) B8007427
theorem B14235425 : Blo 2221435 14235425 := bstep (se 2 (by rfl) ⟨5338284, by rfl⟩ : syracuseStep 14235425 = 10676569) B10676569
theorem B9490283 : Blo 2221435 9490283 := bstep (se 1 (by rfl) ⟨7117712, by rfl⟩ : syracuseStep 9490283 = 14235425) B14235425
theorem B6326855 : Blo 2221435 6326855 := bstep (se 1 (by rfl) ⟨4745141, by rfl⟩ : syracuseStep 6326855 = 9490283) B9490283
theorem B4217903 : Blo 2221435 4217903 := bstep (se 1 (by rfl) ⟨3163427, by rfl⟩ : syracuseStep 4217903 = 6326855) B6326855
theorem B2811935 : Blo 2221435 2811935 := bstep (se 1 (by rfl) ⟨2108951, by rfl⟩ : syracuseStep 2811935 = 4217903) B4217903
theorem B7498493 : Blo 2221435 7498493 := bstep (se 3 (by rfl) ⟨1405967, by rfl⟩ : syracuseStep 7498493 = 2811935) B2811935
theorem B4998995 : Blo 2221435 4998995 := bstep (se 1 (by rfl) ⟨3749246, by rfl⟩ : syracuseStep 4998995 = 7498493) B7498493
theorem B3332663 : Blo 2221435 3332663 := bstep (se 1 (by rfl) ⟨2499497, by rfl⟩ : syracuseStep 3332663 = 4998995) B4998995
theorem B2221775 : Blo 2221435 2221775 := bstep (se 1 (by rfl) ⟨1666331, by rfl⟩ : syracuseStep 2221775 = 3332663) B3332663
theorem B3332669 : Blo 2221435 3332669 := bbase (se 3 (by rfl) ⟨624875, by rfl⟩ : syracuseStep 3332669 = 1249751) (by norm_num)
theorem B2221779 : Blo 2221435 2221779 := bstep (se 1 (by rfl) ⟨1666334, by rfl⟩ : syracuseStep 2221779 = 3332669) B3332669
theorem B4999013 : Blo 2221435 4999013 := bbase (se 4 (by rfl) ⟨468657, by rfl⟩ : syracuseStep 4999013 = 937315) (by norm_num)
theorem B3332675 : Blo 2221435 3332675 := bstep (se 1 (by rfl) ⟨2499506, by rfl⟩ : syracuseStep 3332675 = 4999013) B4999013
theorem B2221783 : Blo 2221435 2221783 := bstep (se 1 (by rfl) ⟨1666337, by rfl⟩ : syracuseStep 2221783 = 3332675) B3332675
theorem B5623901 : Blo 2221435 5623901 := bbase (se 3 (by rfl) ⟨1054481, by rfl⟩ : syracuseStep 5623901 = 2108963) (by norm_num)
theorem B3749267 : Blo 2221435 3749267 := bstep (se 1 (by rfl) ⟨2811950, by rfl⟩ : syracuseStep 3749267 = 5623901) B5623901
theorem B2499511 : Blo 2221435 2499511 := bstep (se 1 (by rfl) ⟨1874633, by rfl⟩ : syracuseStep 2499511 = 3749267) B3749267
theorem B3332681 : Blo 2221435 3332681 := bstep (se 2 (by rfl) ⟨1249755, by rfl⟩ : syracuseStep 3332681 = 2499511) B2499511
theorem B2221787 : Blo 2221435 2221787 := bstep (se 1 (by rfl) ⟨1666340, by rfl⟩ : syracuseStep 2221787 = 3332681) B3332681
theorem B4217933 : Blo 2221435 4217933 := bbase (se 3 (by rfl) ⟨790862, by rfl⟩ : syracuseStep 4217933 = 1581725) (by norm_num)
theorem B11247821 : Blo 2221435 11247821 := bstep (se 3 (by rfl) ⟨2108966, by rfl⟩ : syracuseStep 11247821 = 4217933) B4217933
theorem B7498547 : Blo 2221435 7498547 := bstep (se 1 (by rfl) ⟨5623910, by rfl⟩ : syracuseStep 7498547 = 11247821) B11247821
theorem B4999031 : Blo 2221435 4999031 := bstep (se 1 (by rfl) ⟨3749273, by rfl⟩ : syracuseStep 4999031 = 7498547) B7498547
theorem B3332687 : Blo 2221435 3332687 := bstep (se 1 (by rfl) ⟨2499515, by rfl⟩ : syracuseStep 3332687 = 4999031) B4999031
theorem B2221791 : Blo 2221435 2221791 := bstep (se 1 (by rfl) ⟨1666343, by rfl⟩ : syracuseStep 2221791 = 3332687) B3332687
theorem B3332693 : Blo 2221435 3332693 := bbase (se 8 (by rfl) ⟨19527, by rfl⟩ : syracuseStep 3332693 = 39055) (by norm_num)
theorem B2221795 : Blo 2221435 2221795 := bstep (se 1 (by rfl) ⟨1666346, by rfl⟩ : syracuseStep 2221795 = 3332693) B3332693
theorem B4003757 : Blo 2221435 4003757 := bbase (se 3 (by rfl) ⟨750704, by rfl⟩ : syracuseStep 4003757 = 1501409) (by norm_num)
theorem B2669171 : Blo 2221435 2669171 := bstep (se 1 (by rfl) ⟨2001878, by rfl⟩ : syracuseStep 2669171 = 4003757) B4003757
theorem B7117789 : Blo 2221435 7117789 := bstep (se 3 (by rfl) ⟨1334585, by rfl⟩ : syracuseStep 7117789 = 2669171) B2669171
theorem B9490385 : Blo 2221435 9490385 := bstep (se 2 (by rfl) ⟨3558894, by rfl⟩ : syracuseStep 9490385 = 7117789) B7117789
theorem B6326923 : Blo 2221435 6326923 := bstep (se 1 (by rfl) ⟨4745192, by rfl⟩ : syracuseStep 6326923 = 9490385) B9490385
theorem B8435897 : Blo 2221435 8435897 := bstep (se 2 (by rfl) ⟨3163461, by rfl⟩ : syracuseStep 8435897 = 6326923) B6326923
theorem B5623931 : Blo 2221435 5623931 := bstep (se 1 (by rfl) ⟨4217948, by rfl⟩ : syracuseStep 5623931 = 8435897) B8435897
theorem B3749287 : Blo 2221435 3749287 := bstep (se 1 (by rfl) ⟨2811965, by rfl⟩ : syracuseStep 3749287 = 5623931) B5623931
theorem B4999049 : Blo 2221435 4999049 := bstep (se 2 (by rfl) ⟨1874643, by rfl⟩ : syracuseStep 4999049 = 3749287) B3749287
theorem B3332699 : Blo 2221435 3332699 := bstep (se 1 (by rfl) ⟨2499524, by rfl⟩ : syracuseStep 3332699 = 4999049) B4999049
theorem B2221799 : Blo 2221435 2221799 := bstep (se 1 (by rfl) ⟨1666349, by rfl⟩ : syracuseStep 2221799 = 3332699) B3332699
theorem B2499529 : Blo 2221435 2499529 := bbase (se 2 (by rfl) ⟨937323, by rfl⟩ : syracuseStep 2499529 = 1874647) (by norm_num)
theorem B3332705 : Blo 2221435 3332705 := bstep (se 2 (by rfl) ⟨1249764, by rfl⟩ : syracuseStep 3332705 = 2499529) B2499529
theorem B2221803 : Blo 2221435 2221803 := bstep (se 1 (by rfl) ⟨1666352, by rfl⟩ : syracuseStep 2221803 = 3332705) B3332705
theorem B2533637 : Blo 2221435 2533637 := bbase (se 4 (by rfl) ⟨237528, by rfl⟩ : syracuseStep 2533637 = 475057) (by norm_num)
theorem B6756365 : Blo 2221435 6756365 := bstep (se 3 (by rfl) ⟨1266818, by rfl⟩ : syracuseStep 6756365 = 2533637) B2533637
theorem B4504243 : Blo 2221435 4504243 := bstep (se 1 (by rfl) ⟨3378182, by rfl⟩ : syracuseStep 4504243 = 6756365) B6756365
theorem B6005657 : Blo 2221435 6005657 := bstep (se 2 (by rfl) ⟨2252121, by rfl⟩ : syracuseStep 6005657 = 4504243) B4504243
theorem B4003771 : Blo 2221435 4003771 := bstep (se 1 (by rfl) ⟨3002828, by rfl⟩ : syracuseStep 4003771 = 6005657) B6005657
theorem B5338361 : Blo 2221435 5338361 := bstep (se 2 (by rfl) ⟨2001885, by rfl⟩ : syracuseStep 5338361 = 4003771) B4003771
theorem B3558907 : Blo 2221435 3558907 := bstep (se 1 (by rfl) ⟨2669180, by rfl⟩ : syracuseStep 3558907 = 5338361) B5338361
theorem B18980837 : Blo 2221435 18980837 := bstep (se 4 (by rfl) ⟨1779453, by rfl⟩ : syracuseStep 18980837 = 3558907) B3558907
theorem B12653891 : Blo 2221435 12653891 := bstep (se 1 (by rfl) ⟨9490418, by rfl⟩ : syracuseStep 12653891 = 18980837) B18980837
theorem B8435927 : Blo 2221435 8435927 := bstep (se 1 (by rfl) ⟨6326945, by rfl⟩ : syracuseStep 8435927 = 12653891) B12653891
theorem B5623951 : Blo 2221435 5623951 := bstep (se 1 (by rfl) ⟨4217963, by rfl⟩ : syracuseStep 5623951 = 8435927) B8435927
theorem B7498601 : Blo 2221435 7498601 := bstep (se 2 (by rfl) ⟨2811975, by rfl⟩ : syracuseStep 7498601 = 5623951) B5623951
theorem B4999067 : Blo 2221435 4999067 := bstep (se 1 (by rfl) ⟨3749300, by rfl⟩ : syracuseStep 4999067 = 7498601) B7498601
theorem B3332711 : Blo 2221435 3332711 := bstep (se 1 (by rfl) ⟨2499533, by rfl⟩ : syracuseStep 3332711 = 4999067) B4999067
theorem B2221807 : Blo 2221435 2221807 := bstep (se 1 (by rfl) ⟨1666355, by rfl⟩ : syracuseStep 2221807 = 3332711) B3332711
theorem B3332717 : Blo 2221435 3332717 := bbase (se 3 (by rfl) ⟨624884, by rfl⟩ : syracuseStep 3332717 = 1249769) (by norm_num)
theorem B2221811 : Blo 2221435 2221811 := bstep (se 1 (by rfl) ⟨1666358, by rfl⟩ : syracuseStep 2221811 = 3332717) B3332717
theorem B4999085 : Blo 2221435 4999085 := bbase (se 3 (by rfl) ⟨937328, by rfl⟩ : syracuseStep 4999085 = 1874657) (by norm_num)
theorem B3332723 : Blo 2221435 3332723 := bstep (se 1 (by rfl) ⟨2499542, by rfl⟩ : syracuseStep 3332723 = 4999085) B4999085
theorem B2221815 : Blo 2221435 2221815 := bstep (se 1 (by rfl) ⟨1666361, by rfl⟩ : syracuseStep 2221815 = 3332723) B3332723
theorem B6326981 : Blo 2221435 6326981 := bbase (se 4 (by rfl) ⟨593154, by rfl⟩ : syracuseStep 6326981 = 1186309) (by norm_num)
theorem B4217987 : Blo 2221435 4217987 := bstep (se 1 (by rfl) ⟨3163490, by rfl⟩ : syracuseStep 4217987 = 6326981) B6326981
theorem B2811991 : Blo 2221435 2811991 := bstep (se 1 (by rfl) ⟨2108993, by rfl⟩ : syracuseStep 2811991 = 4217987) B4217987
theorem B3749321 : Blo 2221435 3749321 := bstep (se 2 (by rfl) ⟨1405995, by rfl⟩ : syracuseStep 3749321 = 2811991) B2811991
theorem B2499547 : Blo 2221435 2499547 := bstep (se 1 (by rfl) ⟨1874660, by rfl⟩ : syracuseStep 2499547 = 3749321) B3749321
theorem B3332729 : Blo 2221435 3332729 := bstep (se 2 (by rfl) ⟨1249773, by rfl⟩ : syracuseStep 3332729 = 2499547) B2499547
theorem B2221819 : Blo 2221435 2221819 := bstep (se 1 (by rfl) ⟨1666364, by rfl⟩ : syracuseStep 2221819 = 3332729) B3332729
theorem B9008549 : Blo 2221435 9008549 := bbase (se 4 (by rfl) ⟨844551, by rfl⟩ : syracuseStep 9008549 = 1689103) (by norm_num)
theorem B6005699 : Blo 2221435 6005699 := bstep (se 1 (by rfl) ⟨4504274, by rfl⟩ : syracuseStep 6005699 = 9008549) B9008549
theorem B4003799 : Blo 2221435 4003799 := bstep (se 1 (by rfl) ⟨3002849, by rfl⟩ : syracuseStep 4003799 = 6005699) B6005699
theorem B42707189 : Blo 2221435 42707189 := bstep (se 5 (by rfl) ⟨2001899, by rfl⟩ : syracuseStep 42707189 = 4003799) B4003799
theorem B28471459 : Blo 2221435 28471459 := bstep (se 1 (by rfl) ⟨21353594, by rfl⟩ : syracuseStep 28471459 = 42707189) B42707189
theorem B37961945 : Blo 2221435 37961945 := bstep (se 2 (by rfl) ⟨14235729, by rfl⟩ : syracuseStep 37961945 = 28471459) B28471459
theorem B25307963 : Blo 2221435 25307963 := bstep (se 1 (by rfl) ⟨18980972, by rfl⟩ : syracuseStep 25307963 = 37961945) B37961945
theorem B16871975 : Blo 2221435 16871975 := bstep (se 1 (by rfl) ⟨12653981, by rfl⟩ : syracuseStep 16871975 = 25307963) B25307963
theorem B11247983 : Blo 2221435 11247983 := bstep (se 1 (by rfl) ⟨8435987, by rfl⟩ : syracuseStep 11247983 = 16871975) B16871975
theorem B7498655 : Blo 2221435 7498655 := bstep (se 1 (by rfl) ⟨5623991, by rfl⟩ : syracuseStep 7498655 = 11247983) B11247983
theorem B4999103 : Blo 2221435 4999103 := bstep (se 1 (by rfl) ⟨3749327, by rfl⟩ : syracuseStep 4999103 = 7498655) B7498655
theorem B3332735 : Blo 2221435 3332735 := bstep (se 1 (by rfl) ⟨2499551, by rfl⟩ : syracuseStep 3332735 = 4999103) B4999103
theorem B2221823 : Blo 2221435 2221823 := bstep (se 1 (by rfl) ⟨1666367, by rfl⟩ : syracuseStep 2221823 = 3332735) B3332735
theorem B3332741 : Blo 2221435 3332741 := bbase (se 4 (by rfl) ⟨312444, by rfl⟩ : syracuseStep 3332741 = 624889) (by norm_num)
theorem B2221827 : Blo 2221435 2221827 := bstep (se 1 (by rfl) ⟨1666370, by rfl⟩ : syracuseStep 2221827 = 3332741) B3332741
theorem B3749341 : Blo 2221435 3749341 := bbase (se 3 (by rfl) ⟨703001, by rfl⟩ : syracuseStep 3749341 = 1406003) (by norm_num)
theorem B4999121 : Blo 2221435 4999121 := bstep (se 2 (by rfl) ⟨1874670, by rfl⟩ : syracuseStep 4999121 = 3749341) B3749341
theorem B3332747 : Blo 2221435 3332747 := bstep (se 1 (by rfl) ⟨2499560, by rfl⟩ : syracuseStep 3332747 = 4999121) B4999121
theorem B2221831 : Blo 2221435 2221831 := bstep (se 1 (by rfl) ⟨1666373, by rfl⟩ : syracuseStep 2221831 = 3332747) B3332747
theorem B2499565 : Blo 2221435 2499565 := bbase (se 3 (by rfl) ⟨468668, by rfl⟩ : syracuseStep 2499565 = 937337) (by norm_num)
theorem B3332753 : Blo 2221435 3332753 := bstep (se 2 (by rfl) ⟨1249782, by rfl⟩ : syracuseStep 3332753 = 2499565) B2499565
theorem B2221835 : Blo 2221435 2221835 := bstep (se 1 (by rfl) ⟨1666376, by rfl⟩ : syracuseStep 2221835 = 3332753) B3332753
theorem B7498709 : Blo 2221435 7498709 := bbase (se 7 (by rfl) ⟨87875, by rfl⟩ : syracuseStep 7498709 = 175751) (by norm_num)
theorem B4999139 : Blo 2221435 4999139 := bstep (se 1 (by rfl) ⟨3749354, by rfl⟩ : syracuseStep 4999139 = 7498709) B7498709
theorem B3332759 : Blo 2221435 3332759 := bstep (se 1 (by rfl) ⟨2499569, by rfl⟩ : syracuseStep 3332759 = 4999139) B4999139
theorem B2221839 : Blo 2221435 2221839 := bstep (se 1 (by rfl) ⟨1666379, by rfl⟩ : syracuseStep 2221839 = 3332759) B3332759
theorem B3332765 : Blo 2221435 3332765 := bbase (se 3 (by rfl) ⟨624893, by rfl⟩ : syracuseStep 3332765 = 1249787) (by norm_num)
theorem B2221843 : Blo 2221435 2221843 := bstep (se 1 (by rfl) ⟨1666382, by rfl⟩ : syracuseStep 2221843 = 3332765) B3332765
theorem B4999157 : Blo 2221435 4999157 := bbase (se 5 (by rfl) ⟨234335, by rfl⟩ : syracuseStep 4999157 = 468671) (by norm_num)
theorem B3332771 : Blo 2221435 3332771 := bstep (se 1 (by rfl) ⟨2499578, by rfl⟩ : syracuseStep 3332771 = 4999157) B4999157
theorem B2221847 : Blo 2221435 2221847 := bstep (se 1 (by rfl) ⟨1666385, by rfl⟩ : syracuseStep 2221847 = 3332771) B3332771
theorem B20269493 : Blo 2221435 20269493 := bbase (se 5 (by rfl) ⟨950132, by rfl⟩ : syracuseStep 20269493 = 1900265) (by norm_num)
theorem B13512995 : Blo 2221435 13512995 := bstep (se 1 (by rfl) ⟨10134746, by rfl⟩ : syracuseStep 13512995 = 20269493) B20269493
theorem B9008663 : Blo 2221435 9008663 := bstep (se 1 (by rfl) ⟨6756497, by rfl⟩ : syracuseStep 9008663 = 13512995) B13512995
theorem B96092405 : Blo 2221435 96092405 := bstep (se 5 (by rfl) ⟨4504331, by rfl⟩ : syracuseStep 96092405 = 9008663) B9008663
theorem B64061603 : Blo 2221435 64061603 := bstep (se 1 (by rfl) ⟨48046202, by rfl⟩ : syracuseStep 64061603 = 96092405) B96092405
theorem B42707735 : Blo 2221435 42707735 := bstep (se 1 (by rfl) ⟨32030801, by rfl⟩ : syracuseStep 42707735 = 64061603) B64061603
theorem B28471823 : Blo 2221435 28471823 := bstep (se 1 (by rfl) ⟨21353867, by rfl⟩ : syracuseStep 28471823 = 42707735) B42707735
theorem B18981215 : Blo 2221435 18981215 := bstep (se 1 (by rfl) ⟨14235911, by rfl⟩ : syracuseStep 18981215 = 28471823) B28471823
theorem B12654143 : Blo 2221435 12654143 := bstep (se 1 (by rfl) ⟨9490607, by rfl⟩ : syracuseStep 12654143 = 18981215) B18981215
theorem B8436095 : Blo 2221435 8436095 := bstep (se 1 (by rfl) ⟨6327071, by rfl⟩ : syracuseStep 8436095 = 12654143) B12654143
theorem B5624063 : Blo 2221435 5624063 := bstep (se 1 (by rfl) ⟨4218047, by rfl⟩ : syracuseStep 5624063 = 8436095) B8436095
theorem B3749375 : Blo 2221435 3749375 := bstep (se 1 (by rfl) ⟨2812031, by rfl⟩ : syracuseStep 3749375 = 5624063) B5624063
theorem B2499583 : Blo 2221435 2499583 := bstep (se 1 (by rfl) ⟨1874687, by rfl⟩ : syracuseStep 2499583 = 3749375) B3749375
theorem B3332777 : Blo 2221435 3332777 := bstep (se 2 (by rfl) ⟨1249791, by rfl⟩ : syracuseStep 3332777 = 2499583) B2499583
theorem B2221851 : Blo 2221435 2221851 := bstep (se 1 (by rfl) ⟨1666388, by rfl⟩ : syracuseStep 2221851 = 3332777) B3332777
theorem B3163541 : Blo 2221435 3163541 := bbase (se 6 (by rfl) ⟨74145, by rfl⟩ : syracuseStep 3163541 = 148291) (by norm_num)
theorem B8436109 : Blo 2221435 8436109 := bstep (se 3 (by rfl) ⟨1581770, by rfl⟩ : syracuseStep 8436109 = 3163541) B3163541
theorem B11248145 : Blo 2221435 11248145 := bstep (se 2 (by rfl) ⟨4218054, by rfl⟩ : syracuseStep 11248145 = 8436109) B8436109
theorem B7498763 : Blo 2221435 7498763 := bstep (se 1 (by rfl) ⟨5624072, by rfl⟩ : syracuseStep 7498763 = 11248145) B11248145
theorem B4999175 : Blo 2221435 4999175 := bstep (se 1 (by rfl) ⟨3749381, by rfl⟩ : syracuseStep 4999175 = 7498763) B7498763
theorem B3332783 : Blo 2221435 3332783 := bstep (se 1 (by rfl) ⟨2499587, by rfl⟩ : syracuseStep 3332783 = 4999175) B4999175
theorem B2221855 : Blo 2221435 2221855 := bstep (se 1 (by rfl) ⟨1666391, by rfl⟩ : syracuseStep 2221855 = 3332783) B3332783
theorem B3332789 : Blo 2221435 3332789 := bbase (se 5 (by rfl) ⟨156224, by rfl⟩ : syracuseStep 3332789 = 312449) (by norm_num)
theorem B2221859 : Blo 2221435 2221859 := bstep (se 1 (by rfl) ⟨1666394, by rfl⟩ : syracuseStep 2221859 = 3332789) B3332789
theorem B5624093 : Blo 2221435 5624093 := bbase (se 3 (by rfl) ⟨1054517, by rfl⟩ : syracuseStep 5624093 = 2109035) (by norm_num)
theorem B3749395 : Blo 2221435 3749395 := bstep (se 1 (by rfl) ⟨2812046, by rfl⟩ : syracuseStep 3749395 = 5624093) B5624093
theorem B4999193 : Blo 2221435 4999193 := bstep (se 2 (by rfl) ⟨1874697, by rfl⟩ : syracuseStep 4999193 = 3749395) B3749395
theorem B3332795 : Blo 2221435 3332795 := bstep (se 1 (by rfl) ⟨2499596, by rfl⟩ : syracuseStep 3332795 = 4999193) B4999193
theorem B2221863 : Blo 2221435 2221863 := bstep (se 1 (by rfl) ⟨1666397, by rfl⟩ : syracuseStep 2221863 = 3332795) B3332795
theorem B2499601 : Blo 2221435 2499601 := bbase (se 2 (by rfl) ⟨937350, by rfl⟩ : syracuseStep 2499601 = 1874701) (by norm_num)
theorem B3332801 : Blo 2221435 3332801 := bstep (se 2 (by rfl) ⟨1249800, by rfl⟩ : syracuseStep 3332801 = 2499601) B2499601
theorem B2221867 : Blo 2221435 2221867 := bstep (se 1 (by rfl) ⟨1666400, by rfl⟩ : syracuseStep 2221867 = 3332801) B3332801
theorem B4218085 : Blo 2221435 4218085 := bbase (se 4 (by rfl) ⟨395445, by rfl⟩ : syracuseStep 4218085 = 790891) (by norm_num)
theorem B5624113 : Blo 2221435 5624113 := bstep (se 2 (by rfl) ⟨2109042, by rfl⟩ : syracuseStep 5624113 = 4218085) B4218085
theorem B7498817 : Blo 2221435 7498817 := bstep (se 2 (by rfl) ⟨2812056, by rfl⟩ : syracuseStep 7498817 = 5624113) B5624113
theorem B4999211 : Blo 2221435 4999211 := bstep (se 1 (by rfl) ⟨3749408, by rfl⟩ : syracuseStep 4999211 = 7498817) B7498817
theorem B3332807 : Blo 2221435 3332807 := bstep (se 1 (by rfl) ⟨2499605, by rfl⟩ : syracuseStep 3332807 = 4999211) B4999211
theorem B2221871 : Blo 2221435 2221871 := bstep (se 1 (by rfl) ⟨1666403, by rfl⟩ : syracuseStep 2221871 = 3332807) B3332807
theorem B3332813 : Blo 2221435 3332813 := bbase (se 3 (by rfl) ⟨624902, by rfl⟩ : syracuseStep 3332813 = 1249805) (by norm_num)
theorem B2221875 : Blo 2221435 2221875 := bstep (se 1 (by rfl) ⟨1666406, by rfl⟩ : syracuseStep 2221875 = 3332813) B3332813
theorem B4999229 : Blo 2221435 4999229 := bbase (se 3 (by rfl) ⟨937355, by rfl⟩ : syracuseStep 4999229 = 1874711) (by norm_num)
theorem B3332819 : Blo 2221435 3332819 := bstep (se 1 (by rfl) ⟨2499614, by rfl⟩ : syracuseStep 3332819 = 4999229) B4999229
theorem B2221879 : Blo 2221435 2221879 := bstep (se 1 (by rfl) ⟨1666409, by rfl⟩ : syracuseStep 2221879 = 3332819) B3332819
theorem B3749429 : Blo 2221435 3749429 := bbase (se 5 (by rfl) ⟨175754, by rfl⟩ : syracuseStep 3749429 = 351509) (by norm_num)
theorem B2499619 : Blo 2221435 2499619 := bstep (se 1 (by rfl) ⟨1874714, by rfl⟩ : syracuseStep 2499619 = 3749429) B3749429
theorem B3332825 : Blo 2221435 3332825 := bstep (se 2 (by rfl) ⟨1249809, by rfl⟩ : syracuseStep 3332825 = 2499619) B2499619
theorem B2221883 : Blo 2221435 2221883 := bstep (se 1 (by rfl) ⟨1666412, by rfl⟩ : syracuseStep 2221883 = 3332825) B3332825
theorem B6327173 : Blo 2221435 6327173 := bbase (se 4 (by rfl) ⟨593172, by rfl⟩ : syracuseStep 6327173 = 1186345) (by norm_num)
theorem B16872461 : Blo 2221435 16872461 := bstep (se 3 (by rfl) ⟨3163586, by rfl⟩ : syracuseStep 16872461 = 6327173) B6327173
theorem B11248307 : Blo 2221435 11248307 := bstep (se 1 (by rfl) ⟨8436230, by rfl⟩ : syracuseStep 11248307 = 16872461) B16872461
theorem B7498871 : Blo 2221435 7498871 := bstep (se 1 (by rfl) ⟨5624153, by rfl⟩ : syracuseStep 7498871 = 11248307) B11248307
theorem B4999247 : Blo 2221435 4999247 := bstep (se 1 (by rfl) ⟨3749435, by rfl⟩ : syracuseStep 4999247 = 7498871) B7498871
theorem B3332831 : Blo 2221435 3332831 := bstep (se 1 (by rfl) ⟨2499623, by rfl⟩ : syracuseStep 3332831 = 4999247) B4999247
theorem B2221887 : Blo 2221435 2221887 := bstep (se 1 (by rfl) ⟨1666415, by rfl⟩ : syracuseStep 2221887 = 3332831) B3332831
theorem B3332837 : Blo 2221435 3332837 := bbase (se 4 (by rfl) ⟨312453, by rfl⟩ : syracuseStep 3332837 = 624907) (by norm_num)
theorem B2221891 : Blo 2221435 2221891 := bstep (se 1 (by rfl) ⟨1666418, by rfl⟩ : syracuseStep 2221891 = 3332837) B3332837
theorem B100081493 : Blo 2221435 100081493 := bbase (se 9 (by rfl) ⟨293207, by rfl⟩ : syracuseStep 100081493 = 586415) (by norm_num)
theorem B66720995 : Blo 2221435 66720995 := bstep (se 1 (by rfl) ⟨50040746, by rfl⟩ : syracuseStep 66720995 = 100081493) B100081493
theorem B44480663 : Blo 2221435 44480663 := bstep (se 1 (by rfl) ⟨33360497, by rfl⟩ : syracuseStep 44480663 = 66720995) B66720995
theorem B29653775 : Blo 2221435 29653775 := bstep (se 1 (by rfl) ⟨22240331, by rfl⟩ : syracuseStep 29653775 = 44480663) B44480663
theorem B19769183 : Blo 2221435 19769183 := bstep (se 1 (by rfl) ⟨14826887, by rfl⟩ : syracuseStep 19769183 = 29653775) B29653775
theorem B13179455 : Blo 2221435 13179455 := bstep (se 1 (by rfl) ⟨9884591, by rfl⟩ : syracuseStep 13179455 = 19769183) B19769183
theorem B8786303 : Blo 2221435 8786303 := bstep (se 1 (by rfl) ⟨6589727, by rfl⟩ : syracuseStep 8786303 = 13179455) B13179455
theorem B5857535 : Blo 2221435 5857535 := bstep (se 1 (by rfl) ⟨4393151, by rfl⟩ : syracuseStep 5857535 = 8786303) B8786303
theorem B3905023 : Blo 2221435 3905023 := bstep (se 1 (by rfl) ⟨2928767, by rfl⟩ : syracuseStep 3905023 = 5857535) B5857535
theorem B5206697 : Blo 2221435 5206697 := bstep (se 2 (by rfl) ⟨1952511, by rfl⟩ : syracuseStep 5206697 = 3905023) B3905023
theorem B3471131 : Blo 2221435 3471131 := bstep (se 1 (by rfl) ⟨2603348, by rfl⟩ : syracuseStep 3471131 = 5206697) B5206697
theorem B9256349 : Blo 2221435 9256349 := bstep (se 3 (by rfl) ⟨1735565, by rfl⟩ : syracuseStep 9256349 = 3471131) B3471131
theorem B6170899 : Blo 2221435 6170899 := bstep (se 1 (by rfl) ⟨4628174, by rfl⟩ : syracuseStep 6170899 = 9256349) B9256349
theorem B8227865 : Blo 2221435 8227865 := bstep (se 2 (by rfl) ⟨3085449, by rfl⟩ : syracuseStep 8227865 = 6170899) B6170899
theorem B5485243 : Blo 2221435 5485243 := bstep (se 1 (by rfl) ⟨4113932, by rfl⟩ : syracuseStep 5485243 = 8227865) B8227865
theorem B7313657 : Blo 2221435 7313657 := bstep (se 2 (by rfl) ⟨2742621, by rfl⟩ : syracuseStep 7313657 = 5485243) B5485243
theorem B78012341 : Blo 2221435 78012341 := bstep (se 5 (by rfl) ⟨3656828, by rfl⟩ : syracuseStep 78012341 = 7313657) B7313657
theorem B52008227 : Blo 2221435 52008227 := bstep (se 1 (by rfl) ⟨39006170, by rfl⟩ : syracuseStep 52008227 = 78012341) B78012341
theorem B34672151 : Blo 2221435 34672151 := bstep (se 1 (by rfl) ⟨26004113, by rfl⟩ : syracuseStep 34672151 = 52008227) B52008227
theorem B92459069 : Blo 2221435 92459069 := bstep (se 3 (by rfl) ⟨17336075, by rfl⟩ : syracuseStep 92459069 = 34672151) B34672151
theorem B61639379 : Blo 2221435 61639379 := bstep (se 1 (by rfl) ⟨46229534, by rfl⟩ : syracuseStep 61639379 = 92459069) B92459069
theorem B41092919 : Blo 2221435 41092919 := bstep (se 1 (by rfl) ⟨30819689, by rfl⟩ : syracuseStep 41092919 = 61639379) B61639379
theorem B27395279 : Blo 2221435 27395279 := bstep (se 1 (by rfl) ⟨20546459, by rfl⟩ : syracuseStep 27395279 = 41092919) B41092919
theorem B18263519 : Blo 2221435 18263519 := bstep (se 1 (by rfl) ⟨13697639, by rfl⟩ : syracuseStep 18263519 = 27395279) B27395279
theorem B12175679 : Blo 2221435 12175679 := bstep (se 1 (by rfl) ⟨9131759, by rfl⟩ : syracuseStep 12175679 = 18263519) B18263519
theorem B8117119 : Blo 2221435 8117119 := bstep (se 1 (by rfl) ⟨6087839, by rfl⟩ : syracuseStep 8117119 = 12175679) B12175679
theorem B10822825 : Blo 2221435 10822825 := bstep (se 2 (by rfl) ⟨4058559, by rfl⟩ : syracuseStep 10822825 = 8117119) B8117119
theorem B57721733 : Blo 2221435 57721733 := bstep (se 4 (by rfl) ⟨5411412, by rfl⟩ : syracuseStep 57721733 = 10822825) B10822825
theorem B38481155 : Blo 2221435 38481155 := bstep (se 1 (by rfl) ⟨28860866, by rfl⟩ : syracuseStep 38481155 = 57721733) B57721733
theorem B25654103 : Blo 2221435 25654103 := bstep (se 1 (by rfl) ⟨19240577, by rfl⟩ : syracuseStep 25654103 = 38481155) B38481155
theorem B17102735 : Blo 2221435 17102735 := bstep (se 1 (by rfl) ⟨12827051, by rfl⟩ : syracuseStep 17102735 = 25654103) B25654103
theorem B11401823 : Blo 2221435 11401823 := bstep (se 1 (by rfl) ⟨8551367, by rfl⟩ : syracuseStep 11401823 = 17102735) B17102735
theorem B7601215 : Blo 2221435 7601215 := bstep (se 1 (by rfl) ⟨5700911, by rfl⟩ : syracuseStep 7601215 = 11401823) B11401823
theorem B10134953 : Blo 2221435 10134953 := bstep (se 2 (by rfl) ⟨3800607, by rfl⟩ : syracuseStep 10134953 = 7601215) B7601215
theorem B6756635 : Blo 2221435 6756635 := bstep (se 1 (by rfl) ⟨5067476, by rfl⟩ : syracuseStep 6756635 = 10134953) B10134953
theorem B4504423 : Blo 2221435 4504423 := bstep (se 1 (by rfl) ⟨3378317, by rfl⟩ : syracuseStep 4504423 = 6756635) B6756635
theorem B6005897 : Blo 2221435 6005897 := bstep (se 2 (by rfl) ⟨2252211, by rfl⟩ : syracuseStep 6005897 = 4504423) B4504423
theorem B4003931 : Blo 2221435 4003931 := bstep (se 1 (by rfl) ⟨3002948, by rfl⟩ : syracuseStep 4003931 = 6005897) B6005897
theorem B2669287 : Blo 2221435 2669287 := bstep (se 1 (by rfl) ⟨2001965, by rfl⟩ : syracuseStep 2669287 = 4003931) B4003931
theorem B3559049 : Blo 2221435 3559049 := bstep (se 2 (by rfl) ⟨1334643, by rfl⟩ : syracuseStep 3559049 = 2669287) B2669287
theorem B2372699 : Blo 2221435 2372699 := bstep (se 1 (by rfl) ⟨1779524, by rfl⟩ : syracuseStep 2372699 = 3559049) B3559049
theorem B6327197 : Blo 2221435 6327197 := bstep (se 3 (by rfl) ⟨1186349, by rfl⟩ : syracuseStep 6327197 = 2372699) B2372699
theorem B4218131 : Blo 2221435 4218131 := bstep (se 1 (by rfl) ⟨3163598, by rfl⟩ : syracuseStep 4218131 = 6327197) B6327197
theorem B2812087 : Blo 2221435 2812087 := bstep (se 1 (by rfl) ⟨2109065, by rfl⟩ : syracuseStep 2812087 = 4218131) B4218131
theorem B3749449 : Blo 2221435 3749449 := bstep (se 2 (by rfl) ⟨1406043, by rfl⟩ : syracuseStep 3749449 = 2812087) B2812087
theorem B4999265 : Blo 2221435 4999265 := bstep (se 2 (by rfl) ⟨1874724, by rfl⟩ : syracuseStep 4999265 = 3749449) B3749449
theorem B3332843 : Blo 2221435 3332843 := bstep (se 1 (by rfl) ⟨2499632, by rfl⟩ : syracuseStep 3332843 = 4999265) B4999265
theorem B2221895 : Blo 2221435 2221895 := bstep (se 1 (by rfl) ⟨1666421, by rfl⟩ : syracuseStep 2221895 = 3332843) B3332843
theorem B2499637 : Blo 2221435 2499637 := bbase (se 5 (by rfl) ⟨117170, by rfl⟩ : syracuseStep 2499637 = 234341) (by norm_num)
theorem B3332849 : Blo 2221435 3332849 := bstep (se 2 (by rfl) ⟨1249818, by rfl⟩ : syracuseStep 3332849 = 2499637) B2499637
theorem B2221899 : Blo 2221435 2221899 := bstep (se 1 (by rfl) ⟨1666424, by rfl⟩ : syracuseStep 2221899 = 3332849) B3332849
theorem B2812097 : Blo 2221435 2812097 := bbase (se 2 (by rfl) ⟨1054536, by rfl⟩ : syracuseStep 2812097 = 2109073) (by norm_num)
theorem B7498925 : Blo 2221435 7498925 := bstep (se 3 (by rfl) ⟨1406048, by rfl⟩ : syracuseStep 7498925 = 2812097) B2812097
theorem B4999283 : Blo 2221435 4999283 := bstep (se 1 (by rfl) ⟨3749462, by rfl⟩ : syracuseStep 4999283 = 7498925) B7498925
theorem B3332855 : Blo 2221435 3332855 := bstep (se 1 (by rfl) ⟨2499641, by rfl⟩ : syracuseStep 3332855 = 4999283) B4999283
theorem B2221903 : Blo 2221435 2221903 := bstep (se 1 (by rfl) ⟨1666427, by rfl⟩ : syracuseStep 2221903 = 3332855) B3332855
theorem B3332861 : Blo 2221435 3332861 := bbase (se 3 (by rfl) ⟨624911, by rfl⟩ : syracuseStep 3332861 = 1249823) (by norm_num)
theorem B2221907 : Blo 2221435 2221907 := bstep (se 1 (by rfl) ⟨1666430, by rfl⟩ : syracuseStep 2221907 = 3332861) B3332861
theorem B4999301 : Blo 2221435 4999301 := bbase (se 4 (by rfl) ⟨468684, by rfl⟩ : syracuseStep 4999301 = 937369) (by norm_num)
theorem B3332867 : Blo 2221435 3332867 := bstep (se 1 (by rfl) ⟨2499650, by rfl⟩ : syracuseStep 3332867 = 4999301) B4999301
theorem B2221911 : Blo 2221435 2221911 := bstep (se 1 (by rfl) ⟨1666433, by rfl⟩ : syracuseStep 2221911 = 3332867) B3332867
theorem B5411461 : Blo 2221435 5411461 := bbase (se 4 (by rfl) ⟨507324, by rfl⟩ : syracuseStep 5411461 = 1014649) (by norm_num)
theorem B7215281 : Blo 2221435 7215281 := bstep (se 2 (by rfl) ⟨2705730, by rfl⟩ : syracuseStep 7215281 = 5411461) B5411461
theorem B4810187 : Blo 2221435 4810187 := bstep (se 1 (by rfl) ⟨3607640, by rfl⟩ : syracuseStep 4810187 = 7215281) B7215281
theorem B12827165 : Blo 2221435 12827165 := bstep (se 3 (by rfl) ⟨2405093, by rfl⟩ : syracuseStep 12827165 = 4810187) B4810187
theorem B34205773 : Blo 2221435 34205773 := bstep (se 3 (by rfl) ⟨6413582, by rfl⟩ : syracuseStep 34205773 = 12827165) B12827165
theorem B45607697 : Blo 2221435 45607697 := bstep (se 2 (by rfl) ⟨17102886, by rfl⟩ : syracuseStep 45607697 = 34205773) B34205773
theorem B30405131 : Blo 2221435 30405131 := bstep (se 1 (by rfl) ⟨22803848, by rfl⟩ : syracuseStep 30405131 = 45607697) B45607697
theorem B20270087 : Blo 2221435 20270087 := bstep (se 1 (by rfl) ⟨15202565, by rfl⟩ : syracuseStep 20270087 = 30405131) B30405131
theorem B13513391 : Blo 2221435 13513391 := bstep (se 1 (by rfl) ⟨10135043, by rfl⟩ : syracuseStep 13513391 = 20270087) B20270087
theorem B9008927 : Blo 2221435 9008927 := bstep (se 1 (by rfl) ⟨6756695, by rfl⟩ : syracuseStep 9008927 = 13513391) B13513391
theorem B6005951 : Blo 2221435 6005951 := bstep (se 1 (by rfl) ⟨4504463, by rfl⟩ : syracuseStep 6005951 = 9008927) B9008927
theorem B4003967 : Blo 2221435 4003967 := bstep (se 1 (by rfl) ⟨3002975, by rfl⟩ : syracuseStep 4003967 = 6005951) B6005951
theorem B2669311 : Blo 2221435 2669311 := bstep (se 1 (by rfl) ⟨2001983, by rfl⟩ : syracuseStep 2669311 = 4003967) B4003967
theorem B3559081 : Blo 2221435 3559081 := bstep (se 2 (by rfl) ⟨1334655, by rfl⟩ : syracuseStep 3559081 = 2669311) B2669311
theorem B4745441 : Blo 2221435 4745441 := bstep (se 2 (by rfl) ⟨1779540, by rfl⟩ : syracuseStep 4745441 = 3559081) B3559081
theorem B3163627 : Blo 2221435 3163627 := bstep (se 1 (by rfl) ⟨2372720, by rfl⟩ : syracuseStep 3163627 = 4745441) B4745441
theorem B4218169 : Blo 2221435 4218169 := bstep (se 2 (by rfl) ⟨1581813, by rfl⟩ : syracuseStep 4218169 = 3163627) B3163627
theorem B5624225 : Blo 2221435 5624225 := bstep (se 2 (by rfl) ⟨2109084, by rfl⟩ : syracuseStep 5624225 = 4218169) B4218169
theorem B3749483 : Blo 2221435 3749483 := bstep (se 1 (by rfl) ⟨2812112, by rfl⟩ : syracuseStep 3749483 = 5624225) B5624225
theorem B2499655 : Blo 2221435 2499655 := bstep (se 1 (by rfl) ⟨1874741, by rfl⟩ : syracuseStep 2499655 = 3749483) B3749483
theorem B3332873 : Blo 2221435 3332873 := bstep (se 2 (by rfl) ⟨1249827, by rfl⟩ : syracuseStep 3332873 = 2499655) B2499655
theorem B2221915 : Blo 2221435 2221915 := bstep (se 1 (by rfl) ⟨1666436, by rfl⟩ : syracuseStep 2221915 = 3332873) B3332873
theorem B11248469 : Blo 2221435 11248469 := bbase (se 9 (by rfl) ⟨32954, by rfl⟩ : syracuseStep 11248469 = 65909) (by norm_num)
theorem B7498979 : Blo 2221435 7498979 := bstep (se 1 (by rfl) ⟨5624234, by rfl⟩ : syracuseStep 7498979 = 11248469) B11248469
theorem B4999319 : Blo 2221435 4999319 := bstep (se 1 (by rfl) ⟨3749489, by rfl⟩ : syracuseStep 4999319 = 7498979) B7498979
theorem B3332879 : Blo 2221435 3332879 := bstep (se 1 (by rfl) ⟨2499659, by rfl⟩ : syracuseStep 3332879 = 4999319) B4999319
theorem B2221919 : Blo 2221435 2221919 := bstep (se 1 (by rfl) ⟨1666439, by rfl⟩ : syracuseStep 2221919 = 3332879) B3332879
theorem B3332885 : Blo 2221435 3332885 := bbase (se 6 (by rfl) ⟨78114, by rfl⟩ : syracuseStep 3332885 = 156229) (by norm_num)
theorem B2221923 : Blo 2221435 2221923 := bstep (se 1 (by rfl) ⟨1666442, by rfl⟩ : syracuseStep 2221923 = 3332885) B3332885
theorem B72071765 : Blo 2221435 72071765 := bbase (se 8 (by rfl) ⟨422295, by rfl⟩ : syracuseStep 72071765 = 844591) (by norm_num)
theorem B48047843 : Blo 2221435 48047843 := bstep (se 1 (by rfl) ⟨36035882, by rfl⟩ : syracuseStep 48047843 = 72071765) B72071765
theorem B32031895 : Blo 2221435 32031895 := bstep (se 1 (by rfl) ⟨24023921, by rfl⟩ : syracuseStep 32031895 = 48047843) B48047843
theorem B42709193 : Blo 2221435 42709193 := bstep (se 2 (by rfl) ⟨16015947, by rfl⟩ : syracuseStep 42709193 = 32031895) B32031895
theorem B28472795 : Blo 2221435 28472795 := bstep (se 1 (by rfl) ⟨21354596, by rfl⟩ : syracuseStep 28472795 = 42709193) B42709193
theorem B18981863 : Blo 2221435 18981863 := bstep (se 1 (by rfl) ⟨14236397, by rfl⟩ : syracuseStep 18981863 = 28472795) B28472795
theorem B12654575 : Blo 2221435 12654575 := bstep (se 1 (by rfl) ⟨9490931, by rfl⟩ : syracuseStep 12654575 = 18981863) B18981863
theorem B8436383 : Blo 2221435 8436383 := bstep (se 1 (by rfl) ⟨6327287, by rfl⟩ : syracuseStep 8436383 = 12654575) B12654575
theorem B5624255 : Blo 2221435 5624255 := bstep (se 1 (by rfl) ⟨4218191, by rfl⟩ : syracuseStep 5624255 = 8436383) B8436383
theorem B3749503 : Blo 2221435 3749503 := bstep (se 1 (by rfl) ⟨2812127, by rfl⟩ : syracuseStep 3749503 = 5624255) B5624255
theorem B4999337 : Blo 2221435 4999337 := bstep (se 2 (by rfl) ⟨1874751, by rfl⟩ : syracuseStep 4999337 = 3749503) B3749503
theorem B3332891 : Blo 2221435 3332891 := bstep (se 1 (by rfl) ⟨2499668, by rfl⟩ : syracuseStep 3332891 = 4999337) B4999337
theorem B2221927 : Blo 2221435 2221927 := bstep (se 1 (by rfl) ⟨1666445, by rfl⟩ : syracuseStep 2221927 = 3332891) B3332891
theorem B2499673 : Blo 2221435 2499673 := bbase (se 2 (by rfl) ⟨937377, by rfl⟩ : syracuseStep 2499673 = 1874755) (by norm_num)
theorem B3332897 : Blo 2221435 3332897 := bstep (se 2 (by rfl) ⟨1249836, by rfl⟩ : syracuseStep 3332897 = 2499673) B2499673
theorem B2221931 : Blo 2221435 2221931 := bstep (se 1 (by rfl) ⟨1666448, by rfl⟩ : syracuseStep 2221931 = 3332897) B3332897
theorem B5338669 : Blo 2221435 5338669 := bbase (se 3 (by rfl) ⟨1001000, by rfl⟩ : syracuseStep 5338669 = 2002001) (by norm_num)
theorem B7118225 : Blo 2221435 7118225 := bstep (se 2 (by rfl) ⟨2669334, by rfl⟩ : syracuseStep 7118225 = 5338669) B5338669
theorem B4745483 : Blo 2221435 4745483 := bstep (se 1 (by rfl) ⟨3559112, by rfl⟩ : syracuseStep 4745483 = 7118225) B7118225
theorem B3163655 : Blo 2221435 3163655 := bstep (se 1 (by rfl) ⟨2372741, by rfl⟩ : syracuseStep 3163655 = 4745483) B4745483
theorem B8436413 : Blo 2221435 8436413 := bstep (se 3 (by rfl) ⟨1581827, by rfl⟩ : syracuseStep 8436413 = 3163655) B3163655
theorem B5624275 : Blo 2221435 5624275 := bstep (se 1 (by rfl) ⟨4218206, by rfl⟩ : syracuseStep 5624275 = 8436413) B8436413
theorem B7499033 : Blo 2221435 7499033 := bstep (se 2 (by rfl) ⟨2812137, by rfl⟩ : syracuseStep 7499033 = 5624275) B5624275
theorem B4999355 : Blo 2221435 4999355 := bstep (se 1 (by rfl) ⟨3749516, by rfl⟩ : syracuseStep 4999355 = 7499033) B7499033
theorem B3332903 : Blo 2221435 3332903 := bstep (se 1 (by rfl) ⟨2499677, by rfl⟩ : syracuseStep 3332903 = 4999355) B4999355
theorem B2221935 : Blo 2221435 2221935 := bstep (se 1 (by rfl) ⟨1666451, by rfl⟩ : syracuseStep 2221935 = 3332903) B3332903
theorem B3332909 : Blo 2221435 3332909 := bbase (se 3 (by rfl) ⟨624920, by rfl⟩ : syracuseStep 3332909 = 1249841) (by norm_num)
theorem B2221939 : Blo 2221435 2221939 := bstep (se 1 (by rfl) ⟨1666454, by rfl⟩ : syracuseStep 2221939 = 3332909) B3332909
theorem B4999373 : Blo 2221435 4999373 := bbase (se 3 (by rfl) ⟨937382, by rfl⟩ : syracuseStep 4999373 = 1874765) (by norm_num)
theorem B3332915 : Blo 2221435 3332915 := bstep (se 1 (by rfl) ⟨2499686, by rfl⟩ : syracuseStep 3332915 = 4999373) B4999373
theorem B2221943 : Blo 2221435 2221943 := bstep (se 1 (by rfl) ⟨1666457, by rfl⟩ : syracuseStep 2221943 = 3332915) B3332915
theorem B2812153 : Blo 2221435 2812153 := bbase (se 2 (by rfl) ⟨1054557, by rfl⟩ : syracuseStep 2812153 = 2109115) (by norm_num)
theorem B3749537 : Blo 2221435 3749537 := bstep (se 2 (by rfl) ⟨1406076, by rfl⟩ : syracuseStep 3749537 = 2812153) B2812153
theorem B2499691 : Blo 2221435 2499691 := bstep (se 1 (by rfl) ⟨1874768, by rfl⟩ : syracuseStep 2499691 = 3749537) B3749537
theorem B3332921 : Blo 2221435 3332921 := bstep (se 2 (by rfl) ⟨1249845, by rfl⟩ : syracuseStep 3332921 = 2499691) B2499691
theorem B2221947 : Blo 2221435 2221947 := bstep (se 1 (by rfl) ⟨1666460, by rfl⟩ : syracuseStep 2221947 = 3332921) B3332921
theorem B10677413 : Blo 2221435 10677413 := bbase (se 4 (by rfl) ⟨1001007, by rfl⟩ : syracuseStep 10677413 = 2002015) (by norm_num)
theorem B7118275 : Blo 2221435 7118275 := bstep (se 1 (by rfl) ⟨5338706, by rfl⟩ : syracuseStep 7118275 = 10677413) B10677413
theorem B9491033 : Blo 2221435 9491033 := bstep (se 2 (by rfl) ⟨3559137, by rfl⟩ : syracuseStep 9491033 = 7118275) B7118275
theorem B25309421 : Blo 2221435 25309421 := bstep (se 3 (by rfl) ⟨4745516, by rfl⟩ : syracuseStep 25309421 = 9491033) B9491033
theorem B16872947 : Blo 2221435 16872947 := bstep (se 1 (by rfl) ⟨12654710, by rfl⟩ : syracuseStep 16872947 = 25309421) B25309421
theorem B11248631 : Blo 2221435 11248631 := bstep (se 1 (by rfl) ⟨8436473, by rfl⟩ : syracuseStep 11248631 = 16872947) B16872947
theorem B7499087 : Blo 2221435 7499087 := bstep (se 1 (by rfl) ⟨5624315, by rfl⟩ : syracuseStep 7499087 = 11248631) B11248631
theorem B4999391 : Blo 2221435 4999391 := bstep (se 1 (by rfl) ⟨3749543, by rfl⟩ : syracuseStep 4999391 = 7499087) B7499087
theorem B3332927 : Blo 2221435 3332927 := bstep (se 1 (by rfl) ⟨2499695, by rfl⟩ : syracuseStep 3332927 = 4999391) B4999391
theorem B2221951 : Blo 2221435 2221951 := bstep (se 1 (by rfl) ⟨1666463, by rfl⟩ : syracuseStep 2221951 = 3332927) B3332927
theorem B3332933 : Blo 2221435 3332933 := bbase (se 4 (by rfl) ⟨312462, by rfl⟩ : syracuseStep 3332933 = 624925) (by norm_num)
theorem B2221955 : Blo 2221435 2221955 := bstep (se 1 (by rfl) ⟨1666466, by rfl⟩ : syracuseStep 2221955 = 3332933) B3332933
theorem B3749557 : Blo 2221435 3749557 := bbase (se 5 (by rfl) ⟨175760, by rfl⟩ : syracuseStep 3749557 = 351521) (by norm_num)
theorem B4999409 : Blo 2221435 4999409 := bstep (se 2 (by rfl) ⟨1874778, by rfl⟩ : syracuseStep 4999409 = 3749557) B3749557
theorem B3332939 : Blo 2221435 3332939 := bstep (se 1 (by rfl) ⟨2499704, by rfl⟩ : syracuseStep 3332939 = 4999409) B4999409
theorem B2221959 : Blo 2221435 2221959 := bstep (se 1 (by rfl) ⟨1666469, by rfl⟩ : syracuseStep 2221959 = 3332939) B3332939
theorem B2499709 : Blo 2221435 2499709 := bbase (se 3 (by rfl) ⟨468695, by rfl⟩ : syracuseStep 2499709 = 937391) (by norm_num)
theorem B3332945 : Blo 2221435 3332945 := bstep (se 2 (by rfl) ⟨1249854, by rfl⟩ : syracuseStep 3332945 = 2499709) B2499709
theorem B2221963 : Blo 2221435 2221963 := bstep (se 1 (by rfl) ⟨1666472, by rfl⟩ : syracuseStep 2221963 = 3332945) B3332945
theorem B7499141 : Blo 2221435 7499141 := bbase (se 4 (by rfl) ⟨703044, by rfl⟩ : syracuseStep 7499141 = 1406089) (by norm_num)
theorem B4999427 : Blo 2221435 4999427 := bstep (se 1 (by rfl) ⟨3749570, by rfl⟩ : syracuseStep 4999427 = 7499141) B7499141
theorem B3332951 : Blo 2221435 3332951 := bstep (se 1 (by rfl) ⟨2499713, by rfl⟩ : syracuseStep 3332951 = 4999427) B4999427
theorem B2221967 : Blo 2221435 2221967 := bstep (se 1 (by rfl) ⟨1666475, by rfl⟩ : syracuseStep 2221967 = 3332951) B3332951
theorem B3332957 : Blo 2221435 3332957 := bbase (se 3 (by rfl) ⟨624929, by rfl⟩ : syracuseStep 3332957 = 1249859) (by norm_num)
theorem B2221971 : Blo 2221435 2221971 := bstep (se 1 (by rfl) ⟨1666478, by rfl⟩ : syracuseStep 2221971 = 3332957) B3332957
theorem B4999445 : Blo 2221435 4999445 := bbase (se 6 (by rfl) ⟨117174, by rfl⟩ : syracuseStep 4999445 = 234349) (by norm_num)
theorem B3332963 : Blo 2221435 3332963 := bstep (se 1 (by rfl) ⟨2499722, by rfl⟩ : syracuseStep 3332963 = 4999445) B4999445
theorem B2221975 : Blo 2221435 2221975 := bstep (se 1 (by rfl) ⟨1666481, by rfl⟩ : syracuseStep 2221975 = 3332963) B3332963
theorem B8436581 : Blo 2221435 8436581 := bbase (se 4 (by rfl) ⟨790929, by rfl⟩ : syracuseStep 8436581 = 1581859) (by norm_num)
theorem B5624387 : Blo 2221435 5624387 := bstep (se 1 (by rfl) ⟨4218290, by rfl⟩ : syracuseStep 5624387 = 8436581) B8436581
theorem B3749591 : Blo 2221435 3749591 := bstep (se 1 (by rfl) ⟨2812193, by rfl⟩ : syracuseStep 3749591 = 5624387) B5624387
theorem B2499727 : Blo 2221435 2499727 := bstep (se 1 (by rfl) ⟨1874795, by rfl⟩ : syracuseStep 2499727 = 3749591) B3749591
theorem B3332969 : Blo 2221435 3332969 := bstep (se 2 (by rfl) ⟨1249863, by rfl⟩ : syracuseStep 3332969 = 2499727) B2499727
theorem B2221979 : Blo 2221435 2221979 := bstep (se 1 (by rfl) ⟨1666484, by rfl⟩ : syracuseStep 2221979 = 3332969) B3332969
theorem B3559189 : Blo 2221435 3559189 := bbase (se 6 (by rfl) ⟨83418, by rfl⟩ : syracuseStep 3559189 = 166837) (by norm_num)
theorem B4745585 : Blo 2221435 4745585 := bstep (se 2 (by rfl) ⟨1779594, by rfl⟩ : syracuseStep 4745585 = 3559189) B3559189
theorem B12654893 : Blo 2221435 12654893 := bstep (se 3 (by rfl) ⟨2372792, by rfl⟩ : syracuseStep 12654893 = 4745585) B4745585
theorem B8436595 : Blo 2221435 8436595 := bstep (se 1 (by rfl) ⟨6327446, by rfl⟩ : syracuseStep 8436595 = 12654893) B12654893
theorem B11248793 : Blo 2221435 11248793 := bstep (se 2 (by rfl) ⟨4218297, by rfl⟩ : syracuseStep 11248793 = 8436595) B8436595
theorem B7499195 : Blo 2221435 7499195 := bstep (se 1 (by rfl) ⟨5624396, by rfl⟩ : syracuseStep 7499195 = 11248793) B11248793
theorem B4999463 : Blo 2221435 4999463 := bstep (se 1 (by rfl) ⟨3749597, by rfl⟩ : syracuseStep 4999463 = 7499195) B7499195
theorem B3332975 : Blo 2221435 3332975 := bstep (se 1 (by rfl) ⟨2499731, by rfl⟩ : syracuseStep 3332975 = 4999463) B4999463
theorem B2221983 : Blo 2221435 2221983 := bstep (se 1 (by rfl) ⟨1666487, by rfl⟩ : syracuseStep 2221983 = 3332975) B3332975
theorem B3332981 : Blo 2221435 3332981 := bbase (se 5 (by rfl) ⟨156233, by rfl⟩ : syracuseStep 3332981 = 312467) (by norm_num)
theorem B2221987 : Blo 2221435 2221987 := bstep (se 1 (by rfl) ⟨1666490, by rfl⟩ : syracuseStep 2221987 = 3332981) B3332981
theorem B7118405 : Blo 2221435 7118405 := bbase (se 4 (by rfl) ⟨667350, by rfl⟩ : syracuseStep 7118405 = 1334701) (by norm_num)
theorem B4745603 : Blo 2221435 4745603 := bstep (se 1 (by rfl) ⟨3559202, by rfl⟩ : syracuseStep 4745603 = 7118405) B7118405
theorem B3163735 : Blo 2221435 3163735 := bstep (se 1 (by rfl) ⟨2372801, by rfl⟩ : syracuseStep 3163735 = 4745603) B4745603
theorem B4218313 : Blo 2221435 4218313 := bstep (se 2 (by rfl) ⟨1581867, by rfl⟩ : syracuseStep 4218313 = 3163735) B3163735
theorem B5624417 : Blo 2221435 5624417 := bstep (se 2 (by rfl) ⟨2109156, by rfl⟩ : syracuseStep 5624417 = 4218313) B4218313
theorem B3749611 : Blo 2221435 3749611 := bstep (se 1 (by rfl) ⟨2812208, by rfl⟩ : syracuseStep 3749611 = 5624417) B5624417
theorem B4999481 : Blo 2221435 4999481 := bstep (se 2 (by rfl) ⟨1874805, by rfl⟩ : syracuseStep 4999481 = 3749611) B3749611
theorem B3332987 : Blo 2221435 3332987 := bstep (se 1 (by rfl) ⟨2499740, by rfl⟩ : syracuseStep 3332987 = 4999481) B4999481
theorem B2221991 : Blo 2221435 2221991 := bstep (se 1 (by rfl) ⟨1666493, by rfl⟩ : syracuseStep 2221991 = 3332987) B3332987
theorem B2499745 : Blo 2221435 2499745 := bbase (se 2 (by rfl) ⟨937404, by rfl⟩ : syracuseStep 2499745 = 1874809) (by norm_num)
theorem B3332993 : Blo 2221435 3332993 := bstep (se 2 (by rfl) ⟨1249872, by rfl⟩ : syracuseStep 3332993 = 2499745) B2499745
theorem B2221995 : Blo 2221435 2221995 := bstep (se 1 (by rfl) ⟨1666496, by rfl⟩ : syracuseStep 2221995 = 3332993) B3332993
theorem B5624437 : Blo 2221435 5624437 := bbase (se 5 (by rfl) ⟨263645, by rfl⟩ : syracuseStep 5624437 = 527291) (by norm_num)
theorem B7499249 : Blo 2221435 7499249 := bstep (se 2 (by rfl) ⟨2812218, by rfl⟩ : syracuseStep 7499249 = 5624437) B5624437
theorem B4999499 : Blo 2221435 4999499 := bstep (se 1 (by rfl) ⟨3749624, by rfl⟩ : syracuseStep 4999499 = 7499249) B7499249
theorem B3332999 : Blo 2221435 3332999 := bstep (se 1 (by rfl) ⟨2499749, by rfl⟩ : syracuseStep 3332999 = 4999499) B4999499
theorem B2221999 : Blo 2221435 2221999 := bstep (se 1 (by rfl) ⟨1666499, by rfl⟩ : syracuseStep 2221999 = 3332999) B3332999
theorem B3333005 : Blo 2221435 3333005 := bbase (se 3 (by rfl) ⟨624938, by rfl⟩ : syracuseStep 3333005 = 1249877) (by norm_num)
theorem B2222003 : Blo 2221435 2222003 := bstep (se 1 (by rfl) ⟨1666502, by rfl⟩ : syracuseStep 2222003 = 3333005) B3333005
theorem B4999517 : Blo 2221435 4999517 := bbase (se 3 (by rfl) ⟨937409, by rfl⟩ : syracuseStep 4999517 = 1874819) (by norm_num)
theorem B3333011 : Blo 2221435 3333011 := bstep (se 1 (by rfl) ⟨2499758, by rfl⟩ : syracuseStep 3333011 = 4999517) B4999517
theorem B2222007 : Blo 2221435 2222007 := bstep (se 1 (by rfl) ⟨1666505, by rfl⟩ : syracuseStep 2222007 = 3333011) B3333011
theorem B3749645 : Blo 2221435 3749645 := bbase (se 3 (by rfl) ⟨703058, by rfl⟩ : syracuseStep 3749645 = 1406117) (by norm_num)
theorem B2499763 : Blo 2221435 2499763 := bstep (se 1 (by rfl) ⟨1874822, by rfl⟩ : syracuseStep 2499763 = 3749645) B3749645
theorem B3333017 : Blo 2221435 3333017 := bstep (se 2 (by rfl) ⟨1249881, by rfl⟩ : syracuseStep 3333017 = 2499763) B2499763
theorem B2222011 : Blo 2221435 2222011 := bstep (se 1 (by rfl) ⟨1666508, by rfl⟩ : syracuseStep 2222011 = 3333017) B3333017
theorem B18982613 : Blo 2221435 18982613 := bbase (se 7 (by rfl) ⟨222452, by rfl⟩ : syracuseStep 18982613 = 444905) (by norm_num)
theorem B12655075 : Blo 2221435 12655075 := bstep (se 1 (by rfl) ⟨9491306, by rfl⟩ : syracuseStep 12655075 = 18982613) B18982613
theorem B16873433 : Blo 2221435 16873433 := bstep (se 2 (by rfl) ⟨6327537, by rfl⟩ : syracuseStep 16873433 = 12655075) B12655075
theorem B11248955 : Blo 2221435 11248955 := bstep (se 1 (by rfl) ⟨8436716, by rfl⟩ : syracuseStep 11248955 = 16873433) B16873433
theorem B7499303 : Blo 2221435 7499303 := bstep (se 1 (by rfl) ⟨5624477, by rfl⟩ : syracuseStep 7499303 = 11248955) B11248955
theorem B4999535 : Blo 2221435 4999535 := bstep (se 1 (by rfl) ⟨3749651, by rfl⟩ : syracuseStep 4999535 = 7499303) B7499303
theorem B3333023 : Blo 2221435 3333023 := bstep (se 1 (by rfl) ⟨2499767, by rfl⟩ : syracuseStep 3333023 = 4999535) B4999535
theorem B2222015 : Blo 2221435 2222015 := bstep (se 1 (by rfl) ⟨1666511, by rfl⟩ : syracuseStep 2222015 = 3333023) B3333023
theorem B3333029 : Blo 2221435 3333029 := bbase (se 4 (by rfl) ⟨312471, by rfl⟩ : syracuseStep 3333029 = 624943) (by norm_num)
theorem B2222019 : Blo 2221435 2222019 := bstep (se 1 (by rfl) ⟨1666514, by rfl⟩ : syracuseStep 2222019 = 3333029) B3333029
theorem B2812249 : Blo 2221435 2812249 := bbase (se 2 (by rfl) ⟨1054593, by rfl⟩ : syracuseStep 2812249 = 2109187) (by norm_num)
theorem B3749665 : Blo 2221435 3749665 := bstep (se 2 (by rfl) ⟨1406124, by rfl⟩ : syracuseStep 3749665 = 2812249) B2812249
theorem B4999553 : Blo 2221435 4999553 := bstep (se 2 (by rfl) ⟨1874832, by rfl⟩ : syracuseStep 4999553 = 3749665) B3749665
theorem B3333035 : Blo 2221435 3333035 := bstep (se 1 (by rfl) ⟨2499776, by rfl⟩ : syracuseStep 3333035 = 4999553) B4999553
theorem B2222023 : Blo 2221435 2222023 := bstep (se 1 (by rfl) ⟨1666517, by rfl⟩ : syracuseStep 2222023 = 3333035) B3333035
theorem B2499781 : Blo 2221435 2499781 := bbase (se 4 (by rfl) ⟨234354, by rfl⟩ : syracuseStep 2499781 = 468709) (by norm_num)
theorem B3333041 : Blo 2221435 3333041 := bstep (se 2 (by rfl) ⟨1249890, by rfl⟩ : syracuseStep 3333041 = 2499781) B2499781
theorem B2222027 : Blo 2221435 2222027 := bstep (se 1 (by rfl) ⟨1666520, by rfl⟩ : syracuseStep 2222027 = 3333041) B3333041
theorem B4218389 : Blo 2221435 4218389 := bbase (se 6 (by rfl) ⟨98868, by rfl⟩ : syracuseStep 4218389 = 197737) (by norm_num)
theorem B2812259 : Blo 2221435 2812259 := bstep (se 1 (by rfl) ⟨2109194, by rfl⟩ : syracuseStep 2812259 = 4218389) B4218389
theorem B7499357 : Blo 2221435 7499357 := bstep (se 3 (by rfl) ⟨1406129, by rfl⟩ : syracuseStep 7499357 = 2812259) B2812259
theorem B4999571 : Blo 2221435 4999571 := bstep (se 1 (by rfl) ⟨3749678, by rfl⟩ : syracuseStep 4999571 = 7499357) B7499357
theorem B3333047 : Blo 2221435 3333047 := bstep (se 1 (by rfl) ⟨2499785, by rfl⟩ : syracuseStep 3333047 = 4999571) B4999571
theorem B2222031 : Blo 2221435 2222031 := bstep (se 1 (by rfl) ⟨1666523, by rfl⟩ : syracuseStep 2222031 = 3333047) B3333047
theorem B3333053 : Blo 2221435 3333053 := bbase (se 3 (by rfl) ⟨624947, by rfl⟩ : syracuseStep 3333053 = 1249895) (by norm_num)
theorem B2222035 : Blo 2221435 2222035 := bstep (se 1 (by rfl) ⟨1666526, by rfl⟩ : syracuseStep 2222035 = 3333053) B3333053
theorem B4999589 : Blo 2221435 4999589 := bbase (se 4 (by rfl) ⟨468711, by rfl⟩ : syracuseStep 4999589 = 937423) (by norm_num)
theorem B3333059 : Blo 2221435 3333059 := bstep (se 1 (by rfl) ⟨2499794, by rfl⟩ : syracuseStep 3333059 = 4999589) B4999589
theorem B2222039 : Blo 2221435 2222039 := bstep (se 1 (by rfl) ⟨1666529, by rfl⟩ : syracuseStep 2222039 = 3333059) B3333059
theorem B5624549 : Blo 2221435 5624549 := bbase (se 4 (by rfl) ⟨527301, by rfl⟩ : syracuseStep 5624549 = 1054603) (by norm_num)
theorem B3749699 : Blo 2221435 3749699 := bstep (se 1 (by rfl) ⟨2812274, by rfl⟩ : syracuseStep 3749699 = 5624549) B5624549
theorem B2499799 : Blo 2221435 2499799 := bstep (se 1 (by rfl) ⟨1874849, by rfl⟩ : syracuseStep 2499799 = 3749699) B3749699
theorem B3333065 : Blo 2221435 3333065 := bstep (se 2 (by rfl) ⟨1249899, by rfl⟩ : syracuseStep 3333065 = 2499799) B2499799
theorem B2222043 : Blo 2221435 2222043 := bstep (se 1 (by rfl) ⟨1666532, by rfl⟩ : syracuseStep 2222043 = 3333065) B3333065
theorem B2372861 : Blo 2221435 2372861 := bbase (se 3 (by rfl) ⟨444911, by rfl⟩ : syracuseStep 2372861 = 889823) (by norm_num)
theorem B6327629 : Blo 2221435 6327629 := bstep (se 3 (by rfl) ⟨1186430, by rfl⟩ : syracuseStep 6327629 = 2372861) B2372861
theorem B4218419 : Blo 2221435 4218419 := bstep (se 1 (by rfl) ⟨3163814, by rfl⟩ : syracuseStep 4218419 = 6327629) B6327629
theorem B11249117 : Blo 2221435 11249117 := bstep (se 3 (by rfl) ⟨2109209, by rfl⟩ : syracuseStep 11249117 = 4218419) B4218419
theorem B7499411 : Blo 2221435 7499411 := bstep (se 1 (by rfl) ⟨5624558, by rfl⟩ : syracuseStep 7499411 = 11249117) B11249117
theorem B4999607 : Blo 2221435 4999607 := bstep (se 1 (by rfl) ⟨3749705, by rfl⟩ : syracuseStep 4999607 = 7499411) B7499411
theorem B3333071 : Blo 2221435 3333071 := bstep (se 1 (by rfl) ⟨2499803, by rfl⟩ : syracuseStep 3333071 = 4999607) B4999607
theorem B2222047 : Blo 2221435 2222047 := bstep (se 1 (by rfl) ⟨1666535, by rfl⟩ : syracuseStep 2222047 = 3333071) B3333071
theorem B3333077 : Blo 2221435 3333077 := bbase (se 7 (by rfl) ⟨39059, by rfl⟩ : syracuseStep 3333077 = 78119) (by norm_num)
theorem B2222051 : Blo 2221435 2222051 := bstep (se 1 (by rfl) ⟨1666538, by rfl⟩ : syracuseStep 2222051 = 3333077) B3333077
theorem B8436869 : Blo 2221435 8436869 := bbase (se 4 (by rfl) ⟨790956, by rfl⟩ : syracuseStep 8436869 = 1581913) (by norm_num)
theorem B5624579 : Blo 2221435 5624579 := bstep (se 1 (by rfl) ⟨4218434, by rfl⟩ : syracuseStep 5624579 = 8436869) B8436869
theorem B3749719 : Blo 2221435 3749719 := bstep (se 1 (by rfl) ⟨2812289, by rfl⟩ : syracuseStep 3749719 = 5624579) B5624579
theorem B4999625 : Blo 2221435 4999625 := bstep (se 2 (by rfl) ⟨1874859, by rfl⟩ : syracuseStep 4999625 = 3749719) B3749719
theorem B3333083 : Blo 2221435 3333083 := bstep (se 1 (by rfl) ⟨2499812, by rfl⟩ : syracuseStep 3333083 = 4999625) B4999625
theorem B2222055 : Blo 2221435 2222055 := bstep (se 1 (by rfl) ⟨1666541, by rfl⟩ : syracuseStep 2222055 = 3333083) B3333083
theorem B2499817 : Blo 2221435 2499817 := bbase (se 2 (by rfl) ⟨937431, by rfl⟩ : syracuseStep 2499817 = 1874863) (by norm_num)
theorem B3333089 : Blo 2221435 3333089 := bstep (se 2 (by rfl) ⟨1249908, by rfl⟩ : syracuseStep 3333089 = 2499817) B2499817
theorem B2222059 : Blo 2221435 2222059 := bstep (se 1 (by rfl) ⟨1666544, by rfl⟩ : syracuseStep 2222059 = 3333089) B3333089
theorem B12655349 : Blo 2221435 12655349 := bbase (se 5 (by rfl) ⟨593219, by rfl⟩ : syracuseStep 12655349 = 1186439) (by norm_num)
theorem B8436899 : Blo 2221435 8436899 := bstep (se 1 (by rfl) ⟨6327674, by rfl⟩ : syracuseStep 8436899 = 12655349) B12655349
theorem B5624599 : Blo 2221435 5624599 := bstep (se 1 (by rfl) ⟨4218449, by rfl⟩ : syracuseStep 5624599 = 8436899) B8436899
theorem B7499465 : Blo 2221435 7499465 := bstep (se 2 (by rfl) ⟨2812299, by rfl⟩ : syracuseStep 7499465 = 5624599) B5624599
theorem B4999643 : Blo 2221435 4999643 := bstep (se 1 (by rfl) ⟨3749732, by rfl⟩ : syracuseStep 4999643 = 7499465) B7499465
theorem B3333095 : Blo 2221435 3333095 := bstep (se 1 (by rfl) ⟨2499821, by rfl⟩ : syracuseStep 3333095 = 4999643) B4999643
theorem B2222063 : Blo 2221435 2222063 := bstep (se 1 (by rfl) ⟨1666547, by rfl⟩ : syracuseStep 2222063 = 3333095) B3333095
theorem B3333101 : Blo 2221435 3333101 := bbase (se 3 (by rfl) ⟨624956, by rfl⟩ : syracuseStep 3333101 = 1249913) (by norm_num)
theorem B2222067 : Blo 2221435 2222067 := bstep (se 1 (by rfl) ⟨1666550, by rfl⟩ : syracuseStep 2222067 = 3333101) B3333101
theorem B4999661 : Blo 2221435 4999661 := bbase (se 3 (by rfl) ⟨937436, by rfl⟩ : syracuseStep 4999661 = 1874873) (by norm_num)
theorem B3333107 : Blo 2221435 3333107 := bstep (se 1 (by rfl) ⟨2499830, by rfl⟩ : syracuseStep 3333107 = 4999661) B4999661
theorem B2222071 : Blo 2221435 2222071 := bstep (se 1 (by rfl) ⟨1666553, by rfl⟩ : syracuseStep 2222071 = 3333107) B3333107
theorem B17104117 : Blo 2221435 17104117 := bbase (se 5 (by rfl) ⟨801755, by rfl⟩ : syracuseStep 17104117 = 1603511) (by norm_num)
theorem B22805489 : Blo 2221435 22805489 := bstep (se 2 (by rfl) ⟨8552058, by rfl⟩ : syracuseStep 22805489 = 17104117) B17104117
theorem B15203659 : Blo 2221435 15203659 := bstep (se 1 (by rfl) ⟨11402744, by rfl⟩ : syracuseStep 15203659 = 22805489) B22805489
theorem B20271545 : Blo 2221435 20271545 := bstep (se 2 (by rfl) ⟨7601829, by rfl⟩ : syracuseStep 20271545 = 15203659) B15203659
theorem B13514363 : Blo 2221435 13514363 := bstep (se 1 (by rfl) ⟨10135772, by rfl⟩ : syracuseStep 13514363 = 20271545) B20271545
theorem B9009575 : Blo 2221435 9009575 := bstep (se 1 (by rfl) ⟨6757181, by rfl⟩ : syracuseStep 9009575 = 13514363) B13514363
theorem B6006383 : Blo 2221435 6006383 := bstep (se 1 (by rfl) ⟨4504787, by rfl⟩ : syracuseStep 6006383 = 9009575) B9009575
theorem B4004255 : Blo 2221435 4004255 := bstep (se 1 (by rfl) ⟨3003191, by rfl⟩ : syracuseStep 4004255 = 6006383) B6006383
theorem B10678013 : Blo 2221435 10678013 := bstep (se 3 (by rfl) ⟨2002127, by rfl⟩ : syracuseStep 10678013 = 4004255) B4004255
theorem B7118675 : Blo 2221435 7118675 := bstep (se 1 (by rfl) ⟨5339006, by rfl⟩ : syracuseStep 7118675 = 10678013) B10678013
theorem B4745783 : Blo 2221435 4745783 := bstep (se 1 (by rfl) ⟨3559337, by rfl⟩ : syracuseStep 4745783 = 7118675) B7118675
theorem B3163855 : Blo 2221435 3163855 := bstep (se 1 (by rfl) ⟨2372891, by rfl⟩ : syracuseStep 3163855 = 4745783) B4745783
theorem B4218473 : Blo 2221435 4218473 := bstep (se 2 (by rfl) ⟨1581927, by rfl⟩ : syracuseStep 4218473 = 3163855) B3163855
theorem B2812315 : Blo 2221435 2812315 := bstep (se 1 (by rfl) ⟨2109236, by rfl⟩ : syracuseStep 2812315 = 4218473) B4218473
theorem B3749753 : Blo 2221435 3749753 := bstep (se 2 (by rfl) ⟨1406157, by rfl⟩ : syracuseStep 3749753 = 2812315) B2812315
theorem B2499835 : Blo 2221435 2499835 := bstep (se 1 (by rfl) ⟨1874876, by rfl⟩ : syracuseStep 2499835 = 3749753) B3749753
theorem B3333113 : Blo 2221435 3333113 := bstep (se 2 (by rfl) ⟨1249917, by rfl⟩ : syracuseStep 3333113 = 2499835) B2499835
theorem B2222075 : Blo 2221435 2222075 := bstep (se 1 (by rfl) ⟨1666556, by rfl⟩ : syracuseStep 2222075 = 3333113) B3333113
theorem B2226725 : Blo 2221435 2226725 := bbase (se 4 (by rfl) ⟨208755, by rfl⟩ : syracuseStep 2226725 = 417511) (by norm_num)
theorem B95006933 : Blo 2221435 95006933 := bstep (se 7 (by rfl) ⟨1113362, by rfl⟩ : syracuseStep 95006933 = 2226725) B2226725
theorem B63337955 : Blo 2221435 63337955 := bstep (se 1 (by rfl) ⟨47503466, by rfl⟩ : syracuseStep 63337955 = 95006933) B95006933
theorem B168901213 : Blo 2221435 168901213 := bstep (se 3 (by rfl) ⟨31668977, by rfl⟩ : syracuseStep 168901213 = 63337955) B63337955
theorem B225201617 : Blo 2221435 225201617 := bstep (se 2 (by rfl) ⟨84450606, by rfl⟩ : syracuseStep 225201617 = 168901213) B168901213
theorem B150134411 : Blo 2221435 150134411 := bstep (se 1 (by rfl) ⟨112600808, by rfl⟩ : syracuseStep 150134411 = 225201617) B225201617
theorem B100089607 : Blo 2221435 100089607 := bstep (se 1 (by rfl) ⟨75067205, by rfl⟩ : syracuseStep 100089607 = 150134411) B150134411
theorem B133452809 : Blo 2221435 133452809 := bstep (se 2 (by rfl) ⟨50044803, by rfl⟩ : syracuseStep 133452809 = 100089607) B100089607
theorem B88968539 : Blo 2221435 88968539 := bstep (se 1 (by rfl) ⟨66726404, by rfl⟩ : syracuseStep 88968539 = 133452809) B133452809
theorem B59312359 : Blo 2221435 59312359 := bstep (se 1 (by rfl) ⟨44484269, by rfl⟩ : syracuseStep 59312359 = 88968539) B88968539
theorem B79083145 : Blo 2221435 79083145 := bstep (se 2 (by rfl) ⟨29656179, by rfl⟩ : syracuseStep 79083145 = 59312359) B59312359
theorem B105444193 : Blo 2221435 105444193 := bstep (se 2 (by rfl) ⟨39541572, by rfl⟩ : syracuseStep 105444193 = 79083145) B79083145
theorem B140592257 : Blo 2221435 140592257 := bstep (se 2 (by rfl) ⟨52722096, by rfl⟩ : syracuseStep 140592257 = 105444193) B105444193
theorem B93728171 : Blo 2221435 93728171 := bstep (se 1 (by rfl) ⟨70296128, by rfl⟩ : syracuseStep 93728171 = 140592257) B140592257
theorem B249941789 : Blo 2221435 249941789 := bstep (se 3 (by rfl) ⟨46864085, by rfl⟩ : syracuseStep 249941789 = 93728171) B93728171
theorem B166627859 : Blo 2221435 166627859 := bstep (se 1 (by rfl) ⟨124970894, by rfl⟩ : syracuseStep 166627859 = 249941789) B249941789
theorem B1777363829 : Blo 2221435 1777363829 := bstep (se 5 (by rfl) ⟨83313929, by rfl⟩ : syracuseStep 1777363829 = 166627859) B166627859
theorem B1184909219 : Blo 2221435 1184909219 := bstep (se 1 (by rfl) ⟨888681914, by rfl⟩ : syracuseStep 1184909219 = 1777363829) B1777363829
theorem B789939479 : Blo 2221435 789939479 := bstep (se 1 (by rfl) ⟨592454609, by rfl⟩ : syracuseStep 789939479 = 1184909219) B1184909219
theorem B526626319 : Blo 2221435 526626319 := bstep (se 1 (by rfl) ⟨394969739, by rfl⟩ : syracuseStep 526626319 = 789939479) B789939479
theorem B702168425 : Blo 2221435 702168425 := bstep (se 2 (by rfl) ⟨263313159, by rfl⟩ : syracuseStep 702168425 = 526626319) B526626319
theorem B468112283 : Blo 2221435 468112283 := bstep (se 1 (by rfl) ⟨351084212, by rfl⟩ : syracuseStep 468112283 = 702168425) B702168425
theorem B312074855 : Blo 2221435 312074855 := bstep (se 1 (by rfl) ⟨234056141, by rfl⟩ : syracuseStep 312074855 = 468112283) B468112283
theorem B208049903 : Blo 2221435 208049903 := bstep (se 1 (by rfl) ⟨156037427, by rfl⟩ : syracuseStep 208049903 = 312074855) B312074855
theorem B138699935 : Blo 2221435 138699935 := bstep (se 1 (by rfl) ⟨104024951, by rfl⟩ : syracuseStep 138699935 = 208049903) B208049903
theorem B92466623 : Blo 2221435 92466623 := bstep (se 1 (by rfl) ⟨69349967, by rfl⟩ : syracuseStep 92466623 = 138699935) B138699935
theorem B246577661 : Blo 2221435 246577661 := bstep (se 3 (by rfl) ⟨46233311, by rfl⟩ : syracuseStep 246577661 = 92466623) B92466623
theorem B164385107 : Blo 2221435 164385107 := bstep (se 1 (by rfl) ⟨123288830, by rfl⟩ : syracuseStep 164385107 = 246577661) B246577661
theorem B7013764565 : Blo 2221435 7013764565 := bstep (se 7 (by rfl) ⟨82192553, by rfl⟩ : syracuseStep 7013764565 = 164385107) B164385107
theorem B4675843043 : Blo 2221435 4675843043 := bstep (se 1 (by rfl) ⟨3506882282, by rfl⟩ : syracuseStep 4675843043 = 7013764565) B7013764565
theorem B3117228695 : Blo 2221435 3117228695 := bstep (se 1 (by rfl) ⟨2337921521, by rfl⟩ : syracuseStep 3117228695 = 4675843043) B4675843043
theorem B2078152463 : Blo 2221435 2078152463 := bstep (se 1 (by rfl) ⟨1558614347, by rfl⟩ : syracuseStep 2078152463 = 3117228695) B3117228695
theorem B1385434975 : Blo 2221435 1385434975 := bstep (se 1 (by rfl) ⟨1039076231, by rfl⟩ : syracuseStep 1385434975 = 2078152463) B2078152463
theorem B1847246633 : Blo 2221435 1847246633 := bstep (se 2 (by rfl) ⟨692717487, by rfl⟩ : syracuseStep 1847246633 = 1385434975) B1385434975
theorem B1231497755 : Blo 2221435 1231497755 := bstep (se 1 (by rfl) ⟨923623316, by rfl⟩ : syracuseStep 1231497755 = 1847246633) B1847246633
theorem B820998503 : Blo 2221435 820998503 := bstep (se 1 (by rfl) ⟨615748877, by rfl⟩ : syracuseStep 820998503 = 1231497755) B1231497755
theorem B547332335 : Blo 2221435 547332335 := bstep (se 1 (by rfl) ⟨410499251, by rfl⟩ : syracuseStep 547332335 = 820998503) B820998503
theorem B364888223 : Blo 2221435 364888223 := bstep (se 1 (by rfl) ⟨273666167, by rfl⟩ : syracuseStep 364888223 = 547332335) B547332335
theorem B243258815 : Blo 2221435 243258815 := bstep (se 1 (by rfl) ⟨182444111, by rfl⟩ : syracuseStep 243258815 = 364888223) B364888223
theorem B162172543 : Blo 2221435 162172543 := bstep (se 1 (by rfl) ⟨121629407, by rfl⟩ : syracuseStep 162172543 = 243258815) B243258815
theorem B216230057 : Blo 2221435 216230057 := bstep (se 2 (by rfl) ⟨81086271, by rfl⟩ : syracuseStep 216230057 = 162172543) B162172543
theorem B144153371 : Blo 2221435 144153371 := bstep (se 1 (by rfl) ⟨108115028, by rfl⟩ : syracuseStep 144153371 = 216230057) B216230057
theorem B96102247 : Blo 2221435 96102247 := bstep (se 1 (by rfl) ⟨72076685, by rfl⟩ : syracuseStep 96102247 = 144153371) B144153371
theorem B128136329 : Blo 2221435 128136329 := bstep (se 2 (by rfl) ⟨48051123, by rfl⟩ : syracuseStep 128136329 = 96102247) B96102247
theorem B85424219 : Blo 2221435 85424219 := bstep (se 1 (by rfl) ⟨64068164, by rfl⟩ : syracuseStep 85424219 = 128136329) B128136329
theorem B56949479 : Blo 2221435 56949479 := bstep (se 1 (by rfl) ⟨42712109, by rfl⟩ : syracuseStep 56949479 = 85424219) B85424219
theorem B37966319 : Blo 2221435 37966319 := bstep (se 1 (by rfl) ⟨28474739, by rfl⟩ : syracuseStep 37966319 = 56949479) B56949479
theorem B25310879 : Blo 2221435 25310879 := bstep (se 1 (by rfl) ⟨18983159, by rfl⟩ : syracuseStep 25310879 = 37966319) B37966319
theorem B16873919 : Blo 2221435 16873919 := bstep (se 1 (by rfl) ⟨12655439, by rfl⟩ : syracuseStep 16873919 = 25310879) B25310879
theorem B11249279 : Blo 2221435 11249279 := bstep (se 1 (by rfl) ⟨8436959, by rfl⟩ : syracuseStep 11249279 = 16873919) B16873919
theorem B7499519 : Blo 2221435 7499519 := bstep (se 1 (by rfl) ⟨5624639, by rfl⟩ : syracuseStep 7499519 = 11249279) B11249279
theorem B4999679 : Blo 2221435 4999679 := bstep (se 1 (by rfl) ⟨3749759, by rfl⟩ : syracuseStep 4999679 = 7499519) B7499519
theorem B3333119 : Blo 2221435 3333119 := bstep (se 1 (by rfl) ⟨2499839, by rfl⟩ : syracuseStep 3333119 = 4999679) B4999679
theorem B2222079 : Blo 2221435 2222079 := bstep (se 1 (by rfl) ⟨1666559, by rfl⟩ : syracuseStep 2222079 = 3333119) B3333119
theorem B3333125 : Blo 2221435 3333125 := bbase (se 4 (by rfl) ⟨312480, by rfl⟩ : syracuseStep 3333125 = 624961) (by norm_num)
theorem B2222083 : Blo 2221435 2222083 := bstep (se 1 (by rfl) ⟨1666562, by rfl⟩ : syracuseStep 2222083 = 3333125) B3333125
theorem B3749773 : Blo 2221435 3749773 := bbase (se 3 (by rfl) ⟨703082, by rfl⟩ : syracuseStep 3749773 = 1406165) (by norm_num)
theorem B4999697 : Blo 2221435 4999697 := bstep (se 2 (by rfl) ⟨1874886, by rfl⟩ : syracuseStep 4999697 = 3749773) B3749773
theorem B3333131 : Blo 2221435 3333131 := bstep (se 1 (by rfl) ⟨2499848, by rfl⟩ : syracuseStep 3333131 = 4999697) B4999697
theorem B2222087 : Blo 2221435 2222087 := bstep (se 1 (by rfl) ⟨1666565, by rfl⟩ : syracuseStep 2222087 = 3333131) B3333131
theorem B2499853 : Blo 2221435 2499853 := bbase (se 3 (by rfl) ⟨468722, by rfl⟩ : syracuseStep 2499853 = 937445) (by norm_num)
theorem B3333137 : Blo 2221435 3333137 := bstep (se 2 (by rfl) ⟨1249926, by rfl⟩ : syracuseStep 3333137 = 2499853) B2499853
theorem B2222091 : Blo 2221435 2222091 := bstep (se 1 (by rfl) ⟨1666568, by rfl⟩ : syracuseStep 2222091 = 3333137) B3333137
theorem B7499573 : Blo 2221435 7499573 := bbase (se 5 (by rfl) ⟨351542, by rfl⟩ : syracuseStep 7499573 = 703085) (by norm_num)
theorem B4999715 : Blo 2221435 4999715 := bstep (se 1 (by rfl) ⟨3749786, by rfl⟩ : syracuseStep 4999715 = 7499573) B7499573
theorem B3333143 : Blo 2221435 3333143 := bstep (se 1 (by rfl) ⟨2499857, by rfl⟩ : syracuseStep 3333143 = 4999715) B4999715
theorem B2222095 : Blo 2221435 2222095 := bstep (se 1 (by rfl) ⟨1666571, by rfl⟩ : syracuseStep 2222095 = 3333143) B3333143
theorem B3333149 : Blo 2221435 3333149 := bbase (se 3 (by rfl) ⟨624965, by rfl⟩ : syracuseStep 3333149 = 1249931) (by norm_num)
theorem B2222099 : Blo 2221435 2222099 := bstep (se 1 (by rfl) ⟨1666574, by rfl⟩ : syracuseStep 2222099 = 3333149) B3333149
theorem B4999733 : Blo 2221435 4999733 := bbase (se 5 (by rfl) ⟨234362, by rfl⟩ : syracuseStep 4999733 = 468725) (by norm_num)
theorem B3333155 : Blo 2221435 3333155 := bstep (se 1 (by rfl) ⟨2499866, by rfl⟩ : syracuseStep 3333155 = 4999733) B4999733
theorem B2222103 : Blo 2221435 2222103 := bstep (se 1 (by rfl) ⟨1666577, by rfl⟩ : syracuseStep 2222103 = 3333155) B3333155
theorem B9491701 : Blo 2221435 9491701 := bbase (se 5 (by rfl) ⟨444923, by rfl⟩ : syracuseStep 9491701 = 889847) (by norm_num)
theorem B12655601 : Blo 2221435 12655601 := bstep (se 2 (by rfl) ⟨4745850, by rfl⟩ : syracuseStep 12655601 = 9491701) B9491701
theorem B8437067 : Blo 2221435 8437067 := bstep (se 1 (by rfl) ⟨6327800, by rfl⟩ : syracuseStep 8437067 = 12655601) B12655601
theorem B5624711 : Blo 2221435 5624711 := bstep (se 1 (by rfl) ⟨4218533, by rfl⟩ : syracuseStep 5624711 = 8437067) B8437067
theorem B3749807 : Blo 2221435 3749807 := bstep (se 1 (by rfl) ⟨2812355, by rfl⟩ : syracuseStep 3749807 = 5624711) B5624711
theorem B2499871 : Blo 2221435 2499871 := bstep (se 1 (by rfl) ⟨1874903, by rfl⟩ : syracuseStep 2499871 = 3749807) B3749807
theorem B3333161 : Blo 2221435 3333161 := bstep (se 2 (by rfl) ⟨1249935, by rfl⟩ : syracuseStep 3333161 = 2499871) B2499871
theorem B2222107 : Blo 2221435 2222107 := bstep (se 1 (by rfl) ⟨1666580, by rfl⟩ : syracuseStep 2222107 = 3333161) B3333161
theorem B9491717 : Blo 2221435 9491717 := bbase (se 4 (by rfl) ⟨889848, by rfl⟩ : syracuseStep 9491717 = 1779697) (by norm_num)
theorem B6327811 : Blo 2221435 6327811 := bstep (se 1 (by rfl) ⟨4745858, by rfl⟩ : syracuseStep 6327811 = 9491717) B9491717
theorem B8437081 : Blo 2221435 8437081 := bstep (se 2 (by rfl) ⟨3163905, by rfl⟩ : syracuseStep 8437081 = 6327811) B6327811
theorem B11249441 : Blo 2221435 11249441 := bstep (se 2 (by rfl) ⟨4218540, by rfl⟩ : syracuseStep 11249441 = 8437081) B8437081
theorem B7499627 : Blo 2221435 7499627 := bstep (se 1 (by rfl) ⟨5624720, by rfl⟩ : syracuseStep 7499627 = 11249441) B11249441
theorem B4999751 : Blo 2221435 4999751 := bstep (se 1 (by rfl) ⟨3749813, by rfl⟩ : syracuseStep 4999751 = 7499627) B7499627
theorem B3333167 : Blo 2221435 3333167 := bstep (se 1 (by rfl) ⟨2499875, by rfl⟩ : syracuseStep 3333167 = 4999751) B4999751
theorem B2222111 : Blo 2221435 2222111 := bstep (se 1 (by rfl) ⟨1666583, by rfl⟩ : syracuseStep 2222111 = 3333167) B3333167
theorem B3333173 : Blo 2221435 3333173 := bbase (se 5 (by rfl) ⟨156242, by rfl⟩ : syracuseStep 3333173 = 312485) (by norm_num)
theorem B2222115 : Blo 2221435 2222115 := bstep (se 1 (by rfl) ⟨1666586, by rfl⟩ : syracuseStep 2222115 = 3333173) B3333173
theorem B5624741 : Blo 2221435 5624741 := bbase (se 4 (by rfl) ⟨527319, by rfl⟩ : syracuseStep 5624741 = 1054639) (by norm_num)
theorem B3749827 : Blo 2221435 3749827 := bstep (se 1 (by rfl) ⟨2812370, by rfl⟩ : syracuseStep 3749827 = 5624741) B5624741
theorem B4999769 : Blo 2221435 4999769 := bstep (se 2 (by rfl) ⟨1874913, by rfl⟩ : syracuseStep 4999769 = 3749827) B3749827
theorem B3333179 : Blo 2221435 3333179 := bstep (se 1 (by rfl) ⟨2499884, by rfl⟩ : syracuseStep 3333179 = 4999769) B4999769
theorem B2222119 : Blo 2221435 2222119 := bstep (se 1 (by rfl) ⟨1666589, by rfl⟩ : syracuseStep 2222119 = 3333179) B3333179
theorem B2499889 : Blo 2221435 2499889 := bbase (se 2 (by rfl) ⟨937458, by rfl⟩ : syracuseStep 2499889 = 1874917) (by norm_num)
theorem B3333185 : Blo 2221435 3333185 := bstep (se 2 (by rfl) ⟨1249944, by rfl⟩ : syracuseStep 3333185 = 2499889) B2499889
theorem B2222123 : Blo 2221435 2222123 := bstep (se 1 (by rfl) ⟨1666592, by rfl⟩ : syracuseStep 2222123 = 3333185) B3333185
theorem B4745893 : Blo 2221435 4745893 := bbase (se 4 (by rfl) ⟨444927, by rfl⟩ : syracuseStep 4745893 = 889855) (by norm_num)
theorem B6327857 : Blo 2221435 6327857 := bstep (se 2 (by rfl) ⟨2372946, by rfl⟩ : syracuseStep 6327857 = 4745893) B4745893
theorem B4218571 : Blo 2221435 4218571 := bstep (se 1 (by rfl) ⟨3163928, by rfl⟩ : syracuseStep 4218571 = 6327857) B6327857
theorem B5624761 : Blo 2221435 5624761 := bstep (se 2 (by rfl) ⟨2109285, by rfl⟩ : syracuseStep 5624761 = 4218571) B4218571
theorem B7499681 : Blo 2221435 7499681 := bstep (se 2 (by rfl) ⟨2812380, by rfl⟩ : syracuseStep 7499681 = 5624761) B5624761
theorem B4999787 : Blo 2221435 4999787 := bstep (se 1 (by rfl) ⟨3749840, by rfl⟩ : syracuseStep 4999787 = 7499681) B7499681
theorem B3333191 : Blo 2221435 3333191 := bstep (se 1 (by rfl) ⟨2499893, by rfl⟩ : syracuseStep 3333191 = 4999787) B4999787
theorem B2222127 : Blo 2221435 2222127 := bstep (se 1 (by rfl) ⟨1666595, by rfl⟩ : syracuseStep 2222127 = 3333191) B3333191
theorem B3333197 : Blo 2221435 3333197 := bbase (se 3 (by rfl) ⟨624974, by rfl⟩ : syracuseStep 3333197 = 1249949) (by norm_num)
theorem B2222131 : Blo 2221435 2222131 := bstep (se 1 (by rfl) ⟨1666598, by rfl⟩ : syracuseStep 2222131 = 3333197) B3333197
theorem B4999805 : Blo 2221435 4999805 := bbase (se 3 (by rfl) ⟨937463, by rfl⟩ : syracuseStep 4999805 = 1874927) (by norm_num)
theorem B3333203 : Blo 2221435 3333203 := bstep (se 1 (by rfl) ⟨2499902, by rfl⟩ : syracuseStep 3333203 = 4999805) B4999805
theorem B2222135 : Blo 2221435 2222135 := bstep (se 1 (by rfl) ⟨1666601, by rfl⟩ : syracuseStep 2222135 = 3333203) B3333203
theorem B3749861 : Blo 2221435 3749861 := bbase (se 4 (by rfl) ⟨351549, by rfl⟩ : syracuseStep 3749861 = 703099) (by norm_num)
theorem B2499907 : Blo 2221435 2499907 := bstep (se 1 (by rfl) ⟨1874930, by rfl⟩ : syracuseStep 2499907 = 3749861) B3749861
theorem B3333209 : Blo 2221435 3333209 := bstep (se 2 (by rfl) ⟨1249953, by rfl⟩ : syracuseStep 3333209 = 2499907) B2499907
theorem B2222139 : Blo 2221435 2222139 := bstep (se 1 (by rfl) ⟨1666604, by rfl⟩ : syracuseStep 2222139 = 3333209) B3333209
theorem B6006565 : Blo 2221435 6006565 := bbase (se 4 (by rfl) ⟨563115, by rfl⟩ : syracuseStep 6006565 = 1126231) (by norm_num)
theorem B8008753 : Blo 2221435 8008753 := bstep (se 2 (by rfl) ⟨3003282, by rfl⟩ : syracuseStep 8008753 = 6006565) B6006565
theorem B10678337 : Blo 2221435 10678337 := bstep (se 2 (by rfl) ⟨4004376, by rfl⟩ : syracuseStep 10678337 = 8008753) B8008753
theorem B7118891 : Blo 2221435 7118891 := bstep (se 1 (by rfl) ⟨5339168, by rfl⟩ : syracuseStep 7118891 = 10678337) B10678337
theorem B4745927 : Blo 2221435 4745927 := bstep (se 1 (by rfl) ⟨3559445, by rfl⟩ : syracuseStep 4745927 = 7118891) B7118891
theorem B3163951 : Blo 2221435 3163951 := bstep (se 1 (by rfl) ⟨2372963, by rfl⟩ : syracuseStep 3163951 = 4745927) B4745927
theorem B16874405 : Blo 2221435 16874405 := bstep (se 4 (by rfl) ⟨1581975, by rfl⟩ : syracuseStep 16874405 = 3163951) B3163951
theorem B11249603 : Blo 2221435 11249603 := bstep (se 1 (by rfl) ⟨8437202, by rfl⟩ : syracuseStep 11249603 = 16874405) B16874405
theorem B7499735 : Blo 2221435 7499735 := bstep (se 1 (by rfl) ⟨5624801, by rfl⟩ : syracuseStep 7499735 = 11249603) B11249603
theorem B4999823 : Blo 2221435 4999823 := bstep (se 1 (by rfl) ⟨3749867, by rfl⟩ : syracuseStep 4999823 = 7499735) B7499735
theorem B3333215 : Blo 2221435 3333215 := bstep (se 1 (by rfl) ⟨2499911, by rfl⟩ : syracuseStep 3333215 = 4999823) B4999823
theorem B2222143 : Blo 2221435 2222143 := bstep (se 1 (by rfl) ⟨1666607, by rfl⟩ : syracuseStep 2222143 = 3333215) B3333215
theorem B3333221 : Blo 2221435 3333221 := bbase (se 4 (by rfl) ⟨312489, by rfl⟩ : syracuseStep 3333221 = 624979) (by norm_num)
theorem B2222147 : Blo 2221435 2222147 := bstep (se 1 (by rfl) ⟨1666610, by rfl⟩ : syracuseStep 2222147 = 3333221) B3333221
theorem B5339189 : Blo 2221435 5339189 := bbase (se 5 (by rfl) ⟨250274, by rfl⟩ : syracuseStep 5339189 = 500549) (by norm_num)
theorem B3559459 : Blo 2221435 3559459 := bstep (se 1 (by rfl) ⟨2669594, by rfl⟩ : syracuseStep 3559459 = 5339189) B5339189
theorem B4745945 : Blo 2221435 4745945 := bstep (se 2 (by rfl) ⟨1779729, by rfl⟩ : syracuseStep 4745945 = 3559459) B3559459
theorem B3163963 : Blo 2221435 3163963 := bstep (se 1 (by rfl) ⟨2372972, by rfl⟩ : syracuseStep 3163963 = 4745945) B4745945
theorem B4218617 : Blo 2221435 4218617 := bstep (se 2 (by rfl) ⟨1581981, by rfl⟩ : syracuseStep 4218617 = 3163963) B3163963
theorem B2812411 : Blo 2221435 2812411 := bstep (se 1 (by rfl) ⟨2109308, by rfl⟩ : syracuseStep 2812411 = 4218617) B4218617
theorem B3749881 : Blo 2221435 3749881 := bstep (se 2 (by rfl) ⟨1406205, by rfl⟩ : syracuseStep 3749881 = 2812411) B2812411
theorem B4999841 : Blo 2221435 4999841 := bstep (se 2 (by rfl) ⟨1874940, by rfl⟩ : syracuseStep 4999841 = 3749881) B3749881
theorem B3333227 : Blo 2221435 3333227 := bstep (se 1 (by rfl) ⟨2499920, by rfl⟩ : syracuseStep 3333227 = 4999841) B4999841
theorem B2222151 : Blo 2221435 2222151 := bstep (se 1 (by rfl) ⟨1666613, by rfl⟩ : syracuseStep 2222151 = 3333227) B3333227
theorem B2499925 : Blo 2221435 2499925 := bbase (se 12 (by rfl) ⟨915, by rfl⟩ : syracuseStep 2499925 = 1831) (by norm_num)
theorem B3333233 : Blo 2221435 3333233 := bstep (se 2 (by rfl) ⟨1249962, by rfl⟩ : syracuseStep 3333233 = 2499925) B2499925
theorem B2222155 : Blo 2221435 2222155 := bstep (se 1 (by rfl) ⟨1666616, by rfl⟩ : syracuseStep 2222155 = 3333233) B3333233
theorem B2812421 : Blo 2221435 2812421 := bbase (se 4 (by rfl) ⟨263664, by rfl⟩ : syracuseStep 2812421 = 527329) (by norm_num)
theorem B7499789 : Blo 2221435 7499789 := bstep (se 3 (by rfl) ⟨1406210, by rfl⟩ : syracuseStep 7499789 = 2812421) B2812421
theorem B4999859 : Blo 2221435 4999859 := bstep (se 1 (by rfl) ⟨3749894, by rfl⟩ : syracuseStep 4999859 = 7499789) B7499789
theorem B3333239 : Blo 2221435 3333239 := bstep (se 1 (by rfl) ⟨2499929, by rfl⟩ : syracuseStep 3333239 = 4999859) B4999859
theorem B2222159 : Blo 2221435 2222159 := bstep (se 1 (by rfl) ⟨1666619, by rfl⟩ : syracuseStep 2222159 = 3333239) B3333239
theorem B3333245 : Blo 2221435 3333245 := bbase (se 3 (by rfl) ⟨624983, by rfl⟩ : syracuseStep 3333245 = 1249967) (by norm_num)
theorem B2222163 : Blo 2221435 2222163 := bstep (se 1 (by rfl) ⟨1666622, by rfl⟩ : syracuseStep 2222163 = 3333245) B3333245
theorem B4999877 : Blo 2221435 4999877 := bbase (se 4 (by rfl) ⟨468738, by rfl⟩ : syracuseStep 4999877 = 937477) (by norm_num)
theorem B3333251 : Blo 2221435 3333251 := bstep (se 1 (by rfl) ⟨2499938, by rfl⟩ : syracuseStep 3333251 = 4999877) B4999877
theorem B2222167 : Blo 2221435 2222167 := bstep (se 1 (by rfl) ⟨1666625, by rfl⟩ : syracuseStep 2222167 = 3333251) B3333251
theorem B4504981 : Blo 2221435 4504981 := bbase (se 6 (by rfl) ⟨105585, by rfl⟩ : syracuseStep 4504981 = 211171) (by norm_num)
theorem B6006641 : Blo 2221435 6006641 := bstep (se 2 (by rfl) ⟨2252490, by rfl⟩ : syracuseStep 6006641 = 4504981) B4504981
theorem B16017709 : Blo 2221435 16017709 := bstep (se 3 (by rfl) ⟨3003320, by rfl⟩ : syracuseStep 16017709 = 6006641) B6006641
theorem B21356945 : Blo 2221435 21356945 := bstep (se 2 (by rfl) ⟨8008854, by rfl⟩ : syracuseStep 21356945 = 16017709) B16017709
theorem B14237963 : Blo 2221435 14237963 := bstep (se 1 (by rfl) ⟨10678472, by rfl⟩ : syracuseStep 14237963 = 21356945) B21356945
theorem B9491975 : Blo 2221435 9491975 := bstep (se 1 (by rfl) ⟨7118981, by rfl⟩ : syracuseStep 9491975 = 14237963) B14237963
theorem B6327983 : Blo 2221435 6327983 := bstep (se 1 (by rfl) ⟨4745987, by rfl⟩ : syracuseStep 6327983 = 9491975) B9491975
theorem B4218655 : Blo 2221435 4218655 := bstep (se 1 (by rfl) ⟨3163991, by rfl⟩ : syracuseStep 4218655 = 6327983) B6327983
theorem B5624873 : Blo 2221435 5624873 := bstep (se 2 (by rfl) ⟨2109327, by rfl⟩ : syracuseStep 5624873 = 4218655) B4218655
theorem B3749915 : Blo 2221435 3749915 := bstep (se 1 (by rfl) ⟨2812436, by rfl⟩ : syracuseStep 3749915 = 5624873) B5624873
theorem B2499943 : Blo 2221435 2499943 := bstep (se 1 (by rfl) ⟨1874957, by rfl⟩ : syracuseStep 2499943 = 3749915) B3749915
theorem B3333257 : Blo 2221435 3333257 := bstep (se 2 (by rfl) ⟨1249971, by rfl⟩ : syracuseStep 3333257 = 2499943) B2499943
theorem B2222171 : Blo 2221435 2222171 := bstep (se 1 (by rfl) ⟨1666628, by rfl⟩ : syracuseStep 2222171 = 3333257) B3333257
theorem B11249765 : Blo 2221435 11249765 := bbase (se 4 (by rfl) ⟨1054665, by rfl⟩ : syracuseStep 11249765 = 2109331) (by norm_num)
theorem B7499843 : Blo 2221435 7499843 := bstep (se 1 (by rfl) ⟨5624882, by rfl⟩ : syracuseStep 7499843 = 11249765) B11249765
theorem B4999895 : Blo 2221435 4999895 := bstep (se 1 (by rfl) ⟨3749921, by rfl⟩ : syracuseStep 4999895 = 7499843) B7499843
theorem B3333263 : Blo 2221435 3333263 := bstep (se 1 (by rfl) ⟨2499947, by rfl⟩ : syracuseStep 3333263 = 4999895) B4999895
theorem B2222175 : Blo 2221435 2222175 := bstep (se 1 (by rfl) ⟨1666631, by rfl⟩ : syracuseStep 2222175 = 3333263) B3333263
theorem B3333269 : Blo 2221435 3333269 := bbase (se 6 (by rfl) ⟨78123, by rfl⟩ : syracuseStep 3333269 = 156247) (by norm_num)
theorem B2222179 : Blo 2221435 2222179 := bstep (se 1 (by rfl) ⟨1666634, by rfl⟩ : syracuseStep 2222179 = 3333269) B3333269
theorem B4505005 : Blo 2221435 4505005 := bbase (se 3 (by rfl) ⟨844688, by rfl⟩ : syracuseStep 4505005 = 1689377) (by norm_num)
theorem B6006673 : Blo 2221435 6006673 := bstep (se 2 (by rfl) ⟨2252502, by rfl⟩ : syracuseStep 6006673 = 4505005) B4505005
theorem B8008897 : Blo 2221435 8008897 := bstep (se 2 (by rfl) ⟨3003336, by rfl⟩ : syracuseStep 8008897 = 6006673) B6006673
theorem B10678529 : Blo 2221435 10678529 := bstep (se 2 (by rfl) ⟨4004448, by rfl⟩ : syracuseStep 10678529 = 8008897) B8008897
theorem B7119019 : Blo 2221435 7119019 := bstep (se 1 (by rfl) ⟨5339264, by rfl⟩ : syracuseStep 7119019 = 10678529) B10678529
theorem B9492025 : Blo 2221435 9492025 := bstep (se 2 (by rfl) ⟨3559509, by rfl⟩ : syracuseStep 9492025 = 7119019) B7119019
theorem B12656033 : Blo 2221435 12656033 := bstep (se 2 (by rfl) ⟨4746012, by rfl⟩ : syracuseStep 12656033 = 9492025) B9492025
theorem B8437355 : Blo 2221435 8437355 := bstep (se 1 (by rfl) ⟨6328016, by rfl⟩ : syracuseStep 8437355 = 12656033) B12656033
theorem B5624903 : Blo 2221435 5624903 := bstep (se 1 (by rfl) ⟨4218677, by rfl⟩ : syracuseStep 5624903 = 8437355) B8437355
theorem B3749935 : Blo 2221435 3749935 := bstep (se 1 (by rfl) ⟨2812451, by rfl⟩ : syracuseStep 3749935 = 5624903) B5624903
theorem B4999913 : Blo 2221435 4999913 := bstep (se 2 (by rfl) ⟨1874967, by rfl⟩ : syracuseStep 4999913 = 3749935) B3749935
theorem B3333275 : Blo 2221435 3333275 := bstep (se 1 (by rfl) ⟨2499956, by rfl⟩ : syracuseStep 3333275 = 4999913) B4999913
theorem B2222183 : Blo 2221435 2222183 := bstep (se 1 (by rfl) ⟨1666637, by rfl⟩ : syracuseStep 2222183 = 3333275) B3333275
theorem B2499961 : Blo 2221435 2499961 := bbase (se 2 (by rfl) ⟨937485, by rfl⟩ : syracuseStep 2499961 = 1874971) (by norm_num)
theorem B3333281 : Blo 2221435 3333281 := bstep (se 2 (by rfl) ⟨1249980, by rfl⟩ : syracuseStep 3333281 = 2499961) B2499961
theorem B2222187 : Blo 2221435 2222187 := bstep (se 1 (by rfl) ⟨1666640, by rfl⟩ : syracuseStep 2222187 = 3333281) B3333281
theorem B105449557 : Blo 2221435 105449557 := bbase (se 8 (by rfl) ⟨617868, by rfl⟩ : syracuseStep 105449557 = 1235737) (by norm_num)
theorem B140599409 : Blo 2221435 140599409 := bstep (se 2 (by rfl) ⟨52724778, by rfl⟩ : syracuseStep 140599409 = 105449557) B105449557
theorem B374931757 : Blo 2221435 374931757 := bstep (se 3 (by rfl) ⟨70299704, by rfl⟩ : syracuseStep 374931757 = 140599409) B140599409
theorem B499909009 : Blo 2221435 499909009 := bstep (se 2 (by rfl) ⟨187465878, by rfl⟩ : syracuseStep 499909009 = 374931757) B374931757
theorem B666545345 : Blo 2221435 666545345 := bstep (se 2 (by rfl) ⟨249954504, by rfl⟩ : syracuseStep 666545345 = 499909009) B499909009
theorem B444363563 : Blo 2221435 444363563 := bstep (se 1 (by rfl) ⟨333272672, by rfl⟩ : syracuseStep 444363563 = 666545345) B666545345
theorem B296242375 : Blo 2221435 296242375 := bstep (se 1 (by rfl) ⟨222181781, by rfl⟩ : syracuseStep 296242375 = 444363563) B444363563
theorem B394989833 : Blo 2221435 394989833 := bstep (se 2 (by rfl) ⟨148121187, by rfl⟩ : syracuseStep 394989833 = 296242375) B296242375
theorem B263326555 : Blo 2221435 263326555 := bstep (se 1 (by rfl) ⟨197494916, by rfl⟩ : syracuseStep 263326555 = 394989833) B394989833
theorem B351102073 : Blo 2221435 351102073 := bstep (se 2 (by rfl) ⟨131663277, by rfl⟩ : syracuseStep 351102073 = 263326555) B263326555
theorem B468136097 : Blo 2221435 468136097 := bstep (se 2 (by rfl) ⟨175551036, by rfl⟩ : syracuseStep 468136097 = 351102073) B351102073
theorem B312090731 : Blo 2221435 312090731 := bstep (se 1 (by rfl) ⟨234068048, by rfl⟩ : syracuseStep 312090731 = 468136097) B468136097
theorem B208060487 : Blo 2221435 208060487 := bstep (se 1 (by rfl) ⟨156045365, by rfl⟩ : syracuseStep 208060487 = 312090731) B312090731
theorem B138706991 : Blo 2221435 138706991 := bstep (se 1 (by rfl) ⟨104030243, by rfl⟩ : syracuseStep 138706991 = 208060487) B208060487
theorem B92471327 : Blo 2221435 92471327 := bstep (se 1 (by rfl) ⟨69353495, by rfl⟩ : syracuseStep 92471327 = 138706991) B138706991
theorem B61647551 : Blo 2221435 61647551 := bstep (se 1 (by rfl) ⟨46235663, by rfl⟩ : syracuseStep 61647551 = 92471327) B92471327
theorem B41098367 : Blo 2221435 41098367 := bstep (se 1 (by rfl) ⟨30823775, by rfl⟩ : syracuseStep 41098367 = 61647551) B61647551
theorem B27398911 : Blo 2221435 27398911 := bstep (se 1 (by rfl) ⟨20549183, by rfl⟩ : syracuseStep 27398911 = 41098367) B41098367
theorem B36531881 : Blo 2221435 36531881 := bstep (se 2 (by rfl) ⟨13699455, by rfl⟩ : syracuseStep 36531881 = 27398911) B27398911
theorem B24354587 : Blo 2221435 24354587 := bstep (se 1 (by rfl) ⟨18265940, by rfl⟩ : syracuseStep 24354587 = 36531881) B36531881
theorem B16236391 : Blo 2221435 16236391 := bstep (se 1 (by rfl) ⟨12177293, by rfl⟩ : syracuseStep 16236391 = 24354587) B24354587
theorem B21648521 : Blo 2221435 21648521 := bstep (se 2 (by rfl) ⟨8118195, by rfl⟩ : syracuseStep 21648521 = 16236391) B16236391
theorem B14432347 : Blo 2221435 14432347 := bstep (se 1 (by rfl) ⟨10824260, by rfl⟩ : syracuseStep 14432347 = 21648521) B21648521
theorem B19243129 : Blo 2221435 19243129 := bstep (se 2 (by rfl) ⟨7216173, by rfl⟩ : syracuseStep 19243129 = 14432347) B14432347
theorem B25657505 : Blo 2221435 25657505 := bstep (se 2 (by rfl) ⟨9621564, by rfl⟩ : syracuseStep 25657505 = 19243129) B19243129
theorem B17105003 : Blo 2221435 17105003 := bstep (se 1 (by rfl) ⟨12828752, by rfl⟩ : syracuseStep 17105003 = 25657505) B25657505
theorem B11403335 : Blo 2221435 11403335 := bstep (se 1 (by rfl) ⟨8552501, by rfl⟩ : syracuseStep 11403335 = 17105003) B17105003
theorem B7602223 : Blo 2221435 7602223 := bstep (se 1 (by rfl) ⟨5701667, by rfl⟩ : syracuseStep 7602223 = 11403335) B11403335
theorem B10136297 : Blo 2221435 10136297 := bstep (se 2 (by rfl) ⟨3801111, by rfl⟩ : syracuseStep 10136297 = 7602223) B7602223
theorem B27030125 : Blo 2221435 27030125 := bstep (se 3 (by rfl) ⟨5068148, by rfl⟩ : syracuseStep 27030125 = 10136297) B10136297
theorem B18020083 : Blo 2221435 18020083 := bstep (se 1 (by rfl) ⟨13515062, by rfl⟩ : syracuseStep 18020083 = 27030125) B27030125
theorem B24026777 : Blo 2221435 24026777 := bstep (se 2 (by rfl) ⟨9010041, by rfl⟩ : syracuseStep 24026777 = 18020083) B18020083
theorem B16017851 : Blo 2221435 16017851 := bstep (se 1 (by rfl) ⟨12013388, by rfl⟩ : syracuseStep 16017851 = 24026777) B24026777
theorem B10678567 : Blo 2221435 10678567 := bstep (se 1 (by rfl) ⟨8008925, by rfl⟩ : syracuseStep 10678567 = 16017851) B16017851
theorem B14238089 : Blo 2221435 14238089 := bstep (se 2 (by rfl) ⟨5339283, by rfl⟩ : syracuseStep 14238089 = 10678567) B10678567
theorem B9492059 : Blo 2221435 9492059 := bstep (se 1 (by rfl) ⟨7119044, by rfl⟩ : syracuseStep 9492059 = 14238089) B14238089
theorem B6328039 : Blo 2221435 6328039 := bstep (se 1 (by rfl) ⟨4746029, by rfl⟩ : syracuseStep 6328039 = 9492059) B9492059
theorem B8437385 : Blo 2221435 8437385 := bstep (se 2 (by rfl) ⟨3164019, by rfl⟩ : syracuseStep 8437385 = 6328039) B6328039
theorem B5624923 : Blo 2221435 5624923 := bstep (se 1 (by rfl) ⟨4218692, by rfl⟩ : syracuseStep 5624923 = 8437385) B8437385
theorem B7499897 : Blo 2221435 7499897 := bstep (se 2 (by rfl) ⟨2812461, by rfl⟩ : syracuseStep 7499897 = 5624923) B5624923
theorem B4999931 : Blo 2221435 4999931 := bstep (se 1 (by rfl) ⟨3749948, by rfl⟩ : syracuseStep 4999931 = 7499897) B7499897
theorem B3333287 : Blo 2221435 3333287 := bstep (se 1 (by rfl) ⟨2499965, by rfl⟩ : syracuseStep 3333287 = 4999931) B4999931
theorem B2222191 : Blo 2221435 2222191 := bstep (se 1 (by rfl) ⟨1666643, by rfl⟩ : syracuseStep 2222191 = 3333287) B3333287
theorem B3333293 : Blo 2221435 3333293 := bbase (se 3 (by rfl) ⟨624992, by rfl⟩ : syracuseStep 3333293 = 1249985) (by norm_num)
theorem B2222195 : Blo 2221435 2222195 := bstep (se 1 (by rfl) ⟨1666646, by rfl⟩ : syracuseStep 2222195 = 3333293) B3333293
theorem B4999949 : Blo 2221435 4999949 := bbase (se 3 (by rfl) ⟨937490, by rfl⟩ : syracuseStep 4999949 = 1874981) (by norm_num)
theorem B3333299 : Blo 2221435 3333299 := bstep (se 1 (by rfl) ⟨2499974, by rfl⟩ : syracuseStep 3333299 = 4999949) B4999949
theorem B2222199 : Blo 2221435 2222199 := bstep (se 1 (by rfl) ⟨1666649, by rfl⟩ : syracuseStep 2222199 = 3333299) B3333299
theorem B2812477 : Blo 2221435 2812477 := bbase (se 3 (by rfl) ⟨527339, by rfl⟩ : syracuseStep 2812477 = 1054679) (by norm_num)
theorem B3749969 : Blo 2221435 3749969 := bstep (se 2 (by rfl) ⟨1406238, by rfl⟩ : syracuseStep 3749969 = 2812477) B2812477
theorem B2499979 : Blo 2221435 2499979 := bstep (se 1 (by rfl) ⟨1874984, by rfl⟩ : syracuseStep 2499979 = 3749969) B3749969
theorem B3333305 : Blo 2221435 3333305 := bstep (se 2 (by rfl) ⟨1249989, by rfl⟩ : syracuseStep 3333305 = 2499979) B2499979
theorem B2222203 : Blo 2221435 2222203 := bstep (se 1 (by rfl) ⟨1666652, by rfl⟩ : syracuseStep 2222203 = 3333305) B3333305
theorem B4505053 : Blo 2221435 4505053 := bbase (se 3 (by rfl) ⟨844697, by rfl⟩ : syracuseStep 4505053 = 1689395) (by norm_num)
theorem B6006737 : Blo 2221435 6006737 := bstep (se 2 (by rfl) ⟨2252526, by rfl⟩ : syracuseStep 6006737 = 4505053) B4505053
theorem B16017965 : Blo 2221435 16017965 := bstep (se 3 (by rfl) ⟨3003368, by rfl⟩ : syracuseStep 16017965 = 6006737) B6006737
theorem B10678643 : Blo 2221435 10678643 := bstep (se 1 (by rfl) ⟨8008982, by rfl⟩ : syracuseStep 10678643 = 16017965) B16017965
theorem B7119095 : Blo 2221435 7119095 := bstep (se 1 (by rfl) ⟨5339321, by rfl⟩ : syracuseStep 7119095 = 10678643) B10678643
theorem B18984253 : Blo 2221435 18984253 := bstep (se 3 (by rfl) ⟨3559547, by rfl⟩ : syracuseStep 18984253 = 7119095) B7119095
theorem B25312337 : Blo 2221435 25312337 := bstep (se 2 (by rfl) ⟨9492126, by rfl⟩ : syracuseStep 25312337 = 18984253) B18984253
theorem B16874891 : Blo 2221435 16874891 := bstep (se 1 (by rfl) ⟨12656168, by rfl⟩ : syracuseStep 16874891 = 25312337) B25312337
theorem B11249927 : Blo 2221435 11249927 := bstep (se 1 (by rfl) ⟨8437445, by rfl⟩ : syracuseStep 11249927 = 16874891) B16874891
theorem B7499951 : Blo 2221435 7499951 := bstep (se 1 (by rfl) ⟨5624963, by rfl⟩ : syracuseStep 7499951 = 11249927) B11249927
theorem B4999967 : Blo 2221435 4999967 := bstep (se 1 (by rfl) ⟨3749975, by rfl⟩ : syracuseStep 4999967 = 7499951) B7499951
theorem B3333311 : Blo 2221435 3333311 := bstep (se 1 (by rfl) ⟨2499983, by rfl⟩ : syracuseStep 3333311 = 4999967) B4999967
theorem B2222207 : Blo 2221435 2222207 := bstep (se 1 (by rfl) ⟨1666655, by rfl⟩ : syracuseStep 2222207 = 3333311) B3333311
theorem B3333317 : Blo 2221435 3333317 := bbase (se 4 (by rfl) ⟨312498, by rfl⟩ : syracuseStep 3333317 = 624997) (by norm_num)
theorem B2222211 : Blo 2221435 2222211 := bstep (se 1 (by rfl) ⟨1666658, by rfl⟩ : syracuseStep 2222211 = 3333317) B3333317
theorem B3749989 : Blo 2221435 3749989 := bbase (se 4 (by rfl) ⟨351561, by rfl⟩ : syracuseStep 3749989 = 703123) (by norm_num)
theorem B4999985 : Blo 2221435 4999985 := bstep (se 2 (by rfl) ⟨1874994, by rfl⟩ : syracuseStep 4999985 = 3749989) B3749989
theorem B3333323 : Blo 2221435 3333323 := bstep (se 1 (by rfl) ⟨2499992, by rfl⟩ : syracuseStep 3333323 = 4999985) B4999985
theorem B2222215 : Blo 2221435 2222215 := bstep (se 1 (by rfl) ⟨1666661, by rfl⟩ : syracuseStep 2222215 = 3333323) B3333323
theorem B2499997 : Blo 2221435 2499997 := bbase (se 3 (by rfl) ⟨468749, by rfl⟩ : syracuseStep 2499997 = 937499) (by norm_num)
theorem B3333329 : Blo 2221435 3333329 := bstep (se 2 (by rfl) ⟨1249998, by rfl⟩ : syracuseStep 3333329 = 2499997) B2499997
theorem B2222219 : Blo 2221435 2222219 := bstep (se 1 (by rfl) ⟨1666664, by rfl⟩ : syracuseStep 2222219 = 3333329) B3333329
theorem B7500005 : Blo 2221435 7500005 := bbase (se 4 (by rfl) ⟨703125, by rfl⟩ : syracuseStep 7500005 = 1406251) (by norm_num)
theorem B5000003 : Blo 2221435 5000003 := bstep (se 1 (by rfl) ⟨3750002, by rfl⟩ : syracuseStep 5000003 = 7500005) B7500005
theorem B3333335 : Blo 2221435 3333335 := bstep (se 1 (by rfl) ⟨2500001, by rfl⟩ : syracuseStep 3333335 = 5000003) B5000003
theorem B2222223 : Blo 2221435 2222223 := bstep (se 1 (by rfl) ⟨1666667, by rfl⟩ : syracuseStep 2222223 = 3333335) B3333335
theorem B3333341 : Blo 2221435 3333341 := bbase (se 3 (by rfl) ⟨625001, by rfl⟩ : syracuseStep 3333341 = 1250003) (by norm_num)
theorem B2222227 : Blo 2221435 2222227 := bstep (se 1 (by rfl) ⟨1666670, by rfl⟩ : syracuseStep 2222227 = 3333341) B3333341
theorem B5000021 : Blo 2221435 5000021 := bbase (se 9 (by rfl) ⟨14648, by rfl⟩ : syracuseStep 5000021 = 29297) (by norm_num)
theorem B3333347 : Blo 2221435 3333347 := bstep (se 1 (by rfl) ⟨2500010, by rfl⟩ : syracuseStep 3333347 = 5000021) B5000021
theorem B2222231 : Blo 2221435 2222231 := bstep (se 1 (by rfl) ⟨1666673, by rfl⟩ : syracuseStep 2222231 = 3333347) B3333347
theorem B6328165 : Blo 2221435 6328165 := bbase (se 4 (by rfl) ⟨593265, by rfl⟩ : syracuseStep 6328165 = 1186531) (by norm_num)
theorem B8437553 : Blo 2221435 8437553 := bstep (se 2 (by rfl) ⟨3164082, by rfl⟩ : syracuseStep 8437553 = 6328165) B6328165
theorem B5625035 : Blo 2221435 5625035 := bstep (se 1 (by rfl) ⟨4218776, by rfl⟩ : syracuseStep 5625035 = 8437553) B8437553
theorem B3750023 : Blo 2221435 3750023 := bstep (se 1 (by rfl) ⟨2812517, by rfl⟩ : syracuseStep 3750023 = 5625035) B5625035
theorem B2500015 : Blo 2221435 2500015 := bstep (se 1 (by rfl) ⟨1875011, by rfl⟩ : syracuseStep 2500015 = 3750023) B3750023
theorem B3333353 : Blo 2221435 3333353 := bstep (se 2 (by rfl) ⟨1250007, by rfl⟩ : syracuseStep 3333353 = 2500015) B2500015
theorem B2222235 : Blo 2221435 2222235 := bstep (se 1 (by rfl) ⟨1666676, by rfl⟩ : syracuseStep 2222235 = 3333353) B3333353
theorem B3608165 : Blo 2221435 3608165 := bbase (se 4 (by rfl) ⟨338265, by rfl⟩ : syracuseStep 3608165 = 676531) (by norm_num)
theorem B9621773 : Blo 2221435 9621773 := bstep (se 3 (by rfl) ⟨1804082, by rfl⟩ : syracuseStep 9621773 = 3608165) B3608165
theorem B6414515 : Blo 2221435 6414515 := bstep (se 1 (by rfl) ⟨4810886, by rfl⟩ : syracuseStep 6414515 = 9621773) B9621773
theorem B4276343 : Blo 2221435 4276343 := bstep (se 1 (by rfl) ⟨3207257, by rfl⟩ : syracuseStep 4276343 = 6414515) B6414515
theorem B2850895 : Blo 2221435 2850895 := bstep (se 1 (by rfl) ⟨2138171, by rfl⟩ : syracuseStep 2850895 = 4276343) B4276343
theorem B15204773 : Blo 2221435 15204773 := bstep (se 4 (by rfl) ⟨1425447, by rfl⟩ : syracuseStep 15204773 = 2850895) B2850895
theorem B10136515 : Blo 2221435 10136515 := bstep (se 1 (by rfl) ⟨7602386, by rfl⟩ : syracuseStep 10136515 = 15204773) B15204773
theorem B13515353 : Blo 2221435 13515353 := bstep (se 2 (by rfl) ⟨5068257, by rfl⟩ : syracuseStep 13515353 = 10136515) B10136515
theorem B9010235 : Blo 2221435 9010235 := bstep (se 1 (by rfl) ⟨6757676, by rfl⟩ : syracuseStep 9010235 = 13515353) B13515353
theorem B24027293 : Blo 2221435 24027293 := bstep (se 3 (by rfl) ⟨4505117, by rfl⟩ : syracuseStep 24027293 = 9010235) B9010235
theorem B64072781 : Blo 2221435 64072781 := bstep (se 3 (by rfl) ⟨12013646, by rfl⟩ : syracuseStep 64072781 = 24027293) B24027293
theorem B42715187 : Blo 2221435 42715187 := bstep (se 1 (by rfl) ⟨32036390, by rfl⟩ : syracuseStep 42715187 = 64072781) B64072781
theorem B28476791 : Blo 2221435 28476791 := bstep (se 1 (by rfl) ⟨21357593, by rfl⟩ : syracuseStep 28476791 = 42715187) B42715187
theorem B18984527 : Blo 2221435 18984527 := bstep (se 1 (by rfl) ⟨14238395, by rfl⟩ : syracuseStep 18984527 = 28476791) B28476791
theorem B12656351 : Blo 2221435 12656351 := bstep (se 1 (by rfl) ⟨9492263, by rfl⟩ : syracuseStep 12656351 = 18984527) B18984527
theorem B8437567 : Blo 2221435 8437567 := bstep (se 1 (by rfl) ⟨6328175, by rfl⟩ : syracuseStep 8437567 = 12656351) B12656351
theorem B11250089 : Blo 2221435 11250089 := bstep (se 2 (by rfl) ⟨4218783, by rfl⟩ : syracuseStep 11250089 = 8437567) B8437567
theorem B7500059 : Blo 2221435 7500059 := bstep (se 1 (by rfl) ⟨5625044, by rfl⟩ : syracuseStep 7500059 = 11250089) B11250089
theorem B5000039 : Blo 2221435 5000039 := bstep (se 1 (by rfl) ⟨3750029, by rfl⟩ : syracuseStep 5000039 = 7500059) B7500059
theorem B3333359 : Blo 2221435 3333359 := bstep (se 1 (by rfl) ⟨2500019, by rfl⟩ : syracuseStep 3333359 = 5000039) B5000039
theorem B2222239 : Blo 2221435 2222239 := bstep (se 1 (by rfl) ⟨1666679, by rfl⟩ : syracuseStep 2222239 = 3333359) B3333359
theorem B3333365 : Blo 2221435 3333365 := bbase (se 5 (by rfl) ⟨156251, by rfl⟩ : syracuseStep 3333365 = 312503) (by norm_num)
theorem B2222243 : Blo 2221435 2222243 := bstep (se 1 (by rfl) ⟨1666682, by rfl⟩ : syracuseStep 2222243 = 3333365) B3333365
theorem B10678837 : Blo 2221435 10678837 := bbase (se 5 (by rfl) ⟨500570, by rfl⟩ : syracuseStep 10678837 = 1001141) (by norm_num)
theorem B14238449 : Blo 2221435 14238449 := bstep (se 2 (by rfl) ⟨5339418, by rfl⟩ : syracuseStep 14238449 = 10678837) B10678837
theorem B9492299 : Blo 2221435 9492299 := bstep (se 1 (by rfl) ⟨7119224, by rfl⟩ : syracuseStep 9492299 = 14238449) B14238449
theorem B6328199 : Blo 2221435 6328199 := bstep (se 1 (by rfl) ⟨4746149, by rfl⟩ : syracuseStep 6328199 = 9492299) B9492299
theorem B4218799 : Blo 2221435 4218799 := bstep (se 1 (by rfl) ⟨3164099, by rfl⟩ : syracuseStep 4218799 = 6328199) B6328199
theorem B5625065 : Blo 2221435 5625065 := bstep (se 2 (by rfl) ⟨2109399, by rfl⟩ : syracuseStep 5625065 = 4218799) B4218799
theorem B3750043 : Blo 2221435 3750043 := bstep (se 1 (by rfl) ⟨2812532, by rfl⟩ : syracuseStep 3750043 = 5625065) B5625065
theorem B5000057 : Blo 2221435 5000057 := bstep (se 2 (by rfl) ⟨1875021, by rfl⟩ : syracuseStep 5000057 = 3750043) B3750043
theorem B3333371 : Blo 2221435 3333371 := bstep (se 1 (by rfl) ⟨2500028, by rfl⟩ : syracuseStep 3333371 = 5000057) B5000057
theorem B2222247 : Blo 2221435 2222247 := bstep (se 1 (by rfl) ⟨1666685, by rfl⟩ : syracuseStep 2222247 = 3333371) B3333371
theorem B2500033 : Blo 2221435 2500033 := bbase (se 2 (by rfl) ⟨937512, by rfl⟩ : syracuseStep 2500033 = 1875025) (by norm_num)
theorem B3333377 : Blo 2221435 3333377 := bstep (se 2 (by rfl) ⟨1250016, by rfl⟩ : syracuseStep 3333377 = 2500033) B2500033
theorem B2222251 : Blo 2221435 2222251 := bstep (se 1 (by rfl) ⟨1666688, by rfl⟩ : syracuseStep 2222251 = 3333377) B3333377
theorem B5625085 : Blo 2221435 5625085 := bbase (se 3 (by rfl) ⟨1054703, by rfl⟩ : syracuseStep 5625085 = 2109407) (by norm_num)
theorem B7500113 : Blo 2221435 7500113 := bstep (se 2 (by rfl) ⟨2812542, by rfl⟩ : syracuseStep 7500113 = 5625085) B5625085
theorem B5000075 : Blo 2221435 5000075 := bstep (se 1 (by rfl) ⟨3750056, by rfl⟩ : syracuseStep 5000075 = 7500113) B7500113
theorem B3333383 : Blo 2221435 3333383 := bstep (se 1 (by rfl) ⟨2500037, by rfl⟩ : syracuseStep 3333383 = 5000075) B5000075
theorem B2222255 : Blo 2221435 2222255 := bstep (se 1 (by rfl) ⟨1666691, by rfl⟩ : syracuseStep 2222255 = 3333383) B3333383
theorem B3333389 : Blo 2221435 3333389 := bbase (se 3 (by rfl) ⟨625010, by rfl⟩ : syracuseStep 3333389 = 1250021) (by norm_num)
theorem B2222259 : Blo 2221435 2222259 := bstep (se 1 (by rfl) ⟨1666694, by rfl⟩ : syracuseStep 2222259 = 3333389) B3333389
theorem B5000093 : Blo 2221435 5000093 := bbase (se 3 (by rfl) ⟨937517, by rfl⟩ : syracuseStep 5000093 = 1875035) (by norm_num)
theorem B3333395 : Blo 2221435 3333395 := bstep (se 1 (by rfl) ⟨2500046, by rfl⟩ : syracuseStep 3333395 = 5000093) B5000093
theorem B2222263 : Blo 2221435 2222263 := bstep (se 1 (by rfl) ⟨1666697, by rfl⟩ : syracuseStep 2222263 = 3333395) B3333395
theorem B3750077 : Blo 2221435 3750077 := bbase (se 3 (by rfl) ⟨703139, by rfl⟩ : syracuseStep 3750077 = 1406279) (by norm_num)
theorem B2500051 : Blo 2221435 2500051 := bstep (se 1 (by rfl) ⟨1875038, by rfl⟩ : syracuseStep 2500051 = 3750077) B3750077
theorem B3333401 : Blo 2221435 3333401 := bstep (se 2 (by rfl) ⟨1250025, by rfl⟩ : syracuseStep 3333401 = 2500051) B2500051
theorem B2222267 : Blo 2221435 2222267 := bstep (se 1 (by rfl) ⟨1666700, by rfl⟩ : syracuseStep 2222267 = 3333401) B3333401
theorem B12656533 : Blo 2221435 12656533 := bbase (se 6 (by rfl) ⟨296637, by rfl⟩ : syracuseStep 12656533 = 593275) (by norm_num)
theorem B16875377 : Blo 2221435 16875377 := bstep (se 2 (by rfl) ⟨6328266, by rfl⟩ : syracuseStep 16875377 = 12656533) B12656533
theorem B11250251 : Blo 2221435 11250251 := bstep (se 1 (by rfl) ⟨8437688, by rfl⟩ : syracuseStep 11250251 = 16875377) B16875377
theorem B7500167 : Blo 2221435 7500167 := bstep (se 1 (by rfl) ⟨5625125, by rfl⟩ : syracuseStep 7500167 = 11250251) B11250251
theorem B5000111 : Blo 2221435 5000111 := bstep (se 1 (by rfl) ⟨3750083, by rfl⟩ : syracuseStep 5000111 = 7500167) B7500167
theorem B3333407 : Blo 2221435 3333407 := bstep (se 1 (by rfl) ⟨2500055, by rfl⟩ : syracuseStep 3333407 = 5000111) B5000111
theorem B2222271 : Blo 2221435 2222271 := bstep (se 1 (by rfl) ⟨1666703, by rfl⟩ : syracuseStep 2222271 = 3333407) B3333407
theorem B3333413 : Blo 2221435 3333413 := bbase (se 4 (by rfl) ⟨312507, by rfl⟩ : syracuseStep 3333413 = 625015) (by norm_num)
theorem B2222275 : Blo 2221435 2222275 := bstep (se 1 (by rfl) ⟨1666706, by rfl⟩ : syracuseStep 2222275 = 3333413) B3333413
theorem B2812573 : Blo 2221435 2812573 := bbase (se 3 (by rfl) ⟨527357, by rfl⟩ : syracuseStep 2812573 = 1054715) (by norm_num)
theorem B3750097 : Blo 2221435 3750097 := bstep (se 2 (by rfl) ⟨1406286, by rfl⟩ : syracuseStep 3750097 = 2812573) B2812573
theorem B5000129 : Blo 2221435 5000129 := bstep (se 2 (by rfl) ⟨1875048, by rfl⟩ : syracuseStep 5000129 = 3750097) B3750097
theorem B3333419 : Blo 2221435 3333419 := bstep (se 1 (by rfl) ⟨2500064, by rfl⟩ : syracuseStep 3333419 = 5000129) B5000129
theorem B2222279 : Blo 2221435 2222279 := bstep (se 1 (by rfl) ⟨1666709, by rfl⟩ : syracuseStep 2222279 = 3333419) B3333419
theorem B2500069 : Blo 2221435 2500069 := bbase (se 4 (by rfl) ⟨234381, by rfl⟩ : syracuseStep 2500069 = 468763) (by norm_num)
theorem B3333425 : Blo 2221435 3333425 := bstep (se 2 (by rfl) ⟨1250034, by rfl⟩ : syracuseStep 3333425 = 2500069) B2500069
theorem B2222283 : Blo 2221435 2222283 := bstep (se 1 (by rfl) ⟨1666712, by rfl⟩ : syracuseStep 2222283 = 3333425) B3333425
theorem B3801277 : Blo 2221435 3801277 := bbase (se 3 (by rfl) ⟨712739, by rfl⟩ : syracuseStep 3801277 = 1425479) (by norm_num)
theorem B5068369 : Blo 2221435 5068369 := bstep (se 2 (by rfl) ⟨1900638, by rfl⟩ : syracuseStep 5068369 = 3801277) B3801277
theorem B6757825 : Blo 2221435 6757825 := bstep (se 2 (by rfl) ⟨2534184, by rfl⟩ : syracuseStep 6757825 = 5068369) B5068369
theorem B9010433 : Blo 2221435 9010433 := bstep (se 2 (by rfl) ⟨3378912, by rfl⟩ : syracuseStep 9010433 = 6757825) B6757825
theorem B6006955 : Blo 2221435 6006955 := bstep (se 1 (by rfl) ⟨4505216, by rfl⟩ : syracuseStep 6006955 = 9010433) B9010433
theorem B8009273 : Blo 2221435 8009273 := bstep (se 2 (by rfl) ⟨3003477, by rfl⟩ : syracuseStep 8009273 = 6006955) B6006955
theorem B5339515 : Blo 2221435 5339515 := bstep (se 1 (by rfl) ⟨4004636, by rfl⟩ : syracuseStep 5339515 = 8009273) B8009273
theorem B7119353 : Blo 2221435 7119353 := bstep (se 2 (by rfl) ⟨2669757, by rfl⟩ : syracuseStep 7119353 = 5339515) B5339515
theorem B4746235 : Blo 2221435 4746235 := bstep (se 1 (by rfl) ⟨3559676, by rfl⟩ : syracuseStep 4746235 = 7119353) B7119353
theorem B6328313 : Blo 2221435 6328313 := bstep (se 2 (by rfl) ⟨2373117, by rfl⟩ : syracuseStep 6328313 = 4746235) B4746235
theorem B4218875 : Blo 2221435 4218875 := bstep (se 1 (by rfl) ⟨3164156, by rfl⟩ : syracuseStep 4218875 = 6328313) B6328313
theorem B2812583 : Blo 2221435 2812583 := bstep (se 1 (by rfl) ⟨2109437, by rfl⟩ : syracuseStep 2812583 = 4218875) B4218875
theorem B7500221 : Blo 2221435 7500221 := bstep (se 3 (by rfl) ⟨1406291, by rfl⟩ : syracuseStep 7500221 = 2812583) B2812583
theorem B5000147 : Blo 2221435 5000147 := bstep (se 1 (by rfl) ⟨3750110, by rfl⟩ : syracuseStep 5000147 = 7500221) B7500221
theorem B3333431 : Blo 2221435 3333431 := bstep (se 1 (by rfl) ⟨2500073, by rfl⟩ : syracuseStep 3333431 = 5000147) B5000147
theorem B2222287 : Blo 2221435 2222287 := bstep (se 1 (by rfl) ⟨1666715, by rfl⟩ : syracuseStep 2222287 = 3333431) B3333431
theorem B3333437 : Blo 2221435 3333437 := bbase (se 3 (by rfl) ⟨625019, by rfl⟩ : syracuseStep 3333437 = 1250039) (by norm_num)
theorem B2222291 : Blo 2221435 2222291 := bstep (se 1 (by rfl) ⟨1666718, by rfl⟩ : syracuseStep 2222291 = 3333437) B3333437
theorem B5000165 : Blo 2221435 5000165 := bbase (se 4 (by rfl) ⟨468765, by rfl⟩ : syracuseStep 5000165 = 937531) (by norm_num)
theorem B3333443 : Blo 2221435 3333443 := bstep (se 1 (by rfl) ⟨2500082, by rfl⟩ : syracuseStep 3333443 = 5000165) B5000165
theorem B2222295 : Blo 2221435 2222295 := bstep (se 1 (by rfl) ⟨1666721, by rfl⟩ : syracuseStep 2222295 = 3333443) B3333443
theorem B5625197 : Blo 2221435 5625197 := bbase (se 3 (by rfl) ⟨1054724, by rfl⟩ : syracuseStep 5625197 = 2109449) (by norm_num)
theorem B3750131 : Blo 2221435 3750131 := bstep (se 1 (by rfl) ⟨2812598, by rfl⟩ : syracuseStep 3750131 = 5625197) B5625197
theorem B2500087 : Blo 2221435 2500087 := bstep (se 1 (by rfl) ⟨1875065, by rfl⟩ : syracuseStep 2500087 = 3750131) B3750131
theorem B3333449 : Blo 2221435 3333449 := bstep (se 2 (by rfl) ⟨1250043, by rfl⟩ : syracuseStep 3333449 = 2500087) B2500087
theorem B2222299 : Blo 2221435 2222299 := bstep (se 1 (by rfl) ⟨1666724, by rfl⟩ : syracuseStep 2222299 = 3333449) B3333449
theorem B4746269 : Blo 2221435 4746269 := bbase (se 3 (by rfl) ⟨889925, by rfl⟩ : syracuseStep 4746269 = 1779851) (by norm_num)
theorem B3164179 : Blo 2221435 3164179 := bstep (se 1 (by rfl) ⟨2373134, by rfl⟩ : syracuseStep 3164179 = 4746269) B4746269
theorem B4218905 : Blo 2221435 4218905 := bstep (se 2 (by rfl) ⟨1582089, by rfl⟩ : syracuseStep 4218905 = 3164179) B3164179
theorem B11250413 : Blo 2221435 11250413 := bstep (se 3 (by rfl) ⟨2109452, by rfl⟩ : syracuseStep 11250413 = 4218905) B4218905
theorem B7500275 : Blo 2221435 7500275 := bstep (se 1 (by rfl) ⟨5625206, by rfl⟩ : syracuseStep 7500275 = 11250413) B11250413
theorem B5000183 : Blo 2221435 5000183 := bstep (se 1 (by rfl) ⟨3750137, by rfl⟩ : syracuseStep 5000183 = 7500275) B7500275
theorem B3333455 : Blo 2221435 3333455 := bstep (se 1 (by rfl) ⟨2500091, by rfl⟩ : syracuseStep 3333455 = 5000183) B5000183
theorem B2222303 : Blo 2221435 2222303 := bstep (se 1 (by rfl) ⟨1666727, by rfl⟩ : syracuseStep 2222303 = 3333455) B3333455
theorem B3333461 : Blo 2221435 3333461 := bbase (se 11 (by rfl) ⟨2441, by rfl⟩ : syracuseStep 3333461 = 4883) (by norm_num)
theorem B2222307 : Blo 2221435 2222307 := bstep (se 1 (by rfl) ⟨1666730, by rfl⟩ : syracuseStep 2222307 = 3333461) B3333461
theorem B5339573 : Blo 2221435 5339573 := bbase (se 5 (by rfl) ⟨250292, by rfl⟩ : syracuseStep 5339573 = 500585) (by norm_num)
theorem B3559715 : Blo 2221435 3559715 := bstep (se 1 (by rfl) ⟨2669786, by rfl⟩ : syracuseStep 3559715 = 5339573) B5339573
theorem B2373143 : Blo 2221435 2373143 := bstep (se 1 (by rfl) ⟨1779857, by rfl⟩ : syracuseStep 2373143 = 3559715) B3559715
theorem B6328381 : Blo 2221435 6328381 := bstep (se 3 (by rfl) ⟨1186571, by rfl⟩ : syracuseStep 6328381 = 2373143) B2373143
theorem B8437841 : Blo 2221435 8437841 := bstep (se 2 (by rfl) ⟨3164190, by rfl⟩ : syracuseStep 8437841 = 6328381) B6328381
theorem B5625227 : Blo 2221435 5625227 := bstep (se 1 (by rfl) ⟨4218920, by rfl⟩ : syracuseStep 5625227 = 8437841) B8437841
theorem B3750151 : Blo 2221435 3750151 := bstep (se 1 (by rfl) ⟨2812613, by rfl⟩ : syracuseStep 3750151 = 5625227) B5625227
theorem B5000201 : Blo 2221435 5000201 := bstep (se 2 (by rfl) ⟨1875075, by rfl⟩ : syracuseStep 5000201 = 3750151) B3750151
theorem B3333467 : Blo 2221435 3333467 := bstep (se 1 (by rfl) ⟨2500100, by rfl⟩ : syracuseStep 3333467 = 5000201) B5000201
theorem B2222311 : Blo 2221435 2222311 := bstep (se 1 (by rfl) ⟨1666733, by rfl⟩ : syracuseStep 2222311 = 3333467) B3333467
theorem B2500105 : Blo 2221435 2500105 := bbase (se 2 (by rfl) ⟨937539, by rfl⟩ : syracuseStep 2500105 = 1875079) (by norm_num)
theorem B3333473 : Blo 2221435 3333473 := bstep (se 2 (by rfl) ⟨1250052, by rfl⟩ : syracuseStep 3333473 = 2500105) B2500105
theorem B2222315 : Blo 2221435 2222315 := bstep (se 1 (by rfl) ⟨1666736, by rfl⟩ : syracuseStep 2222315 = 3333473) B3333473
theorem B5779789 : Blo 2221435 5779789 := bbase (se 3 (by rfl) ⟨1083710, by rfl⟩ : syracuseStep 5779789 = 2167421) (by norm_num)
theorem B30825541 : Blo 2221435 30825541 := bstep (se 4 (by rfl) ⟨2889894, by rfl⟩ : syracuseStep 30825541 = 5779789) B5779789
theorem B164402885 : Blo 2221435 164402885 := bstep (se 4 (by rfl) ⟨15412770, by rfl⟩ : syracuseStep 164402885 = 30825541) B30825541
theorem B109601923 : Blo 2221435 109601923 := bstep (se 1 (by rfl) ⟨82201442, by rfl⟩ : syracuseStep 109601923 = 164402885) B164402885
theorem B146135897 : Blo 2221435 146135897 := bstep (se 2 (by rfl) ⟨54800961, by rfl⟩ : syracuseStep 146135897 = 109601923) B109601923
theorem B97423931 : Blo 2221435 97423931 := bstep (se 1 (by rfl) ⟨73067948, by rfl⟩ : syracuseStep 97423931 = 146135897) B146135897
theorem B64949287 : Blo 2221435 64949287 := bstep (se 1 (by rfl) ⟨48711965, by rfl⟩ : syracuseStep 64949287 = 97423931) B97423931
theorem B86599049 : Blo 2221435 86599049 := bstep (se 2 (by rfl) ⟨32474643, by rfl⟩ : syracuseStep 86599049 = 64949287) B64949287
theorem B923723189 : Blo 2221435 923723189 := bstep (se 5 (by rfl) ⟨43299524, by rfl⟩ : syracuseStep 923723189 = 86599049) B86599049
theorem B615815459 : Blo 2221435 615815459 := bstep (se 1 (by rfl) ⟨461861594, by rfl⟩ : syracuseStep 615815459 = 923723189) B923723189
theorem B410543639 : Blo 2221435 410543639 := bstep (se 1 (by rfl) ⟨307907729, by rfl⟩ : syracuseStep 410543639 = 615815459) B615815459
theorem B273695759 : Blo 2221435 273695759 := bstep (se 1 (by rfl) ⟨205271819, by rfl⟩ : syracuseStep 273695759 = 410543639) B410543639
theorem B182463839 : Blo 2221435 182463839 := bstep (se 1 (by rfl) ⟨136847879, by rfl⟩ : syracuseStep 182463839 = 273695759) B273695759
theorem B121642559 : Blo 2221435 121642559 := bstep (se 1 (by rfl) ⟨91231919, by rfl⟩ : syracuseStep 121642559 = 182463839) B182463839
theorem B81095039 : Blo 2221435 81095039 := bstep (se 1 (by rfl) ⟨60821279, by rfl⟩ : syracuseStep 81095039 = 121642559) B121642559
theorem B54063359 : Blo 2221435 54063359 := bstep (se 1 (by rfl) ⟨40547519, by rfl⟩ : syracuseStep 54063359 = 81095039) B81095039
theorem B36042239 : Blo 2221435 36042239 := bstep (se 1 (by rfl) ⟨27031679, by rfl⟩ : syracuseStep 36042239 = 54063359) B54063359
theorem B24028159 : Blo 2221435 24028159 := bstep (se 1 (by rfl) ⟨18021119, by rfl⟩ : syracuseStep 24028159 = 36042239) B36042239
theorem B32037545 : Blo 2221435 32037545 := bstep (se 2 (by rfl) ⟨12014079, by rfl⟩ : syracuseStep 32037545 = 24028159) B24028159
theorem B21358363 : Blo 2221435 21358363 := bstep (se 1 (by rfl) ⟨16018772, by rfl⟩ : syracuseStep 21358363 = 32037545) B32037545
theorem B28477817 : Blo 2221435 28477817 := bstep (se 2 (by rfl) ⟨10679181, by rfl⟩ : syracuseStep 28477817 = 21358363) B21358363
theorem B18985211 : Blo 2221435 18985211 := bstep (se 1 (by rfl) ⟨14238908, by rfl⟩ : syracuseStep 18985211 = 28477817) B28477817
theorem B12656807 : Blo 2221435 12656807 := bstep (se 1 (by rfl) ⟨9492605, by rfl⟩ : syracuseStep 12656807 = 18985211) B18985211
theorem B8437871 : Blo 2221435 8437871 := bstep (se 1 (by rfl) ⟨6328403, by rfl⟩ : syracuseStep 8437871 = 12656807) B12656807
theorem B5625247 : Blo 2221435 5625247 := bstep (se 1 (by rfl) ⟨4218935, by rfl⟩ : syracuseStep 5625247 = 8437871) B8437871
theorem B7500329 : Blo 2221435 7500329 := bstep (se 2 (by rfl) ⟨2812623, by rfl⟩ : syracuseStep 7500329 = 5625247) B5625247
theorem B5000219 : Blo 2221435 5000219 := bstep (se 1 (by rfl) ⟨3750164, by rfl⟩ : syracuseStep 5000219 = 7500329) B7500329
theorem B3333479 : Blo 2221435 3333479 := bstep (se 1 (by rfl) ⟨2500109, by rfl⟩ : syracuseStep 3333479 = 5000219) B5000219
theorem B2222319 : Blo 2221435 2222319 := bstep (se 1 (by rfl) ⟨1666739, by rfl⟩ : syracuseStep 2222319 = 3333479) B3333479
theorem B3333485 : Blo 2221435 3333485 := bbase (se 3 (by rfl) ⟨625028, by rfl⟩ : syracuseStep 3333485 = 1250057) (by norm_num)
theorem B2222323 : Blo 2221435 2222323 := bstep (se 1 (by rfl) ⟨1666742, by rfl⟩ : syracuseStep 2222323 = 3333485) B3333485
theorem B5000237 : Blo 2221435 5000237 := bbase (se 3 (by rfl) ⟨937544, by rfl⟩ : syracuseStep 5000237 = 1875089) (by norm_num)
theorem B3333491 : Blo 2221435 3333491 := bstep (se 1 (by rfl) ⟨2500118, by rfl⟩ : syracuseStep 3333491 = 5000237) B5000237
theorem B2222327 : Blo 2221435 2222327 := bstep (se 1 (by rfl) ⟨1666745, by rfl⟩ : syracuseStep 2222327 = 3333491) B3333491
theorem B5339621 : Blo 2221435 5339621 := bbase (se 4 (by rfl) ⟨500589, by rfl⟩ : syracuseStep 5339621 = 1001179) (by norm_num)
theorem B14238989 : Blo 2221435 14238989 := bstep (se 3 (by rfl) ⟨2669810, by rfl⟩ : syracuseStep 14238989 = 5339621) B5339621
theorem B9492659 : Blo 2221435 9492659 := bstep (se 1 (by rfl) ⟨7119494, by rfl⟩ : syracuseStep 9492659 = 14238989) B14238989
theorem B6328439 : Blo 2221435 6328439 := bstep (se 1 (by rfl) ⟨4746329, by rfl⟩ : syracuseStep 6328439 = 9492659) B9492659
theorem B4218959 : Blo 2221435 4218959 := bstep (se 1 (by rfl) ⟨3164219, by rfl⟩ : syracuseStep 4218959 = 6328439) B6328439
theorem B2812639 : Blo 2221435 2812639 := bstep (se 1 (by rfl) ⟨2109479, by rfl⟩ : syracuseStep 2812639 = 4218959) B4218959
theorem B3750185 : Blo 2221435 3750185 := bstep (se 2 (by rfl) ⟨1406319, by rfl⟩ : syracuseStep 3750185 = 2812639) B2812639
theorem B2500123 : Blo 2221435 2500123 := bstep (se 1 (by rfl) ⟨1875092, by rfl⟩ : syracuseStep 2500123 = 3750185) B3750185
theorem B3333497 : Blo 2221435 3333497 := bstep (se 2 (by rfl) ⟨1250061, by rfl⟩ : syracuseStep 3333497 = 2500123) B2500123
theorem B2222331 : Blo 2221435 2222331 := bstep (se 1 (by rfl) ⟨1666748, by rfl⟩ : syracuseStep 2222331 = 3333497) B3333497
theorem B5339629 : Blo 2221435 5339629 := bbase (se 3 (by rfl) ⟨1001180, by rfl⟩ : syracuseStep 5339629 = 2002361) (by norm_num)
theorem B7119505 : Blo 2221435 7119505 := bstep (se 2 (by rfl) ⟨2669814, by rfl⟩ : syracuseStep 7119505 = 5339629) B5339629
theorem B37970693 : Blo 2221435 37970693 := bstep (se 4 (by rfl) ⟨3559752, by rfl⟩ : syracuseStep 37970693 = 7119505) B7119505
theorem B25313795 : Blo 2221435 25313795 := bstep (se 1 (by rfl) ⟨18985346, by rfl⟩ : syracuseStep 25313795 = 37970693) B37970693
theorem B16875863 : Blo 2221435 16875863 := bstep (se 1 (by rfl) ⟨12656897, by rfl⟩ : syracuseStep 16875863 = 25313795) B25313795
theorem B11250575 : Blo 2221435 11250575 := bstep (se 1 (by rfl) ⟨8437931, by rfl⟩ : syracuseStep 11250575 = 16875863) B16875863
theorem B7500383 : Blo 2221435 7500383 := bstep (se 1 (by rfl) ⟨5625287, by rfl⟩ : syracuseStep 7500383 = 11250575) B11250575
theorem B5000255 : Blo 2221435 5000255 := bstep (se 1 (by rfl) ⟨3750191, by rfl⟩ : syracuseStep 5000255 = 7500383) B7500383
theorem B3333503 : Blo 2221435 3333503 := bstep (se 1 (by rfl) ⟨2500127, by rfl⟩ : syracuseStep 3333503 = 5000255) B5000255
theorem B2222335 : Blo 2221435 2222335 := bstep (se 1 (by rfl) ⟨1666751, by rfl⟩ : syracuseStep 2222335 = 3333503) B3333503
theorem B3333509 : Blo 2221435 3333509 := bbase (se 4 (by rfl) ⟨312516, by rfl⟩ : syracuseStep 3333509 = 625033) (by norm_num)
theorem B2222339 : Blo 2221435 2222339 := bstep (se 1 (by rfl) ⟨1666754, by rfl⟩ : syracuseStep 2222339 = 3333509) B3333509
theorem B3750205 : Blo 2221435 3750205 := bbase (se 3 (by rfl) ⟨703163, by rfl⟩ : syracuseStep 3750205 = 1406327) (by norm_num)
theorem B5000273 : Blo 2221435 5000273 := bstep (se 2 (by rfl) ⟨1875102, by rfl⟩ : syracuseStep 5000273 = 3750205) B3750205
theorem B3333515 : Blo 2221435 3333515 := bstep (se 1 (by rfl) ⟨2500136, by rfl⟩ : syracuseStep 3333515 = 5000273) B5000273
theorem B2222343 : Blo 2221435 2222343 := bstep (se 1 (by rfl) ⟨1666757, by rfl⟩ : syracuseStep 2222343 = 3333515) B3333515
theorem B2500141 : Blo 2221435 2500141 := bbase (se 3 (by rfl) ⟨468776, by rfl⟩ : syracuseStep 2500141 = 937553) (by norm_num)
theorem B3333521 : Blo 2221435 3333521 := bstep (se 2 (by rfl) ⟨1250070, by rfl⟩ : syracuseStep 3333521 = 2500141) B2500141
theorem B2222347 : Blo 2221435 2222347 := bstep (se 1 (by rfl) ⟨1666760, by rfl⟩ : syracuseStep 2222347 = 3333521) B3333521
theorem B7500437 : Blo 2221435 7500437 := bbase (se 6 (by rfl) ⟨175791, by rfl⟩ : syracuseStep 7500437 = 351583) (by norm_num)
theorem B5000291 : Blo 2221435 5000291 := bstep (se 1 (by rfl) ⟨3750218, by rfl⟩ : syracuseStep 5000291 = 7500437) B7500437
theorem B3333527 : Blo 2221435 3333527 := bstep (se 1 (by rfl) ⟨2500145, by rfl⟩ : syracuseStep 3333527 = 5000291) B5000291
theorem B2222351 : Blo 2221435 2222351 := bstep (se 1 (by rfl) ⟨1666763, by rfl⟩ : syracuseStep 2222351 = 3333527) B3333527
theorem B3333533 : Blo 2221435 3333533 := bbase (se 3 (by rfl) ⟨625037, by rfl⟩ : syracuseStep 3333533 = 1250075) (by norm_num)
theorem B2222355 : Blo 2221435 2222355 := bstep (se 1 (by rfl) ⟨1666766, by rfl⟩ : syracuseStep 2222355 = 3333533) B3333533
theorem B5000309 : Blo 2221435 5000309 := bbase (se 5 (by rfl) ⟨234389, by rfl⟩ : syracuseStep 5000309 = 468779) (by norm_num)
theorem B3333539 : Blo 2221435 3333539 := bstep (se 1 (by rfl) ⟨2500154, by rfl⟩ : syracuseStep 3333539 = 5000309) B5000309
theorem B2222359 : Blo 2221435 2222359 := bstep (se 1 (by rfl) ⟨1666769, by rfl⟩ : syracuseStep 2222359 = 3333539) B3333539
theorem B18985589 : Blo 2221435 18985589 := bbase (se 5 (by rfl) ⟨889949, by rfl⟩ : syracuseStep 18985589 = 1779899) (by norm_num)
theorem B12657059 : Blo 2221435 12657059 := bstep (se 1 (by rfl) ⟨9492794, by rfl⟩ : syracuseStep 12657059 = 18985589) B18985589
theorem B8438039 : Blo 2221435 8438039 := bstep (se 1 (by rfl) ⟨6328529, by rfl⟩ : syracuseStep 8438039 = 12657059) B12657059
theorem B5625359 : Blo 2221435 5625359 := bstep (se 1 (by rfl) ⟨4219019, by rfl⟩ : syracuseStep 5625359 = 8438039) B8438039
theorem B3750239 : Blo 2221435 3750239 := bstep (se 1 (by rfl) ⟨2812679, by rfl⟩ : syracuseStep 3750239 = 5625359) B5625359
theorem B2500159 : Blo 2221435 2500159 := bstep (se 1 (by rfl) ⟨1875119, by rfl⟩ : syracuseStep 2500159 = 3750239) B3750239
theorem B3333545 : Blo 2221435 3333545 := bstep (se 2 (by rfl) ⟨1250079, by rfl⟩ : syracuseStep 3333545 = 2500159) B2500159
theorem B2222363 : Blo 2221435 2222363 := bstep (se 1 (by rfl) ⟨1666772, by rfl⟩ : syracuseStep 2222363 = 3333545) B3333545
theorem B8438053 : Blo 2221435 8438053 := bbase (se 4 (by rfl) ⟨791067, by rfl⟩ : syracuseStep 8438053 = 1582135) (by norm_num)
theorem B11250737 : Blo 2221435 11250737 := bstep (se 2 (by rfl) ⟨4219026, by rfl⟩ : syracuseStep 11250737 = 8438053) B8438053
theorem B7500491 : Blo 2221435 7500491 := bstep (se 1 (by rfl) ⟨5625368, by rfl⟩ : syracuseStep 7500491 = 11250737) B11250737
theorem B5000327 : Blo 2221435 5000327 := bstep (se 1 (by rfl) ⟨3750245, by rfl⟩ : syracuseStep 5000327 = 7500491) B7500491
theorem B3333551 : Blo 2221435 3333551 := bstep (se 1 (by rfl) ⟨2500163, by rfl⟩ : syracuseStep 3333551 = 5000327) B5000327
theorem B2222367 : Blo 2221435 2222367 := bstep (se 1 (by rfl) ⟨1666775, by rfl⟩ : syracuseStep 2222367 = 3333551) B3333551
theorem B3333557 : Blo 2221435 3333557 := bbase (se 5 (by rfl) ⟨156260, by rfl⟩ : syracuseStep 3333557 = 312521) (by norm_num)
theorem B2222371 : Blo 2221435 2222371 := bstep (se 1 (by rfl) ⟨1666778, by rfl⟩ : syracuseStep 2222371 = 3333557) B3333557
theorem B5625389 : Blo 2221435 5625389 := bbase (se 3 (by rfl) ⟨1054760, by rfl⟩ : syracuseStep 5625389 = 2109521) (by norm_num)
theorem B3750259 : Blo 2221435 3750259 := bstep (se 1 (by rfl) ⟨2812694, by rfl⟩ : syracuseStep 3750259 = 5625389) B5625389
theorem B5000345 : Blo 2221435 5000345 := bstep (se 2 (by rfl) ⟨1875129, by rfl⟩ : syracuseStep 5000345 = 3750259) B3750259
theorem B3333563 : Blo 2221435 3333563 := bstep (se 1 (by rfl) ⟨2500172, by rfl⟩ : syracuseStep 3333563 = 5000345) B5000345
theorem B2222375 : Blo 2221435 2222375 := bstep (se 1 (by rfl) ⟨1666781, by rfl⟩ : syracuseStep 2222375 = 3333563) B3333563
theorem B2500177 : Blo 2221435 2500177 := bbase (se 2 (by rfl) ⟨937566, by rfl⟩ : syracuseStep 2500177 = 1875133) (by norm_num)
theorem B3333569 : Blo 2221435 3333569 := bstep (se 2 (by rfl) ⟨1250088, by rfl⟩ : syracuseStep 3333569 = 2500177) B2500177
theorem B2222379 : Blo 2221435 2222379 := bstep (se 1 (by rfl) ⟨1666784, by rfl⟩ : syracuseStep 2222379 = 3333569) B3333569
theorem B3164293 : Blo 2221435 3164293 := bbase (se 4 (by rfl) ⟨296652, by rfl⟩ : syracuseStep 3164293 = 593305) (by norm_num)
theorem B4219057 : Blo 2221435 4219057 := bstep (se 2 (by rfl) ⟨1582146, by rfl⟩ : syracuseStep 4219057 = 3164293) B3164293
theorem B5625409 : Blo 2221435 5625409 := bstep (se 2 (by rfl) ⟨2109528, by rfl⟩ : syracuseStep 5625409 = 4219057) B4219057
theorem B7500545 : Blo 2221435 7500545 := bstep (se 2 (by rfl) ⟨2812704, by rfl⟩ : syracuseStep 7500545 = 5625409) B5625409
theorem B5000363 : Blo 2221435 5000363 := bstep (se 1 (by rfl) ⟨3750272, by rfl⟩ : syracuseStep 5000363 = 7500545) B7500545
theorem B3333575 : Blo 2221435 3333575 := bstep (se 1 (by rfl) ⟨2500181, by rfl⟩ : syracuseStep 3333575 = 5000363) B5000363
theorem B2222383 : Blo 2221435 2222383 := bstep (se 1 (by rfl) ⟨1666787, by rfl⟩ : syracuseStep 2222383 = 3333575) B3333575
theorem B3333581 : Blo 2221435 3333581 := bbase (se 3 (by rfl) ⟨625046, by rfl⟩ : syracuseStep 3333581 = 1250093) (by norm_num)
theorem B2222387 : Blo 2221435 2222387 := bstep (se 1 (by rfl) ⟨1666790, by rfl⟩ : syracuseStep 2222387 = 3333581) B3333581
theorem B5000381 : Blo 2221435 5000381 := bbase (se 3 (by rfl) ⟨937571, by rfl⟩ : syracuseStep 5000381 = 1875143) (by norm_num)
theorem B3333587 : Blo 2221435 3333587 := bstep (se 1 (by rfl) ⟨2500190, by rfl⟩ : syracuseStep 3333587 = 5000381) B5000381
theorem B2222391 : Blo 2221435 2222391 := bstep (se 1 (by rfl) ⟨1666793, by rfl⟩ : syracuseStep 2222391 = 3333587) B3333587
theorem B3750293 : Blo 2221435 3750293 := bbase (se 6 (by rfl) ⟨87897, by rfl⟩ : syracuseStep 3750293 = 175795) (by norm_num)
theorem B2500195 : Blo 2221435 2500195 := bstep (se 1 (by rfl) ⟨1875146, by rfl⟩ : syracuseStep 2500195 = 3750293) B3750293
theorem B3333593 : Blo 2221435 3333593 := bstep (se 2 (by rfl) ⟨1250097, by rfl⟩ : syracuseStep 3333593 = 2500195) B2500195
theorem B2222395 : Blo 2221435 2222395 := bstep (se 1 (by rfl) ⟨1666796, by rfl⟩ : syracuseStep 2222395 = 3333593) B3333593
theorem B9010885 : Blo 2221435 9010885 := bbase (se 4 (by rfl) ⟨844770, by rfl⟩ : syracuseStep 9010885 = 1689541) (by norm_num)
theorem B12014513 : Blo 2221435 12014513 := bstep (se 2 (by rfl) ⟨4505442, by rfl⟩ : syracuseStep 12014513 = 9010885) B9010885
theorem B8009675 : Blo 2221435 8009675 := bstep (se 1 (by rfl) ⟨6007256, by rfl⟩ : syracuseStep 8009675 = 12014513) B12014513
theorem B5339783 : Blo 2221435 5339783 := bstep (se 1 (by rfl) ⟨4004837, by rfl⟩ : syracuseStep 5339783 = 8009675) B8009675
theorem B14239421 : Blo 2221435 14239421 := bstep (se 3 (by rfl) ⟨2669891, by rfl⟩ : syracuseStep 14239421 = 5339783) B5339783
theorem B9492947 : Blo 2221435 9492947 := bstep (se 1 (by rfl) ⟨7119710, by rfl⟩ : syracuseStep 9492947 = 14239421) B14239421
theorem B6328631 : Blo 2221435 6328631 := bstep (se 1 (by rfl) ⟨4746473, by rfl⟩ : syracuseStep 6328631 = 9492947) B9492947
theorem B16876349 : Blo 2221435 16876349 := bstep (se 3 (by rfl) ⟨3164315, by rfl⟩ : syracuseStep 16876349 = 6328631) B6328631
theorem B11250899 : Blo 2221435 11250899 := bstep (se 1 (by rfl) ⟨8438174, by rfl⟩ : syracuseStep 11250899 = 16876349) B16876349
theorem B7500599 : Blo 2221435 7500599 := bstep (se 1 (by rfl) ⟨5625449, by rfl⟩ : syracuseStep 7500599 = 11250899) B11250899
theorem B5000399 : Blo 2221435 5000399 := bstep (se 1 (by rfl) ⟨3750299, by rfl⟩ : syracuseStep 5000399 = 7500599) B7500599
theorem B3333599 : Blo 2221435 3333599 := bstep (se 1 (by rfl) ⟨2500199, by rfl⟩ : syracuseStep 3333599 = 5000399) B5000399
theorem B2222399 : Blo 2221435 2222399 := bstep (se 1 (by rfl) ⟨1666799, by rfl⟩ : syracuseStep 2222399 = 3333599) B3333599
theorem B3333605 : Blo 2221435 3333605 := bbase (se 4 (by rfl) ⟨312525, by rfl⟩ : syracuseStep 3333605 = 625051) (by norm_num)
theorem B2222403 : Blo 2221435 2222403 := bstep (se 1 (by rfl) ⟨1666802, by rfl⟩ : syracuseStep 2222403 = 3333605) B3333605
theorem B38490005 : Blo 2221435 38490005 := bbase (se 6 (by rfl) ⟨902109, by rfl⟩ : syracuseStep 38490005 = 1804219) (by norm_num)
theorem B25660003 : Blo 2221435 25660003 := bstep (se 1 (by rfl) ⟨19245002, by rfl⟩ : syracuseStep 25660003 = 38490005) B38490005
theorem B34213337 : Blo 2221435 34213337 := bstep (se 2 (by rfl) ⟨12830001, by rfl⟩ : syracuseStep 34213337 = 25660003) B25660003
theorem B22808891 : Blo 2221435 22808891 := bstep (se 1 (by rfl) ⟨17106668, by rfl⟩ : syracuseStep 22808891 = 34213337) B34213337
theorem B15205927 : Blo 2221435 15205927 := bstep (se 1 (by rfl) ⟨11404445, by rfl⟩ : syracuseStep 15205927 = 22808891) B22808891
theorem B20274569 : Blo 2221435 20274569 := bstep (se 2 (by rfl) ⟨7602963, by rfl⟩ : syracuseStep 20274569 = 15205927) B15205927
theorem B13516379 : Blo 2221435 13516379 := bstep (se 1 (by rfl) ⟨10137284, by rfl⟩ : syracuseStep 13516379 = 20274569) B20274569
theorem B9010919 : Blo 2221435 9010919 := bstep (se 1 (by rfl) ⟨6758189, by rfl⟩ : syracuseStep 9010919 = 13516379) B13516379
theorem B6007279 : Blo 2221435 6007279 := bstep (se 1 (by rfl) ⟨4505459, by rfl⟩ : syracuseStep 6007279 = 9010919) B9010919
theorem B8009705 : Blo 2221435 8009705 := bstep (se 2 (by rfl) ⟨3003639, by rfl⟩ : syracuseStep 8009705 = 6007279) B6007279
theorem B21359213 : Blo 2221435 21359213 := bstep (se 3 (by rfl) ⟨4004852, by rfl⟩ : syracuseStep 21359213 = 8009705) B8009705
theorem B14239475 : Blo 2221435 14239475 := bstep (se 1 (by rfl) ⟨10679606, by rfl⟩ : syracuseStep 14239475 = 21359213) B21359213
theorem B9492983 : Blo 2221435 9492983 := bstep (se 1 (by rfl) ⟨7119737, by rfl⟩ : syracuseStep 9492983 = 14239475) B14239475
theorem B6328655 : Blo 2221435 6328655 := bstep (se 1 (by rfl) ⟨4746491, by rfl⟩ : syracuseStep 6328655 = 9492983) B9492983
theorem B4219103 : Blo 2221435 4219103 := bstep (se 1 (by rfl) ⟨3164327, by rfl⟩ : syracuseStep 4219103 = 6328655) B6328655
theorem B2812735 : Blo 2221435 2812735 := bstep (se 1 (by rfl) ⟨2109551, by rfl⟩ : syracuseStep 2812735 = 4219103) B4219103
theorem B3750313 : Blo 2221435 3750313 := bstep (se 2 (by rfl) ⟨1406367, by rfl⟩ : syracuseStep 3750313 = 2812735) B2812735
theorem B5000417 : Blo 2221435 5000417 := bstep (se 2 (by rfl) ⟨1875156, by rfl⟩ : syracuseStep 5000417 = 3750313) B3750313
theorem B3333611 : Blo 2221435 3333611 := bstep (se 1 (by rfl) ⟨2500208, by rfl⟩ : syracuseStep 3333611 = 5000417) B5000417
theorem B2222407 : Blo 2221435 2222407 := bstep (se 1 (by rfl) ⟨1666805, by rfl⟩ : syracuseStep 2222407 = 3333611) B3333611
theorem B2500213 : Blo 2221435 2500213 := bbase (se 5 (by rfl) ⟨117197, by rfl⟩ : syracuseStep 2500213 = 234395) (by norm_num)
theorem B3333617 : Blo 2221435 3333617 := bstep (se 2 (by rfl) ⟨1250106, by rfl⟩ : syracuseStep 3333617 = 2500213) B2500213
theorem B2222411 : Blo 2221435 2222411 := bstep (se 1 (by rfl) ⟨1666808, by rfl⟩ : syracuseStep 2222411 = 3333617) B3333617
theorem B2812745 : Blo 2221435 2812745 := bbase (se 2 (by rfl) ⟨1054779, by rfl⟩ : syracuseStep 2812745 = 2109559) (by norm_num)
theorem B7500653 : Blo 2221435 7500653 := bstep (se 3 (by rfl) ⟨1406372, by rfl⟩ : syracuseStep 7500653 = 2812745) B2812745
theorem B5000435 : Blo 2221435 5000435 := bstep (se 1 (by rfl) ⟨3750326, by rfl⟩ : syracuseStep 5000435 = 7500653) B7500653
theorem B3333623 : Blo 2221435 3333623 := bstep (se 1 (by rfl) ⟨2500217, by rfl⟩ : syracuseStep 3333623 = 5000435) B5000435
theorem B2222415 : Blo 2221435 2222415 := bstep (se 1 (by rfl) ⟨1666811, by rfl⟩ : syracuseStep 2222415 = 3333623) B3333623
theorem B3333629 : Blo 2221435 3333629 := bbase (se 3 (by rfl) ⟨625055, by rfl⟩ : syracuseStep 3333629 = 1250111) (by norm_num)
theorem B2222419 : Blo 2221435 2222419 := bstep (se 1 (by rfl) ⟨1666814, by rfl⟩ : syracuseStep 2222419 = 3333629) B3333629
theorem B5000453 : Blo 2221435 5000453 := bbase (se 4 (by rfl) ⟨468792, by rfl⟩ : syracuseStep 5000453 = 937585) (by norm_num)
theorem B3333635 : Blo 2221435 3333635 := bstep (se 1 (by rfl) ⟨2500226, by rfl⟩ : syracuseStep 3333635 = 5000453) B5000453
theorem B2222423 : Blo 2221435 2222423 := bstep (se 1 (by rfl) ⟨1666817, by rfl⟩ : syracuseStep 2222423 = 3333635) B3333635
theorem B4219141 : Blo 2221435 4219141 := bbase (se 4 (by rfl) ⟨395544, by rfl⟩ : syracuseStep 4219141 = 791089) (by norm_num)
theorem B5625521 : Blo 2221435 5625521 := bstep (se 2 (by rfl) ⟨2109570, by rfl⟩ : syracuseStep 5625521 = 4219141) B4219141
theorem B3750347 : Blo 2221435 3750347 := bstep (se 1 (by rfl) ⟨2812760, by rfl⟩ : syracuseStep 3750347 = 5625521) B5625521
theorem B2500231 : Blo 2221435 2500231 := bstep (se 1 (by rfl) ⟨1875173, by rfl⟩ : syracuseStep 2500231 = 3750347) B3750347
theorem B3333641 : Blo 2221435 3333641 := bstep (se 2 (by rfl) ⟨1250115, by rfl⟩ : syracuseStep 3333641 = 2500231) B2500231
theorem B2222427 : Blo 2221435 2222427 := bstep (se 1 (by rfl) ⟨1666820, by rfl⟩ : syracuseStep 2222427 = 3333641) B3333641
theorem B11251061 : Blo 2221435 11251061 := bbase (se 5 (by rfl) ⟨527393, by rfl⟩ : syracuseStep 11251061 = 1054787) (by norm_num)
theorem B7500707 : Blo 2221435 7500707 := bstep (se 1 (by rfl) ⟨5625530, by rfl⟩ : syracuseStep 7500707 = 11251061) B11251061
theorem B5000471 : Blo 2221435 5000471 := bstep (se 1 (by rfl) ⟨3750353, by rfl⟩ : syracuseStep 5000471 = 7500707) B7500707
theorem B3333647 : Blo 2221435 3333647 := bstep (se 1 (by rfl) ⟨2500235, by rfl⟩ : syracuseStep 3333647 = 5000471) B5000471
theorem B2222431 : Blo 2221435 2222431 := bstep (se 1 (by rfl) ⟨1666823, by rfl⟩ : syracuseStep 2222431 = 3333647) B3333647
theorem B3333653 : Blo 2221435 3333653 := bbase (se 6 (by rfl) ⟨78132, by rfl⟩ : syracuseStep 3333653 = 156265) (by norm_num)
theorem B2222435 : Blo 2221435 2222435 := bstep (se 1 (by rfl) ⟨1666826, by rfl⟩ : syracuseStep 2222435 = 3333653) B3333653
theorem B4335077 : Blo 2221435 4335077 := bbase (se 4 (by rfl) ⟨406413, by rfl⟩ : syracuseStep 4335077 = 812827) (by norm_num)
theorem B11560205 : Blo 2221435 11560205 := bstep (se 3 (by rfl) ⟨2167538, by rfl⟩ : syracuseStep 11560205 = 4335077) B4335077
theorem B7706803 : Blo 2221435 7706803 := bstep (se 1 (by rfl) ⟨5780102, by rfl⟩ : syracuseStep 7706803 = 11560205) B11560205
theorem B10275737 : Blo 2221435 10275737 := bstep (se 2 (by rfl) ⟨3853401, by rfl⟩ : syracuseStep 10275737 = 7706803) B7706803
theorem B109607861 : Blo 2221435 109607861 := bstep (se 5 (by rfl) ⟨5137868, by rfl⟩ : syracuseStep 109607861 = 10275737) B10275737
theorem B292287629 : Blo 2221435 292287629 := bstep (se 3 (by rfl) ⟨54803930, by rfl⟩ : syracuseStep 292287629 = 109607861) B109607861
theorem B194858419 : Blo 2221435 194858419 := bstep (se 1 (by rfl) ⟨146143814, by rfl⟩ : syracuseStep 194858419 = 292287629) B292287629
theorem B259811225 : Blo 2221435 259811225 := bstep (se 2 (by rfl) ⟨97429209, by rfl⟩ : syracuseStep 259811225 = 194858419) B194858419
theorem B173207483 : Blo 2221435 173207483 := bstep (se 1 (by rfl) ⟨129905612, by rfl⟩ : syracuseStep 173207483 = 259811225) B259811225
theorem B115471655 : Blo 2221435 115471655 := bstep (se 1 (by rfl) ⟨86603741, by rfl⟩ : syracuseStep 115471655 = 173207483) B173207483
theorem B76981103 : Blo 2221435 76981103 := bstep (se 1 (by rfl) ⟨57735827, by rfl⟩ : syracuseStep 76981103 = 115471655) B115471655
theorem B51320735 : Blo 2221435 51320735 := bstep (se 1 (by rfl) ⟨38490551, by rfl⟩ : syracuseStep 51320735 = 76981103) B76981103
theorem B34213823 : Blo 2221435 34213823 := bstep (se 1 (by rfl) ⟨25660367, by rfl⟩ : syracuseStep 34213823 = 51320735) B51320735
theorem B22809215 : Blo 2221435 22809215 := bstep (se 1 (by rfl) ⟨17106911, by rfl⟩ : syracuseStep 22809215 = 34213823) B34213823
theorem B15206143 : Blo 2221435 15206143 := bstep (se 1 (by rfl) ⟨11404607, by rfl⟩ : syracuseStep 15206143 = 22809215) B22809215
theorem B20274857 : Blo 2221435 20274857 := bstep (se 2 (by rfl) ⟨7603071, by rfl⟩ : syracuseStep 20274857 = 15206143) B15206143
theorem B13516571 : Blo 2221435 13516571 := bstep (se 1 (by rfl) ⟨10137428, by rfl⟩ : syracuseStep 13516571 = 20274857) B20274857
theorem B36044189 : Blo 2221435 36044189 := bstep (se 3 (by rfl) ⟨6758285, by rfl⟩ : syracuseStep 36044189 = 13516571) B13516571
theorem B24029459 : Blo 2221435 24029459 := bstep (se 1 (by rfl) ⟨18022094, by rfl⟩ : syracuseStep 24029459 = 36044189) B36044189
theorem B16019639 : Blo 2221435 16019639 := bstep (se 1 (by rfl) ⟨12014729, by rfl⟩ : syracuseStep 16019639 = 24029459) B24029459
theorem B10679759 : Blo 2221435 10679759 := bstep (se 1 (by rfl) ⟨8009819, by rfl⟩ : syracuseStep 10679759 = 16019639) B16019639
theorem B7119839 : Blo 2221435 7119839 := bstep (se 1 (by rfl) ⟨5339879, by rfl⟩ : syracuseStep 7119839 = 10679759) B10679759
theorem B18986237 : Blo 2221435 18986237 := bstep (se 3 (by rfl) ⟨3559919, by rfl⟩ : syracuseStep 18986237 = 7119839) B7119839
theorem B12657491 : Blo 2221435 12657491 := bstep (se 1 (by rfl) ⟨9493118, by rfl⟩ : syracuseStep 12657491 = 18986237) B18986237
theorem B8438327 : Blo 2221435 8438327 := bstep (se 1 (by rfl) ⟨6328745, by rfl⟩ : syracuseStep 8438327 = 12657491) B12657491
theorem B5625551 : Blo 2221435 5625551 := bstep (se 1 (by rfl) ⟨4219163, by rfl⟩ : syracuseStep 5625551 = 8438327) B8438327
theorem B3750367 : Blo 2221435 3750367 := bstep (se 1 (by rfl) ⟨2812775, by rfl⟩ : syracuseStep 3750367 = 5625551) B5625551
theorem B5000489 : Blo 2221435 5000489 := bstep (se 2 (by rfl) ⟨1875183, by rfl⟩ : syracuseStep 5000489 = 3750367) B3750367
theorem B3333659 : Blo 2221435 3333659 := bstep (se 1 (by rfl) ⟨2500244, by rfl⟩ : syracuseStep 3333659 = 5000489) B5000489
theorem B2222439 : Blo 2221435 2222439 := bstep (se 1 (by rfl) ⟨1666829, by rfl⟩ : syracuseStep 2222439 = 3333659) B3333659
theorem B2500249 : Blo 2221435 2500249 := bbase (se 2 (by rfl) ⟨937593, by rfl⟩ : syracuseStep 2500249 = 1875187) (by norm_num)
theorem B3333665 : Blo 2221435 3333665 := bstep (se 2 (by rfl) ⟨1250124, by rfl⟩ : syracuseStep 3333665 = 2500249) B2500249
theorem B2222443 : Blo 2221435 2222443 := bstep (se 1 (by rfl) ⟨1666832, by rfl⟩ : syracuseStep 2222443 = 3333665) B3333665
theorem B8438357 : Blo 2221435 8438357 := bbase (se 8 (by rfl) ⟨49443, by rfl⟩ : syracuseStep 8438357 = 98887) (by norm_num)
theorem B5625571 : Blo 2221435 5625571 := bstep (se 1 (by rfl) ⟨4219178, by rfl⟩ : syracuseStep 5625571 = 8438357) B8438357
theorem B7500761 : Blo 2221435 7500761 := bstep (se 2 (by rfl) ⟨2812785, by rfl⟩ : syracuseStep 7500761 = 5625571) B5625571
theorem B5000507 : Blo 2221435 5000507 := bstep (se 1 (by rfl) ⟨3750380, by rfl⟩ : syracuseStep 5000507 = 7500761) B7500761
theorem B3333671 : Blo 2221435 3333671 := bstep (se 1 (by rfl) ⟨2500253, by rfl⟩ : syracuseStep 3333671 = 5000507) B5000507
theorem B2222447 : Blo 2221435 2222447 := bstep (se 1 (by rfl) ⟨1666835, by rfl⟩ : syracuseStep 2222447 = 3333671) B3333671
theorem B3333677 : Blo 2221435 3333677 := bbase (se 3 (by rfl) ⟨625064, by rfl⟩ : syracuseStep 3333677 = 1250129) (by norm_num)
theorem B2222451 : Blo 2221435 2222451 := bstep (se 1 (by rfl) ⟨1666838, by rfl⟩ : syracuseStep 2222451 = 3333677) B3333677
theorem B5000525 : Blo 2221435 5000525 := bbase (se 3 (by rfl) ⟨937598, by rfl⟩ : syracuseStep 5000525 = 1875197) (by norm_num)
theorem B3333683 : Blo 2221435 3333683 := bstep (se 1 (by rfl) ⟨2500262, by rfl⟩ : syracuseStep 3333683 = 5000525) B5000525
theorem B2222455 : Blo 2221435 2222455 := bstep (se 1 (by rfl) ⟨1666841, by rfl⟩ : syracuseStep 2222455 = 3333683) B3333683
theorem B2812801 : Blo 2221435 2812801 := bbase (se 2 (by rfl) ⟨1054800, by rfl⟩ : syracuseStep 2812801 = 2109601) (by norm_num)
theorem B3750401 : Blo 2221435 3750401 := bstep (se 2 (by rfl) ⟨1406400, by rfl⟩ : syracuseStep 3750401 = 2812801) B2812801
theorem B2500267 : Blo 2221435 2500267 := bstep (se 1 (by rfl) ⟨1875200, by rfl⟩ : syracuseStep 2500267 = 3750401) B3750401
theorem B3333689 : Blo 2221435 3333689 := bstep (se 2 (by rfl) ⟨1250133, by rfl⟩ : syracuseStep 3333689 = 2500267) B2500267
theorem B2222459 : Blo 2221435 2222459 := bstep (se 1 (by rfl) ⟨1666844, by rfl⟩ : syracuseStep 2222459 = 3333689) B3333689
theorem B2373305 : Blo 2221435 2373305 := bbase (se 2 (by rfl) ⟨889989, by rfl⟩ : syracuseStep 2373305 = 1779979) (by norm_num)
theorem B25315253 : Blo 2221435 25315253 := bstep (se 5 (by rfl) ⟨1186652, by rfl⟩ : syracuseStep 25315253 = 2373305) B2373305
theorem B16876835 : Blo 2221435 16876835 := bstep (se 1 (by rfl) ⟨12657626, by rfl⟩ : syracuseStep 16876835 = 25315253) B25315253
theorem B11251223 : Blo 2221435 11251223 := bstep (se 1 (by rfl) ⟨8438417, by rfl⟩ : syracuseStep 11251223 = 16876835) B16876835
theorem B7500815 : Blo 2221435 7500815 := bstep (se 1 (by rfl) ⟨5625611, by rfl⟩ : syracuseStep 7500815 = 11251223) B11251223
theorem B5000543 : Blo 2221435 5000543 := bstep (se 1 (by rfl) ⟨3750407, by rfl⟩ : syracuseStep 5000543 = 7500815) B7500815
theorem B3333695 : Blo 2221435 3333695 := bstep (se 1 (by rfl) ⟨2500271, by rfl⟩ : syracuseStep 3333695 = 5000543) B5000543
theorem B2222463 : Blo 2221435 2222463 := bstep (se 1 (by rfl) ⟨1666847, by rfl⟩ : syracuseStep 2222463 = 3333695) B3333695
theorem B3333701 : Blo 2221435 3333701 := bbase (se 4 (by rfl) ⟨312534, by rfl⟩ : syracuseStep 3333701 = 625069) (by norm_num)
theorem B2222467 : Blo 2221435 2222467 := bstep (se 1 (by rfl) ⟨1666850, by rfl⟩ : syracuseStep 2222467 = 3333701) B3333701
theorem B3750421 : Blo 2221435 3750421 := bbase (se 6 (by rfl) ⟨87900, by rfl⟩ : syracuseStep 3750421 = 175801) (by norm_num)
theorem B5000561 : Blo 2221435 5000561 := bstep (se 2 (by rfl) ⟨1875210, by rfl⟩ : syracuseStep 5000561 = 3750421) B3750421
theorem B3333707 : Blo 2221435 3333707 := bstep (se 1 (by rfl) ⟨2500280, by rfl⟩ : syracuseStep 3333707 = 5000561) B5000561
theorem B2222471 : Blo 2221435 2222471 := bstep (se 1 (by rfl) ⟨1666853, by rfl⟩ : syracuseStep 2222471 = 3333707) B3333707
theorem B2500285 : Blo 2221435 2500285 := bbase (se 3 (by rfl) ⟨468803, by rfl⟩ : syracuseStep 2500285 = 937607) (by norm_num)
theorem B3333713 : Blo 2221435 3333713 := bstep (se 2 (by rfl) ⟨1250142, by rfl⟩ : syracuseStep 3333713 = 2500285) B2500285
theorem B2222475 : Blo 2221435 2222475 := bstep (se 1 (by rfl) ⟨1666856, by rfl⟩ : syracuseStep 2222475 = 3333713) B3333713
theorem B7500869 : Blo 2221435 7500869 := bbase (se 4 (by rfl) ⟨703206, by rfl⟩ : syracuseStep 7500869 = 1406413) (by norm_num)
theorem B5000579 : Blo 2221435 5000579 := bstep (se 1 (by rfl) ⟨3750434, by rfl⟩ : syracuseStep 5000579 = 7500869) B7500869
theorem B3333719 : Blo 2221435 3333719 := bstep (se 1 (by rfl) ⟨2500289, by rfl⟩ : syracuseStep 3333719 = 5000579) B5000579
theorem B2222479 : Blo 2221435 2222479 := bstep (se 1 (by rfl) ⟨1666859, by rfl⟩ : syracuseStep 2222479 = 3333719) B3333719
theorem B3333725 : Blo 2221435 3333725 := bbase (se 3 (by rfl) ⟨625073, by rfl⟩ : syracuseStep 3333725 = 1250147) (by norm_num)
theorem B2222483 : Blo 2221435 2222483 := bstep (se 1 (by rfl) ⟨1666862, by rfl⟩ : syracuseStep 2222483 = 3333725) B3333725
theorem B5000597 : Blo 2221435 5000597 := bbase (se 6 (by rfl) ⟨117201, by rfl⟩ : syracuseStep 5000597 = 234403) (by norm_num)
theorem B3333731 : Blo 2221435 3333731 := bstep (se 1 (by rfl) ⟨2500298, by rfl⟩ : syracuseStep 3333731 = 5000597) B5000597
theorem B2222487 : Blo 2221435 2222487 := bstep (se 1 (by rfl) ⟨1666865, by rfl⟩ : syracuseStep 2222487 = 3333731) B3333731
theorem B7603253 : Blo 2221435 7603253 := bbase (se 5 (by rfl) ⟨356402, by rfl⟩ : syracuseStep 7603253 = 712805) (by norm_num)
theorem B5068835 : Blo 2221435 5068835 := bstep (se 1 (by rfl) ⟨3801626, by rfl⟩ : syracuseStep 5068835 = 7603253) B7603253
theorem B3379223 : Blo 2221435 3379223 := bstep (se 1 (by rfl) ⟨2534417, by rfl⟩ : syracuseStep 3379223 = 5068835) B5068835
theorem B2252815 : Blo 2221435 2252815 := bstep (se 1 (by rfl) ⟨1689611, by rfl⟩ : syracuseStep 2252815 = 3379223) B3379223
theorem B12015013 : Blo 2221435 12015013 := bstep (se 4 (by rfl) ⟨1126407, by rfl⟩ : syracuseStep 12015013 = 2252815) B2252815
theorem B16020017 : Blo 2221435 16020017 := bstep (se 2 (by rfl) ⟨6007506, by rfl⟩ : syracuseStep 16020017 = 12015013) B12015013
theorem B10680011 : Blo 2221435 10680011 := bstep (se 1 (by rfl) ⟨8010008, by rfl⟩ : syracuseStep 10680011 = 16020017) B16020017
theorem B7120007 : Blo 2221435 7120007 := bstep (se 1 (by rfl) ⟨5340005, by rfl⟩ : syracuseStep 7120007 = 10680011) B10680011
theorem B4746671 : Blo 2221435 4746671 := bstep (se 1 (by rfl) ⟨3560003, by rfl⟩ : syracuseStep 4746671 = 7120007) B7120007
theorem B3164447 : Blo 2221435 3164447 := bstep (se 1 (by rfl) ⟨2373335, by rfl⟩ : syracuseStep 3164447 = 4746671) B4746671
theorem B8438525 : Blo 2221435 8438525 := bstep (se 3 (by rfl) ⟨1582223, by rfl⟩ : syracuseStep 8438525 = 3164447) B3164447
theorem B5625683 : Blo 2221435 5625683 := bstep (se 1 (by rfl) ⟨4219262, by rfl⟩ : syracuseStep 5625683 = 8438525) B8438525
theorem B3750455 : Blo 2221435 3750455 := bstep (se 1 (by rfl) ⟨2812841, by rfl⟩ : syracuseStep 3750455 = 5625683) B5625683
theorem B2500303 : Blo 2221435 2500303 := bstep (se 1 (by rfl) ⟨1875227, by rfl⟩ : syracuseStep 2500303 = 3750455) B3750455
theorem B3333737 : Blo 2221435 3333737 := bstep (se 2 (by rfl) ⟨1250151, by rfl⟩ : syracuseStep 3333737 = 2500303) B2500303
theorem B2222491 : Blo 2221435 2222491 := bstep (se 1 (by rfl) ⟨1666868, by rfl⟩ : syracuseStep 2222491 = 3333737) B3333737
theorem B3379229 : Blo 2221435 3379229 := bbase (se 3 (by rfl) ⟨633605, by rfl⟩ : syracuseStep 3379229 = 1267211) (by norm_num)
theorem B2252819 : Blo 2221435 2252819 := bstep (se 1 (by rfl) ⟨1689614, by rfl⟩ : syracuseStep 2252819 = 3379229) B3379229
theorem B6007517 : Blo 2221435 6007517 := bstep (se 3 (by rfl) ⟨1126409, by rfl⟩ : syracuseStep 6007517 = 2252819) B2252819
theorem B4005011 : Blo 2221435 4005011 := bstep (se 1 (by rfl) ⟨3003758, by rfl⟩ : syracuseStep 4005011 = 6007517) B6007517
theorem B2670007 : Blo 2221435 2670007 := bstep (se 1 (by rfl) ⟨2002505, by rfl⟩ : syracuseStep 2670007 = 4005011) B4005011
theorem B3560009 : Blo 2221435 3560009 := bstep (se 2 (by rfl) ⟨1335003, by rfl⟩ : syracuseStep 3560009 = 2670007) B2670007
theorem B9493357 : Blo 2221435 9493357 := bstep (se 3 (by rfl) ⟨1780004, by rfl⟩ : syracuseStep 9493357 = 3560009) B3560009
theorem B12657809 : Blo 2221435 12657809 := bstep (se 2 (by rfl) ⟨4746678, by rfl⟩ : syracuseStep 12657809 = 9493357) B9493357
theorem B8438539 : Blo 2221435 8438539 := bstep (se 1 (by rfl) ⟨6328904, by rfl⟩ : syracuseStep 8438539 = 12657809) B12657809
theorem B11251385 : Blo 2221435 11251385 := bstep (se 2 (by rfl) ⟨4219269, by rfl⟩ : syracuseStep 11251385 = 8438539) B8438539
theorem B7500923 : Blo 2221435 7500923 := bstep (se 1 (by rfl) ⟨5625692, by rfl⟩ : syracuseStep 7500923 = 11251385) B11251385
theorem B5000615 : Blo 2221435 5000615 := bstep (se 1 (by rfl) ⟨3750461, by rfl⟩ : syracuseStep 5000615 = 7500923) B7500923
theorem B3333743 : Blo 2221435 3333743 := bstep (se 1 (by rfl) ⟨2500307, by rfl⟩ : syracuseStep 3333743 = 5000615) B5000615
theorem B2222495 : Blo 2221435 2222495 := bstep (se 1 (by rfl) ⟨1666871, by rfl⟩ : syracuseStep 2222495 = 3333743) B3333743
theorem B3333749 : Blo 2221435 3333749 := bbase (se 5 (by rfl) ⟨156269, by rfl⟩ : syracuseStep 3333749 = 312539) (by norm_num)
theorem B2222499 : Blo 2221435 2222499 := bstep (se 1 (by rfl) ⟨1666874, by rfl⟩ : syracuseStep 2222499 = 3333749) B3333749
theorem B4219285 : Blo 2221435 4219285 := bbase (se 6 (by rfl) ⟨98889, by rfl⟩ : syracuseStep 4219285 = 197779) (by norm_num)
theorem B5625713 : Blo 2221435 5625713 := bstep (se 2 (by rfl) ⟨2109642, by rfl⟩ : syracuseStep 5625713 = 4219285) B4219285
theorem B3750475 : Blo 2221435 3750475 := bstep (se 1 (by rfl) ⟨2812856, by rfl⟩ : syracuseStep 3750475 = 5625713) B5625713
theorem B5000633 : Blo 2221435 5000633 := bstep (se 2 (by rfl) ⟨1875237, by rfl⟩ : syracuseStep 5000633 = 3750475) B3750475
theorem B3333755 : Blo 2221435 3333755 := bstep (se 1 (by rfl) ⟨2500316, by rfl⟩ : syracuseStep 3333755 = 5000633) B5000633
theorem B2222503 : Blo 2221435 2222503 := bstep (se 1 (by rfl) ⟨1666877, by rfl⟩ : syracuseStep 2222503 = 3333755) B3333755
theorem B2500321 : Blo 2221435 2500321 := bbase (se 2 (by rfl) ⟨937620, by rfl⟩ : syracuseStep 2500321 = 1875241) (by norm_num)
theorem B3333761 : Blo 2221435 3333761 := bstep (se 2 (by rfl) ⟨1250160, by rfl⟩ : syracuseStep 3333761 = 2500321) B2500321
theorem B2222507 : Blo 2221435 2222507 := bstep (se 1 (by rfl) ⟨1666880, by rfl⟩ : syracuseStep 2222507 = 3333761) B3333761
theorem B5625733 : Blo 2221435 5625733 := bbase (se 4 (by rfl) ⟨527412, by rfl⟩ : syracuseStep 5625733 = 1054825) (by norm_num)
theorem B7500977 : Blo 2221435 7500977 := bstep (se 2 (by rfl) ⟨2812866, by rfl⟩ : syracuseStep 7500977 = 5625733) B5625733
theorem B5000651 : Blo 2221435 5000651 := bstep (se 1 (by rfl) ⟨3750488, by rfl⟩ : syracuseStep 5000651 = 7500977) B7500977
theorem B3333767 : Blo 2221435 3333767 := bstep (se 1 (by rfl) ⟨2500325, by rfl⟩ : syracuseStep 3333767 = 5000651) B5000651
theorem B2222511 : Blo 2221435 2222511 := bstep (se 1 (by rfl) ⟨1666883, by rfl⟩ : syracuseStep 2222511 = 3333767) B3333767
theorem B3333773 : Blo 2221435 3333773 := bbase (se 3 (by rfl) ⟨625082, by rfl⟩ : syracuseStep 3333773 = 1250165) (by norm_num)
theorem B2222515 : Blo 2221435 2222515 := bstep (se 1 (by rfl) ⟨1666886, by rfl⟩ : syracuseStep 2222515 = 3333773) B3333773
theorem B5000669 : Blo 2221435 5000669 := bbase (se 3 (by rfl) ⟨937625, by rfl⟩ : syracuseStep 5000669 = 1875251) (by norm_num)
theorem B3333779 : Blo 2221435 3333779 := bstep (se 1 (by rfl) ⟨2500334, by rfl⟩ : syracuseStep 3333779 = 5000669) B5000669
theorem B2222519 : Blo 2221435 2222519 := bstep (se 1 (by rfl) ⟨1666889, by rfl⟩ : syracuseStep 2222519 = 3333779) B3333779
theorem B3750509 : Blo 2221435 3750509 := bbase (se 3 (by rfl) ⟨703220, by rfl⟩ : syracuseStep 3750509 = 1406441) (by norm_num)
theorem B2500339 : Blo 2221435 2500339 := bstep (se 1 (by rfl) ⟨1875254, by rfl⟩ : syracuseStep 2500339 = 3750509) B3750509
theorem B3333785 : Blo 2221435 3333785 := bstep (se 2 (by rfl) ⟨1250169, by rfl⟩ : syracuseStep 3333785 = 2500339) B2500339
theorem B2222523 : Blo 2221435 2222523 := bstep (se 1 (by rfl) ⟨1666892, by rfl⟩ : syracuseStep 2222523 = 3333785) B3333785
theorem B4811509 : Blo 2221435 4811509 := bbase (se 5 (by rfl) ⟨225539, by rfl⟩ : syracuseStep 4811509 = 451079) (by norm_num)
theorem B6415345 : Blo 2221435 6415345 := bstep (se 2 (by rfl) ⟨2405754, by rfl⟩ : syracuseStep 6415345 = 4811509) B4811509
theorem B8553793 : Blo 2221435 8553793 := bstep (se 2 (by rfl) ⟨3207672, by rfl⟩ : syracuseStep 8553793 = 6415345) B6415345
theorem B11405057 : Blo 2221435 11405057 := bstep (se 2 (by rfl) ⟨4276896, by rfl⟩ : syracuseStep 11405057 = 8553793) B8553793
theorem B30413485 : Blo 2221435 30413485 := bstep (se 3 (by rfl) ⟨5702528, by rfl⟩ : syracuseStep 30413485 = 11405057) B11405057
theorem B40551313 : Blo 2221435 40551313 := bstep (se 2 (by rfl) ⟨15206742, by rfl⟩ : syracuseStep 40551313 = 30413485) B30413485
theorem B54068417 : Blo 2221435 54068417 := bstep (se 2 (by rfl) ⟨20275656, by rfl⟩ : syracuseStep 54068417 = 40551313) B40551313
theorem B36045611 : Blo 2221435 36045611 := bstep (se 1 (by rfl) ⟨27034208, by rfl⟩ : syracuseStep 36045611 = 54068417) B54068417
theorem B24030407 : Blo 2221435 24030407 := bstep (se 1 (by rfl) ⟨18022805, by rfl⟩ : syracuseStep 24030407 = 36045611) B36045611
theorem B16020271 : Blo 2221435 16020271 := bstep (se 1 (by rfl) ⟨12015203, by rfl⟩ : syracuseStep 16020271 = 24030407) B24030407
theorem B21360361 : Blo 2221435 21360361 := bstep (se 2 (by rfl) ⟨8010135, by rfl⟩ : syracuseStep 21360361 = 16020271) B16020271
theorem B28480481 : Blo 2221435 28480481 := bstep (se 2 (by rfl) ⟨10680180, by rfl⟩ : syracuseStep 28480481 = 21360361) B21360361
theorem B18986987 : Blo 2221435 18986987 := bstep (se 1 (by rfl) ⟨14240240, by rfl⟩ : syracuseStep 18986987 = 28480481) B28480481
theorem B12657991 : Blo 2221435 12657991 := bstep (se 1 (by rfl) ⟨9493493, by rfl⟩ : syracuseStep 12657991 = 18986987) B18986987
theorem B16877321 : Blo 2221435 16877321 := bstep (se 2 (by rfl) ⟨6328995, by rfl⟩ : syracuseStep 16877321 = 12657991) B12657991
theorem B11251547 : Blo 2221435 11251547 := bstep (se 1 (by rfl) ⟨8438660, by rfl⟩ : syracuseStep 11251547 = 16877321) B16877321
theorem B7501031 : Blo 2221435 7501031 := bstep (se 1 (by rfl) ⟨5625773, by rfl⟩ : syracuseStep 7501031 = 11251547) B11251547
theorem B5000687 : Blo 2221435 5000687 := bstep (se 1 (by rfl) ⟨3750515, by rfl⟩ : syracuseStep 5000687 = 7501031) B7501031
theorem B3333791 : Blo 2221435 3333791 := bstep (se 1 (by rfl) ⟨2500343, by rfl⟩ : syracuseStep 3333791 = 5000687) B5000687
theorem B2222527 : Blo 2221435 2222527 := bstep (se 1 (by rfl) ⟨1666895, by rfl⟩ : syracuseStep 2222527 = 3333791) B3333791
theorem B3333797 : Blo 2221435 3333797 := bbase (se 4 (by rfl) ⟨312543, by rfl⟩ : syracuseStep 3333797 = 625087) (by norm_num)
theorem B2222531 : Blo 2221435 2222531 := bstep (se 1 (by rfl) ⟨1666898, by rfl⟩ : syracuseStep 2222531 = 3333797) B3333797
theorem B2812897 : Blo 2221435 2812897 := bbase (se 2 (by rfl) ⟨1054836, by rfl⟩ : syracuseStep 2812897 = 2109673) (by norm_num)
theorem B3750529 : Blo 2221435 3750529 := bstep (se 2 (by rfl) ⟨1406448, by rfl⟩ : syracuseStep 3750529 = 2812897) B2812897
theorem B5000705 : Blo 2221435 5000705 := bstep (se 2 (by rfl) ⟨1875264, by rfl⟩ : syracuseStep 5000705 = 3750529) B3750529
theorem B3333803 : Blo 2221435 3333803 := bstep (se 1 (by rfl) ⟨2500352, by rfl⟩ : syracuseStep 3333803 = 5000705) B5000705
theorem B2222535 : Blo 2221435 2222535 := bstep (se 1 (by rfl) ⟨1666901, by rfl⟩ : syracuseStep 2222535 = 3333803) B3333803
theorem B2500357 : Blo 2221435 2500357 := bbase (se 4 (by rfl) ⟨234408, by rfl⟩ : syracuseStep 2500357 = 468817) (by norm_num)
theorem B3333809 : Blo 2221435 3333809 := bstep (se 2 (by rfl) ⟨1250178, by rfl⟩ : syracuseStep 3333809 = 2500357) B2500357
theorem B2222539 : Blo 2221435 2222539 := bstep (se 1 (by rfl) ⟨1666904, by rfl⟩ : syracuseStep 2222539 = 3333809) B3333809
theorem B8010197 : Blo 2221435 8010197 := bbase (se 7 (by rfl) ⟨93869, by rfl⟩ : syracuseStep 8010197 = 187739) (by norm_num)
theorem B5340131 : Blo 2221435 5340131 := bstep (se 1 (by rfl) ⟨4005098, by rfl⟩ : syracuseStep 5340131 = 8010197) B8010197
theorem B3560087 : Blo 2221435 3560087 := bstep (se 1 (by rfl) ⟨2670065, by rfl⟩ : syracuseStep 3560087 = 5340131) B5340131
theorem B2373391 : Blo 2221435 2373391 := bstep (se 1 (by rfl) ⟨1780043, by rfl⟩ : syracuseStep 2373391 = 3560087) B3560087
theorem B3164521 : Blo 2221435 3164521 := bstep (se 2 (by rfl) ⟨1186695, by rfl⟩ : syracuseStep 3164521 = 2373391) B2373391
theorem B4219361 : Blo 2221435 4219361 := bstep (se 2 (by rfl) ⟨1582260, by rfl⟩ : syracuseStep 4219361 = 3164521) B3164521
theorem B2812907 : Blo 2221435 2812907 := bstep (se 1 (by rfl) ⟨2109680, by rfl⟩ : syracuseStep 2812907 = 4219361) B4219361
theorem B7501085 : Blo 2221435 7501085 := bstep (se 3 (by rfl) ⟨1406453, by rfl⟩ : syracuseStep 7501085 = 2812907) B2812907
theorem B5000723 : Blo 2221435 5000723 := bstep (se 1 (by rfl) ⟨3750542, by rfl⟩ : syracuseStep 5000723 = 7501085) B7501085
theorem B3333815 : Blo 2221435 3333815 := bstep (se 1 (by rfl) ⟨2500361, by rfl⟩ : syracuseStep 3333815 = 5000723) B5000723
theorem B2222543 : Blo 2221435 2222543 := bstep (se 1 (by rfl) ⟨1666907, by rfl⟩ : syracuseStep 2222543 = 3333815) B3333815
theorem B3333821 : Blo 2221435 3333821 := bbase (se 3 (by rfl) ⟨625091, by rfl⟩ : syracuseStep 3333821 = 1250183) (by norm_num)
theorem B2222547 : Blo 2221435 2222547 := bstep (se 1 (by rfl) ⟨1666910, by rfl⟩ : syracuseStep 2222547 = 3333821) B3333821
theorem B5000741 : Blo 2221435 5000741 := bbase (se 4 (by rfl) ⟨468819, by rfl⟩ : syracuseStep 5000741 = 937639) (by norm_num)
theorem B3333827 : Blo 2221435 3333827 := bstep (se 1 (by rfl) ⟨2500370, by rfl⟩ : syracuseStep 3333827 = 5000741) B5000741
theorem B2222551 : Blo 2221435 2222551 := bstep (se 1 (by rfl) ⟨1666913, by rfl⟩ : syracuseStep 2222551 = 3333827) B3333827
theorem B5625845 : Blo 2221435 5625845 := bbase (se 5 (by rfl) ⟨263711, by rfl⟩ : syracuseStep 5625845 = 527423) (by norm_num)
theorem B3750563 : Blo 2221435 3750563 := bstep (se 1 (by rfl) ⟨2812922, by rfl⟩ : syracuseStep 3750563 = 5625845) B5625845
theorem B2500375 : Blo 2221435 2500375 := bstep (se 1 (by rfl) ⟨1875281, by rfl⟩ : syracuseStep 2500375 = 3750563) B3750563
theorem B3333833 : Blo 2221435 3333833 := bstep (se 2 (by rfl) ⟨1250187, by rfl⟩ : syracuseStep 3333833 = 2500375) B2500375
theorem B2222555 : Blo 2221435 2222555 := bstep (se 1 (by rfl) ⟨1666916, by rfl⟩ : syracuseStep 2222555 = 3333833) B3333833
theorem B2569073 : Blo 2221435 2569073 := bbase (se 2 (by rfl) ⟨963402, by rfl⟩ : syracuseStep 2569073 = 1926805) (by norm_num)
theorem B6850861 : Blo 2221435 6850861 := bstep (se 3 (by rfl) ⟨1284536, by rfl⟩ : syracuseStep 6850861 = 2569073) B2569073
theorem B36537925 : Blo 2221435 36537925 := bstep (se 4 (by rfl) ⟨3425430, by rfl⟩ : syracuseStep 36537925 = 6850861) B6850861
theorem B48717233 : Blo 2221435 48717233 := bstep (se 2 (by rfl) ⟨18268962, by rfl⟩ : syracuseStep 48717233 = 36537925) B36537925
theorem B32478155 : Blo 2221435 32478155 := bstep (se 1 (by rfl) ⟨24358616, by rfl⟩ : syracuseStep 32478155 = 48717233) B48717233
theorem B21652103 : Blo 2221435 21652103 := bstep (se 1 (by rfl) ⟨16239077, by rfl⟩ : syracuseStep 21652103 = 32478155) B32478155
theorem B14434735 : Blo 2221435 14434735 := bstep (se 1 (by rfl) ⟨10826051, by rfl⟩ : syracuseStep 14434735 = 21652103) B21652103
theorem B19246313 : Blo 2221435 19246313 := bstep (se 2 (by rfl) ⟨7217367, by rfl⟩ : syracuseStep 19246313 = 14434735) B14434735
theorem B12830875 : Blo 2221435 12830875 := bstep (se 1 (by rfl) ⟨9623156, by rfl⟩ : syracuseStep 12830875 = 19246313) B19246313
theorem B68431333 : Blo 2221435 68431333 := bstep (se 4 (by rfl) ⟨6415437, by rfl⟩ : syracuseStep 68431333 = 12830875) B12830875
theorem B91241777 : Blo 2221435 91241777 := bstep (se 2 (by rfl) ⟨34215666, by rfl⟩ : syracuseStep 91241777 = 68431333) B68431333
theorem B60827851 : Blo 2221435 60827851 := bstep (se 1 (by rfl) ⟨45620888, by rfl⟩ : syracuseStep 60827851 = 91241777) B91241777
theorem B81103801 : Blo 2221435 81103801 := bstep (se 2 (by rfl) ⟨30413925, by rfl⟩ : syracuseStep 81103801 = 60827851) B60827851
theorem B108138401 : Blo 2221435 108138401 := bstep (se 2 (by rfl) ⟨40551900, by rfl⟩ : syracuseStep 108138401 = 81103801) B81103801
theorem B72092267 : Blo 2221435 72092267 := bstep (se 1 (by rfl) ⟨54069200, by rfl⟩ : syracuseStep 72092267 = 108138401) B108138401
theorem B48061511 : Blo 2221435 48061511 := bstep (se 1 (by rfl) ⟨36046133, by rfl⟩ : syracuseStep 48061511 = 72092267) B72092267
theorem B32041007 : Blo 2221435 32041007 := bstep (se 1 (by rfl) ⟨24030755, by rfl⟩ : syracuseStep 32041007 = 48061511) B48061511
theorem B21360671 : Blo 2221435 21360671 := bstep (se 1 (by rfl) ⟨16020503, by rfl⟩ : syracuseStep 21360671 = 32041007) B32041007
theorem B14240447 : Blo 2221435 14240447 := bstep (se 1 (by rfl) ⟨10680335, by rfl⟩ : syracuseStep 14240447 = 21360671) B21360671
theorem B9493631 : Blo 2221435 9493631 := bstep (se 1 (by rfl) ⟨7120223, by rfl⟩ : syracuseStep 9493631 = 14240447) B14240447
theorem B6329087 : Blo 2221435 6329087 := bstep (se 1 (by rfl) ⟨4746815, by rfl⟩ : syracuseStep 6329087 = 9493631) B9493631
theorem B4219391 : Blo 2221435 4219391 := bstep (se 1 (by rfl) ⟨3164543, by rfl⟩ : syracuseStep 4219391 = 6329087) B6329087
theorem B11251709 : Blo 2221435 11251709 := bstep (se 3 (by rfl) ⟨2109695, by rfl⟩ : syracuseStep 11251709 = 4219391) B4219391
theorem B7501139 : Blo 2221435 7501139 := bstep (se 1 (by rfl) ⟨5625854, by rfl⟩ : syracuseStep 7501139 = 11251709) B11251709
theorem B5000759 : Blo 2221435 5000759 := bstep (se 1 (by rfl) ⟨3750569, by rfl⟩ : syracuseStep 5000759 = 7501139) B7501139
theorem B3333839 : Blo 2221435 3333839 := bstep (se 1 (by rfl) ⟨2500379, by rfl⟩ : syracuseStep 3333839 = 5000759) B5000759
theorem B2222559 : Blo 2221435 2222559 := bstep (se 1 (by rfl) ⟨1666919, by rfl⟩ : syracuseStep 2222559 = 3333839) B3333839
theorem B3333845 : Blo 2221435 3333845 := bbase (se 7 (by rfl) ⟨39068, by rfl⟩ : syracuseStep 3333845 = 78137) (by norm_num)
theorem B2222563 : Blo 2221435 2222563 := bstep (se 1 (by rfl) ⟨1666922, by rfl⟩ : syracuseStep 2222563 = 3333845) B3333845
theorem B3560125 : Blo 2221435 3560125 := bbase (se 3 (by rfl) ⟨667523, by rfl⟩ : syracuseStep 3560125 = 1335047) (by norm_num)
theorem B4746833 : Blo 2221435 4746833 := bstep (se 2 (by rfl) ⟨1780062, by rfl⟩ : syracuseStep 4746833 = 3560125) B3560125
theorem B3164555 : Blo 2221435 3164555 := bstep (se 1 (by rfl) ⟨2373416, by rfl⟩ : syracuseStep 3164555 = 4746833) B4746833
theorem B8438813 : Blo 2221435 8438813 := bstep (se 3 (by rfl) ⟨1582277, by rfl⟩ : syracuseStep 8438813 = 3164555) B3164555
theorem B5625875 : Blo 2221435 5625875 := bstep (se 1 (by rfl) ⟨4219406, by rfl⟩ : syracuseStep 5625875 = 8438813) B8438813
theorem B3750583 : Blo 2221435 3750583 := bstep (se 1 (by rfl) ⟨2812937, by rfl⟩ : syracuseStep 3750583 = 5625875) B5625875
theorem B5000777 : Blo 2221435 5000777 := bstep (se 2 (by rfl) ⟨1875291, by rfl⟩ : syracuseStep 5000777 = 3750583) B3750583
theorem B3333851 : Blo 2221435 3333851 := bstep (se 1 (by rfl) ⟨2500388, by rfl⟩ : syracuseStep 3333851 = 5000777) B5000777
theorem B2222567 : Blo 2221435 2222567 := bstep (se 1 (by rfl) ⟨1666925, by rfl⟩ : syracuseStep 2222567 = 3333851) B3333851
theorem B2500393 : Blo 2221435 2500393 := bbase (se 2 (by rfl) ⟨937647, by rfl⟩ : syracuseStep 2500393 = 1875295) (by norm_num)
theorem B3333857 : Blo 2221435 3333857 := bstep (se 2 (by rfl) ⟨1250196, by rfl⟩ : syracuseStep 3333857 = 2500393) B2500393
theorem B2222571 : Blo 2221435 2222571 := bstep (se 1 (by rfl) ⟨1666928, by rfl⟩ : syracuseStep 2222571 = 3333857) B3333857
theorem B6007733 : Blo 2221435 6007733 := bbase (se 5 (by rfl) ⟨281612, by rfl⟩ : syracuseStep 6007733 = 563225) (by norm_num)
theorem B4005155 : Blo 2221435 4005155 := bstep (se 1 (by rfl) ⟨3003866, by rfl⟩ : syracuseStep 4005155 = 6007733) B6007733
theorem B2670103 : Blo 2221435 2670103 := bstep (se 1 (by rfl) ⟨2002577, by rfl⟩ : syracuseStep 2670103 = 4005155) B4005155
theorem B14240549 : Blo 2221435 14240549 := bstep (se 4 (by rfl) ⟨1335051, by rfl⟩ : syracuseStep 14240549 = 2670103) B2670103
theorem B9493699 : Blo 2221435 9493699 := bstep (se 1 (by rfl) ⟨7120274, by rfl⟩ : syracuseStep 9493699 = 14240549) B14240549
theorem B12658265 : Blo 2221435 12658265 := bstep (se 2 (by rfl) ⟨4746849, by rfl⟩ : syracuseStep 12658265 = 9493699) B9493699
theorem B8438843 : Blo 2221435 8438843 := bstep (se 1 (by rfl) ⟨6329132, by rfl⟩ : syracuseStep 8438843 = 12658265) B12658265
theorem B5625895 : Blo 2221435 5625895 := bstep (se 1 (by rfl) ⟨4219421, by rfl⟩ : syracuseStep 5625895 = 8438843) B8438843
theorem B7501193 : Blo 2221435 7501193 := bstep (se 2 (by rfl) ⟨2812947, by rfl⟩ : syracuseStep 7501193 = 5625895) B5625895
theorem B5000795 : Blo 2221435 5000795 := bstep (se 1 (by rfl) ⟨3750596, by rfl⟩ : syracuseStep 5000795 = 7501193) B7501193
theorem B3333863 : Blo 2221435 3333863 := bstep (se 1 (by rfl) ⟨2500397, by rfl⟩ : syracuseStep 3333863 = 5000795) B5000795
theorem B2222575 : Blo 2221435 2222575 := bstep (se 1 (by rfl) ⟨1666931, by rfl⟩ : syracuseStep 2222575 = 3333863) B3333863
theorem B3333869 : Blo 2221435 3333869 := bbase (se 3 (by rfl) ⟨625100, by rfl⟩ : syracuseStep 3333869 = 1250201) (by norm_num)
theorem B2222579 : Blo 2221435 2222579 := bstep (se 1 (by rfl) ⟨1666934, by rfl⟩ : syracuseStep 2222579 = 3333869) B3333869
theorem B5000813 : Blo 2221435 5000813 := bbase (se 3 (by rfl) ⟨937652, by rfl⟩ : syracuseStep 5000813 = 1875305) (by norm_num)
theorem B3333875 : Blo 2221435 3333875 := bstep (se 1 (by rfl) ⟨2500406, by rfl⟩ : syracuseStep 3333875 = 5000813) B5000813
theorem B2222583 : Blo 2221435 2222583 := bstep (se 1 (by rfl) ⟨1666937, by rfl⟩ : syracuseStep 2222583 = 3333875) B3333875
theorem B4219445 : Blo 2221435 4219445 := bbase (se 5 (by rfl) ⟨197786, by rfl⟩ : syracuseStep 4219445 = 395573) (by norm_num)
theorem B2812963 : Blo 2221435 2812963 := bstep (se 1 (by rfl) ⟨2109722, by rfl⟩ : syracuseStep 2812963 = 4219445) B4219445
theorem B3750617 : Blo 2221435 3750617 := bstep (se 2 (by rfl) ⟨1406481, by rfl⟩ : syracuseStep 3750617 = 2812963) B2812963
theorem B2500411 : Blo 2221435 2500411 := bstep (se 1 (by rfl) ⟨1875308, by rfl⟩ : syracuseStep 2500411 = 3750617) B3750617
theorem B3333881 : Blo 2221435 3333881 := bstep (se 2 (by rfl) ⟨1250205, by rfl⟩ : syracuseStep 3333881 = 2500411) B2500411
theorem B2222587 : Blo 2221435 2222587 := bstep (se 1 (by rfl) ⟨1666940, by rfl⟩ : syracuseStep 2222587 = 3333881) B3333881
theorem B12345653 : Blo 2221435 12345653 := bbase (se 5 (by rfl) ⟨578702, by rfl⟩ : syracuseStep 12345653 = 1157405) (by norm_num)
theorem B32921741 : Blo 2221435 32921741 := bstep (se 3 (by rfl) ⟨6172826, by rfl⟩ : syracuseStep 32921741 = 12345653) B12345653
theorem B21947827 : Blo 2221435 21947827 := bstep (se 1 (by rfl) ⟨16460870, by rfl⟩ : syracuseStep 21947827 = 32921741) B32921741
theorem B29263769 : Blo 2221435 29263769 := bstep (se 2 (by rfl) ⟨10973913, by rfl⟩ : syracuseStep 29263769 = 21947827) B21947827
theorem B19509179 : Blo 2221435 19509179 := bstep (se 1 (by rfl) ⟨14631884, by rfl⟩ : syracuseStep 19509179 = 29263769) B29263769
theorem B52024477 : Blo 2221435 52024477 := bstep (se 3 (by rfl) ⟨9754589, by rfl⟩ : syracuseStep 52024477 = 19509179) B19509179
theorem B69365969 : Blo 2221435 69365969 := bstep (se 2 (by rfl) ⟨26012238, by rfl⟩ : syracuseStep 69365969 = 52024477) B52024477
theorem B46243979 : Blo 2221435 46243979 := bstep (se 1 (by rfl) ⟨34682984, by rfl⟩ : syracuseStep 46243979 = 69365969) B69365969
theorem B30829319 : Blo 2221435 30829319 := bstep (se 1 (by rfl) ⟨23121989, by rfl⟩ : syracuseStep 30829319 = 46243979) B46243979
theorem B20552879 : Blo 2221435 20552879 := bstep (se 1 (by rfl) ⟨15414659, by rfl⟩ : syracuseStep 20552879 = 30829319) B30829319
theorem B13701919 : Blo 2221435 13701919 := bstep (se 1 (by rfl) ⟨10276439, by rfl⟩ : syracuseStep 13701919 = 20552879) B20552879
theorem B18269225 : Blo 2221435 18269225 := bstep (se 2 (by rfl) ⟨6850959, by rfl⟩ : syracuseStep 18269225 = 13701919) B13701919
theorem B12179483 : Blo 2221435 12179483 := bstep (se 1 (by rfl) ⟨9134612, by rfl⟩ : syracuseStep 12179483 = 18269225) B18269225
theorem B8119655 : Blo 2221435 8119655 := bstep (se 1 (by rfl) ⟨6089741, by rfl⟩ : syracuseStep 8119655 = 12179483) B12179483
theorem B5413103 : Blo 2221435 5413103 := bstep (se 1 (by rfl) ⟨4059827, by rfl⟩ : syracuseStep 5413103 = 8119655) B8119655
theorem B3608735 : Blo 2221435 3608735 := bstep (se 1 (by rfl) ⟨2706551, by rfl⟩ : syracuseStep 3608735 = 5413103) B5413103
theorem B38493173 : Blo 2221435 38493173 := bstep (se 5 (by rfl) ⟨1804367, by rfl⟩ : syracuseStep 38493173 = 3608735) B3608735
theorem B25662115 : Blo 2221435 25662115 := bstep (se 1 (by rfl) ⟨19246586, by rfl⟩ : syracuseStep 25662115 = 38493173) B38493173
theorem B136864613 : Blo 2221435 136864613 := bstep (se 4 (by rfl) ⟨12831057, by rfl⟩ : syracuseStep 136864613 = 25662115) B25662115
theorem B364972301 : Blo 2221435 364972301 := bstep (se 3 (by rfl) ⟨68432306, by rfl⟩ : syracuseStep 364972301 = 136864613) B136864613
theorem B243314867 : Blo 2221435 243314867 := bstep (se 1 (by rfl) ⟨182486150, by rfl⟩ : syracuseStep 243314867 = 364972301) B364972301
theorem B162209911 : Blo 2221435 162209911 := bstep (se 1 (by rfl) ⟨121657433, by rfl⟩ : syracuseStep 162209911 = 243314867) B243314867
theorem B216279881 : Blo 2221435 216279881 := bstep (se 2 (by rfl) ⟨81104955, by rfl⟩ : syracuseStep 216279881 = 162209911) B162209911
theorem B144186587 : Blo 2221435 144186587 := bstep (se 1 (by rfl) ⟨108139940, by rfl⟩ : syracuseStep 144186587 = 216279881) B216279881
theorem B96124391 : Blo 2221435 96124391 := bstep (se 1 (by rfl) ⟨72093293, by rfl⟩ : syracuseStep 96124391 = 144186587) B144186587
theorem B64082927 : Blo 2221435 64082927 := bstep (se 1 (by rfl) ⟨48062195, by rfl⟩ : syracuseStep 64082927 = 96124391) B96124391
theorem B42721951 : Blo 2221435 42721951 := bstep (se 1 (by rfl) ⟨32041463, by rfl⟩ : syracuseStep 42721951 = 64082927) B64082927
theorem B56962601 : Blo 2221435 56962601 := bstep (se 2 (by rfl) ⟨21360975, by rfl⟩ : syracuseStep 56962601 = 42721951) B42721951
theorem B37975067 : Blo 2221435 37975067 := bstep (se 1 (by rfl) ⟨28481300, by rfl⟩ : syracuseStep 37975067 = 56962601) B56962601
theorem B25316711 : Blo 2221435 25316711 := bstep (se 1 (by rfl) ⟨18987533, by rfl⟩ : syracuseStep 25316711 = 37975067) B37975067
theorem B16877807 : Blo 2221435 16877807 := bstep (se 1 (by rfl) ⟨12658355, by rfl⟩ : syracuseStep 16877807 = 25316711) B25316711
theorem B11251871 : Blo 2221435 11251871 := bstep (se 1 (by rfl) ⟨8438903, by rfl⟩ : syracuseStep 11251871 = 16877807) B16877807
theorem B7501247 : Blo 2221435 7501247 := bstep (se 1 (by rfl) ⟨5625935, by rfl⟩ : syracuseStep 7501247 = 11251871) B11251871
theorem B5000831 : Blo 2221435 5000831 := bstep (se 1 (by rfl) ⟨3750623, by rfl⟩ : syracuseStep 5000831 = 7501247) B7501247
theorem B3333887 : Blo 2221435 3333887 := bstep (se 1 (by rfl) ⟨2500415, by rfl⟩ : syracuseStep 3333887 = 5000831) B5000831
theorem B2222591 : Blo 2221435 2222591 := bstep (se 1 (by rfl) ⟨1666943, by rfl⟩ : syracuseStep 2222591 = 3333887) B3333887
theorem B3333893 : Blo 2221435 3333893 := bbase (se 4 (by rfl) ⟨312552, by rfl⟩ : syracuseStep 3333893 = 625105) (by norm_num)
theorem B2222595 : Blo 2221435 2222595 := bstep (se 1 (by rfl) ⟨1666946, by rfl⟩ : syracuseStep 2222595 = 3333893) B3333893
theorem B3750637 : Blo 2221435 3750637 := bbase (se 3 (by rfl) ⟨703244, by rfl⟩ : syracuseStep 3750637 = 1406489) (by norm_num)
theorem B5000849 : Blo 2221435 5000849 := bstep (se 2 (by rfl) ⟨1875318, by rfl⟩ : syracuseStep 5000849 = 3750637) B3750637
theorem B3333899 : Blo 2221435 3333899 := bstep (se 1 (by rfl) ⟨2500424, by rfl⟩ : syracuseStep 3333899 = 5000849) B5000849
theorem B2222599 : Blo 2221435 2222599 := bstep (se 1 (by rfl) ⟨1666949, by rfl⟩ : syracuseStep 2222599 = 3333899) B3333899
theorem B2500429 : Blo 2221435 2500429 := bbase (se 3 (by rfl) ⟨468830, by rfl⟩ : syracuseStep 2500429 = 937661) (by norm_num)
theorem B3333905 : Blo 2221435 3333905 := bstep (se 2 (by rfl) ⟨1250214, by rfl⟩ : syracuseStep 3333905 = 2500429) B2500429
theorem B2222603 : Blo 2221435 2222603 := bstep (se 1 (by rfl) ⟨1666952, by rfl⟩ : syracuseStep 2222603 = 3333905) B3333905
theorem B7501301 : Blo 2221435 7501301 := bbase (se 5 (by rfl) ⟨351623, by rfl⟩ : syracuseStep 7501301 = 703247) (by norm_num)
theorem B5000867 : Blo 2221435 5000867 := bstep (se 1 (by rfl) ⟨3750650, by rfl⟩ : syracuseStep 5000867 = 7501301) B7501301
theorem B3333911 : Blo 2221435 3333911 := bstep (se 1 (by rfl) ⟨2500433, by rfl⟩ : syracuseStep 3333911 = 5000867) B5000867
theorem B2222607 : Blo 2221435 2222607 := bstep (se 1 (by rfl) ⟨1666955, by rfl⟩ : syracuseStep 2222607 = 3333911) B3333911
theorem B3333917 : Blo 2221435 3333917 := bbase (se 3 (by rfl) ⟨625109, by rfl⟩ : syracuseStep 3333917 = 1250219) (by norm_num)
theorem B2222611 : Blo 2221435 2222611 := bstep (se 1 (by rfl) ⟨1666958, by rfl⟩ : syracuseStep 2222611 = 3333917) B3333917
theorem B5000885 : Blo 2221435 5000885 := bbase (se 5 (by rfl) ⟨234416, by rfl⟩ : syracuseStep 5000885 = 468833) (by norm_num)
theorem B3333923 : Blo 2221435 3333923 := bstep (se 1 (by rfl) ⟨2500442, by rfl⟩ : syracuseStep 3333923 = 5000885) B5000885
theorem B2222615 : Blo 2221435 2222615 := bstep (se 1 (by rfl) ⟨1666961, by rfl⟩ : syracuseStep 2222615 = 3333923) B3333923
theorem B12658517 : Blo 2221435 12658517 := bbase (se 9 (by rfl) ⟨37085, by rfl⟩ : syracuseStep 12658517 = 74171) (by norm_num)
theorem B8439011 : Blo 2221435 8439011 := bstep (se 1 (by rfl) ⟨6329258, by rfl⟩ : syracuseStep 8439011 = 12658517) B12658517
theorem B5626007 : Blo 2221435 5626007 := bstep (se 1 (by rfl) ⟨4219505, by rfl⟩ : syracuseStep 5626007 = 8439011) B8439011
theorem B3750671 : Blo 2221435 3750671 := bstep (se 1 (by rfl) ⟨2813003, by rfl⟩ : syracuseStep 3750671 = 5626007) B5626007
theorem B2500447 : Blo 2221435 2500447 := bstep (se 1 (by rfl) ⟨1875335, by rfl⟩ : syracuseStep 2500447 = 3750671) B3750671
theorem B3333929 : Blo 2221435 3333929 := bstep (se 2 (by rfl) ⟨1250223, by rfl⟩ : syracuseStep 3333929 = 2500447) B2500447
theorem B2222619 : Blo 2221435 2222619 := bstep (se 1 (by rfl) ⟨1666964, by rfl⟩ : syracuseStep 2222619 = 3333929) B3333929
theorem B6329269 : Blo 2221435 6329269 := bbase (se 5 (by rfl) ⟨296684, by rfl⟩ : syracuseStep 6329269 = 593369) (by norm_num)
theorem B8439025 : Blo 2221435 8439025 := bstep (se 2 (by rfl) ⟨3164634, by rfl⟩ : syracuseStep 8439025 = 6329269) B6329269
theorem B11252033 : Blo 2221435 11252033 := bstep (se 2 (by rfl) ⟨4219512, by rfl⟩ : syracuseStep 11252033 = 8439025) B8439025
theorem B7501355 : Blo 2221435 7501355 := bstep (se 1 (by rfl) ⟨5626016, by rfl⟩ : syracuseStep 7501355 = 11252033) B11252033
theorem B5000903 : Blo 2221435 5000903 := bstep (se 1 (by rfl) ⟨3750677, by rfl⟩ : syracuseStep 5000903 = 7501355) B7501355
theorem B3333935 : Blo 2221435 3333935 := bstep (se 1 (by rfl) ⟨2500451, by rfl⟩ : syracuseStep 3333935 = 5000903) B5000903
theorem B2222623 : Blo 2221435 2222623 := bstep (se 1 (by rfl) ⟨1666967, by rfl⟩ : syracuseStep 2222623 = 3333935) B3333935
theorem B3333941 : Blo 2221435 3333941 := bbase (se 5 (by rfl) ⟨156278, by rfl⟩ : syracuseStep 3333941 = 312557) (by norm_num)
theorem B2222627 : Blo 2221435 2222627 := bstep (se 1 (by rfl) ⟨1666970, by rfl⟩ : syracuseStep 2222627 = 3333941) B3333941
theorem B5626037 : Blo 2221435 5626037 := bbase (se 5 (by rfl) ⟨263720, by rfl⟩ : syracuseStep 5626037 = 527441) (by norm_num)
theorem B3750691 : Blo 2221435 3750691 := bstep (se 1 (by rfl) ⟨2813018, by rfl⟩ : syracuseStep 3750691 = 5626037) B5626037
theorem B5000921 : Blo 2221435 5000921 := bstep (se 2 (by rfl) ⟨1875345, by rfl⟩ : syracuseStep 5000921 = 3750691) B3750691
theorem B3333947 : Blo 2221435 3333947 := bstep (se 1 (by rfl) ⟨2500460, by rfl⟩ : syracuseStep 3333947 = 5000921) B5000921
theorem B2222631 : Blo 2221435 2222631 := bstep (se 1 (by rfl) ⟨1666973, by rfl⟩ : syracuseStep 2222631 = 3333947) B3333947
theorem B2500465 : Blo 2221435 2500465 := bbase (se 2 (by rfl) ⟨937674, by rfl⟩ : syracuseStep 2500465 = 1875349) (by norm_num)
theorem B3333953 : Blo 2221435 3333953 := bstep (se 2 (by rfl) ⟨1250232, by rfl⟩ : syracuseStep 3333953 = 2500465) B2500465
theorem B2222635 : Blo 2221435 2222635 := bstep (se 1 (by rfl) ⟨1666976, by rfl⟩ : syracuseStep 2222635 = 3333953) B3333953
theorem B9493973 : Blo 2221435 9493973 := bbase (se 7 (by rfl) ⟨111257, by rfl⟩ : syracuseStep 9493973 = 222515) (by norm_num)
theorem B6329315 : Blo 2221435 6329315 := bstep (se 1 (by rfl) ⟨4746986, by rfl⟩ : syracuseStep 6329315 = 9493973) B9493973
theorem B4219543 : Blo 2221435 4219543 := bstep (se 1 (by rfl) ⟨3164657, by rfl⟩ : syracuseStep 4219543 = 6329315) B6329315
theorem B5626057 : Blo 2221435 5626057 := bstep (se 2 (by rfl) ⟨2109771, by rfl⟩ : syracuseStep 5626057 = 4219543) B4219543
theorem B7501409 : Blo 2221435 7501409 := bstep (se 2 (by rfl) ⟨2813028, by rfl⟩ : syracuseStep 7501409 = 5626057) B5626057
theorem B5000939 : Blo 2221435 5000939 := bstep (se 1 (by rfl) ⟨3750704, by rfl⟩ : syracuseStep 5000939 = 7501409) B7501409
theorem B3333959 : Blo 2221435 3333959 := bstep (se 1 (by rfl) ⟨2500469, by rfl⟩ : syracuseStep 3333959 = 5000939) B5000939
theorem B2222639 : Blo 2221435 2222639 := bstep (se 1 (by rfl) ⟨1666979, by rfl⟩ : syracuseStep 2222639 = 3333959) B3333959
theorem B3333965 : Blo 2221435 3333965 := bbase (se 3 (by rfl) ⟨625118, by rfl⟩ : syracuseStep 3333965 = 1250237) (by norm_num)
theorem B2222643 : Blo 2221435 2222643 := bstep (se 1 (by rfl) ⟨1666982, by rfl⟩ : syracuseStep 2222643 = 3333965) B3333965
theorem B5000957 : Blo 2221435 5000957 := bbase (se 3 (by rfl) ⟨937679, by rfl⟩ : syracuseStep 5000957 = 1875359) (by norm_num)
theorem B3333971 : Blo 2221435 3333971 := bstep (se 1 (by rfl) ⟨2500478, by rfl⟩ : syracuseStep 3333971 = 5000957) B5000957
theorem B2222647 : Blo 2221435 2222647 := bstep (se 1 (by rfl) ⟨1666985, by rfl⟩ : syracuseStep 2222647 = 3333971) B3333971
theorem B3750725 : Blo 2221435 3750725 := bbase (se 4 (by rfl) ⟨351630, by rfl⟩ : syracuseStep 3750725 = 703261) (by norm_num)
theorem B2500483 : Blo 2221435 2500483 := bstep (se 1 (by rfl) ⟨1875362, by rfl⟩ : syracuseStep 2500483 = 3750725) B3750725
theorem B3333977 : Blo 2221435 3333977 := bstep (se 2 (by rfl) ⟨1250241, by rfl⟩ : syracuseStep 3333977 = 2500483) B2500483
theorem B2222651 : Blo 2221435 2222651 := bstep (se 1 (by rfl) ⟨1666988, by rfl⟩ : syracuseStep 2222651 = 3333977) B3333977
theorem B16878293 : Blo 2221435 16878293 := bbase (se 7 (by rfl) ⟨197792, by rfl⟩ : syracuseStep 16878293 = 395585) (by norm_num)
theorem B11252195 : Blo 2221435 11252195 := bstep (se 1 (by rfl) ⟨8439146, by rfl⟩ : syracuseStep 11252195 = 16878293) B16878293
theorem B7501463 : Blo 2221435 7501463 := bstep (se 1 (by rfl) ⟨5626097, by rfl⟩ : syracuseStep 7501463 = 11252195) B11252195
theorem B5000975 : Blo 2221435 5000975 := bstep (se 1 (by rfl) ⟨3750731, by rfl⟩ : syracuseStep 5000975 = 7501463) B7501463
theorem B3333983 : Blo 2221435 3333983 := bstep (se 1 (by rfl) ⟨2500487, by rfl⟩ : syracuseStep 3333983 = 5000975) B5000975
theorem B2222655 : Blo 2221435 2222655 := bstep (se 1 (by rfl) ⟨1666991, by rfl⟩ : syracuseStep 2222655 = 3333983) B3333983
theorem B3333989 : Blo 2221435 3333989 := bbase (se 4 (by rfl) ⟨312561, by rfl⟩ : syracuseStep 3333989 = 625123) (by norm_num)
theorem B2222659 : Blo 2221435 2222659 := bstep (se 1 (by rfl) ⟨1666994, by rfl⟩ : syracuseStep 2222659 = 3333989) B3333989
theorem B4219589 : Blo 2221435 4219589 := bbase (se 4 (by rfl) ⟨395586, by rfl⟩ : syracuseStep 4219589 = 791173) (by norm_num)
theorem B2813059 : Blo 2221435 2813059 := bstep (se 1 (by rfl) ⟨2109794, by rfl⟩ : syracuseStep 2813059 = 4219589) B4219589
theorem B3750745 : Blo 2221435 3750745 := bstep (se 2 (by rfl) ⟨1406529, by rfl⟩ : syracuseStep 3750745 = 2813059) B2813059
theorem B5000993 : Blo 2221435 5000993 := bstep (se 2 (by rfl) ⟨1875372, by rfl⟩ : syracuseStep 5000993 = 3750745) B3750745
theorem B3333995 : Blo 2221435 3333995 := bstep (se 1 (by rfl) ⟨2500496, by rfl⟩ : syracuseStep 3333995 = 5000993) B5000993
theorem B2222663 : Blo 2221435 2222663 := bstep (se 1 (by rfl) ⟨1666997, by rfl⟩ : syracuseStep 2222663 = 3333995) B3333995
theorem B2500501 : Blo 2221435 2500501 := bbase (se 6 (by rfl) ⟨58605, by rfl⟩ : syracuseStep 2500501 = 117211) (by norm_num)
theorem B3334001 : Blo 2221435 3334001 := bstep (se 2 (by rfl) ⟨1250250, by rfl⟩ : syracuseStep 3334001 = 2500501) B2500501
theorem B2222667 : Blo 2221435 2222667 := bstep (se 1 (by rfl) ⟨1667000, by rfl⟩ : syracuseStep 2222667 = 3334001) B3334001
theorem B2813069 : Blo 2221435 2813069 := bbase (se 3 (by rfl) ⟨527450, by rfl⟩ : syracuseStep 2813069 = 1054901) (by norm_num)
theorem B7501517 : Blo 2221435 7501517 := bstep (se 3 (by rfl) ⟨1406534, by rfl⟩ : syracuseStep 7501517 = 2813069) B2813069
theorem B5001011 : Blo 2221435 5001011 := bstep (se 1 (by rfl) ⟨3750758, by rfl⟩ : syracuseStep 5001011 = 7501517) B7501517
theorem B3334007 : Blo 2221435 3334007 := bstep (se 1 (by rfl) ⟨2500505, by rfl⟩ : syracuseStep 3334007 = 5001011) B5001011
theorem B2222671 : Blo 2221435 2222671 := bstep (se 1 (by rfl) ⟨1667003, by rfl⟩ : syracuseStep 2222671 = 3334007) B3334007
theorem B3334013 : Blo 2221435 3334013 := bbase (se 3 (by rfl) ⟨625127, by rfl⟩ : syracuseStep 3334013 = 1250255) (by norm_num)
theorem B2222675 : Blo 2221435 2222675 := bstep (se 1 (by rfl) ⟨1667006, by rfl⟩ : syracuseStep 2222675 = 3334013) B3334013
theorem B5001029 : Blo 2221435 5001029 := bbase (se 4 (by rfl) ⟨468846, by rfl⟩ : syracuseStep 5001029 = 937693) (by norm_num)
theorem B3334019 : Blo 2221435 3334019 := bstep (se 1 (by rfl) ⟨2500514, by rfl⟩ : syracuseStep 3334019 = 5001029) B5001029
theorem B2222679 : Blo 2221435 2222679 := bstep (se 1 (by rfl) ⟨1667009, by rfl⟩ : syracuseStep 2222679 = 3334019) B3334019
theorem B3004013 : Blo 2221435 3004013 := bbase (se 3 (by rfl) ⟨563252, by rfl⟩ : syracuseStep 3004013 = 1126505) (by norm_num)
theorem B8010701 : Blo 2221435 8010701 := bstep (se 3 (by rfl) ⟨1502006, by rfl⟩ : syracuseStep 8010701 = 3004013) B3004013
theorem B5340467 : Blo 2221435 5340467 := bstep (se 1 (by rfl) ⟨4005350, by rfl⟩ : syracuseStep 5340467 = 8010701) B8010701
theorem B3560311 : Blo 2221435 3560311 := bstep (se 1 (by rfl) ⟨2670233, by rfl⟩ : syracuseStep 3560311 = 5340467) B5340467
theorem B4747081 : Blo 2221435 4747081 := bstep (se 2 (by rfl) ⟨1780155, by rfl⟩ : syracuseStep 4747081 = 3560311) B3560311
theorem B6329441 : Blo 2221435 6329441 := bstep (se 2 (by rfl) ⟨2373540, by rfl⟩ : syracuseStep 6329441 = 4747081) B4747081
theorem B4219627 : Blo 2221435 4219627 := bstep (se 1 (by rfl) ⟨3164720, by rfl⟩ : syracuseStep 4219627 = 6329441) B6329441
theorem B5626169 : Blo 2221435 5626169 := bstep (se 2 (by rfl) ⟨2109813, by rfl⟩ : syracuseStep 5626169 = 4219627) B4219627
theorem B3750779 : Blo 2221435 3750779 := bstep (se 1 (by rfl) ⟨2813084, by rfl⟩ : syracuseStep 3750779 = 5626169) B5626169
theorem B2500519 : Blo 2221435 2500519 := bstep (se 1 (by rfl) ⟨1875389, by rfl⟩ : syracuseStep 2500519 = 3750779) B3750779
theorem B3334025 : Blo 2221435 3334025 := bstep (se 2 (by rfl) ⟨1250259, by rfl⟩ : syracuseStep 3334025 = 2500519) B2500519
theorem B2222683 : Blo 2221435 2222683 := bstep (se 1 (by rfl) ⟨1667012, by rfl⟩ : syracuseStep 2222683 = 3334025) B3334025
theorem B11252357 : Blo 2221435 11252357 := bbase (se 4 (by rfl) ⟨1054908, by rfl⟩ : syracuseStep 11252357 = 2109817) (by norm_num)
theorem B7501571 : Blo 2221435 7501571 := bstep (se 1 (by rfl) ⟨5626178, by rfl⟩ : syracuseStep 7501571 = 11252357) B11252357
theorem B5001047 : Blo 2221435 5001047 := bstep (se 1 (by rfl) ⟨3750785, by rfl⟩ : syracuseStep 5001047 = 7501571) B7501571
theorem B3334031 : Blo 2221435 3334031 := bstep (se 1 (by rfl) ⟨2500523, by rfl⟩ : syracuseStep 3334031 = 5001047) B5001047
theorem B2222687 : Blo 2221435 2222687 := bstep (se 1 (by rfl) ⟨1667015, by rfl⟩ : syracuseStep 2222687 = 3334031) B3334031
theorem B3334037 : Blo 2221435 3334037 := bbase (se 6 (by rfl) ⟨78141, by rfl⟩ : syracuseStep 3334037 = 156283) (by norm_num)
theorem B2222691 : Blo 2221435 2222691 := bstep (se 1 (by rfl) ⟨1667018, by rfl⟩ : syracuseStep 2222691 = 3334037) B3334037
theorem B2373553 : Blo 2221435 2373553 := bbase (se 2 (by rfl) ⟨890082, by rfl⟩ : syracuseStep 2373553 = 1780165) (by norm_num)
theorem B12658949 : Blo 2221435 12658949 := bstep (se 4 (by rfl) ⟨1186776, by rfl⟩ : syracuseStep 12658949 = 2373553) B2373553
theorem B8439299 : Blo 2221435 8439299 := bstep (se 1 (by rfl) ⟨6329474, by rfl⟩ : syracuseStep 8439299 = 12658949) B12658949
theorem B5626199 : Blo 2221435 5626199 := bstep (se 1 (by rfl) ⟨4219649, by rfl⟩ : syracuseStep 5626199 = 8439299) B8439299
theorem B3750799 : Blo 2221435 3750799 := bstep (se 1 (by rfl) ⟨2813099, by rfl⟩ : syracuseStep 3750799 = 5626199) B5626199
theorem B5001065 : Blo 2221435 5001065 := bstep (se 2 (by rfl) ⟨1875399, by rfl⟩ : syracuseStep 5001065 = 3750799) B3750799
theorem B3334043 : Blo 2221435 3334043 := bstep (se 1 (by rfl) ⟨2500532, by rfl⟩ : syracuseStep 3334043 = 5001065) B5001065
theorem B2222695 : Blo 2221435 2222695 := bstep (se 1 (by rfl) ⟨1667021, by rfl⟩ : syracuseStep 2222695 = 3334043) B3334043
theorem B2500537 : Blo 2221435 2500537 := bbase (se 2 (by rfl) ⟨937701, by rfl⟩ : syracuseStep 2500537 = 1875403) (by norm_num)
theorem B3334049 : Blo 2221435 3334049 := bstep (se 2 (by rfl) ⟨1250268, by rfl⟩ : syracuseStep 3334049 = 2500537) B2500537
theorem B2222699 : Blo 2221435 2222699 := bstep (se 1 (by rfl) ⟨1667024, by rfl⟩ : syracuseStep 2222699 = 3334049) B3334049
theorem B2670257 : Blo 2221435 2670257 := bbase (se 2 (by rfl) ⟨1001346, by rfl⟩ : syracuseStep 2670257 = 2002693) (by norm_num)
theorem B7120685 : Blo 2221435 7120685 := bstep (se 3 (by rfl) ⟨1335128, by rfl⟩ : syracuseStep 7120685 = 2670257) B2670257
theorem B4747123 : Blo 2221435 4747123 := bstep (se 1 (by rfl) ⟨3560342, by rfl⟩ : syracuseStep 4747123 = 7120685) B7120685
theorem B6329497 : Blo 2221435 6329497 := bstep (se 2 (by rfl) ⟨2373561, by rfl⟩ : syracuseStep 6329497 = 4747123) B4747123
theorem B8439329 : Blo 2221435 8439329 := bstep (se 2 (by rfl) ⟨3164748, by rfl⟩ : syracuseStep 8439329 = 6329497) B6329497
theorem B5626219 : Blo 2221435 5626219 := bstep (se 1 (by rfl) ⟨4219664, by rfl⟩ : syracuseStep 5626219 = 8439329) B8439329
theorem B7501625 : Blo 2221435 7501625 := bstep (se 2 (by rfl) ⟨2813109, by rfl⟩ : syracuseStep 7501625 = 5626219) B5626219
theorem B5001083 : Blo 2221435 5001083 := bstep (se 1 (by rfl) ⟨3750812, by rfl⟩ : syracuseStep 5001083 = 7501625) B7501625
theorem B3334055 : Blo 2221435 3334055 := bstep (se 1 (by rfl) ⟨2500541, by rfl⟩ : syracuseStep 3334055 = 5001083) B5001083
theorem B2222703 : Blo 2221435 2222703 := bstep (se 1 (by rfl) ⟨1667027, by rfl⟩ : syracuseStep 2222703 = 3334055) B3334055
theorem B3334061 : Blo 2221435 3334061 := bbase (se 3 (by rfl) ⟨625136, by rfl⟩ : syracuseStep 3334061 = 1250273) (by norm_num)
theorem B2222707 : Blo 2221435 2222707 := bstep (se 1 (by rfl) ⟨1667030, by rfl⟩ : syracuseStep 2222707 = 3334061) B3334061
theorem B5001101 : Blo 2221435 5001101 := bbase (se 3 (by rfl) ⟨937706, by rfl⟩ : syracuseStep 5001101 = 1875413) (by norm_num)
theorem B3334067 : Blo 2221435 3334067 := bstep (se 1 (by rfl) ⟨2500550, by rfl⟩ : syracuseStep 3334067 = 5001101) B5001101
theorem B2222711 : Blo 2221435 2222711 := bstep (se 1 (by rfl) ⟨1667033, by rfl⟩ : syracuseStep 2222711 = 3334067) B3334067
theorem B2813125 : Blo 2221435 2813125 := bbase (se 4 (by rfl) ⟨263730, by rfl⟩ : syracuseStep 2813125 = 527461) (by norm_num)
theorem B3750833 : Blo 2221435 3750833 := bstep (se 2 (by rfl) ⟨1406562, by rfl⟩ : syracuseStep 3750833 = 2813125) B2813125
theorem B2500555 : Blo 2221435 2500555 := bstep (se 1 (by rfl) ⟨1875416, by rfl⟩ : syracuseStep 2500555 = 3750833) B3750833
theorem B3334073 : Blo 2221435 3334073 := bstep (se 2 (by rfl) ⟨1250277, by rfl⟩ : syracuseStep 3334073 = 2500555) B2500555
theorem B2222715 : Blo 2221435 2222715 := bstep (se 1 (by rfl) ⟨1667036, by rfl⟩ : syracuseStep 2222715 = 3334073) B3334073
theorem B36048725 : Blo 2221435 36048725 := bbase (se 9 (by rfl) ⟨105611, by rfl⟩ : syracuseStep 36048725 = 211223) (by norm_num)
theorem B24032483 : Blo 2221435 24032483 := bstep (se 1 (by rfl) ⟨18024362, by rfl⟩ : syracuseStep 24032483 = 36048725) B36048725
theorem B16021655 : Blo 2221435 16021655 := bstep (se 1 (by rfl) ⟨12016241, by rfl⟩ : syracuseStep 16021655 = 24032483) B24032483
theorem B10681103 : Blo 2221435 10681103 := bstep (se 1 (by rfl) ⟨8010827, by rfl⟩ : syracuseStep 10681103 = 16021655) B16021655
theorem B28482941 : Blo 2221435 28482941 := bstep (se 3 (by rfl) ⟨5340551, by rfl⟩ : syracuseStep 28482941 = 10681103) B10681103
theorem B18988627 : Blo 2221435 18988627 := bstep (se 1 (by rfl) ⟨14241470, by rfl⟩ : syracuseStep 18988627 = 28482941) B28482941
theorem B25318169 : Blo 2221435 25318169 := bstep (se 2 (by rfl) ⟨9494313, by rfl⟩ : syracuseStep 25318169 = 18988627) B18988627
theorem B16878779 : Blo 2221435 16878779 := bstep (se 1 (by rfl) ⟨12659084, by rfl⟩ : syracuseStep 16878779 = 25318169) B25318169
theorem B11252519 : Blo 2221435 11252519 := bstep (se 1 (by rfl) ⟨8439389, by rfl⟩ : syracuseStep 11252519 = 16878779) B16878779
theorem B7501679 : Blo 2221435 7501679 := bstep (se 1 (by rfl) ⟨5626259, by rfl⟩ : syracuseStep 7501679 = 11252519) B11252519
theorem B5001119 : Blo 2221435 5001119 := bstep (se 1 (by rfl) ⟨3750839, by rfl⟩ : syracuseStep 5001119 = 7501679) B7501679
theorem B3334079 : Blo 2221435 3334079 := bstep (se 1 (by rfl) ⟨2500559, by rfl⟩ : syracuseStep 3334079 = 5001119) B5001119
theorem B2222719 : Blo 2221435 2222719 := bstep (se 1 (by rfl) ⟨1667039, by rfl⟩ : syracuseStep 2222719 = 3334079) B3334079
theorem B3334085 : Blo 2221435 3334085 := bbase (se 4 (by rfl) ⟨312570, by rfl⟩ : syracuseStep 3334085 = 625141) (by norm_num)
theorem B2222723 : Blo 2221435 2222723 := bstep (se 1 (by rfl) ⟨1667042, by rfl⟩ : syracuseStep 2222723 = 3334085) B3334085
theorem B3750853 : Blo 2221435 3750853 := bbase (se 4 (by rfl) ⟨351642, by rfl⟩ : syracuseStep 3750853 = 703285) (by norm_num)
theorem B5001137 : Blo 2221435 5001137 := bstep (se 2 (by rfl) ⟨1875426, by rfl⟩ : syracuseStep 5001137 = 3750853) B3750853
theorem B3334091 : Blo 2221435 3334091 := bstep (se 1 (by rfl) ⟨2500568, by rfl⟩ : syracuseStep 3334091 = 5001137) B5001137
theorem B2222727 : Blo 2221435 2222727 := bstep (se 1 (by rfl) ⟨1667045, by rfl⟩ : syracuseStep 2222727 = 3334091) B3334091
theorem B2500573 : Blo 2221435 2500573 := bbase (se 3 (by rfl) ⟨468857, by rfl⟩ : syracuseStep 2500573 = 937715) (by norm_num)
theorem B3334097 : Blo 2221435 3334097 := bstep (se 2 (by rfl) ⟨1250286, by rfl⟩ : syracuseStep 3334097 = 2500573) B2500573
theorem B2222731 : Blo 2221435 2222731 := bstep (se 1 (by rfl) ⟨1667048, by rfl⟩ : syracuseStep 2222731 = 3334097) B3334097
theorem B7501733 : Blo 2221435 7501733 := bbase (se 4 (by rfl) ⟨703287, by rfl⟩ : syracuseStep 7501733 = 1406575) (by norm_num)
theorem B5001155 : Blo 2221435 5001155 := bstep (se 1 (by rfl) ⟨3750866, by rfl⟩ : syracuseStep 5001155 = 7501733) B7501733
theorem B3334103 : Blo 2221435 3334103 := bstep (se 1 (by rfl) ⟨2500577, by rfl⟩ : syracuseStep 3334103 = 5001155) B5001155
theorem B2222735 : Blo 2221435 2222735 := bstep (se 1 (by rfl) ⟨1667051, by rfl⟩ : syracuseStep 2222735 = 3334103) B3334103
theorem B3334109 : Blo 2221435 3334109 := bbase (se 3 (by rfl) ⟨625145, by rfl⟩ : syracuseStep 3334109 = 1250291) (by norm_num)
theorem B2222739 : Blo 2221435 2222739 := bstep (se 1 (by rfl) ⟨1667054, by rfl⟩ : syracuseStep 2222739 = 3334109) B3334109
theorem B5001173 : Blo 2221435 5001173 := bbase (se 7 (by rfl) ⟨58607, by rfl⟩ : syracuseStep 5001173 = 117215) (by norm_num)
theorem B3334115 : Blo 2221435 3334115 := bstep (se 1 (by rfl) ⟨2500586, by rfl⟩ : syracuseStep 3334115 = 5001173) B5001173
theorem B2222743 : Blo 2221435 2222743 := bstep (se 1 (by rfl) ⟨1667057, by rfl⟩ : syracuseStep 2222743 = 3334115) B3334115
theorem B14241653 : Blo 2221435 14241653 := bbase (se 5 (by rfl) ⟨667577, by rfl⟩ : syracuseStep 14241653 = 1335155) (by norm_num)
theorem B9494435 : Blo 2221435 9494435 := bstep (se 1 (by rfl) ⟨7120826, by rfl⟩ : syracuseStep 9494435 = 14241653) B14241653
theorem B6329623 : Blo 2221435 6329623 := bstep (se 1 (by rfl) ⟨4747217, by rfl⟩ : syracuseStep 6329623 = 9494435) B9494435
theorem B8439497 : Blo 2221435 8439497 := bstep (se 2 (by rfl) ⟨3164811, by rfl⟩ : syracuseStep 8439497 = 6329623) B6329623
theorem B5626331 : Blo 2221435 5626331 := bstep (se 1 (by rfl) ⟨4219748, by rfl⟩ : syracuseStep 5626331 = 8439497) B8439497
theorem B3750887 : Blo 2221435 3750887 := bstep (se 1 (by rfl) ⟨2813165, by rfl⟩ : syracuseStep 3750887 = 5626331) B5626331
theorem B2500591 : Blo 2221435 2500591 := bstep (se 1 (by rfl) ⟨1875443, by rfl⟩ : syracuseStep 2500591 = 3750887) B3750887
theorem B3334121 : Blo 2221435 3334121 := bstep (se 2 (by rfl) ⟨1250295, by rfl⟩ : syracuseStep 3334121 = 2500591) B2500591
theorem B2222747 : Blo 2221435 2222747 := bstep (se 1 (by rfl) ⟨1667060, by rfl⟩ : syracuseStep 2222747 = 3334121) B3334121
theorem B5340629 : Blo 2221435 5340629 := bbase (se 7 (by rfl) ⟨62585, by rfl⟩ : syracuseStep 5340629 = 125171) (by norm_num)
theorem B3560419 : Blo 2221435 3560419 := bstep (se 1 (by rfl) ⟨2670314, by rfl⟩ : syracuseStep 3560419 = 5340629) B5340629
theorem B18988901 : Blo 2221435 18988901 := bstep (se 4 (by rfl) ⟨1780209, by rfl⟩ : syracuseStep 18988901 = 3560419) B3560419
theorem B12659267 : Blo 2221435 12659267 := bstep (se 1 (by rfl) ⟨9494450, by rfl⟩ : syracuseStep 12659267 = 18988901) B18988901
theorem B8439511 : Blo 2221435 8439511 := bstep (se 1 (by rfl) ⟨6329633, by rfl⟩ : syracuseStep 8439511 = 12659267) B12659267
theorem B11252681 : Blo 2221435 11252681 := bstep (se 2 (by rfl) ⟨4219755, by rfl⟩ : syracuseStep 11252681 = 8439511) B8439511
theorem B7501787 : Blo 2221435 7501787 := bstep (se 1 (by rfl) ⟨5626340, by rfl⟩ : syracuseStep 7501787 = 11252681) B11252681
theorem B5001191 : Blo 2221435 5001191 := bstep (se 1 (by rfl) ⟨3750893, by rfl⟩ : syracuseStep 5001191 = 7501787) B7501787
theorem B3334127 : Blo 2221435 3334127 := bstep (se 1 (by rfl) ⟨2500595, by rfl⟩ : syracuseStep 3334127 = 5001191) B5001191
theorem B2222751 : Blo 2221435 2222751 := bstep (se 1 (by rfl) ⟨1667063, by rfl⟩ : syracuseStep 2222751 = 3334127) B3334127
theorem B3334133 : Blo 2221435 3334133 := bbase (se 5 (by rfl) ⟨156287, by rfl⟩ : syracuseStep 3334133 = 312575) (by norm_num)
theorem B2222755 : Blo 2221435 2222755 := bstep (se 1 (by rfl) ⟨1667066, by rfl⟩ : syracuseStep 2222755 = 3334133) B3334133
theorem B5413517 : Blo 2221435 5413517 := bbase (se 3 (by rfl) ⟨1015034, by rfl⟩ : syracuseStep 5413517 = 2030069) (by norm_num)
theorem B3609011 : Blo 2221435 3609011 := bstep (se 1 (by rfl) ⟨2706758, by rfl⟩ : syracuseStep 3609011 = 5413517) B5413517
theorem B2406007 : Blo 2221435 2406007 := bstep (se 1 (by rfl) ⟨1804505, by rfl⟩ : syracuseStep 2406007 = 3609011) B3609011
theorem B3208009 : Blo 2221435 3208009 := bstep (se 2 (by rfl) ⟨1203003, by rfl⟩ : syracuseStep 3208009 = 2406007) B2406007
theorem B4277345 : Blo 2221435 4277345 := bstep (se 2 (by rfl) ⟨1604004, by rfl⟩ : syracuseStep 4277345 = 3208009) B3208009
theorem B11406253 : Blo 2221435 11406253 := bstep (se 3 (by rfl) ⟨2138672, by rfl⟩ : syracuseStep 11406253 = 4277345) B4277345
theorem B15208337 : Blo 2221435 15208337 := bstep (se 2 (by rfl) ⟨5703126, by rfl⟩ : syracuseStep 15208337 = 11406253) B11406253
theorem B10138891 : Blo 2221435 10138891 := bstep (se 1 (by rfl) ⟨7604168, by rfl⟩ : syracuseStep 10138891 = 15208337) B15208337
theorem B13518521 : Blo 2221435 13518521 := bstep (se 2 (by rfl) ⟨5069445, by rfl⟩ : syracuseStep 13518521 = 10138891) B10138891
theorem B9012347 : Blo 2221435 9012347 := bstep (se 1 (by rfl) ⟨6759260, by rfl⟩ : syracuseStep 9012347 = 13518521) B13518521
theorem B6008231 : Blo 2221435 6008231 := bstep (se 1 (by rfl) ⟨4506173, by rfl⟩ : syracuseStep 6008231 = 9012347) B9012347
theorem B4005487 : Blo 2221435 4005487 := bstep (se 1 (by rfl) ⟨3004115, by rfl⟩ : syracuseStep 4005487 = 6008231) B6008231
theorem B5340649 : Blo 2221435 5340649 := bstep (se 2 (by rfl) ⟨2002743, by rfl⟩ : syracuseStep 5340649 = 4005487) B4005487
theorem B7120865 : Blo 2221435 7120865 := bstep (se 2 (by rfl) ⟨2670324, by rfl⟩ : syracuseStep 7120865 = 5340649) B5340649
theorem B4747243 : Blo 2221435 4747243 := bstep (se 1 (by rfl) ⟨3560432, by rfl⟩ : syracuseStep 4747243 = 7120865) B7120865
theorem B6329657 : Blo 2221435 6329657 := bstep (se 2 (by rfl) ⟨2373621, by rfl⟩ : syracuseStep 6329657 = 4747243) B4747243
theorem B4219771 : Blo 2221435 4219771 := bstep (se 1 (by rfl) ⟨3164828, by rfl⟩ : syracuseStep 4219771 = 6329657) B6329657
theorem B5626361 : Blo 2221435 5626361 := bstep (se 2 (by rfl) ⟨2109885, by rfl⟩ : syracuseStep 5626361 = 4219771) B4219771
theorem B3750907 : Blo 2221435 3750907 := bstep (se 1 (by rfl) ⟨2813180, by rfl⟩ : syracuseStep 3750907 = 5626361) B5626361
theorem B5001209 : Blo 2221435 5001209 := bstep (se 2 (by rfl) ⟨1875453, by rfl⟩ : syracuseStep 5001209 = 3750907) B3750907
theorem B3334139 : Blo 2221435 3334139 := bstep (se 1 (by rfl) ⟨2500604, by rfl⟩ : syracuseStep 3334139 = 5001209) B5001209
theorem B2222759 : Blo 2221435 2222759 := bstep (se 1 (by rfl) ⟨1667069, by rfl⟩ : syracuseStep 2222759 = 3334139) B3334139
theorem B2500609 : Blo 2221435 2500609 := bbase (se 2 (by rfl) ⟨937728, by rfl⟩ : syracuseStep 2500609 = 1875457) (by norm_num)
theorem B3334145 : Blo 2221435 3334145 := bstep (se 2 (by rfl) ⟨1250304, by rfl⟩ : syracuseStep 3334145 = 2500609) B2500609
theorem B2222763 : Blo 2221435 2222763 := bstep (se 1 (by rfl) ⟨1667072, by rfl⟩ : syracuseStep 2222763 = 3334145) B3334145
theorem B5626381 : Blo 2221435 5626381 := bbase (se 3 (by rfl) ⟨1054946, by rfl⟩ : syracuseStep 5626381 = 2109893) (by norm_num)
theorem B7501841 : Blo 2221435 7501841 := bstep (se 2 (by rfl) ⟨2813190, by rfl⟩ : syracuseStep 7501841 = 5626381) B5626381
theorem B5001227 : Blo 2221435 5001227 := bstep (se 1 (by rfl) ⟨3750920, by rfl⟩ : syracuseStep 5001227 = 7501841) B7501841
theorem B3334151 : Blo 2221435 3334151 := bstep (se 1 (by rfl) ⟨2500613, by rfl⟩ : syracuseStep 3334151 = 5001227) B5001227
theorem B2222767 : Blo 2221435 2222767 := bstep (se 1 (by rfl) ⟨1667075, by rfl⟩ : syracuseStep 2222767 = 3334151) B3334151
theorem B3334157 : Blo 2221435 3334157 := bbase (se 3 (by rfl) ⟨625154, by rfl⟩ : syracuseStep 3334157 = 1250309) (by norm_num)
theorem B2222771 : Blo 2221435 2222771 := bstep (se 1 (by rfl) ⟨1667078, by rfl⟩ : syracuseStep 2222771 = 3334157) B3334157
theorem B5001245 : Blo 2221435 5001245 := bbase (se 3 (by rfl) ⟨937733, by rfl⟩ : syracuseStep 5001245 = 1875467) (by norm_num)
theorem B3334163 : Blo 2221435 3334163 := bstep (se 1 (by rfl) ⟨2500622, by rfl⟩ : syracuseStep 3334163 = 5001245) B5001245
theorem B2222775 : Blo 2221435 2222775 := bstep (se 1 (by rfl) ⟨1667081, by rfl⟩ : syracuseStep 2222775 = 3334163) B3334163
theorem B3750941 : Blo 2221435 3750941 := bbase (se 3 (by rfl) ⟨703301, by rfl⟩ : syracuseStep 3750941 = 1406603) (by norm_num)
theorem B2500627 : Blo 2221435 2500627 := bstep (se 1 (by rfl) ⟨1875470, by rfl⟩ : syracuseStep 2500627 = 3750941) B3750941
theorem B3334169 : Blo 2221435 3334169 := bstep (se 2 (by rfl) ⟨1250313, by rfl⟩ : syracuseStep 3334169 = 2500627) B2500627
theorem B2222779 : Blo 2221435 2222779 := bstep (se 1 (by rfl) ⟨1667084, by rfl⟩ : syracuseStep 2222779 = 3334169) B3334169
theorem B4506221 : Blo 2221435 4506221 := bbase (se 3 (by rfl) ⟨844916, by rfl⟩ : syracuseStep 4506221 = 1689833) (by norm_num)
theorem B3004147 : Blo 2221435 3004147 := bstep (se 1 (by rfl) ⟨2253110, by rfl⟩ : syracuseStep 3004147 = 4506221) B4506221
theorem B16022117 : Blo 2221435 16022117 := bstep (se 4 (by rfl) ⟨1502073, by rfl⟩ : syracuseStep 16022117 = 3004147) B3004147
theorem B10681411 : Blo 2221435 10681411 := bstep (se 1 (by rfl) ⟨8011058, by rfl⟩ : syracuseStep 10681411 = 16022117) B16022117
theorem B14241881 : Blo 2221435 14241881 := bstep (se 2 (by rfl) ⟨5340705, by rfl⟩ : syracuseStep 14241881 = 10681411) B10681411
theorem B9494587 : Blo 2221435 9494587 := bstep (se 1 (by rfl) ⟨7120940, by rfl⟩ : syracuseStep 9494587 = 14241881) B14241881
theorem B12659449 : Blo 2221435 12659449 := bstep (se 2 (by rfl) ⟨4747293, by rfl⟩ : syracuseStep 12659449 = 9494587) B9494587
theorem B16879265 : Blo 2221435 16879265 := bstep (se 2 (by rfl) ⟨6329724, by rfl⟩ : syracuseStep 16879265 = 12659449) B12659449
theorem B11252843 : Blo 2221435 11252843 := bstep (se 1 (by rfl) ⟨8439632, by rfl⟩ : syracuseStep 11252843 = 16879265) B16879265
theorem B7501895 : Blo 2221435 7501895 := bstep (se 1 (by rfl) ⟨5626421, by rfl⟩ : syracuseStep 7501895 = 11252843) B11252843
theorem B5001263 : Blo 2221435 5001263 := bstep (se 1 (by rfl) ⟨3750947, by rfl⟩ : syracuseStep 5001263 = 7501895) B7501895
theorem B3334175 : Blo 2221435 3334175 := bstep (se 1 (by rfl) ⟨2500631, by rfl⟩ : syracuseStep 3334175 = 5001263) B5001263
theorem B2222783 : Blo 2221435 2222783 := bstep (se 1 (by rfl) ⟨1667087, by rfl⟩ : syracuseStep 2222783 = 3334175) B3334175
theorem B3334181 : Blo 2221435 3334181 := bbase (se 4 (by rfl) ⟨312579, by rfl⟩ : syracuseStep 3334181 = 625159) (by norm_num)
theorem B2222787 : Blo 2221435 2222787 := bstep (se 1 (by rfl) ⟨1667090, by rfl⟩ : syracuseStep 2222787 = 3334181) B3334181
theorem B2813221 : Blo 2221435 2813221 := bbase (se 4 (by rfl) ⟨263739, by rfl⟩ : syracuseStep 2813221 = 527479) (by norm_num)
theorem B3750961 : Blo 2221435 3750961 := bstep (se 2 (by rfl) ⟨1406610, by rfl⟩ : syracuseStep 3750961 = 2813221) B2813221
theorem B5001281 : Blo 2221435 5001281 := bstep (se 2 (by rfl) ⟨1875480, by rfl⟩ : syracuseStep 5001281 = 3750961) B3750961
theorem B3334187 : Blo 2221435 3334187 := bstep (se 1 (by rfl) ⟨2500640, by rfl⟩ : syracuseStep 3334187 = 5001281) B5001281
theorem B2222791 : Blo 2221435 2222791 := bstep (se 1 (by rfl) ⟨1667093, by rfl⟩ : syracuseStep 2222791 = 3334187) B3334187
theorem B2500645 : Blo 2221435 2500645 := bbase (se 4 (by rfl) ⟨234435, by rfl⟩ : syracuseStep 2500645 = 468871) (by norm_num)
theorem B3334193 : Blo 2221435 3334193 := bstep (se 2 (by rfl) ⟨1250322, by rfl⟩ : syracuseStep 3334193 = 2500645) B2500645
theorem B2222795 : Blo 2221435 2222795 := bstep (se 1 (by rfl) ⟨1667096, by rfl⟩ : syracuseStep 2222795 = 3334193) B3334193
theorem B2283869 : Blo 2221435 2283869 := bbase (se 3 (by rfl) ⟨428225, by rfl⟩ : syracuseStep 2283869 = 856451) (by norm_num)
theorem B6090317 : Blo 2221435 6090317 := bstep (se 3 (by rfl) ⟨1141934, by rfl⟩ : syracuseStep 6090317 = 2283869) B2283869
theorem B4060211 : Blo 2221435 4060211 := bstep (se 1 (by rfl) ⟨3045158, by rfl⟩ : syracuseStep 4060211 = 6090317) B6090317
theorem B10827229 : Blo 2221435 10827229 := bstep (se 3 (by rfl) ⟨2030105, by rfl⟩ : syracuseStep 10827229 = 4060211) B4060211
theorem B14436305 : Blo 2221435 14436305 := bstep (se 2 (by rfl) ⟨5413614, by rfl⟩ : syracuseStep 14436305 = 10827229) B10827229
theorem B9624203 : Blo 2221435 9624203 := bstep (se 1 (by rfl) ⟨7218152, by rfl⟩ : syracuseStep 9624203 = 14436305) B14436305
theorem B6416135 : Blo 2221435 6416135 := bstep (se 1 (by rfl) ⟨4812101, by rfl⟩ : syracuseStep 6416135 = 9624203) B9624203
theorem B4277423 : Blo 2221435 4277423 := bstep (se 1 (by rfl) ⟨3208067, by rfl⟩ : syracuseStep 4277423 = 6416135) B6416135
theorem B2851615 : Blo 2221435 2851615 := bstep (se 1 (by rfl) ⟨2138711, by rfl⟩ : syracuseStep 2851615 = 4277423) B4277423
theorem B3802153 : Blo 2221435 3802153 := bstep (se 2 (by rfl) ⟨1425807, by rfl⟩ : syracuseStep 3802153 = 2851615) B2851615
theorem B5069537 : Blo 2221435 5069537 := bstep (se 2 (by rfl) ⟨1901076, by rfl⟩ : syracuseStep 5069537 = 3802153) B3802153
theorem B3379691 : Blo 2221435 3379691 := bstep (se 1 (by rfl) ⟨2534768, by rfl⟩ : syracuseStep 3379691 = 5069537) B5069537
theorem B9012509 : Blo 2221435 9012509 := bstep (se 3 (by rfl) ⟨1689845, by rfl⟩ : syracuseStep 9012509 = 3379691) B3379691
theorem B6008339 : Blo 2221435 6008339 := bstep (se 1 (by rfl) ⟨4506254, by rfl⟩ : syracuseStep 6008339 = 9012509) B9012509
theorem B4005559 : Blo 2221435 4005559 := bstep (se 1 (by rfl) ⟨3004169, by rfl⟩ : syracuseStep 4005559 = 6008339) B6008339
theorem B5340745 : Blo 2221435 5340745 := bstep (se 2 (by rfl) ⟨2002779, by rfl⟩ : syracuseStep 5340745 = 4005559) B4005559
theorem B7120993 : Blo 2221435 7120993 := bstep (se 2 (by rfl) ⟨2670372, by rfl⟩ : syracuseStep 7120993 = 5340745) B5340745
theorem B9494657 : Blo 2221435 9494657 := bstep (se 2 (by rfl) ⟨3560496, by rfl⟩ : syracuseStep 9494657 = 7120993) B7120993
theorem B6329771 : Blo 2221435 6329771 := bstep (se 1 (by rfl) ⟨4747328, by rfl⟩ : syracuseStep 6329771 = 9494657) B9494657
theorem B4219847 : Blo 2221435 4219847 := bstep (se 1 (by rfl) ⟨3164885, by rfl⟩ : syracuseStep 4219847 = 6329771) B6329771
theorem B2813231 : Blo 2221435 2813231 := bstep (se 1 (by rfl) ⟨2109923, by rfl⟩ : syracuseStep 2813231 = 4219847) B4219847
theorem B7501949 : Blo 2221435 7501949 := bstep (se 3 (by rfl) ⟨1406615, by rfl⟩ : syracuseStep 7501949 = 2813231) B2813231
theorem B5001299 : Blo 2221435 5001299 := bstep (se 1 (by rfl) ⟨3750974, by rfl⟩ : syracuseStep 5001299 = 7501949) B7501949
theorem B3334199 : Blo 2221435 3334199 := bstep (se 1 (by rfl) ⟨2500649, by rfl⟩ : syracuseStep 3334199 = 5001299) B5001299
theorem B2222799 : Blo 2221435 2222799 := bstep (se 1 (by rfl) ⟨1667099, by rfl⟩ : syracuseStep 2222799 = 3334199) B3334199
theorem B3334205 : Blo 2221435 3334205 := bbase (se 3 (by rfl) ⟨625163, by rfl⟩ : syracuseStep 3334205 = 1250327) (by norm_num)
theorem B2222803 : Blo 2221435 2222803 := bstep (se 1 (by rfl) ⟨1667102, by rfl⟩ : syracuseStep 2222803 = 3334205) B3334205
theorem B5001317 : Blo 2221435 5001317 := bbase (se 4 (by rfl) ⟨468873, by rfl⟩ : syracuseStep 5001317 = 937747) (by norm_num)
theorem B3334211 : Blo 2221435 3334211 := bstep (se 1 (by rfl) ⟨2500658, by rfl⟩ : syracuseStep 3334211 = 5001317) B5001317
theorem B2222807 : Blo 2221435 2222807 := bstep (se 1 (by rfl) ⟨1667105, by rfl⟩ : syracuseStep 2222807 = 3334211) B3334211
theorem B5626493 : Blo 2221435 5626493 := bbase (se 3 (by rfl) ⟨1054967, by rfl⟩ : syracuseStep 5626493 = 2109935) (by norm_num)
theorem B3750995 : Blo 2221435 3750995 := bstep (se 1 (by rfl) ⟨2813246, by rfl⟩ : syracuseStep 3750995 = 5626493) B5626493
theorem B2500663 : Blo 2221435 2500663 := bstep (se 1 (by rfl) ⟨1875497, by rfl⟩ : syracuseStep 2500663 = 3750995) B3750995
theorem B3334217 : Blo 2221435 3334217 := bstep (se 2 (by rfl) ⟨1250331, by rfl⟩ : syracuseStep 3334217 = 2500663) B2500663
theorem B2222811 : Blo 2221435 2222811 := bstep (se 1 (by rfl) ⟨1667108, by rfl⟩ : syracuseStep 2222811 = 3334217) B3334217
theorem B4219877 : Blo 2221435 4219877 := bbase (se 4 (by rfl) ⟨395613, by rfl⟩ : syracuseStep 4219877 = 791227) (by norm_num)
theorem B11253005 : Blo 2221435 11253005 := bstep (se 3 (by rfl) ⟨2109938, by rfl⟩ : syracuseStep 11253005 = 4219877) B4219877
theorem B7502003 : Blo 2221435 7502003 := bstep (se 1 (by rfl) ⟨5626502, by rfl⟩ : syracuseStep 7502003 = 11253005) B11253005
theorem B5001335 : Blo 2221435 5001335 := bstep (se 1 (by rfl) ⟨3751001, by rfl⟩ : syracuseStep 5001335 = 7502003) B7502003
theorem B3334223 : Blo 2221435 3334223 := bstep (se 1 (by rfl) ⟨2500667, by rfl⟩ : syracuseStep 3334223 = 5001335) B5001335
theorem B2222815 : Blo 2221435 2222815 := bstep (se 1 (by rfl) ⟨1667111, by rfl⟩ : syracuseStep 2222815 = 3334223) B3334223
theorem B3334229 : Blo 2221435 3334229 := bbase (se 8 (by rfl) ⟨19536, by rfl⟩ : syracuseStep 3334229 = 39073) (by norm_num)
theorem B2222819 : Blo 2221435 2222819 := bstep (se 1 (by rfl) ⟨1667114, by rfl⟩ : syracuseStep 2222819 = 3334229) B3334229
theorem B2851645 : Blo 2221435 2851645 := bbase (se 3 (by rfl) ⟨534683, by rfl⟩ : syracuseStep 2851645 = 1069367) (by norm_num)
theorem B3802193 : Blo 2221435 3802193 := bstep (se 2 (by rfl) ⟨1425822, by rfl⟩ : syracuseStep 3802193 = 2851645) B2851645
theorem B2534795 : Blo 2221435 2534795 := bstep (se 1 (by rfl) ⟨1901096, by rfl⟩ : syracuseStep 2534795 = 3802193) B3802193
theorem B27037813 : Blo 2221435 27037813 := bstep (se 5 (by rfl) ⟨1267397, by rfl⟩ : syracuseStep 27037813 = 2534795) B2534795
theorem B36050417 : Blo 2221435 36050417 := bstep (se 2 (by rfl) ⟨13518906, by rfl⟩ : syracuseStep 36050417 = 27037813) B27037813
theorem B24033611 : Blo 2221435 24033611 := bstep (se 1 (by rfl) ⟨18025208, by rfl⟩ : syracuseStep 24033611 = 36050417) B36050417
theorem B16022407 : Blo 2221435 16022407 := bstep (se 1 (by rfl) ⟨12016805, by rfl⟩ : syracuseStep 16022407 = 24033611) B24033611
theorem B21363209 : Blo 2221435 21363209 := bstep (se 2 (by rfl) ⟨8011203, by rfl⟩ : syracuseStep 21363209 = 16022407) B16022407
theorem B14242139 : Blo 2221435 14242139 := bstep (se 1 (by rfl) ⟨10681604, by rfl⟩ : syracuseStep 14242139 = 21363209) B21363209
theorem B9494759 : Blo 2221435 9494759 := bstep (se 1 (by rfl) ⟨7121069, by rfl⟩ : syracuseStep 9494759 = 14242139) B14242139
theorem B6329839 : Blo 2221435 6329839 := bstep (se 1 (by rfl) ⟨4747379, by rfl⟩ : syracuseStep 6329839 = 9494759) B9494759
theorem B8439785 : Blo 2221435 8439785 := bstep (se 2 (by rfl) ⟨3164919, by rfl⟩ : syracuseStep 8439785 = 6329839) B6329839
theorem B5626523 : Blo 2221435 5626523 := bstep (se 1 (by rfl) ⟨4219892, by rfl⟩ : syracuseStep 5626523 = 8439785) B8439785
theorem B3751015 : Blo 2221435 3751015 := bstep (se 1 (by rfl) ⟨2813261, by rfl⟩ : syracuseStep 3751015 = 5626523) B5626523
theorem B5001353 : Blo 2221435 5001353 := bstep (se 2 (by rfl) ⟨1875507, by rfl⟩ : syracuseStep 5001353 = 3751015) B3751015
theorem B3334235 : Blo 2221435 3334235 := bstep (se 1 (by rfl) ⟨2500676, by rfl⟩ : syracuseStep 3334235 = 5001353) B5001353
theorem B2222823 : Blo 2221435 2222823 := bstep (se 1 (by rfl) ⟨1667117, by rfl⟩ : syracuseStep 2222823 = 3334235) B3334235
theorem B2500681 : Blo 2221435 2500681 := bbase (se 2 (by rfl) ⟨937755, by rfl⟩ : syracuseStep 2500681 = 1875511) (by norm_num)
theorem B3334241 : Blo 2221435 3334241 := bstep (se 2 (by rfl) ⟨1250340, by rfl⟩ : syracuseStep 3334241 = 2500681) B2500681
theorem B2222827 : Blo 2221435 2222827 := bstep (se 1 (by rfl) ⟨1667120, by rfl⟩ : syracuseStep 2222827 = 3334241) B3334241
theorem B5340821 : Blo 2221435 5340821 := bbase (se 6 (by rfl) ⟨125175, by rfl⟩ : syracuseStep 5340821 = 250351) (by norm_num)
theorem B14242189 : Blo 2221435 14242189 := bstep (se 3 (by rfl) ⟨2670410, by rfl⟩ : syracuseStep 14242189 = 5340821) B5340821
theorem B18989585 : Blo 2221435 18989585 := bstep (se 2 (by rfl) ⟨7121094, by rfl⟩ : syracuseStep 18989585 = 14242189) B14242189
theorem B12659723 : Blo 2221435 12659723 := bstep (se 1 (by rfl) ⟨9494792, by rfl⟩ : syracuseStep 12659723 = 18989585) B18989585
theorem B8439815 : Blo 2221435 8439815 := bstep (se 1 (by rfl) ⟨6329861, by rfl⟩ : syracuseStep 8439815 = 12659723) B12659723
theorem B5626543 : Blo 2221435 5626543 := bstep (se 1 (by rfl) ⟨4219907, by rfl⟩ : syracuseStep 5626543 = 8439815) B8439815
theorem B7502057 : Blo 2221435 7502057 := bstep (se 2 (by rfl) ⟨2813271, by rfl⟩ : syracuseStep 7502057 = 5626543) B5626543
theorem B5001371 : Blo 2221435 5001371 := bstep (se 1 (by rfl) ⟨3751028, by rfl⟩ : syracuseStep 5001371 = 7502057) B7502057
theorem B3334247 : Blo 2221435 3334247 := bstep (se 1 (by rfl) ⟨2500685, by rfl⟩ : syracuseStep 3334247 = 5001371) B5001371
theorem B2222831 : Blo 2221435 2222831 := bstep (se 1 (by rfl) ⟨1667123, by rfl⟩ : syracuseStep 2222831 = 3334247) B3334247
theorem B3334253 : Blo 2221435 3334253 := bbase (se 3 (by rfl) ⟨625172, by rfl⟩ : syracuseStep 3334253 = 1250345) (by norm_num)
theorem B2222835 : Blo 2221435 2222835 := bstep (se 1 (by rfl) ⟨1667126, by rfl⟩ : syracuseStep 2222835 = 3334253) B3334253
theorem B5001389 : Blo 2221435 5001389 := bbase (se 3 (by rfl) ⟨937760, by rfl⟩ : syracuseStep 5001389 = 1875521) (by norm_num)
theorem B3334259 : Blo 2221435 3334259 := bstep (se 1 (by rfl) ⟨2500694, by rfl⟩ : syracuseStep 3334259 = 5001389) B5001389
theorem B2222839 : Blo 2221435 2222839 := bstep (se 1 (by rfl) ⟨1667129, by rfl⟩ : syracuseStep 2222839 = 3334259) B3334259
theorem B9624389 : Blo 2221435 9624389 := bbase (se 4 (by rfl) ⟨902286, by rfl⟩ : syracuseStep 9624389 = 1804573) (by norm_num)
theorem B102660149 : Blo 2221435 102660149 := bstep (se 5 (by rfl) ⟨4812194, by rfl⟩ : syracuseStep 102660149 = 9624389) B9624389
theorem B68440099 : Blo 2221435 68440099 := bstep (se 1 (by rfl) ⟨51330074, by rfl⟩ : syracuseStep 68440099 = 102660149) B102660149
theorem B91253465 : Blo 2221435 91253465 := bstep (se 2 (by rfl) ⟨34220049, by rfl⟩ : syracuseStep 91253465 = 68440099) B68440099
theorem B60835643 : Blo 2221435 60835643 := bstep (se 1 (by rfl) ⟨45626732, by rfl⟩ : syracuseStep 60835643 = 91253465) B91253465
theorem B40557095 : Blo 2221435 40557095 := bstep (se 1 (by rfl) ⟨30417821, by rfl⟩ : syracuseStep 40557095 = 60835643) B60835643
theorem B27038063 : Blo 2221435 27038063 := bstep (se 1 (by rfl) ⟨20278547, by rfl⟩ : syracuseStep 27038063 = 40557095) B40557095
theorem B18025375 : Blo 2221435 18025375 := bstep (se 1 (by rfl) ⟨13519031, by rfl⟩ : syracuseStep 18025375 = 27038063) B27038063
theorem B24033833 : Blo 2221435 24033833 := bstep (se 2 (by rfl) ⟨9012687, by rfl⟩ : syracuseStep 24033833 = 18025375) B18025375
theorem B16022555 : Blo 2221435 16022555 := bstep (se 1 (by rfl) ⟨12016916, by rfl⟩ : syracuseStep 16022555 = 24033833) B24033833
theorem B10681703 : Blo 2221435 10681703 := bstep (se 1 (by rfl) ⟨8011277, by rfl⟩ : syracuseStep 10681703 = 16022555) B16022555
theorem B7121135 : Blo 2221435 7121135 := bstep (se 1 (by rfl) ⟨5340851, by rfl⟩ : syracuseStep 7121135 = 10681703) B10681703
theorem B4747423 : Blo 2221435 4747423 := bstep (se 1 (by rfl) ⟨3560567, by rfl⟩ : syracuseStep 4747423 = 7121135) B7121135
theorem B6329897 : Blo 2221435 6329897 := bstep (se 2 (by rfl) ⟨2373711, by rfl⟩ : syracuseStep 6329897 = 4747423) B4747423
theorem B4219931 : Blo 2221435 4219931 := bstep (se 1 (by rfl) ⟨3164948, by rfl⟩ : syracuseStep 4219931 = 6329897) B6329897
theorem B2813287 : Blo 2221435 2813287 := bstep (se 1 (by rfl) ⟨2109965, by rfl⟩ : syracuseStep 2813287 = 4219931) B4219931
theorem B3751049 : Blo 2221435 3751049 := bstep (se 2 (by rfl) ⟨1406643, by rfl⟩ : syracuseStep 3751049 = 2813287) B2813287
theorem B2500699 : Blo 2221435 2500699 := bstep (se 1 (by rfl) ⟨1875524, by rfl⟩ : syracuseStep 2500699 = 3751049) B3751049
theorem B3334265 : Blo 2221435 3334265 := bstep (se 2 (by rfl) ⟨1250349, by rfl⟩ : syracuseStep 3334265 = 2500699) B2500699
theorem B2222843 : Blo 2221435 2222843 := bstep (se 1 (by rfl) ⟨1667132, by rfl⟩ : syracuseStep 2222843 = 3334265) B3334265
theorem B5069645 : Blo 2221435 5069645 := bbase (se 3 (by rfl) ⟨950558, by rfl⟩ : syracuseStep 5069645 = 1901117) (by norm_num)
theorem B3379763 : Blo 2221435 3379763 := bstep (se 1 (by rfl) ⟨2534822, by rfl⟩ : syracuseStep 3379763 = 5069645) B5069645
theorem B9012701 : Blo 2221435 9012701 := bstep (se 3 (by rfl) ⟨1689881, by rfl⟩ : syracuseStep 9012701 = 3379763) B3379763
theorem B6008467 : Blo 2221435 6008467 := bstep (se 1 (by rfl) ⟨4506350, by rfl⟩ : syracuseStep 6008467 = 9012701) B9012701
theorem B8011289 : Blo 2221435 8011289 := bstep (se 2 (by rfl) ⟨3004233, by rfl⟩ : syracuseStep 8011289 = 6008467) B6008467
theorem B5340859 : Blo 2221435 5340859 := bstep (se 1 (by rfl) ⟨4005644, by rfl⟩ : syracuseStep 5340859 = 8011289) B8011289
theorem B28484581 : Blo 2221435 28484581 := bstep (se 4 (by rfl) ⟨2670429, by rfl⟩ : syracuseStep 28484581 = 5340859) B5340859
theorem B37979441 : Blo 2221435 37979441 := bstep (se 2 (by rfl) ⟨14242290, by rfl⟩ : syracuseStep 37979441 = 28484581) B28484581
theorem B25319627 : Blo 2221435 25319627 := bstep (se 1 (by rfl) ⟨18989720, by rfl⟩ : syracuseStep 25319627 = 37979441) B37979441
theorem B16879751 : Blo 2221435 16879751 := bstep (se 1 (by rfl) ⟨12659813, by rfl⟩ : syracuseStep 16879751 = 25319627) B25319627
theorem B11253167 : Blo 2221435 11253167 := bstep (se 1 (by rfl) ⟨8439875, by rfl⟩ : syracuseStep 11253167 = 16879751) B16879751
theorem B7502111 : Blo 2221435 7502111 := bstep (se 1 (by rfl) ⟨5626583, by rfl⟩ : syracuseStep 7502111 = 11253167) B11253167
theorem B5001407 : Blo 2221435 5001407 := bstep (se 1 (by rfl) ⟨3751055, by rfl⟩ : syracuseStep 5001407 = 7502111) B7502111
theorem B3334271 : Blo 2221435 3334271 := bstep (se 1 (by rfl) ⟨2500703, by rfl⟩ : syracuseStep 3334271 = 5001407) B5001407
theorem B2222847 : Blo 2221435 2222847 := bstep (se 1 (by rfl) ⟨1667135, by rfl⟩ : syracuseStep 2222847 = 3334271) B3334271
theorem B3334277 : Blo 2221435 3334277 := bbase (se 4 (by rfl) ⟨312588, by rfl⟩ : syracuseStep 3334277 = 625177) (by norm_num)
theorem B2222851 : Blo 2221435 2222851 := bstep (se 1 (by rfl) ⟨1667138, by rfl⟩ : syracuseStep 2222851 = 3334277) B3334277
theorem B3751069 : Blo 2221435 3751069 := bbase (se 3 (by rfl) ⟨703325, by rfl⟩ : syracuseStep 3751069 = 1406651) (by norm_num)
theorem B5001425 : Blo 2221435 5001425 := bstep (se 2 (by rfl) ⟨1875534, by rfl⟩ : syracuseStep 5001425 = 3751069) B3751069
theorem B3334283 : Blo 2221435 3334283 := bstep (se 1 (by rfl) ⟨2500712, by rfl⟩ : syracuseStep 3334283 = 5001425) B5001425
theorem B2222855 : Blo 2221435 2222855 := bstep (se 1 (by rfl) ⟨1667141, by rfl⟩ : syracuseStep 2222855 = 3334283) B3334283
theorem B2500717 : Blo 2221435 2500717 := bbase (se 3 (by rfl) ⟨468884, by rfl⟩ : syracuseStep 2500717 = 937769) (by norm_num)
theorem B3334289 : Blo 2221435 3334289 := bstep (se 2 (by rfl) ⟨1250358, by rfl⟩ : syracuseStep 3334289 = 2500717) B2500717
theorem B2222859 : Blo 2221435 2222859 := bstep (se 1 (by rfl) ⟨1667144, by rfl⟩ : syracuseStep 2222859 = 3334289) B3334289
theorem B7502165 : Blo 2221435 7502165 := bbase (se 10 (by rfl) ⟨10989, by rfl⟩ : syracuseStep 7502165 = 21979) (by norm_num)
theorem B5001443 : Blo 2221435 5001443 := bstep (se 1 (by rfl) ⟨3751082, by rfl⟩ : syracuseStep 5001443 = 7502165) B7502165
theorem B3334295 : Blo 2221435 3334295 := bstep (se 1 (by rfl) ⟨2500721, by rfl⟩ : syracuseStep 3334295 = 5001443) B5001443
theorem B2222863 : Blo 2221435 2222863 := bstep (se 1 (by rfl) ⟨1667147, by rfl⟩ : syracuseStep 2222863 = 3334295) B3334295
theorem B3334301 : Blo 2221435 3334301 := bbase (se 3 (by rfl) ⟨625181, by rfl⟩ : syracuseStep 3334301 = 1250363) (by norm_num)
theorem B2222867 : Blo 2221435 2222867 := bstep (se 1 (by rfl) ⟨1667150, by rfl⟩ : syracuseStep 2222867 = 3334301) B3334301
theorem B5001461 : Blo 2221435 5001461 := bbase (se 5 (by rfl) ⟨234443, by rfl⟩ : syracuseStep 5001461 = 468887) (by norm_num)
theorem B3334307 : Blo 2221435 3334307 := bstep (se 1 (by rfl) ⟨2500730, by rfl⟩ : syracuseStep 3334307 = 5001461) B5001461
theorem B2222871 : Blo 2221435 2222871 := bstep (se 1 (by rfl) ⟨1667153, by rfl⟩ : syracuseStep 2222871 = 3334307) B3334307
theorem B5208989 : Blo 2221435 5208989 := bbase (se 3 (by rfl) ⟨976685, by rfl⟩ : syracuseStep 5208989 = 1953371) (by norm_num)
theorem B13890637 : Blo 2221435 13890637 := bstep (se 3 (by rfl) ⟨2604494, by rfl⟩ : syracuseStep 13890637 = 5208989) B5208989
theorem B18520849 : Blo 2221435 18520849 := bstep (se 2 (by rfl) ⟨6945318, by rfl⟩ : syracuseStep 18520849 = 13890637) B13890637
theorem B24694465 : Blo 2221435 24694465 := bstep (se 2 (by rfl) ⟨9260424, by rfl⟩ : syracuseStep 24694465 = 18520849) B18520849
theorem B32925953 : Blo 2221435 32925953 := bstep (se 2 (by rfl) ⟨12347232, by rfl⟩ : syracuseStep 32925953 = 24694465) B24694465
theorem B21950635 : Blo 2221435 21950635 := bstep (se 1 (by rfl) ⟨16462976, by rfl⟩ : syracuseStep 21950635 = 32925953) B32925953
theorem B29267513 : Blo 2221435 29267513 := bstep (se 2 (by rfl) ⟨10975317, by rfl⟩ : syracuseStep 29267513 = 21950635) B21950635
theorem B19511675 : Blo 2221435 19511675 := bstep (se 1 (by rfl) ⟨14633756, by rfl⟩ : syracuseStep 19511675 = 29267513) B29267513
theorem B13007783 : Blo 2221435 13007783 := bstep (se 1 (by rfl) ⟨9755837, by rfl⟩ : syracuseStep 13007783 = 19511675) B19511675
theorem B8671855 : Blo 2221435 8671855 := bstep (se 1 (by rfl) ⟨6503891, by rfl⟩ : syracuseStep 8671855 = 13007783) B13007783
theorem B11562473 : Blo 2221435 11562473 := bstep (se 2 (by rfl) ⟨4335927, by rfl⟩ : syracuseStep 11562473 = 8671855) B8671855
theorem B7708315 : Blo 2221435 7708315 := bstep (se 1 (by rfl) ⟨5781236, by rfl⟩ : syracuseStep 7708315 = 11562473) B11562473
theorem B10277753 : Blo 2221435 10277753 := bstep (se 2 (by rfl) ⟨3854157, by rfl⟩ : syracuseStep 10277753 = 7708315) B7708315
theorem B27407341 : Blo 2221435 27407341 := bstep (se 3 (by rfl) ⟨5138876, by rfl⟩ : syracuseStep 27407341 = 10277753) B10277753
theorem B146172485 : Blo 2221435 146172485 := bstep (se 4 (by rfl) ⟨13703670, by rfl⟩ : syracuseStep 146172485 = 27407341) B27407341
theorem B389793293 : Blo 2221435 389793293 := bstep (se 3 (by rfl) ⟨73086242, by rfl⟩ : syracuseStep 389793293 = 146172485) B146172485
theorem B259862195 : Blo 2221435 259862195 := bstep (se 1 (by rfl) ⟨194896646, by rfl⟩ : syracuseStep 259862195 = 389793293) B389793293
theorem B173241463 : Blo 2221435 173241463 := bstep (se 1 (by rfl) ⟨129931097, by rfl⟩ : syracuseStep 173241463 = 259862195) B259862195
theorem B230988617 : Blo 2221435 230988617 := bstep (se 2 (by rfl) ⟨86620731, by rfl⟩ : syracuseStep 230988617 = 173241463) B173241463
theorem B153992411 : Blo 2221435 153992411 := bstep (se 1 (by rfl) ⟨115494308, by rfl⟩ : syracuseStep 153992411 = 230988617) B230988617
theorem B102661607 : Blo 2221435 102661607 := bstep (se 1 (by rfl) ⟨76996205, by rfl⟩ : syracuseStep 102661607 = 153992411) B153992411
theorem B68441071 : Blo 2221435 68441071 := bstep (se 1 (by rfl) ⟨51330803, by rfl⟩ : syracuseStep 68441071 = 102661607) B102661607
theorem B91254761 : Blo 2221435 91254761 := bstep (se 2 (by rfl) ⟨34220535, by rfl⟩ : syracuseStep 91254761 = 68441071) B68441071
theorem B60836507 : Blo 2221435 60836507 := bstep (se 1 (by rfl) ⟨45627380, by rfl⟩ : syracuseStep 60836507 = 91254761) B91254761
theorem B40557671 : Blo 2221435 40557671 := bstep (se 1 (by rfl) ⟨30418253, by rfl⟩ : syracuseStep 40557671 = 60836507) B60836507
theorem B27038447 : Blo 2221435 27038447 := bstep (se 1 (by rfl) ⟨20278835, by rfl⟩ : syracuseStep 27038447 = 40557671) B40557671
theorem B18025631 : Blo 2221435 18025631 := bstep (se 1 (by rfl) ⟨13519223, by rfl⟩ : syracuseStep 18025631 = 27038447) B27038447
theorem B12017087 : Blo 2221435 12017087 := bstep (se 1 (by rfl) ⟨9012815, by rfl⟩ : syracuseStep 12017087 = 18025631) B18025631
theorem B8011391 : Blo 2221435 8011391 := bstep (se 1 (by rfl) ⟨6008543, by rfl⟩ : syracuseStep 8011391 = 12017087) B12017087
theorem B21363709 : Blo 2221435 21363709 := bstep (se 3 (by rfl) ⟨4005695, by rfl⟩ : syracuseStep 21363709 = 8011391) B8011391
theorem B28484945 : Blo 2221435 28484945 := bstep (se 2 (by rfl) ⟨10681854, by rfl⟩ : syracuseStep 28484945 = 21363709) B21363709
theorem B18989963 : Blo 2221435 18989963 := bstep (se 1 (by rfl) ⟨14242472, by rfl⟩ : syracuseStep 18989963 = 28484945) B28484945
theorem B12659975 : Blo 2221435 12659975 := bstep (se 1 (by rfl) ⟨9494981, by rfl⟩ : syracuseStep 12659975 = 18989963) B18989963
theorem B8439983 : Blo 2221435 8439983 := bstep (se 1 (by rfl) ⟨6329987, by rfl⟩ : syracuseStep 8439983 = 12659975) B12659975
theorem B5626655 : Blo 2221435 5626655 := bstep (se 1 (by rfl) ⟨4219991, by rfl⟩ : syracuseStep 5626655 = 8439983) B8439983
theorem B3751103 : Blo 2221435 3751103 := bstep (se 1 (by rfl) ⟨2813327, by rfl⟩ : syracuseStep 3751103 = 5626655) B5626655
theorem B2500735 : Blo 2221435 2500735 := bstep (se 1 (by rfl) ⟨1875551, by rfl⟩ : syracuseStep 2500735 = 3751103) B3751103
theorem B3334313 : Blo 2221435 3334313 := bstep (se 2 (by rfl) ⟨1250367, by rfl⟩ : syracuseStep 3334313 = 2500735) B2500735
theorem B2222875 : Blo 2221435 2222875 := bstep (se 1 (by rfl) ⟨1667156, by rfl⟩ : syracuseStep 2222875 = 3334313) B3334313
theorem B11406869 : Blo 2221435 11406869 := bbase (se 6 (by rfl) ⟨267348, by rfl⟩ : syracuseStep 11406869 = 534697) (by norm_num)
theorem B7604579 : Blo 2221435 7604579 := bstep (se 1 (by rfl) ⟨5703434, by rfl⟩ : syracuseStep 7604579 = 11406869) B11406869
theorem B5069719 : Blo 2221435 5069719 := bstep (se 1 (by rfl) ⟨3802289, by rfl⟩ : syracuseStep 5069719 = 7604579) B7604579
theorem B6759625 : Blo 2221435 6759625 := bstep (se 2 (by rfl) ⟨2534859, by rfl⟩ : syracuseStep 6759625 = 5069719) B5069719
theorem B9012833 : Blo 2221435 9012833 := bstep (se 2 (by rfl) ⟨3379812, by rfl⟩ : syracuseStep 9012833 = 6759625) B6759625
theorem B6008555 : Blo 2221435 6008555 := bstep (se 1 (by rfl) ⟨4506416, by rfl⟩ : syracuseStep 6008555 = 9012833) B9012833
theorem B4005703 : Blo 2221435 4005703 := bstep (se 1 (by rfl) ⟨3004277, by rfl⟩ : syracuseStep 4005703 = 6008555) B6008555
theorem B5340937 : Blo 2221435 5340937 := bstep (se 2 (by rfl) ⟨2002851, by rfl⟩ : syracuseStep 5340937 = 4005703) B4005703
theorem B7121249 : Blo 2221435 7121249 := bstep (se 2 (by rfl) ⟨2670468, by rfl⟩ : syracuseStep 7121249 = 5340937) B5340937
theorem B4747499 : Blo 2221435 4747499 := bstep (se 1 (by rfl) ⟨3560624, by rfl⟩ : syracuseStep 4747499 = 7121249) B7121249
theorem B3164999 : Blo 2221435 3164999 := bstep (se 1 (by rfl) ⟨2373749, by rfl⟩ : syracuseStep 3164999 = 4747499) B4747499
theorem B8439997 : Blo 2221435 8439997 := bstep (se 3 (by rfl) ⟨1582499, by rfl⟩ : syracuseStep 8439997 = 3164999) B3164999
theorem B11253329 : Blo 2221435 11253329 := bstep (se 2 (by rfl) ⟨4219998, by rfl⟩ : syracuseStep 11253329 = 8439997) B8439997
theorem B7502219 : Blo 2221435 7502219 := bstep (se 1 (by rfl) ⟨5626664, by rfl⟩ : syracuseStep 7502219 = 11253329) B11253329
theorem B5001479 : Blo 2221435 5001479 := bstep (se 1 (by rfl) ⟨3751109, by rfl⟩ : syracuseStep 5001479 = 7502219) B7502219
theorem B3334319 : Blo 2221435 3334319 := bstep (se 1 (by rfl) ⟨2500739, by rfl⟩ : syracuseStep 3334319 = 5001479) B5001479
theorem B2222879 : Blo 2221435 2222879 := bstep (se 1 (by rfl) ⟨1667159, by rfl⟩ : syracuseStep 2222879 = 3334319) B3334319
theorem B3334325 : Blo 2221435 3334325 := bbase (se 5 (by rfl) ⟨156296, by rfl⟩ : syracuseStep 3334325 = 312593) (by norm_num)
theorem B2222883 : Blo 2221435 2222883 := bstep (se 1 (by rfl) ⟨1667162, by rfl⟩ : syracuseStep 2222883 = 3334325) B3334325
theorem B5626685 : Blo 2221435 5626685 := bbase (se 3 (by rfl) ⟨1055003, by rfl⟩ : syracuseStep 5626685 = 2110007) (by norm_num)
theorem B3751123 : Blo 2221435 3751123 := bstep (se 1 (by rfl) ⟨2813342, by rfl⟩ : syracuseStep 3751123 = 5626685) B5626685
theorem B5001497 : Blo 2221435 5001497 := bstep (se 2 (by rfl) ⟨1875561, by rfl⟩ : syracuseStep 5001497 = 3751123) B3751123
theorem B3334331 : Blo 2221435 3334331 := bstep (se 1 (by rfl) ⟨2500748, by rfl⟩ : syracuseStep 3334331 = 5001497) B5001497
theorem B2222887 : Blo 2221435 2222887 := bstep (se 1 (by rfl) ⟨1667165, by rfl⟩ : syracuseStep 2222887 = 3334331) B3334331
theorem B2500753 : Blo 2221435 2500753 := bbase (se 2 (by rfl) ⟨937782, by rfl⟩ : syracuseStep 2500753 = 1875565) (by norm_num)
theorem B3334337 : Blo 2221435 3334337 := bstep (se 2 (by rfl) ⟨1250376, by rfl⟩ : syracuseStep 3334337 = 2500753) B2500753
theorem B2222891 : Blo 2221435 2222891 := bstep (se 1 (by rfl) ⟨1667168, by rfl⟩ : syracuseStep 2222891 = 3334337) B3334337
theorem B4220029 : Blo 2221435 4220029 := bbase (se 3 (by rfl) ⟨791255, by rfl⟩ : syracuseStep 4220029 = 1582511) (by norm_num)
theorem B5626705 : Blo 2221435 5626705 := bstep (se 2 (by rfl) ⟨2110014, by rfl⟩ : syracuseStep 5626705 = 4220029) B4220029
theorem B7502273 : Blo 2221435 7502273 := bstep (se 2 (by rfl) ⟨2813352, by rfl⟩ : syracuseStep 7502273 = 5626705) B5626705
theorem B5001515 : Blo 2221435 5001515 := bstep (se 1 (by rfl) ⟨3751136, by rfl⟩ : syracuseStep 5001515 = 7502273) B7502273
theorem B3334343 : Blo 2221435 3334343 := bstep (se 1 (by rfl) ⟨2500757, by rfl⟩ : syracuseStep 3334343 = 5001515) B5001515
theorem B2222895 : Blo 2221435 2222895 := bstep (se 1 (by rfl) ⟨1667171, by rfl⟩ : syracuseStep 2222895 = 3334343) B3334343
theorem B3334349 : Blo 2221435 3334349 := bbase (se 3 (by rfl) ⟨625190, by rfl⟩ : syracuseStep 3334349 = 1250381) (by norm_num)
theorem B2222899 : Blo 2221435 2222899 := bstep (se 1 (by rfl) ⟨1667174, by rfl⟩ : syracuseStep 2222899 = 3334349) B3334349
theorem B5001533 : Blo 2221435 5001533 := bbase (se 3 (by rfl) ⟨937787, by rfl⟩ : syracuseStep 5001533 = 1875575) (by norm_num)
theorem B3334355 : Blo 2221435 3334355 := bstep (se 1 (by rfl) ⟨2500766, by rfl⟩ : syracuseStep 3334355 = 5001533) B5001533
theorem B2222903 : Blo 2221435 2222903 := bstep (se 1 (by rfl) ⟨1667177, by rfl⟩ : syracuseStep 2222903 = 3334355) B3334355
theorem B3751157 : Blo 2221435 3751157 := bbase (se 5 (by rfl) ⟨175835, by rfl⟩ : syracuseStep 3751157 = 351671) (by norm_num)
theorem B2500771 : Blo 2221435 2500771 := bstep (se 1 (by rfl) ⟨1875578, by rfl⟩ : syracuseStep 2500771 = 3751157) B3751157
theorem B3334361 : Blo 2221435 3334361 := bstep (se 2 (by rfl) ⟨1250385, by rfl⟩ : syracuseStep 3334361 = 2500771) B2500771
theorem B2222907 : Blo 2221435 2222907 := bstep (se 1 (by rfl) ⟨1667180, by rfl⟩ : syracuseStep 2222907 = 3334361) B3334361
theorem B15416885 : Blo 2221435 15416885 := bbase (se 5 (by rfl) ⟨722666, by rfl⟩ : syracuseStep 15416885 = 1445333) (by norm_num)
theorem B10277923 : Blo 2221435 10277923 := bstep (se 1 (by rfl) ⟨7708442, by rfl⟩ : syracuseStep 10277923 = 15416885) B15416885
theorem B13703897 : Blo 2221435 13703897 := bstep (se 2 (by rfl) ⟨5138961, by rfl⟩ : syracuseStep 13703897 = 10277923) B10277923
theorem B9135931 : Blo 2221435 9135931 := bstep (se 1 (by rfl) ⟨6851948, by rfl⟩ : syracuseStep 9135931 = 13703897) B13703897
theorem B12181241 : Blo 2221435 12181241 := bstep (se 2 (by rfl) ⟨4567965, by rfl⟩ : syracuseStep 12181241 = 9135931) B9135931
theorem B8120827 : Blo 2221435 8120827 := bstep (se 1 (by rfl) ⟨6090620, by rfl⟩ : syracuseStep 8120827 = 12181241) B12181241
theorem B10827769 : Blo 2221435 10827769 := bstep (se 2 (by rfl) ⟨4060413, by rfl⟩ : syracuseStep 10827769 = 8120827) B8120827
theorem B14437025 : Blo 2221435 14437025 := bstep (se 2 (by rfl) ⟨5413884, by rfl⟩ : syracuseStep 14437025 = 10827769) B10827769
theorem B9624683 : Blo 2221435 9624683 := bstep (se 1 (by rfl) ⟨7218512, by rfl⟩ : syracuseStep 9624683 = 14437025) B14437025
theorem B25665821 : Blo 2221435 25665821 := bstep (se 3 (by rfl) ⟨4812341, by rfl⟩ : syracuseStep 25665821 = 9624683) B9624683
theorem B17110547 : Blo 2221435 17110547 := bstep (se 1 (by rfl) ⟨12832910, by rfl⟩ : syracuseStep 17110547 = 25665821) B25665821
theorem B11407031 : Blo 2221435 11407031 := bstep (se 1 (by rfl) ⟨8555273, by rfl⟩ : syracuseStep 11407031 = 17110547) B17110547
theorem B7604687 : Blo 2221435 7604687 := bstep (se 1 (by rfl) ⟨5703515, by rfl⟩ : syracuseStep 7604687 = 11407031) B11407031
theorem B5069791 : Blo 2221435 5069791 := bstep (se 1 (by rfl) ⟨3802343, by rfl⟩ : syracuseStep 5069791 = 7604687) B7604687
theorem B6759721 : Blo 2221435 6759721 := bstep (se 2 (by rfl) ⟨2534895, by rfl⟩ : syracuseStep 6759721 = 5069791) B5069791
theorem B9012961 : Blo 2221435 9012961 := bstep (se 2 (by rfl) ⟨3379860, by rfl⟩ : syracuseStep 9012961 = 6759721) B6759721
theorem B12017281 : Blo 2221435 12017281 := bstep (se 2 (by rfl) ⟨4506480, by rfl⟩ : syracuseStep 12017281 = 9012961) B9012961
theorem B16023041 : Blo 2221435 16023041 := bstep (se 2 (by rfl) ⟨6008640, by rfl⟩ : syracuseStep 16023041 = 12017281) B12017281
theorem B10682027 : Blo 2221435 10682027 := bstep (se 1 (by rfl) ⟨8011520, by rfl⟩ : syracuseStep 10682027 = 16023041) B16023041
theorem B7121351 : Blo 2221435 7121351 := bstep (se 1 (by rfl) ⟨5341013, by rfl⟩ : syracuseStep 7121351 = 10682027) B10682027
theorem B4747567 : Blo 2221435 4747567 := bstep (se 1 (by rfl) ⟨3560675, by rfl⟩ : syracuseStep 4747567 = 7121351) B7121351
theorem B6330089 : Blo 2221435 6330089 := bstep (se 2 (by rfl) ⟨2373783, by rfl⟩ : syracuseStep 6330089 = 4747567) B4747567
theorem B16880237 : Blo 2221435 16880237 := bstep (se 3 (by rfl) ⟨3165044, by rfl⟩ : syracuseStep 16880237 = 6330089) B6330089
theorem B11253491 : Blo 2221435 11253491 := bstep (se 1 (by rfl) ⟨8440118, by rfl⟩ : syracuseStep 11253491 = 16880237) B16880237
theorem B7502327 : Blo 2221435 7502327 := bstep (se 1 (by rfl) ⟨5626745, by rfl⟩ : syracuseStep 7502327 = 11253491) B11253491
theorem B5001551 : Blo 2221435 5001551 := bstep (se 1 (by rfl) ⟨3751163, by rfl⟩ : syracuseStep 5001551 = 7502327) B7502327
theorem B3334367 : Blo 2221435 3334367 := bstep (se 1 (by rfl) ⟨2500775, by rfl⟩ : syracuseStep 3334367 = 5001551) B5001551
theorem B2222911 : Blo 2221435 2222911 := bstep (se 1 (by rfl) ⟨1667183, by rfl⟩ : syracuseStep 2222911 = 3334367) B3334367
theorem B3334373 : Blo 2221435 3334373 := bbase (se 4 (by rfl) ⟨312597, by rfl⟩ : syracuseStep 3334373 = 625195) (by norm_num)
theorem B2222915 : Blo 2221435 2222915 := bstep (se 1 (by rfl) ⟨1667186, by rfl⟩ : syracuseStep 2222915 = 3334373) B3334373
theorem B2670517 : Blo 2221435 2670517 := bbase (se 5 (by rfl) ⟨125180, by rfl⟩ : syracuseStep 2670517 = 250361) (by norm_num)
theorem B3560689 : Blo 2221435 3560689 := bstep (se 2 (by rfl) ⟨1335258, by rfl⟩ : syracuseStep 3560689 = 2670517) B2670517
theorem B4747585 : Blo 2221435 4747585 := bstep (se 2 (by rfl) ⟨1780344, by rfl⟩ : syracuseStep 4747585 = 3560689) B3560689
theorem B6330113 : Blo 2221435 6330113 := bstep (se 2 (by rfl) ⟨2373792, by rfl⟩ : syracuseStep 6330113 = 4747585) B4747585
theorem B4220075 : Blo 2221435 4220075 := bstep (se 1 (by rfl) ⟨3165056, by rfl⟩ : syracuseStep 4220075 = 6330113) B6330113
theorem B2813383 : Blo 2221435 2813383 := bstep (se 1 (by rfl) ⟨2110037, by rfl⟩ : syracuseStep 2813383 = 4220075) B4220075
theorem B3751177 : Blo 2221435 3751177 := bstep (se 2 (by rfl) ⟨1406691, by rfl⟩ : syracuseStep 3751177 = 2813383) B2813383
theorem B5001569 : Blo 2221435 5001569 := bstep (se 2 (by rfl) ⟨1875588, by rfl⟩ : syracuseStep 5001569 = 3751177) B3751177
theorem B3334379 : Blo 2221435 3334379 := bstep (se 1 (by rfl) ⟨2500784, by rfl⟩ : syracuseStep 3334379 = 5001569) B5001569
theorem B2222919 : Blo 2221435 2222919 := bstep (se 1 (by rfl) ⟨1667189, by rfl⟩ : syracuseStep 2222919 = 3334379) B3334379
theorem B2500789 : Blo 2221435 2500789 := bbase (se 5 (by rfl) ⟨117224, by rfl⟩ : syracuseStep 2500789 = 234449) (by norm_num)
theorem B3334385 : Blo 2221435 3334385 := bstep (se 2 (by rfl) ⟨1250394, by rfl⟩ : syracuseStep 3334385 = 2500789) B2500789
theorem B2222923 : Blo 2221435 2222923 := bstep (se 1 (by rfl) ⟨1667192, by rfl⟩ : syracuseStep 2222923 = 3334385) B3334385
theorem B2813393 : Blo 2221435 2813393 := bbase (se 2 (by rfl) ⟨1055022, by rfl⟩ : syracuseStep 2813393 = 2110045) (by norm_num)
theorem B7502381 : Blo 2221435 7502381 := bstep (se 3 (by rfl) ⟨1406696, by rfl⟩ : syracuseStep 7502381 = 2813393) B2813393
theorem B5001587 : Blo 2221435 5001587 := bstep (se 1 (by rfl) ⟨3751190, by rfl⟩ : syracuseStep 5001587 = 7502381) B7502381
theorem B3334391 : Blo 2221435 3334391 := bstep (se 1 (by rfl) ⟨2500793, by rfl⟩ : syracuseStep 3334391 = 5001587) B5001587
theorem B2222927 : Blo 2221435 2222927 := bstep (se 1 (by rfl) ⟨1667195, by rfl⟩ : syracuseStep 2222927 = 3334391) B3334391
theorem B3334397 : Blo 2221435 3334397 := bbase (se 3 (by rfl) ⟨625199, by rfl⟩ : syracuseStep 3334397 = 1250399) (by norm_num)
theorem B2222931 : Blo 2221435 2222931 := bstep (se 1 (by rfl) ⟨1667198, by rfl⟩ : syracuseStep 2222931 = 3334397) B3334397
theorem B5001605 : Blo 2221435 5001605 := bbase (se 4 (by rfl) ⟨468900, by rfl⟩ : syracuseStep 5001605 = 937801) (by norm_num)
theorem B3334403 : Blo 2221435 3334403 := bstep (se 1 (by rfl) ⟨2500802, by rfl⟩ : syracuseStep 3334403 = 5001605) B5001605
theorem B2222935 : Blo 2221435 2222935 := bstep (se 1 (by rfl) ⟨1667201, by rfl⟩ : syracuseStep 2222935 = 3334403) B3334403
theorem B3165085 : Blo 2221435 3165085 := bbase (se 3 (by rfl) ⟨593453, by rfl⟩ : syracuseStep 3165085 = 1186907) (by norm_num)
theorem B4220113 : Blo 2221435 4220113 := bstep (se 2 (by rfl) ⟨1582542, by rfl⟩ : syracuseStep 4220113 = 3165085) B3165085
theorem B5626817 : Blo 2221435 5626817 := bstep (se 2 (by rfl) ⟨2110056, by rfl⟩ : syracuseStep 5626817 = 4220113) B4220113
theorem B3751211 : Blo 2221435 3751211 := bstep (se 1 (by rfl) ⟨2813408, by rfl⟩ : syracuseStep 3751211 = 5626817) B5626817
theorem B2500807 : Blo 2221435 2500807 := bstep (se 1 (by rfl) ⟨1875605, by rfl⟩ : syracuseStep 2500807 = 3751211) B3751211
theorem B3334409 : Blo 2221435 3334409 := bstep (se 2 (by rfl) ⟨1250403, by rfl⟩ : syracuseStep 3334409 = 2500807) B2500807
theorem B2222939 : Blo 2221435 2222939 := bstep (se 1 (by rfl) ⟨1667204, by rfl⟩ : syracuseStep 2222939 = 3334409) B3334409
theorem B11253653 : Blo 2221435 11253653 := bbase (se 6 (by rfl) ⟨263757, by rfl⟩ : syracuseStep 11253653 = 527515) (by norm_num)
theorem B7502435 : Blo 2221435 7502435 := bstep (se 1 (by rfl) ⟨5626826, by rfl⟩ : syracuseStep 7502435 = 11253653) B11253653
theorem B5001623 : Blo 2221435 5001623 := bstep (se 1 (by rfl) ⟨3751217, by rfl⟩ : syracuseStep 5001623 = 7502435) B7502435
theorem B3334415 : Blo 2221435 3334415 := bstep (se 1 (by rfl) ⟨2500811, by rfl⟩ : syracuseStep 3334415 = 5001623) B5001623
theorem B2222943 : Blo 2221435 2222943 := bstep (se 1 (by rfl) ⟨1667207, by rfl⟩ : syracuseStep 2222943 = 3334415) B3334415
theorem B3334421 : Blo 2221435 3334421 := bbase (se 6 (by rfl) ⟨78150, by rfl⟩ : syracuseStep 3334421 = 156301) (by norm_num)
theorem B2222947 : Blo 2221435 2222947 := bstep (se 1 (by rfl) ⟨1667210, by rfl⟩ : syracuseStep 2222947 = 3334421) B3334421
theorem B2534941 : Blo 2221435 2534941 := bbase (se 3 (by rfl) ⟨475301, by rfl⟩ : syracuseStep 2534941 = 950603) (by norm_num)
theorem B13519685 : Blo 2221435 13519685 := bstep (se 4 (by rfl) ⟨1267470, by rfl⟩ : syracuseStep 13519685 = 2534941) B2534941
theorem B9013123 : Blo 2221435 9013123 := bstep (se 1 (by rfl) ⟨6759842, by rfl⟩ : syracuseStep 9013123 = 13519685) B13519685
theorem B12017497 : Blo 2221435 12017497 := bstep (se 2 (by rfl) ⟨4506561, by rfl⟩ : syracuseStep 12017497 = 9013123) B9013123
theorem B16023329 : Blo 2221435 16023329 := bstep (se 2 (by rfl) ⟨6008748, by rfl⟩ : syracuseStep 16023329 = 12017497) B12017497
theorem B10682219 : Blo 2221435 10682219 := bstep (se 1 (by rfl) ⟨8011664, by rfl⟩ : syracuseStep 10682219 = 16023329) B16023329
theorem B28485917 : Blo 2221435 28485917 := bstep (se 3 (by rfl) ⟨5341109, by rfl⟩ : syracuseStep 28485917 = 10682219) B10682219
theorem B18990611 : Blo 2221435 18990611 := bstep (se 1 (by rfl) ⟨14242958, by rfl⟩ : syracuseStep 18990611 = 28485917) B28485917
theorem B12660407 : Blo 2221435 12660407 := bstep (se 1 (by rfl) ⟨9495305, by rfl⟩ : syracuseStep 12660407 = 18990611) B18990611
theorem B8440271 : Blo 2221435 8440271 := bstep (se 1 (by rfl) ⟨6330203, by rfl⟩ : syracuseStep 8440271 = 12660407) B12660407
theorem B5626847 : Blo 2221435 5626847 := bstep (se 1 (by rfl) ⟨4220135, by rfl⟩ : syracuseStep 5626847 = 8440271) B8440271
theorem B3751231 : Blo 2221435 3751231 := bstep (se 1 (by rfl) ⟨2813423, by rfl⟩ : syracuseStep 3751231 = 5626847) B5626847
theorem B5001641 : Blo 2221435 5001641 := bstep (se 2 (by rfl) ⟨1875615, by rfl⟩ : syracuseStep 5001641 = 3751231) B3751231
theorem B3334427 : Blo 2221435 3334427 := bstep (se 1 (by rfl) ⟨2500820, by rfl⟩ : syracuseStep 3334427 = 5001641) B5001641
theorem B2222951 : Blo 2221435 2222951 := bstep (se 1 (by rfl) ⟨1667213, by rfl⟩ : syracuseStep 2222951 = 3334427) B3334427
theorem B2500825 : Blo 2221435 2500825 := bbase (se 2 (by rfl) ⟨937809, by rfl⟩ : syracuseStep 2500825 = 1875619) (by norm_num)
theorem B3334433 : Blo 2221435 3334433 := bstep (se 2 (by rfl) ⟨1250412, by rfl⟩ : syracuseStep 3334433 = 2500825) B2500825
theorem B2222955 : Blo 2221435 2222955 := bstep (se 1 (by rfl) ⟨1667216, by rfl⟩ : syracuseStep 2222955 = 3334433) B3334433
theorem B2670565 : Blo 2221435 2670565 := bbase (se 4 (by rfl) ⟨250365, by rfl⟩ : syracuseStep 2670565 = 500731) (by norm_num)
theorem B3560753 : Blo 2221435 3560753 := bstep (se 2 (by rfl) ⟨1335282, by rfl⟩ : syracuseStep 3560753 = 2670565) B2670565
theorem B2373835 : Blo 2221435 2373835 := bstep (se 1 (by rfl) ⟨1780376, by rfl⟩ : syracuseStep 2373835 = 3560753) B3560753
theorem B3165113 : Blo 2221435 3165113 := bstep (se 2 (by rfl) ⟨1186917, by rfl⟩ : syracuseStep 3165113 = 2373835) B2373835
theorem B8440301 : Blo 2221435 8440301 := bstep (se 3 (by rfl) ⟨1582556, by rfl⟩ : syracuseStep 8440301 = 3165113) B3165113
theorem B5626867 : Blo 2221435 5626867 := bstep (se 1 (by rfl) ⟨4220150, by rfl⟩ : syracuseStep 5626867 = 8440301) B8440301
theorem B7502489 : Blo 2221435 7502489 := bstep (se 2 (by rfl) ⟨2813433, by rfl⟩ : syracuseStep 7502489 = 5626867) B5626867
theorem B5001659 : Blo 2221435 5001659 := bstep (se 1 (by rfl) ⟨3751244, by rfl⟩ : syracuseStep 5001659 = 7502489) B7502489
theorem B3334439 : Blo 2221435 3334439 := bstep (se 1 (by rfl) ⟨2500829, by rfl⟩ : syracuseStep 3334439 = 5001659) B5001659
theorem B2222959 : Blo 2221435 2222959 := bstep (se 1 (by rfl) ⟨1667219, by rfl⟩ : syracuseStep 2222959 = 3334439) B3334439
theorem B3334445 : Blo 2221435 3334445 := bbase (se 3 (by rfl) ⟨625208, by rfl⟩ : syracuseStep 3334445 = 1250417) (by norm_num)
theorem B2222963 : Blo 2221435 2222963 := bstep (se 1 (by rfl) ⟨1667222, by rfl⟩ : syracuseStep 2222963 = 3334445) B3334445
theorem B5001677 : Blo 2221435 5001677 := bbase (se 3 (by rfl) ⟨937814, by rfl⟩ : syracuseStep 5001677 = 1875629) (by norm_num)
theorem B3334451 : Blo 2221435 3334451 := bstep (se 1 (by rfl) ⟨2500838, by rfl⟩ : syracuseStep 3334451 = 5001677) B5001677
theorem B2222967 : Blo 2221435 2222967 := bstep (se 1 (by rfl) ⟨1667225, by rfl⟩ : syracuseStep 2222967 = 3334451) B3334451
theorem B2813449 : Blo 2221435 2813449 := bbase (se 2 (by rfl) ⟨1055043, by rfl⟩ : syracuseStep 2813449 = 2110087) (by norm_num)
theorem B3751265 : Blo 2221435 3751265 := bstep (se 2 (by rfl) ⟨1406724, by rfl⟩ : syracuseStep 3751265 = 2813449) B2813449
theorem B2500843 : Blo 2221435 2500843 := bstep (se 1 (by rfl) ⟨1875632, by rfl⟩ : syracuseStep 2500843 = 3751265) B3751265
theorem B3334457 : Blo 2221435 3334457 := bstep (se 2 (by rfl) ⟨1250421, by rfl⟩ : syracuseStep 3334457 = 2500843) B2500843
theorem B2222971 : Blo 2221435 2222971 := bstep (se 1 (by rfl) ⟨1667228, by rfl⟩ : syracuseStep 2222971 = 3334457) B3334457
theorem B13519829 : Blo 2221435 13519829 := bbase (se 7 (by rfl) ⟨158435, by rfl⟩ : syracuseStep 13519829 = 316871) (by norm_num)
theorem B36052877 : Blo 2221435 36052877 := bstep (se 3 (by rfl) ⟨6759914, by rfl⟩ : syracuseStep 36052877 = 13519829) B13519829
theorem B24035251 : Blo 2221435 24035251 := bstep (se 1 (by rfl) ⟨18026438, by rfl⟩ : syracuseStep 24035251 = 36052877) B36052877
theorem B32047001 : Blo 2221435 32047001 := bstep (se 2 (by rfl) ⟨12017625, by rfl⟩ : syracuseStep 32047001 = 24035251) B24035251
theorem B21364667 : Blo 2221435 21364667 := bstep (se 1 (by rfl) ⟨16023500, by rfl⟩ : syracuseStep 21364667 = 32047001) B32047001
theorem B14243111 : Blo 2221435 14243111 := bstep (se 1 (by rfl) ⟨10682333, by rfl⟩ : syracuseStep 14243111 = 21364667) B21364667
theorem B9495407 : Blo 2221435 9495407 := bstep (se 1 (by rfl) ⟨7121555, by rfl⟩ : syracuseStep 9495407 = 14243111) B14243111
theorem B25321085 : Blo 2221435 25321085 := bstep (se 3 (by rfl) ⟨4747703, by rfl⟩ : syracuseStep 25321085 = 9495407) B9495407
theorem B16880723 : Blo 2221435 16880723 := bstep (se 1 (by rfl) ⟨12660542, by rfl⟩ : syracuseStep 16880723 = 25321085) B25321085
theorem B11253815 : Blo 2221435 11253815 := bstep (se 1 (by rfl) ⟨8440361, by rfl⟩ : syracuseStep 11253815 = 16880723) B16880723
theorem B7502543 : Blo 2221435 7502543 := bstep (se 1 (by rfl) ⟨5626907, by rfl⟩ : syracuseStep 7502543 = 11253815) B11253815
theorem B5001695 : Blo 2221435 5001695 := bstep (se 1 (by rfl) ⟨3751271, by rfl⟩ : syracuseStep 5001695 = 7502543) B7502543
theorem B3334463 : Blo 2221435 3334463 := bstep (se 1 (by rfl) ⟨2500847, by rfl⟩ : syracuseStep 3334463 = 5001695) B5001695
theorem B2222975 : Blo 2221435 2222975 := bstep (se 1 (by rfl) ⟨1667231, by rfl⟩ : syracuseStep 2222975 = 3334463) B3334463
theorem B3334469 : Blo 2221435 3334469 := bbase (se 4 (by rfl) ⟨312606, by rfl⟩ : syracuseStep 3334469 = 625213) (by norm_num)
theorem B2222979 : Blo 2221435 2222979 := bstep (se 1 (by rfl) ⟨1667234, by rfl⟩ : syracuseStep 2222979 = 3334469) B3334469
theorem B3751285 : Blo 2221435 3751285 := bbase (se 5 (by rfl) ⟨175841, by rfl⟩ : syracuseStep 3751285 = 351683) (by norm_num)
theorem B5001713 : Blo 2221435 5001713 := bstep (se 2 (by rfl) ⟨1875642, by rfl⟩ : syracuseStep 5001713 = 3751285) B3751285
theorem B3334475 : Blo 2221435 3334475 := bstep (se 1 (by rfl) ⟨2500856, by rfl⟩ : syracuseStep 3334475 = 5001713) B5001713
theorem B2222983 : Blo 2221435 2222983 := bstep (se 1 (by rfl) ⟨1667237, by rfl⟩ : syracuseStep 2222983 = 3334475) B3334475
theorem B2500861 : Blo 2221435 2500861 := bbase (se 3 (by rfl) ⟨468911, by rfl⟩ : syracuseStep 2500861 = 937823) (by norm_num)
theorem B3334481 : Blo 2221435 3334481 := bstep (se 2 (by rfl) ⟨1250430, by rfl⟩ : syracuseStep 3334481 = 2500861) B2500861
theorem B2222987 : Blo 2221435 2222987 := bstep (se 1 (by rfl) ⟨1667240, by rfl⟩ : syracuseStep 2222987 = 3334481) B3334481
theorem B7502597 : Blo 2221435 7502597 := bbase (se 4 (by rfl) ⟨703368, by rfl⟩ : syracuseStep 7502597 = 1406737) (by norm_num)
theorem B5001731 : Blo 2221435 5001731 := bstep (se 1 (by rfl) ⟨3751298, by rfl⟩ : syracuseStep 5001731 = 7502597) B7502597
theorem B3334487 : Blo 2221435 3334487 := bstep (se 1 (by rfl) ⟨2500865, by rfl⟩ : syracuseStep 3334487 = 5001731) B5001731
theorem B2222991 : Blo 2221435 2222991 := bstep (se 1 (by rfl) ⟨1667243, by rfl⟩ : syracuseStep 2222991 = 3334487) B3334487
theorem B3334493 : Blo 2221435 3334493 := bbase (se 3 (by rfl) ⟨625217, by rfl⟩ : syracuseStep 3334493 = 1250435) (by norm_num)
theorem B2222995 : Blo 2221435 2222995 := bstep (se 1 (by rfl) ⟨1667246, by rfl⟩ : syracuseStep 2222995 = 3334493) B3334493
theorem B5001749 : Blo 2221435 5001749 := bbase (se 6 (by rfl) ⟨117228, by rfl⟩ : syracuseStep 5001749 = 234457) (by norm_num)
theorem B3334499 : Blo 2221435 3334499 := bstep (se 1 (by rfl) ⟨2500874, by rfl⟩ : syracuseStep 3334499 = 5001749) B5001749
theorem B2222999 : Blo 2221435 2222999 := bstep (se 1 (by rfl) ⟨1667249, by rfl⟩ : syracuseStep 2222999 = 3334499) B3334499
theorem B8440469 : Blo 2221435 8440469 := bbase (se 6 (by rfl) ⟨197823, by rfl⟩ : syracuseStep 8440469 = 395647) (by norm_num)
theorem B5626979 : Blo 2221435 5626979 := bstep (se 1 (by rfl) ⟨4220234, by rfl⟩ : syracuseStep 5626979 = 8440469) B8440469
theorem B3751319 : Blo 2221435 3751319 := bstep (se 1 (by rfl) ⟨2813489, by rfl⟩ : syracuseStep 3751319 = 5626979) B5626979
theorem B2500879 : Blo 2221435 2500879 := bstep (se 1 (by rfl) ⟨1875659, by rfl⟩ : syracuseStep 2500879 = 3751319) B3751319
theorem B3334505 : Blo 2221435 3334505 := bstep (se 2 (by rfl) ⟨1250439, by rfl⟩ : syracuseStep 3334505 = 2500879) B2500879
theorem B2223003 : Blo 2221435 2223003 := bstep (se 1 (by rfl) ⟨1667252, by rfl⟩ : syracuseStep 2223003 = 3334505) B3334505
theorem B12660725 : Blo 2221435 12660725 := bbase (se 5 (by rfl) ⟨593471, by rfl⟩ : syracuseStep 12660725 = 1186943) (by norm_num)
theorem B8440483 : Blo 2221435 8440483 := bstep (se 1 (by rfl) ⟨6330362, by rfl⟩ : syracuseStep 8440483 = 12660725) B12660725
theorem B11253977 : Blo 2221435 11253977 := bstep (se 2 (by rfl) ⟨4220241, by rfl⟩ : syracuseStep 11253977 = 8440483) B8440483
theorem B7502651 : Blo 2221435 7502651 := bstep (se 1 (by rfl) ⟨5626988, by rfl⟩ : syracuseStep 7502651 = 11253977) B11253977
theorem B5001767 : Blo 2221435 5001767 := bstep (se 1 (by rfl) ⟨3751325, by rfl⟩ : syracuseStep 5001767 = 7502651) B7502651
theorem B3334511 : Blo 2221435 3334511 := bstep (se 1 (by rfl) ⟨2500883, by rfl⟩ : syracuseStep 3334511 = 5001767) B5001767
theorem B2223007 : Blo 2221435 2223007 := bstep (se 1 (by rfl) ⟨1667255, by rfl⟩ : syracuseStep 2223007 = 3334511) B3334511
theorem B3334517 : Blo 2221435 3334517 := bbase (se 5 (by rfl) ⟨156305, by rfl⟩ : syracuseStep 3334517 = 312611) (by norm_num)
theorem B2223011 : Blo 2221435 2223011 := bstep (se 1 (by rfl) ⟨1667258, by rfl⟩ : syracuseStep 2223011 = 3334517) B3334517
theorem B4005949 : Blo 2221435 4005949 := bbase (se 3 (by rfl) ⟨751115, by rfl⟩ : syracuseStep 4005949 = 1502231) (by norm_num)
theorem B5341265 : Blo 2221435 5341265 := bstep (se 2 (by rfl) ⟨2002974, by rfl⟩ : syracuseStep 5341265 = 4005949) B4005949
theorem B3560843 : Blo 2221435 3560843 := bstep (se 1 (by rfl) ⟨2670632, by rfl⟩ : syracuseStep 3560843 = 5341265) B5341265
theorem B2373895 : Blo 2221435 2373895 := bstep (se 1 (by rfl) ⟨1780421, by rfl⟩ : syracuseStep 2373895 = 3560843) B3560843
theorem B3165193 : Blo 2221435 3165193 := bstep (se 2 (by rfl) ⟨1186947, by rfl⟩ : syracuseStep 3165193 = 2373895) B2373895
theorem B4220257 : Blo 2221435 4220257 := bstep (se 2 (by rfl) ⟨1582596, by rfl⟩ : syracuseStep 4220257 = 3165193) B3165193
theorem B5627009 : Blo 2221435 5627009 := bstep (se 2 (by rfl) ⟨2110128, by rfl⟩ : syracuseStep 5627009 = 4220257) B4220257
theorem B3751339 : Blo 2221435 3751339 := bstep (se 1 (by rfl) ⟨2813504, by rfl⟩ : syracuseStep 3751339 = 5627009) B5627009
theorem B5001785 : Blo 2221435 5001785 := bstep (se 2 (by rfl) ⟨1875669, by rfl⟩ : syracuseStep 5001785 = 3751339) B3751339
theorem B3334523 : Blo 2221435 3334523 := bstep (se 1 (by rfl) ⟨2500892, by rfl⟩ : syracuseStep 3334523 = 5001785) B5001785
theorem B2223015 : Blo 2221435 2223015 := bstep (se 1 (by rfl) ⟨1667261, by rfl⟩ : syracuseStep 2223015 = 3334523) B3334523
theorem B2500897 : Blo 2221435 2500897 := bbase (se 2 (by rfl) ⟨937836, by rfl⟩ : syracuseStep 2500897 = 1875673) (by norm_num)
theorem B3334529 : Blo 2221435 3334529 := bstep (se 2 (by rfl) ⟨1250448, by rfl⟩ : syracuseStep 3334529 = 2500897) B2500897
theorem B2223019 : Blo 2221435 2223019 := bstep (se 1 (by rfl) ⟨1667264, by rfl⟩ : syracuseStep 2223019 = 3334529) B3334529
theorem B5627029 : Blo 2221435 5627029 := bbase (se 6 (by rfl) ⟨131883, by rfl⟩ : syracuseStep 5627029 = 263767) (by norm_num)
theorem B7502705 : Blo 2221435 7502705 := bstep (se 2 (by rfl) ⟨2813514, by rfl⟩ : syracuseStep 7502705 = 5627029) B5627029
theorem B5001803 : Blo 2221435 5001803 := bstep (se 1 (by rfl) ⟨3751352, by rfl⟩ : syracuseStep 5001803 = 7502705) B7502705
theorem B3334535 : Blo 2221435 3334535 := bstep (se 1 (by rfl) ⟨2500901, by rfl⟩ : syracuseStep 3334535 = 5001803) B5001803
theorem B2223023 : Blo 2221435 2223023 := bstep (se 1 (by rfl) ⟨1667267, by rfl⟩ : syracuseStep 2223023 = 3334535) B3334535
theorem B3334541 : Blo 2221435 3334541 := bbase (se 3 (by rfl) ⟨625226, by rfl⟩ : syracuseStep 3334541 = 1250453) (by norm_num)
theorem B2223027 : Blo 2221435 2223027 := bstep (se 1 (by rfl) ⟨1667270, by rfl⟩ : syracuseStep 2223027 = 3334541) B3334541
theorem B5001821 : Blo 2221435 5001821 := bbase (se 3 (by rfl) ⟨937841, by rfl⟩ : syracuseStep 5001821 = 1875683) (by norm_num)
theorem B3334547 : Blo 2221435 3334547 := bstep (se 1 (by rfl) ⟨2500910, by rfl⟩ : syracuseStep 3334547 = 5001821) B5001821
theorem B2223031 : Blo 2221435 2223031 := bstep (se 1 (by rfl) ⟨1667273, by rfl⟩ : syracuseStep 2223031 = 3334547) B3334547
theorem B3751373 : Blo 2221435 3751373 := bbase (se 3 (by rfl) ⟨703382, by rfl⟩ : syracuseStep 3751373 = 1406765) (by norm_num)
theorem B2500915 : Blo 2221435 2500915 := bstep (se 1 (by rfl) ⟨1875686, by rfl⟩ : syracuseStep 2500915 = 3751373) B3751373
theorem B3334553 : Blo 2221435 3334553 := bstep (se 2 (by rfl) ⟨1250457, by rfl⟩ : syracuseStep 3334553 = 2500915) B2500915
theorem B2223035 : Blo 2221435 2223035 := bstep (se 1 (by rfl) ⟨1667276, by rfl⟩ : syracuseStep 2223035 = 3334553) B3334553
theorem B3004493 : Blo 2221435 3004493 := bbase (se 3 (by rfl) ⟨563342, by rfl⟩ : syracuseStep 3004493 = 1126685) (by norm_num)
theorem B8011981 : Blo 2221435 8011981 := bstep (se 3 (by rfl) ⟨1502246, by rfl⟩ : syracuseStep 8011981 = 3004493) B3004493
theorem B10682641 : Blo 2221435 10682641 := bstep (se 2 (by rfl) ⟨4005990, by rfl⟩ : syracuseStep 10682641 = 8011981) B8011981
theorem B14243521 : Blo 2221435 14243521 := bstep (se 2 (by rfl) ⟨5341320, by rfl⟩ : syracuseStep 14243521 = 10682641) B10682641
theorem B18991361 : Blo 2221435 18991361 := bstep (se 2 (by rfl) ⟨7121760, by rfl⟩ : syracuseStep 18991361 = 14243521) B14243521
theorem B12660907 : Blo 2221435 12660907 := bstep (se 1 (by rfl) ⟨9495680, by rfl⟩ : syracuseStep 12660907 = 18991361) B18991361
theorem B16881209 : Blo 2221435 16881209 := bstep (se 2 (by rfl) ⟨6330453, by rfl⟩ : syracuseStep 16881209 = 12660907) B12660907
theorem B11254139 : Blo 2221435 11254139 := bstep (se 1 (by rfl) ⟨8440604, by rfl⟩ : syracuseStep 11254139 = 16881209) B16881209
theorem B7502759 : Blo 2221435 7502759 := bstep (se 1 (by rfl) ⟨5627069, by rfl⟩ : syracuseStep 7502759 = 11254139) B11254139
theorem B5001839 : Blo 2221435 5001839 := bstep (se 1 (by rfl) ⟨3751379, by rfl⟩ : syracuseStep 5001839 = 7502759) B7502759
theorem B3334559 : Blo 2221435 3334559 := bstep (se 1 (by rfl) ⟨2500919, by rfl⟩ : syracuseStep 3334559 = 5001839) B5001839
theorem B2223039 : Blo 2221435 2223039 := bstep (se 1 (by rfl) ⟨1667279, by rfl⟩ : syracuseStep 2223039 = 3334559) B3334559
theorem B3334565 : Blo 2221435 3334565 := bbase (se 4 (by rfl) ⟨312615, by rfl⟩ : syracuseStep 3334565 = 625231) (by norm_num)
theorem B2223043 : Blo 2221435 2223043 := bstep (se 1 (by rfl) ⟨1667282, by rfl⟩ : syracuseStep 2223043 = 3334565) B3334565
theorem B2813545 : Blo 2221435 2813545 := bbase (se 2 (by rfl) ⟨1055079, by rfl⟩ : syracuseStep 2813545 = 2110159) (by norm_num)
theorem B3751393 : Blo 2221435 3751393 := bstep (se 2 (by rfl) ⟨1406772, by rfl⟩ : syracuseStep 3751393 = 2813545) B2813545
theorem B5001857 : Blo 2221435 5001857 := bstep (se 2 (by rfl) ⟨1875696, by rfl⟩ : syracuseStep 5001857 = 3751393) B3751393
theorem B3334571 : Blo 2221435 3334571 := bstep (se 1 (by rfl) ⟨2500928, by rfl⟩ : syracuseStep 3334571 = 5001857) B5001857
theorem B2223047 : Blo 2221435 2223047 := bstep (se 1 (by rfl) ⟨1667285, by rfl⟩ : syracuseStep 2223047 = 3334571) B3334571
theorem B2500933 : Blo 2221435 2500933 := bbase (se 4 (by rfl) ⟨234462, by rfl⟩ : syracuseStep 2500933 = 468925) (by norm_num)
theorem B3334577 : Blo 2221435 3334577 := bstep (se 2 (by rfl) ⟨1250466, by rfl⟩ : syracuseStep 3334577 = 2500933) B2500933
theorem B2223051 : Blo 2221435 2223051 := bstep (se 1 (by rfl) ⟨1667288, by rfl⟩ : syracuseStep 2223051 = 3334577) B3334577
theorem B4220333 : Blo 2221435 4220333 := bbase (se 3 (by rfl) ⟨791312, by rfl⟩ : syracuseStep 4220333 = 1582625) (by norm_num)
theorem B2813555 : Blo 2221435 2813555 := bstep (se 1 (by rfl) ⟨2110166, by rfl⟩ : syracuseStep 2813555 = 4220333) B4220333
theorem B7502813 : Blo 2221435 7502813 := bstep (se 3 (by rfl) ⟨1406777, by rfl⟩ : syracuseStep 7502813 = 2813555) B2813555
theorem B5001875 : Blo 2221435 5001875 := bstep (se 1 (by rfl) ⟨3751406, by rfl⟩ : syracuseStep 5001875 = 7502813) B7502813
theorem B3334583 : Blo 2221435 3334583 := bstep (se 1 (by rfl) ⟨2500937, by rfl⟩ : syracuseStep 3334583 = 5001875) B5001875
theorem B2223055 : Blo 2221435 2223055 := bstep (se 1 (by rfl) ⟨1667291, by rfl⟩ : syracuseStep 2223055 = 3334583) B3334583
theorem B3334589 : Blo 2221435 3334589 := bbase (se 3 (by rfl) ⟨625235, by rfl⟩ : syracuseStep 3334589 = 1250471) (by norm_num)
theorem B2223059 : Blo 2221435 2223059 := bstep (se 1 (by rfl) ⟨1667294, by rfl⟩ : syracuseStep 2223059 = 3334589) B3334589
theorem B5001893 : Blo 2221435 5001893 := bbase (se 4 (by rfl) ⟨468927, by rfl⟩ : syracuseStep 5001893 = 937855) (by norm_num)
theorem B3334595 : Blo 2221435 3334595 := bstep (se 1 (by rfl) ⟨2500946, by rfl⟩ : syracuseStep 3334595 = 5001893) B5001893
theorem B2223063 : Blo 2221435 2223063 := bstep (se 1 (by rfl) ⟨1667297, by rfl⟩ : syracuseStep 2223063 = 3334595) B3334595
theorem B5627141 : Blo 2221435 5627141 := bbase (se 4 (by rfl) ⟨527544, by rfl⟩ : syracuseStep 5627141 = 1055089) (by norm_num)
theorem B3751427 : Blo 2221435 3751427 := bstep (se 1 (by rfl) ⟨2813570, by rfl⟩ : syracuseStep 3751427 = 5627141) B5627141
theorem B2500951 : Blo 2221435 2500951 := bstep (se 1 (by rfl) ⟨1875713, by rfl⟩ : syracuseStep 2500951 = 3751427) B3751427
theorem B3334601 : Blo 2221435 3334601 := bstep (se 2 (by rfl) ⟨1250475, by rfl⟩ : syracuseStep 3334601 = 2500951) B2500951
theorem B2223067 : Blo 2221435 2223067 := bstep (se 1 (by rfl) ⟨1667300, by rfl⟩ : syracuseStep 2223067 = 3334601) B3334601
theorem B4747909 : Blo 2221435 4747909 := bbase (se 4 (by rfl) ⟨445116, by rfl⟩ : syracuseStep 4747909 = 890233) (by norm_num)
theorem B6330545 : Blo 2221435 6330545 := bstep (se 2 (by rfl) ⟨2373954, by rfl⟩ : syracuseStep 6330545 = 4747909) B4747909
theorem B4220363 : Blo 2221435 4220363 := bstep (se 1 (by rfl) ⟨3165272, by rfl⟩ : syracuseStep 4220363 = 6330545) B6330545
theorem B11254301 : Blo 2221435 11254301 := bstep (se 3 (by rfl) ⟨2110181, by rfl⟩ : syracuseStep 11254301 = 4220363) B4220363
theorem B7502867 : Blo 2221435 7502867 := bstep (se 1 (by rfl) ⟨5627150, by rfl⟩ : syracuseStep 7502867 = 11254301) B11254301
theorem B5001911 : Blo 2221435 5001911 := bstep (se 1 (by rfl) ⟨3751433, by rfl⟩ : syracuseStep 5001911 = 7502867) B7502867
theorem B3334607 : Blo 2221435 3334607 := bstep (se 1 (by rfl) ⟨2500955, by rfl⟩ : syracuseStep 3334607 = 5001911) B5001911
theorem B2223071 : Blo 2221435 2223071 := bstep (se 1 (by rfl) ⟨1667303, by rfl⟩ : syracuseStep 2223071 = 3334607) B3334607
theorem B3334613 : Blo 2221435 3334613 := bbase (se 7 (by rfl) ⟨39077, by rfl⟩ : syracuseStep 3334613 = 78155) (by norm_num)
theorem B2223075 : Blo 2221435 2223075 := bstep (se 1 (by rfl) ⟨1667306, by rfl⟩ : syracuseStep 2223075 = 3334613) B3334613
theorem B8440757 : Blo 2221435 8440757 := bbase (se 5 (by rfl) ⟨395660, by rfl⟩ : syracuseStep 8440757 = 791321) (by norm_num)
theorem B5627171 : Blo 2221435 5627171 := bstep (se 1 (by rfl) ⟨4220378, by rfl⟩ : syracuseStep 5627171 = 8440757) B8440757
theorem B3751447 : Blo 2221435 3751447 := bstep (se 1 (by rfl) ⟨2813585, by rfl⟩ : syracuseStep 3751447 = 5627171) B5627171
theorem B5001929 : Blo 2221435 5001929 := bstep (se 2 (by rfl) ⟨1875723, by rfl⟩ : syracuseStep 5001929 = 3751447) B3751447
theorem B3334619 : Blo 2221435 3334619 := bstep (se 1 (by rfl) ⟨2500964, by rfl⟩ : syracuseStep 3334619 = 5001929) B5001929
theorem B2223079 : Blo 2221435 2223079 := bstep (se 1 (by rfl) ⟨1667309, by rfl⟩ : syracuseStep 2223079 = 3334619) B3334619
theorem B2500969 : Blo 2221435 2500969 := bbase (se 2 (by rfl) ⟨937863, by rfl⟩ : syracuseStep 2500969 = 1875727) (by norm_num)
theorem B3334625 : Blo 2221435 3334625 := bstep (se 2 (by rfl) ⟨1250484, by rfl⟩ : syracuseStep 3334625 = 2500969) B2500969
theorem B2223083 : Blo 2221435 2223083 := bstep (se 1 (by rfl) ⟨1667312, by rfl⟩ : syracuseStep 2223083 = 3334625) B3334625
theorem B9756773 : Blo 2221435 9756773 := bbase (se 4 (by rfl) ⟨914697, by rfl⟩ : syracuseStep 9756773 = 1829395) (by norm_num)
theorem B6504515 : Blo 2221435 6504515 := bstep (se 1 (by rfl) ⟨4878386, by rfl⟩ : syracuseStep 6504515 = 9756773) B9756773
theorem B4336343 : Blo 2221435 4336343 := bstep (se 1 (by rfl) ⟨3252257, by rfl⟩ : syracuseStep 4336343 = 6504515) B6504515
theorem B2890895 : Blo 2221435 2890895 := bstep (se 1 (by rfl) ⟨2168171, by rfl⟩ : syracuseStep 2890895 = 4336343) B4336343
theorem B30836213 : Blo 2221435 30836213 := bstep (se 5 (by rfl) ⟨1445447, by rfl⟩ : syracuseStep 30836213 = 2890895) B2890895
theorem B20557475 : Blo 2221435 20557475 := bstep (se 1 (by rfl) ⟨15418106, by rfl⟩ : syracuseStep 20557475 = 30836213) B30836213
theorem B13704983 : Blo 2221435 13704983 := bstep (se 1 (by rfl) ⟨10278737, by rfl⟩ : syracuseStep 13704983 = 20557475) B20557475
theorem B9136655 : Blo 2221435 9136655 := bstep (se 1 (by rfl) ⟨6852491, by rfl⟩ : syracuseStep 9136655 = 13704983) B13704983
theorem B6091103 : Blo 2221435 6091103 := bstep (se 1 (by rfl) ⟨4568327, by rfl⟩ : syracuseStep 6091103 = 9136655) B9136655
theorem B4060735 : Blo 2221435 4060735 := bstep (se 1 (by rfl) ⟨3045551, by rfl⟩ : syracuseStep 4060735 = 6091103) B6091103
theorem B21657253 : Blo 2221435 21657253 := bstep (se 4 (by rfl) ⟨2030367, by rfl⟩ : syracuseStep 21657253 = 4060735) B4060735
theorem B28876337 : Blo 2221435 28876337 := bstep (se 2 (by rfl) ⟨10828626, by rfl⟩ : syracuseStep 28876337 = 21657253) B21657253
theorem B19250891 : Blo 2221435 19250891 := bstep (se 1 (by rfl) ⟨14438168, by rfl⟩ : syracuseStep 19250891 = 28876337) B28876337
theorem B12833927 : Blo 2221435 12833927 := bstep (se 1 (by rfl) ⟨9625445, by rfl⟩ : syracuseStep 12833927 = 19250891) B19250891
theorem B8555951 : Blo 2221435 8555951 := bstep (se 1 (by rfl) ⟨6416963, by rfl⟩ : syracuseStep 8555951 = 12833927) B12833927
theorem B5703967 : Blo 2221435 5703967 := bstep (se 1 (by rfl) ⟨4277975, by rfl⟩ : syracuseStep 5703967 = 8555951) B8555951
theorem B7605289 : Blo 2221435 7605289 := bstep (se 2 (by rfl) ⟨2851983, by rfl⟩ : syracuseStep 7605289 = 5703967) B5703967
theorem B10140385 : Blo 2221435 10140385 := bstep (se 2 (by rfl) ⟨3802644, by rfl⟩ : syracuseStep 10140385 = 7605289) B7605289
theorem B13520513 : Blo 2221435 13520513 := bstep (se 2 (by rfl) ⟨5070192, by rfl⟩ : syracuseStep 13520513 = 10140385) B10140385
theorem B9013675 : Blo 2221435 9013675 := bstep (se 1 (by rfl) ⟨6760256, by rfl⟩ : syracuseStep 9013675 = 13520513) B13520513
theorem B12018233 : Blo 2221435 12018233 := bstep (se 2 (by rfl) ⟨4506837, by rfl⟩ : syracuseStep 12018233 = 9013675) B9013675
theorem B8012155 : Blo 2221435 8012155 := bstep (se 1 (by rfl) ⟨6009116, by rfl⟩ : syracuseStep 8012155 = 12018233) B12018233
theorem B10682873 : Blo 2221435 10682873 := bstep (se 2 (by rfl) ⟨4006077, by rfl⟩ : syracuseStep 10682873 = 8012155) B8012155
theorem B7121915 : Blo 2221435 7121915 := bstep (se 1 (by rfl) ⟨5341436, by rfl⟩ : syracuseStep 7121915 = 10682873) B10682873
theorem B4747943 : Blo 2221435 4747943 := bstep (se 1 (by rfl) ⟨3560957, by rfl⟩ : syracuseStep 4747943 = 7121915) B7121915
theorem B12661181 : Blo 2221435 12661181 := bstep (se 3 (by rfl) ⟨2373971, by rfl⟩ : syracuseStep 12661181 = 4747943) B4747943
theorem B8440787 : Blo 2221435 8440787 := bstep (se 1 (by rfl) ⟨6330590, by rfl⟩ : syracuseStep 8440787 = 12661181) B12661181
theorem B5627191 : Blo 2221435 5627191 := bstep (se 1 (by rfl) ⟨4220393, by rfl⟩ : syracuseStep 5627191 = 8440787) B8440787
theorem B7502921 : Blo 2221435 7502921 := bstep (se 2 (by rfl) ⟨2813595, by rfl⟩ : syracuseStep 7502921 = 5627191) B5627191
theorem B5001947 : Blo 2221435 5001947 := bstep (se 1 (by rfl) ⟨3751460, by rfl⟩ : syracuseStep 5001947 = 7502921) B7502921
theorem B3334631 : Blo 2221435 3334631 := bstep (se 1 (by rfl) ⟨2500973, by rfl⟩ : syracuseStep 3334631 = 5001947) B5001947
theorem B2223087 : Blo 2221435 2223087 := bstep (se 1 (by rfl) ⟨1667315, by rfl⟩ : syracuseStep 2223087 = 3334631) B3334631
theorem B3334637 : Blo 2221435 3334637 := bbase (se 3 (by rfl) ⟨625244, by rfl⟩ : syracuseStep 3334637 = 1250489) (by norm_num)
theorem B2223091 : Blo 2221435 2223091 := bstep (se 1 (by rfl) ⟨1667318, by rfl⟩ : syracuseStep 2223091 = 3334637) B3334637
theorem B5001965 : Blo 2221435 5001965 := bbase (se 3 (by rfl) ⟨937868, by rfl⟩ : syracuseStep 5001965 = 1875737) (by norm_num)
theorem B3334643 : Blo 2221435 3334643 := bstep (se 1 (by rfl) ⟨2500982, by rfl⟩ : syracuseStep 3334643 = 5001965) B5001965
theorem B2223095 : Blo 2221435 2223095 := bstep (se 1 (by rfl) ⟨1667321, by rfl⟩ : syracuseStep 2223095 = 3334643) B3334643
theorem B2373985 : Blo 2221435 2373985 := bbase (se 2 (by rfl) ⟨890244, by rfl⟩ : syracuseStep 2373985 = 1780489) (by norm_num)
theorem B3165313 : Blo 2221435 3165313 := bstep (se 2 (by rfl) ⟨1186992, by rfl⟩ : syracuseStep 3165313 = 2373985) B2373985
theorem B4220417 : Blo 2221435 4220417 := bstep (se 2 (by rfl) ⟨1582656, by rfl⟩ : syracuseStep 4220417 = 3165313) B3165313
theorem B2813611 : Blo 2221435 2813611 := bstep (se 1 (by rfl) ⟨2110208, by rfl⟩ : syracuseStep 2813611 = 4220417) B4220417
theorem B3751481 : Blo 2221435 3751481 := bstep (se 2 (by rfl) ⟨1406805, by rfl⟩ : syracuseStep 3751481 = 2813611) B2813611
theorem B2500987 : Blo 2221435 2500987 := bstep (se 1 (by rfl) ⟨1875740, by rfl⟩ : syracuseStep 2500987 = 3751481) B3751481
theorem B3334649 : Blo 2221435 3334649 := bstep (se 2 (by rfl) ⟨1250493, by rfl⟩ : syracuseStep 3334649 = 2500987) B2500987
theorem B2223099 : Blo 2221435 2223099 := bstep (se 1 (by rfl) ⟨1667324, by rfl⟩ : syracuseStep 2223099 = 3334649) B3334649
theorem B5781829 : Blo 2221435 5781829 := bbase (se 4 (by rfl) ⟨542046, by rfl⟩ : syracuseStep 5781829 = 1084093) (by norm_num)
theorem B7709105 : Blo 2221435 7709105 := bstep (se 2 (by rfl) ⟨2890914, by rfl⟩ : syracuseStep 7709105 = 5781829) B5781829
theorem B20557613 : Blo 2221435 20557613 := bstep (se 3 (by rfl) ⟨3854552, by rfl⟩ : syracuseStep 20557613 = 7709105) B7709105
theorem B13705075 : Blo 2221435 13705075 := bstep (se 1 (by rfl) ⟨10278806, by rfl⟩ : syracuseStep 13705075 = 20557613) B20557613
theorem B18273433 : Blo 2221435 18273433 := bstep (se 2 (by rfl) ⟨6852537, by rfl⟩ : syracuseStep 18273433 = 13705075) B13705075
theorem B24364577 : Blo 2221435 24364577 := bstep (se 2 (by rfl) ⟨9136716, by rfl⟩ : syracuseStep 24364577 = 18273433) B18273433
theorem B16243051 : Blo 2221435 16243051 := bstep (se 1 (by rfl) ⟨12182288, by rfl⟩ : syracuseStep 16243051 = 24364577) B24364577
theorem B21657401 : Blo 2221435 21657401 := bstep (se 2 (by rfl) ⟨8121525, by rfl⟩ : syracuseStep 21657401 = 16243051) B16243051
theorem B14438267 : Blo 2221435 14438267 := bstep (se 1 (by rfl) ⟨10828700, by rfl⟩ : syracuseStep 14438267 = 21657401) B21657401
theorem B9625511 : Blo 2221435 9625511 := bstep (se 1 (by rfl) ⟨7219133, by rfl⟩ : syracuseStep 9625511 = 14438267) B14438267
theorem B25668029 : Blo 2221435 25668029 := bstep (se 3 (by rfl) ⟨4812755, by rfl⟩ : syracuseStep 25668029 = 9625511) B9625511
theorem B17112019 : Blo 2221435 17112019 := bstep (se 1 (by rfl) ⟨12834014, by rfl⟩ : syracuseStep 17112019 = 25668029) B25668029
theorem B22816025 : Blo 2221435 22816025 := bstep (se 2 (by rfl) ⟨8556009, by rfl⟩ : syracuseStep 22816025 = 17112019) B17112019
theorem B15210683 : Blo 2221435 15210683 := bstep (se 1 (by rfl) ⟨11408012, by rfl⟩ : syracuseStep 15210683 = 22816025) B22816025
theorem B10140455 : Blo 2221435 10140455 := bstep (se 1 (by rfl) ⟨7605341, by rfl⟩ : syracuseStep 10140455 = 15210683) B15210683
theorem B27041213 : Blo 2221435 27041213 := bstep (se 3 (by rfl) ⟨5070227, by rfl⟩ : syracuseStep 27041213 = 10140455) B10140455
theorem B72109901 : Blo 2221435 72109901 := bstep (se 3 (by rfl) ⟨13520606, by rfl⟩ : syracuseStep 72109901 = 27041213) B27041213
theorem B48073267 : Blo 2221435 48073267 := bstep (se 1 (by rfl) ⟨36054950, by rfl⟩ : syracuseStep 48073267 = 72109901) B72109901
theorem B64097689 : Blo 2221435 64097689 := bstep (se 2 (by rfl) ⟨24036633, by rfl⟩ : syracuseStep 64097689 = 48073267) B48073267
theorem B85463585 : Blo 2221435 85463585 := bstep (se 2 (by rfl) ⟨32048844, by rfl⟩ : syracuseStep 85463585 = 64097689) B64097689
theorem B56975723 : Blo 2221435 56975723 := bstep (se 1 (by rfl) ⟨42731792, by rfl⟩ : syracuseStep 56975723 = 85463585) B85463585
theorem B37983815 : Blo 2221435 37983815 := bstep (se 1 (by rfl) ⟨28487861, by rfl⟩ : syracuseStep 37983815 = 56975723) B56975723
theorem B25322543 : Blo 2221435 25322543 := bstep (se 1 (by rfl) ⟨18991907, by rfl⟩ : syracuseStep 25322543 = 37983815) B37983815
theorem B16881695 : Blo 2221435 16881695 := bstep (se 1 (by rfl) ⟨12661271, by rfl⟩ : syracuseStep 16881695 = 25322543) B25322543
theorem B11254463 : Blo 2221435 11254463 := bstep (se 1 (by rfl) ⟨8440847, by rfl⟩ : syracuseStep 11254463 = 16881695) B16881695
theorem B7502975 : Blo 2221435 7502975 := bstep (se 1 (by rfl) ⟨5627231, by rfl⟩ : syracuseStep 7502975 = 11254463) B11254463
theorem B5001983 : Blo 2221435 5001983 := bstep (se 1 (by rfl) ⟨3751487, by rfl⟩ : syracuseStep 5001983 = 7502975) B7502975
theorem B3334655 : Blo 2221435 3334655 := bstep (se 1 (by rfl) ⟨2500991, by rfl⟩ : syracuseStep 3334655 = 5001983) B5001983
theorem B2223103 : Blo 2221435 2223103 := bstep (se 1 (by rfl) ⟨1667327, by rfl⟩ : syracuseStep 2223103 = 3334655) B3334655
theorem B3334661 : Blo 2221435 3334661 := bbase (se 4 (by rfl) ⟨312624, by rfl⟩ : syracuseStep 3334661 = 625249) (by norm_num)
theorem B2223107 : Blo 2221435 2223107 := bstep (se 1 (by rfl) ⟨1667330, by rfl⟩ : syracuseStep 2223107 = 3334661) B3334661
theorem B3751501 : Blo 2221435 3751501 := bbase (se 3 (by rfl) ⟨703406, by rfl⟩ : syracuseStep 3751501 = 1406813) (by norm_num)
theorem B5002001 : Blo 2221435 5002001 := bstep (se 2 (by rfl) ⟨1875750, by rfl⟩ : syracuseStep 5002001 = 3751501) B3751501
theorem B3334667 : Blo 2221435 3334667 := bstep (se 1 (by rfl) ⟨2501000, by rfl⟩ : syracuseStep 3334667 = 5002001) B5002001
theorem B2223111 : Blo 2221435 2223111 := bstep (se 1 (by rfl) ⟨1667333, by rfl⟩ : syracuseStep 2223111 = 3334667) B3334667
theorem B2501005 : Blo 2221435 2501005 := bbase (se 3 (by rfl) ⟨468938, by rfl⟩ : syracuseStep 2501005 = 937877) (by norm_num)
theorem B3334673 : Blo 2221435 3334673 := bstep (se 2 (by rfl) ⟨1250502, by rfl⟩ : syracuseStep 3334673 = 2501005) B2501005
theorem B2223115 : Blo 2221435 2223115 := bstep (se 1 (by rfl) ⟨1667336, by rfl⟩ : syracuseStep 2223115 = 3334673) B3334673
theorem B7503029 : Blo 2221435 7503029 := bbase (se 5 (by rfl) ⟨351704, by rfl⟩ : syracuseStep 7503029 = 703409) (by norm_num)
theorem B5002019 : Blo 2221435 5002019 := bstep (se 1 (by rfl) ⟨3751514, by rfl⟩ : syracuseStep 5002019 = 7503029) B7503029
theorem B3334679 : Blo 2221435 3334679 := bstep (se 1 (by rfl) ⟨2501009, by rfl⟩ : syracuseStep 3334679 = 5002019) B5002019
theorem B2223119 : Blo 2221435 2223119 := bstep (se 1 (by rfl) ⟨1667339, by rfl⟩ : syracuseStep 2223119 = 3334679) B3334679
theorem B3334685 : Blo 2221435 3334685 := bbase (se 3 (by rfl) ⟨625253, by rfl⟩ : syracuseStep 3334685 = 1250507) (by norm_num)
theorem B2223123 : Blo 2221435 2223123 := bstep (se 1 (by rfl) ⟨1667342, by rfl⟩ : syracuseStep 2223123 = 3334685) B3334685
theorem B5002037 : Blo 2221435 5002037 := bbase (se 5 (by rfl) ⟨234470, by rfl⟩ : syracuseStep 5002037 = 468941) (by norm_num)
theorem B3334691 : Blo 2221435 3334691 := bstep (se 1 (by rfl) ⟨2501018, by rfl⟩ : syracuseStep 3334691 = 5002037) B5002037
theorem B2223127 : Blo 2221435 2223127 := bstep (se 1 (by rfl) ⟨1667345, by rfl⟩ : syracuseStep 2223127 = 3334691) B3334691
theorem B4006157 : Blo 2221435 4006157 := bbase (se 3 (by rfl) ⟨751154, by rfl⟩ : syracuseStep 4006157 = 1502309) (by norm_num)
theorem B10683085 : Blo 2221435 10683085 := bstep (se 3 (by rfl) ⟨2003078, by rfl⟩ : syracuseStep 10683085 = 4006157) B4006157
theorem B14244113 : Blo 2221435 14244113 := bstep (se 2 (by rfl) ⟨5341542, by rfl⟩ : syracuseStep 14244113 = 10683085) B10683085
theorem B9496075 : Blo 2221435 9496075 := bstep (se 1 (by rfl) ⟨7122056, by rfl⟩ : syracuseStep 9496075 = 14244113) B14244113
theorem B12661433 : Blo 2221435 12661433 := bstep (se 2 (by rfl) ⟨4748037, by rfl⟩ : syracuseStep 12661433 = 9496075) B9496075
theorem B8440955 : Blo 2221435 8440955 := bstep (se 1 (by rfl) ⟨6330716, by rfl⟩ : syracuseStep 8440955 = 12661433) B12661433
theorem B5627303 : Blo 2221435 5627303 := bstep (se 1 (by rfl) ⟨4220477, by rfl⟩ : syracuseStep 5627303 = 8440955) B8440955
theorem B3751535 : Blo 2221435 3751535 := bstep (se 1 (by rfl) ⟨2813651, by rfl⟩ : syracuseStep 3751535 = 5627303) B5627303
theorem B2501023 : Blo 2221435 2501023 := bstep (se 1 (by rfl) ⟨1875767, by rfl⟩ : syracuseStep 2501023 = 3751535) B3751535
theorem B3334697 : Blo 2221435 3334697 := bstep (se 2 (by rfl) ⟨1250511, by rfl⟩ : syracuseStep 3334697 = 2501023) B2501023
theorem B2223131 : Blo 2221435 2223131 := bstep (se 1 (by rfl) ⟨1667348, by rfl⟩ : syracuseStep 2223131 = 3334697) B3334697
theorem B20281205 : Blo 2221435 20281205 := bbase (se 5 (by rfl) ⟨950681, by rfl⟩ : syracuseStep 20281205 = 1901363) (by norm_num)
theorem B54083213 : Blo 2221435 54083213 := bstep (se 3 (by rfl) ⟨10140602, by rfl⟩ : syracuseStep 54083213 = 20281205) B20281205
theorem B36055475 : Blo 2221435 36055475 := bstep (se 1 (by rfl) ⟨27041606, by rfl⟩ : syracuseStep 36055475 = 54083213) B54083213
theorem B24036983 : Blo 2221435 24036983 := bstep (se 1 (by rfl) ⟨18027737, by rfl⟩ : syracuseStep 24036983 = 36055475) B36055475
theorem B16024655 : Blo 2221435 16024655 := bstep (se 1 (by rfl) ⟨12018491, by rfl⟩ : syracuseStep 16024655 = 24036983) B24036983
theorem B10683103 : Blo 2221435 10683103 := bstep (se 1 (by rfl) ⟨8012327, by rfl⟩ : syracuseStep 10683103 = 16024655) B16024655
theorem B14244137 : Blo 2221435 14244137 := bstep (se 2 (by rfl) ⟨5341551, by rfl⟩ : syracuseStep 14244137 = 10683103) B10683103
theorem B9496091 : Blo 2221435 9496091 := bstep (se 1 (by rfl) ⟨7122068, by rfl⟩ : syracuseStep 9496091 = 14244137) B14244137
theorem B6330727 : Blo 2221435 6330727 := bstep (se 1 (by rfl) ⟨4748045, by rfl⟩ : syracuseStep 6330727 = 9496091) B9496091
theorem B8440969 : Blo 2221435 8440969 := bstep (se 2 (by rfl) ⟨3165363, by rfl⟩ : syracuseStep 8440969 = 6330727) B6330727
theorem B11254625 : Blo 2221435 11254625 := bstep (se 2 (by rfl) ⟨4220484, by rfl⟩ : syracuseStep 11254625 = 8440969) B8440969
theorem B7503083 : Blo 2221435 7503083 := bstep (se 1 (by rfl) ⟨5627312, by rfl⟩ : syracuseStep 7503083 = 11254625) B11254625
theorem B5002055 : Blo 2221435 5002055 := bstep (se 1 (by rfl) ⟨3751541, by rfl⟩ : syracuseStep 5002055 = 7503083) B7503083
theorem B3334703 : Blo 2221435 3334703 := bstep (se 1 (by rfl) ⟨2501027, by rfl⟩ : syracuseStep 3334703 = 5002055) B5002055
theorem B2223135 : Blo 2221435 2223135 := bstep (se 1 (by rfl) ⟨1667351, by rfl⟩ : syracuseStep 2223135 = 3334703) B3334703
theorem B3334709 : Blo 2221435 3334709 := bbase (se 5 (by rfl) ⟨156314, by rfl⟩ : syracuseStep 3334709 = 312629) (by norm_num)
theorem B2223139 : Blo 2221435 2223139 := bstep (se 1 (by rfl) ⟨1667354, by rfl⟩ : syracuseStep 2223139 = 3334709) B3334709
theorem B5627333 : Blo 2221435 5627333 := bbase (se 4 (by rfl) ⟨527562, by rfl⟩ : syracuseStep 5627333 = 1055125) (by norm_num)
theorem B3751555 : Blo 2221435 3751555 := bstep (se 1 (by rfl) ⟨2813666, by rfl⟩ : syracuseStep 3751555 = 5627333) B5627333
theorem B5002073 : Blo 2221435 5002073 := bstep (se 2 (by rfl) ⟨1875777, by rfl⟩ : syracuseStep 5002073 = 3751555) B3751555
theorem B3334715 : Blo 2221435 3334715 := bstep (se 1 (by rfl) ⟨2501036, by rfl⟩ : syracuseStep 3334715 = 5002073) B5002073
theorem B2223143 : Blo 2221435 2223143 := bstep (se 1 (by rfl) ⟨1667357, by rfl⟩ : syracuseStep 2223143 = 3334715) B3334715
theorem B2501041 : Blo 2221435 2501041 := bbase (se 2 (by rfl) ⟨937890, by rfl⟩ : syracuseStep 2501041 = 1875781) (by norm_num)
theorem B3334721 : Blo 2221435 3334721 := bstep (se 2 (by rfl) ⟨1250520, by rfl⟩ : syracuseStep 3334721 = 2501041) B2501041
theorem B2223147 : Blo 2221435 2223147 := bstep (se 1 (by rfl) ⟨1667360, by rfl⟩ : syracuseStep 2223147 = 3334721) B3334721
theorem B6330773 : Blo 2221435 6330773 := bbase (se 6 (by rfl) ⟨148377, by rfl⟩ : syracuseStep 6330773 = 296755) (by norm_num)
theorem B4220515 : Blo 2221435 4220515 := bstep (se 1 (by rfl) ⟨3165386, by rfl⟩ : syracuseStep 4220515 = 6330773) B6330773
theorem B5627353 : Blo 2221435 5627353 := bstep (se 2 (by rfl) ⟨2110257, by rfl⟩ : syracuseStep 5627353 = 4220515) B4220515
theorem B7503137 : Blo 2221435 7503137 := bstep (se 2 (by rfl) ⟨2813676, by rfl⟩ : syracuseStep 7503137 = 5627353) B5627353
theorem B5002091 : Blo 2221435 5002091 := bstep (se 1 (by rfl) ⟨3751568, by rfl⟩ : syracuseStep 5002091 = 7503137) B7503137
theorem B3334727 : Blo 2221435 3334727 := bstep (se 1 (by rfl) ⟨2501045, by rfl⟩ : syracuseStep 3334727 = 5002091) B5002091
theorem B2223151 : Blo 2221435 2223151 := bstep (se 1 (by rfl) ⟨1667363, by rfl⟩ : syracuseStep 2223151 = 3334727) B3334727
theorem B3334733 : Blo 2221435 3334733 := bbase (se 3 (by rfl) ⟨625262, by rfl⟩ : syracuseStep 3334733 = 1250525) (by norm_num)
theorem B2223155 : Blo 2221435 2223155 := bstep (se 1 (by rfl) ⟨1667366, by rfl⟩ : syracuseStep 2223155 = 3334733) B3334733
theorem B5002109 : Blo 2221435 5002109 := bbase (se 3 (by rfl) ⟨937895, by rfl⟩ : syracuseStep 5002109 = 1875791) (by norm_num)
theorem B3334739 : Blo 2221435 3334739 := bstep (se 1 (by rfl) ⟨2501054, by rfl⟩ : syracuseStep 3334739 = 5002109) B5002109
theorem B2223159 : Blo 2221435 2223159 := bstep (se 1 (by rfl) ⟨1667369, by rfl⟩ : syracuseStep 2223159 = 3334739) B3334739
theorem B3751589 : Blo 2221435 3751589 := bbase (se 4 (by rfl) ⟨351711, by rfl⟩ : syracuseStep 3751589 = 703423) (by norm_num)
theorem B2501059 : Blo 2221435 2501059 := bstep (se 1 (by rfl) ⟨1875794, by rfl⟩ : syracuseStep 2501059 = 3751589) B3751589
theorem B3334745 : Blo 2221435 3334745 := bstep (se 2 (by rfl) ⟨1250529, by rfl⟩ : syracuseStep 3334745 = 2501059) B2501059
theorem B2223163 : Blo 2221435 2223163 := bstep (se 1 (by rfl) ⟨1667372, by rfl⟩ : syracuseStep 2223163 = 3334745) B3334745
theorem B2374057 : Blo 2221435 2374057 := bbase (se 2 (by rfl) ⟨890271, by rfl⟩ : syracuseStep 2374057 = 1780543) (by norm_num)
theorem B3165409 : Blo 2221435 3165409 := bstep (se 2 (by rfl) ⟨1187028, by rfl⟩ : syracuseStep 3165409 = 2374057) B2374057
theorem B16882181 : Blo 2221435 16882181 := bstep (se 4 (by rfl) ⟨1582704, by rfl⟩ : syracuseStep 16882181 = 3165409) B3165409
theorem B11254787 : Blo 2221435 11254787 := bstep (se 1 (by rfl) ⟨8441090, by rfl⟩ : syracuseStep 11254787 = 16882181) B16882181
theorem B7503191 : Blo 2221435 7503191 := bstep (se 1 (by rfl) ⟨5627393, by rfl⟩ : syracuseStep 7503191 = 11254787) B11254787
theorem B5002127 : Blo 2221435 5002127 := bstep (se 1 (by rfl) ⟨3751595, by rfl⟩ : syracuseStep 5002127 = 7503191) B7503191
theorem B3334751 : Blo 2221435 3334751 := bstep (se 1 (by rfl) ⟨2501063, by rfl⟩ : syracuseStep 3334751 = 5002127) B5002127
theorem B2223167 : Blo 2221435 2223167 := bstep (se 1 (by rfl) ⟨1667375, by rfl⟩ : syracuseStep 2223167 = 3334751) B3334751
theorem B3334757 : Blo 2221435 3334757 := bbase (se 4 (by rfl) ⟨312633, by rfl⟩ : syracuseStep 3334757 = 625267) (by norm_num)
theorem B2223171 : Blo 2221435 2223171 := bstep (se 1 (by rfl) ⟨1667378, by rfl⟩ : syracuseStep 2223171 = 3334757) B3334757
theorem B3165421 : Blo 2221435 3165421 := bbase (se 3 (by rfl) ⟨593516, by rfl⟩ : syracuseStep 3165421 = 1187033) (by norm_num)
theorem B4220561 : Blo 2221435 4220561 := bstep (se 2 (by rfl) ⟨1582710, by rfl⟩ : syracuseStep 4220561 = 3165421) B3165421
theorem B2813707 : Blo 2221435 2813707 := bstep (se 1 (by rfl) ⟨2110280, by rfl⟩ : syracuseStep 2813707 = 4220561) B4220561
theorem B3751609 : Blo 2221435 3751609 := bstep (se 2 (by rfl) ⟨1406853, by rfl⟩ : syracuseStep 3751609 = 2813707) B2813707
theorem B5002145 : Blo 2221435 5002145 := bstep (se 2 (by rfl) ⟨1875804, by rfl⟩ : syracuseStep 5002145 = 3751609) B3751609
theorem B3334763 : Blo 2221435 3334763 := bstep (se 1 (by rfl) ⟨2501072, by rfl⟩ : syracuseStep 3334763 = 5002145) B5002145
theorem B2223175 : Blo 2221435 2223175 := bstep (se 1 (by rfl) ⟨1667381, by rfl⟩ : syracuseStep 2223175 = 3334763) B3334763
theorem B2501077 : Blo 2221435 2501077 := bbase (se 7 (by rfl) ⟨29309, by rfl⟩ : syracuseStep 2501077 = 58619) (by norm_num)
theorem B3334769 : Blo 2221435 3334769 := bstep (se 2 (by rfl) ⟨1250538, by rfl⟩ : syracuseStep 3334769 = 2501077) B2501077
theorem B2223179 : Blo 2221435 2223179 := bstep (se 1 (by rfl) ⟨1667384, by rfl⟩ : syracuseStep 2223179 = 3334769) B3334769
theorem B2813717 : Blo 2221435 2813717 := bbase (se 6 (by rfl) ⟨65946, by rfl⟩ : syracuseStep 2813717 = 131893) (by norm_num)
theorem B7503245 : Blo 2221435 7503245 := bstep (se 3 (by rfl) ⟨1406858, by rfl⟩ : syracuseStep 7503245 = 2813717) B2813717
theorem B5002163 : Blo 2221435 5002163 := bstep (se 1 (by rfl) ⟨3751622, by rfl⟩ : syracuseStep 5002163 = 7503245) B7503245
theorem B3334775 : Blo 2221435 3334775 := bstep (se 1 (by rfl) ⟨2501081, by rfl⟩ : syracuseStep 3334775 = 5002163) B5002163
theorem B2223183 : Blo 2221435 2223183 := bstep (se 1 (by rfl) ⟨1667387, by rfl⟩ : syracuseStep 2223183 = 3334775) B3334775
theorem B3334781 : Blo 2221435 3334781 := bbase (se 3 (by rfl) ⟨625271, by rfl⟩ : syracuseStep 3334781 = 1250543) (by norm_num)
theorem B2223187 : Blo 2221435 2223187 := bstep (se 1 (by rfl) ⟨1667390, by rfl⟩ : syracuseStep 2223187 = 3334781) B3334781
theorem B5002181 : Blo 2221435 5002181 := bbase (se 4 (by rfl) ⟨468954, by rfl⟩ : syracuseStep 5002181 = 937909) (by norm_num)
theorem B3334787 : Blo 2221435 3334787 := bstep (se 1 (by rfl) ⟨2501090, by rfl⟩ : syracuseStep 3334787 = 5002181) B5002181
theorem B2223191 : Blo 2221435 2223191 := bstep (se 1 (by rfl) ⟨1667393, by rfl⟩ : syracuseStep 2223191 = 3334787) B3334787
theorem B2253529 : Blo 2221435 2253529 := bbase (se 2 (by rfl) ⟨845073, by rfl⟩ : syracuseStep 2253529 = 1690147) (by norm_num)
theorem B3004705 : Blo 2221435 3004705 := bstep (se 2 (by rfl) ⟨1126764, by rfl⟩ : syracuseStep 3004705 = 2253529) B2253529
theorem B4006273 : Blo 2221435 4006273 := bstep (se 2 (by rfl) ⟨1502352, by rfl⟩ : syracuseStep 4006273 = 3004705) B3004705
theorem B5341697 : Blo 2221435 5341697 := bstep (se 2 (by rfl) ⟨2003136, by rfl⟩ : syracuseStep 5341697 = 4006273) B4006273
theorem B3561131 : Blo 2221435 3561131 := bstep (se 1 (by rfl) ⟨2670848, by rfl⟩ : syracuseStep 3561131 = 5341697) B5341697
theorem B9496349 : Blo 2221435 9496349 := bstep (se 3 (by rfl) ⟨1780565, by rfl⟩ : syracuseStep 9496349 = 3561131) B3561131
theorem B6330899 : Blo 2221435 6330899 := bstep (se 1 (by rfl) ⟨4748174, by rfl⟩ : syracuseStep 6330899 = 9496349) B9496349
theorem B4220599 : Blo 2221435 4220599 := bstep (se 1 (by rfl) ⟨3165449, by rfl⟩ : syracuseStep 4220599 = 6330899) B6330899
theorem B5627465 : Blo 2221435 5627465 := bstep (se 2 (by rfl) ⟨2110299, by rfl⟩ : syracuseStep 5627465 = 4220599) B4220599
theorem B3751643 : Blo 2221435 3751643 := bstep (se 1 (by rfl) ⟨2813732, by rfl⟩ : syracuseStep 3751643 = 5627465) B5627465
theorem B2501095 : Blo 2221435 2501095 := bstep (se 1 (by rfl) ⟨1875821, by rfl⟩ : syracuseStep 2501095 = 3751643) B3751643
theorem B3334793 : Blo 2221435 3334793 := bstep (se 2 (by rfl) ⟨1250547, by rfl⟩ : syracuseStep 3334793 = 2501095) B2501095
theorem B2223195 : Blo 2221435 2223195 := bstep (se 1 (by rfl) ⟨1667396, by rfl⟩ : syracuseStep 2223195 = 3334793) B3334793
theorem B11254949 : Blo 2221435 11254949 := bbase (se 4 (by rfl) ⟨1055151, by rfl⟩ : syracuseStep 11254949 = 2110303) (by norm_num)
theorem B7503299 : Blo 2221435 7503299 := bstep (se 1 (by rfl) ⟨5627474, by rfl⟩ : syracuseStep 7503299 = 11254949) B11254949
theorem B5002199 : Blo 2221435 5002199 := bstep (se 1 (by rfl) ⟨3751649, by rfl⟩ : syracuseStep 5002199 = 7503299) B7503299
theorem B3334799 : Blo 2221435 3334799 := bstep (se 1 (by rfl) ⟨2501099, by rfl⟩ : syracuseStep 3334799 = 5002199) B5002199
theorem B2223199 : Blo 2221435 2223199 := bstep (se 1 (by rfl) ⟨1667399, by rfl⟩ : syracuseStep 2223199 = 3334799) B3334799
theorem B3334805 : Blo 2221435 3334805 := bbase (se 6 (by rfl) ⟨78159, by rfl⟩ : syracuseStep 3334805 = 156319) (by norm_num)
theorem B2223203 : Blo 2221435 2223203 := bstep (se 1 (by rfl) ⟨1667402, by rfl⟩ : syracuseStep 2223203 = 3334805) B3334805
theorem B2535233 : Blo 2221435 2535233 := bbase (se 2 (by rfl) ⟨950712, by rfl⟩ : syracuseStep 2535233 = 1901425) (by norm_num)
theorem B6760621 : Blo 2221435 6760621 := bstep (se 3 (by rfl) ⟨1267616, by rfl⟩ : syracuseStep 6760621 = 2535233) B2535233
theorem B9014161 : Blo 2221435 9014161 := bstep (se 2 (by rfl) ⟨3380310, by rfl⟩ : syracuseStep 9014161 = 6760621) B6760621
theorem B12018881 : Blo 2221435 12018881 := bstep (se 2 (by rfl) ⟨4507080, by rfl⟩ : syracuseStep 12018881 = 9014161) B9014161
theorem B32050349 : Blo 2221435 32050349 := bstep (se 3 (by rfl) ⟨6009440, by rfl⟩ : syracuseStep 32050349 = 12018881) B12018881
theorem B21366899 : Blo 2221435 21366899 := bstep (se 1 (by rfl) ⟨16025174, by rfl⟩ : syracuseStep 21366899 = 32050349) B32050349
theorem B14244599 : Blo 2221435 14244599 := bstep (se 1 (by rfl) ⟨10683449, by rfl⟩ : syracuseStep 14244599 = 21366899) B21366899
theorem B9496399 : Blo 2221435 9496399 := bstep (se 1 (by rfl) ⟨7122299, by rfl⟩ : syracuseStep 9496399 = 14244599) B14244599
theorem B12661865 : Blo 2221435 12661865 := bstep (se 2 (by rfl) ⟨4748199, by rfl⟩ : syracuseStep 12661865 = 9496399) B9496399
theorem B8441243 : Blo 2221435 8441243 := bstep (se 1 (by rfl) ⟨6330932, by rfl⟩ : syracuseStep 8441243 = 12661865) B12661865
theorem B5627495 : Blo 2221435 5627495 := bstep (se 1 (by rfl) ⟨4220621, by rfl⟩ : syracuseStep 5627495 = 8441243) B8441243
theorem B3751663 : Blo 2221435 3751663 := bstep (se 1 (by rfl) ⟨2813747, by rfl⟩ : syracuseStep 3751663 = 5627495) B5627495
theorem B5002217 : Blo 2221435 5002217 := bstep (se 2 (by rfl) ⟨1875831, by rfl⟩ : syracuseStep 5002217 = 3751663) B3751663
theorem B3334811 : Blo 2221435 3334811 := bstep (se 1 (by rfl) ⟨2501108, by rfl⟩ : syracuseStep 3334811 = 5002217) B5002217
theorem B2223207 : Blo 2221435 2223207 := bstep (se 1 (by rfl) ⟨1667405, by rfl⟩ : syracuseStep 2223207 = 3334811) B3334811
theorem B2501113 : Blo 2221435 2501113 := bbase (se 2 (by rfl) ⟨937917, by rfl⟩ : syracuseStep 2501113 = 1875835) (by norm_num)
theorem B3334817 : Blo 2221435 3334817 := bstep (se 2 (by rfl) ⟨1250556, by rfl⟩ : syracuseStep 3334817 = 2501113) B2501113
theorem B2223211 : Blo 2221435 2223211 := bstep (se 1 (by rfl) ⟨1667408, by rfl⟩ : syracuseStep 2223211 = 3334817) B3334817
theorem B7122325 : Blo 2221435 7122325 := bbase (se 6 (by rfl) ⟨166929, by rfl⟩ : syracuseStep 7122325 = 333859) (by norm_num)
theorem B9496433 : Blo 2221435 9496433 := bstep (se 2 (by rfl) ⟨3561162, by rfl⟩ : syracuseStep 9496433 = 7122325) B7122325
theorem B6330955 : Blo 2221435 6330955 := bstep (se 1 (by rfl) ⟨4748216, by rfl⟩ : syracuseStep 6330955 = 9496433) B9496433
theorem B8441273 : Blo 2221435 8441273 := bstep (se 2 (by rfl) ⟨3165477, by rfl⟩ : syracuseStep 8441273 = 6330955) B6330955
theorem B5627515 : Blo 2221435 5627515 := bstep (se 1 (by rfl) ⟨4220636, by rfl⟩ : syracuseStep 5627515 = 8441273) B8441273
theorem B7503353 : Blo 2221435 7503353 := bstep (se 2 (by rfl) ⟨2813757, by rfl⟩ : syracuseStep 7503353 = 5627515) B5627515
theorem B5002235 : Blo 2221435 5002235 := bstep (se 1 (by rfl) ⟨3751676, by rfl⟩ : syracuseStep 5002235 = 7503353) B7503353
theorem B3334823 : Blo 2221435 3334823 := bstep (se 1 (by rfl) ⟨2501117, by rfl⟩ : syracuseStep 3334823 = 5002235) B5002235
theorem B2223215 : Blo 2221435 2223215 := bstep (se 1 (by rfl) ⟨1667411, by rfl⟩ : syracuseStep 2223215 = 3334823) B3334823
theorem B3334829 : Blo 2221435 3334829 := bbase (se 3 (by rfl) ⟨625280, by rfl⟩ : syracuseStep 3334829 = 1250561) (by norm_num)
theorem B2223219 : Blo 2221435 2223219 := bstep (se 1 (by rfl) ⟨1667414, by rfl⟩ : syracuseStep 2223219 = 3334829) B3334829
theorem B5002253 : Blo 2221435 5002253 := bbase (se 3 (by rfl) ⟨937922, by rfl⟩ : syracuseStep 5002253 = 1875845) (by norm_num)
theorem B3334835 : Blo 2221435 3334835 := bstep (se 1 (by rfl) ⟨2501126, by rfl⟩ : syracuseStep 3334835 = 5002253) B5002253
theorem B2223223 : Blo 2221435 2223223 := bstep (se 1 (by rfl) ⟨1667417, by rfl⟩ : syracuseStep 2223223 = 3334835) B3334835
theorem B2813773 : Blo 2221435 2813773 := bbase (se 3 (by rfl) ⟨527582, by rfl⟩ : syracuseStep 2813773 = 1055165) (by norm_num)
theorem B3751697 : Blo 2221435 3751697 := bstep (se 2 (by rfl) ⟨1406886, by rfl⟩ : syracuseStep 3751697 = 2813773) B2813773
theorem B2501131 : Blo 2221435 2501131 := bstep (se 1 (by rfl) ⟨1875848, by rfl⟩ : syracuseStep 2501131 = 3751697) B3751697
theorem B3334841 : Blo 2221435 3334841 := bstep (se 2 (by rfl) ⟨1250565, by rfl⟩ : syracuseStep 3334841 = 2501131) B2501131
theorem B2223227 : Blo 2221435 2223227 := bstep (se 1 (by rfl) ⟨1667420, by rfl⟩ : syracuseStep 2223227 = 3334841) B3334841
theorem B6760693 : Blo 2221435 6760693 := bbase (se 5 (by rfl) ⟨316907, by rfl⟩ : syracuseStep 6760693 = 633815) (by norm_num)
theorem B9014257 : Blo 2221435 9014257 := bstep (se 2 (by rfl) ⟨3380346, by rfl⟩ : syracuseStep 9014257 = 6760693) B6760693
theorem B48076037 : Blo 2221435 48076037 := bstep (se 4 (by rfl) ⟨4507128, by rfl⟩ : syracuseStep 48076037 = 9014257) B9014257
theorem B32050691 : Blo 2221435 32050691 := bstep (se 1 (by rfl) ⟨24038018, by rfl⟩ : syracuseStep 32050691 = 48076037) B48076037
theorem B21367127 : Blo 2221435 21367127 := bstep (se 1 (by rfl) ⟨16025345, by rfl⟩ : syracuseStep 21367127 = 32050691) B32050691
theorem B14244751 : Blo 2221435 14244751 := bstep (se 1 (by rfl) ⟨10683563, by rfl⟩ : syracuseStep 14244751 = 21367127) B21367127
theorem B18993001 : Blo 2221435 18993001 := bstep (se 2 (by rfl) ⟨7122375, by rfl⟩ : syracuseStep 18993001 = 14244751) B14244751
theorem B25324001 : Blo 2221435 25324001 := bstep (se 2 (by rfl) ⟨9496500, by rfl⟩ : syracuseStep 25324001 = 18993001) B18993001
theorem B16882667 : Blo 2221435 16882667 := bstep (se 1 (by rfl) ⟨12662000, by rfl⟩ : syracuseStep 16882667 = 25324001) B25324001
theorem B11255111 : Blo 2221435 11255111 := bstep (se 1 (by rfl) ⟨8441333, by rfl⟩ : syracuseStep 11255111 = 16882667) B16882667
theorem B7503407 : Blo 2221435 7503407 := bstep (se 1 (by rfl) ⟨5627555, by rfl⟩ : syracuseStep 7503407 = 11255111) B11255111
theorem B5002271 : Blo 2221435 5002271 := bstep (se 1 (by rfl) ⟨3751703, by rfl⟩ : syracuseStep 5002271 = 7503407) B7503407
theorem B3334847 : Blo 2221435 3334847 := bstep (se 1 (by rfl) ⟨2501135, by rfl⟩ : syracuseStep 3334847 = 5002271) B5002271
theorem B2223231 : Blo 2221435 2223231 := bstep (se 1 (by rfl) ⟨1667423, by rfl⟩ : syracuseStep 2223231 = 3334847) B3334847
theorem B3334853 : Blo 2221435 3334853 := bbase (se 4 (by rfl) ⟨312642, by rfl⟩ : syracuseStep 3334853 = 625285) (by norm_num)
theorem B2223235 : Blo 2221435 2223235 := bstep (se 1 (by rfl) ⟨1667426, by rfl⟩ : syracuseStep 2223235 = 3334853) B3334853
theorem B3751717 : Blo 2221435 3751717 := bbase (se 4 (by rfl) ⟨351723, by rfl⟩ : syracuseStep 3751717 = 703447) (by norm_num)
theorem B5002289 : Blo 2221435 5002289 := bstep (se 2 (by rfl) ⟨1875858, by rfl⟩ : syracuseStep 5002289 = 3751717) B3751717
theorem B3334859 : Blo 2221435 3334859 := bstep (se 1 (by rfl) ⟨2501144, by rfl⟩ : syracuseStep 3334859 = 5002289) B5002289
theorem B2223239 : Blo 2221435 2223239 := bstep (se 1 (by rfl) ⟨1667429, by rfl⟩ : syracuseStep 2223239 = 3334859) B3334859
theorem B2501149 : Blo 2221435 2501149 := bbase (se 3 (by rfl) ⟨468965, by rfl⟩ : syracuseStep 2501149 = 937931) (by norm_num)
theorem B3334865 : Blo 2221435 3334865 := bstep (se 2 (by rfl) ⟨1250574, by rfl⟩ : syracuseStep 3334865 = 2501149) B2501149
theorem B2223243 : Blo 2221435 2223243 := bstep (se 1 (by rfl) ⟨1667432, by rfl⟩ : syracuseStep 2223243 = 3334865) B3334865
theorem B7503461 : Blo 2221435 7503461 := bbase (se 4 (by rfl) ⟨703449, by rfl⟩ : syracuseStep 7503461 = 1406899) (by norm_num)
theorem B5002307 : Blo 2221435 5002307 := bstep (se 1 (by rfl) ⟨3751730, by rfl⟩ : syracuseStep 5002307 = 7503461) B7503461
theorem B3334871 : Blo 2221435 3334871 := bstep (se 1 (by rfl) ⟨2501153, by rfl⟩ : syracuseStep 3334871 = 5002307) B5002307
theorem B2223247 : Blo 2221435 2223247 := bstep (se 1 (by rfl) ⟨1667435, by rfl⟩ : syracuseStep 2223247 = 3334871) B3334871
theorem B3334877 : Blo 2221435 3334877 := bbase (se 3 (by rfl) ⟨625289, by rfl⟩ : syracuseStep 3334877 = 1250579) (by norm_num)
theorem B2223251 : Blo 2221435 2223251 := bstep (se 1 (by rfl) ⟨1667438, by rfl⟩ : syracuseStep 2223251 = 3334877) B3334877
theorem B5002325 : Blo 2221435 5002325 := bbase (se 8 (by rfl) ⟨29310, by rfl⟩ : syracuseStep 5002325 = 58621) (by norm_num)
theorem B3334883 : Blo 2221435 3334883 := bstep (se 1 (by rfl) ⟨2501162, by rfl⟩ : syracuseStep 3334883 = 5002325) B5002325
theorem B2223255 : Blo 2221435 2223255 := bstep (se 1 (by rfl) ⟨1667441, by rfl⟩ : syracuseStep 2223255 = 3334883) B3334883
theorem B10683701 : Blo 2221435 10683701 := bbase (se 5 (by rfl) ⟨500798, by rfl⟩ : syracuseStep 10683701 = 1001597) (by norm_num)
theorem B7122467 : Blo 2221435 7122467 := bstep (se 1 (by rfl) ⟨5341850, by rfl⟩ : syracuseStep 7122467 = 10683701) B10683701
theorem B4748311 : Blo 2221435 4748311 := bstep (se 1 (by rfl) ⟨3561233, by rfl⟩ : syracuseStep 4748311 = 7122467) B7122467
theorem B6331081 : Blo 2221435 6331081 := bstep (se 2 (by rfl) ⟨2374155, by rfl⟩ : syracuseStep 6331081 = 4748311) B4748311
theorem B8441441 : Blo 2221435 8441441 := bstep (se 2 (by rfl) ⟨3165540, by rfl⟩ : syracuseStep 8441441 = 6331081) B6331081
theorem B5627627 : Blo 2221435 5627627 := bstep (se 1 (by rfl) ⟨4220720, by rfl⟩ : syracuseStep 5627627 = 8441441) B8441441
theorem B3751751 : Blo 2221435 3751751 := bstep (se 1 (by rfl) ⟨2813813, by rfl⟩ : syracuseStep 3751751 = 5627627) B5627627
theorem B2501167 : Blo 2221435 2501167 := bstep (se 1 (by rfl) ⟨1875875, by rfl⟩ : syracuseStep 2501167 = 3751751) B3751751
theorem B3334889 : Blo 2221435 3334889 := bstep (se 2 (by rfl) ⟨1250583, by rfl⟩ : syracuseStep 3334889 = 2501167) B2501167
theorem B2223259 : Blo 2221435 2223259 := bstep (se 1 (by rfl) ⟨1667444, by rfl⟩ : syracuseStep 2223259 = 3334889) B3334889
theorem B2852209 : Blo 2221435 2852209 := bbase (se 2 (by rfl) ⟨1069578, by rfl⟩ : syracuseStep 2852209 = 2139157) (by norm_num)
theorem B3802945 : Blo 2221435 3802945 := bstep (se 2 (by rfl) ⟨1426104, by rfl⟩ : syracuseStep 3802945 = 2852209) B2852209
theorem B5070593 : Blo 2221435 5070593 := bstep (se 2 (by rfl) ⟨1901472, by rfl⟩ : syracuseStep 5070593 = 3802945) B3802945
theorem B13521581 : Blo 2221435 13521581 := bstep (se 3 (by rfl) ⟨2535296, by rfl⟩ : syracuseStep 13521581 = 5070593) B5070593
theorem B9014387 : Blo 2221435 9014387 := bstep (se 1 (by rfl) ⟨6760790, by rfl⟩ : syracuseStep 9014387 = 13521581) B13521581
theorem B24038365 : Blo 2221435 24038365 := bstep (se 3 (by rfl) ⟨4507193, by rfl⟩ : syracuseStep 24038365 = 9014387) B9014387
theorem B32051153 : Blo 2221435 32051153 := bstep (se 2 (by rfl) ⟨12019182, by rfl⟩ : syracuseStep 32051153 = 24038365) B24038365
theorem B21367435 : Blo 2221435 21367435 := bstep (se 1 (by rfl) ⟨16025576, by rfl⟩ : syracuseStep 21367435 = 32051153) B32051153
theorem B28489913 : Blo 2221435 28489913 := bstep (se 2 (by rfl) ⟨10683717, by rfl⟩ : syracuseStep 28489913 = 21367435) B21367435
theorem B18993275 : Blo 2221435 18993275 := bstep (se 1 (by rfl) ⟨14244956, by rfl⟩ : syracuseStep 18993275 = 28489913) B28489913
theorem B12662183 : Blo 2221435 12662183 := bstep (se 1 (by rfl) ⟨9496637, by rfl⟩ : syracuseStep 12662183 = 18993275) B18993275
theorem B8441455 : Blo 2221435 8441455 := bstep (se 1 (by rfl) ⟨6331091, by rfl⟩ : syracuseStep 8441455 = 12662183) B12662183
theorem B11255273 : Blo 2221435 11255273 := bstep (se 2 (by rfl) ⟨4220727, by rfl⟩ : syracuseStep 11255273 = 8441455) B8441455
theorem B7503515 : Blo 2221435 7503515 := bstep (se 1 (by rfl) ⟨5627636, by rfl⟩ : syracuseStep 7503515 = 11255273) B11255273
theorem B5002343 : Blo 2221435 5002343 := bstep (se 1 (by rfl) ⟨3751757, by rfl⟩ : syracuseStep 5002343 = 7503515) B7503515
theorem B3334895 : Blo 2221435 3334895 := bstep (se 1 (by rfl) ⟨2501171, by rfl⟩ : syracuseStep 3334895 = 5002343) B5002343
theorem B2223263 : Blo 2221435 2223263 := bstep (se 1 (by rfl) ⟨1667447, by rfl⟩ : syracuseStep 2223263 = 3334895) B3334895
theorem B3334901 : Blo 2221435 3334901 := bbase (se 5 (by rfl) ⟨156323, by rfl⟩ : syracuseStep 3334901 = 312647) (by norm_num)
theorem B2223267 : Blo 2221435 2223267 := bstep (se 1 (by rfl) ⟨1667450, by rfl⟩ : syracuseStep 2223267 = 3334901) B3334901
theorem B5070613 : Blo 2221435 5070613 := bbase (se 6 (by rfl) ⟨118842, by rfl⟩ : syracuseStep 5070613 = 237685) (by norm_num)
theorem B6760817 : Blo 2221435 6760817 := bstep (se 2 (by rfl) ⟨2535306, by rfl⟩ : syracuseStep 6760817 = 5070613) B5070613
theorem B4507211 : Blo 2221435 4507211 := bstep (se 1 (by rfl) ⟨3380408, by rfl⟩ : syracuseStep 4507211 = 6760817) B6760817
theorem B12019229 : Blo 2221435 12019229 := bstep (se 3 (by rfl) ⟨2253605, by rfl⟩ : syracuseStep 12019229 = 4507211) B4507211
theorem B8012819 : Blo 2221435 8012819 := bstep (se 1 (by rfl) ⟨6009614, by rfl⟩ : syracuseStep 8012819 = 12019229) B12019229
theorem B5341879 : Blo 2221435 5341879 := bstep (se 1 (by rfl) ⟨4006409, by rfl⟩ : syracuseStep 5341879 = 8012819) B8012819
theorem B7122505 : Blo 2221435 7122505 := bstep (se 2 (by rfl) ⟨2670939, by rfl⟩ : syracuseStep 7122505 = 5341879) B5341879
theorem B9496673 : Blo 2221435 9496673 := bstep (se 2 (by rfl) ⟨3561252, by rfl⟩ : syracuseStep 9496673 = 7122505) B7122505
theorem B6331115 : Blo 2221435 6331115 := bstep (se 1 (by rfl) ⟨4748336, by rfl⟩ : syracuseStep 6331115 = 9496673) B9496673
theorem B4220743 : Blo 2221435 4220743 := bstep (se 1 (by rfl) ⟨3165557, by rfl⟩ : syracuseStep 4220743 = 6331115) B6331115
theorem B5627657 : Blo 2221435 5627657 := bstep (se 2 (by rfl) ⟨2110371, by rfl⟩ : syracuseStep 5627657 = 4220743) B4220743
theorem B3751771 : Blo 2221435 3751771 := bstep (se 1 (by rfl) ⟨2813828, by rfl⟩ : syracuseStep 3751771 = 5627657) B5627657
theorem B5002361 : Blo 2221435 5002361 := bstep (se 2 (by rfl) ⟨1875885, by rfl⟩ : syracuseStep 5002361 = 3751771) B3751771
theorem B3334907 : Blo 2221435 3334907 := bstep (se 1 (by rfl) ⟨2501180, by rfl⟩ : syracuseStep 3334907 = 5002361) B5002361
theorem B2223271 : Blo 2221435 2223271 := bstep (se 1 (by rfl) ⟨1667453, by rfl⟩ : syracuseStep 2223271 = 3334907) B3334907
theorem B2501185 : Blo 2221435 2501185 := bbase (se 2 (by rfl) ⟨937944, by rfl⟩ : syracuseStep 2501185 = 1875889) (by norm_num)
theorem B3334913 : Blo 2221435 3334913 := bstep (se 2 (by rfl) ⟨1250592, by rfl⟩ : syracuseStep 3334913 = 2501185) B2501185
theorem B2223275 : Blo 2221435 2223275 := bstep (se 1 (by rfl) ⟨1667456, by rfl⟩ : syracuseStep 2223275 = 3334913) B3334913
theorem B5627677 : Blo 2221435 5627677 := bbase (se 3 (by rfl) ⟨1055189, by rfl⟩ : syracuseStep 5627677 = 2110379) (by norm_num)
theorem B7503569 : Blo 2221435 7503569 := bstep (se 2 (by rfl) ⟨2813838, by rfl⟩ : syracuseStep 7503569 = 5627677) B5627677
theorem B5002379 : Blo 2221435 5002379 := bstep (se 1 (by rfl) ⟨3751784, by rfl⟩ : syracuseStep 5002379 = 7503569) B7503569
theorem B3334919 : Blo 2221435 3334919 := bstep (se 1 (by rfl) ⟨2501189, by rfl⟩ : syracuseStep 3334919 = 5002379) B5002379
theorem B2223279 : Blo 2221435 2223279 := bstep (se 1 (by rfl) ⟨1667459, by rfl⟩ : syracuseStep 2223279 = 3334919) B3334919
theorem B3334925 : Blo 2221435 3334925 := bbase (se 3 (by rfl) ⟨625298, by rfl⟩ : syracuseStep 3334925 = 1250597) (by norm_num)
theorem B2223283 : Blo 2221435 2223283 := bstep (se 1 (by rfl) ⟨1667462, by rfl⟩ : syracuseStep 2223283 = 3334925) B3334925
theorem B5002397 : Blo 2221435 5002397 := bbase (se 3 (by rfl) ⟨937949, by rfl⟩ : syracuseStep 5002397 = 1875899) (by norm_num)
theorem B3334931 : Blo 2221435 3334931 := bstep (se 1 (by rfl) ⟨2501198, by rfl⟩ : syracuseStep 3334931 = 5002397) B5002397
theorem B2223287 : Blo 2221435 2223287 := bstep (se 1 (by rfl) ⟨1667465, by rfl⟩ : syracuseStep 2223287 = 3334931) B3334931
theorem B3751805 : Blo 2221435 3751805 := bbase (se 3 (by rfl) ⟨703463, by rfl⟩ : syracuseStep 3751805 = 1406927) (by norm_num)
theorem B2501203 : Blo 2221435 2501203 := bstep (se 1 (by rfl) ⟨1875902, by rfl⟩ : syracuseStep 2501203 = 3751805) B3751805
theorem B3334937 : Blo 2221435 3334937 := bstep (se 2 (by rfl) ⟨1250601, by rfl⟩ : syracuseStep 3334937 = 2501203) B2501203
theorem B2223291 : Blo 2221435 2223291 := bstep (se 1 (by rfl) ⟨1667468, by rfl⟩ : syracuseStep 2223291 = 3334937) B3334937
theorem B7122581 : Blo 2221435 7122581 := bbase (se 6 (by rfl) ⟨166935, by rfl⟩ : syracuseStep 7122581 = 333871) (by norm_num)
theorem B4748387 : Blo 2221435 4748387 := bstep (se 1 (by rfl) ⟨3561290, by rfl⟩ : syracuseStep 4748387 = 7122581) B7122581
theorem B12662365 : Blo 2221435 12662365 := bstep (se 3 (by rfl) ⟨2374193, by rfl⟩ : syracuseStep 12662365 = 4748387) B4748387
theorem B16883153 : Blo 2221435 16883153 := bstep (se 2 (by rfl) ⟨6331182, by rfl⟩ : syracuseStep 16883153 = 12662365) B12662365
theorem B11255435 : Blo 2221435 11255435 := bstep (se 1 (by rfl) ⟨8441576, by rfl⟩ : syracuseStep 11255435 = 16883153) B16883153
theorem B7503623 : Blo 2221435 7503623 := bstep (se 1 (by rfl) ⟨5627717, by rfl⟩ : syracuseStep 7503623 = 11255435) B11255435
theorem B5002415 : Blo 2221435 5002415 := bstep (se 1 (by rfl) ⟨3751811, by rfl⟩ : syracuseStep 5002415 = 7503623) B7503623
theorem B3334943 : Blo 2221435 3334943 := bstep (se 1 (by rfl) ⟨2501207, by rfl⟩ : syracuseStep 3334943 = 5002415) B5002415
theorem B2223295 : Blo 2221435 2223295 := bstep (se 1 (by rfl) ⟨1667471, by rfl⟩ : syracuseStep 2223295 = 3334943) B3334943
theorem B3334949 : Blo 2221435 3334949 := bbase (se 4 (by rfl) ⟨312651, by rfl⟩ : syracuseStep 3334949 = 625303) (by norm_num)
theorem B2223299 : Blo 2221435 2223299 := bstep (se 1 (by rfl) ⟨1667474, by rfl⟩ : syracuseStep 2223299 = 3334949) B3334949
theorem B2813869 : Blo 2221435 2813869 := bbase (se 3 (by rfl) ⟨527600, by rfl⟩ : syracuseStep 2813869 = 1055201) (by norm_num)
theorem B3751825 : Blo 2221435 3751825 := bstep (se 2 (by rfl) ⟨1406934, by rfl⟩ : syracuseStep 3751825 = 2813869) B2813869
theorem B5002433 : Blo 2221435 5002433 := bstep (se 2 (by rfl) ⟨1875912, by rfl⟩ : syracuseStep 5002433 = 3751825) B3751825
theorem B3334955 : Blo 2221435 3334955 := bstep (se 1 (by rfl) ⟨2501216, by rfl⟩ : syracuseStep 3334955 = 5002433) B5002433
theorem B2223303 : Blo 2221435 2223303 := bstep (se 1 (by rfl) ⟨1667477, by rfl⟩ : syracuseStep 2223303 = 3334955) B3334955
theorem B2501221 : Blo 2221435 2501221 := bbase (se 4 (by rfl) ⟨234489, by rfl⟩ : syracuseStep 2501221 = 468979) (by norm_num)
theorem B3334961 : Blo 2221435 3334961 := bstep (se 2 (by rfl) ⟨1250610, by rfl⟩ : syracuseStep 3334961 = 2501221) B2501221
theorem B2223307 : Blo 2221435 2223307 := bstep (se 1 (by rfl) ⟨1667480, by rfl⟩ : syracuseStep 2223307 = 3334961) B3334961
theorem B3561317 : Blo 2221435 3561317 := bbase (se 4 (by rfl) ⟨333873, by rfl⟩ : syracuseStep 3561317 = 667747) (by norm_num)
theorem B2374211 : Blo 2221435 2374211 := bstep (se 1 (by rfl) ⟨1780658, by rfl⟩ : syracuseStep 2374211 = 3561317) B3561317
theorem B6331229 : Blo 2221435 6331229 := bstep (se 3 (by rfl) ⟨1187105, by rfl⟩ : syracuseStep 6331229 = 2374211) B2374211
theorem B4220819 : Blo 2221435 4220819 := bstep (se 1 (by rfl) ⟨3165614, by rfl⟩ : syracuseStep 4220819 = 6331229) B6331229
theorem B2813879 : Blo 2221435 2813879 := bstep (se 1 (by rfl) ⟨2110409, by rfl⟩ : syracuseStep 2813879 = 4220819) B4220819
theorem B7503677 : Blo 2221435 7503677 := bstep (se 3 (by rfl) ⟨1406939, by rfl⟩ : syracuseStep 7503677 = 2813879) B2813879
theorem B5002451 : Blo 2221435 5002451 := bstep (se 1 (by rfl) ⟨3751838, by rfl⟩ : syracuseStep 5002451 = 7503677) B7503677
theorem B3334967 : Blo 2221435 3334967 := bstep (se 1 (by rfl) ⟨2501225, by rfl⟩ : syracuseStep 3334967 = 5002451) B5002451
theorem B2223311 : Blo 2221435 2223311 := bstep (se 1 (by rfl) ⟨1667483, by rfl⟩ : syracuseStep 2223311 = 3334967) B3334967
theorem B3334973 : Blo 2221435 3334973 := bbase (se 3 (by rfl) ⟨625307, by rfl⟩ : syracuseStep 3334973 = 1250615) (by norm_num)
theorem B2223315 : Blo 2221435 2223315 := bstep (se 1 (by rfl) ⟨1667486, by rfl⟩ : syracuseStep 2223315 = 3334973) B3334973
theorem B5002469 : Blo 2221435 5002469 := bbase (se 4 (by rfl) ⟨468981, by rfl⟩ : syracuseStep 5002469 = 937963) (by norm_num)
theorem B3334979 : Blo 2221435 3334979 := bstep (se 1 (by rfl) ⟨2501234, by rfl⟩ : syracuseStep 3334979 = 5002469) B5002469
theorem B2223319 : Blo 2221435 2223319 := bstep (se 1 (by rfl) ⟨1667489, by rfl⟩ : syracuseStep 2223319 = 3334979) B3334979
theorem B5627789 : Blo 2221435 5627789 := bbase (se 3 (by rfl) ⟨1055210, by rfl⟩ : syracuseStep 5627789 = 2110421) (by norm_num)
theorem B3751859 : Blo 2221435 3751859 := bstep (se 1 (by rfl) ⟨2813894, by rfl⟩ : syracuseStep 3751859 = 5627789) B5627789
theorem B2501239 : Blo 2221435 2501239 := bstep (se 1 (by rfl) ⟨1875929, by rfl⟩ : syracuseStep 2501239 = 3751859) B3751859
theorem B3334985 : Blo 2221435 3334985 := bstep (se 2 (by rfl) ⟨1250619, by rfl⟩ : syracuseStep 3334985 = 2501239) B2501239
theorem B2223323 : Blo 2221435 2223323 := bstep (se 1 (by rfl) ⟨1667492, by rfl⟩ : syracuseStep 2223323 = 3334985) B3334985
theorem B3165637 : Blo 2221435 3165637 := bbase (se 4 (by rfl) ⟨296778, by rfl⟩ : syracuseStep 3165637 = 593557) (by norm_num)
theorem B4220849 : Blo 2221435 4220849 := bstep (se 2 (by rfl) ⟨1582818, by rfl⟩ : syracuseStep 4220849 = 3165637) B3165637
theorem B11255597 : Blo 2221435 11255597 := bstep (se 3 (by rfl) ⟨2110424, by rfl⟩ : syracuseStep 11255597 = 4220849) B4220849
theorem B7503731 : Blo 2221435 7503731 := bstep (se 1 (by rfl) ⟨5627798, by rfl⟩ : syracuseStep 7503731 = 11255597) B11255597
theorem B5002487 : Blo 2221435 5002487 := bstep (se 1 (by rfl) ⟨3751865, by rfl⟩ : syracuseStep 5002487 = 7503731) B7503731
theorem B3334991 : Blo 2221435 3334991 := bstep (se 1 (by rfl) ⟨2501243, by rfl⟩ : syracuseStep 3334991 = 5002487) B5002487
theorem B2223327 : Blo 2221435 2223327 := bstep (se 1 (by rfl) ⟨1667495, by rfl⟩ : syracuseStep 2223327 = 3334991) B3334991
theorem B3334997 : Blo 2221435 3334997 := bbase (se 9 (by rfl) ⟨9770, by rfl⟩ : syracuseStep 3334997 = 19541) (by norm_num)
theorem B2223331 : Blo 2221435 2223331 := bstep (se 1 (by rfl) ⟨1667498, by rfl⟩ : syracuseStep 2223331 = 3334997) B3334997
theorem B4006525 : Blo 2221435 4006525 := bbase (se 3 (by rfl) ⟨751223, by rfl⟩ : syracuseStep 4006525 = 1502447) (by norm_num)
theorem B5342033 : Blo 2221435 5342033 := bstep (se 2 (by rfl) ⟨2003262, by rfl⟩ : syracuseStep 5342033 = 4006525) B4006525
theorem B3561355 : Blo 2221435 3561355 := bstep (se 1 (by rfl) ⟨2671016, by rfl⟩ : syracuseStep 3561355 = 5342033) B5342033
theorem B4748473 : Blo 2221435 4748473 := bstep (se 2 (by rfl) ⟨1780677, by rfl⟩ : syracuseStep 4748473 = 3561355) B3561355
theorem B6331297 : Blo 2221435 6331297 := bstep (se 2 (by rfl) ⟨2374236, by rfl⟩ : syracuseStep 6331297 = 4748473) B4748473
theorem B8441729 : Blo 2221435 8441729 := bstep (se 2 (by rfl) ⟨3165648, by rfl⟩ : syracuseStep 8441729 = 6331297) B6331297
theorem B5627819 : Blo 2221435 5627819 := bstep (se 1 (by rfl) ⟨4220864, by rfl⟩ : syracuseStep 5627819 = 8441729) B8441729
theorem B3751879 : Blo 2221435 3751879 := bstep (se 1 (by rfl) ⟨2813909, by rfl⟩ : syracuseStep 3751879 = 5627819) B5627819
theorem B5002505 : Blo 2221435 5002505 := bstep (se 2 (by rfl) ⟨1875939, by rfl⟩ : syracuseStep 5002505 = 3751879) B3751879
theorem B3335003 : Blo 2221435 3335003 := bstep (se 1 (by rfl) ⟨2501252, by rfl⟩ : syracuseStep 3335003 = 5002505) B5002505
theorem B2223335 : Blo 2221435 2223335 := bstep (se 1 (by rfl) ⟨1667501, by rfl⟩ : syracuseStep 2223335 = 3335003) B3335003
theorem B2501257 : Blo 2221435 2501257 := bbase (se 2 (by rfl) ⟨937971, by rfl⟩ : syracuseStep 2501257 = 1875943) (by norm_num)
theorem B3335009 : Blo 2221435 3335009 := bstep (se 2 (by rfl) ⟨1250628, by rfl⟩ : syracuseStep 3335009 = 2501257) B2501257
theorem B2223339 : Blo 2221435 2223339 := bstep (se 1 (by rfl) ⟨1667504, by rfl⟩ : syracuseStep 2223339 = 3335009) B3335009
theorem B12183605 : Blo 2221435 12183605 := bbase (se 5 (by rfl) ⟨571106, by rfl⟩ : syracuseStep 12183605 = 1142213) (by norm_num)
theorem B8122403 : Blo 2221435 8122403 := bstep (se 1 (by rfl) ⟨6091802, by rfl⟩ : syracuseStep 8122403 = 12183605) B12183605
theorem B5414935 : Blo 2221435 5414935 := bstep (se 1 (by rfl) ⟨4061201, by rfl⟩ : syracuseStep 5414935 = 8122403) B8122403
theorem B7219913 : Blo 2221435 7219913 := bstep (se 2 (by rfl) ⟨2707467, by rfl⟩ : syracuseStep 7219913 = 5414935) B5414935
theorem B19253101 : Blo 2221435 19253101 := bstep (se 3 (by rfl) ⟨3609956, by rfl⟩ : syracuseStep 19253101 = 7219913) B7219913
theorem B25670801 : Blo 2221435 25670801 := bstep (se 2 (by rfl) ⟨9626550, by rfl⟩ : syracuseStep 25670801 = 19253101) B19253101
theorem B68455469 : Blo 2221435 68455469 := bstep (se 3 (by rfl) ⟨12835400, by rfl⟩ : syracuseStep 68455469 = 25670801) B25670801
theorem B45636979 : Blo 2221435 45636979 := bstep (se 1 (by rfl) ⟨34227734, by rfl⟩ : syracuseStep 45636979 = 68455469) B68455469
theorem B60849305 : Blo 2221435 60849305 := bstep (se 2 (by rfl) ⟨22818489, by rfl⟩ : syracuseStep 60849305 = 45636979) B45636979
theorem B40566203 : Blo 2221435 40566203 := bstep (se 1 (by rfl) ⟨30424652, by rfl⟩ : syracuseStep 40566203 = 60849305) B60849305
theorem B27044135 : Blo 2221435 27044135 := bstep (se 1 (by rfl) ⟨20283101, by rfl⟩ : syracuseStep 27044135 = 40566203) B40566203
theorem B18029423 : Blo 2221435 18029423 := bstep (se 1 (by rfl) ⟨13522067, by rfl⟩ : syracuseStep 18029423 = 27044135) B27044135
theorem B48078461 : Blo 2221435 48078461 := bstep (se 3 (by rfl) ⟨9014711, by rfl⟩ : syracuseStep 48078461 = 18029423) B18029423
theorem B32052307 : Blo 2221435 32052307 := bstep (se 1 (by rfl) ⟨24039230, by rfl⟩ : syracuseStep 32052307 = 48078461) B48078461
theorem B42736409 : Blo 2221435 42736409 := bstep (se 2 (by rfl) ⟨16026153, by rfl⟩ : syracuseStep 42736409 = 32052307) B32052307
theorem B28490939 : Blo 2221435 28490939 := bstep (se 1 (by rfl) ⟨21368204, by rfl⟩ : syracuseStep 28490939 = 42736409) B42736409
theorem B18993959 : Blo 2221435 18993959 := bstep (se 1 (by rfl) ⟨14245469, by rfl⟩ : syracuseStep 18993959 = 28490939) B28490939
theorem B12662639 : Blo 2221435 12662639 := bstep (se 1 (by rfl) ⟨9496979, by rfl⟩ : syracuseStep 12662639 = 18993959) B18993959
theorem B8441759 : Blo 2221435 8441759 := bstep (se 1 (by rfl) ⟨6331319, by rfl⟩ : syracuseStep 8441759 = 12662639) B12662639
theorem B5627839 : Blo 2221435 5627839 := bstep (se 1 (by rfl) ⟨4220879, by rfl⟩ : syracuseStep 5627839 = 8441759) B8441759
theorem B7503785 : Blo 2221435 7503785 := bstep (se 2 (by rfl) ⟨2813919, by rfl⟩ : syracuseStep 7503785 = 5627839) B5627839
theorem B5002523 : Blo 2221435 5002523 := bstep (se 1 (by rfl) ⟨3751892, by rfl⟩ : syracuseStep 5002523 = 7503785) B7503785
theorem B3335015 : Blo 2221435 3335015 := bstep (se 1 (by rfl) ⟨2501261, by rfl⟩ : syracuseStep 3335015 = 5002523) B5002523
theorem B2223343 : Blo 2221435 2223343 := bstep (se 1 (by rfl) ⟨1667507, by rfl⟩ : syracuseStep 2223343 = 3335015) B3335015
theorem B3335021 : Blo 2221435 3335021 := bbase (se 3 (by rfl) ⟨625316, by rfl⟩ : syracuseStep 3335021 = 1250633) (by norm_num)
theorem B2223347 : Blo 2221435 2223347 := bstep (se 1 (by rfl) ⟨1667510, by rfl⟩ : syracuseStep 2223347 = 3335021) B3335021
theorem B5002541 : Blo 2221435 5002541 := bbase (se 3 (by rfl) ⟨937976, by rfl⟩ : syracuseStep 5002541 = 1875953) (by norm_num)
theorem B3335027 : Blo 2221435 3335027 := bstep (se 1 (by rfl) ⟨2501270, by rfl⟩ : syracuseStep 3335027 = 5002541) B5002541
theorem B2223351 : Blo 2221435 2223351 := bstep (se 1 (by rfl) ⟨1667513, by rfl⟩ : syracuseStep 2223351 = 3335027) B3335027
theorem B2852329 : Blo 2221435 2852329 := bbase (se 2 (by rfl) ⟨1069623, by rfl⟩ : syracuseStep 2852329 = 2139247) (by norm_num)
theorem B3803105 : Blo 2221435 3803105 := bstep (se 2 (by rfl) ⟨1426164, by rfl⟩ : syracuseStep 3803105 = 2852329) B2852329
theorem B2535403 : Blo 2221435 2535403 := bstep (se 1 (by rfl) ⟨1901552, by rfl⟩ : syracuseStep 2535403 = 3803105) B3803105
theorem B3380537 : Blo 2221435 3380537 := bstep (se 2 (by rfl) ⟨1267701, by rfl⟩ : syracuseStep 3380537 = 2535403) B2535403
theorem B2253691 : Blo 2221435 2253691 := bstep (se 1 (by rfl) ⟨1690268, by rfl⟩ : syracuseStep 2253691 = 3380537) B3380537
theorem B3004921 : Blo 2221435 3004921 := bstep (se 2 (by rfl) ⟨1126845, by rfl⟩ : syracuseStep 3004921 = 2253691) B2253691
theorem B16026245 : Blo 2221435 16026245 := bstep (se 4 (by rfl) ⟨1502460, by rfl⟩ : syracuseStep 16026245 = 3004921) B3004921
theorem B10684163 : Blo 2221435 10684163 := bstep (se 1 (by rfl) ⟨8013122, by rfl⟩ : syracuseStep 10684163 = 16026245) B16026245
theorem B7122775 : Blo 2221435 7122775 := bstep (se 1 (by rfl) ⟨5342081, by rfl⟩ : syracuseStep 7122775 = 10684163) B10684163
theorem B9497033 : Blo 2221435 9497033 := bstep (se 2 (by rfl) ⟨3561387, by rfl⟩ : syracuseStep 9497033 = 7122775) B7122775
theorem B6331355 : Blo 2221435 6331355 := bstep (se 1 (by rfl) ⟨4748516, by rfl⟩ : syracuseStep 6331355 = 9497033) B9497033
theorem B4220903 : Blo 2221435 4220903 := bstep (se 1 (by rfl) ⟨3165677, by rfl⟩ : syracuseStep 4220903 = 6331355) B6331355
theorem B2813935 : Blo 2221435 2813935 := bstep (se 1 (by rfl) ⟨2110451, by rfl⟩ : syracuseStep 2813935 = 4220903) B4220903
theorem B3751913 : Blo 2221435 3751913 := bstep (se 2 (by rfl) ⟨1406967, by rfl⟩ : syracuseStep 3751913 = 2813935) B2813935
theorem B2501275 : Blo 2221435 2501275 := bstep (se 1 (by rfl) ⟨1875956, by rfl⟩ : syracuseStep 2501275 = 3751913) B3751913
theorem B3335033 : Blo 2221435 3335033 := bstep (se 2 (by rfl) ⟨1250637, by rfl⟩ : syracuseStep 3335033 = 2501275) B2501275
theorem B2223355 : Blo 2221435 2223355 := bstep (se 1 (by rfl) ⟨1667516, by rfl⟩ : syracuseStep 2223355 = 3335033) B3335033
theorem B8556997 : Blo 2221435 8556997 := bbase (se 4 (by rfl) ⟨802218, by rfl⟩ : syracuseStep 8556997 = 1604437) (by norm_num)
theorem B11409329 : Blo 2221435 11409329 := bstep (se 2 (by rfl) ⟨4278498, by rfl⟩ : syracuseStep 11409329 = 8556997) B8556997
theorem B7606219 : Blo 2221435 7606219 := bstep (se 1 (by rfl) ⟨5704664, by rfl⟩ : syracuseStep 7606219 = 11409329) B11409329
theorem B10141625 : Blo 2221435 10141625 := bstep (se 2 (by rfl) ⟨3803109, by rfl⟩ : syracuseStep 10141625 = 7606219) B7606219
theorem B6761083 : Blo 2221435 6761083 := bstep (se 1 (by rfl) ⟨5070812, by rfl⟩ : syracuseStep 6761083 = 10141625) B10141625
theorem B9014777 : Blo 2221435 9014777 := bstep (se 2 (by rfl) ⟨3380541, by rfl⟩ : syracuseStep 9014777 = 6761083) B6761083
theorem B6009851 : Blo 2221435 6009851 := bstep (se 1 (by rfl) ⟨4507388, by rfl⟩ : syracuseStep 6009851 = 9014777) B9014777
theorem B4006567 : Blo 2221435 4006567 := bstep (se 1 (by rfl) ⟨3004925, by rfl⟩ : syracuseStep 4006567 = 6009851) B6009851
theorem B21368357 : Blo 2221435 21368357 := bstep (se 4 (by rfl) ⟨2003283, by rfl⟩ : syracuseStep 21368357 = 4006567) B4006567
theorem B14245571 : Blo 2221435 14245571 := bstep (se 1 (by rfl) ⟨10684178, by rfl⟩ : syracuseStep 14245571 = 21368357) B21368357
theorem B37988189 : Blo 2221435 37988189 := bstep (se 3 (by rfl) ⟨7122785, by rfl⟩ : syracuseStep 37988189 = 14245571) B14245571
theorem B25325459 : Blo 2221435 25325459 := bstep (se 1 (by rfl) ⟨18994094, by rfl⟩ : syracuseStep 25325459 = 37988189) B37988189
theorem B16883639 : Blo 2221435 16883639 := bstep (se 1 (by rfl) ⟨12662729, by rfl⟩ : syracuseStep 16883639 = 25325459) B25325459
theorem B11255759 : Blo 2221435 11255759 := bstep (se 1 (by rfl) ⟨8441819, by rfl⟩ : syracuseStep 11255759 = 16883639) B16883639
theorem B7503839 : Blo 2221435 7503839 := bstep (se 1 (by rfl) ⟨5627879, by rfl⟩ : syracuseStep 7503839 = 11255759) B11255759
theorem B5002559 : Blo 2221435 5002559 := bstep (se 1 (by rfl) ⟨3751919, by rfl⟩ : syracuseStep 5002559 = 7503839) B7503839
theorem B3335039 : Blo 2221435 3335039 := bstep (se 1 (by rfl) ⟨2501279, by rfl⟩ : syracuseStep 3335039 = 5002559) B5002559
theorem B2223359 : Blo 2221435 2223359 := bstep (se 1 (by rfl) ⟨1667519, by rfl⟩ : syracuseStep 2223359 = 3335039) B3335039
theorem B3335045 : Blo 2221435 3335045 := bbase (se 4 (by rfl) ⟨312660, by rfl⟩ : syracuseStep 3335045 = 625321) (by norm_num)
theorem B2223363 : Blo 2221435 2223363 := bstep (se 1 (by rfl) ⟨1667522, by rfl⟩ : syracuseStep 2223363 = 3335045) B3335045
theorem B3751933 : Blo 2221435 3751933 := bbase (se 3 (by rfl) ⟨703487, by rfl⟩ : syracuseStep 3751933 = 1406975) (by norm_num)
theorem B5002577 : Blo 2221435 5002577 := bstep (se 2 (by rfl) ⟨1875966, by rfl⟩ : syracuseStep 5002577 = 3751933) B3751933
theorem B3335051 : Blo 2221435 3335051 := bstep (se 1 (by rfl) ⟨2501288, by rfl⟩ : syracuseStep 3335051 = 5002577) B5002577
theorem B2223367 : Blo 2221435 2223367 := bstep (se 1 (by rfl) ⟨1667525, by rfl⟩ : syracuseStep 2223367 = 3335051) B3335051
theorem B2501293 : Blo 2221435 2501293 := bbase (se 3 (by rfl) ⟨468992, by rfl⟩ : syracuseStep 2501293 = 937985) (by norm_num)
theorem B3335057 : Blo 2221435 3335057 := bstep (se 2 (by rfl) ⟨1250646, by rfl⟩ : syracuseStep 3335057 = 2501293) B2501293
theorem B2223371 : Blo 2221435 2223371 := bstep (se 1 (by rfl) ⟨1667528, by rfl⟩ : syracuseStep 2223371 = 3335057) B3335057
theorem B7503893 : Blo 2221435 7503893 := bbase (se 6 (by rfl) ⟨175872, by rfl⟩ : syracuseStep 7503893 = 351745) (by norm_num)
theorem B5002595 : Blo 2221435 5002595 := bstep (se 1 (by rfl) ⟨3751946, by rfl⟩ : syracuseStep 5002595 = 7503893) B7503893
theorem B3335063 : Blo 2221435 3335063 := bstep (se 1 (by rfl) ⟨2501297, by rfl⟩ : syracuseStep 3335063 = 5002595) B5002595
theorem B2223375 : Blo 2221435 2223375 := bstep (se 1 (by rfl) ⟨1667531, by rfl⟩ : syracuseStep 2223375 = 3335063) B3335063
theorem B3335069 : Blo 2221435 3335069 := bbase (se 3 (by rfl) ⟨625325, by rfl⟩ : syracuseStep 3335069 = 1250651) (by norm_num)
theorem B2223379 : Blo 2221435 2223379 := bstep (se 1 (by rfl) ⟨1667534, by rfl⟩ : syracuseStep 2223379 = 3335069) B3335069
theorem B5002613 : Blo 2221435 5002613 := bbase (se 5 (by rfl) ⟨234497, by rfl⟩ : syracuseStep 5002613 = 468995) (by norm_num)
theorem B3335075 : Blo 2221435 3335075 := bstep (se 1 (by rfl) ⟨2501306, by rfl⟩ : syracuseStep 3335075 = 5002613) B5002613
theorem B2223383 : Blo 2221435 2223383 := bstep (se 1 (by rfl) ⟨1667537, by rfl⟩ : syracuseStep 2223383 = 3335075) B3335075
theorem B6417829 : Blo 2221435 6417829 := bbase (se 4 (by rfl) ⟨601671, by rfl⟩ : syracuseStep 6417829 = 1203343) (by norm_num)
theorem B8557105 : Blo 2221435 8557105 := bstep (se 2 (by rfl) ⟨3208914, by rfl⟩ : syracuseStep 8557105 = 6417829) B6417829
theorem B11409473 : Blo 2221435 11409473 := bstep (se 2 (by rfl) ⟨4278552, by rfl⟩ : syracuseStep 11409473 = 8557105) B8557105
theorem B7606315 : Blo 2221435 7606315 := bstep (se 1 (by rfl) ⟨5704736, by rfl⟩ : syracuseStep 7606315 = 11409473) B11409473
theorem B40567013 : Blo 2221435 40567013 := bstep (se 4 (by rfl) ⟨3803157, by rfl⟩ : syracuseStep 40567013 = 7606315) B7606315
theorem B27044675 : Blo 2221435 27044675 := bstep (se 1 (by rfl) ⟨20283506, by rfl⟩ : syracuseStep 27044675 = 40567013) B40567013
theorem B18029783 : Blo 2221435 18029783 := bstep (se 1 (by rfl) ⟨13522337, by rfl⟩ : syracuseStep 18029783 = 27044675) B27044675
theorem B12019855 : Blo 2221435 12019855 := bstep (se 1 (by rfl) ⟨9014891, by rfl⟩ : syracuseStep 12019855 = 18029783) B18029783
theorem B16026473 : Blo 2221435 16026473 := bstep (se 2 (by rfl) ⟨6009927, by rfl⟩ : syracuseStep 16026473 = 12019855) B12019855
theorem B10684315 : Blo 2221435 10684315 := bstep (se 1 (by rfl) ⟨8013236, by rfl⟩ : syracuseStep 10684315 = 16026473) B16026473
theorem B14245753 : Blo 2221435 14245753 := bstep (se 2 (by rfl) ⟨5342157, by rfl⟩ : syracuseStep 14245753 = 10684315) B10684315
theorem B18994337 : Blo 2221435 18994337 := bstep (se 2 (by rfl) ⟨7122876, by rfl⟩ : syracuseStep 18994337 = 14245753) B14245753
theorem B12662891 : Blo 2221435 12662891 := bstep (se 1 (by rfl) ⟨9497168, by rfl⟩ : syracuseStep 12662891 = 18994337) B18994337
theorem B8441927 : Blo 2221435 8441927 := bstep (se 1 (by rfl) ⟨6331445, by rfl⟩ : syracuseStep 8441927 = 12662891) B12662891
theorem B5627951 : Blo 2221435 5627951 := bstep (se 1 (by rfl) ⟨4220963, by rfl⟩ : syracuseStep 5627951 = 8441927) B8441927
theorem B3751967 : Blo 2221435 3751967 := bstep (se 1 (by rfl) ⟨2813975, by rfl⟩ : syracuseStep 3751967 = 5627951) B5627951
theorem B2501311 : Blo 2221435 2501311 := bstep (se 1 (by rfl) ⟨1875983, by rfl⟩ : syracuseStep 2501311 = 3751967) B3751967
theorem B3335081 : Blo 2221435 3335081 := bstep (se 2 (by rfl) ⟨1250655, by rfl⟩ : syracuseStep 3335081 = 2501311) B2501311
theorem B2223387 : Blo 2221435 2223387 := bstep (se 1 (by rfl) ⟨1667540, by rfl⟩ : syracuseStep 2223387 = 3335081) B3335081
theorem B8441941 : Blo 2221435 8441941 := bbase (se 8 (by rfl) ⟨49464, by rfl⟩ : syracuseStep 8441941 = 98929) (by norm_num)
theorem B11255921 : Blo 2221435 11255921 := bstep (se 2 (by rfl) ⟨4220970, by rfl⟩ : syracuseStep 11255921 = 8441941) B8441941
theorem B7503947 : Blo 2221435 7503947 := bstep (se 1 (by rfl) ⟨5627960, by rfl⟩ : syracuseStep 7503947 = 11255921) B11255921
theorem B5002631 : Blo 2221435 5002631 := bstep (se 1 (by rfl) ⟨3751973, by rfl⟩ : syracuseStep 5002631 = 7503947) B7503947
theorem B3335087 : Blo 2221435 3335087 := bstep (se 1 (by rfl) ⟨2501315, by rfl⟩ : syracuseStep 3335087 = 5002631) B5002631
theorem B2223391 : Blo 2221435 2223391 := bstep (se 1 (by rfl) ⟨1667543, by rfl⟩ : syracuseStep 2223391 = 3335087) B3335087
theorem B3335093 : Blo 2221435 3335093 := bbase (se 5 (by rfl) ⟨156332, by rfl⟩ : syracuseStep 3335093 = 312665) (by norm_num)
theorem B2223395 : Blo 2221435 2223395 := bstep (se 1 (by rfl) ⟨1667546, by rfl⟩ : syracuseStep 2223395 = 3335093) B3335093
theorem B5627981 : Blo 2221435 5627981 := bbase (se 3 (by rfl) ⟨1055246, by rfl⟩ : syracuseStep 5627981 = 2110493) (by norm_num)
theorem B3751987 : Blo 2221435 3751987 := bstep (se 1 (by rfl) ⟨2813990, by rfl⟩ : syracuseStep 3751987 = 5627981) B5627981
theorem B5002649 : Blo 2221435 5002649 := bstep (se 2 (by rfl) ⟨1875993, by rfl⟩ : syracuseStep 5002649 = 3751987) B3751987
theorem B3335099 : Blo 2221435 3335099 := bstep (se 1 (by rfl) ⟨2501324, by rfl⟩ : syracuseStep 3335099 = 5002649) B5002649
theorem B2223399 : Blo 2221435 2223399 := bstep (se 1 (by rfl) ⟨1667549, by rfl⟩ : syracuseStep 2223399 = 3335099) B3335099
theorem B2501329 : Blo 2221435 2501329 := bbase (se 2 (by rfl) ⟨937998, by rfl⟩ : syracuseStep 2501329 = 1875997) (by norm_num)
theorem B3335105 : Blo 2221435 3335105 := bstep (se 2 (by rfl) ⟨1250664, by rfl⟩ : syracuseStep 3335105 = 2501329) B2501329
theorem B2223403 : Blo 2221435 2223403 := bstep (se 1 (by rfl) ⟨1667552, by rfl⟩ : syracuseStep 2223403 = 3335105) B3335105
theorem B21660373 : Blo 2221435 21660373 := bbase (se 7 (by rfl) ⟨253832, by rfl⟩ : syracuseStep 21660373 = 507665) (by norm_num)
theorem B28880497 : Blo 2221435 28880497 := bstep (se 2 (by rfl) ⟨10830186, by rfl⟩ : syracuseStep 28880497 = 21660373) B21660373
theorem B38507329 : Blo 2221435 38507329 := bstep (se 2 (by rfl) ⟨14440248, by rfl⟩ : syracuseStep 38507329 = 28880497) B28880497
theorem B51343105 : Blo 2221435 51343105 := bstep (se 2 (by rfl) ⟨19253664, by rfl⟩ : syracuseStep 51343105 = 38507329) B38507329
theorem B68457473 : Blo 2221435 68457473 := bstep (se 2 (by rfl) ⟨25671552, by rfl⟩ : syracuseStep 68457473 = 51343105) B51343105
theorem B45638315 : Blo 2221435 45638315 := bstep (se 1 (by rfl) ⟨34228736, by rfl⟩ : syracuseStep 45638315 = 68457473) B68457473
theorem B30425543 : Blo 2221435 30425543 := bstep (se 1 (by rfl) ⟨22819157, by rfl⟩ : syracuseStep 30425543 = 45638315) B45638315
theorem B20283695 : Blo 2221435 20283695 := bstep (se 1 (by rfl) ⟨15212771, by rfl⟩ : syracuseStep 20283695 = 30425543) B30425543
theorem B13522463 : Blo 2221435 13522463 := bstep (se 1 (by rfl) ⟨10141847, by rfl⟩ : syracuseStep 13522463 = 20283695) B20283695
theorem B9014975 : Blo 2221435 9014975 := bstep (se 1 (by rfl) ⟨6761231, by rfl⟩ : syracuseStep 9014975 = 13522463) B13522463
theorem B6009983 : Blo 2221435 6009983 := bstep (se 1 (by rfl) ⟨4507487, by rfl⟩ : syracuseStep 6009983 = 9014975) B9014975
theorem B4006655 : Blo 2221435 4006655 := bstep (se 1 (by rfl) ⟨3004991, by rfl⟩ : syracuseStep 4006655 = 6009983) B6009983
theorem B2671103 : Blo 2221435 2671103 := bstep (se 1 (by rfl) ⟨2003327, by rfl⟩ : syracuseStep 2671103 = 4006655) B4006655
theorem B7122941 : Blo 2221435 7122941 := bstep (se 3 (by rfl) ⟨1335551, by rfl⟩ : syracuseStep 7122941 = 2671103) B2671103
theorem B4748627 : Blo 2221435 4748627 := bstep (se 1 (by rfl) ⟨3561470, by rfl⟩ : syracuseStep 4748627 = 7122941) B7122941
theorem B3165751 : Blo 2221435 3165751 := bstep (se 1 (by rfl) ⟨2374313, by rfl⟩ : syracuseStep 3165751 = 4748627) B4748627
theorem B4221001 : Blo 2221435 4221001 := bstep (se 2 (by rfl) ⟨1582875, by rfl⟩ : syracuseStep 4221001 = 3165751) B3165751
theorem B5628001 : Blo 2221435 5628001 := bstep (se 2 (by rfl) ⟨2110500, by rfl⟩ : syracuseStep 5628001 = 4221001) B4221001
theorem B7504001 : Blo 2221435 7504001 := bstep (se 2 (by rfl) ⟨2814000, by rfl⟩ : syracuseStep 7504001 = 5628001) B5628001
theorem B5002667 : Blo 2221435 5002667 := bstep (se 1 (by rfl) ⟨3752000, by rfl⟩ : syracuseStep 5002667 = 7504001) B7504001
theorem B3335111 : Blo 2221435 3335111 := bstep (se 1 (by rfl) ⟨2501333, by rfl⟩ : syracuseStep 3335111 = 5002667) B5002667
theorem B2223407 : Blo 2221435 2223407 := bstep (se 1 (by rfl) ⟨1667555, by rfl⟩ : syracuseStep 2223407 = 3335111) B3335111
theorem B3335117 : Blo 2221435 3335117 := bbase (se 3 (by rfl) ⟨625334, by rfl⟩ : syracuseStep 3335117 = 1250669) (by norm_num)
theorem B2223411 : Blo 2221435 2223411 := bstep (se 1 (by rfl) ⟨1667558, by rfl⟩ : syracuseStep 2223411 = 3335117) B3335117
theorem B5002685 : Blo 2221435 5002685 := bbase (se 3 (by rfl) ⟨938003, by rfl⟩ : syracuseStep 5002685 = 1876007) (by norm_num)
theorem B3335123 : Blo 2221435 3335123 := bstep (se 1 (by rfl) ⟨2501342, by rfl⟩ : syracuseStep 3335123 = 5002685) B5002685
theorem B2223415 : Blo 2221435 2223415 := bstep (se 1 (by rfl) ⟨1667561, by rfl⟩ : syracuseStep 2223415 = 3335123) B3335123
theorem B3752021 : Blo 2221435 3752021 := bbase (se 8 (by rfl) ⟨21984, by rfl⟩ : syracuseStep 3752021 = 43969) (by norm_num)
theorem B2501347 : Blo 2221435 2501347 := bstep (se 1 (by rfl) ⟨1876010, by rfl⟩ : syracuseStep 2501347 = 3752021) B3752021
theorem B3335129 : Blo 2221435 3335129 := bstep (se 2 (by rfl) ⟨1250673, by rfl⟩ : syracuseStep 3335129 = 2501347) B2501347
theorem B2223419 : Blo 2221435 2223419 := bstep (se 1 (by rfl) ⟨1667564, by rfl⟩ : syracuseStep 2223419 = 3335129) B3335129
theorem B17114485 : Blo 2221435 17114485 := bbase (se 5 (by rfl) ⟨802241, by rfl⟩ : syracuseStep 17114485 = 1604483) (by norm_num)
theorem B22819313 : Blo 2221435 22819313 := bstep (se 2 (by rfl) ⟨8557242, by rfl⟩ : syracuseStep 22819313 = 17114485) B17114485
theorem B15212875 : Blo 2221435 15212875 := bstep (se 1 (by rfl) ⟨11409656, by rfl⟩ : syracuseStep 15212875 = 22819313) B22819313
theorem B20283833 : Blo 2221435 20283833 := bstep (se 2 (by rfl) ⟨7606437, by rfl⟩ : syracuseStep 20283833 = 15212875) B15212875
theorem B13522555 : Blo 2221435 13522555 := bstep (se 1 (by rfl) ⟨10141916, by rfl⟩ : syracuseStep 13522555 = 20283833) B20283833
theorem B18030073 : Blo 2221435 18030073 := bstep (se 2 (by rfl) ⟨6761277, by rfl⟩ : syracuseStep 18030073 = 13522555) B13522555
theorem B24040097 : Blo 2221435 24040097 := bstep (se 2 (by rfl) ⟨9015036, by rfl⟩ : syracuseStep 24040097 = 18030073) B18030073
theorem B16026731 : Blo 2221435 16026731 := bstep (se 1 (by rfl) ⟨12020048, by rfl⟩ : syracuseStep 16026731 = 24040097) B24040097
theorem B10684487 : Blo 2221435 10684487 := bstep (se 1 (by rfl) ⟨8013365, by rfl⟩ : syracuseStep 10684487 = 16026731) B16026731
theorem B7122991 : Blo 2221435 7122991 := bstep (se 1 (by rfl) ⟨5342243, by rfl⟩ : syracuseStep 7122991 = 10684487) B10684487
theorem B9497321 : Blo 2221435 9497321 := bstep (se 2 (by rfl) ⟨3561495, by rfl⟩ : syracuseStep 9497321 = 7122991) B7122991
theorem B6331547 : Blo 2221435 6331547 := bstep (se 1 (by rfl) ⟨4748660, by rfl⟩ : syracuseStep 6331547 = 9497321) B9497321
theorem B16884125 : Blo 2221435 16884125 := bstep (se 3 (by rfl) ⟨3165773, by rfl⟩ : syracuseStep 16884125 = 6331547) B6331547
theorem B11256083 : Blo 2221435 11256083 := bstep (se 1 (by rfl) ⟨8442062, by rfl⟩ : syracuseStep 11256083 = 16884125) B16884125
theorem B7504055 : Blo 2221435 7504055 := bstep (se 1 (by rfl) ⟨5628041, by rfl⟩ : syracuseStep 7504055 = 11256083) B11256083
theorem B5002703 : Blo 2221435 5002703 := bstep (se 1 (by rfl) ⟨3752027, by rfl⟩ : syracuseStep 5002703 = 7504055) B7504055
theorem B3335135 : Blo 2221435 3335135 := bstep (se 1 (by rfl) ⟨2501351, by rfl⟩ : syracuseStep 3335135 = 5002703) B5002703
theorem B2223423 : Blo 2221435 2223423 := bstep (se 1 (by rfl) ⟨1667567, by rfl⟩ : syracuseStep 2223423 = 3335135) B3335135
theorem B3335141 : Blo 2221435 3335141 := bbase (se 4 (by rfl) ⟨312669, by rfl⟩ : syracuseStep 3335141 = 625339) (by norm_num)
theorem B2223427 : Blo 2221435 2223427 := bstep (se 1 (by rfl) ⟨1667570, by rfl⟩ : syracuseStep 2223427 = 3335141) B3335141
theorem B3561509 : Blo 2221435 3561509 := bbase (se 4 (by rfl) ⟨333891, by rfl⟩ : syracuseStep 3561509 = 667783) (by norm_num)
theorem B9497357 : Blo 2221435 9497357 := bstep (se 3 (by rfl) ⟨1780754, by rfl⟩ : syracuseStep 9497357 = 3561509) B3561509
theorem B6331571 : Blo 2221435 6331571 := bstep (se 1 (by rfl) ⟨4748678, by rfl⟩ : syracuseStep 6331571 = 9497357) B9497357
theorem B4221047 : Blo 2221435 4221047 := bstep (se 1 (by rfl) ⟨3165785, by rfl⟩ : syracuseStep 4221047 = 6331571) B6331571
theorem B2814031 : Blo 2221435 2814031 := bstep (se 1 (by rfl) ⟨2110523, by rfl⟩ : syracuseStep 2814031 = 4221047) B4221047
theorem B3752041 : Blo 2221435 3752041 := bstep (se 2 (by rfl) ⟨1407015, by rfl⟩ : syracuseStep 3752041 = 2814031) B2814031
theorem B5002721 : Blo 2221435 5002721 := bstep (se 2 (by rfl) ⟨1876020, by rfl⟩ : syracuseStep 5002721 = 3752041) B3752041
theorem B3335147 : Blo 2221435 3335147 := bstep (se 1 (by rfl) ⟨2501360, by rfl⟩ : syracuseStep 3335147 = 5002721) B5002721
theorem B2223431 : Blo 2221435 2223431 := bstep (se 1 (by rfl) ⟨1667573, by rfl⟩ : syracuseStep 2223431 = 3335147) B3335147
theorem B2501365 : Blo 2221435 2501365 := bbase (se 5 (by rfl) ⟨117251, by rfl⟩ : syracuseStep 2501365 = 234503) (by norm_num)
theorem B3335153 : Blo 2221435 3335153 := bstep (se 2 (by rfl) ⟨1250682, by rfl⟩ : syracuseStep 3335153 = 2501365) B2501365
theorem B2223435 : Blo 2221435 2223435 := bstep (se 1 (by rfl) ⟨1667576, by rfl⟩ : syracuseStep 2223435 = 3335153) B3335153
theorem C0 (j : ℕ) (h1 : 555358 ≤ j) (h2 : j ≤ 555858) : Blo 2221435 (4 * j + 3) := by
  interval_cases j
  · exact B2221435
  · exact B2221439
  · exact B2221443
  · exact B2221447
  · exact B2221451
  · exact B2221455
  · exact B2221459
  · exact B2221463
  · exact B2221467
  · exact B2221471
  · exact B2221475
  · exact B2221479
  · exact B2221483
  · exact B2221487
  · exact B2221491
  · exact B2221495
  · exact B2221499
  · exact B2221503
  · exact B2221507
  · exact B2221511
  · exact B2221515
  · exact B2221519
  · exact B2221523
  · exact B2221527
  · exact B2221531
  · exact B2221535
  · exact B2221539
  · exact B2221543
  · exact B2221547
  · exact B2221551
  · exact B2221555
  · exact B2221559
  · exact B2221563
  · exact B2221567
  · exact B2221571
  · exact B2221575
  · exact B2221579
  · exact B2221583
  · exact B2221587
  · exact B2221591
  · exact B2221595
  · exact B2221599
  · exact B2221603
  · exact B2221607
  · exact B2221611
  · exact B2221615
  · exact B2221619
  · exact B2221623
  · exact B2221627
  · exact B2221631
  · exact B2221635
  · exact B2221639
  · exact B2221643
  · exact B2221647
  · exact B2221651
  · exact B2221655
  · exact B2221659
  · exact B2221663
  · exact B2221667
  · exact B2221671
  · exact B2221675
  · exact B2221679
  · exact B2221683
  · exact B2221687
  · exact B2221691
  · exact B2221695
  · exact B2221699
  · exact B2221703
  · exact B2221707
  · exact B2221711
  · exact B2221715
  · exact B2221719
  · exact B2221723
  · exact B2221727
  · exact B2221731
  · exact B2221735
  · exact B2221739
  · exact B2221743
  · exact B2221747
  · exact B2221751
  · exact B2221755
  · exact B2221759
  · exact B2221763
  · exact B2221767
  · exact B2221771
  · exact B2221775
  · exact B2221779
  · exact B2221783
  · exact B2221787
  · exact B2221791
  · exact B2221795
  · exact B2221799
  · exact B2221803
  · exact B2221807
  · exact B2221811
  · exact B2221815
  · exact B2221819
  · exact B2221823
  · exact B2221827
  · exact B2221831
  · exact B2221835
  · exact B2221839
  · exact B2221843
  · exact B2221847
  · exact B2221851
  · exact B2221855
  · exact B2221859
  · exact B2221863
  · exact B2221867
  · exact B2221871
  · exact B2221875
  · exact B2221879
  · exact B2221883
  · exact B2221887
  · exact B2221891
  · exact B2221895
  · exact B2221899
  · exact B2221903
  · exact B2221907
  · exact B2221911
  · exact B2221915
  · exact B2221919
  · exact B2221923
  · exact B2221927
  · exact B2221931
  · exact B2221935
  · exact B2221939
  · exact B2221943
  · exact B2221947
  · exact B2221951
  · exact B2221955
  · exact B2221959
  · exact B2221963
  · exact B2221967
  · exact B2221971
  · exact B2221975
  · exact B2221979
  · exact B2221983
  · exact B2221987
  · exact B2221991
  · exact B2221995
  · exact B2221999
  · exact B2222003
  · exact B2222007
  · exact B2222011
  · exact B2222015
  · exact B2222019
  · exact B2222023
  · exact B2222027
  · exact B2222031
  · exact B2222035
  · exact B2222039
  · exact B2222043
  · exact B2222047
  · exact B2222051
  · exact B2222055
  · exact B2222059
  · exact B2222063
  · exact B2222067
  · exact B2222071
  · exact B2222075
  · exact B2222079
  · exact B2222083
  · exact B2222087
  · exact B2222091
  · exact B2222095
  · exact B2222099
  · exact B2222103
  · exact B2222107
  · exact B2222111
  · exact B2222115
  · exact B2222119
  · exact B2222123
  · exact B2222127
  · exact B2222131
  · exact B2222135
  · exact B2222139
  · exact B2222143
  · exact B2222147
  · exact B2222151
  · exact B2222155
  · exact B2222159
  · exact B2222163
  · exact B2222167
  · exact B2222171
  · exact B2222175
  · exact B2222179
  · exact B2222183
  · exact B2222187
  · exact B2222191
  · exact B2222195
  · exact B2222199
  · exact B2222203
  · exact B2222207
  · exact B2222211
  · exact B2222215
  · exact B2222219
  · exact B2222223
  · exact B2222227
  · exact B2222231
  · exact B2222235
  · exact B2222239
  · exact B2222243
  · exact B2222247
  · exact B2222251
  · exact B2222255
  · exact B2222259
  · exact B2222263
  · exact B2222267
  · exact B2222271
  · exact B2222275
  · exact B2222279
  · exact B2222283
  · exact B2222287
  · exact B2222291
  · exact B2222295
  · exact B2222299
  · exact B2222303
  · exact B2222307
  · exact B2222311
  · exact B2222315
  · exact B2222319
  · exact B2222323
  · exact B2222327
  · exact B2222331
  · exact B2222335
  · exact B2222339
  · exact B2222343
  · exact B2222347
  · exact B2222351
  · exact B2222355
  · exact B2222359
  · exact B2222363
  · exact B2222367
  · exact B2222371
  · exact B2222375
  · exact B2222379
  · exact B2222383
  · exact B2222387
  · exact B2222391
  · exact B2222395
  · exact B2222399
  · exact B2222403
  · exact B2222407
  · exact B2222411
  · exact B2222415
  · exact B2222419
  · exact B2222423
  · exact B2222427
  · exact B2222431
  · exact B2222435
  · exact B2222439
  · exact B2222443
  · exact B2222447
  · exact B2222451
  · exact B2222455
  · exact B2222459
  · exact B2222463
  · exact B2222467
  · exact B2222471
  · exact B2222475
  · exact B2222479
  · exact B2222483
  · exact B2222487
  · exact B2222491
  · exact B2222495
  · exact B2222499
  · exact B2222503
  · exact B2222507
  · exact B2222511
  · exact B2222515
  · exact B2222519
  · exact B2222523
  · exact B2222527
  · exact B2222531
  · exact B2222535
  · exact B2222539
  · exact B2222543
  · exact B2222547
  · exact B2222551
  · exact B2222555
  · exact B2222559
  · exact B2222563
  · exact B2222567
  · exact B2222571
  · exact B2222575
  · exact B2222579
  · exact B2222583
  · exact B2222587
  · exact B2222591
  · exact B2222595
  · exact B2222599
  · exact B2222603
  · exact B2222607
  · exact B2222611
  · exact B2222615
  · exact B2222619
  · exact B2222623
  · exact B2222627
  · exact B2222631
  · exact B2222635
  · exact B2222639
  · exact B2222643
  · exact B2222647
  · exact B2222651
  · exact B2222655
  · exact B2222659
  · exact B2222663
  · exact B2222667
  · exact B2222671
  · exact B2222675
  · exact B2222679
  · exact B2222683
  · exact B2222687
  · exact B2222691
  · exact B2222695
  · exact B2222699
  · exact B2222703
  · exact B2222707
  · exact B2222711
  · exact B2222715
  · exact B2222719
  · exact B2222723
  · exact B2222727
  · exact B2222731
  · exact B2222735
  · exact B2222739
  · exact B2222743
  · exact B2222747
  · exact B2222751
  · exact B2222755
  · exact B2222759
  · exact B2222763
  · exact B2222767
  · exact B2222771
  · exact B2222775
  · exact B2222779
  · exact B2222783
  · exact B2222787
  · exact B2222791
  · exact B2222795
  · exact B2222799
  · exact B2222803
  · exact B2222807
  · exact B2222811
  · exact B2222815
  · exact B2222819
  · exact B2222823
  · exact B2222827
  · exact B2222831
  · exact B2222835
  · exact B2222839
  · exact B2222843
  · exact B2222847
  · exact B2222851
  · exact B2222855
  · exact B2222859
  · exact B2222863
  · exact B2222867
  · exact B2222871
  · exact B2222875
  · exact B2222879
  · exact B2222883
  · exact B2222887
  · exact B2222891
  · exact B2222895
  · exact B2222899
  · exact B2222903
  · exact B2222907
  · exact B2222911
  · exact B2222915
  · exact B2222919
  · exact B2222923
  · exact B2222927
  · exact B2222931
  · exact B2222935
  · exact B2222939
  · exact B2222943
  · exact B2222947
  · exact B2222951
  · exact B2222955
  · exact B2222959
  · exact B2222963
  · exact B2222967
  · exact B2222971
  · exact B2222975
  · exact B2222979
  · exact B2222983
  · exact B2222987
  · exact B2222991
  · exact B2222995
  · exact B2222999
  · exact B2223003
  · exact B2223007
  · exact B2223011
  · exact B2223015
  · exact B2223019
  · exact B2223023
  · exact B2223027
  · exact B2223031
  · exact B2223035
  · exact B2223039
  · exact B2223043
  · exact B2223047
  · exact B2223051
  · exact B2223055
  · exact B2223059
  · exact B2223063
  · exact B2223067
  · exact B2223071
  · exact B2223075
  · exact B2223079
  · exact B2223083
  · exact B2223087
  · exact B2223091
  · exact B2223095
  · exact B2223099
  · exact B2223103
  · exact B2223107
  · exact B2223111
  · exact B2223115
  · exact B2223119
  · exact B2223123
  · exact B2223127
  · exact B2223131
  · exact B2223135
  · exact B2223139
  · exact B2223143
  · exact B2223147
  · exact B2223151
  · exact B2223155
  · exact B2223159
  · exact B2223163
  · exact B2223167
  · exact B2223171
  · exact B2223175
  · exact B2223179
  · exact B2223183
  · exact B2223187
  · exact B2223191
  · exact B2223195
  · exact B2223199
  · exact B2223203
  · exact B2223207
  · exact B2223211
  · exact B2223215
  · exact B2223219
  · exact B2223223
  · exact B2223227
  · exact B2223231
  · exact B2223235
  · exact B2223239
  · exact B2223243
  · exact B2223247
  · exact B2223251
  · exact B2223255
  · exact B2223259
  · exact B2223263
  · exact B2223267
  · exact B2223271
  · exact B2223275
  · exact B2223279
  · exact B2223283
  · exact B2223287
  · exact B2223291
  · exact B2223295
  · exact B2223299
  · exact B2223303
  · exact B2223307
  · exact B2223311
  · exact B2223315
  · exact B2223319
  · exact B2223323
  · exact B2223327
  · exact B2223331
  · exact B2223335
  · exact B2223339
  · exact B2223343
  · exact B2223347
  · exact B2223351
  · exact B2223355
  · exact B2223359
  · exact B2223363
  · exact B2223367
  · exact B2223371
  · exact B2223375
  · exact B2223379
  · exact B2223383
  · exact B2223387
  · exact B2223391
  · exact B2223395
  · exact B2223399
  · exact B2223403
  · exact B2223407
  · exact B2223411
  · exact B2223415
  · exact B2223419
  · exact B2223423
  · exact B2223427
  · exact B2223431
  · exact B2223435
theorem solution (m : ℕ) (hlo : 2221435 ≤ m) (hhi : m ≤ 2223435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 555358 ≤ j := by omega
    have hj2 : j ≤ 555858 := by omega
    have hb : Blo 2221435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
