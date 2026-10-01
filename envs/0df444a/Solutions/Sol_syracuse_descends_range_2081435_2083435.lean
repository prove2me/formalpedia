-- Prove2me | solution 1 for syracuse_descends_range_2081435_2083435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:16:16.265632+00:00
-- url     : https://prove2.me/submissions/404abfc7-c7b8-4f75-b14d-0bab09e981e4

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

theorem B2851493 : Blo 2081435 2851493 := bbase (se 4 (by rfl) ⟨267327, by rfl⟩ : syracuseStep 2851493 = 534655) (by norm_num)
theorem B30415925 : Blo 2081435 30415925 := bstep (se 5 (by rfl) ⟨1425746, by rfl⟩ : syracuseStep 30415925 = 2851493) B2851493
theorem B81109133 : Blo 2081435 81109133 := bstep (se 3 (by rfl) ⟨15207962, by rfl⟩ : syracuseStep 81109133 = 30415925) B30415925
theorem B54072755 : Blo 2081435 54072755 := bstep (se 1 (by rfl) ⟨40554566, by rfl⟩ : syracuseStep 54072755 = 81109133) B81109133
theorem B36048503 : Blo 2081435 36048503 := bstep (se 1 (by rfl) ⟨27036377, by rfl⟩ : syracuseStep 36048503 = 54072755) B54072755
theorem B24032335 : Blo 2081435 24032335 := bstep (se 1 (by rfl) ⟨18024251, by rfl⟩ : syracuseStep 24032335 = 36048503) B36048503
theorem B32043113 : Blo 2081435 32043113 := bstep (se 2 (by rfl) ⟨12016167, by rfl⟩ : syracuseStep 32043113 = 24032335) B24032335
theorem B21362075 : Blo 2081435 21362075 := bstep (se 1 (by rfl) ⟨16021556, by rfl⟩ : syracuseStep 21362075 = 32043113) B32043113
theorem B14241383 : Blo 2081435 14241383 := bstep (se 1 (by rfl) ⟨10681037, by rfl⟩ : syracuseStep 14241383 = 21362075) B21362075
theorem B9494255 : Blo 2081435 9494255 := bstep (se 1 (by rfl) ⟨7120691, by rfl⟩ : syracuseStep 9494255 = 14241383) B14241383
theorem B6329503 : Blo 2081435 6329503 := bstep (se 1 (by rfl) ⟨4747127, by rfl⟩ : syracuseStep 6329503 = 9494255) B9494255
theorem B8439337 : Blo 2081435 8439337 := bstep (se 2 (by rfl) ⟨3164751, by rfl⟩ : syracuseStep 8439337 = 6329503) B6329503
theorem B11252449 : Blo 2081435 11252449 := bstep (se 2 (by rfl) ⟨4219668, by rfl⟩ : syracuseStep 11252449 = 8439337) B8439337
theorem B15003265 : Blo 2081435 15003265 := bstep (se 2 (by rfl) ⟨5626224, by rfl⟩ : syracuseStep 15003265 = 11252449) B11252449
theorem B20004353 : Blo 2081435 20004353 := bstep (se 2 (by rfl) ⟨7501632, by rfl⟩ : syracuseStep 20004353 = 15003265) B15003265
theorem B13336235 : Blo 2081435 13336235 := bstep (se 1 (by rfl) ⟨10002176, by rfl⟩ : syracuseStep 13336235 = 20004353) B20004353
theorem B8890823 : Blo 2081435 8890823 := bstep (se 1 (by rfl) ⟨6668117, by rfl⟩ : syracuseStep 8890823 = 13336235) B13336235
theorem B5927215 : Blo 2081435 5927215 := bstep (se 1 (by rfl) ⟨4445411, by rfl⟩ : syracuseStep 5927215 = 8890823) B8890823
theorem B7902953 : Blo 2081435 7902953 := bstep (se 2 (by rfl) ⟨2963607, by rfl⟩ : syracuseStep 7902953 = 5927215) B5927215
theorem B5268635 : Blo 2081435 5268635 := bstep (se 1 (by rfl) ⟨3951476, by rfl⟩ : syracuseStep 5268635 = 7902953) B7902953
theorem B3512423 : Blo 2081435 3512423 := bstep (se 1 (by rfl) ⟨2634317, by rfl⟩ : syracuseStep 3512423 = 5268635) B5268635
theorem B2341615 : Blo 2081435 2341615 := bstep (se 1 (by rfl) ⟨1756211, by rfl⟩ : syracuseStep 2341615 = 3512423) B3512423
theorem B3122153 : Blo 2081435 3122153 := bstep (se 2 (by rfl) ⟨1170807, by rfl⟩ : syracuseStep 3122153 = 2341615) B2341615
theorem B2081435 : Blo 2081435 2081435 := bstep (se 1 (by rfl) ⟨1561076, by rfl⟩ : syracuseStep 2081435 = 3122153) B3122153
theorem B4005397 : Blo 2081435 4005397 := bbase (se 6 (by rfl) ⟨93876, by rfl⟩ : syracuseStep 4005397 = 187753) (by norm_num)
theorem B5340529 : Blo 2081435 5340529 := bstep (se 2 (by rfl) ⟨2002698, by rfl⟩ : syracuseStep 5340529 = 4005397) B4005397
theorem B7120705 : Blo 2081435 7120705 := bstep (se 2 (by rfl) ⟨2670264, by rfl⟩ : syracuseStep 7120705 = 5340529) B5340529
theorem B9494273 : Blo 2081435 9494273 := bstep (se 2 (by rfl) ⟨3560352, by rfl⟩ : syracuseStep 9494273 = 7120705) B7120705
theorem B6329515 : Blo 2081435 6329515 := bstep (se 1 (by rfl) ⟨4747136, by rfl⟩ : syracuseStep 6329515 = 9494273) B9494273
theorem B8439353 : Blo 2081435 8439353 := bstep (se 2 (by rfl) ⟨3164757, by rfl⟩ : syracuseStep 8439353 = 6329515) B6329515
theorem B5626235 : Blo 2081435 5626235 := bstep (se 1 (by rfl) ⟨4219676, by rfl⟩ : syracuseStep 5626235 = 8439353) B8439353
theorem B3750823 : Blo 2081435 3750823 := bstep (se 1 (by rfl) ⟨2813117, by rfl⟩ : syracuseStep 3750823 = 5626235) B5626235
theorem B5001097 : Blo 2081435 5001097 := bstep (se 2 (by rfl) ⟨1875411, by rfl⟩ : syracuseStep 5001097 = 3750823) B3750823
theorem B6668129 : Blo 2081435 6668129 := bstep (se 2 (by rfl) ⟨2500548, by rfl⟩ : syracuseStep 6668129 = 5001097) B5001097
theorem B17781677 : Blo 2081435 17781677 := bstep (se 3 (by rfl) ⟨3334064, by rfl⟩ : syracuseStep 17781677 = 6668129) B6668129
theorem B11854451 : Blo 2081435 11854451 := bstep (se 1 (by rfl) ⟨8890838, by rfl⟩ : syracuseStep 11854451 = 17781677) B17781677
theorem B7902967 : Blo 2081435 7902967 := bstep (se 1 (by rfl) ⟨5927225, by rfl⟩ : syracuseStep 7902967 = 11854451) B11854451
theorem B10537289 : Blo 2081435 10537289 := bstep (se 2 (by rfl) ⟨3951483, by rfl⟩ : syracuseStep 10537289 = 7902967) B7902967
theorem B7024859 : Blo 2081435 7024859 := bstep (se 1 (by rfl) ⟨5268644, by rfl⟩ : syracuseStep 7024859 = 10537289) B10537289
theorem B4683239 : Blo 2081435 4683239 := bstep (se 1 (by rfl) ⟨3512429, by rfl⟩ : syracuseStep 4683239 = 7024859) B7024859
theorem B3122159 : Blo 2081435 3122159 := bstep (se 1 (by rfl) ⟨2341619, by rfl⟩ : syracuseStep 3122159 = 4683239) B4683239
theorem B2081439 : Blo 2081435 2081439 := bstep (se 1 (by rfl) ⟨1561079, by rfl⟩ : syracuseStep 2081439 = 3122159) B3122159
theorem B3122165 : Blo 2081435 3122165 := bbase (se 5 (by rfl) ⟨146351, by rfl⟩ : syracuseStep 3122165 = 292703) (by norm_num)
theorem B2081443 : Blo 2081435 2081443 := bstep (se 1 (by rfl) ⟨1561082, by rfl⟩ : syracuseStep 2081443 = 3122165) B3122165
theorem B4445437 : Blo 2081435 4445437 := bbase (se 3 (by rfl) ⟨833519, by rfl⟩ : syracuseStep 4445437 = 1667039) (by norm_num)
theorem B5927249 : Blo 2081435 5927249 := bstep (se 2 (by rfl) ⟨2222718, by rfl⟩ : syracuseStep 5927249 = 4445437) B4445437
theorem B3951499 : Blo 2081435 3951499 := bstep (se 1 (by rfl) ⟨2963624, by rfl⟩ : syracuseStep 3951499 = 5927249) B5927249
theorem B5268665 : Blo 2081435 5268665 := bstep (se 2 (by rfl) ⟨1975749, by rfl⟩ : syracuseStep 5268665 = 3951499) B3951499
theorem B3512443 : Blo 2081435 3512443 := bstep (se 1 (by rfl) ⟨2634332, by rfl⟩ : syracuseStep 3512443 = 5268665) B5268665
theorem B4683257 : Blo 2081435 4683257 := bstep (se 2 (by rfl) ⟨1756221, by rfl⟩ : syracuseStep 4683257 = 3512443) B3512443
theorem B3122171 : Blo 2081435 3122171 := bstep (se 1 (by rfl) ⟨2341628, by rfl⟩ : syracuseStep 3122171 = 4683257) B4683257
theorem B2081447 : Blo 2081435 2081447 := bstep (se 1 (by rfl) ⟨1561085, by rfl⟩ : syracuseStep 2081447 = 3122171) B3122171
theorem B2341633 : Blo 2081435 2341633 := bbase (se 2 (by rfl) ⟨878112, by rfl⟩ : syracuseStep 2341633 = 1756225) (by norm_num)
theorem B3122177 : Blo 2081435 3122177 := bstep (se 2 (by rfl) ⟨1170816, by rfl⟩ : syracuseStep 3122177 = 2341633) B2341633
theorem B2081451 : Blo 2081435 2081451 := bstep (se 1 (by rfl) ⟨1561088, by rfl⟩ : syracuseStep 2081451 = 3122177) B3122177
theorem B5268685 : Blo 2081435 5268685 := bbase (se 3 (by rfl) ⟨987878, by rfl⟩ : syracuseStep 5268685 = 1975757) (by norm_num)
theorem B7024913 : Blo 2081435 7024913 := bstep (se 2 (by rfl) ⟨2634342, by rfl⟩ : syracuseStep 7024913 = 5268685) B5268685
theorem B4683275 : Blo 2081435 4683275 := bstep (se 1 (by rfl) ⟨3512456, by rfl⟩ : syracuseStep 4683275 = 7024913) B7024913
theorem B3122183 : Blo 2081435 3122183 := bstep (se 1 (by rfl) ⟨2341637, by rfl⟩ : syracuseStep 3122183 = 4683275) B4683275
theorem B2081455 : Blo 2081435 2081455 := bstep (se 1 (by rfl) ⟨1561091, by rfl⟩ : syracuseStep 2081455 = 3122183) B3122183
theorem B3122189 : Blo 2081435 3122189 := bbase (se 3 (by rfl) ⟨585410, by rfl⟩ : syracuseStep 3122189 = 1170821) (by norm_num)
theorem B2081459 : Blo 2081435 2081459 := bstep (se 1 (by rfl) ⟨1561094, by rfl⟩ : syracuseStep 2081459 = 3122189) B3122189
theorem B4683293 : Blo 2081435 4683293 := bbase (se 3 (by rfl) ⟨878117, by rfl⟩ : syracuseStep 4683293 = 1756235) (by norm_num)
theorem B3122195 : Blo 2081435 3122195 := bstep (se 1 (by rfl) ⟨2341646, by rfl⟩ : syracuseStep 3122195 = 4683293) B4683293
theorem B2081463 : Blo 2081435 2081463 := bstep (se 1 (by rfl) ⟨1561097, by rfl⟩ : syracuseStep 2081463 = 3122195) B3122195
theorem B3512477 : Blo 2081435 3512477 := bbase (se 3 (by rfl) ⟨658589, by rfl⟩ : syracuseStep 3512477 = 1317179) (by norm_num)
theorem B2341651 : Blo 2081435 2341651 := bstep (se 1 (by rfl) ⟨1756238, by rfl⟩ : syracuseStep 2341651 = 3512477) B3512477
theorem B3122201 : Blo 2081435 3122201 := bstep (se 2 (by rfl) ⟨1170825, by rfl⟩ : syracuseStep 3122201 = 2341651) B2341651
theorem B2081467 : Blo 2081435 2081467 := bstep (se 1 (by rfl) ⟨1561100, by rfl⟩ : syracuseStep 2081467 = 3122201) B3122201
theorem B2670305 : Blo 2081435 2670305 := bbase (se 2 (by rfl) ⟨1001364, by rfl⟩ : syracuseStep 2670305 = 2002729) (by norm_num)
theorem B7120813 : Blo 2081435 7120813 := bstep (se 3 (by rfl) ⟨1335152, by rfl⟩ : syracuseStep 7120813 = 2670305) B2670305
theorem B9494417 : Blo 2081435 9494417 := bstep (se 2 (by rfl) ⟨3560406, by rfl⟩ : syracuseStep 9494417 = 7120813) B7120813
theorem B6329611 : Blo 2081435 6329611 := bstep (se 1 (by rfl) ⟨4747208, by rfl⟩ : syracuseStep 6329611 = 9494417) B9494417
theorem B8439481 : Blo 2081435 8439481 := bstep (se 2 (by rfl) ⟨3164805, by rfl⟩ : syracuseStep 8439481 = 6329611) B6329611
theorem B45010565 : Blo 2081435 45010565 := bstep (se 4 (by rfl) ⟨4219740, by rfl⟩ : syracuseStep 45010565 = 8439481) B8439481
theorem B30007043 : Blo 2081435 30007043 := bstep (se 1 (by rfl) ⟨22505282, by rfl⟩ : syracuseStep 30007043 = 45010565) B45010565
theorem B20004695 : Blo 2081435 20004695 := bstep (se 1 (by rfl) ⟨15003521, by rfl⟩ : syracuseStep 20004695 = 30007043) B30007043
theorem B13336463 : Blo 2081435 13336463 := bstep (se 1 (by rfl) ⟨10002347, by rfl⟩ : syracuseStep 13336463 = 20004695) B20004695
theorem B8890975 : Blo 2081435 8890975 := bstep (se 1 (by rfl) ⟨6668231, by rfl⟩ : syracuseStep 8890975 = 13336463) B13336463
theorem B11854633 : Blo 2081435 11854633 := bstep (se 2 (by rfl) ⟨4445487, by rfl⟩ : syracuseStep 11854633 = 8890975) B8890975
theorem B15806177 : Blo 2081435 15806177 := bstep (se 2 (by rfl) ⟨5927316, by rfl⟩ : syracuseStep 15806177 = 11854633) B11854633
theorem B10537451 : Blo 2081435 10537451 := bstep (se 1 (by rfl) ⟨7903088, by rfl⟩ : syracuseStep 10537451 = 15806177) B15806177
theorem B7024967 : Blo 2081435 7024967 := bstep (se 1 (by rfl) ⟨5268725, by rfl⟩ : syracuseStep 7024967 = 10537451) B10537451
theorem B4683311 : Blo 2081435 4683311 := bstep (se 1 (by rfl) ⟨3512483, by rfl⟩ : syracuseStep 4683311 = 7024967) B7024967
theorem B3122207 : Blo 2081435 3122207 := bstep (se 1 (by rfl) ⟨2341655, by rfl⟩ : syracuseStep 3122207 = 4683311) B4683311
theorem B2081471 : Blo 2081435 2081471 := bstep (se 1 (by rfl) ⟨1561103, by rfl⟩ : syracuseStep 2081471 = 3122207) B3122207
theorem B3122213 : Blo 2081435 3122213 := bbase (se 4 (by rfl) ⟨292707, by rfl⟩ : syracuseStep 3122213 = 585415) (by norm_num)
theorem B2081475 : Blo 2081435 2081475 := bstep (se 1 (by rfl) ⟨1561106, by rfl⟩ : syracuseStep 2081475 = 3122213) B3122213
theorem B2634373 : Blo 2081435 2634373 := bbase (se 4 (by rfl) ⟨246972, by rfl⟩ : syracuseStep 2634373 = 493945) (by norm_num)
theorem B3512497 : Blo 2081435 3512497 := bstep (se 2 (by rfl) ⟨1317186, by rfl⟩ : syracuseStep 3512497 = 2634373) B2634373
theorem B4683329 : Blo 2081435 4683329 := bstep (se 2 (by rfl) ⟨1756248, by rfl⟩ : syracuseStep 4683329 = 3512497) B3512497
theorem B3122219 : Blo 2081435 3122219 := bstep (se 1 (by rfl) ⟨2341664, by rfl⟩ : syracuseStep 3122219 = 4683329) B4683329
theorem B2081479 : Blo 2081435 2081479 := bstep (se 1 (by rfl) ⟨1561109, by rfl⟩ : syracuseStep 2081479 = 3122219) B3122219
theorem B2341669 : Blo 2081435 2341669 := bbase (se 4 (by rfl) ⟨219531, by rfl⟩ : syracuseStep 2341669 = 439063) (by norm_num)
theorem B3122225 : Blo 2081435 3122225 := bstep (se 2 (by rfl) ⟨1170834, by rfl⟩ : syracuseStep 3122225 = 2341669) B2341669
theorem B2081483 : Blo 2081435 2081483 := bstep (se 1 (by rfl) ⟨1561112, by rfl⟩ : syracuseStep 2081483 = 3122225) B3122225
theorem B8891045 : Blo 2081435 8891045 := bbase (se 4 (by rfl) ⟨833535, by rfl⟩ : syracuseStep 8891045 = 1667071) (by norm_num)
theorem B5927363 : Blo 2081435 5927363 := bstep (se 1 (by rfl) ⟨4445522, by rfl⟩ : syracuseStep 5927363 = 8891045) B8891045
theorem B3951575 : Blo 2081435 3951575 := bstep (se 1 (by rfl) ⟨2963681, by rfl⟩ : syracuseStep 3951575 = 5927363) B5927363
theorem B2634383 : Blo 2081435 2634383 := bstep (se 1 (by rfl) ⟨1975787, by rfl⟩ : syracuseStep 2634383 = 3951575) B3951575
theorem B7025021 : Blo 2081435 7025021 := bstep (se 3 (by rfl) ⟨1317191, by rfl⟩ : syracuseStep 7025021 = 2634383) B2634383
theorem B4683347 : Blo 2081435 4683347 := bstep (se 1 (by rfl) ⟨3512510, by rfl⟩ : syracuseStep 4683347 = 7025021) B7025021
theorem B3122231 : Blo 2081435 3122231 := bstep (se 1 (by rfl) ⟨2341673, by rfl⟩ : syracuseStep 3122231 = 4683347) B4683347
theorem B2081487 : Blo 2081435 2081487 := bstep (se 1 (by rfl) ⟨1561115, by rfl⟩ : syracuseStep 2081487 = 3122231) B3122231
theorem B3122237 : Blo 2081435 3122237 := bbase (se 3 (by rfl) ⟨585419, by rfl⟩ : syracuseStep 3122237 = 1170839) (by norm_num)
theorem B2081491 : Blo 2081435 2081491 := bstep (se 1 (by rfl) ⟨1561118, by rfl⟩ : syracuseStep 2081491 = 3122237) B3122237
theorem B4683365 : Blo 2081435 4683365 := bbase (se 4 (by rfl) ⟨439065, by rfl⟩ : syracuseStep 4683365 = 878131) (by norm_num)
theorem B3122243 : Blo 2081435 3122243 := bstep (se 1 (by rfl) ⟨2341682, by rfl⟩ : syracuseStep 3122243 = 4683365) B4683365
theorem B2081495 : Blo 2081435 2081495 := bstep (se 1 (by rfl) ⟨1561121, by rfl⟩ : syracuseStep 2081495 = 3122243) B3122243
theorem B5268797 : Blo 2081435 5268797 := bbase (se 3 (by rfl) ⟨987899, by rfl⟩ : syracuseStep 5268797 = 1975799) (by norm_num)
theorem B3512531 : Blo 2081435 3512531 := bstep (se 1 (by rfl) ⟨2634398, by rfl⟩ : syracuseStep 3512531 = 5268797) B5268797
theorem B2341687 : Blo 2081435 2341687 := bstep (se 1 (by rfl) ⟨1756265, by rfl⟩ : syracuseStep 2341687 = 3512531) B3512531
theorem B3122249 : Blo 2081435 3122249 := bstep (se 2 (by rfl) ⟨1170843, by rfl⟩ : syracuseStep 3122249 = 2341687) B2341687
theorem B2081499 : Blo 2081435 2081499 := bstep (se 1 (by rfl) ⟨1561124, by rfl⟩ : syracuseStep 2081499 = 3122249) B3122249
theorem B3951605 : Blo 2081435 3951605 := bbase (se 5 (by rfl) ⟨185231, by rfl⟩ : syracuseStep 3951605 = 370463) (by norm_num)
theorem B10537613 : Blo 2081435 10537613 := bstep (se 3 (by rfl) ⟨1975802, by rfl⟩ : syracuseStep 10537613 = 3951605) B3951605
theorem B7025075 : Blo 2081435 7025075 := bstep (se 1 (by rfl) ⟨5268806, by rfl⟩ : syracuseStep 7025075 = 10537613) B10537613
theorem B4683383 : Blo 2081435 4683383 := bstep (se 1 (by rfl) ⟨3512537, by rfl⟩ : syracuseStep 4683383 = 7025075) B7025075
theorem B3122255 : Blo 2081435 3122255 := bstep (se 1 (by rfl) ⟨2341691, by rfl⟩ : syracuseStep 3122255 = 4683383) B4683383
theorem B2081503 : Blo 2081435 2081503 := bstep (se 1 (by rfl) ⟨1561127, by rfl⟩ : syracuseStep 2081503 = 3122255) B3122255
theorem B3122261 : Blo 2081435 3122261 := bbase (se 8 (by rfl) ⟨18294, by rfl⟩ : syracuseStep 3122261 = 36589) (by norm_num)
theorem B2081507 : Blo 2081435 2081507 := bstep (se 1 (by rfl) ⟨1561130, by rfl⟩ : syracuseStep 2081507 = 3122261) B3122261
theorem B10681429 : Blo 2081435 10681429 := bbase (se 8 (by rfl) ⟨62586, by rfl⟩ : syracuseStep 10681429 = 125173) (by norm_num)
theorem B14241905 : Blo 2081435 14241905 := bstep (se 2 (by rfl) ⟨5340714, by rfl⟩ : syracuseStep 14241905 = 10681429) B10681429
theorem B9494603 : Blo 2081435 9494603 := bstep (se 1 (by rfl) ⟨7120952, by rfl⟩ : syracuseStep 9494603 = 14241905) B14241905
theorem B6329735 : Blo 2081435 6329735 := bstep (se 1 (by rfl) ⟨4747301, by rfl⟩ : syracuseStep 6329735 = 9494603) B9494603
theorem B4219823 : Blo 2081435 4219823 := bstep (se 1 (by rfl) ⟨3164867, by rfl⟩ : syracuseStep 4219823 = 6329735) B6329735
theorem B2813215 : Blo 2081435 2813215 := bstep (se 1 (by rfl) ⟨2109911, by rfl⟩ : syracuseStep 2813215 = 4219823) B4219823
theorem B3750953 : Blo 2081435 3750953 := bstep (se 2 (by rfl) ⟨1406607, by rfl⟩ : syracuseStep 3750953 = 2813215) B2813215
theorem B10002541 : Blo 2081435 10002541 := bstep (se 3 (by rfl) ⟨1875476, by rfl⟩ : syracuseStep 10002541 = 3750953) B3750953
theorem B13336721 : Blo 2081435 13336721 := bstep (se 2 (by rfl) ⟨5001270, by rfl⟩ : syracuseStep 13336721 = 10002541) B10002541
theorem B8891147 : Blo 2081435 8891147 := bstep (se 1 (by rfl) ⟨6668360, by rfl⟩ : syracuseStep 8891147 = 13336721) B13336721
theorem B5927431 : Blo 2081435 5927431 := bstep (se 1 (by rfl) ⟨4445573, by rfl⟩ : syracuseStep 5927431 = 8891147) B8891147
theorem B7903241 : Blo 2081435 7903241 := bstep (se 2 (by rfl) ⟨2963715, by rfl⟩ : syracuseStep 7903241 = 5927431) B5927431
theorem B5268827 : Blo 2081435 5268827 := bstep (se 1 (by rfl) ⟨3951620, by rfl⟩ : syracuseStep 5268827 = 7903241) B7903241
theorem B3512551 : Blo 2081435 3512551 := bstep (se 1 (by rfl) ⟨2634413, by rfl⟩ : syracuseStep 3512551 = 5268827) B5268827
theorem B4683401 : Blo 2081435 4683401 := bstep (se 2 (by rfl) ⟨1756275, by rfl⟩ : syracuseStep 4683401 = 3512551) B3512551
theorem B3122267 : Blo 2081435 3122267 := bstep (se 1 (by rfl) ⟨2341700, by rfl⟩ : syracuseStep 3122267 = 4683401) B4683401
theorem B2081511 : Blo 2081435 2081511 := bstep (se 1 (by rfl) ⟨1561133, by rfl⟩ : syracuseStep 2081511 = 3122267) B3122267
theorem B2341705 : Blo 2081435 2341705 := bbase (se 2 (by rfl) ⟨878139, by rfl⟩ : syracuseStep 2341705 = 1756279) (by norm_num)
theorem B3122273 : Blo 2081435 3122273 := bstep (se 2 (by rfl) ⟨1170852, by rfl⟩ : syracuseStep 3122273 = 2341705) B2341705
theorem B2081515 : Blo 2081435 2081515 := bstep (se 1 (by rfl) ⟨1561136, by rfl⟩ : syracuseStep 2081515 = 3122273) B3122273
theorem B3208061 : Blo 2081435 3208061 := bbase (se 3 (by rfl) ⟨601511, by rfl⟩ : syracuseStep 3208061 = 1203023) (by norm_num)
theorem B2138707 : Blo 2081435 2138707 := bstep (se 1 (by rfl) ⟨1604030, by rfl⟩ : syracuseStep 2138707 = 3208061) B3208061
theorem B2851609 : Blo 2081435 2851609 := bstep (se 2 (by rfl) ⟨1069353, by rfl⟩ : syracuseStep 2851609 = 2138707) B2138707
theorem B3802145 : Blo 2081435 3802145 := bstep (se 2 (by rfl) ⟨1425804, by rfl⟩ : syracuseStep 3802145 = 2851609) B2851609
theorem B10139053 : Blo 2081435 10139053 := bstep (se 3 (by rfl) ⟨1901072, by rfl⟩ : syracuseStep 10139053 = 3802145) B3802145
theorem B13518737 : Blo 2081435 13518737 := bstep (se 2 (by rfl) ⟨5069526, by rfl⟩ : syracuseStep 13518737 = 10139053) B10139053
theorem B9012491 : Blo 2081435 9012491 := bstep (se 1 (by rfl) ⟨6759368, by rfl⟩ : syracuseStep 9012491 = 13518737) B13518737
theorem B6008327 : Blo 2081435 6008327 := bstep (se 1 (by rfl) ⟨4506245, by rfl⟩ : syracuseStep 6008327 = 9012491) B9012491
theorem B4005551 : Blo 2081435 4005551 := bstep (se 1 (by rfl) ⟨3004163, by rfl⟩ : syracuseStep 4005551 = 6008327) B6008327
theorem B10681469 : Blo 2081435 10681469 := bstep (se 3 (by rfl) ⟨2002775, by rfl⟩ : syracuseStep 10681469 = 4005551) B4005551
theorem B7120979 : Blo 2081435 7120979 := bstep (se 1 (by rfl) ⟨5340734, by rfl⟩ : syracuseStep 7120979 = 10681469) B10681469
theorem B4747319 : Blo 2081435 4747319 := bstep (se 1 (by rfl) ⟨3560489, by rfl⟩ : syracuseStep 4747319 = 7120979) B7120979
theorem B3164879 : Blo 2081435 3164879 := bstep (se 1 (by rfl) ⟨2373659, by rfl⟩ : syracuseStep 3164879 = 4747319) B4747319
theorem B8439677 : Blo 2081435 8439677 := bstep (se 3 (by rfl) ⟨1582439, by rfl⟩ : syracuseStep 8439677 = 3164879) B3164879
theorem B5626451 : Blo 2081435 5626451 := bstep (se 1 (by rfl) ⟨4219838, by rfl⟩ : syracuseStep 5626451 = 8439677) B8439677
theorem B3750967 : Blo 2081435 3750967 := bstep (se 1 (by rfl) ⟨2813225, by rfl⟩ : syracuseStep 3750967 = 5626451) B5626451
theorem B20005157 : Blo 2081435 20005157 := bstep (se 4 (by rfl) ⟨1875483, by rfl⟩ : syracuseStep 20005157 = 3750967) B3750967
theorem B13336771 : Blo 2081435 13336771 := bstep (se 1 (by rfl) ⟨10002578, by rfl⟩ : syracuseStep 13336771 = 20005157) B20005157
theorem B17782361 : Blo 2081435 17782361 := bstep (se 2 (by rfl) ⟨6668385, by rfl⟩ : syracuseStep 17782361 = 13336771) B13336771
theorem B11854907 : Blo 2081435 11854907 := bstep (se 1 (by rfl) ⟨8891180, by rfl⟩ : syracuseStep 11854907 = 17782361) B17782361
theorem B7903271 : Blo 2081435 7903271 := bstep (se 1 (by rfl) ⟨5927453, by rfl⟩ : syracuseStep 7903271 = 11854907) B11854907
theorem B5268847 : Blo 2081435 5268847 := bstep (se 1 (by rfl) ⟨3951635, by rfl⟩ : syracuseStep 5268847 = 7903271) B7903271
theorem B7025129 : Blo 2081435 7025129 := bstep (se 2 (by rfl) ⟨2634423, by rfl⟩ : syracuseStep 7025129 = 5268847) B5268847
theorem B4683419 : Blo 2081435 4683419 := bstep (se 1 (by rfl) ⟨3512564, by rfl⟩ : syracuseStep 4683419 = 7025129) B7025129
theorem B3122279 : Blo 2081435 3122279 := bstep (se 1 (by rfl) ⟨2341709, by rfl⟩ : syracuseStep 3122279 = 4683419) B4683419
theorem B2081519 : Blo 2081435 2081519 := bstep (se 1 (by rfl) ⟨1561139, by rfl⟩ : syracuseStep 2081519 = 3122279) B3122279
theorem B3122285 : Blo 2081435 3122285 := bbase (se 3 (by rfl) ⟨585428, by rfl⟩ : syracuseStep 3122285 = 1170857) (by norm_num)
theorem B2081523 : Blo 2081435 2081523 := bstep (se 1 (by rfl) ⟨1561142, by rfl⟩ : syracuseStep 2081523 = 3122285) B3122285
theorem B4683437 : Blo 2081435 4683437 := bbase (se 3 (by rfl) ⟨878144, by rfl⟩ : syracuseStep 4683437 = 1756289) (by norm_num)
theorem B3122291 : Blo 2081435 3122291 := bstep (se 1 (by rfl) ⟨2341718, by rfl⟩ : syracuseStep 3122291 = 4683437) B4683437
theorem B2081527 : Blo 2081435 2081527 := bstep (se 1 (by rfl) ⟨1561145, by rfl⟩ : syracuseStep 2081527 = 3122291) B3122291
theorem B3334213 : Blo 2081435 3334213 := bbase (se 4 (by rfl) ⟨312582, by rfl⟩ : syracuseStep 3334213 = 625165) (by norm_num)
theorem B4445617 : Blo 2081435 4445617 := bstep (se 2 (by rfl) ⟨1667106, by rfl⟩ : syracuseStep 4445617 = 3334213) B3334213
theorem B5927489 : Blo 2081435 5927489 := bstep (se 2 (by rfl) ⟨2222808, by rfl⟩ : syracuseStep 5927489 = 4445617) B4445617
theorem B3951659 : Blo 2081435 3951659 := bstep (se 1 (by rfl) ⟨2963744, by rfl⟩ : syracuseStep 3951659 = 5927489) B5927489
theorem B2634439 : Blo 2081435 2634439 := bstep (se 1 (by rfl) ⟨1975829, by rfl⟩ : syracuseStep 2634439 = 3951659) B3951659
theorem B3512585 : Blo 2081435 3512585 := bstep (se 2 (by rfl) ⟨1317219, by rfl⟩ : syracuseStep 3512585 = 2634439) B2634439
theorem B2341723 : Blo 2081435 2341723 := bstep (se 1 (by rfl) ⟨1756292, by rfl⟩ : syracuseStep 2341723 = 3512585) B3512585
theorem B3122297 : Blo 2081435 3122297 := bstep (se 2 (by rfl) ⟨1170861, by rfl⟩ : syracuseStep 3122297 = 2341723) B2341723
theorem B2081531 : Blo 2081435 2081531 := bstep (se 1 (by rfl) ⟨1561148, by rfl⟩ : syracuseStep 2081531 = 3122297) B3122297
theorem B3379709 : Blo 2081435 3379709 := bbase (se 3 (by rfl) ⟨633695, by rfl⟩ : syracuseStep 3379709 = 1267391) (by norm_num)
theorem B2253139 : Blo 2081435 2253139 := bstep (se 1 (by rfl) ⟨1689854, by rfl⟩ : syracuseStep 2253139 = 3379709) B3379709
theorem B48066965 : Blo 2081435 48066965 := bstep (se 6 (by rfl) ⟨1126569, by rfl⟩ : syracuseStep 48066965 = 2253139) B2253139
theorem B32044643 : Blo 2081435 32044643 := bstep (se 1 (by rfl) ⟨24033482, by rfl⟩ : syracuseStep 32044643 = 48066965) B48066965
theorem B21363095 : Blo 2081435 21363095 := bstep (se 1 (by rfl) ⟨16022321, by rfl⟩ : syracuseStep 21363095 = 32044643) B32044643
theorem B14242063 : Blo 2081435 14242063 := bstep (se 1 (by rfl) ⟨10681547, by rfl⟩ : syracuseStep 14242063 = 21363095) B21363095
theorem B18989417 : Blo 2081435 18989417 := bstep (se 2 (by rfl) ⟨7121031, by rfl⟩ : syracuseStep 18989417 = 14242063) B14242063
theorem B12659611 : Blo 2081435 12659611 := bstep (se 1 (by rfl) ⟨9494708, by rfl⟩ : syracuseStep 12659611 = 18989417) B18989417
theorem B16879481 : Blo 2081435 16879481 := bstep (se 2 (by rfl) ⟨6329805, by rfl⟩ : syracuseStep 16879481 = 12659611) B12659611
theorem B11252987 : Blo 2081435 11252987 := bstep (se 1 (by rfl) ⟨8439740, by rfl⟩ : syracuseStep 11252987 = 16879481) B16879481
theorem B7501991 : Blo 2081435 7501991 := bstep (se 1 (by rfl) ⟨5626493, by rfl⟩ : syracuseStep 7501991 = 11252987) B11252987
theorem B20005309 : Blo 2081435 20005309 := bstep (se 3 (by rfl) ⟨3750995, by rfl⟩ : syracuseStep 20005309 = 7501991) B7501991
theorem B26673745 : Blo 2081435 26673745 := bstep (se 2 (by rfl) ⟨10002654, by rfl⟩ : syracuseStep 26673745 = 20005309) B20005309
theorem B35564993 : Blo 2081435 35564993 := bstep (se 2 (by rfl) ⟨13336872, by rfl⟩ : syracuseStep 35564993 = 26673745) B26673745
theorem B23709995 : Blo 2081435 23709995 := bstep (se 1 (by rfl) ⟨17782496, by rfl⟩ : syracuseStep 23709995 = 35564993) B35564993
theorem B15806663 : Blo 2081435 15806663 := bstep (se 1 (by rfl) ⟨11854997, by rfl⟩ : syracuseStep 15806663 = 23709995) B23709995
theorem B10537775 : Blo 2081435 10537775 := bstep (se 1 (by rfl) ⟨7903331, by rfl⟩ : syracuseStep 10537775 = 15806663) B15806663
theorem B7025183 : Blo 2081435 7025183 := bstep (se 1 (by rfl) ⟨5268887, by rfl⟩ : syracuseStep 7025183 = 10537775) B10537775
theorem B4683455 : Blo 2081435 4683455 := bstep (se 1 (by rfl) ⟨3512591, by rfl⟩ : syracuseStep 4683455 = 7025183) B7025183
theorem B3122303 : Blo 2081435 3122303 := bstep (se 1 (by rfl) ⟨2341727, by rfl⟩ : syracuseStep 3122303 = 4683455) B4683455
theorem B2081535 : Blo 2081435 2081535 := bstep (se 1 (by rfl) ⟨1561151, by rfl⟩ : syracuseStep 2081535 = 3122303) B3122303
theorem B3122309 : Blo 2081435 3122309 := bbase (se 4 (by rfl) ⟨292716, by rfl⟩ : syracuseStep 3122309 = 585433) (by norm_num)
theorem B2081539 : Blo 2081435 2081539 := bstep (se 1 (by rfl) ⟨1561154, by rfl⟩ : syracuseStep 2081539 = 3122309) B3122309
theorem B3512605 : Blo 2081435 3512605 := bbase (se 3 (by rfl) ⟨658613, by rfl⟩ : syracuseStep 3512605 = 1317227) (by norm_num)
theorem B4683473 : Blo 2081435 4683473 := bstep (se 2 (by rfl) ⟨1756302, by rfl⟩ : syracuseStep 4683473 = 3512605) B3512605
theorem B3122315 : Blo 2081435 3122315 := bstep (se 1 (by rfl) ⟨2341736, by rfl⟩ : syracuseStep 3122315 = 4683473) B4683473
theorem B2081543 : Blo 2081435 2081543 := bstep (se 1 (by rfl) ⟨1561157, by rfl⟩ : syracuseStep 2081543 = 3122315) B3122315
theorem B2341741 : Blo 2081435 2341741 := bbase (se 3 (by rfl) ⟨439076, by rfl⟩ : syracuseStep 2341741 = 878153) (by norm_num)
theorem B3122321 : Blo 2081435 3122321 := bstep (se 2 (by rfl) ⟨1170870, by rfl⟩ : syracuseStep 3122321 = 2341741) B2341741
theorem B2081547 : Blo 2081435 2081547 := bstep (se 1 (by rfl) ⟨1561160, by rfl⟩ : syracuseStep 2081547 = 3122321) B3122321
theorem B7025237 : Blo 2081435 7025237 := bbase (se 8 (by rfl) ⟨41163, by rfl⟩ : syracuseStep 7025237 = 82327) (by norm_num)
theorem B4683491 : Blo 2081435 4683491 := bstep (se 1 (by rfl) ⟨3512618, by rfl⟩ : syracuseStep 4683491 = 7025237) B7025237
theorem B3122327 : Blo 2081435 3122327 := bstep (se 1 (by rfl) ⟨2341745, by rfl⟩ : syracuseStep 3122327 = 4683491) B4683491
theorem B2081551 : Blo 2081435 2081551 := bstep (se 1 (by rfl) ⟨1561163, by rfl⟩ : syracuseStep 2081551 = 3122327) B3122327
theorem B3122333 : Blo 2081435 3122333 := bbase (se 3 (by rfl) ⟨585437, by rfl⟩ : syracuseStep 3122333 = 1170875) (by norm_num)
theorem B2081555 : Blo 2081435 2081555 := bstep (se 1 (by rfl) ⟨1561166, by rfl⟩ : syracuseStep 2081555 = 3122333) B3122333
theorem B4683509 : Blo 2081435 4683509 := bbase (se 5 (by rfl) ⟨219539, by rfl⟩ : syracuseStep 4683509 = 439079) (by norm_num)
theorem B3122339 : Blo 2081435 3122339 := bstep (se 1 (by rfl) ⟨2341754, by rfl⟩ : syracuseStep 3122339 = 4683509) B4683509
theorem B2081559 : Blo 2081435 2081559 := bstep (se 1 (by rfl) ⟨1561169, by rfl⟩ : syracuseStep 2081559 = 3122339) B3122339
theorem B6759509 : Blo 2081435 6759509 := bbase (se 8 (by rfl) ⟨39606, by rfl⟩ : syracuseStep 6759509 = 79213) (by norm_num)
theorem B18025357 : Blo 2081435 18025357 := bstep (se 3 (by rfl) ⟨3379754, by rfl⟩ : syracuseStep 18025357 = 6759509) B6759509
theorem B24033809 : Blo 2081435 24033809 := bstep (se 2 (by rfl) ⟨9012678, by rfl⟩ : syracuseStep 24033809 = 18025357) B18025357
theorem B16022539 : Blo 2081435 16022539 := bstep (se 1 (by rfl) ⟨12016904, by rfl⟩ : syracuseStep 16022539 = 24033809) B24033809
theorem B85453541 : Blo 2081435 85453541 := bstep (se 4 (by rfl) ⟨8011269, by rfl⟩ : syracuseStep 85453541 = 16022539) B16022539
theorem B56969027 : Blo 2081435 56969027 := bstep (se 1 (by rfl) ⟨42726770, by rfl⟩ : syracuseStep 56969027 = 85453541) B85453541
theorem B37979351 : Blo 2081435 37979351 := bstep (se 1 (by rfl) ⟨28484513, by rfl⟩ : syracuseStep 37979351 = 56969027) B56969027
theorem B25319567 : Blo 2081435 25319567 := bstep (se 1 (by rfl) ⟨18989675, by rfl⟩ : syracuseStep 25319567 = 37979351) B37979351
theorem B16879711 : Blo 2081435 16879711 := bstep (se 1 (by rfl) ⟨12659783, by rfl⟩ : syracuseStep 16879711 = 25319567) B25319567
theorem B22506281 : Blo 2081435 22506281 := bstep (se 2 (by rfl) ⟨8439855, by rfl⟩ : syracuseStep 22506281 = 16879711) B16879711
theorem B15004187 : Blo 2081435 15004187 := bstep (se 1 (by rfl) ⟨11253140, by rfl⟩ : syracuseStep 15004187 = 22506281) B22506281
theorem B10002791 : Blo 2081435 10002791 := bstep (se 1 (by rfl) ⟨7502093, by rfl⟩ : syracuseStep 10002791 = 15004187) B15004187
theorem B26674109 : Blo 2081435 26674109 := bstep (se 3 (by rfl) ⟨5001395, by rfl⟩ : syracuseStep 26674109 = 10002791) B10002791
theorem B17782739 : Blo 2081435 17782739 := bstep (se 1 (by rfl) ⟨13337054, by rfl⟩ : syracuseStep 17782739 = 26674109) B26674109
theorem B11855159 : Blo 2081435 11855159 := bstep (se 1 (by rfl) ⟨8891369, by rfl⟩ : syracuseStep 11855159 = 17782739) B17782739
theorem B7903439 : Blo 2081435 7903439 := bstep (se 1 (by rfl) ⟨5927579, by rfl⟩ : syracuseStep 7903439 = 11855159) B11855159
theorem B5268959 : Blo 2081435 5268959 := bstep (se 1 (by rfl) ⟨3951719, by rfl⟩ : syracuseStep 5268959 = 7903439) B7903439
theorem B3512639 : Blo 2081435 3512639 := bstep (se 1 (by rfl) ⟨2634479, by rfl⟩ : syracuseStep 3512639 = 5268959) B5268959
theorem B2341759 : Blo 2081435 2341759 := bstep (se 1 (by rfl) ⟨1756319, by rfl⟩ : syracuseStep 2341759 = 3512639) B3512639
theorem B3122345 : Blo 2081435 3122345 := bstep (se 2 (by rfl) ⟨1170879, by rfl⟩ : syracuseStep 3122345 = 2341759) B2341759
theorem B2081563 : Blo 2081435 2081563 := bstep (se 1 (by rfl) ⟨1561172, by rfl⟩ : syracuseStep 2081563 = 3122345) B3122345
theorem B4445693 : Blo 2081435 4445693 := bbase (se 3 (by rfl) ⟨833567, by rfl⟩ : syracuseStep 4445693 = 1667135) (by norm_num)
theorem B2963795 : Blo 2081435 2963795 := bstep (se 1 (by rfl) ⟨2222846, by rfl⟩ : syracuseStep 2963795 = 4445693) B4445693
theorem B7903453 : Blo 2081435 7903453 := bstep (se 3 (by rfl) ⟨1481897, by rfl⟩ : syracuseStep 7903453 = 2963795) B2963795
theorem B10537937 : Blo 2081435 10537937 := bstep (se 2 (by rfl) ⟨3951726, by rfl⟩ : syracuseStep 10537937 = 7903453) B7903453
theorem B7025291 : Blo 2081435 7025291 := bstep (se 1 (by rfl) ⟨5268968, by rfl⟩ : syracuseStep 7025291 = 10537937) B10537937
theorem B4683527 : Blo 2081435 4683527 := bstep (se 1 (by rfl) ⟨3512645, by rfl⟩ : syracuseStep 4683527 = 7025291) B7025291
theorem B3122351 : Blo 2081435 3122351 := bstep (se 1 (by rfl) ⟨2341763, by rfl⟩ : syracuseStep 3122351 = 4683527) B4683527
theorem B2081567 : Blo 2081435 2081567 := bstep (se 1 (by rfl) ⟨1561175, by rfl⟩ : syracuseStep 2081567 = 3122351) B3122351
theorem B3122357 : Blo 2081435 3122357 := bbase (se 5 (by rfl) ⟨146360, by rfl⟩ : syracuseStep 3122357 = 292721) (by norm_num)
theorem B2081571 : Blo 2081435 2081571 := bstep (se 1 (by rfl) ⟨1561178, by rfl⟩ : syracuseStep 2081571 = 3122357) B3122357
theorem B5268989 : Blo 2081435 5268989 := bbase (se 3 (by rfl) ⟨987935, by rfl⟩ : syracuseStep 5268989 = 1975871) (by norm_num)
theorem B3512659 : Blo 2081435 3512659 := bstep (se 1 (by rfl) ⟨2634494, by rfl⟩ : syracuseStep 3512659 = 5268989) B5268989
theorem B4683545 : Blo 2081435 4683545 := bstep (se 2 (by rfl) ⟨1756329, by rfl⟩ : syracuseStep 4683545 = 3512659) B3512659
theorem B3122363 : Blo 2081435 3122363 := bstep (se 1 (by rfl) ⟨2341772, by rfl⟩ : syracuseStep 3122363 = 4683545) B4683545
theorem B2081575 : Blo 2081435 2081575 := bstep (se 1 (by rfl) ⟨1561181, by rfl⟩ : syracuseStep 2081575 = 3122363) B3122363
theorem B2341777 : Blo 2081435 2341777 := bbase (se 2 (by rfl) ⟨878166, by rfl⟩ : syracuseStep 2341777 = 1756333) (by norm_num)
theorem B3122369 : Blo 2081435 3122369 := bstep (se 2 (by rfl) ⟨1170888, by rfl⟩ : syracuseStep 3122369 = 2341777) B2341777
theorem B2081579 : Blo 2081435 2081579 := bstep (se 1 (by rfl) ⟨1561184, by rfl⟩ : syracuseStep 2081579 = 3122369) B3122369
theorem B3951757 : Blo 2081435 3951757 := bbase (se 3 (by rfl) ⟨740954, by rfl⟩ : syracuseStep 3951757 = 1481909) (by norm_num)
theorem B5269009 : Blo 2081435 5269009 := bstep (se 2 (by rfl) ⟨1975878, by rfl⟩ : syracuseStep 5269009 = 3951757) B3951757
theorem B7025345 : Blo 2081435 7025345 := bstep (se 2 (by rfl) ⟨2634504, by rfl⟩ : syracuseStep 7025345 = 5269009) B5269009
theorem B4683563 : Blo 2081435 4683563 := bstep (se 1 (by rfl) ⟨3512672, by rfl⟩ : syracuseStep 4683563 = 7025345) B7025345
theorem B3122375 : Blo 2081435 3122375 := bstep (se 1 (by rfl) ⟨2341781, by rfl⟩ : syracuseStep 3122375 = 4683563) B4683563
theorem B2081583 : Blo 2081435 2081583 := bstep (se 1 (by rfl) ⟨1561187, by rfl⟩ : syracuseStep 2081583 = 3122375) B3122375
theorem B3122381 : Blo 2081435 3122381 := bbase (se 3 (by rfl) ⟨585446, by rfl⟩ : syracuseStep 3122381 = 1170893) (by norm_num)
theorem B2081587 : Blo 2081435 2081587 := bstep (se 1 (by rfl) ⟨1561190, by rfl⟩ : syracuseStep 2081587 = 3122381) B3122381
theorem B4683581 : Blo 2081435 4683581 := bbase (se 3 (by rfl) ⟨878171, by rfl⟩ : syracuseStep 4683581 = 1756343) (by norm_num)
theorem B3122387 : Blo 2081435 3122387 := bstep (se 1 (by rfl) ⟨2341790, by rfl⟩ : syracuseStep 3122387 = 4683581) B4683581
theorem B2081591 : Blo 2081435 2081591 := bstep (se 1 (by rfl) ⟨1561193, by rfl⟩ : syracuseStep 2081591 = 3122387) B3122387
theorem B3512693 : Blo 2081435 3512693 := bbase (se 5 (by rfl) ⟨164657, by rfl⟩ : syracuseStep 3512693 = 329315) (by norm_num)
theorem B2341795 : Blo 2081435 2341795 := bstep (se 1 (by rfl) ⟨1756346, by rfl⟩ : syracuseStep 2341795 = 3512693) B3512693
theorem B3122393 : Blo 2081435 3122393 := bstep (se 2 (by rfl) ⟨1170897, by rfl⟩ : syracuseStep 3122393 = 2341795) B2341795
theorem B2081595 : Blo 2081435 2081595 := bstep (se 1 (by rfl) ⟨1561196, by rfl⟩ : syracuseStep 2081595 = 3122393) B3122393
theorem B2500741 : Blo 2081435 2500741 := bbase (se 4 (by rfl) ⟨234444, by rfl⟩ : syracuseStep 2500741 = 468889) (by norm_num)
theorem B3334321 : Blo 2081435 3334321 := bstep (se 2 (by rfl) ⟨1250370, by rfl⟩ : syracuseStep 3334321 = 2500741) B2500741
theorem B4445761 : Blo 2081435 4445761 := bstep (se 2 (by rfl) ⟨1667160, by rfl⟩ : syracuseStep 4445761 = 3334321) B3334321
theorem B5927681 : Blo 2081435 5927681 := bstep (se 2 (by rfl) ⟨2222880, by rfl⟩ : syracuseStep 5927681 = 4445761) B4445761
theorem B15807149 : Blo 2081435 15807149 := bstep (se 3 (by rfl) ⟨2963840, by rfl⟩ : syracuseStep 15807149 = 5927681) B5927681
theorem B10538099 : Blo 2081435 10538099 := bstep (se 1 (by rfl) ⟨7903574, by rfl⟩ : syracuseStep 10538099 = 15807149) B15807149
theorem B7025399 : Blo 2081435 7025399 := bstep (se 1 (by rfl) ⟨5269049, by rfl⟩ : syracuseStep 7025399 = 10538099) B10538099
theorem B4683599 : Blo 2081435 4683599 := bstep (se 1 (by rfl) ⟨3512699, by rfl⟩ : syracuseStep 4683599 = 7025399) B7025399
theorem B3122399 : Blo 2081435 3122399 := bstep (se 1 (by rfl) ⟨2341799, by rfl⟩ : syracuseStep 3122399 = 4683599) B4683599
theorem B2081599 : Blo 2081435 2081599 := bstep (se 1 (by rfl) ⟨1561199, by rfl⟩ : syracuseStep 2081599 = 3122399) B3122399
theorem B3122405 : Blo 2081435 3122405 := bbase (se 4 (by rfl) ⟨292725, by rfl⟩ : syracuseStep 3122405 = 585451) (by norm_num)
theorem B2081603 : Blo 2081435 2081603 := bstep (se 1 (by rfl) ⟨1561202, by rfl⟩ : syracuseStep 2081603 = 3122405) B3122405
theorem B8440037 : Blo 2081435 8440037 := bbase (se 4 (by rfl) ⟨791253, by rfl⟩ : syracuseStep 8440037 = 1582507) (by norm_num)
theorem B5626691 : Blo 2081435 5626691 := bstep (se 1 (by rfl) ⟨4220018, by rfl⟩ : syracuseStep 5626691 = 8440037) B8440037
theorem B3751127 : Blo 2081435 3751127 := bstep (se 1 (by rfl) ⟨2813345, by rfl⟩ : syracuseStep 3751127 = 5626691) B5626691
theorem B2500751 : Blo 2081435 2500751 := bstep (se 1 (by rfl) ⟨1875563, by rfl⟩ : syracuseStep 2500751 = 3751127) B3751127
theorem B6668669 : Blo 2081435 6668669 := bstep (se 3 (by rfl) ⟨1250375, by rfl⟩ : syracuseStep 6668669 = 2500751) B2500751
theorem B4445779 : Blo 2081435 4445779 := bstep (se 1 (by rfl) ⟨3334334, by rfl⟩ : syracuseStep 4445779 = 6668669) B6668669
theorem B5927705 : Blo 2081435 5927705 := bstep (se 2 (by rfl) ⟨2222889, by rfl⟩ : syracuseStep 5927705 = 4445779) B4445779
theorem B3951803 : Blo 2081435 3951803 := bstep (se 1 (by rfl) ⟨2963852, by rfl⟩ : syracuseStep 3951803 = 5927705) B5927705
theorem B2634535 : Blo 2081435 2634535 := bstep (se 1 (by rfl) ⟨1975901, by rfl⟩ : syracuseStep 2634535 = 3951803) B3951803
theorem B3512713 : Blo 2081435 3512713 := bstep (se 2 (by rfl) ⟨1317267, by rfl⟩ : syracuseStep 3512713 = 2634535) B2634535
theorem B4683617 : Blo 2081435 4683617 := bstep (se 2 (by rfl) ⟨1756356, by rfl⟩ : syracuseStep 4683617 = 3512713) B3512713
theorem B3122411 : Blo 2081435 3122411 := bstep (se 1 (by rfl) ⟨2341808, by rfl⟩ : syracuseStep 3122411 = 4683617) B4683617
theorem B2081607 : Blo 2081435 2081607 := bstep (se 1 (by rfl) ⟨1561205, by rfl⟩ : syracuseStep 2081607 = 3122411) B3122411
theorem B2341813 : Blo 2081435 2341813 := bbase (se 5 (by rfl) ⟨109772, by rfl⟩ : syracuseStep 2341813 = 219545) (by norm_num)
theorem B3122417 : Blo 2081435 3122417 := bstep (se 2 (by rfl) ⟨1170906, by rfl⟩ : syracuseStep 3122417 = 2341813) B2341813
theorem B2081611 : Blo 2081435 2081611 := bstep (se 1 (by rfl) ⟨1561208, by rfl⟩ : syracuseStep 2081611 = 3122417) B3122417
theorem B2634545 : Blo 2081435 2634545 := bbase (se 2 (by rfl) ⟨987954, by rfl⟩ : syracuseStep 2634545 = 1975909) (by norm_num)
theorem B7025453 : Blo 2081435 7025453 := bstep (se 3 (by rfl) ⟨1317272, by rfl⟩ : syracuseStep 7025453 = 2634545) B2634545
theorem B4683635 : Blo 2081435 4683635 := bstep (se 1 (by rfl) ⟨3512726, by rfl⟩ : syracuseStep 4683635 = 7025453) B7025453
theorem B3122423 : Blo 2081435 3122423 := bstep (se 1 (by rfl) ⟨2341817, by rfl⟩ : syracuseStep 3122423 = 4683635) B4683635
theorem B2081615 : Blo 2081435 2081615 := bstep (se 1 (by rfl) ⟨1561211, by rfl⟩ : syracuseStep 2081615 = 3122423) B3122423
theorem B3122429 : Blo 2081435 3122429 := bbase (se 3 (by rfl) ⟨585455, by rfl⟩ : syracuseStep 3122429 = 1170911) (by norm_num)
theorem B2081619 : Blo 2081435 2081619 := bstep (se 1 (by rfl) ⟨1561214, by rfl⟩ : syracuseStep 2081619 = 3122429) B3122429
theorem B4683653 : Blo 2081435 4683653 := bbase (se 4 (by rfl) ⟨439092, by rfl⟩ : syracuseStep 4683653 = 878185) (by norm_num)
theorem B3122435 : Blo 2081435 3122435 := bstep (se 1 (by rfl) ⟨2341826, by rfl⟩ : syracuseStep 3122435 = 4683653) B4683653
theorem B2081623 : Blo 2081435 2081623 := bstep (se 1 (by rfl) ⟨1561217, by rfl⟩ : syracuseStep 2081623 = 3122435) B3122435
theorem B15416885 : Blo 2081435 15416885 := bbase (se 5 (by rfl) ⟨722666, by rfl⟩ : syracuseStep 15416885 = 1445333) (by norm_num)
theorem B10277923 : Blo 2081435 10277923 := bstep (se 1 (by rfl) ⟨7708442, by rfl⟩ : syracuseStep 10277923 = 15416885) B15416885
theorem B13703897 : Blo 2081435 13703897 := bstep (se 2 (by rfl) ⟨5138961, by rfl⟩ : syracuseStep 13703897 = 10277923) B10277923
theorem B9135931 : Blo 2081435 9135931 := bstep (se 1 (by rfl) ⟨6851948, by rfl⟩ : syracuseStep 9135931 = 13703897) B13703897
theorem B12181241 : Blo 2081435 12181241 := bstep (se 2 (by rfl) ⟨4567965, by rfl⟩ : syracuseStep 12181241 = 9135931) B9135931
theorem B8120827 : Blo 2081435 8120827 := bstep (se 1 (by rfl) ⟨6090620, by rfl⟩ : syracuseStep 8120827 = 12181241) B12181241
theorem B10827769 : Blo 2081435 10827769 := bstep (se 2 (by rfl) ⟨4060413, by rfl⟩ : syracuseStep 10827769 = 8120827) B8120827
theorem B14437025 : Blo 2081435 14437025 := bstep (se 2 (by rfl) ⟨5413884, by rfl⟩ : syracuseStep 14437025 = 10827769) B10827769
theorem B9624683 : Blo 2081435 9624683 := bstep (se 1 (by rfl) ⟨7218512, by rfl⟩ : syracuseStep 9624683 = 14437025) B14437025
theorem B25665821 : Blo 2081435 25665821 := bstep (se 3 (by rfl) ⟨4812341, by rfl⟩ : syracuseStep 25665821 = 9624683) B9624683
theorem B17110547 : Blo 2081435 17110547 := bstep (se 1 (by rfl) ⟨12832910, by rfl⟩ : syracuseStep 17110547 = 25665821) B25665821
theorem B11407031 : Blo 2081435 11407031 := bstep (se 1 (by rfl) ⟨8555273, by rfl⟩ : syracuseStep 11407031 = 17110547) B17110547
theorem B7604687 : Blo 2081435 7604687 := bstep (se 1 (by rfl) ⟨5703515, by rfl⟩ : syracuseStep 7604687 = 11407031) B11407031
theorem B5069791 : Blo 2081435 5069791 := bstep (se 1 (by rfl) ⟨3802343, by rfl⟩ : syracuseStep 5069791 = 7604687) B7604687
theorem B6759721 : Blo 2081435 6759721 := bstep (se 2 (by rfl) ⟨2534895, by rfl⟩ : syracuseStep 6759721 = 5069791) B5069791
theorem B9012961 : Blo 2081435 9012961 := bstep (se 2 (by rfl) ⟨3379860, by rfl⟩ : syracuseStep 9012961 = 6759721) B6759721
theorem B12017281 : Blo 2081435 12017281 := bstep (se 2 (by rfl) ⟨4506480, by rfl⟩ : syracuseStep 12017281 = 9012961) B9012961
theorem B16023041 : Blo 2081435 16023041 := bstep (se 2 (by rfl) ⟨6008640, by rfl⟩ : syracuseStep 16023041 = 12017281) B12017281
theorem B10682027 : Blo 2081435 10682027 := bstep (se 1 (by rfl) ⟨8011520, by rfl⟩ : syracuseStep 10682027 = 16023041) B16023041
theorem B7121351 : Blo 2081435 7121351 := bstep (se 1 (by rfl) ⟨5341013, by rfl⟩ : syracuseStep 7121351 = 10682027) B10682027
theorem B4747567 : Blo 2081435 4747567 := bstep (se 1 (by rfl) ⟨3560675, by rfl⟩ : syracuseStep 4747567 = 7121351) B7121351
theorem B6330089 : Blo 2081435 6330089 := bstep (se 2 (by rfl) ⟨2373783, by rfl⟩ : syracuseStep 6330089 = 4747567) B4747567
theorem B16880237 : Blo 2081435 16880237 := bstep (se 3 (by rfl) ⟨3165044, by rfl⟩ : syracuseStep 16880237 = 6330089) B6330089
theorem B11253491 : Blo 2081435 11253491 := bstep (se 1 (by rfl) ⟨8440118, by rfl⟩ : syracuseStep 11253491 = 16880237) B16880237
theorem B7502327 : Blo 2081435 7502327 := bstep (se 1 (by rfl) ⟨5626745, by rfl⟩ : syracuseStep 7502327 = 11253491) B11253491
theorem B5001551 : Blo 2081435 5001551 := bstep (se 1 (by rfl) ⟨3751163, by rfl⟩ : syracuseStep 5001551 = 7502327) B7502327
theorem B3334367 : Blo 2081435 3334367 := bstep (se 1 (by rfl) ⟨2500775, by rfl⟩ : syracuseStep 3334367 = 5001551) B5001551
theorem B2222911 : Blo 2081435 2222911 := bstep (se 1 (by rfl) ⟨1667183, by rfl⟩ : syracuseStep 2222911 = 3334367) B3334367
theorem B2963881 : Blo 2081435 2963881 := bstep (se 2 (by rfl) ⟨1111455, by rfl⟩ : syracuseStep 2963881 = 2222911) B2222911
theorem B3951841 : Blo 2081435 3951841 := bstep (se 2 (by rfl) ⟨1481940, by rfl⟩ : syracuseStep 3951841 = 2963881) B2963881
theorem B5269121 : Blo 2081435 5269121 := bstep (se 2 (by rfl) ⟨1975920, by rfl⟩ : syracuseStep 5269121 = 3951841) B3951841
theorem B3512747 : Blo 2081435 3512747 := bstep (se 1 (by rfl) ⟨2634560, by rfl⟩ : syracuseStep 3512747 = 5269121) B5269121
theorem B2341831 : Blo 2081435 2341831 := bstep (se 1 (by rfl) ⟨1756373, by rfl⟩ : syracuseStep 2341831 = 3512747) B3512747
theorem B3122441 : Blo 2081435 3122441 := bstep (se 2 (by rfl) ⟨1170915, by rfl⟩ : syracuseStep 3122441 = 2341831) B2341831
theorem B2081627 : Blo 2081435 2081627 := bstep (se 1 (by rfl) ⟨1561220, by rfl⟩ : syracuseStep 2081627 = 3122441) B3122441
theorem B10538261 : Blo 2081435 10538261 := bbase (se 6 (by rfl) ⟨246990, by rfl⟩ : syracuseStep 10538261 = 493981) (by norm_num)
theorem B7025507 : Blo 2081435 7025507 := bstep (se 1 (by rfl) ⟨5269130, by rfl⟩ : syracuseStep 7025507 = 10538261) B10538261
theorem B4683671 : Blo 2081435 4683671 := bstep (se 1 (by rfl) ⟨3512753, by rfl⟩ : syracuseStep 4683671 = 7025507) B7025507
theorem B3122447 : Blo 2081435 3122447 := bstep (se 1 (by rfl) ⟨2341835, by rfl⟩ : syracuseStep 3122447 = 4683671) B4683671
theorem B2081631 : Blo 2081435 2081631 := bstep (se 1 (by rfl) ⟨1561223, by rfl⟩ : syracuseStep 2081631 = 3122447) B3122447
theorem B3122453 : Blo 2081435 3122453 := bbase (se 6 (by rfl) ⟨73182, by rfl⟩ : syracuseStep 3122453 = 146365) (by norm_num)
theorem B2081635 : Blo 2081435 2081635 := bstep (se 1 (by rfl) ⟨1561226, by rfl⟩ : syracuseStep 2081635 = 3122453) B3122453
theorem B30418901 : Blo 2081435 30418901 := bbase (se 7 (by rfl) ⟨356471, by rfl⟩ : syracuseStep 30418901 = 712943) (by norm_num)
theorem B20279267 : Blo 2081435 20279267 := bstep (se 1 (by rfl) ⟨15209450, by rfl⟩ : syracuseStep 20279267 = 30418901) B30418901
theorem B13519511 : Blo 2081435 13519511 := bstep (se 1 (by rfl) ⟨10139633, by rfl⟩ : syracuseStep 13519511 = 20279267) B20279267
theorem B9013007 : Blo 2081435 9013007 := bstep (se 1 (by rfl) ⟨6759755, by rfl⟩ : syracuseStep 9013007 = 13519511) B13519511
theorem B6008671 : Blo 2081435 6008671 := bstep (se 1 (by rfl) ⟨4506503, by rfl⟩ : syracuseStep 6008671 = 9013007) B9013007
theorem B32046245 : Blo 2081435 32046245 := bstep (se 4 (by rfl) ⟨3004335, by rfl⟩ : syracuseStep 32046245 = 6008671) B6008671
theorem B21364163 : Blo 2081435 21364163 := bstep (se 1 (by rfl) ⟨16023122, by rfl⟩ : syracuseStep 21364163 = 32046245) B32046245
theorem B14242775 : Blo 2081435 14242775 := bstep (se 1 (by rfl) ⟨10682081, by rfl⟩ : syracuseStep 14242775 = 21364163) B21364163
theorem B37980733 : Blo 2081435 37980733 := bstep (se 3 (by rfl) ⟨7121387, by rfl⟩ : syracuseStep 37980733 = 14242775) B14242775
theorem B50640977 : Blo 2081435 50640977 := bstep (se 2 (by rfl) ⟨18990366, by rfl⟩ : syracuseStep 50640977 = 37980733) B37980733
theorem B33760651 : Blo 2081435 33760651 := bstep (se 1 (by rfl) ⟨25320488, by rfl⟩ : syracuseStep 33760651 = 50640977) B50640977
theorem B45014201 : Blo 2081435 45014201 := bstep (se 2 (by rfl) ⟨16880325, by rfl⟩ : syracuseStep 45014201 = 33760651) B33760651
theorem B30009467 : Blo 2081435 30009467 := bstep (se 1 (by rfl) ⟨22507100, by rfl⟩ : syracuseStep 30009467 = 45014201) B45014201
theorem B20006311 : Blo 2081435 20006311 := bstep (se 1 (by rfl) ⟨15004733, by rfl⟩ : syracuseStep 20006311 = 30009467) B30009467
theorem B26675081 : Blo 2081435 26675081 := bstep (se 2 (by rfl) ⟨10003155, by rfl⟩ : syracuseStep 26675081 = 20006311) B20006311
theorem B17783387 : Blo 2081435 17783387 := bstep (se 1 (by rfl) ⟨13337540, by rfl⟩ : syracuseStep 17783387 = 26675081) B26675081
theorem B11855591 : Blo 2081435 11855591 := bstep (se 1 (by rfl) ⟨8891693, by rfl⟩ : syracuseStep 11855591 = 17783387) B17783387
theorem B7903727 : Blo 2081435 7903727 := bstep (se 1 (by rfl) ⟨5927795, by rfl⟩ : syracuseStep 7903727 = 11855591) B11855591
theorem B5269151 : Blo 2081435 5269151 := bstep (se 1 (by rfl) ⟨3951863, by rfl⟩ : syracuseStep 5269151 = 7903727) B7903727
theorem B3512767 : Blo 2081435 3512767 := bstep (se 1 (by rfl) ⟨2634575, by rfl⟩ : syracuseStep 3512767 = 5269151) B5269151
theorem B4683689 : Blo 2081435 4683689 := bstep (se 2 (by rfl) ⟨1756383, by rfl⟩ : syracuseStep 4683689 = 3512767) B3512767
theorem B3122459 : Blo 2081435 3122459 := bstep (se 1 (by rfl) ⟨2341844, by rfl⟩ : syracuseStep 3122459 = 4683689) B4683689
theorem B2081639 : Blo 2081435 2081639 := bstep (se 1 (by rfl) ⟨1561229, by rfl⟩ : syracuseStep 2081639 = 3122459) B3122459
theorem B2341849 : Blo 2081435 2341849 := bbase (se 2 (by rfl) ⟨878193, by rfl⟩ : syracuseStep 2341849 = 1756387) (by norm_num)
theorem B3122465 : Blo 2081435 3122465 := bstep (se 2 (by rfl) ⟨1170924, by rfl⟩ : syracuseStep 3122465 = 2341849) B2341849
theorem B2081643 : Blo 2081435 2081643 := bstep (se 1 (by rfl) ⟨1561232, by rfl⟩ : syracuseStep 2081643 = 3122465) B3122465
theorem B2963909 : Blo 2081435 2963909 := bbase (se 4 (by rfl) ⟨277866, by rfl⟩ : syracuseStep 2963909 = 555733) (by norm_num)
theorem B7903757 : Blo 2081435 7903757 := bstep (se 3 (by rfl) ⟨1481954, by rfl⟩ : syracuseStep 7903757 = 2963909) B2963909
theorem B5269171 : Blo 2081435 5269171 := bstep (se 1 (by rfl) ⟨3951878, by rfl⟩ : syracuseStep 5269171 = 7903757) B7903757
theorem B7025561 : Blo 2081435 7025561 := bstep (se 2 (by rfl) ⟨2634585, by rfl⟩ : syracuseStep 7025561 = 5269171) B5269171
theorem B4683707 : Blo 2081435 4683707 := bstep (se 1 (by rfl) ⟨3512780, by rfl⟩ : syracuseStep 4683707 = 7025561) B7025561
theorem B3122471 : Blo 2081435 3122471 := bstep (se 1 (by rfl) ⟨2341853, by rfl⟩ : syracuseStep 3122471 = 4683707) B4683707
theorem B2081647 : Blo 2081435 2081647 := bstep (se 1 (by rfl) ⟨1561235, by rfl⟩ : syracuseStep 2081647 = 3122471) B3122471
theorem B3122477 : Blo 2081435 3122477 := bbase (se 3 (by rfl) ⟨585464, by rfl⟩ : syracuseStep 3122477 = 1170929) (by norm_num)
theorem B2081651 : Blo 2081435 2081651 := bstep (se 1 (by rfl) ⟨1561238, by rfl⟩ : syracuseStep 2081651 = 3122477) B3122477
theorem B4683725 : Blo 2081435 4683725 := bbase (se 3 (by rfl) ⟨878198, by rfl⟩ : syracuseStep 4683725 = 1756397) (by norm_num)
theorem B3122483 : Blo 2081435 3122483 := bstep (se 1 (by rfl) ⟨2341862, by rfl⟩ : syracuseStep 3122483 = 4683725) B4683725
theorem B2081655 : Blo 2081435 2081655 := bstep (se 1 (by rfl) ⟨1561241, by rfl⟩ : syracuseStep 2081655 = 3122483) B3122483
theorem B2634601 : Blo 2081435 2634601 := bbase (se 2 (by rfl) ⟨987975, by rfl⟩ : syracuseStep 2634601 = 1975951) (by norm_num)
theorem B3512801 : Blo 2081435 3512801 := bstep (se 2 (by rfl) ⟨1317300, by rfl⟩ : syracuseStep 3512801 = 2634601) B2634601
theorem B2341867 : Blo 2081435 2341867 := bstep (se 1 (by rfl) ⟨1756400, by rfl⟩ : syracuseStep 2341867 = 3512801) B3512801
theorem B3122489 : Blo 2081435 3122489 := bstep (se 2 (by rfl) ⟨1170933, by rfl⟩ : syracuseStep 3122489 = 2341867) B2341867
theorem B2081659 : Blo 2081435 2081659 := bstep (se 1 (by rfl) ⟨1561244, by rfl⟩ : syracuseStep 2081659 = 3122489) B3122489
theorem B7502453 : Blo 2081435 7502453 := bbase (se 5 (by rfl) ⟨351677, by rfl⟩ : syracuseStep 7502453 = 703355) (by norm_num)
theorem B5001635 : Blo 2081435 5001635 := bstep (se 1 (by rfl) ⟨3751226, by rfl⟩ : syracuseStep 5001635 = 7502453) B7502453
theorem B13337693 : Blo 2081435 13337693 := bstep (se 3 (by rfl) ⟨2500817, by rfl⟩ : syracuseStep 13337693 = 5001635) B5001635
theorem B8891795 : Blo 2081435 8891795 := bstep (se 1 (by rfl) ⟨6668846, by rfl⟩ : syracuseStep 8891795 = 13337693) B13337693
theorem B23711453 : Blo 2081435 23711453 := bstep (se 3 (by rfl) ⟨4445897, by rfl⟩ : syracuseStep 23711453 = 8891795) B8891795
theorem B15807635 : Blo 2081435 15807635 := bstep (se 1 (by rfl) ⟨11855726, by rfl⟩ : syracuseStep 15807635 = 23711453) B23711453
theorem B10538423 : Blo 2081435 10538423 := bstep (se 1 (by rfl) ⟨7903817, by rfl⟩ : syracuseStep 10538423 = 15807635) B15807635
theorem B7025615 : Blo 2081435 7025615 := bstep (se 1 (by rfl) ⟨5269211, by rfl⟩ : syracuseStep 7025615 = 10538423) B10538423
theorem B4683743 : Blo 2081435 4683743 := bstep (se 1 (by rfl) ⟨3512807, by rfl⟩ : syracuseStep 4683743 = 7025615) B7025615
theorem B3122495 : Blo 2081435 3122495 := bstep (se 1 (by rfl) ⟨2341871, by rfl⟩ : syracuseStep 3122495 = 4683743) B4683743
theorem B2081663 : Blo 2081435 2081663 := bstep (se 1 (by rfl) ⟨1561247, by rfl⟩ : syracuseStep 2081663 = 3122495) B3122495
theorem B3122501 : Blo 2081435 3122501 := bbase (se 4 (by rfl) ⟨292734, by rfl⟩ : syracuseStep 3122501 = 585469) (by norm_num)
theorem B2081667 : Blo 2081435 2081667 := bstep (se 1 (by rfl) ⟨1561250, by rfl⟩ : syracuseStep 2081667 = 3122501) B3122501
theorem B3512821 : Blo 2081435 3512821 := bbase (se 5 (by rfl) ⟨164663, by rfl⟩ : syracuseStep 3512821 = 329327) (by norm_num)
theorem B4683761 : Blo 2081435 4683761 := bstep (se 2 (by rfl) ⟨1756410, by rfl⟩ : syracuseStep 4683761 = 3512821) B3512821
theorem B3122507 : Blo 2081435 3122507 := bstep (se 1 (by rfl) ⟨2341880, by rfl⟩ : syracuseStep 3122507 = 4683761) B4683761
theorem B2081671 : Blo 2081435 2081671 := bstep (se 1 (by rfl) ⟨1561253, by rfl⟩ : syracuseStep 2081671 = 3122507) B3122507
theorem B2341885 : Blo 2081435 2341885 := bbase (se 3 (by rfl) ⟨439103, by rfl⟩ : syracuseStep 2341885 = 878207) (by norm_num)
theorem B3122513 : Blo 2081435 3122513 := bstep (se 2 (by rfl) ⟨1170942, by rfl⟩ : syracuseStep 3122513 = 2341885) B2341885
theorem B2081675 : Blo 2081435 2081675 := bstep (se 1 (by rfl) ⟨1561256, by rfl⟩ : syracuseStep 2081675 = 3122513) B3122513
theorem B7025669 : Blo 2081435 7025669 := bbase (se 4 (by rfl) ⟨658656, by rfl⟩ : syracuseStep 7025669 = 1317313) (by norm_num)
theorem B4683779 : Blo 2081435 4683779 := bstep (se 1 (by rfl) ⟨3512834, by rfl⟩ : syracuseStep 4683779 = 7025669) B7025669
theorem B3122519 : Blo 2081435 3122519 := bstep (se 1 (by rfl) ⟨2341889, by rfl⟩ : syracuseStep 3122519 = 4683779) B4683779
theorem B2081679 : Blo 2081435 2081679 := bstep (se 1 (by rfl) ⟨1561259, by rfl⟩ : syracuseStep 2081679 = 3122519) B3122519
theorem B3122525 : Blo 2081435 3122525 := bbase (se 3 (by rfl) ⟨585473, by rfl⟩ : syracuseStep 3122525 = 1170947) (by norm_num)
theorem B2081683 : Blo 2081435 2081683 := bstep (se 1 (by rfl) ⟨1561262, by rfl⟩ : syracuseStep 2081683 = 3122525) B3122525
theorem B4683797 : Blo 2081435 4683797 := bbase (se 6 (by rfl) ⟨109776, by rfl⟩ : syracuseStep 4683797 = 219553) (by norm_num)
theorem B3122531 : Blo 2081435 3122531 := bstep (se 1 (by rfl) ⟨2341898, by rfl⟩ : syracuseStep 3122531 = 4683797) B4683797
theorem B2081687 : Blo 2081435 2081687 := bstep (se 1 (by rfl) ⟨1561265, by rfl⟩ : syracuseStep 2081687 = 3122531) B3122531
theorem B7903925 : Blo 2081435 7903925 := bbase (se 5 (by rfl) ⟨370496, by rfl⟩ : syracuseStep 7903925 = 740993) (by norm_num)
theorem B5269283 : Blo 2081435 5269283 := bstep (se 1 (by rfl) ⟨3951962, by rfl⟩ : syracuseStep 5269283 = 7903925) B7903925
theorem B3512855 : Blo 2081435 3512855 := bstep (se 1 (by rfl) ⟨2634641, by rfl⟩ : syracuseStep 3512855 = 5269283) B5269283
theorem B2341903 : Blo 2081435 2341903 := bstep (se 1 (by rfl) ⟨1756427, by rfl⟩ : syracuseStep 2341903 = 3512855) B3512855
theorem B3122537 : Blo 2081435 3122537 := bstep (se 2 (by rfl) ⟨1170951, by rfl⟩ : syracuseStep 3122537 = 2341903) B2341903
theorem B2081691 : Blo 2081435 2081691 := bstep (se 1 (by rfl) ⟨1561268, by rfl⟩ : syracuseStep 2081691 = 3122537) B3122537
theorem B3751285 : Blo 2081435 3751285 := bbase (se 5 (by rfl) ⟨175841, by rfl⟩ : syracuseStep 3751285 = 351683) (by norm_num)
theorem B5001713 : Blo 2081435 5001713 := bstep (se 2 (by rfl) ⟨1875642, by rfl⟩ : syracuseStep 5001713 = 3751285) B3751285
theorem B3334475 : Blo 2081435 3334475 := bstep (se 1 (by rfl) ⟨2500856, by rfl⟩ : syracuseStep 3334475 = 5001713) B5001713
theorem B2222983 : Blo 2081435 2222983 := bstep (se 1 (by rfl) ⟨1667237, by rfl⟩ : syracuseStep 2222983 = 3334475) B3334475
theorem B11855909 : Blo 2081435 11855909 := bstep (se 4 (by rfl) ⟨1111491, by rfl⟩ : syracuseStep 11855909 = 2222983) B2222983
theorem B7903939 : Blo 2081435 7903939 := bstep (se 1 (by rfl) ⟨5927954, by rfl⟩ : syracuseStep 7903939 = 11855909) B11855909
theorem B10538585 : Blo 2081435 10538585 := bstep (se 2 (by rfl) ⟨3951969, by rfl⟩ : syracuseStep 10538585 = 7903939) B7903939
theorem B7025723 : Blo 2081435 7025723 := bstep (se 1 (by rfl) ⟨5269292, by rfl⟩ : syracuseStep 7025723 = 10538585) B10538585
theorem B4683815 : Blo 2081435 4683815 := bstep (se 1 (by rfl) ⟨3512861, by rfl⟩ : syracuseStep 4683815 = 7025723) B7025723
theorem B3122543 : Blo 2081435 3122543 := bstep (se 1 (by rfl) ⟨2341907, by rfl⟩ : syracuseStep 3122543 = 4683815) B4683815
theorem B2081695 : Blo 2081435 2081695 := bstep (se 1 (by rfl) ⟨1561271, by rfl⟩ : syracuseStep 2081695 = 3122543) B3122543
theorem B3122549 : Blo 2081435 3122549 := bbase (se 5 (by rfl) ⟨146369, by rfl⟩ : syracuseStep 3122549 = 292739) (by norm_num)
theorem B2081699 : Blo 2081435 2081699 := bstep (se 1 (by rfl) ⟨1561274, by rfl⟩ : syracuseStep 2081699 = 3122549) B3122549
theorem B2963989 : Blo 2081435 2963989 := bbase (se 6 (by rfl) ⟨69468, by rfl⟩ : syracuseStep 2963989 = 138937) (by norm_num)
theorem B3951985 : Blo 2081435 3951985 := bstep (se 2 (by rfl) ⟨1481994, by rfl⟩ : syracuseStep 3951985 = 2963989) B2963989
theorem B5269313 : Blo 2081435 5269313 := bstep (se 2 (by rfl) ⟨1975992, by rfl⟩ : syracuseStep 5269313 = 3951985) B3951985
theorem B3512875 : Blo 2081435 3512875 := bstep (se 1 (by rfl) ⟨2634656, by rfl⟩ : syracuseStep 3512875 = 5269313) B5269313
theorem B4683833 : Blo 2081435 4683833 := bstep (se 2 (by rfl) ⟨1756437, by rfl⟩ : syracuseStep 4683833 = 3512875) B3512875
theorem B3122555 : Blo 2081435 3122555 := bstep (se 1 (by rfl) ⟨2341916, by rfl⟩ : syracuseStep 3122555 = 4683833) B4683833
theorem B2081703 : Blo 2081435 2081703 := bstep (se 1 (by rfl) ⟨1561277, by rfl⟩ : syracuseStep 2081703 = 3122555) B3122555
theorem B2341921 : Blo 2081435 2341921 := bbase (se 2 (by rfl) ⟨878220, by rfl⟩ : syracuseStep 2341921 = 1756441) (by norm_num)
theorem B3122561 : Blo 2081435 3122561 := bstep (se 2 (by rfl) ⟨1170960, by rfl⟩ : syracuseStep 3122561 = 2341921) B2341921
theorem B2081707 : Blo 2081435 2081707 := bstep (se 1 (by rfl) ⟨1561280, by rfl⟩ : syracuseStep 2081707 = 3122561) B3122561
theorem B5269333 : Blo 2081435 5269333 := bbase (se 9 (by rfl) ⟨15437, by rfl⟩ : syracuseStep 5269333 = 30875) (by norm_num)
theorem B7025777 : Blo 2081435 7025777 := bstep (se 2 (by rfl) ⟨2634666, by rfl⟩ : syracuseStep 7025777 = 5269333) B5269333
theorem B4683851 : Blo 2081435 4683851 := bstep (se 1 (by rfl) ⟨3512888, by rfl⟩ : syracuseStep 4683851 = 7025777) B7025777
theorem B3122567 : Blo 2081435 3122567 := bstep (se 1 (by rfl) ⟨2341925, by rfl⟩ : syracuseStep 3122567 = 4683851) B4683851
theorem B2081711 : Blo 2081435 2081711 := bstep (se 1 (by rfl) ⟨1561283, by rfl⟩ : syracuseStep 2081711 = 3122567) B3122567
theorem B3122573 : Blo 2081435 3122573 := bbase (se 3 (by rfl) ⟨585482, by rfl⟩ : syracuseStep 3122573 = 1170965) (by norm_num)
theorem B2081715 : Blo 2081435 2081715 := bstep (se 1 (by rfl) ⟨1561286, by rfl⟩ : syracuseStep 2081715 = 3122573) B3122573
theorem B4683869 : Blo 2081435 4683869 := bbase (se 3 (by rfl) ⟨878225, by rfl⟩ : syracuseStep 4683869 = 1756451) (by norm_num)
theorem B3122579 : Blo 2081435 3122579 := bstep (se 1 (by rfl) ⟨2341934, by rfl⟩ : syracuseStep 3122579 = 4683869) B4683869
theorem B2081719 : Blo 2081435 2081719 := bstep (se 1 (by rfl) ⟨1561289, by rfl⟩ : syracuseStep 2081719 = 3122579) B3122579
theorem B3512909 : Blo 2081435 3512909 := bbase (se 3 (by rfl) ⟨658670, by rfl⟩ : syracuseStep 3512909 = 1317341) (by norm_num)
theorem B2341939 : Blo 2081435 2341939 := bstep (se 1 (by rfl) ⟨1756454, by rfl⟩ : syracuseStep 2341939 = 3512909) B3512909
theorem B3122585 : Blo 2081435 3122585 := bstep (se 2 (by rfl) ⟨1170969, by rfl⟩ : syracuseStep 3122585 = 2341939) B2341939
theorem B2081723 : Blo 2081435 2081723 := bstep (se 1 (by rfl) ⟨1561292, by rfl⟩ : syracuseStep 2081723 = 3122585) B3122585
theorem B10682533 : Blo 2081435 10682533 := bbase (se 4 (by rfl) ⟨1001487, by rfl⟩ : syracuseStep 10682533 = 2002975) (by norm_num)
theorem B14243377 : Blo 2081435 14243377 := bstep (se 2 (by rfl) ⟨5341266, by rfl⟩ : syracuseStep 14243377 = 10682533) B10682533
theorem B18991169 : Blo 2081435 18991169 := bstep (se 2 (by rfl) ⟨7121688, by rfl⟩ : syracuseStep 18991169 = 14243377) B14243377
theorem B12660779 : Blo 2081435 12660779 := bstep (se 1 (by rfl) ⟨9495584, by rfl⟩ : syracuseStep 12660779 = 18991169) B18991169
theorem B8440519 : Blo 2081435 8440519 := bstep (se 1 (by rfl) ⟨6330389, by rfl⟩ : syracuseStep 8440519 = 12660779) B12660779
theorem B11254025 : Blo 2081435 11254025 := bstep (se 2 (by rfl) ⟨4220259, by rfl⟩ : syracuseStep 11254025 = 8440519) B8440519
theorem B30010733 : Blo 2081435 30010733 := bstep (se 3 (by rfl) ⟨5627012, by rfl⟩ : syracuseStep 30010733 = 11254025) B11254025
theorem B20007155 : Blo 2081435 20007155 := bstep (se 1 (by rfl) ⟨15005366, by rfl⟩ : syracuseStep 20007155 = 30010733) B30010733
theorem B13338103 : Blo 2081435 13338103 := bstep (se 1 (by rfl) ⟨10003577, by rfl⟩ : syracuseStep 13338103 = 20007155) B20007155
theorem B17784137 : Blo 2081435 17784137 := bstep (se 2 (by rfl) ⟨6669051, by rfl⟩ : syracuseStep 17784137 = 13338103) B13338103
theorem B11856091 : Blo 2081435 11856091 := bstep (se 1 (by rfl) ⟨8892068, by rfl⟩ : syracuseStep 11856091 = 17784137) B17784137
theorem B15808121 : Blo 2081435 15808121 := bstep (se 2 (by rfl) ⟨5928045, by rfl⟩ : syracuseStep 15808121 = 11856091) B11856091
theorem B10538747 : Blo 2081435 10538747 := bstep (se 1 (by rfl) ⟨7904060, by rfl⟩ : syracuseStep 10538747 = 15808121) B15808121
theorem B7025831 : Blo 2081435 7025831 := bstep (se 1 (by rfl) ⟨5269373, by rfl⟩ : syracuseStep 7025831 = 10538747) B10538747
theorem B4683887 : Blo 2081435 4683887 := bstep (se 1 (by rfl) ⟨3512915, by rfl⟩ : syracuseStep 4683887 = 7025831) B7025831
theorem B3122591 : Blo 2081435 3122591 := bstep (se 1 (by rfl) ⟨2341943, by rfl⟩ : syracuseStep 3122591 = 4683887) B4683887
theorem B2081727 : Blo 2081435 2081727 := bstep (se 1 (by rfl) ⟨1561295, by rfl⟩ : syracuseStep 2081727 = 3122591) B3122591
theorem B3122597 : Blo 2081435 3122597 := bbase (se 4 (by rfl) ⟨292743, by rfl⟩ : syracuseStep 3122597 = 585487) (by norm_num)
theorem B2081731 : Blo 2081435 2081731 := bstep (se 1 (by rfl) ⟨1561298, by rfl⟩ : syracuseStep 2081731 = 3122597) B3122597
theorem B2634697 : Blo 2081435 2634697 := bbase (se 2 (by rfl) ⟨988011, by rfl⟩ : syracuseStep 2634697 = 1976023) (by norm_num)
theorem B3512929 : Blo 2081435 3512929 := bstep (se 2 (by rfl) ⟨1317348, by rfl⟩ : syracuseStep 3512929 = 2634697) B2634697
theorem B4683905 : Blo 2081435 4683905 := bstep (se 2 (by rfl) ⟨1756464, by rfl⟩ : syracuseStep 4683905 = 3512929) B3512929
theorem B3122603 : Blo 2081435 3122603 := bstep (se 1 (by rfl) ⟨2341952, by rfl⟩ : syracuseStep 3122603 = 4683905) B4683905
theorem B2081735 : Blo 2081435 2081735 := bstep (se 1 (by rfl) ⟨1561301, by rfl⟩ : syracuseStep 2081735 = 3122603) B3122603
theorem B2341957 : Blo 2081435 2341957 := bbase (se 4 (by rfl) ⟨219558, by rfl⟩ : syracuseStep 2341957 = 439117) (by norm_num)
theorem B3122609 : Blo 2081435 3122609 := bstep (se 2 (by rfl) ⟨1170978, by rfl⟩ : syracuseStep 3122609 = 2341957) B2341957
theorem B2081739 : Blo 2081435 2081739 := bstep (se 1 (by rfl) ⟨1561304, by rfl⟩ : syracuseStep 2081739 = 3122609) B3122609
theorem B3952061 : Blo 2081435 3952061 := bbase (se 3 (by rfl) ⟨741011, by rfl⟩ : syracuseStep 3952061 = 1482023) (by norm_num)
theorem B2634707 : Blo 2081435 2634707 := bstep (se 1 (by rfl) ⟨1976030, by rfl⟩ : syracuseStep 2634707 = 3952061) B3952061
theorem B7025885 : Blo 2081435 7025885 := bstep (se 3 (by rfl) ⟨1317353, by rfl⟩ : syracuseStep 7025885 = 2634707) B2634707
theorem B4683923 : Blo 2081435 4683923 := bstep (se 1 (by rfl) ⟨3512942, by rfl⟩ : syracuseStep 4683923 = 7025885) B7025885
theorem B3122615 : Blo 2081435 3122615 := bstep (se 1 (by rfl) ⟨2341961, by rfl⟩ : syracuseStep 3122615 = 4683923) B4683923
theorem B2081743 : Blo 2081435 2081743 := bstep (se 1 (by rfl) ⟨1561307, by rfl⟩ : syracuseStep 2081743 = 3122615) B3122615
theorem B3122621 : Blo 2081435 3122621 := bbase (se 3 (by rfl) ⟨585491, by rfl⟩ : syracuseStep 3122621 = 1170983) (by norm_num)
theorem B2081747 : Blo 2081435 2081747 := bstep (se 1 (by rfl) ⟨1561310, by rfl⟩ : syracuseStep 2081747 = 3122621) B3122621
theorem B4683941 : Blo 2081435 4683941 := bbase (se 4 (by rfl) ⟨439119, by rfl⟩ : syracuseStep 4683941 = 878239) (by norm_num)
theorem B3122627 : Blo 2081435 3122627 := bstep (se 1 (by rfl) ⟨2341970, by rfl⟩ : syracuseStep 3122627 = 4683941) B4683941
theorem B2081751 : Blo 2081435 2081751 := bstep (se 1 (by rfl) ⟨1561313, by rfl⟩ : syracuseStep 2081751 = 3122627) B3122627
theorem B5269445 : Blo 2081435 5269445 := bbase (se 4 (by rfl) ⟨494010, by rfl⟩ : syracuseStep 5269445 = 988021) (by norm_num)
theorem B3512963 : Blo 2081435 3512963 := bstep (se 1 (by rfl) ⟨2634722, by rfl⟩ : syracuseStep 3512963 = 5269445) B5269445
theorem B2341975 : Blo 2081435 2341975 := bstep (se 1 (by rfl) ⟨1756481, by rfl⟩ : syracuseStep 2341975 = 3512963) B3512963
theorem B3122633 : Blo 2081435 3122633 := bstep (se 2 (by rfl) ⟨1170987, by rfl⟩ : syracuseStep 3122633 = 2341975) B2341975
theorem B2081755 : Blo 2081435 2081755 := bstep (se 1 (by rfl) ⟨1561316, by rfl⟩ : syracuseStep 2081755 = 3122633) B3122633
theorem B10003733 : Blo 2081435 10003733 := bbase (se 6 (by rfl) ⟨234462, by rfl⟩ : syracuseStep 10003733 = 468925) (by norm_num)
theorem B6669155 : Blo 2081435 6669155 := bstep (se 1 (by rfl) ⟨5001866, by rfl⟩ : syracuseStep 6669155 = 10003733) B10003733
theorem B4446103 : Blo 2081435 4446103 := bstep (se 1 (by rfl) ⟨3334577, by rfl⟩ : syracuseStep 4446103 = 6669155) B6669155
theorem B5928137 : Blo 2081435 5928137 := bstep (se 2 (by rfl) ⟨2223051, by rfl⟩ : syracuseStep 5928137 = 4446103) B4446103
theorem B3952091 : Blo 2081435 3952091 := bstep (se 1 (by rfl) ⟨2964068, by rfl⟩ : syracuseStep 3952091 = 5928137) B5928137
theorem B10538909 : Blo 2081435 10538909 := bstep (se 3 (by rfl) ⟨1976045, by rfl⟩ : syracuseStep 10538909 = 3952091) B3952091
theorem B7025939 : Blo 2081435 7025939 := bstep (se 1 (by rfl) ⟨5269454, by rfl⟩ : syracuseStep 7025939 = 10538909) B10538909
theorem B4683959 : Blo 2081435 4683959 := bstep (se 1 (by rfl) ⟨3512969, by rfl⟩ : syracuseStep 4683959 = 7025939) B7025939
theorem B3122639 : Blo 2081435 3122639 := bstep (se 1 (by rfl) ⟨2341979, by rfl⟩ : syracuseStep 3122639 = 4683959) B4683959
theorem B2081759 : Blo 2081435 2081759 := bstep (se 1 (by rfl) ⟨1561319, by rfl⟩ : syracuseStep 2081759 = 3122639) B3122639
theorem B3122645 : Blo 2081435 3122645 := bbase (se 7 (by rfl) ⟨36593, by rfl⟩ : syracuseStep 3122645 = 73187) (by norm_num)
theorem B2081763 : Blo 2081435 2081763 := bstep (se 1 (by rfl) ⟨1561322, by rfl⟩ : syracuseStep 2081763 = 3122645) B3122645
theorem B7904213 : Blo 2081435 7904213 := bbase (se 7 (by rfl) ⟨92627, by rfl⟩ : syracuseStep 7904213 = 185255) (by norm_num)
theorem B5269475 : Blo 2081435 5269475 := bstep (se 1 (by rfl) ⟨3952106, by rfl⟩ : syracuseStep 5269475 = 7904213) B7904213
theorem B3512983 : Blo 2081435 3512983 := bstep (se 1 (by rfl) ⟨2634737, by rfl⟩ : syracuseStep 3512983 = 5269475) B5269475
theorem B4683977 : Blo 2081435 4683977 := bstep (se 2 (by rfl) ⟨1756491, by rfl⟩ : syracuseStep 4683977 = 3512983) B3512983
theorem B3122651 : Blo 2081435 3122651 := bstep (se 1 (by rfl) ⟨2341988, by rfl⟩ : syracuseStep 3122651 = 4683977) B4683977
theorem B2081767 : Blo 2081435 2081767 := bstep (se 1 (by rfl) ⟨1561325, by rfl⟩ : syracuseStep 2081767 = 3122651) B3122651
theorem B2341993 : Blo 2081435 2341993 := bbase (se 2 (by rfl) ⟨878247, by rfl⟩ : syracuseStep 2341993 = 1756495) (by norm_num)
theorem B3122657 : Blo 2081435 3122657 := bstep (se 2 (by rfl) ⟨1170996, by rfl⟩ : syracuseStep 3122657 = 2341993) B2341993
theorem B2081771 : Blo 2081435 2081771 := bstep (se 1 (by rfl) ⟨1561328, by rfl⟩ : syracuseStep 2081771 = 3122657) B3122657
theorem B3751429 : Blo 2081435 3751429 := bbase (se 4 (by rfl) ⟨351696, by rfl⟩ : syracuseStep 3751429 = 703393) (by norm_num)
theorem B5001905 : Blo 2081435 5001905 := bstep (se 2 (by rfl) ⟨1875714, by rfl⟩ : syracuseStep 5001905 = 3751429) B3751429
theorem B3334603 : Blo 2081435 3334603 := bstep (se 1 (by rfl) ⟨2500952, by rfl⟩ : syracuseStep 3334603 = 5001905) B5001905
theorem B4446137 : Blo 2081435 4446137 := bstep (se 2 (by rfl) ⟨1667301, by rfl⟩ : syracuseStep 4446137 = 3334603) B3334603
theorem B11856365 : Blo 2081435 11856365 := bstep (se 3 (by rfl) ⟨2223068, by rfl⟩ : syracuseStep 11856365 = 4446137) B4446137
theorem B7904243 : Blo 2081435 7904243 := bstep (se 1 (by rfl) ⟨5928182, by rfl⟩ : syracuseStep 7904243 = 11856365) B11856365
theorem B5269495 : Blo 2081435 5269495 := bstep (se 1 (by rfl) ⟨3952121, by rfl⟩ : syracuseStep 5269495 = 7904243) B7904243
theorem B7025993 : Blo 2081435 7025993 := bstep (se 2 (by rfl) ⟨2634747, by rfl⟩ : syracuseStep 7025993 = 5269495) B5269495
theorem B4683995 : Blo 2081435 4683995 := bstep (se 1 (by rfl) ⟨3512996, by rfl⟩ : syracuseStep 4683995 = 7025993) B7025993
theorem B3122663 : Blo 2081435 3122663 := bstep (se 1 (by rfl) ⟨2341997, by rfl⟩ : syracuseStep 3122663 = 4683995) B4683995
theorem B2081775 : Blo 2081435 2081775 := bstep (se 1 (by rfl) ⟨1561331, by rfl⟩ : syracuseStep 2081775 = 3122663) B3122663
theorem B3122669 : Blo 2081435 3122669 := bbase (se 3 (by rfl) ⟨585500, by rfl⟩ : syracuseStep 3122669 = 1171001) (by norm_num)
theorem B2081779 : Blo 2081435 2081779 := bstep (se 1 (by rfl) ⟨1561334, by rfl⟩ : syracuseStep 2081779 = 3122669) B3122669
theorem B4684013 : Blo 2081435 4684013 := bbase (se 3 (by rfl) ⟨878252, by rfl⟩ : syracuseStep 4684013 = 1756505) (by norm_num)
theorem B3122675 : Blo 2081435 3122675 := bstep (se 1 (by rfl) ⟨2342006, by rfl⟩ : syracuseStep 3122675 = 4684013) B4684013
theorem B2081783 : Blo 2081435 2081783 := bstep (se 1 (by rfl) ⟨1561337, by rfl⟩ : syracuseStep 2081783 = 3122675) B3122675
theorem B2964109 : Blo 2081435 2964109 := bbase (se 3 (by rfl) ⟨555770, by rfl⟩ : syracuseStep 2964109 = 1111541) (by norm_num)
theorem B3952145 : Blo 2081435 3952145 := bstep (se 2 (by rfl) ⟨1482054, by rfl⟩ : syracuseStep 3952145 = 2964109) B2964109
theorem B2634763 : Blo 2081435 2634763 := bstep (se 1 (by rfl) ⟨1976072, by rfl⟩ : syracuseStep 2634763 = 3952145) B3952145
theorem B3513017 : Blo 2081435 3513017 := bstep (se 2 (by rfl) ⟨1317381, by rfl⟩ : syracuseStep 3513017 = 2634763) B2634763
theorem B2342011 : Blo 2081435 2342011 := bstep (se 1 (by rfl) ⟨1756508, by rfl⟩ : syracuseStep 2342011 = 3513017) B3513017
theorem B3122681 : Blo 2081435 3122681 := bstep (se 2 (by rfl) ⟨1171005, by rfl⟩ : syracuseStep 3122681 = 2342011) B2342011
theorem B2081787 : Blo 2081435 2081787 := bstep (se 1 (by rfl) ⟨1561340, by rfl⟩ : syracuseStep 2081787 = 3122681) B3122681
theorem B4220389 : Blo 2081435 4220389 := bbase (se 4 (by rfl) ⟨395661, by rfl⟩ : syracuseStep 4220389 = 791323) (by norm_num)
theorem B22508741 : Blo 2081435 22508741 := bstep (se 4 (by rfl) ⟨2110194, by rfl⟩ : syracuseStep 22508741 = 4220389) B4220389
theorem B15005827 : Blo 2081435 15005827 := bstep (se 1 (by rfl) ⟨11254370, by rfl⟩ : syracuseStep 15005827 = 22508741) B22508741
theorem B80031077 : Blo 2081435 80031077 := bstep (se 4 (by rfl) ⟨7502913, by rfl⟩ : syracuseStep 80031077 = 15005827) B15005827
theorem B53354051 : Blo 2081435 53354051 := bstep (se 1 (by rfl) ⟨40015538, by rfl⟩ : syracuseStep 53354051 = 80031077) B80031077
theorem B35569367 : Blo 2081435 35569367 := bstep (se 1 (by rfl) ⟨26677025, by rfl⟩ : syracuseStep 35569367 = 53354051) B53354051
theorem B23712911 : Blo 2081435 23712911 := bstep (se 1 (by rfl) ⟨17784683, by rfl⟩ : syracuseStep 23712911 = 35569367) B35569367
theorem B15808607 : Blo 2081435 15808607 := bstep (se 1 (by rfl) ⟨11856455, by rfl⟩ : syracuseStep 15808607 = 23712911) B23712911
theorem B10539071 : Blo 2081435 10539071 := bstep (se 1 (by rfl) ⟨7904303, by rfl⟩ : syracuseStep 10539071 = 15808607) B15808607
theorem B7026047 : Blo 2081435 7026047 := bstep (se 1 (by rfl) ⟨5269535, by rfl⟩ : syracuseStep 7026047 = 10539071) B10539071
theorem B4684031 : Blo 2081435 4684031 := bstep (se 1 (by rfl) ⟨3513023, by rfl⟩ : syracuseStep 4684031 = 7026047) B7026047
theorem B3122687 : Blo 2081435 3122687 := bstep (se 1 (by rfl) ⟨2342015, by rfl⟩ : syracuseStep 3122687 = 4684031) B4684031
theorem B2081791 : Blo 2081435 2081791 := bstep (se 1 (by rfl) ⟨1561343, by rfl⟩ : syracuseStep 2081791 = 3122687) B3122687
theorem B3122693 : Blo 2081435 3122693 := bbase (se 4 (by rfl) ⟨292752, by rfl⟩ : syracuseStep 3122693 = 585505) (by norm_num)
theorem B2081795 : Blo 2081435 2081795 := bstep (se 1 (by rfl) ⟨1561346, by rfl⟩ : syracuseStep 2081795 = 3122693) B3122693
theorem B3513037 : Blo 2081435 3513037 := bbase (se 3 (by rfl) ⟨658694, by rfl⟩ : syracuseStep 3513037 = 1317389) (by norm_num)
theorem B4684049 : Blo 2081435 4684049 := bstep (se 2 (by rfl) ⟨1756518, by rfl⟩ : syracuseStep 4684049 = 3513037) B3513037
theorem B3122699 : Blo 2081435 3122699 := bstep (se 1 (by rfl) ⟨2342024, by rfl⟩ : syracuseStep 3122699 = 4684049) B4684049
theorem B2081799 : Blo 2081435 2081799 := bstep (se 1 (by rfl) ⟨1561349, by rfl⟩ : syracuseStep 2081799 = 3122699) B3122699
theorem B2342029 : Blo 2081435 2342029 := bbase (se 3 (by rfl) ⟨439130, by rfl⟩ : syracuseStep 2342029 = 878261) (by norm_num)
theorem B3122705 : Blo 2081435 3122705 := bstep (se 2 (by rfl) ⟨1171014, by rfl⟩ : syracuseStep 3122705 = 2342029) B2342029
theorem B2081803 : Blo 2081435 2081803 := bstep (se 1 (by rfl) ⟨1561352, by rfl⟩ : syracuseStep 2081803 = 3122705) B3122705
theorem B7026101 : Blo 2081435 7026101 := bbase (se 5 (by rfl) ⟨329348, by rfl⟩ : syracuseStep 7026101 = 658697) (by norm_num)
theorem B4684067 : Blo 2081435 4684067 := bstep (se 1 (by rfl) ⟨3513050, by rfl⟩ : syracuseStep 4684067 = 7026101) B7026101
theorem B3122711 : Blo 2081435 3122711 := bstep (se 1 (by rfl) ⟨2342033, by rfl⟩ : syracuseStep 3122711 = 4684067) B4684067
theorem B2081807 : Blo 2081435 2081807 := bstep (se 1 (by rfl) ⟨1561355, by rfl⟩ : syracuseStep 2081807 = 3122711) B3122711
theorem B3122717 : Blo 2081435 3122717 := bbase (se 3 (by rfl) ⟨585509, by rfl⟩ : syracuseStep 3122717 = 1171019) (by norm_num)
theorem B2081811 : Blo 2081435 2081811 := bstep (se 1 (by rfl) ⟨1561358, by rfl⟩ : syracuseStep 2081811 = 3122717) B3122717
theorem B4684085 : Blo 2081435 4684085 := bbase (se 5 (by rfl) ⟨219566, by rfl⟩ : syracuseStep 4684085 = 439133) (by norm_num)
theorem B3122723 : Blo 2081435 3122723 := bstep (se 1 (by rfl) ⟨2342042, by rfl⟩ : syracuseStep 3122723 = 4684085) B4684085
theorem B2081815 : Blo 2081435 2081815 := bstep (se 1 (by rfl) ⟨1561361, by rfl⟩ : syracuseStep 2081815 = 3122723) B3122723
theorem B5414381 : Blo 2081435 5414381 := bbase (se 3 (by rfl) ⟨1015196, by rfl⟩ : syracuseStep 5414381 = 2030393) (by norm_num)
theorem B3609587 : Blo 2081435 3609587 := bstep (se 1 (by rfl) ⟨2707190, by rfl⟩ : syracuseStep 3609587 = 5414381) B5414381
theorem B2406391 : Blo 2081435 2406391 := bstep (se 1 (by rfl) ⟨1804793, by rfl⟩ : syracuseStep 2406391 = 3609587) B3609587
theorem B51336341 : Blo 2081435 51336341 := bstep (se 6 (by rfl) ⟨1203195, by rfl⟩ : syracuseStep 51336341 = 2406391) B2406391
theorem B34224227 : Blo 2081435 34224227 := bstep (se 1 (by rfl) ⟨25668170, by rfl⟩ : syracuseStep 34224227 = 51336341) B51336341
theorem B22816151 : Blo 2081435 22816151 := bstep (se 1 (by rfl) ⟨17112113, by rfl⟩ : syracuseStep 22816151 = 34224227) B34224227
theorem B15210767 : Blo 2081435 15210767 := bstep (se 1 (by rfl) ⟨11408075, by rfl⟩ : syracuseStep 15210767 = 22816151) B22816151
theorem B40562045 : Blo 2081435 40562045 := bstep (se 3 (by rfl) ⟨7605383, by rfl⟩ : syracuseStep 40562045 = 15210767) B15210767
theorem B27041363 : Blo 2081435 27041363 := bstep (se 1 (by rfl) ⟨20281022, by rfl⟩ : syracuseStep 27041363 = 40562045) B40562045
theorem B18027575 : Blo 2081435 18027575 := bstep (se 1 (by rfl) ⟨13520681, by rfl⟩ : syracuseStep 18027575 = 27041363) B27041363
theorem B12018383 : Blo 2081435 12018383 := bstep (se 1 (by rfl) ⟨9013787, by rfl⟩ : syracuseStep 12018383 = 18027575) B18027575
theorem B8012255 : Blo 2081435 8012255 := bstep (se 1 (by rfl) ⟨6009191, by rfl⟩ : syracuseStep 8012255 = 12018383) B12018383
theorem B21366013 : Blo 2081435 21366013 := bstep (se 3 (by rfl) ⟨4006127, by rfl⟩ : syracuseStep 21366013 = 8012255) B8012255
theorem B28488017 : Blo 2081435 28488017 := bstep (se 2 (by rfl) ⟨10683006, by rfl⟩ : syracuseStep 28488017 = 21366013) B21366013
theorem B18992011 : Blo 2081435 18992011 := bstep (se 1 (by rfl) ⟨14244008, by rfl⟩ : syracuseStep 18992011 = 28488017) B28488017
theorem B25322681 : Blo 2081435 25322681 := bstep (se 2 (by rfl) ⟨9496005, by rfl⟩ : syracuseStep 25322681 = 18992011) B18992011
theorem B16881787 : Blo 2081435 16881787 := bstep (se 1 (by rfl) ⟨12661340, by rfl⟩ : syracuseStep 16881787 = 25322681) B25322681
theorem B22509049 : Blo 2081435 22509049 := bstep (se 2 (by rfl) ⟨8440893, by rfl⟩ : syracuseStep 22509049 = 16881787) B16881787
theorem B30012065 : Blo 2081435 30012065 := bstep (se 2 (by rfl) ⟨11254524, by rfl⟩ : syracuseStep 30012065 = 22509049) B22509049
theorem B20008043 : Blo 2081435 20008043 := bstep (se 1 (by rfl) ⟨15006032, by rfl⟩ : syracuseStep 20008043 = 30012065) B30012065
theorem B13338695 : Blo 2081435 13338695 := bstep (se 1 (by rfl) ⟨10004021, by rfl⟩ : syracuseStep 13338695 = 20008043) B20008043
theorem B8892463 : Blo 2081435 8892463 := bstep (se 1 (by rfl) ⟨6669347, by rfl⟩ : syracuseStep 8892463 = 13338695) B13338695
theorem B11856617 : Blo 2081435 11856617 := bstep (se 2 (by rfl) ⟨4446231, by rfl⟩ : syracuseStep 11856617 = 8892463) B8892463
theorem B7904411 : Blo 2081435 7904411 := bstep (se 1 (by rfl) ⟨5928308, by rfl⟩ : syracuseStep 7904411 = 11856617) B11856617
theorem B5269607 : Blo 2081435 5269607 := bstep (se 1 (by rfl) ⟨3952205, by rfl⟩ : syracuseStep 5269607 = 7904411) B7904411
theorem B3513071 : Blo 2081435 3513071 := bstep (se 1 (by rfl) ⟨2634803, by rfl⟩ : syracuseStep 3513071 = 5269607) B5269607
theorem B2342047 : Blo 2081435 2342047 := bstep (se 1 (by rfl) ⟨1756535, by rfl⟩ : syracuseStep 2342047 = 3513071) B3513071
theorem B3122729 : Blo 2081435 3122729 := bstep (se 2 (by rfl) ⟨1171023, by rfl⟩ : syracuseStep 3122729 = 2342047) B2342047
theorem B2081819 : Blo 2081435 2081819 := bstep (se 1 (by rfl) ⟨1561364, by rfl⟩ : syracuseStep 2081819 = 3122729) B3122729
theorem B2535133 : Blo 2081435 2535133 := bbase (se 3 (by rfl) ⟨475337, by rfl⟩ : syracuseStep 2535133 = 950675) (by norm_num)
theorem B3380177 : Blo 2081435 3380177 := bstep (se 2 (by rfl) ⟨1267566, by rfl⟩ : syracuseStep 3380177 = 2535133) B2535133
theorem B9013805 : Blo 2081435 9013805 := bstep (se 3 (by rfl) ⟨1690088, by rfl⟩ : syracuseStep 9013805 = 3380177) B3380177
theorem B6009203 : Blo 2081435 6009203 := bstep (se 1 (by rfl) ⟨4506902, by rfl⟩ : syracuseStep 6009203 = 9013805) B9013805
theorem B4006135 : Blo 2081435 4006135 := bstep (se 1 (by rfl) ⟨3004601, by rfl⟩ : syracuseStep 4006135 = 6009203) B6009203
theorem B5341513 : Blo 2081435 5341513 := bstep (se 2 (by rfl) ⟨2003067, by rfl⟩ : syracuseStep 5341513 = 4006135) B4006135
theorem B7122017 : Blo 2081435 7122017 := bstep (se 2 (by rfl) ⟨2670756, by rfl⟩ : syracuseStep 7122017 = 5341513) B5341513
theorem B18992045 : Blo 2081435 18992045 := bstep (se 3 (by rfl) ⟨3561008, by rfl⟩ : syracuseStep 18992045 = 7122017) B7122017
theorem B12661363 : Blo 2081435 12661363 := bstep (se 1 (by rfl) ⟨9496022, by rfl⟩ : syracuseStep 12661363 = 18992045) B18992045
theorem B67527269 : Blo 2081435 67527269 := bstep (se 4 (by rfl) ⟨6330681, by rfl⟩ : syracuseStep 67527269 = 12661363) B12661363
theorem B45018179 : Blo 2081435 45018179 := bstep (se 1 (by rfl) ⟨33763634, by rfl⟩ : syracuseStep 45018179 = 67527269) B67527269
theorem B30012119 : Blo 2081435 30012119 := bstep (se 1 (by rfl) ⟨22509089, by rfl⟩ : syracuseStep 30012119 = 45018179) B45018179
theorem B20008079 : Blo 2081435 20008079 := bstep (se 1 (by rfl) ⟨15006059, by rfl⟩ : syracuseStep 20008079 = 30012119) B30012119
theorem B13338719 : Blo 2081435 13338719 := bstep (se 1 (by rfl) ⟨10004039, by rfl⟩ : syracuseStep 13338719 = 20008079) B20008079
theorem B8892479 : Blo 2081435 8892479 := bstep (se 1 (by rfl) ⟨6669359, by rfl⟩ : syracuseStep 8892479 = 13338719) B13338719
theorem B5928319 : Blo 2081435 5928319 := bstep (se 1 (by rfl) ⟨4446239, by rfl⟩ : syracuseStep 5928319 = 8892479) B8892479
theorem B7904425 : Blo 2081435 7904425 := bstep (se 2 (by rfl) ⟨2964159, by rfl⟩ : syracuseStep 7904425 = 5928319) B5928319
theorem B10539233 : Blo 2081435 10539233 := bstep (se 2 (by rfl) ⟨3952212, by rfl⟩ : syracuseStep 10539233 = 7904425) B7904425
theorem B7026155 : Blo 2081435 7026155 := bstep (se 1 (by rfl) ⟨5269616, by rfl⟩ : syracuseStep 7026155 = 10539233) B10539233
theorem B4684103 : Blo 2081435 4684103 := bstep (se 1 (by rfl) ⟨3513077, by rfl⟩ : syracuseStep 4684103 = 7026155) B7026155
theorem B3122735 : Blo 2081435 3122735 := bstep (se 1 (by rfl) ⟨2342051, by rfl⟩ : syracuseStep 3122735 = 4684103) B4684103
theorem B2081823 : Blo 2081435 2081823 := bstep (se 1 (by rfl) ⟨1561367, by rfl⟩ : syracuseStep 2081823 = 3122735) B3122735
theorem B3122741 : Blo 2081435 3122741 := bbase (se 5 (by rfl) ⟨146378, by rfl⟩ : syracuseStep 3122741 = 292757) (by norm_num)
theorem B2081827 : Blo 2081435 2081827 := bstep (se 1 (by rfl) ⟨1561370, by rfl⟩ : syracuseStep 2081827 = 3122741) B3122741
theorem B5269637 : Blo 2081435 5269637 := bbase (se 4 (by rfl) ⟨494028, by rfl⟩ : syracuseStep 5269637 = 988057) (by norm_num)
theorem B3513091 : Blo 2081435 3513091 := bstep (se 1 (by rfl) ⟨2634818, by rfl⟩ : syracuseStep 3513091 = 5269637) B5269637
theorem B4684121 : Blo 2081435 4684121 := bstep (se 2 (by rfl) ⟨1756545, by rfl⟩ : syracuseStep 4684121 = 3513091) B3513091
theorem B3122747 : Blo 2081435 3122747 := bstep (se 1 (by rfl) ⟨2342060, by rfl⟩ : syracuseStep 3122747 = 4684121) B4684121
theorem B2081831 : Blo 2081435 2081831 := bstep (se 1 (by rfl) ⟨1561373, by rfl⟩ : syracuseStep 2081831 = 3122747) B3122747
theorem B2342065 : Blo 2081435 2342065 := bbase (se 2 (by rfl) ⟨878274, by rfl⟩ : syracuseStep 2342065 = 1756549) (by norm_num)
theorem B3122753 : Blo 2081435 3122753 := bstep (se 2 (by rfl) ⟨1171032, by rfl⟩ : syracuseStep 3122753 = 2342065) B2342065
theorem B2081835 : Blo 2081435 2081835 := bstep (se 1 (by rfl) ⟨1561376, by rfl⟩ : syracuseStep 2081835 = 3122753) B3122753
theorem B2223137 : Blo 2081435 2223137 := bbase (se 2 (by rfl) ⟨833676, by rfl⟩ : syracuseStep 2223137 = 1667353) (by norm_num)
theorem B5928365 : Blo 2081435 5928365 := bstep (se 3 (by rfl) ⟨1111568, by rfl⟩ : syracuseStep 5928365 = 2223137) B2223137
theorem B3952243 : Blo 2081435 3952243 := bstep (se 1 (by rfl) ⟨2964182, by rfl⟩ : syracuseStep 3952243 = 5928365) B5928365
theorem B5269657 : Blo 2081435 5269657 := bstep (se 2 (by rfl) ⟨1976121, by rfl⟩ : syracuseStep 5269657 = 3952243) B3952243
theorem B7026209 : Blo 2081435 7026209 := bstep (se 2 (by rfl) ⟨2634828, by rfl⟩ : syracuseStep 7026209 = 5269657) B5269657
theorem B4684139 : Blo 2081435 4684139 := bstep (se 1 (by rfl) ⟨3513104, by rfl⟩ : syracuseStep 4684139 = 7026209) B7026209
theorem B3122759 : Blo 2081435 3122759 := bstep (se 1 (by rfl) ⟨2342069, by rfl⟩ : syracuseStep 3122759 = 4684139) B4684139
theorem B2081839 : Blo 2081435 2081839 := bstep (se 1 (by rfl) ⟨1561379, by rfl⟩ : syracuseStep 2081839 = 3122759) B3122759
theorem B3122765 : Blo 2081435 3122765 := bbase (se 3 (by rfl) ⟨585518, by rfl⟩ : syracuseStep 3122765 = 1171037) (by norm_num)
theorem B2081843 : Blo 2081435 2081843 := bstep (se 1 (by rfl) ⟨1561382, by rfl⟩ : syracuseStep 2081843 = 3122765) B3122765
theorem B4684157 : Blo 2081435 4684157 := bbase (se 3 (by rfl) ⟨878279, by rfl⟩ : syracuseStep 4684157 = 1756559) (by norm_num)
theorem B3122771 : Blo 2081435 3122771 := bstep (se 1 (by rfl) ⟨2342078, by rfl⟩ : syracuseStep 3122771 = 4684157) B4684157
theorem B2081847 : Blo 2081435 2081847 := bstep (se 1 (by rfl) ⟨1561385, by rfl⟩ : syracuseStep 2081847 = 3122771) B3122771
theorem B3513125 : Blo 2081435 3513125 := bbase (se 4 (by rfl) ⟨329355, by rfl⟩ : syracuseStep 3513125 = 658711) (by norm_num)
theorem B2342083 : Blo 2081435 2342083 := bstep (se 1 (by rfl) ⟨1756562, by rfl⟩ : syracuseStep 2342083 = 3513125) B3513125
theorem B3122777 : Blo 2081435 3122777 := bstep (se 2 (by rfl) ⟨1171041, by rfl⟩ : syracuseStep 3122777 = 2342083) B2342083
theorem B2081851 : Blo 2081435 2081851 := bstep (se 1 (by rfl) ⟨1561388, by rfl⟩ : syracuseStep 2081851 = 3122777) B3122777
theorem B2964205 : Blo 2081435 2964205 := bbase (se 3 (by rfl) ⟨555788, by rfl⟩ : syracuseStep 2964205 = 1111577) (by norm_num)
theorem B15809093 : Blo 2081435 15809093 := bstep (se 4 (by rfl) ⟨1482102, by rfl⟩ : syracuseStep 15809093 = 2964205) B2964205
theorem B10539395 : Blo 2081435 10539395 := bstep (se 1 (by rfl) ⟨7904546, by rfl⟩ : syracuseStep 10539395 = 15809093) B15809093
theorem B7026263 : Blo 2081435 7026263 := bstep (se 1 (by rfl) ⟨5269697, by rfl⟩ : syracuseStep 7026263 = 10539395) B10539395
theorem B4684175 : Blo 2081435 4684175 := bstep (se 1 (by rfl) ⟨3513131, by rfl⟩ : syracuseStep 4684175 = 7026263) B7026263
theorem B3122783 : Blo 2081435 3122783 := bstep (se 1 (by rfl) ⟨2342087, by rfl⟩ : syracuseStep 3122783 = 4684175) B4684175
theorem B2081855 : Blo 2081435 2081855 := bstep (se 1 (by rfl) ⟨1561391, by rfl⟩ : syracuseStep 2081855 = 3122783) B3122783
theorem B3122789 : Blo 2081435 3122789 := bbase (se 4 (by rfl) ⟨292761, by rfl⟩ : syracuseStep 3122789 = 585523) (by norm_num)
theorem B2081859 : Blo 2081435 2081859 := bstep (se 1 (by rfl) ⟨1561394, by rfl⟩ : syracuseStep 2081859 = 3122789) B3122789
theorem B3751589 : Blo 2081435 3751589 := bbase (se 4 (by rfl) ⟨351711, by rfl⟩ : syracuseStep 3751589 = 703423) (by norm_num)
theorem B2501059 : Blo 2081435 2501059 := bstep (se 1 (by rfl) ⟨1875794, by rfl⟩ : syracuseStep 2501059 = 3751589) B3751589
theorem B3334745 : Blo 2081435 3334745 := bstep (se 2 (by rfl) ⟨1250529, by rfl⟩ : syracuseStep 3334745 = 2501059) B2501059
theorem B2223163 : Blo 2081435 2223163 := bstep (se 1 (by rfl) ⟨1667372, by rfl⟩ : syracuseStep 2223163 = 3334745) B3334745
theorem B2964217 : Blo 2081435 2964217 := bstep (se 2 (by rfl) ⟨1111581, by rfl⟩ : syracuseStep 2964217 = 2223163) B2223163
theorem B3952289 : Blo 2081435 3952289 := bstep (se 2 (by rfl) ⟨1482108, by rfl⟩ : syracuseStep 3952289 = 2964217) B2964217
theorem B2634859 : Blo 2081435 2634859 := bstep (se 1 (by rfl) ⟨1976144, by rfl⟩ : syracuseStep 2634859 = 3952289) B3952289
theorem B3513145 : Blo 2081435 3513145 := bstep (se 2 (by rfl) ⟨1317429, by rfl⟩ : syracuseStep 3513145 = 2634859) B2634859
theorem B4684193 : Blo 2081435 4684193 := bstep (se 2 (by rfl) ⟨1756572, by rfl⟩ : syracuseStep 4684193 = 3513145) B3513145
theorem B3122795 : Blo 2081435 3122795 := bstep (se 1 (by rfl) ⟨2342096, by rfl⟩ : syracuseStep 3122795 = 4684193) B4684193
theorem B2081863 : Blo 2081435 2081863 := bstep (se 1 (by rfl) ⟨1561397, by rfl⟩ : syracuseStep 2081863 = 3122795) B3122795
theorem B2342101 : Blo 2081435 2342101 := bbase (se 7 (by rfl) ⟨27446, by rfl⟩ : syracuseStep 2342101 = 54893) (by norm_num)
theorem B3122801 : Blo 2081435 3122801 := bstep (se 2 (by rfl) ⟨1171050, by rfl⟩ : syracuseStep 3122801 = 2342101) B2342101
theorem B2081867 : Blo 2081435 2081867 := bstep (se 1 (by rfl) ⟨1561400, by rfl⟩ : syracuseStep 2081867 = 3122801) B3122801
theorem B2634869 : Blo 2081435 2634869 := bbase (se 5 (by rfl) ⟨123509, by rfl⟩ : syracuseStep 2634869 = 247019) (by norm_num)
theorem B7026317 : Blo 2081435 7026317 := bstep (se 3 (by rfl) ⟨1317434, by rfl⟩ : syracuseStep 7026317 = 2634869) B2634869
theorem B4684211 : Blo 2081435 4684211 := bstep (se 1 (by rfl) ⟨3513158, by rfl⟩ : syracuseStep 4684211 = 7026317) B7026317
theorem B3122807 : Blo 2081435 3122807 := bstep (se 1 (by rfl) ⟨2342105, by rfl⟩ : syracuseStep 3122807 = 4684211) B4684211
theorem B2081871 : Blo 2081435 2081871 := bstep (se 1 (by rfl) ⟨1561403, by rfl⟩ : syracuseStep 2081871 = 3122807) B3122807
theorem B3122813 : Blo 2081435 3122813 := bbase (se 3 (by rfl) ⟨585527, by rfl⟩ : syracuseStep 3122813 = 1171055) (by norm_num)
theorem B2081875 : Blo 2081435 2081875 := bstep (se 1 (by rfl) ⟨1561406, by rfl⟩ : syracuseStep 2081875 = 3122813) B3122813
theorem B4684229 : Blo 2081435 4684229 := bbase (se 4 (by rfl) ⟨439146, by rfl⟩ : syracuseStep 4684229 = 878293) (by norm_num)
theorem B3122819 : Blo 2081435 3122819 := bstep (se 1 (by rfl) ⟨2342114, by rfl⟩ : syracuseStep 3122819 = 4684229) B4684229
theorem B2081879 : Blo 2081435 2081879 := bstep (se 1 (by rfl) ⟨1561409, by rfl⟩ : syracuseStep 2081879 = 3122819) B3122819
theorem B5002165 : Blo 2081435 5002165 := bbase (se 5 (by rfl) ⟨234476, by rfl⟩ : syracuseStep 5002165 = 468953) (by norm_num)
theorem B6669553 : Blo 2081435 6669553 := bstep (se 2 (by rfl) ⟨2501082, by rfl⟩ : syracuseStep 6669553 = 5002165) B5002165
theorem B8892737 : Blo 2081435 8892737 := bstep (se 2 (by rfl) ⟨3334776, by rfl⟩ : syracuseStep 8892737 = 6669553) B6669553
theorem B5928491 : Blo 2081435 5928491 := bstep (se 1 (by rfl) ⟨4446368, by rfl⟩ : syracuseStep 5928491 = 8892737) B8892737
theorem B3952327 : Blo 2081435 3952327 := bstep (se 1 (by rfl) ⟨2964245, by rfl⟩ : syracuseStep 3952327 = 5928491) B5928491
theorem B5269769 : Blo 2081435 5269769 := bstep (se 2 (by rfl) ⟨1976163, by rfl⟩ : syracuseStep 5269769 = 3952327) B3952327
theorem B3513179 : Blo 2081435 3513179 := bstep (se 1 (by rfl) ⟨2634884, by rfl⟩ : syracuseStep 3513179 = 5269769) B5269769
theorem B2342119 : Blo 2081435 2342119 := bstep (se 1 (by rfl) ⟨1756589, by rfl⟩ : syracuseStep 2342119 = 3513179) B3513179
theorem B3122825 : Blo 2081435 3122825 := bstep (se 2 (by rfl) ⟨1171059, by rfl⟩ : syracuseStep 3122825 = 2342119) B2342119
theorem B2081883 : Blo 2081435 2081883 := bstep (se 1 (by rfl) ⟨1561412, by rfl⟩ : syracuseStep 2081883 = 3122825) B3122825
theorem B10539557 : Blo 2081435 10539557 := bbase (se 4 (by rfl) ⟨988083, by rfl⟩ : syracuseStep 10539557 = 1976167) (by norm_num)
theorem B7026371 : Blo 2081435 7026371 := bstep (se 1 (by rfl) ⟨5269778, by rfl⟩ : syracuseStep 7026371 = 10539557) B10539557
theorem B4684247 : Blo 2081435 4684247 := bstep (se 1 (by rfl) ⟨3513185, by rfl⟩ : syracuseStep 4684247 = 7026371) B7026371
theorem B3122831 : Blo 2081435 3122831 := bstep (se 1 (by rfl) ⟨2342123, by rfl⟩ : syracuseStep 3122831 = 4684247) B4684247
theorem B2081887 : Blo 2081435 2081887 := bstep (se 1 (by rfl) ⟨1561415, by rfl⟩ : syracuseStep 2081887 = 3122831) B3122831
theorem B3122837 : Blo 2081435 3122837 := bbase (se 6 (by rfl) ⟨73191, by rfl⟩ : syracuseStep 3122837 = 146383) (by norm_num)
theorem B2081891 : Blo 2081435 2081891 := bstep (se 1 (by rfl) ⟨1561418, by rfl⟩ : syracuseStep 2081891 = 3122837) B3122837
theorem B3751645 : Blo 2081435 3751645 := bbase (se 3 (by rfl) ⟨703433, by rfl⟩ : syracuseStep 3751645 = 1406867) (by norm_num)
theorem B5002193 : Blo 2081435 5002193 := bstep (se 2 (by rfl) ⟨1875822, by rfl⟩ : syracuseStep 5002193 = 3751645) B3751645
theorem B13339181 : Blo 2081435 13339181 := bstep (se 3 (by rfl) ⟨2501096, by rfl⟩ : syracuseStep 13339181 = 5002193) B5002193
theorem B8892787 : Blo 2081435 8892787 := bstep (se 1 (by rfl) ⟨6669590, by rfl⟩ : syracuseStep 8892787 = 13339181) B13339181
theorem B11857049 : Blo 2081435 11857049 := bstep (se 2 (by rfl) ⟨4446393, by rfl⟩ : syracuseStep 11857049 = 8892787) B8892787
theorem B7904699 : Blo 2081435 7904699 := bstep (se 1 (by rfl) ⟨5928524, by rfl⟩ : syracuseStep 7904699 = 11857049) B11857049
theorem B5269799 : Blo 2081435 5269799 := bstep (se 1 (by rfl) ⟨3952349, by rfl⟩ : syracuseStep 5269799 = 7904699) B7904699
theorem B3513199 : Blo 2081435 3513199 := bstep (se 1 (by rfl) ⟨2634899, by rfl⟩ : syracuseStep 3513199 = 5269799) B5269799
theorem B4684265 : Blo 2081435 4684265 := bstep (se 2 (by rfl) ⟨1756599, by rfl⟩ : syracuseStep 4684265 = 3513199) B3513199
theorem B3122843 : Blo 2081435 3122843 := bstep (se 1 (by rfl) ⟨2342132, by rfl⟩ : syracuseStep 3122843 = 4684265) B4684265
theorem B2081895 : Blo 2081435 2081895 := bstep (se 1 (by rfl) ⟨1561421, by rfl⟩ : syracuseStep 2081895 = 3122843) B3122843
theorem B2342137 : Blo 2081435 2342137 := bbase (se 2 (by rfl) ⟨878301, by rfl⟩ : syracuseStep 2342137 = 1756603) (by norm_num)
theorem B3122849 : Blo 2081435 3122849 := bstep (se 2 (by rfl) ⟨1171068, by rfl⟩ : syracuseStep 3122849 = 2342137) B2342137
theorem B2081899 : Blo 2081435 2081899 := bstep (se 1 (by rfl) ⟨1561424, by rfl⟩ : syracuseStep 2081899 = 3122849) B3122849
theorem B8892821 : Blo 2081435 8892821 := bbase (se 6 (by rfl) ⟨208425, by rfl⟩ : syracuseStep 8892821 = 416851) (by norm_num)
theorem B5928547 : Blo 2081435 5928547 := bstep (se 1 (by rfl) ⟨4446410, by rfl⟩ : syracuseStep 5928547 = 8892821) B8892821
theorem B7904729 : Blo 2081435 7904729 := bstep (se 2 (by rfl) ⟨2964273, by rfl⟩ : syracuseStep 7904729 = 5928547) B5928547
theorem B5269819 : Blo 2081435 5269819 := bstep (se 1 (by rfl) ⟨3952364, by rfl⟩ : syracuseStep 5269819 = 7904729) B7904729
theorem B7026425 : Blo 2081435 7026425 := bstep (se 2 (by rfl) ⟨2634909, by rfl⟩ : syracuseStep 7026425 = 5269819) B5269819
theorem B4684283 : Blo 2081435 4684283 := bstep (se 1 (by rfl) ⟨3513212, by rfl⟩ : syracuseStep 4684283 = 7026425) B7026425
theorem B3122855 : Blo 2081435 3122855 := bstep (se 1 (by rfl) ⟨2342141, by rfl⟩ : syracuseStep 3122855 = 4684283) B4684283
theorem B2081903 : Blo 2081435 2081903 := bstep (se 1 (by rfl) ⟨1561427, by rfl⟩ : syracuseStep 2081903 = 3122855) B3122855
theorem B3122861 : Blo 2081435 3122861 := bbase (se 3 (by rfl) ⟨585536, by rfl⟩ : syracuseStep 3122861 = 1171073) (by norm_num)
theorem B2081907 : Blo 2081435 2081907 := bstep (se 1 (by rfl) ⟨1561430, by rfl⟩ : syracuseStep 2081907 = 3122861) B3122861
theorem B4684301 : Blo 2081435 4684301 := bbase (se 3 (by rfl) ⟨878306, by rfl⟩ : syracuseStep 4684301 = 1756613) (by norm_num)
theorem B3122867 : Blo 2081435 3122867 := bstep (se 1 (by rfl) ⟨2342150, by rfl⟩ : syracuseStep 3122867 = 4684301) B4684301
theorem B2081911 : Blo 2081435 2081911 := bstep (se 1 (by rfl) ⟨1561433, by rfl⟩ : syracuseStep 2081911 = 3122867) B3122867
theorem B2634925 : Blo 2081435 2634925 := bbase (se 3 (by rfl) ⟨494048, by rfl⟩ : syracuseStep 2634925 = 988097) (by norm_num)
theorem B3513233 : Blo 2081435 3513233 := bstep (se 2 (by rfl) ⟨1317462, by rfl⟩ : syracuseStep 3513233 = 2634925) B2634925
theorem B2342155 : Blo 2081435 2342155 := bstep (se 1 (by rfl) ⟨1756616, by rfl⟩ : syracuseStep 2342155 = 3513233) B3513233
theorem B3122873 : Blo 2081435 3122873 := bstep (se 2 (by rfl) ⟨1171077, by rfl⟩ : syracuseStep 3122873 = 2342155) B2342155
theorem B2081915 : Blo 2081435 2081915 := bstep (se 1 (by rfl) ⟨1561436, by rfl⟩ : syracuseStep 2081915 = 3122873) B3122873
theorem B2501125 : Blo 2081435 2501125 := bbase (se 4 (by rfl) ⟨234480, by rfl⟩ : syracuseStep 2501125 = 468961) (by norm_num)
theorem B13339333 : Blo 2081435 13339333 := bstep (se 4 (by rfl) ⟨1250562, by rfl⟩ : syracuseStep 13339333 = 2501125) B2501125
theorem B17785777 : Blo 2081435 17785777 := bstep (se 2 (by rfl) ⟨6669666, by rfl⟩ : syracuseStep 17785777 = 13339333) B13339333
theorem B23714369 : Blo 2081435 23714369 := bstep (se 2 (by rfl) ⟨8892888, by rfl⟩ : syracuseStep 23714369 = 17785777) B17785777
theorem B15809579 : Blo 2081435 15809579 := bstep (se 1 (by rfl) ⟨11857184, by rfl⟩ : syracuseStep 15809579 = 23714369) B23714369
theorem B10539719 : Blo 2081435 10539719 := bstep (se 1 (by rfl) ⟨7904789, by rfl⟩ : syracuseStep 10539719 = 15809579) B15809579
theorem B7026479 : Blo 2081435 7026479 := bstep (se 1 (by rfl) ⟨5269859, by rfl⟩ : syracuseStep 7026479 = 10539719) B10539719
theorem B4684319 : Blo 2081435 4684319 := bstep (se 1 (by rfl) ⟨3513239, by rfl⟩ : syracuseStep 4684319 = 7026479) B7026479
theorem B3122879 : Blo 2081435 3122879 := bstep (se 1 (by rfl) ⟨2342159, by rfl⟩ : syracuseStep 3122879 = 4684319) B4684319
theorem B2081919 : Blo 2081435 2081919 := bstep (se 1 (by rfl) ⟨1561439, by rfl⟩ : syracuseStep 2081919 = 3122879) B3122879
theorem B3122885 : Blo 2081435 3122885 := bbase (se 4 (by rfl) ⟨292770, by rfl⟩ : syracuseStep 3122885 = 585541) (by norm_num)
theorem B2081923 : Blo 2081435 2081923 := bstep (se 1 (by rfl) ⟨1561442, by rfl⟩ : syracuseStep 2081923 = 3122885) B3122885
theorem B3513253 : Blo 2081435 3513253 := bbase (se 4 (by rfl) ⟨329367, by rfl⟩ : syracuseStep 3513253 = 658735) (by norm_num)
theorem B4684337 : Blo 2081435 4684337 := bstep (se 2 (by rfl) ⟨1756626, by rfl⟩ : syracuseStep 4684337 = 3513253) B3513253
theorem B3122891 : Blo 2081435 3122891 := bstep (se 1 (by rfl) ⟨2342168, by rfl⟩ : syracuseStep 3122891 = 4684337) B4684337
theorem B2081927 : Blo 2081435 2081927 := bstep (se 1 (by rfl) ⟨1561445, by rfl⟩ : syracuseStep 2081927 = 3122891) B3122891
theorem B2342173 : Blo 2081435 2342173 := bbase (se 3 (by rfl) ⟨439157, by rfl⟩ : syracuseStep 2342173 = 878315) (by norm_num)
theorem B3122897 : Blo 2081435 3122897 := bstep (se 2 (by rfl) ⟨1171086, by rfl⟩ : syracuseStep 3122897 = 2342173) B2342173
theorem B2081931 : Blo 2081435 2081931 := bstep (se 1 (by rfl) ⟨1561448, by rfl⟩ : syracuseStep 2081931 = 3122897) B3122897
theorem B7026533 : Blo 2081435 7026533 := bbase (se 4 (by rfl) ⟨658737, by rfl⟩ : syracuseStep 7026533 = 1317475) (by norm_num)
theorem B4684355 : Blo 2081435 4684355 := bstep (se 1 (by rfl) ⟨3513266, by rfl⟩ : syracuseStep 4684355 = 7026533) B7026533
theorem B3122903 : Blo 2081435 3122903 := bstep (se 1 (by rfl) ⟨2342177, by rfl⟩ : syracuseStep 3122903 = 4684355) B4684355
theorem B2081935 : Blo 2081435 2081935 := bstep (se 1 (by rfl) ⟨1561451, by rfl⟩ : syracuseStep 2081935 = 3122903) B3122903
theorem B3122909 : Blo 2081435 3122909 := bbase (se 3 (by rfl) ⟨585545, by rfl⟩ : syracuseStep 3122909 = 1171091) (by norm_num)
theorem B2081939 : Blo 2081435 2081939 := bstep (se 1 (by rfl) ⟨1561454, by rfl⟩ : syracuseStep 2081939 = 3122909) B3122909
theorem B4684373 : Blo 2081435 4684373 := bbase (se 8 (by rfl) ⟨27447, by rfl⟩ : syracuseStep 4684373 = 54895) (by norm_num)
theorem B3122915 : Blo 2081435 3122915 := bstep (se 1 (by rfl) ⟨2342186, by rfl⟩ : syracuseStep 3122915 = 4684373) B4684373
theorem B2081943 : Blo 2081435 2081943 := bstep (se 1 (by rfl) ⟨1561457, by rfl⟩ : syracuseStep 2081943 = 3122915) B3122915
theorem B6331061 : Blo 2081435 6331061 := bbase (se 5 (by rfl) ⟨296768, by rfl⟩ : syracuseStep 6331061 = 593537) (by norm_num)
theorem B16882829 : Blo 2081435 16882829 := bstep (se 3 (by rfl) ⟨3165530, by rfl⟩ : syracuseStep 16882829 = 6331061) B6331061
theorem B11255219 : Blo 2081435 11255219 := bstep (se 1 (by rfl) ⟨8441414, by rfl⟩ : syracuseStep 11255219 = 16882829) B16882829
theorem B7503479 : Blo 2081435 7503479 := bstep (se 1 (by rfl) ⟨5627609, by rfl⟩ : syracuseStep 7503479 = 11255219) B11255219
theorem B5002319 : Blo 2081435 5002319 := bstep (se 1 (by rfl) ⟨3751739, by rfl⟩ : syracuseStep 5002319 = 7503479) B7503479
theorem B3334879 : Blo 2081435 3334879 := bstep (se 1 (by rfl) ⟨2501159, by rfl⟩ : syracuseStep 3334879 = 5002319) B5002319
theorem B4446505 : Blo 2081435 4446505 := bstep (se 2 (by rfl) ⟨1667439, by rfl⟩ : syracuseStep 4446505 = 3334879) B3334879
theorem B5928673 : Blo 2081435 5928673 := bstep (se 2 (by rfl) ⟨2223252, by rfl⟩ : syracuseStep 5928673 = 4446505) B4446505
theorem B7904897 : Blo 2081435 7904897 := bstep (se 2 (by rfl) ⟨2964336, by rfl⟩ : syracuseStep 7904897 = 5928673) B5928673
theorem B5269931 : Blo 2081435 5269931 := bstep (se 1 (by rfl) ⟨3952448, by rfl⟩ : syracuseStep 5269931 = 7904897) B7904897
theorem B3513287 : Blo 2081435 3513287 := bstep (se 1 (by rfl) ⟨2634965, by rfl⟩ : syracuseStep 3513287 = 5269931) B5269931
theorem B2342191 : Blo 2081435 2342191 := bstep (se 1 (by rfl) ⟨1756643, by rfl⟩ : syracuseStep 2342191 = 3513287) B3513287
theorem B3122921 : Blo 2081435 3122921 := bstep (se 2 (by rfl) ⟨1171095, by rfl⟩ : syracuseStep 3122921 = 2342191) B2342191
theorem B2081947 : Blo 2081435 2081947 := bstep (se 1 (by rfl) ⟨1561460, by rfl⟩ : syracuseStep 2081947 = 3122921) B3122921
theorem B2110357 : Blo 2081435 2110357 := bbase (se 6 (by rfl) ⟨49461, by rfl⟩ : syracuseStep 2110357 = 98923) (by norm_num)
theorem B11255237 : Blo 2081435 11255237 := bstep (se 4 (by rfl) ⟨1055178, by rfl⟩ : syracuseStep 11255237 = 2110357) B2110357
theorem B7503491 : Blo 2081435 7503491 := bstep (se 1 (by rfl) ⟨5627618, by rfl⟩ : syracuseStep 7503491 = 11255237) B11255237
theorem B5002327 : Blo 2081435 5002327 := bstep (se 1 (by rfl) ⟨3751745, by rfl⟩ : syracuseStep 5002327 = 7503491) B7503491
theorem B26679077 : Blo 2081435 26679077 := bstep (se 4 (by rfl) ⟨2501163, by rfl⟩ : syracuseStep 26679077 = 5002327) B5002327
theorem B17786051 : Blo 2081435 17786051 := bstep (se 1 (by rfl) ⟨13339538, by rfl⟩ : syracuseStep 17786051 = 26679077) B26679077
theorem B11857367 : Blo 2081435 11857367 := bstep (se 1 (by rfl) ⟨8893025, by rfl⟩ : syracuseStep 11857367 = 17786051) B17786051
theorem B7904911 : Blo 2081435 7904911 := bstep (se 1 (by rfl) ⟨5928683, by rfl⟩ : syracuseStep 7904911 = 11857367) B11857367
theorem B10539881 : Blo 2081435 10539881 := bstep (se 2 (by rfl) ⟨3952455, by rfl⟩ : syracuseStep 10539881 = 7904911) B7904911
theorem B7026587 : Blo 2081435 7026587 := bstep (se 1 (by rfl) ⟨5269940, by rfl⟩ : syracuseStep 7026587 = 10539881) B10539881
theorem B4684391 : Blo 2081435 4684391 := bstep (se 1 (by rfl) ⟨3513293, by rfl⟩ : syracuseStep 4684391 = 7026587) B7026587
theorem B3122927 : Blo 2081435 3122927 := bstep (se 1 (by rfl) ⟨2342195, by rfl⟩ : syracuseStep 3122927 = 4684391) B4684391
theorem B2081951 : Blo 2081435 2081951 := bstep (se 1 (by rfl) ⟨1561463, by rfl⟩ : syracuseStep 2081951 = 3122927) B3122927
theorem B3122933 : Blo 2081435 3122933 := bbase (se 5 (by rfl) ⟨146387, by rfl⟩ : syracuseStep 3122933 = 292775) (by norm_num)
theorem B2081955 : Blo 2081435 2081955 := bstep (se 1 (by rfl) ⟨1561466, by rfl⟩ : syracuseStep 2081955 = 3122933) B3122933
theorem B8893061 : Blo 2081435 8893061 := bbase (se 4 (by rfl) ⟨833724, by rfl⟩ : syracuseStep 8893061 = 1667449) (by norm_num)
theorem B5928707 : Blo 2081435 5928707 := bstep (se 1 (by rfl) ⟨4446530, by rfl⟩ : syracuseStep 5928707 = 8893061) B8893061
theorem B3952471 : Blo 2081435 3952471 := bstep (se 1 (by rfl) ⟨2964353, by rfl⟩ : syracuseStep 3952471 = 5928707) B5928707
theorem B5269961 : Blo 2081435 5269961 := bstep (se 2 (by rfl) ⟨1976235, by rfl⟩ : syracuseStep 5269961 = 3952471) B3952471
theorem B3513307 : Blo 2081435 3513307 := bstep (se 1 (by rfl) ⟨2634980, by rfl⟩ : syracuseStep 3513307 = 5269961) B5269961
theorem B4684409 : Blo 2081435 4684409 := bstep (se 2 (by rfl) ⟨1756653, by rfl⟩ : syracuseStep 4684409 = 3513307) B3513307
theorem B3122939 : Blo 2081435 3122939 := bstep (se 1 (by rfl) ⟨2342204, by rfl⟩ : syracuseStep 3122939 = 4684409) B4684409
theorem B2081959 : Blo 2081435 2081959 := bstep (se 1 (by rfl) ⟨1561469, by rfl⟩ : syracuseStep 2081959 = 3122939) B3122939
theorem B2342209 : Blo 2081435 2342209 := bbase (se 2 (by rfl) ⟨878328, by rfl⟩ : syracuseStep 2342209 = 1756657) (by norm_num)
theorem B3122945 : Blo 2081435 3122945 := bstep (se 2 (by rfl) ⟨1171104, by rfl⟩ : syracuseStep 3122945 = 2342209) B2342209
theorem B2081963 : Blo 2081435 2081963 := bstep (se 1 (by rfl) ⟨1561472, by rfl⟩ : syracuseStep 2081963 = 3122945) B3122945
theorem B5269981 : Blo 2081435 5269981 := bbase (se 3 (by rfl) ⟨988121, by rfl⟩ : syracuseStep 5269981 = 1976243) (by norm_num)
theorem B7026641 : Blo 2081435 7026641 := bstep (se 2 (by rfl) ⟨2634990, by rfl⟩ : syracuseStep 7026641 = 5269981) B5269981
theorem B4684427 : Blo 2081435 4684427 := bstep (se 1 (by rfl) ⟨3513320, by rfl⟩ : syracuseStep 4684427 = 7026641) B7026641
theorem B3122951 : Blo 2081435 3122951 := bstep (se 1 (by rfl) ⟨2342213, by rfl⟩ : syracuseStep 3122951 = 4684427) B4684427
theorem B2081967 : Blo 2081435 2081967 := bstep (se 1 (by rfl) ⟨1561475, by rfl⟩ : syracuseStep 2081967 = 3122951) B3122951
theorem B3122957 : Blo 2081435 3122957 := bbase (se 3 (by rfl) ⟨585554, by rfl⟩ : syracuseStep 3122957 = 1171109) (by norm_num)
theorem B2081971 : Blo 2081435 2081971 := bstep (se 1 (by rfl) ⟨1561478, by rfl⟩ : syracuseStep 2081971 = 3122957) B3122957
theorem B4684445 : Blo 2081435 4684445 := bbase (se 3 (by rfl) ⟨878333, by rfl⟩ : syracuseStep 4684445 = 1756667) (by norm_num)
theorem B3122963 : Blo 2081435 3122963 := bstep (se 1 (by rfl) ⟨2342222, by rfl⟩ : syracuseStep 3122963 = 4684445) B4684445
theorem B2081975 : Blo 2081435 2081975 := bstep (se 1 (by rfl) ⟨1561481, by rfl⟩ : syracuseStep 2081975 = 3122963) B3122963
theorem B3513341 : Blo 2081435 3513341 := bbase (se 3 (by rfl) ⟨658751, by rfl⟩ : syracuseStep 3513341 = 1317503) (by norm_num)
theorem B2342227 : Blo 2081435 2342227 := bstep (se 1 (by rfl) ⟨1756670, by rfl⟩ : syracuseStep 2342227 = 3513341) B3513341
theorem B3122969 : Blo 2081435 3122969 := bstep (se 2 (by rfl) ⟨1171113, by rfl⟩ : syracuseStep 3122969 = 2342227) B2342227
theorem B2081979 : Blo 2081435 2081979 := bstep (se 1 (by rfl) ⟨1561484, by rfl⟩ : syracuseStep 2081979 = 3122969) B3122969
theorem B4446581 : Blo 2081435 4446581 := bbase (se 5 (by rfl) ⟨208433, by rfl⟩ : syracuseStep 4446581 = 416867) (by norm_num)
theorem B11857549 : Blo 2081435 11857549 := bstep (se 3 (by rfl) ⟨2223290, by rfl⟩ : syracuseStep 11857549 = 4446581) B4446581
theorem B15810065 : Blo 2081435 15810065 := bstep (se 2 (by rfl) ⟨5928774, by rfl⟩ : syracuseStep 15810065 = 11857549) B11857549
theorem B10540043 : Blo 2081435 10540043 := bstep (se 1 (by rfl) ⟨7905032, by rfl⟩ : syracuseStep 10540043 = 15810065) B15810065
theorem B7026695 : Blo 2081435 7026695 := bstep (se 1 (by rfl) ⟨5270021, by rfl⟩ : syracuseStep 7026695 = 10540043) B10540043
theorem B4684463 : Blo 2081435 4684463 := bstep (se 1 (by rfl) ⟨3513347, by rfl⟩ : syracuseStep 4684463 = 7026695) B7026695
theorem B3122975 : Blo 2081435 3122975 := bstep (se 1 (by rfl) ⟨2342231, by rfl⟩ : syracuseStep 3122975 = 4684463) B4684463
theorem B2081983 : Blo 2081435 2081983 := bstep (se 1 (by rfl) ⟨1561487, by rfl⟩ : syracuseStep 2081983 = 3122975) B3122975
theorem B3122981 : Blo 2081435 3122981 := bbase (se 4 (by rfl) ⟨292779, by rfl⟩ : syracuseStep 3122981 = 585559) (by norm_num)
theorem B2081987 : Blo 2081435 2081987 := bstep (se 1 (by rfl) ⟨1561490, by rfl⟩ : syracuseStep 2081987 = 3122981) B3122981
theorem B2635021 : Blo 2081435 2635021 := bbase (se 3 (by rfl) ⟨494066, by rfl⟩ : syracuseStep 2635021 = 988133) (by norm_num)
theorem B3513361 : Blo 2081435 3513361 := bstep (se 2 (by rfl) ⟨1317510, by rfl⟩ : syracuseStep 3513361 = 2635021) B2635021
theorem B4684481 : Blo 2081435 4684481 := bstep (se 2 (by rfl) ⟨1756680, by rfl⟩ : syracuseStep 4684481 = 3513361) B3513361
theorem B3122987 : Blo 2081435 3122987 := bstep (se 1 (by rfl) ⟨2342240, by rfl⟩ : syracuseStep 3122987 = 4684481) B4684481
theorem B2081991 : Blo 2081435 2081991 := bstep (se 1 (by rfl) ⟨1561493, by rfl⟩ : syracuseStep 2081991 = 3122987) B3122987
theorem B2342245 : Blo 2081435 2342245 := bbase (se 4 (by rfl) ⟨219585, by rfl⟩ : syracuseStep 2342245 = 439171) (by norm_num)
theorem B3122993 : Blo 2081435 3122993 := bstep (se 2 (by rfl) ⟨1171122, by rfl⟩ : syracuseStep 3122993 = 2342245) B2342245
theorem B2081995 : Blo 2081435 2081995 := bstep (se 1 (by rfl) ⟨1561496, by rfl⟩ : syracuseStep 2081995 = 3122993) B3122993
theorem B5928821 : Blo 2081435 5928821 := bbase (se 5 (by rfl) ⟨277913, by rfl⟩ : syracuseStep 5928821 = 555827) (by norm_num)
theorem B3952547 : Blo 2081435 3952547 := bstep (se 1 (by rfl) ⟨2964410, by rfl⟩ : syracuseStep 3952547 = 5928821) B5928821
theorem B2635031 : Blo 2081435 2635031 := bstep (se 1 (by rfl) ⟨1976273, by rfl⟩ : syracuseStep 2635031 = 3952547) B3952547
theorem B7026749 : Blo 2081435 7026749 := bstep (se 3 (by rfl) ⟨1317515, by rfl⟩ : syracuseStep 7026749 = 2635031) B2635031
theorem B4684499 : Blo 2081435 4684499 := bstep (se 1 (by rfl) ⟨3513374, by rfl⟩ : syracuseStep 4684499 = 7026749) B7026749
theorem B3122999 : Blo 2081435 3122999 := bstep (se 1 (by rfl) ⟨2342249, by rfl⟩ : syracuseStep 3122999 = 4684499) B4684499
theorem B2081999 : Blo 2081435 2081999 := bstep (se 1 (by rfl) ⟨1561499, by rfl⟩ : syracuseStep 2081999 = 3122999) B3122999
theorem B3123005 : Blo 2081435 3123005 := bbase (se 3 (by rfl) ⟨585563, by rfl⟩ : syracuseStep 3123005 = 1171127) (by norm_num)
theorem B2082003 : Blo 2081435 2082003 := bstep (se 1 (by rfl) ⟨1561502, by rfl⟩ : syracuseStep 2082003 = 3123005) B3123005
theorem B4684517 : Blo 2081435 4684517 := bbase (se 4 (by rfl) ⟨439173, by rfl⟩ : syracuseStep 4684517 = 878347) (by norm_num)
theorem B3123011 : Blo 2081435 3123011 := bstep (se 1 (by rfl) ⟨2342258, by rfl⟩ : syracuseStep 3123011 = 4684517) B4684517
theorem B2082007 : Blo 2081435 2082007 := bstep (se 1 (by rfl) ⟨1561505, by rfl⟩ : syracuseStep 2082007 = 3123011) B3123011
theorem B5270093 : Blo 2081435 5270093 := bbase (se 3 (by rfl) ⟨988142, by rfl⟩ : syracuseStep 5270093 = 1976285) (by norm_num)
theorem B3513395 : Blo 2081435 3513395 := bstep (se 1 (by rfl) ⟨2635046, by rfl⟩ : syracuseStep 3513395 = 5270093) B5270093
theorem B2342263 : Blo 2081435 2342263 := bstep (se 1 (by rfl) ⟨1756697, by rfl⟩ : syracuseStep 2342263 = 3513395) B3513395
theorem B3123017 : Blo 2081435 3123017 := bstep (se 2 (by rfl) ⟨1171131, by rfl⟩ : syracuseStep 3123017 = 2342263) B2342263
theorem B2082011 : Blo 2081435 2082011 := bstep (se 1 (by rfl) ⟨1561508, by rfl⟩ : syracuseStep 2082011 = 3123017) B3123017
theorem B2223325 : Blo 2081435 2223325 := bbase (se 3 (by rfl) ⟨416873, by rfl⟩ : syracuseStep 2223325 = 833747) (by norm_num)
theorem B2964433 : Blo 2081435 2964433 := bstep (se 2 (by rfl) ⟨1111662, by rfl⟩ : syracuseStep 2964433 = 2223325) B2223325
theorem B3952577 : Blo 2081435 3952577 := bstep (se 2 (by rfl) ⟨1482216, by rfl⟩ : syracuseStep 3952577 = 2964433) B2964433
theorem B10540205 : Blo 2081435 10540205 := bstep (se 3 (by rfl) ⟨1976288, by rfl⟩ : syracuseStep 10540205 = 3952577) B3952577
theorem B7026803 : Blo 2081435 7026803 := bstep (se 1 (by rfl) ⟨5270102, by rfl⟩ : syracuseStep 7026803 = 10540205) B10540205
theorem B4684535 : Blo 2081435 4684535 := bstep (se 1 (by rfl) ⟨3513401, by rfl⟩ : syracuseStep 4684535 = 7026803) B7026803
theorem B3123023 : Blo 2081435 3123023 := bstep (se 1 (by rfl) ⟨2342267, by rfl⟩ : syracuseStep 3123023 = 4684535) B4684535
theorem B2082015 : Blo 2081435 2082015 := bstep (se 1 (by rfl) ⟨1561511, by rfl⟩ : syracuseStep 2082015 = 3123023) B3123023
theorem B3123029 : Blo 2081435 3123029 := bbase (se 9 (by rfl) ⟨9149, by rfl⟩ : syracuseStep 3123029 = 18299) (by norm_num)
theorem B2082019 : Blo 2081435 2082019 := bstep (se 1 (by rfl) ⟨1561514, by rfl⟩ : syracuseStep 2082019 = 3123029) B3123029
theorem B5002501 : Blo 2081435 5002501 := bbase (se 4 (by rfl) ⟨468984, by rfl⟩ : syracuseStep 5002501 = 937969) (by norm_num)
theorem B6670001 : Blo 2081435 6670001 := bstep (se 2 (by rfl) ⟨2501250, by rfl⟩ : syracuseStep 6670001 = 5002501) B5002501
theorem B4446667 : Blo 2081435 4446667 := bstep (se 1 (by rfl) ⟨3335000, by rfl⟩ : syracuseStep 4446667 = 6670001) B6670001
theorem B5928889 : Blo 2081435 5928889 := bstep (se 2 (by rfl) ⟨2223333, by rfl⟩ : syracuseStep 5928889 = 4446667) B4446667
theorem B7905185 : Blo 2081435 7905185 := bstep (se 2 (by rfl) ⟨2964444, by rfl⟩ : syracuseStep 7905185 = 5928889) B5928889
theorem B5270123 : Blo 2081435 5270123 := bstep (se 1 (by rfl) ⟨3952592, by rfl⟩ : syracuseStep 5270123 = 7905185) B7905185
theorem B3513415 : Blo 2081435 3513415 := bstep (se 1 (by rfl) ⟨2635061, by rfl⟩ : syracuseStep 3513415 = 5270123) B5270123
theorem B4684553 : Blo 2081435 4684553 := bstep (se 2 (by rfl) ⟨1756707, by rfl⟩ : syracuseStep 4684553 = 3513415) B3513415
theorem B3123035 : Blo 2081435 3123035 := bstep (se 1 (by rfl) ⟨2342276, by rfl⟩ : syracuseStep 3123035 = 4684553) B4684553
theorem B2082023 : Blo 2081435 2082023 := bstep (se 1 (by rfl) ⟨1561517, by rfl⟩ : syracuseStep 2082023 = 3123035) B3123035
theorem B2342281 : Blo 2081435 2342281 := bbase (se 2 (by rfl) ⟨878355, by rfl⟩ : syracuseStep 2342281 = 1756711) (by norm_num)
theorem B3123041 : Blo 2081435 3123041 := bstep (se 2 (by rfl) ⟨1171140, by rfl⟩ : syracuseStep 3123041 = 2342281) B2342281
theorem B2082027 : Blo 2081435 2082027 := bstep (se 1 (by rfl) ⟨1561520, by rfl⟩ : syracuseStep 2082027 = 3123041) B3123041
theorem B3004901 : Blo 2081435 3004901 := bbase (se 4 (by rfl) ⟨281709, by rfl⟩ : syracuseStep 3004901 = 563419) (by norm_num)
theorem B32052277 : Blo 2081435 32052277 := bstep (se 5 (by rfl) ⟨1502450, by rfl⟩ : syracuseStep 32052277 = 3004901) B3004901
theorem B42736369 : Blo 2081435 42736369 := bstep (se 2 (by rfl) ⟨16026138, by rfl⟩ : syracuseStep 42736369 = 32052277) B32052277
theorem B56981825 : Blo 2081435 56981825 := bstep (se 2 (by rfl) ⟨21368184, by rfl⟩ : syracuseStep 56981825 = 42736369) B42736369
theorem B37987883 : Blo 2081435 37987883 := bstep (se 1 (by rfl) ⟨28490912, by rfl⟩ : syracuseStep 37987883 = 56981825) B56981825
theorem B25325255 : Blo 2081435 25325255 := bstep (se 1 (by rfl) ⟨18993941, by rfl⟩ : syracuseStep 25325255 = 37987883) B37987883
theorem B67534013 : Blo 2081435 67534013 := bstep (se 3 (by rfl) ⟨12662627, by rfl⟩ : syracuseStep 67534013 = 25325255) B25325255
theorem B45022675 : Blo 2081435 45022675 := bstep (se 1 (by rfl) ⟨33767006, by rfl⟩ : syracuseStep 45022675 = 67534013) B67534013
theorem B60030233 : Blo 2081435 60030233 := bstep (se 2 (by rfl) ⟨22511337, by rfl⟩ : syracuseStep 60030233 = 45022675) B45022675
theorem B40020155 : Blo 2081435 40020155 := bstep (se 1 (by rfl) ⟨30015116, by rfl⟩ : syracuseStep 40020155 = 60030233) B60030233
theorem B26680103 : Blo 2081435 26680103 := bstep (se 1 (by rfl) ⟨20010077, by rfl⟩ : syracuseStep 26680103 = 40020155) B40020155
theorem B17786735 : Blo 2081435 17786735 := bstep (se 1 (by rfl) ⟨13340051, by rfl⟩ : syracuseStep 17786735 = 26680103) B26680103
theorem B11857823 : Blo 2081435 11857823 := bstep (se 1 (by rfl) ⟨8893367, by rfl⟩ : syracuseStep 11857823 = 17786735) B17786735
theorem B7905215 : Blo 2081435 7905215 := bstep (se 1 (by rfl) ⟨5928911, by rfl⟩ : syracuseStep 7905215 = 11857823) B11857823
theorem B5270143 : Blo 2081435 5270143 := bstep (se 1 (by rfl) ⟨3952607, by rfl⟩ : syracuseStep 5270143 = 7905215) B7905215
theorem B7026857 : Blo 2081435 7026857 := bstep (se 2 (by rfl) ⟨2635071, by rfl⟩ : syracuseStep 7026857 = 5270143) B5270143
theorem B4684571 : Blo 2081435 4684571 := bstep (se 1 (by rfl) ⟨3513428, by rfl⟩ : syracuseStep 4684571 = 7026857) B7026857
theorem B3123047 : Blo 2081435 3123047 := bstep (se 1 (by rfl) ⟨2342285, by rfl⟩ : syracuseStep 3123047 = 4684571) B4684571
theorem B2082031 : Blo 2081435 2082031 := bstep (se 1 (by rfl) ⟨1561523, by rfl⟩ : syracuseStep 2082031 = 3123047) B3123047
theorem B3123053 : Blo 2081435 3123053 := bbase (se 3 (by rfl) ⟨585572, by rfl⟩ : syracuseStep 3123053 = 1171145) (by norm_num)
theorem B2082035 : Blo 2081435 2082035 := bstep (se 1 (by rfl) ⟨1561526, by rfl⟩ : syracuseStep 2082035 = 3123053) B3123053
theorem B4684589 : Blo 2081435 4684589 := bbase (se 3 (by rfl) ⟨878360, by rfl⟩ : syracuseStep 4684589 = 1756721) (by norm_num)
theorem B3123059 : Blo 2081435 3123059 := bstep (se 1 (by rfl) ⟨2342294, by rfl⟩ : syracuseStep 3123059 = 4684589) B4684589
theorem B2082039 : Blo 2081435 2082039 := bstep (se 1 (by rfl) ⟨1561529, by rfl⟩ : syracuseStep 2082039 = 3123059) B3123059
theorem B9137765 : Blo 2081435 9137765 := bbase (se 4 (by rfl) ⟨856665, by rfl⟩ : syracuseStep 9137765 = 1713331) (by norm_num)
theorem B6091843 : Blo 2081435 6091843 := bstep (se 1 (by rfl) ⟨4568882, by rfl⟩ : syracuseStep 6091843 = 9137765) B9137765
theorem B8122457 : Blo 2081435 8122457 := bstep (se 2 (by rfl) ⟨3045921, by rfl⟩ : syracuseStep 8122457 = 6091843) B6091843
theorem B5414971 : Blo 2081435 5414971 := bstep (se 1 (by rfl) ⟨4061228, by rfl⟩ : syracuseStep 5414971 = 8122457) B8122457
theorem B7219961 : Blo 2081435 7219961 := bstep (se 2 (by rfl) ⟨2707485, by rfl⟩ : syracuseStep 7219961 = 5414971) B5414971
theorem B4813307 : Blo 2081435 4813307 := bstep (se 1 (by rfl) ⟨3609980, by rfl⟩ : syracuseStep 4813307 = 7219961) B7219961
theorem B3208871 : Blo 2081435 3208871 := bstep (se 1 (by rfl) ⟨2406653, by rfl⟩ : syracuseStep 3208871 = 4813307) B4813307
theorem B2139247 : Blo 2081435 2139247 := bstep (se 1 (by rfl) ⟨1604435, by rfl⟩ : syracuseStep 2139247 = 3208871) B3208871
theorem B2852329 : Blo 2081435 2852329 := bstep (se 2 (by rfl) ⟨1069623, by rfl⟩ : syracuseStep 2852329 = 2139247) B2139247
theorem B3803105 : Blo 2081435 3803105 := bstep (se 2 (by rfl) ⟨1426164, by rfl⟩ : syracuseStep 3803105 = 2852329) B2852329
theorem B2535403 : Blo 2081435 2535403 := bstep (se 1 (by rfl) ⟨1901552, by rfl⟩ : syracuseStep 2535403 = 3803105) B3803105
theorem B3380537 : Blo 2081435 3380537 := bstep (se 2 (by rfl) ⟨1267701, by rfl⟩ : syracuseStep 3380537 = 2535403) B2535403
theorem B2253691 : Blo 2081435 2253691 := bstep (se 1 (by rfl) ⟨1690268, by rfl⟩ : syracuseStep 2253691 = 3380537) B3380537
theorem B3004921 : Blo 2081435 3004921 := bstep (se 2 (by rfl) ⟨1126845, by rfl⟩ : syracuseStep 3004921 = 2253691) B2253691
theorem B16026245 : Blo 2081435 16026245 := bstep (se 4 (by rfl) ⟨1502460, by rfl⟩ : syracuseStep 16026245 = 3004921) B3004921
theorem B10684163 : Blo 2081435 10684163 := bstep (se 1 (by rfl) ⟨8013122, by rfl⟩ : syracuseStep 10684163 = 16026245) B16026245
theorem B7122775 : Blo 2081435 7122775 := bstep (se 1 (by rfl) ⟨5342081, by rfl⟩ : syracuseStep 7122775 = 10684163) B10684163
theorem B9497033 : Blo 2081435 9497033 := bstep (se 2 (by rfl) ⟨3561387, by rfl⟩ : syracuseStep 9497033 = 7122775) B7122775
theorem B6331355 : Blo 2081435 6331355 := bstep (se 1 (by rfl) ⟨4748516, by rfl⟩ : syracuseStep 6331355 = 9497033) B9497033
theorem B4220903 : Blo 2081435 4220903 := bstep (se 1 (by rfl) ⟨3165677, by rfl⟩ : syracuseStep 4220903 = 6331355) B6331355
theorem B2813935 : Blo 2081435 2813935 := bstep (se 1 (by rfl) ⟨2110451, by rfl⟩ : syracuseStep 2813935 = 4220903) B4220903
theorem B3751913 : Blo 2081435 3751913 := bstep (se 2 (by rfl) ⟨1406967, by rfl⟩ : syracuseStep 3751913 = 2813935) B2813935
theorem B2501275 : Blo 2081435 2501275 := bstep (se 1 (by rfl) ⟨1875956, by rfl⟩ : syracuseStep 2501275 = 3751913) B3751913
theorem B3335033 : Blo 2081435 3335033 := bstep (se 2 (by rfl) ⟨1250637, by rfl⟩ : syracuseStep 3335033 = 2501275) B2501275
theorem B8893421 : Blo 2081435 8893421 := bstep (se 3 (by rfl) ⟨1667516, by rfl⟩ : syracuseStep 8893421 = 3335033) B3335033
theorem B5928947 : Blo 2081435 5928947 := bstep (se 1 (by rfl) ⟨4446710, by rfl⟩ : syracuseStep 5928947 = 8893421) B8893421
theorem B3952631 : Blo 2081435 3952631 := bstep (se 1 (by rfl) ⟨2964473, by rfl⟩ : syracuseStep 3952631 = 5928947) B5928947
theorem B2635087 : Blo 2081435 2635087 := bstep (se 1 (by rfl) ⟨1976315, by rfl⟩ : syracuseStep 2635087 = 3952631) B3952631
theorem B3513449 : Blo 2081435 3513449 := bstep (se 2 (by rfl) ⟨1317543, by rfl⟩ : syracuseStep 3513449 = 2635087) B2635087
theorem B2342299 : Blo 2081435 2342299 := bstep (se 1 (by rfl) ⟨1756724, by rfl⟩ : syracuseStep 2342299 = 3513449) B3513449
theorem B3123065 : Blo 2081435 3123065 := bstep (se 2 (by rfl) ⟨1171149, by rfl⟩ : syracuseStep 3123065 = 2342299) B2342299
theorem B2082043 : Blo 2081435 2082043 := bstep (se 1 (by rfl) ⟨1561532, by rfl⟩ : syracuseStep 2082043 = 3123065) B3123065
theorem B2374261 : Blo 2081435 2374261 := bbase (se 5 (by rfl) ⟨111293, by rfl⟩ : syracuseStep 2374261 = 222587) (by norm_num)
theorem B12662725 : Blo 2081435 12662725 := bstep (se 4 (by rfl) ⟨1187130, by rfl⟩ : syracuseStep 12662725 = 2374261) B2374261
theorem B16883633 : Blo 2081435 16883633 := bstep (se 2 (by rfl) ⟨6331362, by rfl⟩ : syracuseStep 16883633 = 12662725) B12662725
theorem B11255755 : Blo 2081435 11255755 := bstep (se 1 (by rfl) ⟨8441816, by rfl⟩ : syracuseStep 11255755 = 16883633) B16883633
theorem B15007673 : Blo 2081435 15007673 := bstep (se 2 (by rfl) ⟨5627877, by rfl⟩ : syracuseStep 15007673 = 11255755) B11255755
theorem B10005115 : Blo 2081435 10005115 := bstep (se 1 (by rfl) ⟨7503836, by rfl⟩ : syracuseStep 10005115 = 15007673) B15007673
theorem B13340153 : Blo 2081435 13340153 := bstep (se 2 (by rfl) ⟨5002557, by rfl⟩ : syracuseStep 13340153 = 10005115) B10005115
theorem B35573741 : Blo 2081435 35573741 := bstep (se 3 (by rfl) ⟨6670076, by rfl⟩ : syracuseStep 35573741 = 13340153) B13340153
theorem B23715827 : Blo 2081435 23715827 := bstep (se 1 (by rfl) ⟨17786870, by rfl⟩ : syracuseStep 23715827 = 35573741) B35573741
theorem B15810551 : Blo 2081435 15810551 := bstep (se 1 (by rfl) ⟨11857913, by rfl⟩ : syracuseStep 15810551 = 23715827) B23715827
theorem B10540367 : Blo 2081435 10540367 := bstep (se 1 (by rfl) ⟨7905275, by rfl⟩ : syracuseStep 10540367 = 15810551) B15810551
theorem B7026911 : Blo 2081435 7026911 := bstep (se 1 (by rfl) ⟨5270183, by rfl⟩ : syracuseStep 7026911 = 10540367) B10540367
theorem B4684607 : Blo 2081435 4684607 := bstep (se 1 (by rfl) ⟨3513455, by rfl⟩ : syracuseStep 4684607 = 7026911) B7026911
theorem B3123071 : Blo 2081435 3123071 := bstep (se 1 (by rfl) ⟨2342303, by rfl⟩ : syracuseStep 3123071 = 4684607) B4684607
theorem B2082047 : Blo 2081435 2082047 := bstep (se 1 (by rfl) ⟨1561535, by rfl⟩ : syracuseStep 2082047 = 3123071) B3123071
theorem B3123077 : Blo 2081435 3123077 := bbase (se 4 (by rfl) ⟨292788, by rfl⟩ : syracuseStep 3123077 = 585577) (by norm_num)
theorem B2082051 : Blo 2081435 2082051 := bstep (se 1 (by rfl) ⟨1561538, by rfl⟩ : syracuseStep 2082051 = 3123077) B3123077
theorem B3513469 : Blo 2081435 3513469 := bbase (se 3 (by rfl) ⟨658775, by rfl⟩ : syracuseStep 3513469 = 1317551) (by norm_num)
theorem B4684625 : Blo 2081435 4684625 := bstep (se 2 (by rfl) ⟨1756734, by rfl⟩ : syracuseStep 4684625 = 3513469) B3513469
theorem B3123083 : Blo 2081435 3123083 := bstep (se 1 (by rfl) ⟨2342312, by rfl⟩ : syracuseStep 3123083 = 4684625) B4684625
theorem B2082055 : Blo 2081435 2082055 := bstep (se 1 (by rfl) ⟨1561541, by rfl⟩ : syracuseStep 2082055 = 3123083) B3123083
theorem B2342317 : Blo 2081435 2342317 := bbase (se 3 (by rfl) ⟨439184, by rfl⟩ : syracuseStep 2342317 = 878369) (by norm_num)
theorem B3123089 : Blo 2081435 3123089 := bstep (se 2 (by rfl) ⟨1171158, by rfl⟩ : syracuseStep 3123089 = 2342317) B2342317
theorem B2082059 : Blo 2081435 2082059 := bstep (se 1 (by rfl) ⟨1561544, by rfl⟩ : syracuseStep 2082059 = 3123089) B3123089
theorem B7026965 : Blo 2081435 7026965 := bbase (se 6 (by rfl) ⟨164694, by rfl⟩ : syracuseStep 7026965 = 329389) (by norm_num)
theorem B4684643 : Blo 2081435 4684643 := bstep (se 1 (by rfl) ⟨3513482, by rfl⟩ : syracuseStep 4684643 = 7026965) B7026965
theorem B3123095 : Blo 2081435 3123095 := bstep (se 1 (by rfl) ⟨2342321, by rfl⟩ : syracuseStep 3123095 = 4684643) B4684643
theorem B2082063 : Blo 2081435 2082063 := bstep (se 1 (by rfl) ⟨1561547, by rfl⟩ : syracuseStep 2082063 = 3123095) B3123095
theorem B3123101 : Blo 2081435 3123101 := bbase (se 3 (by rfl) ⟨585581, by rfl⟩ : syracuseStep 3123101 = 1171163) (by norm_num)
theorem B2082067 : Blo 2081435 2082067 := bstep (se 1 (by rfl) ⟨1561550, by rfl⟩ : syracuseStep 2082067 = 3123101) B3123101
theorem B4684661 : Blo 2081435 4684661 := bbase (se 5 (by rfl) ⟨219593, by rfl⟩ : syracuseStep 4684661 = 439187) (by norm_num)
theorem B3123107 : Blo 2081435 3123107 := bstep (se 1 (by rfl) ⟨2342330, by rfl⟩ : syracuseStep 3123107 = 4684661) B4684661
theorem B2082071 : Blo 2081435 2082071 := bstep (se 1 (by rfl) ⟨1561553, by rfl⟩ : syracuseStep 2082071 = 3123107) B3123107
theorem B9497173 : Blo 2081435 9497173 := bbase (se 8 (by rfl) ⟨55647, by rfl⟩ : syracuseStep 9497173 = 111295) (by norm_num)
theorem B12662897 : Blo 2081435 12662897 := bstep (se 2 (by rfl) ⟨4748586, by rfl⟩ : syracuseStep 12662897 = 9497173) B9497173
theorem B33767725 : Blo 2081435 33767725 := bstep (se 3 (by rfl) ⟨6331448, by rfl⟩ : syracuseStep 33767725 = 12662897) B12662897
theorem B45023633 : Blo 2081435 45023633 := bstep (se 2 (by rfl) ⟨16883862, by rfl⟩ : syracuseStep 45023633 = 33767725) B33767725
theorem B30015755 : Blo 2081435 30015755 := bstep (se 1 (by rfl) ⟨22511816, by rfl⟩ : syracuseStep 30015755 = 45023633) B45023633
theorem B20010503 : Blo 2081435 20010503 := bstep (se 1 (by rfl) ⟨15007877, by rfl⟩ : syracuseStep 20010503 = 30015755) B30015755
theorem B13340335 : Blo 2081435 13340335 := bstep (se 1 (by rfl) ⟨10005251, by rfl⟩ : syracuseStep 13340335 = 20010503) B20010503
theorem B17787113 : Blo 2081435 17787113 := bstep (se 2 (by rfl) ⟨6670167, by rfl⟩ : syracuseStep 17787113 = 13340335) B13340335
theorem B11858075 : Blo 2081435 11858075 := bstep (se 1 (by rfl) ⟨8893556, by rfl⟩ : syracuseStep 11858075 = 17787113) B17787113
theorem B7905383 : Blo 2081435 7905383 := bstep (se 1 (by rfl) ⟨5929037, by rfl⟩ : syracuseStep 7905383 = 11858075) B11858075
theorem B5270255 : Blo 2081435 5270255 := bstep (se 1 (by rfl) ⟨3952691, by rfl⟩ : syracuseStep 5270255 = 7905383) B7905383
theorem B3513503 : Blo 2081435 3513503 := bstep (se 1 (by rfl) ⟨2635127, by rfl⟩ : syracuseStep 3513503 = 5270255) B5270255
theorem B2342335 : Blo 2081435 2342335 := bstep (se 1 (by rfl) ⟨1756751, by rfl⟩ : syracuseStep 2342335 = 3513503) B3513503
theorem B3123113 : Blo 2081435 3123113 := bstep (se 2 (by rfl) ⟨1171167, by rfl⟩ : syracuseStep 3123113 = 2342335) B2342335
theorem B2082075 : Blo 2081435 2082075 := bstep (se 1 (by rfl) ⟨1561556, by rfl⟩ : syracuseStep 2082075 = 3123113) B3123113
theorem B7905397 : Blo 2081435 7905397 := bbase (se 5 (by rfl) ⟨370565, by rfl⟩ : syracuseStep 7905397 = 741131) (by norm_num)
theorem B10540529 : Blo 2081435 10540529 := bstep (se 2 (by rfl) ⟨3952698, by rfl⟩ : syracuseStep 10540529 = 7905397) B7905397
theorem B7027019 : Blo 2081435 7027019 := bstep (se 1 (by rfl) ⟨5270264, by rfl⟩ : syracuseStep 7027019 = 10540529) B10540529
theorem B4684679 : Blo 2081435 4684679 := bstep (se 1 (by rfl) ⟨3513509, by rfl⟩ : syracuseStep 4684679 = 7027019) B7027019
theorem B3123119 : Blo 2081435 3123119 := bstep (se 1 (by rfl) ⟨2342339, by rfl⟩ : syracuseStep 3123119 = 4684679) B4684679
theorem B2082079 : Blo 2081435 2082079 := bstep (se 1 (by rfl) ⟨1561559, by rfl⟩ : syracuseStep 2082079 = 3123119) B3123119
theorem B3123125 : Blo 2081435 3123125 := bbase (se 5 (by rfl) ⟨146396, by rfl⟩ : syracuseStep 3123125 = 292793) (by norm_num)
theorem B2082083 : Blo 2081435 2082083 := bstep (se 1 (by rfl) ⟨1561562, by rfl⟩ : syracuseStep 2082083 = 3123125) B3123125
theorem B5270285 : Blo 2081435 5270285 := bbase (se 3 (by rfl) ⟨988178, by rfl⟩ : syracuseStep 5270285 = 1976357) (by norm_num)
theorem B3513523 : Blo 2081435 3513523 := bstep (se 1 (by rfl) ⟨2635142, by rfl⟩ : syracuseStep 3513523 = 5270285) B5270285
theorem B4684697 : Blo 2081435 4684697 := bstep (se 2 (by rfl) ⟨1756761, by rfl⟩ : syracuseStep 4684697 = 3513523) B3513523
theorem B3123131 : Blo 2081435 3123131 := bstep (se 1 (by rfl) ⟨2342348, by rfl⟩ : syracuseStep 3123131 = 4684697) B4684697
theorem B2082087 : Blo 2081435 2082087 := bstep (se 1 (by rfl) ⟨1561565, by rfl⟩ : syracuseStep 2082087 = 3123131) B3123131
theorem B2342353 : Blo 2081435 2342353 := bbase (se 2 (by rfl) ⟨878382, by rfl⟩ : syracuseStep 2342353 = 1756765) (by norm_num)
theorem B3123137 : Blo 2081435 3123137 := bstep (se 2 (by rfl) ⟨1171176, by rfl⟩ : syracuseStep 3123137 = 2342353) B2342353
theorem B2082091 : Blo 2081435 2082091 := bstep (se 1 (by rfl) ⟨1561568, by rfl⟩ : syracuseStep 2082091 = 3123137) B3123137
theorem B4446821 : Blo 2081435 4446821 := bbase (se 4 (by rfl) ⟨416889, by rfl⟩ : syracuseStep 4446821 = 833779) (by norm_num)
theorem B2964547 : Blo 2081435 2964547 := bstep (se 1 (by rfl) ⟨2223410, by rfl⟩ : syracuseStep 2964547 = 4446821) B4446821
theorem B3952729 : Blo 2081435 3952729 := bstep (se 2 (by rfl) ⟨1482273, by rfl⟩ : syracuseStep 3952729 = 2964547) B2964547
theorem B5270305 : Blo 2081435 5270305 := bstep (se 2 (by rfl) ⟨1976364, by rfl⟩ : syracuseStep 5270305 = 3952729) B3952729
theorem B7027073 : Blo 2081435 7027073 := bstep (se 2 (by rfl) ⟨2635152, by rfl⟩ : syracuseStep 7027073 = 5270305) B5270305
theorem B4684715 : Blo 2081435 4684715 := bstep (se 1 (by rfl) ⟨3513536, by rfl⟩ : syracuseStep 4684715 = 7027073) B7027073
theorem B3123143 : Blo 2081435 3123143 := bstep (se 1 (by rfl) ⟨2342357, by rfl⟩ : syracuseStep 3123143 = 4684715) B4684715
theorem B2082095 : Blo 2081435 2082095 := bstep (se 1 (by rfl) ⟨1561571, by rfl⟩ : syracuseStep 2082095 = 3123143) B3123143
theorem B3123149 : Blo 2081435 3123149 := bbase (se 3 (by rfl) ⟨585590, by rfl⟩ : syracuseStep 3123149 = 1171181) (by norm_num)
theorem B2082099 : Blo 2081435 2082099 := bstep (se 1 (by rfl) ⟨1561574, by rfl⟩ : syracuseStep 2082099 = 3123149) B3123149
theorem B4684733 : Blo 2081435 4684733 := bbase (se 3 (by rfl) ⟨878387, by rfl⟩ : syracuseStep 4684733 = 1756775) (by norm_num)
theorem B3123155 : Blo 2081435 3123155 := bstep (se 1 (by rfl) ⟨2342366, by rfl⟩ : syracuseStep 3123155 = 4684733) B4684733
theorem B2082103 : Blo 2081435 2082103 := bstep (se 1 (by rfl) ⟨1561577, by rfl⟩ : syracuseStep 2082103 = 3123155) B3123155
theorem B3513557 : Blo 2081435 3513557 := bbase (se 7 (by rfl) ⟨41174, by rfl⟩ : syracuseStep 3513557 = 82349) (by norm_num)
theorem B2342371 : Blo 2081435 2342371 := bstep (se 1 (by rfl) ⟨1756778, by rfl⟩ : syracuseStep 2342371 = 3513557) B3513557
theorem B3123161 : Blo 2081435 3123161 := bstep (se 2 (by rfl) ⟨1171185, by rfl⟩ : syracuseStep 3123161 = 2342371) B2342371
theorem B2082107 : Blo 2081435 2082107 := bstep (se 1 (by rfl) ⟨1561580, by rfl⟩ : syracuseStep 2082107 = 3123161) B3123161
theorem B3335141 : Blo 2081435 3335141 := bbase (se 4 (by rfl) ⟨312669, by rfl⟩ : syracuseStep 3335141 = 625339) (by norm_num)
theorem B8893709 : Blo 2081435 8893709 := bstep (se 3 (by rfl) ⟨1667570, by rfl⟩ : syracuseStep 8893709 = 3335141) B3335141
theorem B5929139 : Blo 2081435 5929139 := bstep (se 1 (by rfl) ⟨4446854, by rfl⟩ : syracuseStep 5929139 = 8893709) B8893709
theorem B15811037 : Blo 2081435 15811037 := bstep (se 3 (by rfl) ⟨2964569, by rfl⟩ : syracuseStep 15811037 = 5929139) B5929139
theorem B10540691 : Blo 2081435 10540691 := bstep (se 1 (by rfl) ⟨7905518, by rfl⟩ : syracuseStep 10540691 = 15811037) B15811037
theorem B7027127 : Blo 2081435 7027127 := bstep (se 1 (by rfl) ⟨5270345, by rfl⟩ : syracuseStep 7027127 = 10540691) B10540691
theorem B4684751 : Blo 2081435 4684751 := bstep (se 1 (by rfl) ⟨3513563, by rfl⟩ : syracuseStep 4684751 = 7027127) B7027127
theorem B3123167 : Blo 2081435 3123167 := bstep (se 1 (by rfl) ⟨2342375, by rfl⟩ : syracuseStep 3123167 = 4684751) B4684751
theorem B2082111 : Blo 2081435 2082111 := bstep (se 1 (by rfl) ⟨1561583, by rfl⟩ : syracuseStep 2082111 = 3123167) B3123167
theorem B3123173 : Blo 2081435 3123173 := bbase (se 4 (by rfl) ⟨292797, by rfl⟩ : syracuseStep 3123173 = 585595) (by norm_num)
theorem B2082115 : Blo 2081435 2082115 := bstep (se 1 (by rfl) ⟨1561586, by rfl⟩ : syracuseStep 2082115 = 3123173) B3123173
theorem B6670309 : Blo 2081435 6670309 := bbase (se 4 (by rfl) ⟨625341, by rfl⟩ : syracuseStep 6670309 = 1250683) (by norm_num)
theorem B8893745 : Blo 2081435 8893745 := bstep (se 2 (by rfl) ⟨3335154, by rfl⟩ : syracuseStep 8893745 = 6670309) B6670309
theorem B5929163 : Blo 2081435 5929163 := bstep (se 1 (by rfl) ⟨4446872, by rfl⟩ : syracuseStep 5929163 = 8893745) B8893745
theorem B3952775 : Blo 2081435 3952775 := bstep (se 1 (by rfl) ⟨2964581, by rfl⟩ : syracuseStep 3952775 = 5929163) B5929163
theorem B2635183 : Blo 2081435 2635183 := bstep (se 1 (by rfl) ⟨1976387, by rfl⟩ : syracuseStep 2635183 = 3952775) B3952775
theorem B3513577 : Blo 2081435 3513577 := bstep (se 2 (by rfl) ⟨1317591, by rfl⟩ : syracuseStep 3513577 = 2635183) B2635183
theorem B4684769 : Blo 2081435 4684769 := bstep (se 2 (by rfl) ⟨1756788, by rfl⟩ : syracuseStep 4684769 = 3513577) B3513577
theorem B3123179 : Blo 2081435 3123179 := bstep (se 1 (by rfl) ⟨2342384, by rfl⟩ : syracuseStep 3123179 = 4684769) B4684769
theorem B2082119 : Blo 2081435 2082119 := bstep (se 1 (by rfl) ⟨1561589, by rfl⟩ : syracuseStep 2082119 = 3123179) B3123179
theorem B2342389 : Blo 2081435 2342389 := bbase (se 5 (by rfl) ⟨109799, by rfl⟩ : syracuseStep 2342389 = 219599) (by norm_num)
theorem B3123185 : Blo 2081435 3123185 := bstep (se 2 (by rfl) ⟨1171194, by rfl⟩ : syracuseStep 3123185 = 2342389) B2342389
theorem B2082123 : Blo 2081435 2082123 := bstep (se 1 (by rfl) ⟨1561592, by rfl⟩ : syracuseStep 2082123 = 3123185) B3123185
theorem B2635193 : Blo 2081435 2635193 := bbase (se 2 (by rfl) ⟨988197, by rfl⟩ : syracuseStep 2635193 = 1976395) (by norm_num)
theorem B7027181 : Blo 2081435 7027181 := bstep (se 3 (by rfl) ⟨1317596, by rfl⟩ : syracuseStep 7027181 = 2635193) B2635193
theorem B4684787 : Blo 2081435 4684787 := bstep (se 1 (by rfl) ⟨3513590, by rfl⟩ : syracuseStep 4684787 = 7027181) B7027181
theorem B3123191 : Blo 2081435 3123191 := bstep (se 1 (by rfl) ⟨2342393, by rfl⟩ : syracuseStep 3123191 = 4684787) B4684787
theorem B2082127 : Blo 2081435 2082127 := bstep (se 1 (by rfl) ⟨1561595, by rfl⟩ : syracuseStep 2082127 = 3123191) B3123191
theorem B3123197 : Blo 2081435 3123197 := bbase (se 3 (by rfl) ⟨585599, by rfl⟩ : syracuseStep 3123197 = 1171199) (by norm_num)
theorem B2082131 : Blo 2081435 2082131 := bstep (se 1 (by rfl) ⟨1561598, by rfl⟩ : syracuseStep 2082131 = 3123197) B3123197
theorem B4684805 : Blo 2081435 4684805 := bbase (se 4 (by rfl) ⟨439200, by rfl⟩ : syracuseStep 4684805 = 878401) (by norm_num)
theorem B3123203 : Blo 2081435 3123203 := bstep (se 1 (by rfl) ⟨2342402, by rfl⟩ : syracuseStep 3123203 = 4684805) B4684805
theorem B2082135 : Blo 2081435 2082135 := bstep (se 1 (by rfl) ⟨1561601, by rfl⟩ : syracuseStep 2082135 = 3123203) B3123203
theorem B3952813 : Blo 2081435 3952813 := bbase (se 3 (by rfl) ⟨741152, by rfl⟩ : syracuseStep 3952813 = 1482305) (by norm_num)
theorem B5270417 : Blo 2081435 5270417 := bstep (se 2 (by rfl) ⟨1976406, by rfl⟩ : syracuseStep 5270417 = 3952813) B3952813
theorem B3513611 : Blo 2081435 3513611 := bstep (se 1 (by rfl) ⟨2635208, by rfl⟩ : syracuseStep 3513611 = 5270417) B5270417
theorem B2342407 : Blo 2081435 2342407 := bstep (se 1 (by rfl) ⟨1756805, by rfl⟩ : syracuseStep 2342407 = 3513611) B3513611
theorem B3123209 : Blo 2081435 3123209 := bstep (se 2 (by rfl) ⟨1171203, by rfl⟩ : syracuseStep 3123209 = 2342407) B2342407
theorem B2082139 : Blo 2081435 2082139 := bstep (se 1 (by rfl) ⟨1561604, by rfl⟩ : syracuseStep 2082139 = 3123209) B3123209
theorem B10540853 : Blo 2081435 10540853 := bbase (se 5 (by rfl) ⟨494102, by rfl⟩ : syracuseStep 10540853 = 988205) (by norm_num)
theorem B7027235 : Blo 2081435 7027235 := bstep (se 1 (by rfl) ⟨5270426, by rfl⟩ : syracuseStep 7027235 = 10540853) B10540853
theorem B4684823 : Blo 2081435 4684823 := bstep (se 1 (by rfl) ⟨3513617, by rfl⟩ : syracuseStep 4684823 = 7027235) B7027235
theorem B3123215 : Blo 2081435 3123215 := bstep (se 1 (by rfl) ⟨2342411, by rfl⟩ : syracuseStep 3123215 = 4684823) B4684823
theorem B2082143 : Blo 2081435 2082143 := bstep (se 1 (by rfl) ⟨1561607, by rfl⟩ : syracuseStep 2082143 = 3123215) B3123215
theorem B3123221 : Blo 2081435 3123221 := bbase (se 6 (by rfl) ⟨73200, by rfl⟩ : syracuseStep 3123221 = 146401) (by norm_num)
theorem B2082147 : Blo 2081435 2082147 := bstep (se 1 (by rfl) ⟨1561610, by rfl⟩ : syracuseStep 2082147 = 3123221) B3123221
theorem B13340821 : Blo 2081435 13340821 := bbase (se 6 (by rfl) ⟨312675, by rfl⟩ : syracuseStep 13340821 = 625351) (by norm_num)
theorem B17787761 : Blo 2081435 17787761 := bstep (se 2 (by rfl) ⟨6670410, by rfl⟩ : syracuseStep 17787761 = 13340821) B13340821
theorem B11858507 : Blo 2081435 11858507 := bstep (se 1 (by rfl) ⟨8893880, by rfl⟩ : syracuseStep 11858507 = 17787761) B17787761
theorem B7905671 : Blo 2081435 7905671 := bstep (se 1 (by rfl) ⟨5929253, by rfl⟩ : syracuseStep 7905671 = 11858507) B11858507
theorem B5270447 : Blo 2081435 5270447 := bstep (se 1 (by rfl) ⟨3952835, by rfl⟩ : syracuseStep 5270447 = 7905671) B7905671
theorem B3513631 : Blo 2081435 3513631 := bstep (se 1 (by rfl) ⟨2635223, by rfl⟩ : syracuseStep 3513631 = 5270447) B5270447
theorem B4684841 : Blo 2081435 4684841 := bstep (se 2 (by rfl) ⟨1756815, by rfl⟩ : syracuseStep 4684841 = 3513631) B3513631
theorem B3123227 : Blo 2081435 3123227 := bstep (se 1 (by rfl) ⟨2342420, by rfl⟩ : syracuseStep 3123227 = 4684841) B4684841
theorem B2082151 : Blo 2081435 2082151 := bstep (se 1 (by rfl) ⟨1561613, by rfl⟩ : syracuseStep 2082151 = 3123227) B3123227
theorem B2342425 : Blo 2081435 2342425 := bbase (se 2 (by rfl) ⟨878409, by rfl⟩ : syracuseStep 2342425 = 1756819) (by norm_num)
theorem B3123233 : Blo 2081435 3123233 := bstep (se 2 (by rfl) ⟨1171212, by rfl⟩ : syracuseStep 3123233 = 2342425) B2342425
theorem B2082155 : Blo 2081435 2082155 := bstep (se 1 (by rfl) ⟨1561616, by rfl⟩ : syracuseStep 2082155 = 3123233) B3123233
theorem B7905701 : Blo 2081435 7905701 := bbase (se 4 (by rfl) ⟨741159, by rfl⟩ : syracuseStep 7905701 = 1482319) (by norm_num)
theorem B5270467 : Blo 2081435 5270467 := bstep (se 1 (by rfl) ⟨3952850, by rfl⟩ : syracuseStep 5270467 = 7905701) B7905701
theorem B7027289 : Blo 2081435 7027289 := bstep (se 2 (by rfl) ⟨2635233, by rfl⟩ : syracuseStep 7027289 = 5270467) B5270467
theorem B4684859 : Blo 2081435 4684859 := bstep (se 1 (by rfl) ⟨3513644, by rfl⟩ : syracuseStep 4684859 = 7027289) B7027289
theorem B3123239 : Blo 2081435 3123239 := bstep (se 1 (by rfl) ⟨2342429, by rfl⟩ : syracuseStep 3123239 = 4684859) B4684859
theorem B2082159 : Blo 2081435 2082159 := bstep (se 1 (by rfl) ⟨1561619, by rfl⟩ : syracuseStep 2082159 = 3123239) B3123239
theorem B3123245 : Blo 2081435 3123245 := bbase (se 3 (by rfl) ⟨585608, by rfl⟩ : syracuseStep 3123245 = 1171217) (by norm_num)
theorem B2082163 : Blo 2081435 2082163 := bstep (se 1 (by rfl) ⟨1561622, by rfl⟩ : syracuseStep 2082163 = 3123245) B3123245
theorem B4684877 : Blo 2081435 4684877 := bbase (se 3 (by rfl) ⟨878414, by rfl⟩ : syracuseStep 4684877 = 1756829) (by norm_num)
theorem B3123251 : Blo 2081435 3123251 := bstep (se 1 (by rfl) ⟨2342438, by rfl⟩ : syracuseStep 3123251 = 4684877) B4684877
theorem B2082167 : Blo 2081435 2082167 := bstep (se 1 (by rfl) ⟨1561625, by rfl⟩ : syracuseStep 2082167 = 3123251) B3123251
theorem B2635249 : Blo 2081435 2635249 := bbase (se 2 (by rfl) ⟨988218, by rfl⟩ : syracuseStep 2635249 = 1976437) (by norm_num)
theorem B3513665 : Blo 2081435 3513665 := bstep (se 2 (by rfl) ⟨1317624, by rfl⟩ : syracuseStep 3513665 = 2635249) B2635249
theorem B2342443 : Blo 2081435 2342443 := bstep (se 1 (by rfl) ⟨1756832, by rfl⟩ : syracuseStep 2342443 = 3513665) B3513665
theorem B3123257 : Blo 2081435 3123257 := bstep (se 2 (by rfl) ⟨1171221, by rfl⟩ : syracuseStep 3123257 = 2342443) B2342443
theorem B2082171 : Blo 2081435 2082171 := bstep (se 1 (by rfl) ⟨1561628, by rfl⟩ : syracuseStep 2082171 = 3123257) B3123257
theorem B15008597 : Blo 2081435 15008597 := bbase (se 9 (by rfl) ⟨43970, by rfl⟩ : syracuseStep 15008597 = 87941) (by norm_num)
theorem B10005731 : Blo 2081435 10005731 := bstep (se 1 (by rfl) ⟨7504298, by rfl⟩ : syracuseStep 10005731 = 15008597) B15008597
theorem B6670487 : Blo 2081435 6670487 := bstep (se 1 (by rfl) ⟨5002865, by rfl⟩ : syracuseStep 6670487 = 10005731) B10005731
theorem B4446991 : Blo 2081435 4446991 := bstep (se 1 (by rfl) ⟨3335243, by rfl⟩ : syracuseStep 4446991 = 6670487) B6670487
theorem B23717285 : Blo 2081435 23717285 := bstep (se 4 (by rfl) ⟨2223495, by rfl⟩ : syracuseStep 23717285 = 4446991) B4446991
theorem B15811523 : Blo 2081435 15811523 := bstep (se 1 (by rfl) ⟨11858642, by rfl⟩ : syracuseStep 15811523 = 23717285) B23717285
theorem B10541015 : Blo 2081435 10541015 := bstep (se 1 (by rfl) ⟨7905761, by rfl⟩ : syracuseStep 10541015 = 15811523) B15811523
theorem B7027343 : Blo 2081435 7027343 := bstep (se 1 (by rfl) ⟨5270507, by rfl⟩ : syracuseStep 7027343 = 10541015) B10541015
theorem B4684895 : Blo 2081435 4684895 := bstep (se 1 (by rfl) ⟨3513671, by rfl⟩ : syracuseStep 4684895 = 7027343) B7027343
theorem B3123263 : Blo 2081435 3123263 := bstep (se 1 (by rfl) ⟨2342447, by rfl⟩ : syracuseStep 3123263 = 4684895) B4684895
theorem B2082175 : Blo 2081435 2082175 := bstep (se 1 (by rfl) ⟨1561631, by rfl⟩ : syracuseStep 2082175 = 3123263) B3123263
theorem B3123269 : Blo 2081435 3123269 := bbase (se 4 (by rfl) ⟨292806, by rfl⟩ : syracuseStep 3123269 = 585613) (by norm_num)
theorem B2082179 : Blo 2081435 2082179 := bstep (se 1 (by rfl) ⟨1561634, by rfl⟩ : syracuseStep 2082179 = 3123269) B3123269
theorem B3513685 : Blo 2081435 3513685 := bbase (se 11 (by rfl) ⟨2573, by rfl⟩ : syracuseStep 3513685 = 5147) (by norm_num)
theorem B4684913 : Blo 2081435 4684913 := bstep (se 2 (by rfl) ⟨1756842, by rfl⟩ : syracuseStep 4684913 = 3513685) B3513685
theorem B3123275 : Blo 2081435 3123275 := bstep (se 1 (by rfl) ⟨2342456, by rfl⟩ : syracuseStep 3123275 = 4684913) B4684913
theorem B2082183 : Blo 2081435 2082183 := bstep (se 1 (by rfl) ⟨1561637, by rfl⟩ : syracuseStep 2082183 = 3123275) B3123275
theorem B2342461 : Blo 2081435 2342461 := bbase (se 3 (by rfl) ⟨439211, by rfl⟩ : syracuseStep 2342461 = 878423) (by norm_num)
theorem B3123281 : Blo 2081435 3123281 := bstep (se 2 (by rfl) ⟨1171230, by rfl⟩ : syracuseStep 3123281 = 2342461) B2342461
theorem B2082187 : Blo 2081435 2082187 := bstep (se 1 (by rfl) ⟨1561640, by rfl⟩ : syracuseStep 2082187 = 3123281) B3123281
theorem B7027397 : Blo 2081435 7027397 := bbase (se 4 (by rfl) ⟨658818, by rfl⟩ : syracuseStep 7027397 = 1317637) (by norm_num)
theorem B4684931 : Blo 2081435 4684931 := bstep (se 1 (by rfl) ⟨3513698, by rfl⟩ : syracuseStep 4684931 = 7027397) B7027397
theorem B3123287 : Blo 2081435 3123287 := bstep (se 1 (by rfl) ⟨2342465, by rfl⟩ : syracuseStep 3123287 = 4684931) B4684931
theorem B2082191 : Blo 2081435 2082191 := bstep (se 1 (by rfl) ⟨1561643, by rfl⟩ : syracuseStep 2082191 = 3123287) B3123287
theorem B3123293 : Blo 2081435 3123293 := bbase (se 3 (by rfl) ⟨585617, by rfl⟩ : syracuseStep 3123293 = 1171235) (by norm_num)
theorem B2082195 : Blo 2081435 2082195 := bstep (se 1 (by rfl) ⟨1561646, by rfl⟩ : syracuseStep 2082195 = 3123293) B3123293
theorem B4684949 : Blo 2081435 4684949 := bbase (se 6 (by rfl) ⟨109803, by rfl⟩ : syracuseStep 4684949 = 219607) (by norm_num)
theorem B3123299 : Blo 2081435 3123299 := bstep (se 1 (by rfl) ⟨2342474, by rfl⟩ : syracuseStep 3123299 = 4684949) B4684949
theorem B2082199 : Blo 2081435 2082199 := bstep (se 1 (by rfl) ⟨1561649, by rfl⟩ : syracuseStep 2082199 = 3123299) B3123299
theorem B2964701 : Blo 2081435 2964701 := bbase (se 3 (by rfl) ⟨555881, by rfl⟩ : syracuseStep 2964701 = 1111763) (by norm_num)
theorem B7905869 : Blo 2081435 7905869 := bstep (se 3 (by rfl) ⟨1482350, by rfl⟩ : syracuseStep 7905869 = 2964701) B2964701
theorem B5270579 : Blo 2081435 5270579 := bstep (se 1 (by rfl) ⟨3952934, by rfl⟩ : syracuseStep 5270579 = 7905869) B7905869
theorem B3513719 : Blo 2081435 3513719 := bstep (se 1 (by rfl) ⟨2635289, by rfl⟩ : syracuseStep 3513719 = 5270579) B5270579
theorem B2342479 : Blo 2081435 2342479 := bstep (se 1 (by rfl) ⟨1756859, by rfl⟩ : syracuseStep 2342479 = 3513719) B3513719
theorem B3123305 : Blo 2081435 3123305 := bstep (se 2 (by rfl) ⟨1171239, by rfl⟩ : syracuseStep 3123305 = 2342479) B2342479
theorem B2082203 : Blo 2081435 2082203 := bstep (se 1 (by rfl) ⟨1561652, by rfl⟩ : syracuseStep 2082203 = 3123305) B3123305
theorem B10684997 : Blo 2081435 10684997 := bbase (se 4 (by rfl) ⟨1001718, by rfl⟩ : syracuseStep 10684997 = 2003437) (by norm_num)
theorem B7123331 : Blo 2081435 7123331 := bstep (se 1 (by rfl) ⟨5342498, by rfl⟩ : syracuseStep 7123331 = 10684997) B10684997
theorem B4748887 : Blo 2081435 4748887 := bstep (se 1 (by rfl) ⟨3561665, by rfl⟩ : syracuseStep 4748887 = 7123331) B7123331
theorem B25327397 : Blo 2081435 25327397 := bstep (se 4 (by rfl) ⟨2374443, by rfl⟩ : syracuseStep 25327397 = 4748887) B4748887
theorem B16884931 : Blo 2081435 16884931 := bstep (se 1 (by rfl) ⟨12663698, by rfl⟩ : syracuseStep 16884931 = 25327397) B25327397
theorem B22513241 : Blo 2081435 22513241 := bstep (se 2 (by rfl) ⟨8442465, by rfl⟩ : syracuseStep 22513241 = 16884931) B16884931
theorem B15008827 : Blo 2081435 15008827 := bstep (se 1 (by rfl) ⟨11256620, by rfl⟩ : syracuseStep 15008827 = 22513241) B22513241
theorem B20011769 : Blo 2081435 20011769 := bstep (se 2 (by rfl) ⟨7504413, by rfl⟩ : syracuseStep 20011769 = 15008827) B15008827
theorem B13341179 : Blo 2081435 13341179 := bstep (se 1 (by rfl) ⟨10005884, by rfl⟩ : syracuseStep 13341179 = 20011769) B20011769
theorem B8894119 : Blo 2081435 8894119 := bstep (se 1 (by rfl) ⟨6670589, by rfl⟩ : syracuseStep 8894119 = 13341179) B13341179
theorem B11858825 : Blo 2081435 11858825 := bstep (se 2 (by rfl) ⟨4447059, by rfl⟩ : syracuseStep 11858825 = 8894119) B8894119
theorem B7905883 : Blo 2081435 7905883 := bstep (se 1 (by rfl) ⟨5929412, by rfl⟩ : syracuseStep 7905883 = 11858825) B11858825
theorem B10541177 : Blo 2081435 10541177 := bstep (se 2 (by rfl) ⟨3952941, by rfl⟩ : syracuseStep 10541177 = 7905883) B7905883
theorem B7027451 : Blo 2081435 7027451 := bstep (se 1 (by rfl) ⟨5270588, by rfl⟩ : syracuseStep 7027451 = 10541177) B10541177
theorem B4684967 : Blo 2081435 4684967 := bstep (se 1 (by rfl) ⟨3513725, by rfl⟩ : syracuseStep 4684967 = 7027451) B7027451
theorem B3123311 : Blo 2081435 3123311 := bstep (se 1 (by rfl) ⟨2342483, by rfl⟩ : syracuseStep 3123311 = 4684967) B4684967
theorem B2082207 : Blo 2081435 2082207 := bstep (se 1 (by rfl) ⟨1561655, by rfl⟩ : syracuseStep 2082207 = 3123311) B3123311
theorem B3123317 : Blo 2081435 3123317 := bbase (se 5 (by rfl) ⟨146405, by rfl⟩ : syracuseStep 3123317 = 292811) (by norm_num)
theorem B2082211 : Blo 2081435 2082211 := bstep (se 1 (by rfl) ⟨1561658, by rfl⟩ : syracuseStep 2082211 = 3123317) B3123317
theorem B3952957 : Blo 2081435 3952957 := bbase (se 3 (by rfl) ⟨741179, by rfl⟩ : syracuseStep 3952957 = 1482359) (by norm_num)
theorem B5270609 : Blo 2081435 5270609 := bstep (se 2 (by rfl) ⟨1976478, by rfl⟩ : syracuseStep 5270609 = 3952957) B3952957
theorem B3513739 : Blo 2081435 3513739 := bstep (se 1 (by rfl) ⟨2635304, by rfl⟩ : syracuseStep 3513739 = 5270609) B5270609
theorem B4684985 : Blo 2081435 4684985 := bstep (se 2 (by rfl) ⟨1756869, by rfl⟩ : syracuseStep 4684985 = 3513739) B3513739
theorem B3123323 : Blo 2081435 3123323 := bstep (se 1 (by rfl) ⟨2342492, by rfl⟩ : syracuseStep 3123323 = 4684985) B4684985
theorem B2082215 : Blo 2081435 2082215 := bstep (se 1 (by rfl) ⟨1561661, by rfl⟩ : syracuseStep 2082215 = 3123323) B3123323
theorem B2342497 : Blo 2081435 2342497 := bbase (se 2 (by rfl) ⟨878436, by rfl⟩ : syracuseStep 2342497 = 1756873) (by norm_num)
theorem B3123329 : Blo 2081435 3123329 := bstep (se 2 (by rfl) ⟨1171248, by rfl⟩ : syracuseStep 3123329 = 2342497) B2342497
theorem B2082219 : Blo 2081435 2082219 := bstep (se 1 (by rfl) ⟨1561664, by rfl⟩ : syracuseStep 2082219 = 3123329) B3123329
theorem B5270629 : Blo 2081435 5270629 := bbase (se 4 (by rfl) ⟨494121, by rfl⟩ : syracuseStep 5270629 = 988243) (by norm_num)
theorem B7027505 : Blo 2081435 7027505 := bstep (se 2 (by rfl) ⟨2635314, by rfl⟩ : syracuseStep 7027505 = 5270629) B5270629
theorem B4685003 : Blo 2081435 4685003 := bstep (se 1 (by rfl) ⟨3513752, by rfl⟩ : syracuseStep 4685003 = 7027505) B7027505
theorem B3123335 : Blo 2081435 3123335 := bstep (se 1 (by rfl) ⟨2342501, by rfl⟩ : syracuseStep 3123335 = 4685003) B4685003
theorem B2082223 : Blo 2081435 2082223 := bstep (se 1 (by rfl) ⟨1561667, by rfl⟩ : syracuseStep 2082223 = 3123335) B3123335
theorem B3123341 : Blo 2081435 3123341 := bbase (se 3 (by rfl) ⟨585626, by rfl⟩ : syracuseStep 3123341 = 1171253) (by norm_num)
theorem B2082227 : Blo 2081435 2082227 := bstep (se 1 (by rfl) ⟨1561670, by rfl⟩ : syracuseStep 2082227 = 3123341) B3123341
theorem B4685021 : Blo 2081435 4685021 := bbase (se 3 (by rfl) ⟨878441, by rfl⟩ : syracuseStep 4685021 = 1756883) (by norm_num)
theorem B3123347 : Blo 2081435 3123347 := bstep (se 1 (by rfl) ⟨2342510, by rfl⟩ : syracuseStep 3123347 = 4685021) B4685021
theorem B2082231 : Blo 2081435 2082231 := bstep (se 1 (by rfl) ⟨1561673, by rfl⟩ : syracuseStep 2082231 = 3123347) B3123347
theorem B3513773 : Blo 2081435 3513773 := bbase (se 3 (by rfl) ⟨658832, by rfl⟩ : syracuseStep 3513773 = 1317665) (by norm_num)
theorem B2342515 : Blo 2081435 2342515 := bstep (se 1 (by rfl) ⟨1756886, by rfl⟩ : syracuseStep 2342515 = 3513773) B3513773
theorem B3123353 : Blo 2081435 3123353 := bstep (se 2 (by rfl) ⟨1171257, by rfl⟩ : syracuseStep 3123353 = 2342515) B2342515
theorem B2082235 : Blo 2081435 2082235 := bstep (se 1 (by rfl) ⟨1561676, by rfl⟩ : syracuseStep 2082235 = 3123353) B3123353
theorem B3165973 : Blo 2081435 3165973 := bbase (se 6 (by rfl) ⟨74202, by rfl⟩ : syracuseStep 3165973 = 148405) (by norm_num)
theorem B16885189 : Blo 2081435 16885189 := bstep (se 4 (by rfl) ⟨1582986, by rfl⟩ : syracuseStep 16885189 = 3165973) B3165973
theorem B90054341 : Blo 2081435 90054341 := bstep (se 4 (by rfl) ⟨8442594, by rfl⟩ : syracuseStep 90054341 = 16885189) B16885189
theorem B60036227 : Blo 2081435 60036227 := bstep (se 1 (by rfl) ⟨45027170, by rfl⟩ : syracuseStep 60036227 = 90054341) B90054341
theorem B40024151 : Blo 2081435 40024151 := bstep (se 1 (by rfl) ⟨30018113, by rfl⟩ : syracuseStep 40024151 = 60036227) B60036227
theorem B26682767 : Blo 2081435 26682767 := bstep (se 1 (by rfl) ⟨20012075, by rfl⟩ : syracuseStep 26682767 = 40024151) B40024151
theorem B17788511 : Blo 2081435 17788511 := bstep (se 1 (by rfl) ⟨13341383, by rfl⟩ : syracuseStep 17788511 = 26682767) B26682767
theorem B11859007 : Blo 2081435 11859007 := bstep (se 1 (by rfl) ⟨8894255, by rfl⟩ : syracuseStep 11859007 = 17788511) B17788511
theorem B15812009 : Blo 2081435 15812009 := bstep (se 2 (by rfl) ⟨5929503, by rfl⟩ : syracuseStep 15812009 = 11859007) B11859007
theorem B10541339 : Blo 2081435 10541339 := bstep (se 1 (by rfl) ⟨7906004, by rfl⟩ : syracuseStep 10541339 = 15812009) B15812009
theorem B7027559 : Blo 2081435 7027559 := bstep (se 1 (by rfl) ⟨5270669, by rfl⟩ : syracuseStep 7027559 = 10541339) B10541339
theorem B4685039 : Blo 2081435 4685039 := bstep (se 1 (by rfl) ⟨3513779, by rfl⟩ : syracuseStep 4685039 = 7027559) B7027559
theorem B3123359 : Blo 2081435 3123359 := bstep (se 1 (by rfl) ⟨2342519, by rfl⟩ : syracuseStep 3123359 = 4685039) B4685039
theorem B2082239 : Blo 2081435 2082239 := bstep (se 1 (by rfl) ⟨1561679, by rfl⟩ : syracuseStep 2082239 = 3123359) B3123359
theorem B3123365 : Blo 2081435 3123365 := bbase (se 4 (by rfl) ⟨292815, by rfl⟩ : syracuseStep 3123365 = 585631) (by norm_num)
theorem B2082243 : Blo 2081435 2082243 := bstep (se 1 (by rfl) ⟨1561682, by rfl⟩ : syracuseStep 2082243 = 3123365) B3123365
theorem B2635345 : Blo 2081435 2635345 := bbase (se 2 (by rfl) ⟨988254, by rfl⟩ : syracuseStep 2635345 = 1976509) (by norm_num)
theorem B3513793 : Blo 2081435 3513793 := bstep (se 2 (by rfl) ⟨1317672, by rfl⟩ : syracuseStep 3513793 = 2635345) B2635345
theorem B4685057 : Blo 2081435 4685057 := bstep (se 2 (by rfl) ⟨1756896, by rfl⟩ : syracuseStep 4685057 = 3513793) B3513793
theorem B3123371 : Blo 2081435 3123371 := bstep (se 1 (by rfl) ⟨2342528, by rfl⟩ : syracuseStep 3123371 = 4685057) B4685057
theorem B2082247 : Blo 2081435 2082247 := bstep (se 1 (by rfl) ⟨1561685, by rfl⟩ : syracuseStep 2082247 = 3123371) B3123371
theorem B2342533 : Blo 2081435 2342533 := bbase (se 4 (by rfl) ⟨219612, by rfl⟩ : syracuseStep 2342533 = 439225) (by norm_num)
theorem B3123377 : Blo 2081435 3123377 := bstep (se 2 (by rfl) ⟨1171266, by rfl⟩ : syracuseStep 3123377 = 2342533) B2342533
theorem B2082251 : Blo 2081435 2082251 := bstep (se 1 (by rfl) ⟨1561688, by rfl⟩ : syracuseStep 2082251 = 3123377) B3123377
theorem B2814221 : Blo 2081435 2814221 := bbase (se 3 (by rfl) ⟨527666, by rfl⟩ : syracuseStep 2814221 = 1055333) (by norm_num)
theorem B7504589 : Blo 2081435 7504589 := bstep (se 3 (by rfl) ⟨1407110, by rfl⟩ : syracuseStep 7504589 = 2814221) B2814221
theorem B5003059 : Blo 2081435 5003059 := bstep (se 1 (by rfl) ⟨3752294, by rfl⟩ : syracuseStep 5003059 = 7504589) B7504589
theorem B6670745 : Blo 2081435 6670745 := bstep (se 2 (by rfl) ⟨2501529, by rfl⟩ : syracuseStep 6670745 = 5003059) B5003059
theorem B4447163 : Blo 2081435 4447163 := bstep (se 1 (by rfl) ⟨3335372, by rfl⟩ : syracuseStep 4447163 = 6670745) B6670745
theorem B2964775 : Blo 2081435 2964775 := bstep (se 1 (by rfl) ⟨2223581, by rfl⟩ : syracuseStep 2964775 = 4447163) B4447163
theorem B3953033 : Blo 2081435 3953033 := bstep (se 2 (by rfl) ⟨1482387, by rfl⟩ : syracuseStep 3953033 = 2964775) B2964775
theorem B2635355 : Blo 2081435 2635355 := bstep (se 1 (by rfl) ⟨1976516, by rfl⟩ : syracuseStep 2635355 = 3953033) B3953033
theorem B7027613 : Blo 2081435 7027613 := bstep (se 3 (by rfl) ⟨1317677, by rfl⟩ : syracuseStep 7027613 = 2635355) B2635355
theorem B4685075 : Blo 2081435 4685075 := bstep (se 1 (by rfl) ⟨3513806, by rfl⟩ : syracuseStep 4685075 = 7027613) B7027613
theorem B3123383 : Blo 2081435 3123383 := bstep (se 1 (by rfl) ⟨2342537, by rfl⟩ : syracuseStep 3123383 = 4685075) B4685075
theorem B2082255 : Blo 2081435 2082255 := bstep (se 1 (by rfl) ⟨1561691, by rfl⟩ : syracuseStep 2082255 = 3123383) B3123383
theorem B3123389 : Blo 2081435 3123389 := bbase (se 3 (by rfl) ⟨585635, by rfl⟩ : syracuseStep 3123389 = 1171271) (by norm_num)
theorem B2082259 : Blo 2081435 2082259 := bstep (se 1 (by rfl) ⟨1561694, by rfl⟩ : syracuseStep 2082259 = 3123389) B3123389
theorem B4685093 : Blo 2081435 4685093 := bbase (se 4 (by rfl) ⟨439227, by rfl⟩ : syracuseStep 4685093 = 878455) (by norm_num)
theorem B3123395 : Blo 2081435 3123395 := bstep (se 1 (by rfl) ⟨2342546, by rfl⟩ : syracuseStep 3123395 = 4685093) B4685093
theorem B2082263 : Blo 2081435 2082263 := bstep (se 1 (by rfl) ⟨1561697, by rfl⟩ : syracuseStep 2082263 = 3123395) B3123395
theorem B5270741 : Blo 2081435 5270741 := bbase (se 7 (by rfl) ⟨61766, by rfl⟩ : syracuseStep 5270741 = 123533) (by norm_num)
theorem B3513827 : Blo 2081435 3513827 := bstep (se 1 (by rfl) ⟨2635370, by rfl⟩ : syracuseStep 3513827 = 5270741) B5270741
theorem B2342551 : Blo 2081435 2342551 := bstep (se 1 (by rfl) ⟨1756913, by rfl⟩ : syracuseStep 2342551 = 3513827) B3513827
theorem B3123401 : Blo 2081435 3123401 := bstep (se 2 (by rfl) ⟨1171275, by rfl⟩ : syracuseStep 3123401 = 2342551) B2342551
theorem B2082267 : Blo 2081435 2082267 := bstep (se 1 (by rfl) ⟨1561700, by rfl⟩ : syracuseStep 2082267 = 3123401) B3123401
theorem B7504645 : Blo 2081435 7504645 := bbase (se 4 (by rfl) ⟨703560, by rfl⟩ : syracuseStep 7504645 = 1407121) (by norm_num)
theorem B10006193 : Blo 2081435 10006193 := bstep (se 2 (by rfl) ⟨3752322, by rfl⟩ : syracuseStep 10006193 = 7504645) B7504645
theorem B6670795 : Blo 2081435 6670795 := bstep (se 1 (by rfl) ⟨5003096, by rfl⟩ : syracuseStep 6670795 = 10006193) B10006193
theorem B8894393 : Blo 2081435 8894393 := bstep (se 2 (by rfl) ⟨3335397, by rfl⟩ : syracuseStep 8894393 = 6670795) B6670795
theorem B5929595 : Blo 2081435 5929595 := bstep (se 1 (by rfl) ⟨4447196, by rfl⟩ : syracuseStep 5929595 = 8894393) B8894393
theorem B3953063 : Blo 2081435 3953063 := bstep (se 1 (by rfl) ⟨2964797, by rfl⟩ : syracuseStep 3953063 = 5929595) B5929595
theorem B10541501 : Blo 2081435 10541501 := bstep (se 3 (by rfl) ⟨1976531, by rfl⟩ : syracuseStep 10541501 = 3953063) B3953063
theorem B7027667 : Blo 2081435 7027667 := bstep (se 1 (by rfl) ⟨5270750, by rfl⟩ : syracuseStep 7027667 = 10541501) B10541501
theorem B4685111 : Blo 2081435 4685111 := bstep (se 1 (by rfl) ⟨3513833, by rfl⟩ : syracuseStep 4685111 = 7027667) B7027667
theorem B3123407 : Blo 2081435 3123407 := bstep (se 1 (by rfl) ⟨2342555, by rfl⟩ : syracuseStep 3123407 = 4685111) B4685111
theorem B2082271 : Blo 2081435 2082271 := bstep (se 1 (by rfl) ⟨1561703, by rfl⟩ : syracuseStep 2082271 = 3123407) B3123407
theorem B3123413 : Blo 2081435 3123413 := bbase (se 7 (by rfl) ⟨36602, by rfl⟩ : syracuseStep 3123413 = 73205) (by norm_num)
theorem B2082275 : Blo 2081435 2082275 := bstep (se 1 (by rfl) ⟨1561706, by rfl⟩ : syracuseStep 2082275 = 3123413) B3123413
theorem B5003117 : Blo 2081435 5003117 := bbase (se 3 (by rfl) ⟨938084, by rfl⟩ : syracuseStep 5003117 = 1876169) (by norm_num)
theorem B3335411 : Blo 2081435 3335411 := bstep (se 1 (by rfl) ⟨2501558, by rfl⟩ : syracuseStep 3335411 = 5003117) B5003117
theorem B2223607 : Blo 2081435 2223607 := bstep (se 1 (by rfl) ⟨1667705, by rfl⟩ : syracuseStep 2223607 = 3335411) B3335411
theorem B2964809 : Blo 2081435 2964809 := bstep (se 2 (by rfl) ⟨1111803, by rfl⟩ : syracuseStep 2964809 = 2223607) B2223607
theorem B7906157 : Blo 2081435 7906157 := bstep (se 3 (by rfl) ⟨1482404, by rfl⟩ : syracuseStep 7906157 = 2964809) B2964809
theorem B5270771 : Blo 2081435 5270771 := bstep (se 1 (by rfl) ⟨3953078, by rfl⟩ : syracuseStep 5270771 = 7906157) B7906157
theorem B3513847 : Blo 2081435 3513847 := bstep (se 1 (by rfl) ⟨2635385, by rfl⟩ : syracuseStep 3513847 = 5270771) B5270771
theorem B4685129 : Blo 2081435 4685129 := bstep (se 2 (by rfl) ⟨1756923, by rfl⟩ : syracuseStep 4685129 = 3513847) B3513847
theorem B3123419 : Blo 2081435 3123419 := bstep (se 1 (by rfl) ⟨2342564, by rfl⟩ : syracuseStep 3123419 = 4685129) B4685129
theorem B2082279 : Blo 2081435 2082279 := bstep (se 1 (by rfl) ⟨1561709, by rfl⟩ : syracuseStep 2082279 = 3123419) B3123419
theorem B2342569 : Blo 2081435 2342569 := bbase (se 2 (by rfl) ⟨878463, by rfl⟩ : syracuseStep 2342569 = 1756927) (by norm_num)
theorem B3123425 : Blo 2081435 3123425 := bstep (se 2 (by rfl) ⟨1171284, by rfl⟩ : syracuseStep 3123425 = 2342569) B2342569
theorem B2082283 : Blo 2081435 2082283 := bstep (se 1 (by rfl) ⟨1561712, by rfl⟩ : syracuseStep 2082283 = 3123425) B3123425
theorem B6761861 : Blo 2081435 6761861 := bbase (se 4 (by rfl) ⟨633924, by rfl⟩ : syracuseStep 6761861 = 1267849) (by norm_num)
theorem B4507907 : Blo 2081435 4507907 := bstep (se 1 (by rfl) ⟨3380930, by rfl⟩ : syracuseStep 4507907 = 6761861) B6761861
theorem B12021085 : Blo 2081435 12021085 := bstep (se 3 (by rfl) ⟨2253953, by rfl⟩ : syracuseStep 12021085 = 4507907) B4507907
theorem B16028113 : Blo 2081435 16028113 := bstep (se 2 (by rfl) ⟨6010542, by rfl⟩ : syracuseStep 16028113 = 12021085) B12021085
theorem B21370817 : Blo 2081435 21370817 := bstep (se 2 (by rfl) ⟨8014056, by rfl⟩ : syracuseStep 21370817 = 16028113) B16028113
theorem B56988845 : Blo 2081435 56988845 := bstep (se 3 (by rfl) ⟨10685408, by rfl⟩ : syracuseStep 56988845 = 21370817) B21370817
theorem B37992563 : Blo 2081435 37992563 := bstep (se 1 (by rfl) ⟨28494422, by rfl⟩ : syracuseStep 37992563 = 56988845) B56988845
theorem B25328375 : Blo 2081435 25328375 := bstep (se 1 (by rfl) ⟨18996281, by rfl⟩ : syracuseStep 25328375 = 37992563) B37992563
theorem B16885583 : Blo 2081435 16885583 := bstep (se 1 (by rfl) ⟨12664187, by rfl⟩ : syracuseStep 16885583 = 25328375) B25328375
theorem B11257055 : Blo 2081435 11257055 := bstep (se 1 (by rfl) ⟨8442791, by rfl⟩ : syracuseStep 11257055 = 16885583) B16885583
theorem B7504703 : Blo 2081435 7504703 := bstep (se 1 (by rfl) ⟨5628527, by rfl⟩ : syracuseStep 7504703 = 11257055) B11257055
theorem B5003135 : Blo 2081435 5003135 := bstep (se 1 (by rfl) ⟨3752351, by rfl⟩ : syracuseStep 5003135 = 7504703) B7504703
theorem B3335423 : Blo 2081435 3335423 := bstep (se 1 (by rfl) ⟨2501567, by rfl⟩ : syracuseStep 3335423 = 5003135) B5003135
theorem B8894461 : Blo 2081435 8894461 := bstep (se 3 (by rfl) ⟨1667711, by rfl⟩ : syracuseStep 8894461 = 3335423) B3335423
theorem B11859281 : Blo 2081435 11859281 := bstep (se 2 (by rfl) ⟨4447230, by rfl⟩ : syracuseStep 11859281 = 8894461) B8894461
theorem B7906187 : Blo 2081435 7906187 := bstep (se 1 (by rfl) ⟨5929640, by rfl⟩ : syracuseStep 7906187 = 11859281) B11859281
theorem B5270791 : Blo 2081435 5270791 := bstep (se 1 (by rfl) ⟨3953093, by rfl⟩ : syracuseStep 5270791 = 7906187) B7906187
theorem B7027721 : Blo 2081435 7027721 := bstep (se 2 (by rfl) ⟨2635395, by rfl⟩ : syracuseStep 7027721 = 5270791) B5270791
theorem B4685147 : Blo 2081435 4685147 := bstep (se 1 (by rfl) ⟨3513860, by rfl⟩ : syracuseStep 4685147 = 7027721) B7027721
theorem B3123431 : Blo 2081435 3123431 := bstep (se 1 (by rfl) ⟨2342573, by rfl⟩ : syracuseStep 3123431 = 4685147) B4685147
theorem B2082287 : Blo 2081435 2082287 := bstep (se 1 (by rfl) ⟨1561715, by rfl⟩ : syracuseStep 2082287 = 3123431) B3123431
theorem B3123437 : Blo 2081435 3123437 := bbase (se 3 (by rfl) ⟨585644, by rfl⟩ : syracuseStep 3123437 = 1171289) (by norm_num)
theorem B2082291 : Blo 2081435 2082291 := bstep (se 1 (by rfl) ⟨1561718, by rfl⟩ : syracuseStep 2082291 = 3123437) B3123437
theorem B4685165 : Blo 2081435 4685165 := bbase (se 3 (by rfl) ⟨878468, by rfl⟩ : syracuseStep 4685165 = 1756937) (by norm_num)
theorem B3123443 : Blo 2081435 3123443 := bstep (se 1 (by rfl) ⟨2342582, by rfl⟩ : syracuseStep 3123443 = 4685165) B4685165
theorem B2082295 : Blo 2081435 2082295 := bstep (se 1 (by rfl) ⟨1561721, by rfl⟩ : syracuseStep 2082295 = 3123443) B3123443
theorem B3953117 : Blo 2081435 3953117 := bbase (se 3 (by rfl) ⟨741209, by rfl⟩ : syracuseStep 3953117 = 1482419) (by norm_num)
theorem B2635411 : Blo 2081435 2635411 := bstep (se 1 (by rfl) ⟨1976558, by rfl⟩ : syracuseStep 2635411 = 3953117) B3953117
theorem B3513881 : Blo 2081435 3513881 := bstep (se 2 (by rfl) ⟨1317705, by rfl⟩ : syracuseStep 3513881 = 2635411) B2635411
theorem B2342587 : Blo 2081435 2342587 := bstep (se 1 (by rfl) ⟨1756940, by rfl⟩ : syracuseStep 2342587 = 3513881) B3513881
theorem B3123449 : Blo 2081435 3123449 := bstep (se 2 (by rfl) ⟨1171293, by rfl⟩ : syracuseStep 3123449 = 2342587) B2342587
theorem B2082299 : Blo 2081435 2082299 := bstep (se 1 (by rfl) ⟨1561724, by rfl⟩ : syracuseStep 2082299 = 3123449) B3123449
theorem B2374553 : Blo 2081435 2374553 := bbase (se 2 (by rfl) ⟨890457, by rfl⟩ : syracuseStep 2374553 = 1780915) (by norm_num)
theorem B6332141 : Blo 2081435 6332141 := bstep (se 3 (by rfl) ⟨1187276, by rfl⟩ : syracuseStep 6332141 = 2374553) B2374553
theorem B16885709 : Blo 2081435 16885709 := bstep (se 3 (by rfl) ⟨3166070, by rfl⟩ : syracuseStep 16885709 = 6332141) B6332141
theorem B11257139 : Blo 2081435 11257139 := bstep (se 1 (by rfl) ⟨8442854, by rfl⟩ : syracuseStep 11257139 = 16885709) B16885709
theorem B7504759 : Blo 2081435 7504759 := bstep (se 1 (by rfl) ⟨5628569, by rfl⟩ : syracuseStep 7504759 = 11257139) B11257139
theorem B10006345 : Blo 2081435 10006345 := bstep (se 2 (by rfl) ⟨3752379, by rfl⟩ : syracuseStep 10006345 = 7504759) B7504759
theorem B53367173 : Blo 2081435 53367173 := bstep (se 4 (by rfl) ⟨5003172, by rfl⟩ : syracuseStep 53367173 = 10006345) B10006345
theorem B35578115 : Blo 2081435 35578115 := bstep (se 1 (by rfl) ⟨26683586, by rfl⟩ : syracuseStep 35578115 = 53367173) B53367173
theorem B23718743 : Blo 2081435 23718743 := bstep (se 1 (by rfl) ⟨17789057, by rfl⟩ : syracuseStep 23718743 = 35578115) B35578115
theorem B15812495 : Blo 2081435 15812495 := bstep (se 1 (by rfl) ⟨11859371, by rfl⟩ : syracuseStep 15812495 = 23718743) B23718743
theorem B10541663 : Blo 2081435 10541663 := bstep (se 1 (by rfl) ⟨7906247, by rfl⟩ : syracuseStep 10541663 = 15812495) B15812495
theorem B7027775 : Blo 2081435 7027775 := bstep (se 1 (by rfl) ⟨5270831, by rfl⟩ : syracuseStep 7027775 = 10541663) B10541663
theorem B4685183 : Blo 2081435 4685183 := bstep (se 1 (by rfl) ⟨3513887, by rfl⟩ : syracuseStep 4685183 = 7027775) B7027775
theorem B3123455 : Blo 2081435 3123455 := bstep (se 1 (by rfl) ⟨2342591, by rfl⟩ : syracuseStep 3123455 = 4685183) B4685183
theorem B2082303 : Blo 2081435 2082303 := bstep (se 1 (by rfl) ⟨1561727, by rfl⟩ : syracuseStep 2082303 = 3123455) B3123455
theorem B3123461 : Blo 2081435 3123461 := bbase (se 4 (by rfl) ⟨292824, by rfl⟩ : syracuseStep 3123461 = 585649) (by norm_num)
theorem B2082307 : Blo 2081435 2082307 := bstep (se 1 (by rfl) ⟨1561730, by rfl⟩ : syracuseStep 2082307 = 3123461) B3123461
theorem B3513901 : Blo 2081435 3513901 := bbase (se 3 (by rfl) ⟨658856, by rfl⟩ : syracuseStep 3513901 = 1317713) (by norm_num)
theorem B4685201 : Blo 2081435 4685201 := bstep (se 2 (by rfl) ⟨1756950, by rfl⟩ : syracuseStep 4685201 = 3513901) B3513901
theorem B3123467 : Blo 2081435 3123467 := bstep (se 1 (by rfl) ⟨2342600, by rfl⟩ : syracuseStep 3123467 = 4685201) B4685201
theorem B2082311 : Blo 2081435 2082311 := bstep (se 1 (by rfl) ⟨1561733, by rfl⟩ : syracuseStep 2082311 = 3123467) B3123467
theorem B2342605 : Blo 2081435 2342605 := bbase (se 3 (by rfl) ⟨439238, by rfl⟩ : syracuseStep 2342605 = 878477) (by norm_num)
theorem B3123473 : Blo 2081435 3123473 := bstep (se 2 (by rfl) ⟨1171302, by rfl⟩ : syracuseStep 3123473 = 2342605) B2342605
theorem B2082315 : Blo 2081435 2082315 := bstep (se 1 (by rfl) ⟨1561736, by rfl⟩ : syracuseStep 2082315 = 3123473) B3123473
theorem B7027829 : Blo 2081435 7027829 := bbase (se 5 (by rfl) ⟨329429, by rfl⟩ : syracuseStep 7027829 = 658859) (by norm_num)
theorem B4685219 : Blo 2081435 4685219 := bstep (se 1 (by rfl) ⟨3513914, by rfl⟩ : syracuseStep 4685219 = 7027829) B7027829
theorem B3123479 : Blo 2081435 3123479 := bstep (se 1 (by rfl) ⟨2342609, by rfl⟩ : syracuseStep 3123479 = 4685219) B4685219
theorem B2082319 : Blo 2081435 2082319 := bstep (se 1 (by rfl) ⟨1561739, by rfl⟩ : syracuseStep 2082319 = 3123479) B3123479
theorem B3123485 : Blo 2081435 3123485 := bbase (se 3 (by rfl) ⟨585653, by rfl⟩ : syracuseStep 3123485 = 1171307) (by norm_num)
theorem B2082323 : Blo 2081435 2082323 := bstep (se 1 (by rfl) ⟨1561742, by rfl⟩ : syracuseStep 2082323 = 3123485) B3123485
theorem B4685237 : Blo 2081435 4685237 := bbase (se 5 (by rfl) ⟨219620, by rfl⟩ : syracuseStep 4685237 = 439241) (by norm_num)
theorem B3123491 : Blo 2081435 3123491 := bstep (se 1 (by rfl) ⟨2342618, by rfl⟩ : syracuseStep 3123491 = 4685237) B4685237
theorem B2082327 : Blo 2081435 2082327 := bstep (se 1 (by rfl) ⟨1561745, by rfl⟩ : syracuseStep 2082327 = 3123491) B3123491
theorem B4447325 : Blo 2081435 4447325 := bbase (se 3 (by rfl) ⟨833873, by rfl⟩ : syracuseStep 4447325 = 1667747) (by norm_num)
theorem B11859533 : Blo 2081435 11859533 := bstep (se 3 (by rfl) ⟨2223662, by rfl⟩ : syracuseStep 11859533 = 4447325) B4447325
theorem B7906355 : Blo 2081435 7906355 := bstep (se 1 (by rfl) ⟨5929766, by rfl⟩ : syracuseStep 7906355 = 11859533) B11859533
theorem B5270903 : Blo 2081435 5270903 := bstep (se 1 (by rfl) ⟨3953177, by rfl⟩ : syracuseStep 5270903 = 7906355) B7906355
theorem B3513935 : Blo 2081435 3513935 := bstep (se 1 (by rfl) ⟨2635451, by rfl⟩ : syracuseStep 3513935 = 5270903) B5270903
theorem B2342623 : Blo 2081435 2342623 := bstep (se 1 (by rfl) ⟨1756967, by rfl⟩ : syracuseStep 2342623 = 3513935) B3513935
theorem B3123497 : Blo 2081435 3123497 := bstep (se 2 (by rfl) ⟨1171311, by rfl⟩ : syracuseStep 3123497 = 2342623) B2342623
theorem B2082331 : Blo 2081435 2082331 := bstep (se 1 (by rfl) ⟨1561748, by rfl⟩ : syracuseStep 2082331 = 3123497) B3123497
theorem B4447333 : Blo 2081435 4447333 := bbase (se 4 (by rfl) ⟨416937, by rfl⟩ : syracuseStep 4447333 = 833875) (by norm_num)
theorem B5929777 : Blo 2081435 5929777 := bstep (se 2 (by rfl) ⟨2223666, by rfl⟩ : syracuseStep 5929777 = 4447333) B4447333
theorem B7906369 : Blo 2081435 7906369 := bstep (se 2 (by rfl) ⟨2964888, by rfl⟩ : syracuseStep 7906369 = 5929777) B5929777
theorem B10541825 : Blo 2081435 10541825 := bstep (se 2 (by rfl) ⟨3953184, by rfl⟩ : syracuseStep 10541825 = 7906369) B7906369
theorem B7027883 : Blo 2081435 7027883 := bstep (se 1 (by rfl) ⟨5270912, by rfl⟩ : syracuseStep 7027883 = 10541825) B10541825
theorem B4685255 : Blo 2081435 4685255 := bstep (se 1 (by rfl) ⟨3513941, by rfl⟩ : syracuseStep 4685255 = 7027883) B7027883
theorem B3123503 : Blo 2081435 3123503 := bstep (se 1 (by rfl) ⟨2342627, by rfl⟩ : syracuseStep 3123503 = 4685255) B4685255
theorem B2082335 : Blo 2081435 2082335 := bstep (se 1 (by rfl) ⟨1561751, by rfl⟩ : syracuseStep 2082335 = 3123503) B3123503
theorem B3123509 : Blo 2081435 3123509 := bbase (se 5 (by rfl) ⟨146414, by rfl⟩ : syracuseStep 3123509 = 292829) (by norm_num)
theorem B2082339 : Blo 2081435 2082339 := bstep (se 1 (by rfl) ⟨1561754, by rfl⟩ : syracuseStep 2082339 = 3123509) B3123509
theorem B5270933 : Blo 2081435 5270933 := bbase (se 6 (by rfl) ⟨123537, by rfl⟩ : syracuseStep 5270933 = 247075) (by norm_num)
theorem B3513955 : Blo 2081435 3513955 := bstep (se 1 (by rfl) ⟨2635466, by rfl⟩ : syracuseStep 3513955 = 5270933) B5270933
theorem B4685273 : Blo 2081435 4685273 := bstep (se 2 (by rfl) ⟨1756977, by rfl⟩ : syracuseStep 4685273 = 3513955) B3513955
theorem B3123515 : Blo 2081435 3123515 := bstep (se 1 (by rfl) ⟨2342636, by rfl⟩ : syracuseStep 3123515 = 4685273) B4685273
theorem B2082343 : Blo 2081435 2082343 := bstep (se 1 (by rfl) ⟨1561757, by rfl⟩ : syracuseStep 2082343 = 3123515) B3123515
theorem B2342641 : Blo 2081435 2342641 := bbase (se 2 (by rfl) ⟨878490, by rfl⟩ : syracuseStep 2342641 = 1756981) (by norm_num)
theorem B3123521 : Blo 2081435 3123521 := bstep (se 2 (by rfl) ⟨1171320, by rfl⟩ : syracuseStep 3123521 = 2342641) B2342641
theorem B2082347 : Blo 2081435 2082347 := bstep (se 1 (by rfl) ⟨1561760, by rfl⟩ : syracuseStep 2082347 = 3123521) B3123521
theorem B30019733 : Blo 2081435 30019733 := bbase (se 6 (by rfl) ⟨703587, by rfl⟩ : syracuseStep 30019733 = 1407175) (by norm_num)
theorem B20013155 : Blo 2081435 20013155 := bstep (se 1 (by rfl) ⟨15009866, by rfl⟩ : syracuseStep 20013155 = 30019733) B30019733
theorem B13342103 : Blo 2081435 13342103 := bstep (se 1 (by rfl) ⟨10006577, by rfl⟩ : syracuseStep 13342103 = 20013155) B20013155
theorem B8894735 : Blo 2081435 8894735 := bstep (se 1 (by rfl) ⟨6671051, by rfl⟩ : syracuseStep 8894735 = 13342103) B13342103
theorem B5929823 : Blo 2081435 5929823 := bstep (se 1 (by rfl) ⟨4447367, by rfl⟩ : syracuseStep 5929823 = 8894735) B8894735
theorem B3953215 : Blo 2081435 3953215 := bstep (se 1 (by rfl) ⟨2964911, by rfl⟩ : syracuseStep 3953215 = 5929823) B5929823
theorem B5270953 : Blo 2081435 5270953 := bstep (se 2 (by rfl) ⟨1976607, by rfl⟩ : syracuseStep 5270953 = 3953215) B3953215
theorem B7027937 : Blo 2081435 7027937 := bstep (se 2 (by rfl) ⟨2635476, by rfl⟩ : syracuseStep 7027937 = 5270953) B5270953
theorem B4685291 : Blo 2081435 4685291 := bstep (se 1 (by rfl) ⟨3513968, by rfl⟩ : syracuseStep 4685291 = 7027937) B7027937
theorem B3123527 : Blo 2081435 3123527 := bstep (se 1 (by rfl) ⟨2342645, by rfl⟩ : syracuseStep 3123527 = 4685291) B4685291
theorem B2082351 : Blo 2081435 2082351 := bstep (se 1 (by rfl) ⟨1561763, by rfl⟩ : syracuseStep 2082351 = 3123527) B3123527
theorem B3123533 : Blo 2081435 3123533 := bbase (se 3 (by rfl) ⟨585662, by rfl⟩ : syracuseStep 3123533 = 1171325) (by norm_num)
theorem B2082355 : Blo 2081435 2082355 := bstep (se 1 (by rfl) ⟨1561766, by rfl⟩ : syracuseStep 2082355 = 3123533) B3123533
theorem B4685309 : Blo 2081435 4685309 := bbase (se 3 (by rfl) ⟨878495, by rfl⟩ : syracuseStep 4685309 = 1756991) (by norm_num)
theorem B3123539 : Blo 2081435 3123539 := bstep (se 1 (by rfl) ⟨2342654, by rfl⟩ : syracuseStep 3123539 = 4685309) B4685309
theorem B2082359 : Blo 2081435 2082359 := bstep (se 1 (by rfl) ⟨1561769, by rfl⟩ : syracuseStep 2082359 = 3123539) B3123539
theorem B3513989 : Blo 2081435 3513989 := bbase (se 4 (by rfl) ⟨329436, by rfl⟩ : syracuseStep 3513989 = 658873) (by norm_num)
theorem B2342659 : Blo 2081435 2342659 := bstep (se 1 (by rfl) ⟨1756994, by rfl⟩ : syracuseStep 2342659 = 3513989) B3513989
theorem B3123545 : Blo 2081435 3123545 := bstep (se 2 (by rfl) ⟨1171329, by rfl⟩ : syracuseStep 3123545 = 2342659) B2342659
theorem B2082363 : Blo 2081435 2082363 := bstep (se 1 (by rfl) ⟨1561772, by rfl⟩ : syracuseStep 2082363 = 3123545) B3123545
theorem B15812981 : Blo 2081435 15812981 := bbase (se 5 (by rfl) ⟨741233, by rfl⟩ : syracuseStep 15812981 = 1482467) (by norm_num)
theorem B10541987 : Blo 2081435 10541987 := bstep (se 1 (by rfl) ⟨7906490, by rfl⟩ : syracuseStep 10541987 = 15812981) B15812981
theorem B7027991 : Blo 2081435 7027991 := bstep (se 1 (by rfl) ⟨5270993, by rfl⟩ : syracuseStep 7027991 = 10541987) B10541987
theorem B4685327 : Blo 2081435 4685327 := bstep (se 1 (by rfl) ⟨3513995, by rfl⟩ : syracuseStep 4685327 = 7027991) B7027991
theorem B3123551 : Blo 2081435 3123551 := bstep (se 1 (by rfl) ⟨2342663, by rfl⟩ : syracuseStep 3123551 = 4685327) B4685327
theorem B2082367 : Blo 2081435 2082367 := bstep (se 1 (by rfl) ⟨1561775, by rfl⟩ : syracuseStep 2082367 = 3123551) B3123551
theorem B3123557 : Blo 2081435 3123557 := bbase (se 4 (by rfl) ⟨292833, by rfl⟩ : syracuseStep 3123557 = 585667) (by norm_num)
theorem B2082371 : Blo 2081435 2082371 := bstep (se 1 (by rfl) ⟨1561778, by rfl⟩ : syracuseStep 2082371 = 3123557) B3123557
theorem B3953261 : Blo 2081435 3953261 := bbase (se 3 (by rfl) ⟨741236, by rfl⟩ : syracuseStep 3953261 = 1482473) (by norm_num)
theorem B2635507 : Blo 2081435 2635507 := bstep (se 1 (by rfl) ⟨1976630, by rfl⟩ : syracuseStep 2635507 = 3953261) B3953261
theorem B3514009 : Blo 2081435 3514009 := bstep (se 2 (by rfl) ⟨1317753, by rfl⟩ : syracuseStep 3514009 = 2635507) B2635507
theorem B4685345 : Blo 2081435 4685345 := bstep (se 2 (by rfl) ⟨1757004, by rfl⟩ : syracuseStep 4685345 = 3514009) B3514009
theorem B3123563 : Blo 2081435 3123563 := bstep (se 1 (by rfl) ⟨2342672, by rfl⟩ : syracuseStep 3123563 = 4685345) B4685345
theorem B2082375 : Blo 2081435 2082375 := bstep (se 1 (by rfl) ⟨1561781, by rfl⟩ : syracuseStep 2082375 = 3123563) B3123563
theorem B2342677 : Blo 2081435 2342677 := bbase (se 6 (by rfl) ⟨54906, by rfl⟩ : syracuseStep 2342677 = 109813) (by norm_num)
theorem B3123569 : Blo 2081435 3123569 := bstep (se 2 (by rfl) ⟨1171338, by rfl⟩ : syracuseStep 3123569 = 2342677) B2342677
theorem B2082379 : Blo 2081435 2082379 := bstep (se 1 (by rfl) ⟨1561784, by rfl⟩ : syracuseStep 2082379 = 3123569) B3123569
theorem B2635517 : Blo 2081435 2635517 := bbase (se 3 (by rfl) ⟨494159, by rfl⟩ : syracuseStep 2635517 = 988319) (by norm_num)
theorem B7028045 : Blo 2081435 7028045 := bstep (se 3 (by rfl) ⟨1317758, by rfl⟩ : syracuseStep 7028045 = 2635517) B2635517
theorem B4685363 : Blo 2081435 4685363 := bstep (se 1 (by rfl) ⟨3514022, by rfl⟩ : syracuseStep 4685363 = 7028045) B7028045
theorem B3123575 : Blo 2081435 3123575 := bstep (se 1 (by rfl) ⟨2342681, by rfl⟩ : syracuseStep 3123575 = 4685363) B4685363
theorem B2082383 : Blo 2081435 2082383 := bstep (se 1 (by rfl) ⟨1561787, by rfl⟩ : syracuseStep 2082383 = 3123575) B3123575
theorem B3123581 : Blo 2081435 3123581 := bbase (se 3 (by rfl) ⟨585671, by rfl⟩ : syracuseStep 3123581 = 1171343) (by norm_num)
theorem B2082387 : Blo 2081435 2082387 := bstep (se 1 (by rfl) ⟨1561790, by rfl⟩ : syracuseStep 2082387 = 3123581) B3123581
theorem B4685381 : Blo 2081435 4685381 := bbase (se 4 (by rfl) ⟨439254, by rfl⟩ : syracuseStep 4685381 = 878509) (by norm_num)
theorem B3123587 : Blo 2081435 3123587 := bstep (se 1 (by rfl) ⟨2342690, by rfl⟩ : syracuseStep 3123587 = 4685381) B4685381
theorem B2082391 : Blo 2081435 2082391 := bstep (se 1 (by rfl) ⟨1561793, by rfl⟩ : syracuseStep 2082391 = 3123587) B3123587
theorem B3335597 : Blo 2081435 3335597 := bbase (se 3 (by rfl) ⟨625424, by rfl⟩ : syracuseStep 3335597 = 1250849) (by norm_num)
theorem B2223731 : Blo 2081435 2223731 := bstep (se 1 (by rfl) ⟨1667798, by rfl⟩ : syracuseStep 2223731 = 3335597) B3335597
theorem B5929949 : Blo 2081435 5929949 := bstep (se 3 (by rfl) ⟨1111865, by rfl⟩ : syracuseStep 5929949 = 2223731) B2223731
theorem B3953299 : Blo 2081435 3953299 := bstep (se 1 (by rfl) ⟨2964974, by rfl⟩ : syracuseStep 3953299 = 5929949) B5929949
theorem B5271065 : Blo 2081435 5271065 := bstep (se 2 (by rfl) ⟨1976649, by rfl⟩ : syracuseStep 5271065 = 3953299) B3953299
theorem B3514043 : Blo 2081435 3514043 := bstep (se 1 (by rfl) ⟨2635532, by rfl⟩ : syracuseStep 3514043 = 5271065) B5271065
theorem B2342695 : Blo 2081435 2342695 := bstep (se 1 (by rfl) ⟨1757021, by rfl⟩ : syracuseStep 2342695 = 3514043) B3514043
theorem B3123593 : Blo 2081435 3123593 := bstep (se 2 (by rfl) ⟨1171347, by rfl⟩ : syracuseStep 3123593 = 2342695) B2342695
theorem B2082395 : Blo 2081435 2082395 := bstep (se 1 (by rfl) ⟨1561796, by rfl⟩ : syracuseStep 2082395 = 3123593) B3123593
theorem B10542149 : Blo 2081435 10542149 := bbase (se 4 (by rfl) ⟨988326, by rfl⟩ : syracuseStep 10542149 = 1976653) (by norm_num)
theorem B7028099 : Blo 2081435 7028099 := bstep (se 1 (by rfl) ⟨5271074, by rfl⟩ : syracuseStep 7028099 = 10542149) B10542149
theorem B4685399 : Blo 2081435 4685399 := bstep (se 1 (by rfl) ⟨3514049, by rfl⟩ : syracuseStep 4685399 = 7028099) B7028099
theorem B3123599 : Blo 2081435 3123599 := bstep (se 1 (by rfl) ⟨2342699, by rfl⟩ : syracuseStep 3123599 = 4685399) B4685399
theorem B2082399 : Blo 2081435 2082399 := bstep (se 1 (by rfl) ⟨1561799, by rfl⟩ : syracuseStep 2082399 = 3123599) B3123599
theorem B3123605 : Blo 2081435 3123605 := bbase (se 6 (by rfl) ⟨73209, by rfl⟩ : syracuseStep 3123605 = 146419) (by norm_num)
theorem B2082403 : Blo 2081435 2082403 := bstep (se 1 (by rfl) ⟨1561802, by rfl⟩ : syracuseStep 2082403 = 3123605) B3123605
theorem B4337621 : Blo 2081435 4337621 := bbase (se 7 (by rfl) ⟨50831, by rfl⟩ : syracuseStep 4337621 = 101663) (by norm_num)
theorem B2891747 : Blo 2081435 2891747 := bstep (se 1 (by rfl) ⟨2168810, by rfl⟩ : syracuseStep 2891747 = 4337621) B4337621
theorem B7711325 : Blo 2081435 7711325 := bstep (se 3 (by rfl) ⟨1445873, by rfl⟩ : syracuseStep 7711325 = 2891747) B2891747
theorem B5140883 : Blo 2081435 5140883 := bstep (se 1 (by rfl) ⟨3855662, by rfl⟩ : syracuseStep 5140883 = 7711325) B7711325
theorem B3427255 : Blo 2081435 3427255 := bstep (se 1 (by rfl) ⟨2570441, by rfl⟩ : syracuseStep 3427255 = 5140883) B5140883
theorem B18278693 : Blo 2081435 18278693 := bstep (se 4 (by rfl) ⟨1713627, by rfl⟩ : syracuseStep 18278693 = 3427255) B3427255
theorem B12185795 : Blo 2081435 12185795 := bstep (se 1 (by rfl) ⟨9139346, by rfl⟩ : syracuseStep 12185795 = 18278693) B18278693
theorem B8123863 : Blo 2081435 8123863 := bstep (se 1 (by rfl) ⟨6092897, by rfl⟩ : syracuseStep 8123863 = 12185795) B12185795
theorem B10831817 : Blo 2081435 10831817 := bstep (se 2 (by rfl) ⟨4061931, by rfl⟩ : syracuseStep 10831817 = 8123863) B8123863
theorem B28884845 : Blo 2081435 28884845 := bstep (se 3 (by rfl) ⟨5415908, by rfl⟩ : syracuseStep 28884845 = 10831817) B10831817
theorem B19256563 : Blo 2081435 19256563 := bstep (se 1 (by rfl) ⟨14442422, by rfl⟩ : syracuseStep 19256563 = 28884845) B28884845
theorem B25675417 : Blo 2081435 25675417 := bstep (se 2 (by rfl) ⟨9628281, by rfl⟩ : syracuseStep 25675417 = 19256563) B19256563
theorem B34233889 : Blo 2081435 34233889 := bstep (se 2 (by rfl) ⟨12837708, by rfl⟩ : syracuseStep 34233889 = 25675417) B25675417
theorem B45645185 : Blo 2081435 45645185 := bstep (se 2 (by rfl) ⟨17116944, by rfl⟩ : syracuseStep 45645185 = 34233889) B34233889
theorem B30430123 : Blo 2081435 30430123 := bstep (se 1 (by rfl) ⟨22822592, by rfl⟩ : syracuseStep 30430123 = 45645185) B45645185
theorem B162293989 : Blo 2081435 162293989 := bstep (se 4 (by rfl) ⟨15215061, by rfl⟩ : syracuseStep 162293989 = 30430123) B30430123
theorem B216391985 : Blo 2081435 216391985 := bstep (se 2 (by rfl) ⟨81146994, by rfl⟩ : syracuseStep 216391985 = 162293989) B162293989
theorem B144261323 : Blo 2081435 144261323 := bstep (se 1 (by rfl) ⟨108195992, by rfl⟩ : syracuseStep 144261323 = 216391985) B216391985
theorem B96174215 : Blo 2081435 96174215 := bstep (se 1 (by rfl) ⟨72130661, by rfl⟩ : syracuseStep 96174215 = 144261323) B144261323
theorem B64116143 : Blo 2081435 64116143 := bstep (se 1 (by rfl) ⟨48087107, by rfl⟩ : syracuseStep 64116143 = 96174215) B96174215
theorem B42744095 : Blo 2081435 42744095 := bstep (se 1 (by rfl) ⟨32058071, by rfl⟩ : syracuseStep 42744095 = 64116143) B64116143
theorem B28496063 : Blo 2081435 28496063 := bstep (se 1 (by rfl) ⟨21372047, by rfl⟩ : syracuseStep 28496063 = 42744095) B42744095
theorem B75989501 : Blo 2081435 75989501 := bstep (se 3 (by rfl) ⟨14248031, by rfl⟩ : syracuseStep 75989501 = 28496063) B28496063
theorem B50659667 : Blo 2081435 50659667 := bstep (se 1 (by rfl) ⟨37994750, by rfl⟩ : syracuseStep 50659667 = 75989501) B75989501
theorem B33773111 : Blo 2081435 33773111 := bstep (se 1 (by rfl) ⟨25329833, by rfl⟩ : syracuseStep 33773111 = 50659667) B50659667
theorem B22515407 : Blo 2081435 22515407 := bstep (se 1 (by rfl) ⟨16886555, by rfl⟩ : syracuseStep 22515407 = 33773111) B33773111
theorem B15010271 : Blo 2081435 15010271 := bstep (se 1 (by rfl) ⟨11257703, by rfl⟩ : syracuseStep 15010271 = 22515407) B22515407
theorem B10006847 : Blo 2081435 10006847 := bstep (se 1 (by rfl) ⟨7505135, by rfl⟩ : syracuseStep 10006847 = 15010271) B15010271
theorem B6671231 : Blo 2081435 6671231 := bstep (se 1 (by rfl) ⟨5003423, by rfl⟩ : syracuseStep 6671231 = 10006847) B10006847
theorem B4447487 : Blo 2081435 4447487 := bstep (se 1 (by rfl) ⟨3335615, by rfl⟩ : syracuseStep 4447487 = 6671231) B6671231
theorem B11859965 : Blo 2081435 11859965 := bstep (se 3 (by rfl) ⟨2223743, by rfl⟩ : syracuseStep 11859965 = 4447487) B4447487
theorem B7906643 : Blo 2081435 7906643 := bstep (se 1 (by rfl) ⟨5929982, by rfl⟩ : syracuseStep 7906643 = 11859965) B11859965
theorem B5271095 : Blo 2081435 5271095 := bstep (se 1 (by rfl) ⟨3953321, by rfl⟩ : syracuseStep 5271095 = 7906643) B7906643
theorem B3514063 : Blo 2081435 3514063 := bstep (se 1 (by rfl) ⟨2635547, by rfl⟩ : syracuseStep 3514063 = 5271095) B5271095
theorem B4685417 : Blo 2081435 4685417 := bstep (se 2 (by rfl) ⟨1757031, by rfl⟩ : syracuseStep 4685417 = 3514063) B3514063
theorem B3123611 : Blo 2081435 3123611 := bstep (se 1 (by rfl) ⟨2342708, by rfl⟩ : syracuseStep 3123611 = 4685417) B4685417
theorem B2082407 : Blo 2081435 2082407 := bstep (se 1 (by rfl) ⟨1561805, by rfl⟩ : syracuseStep 2082407 = 3123611) B3123611
theorem B2342713 : Blo 2081435 2342713 := bbase (se 2 (by rfl) ⟨878517, by rfl⟩ : syracuseStep 2342713 = 1757035) (by norm_num)
theorem B3123617 : Blo 2081435 3123617 := bstep (se 2 (by rfl) ⟨1171356, by rfl⟩ : syracuseStep 3123617 = 2342713) B2342713
theorem B2082411 : Blo 2081435 2082411 := bstep (se 1 (by rfl) ⟨1561808, by rfl⟩ : syracuseStep 2082411 = 3123617) B3123617
theorem B5930005 : Blo 2081435 5930005 := bbase (se 6 (by rfl) ⟨138984, by rfl⟩ : syracuseStep 5930005 = 277969) (by norm_num)
theorem B7906673 : Blo 2081435 7906673 := bstep (se 2 (by rfl) ⟨2965002, by rfl⟩ : syracuseStep 7906673 = 5930005) B5930005
theorem B5271115 : Blo 2081435 5271115 := bstep (se 1 (by rfl) ⟨3953336, by rfl⟩ : syracuseStep 5271115 = 7906673) B7906673
theorem B7028153 : Blo 2081435 7028153 := bstep (se 2 (by rfl) ⟨2635557, by rfl⟩ : syracuseStep 7028153 = 5271115) B5271115
theorem B4685435 : Blo 2081435 4685435 := bstep (se 1 (by rfl) ⟨3514076, by rfl⟩ : syracuseStep 4685435 = 7028153) B7028153
theorem B3123623 : Blo 2081435 3123623 := bstep (se 1 (by rfl) ⟨2342717, by rfl⟩ : syracuseStep 3123623 = 4685435) B4685435
theorem B2082415 : Blo 2081435 2082415 := bstep (se 1 (by rfl) ⟨1561811, by rfl⟩ : syracuseStep 2082415 = 3123623) B3123623
theorem B3123629 : Blo 2081435 3123629 := bbase (se 3 (by rfl) ⟨585680, by rfl⟩ : syracuseStep 3123629 = 1171361) (by norm_num)
theorem B2082419 : Blo 2081435 2082419 := bstep (se 1 (by rfl) ⟨1561814, by rfl⟩ : syracuseStep 2082419 = 3123629) B3123629
theorem B4685453 : Blo 2081435 4685453 := bbase (se 3 (by rfl) ⟨878522, by rfl⟩ : syracuseStep 4685453 = 1757045) (by norm_num)
theorem B3123635 : Blo 2081435 3123635 := bstep (se 1 (by rfl) ⟨2342726, by rfl⟩ : syracuseStep 3123635 = 4685453) B4685453
theorem B2082423 : Blo 2081435 2082423 := bstep (se 1 (by rfl) ⟨1561817, by rfl⟩ : syracuseStep 2082423 = 3123635) B3123635
theorem B2635573 : Blo 2081435 2635573 := bbase (se 5 (by rfl) ⟨123542, by rfl⟩ : syracuseStep 2635573 = 247085) (by norm_num)
theorem B3514097 : Blo 2081435 3514097 := bstep (se 2 (by rfl) ⟨1317786, by rfl⟩ : syracuseStep 3514097 = 2635573) B2635573
theorem B2342731 : Blo 2081435 2342731 := bstep (se 1 (by rfl) ⟨1757048, by rfl⟩ : syracuseStep 2342731 = 3514097) B3514097
theorem B3123641 : Blo 2081435 3123641 := bstep (se 2 (by rfl) ⟨1171365, by rfl⟩ : syracuseStep 3123641 = 2342731) B2342731
theorem B2082427 : Blo 2081435 2082427 := bstep (se 1 (by rfl) ⟨1561820, by rfl⟩ : syracuseStep 2082427 = 3123641) B3123641
theorem B2671537 : Blo 2081435 2671537 := bbase (se 2 (by rfl) ⟨1001826, by rfl⟩ : syracuseStep 2671537 = 2003653) (by norm_num)
theorem B3562049 : Blo 2081435 3562049 := bstep (se 2 (by rfl) ⟨1335768, by rfl⟩ : syracuseStep 3562049 = 2671537) B2671537
theorem B2374699 : Blo 2081435 2374699 := bstep (se 1 (by rfl) ⟨1781024, by rfl⟩ : syracuseStep 2374699 = 3562049) B3562049
theorem B3166265 : Blo 2081435 3166265 := bstep (se 2 (by rfl) ⟨1187349, by rfl⟩ : syracuseStep 3166265 = 2374699) B2374699
theorem B8443373 : Blo 2081435 8443373 := bstep (se 3 (by rfl) ⟨1583132, by rfl⟩ : syracuseStep 8443373 = 3166265) B3166265
theorem B22515661 : Blo 2081435 22515661 := bstep (se 3 (by rfl) ⟨4221686, by rfl⟩ : syracuseStep 22515661 = 8443373) B8443373
theorem B30020881 : Blo 2081435 30020881 := bstep (se 2 (by rfl) ⟨11257830, by rfl⟩ : syracuseStep 30020881 = 22515661) B22515661
theorem B40027841 : Blo 2081435 40027841 := bstep (se 2 (by rfl) ⟨15010440, by rfl⟩ : syracuseStep 40027841 = 30020881) B30020881
theorem B26685227 : Blo 2081435 26685227 := bstep (se 1 (by rfl) ⟨20013920, by rfl⟩ : syracuseStep 26685227 = 40027841) B40027841
theorem B17790151 : Blo 2081435 17790151 := bstep (se 1 (by rfl) ⟨13342613, by rfl⟩ : syracuseStep 17790151 = 26685227) B26685227
theorem B23720201 : Blo 2081435 23720201 := bstep (se 2 (by rfl) ⟨8895075, by rfl⟩ : syracuseStep 23720201 = 17790151) B17790151
theorem B15813467 : Blo 2081435 15813467 := bstep (se 1 (by rfl) ⟨11860100, by rfl⟩ : syracuseStep 15813467 = 23720201) B23720201
theorem B10542311 : Blo 2081435 10542311 := bstep (se 1 (by rfl) ⟨7906733, by rfl⟩ : syracuseStep 10542311 = 15813467) B15813467
theorem B7028207 : Blo 2081435 7028207 := bstep (se 1 (by rfl) ⟨5271155, by rfl⟩ : syracuseStep 7028207 = 10542311) B10542311
theorem B4685471 : Blo 2081435 4685471 := bstep (se 1 (by rfl) ⟨3514103, by rfl⟩ : syracuseStep 4685471 = 7028207) B7028207
theorem B3123647 : Blo 2081435 3123647 := bstep (se 1 (by rfl) ⟨2342735, by rfl⟩ : syracuseStep 3123647 = 4685471) B4685471
theorem B2082431 : Blo 2081435 2082431 := bstep (se 1 (by rfl) ⟨1561823, by rfl⟩ : syracuseStep 2082431 = 3123647) B3123647
theorem B3123653 : Blo 2081435 3123653 := bbase (se 4 (by rfl) ⟨292842, by rfl⟩ : syracuseStep 3123653 = 585685) (by norm_num)
theorem B2082435 : Blo 2081435 2082435 := bstep (se 1 (by rfl) ⟨1561826, by rfl⟩ : syracuseStep 2082435 = 3123653) B3123653
theorem B3514117 : Blo 2081435 3514117 := bbase (se 4 (by rfl) ⟨329448, by rfl⟩ : syracuseStep 3514117 = 658897) (by norm_num)
theorem B4685489 : Blo 2081435 4685489 := bstep (se 2 (by rfl) ⟨1757058, by rfl⟩ : syracuseStep 4685489 = 3514117) B3514117
theorem B3123659 : Blo 2081435 3123659 := bstep (se 1 (by rfl) ⟨2342744, by rfl⟩ : syracuseStep 3123659 = 4685489) B4685489
theorem B2082439 : Blo 2081435 2082439 := bstep (se 1 (by rfl) ⟨1561829, by rfl⟩ : syracuseStep 2082439 = 3123659) B3123659
theorem B2342749 : Blo 2081435 2342749 := bbase (se 3 (by rfl) ⟨439265, by rfl⟩ : syracuseStep 2342749 = 878531) (by norm_num)
theorem B3123665 : Blo 2081435 3123665 := bstep (se 2 (by rfl) ⟨1171374, by rfl⟩ : syracuseStep 3123665 = 2342749) B2342749
theorem B2082443 : Blo 2081435 2082443 := bstep (se 1 (by rfl) ⟨1561832, by rfl⟩ : syracuseStep 2082443 = 3123665) B3123665
theorem B7028261 : Blo 2081435 7028261 := bbase (se 4 (by rfl) ⟨658899, by rfl⟩ : syracuseStep 7028261 = 1317799) (by norm_num)
theorem B4685507 : Blo 2081435 4685507 := bstep (se 1 (by rfl) ⟨3514130, by rfl⟩ : syracuseStep 4685507 = 7028261) B7028261
theorem B3123671 : Blo 2081435 3123671 := bstep (se 1 (by rfl) ⟨2342753, by rfl⟩ : syracuseStep 3123671 = 4685507) B4685507
theorem B2082447 : Blo 2081435 2082447 := bstep (se 1 (by rfl) ⟨1561835, by rfl⟩ : syracuseStep 2082447 = 3123671) B3123671
theorem B3123677 : Blo 2081435 3123677 := bbase (se 3 (by rfl) ⟨585689, by rfl⟩ : syracuseStep 3123677 = 1171379) (by norm_num)
theorem B2082451 : Blo 2081435 2082451 := bstep (se 1 (by rfl) ⟨1561838, by rfl⟩ : syracuseStep 2082451 = 3123677) B3123677
theorem B4685525 : Blo 2081435 4685525 := bbase (se 7 (by rfl) ⟨54908, by rfl⟩ : syracuseStep 4685525 = 109817) (by norm_num)
theorem B3123683 : Blo 2081435 3123683 := bstep (se 1 (by rfl) ⟨2342762, by rfl⟩ : syracuseStep 3123683 = 4685525) B4685525
theorem B2082455 : Blo 2081435 2082455 := bstep (se 1 (by rfl) ⟨1561841, by rfl⟩ : syracuseStep 2082455 = 3123683) B3123683
theorem B5003549 : Blo 2081435 5003549 := bbase (se 3 (by rfl) ⟨938165, by rfl⟩ : syracuseStep 5003549 = 1876331) (by norm_num)
theorem B3335699 : Blo 2081435 3335699 := bstep (se 1 (by rfl) ⟨2501774, by rfl⟩ : syracuseStep 3335699 = 5003549) B5003549
theorem B8895197 : Blo 2081435 8895197 := bstep (se 3 (by rfl) ⟨1667849, by rfl⟩ : syracuseStep 8895197 = 3335699) B3335699
theorem B5930131 : Blo 2081435 5930131 := bstep (se 1 (by rfl) ⟨4447598, by rfl⟩ : syracuseStep 5930131 = 8895197) B8895197
theorem B7906841 : Blo 2081435 7906841 := bstep (se 2 (by rfl) ⟨2965065, by rfl⟩ : syracuseStep 7906841 = 5930131) B5930131
theorem B5271227 : Blo 2081435 5271227 := bstep (se 1 (by rfl) ⟨3953420, by rfl⟩ : syracuseStep 5271227 = 7906841) B7906841
theorem B3514151 : Blo 2081435 3514151 := bstep (se 1 (by rfl) ⟨2635613, by rfl⟩ : syracuseStep 3514151 = 5271227) B5271227
theorem B2342767 : Blo 2081435 2342767 := bstep (se 1 (by rfl) ⟨1757075, by rfl⟩ : syracuseStep 2342767 = 3514151) B3514151
theorem B3123689 : Blo 2081435 3123689 := bstep (se 2 (by rfl) ⟨1171383, by rfl⟩ : syracuseStep 3123689 = 2342767) B2342767
theorem B2082459 : Blo 2081435 2082459 := bstep (se 1 (by rfl) ⟨1561844, by rfl⟩ : syracuseStep 2082459 = 3123689) B3123689
theorem B20014229 : Blo 2081435 20014229 := bbase (se 6 (by rfl) ⟨469083, by rfl⟩ : syracuseStep 20014229 = 938167) (by norm_num)
theorem B13342819 : Blo 2081435 13342819 := bstep (se 1 (by rfl) ⟨10007114, by rfl⟩ : syracuseStep 13342819 = 20014229) B20014229
theorem B17790425 : Blo 2081435 17790425 := bstep (se 2 (by rfl) ⟨6671409, by rfl⟩ : syracuseStep 17790425 = 13342819) B13342819
theorem B11860283 : Blo 2081435 11860283 := bstep (se 1 (by rfl) ⟨8895212, by rfl⟩ : syracuseStep 11860283 = 17790425) B17790425
theorem B7906855 : Blo 2081435 7906855 := bstep (se 1 (by rfl) ⟨5930141, by rfl⟩ : syracuseStep 7906855 = 11860283) B11860283
theorem B10542473 : Blo 2081435 10542473 := bstep (se 2 (by rfl) ⟨3953427, by rfl⟩ : syracuseStep 10542473 = 7906855) B7906855
theorem B7028315 : Blo 2081435 7028315 := bstep (se 1 (by rfl) ⟨5271236, by rfl⟩ : syracuseStep 7028315 = 10542473) B10542473
theorem B4685543 : Blo 2081435 4685543 := bstep (se 1 (by rfl) ⟨3514157, by rfl⟩ : syracuseStep 4685543 = 7028315) B7028315
theorem B3123695 : Blo 2081435 3123695 := bstep (se 1 (by rfl) ⟨2342771, by rfl⟩ : syracuseStep 3123695 = 4685543) B4685543
theorem B2082463 : Blo 2081435 2082463 := bstep (se 1 (by rfl) ⟨1561847, by rfl⟩ : syracuseStep 2082463 = 3123695) B3123695
theorem B3123701 : Blo 2081435 3123701 := bbase (se 5 (by rfl) ⟨146423, by rfl⟩ : syracuseStep 3123701 = 292847) (by norm_num)
theorem B2082467 : Blo 2081435 2082467 := bstep (se 1 (by rfl) ⟨1561850, by rfl⟩ : syracuseStep 2082467 = 3123701) B3123701
theorem B5930165 : Blo 2081435 5930165 := bbase (se 5 (by rfl) ⟨277976, by rfl⟩ : syracuseStep 5930165 = 555953) (by norm_num)
theorem B3953443 : Blo 2081435 3953443 := bstep (se 1 (by rfl) ⟨2965082, by rfl⟩ : syracuseStep 3953443 = 5930165) B5930165
theorem B5271257 : Blo 2081435 5271257 := bstep (se 2 (by rfl) ⟨1976721, by rfl⟩ : syracuseStep 5271257 = 3953443) B3953443
theorem B3514171 : Blo 2081435 3514171 := bstep (se 1 (by rfl) ⟨2635628, by rfl⟩ : syracuseStep 3514171 = 5271257) B5271257
theorem B4685561 : Blo 2081435 4685561 := bstep (se 2 (by rfl) ⟨1757085, by rfl⟩ : syracuseStep 4685561 = 3514171) B3514171
theorem B3123707 : Blo 2081435 3123707 := bstep (se 1 (by rfl) ⟨2342780, by rfl⟩ : syracuseStep 3123707 = 4685561) B4685561
theorem B2082471 : Blo 2081435 2082471 := bstep (se 1 (by rfl) ⟨1561853, by rfl⟩ : syracuseStep 2082471 = 3123707) B3123707
theorem B2342785 : Blo 2081435 2342785 := bbase (se 2 (by rfl) ⟨878544, by rfl⟩ : syracuseStep 2342785 = 1757089) (by norm_num)
theorem B3123713 : Blo 2081435 3123713 := bstep (se 2 (by rfl) ⟨1171392, by rfl⟩ : syracuseStep 3123713 = 2342785) B2342785
theorem B2082475 : Blo 2081435 2082475 := bstep (se 1 (by rfl) ⟨1561856, by rfl⟩ : syracuseStep 2082475 = 3123713) B3123713
theorem B5271277 : Blo 2081435 5271277 := bbase (se 3 (by rfl) ⟨988364, by rfl⟩ : syracuseStep 5271277 = 1976729) (by norm_num)
theorem B7028369 : Blo 2081435 7028369 := bstep (se 2 (by rfl) ⟨2635638, by rfl⟩ : syracuseStep 7028369 = 5271277) B5271277
theorem B4685579 : Blo 2081435 4685579 := bstep (se 1 (by rfl) ⟨3514184, by rfl⟩ : syracuseStep 4685579 = 7028369) B7028369
theorem B3123719 : Blo 2081435 3123719 := bstep (se 1 (by rfl) ⟨2342789, by rfl⟩ : syracuseStep 3123719 = 4685579) B4685579
theorem B2082479 : Blo 2081435 2082479 := bstep (se 1 (by rfl) ⟨1561859, by rfl⟩ : syracuseStep 2082479 = 3123719) B3123719
theorem B3123725 : Blo 2081435 3123725 := bbase (se 3 (by rfl) ⟨585698, by rfl⟩ : syracuseStep 3123725 = 1171397) (by norm_num)
theorem B2082483 : Blo 2081435 2082483 := bstep (se 1 (by rfl) ⟨1561862, by rfl⟩ : syracuseStep 2082483 = 3123725) B3123725
theorem B4685597 : Blo 2081435 4685597 := bbase (se 3 (by rfl) ⟨878549, by rfl⟩ : syracuseStep 4685597 = 1757099) (by norm_num)
theorem B3123731 : Blo 2081435 3123731 := bstep (se 1 (by rfl) ⟨2342798, by rfl⟩ : syracuseStep 3123731 = 4685597) B4685597
theorem B2082487 : Blo 2081435 2082487 := bstep (se 1 (by rfl) ⟨1561865, by rfl⟩ : syracuseStep 2082487 = 3123731) B3123731
theorem B3514205 : Blo 2081435 3514205 := bbase (se 3 (by rfl) ⟨658913, by rfl⟩ : syracuseStep 3514205 = 1317827) (by norm_num)
theorem B2342803 : Blo 2081435 2342803 := bstep (se 1 (by rfl) ⟨1757102, by rfl⟩ : syracuseStep 2342803 = 3514205) B3514205
theorem B3123737 : Blo 2081435 3123737 := bstep (se 2 (by rfl) ⟨1171401, by rfl⟩ : syracuseStep 3123737 = 2342803) B2342803
theorem B2082491 : Blo 2081435 2082491 := bstep (se 1 (by rfl) ⟨1561868, by rfl⟩ : syracuseStep 2082491 = 3123737) B3123737
theorem B8895349 : Blo 2081435 8895349 := bbase (se 5 (by rfl) ⟨416969, by rfl⟩ : syracuseStep 8895349 = 833939) (by norm_num)
theorem B11860465 : Blo 2081435 11860465 := bstep (se 2 (by rfl) ⟨4447674, by rfl⟩ : syracuseStep 11860465 = 8895349) B8895349
theorem B15813953 : Blo 2081435 15813953 := bstep (se 2 (by rfl) ⟨5930232, by rfl⟩ : syracuseStep 15813953 = 11860465) B11860465
theorem B10542635 : Blo 2081435 10542635 := bstep (se 1 (by rfl) ⟨7906976, by rfl⟩ : syracuseStep 10542635 = 15813953) B15813953
theorem B7028423 : Blo 2081435 7028423 := bstep (se 1 (by rfl) ⟨5271317, by rfl⟩ : syracuseStep 7028423 = 10542635) B10542635
theorem B4685615 : Blo 2081435 4685615 := bstep (se 1 (by rfl) ⟨3514211, by rfl⟩ : syracuseStep 4685615 = 7028423) B7028423
theorem B3123743 : Blo 2081435 3123743 := bstep (se 1 (by rfl) ⟨2342807, by rfl⟩ : syracuseStep 3123743 = 4685615) B4685615
theorem B2082495 : Blo 2081435 2082495 := bstep (se 1 (by rfl) ⟨1561871, by rfl⟩ : syracuseStep 2082495 = 3123743) B3123743
theorem B3123749 : Blo 2081435 3123749 := bbase (se 4 (by rfl) ⟨292851, by rfl⟩ : syracuseStep 3123749 = 585703) (by norm_num)
theorem B2082499 : Blo 2081435 2082499 := bstep (se 1 (by rfl) ⟨1561874, by rfl⟩ : syracuseStep 2082499 = 3123749) B3123749
theorem B2635669 : Blo 2081435 2635669 := bbase (se 6 (by rfl) ⟨61773, by rfl⟩ : syracuseStep 2635669 = 123547) (by norm_num)
theorem B3514225 : Blo 2081435 3514225 := bstep (se 2 (by rfl) ⟨1317834, by rfl⟩ : syracuseStep 3514225 = 2635669) B2635669
theorem B4685633 : Blo 2081435 4685633 := bstep (se 2 (by rfl) ⟨1757112, by rfl⟩ : syracuseStep 4685633 = 3514225) B3514225
theorem B3123755 : Blo 2081435 3123755 := bstep (se 1 (by rfl) ⟨2342816, by rfl⟩ : syracuseStep 3123755 = 4685633) B4685633
theorem B2082503 : Blo 2081435 2082503 := bstep (se 1 (by rfl) ⟨1561877, by rfl⟩ : syracuseStep 2082503 = 3123755) B3123755
theorem B2342821 : Blo 2081435 2342821 := bbase (se 4 (by rfl) ⟨219639, by rfl⟩ : syracuseStep 2342821 = 439279) (by norm_num)
theorem B3123761 : Blo 2081435 3123761 := bstep (se 2 (by rfl) ⟨1171410, by rfl⟩ : syracuseStep 3123761 = 2342821) B2342821
theorem B2082507 : Blo 2081435 2082507 := bstep (se 1 (by rfl) ⟨1561880, by rfl⟩ : syracuseStep 2082507 = 3123761) B3123761
theorem B2110925 : Blo 2081435 2110925 := bbase (se 3 (by rfl) ⟨395798, by rfl⟩ : syracuseStep 2110925 = 791597) (by norm_num)
theorem B5629133 : Blo 2081435 5629133 := bstep (se 3 (by rfl) ⟨1055462, by rfl⟩ : syracuseStep 5629133 = 2110925) B2110925
theorem B15011021 : Blo 2081435 15011021 := bstep (se 3 (by rfl) ⟨2814566, by rfl⟩ : syracuseStep 15011021 = 5629133) B5629133
theorem B10007347 : Blo 2081435 10007347 := bstep (se 1 (by rfl) ⟨7505510, by rfl⟩ : syracuseStep 10007347 = 15011021) B15011021
theorem B13343129 : Blo 2081435 13343129 := bstep (se 2 (by rfl) ⟨5003673, by rfl⟩ : syracuseStep 13343129 = 10007347) B10007347
theorem B8895419 : Blo 2081435 8895419 := bstep (se 1 (by rfl) ⟨6671564, by rfl⟩ : syracuseStep 8895419 = 13343129) B13343129
theorem B5930279 : Blo 2081435 5930279 := bstep (se 1 (by rfl) ⟨4447709, by rfl⟩ : syracuseStep 5930279 = 8895419) B8895419
theorem B3953519 : Blo 2081435 3953519 := bstep (se 1 (by rfl) ⟨2965139, by rfl⟩ : syracuseStep 3953519 = 5930279) B5930279
theorem B2635679 : Blo 2081435 2635679 := bstep (se 1 (by rfl) ⟨1976759, by rfl⟩ : syracuseStep 2635679 = 3953519) B3953519
theorem B7028477 : Blo 2081435 7028477 := bstep (se 3 (by rfl) ⟨1317839, by rfl⟩ : syracuseStep 7028477 = 2635679) B2635679
theorem B4685651 : Blo 2081435 4685651 := bstep (se 1 (by rfl) ⟨3514238, by rfl⟩ : syracuseStep 4685651 = 7028477) B7028477
theorem B3123767 : Blo 2081435 3123767 := bstep (se 1 (by rfl) ⟨2342825, by rfl⟩ : syracuseStep 3123767 = 4685651) B4685651
theorem B2082511 : Blo 2081435 2082511 := bstep (se 1 (by rfl) ⟨1561883, by rfl⟩ : syracuseStep 2082511 = 3123767) B3123767
theorem B3123773 : Blo 2081435 3123773 := bbase (se 3 (by rfl) ⟨585707, by rfl⟩ : syracuseStep 3123773 = 1171415) (by norm_num)
theorem B2082515 : Blo 2081435 2082515 := bstep (se 1 (by rfl) ⟨1561886, by rfl⟩ : syracuseStep 2082515 = 3123773) B3123773
theorem B4685669 : Blo 2081435 4685669 := bbase (se 4 (by rfl) ⟨439281, by rfl⟩ : syracuseStep 4685669 = 878563) (by norm_num)
theorem B3123779 : Blo 2081435 3123779 := bstep (se 1 (by rfl) ⟨2342834, by rfl⟩ : syracuseStep 3123779 = 4685669) B4685669
theorem B2082519 : Blo 2081435 2082519 := bstep (se 1 (by rfl) ⟨1561889, by rfl⟩ : syracuseStep 2082519 = 3123779) B3123779
theorem B5271389 : Blo 2081435 5271389 := bbase (se 3 (by rfl) ⟨988385, by rfl⟩ : syracuseStep 5271389 = 1976771) (by norm_num)
theorem B3514259 : Blo 2081435 3514259 := bstep (se 1 (by rfl) ⟨2635694, by rfl⟩ : syracuseStep 3514259 = 5271389) B5271389
theorem B2342839 : Blo 2081435 2342839 := bstep (se 1 (by rfl) ⟨1757129, by rfl⟩ : syracuseStep 2342839 = 3514259) B3514259
theorem B3123785 : Blo 2081435 3123785 := bstep (se 2 (by rfl) ⟨1171419, by rfl⟩ : syracuseStep 3123785 = 2342839) B2342839
theorem B2082523 : Blo 2081435 2082523 := bstep (se 1 (by rfl) ⟨1561892, by rfl⟩ : syracuseStep 2082523 = 3123785) B3123785
theorem B3953549 : Blo 2081435 3953549 := bbase (se 3 (by rfl) ⟨741290, by rfl⟩ : syracuseStep 3953549 = 1482581) (by norm_num)
theorem B10542797 : Blo 2081435 10542797 := bstep (se 3 (by rfl) ⟨1976774, by rfl⟩ : syracuseStep 10542797 = 3953549) B3953549
theorem B7028531 : Blo 2081435 7028531 := bstep (se 1 (by rfl) ⟨5271398, by rfl⟩ : syracuseStep 7028531 = 10542797) B10542797
theorem B4685687 : Blo 2081435 4685687 := bstep (se 1 (by rfl) ⟨3514265, by rfl⟩ : syracuseStep 4685687 = 7028531) B7028531
theorem B3123791 : Blo 2081435 3123791 := bstep (se 1 (by rfl) ⟨2342843, by rfl⟩ : syracuseStep 3123791 = 4685687) B4685687
theorem B2082527 : Blo 2081435 2082527 := bstep (se 1 (by rfl) ⟨1561895, by rfl⟩ : syracuseStep 2082527 = 3123791) B3123791
theorem B3123797 : Blo 2081435 3123797 := bbase (se 8 (by rfl) ⟨18303, by rfl⟩ : syracuseStep 3123797 = 36607) (by norm_num)
theorem B2082531 : Blo 2081435 2082531 := bstep (se 1 (by rfl) ⟨1561898, by rfl⟩ : syracuseStep 2082531 = 3123797) B3123797
theorem B4749637 : Blo 2081435 4749637 := bbase (se 4 (by rfl) ⟨445278, by rfl⟩ : syracuseStep 4749637 = 890557) (by norm_num)
theorem B6332849 : Blo 2081435 6332849 := bstep (se 2 (by rfl) ⟨2374818, by rfl⟩ : syracuseStep 6332849 = 4749637) B4749637
theorem B4221899 : Blo 2081435 4221899 := bstep (se 1 (by rfl) ⟨3166424, by rfl⟩ : syracuseStep 4221899 = 6332849) B6332849
theorem B2814599 : Blo 2081435 2814599 := bstep (se 1 (by rfl) ⟨2110949, by rfl⟩ : syracuseStep 2814599 = 4221899) B4221899
theorem B7505597 : Blo 2081435 7505597 := bstep (se 3 (by rfl) ⟨1407299, by rfl⟩ : syracuseStep 7505597 = 2814599) B2814599
theorem B5003731 : Blo 2081435 5003731 := bstep (se 1 (by rfl) ⟨3752798, by rfl⟩ : syracuseStep 5003731 = 7505597) B7505597
theorem B6671641 : Blo 2081435 6671641 := bstep (se 2 (by rfl) ⟨2501865, by rfl⟩ : syracuseStep 6671641 = 5003731) B5003731
theorem B8895521 : Blo 2081435 8895521 := bstep (se 2 (by rfl) ⟨3335820, by rfl⟩ : syracuseStep 8895521 = 6671641) B6671641
theorem B5930347 : Blo 2081435 5930347 := bstep (se 1 (by rfl) ⟨4447760, by rfl⟩ : syracuseStep 5930347 = 8895521) B8895521
theorem B7907129 : Blo 2081435 7907129 := bstep (se 2 (by rfl) ⟨2965173, by rfl⟩ : syracuseStep 7907129 = 5930347) B5930347
theorem B5271419 : Blo 2081435 5271419 := bstep (se 1 (by rfl) ⟨3953564, by rfl⟩ : syracuseStep 5271419 = 7907129) B7907129
theorem B3514279 : Blo 2081435 3514279 := bstep (se 1 (by rfl) ⟨2635709, by rfl⟩ : syracuseStep 3514279 = 5271419) B5271419
theorem B4685705 : Blo 2081435 4685705 := bstep (se 2 (by rfl) ⟨1757139, by rfl⟩ : syracuseStep 4685705 = 3514279) B3514279
theorem B3123803 : Blo 2081435 3123803 := bstep (se 1 (by rfl) ⟨2342852, by rfl⟩ : syracuseStep 3123803 = 4685705) B4685705
theorem B2082535 : Blo 2081435 2082535 := bstep (se 1 (by rfl) ⟨1561901, by rfl⟩ : syracuseStep 2082535 = 3123803) B3123803
theorem B2342857 : Blo 2081435 2342857 := bbase (se 2 (by rfl) ⟨878571, by rfl⟩ : syracuseStep 2342857 = 1757143) (by norm_num)
theorem B3123809 : Blo 2081435 3123809 := bstep (se 2 (by rfl) ⟨1171428, by rfl⟩ : syracuseStep 3123809 = 2342857) B2342857
theorem B2082539 : Blo 2081435 2082539 := bstep (se 1 (by rfl) ⟨1561904, by rfl⟩ : syracuseStep 2082539 = 3123809) B3123809
theorem B3752813 : Blo 2081435 3752813 := bbase (se 3 (by rfl) ⟨703652, by rfl⟩ : syracuseStep 3752813 = 1407305) (by norm_num)
theorem B2501875 : Blo 2081435 2501875 := bstep (se 1 (by rfl) ⟨1876406, by rfl⟩ : syracuseStep 2501875 = 3752813) B3752813
theorem B3335833 : Blo 2081435 3335833 := bstep (se 2 (by rfl) ⟨1250937, by rfl⟩ : syracuseStep 3335833 = 2501875) B2501875
theorem B17791109 : Blo 2081435 17791109 := bstep (se 4 (by rfl) ⟨1667916, by rfl⟩ : syracuseStep 17791109 = 3335833) B3335833
theorem B11860739 : Blo 2081435 11860739 := bstep (se 1 (by rfl) ⟨8895554, by rfl⟩ : syracuseStep 11860739 = 17791109) B17791109
theorem B7907159 : Blo 2081435 7907159 := bstep (se 1 (by rfl) ⟨5930369, by rfl⟩ : syracuseStep 7907159 = 11860739) B11860739
theorem B5271439 : Blo 2081435 5271439 := bstep (se 1 (by rfl) ⟨3953579, by rfl⟩ : syracuseStep 5271439 = 7907159) B7907159
theorem B7028585 : Blo 2081435 7028585 := bstep (se 2 (by rfl) ⟨2635719, by rfl⟩ : syracuseStep 7028585 = 5271439) B5271439
theorem B4685723 : Blo 2081435 4685723 := bstep (se 1 (by rfl) ⟨3514292, by rfl⟩ : syracuseStep 4685723 = 7028585) B7028585
theorem B3123815 : Blo 2081435 3123815 := bstep (se 1 (by rfl) ⟨2342861, by rfl⟩ : syracuseStep 3123815 = 4685723) B4685723
theorem B2082543 : Blo 2081435 2082543 := bstep (se 1 (by rfl) ⟨1561907, by rfl⟩ : syracuseStep 2082543 = 3123815) B3123815
theorem B3123821 : Blo 2081435 3123821 := bbase (se 3 (by rfl) ⟨585716, by rfl⟩ : syracuseStep 3123821 = 1171433) (by norm_num)
theorem B2082547 : Blo 2081435 2082547 := bstep (se 1 (by rfl) ⟨1561910, by rfl⟩ : syracuseStep 2082547 = 3123821) B3123821
theorem B4685741 : Blo 2081435 4685741 := bbase (se 3 (by rfl) ⟨878576, by rfl⟩ : syracuseStep 4685741 = 1757153) (by norm_num)
theorem B3123827 : Blo 2081435 3123827 := bstep (se 1 (by rfl) ⟨2342870, by rfl⟩ : syracuseStep 3123827 = 4685741) B4685741
theorem B2082551 : Blo 2081435 2082551 := bstep (se 1 (by rfl) ⟨1561913, by rfl⟩ : syracuseStep 2082551 = 3123827) B3123827
theorem B5930405 : Blo 2081435 5930405 := bbase (se 4 (by rfl) ⟨555975, by rfl⟩ : syracuseStep 5930405 = 1111951) (by norm_num)
theorem B3953603 : Blo 2081435 3953603 := bstep (se 1 (by rfl) ⟨2965202, by rfl⟩ : syracuseStep 3953603 = 5930405) B5930405
theorem B2635735 : Blo 2081435 2635735 := bstep (se 1 (by rfl) ⟨1976801, by rfl⟩ : syracuseStep 2635735 = 3953603) B3953603
theorem B3514313 : Blo 2081435 3514313 := bstep (se 2 (by rfl) ⟨1317867, by rfl⟩ : syracuseStep 3514313 = 2635735) B2635735
theorem B2342875 : Blo 2081435 2342875 := bstep (se 1 (by rfl) ⟨1757156, by rfl⟩ : syracuseStep 2342875 = 3514313) B3514313
theorem B3123833 : Blo 2081435 3123833 := bstep (se 2 (by rfl) ⟨1171437, by rfl⟩ : syracuseStep 3123833 = 2342875) B2342875
theorem B2082555 : Blo 2081435 2082555 := bstep (se 1 (by rfl) ⟨1561916, by rfl⟩ : syracuseStep 2082555 = 3123833) B3123833
theorem B2110973 : Blo 2081435 2110973 := bbase (se 3 (by rfl) ⟨395807, by rfl⟩ : syracuseStep 2110973 = 791615) (by norm_num)
theorem B22517045 : Blo 2081435 22517045 := bstep (se 5 (by rfl) ⟨1055486, by rfl⟩ : syracuseStep 22517045 = 2110973) B2110973
theorem B15011363 : Blo 2081435 15011363 := bstep (se 1 (by rfl) ⟨11258522, by rfl⟩ : syracuseStep 15011363 = 22517045) B22517045
theorem B40030301 : Blo 2081435 40030301 := bstep (se 3 (by rfl) ⟨7505681, by rfl⟩ : syracuseStep 40030301 = 15011363) B15011363
theorem B26686867 : Blo 2081435 26686867 := bstep (se 1 (by rfl) ⟨20015150, by rfl⟩ : syracuseStep 26686867 = 40030301) B40030301
theorem B35582489 : Blo 2081435 35582489 := bstep (se 2 (by rfl) ⟨13343433, by rfl⟩ : syracuseStep 35582489 = 26686867) B26686867
theorem B23721659 : Blo 2081435 23721659 := bstep (se 1 (by rfl) ⟨17791244, by rfl⟩ : syracuseStep 23721659 = 35582489) B35582489
theorem B15814439 : Blo 2081435 15814439 := bstep (se 1 (by rfl) ⟨11860829, by rfl⟩ : syracuseStep 15814439 = 23721659) B23721659
theorem B10542959 : Blo 2081435 10542959 := bstep (se 1 (by rfl) ⟨7907219, by rfl⟩ : syracuseStep 10542959 = 15814439) B15814439
theorem B7028639 : Blo 2081435 7028639 := bstep (se 1 (by rfl) ⟨5271479, by rfl⟩ : syracuseStep 7028639 = 10542959) B10542959
theorem B4685759 : Blo 2081435 4685759 := bstep (se 1 (by rfl) ⟨3514319, by rfl⟩ : syracuseStep 4685759 = 7028639) B7028639
theorem B3123839 : Blo 2081435 3123839 := bstep (se 1 (by rfl) ⟨2342879, by rfl⟩ : syracuseStep 3123839 = 4685759) B4685759
theorem B2082559 : Blo 2081435 2082559 := bstep (se 1 (by rfl) ⟨1561919, by rfl⟩ : syracuseStep 2082559 = 3123839) B3123839
theorem B3123845 : Blo 2081435 3123845 := bbase (se 4 (by rfl) ⟨292860, by rfl⟩ : syracuseStep 3123845 = 585721) (by norm_num)
theorem B2082563 : Blo 2081435 2082563 := bstep (se 1 (by rfl) ⟨1561922, by rfl⟩ : syracuseStep 2082563 = 3123845) B3123845
theorem B3514333 : Blo 2081435 3514333 := bbase (se 3 (by rfl) ⟨658937, by rfl⟩ : syracuseStep 3514333 = 1317875) (by norm_num)
theorem B4685777 : Blo 2081435 4685777 := bstep (se 2 (by rfl) ⟨1757166, by rfl⟩ : syracuseStep 4685777 = 3514333) B3514333
theorem B3123851 : Blo 2081435 3123851 := bstep (se 1 (by rfl) ⟨2342888, by rfl⟩ : syracuseStep 3123851 = 4685777) B4685777
theorem B2082567 : Blo 2081435 2082567 := bstep (se 1 (by rfl) ⟨1561925, by rfl⟩ : syracuseStep 2082567 = 3123851) B3123851
theorem B2342893 : Blo 2081435 2342893 := bbase (se 3 (by rfl) ⟨439292, by rfl⟩ : syracuseStep 2342893 = 878585) (by norm_num)
theorem B3123857 : Blo 2081435 3123857 := bstep (se 2 (by rfl) ⟨1171446, by rfl⟩ : syracuseStep 3123857 = 2342893) B2342893
theorem B2082571 : Blo 2081435 2082571 := bstep (se 1 (by rfl) ⟨1561928, by rfl⟩ : syracuseStep 2082571 = 3123857) B3123857
theorem B7028693 : Blo 2081435 7028693 := bbase (se 7 (by rfl) ⟨82367, by rfl⟩ : syracuseStep 7028693 = 164735) (by norm_num)
theorem B4685795 : Blo 2081435 4685795 := bstep (se 1 (by rfl) ⟨3514346, by rfl⟩ : syracuseStep 4685795 = 7028693) B7028693
theorem B3123863 : Blo 2081435 3123863 := bstep (se 1 (by rfl) ⟨2342897, by rfl⟩ : syracuseStep 3123863 = 4685795) B4685795
theorem B2082575 : Blo 2081435 2082575 := bstep (se 1 (by rfl) ⟨1561931, by rfl⟩ : syracuseStep 2082575 = 3123863) B3123863
theorem B3123869 : Blo 2081435 3123869 := bbase (se 3 (by rfl) ⟨585725, by rfl⟩ : syracuseStep 3123869 = 1171451) (by norm_num)
theorem B2082579 : Blo 2081435 2082579 := bstep (se 1 (by rfl) ⟨1561934, by rfl⟩ : syracuseStep 2082579 = 3123869) B3123869
theorem B4685813 : Blo 2081435 4685813 := bbase (se 5 (by rfl) ⟨219647, by rfl⟩ : syracuseStep 4685813 = 439295) (by norm_num)
theorem B3123875 : Blo 2081435 3123875 := bstep (se 1 (by rfl) ⟨2342906, by rfl⟩ : syracuseStep 3123875 = 4685813) B4685813
theorem B2082583 : Blo 2081435 2082583 := bstep (se 1 (by rfl) ⟨1561937, by rfl⟩ : syracuseStep 2082583 = 3123875) B3123875
theorem B20288501 : Blo 2081435 20288501 := bbase (se 5 (by rfl) ⟨951023, by rfl⟩ : syracuseStep 20288501 = 1902047) (by norm_num)
theorem B13525667 : Blo 2081435 13525667 := bstep (se 1 (by rfl) ⟨10144250, by rfl⟩ : syracuseStep 13525667 = 20288501) B20288501
theorem B9017111 : Blo 2081435 9017111 := bstep (se 1 (by rfl) ⟨6762833, by rfl⟩ : syracuseStep 9017111 = 13525667) B13525667
theorem B384730069 : Blo 2081435 384730069 := bstep (se 7 (by rfl) ⟨4508555, by rfl⟩ : syracuseStep 384730069 = 9017111) B9017111
theorem B512973425 : Blo 2081435 512973425 := bstep (se 2 (by rfl) ⟨192365034, by rfl⟩ : syracuseStep 512973425 = 384730069) B384730069
theorem B341982283 : Blo 2081435 341982283 := bstep (se 1 (by rfl) ⟨256486712, by rfl⟩ : syracuseStep 341982283 = 512973425) B512973425
theorem B455976377 : Blo 2081435 455976377 := bstep (se 2 (by rfl) ⟨170991141, by rfl⟩ : syracuseStep 455976377 = 341982283) B341982283
theorem B303984251 : Blo 2081435 303984251 := bstep (se 1 (by rfl) ⟨227988188, by rfl⟩ : syracuseStep 303984251 = 455976377) B455976377
theorem B202656167 : Blo 2081435 202656167 := bstep (se 1 (by rfl) ⟨151992125, by rfl⟩ : syracuseStep 202656167 = 303984251) B303984251
theorem B135104111 : Blo 2081435 135104111 := bstep (se 1 (by rfl) ⟨101328083, by rfl⟩ : syracuseStep 135104111 = 202656167) B202656167
theorem B90069407 : Blo 2081435 90069407 := bstep (se 1 (by rfl) ⟨67552055, by rfl⟩ : syracuseStep 90069407 = 135104111) B135104111
theorem B60046271 : Blo 2081435 60046271 := bstep (se 1 (by rfl) ⟨45034703, by rfl⟩ : syracuseStep 60046271 = 90069407) B90069407
theorem B40030847 : Blo 2081435 40030847 := bstep (se 1 (by rfl) ⟨30023135, by rfl⟩ : syracuseStep 40030847 = 60046271) B60046271
theorem B26687231 : Blo 2081435 26687231 := bstep (se 1 (by rfl) ⟨20015423, by rfl⟩ : syracuseStep 26687231 = 40030847) B40030847
theorem B17791487 : Blo 2081435 17791487 := bstep (se 1 (by rfl) ⟨13343615, by rfl⟩ : syracuseStep 17791487 = 26687231) B26687231
theorem B11860991 : Blo 2081435 11860991 := bstep (se 1 (by rfl) ⟨8895743, by rfl⟩ : syracuseStep 11860991 = 17791487) B17791487
theorem B7907327 : Blo 2081435 7907327 := bstep (se 1 (by rfl) ⟨5930495, by rfl⟩ : syracuseStep 7907327 = 11860991) B11860991
theorem B5271551 : Blo 2081435 5271551 := bstep (se 1 (by rfl) ⟨3953663, by rfl⟩ : syracuseStep 5271551 = 7907327) B7907327
theorem B3514367 : Blo 2081435 3514367 := bstep (se 1 (by rfl) ⟨2635775, by rfl⟩ : syracuseStep 3514367 = 5271551) B5271551
theorem B2342911 : Blo 2081435 2342911 := bstep (se 1 (by rfl) ⟨1757183, by rfl⟩ : syracuseStep 2342911 = 3514367) B3514367
theorem B3123881 : Blo 2081435 3123881 := bstep (se 2 (by rfl) ⟨1171455, by rfl⟩ : syracuseStep 3123881 = 2342911) B2342911
theorem B2082587 : Blo 2081435 2082587 := bstep (se 1 (by rfl) ⟨1561940, by rfl⟩ : syracuseStep 2082587 = 3123881) B3123881
theorem B2965253 : Blo 2081435 2965253 := bbase (se 4 (by rfl) ⟨277992, by rfl⟩ : syracuseStep 2965253 = 555985) (by norm_num)
theorem B7907341 : Blo 2081435 7907341 := bstep (se 3 (by rfl) ⟨1482626, by rfl⟩ : syracuseStep 7907341 = 2965253) B2965253
theorem B10543121 : Blo 2081435 10543121 := bstep (se 2 (by rfl) ⟨3953670, by rfl⟩ : syracuseStep 10543121 = 7907341) B7907341
theorem B7028747 : Blo 2081435 7028747 := bstep (se 1 (by rfl) ⟨5271560, by rfl⟩ : syracuseStep 7028747 = 10543121) B10543121
theorem B4685831 : Blo 2081435 4685831 := bstep (se 1 (by rfl) ⟨3514373, by rfl⟩ : syracuseStep 4685831 = 7028747) B7028747
theorem B3123887 : Blo 2081435 3123887 := bstep (se 1 (by rfl) ⟨2342915, by rfl⟩ : syracuseStep 3123887 = 4685831) B4685831
theorem B2082591 : Blo 2081435 2082591 := bstep (se 1 (by rfl) ⟨1561943, by rfl⟩ : syracuseStep 2082591 = 3123887) B3123887
theorem B3123893 : Blo 2081435 3123893 := bbase (se 5 (by rfl) ⟨146432, by rfl⟩ : syracuseStep 3123893 = 292865) (by norm_num)
theorem B2082595 : Blo 2081435 2082595 := bstep (se 1 (by rfl) ⟨1561946, by rfl⟩ : syracuseStep 2082595 = 3123893) B3123893
theorem B5271581 : Blo 2081435 5271581 := bbase (se 3 (by rfl) ⟨988421, by rfl⟩ : syracuseStep 5271581 = 1976843) (by norm_num)
theorem B3514387 : Blo 2081435 3514387 := bstep (se 1 (by rfl) ⟨2635790, by rfl⟩ : syracuseStep 3514387 = 5271581) B5271581
theorem B4685849 : Blo 2081435 4685849 := bstep (se 2 (by rfl) ⟨1757193, by rfl⟩ : syracuseStep 4685849 = 3514387) B3514387
theorem B3123899 : Blo 2081435 3123899 := bstep (se 1 (by rfl) ⟨2342924, by rfl⟩ : syracuseStep 3123899 = 4685849) B4685849
theorem B2082599 : Blo 2081435 2082599 := bstep (se 1 (by rfl) ⟨1561949, by rfl⟩ : syracuseStep 2082599 = 3123899) B3123899
theorem B2342929 : Blo 2081435 2342929 := bbase (se 2 (by rfl) ⟨878598, by rfl⟩ : syracuseStep 2342929 = 1757197) (by norm_num)
theorem B3123905 : Blo 2081435 3123905 := bstep (se 2 (by rfl) ⟨1171464, by rfl⟩ : syracuseStep 3123905 = 2342929) B2342929
theorem B2082603 : Blo 2081435 2082603 := bstep (se 1 (by rfl) ⟨1561952, by rfl⟩ : syracuseStep 2082603 = 3123905) B3123905
theorem B3953701 : Blo 2081435 3953701 := bbase (se 4 (by rfl) ⟨370659, by rfl⟩ : syracuseStep 3953701 = 741319) (by norm_num)
theorem B5271601 : Blo 2081435 5271601 := bstep (se 2 (by rfl) ⟨1976850, by rfl⟩ : syracuseStep 5271601 = 3953701) B3953701
theorem B7028801 : Blo 2081435 7028801 := bstep (se 2 (by rfl) ⟨2635800, by rfl⟩ : syracuseStep 7028801 = 5271601) B5271601
theorem B4685867 : Blo 2081435 4685867 := bstep (se 1 (by rfl) ⟨3514400, by rfl⟩ : syracuseStep 4685867 = 7028801) B7028801
theorem B3123911 : Blo 2081435 3123911 := bstep (se 1 (by rfl) ⟨2342933, by rfl⟩ : syracuseStep 3123911 = 4685867) B4685867
theorem B2082607 : Blo 2081435 2082607 := bstep (se 1 (by rfl) ⟨1561955, by rfl⟩ : syracuseStep 2082607 = 3123911) B3123911
theorem B3123917 : Blo 2081435 3123917 := bbase (se 3 (by rfl) ⟨585734, by rfl⟩ : syracuseStep 3123917 = 1171469) (by norm_num)
theorem B2082611 : Blo 2081435 2082611 := bstep (se 1 (by rfl) ⟨1561958, by rfl⟩ : syracuseStep 2082611 = 3123917) B3123917
theorem B4685885 : Blo 2081435 4685885 := bbase (se 3 (by rfl) ⟨878603, by rfl⟩ : syracuseStep 4685885 = 1757207) (by norm_num)
theorem B3123923 : Blo 2081435 3123923 := bstep (se 1 (by rfl) ⟨2342942, by rfl⟩ : syracuseStep 3123923 = 4685885) B4685885
theorem B2082615 : Blo 2081435 2082615 := bstep (se 1 (by rfl) ⟨1561961, by rfl⟩ : syracuseStep 2082615 = 3123923) B3123923
theorem B3514421 : Blo 2081435 3514421 := bbase (se 5 (by rfl) ⟨164738, by rfl⟩ : syracuseStep 3514421 = 329477) (by norm_num)
theorem B2342947 : Blo 2081435 2342947 := bstep (se 1 (by rfl) ⟨1757210, by rfl⟩ : syracuseStep 2342947 = 3514421) B3514421
theorem B3123929 : Blo 2081435 3123929 := bstep (se 2 (by rfl) ⟨1171473, by rfl⟩ : syracuseStep 3123929 = 2342947) B2342947
theorem B2082619 : Blo 2081435 2082619 := bstep (se 1 (by rfl) ⟨1561964, by rfl⟩ : syracuseStep 2082619 = 3123929) B3123929
theorem B5930597 : Blo 2081435 5930597 := bbase (se 4 (by rfl) ⟨555993, by rfl⟩ : syracuseStep 5930597 = 1111987) (by norm_num)
theorem B15814925 : Blo 2081435 15814925 := bstep (se 3 (by rfl) ⟨2965298, by rfl⟩ : syracuseStep 15814925 = 5930597) B5930597
theorem B10543283 : Blo 2081435 10543283 := bstep (se 1 (by rfl) ⟨7907462, by rfl⟩ : syracuseStep 10543283 = 15814925) B15814925
theorem B7028855 : Blo 2081435 7028855 := bstep (se 1 (by rfl) ⟨5271641, by rfl⟩ : syracuseStep 7028855 = 10543283) B10543283
theorem B4685903 : Blo 2081435 4685903 := bstep (se 1 (by rfl) ⟨3514427, by rfl⟩ : syracuseStep 4685903 = 7028855) B7028855
theorem B3123935 : Blo 2081435 3123935 := bstep (se 1 (by rfl) ⟨2342951, by rfl⟩ : syracuseStep 3123935 = 4685903) B4685903
theorem B2082623 : Blo 2081435 2082623 := bstep (se 1 (by rfl) ⟨1561967, by rfl⟩ : syracuseStep 2082623 = 3123935) B3123935
theorem B3123941 : Blo 2081435 3123941 := bbase (se 4 (by rfl) ⟨292869, by rfl⟩ : syracuseStep 3123941 = 585739) (by norm_num)
theorem B2082627 : Blo 2081435 2082627 := bstep (se 1 (by rfl) ⟨1561970, by rfl⟩ : syracuseStep 2082627 = 3123941) B3123941
theorem B4007693 : Blo 2081435 4007693 := bbase (se 3 (by rfl) ⟨751442, by rfl⟩ : syracuseStep 4007693 = 1502885) (by norm_num)
theorem B2671795 : Blo 2081435 2671795 := bstep (se 1 (by rfl) ⟨2003846, by rfl⟩ : syracuseStep 2671795 = 4007693) B4007693
theorem B3562393 : Blo 2081435 3562393 := bstep (se 2 (by rfl) ⟨1335897, by rfl⟩ : syracuseStep 3562393 = 2671795) B2671795
theorem B4749857 : Blo 2081435 4749857 := bstep (se 2 (by rfl) ⟨1781196, by rfl⟩ : syracuseStep 4749857 = 3562393) B3562393
theorem B3166571 : Blo 2081435 3166571 := bstep (se 1 (by rfl) ⟨2374928, by rfl⟩ : syracuseStep 3166571 = 4749857) B4749857
theorem B8444189 : Blo 2081435 8444189 := bstep (se 3 (by rfl) ⟨1583285, by rfl⟩ : syracuseStep 8444189 = 3166571) B3166571
theorem B5629459 : Blo 2081435 5629459 := bstep (se 1 (by rfl) ⟨4222094, by rfl⟩ : syracuseStep 5629459 = 8444189) B8444189
theorem B7505945 : Blo 2081435 7505945 := bstep (se 2 (by rfl) ⟨2814729, by rfl⟩ : syracuseStep 7505945 = 5629459) B5629459
theorem B5003963 : Blo 2081435 5003963 := bstep (se 1 (by rfl) ⟨3752972, by rfl⟩ : syracuseStep 5003963 = 7505945) B7505945
theorem B3335975 : Blo 2081435 3335975 := bstep (se 1 (by rfl) ⟨2501981, by rfl⟩ : syracuseStep 3335975 = 5003963) B5003963
theorem B2223983 : Blo 2081435 2223983 := bstep (se 1 (by rfl) ⟨1667987, by rfl⟩ : syracuseStep 2223983 = 3335975) B3335975
theorem B5930621 : Blo 2081435 5930621 := bstep (se 3 (by rfl) ⟨1111991, by rfl⟩ : syracuseStep 5930621 = 2223983) B2223983
theorem B3953747 : Blo 2081435 3953747 := bstep (se 1 (by rfl) ⟨2965310, by rfl⟩ : syracuseStep 3953747 = 5930621) B5930621
theorem B2635831 : Blo 2081435 2635831 := bstep (se 1 (by rfl) ⟨1976873, by rfl⟩ : syracuseStep 2635831 = 3953747) B3953747
theorem B3514441 : Blo 2081435 3514441 := bstep (se 2 (by rfl) ⟨1317915, by rfl⟩ : syracuseStep 3514441 = 2635831) B2635831
theorem B4685921 : Blo 2081435 4685921 := bstep (se 2 (by rfl) ⟨1757220, by rfl⟩ : syracuseStep 4685921 = 3514441) B3514441
theorem B3123947 : Blo 2081435 3123947 := bstep (se 1 (by rfl) ⟨2342960, by rfl⟩ : syracuseStep 3123947 = 4685921) B4685921
theorem B2082631 : Blo 2081435 2082631 := bstep (se 1 (by rfl) ⟨1561973, by rfl⟩ : syracuseStep 2082631 = 3123947) B3123947
theorem B2342965 : Blo 2081435 2342965 := bbase (se 5 (by rfl) ⟨109826, by rfl⟩ : syracuseStep 2342965 = 219653) (by norm_num)
theorem B3123953 : Blo 2081435 3123953 := bstep (se 2 (by rfl) ⟨1171482, by rfl⟩ : syracuseStep 3123953 = 2342965) B2342965
theorem B2082635 : Blo 2081435 2082635 := bstep (se 1 (by rfl) ⟨1561976, by rfl⟩ : syracuseStep 2082635 = 3123953) B3123953
theorem B2635841 : Blo 2081435 2635841 := bbase (se 2 (by rfl) ⟨988440, by rfl⟩ : syracuseStep 2635841 = 1976881) (by norm_num)
theorem B7028909 : Blo 2081435 7028909 := bstep (se 3 (by rfl) ⟨1317920, by rfl⟩ : syracuseStep 7028909 = 2635841) B2635841
theorem B4685939 : Blo 2081435 4685939 := bstep (se 1 (by rfl) ⟨3514454, by rfl⟩ : syracuseStep 4685939 = 7028909) B7028909
theorem B3123959 : Blo 2081435 3123959 := bstep (se 1 (by rfl) ⟨2342969, by rfl⟩ : syracuseStep 3123959 = 4685939) B4685939
theorem B2082639 : Blo 2081435 2082639 := bstep (se 1 (by rfl) ⟨1561979, by rfl⟩ : syracuseStep 2082639 = 3123959) B3123959
theorem B3123965 : Blo 2081435 3123965 := bbase (se 3 (by rfl) ⟨585743, by rfl⟩ : syracuseStep 3123965 = 1171487) (by norm_num)
theorem B2082643 : Blo 2081435 2082643 := bstep (se 1 (by rfl) ⟨1561982, by rfl⟩ : syracuseStep 2082643 = 3123965) B3123965
theorem B4685957 : Blo 2081435 4685957 := bbase (se 4 (by rfl) ⟨439308, by rfl⟩ : syracuseStep 4685957 = 878617) (by norm_num)
theorem B3123971 : Blo 2081435 3123971 := bstep (se 1 (by rfl) ⟨2342978, by rfl⟩ : syracuseStep 3123971 = 4685957) B4685957
theorem B2082647 : Blo 2081435 2082647 := bstep (se 1 (by rfl) ⟨1561985, by rfl⟩ : syracuseStep 2082647 = 3123971) B3123971
theorem B2254349 : Blo 2081435 2254349 := bbase (se 3 (by rfl) ⟨422690, by rfl⟩ : syracuseStep 2254349 = 845381) (by norm_num)
theorem B6011597 : Blo 2081435 6011597 := bstep (se 3 (by rfl) ⟨1127174, by rfl⟩ : syracuseStep 6011597 = 2254349) B2254349
theorem B4007731 : Blo 2081435 4007731 := bstep (se 1 (by rfl) ⟨3005798, by rfl⟩ : syracuseStep 4007731 = 6011597) B6011597
theorem B5343641 : Blo 2081435 5343641 := bstep (se 2 (by rfl) ⟨2003865, by rfl⟩ : syracuseStep 5343641 = 4007731) B4007731
theorem B3562427 : Blo 2081435 3562427 := bstep (se 1 (by rfl) ⟨2671820, by rfl⟩ : syracuseStep 3562427 = 5343641) B5343641
theorem B9499805 : Blo 2081435 9499805 := bstep (se 3 (by rfl) ⟨1781213, by rfl⟩ : syracuseStep 9499805 = 3562427) B3562427
theorem B6333203 : Blo 2081435 6333203 := bstep (se 1 (by rfl) ⟨4749902, by rfl⟩ : syracuseStep 6333203 = 9499805) B9499805
theorem B4222135 : Blo 2081435 4222135 := bstep (se 1 (by rfl) ⟨3166601, by rfl⟩ : syracuseStep 4222135 = 6333203) B6333203
theorem B5629513 : Blo 2081435 5629513 := bstep (se 2 (by rfl) ⟨2111067, by rfl⟩ : syracuseStep 5629513 = 4222135) B4222135
theorem B7506017 : Blo 2081435 7506017 := bstep (se 2 (by rfl) ⟨2814756, by rfl⟩ : syracuseStep 7506017 = 5629513) B5629513
theorem B5004011 : Blo 2081435 5004011 := bstep (se 1 (by rfl) ⟨3753008, by rfl⟩ : syracuseStep 5004011 = 7506017) B7506017
theorem B3336007 : Blo 2081435 3336007 := bstep (se 1 (by rfl) ⟨2502005, by rfl⟩ : syracuseStep 3336007 = 5004011) B5004011
theorem B4448009 : Blo 2081435 4448009 := bstep (se 2 (by rfl) ⟨1668003, by rfl⟩ : syracuseStep 4448009 = 3336007) B3336007
theorem B2965339 : Blo 2081435 2965339 := bstep (se 1 (by rfl) ⟨2224004, by rfl⟩ : syracuseStep 2965339 = 4448009) B4448009
theorem B3953785 : Blo 2081435 3953785 := bstep (se 2 (by rfl) ⟨1482669, by rfl⟩ : syracuseStep 3953785 = 2965339) B2965339
theorem B5271713 : Blo 2081435 5271713 := bstep (se 2 (by rfl) ⟨1976892, by rfl⟩ : syracuseStep 5271713 = 3953785) B3953785
theorem B3514475 : Blo 2081435 3514475 := bstep (se 1 (by rfl) ⟨2635856, by rfl⟩ : syracuseStep 3514475 = 5271713) B5271713
theorem B2342983 : Blo 2081435 2342983 := bstep (se 1 (by rfl) ⟨1757237, by rfl⟩ : syracuseStep 2342983 = 3514475) B3514475
theorem B3123977 : Blo 2081435 3123977 := bstep (se 2 (by rfl) ⟨1171491, by rfl⟩ : syracuseStep 3123977 = 2342983) B2342983
theorem B2082651 : Blo 2081435 2082651 := bstep (se 1 (by rfl) ⟨1561988, by rfl⟩ : syracuseStep 2082651 = 3123977) B3123977
theorem B10543445 : Blo 2081435 10543445 := bbase (se 10 (by rfl) ⟨15444, by rfl⟩ : syracuseStep 10543445 = 30889) (by norm_num)
theorem B7028963 : Blo 2081435 7028963 := bstep (se 1 (by rfl) ⟨5271722, by rfl⟩ : syracuseStep 7028963 = 10543445) B10543445
theorem B4685975 : Blo 2081435 4685975 := bstep (se 1 (by rfl) ⟨3514481, by rfl⟩ : syracuseStep 4685975 = 7028963) B7028963
theorem B3123983 : Blo 2081435 3123983 := bstep (se 1 (by rfl) ⟨2342987, by rfl⟩ : syracuseStep 3123983 = 4685975) B4685975
theorem B2082655 : Blo 2081435 2082655 := bstep (se 1 (by rfl) ⟨1561991, by rfl⟩ : syracuseStep 2082655 = 3123983) B3123983
theorem B3123989 : Blo 2081435 3123989 := bbase (se 6 (by rfl) ⟨73218, by rfl⟩ : syracuseStep 3123989 = 146437) (by norm_num)
theorem B2082659 : Blo 2081435 2082659 := bstep (se 1 (by rfl) ⟨1561994, by rfl⟩ : syracuseStep 2082659 = 3123989) B3123989
theorem B17352629 : Blo 2081435 17352629 := bbase (se 5 (by rfl) ⟨813404, by rfl⟩ : syracuseStep 17352629 = 1626809) (by norm_num)
theorem B11568419 : Blo 2081435 11568419 := bstep (se 1 (by rfl) ⟨8676314, by rfl⟩ : syracuseStep 11568419 = 17352629) B17352629
theorem B7712279 : Blo 2081435 7712279 := bstep (se 1 (by rfl) ⟨5784209, by rfl⟩ : syracuseStep 7712279 = 11568419) B11568419
theorem B5141519 : Blo 2081435 5141519 := bstep (se 1 (by rfl) ⟨3856139, by rfl⟩ : syracuseStep 5141519 = 7712279) B7712279
theorem B3427679 : Blo 2081435 3427679 := bstep (se 1 (by rfl) ⟨2570759, by rfl⟩ : syracuseStep 3427679 = 5141519) B5141519
theorem B2285119 : Blo 2081435 2285119 := bstep (se 1 (by rfl) ⟨1713839, by rfl⟩ : syracuseStep 2285119 = 3427679) B3427679
theorem B3046825 : Blo 2081435 3046825 := bstep (se 2 (by rfl) ⟨1142559, by rfl⟩ : syracuseStep 3046825 = 2285119) B2285119
theorem B4062433 : Blo 2081435 4062433 := bstep (se 2 (by rfl) ⟨1523412, by rfl⟩ : syracuseStep 4062433 = 3046825) B3046825
theorem B5416577 : Blo 2081435 5416577 := bstep (se 2 (by rfl) ⟨2031216, by rfl⟩ : syracuseStep 5416577 = 4062433) B4062433
theorem B3611051 : Blo 2081435 3611051 := bstep (se 1 (by rfl) ⟨2708288, by rfl⟩ : syracuseStep 3611051 = 5416577) B5416577
theorem B2407367 : Blo 2081435 2407367 := bstep (se 1 (by rfl) ⟨1805525, by rfl⟩ : syracuseStep 2407367 = 3611051) B3611051
theorem B6419645 : Blo 2081435 6419645 := bstep (se 3 (by rfl) ⟨1203683, by rfl⟩ : syracuseStep 6419645 = 2407367) B2407367
theorem B4279763 : Blo 2081435 4279763 := bstep (se 1 (by rfl) ⟨3209822, by rfl⟩ : syracuseStep 4279763 = 6419645) B6419645
theorem B11412701 : Blo 2081435 11412701 := bstep (se 3 (by rfl) ⟨2139881, by rfl⟩ : syracuseStep 11412701 = 4279763) B4279763
theorem B7608467 : Blo 2081435 7608467 := bstep (se 1 (by rfl) ⟨5706350, by rfl⟩ : syracuseStep 7608467 = 11412701) B11412701
theorem B5072311 : Blo 2081435 5072311 := bstep (se 1 (by rfl) ⟨3804233, by rfl⟩ : syracuseStep 5072311 = 7608467) B7608467
theorem B27052325 : Blo 2081435 27052325 := bstep (se 4 (by rfl) ⟨2536155, by rfl⟩ : syracuseStep 27052325 = 5072311) B5072311
theorem B18034883 : Blo 2081435 18034883 := bstep (se 1 (by rfl) ⟨13526162, by rfl⟩ : syracuseStep 18034883 = 27052325) B27052325
theorem B12023255 : Blo 2081435 12023255 := bstep (se 1 (by rfl) ⟨9017441, by rfl⟩ : syracuseStep 12023255 = 18034883) B18034883
theorem B32062013 : Blo 2081435 32062013 := bstep (se 3 (by rfl) ⟨6011627, by rfl⟩ : syracuseStep 32062013 = 12023255) B12023255
theorem B21374675 : Blo 2081435 21374675 := bstep (se 1 (by rfl) ⟨16031006, by rfl⟩ : syracuseStep 21374675 = 32062013) B32062013
theorem B14249783 : Blo 2081435 14249783 := bstep (se 1 (by rfl) ⟨10687337, by rfl⟩ : syracuseStep 14249783 = 21374675) B21374675
theorem B9499855 : Blo 2081435 9499855 := bstep (se 1 (by rfl) ⟨7124891, by rfl⟩ : syracuseStep 9499855 = 14249783) B14249783
theorem B12666473 : Blo 2081435 12666473 := bstep (se 2 (by rfl) ⟨4749927, by rfl⟩ : syracuseStep 12666473 = 9499855) B9499855
theorem B8444315 : Blo 2081435 8444315 := bstep (se 1 (by rfl) ⟨6333236, by rfl⟩ : syracuseStep 8444315 = 12666473) B12666473
theorem B5629543 : Blo 2081435 5629543 := bstep (se 1 (by rfl) ⟨4222157, by rfl⟩ : syracuseStep 5629543 = 8444315) B8444315
theorem B30024229 : Blo 2081435 30024229 := bstep (se 4 (by rfl) ⟨2814771, by rfl⟩ : syracuseStep 30024229 = 5629543) B5629543
theorem B40032305 : Blo 2081435 40032305 := bstep (se 2 (by rfl) ⟨15012114, by rfl⟩ : syracuseStep 40032305 = 30024229) B30024229
theorem B26688203 : Blo 2081435 26688203 := bstep (se 1 (by rfl) ⟨20016152, by rfl⟩ : syracuseStep 26688203 = 40032305) B40032305
theorem B17792135 : Blo 2081435 17792135 := bstep (se 1 (by rfl) ⟨13344101, by rfl⟩ : syracuseStep 17792135 = 26688203) B26688203
theorem B11861423 : Blo 2081435 11861423 := bstep (se 1 (by rfl) ⟨8896067, by rfl⟩ : syracuseStep 11861423 = 17792135) B17792135
theorem B7907615 : Blo 2081435 7907615 := bstep (se 1 (by rfl) ⟨5930711, by rfl⟩ : syracuseStep 7907615 = 11861423) B11861423
theorem B5271743 : Blo 2081435 5271743 := bstep (se 1 (by rfl) ⟨3953807, by rfl⟩ : syracuseStep 5271743 = 7907615) B7907615
theorem B3514495 : Blo 2081435 3514495 := bstep (se 1 (by rfl) ⟨2635871, by rfl⟩ : syracuseStep 3514495 = 5271743) B5271743
theorem B4685993 : Blo 2081435 4685993 := bstep (se 2 (by rfl) ⟨1757247, by rfl⟩ : syracuseStep 4685993 = 3514495) B3514495
theorem B3123995 : Blo 2081435 3123995 := bstep (se 1 (by rfl) ⟨2342996, by rfl⟩ : syracuseStep 3123995 = 4685993) B4685993
theorem B2082663 : Blo 2081435 2082663 := bstep (se 1 (by rfl) ⟨1561997, by rfl⟩ : syracuseStep 2082663 = 3123995) B3123995
theorem B2343001 : Blo 2081435 2343001 := bbase (se 2 (by rfl) ⟨878625, by rfl⟩ : syracuseStep 2343001 = 1757251) (by norm_num)
theorem B3124001 : Blo 2081435 3124001 := bstep (se 2 (by rfl) ⟨1171500, by rfl⟩ : syracuseStep 3124001 = 2343001) B2343001
theorem B2082667 : Blo 2081435 2082667 := bstep (se 1 (by rfl) ⟨1562000, by rfl⟩ : syracuseStep 2082667 = 3124001) B3124001
theorem B2502029 : Blo 2081435 2502029 := bbase (se 3 (by rfl) ⟨469130, by rfl⟩ : syracuseStep 2502029 = 938261) (by norm_num)
theorem B6672077 : Blo 2081435 6672077 := bstep (se 3 (by rfl) ⟨1251014, by rfl⟩ : syracuseStep 6672077 = 2502029) B2502029
theorem B4448051 : Blo 2081435 4448051 := bstep (se 1 (by rfl) ⟨3336038, by rfl⟩ : syracuseStep 4448051 = 6672077) B6672077
theorem B2965367 : Blo 2081435 2965367 := bstep (se 1 (by rfl) ⟨2224025, by rfl⟩ : syracuseStep 2965367 = 4448051) B4448051
theorem B7907645 : Blo 2081435 7907645 := bstep (se 3 (by rfl) ⟨1482683, by rfl⟩ : syracuseStep 7907645 = 2965367) B2965367
theorem B5271763 : Blo 2081435 5271763 := bstep (se 1 (by rfl) ⟨3953822, by rfl⟩ : syracuseStep 5271763 = 7907645) B7907645
theorem B7029017 : Blo 2081435 7029017 := bstep (se 2 (by rfl) ⟨2635881, by rfl⟩ : syracuseStep 7029017 = 5271763) B5271763
theorem B4686011 : Blo 2081435 4686011 := bstep (se 1 (by rfl) ⟨3514508, by rfl⟩ : syracuseStep 4686011 = 7029017) B7029017
theorem B3124007 : Blo 2081435 3124007 := bstep (se 1 (by rfl) ⟨2343005, by rfl⟩ : syracuseStep 3124007 = 4686011) B4686011
theorem B2082671 : Blo 2081435 2082671 := bstep (se 1 (by rfl) ⟨1562003, by rfl⟩ : syracuseStep 2082671 = 3124007) B3124007
theorem B3124013 : Blo 2081435 3124013 := bbase (se 3 (by rfl) ⟨585752, by rfl⟩ : syracuseStep 3124013 = 1171505) (by norm_num)
theorem B2082675 : Blo 2081435 2082675 := bstep (se 1 (by rfl) ⟨1562006, by rfl⟩ : syracuseStep 2082675 = 3124013) B3124013
theorem B4686029 : Blo 2081435 4686029 := bbase (se 3 (by rfl) ⟨878630, by rfl⟩ : syracuseStep 4686029 = 1757261) (by norm_num)
theorem B3124019 : Blo 2081435 3124019 := bstep (se 1 (by rfl) ⟨2343014, by rfl⟩ : syracuseStep 3124019 = 4686029) B4686029
theorem B2082679 : Blo 2081435 2082679 := bstep (se 1 (by rfl) ⟨1562009, by rfl⟩ : syracuseStep 2082679 = 3124019) B3124019
theorem B2635897 : Blo 2081435 2635897 := bbase (se 2 (by rfl) ⟨988461, by rfl⟩ : syracuseStep 2635897 = 1976923) (by norm_num)
theorem B3514529 : Blo 2081435 3514529 := bstep (se 2 (by rfl) ⟨1317948, by rfl⟩ : syracuseStep 3514529 = 2635897) B2635897
theorem B2343019 : Blo 2081435 2343019 := bstep (se 1 (by rfl) ⟨1757264, by rfl⟩ : syracuseStep 2343019 = 3514529) B3514529
theorem B3124025 : Blo 2081435 3124025 := bstep (se 2 (by rfl) ⟨1171509, by rfl⟩ : syracuseStep 3124025 = 2343019) B2343019
theorem B2082683 : Blo 2081435 2082683 := bstep (se 1 (by rfl) ⟨1562012, by rfl⟩ : syracuseStep 2082683 = 3124025) B3124025
theorem B6419717 : Blo 2081435 6419717 := bbase (se 4 (by rfl) ⟨601848, by rfl⟩ : syracuseStep 6419717 = 1203697) (by norm_num)
theorem B4279811 : Blo 2081435 4279811 := bstep (se 1 (by rfl) ⟨3209858, by rfl⟩ : syracuseStep 4279811 = 6419717) B6419717
theorem B11412829 : Blo 2081435 11412829 := bstep (se 3 (by rfl) ⟨2139905, by rfl⟩ : syracuseStep 11412829 = 4279811) B4279811
theorem B60868421 : Blo 2081435 60868421 := bstep (se 4 (by rfl) ⟨5706414, by rfl⟩ : syracuseStep 60868421 = 11412829) B11412829
theorem B40578947 : Blo 2081435 40578947 := bstep (se 1 (by rfl) ⟨30434210, by rfl⟩ : syracuseStep 40578947 = 60868421) B60868421
theorem B27052631 : Blo 2081435 27052631 := bstep (se 1 (by rfl) ⟨20289473, by rfl⟩ : syracuseStep 27052631 = 40578947) B40578947
theorem B18035087 : Blo 2081435 18035087 := bstep (se 1 (by rfl) ⟨13526315, by rfl⟩ : syracuseStep 18035087 = 27052631) B27052631
theorem B192374261 : Blo 2081435 192374261 := bstep (se 5 (by rfl) ⟨9017543, by rfl⟩ : syracuseStep 192374261 = 18035087) B18035087
theorem B128249507 : Blo 2081435 128249507 := bstep (se 1 (by rfl) ⟨96187130, by rfl⟩ : syracuseStep 128249507 = 192374261) B192374261
theorem B85499671 : Blo 2081435 85499671 := bstep (se 1 (by rfl) ⟨64124753, by rfl⟩ : syracuseStep 85499671 = 128249507) B128249507
theorem B113999561 : Blo 2081435 113999561 := bstep (se 2 (by rfl) ⟨42749835, by rfl⟩ : syracuseStep 113999561 = 85499671) B85499671
theorem B75999707 : Blo 2081435 75999707 := bstep (se 1 (by rfl) ⟨56999780, by rfl⟩ : syracuseStep 75999707 = 113999561) B113999561
theorem B50666471 : Blo 2081435 50666471 := bstep (se 1 (by rfl) ⟨37999853, by rfl⟩ : syracuseStep 50666471 = 75999707) B75999707
theorem B33777647 : Blo 2081435 33777647 := bstep (se 1 (by rfl) ⟨25333235, by rfl⟩ : syracuseStep 33777647 = 50666471) B50666471
theorem B22518431 : Blo 2081435 22518431 := bstep (se 1 (by rfl) ⟨16888823, by rfl⟩ : syracuseStep 22518431 = 33777647) B33777647
theorem B15012287 : Blo 2081435 15012287 := bstep (se 1 (by rfl) ⟨11259215, by rfl⟩ : syracuseStep 15012287 = 22518431) B22518431
theorem B10008191 : Blo 2081435 10008191 := bstep (se 1 (by rfl) ⟨7506143, by rfl⟩ : syracuseStep 10008191 = 15012287) B15012287
theorem B6672127 : Blo 2081435 6672127 := bstep (se 1 (by rfl) ⟨5004095, by rfl⟩ : syracuseStep 6672127 = 10008191) B10008191
theorem B8896169 : Blo 2081435 8896169 := bstep (se 2 (by rfl) ⟨3336063, by rfl⟩ : syracuseStep 8896169 = 6672127) B6672127
theorem B23723117 : Blo 2081435 23723117 := bstep (se 3 (by rfl) ⟨4448084, by rfl⟩ : syracuseStep 23723117 = 8896169) B8896169
theorem B15815411 : Blo 2081435 15815411 := bstep (se 1 (by rfl) ⟨11861558, by rfl⟩ : syracuseStep 15815411 = 23723117) B23723117
theorem B10543607 : Blo 2081435 10543607 := bstep (se 1 (by rfl) ⟨7907705, by rfl⟩ : syracuseStep 10543607 = 15815411) B15815411
theorem B7029071 : Blo 2081435 7029071 := bstep (se 1 (by rfl) ⟨5271803, by rfl⟩ : syracuseStep 7029071 = 10543607) B10543607
theorem B4686047 : Blo 2081435 4686047 := bstep (se 1 (by rfl) ⟨3514535, by rfl⟩ : syracuseStep 4686047 = 7029071) B7029071
theorem B3124031 : Blo 2081435 3124031 := bstep (se 1 (by rfl) ⟨2343023, by rfl⟩ : syracuseStep 3124031 = 4686047) B4686047
theorem B2082687 : Blo 2081435 2082687 := bstep (se 1 (by rfl) ⟨1562015, by rfl⟩ : syracuseStep 2082687 = 3124031) B3124031
theorem B3124037 : Blo 2081435 3124037 := bbase (se 4 (by rfl) ⟨292878, by rfl⟩ : syracuseStep 3124037 = 585757) (by norm_num)
theorem B2082691 : Blo 2081435 2082691 := bstep (se 1 (by rfl) ⟨1562018, by rfl⟩ : syracuseStep 2082691 = 3124037) B3124037
theorem B3514549 : Blo 2081435 3514549 := bbase (se 5 (by rfl) ⟨164744, by rfl⟩ : syracuseStep 3514549 = 329489) (by norm_num)
theorem B4686065 : Blo 2081435 4686065 := bstep (se 2 (by rfl) ⟨1757274, by rfl⟩ : syracuseStep 4686065 = 3514549) B3514549
theorem B3124043 : Blo 2081435 3124043 := bstep (se 1 (by rfl) ⟨2343032, by rfl⟩ : syracuseStep 3124043 = 4686065) B4686065
theorem B2082695 : Blo 2081435 2082695 := bstep (se 1 (by rfl) ⟨1562021, by rfl⟩ : syracuseStep 2082695 = 3124043) B3124043
theorem B2343037 : Blo 2081435 2343037 := bbase (se 3 (by rfl) ⟨439319, by rfl⟩ : syracuseStep 2343037 = 878639) (by norm_num)
theorem B3124049 : Blo 2081435 3124049 := bstep (se 2 (by rfl) ⟨1171518, by rfl⟩ : syracuseStep 3124049 = 2343037) B2343037
theorem B2082699 : Blo 2081435 2082699 := bstep (se 1 (by rfl) ⟨1562024, by rfl⟩ : syracuseStep 2082699 = 3124049) B3124049
theorem B7029125 : Blo 2081435 7029125 := bbase (se 4 (by rfl) ⟨658980, by rfl⟩ : syracuseStep 7029125 = 1317961) (by norm_num)
theorem B4686083 : Blo 2081435 4686083 := bstep (se 1 (by rfl) ⟨3514562, by rfl⟩ : syracuseStep 4686083 = 7029125) B7029125
theorem B3124055 : Blo 2081435 3124055 := bstep (se 1 (by rfl) ⟨2343041, by rfl⟩ : syracuseStep 3124055 = 4686083) B4686083
theorem B2082703 : Blo 2081435 2082703 := bstep (se 1 (by rfl) ⟨1562027, by rfl⟩ : syracuseStep 2082703 = 3124055) B3124055
theorem B3124061 : Blo 2081435 3124061 := bbase (se 3 (by rfl) ⟨585761, by rfl⟩ : syracuseStep 3124061 = 1171523) (by norm_num)
theorem B2082707 : Blo 2081435 2082707 := bstep (se 1 (by rfl) ⟨1562030, by rfl⟩ : syracuseStep 2082707 = 3124061) B3124061
theorem B4686101 : Blo 2081435 4686101 := bbase (se 6 (by rfl) ⟨109830, by rfl⟩ : syracuseStep 4686101 = 219661) (by norm_num)
theorem B3124067 : Blo 2081435 3124067 := bstep (se 1 (by rfl) ⟨2343050, by rfl⟩ : syracuseStep 3124067 = 4686101) B4686101
theorem B2082711 : Blo 2081435 2082711 := bstep (se 1 (by rfl) ⟨1562033, by rfl⟩ : syracuseStep 2082711 = 3124067) B3124067
theorem B7907813 : Blo 2081435 7907813 := bbase (se 4 (by rfl) ⟨741357, by rfl⟩ : syracuseStep 7907813 = 1482715) (by norm_num)
theorem B5271875 : Blo 2081435 5271875 := bstep (se 1 (by rfl) ⟨3953906, by rfl⟩ : syracuseStep 5271875 = 7907813) B7907813
theorem B3514583 : Blo 2081435 3514583 := bstep (se 1 (by rfl) ⟨2635937, by rfl⟩ : syracuseStep 3514583 = 5271875) B5271875
theorem B2343055 : Blo 2081435 2343055 := bstep (se 1 (by rfl) ⟨1757291, by rfl⟩ : syracuseStep 2343055 = 3514583) B3514583
theorem B3124073 : Blo 2081435 3124073 := bstep (se 2 (by rfl) ⟨1171527, by rfl⟩ : syracuseStep 3124073 = 2343055) B2343055
theorem B2082715 : Blo 2081435 2082715 := bstep (se 1 (by rfl) ⟨1562036, by rfl⟩ : syracuseStep 2082715 = 3124073) B3124073
theorem B5004173 : Blo 2081435 5004173 := bbase (se 3 (by rfl) ⟨938282, by rfl⟩ : syracuseStep 5004173 = 1876565) (by norm_num)
theorem B3336115 : Blo 2081435 3336115 := bstep (se 1 (by rfl) ⟨2502086, by rfl⟩ : syracuseStep 3336115 = 5004173) B5004173
theorem B4448153 : Blo 2081435 4448153 := bstep (se 2 (by rfl) ⟨1668057, by rfl⟩ : syracuseStep 4448153 = 3336115) B3336115
theorem B11861741 : Blo 2081435 11861741 := bstep (se 3 (by rfl) ⟨2224076, by rfl⟩ : syracuseStep 11861741 = 4448153) B4448153
theorem B7907827 : Blo 2081435 7907827 := bstep (se 1 (by rfl) ⟨5930870, by rfl⟩ : syracuseStep 7907827 = 11861741) B11861741
theorem B10543769 : Blo 2081435 10543769 := bstep (se 2 (by rfl) ⟨3953913, by rfl⟩ : syracuseStep 10543769 = 7907827) B7907827
theorem B7029179 : Blo 2081435 7029179 := bstep (se 1 (by rfl) ⟨5271884, by rfl⟩ : syracuseStep 7029179 = 10543769) B10543769
theorem B4686119 : Blo 2081435 4686119 := bstep (se 1 (by rfl) ⟨3514589, by rfl⟩ : syracuseStep 4686119 = 7029179) B7029179
theorem B3124079 : Blo 2081435 3124079 := bstep (se 1 (by rfl) ⟨2343059, by rfl⟩ : syracuseStep 3124079 = 4686119) B4686119
theorem B2082719 : Blo 2081435 2082719 := bstep (se 1 (by rfl) ⟨1562039, by rfl⟩ : syracuseStep 2082719 = 3124079) B3124079
theorem B3124085 : Blo 2081435 3124085 := bbase (se 5 (by rfl) ⟨146441, by rfl⟩ : syracuseStep 3124085 = 292883) (by norm_num)
theorem B2082723 : Blo 2081435 2082723 := bstep (se 1 (by rfl) ⟨1562042, by rfl⟩ : syracuseStep 2082723 = 3124085) B3124085
theorem B3166717 : Blo 2081435 3166717 := bbase (se 3 (by rfl) ⟨593759, by rfl⟩ : syracuseStep 3166717 = 1187519) (by norm_num)
theorem B4222289 : Blo 2081435 4222289 := bstep (se 2 (by rfl) ⟨1583358, by rfl⟩ : syracuseStep 4222289 = 3166717) B3166717
theorem B2814859 : Blo 2081435 2814859 := bstep (se 1 (by rfl) ⟨2111144, by rfl⟩ : syracuseStep 2814859 = 4222289) B4222289
theorem B3753145 : Blo 2081435 3753145 := bstep (se 2 (by rfl) ⟨1407429, by rfl⟩ : syracuseStep 3753145 = 2814859) B2814859
theorem B5004193 : Blo 2081435 5004193 := bstep (se 2 (by rfl) ⟨1876572, by rfl⟩ : syracuseStep 5004193 = 3753145) B3753145
theorem B6672257 : Blo 2081435 6672257 := bstep (se 2 (by rfl) ⟨2502096, by rfl⟩ : syracuseStep 6672257 = 5004193) B5004193
theorem B4448171 : Blo 2081435 4448171 := bstep (se 1 (by rfl) ⟨3336128, by rfl⟩ : syracuseStep 4448171 = 6672257) B6672257
theorem B2965447 : Blo 2081435 2965447 := bstep (se 1 (by rfl) ⟨2224085, by rfl⟩ : syracuseStep 2965447 = 4448171) B4448171
theorem B3953929 : Blo 2081435 3953929 := bstep (se 2 (by rfl) ⟨1482723, by rfl⟩ : syracuseStep 3953929 = 2965447) B2965447
theorem B5271905 : Blo 2081435 5271905 := bstep (se 2 (by rfl) ⟨1976964, by rfl⟩ : syracuseStep 5271905 = 3953929) B3953929
theorem B3514603 : Blo 2081435 3514603 := bstep (se 1 (by rfl) ⟨2635952, by rfl⟩ : syracuseStep 3514603 = 5271905) B5271905
theorem B4686137 : Blo 2081435 4686137 := bstep (se 2 (by rfl) ⟨1757301, by rfl⟩ : syracuseStep 4686137 = 3514603) B3514603
theorem B3124091 : Blo 2081435 3124091 := bstep (se 1 (by rfl) ⟨2343068, by rfl⟩ : syracuseStep 3124091 = 4686137) B4686137
theorem B2082727 : Blo 2081435 2082727 := bstep (se 1 (by rfl) ⟨1562045, by rfl⟩ : syracuseStep 2082727 = 3124091) B3124091
theorem B2343073 : Blo 2081435 2343073 := bbase (se 2 (by rfl) ⟨878652, by rfl⟩ : syracuseStep 2343073 = 1757305) (by norm_num)
theorem B3124097 : Blo 2081435 3124097 := bstep (se 2 (by rfl) ⟨1171536, by rfl⟩ : syracuseStep 3124097 = 2343073) B2343073
theorem B2082731 : Blo 2081435 2082731 := bstep (se 1 (by rfl) ⟨1562048, by rfl⟩ : syracuseStep 2082731 = 3124097) B3124097
theorem B5271925 : Blo 2081435 5271925 := bbase (se 5 (by rfl) ⟨247121, by rfl⟩ : syracuseStep 5271925 = 494243) (by norm_num)
theorem B7029233 : Blo 2081435 7029233 := bstep (se 2 (by rfl) ⟨2635962, by rfl⟩ : syracuseStep 7029233 = 5271925) B5271925
theorem B4686155 : Blo 2081435 4686155 := bstep (se 1 (by rfl) ⟨3514616, by rfl⟩ : syracuseStep 4686155 = 7029233) B7029233
theorem B3124103 : Blo 2081435 3124103 := bstep (se 1 (by rfl) ⟨2343077, by rfl⟩ : syracuseStep 3124103 = 4686155) B4686155
theorem B2082735 : Blo 2081435 2082735 := bstep (se 1 (by rfl) ⟨1562051, by rfl⟩ : syracuseStep 2082735 = 3124103) B3124103
theorem B3124109 : Blo 2081435 3124109 := bbase (se 3 (by rfl) ⟨585770, by rfl⟩ : syracuseStep 3124109 = 1171541) (by norm_num)
theorem B2082739 : Blo 2081435 2082739 := bstep (se 1 (by rfl) ⟨1562054, by rfl⟩ : syracuseStep 2082739 = 3124109) B3124109
theorem B4686173 : Blo 2081435 4686173 := bbase (se 3 (by rfl) ⟨878657, by rfl⟩ : syracuseStep 4686173 = 1757315) (by norm_num)
theorem B3124115 : Blo 2081435 3124115 := bstep (se 1 (by rfl) ⟨2343086, by rfl⟩ : syracuseStep 3124115 = 4686173) B4686173
theorem B2082743 : Blo 2081435 2082743 := bstep (se 1 (by rfl) ⟨1562057, by rfl⟩ : syracuseStep 2082743 = 3124115) B3124115
theorem B3514637 : Blo 2081435 3514637 := bbase (se 3 (by rfl) ⟨658994, by rfl⟩ : syracuseStep 3514637 = 1317989) (by norm_num)
theorem B2343091 : Blo 2081435 2343091 := bstep (se 1 (by rfl) ⟨1757318, by rfl⟩ : syracuseStep 2343091 = 3514637) B3514637
theorem B3124121 : Blo 2081435 3124121 := bstep (se 2 (by rfl) ⟨1171545, by rfl⟩ : syracuseStep 3124121 = 2343091) B2343091
theorem B2082747 : Blo 2081435 2082747 := bstep (se 1 (by rfl) ⟨1562060, by rfl⟩ : syracuseStep 2082747 = 3124121) B3124121
theorem B17792885 : Blo 2081435 17792885 := bbase (se 5 (by rfl) ⟨834041, by rfl⟩ : syracuseStep 17792885 = 1668083) (by norm_num)
theorem B11861923 : Blo 2081435 11861923 := bstep (se 1 (by rfl) ⟨8896442, by rfl⟩ : syracuseStep 11861923 = 17792885) B17792885
theorem B15815897 : Blo 2081435 15815897 := bstep (se 2 (by rfl) ⟨5930961, by rfl⟩ : syracuseStep 15815897 = 11861923) B11861923
theorem B10543931 : Blo 2081435 10543931 := bstep (se 1 (by rfl) ⟨7907948, by rfl⟩ : syracuseStep 10543931 = 15815897) B15815897
theorem B7029287 : Blo 2081435 7029287 := bstep (se 1 (by rfl) ⟨5271965, by rfl⟩ : syracuseStep 7029287 = 10543931) B10543931
theorem B4686191 : Blo 2081435 4686191 := bstep (se 1 (by rfl) ⟨3514643, by rfl⟩ : syracuseStep 4686191 = 7029287) B7029287
theorem B3124127 : Blo 2081435 3124127 := bstep (se 1 (by rfl) ⟨2343095, by rfl⟩ : syracuseStep 3124127 = 4686191) B4686191
theorem B2082751 : Blo 2081435 2082751 := bstep (se 1 (by rfl) ⟨1562063, by rfl⟩ : syracuseStep 2082751 = 3124127) B3124127
theorem B3124133 : Blo 2081435 3124133 := bbase (se 4 (by rfl) ⟨292887, by rfl⟩ : syracuseStep 3124133 = 585775) (by norm_num)
theorem B2082755 : Blo 2081435 2082755 := bstep (se 1 (by rfl) ⟨1562066, by rfl⟩ : syracuseStep 2082755 = 3124133) B3124133
theorem B2635993 : Blo 2081435 2635993 := bbase (se 2 (by rfl) ⟨988497, by rfl⟩ : syracuseStep 2635993 = 1976995) (by norm_num)
theorem B3514657 : Blo 2081435 3514657 := bstep (se 2 (by rfl) ⟨1317996, by rfl⟩ : syracuseStep 3514657 = 2635993) B2635993
theorem B4686209 : Blo 2081435 4686209 := bstep (se 2 (by rfl) ⟨1757328, by rfl⟩ : syracuseStep 4686209 = 3514657) B3514657
theorem B3124139 : Blo 2081435 3124139 := bstep (se 1 (by rfl) ⟨2343104, by rfl⟩ : syracuseStep 3124139 = 4686209) B4686209
theorem B2082759 : Blo 2081435 2082759 := bstep (se 1 (by rfl) ⟨1562069, by rfl⟩ : syracuseStep 2082759 = 3124139) B3124139
theorem B2343109 : Blo 2081435 2343109 := bbase (se 4 (by rfl) ⟨219666, by rfl⟩ : syracuseStep 2343109 = 439333) (by norm_num)
theorem B3124145 : Blo 2081435 3124145 := bstep (se 2 (by rfl) ⟨1171554, by rfl⟩ : syracuseStep 3124145 = 2343109) B2343109
theorem B2082763 : Blo 2081435 2082763 := bstep (se 1 (by rfl) ⟨1562072, by rfl⟩ : syracuseStep 2082763 = 3124145) B3124145
theorem B3954005 : Blo 2081435 3954005 := bbase (se 16 (by rfl) ⟨90, by rfl⟩ : syracuseStep 3954005 = 181) (by norm_num)
theorem B2636003 : Blo 2081435 2636003 := bstep (se 1 (by rfl) ⟨1977002, by rfl⟩ : syracuseStep 2636003 = 3954005) B3954005
theorem B7029341 : Blo 2081435 7029341 := bstep (se 3 (by rfl) ⟨1318001, by rfl⟩ : syracuseStep 7029341 = 2636003) B2636003
theorem B4686227 : Blo 2081435 4686227 := bstep (se 1 (by rfl) ⟨3514670, by rfl⟩ : syracuseStep 4686227 = 7029341) B7029341
theorem B3124151 : Blo 2081435 3124151 := bstep (se 1 (by rfl) ⟨2343113, by rfl⟩ : syracuseStep 3124151 = 4686227) B4686227
theorem B2082767 : Blo 2081435 2082767 := bstep (se 1 (by rfl) ⟨1562075, by rfl⟩ : syracuseStep 2082767 = 3124151) B3124151
theorem B3124157 : Blo 2081435 3124157 := bbase (se 3 (by rfl) ⟨585779, by rfl⟩ : syracuseStep 3124157 = 1171559) (by norm_num)
theorem B2082771 : Blo 2081435 2082771 := bstep (se 1 (by rfl) ⟨1562078, by rfl⟩ : syracuseStep 2082771 = 3124157) B3124157
theorem B4686245 : Blo 2081435 4686245 := bbase (se 4 (by rfl) ⟨439335, by rfl⟩ : syracuseStep 4686245 = 878671) (by norm_num)
theorem B3124163 : Blo 2081435 3124163 := bstep (se 1 (by rfl) ⟨2343122, by rfl⟩ : syracuseStep 3124163 = 4686245) B4686245
theorem B2082775 : Blo 2081435 2082775 := bstep (se 1 (by rfl) ⟨1562081, by rfl⟩ : syracuseStep 2082775 = 3124163) B3124163
theorem B5272037 : Blo 2081435 5272037 := bbase (se 4 (by rfl) ⟨494253, by rfl⟩ : syracuseStep 5272037 = 988507) (by norm_num)
theorem B3514691 : Blo 2081435 3514691 := bstep (se 1 (by rfl) ⟨2636018, by rfl⟩ : syracuseStep 3514691 = 5272037) B5272037
theorem B2343127 : Blo 2081435 2343127 := bstep (se 1 (by rfl) ⟨1757345, by rfl⟩ : syracuseStep 2343127 = 3514691) B3514691
theorem B3124169 : Blo 2081435 3124169 := bstep (se 2 (by rfl) ⟨1171563, by rfl⟩ : syracuseStep 3124169 = 2343127) B2343127
theorem B2082779 : Blo 2081435 2082779 := bstep (se 1 (by rfl) ⟨1562084, by rfl⟩ : syracuseStep 2082779 = 3124169) B3124169
theorem B2224145 : Blo 2081435 2224145 := bbase (se 2 (by rfl) ⟨834054, by rfl⟩ : syracuseStep 2224145 = 1668109) (by norm_num)
theorem B5931053 : Blo 2081435 5931053 := bstep (se 3 (by rfl) ⟨1112072, by rfl⟩ : syracuseStep 5931053 = 2224145) B2224145
theorem B3954035 : Blo 2081435 3954035 := bstep (se 1 (by rfl) ⟨2965526, by rfl⟩ : syracuseStep 3954035 = 5931053) B5931053
theorem B10544093 : Blo 2081435 10544093 := bstep (se 3 (by rfl) ⟨1977017, by rfl⟩ : syracuseStep 10544093 = 3954035) B3954035
theorem B7029395 : Blo 2081435 7029395 := bstep (se 1 (by rfl) ⟨5272046, by rfl⟩ : syracuseStep 7029395 = 10544093) B10544093
theorem B4686263 : Blo 2081435 4686263 := bstep (se 1 (by rfl) ⟨3514697, by rfl⟩ : syracuseStep 4686263 = 7029395) B7029395
theorem B3124175 : Blo 2081435 3124175 := bstep (se 1 (by rfl) ⟨2343131, by rfl⟩ : syracuseStep 3124175 = 4686263) B4686263
theorem B2082783 : Blo 2081435 2082783 := bstep (se 1 (by rfl) ⟨1562087, by rfl⟩ : syracuseStep 2082783 = 3124175) B3124175
theorem B3124181 : Blo 2081435 3124181 := bbase (se 7 (by rfl) ⟨36611, by rfl⟩ : syracuseStep 3124181 = 73223) (by norm_num)
theorem B2082787 : Blo 2081435 2082787 := bstep (se 1 (by rfl) ⟨1562090, by rfl⟩ : syracuseStep 2082787 = 3124181) B3124181
theorem B7908101 : Blo 2081435 7908101 := bbase (se 4 (by rfl) ⟨741384, by rfl⟩ : syracuseStep 7908101 = 1482769) (by norm_num)
theorem B5272067 : Blo 2081435 5272067 := bstep (se 1 (by rfl) ⟨3954050, by rfl⟩ : syracuseStep 5272067 = 7908101) B7908101
theorem B3514711 : Blo 2081435 3514711 := bstep (se 1 (by rfl) ⟨2636033, by rfl⟩ : syracuseStep 3514711 = 5272067) B5272067
theorem B4686281 : Blo 2081435 4686281 := bstep (se 2 (by rfl) ⟨1757355, by rfl⟩ : syracuseStep 4686281 = 3514711) B3514711
theorem B3124187 : Blo 2081435 3124187 := bstep (se 1 (by rfl) ⟨2343140, by rfl⟩ : syracuseStep 3124187 = 4686281) B4686281
theorem B2082791 : Blo 2081435 2082791 := bstep (se 1 (by rfl) ⟨1562093, by rfl⟩ : syracuseStep 2082791 = 3124187) B3124187
theorem B2343145 : Blo 2081435 2343145 := bbase (se 2 (by rfl) ⟨878679, by rfl⟩ : syracuseStep 2343145 = 1757359) (by norm_num)
theorem B3124193 : Blo 2081435 3124193 := bstep (se 2 (by rfl) ⟨1171572, by rfl⟩ : syracuseStep 3124193 = 2343145) B2343145
theorem B2082795 : Blo 2081435 2082795 := bstep (se 1 (by rfl) ⟨1562096, by rfl⟩ : syracuseStep 2082795 = 3124193) B3124193
theorem B11862197 : Blo 2081435 11862197 := bbase (se 5 (by rfl) ⟨556040, by rfl⟩ : syracuseStep 11862197 = 1112081) (by norm_num)
theorem B7908131 : Blo 2081435 7908131 := bstep (se 1 (by rfl) ⟨5931098, by rfl⟩ : syracuseStep 7908131 = 11862197) B11862197
theorem B5272087 : Blo 2081435 5272087 := bstep (se 1 (by rfl) ⟨3954065, by rfl⟩ : syracuseStep 5272087 = 7908131) B7908131
theorem B7029449 : Blo 2081435 7029449 := bstep (se 2 (by rfl) ⟨2636043, by rfl⟩ : syracuseStep 7029449 = 5272087) B5272087
theorem B4686299 : Blo 2081435 4686299 := bstep (se 1 (by rfl) ⟨3514724, by rfl⟩ : syracuseStep 4686299 = 7029449) B7029449
theorem B3124199 : Blo 2081435 3124199 := bstep (se 1 (by rfl) ⟨2343149, by rfl⟩ : syracuseStep 3124199 = 4686299) B4686299
theorem B2082799 : Blo 2081435 2082799 := bstep (se 1 (by rfl) ⟨1562099, by rfl⟩ : syracuseStep 2082799 = 3124199) B3124199
theorem B3124205 : Blo 2081435 3124205 := bbase (se 3 (by rfl) ⟨585788, by rfl⟩ : syracuseStep 3124205 = 1171577) (by norm_num)
theorem B2082803 : Blo 2081435 2082803 := bstep (se 1 (by rfl) ⟨1562102, by rfl⟩ : syracuseStep 2082803 = 3124205) B3124205
theorem B4686317 : Blo 2081435 4686317 := bbase (se 3 (by rfl) ⟨878684, by rfl⟩ : syracuseStep 4686317 = 1757369) (by norm_num)
theorem B3124211 : Blo 2081435 3124211 := bstep (se 1 (by rfl) ⟨2343158, by rfl⟩ : syracuseStep 3124211 = 4686317) B4686317
theorem B2082807 : Blo 2081435 2082807 := bstep (se 1 (by rfl) ⟨1562105, by rfl⟩ : syracuseStep 2082807 = 3124211) B3124211
theorem B3006029 : Blo 2081435 3006029 := bbase (se 3 (by rfl) ⟨563630, by rfl⟩ : syracuseStep 3006029 = 1127261) (by norm_num)
theorem B8016077 : Blo 2081435 8016077 := bstep (se 3 (by rfl) ⟨1503014, by rfl⟩ : syracuseStep 8016077 = 3006029) B3006029
theorem B5344051 : Blo 2081435 5344051 := bstep (se 1 (by rfl) ⟨4008038, by rfl⟩ : syracuseStep 5344051 = 8016077) B8016077
theorem B7125401 : Blo 2081435 7125401 := bstep (se 2 (by rfl) ⟨2672025, by rfl⟩ : syracuseStep 7125401 = 5344051) B5344051
theorem B4750267 : Blo 2081435 4750267 := bstep (se 1 (by rfl) ⟨3562700, by rfl⟩ : syracuseStep 4750267 = 7125401) B7125401
theorem B6333689 : Blo 2081435 6333689 := bstep (se 2 (by rfl) ⟨2375133, by rfl⟩ : syracuseStep 6333689 = 4750267) B4750267
theorem B4222459 : Blo 2081435 4222459 := bstep (se 1 (by rfl) ⟨3166844, by rfl⟩ : syracuseStep 4222459 = 6333689) B6333689
theorem B22519781 : Blo 2081435 22519781 := bstep (se 4 (by rfl) ⟨2111229, by rfl⟩ : syracuseStep 22519781 = 4222459) B4222459
theorem B15013187 : Blo 2081435 15013187 := bstep (se 1 (by rfl) ⟨11259890, by rfl⟩ : syracuseStep 15013187 = 22519781) B22519781
theorem B10008791 : Blo 2081435 10008791 := bstep (se 1 (by rfl) ⟨7506593, by rfl⟩ : syracuseStep 10008791 = 15013187) B15013187
theorem B6672527 : Blo 2081435 6672527 := bstep (se 1 (by rfl) ⟨5004395, by rfl⟩ : syracuseStep 6672527 = 10008791) B10008791
theorem B4448351 : Blo 2081435 4448351 := bstep (se 1 (by rfl) ⟨3336263, by rfl⟩ : syracuseStep 4448351 = 6672527) B6672527
theorem B2965567 : Blo 2081435 2965567 := bstep (se 1 (by rfl) ⟨2224175, by rfl⟩ : syracuseStep 2965567 = 4448351) B4448351
theorem B3954089 : Blo 2081435 3954089 := bstep (se 2 (by rfl) ⟨1482783, by rfl⟩ : syracuseStep 3954089 = 2965567) B2965567
theorem B2636059 : Blo 2081435 2636059 := bstep (se 1 (by rfl) ⟨1977044, by rfl⟩ : syracuseStep 2636059 = 3954089) B3954089
theorem B3514745 : Blo 2081435 3514745 := bstep (se 2 (by rfl) ⟨1318029, by rfl⟩ : syracuseStep 3514745 = 2636059) B2636059
theorem B2343163 : Blo 2081435 2343163 := bstep (se 1 (by rfl) ⟨1757372, by rfl⟩ : syracuseStep 2343163 = 3514745) B3514745
theorem B3124217 : Blo 2081435 3124217 := bstep (se 2 (by rfl) ⟨1171581, by rfl⟩ : syracuseStep 3124217 = 2343163) B2343163
theorem B2082811 : Blo 2081435 2082811 := bstep (se 1 (by rfl) ⟨1562108, by rfl⟩ : syracuseStep 2082811 = 3124217) B3124217
theorem B2672029 : Blo 2081435 2672029 := bbase (se 3 (by rfl) ⟨501005, by rfl⟩ : syracuseStep 2672029 = 1002011) (by norm_num)
theorem B3562705 : Blo 2081435 3562705 := bstep (se 2 (by rfl) ⟨1336014, by rfl⟩ : syracuseStep 3562705 = 2672029) B2672029
theorem B4750273 : Blo 2081435 4750273 := bstep (se 2 (by rfl) ⟨1781352, by rfl⟩ : syracuseStep 4750273 = 3562705) B3562705
theorem B25334789 : Blo 2081435 25334789 := bstep (se 4 (by rfl) ⟨2375136, by rfl⟩ : syracuseStep 25334789 = 4750273) B4750273
theorem B67559437 : Blo 2081435 67559437 := bstep (se 3 (by rfl) ⟨12667394, by rfl⟩ : syracuseStep 67559437 = 25334789) B25334789
theorem B90079249 : Blo 2081435 90079249 := bstep (se 2 (by rfl) ⟨33779718, by rfl⟩ : syracuseStep 90079249 = 67559437) B67559437
theorem B120105665 : Blo 2081435 120105665 := bstep (se 2 (by rfl) ⟨45039624, by rfl⟩ : syracuseStep 120105665 = 90079249) B90079249
theorem B80070443 : Blo 2081435 80070443 := bstep (se 1 (by rfl) ⟨60052832, by rfl⟩ : syracuseStep 80070443 = 120105665) B120105665
theorem B53380295 : Blo 2081435 53380295 := bstep (se 1 (by rfl) ⟨40035221, by rfl⟩ : syracuseStep 53380295 = 80070443) B80070443
theorem B35586863 : Blo 2081435 35586863 := bstep (se 1 (by rfl) ⟨26690147, by rfl⟩ : syracuseStep 35586863 = 53380295) B53380295
theorem B23724575 : Blo 2081435 23724575 := bstep (se 1 (by rfl) ⟨17793431, by rfl⟩ : syracuseStep 23724575 = 35586863) B35586863
theorem B15816383 : Blo 2081435 15816383 := bstep (se 1 (by rfl) ⟨11862287, by rfl⟩ : syracuseStep 15816383 = 23724575) B23724575
theorem B10544255 : Blo 2081435 10544255 := bstep (se 1 (by rfl) ⟨7908191, by rfl⟩ : syracuseStep 10544255 = 15816383) B15816383
theorem B7029503 : Blo 2081435 7029503 := bstep (se 1 (by rfl) ⟨5272127, by rfl⟩ : syracuseStep 7029503 = 10544255) B10544255
theorem B4686335 : Blo 2081435 4686335 := bstep (se 1 (by rfl) ⟨3514751, by rfl⟩ : syracuseStep 4686335 = 7029503) B7029503
theorem B3124223 : Blo 2081435 3124223 := bstep (se 1 (by rfl) ⟨2343167, by rfl⟩ : syracuseStep 3124223 = 4686335) B4686335
theorem B2082815 : Blo 2081435 2082815 := bstep (se 1 (by rfl) ⟨1562111, by rfl⟩ : syracuseStep 2082815 = 3124223) B3124223
theorem B3124229 : Blo 2081435 3124229 := bbase (se 4 (by rfl) ⟨292896, by rfl⟩ : syracuseStep 3124229 = 585793) (by norm_num)
theorem B2082819 : Blo 2081435 2082819 := bstep (se 1 (by rfl) ⟨1562114, by rfl⟩ : syracuseStep 2082819 = 3124229) B3124229
theorem B3514765 : Blo 2081435 3514765 := bbase (se 3 (by rfl) ⟨659018, by rfl⟩ : syracuseStep 3514765 = 1318037) (by norm_num)
theorem B4686353 : Blo 2081435 4686353 := bstep (se 2 (by rfl) ⟨1757382, by rfl⟩ : syracuseStep 4686353 = 3514765) B3514765
theorem B3124235 : Blo 2081435 3124235 := bstep (se 1 (by rfl) ⟨2343176, by rfl⟩ : syracuseStep 3124235 = 4686353) B4686353
theorem B2082823 : Blo 2081435 2082823 := bstep (se 1 (by rfl) ⟨1562117, by rfl⟩ : syracuseStep 2082823 = 3124235) B3124235
theorem B2343181 : Blo 2081435 2343181 := bbase (se 3 (by rfl) ⟨439346, by rfl⟩ : syracuseStep 2343181 = 878693) (by norm_num)
theorem B3124241 : Blo 2081435 3124241 := bstep (se 2 (by rfl) ⟨1171590, by rfl⟩ : syracuseStep 3124241 = 2343181) B2343181
theorem B2082827 : Blo 2081435 2082827 := bstep (se 1 (by rfl) ⟨1562120, by rfl⟩ : syracuseStep 2082827 = 3124241) B3124241
theorem B7029557 : Blo 2081435 7029557 := bbase (se 5 (by rfl) ⟨329510, by rfl⟩ : syracuseStep 7029557 = 659021) (by norm_num)
theorem B4686371 : Blo 2081435 4686371 := bstep (se 1 (by rfl) ⟨3514778, by rfl⟩ : syracuseStep 4686371 = 7029557) B7029557
theorem B3124247 : Blo 2081435 3124247 := bstep (se 1 (by rfl) ⟨2343185, by rfl⟩ : syracuseStep 3124247 = 4686371) B4686371
theorem B2082831 : Blo 2081435 2082831 := bstep (se 1 (by rfl) ⟨1562123, by rfl⟩ : syracuseStep 2082831 = 3124247) B3124247
theorem B3124253 : Blo 2081435 3124253 := bbase (se 3 (by rfl) ⟨585797, by rfl⟩ : syracuseStep 3124253 = 1171595) (by norm_num)
theorem B2082835 : Blo 2081435 2082835 := bstep (se 1 (by rfl) ⟨1562126, by rfl⟩ : syracuseStep 2082835 = 3124253) B3124253
theorem B4686389 : Blo 2081435 4686389 := bbase (se 5 (by rfl) ⟨219674, by rfl⟩ : syracuseStep 4686389 = 439349) (by norm_num)
theorem B3124259 : Blo 2081435 3124259 := bstep (se 1 (by rfl) ⟨2343194, by rfl⟩ : syracuseStep 3124259 = 4686389) B4686389
theorem B2082839 : Blo 2081435 2082839 := bstep (se 1 (by rfl) ⟨1562129, by rfl⟩ : syracuseStep 2082839 = 3124259) B3124259
theorem B8896837 : Blo 2081435 8896837 := bbase (se 4 (by rfl) ⟨834078, by rfl⟩ : syracuseStep 8896837 = 1668157) (by norm_num)
theorem B11862449 : Blo 2081435 11862449 := bstep (se 2 (by rfl) ⟨4448418, by rfl⟩ : syracuseStep 11862449 = 8896837) B8896837
theorem B7908299 : Blo 2081435 7908299 := bstep (se 1 (by rfl) ⟨5931224, by rfl⟩ : syracuseStep 7908299 = 11862449) B11862449
theorem B5272199 : Blo 2081435 5272199 := bstep (se 1 (by rfl) ⟨3954149, by rfl⟩ : syracuseStep 5272199 = 7908299) B7908299
theorem B3514799 : Blo 2081435 3514799 := bstep (se 1 (by rfl) ⟨2636099, by rfl⟩ : syracuseStep 3514799 = 5272199) B5272199
theorem B2343199 : Blo 2081435 2343199 := bstep (se 1 (by rfl) ⟨1757399, by rfl⟩ : syracuseStep 2343199 = 3514799) B3514799
theorem B3124265 : Blo 2081435 3124265 := bstep (se 2 (by rfl) ⟨1171599, by rfl⟩ : syracuseStep 3124265 = 2343199) B2343199
theorem B2082843 : Blo 2081435 2082843 := bstep (se 1 (by rfl) ⟨1562132, by rfl⟩ : syracuseStep 2082843 = 3124265) B3124265
theorem B8896853 : Blo 2081435 8896853 := bbase (se 10 (by rfl) ⟨13032, by rfl⟩ : syracuseStep 8896853 = 26065) (by norm_num)
theorem B5931235 : Blo 2081435 5931235 := bstep (se 1 (by rfl) ⟨4448426, by rfl⟩ : syracuseStep 5931235 = 8896853) B8896853
theorem B7908313 : Blo 2081435 7908313 := bstep (se 2 (by rfl) ⟨2965617, by rfl⟩ : syracuseStep 7908313 = 5931235) B5931235
theorem B10544417 : Blo 2081435 10544417 := bstep (se 2 (by rfl) ⟨3954156, by rfl⟩ : syracuseStep 10544417 = 7908313) B7908313
theorem B7029611 : Blo 2081435 7029611 := bstep (se 1 (by rfl) ⟨5272208, by rfl⟩ : syracuseStep 7029611 = 10544417) B10544417
theorem B4686407 : Blo 2081435 4686407 := bstep (se 1 (by rfl) ⟨3514805, by rfl⟩ : syracuseStep 4686407 = 7029611) B7029611
theorem B3124271 : Blo 2081435 3124271 := bstep (se 1 (by rfl) ⟨2343203, by rfl⟩ : syracuseStep 3124271 = 4686407) B4686407
theorem B2082847 : Blo 2081435 2082847 := bstep (se 1 (by rfl) ⟨1562135, by rfl⟩ : syracuseStep 2082847 = 3124271) B3124271
theorem B3124277 : Blo 2081435 3124277 := bbase (se 5 (by rfl) ⟨146450, by rfl⟩ : syracuseStep 3124277 = 292901) (by norm_num)
theorem B2082851 : Blo 2081435 2082851 := bstep (se 1 (by rfl) ⟨1562138, by rfl⟩ : syracuseStep 2082851 = 3124277) B3124277
theorem B5272229 : Blo 2081435 5272229 := bbase (se 4 (by rfl) ⟨494271, by rfl⟩ : syracuseStep 5272229 = 988543) (by norm_num)
theorem B3514819 : Blo 2081435 3514819 := bstep (se 1 (by rfl) ⟨2636114, by rfl⟩ : syracuseStep 3514819 = 5272229) B5272229
theorem B4686425 : Blo 2081435 4686425 := bstep (se 2 (by rfl) ⟨1757409, by rfl⟩ : syracuseStep 4686425 = 3514819) B3514819
theorem B3124283 : Blo 2081435 3124283 := bstep (se 1 (by rfl) ⟨2343212, by rfl⟩ : syracuseStep 3124283 = 4686425) B4686425
theorem B2082855 : Blo 2081435 2082855 := bstep (se 1 (by rfl) ⟨1562141, by rfl⟩ : syracuseStep 2082855 = 3124283) B3124283
theorem B2343217 : Blo 2081435 2343217 := bbase (se 2 (by rfl) ⟨878706, by rfl⟩ : syracuseStep 2343217 = 1757413) (by norm_num)
theorem B3124289 : Blo 2081435 3124289 := bstep (se 2 (by rfl) ⟨1171608, by rfl⟩ : syracuseStep 3124289 = 2343217) B2343217
theorem B2082859 : Blo 2081435 2082859 := bstep (se 1 (by rfl) ⟨1562144, by rfl⟩ : syracuseStep 2082859 = 3124289) B3124289
theorem B4448461 : Blo 2081435 4448461 := bbase (se 3 (by rfl) ⟨834086, by rfl⟩ : syracuseStep 4448461 = 1668173) (by norm_num)
theorem B5931281 : Blo 2081435 5931281 := bstep (se 2 (by rfl) ⟨2224230, by rfl⟩ : syracuseStep 5931281 = 4448461) B4448461
theorem B3954187 : Blo 2081435 3954187 := bstep (se 1 (by rfl) ⟨2965640, by rfl⟩ : syracuseStep 3954187 = 5931281) B5931281
theorem B5272249 : Blo 2081435 5272249 := bstep (se 2 (by rfl) ⟨1977093, by rfl⟩ : syracuseStep 5272249 = 3954187) B3954187
theorem B7029665 : Blo 2081435 7029665 := bstep (se 2 (by rfl) ⟨2636124, by rfl⟩ : syracuseStep 7029665 = 5272249) B5272249
theorem B4686443 : Blo 2081435 4686443 := bstep (se 1 (by rfl) ⟨3514832, by rfl⟩ : syracuseStep 4686443 = 7029665) B7029665
theorem B3124295 : Blo 2081435 3124295 := bstep (se 1 (by rfl) ⟨2343221, by rfl⟩ : syracuseStep 3124295 = 4686443) B4686443
theorem B2082863 : Blo 2081435 2082863 := bstep (se 1 (by rfl) ⟨1562147, by rfl⟩ : syracuseStep 2082863 = 3124295) B3124295
theorem B3124301 : Blo 2081435 3124301 := bbase (se 3 (by rfl) ⟨585806, by rfl⟩ : syracuseStep 3124301 = 1171613) (by norm_num)
theorem B2082867 : Blo 2081435 2082867 := bstep (se 1 (by rfl) ⟨1562150, by rfl⟩ : syracuseStep 2082867 = 3124301) B3124301
theorem B4686461 : Blo 2081435 4686461 := bbase (se 3 (by rfl) ⟨878711, by rfl⟩ : syracuseStep 4686461 = 1757423) (by norm_num)
theorem B3124307 : Blo 2081435 3124307 := bstep (se 1 (by rfl) ⟨2343230, by rfl⟩ : syracuseStep 3124307 = 4686461) B4686461
theorem B2082871 : Blo 2081435 2082871 := bstep (se 1 (by rfl) ⟨1562153, by rfl⟩ : syracuseStep 2082871 = 3124307) B3124307
theorem B3514853 : Blo 2081435 3514853 := bbase (se 4 (by rfl) ⟨329517, by rfl⟩ : syracuseStep 3514853 = 659035) (by norm_num)
theorem B2343235 : Blo 2081435 2343235 := bstep (se 1 (by rfl) ⟨1757426, by rfl⟩ : syracuseStep 2343235 = 3514853) B3514853
theorem B3124313 : Blo 2081435 3124313 := bstep (se 2 (by rfl) ⟨1171617, by rfl⟩ : syracuseStep 3124313 = 2343235) B2343235
theorem B2082875 : Blo 2081435 2082875 := bstep (se 1 (by rfl) ⟨1562156, by rfl⟩ : syracuseStep 2082875 = 3124313) B3124313
theorem B2708569 : Blo 2081435 2708569 := bbase (se 2 (by rfl) ⟨1015713, by rfl⟩ : syracuseStep 2708569 = 2031427) (by norm_num)
theorem B14445701 : Blo 2081435 14445701 := bstep (se 4 (by rfl) ⟨1354284, by rfl⟩ : syracuseStep 14445701 = 2708569) B2708569
theorem B9630467 : Blo 2081435 9630467 := bstep (se 1 (by rfl) ⟨7222850, by rfl⟩ : syracuseStep 9630467 = 14445701) B14445701
theorem B6420311 : Blo 2081435 6420311 := bstep (se 1 (by rfl) ⟨4815233, by rfl⟩ : syracuseStep 6420311 = 9630467) B9630467
theorem B4280207 : Blo 2081435 4280207 := bstep (se 1 (by rfl) ⟨3210155, by rfl⟩ : syracuseStep 4280207 = 6420311) B6420311
theorem B11413885 : Blo 2081435 11413885 := bstep (se 3 (by rfl) ⟨2140103, by rfl⟩ : syracuseStep 11413885 = 4280207) B4280207
theorem B15218513 : Blo 2081435 15218513 := bstep (se 2 (by rfl) ⟨5706942, by rfl⟩ : syracuseStep 15218513 = 11413885) B11413885
theorem B10145675 : Blo 2081435 10145675 := bstep (se 1 (by rfl) ⟨7609256, by rfl⟩ : syracuseStep 10145675 = 15218513) B15218513
theorem B27055133 : Blo 2081435 27055133 := bstep (se 3 (by rfl) ⟨5072837, by rfl⟩ : syracuseStep 27055133 = 10145675) B10145675
theorem B18036755 : Blo 2081435 18036755 := bstep (se 1 (by rfl) ⟨13527566, by rfl⟩ : syracuseStep 18036755 = 27055133) B27055133
theorem B12024503 : Blo 2081435 12024503 := bstep (se 1 (by rfl) ⟨9018377, by rfl⟩ : syracuseStep 12024503 = 18036755) B18036755
theorem B8016335 : Blo 2081435 8016335 := bstep (se 1 (by rfl) ⟨6012251, by rfl⟩ : syracuseStep 8016335 = 12024503) B12024503
theorem B5344223 : Blo 2081435 5344223 := bstep (se 1 (by rfl) ⟨4008167, by rfl⟩ : syracuseStep 5344223 = 8016335) B8016335
theorem B57005045 : Blo 2081435 57005045 := bstep (se 5 (by rfl) ⟨2672111, by rfl⟩ : syracuseStep 57005045 = 5344223) B5344223
theorem B38003363 : Blo 2081435 38003363 := bstep (se 1 (by rfl) ⟨28502522, by rfl⟩ : syracuseStep 38003363 = 57005045) B57005045
theorem B25335575 : Blo 2081435 25335575 := bstep (se 1 (by rfl) ⟨19001681, by rfl⟩ : syracuseStep 25335575 = 38003363) B38003363
theorem B16890383 : Blo 2081435 16890383 := bstep (se 1 (by rfl) ⟨12667787, by rfl⟩ : syracuseStep 16890383 = 25335575) B25335575
theorem B11260255 : Blo 2081435 11260255 := bstep (se 1 (by rfl) ⟨8445191, by rfl⟩ : syracuseStep 11260255 = 16890383) B16890383
theorem B15013673 : Blo 2081435 15013673 := bstep (se 2 (by rfl) ⟨5630127, by rfl⟩ : syracuseStep 15013673 = 11260255) B11260255
theorem B10009115 : Blo 2081435 10009115 := bstep (se 1 (by rfl) ⟨7506836, by rfl⟩ : syracuseStep 10009115 = 15013673) B15013673
theorem B6672743 : Blo 2081435 6672743 := bstep (se 1 (by rfl) ⟨5004557, by rfl⟩ : syracuseStep 6672743 = 10009115) B10009115
theorem B4448495 : Blo 2081435 4448495 := bstep (se 1 (by rfl) ⟨3336371, by rfl⟩ : syracuseStep 4448495 = 6672743) B6672743
theorem B2965663 : Blo 2081435 2965663 := bstep (se 1 (by rfl) ⟨2224247, by rfl⟩ : syracuseStep 2965663 = 4448495) B4448495
theorem B15816869 : Blo 2081435 15816869 := bstep (se 4 (by rfl) ⟨1482831, by rfl⟩ : syracuseStep 15816869 = 2965663) B2965663
theorem B10544579 : Blo 2081435 10544579 := bstep (se 1 (by rfl) ⟨7908434, by rfl⟩ : syracuseStep 10544579 = 15816869) B15816869
theorem B7029719 : Blo 2081435 7029719 := bstep (se 1 (by rfl) ⟨5272289, by rfl⟩ : syracuseStep 7029719 = 10544579) B10544579
theorem B4686479 : Blo 2081435 4686479 := bstep (se 1 (by rfl) ⟨3514859, by rfl⟩ : syracuseStep 4686479 = 7029719) B7029719
theorem B3124319 : Blo 2081435 3124319 := bstep (se 1 (by rfl) ⟨2343239, by rfl⟩ : syracuseStep 3124319 = 4686479) B4686479
theorem B2082879 : Blo 2081435 2082879 := bstep (se 1 (by rfl) ⟨1562159, by rfl⟩ : syracuseStep 2082879 = 3124319) B3124319
theorem B3124325 : Blo 2081435 3124325 := bbase (se 4 (by rfl) ⟨292905, by rfl⟩ : syracuseStep 3124325 = 585811) (by norm_num)
theorem B2082883 : Blo 2081435 2082883 := bstep (se 1 (by rfl) ⟨1562162, by rfl⟩ : syracuseStep 2082883 = 3124325) B3124325
theorem B2502289 : Blo 2081435 2502289 := bbase (se 2 (by rfl) ⟨938358, by rfl⟩ : syracuseStep 2502289 = 1876717) (by norm_num)
theorem B3336385 : Blo 2081435 3336385 := bstep (se 2 (by rfl) ⟨1251144, by rfl⟩ : syracuseStep 3336385 = 2502289) B2502289
theorem B4448513 : Blo 2081435 4448513 := bstep (se 2 (by rfl) ⟨1668192, by rfl⟩ : syracuseStep 4448513 = 3336385) B3336385
theorem B2965675 : Blo 2081435 2965675 := bstep (se 1 (by rfl) ⟨2224256, by rfl⟩ : syracuseStep 2965675 = 4448513) B4448513
theorem B3954233 : Blo 2081435 3954233 := bstep (se 2 (by rfl) ⟨1482837, by rfl⟩ : syracuseStep 3954233 = 2965675) B2965675
theorem B2636155 : Blo 2081435 2636155 := bstep (se 1 (by rfl) ⟨1977116, by rfl⟩ : syracuseStep 2636155 = 3954233) B3954233
theorem B3514873 : Blo 2081435 3514873 := bstep (se 2 (by rfl) ⟨1318077, by rfl⟩ : syracuseStep 3514873 = 2636155) B2636155
theorem B4686497 : Blo 2081435 4686497 := bstep (se 2 (by rfl) ⟨1757436, by rfl⟩ : syracuseStep 4686497 = 3514873) B3514873
theorem B3124331 : Blo 2081435 3124331 := bstep (se 1 (by rfl) ⟨2343248, by rfl⟩ : syracuseStep 3124331 = 4686497) B4686497
theorem B2082887 : Blo 2081435 2082887 := bstep (se 1 (by rfl) ⟨1562165, by rfl⟩ : syracuseStep 2082887 = 3124331) B3124331
theorem B2343253 : Blo 2081435 2343253 := bbase (se 10 (by rfl) ⟨3432, by rfl⟩ : syracuseStep 2343253 = 6865) (by norm_num)
theorem B3124337 : Blo 2081435 3124337 := bstep (se 2 (by rfl) ⟨1171626, by rfl⟩ : syracuseStep 3124337 = 2343253) B2343253
theorem B2082891 : Blo 2081435 2082891 := bstep (se 1 (by rfl) ⟨1562168, by rfl⟩ : syracuseStep 2082891 = 3124337) B3124337
theorem B2636165 : Blo 2081435 2636165 := bbase (se 4 (by rfl) ⟨247140, by rfl⟩ : syracuseStep 2636165 = 494281) (by norm_num)
theorem B7029773 : Blo 2081435 7029773 := bstep (se 3 (by rfl) ⟨1318082, by rfl⟩ : syracuseStep 7029773 = 2636165) B2636165
theorem B4686515 : Blo 2081435 4686515 := bstep (se 1 (by rfl) ⟨3514886, by rfl⟩ : syracuseStep 4686515 = 7029773) B7029773
theorem B3124343 : Blo 2081435 3124343 := bstep (se 1 (by rfl) ⟨2343257, by rfl⟩ : syracuseStep 3124343 = 4686515) B4686515
theorem B2082895 : Blo 2081435 2082895 := bstep (se 1 (by rfl) ⟨1562171, by rfl⟩ : syracuseStep 2082895 = 3124343) B3124343
theorem B3124349 : Blo 2081435 3124349 := bbase (se 3 (by rfl) ⟨585815, by rfl⟩ : syracuseStep 3124349 = 1171631) (by norm_num)
theorem B2082899 : Blo 2081435 2082899 := bstep (se 1 (by rfl) ⟨1562174, by rfl⟩ : syracuseStep 2082899 = 3124349) B3124349
theorem B4686533 : Blo 2081435 4686533 := bbase (se 4 (by rfl) ⟨439362, by rfl⟩ : syracuseStep 4686533 = 878725) (by norm_num)
theorem B3124355 : Blo 2081435 3124355 := bstep (se 1 (by rfl) ⟨2343266, by rfl⟩ : syracuseStep 3124355 = 4686533) B4686533
theorem B2082903 : Blo 2081435 2082903 := bstep (se 1 (by rfl) ⟨1562177, by rfl⟩ : syracuseStep 2082903 = 3124355) B3124355
theorem B3753469 : Blo 2081435 3753469 := bbase (se 3 (by rfl) ⟨703775, by rfl⟩ : syracuseStep 3753469 = 1407551) (by norm_num)
theorem B20018501 : Blo 2081435 20018501 := bstep (se 4 (by rfl) ⟨1876734, by rfl⟩ : syracuseStep 20018501 = 3753469) B3753469
theorem B13345667 : Blo 2081435 13345667 := bstep (se 1 (by rfl) ⟨10009250, by rfl⟩ : syracuseStep 13345667 = 20018501) B20018501
theorem B8897111 : Blo 2081435 8897111 := bstep (se 1 (by rfl) ⟨6672833, by rfl⟩ : syracuseStep 8897111 = 13345667) B13345667
theorem B5931407 : Blo 2081435 5931407 := bstep (se 1 (by rfl) ⟨4448555, by rfl⟩ : syracuseStep 5931407 = 8897111) B8897111
theorem B3954271 : Blo 2081435 3954271 := bstep (se 1 (by rfl) ⟨2965703, by rfl⟩ : syracuseStep 3954271 = 5931407) B5931407
theorem B5272361 : Blo 2081435 5272361 := bstep (se 2 (by rfl) ⟨1977135, by rfl⟩ : syracuseStep 5272361 = 3954271) B3954271
theorem B3514907 : Blo 2081435 3514907 := bstep (se 1 (by rfl) ⟨2636180, by rfl⟩ : syracuseStep 3514907 = 5272361) B5272361
theorem B2343271 : Blo 2081435 2343271 := bstep (se 1 (by rfl) ⟨1757453, by rfl⟩ : syracuseStep 2343271 = 3514907) B3514907
theorem B3124361 : Blo 2081435 3124361 := bstep (se 2 (by rfl) ⟨1171635, by rfl⟩ : syracuseStep 3124361 = 2343271) B2343271
theorem B2082907 : Blo 2081435 2082907 := bstep (se 1 (by rfl) ⟨1562180, by rfl⟩ : syracuseStep 2082907 = 3124361) B3124361
theorem B10544741 : Blo 2081435 10544741 := bbase (se 4 (by rfl) ⟨988569, by rfl⟩ : syracuseStep 10544741 = 1977139) (by norm_num)
theorem B7029827 : Blo 2081435 7029827 := bstep (se 1 (by rfl) ⟨5272370, by rfl⟩ : syracuseStep 7029827 = 10544741) B10544741
theorem B4686551 : Blo 2081435 4686551 := bstep (se 1 (by rfl) ⟨3514913, by rfl⟩ : syracuseStep 4686551 = 7029827) B7029827
theorem B3124367 : Blo 2081435 3124367 := bstep (se 1 (by rfl) ⟨2343275, by rfl⟩ : syracuseStep 3124367 = 4686551) B4686551
theorem B2082911 : Blo 2081435 2082911 := bstep (se 1 (by rfl) ⟨1562183, by rfl⟩ : syracuseStep 2082911 = 3124367) B3124367
theorem B3124373 : Blo 2081435 3124373 := bbase (se 6 (by rfl) ⟨73227, by rfl⟩ : syracuseStep 3124373 = 146455) (by norm_num)
theorem B2082915 : Blo 2081435 2082915 := bstep (se 1 (by rfl) ⟨1562186, by rfl⟩ : syracuseStep 2082915 = 3124373) B3124373
theorem B2440513 : Blo 2081435 2440513 := bbase (se 2 (by rfl) ⟨915192, by rfl⟩ : syracuseStep 2440513 = 1830385) (by norm_num)
theorem B3254017 : Blo 2081435 3254017 := bstep (se 2 (by rfl) ⟨1220256, by rfl⟩ : syracuseStep 3254017 = 2440513) B2440513
theorem B4338689 : Blo 2081435 4338689 := bstep (se 2 (by rfl) ⟨1627008, by rfl⟩ : syracuseStep 4338689 = 3254017) B3254017
theorem B46279349 : Blo 2081435 46279349 := bstep (se 5 (by rfl) ⟨2169344, by rfl⟩ : syracuseStep 46279349 = 4338689) B4338689
theorem B30852899 : Blo 2081435 30852899 := bstep (se 1 (by rfl) ⟨23139674, by rfl⟩ : syracuseStep 30852899 = 46279349) B46279349
theorem B20568599 : Blo 2081435 20568599 := bstep (se 1 (by rfl) ⟨15426449, by rfl⟩ : syracuseStep 20568599 = 30852899) B30852899
theorem B13712399 : Blo 2081435 13712399 := bstep (se 1 (by rfl) ⟨10284299, by rfl⟩ : syracuseStep 13712399 = 20568599) B20568599
theorem B9141599 : Blo 2081435 9141599 := bstep (se 1 (by rfl) ⟨6856199, by rfl⟩ : syracuseStep 9141599 = 13712399) B13712399
theorem B6094399 : Blo 2081435 6094399 := bstep (se 1 (by rfl) ⟨4570799, by rfl⟩ : syracuseStep 6094399 = 9141599) B9141599
theorem B8125865 : Blo 2081435 8125865 := bstep (se 2 (by rfl) ⟨3047199, by rfl⟩ : syracuseStep 8125865 = 6094399) B6094399
theorem B5417243 : Blo 2081435 5417243 := bstep (se 1 (by rfl) ⟨4062932, by rfl⟩ : syracuseStep 5417243 = 8125865) B8125865
theorem B3611495 : Blo 2081435 3611495 := bstep (se 1 (by rfl) ⟨2708621, by rfl⟩ : syracuseStep 3611495 = 5417243) B5417243
theorem B2407663 : Blo 2081435 2407663 := bstep (se 1 (by rfl) ⟨1805747, by rfl⟩ : syracuseStep 2407663 = 3611495) B3611495
theorem B12840869 : Blo 2081435 12840869 := bstep (se 4 (by rfl) ⟨1203831, by rfl⟩ : syracuseStep 12840869 = 2407663) B2407663
theorem B8560579 : Blo 2081435 8560579 := bstep (se 1 (by rfl) ⟨6420434, by rfl⟩ : syracuseStep 8560579 = 12840869) B12840869
theorem B11414105 : Blo 2081435 11414105 := bstep (se 2 (by rfl) ⟨4280289, by rfl⟩ : syracuseStep 11414105 = 8560579) B8560579
theorem B7609403 : Blo 2081435 7609403 := bstep (se 1 (by rfl) ⟨5707052, by rfl⟩ : syracuseStep 7609403 = 11414105) B11414105
theorem B5072935 : Blo 2081435 5072935 := bstep (se 1 (by rfl) ⟨3804701, by rfl⟩ : syracuseStep 5072935 = 7609403) B7609403
theorem B6763913 : Blo 2081435 6763913 := bstep (se 2 (by rfl) ⟨2536467, by rfl⟩ : syracuseStep 6763913 = 5072935) B5072935
theorem B4509275 : Blo 2081435 4509275 := bstep (se 1 (by rfl) ⟨3381956, by rfl⟩ : syracuseStep 4509275 = 6763913) B6763913
theorem B48098933 : Blo 2081435 48098933 := bstep (se 5 (by rfl) ⟨2254637, by rfl⟩ : syracuseStep 48098933 = 4509275) B4509275
theorem B32065955 : Blo 2081435 32065955 := bstep (se 1 (by rfl) ⟨24049466, by rfl⟩ : syracuseStep 32065955 = 48098933) B48098933
theorem B21377303 : Blo 2081435 21377303 := bstep (se 1 (by rfl) ⟨16032977, by rfl⟩ : syracuseStep 21377303 = 32065955) B32065955
theorem B14251535 : Blo 2081435 14251535 := bstep (se 1 (by rfl) ⟨10688651, by rfl⟩ : syracuseStep 14251535 = 21377303) B21377303
theorem B9501023 : Blo 2081435 9501023 := bstep (se 1 (by rfl) ⟨7125767, by rfl⟩ : syracuseStep 9501023 = 14251535) B14251535
theorem B25336061 : Blo 2081435 25336061 := bstep (se 3 (by rfl) ⟨4750511, by rfl⟩ : syracuseStep 25336061 = 9501023) B9501023
theorem B16890707 : Blo 2081435 16890707 := bstep (se 1 (by rfl) ⟨12668030, by rfl⟩ : syracuseStep 16890707 = 25336061) B25336061
theorem B11260471 : Blo 2081435 11260471 := bstep (se 1 (by rfl) ⟨8445353, by rfl⟩ : syracuseStep 11260471 = 16890707) B16890707
theorem B15013961 : Blo 2081435 15013961 := bstep (se 2 (by rfl) ⟨5630235, by rfl⟩ : syracuseStep 15013961 = 11260471) B11260471
theorem B10009307 : Blo 2081435 10009307 := bstep (se 1 (by rfl) ⟨7506980, by rfl⟩ : syracuseStep 10009307 = 15013961) B15013961
theorem B6672871 : Blo 2081435 6672871 := bstep (se 1 (by rfl) ⟨5004653, by rfl⟩ : syracuseStep 6672871 = 10009307) B10009307
theorem B8897161 : Blo 2081435 8897161 := bstep (se 2 (by rfl) ⟨3336435, by rfl⟩ : syracuseStep 8897161 = 6672871) B6672871
theorem B11862881 : Blo 2081435 11862881 := bstep (se 2 (by rfl) ⟨4448580, by rfl⟩ : syracuseStep 11862881 = 8897161) B8897161
theorem B7908587 : Blo 2081435 7908587 := bstep (se 1 (by rfl) ⟨5931440, by rfl⟩ : syracuseStep 7908587 = 11862881) B11862881
theorem B5272391 : Blo 2081435 5272391 := bstep (se 1 (by rfl) ⟨3954293, by rfl⟩ : syracuseStep 5272391 = 7908587) B7908587
theorem B3514927 : Blo 2081435 3514927 := bstep (se 1 (by rfl) ⟨2636195, by rfl⟩ : syracuseStep 3514927 = 5272391) B5272391
theorem B4686569 : Blo 2081435 4686569 := bstep (se 2 (by rfl) ⟨1757463, by rfl⟩ : syracuseStep 4686569 = 3514927) B3514927
theorem B3124379 : Blo 2081435 3124379 := bstep (se 1 (by rfl) ⟨2343284, by rfl⟩ : syracuseStep 3124379 = 4686569) B4686569
theorem B2082919 : Blo 2081435 2082919 := bstep (se 1 (by rfl) ⟨1562189, by rfl⟩ : syracuseStep 2082919 = 3124379) B3124379
theorem B2343289 : Blo 2081435 2343289 := bbase (se 2 (by rfl) ⟨878733, by rfl⟩ : syracuseStep 2343289 = 1757467) (by norm_num)
theorem B3124385 : Blo 2081435 3124385 := bstep (se 2 (by rfl) ⟨1171644, by rfl⟩ : syracuseStep 3124385 = 2343289) B2343289
theorem B2082923 : Blo 2081435 2082923 := bstep (se 1 (by rfl) ⟨1562192, by rfl⟩ : syracuseStep 2082923 = 3124385) B3124385
theorem B4222693 : Blo 2081435 4222693 := bbase (se 4 (by rfl) ⟨395877, by rfl⟩ : syracuseStep 4222693 = 791755) (by norm_num)
theorem B5630257 : Blo 2081435 5630257 := bstep (se 2 (by rfl) ⟨2111346, by rfl⟩ : syracuseStep 5630257 = 4222693) B4222693
theorem B7507009 : Blo 2081435 7507009 := bstep (se 2 (by rfl) ⟨2815128, by rfl⟩ : syracuseStep 7507009 = 5630257) B5630257
theorem B10009345 : Blo 2081435 10009345 := bstep (se 2 (by rfl) ⟨3753504, by rfl⟩ : syracuseStep 10009345 = 7507009) B7507009
theorem B13345793 : Blo 2081435 13345793 := bstep (se 2 (by rfl) ⟨5004672, by rfl⟩ : syracuseStep 13345793 = 10009345) B10009345
theorem B8897195 : Blo 2081435 8897195 := bstep (se 1 (by rfl) ⟨6672896, by rfl⟩ : syracuseStep 8897195 = 13345793) B13345793
theorem B5931463 : Blo 2081435 5931463 := bstep (se 1 (by rfl) ⟨4448597, by rfl⟩ : syracuseStep 5931463 = 8897195) B8897195
theorem B7908617 : Blo 2081435 7908617 := bstep (se 2 (by rfl) ⟨2965731, by rfl⟩ : syracuseStep 7908617 = 5931463) B5931463
theorem B5272411 : Blo 2081435 5272411 := bstep (se 1 (by rfl) ⟨3954308, by rfl⟩ : syracuseStep 5272411 = 7908617) B7908617
theorem B7029881 : Blo 2081435 7029881 := bstep (se 2 (by rfl) ⟨2636205, by rfl⟩ : syracuseStep 7029881 = 5272411) B5272411
theorem B4686587 : Blo 2081435 4686587 := bstep (se 1 (by rfl) ⟨3514940, by rfl⟩ : syracuseStep 4686587 = 7029881) B7029881
theorem B3124391 : Blo 2081435 3124391 := bstep (se 1 (by rfl) ⟨2343293, by rfl⟩ : syracuseStep 3124391 = 4686587) B4686587
theorem B2082927 : Blo 2081435 2082927 := bstep (se 1 (by rfl) ⟨1562195, by rfl⟩ : syracuseStep 2082927 = 3124391) B3124391
theorem B3124397 : Blo 2081435 3124397 := bbase (se 3 (by rfl) ⟨585824, by rfl⟩ : syracuseStep 3124397 = 1171649) (by norm_num)
theorem B2082931 : Blo 2081435 2082931 := bstep (se 1 (by rfl) ⟨1562198, by rfl⟩ : syracuseStep 2082931 = 3124397) B3124397
theorem B4686605 : Blo 2081435 4686605 := bbase (se 3 (by rfl) ⟨878738, by rfl⟩ : syracuseStep 4686605 = 1757477) (by norm_num)
theorem B3124403 : Blo 2081435 3124403 := bstep (se 1 (by rfl) ⟨2343302, by rfl⟩ : syracuseStep 3124403 = 4686605) B4686605
theorem B2082935 : Blo 2081435 2082935 := bstep (se 1 (by rfl) ⟨1562201, by rfl⟩ : syracuseStep 2082935 = 3124403) B3124403
theorem B2636221 : Blo 2081435 2636221 := bbase (se 3 (by rfl) ⟨494291, by rfl⟩ : syracuseStep 2636221 = 988583) (by norm_num)
theorem B3514961 : Blo 2081435 3514961 := bstep (se 2 (by rfl) ⟨1318110, by rfl⟩ : syracuseStep 3514961 = 2636221) B2636221
theorem B2343307 : Blo 2081435 2343307 := bstep (se 1 (by rfl) ⟨1757480, by rfl⟩ : syracuseStep 2343307 = 3514961) B3514961
theorem B3124409 : Blo 2081435 3124409 := bstep (se 2 (by rfl) ⟨1171653, by rfl⟩ : syracuseStep 3124409 = 2343307) B2343307
theorem B2082939 : Blo 2081435 2082939 := bstep (se 1 (by rfl) ⟨1562204, by rfl⟩ : syracuseStep 2082939 = 3124409) B3124409
theorem B3753533 : Blo 2081435 3753533 := bbase (se 3 (by rfl) ⟨703787, by rfl⟩ : syracuseStep 3753533 = 1407575) (by norm_num)
theorem B10009421 : Blo 2081435 10009421 := bstep (se 3 (by rfl) ⟨1876766, by rfl⟩ : syracuseStep 10009421 = 3753533) B3753533
theorem B6672947 : Blo 2081435 6672947 := bstep (se 1 (by rfl) ⟨5004710, by rfl⟩ : syracuseStep 6672947 = 10009421) B10009421
theorem B17794525 : Blo 2081435 17794525 := bstep (se 3 (by rfl) ⟨3336473, by rfl⟩ : syracuseStep 17794525 = 6672947) B6672947
theorem B23726033 : Blo 2081435 23726033 := bstep (se 2 (by rfl) ⟨8897262, by rfl⟩ : syracuseStep 23726033 = 17794525) B17794525
theorem B15817355 : Blo 2081435 15817355 := bstep (se 1 (by rfl) ⟨11863016, by rfl⟩ : syracuseStep 15817355 = 23726033) B23726033
theorem B10544903 : Blo 2081435 10544903 := bstep (se 1 (by rfl) ⟨7908677, by rfl⟩ : syracuseStep 10544903 = 15817355) B15817355
theorem B7029935 : Blo 2081435 7029935 := bstep (se 1 (by rfl) ⟨5272451, by rfl⟩ : syracuseStep 7029935 = 10544903) B10544903
theorem B4686623 : Blo 2081435 4686623 := bstep (se 1 (by rfl) ⟨3514967, by rfl⟩ : syracuseStep 4686623 = 7029935) B7029935
theorem B3124415 : Blo 2081435 3124415 := bstep (se 1 (by rfl) ⟨2343311, by rfl⟩ : syracuseStep 3124415 = 4686623) B4686623
theorem B2082943 : Blo 2081435 2082943 := bstep (se 1 (by rfl) ⟨1562207, by rfl⟩ : syracuseStep 2082943 = 3124415) B3124415
theorem B3124421 : Blo 2081435 3124421 := bbase (se 4 (by rfl) ⟨292914, by rfl⟩ : syracuseStep 3124421 = 585829) (by norm_num)
theorem B2082947 : Blo 2081435 2082947 := bstep (se 1 (by rfl) ⟨1562210, by rfl⟩ : syracuseStep 2082947 = 3124421) B3124421
theorem B3514981 : Blo 2081435 3514981 := bbase (se 4 (by rfl) ⟨329529, by rfl⟩ : syracuseStep 3514981 = 659059) (by norm_num)
theorem B4686641 : Blo 2081435 4686641 := bstep (se 2 (by rfl) ⟨1757490, by rfl⟩ : syracuseStep 4686641 = 3514981) B3514981
theorem B3124427 : Blo 2081435 3124427 := bstep (se 1 (by rfl) ⟨2343320, by rfl⟩ : syracuseStep 3124427 = 4686641) B4686641
theorem B2082951 : Blo 2081435 2082951 := bstep (se 1 (by rfl) ⟨1562213, by rfl⟩ : syracuseStep 2082951 = 3124427) B3124427
theorem B2343325 : Blo 2081435 2343325 := bbase (se 3 (by rfl) ⟨439373, by rfl⟩ : syracuseStep 2343325 = 878747) (by norm_num)
theorem B3124433 : Blo 2081435 3124433 := bstep (se 2 (by rfl) ⟨1171662, by rfl⟩ : syracuseStep 3124433 = 2343325) B2343325
theorem B2082955 : Blo 2081435 2082955 := bstep (se 1 (by rfl) ⟨1562216, by rfl⟩ : syracuseStep 2082955 = 3124433) B3124433
theorem B7029989 : Blo 2081435 7029989 := bbase (se 4 (by rfl) ⟨659061, by rfl⟩ : syracuseStep 7029989 = 1318123) (by norm_num)
theorem B4686659 : Blo 2081435 4686659 := bstep (se 1 (by rfl) ⟨3514994, by rfl⟩ : syracuseStep 4686659 = 7029989) B7029989
theorem B3124439 : Blo 2081435 3124439 := bstep (se 1 (by rfl) ⟨2343329, by rfl⟩ : syracuseStep 3124439 = 4686659) B4686659
theorem B2082959 : Blo 2081435 2082959 := bstep (se 1 (by rfl) ⟨1562219, by rfl⟩ : syracuseStep 2082959 = 3124439) B3124439
theorem B3124445 : Blo 2081435 3124445 := bbase (se 3 (by rfl) ⟨585833, by rfl⟩ : syracuseStep 3124445 = 1171667) (by norm_num)
theorem B2082963 : Blo 2081435 2082963 := bstep (se 1 (by rfl) ⟨1562222, by rfl⟩ : syracuseStep 2082963 = 3124445) B3124445
theorem B4686677 : Blo 2081435 4686677 := bbase (se 9 (by rfl) ⟨13730, by rfl⟩ : syracuseStep 4686677 = 27461) (by norm_num)
theorem B3124451 : Blo 2081435 3124451 := bstep (se 1 (by rfl) ⟨2343338, by rfl⟩ : syracuseStep 3124451 = 4686677) B4686677
theorem B2082967 : Blo 2081435 2082967 := bstep (se 1 (by rfl) ⟨1562225, by rfl⟩ : syracuseStep 2082967 = 3124451) B3124451
theorem B5931589 : Blo 2081435 5931589 := bbase (se 4 (by rfl) ⟨556086, by rfl⟩ : syracuseStep 5931589 = 1112173) (by norm_num)
theorem B7908785 : Blo 2081435 7908785 := bstep (se 2 (by rfl) ⟨2965794, by rfl⟩ : syracuseStep 7908785 = 5931589) B5931589
theorem B5272523 : Blo 2081435 5272523 := bstep (se 1 (by rfl) ⟨3954392, by rfl⟩ : syracuseStep 5272523 = 7908785) B7908785
theorem B3515015 : Blo 2081435 3515015 := bstep (se 1 (by rfl) ⟨2636261, by rfl⟩ : syracuseStep 3515015 = 5272523) B5272523
theorem B2343343 : Blo 2081435 2343343 := bstep (se 1 (by rfl) ⟨1757507, by rfl⟩ : syracuseStep 2343343 = 3515015) B3515015
theorem B3124457 : Blo 2081435 3124457 := bstep (se 2 (by rfl) ⟨1171671, by rfl⟩ : syracuseStep 3124457 = 2343343) B2343343
theorem B2082971 : Blo 2081435 2082971 := bstep (se 1 (by rfl) ⟨1562228, by rfl⟩ : syracuseStep 2082971 = 3124457) B3124457
theorem B28503829 : Blo 2081435 28503829 := bbase (se 6 (by rfl) ⟨668058, by rfl⟩ : syracuseStep 28503829 = 1336117) (by norm_num)
theorem B152020421 : Blo 2081435 152020421 := bstep (se 4 (by rfl) ⟨14251914, by rfl⟩ : syracuseStep 152020421 = 28503829) B28503829
theorem B101346947 : Blo 2081435 101346947 := bstep (se 1 (by rfl) ⟨76010210, by rfl⟩ : syracuseStep 101346947 = 152020421) B152020421
theorem B67564631 : Blo 2081435 67564631 := bstep (se 1 (by rfl) ⟨50673473, by rfl⟩ : syracuseStep 67564631 = 101346947) B101346947
theorem B45043087 : Blo 2081435 45043087 := bstep (se 1 (by rfl) ⟨33782315, by rfl⟩ : syracuseStep 45043087 = 67564631) B67564631
theorem B60057449 : Blo 2081435 60057449 := bstep (se 2 (by rfl) ⟨22521543, by rfl⟩ : syracuseStep 60057449 = 45043087) B45043087
theorem B40038299 : Blo 2081435 40038299 := bstep (se 1 (by rfl) ⟨30028724, by rfl⟩ : syracuseStep 40038299 = 60057449) B60057449
theorem B26692199 : Blo 2081435 26692199 := bstep (se 1 (by rfl) ⟨20019149, by rfl⟩ : syracuseStep 26692199 = 40038299) B40038299
theorem B17794799 : Blo 2081435 17794799 := bstep (se 1 (by rfl) ⟨13346099, by rfl⟩ : syracuseStep 17794799 = 26692199) B26692199
theorem B11863199 : Blo 2081435 11863199 := bstep (se 1 (by rfl) ⟨8897399, by rfl⟩ : syracuseStep 11863199 = 17794799) B17794799
theorem B7908799 : Blo 2081435 7908799 := bstep (se 1 (by rfl) ⟨5931599, by rfl⟩ : syracuseStep 7908799 = 11863199) B11863199
theorem B10545065 : Blo 2081435 10545065 := bstep (se 2 (by rfl) ⟨3954399, by rfl⟩ : syracuseStep 10545065 = 7908799) B7908799
theorem B7030043 : Blo 2081435 7030043 := bstep (se 1 (by rfl) ⟨5272532, by rfl⟩ : syracuseStep 7030043 = 10545065) B10545065
theorem B4686695 : Blo 2081435 4686695 := bstep (se 1 (by rfl) ⟨3515021, by rfl⟩ : syracuseStep 4686695 = 7030043) B7030043
theorem B3124463 : Blo 2081435 3124463 := bstep (se 1 (by rfl) ⟨2343347, by rfl⟩ : syracuseStep 3124463 = 4686695) B4686695
theorem B2082975 : Blo 2081435 2082975 := bstep (se 1 (by rfl) ⟨1562231, by rfl⟩ : syracuseStep 2082975 = 3124463) B3124463
theorem B3124469 : Blo 2081435 3124469 := bbase (se 5 (by rfl) ⟨146459, by rfl⟩ : syracuseStep 3124469 = 292919) (by norm_num)
theorem B2082979 : Blo 2081435 2082979 := bstep (se 1 (by rfl) ⟨1562234, by rfl⟩ : syracuseStep 2082979 = 3124469) B3124469
theorem B2375329 : Blo 2081435 2375329 := bbase (se 2 (by rfl) ⟨890748, by rfl⟩ : syracuseStep 2375329 = 1781497) (by norm_num)
theorem B3167105 : Blo 2081435 3167105 := bstep (se 2 (by rfl) ⟨1187664, by rfl⟩ : syracuseStep 3167105 = 2375329) B2375329
theorem B33782453 : Blo 2081435 33782453 := bstep (se 5 (by rfl) ⟨1583552, by rfl⟩ : syracuseStep 33782453 = 3167105) B3167105
theorem B22521635 : Blo 2081435 22521635 := bstep (se 1 (by rfl) ⟨16891226, by rfl⟩ : syracuseStep 22521635 = 33782453) B33782453
theorem B15014423 : Blo 2081435 15014423 := bstep (se 1 (by rfl) ⟨11260817, by rfl⟩ : syracuseStep 15014423 = 22521635) B22521635
theorem B10009615 : Blo 2081435 10009615 := bstep (se 1 (by rfl) ⟨7507211, by rfl⟩ : syracuseStep 10009615 = 15014423) B15014423
theorem B13346153 : Blo 2081435 13346153 := bstep (se 2 (by rfl) ⟨5004807, by rfl⟩ : syracuseStep 13346153 = 10009615) B10009615
theorem B8897435 : Blo 2081435 8897435 := bstep (se 1 (by rfl) ⟨6673076, by rfl⟩ : syracuseStep 8897435 = 13346153) B13346153
theorem B5931623 : Blo 2081435 5931623 := bstep (se 1 (by rfl) ⟨4448717, by rfl⟩ : syracuseStep 5931623 = 8897435) B8897435
theorem B3954415 : Blo 2081435 3954415 := bstep (se 1 (by rfl) ⟨2965811, by rfl⟩ : syracuseStep 3954415 = 5931623) B5931623
theorem B5272553 : Blo 2081435 5272553 := bstep (se 2 (by rfl) ⟨1977207, by rfl⟩ : syracuseStep 5272553 = 3954415) B3954415
theorem B3515035 : Blo 2081435 3515035 := bstep (se 1 (by rfl) ⟨2636276, by rfl⟩ : syracuseStep 3515035 = 5272553) B5272553
theorem B4686713 : Blo 2081435 4686713 := bstep (se 2 (by rfl) ⟨1757517, by rfl⟩ : syracuseStep 4686713 = 3515035) B3515035
theorem B3124475 : Blo 2081435 3124475 := bstep (se 1 (by rfl) ⟨2343356, by rfl⟩ : syracuseStep 3124475 = 4686713) B4686713
theorem B2082983 : Blo 2081435 2082983 := bstep (se 1 (by rfl) ⟨1562237, by rfl⟩ : syracuseStep 2082983 = 3124475) B3124475
theorem B2343361 : Blo 2081435 2343361 := bbase (se 2 (by rfl) ⟨878760, by rfl⟩ : syracuseStep 2343361 = 1757521) (by norm_num)
theorem B3124481 : Blo 2081435 3124481 := bstep (se 2 (by rfl) ⟨1171680, by rfl⟩ : syracuseStep 3124481 = 2343361) B2343361
theorem B2082987 : Blo 2081435 2082987 := bstep (se 1 (by rfl) ⟨1562240, by rfl⟩ : syracuseStep 2082987 = 3124481) B3124481
theorem B5272573 : Blo 2081435 5272573 := bbase (se 3 (by rfl) ⟨988607, by rfl⟩ : syracuseStep 5272573 = 1977215) (by norm_num)
theorem B7030097 : Blo 2081435 7030097 := bstep (se 2 (by rfl) ⟨2636286, by rfl⟩ : syracuseStep 7030097 = 5272573) B5272573
theorem B4686731 : Blo 2081435 4686731 := bstep (se 1 (by rfl) ⟨3515048, by rfl⟩ : syracuseStep 4686731 = 7030097) B7030097
theorem B3124487 : Blo 2081435 3124487 := bstep (se 1 (by rfl) ⟨2343365, by rfl⟩ : syracuseStep 3124487 = 4686731) B4686731
theorem B2082991 : Blo 2081435 2082991 := bstep (se 1 (by rfl) ⟨1562243, by rfl⟩ : syracuseStep 2082991 = 3124487) B3124487
theorem B3124493 : Blo 2081435 3124493 := bbase (se 3 (by rfl) ⟨585842, by rfl⟩ : syracuseStep 3124493 = 1171685) (by norm_num)
theorem B2082995 : Blo 2081435 2082995 := bstep (se 1 (by rfl) ⟨1562246, by rfl⟩ : syracuseStep 2082995 = 3124493) B3124493
theorem B4686749 : Blo 2081435 4686749 := bbase (se 3 (by rfl) ⟨878765, by rfl⟩ : syracuseStep 4686749 = 1757531) (by norm_num)
theorem B3124499 : Blo 2081435 3124499 := bstep (se 1 (by rfl) ⟨2343374, by rfl⟩ : syracuseStep 3124499 = 4686749) B4686749
theorem B2082999 : Blo 2081435 2082999 := bstep (se 1 (by rfl) ⟨1562249, by rfl⟩ : syracuseStep 2082999 = 3124499) B3124499
theorem B3515069 : Blo 2081435 3515069 := bbase (se 3 (by rfl) ⟨659075, by rfl⟩ : syracuseStep 3515069 = 1318151) (by norm_num)
theorem B2343379 : Blo 2081435 2343379 := bstep (se 1 (by rfl) ⟨1757534, by rfl⟩ : syracuseStep 2343379 = 3515069) B3515069
theorem B3124505 : Blo 2081435 3124505 := bstep (se 2 (by rfl) ⟨1171689, by rfl⟩ : syracuseStep 3124505 = 2343379) B2343379
theorem B2083003 : Blo 2081435 2083003 := bstep (se 1 (by rfl) ⟨1562252, by rfl⟩ : syracuseStep 2083003 = 3124505) B3124505
theorem B11863381 : Blo 2081435 11863381 := bbase (se 12 (by rfl) ⟨4344, by rfl⟩ : syracuseStep 11863381 = 8689) (by norm_num)
theorem B15817841 : Blo 2081435 15817841 := bstep (se 2 (by rfl) ⟨5931690, by rfl⟩ : syracuseStep 15817841 = 11863381) B11863381
theorem B10545227 : Blo 2081435 10545227 := bstep (se 1 (by rfl) ⟨7908920, by rfl⟩ : syracuseStep 10545227 = 15817841) B15817841
theorem B7030151 : Blo 2081435 7030151 := bstep (se 1 (by rfl) ⟨5272613, by rfl⟩ : syracuseStep 7030151 = 10545227) B10545227
theorem B4686767 : Blo 2081435 4686767 := bstep (se 1 (by rfl) ⟨3515075, by rfl⟩ : syracuseStep 4686767 = 7030151) B7030151
theorem B3124511 : Blo 2081435 3124511 := bstep (se 1 (by rfl) ⟨2343383, by rfl⟩ : syracuseStep 3124511 = 4686767) B4686767
theorem B2083007 : Blo 2081435 2083007 := bstep (se 1 (by rfl) ⟨1562255, by rfl⟩ : syracuseStep 2083007 = 3124511) B3124511
theorem B3124517 : Blo 2081435 3124517 := bbase (se 4 (by rfl) ⟨292923, by rfl⟩ : syracuseStep 3124517 = 585847) (by norm_num)
theorem B2083011 : Blo 2081435 2083011 := bstep (se 1 (by rfl) ⟨1562258, by rfl⟩ : syracuseStep 2083011 = 3124517) B3124517
theorem B2636317 : Blo 2081435 2636317 := bbase (se 3 (by rfl) ⟨494309, by rfl⟩ : syracuseStep 2636317 = 988619) (by norm_num)
theorem B3515089 : Blo 2081435 3515089 := bstep (se 2 (by rfl) ⟨1318158, by rfl⟩ : syracuseStep 3515089 = 2636317) B2636317
theorem B4686785 : Blo 2081435 4686785 := bstep (se 2 (by rfl) ⟨1757544, by rfl⟩ : syracuseStep 4686785 = 3515089) B3515089
theorem B3124523 : Blo 2081435 3124523 := bstep (se 1 (by rfl) ⟨2343392, by rfl⟩ : syracuseStep 3124523 = 4686785) B4686785
theorem B2083015 : Blo 2081435 2083015 := bstep (se 1 (by rfl) ⟨1562261, by rfl⟩ : syracuseStep 2083015 = 3124523) B3124523
theorem B2343397 : Blo 2081435 2343397 := bbase (se 4 (by rfl) ⟨219693, by rfl⟩ : syracuseStep 2343397 = 439387) (by norm_num)
theorem B3124529 : Blo 2081435 3124529 := bstep (se 2 (by rfl) ⟨1171698, by rfl⟩ : syracuseStep 3124529 = 2343397) B2343397
theorem B2083019 : Blo 2081435 2083019 := bstep (se 1 (by rfl) ⟨1562264, by rfl⟩ : syracuseStep 2083019 = 3124529) B3124529
theorem B6673205 : Blo 2081435 6673205 := bbase (se 5 (by rfl) ⟨312806, by rfl⟩ : syracuseStep 6673205 = 625613) (by norm_num)
theorem B4448803 : Blo 2081435 4448803 := bstep (se 1 (by rfl) ⟨3336602, by rfl⟩ : syracuseStep 4448803 = 6673205) B6673205
theorem B5931737 : Blo 2081435 5931737 := bstep (se 2 (by rfl) ⟨2224401, by rfl⟩ : syracuseStep 5931737 = 4448803) B4448803
theorem B3954491 : Blo 2081435 3954491 := bstep (se 1 (by rfl) ⟨2965868, by rfl⟩ : syracuseStep 3954491 = 5931737) B5931737
theorem B2636327 : Blo 2081435 2636327 := bstep (se 1 (by rfl) ⟨1977245, by rfl⟩ : syracuseStep 2636327 = 3954491) B3954491
theorem B7030205 : Blo 2081435 7030205 := bstep (se 3 (by rfl) ⟨1318163, by rfl⟩ : syracuseStep 7030205 = 2636327) B2636327
theorem B4686803 : Blo 2081435 4686803 := bstep (se 1 (by rfl) ⟨3515102, by rfl⟩ : syracuseStep 4686803 = 7030205) B7030205
theorem B3124535 : Blo 2081435 3124535 := bstep (se 1 (by rfl) ⟨2343401, by rfl⟩ : syracuseStep 3124535 = 4686803) B4686803
theorem B2083023 : Blo 2081435 2083023 := bstep (se 1 (by rfl) ⟨1562267, by rfl⟩ : syracuseStep 2083023 = 3124535) B3124535
theorem B3124541 : Blo 2081435 3124541 := bbase (se 3 (by rfl) ⟨585851, by rfl⟩ : syracuseStep 3124541 = 1171703) (by norm_num)
theorem B2083027 : Blo 2081435 2083027 := bstep (se 1 (by rfl) ⟨1562270, by rfl⟩ : syracuseStep 2083027 = 3124541) B3124541
theorem B4686821 : Blo 2081435 4686821 := bbase (se 4 (by rfl) ⟨439389, by rfl⟩ : syracuseStep 4686821 = 878779) (by norm_num)
theorem B3124547 : Blo 2081435 3124547 := bstep (se 1 (by rfl) ⟨2343410, by rfl⟩ : syracuseStep 3124547 = 4686821) B4686821
theorem B2083031 : Blo 2081435 2083031 := bstep (se 1 (by rfl) ⟨1562273, by rfl⟩ : syracuseStep 2083031 = 3124547) B3124547
theorem B5272685 : Blo 2081435 5272685 := bbase (se 3 (by rfl) ⟨988628, by rfl⟩ : syracuseStep 5272685 = 1977257) (by norm_num)
theorem B3515123 : Blo 2081435 3515123 := bstep (se 1 (by rfl) ⟨2636342, by rfl⟩ : syracuseStep 3515123 = 5272685) B5272685
theorem B2343415 : Blo 2081435 2343415 := bstep (se 1 (by rfl) ⟨1757561, by rfl⟩ : syracuseStep 2343415 = 3515123) B3515123
theorem B3124553 : Blo 2081435 3124553 := bstep (se 2 (by rfl) ⟨1171707, by rfl⟩ : syracuseStep 3124553 = 2343415) B2343415
theorem B2083035 : Blo 2081435 2083035 := bstep (se 1 (by rfl) ⟨1562276, by rfl⟩ : syracuseStep 2083035 = 3124553) B3124553
theorem B4448837 : Blo 2081435 4448837 := bbase (se 4 (by rfl) ⟨417078, by rfl⟩ : syracuseStep 4448837 = 834157) (by norm_num)
theorem B2965891 : Blo 2081435 2965891 := bstep (se 1 (by rfl) ⟨2224418, by rfl⟩ : syracuseStep 2965891 = 4448837) B4448837
theorem B3954521 : Blo 2081435 3954521 := bstep (se 2 (by rfl) ⟨1482945, by rfl⟩ : syracuseStep 3954521 = 2965891) B2965891
theorem B10545389 : Blo 2081435 10545389 := bstep (se 3 (by rfl) ⟨1977260, by rfl⟩ : syracuseStep 10545389 = 3954521) B3954521
theorem B7030259 : Blo 2081435 7030259 := bstep (se 1 (by rfl) ⟨5272694, by rfl⟩ : syracuseStep 7030259 = 10545389) B10545389
theorem B4686839 : Blo 2081435 4686839 := bstep (se 1 (by rfl) ⟨3515129, by rfl⟩ : syracuseStep 4686839 = 7030259) B7030259
theorem B3124559 : Blo 2081435 3124559 := bstep (se 1 (by rfl) ⟨2343419, by rfl⟩ : syracuseStep 3124559 = 4686839) B4686839
theorem B2083039 : Blo 2081435 2083039 := bstep (se 1 (by rfl) ⟨1562279, by rfl⟩ : syracuseStep 2083039 = 3124559) B3124559
theorem B3124565 : Blo 2081435 3124565 := bbase (se 11 (by rfl) ⟨2288, by rfl⟩ : syracuseStep 3124565 = 4577) (by norm_num)
theorem B2083043 : Blo 2081435 2083043 := bstep (se 1 (by rfl) ⟨1562282, by rfl⟩ : syracuseStep 2083043 = 3124565) B3124565
theorem B2502481 : Blo 2081435 2502481 := bbase (se 2 (by rfl) ⟨938430, by rfl⟩ : syracuseStep 2502481 = 1876861) (by norm_num)
theorem B3336641 : Blo 2081435 3336641 := bstep (se 2 (by rfl) ⟨1251240, by rfl⟩ : syracuseStep 3336641 = 2502481) B2502481
theorem B2224427 : Blo 2081435 2224427 := bstep (se 1 (by rfl) ⟨1668320, by rfl⟩ : syracuseStep 2224427 = 3336641) B3336641
theorem B5931805 : Blo 2081435 5931805 := bstep (se 3 (by rfl) ⟨1112213, by rfl⟩ : syracuseStep 5931805 = 2224427) B2224427
theorem B7909073 : Blo 2081435 7909073 := bstep (se 2 (by rfl) ⟨2965902, by rfl⟩ : syracuseStep 7909073 = 5931805) B5931805
theorem B5272715 : Blo 2081435 5272715 := bstep (se 1 (by rfl) ⟨3954536, by rfl⟩ : syracuseStep 5272715 = 7909073) B7909073
theorem B3515143 : Blo 2081435 3515143 := bstep (se 1 (by rfl) ⟨2636357, by rfl⟩ : syracuseStep 3515143 = 5272715) B5272715
theorem B4686857 : Blo 2081435 4686857 := bstep (se 2 (by rfl) ⟨1757571, by rfl⟩ : syracuseStep 4686857 = 3515143) B3515143
theorem B3124571 : Blo 2081435 3124571 := bstep (se 1 (by rfl) ⟨2343428, by rfl⟩ : syracuseStep 3124571 = 4686857) B4686857
theorem B2083047 : Blo 2081435 2083047 := bstep (se 1 (by rfl) ⟨1562285, by rfl⟩ : syracuseStep 2083047 = 3124571) B3124571
theorem B2343433 : Blo 2081435 2343433 := bbase (se 2 (by rfl) ⟨878787, by rfl⟩ : syracuseStep 2343433 = 1757575) (by norm_num)
theorem B3124577 : Blo 2081435 3124577 := bstep (se 2 (by rfl) ⟨1171716, by rfl⟩ : syracuseStep 3124577 = 2343433) B2343433
theorem B2083051 : Blo 2081435 2083051 := bstep (se 1 (by rfl) ⟨1562288, by rfl⟩ : syracuseStep 2083051 = 3124577) B3124577
theorem B58576085 : Blo 2081435 58576085 := bbase (se 7 (by rfl) ⟨686438, by rfl⟩ : syracuseStep 58576085 = 1372877) (by norm_num)
theorem B39050723 : Blo 2081435 39050723 := bstep (se 1 (by rfl) ⟨29288042, by rfl⟩ : syracuseStep 39050723 = 58576085) B58576085
theorem B26033815 : Blo 2081435 26033815 := bstep (se 1 (by rfl) ⟨19525361, by rfl⟩ : syracuseStep 26033815 = 39050723) B39050723
theorem B34711753 : Blo 2081435 34711753 := bstep (se 2 (by rfl) ⟨13016907, by rfl⟩ : syracuseStep 34711753 = 26033815) B26033815
theorem B46282337 : Blo 2081435 46282337 := bstep (se 2 (by rfl) ⟨17355876, by rfl⟩ : syracuseStep 46282337 = 34711753) B34711753
theorem B30854891 : Blo 2081435 30854891 := bstep (se 1 (by rfl) ⟨23141168, by rfl⟩ : syracuseStep 30854891 = 46282337) B46282337
theorem B82279709 : Blo 2081435 82279709 := bstep (se 3 (by rfl) ⟨15427445, by rfl⟩ : syracuseStep 82279709 = 30854891) B30854891
theorem B54853139 : Blo 2081435 54853139 := bstep (se 1 (by rfl) ⟨41139854, by rfl⟩ : syracuseStep 54853139 = 82279709) B82279709
theorem B36568759 : Blo 2081435 36568759 := bstep (se 1 (by rfl) ⟨27426569, by rfl⟩ : syracuseStep 36568759 = 54853139) B54853139
theorem B48758345 : Blo 2081435 48758345 := bstep (se 2 (by rfl) ⟨18284379, by rfl⟩ : syracuseStep 48758345 = 36568759) B36568759
theorem B32505563 : Blo 2081435 32505563 := bstep (se 1 (by rfl) ⟨24379172, by rfl⟩ : syracuseStep 32505563 = 48758345) B48758345
theorem B21670375 : Blo 2081435 21670375 := bstep (se 1 (by rfl) ⟨16252781, by rfl⟩ : syracuseStep 21670375 = 32505563) B32505563
theorem B28893833 : Blo 2081435 28893833 := bstep (se 2 (by rfl) ⟨10835187, by rfl⟩ : syracuseStep 28893833 = 21670375) B21670375
theorem B19262555 : Blo 2081435 19262555 := bstep (se 1 (by rfl) ⟨14446916, by rfl⟩ : syracuseStep 19262555 = 28893833) B28893833
theorem B12841703 : Blo 2081435 12841703 := bstep (se 1 (by rfl) ⟨9631277, by rfl⟩ : syracuseStep 12841703 = 19262555) B19262555
theorem B8561135 : Blo 2081435 8561135 := bstep (se 1 (by rfl) ⟨6420851, by rfl⟩ : syracuseStep 8561135 = 12841703) B12841703
theorem B5707423 : Blo 2081435 5707423 := bstep (se 1 (by rfl) ⟨4280567, by rfl⟩ : syracuseStep 5707423 = 8561135) B8561135
theorem B7609897 : Blo 2081435 7609897 := bstep (se 2 (by rfl) ⟨2853711, by rfl⟩ : syracuseStep 7609897 = 5707423) B5707423
theorem B10146529 : Blo 2081435 10146529 := bstep (se 2 (by rfl) ⟨3804948, by rfl⟩ : syracuseStep 10146529 = 7609897) B7609897
theorem B54114821 : Blo 2081435 54114821 := bstep (se 4 (by rfl) ⟨5073264, by rfl⟩ : syracuseStep 54114821 = 10146529) B10146529
theorem B36076547 : Blo 2081435 36076547 := bstep (se 1 (by rfl) ⟨27057410, by rfl⟩ : syracuseStep 36076547 = 54114821) B54114821
theorem B96204125 : Blo 2081435 96204125 := bstep (se 3 (by rfl) ⟨18038273, by rfl⟩ : syracuseStep 96204125 = 36076547) B36076547
theorem B64136083 : Blo 2081435 64136083 := bstep (se 1 (by rfl) ⟨48102062, by rfl⟩ : syracuseStep 64136083 = 96204125) B96204125
theorem B85514777 : Blo 2081435 85514777 := bstep (se 2 (by rfl) ⟨32068041, by rfl⟩ : syracuseStep 85514777 = 64136083) B64136083
theorem B57009851 : Blo 2081435 57009851 := bstep (se 1 (by rfl) ⟨42757388, by rfl⟩ : syracuseStep 57009851 = 85514777) B85514777
theorem B38006567 : Blo 2081435 38006567 := bstep (se 1 (by rfl) ⟨28504925, by rfl⟩ : syracuseStep 38006567 = 57009851) B57009851
theorem B25337711 : Blo 2081435 25337711 := bstep (se 1 (by rfl) ⟨19003283, by rfl⟩ : syracuseStep 25337711 = 38006567) B38006567
theorem B67567229 : Blo 2081435 67567229 := bstep (se 3 (by rfl) ⟨12668855, by rfl⟩ : syracuseStep 67567229 = 25337711) B25337711
theorem B45044819 : Blo 2081435 45044819 := bstep (se 1 (by rfl) ⟨33783614, by rfl⟩ : syracuseStep 45044819 = 67567229) B67567229
theorem B30029879 : Blo 2081435 30029879 := bstep (se 1 (by rfl) ⟨22522409, by rfl⟩ : syracuseStep 30029879 = 45044819) B45044819
theorem B20019919 : Blo 2081435 20019919 := bstep (se 1 (by rfl) ⟨15014939, by rfl⟩ : syracuseStep 20019919 = 30029879) B30029879
theorem B26693225 : Blo 2081435 26693225 := bstep (se 2 (by rfl) ⟨10009959, by rfl⟩ : syracuseStep 26693225 = 20019919) B20019919
theorem B17795483 : Blo 2081435 17795483 := bstep (se 1 (by rfl) ⟨13346612, by rfl⟩ : syracuseStep 17795483 = 26693225) B26693225
theorem B11863655 : Blo 2081435 11863655 := bstep (se 1 (by rfl) ⟨8897741, by rfl⟩ : syracuseStep 11863655 = 17795483) B17795483
theorem B7909103 : Blo 2081435 7909103 := bstep (se 1 (by rfl) ⟨5931827, by rfl⟩ : syracuseStep 7909103 = 11863655) B11863655
theorem B5272735 : Blo 2081435 5272735 := bstep (se 1 (by rfl) ⟨3954551, by rfl⟩ : syracuseStep 5272735 = 7909103) B7909103
theorem B7030313 : Blo 2081435 7030313 := bstep (se 2 (by rfl) ⟨2636367, by rfl⟩ : syracuseStep 7030313 = 5272735) B5272735
theorem B4686875 : Blo 2081435 4686875 := bstep (se 1 (by rfl) ⟨3515156, by rfl⟩ : syracuseStep 4686875 = 7030313) B7030313
theorem B3124583 : Blo 2081435 3124583 := bstep (se 1 (by rfl) ⟨2343437, by rfl⟩ : syracuseStep 3124583 = 4686875) B4686875
theorem B2083055 : Blo 2081435 2083055 := bstep (se 1 (by rfl) ⟨1562291, by rfl⟩ : syracuseStep 2083055 = 3124583) B3124583
theorem B3124589 : Blo 2081435 3124589 := bbase (se 3 (by rfl) ⟨585860, by rfl⟩ : syracuseStep 3124589 = 1171721) (by norm_num)
theorem B2083059 : Blo 2081435 2083059 := bstep (se 1 (by rfl) ⟨1562294, by rfl⟩ : syracuseStep 2083059 = 3124589) B3124589
theorem B4686893 : Blo 2081435 4686893 := bbase (se 3 (by rfl) ⟨878792, by rfl⟩ : syracuseStep 4686893 = 1757585) (by norm_num)
theorem B3124595 : Blo 2081435 3124595 := bstep (se 1 (by rfl) ⟨2343446, by rfl⟩ : syracuseStep 3124595 = 4686893) B4686893
theorem B2083063 : Blo 2081435 2083063 := bstep (se 1 (by rfl) ⟨1562297, by rfl⟩ : syracuseStep 2083063 = 3124595) B3124595
theorem B2502505 : Blo 2081435 2502505 := bbase (se 2 (by rfl) ⟨938439, by rfl⟩ : syracuseStep 2502505 = 1876879) (by norm_num)
theorem B13346693 : Blo 2081435 13346693 := bstep (se 4 (by rfl) ⟨1251252, by rfl⟩ : syracuseStep 13346693 = 2502505) B2502505
theorem B8897795 : Blo 2081435 8897795 := bstep (se 1 (by rfl) ⟨6673346, by rfl⟩ : syracuseStep 8897795 = 13346693) B13346693
theorem B5931863 : Blo 2081435 5931863 := bstep (se 1 (by rfl) ⟨4448897, by rfl⟩ : syracuseStep 5931863 = 8897795) B8897795
theorem B3954575 : Blo 2081435 3954575 := bstep (se 1 (by rfl) ⟨2965931, by rfl⟩ : syracuseStep 3954575 = 5931863) B5931863
theorem B2636383 : Blo 2081435 2636383 := bstep (se 1 (by rfl) ⟨1977287, by rfl⟩ : syracuseStep 2636383 = 3954575) B3954575
theorem B3515177 : Blo 2081435 3515177 := bstep (se 2 (by rfl) ⟨1318191, by rfl⟩ : syracuseStep 3515177 = 2636383) B2636383
theorem B2343451 : Blo 2081435 2343451 := bstep (se 1 (by rfl) ⟨1757588, by rfl⟩ : syracuseStep 2343451 = 3515177) B3515177
theorem B3124601 : Blo 2081435 3124601 := bstep (se 2 (by rfl) ⟨1171725, by rfl⟩ : syracuseStep 3124601 = 2343451) B2343451
theorem B2083067 : Blo 2081435 2083067 := bstep (se 1 (by rfl) ⟨1562300, by rfl⟩ : syracuseStep 2083067 = 3124601) B3124601
theorem B2502509 : Blo 2081435 2502509 := bbase (se 3 (by rfl) ⟨469220, by rfl⟩ : syracuseStep 2502509 = 938441) (by norm_num)
theorem B6673357 : Blo 2081435 6673357 := bstep (se 3 (by rfl) ⟨1251254, by rfl⟩ : syracuseStep 6673357 = 2502509) B2502509
theorem B35591237 : Blo 2081435 35591237 := bstep (se 4 (by rfl) ⟨3336678, by rfl⟩ : syracuseStep 35591237 = 6673357) B6673357
theorem B23727491 : Blo 2081435 23727491 := bstep (se 1 (by rfl) ⟨17795618, by rfl⟩ : syracuseStep 23727491 = 35591237) B35591237
theorem B15818327 : Blo 2081435 15818327 := bstep (se 1 (by rfl) ⟨11863745, by rfl⟩ : syracuseStep 15818327 = 23727491) B23727491
theorem B10545551 : Blo 2081435 10545551 := bstep (se 1 (by rfl) ⟨7909163, by rfl⟩ : syracuseStep 10545551 = 15818327) B15818327
theorem B7030367 : Blo 2081435 7030367 := bstep (se 1 (by rfl) ⟨5272775, by rfl⟩ : syracuseStep 7030367 = 10545551) B10545551
theorem B4686911 : Blo 2081435 4686911 := bstep (se 1 (by rfl) ⟨3515183, by rfl⟩ : syracuseStep 4686911 = 7030367) B7030367
theorem B3124607 : Blo 2081435 3124607 := bstep (se 1 (by rfl) ⟨2343455, by rfl⟩ : syracuseStep 3124607 = 4686911) B4686911
theorem B2083071 : Blo 2081435 2083071 := bstep (se 1 (by rfl) ⟨1562303, by rfl⟩ : syracuseStep 2083071 = 3124607) B3124607
theorem B3124613 : Blo 2081435 3124613 := bbase (se 4 (by rfl) ⟨292932, by rfl⟩ : syracuseStep 3124613 = 585865) (by norm_num)
theorem B2083075 : Blo 2081435 2083075 := bstep (se 1 (by rfl) ⟨1562306, by rfl⟩ : syracuseStep 2083075 = 3124613) B3124613
theorem B3515197 : Blo 2081435 3515197 := bbase (se 3 (by rfl) ⟨659099, by rfl⟩ : syracuseStep 3515197 = 1318199) (by norm_num)
theorem B4686929 : Blo 2081435 4686929 := bstep (se 2 (by rfl) ⟨1757598, by rfl⟩ : syracuseStep 4686929 = 3515197) B3515197
theorem B3124619 : Blo 2081435 3124619 := bstep (se 1 (by rfl) ⟨2343464, by rfl⟩ : syracuseStep 3124619 = 4686929) B4686929
theorem B2083079 : Blo 2081435 2083079 := bstep (se 1 (by rfl) ⟨1562309, by rfl⟩ : syracuseStep 2083079 = 3124619) B3124619
theorem B2343469 : Blo 2081435 2343469 := bbase (se 3 (by rfl) ⟨439400, by rfl⟩ : syracuseStep 2343469 = 878801) (by norm_num)
theorem B3124625 : Blo 2081435 3124625 := bstep (se 2 (by rfl) ⟨1171734, by rfl⟩ : syracuseStep 3124625 = 2343469) B2343469
theorem B2083083 : Blo 2081435 2083083 := bstep (se 1 (by rfl) ⟨1562312, by rfl⟩ : syracuseStep 2083083 = 3124625) B3124625
theorem B7030421 : Blo 2081435 7030421 := bbase (se 6 (by rfl) ⟨164775, by rfl⟩ : syracuseStep 7030421 = 329551) (by norm_num)
theorem B4686947 : Blo 2081435 4686947 := bstep (se 1 (by rfl) ⟨3515210, by rfl⟩ : syracuseStep 4686947 = 7030421) B7030421
theorem B3124631 : Blo 2081435 3124631 := bstep (se 1 (by rfl) ⟨2343473, by rfl⟩ : syracuseStep 3124631 = 4686947) B4686947
theorem B2083087 : Blo 2081435 2083087 := bstep (se 1 (by rfl) ⟨1562315, by rfl⟩ : syracuseStep 2083087 = 3124631) B3124631
theorem B3124637 : Blo 2081435 3124637 := bbase (se 3 (by rfl) ⟨585869, by rfl⟩ : syracuseStep 3124637 = 1171739) (by norm_num)
theorem B2083091 : Blo 2081435 2083091 := bstep (se 1 (by rfl) ⟨1562318, by rfl⟩ : syracuseStep 2083091 = 3124637) B3124637
theorem B4686965 : Blo 2081435 4686965 := bbase (se 5 (by rfl) ⟨219701, by rfl⟩ : syracuseStep 4686965 = 439403) (by norm_num)
theorem B3124643 : Blo 2081435 3124643 := bstep (se 1 (by rfl) ⟨2343482, by rfl⟩ : syracuseStep 3124643 = 4686965) B4686965
theorem B2083095 : Blo 2081435 2083095 := bstep (se 1 (by rfl) ⟨1562321, by rfl⟩ : syracuseStep 2083095 = 3124643) B3124643
theorem B17795861 : Blo 2081435 17795861 := bbase (se 6 (by rfl) ⟨417090, by rfl⟩ : syracuseStep 17795861 = 834181) (by norm_num)
theorem B11863907 : Blo 2081435 11863907 := bstep (se 1 (by rfl) ⟨8897930, by rfl⟩ : syracuseStep 11863907 = 17795861) B17795861
theorem B7909271 : Blo 2081435 7909271 := bstep (se 1 (by rfl) ⟨5931953, by rfl⟩ : syracuseStep 7909271 = 11863907) B11863907
theorem B5272847 : Blo 2081435 5272847 := bstep (se 1 (by rfl) ⟨3954635, by rfl⟩ : syracuseStep 5272847 = 7909271) B7909271
theorem B3515231 : Blo 2081435 3515231 := bstep (se 1 (by rfl) ⟨2636423, by rfl⟩ : syracuseStep 3515231 = 5272847) B5272847
theorem B2343487 : Blo 2081435 2343487 := bstep (se 1 (by rfl) ⟨1757615, by rfl⟩ : syracuseStep 2343487 = 3515231) B3515231
theorem B3124649 : Blo 2081435 3124649 := bstep (se 2 (by rfl) ⟨1171743, by rfl⟩ : syracuseStep 3124649 = 2343487) B2343487
theorem B2083099 : Blo 2081435 2083099 := bstep (se 1 (by rfl) ⟨1562324, by rfl⟩ : syracuseStep 2083099 = 3124649) B3124649
theorem B7909285 : Blo 2081435 7909285 := bbase (se 4 (by rfl) ⟨741495, by rfl⟩ : syracuseStep 7909285 = 1482991) (by norm_num)
theorem B10545713 : Blo 2081435 10545713 := bstep (se 2 (by rfl) ⟨3954642, by rfl⟩ : syracuseStep 10545713 = 7909285) B7909285
theorem B7030475 : Blo 2081435 7030475 := bstep (se 1 (by rfl) ⟨5272856, by rfl⟩ : syracuseStep 7030475 = 10545713) B10545713
theorem B4686983 : Blo 2081435 4686983 := bstep (se 1 (by rfl) ⟨3515237, by rfl⟩ : syracuseStep 4686983 = 7030475) B7030475
theorem B3124655 : Blo 2081435 3124655 := bstep (se 1 (by rfl) ⟨2343491, by rfl⟩ : syracuseStep 3124655 = 4686983) B4686983
theorem B2083103 : Blo 2081435 2083103 := bstep (se 1 (by rfl) ⟨1562327, by rfl⟩ : syracuseStep 2083103 = 3124655) B3124655
theorem B3124661 : Blo 2081435 3124661 := bbase (se 5 (by rfl) ⟨146468, by rfl⟩ : syracuseStep 3124661 = 292937) (by norm_num)
theorem B2083107 : Blo 2081435 2083107 := bstep (se 1 (by rfl) ⟨1562330, by rfl⟩ : syracuseStep 2083107 = 3124661) B3124661
theorem B5272877 : Blo 2081435 5272877 := bbase (se 3 (by rfl) ⟨988664, by rfl⟩ : syracuseStep 5272877 = 1977329) (by norm_num)
theorem B3515251 : Blo 2081435 3515251 := bstep (se 1 (by rfl) ⟨2636438, by rfl⟩ : syracuseStep 3515251 = 5272877) B5272877
theorem B4687001 : Blo 2081435 4687001 := bstep (se 2 (by rfl) ⟨1757625, by rfl⟩ : syracuseStep 4687001 = 3515251) B3515251
theorem B3124667 : Blo 2081435 3124667 := bstep (se 1 (by rfl) ⟨2343500, by rfl⟩ : syracuseStep 3124667 = 4687001) B4687001
theorem B2083111 : Blo 2081435 2083111 := bstep (se 1 (by rfl) ⟨1562333, by rfl⟩ : syracuseStep 2083111 = 3124667) B3124667
theorem B2343505 : Blo 2081435 2343505 := bbase (se 2 (by rfl) ⟨878814, by rfl⟩ : syracuseStep 2343505 = 1757629) (by norm_num)
theorem B3124673 : Blo 2081435 3124673 := bstep (se 2 (by rfl) ⟨1171752, by rfl⟩ : syracuseStep 3124673 = 2343505) B2343505
theorem B2083115 : Blo 2081435 2083115 := bstep (se 1 (by rfl) ⟨1562336, by rfl⟩ : syracuseStep 2083115 = 3124673) B3124673
theorem B2966005 : Blo 2081435 2966005 := bbase (se 5 (by rfl) ⟨139031, by rfl⟩ : syracuseStep 2966005 = 278063) (by norm_num)
theorem B3954673 : Blo 2081435 3954673 := bstep (se 2 (by rfl) ⟨1483002, by rfl⟩ : syracuseStep 3954673 = 2966005) B2966005
theorem B5272897 : Blo 2081435 5272897 := bstep (se 2 (by rfl) ⟨1977336, by rfl⟩ : syracuseStep 5272897 = 3954673) B3954673
theorem B7030529 : Blo 2081435 7030529 := bstep (se 2 (by rfl) ⟨2636448, by rfl⟩ : syracuseStep 7030529 = 5272897) B5272897
theorem B4687019 : Blo 2081435 4687019 := bstep (se 1 (by rfl) ⟨3515264, by rfl⟩ : syracuseStep 4687019 = 7030529) B7030529
theorem B3124679 : Blo 2081435 3124679 := bstep (se 1 (by rfl) ⟨2343509, by rfl⟩ : syracuseStep 3124679 = 4687019) B4687019
theorem B2083119 : Blo 2081435 2083119 := bstep (se 1 (by rfl) ⟨1562339, by rfl⟩ : syracuseStep 2083119 = 3124679) B3124679
theorem B3124685 : Blo 2081435 3124685 := bbase (se 3 (by rfl) ⟨585878, by rfl⟩ : syracuseStep 3124685 = 1171757) (by norm_num)
theorem B2083123 : Blo 2081435 2083123 := bstep (se 1 (by rfl) ⟨1562342, by rfl⟩ : syracuseStep 2083123 = 3124685) B3124685
theorem B4687037 : Blo 2081435 4687037 := bbase (se 3 (by rfl) ⟨878819, by rfl⟩ : syracuseStep 4687037 = 1757639) (by norm_num)
theorem B3124691 : Blo 2081435 3124691 := bstep (se 1 (by rfl) ⟨2343518, by rfl⟩ : syracuseStep 3124691 = 4687037) B4687037
theorem B2083127 : Blo 2081435 2083127 := bstep (se 1 (by rfl) ⟨1562345, by rfl⟩ : syracuseStep 2083127 = 3124691) B3124691
theorem B3515285 : Blo 2081435 3515285 := bbase (se 6 (by rfl) ⟨82389, by rfl⟩ : syracuseStep 3515285 = 164779) (by norm_num)
theorem B2343523 : Blo 2081435 2343523 := bstep (se 1 (by rfl) ⟨1757642, by rfl⟩ : syracuseStep 2343523 = 3515285) B3515285
theorem B3124697 : Blo 2081435 3124697 := bstep (se 2 (by rfl) ⟨1171761, by rfl⟩ : syracuseStep 3124697 = 2343523) B2343523
theorem B2083131 : Blo 2081435 2083131 := bstep (se 1 (by rfl) ⟨1562348, by rfl⟩ : syracuseStep 2083131 = 3124697) B3124697
theorem B13347125 : Blo 2081435 13347125 := bbase (se 5 (by rfl) ⟨625646, by rfl⟩ : syracuseStep 13347125 = 1251293) (by norm_num)
theorem B8898083 : Blo 2081435 8898083 := bstep (se 1 (by rfl) ⟨6673562, by rfl⟩ : syracuseStep 8898083 = 13347125) B13347125
theorem B5932055 : Blo 2081435 5932055 := bstep (se 1 (by rfl) ⟨4449041, by rfl⟩ : syracuseStep 5932055 = 8898083) B8898083
theorem B15818813 : Blo 2081435 15818813 := bstep (se 3 (by rfl) ⟨2966027, by rfl⟩ : syracuseStep 15818813 = 5932055) B5932055
theorem B10545875 : Blo 2081435 10545875 := bstep (se 1 (by rfl) ⟨7909406, by rfl⟩ : syracuseStep 10545875 = 15818813) B15818813
theorem B7030583 : Blo 2081435 7030583 := bstep (se 1 (by rfl) ⟨5272937, by rfl⟩ : syracuseStep 7030583 = 10545875) B10545875
theorem B4687055 : Blo 2081435 4687055 := bstep (se 1 (by rfl) ⟨3515291, by rfl⟩ : syracuseStep 4687055 = 7030583) B7030583
theorem B3124703 : Blo 2081435 3124703 := bstep (se 1 (by rfl) ⟨2343527, by rfl⟩ : syracuseStep 3124703 = 4687055) B4687055
theorem B2083135 : Blo 2081435 2083135 := bstep (se 1 (by rfl) ⟨1562351, by rfl⟩ : syracuseStep 2083135 = 3124703) B3124703
theorem B3124709 : Blo 2081435 3124709 := bbase (se 4 (by rfl) ⟨292941, by rfl⟩ : syracuseStep 3124709 = 585883) (by norm_num)
theorem B2083139 : Blo 2081435 2083139 := bstep (se 1 (by rfl) ⟨1562354, by rfl⟩ : syracuseStep 2083139 = 3124709) B3124709
theorem B2536741 : Blo 2081435 2536741 := bbase (se 4 (by rfl) ⟨237819, by rfl⟩ : syracuseStep 2536741 = 475639) (by norm_num)
theorem B3382321 : Blo 2081435 3382321 := bstep (se 2 (by rfl) ⟨1268370, by rfl⟩ : syracuseStep 3382321 = 2536741) B2536741
theorem B4509761 : Blo 2081435 4509761 := bstep (se 2 (by rfl) ⟨1691160, by rfl⟩ : syracuseStep 4509761 = 3382321) B3382321
theorem B12026029 : Blo 2081435 12026029 := bstep (se 3 (by rfl) ⟨2254880, by rfl⟩ : syracuseStep 12026029 = 4509761) B4509761
theorem B16034705 : Blo 2081435 16034705 := bstep (se 2 (by rfl) ⟨6013014, by rfl⟩ : syracuseStep 16034705 = 12026029) B12026029
theorem B10689803 : Blo 2081435 10689803 := bstep (se 1 (by rfl) ⟨8017352, by rfl⟩ : syracuseStep 10689803 = 16034705) B16034705
theorem B7126535 : Blo 2081435 7126535 := bstep (se 1 (by rfl) ⟨5344901, by rfl⟩ : syracuseStep 7126535 = 10689803) B10689803
theorem B4751023 : Blo 2081435 4751023 := bstep (se 1 (by rfl) ⟨3563267, by rfl⟩ : syracuseStep 4751023 = 7126535) B7126535
theorem B6334697 : Blo 2081435 6334697 := bstep (se 2 (by rfl) ⟨2375511, by rfl⟩ : syracuseStep 6334697 = 4751023) B4751023
theorem B16892525 : Blo 2081435 16892525 := bstep (se 3 (by rfl) ⟨3167348, by rfl⟩ : syracuseStep 16892525 = 6334697) B6334697
theorem B11261683 : Blo 2081435 11261683 := bstep (se 1 (by rfl) ⟨8446262, by rfl⟩ : syracuseStep 11261683 = 16892525) B16892525
theorem B15015577 : Blo 2081435 15015577 := bstep (se 2 (by rfl) ⟨5630841, by rfl⟩ : syracuseStep 15015577 = 11261683) B11261683
theorem B20020769 : Blo 2081435 20020769 := bstep (se 2 (by rfl) ⟨7507788, by rfl⟩ : syracuseStep 20020769 = 15015577) B15015577
theorem B13347179 : Blo 2081435 13347179 := bstep (se 1 (by rfl) ⟨10010384, by rfl⟩ : syracuseStep 13347179 = 20020769) B20020769
theorem B8898119 : Blo 2081435 8898119 := bstep (se 1 (by rfl) ⟨6673589, by rfl⟩ : syracuseStep 8898119 = 13347179) B13347179
theorem B5932079 : Blo 2081435 5932079 := bstep (se 1 (by rfl) ⟨4449059, by rfl⟩ : syracuseStep 5932079 = 8898119) B8898119
theorem B3954719 : Blo 2081435 3954719 := bstep (se 1 (by rfl) ⟨2966039, by rfl⟩ : syracuseStep 3954719 = 5932079) B5932079
theorem B2636479 : Blo 2081435 2636479 := bstep (se 1 (by rfl) ⟨1977359, by rfl⟩ : syracuseStep 2636479 = 3954719) B3954719
theorem B3515305 : Blo 2081435 3515305 := bstep (se 2 (by rfl) ⟨1318239, by rfl⟩ : syracuseStep 3515305 = 2636479) B2636479
theorem B4687073 : Blo 2081435 4687073 := bstep (se 2 (by rfl) ⟨1757652, by rfl⟩ : syracuseStep 4687073 = 3515305) B3515305
theorem B3124715 : Blo 2081435 3124715 := bstep (se 1 (by rfl) ⟨2343536, by rfl⟩ : syracuseStep 3124715 = 4687073) B4687073
theorem B2083143 : Blo 2081435 2083143 := bstep (se 1 (by rfl) ⟨1562357, by rfl⟩ : syracuseStep 2083143 = 3124715) B3124715
theorem B2343541 : Blo 2081435 2343541 := bbase (se 5 (by rfl) ⟨109853, by rfl⟩ : syracuseStep 2343541 = 219707) (by norm_num)
theorem B3124721 : Blo 2081435 3124721 := bstep (se 2 (by rfl) ⟨1171770, by rfl⟩ : syracuseStep 3124721 = 2343541) B2343541
theorem B2083147 : Blo 2081435 2083147 := bstep (se 1 (by rfl) ⟨1562360, by rfl⟩ : syracuseStep 2083147 = 3124721) B3124721
theorem B2636489 : Blo 2081435 2636489 := bbase (se 2 (by rfl) ⟨988683, by rfl⟩ : syracuseStep 2636489 = 1977367) (by norm_num)
theorem B7030637 : Blo 2081435 7030637 := bstep (se 3 (by rfl) ⟨1318244, by rfl⟩ : syracuseStep 7030637 = 2636489) B2636489
theorem B4687091 : Blo 2081435 4687091 := bstep (se 1 (by rfl) ⟨3515318, by rfl⟩ : syracuseStep 4687091 = 7030637) B7030637
theorem B3124727 : Blo 2081435 3124727 := bstep (se 1 (by rfl) ⟨2343545, by rfl⟩ : syracuseStep 3124727 = 4687091) B4687091
theorem B2083151 : Blo 2081435 2083151 := bstep (se 1 (by rfl) ⟨1562363, by rfl⟩ : syracuseStep 2083151 = 3124727) B3124727
theorem B3124733 : Blo 2081435 3124733 := bbase (se 3 (by rfl) ⟨585887, by rfl⟩ : syracuseStep 3124733 = 1171775) (by norm_num)
theorem B2083155 : Blo 2081435 2083155 := bstep (se 1 (by rfl) ⟨1562366, by rfl⟩ : syracuseStep 2083155 = 3124733) B3124733
theorem B4687109 : Blo 2081435 4687109 := bbase (se 4 (by rfl) ⟨439416, by rfl⟩ : syracuseStep 4687109 = 878833) (by norm_num)
theorem B3124739 : Blo 2081435 3124739 := bstep (se 1 (by rfl) ⟨2343554, by rfl⟩ : syracuseStep 3124739 = 4687109) B4687109
theorem B2083159 : Blo 2081435 2083159 := bstep (se 1 (by rfl) ⟨1562369, by rfl⟩ : syracuseStep 2083159 = 3124739) B3124739
theorem B3954757 : Blo 2081435 3954757 := bbase (se 4 (by rfl) ⟨370758, by rfl⟩ : syracuseStep 3954757 = 741517) (by norm_num)
theorem B5273009 : Blo 2081435 5273009 := bstep (se 2 (by rfl) ⟨1977378, by rfl⟩ : syracuseStep 5273009 = 3954757) B3954757
theorem B3515339 : Blo 2081435 3515339 := bstep (se 1 (by rfl) ⟨2636504, by rfl⟩ : syracuseStep 3515339 = 5273009) B5273009
theorem B2343559 : Blo 2081435 2343559 := bstep (se 1 (by rfl) ⟨1757669, by rfl⟩ : syracuseStep 2343559 = 3515339) B3515339
theorem B3124745 : Blo 2081435 3124745 := bstep (se 2 (by rfl) ⟨1171779, by rfl⟩ : syracuseStep 3124745 = 2343559) B2343559
theorem B2083163 : Blo 2081435 2083163 := bstep (se 1 (by rfl) ⟨1562372, by rfl⟩ : syracuseStep 2083163 = 3124745) B3124745
theorem B10546037 : Blo 2081435 10546037 := bbase (se 5 (by rfl) ⟨494345, by rfl⟩ : syracuseStep 10546037 = 988691) (by norm_num)
theorem B7030691 : Blo 2081435 7030691 := bstep (se 1 (by rfl) ⟨5273018, by rfl⟩ : syracuseStep 7030691 = 10546037) B10546037
theorem B4687127 : Blo 2081435 4687127 := bstep (se 1 (by rfl) ⟨3515345, by rfl⟩ : syracuseStep 4687127 = 7030691) B7030691
theorem B3124751 : Blo 2081435 3124751 := bstep (se 1 (by rfl) ⟨2343563, by rfl⟩ : syracuseStep 3124751 = 4687127) B4687127
theorem B2083167 : Blo 2081435 2083167 := bstep (se 1 (by rfl) ⟨1562375, by rfl⟩ : syracuseStep 2083167 = 3124751) B3124751
theorem B3124757 : Blo 2081435 3124757 := bbase (se 6 (by rfl) ⟨73236, by rfl⟩ : syracuseStep 3124757 = 146473) (by norm_num)
theorem B2083171 : Blo 2081435 2083171 := bstep (se 1 (by rfl) ⟨1562378, by rfl⟩ : syracuseStep 2083171 = 3124757) B3124757
theorem B4509829 : Blo 2081435 4509829 := bbase (se 4 (by rfl) ⟨422796, by rfl⟩ : syracuseStep 4509829 = 845593) (by norm_num)
theorem B24052421 : Blo 2081435 24052421 := bstep (se 4 (by rfl) ⟨2254914, by rfl⟩ : syracuseStep 24052421 = 4509829) B4509829
theorem B64139789 : Blo 2081435 64139789 := bstep (se 3 (by rfl) ⟨12026210, by rfl⟩ : syracuseStep 64139789 = 24052421) B24052421
theorem B42759859 : Blo 2081435 42759859 := bstep (se 1 (by rfl) ⟨32069894, by rfl⟩ : syracuseStep 42759859 = 64139789) B64139789
theorem B57013145 : Blo 2081435 57013145 := bstep (se 2 (by rfl) ⟨21379929, by rfl⟩ : syracuseStep 57013145 = 42759859) B42759859
theorem B38008763 : Blo 2081435 38008763 := bstep (se 1 (by rfl) ⟨28506572, by rfl⟩ : syracuseStep 38008763 = 57013145) B57013145
theorem B25339175 : Blo 2081435 25339175 := bstep (se 1 (by rfl) ⟨19004381, by rfl⟩ : syracuseStep 25339175 = 38008763) B38008763
theorem B16892783 : Blo 2081435 16892783 := bstep (se 1 (by rfl) ⟨12669587, by rfl⟩ : syracuseStep 16892783 = 25339175) B25339175
theorem B11261855 : Blo 2081435 11261855 := bstep (se 1 (by rfl) ⟨8446391, by rfl⟩ : syracuseStep 11261855 = 16892783) B16892783
theorem B7507903 : Blo 2081435 7507903 := bstep (se 1 (by rfl) ⟨5630927, by rfl⟩ : syracuseStep 7507903 = 11261855) B11261855
theorem B10010537 : Blo 2081435 10010537 := bstep (se 2 (by rfl) ⟨3753951, by rfl⟩ : syracuseStep 10010537 = 7507903) B7507903
theorem B6673691 : Blo 2081435 6673691 := bstep (se 1 (by rfl) ⟨5005268, by rfl⟩ : syracuseStep 6673691 = 10010537) B10010537
theorem B17796509 : Blo 2081435 17796509 := bstep (se 3 (by rfl) ⟨3336845, by rfl⟩ : syracuseStep 17796509 = 6673691) B6673691
theorem B11864339 : Blo 2081435 11864339 := bstep (se 1 (by rfl) ⟨8898254, by rfl⟩ : syracuseStep 11864339 = 17796509) B17796509
theorem B7909559 : Blo 2081435 7909559 := bstep (se 1 (by rfl) ⟨5932169, by rfl⟩ : syracuseStep 7909559 = 11864339) B11864339
theorem B5273039 : Blo 2081435 5273039 := bstep (se 1 (by rfl) ⟨3954779, by rfl⟩ : syracuseStep 5273039 = 7909559) B7909559
theorem B3515359 : Blo 2081435 3515359 := bstep (se 1 (by rfl) ⟨2636519, by rfl⟩ : syracuseStep 3515359 = 5273039) B5273039
theorem B4687145 : Blo 2081435 4687145 := bstep (se 2 (by rfl) ⟨1757679, by rfl⟩ : syracuseStep 4687145 = 3515359) B3515359
theorem B3124763 : Blo 2081435 3124763 := bstep (se 1 (by rfl) ⟨2343572, by rfl⟩ : syracuseStep 3124763 = 4687145) B4687145
theorem B2083175 : Blo 2081435 2083175 := bstep (se 1 (by rfl) ⟨1562381, by rfl⟩ : syracuseStep 2083175 = 3124763) B3124763
theorem B2343577 : Blo 2081435 2343577 := bbase (se 2 (by rfl) ⟨878841, by rfl⟩ : syracuseStep 2343577 = 1757683) (by norm_num)
theorem B3124769 : Blo 2081435 3124769 := bstep (se 2 (by rfl) ⟨1171788, by rfl⟩ : syracuseStep 3124769 = 2343577) B2343577
theorem B2083179 : Blo 2081435 2083179 := bstep (se 1 (by rfl) ⟨1562384, by rfl⟩ : syracuseStep 2083179 = 3124769) B3124769
theorem B7909589 : Blo 2081435 7909589 := bbase (se 7 (by rfl) ⟨92690, by rfl⟩ : syracuseStep 7909589 = 185381) (by norm_num)
theorem B5273059 : Blo 2081435 5273059 := bstep (se 1 (by rfl) ⟨3954794, by rfl⟩ : syracuseStep 5273059 = 7909589) B7909589
theorem B7030745 : Blo 2081435 7030745 := bstep (se 2 (by rfl) ⟨2636529, by rfl⟩ : syracuseStep 7030745 = 5273059) B5273059
theorem B4687163 : Blo 2081435 4687163 := bstep (se 1 (by rfl) ⟨3515372, by rfl⟩ : syracuseStep 4687163 = 7030745) B7030745
theorem B3124775 : Blo 2081435 3124775 := bstep (se 1 (by rfl) ⟨2343581, by rfl⟩ : syracuseStep 3124775 = 4687163) B4687163
theorem B2083183 : Blo 2081435 2083183 := bstep (se 1 (by rfl) ⟨1562387, by rfl⟩ : syracuseStep 2083183 = 3124775) B3124775
theorem B3124781 : Blo 2081435 3124781 := bbase (se 3 (by rfl) ⟨585896, by rfl⟩ : syracuseStep 3124781 = 1171793) (by norm_num)
theorem B2083187 : Blo 2081435 2083187 := bstep (se 1 (by rfl) ⟨1562390, by rfl⟩ : syracuseStep 2083187 = 3124781) B3124781
theorem B4687181 : Blo 2081435 4687181 := bbase (se 3 (by rfl) ⟨878846, by rfl⟩ : syracuseStep 4687181 = 1757693) (by norm_num)
theorem B3124787 : Blo 2081435 3124787 := bstep (se 1 (by rfl) ⟨2343590, by rfl⟩ : syracuseStep 3124787 = 4687181) B4687181
theorem B2083191 : Blo 2081435 2083191 := bstep (se 1 (by rfl) ⟨1562393, by rfl⟩ : syracuseStep 2083191 = 3124787) B3124787
theorem B2636545 : Blo 2081435 2636545 := bbase (se 2 (by rfl) ⟨988704, by rfl⟩ : syracuseStep 2636545 = 1977409) (by norm_num)
theorem B3515393 : Blo 2081435 3515393 := bstep (se 2 (by rfl) ⟨1318272, by rfl⟩ : syracuseStep 3515393 = 2636545) B2636545
theorem B2343595 : Blo 2081435 2343595 := bstep (se 1 (by rfl) ⟨1757696, by rfl⟩ : syracuseStep 2343595 = 3515393) B3515393
theorem B3124793 : Blo 2081435 3124793 := bstep (se 2 (by rfl) ⟨1171797, by rfl⟩ : syracuseStep 3124793 = 2343595) B2343595
theorem B2083195 : Blo 2081435 2083195 := bstep (se 1 (by rfl) ⟨1562396, by rfl⟩ : syracuseStep 2083195 = 3124793) B3124793
theorem B2224589 : Blo 2081435 2224589 := bbase (se 3 (by rfl) ⟨417110, by rfl⟩ : syracuseStep 2224589 = 834221) (by norm_num)
theorem B23728949 : Blo 2081435 23728949 := bstep (se 5 (by rfl) ⟨1112294, by rfl⟩ : syracuseStep 23728949 = 2224589) B2224589
theorem B15819299 : Blo 2081435 15819299 := bstep (se 1 (by rfl) ⟨11864474, by rfl⟩ : syracuseStep 15819299 = 23728949) B23728949
theorem B10546199 : Blo 2081435 10546199 := bstep (se 1 (by rfl) ⟨7909649, by rfl⟩ : syracuseStep 10546199 = 15819299) B15819299
theorem B7030799 : Blo 2081435 7030799 := bstep (se 1 (by rfl) ⟨5273099, by rfl⟩ : syracuseStep 7030799 = 10546199) B10546199
theorem B4687199 : Blo 2081435 4687199 := bstep (se 1 (by rfl) ⟨3515399, by rfl⟩ : syracuseStep 4687199 = 7030799) B7030799
theorem B3124799 : Blo 2081435 3124799 := bstep (se 1 (by rfl) ⟨2343599, by rfl⟩ : syracuseStep 3124799 = 4687199) B4687199
theorem B2083199 : Blo 2081435 2083199 := bstep (se 1 (by rfl) ⟨1562399, by rfl⟩ : syracuseStep 2083199 = 3124799) B3124799
theorem B3124805 : Blo 2081435 3124805 := bbase (se 4 (by rfl) ⟨292950, by rfl⟩ : syracuseStep 3124805 = 585901) (by norm_num)
theorem B2083203 : Blo 2081435 2083203 := bstep (se 1 (by rfl) ⟨1562402, by rfl⟩ : syracuseStep 2083203 = 3124805) B3124805
theorem B3515413 : Blo 2081435 3515413 := bbase (se 6 (by rfl) ⟨82392, by rfl⟩ : syracuseStep 3515413 = 164785) (by norm_num)
theorem B4687217 : Blo 2081435 4687217 := bstep (se 2 (by rfl) ⟨1757706, by rfl⟩ : syracuseStep 4687217 = 3515413) B3515413
theorem B3124811 : Blo 2081435 3124811 := bstep (se 1 (by rfl) ⟨2343608, by rfl⟩ : syracuseStep 3124811 = 4687217) B4687217
theorem B2083207 : Blo 2081435 2083207 := bstep (se 1 (by rfl) ⟨1562405, by rfl⟩ : syracuseStep 2083207 = 3124811) B3124811
theorem B2343613 : Blo 2081435 2343613 := bbase (se 3 (by rfl) ⟨439427, by rfl⟩ : syracuseStep 2343613 = 878855) (by norm_num)
theorem B3124817 : Blo 2081435 3124817 := bstep (se 2 (by rfl) ⟨1171806, by rfl⟩ : syracuseStep 3124817 = 2343613) B2343613
theorem B2083211 : Blo 2081435 2083211 := bstep (se 1 (by rfl) ⟨1562408, by rfl⟩ : syracuseStep 2083211 = 3124817) B3124817
theorem B7030853 : Blo 2081435 7030853 := bbase (se 4 (by rfl) ⟨659142, by rfl⟩ : syracuseStep 7030853 = 1318285) (by norm_num)
theorem B4687235 : Blo 2081435 4687235 := bstep (se 1 (by rfl) ⟨3515426, by rfl⟩ : syracuseStep 4687235 = 7030853) B7030853
theorem B3124823 : Blo 2081435 3124823 := bstep (se 1 (by rfl) ⟨2343617, by rfl⟩ : syracuseStep 3124823 = 4687235) B4687235
theorem B2083215 : Blo 2081435 2083215 := bstep (se 1 (by rfl) ⟨1562411, by rfl⟩ : syracuseStep 2083215 = 3124823) B3124823
theorem B3124829 : Blo 2081435 3124829 := bbase (se 3 (by rfl) ⟨585905, by rfl⟩ : syracuseStep 3124829 = 1171811) (by norm_num)
theorem B2083219 : Blo 2081435 2083219 := bstep (se 1 (by rfl) ⟨1562414, by rfl⟩ : syracuseStep 2083219 = 3124829) B3124829
theorem B4687253 : Blo 2081435 4687253 := bbase (se 6 (by rfl) ⟨109857, by rfl⟩ : syracuseStep 4687253 = 219715) (by norm_num)
theorem B3124835 : Blo 2081435 3124835 := bstep (se 1 (by rfl) ⟨2343626, by rfl⟩ : syracuseStep 3124835 = 4687253) B4687253
theorem B2083223 : Blo 2081435 2083223 := bstep (se 1 (by rfl) ⟨1562417, by rfl⟩ : syracuseStep 2083223 = 3124835) B3124835
theorem B10010789 : Blo 2081435 10010789 := bbase (se 4 (by rfl) ⟨938511, by rfl⟩ : syracuseStep 10010789 = 1877023) (by norm_num)
theorem B6673859 : Blo 2081435 6673859 := bstep (se 1 (by rfl) ⟨5005394, by rfl⟩ : syracuseStep 6673859 = 10010789) B10010789
theorem B4449239 : Blo 2081435 4449239 := bstep (se 1 (by rfl) ⟨3336929, by rfl⟩ : syracuseStep 4449239 = 6673859) B6673859
theorem B2966159 : Blo 2081435 2966159 := bstep (se 1 (by rfl) ⟨2224619, by rfl⟩ : syracuseStep 2966159 = 4449239) B4449239
theorem B7909757 : Blo 2081435 7909757 := bstep (se 3 (by rfl) ⟨1483079, by rfl⟩ : syracuseStep 7909757 = 2966159) B2966159
theorem B5273171 : Blo 2081435 5273171 := bstep (se 1 (by rfl) ⟨3954878, by rfl⟩ : syracuseStep 5273171 = 7909757) B7909757
theorem B3515447 : Blo 2081435 3515447 := bstep (se 1 (by rfl) ⟨2636585, by rfl⟩ : syracuseStep 3515447 = 5273171) B5273171
theorem B2343631 : Blo 2081435 2343631 := bstep (se 1 (by rfl) ⟨1757723, by rfl⟩ : syracuseStep 2343631 = 3515447) B3515447
theorem B3124841 : Blo 2081435 3124841 := bstep (se 2 (by rfl) ⟨1171815, by rfl⟩ : syracuseStep 3124841 = 2343631) B2343631
theorem B2083227 : Blo 2081435 2083227 := bstep (se 1 (by rfl) ⟨1562420, by rfl⟩ : syracuseStep 2083227 = 3124841) B3124841
theorem B5418053 : Blo 2081435 5418053 := bbase (se 4 (by rfl) ⟨507942, by rfl⟩ : syracuseStep 5418053 = 1015885) (by norm_num)
theorem B3612035 : Blo 2081435 3612035 := bstep (se 1 (by rfl) ⟨2709026, by rfl⟩ : syracuseStep 3612035 = 5418053) B5418053
theorem B9632093 : Blo 2081435 9632093 := bstep (se 3 (by rfl) ⟨1806017, by rfl⟩ : syracuseStep 9632093 = 3612035) B3612035
theorem B25685581 : Blo 2081435 25685581 := bstep (se 3 (by rfl) ⟨4816046, by rfl⟩ : syracuseStep 25685581 = 9632093) B9632093
theorem B34247441 : Blo 2081435 34247441 := bstep (se 2 (by rfl) ⟨12842790, by rfl⟩ : syracuseStep 34247441 = 25685581) B25685581
theorem B22831627 : Blo 2081435 22831627 := bstep (se 1 (by rfl) ⟨17123720, by rfl⟩ : syracuseStep 22831627 = 34247441) B34247441
theorem B30442169 : Blo 2081435 30442169 := bstep (se 2 (by rfl) ⟨11415813, by rfl⟩ : syracuseStep 30442169 = 22831627) B22831627
theorem B81179117 : Blo 2081435 81179117 := bstep (se 3 (by rfl) ⟨15221084, by rfl⟩ : syracuseStep 81179117 = 30442169) B30442169
theorem B54119411 : Blo 2081435 54119411 := bstep (se 1 (by rfl) ⟨40589558, by rfl⟩ : syracuseStep 54119411 = 81179117) B81179117
theorem B36079607 : Blo 2081435 36079607 := bstep (se 1 (by rfl) ⟨27059705, by rfl⟩ : syracuseStep 36079607 = 54119411) B54119411
theorem B24053071 : Blo 2081435 24053071 := bstep (se 1 (by rfl) ⟨18039803, by rfl⟩ : syracuseStep 24053071 = 36079607) B36079607
theorem B32070761 : Blo 2081435 32070761 := bstep (se 2 (by rfl) ⟨12026535, by rfl⟩ : syracuseStep 32070761 = 24053071) B24053071
theorem B21380507 : Blo 2081435 21380507 := bstep (se 1 (by rfl) ⟨16035380, by rfl⟩ : syracuseStep 21380507 = 32070761) B32070761
theorem B14253671 : Blo 2081435 14253671 := bstep (se 1 (by rfl) ⟨10690253, by rfl⟩ : syracuseStep 14253671 = 21380507) B21380507
theorem B9502447 : Blo 2081435 9502447 := bstep (se 1 (by rfl) ⟨7126835, by rfl⟩ : syracuseStep 9502447 = 14253671) B14253671
theorem B12669929 : Blo 2081435 12669929 := bstep (se 2 (by rfl) ⟨4751223, by rfl⟩ : syracuseStep 12669929 = 9502447) B9502447
theorem B8446619 : Blo 2081435 8446619 := bstep (se 1 (by rfl) ⟨6334964, by rfl⟩ : syracuseStep 8446619 = 12669929) B12669929
theorem B5631079 : Blo 2081435 5631079 := bstep (se 1 (by rfl) ⟨4223309, by rfl⟩ : syracuseStep 5631079 = 8446619) B8446619
theorem B7508105 : Blo 2081435 7508105 := bstep (se 2 (by rfl) ⟨2815539, by rfl⟩ : syracuseStep 7508105 = 5631079) B5631079
theorem B5005403 : Blo 2081435 5005403 := bstep (se 1 (by rfl) ⟨3754052, by rfl⟩ : syracuseStep 5005403 = 7508105) B7508105
theorem B3336935 : Blo 2081435 3336935 := bstep (se 1 (by rfl) ⟨2502701, by rfl⟩ : syracuseStep 3336935 = 5005403) B5005403
theorem B8898493 : Blo 2081435 8898493 := bstep (se 3 (by rfl) ⟨1668467, by rfl⟩ : syracuseStep 8898493 = 3336935) B3336935
theorem B11864657 : Blo 2081435 11864657 := bstep (se 2 (by rfl) ⟨4449246, by rfl⟩ : syracuseStep 11864657 = 8898493) B8898493
theorem B7909771 : Blo 2081435 7909771 := bstep (se 1 (by rfl) ⟨5932328, by rfl⟩ : syracuseStep 7909771 = 11864657) B11864657
theorem B10546361 : Blo 2081435 10546361 := bstep (se 2 (by rfl) ⟨3954885, by rfl⟩ : syracuseStep 10546361 = 7909771) B7909771
theorem B7030907 : Blo 2081435 7030907 := bstep (se 1 (by rfl) ⟨5273180, by rfl⟩ : syracuseStep 7030907 = 10546361) B10546361
theorem B4687271 : Blo 2081435 4687271 := bstep (se 1 (by rfl) ⟨3515453, by rfl⟩ : syracuseStep 4687271 = 7030907) B7030907
theorem B3124847 : Blo 2081435 3124847 := bstep (se 1 (by rfl) ⟨2343635, by rfl⟩ : syracuseStep 3124847 = 4687271) B4687271
theorem B2083231 : Blo 2081435 2083231 := bstep (se 1 (by rfl) ⟨1562423, by rfl⟩ : syracuseStep 2083231 = 3124847) B3124847
theorem B3124853 : Blo 2081435 3124853 := bbase (se 5 (by rfl) ⟨146477, by rfl⟩ : syracuseStep 3124853 = 292955) (by norm_num)
theorem B2083235 : Blo 2081435 2083235 := bstep (se 1 (by rfl) ⟨1562426, by rfl⟩ : syracuseStep 2083235 = 3124853) B3124853
theorem B3954901 : Blo 2081435 3954901 := bbase (se 7 (by rfl) ⟨46346, by rfl⟩ : syracuseStep 3954901 = 92693) (by norm_num)
theorem B5273201 : Blo 2081435 5273201 := bstep (se 2 (by rfl) ⟨1977450, by rfl⟩ : syracuseStep 5273201 = 3954901) B3954901
theorem B3515467 : Blo 2081435 3515467 := bstep (se 1 (by rfl) ⟨2636600, by rfl⟩ : syracuseStep 3515467 = 5273201) B5273201
theorem B4687289 : Blo 2081435 4687289 := bstep (se 2 (by rfl) ⟨1757733, by rfl⟩ : syracuseStep 4687289 = 3515467) B3515467
theorem B3124859 : Blo 2081435 3124859 := bstep (se 1 (by rfl) ⟨2343644, by rfl⟩ : syracuseStep 3124859 = 4687289) B4687289
theorem B2083239 : Blo 2081435 2083239 := bstep (se 1 (by rfl) ⟨1562429, by rfl⟩ : syracuseStep 2083239 = 3124859) B3124859
theorem B2343649 : Blo 2081435 2343649 := bbase (se 2 (by rfl) ⟨878868, by rfl⟩ : syracuseStep 2343649 = 1757737) (by norm_num)
theorem B3124865 : Blo 2081435 3124865 := bstep (se 2 (by rfl) ⟨1171824, by rfl⟩ : syracuseStep 3124865 = 2343649) B2343649
theorem B2083243 : Blo 2081435 2083243 := bstep (se 1 (by rfl) ⟨1562432, by rfl⟩ : syracuseStep 2083243 = 3124865) B3124865
theorem B5273221 : Blo 2081435 5273221 := bbase (se 4 (by rfl) ⟨494364, by rfl⟩ : syracuseStep 5273221 = 988729) (by norm_num)
theorem B7030961 : Blo 2081435 7030961 := bstep (se 2 (by rfl) ⟨2636610, by rfl⟩ : syracuseStep 7030961 = 5273221) B5273221
theorem B4687307 : Blo 2081435 4687307 := bstep (se 1 (by rfl) ⟨3515480, by rfl⟩ : syracuseStep 4687307 = 7030961) B7030961
theorem B3124871 : Blo 2081435 3124871 := bstep (se 1 (by rfl) ⟨2343653, by rfl⟩ : syracuseStep 3124871 = 4687307) B4687307
theorem B2083247 : Blo 2081435 2083247 := bstep (se 1 (by rfl) ⟨1562435, by rfl⟩ : syracuseStep 2083247 = 3124871) B3124871
theorem B3124877 : Blo 2081435 3124877 := bbase (se 3 (by rfl) ⟨585914, by rfl⟩ : syracuseStep 3124877 = 1171829) (by norm_num)
theorem B2083251 : Blo 2081435 2083251 := bstep (se 1 (by rfl) ⟨1562438, by rfl⟩ : syracuseStep 2083251 = 3124877) B3124877
theorem B4687325 : Blo 2081435 4687325 := bbase (se 3 (by rfl) ⟨878873, by rfl⟩ : syracuseStep 4687325 = 1757747) (by norm_num)
theorem B3124883 : Blo 2081435 3124883 := bstep (se 1 (by rfl) ⟨2343662, by rfl⟩ : syracuseStep 3124883 = 4687325) B4687325
theorem B2083255 : Blo 2081435 2083255 := bstep (se 1 (by rfl) ⟨1562441, by rfl⟩ : syracuseStep 2083255 = 3124883) B3124883
theorem B3515501 : Blo 2081435 3515501 := bbase (se 3 (by rfl) ⟨659156, by rfl⟩ : syracuseStep 3515501 = 1318313) (by norm_num)
theorem B2343667 : Blo 2081435 2343667 := bstep (se 1 (by rfl) ⟨1757750, by rfl⟩ : syracuseStep 2343667 = 3515501) B3515501
theorem B3124889 : Blo 2081435 3124889 := bstep (se 2 (by rfl) ⟨1171833, by rfl⟩ : syracuseStep 3124889 = 2343667) B2343667
theorem B2083259 : Blo 2081435 2083259 := bstep (se 1 (by rfl) ⟨1562444, by rfl⟩ : syracuseStep 2083259 = 3124889) B3124889
theorem B6421493 : Blo 2081435 6421493 := bbase (se 5 (by rfl) ⟨301007, by rfl⟩ : syracuseStep 6421493 = 602015) (by norm_num)
theorem B4280995 : Blo 2081435 4280995 := bstep (se 1 (by rfl) ⟨3210746, by rfl⟩ : syracuseStep 4280995 = 6421493) B6421493
theorem B22831973 : Blo 2081435 22831973 := bstep (se 4 (by rfl) ⟨2140497, by rfl⟩ : syracuseStep 22831973 = 4280995) B4280995
theorem B15221315 : Blo 2081435 15221315 := bstep (se 1 (by rfl) ⟨11415986, by rfl⟩ : syracuseStep 15221315 = 22831973) B22831973
theorem B40590173 : Blo 2081435 40590173 := bstep (se 3 (by rfl) ⟨7610657, by rfl⟩ : syracuseStep 40590173 = 15221315) B15221315
theorem B108240461 : Blo 2081435 108240461 := bstep (se 3 (by rfl) ⟨20295086, by rfl⟩ : syracuseStep 108240461 = 40590173) B40590173
theorem B72160307 : Blo 2081435 72160307 := bstep (se 1 (by rfl) ⟨54120230, by rfl⟩ : syracuseStep 72160307 = 108240461) B108240461
theorem B48106871 : Blo 2081435 48106871 := bstep (se 1 (by rfl) ⟨36080153, by rfl⟩ : syracuseStep 48106871 = 72160307) B72160307
theorem B32071247 : Blo 2081435 32071247 := bstep (se 1 (by rfl) ⟨24053435, by rfl⟩ : syracuseStep 32071247 = 48106871) B48106871
theorem B21380831 : Blo 2081435 21380831 := bstep (se 1 (by rfl) ⟨16035623, by rfl⟩ : syracuseStep 21380831 = 32071247) B32071247
theorem B14253887 : Blo 2081435 14253887 := bstep (se 1 (by rfl) ⟨10690415, by rfl⟩ : syracuseStep 14253887 = 21380831) B21380831
theorem B9502591 : Blo 2081435 9502591 := bstep (se 1 (by rfl) ⟨7126943, by rfl⟩ : syracuseStep 9502591 = 14253887) B14253887
theorem B12670121 : Blo 2081435 12670121 := bstep (se 2 (by rfl) ⟨4751295, by rfl⟩ : syracuseStep 12670121 = 9502591) B9502591
theorem B8446747 : Blo 2081435 8446747 := bstep (se 1 (by rfl) ⟨6335060, by rfl⟩ : syracuseStep 8446747 = 12670121) B12670121
theorem B11262329 : Blo 2081435 11262329 := bstep (se 2 (by rfl) ⟨4223373, by rfl⟩ : syracuseStep 11262329 = 8446747) B8446747
theorem B7508219 : Blo 2081435 7508219 := bstep (se 1 (by rfl) ⟨5631164, by rfl⟩ : syracuseStep 7508219 = 11262329) B11262329
theorem B20021917 : Blo 2081435 20021917 := bstep (se 3 (by rfl) ⟨3754109, by rfl⟩ : syracuseStep 20021917 = 7508219) B7508219
theorem B26695889 : Blo 2081435 26695889 := bstep (se 2 (by rfl) ⟨10010958, by rfl⟩ : syracuseStep 26695889 = 20021917) B20021917
theorem B17797259 : Blo 2081435 17797259 := bstep (se 1 (by rfl) ⟨13347944, by rfl⟩ : syracuseStep 17797259 = 26695889) B26695889
theorem B11864839 : Blo 2081435 11864839 := bstep (se 1 (by rfl) ⟨8898629, by rfl⟩ : syracuseStep 11864839 = 17797259) B17797259
theorem B15819785 : Blo 2081435 15819785 := bstep (se 2 (by rfl) ⟨5932419, by rfl⟩ : syracuseStep 15819785 = 11864839) B11864839
theorem B10546523 : Blo 2081435 10546523 := bstep (se 1 (by rfl) ⟨7909892, by rfl⟩ : syracuseStep 10546523 = 15819785) B15819785
theorem B7031015 : Blo 2081435 7031015 := bstep (se 1 (by rfl) ⟨5273261, by rfl⟩ : syracuseStep 7031015 = 10546523) B10546523
theorem B4687343 : Blo 2081435 4687343 := bstep (se 1 (by rfl) ⟨3515507, by rfl⟩ : syracuseStep 4687343 = 7031015) B7031015
theorem B3124895 : Blo 2081435 3124895 := bstep (se 1 (by rfl) ⟨2343671, by rfl⟩ : syracuseStep 3124895 = 4687343) B4687343
theorem B2083263 : Blo 2081435 2083263 := bstep (se 1 (by rfl) ⟨1562447, by rfl⟩ : syracuseStep 2083263 = 3124895) B3124895
theorem B3124901 : Blo 2081435 3124901 := bbase (se 4 (by rfl) ⟨292959, by rfl⟩ : syracuseStep 3124901 = 585919) (by norm_num)
theorem B2083267 : Blo 2081435 2083267 := bstep (se 1 (by rfl) ⟨1562450, by rfl⟩ : syracuseStep 2083267 = 3124901) B3124901
theorem B2636641 : Blo 2081435 2636641 := bbase (se 2 (by rfl) ⟨988740, by rfl⟩ : syracuseStep 2636641 = 1977481) (by norm_num)
theorem B3515521 : Blo 2081435 3515521 := bstep (se 2 (by rfl) ⟨1318320, by rfl⟩ : syracuseStep 3515521 = 2636641) B2636641
theorem B4687361 : Blo 2081435 4687361 := bstep (se 2 (by rfl) ⟨1757760, by rfl⟩ : syracuseStep 4687361 = 3515521) B3515521
theorem B3124907 : Blo 2081435 3124907 := bstep (se 1 (by rfl) ⟨2343680, by rfl⟩ : syracuseStep 3124907 = 4687361) B4687361
theorem B2083271 : Blo 2081435 2083271 := bstep (se 1 (by rfl) ⟨1562453, by rfl⟩ : syracuseStep 2083271 = 3124907) B3124907
theorem B2343685 : Blo 2081435 2343685 := bbase (se 4 (by rfl) ⟨219720, by rfl⟩ : syracuseStep 2343685 = 439441) (by norm_num)
theorem B3124913 : Blo 2081435 3124913 := bstep (se 2 (by rfl) ⟨1171842, by rfl⟩ : syracuseStep 3124913 = 2343685) B2343685
theorem B2083275 : Blo 2081435 2083275 := bstep (se 1 (by rfl) ⟨1562456, by rfl⟩ : syracuseStep 2083275 = 3124913) B3124913
theorem B3337013 : Blo 2081435 3337013 := bbase (se 5 (by rfl) ⟨156422, by rfl⟩ : syracuseStep 3337013 = 312845) (by norm_num)
theorem B2224675 : Blo 2081435 2224675 := bstep (se 1 (by rfl) ⟨1668506, by rfl⟩ : syracuseStep 2224675 = 3337013) B3337013
theorem B2966233 : Blo 2081435 2966233 := bstep (se 2 (by rfl) ⟨1112337, by rfl⟩ : syracuseStep 2966233 = 2224675) B2224675
theorem B3954977 : Blo 2081435 3954977 := bstep (se 2 (by rfl) ⟨1483116, by rfl⟩ : syracuseStep 3954977 = 2966233) B2966233
theorem B2636651 : Blo 2081435 2636651 := bstep (se 1 (by rfl) ⟨1977488, by rfl⟩ : syracuseStep 2636651 = 3954977) B3954977
theorem B7031069 : Blo 2081435 7031069 := bstep (se 3 (by rfl) ⟨1318325, by rfl⟩ : syracuseStep 7031069 = 2636651) B2636651
theorem B4687379 : Blo 2081435 4687379 := bstep (se 1 (by rfl) ⟨3515534, by rfl⟩ : syracuseStep 4687379 = 7031069) B7031069
theorem B3124919 : Blo 2081435 3124919 := bstep (se 1 (by rfl) ⟨2343689, by rfl⟩ : syracuseStep 3124919 = 4687379) B4687379
theorem B2083279 : Blo 2081435 2083279 := bstep (se 1 (by rfl) ⟨1562459, by rfl⟩ : syracuseStep 2083279 = 3124919) B3124919
theorem B3124925 : Blo 2081435 3124925 := bbase (se 3 (by rfl) ⟨585923, by rfl⟩ : syracuseStep 3124925 = 1171847) (by norm_num)
theorem B2083283 : Blo 2081435 2083283 := bstep (se 1 (by rfl) ⟨1562462, by rfl⟩ : syracuseStep 2083283 = 3124925) B3124925
theorem B4687397 : Blo 2081435 4687397 := bbase (se 4 (by rfl) ⟨439443, by rfl⟩ : syracuseStep 4687397 = 878887) (by norm_num)
theorem B3124931 : Blo 2081435 3124931 := bstep (se 1 (by rfl) ⟨2343698, by rfl⟩ : syracuseStep 3124931 = 4687397) B4687397
theorem B2083287 : Blo 2081435 2083287 := bstep (se 1 (by rfl) ⟨1562465, by rfl⟩ : syracuseStep 2083287 = 3124931) B3124931
theorem B5273333 : Blo 2081435 5273333 := bbase (se 5 (by rfl) ⟨247187, by rfl⟩ : syracuseStep 5273333 = 494375) (by norm_num)
theorem B3515555 : Blo 2081435 3515555 := bstep (se 1 (by rfl) ⟨2636666, by rfl⟩ : syracuseStep 3515555 = 5273333) B5273333
theorem B2343703 : Blo 2081435 2343703 := bstep (se 1 (by rfl) ⟨1757777, by rfl⟩ : syracuseStep 2343703 = 3515555) B3515555
theorem B3124937 : Blo 2081435 3124937 := bstep (se 2 (by rfl) ⟨1171851, by rfl⟩ : syracuseStep 3124937 = 2343703) B2343703
theorem B2083291 : Blo 2081435 2083291 := bstep (se 1 (by rfl) ⟨1562468, by rfl⟩ : syracuseStep 2083291 = 3124937) B3124937
theorem B2672645 : Blo 2081435 2672645 := bbase (se 4 (by rfl) ⟨250560, by rfl⟩ : syracuseStep 2672645 = 501121) (by norm_num)
theorem B28508213 : Blo 2081435 28508213 := bstep (se 5 (by rfl) ⟨1336322, by rfl⟩ : syracuseStep 28508213 = 2672645) B2672645
theorem B19005475 : Blo 2081435 19005475 := bstep (se 1 (by rfl) ⟨14254106, by rfl⟩ : syracuseStep 19005475 = 28508213) B28508213
theorem B25340633 : Blo 2081435 25340633 := bstep (se 2 (by rfl) ⟨9502737, by rfl⟩ : syracuseStep 25340633 = 19005475) B19005475
theorem B16893755 : Blo 2081435 16893755 := bstep (se 1 (by rfl) ⟨12670316, by rfl⟩ : syracuseStep 16893755 = 25340633) B25340633
theorem B11262503 : Blo 2081435 11262503 := bstep (se 1 (by rfl) ⟨8446877, by rfl⟩ : syracuseStep 11262503 = 16893755) B16893755
theorem B30033341 : Blo 2081435 30033341 := bstep (se 3 (by rfl) ⟨5631251, by rfl⟩ : syracuseStep 30033341 = 11262503) B11262503
theorem B20022227 : Blo 2081435 20022227 := bstep (se 1 (by rfl) ⟨15016670, by rfl⟩ : syracuseStep 20022227 = 30033341) B30033341
theorem B13348151 : Blo 2081435 13348151 := bstep (se 1 (by rfl) ⟨10011113, by rfl⟩ : syracuseStep 13348151 = 20022227) B20022227
theorem B8898767 : Blo 2081435 8898767 := bstep (se 1 (by rfl) ⟨6674075, by rfl⟩ : syracuseStep 8898767 = 13348151) B13348151
theorem B5932511 : Blo 2081435 5932511 := bstep (se 1 (by rfl) ⟨4449383, by rfl⟩ : syracuseStep 5932511 = 8898767) B8898767
theorem B3955007 : Blo 2081435 3955007 := bstep (se 1 (by rfl) ⟨2966255, by rfl⟩ : syracuseStep 3955007 = 5932511) B5932511
theorem B10546685 : Blo 2081435 10546685 := bstep (se 3 (by rfl) ⟨1977503, by rfl⟩ : syracuseStep 10546685 = 3955007) B3955007
theorem B7031123 : Blo 2081435 7031123 := bstep (se 1 (by rfl) ⟨5273342, by rfl⟩ : syracuseStep 7031123 = 10546685) B10546685
theorem B4687415 : Blo 2081435 4687415 := bstep (se 1 (by rfl) ⟨3515561, by rfl⟩ : syracuseStep 4687415 = 7031123) B7031123
theorem B3124943 : Blo 2081435 3124943 := bstep (se 1 (by rfl) ⟨2343707, by rfl⟩ : syracuseStep 3124943 = 4687415) B4687415
theorem B2083295 : Blo 2081435 2083295 := bstep (se 1 (by rfl) ⟨1562471, by rfl⟩ : syracuseStep 2083295 = 3124943) B3124943
theorem B3124949 : Blo 2081435 3124949 := bbase (se 7 (by rfl) ⟨36620, by rfl⟩ : syracuseStep 3124949 = 73241) (by norm_num)
theorem B2083299 : Blo 2081435 2083299 := bstep (se 1 (by rfl) ⟨1562474, by rfl⟩ : syracuseStep 2083299 = 3124949) B3124949
theorem B4751389 : Blo 2081435 4751389 := bbase (se 3 (by rfl) ⟨890885, by rfl⟩ : syracuseStep 4751389 = 1781771) (by norm_num)
theorem B6335185 : Blo 2081435 6335185 := bstep (se 2 (by rfl) ⟨2375694, by rfl⟩ : syracuseStep 6335185 = 4751389) B4751389
theorem B8446913 : Blo 2081435 8446913 := bstep (se 2 (by rfl) ⟨3167592, by rfl⟩ : syracuseStep 8446913 = 6335185) B6335185
theorem B5631275 : Blo 2081435 5631275 := bstep (se 1 (by rfl) ⟨4223456, by rfl⟩ : syracuseStep 5631275 = 8446913) B8446913
theorem B3754183 : Blo 2081435 3754183 := bstep (se 1 (by rfl) ⟨2815637, by rfl⟩ : syracuseStep 3754183 = 5631275) B5631275
theorem B5005577 : Blo 2081435 5005577 := bstep (se 2 (by rfl) ⟨1877091, by rfl⟩ : syracuseStep 5005577 = 3754183) B3754183
theorem B3337051 : Blo 2081435 3337051 := bstep (se 1 (by rfl) ⟨2502788, by rfl⟩ : syracuseStep 3337051 = 5005577) B5005577
theorem B4449401 : Blo 2081435 4449401 := bstep (se 2 (by rfl) ⟨1668525, by rfl⟩ : syracuseStep 4449401 = 3337051) B3337051
theorem B2966267 : Blo 2081435 2966267 := bstep (se 1 (by rfl) ⟨2224700, by rfl⟩ : syracuseStep 2966267 = 4449401) B4449401
theorem B7910045 : Blo 2081435 7910045 := bstep (se 3 (by rfl) ⟨1483133, by rfl⟩ : syracuseStep 7910045 = 2966267) B2966267
theorem B5273363 : Blo 2081435 5273363 := bstep (se 1 (by rfl) ⟨3955022, by rfl⟩ : syracuseStep 5273363 = 7910045) B7910045
theorem B3515575 : Blo 2081435 3515575 := bstep (se 1 (by rfl) ⟨2636681, by rfl⟩ : syracuseStep 3515575 = 5273363) B5273363
theorem B4687433 : Blo 2081435 4687433 := bstep (se 2 (by rfl) ⟨1757787, by rfl⟩ : syracuseStep 4687433 = 3515575) B3515575
theorem B3124955 : Blo 2081435 3124955 := bstep (se 1 (by rfl) ⟨2343716, by rfl⟩ : syracuseStep 3124955 = 4687433) B4687433
theorem B2083303 : Blo 2081435 2083303 := bstep (se 1 (by rfl) ⟨1562477, by rfl⟩ : syracuseStep 2083303 = 3124955) B3124955
theorem B2343721 : Blo 2081435 2343721 := bbase (se 2 (by rfl) ⟨878895, by rfl⟩ : syracuseStep 2343721 = 1757791) (by norm_num)
theorem B3124961 : Blo 2081435 3124961 := bstep (se 2 (by rfl) ⟨1171860, by rfl⟩ : syracuseStep 3124961 = 2343721) B2343721
theorem B2083307 : Blo 2081435 2083307 := bstep (se 1 (by rfl) ⟨1562480, by rfl⟩ : syracuseStep 2083307 = 3124961) B3124961
theorem B8238277 : Blo 2081435 8238277 := bbase (se 4 (by rfl) ⟨772338, by rfl⟩ : syracuseStep 8238277 = 1544677) (by norm_num)
theorem B43937477 : Blo 2081435 43937477 := bstep (se 4 (by rfl) ⟨4119138, by rfl⟩ : syracuseStep 43937477 = 8238277) B8238277
theorem B29291651 : Blo 2081435 29291651 := bstep (se 1 (by rfl) ⟨21968738, by rfl⟩ : syracuseStep 29291651 = 43937477) B43937477
theorem B19527767 : Blo 2081435 19527767 := bstep (se 1 (by rfl) ⟨14645825, by rfl⟩ : syracuseStep 19527767 = 29291651) B29291651
theorem B13018511 : Blo 2081435 13018511 := bstep (se 1 (by rfl) ⟨9763883, by rfl⟩ : syracuseStep 13018511 = 19527767) B19527767
theorem B8679007 : Blo 2081435 8679007 := bstep (se 1 (by rfl) ⟨6509255, by rfl⟩ : syracuseStep 8679007 = 13018511) B13018511
theorem B46288037 : Blo 2081435 46288037 := bstep (se 4 (by rfl) ⟨4339503, by rfl⟩ : syracuseStep 46288037 = 8679007) B8679007
theorem B30858691 : Blo 2081435 30858691 := bstep (se 1 (by rfl) ⟨23144018, by rfl⟩ : syracuseStep 30858691 = 46288037) B46288037
theorem B41144921 : Blo 2081435 41144921 := bstep (se 2 (by rfl) ⟨15429345, by rfl⟩ : syracuseStep 41144921 = 30858691) B30858691
theorem B27429947 : Blo 2081435 27429947 := bstep (se 1 (by rfl) ⟨20572460, by rfl⟩ : syracuseStep 27429947 = 41144921) B41144921
theorem B18286631 : Blo 2081435 18286631 := bstep (se 1 (by rfl) ⟨13714973, by rfl⟩ : syracuseStep 18286631 = 27429947) B27429947
theorem B12191087 : Blo 2081435 12191087 := bstep (se 1 (by rfl) ⟨9143315, by rfl⟩ : syracuseStep 12191087 = 18286631) B18286631
theorem B8127391 : Blo 2081435 8127391 := bstep (se 1 (by rfl) ⟨6095543, by rfl⟩ : syracuseStep 8127391 = 12191087) B12191087
theorem B10836521 : Blo 2081435 10836521 := bstep (se 2 (by rfl) ⟨4063695, by rfl⟩ : syracuseStep 10836521 = 8127391) B8127391
theorem B7224347 : Blo 2081435 7224347 := bstep (se 1 (by rfl) ⟨5418260, by rfl⟩ : syracuseStep 7224347 = 10836521) B10836521
theorem B19264925 : Blo 2081435 19264925 := bstep (se 3 (by rfl) ⟨3612173, by rfl⟩ : syracuseStep 19264925 = 7224347) B7224347
theorem B12843283 : Blo 2081435 12843283 := bstep (se 1 (by rfl) ⟨9632462, by rfl⟩ : syracuseStep 12843283 = 19264925) B19264925
theorem B17124377 : Blo 2081435 17124377 := bstep (se 2 (by rfl) ⟨6421641, by rfl⟩ : syracuseStep 17124377 = 12843283) B12843283
theorem B45665005 : Blo 2081435 45665005 := bstep (se 3 (by rfl) ⟨8562188, by rfl⟩ : syracuseStep 45665005 = 17124377) B17124377
theorem B60886673 : Blo 2081435 60886673 := bstep (se 2 (by rfl) ⟨22832502, by rfl⟩ : syracuseStep 60886673 = 45665005) B45665005
theorem B40591115 : Blo 2081435 40591115 := bstep (se 1 (by rfl) ⟨30443336, by rfl⟩ : syracuseStep 40591115 = 60886673) B60886673
theorem B27060743 : Blo 2081435 27060743 := bstep (se 1 (by rfl) ⟨20295557, by rfl⟩ : syracuseStep 27060743 = 40591115) B40591115
theorem B18040495 : Blo 2081435 18040495 := bstep (se 1 (by rfl) ⟨13530371, by rfl⟩ : syracuseStep 18040495 = 27060743) B27060743
theorem B24053993 : Blo 2081435 24053993 := bstep (se 2 (by rfl) ⟨9020247, by rfl⟩ : syracuseStep 24053993 = 18040495) B18040495
theorem B16035995 : Blo 2081435 16035995 := bstep (se 1 (by rfl) ⟨12026996, by rfl⟩ : syracuseStep 16035995 = 24053993) B24053993
theorem B42762653 : Blo 2081435 42762653 := bstep (se 3 (by rfl) ⟨8017997, by rfl⟩ : syracuseStep 42762653 = 16035995) B16035995
theorem B28508435 : Blo 2081435 28508435 := bstep (se 1 (by rfl) ⟨21381326, by rfl⟩ : syracuseStep 28508435 = 42762653) B42762653
theorem B19005623 : Blo 2081435 19005623 := bstep (se 1 (by rfl) ⟨14254217, by rfl⟩ : syracuseStep 19005623 = 28508435) B28508435
theorem B12670415 : Blo 2081435 12670415 := bstep (se 1 (by rfl) ⟨9502811, by rfl⟩ : syracuseStep 12670415 = 19005623) B19005623
theorem B8446943 : Blo 2081435 8446943 := bstep (se 1 (by rfl) ⟨6335207, by rfl⟩ : syracuseStep 8446943 = 12670415) B12670415
theorem B5631295 : Blo 2081435 5631295 := bstep (se 1 (by rfl) ⟨4223471, by rfl⟩ : syracuseStep 5631295 = 8446943) B8446943
theorem B7508393 : Blo 2081435 7508393 := bstep (se 2 (by rfl) ⟨2815647, by rfl⟩ : syracuseStep 7508393 = 5631295) B5631295
theorem B5005595 : Blo 2081435 5005595 := bstep (se 1 (by rfl) ⟨3754196, by rfl⟩ : syracuseStep 5005595 = 7508393) B7508393
theorem B13348253 : Blo 2081435 13348253 := bstep (se 3 (by rfl) ⟨2502797, by rfl⟩ : syracuseStep 13348253 = 5005595) B5005595
theorem B8898835 : Blo 2081435 8898835 := bstep (se 1 (by rfl) ⟨6674126, by rfl⟩ : syracuseStep 8898835 = 13348253) B13348253
theorem B11865113 : Blo 2081435 11865113 := bstep (se 2 (by rfl) ⟨4449417, by rfl⟩ : syracuseStep 11865113 = 8898835) B8898835
theorem B7910075 : Blo 2081435 7910075 := bstep (se 1 (by rfl) ⟨5932556, by rfl⟩ : syracuseStep 7910075 = 11865113) B11865113
theorem B5273383 : Blo 2081435 5273383 := bstep (se 1 (by rfl) ⟨3955037, by rfl⟩ : syracuseStep 5273383 = 7910075) B7910075
theorem B7031177 : Blo 2081435 7031177 := bstep (se 2 (by rfl) ⟨2636691, by rfl⟩ : syracuseStep 7031177 = 5273383) B5273383
theorem B4687451 : Blo 2081435 4687451 := bstep (se 1 (by rfl) ⟨3515588, by rfl⟩ : syracuseStep 4687451 = 7031177) B7031177
theorem B3124967 : Blo 2081435 3124967 := bstep (se 1 (by rfl) ⟨2343725, by rfl⟩ : syracuseStep 3124967 = 4687451) B4687451
theorem B2083311 : Blo 2081435 2083311 := bstep (se 1 (by rfl) ⟨1562483, by rfl⟩ : syracuseStep 2083311 = 3124967) B3124967
theorem B3124973 : Blo 2081435 3124973 := bbase (se 3 (by rfl) ⟨585932, by rfl⟩ : syracuseStep 3124973 = 1171865) (by norm_num)
theorem B2083315 : Blo 2081435 2083315 := bstep (se 1 (by rfl) ⟨1562486, by rfl⟩ : syracuseStep 2083315 = 3124973) B3124973
theorem B4687469 : Blo 2081435 4687469 := bbase (se 3 (by rfl) ⟨878900, by rfl⟩ : syracuseStep 4687469 = 1757801) (by norm_num)
theorem B3124979 : Blo 2081435 3124979 := bstep (se 1 (by rfl) ⟨2343734, by rfl⟩ : syracuseStep 3124979 = 4687469) B4687469
theorem B2083319 : Blo 2081435 2083319 := bstep (se 1 (by rfl) ⟨1562489, by rfl⟩ : syracuseStep 2083319 = 3124979) B3124979
theorem B3955061 : Blo 2081435 3955061 := bbase (se 5 (by rfl) ⟨185393, by rfl⟩ : syracuseStep 3955061 = 370787) (by norm_num)
theorem B2636707 : Blo 2081435 2636707 := bstep (se 1 (by rfl) ⟨1977530, by rfl⟩ : syracuseStep 2636707 = 3955061) B3955061
theorem B3515609 : Blo 2081435 3515609 := bstep (se 2 (by rfl) ⟨1318353, by rfl⟩ : syracuseStep 3515609 = 2636707) B2636707
theorem B2343739 : Blo 2081435 2343739 := bstep (se 1 (by rfl) ⟨1757804, by rfl⟩ : syracuseStep 2343739 = 3515609) B3515609
theorem B3124985 : Blo 2081435 3124985 := bstep (se 2 (by rfl) ⟨1171869, by rfl⟩ : syracuseStep 3124985 = 2343739) B2343739
theorem B2083323 : Blo 2081435 2083323 := bstep (se 1 (by rfl) ⟨1562492, by rfl⟩ : syracuseStep 2083323 = 3124985) B3124985
theorem B3210845 : Blo 2081435 3210845 := bbase (se 3 (by rfl) ⟨602033, by rfl⟩ : syracuseStep 3210845 = 1204067) (by norm_num)
theorem B34249013 : Blo 2081435 34249013 := bstep (se 5 (by rfl) ⟨1605422, by rfl⟩ : syracuseStep 34249013 = 3210845) B3210845
theorem B22832675 : Blo 2081435 22832675 := bstep (se 1 (by rfl) ⟨17124506, by rfl⟩ : syracuseStep 22832675 = 34249013) B34249013
theorem B15221783 : Blo 2081435 15221783 := bstep (se 1 (by rfl) ⟨11416337, by rfl⟩ : syracuseStep 15221783 = 22832675) B22832675
theorem B10147855 : Blo 2081435 10147855 := bstep (se 1 (by rfl) ⟨7610891, by rfl⟩ : syracuseStep 10147855 = 15221783) B15221783
theorem B13530473 : Blo 2081435 13530473 := bstep (se 2 (by rfl) ⟨5073927, by rfl⟩ : syracuseStep 13530473 = 10147855) B10147855
theorem B9020315 : Blo 2081435 9020315 := bstep (se 1 (by rfl) ⟨6765236, by rfl⟩ : syracuseStep 9020315 = 13530473) B13530473
theorem B6013543 : Blo 2081435 6013543 := bstep (se 1 (by rfl) ⟨4510157, by rfl⟩ : syracuseStep 6013543 = 9020315) B9020315
theorem B8018057 : Blo 2081435 8018057 := bstep (se 2 (by rfl) ⟨3006771, by rfl⟩ : syracuseStep 8018057 = 6013543) B6013543
theorem B5345371 : Blo 2081435 5345371 := bstep (se 1 (by rfl) ⟨4009028, by rfl⟩ : syracuseStep 5345371 = 8018057) B8018057
theorem B28508645 : Blo 2081435 28508645 := bstep (se 4 (by rfl) ⟨2672685, by rfl⟩ : syracuseStep 28508645 = 5345371) B5345371
theorem B19005763 : Blo 2081435 19005763 := bstep (se 1 (by rfl) ⟨14254322, by rfl⟩ : syracuseStep 19005763 = 28508645) B28508645
theorem B25341017 : Blo 2081435 25341017 := bstep (se 2 (by rfl) ⟨9502881, by rfl⟩ : syracuseStep 25341017 = 19005763) B19005763
theorem B67576045 : Blo 2081435 67576045 := bstep (se 3 (by rfl) ⟨12670508, by rfl⟩ : syracuseStep 67576045 = 25341017) B25341017
theorem B90101393 : Blo 2081435 90101393 := bstep (se 2 (by rfl) ⟨33788022, by rfl⟩ : syracuseStep 90101393 = 67576045) B67576045
theorem B60067595 : Blo 2081435 60067595 := bstep (se 1 (by rfl) ⟨45050696, by rfl⟩ : syracuseStep 60067595 = 90101393) B90101393
theorem B40045063 : Blo 2081435 40045063 := bstep (se 1 (by rfl) ⟨30033797, by rfl⟩ : syracuseStep 40045063 = 60067595) B60067595
theorem B53393417 : Blo 2081435 53393417 := bstep (se 2 (by rfl) ⟨20022531, by rfl⟩ : syracuseStep 53393417 = 40045063) B40045063
theorem B35595611 : Blo 2081435 35595611 := bstep (se 1 (by rfl) ⟨26696708, by rfl⟩ : syracuseStep 35595611 = 53393417) B53393417
theorem B23730407 : Blo 2081435 23730407 := bstep (se 1 (by rfl) ⟨17797805, by rfl⟩ : syracuseStep 23730407 = 35595611) B35595611
theorem B15820271 : Blo 2081435 15820271 := bstep (se 1 (by rfl) ⟨11865203, by rfl⟩ : syracuseStep 15820271 = 23730407) B23730407
theorem B10546847 : Blo 2081435 10546847 := bstep (se 1 (by rfl) ⟨7910135, by rfl⟩ : syracuseStep 10546847 = 15820271) B15820271
theorem B7031231 : Blo 2081435 7031231 := bstep (se 1 (by rfl) ⟨5273423, by rfl⟩ : syracuseStep 7031231 = 10546847) B10546847
theorem B4687487 : Blo 2081435 4687487 := bstep (se 1 (by rfl) ⟨3515615, by rfl⟩ : syracuseStep 4687487 = 7031231) B7031231
theorem B3124991 : Blo 2081435 3124991 := bstep (se 1 (by rfl) ⟨2343743, by rfl⟩ : syracuseStep 3124991 = 4687487) B4687487
theorem B2083327 : Blo 2081435 2083327 := bstep (se 1 (by rfl) ⟨1562495, by rfl⟩ : syracuseStep 2083327 = 3124991) B3124991
theorem B3124997 : Blo 2081435 3124997 := bbase (se 4 (by rfl) ⟨292968, by rfl⟩ : syracuseStep 3124997 = 585937) (by norm_num)
theorem B2083331 : Blo 2081435 2083331 := bstep (se 1 (by rfl) ⟨1562498, by rfl⟩ : syracuseStep 2083331 = 3124997) B3124997
theorem B3515629 : Blo 2081435 3515629 := bbase (se 3 (by rfl) ⟨659180, by rfl⟩ : syracuseStep 3515629 = 1318361) (by norm_num)
theorem B4687505 : Blo 2081435 4687505 := bstep (se 2 (by rfl) ⟨1757814, by rfl⟩ : syracuseStep 4687505 = 3515629) B3515629
theorem B3125003 : Blo 2081435 3125003 := bstep (se 1 (by rfl) ⟨2343752, by rfl⟩ : syracuseStep 3125003 = 4687505) B4687505
theorem B2083335 : Blo 2081435 2083335 := bstep (se 1 (by rfl) ⟨1562501, by rfl⟩ : syracuseStep 2083335 = 3125003) B3125003
theorem B2343757 : Blo 2081435 2343757 := bbase (se 3 (by rfl) ⟨439454, by rfl⟩ : syracuseStep 2343757 = 878909) (by norm_num)
theorem B3125009 : Blo 2081435 3125009 := bstep (se 2 (by rfl) ⟨1171878, by rfl⟩ : syracuseStep 3125009 = 2343757) B2343757
theorem B2083339 : Blo 2081435 2083339 := bstep (se 1 (by rfl) ⟨1562504, by rfl⟩ : syracuseStep 2083339 = 3125009) B3125009
theorem B7031285 : Blo 2081435 7031285 := bbase (se 5 (by rfl) ⟨329591, by rfl⟩ : syracuseStep 7031285 = 659183) (by norm_num)
theorem B4687523 : Blo 2081435 4687523 := bstep (se 1 (by rfl) ⟨3515642, by rfl⟩ : syracuseStep 4687523 = 7031285) B7031285
theorem B3125015 : Blo 2081435 3125015 := bstep (se 1 (by rfl) ⟨2343761, by rfl⟩ : syracuseStep 3125015 = 4687523) B4687523
theorem B2083343 : Blo 2081435 2083343 := bstep (se 1 (by rfl) ⟨1562507, by rfl⟩ : syracuseStep 2083343 = 3125015) B3125015
theorem B3125021 : Blo 2081435 3125021 := bbase (se 3 (by rfl) ⟨585941, by rfl⟩ : syracuseStep 3125021 = 1171883) (by norm_num)
theorem B2083347 : Blo 2081435 2083347 := bstep (se 1 (by rfl) ⟨1562510, by rfl⟩ : syracuseStep 2083347 = 3125021) B3125021
theorem B4687541 : Blo 2081435 4687541 := bbase (se 5 (by rfl) ⟨219728, by rfl⟩ : syracuseStep 4687541 = 439457) (by norm_num)
theorem B3125027 : Blo 2081435 3125027 := bstep (se 1 (by rfl) ⟨2343770, by rfl⟩ : syracuseStep 3125027 = 4687541) B4687541
theorem B2083351 : Blo 2081435 2083351 := bstep (se 1 (by rfl) ⟨1562513, by rfl⟩ : syracuseStep 2083351 = 3125027) B3125027
theorem B11865365 : Blo 2081435 11865365 := bbase (se 6 (by rfl) ⟨278094, by rfl⟩ : syracuseStep 11865365 = 556189) (by norm_num)
theorem B7910243 : Blo 2081435 7910243 := bstep (se 1 (by rfl) ⟨5932682, by rfl⟩ : syracuseStep 7910243 = 11865365) B11865365
theorem B5273495 : Blo 2081435 5273495 := bstep (se 1 (by rfl) ⟨3955121, by rfl⟩ : syracuseStep 5273495 = 7910243) B7910243
theorem B3515663 : Blo 2081435 3515663 := bstep (se 1 (by rfl) ⟨2636747, by rfl⟩ : syracuseStep 3515663 = 5273495) B5273495
theorem B2343775 : Blo 2081435 2343775 := bstep (se 1 (by rfl) ⟨1757831, by rfl⟩ : syracuseStep 2343775 = 3515663) B3515663
theorem B3125033 : Blo 2081435 3125033 := bstep (se 2 (by rfl) ⟨1171887, by rfl⟩ : syracuseStep 3125033 = 2343775) B2343775
theorem B2083355 : Blo 2081435 2083355 := bstep (se 1 (by rfl) ⟨1562516, by rfl⟩ : syracuseStep 2083355 = 3125033) B3125033
theorem B5932693 : Blo 2081435 5932693 := bbase (se 6 (by rfl) ⟨139047, by rfl⟩ : syracuseStep 5932693 = 278095) (by norm_num)
theorem B7910257 : Blo 2081435 7910257 := bstep (se 2 (by rfl) ⟨2966346, by rfl⟩ : syracuseStep 7910257 = 5932693) B5932693
theorem B10547009 : Blo 2081435 10547009 := bstep (se 2 (by rfl) ⟨3955128, by rfl⟩ : syracuseStep 10547009 = 7910257) B7910257
theorem B7031339 : Blo 2081435 7031339 := bstep (se 1 (by rfl) ⟨5273504, by rfl⟩ : syracuseStep 7031339 = 10547009) B10547009
theorem B4687559 : Blo 2081435 4687559 := bstep (se 1 (by rfl) ⟨3515669, by rfl⟩ : syracuseStep 4687559 = 7031339) B7031339
theorem B3125039 : Blo 2081435 3125039 := bstep (se 1 (by rfl) ⟨2343779, by rfl⟩ : syracuseStep 3125039 = 4687559) B4687559
theorem B2083359 : Blo 2081435 2083359 := bstep (se 1 (by rfl) ⟨1562519, by rfl⟩ : syracuseStep 2083359 = 3125039) B3125039
theorem B3125045 : Blo 2081435 3125045 := bbase (se 5 (by rfl) ⟨146486, by rfl⟩ : syracuseStep 3125045 = 292973) (by norm_num)
theorem B2083363 : Blo 2081435 2083363 := bstep (se 1 (by rfl) ⟨1562522, by rfl⟩ : syracuseStep 2083363 = 3125045) B3125045
theorem B5273525 : Blo 2081435 5273525 := bbase (se 5 (by rfl) ⟨247196, by rfl⟩ : syracuseStep 5273525 = 494393) (by norm_num)
theorem B3515683 : Blo 2081435 3515683 := bstep (se 1 (by rfl) ⟨2636762, by rfl⟩ : syracuseStep 3515683 = 5273525) B5273525
theorem B4687577 : Blo 2081435 4687577 := bstep (se 2 (by rfl) ⟨1757841, by rfl⟩ : syracuseStep 4687577 = 3515683) B3515683
theorem B3125051 : Blo 2081435 3125051 := bstep (se 1 (by rfl) ⟨2343788, by rfl⟩ : syracuseStep 3125051 = 4687577) B4687577
theorem B2083367 : Blo 2081435 2083367 := bstep (se 1 (by rfl) ⟨1562525, by rfl⟩ : syracuseStep 2083367 = 3125051) B3125051
theorem B2343793 : Blo 2081435 2343793 := bbase (se 2 (by rfl) ⟨878922, by rfl⟩ : syracuseStep 2343793 = 1757845) (by norm_num)
theorem B3125057 : Blo 2081435 3125057 := bstep (se 2 (by rfl) ⟨1171896, by rfl⟩ : syracuseStep 3125057 = 2343793) B2343793
theorem B2083371 : Blo 2081435 2083371 := bstep (se 1 (by rfl) ⟨1562528, by rfl⟩ : syracuseStep 2083371 = 3125057) B3125057
theorem B8899109 : Blo 2081435 8899109 := bbase (se 4 (by rfl) ⟨834291, by rfl⟩ : syracuseStep 8899109 = 1668583) (by norm_num)
theorem B5932739 : Blo 2081435 5932739 := bstep (se 1 (by rfl) ⟨4449554, by rfl⟩ : syracuseStep 5932739 = 8899109) B8899109
theorem B3955159 : Blo 2081435 3955159 := bstep (se 1 (by rfl) ⟨2966369, by rfl⟩ : syracuseStep 3955159 = 5932739) B5932739
theorem B5273545 : Blo 2081435 5273545 := bstep (se 2 (by rfl) ⟨1977579, by rfl⟩ : syracuseStep 5273545 = 3955159) B3955159
theorem B7031393 : Blo 2081435 7031393 := bstep (se 2 (by rfl) ⟨2636772, by rfl⟩ : syracuseStep 7031393 = 5273545) B5273545
theorem B4687595 : Blo 2081435 4687595 := bstep (se 1 (by rfl) ⟨3515696, by rfl⟩ : syracuseStep 4687595 = 7031393) B7031393
theorem B3125063 : Blo 2081435 3125063 := bstep (se 1 (by rfl) ⟨2343797, by rfl⟩ : syracuseStep 3125063 = 4687595) B4687595
theorem B2083375 : Blo 2081435 2083375 := bstep (se 1 (by rfl) ⟨1562531, by rfl⟩ : syracuseStep 2083375 = 3125063) B3125063
theorem B3125069 : Blo 2081435 3125069 := bbase (se 3 (by rfl) ⟨585950, by rfl⟩ : syracuseStep 3125069 = 1171901) (by norm_num)
theorem B2083379 : Blo 2081435 2083379 := bstep (se 1 (by rfl) ⟨1562534, by rfl⟩ : syracuseStep 2083379 = 3125069) B3125069
theorem B4687613 : Blo 2081435 4687613 := bbase (se 3 (by rfl) ⟨878927, by rfl⟩ : syracuseStep 4687613 = 1757855) (by norm_num)
theorem B3125075 : Blo 2081435 3125075 := bstep (se 1 (by rfl) ⟨2343806, by rfl⟩ : syracuseStep 3125075 = 4687613) B4687613
theorem B2083383 : Blo 2081435 2083383 := bstep (se 1 (by rfl) ⟨1562537, by rfl⟩ : syracuseStep 2083383 = 3125075) B3125075
theorem B3515717 : Blo 2081435 3515717 := bbase (se 4 (by rfl) ⟨329598, by rfl⟩ : syracuseStep 3515717 = 659197) (by norm_num)
theorem B2343811 : Blo 2081435 2343811 := bstep (se 1 (by rfl) ⟨1757858, by rfl⟩ : syracuseStep 2343811 = 3515717) B3515717
theorem B3125081 : Blo 2081435 3125081 := bstep (se 2 (by rfl) ⟨1171905, by rfl⟩ : syracuseStep 3125081 = 2343811) B2343811
theorem B2083387 : Blo 2081435 2083387 := bstep (se 1 (by rfl) ⟨1562540, by rfl⟩ : syracuseStep 2083387 = 3125081) B3125081
theorem B15820757 : Blo 2081435 15820757 := bbase (se 7 (by rfl) ⟨185399, by rfl⟩ : syracuseStep 15820757 = 370799) (by norm_num)
theorem B10547171 : Blo 2081435 10547171 := bstep (se 1 (by rfl) ⟨7910378, by rfl⟩ : syracuseStep 10547171 = 15820757) B15820757
theorem B7031447 : Blo 2081435 7031447 := bstep (se 1 (by rfl) ⟨5273585, by rfl⟩ : syracuseStep 7031447 = 10547171) B10547171
theorem B4687631 : Blo 2081435 4687631 := bstep (se 1 (by rfl) ⟨3515723, by rfl⟩ : syracuseStep 4687631 = 7031447) B7031447
theorem B3125087 : Blo 2081435 3125087 := bstep (se 1 (by rfl) ⟨2343815, by rfl⟩ : syracuseStep 3125087 = 4687631) B4687631
theorem B2083391 : Blo 2081435 2083391 := bstep (se 1 (by rfl) ⟨1562543, by rfl⟩ : syracuseStep 2083391 = 3125087) B3125087
theorem B3125093 : Blo 2081435 3125093 := bbase (se 4 (by rfl) ⟨292977, by rfl⟩ : syracuseStep 3125093 = 585955) (by norm_num)
theorem B2083395 : Blo 2081435 2083395 := bstep (se 1 (by rfl) ⟨1562546, by rfl⟩ : syracuseStep 2083395 = 3125093) B3125093
theorem B3955205 : Blo 2081435 3955205 := bbase (se 4 (by rfl) ⟨370800, by rfl⟩ : syracuseStep 3955205 = 741601) (by norm_num)
theorem B2636803 : Blo 2081435 2636803 := bstep (se 1 (by rfl) ⟨1977602, by rfl⟩ : syracuseStep 2636803 = 3955205) B3955205
theorem B3515737 : Blo 2081435 3515737 := bstep (se 2 (by rfl) ⟨1318401, by rfl⟩ : syracuseStep 3515737 = 2636803) B2636803
theorem B4687649 : Blo 2081435 4687649 := bstep (se 2 (by rfl) ⟨1757868, by rfl⟩ : syracuseStep 4687649 = 3515737) B3515737
theorem B3125099 : Blo 2081435 3125099 := bstep (se 1 (by rfl) ⟨2343824, by rfl⟩ : syracuseStep 3125099 = 4687649) B4687649
theorem B2083399 : Blo 2081435 2083399 := bstep (se 1 (by rfl) ⟨1562549, by rfl⟩ : syracuseStep 2083399 = 3125099) B3125099
theorem B2343829 : Blo 2081435 2343829 := bbase (se 6 (by rfl) ⟨54933, by rfl⟩ : syracuseStep 2343829 = 109867) (by norm_num)
theorem B3125105 : Blo 2081435 3125105 := bstep (se 2 (by rfl) ⟨1171914, by rfl⟩ : syracuseStep 3125105 = 2343829) B2343829
theorem B2083403 : Blo 2081435 2083403 := bstep (se 1 (by rfl) ⟨1562552, by rfl⟩ : syracuseStep 2083403 = 3125105) B3125105
theorem B2636813 : Blo 2081435 2636813 := bbase (se 3 (by rfl) ⟨494402, by rfl⟩ : syracuseStep 2636813 = 988805) (by norm_num)
theorem B7031501 : Blo 2081435 7031501 := bstep (se 3 (by rfl) ⟨1318406, by rfl⟩ : syracuseStep 7031501 = 2636813) B2636813
theorem B4687667 : Blo 2081435 4687667 := bstep (se 1 (by rfl) ⟨3515750, by rfl⟩ : syracuseStep 4687667 = 7031501) B7031501
theorem B3125111 : Blo 2081435 3125111 := bstep (se 1 (by rfl) ⟨2343833, by rfl⟩ : syracuseStep 3125111 = 4687667) B4687667
theorem B2083407 : Blo 2081435 2083407 := bstep (se 1 (by rfl) ⟨1562555, by rfl⟩ : syracuseStep 2083407 = 3125111) B3125111
theorem B3125117 : Blo 2081435 3125117 := bbase (se 3 (by rfl) ⟨585959, by rfl⟩ : syracuseStep 3125117 = 1171919) (by norm_num)
theorem B2083411 : Blo 2081435 2083411 := bstep (se 1 (by rfl) ⟨1562558, by rfl⟩ : syracuseStep 2083411 = 3125117) B3125117
theorem B4687685 : Blo 2081435 4687685 := bbase (se 4 (by rfl) ⟨439470, by rfl⟩ : syracuseStep 4687685 = 878941) (by norm_num)
theorem B3125123 : Blo 2081435 3125123 := bstep (se 1 (by rfl) ⟨2343842, by rfl⟩ : syracuseStep 3125123 = 4687685) B4687685
theorem B2083415 : Blo 2081435 2083415 := bstep (se 1 (by rfl) ⟨1562561, by rfl⟩ : syracuseStep 2083415 = 3125123) B3125123
theorem B3337237 : Blo 2081435 3337237 := bbase (se 6 (by rfl) ⟨78216, by rfl⟩ : syracuseStep 3337237 = 156433) (by norm_num)
theorem B4449649 : Blo 2081435 4449649 := bstep (se 2 (by rfl) ⟨1668618, by rfl⟩ : syracuseStep 4449649 = 3337237) B3337237
theorem B5932865 : Blo 2081435 5932865 := bstep (se 2 (by rfl) ⟨2224824, by rfl⟩ : syracuseStep 5932865 = 4449649) B4449649
theorem B3955243 : Blo 2081435 3955243 := bstep (se 1 (by rfl) ⟨2966432, by rfl⟩ : syracuseStep 3955243 = 5932865) B5932865
theorem B5273657 : Blo 2081435 5273657 := bstep (se 2 (by rfl) ⟨1977621, by rfl⟩ : syracuseStep 5273657 = 3955243) B3955243
theorem B3515771 : Blo 2081435 3515771 := bstep (se 1 (by rfl) ⟨2636828, by rfl⟩ : syracuseStep 3515771 = 5273657) B5273657
theorem B2343847 : Blo 2081435 2343847 := bstep (se 1 (by rfl) ⟨1757885, by rfl⟩ : syracuseStep 2343847 = 3515771) B3515771
theorem B3125129 : Blo 2081435 3125129 := bstep (se 2 (by rfl) ⟨1171923, by rfl⟩ : syracuseStep 3125129 = 2343847) B2343847
theorem B2083419 : Blo 2081435 2083419 := bstep (se 1 (by rfl) ⟨1562564, by rfl⟩ : syracuseStep 2083419 = 3125129) B3125129
theorem B10547333 : Blo 2081435 10547333 := bbase (se 4 (by rfl) ⟨988812, by rfl⟩ : syracuseStep 10547333 = 1977625) (by norm_num)
theorem B7031555 : Blo 2081435 7031555 := bstep (se 1 (by rfl) ⟨5273666, by rfl⟩ : syracuseStep 7031555 = 10547333) B10547333
theorem B4687703 : Blo 2081435 4687703 := bstep (se 1 (by rfl) ⟨3515777, by rfl⟩ : syracuseStep 4687703 = 7031555) B7031555
theorem B3125135 : Blo 2081435 3125135 := bstep (se 1 (by rfl) ⟨2343851, by rfl⟩ : syracuseStep 3125135 = 4687703) B4687703
theorem B2083423 : Blo 2081435 2083423 := bstep (se 1 (by rfl) ⟨1562567, by rfl⟩ : syracuseStep 2083423 = 3125135) B3125135
theorem B3125141 : Blo 2081435 3125141 := bbase (se 6 (by rfl) ⟨73245, by rfl⟩ : syracuseStep 3125141 = 146491) (by norm_num)
theorem B2083427 : Blo 2081435 2083427 := bstep (se 1 (by rfl) ⟨1562570, by rfl⟩ : syracuseStep 2083427 = 3125141) B3125141
theorem B2224837 : Blo 2081435 2224837 := bbase (se 4 (by rfl) ⟨208578, by rfl⟩ : syracuseStep 2224837 = 417157) (by norm_num)
theorem B11865797 : Blo 2081435 11865797 := bstep (se 4 (by rfl) ⟨1112418, by rfl⟩ : syracuseStep 11865797 = 2224837) B2224837
theorem B7910531 : Blo 2081435 7910531 := bstep (se 1 (by rfl) ⟨5932898, by rfl⟩ : syracuseStep 7910531 = 11865797) B11865797
theorem B5273687 : Blo 2081435 5273687 := bstep (se 1 (by rfl) ⟨3955265, by rfl⟩ : syracuseStep 5273687 = 7910531) B7910531
theorem B3515791 : Blo 2081435 3515791 := bstep (se 1 (by rfl) ⟨2636843, by rfl⟩ : syracuseStep 3515791 = 5273687) B5273687
theorem B4687721 : Blo 2081435 4687721 := bstep (se 2 (by rfl) ⟨1757895, by rfl⟩ : syracuseStep 4687721 = 3515791) B3515791
theorem B3125147 : Blo 2081435 3125147 := bstep (se 1 (by rfl) ⟨2343860, by rfl⟩ : syracuseStep 3125147 = 4687721) B4687721
theorem B2083431 : Blo 2081435 2083431 := bstep (se 1 (by rfl) ⟨1562573, by rfl⟩ : syracuseStep 2083431 = 3125147) B3125147
theorem B2343865 : Blo 2081435 2343865 := bbase (se 2 (by rfl) ⟨878949, by rfl⟩ : syracuseStep 2343865 = 1757899) (by norm_num)
theorem B3125153 : Blo 2081435 3125153 := bstep (se 2 (by rfl) ⟨1171932, by rfl⟩ : syracuseStep 3125153 = 2343865) B2343865
theorem B2083435 : Blo 2081435 2083435 := bstep (se 1 (by rfl) ⟨1562576, by rfl⟩ : syracuseStep 2083435 = 3125153) B3125153
theorem C0 (j : ℕ) (h1 : 520358 ≤ j) (h2 : j ≤ 520858) : Blo 2081435 (4 * j + 3) := by
  interval_cases j
  · exact B2081435
  · exact B2081439
  · exact B2081443
  · exact B2081447
  · exact B2081451
  · exact B2081455
  · exact B2081459
  · exact B2081463
  · exact B2081467
  · exact B2081471
  · exact B2081475
  · exact B2081479
  · exact B2081483
  · exact B2081487
  · exact B2081491
  · exact B2081495
  · exact B2081499
  · exact B2081503
  · exact B2081507
  · exact B2081511
  · exact B2081515
  · exact B2081519
  · exact B2081523
  · exact B2081527
  · exact B2081531
  · exact B2081535
  · exact B2081539
  · exact B2081543
  · exact B2081547
  · exact B2081551
  · exact B2081555
  · exact B2081559
  · exact B2081563
  · exact B2081567
  · exact B2081571
  · exact B2081575
  · exact B2081579
  · exact B2081583
  · exact B2081587
  · exact B2081591
  · exact B2081595
  · exact B2081599
  · exact B2081603
  · exact B2081607
  · exact B2081611
  · exact B2081615
  · exact B2081619
  · exact B2081623
  · exact B2081627
  · exact B2081631
  · exact B2081635
  · exact B2081639
  · exact B2081643
  · exact B2081647
  · exact B2081651
  · exact B2081655
  · exact B2081659
  · exact B2081663
  · exact B2081667
  · exact B2081671
  · exact B2081675
  · exact B2081679
  · exact B2081683
  · exact B2081687
  · exact B2081691
  · exact B2081695
  · exact B2081699
  · exact B2081703
  · exact B2081707
  · exact B2081711
  · exact B2081715
  · exact B2081719
  · exact B2081723
  · exact B2081727
  · exact B2081731
  · exact B2081735
  · exact B2081739
  · exact B2081743
  · exact B2081747
  · exact B2081751
  · exact B2081755
  · exact B2081759
  · exact B2081763
  · exact B2081767
  · exact B2081771
  · exact B2081775
  · exact B2081779
  · exact B2081783
  · exact B2081787
  · exact B2081791
  · exact B2081795
  · exact B2081799
  · exact B2081803
  · exact B2081807
  · exact B2081811
  · exact B2081815
  · exact B2081819
  · exact B2081823
  · exact B2081827
  · exact B2081831
  · exact B2081835
  · exact B2081839
  · exact B2081843
  · exact B2081847
  · exact B2081851
  · exact B2081855
  · exact B2081859
  · exact B2081863
  · exact B2081867
  · exact B2081871
  · exact B2081875
  · exact B2081879
  · exact B2081883
  · exact B2081887
  · exact B2081891
  · exact B2081895
  · exact B2081899
  · exact B2081903
  · exact B2081907
  · exact B2081911
  · exact B2081915
  · exact B2081919
  · exact B2081923
  · exact B2081927
  · exact B2081931
  · exact B2081935
  · exact B2081939
  · exact B2081943
  · exact B2081947
  · exact B2081951
  · exact B2081955
  · exact B2081959
  · exact B2081963
  · exact B2081967
  · exact B2081971
  · exact B2081975
  · exact B2081979
  · exact B2081983
  · exact B2081987
  · exact B2081991
  · exact B2081995
  · exact B2081999
  · exact B2082003
  · exact B2082007
  · exact B2082011
  · exact B2082015
  · exact B2082019
  · exact B2082023
  · exact B2082027
  · exact B2082031
  · exact B2082035
  · exact B2082039
  · exact B2082043
  · exact B2082047
  · exact B2082051
  · exact B2082055
  · exact B2082059
  · exact B2082063
  · exact B2082067
  · exact B2082071
  · exact B2082075
  · exact B2082079
  · exact B2082083
  · exact B2082087
  · exact B2082091
  · exact B2082095
  · exact B2082099
  · exact B2082103
  · exact B2082107
  · exact B2082111
  · exact B2082115
  · exact B2082119
  · exact B2082123
  · exact B2082127
  · exact B2082131
  · exact B2082135
  · exact B2082139
  · exact B2082143
  · exact B2082147
  · exact B2082151
  · exact B2082155
  · exact B2082159
  · exact B2082163
  · exact B2082167
  · exact B2082171
  · exact B2082175
  · exact B2082179
  · exact B2082183
  · exact B2082187
  · exact B2082191
  · exact B2082195
  · exact B2082199
  · exact B2082203
  · exact B2082207
  · exact B2082211
  · exact B2082215
  · exact B2082219
  · exact B2082223
  · exact B2082227
  · exact B2082231
  · exact B2082235
  · exact B2082239
  · exact B2082243
  · exact B2082247
  · exact B2082251
  · exact B2082255
  · exact B2082259
  · exact B2082263
  · exact B2082267
  · exact B2082271
  · exact B2082275
  · exact B2082279
  · exact B2082283
  · exact B2082287
  · exact B2082291
  · exact B2082295
  · exact B2082299
  · exact B2082303
  · exact B2082307
  · exact B2082311
  · exact B2082315
  · exact B2082319
  · exact B2082323
  · exact B2082327
  · exact B2082331
  · exact B2082335
  · exact B2082339
  · exact B2082343
  · exact B2082347
  · exact B2082351
  · exact B2082355
  · exact B2082359
  · exact B2082363
  · exact B2082367
  · exact B2082371
  · exact B2082375
  · exact B2082379
  · exact B2082383
  · exact B2082387
  · exact B2082391
  · exact B2082395
  · exact B2082399
  · exact B2082403
  · exact B2082407
  · exact B2082411
  · exact B2082415
  · exact B2082419
  · exact B2082423
  · exact B2082427
  · exact B2082431
  · exact B2082435
  · exact B2082439
  · exact B2082443
  · exact B2082447
  · exact B2082451
  · exact B2082455
  · exact B2082459
  · exact B2082463
  · exact B2082467
  · exact B2082471
  · exact B2082475
  · exact B2082479
  · exact B2082483
  · exact B2082487
  · exact B2082491
  · exact B2082495
  · exact B2082499
  · exact B2082503
  · exact B2082507
  · exact B2082511
  · exact B2082515
  · exact B2082519
  · exact B2082523
  · exact B2082527
  · exact B2082531
  · exact B2082535
  · exact B2082539
  · exact B2082543
  · exact B2082547
  · exact B2082551
  · exact B2082555
  · exact B2082559
  · exact B2082563
  · exact B2082567
  · exact B2082571
  · exact B2082575
  · exact B2082579
  · exact B2082583
  · exact B2082587
  · exact B2082591
  · exact B2082595
  · exact B2082599
  · exact B2082603
  · exact B2082607
  · exact B2082611
  · exact B2082615
  · exact B2082619
  · exact B2082623
  · exact B2082627
  · exact B2082631
  · exact B2082635
  · exact B2082639
  · exact B2082643
  · exact B2082647
  · exact B2082651
  · exact B2082655
  · exact B2082659
  · exact B2082663
  · exact B2082667
  · exact B2082671
  · exact B2082675
  · exact B2082679
  · exact B2082683
  · exact B2082687
  · exact B2082691
  · exact B2082695
  · exact B2082699
  · exact B2082703
  · exact B2082707
  · exact B2082711
  · exact B2082715
  · exact B2082719
  · exact B2082723
  · exact B2082727
  · exact B2082731
  · exact B2082735
  · exact B2082739
  · exact B2082743
  · exact B2082747
  · exact B2082751
  · exact B2082755
  · exact B2082759
  · exact B2082763
  · exact B2082767
  · exact B2082771
  · exact B2082775
  · exact B2082779
  · exact B2082783
  · exact B2082787
  · exact B2082791
  · exact B2082795
  · exact B2082799
  · exact B2082803
  · exact B2082807
  · exact B2082811
  · exact B2082815
  · exact B2082819
  · exact B2082823
  · exact B2082827
  · exact B2082831
  · exact B2082835
  · exact B2082839
  · exact B2082843
  · exact B2082847
  · exact B2082851
  · exact B2082855
  · exact B2082859
  · exact B2082863
  · exact B2082867
  · exact B2082871
  · exact B2082875
  · exact B2082879
  · exact B2082883
  · exact B2082887
  · exact B2082891
  · exact B2082895
  · exact B2082899
  · exact B2082903
  · exact B2082907
  · exact B2082911
  · exact B2082915
  · exact B2082919
  · exact B2082923
  · exact B2082927
  · exact B2082931
  · exact B2082935
  · exact B2082939
  · exact B2082943
  · exact B2082947
  · exact B2082951
  · exact B2082955
  · exact B2082959
  · exact B2082963
  · exact B2082967
  · exact B2082971
  · exact B2082975
  · exact B2082979
  · exact B2082983
  · exact B2082987
  · exact B2082991
  · exact B2082995
  · exact B2082999
  · exact B2083003
  · exact B2083007
  · exact B2083011
  · exact B2083015
  · exact B2083019
  · exact B2083023
  · exact B2083027
  · exact B2083031
  · exact B2083035
  · exact B2083039
  · exact B2083043
  · exact B2083047
  · exact B2083051
  · exact B2083055
  · exact B2083059
  · exact B2083063
  · exact B2083067
  · exact B2083071
  · exact B2083075
  · exact B2083079
  · exact B2083083
  · exact B2083087
  · exact B2083091
  · exact B2083095
  · exact B2083099
  · exact B2083103
  · exact B2083107
  · exact B2083111
  · exact B2083115
  · exact B2083119
  · exact B2083123
  · exact B2083127
  · exact B2083131
  · exact B2083135
  · exact B2083139
  · exact B2083143
  · exact B2083147
  · exact B2083151
  · exact B2083155
  · exact B2083159
  · exact B2083163
  · exact B2083167
  · exact B2083171
  · exact B2083175
  · exact B2083179
  · exact B2083183
  · exact B2083187
  · exact B2083191
  · exact B2083195
  · exact B2083199
  · exact B2083203
  · exact B2083207
  · exact B2083211
  · exact B2083215
  · exact B2083219
  · exact B2083223
  · exact B2083227
  · exact B2083231
  · exact B2083235
  · exact B2083239
  · exact B2083243
  · exact B2083247
  · exact B2083251
  · exact B2083255
  · exact B2083259
  · exact B2083263
  · exact B2083267
  · exact B2083271
  · exact B2083275
  · exact B2083279
  · exact B2083283
  · exact B2083287
  · exact B2083291
  · exact B2083295
  · exact B2083299
  · exact B2083303
  · exact B2083307
  · exact B2083311
  · exact B2083315
  · exact B2083319
  · exact B2083323
  · exact B2083327
  · exact B2083331
  · exact B2083335
  · exact B2083339
  · exact B2083343
  · exact B2083347
  · exact B2083351
  · exact B2083355
  · exact B2083359
  · exact B2083363
  · exact B2083367
  · exact B2083371
  · exact B2083375
  · exact B2083379
  · exact B2083383
  · exact B2083387
  · exact B2083391
  · exact B2083395
  · exact B2083399
  · exact B2083403
  · exact B2083407
  · exact B2083411
  · exact B2083415
  · exact B2083419
  · exact B2083423
  · exact B2083427
  · exact B2083431
  · exact B2083435
theorem solution (m : ℕ) (hlo : 2081435 ≤ m) (hhi : m ≤ 2083435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 520358 ≤ j := by omega
    have hj2 : j ≤ 520858 := by omega
    have hb : Blo 2081435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
