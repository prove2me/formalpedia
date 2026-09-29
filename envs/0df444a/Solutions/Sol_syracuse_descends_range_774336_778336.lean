-- Prove2me | solution 1 for syracuse_descends_range_774336_778336
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:05:25.363672+00:00
-- url     : https://prove2.me/submissions/15f692fc-8ca3-4bf0-9600-ae7ef455ce03

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


theorem B4423733 : Blo 774336 4423733 := bbase (se 5 (by rfl) ⟨207362, by rfl⟩ : syracuseStep 4423733 = 414725) (by norm_num)
theorem B1966133 : Blo 774336 1966133 := bbase (se 5 (by rfl) ⟨92162, by rfl⟩ : syracuseStep 1966133 = 184325) (by norm_num)
theorem B1310789 : Blo 774336 1310789 := bbase (se 4 (by rfl) ⟨122886, by rfl⟩ : syracuseStep 1310789 = 245773) (by norm_num)
theorem B983117 : Blo 774336 983117 := bbase (se 3 (by rfl) ⟨184334, by rfl⟩ : syracuseStep 983117 = 368669) (by norm_num)
theorem B1572949 : Blo 774336 1572949 := bbase (se 8 (by rfl) ⟨9216, by rfl⟩ : syracuseStep 1572949 = 18433) (by norm_num)
theorem B1474661 : Blo 774336 1474661 := bbase (se 4 (by rfl) ⟨138249, by rfl⟩ : syracuseStep 1474661 = 276499) (by norm_num)
theorem B4259957 : Blo 774336 4259957 := bbase (se 5 (by rfl) ⟨199685, by rfl⟩ : syracuseStep 4259957 = 399371) (by norm_num)
theorem B983173 : Blo 774336 983173 := bbase (se 4 (by rfl) ⟨92172, by rfl⟩ : syracuseStep 983173 = 184345) (by norm_num)
theorem B1310917 : Blo 774336 1310917 := bbase (se 4 (by rfl) ⟨122898, by rfl⟩ : syracuseStep 1310917 = 245797) (by norm_num)
theorem B983269 : Blo 774336 983269 := bbase (se 4 (by rfl) ⟨92181, by rfl⟩ : syracuseStep 983269 = 184363) (by norm_num)
theorem B1311005 : Blo 774336 1311005 := bbase (se 3 (by rfl) ⟨245813, by rfl⟩ : syracuseStep 1311005 = 491627) (by norm_num)
theorem B5898581 : Blo 774336 5898581 := bbase (se 10 (by rfl) ⟨8640, by rfl⟩ : syracuseStep 5898581 = 17281) (by norm_num)
theorem B2490709 : Blo 774336 2490709 := bbase (se 10 (by rfl) ⟨3648, by rfl⟩ : syracuseStep 2490709 = 7297) (by norm_num)
theorem B1245565 : Blo 774336 1245565 := bbase (se 3 (by rfl) ⟨233543, by rfl⟩ : syracuseStep 1245565 = 467087) (by norm_num)
theorem B3932549 : Blo 774336 3932549 := bbase (se 4 (by rfl) ⟨368676, by rfl⟩ : syracuseStep 3932549 = 737353) (by norm_num)
theorem B1474949 : Blo 774336 1474949 := bbase (se 4 (by rfl) ⟨138276, by rfl⟩ : syracuseStep 1474949 = 276553) (by norm_num)
theorem B1966477 : Blo 774336 1966477 := bbase (se 3 (by rfl) ⟨368714, by rfl⟩ : syracuseStep 1966477 = 737429) (by norm_num)
theorem B983441 : Blo 774336 983441 := bbase (se 2 (by rfl) ⟨368790, by rfl⟩ : syracuseStep 983441 = 737581) (by norm_num)
theorem B1311133 : Blo 774336 1311133 := bbase (se 3 (by rfl) ⟨245837, by rfl⟩ : syracuseStep 1311133 = 491675) (by norm_num)
theorem B2621861 : Blo 774336 2621861 := bbase (se 4 (by rfl) ⟨245799, by rfl⟩ : syracuseStep 2621861 = 491599) (by norm_num)
theorem B983497 : Blo 774336 983497 := bbase (se 2 (by rfl) ⟨368811, by rfl⟩ : syracuseStep 983497 = 737623) (by norm_num)
theorem B1769933 : Blo 774336 1769933 := bbase (se 3 (by rfl) ⟨331862, by rfl⟩ : syracuseStep 1769933 = 663725) (by norm_num)
theorem B1311221 : Blo 774336 1311221 := bbase (se 5 (by rfl) ⟨61463, by rfl⟩ : syracuseStep 1311221 = 122927) (by norm_num)
theorem B1966589 : Blo 774336 1966589 := bbase (se 3 (by rfl) ⟨368735, by rfl⟩ : syracuseStep 1966589 = 737471) (by norm_num)
theorem B786953 : Blo 774336 786953 := bbase (se 2 (by rfl) ⟨295107, by rfl⟩ : syracuseStep 786953 = 590215) (by norm_num)
theorem B6291989 : Blo 774336 6291989 := bbase (se 6 (by rfl) ⟨147468, by rfl⟩ : syracuseStep 6291989 = 294937) (by norm_num)
theorem B1475101 : Blo 774336 1475101 := bbase (se 3 (by rfl) ⟨276581, by rfl⟩ : syracuseStep 1475101 = 553163) (by norm_num)
theorem B983593 : Blo 774336 983593 := bbase (se 2 (by rfl) ⟨368847, by rfl⟩ : syracuseStep 983593 = 737695) (by norm_num)
theorem B1311349 : Blo 774336 1311349 := bbase (se 5 (by rfl) ⟨61469, by rfl⟩ : syracuseStep 1311349 = 122939) (by norm_num)
theorem B1573501 : Blo 774336 1573501 := bbase (se 3 (by rfl) ⟨295031, by rfl⟩ : syracuseStep 1573501 = 590063) (by norm_num)
theorem B1966781 : Blo 774336 1966781 := bbase (se 3 (by rfl) ⟨368771, by rfl⟩ : syracuseStep 1966781 = 737543) (by norm_num)
theorem B1311437 : Blo 774336 1311437 := bbase (se 3 (by rfl) ⟨245894, by rfl⟩ : syracuseStep 1311437 = 491789) (by norm_num)
theorem B983765 : Blo 774336 983765 := bbase (se 7 (by rfl) ⟨11528, by rfl⟩ : syracuseStep 983765 = 23057) (by norm_num)
theorem B983821 : Blo 774336 983821 := bbase (se 3 (by rfl) ⟨184466, by rfl⟩ : syracuseStep 983821 = 368933) (by norm_num)
theorem B1475405 : Blo 774336 1475405 := bbase (se 3 (by rfl) ⟨276638, by rfl⟩ : syracuseStep 1475405 = 553277) (by norm_num)
theorem B1311565 : Blo 774336 1311565 := bbase (se 3 (by rfl) ⟨245918, by rfl⟩ : syracuseStep 1311565 = 491837) (by norm_num)
theorem B787285 : Blo 774336 787285 := bbase (se 9 (by rfl) ⟨2306, by rfl⟩ : syracuseStep 787285 = 4613) (by norm_num)
theorem B2622293 : Blo 774336 2622293 := bbase (se 9 (by rfl) ⟨7682, by rfl⟩ : syracuseStep 2622293 = 15365) (by norm_num)
theorem B983917 : Blo 774336 983917 := bbase (se 3 (by rfl) ⟨184484, by rfl⟩ : syracuseStep 983917 = 368969) (by norm_num)
theorem B4981621 : Blo 774336 4981621 := bbase (se 5 (by rfl) ⟨233513, by rfl⟩ : syracuseStep 4981621 = 467027) (by norm_num)
theorem B1311653 : Blo 774336 1311653 := bbase (se 4 (by rfl) ⟨122967, by rfl⟩ : syracuseStep 1311653 = 245935) (by norm_num)
theorem B2655173 : Blo 774336 2655173 := bbase (se 4 (by rfl) ⟨248922, by rfl⟩ : syracuseStep 2655173 = 497845) (by norm_num)
theorem B1967125 : Blo 774336 1967125 := bbase (se 6 (by rfl) ⟨46104, by rfl⟩ : syracuseStep 1967125 = 92209) (by norm_num)
theorem B984089 : Blo 774336 984089 := bbase (se 2 (by rfl) ⟨369033, by rfl⟩ : syracuseStep 984089 = 738067) (by norm_num)
theorem B1311781 : Blo 774336 1311781 := bbase (se 4 (by rfl) ⟨122979, by rfl⟩ : syracuseStep 1311781 = 245959) (by norm_num)
theorem B984145 : Blo 774336 984145 := bbase (se 2 (by rfl) ⟨369054, by rfl⟩ : syracuseStep 984145 = 738109) (by norm_num)
theorem B1311869 : Blo 774336 1311869 := bbase (se 3 (by rfl) ⟨245975, by rfl⟩ : syracuseStep 1311869 = 491951) (by norm_num)
theorem B1967237 : Blo 774336 1967237 := bbase (se 4 (by rfl) ⟨184428, by rfl⟩ : syracuseStep 1967237 = 368857) (by norm_num)
theorem B984241 : Blo 774336 984241 := bbase (se 2 (by rfl) ⟨369090, by rfl⟩ : syracuseStep 984241 = 738181) (by norm_num)
theorem B1311997 : Blo 774336 1311997 := bbase (se 3 (by rfl) ⟨245999, by rfl⟩ : syracuseStep 1311997 = 491999) (by norm_num)
theorem B2622725 : Blo 774336 2622725 := bbase (se 4 (by rfl) ⟨245880, by rfl⟩ : syracuseStep 2622725 = 491761) (by norm_num)
theorem B1574213 : Blo 774336 1574213 := bbase (se 4 (by rfl) ⟨147582, by rfl⟩ : syracuseStep 1574213 = 295165) (by norm_num)
theorem B1967429 : Blo 774336 1967429 := bbase (se 4 (by rfl) ⟨184446, by rfl⟩ : syracuseStep 1967429 = 368893) (by norm_num)
theorem B1312085 : Blo 774336 1312085 := bbase (se 12 (by rfl) ⟨480, by rfl⟩ : syracuseStep 1312085 = 961) (by norm_num)
theorem B984413 : Blo 774336 984413 := bbase (se 3 (by rfl) ⟨184577, by rfl⟩ : syracuseStep 984413 = 369155) (by norm_num)
theorem B1246565 : Blo 774336 1246565 := bbase (se 4 (by rfl) ⟨116865, by rfl⟩ : syracuseStep 1246565 = 233731) (by norm_num)
theorem B787853 : Blo 774336 787853 := bbase (se 3 (by rfl) ⟨147722, by rfl⟩ : syracuseStep 787853 = 295445) (by norm_num)
theorem B984469 : Blo 774336 984469 := bbase (se 6 (by rfl) ⟨23073, by rfl⟩ : syracuseStep 984469 = 46147) (by norm_num)
theorem B886225 : Blo 774336 886225 := bbase (se 2 (by rfl) ⟨332334, by rfl⟩ : syracuseStep 886225 = 664669) (by norm_num)
theorem B2950613 : Blo 774336 2950613 := bbase (se 7 (by rfl) ⟨34577, by rfl⟩ : syracuseStep 2950613 = 69155) (by norm_num)
theorem B1312213 : Blo 774336 1312213 := bbase (se 7 (by rfl) ⟨15377, by rfl⟩ : syracuseStep 1312213 = 30755) (by norm_num)
theorem B1246693 : Blo 774336 1246693 := bbase (se 4 (by rfl) ⟨116877, by rfl⟩ : syracuseStep 1246693 = 233755) (by norm_num)
theorem B984565 : Blo 774336 984565 := bbase (se 5 (by rfl) ⟨46151, by rfl⟩ : syracuseStep 984565 = 92303) (by norm_num)
theorem B1312301 : Blo 774336 1312301 := bbase (se 3 (by rfl) ⟨246056, by rfl⟩ : syracuseStep 1312301 = 492113) (by norm_num)
theorem B1476157 : Blo 774336 1476157 := bbase (se 3 (by rfl) ⟨276779, by rfl⟩ : syracuseStep 1476157 = 553559) (by norm_num)
theorem B4785749 : Blo 774336 4785749 := bbase (se 8 (by rfl) ⟨28041, by rfl⟩ : syracuseStep 4785749 = 56083) (by norm_num)
theorem B2360981 : Blo 774336 2360981 := bbase (se 6 (by rfl) ⟨55335, by rfl⟩ : syracuseStep 2360981 = 110671) (by norm_num)
theorem B3933845 : Blo 774336 3933845 := bbase (se 6 (by rfl) ⟨92199, by rfl⟩ : syracuseStep 3933845 = 184399) (by norm_num)
theorem B1181341 : Blo 774336 1181341 := bbase (se 3 (by rfl) ⟨221501, by rfl⟩ : syracuseStep 1181341 = 443003) (by norm_num)
theorem B1967773 : Blo 774336 1967773 := bbase (se 3 (by rfl) ⟨368957, by rfl⟩ : syracuseStep 1967773 = 737915) (by norm_num)
theorem B984737 : Blo 774336 984737 := bbase (se 2 (by rfl) ⟨369276, by rfl⟩ : syracuseStep 984737 = 738553) (by norm_num)
theorem B1312429 : Blo 774336 1312429 := bbase (se 3 (by rfl) ⟨246080, by rfl⟩ : syracuseStep 1312429 = 492161) (by norm_num)
theorem B2623157 : Blo 774336 2623157 := bbase (se 5 (by rfl) ⟨122960, by rfl⟩ : syracuseStep 2623157 = 245921) (by norm_num)
theorem B1869493 : Blo 774336 1869493 := bbase (se 5 (by rfl) ⟨87632, by rfl⟩ : syracuseStep 1869493 = 175265) (by norm_num)
theorem B886477 : Blo 774336 886477 := bbase (se 3 (by rfl) ⟨166214, by rfl⟩ : syracuseStep 886477 = 332429) (by norm_num)
theorem B1476301 : Blo 774336 1476301 := bbase (se 3 (by rfl) ⟨276806, by rfl⟩ : syracuseStep 1476301 = 553613) (by norm_num)
theorem B984793 : Blo 774336 984793 := bbase (se 2 (by rfl) ⟨369297, by rfl⟩ : syracuseStep 984793 = 738595) (by norm_num)
theorem B2950901 : Blo 774336 2950901 := bbase (se 5 (by rfl) ⟨138323, by rfl⟩ : syracuseStep 2950901 = 276647) (by norm_num)
theorem B1312517 : Blo 774336 1312517 := bbase (se 4 (by rfl) ⟨123048, by rfl⟩ : syracuseStep 1312517 = 246097) (by norm_num)
theorem B1967885 : Blo 774336 1967885 := bbase (se 3 (by rfl) ⟨368978, by rfl⟩ : syracuseStep 1967885 = 737957) (by norm_num)
theorem B2361125 : Blo 774336 2361125 := bbase (se 4 (by rfl) ⟨221355, by rfl⟩ : syracuseStep 2361125 = 442711) (by norm_num)
theorem B984889 : Blo 774336 984889 := bbase (se 2 (by rfl) ⟨369333, by rfl⟩ : syracuseStep 984889 = 738667) (by norm_num)
theorem B1476461 : Blo 774336 1476461 := bbase (se 3 (by rfl) ⟨276836, by rfl⟩ : syracuseStep 1476461 = 553673) (by norm_num)
theorem B886645 : Blo 774336 886645 := bbase (se 5 (by rfl) ⟨41561, by rfl⟩ : syracuseStep 886645 = 83123) (by norm_num)
theorem B1312645 : Blo 774336 1312645 := bbase (se 4 (by rfl) ⟨123060, by rfl⟩ : syracuseStep 1312645 = 246121) (by norm_num)
theorem B2492309 : Blo 774336 2492309 := bbase (se 6 (by rfl) ⟨58413, by rfl⟩ : syracuseStep 2492309 = 116827) (by norm_num)
theorem B1968077 : Blo 774336 1968077 := bbase (se 3 (by rfl) ⟨369014, by rfl⟩ : syracuseStep 1968077 = 738029) (by norm_num)
theorem B1312733 : Blo 774336 1312733 := bbase (se 3 (by rfl) ⟨246137, by rfl⟩ : syracuseStep 1312733 = 492275) (by norm_num)
theorem B985061 : Blo 774336 985061 := bbase (se 4 (by rfl) ⟨92349, by rfl⟩ : syracuseStep 985061 = 184699) (by norm_num)
theorem B1476605 : Blo 774336 1476605 := bbase (se 3 (by rfl) ⟨276863, by rfl⟩ : syracuseStep 1476605 = 553727) (by norm_num)
theorem B1312861 : Blo 774336 1312861 := bbase (se 3 (by rfl) ⟨246161, by rfl⟩ : syracuseStep 1312861 = 492323) (by norm_num)
theorem B2623589 : Blo 774336 2623589 := bbase (se 4 (by rfl) ⟨245961, by rfl⟩ : syracuseStep 2623589 = 491923) (by norm_num)
theorem B1771685 : Blo 774336 1771685 := bbase (se 4 (by rfl) ⟨166095, by rfl⟩ : syracuseStep 1771685 = 332191) (by norm_num)
theorem B1312949 : Blo 774336 1312949 := bbase (se 5 (by rfl) ⟨61544, by rfl⟩ : syracuseStep 1312949 = 123089) (by norm_num)
theorem B4425941 : Blo 774336 4425941 := bbase (se 7 (by rfl) ⟨51866, by rfl⟩ : syracuseStep 4425941 = 103733) (by norm_num)
theorem B788761 : Blo 774336 788761 := bbase (se 2 (by rfl) ⟨295785, by rfl⟩ : syracuseStep 788761 = 591571) (by norm_num)
theorem B1476893 : Blo 774336 1476893 := bbase (se 3 (by rfl) ⟨276917, by rfl⟩ : syracuseStep 1476893 = 553835) (by norm_num)
theorem B1968421 : Blo 774336 1968421 := bbase (se 4 (by rfl) ⟨184539, by rfl⟩ : syracuseStep 1968421 = 369079) (by norm_num)
theorem B1313077 : Blo 774336 1313077 := bbase (se 5 (by rfl) ⟨61550, by rfl⟩ : syracuseStep 1313077 = 123101) (by norm_num)
theorem B1050989 : Blo 774336 1050989 := bbase (se 3 (by rfl) ⟨197060, by rfl⟩ : syracuseStep 1050989 = 394121) (by norm_num)
theorem B1313165 : Blo 774336 1313165 := bbase (se 3 (by rfl) ⟨246218, by rfl⟩ : syracuseStep 1313165 = 492437) (by norm_num)
theorem B1968533 : Blo 774336 1968533 := bbase (se 6 (by rfl) ⟨46137, by rfl⟩ : syracuseStep 1968533 = 92275) (by norm_num)
theorem B1477045 : Blo 774336 1477045 := bbase (se 5 (by rfl) ⟨69236, by rfl⟩ : syracuseStep 1477045 = 138473) (by norm_num)
theorem B1313293 : Blo 774336 1313293 := bbase (se 3 (by rfl) ⟨246242, by rfl⟩ : syracuseStep 1313293 = 492485) (by norm_num)
theorem B2624021 : Blo 774336 2624021 := bbase (se 6 (by rfl) ⟨61500, by rfl⟩ : syracuseStep 2624021 = 123001) (by norm_num)
theorem B3312197 : Blo 774336 3312197 := bbase (se 4 (by rfl) ⟨310518, by rfl⟩ : syracuseStep 3312197 = 621037) (by norm_num)
theorem B1968725 : Blo 774336 1968725 := bbase (se 8 (by rfl) ⟨11535, by rfl⟩ : syracuseStep 1968725 = 23071) (by norm_num)
theorem B1313381 : Blo 774336 1313381 := bbase (se 4 (by rfl) ⟨123129, by rfl⟩ : syracuseStep 1313381 = 246259) (by norm_num)
theorem B1477349 : Blo 774336 1477349 := bbase (se 4 (by rfl) ⟨138501, by rfl⟩ : syracuseStep 1477349 = 277003) (by norm_num)
theorem B1182485 : Blo 774336 1182485 := bbase (se 6 (by rfl) ⟨27714, by rfl⟩ : syracuseStep 1182485 = 55429) (by norm_num)
theorem B3312485 : Blo 774336 3312485 := bbase (se 4 (by rfl) ⟨310545, by rfl⟩ : syracuseStep 3312485 = 621091) (by norm_num)
theorem B2657141 : Blo 774336 2657141 := bbase (se 5 (by rfl) ⟨124553, by rfl⟩ : syracuseStep 2657141 = 249107) (by norm_num)
theorem B2952085 : Blo 774336 2952085 := bbase (se 6 (by rfl) ⟨69189, by rfl⟩ : syracuseStep 2952085 = 138379) (by norm_num)
theorem B3935141 : Blo 774336 3935141 := bbase (se 4 (by rfl) ⟨368919, by rfl⟩ : syracuseStep 3935141 = 737839) (by norm_num)
theorem B1969069 : Blo 774336 1969069 := bbase (se 3 (by rfl) ⟨369200, by rfl⟩ : syracuseStep 1969069 = 738401) (by norm_num)
theorem B2624453 : Blo 774336 2624453 := bbase (se 4 (by rfl) ⟨246042, by rfl⟩ : syracuseStep 2624453 = 492085) (by norm_num)
theorem B2493413 : Blo 774336 2493413 := bbase (se 4 (by rfl) ⟨233757, by rfl⟩ : syracuseStep 2493413 = 467515) (by norm_num)
theorem B1575965 : Blo 774336 1575965 := bbase (se 3 (by rfl) ⟨295493, by rfl⟩ : syracuseStep 1575965 = 590987) (by norm_num)
theorem B1969181 : Blo 774336 1969181 := bbase (se 3 (by rfl) ⟨369221, by rfl⟩ : syracuseStep 1969181 = 738443) (by norm_num)
theorem B2952389 : Blo 774336 2952389 := bbase (se 4 (by rfl) ⟨276786, by rfl⟩ : syracuseStep 2952389 = 553573) (by norm_num)
theorem B1969373 : Blo 774336 1969373 := bbase (se 3 (by rfl) ⟨369257, by rfl⟩ : syracuseStep 1969373 = 738515) (by norm_num)
theorem B2624885 : Blo 774336 2624885 := bbase (se 5 (by rfl) ⟨123041, by rfl⟩ : syracuseStep 2624885 = 246083) (by norm_num)
theorem B4722229 : Blo 774336 4722229 := bbase (se 5 (by rfl) ⟨221354, by rfl⟩ : syracuseStep 4722229 = 442709) (by norm_num)
theorem B1969717 : Blo 774336 1969717 := bbase (se 5 (by rfl) ⟨92330, by rfl⟩ : syracuseStep 1969717 = 184661) (by norm_num)
theorem B3313237 : Blo 774336 3313237 := bbase (se 8 (by rfl) ⟨19413, by rfl⟩ : syracuseStep 3313237 = 38827) (by norm_num)
theorem B1969829 : Blo 774336 1969829 := bbase (se 4 (by rfl) ⟨184671, by rfl⟩ : syracuseStep 1969829 = 369343) (by norm_num)
theorem B2625317 : Blo 774336 2625317 := bbase (se 4 (by rfl) ⟨246123, by rfl⟩ : syracuseStep 2625317 = 492247) (by norm_num)
theorem B1970021 : Blo 774336 1970021 := bbase (se 4 (by rfl) ⟨184689, by rfl⟩ : syracuseStep 1970021 = 369379) (by norm_num)
theorem B2101157 : Blo 774336 2101157 := bbase (se 4 (by rfl) ⟨196983, by rfl⟩ : syracuseStep 2101157 = 393967) (by norm_num)
theorem B2363413 : Blo 774336 2363413 := bbase (se 6 (by rfl) ⟨55392, by rfl⟩ : syracuseStep 2363413 = 110785) (by norm_num)
theorem B3543077 : Blo 774336 3543077 := bbase (se 4 (by rfl) ⟨332163, by rfl⟩ : syracuseStep 3543077 = 664327) (by norm_num)
theorem B3936437 : Blo 774336 3936437 := bbase (se 5 (by rfl) ⟨184520, by rfl⟩ : syracuseStep 3936437 = 369041) (by norm_num)
theorem B8523989 : Blo 774336 8523989 := bbase (se 7 (by rfl) ⟨99890, by rfl⟩ : syracuseStep 8523989 = 199781) (by norm_num)
theorem B2625749 : Blo 774336 2625749 := bbase (se 7 (by rfl) ⟨30770, by rfl⟩ : syracuseStep 2625749 = 61541) (by norm_num)
theorem B3739925 : Blo 774336 3739925 := bbase (se 6 (by rfl) ⟨87654, by rfl⟩ : syracuseStep 3739925 = 175309) (by norm_num)
theorem B3313973 : Blo 774336 3313973 := bbase (se 5 (by rfl) ⟨155342, by rfl⟩ : syracuseStep 3313973 = 310685) (by norm_num)
theorem B2626181 : Blo 774336 2626181 := bbase (se 4 (by rfl) ⟨246204, by rfl⟩ : syracuseStep 2626181 = 492409) (by norm_num)
theorem B2626613 : Blo 774336 2626613 := bbase (se 5 (by rfl) ⟨123122, by rfl⟩ : syracuseStep 2626613 = 246245) (by norm_num)
theorem B2954501 : Blo 774336 2954501 := bbase (se 4 (by rfl) ⟨276984, by rfl⟩ : syracuseStep 2954501 = 553969) (by norm_num)
theorem B1774997 : Blo 774336 1774997 := bbase (se 6 (by rfl) ⟨41601, by rfl⟩ : syracuseStep 1774997 = 83203) (by norm_num)
theorem B3937733 : Blo 774336 3937733 := bbase (se 4 (by rfl) ⟨369162, by rfl⟩ : syracuseStep 3937733 = 738325) (by norm_num)
theorem B1742309 : Blo 774336 1742309 := bbase (se 4 (by rfl) ⟨163341, by rfl⟩ : syracuseStep 1742309 = 326683) (by norm_num)
theorem B2954789 : Blo 774336 2954789 := bbase (se 4 (by rfl) ⟨277011, by rfl⟩ : syracuseStep 2954789 = 554023) (by norm_num)
theorem B1742381 : Blo 774336 1742381 := bbase (se 3 (by rfl) ⟨326696, by rfl⟩ : syracuseStep 1742381 = 653393) (by norm_num)
theorem B1742453 : Blo 774336 1742453 := bbase (se 5 (by rfl) ⟨81677, by rfl⟩ : syracuseStep 1742453 = 163355) (by norm_num)
theorem B1742525 : Blo 774336 1742525 := bbase (se 3 (by rfl) ⟨326723, by rfl⟩ : syracuseStep 1742525 = 653447) (by norm_num)
theorem B1349357 : Blo 774336 1349357 := bbase (se 3 (by rfl) ⟨253004, by rfl⟩ : syracuseStep 1349357 = 506009) (by norm_num)
theorem B1742597 : Blo 774336 1742597 := bbase (se 4 (by rfl) ⟨163368, by rfl⟩ : syracuseStep 1742597 = 326737) (by norm_num)
theorem B1414973 : Blo 774336 1414973 := bbase (se 3 (by rfl) ⟨265307, by rfl⟩ : syracuseStep 1414973 = 530615) (by norm_num)
theorem B1742669 : Blo 774336 1742669 := bbase (se 3 (by rfl) ⟨326750, by rfl⟩ : syracuseStep 1742669 = 653501) (by norm_num)
theorem B1742741 : Blo 774336 1742741 := bbase (se 6 (by rfl) ⟨40845, by rfl⟩ : syracuseStep 1742741 = 81691) (by norm_num)
theorem B2660309 : Blo 774336 2660309 := bbase (se 7 (by rfl) ⟨31175, by rfl⟩ : syracuseStep 2660309 = 62351) (by norm_num)
theorem B1742813 : Blo 774336 1742813 := bbase (se 3 (by rfl) ⟨326777, by rfl⟩ : syracuseStep 1742813 = 653555) (by norm_num)
theorem B1742885 : Blo 774336 1742885 := bbase (se 4 (by rfl) ⟨163395, by rfl⟩ : syracuseStep 1742885 = 326791) (by norm_num)
theorem B3545189 : Blo 774336 3545189 := bbase (se 4 (by rfl) ⟨332361, by rfl⟩ : syracuseStep 3545189 = 664723) (by norm_num)
theorem B1742957 : Blo 774336 1742957 := bbase (se 3 (by rfl) ⟨326804, by rfl⟩ : syracuseStep 1742957 = 653609) (by norm_num)
theorem B1743029 : Blo 774336 1743029 := bbase (se 5 (by rfl) ⟨81704, by rfl⟩ : syracuseStep 1743029 = 163409) (by norm_num)
theorem B1743101 : Blo 774336 1743101 := bbase (se 3 (by rfl) ⟨326831, by rfl⟩ : syracuseStep 1743101 = 653663) (by norm_num)
theorem B1743173 : Blo 774336 1743173 := bbase (se 4 (by rfl) ⟨163422, by rfl⟩ : syracuseStep 1743173 = 326845) (by norm_num)
theorem B1743245 : Blo 774336 1743245 := bbase (se 3 (by rfl) ⟨326858, by rfl⟩ : syracuseStep 1743245 = 653717) (by norm_num)
theorem B1743317 : Blo 774336 1743317 := bbase (se 7 (by rfl) ⟨20429, by rfl⟩ : syracuseStep 1743317 = 40859) (by norm_num)
theorem B5610005 : Blo 774336 5610005 := bbase (se 6 (by rfl) ⟨131484, by rfl⟩ : syracuseStep 5610005 = 262969) (by norm_num)
theorem B1743389 : Blo 774336 1743389 := bbase (se 3 (by rfl) ⟨326885, by rfl⟩ : syracuseStep 1743389 = 653771) (by norm_num)
theorem B1743461 : Blo 774336 1743461 := bbase (se 4 (by rfl) ⟨163449, by rfl⟩ : syracuseStep 1743461 = 326899) (by norm_num)
theorem B1743533 : Blo 774336 1743533 := bbase (se 3 (by rfl) ⟨326912, by rfl⟩ : syracuseStep 1743533 = 653825) (by norm_num)
theorem B957133 : Blo 774336 957133 := bbase (se 3 (by rfl) ⟨179462, by rfl⟩ : syracuseStep 957133 = 358925) (by norm_num)
theorem B3939029 : Blo 774336 3939029 := bbase (se 7 (by rfl) ⟨46160, by rfl⟩ : syracuseStep 3939029 = 92321) (by norm_num)
theorem B1743605 : Blo 774336 1743605 := bbase (se 5 (by rfl) ⟨81731, by rfl⟩ : syracuseStep 1743605 = 163463) (by norm_num)
theorem B2792245 : Blo 774336 2792245 := bbase (se 5 (by rfl) ⟨130886, by rfl⟩ : syracuseStep 2792245 = 261773) (by norm_num)
theorem B1743677 : Blo 774336 1743677 := bbase (se 3 (by rfl) ⟨326939, by rfl⟩ : syracuseStep 1743677 = 653879) (by norm_num)
theorem B2235269 : Blo 774336 2235269 := bbase (se 4 (by rfl) ⟨209556, by rfl⟩ : syracuseStep 2235269 = 419113) (by norm_num)
theorem B1743749 : Blo 774336 1743749 := bbase (se 4 (by rfl) ⟨163476, by rfl⟩ : syracuseStep 1743749 = 326953) (by norm_num)
theorem B1743821 : Blo 774336 1743821 := bbase (se 3 (by rfl) ⟨326966, by rfl⟩ : syracuseStep 1743821 = 653933) (by norm_num)
theorem B1743893 : Blo 774336 1743893 := bbase (se 6 (by rfl) ⟨40872, by rfl⟩ : syracuseStep 1743893 = 81745) (by norm_num)
theorem B1743965 : Blo 774336 1743965 := bbase (se 3 (by rfl) ⟨326993, by rfl⟩ : syracuseStep 1743965 = 653987) (by norm_num)
theorem B1744037 : Blo 774336 1744037 := bbase (se 4 (by rfl) ⟨163503, by rfl⟩ : syracuseStep 1744037 = 327007) (by norm_num)
theorem B1744109 : Blo 774336 1744109 := bbase (se 3 (by rfl) ⟨327020, by rfl⟩ : syracuseStep 1744109 = 654041) (by norm_num)
theorem B1744181 : Blo 774336 1744181 := bbase (se 5 (by rfl) ⟨81758, by rfl⟩ : syracuseStep 1744181 = 163517) (by norm_num)
theorem B1744253 : Blo 774336 1744253 := bbase (se 3 (by rfl) ⟨327047, by rfl⟩ : syracuseStep 1744253 = 654095) (by norm_num)
theorem B1744325 : Blo 774336 1744325 := bbase (se 4 (by rfl) ⟨163530, by rfl⟩ : syracuseStep 1744325 = 327061) (by norm_num)
theorem B1744397 : Blo 774336 1744397 := bbase (se 3 (by rfl) ⟨327074, by rfl⟩ : syracuseStep 1744397 = 654149) (by norm_num)
theorem B3317269 : Blo 774336 3317269 := bbase (se 6 (by rfl) ⟨77748, by rfl⟩ : syracuseStep 3317269 = 155497) (by norm_num)
theorem B8822357 : Blo 774336 8822357 := bbase (se 8 (by rfl) ⟨51693, by rfl⟩ : syracuseStep 8822357 = 103387) (by norm_num)
theorem B1744469 : Blo 774336 1744469 := bbase (se 8 (by rfl) ⟨10221, by rfl⟩ : syracuseStep 1744469 = 20443) (by norm_num)
theorem B1744541 : Blo 774336 1744541 := bbase (se 3 (by rfl) ⟨327101, by rfl⟩ : syracuseStep 1744541 = 654203) (by norm_num)
theorem B1744613 : Blo 774336 1744613 := bbase (se 4 (by rfl) ⟨163557, by rfl⟩ : syracuseStep 1744613 = 327115) (by norm_num)
theorem B1744685 : Blo 774336 1744685 := bbase (se 3 (by rfl) ⟨327128, by rfl⟩ : syracuseStep 1744685 = 654257) (by norm_num)
theorem B7446325 : Blo 774336 7446325 := bbase (se 5 (by rfl) ⟨349046, by rfl⟩ : syracuseStep 7446325 = 698093) (by norm_num)
theorem B1744757 : Blo 774336 1744757 := bbase (se 5 (by rfl) ⟨81785, by rfl⟩ : syracuseStep 1744757 = 163571) (by norm_num)
theorem B5906357 : Blo 774336 5906357 := bbase (se 5 (by rfl) ⟨276860, by rfl⟩ : syracuseStep 5906357 = 553721) (by norm_num)
theorem B1744829 : Blo 774336 1744829 := bbase (se 3 (by rfl) ⟨327155, by rfl⟩ : syracuseStep 1744829 = 654311) (by norm_num)
theorem B3940325 : Blo 774336 3940325 := bbase (se 4 (by rfl) ⟨369405, by rfl⟩ : syracuseStep 3940325 = 738811) (by norm_num)
theorem B1744901 : Blo 774336 1744901 := bbase (se 4 (by rfl) ⟨163584, by rfl⟩ : syracuseStep 1744901 = 327169) (by norm_num)
theorem B1744973 : Blo 774336 1744973 := bbase (se 3 (by rfl) ⟨327182, by rfl⟩ : syracuseStep 1744973 = 654365) (by norm_num)
theorem B1745045 : Blo 774336 1745045 := bbase (se 6 (by rfl) ⟨40899, by rfl⟩ : syracuseStep 1745045 = 81799) (by norm_num)
theorem B827605 : Blo 774336 827605 := bbase (se 7 (by rfl) ⟨9698, by rfl⟩ : syracuseStep 827605 = 19397) (by norm_num)
theorem B1745117 : Blo 774336 1745117 := bbase (se 3 (by rfl) ⟨327209, by rfl⟩ : syracuseStep 1745117 = 654419) (by norm_num)
theorem B827677 : Blo 774336 827677 := bbase (se 3 (by rfl) ⟨155189, by rfl⟩ : syracuseStep 827677 = 310379) (by norm_num)
theorem B1745189 : Blo 774336 1745189 := bbase (se 4 (by rfl) ⟨163611, by rfl⟩ : syracuseStep 1745189 = 327223) (by norm_num)
theorem B1745261 : Blo 774336 1745261 := bbase (se 3 (by rfl) ⟨327236, by rfl⟩ : syracuseStep 1745261 = 654473) (by norm_num)
theorem B3547525 : Blo 774336 3547525 := bbase (se 4 (by rfl) ⟨332580, by rfl⟩ : syracuseStep 3547525 = 665161) (by norm_num)
theorem B1745333 : Blo 774336 1745333 := bbase (se 5 (by rfl) ⟨81812, by rfl⟩ : syracuseStep 1745333 = 163625) (by norm_num)
theorem B827857 : Blo 774336 827857 := bbase (se 2 (by rfl) ⟨310446, by rfl⟩ : syracuseStep 827857 = 620893) (by norm_num)
theorem B1745405 : Blo 774336 1745405 := bbase (se 3 (by rfl) ⟨327263, by rfl⟩ : syracuseStep 1745405 = 654527) (by norm_num)
theorem B1745477 : Blo 774336 1745477 := bbase (se 4 (by rfl) ⟨163638, by rfl⟩ : syracuseStep 1745477 = 327277) (by norm_num)
theorem B1745549 : Blo 774336 1745549 := bbase (se 3 (by rfl) ⟨327290, by rfl⟩ : syracuseStep 1745549 = 654581) (by norm_num)
theorem B1745621 : Blo 774336 1745621 := bbase (se 7 (by rfl) ⟨20456, by rfl⟩ : syracuseStep 1745621 = 40913) (by norm_num)
theorem B1745693 : Blo 774336 1745693 := bbase (se 3 (by rfl) ⟨327317, by rfl⟩ : syracuseStep 1745693 = 654635) (by norm_num)
theorem B1745765 : Blo 774336 1745765 := bbase (se 4 (by rfl) ⟨163665, by rfl⟩ : syracuseStep 1745765 = 327331) (by norm_num)
theorem B828301 : Blo 774336 828301 := bbase (se 3 (by rfl) ⟨155306, by rfl⟩ : syracuseStep 828301 = 310613) (by norm_num)
theorem B1745837 : Blo 774336 1745837 := bbase (se 3 (by rfl) ⟨327344, by rfl⟩ : syracuseStep 1745837 = 654689) (by norm_num)
theorem B1680365 : Blo 774336 1680365 := bbase (se 3 (by rfl) ⟨315068, by rfl⟩ : syracuseStep 1680365 = 630137) (by norm_num)
theorem B1745909 : Blo 774336 1745909 := bbase (se 5 (by rfl) ⟨81839, by rfl⟩ : syracuseStep 1745909 = 163679) (by norm_num)
theorem B828425 : Blo 774336 828425 := bbase (se 2 (by rfl) ⟨310659, by rfl⟩ : syracuseStep 828425 = 621319) (by norm_num)
theorem B1745981 : Blo 774336 1745981 := bbase (se 3 (by rfl) ⟨327371, by rfl⟩ : syracuseStep 1745981 = 654743) (by norm_num)
theorem B1746053 : Blo 774336 1746053 := bbase (se 4 (by rfl) ⟨163692, by rfl⟩ : syracuseStep 1746053 = 327385) (by norm_num)
theorem B1746125 : Blo 774336 1746125 := bbase (se 3 (by rfl) ⟨327398, by rfl⟩ : syracuseStep 1746125 = 654797) (by norm_num)
theorem B828677 : Blo 774336 828677 := bbase (se 4 (by rfl) ⟨77688, by rfl⟩ : syracuseStep 828677 = 155377) (by norm_num)
theorem B1746197 : Blo 774336 1746197 := bbase (se 6 (by rfl) ⟨40926, by rfl⟩ : syracuseStep 1746197 = 81853) (by norm_num)
theorem B6628661 : Blo 774336 6628661 := bbase (se 5 (by rfl) ⟨310718, by rfl⟩ : syracuseStep 6628661 = 621437) (by norm_num)
theorem B1746269 : Blo 774336 1746269 := bbase (se 3 (by rfl) ⟨327425, by rfl⟩ : syracuseStep 1746269 = 654851) (by norm_num)
theorem B1746341 : Blo 774336 1746341 := bbase (se 4 (by rfl) ⟨163719, by rfl⟩ : syracuseStep 1746341 = 327439) (by norm_num)
theorem B2205157 : Blo 774336 2205157 := bbase (se 4 (by rfl) ⟨206733, by rfl⟩ : syracuseStep 2205157 = 413467) (by norm_num)
theorem B1746413 : Blo 774336 1746413 := bbase (se 3 (by rfl) ⟨327452, by rfl⟩ : syracuseStep 1746413 = 654905) (by norm_num)
theorem B1746485 : Blo 774336 1746485 := bbase (se 5 (by rfl) ⟨81866, by rfl⟩ : syracuseStep 1746485 = 163733) (by norm_num)
theorem B1746557 : Blo 774336 1746557 := bbase (se 3 (by rfl) ⟨327479, by rfl⟩ : syracuseStep 1746557 = 654959) (by norm_num)
theorem B2795141 : Blo 774336 2795141 := bbase (se 4 (by rfl) ⟨262044, by rfl⟩ : syracuseStep 2795141 = 524089) (by norm_num)
theorem B6727349 : Blo 774336 6727349 := bbase (se 5 (by rfl) ⟨315344, by rfl⟩ : syracuseStep 6727349 = 630689) (by norm_num)
theorem B829121 : Blo 774336 829121 := bbase (se 2 (by rfl) ⟨310920, by rfl⟩ : syracuseStep 829121 = 621841) (by norm_num)
theorem B1746629 : Blo 774336 1746629 := bbase (se 4 (by rfl) ⟨163746, by rfl⟩ : syracuseStep 1746629 = 327493) (by norm_num)
theorem B1746701 : Blo 774336 1746701 := bbase (se 3 (by rfl) ⟨327506, by rfl⟩ : syracuseStep 1746701 = 655013) (by norm_num)
theorem B1746773 : Blo 774336 1746773 := bbase (se 9 (by rfl) ⟨5117, by rfl⟩ : syracuseStep 1746773 = 10235) (by norm_num)
theorem B1746845 : Blo 774336 1746845 := bbase (se 3 (by rfl) ⟨327533, by rfl⟩ : syracuseStep 1746845 = 655067) (by norm_num)
theorem B829369 : Blo 774336 829369 := bbase (se 2 (by rfl) ⟨311013, by rfl⟩ : syracuseStep 829369 = 622027) (by norm_num)
theorem B1746917 : Blo 774336 1746917 := bbase (se 4 (by rfl) ⟨163773, by rfl⟩ : syracuseStep 1746917 = 327547) (by norm_num)
theorem B1746989 : Blo 774336 1746989 := bbase (se 3 (by rfl) ⟨327560, by rfl⟩ : syracuseStep 1746989 = 655121) (by norm_num)
theorem B1747061 : Blo 774336 1747061 := bbase (se 5 (by rfl) ⟨81893, by rfl⟩ : syracuseStep 1747061 = 163787) (by norm_num)
theorem B1747133 : Blo 774336 1747133 := bbase (se 3 (by rfl) ⟨327587, by rfl⟩ : syracuseStep 1747133 = 655175) (by norm_num)
theorem B1747205 : Blo 774336 1747205 := bbase (se 4 (by rfl) ⟨163800, by rfl⟩ : syracuseStep 1747205 = 327601) (by norm_num)
theorem B1091917 : Blo 774336 1091917 := bbase (se 3 (by rfl) ⟨204734, by rfl⟩ : syracuseStep 1091917 = 409469) (by norm_num)
theorem B1747277 : Blo 774336 1747277 := bbase (se 3 (by rfl) ⟨327614, by rfl⟩ : syracuseStep 1747277 = 655229) (by norm_num)
theorem B829813 : Blo 774336 829813 := bbase (se 5 (by rfl) ⟨38897, by rfl⟩ : syracuseStep 829813 = 77795) (by norm_num)
theorem B1747349 : Blo 774336 1747349 := bbase (se 6 (by rfl) ⟨40953, by rfl⟩ : syracuseStep 1747349 = 81907) (by norm_num)
theorem B829873 : Blo 774336 829873 := bbase (se 2 (by rfl) ⟨311202, by rfl⟩ : syracuseStep 829873 = 622405) (by norm_num)
theorem B3320261 : Blo 774336 3320261 := bbase (se 4 (by rfl) ⟨311274, by rfl⟩ : syracuseStep 3320261 = 622549) (by norm_num)
theorem B1747421 : Blo 774336 1747421 := bbase (se 3 (by rfl) ⟨327641, by rfl⟩ : syracuseStep 1747421 = 655283) (by norm_num)
theorem B1747493 : Blo 774336 1747493 := bbase (se 4 (by rfl) ⟨163827, by rfl⟩ : syracuseStep 1747493 = 327655) (by norm_num)
theorem B1747565 : Blo 774336 1747565 := bbase (se 3 (by rfl) ⟨327668, by rfl⟩ : syracuseStep 1747565 = 655337) (by norm_num)
theorem B1747637 : Blo 774336 1747637 := bbase (se 5 (by rfl) ⟨81920, by rfl⟩ : syracuseStep 1747637 = 163841) (by norm_num)
theorem B830189 : Blo 774336 830189 := bbase (se 3 (by rfl) ⟨155660, by rfl⟩ : syracuseStep 830189 = 311321) (by norm_num)
theorem B1747709 : Blo 774336 1747709 := bbase (se 3 (by rfl) ⟨327695, by rfl⟩ : syracuseStep 1747709 = 655391) (by norm_num)
theorem B994069 : Blo 774336 994069 := bbase (se 6 (by rfl) ⟨23298, by rfl⟩ : syracuseStep 994069 = 46597) (by norm_num)
theorem B1747781 : Blo 774336 1747781 := bbase (se 4 (by rfl) ⟨163854, by rfl⟩ : syracuseStep 1747781 = 327709) (by norm_num)
theorem B3976069 : Blo 774336 3976069 := bbase (se 4 (by rfl) ⟨372756, by rfl⟩ : syracuseStep 3976069 = 745513) (by norm_num)
theorem B1747853 : Blo 774336 1747853 := bbase (se 3 (by rfl) ⟨327722, by rfl⟩ : syracuseStep 1747853 = 655445) (by norm_num)
theorem B1747925 : Blo 774336 1747925 := bbase (se 7 (by rfl) ⟨20483, by rfl⟩ : syracuseStep 1747925 = 40967) (by norm_num)
theorem B1747997 : Blo 774336 1747997 := bbase (se 3 (by rfl) ⟨327749, by rfl⟩ : syracuseStep 1747997 = 655499) (by norm_num)
theorem B1748069 : Blo 774336 1748069 := bbase (se 4 (by rfl) ⟨163881, by rfl⟩ : syracuseStep 1748069 = 327763) (by norm_num)
theorem B830633 : Blo 774336 830633 := bbase (se 2 (by rfl) ⟨311487, by rfl⟩ : syracuseStep 830633 = 622975) (by norm_num)
theorem B1748141 : Blo 774336 1748141 := bbase (se 3 (by rfl) ⟨327776, by rfl⟩ : syracuseStep 1748141 = 655553) (by norm_num)
theorem B830693 : Blo 774336 830693 := bbase (se 4 (by rfl) ⟨77877, by rfl⟩ : syracuseStep 830693 = 155755) (by norm_num)
theorem B1748213 : Blo 774336 1748213 := bbase (se 5 (by rfl) ⟨81947, by rfl⟩ : syracuseStep 1748213 = 163895) (by norm_num)
theorem B1748285 : Blo 774336 1748285 := bbase (se 3 (by rfl) ⟨327803, by rfl⟩ : syracuseStep 1748285 = 655607) (by norm_num)
theorem B2239829 : Blo 774336 2239829 := bbase (se 11 (by rfl) ⟨1640, by rfl⟩ : syracuseStep 2239829 = 3281) (by norm_num)
theorem B5680469 : Blo 774336 5680469 := bbase (se 11 (by rfl) ⟨4160, by rfl⟩ : syracuseStep 5680469 = 8321) (by norm_num)
theorem B830821 : Blo 774336 830821 := bbase (se 4 (by rfl) ⟨77889, by rfl⟩ : syracuseStep 830821 = 155779) (by norm_num)
theorem B1748357 : Blo 774336 1748357 := bbase (se 4 (by rfl) ⟨163908, by rfl⟩ : syracuseStep 1748357 = 327817) (by norm_num)
theorem B3321269 : Blo 774336 3321269 := bbase (se 5 (by rfl) ⟨155684, by rfl⟩ : syracuseStep 3321269 = 311369) (by norm_num)
theorem B1748429 : Blo 774336 1748429 := bbase (se 3 (by rfl) ⟨327830, by rfl⟩ : syracuseStep 1748429 = 655661) (by norm_num)
theorem B1748501 : Blo 774336 1748501 := bbase (se 6 (by rfl) ⟨40980, by rfl⟩ : syracuseStep 1748501 = 81961) (by norm_num)
theorem B2993717 : Blo 774336 2993717 := bbase (se 5 (by rfl) ⟨140330, by rfl⟩ : syracuseStep 2993717 = 280661) (by norm_num)
theorem B1748573 : Blo 774336 1748573 := bbase (se 3 (by rfl) ⟨327857, by rfl⟩ : syracuseStep 1748573 = 655715) (by norm_num)
theorem B1748645 : Blo 774336 1748645 := bbase (se 4 (by rfl) ⟨163935, by rfl⟩ : syracuseStep 1748645 = 327871) (by norm_num)
theorem B7450325 : Blo 774336 7450325 := bbase (se 7 (by rfl) ⟨87308, by rfl⟩ : syracuseStep 7450325 = 174617) (by norm_num)
theorem B1748717 : Blo 774336 1748717 := bbase (se 3 (by rfl) ⟨327884, by rfl⟩ : syracuseStep 1748717 = 655769) (by norm_num)
theorem B1421077 : Blo 774336 1421077 := bbase (se 6 (by rfl) ⟨33306, by rfl⟩ : syracuseStep 1421077 = 66613) (by norm_num)
theorem B1748789 : Blo 774336 1748789 := bbase (se 5 (by rfl) ⟨81974, by rfl⟩ : syracuseStep 1748789 = 163949) (by norm_num)
theorem B4206421 : Blo 774336 4206421 := bbase (se 9 (by rfl) ⟨12323, by rfl⟩ : syracuseStep 4206421 = 24647) (by norm_num)
theorem B1748861 : Blo 774336 1748861 := bbase (se 3 (by rfl) ⟨327911, by rfl⟩ : syracuseStep 1748861 = 655823) (by norm_num)
theorem B1748933 : Blo 774336 1748933 := bbase (se 4 (by rfl) ⟨163962, by rfl⟩ : syracuseStep 1748933 = 327925) (by norm_num)
theorem B1749005 : Blo 774336 1749005 := bbase (se 3 (by rfl) ⟨327938, by rfl⟩ : syracuseStep 1749005 = 655877) (by norm_num)
theorem B1749077 : Blo 774336 1749077 := bbase (se 8 (by rfl) ⟨10248, by rfl⟩ : syracuseStep 1749077 = 20497) (by norm_num)
theorem B1749149 : Blo 774336 1749149 := bbase (se 3 (by rfl) ⟨327965, by rfl⟩ : syracuseStep 1749149 = 655931) (by norm_num)
theorem B1749221 : Blo 774336 1749221 := bbase (se 4 (by rfl) ⟨163989, by rfl⟩ : syracuseStep 1749221 = 327979) (by norm_num)
theorem B2208005 : Blo 774336 2208005 := bbase (se 4 (by rfl) ⟨207000, by rfl⟩ : syracuseStep 2208005 = 414001) (by norm_num)
theorem B1749293 : Blo 774336 1749293 := bbase (se 3 (by rfl) ⟨327992, by rfl⟩ : syracuseStep 1749293 = 655985) (by norm_num)
theorem B1749365 : Blo 774336 1749365 := bbase (se 5 (by rfl) ⟨82001, by rfl⟩ : syracuseStep 1749365 = 164003) (by norm_num)
theorem B1749437 : Blo 774336 1749437 := bbase (se 3 (by rfl) ⟨328019, by rfl⟩ : syracuseStep 1749437 = 656039) (by norm_num)
theorem B995809 : Blo 774336 995809 := bbase (se 2 (by rfl) ⟨373428, by rfl⟩ : syracuseStep 995809 = 746857) (by norm_num)
theorem B1749509 : Blo 774336 1749509 := bbase (se 4 (by rfl) ⟨164016, by rfl⟩ : syracuseStep 1749509 = 328033) (by norm_num)
theorem B1749581 : Blo 774336 1749581 := bbase (se 3 (by rfl) ⟨328046, by rfl⟩ : syracuseStep 1749581 = 656093) (by norm_num)
theorem B1749653 : Blo 774336 1749653 := bbase (se 6 (by rfl) ⟨41007, by rfl⟩ : syracuseStep 1749653 = 82015) (by norm_num)
theorem B1749725 : Blo 774336 1749725 := bbase (se 3 (by rfl) ⟨328073, by rfl⟩ : syracuseStep 1749725 = 656147) (by norm_num)
theorem B1749797 : Blo 774336 1749797 := bbase (se 4 (by rfl) ⟨164043, by rfl⟩ : syracuseStep 1749797 = 328087) (by norm_num)
theorem B1749869 : Blo 774336 1749869 := bbase (se 3 (by rfl) ⟨328100, by rfl⟩ : syracuseStep 1749869 = 656201) (by norm_num)
theorem B1749941 : Blo 774336 1749941 := bbase (se 5 (by rfl) ⟨82028, by rfl⟩ : syracuseStep 1749941 = 164057) (by norm_num)
theorem B1750013 : Blo 774336 1750013 := bbase (se 3 (by rfl) ⟨328127, by rfl⟩ : syracuseStep 1750013 = 656255) (by norm_num)
theorem B1750085 : Blo 774336 1750085 := bbase (se 4 (by rfl) ⟨164070, by rfl⟩ : syracuseStep 1750085 = 328141) (by norm_num)
theorem B1750157 : Blo 774336 1750157 := bbase (se 3 (by rfl) ⟨328154, by rfl⟩ : syracuseStep 1750157 = 656309) (by norm_num)
theorem B3323045 : Blo 774336 3323045 := bbase (se 4 (by rfl) ⟨311535, by rfl⟩ : syracuseStep 3323045 = 623071) (by norm_num)
theorem B1750229 : Blo 774336 1750229 := bbase (se 7 (by rfl) ⟨20510, by rfl⟩ : syracuseStep 1750229 = 41021) (by norm_num)
theorem B1750301 : Blo 774336 1750301 := bbase (se 3 (by rfl) ⟨328181, by rfl⟩ : syracuseStep 1750301 = 656363) (by norm_num)
theorem B1750373 : Blo 774336 1750373 := bbase (se 4 (by rfl) ⟨164097, by rfl⟩ : syracuseStep 1750373 = 328195) (by norm_num)
theorem B2209189 : Blo 774336 2209189 := bbase (se 4 (by rfl) ⟨207111, by rfl⟩ : syracuseStep 2209189 = 414223) (by norm_num)
theorem B1750445 : Blo 774336 1750445 := bbase (se 3 (by rfl) ⟨328208, by rfl⟩ : syracuseStep 1750445 = 656417) (by norm_num)
theorem B1750517 : Blo 774336 1750517 := bbase (se 5 (by rfl) ⟨82055, by rfl⟩ : syracuseStep 1750517 = 164111) (by norm_num)
theorem B1750589 : Blo 774336 1750589 := bbase (se 3 (by rfl) ⟨328235, by rfl⟩ : syracuseStep 1750589 = 656471) (by norm_num)
theorem B3978821 : Blo 774336 3978821 := bbase (se 4 (by rfl) ⟨373014, by rfl⟩ : syracuseStep 3978821 = 746029) (by norm_num)
theorem B2209349 : Blo 774336 2209349 := bbase (se 4 (by rfl) ⟨207126, by rfl⟩ : syracuseStep 2209349 = 414253) (by norm_num)
theorem B40416853 : Blo 774336 40416853 := bbase (se 8 (by rfl) ⟨236817, by rfl⟩ : syracuseStep 40416853 = 473635) (by norm_num)
theorem B3356293 : Blo 774336 3356293 := bbase (se 4 (by rfl) ⟨314652, by rfl⟩ : syracuseStep 3356293 = 629305) (by norm_num)
theorem B1750661 : Blo 774336 1750661 := bbase (se 4 (by rfl) ⟨164124, by rfl⟩ : syracuseStep 1750661 = 328249) (by norm_num)
theorem B1750733 : Blo 774336 1750733 := bbase (se 3 (by rfl) ⟨328262, by rfl⟩ : syracuseStep 1750733 = 656525) (by norm_num)
theorem B1750805 : Blo 774336 1750805 := bbase (se 6 (by rfl) ⟨41034, by rfl⟩ : syracuseStep 1750805 = 82069) (by norm_num)
theorem B2209589 : Blo 774336 2209589 := bbase (se 5 (by rfl) ⟨103574, by rfl⟩ : syracuseStep 2209589 = 207149) (by norm_num)
theorem B1750877 : Blo 774336 1750877 := bbase (se 3 (by rfl) ⟨328289, by rfl⟩ : syracuseStep 1750877 = 656579) (by norm_num)
theorem B1750949 : Blo 774336 1750949 := bbase (se 4 (by rfl) ⟨164151, by rfl⟩ : syracuseStep 1750949 = 328303) (by norm_num)
theorem B1751021 : Blo 774336 1751021 := bbase (se 3 (by rfl) ⟨328316, by rfl⟩ : syracuseStep 1751021 = 656633) (by norm_num)
theorem B931829 : Blo 774336 931829 := bbase (se 5 (by rfl) ⟨43679, by rfl⟩ : syracuseStep 931829 = 87359) (by norm_num)
theorem B2209781 : Blo 774336 2209781 := bbase (se 5 (by rfl) ⟨103583, by rfl⟩ : syracuseStep 2209781 = 207167) (by norm_num)
theorem B1751093 : Blo 774336 1751093 := bbase (se 5 (by rfl) ⟨82082, by rfl⟩ : syracuseStep 1751093 = 164165) (by norm_num)
theorem B1325117 : Blo 774336 1325117 := bbase (se 3 (by rfl) ⟨248459, by rfl⟩ : syracuseStep 1325117 = 496919) (by norm_num)
theorem B1751165 : Blo 774336 1751165 := bbase (se 3 (by rfl) ⟨328343, by rfl⟩ : syracuseStep 1751165 = 656687) (by norm_num)
theorem B1194149 : Blo 774336 1194149 := bbase (se 4 (by rfl) ⟨111951, by rfl⟩ : syracuseStep 1194149 = 223903) (by norm_num)
theorem B1751237 : Blo 774336 1751237 := bbase (se 4 (by rfl) ⟨164178, by rfl⟩ : syracuseStep 1751237 = 328357) (by norm_num)
theorem B1161509 : Blo 774336 1161509 := bbase (se 4 (by rfl) ⟨108891, by rfl⟩ : syracuseStep 1161509 = 217783) (by norm_num)
theorem B1161533 : Blo 774336 1161533 := bbase (se 3 (by rfl) ⟨217787, by rfl⟩ : syracuseStep 1161533 = 435575) (by norm_num)
theorem B1161557 : Blo 774336 1161557 := bbase (se 10 (by rfl) ⟨1701, by rfl⟩ : syracuseStep 1161557 = 3403) (by norm_num)
theorem B188627285 : Blo 774336 188627285 := bbase (se 10 (by rfl) ⟨276309, by rfl⟩ : syracuseStep 188627285 = 552619) (by norm_num)
theorem B1161581 : Blo 774336 1161581 := bbase (se 3 (by rfl) ⟨217796, by rfl⟩ : syracuseStep 1161581 = 435593) (by norm_num)
theorem B1161605 : Blo 774336 1161605 := bbase (se 4 (by rfl) ⟨108900, by rfl⟩ : syracuseStep 1161605 = 217801) (by norm_num)
theorem B1161629 : Blo 774336 1161629 := bbase (se 3 (by rfl) ⟨217805, by rfl⟩ : syracuseStep 1161629 = 435611) (by norm_num)
theorem B1161653 : Blo 774336 1161653 := bbase (se 5 (by rfl) ⟨54452, by rfl⟩ : syracuseStep 1161653 = 108905) (by norm_num)
theorem B1161677 : Blo 774336 1161677 := bbase (se 3 (by rfl) ⟨217814, by rfl⟩ : syracuseStep 1161677 = 435629) (by norm_num)
theorem B1161701 : Blo 774336 1161701 := bbase (se 4 (by rfl) ⟨108909, by rfl⟩ : syracuseStep 1161701 = 217819) (by norm_num)
theorem B1161725 : Blo 774336 1161725 := bbase (se 3 (by rfl) ⟨217823, by rfl⟩ : syracuseStep 1161725 = 435647) (by norm_num)
theorem B1161749 : Blo 774336 1161749 := bbase (se 6 (by rfl) ⟨27228, by rfl⟩ : syracuseStep 1161749 = 54457) (by norm_num)
theorem B1161773 : Blo 774336 1161773 := bbase (se 3 (by rfl) ⟨217832, by rfl⟩ : syracuseStep 1161773 = 435665) (by norm_num)
theorem B1161797 : Blo 774336 1161797 := bbase (se 4 (by rfl) ⟨108918, by rfl⟩ : syracuseStep 1161797 = 217837) (by norm_num)
theorem B1161821 : Blo 774336 1161821 := bbase (se 3 (by rfl) ⟨217841, by rfl⟩ : syracuseStep 1161821 = 435683) (by norm_num)
theorem B1161845 : Blo 774336 1161845 := bbase (se 5 (by rfl) ⟨54461, by rfl⟩ : syracuseStep 1161845 = 108923) (by norm_num)
theorem B1161869 : Blo 774336 1161869 := bbase (se 3 (by rfl) ⟨217850, by rfl⟩ : syracuseStep 1161869 = 435701) (by norm_num)
theorem B1161893 : Blo 774336 1161893 := bbase (se 4 (by rfl) ⟨108927, by rfl⟩ : syracuseStep 1161893 = 217855) (by norm_num)
theorem B932521 : Blo 774336 932521 := bbase (se 2 (by rfl) ⟨349695, by rfl⟩ : syracuseStep 932521 = 699391) (by norm_num)
theorem B1161917 : Blo 774336 1161917 := bbase (se 3 (by rfl) ⟨217859, by rfl⟩ : syracuseStep 1161917 = 435719) (by norm_num)
theorem B1161941 : Blo 774336 1161941 := bbase (se 7 (by rfl) ⟨13616, by rfl⟩ : syracuseStep 1161941 = 27233) (by norm_num)
theorem B1161965 : Blo 774336 1161965 := bbase (se 3 (by rfl) ⟨217868, by rfl⟩ : syracuseStep 1161965 = 435737) (by norm_num)
theorem B1161989 : Blo 774336 1161989 := bbase (se 4 (by rfl) ⟨108936, by rfl⟩ : syracuseStep 1161989 = 217873) (by norm_num)
theorem B932617 : Blo 774336 932617 := bbase (se 2 (by rfl) ⟨349731, by rfl⟩ : syracuseStep 932617 = 699463) (by norm_num)
theorem B1162013 : Blo 774336 1162013 := bbase (se 3 (by rfl) ⟨217877, by rfl⟩ : syracuseStep 1162013 = 435755) (by norm_num)
theorem B1162037 : Blo 774336 1162037 := bbase (se 5 (by rfl) ⟨54470, by rfl⟩ : syracuseStep 1162037 = 108941) (by norm_num)
theorem B1162061 : Blo 774336 1162061 := bbase (se 3 (by rfl) ⟨217886, by rfl⟩ : syracuseStep 1162061 = 435773) (by norm_num)
theorem B22362965 : Blo 774336 22362965 := bbase (se 9 (by rfl) ⟨65516, by rfl⟩ : syracuseStep 22362965 = 131033) (by norm_num)
theorem B1162085 : Blo 774336 1162085 := bbase (se 4 (by rfl) ⟨108945, by rfl⟩ : syracuseStep 1162085 = 217891) (by norm_num)
theorem B1162109 : Blo 774336 1162109 := bbase (se 3 (by rfl) ⟨217895, by rfl⟩ : syracuseStep 1162109 = 435791) (by norm_num)
theorem B1162133 : Blo 774336 1162133 := bbase (se 6 (by rfl) ⟨27237, by rfl⟩ : syracuseStep 1162133 = 54475) (by norm_num)
theorem B1162157 : Blo 774336 1162157 := bbase (se 3 (by rfl) ⟨217904, by rfl⟩ : syracuseStep 1162157 = 435809) (by norm_num)
theorem B1162181 : Blo 774336 1162181 := bbase (se 4 (by rfl) ⟨108954, by rfl⟩ : syracuseStep 1162181 = 217909) (by norm_num)
theorem B2210773 : Blo 774336 2210773 := bbase (se 7 (by rfl) ⟨25907, by rfl⟩ : syracuseStep 2210773 = 51815) (by norm_num)
theorem B1162205 : Blo 774336 1162205 := bbase (se 3 (by rfl) ⟨217913, by rfl⟩ : syracuseStep 1162205 = 435827) (by norm_num)
theorem B1162229 : Blo 774336 1162229 := bbase (se 5 (by rfl) ⟨54479, by rfl⟩ : syracuseStep 1162229 = 108959) (by norm_num)
theorem B1260533 : Blo 774336 1260533 := bbase (se 5 (by rfl) ⟨59087, by rfl⟩ : syracuseStep 1260533 = 118175) (by norm_num)
theorem B1162253 : Blo 774336 1162253 := bbase (se 3 (by rfl) ⟨217922, by rfl⟩ : syracuseStep 1162253 = 435845) (by norm_num)
theorem B1162277 : Blo 774336 1162277 := bbase (se 4 (by rfl) ⟨108963, by rfl⟩ : syracuseStep 1162277 = 217927) (by norm_num)
theorem B1162301 : Blo 774336 1162301 := bbase (se 3 (by rfl) ⟨217931, by rfl⟩ : syracuseStep 1162301 = 435863) (by norm_num)
theorem B1621061 : Blo 774336 1621061 := bbase (se 4 (by rfl) ⟨151974, by rfl⟩ : syracuseStep 1621061 = 303949) (by norm_num)
theorem B1162325 : Blo 774336 1162325 := bbase (se 8 (by rfl) ⟨6810, by rfl⟩ : syracuseStep 1162325 = 13621) (by norm_num)
theorem B1162349 : Blo 774336 1162349 := bbase (se 3 (by rfl) ⟨217940, by rfl⟩ : syracuseStep 1162349 = 435881) (by norm_num)
theorem B1162373 : Blo 774336 1162373 := bbase (se 4 (by rfl) ⟨108972, by rfl⟩ : syracuseStep 1162373 = 217945) (by norm_num)
theorem B1162397 : Blo 774336 1162397 := bbase (se 3 (by rfl) ⟨217949, by rfl⟩ : syracuseStep 1162397 = 435899) (by norm_num)
theorem B1162421 : Blo 774336 1162421 := bbase (se 5 (by rfl) ⟨54488, by rfl⟩ : syracuseStep 1162421 = 108977) (by norm_num)
theorem B1162445 : Blo 774336 1162445 := bbase (se 3 (by rfl) ⟨217958, by rfl⟩ : syracuseStep 1162445 = 435917) (by norm_num)
theorem B1162469 : Blo 774336 1162469 := bbase (se 4 (by rfl) ⟨108981, by rfl⟩ : syracuseStep 1162469 = 217963) (by norm_num)
theorem B1162493 : Blo 774336 1162493 := bbase (se 3 (by rfl) ⟨217967, by rfl⟩ : syracuseStep 1162493 = 435935) (by norm_num)
theorem B1162517 : Blo 774336 1162517 := bbase (se 6 (by rfl) ⟨27246, by rfl⟩ : syracuseStep 1162517 = 54493) (by norm_num)
theorem B1162541 : Blo 774336 1162541 := bbase (se 3 (by rfl) ⟨217976, by rfl⟩ : syracuseStep 1162541 = 435953) (by norm_num)
theorem B1162565 : Blo 774336 1162565 := bbase (se 4 (by rfl) ⟨108990, by rfl⟩ : syracuseStep 1162565 = 217981) (by norm_num)
theorem B1162589 : Blo 774336 1162589 := bbase (se 3 (by rfl) ⟨217985, by rfl⟩ : syracuseStep 1162589 = 435971) (by norm_num)
theorem B1162613 : Blo 774336 1162613 := bbase (se 5 (by rfl) ⟨54497, by rfl⟩ : syracuseStep 1162613 = 108995) (by norm_num)
theorem B1162637 : Blo 774336 1162637 := bbase (se 3 (by rfl) ⟨217994, by rfl⟩ : syracuseStep 1162637 = 435989) (by norm_num)
theorem B1162661 : Blo 774336 1162661 := bbase (se 4 (by rfl) ⟨108999, by rfl⟩ : syracuseStep 1162661 = 217999) (by norm_num)
theorem B1162685 : Blo 774336 1162685 := bbase (se 3 (by rfl) ⟨218003, by rfl⟩ : syracuseStep 1162685 = 436007) (by norm_num)
theorem B1162709 : Blo 774336 1162709 := bbase (se 7 (by rfl) ⟨13625, by rfl⟩ : syracuseStep 1162709 = 27251) (by norm_num)
theorem B1654253 : Blo 774336 1654253 := bbase (se 3 (by rfl) ⟨310172, by rfl⟩ : syracuseStep 1654253 = 620345) (by norm_num)
theorem B1162733 : Blo 774336 1162733 := bbase (se 3 (by rfl) ⟨218012, by rfl⟩ : syracuseStep 1162733 = 436025) (by norm_num)
theorem B1162757 : Blo 774336 1162757 := bbase (se 4 (by rfl) ⟨109008, by rfl⟩ : syracuseStep 1162757 = 218017) (by norm_num)
theorem B4439573 : Blo 774336 4439573 := bbase (se 6 (by rfl) ⟨104052, by rfl⟩ : syracuseStep 4439573 = 208105) (by norm_num)
theorem B933401 : Blo 774336 933401 := bbase (se 2 (by rfl) ⟨350025, by rfl⟩ : syracuseStep 933401 = 700051) (by norm_num)
theorem B1162781 : Blo 774336 1162781 := bbase (se 3 (by rfl) ⟨218021, by rfl⟩ : syracuseStep 1162781 = 436043) (by norm_num)
theorem B1162805 : Blo 774336 1162805 := bbase (se 5 (by rfl) ⟨54506, by rfl⟩ : syracuseStep 1162805 = 109013) (by norm_num)
theorem B1162829 : Blo 774336 1162829 := bbase (se 3 (by rfl) ⟨218030, by rfl⟩ : syracuseStep 1162829 = 436061) (by norm_num)
theorem B1162853 : Blo 774336 1162853 := bbase (se 4 (by rfl) ⟨109017, by rfl⟩ : syracuseStep 1162853 = 218035) (by norm_num)
theorem B1162877 : Blo 774336 1162877 := bbase (se 3 (by rfl) ⟨218039, by rfl⟩ : syracuseStep 1162877 = 436079) (by norm_num)
theorem B1162901 : Blo 774336 1162901 := bbase (se 6 (by rfl) ⟨27255, by rfl⟩ : syracuseStep 1162901 = 54511) (by norm_num)
theorem B1162925 : Blo 774336 1162925 := bbase (se 3 (by rfl) ⟨218048, by rfl⟩ : syracuseStep 1162925 = 436097) (by norm_num)
theorem B1162949 : Blo 774336 1162949 := bbase (se 4 (by rfl) ⟨109026, by rfl⟩ : syracuseStep 1162949 = 218053) (by norm_num)
theorem B1195733 : Blo 774336 1195733 := bbase (se 7 (by rfl) ⟨14012, by rfl⟩ : syracuseStep 1195733 = 28025) (by norm_num)
theorem B1162973 : Blo 774336 1162973 := bbase (se 3 (by rfl) ⟨218057, by rfl⟩ : syracuseStep 1162973 = 436115) (by norm_num)
theorem B1162997 : Blo 774336 1162997 := bbase (se 5 (by rfl) ⟨54515, by rfl⟩ : syracuseStep 1162997 = 109031) (by norm_num)
theorem B1163021 : Blo 774336 1163021 := bbase (se 3 (by rfl) ⟨218066, by rfl⟩ : syracuseStep 1163021 = 436133) (by norm_num)
theorem B1326869 : Blo 774336 1326869 := bbase (se 6 (by rfl) ⟨31098, by rfl⟩ : syracuseStep 1326869 = 62197) (by norm_num)
theorem B1163045 : Blo 774336 1163045 := bbase (se 4 (by rfl) ⟨109035, by rfl⟩ : syracuseStep 1163045 = 218071) (by norm_num)
theorem B1163069 : Blo 774336 1163069 := bbase (se 3 (by rfl) ⟨218075, by rfl⟩ : syracuseStep 1163069 = 436151) (by norm_num)
theorem B933709 : Blo 774336 933709 := bbase (se 3 (by rfl) ⟨175070, by rfl⟩ : syracuseStep 933709 = 350141) (by norm_num)
theorem B1163093 : Blo 774336 1163093 := bbase (se 9 (by rfl) ⟨3407, by rfl⟩ : syracuseStep 1163093 = 6815) (by norm_num)
theorem B1163117 : Blo 774336 1163117 := bbase (se 3 (by rfl) ⟨218084, by rfl⟩ : syracuseStep 1163117 = 436169) (by norm_num)
theorem B1163141 : Blo 774336 1163141 := bbase (se 4 (by rfl) ⟨109044, by rfl⟩ : syracuseStep 1163141 = 218089) (by norm_num)
theorem B1163165 : Blo 774336 1163165 := bbase (se 3 (by rfl) ⟨218093, by rfl⟩ : syracuseStep 1163165 = 436187) (by norm_num)
theorem B1163189 : Blo 774336 1163189 := bbase (se 5 (by rfl) ⟨54524, by rfl⟩ : syracuseStep 1163189 = 109049) (by norm_num)
theorem B1163213 : Blo 774336 1163213 := bbase (se 3 (by rfl) ⟨218102, by rfl⟩ : syracuseStep 1163213 = 436205) (by norm_num)
theorem B1163237 : Blo 774336 1163237 := bbase (se 4 (by rfl) ⟨109053, by rfl⟩ : syracuseStep 1163237 = 218107) (by norm_num)
theorem B1163261 : Blo 774336 1163261 := bbase (se 3 (by rfl) ⟨218111, by rfl⟩ : syracuseStep 1163261 = 436223) (by norm_num)
theorem B1163285 : Blo 774336 1163285 := bbase (se 6 (by rfl) ⟨27264, by rfl⟩ : syracuseStep 1163285 = 54529) (by norm_num)
theorem B2211877 : Blo 774336 2211877 := bbase (se 4 (by rfl) ⟨207363, by rfl⟩ : syracuseStep 2211877 = 414727) (by norm_num)
theorem B1163309 : Blo 774336 1163309 := bbase (se 3 (by rfl) ⟨218120, by rfl⟩ : syracuseStep 1163309 = 436241) (by norm_num)
theorem B1163333 : Blo 774336 1163333 := bbase (se 4 (by rfl) ⟨109062, by rfl⟩ : syracuseStep 1163333 = 218125) (by norm_num)
theorem B1163357 : Blo 774336 1163357 := bbase (se 3 (by rfl) ⟨218129, by rfl⟩ : syracuseStep 1163357 = 436259) (by norm_num)
theorem B1163381 : Blo 774336 1163381 := bbase (se 5 (by rfl) ⟨54533, by rfl⟩ : syracuseStep 1163381 = 109067) (by norm_num)
theorem B1163405 : Blo 774336 1163405 := bbase (se 3 (by rfl) ⟨218138, by rfl⟩ : syracuseStep 1163405 = 436277) (by norm_num)
theorem B1163429 : Blo 774336 1163429 := bbase (se 4 (by rfl) ⟨109071, by rfl⟩ : syracuseStep 1163429 = 218143) (by norm_num)
theorem B4538549 : Blo 774336 4538549 := bbase (se 5 (by rfl) ⟨212744, by rfl⟩ : syracuseStep 4538549 = 425489) (by norm_num)
theorem B1163453 : Blo 774336 1163453 := bbase (se 3 (by rfl) ⟨218147, by rfl⟩ : syracuseStep 1163453 = 436295) (by norm_num)
theorem B934097 : Blo 774336 934097 := bbase (se 2 (by rfl) ⟨350286, by rfl⟩ : syracuseStep 934097 = 700573) (by norm_num)
theorem B1163477 : Blo 774336 1163477 := bbase (se 7 (by rfl) ⟨13634, by rfl⟩ : syracuseStep 1163477 = 27269) (by norm_num)
theorem B1655005 : Blo 774336 1655005 := bbase (se 3 (by rfl) ⟨310313, by rfl⟩ : syracuseStep 1655005 = 620627) (by norm_num)
theorem B1163501 : Blo 774336 1163501 := bbase (se 3 (by rfl) ⟨218156, by rfl⟩ : syracuseStep 1163501 = 436313) (by norm_num)
theorem B1163525 : Blo 774336 1163525 := bbase (se 4 (by rfl) ⟨109080, by rfl⟩ : syracuseStep 1163525 = 218161) (by norm_num)
theorem B1163549 : Blo 774336 1163549 := bbase (se 3 (by rfl) ⟨218165, by rfl⟩ : syracuseStep 1163549 = 436331) (by norm_num)
theorem B1163573 : Blo 774336 1163573 := bbase (se 5 (by rfl) ⟨54542, by rfl⟩ : syracuseStep 1163573 = 109085) (by norm_num)
theorem B1163597 : Blo 774336 1163597 := bbase (se 3 (by rfl) ⟨218174, by rfl⟩ : syracuseStep 1163597 = 436349) (by norm_num)
theorem B1163621 : Blo 774336 1163621 := bbase (se 4 (by rfl) ⟨109089, by rfl⟩ : syracuseStep 1163621 = 218179) (by norm_num)
theorem B1655149 : Blo 774336 1655149 := bbase (se 3 (by rfl) ⟨310340, by rfl⟩ : syracuseStep 1655149 = 620681) (by norm_num)
theorem B1163645 : Blo 774336 1163645 := bbase (se 3 (by rfl) ⟨218183, by rfl⟩ : syracuseStep 1163645 = 436367) (by norm_num)
theorem B1163669 : Blo 774336 1163669 := bbase (se 6 (by rfl) ⟨27273, by rfl⟩ : syracuseStep 1163669 = 54547) (by norm_num)
theorem B2245013 : Blo 774336 2245013 := bbase (se 6 (by rfl) ⟨52617, by rfl⟩ : syracuseStep 2245013 = 105235) (by norm_num)
theorem B1163693 : Blo 774336 1163693 := bbase (se 3 (by rfl) ⟨218192, by rfl⟩ : syracuseStep 1163693 = 436385) (by norm_num)
theorem B1163717 : Blo 774336 1163717 := bbase (se 4 (by rfl) ⟨109098, by rfl⟩ : syracuseStep 1163717 = 218197) (by norm_num)
theorem B1163741 : Blo 774336 1163741 := bbase (se 3 (by rfl) ⟨218201, by rfl⟩ : syracuseStep 1163741 = 436403) (by norm_num)
theorem B1163765 : Blo 774336 1163765 := bbase (se 5 (by rfl) ⟨54551, by rfl⟩ : syracuseStep 1163765 = 109103) (by norm_num)
theorem B1163789 : Blo 774336 1163789 := bbase (se 3 (by rfl) ⟨218210, by rfl⟩ : syracuseStep 1163789 = 436421) (by norm_num)
theorem B4964885 : Blo 774336 4964885 := bbase (se 6 (by rfl) ⟨116364, by rfl⟩ : syracuseStep 4964885 = 232729) (by norm_num)
theorem B1163813 : Blo 774336 1163813 := bbase (se 4 (by rfl) ⟨109107, by rfl⟩ : syracuseStep 1163813 = 218215) (by norm_num)
theorem B934453 : Blo 774336 934453 := bbase (se 5 (by rfl) ⟨43802, by rfl⟩ : syracuseStep 934453 = 87605) (by norm_num)
theorem B1163837 : Blo 774336 1163837 := bbase (se 3 (by rfl) ⟨218219, by rfl⟩ : syracuseStep 1163837 = 436439) (by norm_num)
theorem B1163861 : Blo 774336 1163861 := bbase (se 8 (by rfl) ⟨6819, by rfl⟩ : syracuseStep 1163861 = 13639) (by norm_num)
theorem B1163885 : Blo 774336 1163885 := bbase (se 3 (by rfl) ⟨218228, by rfl⟩ : syracuseStep 1163885 = 436457) (by norm_num)
theorem B1163909 : Blo 774336 1163909 := bbase (se 4 (by rfl) ⟨109116, by rfl⟩ : syracuseStep 1163909 = 218233) (by norm_num)
theorem B1163933 : Blo 774336 1163933 := bbase (se 3 (by rfl) ⟨218237, by rfl⟩ : syracuseStep 1163933 = 436475) (by norm_num)
theorem B1163957 : Blo 774336 1163957 := bbase (se 5 (by rfl) ⟨54560, by rfl⟩ : syracuseStep 1163957 = 109121) (by norm_num)
theorem B1163981 : Blo 774336 1163981 := bbase (se 3 (by rfl) ⟨218246, by rfl⟩ : syracuseStep 1163981 = 436493) (by norm_num)
theorem B1655525 : Blo 774336 1655525 := bbase (se 4 (by rfl) ⟨155205, by rfl⟩ : syracuseStep 1655525 = 310411) (by norm_num)
theorem B1164005 : Blo 774336 1164005 := bbase (se 4 (by rfl) ⟨109125, by rfl⟩ : syracuseStep 1164005 = 218251) (by norm_num)
theorem B1164029 : Blo 774336 1164029 := bbase (se 3 (by rfl) ⟨218255, by rfl⟩ : syracuseStep 1164029 = 436511) (by norm_num)
theorem B1164053 : Blo 774336 1164053 := bbase (se 6 (by rfl) ⟨27282, by rfl⟩ : syracuseStep 1164053 = 54565) (by norm_num)
theorem B1164077 : Blo 774336 1164077 := bbase (se 3 (by rfl) ⟨218264, by rfl⟩ : syracuseStep 1164077 = 436529) (by norm_num)
theorem B1164101 : Blo 774336 1164101 := bbase (se 4 (by rfl) ⟨109134, by rfl⟩ : syracuseStep 1164101 = 218269) (by norm_num)
theorem B1164125 : Blo 774336 1164125 := bbase (se 3 (by rfl) ⟨218273, by rfl⟩ : syracuseStep 1164125 = 436547) (by norm_num)
theorem B1164149 : Blo 774336 1164149 := bbase (se 5 (by rfl) ⟨54569, by rfl⟩ : syracuseStep 1164149 = 109139) (by norm_num)
theorem B934789 : Blo 774336 934789 := bbase (se 4 (by rfl) ⟨87636, by rfl⟩ : syracuseStep 934789 = 175273) (by norm_num)
theorem B1164173 : Blo 774336 1164173 := bbase (se 3 (by rfl) ⟨218282, by rfl⟩ : syracuseStep 1164173 = 436565) (by norm_num)
theorem B1164197 : Blo 774336 1164197 := bbase (se 4 (by rfl) ⟨109143, by rfl⟩ : syracuseStep 1164197 = 218287) (by norm_num)
theorem B1164221 : Blo 774336 1164221 := bbase (se 3 (by rfl) ⟨218291, by rfl⟩ : syracuseStep 1164221 = 436583) (by norm_num)
theorem B1164245 : Blo 774336 1164245 := bbase (se 7 (by rfl) ⟨13643, by rfl⟩ : syracuseStep 1164245 = 27287) (by norm_num)
theorem B1164269 : Blo 774336 1164269 := bbase (se 3 (by rfl) ⟨218300, by rfl⟩ : syracuseStep 1164269 = 436601) (by norm_num)
theorem B1164293 : Blo 774336 1164293 := bbase (se 4 (by rfl) ⟨109152, by rfl⟩ : syracuseStep 1164293 = 218305) (by norm_num)
theorem B1164317 : Blo 774336 1164317 := bbase (se 3 (by rfl) ⟨218309, by rfl⟩ : syracuseStep 1164317 = 436619) (by norm_num)
theorem B1164341 : Blo 774336 1164341 := bbase (se 5 (by rfl) ⟨54578, by rfl⟩ : syracuseStep 1164341 = 109157) (by norm_num)
theorem B1164365 : Blo 774336 1164365 := bbase (se 3 (by rfl) ⟨218318, by rfl⟩ : syracuseStep 1164365 = 436637) (by norm_num)
theorem B1655893 : Blo 774336 1655893 := bbase (se 8 (by rfl) ⟨9702, by rfl⟩ : syracuseStep 1655893 = 19405) (by norm_num)
theorem B1164389 : Blo 774336 1164389 := bbase (se 4 (by rfl) ⟨109161, by rfl⟩ : syracuseStep 1164389 = 218323) (by norm_num)
theorem B1164413 : Blo 774336 1164413 := bbase (se 3 (by rfl) ⟨218327, by rfl⟩ : syracuseStep 1164413 = 436655) (by norm_num)
theorem B5883029 : Blo 774336 5883029 := bbase (se 6 (by rfl) ⟨137883, by rfl⟩ : syracuseStep 5883029 = 275767) (by norm_num)
theorem B1164437 : Blo 774336 1164437 := bbase (se 6 (by rfl) ⟨27291, by rfl⟩ : syracuseStep 1164437 = 54583) (by norm_num)
theorem B1164461 : Blo 774336 1164461 := bbase (se 3 (by rfl) ⟨218336, by rfl⟩ : syracuseStep 1164461 = 436673) (by norm_num)
theorem B6636725 : Blo 774336 6636725 := bbase (se 5 (by rfl) ⟨311096, by rfl⟩ : syracuseStep 6636725 = 622193) (by norm_num)
theorem B2802869 : Blo 774336 2802869 := bbase (se 5 (by rfl) ⟨131384, by rfl⟩ : syracuseStep 2802869 = 262769) (by norm_num)
theorem B1164485 : Blo 774336 1164485 := bbase (se 4 (by rfl) ⟨109170, by rfl⟩ : syracuseStep 1164485 = 218341) (by norm_num)
theorem B27280597 : Blo 774336 27280597 := bbase (se 7 (by rfl) ⟨319694, by rfl⟩ : syracuseStep 27280597 = 639389) (by norm_num)
theorem B1164509 : Blo 774336 1164509 := bbase (se 3 (by rfl) ⟨218345, by rfl⟩ : syracuseStep 1164509 = 436691) (by norm_num)
theorem B1164533 : Blo 774336 1164533 := bbase (se 5 (by rfl) ⟨54587, by rfl⟩ : syracuseStep 1164533 = 109175) (by norm_num)
theorem B1164557 : Blo 774336 1164557 := bbase (se 3 (by rfl) ⟨218354, by rfl⟩ : syracuseStep 1164557 = 436709) (by norm_num)
theorem B1164581 : Blo 774336 1164581 := bbase (se 4 (by rfl) ⟨109179, by rfl⟩ : syracuseStep 1164581 = 218359) (by norm_num)
theorem B1164605 : Blo 774336 1164605 := bbase (se 3 (by rfl) ⟨218363, by rfl⟩ : syracuseStep 1164605 = 436727) (by norm_num)
theorem B1164629 : Blo 774336 1164629 := bbase (se 12 (by rfl) ⟨426, by rfl⟩ : syracuseStep 1164629 = 853) (by norm_num)
theorem B1164653 : Blo 774336 1164653 := bbase (se 3 (by rfl) ⟨218372, by rfl⟩ : syracuseStep 1164653 = 436745) (by norm_num)
theorem B1164677 : Blo 774336 1164677 := bbase (se 4 (by rfl) ⟨109188, by rfl⟩ : syracuseStep 1164677 = 218377) (by norm_num)
theorem B1164701 : Blo 774336 1164701 := bbase (se 3 (by rfl) ⟨218381, by rfl⟩ : syracuseStep 1164701 = 436763) (by norm_num)
theorem B1164725 : Blo 774336 1164725 := bbase (se 5 (by rfl) ⟨54596, by rfl⟩ : syracuseStep 1164725 = 109193) (by norm_num)
theorem B1164749 : Blo 774336 1164749 := bbase (se 3 (by rfl) ⟨218390, by rfl⟩ : syracuseStep 1164749 = 436781) (by norm_num)
theorem B2803157 : Blo 774336 2803157 := bbase (se 7 (by rfl) ⟨32849, by rfl⟩ : syracuseStep 2803157 = 65699) (by norm_num)
theorem B1164773 : Blo 774336 1164773 := bbase (se 4 (by rfl) ⟨109197, by rfl⟩ : syracuseStep 1164773 = 218395) (by norm_num)
theorem B1164797 : Blo 774336 1164797 := bbase (se 3 (by rfl) ⟨218399, by rfl⟩ : syracuseStep 1164797 = 436799) (by norm_num)
theorem B2213381 : Blo 774336 2213381 := bbase (se 4 (by rfl) ⟨207504, by rfl⟩ : syracuseStep 2213381 = 415009) (by norm_num)
theorem B1164821 : Blo 774336 1164821 := bbase (se 6 (by rfl) ⟨27300, by rfl⟩ : syracuseStep 1164821 = 54601) (by norm_num)
theorem B1164845 : Blo 774336 1164845 := bbase (se 3 (by rfl) ⟨218408, by rfl⟩ : syracuseStep 1164845 = 436817) (by norm_num)
theorem B1164869 : Blo 774336 1164869 := bbase (se 4 (by rfl) ⟨109206, by rfl⟩ : syracuseStep 1164869 = 218413) (by norm_num)
theorem B2246213 : Blo 774336 2246213 := bbase (se 4 (by rfl) ⟨210582, by rfl⟩ : syracuseStep 2246213 = 421165) (by norm_num)
theorem B1164893 : Blo 774336 1164893 := bbase (se 3 (by rfl) ⟨218417, by rfl⟩ : syracuseStep 1164893 = 436835) (by norm_num)
theorem B1164917 : Blo 774336 1164917 := bbase (se 5 (by rfl) ⟨54605, by rfl⟩ : syracuseStep 1164917 = 109211) (by norm_num)
theorem B1164941 : Blo 774336 1164941 := bbase (se 3 (by rfl) ⟨218426, by rfl⟩ : syracuseStep 1164941 = 436853) (by norm_num)
theorem B1164965 : Blo 774336 1164965 := bbase (se 4 (by rfl) ⟨109215, by rfl⟩ : syracuseStep 1164965 = 218431) (by norm_num)
theorem B1164989 : Blo 774336 1164989 := bbase (se 3 (by rfl) ⟨218435, by rfl⟩ : syracuseStep 1164989 = 436871) (by norm_num)
theorem B1165013 : Blo 774336 1165013 := bbase (se 7 (by rfl) ⟨13652, by rfl⟩ : syracuseStep 1165013 = 27305) (by norm_num)
theorem B1165037 : Blo 774336 1165037 := bbase (se 3 (by rfl) ⟨218444, by rfl⟩ : syracuseStep 1165037 = 436889) (by norm_num)
theorem B3032821 : Blo 774336 3032821 := bbase (se 5 (by rfl) ⟨142163, by rfl⟩ : syracuseStep 3032821 = 284327) (by norm_num)
theorem B1165061 : Blo 774336 1165061 := bbase (se 4 (by rfl) ⟨109224, by rfl⟩ : syracuseStep 1165061 = 218449) (by norm_num)
theorem B1165085 : Blo 774336 1165085 := bbase (se 3 (by rfl) ⟨218453, by rfl⟩ : syracuseStep 1165085 = 436907) (by norm_num)
theorem B1165109 : Blo 774336 1165109 := bbase (se 5 (by rfl) ⟨54614, by rfl⟩ : syracuseStep 1165109 = 109229) (by norm_num)
theorem B1165133 : Blo 774336 1165133 := bbase (se 3 (by rfl) ⟨218462, by rfl⟩ : syracuseStep 1165133 = 436925) (by norm_num)
theorem B15976277 : Blo 774336 15976277 := bbase (se 9 (by rfl) ⟨46805, by rfl⟩ : syracuseStep 15976277 = 93611) (by norm_num)
theorem B1165157 : Blo 774336 1165157 := bbase (se 4 (by rfl) ⟨109233, by rfl⟩ : syracuseStep 1165157 = 218467) (by norm_num)
theorem B1165181 : Blo 774336 1165181 := bbase (se 3 (by rfl) ⟨218471, by rfl⟩ : syracuseStep 1165181 = 436943) (by norm_num)
theorem B1165205 : Blo 774336 1165205 := bbase (se 6 (by rfl) ⟨27309, by rfl⟩ : syracuseStep 1165205 = 54619) (by norm_num)
theorem B1165229 : Blo 774336 1165229 := bbase (se 3 (by rfl) ⟨218480, by rfl⟩ : syracuseStep 1165229 = 436961) (by norm_num)
theorem B1165253 : Blo 774336 1165253 := bbase (se 4 (by rfl) ⟨109242, by rfl⟩ : syracuseStep 1165253 = 218485) (by norm_num)
theorem B1165277 : Blo 774336 1165277 := bbase (se 3 (by rfl) ⟨218489, by rfl⟩ : syracuseStep 1165277 = 436979) (by norm_num)
theorem B1165301 : Blo 774336 1165301 := bbase (se 5 (by rfl) ⟨54623, by rfl⟩ : syracuseStep 1165301 = 109247) (by norm_num)
theorem B1165325 : Blo 774336 1165325 := bbase (se 3 (by rfl) ⟨218498, by rfl⟩ : syracuseStep 1165325 = 436997) (by norm_num)
theorem B1165349 : Blo 774336 1165349 := bbase (se 4 (by rfl) ⟨109251, by rfl⟩ : syracuseStep 1165349 = 218503) (by norm_num)
theorem B1165373 : Blo 774336 1165373 := bbase (se 3 (by rfl) ⟨218507, by rfl⟩ : syracuseStep 1165373 = 437015) (by norm_num)
theorem B1165397 : Blo 774336 1165397 := bbase (se 8 (by rfl) ⟨6828, by rfl⟩ : syracuseStep 1165397 = 13657) (by norm_num)
theorem B1165421 : Blo 774336 1165421 := bbase (se 3 (by rfl) ⟨218516, by rfl⟩ : syracuseStep 1165421 = 437033) (by norm_num)
theorem B1165445 : Blo 774336 1165445 := bbase (se 4 (by rfl) ⟨109260, by rfl⟩ : syracuseStep 1165445 = 218521) (by norm_num)
theorem B12601493 : Blo 774336 12601493 := bbase (se 6 (by rfl) ⟨295347, by rfl⟩ : syracuseStep 12601493 = 590695) (by norm_num)
theorem B1165469 : Blo 774336 1165469 := bbase (se 3 (by rfl) ⟨218525, by rfl⟩ : syracuseStep 1165469 = 437051) (by norm_num)
theorem B1165493 : Blo 774336 1165493 := bbase (se 5 (by rfl) ⟨54632, by rfl⟩ : syracuseStep 1165493 = 109265) (by norm_num)
theorem B1165517 : Blo 774336 1165517 := bbase (se 3 (by rfl) ⟨218534, by rfl⟩ : syracuseStep 1165517 = 437069) (by norm_num)
theorem B1165541 : Blo 774336 1165541 := bbase (se 4 (by rfl) ⟨109269, by rfl⟩ : syracuseStep 1165541 = 218539) (by norm_num)
theorem B1165565 : Blo 774336 1165565 := bbase (se 3 (by rfl) ⟨218543, by rfl⟩ : syracuseStep 1165565 = 437087) (by norm_num)
theorem B1165589 : Blo 774336 1165589 := bbase (se 6 (by rfl) ⟨27318, by rfl⟩ : syracuseStep 1165589 = 54637) (by norm_num)
theorem B1165613 : Blo 774336 1165613 := bbase (se 3 (by rfl) ⟨218552, by rfl⟩ : syracuseStep 1165613 = 437105) (by norm_num)
theorem B1165637 : Blo 774336 1165637 := bbase (se 4 (by rfl) ⟨109278, by rfl⟩ : syracuseStep 1165637 = 218557) (by norm_num)
theorem B1165661 : Blo 774336 1165661 := bbase (se 3 (by rfl) ⟨218561, by rfl⟩ : syracuseStep 1165661 = 437123) (by norm_num)
theorem B1493365 : Blo 774336 1493365 := bbase (se 5 (by rfl) ⟨70001, by rfl⟩ : syracuseStep 1493365 = 140003) (by norm_num)
theorem B1165685 : Blo 774336 1165685 := bbase (se 5 (by rfl) ⟨54641, by rfl⟩ : syracuseStep 1165685 = 109283) (by norm_num)
theorem B1165709 : Blo 774336 1165709 := bbase (se 3 (by rfl) ⟨218570, by rfl⟩ : syracuseStep 1165709 = 437141) (by norm_num)
theorem B1165733 : Blo 774336 1165733 := bbase (se 4 (by rfl) ⟨109287, by rfl⟩ : syracuseStep 1165733 = 218575) (by norm_num)
theorem B1165757 : Blo 774336 1165757 := bbase (se 3 (by rfl) ⟨218579, by rfl⟩ : syracuseStep 1165757 = 437159) (by norm_num)
theorem B1165781 : Blo 774336 1165781 := bbase (se 7 (by rfl) ⟨13661, by rfl⟩ : syracuseStep 1165781 = 27323) (by norm_num)
theorem B1165805 : Blo 774336 1165805 := bbase (se 3 (by rfl) ⟨218588, by rfl⟩ : syracuseStep 1165805 = 437177) (by norm_num)
theorem B1165829 : Blo 774336 1165829 := bbase (se 4 (by rfl) ⟨109296, by rfl⟩ : syracuseStep 1165829 = 218593) (by norm_num)
theorem B1165853 : Blo 774336 1165853 := bbase (se 3 (by rfl) ⟨218597, by rfl⟩ : syracuseStep 1165853 = 437195) (by norm_num)
theorem B1657397 : Blo 774336 1657397 := bbase (se 5 (by rfl) ⟨77690, by rfl⟩ : syracuseStep 1657397 = 155381) (by norm_num)
theorem B1165877 : Blo 774336 1165877 := bbase (se 5 (by rfl) ⟨54650, by rfl⟩ : syracuseStep 1165877 = 109301) (by norm_num)
theorem B1165901 : Blo 774336 1165901 := bbase (se 3 (by rfl) ⟨218606, by rfl⟩ : syracuseStep 1165901 = 437213) (by norm_num)
theorem B1165925 : Blo 774336 1165925 := bbase (se 4 (by rfl) ⟨109305, by rfl⟩ : syracuseStep 1165925 = 218611) (by norm_num)
theorem B1165949 : Blo 774336 1165949 := bbase (se 3 (by rfl) ⟨218615, by rfl⟩ : syracuseStep 1165949 = 437231) (by norm_num)
theorem B1165973 : Blo 774336 1165973 := bbase (se 6 (by rfl) ⟨27327, by rfl⟩ : syracuseStep 1165973 = 54655) (by norm_num)
theorem B1165997 : Blo 774336 1165997 := bbase (se 3 (by rfl) ⟨218624, by rfl⟩ : syracuseStep 1165997 = 437249) (by norm_num)
theorem B1657541 : Blo 774336 1657541 := bbase (se 4 (by rfl) ⟨155394, by rfl⟩ : syracuseStep 1657541 = 310789) (by norm_num)
theorem B1166021 : Blo 774336 1166021 := bbase (se 4 (by rfl) ⟨109314, by rfl⟩ : syracuseStep 1166021 = 218629) (by norm_num)
theorem B1166045 : Blo 774336 1166045 := bbase (se 3 (by rfl) ⟨218633, by rfl⟩ : syracuseStep 1166045 = 437267) (by norm_num)
theorem B871141 : Blo 774336 871141 := bbase (se 4 (by rfl) ⟨81669, by rfl⟩ : syracuseStep 871141 = 163339) (by norm_num)
theorem B1166069 : Blo 774336 1166069 := bbase (se 5 (by rfl) ⟨54659, by rfl⟩ : syracuseStep 1166069 = 109319) (by norm_num)
theorem B871177 : Blo 774336 871177 := bbase (se 2 (by rfl) ⟨326691, by rfl⟩ : syracuseStep 871177 = 653383) (by norm_num)
theorem B1166093 : Blo 774336 1166093 := bbase (se 3 (by rfl) ⟨218642, by rfl⟩ : syracuseStep 1166093 = 437285) (by norm_num)
theorem B1166117 : Blo 774336 1166117 := bbase (se 4 (by rfl) ⟨109323, by rfl⟩ : syracuseStep 1166117 = 218647) (by norm_num)
theorem B871213 : Blo 774336 871213 := bbase (se 3 (by rfl) ⟨163352, by rfl⟩ : syracuseStep 871213 = 326705) (by norm_num)
theorem B1166141 : Blo 774336 1166141 := bbase (se 3 (by rfl) ⟨218651, by rfl⟩ : syracuseStep 1166141 = 437303) (by norm_num)
theorem B871249 : Blo 774336 871249 := bbase (se 2 (by rfl) ⟨326718, by rfl⟩ : syracuseStep 871249 = 653437) (by norm_num)
theorem B7064405 : Blo 774336 7064405 := bbase (se 9 (by rfl) ⟨20696, by rfl⟩ : syracuseStep 7064405 = 41393) (by norm_num)
theorem B1166165 : Blo 774336 1166165 := bbase (se 9 (by rfl) ⟨3416, by rfl⟩ : syracuseStep 1166165 = 6833) (by norm_num)
theorem B1919837 : Blo 774336 1919837 := bbase (se 3 (by rfl) ⟨359969, by rfl⟩ : syracuseStep 1919837 = 719939) (by norm_num)
theorem B1166189 : Blo 774336 1166189 := bbase (se 3 (by rfl) ⟨218660, by rfl⟩ : syracuseStep 1166189 = 437321) (by norm_num)
theorem B871285 : Blo 774336 871285 := bbase (se 5 (by rfl) ⟨40841, by rfl⟩ : syracuseStep 871285 = 81683) (by norm_num)
theorem B1166213 : Blo 774336 1166213 := bbase (se 4 (by rfl) ⟨109332, by rfl⟩ : syracuseStep 1166213 = 218665) (by norm_num)
theorem B871321 : Blo 774336 871321 := bbase (se 2 (by rfl) ⟨326745, by rfl⟩ : syracuseStep 871321 = 653491) (by norm_num)
theorem B1166237 : Blo 774336 1166237 := bbase (se 3 (by rfl) ⟨218669, by rfl⟩ : syracuseStep 1166237 = 437339) (by norm_num)
theorem B1166261 : Blo 774336 1166261 := bbase (se 5 (by rfl) ⟨54668, by rfl⟩ : syracuseStep 1166261 = 109337) (by norm_num)
theorem B871357 : Blo 774336 871357 := bbase (se 3 (by rfl) ⟨163379, by rfl⟩ : syracuseStep 871357 = 326759) (by norm_num)
theorem B1166285 : Blo 774336 1166285 := bbase (se 3 (by rfl) ⟨218678, by rfl⟩ : syracuseStep 1166285 = 437357) (by norm_num)
theorem B871393 : Blo 774336 871393 := bbase (se 2 (by rfl) ⟨326772, by rfl⟩ : syracuseStep 871393 = 653545) (by norm_num)
theorem B1166309 : Blo 774336 1166309 := bbase (se 4 (by rfl) ⟨109341, by rfl⟩ : syracuseStep 1166309 = 218683) (by norm_num)
theorem B1166333 : Blo 774336 1166333 := bbase (se 3 (by rfl) ⟨218687, by rfl⟩ : syracuseStep 1166333 = 437375) (by norm_num)
theorem B871429 : Blo 774336 871429 := bbase (se 4 (by rfl) ⟨81696, by rfl⟩ : syracuseStep 871429 = 163393) (by norm_num)
theorem B1166357 : Blo 774336 1166357 := bbase (se 6 (by rfl) ⟨27336, by rfl⟩ : syracuseStep 1166357 = 54673) (by norm_num)
theorem B871465 : Blo 774336 871465 := bbase (se 2 (by rfl) ⟨326799, by rfl⟩ : syracuseStep 871465 = 653599) (by norm_num)
theorem B1657901 : Blo 774336 1657901 := bbase (se 3 (by rfl) ⟨310856, by rfl⟩ : syracuseStep 1657901 = 621713) (by norm_num)
theorem B1166381 : Blo 774336 1166381 := bbase (se 3 (by rfl) ⟨218696, by rfl⟩ : syracuseStep 1166381 = 437393) (by norm_num)
theorem B2214965 : Blo 774336 2214965 := bbase (se 5 (by rfl) ⟨103826, by rfl⟩ : syracuseStep 2214965 = 207653) (by norm_num)
theorem B1166405 : Blo 774336 1166405 := bbase (se 4 (by rfl) ⟨109350, by rfl⟩ : syracuseStep 1166405 = 218701) (by norm_num)
theorem B871501 : Blo 774336 871501 := bbase (se 3 (by rfl) ⟨163406, by rfl⟩ : syracuseStep 871501 = 326813) (by norm_num)
theorem B1166429 : Blo 774336 1166429 := bbase (se 3 (by rfl) ⟨218705, by rfl⟩ : syracuseStep 1166429 = 437411) (by norm_num)
theorem B871537 : Blo 774336 871537 := bbase (se 2 (by rfl) ⟨326826, by rfl⟩ : syracuseStep 871537 = 653653) (by norm_num)
theorem B1166453 : Blo 774336 1166453 := bbase (se 5 (by rfl) ⟨54677, by rfl⟩ : syracuseStep 1166453 = 109355) (by norm_num)
theorem B1166477 : Blo 774336 1166477 := bbase (se 3 (by rfl) ⟨218714, by rfl⟩ : syracuseStep 1166477 = 437429) (by norm_num)
theorem B871573 : Blo 774336 871573 := bbase (se 6 (by rfl) ⟨20427, by rfl⟩ : syracuseStep 871573 = 40855) (by norm_num)
theorem B1166501 : Blo 774336 1166501 := bbase (se 4 (by rfl) ⟨109359, by rfl⟩ : syracuseStep 1166501 = 218719) (by norm_num)
theorem B871609 : Blo 774336 871609 := bbase (se 2 (by rfl) ⟨326853, by rfl⟩ : syracuseStep 871609 = 653707) (by norm_num)
theorem B1166525 : Blo 774336 1166525 := bbase (se 3 (by rfl) ⟨218723, by rfl⟩ : syracuseStep 1166525 = 437447) (by norm_num)
theorem B1166549 : Blo 774336 1166549 := bbase (se 7 (by rfl) ⟨13670, by rfl⟩ : syracuseStep 1166549 = 27341) (by norm_num)
theorem B871645 : Blo 774336 871645 := bbase (se 3 (by rfl) ⟨163433, by rfl⟩ : syracuseStep 871645 = 326867) (by norm_num)
theorem B1166573 : Blo 774336 1166573 := bbase (se 3 (by rfl) ⟨218732, by rfl⟩ : syracuseStep 1166573 = 437465) (by norm_num)
theorem B871681 : Blo 774336 871681 := bbase (se 2 (by rfl) ⟨326880, by rfl⟩ : syracuseStep 871681 = 653761) (by norm_num)
theorem B1166597 : Blo 774336 1166597 := bbase (se 4 (by rfl) ⟨109368, by rfl⟩ : syracuseStep 1166597 = 218737) (by norm_num)
theorem B1166621 : Blo 774336 1166621 := bbase (se 3 (by rfl) ⟨218741, by rfl⟩ : syracuseStep 1166621 = 437483) (by norm_num)
theorem B871717 : Blo 774336 871717 := bbase (se 4 (by rfl) ⟨81723, by rfl⟩ : syracuseStep 871717 = 163447) (by norm_num)
theorem B1166645 : Blo 774336 1166645 := bbase (se 5 (by rfl) ⟨54686, by rfl⟩ : syracuseStep 1166645 = 109373) (by norm_num)
theorem B871753 : Blo 774336 871753 := bbase (se 2 (by rfl) ⟨326907, by rfl⟩ : syracuseStep 871753 = 653815) (by norm_num)
theorem B1166669 : Blo 774336 1166669 := bbase (se 3 (by rfl) ⟨218750, by rfl⟩ : syracuseStep 1166669 = 437501) (by norm_num)
theorem B1166693 : Blo 774336 1166693 := bbase (se 4 (by rfl) ⟨109377, by rfl⟩ : syracuseStep 1166693 = 218755) (by norm_num)
theorem B871789 : Blo 774336 871789 := bbase (se 3 (by rfl) ⟨163460, by rfl⟩ : syracuseStep 871789 = 326921) (by norm_num)
theorem B1166717 : Blo 774336 1166717 := bbase (se 3 (by rfl) ⟨218759, by rfl⟩ : syracuseStep 1166717 = 437519) (by norm_num)
theorem B871825 : Blo 774336 871825 := bbase (se 2 (by rfl) ⟨326934, by rfl⟩ : syracuseStep 871825 = 653869) (by norm_num)
theorem B1166741 : Blo 774336 1166741 := bbase (se 6 (by rfl) ⟨27345, by rfl⟩ : syracuseStep 1166741 = 54691) (by norm_num)
theorem B1166765 : Blo 774336 1166765 := bbase (se 3 (by rfl) ⟨218768, by rfl⟩ : syracuseStep 1166765 = 437537) (by norm_num)
theorem B871861 : Blo 774336 871861 := bbase (se 5 (by rfl) ⟨40868, by rfl⟩ : syracuseStep 871861 = 81737) (by norm_num)
theorem B1166789 : Blo 774336 1166789 := bbase (se 4 (by rfl) ⟨109386, by rfl⟩ : syracuseStep 1166789 = 218773) (by norm_num)
theorem B871897 : Blo 774336 871897 := bbase (se 2 (by rfl) ⟨326961, by rfl⟩ : syracuseStep 871897 = 653923) (by norm_num)
theorem B1166813 : Blo 774336 1166813 := bbase (se 3 (by rfl) ⟨218777, by rfl⟩ : syracuseStep 1166813 = 437555) (by norm_num)
theorem B1166837 : Blo 774336 1166837 := bbase (se 5 (by rfl) ⟨54695, by rfl⟩ : syracuseStep 1166837 = 109391) (by norm_num)
theorem B871933 : Blo 774336 871933 := bbase (se 3 (by rfl) ⟨163487, by rfl⟩ : syracuseStep 871933 = 326975) (by norm_num)
theorem B1166861 : Blo 774336 1166861 := bbase (se 3 (by rfl) ⟨218786, by rfl⟩ : syracuseStep 1166861 = 437573) (by norm_num)
theorem B871969 : Blo 774336 871969 := bbase (se 2 (by rfl) ⟨326988, by rfl⟩ : syracuseStep 871969 = 653977) (by norm_num)
theorem B1166885 : Blo 774336 1166885 := bbase (se 4 (by rfl) ⟨109395, by rfl⟩ : syracuseStep 1166885 = 218791) (by norm_num)
theorem B1166909 : Blo 774336 1166909 := bbase (se 3 (by rfl) ⟨218795, by rfl⟩ : syracuseStep 1166909 = 437591) (by norm_num)
theorem B872005 : Blo 774336 872005 := bbase (se 4 (by rfl) ⟨81750, by rfl⟩ : syracuseStep 872005 = 163501) (by norm_num)
theorem B1166933 : Blo 774336 1166933 := bbase (se 8 (by rfl) ⟨6837, by rfl⟩ : syracuseStep 1166933 = 13675) (by norm_num)
theorem B872041 : Blo 774336 872041 := bbase (se 2 (by rfl) ⟨327015, by rfl⟩ : syracuseStep 872041 = 654031) (by norm_num)
theorem B1166957 : Blo 774336 1166957 := bbase (se 3 (by rfl) ⟨218804, by rfl⟩ : syracuseStep 1166957 = 437609) (by norm_num)
theorem B1166981 : Blo 774336 1166981 := bbase (se 4 (by rfl) ⟨109404, by rfl⟩ : syracuseStep 1166981 = 218809) (by norm_num)
theorem B872077 : Blo 774336 872077 := bbase (se 3 (by rfl) ⟨163514, by rfl⟩ : syracuseStep 872077 = 327029) (by norm_num)
theorem B1167005 : Blo 774336 1167005 := bbase (se 3 (by rfl) ⟨218813, by rfl⟩ : syracuseStep 1167005 = 437627) (by norm_num)
theorem B872113 : Blo 774336 872113 := bbase (se 2 (by rfl) ⟨327042, by rfl⟩ : syracuseStep 872113 = 654085) (by norm_num)
theorem B1167029 : Blo 774336 1167029 := bbase (se 5 (by rfl) ⟨54704, by rfl⟩ : syracuseStep 1167029 = 109409) (by norm_num)
theorem B1167053 : Blo 774336 1167053 := bbase (se 3 (by rfl) ⟨218822, by rfl⟩ : syracuseStep 1167053 = 437645) (by norm_num)
theorem B872149 : Blo 774336 872149 := bbase (se 7 (by rfl) ⟨10220, by rfl⟩ : syracuseStep 872149 = 20441) (by norm_num)
theorem B2215637 : Blo 774336 2215637 := bbase (se 7 (by rfl) ⟨25964, by rfl⟩ : syracuseStep 2215637 = 51929) (by norm_num)
theorem B1167077 : Blo 774336 1167077 := bbase (se 4 (by rfl) ⟨109413, by rfl⟩ : syracuseStep 1167077 = 218827) (by norm_num)
theorem B872185 : Blo 774336 872185 := bbase (se 2 (by rfl) ⟨327069, by rfl⟩ : syracuseStep 872185 = 654139) (by norm_num)
theorem B1167101 : Blo 774336 1167101 := bbase (se 3 (by rfl) ⟨218831, by rfl⟩ : syracuseStep 1167101 = 437663) (by norm_num)
theorem B1167125 : Blo 774336 1167125 := bbase (se 6 (by rfl) ⟨27354, by rfl⟩ : syracuseStep 1167125 = 54709) (by norm_num)
theorem B872221 : Blo 774336 872221 := bbase (se 3 (by rfl) ⟨163541, by rfl⟩ : syracuseStep 872221 = 327083) (by norm_num)
theorem B1167149 : Blo 774336 1167149 := bbase (se 3 (by rfl) ⟨218840, by rfl⟩ : syracuseStep 1167149 = 437681) (by norm_num)
theorem B872257 : Blo 774336 872257 := bbase (se 2 (by rfl) ⟨327096, by rfl⟩ : syracuseStep 872257 = 654193) (by norm_num)
theorem B1167173 : Blo 774336 1167173 := bbase (se 4 (by rfl) ⟨109422, by rfl⟩ : syracuseStep 1167173 = 218845) (by norm_num)
theorem B1167197 : Blo 774336 1167197 := bbase (se 3 (by rfl) ⟨218849, by rfl⟩ : syracuseStep 1167197 = 437699) (by norm_num)
theorem B872293 : Blo 774336 872293 := bbase (se 4 (by rfl) ⟨81777, by rfl⟩ : syracuseStep 872293 = 163555) (by norm_num)
theorem B1167221 : Blo 774336 1167221 := bbase (se 5 (by rfl) ⟨54713, by rfl⟩ : syracuseStep 1167221 = 109427) (by norm_num)
theorem B872329 : Blo 774336 872329 := bbase (se 2 (by rfl) ⟨327123, by rfl⟩ : syracuseStep 872329 = 654247) (by norm_num)
theorem B1167245 : Blo 774336 1167245 := bbase (se 3 (by rfl) ⟨218858, by rfl⟩ : syracuseStep 1167245 = 437717) (by norm_num)
theorem B1658789 : Blo 774336 1658789 := bbase (se 4 (by rfl) ⟨155511, by rfl⟩ : syracuseStep 1658789 = 311023) (by norm_num)
theorem B1167269 : Blo 774336 1167269 := bbase (se 4 (by rfl) ⟨109431, by rfl⟩ : syracuseStep 1167269 = 218863) (by norm_num)
theorem B872365 : Blo 774336 872365 := bbase (se 3 (by rfl) ⟨163568, by rfl⟩ : syracuseStep 872365 = 327137) (by norm_num)
theorem B1167293 : Blo 774336 1167293 := bbase (se 3 (by rfl) ⟨218867, by rfl⟩ : syracuseStep 1167293 = 437735) (by norm_num)
theorem B839629 : Blo 774336 839629 := bbase (se 3 (by rfl) ⟨157430, by rfl⟩ : syracuseStep 839629 = 314861) (by norm_num)
theorem B872401 : Blo 774336 872401 := bbase (se 2 (by rfl) ⟨327150, by rfl⟩ : syracuseStep 872401 = 654301) (by norm_num)
theorem B1167317 : Blo 774336 1167317 := bbase (se 7 (by rfl) ⟨13679, by rfl⟩ : syracuseStep 1167317 = 27359) (by norm_num)
theorem B1167341 : Blo 774336 1167341 := bbase (se 3 (by rfl) ⟨218876, by rfl⟩ : syracuseStep 1167341 = 437753) (by norm_num)
theorem B872437 : Blo 774336 872437 := bbase (se 5 (by rfl) ⟨40895, by rfl⟩ : syracuseStep 872437 = 81791) (by norm_num)
theorem B1167365 : Blo 774336 1167365 := bbase (se 4 (by rfl) ⟨109440, by rfl⟩ : syracuseStep 1167365 = 218881) (by norm_num)
theorem B872473 : Blo 774336 872473 := bbase (se 2 (by rfl) ⟨327177, by rfl⟩ : syracuseStep 872473 = 654355) (by norm_num)
theorem B1167389 : Blo 774336 1167389 := bbase (se 3 (by rfl) ⟨218885, by rfl⟩ : syracuseStep 1167389 = 437771) (by norm_num)
theorem B3723317 : Blo 774336 3723317 := bbase (se 5 (by rfl) ⟨174530, by rfl⟩ : syracuseStep 3723317 = 349061) (by norm_num)
theorem B1167413 : Blo 774336 1167413 := bbase (se 5 (by rfl) ⟨54722, by rfl⟩ : syracuseStep 1167413 = 109445) (by norm_num)
theorem B872509 : Blo 774336 872509 := bbase (se 3 (by rfl) ⟨163595, by rfl⟩ : syracuseStep 872509 = 327191) (by norm_num)
theorem B1167437 : Blo 774336 1167437 := bbase (se 3 (by rfl) ⟨218894, by rfl⟩ : syracuseStep 1167437 = 437789) (by norm_num)
theorem B872545 : Blo 774336 872545 := bbase (se 2 (by rfl) ⟨327204, by rfl⟩ : syracuseStep 872545 = 654409) (by norm_num)
theorem B1167461 : Blo 774336 1167461 := bbase (se 4 (by rfl) ⟨109449, by rfl⟩ : syracuseStep 1167461 = 218899) (by norm_num)
theorem B1167485 : Blo 774336 1167485 := bbase (se 3 (by rfl) ⟨218903, by rfl⟩ : syracuseStep 1167485 = 437807) (by norm_num)
theorem B872581 : Blo 774336 872581 := bbase (se 4 (by rfl) ⟨81804, by rfl⟩ : syracuseStep 872581 = 163609) (by norm_num)
theorem B2216069 : Blo 774336 2216069 := bbase (se 4 (by rfl) ⟨207756, by rfl⟩ : syracuseStep 2216069 = 415513) (by norm_num)
theorem B1659037 : Blo 774336 1659037 := bbase (se 3 (by rfl) ⟨311069, by rfl⟩ : syracuseStep 1659037 = 622139) (by norm_num)
theorem B872617 : Blo 774336 872617 := bbase (se 2 (by rfl) ⟨327231, by rfl⟩ : syracuseStep 872617 = 654463) (by norm_num)
theorem B872653 : Blo 774336 872653 := bbase (se 3 (by rfl) ⟨163622, by rfl⟩ : syracuseStep 872653 = 327245) (by norm_num)
theorem B872689 : Blo 774336 872689 := bbase (se 2 (by rfl) ⟨327258, by rfl⟩ : syracuseStep 872689 = 654517) (by norm_num)
theorem B872725 : Blo 774336 872725 := bbase (se 6 (by rfl) ⟨20454, by rfl⟩ : syracuseStep 872725 = 40909) (by norm_num)
theorem B1397045 : Blo 774336 1397045 := bbase (se 5 (by rfl) ⟨65486, by rfl⟩ : syracuseStep 1397045 = 130973) (by norm_num)
theorem B872761 : Blo 774336 872761 := bbase (se 2 (by rfl) ⟨327285, by rfl⟩ : syracuseStep 872761 = 654571) (by norm_num)
theorem B872797 : Blo 774336 872797 := bbase (se 3 (by rfl) ⟨163649, by rfl⟩ : syracuseStep 872797 = 327299) (by norm_num)
theorem B872833 : Blo 774336 872833 := bbase (se 2 (by rfl) ⟨327312, by rfl⟩ : syracuseStep 872833 = 654625) (by norm_num)
theorem B872869 : Blo 774336 872869 := bbase (se 4 (by rfl) ⟨81831, by rfl⟩ : syracuseStep 872869 = 163663) (by norm_num)
theorem B872905 : Blo 774336 872905 := bbase (se 2 (by rfl) ⟨327339, by rfl⟩ : syracuseStep 872905 = 654679) (by norm_num)
theorem B1888717 : Blo 774336 1888717 := bbase (se 3 (by rfl) ⟨354134, by rfl⟩ : syracuseStep 1888717 = 708269) (by norm_num)
theorem B872941 : Blo 774336 872941 := bbase (se 3 (by rfl) ⟨163676, by rfl⟩ : syracuseStep 872941 = 327353) (by norm_num)
theorem B872977 : Blo 774336 872977 := bbase (se 2 (by rfl) ⟨327366, by rfl⟩ : syracuseStep 872977 = 654733) (by norm_num)
theorem B873013 : Blo 774336 873013 := bbase (se 5 (by rfl) ⟨40922, by rfl⟩ : syracuseStep 873013 = 81845) (by norm_num)
theorem B873049 : Blo 774336 873049 := bbase (se 2 (by rfl) ⟨327393, by rfl⟩ : syracuseStep 873049 = 654787) (by norm_num)
theorem B873085 : Blo 774336 873085 := bbase (se 3 (by rfl) ⟨163703, by rfl⟩ : syracuseStep 873085 = 327407) (by norm_num)
theorem B1659541 : Blo 774336 1659541 := bbase (se 6 (by rfl) ⟨38895, by rfl⟩ : syracuseStep 1659541 = 77791) (by norm_num)
theorem B873121 : Blo 774336 873121 := bbase (se 2 (by rfl) ⟨327420, by rfl⟩ : syracuseStep 873121 = 654841) (by norm_num)
theorem B873157 : Blo 774336 873157 := bbase (se 4 (by rfl) ⟨81858, by rfl⟩ : syracuseStep 873157 = 163717) (by norm_num)
theorem B9425621 : Blo 774336 9425621 := bbase (se 7 (by rfl) ⟨110456, by rfl⟩ : syracuseStep 9425621 = 220913) (by norm_num)
theorem B873193 : Blo 774336 873193 := bbase (se 2 (by rfl) ⟨327447, by rfl⟩ : syracuseStep 873193 = 654895) (by norm_num)
theorem B873229 : Blo 774336 873229 := bbase (se 3 (by rfl) ⟨163730, by rfl⟩ : syracuseStep 873229 = 327461) (by norm_num)
theorem B1495829 : Blo 774336 1495829 := bbase (se 6 (by rfl) ⟨35058, by rfl⟩ : syracuseStep 1495829 = 70117) (by norm_num)
theorem B873265 : Blo 774336 873265 := bbase (se 2 (by rfl) ⟨327474, by rfl⟩ : syracuseStep 873265 = 654949) (by norm_num)
theorem B873301 : Blo 774336 873301 := bbase (se 9 (by rfl) ⟨2558, by rfl⟩ : syracuseStep 873301 = 5117) (by norm_num)
theorem B873337 : Blo 774336 873337 := bbase (se 2 (by rfl) ⟨327501, by rfl⟩ : syracuseStep 873337 = 655003) (by norm_num)
theorem B873373 : Blo 774336 873373 := bbase (se 3 (by rfl) ⟨163757, by rfl⟩ : syracuseStep 873373 = 327515) (by norm_num)
theorem B873409 : Blo 774336 873409 := bbase (se 2 (by rfl) ⟨327528, by rfl⟩ : syracuseStep 873409 = 655057) (by norm_num)
theorem B873445 : Blo 774336 873445 := bbase (se 4 (by rfl) ⟨81885, by rfl⟩ : syracuseStep 873445 = 163771) (by norm_num)
theorem B3920885 : Blo 774336 3920885 := bbase (se 5 (by rfl) ⟨183791, by rfl⟩ : syracuseStep 3920885 = 367583) (by norm_num)
theorem B873481 : Blo 774336 873481 := bbase (se 2 (by rfl) ⟨327555, by rfl⟩ : syracuseStep 873481 = 655111) (by norm_num)
theorem B873517 : Blo 774336 873517 := bbase (se 3 (by rfl) ⟨163784, by rfl⟩ : syracuseStep 873517 = 327569) (by norm_num)
theorem B1102909 : Blo 774336 1102909 := bbase (se 3 (by rfl) ⟨206795, by rfl⟩ : syracuseStep 1102909 = 413591) (by norm_num)
theorem B873553 : Blo 774336 873553 := bbase (se 2 (by rfl) ⟨327582, by rfl⟩ : syracuseStep 873553 = 655165) (by norm_num)
theorem B4412501 : Blo 774336 4412501 := bbase (se 8 (by rfl) ⟨25854, by rfl⟩ : syracuseStep 4412501 = 51709) (by norm_num)
theorem B873589 : Blo 774336 873589 := bbase (se 5 (by rfl) ⟨40949, by rfl⟩ : syracuseStep 873589 = 81899) (by norm_num)
theorem B873625 : Blo 774336 873625 := bbase (se 2 (by rfl) ⟨327609, by rfl⟩ : syracuseStep 873625 = 655219) (by norm_num)
theorem B873661 : Blo 774336 873661 := bbase (se 3 (by rfl) ⟨163811, by rfl⟩ : syracuseStep 873661 = 327623) (by norm_num)
theorem B873697 : Blo 774336 873697 := bbase (se 2 (by rfl) ⟨327636, by rfl⟩ : syracuseStep 873697 = 655273) (by norm_num)
theorem B1397989 : Blo 774336 1397989 := bbase (se 4 (by rfl) ⟨131061, by rfl⟩ : syracuseStep 1397989 = 262123) (by norm_num)
theorem B873733 : Blo 774336 873733 := bbase (se 4 (by rfl) ⟨81912, by rfl⟩ : syracuseStep 873733 = 163825) (by norm_num)
theorem B840989 : Blo 774336 840989 := bbase (se 3 (by rfl) ⟨157685, by rfl⟩ : syracuseStep 840989 = 315371) (by norm_num)
theorem B873769 : Blo 774336 873769 := bbase (se 2 (by rfl) ⟨327663, by rfl⟩ : syracuseStep 873769 = 655327) (by norm_num)
theorem B873805 : Blo 774336 873805 := bbase (se 3 (by rfl) ⟨163838, by rfl⟩ : syracuseStep 873805 = 327677) (by norm_num)
theorem B873841 : Blo 774336 873841 := bbase (se 2 (by rfl) ⟨327690, by rfl⟩ : syracuseStep 873841 = 655381) (by norm_num)
theorem B873877 : Blo 774336 873877 := bbase (se 6 (by rfl) ⟨20481, by rfl⟩ : syracuseStep 873877 = 40963) (by norm_num)
theorem B873913 : Blo 774336 873913 := bbase (se 2 (by rfl) ⟨327717, by rfl⟩ : syracuseStep 873913 = 655435) (by norm_num)
theorem B873949 : Blo 774336 873949 := bbase (se 3 (by rfl) ⟨163865, by rfl⟩ : syracuseStep 873949 = 327731) (by norm_num)
theorem B873985 : Blo 774336 873985 := bbase (se 2 (by rfl) ⟨327744, by rfl⟩ : syracuseStep 873985 = 655489) (by norm_num)
theorem B1660429 : Blo 774336 1660429 := bbase (se 3 (by rfl) ⟨311330, by rfl⟩ : syracuseStep 1660429 = 622661) (by norm_num)
theorem B874021 : Blo 774336 874021 := bbase (se 4 (by rfl) ⟨81939, by rfl⟩ : syracuseStep 874021 = 163879) (by norm_num)
theorem B1791533 : Blo 774336 1791533 := bbase (se 3 (by rfl) ⟨335912, by rfl⟩ : syracuseStep 1791533 = 671825) (by norm_num)
theorem B874057 : Blo 774336 874057 := bbase (se 2 (by rfl) ⟨327771, by rfl⟩ : syracuseStep 874057 = 655543) (by norm_num)
theorem B874093 : Blo 774336 874093 := bbase (se 3 (by rfl) ⟨163892, by rfl⟩ : syracuseStep 874093 = 327785) (by norm_num)
theorem B1103501 : Blo 774336 1103501 := bbase (se 3 (by rfl) ⟨206906, by rfl⟩ : syracuseStep 1103501 = 413813) (by norm_num)
theorem B874129 : Blo 774336 874129 := bbase (se 2 (by rfl) ⟨327798, by rfl⟩ : syracuseStep 874129 = 655597) (by norm_num)
theorem B874165 : Blo 774336 874165 := bbase (se 5 (by rfl) ⟨40976, by rfl⟩ : syracuseStep 874165 = 81953) (by norm_num)
theorem B874201 : Blo 774336 874201 := bbase (se 2 (by rfl) ⟨327825, by rfl⟩ : syracuseStep 874201 = 655651) (by norm_num)
theorem B1103581 : Blo 774336 1103581 := bbase (se 3 (by rfl) ⟨206921, by rfl⟩ : syracuseStep 1103581 = 413843) (by norm_num)
theorem B1398493 : Blo 774336 1398493 := bbase (se 3 (by rfl) ⟨262217, by rfl⟩ : syracuseStep 1398493 = 524435) (by norm_num)
theorem B874237 : Blo 774336 874237 := bbase (se 3 (by rfl) ⟨163919, by rfl⟩ : syracuseStep 874237 = 327839) (by norm_num)
theorem B874273 : Blo 774336 874273 := bbase (se 2 (by rfl) ⟨327852, by rfl⟩ : syracuseStep 874273 = 655705) (by norm_num)
theorem B874309 : Blo 774336 874309 := bbase (se 4 (by rfl) ⟨81966, by rfl⟩ : syracuseStep 874309 = 163933) (by norm_num)
theorem B1103701 : Blo 774336 1103701 := bbase (se 9 (by rfl) ⟨3233, by rfl⟩ : syracuseStep 1103701 = 6467) (by norm_num)
theorem B11196245 : Blo 774336 11196245 := bbase (se 9 (by rfl) ⟨32801, by rfl⟩ : syracuseStep 11196245 = 65603) (by norm_num)
theorem B874345 : Blo 774336 874345 := bbase (se 2 (by rfl) ⟨327879, by rfl⟩ : syracuseStep 874345 = 655759) (by norm_num)
theorem B874381 : Blo 774336 874381 := bbase (se 3 (by rfl) ⟨163946, by rfl⟩ : syracuseStep 874381 = 327893) (by norm_num)
theorem B874417 : Blo 774336 874417 := bbase (se 2 (by rfl) ⟨327906, by rfl⟩ : syracuseStep 874417 = 655813) (by norm_num)
theorem B1103797 : Blo 774336 1103797 := bbase (se 5 (by rfl) ⟨51740, by rfl⟩ : syracuseStep 1103797 = 103481) (by norm_num)
theorem B841681 : Blo 774336 841681 := bbase (se 2 (by rfl) ⟨315630, by rfl⟩ : syracuseStep 841681 = 631261) (by norm_num)
theorem B874453 : Blo 774336 874453 := bbase (se 7 (by rfl) ⟨10247, by rfl⟩ : syracuseStep 874453 = 20495) (by norm_num)
theorem B874489 : Blo 774336 874489 := bbase (se 2 (by rfl) ⟨327933, by rfl⟩ : syracuseStep 874489 = 655867) (by norm_num)
theorem B1660925 : Blo 774336 1660925 := bbase (se 3 (by rfl) ⟨311423, by rfl⟩ : syracuseStep 1660925 = 622847) (by norm_num)
theorem B874525 : Blo 774336 874525 := bbase (se 3 (by rfl) ⟨163973, by rfl⟩ : syracuseStep 874525 = 327947) (by norm_num)
theorem B874561 : Blo 774336 874561 := bbase (se 2 (by rfl) ⟨327960, by rfl⟩ : syracuseStep 874561 = 655921) (by norm_num)
theorem B874597 : Blo 774336 874597 := bbase (se 4 (by rfl) ⟨81993, by rfl⟩ : syracuseStep 874597 = 163987) (by norm_num)
theorem B874633 : Blo 774336 874633 := bbase (se 2 (by rfl) ⟨327987, by rfl⟩ : syracuseStep 874633 = 655975) (by norm_num)
theorem B874669 : Blo 774336 874669 := bbase (se 3 (by rfl) ⟨164000, by rfl⟩ : syracuseStep 874669 = 328001) (by norm_num)
theorem B3725509 : Blo 774336 3725509 := bbase (se 4 (by rfl) ⟨349266, by rfl⟩ : syracuseStep 3725509 = 698533) (by norm_num)
theorem B874705 : Blo 774336 874705 := bbase (se 2 (by rfl) ⟨328014, by rfl⟩ : syracuseStep 874705 = 656029) (by norm_num)
theorem B874741 : Blo 774336 874741 := bbase (se 5 (by rfl) ⟨41003, by rfl⟩ : syracuseStep 874741 = 82007) (by norm_num)
theorem B3922181 : Blo 774336 3922181 := bbase (se 4 (by rfl) ⟨367704, by rfl⟩ : syracuseStep 3922181 = 735409) (by norm_num)
theorem B874777 : Blo 774336 874777 := bbase (se 2 (by rfl) ⟨328041, by rfl⟩ : syracuseStep 874777 = 656083) (by norm_num)
theorem B874813 : Blo 774336 874813 := bbase (se 3 (by rfl) ⟨164027, by rfl⟩ : syracuseStep 874813 = 328055) (by norm_num)
theorem B874849 : Blo 774336 874849 := bbase (se 2 (by rfl) ⟨328068, by rfl⟩ : syracuseStep 874849 = 656137) (by norm_num)
theorem B874885 : Blo 774336 874885 := bbase (se 4 (by rfl) ⟨82020, by rfl⟩ : syracuseStep 874885 = 164041) (by norm_num)
theorem B1104293 : Blo 774336 1104293 := bbase (se 4 (by rfl) ⟨103527, by rfl⟩ : syracuseStep 1104293 = 207055) (by norm_num)
theorem B874921 : Blo 774336 874921 := bbase (se 2 (by rfl) ⟨328095, by rfl⟩ : syracuseStep 874921 = 656191) (by norm_num)
theorem B874957 : Blo 774336 874957 := bbase (se 3 (by rfl) ⟨164054, by rfl⟩ : syracuseStep 874957 = 328109) (by norm_num)
theorem B874993 : Blo 774336 874993 := bbase (se 2 (by rfl) ⟨328122, by rfl⟩ : syracuseStep 874993 = 656245) (by norm_num)
theorem B875029 : Blo 774336 875029 := bbase (se 6 (by rfl) ⟨20508, by rfl⟩ : syracuseStep 875029 = 41017) (by norm_num)
theorem B875065 : Blo 774336 875065 := bbase (se 2 (by rfl) ⟨328149, by rfl⟩ : syracuseStep 875065 = 656299) (by norm_num)
theorem B1399373 : Blo 774336 1399373 := bbase (se 3 (by rfl) ⟨262382, by rfl⟩ : syracuseStep 1399373 = 524765) (by norm_num)
theorem B875101 : Blo 774336 875101 := bbase (se 3 (by rfl) ⟨164081, by rfl⟩ : syracuseStep 875101 = 328163) (by norm_num)
theorem B875137 : Blo 774336 875137 := bbase (se 2 (by rfl) ⟨328176, by rfl⟩ : syracuseStep 875137 = 656353) (by norm_num)
theorem B875173 : Blo 774336 875173 := bbase (se 4 (by rfl) ⟨82047, by rfl⟩ : syracuseStep 875173 = 164095) (by norm_num)
theorem B875209 : Blo 774336 875209 := bbase (se 2 (by rfl) ⟨328203, by rfl⟩ : syracuseStep 875209 = 656407) (by norm_num)
theorem B875245 : Blo 774336 875245 := bbase (se 3 (by rfl) ⟨164108, by rfl⟩ : syracuseStep 875245 = 328217) (by norm_num)
theorem B875281 : Blo 774336 875281 := bbase (se 2 (by rfl) ⟨328230, by rfl⟩ : syracuseStep 875281 = 656461) (by norm_num)
theorem B875317 : Blo 774336 875317 := bbase (se 5 (by rfl) ⟨41030, by rfl⟩ : syracuseStep 875317 = 82061) (by norm_num)
theorem B875353 : Blo 774336 875353 := bbase (se 2 (by rfl) ⟨328257, by rfl⟩ : syracuseStep 875353 = 656515) (by norm_num)
theorem B1661813 : Blo 774336 1661813 := bbase (se 5 (by rfl) ⟨77897, by rfl⟩ : syracuseStep 1661813 = 155795) (by norm_num)
theorem B875389 : Blo 774336 875389 := bbase (se 3 (by rfl) ⟨164135, by rfl⟩ : syracuseStep 875389 = 328271) (by norm_num)
theorem B875425 : Blo 774336 875425 := bbase (se 2 (by rfl) ⟨328284, by rfl⟩ : syracuseStep 875425 = 656569) (by norm_num)
theorem B875461 : Blo 774336 875461 := bbase (se 4 (by rfl) ⟨82074, by rfl⟩ : syracuseStep 875461 = 164149) (by norm_num)
theorem B1104845 : Blo 774336 1104845 := bbase (se 3 (by rfl) ⟨207158, by rfl⟩ : syracuseStep 1104845 = 414317) (by norm_num)
theorem B875497 : Blo 774336 875497 := bbase (se 2 (by rfl) ⟨328311, by rfl⟩ : syracuseStep 875497 = 656623) (by norm_num)
theorem B1661933 : Blo 774336 1661933 := bbase (se 3 (by rfl) ⟨311612, by rfl⟩ : syracuseStep 1661933 = 623225) (by norm_num)
theorem B875533 : Blo 774336 875533 := bbase (se 3 (by rfl) ⟨164162, by rfl⟩ : syracuseStep 875533 = 328325) (by norm_num)
theorem B875569 : Blo 774336 875569 := bbase (se 2 (by rfl) ⟨328338, by rfl⟩ : syracuseStep 875569 = 656677) (by norm_num)
theorem B1399877 : Blo 774336 1399877 := bbase (se 4 (by rfl) ⟨131238, by rfl⟩ : syracuseStep 1399877 = 262477) (by norm_num)
theorem B875605 : Blo 774336 875605 := bbase (se 8 (by rfl) ⟨5130, by rfl⟩ : syracuseStep 875605 = 10261) (by norm_num)
theorem B1596581 : Blo 774336 1596581 := bbase (se 4 (by rfl) ⟨149679, by rfl⟩ : syracuseStep 1596581 = 299359) (by norm_num)
theorem B7462165 : Blo 774336 7462165 := bbase (se 6 (by rfl) ⟨174894, by rfl⟩ : syracuseStep 7462165 = 349789) (by norm_num)
theorem B5037461 : Blo 774336 5037461 := bbase (se 6 (by rfl) ⟨118065, by rfl⟩ : syracuseStep 5037461 = 236131) (by norm_num)
theorem B2940421 : Blo 774336 2940421 := bbase (se 4 (by rfl) ⟨275664, by rfl⟩ : syracuseStep 2940421 = 551329) (by norm_num)
theorem B3988997 : Blo 774336 3988997 := bbase (se 4 (by rfl) ⟨373968, by rfl⟩ : syracuseStep 3988997 = 747937) (by norm_num)
theorem B3923477 : Blo 774336 3923477 := bbase (se 6 (by rfl) ⟨91956, by rfl⟩ : syracuseStep 3923477 = 183913) (by norm_num)
theorem B1531469 : Blo 774336 1531469 := bbase (se 3 (by rfl) ⟨287150, by rfl⟩ : syracuseStep 1531469 = 574301) (by norm_num)
theorem B1105597 : Blo 774336 1105597 := bbase (se 3 (by rfl) ⟨207299, by rfl⟩ : syracuseStep 1105597 = 414599) (by norm_num)
theorem B2940725 : Blo 774336 2940725 := bbase (se 5 (by rfl) ⟨137846, by rfl⟩ : syracuseStep 2940725 = 275693) (by norm_num)
theorem B1892165 : Blo 774336 1892165 := bbase (se 4 (by rfl) ⟨177390, by rfl⟩ : syracuseStep 1892165 = 354781) (by norm_num)
theorem B1990885 : Blo 774336 1990885 := bbase (se 4 (by rfl) ⟨186645, by rfl⟩ : syracuseStep 1990885 = 373291) (by norm_num)
theorem B2613653 : Blo 774336 2613653 := bbase (se 6 (by rfl) ⟨61257, by rfl⟩ : syracuseStep 2613653 = 122515) (by norm_num)
theorem B1106389 : Blo 774336 1106389 := bbase (se 7 (by rfl) ⟨12965, by rfl⟩ : syracuseStep 1106389 = 25931) (by norm_num)
theorem B5890805 : Blo 774336 5890805 := bbase (se 5 (by rfl) ⟨276131, by rfl⟩ : syracuseStep 5890805 = 552263) (by norm_num)
theorem B3924773 : Blo 774336 3924773 := bbase (se 4 (by rfl) ⟨367947, by rfl⟩ : syracuseStep 3924773 = 735895) (by norm_num)
theorem B1106725 : Blo 774336 1106725 := bbase (se 4 (by rfl) ⟨103755, by rfl⟩ : syracuseStep 1106725 = 207511) (by norm_num)
theorem B2614085 : Blo 774336 2614085 := bbase (se 4 (by rfl) ⟨245070, by rfl⟩ : syracuseStep 2614085 = 490141) (by norm_num)
theorem B1106941 : Blo 774336 1106941 := bbase (se 3 (by rfl) ⟨207551, by rfl⟩ : syracuseStep 1106941 = 415103) (by norm_num)
theorem B2483237 : Blo 774336 2483237 := bbase (se 4 (by rfl) ⟨232803, by rfl⟩ : syracuseStep 2483237 = 465607) (by norm_num)
theorem B1402069 : Blo 774336 1402069 := bbase (se 7 (by rfl) ⟨16430, by rfl⟩ : syracuseStep 1402069 = 32861) (by norm_num)
theorem B2614517 : Blo 774336 2614517 := bbase (se 5 (by rfl) ⟨122555, by rfl⟩ : syracuseStep 2614517 = 245111) (by norm_num)
theorem B1598717 : Blo 774336 1598717 := bbase (se 3 (by rfl) ⟨299759, by rfl⟩ : syracuseStep 1598717 = 599519) (by norm_num)
theorem B2123029 : Blo 774336 2123029 := bbase (se 6 (by rfl) ⟨49758, by rfl⟩ : syracuseStep 2123029 = 99517) (by norm_num)
theorem B3368213 : Blo 774336 3368213 := bbase (se 6 (by rfl) ⟨78942, by rfl⟩ : syracuseStep 3368213 = 157885) (by norm_num)
theorem B1107317 : Blo 774336 1107317 := bbase (se 5 (by rfl) ⟨51905, by rfl⟩ : syracuseStep 1107317 = 103811) (by norm_num)
theorem B2614949 : Blo 774336 2614949 := bbase (se 4 (by rfl) ⟨245151, by rfl⟩ : syracuseStep 2614949 = 490303) (by norm_num)
theorem B1009441 : Blo 774336 1009441 := bbase (se 2 (by rfl) ⟨378540, by rfl⟩ : syracuseStep 1009441 = 757081) (by norm_num)
theorem B2942837 : Blo 774336 2942837 := bbase (se 5 (by rfl) ⟨137945, by rfl⟩ : syracuseStep 2942837 = 275891) (by norm_num)
theorem B14378965 : Blo 774336 14378965 := bbase (se 7 (by rfl) ⟨168503, by rfl⟩ : syracuseStep 14378965 = 337007) (by norm_num)
theorem B2517013 : Blo 774336 2517013 := bbase (se 6 (by rfl) ⟨58992, by rfl⟩ : syracuseStep 2517013 = 117985) (by norm_num)
theorem B3926069 : Blo 774336 3926069 := bbase (se 5 (by rfl) ⟨184034, by rfl⟩ : syracuseStep 3926069 = 368069) (by norm_num)
theorem B2615381 : Blo 774336 2615381 := bbase (se 8 (by rfl) ⟨15324, by rfl⟩ : syracuseStep 2615381 = 30649) (by norm_num)
theorem B3729509 : Blo 774336 3729509 := bbase (se 4 (by rfl) ⟨349641, by rfl⟩ : syracuseStep 3729509 = 699283) (by norm_num)
theorem B2943125 : Blo 774336 2943125 := bbase (se 6 (by rfl) ⟨68979, by rfl⟩ : syracuseStep 2943125 = 137959) (by norm_num)
theorem B1960109 : Blo 774336 1960109 := bbase (se 3 (by rfl) ⟨367520, by rfl⟩ : syracuseStep 1960109 = 735041) (by norm_num)
theorem B1894661 : Blo 774336 1894661 := bbase (se 4 (by rfl) ⟨177624, by rfl⟩ : syracuseStep 1894661 = 355249) (by norm_num)
theorem B1861957 : Blo 774336 1861957 := bbase (se 4 (by rfl) ⟨174558, by rfl⟩ : syracuseStep 1861957 = 349117) (by norm_num)
theorem B1960301 : Blo 774336 1960301 := bbase (se 3 (by rfl) ⟨367556, by rfl⟩ : syracuseStep 1960301 = 735113) (by norm_num)
theorem B1010161 : Blo 774336 1010161 := bbase (se 2 (by rfl) ⟨378810, by rfl⟩ : syracuseStep 1010161 = 757621) (by norm_num)
theorem B2615813 : Blo 774336 2615813 := bbase (se 4 (by rfl) ⟨245232, by rfl⟩ : syracuseStep 2615813 = 490465) (by norm_num)
theorem B2517637 : Blo 774336 2517637 := bbase (se 4 (by rfl) ⟨236028, by rfl⟩ : syracuseStep 2517637 = 472057) (by norm_num)
theorem B1960645 : Blo 774336 1960645 := bbase (se 4 (by rfl) ⟨183810, by rfl⟩ : syracuseStep 1960645 = 367621) (by norm_num)
theorem B1960757 : Blo 774336 1960757 := bbase (se 5 (by rfl) ⟨91910, by rfl⟩ : syracuseStep 1960757 = 183821) (by norm_num)
theorem B2616245 : Blo 774336 2616245 := bbase (se 5 (by rfl) ⟨122636, by rfl⟩ : syracuseStep 2616245 = 245273) (by norm_num)
theorem B1862621 : Blo 774336 1862621 := bbase (se 3 (by rfl) ⟨349241, by rfl⟩ : syracuseStep 1862621 = 698483) (by norm_num)
theorem B1960949 : Blo 774336 1960949 := bbase (se 5 (by rfl) ⟨91919, by rfl⟩ : syracuseStep 1960949 = 183839) (by norm_num)
theorem B945265 : Blo 774336 945265 := bbase (se 2 (by rfl) ⟨354474, by rfl⟩ : syracuseStep 945265 = 708949) (by norm_num)
theorem B1862909 : Blo 774336 1862909 := bbase (se 3 (by rfl) ⟨349295, by rfl⟩ : syracuseStep 1862909 = 698591) (by norm_num)
theorem B2944309 : Blo 774336 2944309 := bbase (se 5 (by rfl) ⟨138014, by rfl⟩ : syracuseStep 2944309 = 276029) (by norm_num)
theorem B3927365 : Blo 774336 3927365 := bbase (se 4 (by rfl) ⟨368190, by rfl⟩ : syracuseStep 3927365 = 736381) (by norm_num)
theorem B1961293 : Blo 774336 1961293 := bbase (se 3 (by rfl) ⟨367742, by rfl⟩ : syracuseStep 1961293 = 735485) (by norm_num)
theorem B2616677 : Blo 774336 2616677 := bbase (se 4 (by rfl) ⟨245313, by rfl⟩ : syracuseStep 2616677 = 490627) (by norm_num)
theorem B1961405 : Blo 774336 1961405 := bbase (se 3 (by rfl) ⟨367763, by rfl⟩ : syracuseStep 1961405 = 735527) (by norm_num)
theorem B1240517 : Blo 774336 1240517 := bbase (se 4 (by rfl) ⟨116298, by rfl⟩ : syracuseStep 1240517 = 232597) (by norm_num)
theorem B945605 : Blo 774336 945605 := bbase (se 4 (by rfl) ⟨88650, by rfl⟩ : syracuseStep 945605 = 177301) (by norm_num)
theorem B2944613 : Blo 774336 2944613 := bbase (se 4 (by rfl) ⟨276057, by rfl⟩ : syracuseStep 2944613 = 552115) (by norm_num)
theorem B1961597 : Blo 774336 1961597 := bbase (se 3 (by rfl) ⟨367799, by rfl⟩ : syracuseStep 1961597 = 735599) (by norm_num)
theorem B1535645 : Blo 774336 1535645 := bbase (se 3 (by rfl) ⟨287933, by rfl⟩ : syracuseStep 1535645 = 575867) (by norm_num)
theorem B2617109 : Blo 774336 2617109 := bbase (se 6 (by rfl) ⟨61338, by rfl⟩ : syracuseStep 2617109 = 122677) (by norm_num)
theorem B1240901 : Blo 774336 1240901 := bbase (se 4 (by rfl) ⟨116334, by rfl⟩ : syracuseStep 1240901 = 232669) (by norm_num)
theorem B1470325 : Blo 774336 1470325 := bbase (se 5 (by rfl) ⟨68921, by rfl⟩ : syracuseStep 1470325 = 137843) (by norm_num)
theorem B1241029 : Blo 774336 1241029 := bbase (se 4 (by rfl) ⟨116346, by rfl⟩ : syracuseStep 1241029 = 232693) (by norm_num)
theorem B1961941 : Blo 774336 1961941 := bbase (se 7 (by rfl) ⟨22991, by rfl⟩ : syracuseStep 1961941 = 45983) (by norm_num)
theorem B1470469 : Blo 774336 1470469 := bbase (se 4 (by rfl) ⟨137856, by rfl⟩ : syracuseStep 1470469 = 275713) (by norm_num)
theorem B1962053 : Blo 774336 1962053 := bbase (se 4 (by rfl) ⟨183942, by rfl⟩ : syracuseStep 1962053 = 367885) (by norm_num)
theorem B1470629 : Blo 774336 1470629 := bbase (se 4 (by rfl) ⟨137871, by rfl⟩ : syracuseStep 1470629 = 275743) (by norm_num)
theorem B1306813 : Blo 774336 1306813 := bbase (se 3 (by rfl) ⟨245027, by rfl⟩ : syracuseStep 1306813 = 490055) (by norm_num)
theorem B2617541 : Blo 774336 2617541 := bbase (se 4 (by rfl) ⟨245394, by rfl⟩ : syracuseStep 2617541 = 490789) (by norm_num)
theorem B1962245 : Blo 774336 1962245 := bbase (se 4 (by rfl) ⟨183960, by rfl⟩ : syracuseStep 1962245 = 367921) (by norm_num)
theorem B1306901 : Blo 774336 1306901 := bbase (se 6 (by rfl) ⟨30630, by rfl⟩ : syracuseStep 1306901 = 61261) (by norm_num)
theorem B9957653 : Blo 774336 9957653 := bbase (se 6 (by rfl) ⟨233382, by rfl⟩ : syracuseStep 9957653 = 466765) (by norm_num)
theorem B1470773 : Blo 774336 1470773 := bbase (se 5 (by rfl) ⟨68942, by rfl⟩ : syracuseStep 1470773 = 137885) (by norm_num)
theorem B3535157 : Blo 774336 3535157 := bbase (se 5 (by rfl) ⟨165710, by rfl⟩ : syracuseStep 3535157 = 331421) (by norm_num)
theorem B1307029 : Blo 774336 1307029 := bbase (se 6 (by rfl) ⟨30633, by rfl⟩ : syracuseStep 1307029 = 61267) (by norm_num)
theorem B2355605 : Blo 774336 2355605 := bbase (se 6 (by rfl) ⟨55209, by rfl⟩ : syracuseStep 2355605 = 110419) (by norm_num)
theorem B1307117 : Blo 774336 1307117 := bbase (se 3 (by rfl) ⟨245084, by rfl⟩ : syracuseStep 1307117 = 490169) (by norm_num)
theorem B1471061 : Blo 774336 1471061 := bbase (se 8 (by rfl) ⟨8619, by rfl⟩ : syracuseStep 1471061 = 17239) (by norm_num)
theorem B3928661 : Blo 774336 3928661 := bbase (se 8 (by rfl) ⟨23019, by rfl⟩ : syracuseStep 3928661 = 46039) (by norm_num)
theorem B1962589 : Blo 774336 1962589 := bbase (se 3 (by rfl) ⟨367985, by rfl⟩ : syracuseStep 1962589 = 735971) (by norm_num)
theorem B1307245 : Blo 774336 1307245 := bbase (se 3 (by rfl) ⟨245108, by rfl⟩ : syracuseStep 1307245 = 490217) (by norm_num)
theorem B2617973 : Blo 774336 2617973 := bbase (se 5 (by rfl) ⟨122717, by rfl⟩ : syracuseStep 2617973 = 245435) (by norm_num)
theorem B1307333 : Blo 774336 1307333 := bbase (se 4 (by rfl) ⟨122562, by rfl⟩ : syracuseStep 1307333 = 245125) (by norm_num)
theorem B1962701 : Blo 774336 1962701 := bbase (se 3 (by rfl) ⟨368006, by rfl⟩ : syracuseStep 1962701 = 736013) (by norm_num)
theorem B1471213 : Blo 774336 1471213 := bbase (se 3 (by rfl) ⟨275852, by rfl⟩ : syracuseStep 1471213 = 551705) (by norm_num)
theorem B2487029 : Blo 774336 2487029 := bbase (se 5 (by rfl) ⟨116579, by rfl⟩ : syracuseStep 2487029 = 233159) (by norm_num)
theorem B1766165 : Blo 774336 1766165 := bbase (se 6 (by rfl) ⟨41394, by rfl⟩ : syracuseStep 1766165 = 82789) (by norm_num)
theorem B1307461 : Blo 774336 1307461 := bbase (se 4 (by rfl) ⟨122574, by rfl⟩ : syracuseStep 1307461 = 245149) (by norm_num)
theorem B5665621 : Blo 774336 5665621 := bbase (se 9 (by rfl) ⟨16598, by rfl⟩ : syracuseStep 5665621 = 33197) (by norm_num)
theorem B1962893 : Blo 774336 1962893 := bbase (se 3 (by rfl) ⟨368042, by rfl⟩ : syracuseStep 1962893 = 736085) (by norm_num)
theorem B1307549 : Blo 774336 1307549 := bbase (se 3 (by rfl) ⟨245165, by rfl⟩ : syracuseStep 1307549 = 490331) (by norm_num)
theorem B1700765 : Blo 774336 1700765 := bbase (se 3 (by rfl) ⟨318893, by rfl⟩ : syracuseStep 1700765 = 637787) (by norm_num)
theorem B1242029 : Blo 774336 1242029 := bbase (se 3 (by rfl) ⟨232880, by rfl⟩ : syracuseStep 1242029 = 465761) (by norm_num)
theorem B4420565 : Blo 774336 4420565 := bbase (se 7 (by rfl) ⟨51803, by rfl⟩ : syracuseStep 4420565 = 103607) (by norm_num)
theorem B1307677 : Blo 774336 1307677 := bbase (se 3 (by rfl) ⟨245189, by rfl⟩ : syracuseStep 1307677 = 490379) (by norm_num)
theorem B1471517 : Blo 774336 1471517 := bbase (se 3 (by rfl) ⟨275909, by rfl⟩ : syracuseStep 1471517 = 551819) (by norm_num)
theorem B2618405 : Blo 774336 2618405 := bbase (se 4 (by rfl) ⟨245475, by rfl⟩ : syracuseStep 2618405 = 490951) (by norm_num)
theorem B1242157 : Blo 774336 1242157 := bbase (se 3 (by rfl) ⟨232904, by rfl⟩ : syracuseStep 1242157 = 465809) (by norm_num)
theorem B980029 : Blo 774336 980029 := bbase (se 3 (by rfl) ⟨183755, by rfl⟩ : syracuseStep 980029 = 367511) (by norm_num)
theorem B4977749 : Blo 774336 4977749 := bbase (se 8 (by rfl) ⟨29166, by rfl⟩ : syracuseStep 4977749 = 58333) (by norm_num)
theorem B1307765 : Blo 774336 1307765 := bbase (se 5 (by rfl) ⟨61301, by rfl⟩ : syracuseStep 1307765 = 122603) (by norm_num)
theorem B2126965 : Blo 774336 2126965 := bbase (se 5 (by rfl) ⟨99701, by rfl⟩ : syracuseStep 2126965 = 199403) (by norm_num)
theorem B1569989 : Blo 774336 1569989 := bbase (se 4 (by rfl) ⟨147186, by rfl⟩ : syracuseStep 1569989 = 294373) (by norm_num)
theorem B1963237 : Blo 774336 1963237 := bbase (se 4 (by rfl) ⟨184053, by rfl⟩ : syracuseStep 1963237 = 368107) (by norm_num)
theorem B980201 : Blo 774336 980201 := bbase (se 2 (by rfl) ⟨367575, by rfl⟩ : syracuseStep 980201 = 735151) (by norm_num)
theorem B1307893 : Blo 774336 1307893 := bbase (se 5 (by rfl) ⟨61307, by rfl⟩ : syracuseStep 1307893 = 122615) (by norm_num)
theorem B1864957 : Blo 774336 1864957 := bbase (se 3 (by rfl) ⟨349679, by rfl⟩ : syracuseStep 1864957 = 699359) (by norm_num)
theorem B1570061 : Blo 774336 1570061 := bbase (se 3 (by rfl) ⟨294386, by rfl⟩ : syracuseStep 1570061 = 588773) (by norm_num)
theorem B980257 : Blo 774336 980257 := bbase (se 2 (by rfl) ⟨367596, by rfl⟩ : syracuseStep 980257 = 735193) (by norm_num)
theorem B1307981 : Blo 774336 1307981 := bbase (se 3 (by rfl) ⟨245246, by rfl⟩ : syracuseStep 1307981 = 490493) (by norm_num)
theorem B9925973 : Blo 774336 9925973 := bbase (se 13 (by rfl) ⟨1817, by rfl⟩ : syracuseStep 9925973 = 3635) (by norm_num)
theorem B1963349 : Blo 774336 1963349 := bbase (se 13 (by rfl) ⟨359, by rfl⟩ : syracuseStep 1963349 = 719) (by norm_num)
theorem B980353 : Blo 774336 980353 := bbase (se 2 (by rfl) ⟨367632, by rfl⟩ : syracuseStep 980353 = 735265) (by norm_num)
theorem B1242541 : Blo 774336 1242541 := bbase (se 3 (by rfl) ⟨232976, by rfl⟩ : syracuseStep 1242541 = 465953) (by norm_num)
theorem B7468469 : Blo 774336 7468469 := bbase (se 5 (by rfl) ⟨350084, by rfl⟩ : syracuseStep 7468469 = 700169) (by norm_num)
theorem B1996213 : Blo 774336 1996213 := bbase (se 5 (by rfl) ⟨93572, by rfl⟩ : syracuseStep 1996213 = 187145) (by norm_num)
theorem B1308109 : Blo 774336 1308109 := bbase (se 3 (by rfl) ⟨245270, by rfl⟩ : syracuseStep 1308109 = 490541) (by norm_num)
theorem B2618837 : Blo 774336 2618837 := bbase (se 7 (by rfl) ⟨30689, by rfl⟩ : syracuseStep 2618837 = 61379) (by norm_num)
theorem B6616565 : Blo 774336 6616565 := bbase (se 5 (by rfl) ⟨310151, by rfl⟩ : syracuseStep 6616565 = 620303) (by norm_num)
theorem B1963541 : Blo 774336 1963541 := bbase (se 6 (by rfl) ⟨46020, by rfl⟩ : syracuseStep 1963541 = 92041) (by norm_num)
theorem B1308197 : Blo 774336 1308197 := bbase (se 4 (by rfl) ⟨122643, by rfl⟩ : syracuseStep 1308197 = 245287) (by norm_num)
theorem B980525 : Blo 774336 980525 := bbase (se 3 (by rfl) ⟨183848, by rfl⟩ : syracuseStep 980525 = 367697) (by norm_num)
theorem B980581 : Blo 774336 980581 := bbase (se 4 (by rfl) ⟨91929, by rfl⟩ : syracuseStep 980581 = 183859) (by norm_num)
theorem B2487941 : Blo 774336 2487941 := bbase (se 4 (by rfl) ⟨233244, by rfl⟩ : syracuseStep 2487941 = 466489) (by norm_num)
theorem B3733141 : Blo 774336 3733141 := bbase (se 6 (by rfl) ⟨87495, by rfl⟩ : syracuseStep 3733141 = 174991) (by norm_num)
theorem B1308325 : Blo 774336 1308325 := bbase (se 4 (by rfl) ⟨122655, by rfl⟩ : syracuseStep 1308325 = 245311) (by norm_num)
theorem B2946725 : Blo 774336 2946725 := bbase (se 4 (by rfl) ⟨276255, by rfl⟩ : syracuseStep 2946725 = 552511) (by norm_num)
theorem B1242797 : Blo 774336 1242797 := bbase (se 3 (by rfl) ⟨233024, by rfl⟩ : syracuseStep 1242797 = 466049) (by norm_num)
theorem B5961397 : Blo 774336 5961397 := bbase (se 5 (by rfl) ⟨279440, by rfl⟩ : syracuseStep 5961397 = 558881) (by norm_num)
theorem B6715061 : Blo 774336 6715061 := bbase (se 5 (by rfl) ⟨314768, by rfl⟩ : syracuseStep 6715061 = 629537) (by norm_num)
theorem B980677 : Blo 774336 980677 := bbase (se 4 (by rfl) ⟨91938, by rfl⟩ : syracuseStep 980677 = 183877) (by norm_num)
theorem B1570549 : Blo 774336 1570549 := bbase (se 5 (by rfl) ⟨73619, by rfl⟩ : syracuseStep 1570549 = 147239) (by norm_num)
theorem B1308413 : Blo 774336 1308413 := bbase (se 3 (by rfl) ⟨245327, by rfl⟩ : syracuseStep 1308413 = 490655) (by norm_num)
theorem B1472269 : Blo 774336 1472269 := bbase (se 3 (by rfl) ⟨276050, by rfl⟩ : syracuseStep 1472269 = 552101) (by norm_num)
theorem B3929957 : Blo 774336 3929957 := bbase (se 4 (by rfl) ⟨368433, by rfl⟩ : syracuseStep 3929957 = 736867) (by norm_num)
theorem B1963885 : Blo 774336 1963885 := bbase (se 3 (by rfl) ⟨368228, by rfl⟩ : syracuseStep 1963885 = 736457) (by norm_num)
theorem B980849 : Blo 774336 980849 := bbase (se 2 (by rfl) ⟨367818, by rfl⟩ : syracuseStep 980849 = 735637) (by norm_num)
theorem B1308541 : Blo 774336 1308541 := bbase (se 3 (by rfl) ⟨245351, by rfl⟩ : syracuseStep 1308541 = 490703) (by norm_num)
theorem B2619269 : Blo 774336 2619269 := bbase (se 4 (by rfl) ⟨245556, by rfl⟩ : syracuseStep 2619269 = 491113) (by norm_num)
theorem B1472413 : Blo 774336 1472413 := bbase (se 3 (by rfl) ⟨276077, by rfl⟩ : syracuseStep 1472413 = 552155) (by norm_num)
theorem B980905 : Blo 774336 980905 := bbase (se 2 (by rfl) ⟨367839, by rfl⟩ : syracuseStep 980905 = 735679) (by norm_num)
theorem B1767341 : Blo 774336 1767341 := bbase (se 3 (by rfl) ⟨331376, by rfl⟩ : syracuseStep 1767341 = 662753) (by norm_num)
theorem B2947013 : Blo 774336 2947013 := bbase (se 4 (by rfl) ⟨276282, by rfl⟩ : syracuseStep 2947013 = 552565) (by norm_num)
theorem B1308629 : Blo 774336 1308629 := bbase (se 7 (by rfl) ⟨15335, by rfl⟩ : syracuseStep 1308629 = 30671) (by norm_num)
theorem B1963997 : Blo 774336 1963997 := bbase (se 3 (by rfl) ⟨368249, by rfl⟩ : syracuseStep 1963997 = 736499) (by norm_num)
theorem B981001 : Blo 774336 981001 := bbase (se 2 (by rfl) ⟨367875, by rfl⟩ : syracuseStep 981001 = 735751) (by norm_num)
theorem B1046557 : Blo 774336 1046557 := bbase (se 3 (by rfl) ⟨196229, by rfl⟩ : syracuseStep 1046557 = 392459) (by norm_num)
theorem B1472573 : Blo 774336 1472573 := bbase (se 3 (by rfl) ⟨276107, by rfl⟩ : syracuseStep 1472573 = 552215) (by norm_num)
theorem B1308757 : Blo 774336 1308757 := bbase (se 8 (by rfl) ⟨7668, by rfl⟩ : syracuseStep 1308757 = 15337) (by norm_num)
theorem B1046621 : Blo 774336 1046621 := bbase (se 3 (by rfl) ⟨196241, by rfl⟩ : syracuseStep 1046621 = 392483) (by norm_num)
theorem B4421749 : Blo 774336 4421749 := bbase (se 5 (by rfl) ⟨207269, by rfl⟩ : syracuseStep 4421749 = 414539) (by norm_num)
theorem B1964189 : Blo 774336 1964189 := bbase (se 3 (by rfl) ⟨368285, by rfl⟩ : syracuseStep 1964189 = 736571) (by norm_num)
theorem B1308845 : Blo 774336 1308845 := bbase (se 3 (by rfl) ⟨245408, by rfl⟩ : syracuseStep 1308845 = 490817) (by norm_num)
theorem B981173 : Blo 774336 981173 := bbase (se 5 (by rfl) ⟨45992, by rfl⟩ : syracuseStep 981173 = 91985) (by norm_num)
theorem B1472717 : Blo 774336 1472717 := bbase (se 3 (by rfl) ⟨276134, by rfl⟩ : syracuseStep 1472717 = 552269) (by norm_num)
theorem B981229 : Blo 774336 981229 := bbase (se 3 (by rfl) ⟨183980, by rfl⟩ : syracuseStep 981229 = 367961) (by norm_num)
theorem B1308973 : Blo 774336 1308973 := bbase (se 3 (by rfl) ⟨245432, by rfl⟩ : syracuseStep 1308973 = 490865) (by norm_num)
theorem B2619701 : Blo 774336 2619701 := bbase (se 5 (by rfl) ⟨122798, by rfl⟩ : syracuseStep 2619701 = 245597) (by norm_num)
theorem B981325 : Blo 774336 981325 := bbase (se 3 (by rfl) ⟨183998, by rfl⟩ : syracuseStep 981325 = 367997) (by norm_num)
theorem B1309061 : Blo 774336 1309061 := bbase (se 4 (by rfl) ⟨122724, by rfl⟩ : syracuseStep 1309061 = 245449) (by norm_num)
theorem B1473005 : Blo 774336 1473005 := bbase (se 3 (by rfl) ⟨276188, by rfl⟩ : syracuseStep 1473005 = 552377) (by norm_num)
theorem B1964533 : Blo 774336 1964533 := bbase (se 5 (by rfl) ⟨92087, by rfl⟩ : syracuseStep 1964533 = 184175) (by norm_num)
theorem B981497 : Blo 774336 981497 := bbase (se 2 (by rfl) ⟨368061, by rfl⟩ : syracuseStep 981497 = 736123) (by norm_num)
theorem B1309189 : Blo 774336 1309189 := bbase (se 4 (by rfl) ⟨122736, by rfl⟩ : syracuseStep 1309189 = 245473) (by norm_num)
theorem B1243669 : Blo 774336 1243669 := bbase (se 6 (by rfl) ⟨29148, by rfl⟩ : syracuseStep 1243669 = 58297) (by norm_num)
theorem B981553 : Blo 774336 981553 := bbase (se 2 (by rfl) ⟨368082, by rfl⟩ : syracuseStep 981553 = 736165) (by norm_num)
theorem B1309277 : Blo 774336 1309277 := bbase (se 3 (by rfl) ⟨245489, by rfl⟩ : syracuseStep 1309277 = 490979) (by norm_num)
theorem B1964645 : Blo 774336 1964645 := bbase (se 4 (by rfl) ⟨184185, by rfl⟩ : syracuseStep 1964645 = 368371) (by norm_num)
theorem B1243765 : Blo 774336 1243765 := bbase (se 5 (by rfl) ⟨58301, by rfl⟩ : syracuseStep 1243765 = 116603) (by norm_num)
theorem B1473157 : Blo 774336 1473157 := bbase (se 4 (by rfl) ⟨138108, by rfl⟩ : syracuseStep 1473157 = 276217) (by norm_num)
theorem B981649 : Blo 774336 981649 := bbase (se 2 (by rfl) ⟨368118, by rfl⟩ : syracuseStep 981649 = 736237) (by norm_num)
theorem B1309405 : Blo 774336 1309405 := bbase (se 3 (by rfl) ⟨245513, by rfl⟩ : syracuseStep 1309405 = 491027) (by norm_num)
theorem B2620133 : Blo 774336 2620133 := bbase (se 4 (by rfl) ⟨245637, by rfl⟩ : syracuseStep 2620133 = 491275) (by norm_num)
theorem B3144437 : Blo 774336 3144437 := bbase (se 5 (by rfl) ⟨147395, by rfl⟩ : syracuseStep 3144437 = 294791) (by norm_num)
theorem B1243925 : Blo 774336 1243925 := bbase (se 6 (by rfl) ⟨29154, by rfl⟩ : syracuseStep 1243925 = 58309) (by norm_num)
theorem B1964837 : Blo 774336 1964837 := bbase (se 4 (by rfl) ⟨184203, by rfl⟩ : syracuseStep 1964837 = 368407) (by norm_num)
theorem B1309493 : Blo 774336 1309493 := bbase (se 5 (by rfl) ⟨61382, by rfl⟩ : syracuseStep 1309493 = 122765) (by norm_num)
theorem B981821 : Blo 774336 981821 := bbase (se 3 (by rfl) ⟨184091, by rfl⟩ : syracuseStep 981821 = 368183) (by norm_num)
theorem B785225 : Blo 774336 785225 := bbase (se 2 (by rfl) ⟨294459, by rfl⟩ : syracuseStep 785225 = 588919) (by norm_num)
theorem B981877 : Blo 774336 981877 := bbase (se 5 (by rfl) ⟨46025, by rfl⟩ : syracuseStep 981877 = 92051) (by norm_num)
theorem B1571717 : Blo 774336 1571717 := bbase (se 4 (by rfl) ⟨147348, by rfl⟩ : syracuseStep 1571717 = 294697) (by norm_num)
theorem B1309621 : Blo 774336 1309621 := bbase (se 5 (by rfl) ⟨61388, by rfl⟩ : syracuseStep 1309621 = 122777) (by norm_num)
theorem B1473461 : Blo 774336 1473461 := bbase (se 5 (by rfl) ⟨69068, by rfl⟩ : syracuseStep 1473461 = 138137) (by norm_num)
theorem B2489285 : Blo 774336 2489285 := bbase (se 4 (by rfl) ⟨233370, by rfl⟩ : syracuseStep 2489285 = 466741) (by norm_num)
theorem B981973 : Blo 774336 981973 := bbase (se 7 (by rfl) ⟨11507, by rfl⟩ : syracuseStep 981973 = 23015) (by norm_num)
theorem B1571813 : Blo 774336 1571813 := bbase (se 4 (by rfl) ⟨147357, by rfl⟩ : syracuseStep 1571813 = 294715) (by norm_num)
theorem B1309709 : Blo 774336 1309709 := bbase (se 3 (by rfl) ⟨245570, by rfl⟩ : syracuseStep 1309709 = 491141) (by norm_num)
theorem B883753 : Blo 774336 883753 := bbase (se 2 (by rfl) ⟨331407, by rfl⟩ : syracuseStep 883753 = 662815) (by norm_num)
theorem B2948197 : Blo 774336 2948197 := bbase (se 4 (by rfl) ⟨276393, by rfl⟩ : syracuseStep 2948197 = 552787) (by norm_num)
theorem B3931253 : Blo 774336 3931253 := bbase (se 5 (by rfl) ⟨184277, by rfl⟩ : syracuseStep 3931253 = 368555) (by norm_num)
theorem B1965181 : Blo 774336 1965181 := bbase (se 3 (by rfl) ⟨368471, by rfl⟩ : syracuseStep 1965181 = 736943) (by norm_num)
theorem B982145 : Blo 774336 982145 := bbase (se 2 (by rfl) ⟨368304, by rfl⟩ : syracuseStep 982145 = 736609) (by norm_num)
theorem B1309837 : Blo 774336 1309837 := bbase (se 3 (by rfl) ⟨245594, by rfl⟩ : syracuseStep 1309837 = 491189) (by norm_num)
theorem B2620565 : Blo 774336 2620565 := bbase (se 6 (by rfl) ⟨61419, by rfl⟩ : syracuseStep 2620565 = 122839) (by norm_num)
theorem B982201 : Blo 774336 982201 := bbase (se 2 (by rfl) ⟨368325, by rfl⟩ : syracuseStep 982201 = 736651) (by norm_num)
theorem B1309925 : Blo 774336 1309925 := bbase (se 4 (by rfl) ⟨122805, by rfl⟩ : syracuseStep 1309925 = 245611) (by norm_num)
theorem B1965293 : Blo 774336 1965293 := bbase (se 3 (by rfl) ⟨368492, by rfl⟩ : syracuseStep 1965293 = 736985) (by norm_num)
theorem B982297 : Blo 774336 982297 := bbase (se 2 (by rfl) ⟨368361, by rfl⟩ : syracuseStep 982297 = 736723) (by norm_num)
theorem B1310053 : Blo 774336 1310053 := bbase (se 4 (by rfl) ⟨122817, by rfl⟩ : syracuseStep 1310053 = 245635) (by norm_num)
theorem B785773 : Blo 774336 785773 := bbase (se 3 (by rfl) ⟨147332, by rfl⟩ : syracuseStep 785773 = 294665) (by norm_num)
theorem B2948501 : Blo 774336 2948501 := bbase (se 6 (by rfl) ⟨69105, by rfl⟩ : syracuseStep 2948501 = 138211) (by norm_num)
theorem B1047973 : Blo 774336 1047973 := bbase (se 4 (by rfl) ⟨98247, by rfl⟩ : syracuseStep 1047973 = 196495) (by norm_num)
theorem B1965485 : Blo 774336 1965485 := bbase (se 3 (by rfl) ⟨368528, by rfl⟩ : syracuseStep 1965485 = 737057) (by norm_num)
theorem B1310141 : Blo 774336 1310141 := bbase (se 3 (by rfl) ⟨245651, by rfl⟩ : syracuseStep 1310141 = 491303) (by norm_num)
theorem B982469 : Blo 774336 982469 := bbase (se 4 (by rfl) ⟨92106, by rfl⟩ : syracuseStep 982469 = 184213) (by norm_num)
theorem B982525 : Blo 774336 982525 := bbase (se 3 (by rfl) ⟨184223, by rfl⟩ : syracuseStep 982525 = 368447) (by norm_num)
theorem B1310269 : Blo 774336 1310269 := bbase (se 3 (by rfl) ⟨245675, by rfl⟩ : syracuseStep 1310269 = 491351) (by norm_num)
theorem B2620997 : Blo 774336 2620997 := bbase (se 4 (by rfl) ⟨245718, by rfl⟩ : syracuseStep 2620997 = 491437) (by norm_num)
theorem B1867349 : Blo 774336 1867349 := bbase (se 8 (by rfl) ⟨10941, by rfl⟩ : syracuseStep 1867349 = 21883) (by norm_num)
theorem B982621 : Blo 774336 982621 := bbase (se 3 (by rfl) ⟨184241, by rfl⟩ : syracuseStep 982621 = 368483) (by norm_num)
theorem B1310357 : Blo 774336 1310357 := bbase (se 6 (by rfl) ⟨30711, by rfl⟩ : syracuseStep 1310357 = 61423) (by norm_num)
theorem B1474213 : Blo 774336 1474213 := bbase (se 4 (by rfl) ⟨138207, by rfl⟩ : syracuseStep 1474213 = 276415) (by norm_num)
theorem B1867493 : Blo 774336 1867493 := bbase (se 4 (by rfl) ⟨175077, by rfl⟩ : syracuseStep 1867493 = 350155) (by norm_num)
theorem B1965829 : Blo 774336 1965829 := bbase (se 4 (by rfl) ⟨184296, by rfl⟩ : syracuseStep 1965829 = 368593) (by norm_num)
theorem B982793 : Blo 774336 982793 := bbase (se 2 (by rfl) ⟨368547, by rfl⟩ : syracuseStep 982793 = 737095) (by norm_num)
theorem B4718357 : Blo 774336 4718357 := bbase (se 6 (by rfl) ⟨110586, by rfl⟩ : syracuseStep 4718357 = 221173) (by norm_num)
theorem B1310485 : Blo 774336 1310485 := bbase (se 6 (by rfl) ⟨30714, by rfl⟩ : syracuseStep 1310485 = 61429) (by norm_num)
theorem B1474357 : Blo 774336 1474357 := bbase (se 5 (by rfl) ⟨69110, by rfl⟩ : syracuseStep 1474357 = 138221) (by norm_num)
theorem B982849 : Blo 774336 982849 := bbase (se 2 (by rfl) ⟨368568, by rfl⟩ : syracuseStep 982849 = 737137) (by norm_num)
theorem B1310573 : Blo 774336 1310573 := bbase (se 3 (by rfl) ⟨245732, by rfl⟩ : syracuseStep 1310573 = 491465) (by norm_num)
theorem B1965941 : Blo 774336 1965941 := bbase (se 5 (by rfl) ⟨92153, by rfl⟩ : syracuseStep 1965941 = 184307) (by norm_num)
theorem B1245053 : Blo 774336 1245053 := bbase (se 3 (by rfl) ⟨233447, by rfl⟩ : syracuseStep 1245053 = 466895) (by norm_num)
theorem B982945 : Blo 774336 982945 := bbase (se 2 (by rfl) ⟨368604, by rfl⟩ : syracuseStep 982945 = 737209) (by norm_num)
theorem B1474517 : Blo 774336 1474517 := bbase (se 7 (by rfl) ⟨17279, by rfl⟩ : syracuseStep 1474517 = 34559) (by norm_num)
theorem B1310701 : Blo 774336 1310701 := bbase (se 3 (by rfl) ⟨245756, by rfl⟩ : syracuseStep 1310701 = 491513) (by norm_num)
theorem B2621429 : Blo 774336 2621429 := bbase (se 5 (by rfl) ⟨122879, by rfl⟩ : syracuseStep 2621429 = 245759) (by norm_num)
theorem B2949155 : Blo 774336 2949155 := bstep (se 1 (by rfl) ⟨2211866, by rfl⟩ : syracuseStep 2949155 = 4423733) B4423733
theorem B1310755 : Blo 774336 1310755 := bstep (se 1 (by rfl) ⟨983066, by rfl⟩ : syracuseStep 1310755 = 1966133) B1966133
theorem B2949169 : Blo 774336 2949169 := bstep (se 2 (by rfl) ⟨1105938, by rfl⟩ : syracuseStep 2949169 = 2211877) B2211877
theorem B983107 : Blo 774336 983107 := bstep (se 1 (by rfl) ⟨737330, by rfl⟩ : syracuseStep 983107 = 1474661) B1474661
theorem B2097265 : Blo 774336 2097265 := bstep (se 2 (by rfl) ⟨786474, by rfl⟩ : syracuseStep 2097265 = 1572949) B1572949
theorem B1310897 : Blo 774336 1310897 := bstep (se 2 (by rfl) ⟨491586, by rfl⟩ : syracuseStep 1310897 = 983173) B983173
theorem B2621645 : Blo 774336 2621645 := bstep (se 3 (by rfl) ⟨491558, by rfl⟩ : syracuseStep 2621645 = 983117) B983117
theorem B3932387 : Blo 774336 3932387 := bstep (se 1 (by rfl) ⟨2949290, by rfl⟩ : syracuseStep 3932387 = 5898581) B5898581
theorem B2621699 : Blo 774336 2621699 := bstep (se 1 (by rfl) ⟨1966274, by rfl⟩ : syracuseStep 2621699 = 3932549) B3932549
theorem B2654513 : Blo 774336 2654513 := bstep (se 2 (by rfl) ⟨995442, by rfl⟩ : syracuseStep 2654513 = 1990885) B1990885
theorem B1311025 : Blo 774336 1311025 := bstep (se 2 (by rfl) ⟨491634, by rfl⟩ : syracuseStep 1311025 = 983269) B983269
theorem B1179955 : Blo 774336 1179955 := bstep (se 1 (by rfl) ⟨884966, by rfl⟩ : syracuseStep 1179955 = 1769933) B1769933
theorem B1311059 : Blo 774336 1311059 := bstep (se 1 (by rfl) ⟨983294, by rfl⟩ : syracuseStep 1311059 = 1966589) B1966589
theorem B3309923 : Blo 774336 3309923 := bstep (se 1 (by rfl) ⟨2482442, by rfl⟩ : syracuseStep 3309923 = 4964885) B4964885
theorem B4194659 : Blo 774336 4194659 := bstep (se 1 (by rfl) ⟨3145994, by rfl⟩ : syracuseStep 4194659 = 6291989) B6291989
theorem B1311187 : Blo 774336 1311187 := bstep (se 1 (by rfl) ⟨983390, by rfl⟩ : syracuseStep 1311187 = 1966781) B1966781
theorem B2621969 : Blo 774336 2621969 := bstep (se 2 (by rfl) ⟨983238, by rfl⟩ : syracuseStep 2621969 = 1966477) B1966477
theorem B2490925 : Blo 774336 2490925 := bstep (se 3 (by rfl) ⟨467048, by rfl⟩ : syracuseStep 2490925 = 934097) B934097
theorem B983603 : Blo 774336 983603 := bstep (se 1 (by rfl) ⟨737702, by rfl⟩ : syracuseStep 983603 = 1475405) B1475405
theorem B1311329 : Blo 774336 1311329 := bstep (se 2 (by rfl) ⟨491748, by rfl⟩ : syracuseStep 1311329 = 983497) B983497
theorem B1475185 : Blo 774336 1475185 := bstep (se 2 (by rfl) ⟨553194, by rfl⟩ : syracuseStep 1475185 = 1106389) B1106389
theorem B1770115 : Blo 774336 1770115 := bstep (se 1 (by rfl) ⟨1327586, by rfl⟩ : syracuseStep 1770115 = 2655173) B2655173
theorem B1966801 : Blo 774336 1966801 := bstep (se 2 (by rfl) ⟨737550, by rfl⟩ : syracuseStep 1966801 = 1475101) B1475101
theorem B1311457 : Blo 774336 1311457 := bstep (se 2 (by rfl) ⟨491796, by rfl⟩ : syracuseStep 1311457 = 983593) B983593
theorem B1245937 : Blo 774336 1245937 := bstep (se 2 (by rfl) ⟨467226, by rfl⟩ : syracuseStep 1245937 = 934453) B934453
theorem B1311491 : Blo 774336 1311491 := bstep (se 1 (by rfl) ⟨983618, by rfl⟩ : syracuseStep 1311491 = 1967237) B1967237
theorem B4424483 : Blo 774336 4424483 := bstep (se 1 (by rfl) ⟨3318362, by rfl⟩ : syracuseStep 4424483 = 6636725) B6636725
theorem B1868579 : Blo 774336 1868579 := bstep (se 1 (by rfl) ⟨1401434, by rfl⟩ : syracuseStep 1868579 = 2802869) B2802869
theorem B2098001 : Blo 774336 2098001 := bstep (se 2 (by rfl) ⟨786750, by rfl⟩ : syracuseStep 2098001 = 1573501) B1573501
theorem B1311619 : Blo 774336 1311619 := bstep (se 1 (by rfl) ⟨983714, by rfl⟩ : syracuseStep 1311619 = 1967429) B1967429
theorem B1967075 : Blo 774336 1967075 := bstep (se 1 (by rfl) ⟨1475306, by rfl⟩ : syracuseStep 1967075 = 2950613) B2950613
theorem B1868771 : Blo 774336 1868771 := bstep (se 1 (by rfl) ⟨1401578, by rfl⟩ : syracuseStep 1868771 = 2803157) B2803157
theorem B1475587 : Blo 774336 1475587 := bstep (se 1 (by rfl) ⟨1106690, by rfl⟩ : syracuseStep 1475587 = 2213381) B2213381
theorem B3933197 : Blo 774336 3933197 := bstep (se 3 (by rfl) ⟨737474, by rfl⟩ : syracuseStep 3933197 = 1474949) B1474949
theorem B1311761 : Blo 774336 1311761 := bstep (se 2 (by rfl) ⟨491910, by rfl⟩ : syracuseStep 1311761 = 983821) B983821
theorem B2622509 : Blo 774336 2622509 := bstep (se 3 (by rfl) ⟨491720, by rfl⟩ : syracuseStep 2622509 = 983441) B983441
theorem B1475633 : Blo 774336 1475633 := bstep (se 2 (by rfl) ⟨553362, by rfl⟩ : syracuseStep 1475633 = 1106725) B1106725
theorem B37815349 : Blo 774336 37815349 := bstep (se 5 (by rfl) ⟨1772594, by rfl⟩ : syracuseStep 37815349 = 3545189) B3545189
theorem B1573987 : Blo 774336 1573987 := bstep (se 1 (by rfl) ⟨1180490, by rfl⟩ : syracuseStep 1573987 = 2360981) B2360981
theorem B2622563 : Blo 774336 2622563 := bstep (se 1 (by rfl) ⟨1966922, by rfl⟩ : syracuseStep 2622563 = 3933845) B3933845
theorem B1311889 : Blo 774336 1311889 := bstep (se 2 (by rfl) ⟨491958, by rfl⟩ : syracuseStep 1311889 = 983917) B983917
theorem B1967267 : Blo 774336 1967267 := bstep (se 1 (by rfl) ⟨1475450, by rfl⟩ : syracuseStep 1967267 = 2950901) B2950901
theorem B1246385 : Blo 774336 1246385 := bstep (se 2 (by rfl) ⟨467394, by rfl⟩ : syracuseStep 1246385 = 934789) B934789
theorem B1311923 : Blo 774336 1311923 := bstep (se 1 (by rfl) ⟨983942, by rfl⟩ : syracuseStep 1311923 = 1967885) B1967885
theorem B1574083 : Blo 774336 1574083 := bstep (se 1 (by rfl) ⟨1180562, by rfl⟩ : syracuseStep 1574083 = 2361125) B2361125
theorem B10650851 : Blo 774336 10650851 := bstep (se 1 (by rfl) ⟨7988138, by rfl⟩ : syracuseStep 10650851 = 15976277) B15976277
theorem B984307 : Blo 774336 984307 := bstep (se 1 (by rfl) ⟨738230, by rfl⟩ : syracuseStep 984307 = 1476461) B1476461
theorem B1312051 : Blo 774336 1312051 := bstep (se 1 (by rfl) ⟨984038, by rfl⟩ : syracuseStep 1312051 = 1968077) B1968077
theorem B1475921 : Blo 774336 1475921 := bstep (se 2 (by rfl) ⟨553470, by rfl⟩ : syracuseStep 1475921 = 1106941) B1106941
theorem B984403 : Blo 774336 984403 := bstep (se 1 (by rfl) ⟨738302, by rfl⟩ : syracuseStep 984403 = 1476605) B1476605
theorem B2098541 : Blo 774336 2098541 := bstep (se 3 (by rfl) ⟨393476, by rfl⟩ : syracuseStep 2098541 = 786953) B786953
theorem B2622833 : Blo 774336 2622833 := bstep (se 2 (by rfl) ⟨983562, by rfl⟩ : syracuseStep 2622833 = 1967125) B1967125
theorem B1312193 : Blo 774336 1312193 := bstep (se 2 (by rfl) ⟨492072, by rfl⟩ : syracuseStep 1312193 = 984145) B984145
theorem B1181123 : Blo 774336 1181123 := bstep (se 1 (by rfl) ⟨885842, by rfl⟩ : syracuseStep 1181123 = 1771685) B1771685
theorem B2950627 : Blo 774336 2950627 := bstep (se 1 (by rfl) ⟨2212970, by rfl⟩ : syracuseStep 2950627 = 4425941) B4425941
theorem B1312321 : Blo 774336 1312321 := bstep (se 2 (by rfl) ⟨492120, by rfl⟩ : syracuseStep 1312321 = 984241) B984241
theorem B1312355 : Blo 774336 1312355 := bstep (se 1 (by rfl) ⟨984266, by rfl⟩ : syracuseStep 1312355 = 1968533) B1968533
theorem B36374129 : Blo 774336 36374129 := bstep (se 2 (by rfl) ⟨13640298, by rfl⟩ : syracuseStep 36374129 = 27280597) B27280597
theorem B1869425 : Blo 774336 1869425 := bstep (se 2 (by rfl) ⟨701034, by rfl⟩ : syracuseStep 1869425 = 1402069) B1402069
theorem B9930437 : Blo 774336 9930437 := bstep (se 4 (by rfl) ⟨930978, by rfl⟩ : syracuseStep 9930437 = 1861957) B1861957
theorem B1312483 : Blo 774336 1312483 := bstep (se 1 (by rfl) ⟨984362, by rfl⟩ : syracuseStep 1312483 = 1968725) B1968725
theorem B984899 : Blo 774336 984899 := bstep (se 1 (by rfl) ⟨738674, by rfl⟩ : syracuseStep 984899 = 1477349) B1477349
theorem B1312625 : Blo 774336 1312625 := bstep (se 2 (by rfl) ⟨492234, by rfl⟩ : syracuseStep 1312625 = 984469) B984469
theorem B2623373 : Blo 774336 2623373 := bstep (se 3 (by rfl) ⟨491882, by rfl⟩ : syracuseStep 2623373 = 983765) B983765
theorem B1279891 : Blo 774336 1279891 := bstep (se 1 (by rfl) ⟨959918, by rfl⟩ : syracuseStep 1279891 = 1919837) B1919837
theorem B1771427 : Blo 774336 1771427 := bstep (se 1 (by rfl) ⟨1328570, by rfl⟩ : syracuseStep 1771427 = 2657141) B2657141
theorem B1181633 : Blo 774336 1181633 := bstep (se 2 (by rfl) ⟨443112, by rfl⟩ : syracuseStep 1181633 = 886225) B886225
theorem B2623427 : Blo 774336 2623427 := bstep (se 1 (by rfl) ⟨1967570, by rfl⟩ : syracuseStep 2623427 = 3935141) B3935141
theorem B1312753 : Blo 774336 1312753 := bstep (se 2 (by rfl) ⟨492282, by rfl⟩ : syracuseStep 1312753 = 984565) B984565
theorem B1050643 : Blo 774336 1050643 := bstep (se 1 (by rfl) ⟨787982, by rfl⟩ : syracuseStep 1050643 = 1575965) B1575965
theorem B1312787 : Blo 774336 1312787 := bstep (se 1 (by rfl) ⟨984590, by rfl⟩ : syracuseStep 1312787 = 1969181) B1969181
theorem B1476643 : Blo 774336 1476643 := bstep (se 1 (by rfl) ⟨1107482, by rfl⟩ : syracuseStep 1476643 = 2214965) B2214965
theorem B1968209 : Blo 774336 1968209 := bstep (se 2 (by rfl) ⟨738078, by rfl⟩ : syracuseStep 1968209 = 1476157) B1476157
theorem B1968259 : Blo 774336 1968259 := bstep (se 1 (by rfl) ⟨1476194, by rfl⟩ : syracuseStep 1968259 = 2952389) B2952389
theorem B1312915 : Blo 774336 1312915 := bstep (se 1 (by rfl) ⟨984686, by rfl⟩ : syracuseStep 1312915 = 1969373) B1969373
theorem B1575121 : Blo 774336 1575121 := bstep (se 2 (by rfl) ⟨590670, by rfl⟩ : syracuseStep 1575121 = 1181341) B1181341
theorem B2623697 : Blo 774336 2623697 := bstep (se 2 (by rfl) ⟨983886, by rfl⟩ : syracuseStep 2623697 = 1967773) B1967773
theorem B2492657 : Blo 774336 2492657 := bstep (se 2 (by rfl) ⟨934746, by rfl⟩ : syracuseStep 2492657 = 1869493) B1869493
theorem B1181969 : Blo 774336 1181969 := bstep (se 2 (by rfl) ⟨443238, by rfl⟩ : syracuseStep 1181969 = 886477) B886477
theorem B1968401 : Blo 774336 1968401 := bstep (se 2 (by rfl) ⟨738150, by rfl⟩ : syracuseStep 1968401 = 1476301) B1476301
theorem B1313057 : Blo 774336 1313057 := bstep (se 2 (by rfl) ⟨492396, by rfl⟩ : syracuseStep 1313057 = 984793) B984793
theorem B1345921 : Blo 774336 1345921 := bstep (se 2 (by rfl) ⟨504720, by rfl⟩ : syracuseStep 1345921 = 1009441) B1009441
theorem B1313185 : Blo 774336 1313185 := bstep (se 2 (by rfl) ⟨492444, by rfl⟩ : syracuseStep 1313185 = 984889) B984889
theorem B1313219 : Blo 774336 1313219 := bstep (se 1 (by rfl) ⟨984914, by rfl⟩ : syracuseStep 1313219 = 1969829) B1969829
theorem B1477091 : Blo 774336 1477091 := bstep (se 1 (by rfl) ⟨1107818, by rfl⟩ : syracuseStep 1477091 = 2215637) B2215637
theorem B1313347 : Blo 774336 1313347 := bstep (se 1 (by rfl) ⟨985010, by rfl⟩ : syracuseStep 1313347 = 1970021) B1970021
theorem B2362051 : Blo 774336 2362051 := bstep (se 1 (by rfl) ⟨1771538, by rfl⟩ : syracuseStep 2362051 = 3543077) B3543077
theorem B2624237 : Blo 774336 2624237 := bstep (se 3 (by rfl) ⟨492044, by rfl⟩ : syracuseStep 2624237 = 984089) B984089
theorem B1477379 : Blo 774336 1477379 := bstep (se 1 (by rfl) ⟨1108034, by rfl⟩ : syracuseStep 1477379 = 2216069) B2216069
theorem B2624291 : Blo 774336 2624291 := bstep (se 1 (by rfl) ⟨1968218, by rfl⟩ : syracuseStep 2624291 = 3936437) B3936437
theorem B2493283 : Blo 774336 2493283 := bstep (se 1 (by rfl) ⟨1869962, by rfl⟩ : syracuseStep 2493283 = 3739925) B3739925
theorem B2624561 : Blo 774336 2624561 := bstep (se 2 (by rfl) ⟨984210, by rfl⟩ : syracuseStep 2624561 = 1968421) B1968421
theorem B1969393 : Blo 774336 1969393 := bstep (se 2 (by rfl) ⟨738522, by rfl⟩ : syracuseStep 1969393 = 1477045) B1477045
theorem B1346881 : Blo 774336 1346881 := bstep (se 2 (by rfl) ⟨505080, by rfl⟩ : syracuseStep 1346881 = 1010161) B1010161
theorem B1969667 : Blo 774336 1969667 := bstep (se 1 (by rfl) ⟨1477250, by rfl⟩ : syracuseStep 1969667 = 2954501) B2954501
theorem B4197901 : Blo 774336 4197901 := bstep (se 3 (by rfl) ⟨787106, by rfl⟩ : syracuseStep 4197901 = 1574213) B1574213
theorem B2625101 : Blo 774336 2625101 := bstep (se 3 (by rfl) ⟨492206, by rfl⟩ : syracuseStep 2625101 = 984413) B984413
theorem B1183331 : Blo 774336 1183331 := bstep (se 1 (by rfl) ⟨887498, by rfl⟩ : syracuseStep 1183331 = 1774997) B1774997
theorem B2625155 : Blo 774336 2625155 := bstep (se 1 (by rfl) ⟨1968866, by rfl⟩ : syracuseStep 2625155 = 3937733) B3937733
theorem B2952845 : Blo 774336 2952845 := bstep (se 3 (by rfl) ⟨553658, by rfl⟩ : syracuseStep 2952845 = 1107317) B1107317
theorem B1969859 : Blo 774336 1969859 := bstep (se 1 (by rfl) ⟨1477394, by rfl⟩ : syracuseStep 1969859 = 2954789) B2954789
theorem B2100941 : Blo 774336 2100941 := bstep (se 3 (by rfl) ⟨393926, by rfl⟩ : syracuseStep 2100941 = 787853) B787853
theorem B3936113 : Blo 774336 3936113 := bstep (se 2 (by rfl) ⟨1476042, by rfl⟩ : syracuseStep 3936113 = 2952085) B2952085
theorem B2625425 : Blo 774336 2625425 := bstep (se 2 (by rfl) ⟨984534, by rfl⟩ : syracuseStep 2625425 = 1969069) B1969069
theorem B1773539 : Blo 774336 1773539 := bstep (se 1 (by rfl) ⟨1330154, by rfl⟩ : syracuseStep 1773539 = 2660309) B2660309
theorem B3740003 : Blo 774336 3740003 := bstep (se 1 (by rfl) ⟨2805002, by rfl⟩ : syracuseStep 3740003 = 5610005) B5610005
theorem B2625965 : Blo 774336 2625965 := bstep (se 3 (by rfl) ⟨492368, by rfl⟩ : syracuseStep 2625965 = 984737) B984737
theorem B4198853 : Blo 774336 4198853 := bstep (se 4 (by rfl) ⟨393642, by rfl⟩ : syracuseStep 4198853 = 787285) B787285
theorem B3314125 : Blo 774336 3314125 := bstep (se 3 (by rfl) ⟨621398, by rfl⟩ : syracuseStep 3314125 = 1242797) B1242797
theorem B2626019 : Blo 774336 2626019 := bstep (se 1 (by rfl) ⟨1969514, by rfl⟩ : syracuseStep 2626019 = 3939029) B3939029
theorem B6296305 : Blo 774336 6296305 := bstep (se 2 (by rfl) ⟨2361114, by rfl⟩ : syracuseStep 6296305 = 4722229) B4722229
theorem B2626289 : Blo 774336 2626289 := bstep (se 2 (by rfl) ⟨984858, by rfl⟩ : syracuseStep 2626289 = 1969717) B1969717
theorem B2659331 : Blo 774336 2659331 := bstep (se 1 (by rfl) ⟨1994498, by rfl⟩ : syracuseStep 2659331 = 3988997) B3988997
theorem B1020979 : Blo 774336 1020979 := bstep (se 1 (by rfl) ⟨765734, by rfl⟩ : syracuseStep 1020979 = 1531469) B1531469
theorem B2626829 : Blo 774336 2626829 := bstep (se 3 (by rfl) ⟨492530, by rfl⟩ : syracuseStep 2626829 = 985061) B985061
theorem B1119505 : Blo 774336 1119505 := bstep (se 2 (by rfl) ⟨419814, by rfl⟩ : syracuseStep 1119505 = 839629) B839629
theorem B3937571 : Blo 774336 3937571 := bstep (se 1 (by rfl) ⟨2953178, by rfl⟩ : syracuseStep 3937571 = 5906357) B5906357
theorem B2626883 : Blo 774336 2626883 := bstep (se 1 (by rfl) ⟨1970162, by rfl⟩ : syracuseStep 2626883 = 3940325) B3940325
theorem B3151217 : Blo 774336 3151217 := bstep (se 2 (by rfl) ⟨1181706, by rfl⟩ : syracuseStep 3151217 = 2363413) B2363413
theorem B2790989 : Blo 774336 2790989 := bstep (se 3 (by rfl) ⟨523310, by rfl⟩ : syracuseStep 2790989 = 1046621) B1046621
theorem B1742417 : Blo 774336 1742417 := bstep (se 2 (by rfl) ⟨653406, by rfl⟩ : syracuseStep 1742417 = 1306813) B1306813
theorem B1742435 : Blo 774336 1742435 := bstep (se 1 (by rfl) ⟨1306826, by rfl⟩ : syracuseStep 1742435 = 2613653) B2613653
theorem B1742705 : Blo 774336 1742705 := bstep (se 2 (by rfl) ⟨653514, by rfl⟩ : syracuseStep 1742705 = 1307029) B1307029
theorem B1742723 : Blo 774336 1742723 := bstep (se 1 (by rfl) ⟨1307042, by rfl⟩ : syracuseStep 1742723 = 2614085) B2614085
theorem B1120243 : Blo 774336 1120243 := bstep (se 1 (by rfl) ⟨840182, by rfl⟩ : syracuseStep 1120243 = 1680365) B1680365
theorem B3938381 : Blo 774336 3938381 := bstep (se 3 (by rfl) ⟨738446, by rfl⟩ : syracuseStep 3938381 = 1476893) B1476893
theorem B1742993 : Blo 774336 1742993 := bstep (se 2 (by rfl) ⟨653622, by rfl⟩ : syracuseStep 1742993 = 1307245) B1307245
theorem B1743011 : Blo 774336 1743011 := bstep (se 1 (by rfl) ⟨1307258, by rfl⟩ : syracuseStep 1743011 = 2614517) B2614517
theorem B1743281 : Blo 774336 1743281 := bstep (se 2 (by rfl) ⟨653730, by rfl⟩ : syracuseStep 1743281 = 1307461) B1307461
theorem B1743299 : Blo 774336 1743299 := bstep (se 1 (by rfl) ⟨1307474, by rfl⟩ : syracuseStep 1743299 = 2614949) B2614949
theorem B1743569 : Blo 774336 1743569 := bstep (se 2 (by rfl) ⟨653838, by rfl⟩ : syracuseStep 1743569 = 1307677) B1307677
theorem B1743587 : Blo 774336 1743587 := bstep (se 1 (by rfl) ⟨1307690, by rfl⟩ : syracuseStep 1743587 = 2615381) B2615381
theorem B1743857 : Blo 774336 1743857 := bstep (se 2 (by rfl) ⟨653946, by rfl⟩ : syracuseStep 1743857 = 1307893) B1307893
theorem B1743875 : Blo 774336 1743875 := bstep (se 1 (by rfl) ⟨1307906, by rfl⟩ : syracuseStep 1743875 = 2615813) B2615813
theorem B2661617 : Blo 774336 2661617 := bstep (se 2 (by rfl) ⟨998106, by rfl⟩ : syracuseStep 2661617 = 1996213) B1996213
theorem B1744145 : Blo 774336 1744145 := bstep (se 2 (by rfl) ⟨654054, by rfl⟩ : syracuseStep 1744145 = 1308109) B1308109
theorem B1744163 : Blo 774336 1744163 := bstep (se 1 (by rfl) ⟨1308122, by rfl⟩ : syracuseStep 1744163 = 2616245) B2616245
theorem B3153293 : Blo 774336 3153293 := bstep (se 3 (by rfl) ⟨591242, by rfl⟩ : syracuseStep 3153293 = 1182485) B1182485
theorem B1744433 : Blo 774336 1744433 := bstep (se 2 (by rfl) ⟨654162, by rfl⟩ : syracuseStep 1744433 = 1308325) B1308325
theorem B1744451 : Blo 774336 1744451 := bstep (se 1 (by rfl) ⟨1308338, by rfl⟩ : syracuseStep 1744451 = 2616677) B2616677
theorem B827011 : Blo 774336 827011 := bstep (se 1 (by rfl) ⟨620258, by rfl⟩ : syracuseStep 827011 = 1240517) B1240517
theorem B1023763 : Blo 774336 1023763 := bstep (se 1 (by rfl) ⟨767822, by rfl⟩ : syracuseStep 1023763 = 1535645) B1535645
theorem B1744721 : Blo 774336 1744721 := bstep (se 2 (by rfl) ⟨654270, by rfl⟩ : syracuseStep 1744721 = 1308541) B1308541
theorem B1744739 : Blo 774336 1744739 := bstep (se 1 (by rfl) ⟨1308554, by rfl⟩ : syracuseStep 1744739 = 2617109) B2617109
theorem B827267 : Blo 774336 827267 := bstep (se 1 (by rfl) ⟨620450, by rfl⟩ : syracuseStep 827267 = 1240901) B1240901
theorem B1122241 : Blo 774336 1122241 := bstep (se 2 (by rfl) ⟨420840, by rfl⟩ : syracuseStep 1122241 = 841681) B841681
theorem B1745009 : Blo 774336 1745009 := bstep (se 2 (by rfl) ⟨654378, by rfl⟩ : syracuseStep 1745009 = 1308757) B1308757
theorem B1745027 : Blo 774336 1745027 := bstep (se 1 (by rfl) ⟨1308770, by rfl⟩ : syracuseStep 1745027 = 2617541) B2617541
theorem B1745297 : Blo 774336 1745297 := bstep (se 2 (by rfl) ⟨654486, by rfl⟩ : syracuseStep 1745297 = 1308973) B1308973
theorem B1745315 : Blo 774336 1745315 := bstep (se 1 (by rfl) ⟨1308986, by rfl⟩ : syracuseStep 1745315 = 2617973) B2617973
theorem B828019 : Blo 774336 828019 := bstep (se 1 (by rfl) ⟨621014, by rfl⟩ : syracuseStep 828019 = 1242029) B1242029
theorem B1745585 : Blo 774336 1745585 := bstep (se 2 (by rfl) ⟨654594, by rfl⟩ : syracuseStep 1745585 = 1309189) B1309189
theorem B1745603 : Blo 774336 1745603 := bstep (se 1 (by rfl) ⟨1309202, by rfl⟩ : syracuseStep 1745603 = 2618405) B2618405
theorem B3318499 : Blo 774336 3318499 := bstep (se 1 (by rfl) ⟨2488874, by rfl⟩ : syracuseStep 3318499 = 4977749) B4977749
theorem B1745873 : Blo 774336 1745873 := bstep (se 2 (by rfl) ⟨654702, by rfl⟩ : syracuseStep 1745873 = 1309405) B1309405
theorem B1745891 : Blo 774336 1745891 := bstep (se 1 (by rfl) ⟨1309418, by rfl⟩ : syracuseStep 1745891 = 2618837) B2618837
theorem B1746161 : Blo 774336 1746161 := bstep (se 2 (by rfl) ⟨654810, by rfl⟩ : syracuseStep 1746161 = 1309621) B1309621
theorem B1746179 : Blo 774336 1746179 := bstep (se 1 (by rfl) ⟨1309634, by rfl⟩ : syracuseStep 1746179 = 2619269) B2619269
theorem B796099 : Blo 774336 796099 := bstep (se 1 (by rfl) ⟨597074, by rfl⟩ : syracuseStep 796099 = 1194149) B1194149
theorem B1746449 : Blo 774336 1746449 := bstep (se 2 (by rfl) ⟨654918, by rfl⟩ : syracuseStep 1746449 = 1309837) B1309837
theorem B1746467 : Blo 774336 1746467 := bstep (se 1 (by rfl) ⟨1309850, by rfl⟩ : syracuseStep 1746467 = 2619701) B2619701
theorem B1746737 : Blo 774336 1746737 := bstep (se 2 (by rfl) ⟨655026, by rfl⟩ : syracuseStep 1746737 = 1310053) B1310053
theorem B1746755 : Blo 774336 1746755 := bstep (se 1 (by rfl) ⟨1310066, by rfl⟩ : syracuseStep 1746755 = 2620133) B2620133
theorem B829283 : Blo 774336 829283 := bstep (se 1 (by rfl) ⟨621962, by rfl⟩ : syracuseStep 829283 = 1243925) B1243925
theorem B3188621 : Blo 774336 3188621 := bstep (se 3 (by rfl) ⟨597866, by rfl⟩ : syracuseStep 3188621 = 1195733) B1195733
theorem B4728773 : Blo 774336 4728773 := bstep (se 4 (by rfl) ⟨443322, by rfl⟩ : syracuseStep 4728773 = 886645) B886645
theorem B1747025 : Blo 774336 1747025 := bstep (se 2 (by rfl) ⟨655134, by rfl⟩ : syracuseStep 1747025 = 1310269) B1310269
theorem B1747043 : Blo 774336 1747043 := bstep (se 1 (by rfl) ⟨1310282, by rfl⟩ : syracuseStep 1747043 = 2620565) B2620565
theorem B2959715 : Blo 774336 2959715 := bstep (se 1 (by rfl) ⟨2219786, by rfl⟩ : syracuseStep 2959715 = 4439573) B4439573
theorem B1747313 : Blo 774336 1747313 := bstep (se 2 (by rfl) ⟨655242, by rfl⟩ : syracuseStep 1747313 = 1310485) B1310485
theorem B1747331 : Blo 774336 1747331 := bstep (se 1 (by rfl) ⟨1310498, by rfl⟩ : syracuseStep 1747331 = 2620997) B2620997
theorem B76687813 : Blo 774336 76687813 := bstep (se 4 (by rfl) ⟨7189482, by rfl⟩ : syracuseStep 76687813 = 14378965) B14378965
theorem B830035 : Blo 774336 830035 := bstep (se 1 (by rfl) ⟨622526, by rfl⟩ : syracuseStep 830035 = 1245053) B1245053
theorem B1747601 : Blo 774336 1747601 := bstep (se 2 (by rfl) ⟨655350, by rfl⟩ : syracuseStep 1747601 = 1310701) B1310701
theorem B1747619 : Blo 774336 1747619 := bstep (se 1 (by rfl) ⟨1310714, by rfl⟩ : syracuseStep 1747619 = 2621429) B2621429
theorem B1747889 : Blo 774336 1747889 := bstep (se 2 (by rfl) ⟨655458, by rfl⟩ : syracuseStep 1747889 = 1310917) B1310917
theorem B1747907 : Blo 774336 1747907 := bstep (se 1 (by rfl) ⟨1310930, by rfl⟩ : syracuseStep 1747907 = 2621861) B2621861
theorem B2206673 : Blo 774336 2206673 := bstep (se 2 (by rfl) ⟨827502, by rfl⟩ : syracuseStep 2206673 = 1655005) B1655005
theorem B3320945 : Blo 774336 3320945 := bstep (se 2 (by rfl) ⟨1245354, by rfl⟩ : syracuseStep 3320945 = 2490709) B2490709
theorem B12102797 : Blo 774336 12102797 := bstep (se 3 (by rfl) ⟨2269274, by rfl⟩ : syracuseStep 12102797 = 4538549) B4538549
theorem B2206865 : Blo 774336 2206865 := bstep (se 2 (by rfl) ⟨827574, by rfl⟩ : syracuseStep 2206865 = 1655149) B1655149
theorem B4730033 : Blo 774336 4730033 := bstep (se 2 (by rfl) ⟨1773762, by rfl⟩ : syracuseStep 4730033 = 3547525) B3547525
theorem B1748177 : Blo 774336 1748177 := bstep (se 2 (by rfl) ⟨655566, by rfl⟩ : syracuseStep 1748177 = 1311133) B1311133
theorem B1748195 : Blo 774336 1748195 := bstep (se 1 (by rfl) ⟨1311146, by rfl⟩ : syracuseStep 1748195 = 2622293) B2622293
theorem B1748465 : Blo 774336 1748465 := bstep (se 2 (by rfl) ⟨655674, by rfl⟩ : syracuseStep 1748465 = 1311349) B1311349
theorem B1748483 : Blo 774336 1748483 := bstep (se 1 (by rfl) ⟨1311362, by rfl⟩ : syracuseStep 1748483 = 2622725) B2622725
theorem B18853397 : Blo 774336 18853397 := bstep (se 6 (by rfl) ⟨441876, by rfl⟩ : syracuseStep 18853397 = 883753) B883753
theorem B831043 : Blo 774336 831043 := bstep (se 1 (by rfl) ⟨623282, by rfl⟩ : syracuseStep 831043 = 1246565) B1246565
theorem B3190499 : Blo 774336 3190499 := bstep (se 1 (by rfl) ⟨2392874, by rfl⟩ : syracuseStep 3190499 = 4785749) B4785749
theorem B1748753 : Blo 774336 1748753 := bstep (se 2 (by rfl) ⟨655782, by rfl⟩ : syracuseStep 1748753 = 1311565) B1311565
theorem B1748771 : Blo 774336 1748771 := bstep (se 1 (by rfl) ⟨1311578, by rfl⟩ : syracuseStep 1748771 = 2623157) B2623157
theorem B1749041 : Blo 774336 1749041 := bstep (se 2 (by rfl) ⟨655890, by rfl⟩ : syracuseStep 1749041 = 1311781) B1311781
theorem B1749059 : Blo 774336 1749059 := bstep (se 1 (by rfl) ⟨1311794, by rfl⟩ : syracuseStep 1749059 = 2623589) B2623589
theorem B8400995 : Blo 774336 8400995 := bstep (se 1 (by rfl) ⟨6300746, by rfl⟩ : syracuseStep 8400995 = 12601493) B12601493
theorem B2207857 : Blo 774336 2207857 := bstep (se 2 (by rfl) ⟨827946, by rfl⟩ : syracuseStep 2207857 = 1655893) B1655893
theorem B4206725 : Blo 774336 4206725 := bstep (se 4 (by rfl) ⟨394380, by rfl⟩ : syracuseStep 4206725 = 788761) B788761
theorem B1749329 : Blo 774336 1749329 := bstep (se 2 (by rfl) ⟨655998, by rfl⟩ : syracuseStep 1749329 = 1311997) B1311997
theorem B1749347 : Blo 774336 1749347 := bstep (se 1 (by rfl) ⟨1312010, by rfl⟩ : syracuseStep 1749347 = 2624021) B2624021
theorem B2208131 : Blo 774336 2208131 := bstep (se 1 (by rfl) ⟨1656098, by rfl⟩ : syracuseStep 2208131 = 3312197) B3312197
theorem B2208323 : Blo 774336 2208323 := bstep (se 1 (by rfl) ⟨1656242, by rfl⟩ : syracuseStep 2208323 = 3312485) B3312485
theorem B1749617 : Blo 774336 1749617 := bstep (se 2 (by rfl) ⟨656106, by rfl⟩ : syracuseStep 1749617 = 1312213) B1312213
theorem B1749635 : Blo 774336 1749635 := bstep (se 1 (by rfl) ⟨1312226, by rfl⟩ : syracuseStep 1749635 = 2624453) B2624453
theorem B6632077 : Blo 774336 6632077 := bstep (se 3 (by rfl) ⟨1243514, by rfl⟩ : syracuseStep 6632077 = 2487029) B2487029
theorem B1749905 : Blo 774336 1749905 := bstep (se 2 (by rfl) ⟨656214, by rfl⟩ : syracuseStep 1749905 = 1312429) B1312429
theorem B1749923 : Blo 774336 1749923 := bstep (se 1 (by rfl) ⟨1312442, by rfl⟩ : syracuseStep 1749923 = 2624885) B2624885
theorem B1750193 : Blo 774336 1750193 := bstep (se 2 (by rfl) ⟨656322, by rfl⟩ : syracuseStep 1750193 = 1312645) B1312645
theorem B1750211 : Blo 774336 1750211 := bstep (se 1 (by rfl) ⟨1312658, by rfl⟩ : syracuseStep 1750211 = 2625317) B2625317
theorem B2209133 : Blo 774336 2209133 := bstep (se 3 (by rfl) ⟨414212, by rfl⟩ : syracuseStep 2209133 = 828425) B828425
theorem B1750481 : Blo 774336 1750481 := bstep (se 2 (by rfl) ⟨656430, by rfl⟩ : syracuseStep 1750481 = 1312861) B1312861
theorem B5682659 : Blo 774336 5682659 := bstep (se 1 (by rfl) ⟨4261994, by rfl⟩ : syracuseStep 5682659 = 8523989) B8523989
theorem B1750499 : Blo 774336 1750499 := bstep (se 1 (by rfl) ⟨1312874, by rfl⟩ : syracuseStep 1750499 = 2625749) B2625749
theorem B2209315 : Blo 774336 2209315 := bstep (se 1 (by rfl) ⟨1656986, by rfl⟩ : syracuseStep 2209315 = 3313973) B3313973
theorem B1750769 : Blo 774336 1750769 := bstep (se 2 (by rfl) ⟨656538, by rfl⟩ : syracuseStep 1750769 = 1313077) B1313077
theorem B1750787 : Blo 774336 1750787 := bstep (se 1 (by rfl) ⟨1313090, by rfl⟩ : syracuseStep 1750787 = 2626181) B2626181
theorem B1455889 : Blo 774336 1455889 := bstep (se 2 (by rfl) ⟨545958, by rfl⟩ : syracuseStep 1455889 = 1091917) B1091917
theorem B997219 : Blo 774336 997219 := bstep (se 1 (by rfl) ⟨747914, by rfl⟩ : syracuseStep 997219 = 1495829) B1495829
theorem B6633413 : Blo 774336 6633413 := bstep (se 4 (by rfl) ⟨621882, by rfl⟩ : syracuseStep 6633413 = 1243765) B1243765
theorem B2209805 : Blo 774336 2209805 := bstep (se 3 (by rfl) ⟨414338, by rfl⟩ : syracuseStep 2209805 = 828677) B828677
theorem B1751057 : Blo 774336 1751057 := bstep (se 2 (by rfl) ⟨656646, by rfl⟩ : syracuseStep 1751057 = 1313293) B1313293
theorem B1751075 : Blo 774336 1751075 := bstep (se 1 (by rfl) ⟨1313306, by rfl⟩ : syracuseStep 1751075 = 2626613) B2626613
theorem B2242637 : Blo 774336 2242637 := bstep (se 3 (by rfl) ⟨420494, by rfl⟩ : syracuseStep 2242637 = 840989) B840989
theorem B3356849 : Blo 774336 3356849 := bstep (se 2 (by rfl) ⟨1258818, by rfl⟩ : syracuseStep 3356849 = 2517637) B2517637
theorem B1161521 : Blo 774336 1161521 := bstep (se 2 (by rfl) ⟨435570, by rfl⟩ : syracuseStep 1161521 = 871141) B871141
theorem B1161539 : Blo 774336 1161539 := bstep (se 1 (by rfl) ⟨871154, by rfl⟩ : syracuseStep 1161539 = 1742309) B1742309
theorem B1161569 : Blo 774336 1161569 := bstep (se 2 (by rfl) ⟨435588, by rfl⟩ : syracuseStep 1161569 = 871177) B871177
theorem B1325425 : Blo 774336 1325425 := bstep (se 2 (by rfl) ⟨497034, by rfl⟩ : syracuseStep 1325425 = 994069) B994069
theorem B1161587 : Blo 774336 1161587 := bstep (se 1 (by rfl) ⟨871190, by rfl⟩ : syracuseStep 1161587 = 1742381) B1742381
theorem B1194355 : Blo 774336 1194355 := bstep (se 1 (by rfl) ⟨895766, by rfl⟩ : syracuseStep 1194355 = 1791533) B1791533
theorem B1161617 : Blo 774336 1161617 := bstep (se 2 (by rfl) ⟨435606, by rfl⟩ : syracuseStep 1161617 = 871213) B871213
theorem B1161635 : Blo 774336 1161635 := bstep (se 1 (by rfl) ⟨871226, by rfl⟩ : syracuseStep 1161635 = 1742453) B1742453
theorem B1161665 : Blo 774336 1161665 := bstep (se 2 (by rfl) ⟨435624, by rfl⟩ : syracuseStep 1161665 = 871249) B871249
theorem B1161683 : Blo 774336 1161683 := bstep (se 1 (by rfl) ⟨871262, by rfl⟩ : syracuseStep 1161683 = 1742525) B1742525
theorem B1161713 : Blo 774336 1161713 := bstep (se 2 (by rfl) ⟨435642, by rfl⟩ : syracuseStep 1161713 = 871285) B871285
theorem B1161731 : Blo 774336 1161731 := bstep (se 1 (by rfl) ⟨871298, by rfl⟩ : syracuseStep 1161731 = 1742597) B1742597
theorem B1161761 : Blo 774336 1161761 := bstep (se 2 (by rfl) ⟨435660, by rfl⟩ : syracuseStep 1161761 = 871321) B871321
theorem B1161779 : Blo 774336 1161779 := bstep (se 1 (by rfl) ⟨871334, by rfl⟩ : syracuseStep 1161779 = 1742669) B1742669
theorem B1161809 : Blo 774336 1161809 := bstep (se 2 (by rfl) ⟨435678, by rfl⟩ : syracuseStep 1161809 = 871357) B871357
theorem B1161827 : Blo 774336 1161827 := bstep (se 1 (by rfl) ⟨871370, by rfl⟩ : syracuseStep 1161827 = 1742741) B1742741
theorem B1161857 : Blo 774336 1161857 := bstep (se 2 (by rfl) ⟨435696, by rfl⟩ : syracuseStep 1161857 = 871393) B871393
theorem B1161875 : Blo 774336 1161875 := bstep (se 1 (by rfl) ⟨871406, by rfl⟩ : syracuseStep 1161875 = 1742813) B1742813
theorem B1161905 : Blo 774336 1161905 := bstep (se 2 (by rfl) ⟨435714, by rfl⟩ : syracuseStep 1161905 = 871429) B871429
theorem B1161923 : Blo 774336 1161923 := bstep (se 1 (by rfl) ⟨871442, by rfl⟩ : syracuseStep 1161923 = 1742885) B1742885
theorem B1161953 : Blo 774336 1161953 := bstep (se 2 (by rfl) ⟨435732, by rfl⟩ : syracuseStep 1161953 = 871465) B871465
theorem B1161971 : Blo 774336 1161971 := bstep (se 1 (by rfl) ⟨871478, by rfl⟩ : syracuseStep 1161971 = 1742957) B1742957
theorem B1162001 : Blo 774336 1162001 := bstep (se 2 (by rfl) ⟨435750, by rfl⟩ : syracuseStep 1162001 = 871501) B871501
theorem B1162019 : Blo 774336 1162019 := bstep (se 1 (by rfl) ⟨871514, by rfl⟩ : syracuseStep 1162019 = 1743029) B1743029
theorem B1162049 : Blo 774336 1162049 := bstep (se 2 (by rfl) ⟨435768, by rfl⟩ : syracuseStep 1162049 = 871537) B871537
theorem B1260353 : Blo 774336 1260353 := bstep (se 2 (by rfl) ⟨472632, by rfl⟩ : syracuseStep 1260353 = 945265) B945265
theorem B1162067 : Blo 774336 1162067 := bstep (se 1 (by rfl) ⟨871550, by rfl⟩ : syracuseStep 1162067 = 1743101) B1743101
theorem B1162097 : Blo 774336 1162097 := bstep (se 2 (by rfl) ⟨435786, by rfl⟩ : syracuseStep 1162097 = 871573) B871573
theorem B1162115 : Blo 774336 1162115 := bstep (se 1 (by rfl) ⟨871586, by rfl⟩ : syracuseStep 1162115 = 1743173) B1743173
theorem B1162145 : Blo 774336 1162145 := bstep (se 2 (by rfl) ⟨435804, by rfl⟩ : syracuseStep 1162145 = 871609) B871609
theorem B1162163 : Blo 774336 1162163 := bstep (se 1 (by rfl) ⟨871622, by rfl⟩ : syracuseStep 1162163 = 1743245) B1743245
theorem B1162193 : Blo 774336 1162193 := bstep (se 2 (by rfl) ⟨435822, by rfl⟩ : syracuseStep 1162193 = 871645) B871645
theorem B1162211 : Blo 774336 1162211 := bstep (se 1 (by rfl) ⟨871658, by rfl⟩ : syracuseStep 1162211 = 1743317) B1743317
theorem B1162241 : Blo 774336 1162241 := bstep (se 2 (by rfl) ⟨435840, by rfl⟩ : syracuseStep 1162241 = 871681) B871681
theorem B1162259 : Blo 774336 1162259 := bstep (se 1 (by rfl) ⟨871694, by rfl⟩ : syracuseStep 1162259 = 1743389) B1743389
theorem B1162289 : Blo 774336 1162289 := bstep (se 2 (by rfl) ⟨435858, by rfl⟩ : syracuseStep 1162289 = 871717) B871717
theorem B932915 : Blo 774336 932915 := bstep (se 1 (by rfl) ⟨699686, by rfl⟩ : syracuseStep 932915 = 1399373) B1399373
theorem B1162307 : Blo 774336 1162307 := bstep (se 1 (by rfl) ⟨871730, by rfl⟩ : syracuseStep 1162307 = 1743461) B1743461
theorem B1162337 : Blo 774336 1162337 := bstep (se 2 (by rfl) ⟨435876, by rfl⟩ : syracuseStep 1162337 = 871753) B871753
theorem B1162355 : Blo 774336 1162355 := bstep (se 1 (by rfl) ⟨871766, by rfl⟩ : syracuseStep 1162355 = 1743533) B1743533
theorem B1162385 : Blo 774336 1162385 := bstep (se 2 (by rfl) ⟨435894, by rfl⟩ : syracuseStep 1162385 = 871789) B871789
theorem B1162403 : Blo 774336 1162403 := bstep (se 1 (by rfl) ⟨871802, by rfl⟩ : syracuseStep 1162403 = 1743605) B1743605
theorem B2210989 : Blo 774336 2210989 := bstep (se 3 (by rfl) ⟨414560, by rfl⟩ : syracuseStep 2210989 = 829121) B829121
theorem B1162433 : Blo 774336 1162433 := bstep (se 2 (by rfl) ⟨435912, by rfl⟩ : syracuseStep 1162433 = 871825) B871825
theorem B1162451 : Blo 774336 1162451 := bstep (se 1 (by rfl) ⟨871838, by rfl⟩ : syracuseStep 1162451 = 1743677) B1743677
theorem B1162481 : Blo 774336 1162481 := bstep (se 2 (by rfl) ⟨435930, by rfl⟩ : syracuseStep 1162481 = 871861) B871861
theorem B1490179 : Blo 774336 1490179 := bstep (se 1 (by rfl) ⟨1117634, by rfl⟩ : syracuseStep 1490179 = 2235269) B2235269
theorem B1162499 : Blo 774336 1162499 := bstep (se 1 (by rfl) ⟨871874, by rfl⟩ : syracuseStep 1162499 = 1743749) B1743749
theorem B1162529 : Blo 774336 1162529 := bstep (se 2 (by rfl) ⟨435948, by rfl⟩ : syracuseStep 1162529 = 871897) B871897
theorem B1162547 : Blo 774336 1162547 := bstep (se 1 (by rfl) ⟨871910, by rfl⟩ : syracuseStep 1162547 = 1743821) B1743821
theorem B1162577 : Blo 774336 1162577 := bstep (se 2 (by rfl) ⟨435966, by rfl⟩ : syracuseStep 1162577 = 871933) B871933
theorem B1162595 : Blo 774336 1162595 := bstep (se 1 (by rfl) ⟨871946, by rfl⟩ : syracuseStep 1162595 = 1743893) B1743893
theorem B1162625 : Blo 774336 1162625 := bstep (se 2 (by rfl) ⟨435984, by rfl⟩ : syracuseStep 1162625 = 871969) B871969
theorem B933251 : Blo 774336 933251 := bstep (se 1 (by rfl) ⟨699938, by rfl⟩ : syracuseStep 933251 = 1399877) B1399877
theorem B1162643 : Blo 774336 1162643 := bstep (se 1 (by rfl) ⟨871982, by rfl⟩ : syracuseStep 1162643 = 1743965) B1743965
theorem B1162673 : Blo 774336 1162673 := bstep (se 2 (by rfl) ⟨436002, by rfl⟩ : syracuseStep 1162673 = 872005) B872005
theorem B1162691 : Blo 774336 1162691 := bstep (se 1 (by rfl) ⟨872018, by rfl⟩ : syracuseStep 1162691 = 1744037) B1744037
theorem B1064387 : Blo 774336 1064387 := bstep (se 1 (by rfl) ⟨798290, by rfl⟩ : syracuseStep 1064387 = 1596581) B1596581
theorem B1162721 : Blo 774336 1162721 := bstep (se 2 (by rfl) ⟨436020, by rfl⟩ : syracuseStep 1162721 = 872041) B872041
theorem B1162739 : Blo 774336 1162739 := bstep (se 1 (by rfl) ⟨872054, by rfl⟩ : syracuseStep 1162739 = 1744109) B1744109
theorem B1162769 : Blo 774336 1162769 := bstep (se 2 (by rfl) ⟨436038, by rfl⟩ : syracuseStep 1162769 = 872077) B872077
theorem B1162787 : Blo 774336 1162787 := bstep (se 1 (by rfl) ⟨872090, by rfl⟩ : syracuseStep 1162787 = 1744181) B1744181
theorem B1162817 : Blo 774336 1162817 := bstep (se 2 (by rfl) ⟨436056, by rfl⟩ : syracuseStep 1162817 = 872113) B872113
theorem B1162835 : Blo 774336 1162835 := bstep (se 1 (by rfl) ⟨872126, by rfl⟩ : syracuseStep 1162835 = 1744253) B1744253
theorem B3358307 : Blo 774336 3358307 := bstep (se 1 (by rfl) ⟨2518730, by rfl⟩ : syracuseStep 3358307 = 5037461) B5037461
theorem B1162865 : Blo 774336 1162865 := bstep (se 2 (by rfl) ⟨436074, by rfl⟩ : syracuseStep 1162865 = 872149) B872149
theorem B1162883 : Blo 774336 1162883 := bstep (se 1 (by rfl) ⟨872162, by rfl⟩ : syracuseStep 1162883 = 1744325) B1744325
theorem B1162913 : Blo 774336 1162913 := bstep (se 2 (by rfl) ⟨436092, by rfl⟩ : syracuseStep 1162913 = 872185) B872185
theorem B1162931 : Blo 774336 1162931 := bstep (se 1 (by rfl) ⟨872198, by rfl⟩ : syracuseStep 1162931 = 1744397) B1744397
theorem B1162961 : Blo 774336 1162961 := bstep (se 2 (by rfl) ⟨436110, by rfl⟩ : syracuseStep 1162961 = 872221) B872221
theorem B5881571 : Blo 774336 5881571 := bstep (se 1 (by rfl) ⟨4411178, by rfl⟩ : syracuseStep 5881571 = 8822357) B8822357
theorem B1162979 : Blo 774336 1162979 := bstep (se 1 (by rfl) ⟨872234, by rfl⟩ : syracuseStep 1162979 = 1744469) B1744469
theorem B1163009 : Blo 774336 1163009 := bstep (se 2 (by rfl) ⟨436128, by rfl⟩ : syracuseStep 1163009 = 872257) B872257
theorem B1163027 : Blo 774336 1163027 := bstep (se 1 (by rfl) ⟨872270, by rfl⟩ : syracuseStep 1163027 = 1744541) B1744541
theorem B1163057 : Blo 774336 1163057 := bstep (se 2 (by rfl) ⟨436146, by rfl⟩ : syracuseStep 1163057 = 872293) B872293
theorem B1163075 : Blo 774336 1163075 := bstep (se 1 (by rfl) ⟨872306, by rfl⟩ : syracuseStep 1163075 = 1744613) B1744613
theorem B1163105 : Blo 774336 1163105 := bstep (se 2 (by rfl) ⟨436164, by rfl⟩ : syracuseStep 1163105 = 872329) B872329
theorem B1163123 : Blo 774336 1163123 := bstep (se 1 (by rfl) ⟨872342, by rfl⟩ : syracuseStep 1163123 = 1744685) B1744685
theorem B1163153 : Blo 774336 1163153 := bstep (se 2 (by rfl) ⟨436182, by rfl⟩ : syracuseStep 1163153 = 872365) B872365
theorem B1163171 : Blo 774336 1163171 := bstep (se 1 (by rfl) ⟨872378, by rfl⟩ : syracuseStep 1163171 = 1744757) B1744757
theorem B1654705 : Blo 774336 1654705 := bstep (se 2 (by rfl) ⟨620514, by rfl⟩ : syracuseStep 1654705 = 1241029) B1241029
theorem B1163201 : Blo 774336 1163201 := bstep (se 2 (by rfl) ⟨436200, by rfl⟩ : syracuseStep 1163201 = 872401) B872401
theorem B1163219 : Blo 774336 1163219 := bstep (se 1 (by rfl) ⟨872414, by rfl⟩ : syracuseStep 1163219 = 1744829) B1744829
theorem B1163249 : Blo 774336 1163249 := bstep (se 2 (by rfl) ⟨436218, by rfl⟩ : syracuseStep 1163249 = 872437) B872437
theorem B1163267 : Blo 774336 1163267 := bstep (se 1 (by rfl) ⟨872450, by rfl⟩ : syracuseStep 1163267 = 1744901) B1744901
theorem B1163297 : Blo 774336 1163297 := bstep (se 2 (by rfl) ⟨436236, by rfl⟩ : syracuseStep 1163297 = 872473) B872473
theorem B1163315 : Blo 774336 1163315 := bstep (se 1 (by rfl) ⟨872486, by rfl⟩ : syracuseStep 1163315 = 1744973) B1744973
theorem B1163345 : Blo 774336 1163345 := bstep (se 2 (by rfl) ⟨436254, by rfl⟩ : syracuseStep 1163345 = 872509) B872509
theorem B1163363 : Blo 774336 1163363 := bstep (se 1 (by rfl) ⟨872522, by rfl⟩ : syracuseStep 1163363 = 1745045) B1745045
theorem B1163393 : Blo 774336 1163393 := bstep (se 2 (by rfl) ⟨436272, by rfl⟩ : syracuseStep 1163393 = 872545) B872545
theorem B1163411 : Blo 774336 1163411 := bstep (se 1 (by rfl) ⟨872558, by rfl⟩ : syracuseStep 1163411 = 1745117) B1745117
theorem B1163441 : Blo 774336 1163441 := bstep (se 2 (by rfl) ⟨436290, by rfl⟩ : syracuseStep 1163441 = 872581) B872581
theorem B1163459 : Blo 774336 1163459 := bstep (se 1 (by rfl) ⟨872594, by rfl⟩ : syracuseStep 1163459 = 1745189) B1745189
theorem B2212049 : Blo 774336 2212049 := bstep (se 2 (by rfl) ⟨829518, by rfl⟩ : syracuseStep 2212049 = 1659037) B1659037
theorem B1163489 : Blo 774336 1163489 := bstep (se 2 (by rfl) ⟨436308, by rfl⟩ : syracuseStep 1163489 = 872617) B872617
theorem B1163507 : Blo 774336 1163507 := bstep (se 1 (by rfl) ⟨872630, by rfl⟩ : syracuseStep 1163507 = 1745261) B1745261
theorem B1163537 : Blo 774336 1163537 := bstep (se 2 (by rfl) ⟨436326, by rfl⟩ : syracuseStep 1163537 = 872653) B872653
theorem B1163555 : Blo 774336 1163555 := bstep (se 1 (by rfl) ⟨872666, by rfl⟩ : syracuseStep 1163555 = 1745333) B1745333
theorem B1163585 : Blo 774336 1163585 := bstep (se 2 (by rfl) ⟨436344, by rfl⟩ : syracuseStep 1163585 = 872689) B872689
theorem B1163603 : Blo 774336 1163603 := bstep (se 1 (by rfl) ⟨872702, by rfl⟩ : syracuseStep 1163603 = 1745405) B1745405
theorem B1163633 : Blo 774336 1163633 := bstep (se 2 (by rfl) ⟨436362, by rfl⟩ : syracuseStep 1163633 = 872725) B872725
theorem B1163651 : Blo 774336 1163651 := bstep (se 1 (by rfl) ⟨872738, by rfl⟩ : syracuseStep 1163651 = 1745477) B1745477
theorem B1163681 : Blo 774336 1163681 := bstep (se 2 (by rfl) ⟨436380, by rfl⟩ : syracuseStep 1163681 = 872761) B872761
theorem B1163699 : Blo 774336 1163699 := bstep (se 1 (by rfl) ⟨872774, by rfl⟩ : syracuseStep 1163699 = 1745549) B1745549
theorem B1163729 : Blo 774336 1163729 := bstep (se 2 (by rfl) ⟨436398, by rfl⟩ : syracuseStep 1163729 = 872797) B872797
theorem B1163747 : Blo 774336 1163747 := bstep (se 1 (by rfl) ⟨872810, by rfl⟩ : syracuseStep 1163747 = 1745621) B1745621
theorem B1163777 : Blo 774336 1163777 := bstep (se 2 (by rfl) ⟨436416, by rfl⟩ : syracuseStep 1163777 = 872833) B872833
theorem B1163795 : Blo 774336 1163795 := bstep (se 1 (by rfl) ⟨872846, by rfl⟩ : syracuseStep 1163795 = 1745693) B1745693
theorem B1163825 : Blo 774336 1163825 := bstep (se 2 (by rfl) ⟨436434, by rfl⟩ : syracuseStep 1163825 = 872869) B872869
theorem B1163843 : Blo 774336 1163843 := bstep (se 1 (by rfl) ⟨872882, by rfl⟩ : syracuseStep 1163843 = 1745765) B1745765
theorem B1163873 : Blo 774336 1163873 := bstep (se 2 (by rfl) ⟨436452, by rfl⟩ : syracuseStep 1163873 = 872905) B872905
theorem B1163891 : Blo 774336 1163891 := bstep (se 1 (by rfl) ⟨872918, by rfl⟩ : syracuseStep 1163891 = 1745837) B1745837
theorem B1327745 : Blo 774336 1327745 := bstep (se 2 (by rfl) ⟨497904, by rfl⟩ : syracuseStep 1327745 = 995809) B995809
theorem B1163921 : Blo 774336 1163921 := bstep (se 2 (by rfl) ⟨436470, by rfl⟩ : syracuseStep 1163921 = 872941) B872941
theorem B1163939 : Blo 774336 1163939 := bstep (se 1 (by rfl) ⟨872954, by rfl⟩ : syracuseStep 1163939 = 1745909) B1745909
theorem B1163969 : Blo 774336 1163969 := bstep (se 2 (by rfl) ⟨436488, by rfl⟩ : syracuseStep 1163969 = 872977) B872977
theorem B1655491 : Blo 774336 1655491 := bstep (se 1 (by rfl) ⟨1241618, by rfl⟩ : syracuseStep 1655491 = 2483237) B2483237
theorem B1163987 : Blo 774336 1163987 := bstep (se 1 (by rfl) ⟨872990, by rfl⟩ : syracuseStep 1163987 = 1745981) B1745981
theorem B1164017 : Blo 774336 1164017 := bstep (se 2 (by rfl) ⟨436506, by rfl⟩ : syracuseStep 1164017 = 873013) B873013
theorem B1164035 : Blo 774336 1164035 := bstep (se 1 (by rfl) ⟨873026, by rfl⟩ : syracuseStep 1164035 = 1746053) B1746053
theorem B1164065 : Blo 774336 1164065 := bstep (se 2 (by rfl) ⟨436524, by rfl⟩ : syracuseStep 1164065 = 873049) B873049
theorem B1164083 : Blo 774336 1164083 := bstep (se 1 (by rfl) ⟨873062, by rfl⟩ : syracuseStep 1164083 = 1746125) B1746125
theorem B1164113 : Blo 774336 1164113 := bstep (se 2 (by rfl) ⟨436542, by rfl⟩ : syracuseStep 1164113 = 873085) B873085
theorem B1065811 : Blo 774336 1065811 := bstep (se 1 (by rfl) ⟨799358, by rfl⟩ : syracuseStep 1065811 = 1598717) B1598717
theorem B1164131 : Blo 774336 1164131 := bstep (se 1 (by rfl) ⟨873098, by rfl⟩ : syracuseStep 1164131 = 1746197) B1746197
theorem B2245475 : Blo 774336 2245475 := bstep (se 1 (by rfl) ⟨1684106, by rfl⟩ : syracuseStep 2245475 = 3368213) B3368213
theorem B2212721 : Blo 774336 2212721 := bstep (se 2 (by rfl) ⟨829770, by rfl⟩ : syracuseStep 2212721 = 1659541) B1659541
theorem B1164161 : Blo 774336 1164161 := bstep (se 2 (by rfl) ⟨436560, by rfl⟩ : syracuseStep 1164161 = 873121) B873121
theorem B1164179 : Blo 774336 1164179 := bstep (se 1 (by rfl) ⟨873134, by rfl⟩ : syracuseStep 1164179 = 1746269) B1746269
theorem B1164209 : Blo 774336 1164209 := bstep (se 2 (by rfl) ⟨436578, by rfl⟩ : syracuseStep 1164209 = 873157) B873157
theorem B1164227 : Blo 774336 1164227 := bstep (se 1 (by rfl) ⟨873170, by rfl⟩ : syracuseStep 1164227 = 1746341) B1746341
theorem B2802637 : Blo 774336 2802637 := bstep (se 3 (by rfl) ⟨525494, by rfl⟩ : syracuseStep 2802637 = 1050989) B1050989
theorem B1164257 : Blo 774336 1164257 := bstep (se 2 (by rfl) ⟨436596, by rfl⟩ : syracuseStep 1164257 = 873193) B873193
theorem B1164275 : Blo 774336 1164275 := bstep (se 1 (by rfl) ⟨873206, by rfl⟩ : syracuseStep 1164275 = 1746413) B1746413
theorem B1164305 : Blo 774336 1164305 := bstep (se 2 (by rfl) ⟨436614, by rfl⟩ : syracuseStep 1164305 = 873229) B873229
theorem B1164323 : Blo 774336 1164323 := bstep (se 1 (by rfl) ⟨873242, by rfl⟩ : syracuseStep 1164323 = 1746485) B1746485
theorem B1164353 : Blo 774336 1164353 := bstep (se 2 (by rfl) ⟨436632, by rfl⟩ : syracuseStep 1164353 = 873265) B873265
theorem B1164371 : Blo 774336 1164371 := bstep (se 1 (by rfl) ⟨873278, by rfl⟩ : syracuseStep 1164371 = 1746557) B1746557
theorem B7554161 : Blo 774336 7554161 := bstep (se 2 (by rfl) ⟨2832810, by rfl⟩ : syracuseStep 7554161 = 5665621) B5665621
theorem B1164401 : Blo 774336 1164401 := bstep (se 2 (by rfl) ⟨436650, by rfl⟩ : syracuseStep 1164401 = 873301) B873301
theorem B1164419 : Blo 774336 1164419 := bstep (se 1 (by rfl) ⟨873314, by rfl⟩ : syracuseStep 1164419 = 1746629) B1746629
theorem B1164449 : Blo 774336 1164449 := bstep (se 2 (by rfl) ⟨436668, by rfl⟩ : syracuseStep 1164449 = 873337) B873337
theorem B1164467 : Blo 774336 1164467 := bstep (se 1 (by rfl) ⟨873350, by rfl⟩ : syracuseStep 1164467 = 1746701) B1746701
theorem B1164497 : Blo 774336 1164497 := bstep (se 2 (by rfl) ⟨436686, by rfl⟩ : syracuseStep 1164497 = 873373) B873373
theorem B1164515 : Blo 774336 1164515 := bstep (se 1 (by rfl) ⟨873386, by rfl⟩ : syracuseStep 1164515 = 1746773) B1746773
theorem B1164545 : Blo 774336 1164545 := bstep (se 2 (by rfl) ⟨436704, by rfl⟩ : syracuseStep 1164545 = 873409) B873409
theorem B1164563 : Blo 774336 1164563 := bstep (se 1 (by rfl) ⟨873422, by rfl⟩ : syracuseStep 1164563 = 1746845) B1746845
theorem B1164593 : Blo 774336 1164593 := bstep (se 2 (by rfl) ⟨436722, by rfl⟩ : syracuseStep 1164593 = 873445) B873445
theorem B1164611 : Blo 774336 1164611 := bstep (se 1 (by rfl) ⟨873458, by rfl⟩ : syracuseStep 1164611 = 1746917) B1746917
theorem B1164641 : Blo 774336 1164641 := bstep (se 2 (by rfl) ⟨436740, by rfl⟩ : syracuseStep 1164641 = 873481) B873481
theorem B1164659 : Blo 774336 1164659 := bstep (se 1 (by rfl) ⟨873494, by rfl⟩ : syracuseStep 1164659 = 1746989) B1746989
theorem B1656209 : Blo 774336 1656209 := bstep (se 2 (by rfl) ⟨621078, by rfl⟩ : syracuseStep 1656209 = 1242157) B1242157
theorem B1164689 : Blo 774336 1164689 := bstep (se 2 (by rfl) ⟨436758, by rfl⟩ : syracuseStep 1164689 = 873517) B873517
theorem B1164707 : Blo 774336 1164707 := bstep (se 1 (by rfl) ⟨873530, by rfl⟩ : syracuseStep 1164707 = 1747061) B1747061
theorem B1164737 : Blo 774336 1164737 := bstep (se 2 (by rfl) ⟨436776, by rfl⟩ : syracuseStep 1164737 = 873553) B873553
theorem B11322821 : Blo 774336 11322821 := bstep (se 4 (by rfl) ⟨1061514, by rfl⟩ : syracuseStep 11322821 = 2123029) B2123029
theorem B1164755 : Blo 774336 1164755 := bstep (se 1 (by rfl) ⟨873566, by rfl⟩ : syracuseStep 1164755 = 1747133) B1747133
theorem B2835953 : Blo 774336 2835953 := bstep (se 2 (by rfl) ⟨1063482, by rfl⟩ : syracuseStep 2835953 = 2126965) B2126965
theorem B1164785 : Blo 774336 1164785 := bstep (se 2 (by rfl) ⟨436794, by rfl⟩ : syracuseStep 1164785 = 873589) B873589
theorem B1164803 : Blo 774336 1164803 := bstep (se 1 (by rfl) ⟨873602, by rfl⟩ : syracuseStep 1164803 = 1747205) B1747205
theorem B1263107 : Blo 774336 1263107 := bstep (se 1 (by rfl) ⟨947330, by rfl⟩ : syracuseStep 1263107 = 1894661) B1894661
theorem B1164833 : Blo 774336 1164833 := bstep (se 2 (by rfl) ⟨436812, by rfl⟩ : syracuseStep 1164833 = 873625) B873625
theorem B1164851 : Blo 774336 1164851 := bstep (se 1 (by rfl) ⟨873638, by rfl⟩ : syracuseStep 1164851 = 1747277) B1747277
theorem B1164881 : Blo 774336 1164881 := bstep (se 2 (by rfl) ⟨436830, by rfl⟩ : syracuseStep 1164881 = 873661) B873661
theorem B1164899 : Blo 774336 1164899 := bstep (se 1 (by rfl) ⟨873674, by rfl⟩ : syracuseStep 1164899 = 1747349) B1747349
theorem B1164929 : Blo 774336 1164929 := bstep (se 2 (by rfl) ⟨436848, by rfl⟩ : syracuseStep 1164929 = 873697) B873697
theorem B2213507 : Blo 774336 2213507 := bstep (se 1 (by rfl) ⟨1660130, by rfl⟩ : syracuseStep 2213507 = 3320261) B3320261
theorem B1164947 : Blo 774336 1164947 := bstep (se 1 (by rfl) ⟨873710, by rfl⟩ : syracuseStep 1164947 = 1747421) B1747421
theorem B1164977 : Blo 774336 1164977 := bstep (se 2 (by rfl) ⟨436866, by rfl⟩ : syracuseStep 1164977 = 873733) B873733
theorem B1164995 : Blo 774336 1164995 := bstep (se 1 (by rfl) ⟨873746, by rfl⟩ : syracuseStep 1164995 = 1747493) B1747493
theorem B1165025 : Blo 774336 1165025 := bstep (se 2 (by rfl) ⟨436884, by rfl⟩ : syracuseStep 1165025 = 873769) B873769
theorem B1165043 : Blo 774336 1165043 := bstep (se 1 (by rfl) ⟨873782, by rfl⟩ : syracuseStep 1165043 = 1747565) B1747565
theorem B1165073 : Blo 774336 1165073 := bstep (se 2 (by rfl) ⟨436902, by rfl⟩ : syracuseStep 1165073 = 873805) B873805
theorem B1165091 : Blo 774336 1165091 := bstep (se 1 (by rfl) ⟨873818, by rfl⟩ : syracuseStep 1165091 = 1747637) B1747637
theorem B1165121 : Blo 774336 1165121 := bstep (se 2 (by rfl) ⟨436920, by rfl⟩ : syracuseStep 1165121 = 873841) B873841
theorem B1165139 : Blo 774336 1165139 := bstep (se 1 (by rfl) ⟨873854, by rfl⟩ : syracuseStep 1165139 = 1747709) B1747709
theorem B1165169 : Blo 774336 1165169 := bstep (se 2 (by rfl) ⟨436938, by rfl⟩ : syracuseStep 1165169 = 873877) B873877
theorem B1165187 : Blo 774336 1165187 := bstep (se 1 (by rfl) ⟨873890, by rfl⟩ : syracuseStep 1165187 = 1747781) B1747781
theorem B1656721 : Blo 774336 1656721 := bstep (se 2 (by rfl) ⟨621270, by rfl⟩ : syracuseStep 1656721 = 1242541) B1242541
theorem B1165217 : Blo 774336 1165217 := bstep (se 2 (by rfl) ⟨436956, by rfl⟩ : syracuseStep 1165217 = 873913) B873913
theorem B1165235 : Blo 774336 1165235 := bstep (se 1 (by rfl) ⟨873926, by rfl⟩ : syracuseStep 1165235 = 1747853) B1747853
theorem B2213837 : Blo 774336 2213837 := bstep (se 3 (by rfl) ⟨415094, by rfl⟩ : syracuseStep 2213837 = 830189) B830189
theorem B1165265 : Blo 774336 1165265 := bstep (se 2 (by rfl) ⟨436974, by rfl⟩ : syracuseStep 1165265 = 873949) B873949
theorem B1165283 : Blo 774336 1165283 := bstep (se 1 (by rfl) ⟨873962, by rfl⟩ : syracuseStep 1165283 = 1747925) B1747925
theorem B1165313 : Blo 774336 1165313 := bstep (se 2 (by rfl) ⟨436992, by rfl⟩ : syracuseStep 1165313 = 873985) B873985
theorem B2213905 : Blo 774336 2213905 := bstep (se 2 (by rfl) ⟨830214, by rfl⟩ : syracuseStep 2213905 = 1660429) B1660429
theorem B1165331 : Blo 774336 1165331 := bstep (se 1 (by rfl) ⟨873998, by rfl⟩ : syracuseStep 1165331 = 1747997) B1747997
theorem B1165361 : Blo 774336 1165361 := bstep (se 2 (by rfl) ⟨437010, by rfl⟩ : syracuseStep 1165361 = 874021) B874021
theorem B1165379 : Blo 774336 1165379 := bstep (se 1 (by rfl) ⟨874034, by rfl⟩ : syracuseStep 1165379 = 1748069) B1748069
theorem B1165409 : Blo 774336 1165409 := bstep (se 2 (by rfl) ⟨437028, by rfl⟩ : syracuseStep 1165409 = 874057) B874057
theorem B53889137 : Blo 774336 53889137 := bstep (se 2 (by rfl) ⟨20208426, by rfl⟩ : syracuseStep 53889137 = 40416853) B40416853
theorem B1165427 : Blo 774336 1165427 := bstep (se 1 (by rfl) ⟨874070, by rfl⟩ : syracuseStep 1165427 = 1748141) B1748141
theorem B1165457 : Blo 774336 1165457 := bstep (se 2 (by rfl) ⟨437046, by rfl⟩ : syracuseStep 1165457 = 874093) B874093
theorem B1165475 : Blo 774336 1165475 := bstep (se 1 (by rfl) ⟨874106, by rfl⟩ : syracuseStep 1165475 = 1748213) B1748213
theorem B4475057 : Blo 774336 4475057 := bstep (se 2 (by rfl) ⟨1678146, by rfl⟩ : syracuseStep 4475057 = 3356293) B3356293
theorem B1165505 : Blo 774336 1165505 := bstep (se 2 (by rfl) ⟨437064, by rfl⟩ : syracuseStep 1165505 = 874129) B874129
theorem B1165523 : Blo 774336 1165523 := bstep (se 1 (by rfl) ⟨874142, by rfl⟩ : syracuseStep 1165523 = 1748285) B1748285
theorem B1493219 : Blo 774336 1493219 := bstep (se 1 (by rfl) ⟨1119914, by rfl⟩ : syracuseStep 1493219 = 2239829) B2239829
theorem B3786979 : Blo 774336 3786979 := bstep (se 1 (by rfl) ⟨2840234, by rfl⟩ : syracuseStep 3786979 = 5680469) B5680469
theorem B7948529 : Blo 774336 7948529 := bstep (se 2 (by rfl) ⟨2980698, by rfl⟩ : syracuseStep 7948529 = 5961397) B5961397
theorem B1165553 : Blo 774336 1165553 := bstep (se 2 (by rfl) ⟨437082, by rfl⟩ : syracuseStep 1165553 = 874165) B874165
theorem B1165571 : Blo 774336 1165571 := bstep (se 1 (by rfl) ⟨874178, by rfl⟩ : syracuseStep 1165571 = 1748357) B1748357
theorem B1165601 : Blo 774336 1165601 := bstep (se 2 (by rfl) ⟨437100, by rfl⟩ : syracuseStep 1165601 = 874201) B874201
theorem B2214179 : Blo 774336 2214179 := bstep (se 1 (by rfl) ⟨1660634, by rfl⟩ : syracuseStep 2214179 = 3321269) B3321269
theorem B1165619 : Blo 774336 1165619 := bstep (se 1 (by rfl) ⟨874214, by rfl⟩ : syracuseStep 1165619 = 1748429) B1748429
theorem B1165649 : Blo 774336 1165649 := bstep (se 2 (by rfl) ⟨437118, by rfl⟩ : syracuseStep 1165649 = 874237) B874237
theorem B1165667 : Blo 774336 1165667 := bstep (se 1 (by rfl) ⟨874250, by rfl⟩ : syracuseStep 1165667 = 1748501) B1748501
theorem B1165697 : Blo 774336 1165697 := bstep (se 2 (by rfl) ⟨437136, by rfl⟩ : syracuseStep 1165697 = 874273) B874273
theorem B1165715 : Blo 774336 1165715 := bstep (se 1 (by rfl) ⟨874286, by rfl⟩ : syracuseStep 1165715 = 1748573) B1748573
theorem B1165745 : Blo 774336 1165745 := bstep (se 2 (by rfl) ⟨437154, by rfl⟩ : syracuseStep 1165745 = 874309) B874309
theorem B1165763 : Blo 774336 1165763 := bstep (se 1 (by rfl) ⟨874322, by rfl⟩ : syracuseStep 1165763 = 1748645) B1748645
theorem B1165793 : Blo 774336 1165793 := bstep (se 2 (by rfl) ⟨437172, by rfl⟩ : syracuseStep 1165793 = 874345) B874345
theorem B4966883 : Blo 774336 4966883 := bstep (se 1 (by rfl) ⟨3725162, by rfl⟩ : syracuseStep 4966883 = 7450325) B7450325
theorem B1165811 : Blo 774336 1165811 := bstep (se 1 (by rfl) ⟨874358, by rfl⟩ : syracuseStep 1165811 = 1748717) B1748717
theorem B1165841 : Blo 774336 1165841 := bstep (se 2 (by rfl) ⟨437190, by rfl⟩ : syracuseStep 1165841 = 874381) B874381
theorem B1165859 : Blo 774336 1165859 := bstep (se 1 (by rfl) ⟨874394, by rfl⟩ : syracuseStep 1165859 = 1748789) B1748789
theorem B1165889 : Blo 774336 1165889 := bstep (se 2 (by rfl) ⟨437208, by rfl⟩ : syracuseStep 1165889 = 874417) B874417
theorem B1165907 : Blo 774336 1165907 := bstep (se 1 (by rfl) ⟨874430, by rfl⟩ : syracuseStep 1165907 = 1748861) B1748861
theorem B1165937 : Blo 774336 1165937 := bstep (se 2 (by rfl) ⟨437226, by rfl⟩ : syracuseStep 1165937 = 874453) B874453
theorem B1165955 : Blo 774336 1165955 := bstep (se 1 (by rfl) ⟨874466, by rfl⟩ : syracuseStep 1165955 = 1748933) B1748933
theorem B3361421 : Blo 774336 3361421 := bstep (se 3 (by rfl) ⟨630266, by rfl⟩ : syracuseStep 3361421 = 1260533) B1260533
theorem B1165985 : Blo 774336 1165985 := bstep (se 2 (by rfl) ⟨437244, by rfl⟩ : syracuseStep 1165985 = 874489) B874489
theorem B1166003 : Blo 774336 1166003 := bstep (se 1 (by rfl) ⟨874502, by rfl⟩ : syracuseStep 1166003 = 1749005) B1749005
theorem B1395409 : Blo 774336 1395409 := bstep (se 2 (by rfl) ⟨523278, by rfl⟩ : syracuseStep 1395409 = 1046557) B1046557
theorem B1166033 : Blo 774336 1166033 := bstep (se 2 (by rfl) ⟨437262, by rfl⟩ : syracuseStep 1166033 = 874525) B874525
theorem B1166051 : Blo 774336 1166051 := bstep (se 1 (by rfl) ⟨874538, by rfl⟩ : syracuseStep 1166051 = 1749077) B1749077
theorem B1166081 : Blo 774336 1166081 := bstep (se 2 (by rfl) ⟨437280, by rfl⟩ : syracuseStep 1166081 = 874561) B874561
theorem B1166099 : Blo 774336 1166099 := bstep (se 1 (by rfl) ⟨874574, by rfl⟩ : syracuseStep 1166099 = 1749149) B1749149
theorem B1166129 : Blo 774336 1166129 := bstep (se 2 (by rfl) ⟨437298, by rfl⟩ : syracuseStep 1166129 = 874597) B874597
theorem B1166147 : Blo 774336 1166147 := bstep (se 1 (by rfl) ⟨874610, by rfl⟩ : syracuseStep 1166147 = 1749221) B1749221
theorem B1166177 : Blo 774336 1166177 := bstep (se 2 (by rfl) ⟨437316, by rfl⟩ : syracuseStep 1166177 = 874633) B874633
theorem B871267 : Blo 774336 871267 := bstep (se 1 (by rfl) ⟨653450, by rfl⟩ : syracuseStep 871267 = 1306901) B1306901
theorem B6638435 : Blo 774336 6638435 := bstep (se 1 (by rfl) ⟨4978826, by rfl⟩ : syracuseStep 6638435 = 9957653) B9957653
theorem B1166195 : Blo 774336 1166195 := bstep (se 1 (by rfl) ⟨874646, by rfl⟩ : syracuseStep 1166195 = 1749293) B1749293
theorem B1166225 : Blo 774336 1166225 := bstep (se 2 (by rfl) ⟨437334, by rfl⟩ : syracuseStep 1166225 = 874669) B874669
theorem B1166243 : Blo 774336 1166243 := bstep (se 1 (by rfl) ⟨874682, by rfl⟩ : syracuseStep 1166243 = 1749365) B1749365
theorem B4967345 : Blo 774336 4967345 := bstep (se 2 (by rfl) ⟨1862754, by rfl⟩ : syracuseStep 4967345 = 3725509) B3725509
theorem B1166273 : Blo 774336 1166273 := bstep (se 2 (by rfl) ⟨437352, by rfl⟩ : syracuseStep 1166273 = 874705) B874705
theorem B1166291 : Blo 774336 1166291 := bstep (se 1 (by rfl) ⟨874718, by rfl⟩ : syracuseStep 1166291 = 1749437) B1749437
theorem B1166321 : Blo 774336 1166321 := bstep (se 2 (by rfl) ⟨437370, by rfl⟩ : syracuseStep 1166321 = 874741) B874741
theorem B871411 : Blo 774336 871411 := bstep (se 1 (by rfl) ⟨653558, by rfl⟩ : syracuseStep 871411 = 1307117) B1307117
theorem B1166339 : Blo 774336 1166339 := bstep (se 1 (by rfl) ⟨874754, by rfl⟩ : syracuseStep 1166339 = 1749509) B1749509
theorem B1166369 : Blo 774336 1166369 := bstep (se 2 (by rfl) ⟨437388, by rfl⟩ : syracuseStep 1166369 = 874777) B874777
theorem B1166387 : Blo 774336 1166387 := bstep (se 1 (by rfl) ⟨874790, by rfl⟩ : syracuseStep 1166387 = 1749581) B1749581
theorem B1166417 : Blo 774336 1166417 := bstep (se 2 (by rfl) ⟨437406, by rfl⟩ : syracuseStep 1166417 = 874813) B874813
theorem B1166435 : Blo 774336 1166435 := bstep (se 1 (by rfl) ⟨874826, by rfl⟩ : syracuseStep 1166435 = 1749653) B1749653
theorem B2215021 : Blo 774336 2215021 := bstep (se 3 (by rfl) ⟨415316, by rfl⟩ : syracuseStep 2215021 = 830633) B830633
theorem B1166465 : Blo 774336 1166465 := bstep (se 2 (by rfl) ⟨437424, by rfl⟩ : syracuseStep 1166465 = 874849) B874849
theorem B871555 : Blo 774336 871555 := bstep (se 1 (by rfl) ⟨653666, by rfl⟩ : syracuseStep 871555 = 1307333) B1307333
theorem B1166483 : Blo 774336 1166483 := bstep (se 1 (by rfl) ⟨874862, by rfl⟩ : syracuseStep 1166483 = 1749725) B1749725
theorem B1166513 : Blo 774336 1166513 := bstep (se 2 (by rfl) ⟨437442, by rfl⟩ : syracuseStep 1166513 = 874885) B874885
theorem B1166531 : Blo 774336 1166531 := bstep (se 1 (by rfl) ⟨874898, by rfl⟩ : syracuseStep 1166531 = 1749797) B1749797
theorem B1166561 : Blo 774336 1166561 := bstep (se 2 (by rfl) ⟨437460, by rfl⟩ : syracuseStep 1166561 = 874921) B874921
theorem B1166579 : Blo 774336 1166579 := bstep (se 1 (by rfl) ⟨874934, by rfl⟩ : syracuseStep 1166579 = 1749869) B1749869
theorem B2215181 : Blo 774336 2215181 := bstep (se 3 (by rfl) ⟨415346, by rfl⟩ : syracuseStep 2215181 = 830693) B830693
theorem B1166609 : Blo 774336 1166609 := bstep (se 2 (by rfl) ⟨437478, by rfl⟩ : syracuseStep 1166609 = 874957) B874957
theorem B871699 : Blo 774336 871699 := bstep (se 1 (by rfl) ⟨653774, by rfl⟩ : syracuseStep 871699 = 1307549) B1307549
theorem B1133843 : Blo 774336 1133843 := bstep (se 1 (by rfl) ⟨850382, by rfl⟩ : syracuseStep 1133843 = 1700765) B1700765
theorem B1166627 : Blo 774336 1166627 := bstep (se 1 (by rfl) ⟨874970, by rfl⟩ : syracuseStep 1166627 = 1749941) B1749941
theorem B1166657 : Blo 774336 1166657 := bstep (se 2 (by rfl) ⟨437496, by rfl⟩ : syracuseStep 1166657 = 874993) B874993
theorem B1166675 : Blo 774336 1166675 := bstep (se 1 (by rfl) ⟨875006, by rfl⟩ : syracuseStep 1166675 = 1750013) B1750013
theorem B1658225 : Blo 774336 1658225 := bstep (se 2 (by rfl) ⟨621834, by rfl⟩ : syracuseStep 1658225 = 1243669) B1243669
theorem B1166705 : Blo 774336 1166705 := bstep (se 2 (by rfl) ⟨437514, by rfl⟩ : syracuseStep 1166705 = 875029) B875029
theorem B1166723 : Blo 774336 1166723 := bstep (se 1 (by rfl) ⟨875042, by rfl⟩ : syracuseStep 1166723 = 1750085) B1750085
theorem B1166753 : Blo 774336 1166753 := bstep (se 2 (by rfl) ⟨437532, by rfl⟩ : syracuseStep 1166753 = 875065) B875065
theorem B871843 : Blo 774336 871843 := bstep (se 1 (by rfl) ⟨653882, by rfl⟩ : syracuseStep 871843 = 1307765) B1307765
theorem B1166771 : Blo 774336 1166771 := bstep (se 1 (by rfl) ⟨875078, by rfl⟩ : syracuseStep 1166771 = 1750157) B1750157
theorem B2215363 : Blo 774336 2215363 := bstep (se 1 (by rfl) ⟨1661522, by rfl⟩ : syracuseStep 2215363 = 3323045) B3323045
theorem B1166801 : Blo 774336 1166801 := bstep (se 2 (by rfl) ⟨437550, by rfl⟩ : syracuseStep 1166801 = 875101) B875101
theorem B1166819 : Blo 774336 1166819 := bstep (se 1 (by rfl) ⟨875114, by rfl⟩ : syracuseStep 1166819 = 1750229) B1750229
theorem B1166849 : Blo 774336 1166849 := bstep (se 2 (by rfl) ⟨437568, by rfl⟩ : syracuseStep 1166849 = 875137) B875137
theorem B1166867 : Blo 774336 1166867 := bstep (se 1 (by rfl) ⟨875150, by rfl⟩ : syracuseStep 1166867 = 1750301) B1750301
theorem B1166897 : Blo 774336 1166897 := bstep (se 2 (by rfl) ⟨437586, by rfl⟩ : syracuseStep 1166897 = 875173) B875173
theorem B871987 : Blo 774336 871987 := bstep (se 1 (by rfl) ⟨653990, by rfl⟩ : syracuseStep 871987 = 1307981) B1307981
theorem B1166915 : Blo 774336 1166915 := bstep (se 1 (by rfl) ⟨875186, by rfl⟩ : syracuseStep 1166915 = 1750373) B1750373
theorem B1166945 : Blo 774336 1166945 := bstep (se 2 (by rfl) ⟨437604, by rfl⟩ : syracuseStep 1166945 = 875209) B875209
theorem B1166963 : Blo 774336 1166963 := bstep (se 1 (by rfl) ⟨875222, by rfl⟩ : syracuseStep 1166963 = 1750445) B1750445
theorem B1166993 : Blo 774336 1166993 := bstep (se 2 (by rfl) ⟨437622, by rfl⟩ : syracuseStep 1166993 = 875245) B875245
theorem B4411043 : Blo 774336 4411043 := bstep (se 1 (by rfl) ⟨3308282, by rfl⟩ : syracuseStep 4411043 = 6616565) B6616565
theorem B1167011 : Blo 774336 1167011 := bstep (se 1 (by rfl) ⟨875258, by rfl⟩ : syracuseStep 1167011 = 1750517) B1750517
theorem B1167041 : Blo 774336 1167041 := bstep (se 2 (by rfl) ⟨437640, by rfl⟩ : syracuseStep 1167041 = 875281) B875281
theorem B872131 : Blo 774336 872131 := bstep (se 1 (by rfl) ⟨654098, by rfl⟩ : syracuseStep 872131 = 1308197) B1308197
theorem B1167059 : Blo 774336 1167059 := bstep (se 1 (by rfl) ⟨875294, by rfl⟩ : syracuseStep 1167059 = 1750589) B1750589
theorem B3722993 : Blo 774336 3722993 := bstep (se 2 (by rfl) ⟨1396122, by rfl⟩ : syracuseStep 3722993 = 2792245) B2792245
theorem B1167089 : Blo 774336 1167089 := bstep (se 2 (by rfl) ⟨437658, by rfl⟩ : syracuseStep 1167089 = 875317) B875317
theorem B1658627 : Blo 774336 1658627 := bstep (se 1 (by rfl) ⟨1243970, by rfl⟩ : syracuseStep 1658627 = 2487941) B2487941
theorem B1167107 : Blo 774336 1167107 := bstep (se 1 (by rfl) ⟨875330, by rfl⟩ : syracuseStep 1167107 = 1750661) B1750661
theorem B1167137 : Blo 774336 1167137 := bstep (se 2 (by rfl) ⟨437676, by rfl⟩ : syracuseStep 1167137 = 875353) B875353
theorem B4476707 : Blo 774336 4476707 := bstep (se 1 (by rfl) ⟨3357530, by rfl⟩ : syracuseStep 4476707 = 6715061) B6715061
theorem B1167155 : Blo 774336 1167155 := bstep (se 1 (by rfl) ⟨875366, by rfl⟩ : syracuseStep 1167155 = 1750733) B1750733
theorem B1167185 : Blo 774336 1167185 := bstep (se 2 (by rfl) ⟨437694, by rfl⟩ : syracuseStep 1167185 = 875389) B875389
theorem B872275 : Blo 774336 872275 := bstep (se 1 (by rfl) ⟨654206, by rfl⟩ : syracuseStep 872275 = 1308413) B1308413
theorem B1167203 : Blo 774336 1167203 := bstep (se 1 (by rfl) ⟨875402, by rfl⟩ : syracuseStep 1167203 = 1750805) B1750805
theorem B1167233 : Blo 774336 1167233 := bstep (se 2 (by rfl) ⟨437712, by rfl⟩ : syracuseStep 1167233 = 875425) B875425
theorem B1167251 : Blo 774336 1167251 := bstep (se 1 (by rfl) ⟨875438, by rfl⟩ : syracuseStep 1167251 = 1750877) B1750877
theorem B1167281 : Blo 774336 1167281 := bstep (se 2 (by rfl) ⟨437730, by rfl⟩ : syracuseStep 1167281 = 875461) B875461
theorem B1167299 : Blo 774336 1167299 := bstep (se 1 (by rfl) ⟨875474, by rfl⟩ : syracuseStep 1167299 = 1750949) B1750949
theorem B16175045 : Blo 774336 16175045 := bstep (se 4 (by rfl) ⟨1516410, by rfl⟩ : syracuseStep 16175045 = 3032821) B3032821
theorem B1167329 : Blo 774336 1167329 := bstep (se 2 (by rfl) ⟨437748, by rfl⟩ : syracuseStep 1167329 = 875497) B875497
theorem B872419 : Blo 774336 872419 := bstep (se 1 (by rfl) ⟨654314, by rfl⟩ : syracuseStep 872419 = 1308629) B1308629
theorem B1167347 : Blo 774336 1167347 := bstep (se 1 (by rfl) ⟨875510, by rfl⟩ : syracuseStep 1167347 = 1751021) B1751021
theorem B1167377 : Blo 774336 1167377 := bstep (se 2 (by rfl) ⟨437766, by rfl⟩ : syracuseStep 1167377 = 875533) B875533
theorem B1167395 : Blo 774336 1167395 := bstep (se 1 (by rfl) ⟨875546, by rfl⟩ : syracuseStep 1167395 = 1751093) B1751093
theorem B1167425 : Blo 774336 1167425 := bstep (se 2 (by rfl) ⟨437784, by rfl⟩ : syracuseStep 1167425 = 875569) B875569
theorem B1167443 : Blo 774336 1167443 := bstep (se 1 (by rfl) ⟨875582, by rfl⟩ : syracuseStep 1167443 = 1751165) B1751165
theorem B1167473 : Blo 774336 1167473 := bstep (se 2 (by rfl) ⟨437802, by rfl⟩ : syracuseStep 1167473 = 875605) B875605
theorem B872563 : Blo 774336 872563 := bstep (se 1 (by rfl) ⟨654422, by rfl⟩ : syracuseStep 872563 = 1308845) B1308845
theorem B1167491 : Blo 774336 1167491 := bstep (se 1 (by rfl) ⟨875618, by rfl⟩ : syracuseStep 1167491 = 1751237) B1751237
theorem B7983245 : Blo 774336 7983245 := bstep (se 3 (by rfl) ⟨1496858, by rfl⟩ : syracuseStep 7983245 = 2993717) B2993717
theorem B774339 : Blo 774336 774339 := bstep (se 1 (by rfl) ⟨580754, by rfl⟩ : syracuseStep 774339 = 1161509) B1161509
theorem B774355 : Blo 774336 774355 := bstep (se 1 (by rfl) ⟨580766, by rfl⟩ : syracuseStep 774355 = 1161533) B1161533
theorem B774371 : Blo 774336 774371 := bstep (se 1 (by rfl) ⟨580778, by rfl⟩ : syracuseStep 774371 = 1161557) B1161557
theorem B125751523 : Blo 774336 125751523 := bstep (se 1 (by rfl) ⟨94313642, by rfl⟩ : syracuseStep 125751523 = 188627285) B188627285
theorem B774387 : Blo 774336 774387 := bstep (se 1 (by rfl) ⟨580790, by rfl⟩ : syracuseStep 774387 = 1161581) B1161581
theorem B774403 : Blo 774336 774403 := bstep (se 1 (by rfl) ⟨580802, by rfl⟩ : syracuseStep 774403 = 1161605) B1161605
theorem B872707 : Blo 774336 872707 := bstep (se 1 (by rfl) ⟨654530, by rfl⟩ : syracuseStep 872707 = 1309061) B1309061
theorem B774419 : Blo 774336 774419 := bstep (se 1 (by rfl) ⟨580814, by rfl⟩ : syracuseStep 774419 = 1161629) B1161629
theorem B774435 : Blo 774336 774435 := bstep (se 1 (by rfl) ⟨580826, by rfl⟩ : syracuseStep 774435 = 1161653) B1161653
theorem B774451 : Blo 774336 774451 := bstep (se 1 (by rfl) ⟨580838, by rfl⟩ : syracuseStep 774451 = 1161677) B1161677
theorem B774467 : Blo 774336 774467 := bstep (se 1 (by rfl) ⟨580850, by rfl⟩ : syracuseStep 774467 = 1161701) B1161701
theorem B774483 : Blo 774336 774483 := bstep (se 1 (by rfl) ⟨580862, by rfl⟩ : syracuseStep 774483 = 1161725) B1161725
theorem B774499 : Blo 774336 774499 := bstep (se 1 (by rfl) ⟨580874, by rfl⟩ : syracuseStep 774499 = 1161749) B1161749
theorem B9949553 : Blo 774336 9949553 := bstep (se 2 (by rfl) ⟨3731082, by rfl⟩ : syracuseStep 9949553 = 7462165) B7462165
theorem B774515 : Blo 774336 774515 := bstep (se 1 (by rfl) ⟨580886, by rfl⟩ : syracuseStep 774515 = 1161773) B1161773
theorem B774531 : Blo 774336 774531 := bstep (se 1 (by rfl) ⟨580898, by rfl⟩ : syracuseStep 774531 = 1161797) B1161797
theorem B774547 : Blo 774336 774547 := bstep (se 1 (by rfl) ⟨580910, by rfl⟩ : syracuseStep 774547 = 1161821) B1161821
theorem B872851 : Blo 774336 872851 := bstep (se 1 (by rfl) ⟨654638, by rfl⟩ : syracuseStep 872851 = 1309277) B1309277
theorem B774563 : Blo 774336 774563 := bstep (se 1 (by rfl) ⟨580922, by rfl⟩ : syracuseStep 774563 = 1161845) B1161845
theorem B774579 : Blo 774336 774579 := bstep (se 1 (by rfl) ⟨580934, by rfl⟩ : syracuseStep 774579 = 1161869) B1161869
theorem B774595 : Blo 774336 774595 := bstep (se 1 (by rfl) ⟨580946, by rfl⟩ : syracuseStep 774595 = 1161893) B1161893
theorem B22434245 : Blo 774336 22434245 := bstep (se 4 (by rfl) ⟨2103210, by rfl⟩ : syracuseStep 22434245 = 4206421) B4206421
theorem B774611 : Blo 774336 774611 := bstep (se 1 (by rfl) ⟨580958, by rfl⟩ : syracuseStep 774611 = 1161917) B1161917
theorem B774627 : Blo 774336 774627 := bstep (se 1 (by rfl) ⟨580970, by rfl⟩ : syracuseStep 774627 = 1161941) B1161941
theorem B774643 : Blo 774336 774643 := bstep (se 1 (by rfl) ⟨580982, by rfl⟩ : syracuseStep 774643 = 1161965) B1161965
theorem B774659 : Blo 774336 774659 := bstep (se 1 (by rfl) ⟨580994, by rfl⟩ : syracuseStep 774659 = 1161989) B1161989
theorem B774675 : Blo 774336 774675 := bstep (se 1 (by rfl) ⟨581006, by rfl⟩ : syracuseStep 774675 = 1162013) B1162013
theorem B774691 : Blo 774336 774691 := bstep (se 1 (by rfl) ⟨581018, by rfl⟩ : syracuseStep 774691 = 1162037) B1162037
theorem B872995 : Blo 774336 872995 := bstep (se 1 (by rfl) ⟨654746, by rfl⟩ : syracuseStep 872995 = 1309493) B1309493
theorem B1397297 : Blo 774336 1397297 := bstep (se 2 (by rfl) ⟨523986, by rfl⟩ : syracuseStep 1397297 = 1047973) B1047973
theorem B774707 : Blo 774336 774707 := bstep (se 1 (by rfl) ⟨581030, by rfl⟩ : syracuseStep 774707 = 1162061) B1162061
theorem B774723 : Blo 774336 774723 := bstep (se 1 (by rfl) ⟨581042, by rfl⟩ : syracuseStep 774723 = 1162085) B1162085
theorem B774739 : Blo 774336 774739 := bstep (se 1 (by rfl) ⟨581054, by rfl⟩ : syracuseStep 774739 = 1162109) B1162109
theorem B774755 : Blo 774336 774755 := bstep (se 1 (by rfl) ⟨581066, by rfl⟩ : syracuseStep 774755 = 1162133) B1162133
theorem B774771 : Blo 774336 774771 := bstep (se 1 (by rfl) ⟨581078, by rfl⟩ : syracuseStep 774771 = 1162157) B1162157
theorem B774787 : Blo 774336 774787 := bstep (se 1 (by rfl) ⟨581090, by rfl⟩ : syracuseStep 774787 = 1162181) B1162181
theorem B1659523 : Blo 774336 1659523 := bstep (se 1 (by rfl) ⟨1244642, by rfl⟩ : syracuseStep 1659523 = 2489285) B2489285
theorem B774803 : Blo 774336 774803 := bstep (se 1 (by rfl) ⟨581102, by rfl⟩ : syracuseStep 774803 = 1162205) B1162205
theorem B774819 : Blo 774336 774819 := bstep (se 1 (by rfl) ⟨581114, by rfl⟩ : syracuseStep 774819 = 1162229) B1162229
theorem B3920561 : Blo 774336 3920561 := bstep (se 2 (by rfl) ⟨1470210, by rfl⟩ : syracuseStep 3920561 = 2940421) B2940421
theorem B774835 : Blo 774336 774835 := bstep (se 1 (by rfl) ⟨581126, by rfl⟩ : syracuseStep 774835 = 1162253) B1162253
theorem B873139 : Blo 774336 873139 := bstep (se 1 (by rfl) ⟨654854, by rfl⟩ : syracuseStep 873139 = 1309709) B1309709
theorem B774851 : Blo 774336 774851 := bstep (se 1 (by rfl) ⟨581138, by rfl⟩ : syracuseStep 774851 = 1162277) B1162277
theorem B774867 : Blo 774336 774867 := bstep (se 1 (by rfl) ⟨581150, by rfl⟩ : syracuseStep 774867 = 1162301) B1162301
theorem B774883 : Blo 774336 774883 := bstep (se 1 (by rfl) ⟨581162, by rfl⟩ : syracuseStep 774883 = 1162325) B1162325
theorem B774899 : Blo 774336 774899 := bstep (se 1 (by rfl) ⟨581174, by rfl⟩ : syracuseStep 774899 = 1162349) B1162349
theorem B774915 : Blo 774336 774915 := bstep (se 1 (by rfl) ⟨581186, by rfl⟩ : syracuseStep 774915 = 1162373) B1162373
theorem B774931 : Blo 774336 774931 := bstep (se 1 (by rfl) ⟨581198, by rfl⟩ : syracuseStep 774931 = 1162397) B1162397
theorem B774947 : Blo 774336 774947 := bstep (se 1 (by rfl) ⟨581210, by rfl⟩ : syracuseStep 774947 = 1162421) B1162421
theorem B774963 : Blo 774336 774963 := bstep (se 1 (by rfl) ⟨581222, by rfl⟩ : syracuseStep 774963 = 1162445) B1162445
theorem B774979 : Blo 774336 774979 := bstep (se 1 (by rfl) ⟨581234, by rfl⟩ : syracuseStep 774979 = 1162469) B1162469
theorem B873283 : Blo 774336 873283 := bstep (se 1 (by rfl) ⟨654962, by rfl⟩ : syracuseStep 873283 = 1309925) B1309925
theorem B774995 : Blo 774336 774995 := bstep (se 1 (by rfl) ⟨581246, by rfl⟩ : syracuseStep 774995 = 1162493) B1162493
theorem B775011 : Blo 774336 775011 := bstep (se 1 (by rfl) ⟨581258, by rfl⟩ : syracuseStep 775011 = 1162517) B1162517
theorem B775027 : Blo 774336 775027 := bstep (se 1 (by rfl) ⟨581270, by rfl⟩ : syracuseStep 775027 = 1162541) B1162541
theorem B775043 : Blo 774336 775043 := bstep (se 1 (by rfl) ⟨581282, by rfl⟩ : syracuseStep 775043 = 1162565) B1162565
theorem B775059 : Blo 774336 775059 := bstep (se 1 (by rfl) ⟨581294, by rfl⟩ : syracuseStep 775059 = 1162589) B1162589
theorem B775075 : Blo 774336 775075 := bstep (se 1 (by rfl) ⟨581306, by rfl⟩ : syracuseStep 775075 = 1162613) B1162613
theorem B775091 : Blo 774336 775091 := bstep (se 1 (by rfl) ⟨581318, by rfl⟩ : syracuseStep 775091 = 1162637) B1162637
theorem B775107 : Blo 774336 775107 := bstep (se 1 (by rfl) ⟨581330, by rfl⟩ : syracuseStep 775107 = 1162661) B1162661
theorem B5886917 : Blo 774336 5886917 := bstep (se 4 (by rfl) ⟨551898, by rfl⟩ : syracuseStep 5886917 = 1103797) B1103797
theorem B775123 : Blo 774336 775123 := bstep (se 1 (by rfl) ⟨581342, by rfl⟩ : syracuseStep 775123 = 1162685) B1162685
theorem B873427 : Blo 774336 873427 := bstep (se 1 (by rfl) ⟨655070, by rfl⟩ : syracuseStep 873427 = 1310141) B1310141
theorem B775139 : Blo 774336 775139 := bstep (se 1 (by rfl) ⟨581354, by rfl⟩ : syracuseStep 775139 = 1162709) B1162709
theorem B775155 : Blo 774336 775155 := bstep (se 1 (by rfl) ⟨581366, by rfl⟩ : syracuseStep 775155 = 1162733) B1162733
theorem B1102835 : Blo 774336 1102835 := bstep (se 1 (by rfl) ⟨827126, by rfl⟩ : syracuseStep 1102835 = 1654253) B1654253
theorem B775171 : Blo 774336 775171 := bstep (se 1 (by rfl) ⟨581378, by rfl⟩ : syracuseStep 775171 = 1162757) B1162757
theorem B775187 : Blo 774336 775187 := bstep (se 1 (by rfl) ⟨581390, by rfl⟩ : syracuseStep 775187 = 1162781) B1162781
theorem B775203 : Blo 774336 775203 := bstep (se 1 (by rfl) ⟨581402, by rfl⟩ : syracuseStep 775203 = 1162805) B1162805
theorem B775219 : Blo 774336 775219 := bstep (se 1 (by rfl) ⟨581414, by rfl⟩ : syracuseStep 775219 = 1162829) B1162829
theorem B775235 : Blo 774336 775235 := bstep (se 1 (by rfl) ⟨581426, by rfl⟩ : syracuseStep 775235 = 1162853) B1162853
theorem B775251 : Blo 774336 775251 := bstep (se 1 (by rfl) ⟨581438, by rfl⟩ : syracuseStep 775251 = 1162877) B1162877
theorem B775267 : Blo 774336 775267 := bstep (se 1 (by rfl) ⟨581450, by rfl⟩ : syracuseStep 775267 = 1162901) B1162901
theorem B873571 : Blo 774336 873571 := bstep (se 1 (by rfl) ⟨655178, by rfl⟩ : syracuseStep 873571 = 1310357) B1310357
theorem B775283 : Blo 774336 775283 := bstep (se 1 (by rfl) ⟨581462, by rfl⟩ : syracuseStep 775283 = 1162925) B1162925
theorem B775299 : Blo 774336 775299 := bstep (se 1 (by rfl) ⟨581474, by rfl⟩ : syracuseStep 775299 = 1162949) B1162949
theorem B775315 : Blo 774336 775315 := bstep (se 1 (by rfl) ⟨581486, by rfl⟩ : syracuseStep 775315 = 1162973) B1162973
theorem B775331 : Blo 774336 775331 := bstep (se 1 (by rfl) ⟨581498, by rfl⟩ : syracuseStep 775331 = 1162997) B1162997
theorem B775347 : Blo 774336 775347 := bstep (se 1 (by rfl) ⟨581510, by rfl⟩ : syracuseStep 775347 = 1163021) B1163021
theorem B775363 : Blo 774336 775363 := bstep (se 1 (by rfl) ⟨581522, by rfl⟩ : syracuseStep 775363 = 1163045) B1163045
theorem B775379 : Blo 774336 775379 := bstep (se 1 (by rfl) ⟨581534, by rfl⟩ : syracuseStep 775379 = 1163069) B1163069
theorem B775395 : Blo 774336 775395 := bstep (se 1 (by rfl) ⟨581546, by rfl⟩ : syracuseStep 775395 = 1163093) B1163093
theorem B775411 : Blo 774336 775411 := bstep (se 1 (by rfl) ⟨581558, by rfl⟩ : syracuseStep 775411 = 1163117) B1163117
theorem B873715 : Blo 774336 873715 := bstep (se 1 (by rfl) ⟨655286, by rfl⟩ : syracuseStep 873715 = 1310573) B1310573
theorem B775427 : Blo 774336 775427 := bstep (se 1 (by rfl) ⟨581570, by rfl⟩ : syracuseStep 775427 = 1163141) B1163141
theorem B775443 : Blo 774336 775443 := bstep (se 1 (by rfl) ⟨581582, by rfl⟩ : syracuseStep 775443 = 1163165) B1163165
theorem B775459 : Blo 774336 775459 := bstep (se 1 (by rfl) ⟨581594, by rfl⟩ : syracuseStep 775459 = 1163189) B1163189
theorem B775475 : Blo 774336 775475 := bstep (se 1 (by rfl) ⟨581606, by rfl⟩ : syracuseStep 775475 = 1163213) B1163213
theorem B775491 : Blo 774336 775491 := bstep (se 1 (by rfl) ⟨581618, by rfl⟩ : syracuseStep 775491 = 1163237) B1163237
theorem B775507 : Blo 774336 775507 := bstep (se 1 (by rfl) ⟨581630, by rfl⟩ : syracuseStep 775507 = 1163261) B1163261
theorem B775523 : Blo 774336 775523 := bstep (se 1 (by rfl) ⟨581642, by rfl⟩ : syracuseStep 775523 = 1163285) B1163285
theorem B775539 : Blo 774336 775539 := bstep (se 1 (by rfl) ⟨581654, by rfl⟩ : syracuseStep 775539 = 1163309) B1163309
theorem B775555 : Blo 774336 775555 := bstep (se 1 (by rfl) ⟨581666, by rfl⟩ : syracuseStep 775555 = 1163333) B1163333
theorem B873859 : Blo 774336 873859 := bstep (se 1 (by rfl) ⟨655394, by rfl⟩ : syracuseStep 873859 = 1310789) B1310789
theorem B775571 : Blo 774336 775571 := bstep (se 1 (by rfl) ⟨581678, by rfl⟩ : syracuseStep 775571 = 1163357) B1163357
theorem B775587 : Blo 774336 775587 := bstep (se 1 (by rfl) ⟨581690, by rfl⟩ : syracuseStep 775587 = 1163381) B1163381
theorem B775603 : Blo 774336 775603 := bstep (se 1 (by rfl) ⟨581702, by rfl⟩ : syracuseStep 775603 = 1163405) B1163405
theorem B775619 : Blo 774336 775619 := bstep (se 1 (by rfl) ⟨581714, by rfl⟩ : syracuseStep 775619 = 1163429) B1163429
theorem B13424069 : Blo 774336 13424069 := bstep (se 4 (by rfl) ⟨1258506, by rfl⟩ : syracuseStep 13424069 = 2517013) B2517013
theorem B775635 : Blo 774336 775635 := bstep (se 1 (by rfl) ⟨581726, by rfl⟩ : syracuseStep 775635 = 1163453) B1163453
theorem B775651 : Blo 774336 775651 := bstep (se 1 (by rfl) ⟨581738, by rfl⟩ : syracuseStep 775651 = 1163477) B1163477
theorem B775667 : Blo 774336 775667 := bstep (se 1 (by rfl) ⟨581750, by rfl⟩ : syracuseStep 775667 = 1163501) B1163501
theorem B775683 : Blo 774336 775683 := bstep (se 1 (by rfl) ⟨581762, by rfl⟩ : syracuseStep 775683 = 1163525) B1163525
theorem B775699 : Blo 774336 775699 := bstep (se 1 (by rfl) ⟨581774, by rfl⟩ : syracuseStep 775699 = 1163549) B1163549
theorem B874003 : Blo 774336 874003 := bstep (se 1 (by rfl) ⟨655502, by rfl⟩ : syracuseStep 874003 = 1311005) B1311005
theorem B775715 : Blo 774336 775715 := bstep (se 1 (by rfl) ⟨581786, by rfl⟩ : syracuseStep 775715 = 1163573) B1163573
theorem B775731 : Blo 774336 775731 := bstep (se 1 (by rfl) ⟨581798, by rfl⟩ : syracuseStep 775731 = 1163597) B1163597
theorem B775747 : Blo 774336 775747 := bstep (se 1 (by rfl) ⟨581810, by rfl⟩ : syracuseStep 775747 = 1163621) B1163621
theorem B775763 : Blo 774336 775763 := bstep (se 1 (by rfl) ⟨581822, by rfl⟩ : syracuseStep 775763 = 1163645) B1163645
theorem B775779 : Blo 774336 775779 := bstep (se 1 (by rfl) ⟨581834, by rfl⟩ : syracuseStep 775779 = 1163669) B1163669
theorem B1496675 : Blo 774336 1496675 := bstep (se 1 (by rfl) ⟨1122506, by rfl⟩ : syracuseStep 1496675 = 2245013) B2245013
theorem B1103473 : Blo 774336 1103473 := bstep (se 2 (by rfl) ⟨413802, by rfl⟩ : syracuseStep 1103473 = 827605) B827605
theorem B775795 : Blo 774336 775795 := bstep (se 1 (by rfl) ⟨581846, by rfl⟩ : syracuseStep 775795 = 1163693) B1163693
theorem B775811 : Blo 774336 775811 := bstep (se 1 (by rfl) ⟨581858, by rfl⟩ : syracuseStep 775811 = 1163717) B1163717
theorem B775827 : Blo 774336 775827 := bstep (se 1 (by rfl) ⟨581870, by rfl⟩ : syracuseStep 775827 = 1163741) B1163741
theorem B775843 : Blo 774336 775843 := bstep (se 1 (by rfl) ⟨581882, by rfl⟩ : syracuseStep 775843 = 1163765) B1163765
theorem B874147 : Blo 774336 874147 := bstep (se 1 (by rfl) ⟨655610, by rfl⟩ : syracuseStep 874147 = 1311221) B1311221
theorem B775859 : Blo 774336 775859 := bstep (se 1 (by rfl) ⟨581894, by rfl⟩ : syracuseStep 775859 = 1163789) B1163789
theorem B775875 : Blo 774336 775875 := bstep (se 1 (by rfl) ⟨581906, by rfl⟩ : syracuseStep 775875 = 1163813) B1163813
theorem B775891 : Blo 774336 775891 := bstep (se 1 (by rfl) ⟨581918, by rfl⟩ : syracuseStep 775891 = 1163837) B1163837
theorem B775907 : Blo 774336 775907 := bstep (se 1 (by rfl) ⟨581930, by rfl⟩ : syracuseStep 775907 = 1163861) B1163861
theorem B775923 : Blo 774336 775923 := bstep (se 1 (by rfl) ⟨581942, by rfl⟩ : syracuseStep 775923 = 1163885) B1163885
theorem B775939 : Blo 774336 775939 := bstep (se 1 (by rfl) ⟨581954, by rfl⟩ : syracuseStep 775939 = 1163909) B1163909
theorem B775955 : Blo 774336 775955 := bstep (se 1 (by rfl) ⟨581966, by rfl⟩ : syracuseStep 775955 = 1163933) B1163933
theorem B775971 : Blo 774336 775971 := bstep (se 1 (by rfl) ⟨581978, by rfl⟩ : syracuseStep 775971 = 1163957) B1163957
theorem B775987 : Blo 774336 775987 := bstep (se 1 (by rfl) ⟨581990, by rfl⟩ : syracuseStep 775987 = 1163981) B1163981
theorem B874291 : Blo 774336 874291 := bstep (se 1 (by rfl) ⟨655718, by rfl⟩ : syracuseStep 874291 = 1311437) B1311437
theorem B776003 : Blo 774336 776003 := bstep (se 1 (by rfl) ⟨582002, by rfl⟩ : syracuseStep 776003 = 1164005) B1164005
theorem B1660753 : Blo 774336 1660753 := bstep (se 2 (by rfl) ⟨622782, by rfl⟩ : syracuseStep 1660753 = 1245565) B1245565
theorem B776019 : Blo 774336 776019 := bstep (se 1 (by rfl) ⟨582014, by rfl⟩ : syracuseStep 776019 = 1164029) B1164029
theorem B776035 : Blo 774336 776035 := bstep (se 1 (by rfl) ⟨582026, by rfl⟩ : syracuseStep 776035 = 1164053) B1164053
theorem B776051 : Blo 774336 776051 := bstep (se 1 (by rfl) ⟨582038, by rfl⟩ : syracuseStep 776051 = 1164077) B1164077
theorem B776067 : Blo 774336 776067 := bstep (se 1 (by rfl) ⟨582050, by rfl⟩ : syracuseStep 776067 = 1164101) B1164101
theorem B776083 : Blo 774336 776083 := bstep (se 1 (by rfl) ⟨582062, by rfl⟩ : syracuseStep 776083 = 1164125) B1164125
theorem B776099 : Blo 774336 776099 := bstep (se 1 (by rfl) ⟨582074, by rfl⟩ : syracuseStep 776099 = 1164149) B1164149
theorem B776115 : Blo 774336 776115 := bstep (se 1 (by rfl) ⟨582086, by rfl⟩ : syracuseStep 776115 = 1164173) B1164173
theorem B1103809 : Blo 774336 1103809 := bstep (se 2 (by rfl) ⟨413928, by rfl⟩ : syracuseStep 1103809 = 827857) B827857
theorem B776131 : Blo 774336 776131 := bstep (se 1 (by rfl) ⟨582098, by rfl⟩ : syracuseStep 776131 = 1164197) B1164197
theorem B874435 : Blo 774336 874435 := bstep (se 1 (by rfl) ⟨655826, by rfl⟩ : syracuseStep 874435 = 1311653) B1311653
theorem B776147 : Blo 774336 776147 := bstep (se 1 (by rfl) ⟨582110, by rfl⟩ : syracuseStep 776147 = 1164221) B1164221
theorem B776163 : Blo 774336 776163 := bstep (se 1 (by rfl) ⟨582122, by rfl⟩ : syracuseStep 776163 = 1164245) B1164245
theorem B776179 : Blo 774336 776179 := bstep (se 1 (by rfl) ⟨582134, by rfl⟩ : syracuseStep 776179 = 1164269) B1164269
theorem B776195 : Blo 774336 776195 := bstep (se 1 (by rfl) ⟨582146, by rfl⟩ : syracuseStep 776195 = 1164293) B1164293
theorem B776211 : Blo 774336 776211 := bstep (se 1 (by rfl) ⟨582158, by rfl⟩ : syracuseStep 776211 = 1164317) B1164317
theorem B776227 : Blo 774336 776227 := bstep (se 1 (by rfl) ⟨582170, by rfl⟩ : syracuseStep 776227 = 1164341) B1164341
theorem B776243 : Blo 774336 776243 := bstep (se 1 (by rfl) ⟨582182, by rfl⟩ : syracuseStep 776243 = 1164365) B1164365
theorem B776259 : Blo 774336 776259 := bstep (se 1 (by rfl) ⟨582194, by rfl⟩ : syracuseStep 776259 = 1164389) B1164389
theorem B776275 : Blo 774336 776275 := bstep (se 1 (by rfl) ⟨582206, by rfl⟩ : syracuseStep 776275 = 1164413) B1164413
theorem B874579 : Blo 774336 874579 := bstep (se 1 (by rfl) ⟨655934, by rfl⟩ : syracuseStep 874579 = 1311869) B1311869
theorem B3922019 : Blo 774336 3922019 := bstep (se 1 (by rfl) ⟨2941514, by rfl⟩ : syracuseStep 3922019 = 5883029) B5883029
theorem B776291 : Blo 774336 776291 := bstep (se 1 (by rfl) ⟨582218, by rfl⟩ : syracuseStep 776291 = 1164437) B1164437
theorem B776307 : Blo 774336 776307 := bstep (se 1 (by rfl) ⟨582230, by rfl⟩ : syracuseStep 776307 = 1164461) B1164461
theorem B776323 : Blo 774336 776323 := bstep (se 1 (by rfl) ⟨582242, by rfl⟩ : syracuseStep 776323 = 1164485) B1164485
theorem B3725453 : Blo 774336 3725453 := bstep (se 3 (by rfl) ⟨698522, by rfl⟩ : syracuseStep 3725453 = 1397045) B1397045
theorem B776339 : Blo 774336 776339 := bstep (se 1 (by rfl) ⟨582254, by rfl⟩ : syracuseStep 776339 = 1164509) B1164509
theorem B776355 : Blo 774336 776355 := bstep (se 1 (by rfl) ⟨582266, by rfl⟩ : syracuseStep 776355 = 1164533) B1164533
theorem B776371 : Blo 774336 776371 := bstep (se 1 (by rfl) ⟨582278, by rfl⟩ : syracuseStep 776371 = 1164557) B1164557
theorem B776387 : Blo 774336 776387 := bstep (se 1 (by rfl) ⟨582290, by rfl⟩ : syracuseStep 776387 = 1164581) B1164581
theorem B776403 : Blo 774336 776403 := bstep (se 1 (by rfl) ⟨582302, by rfl⟩ : syracuseStep 776403 = 1164605) B1164605
theorem B776419 : Blo 774336 776419 := bstep (se 1 (by rfl) ⟨582314, by rfl⟩ : syracuseStep 776419 = 1164629) B1164629
theorem B874723 : Blo 774336 874723 := bstep (se 1 (by rfl) ⟨656042, by rfl⟩ : syracuseStep 874723 = 1312085) B1312085
theorem B776435 : Blo 774336 776435 := bstep (se 1 (by rfl) ⟨582326, by rfl⟩ : syracuseStep 776435 = 1164653) B1164653
theorem B776451 : Blo 774336 776451 := bstep (se 1 (by rfl) ⟨582338, by rfl⟩ : syracuseStep 776451 = 1164677) B1164677
theorem B776467 : Blo 774336 776467 := bstep (se 1 (by rfl) ⟨582350, by rfl⟩ : syracuseStep 776467 = 1164701) B1164701
theorem B776483 : Blo 774336 776483 := bstep (se 1 (by rfl) ⟨582362, by rfl⟩ : syracuseStep 776483 = 1164725) B1164725
theorem B776499 : Blo 774336 776499 := bstep (se 1 (by rfl) ⟨582374, by rfl⟩ : syracuseStep 776499 = 1164749) B1164749
theorem B776515 : Blo 774336 776515 := bstep (se 1 (by rfl) ⟨582386, by rfl⟩ : syracuseStep 776515 = 1164773) B1164773
theorem B776531 : Blo 774336 776531 := bstep (se 1 (by rfl) ⟨582398, by rfl⟩ : syracuseStep 776531 = 1164797) B1164797
theorem B776547 : Blo 774336 776547 := bstep (se 1 (by rfl) ⟨582410, by rfl⟩ : syracuseStep 776547 = 1164821) B1164821
theorem B776563 : Blo 774336 776563 := bstep (se 1 (by rfl) ⟨582422, by rfl⟩ : syracuseStep 776563 = 1164845) B1164845
theorem B874867 : Blo 774336 874867 := bstep (se 1 (by rfl) ⟨656150, by rfl⟩ : syracuseStep 874867 = 1312301) B1312301
theorem B776579 : Blo 774336 776579 := bstep (se 1 (by rfl) ⟨582434, by rfl⟩ : syracuseStep 776579 = 1164869) B1164869
theorem B1497475 : Blo 774336 1497475 := bstep (se 1 (by rfl) ⟨1123106, by rfl⟩ : syracuseStep 1497475 = 2246213) B2246213
theorem B776595 : Blo 774336 776595 := bstep (se 1 (by rfl) ⟨582446, by rfl⟩ : syracuseStep 776595 = 1164893) B1164893
theorem B776611 : Blo 774336 776611 := bstep (se 1 (by rfl) ⟨582458, by rfl⟩ : syracuseStep 776611 = 1164917) B1164917
theorem B776627 : Blo 774336 776627 := bstep (se 1 (by rfl) ⟨582470, by rfl⟩ : syracuseStep 776627 = 1164941) B1164941
theorem B776643 : Blo 774336 776643 := bstep (se 1 (by rfl) ⟨582482, by rfl⟩ : syracuseStep 776643 = 1164965) B1164965
theorem B776659 : Blo 774336 776659 := bstep (se 1 (by rfl) ⟨582494, by rfl⟩ : syracuseStep 776659 = 1164989) B1164989
theorem B776675 : Blo 774336 776675 := bstep (se 1 (by rfl) ⟨582506, by rfl⟩ : syracuseStep 776675 = 1165013) B1165013
theorem B6642161 : Blo 774336 6642161 := bstep (se 2 (by rfl) ⟨2490810, by rfl⟩ : syracuseStep 6642161 = 4981621) B4981621
theorem B776691 : Blo 774336 776691 := bstep (se 1 (by rfl) ⟨582518, by rfl⟩ : syracuseStep 776691 = 1165037) B1165037
theorem B776707 : Blo 774336 776707 := bstep (se 1 (by rfl) ⟨582530, by rfl⟩ : syracuseStep 776707 = 1165061) B1165061
theorem B875011 : Blo 774336 875011 := bstep (se 1 (by rfl) ⟨656258, by rfl⟩ : syracuseStep 875011 = 1312517) B1312517
theorem B1104401 : Blo 774336 1104401 := bstep (se 2 (by rfl) ⟨414150, by rfl⟩ : syracuseStep 1104401 = 828301) B828301
theorem B776723 : Blo 774336 776723 := bstep (se 1 (by rfl) ⟨582542, by rfl⟩ : syracuseStep 776723 = 1165085) B1165085
theorem B776739 : Blo 774336 776739 := bstep (se 1 (by rfl) ⟨582554, by rfl⟩ : syracuseStep 776739 = 1165109) B1165109
theorem B776755 : Blo 774336 776755 := bstep (se 1 (by rfl) ⟨582566, by rfl⟩ : syracuseStep 776755 = 1165133) B1165133
theorem B45439541 : Blo 774336 45439541 := bstep (se 5 (by rfl) ⟨2129978, by rfl⟩ : syracuseStep 45439541 = 4259957) B4259957
theorem B776771 : Blo 774336 776771 := bstep (se 1 (by rfl) ⟨582578, by rfl⟩ : syracuseStep 776771 = 1165157) B1165157
theorem B776787 : Blo 774336 776787 := bstep (se 1 (by rfl) ⟨582590, by rfl⟩ : syracuseStep 776787 = 1165181) B1165181
theorem B776803 : Blo 774336 776803 := bstep (se 1 (by rfl) ⟨582602, by rfl⟩ : syracuseStep 776803 = 1165205) B1165205
theorem B776819 : Blo 774336 776819 := bstep (se 1 (by rfl) ⟨582614, by rfl⟩ : syracuseStep 776819 = 1165229) B1165229
theorem B776835 : Blo 774336 776835 := bstep (se 1 (by rfl) ⟨582626, by rfl⟩ : syracuseStep 776835 = 1165253) B1165253
theorem B776851 : Blo 774336 776851 := bstep (se 1 (by rfl) ⟨582638, by rfl⟩ : syracuseStep 776851 = 1165277) B1165277
theorem B875155 : Blo 774336 875155 := bstep (se 1 (by rfl) ⟨656366, by rfl⟩ : syracuseStep 875155 = 1312733) B1312733
theorem B776867 : Blo 774336 776867 := bstep (se 1 (by rfl) ⟨582650, by rfl⟩ : syracuseStep 776867 = 1165301) B1165301
theorem B776883 : Blo 774336 776883 := bstep (se 1 (by rfl) ⟨582662, by rfl⟩ : syracuseStep 776883 = 1165325) B1165325
theorem B776899 : Blo 774336 776899 := bstep (se 1 (by rfl) ⟨582674, by rfl⟩ : syracuseStep 776899 = 1165349) B1165349
theorem B776915 : Blo 774336 776915 := bstep (se 1 (by rfl) ⟨582686, by rfl⟩ : syracuseStep 776915 = 1165373) B1165373
theorem B776931 : Blo 774336 776931 := bstep (se 1 (by rfl) ⟨582698, by rfl⟩ : syracuseStep 776931 = 1165397) B1165397
theorem B776947 : Blo 774336 776947 := bstep (se 1 (by rfl) ⟨582710, by rfl⟩ : syracuseStep 776947 = 1165421) B1165421
theorem B776963 : Blo 774336 776963 := bstep (se 1 (by rfl) ⟨582722, by rfl⟩ : syracuseStep 776963 = 1165445) B1165445
theorem B776979 : Blo 774336 776979 := bstep (se 1 (by rfl) ⟨582734, by rfl⟩ : syracuseStep 776979 = 1165469) B1165469
theorem B776995 : Blo 774336 776995 := bstep (se 1 (by rfl) ⟨582746, by rfl⟩ : syracuseStep 776995 = 1165493) B1165493
theorem B875299 : Blo 774336 875299 := bstep (se 1 (by rfl) ⟨656474, by rfl⟩ : syracuseStep 875299 = 1312949) B1312949
theorem B777011 : Blo 774336 777011 := bstep (se 1 (by rfl) ⟨582758, by rfl⟩ : syracuseStep 777011 = 1165517) B1165517
theorem B777027 : Blo 774336 777027 := bstep (se 1 (by rfl) ⟨582770, by rfl⟩ : syracuseStep 777027 = 1165541) B1165541
theorem B4414277 : Blo 774336 4414277 := bstep (se 4 (by rfl) ⟨413838, by rfl⟩ : syracuseStep 4414277 = 827677) B827677
theorem B777043 : Blo 774336 777043 := bstep (se 1 (by rfl) ⟨582782, by rfl⟩ : syracuseStep 777043 = 1165565) B1165565
theorem B777059 : Blo 774336 777059 := bstep (se 1 (by rfl) ⟨582794, by rfl⟩ : syracuseStep 777059 = 1165589) B1165589
theorem B777075 : Blo 774336 777075 := bstep (se 1 (by rfl) ⟨582806, by rfl⟩ : syracuseStep 777075 = 1165613) B1165613
theorem B777091 : Blo 774336 777091 := bstep (se 1 (by rfl) ⟨582818, by rfl⟩ : syracuseStep 777091 = 1165637) B1165637
theorem B3922829 : Blo 774336 3922829 := bstep (se 3 (by rfl) ⟨735530, by rfl⟩ : syracuseStep 3922829 = 1471061) B1471061
theorem B777107 : Blo 774336 777107 := bstep (se 1 (by rfl) ⟨582830, by rfl⟩ : syracuseStep 777107 = 1165661) B1165661
theorem B777123 : Blo 774336 777123 := bstep (se 1 (by rfl) ⟨582842, by rfl⟩ : syracuseStep 777123 = 1165685) B1165685
theorem B777139 : Blo 774336 777139 := bstep (se 1 (by rfl) ⟨582854, by rfl⟩ : syracuseStep 777139 = 1165709) B1165709
theorem B875443 : Blo 774336 875443 := bstep (se 1 (by rfl) ⟨656582, by rfl⟩ : syracuseStep 875443 = 1313165) B1313165
theorem B777155 : Blo 774336 777155 := bstep (se 1 (by rfl) ⟨582866, by rfl⟩ : syracuseStep 777155 = 1165733) B1165733
theorem B777171 : Blo 774336 777171 := bstep (se 1 (by rfl) ⟨582878, by rfl⟩ : syracuseStep 777171 = 1165757) B1165757
theorem B777187 : Blo 774336 777187 := bstep (se 1 (by rfl) ⟨582890, by rfl⟩ : syracuseStep 777187 = 1165781) B1165781
theorem B777203 : Blo 774336 777203 := bstep (se 1 (by rfl) ⟨582902, by rfl⟩ : syracuseStep 777203 = 1165805) B1165805
theorem B777219 : Blo 774336 777219 := bstep (se 1 (by rfl) ⟨582914, by rfl⟩ : syracuseStep 777219 = 1165829) B1165829
theorem B777235 : Blo 774336 777235 := bstep (se 1 (by rfl) ⟨582926, by rfl⟩ : syracuseStep 777235 = 1165853) B1165853
theorem B1104931 : Blo 774336 1104931 := bstep (se 1 (by rfl) ⟨828698, by rfl⟩ : syracuseStep 1104931 = 1657397) B1657397
theorem B777251 : Blo 774336 777251 := bstep (se 1 (by rfl) ⟨582938, by rfl⟩ : syracuseStep 777251 = 1165877) B1165877
theorem B777267 : Blo 774336 777267 := bstep (se 1 (by rfl) ⟨582950, by rfl⟩ : syracuseStep 777267 = 1165901) B1165901
theorem B777283 : Blo 774336 777283 := bstep (se 1 (by rfl) ⟨582962, by rfl⟩ : syracuseStep 777283 = 1165925) B1165925
theorem B875587 : Blo 774336 875587 := bstep (se 1 (by rfl) ⟨656690, by rfl⟩ : syracuseStep 875587 = 1313381) B1313381
theorem B777299 : Blo 774336 777299 := bstep (se 1 (by rfl) ⟨582974, by rfl⟩ : syracuseStep 777299 = 1165949) B1165949
theorem B777315 : Blo 774336 777315 := bstep (se 1 (by rfl) ⟨582986, by rfl⟩ : syracuseStep 777315 = 1165973) B1165973
theorem B777331 : Blo 774336 777331 := bstep (se 1 (by rfl) ⟨582998, by rfl⟩ : syracuseStep 777331 = 1165997) B1165997
theorem B777347 : Blo 774336 777347 := bstep (se 1 (by rfl) ⟨583010, by rfl⟩ : syracuseStep 777347 = 1166021) B1166021
theorem B777363 : Blo 774336 777363 := bstep (se 1 (by rfl) ⟨583022, by rfl⟩ : syracuseStep 777363 = 1166045) B1166045
theorem B777379 : Blo 774336 777379 := bstep (se 1 (by rfl) ⟨583034, by rfl⟩ : syracuseStep 777379 = 1166069) B1166069
theorem B777395 : Blo 774336 777395 := bstep (se 1 (by rfl) ⟨583046, by rfl⟩ : syracuseStep 777395 = 1166093) B1166093
theorem B777411 : Blo 774336 777411 := bstep (se 1 (by rfl) ⟨583058, by rfl⟩ : syracuseStep 777411 = 1166117) B1166117
theorem B777427 : Blo 774336 777427 := bstep (se 1 (by rfl) ⟨583070, by rfl⟩ : syracuseStep 777427 = 1166141) B1166141
theorem B4709603 : Blo 774336 4709603 := bstep (se 1 (by rfl) ⟨3532202, by rfl⟩ : syracuseStep 4709603 = 7064405) B7064405
theorem B777443 : Blo 774336 777443 := bstep (se 1 (by rfl) ⟨583082, by rfl⟩ : syracuseStep 777443 = 1166165) B1166165
theorem B777459 : Blo 774336 777459 := bstep (se 1 (by rfl) ⟨583094, by rfl⟩ : syracuseStep 777459 = 1166189) B1166189
theorem B777475 : Blo 774336 777475 := bstep (se 1 (by rfl) ⟨583106, by rfl⟩ : syracuseStep 777475 = 1166213) B1166213
theorem B4414733 : Blo 774336 4414733 := bstep (se 3 (by rfl) ⟨827762, by rfl⟩ : syracuseStep 4414733 = 1655525) B1655525
theorem B777491 : Blo 774336 777491 := bstep (se 1 (by rfl) ⟨583118, by rfl⟩ : syracuseStep 777491 = 1166237) B1166237
theorem B777507 : Blo 774336 777507 := bstep (se 1 (by rfl) ⟨583130, by rfl⟩ : syracuseStep 777507 = 1166261) B1166261
theorem B2940209 : Blo 774336 2940209 := bstep (se 2 (by rfl) ⟨1102578, by rfl⟩ : syracuseStep 2940209 = 2205157) B2205157
theorem B1662257 : Blo 774336 1662257 := bstep (se 2 (by rfl) ⟨623346, by rfl⟩ : syracuseStep 1662257 = 1246693) B1246693
theorem B777523 : Blo 774336 777523 := bstep (se 1 (by rfl) ⟨583142, by rfl⟩ : syracuseStep 777523 = 1166285) B1166285
theorem B777539 : Blo 774336 777539 := bstep (se 1 (by rfl) ⟨583154, by rfl⟩ : syracuseStep 777539 = 1166309) B1166309
theorem B1662275 : Blo 774336 1662275 := bstep (se 1 (by rfl) ⟨1246706, by rfl⟩ : syracuseStep 1662275 = 2493413) B2493413
theorem B777555 : Blo 774336 777555 := bstep (se 1 (by rfl) ⟨583166, by rfl⟩ : syracuseStep 777555 = 1166333) B1166333
theorem B777571 : Blo 774336 777571 := bstep (se 1 (by rfl) ⟨583178, by rfl⟩ : syracuseStep 777571 = 1166357) B1166357
theorem B1105267 : Blo 774336 1105267 := bstep (se 1 (by rfl) ⟨828950, by rfl⟩ : syracuseStep 1105267 = 1657901) B1657901
theorem B777587 : Blo 774336 777587 := bstep (se 1 (by rfl) ⟨583190, by rfl⟩ : syracuseStep 777587 = 1166381) B1166381
theorem B777603 : Blo 774336 777603 := bstep (se 1 (by rfl) ⟨583202, by rfl⟩ : syracuseStep 777603 = 1166405) B1166405
theorem B4709773 : Blo 774336 4709773 := bstep (se 3 (by rfl) ⟨883082, by rfl⟩ : syracuseStep 4709773 = 1766165) B1766165
theorem B777619 : Blo 774336 777619 := bstep (se 1 (by rfl) ⟨583214, by rfl⟩ : syracuseStep 777619 = 1166429) B1166429
theorem B777635 : Blo 774336 777635 := bstep (se 1 (by rfl) ⟨583226, by rfl⟩ : syracuseStep 777635 = 1166453) B1166453
theorem B777651 : Blo 774336 777651 := bstep (se 1 (by rfl) ⟨583238, by rfl⟩ : syracuseStep 777651 = 1166477) B1166477
theorem B777667 : Blo 774336 777667 := bstep (se 1 (by rfl) ⟨583250, by rfl⟩ : syracuseStep 777667 = 1166501) B1166501
theorem B777683 : Blo 774336 777683 := bstep (se 1 (by rfl) ⟨583262, by rfl⟩ : syracuseStep 777683 = 1166525) B1166525
theorem B777699 : Blo 774336 777699 := bstep (se 1 (by rfl) ⟨583274, by rfl⟩ : syracuseStep 777699 = 1166549) B1166549
theorem B777715 : Blo 774336 777715 := bstep (se 1 (by rfl) ⟨583286, by rfl⟩ : syracuseStep 777715 = 1166573) B1166573
theorem B777731 : Blo 774336 777731 := bstep (se 1 (by rfl) ⟨583298, by rfl⟩ : syracuseStep 777731 = 1166597) B1166597
theorem B777747 : Blo 774336 777747 := bstep (se 1 (by rfl) ⟨583310, by rfl⟩ : syracuseStep 777747 = 1166621) B1166621
theorem B777763 : Blo 774336 777763 := bstep (se 1 (by rfl) ⟨583322, by rfl⟩ : syracuseStep 777763 = 1166645) B1166645
theorem B777779 : Blo 774336 777779 := bstep (se 1 (by rfl) ⟨583334, by rfl⟩ : syracuseStep 777779 = 1166669) B1166669
theorem B777795 : Blo 774336 777795 := bstep (se 1 (by rfl) ⟨583346, by rfl⟩ : syracuseStep 777795 = 1166693) B1166693
theorem B777811 : Blo 774336 777811 := bstep (se 1 (by rfl) ⟨583358, by rfl⟩ : syracuseStep 777811 = 1166717) B1166717
theorem B777827 : Blo 774336 777827 := bstep (se 1 (by rfl) ⟨583370, by rfl⟩ : syracuseStep 777827 = 1166741) B1166741
theorem B777843 : Blo 774336 777843 := bstep (se 1 (by rfl) ⟨583382, by rfl⟩ : syracuseStep 777843 = 1166765) B1166765
theorem B777859 : Blo 774336 777859 := bstep (se 1 (by rfl) ⟨583394, by rfl⟩ : syracuseStep 777859 = 1166789) B1166789
theorem B777875 : Blo 774336 777875 := bstep (se 1 (by rfl) ⟨583406, by rfl⟩ : syracuseStep 777875 = 1166813) B1166813
theorem B777891 : Blo 774336 777891 := bstep (se 1 (by rfl) ⟨583418, by rfl⟩ : syracuseStep 777891 = 1166837) B1166837
theorem B777907 : Blo 774336 777907 := bstep (se 1 (by rfl) ⟨583430, by rfl⟩ : syracuseStep 777907 = 1166861) B1166861
theorem B777923 : Blo 774336 777923 := bstep (se 1 (by rfl) ⟨583442, by rfl⟩ : syracuseStep 777923 = 1166885) B1166885
theorem B777939 : Blo 774336 777939 := bstep (se 1 (by rfl) ⟨583454, by rfl⟩ : syracuseStep 777939 = 1166909) B1166909
theorem B777955 : Blo 774336 777955 := bstep (se 1 (by rfl) ⟨583466, by rfl⟩ : syracuseStep 777955 = 1166933) B1166933
theorem B777971 : Blo 774336 777971 := bstep (se 1 (by rfl) ⟨583478, by rfl⟩ : syracuseStep 777971 = 1166957) B1166957
theorem B777987 : Blo 774336 777987 := bstep (se 1 (by rfl) ⟨583490, by rfl⟩ : syracuseStep 777987 = 1166981) B1166981
theorem B778003 : Blo 774336 778003 := bstep (se 1 (by rfl) ⟨583502, by rfl⟩ : syracuseStep 778003 = 1167005) B1167005
theorem B778019 : Blo 774336 778019 := bstep (se 1 (by rfl) ⟨583514, by rfl⟩ : syracuseStep 778019 = 1167029) B1167029
theorem B778035 : Blo 774336 778035 := bstep (se 1 (by rfl) ⟨583526, by rfl⟩ : syracuseStep 778035 = 1167053) B1167053
theorem B778051 : Blo 774336 778051 := bstep (se 1 (by rfl) ⟨583538, by rfl⟩ : syracuseStep 778051 = 1167077) B1167077
theorem B778067 : Blo 774336 778067 := bstep (se 1 (by rfl) ⟨583550, by rfl⟩ : syracuseStep 778067 = 1167101) B1167101
theorem B778083 : Blo 774336 778083 := bstep (se 1 (by rfl) ⟨583562, by rfl⟩ : syracuseStep 778083 = 1167125) B1167125
theorem B778099 : Blo 774336 778099 := bstep (se 1 (by rfl) ⟨583574, by rfl⟩ : syracuseStep 778099 = 1167149) B1167149
theorem B778115 : Blo 774336 778115 := bstep (se 1 (by rfl) ⟨583586, by rfl⟩ : syracuseStep 778115 = 1167173) B1167173
theorem B778131 : Blo 774336 778131 := bstep (se 1 (by rfl) ⟨583598, by rfl⟩ : syracuseStep 778131 = 1167197) B1167197
theorem B1105825 : Blo 774336 1105825 := bstep (se 2 (by rfl) ⟨414684, by rfl⟩ : syracuseStep 1105825 = 829369) B829369
theorem B778147 : Blo 774336 778147 := bstep (se 1 (by rfl) ⟨583610, by rfl⟩ : syracuseStep 778147 = 1167221) B1167221
theorem B778163 : Blo 774336 778163 := bstep (se 1 (by rfl) ⟨583622, by rfl⟩ : syracuseStep 778163 = 1167245) B1167245
theorem B1105859 : Blo 774336 1105859 := bstep (se 1 (by rfl) ⟨829394, by rfl⟩ : syracuseStep 1105859 = 1658789) B1658789
theorem B1400771 : Blo 774336 1400771 := bstep (se 1 (by rfl) ⟨1050578, by rfl⟩ : syracuseStep 1400771 = 2101157) B2101157
theorem B778179 : Blo 774336 778179 := bstep (se 1 (by rfl) ⟨583634, by rfl⟩ : syracuseStep 778179 = 1167269) B1167269
theorem B778195 : Blo 774336 778195 := bstep (se 1 (by rfl) ⟨583646, by rfl⟩ : syracuseStep 778195 = 1167293) B1167293
theorem B778211 : Blo 774336 778211 := bstep (se 1 (by rfl) ⟨583658, by rfl⟩ : syracuseStep 778211 = 1167317) B1167317
theorem B778227 : Blo 774336 778227 := bstep (se 1 (by rfl) ⟨583670, by rfl⟩ : syracuseStep 778227 = 1167341) B1167341
theorem B778243 : Blo 774336 778243 := bstep (se 1 (by rfl) ⟨583682, by rfl⟩ : syracuseStep 778243 = 1167365) B1167365
theorem B778259 : Blo 774336 778259 := bstep (se 1 (by rfl) ⟨583694, by rfl⟩ : syracuseStep 778259 = 1167389) B1167389
theorem B2482211 : Blo 774336 2482211 := bstep (se 1 (by rfl) ⟨1861658, by rfl⟩ : syracuseStep 2482211 = 3723317) B3723317
theorem B778275 : Blo 774336 778275 := bstep (se 1 (by rfl) ⟨583706, by rfl⟩ : syracuseStep 778275 = 1167413) B1167413
theorem B778291 : Blo 774336 778291 := bstep (se 1 (by rfl) ⟨583718, by rfl⟩ : syracuseStep 778291 = 1167437) B1167437
theorem B778307 : Blo 774336 778307 := bstep (se 1 (by rfl) ⟨583730, by rfl⟩ : syracuseStep 778307 = 1167461) B1167461
theorem B778323 : Blo 774336 778323 := bstep (se 1 (by rfl) ⟨583742, by rfl⟩ : syracuseStep 778323 = 1167485) B1167485
theorem B6283747 : Blo 774336 6283747 := bstep (se 1 (by rfl) ⟨4712810, by rfl⟩ : syracuseStep 6283747 = 9425621) B9425621
theorem B1991153 : Blo 774336 1991153 := bstep (se 2 (by rfl) ⟨746682, by rfl⟩ : syracuseStep 1991153 = 1493365) B1493365
theorem B1106417 : Blo 774336 1106417 := bstep (se 2 (by rfl) ⟨414906, by rfl⟩ : syracuseStep 1106417 = 829813) B829813
theorem B4186637 : Blo 774336 4186637 := bstep (se 3 (by rfl) ⟨784994, by rfl⟩ : syracuseStep 4186637 = 1569989) B1569989
theorem B1106497 : Blo 774336 1106497 := bstep (se 2 (by rfl) ⟨414936, by rfl⟩ : syracuseStep 1106497 = 829873) B829873
theorem B2613869 : Blo 774336 2613869 := bstep (se 3 (by rfl) ⟨490100, by rfl⟩ : syracuseStep 2613869 = 980201) B980201
theorem B2613923 : Blo 774336 2613923 := bstep (se 1 (by rfl) ⟨1960442, by rfl⟩ : syracuseStep 2613923 = 3920885) B3920885
theorem B4186829 : Blo 774336 4186829 := bstep (se 3 (by rfl) ⟨785030, by rfl⟩ : syracuseStep 4186829 = 1570061) B1570061
theorem B2941667 : Blo 774336 2941667 := bstep (se 1 (by rfl) ⟨2206250, by rfl⟩ : syracuseStep 2941667 = 4412501) B4412501
theorem B2614193 : Blo 774336 2614193 := bstep (se 2 (by rfl) ⟨980322, by rfl⟩ : syracuseStep 2614193 = 1960645) B1960645
theorem B5104709 : Blo 774336 5104709 := bstep (se 4 (by rfl) ⟨478566, by rfl⟩ : syracuseStep 5104709 = 957133) B957133
theorem B5301425 : Blo 774336 5301425 := bstep (se 2 (by rfl) ⟨1988034, by rfl⟩ : syracuseStep 5301425 = 3976069) B3976069
theorem B943315 : Blo 774336 943315 := bstep (se 1 (by rfl) ⟨707486, by rfl⟩ : syracuseStep 943315 = 1414973) B1414973
theorem B7464163 : Blo 774336 7464163 := bstep (se 1 (by rfl) ⟨5598122, by rfl⟩ : syracuseStep 7464163 = 11196245) B11196245
theorem B1107283 : Blo 774336 1107283 := bstep (se 1 (by rfl) ⟨830462, by rfl⟩ : syracuseStep 1107283 = 1660925) B1660925
theorem B4973957 : Blo 774336 4973957 := bstep (se 4 (by rfl) ⟨466308, by rfl⟩ : syracuseStep 4973957 = 932617) B932617
theorem B2614733 : Blo 774336 2614733 := bstep (se 3 (by rfl) ⟨490262, by rfl⟩ : syracuseStep 2614733 = 980525) B980525
theorem B2614787 : Blo 774336 2614787 := bstep (se 1 (by rfl) ⟨1961090, by rfl⟩ : syracuseStep 2614787 = 3922181) B3922181
theorem B2942669 : Blo 774336 2942669 := bstep (se 3 (by rfl) ⟨551750, by rfl⟩ : syracuseStep 2942669 = 1103501) B1103501
theorem B3925745 : Blo 774336 3925745 := bstep (se 2 (by rfl) ⟨1472154, by rfl⟩ : syracuseStep 3925745 = 2944309) B2944309
theorem B2615057 : Blo 774336 2615057 := bstep (se 2 (by rfl) ⟨980646, by rfl⟩ : syracuseStep 2615057 = 1961293) B1961293
theorem B1107761 : Blo 774336 1107761 := bstep (se 2 (by rfl) ⟨415410, by rfl⟩ : syracuseStep 1107761 = 830821) B830821
theorem B1107875 : Blo 774336 1107875 := bstep (se 1 (by rfl) ⟨830906, by rfl⟩ : syracuseStep 1107875 = 1661813) B1661813
theorem B3598285 : Blo 774336 3598285 := bstep (se 3 (by rfl) ⟨674678, by rfl⟩ : syracuseStep 3598285 = 1349357) B1349357
theorem B1107955 : Blo 774336 1107955 := bstep (se 1 (by rfl) ⟨830966, by rfl⟩ : syracuseStep 1107955 = 1661933) B1661933
theorem B4417649 : Blo 774336 4417649 := bstep (se 2 (by rfl) ⟨1656618, by rfl⟩ : syracuseStep 4417649 = 3313237) B3313237
theorem B2615597 : Blo 774336 2615597 := bstep (se 3 (by rfl) ⟨490424, by rfl⟩ : syracuseStep 2615597 = 980849) B980849
theorem B2615651 : Blo 774336 2615651 := bstep (se 1 (by rfl) ⟨1961738, by rfl⟩ : syracuseStep 2615651 = 3923477) B3923477
theorem B1894769 : Blo 774336 1894769 := bstep (se 2 (by rfl) ⟨710538, by rfl⟩ : syracuseStep 1894769 = 1421077) B1421077
theorem B6646157 : Blo 774336 6646157 := bstep (se 3 (by rfl) ⟨1246154, by rfl⟩ : syracuseStep 6646157 = 2492309) B2492309
theorem B1960433 : Blo 774336 1960433 := bstep (se 2 (by rfl) ⟨735162, by rfl⟩ : syracuseStep 1960433 = 1470325) B1470325
theorem B1960483 : Blo 774336 1960483 := bstep (se 1 (by rfl) ⟨1470362, by rfl⟩ : syracuseStep 1960483 = 2940725) B2940725
theorem B2615921 : Blo 774336 2615921 := bstep (se 2 (by rfl) ⟨980970, by rfl⟩ : syracuseStep 2615921 = 1961941) B1961941
theorem B2484877 : Blo 774336 2484877 := bstep (se 3 (by rfl) ⟨465914, by rfl⟩ : syracuseStep 2484877 = 931829) B931829
theorem B5892749 : Blo 774336 5892749 := bstep (se 3 (by rfl) ⟨1104890, by rfl⟩ : syracuseStep 5892749 = 2209781) B2209781
theorem B1960625 : Blo 774336 1960625 := bstep (se 2 (by rfl) ⟨735234, by rfl⟩ : syracuseStep 1960625 = 1470469) B1470469
theorem B3533645 : Blo 774336 3533645 := bstep (se 3 (by rfl) ⟨662558, by rfl⟩ : syracuseStep 3533645 = 1325117) B1325117
theorem B2616461 : Blo 774336 2616461 := bstep (se 3 (by rfl) ⟨490586, by rfl⟩ : syracuseStep 2616461 = 981173) B981173
theorem B3927203 : Blo 774336 3927203 := bstep (se 1 (by rfl) ⟨2945402, by rfl⟩ : syracuseStep 3927203 = 5890805) B5890805
theorem B2616515 : Blo 774336 2616515 := bstep (se 1 (by rfl) ⟨1962386, by rfl⟩ : syracuseStep 2616515 = 3924773) B3924773
theorem B2518289 : Blo 774336 2518289 := bstep (se 2 (by rfl) ⟨944358, by rfl⟩ : syracuseStep 2518289 = 1888717) B1888717
theorem B2616785 : Blo 774336 2616785 := bstep (se 2 (by rfl) ⟨981294, by rfl⟩ : syracuseStep 2616785 = 1962589) B1962589
theorem B4419107 : Blo 774336 4419107 := bstep (se 1 (by rfl) ⟨3314330, by rfl⟩ : syracuseStep 4419107 = 6628661) B6628661
theorem B1961617 : Blo 774336 1961617 := bstep (se 2 (by rfl) ⟨735606, by rfl⟩ : syracuseStep 1961617 = 1471213) B1471213
theorem B1863427 : Blo 774336 1863427 := bstep (se 1 (by rfl) ⟨1397570, by rfl⟩ : syracuseStep 1863427 = 2795141) B2795141
theorem B2944781 : Blo 774336 2944781 := bstep (se 3 (by rfl) ⟨552146, by rfl⟩ : syracuseStep 2944781 = 1104293) B1104293
theorem B4484899 : Blo 774336 4484899 := bstep (se 1 (by rfl) ⟨3363674, by rfl⟩ : syracuseStep 4484899 = 6727349) B6727349
theorem B1961891 : Blo 774336 1961891 := bstep (se 1 (by rfl) ⟨1471418, by rfl⟩ : syracuseStep 1961891 = 2942837) B2942837
theorem B3928013 : Blo 774336 3928013 := bstep (se 3 (by rfl) ⟨736502, by rfl⟩ : syracuseStep 3928013 = 1473005) B1473005
theorem B2617325 : Blo 774336 2617325 := bstep (se 3 (by rfl) ⟨490748, by rfl⟩ : syracuseStep 2617325 = 981497) B981497
theorem B2617379 : Blo 774336 2617379 := bstep (se 1 (by rfl) ⟨1963034, by rfl⟩ : syracuseStep 2617379 = 3926069) B3926069
theorem B2486339 : Blo 774336 2486339 := bstep (se 1 (by rfl) ⟨1864754, by rfl⟩ : syracuseStep 2486339 = 3729509) B3729509
theorem B1306705 : Blo 774336 1306705 := bstep (se 2 (by rfl) ⟨490014, by rfl⟩ : syracuseStep 1306705 = 980029) B980029
theorem B1470545 : Blo 774336 1470545 := bstep (se 2 (by rfl) ⟨551454, by rfl⟩ : syracuseStep 1470545 = 1102909) B1102909
theorem B1962083 : Blo 774336 1962083 := bstep (se 1 (by rfl) ⟨1471562, by rfl⟩ : syracuseStep 1962083 = 2943125) B2943125
theorem B1306739 : Blo 774336 1306739 := bstep (se 1 (by rfl) ⟨980054, by rfl⟩ : syracuseStep 1306739 = 1960109) B1960109
theorem B1306867 : Blo 774336 1306867 := bstep (se 1 (by rfl) ⟨980150, by rfl⟩ : syracuseStep 1306867 = 1960301) B1960301
theorem B2617649 : Blo 774336 2617649 := bstep (se 2 (by rfl) ⟨981618, by rfl⟩ : syracuseStep 2617649 = 1963237) B1963237
theorem B1863985 : Blo 774336 1863985 := bstep (se 2 (by rfl) ⟨698994, by rfl⟩ : syracuseStep 1863985 = 1397989) B1397989
theorem B2486609 : Blo 774336 2486609 := bstep (se 2 (by rfl) ⟨932478, by rfl⟩ : syracuseStep 2486609 = 1864957) B1864957
theorem B1307009 : Blo 774336 1307009 := bstep (se 2 (by rfl) ⟨490128, by rfl⟩ : syracuseStep 1307009 = 980257) B980257
theorem B1307137 : Blo 774336 1307137 := bstep (se 2 (by rfl) ⟨490176, by rfl⟩ : syracuseStep 1307137 = 980353) B980353
theorem B4420109 : Blo 774336 4420109 := bstep (se 3 (by rfl) ⟨828770, by rfl⟩ : syracuseStep 4420109 = 1657541) B1657541
theorem B1307171 : Blo 774336 1307171 := bstep (se 1 (by rfl) ⟨980378, by rfl⟩ : syracuseStep 1307171 = 1960757) B1960757
theorem B2945585 : Blo 774336 2945585 := bstep (se 2 (by rfl) ⟨1104594, by rfl⟩ : syracuseStep 2945585 = 2209189) B2209189
theorem B1241747 : Blo 774336 1241747 := bstep (se 1 (by rfl) ⟨931310, by rfl⟩ : syracuseStep 1241747 = 1862621) B1862621
theorem B1307299 : Blo 774336 1307299 := bstep (se 1 (by rfl) ⟨980474, by rfl⟩ : syracuseStep 1307299 = 1960949) B1960949
theorem B1307441 : Blo 774336 1307441 := bstep (se 2 (by rfl) ⟨490290, by rfl⟩ : syracuseStep 1307441 = 980581) B980581
theorem B2618189 : Blo 774336 2618189 := bstep (se 3 (by rfl) ⟨490910, by rfl⟩ : syracuseStep 2618189 = 981821) B981821
theorem B1241939 : Blo 774336 1241939 := bstep (se 1 (by rfl) ⟨931454, by rfl⟩ : syracuseStep 1241939 = 1862909) B1862909
theorem B2093933 : Blo 774336 2093933 := bstep (se 3 (by rfl) ⟨392612, by rfl⟩ : syracuseStep 2093933 = 785225) B785225
theorem B4977521 : Blo 774336 4977521 := bstep (se 2 (by rfl) ⟨1866570, by rfl⟩ : syracuseStep 4977521 = 3733141) B3733141
theorem B2618243 : Blo 774336 2618243 := bstep (se 1 (by rfl) ⟨1963682, by rfl⟩ : syracuseStep 2618243 = 3927365) B3927365
theorem B1307569 : Blo 774336 1307569 := bstep (se 2 (by rfl) ⟨490338, by rfl⟩ : syracuseStep 1307569 = 980677) B980677
theorem B1471441 : Blo 774336 1471441 := bstep (se 2 (by rfl) ⟨551790, by rfl⟩ : syracuseStep 1471441 = 1103581) B1103581
theorem B1864657 : Blo 774336 1864657 := bstep (se 2 (by rfl) ⟨699246, by rfl⟩ : syracuseStep 1864657 = 1398493) B1398493
theorem B1307603 : Blo 774336 1307603 := bstep (se 1 (by rfl) ⟨980702, by rfl⟩ : syracuseStep 1307603 = 1961405) B1961405
theorem B2094065 : Blo 774336 2094065 := bstep (se 2 (by rfl) ⟨785274, by rfl⟩ : syracuseStep 2094065 = 1570549) B1570549
theorem B1963025 : Blo 774336 1963025 := bstep (se 2 (by rfl) ⟨736134, by rfl⟩ : syracuseStep 1963025 = 1472269) B1472269
theorem B1963075 : Blo 774336 1963075 := bstep (se 1 (by rfl) ⟨1472306, by rfl⟩ : syracuseStep 1963075 = 2944613) B2944613
theorem B1307731 : Blo 774336 1307731 := bstep (se 1 (by rfl) ⟨980798, by rfl⟩ : syracuseStep 1307731 = 1961597) B1961597
theorem B1471601 : Blo 774336 1471601 := bstep (se 2 (by rfl) ⟨551850, by rfl⟩ : syracuseStep 1471601 = 1103701) B1103701
theorem B2618513 : Blo 774336 2618513 := bstep (se 2 (by rfl) ⟨981942, by rfl⟩ : syracuseStep 2618513 = 1963885) B1963885
theorem B2946253 : Blo 774336 2946253 := bstep (se 3 (by rfl) ⟨552422, by rfl⟩ : syracuseStep 2946253 = 1104845) B1104845
theorem B1963217 : Blo 774336 1963217 := bstep (se 2 (by rfl) ⟨736206, by rfl⟩ : syracuseStep 1963217 = 1472413) B1472413
theorem B1307873 : Blo 774336 1307873 := bstep (se 2 (by rfl) ⟨490452, by rfl⟩ : syracuseStep 1307873 = 980905) B980905
theorem B1308001 : Blo 774336 1308001 := bstep (se 2 (by rfl) ⟨490500, by rfl⟩ : syracuseStep 1308001 = 981001) B981001
theorem B1308035 : Blo 774336 1308035 := bstep (se 1 (by rfl) ⟨981026, by rfl⟩ : syracuseStep 1308035 = 1962053) B1962053
theorem B980419 : Blo 774336 980419 := bstep (se 1 (by rfl) ⟨735314, by rfl⟩ : syracuseStep 980419 = 1470629) B1470629
theorem B5895665 : Blo 774336 5895665 := bstep (se 2 (by rfl) ⟨2210874, by rfl⟩ : syracuseStep 5895665 = 4421749) B4421749
theorem B1308163 : Blo 774336 1308163 := bstep (se 1 (by rfl) ⟨981122, by rfl⟩ : syracuseStep 1308163 = 1962245) B1962245
theorem B1472003 : Blo 774336 1472003 := bstep (se 1 (by rfl) ⟨1104002, by rfl⟩ : syracuseStep 1472003 = 2208005) B2208005
theorem B980515 : Blo 774336 980515 := bstep (se 1 (by rfl) ⟨735386, by rfl⟩ : syracuseStep 980515 = 1470773) B1470773
theorem B2356771 : Blo 774336 2356771 := bstep (se 1 (by rfl) ⟨1767578, by rfl⟩ : syracuseStep 2356771 = 3535157) B3535157
theorem B1570403 : Blo 774336 1570403 := bstep (se 1 (by rfl) ⟨1177802, by rfl⟩ : syracuseStep 1570403 = 2355605) B2355605
theorem B1308305 : Blo 774336 1308305 := bstep (se 2 (by rfl) ⟨490614, by rfl⟩ : syracuseStep 1308305 = 981229) B981229
theorem B2619053 : Blo 774336 2619053 := bstep (se 3 (by rfl) ⟨491072, by rfl⟩ : syracuseStep 2619053 = 982145) B982145
theorem B2619107 : Blo 774336 2619107 := bstep (se 1 (by rfl) ⟨1964330, by rfl⟩ : syracuseStep 2619107 = 3928661) B3928661
theorem B1308433 : Blo 774336 1308433 := bstep (se 2 (by rfl) ⟨490662, by rfl⟩ : syracuseStep 1308433 = 981325) B981325
theorem B1308467 : Blo 774336 1308467 := bstep (se 1 (by rfl) ⟨981350, by rfl⟩ : syracuseStep 1308467 = 1962701) B1962701
theorem B1308595 : Blo 774336 1308595 := bstep (se 1 (by rfl) ⟨981446, by rfl⟩ : syracuseStep 1308595 = 1962893) B1962893
theorem B2947043 : Blo 774336 2947043 := bstep (se 1 (by rfl) ⟨2210282, by rfl⟩ : syracuseStep 2947043 = 4420565) B4420565
theorem B2619377 : Blo 774336 2619377 := bstep (se 2 (by rfl) ⟨982266, by rfl⟩ : syracuseStep 2619377 = 1964533) B1964533
theorem B981011 : Blo 774336 981011 := bstep (se 1 (by rfl) ⟨735758, by rfl⟩ : syracuseStep 981011 = 1471517) B1471517
theorem B20183093 : Blo 774336 20183093 := bstep (se 5 (by rfl) ⟨946082, by rfl⟩ : syracuseStep 20183093 = 1892165) B1892165
theorem B1308737 : Blo 774336 1308737 := bstep (se 2 (by rfl) ⟨490776, by rfl⟩ : syracuseStep 1308737 = 981553) B981553
theorem B1964209 : Blo 774336 1964209 := bstep (se 2 (by rfl) ⟨736578, by rfl⟩ : syracuseStep 1964209 = 1473157) B1473157
theorem B1308865 : Blo 774336 1308865 := bstep (se 2 (by rfl) ⟨490824, by rfl⟩ : syracuseStep 1308865 = 981649) B981649
theorem B1243361 : Blo 774336 1243361 := bstep (se 2 (by rfl) ⟨466260, by rfl⟩ : syracuseStep 1243361 = 932521) B932521
theorem B6617315 : Blo 774336 6617315 := bstep (se 1 (by rfl) ⟨4962986, by rfl⟩ : syracuseStep 6617315 = 9925973) B9925973
theorem B1308899 : Blo 774336 1308899 := bstep (se 1 (by rfl) ⟨981674, by rfl⟩ : syracuseStep 1308899 = 1963349) B1963349
theorem B4978979 : Blo 774336 4978979 := bstep (se 1 (by rfl) ⟨3734234, by rfl⟩ : syracuseStep 4978979 = 7468469) B7468469
theorem B1309027 : Blo 774336 1309027 := bstep (se 1 (by rfl) ⟨981770, by rfl⟩ : syracuseStep 1309027 = 1963541) B1963541
theorem B2652547 : Blo 774336 2652547 := bstep (se 1 (by rfl) ⟨1989410, by rfl⟩ : syracuseStep 2652547 = 3978821) B3978821
theorem B1472899 : Blo 774336 1472899 := bstep (se 1 (by rfl) ⟨1104674, by rfl⟩ : syracuseStep 1472899 = 2209349) B2209349
theorem B1964483 : Blo 774336 1964483 := bstep (se 1 (by rfl) ⟨1473362, by rfl⟩ : syracuseStep 1964483 = 2946725) B2946725
theorem B1309169 : Blo 774336 1309169 := bstep (se 2 (by rfl) ⟨490938, by rfl⟩ : syracuseStep 1309169 = 981877) B981877
theorem B2619917 : Blo 774336 2619917 := bstep (se 3 (by rfl) ⟨491234, by rfl⟩ : syracuseStep 2619917 = 982469) B982469
theorem B2521613 : Blo 774336 2521613 := bstep (se 3 (by rfl) ⟨472802, by rfl⟩ : syracuseStep 2521613 = 945605) B945605
theorem B1473059 : Blo 774336 1473059 := bstep (se 1 (by rfl) ⟨1104794, by rfl⟩ : syracuseStep 1473059 = 2209589) B2209589
theorem B2619971 : Blo 774336 2619971 := bstep (se 1 (by rfl) ⟨1964978, by rfl⟩ : syracuseStep 2619971 = 3929957) B3929957
theorem B1309297 : Blo 774336 1309297 := bstep (se 2 (by rfl) ⟨490986, by rfl⟩ : syracuseStep 1309297 = 981973) B981973
theorem B2947697 : Blo 774336 2947697 := bstep (se 2 (by rfl) ⟨1105386, by rfl⟩ : syracuseStep 2947697 = 2210773) B2210773
theorem B1178227 : Blo 774336 1178227 := bstep (se 1 (by rfl) ⟨883670, by rfl⟩ : syracuseStep 1178227 = 1767341) B1767341
theorem B1964675 : Blo 774336 1964675 := bstep (se 1 (by rfl) ⟨1473506, by rfl⟩ : syracuseStep 1964675 = 2947013) B2947013
theorem B1309331 : Blo 774336 1309331 := bstep (se 1 (by rfl) ⟨981998, by rfl⟩ : syracuseStep 1309331 = 1963997) B1963997
theorem B981715 : Blo 774336 981715 := bstep (se 1 (by rfl) ⟨736286, by rfl⟩ : syracuseStep 981715 = 1472573) B1472573
theorem B2489069 : Blo 774336 2489069 := bstep (se 3 (by rfl) ⟨466700, by rfl⟩ : syracuseStep 2489069 = 933401) B933401
theorem B1309459 : Blo 774336 1309459 := bstep (se 1 (by rfl) ⟨982094, by rfl⟩ : syracuseStep 1309459 = 1964189) B1964189
theorem B3930929 : Blo 774336 3930929 := bstep (se 2 (by rfl) ⟨1474098, by rfl⟩ : syracuseStep 3930929 = 2948197) B2948197
theorem B981811 : Blo 774336 981811 := bstep (se 1 (by rfl) ⟨736358, by rfl⟩ : syracuseStep 981811 = 1472717) B1472717
theorem B2620241 : Blo 774336 2620241 := bstep (se 2 (by rfl) ⟨982590, by rfl⟩ : syracuseStep 2620241 = 1965181) B1965181
theorem B1309601 : Blo 774336 1309601 := bstep (se 2 (by rfl) ⟨491100, by rfl⟩ : syracuseStep 1309601 = 982201) B982201
theorem B1309729 : Blo 774336 1309729 := bstep (se 2 (by rfl) ⟨491148, by rfl⟩ : syracuseStep 1309729 = 982297) B982297
theorem B1309763 : Blo 774336 1309763 := bstep (se 1 (by rfl) ⟨982322, by rfl⟩ : syracuseStep 1309763 = 1964645) B1964645
theorem B1047697 : Blo 774336 1047697 := bstep (se 2 (by rfl) ⟨392886, by rfl⟩ : syracuseStep 1047697 = 785773) B785773
theorem B2096291 : Blo 774336 2096291 := bstep (se 1 (by rfl) ⟨1572218, by rfl⟩ : syracuseStep 2096291 = 3144437) B3144437
theorem B1309891 : Blo 774336 1309891 := bstep (se 1 (by rfl) ⟨982418, by rfl⟩ : syracuseStep 1309891 = 1964837) B1964837
theorem B14908643 : Blo 774336 14908643 := bstep (se 1 (by rfl) ⟨11181482, by rfl⟩ : syracuseStep 14908643 = 22362965) B22362965
theorem B1047811 : Blo 774336 1047811 := bstep (se 1 (by rfl) ⟨785858, by rfl⟩ : syracuseStep 1047811 = 1571717) B1571717
theorem B4979981 : Blo 774336 4979981 := bstep (se 3 (by rfl) ⟨933746, by rfl⟩ : syracuseStep 4979981 = 1867493) B1867493
theorem B982307 : Blo 774336 982307 := bstep (se 1 (by rfl) ⟨736730, by rfl⟩ : syracuseStep 982307 = 1473461) B1473461
theorem B1047875 : Blo 774336 1047875 := bstep (se 1 (by rfl) ⟨785906, by rfl⟩ : syracuseStep 1047875 = 1571813) B1571813
theorem B1310033 : Blo 774336 1310033 := bstep (se 2 (by rfl) ⟨491262, by rfl⟩ : syracuseStep 1310033 = 982525) B982525
theorem B2620781 : Blo 774336 2620781 := bstep (se 3 (by rfl) ⟨491396, by rfl⟩ : syracuseStep 2620781 = 982793) B982793
theorem B4423025 : Blo 774336 4423025 := bstep (se 2 (by rfl) ⟨1658634, by rfl⟩ : syracuseStep 4423025 = 3317269) B3317269
theorem B1080707 : Blo 774336 1080707 := bstep (se 1 (by rfl) ⟨810530, by rfl⟩ : syracuseStep 1080707 = 1621061) B1621061
theorem B2620835 : Blo 774336 2620835 := bstep (se 1 (by rfl) ⟨1965626, by rfl⟩ : syracuseStep 2620835 = 3931253) B3931253
theorem B1310161 : Blo 774336 1310161 := bstep (se 2 (by rfl) ⟨491310, by rfl⟩ : syracuseStep 1310161 = 982621) B982621
theorem B1310195 : Blo 774336 1310195 := bstep (se 1 (by rfl) ⟨982646, by rfl⟩ : syracuseStep 1310195 = 1965293) B1965293
theorem B1965617 : Blo 774336 1965617 := bstep (se 2 (by rfl) ⟨737106, by rfl⟩ : syracuseStep 1965617 = 1474213) B1474213
theorem B1474129 : Blo 774336 1474129 := bstep (se 2 (by rfl) ⟨552798, by rfl⟩ : syracuseStep 1474129 = 1105597) B1105597
theorem B1965667 : Blo 774336 1965667 := bstep (se 1 (by rfl) ⟨1474250, by rfl⟩ : syracuseStep 1965667 = 2948501) B2948501
theorem B1310323 : Blo 774336 1310323 := bstep (se 1 (by rfl) ⟨982742, by rfl⟩ : syracuseStep 1310323 = 1965485) B1965485
theorem B2621105 : Blo 774336 2621105 := bstep (se 2 (by rfl) ⟨982914, by rfl⟩ : syracuseStep 2621105 = 1965829) B1965829
theorem B1244899 : Blo 774336 1244899 := bstep (se 1 (by rfl) ⟨933674, by rfl⟩ : syracuseStep 1244899 = 1867349) B1867349
theorem B9928433 : Blo 774336 9928433 := bstep (se 2 (by rfl) ⟨3723162, by rfl⟩ : syracuseStep 9928433 = 7446325) B7446325
theorem B1965809 : Blo 774336 1965809 := bstep (se 2 (by rfl) ⟨737178, by rfl⟩ : syracuseStep 1965809 = 1474357) B1474357
theorem B1310465 : Blo 774336 1310465 := bstep (se 2 (by rfl) ⟨491424, by rfl⟩ : syracuseStep 1310465 = 982849) B982849
theorem B1244945 : Blo 774336 1244945 := bstep (se 2 (by rfl) ⟨466854, by rfl⟩ : syracuseStep 1244945 = 933709) B933709
theorem B884579 : Blo 774336 884579 := bstep (se 1 (by rfl) ⟨663434, by rfl⟩ : syracuseStep 884579 = 1326869) B1326869
theorem B3145571 : Blo 774336 3145571 := bstep (se 1 (by rfl) ⟨2359178, by rfl⟩ : syracuseStep 3145571 = 4718357) B4718357
theorem B1310593 : Blo 774336 1310593 := bstep (se 2 (by rfl) ⟨491472, by rfl⟩ : syracuseStep 1310593 = 982945) B982945
theorem B1310627 : Blo 774336 1310627 := bstep (se 1 (by rfl) ⟨982970, by rfl⟩ : syracuseStep 1310627 = 1965941) B1965941
theorem B983011 : Blo 774336 983011 := bstep (se 1 (by rfl) ⟨737258, by rfl⟩ : syracuseStep 983011 = 1474517) B1474517
theorem B1966103 : Blo 774336 1966103 := bstep (se 1 (by rfl) ⟨1474577, by rfl⟩ : syracuseStep 1966103 = 2949155) B2949155
theorem B3932225 : Blo 774336 3932225 := bstep (se 2 (by rfl) ⟨1474584, by rfl⟩ : syracuseStep 3932225 = 2949169) B2949169
theorem B1310809 : Blo 774336 1310809 := bstep (se 2 (by rfl) ⟨491553, by rfl⟩ : syracuseStep 1310809 = 983107) B983107
theorem B6619229 : Blo 774336 6619229 := bstep (se 3 (by rfl) ⟨1241105, by rfl⟩ : syracuseStep 6619229 = 2482211) B2482211
theorem B1474699 : Blo 774336 1474699 := bstep (se 1 (by rfl) ⟨1106024, by rfl⟩ : syracuseStep 1474699 = 2212049) B2212049
theorem B2621591 : Blo 774336 2621591 := bstep (se 1 (by rfl) ⟨1966193, by rfl⟩ : syracuseStep 2621591 = 3932387) B3932387
theorem B1573273 : Blo 774336 1573273 := bstep (se 2 (by rfl) ⟨589977, by rfl⟩ : syracuseStep 1573273 = 1179955) B1179955
theorem B885163 : Blo 774336 885163 := bstep (se 1 (by rfl) ⟨663872, by rfl⟩ : syracuseStep 885163 = 1327745) B1327745
theorem B2949655 : Blo 774336 2949655 := bstep (se 1 (by rfl) ⟨2212241, by rfl⟩ : syracuseStep 2949655 = 4424483) B4424483
theorem B1245719 : Blo 774336 1245719 := bstep (se 1 (by rfl) ⟨934289, by rfl⟩ : syracuseStep 1245719 = 1868579) B1868579
theorem B1475147 : Blo 774336 1475147 := bstep (se 1 (by rfl) ⟨1106360, by rfl⟩ : syracuseStep 1475147 = 2212721) B2212721
theorem B1311383 : Blo 774336 1311383 := bstep (se 1 (by rfl) ⟨983537, by rfl⟩ : syracuseStep 1311383 = 1967075) B1967075
theorem B2622131 : Blo 774336 2622131 := bstep (se 1 (by rfl) ⟨1966598, by rfl⟩ : syracuseStep 2622131 = 3933197) B3933197
theorem B983755 : Blo 774336 983755 := bstep (se 1 (by rfl) ⟨737816, by rfl⟩ : syracuseStep 983755 = 1475633) B1475633
theorem B1475329 : Blo 774336 1475329 := bstep (se 2 (by rfl) ⟨553248, by rfl⟩ : syracuseStep 1475329 = 1106497) B1106497
theorem B1311511 : Blo 774336 1311511 := bstep (se 1 (by rfl) ⟨983633, by rfl⟩ : syracuseStep 1311511 = 1967267) B1967267
theorem B1966913 : Blo 774336 1966913 := bstep (se 2 (by rfl) ⟨737592, by rfl⟩ : syracuseStep 1966913 = 1475185) B1475185
theorem B2360153 : Blo 774336 2360153 := bstep (se 2 (by rfl) ⟨885057, by rfl⟩ : syracuseStep 2360153 = 1770115) B1770115
theorem B2622401 : Blo 774336 2622401 := bstep (se 2 (by rfl) ⟨983400, by rfl⟩ : syracuseStep 2622401 = 1966801) B1966801
theorem B787415 : Blo 774336 787415 := bstep (se 1 (by rfl) ⟨590561, by rfl⟩ : syracuseStep 787415 = 1181123) B1181123
theorem B4424665 : Blo 774336 4424665 := bstep (se 2 (by rfl) ⟨1659249, by rfl⟩ : syracuseStep 4424665 = 3318499) B3318499
theorem B24249419 : Blo 774336 24249419 := bstep (se 1 (by rfl) ⟨18187064, by rfl⟩ : syracuseStep 24249419 = 36374129) B36374129
theorem B1246283 : Blo 774336 1246283 := bstep (se 1 (by rfl) ⟨934712, by rfl⟩ : syracuseStep 1246283 = 1869425) B1869425
theorem B1475671 : Blo 774336 1475671 := bstep (se 1 (by rfl) ⟨1106753, by rfl⟩ : syracuseStep 1475671 = 2213507) B2213507
theorem B6620291 : Blo 774336 6620291 := bstep (se 1 (by rfl) ⟨4965218, by rfl⟩ : syracuseStep 6620291 = 9930437) B9930437
theorem B3736849 : Blo 774336 3736849 := bstep (se 2 (by rfl) ⟨1401318, by rfl⟩ : syracuseStep 3736849 = 2802637) B2802637
theorem B2950445 : Blo 774336 2950445 := bstep (se 3 (by rfl) ⟨553208, by rfl⟩ : syracuseStep 2950445 = 1106417) B1106417
theorem B1475891 : Blo 774336 1475891 := bstep (se 1 (by rfl) ⟨1106918, by rfl⟩ : syracuseStep 1475891 = 2213837) B2213837
theorem B1967449 : Blo 774336 1967449 := bstep (se 2 (by rfl) ⟨737793, by rfl⟩ : syracuseStep 1967449 = 1475587) B1475587
theorem B1312139 : Blo 774336 1312139 := bstep (se 1 (by rfl) ⟨984104, by rfl⟩ : syracuseStep 1312139 = 1968209) B1968209
theorem B2098649 : Blo 774336 2098649 := bstep (se 2 (by rfl) ⟨786993, by rfl⟩ : syracuseStep 2098649 = 1573987) B1573987
theorem B2622941 : Blo 774336 2622941 := bstep (se 3 (by rfl) ⟨491801, by rfl⟩ : syracuseStep 2622941 = 983603) B983603
theorem B787979 : Blo 774336 787979 := bstep (se 1 (by rfl) ⟨590984, by rfl⟩ : syracuseStep 787979 = 1181969) B1181969
theorem B1312267 : Blo 774336 1312267 := bstep (se 1 (by rfl) ⟨984200, by rfl⟩ : syracuseStep 1312267 = 1968401) B1968401
theorem B1476119 : Blo 774336 1476119 := bstep (se 1 (by rfl) ⟨1107089, by rfl⟩ : syracuseStep 1476119 = 2214179) B2214179
theorem B3311255 : Blo 774336 3311255 := bstep (se 1 (by rfl) ⟨2483441, by rfl⟩ : syracuseStep 3311255 = 4966883) B4966883
theorem B984727 : Blo 774336 984727 := bstep (se 1 (by rfl) ⟨738545, by rfl⟩ : syracuseStep 984727 = 1477091) B1477091
theorem B1312409 : Blo 774336 1312409 := bstep (se 2 (by rfl) ⟨492153, by rfl⟩ : syracuseStep 1312409 = 984307) B984307
theorem B1476377 : Blo 774336 1476377 := bstep (se 2 (by rfl) ⟨553641, by rfl⟩ : syracuseStep 1476377 = 1107283) B1107283
theorem B1312537 : Blo 774336 1312537 := bstep (se 2 (by rfl) ⟨492201, by rfl⟩ : syracuseStep 1312537 = 984403) B984403
theorem B4425623 : Blo 774336 4425623 := bstep (se 1 (by rfl) ⟨3319217, by rfl⟩ : syracuseStep 4425623 = 6638435) B6638435
theorem B3311563 : Blo 774336 3311563 := bstep (se 1 (by rfl) ⟨2483672, by rfl⟩ : syracuseStep 3311563 = 4967345) B4967345
theorem B3934169 : Blo 774336 3934169 := bstep (se 2 (by rfl) ⟨1475313, by rfl⟩ : syracuseStep 3934169 = 2950627) B2950627
theorem B1476787 : Blo 774336 1476787 := bstep (se 1 (by rfl) ⟨1107590, by rfl⟩ : syracuseStep 1476787 = 2215181) B2215181
theorem B3311837 : Blo 774336 3311837 := bstep (se 3 (by rfl) ⟨620969, by rfl⟩ : syracuseStep 3311837 = 1241939) B1241939
theorem B1313111 : Blo 774336 1313111 := bstep (se 1 (by rfl) ⟨984833, by rfl⟩ : syracuseStep 1313111 = 1969667) B1969667
theorem B788887 : Blo 774336 788887 := bstep (se 1 (by rfl) ⟨591665, by rfl⟩ : syracuseStep 788887 = 1183331) B1183331
theorem B1968563 : Blo 774336 1968563 := bstep (se 1 (by rfl) ⟨1476422, by rfl⟩ : syracuseStep 1968563 = 2952845) B2952845
theorem B1313239 : Blo 774336 1313239 := bstep (se 1 (by rfl) ⟨984929, by rfl⟩ : syracuseStep 1313239 = 1969859) B1969859
theorem B2984471 : Blo 774336 2984471 := bstep (se 1 (by rfl) ⟨2238353, by rfl⟩ : syracuseStep 2984471 = 4476707) B4476707
theorem B1706521 : Blo 774336 1706521 := bstep (se 2 (by rfl) ⟨639945, by rfl⟩ : syracuseStep 1706521 = 1279891) B1279891
theorem B2624075 : Blo 774336 2624075 := bstep (se 1 (by rfl) ⟨1968056, by rfl⟩ : syracuseStep 2624075 = 3936113) B3936113
theorem B4983389 : Blo 774336 4983389 := bstep (se 3 (by rfl) ⟨934385, by rfl⟩ : syracuseStep 4983389 = 1868771) B1868771
theorem B10783363 : Blo 774336 10783363 := bstep (se 1 (by rfl) ⟨8087522, by rfl⟩ : syracuseStep 10783363 = 16175045) B16175045
theorem B1182359 : Blo 774336 1182359 := bstep (se 1 (by rfl) ⟨886769, by rfl⟩ : syracuseStep 1182359 = 1773539) B1773539
theorem B1477273 : Blo 774336 1477273 := bstep (se 2 (by rfl) ⟨553977, by rfl⟩ : syracuseStep 1477273 = 1107955) B1107955
theorem B2951873 : Blo 774336 2951873 := bstep (se 2 (by rfl) ⟨1106952, by rfl⟩ : syracuseStep 2951873 = 2213905) B2213905
theorem B1968857 : Blo 774336 1968857 := bstep (se 2 (by rfl) ⟨738321, by rfl⟩ : syracuseStep 1968857 = 1476643) B1476643
theorem B2624345 : Blo 774336 2624345 := bstep (se 2 (by rfl) ⟨984129, by rfl⟩ : syracuseStep 2624345 = 1968259) B1968259
theorem B2493335 : Blo 774336 2493335 := bstep (se 1 (by rfl) ⟨1870001, by rfl⟩ : syracuseStep 2493335 = 3740003) B3740003
theorem B2100161 : Blo 774336 2100161 := bstep (se 2 (by rfl) ⟨787560, by rfl⟩ : syracuseStep 2100161 = 1575121) B1575121
theorem B5049305 : Blo 774336 5049305 := bstep (se 2 (by rfl) ⟨1893489, by rfl⟩ : syracuseStep 5049305 = 3786979) B3786979
theorem B28314805 : Blo 774336 28314805 := bstep (se 5 (by rfl) ⟨1327256, by rfl⟩ : syracuseStep 28314805 = 2654513) B2654513
theorem B3313169 : Blo 774336 3313169 := bstep (se 2 (by rfl) ⟨1242438, by rfl⟩ : syracuseStep 3313169 = 2484877) B2484877
theorem B2625047 : Blo 774336 2625047 := bstep (se 1 (by rfl) ⟨1968785, by rfl⟩ : syracuseStep 2625047 = 3937571) B3937571
theorem B3935789 : Blo 774336 3935789 := bstep (se 3 (by rfl) ⟨737960, by rfl⟩ : syracuseStep 3935789 = 1475921) B1475921
theorem B2100811 : Blo 774336 2100811 := bstep (se 1 (by rfl) ⟨1575608, by rfl⟩ : syracuseStep 2100811 = 3151217) B3151217
theorem B3149401 : Blo 774336 3149401 := bstep (se 2 (by rfl) ⟨1181025, by rfl⟩ : syracuseStep 3149401 = 2362051) B2362051
theorem B8949379 : Blo 774336 8949379 := bstep (se 1 (by rfl) ⟨6712034, by rfl⟩ : syracuseStep 8949379 = 13424069) B13424069
theorem B2625587 : Blo 774336 2625587 := bstep (se 1 (by rfl) ⟨1969190, by rfl⟩ : syracuseStep 2625587 = 3938381) B3938381
theorem B2953361 : Blo 774336 2953361 := bstep (se 2 (by rfl) ⟨1107510, by rfl⟩ : syracuseStep 2953361 = 2215021) B2215021
theorem B2625857 : Blo 774336 2625857 := bstep (se 2 (by rfl) ⟨984696, by rfl⟩ : syracuseStep 2625857 = 1969393) B1969393
theorem B4428107 : Blo 774336 4428107 := bstep (se 1 (by rfl) ⟨3321080, by rfl⟩ : syracuseStep 4428107 = 6642161) B6642161
theorem B2953817 : Blo 774336 2953817 := bstep (se 2 (by rfl) ⟨1107681, by rfl⟩ : syracuseStep 2953817 = 2215363) B2215363
theorem B2954029 : Blo 774336 2954029 := bstep (se 3 (by rfl) ⟨553880, by rfl⟩ : syracuseStep 2954029 = 1107761) B1107761
theorem B2626397 : Blo 774336 2626397 := bstep (se 3 (by rfl) ⟨492449, by rfl⟩ : syracuseStep 2626397 = 984899) B984899
theorem B2102195 : Blo 774336 2102195 := bstep (se 1 (by rfl) ⟨1576646, by rfl⟩ : syracuseStep 2102195 = 3153293) B3153293
theorem B4723805 : Blo 774336 4723805 := bstep (se 3 (by rfl) ⟨885713, by rfl⟩ : syracuseStep 4723805 = 1771427) B1771427
theorem B2954333 : Blo 774336 2954333 := bstep (se 3 (by rfl) ⟨553937, by rfl⟩ : syracuseStep 2954333 = 1107875) B1107875
theorem B3151021 : Blo 774336 3151021 := bstep (se 3 (by rfl) ⟨590816, by rfl⟩ : syracuseStep 3151021 = 1181633) B1181633
theorem B1742273 : Blo 774336 1742273 := bstep (se 2 (by rfl) ⟨653352, by rfl⟩ : syracuseStep 1742273 = 1306705) B1306705
theorem B1742489 : Blo 774336 1742489 := bstep (se 2 (by rfl) ⟨653433, by rfl⟩ : syracuseStep 1742489 = 1306867) B1306867
theorem B2791091 : Blo 774336 2791091 := bstep (se 1 (by rfl) ⟨2093318, by rfl⟩ : syracuseStep 2791091 = 4186637) B4186637
theorem B1742579 : Blo 774336 1742579 := bstep (se 1 (by rfl) ⟨1306934, by rfl⟩ : syracuseStep 1742579 = 2613869) B2613869
theorem B1742615 : Blo 774336 1742615 := bstep (se 1 (by rfl) ⟨1306961, by rfl⟩ : syracuseStep 1742615 = 2613923) B2613923
theorem B8951597 : Blo 774336 8951597 := bstep (se 3 (by rfl) ⟨1678424, by rfl⟩ : syracuseStep 8951597 = 3356849) B3356849
theorem B3315629 : Blo 774336 3315629 := bstep (se 3 (by rfl) ⟨621680, by rfl⟩ : syracuseStep 3315629 = 1243361) B1243361
theorem B1742795 : Blo 774336 1742795 := bstep (se 1 (by rfl) ⟨1307096, by rfl⟩ : syracuseStep 1742795 = 2614193) B2614193
theorem B1742849 : Blo 774336 1742849 := bstep (se 2 (by rfl) ⟨653568, by rfl⟩ : syracuseStep 1742849 = 1307137) B1307137
theorem B1743065 : Blo 774336 1743065 := bstep (se 2 (by rfl) ⟨653649, by rfl⟩ : syracuseStep 1743065 = 1307299) B1307299
theorem B3315971 : Blo 774336 3315971 := bstep (se 1 (by rfl) ⟨2486978, by rfl⟩ : syracuseStep 3315971 = 4973957) B4973957
theorem B1743155 : Blo 774336 1743155 := bstep (se 1 (by rfl) ⟨1307366, by rfl⟩ : syracuseStep 1743155 = 2614733) B2614733
theorem B8395073 : Blo 774336 8395073 := bstep (se 2 (by rfl) ⟨3148152, by rfl⟩ : syracuseStep 8395073 = 6296305) B6296305
theorem B1743191 : Blo 774336 1743191 := bstep (se 1 (by rfl) ⟨1307393, by rfl⟩ : syracuseStep 1743191 = 2614787) B2614787
theorem B8395109 : Blo 774336 8395109 := bstep (se 4 (by rfl) ⟨787041, by rfl⟩ : syracuseStep 8395109 = 1574083) B1574083
theorem B1743371 : Blo 774336 1743371 := bstep (se 1 (by rfl) ⟨1307528, by rfl⟩ : syracuseStep 1743371 = 2615057) B2615057
theorem B1743425 : Blo 774336 1743425 := bstep (se 2 (by rfl) ⟨653784, by rfl⟩ : syracuseStep 1743425 = 1307569) B1307569
theorem B3152515 : Blo 774336 3152515 := bstep (se 1 (by rfl) ⟨2364386, by rfl⟩ : syracuseStep 3152515 = 4728773) B4728773
theorem B1743641 : Blo 774336 1743641 := bstep (se 2 (by rfl) ⟨653865, by rfl⟩ : syracuseStep 1743641 = 1307731) B1307731
theorem B1743731 : Blo 774336 1743731 := bstep (se 1 (by rfl) ⟨1307798, by rfl⟩ : syracuseStep 1743731 = 2615597) B2615597
theorem B1743767 : Blo 774336 1743767 := bstep (se 1 (by rfl) ⟨1307825, by rfl⟩ : syracuseStep 1743767 = 2615651) B2615651
theorem B1973143 : Blo 774336 1973143 := bstep (se 1 (by rfl) ⟨1479857, by rfl⟩ : syracuseStep 1973143 = 2959715) B2959715
theorem B4430771 : Blo 774336 4430771 := bstep (se 1 (by rfl) ⟨3323078, by rfl⟩ : syracuseStep 4430771 = 6646157) B6646157
theorem B1743947 : Blo 774336 1743947 := bstep (se 1 (by rfl) ⟨1307960, by rfl⟩ : syracuseStep 1743947 = 2615921) B2615921
theorem B1744001 : Blo 774336 1744001 := bstep (se 2 (by rfl) ⟨654000, by rfl⟩ : syracuseStep 1744001 = 1308001) B1308001
theorem B1744217 : Blo 774336 1744217 := bstep (se 2 (by rfl) ⟨654081, by rfl⟩ : syracuseStep 1744217 = 1308163) B1308163
theorem B3939677 : Blo 774336 3939677 := bstep (se 3 (by rfl) ⟨738689, by rfl⟩ : syracuseStep 3939677 = 1477379) B1477379
theorem B1744307 : Blo 774336 1744307 := bstep (se 1 (by rfl) ⟨1308230, by rfl⟩ : syracuseStep 1744307 = 2616461) B2616461
theorem B8068531 : Blo 774336 8068531 := bstep (se 1 (by rfl) ⟨6051398, by rfl⟩ : syracuseStep 8068531 = 12102797) B12102797
theorem B1744343 : Blo 774336 1744343 := bstep (se 1 (by rfl) ⟨1308257, by rfl⟩ : syracuseStep 1744343 = 2616515) B2616515
theorem B1678859 : Blo 774336 1678859 := bstep (se 1 (by rfl) ⟨1259144, by rfl⟩ : syracuseStep 1678859 = 2518289) B2518289
theorem B1744523 : Blo 774336 1744523 := bstep (se 1 (by rfl) ⟨1308392, by rfl⟩ : syracuseStep 1744523 = 2616785) B2616785
theorem B1744577 : Blo 774336 1744577 := bstep (se 2 (by rfl) ⟨654216, by rfl⟩ : syracuseStep 1744577 = 1308433) B1308433
theorem B1941185 : Blo 774336 1941185 := bstep (se 2 (by rfl) ⟨727944, by rfl⟩ : syracuseStep 1941185 = 1455889) B1455889
theorem B1744793 : Blo 774336 1744793 := bstep (se 2 (by rfl) ⟨654297, by rfl⟩ : syracuseStep 1744793 = 1308595) B1308595
theorem B1744883 : Blo 774336 1744883 := bstep (se 1 (by rfl) ⟨1308662, by rfl⟩ : syracuseStep 1744883 = 2617325) B2617325
theorem B28712981 : Blo 774336 28712981 := bstep (se 6 (by rfl) ⟨672960, by rfl⟩ : syracuseStep 28712981 = 1345921) B1345921
theorem B1744919 : Blo 774336 1744919 := bstep (se 1 (by rfl) ⟨1308689, by rfl⟩ : syracuseStep 1744919 = 2617379) B2617379
theorem B1745099 : Blo 774336 1745099 := bstep (se 1 (by rfl) ⟨1308824, by rfl⟩ : syracuseStep 1745099 = 2617649) B2617649
theorem B1745153 : Blo 774336 1745153 := bstep (se 2 (by rfl) ⟨654432, by rfl⟩ : syracuseStep 1745153 = 1308865) B1308865
theorem B4432229 : Blo 774336 4432229 := bstep (se 4 (by rfl) ⟨415521, by rfl⟩ : syracuseStep 4432229 = 831043) B831043
theorem B827831 : Blo 774336 827831 := bstep (se 1 (by rfl) ⟨620873, by rfl⟩ : syracuseStep 827831 = 1241747) B1241747
theorem B1745369 : Blo 774336 1745369 := bstep (se 2 (by rfl) ⟨654513, by rfl⟩ : syracuseStep 1745369 = 1309027) B1309027
theorem B1745459 : Blo 774336 1745459 := bstep (se 1 (by rfl) ⟨1309094, by rfl⟩ : syracuseStep 1745459 = 2618189) B2618189
theorem B3318347 : Blo 774336 3318347 := bstep (se 1 (by rfl) ⟨2488760, by rfl⟩ : syracuseStep 3318347 = 4977521) B4977521
theorem B1745495 : Blo 774336 1745495 := bstep (se 1 (by rfl) ⟨1309121, by rfl⟩ : syracuseStep 1745495 = 2618243) B2618243
theorem B3023581 : Blo 774336 3023581 := bstep (se 3 (by rfl) ⟨566921, by rfl⟩ : syracuseStep 3023581 = 1133843) B1133843
theorem B1745675 : Blo 774336 1745675 := bstep (se 1 (by rfl) ⟨1309256, by rfl⟩ : syracuseStep 1745675 = 2618513) B2618513
theorem B1745729 : Blo 774336 1745729 := bstep (se 2 (by rfl) ⟨654648, by rfl⟩ : syracuseStep 1745729 = 1309297) B1309297
theorem B2794333 : Blo 774336 2794333 := bstep (se 3 (by rfl) ⟨523937, by rfl⟩ : syracuseStep 2794333 = 1047875) B1047875
theorem B1745945 : Blo 774336 1745945 := bstep (se 2 (by rfl) ⟨654729, by rfl⟩ : syracuseStep 1745945 = 1309459) B1309459
theorem B1746035 : Blo 774336 1746035 := bstep (se 1 (by rfl) ⟨1309526, by rfl⟩ : syracuseStep 1746035 = 2619053) B2619053
theorem B1746071 : Blo 774336 1746071 := bstep (se 1 (by rfl) ⟨1309553, by rfl⟩ : syracuseStep 1746071 = 2619107) B2619107
theorem B1746251 : Blo 774336 1746251 := bstep (se 1 (by rfl) ⟨1309688, by rfl⟩ : syracuseStep 1746251 = 2619377) B2619377
theorem B1746305 : Blo 774336 1746305 := bstep (se 2 (by rfl) ⟨654864, by rfl⟩ : syracuseStep 1746305 = 1309729) B1309729
theorem B16983445 : Blo 774336 16983445 := bstep (se 6 (by rfl) ⟨398049, by rfl⟩ : syracuseStep 16983445 = 796099) B796099
theorem B3319319 : Blo 774336 3319319 := bstep (se 1 (by rfl) ⟨2489489, by rfl⟩ : syracuseStep 3319319 = 4978979) B4978979
theorem B1746521 : Blo 774336 1746521 := bstep (se 2 (by rfl) ⟨654945, by rfl⟩ : syracuseStep 1746521 = 1309891) B1309891
theorem B8955485 : Blo 774336 8955485 := bstep (se 3 (by rfl) ⟨1679153, by rfl⟩ : syracuseStep 8955485 = 3358307) B3358307
theorem B1746611 : Blo 774336 1746611 := bstep (se 1 (by rfl) ⟨1309958, by rfl⟩ : syracuseStep 1746611 = 2619917) B2619917
theorem B1681075 : Blo 774336 1681075 := bstep (se 1 (by rfl) ⟨1260806, by rfl⟩ : syracuseStep 1681075 = 2521613) B2521613
theorem B1746647 : Blo 774336 1746647 := bstep (se 1 (by rfl) ⟨1309985, by rfl⟩ : syracuseStep 1746647 = 2619971) B2619971
theorem B8857349 : Blo 774336 8857349 := bstep (se 4 (by rfl) ⟨830376, by rfl⟩ : syracuseStep 8857349 = 1660753) B1660753
theorem B1746827 : Blo 774336 1746827 := bstep (se 1 (by rfl) ⟨1310120, by rfl⟩ : syracuseStep 1746827 = 2620241) B2620241
theorem B1746881 : Blo 774336 1746881 := bstep (se 2 (by rfl) ⟨655080, by rfl⟩ : syracuseStep 1746881 = 1310161) B1310161
theorem B9939095 : Blo 774336 9939095 := bstep (se 1 (by rfl) ⟨7454321, by rfl⟩ : syracuseStep 9939095 = 14908643) B14908643
theorem B1747097 : Blo 774336 1747097 := bstep (se 2 (by rfl) ⟨655161, by rfl⟩ : syracuseStep 1747097 = 1310323) B1310323
theorem B3319987 : Blo 774336 3319987 := bstep (se 1 (by rfl) ⟨2489990, by rfl⟩ : syracuseStep 3319987 = 4979981) B4979981
theorem B1747187 : Blo 774336 1747187 := bstep (se 1 (by rfl) ⟨1310390, by rfl⟩ : syracuseStep 1747187 = 2620781) B2620781
theorem B1747223 : Blo 774336 1747223 := bstep (se 1 (by rfl) ⟨1310417, by rfl⟩ : syracuseStep 1747223 = 2620835) B2620835
theorem B2206045 : Blo 774336 2206045 := bstep (se 3 (by rfl) ⟨413633, by rfl⟩ : syracuseStep 2206045 = 827267) B827267
theorem B1747403 : Blo 774336 1747403 := bstep (se 1 (by rfl) ⟨1310552, by rfl⟩ : syracuseStep 1747403 = 2621105) B2621105
theorem B1747457 : Blo 774336 1747457 := bstep (se 2 (by rfl) ⟨655296, by rfl⟩ : syracuseStep 1747457 = 1310593) B1310593
theorem B829963 : Blo 774336 829963 := bstep (se 1 (by rfl) ⟨622472, by rfl⟩ : syracuseStep 829963 = 1244945) B1244945
theorem B2206273 : Blo 774336 2206273 := bstep (se 2 (by rfl) ⟨827352, by rfl⟩ : syracuseStep 2206273 = 1654705) B1654705
theorem B1747673 : Blo 774336 1747673 := bstep (se 2 (by rfl) ⟨655377, by rfl⟩ : syracuseStep 1747673 = 1310755) B1310755
theorem B1747763 : Blo 774336 1747763 := bstep (se 1 (by rfl) ⟨1310822, by rfl⟩ : syracuseStep 1747763 = 2621645) B2621645
theorem B2796353 : Blo 774336 2796353 := bstep (se 2 (by rfl) ⟨1048632, by rfl⟩ : syracuseStep 2796353 = 2097265) B2097265
theorem B1747799 : Blo 774336 1747799 := bstep (se 1 (by rfl) ⟨1310849, by rfl⟩ : syracuseStep 1747799 = 2621699) B2621699
theorem B2206615 : Blo 774336 2206615 := bstep (se 1 (by rfl) ⟨1654961, by rfl⟩ : syracuseStep 2206615 = 3309923) B3309923
theorem B2796439 : Blo 774336 2796439 := bstep (se 1 (by rfl) ⟨2097329, by rfl⟩ : syracuseStep 2796439 = 4194659) B4194659
theorem B1747979 : Blo 774336 1747979 := bstep (se 1 (by rfl) ⟨1310984, by rfl⟩ : syracuseStep 1747979 = 2621969) B2621969
theorem B1748033 : Blo 774336 1748033 := bstep (se 2 (by rfl) ⟨655512, by rfl⟩ : syracuseStep 1748033 = 1311025) B1311025
theorem B1748249 : Blo 774336 1748249 := bstep (se 2 (by rfl) ⟨655593, by rfl⟩ : syracuseStep 1748249 = 1311187) B1311187
theorem B1748339 : Blo 774336 1748339 := bstep (se 1 (by rfl) ⟨1311254, by rfl⟩ : syracuseStep 1748339 = 2622509) B2622509
theorem B3321233 : Blo 774336 3321233 := bstep (se 2 (by rfl) ⟨1245462, by rfl⟩ : syracuseStep 3321233 = 2490925) B2490925
theorem B1748375 : Blo 774336 1748375 := bstep (se 1 (by rfl) ⟨1311281, by rfl⟩ : syracuseStep 1748375 = 2622563) B2622563
theorem B1748555 : Blo 774336 1748555 := bstep (se 1 (by rfl) ⟨1311416, by rfl⟩ : syracuseStep 1748555 = 2622833) B2622833
theorem B2207321 : Blo 774336 2207321 := bstep (se 2 (by rfl) ⟨827745, by rfl⟩ : syracuseStep 2207321 = 1655491) B1655491
theorem B1748609 : Blo 774336 1748609 := bstep (se 2 (by rfl) ⟨655728, by rfl⟩ : syracuseStep 1748609 = 1311457) B1311457
theorem B7548547 : Blo 774336 7548547 := bstep (se 1 (by rfl) ⟨5661410, by rfl⟩ : syracuseStep 7548547 = 11322821) B11322821
theorem B1421081 : Blo 774336 1421081 := bstep (se 2 (by rfl) ⟨532905, by rfl⟩ : syracuseStep 1421081 = 1065811) B1065811
theorem B1748825 : Blo 774336 1748825 := bstep (se 2 (by rfl) ⟨655809, by rfl⟩ : syracuseStep 1748825 = 1311619) B1311619
theorem B1748915 : Blo 774336 1748915 := bstep (se 1 (by rfl) ⟨1311686, by rfl⟩ : syracuseStep 1748915 = 2623373) B2623373
theorem B1748951 : Blo 774336 1748951 := bstep (se 1 (by rfl) ⟨1311713, by rfl⟩ : syracuseStep 1748951 = 2623427) B2623427
theorem B35926091 : Blo 774336 35926091 := bstep (se 1 (by rfl) ⟨26944568, by rfl⟩ : syracuseStep 35926091 = 53889137) B53889137
theorem B1749131 : Blo 774336 1749131 := bstep (se 1 (by rfl) ⟨1311848, by rfl⟩ : syracuseStep 1749131 = 2623697) B2623697
theorem B995479 : Blo 774336 995479 := bstep (se 1 (by rfl) ⟨746609, by rfl⟩ : syracuseStep 995479 = 1493219) B1493219
theorem B1749185 : Blo 774336 1749185 := bstep (se 2 (by rfl) ⟨655944, by rfl⟩ : syracuseStep 1749185 = 1311889) B1311889
theorem B1749401 : Blo 774336 1749401 := bstep (se 2 (by rfl) ⟨656025, by rfl⟩ : syracuseStep 1749401 = 1312051) B1312051
theorem B2240947 : Blo 774336 2240947 := bstep (se 1 (by rfl) ⟨1680710, by rfl⟩ : syracuseStep 2240947 = 3361421) B3361421
theorem B1749491 : Blo 774336 1749491 := bstep (se 1 (by rfl) ⟨1312118, by rfl⟩ : syracuseStep 1749491 = 2624237) B2624237
theorem B1749527 : Blo 774336 1749527 := bstep (se 1 (by rfl) ⟨1312145, by rfl⟩ : syracuseStep 1749527 = 2624291) B2624291
theorem B1749707 : Blo 774336 1749707 := bstep (se 1 (by rfl) ⟨1312280, by rfl⟩ : syracuseStep 1749707 = 2624561) B2624561
theorem B1749761 : Blo 774336 1749761 := bstep (se 2 (by rfl) ⟨656160, by rfl⟩ : syracuseStep 1749761 = 1312321) B1312321
theorem B5583821 : Blo 774336 5583821 := bstep (se 3 (by rfl) ⟨1046966, by rfl⟩ : syracuseStep 5583821 = 2093933) B2093933
theorem B1749977 : Blo 774336 1749977 := bstep (se 2 (by rfl) ⟨656241, by rfl⟩ : syracuseStep 1749977 = 1312483) B1312483
theorem B1750067 : Blo 774336 1750067 := bstep (se 1 (by rfl) ⟨1312550, by rfl⟩ : syracuseStep 1750067 = 2625101) B2625101
theorem B1750103 : Blo 774336 1750103 := bstep (se 1 (by rfl) ⟨1312577, by rfl⟩ : syracuseStep 1750103 = 2625155) B2625155
theorem B2208961 : Blo 774336 2208961 := bstep (se 2 (by rfl) ⟨828360, by rfl⟩ : syracuseStep 2208961 = 1656721) B1656721
theorem B1750283 : Blo 774336 1750283 := bstep (se 1 (by rfl) ⟨1312712, by rfl⟩ : syracuseStep 1750283 = 2625425) B2625425
theorem B4797713 : Blo 774336 4797713 := bstep (se 2 (by rfl) ⟨1799142, by rfl⟩ : syracuseStep 4797713 = 3598285) B3598285
theorem B1750337 : Blo 774336 1750337 := bstep (se 2 (by rfl) ⟨656376, by rfl⟩ : syracuseStep 1750337 = 1312753) B1312753
theorem B7091549 : Blo 774336 7091549 := bstep (se 3 (by rfl) ⟨1329665, by rfl⟩ : syracuseStep 7091549 = 2659331) B2659331
theorem B1750553 : Blo 774336 1750553 := bstep (se 2 (by rfl) ⟨656457, by rfl⟩ : syracuseStep 1750553 = 1312915) B1312915
theorem B6633035 : Blo 774336 6633035 := bstep (se 1 (by rfl) ⟨4974776, by rfl⟩ : syracuseStep 6633035 = 9949553) B9949553
theorem B1750643 : Blo 774336 1750643 := bstep (se 1 (by rfl) ⟨1312982, by rfl⟩ : syracuseStep 1750643 = 2625965) B2625965
theorem B2799235 : Blo 774336 2799235 := bstep (se 1 (by rfl) ⟨2099426, by rfl⟩ : syracuseStep 2799235 = 4198853) B4198853
theorem B14956163 : Blo 774336 14956163 := bstep (se 1 (by rfl) ⟨11217122, by rfl⟩ : syracuseStep 14956163 = 22434245) B22434245
theorem B1750679 : Blo 774336 1750679 := bstep (se 1 (by rfl) ⟨1313009, by rfl⟩ : syracuseStep 1750679 = 2626019) B2626019
theorem B3323693 : Blo 774336 3323693 := bstep (se 3 (by rfl) ⟨623192, by rfl⟩ : syracuseStep 3323693 = 1246385) B1246385
theorem B1750859 : Blo 774336 1750859 := bstep (se 1 (by rfl) ⟨1313144, by rfl⟩ : syracuseStep 1750859 = 2626289) B2626289
theorem B1750913 : Blo 774336 1750913 := bstep (se 2 (by rfl) ⟨656592, by rfl⟩ : syracuseStep 1750913 = 1313185) B1313185
theorem B1751129 : Blo 774336 1751129 := bstep (se 2 (by rfl) ⟨656673, by rfl⟩ : syracuseStep 1751129 = 1313347) B1313347
theorem B1751219 : Blo 774336 1751219 := bstep (se 1 (by rfl) ⟨1313414, by rfl⟩ : syracuseStep 1751219 = 2626829) B2626829
theorem B1751255 : Blo 774336 1751255 := bstep (se 1 (by rfl) ⟨1313441, by rfl⟩ : syracuseStep 1751255 = 2626883) B2626883
theorem B1161611 : Blo 774336 1161611 := bstep (se 1 (by rfl) ⟨871208, by rfl⟩ : syracuseStep 1161611 = 1742417) B1742417
theorem B1161623 : Blo 774336 1161623 := bstep (se 1 (by rfl) ⟨871217, by rfl⟩ : syracuseStep 1161623 = 1742435) B1742435
theorem B1161689 : Blo 774336 1161689 := bstep (se 2 (by rfl) ⟨435633, by rfl⟩ : syracuseStep 1161689 = 871267) B871267
theorem B3324377 : Blo 774336 3324377 := bstep (se 2 (by rfl) ⟨1246641, by rfl⟩ : syracuseStep 3324377 = 2493283) B2493283
theorem B1161803 : Blo 774336 1161803 := bstep (se 1 (by rfl) ⟨871352, by rfl⟩ : syracuseStep 1161803 = 1742705) B1742705
theorem B1161815 : Blo 774336 1161815 := bstep (se 1 (by rfl) ⟨871361, by rfl⟩ : syracuseStep 1161815 = 1742723) B1742723
theorem B1161881 : Blo 774336 1161881 := bstep (se 2 (by rfl) ⟨435705, by rfl⟩ : syracuseStep 1161881 = 871411) B871411
theorem B1161995 : Blo 774336 1161995 := bstep (se 1 (by rfl) ⟨871496, by rfl⟩ : syracuseStep 1161995 = 1742993) B1742993
theorem B1162007 : Blo 774336 1162007 := bstep (se 1 (by rfl) ⟨871505, by rfl⟩ : syracuseStep 1162007 = 1743011) B1743011
theorem B1162073 : Blo 774336 1162073 := bstep (se 2 (by rfl) ⟨435777, by rfl⟩ : syracuseStep 1162073 = 871555) B871555
theorem B1162187 : Blo 774336 1162187 := bstep (se 1 (by rfl) ⟨871640, by rfl⟩ : syracuseStep 1162187 = 1743281) B1743281
theorem B1162199 : Blo 774336 1162199 := bstep (se 1 (by rfl) ⟨871649, by rfl⟩ : syracuseStep 1162199 = 1743299) B1743299
theorem B1162265 : Blo 774336 1162265 := bstep (se 2 (by rfl) ⟨435849, by rfl⟩ : syracuseStep 1162265 = 871699) B871699
theorem B30293027 : Blo 774336 30293027 := bstep (se 1 (by rfl) ⟨22719770, by rfl⟩ : syracuseStep 30293027 = 45439541) B45439541
theorem B1162379 : Blo 774336 1162379 := bstep (se 1 (by rfl) ⟨871784, by rfl⟩ : syracuseStep 1162379 = 1743569) B1743569
theorem B1162391 : Blo 774336 1162391 := bstep (se 1 (by rfl) ⟨871793, by rfl⟩ : syracuseStep 1162391 = 1743587) B1743587
theorem B1162457 : Blo 774336 1162457 := bstep (se 2 (by rfl) ⟨435921, by rfl⟩ : syracuseStep 1162457 = 871843) B871843
theorem B1162571 : Blo 774336 1162571 := bstep (se 1 (by rfl) ⟨871928, by rfl⟩ : syracuseStep 1162571 = 1743857) B1743857
theorem B1162583 : Blo 774336 1162583 := bstep (se 1 (by rfl) ⟨871937, by rfl⟩ : syracuseStep 1162583 = 1743875) B1743875
theorem B1162649 : Blo 774336 1162649 := bstep (se 2 (by rfl) ⟨435993, by rfl⟩ : syracuseStep 1162649 = 871987) B871987
theorem B1162763 : Blo 774336 1162763 := bstep (se 1 (by rfl) ⟨872072, by rfl⟩ : syracuseStep 1162763 = 1744145) B1744145
theorem B1162775 : Blo 774336 1162775 := bstep (se 1 (by rfl) ⟨872081, by rfl⟩ : syracuseStep 1162775 = 1744163) B1744163
theorem B1162841 : Blo 774336 1162841 := bstep (se 2 (by rfl) ⟨436065, by rfl⟩ : syracuseStep 1162841 = 872131) B872131
theorem B1162955 : Blo 774336 1162955 := bstep (se 1 (by rfl) ⟨872216, by rfl⟩ : syracuseStep 1162955 = 1744433) B1744433
theorem B1162967 : Blo 774336 1162967 := bstep (se 1 (by rfl) ⟨872225, by rfl⟩ : syracuseStep 1162967 = 1744451) B1744451
theorem B1163033 : Blo 774336 1163033 := bstep (se 2 (by rfl) ⟨436137, by rfl⟩ : syracuseStep 1163033 = 872275) B872275
theorem B1163147 : Blo 774336 1163147 := bstep (se 1 (by rfl) ⟨872360, by rfl⟩ : syracuseStep 1163147 = 1744721) B1744721
theorem B1163159 : Blo 774336 1163159 := bstep (se 1 (by rfl) ⟨872369, by rfl⟩ : syracuseStep 1163159 = 1744739) B1744739
theorem B1163225 : Blo 774336 1163225 := bstep (se 2 (by rfl) ⟨436209, by rfl⟩ : syracuseStep 1163225 = 872419) B872419
theorem B1163339 : Blo 774336 1163339 := bstep (se 1 (by rfl) ⟨872504, by rfl⟩ : syracuseStep 1163339 = 1745009) B1745009
theorem B1163351 : Blo 774336 1163351 := bstep (se 1 (by rfl) ⟨872513, by rfl⟩ : syracuseStep 1163351 = 1745027) B1745027
theorem B1163417 : Blo 774336 1163417 := bstep (se 2 (by rfl) ⟨436281, by rfl⟩ : syracuseStep 1163417 = 872563) B872563
theorem B1163531 : Blo 774336 1163531 := bstep (se 1 (by rfl) ⟨872648, by rfl⟩ : syracuseStep 1163531 = 1745297) B1745297
theorem B1163543 : Blo 774336 1163543 := bstep (se 1 (by rfl) ⟨872657, by rfl⟩ : syracuseStep 1163543 = 1745315) B1745315
theorem B1327435 : Blo 774336 1327435 := bstep (se 1 (by rfl) ⟨995576, by rfl⟩ : syracuseStep 1327435 = 1991153) B1991153
theorem B1163609 : Blo 774336 1163609 := bstep (se 2 (by rfl) ⟨436353, by rfl⟩ : syracuseStep 1163609 = 872707) B872707
theorem B1163723 : Blo 774336 1163723 := bstep (se 1 (by rfl) ⟨872792, by rfl⟩ : syracuseStep 1163723 = 1745585) B1745585
theorem B1163735 : Blo 774336 1163735 := bstep (se 1 (by rfl) ⟨872801, by rfl⟩ : syracuseStep 1163735 = 1745603) B1745603
theorem B1163801 : Blo 774336 1163801 := bstep (se 2 (by rfl) ⟨436425, by rfl⟩ : syracuseStep 1163801 = 872851) B872851
theorem B1163915 : Blo 774336 1163915 := bstep (se 1 (by rfl) ⟨872936, by rfl⟩ : syracuseStep 1163915 = 1745873) B1745873
theorem B1163927 : Blo 774336 1163927 := bstep (se 1 (by rfl) ⟨872945, by rfl⟩ : syracuseStep 1163927 = 1745891) B1745891
theorem B1163993 : Blo 774336 1163993 := bstep (se 2 (by rfl) ⟨436497, by rfl⟩ : syracuseStep 1163993 = 872995) B872995
theorem B5587717 : Blo 774336 5587717 := bstep (se 4 (by rfl) ⟨523848, by rfl⟩ : syracuseStep 5587717 = 1047697) B1047697
theorem B1164107 : Blo 774336 1164107 := bstep (se 1 (by rfl) ⟨873080, by rfl⟩ : syracuseStep 1164107 = 1746161) B1746161
theorem B1164119 : Blo 774336 1164119 := bstep (se 1 (by rfl) ⟨873089, by rfl⟩ : syracuseStep 1164119 = 1746179) B1746179
theorem B2212697 : Blo 774336 2212697 := bstep (se 2 (by rfl) ⟨829761, by rfl⟩ : syracuseStep 2212697 = 1659523) B1659523
theorem B1164185 : Blo 774336 1164185 := bstep (se 2 (by rfl) ⟨436569, by rfl⟩ : syracuseStep 1164185 = 873139) B873139
theorem B1164299 : Blo 774336 1164299 := bstep (se 1 (by rfl) ⟨873224, by rfl⟩ : syracuseStep 1164299 = 1746449) B1746449
theorem B1164311 : Blo 774336 1164311 := bstep (se 1 (by rfl) ⟨873233, by rfl⟩ : syracuseStep 1164311 = 1746467) B1746467
theorem B1164377 : Blo 774336 1164377 := bstep (se 2 (by rfl) ⟨436641, by rfl⟩ : syracuseStep 1164377 = 873283) B873283
theorem B5031013 : Blo 774336 5031013 := bstep (se 4 (by rfl) ⟨471657, by rfl⟩ : syracuseStep 5031013 = 943315) B943315
theorem B1164491 : Blo 774336 1164491 := bstep (se 1 (by rfl) ⟨873368, by rfl⟩ : syracuseStep 1164491 = 1746737) B1746737
theorem B1164503 : Blo 774336 1164503 := bstep (se 1 (by rfl) ⟨873377, by rfl⟩ : syracuseStep 1164503 = 1746755) B1746755
theorem B1164569 : Blo 774336 1164569 := bstep (se 2 (by rfl) ⟨436713, by rfl⟩ : syracuseStep 1164569 = 873427) B873427
theorem B1164683 : Blo 774336 1164683 := bstep (se 1 (by rfl) ⟨873512, by rfl⟩ : syracuseStep 1164683 = 1747025) B1747025
theorem B1164695 : Blo 774336 1164695 := bstep (se 1 (by rfl) ⟨873521, by rfl⟩ : syracuseStep 1164695 = 1747043) B1747043
theorem B1361305 : Blo 774336 1361305 := bstep (se 2 (by rfl) ⟨510489, by rfl⟩ : syracuseStep 1361305 = 1020979) B1020979
theorem B1164761 : Blo 774336 1164761 := bstep (se 2 (by rfl) ⟨436785, by rfl⟩ : syracuseStep 1164761 = 873571) B873571
theorem B1164875 : Blo 774336 1164875 := bstep (se 1 (by rfl) ⟨873656, by rfl⟩ : syracuseStep 1164875 = 1747313) B1747313
theorem B1263179 : Blo 774336 1263179 := bstep (se 1 (by rfl) ⟨947384, by rfl⟩ : syracuseStep 1263179 = 1894769) B1894769
theorem B1164887 : Blo 774336 1164887 := bstep (se 1 (by rfl) ⟨873665, by rfl⟩ : syracuseStep 1164887 = 1747331) B1747331
theorem B1164953 : Blo 774336 1164953 := bstep (se 2 (by rfl) ⟨436857, by rfl⟩ : syracuseStep 1164953 = 873715) B873715
theorem B1492673 : Blo 774336 1492673 := bstep (se 2 (by rfl) ⟨559752, by rfl⟩ : syracuseStep 1492673 = 1119505) B1119505
theorem B1165067 : Blo 774336 1165067 := bstep (se 1 (by rfl) ⟨873800, by rfl⟩ : syracuseStep 1165067 = 1747601) B1747601
theorem B1165079 : Blo 774336 1165079 := bstep (se 1 (by rfl) ⟨873809, by rfl⟩ : syracuseStep 1165079 = 1747619) B1747619
theorem B1165145 : Blo 774336 1165145 := bstep (se 2 (by rfl) ⟨436929, by rfl⟩ : syracuseStep 1165145 = 873859) B873859
theorem B1165259 : Blo 774336 1165259 := bstep (se 1 (by rfl) ⟨873944, by rfl⟩ : syracuseStep 1165259 = 1747889) B1747889
theorem B1165271 : Blo 774336 1165271 := bstep (se 1 (by rfl) ⟨873953, by rfl⟩ : syracuseStep 1165271 = 1747907) B1747907
theorem B1165337 : Blo 774336 1165337 := bstep (se 2 (by rfl) ⟨437001, by rfl⟩ : syracuseStep 1165337 = 874003) B874003
theorem B2213963 : Blo 774336 2213963 := bstep (se 1 (by rfl) ⟨1660472, by rfl⟩ : syracuseStep 2213963 = 3320945) B3320945
theorem B1165451 : Blo 774336 1165451 := bstep (se 1 (by rfl) ⟨874088, by rfl⟩ : syracuseStep 1165451 = 1748177) B1748177
theorem B1165463 : Blo 774336 1165463 := bstep (se 1 (by rfl) ⟨874097, by rfl⟩ : syracuseStep 1165463 = 1748195) B1748195
theorem B3360941 : Blo 774336 3360941 := bstep (se 3 (by rfl) ⟨630176, by rfl⟩ : syracuseStep 3360941 = 1260353) B1260353
theorem B9423053 : Blo 774336 9423053 := bstep (se 3 (by rfl) ⟨1766822, by rfl⟩ : syracuseStep 9423053 = 3533645) B3533645
theorem B1165529 : Blo 774336 1165529 := bstep (se 2 (by rfl) ⟨437073, by rfl⟩ : syracuseStep 1165529 = 874147) B874147
theorem B1165643 : Blo 774336 1165643 := bstep (se 1 (by rfl) ⟨874232, by rfl⟩ : syracuseStep 1165643 = 1748465) B1748465
theorem B1165655 : Blo 774336 1165655 := bstep (se 1 (by rfl) ⟨874241, by rfl⟩ : syracuseStep 1165655 = 1748483) B1748483
theorem B12568931 : Blo 774336 12568931 := bstep (se 1 (by rfl) ⟨9426698, by rfl⟩ : syracuseStep 12568931 = 18853397) B18853397
theorem B1165721 : Blo 774336 1165721 := bstep (se 2 (by rfl) ⟨437145, by rfl⟩ : syracuseStep 1165721 = 874291) B874291
theorem B1329625 : Blo 774336 1329625 := bstep (se 2 (by rfl) ⟨498609, by rfl⟩ : syracuseStep 1329625 = 997219) B997219
theorem B1165835 : Blo 774336 1165835 := bstep (se 1 (by rfl) ⟨874376, by rfl⟩ : syracuseStep 1165835 = 1748753) B1748753
theorem B1165847 : Blo 774336 1165847 := bstep (se 1 (by rfl) ⟨874385, by rfl⟩ : syracuseStep 1165847 = 1748771) B1748771
theorem B1165913 : Blo 774336 1165913 := bstep (se 2 (by rfl) ⟨437217, by rfl⟩ : syracuseStep 1165913 = 874435) B874435
theorem B1493657 : Blo 774336 1493657 := bstep (se 2 (by rfl) ⟨560121, by rfl⟩ : syracuseStep 1493657 = 1120243) B1120243
theorem B1166027 : Blo 774336 1166027 := bstep (se 1 (by rfl) ⟨874520, by rfl⟩ : syracuseStep 1166027 = 1749041) B1749041
theorem B1657559 : Blo 774336 1657559 := bstep (se 1 (by rfl) ⟨1243169, by rfl⟩ : syracuseStep 1657559 = 2486339) B2486339
theorem B1166039 : Blo 774336 1166039 := bstep (se 1 (by rfl) ⟨874529, by rfl⟩ : syracuseStep 1166039 = 1749059) B1749059
theorem B871159 : Blo 774336 871159 := bstep (se 1 (by rfl) ⟨653369, by rfl⟩ : syracuseStep 871159 = 1306739) B1306739
theorem B2804483 : Blo 774336 2804483 := bstep (se 1 (by rfl) ⟨2103362, by rfl⟩ : syracuseStep 2804483 = 4206725) B4206725
theorem B1166105 : Blo 774336 1166105 := bstep (se 2 (by rfl) ⟨437289, by rfl⟩ : syracuseStep 1166105 = 874579) B874579
theorem B1657739 : Blo 774336 1657739 := bstep (se 1 (by rfl) ⟨1243304, by rfl⟩ : syracuseStep 1657739 = 2486609) B2486609
theorem B1166219 : Blo 774336 1166219 := bstep (se 1 (by rfl) ⟨874664, by rfl⟩ : syracuseStep 1166219 = 1749329) B1749329
theorem B1166231 : Blo 774336 1166231 := bstep (se 1 (by rfl) ⟨874673, by rfl⟩ : syracuseStep 1166231 = 1749347) B1749347
theorem B871339 : Blo 774336 871339 := bstep (se 1 (by rfl) ⟨653504, by rfl⟩ : syracuseStep 871339 = 1307009) B1307009
theorem B1166297 : Blo 774336 1166297 := bstep (se 2 (by rfl) ⟨437361, by rfl⟩ : syracuseStep 1166297 = 874723) B874723
theorem B871447 : Blo 774336 871447 := bstep (se 1 (by rfl) ⟨653585, by rfl⟩ : syracuseStep 871447 = 1307171) B1307171
theorem B5884973 : Blo 774336 5884973 := bstep (se 3 (by rfl) ⟨1103432, by rfl⟩ : syracuseStep 5884973 = 2206865) B2206865
theorem B1166411 : Blo 774336 1166411 := bstep (se 1 (by rfl) ⟨874808, by rfl⟩ : syracuseStep 1166411 = 1749617) B1749617
theorem B1166423 : Blo 774336 1166423 := bstep (se 1 (by rfl) ⟨874817, by rfl⟩ : syracuseStep 1166423 = 1749635) B1749635
theorem B5590109 : Blo 774336 5590109 := bstep (se 3 (by rfl) ⟨1048145, by rfl⟩ : syracuseStep 5590109 = 2096291) B2096291
theorem B1592473 : Blo 774336 1592473 := bstep (se 2 (by rfl) ⟨597177, by rfl⟩ : syracuseStep 1592473 = 1194355) B1194355
theorem B1166489 : Blo 774336 1166489 := bstep (se 2 (by rfl) ⟨437433, by rfl⟩ : syracuseStep 1166489 = 874867) B874867
theorem B871627 : Blo 774336 871627 := bstep (se 1 (by rfl) ⟨653720, by rfl⟩ : syracuseStep 871627 = 1307441) B1307441
theorem B1166603 : Blo 774336 1166603 := bstep (se 1 (by rfl) ⟨874952, by rfl⟩ : syracuseStep 1166603 = 1749905) B1749905
theorem B1166615 : Blo 774336 1166615 := bstep (se 1 (by rfl) ⟨874961, by rfl⟩ : syracuseStep 1166615 = 1749923) B1749923
theorem B7097645 : Blo 774336 7097645 := bstep (se 3 (by rfl) ⟨1330808, by rfl⟩ : syracuseStep 7097645 = 2661617) B2661617
theorem B871735 : Blo 774336 871735 := bstep (se 1 (by rfl) ⟨653801, by rfl⟩ : syracuseStep 871735 = 1307603) B1307603
theorem B1396043 : Blo 774336 1396043 := bstep (se 1 (by rfl) ⟨1047032, by rfl⟩ : syracuseStep 1396043 = 2094065) B2094065
theorem B1166681 : Blo 774336 1166681 := bstep (se 2 (by rfl) ⟨437505, by rfl⟩ : syracuseStep 1166681 = 875011) B875011
theorem B1166795 : Blo 774336 1166795 := bstep (se 1 (by rfl) ⟨875096, by rfl⟩ : syracuseStep 1166795 = 1750193) B1750193
theorem B1166807 : Blo 774336 1166807 := bstep (se 1 (by rfl) ⟨875105, by rfl⟩ : syracuseStep 1166807 = 1750211) B1750211
theorem B871915 : Blo 774336 871915 := bstep (se 1 (by rfl) ⟨653936, by rfl⟩ : syracuseStep 871915 = 1307873) B1307873
theorem B1166873 : Blo 774336 1166873 := bstep (se 2 (by rfl) ⟨437577, by rfl⟩ : syracuseStep 1166873 = 875155) B875155
theorem B872023 : Blo 774336 872023 := bstep (se 1 (by rfl) ⟨654017, by rfl⟩ : syracuseStep 872023 = 1308035) B1308035
theorem B1166987 : Blo 774336 1166987 := bstep (se 1 (by rfl) ⟨875240, by rfl⟩ : syracuseStep 1166987 = 1750481) B1750481
theorem B1166999 : Blo 774336 1166999 := bstep (se 1 (by rfl) ⟨875249, by rfl⟩ : syracuseStep 1166999 = 1750499) B1750499
theorem B1167065 : Blo 774336 1167065 := bstep (se 2 (by rfl) ⟨437649, by rfl⟩ : syracuseStep 1167065 = 875299) B875299
theorem B872203 : Blo 774336 872203 := bstep (se 1 (by rfl) ⟨654152, by rfl⟩ : syracuseStep 872203 = 1308305) B1308305
theorem B1167179 : Blo 774336 1167179 := bstep (se 1 (by rfl) ⟨875384, by rfl⟩ : syracuseStep 1167179 = 1750769) B1750769
theorem B1167191 : Blo 774336 1167191 := bstep (se 1 (by rfl) ⟨875393, by rfl⟩ : syracuseStep 1167191 = 1750787) B1750787
theorem B2838365 : Blo 774336 2838365 := bstep (se 3 (by rfl) ⟨532193, by rfl⟩ : syracuseStep 2838365 = 1064387) B1064387
theorem B872311 : Blo 774336 872311 := bstep (se 1 (by rfl) ⟨654233, by rfl⟩ : syracuseStep 872311 = 1308467) B1308467
theorem B1167257 : Blo 774336 1167257 := bstep (se 2 (by rfl) ⟨437721, by rfl⟩ : syracuseStep 1167257 = 875443) B875443
theorem B1167371 : Blo 774336 1167371 := bstep (se 1 (by rfl) ⟨875528, by rfl⟩ : syracuseStep 1167371 = 1751057) B1751057
theorem B1167383 : Blo 774336 1167383 := bstep (se 1 (by rfl) ⟨875537, by rfl⟩ : syracuseStep 1167383 = 1751075) B1751075
theorem B13455395 : Blo 774336 13455395 := bstep (se 1 (by rfl) ⟨10091546, by rfl⟩ : syracuseStep 13455395 = 20183093) B20183093
theorem B872491 : Blo 774336 872491 := bstep (se 1 (by rfl) ⟨654368, by rfl⟩ : syracuseStep 872491 = 1308737) B1308737
theorem B1495091 : Blo 774336 1495091 := bstep (se 1 (by rfl) ⟨1121318, by rfl⟩ : syracuseStep 1495091 = 2242637) B2242637
theorem B1167449 : Blo 774336 1167449 := bstep (se 2 (by rfl) ⟨437793, by rfl⟩ : syracuseStep 1167449 = 875587) B875587
theorem B4411543 : Blo 774336 4411543 := bstep (se 1 (by rfl) ⟨3308657, by rfl⟩ : syracuseStep 4411543 = 6617315) B6617315
theorem B872599 : Blo 774336 872599 := bstep (se 1 (by rfl) ⟨654449, by rfl⟩ : syracuseStep 872599 = 1308899) B1308899
theorem B774347 : Blo 774336 774347 := bstep (se 1 (by rfl) ⟨580760, by rfl⟩ : syracuseStep 774347 = 1161521) B1161521
theorem B774359 : Blo 774336 774359 := bstep (se 1 (by rfl) ⟨580769, by rfl⟩ : syracuseStep 774359 = 1161539) B1161539
theorem B774379 : Blo 774336 774379 := bstep (se 1 (by rfl) ⟨580784, by rfl⟩ : syracuseStep 774379 = 1161569) B1161569
theorem B774391 : Blo 774336 774391 := bstep (se 1 (by rfl) ⟨580793, by rfl⟩ : syracuseStep 774391 = 1161587) B1161587
theorem B774411 : Blo 774336 774411 := bstep (se 1 (by rfl) ⟨580808, by rfl⟩ : syracuseStep 774411 = 1161617) B1161617
theorem B774423 : Blo 774336 774423 := bstep (se 1 (by rfl) ⟨580817, by rfl⟩ : syracuseStep 774423 = 1161635) B1161635
theorem B774443 : Blo 774336 774443 := bstep (se 1 (by rfl) ⟨580832, by rfl⟩ : syracuseStep 774443 = 1161665) B1161665
theorem B774455 : Blo 774336 774455 := bstep (se 1 (by rfl) ⟨580841, by rfl⟩ : syracuseStep 774455 = 1161683) B1161683
theorem B774475 : Blo 774336 774475 := bstep (se 1 (by rfl) ⟨580856, by rfl⟩ : syracuseStep 774475 = 1161713) B1161713
theorem B872779 : Blo 774336 872779 := bstep (se 1 (by rfl) ⟨654584, by rfl⟩ : syracuseStep 872779 = 1309169) B1309169
theorem B774487 : Blo 774336 774487 := bstep (se 1 (by rfl) ⟨580865, by rfl⟩ : syracuseStep 774487 = 1161731) B1161731
theorem B1986905 : Blo 774336 1986905 := bstep (se 2 (by rfl) ⟨745089, by rfl⟩ : syracuseStep 1986905 = 1490179) B1490179
theorem B1397081 : Blo 774336 1397081 := bstep (se 2 (by rfl) ⟨523905, by rfl⟩ : syracuseStep 1397081 = 1047811) B1047811
theorem B774507 : Blo 774336 774507 := bstep (se 1 (by rfl) ⟨580880, by rfl⟩ : syracuseStep 774507 = 1161761) B1161761
theorem B774519 : Blo 774336 774519 := bstep (se 1 (by rfl) ⟨580889, by rfl⟩ : syracuseStep 774519 = 1161779) B1161779
theorem B774539 : Blo 774336 774539 := bstep (se 1 (by rfl) ⟨580904, by rfl⟩ : syracuseStep 774539 = 1161809) B1161809
theorem B774551 : Blo 774336 774551 := bstep (se 1 (by rfl) ⟨580913, by rfl⟩ : syracuseStep 774551 = 1161827) B1161827
theorem B774571 : Blo 774336 774571 := bstep (se 1 (by rfl) ⟨580928, by rfl⟩ : syracuseStep 774571 = 1161857) B1161857
theorem B774583 : Blo 774336 774583 := bstep (se 1 (by rfl) ⟨580937, by rfl⟩ : syracuseStep 774583 = 1161875) B1161875
theorem B872887 : Blo 774336 872887 := bstep (se 1 (by rfl) ⟨654665, by rfl⟩ : syracuseStep 872887 = 1309331) B1309331
theorem B774603 : Blo 774336 774603 := bstep (se 1 (by rfl) ⟨580952, by rfl⟩ : syracuseStep 774603 = 1161905) B1161905
theorem B774615 : Blo 774336 774615 := bstep (se 1 (by rfl) ⟨580961, by rfl⟩ : syracuseStep 774615 = 1161923) B1161923
theorem B774635 : Blo 774336 774635 := bstep (se 1 (by rfl) ⟨580976, by rfl⟩ : syracuseStep 774635 = 1161953) B1161953
theorem B1659379 : Blo 774336 1659379 := bstep (se 1 (by rfl) ⟨1244534, by rfl⟩ : syracuseStep 1659379 = 2489069) B2489069
theorem B774647 : Blo 774336 774647 := bstep (se 1 (by rfl) ⟨580985, by rfl⟩ : syracuseStep 774647 = 1161971) B1161971
theorem B774667 : Blo 774336 774667 := bstep (se 1 (by rfl) ⟨581000, by rfl⟩ : syracuseStep 774667 = 1162001) B1162001
theorem B6279697 : Blo 774336 6279697 := bstep (se 2 (by rfl) ⟨2354886, by rfl⟩ : syracuseStep 6279697 = 4709773) B4709773
theorem B774679 : Blo 774336 774679 := bstep (se 1 (by rfl) ⟨581009, by rfl⟩ : syracuseStep 774679 = 1162019) B1162019
theorem B774699 : Blo 774336 774699 := bstep (se 1 (by rfl) ⟨581024, by rfl⟩ : syracuseStep 774699 = 1162049) B1162049
theorem B774711 : Blo 774336 774711 := bstep (se 1 (by rfl) ⟨581033, by rfl⟩ : syracuseStep 774711 = 1162067) B1162067
theorem B774731 : Blo 774336 774731 := bstep (se 1 (by rfl) ⟨581048, by rfl⟩ : syracuseStep 774731 = 1162097) B1162097
theorem B774743 : Blo 774336 774743 := bstep (se 1 (by rfl) ⟨581057, by rfl⟩ : syracuseStep 774743 = 1162115) B1162115
theorem B774763 : Blo 774336 774763 := bstep (se 1 (by rfl) ⟨581072, by rfl⟩ : syracuseStep 774763 = 1162145) B1162145
theorem B873067 : Blo 774336 873067 := bstep (se 1 (by rfl) ⟨654800, by rfl⟩ : syracuseStep 873067 = 1309601) B1309601
theorem B774775 : Blo 774336 774775 := bstep (se 1 (by rfl) ⟨581081, by rfl⟩ : syracuseStep 774775 = 1162163) B1162163
theorem B774795 : Blo 774336 774795 := bstep (se 1 (by rfl) ⟨581096, by rfl⟩ : syracuseStep 774795 = 1162193) B1162193
theorem B774807 : Blo 774336 774807 := bstep (se 1 (by rfl) ⟨581105, by rfl⟩ : syracuseStep 774807 = 1162211) B1162211
theorem B774827 : Blo 774336 774827 := bstep (se 1 (by rfl) ⟨581120, by rfl⟩ : syracuseStep 774827 = 1162241) B1162241
theorem B774839 : Blo 774336 774839 := bstep (se 1 (by rfl) ⟨581129, by rfl⟩ : syracuseStep 774839 = 1162259) B1162259
theorem B774859 : Blo 774336 774859 := bstep (se 1 (by rfl) ⟨581144, by rfl⟩ : syracuseStep 774859 = 1162289) B1162289
theorem B774871 : Blo 774336 774871 := bstep (se 1 (by rfl) ⟨581153, by rfl⟩ : syracuseStep 774871 = 1162307) B1162307
theorem B873175 : Blo 774336 873175 := bstep (se 1 (by rfl) ⟨654881, by rfl⟩ : syracuseStep 873175 = 1309763) B1309763
theorem B774891 : Blo 774336 774891 := bstep (se 1 (by rfl) ⟨581168, by rfl⟩ : syracuseStep 774891 = 1162337) B1162337
theorem B774903 : Blo 774336 774903 := bstep (se 1 (by rfl) ⟨581177, by rfl⟩ : syracuseStep 774903 = 1162355) B1162355
theorem B774923 : Blo 774336 774923 := bstep (se 1 (by rfl) ⟨581192, by rfl⟩ : syracuseStep 774923 = 1162385) B1162385
theorem B774935 : Blo 774336 774935 := bstep (se 1 (by rfl) ⟨581201, by rfl⟩ : syracuseStep 774935 = 1162403) B1162403
theorem B774955 : Blo 774336 774955 := bstep (se 1 (by rfl) ⟨581216, by rfl⟩ : syracuseStep 774955 = 1162433) B1162433
theorem B774967 : Blo 774336 774967 := bstep (se 1 (by rfl) ⟨581225, by rfl⟩ : syracuseStep 774967 = 1162451) B1162451
theorem B774987 : Blo 774336 774987 := bstep (se 1 (by rfl) ⟨581240, by rfl⟩ : syracuseStep 774987 = 1162481) B1162481
theorem B774999 : Blo 774336 774999 := bstep (se 1 (by rfl) ⟨581249, by rfl⟩ : syracuseStep 774999 = 1162499) B1162499
theorem B1102681 : Blo 774336 1102681 := bstep (se 2 (by rfl) ⟨413505, by rfl⟩ : syracuseStep 1102681 = 827011) B827011
theorem B775019 : Blo 774336 775019 := bstep (se 1 (by rfl) ⟨581264, by rfl⟩ : syracuseStep 775019 = 1162529) B1162529
theorem B775031 : Blo 774336 775031 := bstep (se 1 (by rfl) ⟨581273, by rfl⟩ : syracuseStep 775031 = 1162547) B1162547
theorem B775051 : Blo 774336 775051 := bstep (se 1 (by rfl) ⟨581288, by rfl⟩ : syracuseStep 775051 = 1162577) B1162577
theorem B873355 : Blo 774336 873355 := bstep (se 1 (by rfl) ⟨655016, by rfl⟩ : syracuseStep 873355 = 1310033) B1310033
theorem B775063 : Blo 774336 775063 := bstep (se 1 (by rfl) ⟨581297, by rfl⟩ : syracuseStep 775063 = 1162595) B1162595
theorem B775083 : Blo 774336 775083 := bstep (se 1 (by rfl) ⟨581312, by rfl⟩ : syracuseStep 775083 = 1162625) B1162625
theorem B775095 : Blo 774336 775095 := bstep (se 1 (by rfl) ⟨581321, by rfl⟩ : syracuseStep 775095 = 1162643) B1162643
theorem B775115 : Blo 774336 775115 := bstep (se 1 (by rfl) ⟨581336, by rfl⟩ : syracuseStep 775115 = 1162673) B1162673
theorem B775127 : Blo 774336 775127 := bstep (se 1 (by rfl) ⟨581345, by rfl⟩ : syracuseStep 775127 = 1162691) B1162691
theorem B1659865 : Blo 774336 1659865 := bstep (se 2 (by rfl) ⟨622449, by rfl⟩ : syracuseStep 1659865 = 1244899) B1244899
theorem B775147 : Blo 774336 775147 := bstep (se 1 (by rfl) ⟨581360, by rfl⟩ : syracuseStep 775147 = 1162721) B1162721
theorem B775159 : Blo 774336 775159 := bstep (se 1 (by rfl) ⟨581369, by rfl⟩ : syracuseStep 775159 = 1162739) B1162739
theorem B873463 : Blo 774336 873463 := bstep (se 1 (by rfl) ⟨655097, by rfl⟩ : syracuseStep 873463 = 1310195) B1310195
theorem B775179 : Blo 774336 775179 := bstep (se 1 (by rfl) ⟨581384, by rfl⟩ : syracuseStep 775179 = 1162769) B1162769
theorem B775191 : Blo 774336 775191 := bstep (se 1 (by rfl) ⟨581393, by rfl⟩ : syracuseStep 775191 = 1162787) B1162787
theorem B1365017 : Blo 774336 1365017 := bstep (se 2 (by rfl) ⟨511881, by rfl⟩ : syracuseStep 1365017 = 1023763) B1023763
theorem B775211 : Blo 774336 775211 := bstep (se 1 (by rfl) ⟨581408, by rfl⟩ : syracuseStep 775211 = 1162817) B1162817
theorem B775223 : Blo 774336 775223 := bstep (se 1 (by rfl) ⟨581417, by rfl⟩ : syracuseStep 775223 = 1162835) B1162835
theorem B775243 : Blo 774336 775243 := bstep (se 1 (by rfl) ⟨581432, by rfl⟩ : syracuseStep 775243 = 1162865) B1162865
theorem B775255 : Blo 774336 775255 := bstep (se 1 (by rfl) ⟨581441, by rfl⟩ : syracuseStep 775255 = 1162883) B1162883
theorem B775275 : Blo 774336 775275 := bstep (se 1 (by rfl) ⟨581456, by rfl⟩ : syracuseStep 775275 = 1162913) B1162913
theorem B775287 : Blo 774336 775287 := bstep (se 1 (by rfl) ⟨581465, by rfl⟩ : syracuseStep 775287 = 1162931) B1162931
theorem B775307 : Blo 774336 775307 := bstep (se 1 (by rfl) ⟨581480, by rfl⟩ : syracuseStep 775307 = 1162961) B1162961
theorem B3921047 : Blo 774336 3921047 := bstep (se 1 (by rfl) ⟨2940785, by rfl⟩ : syracuseStep 3921047 = 5881571) B5881571
theorem B775319 : Blo 774336 775319 := bstep (se 1 (by rfl) ⟨581489, by rfl⟩ : syracuseStep 775319 = 1162979) B1162979
theorem B775339 : Blo 774336 775339 := bstep (se 1 (by rfl) ⟨581504, by rfl⟩ : syracuseStep 775339 = 1163009) B1163009
theorem B873643 : Blo 774336 873643 := bstep (se 1 (by rfl) ⟨655232, by rfl⟩ : syracuseStep 873643 = 1310465) B1310465
theorem B775351 : Blo 774336 775351 := bstep (se 1 (by rfl) ⟨581513, by rfl⟩ : syracuseStep 775351 = 1163027) B1163027
theorem B775371 : Blo 774336 775371 := bstep (se 1 (by rfl) ⟨581528, by rfl⟩ : syracuseStep 775371 = 1163057) B1163057
theorem B775383 : Blo 774336 775383 := bstep (se 1 (by rfl) ⟨581537, by rfl⟩ : syracuseStep 775383 = 1163075) B1163075
theorem B775403 : Blo 774336 775403 := bstep (se 1 (by rfl) ⟨581552, by rfl⟩ : syracuseStep 775403 = 1163105) B1163105
theorem B775415 : Blo 774336 775415 := bstep (se 1 (by rfl) ⟨581561, by rfl⟩ : syracuseStep 775415 = 1163123) B1163123
theorem B1496321 : Blo 774336 1496321 := bstep (se 2 (by rfl) ⟨561120, by rfl⟩ : syracuseStep 1496321 = 1122241) B1122241
theorem B775435 : Blo 774336 775435 := bstep (se 1 (by rfl) ⟨581576, by rfl⟩ : syracuseStep 775435 = 1163153) B1163153
theorem B775447 : Blo 774336 775447 := bstep (se 1 (by rfl) ⟨581585, by rfl⟩ : syracuseStep 775447 = 1163171) B1163171
theorem B873751 : Blo 774336 873751 := bstep (se 1 (by rfl) ⟨655313, by rfl⟩ : syracuseStep 873751 = 1310627) B1310627
theorem B775467 : Blo 774336 775467 := bstep (se 1 (by rfl) ⟨581600, by rfl⟩ : syracuseStep 775467 = 1163201) B1163201
theorem B775479 : Blo 774336 775479 := bstep (se 1 (by rfl) ⟨581609, by rfl⟩ : syracuseStep 775479 = 1163219) B1163219
theorem B775499 : Blo 774336 775499 := bstep (se 1 (by rfl) ⟨581624, by rfl⟩ : syracuseStep 775499 = 1163249) B1163249
theorem B775511 : Blo 774336 775511 := bstep (se 1 (by rfl) ⟨581633, by rfl⟩ : syracuseStep 775511 = 1163267) B1163267
theorem B775531 : Blo 774336 775531 := bstep (se 1 (by rfl) ⟨581648, by rfl⟩ : syracuseStep 775531 = 1163297) B1163297
theorem B775543 : Blo 774336 775543 := bstep (se 1 (by rfl) ⟨581657, by rfl⟩ : syracuseStep 775543 = 1163315) B1163315
theorem B775563 : Blo 774336 775563 := bstep (se 1 (by rfl) ⟨581672, by rfl⟩ : syracuseStep 775563 = 1163345) B1163345
theorem B775575 : Blo 774336 775575 := bstep (se 1 (by rfl) ⟨581681, by rfl⟩ : syracuseStep 775575 = 1163363) B1163363
theorem B775595 : Blo 774336 775595 := bstep (se 1 (by rfl) ⟨581696, by rfl⟩ : syracuseStep 775595 = 1163393) B1163393
theorem B775607 : Blo 774336 775607 := bstep (se 1 (by rfl) ⟨581705, by rfl⟩ : syracuseStep 775607 = 1163411) B1163411
theorem B775627 : Blo 774336 775627 := bstep (se 1 (by rfl) ⟨581720, by rfl⟩ : syracuseStep 775627 = 1163441) B1163441
theorem B873931 : Blo 774336 873931 := bstep (se 1 (by rfl) ⟨655448, by rfl⟩ : syracuseStep 873931 = 1310897) B1310897
theorem B775639 : Blo 774336 775639 := bstep (se 1 (by rfl) ⟨581729, by rfl⟩ : syracuseStep 775639 = 1163459) B1163459
theorem B775659 : Blo 774336 775659 := bstep (se 1 (by rfl) ⟨581744, by rfl⟩ : syracuseStep 775659 = 1163489) B1163489
theorem B775671 : Blo 774336 775671 := bstep (se 1 (by rfl) ⟨581753, by rfl⟩ : syracuseStep 775671 = 1163507) B1163507
theorem B775691 : Blo 774336 775691 := bstep (se 1 (by rfl) ⟨581768, by rfl⟩ : syracuseStep 775691 = 1163537) B1163537
theorem B775703 : Blo 774336 775703 := bstep (se 1 (by rfl) ⟨581777, by rfl⟩ : syracuseStep 775703 = 1163555) B1163555
theorem B775723 : Blo 774336 775723 := bstep (se 1 (by rfl) ⟨581792, by rfl⟩ : syracuseStep 775723 = 1163585) B1163585
theorem B775735 : Blo 774336 775735 := bstep (se 1 (by rfl) ⟨581801, by rfl⟩ : syracuseStep 775735 = 1163603) B1163603
theorem B874039 : Blo 774336 874039 := bstep (se 1 (by rfl) ⟨655529, by rfl⟩ : syracuseStep 874039 = 1311059) B1311059
theorem B775755 : Blo 774336 775755 := bstep (se 1 (by rfl) ⟨581816, by rfl⟩ : syracuseStep 775755 = 1163633) B1163633
theorem B775767 : Blo 774336 775767 := bstep (se 1 (by rfl) ⟨581825, by rfl⟩ : syracuseStep 775767 = 1163651) B1163651
theorem B775787 : Blo 774336 775787 := bstep (se 1 (by rfl) ⟨581840, by rfl⟩ : syracuseStep 775787 = 1163681) B1163681
theorem B775799 : Blo 774336 775799 := bstep (se 1 (by rfl) ⟨581849, by rfl⟩ : syracuseStep 775799 = 1163699) B1163699
theorem B775819 : Blo 774336 775819 := bstep (se 1 (by rfl) ⟨581864, by rfl⟩ : syracuseStep 775819 = 1163729) B1163729
theorem B775831 : Blo 774336 775831 := bstep (se 1 (by rfl) ⟨581873, by rfl⟩ : syracuseStep 775831 = 1163747) B1163747
theorem B775851 : Blo 774336 775851 := bstep (se 1 (by rfl) ⟨581888, by rfl⟩ : syracuseStep 775851 = 1163777) B1163777
theorem B775863 : Blo 774336 775863 := bstep (se 1 (by rfl) ⟨581897, by rfl⟩ : syracuseStep 775863 = 1163795) B1163795
theorem B775883 : Blo 774336 775883 := bstep (se 1 (by rfl) ⟨581912, by rfl⟩ : syracuseStep 775883 = 1163825) B1163825
theorem B21288653 : Blo 774336 21288653 := bstep (se 3 (by rfl) ⟨3991622, by rfl⟩ : syracuseStep 21288653 = 7983245) B7983245
theorem B775895 : Blo 774336 775895 := bstep (se 1 (by rfl) ⟨581921, by rfl⟩ : syracuseStep 775895 = 1163843) B1163843
theorem B775915 : Blo 774336 775915 := bstep (se 1 (by rfl) ⟨581936, by rfl⟩ : syracuseStep 775915 = 1163873) B1163873
theorem B874219 : Blo 774336 874219 := bstep (se 1 (by rfl) ⟨655664, by rfl⟩ : syracuseStep 874219 = 1311329) B1311329
theorem B775927 : Blo 774336 775927 := bstep (se 1 (by rfl) ⟨581945, by rfl⟩ : syracuseStep 775927 = 1163891) B1163891
theorem B775947 : Blo 774336 775947 := bstep (se 1 (by rfl) ⟨581960, by rfl⟩ : syracuseStep 775947 = 1163921) B1163921
theorem B775959 : Blo 774336 775959 := bstep (se 1 (by rfl) ⟨581969, by rfl⟩ : syracuseStep 775959 = 1163939) B1163939
theorem B775979 : Blo 774336 775979 := bstep (se 1 (by rfl) ⟨581984, by rfl⟩ : syracuseStep 775979 = 1163969) B1163969
theorem B775991 : Blo 774336 775991 := bstep (se 1 (by rfl) ⟨581993, by rfl⟩ : syracuseStep 775991 = 1163987) B1163987
theorem B776011 : Blo 774336 776011 := bstep (se 1 (by rfl) ⟨582008, by rfl⟩ : syracuseStep 776011 = 1164017) B1164017
theorem B776023 : Blo 774336 776023 := bstep (se 1 (by rfl) ⟨582017, by rfl⟩ : syracuseStep 776023 = 1164035) B1164035
theorem B874327 : Blo 774336 874327 := bstep (se 1 (by rfl) ⟨655745, by rfl⟩ : syracuseStep 874327 = 1311491) B1311491
theorem B776043 : Blo 774336 776043 := bstep (se 1 (by rfl) ⟨582032, by rfl⟩ : syracuseStep 776043 = 1164065) B1164065
theorem B776055 : Blo 774336 776055 := bstep (se 1 (by rfl) ⟨582041, by rfl⟩ : syracuseStep 776055 = 1164083) B1164083
theorem B776075 : Blo 774336 776075 := bstep (se 1 (by rfl) ⟨582056, by rfl⟩ : syracuseStep 776075 = 1164113) B1164113
theorem B1398667 : Blo 774336 1398667 := bstep (se 1 (by rfl) ⟨1049000, by rfl⟩ : syracuseStep 1398667 = 2098001) B2098001
theorem B776087 : Blo 774336 776087 := bstep (se 1 (by rfl) ⟨582065, by rfl⟩ : syracuseStep 776087 = 1164131) B1164131
theorem B1496983 : Blo 774336 1496983 := bstep (se 1 (by rfl) ⟨1122737, by rfl⟩ : syracuseStep 1496983 = 2245475) B2245475
theorem B776107 : Blo 774336 776107 := bstep (se 1 (by rfl) ⟨582080, by rfl⟩ : syracuseStep 776107 = 1164161) B1164161
theorem B776119 : Blo 774336 776119 := bstep (se 1 (by rfl) ⟨582089, by rfl⟩ : syracuseStep 776119 = 1164179) B1164179
theorem B776139 : Blo 774336 776139 := bstep (se 1 (by rfl) ⟨582104, by rfl⟩ : syracuseStep 776139 = 1164209) B1164209
theorem B776151 : Blo 774336 776151 := bstep (se 1 (by rfl) ⟨582113, by rfl⟩ : syracuseStep 776151 = 1164227) B1164227
theorem B8378329 : Blo 774336 8378329 := bstep (se 2 (by rfl) ⟨3141873, by rfl⟩ : syracuseStep 8378329 = 6283747) B6283747
theorem B776171 : Blo 774336 776171 := bstep (se 1 (by rfl) ⟨582128, by rfl⟩ : syracuseStep 776171 = 1164257) B1164257
theorem B776183 : Blo 774336 776183 := bstep (se 1 (by rfl) ⟨582137, by rfl⟩ : syracuseStep 776183 = 1164275) B1164275
theorem B776203 : Blo 774336 776203 := bstep (se 1 (by rfl) ⟨582152, by rfl⟩ : syracuseStep 776203 = 1164305) B1164305
theorem B874507 : Blo 774336 874507 := bstep (se 1 (by rfl) ⟨655880, by rfl⟩ : syracuseStep 874507 = 1311761) B1311761
theorem B776215 : Blo 774336 776215 := bstep (se 1 (by rfl) ⟨582161, by rfl⟩ : syracuseStep 776215 = 1164323) B1164323
theorem B776235 : Blo 774336 776235 := bstep (se 1 (by rfl) ⟨582176, by rfl⟩ : syracuseStep 776235 = 1164353) B1164353
theorem B776247 : Blo 774336 776247 := bstep (se 1 (by rfl) ⟨582185, by rfl⟩ : syracuseStep 776247 = 1164371) B1164371
theorem B5036107 : Blo 774336 5036107 := bstep (se 1 (by rfl) ⟨3777080, by rfl⟩ : syracuseStep 5036107 = 7554161) B7554161
theorem B776267 : Blo 774336 776267 := bstep (se 1 (by rfl) ⟨582200, by rfl⟩ : syracuseStep 776267 = 1164401) B1164401
theorem B776279 : Blo 774336 776279 := bstep (se 1 (by rfl) ⟨582209, by rfl⟩ : syracuseStep 776279 = 1164419) B1164419
theorem B776299 : Blo 774336 776299 := bstep (se 1 (by rfl) ⟨582224, by rfl⟩ : syracuseStep 776299 = 1164449) B1164449
theorem B776311 : Blo 774336 776311 := bstep (se 1 (by rfl) ⟨582233, by rfl⟩ : syracuseStep 776311 = 1164467) B1164467
theorem B874615 : Blo 774336 874615 := bstep (se 1 (by rfl) ⟨655961, by rfl⟩ : syracuseStep 874615 = 1311923) B1311923
theorem B776331 : Blo 774336 776331 := bstep (se 1 (by rfl) ⟨582248, by rfl⟩ : syracuseStep 776331 = 1164497) B1164497
theorem B776343 : Blo 774336 776343 := bstep (se 1 (by rfl) ⟨582257, by rfl⟩ : syracuseStep 776343 = 1164515) B1164515
theorem B7100567 : Blo 774336 7100567 := bstep (se 1 (by rfl) ⟨5325425, by rfl⟩ : syracuseStep 7100567 = 10650851) B10650851
theorem B1104025 : Blo 774336 1104025 := bstep (se 2 (by rfl) ⟨414009, by rfl⟩ : syracuseStep 1104025 = 828019) B828019
theorem B776363 : Blo 774336 776363 := bstep (se 1 (by rfl) ⟨582272, by rfl⟩ : syracuseStep 776363 = 1164545) B1164545
theorem B776375 : Blo 774336 776375 := bstep (se 1 (by rfl) ⟨582281, by rfl⟩ : syracuseStep 776375 = 1164563) B1164563
theorem B776395 : Blo 774336 776395 := bstep (se 1 (by rfl) ⟨582296, by rfl⟩ : syracuseStep 776395 = 1164593) B1164593
theorem B776407 : Blo 774336 776407 := bstep (se 1 (by rfl) ⟨582305, by rfl⟩ : syracuseStep 776407 = 1164611) B1164611
theorem B776427 : Blo 774336 776427 := bstep (se 1 (by rfl) ⟨582320, by rfl⟩ : syracuseStep 776427 = 1164641) B1164641
theorem B1399027 : Blo 774336 1399027 := bstep (se 1 (by rfl) ⟨1049270, by rfl⟩ : syracuseStep 1399027 = 2098541) B2098541
theorem B776439 : Blo 774336 776439 := bstep (se 1 (by rfl) ⟨582329, by rfl⟩ : syracuseStep 776439 = 1164659) B1164659
theorem B1104139 : Blo 774336 1104139 := bstep (se 1 (by rfl) ⟨828104, by rfl⟩ : syracuseStep 1104139 = 1656209) B1656209
theorem B776459 : Blo 774336 776459 := bstep (se 1 (by rfl) ⟨582344, by rfl⟩ : syracuseStep 776459 = 1164689) B1164689
theorem B776471 : Blo 774336 776471 := bstep (se 1 (by rfl) ⟨582353, by rfl⟩ : syracuseStep 776471 = 1164707) B1164707
theorem B776491 : Blo 774336 776491 := bstep (se 1 (by rfl) ⟨582368, by rfl⟩ : syracuseStep 776491 = 1164737) B1164737
theorem B874795 : Blo 774336 874795 := bstep (se 1 (by rfl) ⟨656096, by rfl⟩ : syracuseStep 874795 = 1312193) B1312193
theorem B776503 : Blo 774336 776503 := bstep (se 1 (by rfl) ⟨582377, by rfl⟩ : syracuseStep 776503 = 1164755) B1164755
theorem B1661249 : Blo 774336 1661249 := bstep (se 2 (by rfl) ⟨622968, by rfl⟩ : syracuseStep 1661249 = 1245937) B1245937
theorem B1890635 : Blo 774336 1890635 := bstep (se 1 (by rfl) ⟨1417976, by rfl⟩ : syracuseStep 1890635 = 2835953) B2835953
theorem B776523 : Blo 774336 776523 := bstep (se 1 (by rfl) ⟨582392, by rfl⟩ : syracuseStep 776523 = 1164785) B1164785
theorem B776535 : Blo 774336 776535 := bstep (se 1 (by rfl) ⟨582401, by rfl⟩ : syracuseStep 776535 = 1164803) B1164803
theorem B842071 : Blo 774336 842071 := bstep (se 1 (by rfl) ⟨631553, by rfl⟩ : syracuseStep 842071 = 1263107) B1263107
theorem B776555 : Blo 774336 776555 := bstep (se 1 (by rfl) ⟨582416, by rfl⟩ : syracuseStep 776555 = 1164833) B1164833
theorem B776567 : Blo 774336 776567 := bstep (se 1 (by rfl) ⟨582425, by rfl⟩ : syracuseStep 776567 = 1164851) B1164851
theorem B776587 : Blo 774336 776587 := bstep (se 1 (by rfl) ⟨582440, by rfl⟩ : syracuseStep 776587 = 1164881) B1164881
theorem B776599 : Blo 774336 776599 := bstep (se 1 (by rfl) ⟨582449, by rfl⟩ : syracuseStep 776599 = 1164899) B1164899
theorem B874903 : Blo 774336 874903 := bstep (se 1 (by rfl) ⟨656177, by rfl⟩ : syracuseStep 874903 = 1312355) B1312355
theorem B776619 : Blo 774336 776619 := bstep (se 1 (by rfl) ⟨582464, by rfl⟩ : syracuseStep 776619 = 1164929) B1164929
theorem B776631 : Blo 774336 776631 := bstep (se 1 (by rfl) ⟨582473, by rfl⟩ : syracuseStep 776631 = 1164947) B1164947
theorem B776651 : Blo 774336 776651 := bstep (se 1 (by rfl) ⟨582488, by rfl⟩ : syracuseStep 776651 = 1164977) B1164977
theorem B776663 : Blo 774336 776663 := bstep (se 1 (by rfl) ⟨582497, by rfl⟩ : syracuseStep 776663 = 1164995) B1164995
theorem B776683 : Blo 774336 776683 := bstep (se 1 (by rfl) ⟨582512, by rfl⟩ : syracuseStep 776683 = 1165025) B1165025
theorem B776695 : Blo 774336 776695 := bstep (se 1 (by rfl) ⟨582521, by rfl⟩ : syracuseStep 776695 = 1165043) B1165043
theorem B776715 : Blo 774336 776715 := bstep (se 1 (by rfl) ⟨582536, by rfl⟩ : syracuseStep 776715 = 1165073) B1165073
theorem B776727 : Blo 774336 776727 := bstep (se 1 (by rfl) ⟨582545, by rfl⟩ : syracuseStep 776727 = 1165091) B1165091
theorem B776747 : Blo 774336 776747 := bstep (se 1 (by rfl) ⟨582560, by rfl⟩ : syracuseStep 776747 = 1165121) B1165121
theorem B776759 : Blo 774336 776759 := bstep (se 1 (by rfl) ⟨582569, by rfl⟩ : syracuseStep 776759 = 1165139) B1165139
theorem B776779 : Blo 774336 776779 := bstep (se 1 (by rfl) ⟨582584, by rfl⟩ : syracuseStep 776779 = 1165169) B1165169
theorem B875083 : Blo 774336 875083 := bstep (se 1 (by rfl) ⟨656312, by rfl⟩ : syracuseStep 875083 = 1312625) B1312625
theorem B776791 : Blo 774336 776791 := bstep (se 1 (by rfl) ⟨582593, by rfl⟩ : syracuseStep 776791 = 1165187) B1165187
theorem B776811 : Blo 774336 776811 := bstep (se 1 (by rfl) ⟨582608, by rfl⟩ : syracuseStep 776811 = 1165217) B1165217
theorem B776823 : Blo 774336 776823 := bstep (se 1 (by rfl) ⟨582617, by rfl⟩ : syracuseStep 776823 = 1165235) B1165235
theorem B776843 : Blo 774336 776843 := bstep (se 1 (by rfl) ⟨582632, by rfl⟩ : syracuseStep 776843 = 1165265) B1165265
theorem B776855 : Blo 774336 776855 := bstep (se 1 (by rfl) ⟨582641, by rfl⟩ : syracuseStep 776855 = 1165283) B1165283
theorem B776875 : Blo 774336 776875 := bstep (se 1 (by rfl) ⟨582656, by rfl⟩ : syracuseStep 776875 = 1165313) B1165313
theorem B776887 : Blo 774336 776887 := bstep (se 1 (by rfl) ⟨582665, by rfl⟩ : syracuseStep 776887 = 1165331) B1165331
theorem B875191 : Blo 774336 875191 := bstep (se 1 (by rfl) ⟨656393, by rfl⟩ : syracuseStep 875191 = 1312787) B1312787
theorem B776907 : Blo 774336 776907 := bstep (se 1 (by rfl) ⟨582680, by rfl⟩ : syracuseStep 776907 = 1165361) B1165361
theorem B776919 : Blo 774336 776919 := bstep (se 1 (by rfl) ⟨582689, by rfl⟩ : syracuseStep 776919 = 1165379) B1165379
theorem B776939 : Blo 774336 776939 := bstep (se 1 (by rfl) ⟨582704, by rfl⟩ : syracuseStep 776939 = 1165409) B1165409
theorem B50420465 : Blo 774336 50420465 := bstep (se 2 (by rfl) ⟨18907674, by rfl⟩ : syracuseStep 50420465 = 37815349) B37815349
theorem B776951 : Blo 774336 776951 := bstep (se 1 (by rfl) ⟨582713, by rfl⟩ : syracuseStep 776951 = 1165427) B1165427
theorem B776971 : Blo 774336 776971 := bstep (se 1 (by rfl) ⟨582728, by rfl⟩ : syracuseStep 776971 = 1165457) B1165457
theorem B776983 : Blo 774336 776983 := bstep (se 1 (by rfl) ⟨582737, by rfl⟩ : syracuseStep 776983 = 1165475) B1165475
theorem B777003 : Blo 774336 777003 := bstep (se 1 (by rfl) ⟨582752, by rfl⟩ : syracuseStep 777003 = 1165505) B1165505
theorem B3726125 : Blo 774336 3726125 := bstep (se 3 (by rfl) ⟨698648, by rfl⟩ : syracuseStep 3726125 = 1397297) B1397297
theorem B777015 : Blo 774336 777015 := bstep (se 1 (by rfl) ⟨582761, by rfl⟩ : syracuseStep 777015 = 1165523) B1165523
theorem B5299019 : Blo 774336 5299019 := bstep (se 1 (by rfl) ⟨3974264, by rfl⟩ : syracuseStep 5299019 = 7948529) B7948529
theorem B777035 : Blo 774336 777035 := bstep (se 1 (by rfl) ⟨582776, by rfl⟩ : syracuseStep 777035 = 1165553) B1165553
theorem B1661771 : Blo 774336 1661771 := bstep (se 1 (by rfl) ⟨1246328, by rfl⟩ : syracuseStep 1661771 = 2492657) B2492657
theorem B777047 : Blo 774336 777047 := bstep (se 1 (by rfl) ⟨582785, by rfl⟩ : syracuseStep 777047 = 1165571) B1165571
theorem B5888861 : Blo 774336 5888861 := bstep (se 3 (by rfl) ⟨1104161, by rfl⟩ : syracuseStep 5888861 = 2208323) B2208323
theorem B777067 : Blo 774336 777067 := bstep (se 1 (by rfl) ⟨582800, by rfl⟩ : syracuseStep 777067 = 1165601) B1165601
theorem B875371 : Blo 774336 875371 := bstep (se 1 (by rfl) ⟨656528, by rfl⟩ : syracuseStep 875371 = 1313057) B1313057
theorem B777079 : Blo 774336 777079 := bstep (se 1 (by rfl) ⟨582809, by rfl⟩ : syracuseStep 777079 = 1165619) B1165619
theorem B777099 : Blo 774336 777099 := bstep (se 1 (by rfl) ⟨582824, by rfl⟩ : syracuseStep 777099 = 1165649) B1165649
theorem B777111 : Blo 774336 777111 := bstep (se 1 (by rfl) ⟨582833, by rfl⟩ : syracuseStep 777111 = 1165667) B1165667
theorem B777131 : Blo 774336 777131 := bstep (se 1 (by rfl) ⟨582848, by rfl⟩ : syracuseStep 777131 = 1165697) B1165697
theorem B777143 : Blo 774336 777143 := bstep (se 1 (by rfl) ⟨582857, by rfl⟩ : syracuseStep 777143 = 1165715) B1165715
theorem B777163 : Blo 774336 777163 := bstep (se 1 (by rfl) ⟨582872, by rfl⟩ : syracuseStep 777163 = 1165745) B1165745
theorem B777175 : Blo 774336 777175 := bstep (se 1 (by rfl) ⟨582881, by rfl⟩ : syracuseStep 777175 = 1165763) B1165763
theorem B875479 : Blo 774336 875479 := bstep (se 1 (by rfl) ⟨656609, by rfl⟩ : syracuseStep 875479 = 1313219) B1313219
theorem B9952217 : Blo 774336 9952217 := bstep (se 2 (by rfl) ⟨3732081, by rfl⟩ : syracuseStep 9952217 = 7464163) B7464163
theorem B777195 : Blo 774336 777195 := bstep (se 1 (by rfl) ⟨582896, by rfl⟩ : syracuseStep 777195 = 1165793) B1165793
theorem B777207 : Blo 774336 777207 := bstep (se 1 (by rfl) ⟨582905, by rfl⟩ : syracuseStep 777207 = 1165811) B1165811
theorem B777227 : Blo 774336 777227 := bstep (se 1 (by rfl) ⟨582920, by rfl⟩ : syracuseStep 777227 = 1165841) B1165841
theorem B777239 : Blo 774336 777239 := bstep (se 1 (by rfl) ⟨582929, by rfl⟩ : syracuseStep 777239 = 1165859) B1165859
theorem B777259 : Blo 774336 777259 := bstep (se 1 (by rfl) ⟨582944, by rfl⟩ : syracuseStep 777259 = 1165889) B1165889
theorem B777271 : Blo 774336 777271 := bstep (se 1 (by rfl) ⟨582953, by rfl⟩ : syracuseStep 777271 = 1165907) B1165907
theorem B777291 : Blo 774336 777291 := bstep (se 1 (by rfl) ⟨582968, by rfl⟩ : syracuseStep 777291 = 1165937) B1165937
theorem B777303 : Blo 774336 777303 := bstep (se 1 (by rfl) ⟨582977, by rfl⟩ : syracuseStep 777303 = 1165955) B1165955
theorem B777323 : Blo 774336 777323 := bstep (se 1 (by rfl) ⟨582992, by rfl⟩ : syracuseStep 777323 = 1165985) B1165985
theorem B777335 : Blo 774336 777335 := bstep (se 1 (by rfl) ⟨583001, by rfl⟩ : syracuseStep 777335 = 1166003) B1166003
theorem B777355 : Blo 774336 777355 := bstep (se 1 (by rfl) ⟨583016, by rfl⟩ : syracuseStep 777355 = 1166033) B1166033
theorem B777367 : Blo 774336 777367 := bstep (se 1 (by rfl) ⟨583025, by rfl⟩ : syracuseStep 777367 = 1166051) B1166051
theorem B777387 : Blo 774336 777387 := bstep (se 1 (by rfl) ⟨583040, by rfl⟩ : syracuseStep 777387 = 1166081) B1166081
theorem B47733941 : Blo 774336 47733941 := bstep (se 5 (by rfl) ⟨2237528, by rfl⟩ : syracuseStep 47733941 = 4475057) B4475057
theorem B777399 : Blo 774336 777399 := bstep (se 1 (by rfl) ⟨583049, by rfl⟩ : syracuseStep 777399 = 1166099) B1166099
theorem B777419 : Blo 774336 777419 := bstep (se 1 (by rfl) ⟨583064, by rfl⟩ : syracuseStep 777419 = 1166129) B1166129
theorem B11164877 : Blo 774336 11164877 := bstep (se 3 (by rfl) ⟨2093414, by rfl⟩ : syracuseStep 11164877 = 4186829) B4186829
theorem B777431 : Blo 774336 777431 := bstep (se 1 (by rfl) ⟨583073, by rfl⟩ : syracuseStep 777431 = 1166147) B1166147
theorem B777451 : Blo 774336 777451 := bstep (se 1 (by rfl) ⟨583088, by rfl⟩ : syracuseStep 777451 = 1166177) B1166177
theorem B777463 : Blo 774336 777463 := bstep (se 1 (by rfl) ⟨583097, by rfl⟩ : syracuseStep 777463 = 1166195) B1166195
theorem B777483 : Blo 774336 777483 := bstep (se 1 (by rfl) ⟨583112, by rfl⟩ : syracuseStep 777483 = 1166225) B1166225
theorem B777495 : Blo 774336 777495 := bstep (se 1 (by rfl) ⟨583121, by rfl⟩ : syracuseStep 777495 = 1166243) B1166243
theorem B777515 : Blo 774336 777515 := bstep (se 1 (by rfl) ⟨583136, by rfl⟩ : syracuseStep 777515 = 1166273) B1166273
theorem B777527 : Blo 774336 777527 := bstep (se 1 (by rfl) ⟨583145, by rfl⟩ : syracuseStep 777527 = 1166291) B1166291
theorem B777547 : Blo 774336 777547 := bstep (se 1 (by rfl) ⟨583160, by rfl⟩ : syracuseStep 777547 = 1166321) B1166321
theorem B777559 : Blo 774336 777559 := bstep (se 1 (by rfl) ⟨583169, by rfl⟩ : syracuseStep 777559 = 1166339) B1166339
theorem B777579 : Blo 774336 777579 := bstep (se 1 (by rfl) ⟨583184, by rfl⟩ : syracuseStep 777579 = 1166369) B1166369
theorem B777591 : Blo 774336 777591 := bstep (se 1 (by rfl) ⟨583193, by rfl⟩ : syracuseStep 777591 = 1166387) B1166387
theorem B777611 : Blo 774336 777611 := bstep (se 1 (by rfl) ⟨583208, by rfl⟩ : syracuseStep 777611 = 1166417) B1166417
theorem B777623 : Blo 774336 777623 := bstep (se 1 (by rfl) ⟨583217, by rfl⟩ : syracuseStep 777623 = 1166435) B1166435
theorem B777643 : Blo 774336 777643 := bstep (se 1 (by rfl) ⟨583232, by rfl⟩ : syracuseStep 777643 = 1166465) B1166465
theorem B777655 : Blo 774336 777655 := bstep (se 1 (by rfl) ⟨583241, by rfl⟩ : syracuseStep 777655 = 1166483) B1166483
theorem B777675 : Blo 774336 777675 := bstep (se 1 (by rfl) ⟨583256, by rfl⟩ : syracuseStep 777675 = 1166513) B1166513
theorem B777687 : Blo 774336 777687 := bstep (se 1 (by rfl) ⟨583265, by rfl⟩ : syracuseStep 777687 = 1166531) B1166531
theorem B777707 : Blo 774336 777707 := bstep (se 1 (by rfl) ⟨583280, by rfl⟩ : syracuseStep 777707 = 1166561) B1166561
theorem B777719 : Blo 774336 777719 := bstep (se 1 (by rfl) ⟨583289, by rfl⟩ : syracuseStep 777719 = 1166579) B1166579
theorem B777739 : Blo 774336 777739 := bstep (se 1 (by rfl) ⟨583304, by rfl⟩ : syracuseStep 777739 = 1166609) B1166609
theorem B777751 : Blo 774336 777751 := bstep (se 1 (by rfl) ⟨583313, by rfl⟩ : syracuseStep 777751 = 1166627) B1166627
theorem B777771 : Blo 774336 777771 := bstep (se 1 (by rfl) ⟨583328, by rfl⟩ : syracuseStep 777771 = 1166657) B1166657
theorem B777783 : Blo 774336 777783 := bstep (se 1 (by rfl) ⟨583337, by rfl⟩ : syracuseStep 777783 = 1166675) B1166675
theorem B1105483 : Blo 774336 1105483 := bstep (se 1 (by rfl) ⟨829112, by rfl⟩ : syracuseStep 1105483 = 1658225) B1658225
theorem B777803 : Blo 774336 777803 := bstep (se 1 (by rfl) ⟨583352, by rfl⟩ : syracuseStep 777803 = 1166705) B1166705
theorem B777815 : Blo 774336 777815 := bstep (se 1 (by rfl) ⟨583361, by rfl⟩ : syracuseStep 777815 = 1166723) B1166723
theorem B777835 : Blo 774336 777835 := bstep (se 1 (by rfl) ⟨583376, by rfl⟩ : syracuseStep 777835 = 1166753) B1166753
theorem B777847 : Blo 774336 777847 := bstep (se 1 (by rfl) ⟨583385, by rfl⟩ : syracuseStep 777847 = 1166771) B1166771
theorem B777867 : Blo 774336 777867 := bstep (se 1 (by rfl) ⟨583400, by rfl⟩ : syracuseStep 777867 = 1166801) B1166801
theorem B777879 : Blo 774336 777879 := bstep (se 1 (by rfl) ⟨583409, by rfl⟩ : syracuseStep 777879 = 1166819) B1166819
theorem B777899 : Blo 774336 777899 := bstep (se 1 (by rfl) ⟨583424, by rfl⟩ : syracuseStep 777899 = 1166849) B1166849
theorem B777911 : Blo 774336 777911 := bstep (se 1 (by rfl) ⟨583433, by rfl⟩ : syracuseStep 777911 = 1166867) B1166867
theorem B409001669 : Blo 774336 409001669 := bstep (se 4 (by rfl) ⟨38343906, by rfl⟩ : syracuseStep 409001669 = 76687813) B76687813
theorem B777931 : Blo 774336 777931 := bstep (se 1 (by rfl) ⟨583448, by rfl⟩ : syracuseStep 777931 = 1166897) B1166897
theorem B777943 : Blo 774336 777943 := bstep (se 1 (by rfl) ⟨583457, by rfl⟩ : syracuseStep 777943 = 1166915) B1166915
theorem B777963 : Blo 774336 777963 := bstep (se 1 (by rfl) ⟨583472, by rfl⟩ : syracuseStep 777963 = 1166945) B1166945
theorem B777975 : Blo 774336 777975 := bstep (se 1 (by rfl) ⟨583481, by rfl⟩ : syracuseStep 777975 = 1166963) B1166963
theorem B777995 : Blo 774336 777995 := bstep (se 1 (by rfl) ⟨583496, by rfl⟩ : syracuseStep 777995 = 1166993) B1166993
theorem B2940695 : Blo 774336 2940695 := bstep (se 1 (by rfl) ⟨2205521, by rfl⟩ : syracuseStep 2940695 = 4411043) B4411043
theorem B778007 : Blo 774336 778007 := bstep (se 1 (by rfl) ⟨583505, by rfl⟩ : syracuseStep 778007 = 1167011) B1167011
theorem B778027 : Blo 774336 778027 := bstep (se 1 (by rfl) ⟨583520, by rfl⟩ : syracuseStep 778027 = 1167041) B1167041
theorem B1400627 : Blo 774336 1400627 := bstep (se 1 (by rfl) ⟨1050470, by rfl⟩ : syracuseStep 1400627 = 2100941) B2100941
theorem B778039 : Blo 774336 778039 := bstep (se 1 (by rfl) ⟨583529, by rfl⟩ : syracuseStep 778039 = 1167059) B1167059
theorem B2481995 : Blo 774336 2481995 := bstep (se 1 (by rfl) ⟨1861496, by rfl⟩ : syracuseStep 2481995 = 3722993) B3722993
theorem B778059 : Blo 774336 778059 := bstep (se 1 (by rfl) ⟨583544, by rfl⟩ : syracuseStep 778059 = 1167089) B1167089
theorem B1105751 : Blo 774336 1105751 := bstep (se 1 (by rfl) ⟨829313, by rfl⟩ : syracuseStep 1105751 = 1658627) B1658627
theorem B778071 : Blo 774336 778071 := bstep (se 1 (by rfl) ⟨583553, by rfl⟩ : syracuseStep 778071 = 1167107) B1167107
theorem B778091 : Blo 774336 778091 := bstep (se 1 (by rfl) ⟨583568, by rfl⟩ : syracuseStep 778091 = 1167137) B1167137
theorem B778103 : Blo 774336 778103 := bstep (se 1 (by rfl) ⟨583577, by rfl⟩ : syracuseStep 778103 = 1167155) B1167155
theorem B778123 : Blo 774336 778123 := bstep (se 1 (by rfl) ⟨583592, by rfl⟩ : syracuseStep 778123 = 1167185) B1167185
theorem B778135 : Blo 774336 778135 := bstep (se 1 (by rfl) ⟨583601, by rfl⟩ : syracuseStep 778135 = 1167203) B1167203
theorem B778155 : Blo 774336 778155 := bstep (se 1 (by rfl) ⟨583616, by rfl⟩ : syracuseStep 778155 = 1167233) B1167233
theorem B778167 : Blo 774336 778167 := bstep (se 1 (by rfl) ⟨583625, by rfl⟩ : syracuseStep 778167 = 1167251) B1167251
theorem B778187 : Blo 774336 778187 := bstep (se 1 (by rfl) ⟨583640, by rfl⟩ : syracuseStep 778187 = 1167281) B1167281
theorem B778199 : Blo 774336 778199 := bstep (se 1 (by rfl) ⟨583649, by rfl⟩ : syracuseStep 778199 = 1167299) B1167299
theorem B2940893 : Blo 774336 2940893 := bstep (se 3 (by rfl) ⟨551417, by rfl⟩ : syracuseStep 2940893 = 1102835) B1102835
theorem B778219 : Blo 774336 778219 := bstep (se 1 (by rfl) ⟨583664, by rfl⟩ : syracuseStep 778219 = 1167329) B1167329
theorem B778231 : Blo 774336 778231 := bstep (se 1 (by rfl) ⟨583673, by rfl⟩ : syracuseStep 778231 = 1167347) B1167347
theorem B778251 : Blo 774336 778251 := bstep (se 1 (by rfl) ⟨583688, by rfl⟩ : syracuseStep 778251 = 1167377) B1167377
theorem B778263 : Blo 774336 778263 := bstep (se 1 (by rfl) ⟨583697, by rfl⟩ : syracuseStep 778263 = 1167395) B1167395
theorem B1400857 : Blo 774336 1400857 := bstep (se 2 (by rfl) ⟨525321, by rfl⟩ : syracuseStep 1400857 = 1050643) B1050643
theorem B778283 : Blo 774336 778283 := bstep (se 1 (by rfl) ⟨583712, by rfl⟩ : syracuseStep 778283 = 1167425) B1167425
theorem B778295 : Blo 774336 778295 := bstep (se 1 (by rfl) ⟨583721, by rfl⟩ : syracuseStep 778295 = 1167443) B1167443
theorem B778315 : Blo 774336 778315 := bstep (se 1 (by rfl) ⟨583736, by rfl⟩ : syracuseStep 778315 = 1167473) B1167473
theorem B778327 : Blo 774336 778327 := bstep (se 1 (by rfl) ⟨583745, by rfl⟩ : syracuseStep 778327 = 1167491) B1167491
theorem B2613707 : Blo 774336 2613707 := bstep (se 1 (by rfl) ⟨1960280, by rfl⟩ : syracuseStep 2613707 = 3920561) B3920561
theorem B3924611 : Blo 774336 3924611 := bstep (se 1 (by rfl) ⟨2943458, by rfl⟩ : syracuseStep 3924611 = 5886917) B5886917
theorem B2613977 : Blo 774336 2613977 := bstep (se 2 (by rfl) ⟨980241, by rfl⟩ : syracuseStep 2613977 = 1960483) B1960483
theorem B1106713 : Blo 774336 1106713 := bstep (se 2 (by rfl) ⟨415017, by rfl⟩ : syracuseStep 1106713 = 830035) B830035
theorem B1860545 : Blo 774336 1860545 := bstep (se 2 (by rfl) ⟨697704, by rfl⟩ : syracuseStep 1860545 = 1395409) B1395409
theorem B1860659 : Blo 774336 1860659 := bstep (se 1 (by rfl) ⟨1395494, by rfl⟩ : syracuseStep 1860659 = 2790989) B2790989
theorem B9954677 : Blo 774336 9954677 := bstep (se 5 (by rfl) ⟨466625, by rfl⟩ : syracuseStep 9954677 = 933251) B933251
theorem B2614679 : Blo 774336 2614679 := bstep (se 1 (by rfl) ⟨1961009, by rfl⟩ : syracuseStep 2614679 = 3922019) B3922019
theorem B2483635 : Blo 774336 2483635 := bstep (se 1 (by rfl) ⟨1862726, by rfl⟩ : syracuseStep 2483635 = 3725453) B3725453
theorem B3991133 : Blo 774336 3991133 := bstep (se 3 (by rfl) ⟨748337, by rfl⟩ : syracuseStep 3991133 = 1496675) B1496675
theorem B1795841 : Blo 774336 1795841 := bstep (se 2 (by rfl) ⟨673440, by rfl⟩ : syracuseStep 1795841 = 1346881) B1346881
theorem B2942851 : Blo 774336 2942851 := bstep (se 1 (by rfl) ⟨2207138, by rfl⟩ : syracuseStep 2942851 = 4414277) B4414277
theorem B2615219 : Blo 774336 2615219 := bstep (se 1 (by rfl) ⟨1961414, by rfl⟩ : syracuseStep 2615219 = 3922829) B3922829
theorem B5597201 : Blo 774336 5597201 := bstep (se 2 (by rfl) ⟨2098950, by rfl⟩ : syracuseStep 5597201 = 4197901) B4197901
theorem B3139735 : Blo 774336 3139735 := bstep (se 1 (by rfl) ⟨2354801, by rfl⟩ : syracuseStep 3139735 = 4709603) B4709603
theorem B2943155 : Blo 774336 2943155 := bstep (se 1 (by rfl) ⟨2207366, by rfl⟩ : syracuseStep 2943155 = 4414733) B4414733
theorem B2615489 : Blo 774336 2615489 := bstep (se 2 (by rfl) ⟨980808, by rfl⟩ : syracuseStep 2615489 = 1961617) B1961617
theorem B1960139 : Blo 774336 1960139 := bstep (se 1 (by rfl) ⟨1470104, by rfl⟩ : syracuseStep 1960139 = 2940209) B2940209
theorem B1108171 : Blo 774336 1108171 := bstep (se 1 (by rfl) ⟨831128, by rfl⟩ : syracuseStep 1108171 = 1662257) B1662257
theorem B1108183 : Blo 774336 1108183 := bstep (se 1 (by rfl) ⟨831137, by rfl⟩ : syracuseStep 1108183 = 1662275) B1662275
theorem B2484569 : Blo 774336 2484569 := bstep (se 2 (by rfl) ⟨931713, by rfl⟩ : syracuseStep 2484569 = 1863427) B1863427
theorem B60615029 : Blo 774336 60615029 := bstep (se 5 (by rfl) ⟨2841329, by rfl⟩ : syracuseStep 60615029 = 5682659) B5682659
theorem B2616029 : Blo 774336 2616029 := bstep (se 3 (by rfl) ⟨490505, by rfl⟩ : syracuseStep 2616029 = 981011) B981011
theorem B2943809 : Blo 774336 2943809 := bstep (se 2 (by rfl) ⟨1103928, by rfl⟩ : syracuseStep 2943809 = 2207857) B2207857
theorem B167668697 : Blo 774336 167668697 := bstep (se 2 (by rfl) ⟨62875761, by rfl⟩ : syracuseStep 167668697 = 125751523) B125751523
theorem B2485313 : Blo 774336 2485313 := bstep (se 2 (by rfl) ⟨931992, by rfl⟩ : syracuseStep 2485313 = 1863985) B1863985
theorem B1961111 : Blo 774336 1961111 := bstep (se 1 (by rfl) ⟨1470833, by rfl⟩ : syracuseStep 1961111 = 2941667) B2941667
theorem B4418833 : Blo 774336 4418833 := bstep (se 2 (by rfl) ⟨1657062, by rfl⟩ : syracuseStep 4418833 = 3314125) B3314125
theorem B3403139 : Blo 774336 3403139 := bstep (se 1 (by rfl) ⟨2552354, by rfl⟩ : syracuseStep 3403139 = 5104709) B5104709
theorem B3534283 : Blo 774336 3534283 := bstep (se 1 (by rfl) ⟨2650712, by rfl⟩ : syracuseStep 3534283 = 5301425) B5301425
theorem B8842769 : Blo 774336 8842769 := bstep (se 2 (by rfl) ⟨3316038, by rfl⟩ : syracuseStep 8842769 = 6632077) B6632077
theorem B1961779 : Blo 774336 1961779 := bstep (se 1 (by rfl) ⟨1471334, by rfl⟩ : syracuseStep 1961779 = 2942669) B2942669
theorem B2617163 : Blo 774336 2617163 := bstep (se 1 (by rfl) ⟨1962872, by rfl⟩ : syracuseStep 2617163 = 3925745) B3925745
theorem B2125747 : Blo 774336 2125747 := bstep (se 1 (by rfl) ⟨1594310, by rfl⟩ : syracuseStep 2125747 = 3188621) B3188621
theorem B1961921 : Blo 774336 1961921 := bstep (se 2 (by rfl) ⟨735720, by rfl⟩ : syracuseStep 1961921 = 1471441) B1471441
theorem B2486209 : Blo 774336 2486209 := bstep (se 2 (by rfl) ⟨932328, by rfl⟩ : syracuseStep 2486209 = 1864657) B1864657
theorem B2945069 : Blo 774336 2945069 := bstep (se 3 (by rfl) ⟨552200, by rfl⟩ : syracuseStep 2945069 = 1104401) B1104401
theorem B2945099 : Blo 774336 2945099 := bstep (se 1 (by rfl) ⟨2208824, by rfl⟩ : syracuseStep 2945099 = 4417649) B4417649
theorem B2617433 : Blo 774336 2617433 := bstep (se 2 (by rfl) ⟨981537, by rfl⟩ : syracuseStep 2617433 = 1963075) B1963075
theorem B3928337 : Blo 774336 3928337 := bstep (se 2 (by rfl) ⟨1473126, by rfl⟩ : syracuseStep 3928337 = 2946253) B2946253
theorem B1306955 : Blo 774336 1306955 := bstep (se 1 (by rfl) ⟨980216, by rfl⟩ : syracuseStep 1306955 = 1960433) B1960433
theorem B3928499 : Blo 774336 3928499 := bstep (se 1 (by rfl) ⟨2946374, by rfl⟩ : syracuseStep 3928499 = 5892749) B5892749
theorem B1307083 : Blo 774336 1307083 := bstep (se 1 (by rfl) ⟨980312, by rfl⟩ : syracuseStep 1307083 = 1960625) B1960625
theorem B1307225 : Blo 774336 1307225 := bstep (se 2 (by rfl) ⟨490209, by rfl⟩ : syracuseStep 1307225 = 980419) B980419
theorem B1471115 : Blo 774336 1471115 := bstep (se 1 (by rfl) ⟨1103336, by rfl⟩ : syracuseStep 1471115 = 2206673) B2206673
theorem B1307353 : Blo 774336 1307353 := bstep (se 2 (by rfl) ⟨490257, by rfl⟩ : syracuseStep 1307353 = 980515) B980515
theorem B3142361 : Blo 774336 3142361 := bstep (se 2 (by rfl) ⟨1178385, by rfl⟩ : syracuseStep 3142361 = 2356771) B2356771
theorem B2945753 : Blo 774336 2945753 := bstep (se 2 (by rfl) ⟨1104657, by rfl⟩ : syracuseStep 2945753 = 2209315) B2209315
theorem B2618135 : Blo 774336 2618135 := bstep (se 1 (by rfl) ⟨1963601, by rfl⟩ : syracuseStep 2618135 = 3927203) B3927203
theorem B1471297 : Blo 774336 1471297 := bstep (se 2 (by rfl) ⟨551736, by rfl⟩ : syracuseStep 1471297 = 1103473) B1103473
theorem B2946071 : Blo 774336 2946071 := bstep (se 1 (by rfl) ⟨2209553, by rfl⟩ : syracuseStep 2946071 = 4419107) B4419107
theorem B2126999 : Blo 774336 2126999 := bstep (se 1 (by rfl) ⟨1595249, by rfl⟩ : syracuseStep 2126999 = 3190499) B3190499
theorem B1963187 : Blo 774336 1963187 := bstep (se 1 (by rfl) ⟨1472390, by rfl⟩ : syracuseStep 1963187 = 2944781) B2944781
theorem B1471745 : Blo 774336 1471745 := bstep (se 2 (by rfl) ⟨551904, by rfl⟩ : syracuseStep 1471745 = 1103809) B1103809
theorem B1307927 : Blo 774336 1307927 := bstep (se 1 (by rfl) ⟨980945, by rfl⟩ : syracuseStep 1307927 = 1961891) B1961891
theorem B2618675 : Blo 774336 2618675 := bstep (se 1 (by rfl) ⟨1964006, by rfl⟩ : syracuseStep 2618675 = 3928013) B3928013
theorem B980363 : Blo 774336 980363 := bstep (se 1 (by rfl) ⟨735272, by rfl⟩ : syracuseStep 980363 = 1470545) B1470545
theorem B1308055 : Blo 774336 1308055 := bstep (se 1 (by rfl) ⟨981041, by rfl⟩ : syracuseStep 1308055 = 1962083) B1962083
theorem B5600663 : Blo 774336 5600663 := bstep (se 1 (by rfl) ⟨4200497, by rfl⟩ : syracuseStep 5600663 = 8400995) B8400995
theorem B2487773 : Blo 774336 2487773 := bstep (se 3 (by rfl) ⟨466457, by rfl⟩ : syracuseStep 2487773 = 932915) B932915
theorem B2618945 : Blo 774336 2618945 := bstep (se 2 (by rfl) ⟨982104, by rfl⟩ : syracuseStep 2618945 = 1964209) B1964209
theorem B1472087 : Blo 774336 1472087 := bstep (se 1 (by rfl) ⟨1104065, by rfl⟩ : syracuseStep 1472087 = 2208131) B2208131
theorem B2946739 : Blo 774336 2946739 := bstep (se 1 (by rfl) ⟨2210054, by rfl⟩ : syracuseStep 2946739 = 4420109) B4420109
theorem B1963723 : Blo 774336 1963723 := bstep (se 1 (by rfl) ⟨1472792, by rfl⟩ : syracuseStep 1963723 = 2945585) B2945585
theorem B12613421 : Blo 774336 12613421 := bstep (se 3 (by rfl) ⟨2365016, by rfl⟩ : syracuseStep 12613421 = 4730033) B4730033
theorem B1767233 : Blo 774336 1767233 := bstep (se 2 (by rfl) ⟨662712, by rfl⟩ : syracuseStep 1767233 = 1325425) B1325425
theorem B3536729 : Blo 774336 3536729 := bstep (se 2 (by rfl) ⟨1326273, by rfl⟩ : syracuseStep 3536729 = 2652547) B2652547
theorem B1963865 : Blo 774336 1963865 := bstep (se 2 (by rfl) ⟨736449, by rfl⟩ : syracuseStep 1963865 = 1472899) B1472899
theorem B1996633 : Blo 774336 1996633 := bstep (se 2 (by rfl) ⟨748737, by rfl⟩ : syracuseStep 1996633 = 1497475) B1497475
theorem B1308683 : Blo 774336 1308683 := bstep (se 1 (by rfl) ⟨981512, by rfl⟩ : syracuseStep 1308683 = 1963025) B1963025
theorem B981067 : Blo 774336 981067 := bstep (se 1 (by rfl) ⟨735800, by rfl⟩ : syracuseStep 981067 = 1471601) B1471601
theorem B2619485 : Blo 774336 2619485 := bstep (se 3 (by rfl) ⟨491153, by rfl⟩ : syracuseStep 2619485 = 982307) B982307
theorem B1308811 : Blo 774336 1308811 := bstep (se 1 (by rfl) ⟨981608, by rfl⟩ : syracuseStep 1308811 = 1963217) B1963217
theorem B1570969 : Blo 774336 1570969 := bstep (se 2 (by rfl) ⟨589113, by rfl⟩ : syracuseStep 1570969 = 1178227) B1178227
theorem B1472755 : Blo 774336 1472755 := bstep (se 1 (by rfl) ⟨1104566, by rfl⟩ : syracuseStep 1472755 = 2209133) B2209133
theorem B1308953 : Blo 774336 1308953 := bstep (se 2 (by rfl) ⟨490857, by rfl⟩ : syracuseStep 1308953 = 981715) B981715
theorem B3930443 : Blo 774336 3930443 := bstep (se 1 (by rfl) ⟨2947832, by rfl⟩ : syracuseStep 3930443 = 5895665) B5895665
theorem B981335 : Blo 774336 981335 := bstep (se 1 (by rfl) ⟨736001, by rfl⟩ : syracuseStep 981335 = 1472003) B1472003
theorem B2881885 : Blo 774336 2881885 := bstep (se 3 (by rfl) ⟨540353, by rfl⟩ : syracuseStep 2881885 = 1080707) B1080707
theorem B8845685 : Blo 774336 8845685 := bstep (se 5 (by rfl) ⟨414641, by rfl⟩ : syracuseStep 8845685 = 829283) B829283
theorem B1046935 : Blo 774336 1046935 := bstep (se 1 (by rfl) ⟨785201, by rfl⟩ : syracuseStep 1046935 = 1570403) B1570403
theorem B1309081 : Blo 774336 1309081 := bstep (se 2 (by rfl) ⟨490905, by rfl⟩ : syracuseStep 1309081 = 981811) B981811
theorem B4422275 : Blo 774336 4422275 := bstep (se 1 (by rfl) ⟨3316706, by rfl⟩ : syracuseStep 4422275 = 6633413) B6633413
theorem B1964695 : Blo 774336 1964695 := bstep (se 1 (by rfl) ⟨1473521, by rfl⟩ : syracuseStep 1964695 = 2947043) B2947043
theorem B1473203 : Blo 774336 1473203 := bstep (se 1 (by rfl) ⟨1104902, by rfl⟩ : syracuseStep 1473203 = 2209805) B2209805
theorem B1473241 : Blo 774336 1473241 := bstep (se 2 (by rfl) ⟨552465, by rfl⟩ : syracuseStep 1473241 = 1104931) B1104931
theorem B23919461 : Blo 774336 23919461 := bstep (se 4 (by rfl) ⟨2242449, by rfl⟩ : syracuseStep 23919461 = 4484899) B4484899
theorem B2947985 : Blo 774336 2947985 := bstep (se 2 (by rfl) ⟨1105494, by rfl⟩ : syracuseStep 2947985 = 2210989) B2210989
theorem B1309655 : Blo 774336 1309655 := bstep (se 1 (by rfl) ⟨982241, by rfl⟩ : syracuseStep 1309655 = 1964483) B1964483
theorem B982039 : Blo 774336 982039 := bstep (se 1 (by rfl) ⟨736529, by rfl⟩ : syracuseStep 982039 = 1473059) B1473059
theorem B1965131 : Blo 774336 1965131 := bstep (se 1 (by rfl) ⟨1473848, by rfl⟩ : syracuseStep 1965131 = 2947697) B2947697
theorem B1309783 : Blo 774336 1309783 := bstep (se 1 (by rfl) ⟨982337, by rfl⟩ : syracuseStep 1309783 = 1964675) B1964675
theorem B1473689 : Blo 774336 1473689 := bstep (se 2 (by rfl) ⟨552633, by rfl⟩ : syracuseStep 1473689 = 1105267) B1105267
theorem B2620619 : Blo 774336 2620619 := bstep (se 1 (by rfl) ⟨1965464, by rfl⟩ : syracuseStep 2620619 = 3930929) B3930929
theorem B1965505 : Blo 774336 1965505 := bstep (se 2 (by rfl) ⟨737064, by rfl⟩ : syracuseStep 1965505 = 1474129) B1474129
theorem B2620889 : Blo 774336 2620889 := bstep (se 2 (by rfl) ⟨982833, by rfl⟩ : syracuseStep 2620889 = 1965667) B1965667
theorem B2948683 : Blo 774336 2948683 := bstep (se 1 (by rfl) ⟨2211512, by rfl⟩ : syracuseStep 2948683 = 4423025) B4423025
theorem B2358877 : Blo 774336 2358877 := bstep (se 3 (by rfl) ⟨442289, by rfl⟩ : syracuseStep 2358877 = 884579) B884579
theorem B1310411 : Blo 774336 1310411 := bstep (se 1 (by rfl) ⟨982808, by rfl⟩ : syracuseStep 1310411 = 1965617) B1965617
theorem B6618955 : Blo 774336 6618955 := bstep (se 1 (by rfl) ⟨4964216, by rfl⟩ : syracuseStep 6618955 = 9928433) B9928433
theorem B1310539 : Blo 774336 1310539 := bstep (se 1 (by rfl) ⟨982904, by rfl⟩ : syracuseStep 1310539 = 1965809) B1965809
theorem B2948957 : Blo 774336 2948957 := bstep (se 3 (by rfl) ⟨552929, by rfl⟩ : syracuseStep 2948957 = 1105859) B1105859
theorem B3735389 : Blo 774336 3735389 := bstep (se 3 (by rfl) ⟨700385, by rfl⟩ : syracuseStep 3735389 = 1400771) B1400771
theorem B1474433 : Blo 774336 1474433 := bstep (se 2 (by rfl) ⟨552912, by rfl⟩ : syracuseStep 1474433 = 1105825) B1105825
theorem B2097047 : Blo 774336 2097047 := bstep (se 1 (by rfl) ⟨1572785, by rfl⟩ : syracuseStep 2097047 = 3145571) B3145571
theorem B1310681 : Blo 774336 1310681 := bstep (se 2 (by rfl) ⟨491505, by rfl⟩ : syracuseStep 1310681 = 983011) B983011
theorem B1310735 : Blo 774336 1310735 := bstep (se 1 (by rfl) ⟨983051, by rfl⟩ : syracuseStep 1310735 = 1966103) B1966103
theorem B2621483 : Blo 774336 2621483 := bstep (se 1 (by rfl) ⟨1966112, by rfl⟩ : syracuseStep 2621483 = 3932225) B3932225
theorem B7471237 : Blo 774336 7471237 := bstep (se 4 (by rfl) ⟨700428, by rfl⟩ : syracuseStep 7471237 = 1400857) B1400857
theorem B1966265 : Blo 774336 1966265 := bstep (se 2 (by rfl) ⟨737349, by rfl⟩ : syracuseStep 1966265 = 1474699) B1474699
theorem B983431 : Blo 774336 983431 := bstep (se 1 (by rfl) ⟨737573, by rfl⟩ : syracuseStep 983431 = 1475147) B1475147
theorem B1311275 : Blo 774336 1311275 := bstep (se 1 (by rfl) ⟨983456, by rfl⟩ : syracuseStep 1311275 = 1966913) B1966913
theorem B1180217 : Blo 774336 1180217 := bstep (se 2 (by rfl) ⟨442581, by rfl⟩ : syracuseStep 1180217 = 885163) B885163
theorem B1573435 : Blo 774336 1573435 := bstep (se 1 (by rfl) ⟨1180076, by rfl⟩ : syracuseStep 1573435 = 2360153) B2360153
theorem B3932873 : Blo 774336 3932873 := bstep (se 2 (by rfl) ⟨1474827, by rfl⟩ : syracuseStep 3932873 = 2949655) B2949655
theorem B5309221 : Blo 774336 5309221 := bstep (se 4 (by rfl) ⟨497739, by rfl⟩ : syracuseStep 5309221 = 995479) B995479
theorem B1966963 : Blo 774336 1966963 := bstep (se 1 (by rfl) ⟨1475222, by rfl⟩ : syracuseStep 1966963 = 2950445) B2950445
theorem B983927 : Blo 774336 983927 := bstep (se 1 (by rfl) ⟨737945, by rfl⟩ : syracuseStep 983927 = 1475891) B1475891
theorem B1311673 : Blo 774336 1311673 := bstep (se 2 (by rfl) ⟨491877, by rfl⟩ : syracuseStep 1311673 = 983755) B983755
theorem B4031441 : Blo 774336 4031441 := bstep (se 2 (by rfl) ⟨1511790, by rfl⟩ : syracuseStep 4031441 = 3023581) B3023581
theorem B1967105 : Blo 774336 1967105 := bstep (se 2 (by rfl) ⟨737664, by rfl⟩ : syracuseStep 1967105 = 1475329) B1475329
theorem B984079 : Blo 774336 984079 := bstep (se 1 (by rfl) ⟨738059, by rfl⟩ : syracuseStep 984079 = 1476119) B1476119
theorem B984251 : Blo 774336 984251 := bstep (se 1 (by rfl) ⟨738188, by rfl⟩ : syracuseStep 984251 = 1476377) B1476377
theorem B2950415 : Blo 774336 2950415 := bstep (se 1 (by rfl) ⟨2212811, by rfl⟩ : syracuseStep 2950415 = 4425623) B4425623
theorem B5899553 : Blo 774336 5899553 := bstep (se 2 (by rfl) ⟨2212332, by rfl⟩ : syracuseStep 5899553 = 4424665) B4424665
theorem B2622779 : Blo 774336 2622779 := bstep (se 1 (by rfl) ⟨1967084, by rfl⟩ : syracuseStep 2622779 = 3934169) B3934169
theorem B1475975 : Blo 774336 1475975 := bstep (se 1 (by rfl) ⟨1106981, by rfl⟩ : syracuseStep 1475975 = 2213963) B2213963
theorem B1967561 : Blo 774336 1967561 := bstep (se 2 (by rfl) ⟨737835, by rfl⟩ : syracuseStep 1967561 = 1475671) B1475671
theorem B1312375 : Blo 774336 1312375 := bstep (se 1 (by rfl) ⟨984281, by rfl⟩ : syracuseStep 1312375 = 1968563) B1968563
theorem B4982465 : Blo 774336 4982465 := bstep (se 2 (by rfl) ⟨1868424, by rfl⟩ : syracuseStep 4982465 = 3736849) B3736849
theorem B7079653 : Blo 774336 7079653 := bstep (se 4 (by rfl) ⟨663717, by rfl⟩ : syracuseStep 7079653 = 1327435) B1327435
theorem B788239 : Blo 774336 788239 := bstep (se 1 (by rfl) ⟨591179, by rfl⟩ : syracuseStep 788239 = 1182359) B1182359
theorem B2623265 : Blo 774336 2623265 := bstep (se 2 (by rfl) ⟨983724, by rfl⟩ : syracuseStep 2623265 = 1967449) B1967449
theorem B1967915 : Blo 774336 1967915 := bstep (se 1 (by rfl) ⟨1475936, by rfl⟩ : syracuseStep 1967915 = 2951873) B2951873
theorem B1312571 : Blo 774336 1312571 := bstep (se 1 (by rfl) ⟨984428, by rfl⟩ : syracuseStep 1312571 = 1968857) B1968857
theorem B1869655 : Blo 774336 1869655 := bstep (se 1 (by rfl) ⟨1402241, by rfl⟩ : syracuseStep 1869655 = 2804483) B2804483
theorem B22644593 : Blo 774336 22644593 := bstep (se 2 (by rfl) ⟨8491722, by rfl⟩ : syracuseStep 22644593 = 16983445) B16983445
theorem B3311513 : Blo 774336 3311513 := bstep (se 2 (by rfl) ⟨1241817, by rfl⟩ : syracuseStep 3311513 = 2483635) B2483635
theorem B8390789 : Blo 774336 8390789 := bstep (se 4 (by rfl) ⟨786636, by rfl⟩ : syracuseStep 8390789 = 1573273) B1573273
theorem B1312969 : Blo 774336 1312969 := bstep (se 2 (by rfl) ⟨492363, by rfl⟩ : syracuseStep 1312969 = 984727) B984727
theorem B5900525 : Blo 774336 5900525 := bstep (se 3 (by rfl) ⟨1106348, by rfl⟩ : syracuseStep 5900525 = 2212697) B2212697
theorem B2623859 : Blo 774336 2623859 := bstep (se 1 (by rfl) ⟨1967894, by rfl⟩ : syracuseStep 2623859 = 3935789) B3935789
theorem B2099773 : Blo 774336 2099773 := bstep (se 3 (by rfl) ⟨393707, by rfl⟩ : syracuseStep 2099773 = 787415) B787415
theorem B1968907 : Blo 774336 1968907 := bstep (se 1 (by rfl) ⟨1476680, by rfl⟩ : syracuseStep 1968907 = 2953361) B2953361
theorem B2952071 : Blo 774336 2952071 := bstep (se 1 (by rfl) ⟨2214053, by rfl⟩ : syracuseStep 2952071 = 4428107) B4428107
theorem B4426649 : Blo 774336 4426649 := bstep (se 2 (by rfl) ⟨1659993, by rfl⟩ : syracuseStep 4426649 = 3319987) B3319987
theorem B1969049 : Blo 774336 1969049 := bstep (se 2 (by rfl) ⟨738393, by rfl⟩ : syracuseStep 1969049 = 1476787) B1476787
theorem B1477577 : Blo 774336 1477577 := bstep (se 2 (by rfl) ⟨554091, by rfl⟩ : syracuseStep 1477577 = 1108183) B1108183
theorem B1969211 : Blo 774336 1969211 := bstep (se 1 (by rfl) ⟨1476908, by rfl⟩ : syracuseStep 1969211 = 2953817) B2953817
theorem B1051849 : Blo 774336 1051849 := bstep (se 2 (by rfl) ⟨394443, by rfl⟩ : syracuseStep 1051849 = 788887) B788887
theorem B1969555 : Blo 774336 1969555 := bstep (se 1 (by rfl) ⟨1477166, by rfl⟩ : syracuseStep 1969555 = 2954333) B2954333
theorem B1969697 : Blo 774336 1969697 := bstep (se 2 (by rfl) ⟨738636, by rfl⟩ : syracuseStep 1969697 = 1477273) B1477273
theorem B14192435 : Blo 774336 14192435 := bstep (se 1 (by rfl) ⟨10644326, by rfl⟩ : syracuseStep 14192435 = 21288653) B21288653
theorem B5967731 : Blo 774336 5967731 := bstep (se 1 (by rfl) ⟨4475798, by rfl⟩ : syracuseStep 5967731 = 8951597) B8951597
theorem B2101277 : Blo 774336 2101277 := bstep (se 3 (by rfl) ⟨393989, by rfl⟩ : syracuseStep 2101277 = 787979) B787979
theorem B8851517 : Blo 774336 8851517 := bstep (se 3 (by rfl) ⟨1659659, by rfl⟩ : syracuseStep 8851517 = 3319319) B3319319
theorem B5902469 : Blo 774336 5902469 := bstep (se 4 (by rfl) ⟨553356, by rfl⟩ : syracuseStep 5902469 = 1106713) B1106713
theorem B37753073 : Blo 774336 37753073 := bstep (se 2 (by rfl) ⟨14157402, by rfl⟩ : syracuseStep 37753073 = 28314805) B28314805
theorem B2953847 : Blo 774336 2953847 := bstep (se 1 (by rfl) ⟨2215385, by rfl⟩ : syracuseStep 2953847 = 4430771) B4430771
theorem B4199201 : Blo 774336 4199201 := bstep (se 2 (by rfl) ⟨1574700, by rfl⟩ : syracuseStep 4199201 = 3149401) B3149401
theorem B31822627 : Blo 774336 31822627 := bstep (se 1 (by rfl) ⟨23866970, by rfl⟩ : syracuseStep 31822627 = 47733941) B47733941
theorem B10523429 : Blo 774336 10523429 := bstep (se 4 (by rfl) ⟨986571, by rfl⟩ : syracuseStep 10523429 = 1973143) B1973143
theorem B7443251 : Blo 774336 7443251 := bstep (se 1 (by rfl) ⟨5582438, by rfl⟩ : syracuseStep 7443251 = 11164877) B11164877
theorem B10064729 : Blo 774336 10064729 := bstep (se 2 (by rfl) ⟨3774273, by rfl⟩ : syracuseStep 10064729 = 7548547) B7548547
theorem B11932505 : Blo 774336 11932505 := bstep (se 2 (by rfl) ⟨4474689, by rfl⟩ : syracuseStep 11932505 = 8949379) B8949379
theorem B2626451 : Blo 774336 2626451 := bstep (se 1 (by rfl) ⟨1969838, by rfl⟩ : syracuseStep 2626451 = 3939677) B3939677
theorem B1119239 : Blo 774336 1119239 := bstep (se 1 (by rfl) ⟨839429, by rfl⟩ : syracuseStep 1119239 = 1678859) B1678859
theorem B272667779 : Blo 774336 272667779 := bstep (se 1 (by rfl) ⟨204500834, by rfl⟩ : syracuseStep 272667779 = 409001669) B409001669
theorem B3314945 : Blo 774336 3314945 := bstep (se 2 (by rfl) ⟨1243104, by rfl⟩ : syracuseStep 3314945 = 2486209) B2486209
theorem B2954819 : Blo 774336 2954819 := bstep (se 1 (by rfl) ⟨2216114, by rfl⟩ : syracuseStep 2954819 = 4432229) B4432229
theorem B1742471 : Blo 774336 1742471 := bstep (se 1 (by rfl) ⟨1306853, by rfl⟩ : syracuseStep 1742471 = 2613707) B2613707
theorem B1742651 : Blo 774336 1742651 := bstep (se 1 (by rfl) ⟨1306988, by rfl⟩ : syracuseStep 1742651 = 2613977) B2613977
theorem B2987929 : Blo 774336 2987929 := bstep (se 2 (by rfl) ⟨1120473, by rfl⟩ : syracuseStep 2987929 = 2240947) B2240947
theorem B1742777 : Blo 774336 1742777 := bstep (se 2 (by rfl) ⟨653541, by rfl⟩ : syracuseStep 1742777 = 1307083) B1307083
theorem B4429997 : Blo 774336 4429997 := bstep (se 3 (by rfl) ⟨830624, by rfl⟩ : syracuseStep 4429997 = 1661249) B1661249
theorem B1743119 : Blo 774336 1743119 := bstep (se 1 (by rfl) ⟨1307339, by rfl⟩ : syracuseStep 1743119 = 2614679) B2614679
theorem B1743137 : Blo 774336 1743137 := bstep (se 2 (by rfl) ⟨653676, by rfl⟩ : syracuseStep 1743137 = 1307353) B1307353
theorem B3938705 : Blo 774336 3938705 := bstep (se 2 (by rfl) ⟨1477014, by rfl⟩ : syracuseStep 3938705 = 2954029) B2954029
theorem B5970323 : Blo 774336 5970323 := bstep (se 1 (by rfl) ⟨4477742, by rfl⟩ : syracuseStep 5970323 = 8955485) B8955485
theorem B5904899 : Blo 774336 5904899 := bstep (se 1 (by rfl) ⟨4428674, by rfl⟩ : syracuseStep 5904899 = 8857349) B8857349
theorem B1743479 : Blo 774336 1743479 := bstep (se 1 (by rfl) ⟨1307609, by rfl⟩ : syracuseStep 1743479 = 2615219) B2615219
theorem B6626063 : Blo 774336 6626063 := bstep (se 1 (by rfl) ⟨4969547, by rfl⟩ : syracuseStep 6626063 = 9939095) B9939095
theorem B1743659 : Blo 774336 1743659 := bstep (se 1 (by rfl) ⟨1307744, by rfl⟩ : syracuseStep 1743659 = 2615489) B2615489
theorem B4201361 : Blo 774336 4201361 := bstep (se 2 (by rfl) ⟨1575510, by rfl⟩ : syracuseStep 4201361 = 3151021) B3151021
theorem B40410019 : Blo 774336 40410019 := bstep (se 1 (by rfl) ⟨30307514, by rfl⟩ : syracuseStep 40410019 = 60615029) B60615029
theorem B1744019 : Blo 774336 1744019 := bstep (se 1 (by rfl) ⟨1308014, by rfl⟩ : syracuseStep 1744019 = 2616029) B2616029
theorem B1744073 : Blo 774336 1744073 := bstep (se 2 (by rfl) ⟨654027, by rfl⟩ : syracuseStep 1744073 = 1308055) B1308055
theorem B111779131 : Blo 774336 111779131 := bstep (se 1 (by rfl) ⟨83834348, by rfl⟩ : syracuseStep 111779131 = 167668697) B167668697
theorem B1744775 : Blo 774336 1744775 := bstep (se 1 (by rfl) ⟨1308581, by rfl⟩ : syracuseStep 1744775 = 2617163) B2617163
theorem B1744955 : Blo 774336 1744955 := bstep (se 1 (by rfl) ⟨1308716, by rfl⟩ : syracuseStep 1744955 = 2617433) B2617433
theorem B1745081 : Blo 774336 1745081 := bstep (se 2 (by rfl) ⟨654405, by rfl⟩ : syracuseStep 1745081 = 1308811) B1308811
theorem B1122761 : Blo 774336 1122761 := bstep (se 2 (by rfl) ⟨421035, by rfl⟩ : syracuseStep 1122761 = 842071) B842071
theorem B3842513 : Blo 774336 3842513 := bstep (se 2 (by rfl) ⟨1440942, by rfl⟩ : syracuseStep 3842513 = 2881885) B2881885
theorem B1745423 : Blo 774336 1745423 := bstep (se 1 (by rfl) ⟨1309067, by rfl⟩ : syracuseStep 1745423 = 2618135) B2618135
theorem B1745441 : Blo 774336 1745441 := bstep (se 2 (by rfl) ⟨654540, by rfl⟩ : syracuseStep 1745441 = 1309081) B1309081
theorem B1417999 : Blo 774336 1417999 := bstep (se 1 (by rfl) ⟨1063499, by rfl⟩ : syracuseStep 1417999 = 2126999) B2126999
theorem B4203353 : Blo 774336 4203353 := bstep (se 2 (by rfl) ⟨1576257, by rfl⟩ : syracuseStep 4203353 = 3152515) B3152515
theorem B1745783 : Blo 774336 1745783 := bstep (se 1 (by rfl) ⟨1309337, by rfl⟩ : syracuseStep 1745783 = 2618675) B2618675
theorem B4727699 : Blo 774336 4727699 := bstep (se 1 (by rfl) ⟨3545774, by rfl⟩ : syracuseStep 4727699 = 7091549) B7091549
theorem B1745963 : Blo 774336 1745963 := bstep (se 1 (by rfl) ⟨1309472, by rfl⟩ : syracuseStep 1745963 = 2618945) B2618945
theorem B9970775 : Blo 774336 9970775 := bstep (se 1 (by rfl) ⟨7478081, by rfl⟩ : syracuseStep 9970775 = 14956163) B14956163
theorem B1746323 : Blo 774336 1746323 := bstep (se 1 (by rfl) ⟨1309742, by rfl⟩ : syracuseStep 1746323 = 2619485) B2619485
theorem B1746377 : Blo 774336 1746377 := bstep (se 2 (by rfl) ⟨654891, by rfl⟩ : syracuseStep 1746377 = 1309783) B1309783
theorem B10758041 : Blo 774336 10758041 := bstep (se 2 (by rfl) ⟨4034265, by rfl⟩ : syracuseStep 10758041 = 8068531) B8068531
theorem B20195351 : Blo 774336 20195351 := bstep (se 1 (by rfl) ⟨15146513, by rfl⟩ : syracuseStep 20195351 = 30293027) B30293027
theorem B1747079 : Blo 774336 1747079 := bstep (se 1 (by rfl) ⟨1310309, by rfl⟩ : syracuseStep 1747079 = 2620619) B2620619
theorem B1747259 : Blo 774336 1747259 := bstep (se 1 (by rfl) ⟨1310444, by rfl⟩ : syracuseStep 1747259 = 2620889) B2620889
theorem B8825273 : Blo 774336 8825273 := bstep (se 2 (by rfl) ⟨3309477, by rfl⟩ : syracuseStep 8825273 = 6618955) B6618955
theorem B1747385 : Blo 774336 1747385 := bstep (se 2 (by rfl) ⟨655269, by rfl⟩ : syracuseStep 1747385 = 1310539) B1310539
theorem B1747727 : Blo 774336 1747727 := bstep (se 1 (by rfl) ⟨1310795, by rfl⟩ : syracuseStep 1747727 = 2621591) B2621591
theorem B1747745 : Blo 774336 1747745 := bstep (se 2 (by rfl) ⟨655404, by rfl⟩ : syracuseStep 1747745 = 1310809) B1310809
theorem B14560181 : Blo 774336 14560181 := bstep (se 5 (by rfl) ⟨682508, by rfl⟩ : syracuseStep 14560181 = 1365017) B1365017
theorem B1748087 : Blo 774336 1748087 := bstep (se 1 (by rfl) ⟨1311065, by rfl⟩ : syracuseStep 1748087 = 2622131) B2622131
theorem B1748267 : Blo 774336 1748267 := bstep (se 1 (by rfl) ⟨1311200, by rfl⟩ : syracuseStep 1748267 = 2622401) B2622401
theorem B16166279 : Blo 774336 16166279 := bstep (se 1 (by rfl) ⟨12124709, by rfl⟩ : syracuseStep 16166279 = 24249419) B24249419
theorem B830855 : Blo 774336 830855 := bstep (se 1 (by rfl) ⟨623141, by rfl⟩ : syracuseStep 830855 = 1246283) B1246283
theorem B1748627 : Blo 774336 1748627 := bstep (se 1 (by rfl) ⟨1311470, by rfl⟩ : syracuseStep 1748627 = 2622941) B2622941
theorem B7450289 : Blo 774336 7450289 := bstep (se 2 (by rfl) ⟨2793858, by rfl⟩ : syracuseStep 7450289 = 5587717) B5587717
theorem B1748681 : Blo 774336 1748681 := bstep (se 2 (by rfl) ⟨655755, by rfl⟩ : syracuseStep 1748681 = 1311511) B1311511
theorem B5910245 : Blo 774336 5910245 := bstep (se 4 (by rfl) ⟨554085, by rfl⟩ : syracuseStep 5910245 = 1108171) B1108171
theorem B2207503 : Blo 774336 2207503 := bstep (se 1 (by rfl) ⟨1655627, by rfl⟩ : syracuseStep 2207503 = 3311255) B3311255
theorem B2207549 : Blo 774336 2207549 := bstep (se 3 (by rfl) ⟨413915, by rfl⟩ : syracuseStep 2207549 = 827831) B827831
theorem B3321917 : Blo 774336 3321917 := bstep (se 3 (by rfl) ⟨622859, by rfl⟩ : syracuseStep 3321917 = 1245719) B1245719
theorem B2240627 : Blo 774336 2240627 := bstep (se 1 (by rfl) ⟨1680470, by rfl⟩ : syracuseStep 2240627 = 3360941) B3360941
theorem B2207891 : Blo 774336 2207891 := bstep (se 1 (by rfl) ⟨1655918, by rfl⟩ : syracuseStep 2207891 = 3311837) B3311837
theorem B1749383 : Blo 774336 1749383 := bstep (se 1 (by rfl) ⟨1312037, by rfl⟩ : syracuseStep 1749383 = 2624075) B2624075
theorem B3322259 : Blo 774336 3322259 := bstep (se 1 (by rfl) ⟨2491694, by rfl⟩ : syracuseStep 3322259 = 4983389) B4983389
theorem B995771 : Blo 774336 995771 := bstep (se 1 (by rfl) ⟨746828, by rfl⟩ : syracuseStep 995771 = 1493657) B1493657
theorem B1749563 : Blo 774336 1749563 := bstep (se 1 (by rfl) ⟨1312172, by rfl⟩ : syracuseStep 1749563 = 2624345) B2624345
theorem B1749689 : Blo 774336 1749689 := bstep (se 2 (by rfl) ⟨656133, by rfl⟩ : syracuseStep 1749689 = 1312267) B1312267
theorem B5583653 : Blo 774336 5583653 := bstep (se 4 (by rfl) ⟨523467, by rfl⟩ : syracuseStep 5583653 = 1046935) B1046935
theorem B4731763 : Blo 774336 4731763 := bstep (se 1 (by rfl) ⟨3548822, by rfl⟩ : syracuseStep 4731763 = 7097645) B7097645
theorem B930695 : Blo 774336 930695 := bstep (se 1 (by rfl) ⟨698021, by rfl⟩ : syracuseStep 930695 = 1396043) B1396043
theorem B2241433 : Blo 774336 2241433 := bstep (se 2 (by rfl) ⟨840537, by rfl⟩ : syracuseStep 2241433 = 1681075) B1681075
theorem B2208779 : Blo 774336 2208779 := bstep (se 1 (by rfl) ⟨1656584, by rfl⟩ : syracuseStep 2208779 = 3313169) B3313169
theorem B1750031 : Blo 774336 1750031 := bstep (se 1 (by rfl) ⟨1312523, by rfl⟩ : syracuseStep 1750031 = 2625047) B2625047
theorem B1750049 : Blo 774336 1750049 := bstep (se 2 (by rfl) ⟨656268, by rfl⟩ : syracuseStep 1750049 = 1312537) B1312537
theorem B7091333 : Blo 774336 7091333 := bstep (se 4 (by rfl) ⟨664812, by rfl⟩ : syracuseStep 7091333 = 1329625) B1329625
theorem B14890189 : Blo 774336 14890189 := bstep (se 3 (by rfl) ⟨2791910, by rfl⟩ : syracuseStep 14890189 = 5583821) B5583821
theorem B996727 : Blo 774336 996727 := bstep (se 1 (by rfl) ⟨747545, by rfl⟩ : syracuseStep 996727 = 1495091) B1495091
theorem B1750391 : Blo 774336 1750391 := bstep (se 1 (by rfl) ⟨1312793, by rfl⟩ : syracuseStep 1750391 = 2625587) B2625587
theorem B1750571 : Blo 774336 1750571 := bstep (se 1 (by rfl) ⟨1312928, by rfl⟩ : syracuseStep 1750571 = 2625857) B2625857
theorem B1324603 : Blo 774336 1324603 := bstep (se 1 (by rfl) ⟨993452, by rfl⟩ : syracuseStep 1324603 = 1986905) B1986905
theorem B931387 : Blo 774336 931387 := bstep (se 1 (by rfl) ⟨698540, by rfl⟩ : syracuseStep 931387 = 1397081) B1397081
theorem B12596813 : Blo 774336 12596813 := bstep (se 3 (by rfl) ⟨2361902, by rfl⟩ : syracuseStep 12596813 = 4723805) B4723805
theorem B1750931 : Blo 774336 1750931 := bstep (se 1 (by rfl) ⟨1313198, by rfl⟩ : syracuseStep 1750931 = 2626397) B2626397
theorem B1750985 : Blo 774336 1750985 := bstep (se 2 (by rfl) ⟨656619, by rfl⟩ : syracuseStep 1750985 = 1313239) B1313239
theorem B2275361 : Blo 774336 2275361 := bstep (se 2 (by rfl) ⟨853260, by rfl⟩ : syracuseStep 2275361 = 1706521) B1706521
theorem B997547 : Blo 774336 997547 := bstep (se 1 (by rfl) ⟨748160, by rfl⟩ : syracuseStep 997547 = 1496321) B1496321
theorem B1161515 : Blo 774336 1161515 := bstep (se 1 (by rfl) ⟨871136, by rfl⟩ : syracuseStep 1161515 = 1742273) B1742273
theorem B1161545 : Blo 774336 1161545 := bstep (se 2 (by rfl) ⟨435579, by rfl⟩ : syracuseStep 1161545 = 871159) B871159
theorem B1161659 : Blo 774336 1161659 := bstep (se 1 (by rfl) ⟨871244, by rfl⟩ : syracuseStep 1161659 = 1742489) B1742489
theorem B1161719 : Blo 774336 1161719 := bstep (se 1 (by rfl) ⟨871289, by rfl⟩ : syracuseStep 1161719 = 1742579) B1742579
theorem B1161743 : Blo 774336 1161743 := bstep (se 1 (by rfl) ⟨871307, by rfl⟩ : syracuseStep 1161743 = 1742615) B1742615
theorem B1161785 : Blo 774336 1161785 := bstep (se 2 (by rfl) ⟨435669, by rfl⟩ : syracuseStep 1161785 = 871339) B871339
theorem B6634061 : Blo 774336 6634061 := bstep (se 3 (by rfl) ⟨1243886, by rfl⟩ : syracuseStep 6634061 = 2487773) B2487773
theorem B2210419 : Blo 774336 2210419 := bstep (se 1 (by rfl) ⟨1657814, by rfl⟩ : syracuseStep 2210419 = 3315629) B3315629
theorem B1161863 : Blo 774336 1161863 := bstep (se 1 (by rfl) ⟨871397, by rfl⟩ : syracuseStep 1161863 = 1742795) B1742795
theorem B1161899 : Blo 774336 1161899 := bstep (se 1 (by rfl) ⟨871424, by rfl⟩ : syracuseStep 1161899 = 1742849) B1742849
theorem B1161929 : Blo 774336 1161929 := bstep (se 2 (by rfl) ⟨435723, by rfl⟩ : syracuseStep 1161929 = 871447) B871447
theorem B4733711 : Blo 774336 4733711 := bstep (se 1 (by rfl) ⟨3550283, by rfl⟩ : syracuseStep 4733711 = 7100567) B7100567
theorem B1162043 : Blo 774336 1162043 := bstep (se 1 (by rfl) ⟨871532, by rfl⟩ : syracuseStep 1162043 = 1743065) B1743065
theorem B2210647 : Blo 774336 2210647 := bstep (se 1 (by rfl) ⟨1657985, by rfl⟩ : syracuseStep 2210647 = 3315971) B3315971
theorem B1162103 : Blo 774336 1162103 := bstep (se 1 (by rfl) ⟨871577, by rfl⟩ : syracuseStep 1162103 = 1743155) B1743155
theorem B1162127 : Blo 774336 1162127 := bstep (se 1 (by rfl) ⟨871595, by rfl⟩ : syracuseStep 1162127 = 1743191) B1743191
theorem B1162169 : Blo 774336 1162169 := bstep (se 2 (by rfl) ⟨435813, by rfl⟩ : syracuseStep 1162169 = 871627) B871627
theorem B1162247 : Blo 774336 1162247 := bstep (se 1 (by rfl) ⟨871685, by rfl⟩ : syracuseStep 1162247 = 1743371) B1743371
theorem B1162283 : Blo 774336 1162283 := bstep (se 1 (by rfl) ⟨871712, by rfl⟩ : syracuseStep 1162283 = 1743425) B1743425
theorem B1162313 : Blo 774336 1162313 := bstep (se 2 (by rfl) ⟨435867, by rfl⟩ : syracuseStep 1162313 = 871735) B871735
theorem B3980461 : Blo 774336 3980461 := bstep (se 3 (by rfl) ⟨746336, by rfl⟩ : syracuseStep 3980461 = 1492673) B1492673
theorem B1162427 : Blo 774336 1162427 := bstep (se 1 (by rfl) ⟨871820, by rfl⟩ : syracuseStep 1162427 = 1743641) B1743641
theorem B1162487 : Blo 774336 1162487 := bstep (se 1 (by rfl) ⟨871865, by rfl⟩ : syracuseStep 1162487 = 1743731) B1743731
theorem B1162511 : Blo 774336 1162511 := bstep (se 1 (by rfl) ⟨871883, by rfl⟩ : syracuseStep 1162511 = 1743767) B1743767
theorem B1162553 : Blo 774336 1162553 := bstep (se 2 (by rfl) ⟨435957, by rfl⟩ : syracuseStep 1162553 = 871915) B871915
theorem B6634811 : Blo 774336 6634811 := bstep (se 1 (by rfl) ⟨4976108, by rfl⟩ : syracuseStep 6634811 = 9952217) B9952217
theorem B1162631 : Blo 774336 1162631 := bstep (se 1 (by rfl) ⟨871973, by rfl⟩ : syracuseStep 1162631 = 1743947) B1743947
theorem B1162667 : Blo 774336 1162667 := bstep (se 1 (by rfl) ⟨872000, by rfl⟩ : syracuseStep 1162667 = 1744001) B1744001
theorem B2801081 : Blo 774336 2801081 := bstep (se 2 (by rfl) ⟨1050405, by rfl⟩ : syracuseStep 2801081 = 2100811) B2100811
theorem B1162697 : Blo 774336 1162697 := bstep (se 2 (by rfl) ⟨436011, by rfl⟩ : syracuseStep 1162697 = 872023) B872023
theorem B8863181 : Blo 774336 8863181 := bstep (se 3 (by rfl) ⟨1661846, by rfl⟩ : syracuseStep 8863181 = 3323693) B3323693
theorem B1162811 : Blo 774336 1162811 := bstep (se 1 (by rfl) ⟨872108, by rfl⟩ : syracuseStep 1162811 = 1744217) B1744217
theorem B1162871 : Blo 774336 1162871 := bstep (se 1 (by rfl) ⟨872153, by rfl⟩ : syracuseStep 1162871 = 1744307) B1744307
theorem B1162895 : Blo 774336 1162895 := bstep (se 1 (by rfl) ⟨872171, by rfl⟩ : syracuseStep 1162895 = 1744343) B1744343
theorem B1162937 : Blo 774336 1162937 := bstep (se 2 (by rfl) ⟨436101, by rfl⟩ : syracuseStep 1162937 = 872203) B872203
theorem B1163015 : Blo 774336 1163015 := bstep (se 1 (by rfl) ⟨872261, by rfl⟩ : syracuseStep 1163015 = 1744523) B1744523
theorem B1163051 : Blo 774336 1163051 := bstep (se 1 (by rfl) ⟨872288, by rfl⟩ : syracuseStep 1163051 = 1744577) B1744577
theorem B1294123 : Blo 774336 1294123 := bstep (se 1 (by rfl) ⟨970592, by rfl⟩ : syracuseStep 1294123 = 1941185) B1941185
theorem B1163081 : Blo 774336 1163081 := bstep (se 2 (by rfl) ⟨436155, by rfl⟩ : syracuseStep 1163081 = 872311) B872311
theorem B933751 : Blo 774336 933751 := bstep (se 1 (by rfl) ⟨700313, by rfl⟩ : syracuseStep 933751 = 1400627) B1400627
theorem B1654663 : Blo 774336 1654663 := bstep (se 1 (by rfl) ⟨1240997, by rfl⟩ : syracuseStep 1654663 = 2481995) B2481995
theorem B1163195 : Blo 774336 1163195 := bstep (se 1 (by rfl) ⟨872396, by rfl⟩ : syracuseStep 1163195 = 1744793) B1744793
theorem B1163255 : Blo 774336 1163255 := bstep (se 1 (by rfl) ⟨872441, by rfl⟩ : syracuseStep 1163255 = 1744883) B1744883
theorem B1163279 : Blo 774336 1163279 := bstep (se 1 (by rfl) ⟨872459, by rfl⟩ : syracuseStep 1163279 = 1744919) B1744919
theorem B1163321 : Blo 774336 1163321 := bstep (se 2 (by rfl) ⟨436245, by rfl⟩ : syracuseStep 1163321 = 872491) B872491
theorem B1163399 : Blo 774336 1163399 := bstep (se 1 (by rfl) ⟨872549, by rfl⟩ : syracuseStep 1163399 = 1745099) B1745099
theorem B1163435 : Blo 774336 1163435 := bstep (se 1 (by rfl) ⟨872576, by rfl⟩ : syracuseStep 1163435 = 1745153) B1745153
theorem B5882057 : Blo 774336 5882057 := bstep (se 2 (by rfl) ⟨2205771, by rfl⟩ : syracuseStep 5882057 = 4411543) B4411543
theorem B1163465 : Blo 774336 1163465 := bstep (se 2 (by rfl) ⟨436299, by rfl⟩ : syracuseStep 1163465 = 872599) B872599
theorem B1163579 : Blo 774336 1163579 := bstep (se 1 (by rfl) ⟨872684, by rfl⟩ : syracuseStep 1163579 = 1745369) B1745369
theorem B1163639 : Blo 774336 1163639 := bstep (se 1 (by rfl) ⟨872729, by rfl⟩ : syracuseStep 1163639 = 1745459) B1745459
theorem B2212231 : Blo 774336 2212231 := bstep (se 1 (by rfl) ⟨1659173, by rfl⟩ : syracuseStep 2212231 = 3318347) B3318347
theorem B1163663 : Blo 774336 1163663 := bstep (se 1 (by rfl) ⟨872747, by rfl⟩ : syracuseStep 1163663 = 1745495) B1745495
theorem B1163705 : Blo 774336 1163705 := bstep (se 2 (by rfl) ⟨436389, by rfl⟩ : syracuseStep 1163705 = 872779) B872779
theorem B1163783 : Blo 774336 1163783 := bstep (se 1 (by rfl) ⟨872837, by rfl⟩ : syracuseStep 1163783 = 1745675) B1745675
theorem B1163819 : Blo 774336 1163819 := bstep (se 1 (by rfl) ⟨872864, by rfl⟩ : syracuseStep 1163819 = 1745729) B1745729
theorem B1163849 : Blo 774336 1163849 := bstep (se 2 (by rfl) ⟨436443, by rfl⟩ : syracuseStep 1163849 = 872887) B872887
theorem B2212505 : Blo 774336 2212505 := bstep (se 2 (by rfl) ⟨829689, by rfl⟩ : syracuseStep 2212505 = 1659379) B1659379
theorem B1163963 : Blo 774336 1163963 := bstep (se 1 (by rfl) ⟨872972, by rfl⟩ : syracuseStep 1163963 = 1745945) B1745945
theorem B8372929 : Blo 774336 8372929 := bstep (se 2 (by rfl) ⟨3139848, by rfl⟩ : syracuseStep 8372929 = 6279697) B6279697
theorem B1164023 : Blo 774336 1164023 := bstep (se 1 (by rfl) ⟨873017, by rfl⟩ : syracuseStep 1164023 = 1746035) B1746035
theorem B1164047 : Blo 774336 1164047 := bstep (se 1 (by rfl) ⟨873035, by rfl⟩ : syracuseStep 1164047 = 1746071) B1746071
theorem B1164089 : Blo 774336 1164089 := bstep (se 2 (by rfl) ⟨436533, by rfl⟩ : syracuseStep 1164089 = 873067) B873067
theorem B1164167 : Blo 774336 1164167 := bstep (se 1 (by rfl) ⟨873125, by rfl⟩ : syracuseStep 1164167 = 1746251) B1746251
theorem B6636451 : Blo 774336 6636451 := bstep (se 1 (by rfl) ⟨4977338, by rfl⟩ : syracuseStep 6636451 = 9954677) B9954677
theorem B1164203 : Blo 774336 1164203 := bstep (se 1 (by rfl) ⟨873152, by rfl⟩ : syracuseStep 1164203 = 1746305) B1746305
theorem B1164233 : Blo 774336 1164233 := bstep (se 2 (by rfl) ⟨436587, by rfl⟩ : syracuseStep 1164233 = 873175) B873175
theorem B1164347 : Blo 774336 1164347 := bstep (se 1 (by rfl) ⟨873260, by rfl⟩ : syracuseStep 1164347 = 1746521) B1746521
theorem B1164407 : Blo 774336 1164407 := bstep (se 1 (by rfl) ⟨873305, by rfl⟩ : syracuseStep 1164407 = 1746611) B1746611
theorem B1164431 : Blo 774336 1164431 := bstep (se 1 (by rfl) ⟨873323, by rfl⟩ : syracuseStep 1164431 = 1746647) B1746647
theorem B1197227 : Blo 774336 1197227 := bstep (se 1 (by rfl) ⟨897920, by rfl⟩ : syracuseStep 1197227 = 1795841) B1795841
theorem B1164473 : Blo 774336 1164473 := bstep (se 2 (by rfl) ⟨436677, by rfl⟩ : syracuseStep 1164473 = 873355) B873355
theorem B1164551 : Blo 774336 1164551 := bstep (se 1 (by rfl) ⟨873413, by rfl⟩ : syracuseStep 1164551 = 1746827) B1746827
theorem B2213153 : Blo 774336 2213153 := bstep (se 2 (by rfl) ⟨829932, by rfl⟩ : syracuseStep 2213153 = 1659865) B1659865
theorem B1164587 : Blo 774336 1164587 := bstep (se 1 (by rfl) ⟨873440, by rfl⟩ : syracuseStep 1164587 = 1746881) B1746881
theorem B1164617 : Blo 774336 1164617 := bstep (se 2 (by rfl) ⟨436731, by rfl⟩ : syracuseStep 1164617 = 873463) B873463
theorem B1164731 : Blo 774336 1164731 := bstep (se 1 (by rfl) ⟨873548, by rfl⟩ : syracuseStep 1164731 = 1747097) B1747097
theorem B1164791 : Blo 774336 1164791 := bstep (se 1 (by rfl) ⟨873593, by rfl⟩ : syracuseStep 1164791 = 1747187) B1747187
theorem B1164815 : Blo 774336 1164815 := bstep (se 1 (by rfl) ⟨873611, by rfl⟩ : syracuseStep 1164815 = 1747223) B1747223
theorem B1164857 : Blo 774336 1164857 := bstep (se 2 (by rfl) ⟨436821, by rfl⟩ : syracuseStep 1164857 = 873643) B873643
theorem B1656379 : Blo 774336 1656379 := bstep (se 1 (by rfl) ⟨1242284, by rfl⟩ : syracuseStep 1656379 = 2484569) B2484569
theorem B1164935 : Blo 774336 1164935 := bstep (se 1 (by rfl) ⟨873701, by rfl⟩ : syracuseStep 1164935 = 1747403) B1747403
theorem B1164971 : Blo 774336 1164971 := bstep (se 1 (by rfl) ⟨873728, by rfl⟩ : syracuseStep 1164971 = 1747457) B1747457
theorem B1165001 : Blo 774336 1165001 := bstep (se 2 (by rfl) ⟨436875, by rfl⟩ : syracuseStep 1165001 = 873751) B873751
theorem B1165115 : Blo 774336 1165115 := bstep (se 1 (by rfl) ⟨873836, by rfl⟩ : syracuseStep 1165115 = 1747673) B1747673
theorem B1165175 : Blo 774336 1165175 := bstep (se 1 (by rfl) ⟨873881, by rfl⟩ : syracuseStep 1165175 = 1747763) B1747763
theorem B1165199 : Blo 774336 1165199 := bstep (se 1 (by rfl) ⟨873899, by rfl⟩ : syracuseStep 1165199 = 1747799) B1747799
theorem B1165241 : Blo 774336 1165241 := bstep (se 2 (by rfl) ⟨436965, by rfl⟩ : syracuseStep 1165241 = 873931) B873931
theorem B1165319 : Blo 774336 1165319 := bstep (se 1 (by rfl) ⟨873989, by rfl⟩ : syracuseStep 1165319 = 1747979) B1747979
theorem B1656875 : Blo 774336 1656875 := bstep (se 1 (by rfl) ⟨1242656, by rfl⟩ : syracuseStep 1656875 = 2485313) B2485313
theorem B1165355 : Blo 774336 1165355 := bstep (se 1 (by rfl) ⟨874016, by rfl⟩ : syracuseStep 1165355 = 1748033) B1748033
theorem B1165385 : Blo 774336 1165385 := bstep (se 2 (by rfl) ⟨437019, by rfl⟩ : syracuseStep 1165385 = 874039) B874039
theorem B7260293 : Blo 774336 7260293 := bstep (se 4 (by rfl) ⟨680652, by rfl⟩ : syracuseStep 7260293 = 1361305) B1361305
theorem B1165499 : Blo 774336 1165499 := bstep (se 1 (by rfl) ⟨874124, by rfl⟩ : syracuseStep 1165499 = 1748249) B1748249
theorem B1165559 : Blo 774336 1165559 := bstep (se 1 (by rfl) ⟨874169, by rfl⟩ : syracuseStep 1165559 = 1748339) B1748339
theorem B2214155 : Blo 774336 2214155 := bstep (se 1 (by rfl) ⟨1660616, by rfl⟩ : syracuseStep 2214155 = 3321233) B3321233
theorem B1165583 : Blo 774336 1165583 := bstep (se 1 (by rfl) ⟨874187, by rfl⟩ : syracuseStep 1165583 = 1748375) B1748375
theorem B1165625 : Blo 774336 1165625 := bstep (se 2 (by rfl) ⟨437109, by rfl⟩ : syracuseStep 1165625 = 874219) B874219
theorem B1165703 : Blo 774336 1165703 := bstep (se 1 (by rfl) ⟨874277, by rfl⟩ : syracuseStep 1165703 = 1748555) B1748555
theorem B1165739 : Blo 774336 1165739 := bstep (se 1 (by rfl) ⟨874304, by rfl⟩ : syracuseStep 1165739 = 1748609) B1748609
theorem B1165769 : Blo 774336 1165769 := bstep (se 2 (by rfl) ⟨437163, by rfl⟩ : syracuseStep 1165769 = 874327) B874327
theorem B1165883 : Blo 774336 1165883 := bstep (se 1 (by rfl) ⟨874412, by rfl⟩ : syracuseStep 1165883 = 1748825) B1748825
theorem B1165943 : Blo 774336 1165943 := bstep (se 1 (by rfl) ⟨874457, by rfl⟩ : syracuseStep 1165943 = 1748915) B1748915
theorem B1165967 : Blo 774336 1165967 := bstep (se 1 (by rfl) ⟨874475, by rfl⟩ : syracuseStep 1165967 = 1748951) B1748951
theorem B1166009 : Blo 774336 1166009 := bstep (se 2 (by rfl) ⟨437253, by rfl⟩ : syracuseStep 1166009 = 874507) B874507
theorem B1166087 : Blo 774336 1166087 := bstep (se 1 (by rfl) ⟨874565, by rfl⟩ : syracuseStep 1166087 = 1749131) B1749131
theorem B1166123 : Blo 774336 1166123 := bstep (se 1 (by rfl) ⟨874592, by rfl⟩ : syracuseStep 1166123 = 1749185) B1749185
theorem B1166153 : Blo 774336 1166153 := bstep (se 2 (by rfl) ⟨437307, by rfl⟩ : syracuseStep 1166153 = 874615) B874615
theorem B871303 : Blo 774336 871303 := bstep (se 1 (by rfl) ⟨653477, by rfl⟩ : syracuseStep 871303 = 1306955) B1306955
theorem B1166267 : Blo 774336 1166267 := bstep (se 1 (by rfl) ⟨874700, by rfl⟩ : syracuseStep 1166267 = 1749401) B1749401
theorem B1166327 : Blo 774336 1166327 := bstep (se 1 (by rfl) ⟨874745, by rfl⟩ : syracuseStep 1166327 = 1749491) B1749491
theorem B1166351 : Blo 774336 1166351 := bstep (se 1 (by rfl) ⟨874763, by rfl⟩ : syracuseStep 1166351 = 1749527) B1749527
theorem B1166393 : Blo 774336 1166393 := bstep (se 2 (by rfl) ⟨437397, by rfl⟩ : syracuseStep 1166393 = 874795) B874795
theorem B871483 : Blo 774336 871483 := bstep (se 1 (by rfl) ⟨653612, by rfl⟩ : syracuseStep 871483 = 1307225) B1307225
theorem B1166471 : Blo 774336 1166471 := bstep (se 1 (by rfl) ⟨874853, by rfl⟩ : syracuseStep 1166471 = 1749707) B1749707
theorem B1166507 : Blo 774336 1166507 := bstep (se 1 (by rfl) ⟨874880, by rfl⟩ : syracuseStep 1166507 = 1749761) B1749761
theorem B1166537 : Blo 774336 1166537 := bstep (se 2 (by rfl) ⟨437451, by rfl⟩ : syracuseStep 1166537 = 874903) B874903
theorem B1166651 : Blo 774336 1166651 := bstep (se 1 (by rfl) ⟨874988, by rfl⟩ : syracuseStep 1166651 = 1749977) B1749977
theorem B1166711 : Blo 774336 1166711 := bstep (se 1 (by rfl) ⟨875033, by rfl⟩ : syracuseStep 1166711 = 1750067) B1750067
theorem B1166735 : Blo 774336 1166735 := bstep (se 1 (by rfl) ⟨875051, by rfl⟩ : syracuseStep 1166735 = 1750103) B1750103
theorem B1166777 : Blo 774336 1166777 := bstep (se 2 (by rfl) ⟨437541, by rfl⟩ : syracuseStep 1166777 = 875083) B875083
theorem B1166855 : Blo 774336 1166855 := bstep (se 1 (by rfl) ⟨875141, by rfl⟩ : syracuseStep 1166855 = 1750283) B1750283
theorem B3198475 : Blo 774336 3198475 := bstep (se 1 (by rfl) ⟨2398856, by rfl⟩ : syracuseStep 3198475 = 4797713) B4797713
theorem B871951 : Blo 774336 871951 := bstep (se 1 (by rfl) ⟨653963, by rfl⟩ : syracuseStep 871951 = 1307927) B1307927
theorem B1166891 : Blo 774336 1166891 := bstep (se 1 (by rfl) ⟨875168, by rfl⟩ : syracuseStep 1166891 = 1750337) B1750337
theorem B1166921 : Blo 774336 1166921 := bstep (se 2 (by rfl) ⟨437595, by rfl⟩ : syracuseStep 1166921 = 875191) B875191
theorem B1167035 : Blo 774336 1167035 := bstep (se 1 (by rfl) ⟨875276, by rfl⟩ : syracuseStep 1167035 = 1750553) B1750553
theorem B1167095 : Blo 774336 1167095 := bstep (se 1 (by rfl) ⟨875321, by rfl⟩ : syracuseStep 1167095 = 1750643) B1750643
theorem B1167119 : Blo 774336 1167119 := bstep (se 1 (by rfl) ⟨875339, by rfl⟩ : syracuseStep 1167119 = 1750679) B1750679
theorem B1167161 : Blo 774336 1167161 := bstep (se 2 (by rfl) ⟨437685, by rfl⟩ : syracuseStep 1167161 = 875371) B875371
theorem B8408947 : Blo 774336 8408947 := bstep (se 1 (by rfl) ⟨6306710, by rfl⟩ : syracuseStep 8408947 = 12613421) B12613421
theorem B1167239 : Blo 774336 1167239 := bstep (se 1 (by rfl) ⟨875429, by rfl⟩ : syracuseStep 1167239 = 1750859) B1750859
theorem B1167275 : Blo 774336 1167275 := bstep (se 1 (by rfl) ⟨875456, by rfl⟩ : syracuseStep 1167275 = 1750913) B1750913
theorem B1167305 : Blo 774336 1167305 := bstep (se 2 (by rfl) ⟨437739, by rfl⟩ : syracuseStep 1167305 = 875479) B875479
theorem B872455 : Blo 774336 872455 := bstep (se 1 (by rfl) ⟨654341, by rfl⟩ : syracuseStep 872455 = 1308683) B1308683
theorem B1167419 : Blo 774336 1167419 := bstep (se 1 (by rfl) ⟨875564, by rfl⟩ : syracuseStep 1167419 = 1751129) B1751129
theorem B1167479 : Blo 774336 1167479 := bstep (se 1 (by rfl) ⟨875609, by rfl⟩ : syracuseStep 1167479 = 1751219) B1751219
theorem B1167503 : Blo 774336 1167503 := bstep (se 1 (by rfl) ⟨875627, by rfl⟩ : syracuseStep 1167503 = 1751255) B1751255
theorem B872635 : Blo 774336 872635 := bstep (se 1 (by rfl) ⟨654476, by rfl⟩ : syracuseStep 872635 = 1308953) B1308953
theorem B774407 : Blo 774336 774407 := bstep (se 1 (by rfl) ⟨580805, by rfl⟩ : syracuseStep 774407 = 1161611) B1161611
theorem B774415 : Blo 774336 774415 := bstep (se 1 (by rfl) ⟨580811, by rfl⟩ : syracuseStep 774415 = 1161623) B1161623
theorem B774459 : Blo 774336 774459 := bstep (se 1 (by rfl) ⟨580844, by rfl⟩ : syracuseStep 774459 = 1161689) B1161689
theorem B2216251 : Blo 774336 2216251 := bstep (se 1 (by rfl) ⟨1662188, by rfl⟩ : syracuseStep 2216251 = 3324377) B3324377
theorem B774535 : Blo 774336 774535 := bstep (se 1 (by rfl) ⟨580901, by rfl⟩ : syracuseStep 774535 = 1161803) B1161803
theorem B774543 : Blo 774336 774543 := bstep (se 1 (by rfl) ⟨580907, by rfl⟩ : syracuseStep 774543 = 1161815) B1161815
theorem B774587 : Blo 774336 774587 := bstep (se 1 (by rfl) ⟨580940, by rfl⟩ : syracuseStep 774587 = 1161881) B1161881
theorem B774663 : Blo 774336 774663 := bstep (se 1 (by rfl) ⟨580997, by rfl⟩ : syracuseStep 774663 = 1161995) B1161995
theorem B774671 : Blo 774336 774671 := bstep (se 1 (by rfl) ⟨581003, by rfl⟩ : syracuseStep 774671 = 1162007) B1162007
theorem B774715 : Blo 774336 774715 := bstep (se 1 (by rfl) ⟨581036, by rfl⟩ : syracuseStep 774715 = 1162073) B1162073
theorem B15946307 : Blo 774336 15946307 := bstep (se 1 (by rfl) ⟨11959730, by rfl⟩ : syracuseStep 15946307 = 23919461) B23919461
theorem B774791 : Blo 774336 774791 := bstep (se 1 (by rfl) ⟨581093, by rfl⟩ : syracuseStep 774791 = 1162187) B1162187
theorem B774799 : Blo 774336 774799 := bstep (se 1 (by rfl) ⟨581099, by rfl⟩ : syracuseStep 774799 = 1162199) B1162199
theorem B873103 : Blo 774336 873103 := bstep (se 1 (by rfl) ⟨654827, by rfl⟩ : syracuseStep 873103 = 1309655) B1309655
theorem B774843 : Blo 774336 774843 := bstep (se 1 (by rfl) ⟨581132, by rfl⟩ : syracuseStep 774843 = 1162265) B1162265
theorem B774919 : Blo 774336 774919 := bstep (se 1 (by rfl) ⟨581189, by rfl⟩ : syracuseStep 774919 = 1162379) B1162379
theorem B774927 : Blo 774336 774927 := bstep (se 1 (by rfl) ⟨581195, by rfl⟩ : syracuseStep 774927 = 1162391) B1162391
theorem B774971 : Blo 774336 774971 := bstep (se 1 (by rfl) ⟨581228, by rfl⟩ : syracuseStep 774971 = 1162457) B1162457
theorem B775047 : Blo 774336 775047 := bstep (se 1 (by rfl) ⟨581285, by rfl⟩ : syracuseStep 775047 = 1162571) B1162571
theorem B775055 : Blo 774336 775055 := bstep (se 1 (by rfl) ⟨581291, by rfl⟩ : syracuseStep 775055 = 1162583) B1162583
theorem B775099 : Blo 774336 775099 := bstep (se 1 (by rfl) ⟨581324, by rfl⟩ : syracuseStep 775099 = 1162649) B1162649
theorem B775175 : Blo 774336 775175 := bstep (se 1 (by rfl) ⟨581381, by rfl⟩ : syracuseStep 775175 = 1162763) B1162763
theorem B775183 : Blo 774336 775183 := bstep (se 1 (by rfl) ⟨581387, by rfl⟩ : syracuseStep 775183 = 1162775) B1162775
theorem B775227 : Blo 774336 775227 := bstep (se 1 (by rfl) ⟨581420, by rfl⟩ : syracuseStep 775227 = 1162841) B1162841
theorem B5592125 : Blo 774336 5592125 := bstep (se 3 (by rfl) ⟨1048523, by rfl⟩ : syracuseStep 5592125 = 2097047) B2097047
theorem B775303 : Blo 774336 775303 := bstep (se 1 (by rfl) ⟨581477, by rfl⟩ : syracuseStep 775303 = 1162955) B1162955
theorem B873607 : Blo 774336 873607 := bstep (se 1 (by rfl) ⟨655205, by rfl⟩ : syracuseStep 873607 = 1310411) B1310411
theorem B775311 : Blo 774336 775311 := bstep (se 1 (by rfl) ⟨581483, by rfl⟩ : syracuseStep 775311 = 1162967) B1162967
theorem B775355 : Blo 774336 775355 := bstep (se 1 (by rfl) ⟨581516, by rfl⟩ : syracuseStep 775355 = 1163033) B1163033
theorem B775431 : Blo 774336 775431 := bstep (se 1 (by rfl) ⟨581573, by rfl⟩ : syracuseStep 775431 = 1163147) B1163147
theorem B775439 : Blo 774336 775439 := bstep (se 1 (by rfl) ⟨581579, by rfl⟩ : syracuseStep 775439 = 1163159) B1163159
theorem B775483 : Blo 774336 775483 := bstep (se 1 (by rfl) ⟨581612, by rfl⟩ : syracuseStep 775483 = 1163225) B1163225
theorem B873787 : Blo 774336 873787 := bstep (se 1 (by rfl) ⟨655340, by rfl⟩ : syracuseStep 873787 = 1310681) B1310681
theorem B775559 : Blo 774336 775559 := bstep (se 1 (by rfl) ⟨581669, by rfl⟩ : syracuseStep 775559 = 1163339) B1163339
theorem B76567949 : Blo 774336 76567949 := bstep (se 3 (by rfl) ⟨14356490, by rfl⟩ : syracuseStep 76567949 = 28712981) B28712981
theorem B775567 : Blo 774336 775567 := bstep (se 1 (by rfl) ⟨581675, by rfl⟩ : syracuseStep 775567 = 1163351) B1163351
theorem B4412819 : Blo 774336 4412819 := bstep (se 1 (by rfl) ⟨3309614, by rfl⟩ : syracuseStep 4412819 = 6619229) B6619229
theorem B775611 : Blo 774336 775611 := bstep (se 1 (by rfl) ⟨581708, by rfl⟩ : syracuseStep 775611 = 1163417) B1163417
theorem B775687 : Blo 774336 775687 := bstep (se 1 (by rfl) ⟨581765, by rfl⟩ : syracuseStep 775687 = 1163531) B1163531
theorem B775695 : Blo 774336 775695 := bstep (se 1 (by rfl) ⟨581771, by rfl⟩ : syracuseStep 775695 = 1163543) B1163543
theorem B775739 : Blo 774336 775739 := bstep (se 1 (by rfl) ⟨581804, by rfl⟩ : syracuseStep 775739 = 1163609) B1163609
theorem B775815 : Blo 774336 775815 := bstep (se 1 (by rfl) ⟨581861, by rfl⟩ : syracuseStep 775815 = 1163723) B1163723
theorem B775823 : Blo 774336 775823 := bstep (se 1 (by rfl) ⟨581867, by rfl⟩ : syracuseStep 775823 = 1163735) B1163735
theorem B775867 : Blo 774336 775867 := bstep (se 1 (by rfl) ⟨581900, by rfl⟩ : syracuseStep 775867 = 1163801) B1163801
theorem B775943 : Blo 774336 775943 := bstep (se 1 (by rfl) ⟨581957, by rfl⟩ : syracuseStep 775943 = 1163915) B1163915
theorem B775951 : Blo 774336 775951 := bstep (se 1 (by rfl) ⟨581963, by rfl⟩ : syracuseStep 775951 = 1163927) B1163927
theorem B874255 : Blo 774336 874255 := bstep (se 1 (by rfl) ⟨655691, by rfl⟩ : syracuseStep 874255 = 1311383) B1311383
theorem B775995 : Blo 774336 775995 := bstep (se 1 (by rfl) ⟨581996, by rfl⟩ : syracuseStep 775995 = 1163993) B1163993
theorem B776071 : Blo 774336 776071 := bstep (se 1 (by rfl) ⟨582053, by rfl⟩ : syracuseStep 776071 = 1164107) B1164107
theorem B776079 : Blo 774336 776079 := bstep (se 1 (by rfl) ⟨582059, by rfl⟩ : syracuseStep 776079 = 1164119) B1164119
theorem B776123 : Blo 774336 776123 := bstep (se 1 (by rfl) ⟨582092, by rfl⟩ : syracuseStep 776123 = 1164185) B1164185
theorem B776199 : Blo 774336 776199 := bstep (se 1 (by rfl) ⟨582149, by rfl⟩ : syracuseStep 776199 = 1164299) B1164299
theorem B776207 : Blo 774336 776207 := bstep (se 1 (by rfl) ⟨582155, by rfl⟩ : syracuseStep 776207 = 1164311) B1164311
theorem B776251 : Blo 774336 776251 := bstep (se 1 (by rfl) ⟨582188, by rfl⟩ : syracuseStep 776251 = 1164377) B1164377
theorem B4413527 : Blo 774336 4413527 := bstep (se 1 (by rfl) ⟨3310145, by rfl⟩ : syracuseStep 4413527 = 6620291) B6620291
theorem B776327 : Blo 774336 776327 := bstep (se 1 (by rfl) ⟨582245, by rfl⟩ : syracuseStep 776327 = 1164491) B1164491
theorem B776335 : Blo 774336 776335 := bstep (se 1 (by rfl) ⟨582251, by rfl⟩ : syracuseStep 776335 = 1164503) B1164503
theorem B776379 : Blo 774336 776379 := bstep (se 1 (by rfl) ⟨582284, by rfl⟩ : syracuseStep 776379 = 1164569) B1164569
theorem B776455 : Blo 774336 776455 := bstep (se 1 (by rfl) ⟨582341, by rfl⟩ : syracuseStep 776455 = 1164683) B1164683
theorem B874759 : Blo 774336 874759 := bstep (se 1 (by rfl) ⟨656069, by rfl⟩ : syracuseStep 874759 = 1312139) B1312139
theorem B776463 : Blo 774336 776463 := bstep (se 1 (by rfl) ⟨582347, by rfl⟩ : syracuseStep 776463 = 1164695) B1164695
theorem B776507 : Blo 774336 776507 := bstep (se 1 (by rfl) ⟨582380, by rfl⟩ : syracuseStep 776507 = 1164761) B1164761
theorem B776583 : Blo 774336 776583 := bstep (se 1 (by rfl) ⟨582437, by rfl⟩ : syracuseStep 776583 = 1164875) B1164875
theorem B842119 : Blo 774336 842119 := bstep (se 1 (by rfl) ⟨631589, by rfl⟩ : syracuseStep 842119 = 1263179) B1263179
theorem B776591 : Blo 774336 776591 := bstep (se 1 (by rfl) ⟨582443, by rfl⟩ : syracuseStep 776591 = 1164887) B1164887
theorem B776635 : Blo 774336 776635 := bstep (se 1 (by rfl) ⟨582476, by rfl⟩ : syracuseStep 776635 = 1164953) B1164953
theorem B874939 : Blo 774336 874939 := bstep (se 1 (by rfl) ⟨656204, by rfl⟩ : syracuseStep 874939 = 1312409) B1312409
theorem B3725777 : Blo 774336 3725777 := bstep (se 2 (by rfl) ⟨1397166, by rfl⟩ : syracuseStep 3725777 = 2794333) B2794333
theorem B776711 : Blo 774336 776711 := bstep (se 1 (by rfl) ⟨582533, by rfl⟩ : syracuseStep 776711 = 1165067) B1165067
theorem B776719 : Blo 774336 776719 := bstep (se 1 (by rfl) ⟨582539, by rfl⟩ : syracuseStep 776719 = 1165079) B1165079
theorem B776763 : Blo 774336 776763 := bstep (se 1 (by rfl) ⟨582572, by rfl⟩ : syracuseStep 776763 = 1165145) B1165145
theorem B776839 : Blo 774336 776839 := bstep (se 1 (by rfl) ⟨582629, by rfl⟩ : syracuseStep 776839 = 1165259) B1165259
theorem B776847 : Blo 774336 776847 := bstep (se 1 (by rfl) ⟨582635, by rfl⟩ : syracuseStep 776847 = 1165271) B1165271
theorem B776891 : Blo 774336 776891 := bstep (se 1 (by rfl) ⟨582668, by rfl⟩ : syracuseStep 776891 = 1165337) B1165337
theorem B776967 : Blo 774336 776967 := bstep (se 1 (by rfl) ⟨582725, by rfl⟩ : syracuseStep 776967 = 1165451) B1165451
theorem B776975 : Blo 774336 776975 := bstep (se 1 (by rfl) ⟨582731, by rfl⟩ : syracuseStep 776975 = 1165463) B1165463
theorem B6708017 : Blo 774336 6708017 := bstep (se 2 (by rfl) ⟨2515506, by rfl⟩ : syracuseStep 6708017 = 5031013) B5031013
theorem B6282035 : Blo 774336 6282035 := bstep (se 1 (by rfl) ⟨4711526, by rfl⟩ : syracuseStep 6282035 = 9423053) B9423053
theorem B777019 : Blo 774336 777019 := bstep (se 1 (by rfl) ⟨582764, by rfl⟩ : syracuseStep 777019 = 1165529) B1165529
theorem B777095 : Blo 774336 777095 := bstep (se 1 (by rfl) ⟨582821, by rfl⟩ : syracuseStep 777095 = 1165643) B1165643
theorem B777103 : Blo 774336 777103 := bstep (se 1 (by rfl) ⟨582827, by rfl⟩ : syracuseStep 777103 = 1165655) B1165655
theorem B875407 : Blo 774336 875407 := bstep (se 1 (by rfl) ⟨656555, by rfl⟩ : syracuseStep 875407 = 1313111) B1313111
theorem B8379287 : Blo 774336 8379287 := bstep (se 1 (by rfl) ⟨6284465, by rfl⟩ : syracuseStep 8379287 = 12568931) B12568931
theorem B777147 : Blo 774336 777147 := bstep (se 1 (by rfl) ⟨582860, by rfl⟩ : syracuseStep 777147 = 1165721) B1165721
theorem B777223 : Blo 774336 777223 := bstep (se 1 (by rfl) ⟨582917, by rfl⟩ : syracuseStep 777223 = 1165835) B1165835
theorem B1989647 : Blo 774336 1989647 := bstep (se 1 (by rfl) ⟨1492235, by rfl⟩ : syracuseStep 1989647 = 2984471) B2984471
theorem B777231 : Blo 774336 777231 := bstep (se 1 (by rfl) ⟨582923, by rfl⟩ : syracuseStep 777231 = 1165847) B1165847
theorem B777275 : Blo 774336 777275 := bstep (se 1 (by rfl) ⟨582956, by rfl⟩ : syracuseStep 777275 = 1165913) B1165913
theorem B777351 : Blo 774336 777351 := bstep (se 1 (by rfl) ⟨583013, by rfl⟩ : syracuseStep 777351 = 1166027) B1166027
theorem B1105039 : Blo 774336 1105039 := bstep (se 1 (by rfl) ⟨828779, by rfl⟩ : syracuseStep 1105039 = 1657559) B1657559
theorem B777359 : Blo 774336 777359 := bstep (se 1 (by rfl) ⟨583019, by rfl⟩ : syracuseStep 777359 = 1166039) B1166039
theorem B777403 : Blo 774336 777403 := bstep (se 1 (by rfl) ⟨583052, by rfl⟩ : syracuseStep 777403 = 1166105) B1166105
theorem B777479 : Blo 774336 777479 := bstep (se 1 (by rfl) ⟨583109, by rfl⟩ : syracuseStep 777479 = 1166219) B1166219
theorem B1105159 : Blo 774336 1105159 := bstep (se 1 (by rfl) ⟨828869, by rfl⟩ : syracuseStep 1105159 = 1657739) B1657739
theorem B777487 : Blo 774336 777487 := bstep (se 1 (by rfl) ⟨583115, by rfl⟩ : syracuseStep 777487 = 1166231) B1166231
theorem B1662223 : Blo 774336 1662223 := bstep (se 1 (by rfl) ⟨1246667, by rfl⟩ : syracuseStep 1662223 = 2493335) B2493335
theorem B3366203 : Blo 774336 3366203 := bstep (se 1 (by rfl) ⟨2524652, by rfl⟩ : syracuseStep 3366203 = 5049305) B5049305
theorem B777531 : Blo 774336 777531 := bstep (se 1 (by rfl) ⟨583148, by rfl⟩ : syracuseStep 777531 = 1166297) B1166297
theorem B3923315 : Blo 774336 3923315 := bstep (se 1 (by rfl) ⟨2942486, by rfl⟩ : syracuseStep 3923315 = 5884973) B5884973
theorem B777607 : Blo 774336 777607 := bstep (se 1 (by rfl) ⟨583205, by rfl⟩ : syracuseStep 777607 = 1166411) B1166411
theorem B777615 : Blo 774336 777615 := bstep (se 1 (by rfl) ⟨583211, by rfl⟩ : syracuseStep 777615 = 1166423) B1166423
theorem B3726739 : Blo 774336 3726739 := bstep (se 1 (by rfl) ⟨2795054, by rfl⟩ : syracuseStep 3726739 = 5590109) B5590109
theorem B777659 : Blo 774336 777659 := bstep (se 1 (by rfl) ⟨583244, by rfl⟩ : syracuseStep 777659 = 1166489) B1166489
theorem B777735 : Blo 774336 777735 := bstep (se 1 (by rfl) ⟨583301, by rfl⟩ : syracuseStep 777735 = 1166603) B1166603
theorem B777743 : Blo 774336 777743 := bstep (se 1 (by rfl) ⟨583307, by rfl⟩ : syracuseStep 777743 = 1166615) B1166615
theorem B777787 : Blo 774336 777787 := bstep (se 1 (by rfl) ⟨583340, by rfl⟩ : syracuseStep 777787 = 1166681) B1166681
theorem B777863 : Blo 774336 777863 := bstep (se 1 (by rfl) ⟨583397, by rfl⟩ : syracuseStep 777863 = 1166795) B1166795
theorem B777871 : Blo 774336 777871 := bstep (se 1 (by rfl) ⟨583403, by rfl⟩ : syracuseStep 777871 = 1166807) B1166807
theorem B777915 : Blo 774336 777915 := bstep (se 1 (by rfl) ⟨583436, by rfl⟩ : syracuseStep 777915 = 1166873) B1166873
theorem B777991 : Blo 774336 777991 := bstep (se 1 (by rfl) ⟨583493, by rfl⟩ : syracuseStep 777991 = 1166987) B1166987
theorem B777999 : Blo 774336 777999 := bstep (se 1 (by rfl) ⟨583499, by rfl⟩ : syracuseStep 777999 = 1166999) B1166999
theorem B778043 : Blo 774336 778043 := bstep (se 1 (by rfl) ⟨583532, by rfl⟩ : syracuseStep 778043 = 1167065) B1167065
theorem B3923801 : Blo 774336 3923801 := bstep (se 2 (by rfl) ⟨1471425, by rfl⟩ : syracuseStep 3923801 = 2942851) B2942851
theorem B778119 : Blo 774336 778119 := bstep (se 1 (by rfl) ⟨583589, by rfl⟩ : syracuseStep 778119 = 1167179) B1167179
theorem B778127 : Blo 774336 778127 := bstep (se 1 (by rfl) ⟨583595, by rfl⟩ : syracuseStep 778127 = 1167191) B1167191
theorem B1892243 : Blo 774336 1892243 := bstep (se 1 (by rfl) ⟨1419182, by rfl⟩ : syracuseStep 1892243 = 2838365) B2838365
theorem B4415417 : Blo 774336 4415417 := bstep (se 2 (by rfl) ⟨1655781, by rfl⟩ : syracuseStep 4415417 = 3311563) B3311563
theorem B778171 : Blo 774336 778171 := bstep (se 1 (by rfl) ⟨583628, by rfl⟩ : syracuseStep 778171 = 1167257) B1167257
theorem B778247 : Blo 774336 778247 := bstep (se 1 (by rfl) ⟨583685, by rfl⟩ : syracuseStep 778247 = 1167371) B1167371
theorem B778255 : Blo 774336 778255 := bstep (se 1 (by rfl) ⟨583691, by rfl⟩ : syracuseStep 778255 = 1167383) B1167383
theorem B8970263 : Blo 774336 8970263 := bstep (se 1 (by rfl) ⟨6727697, by rfl⟩ : syracuseStep 8970263 = 13455395) B13455395
theorem B778299 : Blo 774336 778299 := bstep (se 1 (by rfl) ⟨583724, by rfl⟩ : syracuseStep 778299 = 1167449) B1167449
theorem B4186313 : Blo 774336 4186313 := bstep (se 2 (by rfl) ⟨1569867, by rfl⟩ : syracuseStep 4186313 = 3139735) B3139735
theorem B2941393 : Blo 774336 2941393 := bstep (se 2 (by rfl) ⟨1103022, by rfl⟩ : syracuseStep 2941393 = 2206045) B2206045
theorem B1401463 : Blo 774336 1401463 := bstep (se 1 (by rfl) ⟨1051097, by rfl⟩ : syracuseStep 1401463 = 2102195) B2102195
theorem B1106617 : Blo 774336 1106617 := bstep (se 2 (by rfl) ⟨414981, by rfl⟩ : syracuseStep 1106617 = 829963) B829963
theorem B2941697 : Blo 774336 2941697 := bstep (se 2 (by rfl) ⟨1103136, by rfl⟩ : syracuseStep 2941697 = 2206273) B2206273
theorem B2614031 : Blo 774336 2614031 := bstep (se 1 (by rfl) ⟨1960523, by rfl⟩ : syracuseStep 2614031 = 3921047) B3921047
theorem B14377817 : Blo 774336 14377817 := bstep (se 2 (by rfl) ⟨5391681, by rfl⟩ : syracuseStep 14377817 = 10783363) B10783363
theorem B2614301 : Blo 774336 2614301 := bstep (se 3 (by rfl) ⟨490181, by rfl⟩ : syracuseStep 2614301 = 980363) B980363
theorem B1860727 : Blo 774336 1860727 := bstep (se 1 (by rfl) ⟨1395545, by rfl⟩ : syracuseStep 1860727 = 2791091) B2791091
theorem B2942153 : Blo 774336 2942153 := bstep (se 2 (by rfl) ⟨1103307, by rfl⟩ : syracuseStep 2942153 = 2206615) B2206615
theorem B3728585 : Blo 774336 3728585 := bstep (se 2 (by rfl) ⟨1398219, by rfl⟩ : syracuseStep 3728585 = 2796439) B2796439
theorem B5596397 : Blo 774336 5596397 := bstep (se 3 (by rfl) ⟨1049324, by rfl⟩ : syracuseStep 5596397 = 2098649) B2098649
theorem B2123297 : Blo 774336 2123297 := bstep (se 2 (by rfl) ⟨796236, by rfl⟩ : syracuseStep 2123297 = 1592473) B1592473
theorem B5596715 : Blo 774336 5596715 := bstep (se 1 (by rfl) ⟨4197536, by rfl⟩ : syracuseStep 5596715 = 8395073) B8395073
theorem B5596739 : Blo 774336 5596739 := bstep (se 1 (by rfl) ⟨4197554, by rfl⟩ : syracuseStep 5596739 = 8395109) B8395109
theorem B10643021 : Blo 774336 10643021 := bstep (se 3 (by rfl) ⟨1995566, by rfl⟩ : syracuseStep 10643021 = 3991133) B3991133
theorem B5891777 : Blo 774336 5891777 := bstep (se 2 (by rfl) ⟨2209416, by rfl⟩ : syracuseStep 5891777 = 4418833) B4418833
theorem B33613643 : Blo 774336 33613643 := bstep (se 1 (by rfl) ⟨25210232, by rfl⟩ : syracuseStep 33613643 = 50420465) B50420465
theorem B2484083 : Blo 774336 2484083 := bstep (se 1 (by rfl) ⟨1863062, by rfl⟩ : syracuseStep 2484083 = 3726125) B3726125
theorem B3532679 : Blo 774336 3532679 := bstep (se 1 (by rfl) ⟨2649509, by rfl⟩ : syracuseStep 3532679 = 5299019) B5299019
theorem B1107847 : Blo 774336 1107847 := bstep (se 1 (by rfl) ⟨830885, by rfl⟩ : syracuseStep 1107847 = 1661771) B1661771
theorem B3925907 : Blo 774336 3925907 := bstep (se 1 (by rfl) ⟨2944430, by rfl⟩ : syracuseStep 3925907 = 5888861) B5888861
theorem B4712377 : Blo 774336 4712377 := bstep (se 2 (by rfl) ⟨1767141, by rfl⟩ : syracuseStep 4712377 = 3534283) B3534283
theorem B2615705 : Blo 774336 2615705 := bstep (se 2 (by rfl) ⟨980889, by rfl⟩ : syracuseStep 2615705 = 1961779) B1961779
theorem B1960463 : Blo 774336 1960463 := bstep (se 1 (by rfl) ⟨1470347, by rfl⟩ : syracuseStep 1960463 = 2940695) B2940695
theorem B1960595 : Blo 774336 1960595 := bstep (se 1 (by rfl) ⟨1470446, by rfl⟩ : syracuseStep 1960595 = 2940893) B2940893
theorem B2616407 : Blo 774336 2616407 := bstep (se 1 (by rfl) ⟨1962305, by rfl⟩ : syracuseStep 2616407 = 3924611) B3924611
theorem B1240363 : Blo 774336 1240363 := bstep (se 1 (by rfl) ⟨930272, by rfl⟩ : syracuseStep 1240363 = 1860545) B1860545
theorem B1240439 : Blo 774336 1240439 := bstep (se 1 (by rfl) ⟨930329, by rfl⟩ : syracuseStep 1240439 = 1860659) B1860659
theorem B5041693 : Blo 774336 5041693 := bstep (se 3 (by rfl) ⟨945317, by rfl⟩ : syracuseStep 5041693 = 1890635) B1890635
theorem B2616893 : Blo 774336 2616893 := bstep (se 3 (by rfl) ⟨490667, by rfl⟩ : syracuseStep 2616893 = 981335) B981335
theorem B1961729 : Blo 774336 1961729 := bstep (se 2 (by rfl) ⟨735648, by rfl⟩ : syracuseStep 1961729 = 1471297) B1471297
theorem B1470241 : Blo 774336 1470241 := bstep (se 2 (by rfl) ⟨551340, by rfl⟩ : syracuseStep 1470241 = 1102681) B1102681
theorem B3731467 : Blo 774336 3731467 := bstep (se 1 (by rfl) ⟨2798600, by rfl⟩ : syracuseStep 3731467 = 5597201) B5597201
theorem B1962103 : Blo 774336 1962103 := bstep (se 1 (by rfl) ⟨1471577, by rfl⟩ : syracuseStep 1962103 = 2943155) B2943155
theorem B1306759 : Blo 774336 1306759 := bstep (se 1 (by rfl) ⟨980069, by rfl⟩ : syracuseStep 1306759 = 1960139) B1960139
theorem B2945281 : Blo 774336 2945281 := bstep (se 2 (by rfl) ⟨1104480, by rfl⟩ : syracuseStep 2945281 = 2208961) B2208961
theorem B1962539 : Blo 774336 1962539 := bstep (se 1 (by rfl) ⟨1471904, by rfl⟩ : syracuseStep 1962539 = 2943809) B2943809
theorem B1864235 : Blo 774336 1864235 := bstep (se 1 (by rfl) ⟨1398176, by rfl⟩ : syracuseStep 1864235 = 2796353) B2796353
theorem B1307407 : Blo 774336 1307407 := bstep (se 1 (by rfl) ⟨980555, by rfl⟩ : syracuseStep 1307407 = 1961111) B1961111
theorem B3732313 : Blo 774336 3732313 := bstep (se 2 (by rfl) ⟨1399617, by rfl⟩ : syracuseStep 3732313 = 2799235) B2799235
theorem B3928985 : Blo 774336 3928985 := bstep (se 2 (by rfl) ⟨1473369, by rfl⟩ : syracuseStep 3928985 = 2946739) B2946739
theorem B2618297 : Blo 774336 2618297 := bstep (se 2 (by rfl) ⟨981861, by rfl⟩ : syracuseStep 2618297 = 1963723) B1963723
theorem B5895179 : Blo 774336 5895179 := bstep (se 1 (by rfl) ⟨4421384, by rfl⟩ : syracuseStep 5895179 = 8842769) B8842769
theorem B1471547 : Blo 774336 1471547 := bstep (se 1 (by rfl) ⟨1103660, by rfl⟩ : syracuseStep 1471547 = 2207321) B2207321
theorem B5600429 : Blo 774336 5600429 := bstep (se 3 (by rfl) ⟨1050080, by rfl⟩ : syracuseStep 5600429 = 2100161) B2100161
theorem B1864889 : Blo 774336 1864889 := bstep (se 2 (by rfl) ⟨699333, by rfl⟩ : syracuseStep 1864889 = 1398667) B1398667
theorem B947387 : Blo 774336 947387 := bstep (se 1 (by rfl) ⟨710540, by rfl⟩ : syracuseStep 947387 = 1421081) B1421081
theorem B1995977 : Blo 774336 1995977 := bstep (se 2 (by rfl) ⟨748491, by rfl⟩ : syracuseStep 1995977 = 1496983) B1496983
theorem B11171105 : Blo 774336 11171105 := bstep (se 2 (by rfl) ⟨4189164, by rfl⟩ : syracuseStep 11171105 = 8378329) B8378329
theorem B1307947 : Blo 774336 1307947 := bstep (se 1 (by rfl) ⟨980960, by rfl⟩ : syracuseStep 1307947 = 1961921) B1961921
theorem B1963379 : Blo 774336 1963379 := bstep (se 1 (by rfl) ⟨1472534, by rfl⟩ : syracuseStep 1963379 = 2945069) B2945069
theorem B1963399 : Blo 774336 1963399 := bstep (se 1 (by rfl) ⟨1472549, by rfl⟩ : syracuseStep 1963399 = 2945099) B2945099
theorem B23950727 : Blo 774336 23950727 := bstep (se 1 (by rfl) ⟨17963045, by rfl⟩ : syracuseStep 23950727 = 35926091) B35926091
theorem B1308089 : Blo 774336 1308089 := bstep (se 2 (by rfl) ⟨490533, by rfl⟩ : syracuseStep 1308089 = 981067) B981067
theorem B6714809 : Blo 774336 6714809 := bstep (se 2 (by rfl) ⟨2518053, by rfl⟩ : syracuseStep 6714809 = 5036107) B5036107
theorem B2618891 : Blo 774336 2618891 := bstep (se 1 (by rfl) ⟨1964168, by rfl⟩ : syracuseStep 2618891 = 3928337) B3928337
theorem B2094625 : Blo 774336 2094625 := bstep (se 2 (by rfl) ⟨785484, by rfl⟩ : syracuseStep 2094625 = 1570969) B1570969
theorem B1472033 : Blo 774336 1472033 := bstep (se 2 (by rfl) ⟨552012, by rfl⟩ : syracuseStep 1472033 = 1104025) B1104025
theorem B2618999 : Blo 774336 2618999 := bstep (se 1 (by rfl) ⟨1964249, by rfl⟩ : syracuseStep 2618999 = 3928499) B3928499
theorem B1963673 : Blo 774336 1963673 := bstep (se 2 (by rfl) ⟨736377, by rfl⟩ : syracuseStep 1963673 = 1472755) B1472755
theorem B1865369 : Blo 774336 1865369 := bstep (se 2 (by rfl) ⟨699513, by rfl⟩ : syracuseStep 1865369 = 1399027) B1399027
theorem B1472185 : Blo 774336 1472185 := bstep (se 2 (by rfl) ⟨552069, by rfl⟩ : syracuseStep 1472185 = 1104139) B1104139
theorem B980743 : Blo 774336 980743 := bstep (se 1 (by rfl) ⟨735557, by rfl⟩ : syracuseStep 980743 = 1471115) B1471115
theorem B2094907 : Blo 774336 2094907 := bstep (se 1 (by rfl) ⟨1571180, by rfl⟩ : syracuseStep 2094907 = 3142361) B3142361
theorem B1963835 : Blo 774336 1963835 := bstep (se 1 (by rfl) ⟨1472876, by rfl⟩ : syracuseStep 1963835 = 2945753) B2945753
theorem B1964047 : Blo 774336 1964047 := bstep (se 1 (by rfl) ⟨1473035, by rfl⟩ : syracuseStep 1964047 = 2946071) B2946071
theorem B1308791 : Blo 774336 1308791 := bstep (se 1 (by rfl) ⟨981593, by rfl⟩ : syracuseStep 1308791 = 1963187) B1963187
theorem B981163 : Blo 774336 981163 := bstep (se 1 (by rfl) ⟨735872, by rfl⟩ : syracuseStep 981163 = 1471745) B1471745
theorem B2619593 : Blo 774336 2619593 := bstep (se 2 (by rfl) ⟨982347, by rfl⟩ : syracuseStep 2619593 = 1964695) B1964695
theorem B3733775 : Blo 774336 3733775 := bstep (se 1 (by rfl) ⟨2800331, by rfl⟩ : syracuseStep 3733775 = 5600663) B5600663
theorem B1964321 : Blo 774336 1964321 := bstep (se 2 (by rfl) ⟨736620, by rfl⟩ : syracuseStep 1964321 = 1473241) B1473241
theorem B9075037 : Blo 774336 9075037 := bstep (se 3 (by rfl) ⟨1701569, by rfl⟩ : syracuseStep 9075037 = 3403139) B3403139
theorem B4422023 : Blo 774336 4422023 := bstep (se 1 (by rfl) ⟨3316517, by rfl⟩ : syracuseStep 4422023 = 6633035) B6633035
theorem B981391 : Blo 774336 981391 := bstep (se 1 (by rfl) ⟨736043, by rfl⟩ : syracuseStep 981391 = 1472087) B1472087
theorem B1178155 : Blo 774336 1178155 := bstep (se 1 (by rfl) ⟨883616, by rfl⟩ : syracuseStep 1178155 = 1767233) B1767233
theorem B2357819 : Blo 774336 2357819 := bstep (se 1 (by rfl) ⟨1768364, by rfl⟩ : syracuseStep 2357819 = 3536729) B3536729
theorem B1309243 : Blo 774336 1309243 := bstep (se 1 (by rfl) ⟨981932, by rfl⟩ : syracuseStep 1309243 = 1963865) B1963865
theorem B1309385 : Blo 774336 1309385 := bstep (se 2 (by rfl) ⟨491019, by rfl⟩ : syracuseStep 1309385 = 982039) B982039
theorem B2620295 : Blo 774336 2620295 := bstep (se 1 (by rfl) ⟨1965221, by rfl⟩ : syracuseStep 2620295 = 3930443) B3930443
theorem B5897123 : Blo 774336 5897123 := bstep (se 1 (by rfl) ⟨4422842, by rfl⟩ : syracuseStep 5897123 = 8845685) B8845685
theorem B2948183 : Blo 774336 2948183 := bstep (se 1 (by rfl) ⟨2211137, by rfl⟩ : syracuseStep 2948183 = 4422275) B4422275
theorem B982135 : Blo 774336 982135 := bstep (se 1 (by rfl) ⟨736601, by rfl⟩ : syracuseStep 982135 = 1473203) B1473203
theorem B10648709 : Blo 774336 10648709 := bstep (se 4 (by rfl) ⟨998316, by rfl⟩ : syracuseStep 10648709 = 1996633) B1996633
theorem B2620673 : Blo 774336 2620673 := bstep (se 2 (by rfl) ⟨982752, by rfl⟩ : syracuseStep 2620673 = 1965505) B1965505
theorem B1965323 : Blo 774336 1965323 := bstep (se 1 (by rfl) ⟨1473992, by rfl⟩ : syracuseStep 1965323 = 2947985) B2947985
theorem B1310087 : Blo 774336 1310087 := bstep (se 1 (by rfl) ⟨982565, by rfl⟩ : syracuseStep 1310087 = 1965131) B1965131
theorem B1473977 : Blo 774336 1473977 := bstep (se 2 (by rfl) ⟨552741, by rfl⟩ : syracuseStep 1473977 = 1105483) B1105483
theorem B3931577 : Blo 774336 3931577 := bstep (se 2 (by rfl) ⟨1474341, by rfl⟩ : syracuseStep 3931577 = 2948683) B2948683
theorem B982459 : Blo 774336 982459 := bstep (se 1 (by rfl) ⟨736844, by rfl⟩ : syracuseStep 982459 = 1473689) B1473689
theorem B3145169 : Blo 774336 3145169 := bstep (se 2 (by rfl) ⟨1179438, by rfl⟩ : syracuseStep 3145169 = 2358877) B2358877
theorem B2948669 : Blo 774336 2948669 := bstep (se 3 (by rfl) ⟨552875, by rfl⟩ : syracuseStep 2948669 = 1105751) B1105751
theorem B11337317 : Blo 774336 11337317 := bstep (se 4 (by rfl) ⟨1062873, by rfl⟩ : syracuseStep 11337317 = 2125747) B2125747
theorem B1965971 : Blo 774336 1965971 := bstep (se 1 (by rfl) ⟨1474478, by rfl⟩ : syracuseStep 1965971 = 2948957) B2948957
theorem B2490259 : Blo 774336 2490259 := bstep (se 1 (by rfl) ⟨1867694, by rfl⟩ : syracuseStep 2490259 = 3735389) B3735389
theorem B982955 : Blo 774336 982955 := bstep (se 1 (by rfl) ⟨737216, by rfl⟩ : syracuseStep 982955 = 1474433) B1474433
theorem B1310843 : Blo 774336 1310843 := bstep (se 1 (by rfl) ⟨983132, by rfl⟩ : syracuseStep 1310843 = 1966265) B1966265
theorem B9961649 : Blo 774336 9961649 := bstep (se 2 (by rfl) ⟨3735618, by rfl⟩ : syracuseStep 9961649 = 7471237) B7471237
theorem B1475003 : Blo 774336 1475003 := bstep (se 1 (by rfl) ⟨1106252, by rfl⟩ : syracuseStep 1475003 = 2212505) B2212505
theorem B2621915 : Blo 774336 2621915 := bstep (se 1 (by rfl) ⟨1966436, by rfl⟩ : syracuseStep 2621915 = 3932873) B3932873
theorem B2949641 : Blo 774336 2949641 := bstep (se 2 (by rfl) ⟨1106115, by rfl⟩ : syracuseStep 2949641 = 2212231) B2212231
theorem B1311241 : Blo 774336 1311241 := bstep (se 2 (by rfl) ⟨491715, by rfl⟩ : syracuseStep 1311241 = 983431) B983431
theorem B2687627 : Blo 774336 2687627 := bstep (se 1 (by rfl) ⟨2015720, by rfl⟩ : syracuseStep 2687627 = 4031441) B4031441
theorem B1311403 : Blo 774336 1311403 := bstep (se 1 (by rfl) ⟨983552, by rfl⟩ : syracuseStep 1311403 = 1967105) B1967105
theorem B2097913 : Blo 774336 2097913 := bstep (se 2 (by rfl) ⟨786717, by rfl⟩ : syracuseStep 2097913 = 1573435) B1573435
theorem B1868617 : Blo 774336 1868617 := bstep (se 2 (by rfl) ⟨700731, by rfl⟩ : syracuseStep 1868617 = 1401463) B1401463
theorem B1966943 : Blo 774336 1966943 := bstep (se 1 (by rfl) ⟨1475207, by rfl⟩ : syracuseStep 1966943 = 2950415) B2950415
theorem B3933035 : Blo 774336 3933035 := bstep (se 1 (by rfl) ⟨2949776, by rfl⟩ : syracuseStep 3933035 = 5899553) B5899553
theorem B1475435 : Blo 774336 1475435 := bstep (se 1 (by rfl) ⟨1106576, by rfl⟩ : syracuseStep 1475435 = 2213153) B2213153
theorem B1475489 : Blo 774336 1475489 := bstep (se 2 (by rfl) ⟨553308, by rfl⟩ : syracuseStep 1475489 = 1106617) B1106617
theorem B983983 : Blo 774336 983983 := bstep (se 1 (by rfl) ⟨737987, by rfl⟩ : syracuseStep 983983 = 1475975) B1475975
theorem B1311707 : Blo 774336 1311707 := bstep (se 1 (by rfl) ⟨983780, by rfl⟩ : syracuseStep 1311707 = 1967561) B1967561
theorem B7078961 : Blo 774336 7078961 := bstep (se 2 (by rfl) ⟨2654610, by rfl⟩ : syracuseStep 7078961 = 5309221) B5309221
theorem B2622617 : Blo 774336 2622617 := bstep (se 2 (by rfl) ⟨983481, by rfl⟩ : syracuseStep 2622617 = 1966963) B1966963
theorem B2655389 : Blo 774336 2655389 := bstep (se 3 (by rfl) ⟨497885, by rfl⟩ : syracuseStep 2655389 = 995771) B995771
theorem B1311943 : Blo 774336 1311943 := bstep (se 1 (by rfl) ⟨983957, by rfl⟩ : syracuseStep 1311943 = 1967915) B1967915
theorem B8848601 : Blo 774336 8848601 := bstep (se 2 (by rfl) ⟨3318225, by rfl⟩ : syracuseStep 8848601 = 6636451) B6636451
theorem B1312105 : Blo 774336 1312105 := bstep (se 2 (by rfl) ⟨492039, by rfl⟩ : syracuseStep 1312105 = 984079) B984079
theorem B3147245 : Blo 774336 3147245 := bstep (se 3 (by rfl) ⟨590108, by rfl⟩ : syracuseStep 3147245 = 1180217) B1180217
theorem B3933683 : Blo 774336 3933683 := bstep (se 1 (by rfl) ⟨2950262, by rfl⟩ : syracuseStep 3933683 = 5900525) B5900525
theorem B1968047 : Blo 774336 1968047 := bstep (se 1 (by rfl) ⟨1476035, by rfl⟩ : syracuseStep 1968047 = 2952071) B2952071
theorem B2951099 : Blo 774336 2951099 := bstep (se 1 (by rfl) ⟨2213324, by rfl⟩ : syracuseStep 2951099 = 4426649) B4426649
theorem B1312699 : Blo 774336 1312699 := bstep (se 1 (by rfl) ⟨984524, by rfl⟩ : syracuseStep 1312699 = 1969049) B1969049
theorem B985051 : Blo 774336 985051 := bstep (se 1 (by rfl) ⟨738788, by rfl⟩ : syracuseStep 985051 = 1477577) B1477577
theorem B4491301 : Blo 774336 4491301 := bstep (se 4 (by rfl) ⟨421059, by rfl⟩ : syracuseStep 4491301 = 842119) B842119
theorem B1312807 : Blo 774336 1312807 := bstep (se 1 (by rfl) ⟨984605, by rfl⟩ : syracuseStep 1312807 = 1969211) B1969211
theorem B9439537 : Blo 774336 9439537 := bstep (se 2 (by rfl) ⟨3539826, by rfl⟩ : syracuseStep 9439537 = 7079653) B7079653
theorem B2623805 : Blo 774336 2623805 := bstep (se 3 (by rfl) ⟨491963, by rfl⟩ : syracuseStep 2623805 = 983927) B983927
theorem B1050985 : Blo 774336 1050985 := bstep (se 2 (by rfl) ⟨394119, by rfl⟩ : syracuseStep 1050985 = 788239) B788239
theorem B1313131 : Blo 774336 1313131 := bstep (se 1 (by rfl) ⟨984848, by rfl⟩ : syracuseStep 1313131 = 1969697) B1969697
theorem B2492873 : Blo 774336 2492873 := bstep (se 2 (by rfl) ⟨934827, by rfl⟩ : syracuseStep 2492873 = 1869655) B1869655
theorem B1477129 : Blo 774336 1477129 := bstep (se 2 (by rfl) ⟨553923, by rfl⟩ : syracuseStep 1477129 = 1107847) B1107847
theorem B5901011 : Blo 774336 5901011 := bstep (se 1 (by rfl) ⟨4425758, by rfl⟩ : syracuseStep 5901011 = 8851517) B8851517
theorem B3934979 : Blo 774336 3934979 := bstep (se 1 (by rfl) ⟨2951234, by rfl⟩ : syracuseStep 3934979 = 5902469) B5902469
theorem B25168715 : Blo 774336 25168715 := bstep (se 1 (by rfl) ⟨18876536, by rfl⟩ : syracuseStep 25168715 = 37753073) B37753073
theorem B14912333 : Blo 774336 14912333 := bstep (se 3 (by rfl) ⟨2796062, by rfl⟩ : syracuseStep 14912333 = 5592125) B5592125
theorem B1969231 : Blo 774336 1969231 := bstep (se 1 (by rfl) ⟨1476923, by rfl⟩ : syracuseStep 1969231 = 2953847) B2953847
theorem B2624669 : Blo 774336 2624669 := bstep (se 3 (by rfl) ⟨492125, by rfl⟩ : syracuseStep 2624669 = 984251) B984251
theorem B2526365 : Blo 774336 2526365 := bstep (se 3 (by rfl) ⟨473693, by rfl⟩ : syracuseStep 2526365 = 947387) B947387
theorem B7015619 : Blo 774336 7015619 := bstep (se 1 (by rfl) ⟨5261714, by rfl⟩ : syracuseStep 7015619 = 10523429) B10523429
theorem B2625209 : Blo 774336 2625209 := bstep (se 2 (by rfl) ⟨984453, by rfl⟩ : syracuseStep 2625209 = 1968907) B1968907
theorem B1969879 : Blo 774336 1969879 := bstep (se 1 (by rfl) ⟨1477409, by rfl⟩ : syracuseStep 1969879 = 2954819) B2954819
theorem B2953331 : Blo 774336 2953331 := bstep (se 1 (by rfl) ⟨2214998, by rfl⟩ : syracuseStep 2953331 = 4429997) B4429997
theorem B2625803 : Blo 774336 2625803 := bstep (se 1 (by rfl) ⟨1969352, by rfl⟩ : syracuseStep 2625803 = 3938705) B3938705
theorem B3936599 : Blo 774336 3936599 := bstep (se 1 (by rfl) ⟨2952449, by rfl⟩ : syracuseStep 3936599 = 5904899) B5904899
theorem B2626073 : Blo 774336 2626073 := bstep (se 2 (by rfl) ⟨984777, by rfl⟩ : syracuseStep 2626073 = 1969555) B1969555
theorem B4264633 : Blo 774336 4264633 := bstep (se 2 (by rfl) ⟨1599237, by rfl⟩ : syracuseStep 4264633 = 3198475) B3198475
theorem B11211929 : Blo 774336 11211929 := bstep (se 2 (by rfl) ⟨4204473, by rfl⟩ : syracuseStep 11211929 = 8408947) B8408947
theorem B2790875 : Blo 774336 2790875 := bstep (se 1 (by rfl) ⟨2093156, by rfl⟩ : syracuseStep 2790875 = 4186313) B4186313
theorem B1742345 : Blo 774336 1742345 := bstep (se 2 (by rfl) ⟨653379, by rfl⟩ : syracuseStep 1742345 = 1306759) B1306759
theorem B2561675 : Blo 774336 2561675 := bstep (se 1 (by rfl) ⟨1921256, by rfl⟩ : syracuseStep 2561675 = 3842513) B3842513
theorem B2955001 : Blo 774336 2955001 := bstep (se 2 (by rfl) ⟨1108125, by rfl⟩ : syracuseStep 2955001 = 2216251) B2216251
theorem B2660125 : Blo 774336 2660125 := bstep (se 3 (by rfl) ⟨498773, by rfl⟩ : syracuseStep 2660125 = 997547) B997547
theorem B1742687 : Blo 774336 1742687 := bstep (se 1 (by rfl) ⟨1307015, by rfl⟩ : syracuseStep 1742687 = 2614031) B2614031
theorem B3151799 : Blo 774336 3151799 := bstep (se 1 (by rfl) ⟨2363849, by rfl⟩ : syracuseStep 3151799 = 4727699) B4727699
theorem B1742867 : Blo 774336 1742867 := bstep (se 1 (by rfl) ⟨1307150, by rfl⟩ : syracuseStep 1742867 = 2614301) B2614301
theorem B5904413 : Blo 774336 5904413 := bstep (se 3 (by rfl) ⟨1107077, by rfl⟩ : syracuseStep 5904413 = 2214155) B2214155
theorem B1743209 : Blo 774336 1743209 := bstep (se 2 (by rfl) ⟨653703, by rfl⟩ : syracuseStep 1743209 = 1307407) B1307407
theorem B1415531 : Blo 774336 1415531 := bstep (se 1 (by rfl) ⟨1061648, by rfl⟩ : syracuseStep 1415531 = 2123297) B2123297
theorem B5609861 : Blo 774336 5609861 := bstep (se 4 (by rfl) ⟨525924, by rfl⟩ : syracuseStep 5609861 = 1051849) B1051849
theorem B9935405 : Blo 774336 9935405 := bstep (se 3 (by rfl) ⟨1862888, by rfl⟩ : syracuseStep 9935405 = 3725777) B3725777
theorem B1743803 : Blo 774336 1743803 := bstep (se 1 (by rfl) ⟨1307852, by rfl⟩ : syracuseStep 1743803 = 2615705) B2615705
theorem B1743929 : Blo 774336 1743929 := bstep (se 2 (by rfl) ⟨653973, by rfl⟩ : syracuseStep 1743929 = 1307947) B1307947
theorem B9706787 : Blo 774336 9706787 := bstep (se 1 (by rfl) ⟨7280090, by rfl⟩ : syracuseStep 9706787 = 14560181) B14560181
theorem B1744271 : Blo 774336 1744271 := bstep (se 1 (by rfl) ⟨1308203, by rfl⟩ : syracuseStep 1744271 = 2616407) B2616407
theorem B1744595 : Blo 774336 1744595 := bstep (se 1 (by rfl) ⟨1308446, by rfl⟩ : syracuseStep 1744595 = 2616893) B2616893
theorem B2793209 : Blo 774336 2793209 := bstep (se 2 (by rfl) ⟨1047453, by rfl⟩ : syracuseStep 2793209 = 2094907) B2094907
theorem B3940163 : Blo 774336 3940163 := bstep (se 1 (by rfl) ⟨2955122, by rfl⟩ : syracuseStep 3940163 = 5910245) B5910245
theorem B12100049 : Blo 774336 12100049 := bstep (se 2 (by rfl) ⟨4537518, by rfl⟩ : syracuseStep 12100049 = 9075037) B9075037
theorem B1745531 : Blo 774336 1745531 := bstep (se 1 (by rfl) ⟨1309148, by rfl⟩ : syracuseStep 1745531 = 2618297) B2618297
theorem B1745657 : Blo 774336 1745657 := bstep (se 2 (by rfl) ⟨654621, by rfl⟩ : syracuseStep 1745657 = 1309243) B1309243
theorem B4727555 : Blo 774336 4727555 := bstep (se 1 (by rfl) ⟨3545666, by rfl⟩ : syracuseStep 4727555 = 7091333) B7091333
theorem B7447403 : Blo 774336 7447403 := bstep (se 1 (by rfl) ⟨5585552, by rfl⟩ : syracuseStep 7447403 = 11171105) B11171105
theorem B15967151 : Blo 774336 15967151 := bstep (se 1 (by rfl) ⟨11975363, by rfl⟩ : syracuseStep 15967151 = 23950727) B23950727
theorem B1745927 : Blo 774336 1745927 := bstep (se 1 (by rfl) ⟨1309445, by rfl⟩ : syracuseStep 1745927 = 2618891) B2618891
theorem B8397875 : Blo 774336 8397875 := bstep (se 1 (by rfl) ⟨6298406, by rfl⟩ : syracuseStep 8397875 = 12596813) B12596813
theorem B1745999 : Blo 774336 1745999 := bstep (se 1 (by rfl) ⟨1309499, by rfl⟩ : syracuseStep 1745999 = 2618999) B2618999
theorem B53880025 : Blo 774336 53880025 := bstep (se 2 (by rfl) ⟨20205009, by rfl⟩ : syracuseStep 53880025 = 40410019) B40410019
theorem B1516907 : Blo 774336 1516907 := bstep (se 1 (by rfl) ⟨1137680, by rfl⟩ : syracuseStep 1516907 = 2275361) B2275361
theorem B1746395 : Blo 774336 1746395 := bstep (se 1 (by rfl) ⟨1309796, by rfl⟩ : syracuseStep 1746395 = 2619593) B2619593
theorem B149038841 : Blo 774336 149038841 := bstep (se 2 (by rfl) ⟨55889565, by rfl⟩ : syracuseStep 149038841 = 111779131) B111779131
theorem B3155807 : Blo 774336 3155807 := bstep (se 1 (by rfl) ⟨2366855, by rfl⟩ : syracuseStep 3155807 = 4733711) B4733711
theorem B1746863 : Blo 774336 1746863 := bstep (se 1 (by rfl) ⟨1310147, by rfl⟩ : syracuseStep 1746863 = 2620295) B2620295
theorem B1747115 : Blo 774336 1747115 := bstep (se 1 (by rfl) ⟨1310336, by rfl⟩ : syracuseStep 1747115 = 2620673) B2620673
theorem B5908787 : Blo 774336 5908787 := bstep (se 1 (by rfl) ⟨4431590, by rfl⟩ : syracuseStep 5908787 = 8863181) B8863181
theorem B2206217 : Blo 774336 2206217 := bstep (se 2 (by rfl) ⟨827331, by rfl⟩ : syracuseStep 2206217 = 1654663) B1654663
theorem B3320345 : Blo 774336 3320345 := bstep (se 2 (by rfl) ⟨1245129, by rfl⟩ : syracuseStep 3320345 = 2490259) B2490259
theorem B1747655 : Blo 774336 1747655 := bstep (se 1 (by rfl) ⟨1310741, by rfl⟩ : syracuseStep 1747655 = 2621483) B2621483
theorem B11938549 : Blo 774336 11938549 := bstep (se 5 (by rfl) ⟨559619, by rfl⟩ : syracuseStep 11938549 = 1119239) B1119239
theorem B5975005 : Blo 774336 5975005 := bstep (se 3 (by rfl) ⟨1120313, by rfl⟩ : syracuseStep 5975005 = 2240627) B2240627
theorem B1748519 : Blo 774336 1748519 := bstep (se 1 (by rfl) ⟨1311389, by rfl⟩ : syracuseStep 1748519 = 2622779) B2622779
theorem B3321643 : Blo 774336 3321643 := bstep (se 1 (by rfl) ⟨2491232, by rfl⟩ : syracuseStep 3321643 = 4982465) B4982465
theorem B1748843 : Blo 774336 1748843 := bstep (se 1 (by rfl) ⟨1311632, by rfl⟩ : syracuseStep 1748843 = 2623265) B2623265
theorem B2994029 : Blo 774336 2994029 := bstep (se 3 (by rfl) ⟨561380, by rfl⟩ : syracuseStep 2994029 = 1122761) B1122761
theorem B1748897 : Blo 774336 1748897 := bstep (se 2 (by rfl) ⟨655836, by rfl⟩ : syracuseStep 1748897 = 1311673) B1311673
theorem B2207675 : Blo 774336 2207675 := bstep (se 1 (by rfl) ⟨1655756, by rfl⟩ : syracuseStep 2207675 = 3311513) B3311513
theorem B1749239 : Blo 774336 1749239 := bstep (se 1 (by rfl) ⟨1311929, by rfl⟩ : syracuseStep 1749239 = 2623859) B2623859
theorem B1749833 : Blo 774336 1749833 := bstep (se 2 (by rfl) ⟨656187, by rfl⟩ : syracuseStep 1749833 = 1312375) B1312375
theorem B3978487 : Blo 774336 3978487 := bstep (se 1 (by rfl) ⟨2983865, by rfl⟩ : syracuseStep 3978487 = 5967731) B5967731
theorem B1750625 : Blo 774336 1750625 := bstep (se 2 (by rfl) ⟨656484, by rfl⟩ : syracuseStep 1750625 = 1312969) B1312969
theorem B10630871 : Blo 774336 10630871 := bstep (se 1 (by rfl) ⟨7973153, by rfl⟩ : syracuseStep 10630871 = 15946307) B15946307
theorem B3192605 : Blo 774336 3192605 := bstep (se 3 (by rfl) ⟨598613, by rfl⟩ : syracuseStep 3192605 = 1197227) B1197227
theorem B2799467 : Blo 774336 2799467 := bstep (se 1 (by rfl) ⟨2099600, by rfl⟩ : syracuseStep 2799467 = 4199201) B4199201
theorem B4962167 : Blo 774336 4962167 := bstep (se 1 (by rfl) ⟨3721625, by rfl⟩ : syracuseStep 4962167 = 7443251) B7443251
theorem B1750967 : Blo 774336 1750967 := bstep (se 1 (by rfl) ⟨1313225, by rfl⟩ : syracuseStep 1750967 = 2626451) B2626451
theorem B2799697 : Blo 774336 2799697 := bstep (se 2 (by rfl) ⟨1049886, by rfl⟩ : syracuseStep 2799697 = 2099773) B2099773
theorem B181778519 : Blo 774336 181778519 := bstep (se 1 (by rfl) ⟨136333889, by rfl⟩ : syracuseStep 181778519 = 272667779) B272667779
theorem B1161647 : Blo 774336 1161647 := bstep (se 1 (by rfl) ⟨871235, by rfl⟩ : syracuseStep 1161647 = 1742471) B1742471
theorem B1161737 : Blo 774336 1161737 := bstep (se 2 (by rfl) ⟨435651, by rfl⟩ : syracuseStep 1161737 = 871303) B871303
theorem B1161767 : Blo 774336 1161767 := bstep (se 1 (by rfl) ⟨871325, by rfl⟩ : syracuseStep 1161767 = 1742651) B1742651
theorem B1161851 : Blo 774336 1161851 := bstep (se 1 (by rfl) ⟨871388, by rfl⟩ : syracuseStep 1161851 = 1742777) B1742777
theorem B1161977 : Blo 774336 1161977 := bstep (se 2 (by rfl) ⟨435741, by rfl⟩ : syracuseStep 1161977 = 871483) B871483
theorem B1162079 : Blo 774336 1162079 := bstep (se 1 (by rfl) ⟨871559, by rfl⟩ : syracuseStep 1162079 = 1743119) B1743119
theorem B1162091 : Blo 774336 1162091 := bstep (se 1 (by rfl) ⟨871568, by rfl⟩ : syracuseStep 1162091 = 1743137) B1743137
theorem B3980215 : Blo 774336 3980215 := bstep (se 1 (by rfl) ⟨2985161, by rfl⟩ : syracuseStep 3980215 = 5970323) B5970323
theorem B1653817 : Blo 774336 1653817 := bstep (se 2 (by rfl) ⟨620181, by rfl⟩ : syracuseStep 1653817 = 1240363) B1240363
theorem B1162319 : Blo 774336 1162319 := bstep (se 1 (by rfl) ⟨871739, by rfl⟩ : syracuseStep 1162319 = 1743479) B1743479
theorem B1162439 : Blo 774336 1162439 := bstep (se 1 (by rfl) ⟨871829, by rfl⟩ : syracuseStep 1162439 = 1743659) B1743659
theorem B4472011 : Blo 774336 4472011 := bstep (se 1 (by rfl) ⟨3354008, by rfl⟩ : syracuseStep 4472011 = 6708017) B6708017
theorem B2800907 : Blo 774336 2800907 := bstep (se 1 (by rfl) ⟨2100680, by rfl⟩ : syracuseStep 2800907 = 4201361) B4201361
theorem B5586191 : Blo 774336 5586191 := bstep (se 1 (by rfl) ⟨4189643, by rfl⟩ : syracuseStep 5586191 = 8379287) B8379287
theorem B1326431 : Blo 774336 1326431 := bstep (se 1 (by rfl) ⟨994823, by rfl⟩ : syracuseStep 1326431 = 1989647) B1989647
theorem B1162601 : Blo 774336 1162601 := bstep (se 2 (by rfl) ⟨435975, by rfl⟩ : syracuseStep 1162601 = 871951) B871951
theorem B1162679 : Blo 774336 1162679 := bstep (se 1 (by rfl) ⟨872009, by rfl⟩ : syracuseStep 1162679 = 1744019) B1744019
theorem B1162715 : Blo 774336 1162715 := bstep (se 1 (by rfl) ⟨872036, by rfl⟩ : syracuseStep 1162715 = 1744073) B1744073
theorem B1163183 : Blo 774336 1163183 := bstep (se 1 (by rfl) ⟨872387, by rfl⟩ : syracuseStep 1163183 = 1744775) B1744775
theorem B1261495 : Blo 774336 1261495 := bstep (se 1 (by rfl) ⟨946121, by rfl⟩ : syracuseStep 1261495 = 1892243) B1892243
theorem B1163273 : Blo 774336 1163273 := bstep (se 2 (by rfl) ⟨436227, by rfl⟩ : syracuseStep 1163273 = 872455) B872455
theorem B5980175 : Blo 774336 5980175 := bstep (se 1 (by rfl) ⟨4485131, by rfl⟩ : syracuseStep 5980175 = 8970263) B8970263
theorem B1163303 : Blo 774336 1163303 := bstep (se 1 (by rfl) ⟨872477, by rfl⟩ : syracuseStep 1163303 = 1744955) B1744955
theorem B1163387 : Blo 774336 1163387 := bstep (se 1 (by rfl) ⟨872540, by rfl⟩ : syracuseStep 1163387 = 1745081) B1745081
theorem B1163513 : Blo 774336 1163513 := bstep (se 2 (by rfl) ⟨436317, by rfl⟩ : syracuseStep 1163513 = 872635) B872635
theorem B1163615 : Blo 774336 1163615 := bstep (se 1 (by rfl) ⟨872711, by rfl⟩ : syracuseStep 1163615 = 1745423) B1745423
theorem B1163627 : Blo 774336 1163627 := bstep (se 1 (by rfl) ⟨872720, by rfl⟩ : syracuseStep 1163627 = 1745441) B1745441
theorem B9585211 : Blo 774336 9585211 := bstep (se 1 (by rfl) ⟨7188908, by rfl⟩ : syracuseStep 9585211 = 14377817) B14377817
theorem B2802235 : Blo 774336 2802235 := bstep (se 1 (by rfl) ⟨2101676, by rfl⟩ : syracuseStep 2802235 = 4203353) B4203353
theorem B1163855 : Blo 774336 1163855 := bstep (se 1 (by rfl) ⟨872891, by rfl⟩ : syracuseStep 1163855 = 1745783) B1745783
theorem B1163975 : Blo 774336 1163975 := bstep (se 1 (by rfl) ⟨872981, by rfl⟩ : syracuseStep 1163975 = 1745963) B1745963
theorem B1164137 : Blo 774336 1164137 := bstep (se 2 (by rfl) ⟨436551, by rfl⟩ : syracuseStep 1164137 = 873103) B873103
theorem B1164215 : Blo 774336 1164215 := bstep (se 1 (by rfl) ⟨873161, by rfl⟩ : syracuseStep 1164215 = 1746323) B1746323
theorem B1164251 : Blo 774336 1164251 := bstep (se 1 (by rfl) ⟨873188, by rfl⟩ : syracuseStep 1164251 = 1746377) B1746377
theorem B7095347 : Blo 774336 7095347 := bstep (se 1 (by rfl) ⟨5321510, by rfl⟩ : syracuseStep 7095347 = 10643021) B10643021
theorem B6309017 : Blo 774336 6309017 := bstep (se 2 (by rfl) ⟨2365881, by rfl⟩ : syracuseStep 6309017 = 4731763) B4731763
theorem B1656055 : Blo 774336 1656055 := bstep (se 1 (by rfl) ⟨1242041, by rfl⟩ : syracuseStep 1656055 = 2484083) B2484083
theorem B1164719 : Blo 774336 1164719 := bstep (se 1 (by rfl) ⟨873539, by rfl⟩ : syracuseStep 1164719 = 1747079) B1747079
theorem B1164809 : Blo 774336 1164809 := bstep (se 2 (by rfl) ⟨436803, by rfl⟩ : syracuseStep 1164809 = 873607) B873607
theorem B1164839 : Blo 774336 1164839 := bstep (se 1 (by rfl) ⟨873629, by rfl⟩ : syracuseStep 1164839 = 1747259) B1747259
theorem B5883515 : Blo 774336 5883515 := bstep (se 1 (by rfl) ⟨4412636, by rfl⟩ : syracuseStep 5883515 = 8825273) B8825273
theorem B1164923 : Blo 774336 1164923 := bstep (se 1 (by rfl) ⟨873692, by rfl⟩ : syracuseStep 1164923 = 1747385) B1747385
theorem B1165049 : Blo 774336 1165049 := bstep (se 2 (by rfl) ⟨436893, by rfl⟩ : syracuseStep 1165049 = 873787) B873787
theorem B1328969 : Blo 774336 1328969 := bstep (se 2 (by rfl) ⟨498363, by rfl⟩ : syracuseStep 1328969 = 996727) B996727
theorem B1165151 : Blo 774336 1165151 := bstep (se 1 (by rfl) ⟨873863, by rfl⟩ : syracuseStep 1165151 = 1747727) B1747727
theorem B1165163 : Blo 774336 1165163 := bstep (se 1 (by rfl) ⟨873872, by rfl⟩ : syracuseStep 1165163 = 1747745) B1747745
theorem B1165391 : Blo 774336 1165391 := bstep (se 1 (by rfl) ⟨874043, by rfl⟩ : syracuseStep 1165391 = 1748087) B1748087
theorem B1165511 : Blo 774336 1165511 := bstep (se 1 (by rfl) ⟨874133, by rfl⟩ : syracuseStep 1165511 = 1748267) B1748267
theorem B1165673 : Blo 774336 1165673 := bstep (se 2 (by rfl) ⟨437127, by rfl⟩ : syracuseStep 1165673 = 874255) B874255
theorem B1165751 : Blo 774336 1165751 := bstep (se 1 (by rfl) ⟨874313, by rfl⟩ : syracuseStep 1165751 = 1748627) B1748627
theorem B4966859 : Blo 774336 4966859 := bstep (se 1 (by rfl) ⟨3725144, by rfl⟩ : syracuseStep 4966859 = 7450289) B7450289
theorem B1165787 : Blo 774336 1165787 := bstep (se 1 (by rfl) ⟨874340, by rfl⟩ : syracuseStep 1165787 = 1748681) B1748681
theorem B3983905 : Blo 774336 3983905 := bstep (se 2 (by rfl) ⟨1493964, by rfl⟩ : syracuseStep 3983905 = 2987929) B2987929
theorem B2214611 : Blo 774336 2214611 := bstep (se 1 (by rfl) ⟨1660958, by rfl⟩ : syracuseStep 2214611 = 3321917) B3321917
theorem B26889029 : Blo 774336 26889029 := bstep (se 4 (by rfl) ⟨2520846, by rfl⟩ : syracuseStep 26889029 = 5041693) B5041693
theorem B1166255 : Blo 774336 1166255 := bstep (se 1 (by rfl) ⟨874691, by rfl⟩ : syracuseStep 1166255 = 1749383) B1749383
theorem B2214839 : Blo 774336 2214839 := bstep (se 1 (by rfl) ⟨1661129, by rfl⟩ : syracuseStep 2214839 = 3322259) B3322259
theorem B8834021 : Blo 774336 8834021 := bstep (se 4 (by rfl) ⟨828189, by rfl⟩ : syracuseStep 8834021 = 1656379) B1656379
theorem B1166345 : Blo 774336 1166345 := bstep (se 2 (by rfl) ⟨437379, by rfl⟩ : syracuseStep 1166345 = 874759) B874759
theorem B1166375 : Blo 774336 1166375 := bstep (se 1 (by rfl) ⟨874781, by rfl⟩ : syracuseStep 1166375 = 1749563) B1749563
theorem B1166459 : Blo 774336 1166459 := bstep (se 1 (by rfl) ⟨874844, by rfl⟩ : syracuseStep 1166459 = 1749689) B1749689
theorem B3722435 : Blo 774336 3722435 := bstep (se 1 (by rfl) ⟨2791826, by rfl⟩ : syracuseStep 3722435 = 5583653) B5583653
theorem B1166585 : Blo 774336 1166585 := bstep (se 2 (by rfl) ⟨437469, by rfl⟩ : syracuseStep 1166585 = 874939) B874939
theorem B1166687 : Blo 774336 1166687 := bstep (se 1 (by rfl) ⟨875015, by rfl⟩ : syracuseStep 1166687 = 1750031) B1750031
theorem B1166699 : Blo 774336 1166699 := bstep (se 1 (by rfl) ⟨875024, by rfl⟩ : syracuseStep 1166699 = 1750049) B1750049
theorem B1330651 : Blo 774336 1330651 := bstep (se 1 (by rfl) ⟨997988, by rfl⟩ : syracuseStep 1330651 = 1995977) B1995977
theorem B1166927 : Blo 774336 1166927 := bstep (se 1 (by rfl) ⟨875195, by rfl⟩ : syracuseStep 1166927 = 1750391) B1750391
theorem B872059 : Blo 774336 872059 := bstep (se 1 (by rfl) ⟨654044, by rfl⟩ : syracuseStep 872059 = 1308089) B1308089
theorem B4476539 : Blo 774336 4476539 := bstep (se 1 (by rfl) ⟨3357404, by rfl⟩ : syracuseStep 4476539 = 6714809) B6714809
theorem B2215613 : Blo 774336 2215613 := bstep (se 3 (by rfl) ⟨415427, by rfl⟩ : syracuseStep 2215613 = 830855) B830855
theorem B1167047 : Blo 774336 1167047 := bstep (se 1 (by rfl) ⟨875285, by rfl⟩ : syracuseStep 1167047 = 1750571) B1750571
theorem B1167209 : Blo 774336 1167209 := bstep (se 2 (by rfl) ⟨437703, by rfl⟩ : syracuseStep 1167209 = 875407) B875407
theorem B1167287 : Blo 774336 1167287 := bstep (se 1 (by rfl) ⟨875465, by rfl⟩ : syracuseStep 1167287 = 1750931) B1750931
theorem B1167323 : Blo 774336 1167323 := bstep (se 1 (by rfl) ⟨875492, by rfl⟩ : syracuseStep 1167323 = 1750985) B1750985
theorem B872527 : Blo 774336 872527 := bstep (se 1 (by rfl) ⟨654395, by rfl⟩ : syracuseStep 872527 = 1308791) B1308791
theorem B774343 : Blo 774336 774343 := bstep (se 1 (by rfl) ⟨580757, by rfl⟩ : syracuseStep 774343 = 1161515) B1161515
theorem B774363 : Blo 774336 774363 := bstep (se 1 (by rfl) ⟨580772, by rfl⟩ : syracuseStep 774363 = 1161545) B1161545
theorem B774439 : Blo 774336 774439 := bstep (se 1 (by rfl) ⟨580829, by rfl⟩ : syracuseStep 774439 = 1161659) B1161659
theorem B774479 : Blo 774336 774479 := bstep (se 1 (by rfl) ⟨580859, by rfl⟩ : syracuseStep 774479 = 1161719) B1161719
theorem B774495 : Blo 774336 774495 := bstep (se 1 (by rfl) ⟨580871, by rfl⟩ : syracuseStep 774495 = 1161743) B1161743
theorem B2216297 : Blo 774336 2216297 := bstep (se 2 (by rfl) ⟨831111, by rfl⟩ : syracuseStep 2216297 = 1662223) B1662223
theorem B774523 : Blo 774336 774523 := bstep (se 1 (by rfl) ⟨580892, by rfl⟩ : syracuseStep 774523 = 1161785) B1161785
theorem B774575 : Blo 774336 774575 := bstep (se 1 (by rfl) ⟨580931, by rfl⟩ : syracuseStep 774575 = 1161863) B1161863
theorem B774599 : Blo 774336 774599 := bstep (se 1 (by rfl) ⟨580949, by rfl⟩ : syracuseStep 774599 = 1161899) B1161899
theorem B774619 : Blo 774336 774619 := bstep (se 1 (by rfl) ⟨580964, by rfl⟩ : syracuseStep 774619 = 1161929) B1161929
theorem B872923 : Blo 774336 872923 := bstep (se 1 (by rfl) ⟨654692, by rfl⟩ : syracuseStep 872923 = 1309385) B1309385
theorem B4968985 : Blo 774336 4968985 := bstep (se 2 (by rfl) ⟨1863369, by rfl⟩ : syracuseStep 4968985 = 3726739) B3726739
theorem B774695 : Blo 774336 774695 := bstep (se 1 (by rfl) ⟨581021, by rfl⟩ : syracuseStep 774695 = 1162043) B1162043
theorem B774735 : Blo 774336 774735 := bstep (se 1 (by rfl) ⟨581051, by rfl⟩ : syracuseStep 774735 = 1162103) B1162103
theorem B774751 : Blo 774336 774751 := bstep (se 1 (by rfl) ⟨581063, by rfl⟩ : syracuseStep 774751 = 1162127) B1162127
theorem B774779 : Blo 774336 774779 := bstep (se 1 (by rfl) ⟨581084, by rfl⟩ : syracuseStep 774779 = 1162169) B1162169
theorem B774831 : Blo 774336 774831 := bstep (se 1 (by rfl) ⟨581123, by rfl⟩ : syracuseStep 774831 = 1162247) B1162247
theorem B774855 : Blo 774336 774855 := bstep (se 1 (by rfl) ⟨581141, by rfl⟩ : syracuseStep 774855 = 1162283) B1162283
theorem B774875 : Blo 774336 774875 := bstep (se 1 (by rfl) ⟨581156, by rfl⟩ : syracuseStep 774875 = 1162313) B1162313
theorem B7099139 : Blo 774336 7099139 := bstep (se 1 (by rfl) ⟨5324354, by rfl⟩ : syracuseStep 7099139 = 10648709) B10648709
theorem B774951 : Blo 774336 774951 := bstep (se 1 (by rfl) ⟨581213, by rfl⟩ : syracuseStep 774951 = 1162427) B1162427
theorem B774991 : Blo 774336 774991 := bstep (se 1 (by rfl) ⟨581243, by rfl⟩ : syracuseStep 774991 = 1162487) B1162487
theorem B775007 : Blo 774336 775007 := bstep (se 1 (by rfl) ⟨581255, by rfl⟩ : syracuseStep 775007 = 1162511) B1162511
theorem B775035 : Blo 774336 775035 := bstep (se 1 (by rfl) ⟨581276, by rfl⟩ : syracuseStep 775035 = 1162553) B1162553
theorem B775087 : Blo 774336 775087 := bstep (se 1 (by rfl) ⟨581315, by rfl⟩ : syracuseStep 775087 = 1162631) B1162631
theorem B873391 : Blo 774336 873391 := bstep (se 1 (by rfl) ⟨655043, by rfl⟩ : syracuseStep 873391 = 1310087) B1310087
theorem B775111 : Blo 774336 775111 := bstep (se 1 (by rfl) ⟨581333, by rfl⟩ : syracuseStep 775111 = 1162667) B1162667
theorem B775131 : Blo 774336 775131 := bstep (se 1 (by rfl) ⟨581348, by rfl⟩ : syracuseStep 775131 = 1162697) B1162697
theorem B775207 : Blo 774336 775207 := bstep (se 1 (by rfl) ⟨581405, by rfl⟩ : syracuseStep 775207 = 1162811) B1162811
theorem B1725497 : Blo 774336 1725497 := bstep (se 2 (by rfl) ⟨647061, by rfl⟩ : syracuseStep 1725497 = 1294123) B1294123
theorem B7558211 : Blo 774336 7558211 := bstep (se 1 (by rfl) ⟨5668658, by rfl⟩ : syracuseStep 7558211 = 11337317) B11337317
theorem B775247 : Blo 774336 775247 := bstep (se 1 (by rfl) ⟨581435, by rfl⟩ : syracuseStep 775247 = 1162871) B1162871
theorem B775263 : Blo 774336 775263 := bstep (se 1 (by rfl) ⟨581447, by rfl⟩ : syracuseStep 775263 = 1162895) B1162895
theorem B775291 : Blo 774336 775291 := bstep (se 1 (by rfl) ⟨581468, by rfl⟩ : syracuseStep 775291 = 1162937) B1162937
theorem B775343 : Blo 774336 775343 := bstep (se 1 (by rfl) ⟨581507, by rfl⟩ : syracuseStep 775343 = 1163015) B1163015
theorem B775367 : Blo 774336 775367 := bstep (se 1 (by rfl) ⟨581525, by rfl⟩ : syracuseStep 775367 = 1163051) B1163051
theorem B775387 : Blo 774336 775387 := bstep (se 1 (by rfl) ⟨581540, by rfl⟩ : syracuseStep 775387 = 1163081) B1163081
theorem B775463 : Blo 774336 775463 := bstep (se 1 (by rfl) ⟨581597, by rfl⟩ : syracuseStep 775463 = 1163195) B1163195
theorem B775503 : Blo 774336 775503 := bstep (se 1 (by rfl) ⟨581627, by rfl⟩ : syracuseStep 775503 = 1163255) B1163255
theorem B775519 : Blo 774336 775519 := bstep (se 1 (by rfl) ⟨581639, by rfl⟩ : syracuseStep 775519 = 1163279) B1163279
theorem B873823 : Blo 774336 873823 := bstep (se 1 (by rfl) ⟨655367, by rfl⟩ : syracuseStep 873823 = 1310735) B1310735
theorem B775547 : Blo 774336 775547 := bstep (se 1 (by rfl) ⟨581660, by rfl⟩ : syracuseStep 775547 = 1163321) B1163321
theorem B775599 : Blo 774336 775599 := bstep (se 1 (by rfl) ⟨581699, by rfl⟩ : syracuseStep 775599 = 1163399) B1163399
theorem B775623 : Blo 774336 775623 := bstep (se 1 (by rfl) ⟨581717, by rfl⟩ : syracuseStep 775623 = 1163435) B1163435
theorem B3921371 : Blo 774336 3921371 := bstep (se 1 (by rfl) ⟨2941028, by rfl⟩ : syracuseStep 3921371 = 5882057) B5882057
theorem B775643 : Blo 774336 775643 := bstep (se 1 (by rfl) ⟨581732, by rfl⟩ : syracuseStep 775643 = 1163465) B1163465
theorem B775719 : Blo 774336 775719 := bstep (se 1 (by rfl) ⟨581789, by rfl⟩ : syracuseStep 775719 = 1163579) B1163579
theorem B775759 : Blo 774336 775759 := bstep (se 1 (by rfl) ⟨581819, by rfl⟩ : syracuseStep 775759 = 1163639) B1163639
theorem B775775 : Blo 774336 775775 := bstep (se 1 (by rfl) ⟨581831, by rfl⟩ : syracuseStep 775775 = 1163663) B1163663
theorem B775803 : Blo 774336 775803 := bstep (se 1 (by rfl) ⟨581852, by rfl⟩ : syracuseStep 775803 = 1163705) B1163705
theorem B775855 : Blo 774336 775855 := bstep (se 1 (by rfl) ⟨581891, by rfl⟩ : syracuseStep 775855 = 1163783) B1163783
theorem B775879 : Blo 774336 775879 := bstep (se 1 (by rfl) ⟨581909, by rfl⟩ : syracuseStep 775879 = 1163819) B1163819
theorem B874183 : Blo 774336 874183 := bstep (se 1 (by rfl) ⟨655637, by rfl⟩ : syracuseStep 874183 = 1311275) B1311275
theorem B775899 : Blo 774336 775899 := bstep (se 1 (by rfl) ⟨581924, by rfl⟩ : syracuseStep 775899 = 1163849) B1163849
theorem B775975 : Blo 774336 775975 := bstep (se 1 (by rfl) ⟨581981, by rfl⟩ : syracuseStep 775975 = 1163963) B1163963
theorem B776015 : Blo 774336 776015 := bstep (se 1 (by rfl) ⟨582011, by rfl⟩ : syracuseStep 776015 = 1164023) B1164023
theorem B776031 : Blo 774336 776031 := bstep (se 1 (by rfl) ⟨582023, by rfl⟩ : syracuseStep 776031 = 1164047) B1164047
theorem B776059 : Blo 774336 776059 := bstep (se 1 (by rfl) ⟨582044, by rfl⟩ : syracuseStep 776059 = 1164089) B1164089
theorem B776111 : Blo 774336 776111 := bstep (se 1 (by rfl) ⟨582083, by rfl⟩ : syracuseStep 776111 = 1164167) B1164167
theorem B3921857 : Blo 774336 3921857 := bstep (se 2 (by rfl) ⟨1470696, by rfl⟩ : syracuseStep 3921857 = 2941393) B2941393
theorem B776135 : Blo 774336 776135 := bstep (se 1 (by rfl) ⟨582101, by rfl⟩ : syracuseStep 776135 = 1164203) B1164203
theorem B776155 : Blo 774336 776155 := bstep (se 1 (by rfl) ⟨582116, by rfl⟩ : syracuseStep 776155 = 1164233) B1164233
theorem B776231 : Blo 774336 776231 := bstep (se 1 (by rfl) ⟨582173, by rfl⟩ : syracuseStep 776231 = 1164347) B1164347
theorem B776271 : Blo 774336 776271 := bstep (se 1 (by rfl) ⟨582203, by rfl⟩ : syracuseStep 776271 = 1164407) B1164407
theorem B776287 : Blo 774336 776287 := bstep (se 1 (by rfl) ⟨582215, by rfl⟩ : syracuseStep 776287 = 1164431) B1164431
theorem B776315 : Blo 774336 776315 := bstep (se 1 (by rfl) ⟨582236, by rfl⟩ : syracuseStep 776315 = 1164473) B1164473
theorem B776367 : Blo 774336 776367 := bstep (se 1 (by rfl) ⟨582275, by rfl⟩ : syracuseStep 776367 = 1164551) B1164551
theorem B776391 : Blo 774336 776391 := bstep (se 1 (by rfl) ⟨582293, by rfl⟩ : syracuseStep 776391 = 1164587) B1164587
theorem B776411 : Blo 774336 776411 := bstep (se 1 (by rfl) ⟨582308, by rfl⟩ : syracuseStep 776411 = 1164617) B1164617
theorem B11163905 : Blo 774336 11163905 := bstep (se 2 (by rfl) ⟨4186464, by rfl⟩ : syracuseStep 11163905 = 8372929) B8372929
theorem B776487 : Blo 774336 776487 := bstep (se 1 (by rfl) ⟨582365, by rfl⟩ : syracuseStep 776487 = 1164731) B1164731
theorem B776527 : Blo 774336 776527 := bstep (se 1 (by rfl) ⟨582395, by rfl⟩ : syracuseStep 776527 = 1164791) B1164791
theorem B776543 : Blo 774336 776543 := bstep (se 1 (by rfl) ⟨582407, by rfl⟩ : syracuseStep 776543 = 1164815) B1164815
theorem B1890665 : Blo 774336 1890665 := bstep (se 2 (by rfl) ⟨708999, by rfl⟩ : syracuseStep 1890665 = 1417999) B1417999
theorem B776571 : Blo 774336 776571 := bstep (se 1 (by rfl) ⟨582428, by rfl⟩ : syracuseStep 776571 = 1164857) B1164857
theorem B776623 : Blo 774336 776623 := bstep (se 1 (by rfl) ⟨582467, by rfl⟩ : syracuseStep 776623 = 1164935) B1164935
theorem B776647 : Blo 774336 776647 := bstep (se 1 (by rfl) ⟨582485, by rfl⟩ : syracuseStep 776647 = 1164971) B1164971
theorem B776667 : Blo 774336 776667 := bstep (se 1 (by rfl) ⟨582500, by rfl⟩ : syracuseStep 776667 = 1165001) B1165001
theorem B776743 : Blo 774336 776743 := bstep (se 1 (by rfl) ⟨582557, by rfl⟩ : syracuseStep 776743 = 1165115) B1165115
theorem B875047 : Blo 774336 875047 := bstep (se 1 (by rfl) ⟨656285, by rfl⟩ : syracuseStep 875047 = 1312571) B1312571
theorem B15096395 : Blo 774336 15096395 := bstep (se 1 (by rfl) ⟨11322296, by rfl⟩ : syracuseStep 15096395 = 22644593) B22644593
theorem B776783 : Blo 774336 776783 := bstep (se 1 (by rfl) ⟨582587, by rfl⟩ : syracuseStep 776783 = 1165175) B1165175
theorem B776799 : Blo 774336 776799 := bstep (se 1 (by rfl) ⟨582599, by rfl⟩ : syracuseStep 776799 = 1165199) B1165199
theorem B776827 : Blo 774336 776827 := bstep (se 1 (by rfl) ⟨582620, by rfl⟩ : syracuseStep 776827 = 1165241) B1165241
theorem B776879 : Blo 774336 776879 := bstep (se 1 (by rfl) ⟨582659, by rfl⟩ : syracuseStep 776879 = 1165319) B1165319
theorem B776903 : Blo 774336 776903 := bstep (se 1 (by rfl) ⟨582677, by rfl⟩ : syracuseStep 776903 = 1165355) B1165355
theorem B776923 : Blo 774336 776923 := bstep (se 1 (by rfl) ⟨582692, by rfl⟩ : syracuseStep 776923 = 1165385) B1165385
theorem B4840195 : Blo 774336 4840195 := bstep (se 1 (by rfl) ⟨3630146, by rfl⟩ : syracuseStep 4840195 = 7260293) B7260293
theorem B5593859 : Blo 774336 5593859 := bstep (se 1 (by rfl) ⟨4195394, by rfl⟩ : syracuseStep 5593859 = 8390789) B8390789
theorem B4971293 : Blo 774336 4971293 := bstep (se 3 (by rfl) ⟨932117, by rfl⟩ : syracuseStep 4971293 = 1864235) B1864235
theorem B776999 : Blo 774336 776999 := bstep (se 1 (by rfl) ⟨582749, by rfl⟩ : syracuseStep 776999 = 1165499) B1165499
theorem B2480969 : Blo 774336 2480969 := bstep (se 2 (by rfl) ⟨930363, by rfl⟩ : syracuseStep 2480969 = 1860727) B1860727
theorem B777039 : Blo 774336 777039 := bstep (se 1 (by rfl) ⟨582779, by rfl⟩ : syracuseStep 777039 = 1165559) B1165559
theorem B777055 : Blo 774336 777055 := bstep (se 1 (by rfl) ⟨582791, by rfl⟩ : syracuseStep 777055 = 1165583) B1165583
theorem B777083 : Blo 774336 777083 := bstep (se 1 (by rfl) ⟨582812, by rfl⟩ : syracuseStep 777083 = 1165625) B1165625
theorem B777135 : Blo 774336 777135 := bstep (se 1 (by rfl) ⟨582851, by rfl⟩ : syracuseStep 777135 = 1165703) B1165703
theorem B777159 : Blo 774336 777159 := bstep (se 1 (by rfl) ⟨582869, by rfl⟩ : syracuseStep 777159 = 1165739) B1165739
theorem B777179 : Blo 774336 777179 := bstep (se 1 (by rfl) ⟨582884, by rfl⟩ : syracuseStep 777179 = 1165769) B1165769
theorem B777255 : Blo 774336 777255 := bstep (se 1 (by rfl) ⟨582941, by rfl⟩ : syracuseStep 777255 = 1165883) B1165883
theorem B777295 : Blo 774336 777295 := bstep (se 1 (by rfl) ⟨582971, by rfl⟩ : syracuseStep 777295 = 1165943) B1165943
theorem B777311 : Blo 774336 777311 := bstep (se 1 (by rfl) ⟨582983, by rfl⟩ : syracuseStep 777311 = 1165967) B1165967
theorem B777339 : Blo 774336 777339 := bstep (se 1 (by rfl) ⟨583004, by rfl⟩ : syracuseStep 777339 = 1166009) B1166009
theorem B777391 : Blo 774336 777391 := bstep (se 1 (by rfl) ⟨583043, by rfl⟩ : syracuseStep 777391 = 1166087) B1166087
theorem B777415 : Blo 774336 777415 := bstep (se 1 (by rfl) ⟨583061, by rfl⟩ : syracuseStep 777415 = 1166123) B1166123
theorem B777435 : Blo 774336 777435 := bstep (se 1 (by rfl) ⟨583076, by rfl⟩ : syracuseStep 777435 = 1166153) B1166153
theorem B777511 : Blo 774336 777511 := bstep (se 1 (by rfl) ⟨583133, by rfl⟩ : syracuseStep 777511 = 1166267) B1166267
theorem B777551 : Blo 774336 777551 := bstep (se 1 (by rfl) ⟨583163, by rfl⟩ : syracuseStep 777551 = 1166327) B1166327
theorem B777567 : Blo 774336 777567 := bstep (se 1 (by rfl) ⟨583175, by rfl⟩ : syracuseStep 777567 = 1166351) B1166351
theorem B777595 : Blo 774336 777595 := bstep (se 1 (by rfl) ⟨583196, by rfl⟩ : syracuseStep 777595 = 1166393) B1166393
theorem B777647 : Blo 774336 777647 := bstep (se 1 (by rfl) ⟨583235, by rfl⟩ : syracuseStep 777647 = 1166471) B1166471
theorem B777671 : Blo 774336 777671 := bstep (se 1 (by rfl) ⟨583253, by rfl⟩ : syracuseStep 777671 = 1166507) B1166507
theorem B777691 : Blo 774336 777691 := bstep (se 1 (by rfl) ⟨583268, by rfl⟩ : syracuseStep 777691 = 1166537) B1166537
theorem B777767 : Blo 774336 777767 := bstep (se 1 (by rfl) ⟨583325, by rfl⟩ : syracuseStep 777767 = 1166651) B1166651
theorem B777807 : Blo 774336 777807 := bstep (se 1 (by rfl) ⟨583355, by rfl⟩ : syracuseStep 777807 = 1166711) B1166711
theorem B777823 : Blo 774336 777823 := bstep (se 1 (by rfl) ⟨583367, by rfl⟩ : syracuseStep 777823 = 1166735) B1166735
theorem B777851 : Blo 774336 777851 := bstep (se 1 (by rfl) ⟨583388, by rfl⟩ : syracuseStep 777851 = 1166777) B1166777
theorem B777903 : Blo 774336 777903 := bstep (se 1 (by rfl) ⟨583427, by rfl⟩ : syracuseStep 777903 = 1166855) B1166855
theorem B2481853 : Blo 774336 2481853 := bstep (se 3 (by rfl) ⟨465347, by rfl⟩ : syracuseStep 2481853 = 930695) B930695
theorem B777927 : Blo 774336 777927 := bstep (se 1 (by rfl) ⟨583445, by rfl⟩ : syracuseStep 777927 = 1166891) B1166891
theorem B777947 : Blo 774336 777947 := bstep (se 1 (by rfl) ⟨583460, by rfl⟩ : syracuseStep 777947 = 1166921) B1166921
theorem B778023 : Blo 774336 778023 := bstep (se 1 (by rfl) ⟨583517, by rfl⟩ : syracuseStep 778023 = 1167035) B1167035
theorem B778063 : Blo 774336 778063 := bstep (se 1 (by rfl) ⟨583547, by rfl⟩ : syracuseStep 778063 = 1167095) B1167095
theorem B778079 : Blo 774336 778079 := bstep (se 1 (by rfl) ⟨583559, by rfl⟩ : syracuseStep 778079 = 1167119) B1167119
theorem B9461623 : Blo 774336 9461623 := bstep (se 1 (by rfl) ⟨7096217, by rfl⟩ : syracuseStep 9461623 = 14192435) B14192435
theorem B778107 : Blo 774336 778107 := bstep (se 1 (by rfl) ⟨583580, by rfl⟩ : syracuseStep 778107 = 1167161) B1167161
theorem B6283169 : Blo 774336 6283169 := bstep (se 2 (by rfl) ⟨2356188, by rfl⟩ : syracuseStep 6283169 = 4712377) B4712377
theorem B778159 : Blo 774336 778159 := bstep (se 1 (by rfl) ⟨583619, by rfl⟩ : syracuseStep 778159 = 1167239) B1167239
theorem B778183 : Blo 774336 778183 := bstep (se 1 (by rfl) ⟨583637, by rfl⟩ : syracuseStep 778183 = 1167275) B1167275
theorem B778203 : Blo 774336 778203 := bstep (se 1 (by rfl) ⟨583652, by rfl⟩ : syracuseStep 778203 = 1167305) B1167305
theorem B1400851 : Blo 774336 1400851 := bstep (se 1 (by rfl) ⟨1050638, by rfl⟩ : syracuseStep 1400851 = 2101277) B2101277
theorem B778279 : Blo 774336 778279 := bstep (se 1 (by rfl) ⟨583709, by rfl⟩ : syracuseStep 778279 = 1167419) B1167419
theorem B778319 : Blo 774336 778319 := bstep (se 1 (by rfl) ⟨583739, by rfl⟩ : syracuseStep 778319 = 1167479) B1167479
theorem B778335 : Blo 774336 778335 := bstep (se 1 (by rfl) ⟨583751, by rfl⟩ : syracuseStep 778335 = 1167503) B1167503
theorem B3924125 : Blo 774336 3924125 := bstep (se 3 (by rfl) ⟨735773, by rfl⟩ : syracuseStep 3924125 = 1471547) B1471547
theorem B6283493 : Blo 774336 6283493 := bstep (se 4 (by rfl) ⟨589077, by rfl⟩ : syracuseStep 6283493 = 1178155) B1178155
theorem B6709819 : Blo 774336 6709819 := bstep (se 1 (by rfl) ⟨5032364, by rfl⟩ : syracuseStep 6709819 = 10064729) B10064729
theorem B7955003 : Blo 774336 7955003 := bstep (se 1 (by rfl) ⟨5966252, by rfl⟩ : syracuseStep 7955003 = 11932505) B11932505
theorem B8839853 : Blo 774336 8839853 := bstep (se 3 (by rfl) ⟨1657472, by rfl⟩ : syracuseStep 8839853 = 3314945) B3314945
theorem B51045299 : Blo 774336 51045299 := bstep (se 1 (by rfl) ⟨38283974, by rfl⟩ : syracuseStep 51045299 = 76567949) B76567949
theorem B2941879 : Blo 774336 2941879 := bstep (se 1 (by rfl) ⟨2206409, by rfl⟩ : syracuseStep 2941879 = 4412819) B4412819
theorem B13231349 : Blo 774336 13231349 := bstep (se 5 (by rfl) ⟨620219, by rfl⟩ : syracuseStep 13231349 = 1240439) B1240439
theorem B2942351 : Blo 774336 2942351 := bstep (se 1 (by rfl) ⟨2206763, by rfl⟩ : syracuseStep 2942351 = 4413527) B4413527
theorem B3925421 : Blo 774336 3925421 := bstep (se 3 (by rfl) ⟨736016, by rfl⟩ : syracuseStep 3925421 = 1472033) B1472033
theorem B4974317 : Blo 774336 4974317 := bstep (se 3 (by rfl) ⟨932684, by rfl⟩ : syracuseStep 4974317 = 1865369) B1865369
theorem B4417375 : Blo 774336 4417375 := bstep (se 1 (by rfl) ⟨3313031, by rfl⟩ : syracuseStep 4417375 = 6626063) B6626063
theorem B4188023 : Blo 774336 4188023 := bstep (se 1 (by rfl) ⟨3141017, by rfl⟩ : syracuseStep 4188023 = 6282035) B6282035
theorem B11954309 : Blo 774336 11954309 := bstep (se 4 (by rfl) ⟨1120716, by rfl⟩ : syracuseStep 11954309 = 2241433) B2241433
theorem B2615543 : Blo 774336 2615543 := bstep (se 1 (by rfl) ⟨1961657, by rfl⟩ : syracuseStep 2615543 = 3923315) B3923315
theorem B2943337 : Blo 774336 2943337 := bstep (se 2 (by rfl) ⟨1103751, by rfl⟩ : syracuseStep 2943337 = 2207503) B2207503
theorem B1960321 : Blo 774336 1960321 := bstep (se 2 (by rfl) ⟨735120, by rfl⟩ : syracuseStep 1960321 = 1470241) B1470241
theorem B2615867 : Blo 774336 2615867 := bstep (se 1 (by rfl) ⟨1961900, by rfl⟩ : syracuseStep 2615867 = 3923801) B3923801
theorem B2943611 : Blo 774336 2943611 := bstep (se 1 (by rfl) ⟨2207708, by rfl⟩ : syracuseStep 2943611 = 4415417) B4415417
theorem B4975289 : Blo 774336 4975289 := bstep (se 2 (by rfl) ⟨1865733, by rfl⟩ : syracuseStep 4975289 = 3731467) B3731467
theorem B4418333 : Blo 774336 4418333 := bstep (se 3 (by rfl) ⟨828437, by rfl⟩ : syracuseStep 4418333 = 1656875) B1656875
theorem B2616137 : Blo 774336 2616137 := bstep (se 2 (by rfl) ⟨981051, by rfl⟩ : syracuseStep 2616137 = 1962103) B1962103
theorem B3927041 : Blo 774336 3927041 := bstep (se 2 (by rfl) ⟨1472640, by rfl⟩ : syracuseStep 3927041 = 2945281) B2945281
theorem B1961131 : Blo 774336 1961131 := bstep (se 1 (by rfl) ⟨1470848, by rfl⟩ : syracuseStep 1961131 = 2941697) B2941697
theorem B6647183 : Blo 774336 6647183 := bstep (se 1 (by rfl) ⟨4985387, by rfl⟩ : syracuseStep 6647183 = 9970775) B9970775
theorem B1961435 : Blo 774336 1961435 := bstep (se 1 (by rfl) ⟨1471076, by rfl⟩ : syracuseStep 1961435 = 2942153) B2942153
theorem B2485723 : Blo 774336 2485723 := bstep (se 1 (by rfl) ⟨1864292, by rfl⟩ : syracuseStep 2485723 = 3728585) B3728585
theorem B3730931 : Blo 774336 3730931 := bstep (se 1 (by rfl) ⟨2798198, by rfl⟩ : syracuseStep 3730931 = 5596397) B5596397
theorem B3731143 : Blo 774336 3731143 := bstep (se 1 (by rfl) ⟨2798357, by rfl⟩ : syracuseStep 3731143 = 5596715) B5596715
theorem B3731159 : Blo 774336 3731159 := bstep (se 1 (by rfl) ⟨2798369, by rfl⟩ : syracuseStep 3731159 = 5596739) B5596739
theorem B42430169 : Blo 774336 42430169 := bstep (se 2 (by rfl) ⟨15911313, by rfl⟩ : syracuseStep 42430169 = 31822627) B31822627
theorem B4976417 : Blo 774336 4976417 := bstep (se 2 (by rfl) ⟨1866156, by rfl⟩ : syracuseStep 4976417 = 3732313) B3732313
theorem B3927851 : Blo 774336 3927851 := bstep (se 1 (by rfl) ⟨2945888, by rfl⟩ : syracuseStep 3927851 = 5891777) B5891777
theorem B22409095 : Blo 774336 22409095 := bstep (se 1 (by rfl) ⟨16806821, by rfl⟩ : syracuseStep 22409095 = 33613643) B33613643
theorem B2355119 : Blo 774336 2355119 := bstep (se 1 (by rfl) ⟨1766339, by rfl⟩ : syracuseStep 2355119 = 3532679) B3532679
theorem B2617271 : Blo 774336 2617271 := bstep (se 1 (by rfl) ⟨1962953, by rfl⟩ : syracuseStep 2617271 = 3925907) B3925907
theorem B7172027 : Blo 774336 7172027 := bstep (se 1 (by rfl) ⟨5379020, by rfl⟩ : syracuseStep 7172027 = 10758041) B10758041
theorem B13463567 : Blo 774336 13463567 := bstep (se 1 (by rfl) ⟨10097675, by rfl⟩ : syracuseStep 13463567 = 20195351) B20195351
theorem B19853585 : Blo 774336 19853585 := bstep (se 2 (by rfl) ⟨7445094, by rfl⟩ : syracuseStep 19853585 = 14890189) B14890189
theorem B1306975 : Blo 774336 1306975 := bstep (se 1 (by rfl) ⟨980231, by rfl⟩ : syracuseStep 1306975 = 1960463) B1960463
theorem B1307063 : Blo 774336 1307063 := bstep (se 1 (by rfl) ⟨980297, by rfl⟩ : syracuseStep 1307063 = 1960595) B1960595
theorem B2617865 : Blo 774336 2617865 := bstep (se 2 (by rfl) ⟨981699, by rfl⟩ : syracuseStep 2617865 = 1963399) B1963399
theorem B1766137 : Blo 774336 1766137 := bstep (se 2 (by rfl) ⟨662301, by rfl⟩ : syracuseStep 1766137 = 1324603) B1324603
theorem B1241849 : Blo 774336 1241849 := bstep (se 2 (by rfl) ⟨465693, by rfl⟩ : syracuseStep 1241849 = 931387) B931387
theorem B1962913 : Blo 774336 1962913 := bstep (se 2 (by rfl) ⟨736092, by rfl⟩ : syracuseStep 1962913 = 1472185) B1472185
theorem B10777519 : Blo 774336 10777519 := bstep (se 1 (by rfl) ⟨8083139, by rfl⟩ : syracuseStep 10777519 = 16166279) B16166279
theorem B1307657 : Blo 774336 1307657 := bstep (se 2 (by rfl) ⟨490371, by rfl⟩ : syracuseStep 1307657 = 980743) B980743
theorem B1307819 : Blo 774336 1307819 := bstep (se 1 (by rfl) ⟨980864, by rfl⟩ : syracuseStep 1307819 = 1961729) B1961729
theorem B1471699 : Blo 774336 1471699 := bstep (se 1 (by rfl) ⟨1103774, by rfl⟩ : syracuseStep 1471699 = 2207549) B2207549
theorem B2618729 : Blo 774336 2618729 := bstep (se 2 (by rfl) ⟨982023, by rfl⟩ : syracuseStep 2618729 = 1964047) B1964047
theorem B1471927 : Blo 774336 1471927 := bstep (se 1 (by rfl) ⟨1103945, by rfl⟩ : syracuseStep 1471927 = 2207891) B2207891
theorem B11171333 : Blo 774336 11171333 := bstep (se 4 (by rfl) ⟨1047312, by rfl⟩ : syracuseStep 11171333 = 2094625) B2094625
theorem B1308217 : Blo 774336 1308217 := bstep (se 2 (by rfl) ⟨490581, by rfl⟩ : syracuseStep 1308217 = 981163) B981163
theorem B1308359 : Blo 774336 1308359 := bstep (se 1 (by rfl) ⟨981269, by rfl⟩ : syracuseStep 1308359 = 1962539) B1962539
theorem B1308521 : Blo 774336 1308521 := bstep (se 2 (by rfl) ⟨490695, by rfl⟩ : syracuseStep 1308521 = 981391) B981391
theorem B2619323 : Blo 774336 2619323 := bstep (se 1 (by rfl) ⟨1964492, by rfl⟩ : syracuseStep 2619323 = 3928985) B3928985
theorem B1472519 : Blo 774336 1472519 := bstep (se 1 (by rfl) ⟨1104389, by rfl⟩ : syracuseStep 1472519 = 2208779) B2208779
theorem B3930119 : Blo 774336 3930119 := bstep (se 1 (by rfl) ⟨2947589, by rfl⟩ : syracuseStep 3930119 = 5895179) B5895179
theorem B3733619 : Blo 774336 3733619 := bstep (se 1 (by rfl) ⟨2800214, by rfl⟩ : syracuseStep 3733619 = 5600429) B5600429
theorem B1243259 : Blo 774336 1243259 := bstep (se 1 (by rfl) ⟨932444, by rfl⟩ : syracuseStep 1243259 = 1864889) B1864889
theorem B2947225 : Blo 774336 2947225 := bstep (se 2 (by rfl) ⟨1105209, by rfl⟩ : syracuseStep 2947225 = 2210419) B2210419
theorem B8976541 : Blo 774336 8976541 := bstep (se 3 (by rfl) ⟨1683101, by rfl⟩ : syracuseStep 8976541 = 3366203) B3366203
theorem B1308919 : Blo 774336 1308919 := bstep (se 1 (by rfl) ⟨981689, by rfl⟩ : syracuseStep 1308919 = 1963379) B1963379
theorem B1309115 : Blo 774336 1309115 := bstep (se 1 (by rfl) ⟨981836, by rfl⟩ : syracuseStep 1309115 = 1963673) B1963673
theorem B2947529 : Blo 774336 2947529 := bstep (se 2 (by rfl) ⟨1105323, by rfl⟩ : syracuseStep 2947529 = 2210647) B2210647
theorem B3930605 : Blo 774336 3930605 := bstep (se 3 (by rfl) ⟨736988, by rfl⟩ : syracuseStep 3930605 = 1473977) B1473977
theorem B1309223 : Blo 774336 1309223 := bstep (se 1 (by rfl) ⟨981917, by rfl⟩ : syracuseStep 1309223 = 1963835) B1963835
theorem B1309513 : Blo 774336 1309513 := bstep (se 2 (by rfl) ⟨491067, by rfl⟩ : syracuseStep 1309513 = 982135) B982135
theorem B2489183 : Blo 774336 2489183 := bstep (se 1 (by rfl) ⟨1866887, by rfl⟩ : syracuseStep 2489183 = 3733775) B3733775
theorem B1473385 : Blo 774336 1473385 := bstep (se 2 (by rfl) ⟨552519, by rfl⟩ : syracuseStep 1473385 = 1105039) B1105039
theorem B1309547 : Blo 774336 1309547 := bstep (se 1 (by rfl) ⟨982160, by rfl⟩ : syracuseStep 1309547 = 1964321) B1964321
theorem B5307281 : Blo 774336 5307281 := bstep (se 2 (by rfl) ⟨1990230, by rfl⟩ : syracuseStep 5307281 = 3980461) B3980461
theorem B2948015 : Blo 774336 2948015 := bstep (se 1 (by rfl) ⟨2211011, by rfl⟩ : syracuseStep 2948015 = 4422023) B4422023
theorem B1473545 : Blo 774336 1473545 := bstep (se 2 (by rfl) ⟨552579, by rfl⟩ : syracuseStep 1473545 = 1105159) B1105159
theorem B1571879 : Blo 774336 1571879 := bstep (se 1 (by rfl) ⟨1178909, by rfl⟩ : syracuseStep 1571879 = 2357819) B2357819
theorem B4422707 : Blo 774336 4422707 := bstep (se 1 (by rfl) ⟨3317030, by rfl⟩ : syracuseStep 4422707 = 6634061) B6634061
theorem B1309945 : Blo 774336 1309945 := bstep (se 2 (by rfl) ⟨491229, by rfl⟩ : syracuseStep 1309945 = 982459) B982459
theorem B3931415 : Blo 774336 3931415 := bstep (se 1 (by rfl) ⟨2948561, by rfl⟩ : syracuseStep 3931415 = 5897123) B5897123
theorem B4980005 : Blo 774336 4980005 := bstep (se 4 (by rfl) ⟨466875, by rfl⟩ : syracuseStep 4980005 = 933751) B933751
theorem B1965455 : Blo 774336 1965455 := bstep (se 1 (by rfl) ⟨1474091, by rfl⟩ : syracuseStep 1965455 = 2948183) B2948183
theorem B1310215 : Blo 774336 1310215 := bstep (se 1 (by rfl) ⟨982661, by rfl⟩ : syracuseStep 1310215 = 1965323) B1965323
theorem B4423207 : Blo 774336 4423207 := bstep (se 1 (by rfl) ⟨3317405, by rfl⟩ : syracuseStep 4423207 = 6634811) B6634811
theorem B2621051 : Blo 774336 2621051 := bstep (se 1 (by rfl) ⟨1965788, by rfl⟩ : syracuseStep 2621051 = 3931577) B3931577
theorem B1867387 : Blo 774336 1867387 := bstep (se 1 (by rfl) ⟨1400540, by rfl⟩ : syracuseStep 1867387 = 2801081) B2801081
theorem B2096779 : Blo 774336 2096779 := bstep (se 1 (by rfl) ⟨1572584, by rfl⟩ : syracuseStep 2096779 = 3145169) B3145169
theorem B1965779 : Blo 774336 1965779 := bstep (se 1 (by rfl) ⟨1474334, by rfl⟩ : syracuseStep 1965779 = 2948669) B2948669
theorem B2621213 : Blo 774336 2621213 := bstep (se 3 (by rfl) ⟨491477, by rfl⟩ : syracuseStep 2621213 = 982955) B982955
theorem B1310647 : Blo 774336 1310647 := bstep (se 1 (by rfl) ⟨982985, by rfl⟩ : syracuseStep 1310647 = 1965971) B1965971
theorem B1867801 : Blo 774336 1867801 := bstep (se 2 (by rfl) ⟨700425, by rfl⟩ : syracuseStep 1867801 = 1400851) B1400851
theorem B983335 : Blo 774336 983335 := bstep (se 1 (by rfl) ⟨737501, by rfl⟩ : syracuseStep 983335 = 1475003) B1475003
theorem B1966427 : Blo 774336 1966427 := bstep (se 1 (by rfl) ⟨1474820, by rfl⟩ : syracuseStep 1966427 = 2949641) B2949641
theorem B1311295 : Blo 774336 1311295 := bstep (se 1 (by rfl) ⟨983471, by rfl⟩ : syracuseStep 1311295 = 1966943) B1966943
theorem B2622023 : Blo 774336 2622023 := bstep (se 1 (by rfl) ⟨1966517, by rfl⟩ : syracuseStep 2622023 = 3933035) B3933035
theorem B983659 : Blo 774336 983659 := bstep (se 1 (by rfl) ⟨737744, by rfl⟩ : syracuseStep 983659 = 1475489) B1475489
theorem B4719307 : Blo 774336 4719307 := bstep (se 1 (by rfl) ⟨3539480, by rfl⟩ : syracuseStep 4719307 = 7078961) B7078961
theorem B8946425 : Blo 774336 8946425 := bstep (se 2 (by rfl) ⟨3354909, by rfl⟩ : syracuseStep 8946425 = 6709819) B6709819
theorem B12780281 : Blo 774336 12780281 := bstep (se 2 (by rfl) ⟨4792605, by rfl⟩ : syracuseStep 12780281 = 9585211) B9585211
theorem B3736313 : Blo 774336 3736313 := bstep (se 2 (by rfl) ⟨1401117, by rfl⟩ : syracuseStep 3736313 = 2802235) B2802235
theorem B5899067 : Blo 774336 5899067 := bstep (se 1 (by rfl) ⟨4424300, by rfl⟩ : syracuseStep 5899067 = 8848601) B8848601
theorem B2098163 : Blo 774336 2098163 := bstep (se 1 (by rfl) ⟨1573622, by rfl⟩ : syracuseStep 2098163 = 3147245) B3147245
theorem B2622455 : Blo 774336 2622455 := bstep (se 1 (by rfl) ⟨1966841, by rfl⟩ : syracuseStep 2622455 = 3933683) B3933683
theorem B2491489 : Blo 774336 2491489 := bstep (se 2 (by rfl) ⟨934308, by rfl⟩ : syracuseStep 2491489 = 1868617) B1868617
theorem B885979 : Blo 774336 885979 := bstep (se 1 (by rfl) ⟨664484, by rfl⟩ : syracuseStep 885979 = 1328969) B1328969
theorem B1311977 : Blo 774336 1311977 := bstep (se 2 (by rfl) ⟨491991, by rfl⟩ : syracuseStep 1311977 = 983983) B983983
theorem B1312031 : Blo 774336 1312031 := bstep (se 1 (by rfl) ⟨984023, by rfl⟩ : syracuseStep 1312031 = 1968047) B1968047
theorem B1967399 : Blo 774336 1967399 := bstep (se 1 (by rfl) ⟨1475549, by rfl⟩ : syracuseStep 1967399 = 2951099) B2951099
theorem B3311239 : Blo 774336 3311239 := bstep (se 1 (by rfl) ⟨2483429, by rfl⟩ : syracuseStep 3311239 = 4966859) B4966859
theorem B3934007 : Blo 774336 3934007 := bstep (se 1 (by rfl) ⟨2950505, by rfl⟩ : syracuseStep 3934007 = 5901011) B5901011
theorem B1476407 : Blo 774336 1476407 := bstep (se 1 (by rfl) ⟨1107305, by rfl⟩ : syracuseStep 1476407 = 2214611) B2214611
theorem B2623319 : Blo 774336 2623319 := bstep (se 1 (by rfl) ⟨1967489, by rfl⟩ : syracuseStep 2623319 = 3934979) B3934979
theorem B17926019 : Blo 774336 17926019 := bstep (se 1 (by rfl) ⟨13444514, by rfl⟩ : syracuseStep 17926019 = 26889029) B26889029
theorem B16779143 : Blo 774336 16779143 := bstep (se 1 (by rfl) ⟨12584357, by rfl⟩ : syracuseStep 16779143 = 25168715) B25168715
theorem B1476559 : Blo 774336 1476559 := bstep (se 1 (by rfl) ⟨1107419, by rfl⟩ : syracuseStep 1476559 = 2214839) B2214839
theorem B3311597 : Blo 774336 3311597 := bstep (se 3 (by rfl) ⟨620924, by rfl⟩ : syracuseStep 3311597 = 1241849) B1241849
theorem B3934493 : Blo 774336 3934493 := bstep (se 3 (by rfl) ⟨737717, by rfl⟩ : syracuseStep 3934493 = 1475435) B1475435
theorem B2984359 : Blo 774336 2984359 := bstep (se 1 (by rfl) ⟨2238269, by rfl⟩ : syracuseStep 2984359 = 4476539) B4476539
theorem B1313401 : Blo 774336 1313401 := bstep (se 2 (by rfl) ⟨492525, by rfl⟩ : syracuseStep 1313401 = 985051) B985051
theorem B1968887 : Blo 774336 1968887 := bstep (se 1 (by rfl) ⟨1476665, by rfl⟩ : syracuseStep 1968887 = 2953331) B2953331
theorem B2624399 : Blo 774336 2624399 := bstep (se 1 (by rfl) ⟨1968299, by rfl⟩ : syracuseStep 2624399 = 3936599) B3936599
theorem B1477531 : Blo 774336 1477531 := bstep (se 1 (by rfl) ⟨1108148, by rfl⟩ : syracuseStep 1477531 = 2216297) B2216297
theorem B12586049 : Blo 774336 12586049 := bstep (se 2 (by rfl) ⟨4719768, by rfl⟩ : syracuseStep 12586049 = 9439537) B9439537
theorem B7081037 : Blo 774336 7081037 := bstep (se 3 (by rfl) ⟨1327694, by rfl⟩ : syracuseStep 7081037 = 2655389) B2655389
theorem B1969505 : Blo 774336 1969505 := bstep (se 2 (by rfl) ⟨738564, by rfl⟩ : syracuseStep 1969505 = 1477129) B1477129
theorem B1150331 : Blo 774336 1150331 := bstep (se 1 (by rfl) ⟨862748, by rfl⟩ : syracuseStep 1150331 = 1725497) B1725497
theorem B5311873 : Blo 774336 5311873 := bstep (se 2 (by rfl) ⟨1991952, by rfl⟩ : syracuseStep 5311873 = 3983905) B3983905
theorem B7474619 : Blo 774336 7474619 := bstep (se 1 (by rfl) ⟨5605964, by rfl⟩ : syracuseStep 7474619 = 11211929) B11211929
theorem B22744709 : Blo 774336 22744709 := bstep (se 4 (by rfl) ⟨2132316, by rfl⟩ : syracuseStep 22744709 = 4264633) B4264633
theorem B2101199 : Blo 774336 2101199 := bstep (se 1 (by rfl) ⟨1575899, by rfl⟩ : syracuseStep 2101199 = 3151799) B3151799
theorem B7966673 : Blo 774336 7966673 := bstep (se 2 (by rfl) ⟨2987502, by rfl⟩ : syracuseStep 7966673 = 5975005) B5975005
theorem B3936275 : Blo 774336 3936275 := bstep (se 1 (by rfl) ⟨2952206, by rfl⟩ : syracuseStep 3936275 = 5904413) B5904413
theorem B2625641 : Blo 774336 2625641 := bstep (se 2 (by rfl) ⟨984615, by rfl⟩ : syracuseStep 2625641 = 1969231) B1969231
theorem B7442603 : Blo 774336 7442603 := bstep (se 1 (by rfl) ⟨5581952, by rfl⟩ : syracuseStep 7442603 = 11163905) B11163905
theorem B3739907 : Blo 774336 3739907 := bstep (se 1 (by rfl) ⟨2804930, by rfl⟩ : syracuseStep 3739907 = 5609861) B5609861
theorem B6623603 : Blo 774336 6623603 := bstep (se 1 (by rfl) ⟨4967702, by rfl⟩ : syracuseStep 6623603 = 9935405) B9935405
theorem B10064263 : Blo 774336 10064263 := bstep (se 1 (by rfl) ⟨7548197, by rfl⟩ : syracuseStep 10064263 = 15096395) B15096395
theorem B3314195 : Blo 774336 3314195 := bstep (se 1 (by rfl) ⟨2485646, by rfl⟩ : syracuseStep 3314195 = 4971293) B4971293
theorem B3314297 : Blo 774336 3314297 := bstep (se 2 (by rfl) ⟨1242861, by rfl⟩ : syracuseStep 3314297 = 2485723) B2485723
theorem B57480101 : Blo 774336 57480101 := bstep (se 4 (by rfl) ⟨5388759, by rfl⟩ : syracuseStep 57480101 = 10777519) B10777519
theorem B2626505 : Blo 774336 2626505 := bstep (se 2 (by rfl) ⟨984939, by rfl⟩ : syracuseStep 2626505 = 1969879) B1969879
theorem B4428857 : Blo 774336 4428857 := bstep (se 2 (by rfl) ⟨1660821, by rfl⟩ : syracuseStep 4428857 = 3321643) B3321643
theorem B2626775 : Blo 774336 2626775 := bstep (se 1 (by rfl) ⟨1970081, by rfl⟩ : syracuseStep 2626775 = 3940163) B3940163
theorem B8066699 : Blo 774336 8066699 := bstep (se 1 (by rfl) ⟨6050024, by rfl⟩ : syracuseStep 8066699 = 12100049) B12100049
theorem B1742633 : Blo 774336 1742633 := bstep (se 2 (by rfl) ⟨653487, by rfl⟩ : syracuseStep 1742633 = 1306975) B1306975
theorem B3151703 : Blo 774336 3151703 := bstep (se 1 (by rfl) ⟨2363777, by rfl⟩ : syracuseStep 3151703 = 4727555) B4727555
theorem B6625313 : Blo 774336 6625313 := bstep (se 2 (by rfl) ⟨2484492, by rfl⟩ : syracuseStep 6625313 = 4968985) B4968985
theorem B8820899 : Blo 774336 8820899 := bstep (se 1 (by rfl) ⟨6615674, by rfl⟩ : syracuseStep 8820899 = 13231349) B13231349
theorem B3316211 : Blo 774336 3316211 := bstep (se 1 (by rfl) ⟨2487158, by rfl⟩ : syracuseStep 3316211 = 4974317) B4974317
theorem B99359227 : Blo 774336 99359227 := bstep (se 1 (by rfl) ⟨74519420, by rfl⟩ : syracuseStep 99359227 = 149038841) B149038841
theorem B2792015 : Blo 774336 2792015 := bstep (se 1 (by rfl) ⟨2094011, by rfl⟩ : syracuseStep 2792015 = 4188023) B4188023
theorem B1743695 : Blo 774336 1743695 := bstep (se 1 (by rfl) ⟨1307771, by rfl⟩ : syracuseStep 1743695 = 2615543) B2615543
theorem B3939191 : Blo 774336 3939191 := bstep (se 1 (by rfl) ⟨2954393, by rfl⟩ : syracuseStep 3939191 = 5908787) B5908787
theorem B1743911 : Blo 774336 1743911 := bstep (se 1 (by rfl) ⟨1307933, by rfl⟩ : syracuseStep 1743911 = 2615867) B2615867
theorem B3316859 : Blo 774336 3316859 := bstep (se 1 (by rfl) ⟨2487644, by rfl⟩ : syracuseStep 3316859 = 4975289) B4975289
theorem B1744091 : Blo 774336 1744091 := bstep (se 1 (by rfl) ⟨1308068, by rfl⟩ : syracuseStep 1744091 = 2616137) B2616137
theorem B1744289 : Blo 774336 1744289 := bstep (se 2 (by rfl) ⟨654108, by rfl⟩ : syracuseStep 1744289 = 1308217) B1308217
theorem B4431455 : Blo 774336 4431455 := bstep (se 1 (by rfl) ⟨3323591, by rfl⟩ : syracuseStep 4431455 = 6647183) B6647183
theorem B3940001 : Blo 774336 3940001 := bstep (se 2 (by rfl) ⟨1477500, by rfl⟩ : syracuseStep 3940001 = 2955001) B2955001
theorem B3546833 : Blo 774336 3546833 := bstep (se 2 (by rfl) ⟨1330062, by rfl⟩ : syracuseStep 3546833 = 2660125) B2660125
theorem B28286779 : Blo 774336 28286779 := bstep (se 1 (by rfl) ⟨21215084, by rfl⟩ : syracuseStep 28286779 = 42430169) B42430169
theorem B3317611 : Blo 774336 3317611 := bstep (se 1 (by rfl) ⟨2488208, by rfl⟩ : syracuseStep 3317611 = 4976417) B4976417
theorem B1744847 : Blo 774336 1744847 := bstep (se 1 (by rfl) ⟨1308635, by rfl⟩ : syracuseStep 1744847 = 2617271) B2617271
theorem B11968721 : Blo 774336 11968721 := bstep (se 2 (by rfl) ⟨4488270, by rfl⟩ : syracuseStep 11968721 = 8976541) B8976541
theorem B1745225 : Blo 774336 1745225 := bstep (se 2 (by rfl) ⟨654459, by rfl⟩ : syracuseStep 1745225 = 1308919) B1308919
theorem B1745243 : Blo 774336 1745243 := bstep (se 1 (by rfl) ⟨1308932, by rfl⟩ : syracuseStep 1745243 = 2617865) B2617865
theorem B1745819 : Blo 774336 1745819 := bstep (se 1 (by rfl) ⟨1309364, by rfl⟩ : syracuseStep 1745819 = 2618729) B2618729
theorem B7447555 : Blo 774336 7447555 := bstep (se 1 (by rfl) ⟨5585666, by rfl⟩ : syracuseStep 7447555 = 11171333) B11171333
theorem B1746017 : Blo 774336 1746017 := bstep (se 2 (by rfl) ⟨654756, by rfl⟩ : syracuseStep 1746017 = 1309513) B1309513
theorem B7087247 : Blo 774336 7087247 := bstep (se 1 (by rfl) ⟨5315435, by rfl⟩ : syracuseStep 7087247 = 10630871) B10630871
theorem B1746215 : Blo 774336 1746215 := bstep (se 1 (by rfl) ⟨1309661, by rfl⟩ : syracuseStep 1746215 = 2619323) B2619323
theorem B121185679 : Blo 774336 121185679 := bstep (se 1 (by rfl) ⟨90889259, by rfl⟩ : syracuseStep 121185679 = 181778519) B181778519
theorem B2205089 : Blo 774336 2205089 := bstep (se 2 (by rfl) ⟨826908, by rfl⟩ : syracuseStep 2205089 = 1653817) B1653817
theorem B828839 : Blo 774336 828839 := bstep (se 1 (by rfl) ⟨621629, by rfl⟩ : syracuseStep 828839 = 1243259) B1243259
theorem B1746593 : Blo 774336 1746593 := bstep (se 2 (by rfl) ⟨654972, by rfl⟩ : syracuseStep 1746593 = 1309945) B1309945
theorem B5908301 : Blo 774336 5908301 := bstep (se 3 (by rfl) ⟨1107806, by rfl⟩ : syracuseStep 5908301 = 2215613) B2215613
theorem B7448557 : Blo 774336 7448557 := bstep (se 3 (by rfl) ⟨1396604, by rfl⟩ : syracuseStep 7448557 = 2793209) B2793209
theorem B1746953 : Blo 774336 1746953 := bstep (se 2 (by rfl) ⟨655107, by rfl⟩ : syracuseStep 1746953 = 1310215) B1310215
theorem B2795705 : Blo 774336 2795705 := bstep (se 2 (by rfl) ⟨1048389, by rfl⟩ : syracuseStep 2795705 = 2096779) B2096779
theorem B3320003 : Blo 774336 3320003 := bstep (se 1 (by rfl) ⟨2490002, by rfl⟩ : syracuseStep 3320003 = 4980005) B4980005
theorem B1747367 : Blo 774336 1747367 := bstep (se 1 (by rfl) ⟨1310525, by rfl⟩ : syracuseStep 1747367 = 2621051) B2621051
theorem B1747475 : Blo 774336 1747475 := bstep (se 1 (by rfl) ⟨1310606, by rfl⟩ : syracuseStep 1747475 = 2621213) B2621213
theorem B1747529 : Blo 774336 1747529 := bstep (se 2 (by rfl) ⟨655323, by rfl⟩ : syracuseStep 1747529 = 1310647) B1310647
theorem B1681993 : Blo 774336 1681993 := bstep (se 2 (by rfl) ⟨630747, by rfl⟩ : syracuseStep 1681993 = 1261495) B1261495
theorem B1747943 : Blo 774336 1747943 := bstep (se 1 (by rfl) ⟨1310957, by rfl⟩ : syracuseStep 1747943 = 2621915) B2621915
theorem B1748321 : Blo 774336 1748321 := bstep (se 2 (by rfl) ⟨655620, by rfl⟩ : syracuseStep 1748321 = 1311241) B1311241
theorem B4730231 : Blo 774336 4730231 := bstep (se 1 (by rfl) ⟨3547673, by rfl⟩ : syracuseStep 4730231 = 7095347) B7095347
theorem B1748411 : Blo 774336 1748411 := bstep (se 1 (by rfl) ⟨1311308, by rfl⟩ : syracuseStep 1748411 = 2622617) B2622617
theorem B4206011 : Blo 774336 4206011 := bstep (se 1 (by rfl) ⟨3154508, by rfl⟩ : syracuseStep 4206011 = 6309017) B6309017
theorem B1748537 : Blo 774336 1748537 := bstep (se 2 (by rfl) ⟨655701, by rfl⟩ : syracuseStep 1748537 = 1311403) B1311403
theorem B2797217 : Blo 774336 2797217 := bstep (se 2 (by rfl) ⟨1048956, by rfl⟩ : syracuseStep 2797217 = 2097913) B2097913
theorem B1749203 : Blo 774336 1749203 := bstep (se 1 (by rfl) ⟨1311902, by rfl⟩ : syracuseStep 1749203 = 2623805) B2623805
theorem B1749257 : Blo 774336 1749257 := bstep (se 2 (by rfl) ⟨655971, by rfl⟩ : syracuseStep 1749257 = 1311943) B1311943
theorem B71840033 : Blo 774336 71840033 := bstep (se 2 (by rfl) ⟨26940012, by rfl⟩ : syracuseStep 71840033 = 53880025) B53880025
theorem B2208073 : Blo 774336 2208073 := bstep (se 2 (by rfl) ⟨828027, by rfl⟩ : syracuseStep 2208073 = 1656055) B1656055
theorem B1749473 : Blo 774336 1749473 := bstep (se 2 (by rfl) ⟨656052, by rfl⟩ : syracuseStep 1749473 = 1312105) B1312105
theorem B9941555 : Blo 774336 9941555 := bstep (se 1 (by rfl) ⟨7456166, by rfl⟩ : syracuseStep 9941555 = 14912333) B14912333
theorem B1749779 : Blo 774336 1749779 := bstep (se 1 (by rfl) ⟨1312334, by rfl⟩ : syracuseStep 1749779 = 2624669) B2624669
theorem B1684243 : Blo 774336 1684243 := bstep (se 1 (by rfl) ⟨1263182, by rfl⟩ : syracuseStep 1684243 = 2526365) B2526365
theorem B1750139 : Blo 774336 1750139 := bstep (se 1 (by rfl) ⟨1312604, by rfl⟩ : syracuseStep 1750139 = 2625209) B2625209
theorem B1750265 : Blo 774336 1750265 := bstep (se 2 (by rfl) ⟨656349, by rfl⟩ : syracuseStep 1750265 = 1312699) B1312699
theorem B1750409 : Blo 774336 1750409 := bstep (se 2 (by rfl) ⟨656403, by rfl⟩ : syracuseStep 1750409 = 1312807) B1312807
theorem B22394333 : Blo 774336 22394333 := bstep (se 3 (by rfl) ⟨4198937, by rfl⟩ : syracuseStep 22394333 = 8397875) B8397875
theorem B1750535 : Blo 774336 1750535 := bstep (se 1 (by rfl) ⟨1312901, by rfl⟩ : syracuseStep 1750535 = 2625803) B2625803
theorem B1750715 : Blo 774336 1750715 := bstep (se 1 (by rfl) ⟨1313036, by rfl⟩ : syracuseStep 1750715 = 2626073) B2626073
theorem B1750841 : Blo 774336 1750841 := bstep (se 2 (by rfl) ⟨656565, by rfl⟩ : syracuseStep 1750841 = 1313131) B1313131
theorem B4732759 : Blo 774336 4732759 := bstep (se 1 (by rfl) ⟨3549569, by rfl⟩ : syracuseStep 4732759 = 7099139) B7099139
theorem B1161563 : Blo 774336 1161563 := bstep (se 1 (by rfl) ⟨871172, by rfl⟩ : syracuseStep 1161563 = 1742345) B1742345
theorem B1161791 : Blo 774336 1161791 := bstep (se 1 (by rfl) ⟨871343, by rfl⟩ : syracuseStep 1161791 = 1742687) B1742687
theorem B1161911 : Blo 774336 1161911 := bstep (se 1 (by rfl) ⟨871433, by rfl⟩ : syracuseStep 1161911 = 1742867) B1742867
theorem B1162139 : Blo 774336 1162139 := bstep (se 1 (by rfl) ⟨871604, by rfl⟩ : syracuseStep 1162139 = 1743209) B1743209
theorem B1260443 : Blo 774336 1260443 := bstep (se 1 (by rfl) ⟨945332, by rfl⟩ : syracuseStep 1260443 = 1890665) B1890665
theorem B1162535 : Blo 774336 1162535 := bstep (se 1 (by rfl) ⟨871901, by rfl⟩ : syracuseStep 1162535 = 1743803) B1743803
theorem B1162619 : Blo 774336 1162619 := bstep (se 1 (by rfl) ⟨871964, by rfl⟩ : syracuseStep 1162619 = 1743929) B1743929
theorem B1162745 : Blo 774336 1162745 := bstep (se 2 (by rfl) ⟨436029, by rfl⟩ : syracuseStep 1162745 = 872059) B872059
theorem B6471191 : Blo 774336 6471191 := bstep (se 1 (by rfl) ⟨4853393, by rfl⟩ : syracuseStep 6471191 = 9706787) B9706787
theorem B1162847 : Blo 774336 1162847 := bstep (se 1 (by rfl) ⟨872135, by rfl⟩ : syracuseStep 1162847 = 1744271) B1744271
theorem B1163063 : Blo 774336 1163063 := bstep (se 1 (by rfl) ⟨872297, by rfl⟩ : syracuseStep 1163063 = 1744595) B1744595
theorem B1163369 : Blo 774336 1163369 := bstep (se 2 (by rfl) ⟨436263, by rfl⟩ : syracuseStep 1163369 = 872527) B872527
theorem B1163687 : Blo 774336 1163687 := bstep (se 1 (by rfl) ⟨872765, by rfl⟩ : syracuseStep 1163687 = 1745531) B1745531
theorem B1163771 : Blo 774336 1163771 := bstep (se 1 (by rfl) ⟨872828, by rfl⟩ : syracuseStep 1163771 = 1745657) B1745657
theorem B4964935 : Blo 774336 4964935 := bstep (se 1 (by rfl) ⟨3723701, by rfl⟩ : syracuseStep 4964935 = 7447403) B7447403
theorem B34030199 : Blo 774336 34030199 := bstep (se 1 (by rfl) ⟨25522649, by rfl⟩ : syracuseStep 34030199 = 51045299) B51045299
theorem B1163897 : Blo 774336 1163897 := bstep (se 2 (by rfl) ⟨436461, by rfl⟩ : syracuseStep 1163897 = 872923) B872923
theorem B1163951 : Blo 774336 1163951 := bstep (se 1 (by rfl) ⟨872963, by rfl⟩ : syracuseStep 1163951 = 1745927) B1745927
theorem B1163999 : Blo 774336 1163999 := bstep (se 1 (by rfl) ⟨872999, by rfl⟩ : syracuseStep 1163999 = 1745999) B1745999
theorem B1164263 : Blo 774336 1164263 := bstep (se 1 (by rfl) ⟨873197, by rfl⟩ : syracuseStep 1164263 = 1746395) B1746395
theorem B1164521 : Blo 774336 1164521 := bstep (se 2 (by rfl) ⟨436695, by rfl⟩ : syracuseStep 1164521 = 873391) B873391
theorem B1164575 : Blo 774336 1164575 := bstep (se 1 (by rfl) ⟨873431, by rfl⟩ : syracuseStep 1164575 = 1746863) B1746863
theorem B1164743 : Blo 774336 1164743 := bstep (se 1 (by rfl) ⟨873557, by rfl⟩ : syracuseStep 1164743 = 1747115) B1747115
theorem B2213563 : Blo 774336 2213563 := bstep (se 1 (by rfl) ⟨1660172, by rfl⟩ : syracuseStep 2213563 = 3320345) B3320345
theorem B1165097 : Blo 774336 1165097 := bstep (se 2 (by rfl) ⟨436911, by rfl⟩ : syracuseStep 1165097 = 873823) B873823
theorem B1165103 : Blo 774336 1165103 := bstep (se 1 (by rfl) ⟨873827, by rfl⟩ : syracuseStep 1165103 = 1747655) B1747655
theorem B1165577 : Blo 774336 1165577 := bstep (se 2 (by rfl) ⟨437091, by rfl⟩ : syracuseStep 1165577 = 874183) B874183
theorem B1165679 : Blo 774336 1165679 := bstep (se 1 (by rfl) ⟨874259, by rfl⟩ : syracuseStep 1165679 = 1748519) B1748519
theorem B7096805 : Blo 774336 7096805 := bstep (se 4 (by rfl) ⟨665325, by rfl⟩ : syracuseStep 7096805 = 1330651) B1330651
theorem B1165895 : Blo 774336 1165895 := bstep (se 1 (by rfl) ⟨874421, by rfl⟩ : syracuseStep 1165895 = 1748843) B1748843
theorem B1165931 : Blo 774336 1165931 := bstep (se 1 (by rfl) ⟨874448, by rfl⟩ : syracuseStep 1165931 = 1748897) B1748897
theorem B1166159 : Blo 774336 1166159 := bstep (se 1 (by rfl) ⟨874619, by rfl⟩ : syracuseStep 1166159 = 1749239) B1749239
theorem B871375 : Blo 774336 871375 := bstep (se 1 (by rfl) ⟨653531, by rfl⟩ : syracuseStep 871375 = 1307063) B1307063
theorem B1166555 : Blo 774336 1166555 := bstep (se 1 (by rfl) ⟨874916, by rfl⟩ : syracuseStep 1166555 = 1749833) B1749833
theorem B871771 : Blo 774336 871771 := bstep (se 1 (by rfl) ⟨653828, by rfl⟩ : syracuseStep 871771 = 1307657) B1307657
theorem B1166729 : Blo 774336 1166729 := bstep (se 2 (by rfl) ⟨437523, by rfl⟩ : syracuseStep 1166729 = 875047) B875047
theorem B871879 : Blo 774336 871879 := bstep (se 1 (by rfl) ⟨653909, by rfl⟩ : syracuseStep 871879 = 1307819) B1307819
theorem B1167083 : Blo 774336 1167083 := bstep (se 1 (by rfl) ⟨875312, by rfl⟩ : syracuseStep 1167083 = 1750625) B1750625
theorem B872239 : Blo 774336 872239 := bstep (se 1 (by rfl) ⟨654179, by rfl⟩ : syracuseStep 872239 = 1308359) B1308359
theorem B872347 : Blo 774336 872347 := bstep (se 1 (by rfl) ⟨654260, by rfl⟩ : syracuseStep 872347 = 1308521) B1308521
theorem B1167311 : Blo 774336 1167311 := bstep (se 1 (by rfl) ⟨875483, by rfl⟩ : syracuseStep 1167311 = 1750967) B1750967
theorem B774431 : Blo 774336 774431 := bstep (se 1 (by rfl) ⟨580823, by rfl⟩ : syracuseStep 774431 = 1161647) B1161647
theorem B872743 : Blo 774336 872743 := bstep (se 1 (by rfl) ⟨654557, by rfl⟩ : syracuseStep 872743 = 1309115) B1309115
theorem B774491 : Blo 774336 774491 := bstep (se 1 (by rfl) ⟨580868, by rfl⟩ : syracuseStep 774491 = 1161737) B1161737
theorem B774511 : Blo 774336 774511 := bstep (se 1 (by rfl) ⟨580883, by rfl⟩ : syracuseStep 774511 = 1161767) B1161767
theorem B872815 : Blo 774336 872815 := bstep (se 1 (by rfl) ⟨654611, by rfl⟩ : syracuseStep 872815 = 1309223) B1309223
theorem B774567 : Blo 774336 774567 := bstep (se 1 (by rfl) ⟨580925, by rfl⟩ : syracuseStep 774567 = 1161851) B1161851
theorem B774651 : Blo 774336 774651 := bstep (se 1 (by rfl) ⟨580988, by rfl⟩ : syracuseStep 774651 = 1161977) B1161977
theorem B774719 : Blo 774336 774719 := bstep (se 1 (by rfl) ⟨581039, by rfl⟩ : syracuseStep 774719 = 1162079) B1162079
theorem B1659455 : Blo 774336 1659455 := bstep (se 1 (by rfl) ⟨1244591, by rfl⟩ : syracuseStep 1659455 = 2489183) B2489183
theorem B774727 : Blo 774336 774727 := bstep (se 1 (by rfl) ⟨581045, by rfl⟩ : syracuseStep 774727 = 1162091) B1162091
theorem B873031 : Blo 774336 873031 := bstep (se 1 (by rfl) ⟨654773, by rfl⟩ : syracuseStep 873031 = 1309547) B1309547
theorem B774879 : Blo 774336 774879 := bstep (se 1 (by rfl) ⟨581159, by rfl⟩ : syracuseStep 774879 = 1162319) B1162319
theorem B774959 : Blo 774336 774959 := bstep (se 1 (by rfl) ⟨581219, by rfl⟩ : syracuseStep 774959 = 1162439) B1162439
theorem B3724127 : Blo 774336 3724127 := bstep (se 1 (by rfl) ⟨2793095, by rfl⟩ : syracuseStep 3724127 = 5586191) B5586191
theorem B775067 : Blo 774336 775067 := bstep (se 1 (by rfl) ⟨581300, by rfl⟩ : syracuseStep 775067 = 1162601) B1162601
theorem B775119 : Blo 774336 775119 := bstep (se 1 (by rfl) ⟨581339, by rfl⟩ : syracuseStep 775119 = 1162679) B1162679
theorem B775143 : Blo 774336 775143 := bstep (se 1 (by rfl) ⟨581357, by rfl⟩ : syracuseStep 775143 = 1162715) B1162715
theorem B775455 : Blo 774336 775455 := bstep (se 1 (by rfl) ⟨581591, by rfl⟩ : syracuseStep 775455 = 1163183) B1163183
theorem B775515 : Blo 774336 775515 := bstep (se 1 (by rfl) ⟨581636, by rfl⟩ : syracuseStep 775515 = 1163273) B1163273
theorem B3986783 : Blo 774336 3986783 := bstep (se 1 (by rfl) ⟨2990087, by rfl⟩ : syracuseStep 3986783 = 5980175) B5980175
theorem B775535 : Blo 774336 775535 := bstep (se 1 (by rfl) ⟨581651, by rfl⟩ : syracuseStep 775535 = 1163303) B1163303
theorem B775591 : Blo 774336 775591 := bstep (se 1 (by rfl) ⟨581693, by rfl⟩ : syracuseStep 775591 = 1163387) B1163387
theorem B873895 : Blo 774336 873895 := bstep (se 1 (by rfl) ⟨655421, by rfl⟩ : syracuseStep 873895 = 1310843) B1310843
theorem B6641099 : Blo 774336 6641099 := bstep (se 1 (by rfl) ⟨4980824, by rfl⟩ : syracuseStep 6641099 = 9961649) B9961649
theorem B775675 : Blo 774336 775675 := bstep (se 1 (by rfl) ⟨581756, by rfl⟩ : syracuseStep 775675 = 1163513) B1163513
theorem B775743 : Blo 774336 775743 := bstep (se 1 (by rfl) ⟨581807, by rfl⟩ : syracuseStep 775743 = 1163615) B1163615
theorem B775751 : Blo 774336 775751 := bstep (se 1 (by rfl) ⟨581813, by rfl⟩ : syracuseStep 775751 = 1163627) B1163627
theorem B775903 : Blo 774336 775903 := bstep (se 1 (by rfl) ⟨581927, by rfl⟩ : syracuseStep 775903 = 1163855) B1163855
theorem B775983 : Blo 774336 775983 := bstep (se 1 (by rfl) ⟨581987, by rfl⟩ : syracuseStep 775983 = 1163975) B1163975
theorem B776091 : Blo 774336 776091 := bstep (se 1 (by rfl) ⟨582068, by rfl⟩ : syracuseStep 776091 = 1164137) B1164137
theorem B776143 : Blo 774336 776143 := bstep (se 1 (by rfl) ⟨582107, by rfl⟩ : syracuseStep 776143 = 1164215) B1164215
theorem B776167 : Blo 774336 776167 := bstep (se 1 (by rfl) ⟨582125, by rfl⟩ : syracuseStep 776167 = 1164251) B1164251
theorem B874471 : Blo 774336 874471 := bstep (se 1 (by rfl) ⟨655853, by rfl⟩ : syracuseStep 874471 = 1311707) B1311707
theorem B776479 : Blo 774336 776479 := bstep (se 1 (by rfl) ⟨582359, by rfl⟩ : syracuseStep 776479 = 1164719) B1164719
theorem B776539 : Blo 774336 776539 := bstep (se 1 (by rfl) ⟨582404, by rfl⟩ : syracuseStep 776539 = 1164809) B1164809
theorem B776559 : Blo 774336 776559 := bstep (se 1 (by rfl) ⟨582419, by rfl⟩ : syracuseStep 776559 = 1164839) B1164839
theorem B3922343 : Blo 774336 3922343 := bstep (se 1 (by rfl) ⟨2941757, by rfl⟩ : syracuseStep 3922343 = 5883515) B5883515
theorem B776615 : Blo 774336 776615 := bstep (se 1 (by rfl) ⟨582461, by rfl⟩ : syracuseStep 776615 = 1164923) B1164923
theorem B776699 : Blo 774336 776699 := bstep (se 1 (by rfl) ⟨582524, by rfl⟩ : syracuseStep 776699 = 1165049) B1165049
theorem B776767 : Blo 774336 776767 := bstep (se 1 (by rfl) ⟨582575, by rfl⟩ : syracuseStep 776767 = 1165151) B1165151
theorem B776775 : Blo 774336 776775 := bstep (se 1 (by rfl) ⟨582581, by rfl⟩ : syracuseStep 776775 = 1165163) B1165163
theorem B3922505 : Blo 774336 3922505 := bstep (se 2 (by rfl) ⟨1470939, by rfl⟩ : syracuseStep 3922505 = 2941879) B2941879
theorem B776927 : Blo 774336 776927 := bstep (se 1 (by rfl) ⟨582695, by rfl⟩ : syracuseStep 776927 = 1165391) B1165391
theorem B777007 : Blo 774336 777007 := bstep (se 1 (by rfl) ⟨582755, by rfl⟩ : syracuseStep 777007 = 1165511) B1165511
theorem B777115 : Blo 774336 777115 := bstep (se 1 (by rfl) ⟨582836, by rfl⟩ : syracuseStep 777115 = 1165673) B1165673
theorem B777167 : Blo 774336 777167 := bstep (se 1 (by rfl) ⟨582875, by rfl⟩ : syracuseStep 777167 = 1165751) B1165751
theorem B1661915 : Blo 774336 1661915 := bstep (se 1 (by rfl) ⟨1246436, by rfl⟩ : syracuseStep 1661915 = 2492873) B2492873
theorem B777191 : Blo 774336 777191 := bstep (se 1 (by rfl) ⟨582893, by rfl⟩ : syracuseStep 777191 = 1165787) B1165787
theorem B7167005 : Blo 774336 7167005 := bstep (se 3 (by rfl) ⟨1343813, by rfl⟩ : syracuseStep 7167005 = 2687627) B2687627
theorem B777503 : Blo 774336 777503 := bstep (se 1 (by rfl) ⟨583127, by rfl⟩ : syracuseStep 777503 = 1166255) B1166255
theorem B5889347 : Blo 774336 5889347 := bstep (se 1 (by rfl) ⟨4417010, by rfl⟩ : syracuseStep 5889347 = 8834021) B8834021
theorem B777563 : Blo 774336 777563 := bstep (se 1 (by rfl) ⟨583172, by rfl⟩ : syracuseStep 777563 = 1166345) B1166345
theorem B777583 : Blo 774336 777583 := bstep (se 1 (by rfl) ⟨583187, by rfl⟩ : syracuseStep 777583 = 1166375) B1166375
theorem B777639 : Blo 774336 777639 := bstep (se 1 (by rfl) ⟨583229, by rfl⟩ : syracuseStep 777639 = 1166459) B1166459
theorem B2481623 : Blo 774336 2481623 := bstep (se 1 (by rfl) ⟨1861217, by rfl⟩ : syracuseStep 2481623 = 3722435) B3722435
theorem B777723 : Blo 774336 777723 := bstep (se 1 (by rfl) ⟨583292, by rfl⟩ : syracuseStep 777723 = 1166585) B1166585
theorem B777791 : Blo 774336 777791 := bstep (se 1 (by rfl) ⟨583343, by rfl⟩ : syracuseStep 777791 = 1166687) B1166687
theorem B777799 : Blo 774336 777799 := bstep (se 1 (by rfl) ⟨583349, by rfl⟩ : syracuseStep 777799 = 1166699) B1166699
theorem B777951 : Blo 774336 777951 := bstep (se 1 (by rfl) ⟨583463, by rfl⟩ : syracuseStep 777951 = 1166927) B1166927
theorem B5889833 : Blo 774336 5889833 := bstep (se 2 (by rfl) ⟨2208687, by rfl⟩ : syracuseStep 5889833 = 4417375) B4417375
theorem B778031 : Blo 774336 778031 := bstep (se 1 (by rfl) ⟨583523, by rfl⟩ : syracuseStep 778031 = 1167047) B1167047
theorem B778139 : Blo 774336 778139 := bstep (se 1 (by rfl) ⟨583604, by rfl⟩ : syracuseStep 778139 = 1167209) B1167209
theorem B778191 : Blo 774336 778191 := bstep (se 1 (by rfl) ⟨583643, by rfl⟩ : syracuseStep 778191 = 1167287) B1167287
theorem B778215 : Blo 774336 778215 := bstep (se 1 (by rfl) ⟨583661, by rfl⟩ : syracuseStep 778215 = 1167323) B1167323
theorem B5988401 : Blo 774336 5988401 := bstep (se 2 (by rfl) ⟨2245650, by rfl⟩ : syracuseStep 5988401 = 4491301) B4491301
theorem B3924449 : Blo 774336 3924449 := bstep (se 2 (by rfl) ⟨1471668, by rfl⟩ : syracuseStep 3924449 = 2943337) B2943337
theorem B1401313 : Blo 774336 1401313 := bstep (se 2 (by rfl) ⟨525492, by rfl⟩ : syracuseStep 1401313 = 1050985) B1050985
theorem B2613761 : Blo 774336 2613761 := bstep (se 2 (by rfl) ⟨980160, by rfl⟩ : syracuseStep 2613761 = 1960321) B1960321
theorem B5038807 : Blo 774336 5038807 := bstep (se 1 (by rfl) ⟨3779105, by rfl⟩ : syracuseStep 5038807 = 7558211) B7558211
theorem B1860583 : Blo 774336 1860583 := bstep (se 1 (by rfl) ⟨1395437, by rfl⟩ : syracuseStep 1860583 = 2790875) B2790875
theorem B2614247 : Blo 774336 2614247 := bstep (se 1 (by rfl) ⟨1960685, by rfl⟩ : syracuseStep 2614247 = 3921371) B3921371
theorem B15918065 : Blo 774336 15918065 := bstep (se 2 (by rfl) ⟨5969274, by rfl⟩ : syracuseStep 15918065 = 11938549) B11938549
theorem B2614571 : Blo 774336 2614571 := bstep (se 1 (by rfl) ⟨1960928, by rfl⟩ : syracuseStep 2614571 = 3921857) B3921857
theorem B2614841 : Blo 774336 2614841 := bstep (se 2 (by rfl) ⟨980565, by rfl⟩ : syracuseStep 2614841 = 1961131) B1961131
theorem B943687 : Blo 774336 943687 := bstep (se 1 (by rfl) ⟨707765, by rfl⟩ : syracuseStep 943687 = 1415531) B1415531
theorem B3729239 : Blo 774336 3729239 := bstep (se 1 (by rfl) ⟨2796929, by rfl⟩ : syracuseStep 3729239 = 5593859) B5593859
theorem B8415485 : Blo 774336 8415485 := bstep (se 3 (by rfl) ⟨1577903, by rfl⟩ : syracuseStep 8415485 = 3155807) B3155807
theorem B4974857 : Blo 774336 4974857 := bstep (se 2 (by rfl) ⟨1865571, by rfl⟩ : syracuseStep 4974857 = 3731143) B3731143
theorem B29878793 : Blo 774336 29878793 := bstep (se 2 (by rfl) ⟨11204547, by rfl⟩ : syracuseStep 29878793 = 22409095) B22409095
theorem B4188779 : Blo 774336 4188779 := bstep (se 1 (by rfl) ⟨3141584, by rfl⟩ : syracuseStep 4188779 = 6283169) B6283169
theorem B3926717 : Blo 774336 3926717 := bstep (se 3 (by rfl) ⟨736259, by rfl⟩ : syracuseStep 3926717 = 1472519) B1472519
theorem B2616083 : Blo 774336 2616083 := bstep (se 1 (by rfl) ⟨1962062, by rfl⟩ : syracuseStep 2616083 = 3924125) B3924125
theorem B4188995 : Blo 774336 4188995 := bstep (se 1 (by rfl) ⟨3141746, by rfl⟩ : syracuseStep 4188995 = 6283493) B6283493
theorem B9956317 : Blo 774336 9956317 := bstep (se 3 (by rfl) ⟨1866809, by rfl⟩ : syracuseStep 9956317 = 3733619) B3733619
theorem B31878157 : Blo 774336 31878157 := bstep (se 3 (by rfl) ⟨5977154, by rfl⟩ : syracuseStep 31878157 = 11954309) B11954309
theorem B5303335 : Blo 774336 5303335 := bstep (se 1 (by rfl) ⟨3977501, by rfl⟩ : syracuseStep 5303335 = 7955003) B7955003
theorem B5893235 : Blo 774336 5893235 := bstep (se 1 (by rfl) ⟨4419926, by rfl⟩ : syracuseStep 5893235 = 8839853) B8839853
theorem B10644767 : Blo 774336 10644767 := bstep (se 1 (by rfl) ⟨7983575, by rfl⟩ : syracuseStep 10644767 = 15967151) B15967151
theorem B1011271 : Blo 774336 1011271 := bstep (se 1 (by rfl) ⟨758453, by rfl⟩ : syracuseStep 1011271 = 1516907) B1516907
theorem B1961567 : Blo 774336 1961567 := bstep (se 1 (by rfl) ⟨1471175, by rfl⟩ : syracuseStep 1961567 = 2942351) B2942351
theorem B2616947 : Blo 774336 2616947 := bstep (se 1 (by rfl) ⟨1962710, by rfl⟩ : syracuseStep 2616947 = 3925421) B3925421
theorem B2354849 : Blo 774336 2354849 := bstep (se 2 (by rfl) ⟨883068, by rfl⟩ : syracuseStep 2354849 = 1766137) B1766137
theorem B2617217 : Blo 774336 2617217 := bstep (se 2 (by rfl) ⟨981456, by rfl⟩ : syracuseStep 2617217 = 1962913) B1962913
theorem B27324533 : Blo 774336 27324533 := bstep (se 5 (by rfl) ⟨1280837, by rfl⟩ : syracuseStep 27324533 = 2561675) B2561675
theorem B1962265 : Blo 774336 1962265 := bstep (se 2 (by rfl) ⟨735849, by rfl⟩ : syracuseStep 1962265 = 1471699) B1471699
theorem B5304649 : Blo 774336 5304649 := bstep (se 2 (by rfl) ⟨1989243, by rfl⟩ : syracuseStep 5304649 = 3978487) B3978487
theorem B1470811 : Blo 774336 1470811 := bstep (se 1 (by rfl) ⟨1103108, by rfl⟩ : syracuseStep 1470811 = 2206217) B2206217
theorem B1962407 : Blo 774336 1962407 := bstep (se 1 (by rfl) ⟨1471805, by rfl⟩ : syracuseStep 1962407 = 2943611) B2943611
theorem B2945555 : Blo 774336 2945555 := bstep (se 1 (by rfl) ⟨2209166, by rfl⟩ : syracuseStep 2945555 = 4418333) B4418333
theorem B1962569 : Blo 774336 1962569 := bstep (se 2 (by rfl) ⟨735963, by rfl⟩ : syracuseStep 1962569 = 1471927) B1471927
theorem B2618027 : Blo 774336 2618027 := bstep (se 1 (by rfl) ⟨1963520, by rfl⟩ : syracuseStep 2618027 = 3927041) B3927041
theorem B6615917 : Blo 774336 6615917 := bstep (se 3 (by rfl) ⟨1240484, by rfl⟩ : syracuseStep 6615917 = 2480969) B2480969
theorem B1307623 : Blo 774336 1307623 := bstep (se 1 (by rfl) ⟨980717, by rfl⟩ : syracuseStep 1307623 = 1961435) B1961435
theorem B2487287 : Blo 774336 2487287 := bstep (se 1 (by rfl) ⟨1865465, by rfl⟩ : syracuseStep 2487287 = 3730931) B3730931
theorem B2487439 : Blo 774336 2487439 := bstep (se 1 (by rfl) ⟨1865579, by rfl⟩ : syracuseStep 2487439 = 3731159) B3731159
theorem B2618567 : Blo 774336 2618567 := bstep (se 1 (by rfl) ⟨1963925, by rfl⟩ : syracuseStep 2618567 = 3927851) B3927851
theorem B1996019 : Blo 774336 1996019 := bstep (se 1 (by rfl) ⟨1497014, by rfl⟩ : syracuseStep 1996019 = 2994029) B2994029
theorem B1570079 : Blo 774336 1570079 := bstep (se 1 (by rfl) ⟨1177559, by rfl⟩ : syracuseStep 1570079 = 2355119) B2355119
theorem B1471783 : Blo 774336 1471783 := bstep (se 1 (by rfl) ⟨1103837, by rfl⟩ : syracuseStep 1471783 = 2207675) B2207675
theorem B4781351 : Blo 774336 4781351 := bstep (se 1 (by rfl) ⟨3586013, by rfl⟩ : syracuseStep 4781351 = 7172027) B7172027
theorem B8975711 : Blo 774336 8975711 := bstep (se 1 (by rfl) ⟨6731783, by rfl⟩ : syracuseStep 8975711 = 13463567) B13463567
theorem B3732929 : Blo 774336 3732929 := bstep (se 2 (by rfl) ⟨1399848, by rfl⟩ : syracuseStep 3732929 = 2799697) B2799697
theorem B13235723 : Blo 774336 13235723 := bstep (se 1 (by rfl) ⟨9926792, by rfl⟩ : syracuseStep 13235723 = 19853585) B19853585
theorem B3929633 : Blo 774336 3929633 := bstep (se 2 (by rfl) ⟨1473612, by rfl⟩ : syracuseStep 3929633 = 2947225) B2947225
theorem B18708317 : Blo 774336 18708317 := bstep (se 3 (by rfl) ⟨3507809, by rfl⟩ : syracuseStep 18708317 = 7015619) B7015619
theorem B6453593 : Blo 774336 6453593 := bstep (se 2 (by rfl) ⟨2420097, by rfl⟩ : syracuseStep 6453593 = 4840195) B4840195
theorem B1964513 : Blo 774336 1964513 := bstep (se 2 (by rfl) ⟨736692, by rfl⟩ : syracuseStep 1964513 = 1473385) B1473385
theorem B2128403 : Blo 774336 2128403 := bstep (se 1 (by rfl) ⟨1596302, by rfl⟩ : syracuseStep 2128403 = 3192605) B3192605
theorem B1866311 : Blo 774336 1866311 := bstep (se 1 (by rfl) ⟨1399733, by rfl⟩ : syracuseStep 1866311 = 2799467) B2799467
theorem B5306953 : Blo 774336 5306953 := bstep (se 2 (by rfl) ⟨1990107, by rfl⟩ : syracuseStep 5306953 = 3980215) B3980215
theorem B3308111 : Blo 774336 3308111 := bstep (se 1 (by rfl) ⟨2481083, by rfl⟩ : syracuseStep 3308111 = 4962167) B4962167
theorem B2620079 : Blo 774336 2620079 := bstep (se 1 (by rfl) ⟨1965059, by rfl⟩ : syracuseStep 2620079 = 3930119) B3930119
theorem B5962681 : Blo 774336 5962681 := bstep (se 2 (by rfl) ⟨2236005, by rfl⟩ : syracuseStep 5962681 = 4472011) B4472011
theorem B1965019 : Blo 774336 1965019 := bstep (se 1 (by rfl) ⟨1473764, by rfl⟩ : syracuseStep 1965019 = 2947529) B2947529
theorem B2620403 : Blo 774336 2620403 := bstep (se 1 (by rfl) ⟨1965302, by rfl⟩ : syracuseStep 2620403 = 3930605) B3930605
theorem B3538187 : Blo 774336 3538187 := bstep (se 1 (by rfl) ⟨2653640, by rfl⟩ : syracuseStep 3538187 = 5307281) B5307281
theorem B1965343 : Blo 774336 1965343 := bstep (se 1 (by rfl) ⟨1474007, by rfl⟩ : syracuseStep 1965343 = 2948015) B2948015
theorem B982363 : Blo 774336 982363 := bstep (se 1 (by rfl) ⟨736772, by rfl⟩ : syracuseStep 982363 = 1473545) B1473545
theorem B1047919 : Blo 774336 1047919 := bstep (se 1 (by rfl) ⟨785939, by rfl⟩ : syracuseStep 1047919 = 1571879) B1571879
theorem B2948471 : Blo 774336 2948471 := bstep (se 1 (by rfl) ⟨2211353, by rfl⟩ : syracuseStep 2948471 = 4422707) B4422707
theorem B5897609 : Blo 774336 5897609 := bstep (se 2 (by rfl) ⟨2211603, by rfl⟩ : syracuseStep 5897609 = 4423207) B4423207
theorem B2489849 : Blo 774336 2489849 := bstep (se 2 (by rfl) ⟨933693, by rfl⟩ : syracuseStep 2489849 = 1867387) B1867387
theorem B1867271 : Blo 774336 1867271 := bstep (se 1 (by rfl) ⟨1400453, by rfl⟩ : syracuseStep 1867271 = 2800907) B2800907
theorem B2620943 : Blo 774336 2620943 := bstep (se 1 (by rfl) ⟨1965707, by rfl⟩ : syracuseStep 2620943 = 3931415) B3931415
theorem B884287 : Blo 774336 884287 := bstep (se 1 (by rfl) ⟨663215, by rfl⟩ : syracuseStep 884287 = 1326431) B1326431
theorem B3309137 : Blo 774336 3309137 := bstep (se 2 (by rfl) ⟨1240926, by rfl⟩ : syracuseStep 3309137 = 2481853) B2481853
theorem B1310303 : Blo 774336 1310303 := bstep (se 1 (by rfl) ⟨982727, by rfl⟩ : syracuseStep 1310303 = 1965455) B1965455
theorem B1310519 : Blo 774336 1310519 := bstep (se 1 (by rfl) ⟨982889, by rfl⟩ : syracuseStep 1310519 = 1965779) B1965779
theorem B12615497 : Blo 774336 12615497 := bstep (se 2 (by rfl) ⟨4730811, by rfl⟩ : syracuseStep 12615497 = 9461623) B9461623
theorem B2490401 : Blo 774336 2490401 := bstep (se 2 (by rfl) ⟨933900, by rfl⟩ : syracuseStep 2490401 = 1867801) B1867801
theorem B1310951 : Blo 774336 1310951 := bstep (se 1 (by rfl) ⟨983213, by rfl⟩ : syracuseStep 1310951 = 1966427) B1966427
theorem B1311113 : Blo 774336 1311113 := bstep (se 2 (by rfl) ⟨491667, by rfl⟩ : syracuseStep 1311113 = 983335) B983335
theorem B5964283 : Blo 774336 5964283 := bstep (se 1 (by rfl) ⟨4473212, by rfl⟩ : syracuseStep 5964283 = 8946425) B8946425
theorem B8520187 : Blo 774336 8520187 := bstep (se 1 (by rfl) ⟨6390140, by rfl⟩ : syracuseStep 8520187 = 12780281) B12780281
theorem B2490875 : Blo 774336 2490875 := bstep (se 1 (by rfl) ⟨1868156, by rfl⟩ : syracuseStep 2490875 = 3736313) B3736313
theorem B3932711 : Blo 774336 3932711 := bstep (se 1 (by rfl) ⟨2949533, by rfl⟩ : syracuseStep 3932711 = 5899067) B5899067
theorem B1868417 : Blo 774336 1868417 := bstep (se 2 (by rfl) ⟨700656, by rfl⟩ : syracuseStep 1868417 = 1401313) B1401313
theorem B6619913 : Blo 774336 6619913 := bstep (se 2 (by rfl) ⟨2482467, by rfl⟩ : syracuseStep 6619913 = 4964935) B4964935
theorem B1311545 : Blo 774336 1311545 := bstep (se 2 (by rfl) ⟨491829, by rfl⟩ : syracuseStep 1311545 = 983659) B983659
theorem B1311599 : Blo 774336 1311599 := bstep (se 1 (by rfl) ⟨983699, by rfl⟩ : syracuseStep 1311599 = 1967399) B1967399
theorem B6292409 : Blo 774336 6292409 := bstep (se 2 (by rfl) ⟨2359653, by rfl⟩ : syracuseStep 6292409 = 4719307) B4719307
theorem B6718409 : Blo 774336 6718409 := bstep (se 2 (by rfl) ⟨2519403, by rfl⟩ : syracuseStep 6718409 = 5038807) B5038807
theorem B2622671 : Blo 774336 2622671 := bstep (se 1 (by rfl) ⟨1967003, by rfl⟩ : syracuseStep 2622671 = 3934007) B3934007
theorem B9930073 : Blo 774336 9930073 := bstep (se 2 (by rfl) ⟨3723777, by rfl⟩ : syracuseStep 9930073 = 7447555) B7447555
theorem B2622995 : Blo 774336 2622995 := bstep (se 1 (by rfl) ⟨1967246, by rfl⟩ : syracuseStep 2622995 = 3934493) B3934493
theorem B1181305 : Blo 774336 1181305 := bstep (se 2 (by rfl) ⟨442989, by rfl⟩ : syracuseStep 1181305 = 885979) B885979
theorem B1312591 : Blo 774336 1312591 := bstep (se 1 (by rfl) ⟨984443, by rfl⟩ : syracuseStep 1312591 = 1968887) B1968887
theorem B161580905 : Blo 774336 161580905 := bstep (se 2 (by rfl) ⟨60592839, by rfl⟩ : syracuseStep 161580905 = 121185679) B121185679
theorem B8390699 : Blo 774336 8390699 := bstep (se 1 (by rfl) ⟨6293024, by rfl⟩ : syracuseStep 8390699 = 12586049) B12586049
theorem B4720691 : Blo 774336 4720691 := bstep (se 1 (by rfl) ⟨3540518, by rfl⟩ : syracuseStep 4720691 = 7081037) B7081037
theorem B1313003 : Blo 774336 1313003 := bstep (se 1 (by rfl) ⟨984752, by rfl⟩ : syracuseStep 1313003 = 1969505) B1969505
theorem B2951417 : Blo 774336 2951417 := bstep (se 2 (by rfl) ⟨1106781, by rfl⟩ : syracuseStep 2951417 = 2213563) B2213563
theorem B1968745 : Blo 774336 1968745 := bstep (se 2 (by rfl) ⟨738279, by rfl⟩ : syracuseStep 1968745 = 1476559) B1476559
theorem B5311115 : Blo 774336 5311115 := bstep (se 1 (by rfl) ⟨3983336, by rfl⟩ : syracuseStep 5311115 = 7966673) B7966673
theorem B9931409 : Blo 774336 9931409 := bstep (se 2 (by rfl) ⟨3724278, by rfl⟩ : syracuseStep 9931409 = 7448557) B7448557
theorem B2624183 : Blo 774336 2624183 := bstep (se 1 (by rfl) ⟨1968137, by rfl⟩ : syracuseStep 2624183 = 3936275) B3936275
theorem B2493271 : Blo 774336 2493271 := bstep (se 1 (by rfl) ⟨1869953, by rfl⟩ : syracuseStep 2493271 = 3739907) B3739907
theorem B2952571 : Blo 774336 2952571 := bstep (se 1 (by rfl) ⟨2214428, by rfl⟩ : syracuseStep 2952571 = 4428857) B4428857
theorem B2657855 : Blo 774336 2657855 := bstep (se 1 (by rfl) ⟨1993391, by rfl⟩ : syracuseStep 2657855 = 3986783) B3986783
theorem B4427399 : Blo 774336 4427399 := bstep (se 1 (by rfl) ⟨3320549, by rfl⟩ : syracuseStep 4427399 = 6641099) B6641099
theorem B5377799 : Blo 774336 5377799 := bstep (se 1 (by rfl) ⟨4033349, by rfl⟩ : syracuseStep 5377799 = 8066699) B8066699
theorem B1970041 : Blo 774336 1970041 := bstep (se 2 (by rfl) ⟨738765, by rfl⟩ : syracuseStep 1970041 = 1477531) B1477531
theorem B2101135 : Blo 774336 2101135 := bstep (se 1 (by rfl) ⟨1575851, by rfl⟩ : syracuseStep 2101135 = 3151703) B3151703
theorem B13275089 : Blo 774336 13275089 := bstep (se 2 (by rfl) ⟨4978158, by rfl⟩ : syracuseStep 13275089 = 9956317) B9956317
theorem B42504209 : Blo 774336 42504209 := bstep (se 2 (by rfl) ⟨15939078, by rfl⟩ : syracuseStep 42504209 = 31878157) B31878157
theorem B8982629 : Blo 774336 8982629 := bstep (se 4 (by rfl) ⟨842121, by rfl⟩ : syracuseStep 8982629 = 1684243) B1684243
theorem B7082497 : Blo 774336 7082497 := bstep (se 2 (by rfl) ⟨2655936, by rfl⟩ : syracuseStep 7082497 = 5311873) B5311873
theorem B2626127 : Blo 774336 2626127 := bstep (se 1 (by rfl) ⟨1969595, by rfl⟩ : syracuseStep 2626127 = 3939191) B3939191
theorem B1348361 : Blo 774336 1348361 := bstep (se 2 (by rfl) ⟨505635, by rfl⟩ : syracuseStep 1348361 = 1011271) B1011271
theorem B3937085 : Blo 774336 3937085 := bstep (se 3 (by rfl) ⟨738203, by rfl⟩ : syracuseStep 3937085 = 1476407) B1476407
theorem B2954303 : Blo 774336 2954303 := bstep (se 1 (by rfl) ⟨2215727, by rfl⟩ : syracuseStep 2954303 = 4431455) B4431455
theorem B2626667 : Blo 774336 2626667 := bstep (se 1 (by rfl) ⟨1970000, by rfl⟩ : syracuseStep 2626667 = 3940001) B3940001
theorem B1742507 : Blo 774336 1742507 := bstep (se 1 (by rfl) ⟨1306880, by rfl⟩ : syracuseStep 1742507 = 2613761) B2613761
theorem B1742831 : Blo 774336 1742831 := bstep (se 1 (by rfl) ⟨1307123, by rfl⟩ : syracuseStep 1742831 = 2614247) B2614247
theorem B4724831 : Blo 774336 4724831 := bstep (se 1 (by rfl) ⟨3543623, by rfl⟩ : syracuseStep 4724831 = 7087247) B7087247
theorem B1743047 : Blo 774336 1743047 := bstep (se 1 (by rfl) ⟨1307285, by rfl⟩ : syracuseStep 1743047 = 2614571) B2614571
theorem B1743227 : Blo 774336 1743227 := bstep (se 1 (by rfl) ⟨1307420, by rfl⟩ : syracuseStep 1743227 = 2614841) B2614841
theorem B3938867 : Blo 774336 3938867 := bstep (se 1 (by rfl) ⟨2954150, by rfl⟩ : syracuseStep 3938867 = 5908301) B5908301
theorem B1743497 : Blo 774336 1743497 := bstep (se 2 (by rfl) ⟨653811, by rfl⟩ : syracuseStep 1743497 = 1307623) B1307623
theorem B5675741 : Blo 774336 5675741 := bstep (se 3 (by rfl) ⟨1064201, by rfl⟩ : syracuseStep 5675741 = 2128403) B2128403
theorem B5610323 : Blo 774336 5610323 := bstep (se 1 (by rfl) ⟨4207742, by rfl⟩ : syracuseStep 5610323 = 8415485) B8415485
theorem B3316571 : Blo 774336 3316571 := bstep (se 1 (by rfl) ⟨2487428, by rfl⟩ : syracuseStep 3316571 = 4974857) B4974857
theorem B2792519 : Blo 774336 2792519 := bstep (se 1 (by rfl) ⟨2094389, by rfl⟩ : syracuseStep 2792519 = 4188779) B4188779
theorem B1744055 : Blo 774336 1744055 := bstep (se 1 (by rfl) ⟨1308041, by rfl⟩ : syracuseStep 1744055 = 2616083) B2616083
theorem B2792663 : Blo 774336 2792663 := bstep (se 1 (by rfl) ⟨2094497, by rfl⟩ : syracuseStep 2792663 = 4188995) B4188995
theorem B3153487 : Blo 774336 3153487 := bstep (se 1 (by rfl) ⟨2365115, by rfl⟩ : syracuseStep 3153487 = 4730231) B4730231
theorem B1744631 : Blo 774336 1744631 := bstep (se 1 (by rfl) ⟨1308473, by rfl⟩ : syracuseStep 1744631 = 2616947) B2616947
theorem B4431773 : Blo 774336 4431773 := bstep (se 3 (by rfl) ⟨830957, by rfl⟩ : syracuseStep 4431773 = 1661915) B1661915
theorem B1744811 : Blo 774336 1744811 := bstep (se 1 (by rfl) ⟨1308608, by rfl⟩ : syracuseStep 1744811 = 2617217) B2617217
theorem B6627703 : Blo 774336 6627703 := bstep (se 1 (by rfl) ⟨4970777, by rfl⟩ : syracuseStep 6627703 = 9941555) B9941555
theorem B1745351 : Blo 774336 1745351 := bstep (se 1 (by rfl) ⟨1309013, by rfl⟩ : syracuseStep 1745351 = 2618027) B2618027
theorem B1745711 : Blo 774336 1745711 := bstep (se 1 (by rfl) ⟨1309283, by rfl⟩ : syracuseStep 1745711 = 2618567) B2618567
theorem B3187567 : Blo 774336 3187567 := bstep (se 1 (by rfl) ⟨2390675, by rfl⟩ : syracuseStep 3187567 = 4781351) B4781351
theorem B8823815 : Blo 774336 8823815 := bstep (se 1 (by rfl) ⟨6617861, by rfl⟩ : syracuseStep 8823815 = 13235723) B13235723
theorem B19932317 : Blo 774336 19932317 := bstep (se 3 (by rfl) ⟨3737309, by rfl⟩ : syracuseStep 19932317 = 7474619) B7474619
theorem B11216029 : Blo 774336 11216029 := bstep (se 3 (by rfl) ⟨2103005, by rfl⟩ : syracuseStep 11216029 = 4206011) B4206011
theorem B4302395 : Blo 774336 4302395 := bstep (se 1 (by rfl) ⟨3226796, by rfl⟩ : syracuseStep 4302395 = 6453593) B6453593
theorem B2205407 : Blo 774336 2205407 := bstep (se 1 (by rfl) ⟨1654055, by rfl⟩ : syracuseStep 2205407 = 3308111) B3308111
theorem B1746719 : Blo 774336 1746719 := bstep (se 1 (by rfl) ⟨1310039, by rfl⟩ : syracuseStep 1746719 = 2620079) B2620079
theorem B1746935 : Blo 774336 1746935 := bstep (se 1 (by rfl) ⟨1310201, by rfl⟩ : syracuseStep 1746935 = 2620403) B2620403
theorem B1747295 : Blo 774336 1747295 := bstep (se 1 (by rfl) ⟨1310471, by rfl⟩ : syracuseStep 1747295 = 2620943) B2620943
theorem B2206091 : Blo 774336 2206091 := bstep (se 1 (by rfl) ⟨1654568, by rfl⟩ : syracuseStep 2206091 = 3309137) B3309137
theorem B1748015 : Blo 774336 1748015 := bstep (se 1 (by rfl) ⟨1311011, by rfl⟩ : syracuseStep 1748015 = 2622023) B2622023
theorem B22686799 : Blo 774336 22686799 := bstep (se 1 (by rfl) ⟨17015099, by rfl⟩ : syracuseStep 22686799 = 34030199) B34030199
theorem B1748303 : Blo 774336 1748303 := bstep (se 1 (by rfl) ⟨1311227, by rfl⟩ : syracuseStep 1748303 = 2622455) B2622455
theorem B1748393 : Blo 774336 1748393 := bstep (se 2 (by rfl) ⟨655647, by rfl⟩ : syracuseStep 1748393 = 1311295) B1311295
theorem B1748879 : Blo 774336 1748879 := bstep (se 1 (by rfl) ⟨1311659, by rfl⟩ : syracuseStep 1748879 = 2623319) B2623319
theorem B11186095 : Blo 774336 11186095 := bstep (se 1 (by rfl) ⟨8389571, by rfl⟩ : syracuseStep 11186095 = 16779143) B16779143
theorem B2207731 : Blo 774336 2207731 := bstep (se 1 (by rfl) ⟨1655798, by rfl⟩ : syracuseStep 2207731 = 3311597) B3311597
theorem B3321985 : Blo 774336 3321985 := bstep (se 2 (by rfl) ⟨1245744, by rfl⟩ : syracuseStep 3321985 = 2491489) B2491489
theorem B4731203 : Blo 774336 4731203 := bstep (se 1 (by rfl) ⟨3548402, by rfl⟩ : syracuseStep 4731203 = 7096805) B7096805
theorem B1749599 : Blo 774336 1749599 := bstep (se 1 (by rfl) ⟨1312199, by rfl⟩ : syracuseStep 1749599 = 2624399) B2624399
theorem B1258249 : Blo 774336 1258249 := bstep (se 2 (by rfl) ⟨471843, by rfl⟩ : syracuseStep 1258249 = 943687) B943687
theorem B1750427 : Blo 774336 1750427 := bstep (se 1 (by rfl) ⟨1312820, by rfl⟩ : syracuseStep 1750427 = 2625641) B2625641
theorem B4961735 : Blo 774336 4961735 := bstep (se 1 (by rfl) ⟨3721301, by rfl⟩ : syracuseStep 4961735 = 7442603) B7442603
theorem B2209463 : Blo 774336 2209463 := bstep (se 1 (by rfl) ⟨1657097, by rfl⟩ : syracuseStep 2209463 = 3314195) B3314195
theorem B2209531 : Blo 774336 2209531 := bstep (se 1 (by rfl) ⟨1657148, by rfl⟩ : syracuseStep 2209531 = 3314297) B3314297
theorem B3979145 : Blo 774336 3979145 := bstep (se 2 (by rfl) ⟨1492179, by rfl⟩ : syracuseStep 3979145 = 2984359) B2984359
theorem B38320067 : Blo 774336 38320067 := bstep (se 1 (by rfl) ⟨28740050, by rfl⟩ : syracuseStep 38320067 = 57480101) B57480101
theorem B1751003 : Blo 774336 1751003 := bstep (se 1 (by rfl) ⟨1313252, by rfl⟩ : syracuseStep 1751003 = 2626505) B2626505
theorem B2242657 : Blo 774336 2242657 := bstep (se 2 (by rfl) ⟨840996, by rfl⟩ : syracuseStep 2242657 = 1681993) B1681993
theorem B1751183 : Blo 774336 1751183 := bstep (se 1 (by rfl) ⟨1313387, by rfl⟩ : syracuseStep 1751183 = 2626775) B2626775
theorem B1751201 : Blo 774336 1751201 := bstep (se 2 (by rfl) ⟨656700, by rfl⟩ : syracuseStep 1751201 = 1313401) B1313401
theorem B2210237 : Blo 774336 2210237 := bstep (se 3 (by rfl) ⟨414419, by rfl⟩ : syracuseStep 2210237 = 828839) B828839
theorem B1161755 : Blo 774336 1161755 := bstep (se 1 (by rfl) ⟨871316, by rfl⟩ : syracuseStep 1161755 = 1742633) B1742633
theorem B1161833 : Blo 774336 1161833 := bstep (se 2 (by rfl) ⟨435687, by rfl⟩ : syracuseStep 1161833 = 871375) B871375
theorem B12270197 : Blo 774336 12270197 := bstep (se 5 (by rfl) ⟨575165, by rfl⟩ : syracuseStep 12270197 = 1150331) B1150331
theorem B5880599 : Blo 774336 5880599 := bstep (se 1 (by rfl) ⟨4410449, by rfl⟩ : syracuseStep 5880599 = 8820899) B8820899
theorem B2210807 : Blo 774336 2210807 := bstep (se 1 (by rfl) ⟨1658105, by rfl⟩ : syracuseStep 2210807 = 3316211) B3316211
theorem B1162361 : Blo 774336 1162361 := bstep (se 2 (by rfl) ⟨435885, by rfl⟩ : syracuseStep 1162361 = 871771) B871771
theorem B1162463 : Blo 774336 1162463 := bstep (se 1 (by rfl) ⟨871847, by rfl⟩ : syracuseStep 1162463 = 1743695) B1743695
theorem B1162505 : Blo 774336 1162505 := bstep (se 2 (by rfl) ⟨435939, by rfl⟩ : syracuseStep 1162505 = 871879) B871879
theorem B1162607 : Blo 774336 1162607 := bstep (se 1 (by rfl) ⟨871955, by rfl⟩ : syracuseStep 1162607 = 1743911) B1743911
theorem B2211239 : Blo 774336 2211239 := bstep (se 1 (by rfl) ⟨1658429, by rfl⟩ : syracuseStep 2211239 = 3316859) B3316859
theorem B1162727 : Blo 774336 1162727 := bstep (se 1 (by rfl) ⟨872045, by rfl⟩ : syracuseStep 1162727 = 1744091) B1744091
theorem B1162859 : Blo 774336 1162859 := bstep (se 1 (by rfl) ⟨872144, by rfl⟩ : syracuseStep 1162859 = 1744289) B1744289
theorem B1654415 : Blo 774336 1654415 := bstep (se 1 (by rfl) ⟨1240811, by rfl⟩ : syracuseStep 1654415 = 2481623) B2481623
theorem B1162985 : Blo 774336 1162985 := bstep (se 2 (by rfl) ⟨436119, by rfl⟩ : syracuseStep 1162985 = 872239) B872239
theorem B1163129 : Blo 774336 1163129 := bstep (se 2 (by rfl) ⟨436173, by rfl⟩ : syracuseStep 1163129 = 872347) B872347
theorem B1163231 : Blo 774336 1163231 := bstep (se 1 (by rfl) ⟨872423, by rfl⟩ : syracuseStep 1163231 = 1744847) B1744847
theorem B7979147 : Blo 774336 7979147 := bstep (se 1 (by rfl) ⟨5984360, by rfl⟩ : syracuseStep 7979147 = 11968721) B11968721
theorem B1163483 : Blo 774336 1163483 := bstep (se 1 (by rfl) ⟨872612, by rfl⟩ : syracuseStep 1163483 = 1745225) B1745225
theorem B1163495 : Blo 774336 1163495 := bstep (se 1 (by rfl) ⟨872621, by rfl⟩ : syracuseStep 1163495 = 1745243) B1745243
theorem B1163657 : Blo 774336 1163657 := bstep (se 2 (by rfl) ⟨436371, by rfl⟩ : syracuseStep 1163657 = 872743) B872743
theorem B1163753 : Blo 774336 1163753 := bstep (se 2 (by rfl) ⟨436407, by rfl⟩ : syracuseStep 1163753 = 872815) B872815
theorem B13419017 : Blo 774336 13419017 := bstep (se 2 (by rfl) ⟨5032131, by rfl⟩ : syracuseStep 13419017 = 10064263) B10064263
theorem B1163879 : Blo 774336 1163879 := bstep (se 1 (by rfl) ⟨872909, by rfl⟩ : syracuseStep 1163879 = 1745819) B1745819
theorem B1164011 : Blo 774336 1164011 := bstep (se 1 (by rfl) ⟨873008, by rfl⟩ : syracuseStep 1164011 = 1746017) B1746017
theorem B1164041 : Blo 774336 1164041 := bstep (se 2 (by rfl) ⟨436515, by rfl⟩ : syracuseStep 1164041 = 873031) B873031
theorem B1164143 : Blo 774336 1164143 := bstep (se 1 (by rfl) ⟨873107, by rfl⟩ : syracuseStep 1164143 = 1746215) B1746215
theorem B1164395 : Blo 774336 1164395 := bstep (se 1 (by rfl) ⟨873296, by rfl⟩ : syracuseStep 1164395 = 1746593) B1746593
theorem B1164635 : Blo 774336 1164635 := bstep (se 1 (by rfl) ⟨873476, by rfl⟩ : syracuseStep 1164635 = 1746953) B1746953
theorem B2213335 : Blo 774336 2213335 := bstep (se 1 (by rfl) ⟨1660001, by rfl⟩ : syracuseStep 2213335 = 3320003) B3320003
theorem B1164911 : Blo 774336 1164911 := bstep (se 1 (by rfl) ⟨873683, by rfl⟩ : syracuseStep 1164911 = 1747367) B1747367
theorem B1164983 : Blo 774336 1164983 := bstep (se 1 (by rfl) ⟨873737, by rfl⟩ : syracuseStep 1164983 = 1747475) B1747475
theorem B1165019 : Blo 774336 1165019 := bstep (se 1 (by rfl) ⟨873764, by rfl⟩ : syracuseStep 1165019 = 1747529) B1747529
theorem B1165193 : Blo 774336 1165193 := bstep (se 2 (by rfl) ⟨436947, by rfl⟩ : syracuseStep 1165193 = 873895) B873895
theorem B1165295 : Blo 774336 1165295 := bstep (se 1 (by rfl) ⟨873971, by rfl⟩ : syracuseStep 1165295 = 1747943) B1747943
theorem B7096511 : Blo 774336 7096511 := bstep (se 1 (by rfl) ⟨5322383, by rfl⟩ : syracuseStep 7096511 = 10644767) B10644767
theorem B1165547 : Blo 774336 1165547 := bstep (se 1 (by rfl) ⟨874160, by rfl⟩ : syracuseStep 1165547 = 1748321) B1748321
theorem B1165607 : Blo 774336 1165607 := bstep (se 1 (by rfl) ⟨874205, by rfl⟩ : syracuseStep 1165607 = 1748411) B1748411
theorem B1165691 : Blo 774336 1165691 := bstep (se 1 (by rfl) ⟨874268, by rfl⟩ : syracuseStep 1165691 = 1748537) B1748537
theorem B6310345 : Blo 774336 6310345 := bstep (se 2 (by rfl) ⟨2366379, by rfl⟩ : syracuseStep 6310345 = 4732759) B4732759
theorem B1165961 : Blo 774336 1165961 := bstep (se 2 (by rfl) ⟨437235, by rfl⟩ : syracuseStep 1165961 = 874471) B874471
theorem B1166135 : Blo 774336 1166135 := bstep (se 1 (by rfl) ⟨874601, by rfl⟩ : syracuseStep 1166135 = 1749203) B1749203
theorem B1166171 : Blo 774336 1166171 := bstep (se 1 (by rfl) ⟨874628, by rfl⟩ : syracuseStep 1166171 = 1749257) B1749257
theorem B47893355 : Blo 774336 47893355 := bstep (se 1 (by rfl) ⟨35920016, by rfl⟩ : syracuseStep 47893355 = 71840033) B71840033
theorem B1166315 : Blo 774336 1166315 := bstep (se 1 (by rfl) ⟨874736, by rfl⟩ : syracuseStep 1166315 = 1749473) B1749473
theorem B1166519 : Blo 774336 1166519 := bstep (se 1 (by rfl) ⟨874889, by rfl⟩ : syracuseStep 1166519 = 1749779) B1749779
theorem B4410611 : Blo 774336 4410611 := bstep (se 1 (by rfl) ⟨3307958, by rfl⟩ : syracuseStep 4410611 = 6615917) B6615917
theorem B1658191 : Blo 774336 1658191 := bstep (se 1 (by rfl) ⟨1243643, by rfl⟩ : syracuseStep 1658191 = 2487287) B2487287
theorem B1166759 : Blo 774336 1166759 := bstep (se 1 (by rfl) ⟨875069, by rfl⟩ : syracuseStep 1166759 = 1750139) B1750139
theorem B1330679 : Blo 774336 1330679 := bstep (se 1 (by rfl) ⟨998009, by rfl⟩ : syracuseStep 1330679 = 1996019) B1996019
theorem B1166843 : Blo 774336 1166843 := bstep (se 1 (by rfl) ⟨875132, by rfl⟩ : syracuseStep 1166843 = 1750265) B1750265
theorem B5983807 : Blo 774336 5983807 := bstep (se 1 (by rfl) ⟨4487855, by rfl⟩ : syracuseStep 5983807 = 8975711) B8975711
theorem B1166939 : Blo 774336 1166939 := bstep (se 1 (by rfl) ⟨875204, by rfl⟩ : syracuseStep 1166939 = 1750409) B1750409
theorem B14929555 : Blo 774336 14929555 := bstep (se 1 (by rfl) ⟨11197166, by rfl⟩ : syracuseStep 14929555 = 22394333) B22394333
theorem B1167023 : Blo 774336 1167023 := bstep (se 1 (by rfl) ⟨875267, by rfl⟩ : syracuseStep 1167023 = 1750535) B1750535
theorem B1167143 : Blo 774336 1167143 := bstep (se 1 (by rfl) ⟨875357, by rfl⟩ : syracuseStep 1167143 = 1750715) B1750715
theorem B1167227 : Blo 774336 1167227 := bstep (se 1 (by rfl) ⟨875420, by rfl⟩ : syracuseStep 1167227 = 1750841) B1750841
theorem B12472211 : Blo 774336 12472211 := bstep (se 1 (by rfl) ⟨9354158, by rfl⟩ : syracuseStep 12472211 = 18708317) B18708317
theorem B7950241 : Blo 774336 7950241 := bstep (se 2 (by rfl) ⟨2981340, by rfl⟩ : syracuseStep 7950241 = 5962681) B5962681
theorem B17256509 : Blo 774336 17256509 := bstep (se 3 (by rfl) ⟨3235595, by rfl⟩ : syracuseStep 17256509 = 6471191) B6471191
theorem B774375 : Blo 774336 774375 := bstep (se 1 (by rfl) ⟨580781, by rfl⟩ : syracuseStep 774375 = 1161563) B1161563
theorem B774527 : Blo 774336 774527 := bstep (se 1 (by rfl) ⟨580895, by rfl⟩ : syracuseStep 774527 = 1161791) B1161791
theorem B774607 : Blo 774336 774607 := bstep (se 1 (by rfl) ⟨580955, by rfl⟩ : syracuseStep 774607 = 1161911) B1161911
theorem B1397225 : Blo 774336 1397225 := bstep (se 2 (by rfl) ⟨523959, by rfl⟩ : syracuseStep 1397225 = 1047919) B1047919
theorem B9458221 : Blo 774336 9458221 := bstep (se 3 (by rfl) ⟨1773416, by rfl⟩ : syracuseStep 9458221 = 3546833) B3546833
theorem B774759 : Blo 774336 774759 := bstep (se 1 (by rfl) ⟨581069, by rfl⟩ : syracuseStep 774759 = 1162139) B1162139
theorem B840295 : Blo 774336 840295 := bstep (se 1 (by rfl) ⟨630221, by rfl⟩ : syracuseStep 840295 = 1260443) B1260443
theorem B775023 : Blo 774336 775023 := bstep (se 1 (by rfl) ⟨581267, by rfl⟩ : syracuseStep 775023 = 1162535) B1162535
theorem B775079 : Blo 774336 775079 := bstep (se 1 (by rfl) ⟨581309, by rfl⟩ : syracuseStep 775079 = 1162619) B1162619
theorem B775163 : Blo 774336 775163 := bstep (se 1 (by rfl) ⟨581372, by rfl⟩ : syracuseStep 775163 = 1162745) B1162745
theorem B1659899 : Blo 774336 1659899 := bstep (se 1 (by rfl) ⟨1244924, by rfl⟩ : syracuseStep 1659899 = 2489849) B2489849
theorem B775231 : Blo 774336 775231 := bstep (se 1 (by rfl) ⟨581423, by rfl⟩ : syracuseStep 775231 = 1162847) B1162847
theorem B873535 : Blo 774336 873535 := bstep (se 1 (by rfl) ⟨655151, by rfl⟩ : syracuseStep 873535 = 1310303) B1310303
theorem B775375 : Blo 774336 775375 := bstep (se 1 (by rfl) ⟨581531, by rfl⟩ : syracuseStep 775375 = 1163063) B1163063
theorem B873679 : Blo 774336 873679 := bstep (se 1 (by rfl) ⟨655259, by rfl⟩ : syracuseStep 873679 = 1310519) B1310519
theorem B8410331 : Blo 774336 8410331 := bstep (se 1 (by rfl) ⟨6307748, by rfl⟩ : syracuseStep 8410331 = 12615497) B12615497
theorem B775579 : Blo 774336 775579 := bstep (se 1 (by rfl) ⟨581684, by rfl⟩ : syracuseStep 775579 = 1163369) B1163369
theorem B775791 : Blo 774336 775791 := bstep (se 1 (by rfl) ⟨581843, by rfl⟩ : syracuseStep 775791 = 1163687) B1163687
theorem B775847 : Blo 774336 775847 := bstep (se 1 (by rfl) ⟨581885, by rfl⟩ : syracuseStep 775847 = 1163771) B1163771
theorem B775931 : Blo 774336 775931 := bstep (se 1 (by rfl) ⟨581948, by rfl⟩ : syracuseStep 775931 = 1163897) B1163897
theorem B775967 : Blo 774336 775967 := bstep (se 1 (by rfl) ⟨581975, by rfl⟩ : syracuseStep 775967 = 1163951) B1163951
theorem B775999 : Blo 774336 775999 := bstep (se 1 (by rfl) ⟨581999, by rfl⟩ : syracuseStep 775999 = 1163999) B1163999
theorem B776175 : Blo 774336 776175 := bstep (se 1 (by rfl) ⟨582131, by rfl⟩ : syracuseStep 776175 = 1164263) B1164263
theorem B1398775 : Blo 774336 1398775 := bstep (se 1 (by rfl) ⟨1049081, by rfl⟩ : syracuseStep 1398775 = 2098163) B2098163
theorem B874651 : Blo 774336 874651 := bstep (se 1 (by rfl) ⟨655988, by rfl⟩ : syracuseStep 874651 = 1311977) B1311977
theorem B776347 : Blo 774336 776347 := bstep (se 1 (by rfl) ⟨582260, by rfl⟩ : syracuseStep 776347 = 1164521) B1164521
theorem B776383 : Blo 774336 776383 := bstep (se 1 (by rfl) ⟨582287, by rfl⟩ : syracuseStep 776383 = 1164575) B1164575
theorem B874687 : Blo 774336 874687 := bstep (se 1 (by rfl) ⟨656015, by rfl⟩ : syracuseStep 874687 = 1312031) B1312031
theorem B776495 : Blo 774336 776495 := bstep (se 1 (by rfl) ⟨582371, by rfl⟩ : syracuseStep 776495 = 1164743) B1164743
theorem B776731 : Blo 774336 776731 := bstep (se 1 (by rfl) ⟨582548, by rfl⟩ : syracuseStep 776731 = 1165097) B1165097
theorem B776735 : Blo 774336 776735 := bstep (se 1 (by rfl) ⟨582551, by rfl⟩ : syracuseStep 776735 = 1165103) B1165103
theorem B11950679 : Blo 774336 11950679 := bstep (se 1 (by rfl) ⟨8963009, by rfl⟩ : syracuseStep 11950679 = 17926019) B17926019
theorem B2480777 : Blo 774336 2480777 := bstep (se 2 (by rfl) ⟨930291, by rfl⟩ : syracuseStep 2480777 = 1860583) B1860583
theorem B777051 : Blo 774336 777051 := bstep (se 1 (by rfl) ⟨582788, by rfl⟩ : syracuseStep 777051 = 1165577) B1165577
theorem B777119 : Blo 774336 777119 := bstep (se 1 (by rfl) ⟨582839, by rfl⟩ : syracuseStep 777119 = 1165679) B1165679
theorem B777263 : Blo 774336 777263 := bstep (se 1 (by rfl) ⟨582947, by rfl⟩ : syracuseStep 777263 = 1165895) B1165895
theorem B777287 : Blo 774336 777287 := bstep (se 1 (by rfl) ⟨582965, by rfl⟩ : syracuseStep 777287 = 1165931) B1165931
theorem B777439 : Blo 774336 777439 := bstep (se 1 (by rfl) ⟨583079, by rfl⟩ : syracuseStep 777439 = 1166159) B1166159
theorem B777703 : Blo 774336 777703 := bstep (se 1 (by rfl) ⟨583277, by rfl⟩ : syracuseStep 777703 = 1166555) B1166555
theorem B4414985 : Blo 774336 4414985 := bstep (se 2 (by rfl) ⟨1655619, by rfl⟩ : syracuseStep 4414985 = 3311239) B3311239
theorem B777819 : Blo 774336 777819 := bstep (se 1 (by rfl) ⟨583364, by rfl⟩ : syracuseStep 777819 = 1166729) B1166729
theorem B15163139 : Blo 774336 15163139 := bstep (se 1 (by rfl) ⟨11372354, by rfl⟩ : syracuseStep 15163139 = 22744709) B22744709
theorem B778055 : Blo 774336 778055 := bstep (se 1 (by rfl) ⟨583541, by rfl⟩ : syracuseStep 778055 = 1167083) B1167083
theorem B778207 : Blo 774336 778207 := bstep (se 1 (by rfl) ⟨583655, by rfl⟩ : syracuseStep 778207 = 1167311) B1167311
theorem B529915877 : Blo 774336 529915877 := bstep (se 4 (by rfl) ⟨49679613, by rfl⟩ : syracuseStep 529915877 = 99359227) B99359227
theorem B4415735 : Blo 774336 4415735 := bstep (se 1 (by rfl) ⟨3311801, by rfl⟩ : syracuseStep 4415735 = 6623603) B6623603
theorem B1106303 : Blo 774336 1106303 := bstep (se 1 (by rfl) ⟨829727, by rfl⟩ : syracuseStep 1106303 = 1659455) B1659455
theorem B2482751 : Blo 774336 2482751 := bstep (se 1 (by rfl) ⟨1862063, by rfl⟩ : syracuseStep 2482751 = 3724127) B3724127
theorem B4416875 : Blo 774336 4416875 := bstep (se 1 (by rfl) ⟨3312656, by rfl⟩ : syracuseStep 4416875 = 6625313) B6625313
theorem B7071113 : Blo 774336 7071113 := bstep (se 2 (by rfl) ⟨2651667, by rfl⟩ : syracuseStep 7071113 = 5303335) B5303335
theorem B2614895 : Blo 774336 2614895 := bstep (se 1 (by rfl) ⟨1961171, by rfl⟩ : syracuseStep 2614895 = 3922343) B3922343
theorem B2615003 : Blo 774336 2615003 := bstep (se 1 (by rfl) ⟨1961252, by rfl⟩ : syracuseStep 2615003 = 3922505) B3922505
theorem B1861343 : Blo 774336 1861343 := bstep (se 1 (by rfl) ⟨1396007, by rfl⟩ : syracuseStep 1861343 = 2792015) B2792015
theorem B4778003 : Blo 774336 4778003 := bstep (se 1 (by rfl) ⟨3583502, by rfl⟩ : syracuseStep 4778003 = 7167005) B7167005
theorem B3926231 : Blo 774336 3926231 := bstep (se 1 (by rfl) ⟨2944673, by rfl⟩ : syracuseStep 3926231 = 5889347) B5889347
theorem B3926555 : Blo 774336 3926555 := bstep (se 1 (by rfl) ⟨2944916, by rfl⟩ : syracuseStep 3926555 = 5889833) B5889833
theorem B3992267 : Blo 774336 3992267 := bstep (se 1 (by rfl) ⟨2994200, by rfl⟩ : syracuseStep 3992267 = 5988401) B5988401
theorem B2616299 : Blo 774336 2616299 := bstep (se 1 (by rfl) ⟨1962224, by rfl⟩ : syracuseStep 2616299 = 3924449) B3924449
theorem B2616353 : Blo 774336 2616353 := bstep (se 2 (by rfl) ⟨981132, by rfl⟩ : syracuseStep 2616353 = 1962265) B1962265
theorem B7072865 : Blo 774336 7072865 := bstep (se 2 (by rfl) ⟨2652324, by rfl⟩ : syracuseStep 7072865 = 5304649) B5304649
theorem B2944097 : Blo 774336 2944097 := bstep (se 2 (by rfl) ⟨1104036, by rfl⟩ : syracuseStep 2944097 = 2208073) B2208073
theorem B1961081 : Blo 774336 1961081 := bstep (se 2 (by rfl) ⟨735405, by rfl⟩ : syracuseStep 1961081 = 1470811) B1470811
theorem B10612043 : Blo 774336 10612043 := bstep (se 1 (by rfl) ⟨7959032, by rfl⟩ : syracuseStep 10612043 = 15918065) B15918065
theorem B13266341 : Blo 774336 13266341 := bstep (se 4 (by rfl) ⟨1243719, by rfl⟩ : syracuseStep 13266341 = 2487439) B2487439
theorem B1470059 : Blo 774336 1470059 := bstep (se 1 (by rfl) ⟨1102544, by rfl⟩ : syracuseStep 1470059 = 2205089) B2205089
theorem B2486159 : Blo 774336 2486159 := bstep (se 1 (by rfl) ⟨1864619, by rfl⟩ : syracuseStep 2486159 = 3729239) B3729239
theorem B1863803 : Blo 774336 1863803 := bstep (se 1 (by rfl) ⟨1397852, by rfl⟩ : syracuseStep 1863803 = 2795705) B2795705
theorem B19919195 : Blo 774336 19919195 := bstep (se 1 (by rfl) ⟨14939396, by rfl⟩ : syracuseStep 19919195 = 29878793) B29878793
theorem B1962377 : Blo 774336 1962377 := bstep (se 2 (by rfl) ⟨735891, by rfl⟩ : syracuseStep 1962377 = 1471783) B1471783
theorem B2617811 : Blo 774336 2617811 := bstep (se 1 (by rfl) ⟨1963358, by rfl⟩ : syracuseStep 2617811 = 3926717) B3926717
theorem B3928823 : Blo 774336 3928823 := bstep (se 1 (by rfl) ⟨2946617, by rfl⟩ : syracuseStep 3928823 = 5893235) B5893235
theorem B1307711 : Blo 774336 1307711 := bstep (se 1 (by rfl) ⟨980783, by rfl⟩ : syracuseStep 1307711 = 1961567) B1961567
theorem B1569899 : Blo 774336 1569899 := bstep (se 1 (by rfl) ⟨1177424, by rfl⟩ : syracuseStep 1569899 = 2354849) B2354849
theorem B1864811 : Blo 774336 1864811 := bstep (se 1 (by rfl) ⟨1398608, by rfl⟩ : syracuseStep 1864811 = 2797217) B2797217
theorem B18216355 : Blo 774336 18216355 := bstep (se 1 (by rfl) ⟨13662266, by rfl⟩ : syracuseStep 18216355 = 27324533) B27324533
theorem B1308271 : Blo 774336 1308271 := bstep (se 1 (by rfl) ⟨981203, by rfl⟩ : syracuseStep 1308271 = 1962407) B1962407
theorem B1963703 : Blo 774336 1963703 := bstep (se 1 (by rfl) ⟨1472777, by rfl⟩ : syracuseStep 1963703 = 2945555) B2945555
theorem B1308379 : Blo 774336 1308379 := bstep (se 1 (by rfl) ⟨981284, by rfl⟩ : syracuseStep 1308379 = 1962569) B1962569
theorem B7075937 : Blo 774336 7075937 := bstep (se 2 (by rfl) ⟨2653476, by rfl⟩ : syracuseStep 7075937 = 5306953) B5306953
theorem B1046719 : Blo 774336 1046719 := bstep (se 1 (by rfl) ⟨785039, by rfl⟩ : syracuseStep 1046719 = 1570079) B1570079
theorem B2488619 : Blo 774336 2488619 := bstep (se 1 (by rfl) ⟨1866464, by rfl⟩ : syracuseStep 2488619 = 3732929) B3732929
theorem B2619755 : Blo 774336 2619755 := bstep (se 1 (by rfl) ⟨1964816, by rfl⟩ : syracuseStep 2619755 = 3929633) B3929633
theorem B2620025 : Blo 774336 2620025 := bstep (se 2 (by rfl) ⟨982509, by rfl⟩ : syracuseStep 2620025 = 1965019) B1965019
theorem B4979389 : Blo 774336 4979389 := bstep (se 3 (by rfl) ⟨933635, by rfl⟩ : syracuseStep 4979389 = 1867271) B1867271
theorem B1309675 : Blo 774336 1309675 := bstep (se 1 (by rfl) ⟨982256, by rfl⟩ : syracuseStep 1309675 = 1964513) B1964513
theorem B2620457 : Blo 774336 2620457 := bstep (se 2 (by rfl) ⟨982671, by rfl⟩ : syracuseStep 2620457 = 1965343) B1965343
theorem B1244207 : Blo 774336 1244207 := bstep (se 1 (by rfl) ⟨933155, by rfl⟩ : syracuseStep 1244207 = 1866311) B1866311
theorem B1309817 : Blo 774336 1309817 := bstep (se 2 (by rfl) ⟨491181, by rfl⟩ : syracuseStep 1309817 = 982363) B982363
theorem B1179049 : Blo 774336 1179049 := bstep (se 2 (by rfl) ⟨442143, by rfl⟩ : syracuseStep 1179049 = 884287) B884287
theorem B2358791 : Blo 774336 2358791 := bstep (se 1 (by rfl) ⟨1769093, by rfl⟩ : syracuseStep 2358791 = 3538187) B3538187
theorem B1965647 : Blo 774336 1965647 := bstep (se 1 (by rfl) ⟨1474235, by rfl⟩ : syracuseStep 1965647 = 2948471) B2948471
theorem B3931739 : Blo 774336 3931739 := bstep (se 1 (by rfl) ⟨2948804, by rfl⟩ : syracuseStep 3931739 = 5897609) B5897609
theorem B37715705 : Blo 774336 37715705 := bstep (se 2 (by rfl) ⟨14143389, by rfl⟩ : syracuseStep 37715705 = 28286779) B28286779
theorem B4423481 : Blo 774336 4423481 := bstep (se 2 (by rfl) ⟨1658805, by rfl⟩ : syracuseStep 4423481 = 3317611) B3317611
theorem B5603197 : Blo 774336 5603197 := bstep (se 3 (by rfl) ⟨1050599, by rfl⟩ : syracuseStep 5603197 = 2101199) B2101199
theorem B8946011 : Blo 774336 8946011 := bstep (se 1 (by rfl) ⟨6709508, by rfl⟩ : syracuseStep 8946011 = 13419017) B13419017
theorem B2621807 : Blo 774336 2621807 := bstep (se 1 (by rfl) ⟨1966355, by rfl⟩ : syracuseStep 2621807 = 3932711) B3932711
theorem B1245611 : Blo 774336 1245611 := bstep (se 1 (by rfl) ⟨934208, by rfl⟩ : syracuseStep 1245611 = 1868417) B1868417
theorem B2950141 : Blo 774336 2950141 := bstep (se 3 (by rfl) ⟨553151, by rfl⟩ : syracuseStep 2950141 = 1106303) B1106303
theorem B1967611 : Blo 774336 1967611 := bstep (se 1 (by rfl) ⟨1475708, by rfl⟩ : syracuseStep 1967611 = 2951417) B2951417
theorem B3540743 : Blo 774336 3540743 := bstep (se 1 (by rfl) ⟨2655557, by rfl⟩ : syracuseStep 3540743 = 5311115) B5311115
theorem B6620939 : Blo 774336 6620939 := bstep (se 1 (by rfl) ⟨4965704, by rfl⟩ : syracuseStep 6620939 = 9931409) B9931409
theorem B13240097 : Blo 774336 13240097 := bstep (se 2 (by rfl) ⟨4965036, by rfl⟩ : syracuseStep 13240097 = 9930073) B9930073
theorem B2951113 : Blo 774336 2951113 := bstep (se 2 (by rfl) ⟨1106667, by rfl⟩ : syracuseStep 2951113 = 2213335) B2213335
theorem B1575073 : Blo 774336 1575073 := bstep (se 2 (by rfl) ⟨590652, by rfl⟩ : syracuseStep 1575073 = 1181305) B1181305
theorem B887119 : Blo 774336 887119 := bstep (se 1 (by rfl) ⟨665339, by rfl⟩ : syracuseStep 887119 = 1330679) B1330679
theorem B1771903 : Blo 774336 1771903 := bstep (se 1 (by rfl) ⟨1328927, by rfl⟩ : syracuseStep 1771903 = 2657855) B2657855
theorem B2951599 : Blo 774336 2951599 := bstep (se 1 (by rfl) ⟨2213699, by rfl⟩ : syracuseStep 2951599 = 4427399) B4427399
theorem B16779757 : Blo 774336 16779757 := bstep (se 3 (by rfl) ⟨3146204, by rfl⟩ : syracuseStep 16779757 = 6292409) B6292409
theorem B8850059 : Blo 774336 8850059 := bstep (se 1 (by rfl) ⟨6637544, by rfl⟩ : syracuseStep 8850059 = 13275089) B13275089
theorem B4426397 : Blo 774336 4426397 := bstep (se 3 (by rfl) ⟨829949, by rfl⟩ : syracuseStep 4426397 = 1659899) B1659899
theorem B11504339 : Blo 774336 11504339 := bstep (se 1 (by rfl) ⟨8628254, by rfl⟩ : syracuseStep 11504339 = 17256509) B17256509
theorem B2624723 : Blo 774336 2624723 := bstep (se 1 (by rfl) ⟨1968542, by rfl⟩ : syracuseStep 2624723 = 3937085) B3937085
theorem B1969535 : Blo 774336 1969535 := bstep (se 1 (by rfl) ⟨1477151, by rfl⟩ : syracuseStep 1969535 = 2954303) B2954303
theorem B2624993 : Blo 774336 2624993 := bstep (se 2 (by rfl) ⟨984372, by rfl⟩ : syracuseStep 2624993 = 1968745) B1968745
theorem B30249065 : Blo 774336 30249065 := bstep (se 2 (by rfl) ⟨11343399, by rfl⟩ : syracuseStep 30249065 = 22686799) B22686799
theorem B2625911 : Blo 774336 2625911 := bstep (se 1 (by rfl) ⟨1969433, by rfl⟩ : syracuseStep 2625911 = 3938867) B3938867
theorem B7967119 : Blo 774336 7967119 := bstep (se 1 (by rfl) ⟨5975339, by rfl⟩ : syracuseStep 7967119 = 11950679) B11950679
theorem B3936761 : Blo 774336 3936761 := bstep (se 2 (by rfl) ⟨1476285, by rfl⟩ : syracuseStep 3936761 = 2952571) B2952571
theorem B3740215 : Blo 774336 3740215 := bstep (se 1 (by rfl) ⟨2805161, by rfl⟩ : syracuseStep 3740215 = 5610323) B5610323
theorem B2626721 : Blo 774336 2626721 := bstep (se 2 (by rfl) ⟨985020, by rfl⟩ : syracuseStep 2626721 = 1970041) B1970041
theorem B14914793 : Blo 774336 14914793 := bstep (se 2 (by rfl) ⟨5593047, by rfl⟩ : syracuseStep 14914793 = 11186095) B11186095
theorem B2954515 : Blo 774336 2954515 := bstep (se 1 (by rfl) ⟨2215886, by rfl⟩ : syracuseStep 2954515 = 4431773) B4431773
theorem B353277251 : Blo 774336 353277251 := bstep (se 1 (by rfl) ⟨264957938, by rfl⟩ : syracuseStep 353277251 = 529915877) B529915877
theorem B12588509 : Blo 774336 12588509 := bstep (se 3 (by rfl) ⟨2360345, by rfl⟩ : syracuseStep 12588509 = 4720691) B4720691
theorem B4429313 : Blo 774336 4429313 := bstep (se 2 (by rfl) ⟨1660992, by rfl⟩ : syracuseStep 4429313 = 3321985) B3321985
theorem B1677665 : Blo 774336 1677665 := bstep (se 2 (by rfl) ⟨629124, by rfl⟩ : syracuseStep 1677665 = 1258249) B1258249
theorem B1743263 : Blo 774336 1743263 := bstep (se 1 (by rfl) ⟨1307447, by rfl⟩ : syracuseStep 1743263 = 2614895) B2614895
theorem B1743335 : Blo 774336 1743335 := bstep (se 1 (by rfl) ⟨1307501, by rfl⟩ : syracuseStep 1743335 = 2615003) B2615003
theorem B3185335 : Blo 774336 3185335 := bstep (se 1 (by rfl) ⟨2389001, by rfl⟩ : syracuseStep 3185335 = 4778003) B4778003
theorem B2661511 : Blo 774336 2661511 := bstep (se 1 (by rfl) ⟨1996133, by rfl⟩ : syracuseStep 2661511 = 3992267) B3992267
theorem B24288473 : Blo 774336 24288473 := bstep (se 2 (by rfl) ⟨9108177, by rfl⟩ : syracuseStep 24288473 = 18216355) B18216355
theorem B1744199 : Blo 774336 1744199 := bstep (se 1 (by rfl) ⟨1308149, by rfl⟩ : syracuseStep 1744199 = 2616299) B2616299
theorem B1744235 : Blo 774336 1744235 := bstep (se 1 (by rfl) ⟨1308176, by rfl⟩ : syracuseStep 1744235 = 2616353) B2616353
theorem B1744361 : Blo 774336 1744361 := bstep (se 2 (by rfl) ⟨654135, by rfl⟩ : syracuseStep 1744361 = 1308271) B1308271
theorem B1744505 : Blo 774336 1744505 := bstep (se 2 (by rfl) ⟨654189, by rfl⟩ : syracuseStep 1744505 = 1308379) B1308379
theorem B3317885 : Blo 774336 3317885 := bstep (se 3 (by rfl) ⟨622103, by rfl⟩ : syracuseStep 3317885 = 1244207) B1244207
theorem B2990209 : Blo 774336 2990209 := bstep (se 2 (by rfl) ⟨1121328, by rfl⟩ : syracuseStep 2990209 = 2242657) B2242657
theorem B3154135 : Blo 774336 3154135 := bstep (se 1 (by rfl) ⟨2365601, by rfl⟩ : syracuseStep 3154135 = 4731203) B4731203
theorem B13279463 : Blo 774336 13279463 := bstep (se 1 (by rfl) ⟨9959597, by rfl⟩ : syracuseStep 13279463 = 19919195) B19919195
theorem B1745207 : Blo 774336 1745207 := bstep (se 1 (by rfl) ⟨1308905, by rfl⟩ : syracuseStep 1745207 = 2617811) B2617811
theorem B1746233 : Blo 774336 1746233 := bstep (se 2 (by rfl) ⟨654837, by rfl⟩ : syracuseStep 1746233 = 1309675) B1309675
theorem B1746503 : Blo 774336 1746503 := bstep (se 1 (by rfl) ⟨1309877, by rfl⟩ : syracuseStep 1746503 = 2619755) B2619755
theorem B1746683 : Blo 774336 1746683 := bstep (se 1 (by rfl) ⟨1310012, by rfl⟩ : syracuseStep 1746683 = 2620025) B2620025
theorem B1746971 : Blo 774336 1746971 := bstep (se 1 (by rfl) ⟨1310228, by rfl⟩ : syracuseStep 1746971 = 2620457) B2620457
theorem B4204649 : Blo 774336 4204649 := bstep (se 2 (by rfl) ⟨1576743, by rfl⟩ : syracuseStep 4204649 = 3153487) B3153487
theorem B25143803 : Blo 774336 25143803 := bstep (se 1 (by rfl) ⟨18857852, by rfl⟩ : syracuseStep 25143803 = 37715705) B37715705
theorem B5319431 : Blo 774336 5319431 := bstep (se 1 (by rfl) ⟨3989573, by rfl⟩ : syracuseStep 5319431 = 7979147) B7979147
theorem B1748447 : Blo 774336 1748447 := bstep (se 1 (by rfl) ⟨1311335, by rfl⟩ : syracuseStep 1748447 = 2622671) B2622671
theorem B1748663 : Blo 774336 1748663 := bstep (se 1 (by rfl) ⟨1311497, by rfl⟩ : syracuseStep 1748663 = 2622995) B2622995
theorem B107720603 : Blo 774336 107720603 := bstep (se 1 (by rfl) ⟨80790452, by rfl⟩ : syracuseStep 107720603 = 161580905) B161580905
theorem B14954705 : Blo 774336 14954705 := bstep (se 2 (by rfl) ⟨5608014, by rfl⟩ : syracuseStep 14954705 = 11216029) B11216029
theorem B1749455 : Blo 774336 1749455 := bstep (se 1 (by rfl) ⟨1312091, by rfl⟩ : syracuseStep 1749455 = 2624183) B2624183
theorem B31928903 : Blo 774336 31928903 := bstep (se 1 (by rfl) ⟨23946677, by rfl⟩ : syracuseStep 31928903 = 47893355) B47893355
theorem B1750121 : Blo 774336 1750121 := bstep (se 2 (by rfl) ⟨656295, by rfl⟩ : syracuseStep 1750121 = 1312591) B1312591
theorem B931483 : Blo 774336 931483 := bstep (se 1 (by rfl) ⟨698612, by rfl⟩ : syracuseStep 931483 = 1397225) B1397225
theorem B1750751 : Blo 774336 1750751 := bstep (se 1 (by rfl) ⟨1313063, by rfl⟩ : syracuseStep 1750751 = 2626127) B2626127
theorem B22427549 : Blo 774336 22427549 := bstep (se 3 (by rfl) ⟨4205165, by rfl⟩ : syracuseStep 22427549 = 8410331) B8410331
theorem B1751111 : Blo 774336 1751111 := bstep (se 1 (by rfl) ⟨1313333, by rfl⟩ : syracuseStep 1751111 = 2626667) B2626667
theorem B1161671 : Blo 774336 1161671 := bstep (se 1 (by rfl) ⟨871253, by rfl⟩ : syracuseStep 1161671 = 1742507) B1742507
theorem B3324361 : Blo 774336 3324361 := bstep (se 2 (by rfl) ⟨1246635, by rfl⟩ : syracuseStep 3324361 = 2493271) B2493271
theorem B1161887 : Blo 774336 1161887 := bstep (se 1 (by rfl) ⟨871415, by rfl⟩ : syracuseStep 1161887 = 1742831) B1742831
theorem B1162031 : Blo 774336 1162031 := bstep (se 1 (by rfl) ⟨871523, by rfl⟩ : syracuseStep 1162031 = 1743047) B1743047
theorem B1162151 : Blo 774336 1162151 := bstep (se 1 (by rfl) ⟨871613, by rfl⟩ : syracuseStep 1162151 = 1743227) B1743227
theorem B1653851 : Blo 774336 1653851 := bstep (se 1 (by rfl) ⟨1240388, by rfl⟩ : syracuseStep 1653851 = 2480777) B2480777
theorem B1162331 : Blo 774336 1162331 := bstep (se 1 (by rfl) ⟨871748, by rfl⟩ : syracuseStep 1162331 = 1743497) B1743497
theorem B2210921 : Blo 774336 2210921 := bstep (se 2 (by rfl) ⟨829095, by rfl⟩ : syracuseStep 2210921 = 1658191) B1658191
theorem B3783827 : Blo 774336 3783827 := bstep (se 1 (by rfl) ⟨2837870, by rfl⟩ : syracuseStep 3783827 = 5675741) B5675741
theorem B2211047 : Blo 774336 2211047 := bstep (se 1 (by rfl) ⟨1658285, by rfl⟩ : syracuseStep 2211047 = 3316571) B3316571
theorem B5881085 : Blo 774336 5881085 := bstep (se 3 (by rfl) ⟨1102703, by rfl⟩ : syracuseStep 5881085 = 2205407) B2205407
theorem B7978409 : Blo 774336 7978409 := bstep (se 2 (by rfl) ⟨2991903, by rfl⟩ : syracuseStep 7978409 = 5983807) B5983807
theorem B1162703 : Blo 774336 1162703 := bstep (se 1 (by rfl) ⟨872027, by rfl⟩ : syracuseStep 1162703 = 1744055) B1744055
theorem B19906073 : Blo 774336 19906073 := bstep (se 2 (by rfl) ⟨7464777, by rfl⟩ : syracuseStep 19906073 = 14929555) B14929555
theorem B1163087 : Blo 774336 1163087 := bstep (se 1 (by rfl) ⟨872315, by rfl⟩ : syracuseStep 1163087 = 1744631) B1744631
theorem B10108759 : Blo 774336 10108759 := bstep (se 1 (by rfl) ⟨7581569, by rfl⟩ : syracuseStep 10108759 = 15163139) B15163139
theorem B2801513 : Blo 774336 2801513 := bstep (se 2 (by rfl) ⟨1050567, by rfl⟩ : syracuseStep 2801513 = 2101135) B2101135
theorem B10600321 : Blo 774336 10600321 := bstep (se 2 (by rfl) ⟨3975120, by rfl⟩ : syracuseStep 10600321 = 7950241) B7950241
theorem B1163207 : Blo 774336 1163207 := bstep (se 1 (by rfl) ⟨872405, by rfl⟩ : syracuseStep 1163207 = 1744811) B1744811
theorem B12599549 : Blo 774336 12599549 := bstep (se 3 (by rfl) ⟨2362415, by rfl⟩ : syracuseStep 12599549 = 4724831) B4724831
theorem B1163567 : Blo 774336 1163567 := bstep (se 1 (by rfl) ⟨872675, by rfl⟩ : syracuseStep 1163567 = 1745351) B1745351
theorem B1655167 : Blo 774336 1655167 := bstep (se 1 (by rfl) ⟨1241375, by rfl⟩ : syracuseStep 1655167 = 2482751) B2482751
theorem B18924029 : Blo 774336 18924029 := bstep (se 3 (by rfl) ⟨3548255, by rfl⟩ : syracuseStep 18924029 = 7096511) B7096511
theorem B1163807 : Blo 774336 1163807 := bstep (se 1 (by rfl) ⟨872855, by rfl⟩ : syracuseStep 1163807 = 1745711) B1745711
theorem B5882543 : Blo 774336 5882543 := bstep (se 1 (by rfl) ⟨4411907, by rfl⟩ : syracuseStep 5882543 = 8823815) B8823815
theorem B13288211 : Blo 774336 13288211 := bstep (se 1 (by rfl) ⟨9966158, by rfl⟩ : syracuseStep 13288211 = 19932317) B19932317
theorem B2868263 : Blo 774336 2868263 := bstep (se 1 (by rfl) ⟨2151197, by rfl⟩ : syracuseStep 2868263 = 4302395) B4302395
theorem B1164479 : Blo 774336 1164479 := bstep (se 1 (by rfl) ⟨873359, by rfl⟩ : syracuseStep 1164479 = 1746719) B1746719
theorem B1164623 : Blo 774336 1164623 := bstep (se 1 (by rfl) ⟨873467, by rfl⟩ : syracuseStep 1164623 = 1746935) B1746935
theorem B1164713 : Blo 774336 1164713 := bstep (se 2 (by rfl) ⟨436767, by rfl⟩ : syracuseStep 1164713 = 873535) B873535
theorem B1164863 : Blo 774336 1164863 := bstep (se 1 (by rfl) ⟨873647, by rfl⟩ : syracuseStep 1164863 = 1747295) B1747295
theorem B1164905 : Blo 774336 1164905 := bstep (se 2 (by rfl) ⟨436839, by rfl⟩ : syracuseStep 1164905 = 873679) B873679
theorem B32720525 : Blo 774336 32720525 := bstep (se 3 (by rfl) ⟨6135098, by rfl⟩ : syracuseStep 32720525 = 12270197) B12270197
theorem B1165343 : Blo 774336 1165343 := bstep (se 1 (by rfl) ⟨874007, by rfl⟩ : syracuseStep 1165343 = 1748015) B1748015
theorem B1165535 : Blo 774336 1165535 := bstep (se 1 (by rfl) ⟨874151, by rfl⟩ : syracuseStep 1165535 = 1748303) B1748303
theorem B1165595 : Blo 774336 1165595 := bstep (se 1 (by rfl) ⟨874196, by rfl⟩ : syracuseStep 1165595 = 1748393) B1748393
theorem B1657439 : Blo 774336 1657439 := bstep (se 1 (by rfl) ⟨1243079, by rfl⟩ : syracuseStep 1657439 = 2486159) B2486159
theorem B1165919 : Blo 774336 1165919 := bstep (se 1 (by rfl) ⟨874439, by rfl⟩ : syracuseStep 1165919 = 1748879) B1748879
theorem B1166201 : Blo 774336 1166201 := bstep (se 2 (by rfl) ⟨437325, by rfl⟩ : syracuseStep 1166201 = 874651) B874651
theorem B1395625 : Blo 774336 1395625 := bstep (se 2 (by rfl) ⟨523359, by rfl⟩ : syracuseStep 1395625 = 1046719) B1046719
theorem B1166249 : Blo 774336 1166249 := bstep (se 2 (by rfl) ⟨437343, by rfl⟩ : syracuseStep 1166249 = 874687) B874687
theorem B1166399 : Blo 774336 1166399 := bstep (se 1 (by rfl) ⟨874799, by rfl⟩ : syracuseStep 1166399 = 1749599) B1749599
theorem B871807 : Blo 774336 871807 := bstep (se 1 (by rfl) ⟨653855, by rfl⟩ : syracuseStep 871807 = 1307711) B1307711
theorem B6639185 : Blo 774336 6639185 := bstep (se 2 (by rfl) ⟨2489694, by rfl⟩ : syracuseStep 6639185 = 4979389) B4979389
theorem B1166951 : Blo 774336 1166951 := bstep (se 1 (by rfl) ⟨875213, by rfl⟩ : syracuseStep 1166951 = 1750427) B1750427
theorem B25546711 : Blo 774336 25546711 := bstep (se 1 (by rfl) ⟨19160033, by rfl⟩ : syracuseStep 25546711 = 38320067) B38320067
theorem B1167335 : Blo 774336 1167335 := bstep (se 1 (by rfl) ⟨875501, by rfl⟩ : syracuseStep 1167335 = 1751003) B1751003
theorem B1167455 : Blo 774336 1167455 := bstep (se 1 (by rfl) ⟨875591, by rfl⟩ : syracuseStep 1167455 = 1751183) B1751183
theorem B1167467 : Blo 774336 1167467 := bstep (se 1 (by rfl) ⟨875600, by rfl⟩ : syracuseStep 1167467 = 1751201) B1751201
theorem B1659079 : Blo 774336 1659079 := bstep (se 1 (by rfl) ⟨1244309, by rfl⟩ : syracuseStep 1659079 = 2488619) B2488619
theorem B774503 : Blo 774336 774503 := bstep (se 1 (by rfl) ⟨580877, by rfl⟩ : syracuseStep 774503 = 1161755) B1161755
theorem B774555 : Blo 774336 774555 := bstep (se 1 (by rfl) ⟨580916, by rfl⟩ : syracuseStep 774555 = 1161833) B1161833
theorem B3920399 : Blo 774336 3920399 := bstep (se 1 (by rfl) ⟨2940299, by rfl⟩ : syracuseStep 3920399 = 5880599) B5880599
theorem B14340797 : Blo 774336 14340797 := bstep (se 3 (by rfl) ⟨2688899, by rfl⟩ : syracuseStep 14340797 = 5377799) B5377799
theorem B774907 : Blo 774336 774907 := bstep (se 1 (by rfl) ⟨581180, by rfl⟩ : syracuseStep 774907 = 1162361) B1162361
theorem B873211 : Blo 774336 873211 := bstep (se 1 (by rfl) ⟨654908, by rfl⟩ : syracuseStep 873211 = 1309817) B1309817
theorem B774975 : Blo 774336 774975 := bstep (se 1 (by rfl) ⟨581231, by rfl⟩ : syracuseStep 774975 = 1162463) B1162463
theorem B775003 : Blo 774336 775003 := bstep (se 1 (by rfl) ⟨581252, by rfl⟩ : syracuseStep 775003 = 1162505) B1162505
theorem B775071 : Blo 774336 775071 := bstep (se 1 (by rfl) ⟨581303, by rfl⟩ : syracuseStep 775071 = 1162607) B1162607
theorem B775151 : Blo 774336 775151 := bstep (se 1 (by rfl) ⟨581363, by rfl⟩ : syracuseStep 775151 = 1162727) B1162727
theorem B775239 : Blo 774336 775239 := bstep (se 1 (by rfl) ⟨581429, by rfl⟩ : syracuseStep 775239 = 1162859) B1162859
theorem B1102943 : Blo 774336 1102943 := bstep (se 1 (by rfl) ⟨827207, by rfl⟩ : syracuseStep 1102943 = 1654415) B1654415
theorem B775323 : Blo 774336 775323 := bstep (se 1 (by rfl) ⟨581492, by rfl⟩ : syracuseStep 775323 = 1162985) B1162985
theorem B775419 : Blo 774336 775419 := bstep (se 1 (by rfl) ⟨581564, by rfl⟩ : syracuseStep 775419 = 1163129) B1163129
theorem B775487 : Blo 774336 775487 := bstep (se 1 (by rfl) ⟨581615, by rfl⟩ : syracuseStep 775487 = 1163231) B1163231
theorem B1660267 : Blo 774336 1660267 := bstep (se 1 (by rfl) ⟨1245200, by rfl⟩ : syracuseStep 1660267 = 2490401) B2490401
theorem B775655 : Blo 774336 775655 := bstep (se 1 (by rfl) ⟨581741, by rfl⟩ : syracuseStep 775655 = 1163483) B1163483
theorem B775663 : Blo 774336 775663 := bstep (se 1 (by rfl) ⟨581747, by rfl⟩ : syracuseStep 775663 = 1163495) B1163495
theorem B873967 : Blo 774336 873967 := bstep (se 1 (by rfl) ⟨655475, by rfl⟩ : syracuseStep 873967 = 1310951) B1310951
theorem B775771 : Blo 774336 775771 := bstep (se 1 (by rfl) ⟨581828, by rfl⟩ : syracuseStep 775771 = 1163657) B1163657
theorem B874075 : Blo 774336 874075 := bstep (se 1 (by rfl) ⟨655556, by rfl⟩ : syracuseStep 874075 = 1311113) B1311113
theorem B775835 : Blo 774336 775835 := bstep (se 1 (by rfl) ⟨581876, by rfl⟩ : syracuseStep 775835 = 1163753) B1163753
theorem B1660583 : Blo 774336 1660583 := bstep (se 1 (by rfl) ⟨1245437, by rfl⟩ : syracuseStep 1660583 = 2490875) B2490875
theorem B775919 : Blo 774336 775919 := bstep (se 1 (by rfl) ⟨581939, by rfl⟩ : syracuseStep 775919 = 1163879) B1163879
theorem B776007 : Blo 774336 776007 := bstep (se 1 (by rfl) ⟨582005, by rfl⟩ : syracuseStep 776007 = 1164011) B1164011
theorem B8836937 : Blo 774336 8836937 := bstep (se 2 (by rfl) ⟨3313851, by rfl⟩ : syracuseStep 8836937 = 6627703) B6627703
theorem B4413275 : Blo 774336 4413275 := bstep (se 1 (by rfl) ⟨3309956, by rfl⟩ : syracuseStep 4413275 = 6619913) B6619913
theorem B776027 : Blo 774336 776027 := bstep (se 1 (by rfl) ⟨582020, by rfl⟩ : syracuseStep 776027 = 1164041) B1164041
theorem B874363 : Blo 774336 874363 := bstep (se 1 (by rfl) ⟨655772, by rfl⟩ : syracuseStep 874363 = 1311545) B1311545
theorem B776095 : Blo 774336 776095 := bstep (se 1 (by rfl) ⟨582071, by rfl⟩ : syracuseStep 776095 = 1164143) B1164143
theorem B874399 : Blo 774336 874399 := bstep (se 1 (by rfl) ⟨655799, by rfl⟩ : syracuseStep 874399 = 1311599) B1311599
theorem B4478939 : Blo 774336 4478939 := bstep (se 1 (by rfl) ⟨3359204, by rfl⟩ : syracuseStep 4478939 = 6718409) B6718409
theorem B7952377 : Blo 774336 7952377 := bstep (se 2 (by rfl) ⟨2982141, by rfl⟩ : syracuseStep 7952377 = 5964283) B5964283
theorem B11360249 : Blo 774336 11360249 := bstep (se 2 (by rfl) ⟨4260093, by rfl⟩ : syracuseStep 11360249 = 8520187) B8520187
theorem B776263 : Blo 774336 776263 := bstep (se 1 (by rfl) ⟨582197, by rfl⟩ : syracuseStep 776263 = 1164395) B1164395
theorem B776423 : Blo 774336 776423 := bstep (se 1 (by rfl) ⟨582317, by rfl⟩ : syracuseStep 776423 = 1164635) B1164635
theorem B776607 : Blo 774336 776607 := bstep (se 1 (by rfl) ⟨582455, by rfl⟩ : syracuseStep 776607 = 1164911) B1164911
theorem B776655 : Blo 774336 776655 := bstep (se 1 (by rfl) ⟨582491, by rfl⟩ : syracuseStep 776655 = 1164983) B1164983
theorem B776679 : Blo 774336 776679 := bstep (se 1 (by rfl) ⟨582509, by rfl⟩ : syracuseStep 776679 = 1165019) B1165019
theorem B4250089 : Blo 774336 4250089 := bstep (se 2 (by rfl) ⟨1593783, by rfl⟩ : syracuseStep 4250089 = 3187567) B3187567
theorem B776795 : Blo 774336 776795 := bstep (se 1 (by rfl) ⟨582596, by rfl⟩ : syracuseStep 776795 = 1165193) B1165193
theorem B776863 : Blo 774336 776863 := bstep (se 1 (by rfl) ⟨582647, by rfl⟩ : syracuseStep 776863 = 1165295) B1165295
theorem B5593799 : Blo 774336 5593799 := bstep (se 1 (by rfl) ⟨4195349, by rfl⟩ : syracuseStep 5593799 = 8390699) B8390699
theorem B777031 : Blo 774336 777031 := bstep (se 1 (by rfl) ⟨582773, by rfl⟩ : syracuseStep 777031 = 1165547) B1165547
theorem B875335 : Blo 774336 875335 := bstep (se 1 (by rfl) ⟨656501, by rfl⟩ : syracuseStep 875335 = 1313003) B1313003
theorem B777071 : Blo 774336 777071 := bstep (se 1 (by rfl) ⟨582803, by rfl⟩ : syracuseStep 777071 = 1165607) B1165607
theorem B777127 : Blo 774336 777127 := bstep (se 1 (by rfl) ⟨582845, by rfl⟩ : syracuseStep 777127 = 1165691) B1165691
theorem B777307 : Blo 774336 777307 := bstep (se 1 (by rfl) ⟨582980, by rfl⟩ : syracuseStep 777307 = 1165961) B1165961
theorem B777423 : Blo 774336 777423 := bstep (se 1 (by rfl) ⟨583067, by rfl⟩ : syracuseStep 777423 = 1166135) B1166135
theorem B777447 : Blo 774336 777447 := bstep (se 1 (by rfl) ⟨583085, by rfl⟩ : syracuseStep 777447 = 1166171) B1166171
theorem B777543 : Blo 774336 777543 := bstep (se 1 (by rfl) ⟨583157, by rfl⟩ : syracuseStep 777543 = 1166315) B1166315
theorem B777679 : Blo 774336 777679 := bstep (se 1 (by rfl) ⟨583259, by rfl⟩ : syracuseStep 777679 = 1166519) B1166519
theorem B2940407 : Blo 774336 2940407 := bstep (se 1 (by rfl) ⟨2205305, by rfl⟩ : syracuseStep 2940407 = 4410611) B4410611
theorem B777839 : Blo 774336 777839 := bstep (se 1 (by rfl) ⟨583379, by rfl⟩ : syracuseStep 777839 = 1166759) B1166759
theorem B777895 : Blo 774336 777895 := bstep (se 1 (by rfl) ⟨583421, by rfl⟩ : syracuseStep 777895 = 1166843) B1166843
theorem B777959 : Blo 774336 777959 := bstep (se 1 (by rfl) ⟨583469, by rfl⟩ : syracuseStep 777959 = 1166939) B1166939
theorem B778015 : Blo 774336 778015 := bstep (se 1 (by rfl) ⟨583511, by rfl⟩ : syracuseStep 778015 = 1167023) B1167023
theorem B778095 : Blo 774336 778095 := bstep (se 1 (by rfl) ⟨583571, by rfl⟩ : syracuseStep 778095 = 1167143) B1167143
theorem B778151 : Blo 774336 778151 := bstep (se 1 (by rfl) ⟨583613, by rfl⟩ : syracuseStep 778151 = 1167227) B1167227
theorem B8314807 : Blo 774336 8314807 := bstep (se 1 (by rfl) ⟨6236105, by rfl⟩ : syracuseStep 8314807 = 12472211) B12472211
theorem B37773317 : Blo 774336 37773317 := bstep (se 4 (by rfl) ⟨3541248, by rfl⟩ : syracuseStep 37773317 = 7082497) B7082497
theorem B28336139 : Blo 774336 28336139 := bstep (se 1 (by rfl) ⟨21252104, by rfl⟩ : syracuseStep 28336139 = 42504209) B42504209
theorem B5988419 : Blo 774336 5988419 := bstep (se 1 (by rfl) ⟨4491314, by rfl⟩ : syracuseStep 5988419 = 8982629) B8982629
theorem B4186397 : Blo 774336 4186397 := bstep (se 3 (by rfl) ⟨784949, by rfl⟩ : syracuseStep 4186397 = 1569899) B1569899
theorem B4481573 : Blo 774336 4481573 := bstep (se 4 (by rfl) ⟨420147, by rfl⟩ : syracuseStep 4481573 = 840295) B840295
theorem B8413793 : Blo 774336 8413793 := bstep (se 2 (by rfl) ⟨3155172, by rfl⟩ : syracuseStep 8413793 = 6310345) B6310345
theorem B1861679 : Blo 774336 1861679 := bstep (se 1 (by rfl) ⟨1396259, by rfl⟩ : syracuseStep 1861679 = 2792519) B2792519
theorem B1861775 : Blo 774336 1861775 := bstep (se 1 (by rfl) ⟨1396331, by rfl⟩ : syracuseStep 1861775 = 2792663) B2792663
theorem B2943323 : Blo 774336 2943323 := bstep (se 1 (by rfl) ⟨2207492, by rfl⟩ : syracuseStep 2943323 = 4414985) B4414985
theorem B2943641 : Blo 774336 2943641 := bstep (se 2 (by rfl) ⟨1103865, by rfl⟩ : syracuseStep 2943641 = 2207731) B2207731
theorem B2943823 : Blo 774336 2943823 := bstep (se 1 (by rfl) ⟨2207867, by rfl⟩ : syracuseStep 2943823 = 4415735) B4415735
theorem B12610961 : Blo 774336 12610961 := bstep (se 2 (by rfl) ⟨4729110, by rfl⟩ : syracuseStep 12610961 = 9458221) B9458221
theorem B2944583 : Blo 774336 2944583 := bstep (se 1 (by rfl) ⟨2208437, by rfl⟩ : syracuseStep 2944583 = 4416875) B4416875
theorem B4714075 : Blo 774336 4714075 := bstep (se 1 (by rfl) ⟨3535556, by rfl⟩ : syracuseStep 4714075 = 7071113) B7071113
theorem B1240895 : Blo 774336 1240895 := bstep (se 1 (by rfl) ⟨930671, by rfl⟩ : syracuseStep 1240895 = 1861343) B1861343
theorem B2617487 : Blo 774336 2617487 := bstep (se 1 (by rfl) ⟨1963115, by rfl⟩ : syracuseStep 2617487 = 3926231) B3926231
theorem B1470727 : Blo 774336 1470727 := bstep (se 1 (by rfl) ⟨1103045, by rfl⟩ : syracuseStep 1470727 = 2206091) B2206091
theorem B2617703 : Blo 774336 2617703 := bstep (se 1 (by rfl) ⟨1963277, by rfl⟩ : syracuseStep 2617703 = 3926555) B3926555
theorem B4715243 : Blo 774336 4715243 := bstep (se 1 (by rfl) ⟨3536432, by rfl⟩ : syracuseStep 4715243 = 7072865) B7072865
theorem B1962731 : Blo 774336 1962731 := bstep (se 1 (by rfl) ⟨1472048, by rfl⟩ : syracuseStep 1962731 = 2944097) B2944097
theorem B1307387 : Blo 774336 1307387 := bstep (se 1 (by rfl) ⟨980540, by rfl⟩ : syracuseStep 1307387 = 1961081) B1961081
theorem B7074695 : Blo 774336 7074695 := bstep (se 1 (by rfl) ⟨5306021, by rfl⟩ : syracuseStep 7074695 = 10612043) B10612043
theorem B8844227 : Blo 774336 8844227 := bstep (se 1 (by rfl) ⟨6633170, by rfl⟩ : syracuseStep 8844227 = 13266341) B13266341
theorem B2946041 : Blo 774336 2946041 := bstep (se 2 (by rfl) ⟨1104765, by rfl⟩ : syracuseStep 2946041 = 2209531) B2209531
theorem B980039 : Blo 774336 980039 := bstep (se 1 (by rfl) ⟨735029, by rfl⟩ : syracuseStep 980039 = 1470059) B1470059
theorem B1865033 : Blo 774336 1865033 := bstep (se 2 (by rfl) ⟨699387, by rfl⟩ : syracuseStep 1865033 = 1398775) B1398775
theorem B1242535 : Blo 774336 1242535 := bstep (se 1 (by rfl) ⟨931901, by rfl⟩ : syracuseStep 1242535 = 1863803) B1863803
theorem B14382517 : Blo 774336 14382517 := bstep (se 5 (by rfl) ⟨674180, by rfl⟩ : syracuseStep 14382517 = 1348361) B1348361
theorem B1308251 : Blo 774336 1308251 := bstep (se 1 (by rfl) ⟨981188, by rfl⟩ : syracuseStep 1308251 = 1962377) B1962377
theorem B2619215 : Blo 774336 2619215 := bstep (se 1 (by rfl) ⟨1964411, by rfl⟩ : syracuseStep 2619215 = 3928823) B3928823
theorem B1243207 : Blo 774336 1243207 := bstep (se 1 (by rfl) ⟨932405, by rfl⟩ : syracuseStep 1243207 = 1864811) B1864811
theorem B3307823 : Blo 774336 3307823 := bstep (se 1 (by rfl) ⟨2480867, by rfl⟩ : syracuseStep 3307823 = 4961735) B4961735
theorem B5896637 : Blo 774336 5896637 := bstep (se 3 (by rfl) ⟨1105619, by rfl⟩ : syracuseStep 5896637 = 2211239) B2211239
theorem B1309135 : Blo 774336 1309135 := bstep (se 1 (by rfl) ⟨981851, by rfl⟩ : syracuseStep 1309135 = 1963703) B1963703
theorem B1472975 : Blo 774336 1472975 := bstep (se 1 (by rfl) ⟨1104731, by rfl⟩ : syracuseStep 1472975 = 2209463) B2209463
theorem B2652763 : Blo 774336 2652763 := bstep (se 1 (by rfl) ⟨1989572, by rfl⟩ : syracuseStep 2652763 = 3979145) B3979145
theorem B4717291 : Blo 774336 4717291 := bstep (se 1 (by rfl) ⟨3537968, by rfl⟩ : syracuseStep 4717291 = 7075937) B7075937
theorem B1473491 : Blo 774336 1473491 := bstep (se 1 (by rfl) ⟨1105118, by rfl⟩ : syracuseStep 1473491 = 2210237) B2210237
theorem B1572065 : Blo 774336 1572065 := bstep (se 2 (by rfl) ⟨589524, by rfl⟩ : syracuseStep 1572065 = 1179049) B1179049
theorem B1473871 : Blo 774336 1473871 := bstep (se 1 (by rfl) ⟨1105403, by rfl⟩ : syracuseStep 1473871 = 2210807) B2210807
theorem B1572527 : Blo 774336 1572527 := bstep (se 1 (by rfl) ⟨1179395, by rfl⟩ : syracuseStep 1572527 = 2358791) B2358791
theorem B1310431 : Blo 774336 1310431 := bstep (se 1 (by rfl) ⟨982823, by rfl⟩ : syracuseStep 1310431 = 1965647) B1965647
theorem B2621159 : Blo 774336 2621159 := bstep (se 1 (by rfl) ⟨1965869, by rfl⟩ : syracuseStep 2621159 = 3931739) B3931739
theorem B7470929 : Blo 774336 7470929 := bstep (se 2 (by rfl) ⟨2801598, by rfl⟩ : syracuseStep 7470929 = 5603197) B5603197
theorem B2948987 : Blo 774336 2948987 := bstep (se 1 (by rfl) ⟨2211740, by rfl⟩ : syracuseStep 2948987 = 4423481) B4423481
theorem B12616019 : Blo 774336 12616019 := bstep (se 1 (by rfl) ⟨9462014, by rfl⟩ : syracuseStep 12616019 = 18924029) B18924029
theorem B23856029 : Blo 774336 23856029 := bstep (se 3 (by rfl) ⟨4473005, by rfl⟩ : syracuseStep 23856029 = 8946011) B8946011
theorem B2360495 : Blo 774336 2360495 := bstep (se 1 (by rfl) ⟨1770371, by rfl⟩ : syracuseStep 2360495 = 3540743) B3540743
theorem B3933521 : Blo 774336 3933521 := bstep (se 2 (by rfl) ⟨1475070, by rfl⟩ : syracuseStep 3933521 = 2950141) B2950141
theorem B5900039 : Blo 774336 5900039 := bstep (se 1 (by rfl) ⟨4425029, by rfl⟩ : syracuseStep 5900039 = 8850059) B8850059
theorem B2950931 : Blo 774336 2950931 := bstep (se 1 (by rfl) ⟨2213198, by rfl⟩ : syracuseStep 2950931 = 4426397) B4426397
theorem B7669559 : Blo 774336 7669559 := bstep (se 1 (by rfl) ⟨5752169, by rfl⟩ : syracuseStep 7669559 = 11504339) B11504339
theorem B2623481 : Blo 774336 2623481 := bstep (se 2 (by rfl) ⟨983805, by rfl⟩ : syracuseStep 2623481 = 1967611) B1967611
theorem B1313023 : Blo 774336 1313023 := bstep (se 1 (by rfl) ⟨984767, by rfl⟩ : syracuseStep 1313023 = 1969535) B1969535
theorem B4426123 : Blo 774336 4426123 := bstep (se 1 (by rfl) ⟨3319592, by rfl⟩ : syracuseStep 4426123 = 6639185) B6639185
theorem B3934817 : Blo 774336 3934817 := bstep (se 2 (by rfl) ⟨1475556, by rfl⟩ : syracuseStep 3934817 = 2951113) B2951113
theorem B2100097 : Blo 774336 2100097 := bstep (se 2 (by rfl) ⟨787536, by rfl⟩ : syracuseStep 2100097 = 1575073) B1575073
theorem B2624507 : Blo 774336 2624507 := bstep (se 1 (by rfl) ⟨1968380, by rfl⟩ : syracuseStep 2624507 = 3936761) B3936761
theorem B2362537 : Blo 774336 2362537 := bstep (se 2 (by rfl) ⟨885951, by rfl⟩ : syracuseStep 2362537 = 1771903) B1771903
theorem B3935465 : Blo 774336 3935465 := bstep (se 2 (by rfl) ⟨1475799, by rfl⟩ : syracuseStep 3935465 = 2951599) B2951599
theorem B8392339 : Blo 774336 8392339 := bstep (se 1 (by rfl) ⟨6294254, by rfl⟩ : syracuseStep 8392339 = 12588509) B12588509
theorem B2952875 : Blo 774336 2952875 := bstep (se 1 (by rfl) ⟨2214656, by rfl⟩ : syracuseStep 2952875 = 4429313) B4429313
theorem B2985959 : Blo 774336 2985959 := bstep (se 1 (by rfl) ⟨2239469, by rfl⟩ : syracuseStep 2985959 = 4478939) B4478939
theorem B7573499 : Blo 774336 7573499 := bstep (se 1 (by rfl) ⟨5680124, by rfl⟩ : syracuseStep 7573499 = 11360249) B11360249
theorem B1118443 : Blo 774336 1118443 := bstep (se 1 (by rfl) ⟨838832, by rfl⟩ : syracuseStep 1118443 = 1677665) B1677665
theorem B16192315 : Blo 774336 16192315 := bstep (se 1 (by rfl) ⟨12144236, by rfl⟩ : syracuseStep 16192315 = 24288473) B24288473
theorem B8852975 : Blo 774336 8852975 := bstep (se 1 (by rfl) ⟨6639731, by rfl⟩ : syracuseStep 8852975 = 13279463) B13279463
theorem B2790931 : Blo 774336 2790931 := bstep (se 1 (by rfl) ⟨2093198, by rfl⟩ : syracuseStep 2790931 = 4186397) B4186397
theorem B5609195 : Blo 774336 5609195 := bstep (se 1 (by rfl) ⟨4206896, by rfl⟩ : syracuseStep 5609195 = 8413793) B8413793
theorem B10622825 : Blo 774336 10622825 := bstep (se 2 (by rfl) ⟨3983559, by rfl⟩ : syracuseStep 10622825 = 7967119) B7967119
theorem B4986953 : Blo 774336 4986953 := bstep (se 2 (by rfl) ⟨1870107, by rfl⟩ : syracuseStep 4986953 = 3740215) B3740215
theorem B3939353 : Blo 774336 3939353 := bstep (se 2 (by rfl) ⟨1477257, by rfl⟩ : syracuseStep 3939353 = 2954515) B2954515
theorem B3546287 : Blo 774336 3546287 := bstep (se 1 (by rfl) ⟨2659715, by rfl⟩ : syracuseStep 3546287 = 5319431) B5319431
theorem B14916797 : Blo 774336 14916797 := bstep (se 3 (by rfl) ⟨2796899, by rfl⟩ : syracuseStep 14916797 = 5593799) B5593799
theorem B19176689 : Blo 774336 19176689 := bstep (se 2 (by rfl) ⟨7191258, by rfl⟩ : syracuseStep 19176689 = 14382517) B14382517
theorem B827263 : Blo 774336 827263 := bstep (se 1 (by rfl) ⟨620447, by rfl⟩ : syracuseStep 827263 = 1240895) B1240895
theorem B1744991 : Blo 774336 1744991 := bstep (se 1 (by rfl) ⟨1308743, by rfl⟩ : syracuseStep 1744991 = 2617487) B2617487
theorem B9969803 : Blo 774336 9969803 := bstep (se 1 (by rfl) ⟨7477352, by rfl⟩ : syracuseStep 9969803 = 14954705) B14954705
theorem B1745135 : Blo 774336 1745135 := bstep (se 1 (by rfl) ⟨1308851, by rfl⟩ : syracuseStep 1745135 = 2617703) B2617703
theorem B4432481 : Blo 774336 4432481 := bstep (se 2 (by rfl) ⟨1662180, by rfl⟩ : syracuseStep 4432481 = 3324361) B3324361
theorem B1745513 : Blo 774336 1745513 := bstep (se 2 (by rfl) ⟨654567, by rfl⟩ : syracuseStep 1745513 = 1309135) B1309135
theorem B1746143 : Blo 774336 1746143 := bstep (se 1 (by rfl) ⟨1309607, by rfl⟩ : syracuseStep 1746143 = 2619215) B2619215
theorem B14951699 : Blo 774336 14951699 := bstep (se 1 (by rfl) ⟨11213774, by rfl⟩ : syracuseStep 14951699 = 22427549) B22427549
theorem B3548681 : Blo 774336 3548681 := bstep (se 2 (by rfl) ⟨1330755, by rfl⟩ : syracuseStep 3548681 = 2661511) B2661511
theorem B2205215 : Blo 774336 2205215 := bstep (se 1 (by rfl) ⟨1653911, by rfl⟩ : syracuseStep 2205215 = 3307823) B3307823
theorem B5318939 : Blo 774336 5318939 := bstep (se 1 (by rfl) ⟨3989204, by rfl⟩ : syracuseStep 5318939 = 7978409) B7978409
theorem B1747241 : Blo 774336 1747241 := bstep (se 2 (by rfl) ⟨655215, by rfl⟩ : syracuseStep 1747241 = 1310431) B1310431
theorem B13478345 : Blo 774336 13478345 := bstep (se 2 (by rfl) ⟨5054379, by rfl⟩ : syracuseStep 13478345 = 10108759) B10108759
theorem B1747439 : Blo 774336 1747439 := bstep (se 1 (by rfl) ⟨1310579, by rfl⟩ : syracuseStep 1747439 = 2621159) B2621159
theorem B14133761 : Blo 774336 14133761 := bstep (se 2 (by rfl) ⟨5300160, by rfl⟩ : syracuseStep 14133761 = 10600321) B10600321
theorem B11086409 : Blo 774336 11086409 := bstep (se 2 (by rfl) ⟨4157403, by rfl⟩ : syracuseStep 11086409 = 8314807) B8314807
theorem B8399699 : Blo 774336 8399699 := bstep (se 1 (by rfl) ⟨6299774, by rfl⟩ : syracuseStep 8399699 = 12599549) B12599549
theorem B1747871 : Blo 774336 1747871 := bstep (se 1 (by rfl) ⟨1310903, by rfl⟩ : syracuseStep 1747871 = 2621807) B2621807
theorem B830407 : Blo 774336 830407 := bstep (se 1 (by rfl) ⟨622805, by rfl⟩ : syracuseStep 830407 = 1245611) B1245611
theorem B4205513 : Blo 774336 4205513 := bstep (se 2 (by rfl) ⟨1577067, by rfl⟩ : syracuseStep 4205513 = 3154135) B3154135
theorem B6630437 : Blo 774336 6630437 := bstep (se 4 (by rfl) ⟨621603, by rfl⟩ : syracuseStep 6630437 = 1243207) B1243207
theorem B2206889 : Blo 774336 2206889 := bstep (se 2 (by rfl) ⟨827583, by rfl⟩ : syracuseStep 2206889 = 1655167) B1655167
theorem B8858807 : Blo 774336 8858807 := bstep (se 1 (by rfl) ⟨6644105, by rfl⟩ : syracuseStep 8858807 = 13288211) B13288211
theorem B1912175 : Blo 774336 1912175 := bstep (se 1 (by rfl) ⟨1434131, by rfl⟩ : syracuseStep 1912175 = 2868263) B2868263
theorem B8826731 : Blo 774336 8826731 := bstep (se 1 (by rfl) ⟨6620048, by rfl⟩ : syracuseStep 8826731 = 13240097) B13240097
theorem B4731301 : Blo 774336 4731301 := bstep (se 4 (by rfl) ⟨443559, by rfl⟩ : syracuseStep 4731301 = 887119) B887119
theorem B1749815 : Blo 774336 1749815 := bstep (se 1 (by rfl) ⟨1312361, by rfl⟩ : syracuseStep 1749815 = 2624723) B2624723
theorem B1749995 : Blo 774336 1749995 := bstep (se 1 (by rfl) ⟨1312496, by rfl⟩ : syracuseStep 1749995 = 2624993) B2624993
theorem B20166043 : Blo 774336 20166043 := bstep (se 1 (by rfl) ⟨15124532, by rfl⟩ : syracuseStep 20166043 = 30249065) B30249065
theorem B1750607 : Blo 774336 1750607 := bstep (se 1 (by rfl) ⟨1312955, by rfl⟩ : syracuseStep 1750607 = 2625911) B2625911
theorem B1751147 : Blo 774336 1751147 := bstep (se 1 (by rfl) ⟨1313360, by rfl⟩ : syracuseStep 1751147 = 2626721) B2626721
theorem B9943195 : Blo 774336 9943195 := bstep (se 1 (by rfl) ⟨7457396, by rfl⟩ : syracuseStep 9943195 = 14914793) B14914793
theorem B235518167 : Blo 774336 235518167 := bstep (se 1 (by rfl) ⟨176638625, by rfl⟩ : syracuseStep 235518167 = 353277251) B353277251
theorem B1162175 : Blo 774336 1162175 := bstep (se 1 (by rfl) ⟨871631, by rfl⟩ : syracuseStep 1162175 = 1743263) B1743263
theorem B1162223 : Blo 774336 1162223 := bstep (se 1 (by rfl) ⟨871667, by rfl⟩ : syracuseStep 1162223 = 1743335) B1743335
theorem B1162409 : Blo 774336 1162409 := bstep (se 2 (by rfl) ⟨435903, by rfl⟩ : syracuseStep 1162409 = 871807) B871807
theorem B1162799 : Blo 774336 1162799 := bstep (se 1 (by rfl) ⟨872099, by rfl⟩ : syracuseStep 1162799 = 1744199) B1744199
theorem B1162823 : Blo 774336 1162823 := bstep (se 1 (by rfl) ⟨872117, by rfl⟩ : syracuseStep 1162823 = 1744235) B1744235
theorem B1162907 : Blo 774336 1162907 := bstep (se 1 (by rfl) ⟨872180, by rfl⟩ : syracuseStep 1162907 = 1744361) B1744361
theorem B1163003 : Blo 774336 1163003 := bstep (se 1 (by rfl) ⟨872252, by rfl⟩ : syracuseStep 1163003 = 1744505) B1744505
theorem B34062281 : Blo 774336 34062281 := bstep (se 2 (by rfl) ⟨12773355, by rfl⟩ : syracuseStep 34062281 = 25546711) B25546711
theorem B25182211 : Blo 774336 25182211 := bstep (se 1 (by rfl) ⟨18886658, by rfl⟩ : syracuseStep 25182211 = 37773317) B37773317
theorem B18890759 : Blo 774336 18890759 := bstep (se 1 (by rfl) ⟨14168069, by rfl⟩ : syracuseStep 18890759 = 28336139) B28336139
theorem B2211923 : Blo 774336 2211923 := bstep (se 1 (by rfl) ⟨1658942, by rfl⟩ : syracuseStep 2211923 = 3317885) B3317885
theorem B1163471 : Blo 774336 1163471 := bstep (se 1 (by rfl) ⟨872603, by rfl⟩ : syracuseStep 1163471 = 1745207) B1745207
theorem B2212105 : Blo 774336 2212105 := bstep (se 2 (by rfl) ⟨829539, by rfl⟩ : syracuseStep 2212105 = 1659079) B1659079
theorem B1164155 : Blo 774336 1164155 := bstep (se 1 (by rfl) ⟨873116, by rfl⟩ : syracuseStep 1164155 = 1746233) B1746233
theorem B1164281 : Blo 774336 1164281 := bstep (se 2 (by rfl) ⟨436605, by rfl⟩ : syracuseStep 1164281 = 873211) B873211
theorem B1164335 : Blo 774336 1164335 := bstep (se 1 (by rfl) ⟨873251, by rfl⟩ : syracuseStep 1164335 = 1746503) B1746503
theorem B1164455 : Blo 774336 1164455 := bstep (se 1 (by rfl) ⟨873341, by rfl⟩ : syracuseStep 1164455 = 1746683) B1746683
theorem B1164647 : Blo 774336 1164647 := bstep (se 1 (by rfl) ⟨873485, by rfl⟩ : syracuseStep 1164647 = 1746971) B1746971
theorem B2803099 : Blo 774336 2803099 := bstep (se 1 (by rfl) ⟨2102324, by rfl⟩ : syracuseStep 2803099 = 4204649) B4204649
theorem B16762535 : Blo 774336 16762535 := bstep (se 1 (by rfl) ⟨12571901, by rfl⟩ : syracuseStep 16762535 = 25143803) B25143803
theorem B2213689 : Blo 774336 2213689 := bstep (se 2 (by rfl) ⟨830133, by rfl⟩ : syracuseStep 2213689 = 1660267) B1660267
theorem B1656713 : Blo 774336 1656713 := bstep (se 2 (by rfl) ⟨621267, by rfl⟩ : syracuseStep 1656713 = 1242535) B1242535
theorem B1165289 : Blo 774336 1165289 := bstep (se 2 (by rfl) ⟨436983, by rfl⟩ : syracuseStep 1165289 = 873967) B873967
theorem B1165433 : Blo 774336 1165433 := bstep (se 2 (by rfl) ⟨437037, by rfl⟩ : syracuseStep 1165433 = 874075) B874075
theorem B8407307 : Blo 774336 8407307 := bstep (se 1 (by rfl) ⟨6305480, by rfl⟩ : syracuseStep 8407307 = 12610961) B12610961
theorem B1165631 : Blo 774336 1165631 := bstep (se 1 (by rfl) ⟨874223, by rfl⟩ : syracuseStep 1165631 = 1748447) B1748447
theorem B1165775 : Blo 774336 1165775 := bstep (se 1 (by rfl) ⟨874331, by rfl⟩ : syracuseStep 1165775 = 1748663) B1748663
theorem B1165817 : Blo 774336 1165817 := bstep (se 2 (by rfl) ⟨437181, by rfl⟩ : syracuseStep 1165817 = 874363) B874363
theorem B1165865 : Blo 774336 1165865 := bstep (se 2 (by rfl) ⟨437199, by rfl⟩ : syracuseStep 1165865 = 874399) B874399
theorem B71813735 : Blo 774336 71813735 := bstep (se 1 (by rfl) ⟨53860301, by rfl⟩ : syracuseStep 71813735 = 107720603) B107720603
theorem B10603169 : Blo 774336 10603169 := bstep (se 2 (by rfl) ⟨3976188, by rfl⟩ : syracuseStep 10603169 = 7952377) B7952377
theorem B1166303 : Blo 774336 1166303 := bstep (se 1 (by rfl) ⟨874727, by rfl⟩ : syracuseStep 1166303 = 1749455) B1749455
theorem B21285935 : Blo 774336 21285935 := bstep (se 1 (by rfl) ⟨15964451, by rfl⟩ : syracuseStep 21285935 = 31928903) B31928903
theorem B871591 : Blo 774336 871591 := bstep (se 1 (by rfl) ⟨653693, by rfl⟩ : syracuseStep 871591 = 1307387) B1307387
theorem B1166747 : Blo 774336 1166747 := bstep (se 1 (by rfl) ⟨875060, by rfl⟩ : syracuseStep 1166747 = 1750121) B1750121
theorem B4247113 : Blo 774336 4247113 := bstep (se 2 (by rfl) ⟨1592667, by rfl⟩ : syracuseStep 4247113 = 3185335) B3185335
theorem B872167 : Blo 774336 872167 := bstep (se 1 (by rfl) ⟨654125, by rfl⟩ : syracuseStep 872167 = 1308251) B1308251
theorem B1167113 : Blo 774336 1167113 := bstep (se 2 (by rfl) ⟨437667, by rfl⟩ : syracuseStep 1167113 = 875335) B875335
theorem B1167167 : Blo 774336 1167167 := bstep (se 1 (by rfl) ⟨875375, by rfl⟩ : syracuseStep 1167167 = 1750751) B1750751
theorem B1167407 : Blo 774336 1167407 := bstep (se 1 (by rfl) ⟨875555, by rfl⟩ : syracuseStep 1167407 = 1751111) B1751111
theorem B774447 : Blo 774336 774447 := bstep (se 1 (by rfl) ⟨580835, by rfl⟩ : syracuseStep 774447 = 1161671) B1161671
theorem B774591 : Blo 774336 774591 := bstep (se 1 (by rfl) ⟨580943, by rfl⟩ : syracuseStep 774591 = 1161887) B1161887
theorem B774687 : Blo 774336 774687 := bstep (se 1 (by rfl) ⟨581015, by rfl⟩ : syracuseStep 774687 = 1162031) B1162031
theorem B774767 : Blo 774336 774767 := bstep (se 1 (by rfl) ⟨581075, by rfl⟩ : syracuseStep 774767 = 1162151) B1162151
theorem B1102567 : Blo 774336 1102567 := bstep (se 1 (by rfl) ⟨826925, by rfl⟩ : syracuseStep 1102567 = 1653851) B1653851
theorem B774887 : Blo 774336 774887 := bstep (se 1 (by rfl) ⟨581165, by rfl⟩ : syracuseStep 774887 = 1162331) B1162331
theorem B3920723 : Blo 774336 3920723 := bstep (se 1 (by rfl) ⟨2940542, by rfl⟩ : syracuseStep 3920723 = 5881085) B5881085
theorem B775135 : Blo 774336 775135 := bstep (se 1 (by rfl) ⟨581351, by rfl⟩ : syracuseStep 775135 = 1162703) B1162703
theorem B775391 : Blo 774336 775391 := bstep (se 1 (by rfl) ⟨581543, by rfl⟩ : syracuseStep 775391 = 1163087) B1163087
theorem B775471 : Blo 774336 775471 := bstep (se 1 (by rfl) ⟨581603, by rfl⟩ : syracuseStep 775471 = 1163207) B1163207
theorem B3986945 : Blo 774336 3986945 := bstep (se 2 (by rfl) ⟨1495104, by rfl⟩ : syracuseStep 3986945 = 2990209) B2990209
theorem B775711 : Blo 774336 775711 := bstep (se 1 (by rfl) ⟨581783, by rfl⟩ : syracuseStep 775711 = 1163567) B1163567
theorem B775871 : Blo 774336 775871 := bstep (se 1 (by rfl) ⟨581903, by rfl⟩ : syracuseStep 775871 = 1163807) B1163807
theorem B3921695 : Blo 774336 3921695 := bstep (se 1 (by rfl) ⟨2941271, by rfl⟩ : syracuseStep 3921695 = 5882543) B5882543
theorem B776319 : Blo 774336 776319 := bstep (se 1 (by rfl) ⟨582239, by rfl⟩ : syracuseStep 776319 = 1164479) B1164479
theorem B776415 : Blo 774336 776415 := bstep (se 1 (by rfl) ⟨582311, by rfl⟩ : syracuseStep 776415 = 1164623) B1164623
theorem B776475 : Blo 774336 776475 := bstep (se 1 (by rfl) ⟨582356, by rfl⟩ : syracuseStep 776475 = 1164713) B1164713
theorem B776575 : Blo 774336 776575 := bstep (se 1 (by rfl) ⟨582431, by rfl⟩ : syracuseStep 776575 = 1164863) B1164863
theorem B776603 : Blo 774336 776603 := bstep (se 1 (by rfl) ⟨582452, by rfl⟩ : syracuseStep 776603 = 1164905) B1164905
theorem B21813683 : Blo 774336 21813683 := bstep (se 1 (by rfl) ⟨16360262, by rfl⟩ : syracuseStep 21813683 = 32720525) B32720525
theorem B4413959 : Blo 774336 4413959 := bstep (se 1 (by rfl) ⟨3310469, by rfl⟩ : syracuseStep 4413959 = 6620939) B6620939
theorem B776895 : Blo 774336 776895 := bstep (se 1 (by rfl) ⟨582671, by rfl⟩ : syracuseStep 776895 = 1165343) B1165343
theorem B777023 : Blo 774336 777023 := bstep (se 1 (by rfl) ⟨582767, by rfl⟩ : syracuseStep 777023 = 1165535) B1165535
theorem B777063 : Blo 774336 777063 := bstep (se 1 (by rfl) ⟨582797, by rfl⟩ : syracuseStep 777063 = 1165595) B1165595
theorem B1104959 : Blo 774336 1104959 := bstep (se 1 (by rfl) ⟨828719, by rfl⟩ : syracuseStep 1104959 = 1657439) B1657439
theorem B777279 : Blo 774336 777279 := bstep (se 1 (by rfl) ⟨582959, by rfl⟩ : syracuseStep 777279 = 1165919) B1165919
theorem B777467 : Blo 774336 777467 := bstep (se 1 (by rfl) ⟨583100, by rfl⟩ : syracuseStep 777467 = 1166201) B1166201
theorem B777499 : Blo 774336 777499 := bstep (se 1 (by rfl) ⟨583124, by rfl⟩ : syracuseStep 777499 = 1166249) B1166249
theorem B777599 : Blo 774336 777599 := bstep (se 1 (by rfl) ⟨583199, by rfl⟩ : syracuseStep 777599 = 1166399) B1166399
theorem B777967 : Blo 774336 777967 := bstep (se 1 (by rfl) ⟨583475, by rfl⟩ : syracuseStep 777967 = 1166951) B1166951
theorem B22667141 : Blo 774336 22667141 := bstep (se 4 (by rfl) ⟨2125044, by rfl⟩ : syracuseStep 22667141 = 4250089) B4250089
theorem B778223 : Blo 774336 778223 := bstep (se 1 (by rfl) ⟨583667, by rfl⟩ : syracuseStep 778223 = 1167335) B1167335
theorem B778303 : Blo 774336 778303 := bstep (se 1 (by rfl) ⟨583727, by rfl⟩ : syracuseStep 778303 = 1167455) B1167455
theorem B778311 : Blo 774336 778311 := bstep (se 1 (by rfl) ⟨583733, by rfl⟩ : syracuseStep 778311 = 1167467) B1167467
theorem B2613437 : Blo 774336 2613437 := bstep (se 3 (by rfl) ⟨490019, by rfl⟩ : syracuseStep 2613437 = 980039) B980039
theorem B2941181 : Blo 774336 2941181 := bstep (se 3 (by rfl) ⟨551471, by rfl⟩ : syracuseStep 2941181 = 1102943) B1102943
theorem B2613599 : Blo 774336 2613599 := bstep (se 1 (by rfl) ⟨1960199, by rfl⟩ : syracuseStep 2613599 = 3920399) B3920399
theorem B9560531 : Blo 774336 9560531 := bstep (se 1 (by rfl) ⟨7170398, by rfl⟩ : syracuseStep 9560531 = 14340797) B14340797
theorem B22373009 : Blo 774336 22373009 := bstep (se 2 (by rfl) ⟨8389878, by rfl⟩ : syracuseStep 22373009 = 16779757) B16779757
theorem B3925097 : Blo 774336 3925097 := bstep (se 2 (by rfl) ⟨1471911, by rfl⟩ : syracuseStep 3925097 = 2943823) B2943823
theorem B1107055 : Blo 774336 1107055 := bstep (se 1 (by rfl) ⟨830291, by rfl⟩ : syracuseStep 1107055 = 1660583) B1660583
theorem B5891291 : Blo 774336 5891291 := bstep (se 1 (by rfl) ⟨4418468, by rfl⟩ : syracuseStep 5891291 = 8836937) B8836937
theorem B1860833 : Blo 774336 1860833 := bstep (se 2 (by rfl) ⟨697812, by rfl⟩ : syracuseStep 1860833 = 1395625) B1395625
theorem B2942183 : Blo 774336 2942183 := bstep (se 1 (by rfl) ⟨2206637, by rfl⟩ : syracuseStep 2942183 = 4413275) B4413275
theorem B6285433 : Blo 774336 6285433 := bstep (se 2 (by rfl) ⟨2357037, by rfl⟩ : syracuseStep 6285433 = 4714075) B4714075
theorem B1960271 : Blo 774336 1960271 := bstep (se 1 (by rfl) ⟨1470203, by rfl⟩ : syracuseStep 1960271 = 2940407) B2940407
theorem B3992279 : Blo 774336 3992279 := bstep (se 1 (by rfl) ⟨2994209, by rfl⟩ : syracuseStep 3992279 = 5988419) B5988419
theorem B1960969 : Blo 774336 1960969 := bstep (se 2 (by rfl) ⟨735363, by rfl⟩ : syracuseStep 1960969 = 1470727) B1470727
theorem B47803445 : Blo 774336 47803445 := bstep (se 5 (by rfl) ⟨2240786, by rfl⟩ : syracuseStep 47803445 = 4481573) B4481573
theorem B1241119 : Blo 774336 1241119 := bstep (se 1 (by rfl) ⟨930839, by rfl⟩ : syracuseStep 1241119 = 1861679) B1861679
theorem B1241183 : Blo 774336 1241183 := bstep (se 1 (by rfl) ⟨930887, by rfl⟩ : syracuseStep 1241183 = 1861775) B1861775
theorem B1962215 : Blo 774336 1962215 := bstep (se 1 (by rfl) ⟨1471661, by rfl⟩ : syracuseStep 1962215 = 2943323) B2943323
theorem B1962427 : Blo 774336 1962427 := bstep (se 1 (by rfl) ⟨1471820, by rfl⟩ : syracuseStep 1962427 = 2943641) B2943641
theorem B1241977 : Blo 774336 1241977 := bstep (se 2 (by rfl) ⟨465741, by rfl⟩ : syracuseStep 1241977 = 931483) B931483
theorem B1963055 : Blo 774336 1963055 := bstep (se 1 (by rfl) ⟨1472291, by rfl⟩ : syracuseStep 1963055 = 2944583) B2944583
theorem B3929309 : Blo 774336 3929309 := bstep (se 3 (by rfl) ⟨736745, by rfl⟩ : syracuseStep 3929309 = 1473491) B1473491
theorem B3143495 : Blo 774336 3143495 := bstep (se 1 (by rfl) ⟨2357621, by rfl⟩ : syracuseStep 3143495 = 4715243) B4715243
theorem B1308487 : Blo 774336 1308487 := bstep (se 1 (by rfl) ⟨981365, by rfl⟩ : syracuseStep 1308487 = 1962731) B1962731
theorem B4716463 : Blo 774336 4716463 := bstep (se 1 (by rfl) ⟨3537347, by rfl⟩ : syracuseStep 4716463 = 7074695) B7074695
theorem B5896151 : Blo 774336 5896151 := bstep (se 1 (by rfl) ⟨4422113, by rfl⟩ : syracuseStep 5896151 = 8844227) B8844227
theorem B1964027 : Blo 774336 1964027 := bstep (se 1 (by rfl) ⟨1473020, by rfl⟩ : syracuseStep 1964027 = 2946041) B2946041
theorem B3537017 : Blo 774336 3537017 := bstep (se 2 (by rfl) ⟨1326381, by rfl⟩ : syracuseStep 3537017 = 2652763) B2652763
theorem B1243355 : Blo 774336 1243355 := bstep (se 1 (by rfl) ⟨932516, by rfl⟩ : syracuseStep 1243355 = 1865033) B1865033
theorem B6289721 : Blo 774336 6289721 := bstep (se 2 (by rfl) ⟨2358645, by rfl⟩ : syracuseStep 6289721 = 4717291) B4717291
theorem B3931091 : Blo 774336 3931091 := bstep (se 1 (by rfl) ⟨2948318, by rfl⟩ : syracuseStep 3931091 = 5896637) B5896637
theorem B981983 : Blo 774336 981983 := bstep (se 1 (by rfl) ⟨736487, by rfl⟩ : syracuseStep 981983 = 1472975) B1472975
theorem B1965161 : Blo 774336 1965161 := bstep (se 2 (by rfl) ⟨736935, by rfl⟩ : syracuseStep 1965161 = 1473871) B1473871
theorem B1473947 : Blo 774336 1473947 := bstep (se 1 (by rfl) ⟨1105460, by rfl⟩ : syracuseStep 1473947 = 2210921) B2210921
theorem B2522551 : Blo 774336 2522551 := bstep (se 1 (by rfl) ⟨1891913, by rfl⟩ : syracuseStep 2522551 = 3783827) B3783827
theorem B1048043 : Blo 774336 1048043 := bstep (se 1 (by rfl) ⟨786032, by rfl⟩ : syracuseStep 1048043 = 1572065) B1572065
theorem B1474031 : Blo 774336 1474031 := bstep (se 1 (by rfl) ⟨1105523, by rfl⟩ : syracuseStep 1474031 = 2211047) B2211047
theorem B7470701 : Blo 774336 7470701 := bstep (se 3 (by rfl) ⟨1400756, by rfl⟩ : syracuseStep 7470701 = 2801513) B2801513
theorem B13270715 : Blo 774336 13270715 := bstep (se 1 (by rfl) ⟨9953036, by rfl⟩ : syracuseStep 13270715 = 19906073) B19906073
theorem B1048351 : Blo 774336 1048351 := bstep (se 1 (by rfl) ⟨786263, by rfl⟩ : syracuseStep 1048351 = 1572527) B1572527
theorem B4980619 : Blo 774336 4980619 := bstep (se 1 (by rfl) ⟨3735464, by rfl⟩ : syracuseStep 4980619 = 7470929) B7470929
theorem B1965991 : Blo 774336 1965991 := bstep (se 1 (by rfl) ⟨1474493, by rfl⟩ : syracuseStep 1965991 = 2948987) B2948987
theorem B1474615 : Blo 774336 1474615 := bstep (se 1 (by rfl) ⟨1105961, by rfl⟩ : syracuseStep 1474615 = 2211923) B2211923
theorem B3309821 : Blo 774336 3309821 := bstep (se 3 (by rfl) ⟨620591, by rfl⟩ : syracuseStep 3309821 = 1241183) B1241183
theorem B2949473 : Blo 774336 2949473 := bstep (se 2 (by rfl) ⟨1106052, by rfl⟩ : syracuseStep 2949473 = 2212105) B2212105
theorem B1573663 : Blo 774336 1573663 := bstep (se 1 (by rfl) ⟨1180247, by rfl⟩ : syracuseStep 1573663 = 2360495) B2360495
theorem B2622347 : Blo 774336 2622347 := bstep (se 1 (by rfl) ⟨1966760, by rfl⟩ : syracuseStep 2622347 = 3933521) B3933521
theorem B11175023 : Blo 774336 11175023 := bstep (se 1 (by rfl) ⟨8381267, by rfl⟩ : syracuseStep 11175023 = 16762535) B16762535
theorem B3933359 : Blo 774336 3933359 := bstep (se 1 (by rfl) ⟨2950019, by rfl⟩ : syracuseStep 3933359 = 5900039) B5900039
theorem B1967287 : Blo 774336 1967287 := bstep (se 1 (by rfl) ⟨1475465, by rfl⟩ : syracuseStep 1967287 = 2950931) B2950931
theorem B5113039 : Blo 774336 5113039 := bstep (se 1 (by rfl) ⟨3834779, by rfl⟩ : syracuseStep 5113039 = 7669559) B7669559
theorem B25494749 : Blo 774336 25494749 := bstep (se 3 (by rfl) ⟨4780265, by rfl⟩ : syracuseStep 25494749 = 9560531) B9560531
theorem B1476073 : Blo 774336 1476073 := bstep (se 2 (by rfl) ⟨553527, by rfl⟩ : syracuseStep 1476073 = 1107055) B1107055
theorem B5604871 : Blo 774336 5604871 := bstep (se 1 (by rfl) ⟨4203653, by rfl⟩ : syracuseStep 5604871 = 8407307) B8407307
theorem B2623211 : Blo 774336 2623211 := bstep (se 1 (by rfl) ⟨1967408, by rfl⟩ : syracuseStep 2623211 = 3934817) B3934817
theorem B47875823 : Blo 774336 47875823 := bstep (se 1 (by rfl) ⟨35906867, by rfl⟩ : syracuseStep 47875823 = 71813735) B71813735
theorem B3737465 : Blo 774336 3737465 := bstep (se 2 (by rfl) ⟨1401549, by rfl⟩ : syracuseStep 3737465 = 2803099) B2803099
theorem B14190623 : Blo 774336 14190623 := bstep (se 1 (by rfl) ⟨10642967, by rfl⟩ : syracuseStep 14190623 = 21285935) B21285935
theorem B2623643 : Blo 774336 2623643 := bstep (se 1 (by rfl) ⟨1967732, by rfl⟩ : syracuseStep 2623643 = 3935465) B3935465
theorem B25233605 : Blo 774336 25233605 := bstep (se 4 (by rfl) ⟨2365650, by rfl⟩ : syracuseStep 25233605 = 4731301) B4731301
theorem B2951585 : Blo 774336 2951585 := bstep (se 2 (by rfl) ⟨1106844, by rfl⟩ : syracuseStep 2951585 = 2213689) B2213689
theorem B1968583 : Blo 774336 1968583 := bstep (se 1 (by rfl) ⟨1476437, by rfl⟩ : syracuseStep 1968583 = 2952875) B2952875
theorem B5048999 : Blo 774336 5048999 := bstep (se 1 (by rfl) ⟨3786749, by rfl⟩ : syracuseStep 5048999 = 7573499) B7573499
theorem B5901497 : Blo 774336 5901497 := bstep (se 2 (by rfl) ⟨2213061, by rfl⟩ : syracuseStep 5901497 = 4426123) B4426123
theorem B5901983 : Blo 774336 5901983 := bstep (se 1 (by rfl) ⟨4426487, by rfl⟩ : syracuseStep 5901983 = 8852975) B8852975
theorem B2657963 : Blo 774336 2657963 := bstep (se 1 (by rfl) ⟨1993472, by rfl⟩ : syracuseStep 2657963 = 3986945) B3986945
theorem B3739463 : Blo 774336 3739463 := bstep (se 1 (by rfl) ⟨2804597, by rfl⟩ : syracuseStep 3739463 = 5609195) B5609195
theorem B7081883 : Blo 774336 7081883 := bstep (se 1 (by rfl) ⟨5311412, by rfl⟩ : syracuseStep 7081883 = 10622825) B10622825
theorem B2626235 : Blo 774336 2626235 := bstep (se 1 (by rfl) ⟨1969676, by rfl⟩ : syracuseStep 2626235 = 3939353) B3939353
theorem B2364191 : Blo 774336 2364191 := bstep (se 1 (by rfl) ⟨1773143, by rfl⟩ : syracuseStep 2364191 = 3546287) B3546287
theorem B1742291 : Blo 774336 1742291 := bstep (se 1 (by rfl) ⟨1306718, by rfl⟩ : syracuseStep 1742291 = 2613437) B2613437
theorem B1742399 : Blo 774336 1742399 := bstep (se 1 (by rfl) ⟨1306799, by rfl⟩ : syracuseStep 1742399 = 2613599) B2613599
theorem B2954987 : Blo 774336 2954987 := bstep (se 1 (by rfl) ⟨2216240, by rfl⟩ : syracuseStep 2954987 = 4432481) B4432481
theorem B14915339 : Blo 774336 14915339 := bstep (se 1 (by rfl) ⟨11186504, by rfl⟩ : syracuseStep 14915339 = 22373009) B22373009
theorem B3315613 : Blo 774336 3315613 := bstep (se 3 (by rfl) ⟨621677, by rfl⟩ : syracuseStep 3315613 = 1243355) B1243355
theorem B9967799 : Blo 774336 9967799 := bstep (se 1 (by rfl) ⟨7475849, by rfl⟩ : syracuseStep 9967799 = 14951699) B14951699
theorem B2365787 : Blo 774336 2365787 := bstep (se 1 (by rfl) ⟨1774340, by rfl⟩ : syracuseStep 2365787 = 3548681) B3548681
theorem B58169821 : Blo 774336 58169821 := bstep (se 3 (by rfl) ⟨10906841, by rfl⟩ : syracuseStep 58169821 = 21813683) B21813683
theorem B3545959 : Blo 774336 3545959 := bstep (se 1 (by rfl) ⟨2659469, by rfl⟩ : syracuseStep 3545959 = 5318939) B5318939
theorem B8985563 : Blo 774336 8985563 := bstep (se 1 (by rfl) ⟨6739172, by rfl⟩ : syracuseStep 8985563 = 13478345) B13478345
theorem B5905871 : Blo 774336 5905871 := bstep (se 1 (by rfl) ⟨4429403, by rfl⟩ : syracuseStep 5905871 = 8858807) B8858807
theorem B1744649 : Blo 774336 1744649 := bstep (se 2 (by rfl) ⟨654243, by rfl⟩ : syracuseStep 1744649 = 1308487) B1308487
theorem B2794781 : Blo 774336 2794781 := bstep (se 3 (by rfl) ⟨524021, by rfl⟩ : syracuseStep 2794781 = 1048043) B1048043
theorem B12593839 : Blo 774336 12593839 := bstep (se 1 (by rfl) ⟨9445379, by rfl⟩ : syracuseStep 12593839 = 18890759) B18890759
theorem B15904019 : Blo 774336 15904019 := bstep (se 1 (by rfl) ⟨11928014, by rfl⟩ : syracuseStep 15904019 = 23856029) B23856029
theorem B1748987 : Blo 774336 1748987 := bstep (se 1 (by rfl) ⟨1311740, by rfl⟩ : syracuseStep 1748987 = 2623481) B2623481
theorem B1749671 : Blo 774336 1749671 := bstep (se 1 (by rfl) ⟨1312253, by rfl⟩ : syracuseStep 1749671 = 2624507) B2624507
theorem B1750697 : Blo 774336 1750697 := bstep (se 2 (by rfl) ⟨656511, by rfl⟩ : syracuseStep 1750697 = 1313023) B1313023
theorem B4962221 : Blo 774336 4962221 := bstep (se 3 (by rfl) ⟨930416, by rfl⟩ : syracuseStep 4962221 = 1860833) B1860833
theorem B3324635 : Blo 774336 3324635 := bstep (se 1 (by rfl) ⟨2493476, by rfl⟩ : syracuseStep 3324635 = 4986953) B4986953
theorem B1162121 : Blo 774336 1162121 := bstep (se 2 (by rfl) ⟨435795, by rfl⟩ : syracuseStep 1162121 = 871591) B871591
theorem B9944531 : Blo 774336 9944531 := bstep (se 1 (by rfl) ⟨7458398, by rfl⟩ : syracuseStep 9944531 = 14916797) B14916797
theorem B1162889 : Blo 774336 1162889 := bstep (se 2 (by rfl) ⟨436083, by rfl⟩ : syracuseStep 1162889 = 872167) B872167
theorem B1654825 : Blo 774336 1654825 := bstep (se 2 (by rfl) ⟨620559, by rfl⟩ : syracuseStep 1654825 = 1241119) B1241119
theorem B1163327 : Blo 774336 1163327 := bstep (se 1 (by rfl) ⟨872495, by rfl⟩ : syracuseStep 1163327 = 1744991) B1744991
theorem B1163423 : Blo 774336 1163423 := bstep (se 1 (by rfl) ⟨872567, by rfl⟩ : syracuseStep 1163423 = 1745135) B1745135
theorem B1491257 : Blo 774336 1491257 := bstep (se 2 (by rfl) ⟨559221, by rfl⟩ : syracuseStep 1491257 = 1118443) B1118443
theorem B1163675 : Blo 774336 1163675 := bstep (se 1 (by rfl) ⟨872756, by rfl⟩ : syracuseStep 1163675 = 1745513) B1745513
theorem B1164095 : Blo 774336 1164095 := bstep (se 1 (by rfl) ⟨873071, by rfl⟩ : syracuseStep 1164095 = 1746143) B1746143
theorem B12600197 : Blo 774336 12600197 := bstep (se 4 (by rfl) ⟨1181268, by rfl⟩ : syracuseStep 12600197 = 2362537) B2362537
theorem B1655969 : Blo 774336 1655969 := bstep (se 2 (by rfl) ⟨620988, by rfl⟩ : syracuseStep 1655969 = 1241977) B1241977
theorem B1164827 : Blo 774336 1164827 := bstep (se 1 (by rfl) ⟨873620, by rfl⟩ : syracuseStep 1164827 = 1747241) B1747241
theorem B1164959 : Blo 774336 1164959 := bstep (se 1 (by rfl) ⟨873719, by rfl⟩ : syracuseStep 1164959 = 1747439) B1747439
theorem B9422507 : Blo 774336 9422507 := bstep (se 1 (by rfl) ⟨7066880, by rfl⟩ : syracuseStep 9422507 = 14133761) B14133761
theorem B7390939 : Blo 774336 7390939 := bstep (se 1 (by rfl) ⟨5543204, by rfl⟩ : syracuseStep 7390939 = 11086409) B11086409
theorem B26888057 : Blo 774336 26888057 := bstep (se 2 (by rfl) ⟨10083021, by rfl⟩ : syracuseStep 26888057 = 20166043) B20166043
theorem B1165247 : Blo 774336 1165247 := bstep (se 1 (by rfl) ⟨873935, by rfl⟩ : syracuseStep 1165247 = 1747871) B1747871
theorem B2803675 : Blo 774336 2803675 := bstep (se 1 (by rfl) ⟨2102756, by rfl⟩ : syracuseStep 2803675 = 4205513) B4205513
theorem B3721241 : Blo 774336 3721241 := bstep (se 2 (by rfl) ⟨1395465, by rfl⟩ : syracuseStep 3721241 = 2790931) B2790931
theorem B31868963 : Blo 774336 31868963 := bstep (se 1 (by rfl) ⟨23901722, by rfl⟩ : syracuseStep 31868963 = 47803445) B47803445
theorem B5884487 : Blo 774336 5884487 := bstep (se 1 (by rfl) ⟨4413365, by rfl⟩ : syracuseStep 5884487 = 8826731) B8826731
theorem B13257593 : Blo 774336 13257593 := bstep (se 2 (by rfl) ⟨4971597, by rfl⟩ : syracuseStep 13257593 = 9943195) B9943195
theorem B1166543 : Blo 774336 1166543 := bstep (se 1 (by rfl) ⟨874907, by rfl⟩ : syracuseStep 1166543 = 1749815) B1749815
theorem B51137837 : Blo 774336 51137837 := bstep (se 3 (by rfl) ⟨9588344, by rfl⟩ : syracuseStep 51137837 = 19176689) B19176689
theorem B1166663 : Blo 774336 1166663 := bstep (se 1 (by rfl) ⟨874997, by rfl⟩ : syracuseStep 1166663 = 1749995) B1749995
theorem B1167071 : Blo 774336 1167071 := bstep (se 1 (by rfl) ⟨875303, by rfl⟩ : syracuseStep 1167071 = 1750607) B1750607
theorem B1167431 : Blo 774336 1167431 := bstep (se 1 (by rfl) ⟨875573, by rfl⟩ : syracuseStep 1167431 = 1751147) B1751147
theorem B157012111 : Blo 774336 157012111 := bstep (se 1 (by rfl) ⟨117759083, by rfl⟩ : syracuseStep 157012111 = 235518167) B235518167
theorem B3363401 : Blo 774336 3363401 := bstep (se 2 (by rfl) ⟨1261275, by rfl⟩ : syracuseStep 3363401 = 2522551) B2522551
theorem B774783 : Blo 774336 774783 := bstep (se 1 (by rfl) ⟨581087, by rfl⟩ : syracuseStep 774783 = 1162175) B1162175
theorem B774815 : Blo 774336 774815 := bstep (se 1 (by rfl) ⟨581111, by rfl⟩ : syracuseStep 774815 = 1162223) B1162223
theorem B4412069 : Blo 774336 4412069 := bstep (se 4 (by rfl) ⟨413631, by rfl⟩ : syracuseStep 4412069 = 827263) B827263
theorem B774939 : Blo 774336 774939 := bstep (se 1 (by rfl) ⟨581204, by rfl⟩ : syracuseStep 774939 = 1162409) B1162409
theorem B60445709 : Blo 774336 60445709 := bstep (se 3 (by rfl) ⟨11333570, by rfl⟩ : syracuseStep 60445709 = 22667141) B22667141
theorem B775199 : Blo 774336 775199 := bstep (se 1 (by rfl) ⟨581399, by rfl⟩ : syracuseStep 775199 = 1162799) B1162799
theorem B1397801 : Blo 774336 1397801 := bstep (se 2 (by rfl) ⟨524175, by rfl⟩ : syracuseStep 1397801 = 1048351) B1048351
theorem B775215 : Blo 774336 775215 := bstep (se 1 (by rfl) ⟨581411, by rfl⟩ : syracuseStep 775215 = 1162823) B1162823
theorem B775271 : Blo 774336 775271 := bstep (se 1 (by rfl) ⟨581453, by rfl⟩ : syracuseStep 775271 = 1162907) B1162907
theorem B775335 : Blo 774336 775335 := bstep (se 1 (by rfl) ⟨581501, by rfl⟩ : syracuseStep 775335 = 1163003) B1163003
theorem B6640825 : Blo 774336 6640825 := bstep (se 2 (by rfl) ⟨2490309, by rfl⟩ : syracuseStep 6640825 = 4980619) B4980619
theorem B33576281 : Blo 774336 33576281 := bstep (se 2 (by rfl) ⟨12591105, by rfl⟩ : syracuseStep 33576281 = 25182211) B25182211
theorem B775647 : Blo 774336 775647 := bstep (se 1 (by rfl) ⟨581735, by rfl⟩ : syracuseStep 775647 = 1163471) B1163471
theorem B8410679 : Blo 774336 8410679 := bstep (se 1 (by rfl) ⟨6308009, by rfl⟩ : syracuseStep 8410679 = 12616019) B12616019
theorem B776103 : Blo 774336 776103 := bstep (se 1 (by rfl) ⟨582077, by rfl⟩ : syracuseStep 776103 = 1164155) B1164155
theorem B776187 : Blo 774336 776187 := bstep (se 1 (by rfl) ⟨582140, by rfl⟩ : syracuseStep 776187 = 1164281) B1164281
theorem B776223 : Blo 774336 776223 := bstep (se 1 (by rfl) ⟨582167, by rfl⟩ : syracuseStep 776223 = 1164335) B1164335
theorem B776303 : Blo 774336 776303 := bstep (se 1 (by rfl) ⟨582227, by rfl⟩ : syracuseStep 776303 = 1164455) B1164455
theorem B776431 : Blo 774336 776431 := bstep (se 1 (by rfl) ⟨582323, by rfl⟩ : syracuseStep 776431 = 1164647) B1164647
theorem B776859 : Blo 774336 776859 := bstep (se 1 (by rfl) ⟨582644, by rfl⟩ : syracuseStep 776859 = 1165289) B1165289
theorem B776955 : Blo 774336 776955 := bstep (se 1 (by rfl) ⟨582716, by rfl⟩ : syracuseStep 776955 = 1165433) B1165433
theorem B777087 : Blo 774336 777087 := bstep (se 1 (by rfl) ⟨582815, by rfl⟩ : syracuseStep 777087 = 1165631) B1165631
theorem B777183 : Blo 774336 777183 := bstep (se 1 (by rfl) ⟨582887, by rfl⟩ : syracuseStep 777183 = 1165775) B1165775
theorem B777211 : Blo 774336 777211 := bstep (se 1 (by rfl) ⟨582908, by rfl⟩ : syracuseStep 777211 = 1165817) B1165817
theorem B777243 : Blo 774336 777243 := bstep (se 1 (by rfl) ⟨582932, by rfl⟩ : syracuseStep 777243 = 1165865) B1165865
theorem B7068779 : Blo 774336 7068779 := bstep (se 1 (by rfl) ⟨5301584, by rfl⟩ : syracuseStep 7068779 = 10603169) B10603169
theorem B777535 : Blo 774336 777535 := bstep (se 1 (by rfl) ⟨583151, by rfl⟩ : syracuseStep 777535 = 1166303) B1166303
theorem B777831 : Blo 774336 777831 := bstep (se 1 (by rfl) ⟨583373, by rfl⟩ : syracuseStep 777831 = 1166747) B1166747
theorem B778075 : Blo 774336 778075 := bstep (se 1 (by rfl) ⟨583556, by rfl⟩ : syracuseStep 778075 = 1167113) B1167113
theorem B778111 : Blo 774336 778111 := bstep (se 1 (by rfl) ⟨583583, by rfl⟩ : syracuseStep 778111 = 1167167) B1167167
theorem B1990639 : Blo 774336 1990639 := bstep (se 1 (by rfl) ⟨1492979, by rfl⟩ : syracuseStep 1990639 = 2985959) B2985959
theorem B778271 : Blo 774336 778271 := bstep (se 1 (by rfl) ⟨583703, by rfl⟩ : syracuseStep 778271 = 1167407) B1167407
theorem B8380577 : Blo 774336 8380577 := bstep (se 2 (by rfl) ⟨3142716, by rfl⟩ : syracuseStep 8380577 = 6285433) B6285433
theorem B2613815 : Blo 774336 2613815 := bstep (se 1 (by rfl) ⟨1960361, by rfl⟩ : syracuseStep 2613815 = 3920723) B3920723
theorem B2614463 : Blo 774336 2614463 := bstep (se 1 (by rfl) ⟨1960847, by rfl⟩ : syracuseStep 2614463 = 3921695) B3921695
theorem B1107209 : Blo 774336 1107209 := bstep (se 2 (by rfl) ⟨415203, by rfl⟩ : syracuseStep 1107209 = 830407) B830407
theorem B2614625 : Blo 774336 2614625 := bstep (se 2 (by rfl) ⟨980484, by rfl⟩ : syracuseStep 2614625 = 1960969) B1960969
theorem B2942639 : Blo 774336 2942639 := bstep (se 1 (by rfl) ⟨2206979, by rfl⟩ : syracuseStep 2942639 = 4413959) B4413959
theorem B11200517 : Blo 774336 11200517 := bstep (se 4 (by rfl) ⟨1050048, by rfl⟩ : syracuseStep 11200517 = 2100097) B2100097
theorem B5662817 : Blo 774336 5662817 := bstep (se 2 (by rfl) ⟨2123556, by rfl⟩ : syracuseStep 5662817 = 4247113) B4247113
theorem B8382653 : Blo 774336 8382653 := bstep (se 3 (by rfl) ⟨1571747, by rfl⟩ : syracuseStep 8382653 = 3143495) B3143495
theorem B4417901 : Blo 774336 4417901 := bstep (se 3 (by rfl) ⟨828356, by rfl⟩ : syracuseStep 4417901 = 1656713) B1656713
theorem B6646535 : Blo 774336 6646535 := bstep (se 1 (by rfl) ⟨4984901, by rfl⟩ : syracuseStep 6646535 = 9969803) B9969803
theorem B1960787 : Blo 774336 1960787 := bstep (se 1 (by rfl) ⟨1470590, by rfl⟩ : syracuseStep 1960787 = 2941181) B2941181
theorem B2616569 : Blo 774336 2616569 := bstep (se 2 (by rfl) ⟨981213, by rfl⟩ : syracuseStep 2616569 = 1962427) B1962427
theorem B2616731 : Blo 774336 2616731 := bstep (se 1 (by rfl) ⟨1962548, by rfl⟩ : syracuseStep 2616731 = 3925097) B3925097
theorem B3927527 : Blo 774336 3927527 := bstep (se 1 (by rfl) ⟨2945645, by rfl⟩ : syracuseStep 3927527 = 5891291) B5891291
theorem B1961455 : Blo 774336 1961455 := bstep (se 1 (by rfl) ⟨1471091, by rfl⟩ : syracuseStep 1961455 = 2942183) B2942183
theorem B1470089 : Blo 774336 1470089 := bstep (se 2 (by rfl) ⟨551283, by rfl⟩ : syracuseStep 1470089 = 1102567) B1102567
theorem B1470143 : Blo 774336 1470143 := bstep (se 1 (by rfl) ⟨1102607, by rfl⟩ : syracuseStep 1470143 = 2205215) B2205215
theorem B21589753 : Blo 774336 21589753 := bstep (se 2 (by rfl) ⟨8096157, by rfl⟩ : syracuseStep 21589753 = 16192315) B16192315
theorem B1306847 : Blo 774336 1306847 := bstep (se 1 (by rfl) ⟨980135, by rfl⟩ : syracuseStep 1306847 = 1960271) B1960271
theorem B5599799 : Blo 774336 5599799 := bstep (se 1 (by rfl) ⟨4199849, by rfl⟩ : syracuseStep 5599799 = 8399699) B8399699
theorem B10646077 : Blo 774336 10646077 := bstep (se 3 (by rfl) ⟨1996139, by rfl⟩ : syracuseStep 10646077 = 3992279) B3992279
theorem B4420291 : Blo 774336 4420291 := bstep (se 1 (by rfl) ⟨3315218, by rfl⟩ : syracuseStep 4420291 = 6630437) B6630437
theorem B1471259 : Blo 774336 1471259 := bstep (se 1 (by rfl) ⟨1103444, by rfl⟩ : syracuseStep 1471259 = 2206889) B2206889
theorem B1274783 : Blo 774336 1274783 := bstep (se 1 (by rfl) ⟨956087, by rfl⟩ : syracuseStep 1274783 = 1912175) B1912175
theorem B6288617 : Blo 774336 6288617 := bstep (se 2 (by rfl) ⟨2358231, by rfl⟩ : syracuseStep 6288617 = 4716463) B4716463
theorem B2618621 : Blo 774336 2618621 := bstep (se 3 (by rfl) ⟨490991, by rfl⟩ : syracuseStep 2618621 = 981983) B981983
theorem B1308143 : Blo 774336 1308143 := bstep (se 1 (by rfl) ⟨981107, by rfl⟩ : syracuseStep 1308143 = 1962215) B1962215
theorem B2946557 : Blo 774336 2946557 := bstep (se 3 (by rfl) ⟨552479, by rfl⟩ : syracuseStep 2946557 = 1104959) B1104959
theorem B1308703 : Blo 774336 1308703 := bstep (se 1 (by rfl) ⟨981527, by rfl⟩ : syracuseStep 1308703 = 1963055) B1963055
theorem B44759141 : Blo 774336 44759141 := bstep (se 4 (by rfl) ⟨4196169, by rfl⟩ : syracuseStep 44759141 = 8392339) B8392339
theorem B2619539 : Blo 774336 2619539 := bstep (se 1 (by rfl) ⟨1964654, by rfl⟩ : syracuseStep 2619539 = 3929309) B3929309
theorem B3930767 : Blo 774336 3930767 := bstep (se 1 (by rfl) ⟨2948075, by rfl⟩ : syracuseStep 3930767 = 5896151) B5896151
theorem B1309351 : Blo 774336 1309351 := bstep (se 1 (by rfl) ⟨982013, by rfl⟩ : syracuseStep 1309351 = 1964027) B1964027
theorem B2358011 : Blo 774336 2358011 := bstep (se 1 (by rfl) ⟨1768508, by rfl⟩ : syracuseStep 2358011 = 3537017) B3537017
theorem B4193147 : Blo 774336 4193147 := bstep (se 1 (by rfl) ⟨3144860, by rfl⟩ : syracuseStep 4193147 = 6289721) B6289721
theorem B2620727 : Blo 774336 2620727 := bstep (se 1 (by rfl) ⟨1965545, by rfl⟩ : syracuseStep 2620727 = 3931091) B3931091
theorem B1310107 : Blo 774336 1310107 := bstep (se 1 (by rfl) ⟨982580, by rfl⟩ : syracuseStep 1310107 = 1965161) B1965161
theorem B982631 : Blo 774336 982631 := bstep (se 1 (by rfl) ⟨736973, by rfl⟩ : syracuseStep 982631 = 1473947) B1473947
theorem B982687 : Blo 774336 982687 := bstep (se 1 (by rfl) ⟨737015, by rfl⟩ : syracuseStep 982687 = 1474031) B1474031
theorem B4980467 : Blo 774336 4980467 := bstep (se 1 (by rfl) ⟨3735350, by rfl⟩ : syracuseStep 4980467 = 7470701) B7470701
theorem B8847143 : Blo 774336 8847143 := bstep (se 1 (by rfl) ⟨6635357, by rfl⟩ : syracuseStep 8847143 = 13270715) B13270715
theorem B2621321 : Blo 774336 2621321 := bstep (se 2 (by rfl) ⟨982995, by rfl⟩ : syracuseStep 2621321 = 1965991) B1965991
theorem B22708187 : Blo 774336 22708187 := bstep (se 1 (by rfl) ⟨17031140, by rfl⟩ : syracuseStep 22708187 = 34062281) B34062281
theorem B1966153 : Blo 774336 1966153 := bstep (se 2 (by rfl) ⟨737307, by rfl⟩ : syracuseStep 1966153 = 1474615) B1474615
theorem B1966315 : Blo 774336 1966315 := bstep (se 1 (by rfl) ⟨1474736, by rfl⟩ : syracuseStep 1966315 = 2949473) B2949473
theorem B2622239 : Blo 774336 2622239 := bstep (se 1 (by rfl) ⟨1966679, by rfl⟩ : syracuseStep 2622239 = 3933359) B3933359
theorem B2098217 : Blo 774336 2098217 := bstep (se 2 (by rfl) ⟨786831, by rfl⟩ : syracuseStep 2098217 = 1573663) B1573663
theorem B31917215 : Blo 774336 31917215 := bstep (se 1 (by rfl) ⟨23937911, by rfl⟩ : syracuseStep 31917215 = 47875823) B47875823
theorem B17925371 : Blo 774336 17925371 := bstep (se 1 (by rfl) ⟨13444028, by rfl⟩ : syracuseStep 17925371 = 26888057) B26888057
theorem B2491643 : Blo 774336 2491643 := bstep (se 1 (by rfl) ⟨1868732, by rfl⟩ : syracuseStep 2491643 = 3737465) B3737465
theorem B2623049 : Blo 774336 2623049 := bstep (se 2 (by rfl) ⟨983643, by rfl⟩ : syracuseStep 2623049 = 1967287) B1967287
theorem B6817385 : Blo 774336 6817385 := bstep (se 2 (by rfl) ⟨2556519, by rfl⟩ : syracuseStep 6817385 = 5113039) B5113039
theorem B1967723 : Blo 774336 1967723 := bstep (se 1 (by rfl) ⟨1475792, by rfl⟩ : syracuseStep 1967723 = 2951585) B2951585
theorem B1968097 : Blo 774336 1968097 := bstep (se 2 (by rfl) ⟨738036, by rfl⟩ : syracuseStep 1968097 = 1476073) B1476073
theorem B7473161 : Blo 774336 7473161 := bstep (se 2 (by rfl) ⟨2802435, by rfl⟩ : syracuseStep 7473161 = 5604871) B5604871
theorem B3934331 : Blo 774336 3934331 := bstep (se 1 (by rfl) ⟨2950748, by rfl⟩ : syracuseStep 3934331 = 5901497) B5901497
theorem B3934655 : Blo 774336 3934655 := bstep (se 1 (by rfl) ⟨2950991, by rfl⟩ : syracuseStep 3934655 = 5901983) B5901983
theorem B1771975 : Blo 774336 1771975 := bstep (se 1 (by rfl) ⟨1328981, by rfl⟩ : syracuseStep 1771975 = 2657963) B2657963
theorem B2492975 : Blo 774336 2492975 := bstep (se 1 (by rfl) ⟨1869731, by rfl⟩ : syracuseStep 2492975 = 3739463) B3739463
theorem B4721255 : Blo 774336 4721255 := bstep (se 1 (by rfl) ⟨3540941, by rfl⟩ : syracuseStep 4721255 = 7081883) B7081883
theorem B3738233 : Blo 774336 3738233 := bstep (se 2 (by rfl) ⟨1401837, by rfl⟩ : syracuseStep 3738233 = 2803675) B2803675
theorem B1576127 : Blo 774336 1576127 := bstep (se 1 (by rfl) ⟨1182095, by rfl⟩ : syracuseStep 1576127 = 2364191) B2364191
theorem B2624777 : Blo 774336 2624777 := bstep (se 2 (by rfl) ⟨984291, by rfl⟩ : syracuseStep 2624777 = 1968583) B1968583
theorem B2952557 : Blo 774336 2952557 := bstep (se 3 (by rfl) ⟨553604, by rfl⟩ : syracuseStep 2952557 = 1107209) B1107209
theorem B22384187 : Blo 774336 22384187 := bstep (se 1 (by rfl) ⟨16788140, by rfl⟩ : syracuseStep 22384187 = 33576281) B33576281
theorem B5607119 : Blo 774336 5607119 := bstep (se 1 (by rfl) ⟨4205339, by rfl⟩ : syracuseStep 5607119 = 8410679) B8410679
theorem B1969991 : Blo 774336 1969991 := bstep (se 1 (by rfl) ⟨1477493, by rfl⟩ : syracuseStep 1969991 = 2954987) B2954987
theorem B3937247 : Blo 774336 3937247 := bstep (se 1 (by rfl) ⟨2952935, by rfl⟩ : syracuseStep 3937247 = 5905871) B5905871
theorem B1742543 : Blo 774336 1742543 := bstep (se 1 (by rfl) ⟨1306907, by rfl⟩ : syracuseStep 1742543 = 2613815) B2613815
theorem B14194769 : Blo 774336 14194769 := bstep (se 2 (by rfl) ⟨5323038, by rfl⟩ : syracuseStep 14194769 = 10646077) B10646077
theorem B1742975 : Blo 774336 1742975 := bstep (se 1 (by rfl) ⟨1307231, by rfl⟩ : syracuseStep 1742975 = 2614463) B2614463
theorem B1743083 : Blo 774336 1743083 := bstep (se 1 (by rfl) ⟨1307312, by rfl⟩ : syracuseStep 1743083 = 2614625) B2614625
theorem B3775211 : Blo 774336 3775211 := bstep (se 1 (by rfl) ⟨2831408, by rfl⟩ : syracuseStep 3775211 = 5662817) B5662817
theorem B8854433 : Blo 774336 8854433 := bstep (se 2 (by rfl) ⟨3320412, by rfl⟩ : syracuseStep 8854433 = 6640825) B6640825
theorem B4431023 : Blo 774336 4431023 := bstep (se 1 (by rfl) ⟨3323267, by rfl⟩ : syracuseStep 4431023 = 6646535) B6646535
theorem B1744379 : Blo 774336 1744379 := bstep (se 1 (by rfl) ⟨1308284, by rfl⟩ : syracuseStep 1744379 = 2616569) B2616569
theorem B1744487 : Blo 774336 1744487 := bstep (se 1 (by rfl) ⟨1308365, by rfl⟩ : syracuseStep 1744487 = 2616731) B2616731
theorem B1744937 : Blo 774336 1744937 := bstep (se 2 (by rfl) ⟨654351, by rfl⟩ : syracuseStep 1744937 = 1308703) B1308703
theorem B1745747 : Blo 774336 1745747 := bstep (se 1 (by rfl) ⟨1309310, by rfl⟩ : syracuseStep 1745747 = 2618621) B2618621
theorem B1745801 : Blo 774336 1745801 := bstep (se 2 (by rfl) ⟨654675, by rfl⟩ : syracuseStep 1745801 = 1309351) B1309351
theorem B4727945 : Blo 774336 4727945 := bstep (se 2 (by rfl) ⟨1772979, by rfl⟩ : syracuseStep 4727945 = 3545959) B3545959
theorem B1746359 : Blo 774336 1746359 := bstep (se 1 (by rfl) ⟨1309769, by rfl⟩ : syracuseStep 1746359 = 2619539) B2619539
theorem B1746809 : Blo 774336 1746809 := bstep (se 2 (by rfl) ⟨655053, by rfl⟩ : syracuseStep 1746809 = 1310107) B1310107
theorem B2795431 : Blo 774336 2795431 := bstep (se 1 (by rfl) ⟨2096573, by rfl⟩ : syracuseStep 2795431 = 4193147) B4193147
theorem B1747151 : Blo 774336 1747151 := bstep (se 1 (by rfl) ⟨1310363, by rfl⟩ : syracuseStep 1747151 = 2620727) B2620727
theorem B6629687 : Blo 774336 6629687 := bstep (se 1 (by rfl) ⟨4972265, by rfl⟩ : syracuseStep 6629687 = 9944531) B9944531
theorem B3320311 : Blo 774336 3320311 := bstep (se 1 (by rfl) ⟨2490233, by rfl⟩ : syracuseStep 3320311 = 4980467) B4980467
theorem B1747547 : Blo 774336 1747547 := bstep (se 1 (by rfl) ⟨1310660, by rfl⟩ : syracuseStep 1747547 = 2621321) B2621321
theorem B2206433 : Blo 774336 2206433 := bstep (se 2 (by rfl) ⟨827412, by rfl⟩ : syracuseStep 2206433 = 1654825) B1654825
theorem B2206547 : Blo 774336 2206547 := bstep (se 1 (by rfl) ⟨1654910, by rfl⟩ : syracuseStep 2206547 = 3309821) B3309821
theorem B8400131 : Blo 774336 8400131 := bstep (se 1 (by rfl) ⟨6300098, by rfl⟩ : syracuseStep 8400131 = 12600197) B12600197
theorem B1748231 : Blo 774336 1748231 := bstep (se 1 (by rfl) ⟨1311173, by rfl⟩ : syracuseStep 1748231 = 2622347) B2622347
theorem B837397925 : Blo 774336 837397925 := bstep (se 4 (by rfl) ⟨78506055, by rfl⟩ : syracuseStep 837397925 = 157012111) B157012111
theorem B3976685 : Blo 774336 3976685 := bstep (se 3 (by rfl) ⟨745628, by rfl⟩ : syracuseStep 3976685 = 1491257) B1491257
theorem B1748807 : Blo 774336 1748807 := bstep (se 1 (by rfl) ⟨1311605, by rfl⟩ : syracuseStep 1748807 = 2623211) B2623211
theorem B21245975 : Blo 774336 21245975 := bstep (se 1 (by rfl) ⟨15934481, by rfl⟩ : syracuseStep 21245975 = 31868963) B31868963
theorem B1749095 : Blo 774336 1749095 := bstep (se 1 (by rfl) ⟨1311821, by rfl⟩ : syracuseStep 1749095 = 2623643) B2623643
theorem B16822403 : Blo 774336 16822403 := bstep (se 1 (by rfl) ⟨12616802, by rfl⟩ : syracuseStep 16822403 = 25233605) B25233605
theorem B34091891 : Blo 774336 34091891 := bstep (se 1 (by rfl) ⟨25568918, by rfl⟩ : syracuseStep 34091891 = 51137837) B51137837
theorem B29800061 : Blo 774336 29800061 := bstep (se 3 (by rfl) ⟨5587511, by rfl⟩ : syracuseStep 29800061 = 11175023) B11175023
theorem B1750823 : Blo 774336 1750823 := bstep (se 1 (by rfl) ⟨1313117, by rfl⟩ : syracuseStep 1750823 = 2626235) B2626235
theorem B931867 : Blo 774336 931867 := bstep (se 1 (by rfl) ⟨698900, by rfl⟩ : syracuseStep 931867 = 1397801) B1397801
theorem B7452749 : Blo 774336 7452749 := bstep (se 3 (by rfl) ⟨1397390, by rfl⟩ : syracuseStep 7452749 = 2794781) B2794781
theorem B16791785 : Blo 774336 16791785 := bstep (se 2 (by rfl) ⟨6296919, by rfl⟩ : syracuseStep 16791785 = 12593839) B12593839
theorem B1161527 : Blo 774336 1161527 := bstep (se 1 (by rfl) ⟨871145, by rfl⟩ : syracuseStep 1161527 = 1742291) B1742291
theorem B1161599 : Blo 774336 1161599 := bstep (se 1 (by rfl) ⟨871199, by rfl⟩ : syracuseStep 1161599 = 1742399) B1742399
theorem B9943559 : Blo 774336 9943559 := bstep (se 1 (by rfl) ⟨7457669, by rfl⟩ : syracuseStep 9943559 = 14915339) B14915339
theorem B28786337 : Blo 774336 28786337 := bstep (se 2 (by rfl) ⟨10794876, by rfl⟩ : syracuseStep 28786337 = 21589753) B21589753
theorem B1163099 : Blo 774336 1163099 := bstep (se 1 (by rfl) ⟨872324, by rfl⟩ : syracuseStep 1163099 = 1744649) B1744649
theorem B5587051 : Blo 774336 5587051 := bstep (se 1 (by rfl) ⟨4190288, by rfl⟩ : syracuseStep 5587051 = 8380577) B8380577
theorem B6308765 : Blo 774336 6308765 := bstep (se 3 (by rfl) ⟨1182893, by rfl⟩ : syracuseStep 6308765 = 2365787) B2365787
theorem B5588435 : Blo 774336 5588435 := bstep (se 1 (by rfl) ⟨4191326, by rfl⟩ : syracuseStep 5588435 = 8382653) B8382653
theorem B10602679 : Blo 774336 10602679 := bstep (se 1 (by rfl) ⟨7952009, by rfl⟩ : syracuseStep 10602679 = 15904019) B15904019
theorem B1165991 : Blo 774336 1165991 := bstep (se 1 (by rfl) ⟨874493, by rfl⟩ : syracuseStep 1165991 = 1748987) B1748987
theorem B871231 : Blo 774336 871231 := bstep (se 1 (by rfl) ⟨653423, by rfl⟩ : syracuseStep 871231 = 1306847) B1306847
theorem B1166447 : Blo 774336 1166447 := bstep (se 1 (by rfl) ⟨874835, by rfl⟩ : syracuseStep 1166447 = 1749671) B1749671
theorem B872095 : Blo 774336 872095 := bstep (se 1 (by rfl) ⟨654071, by rfl⟩ : syracuseStep 872095 = 1308143) B1308143
theorem B1167131 : Blo 774336 1167131 := bstep (se 1 (by rfl) ⟨875348, by rfl⟩ : syracuseStep 1167131 = 1750697) B1750697
theorem B29839427 : Blo 774336 29839427 := bstep (se 1 (by rfl) ⟨22379570, by rfl⟩ : syracuseStep 29839427 = 44759141) B44759141
theorem B3920237 : Blo 774336 3920237 := bstep (se 3 (by rfl) ⟨735044, by rfl⟩ : syracuseStep 3920237 = 1470089) B1470089
theorem B2216423 : Blo 774336 2216423 := bstep (se 1 (by rfl) ⟨1662317, by rfl⟩ : syracuseStep 2216423 = 3324635) B3324635
theorem B774747 : Blo 774336 774747 := bstep (se 1 (by rfl) ⟨581060, by rfl⟩ : syracuseStep 774747 = 1162121) B1162121
theorem B775259 : Blo 774336 775259 := bstep (se 1 (by rfl) ⟨581444, by rfl⟩ : syracuseStep 775259 = 1162889) B1162889
theorem B775551 : Blo 774336 775551 := bstep (se 1 (by rfl) ⟨581663, by rfl⟩ : syracuseStep 775551 = 1163327) B1163327
theorem B775615 : Blo 774336 775615 := bstep (se 1 (by rfl) ⟨581711, by rfl⟩ : syracuseStep 775615 = 1163423) B1163423
theorem B775783 : Blo 774336 775783 := bstep (se 1 (by rfl) ⟨581837, by rfl⟩ : syracuseStep 775783 = 1163675) B1163675
theorem B776063 : Blo 774336 776063 := bstep (se 1 (by rfl) ⟨582047, by rfl⟩ : syracuseStep 776063 = 1164095) B1164095
theorem B16996499 : Blo 774336 16996499 := bstep (se 1 (by rfl) ⟨12747374, by rfl⟩ : syracuseStep 16996499 = 25494749) B25494749
theorem B776551 : Blo 774336 776551 := bstep (se 1 (by rfl) ⟨582413, by rfl⟩ : syracuseStep 776551 = 1164827) B1164827
theorem B776639 : Blo 774336 776639 := bstep (se 1 (by rfl) ⟨582479, by rfl⟩ : syracuseStep 776639 = 1164959) B1164959
theorem B776831 : Blo 774336 776831 := bstep (se 1 (by rfl) ⟨582623, by rfl⟩ : syracuseStep 776831 = 1165247) B1165247
theorem B9460415 : Blo 774336 9460415 := bstep (se 1 (by rfl) ⟨7095311, by rfl⟩ : syracuseStep 9460415 = 14190623) B14190623
theorem B8969069 : Blo 774336 8969069 := bstep (se 3 (by rfl) ⟨1681700, by rfl⟩ : syracuseStep 8969069 = 3363401) B3363401
theorem B3922991 : Blo 774336 3922991 := bstep (se 1 (by rfl) ⟨2942243, by rfl⟩ : syracuseStep 3922991 = 5884487) B5884487
theorem B3365999 : Blo 774336 3365999 := bstep (se 1 (by rfl) ⟨2524499, by rfl⟩ : syracuseStep 3365999 = 5048999) B5048999
theorem B8838395 : Blo 774336 8838395 := bstep (se 1 (by rfl) ⟨6628796, by rfl⟩ : syracuseStep 8838395 = 13257593) B13257593
theorem B777695 : Blo 774336 777695 := bstep (se 1 (by rfl) ⟨583271, by rfl⟩ : syracuseStep 777695 = 1166543) B1166543
theorem B777775 : Blo 774336 777775 := bstep (se 1 (by rfl) ⟨583331, by rfl⟩ : syracuseStep 777775 = 1166663) B1166663
theorem B9854585 : Blo 774336 9854585 := bstep (se 2 (by rfl) ⟨3695469, by rfl⟩ : syracuseStep 9854585 = 7390939) B7390939
theorem B3399421 : Blo 774336 3399421 := bstep (se 3 (by rfl) ⟨637391, by rfl⟩ : syracuseStep 3399421 = 1274783) B1274783
theorem B778047 : Blo 774336 778047 := bstep (se 1 (by rfl) ⟨583535, by rfl⟩ : syracuseStep 778047 = 1167071) B1167071
theorem B778287 : Blo 774336 778287 := bstep (se 1 (by rfl) ⟨583715, by rfl⟩ : syracuseStep 778287 = 1167431) B1167431
theorem B4415917 : Blo 774336 4415917 := bstep (se 3 (by rfl) ⟨827984, by rfl⟩ : syracuseStep 4415917 = 1655969) B1655969
theorem B2941379 : Blo 774336 2941379 := bstep (se 1 (by rfl) ⟨2206034, by rfl⟩ : syracuseStep 2941379 = 4412069) B4412069
theorem B40297139 : Blo 774336 40297139 := bstep (se 1 (by rfl) ⟨30222854, by rfl⟩ : syracuseStep 40297139 = 60445709) B60445709
theorem B6645199 : Blo 774336 6645199 := bstep (se 1 (by rfl) ⟨4983899, by rfl⟩ : syracuseStep 6645199 = 9967799) B9967799
theorem B25126685 : Blo 774336 25126685 := bstep (se 3 (by rfl) ⟨4711253, by rfl⟩ : syracuseStep 25126685 = 9422507) B9422507
theorem B5990375 : Blo 774336 5990375 := bstep (se 1 (by rfl) ⟨4492781, by rfl⟩ : syracuseStep 5990375 = 8985563) B8985563
theorem B2615273 : Blo 774336 2615273 := bstep (se 2 (by rfl) ⟨980727, by rfl⟩ : syracuseStep 2615273 = 1961455) B1961455
theorem B4712519 : Blo 774336 4712519 := bstep (se 1 (by rfl) ⟨3534389, by rfl⟩ : syracuseStep 4712519 = 7068779) B7068779
theorem B9923309 : Blo 774336 9923309 := bstep (se 3 (by rfl) ⟨1860620, by rfl⟩ : syracuseStep 9923309 = 3721241) B3721241
theorem B5893721 : Blo 774336 5893721 := bstep (se 2 (by rfl) ⟨2210145, by rfl⟩ : syracuseStep 5893721 = 4420291) B4420291
theorem B1961759 : Blo 774336 1961759 := bstep (se 1 (by rfl) ⟨1471319, by rfl⟩ : syracuseStep 1961759 = 2942639) B2942639
theorem B7467011 : Blo 774336 7467011 := bstep (se 1 (by rfl) ⟨5600258, by rfl⟩ : syracuseStep 7467011 = 11200517) B11200517
theorem B2945267 : Blo 774336 2945267 := bstep (se 1 (by rfl) ⟨2208950, by rfl⟩ : syracuseStep 2945267 = 4417901) B4417901
theorem B1307191 : Blo 774336 1307191 := bstep (se 1 (by rfl) ⟨980393, by rfl⟩ : syracuseStep 1307191 = 1960787) B1960787
theorem B6288029 : Blo 774336 6288029 := bstep (se 3 (by rfl) ⟨1179005, by rfl⟩ : syracuseStep 6288029 = 2358011) B2358011
theorem B2618351 : Blo 774336 2618351 := bstep (se 1 (by rfl) ⟨1963763, by rfl⟩ : syracuseStep 2618351 = 3927527) B3927527
theorem B980095 : Blo 774336 980095 := bstep (se 1 (by rfl) ⟨735071, by rfl⟩ : syracuseStep 980095 = 1470143) B1470143
theorem B4420817 : Blo 774336 4420817 := bstep (se 2 (by rfl) ⟨1657806, by rfl⟩ : syracuseStep 4420817 = 3315613) B3315613
theorem B3733199 : Blo 774336 3733199 := bstep (se 1 (by rfl) ⟨2799899, by rfl⟩ : syracuseStep 3733199 = 5599799) B5599799
theorem B980839 : Blo 774336 980839 := bstep (se 1 (by rfl) ⟨735629, by rfl⟩ : syracuseStep 980839 = 1471259) B1471259
theorem B77559761 : Blo 774336 77559761 := bstep (se 2 (by rfl) ⟨29084910, by rfl⟩ : syracuseStep 77559761 = 58169821) B58169821
theorem B4192411 : Blo 774336 4192411 := bstep (se 1 (by rfl) ⟨3144308, by rfl⟩ : syracuseStep 4192411 = 6288617) B6288617
theorem B1964371 : Blo 774336 1964371 := bstep (se 1 (by rfl) ⟨1473278, by rfl⟩ : syracuseStep 1964371 = 2946557) B2946557
theorem B3308147 : Blo 774336 3308147 := bstep (se 1 (by rfl) ⟨2481110, by rfl⟩ : syracuseStep 3308147 = 4962221) B4962221
theorem B2620349 : Blo 774336 2620349 := bstep (se 3 (by rfl) ⟨491315, by rfl⟩ : syracuseStep 2620349 = 982631) B982631
theorem B2620511 : Blo 774336 2620511 := bstep (se 1 (by rfl) ⟨1965383, by rfl⟩ : syracuseStep 2620511 = 3930767) B3930767
theorem B1310249 : Blo 774336 1310249 := bstep (se 2 (by rfl) ⟨491343, by rfl⟩ : syracuseStep 1310249 = 982687) B982687
theorem B5898095 : Blo 774336 5898095 := bstep (se 1 (by rfl) ⟨4423571, by rfl⟩ : syracuseStep 5898095 = 8847143) B8847143
theorem B10616741 : Blo 774336 10616741 := bstep (se 4 (by rfl) ⟨995319, by rfl⟩ : syracuseStep 10616741 = 1990639) B1990639
theorem B15138791 : Blo 774336 15138791 := bstep (se 1 (by rfl) ⟨11354093, by rfl⟩ : syracuseStep 15138791 = 22708187) B22708187
theorem B2621537 : Blo 774336 2621537 := bstep (se 2 (by rfl) ⟨983076, by rfl⟩ : syracuseStep 2621537 = 1966153) B1966153
theorem B2621753 : Blo 774336 2621753 := bstep (se 2 (by rfl) ⟨983157, by rfl⟩ : syracuseStep 2621753 = 1966315) B1966315
theorem B1311815 : Blo 774336 1311815 := bstep (se 1 (by rfl) ⟨983861, by rfl⟩ : syracuseStep 1311815 = 1967723) B1967723
theorem B4982107 : Blo 774336 4982107 := bstep (se 1 (by rfl) ⟨3736580, by rfl⟩ : syracuseStep 4982107 = 7473161) B7473161
theorem B2622887 : Blo 774336 2622887 := bstep (se 1 (by rfl) ⟨1967165, by rfl⟩ : syracuseStep 2622887 = 3934331) B3934331
theorem B2623103 : Blo 774336 2623103 := bstep (se 1 (by rfl) ⟨1967327, by rfl⟩ : syracuseStep 2623103 = 3934655) B3934655
theorem B3147503 : Blo 774336 3147503 := bstep (se 1 (by rfl) ⟨2360627, by rfl⟩ : syracuseStep 3147503 = 4721255) B4721255
theorem B2492155 : Blo 774336 2492155 := bstep (se 1 (by rfl) ⟨1869116, by rfl⟩ : syracuseStep 2492155 = 3738233) B3738233
theorem B1050751 : Blo 774336 1050751 := bstep (se 1 (by rfl) ⟨788063, by rfl⟩ : syracuseStep 1050751 = 1576127) B1576127
theorem B1968371 : Blo 774336 1968371 := bstep (se 1 (by rfl) ⟨1476278, by rfl⟩ : syracuseStep 1968371 = 2952557) B2952557
theorem B3738079 : Blo 774336 3738079 := bstep (se 1 (by rfl) ⟨2803559, by rfl⟩ : syracuseStep 3738079 = 5607119) B5607119
theorem B1313327 : Blo 774336 1313327 := bstep (se 1 (by rfl) ⟨984995, by rfl⟩ : syracuseStep 1313327 = 1969991) B1969991
theorem B2624129 : Blo 774336 2624129 := bstep (se 2 (by rfl) ⟨984048, by rfl⟩ : syracuseStep 2624129 = 1968097) B1968097
theorem B19892951 : Blo 774336 19892951 := bstep (se 1 (by rfl) ⟨14919713, by rfl⟩ : syracuseStep 19892951 = 29839427) B29839427
theorem B1477615 : Blo 774336 1477615 := bstep (se 1 (by rfl) ⟨1108211, by rfl⟩ : syracuseStep 1477615 = 2216423) B2216423
theorem B2624831 : Blo 774336 2624831 := bstep (se 1 (by rfl) ⟨1968623, by rfl⟩ : syracuseStep 2624831 = 3937247) B3937247
theorem B4427081 : Blo 774336 4427081 := bstep (se 2 (by rfl) ⟨1660155, by rfl⟩ : syracuseStep 4427081 = 3320311) B3320311
theorem B5902955 : Blo 774336 5902955 := bstep (se 1 (by rfl) ⟨4427216, by rfl⟩ : syracuseStep 5902955 = 8854433) B8854433
theorem B2954015 : Blo 774336 2954015 := bstep (se 1 (by rfl) ⟨2215511, by rfl⟩ : syracuseStep 2954015 = 4431023) B4431023
theorem B37852717 : Blo 774336 37852717 := bstep (se 3 (by rfl) ⟨7097384, by rfl⟩ : syracuseStep 37852717 = 14194769) B14194769
theorem B1742921 : Blo 774336 1742921 := bstep (se 2 (by rfl) ⟨653595, by rfl⟩ : syracuseStep 1742921 = 1307191) B1307191
theorem B3151963 : Blo 774336 3151963 := bstep (se 1 (by rfl) ⟨2363972, by rfl⟩ : syracuseStep 3151963 = 4727945) B4727945
theorem B16751123 : Blo 774336 16751123 := bstep (se 1 (by rfl) ⟨12563342, by rfl⟩ : syracuseStep 16751123 = 25126685) B25126685
theorem B1743515 : Blo 774336 1743515 := bstep (se 1 (by rfl) ⟨1307636, by rfl⟩ : syracuseStep 1743515 = 2615273) B2615273
theorem B14163983 : Blo 774336 14163983 := bstep (se 1 (by rfl) ⟨10622987, by rfl⟩ : syracuseStep 14163983 = 21245975) B21245975
theorem B11214935 : Blo 774336 11214935 := bstep (se 1 (by rfl) ⟨8411201, by rfl⟩ : syracuseStep 11214935 = 16822403) B16822403
theorem B1745567 : Blo 774336 1745567 := bstep (se 1 (by rfl) ⟨1309175, by rfl⟩ : syracuseStep 1745567 = 2618351) B2618351
theorem B19866707 : Blo 774336 19866707 := bstep (se 1 (by rfl) ⟨14900030, by rfl⟩ : syracuseStep 19866707 = 29800061) B29800061
theorem B6629039 : Blo 774336 6629039 := bstep (se 1 (by rfl) ⟨4971779, by rfl⟩ : syracuseStep 6629039 = 9943559) B9943559
theorem B2205431 : Blo 774336 2205431 := bstep (se 1 (by rfl) ⟨1654073, by rfl⟩ : syracuseStep 2205431 = 3308147) B3308147
theorem B1746899 : Blo 774336 1746899 := bstep (se 1 (by rfl) ⟨1310174, by rfl⟩ : syracuseStep 1746899 = 2620349) B2620349
theorem B1747007 : Blo 774336 1747007 := bstep (se 1 (by rfl) ⟨1310255, by rfl⟩ : syracuseStep 1747007 = 2620511) B2620511
theorem B4532561 : Blo 774336 4532561 := bstep (se 2 (by rfl) ⟨1699710, by rfl⟩ : syracuseStep 4532561 = 3399421) B3399421
theorem B7449401 : Blo 774336 7449401 := bstep (se 2 (by rfl) ⟨2793525, by rfl⟩ : syracuseStep 7449401 = 5587051) B5587051
theorem B1748159 : Blo 774336 1748159 := bstep (se 1 (by rfl) ⟨1311119, by rfl⟩ : syracuseStep 1748159 = 2622239) B2622239
theorem B4205843 : Blo 774336 4205843 := bstep (se 1 (by rfl) ⟨3154382, by rfl⟩ : syracuseStep 4205843 = 6308765) B6308765
theorem B21278143 : Blo 774336 21278143 := bstep (se 1 (by rfl) ⟨15958607, by rfl⟩ : syracuseStep 21278143 = 31917215) B31917215
theorem B1748699 : Blo 774336 1748699 := bstep (se 1 (by rfl) ⟨1311524, by rfl⟩ : syracuseStep 1748699 = 2623049) B2623049
theorem B8860265 : Blo 774336 8860265 := bstep (se 2 (by rfl) ⟨3322599, by rfl⟩ : syracuseStep 8860265 = 6645199) B6645199
theorem B1749851 : Blo 774336 1749851 := bstep (se 1 (by rfl) ⟨1312388, by rfl⟩ : syracuseStep 1749851 = 2624777) B2624777
theorem B9450533 : Blo 774336 9450533 := bstep (se 4 (by rfl) ⟨885987, by rfl⟩ : syracuseStep 9450533 = 1771975) B1771975
theorem B14922791 : Blo 774336 14922791 := bstep (se 1 (by rfl) ⟨11192093, by rfl⟩ : syracuseStep 14922791 = 22384187) B22384187
theorem B14136905 : Blo 774336 14136905 := bstep (se 2 (by rfl) ⟨5301339, by rfl⟩ : syracuseStep 14136905 = 10602679) B10602679
theorem B1161641 : Blo 774336 1161641 := bstep (se 2 (by rfl) ⟨435615, by rfl⟩ : syracuseStep 1161641 = 871231) B871231
theorem B1161695 : Blo 774336 1161695 := bstep (se 1 (by rfl) ⟨871271, by rfl⟩ : syracuseStep 1161695 = 1742543) B1742543
theorem B1161983 : Blo 774336 1161983 := bstep (se 1 (by rfl) ⟨871487, by rfl⟩ : syracuseStep 1161983 = 1742975) B1742975
theorem B1162055 : Blo 774336 1162055 := bstep (se 1 (by rfl) ⟨871541, by rfl⟩ : syracuseStep 1162055 = 1743083) B1743083
theorem B6306943 : Blo 774336 6306943 := bstep (se 1 (by rfl) ⟨4730207, by rfl⟩ : syracuseStep 6306943 = 9460415) B9460415
theorem B5979379 : Blo 774336 5979379 := bstep (se 1 (by rfl) ⟨4484534, by rfl⟩ : syracuseStep 5979379 = 8969069) B8969069
theorem B2243999 : Blo 774336 2243999 := bstep (se 1 (by rfl) ⟨1682999, by rfl⟩ : syracuseStep 2243999 = 3365999) B3365999
theorem B1162793 : Blo 774336 1162793 := bstep (se 2 (by rfl) ⟨436047, by rfl⟩ : syracuseStep 1162793 = 872095) B872095
theorem B1162919 : Blo 774336 1162919 := bstep (se 1 (by rfl) ⟨872189, by rfl⟩ : syracuseStep 1162919 = 1744379) B1744379
theorem B1162991 : Blo 774336 1162991 := bstep (se 1 (by rfl) ⟨872243, by rfl⟩ : syracuseStep 1162991 = 1744487) B1744487
theorem B6569723 : Blo 774336 6569723 := bstep (se 1 (by rfl) ⟨4927292, by rfl⟩ : syracuseStep 6569723 = 9854585) B9854585
theorem B1163291 : Blo 774336 1163291 := bstep (se 1 (by rfl) ⟨872468, by rfl⟩ : syracuseStep 1163291 = 1744937) B1744937
theorem B1163831 : Blo 774336 1163831 := bstep (se 1 (by rfl) ⟨872873, by rfl⟩ : syracuseStep 1163831 = 1745747) B1745747
theorem B1163867 : Blo 774336 1163867 := bstep (se 1 (by rfl) ⟨872900, by rfl⟩ : syracuseStep 1163867 = 1745801) B1745801
theorem B1164239 : Blo 774336 1164239 := bstep (se 1 (by rfl) ⟨873179, by rfl⟩ : syracuseStep 1164239 = 1746359) B1746359
theorem B1164539 : Blo 774336 1164539 := bstep (se 1 (by rfl) ⟨873404, by rfl⟩ : syracuseStep 1164539 = 1746809) B1746809
theorem B1164767 : Blo 774336 1164767 := bstep (se 1 (by rfl) ⟨873575, by rfl⟩ : syracuseStep 1164767 = 1747151) B1747151
theorem B1165031 : Blo 774336 1165031 := bstep (se 1 (by rfl) ⟨873773, by rfl⟩ : syracuseStep 1165031 = 1747547) B1747547
theorem B1165487 : Blo 774336 1165487 := bstep (se 1 (by rfl) ⟨874115, by rfl⟩ : syracuseStep 1165487 = 1748231) B1748231
theorem B1165871 : Blo 774336 1165871 := bstep (se 1 (by rfl) ⟨874403, by rfl⟩ : syracuseStep 1165871 = 1748807) B1748807
theorem B1166063 : Blo 774336 1166063 := bstep (se 1 (by rfl) ⟨874547, by rfl⟩ : syracuseStep 1166063 = 1749095) B1749095
theorem B5589881 : Blo 774336 5589881 := bstep (se 2 (by rfl) ⟨2096205, by rfl⟩ : syracuseStep 5589881 = 4192411) B4192411
theorem B22727927 : Blo 774336 22727927 := bstep (se 1 (by rfl) ⟨17045945, by rfl⟩ : syracuseStep 22727927 = 34091891) B34091891
theorem B1167215 : Blo 774336 1167215 := bstep (se 1 (by rfl) ⟨875411, by rfl⟩ : syracuseStep 1167215 = 1750823) B1750823
theorem B4968499 : Blo 774336 4968499 := bstep (se 1 (by rfl) ⟨3726374, by rfl⟩ : syracuseStep 4968499 = 7452749) B7452749
theorem B11194523 : Blo 774336 11194523 := bstep (se 1 (by rfl) ⟨8395892, by rfl⟩ : syracuseStep 11194523 = 16791785) B16791785
theorem B774351 : Blo 774336 774351 := bstep (se 1 (by rfl) ⟨580763, by rfl⟩ : syracuseStep 774351 = 1161527) B1161527
theorem B774399 : Blo 774336 774399 := bstep (se 1 (by rfl) ⟨580799, by rfl⟩ : syracuseStep 774399 = 1161599) B1161599
theorem B873499 : Blo 774336 873499 := bstep (se 1 (by rfl) ⟨655124, by rfl⟩ : syracuseStep 873499 = 1310249) B1310249
theorem B19190891 : Blo 774336 19190891 := bstep (se 1 (by rfl) ⟨14393168, by rfl⟩ : syracuseStep 19190891 = 28786337) B28786337
theorem B775399 : Blo 774336 775399 := bstep (se 1 (by rfl) ⟨581549, by rfl⟩ : syracuseStep 775399 = 1163099) B1163099
theorem B5887889 : Blo 774336 5887889 := bstep (se 2 (by rfl) ⟨2207958, by rfl⟩ : syracuseStep 5887889 = 4415917) B4415917
theorem B19879829 : Blo 774336 19879829 := bstep (se 6 (by rfl) ⟨465933, by rfl⟩ : syracuseStep 19879829 = 931867) B931867
theorem B1398811 : Blo 774336 1398811 := bstep (se 1 (by rfl) ⟨1049108, by rfl⟩ : syracuseStep 1398811 = 2098217) B2098217
theorem B11950247 : Blo 774336 11950247 := bstep (se 1 (by rfl) ⟨8962685, by rfl⟩ : syracuseStep 11950247 = 17925371) B17925371
theorem B1661095 : Blo 774336 1661095 := bstep (se 1 (by rfl) ⟨1245821, by rfl⟩ : syracuseStep 1661095 = 2491643) B2491643
theorem B3725623 : Blo 774336 3725623 := bstep (se 1 (by rfl) ⟨2794217, by rfl⟩ : syracuseStep 3725623 = 5588435) B5588435
theorem B4544923 : Blo 774336 4544923 := bstep (se 1 (by rfl) ⟨3408692, by rfl⟩ : syracuseStep 4544923 = 6817385) B6817385
theorem B777327 : Blo 774336 777327 := bstep (se 1 (by rfl) ⟨582995, by rfl⟩ : syracuseStep 777327 = 1165991) B1165991
theorem B777631 : Blo 774336 777631 := bstep (se 1 (by rfl) ⟨583223, by rfl⟩ : syracuseStep 777631 = 1166447) B1166447
theorem B778087 : Blo 774336 778087 := bstep (se 1 (by rfl) ⟨583565, by rfl⟩ : syracuseStep 778087 = 1167131) B1167131
theorem B3727241 : Blo 774336 3727241 := bstep (se 2 (by rfl) ⟨1397715, by rfl⟩ : syracuseStep 3727241 = 2795431) B2795431
theorem B2613491 : Blo 774336 2613491 := bstep (se 1 (by rfl) ⟨1960118, by rfl⟩ : syracuseStep 2613491 = 3920237) B3920237
theorem B11330999 : Blo 774336 11330999 := bstep (se 1 (by rfl) ⟨8498249, by rfl⟩ : syracuseStep 11330999 = 16996499) B16996499
theorem B2516807 : Blo 774336 2516807 := bstep (se 1 (by rfl) ⟨1887605, by rfl⟩ : syracuseStep 2516807 = 3775211) B3775211
theorem B2615327 : Blo 774336 2615327 := bstep (se 1 (by rfl) ⟨1961495, by rfl⟩ : syracuseStep 2615327 = 3922991) B3922991
theorem B5892263 : Blo 774336 5892263 := bstep (se 1 (by rfl) ⟨4419197, by rfl⟩ : syracuseStep 5892263 = 8838395) B8838395
theorem B1960919 : Blo 774336 1960919 := bstep (se 1 (by rfl) ⟨1470689, by rfl⟩ : syracuseStep 1960919 = 2941379) B2941379
theorem B26864759 : Blo 774336 26864759 := bstep (se 1 (by rfl) ⟨20148569, by rfl⟩ : syracuseStep 26864759 = 40297139) B40297139
theorem B3993583 : Blo 774336 3993583 := bstep (se 1 (by rfl) ⟨2995187, by rfl⟩ : syracuseStep 3993583 = 5990375) B5990375
theorem B3141679 : Blo 774336 3141679 := bstep (se 1 (by rfl) ⟨2356259, by rfl⟩ : syracuseStep 3141679 = 4712519) B4712519
theorem B6647933 : Blo 774336 6647933 := bstep (se 3 (by rfl) ⟨1246487, by rfl⟩ : syracuseStep 6647933 = 2492975) B2492975
theorem B1306793 : Blo 774336 1306793 := bstep (se 2 (by rfl) ⟨490047, by rfl⟩ : syracuseStep 1306793 = 980095) B980095
theorem B4419791 : Blo 774336 4419791 := bstep (se 1 (by rfl) ⟨3314843, by rfl⟩ : syracuseStep 4419791 = 6629687) B6629687
theorem B1470955 : Blo 774336 1470955 := bstep (se 1 (by rfl) ⟨1103216, by rfl⟩ : syracuseStep 1470955 = 2206433) B2206433
theorem B6615539 : Blo 774336 6615539 := bstep (se 1 (by rfl) ⟨4961654, by rfl⟩ : syracuseStep 6615539 = 9923309) B9923309
theorem B1471031 : Blo 774336 1471031 := bstep (se 1 (by rfl) ⟨1103273, by rfl⟩ : syracuseStep 1471031 = 2206547) B2206547
theorem B5600087 : Blo 774336 5600087 := bstep (se 1 (by rfl) ⟨4200065, by rfl⟩ : syracuseStep 5600087 = 8400131) B8400131
theorem B558265283 : Blo 774336 558265283 := bstep (se 1 (by rfl) ⟨418698962, by rfl⟩ : syracuseStep 558265283 = 837397925) B837397925
theorem B2651123 : Blo 774336 2651123 := bstep (se 1 (by rfl) ⟨1988342, by rfl⟩ : syracuseStep 2651123 = 3976685) B3976685
theorem B3929147 : Blo 774336 3929147 := bstep (se 1 (by rfl) ⟨2946860, by rfl⟩ : syracuseStep 3929147 = 5893721) B5893721
theorem B1307785 : Blo 774336 1307785 := bstep (se 2 (by rfl) ⟨490419, by rfl⟩ : syracuseStep 1307785 = 980839) B980839
theorem B1307839 : Blo 774336 1307839 := bstep (se 1 (by rfl) ⟨980879, by rfl⟩ : syracuseStep 1307839 = 1961759) B1961759
theorem B4978007 : Blo 774336 4978007 := bstep (se 1 (by rfl) ⟨3733505, by rfl⟩ : syracuseStep 4978007 = 7467011) B7467011
theorem B1963511 : Blo 774336 1963511 := bstep (se 1 (by rfl) ⟨1472633, by rfl⟩ : syracuseStep 1963511 = 2945267) B2945267
theorem B4192019 : Blo 774336 4192019 := bstep (se 1 (by rfl) ⟨3144014, by rfl⟩ : syracuseStep 4192019 = 6288029) B6288029
theorem B2619161 : Blo 774336 2619161 := bstep (se 2 (by rfl) ⟨982185, by rfl⟩ : syracuseStep 2619161 = 1964371) B1964371
theorem B2947211 : Blo 774336 2947211 := bstep (se 1 (by rfl) ⟨2210408, by rfl⟩ : syracuseStep 2947211 = 4420817) B4420817
theorem B2488799 : Blo 774336 2488799 := bstep (se 1 (by rfl) ⟨1866599, by rfl⟩ : syracuseStep 2488799 = 3733199) B3733199
theorem B51706507 : Blo 774336 51706507 := bstep (se 1 (by rfl) ⟨38779880, by rfl⟩ : syracuseStep 51706507 = 77559761) B77559761
theorem B3932063 : Blo 774336 3932063 := bstep (se 1 (by rfl) ⟨2949047, by rfl⟩ : syracuseStep 3932063 = 5898095) B5898095
theorem B7077827 : Blo 774336 7077827 := bstep (se 1 (by rfl) ⟨5308370, by rfl⟩ : syracuseStep 7077827 = 10616741) B10616741
theorem B10092527 : Blo 774336 10092527 := bstep (se 1 (by rfl) ⟨7569395, by rfl⟩ : syracuseStep 10092527 = 15138791) B15138791
theorem B5604005 : Blo 774336 5604005 := bstep (se 4 (by rfl) ⟨525375, by rfl⟩ : syracuseStep 5604005 = 1050751) B1050751
theorem B1312247 : Blo 774336 1312247 := bstep (se 1 (by rfl) ⟨984185, by rfl⟩ : syracuseStep 1312247 = 1968371) B1968371
theorem B2951387 : Blo 774336 2951387 := bstep (se 1 (by rfl) ⟨2213540, by rfl⟩ : syracuseStep 2951387 = 4427081) B4427081
theorem B3935303 : Blo 774336 3935303 := bstep (se 1 (by rfl) ⟨2951477, by rfl⟩ : syracuseStep 3935303 = 5902955) B5902955
theorem B1969343 : Blo 774336 1969343 := bstep (se 1 (by rfl) ⟨1477007, by rfl⟩ : syracuseStep 1969343 = 2954015) B2954015
theorem B4984105 : Blo 774336 4984105 := bstep (se 2 (by rfl) ⟨1869039, by rfl⟩ : syracuseStep 4984105 = 3738079) B3738079
theorem B1970153 : Blo 774336 1970153 := bstep (se 2 (by rfl) ⟨738807, by rfl⟩ : syracuseStep 1970153 = 1477615) B1477615
theorem B7966831 : Blo 774336 7966831 := bstep (se 1 (by rfl) ⟨5975123, by rfl⟩ : syracuseStep 7966831 = 11950247) B11950247
theorem B8393341 : Blo 774336 8393341 := bstep (se 3 (by rfl) ⟨1573751, by rfl⟩ : syracuseStep 8393341 = 3147503) B3147503
theorem B9442655 : Blo 774336 9442655 := bstep (se 1 (by rfl) ⟨7081991, by rfl⟩ : syracuseStep 9442655 = 14163983) B14163983
theorem B7476623 : Blo 774336 7476623 := bstep (se 1 (by rfl) ⟨5607467, by rfl⟩ : syracuseStep 7476623 = 11214935) B11214935
theorem B6624665 : Blo 774336 6624665 := bstep (se 2 (by rfl) ⟨2484249, by rfl⟩ : syracuseStep 6624665 = 4968499) B4968499
theorem B1742327 : Blo 774336 1742327 := bstep (se 1 (by rfl) ⟨1306745, by rfl⟩ : syracuseStep 1742327 = 2613491) B2613491
theorem B13244471 : Blo 774336 13244471 := bstep (se 1 (by rfl) ⟨9933353, by rfl⟩ : syracuseStep 13244471 = 19866707) B19866707
theorem B1677871 : Blo 774336 1677871 := bstep (se 1 (by rfl) ⟨1258403, by rfl⟩ : syracuseStep 1677871 = 2516807) B2516807
theorem B1743551 : Blo 774336 1743551 := bstep (se 1 (by rfl) ⟨1307663, by rfl⟩ : syracuseStep 1743551 = 2615327) B2615327
theorem B1743713 : Blo 774336 1743713 := bstep (se 2 (by rfl) ⟨653892, by rfl⟩ : syracuseStep 1743713 = 1307785) B1307785
theorem B3021707 : Blo 774336 3021707 := bstep (se 1 (by rfl) ⟨2266280, by rfl⟩ : syracuseStep 3021707 = 4532561) B4532561
theorem B1743785 : Blo 774336 1743785 := bstep (se 2 (by rfl) ⟨653919, by rfl⟩ : syracuseStep 1743785 = 1307839) B1307839
theorem B50470289 : Blo 774336 50470289 := bstep (se 2 (by rfl) ⟨18926358, by rfl⟩ : syracuseStep 50470289 = 37852717) B37852717
theorem B4431955 : Blo 774336 4431955 := bstep (se 1 (by rfl) ⟨3323966, by rfl⟩ : syracuseStep 4431955 = 6647933) B6647933
theorem B4202617 : Blo 774336 4202617 := bstep (se 2 (by rfl) ⟨1575981, by rfl⟩ : syracuseStep 4202617 = 3151963) B3151963
theorem B5906843 : Blo 774336 5906843 := bstep (se 1 (by rfl) ⟨4430132, by rfl⟩ : syracuseStep 5906843 = 8860265) B8860265
theorem B6300355 : Blo 774336 6300355 := bstep (se 1 (by rfl) ⟨4725266, by rfl⟩ : syracuseStep 6300355 = 9450533) B9450533
theorem B3318671 : Blo 774336 3318671 := bstep (se 1 (by rfl) ⟨2489003, by rfl⟩ : syracuseStep 3318671 = 4978007) B4978007
theorem B2794679 : Blo 774336 2794679 := bstep (se 1 (by rfl) ⟨2096009, by rfl⟩ : syracuseStep 2794679 = 4192019) B4192019
theorem B1746107 : Blo 774336 1746107 := bstep (se 1 (by rfl) ⟨1309580, by rfl⟩ : syracuseStep 1746107 = 2619161) B2619161
theorem B7972505 : Blo 774336 7972505 := bstep (se 2 (by rfl) ⟨2989689, by rfl⟩ : syracuseStep 7972505 = 5979379) B5979379
theorem B6728351 : Blo 774336 6728351 := bstep (se 1 (by rfl) ⟨5046263, by rfl⟩ : syracuseStep 6728351 = 10092527) B10092527
theorem B1747691 : Blo 774336 1747691 := bstep (se 1 (by rfl) ⟨1310768, by rfl⟩ : syracuseStep 1747691 = 2621537) B2621537
theorem B1747835 : Blo 774336 1747835 := bstep (se 1 (by rfl) ⟨1310876, by rfl⟩ : syracuseStep 1747835 = 2621753) B2621753
theorem B1748591 : Blo 774336 1748591 := bstep (se 1 (by rfl) ⟨1311443, by rfl⟩ : syracuseStep 1748591 = 2622887) B2622887
theorem B1748735 : Blo 774336 1748735 := bstep (se 1 (by rfl) ⟨1311551, by rfl⟩ : syracuseStep 1748735 = 2623103) B2623103
theorem B1749419 : Blo 774336 1749419 := bstep (se 1 (by rfl) ⟨1312064, by rfl⟩ : syracuseStep 1749419 = 2624129) B2624129
theorem B15151951 : Blo 774336 15151951 := bstep (se 1 (by rfl) ⟨11363963, by rfl⟩ : syracuseStep 15151951 = 22727927) B22727927
theorem B1749887 : Blo 774336 1749887 := bstep (se 1 (by rfl) ⟨1312415, by rfl⟩ : syracuseStep 1749887 = 2624831) B2624831
theorem B3322873 : Blo 774336 3322873 := bstep (se 2 (by rfl) ⟨1246077, by rfl⟩ : syracuseStep 3322873 = 2492155) B2492155
theorem B13253219 : Blo 774336 13253219 := bstep (se 1 (by rfl) ⟨9939914, by rfl⟩ : syracuseStep 13253219 = 19879829) B19879829
theorem B1161947 : Blo 774336 1161947 := bstep (se 1 (by rfl) ⟨871460, by rfl⟩ : syracuseStep 1161947 = 1742921) B1742921
theorem B1162343 : Blo 774336 1162343 := bstep (se 1 (by rfl) ⟨871757, by rfl⟩ : syracuseStep 1162343 = 1743515) B1743515
theorem B5324777 : Blo 774336 5324777 := bstep (se 2 (by rfl) ⟨1996791, by rfl⟩ : syracuseStep 5324777 = 3993583) B3993583
theorem B1163711 : Blo 774336 1163711 := bstep (se 1 (by rfl) ⟨872783, by rfl⟩ : syracuseStep 1163711 = 1745567) B1745567
theorem B7553999 : Blo 774336 7553999 := bstep (se 1 (by rfl) ⟨5665499, by rfl⟩ : syracuseStep 7553999 = 11330999) B11330999
theorem B1164599 : Blo 774336 1164599 := bstep (se 1 (by rfl) ⟨873449, by rfl⟩ : syracuseStep 1164599 = 1746899) B1746899
theorem B1164665 : Blo 774336 1164665 := bstep (se 2 (by rfl) ⟨436749, by rfl⟩ : syracuseStep 1164665 = 873499) B873499
theorem B1164671 : Blo 774336 1164671 := bstep (se 1 (by rfl) ⟨873503, by rfl⟩ : syracuseStep 1164671 = 1747007) B1747007
theorem B4966267 : Blo 774336 4966267 := bstep (se 1 (by rfl) ⟨3724700, by rfl⟩ : syracuseStep 4966267 = 7449401) B7449401
theorem B17909839 : Blo 774336 17909839 := bstep (se 1 (by rfl) ⟨13432379, by rfl⟩ : syracuseStep 17909839 = 26864759) B26864759
theorem B1165439 : Blo 774336 1165439 := bstep (se 1 (by rfl) ⟨874079, by rfl⟩ : syracuseStep 1165439 = 1748159) B1748159
theorem B2803895 : Blo 774336 2803895 := bstep (se 1 (by rfl) ⟨2102921, by rfl⟩ : syracuseStep 2803895 = 4205843) B4205843
theorem B1165799 : Blo 774336 1165799 := bstep (se 1 (by rfl) ⟨874349, by rfl⟩ : syracuseStep 1165799 = 1748699) B1748699
theorem B871195 : Blo 774336 871195 := bstep (se 1 (by rfl) ⟨653396, by rfl⟩ : syracuseStep 871195 = 1306793) B1306793
theorem B2214793 : Blo 774336 2214793 := bstep (se 2 (by rfl) ⟨830547, by rfl⟩ : syracuseStep 2214793 = 1661095) B1661095
theorem B4410359 : Blo 774336 4410359 := bstep (se 1 (by rfl) ⟨3307769, by rfl⟩ : syracuseStep 4410359 = 6615539) B6615539
theorem B4967497 : Blo 774336 4967497 := bstep (se 2 (by rfl) ⟨1862811, by rfl⟩ : syracuseStep 4967497 = 3725623) B3725623
theorem B1166567 : Blo 774336 1166567 := bstep (se 1 (by rfl) ⟨874925, by rfl⟩ : syracuseStep 1166567 = 1749851) B1749851
theorem B9948527 : Blo 774336 9948527 := bstep (se 1 (by rfl) ⟨7461395, by rfl⟩ : syracuseStep 9948527 = 14922791) B14922791
theorem B9424603 : Blo 774336 9424603 := bstep (se 1 (by rfl) ⟨7068452, by rfl⟩ : syracuseStep 9424603 = 14136905) B14136905
theorem B8409257 : Blo 774336 8409257 := bstep (se 2 (by rfl) ⟨3153471, by rfl⟩ : syracuseStep 8409257 = 6306943) B6306943
theorem B774427 : Blo 774336 774427 := bstep (se 1 (by rfl) ⟨580820, by rfl⟩ : syracuseStep 774427 = 1161641) B1161641
theorem B774463 : Blo 774336 774463 := bstep (se 1 (by rfl) ⟨580847, by rfl⟩ : syracuseStep 774463 = 1161695) B1161695
theorem B1659199 : Blo 774336 1659199 := bstep (se 1 (by rfl) ⟨1244399, by rfl⟩ : syracuseStep 1659199 = 2488799) B2488799
theorem B774655 : Blo 774336 774655 := bstep (se 1 (by rfl) ⟨580991, by rfl⟩ : syracuseStep 774655 = 1161983) B1161983
theorem B774703 : Blo 774336 774703 := bstep (se 1 (by rfl) ⟨581027, by rfl⟩ : syracuseStep 774703 = 1162055) B1162055
theorem B1495999 : Blo 774336 1495999 := bstep (se 1 (by rfl) ⟨1121999, by rfl⟩ : syracuseStep 1495999 = 2243999) B2243999
theorem B775195 : Blo 774336 775195 := bstep (se 1 (by rfl) ⟨581396, by rfl⟩ : syracuseStep 775195 = 1162793) B1162793
theorem B775279 : Blo 774336 775279 := bstep (se 1 (by rfl) ⟨581459, by rfl⟩ : syracuseStep 775279 = 1162919) B1162919
theorem B775327 : Blo 774336 775327 := bstep (se 1 (by rfl) ⟨581495, by rfl⟩ : syracuseStep 775327 = 1162991) B1162991
theorem B4379815 : Blo 774336 4379815 := bstep (se 1 (by rfl) ⟨3284861, by rfl⟩ : syracuseStep 4379815 = 6569723) B6569723
theorem B775527 : Blo 774336 775527 := bstep (se 1 (by rfl) ⟨581645, by rfl⟩ : syracuseStep 775527 = 1163291) B1163291
theorem B775887 : Blo 774336 775887 := bstep (se 1 (by rfl) ⟨581915, by rfl⟩ : syracuseStep 775887 = 1163831) B1163831
theorem B775911 : Blo 774336 775911 := bstep (se 1 (by rfl) ⟨581933, by rfl⟩ : syracuseStep 775911 = 1163867) B1163867
theorem B776159 : Blo 774336 776159 := bstep (se 1 (by rfl) ⟨582119, by rfl⟩ : syracuseStep 776159 = 1164239) B1164239
theorem B874543 : Blo 774336 874543 := bstep (se 1 (by rfl) ⟨655907, by rfl⟩ : syracuseStep 874543 = 1311815) B1311815
theorem B776359 : Blo 774336 776359 := bstep (se 1 (by rfl) ⟨582269, by rfl⟩ : syracuseStep 776359 = 1164539) B1164539
theorem B776511 : Blo 774336 776511 := bstep (se 1 (by rfl) ⟨582383, by rfl⟩ : syracuseStep 776511 = 1164767) B1164767
theorem B776687 : Blo 774336 776687 := bstep (se 1 (by rfl) ⟨582515, by rfl⟩ : syracuseStep 776687 = 1165031) B1165031
theorem B776991 : Blo 774336 776991 := bstep (se 1 (by rfl) ⟨582743, by rfl⟩ : syracuseStep 776991 = 1165487) B1165487
theorem B777247 : Blo 774336 777247 := bstep (se 1 (by rfl) ⟨582935, by rfl⟩ : syracuseStep 777247 = 1165871) B1165871
theorem B875551 : Blo 774336 875551 := bstep (se 1 (by rfl) ⟨656663, by rfl⟩ : syracuseStep 875551 = 1313327) B1313327
theorem B6642809 : Blo 774336 6642809 := bstep (se 2 (by rfl) ⟨2491053, by rfl⟩ : syracuseStep 6642809 = 4982107) B4982107
theorem B13261967 : Blo 774336 13261967 := bstep (se 1 (by rfl) ⟨9946475, by rfl⟩ : syracuseStep 13261967 = 19892951) B19892951
theorem B777375 : Blo 774336 777375 := bstep (se 1 (by rfl) ⟨583031, by rfl⟩ : syracuseStep 777375 = 1166063) B1166063
theorem B3726587 : Blo 774336 3726587 := bstep (se 1 (by rfl) ⟨2794940, by rfl⟩ : syracuseStep 3726587 = 5589881) B5589881
theorem B778143 : Blo 774336 778143 := bstep (se 1 (by rfl) ⟨583607, by rfl⟩ : syracuseStep 778143 = 1167215) B1167215
theorem B7463015 : Blo 774336 7463015 := bstep (se 1 (by rfl) ⟨5597261, by rfl⟩ : syracuseStep 7463015 = 11194523) B11194523
theorem B51175709 : Blo 774336 51175709 := bstep (se 3 (by rfl) ⟨9595445, by rfl⟩ : syracuseStep 51175709 = 19190891) B19190891
theorem B3925259 : Blo 774336 3925259 := bstep (se 1 (by rfl) ⟨2943944, by rfl⟩ : syracuseStep 3925259 = 5887889) B5887889
theorem B11167415 : Blo 774336 11167415 := bstep (se 1 (by rfl) ⟨8375561, by rfl⟩ : syracuseStep 11167415 = 16751123) B16751123
theorem B28370857 : Blo 774336 28370857 := bstep (se 2 (by rfl) ⟨10639071, by rfl⟩ : syracuseStep 28370857 = 21278143) B21278143
theorem B2484827 : Blo 774336 2484827 := bstep (se 1 (by rfl) ⟨1863620, by rfl⟩ : syracuseStep 2484827 = 3727241) B3727241
theorem B4188905 : Blo 774336 4188905 := bstep (se 2 (by rfl) ⟨1570839, by rfl⟩ : syracuseStep 4188905 = 3141679) B3141679
theorem B1961273 : Blo 774336 1961273 := bstep (se 2 (by rfl) ⟨735477, by rfl⟩ : syracuseStep 1961273 = 1470955) B1470955
theorem B4419359 : Blo 774336 4419359 := bstep (se 1 (by rfl) ⟨3314519, by rfl⟩ : syracuseStep 4419359 = 6629039) B6629039
theorem B1470287 : Blo 774336 1470287 := bstep (se 1 (by rfl) ⟨1102715, by rfl⟩ : syracuseStep 1470287 = 2205431) B2205431
theorem B3928175 : Blo 774336 3928175 := bstep (se 1 (by rfl) ⟨2946131, by rfl⟩ : syracuseStep 3928175 = 5892263) B5892263
theorem B1307279 : Blo 774336 1307279 := bstep (se 1 (by rfl) ⟨980459, by rfl⟩ : syracuseStep 1307279 = 1960919) B1960919
theorem B1865081 : Blo 774336 1865081 := bstep (se 2 (by rfl) ⟨699405, by rfl⟩ : syracuseStep 1865081 = 1398811) B1398811
theorem B2946527 : Blo 774336 2946527 := bstep (se 1 (by rfl) ⟨2209895, by rfl⟩ : syracuseStep 2946527 = 4419791) B4419791
theorem B980687 : Blo 774336 980687 := bstep (se 1 (by rfl) ⟨735515, by rfl⟩ : syracuseStep 980687 = 1471031) B1471031
theorem B6059897 : Blo 774336 6059897 := bstep (se 2 (by rfl) ⟨2272461, by rfl⟩ : syracuseStep 6059897 = 4544923) B4544923
theorem B3733391 : Blo 774336 3733391 := bstep (se 1 (by rfl) ⟨2800043, by rfl⟩ : syracuseStep 3733391 = 5600087) B5600087
theorem B372176855 : Blo 774336 372176855 := bstep (se 1 (by rfl) ⟨279132641, by rfl⟩ : syracuseStep 372176855 = 558265283) B558265283
theorem B1767415 : Blo 774336 1767415 := bstep (se 1 (by rfl) ⟨1325561, by rfl⟩ : syracuseStep 1767415 = 2651123) B2651123
theorem B2619431 : Blo 774336 2619431 := bstep (se 1 (by rfl) ⟨1964573, by rfl⟩ : syracuseStep 2619431 = 3929147) B3929147
theorem B68942009 : Blo 774336 68942009 := bstep (se 2 (by rfl) ⟨25853253, by rfl⟩ : syracuseStep 68942009 = 51706507) B51706507
theorem B1309007 : Blo 774336 1309007 := bstep (se 1 (by rfl) ⟨981755, by rfl⟩ : syracuseStep 1309007 = 1963511) B1963511
theorem B1964807 : Blo 774336 1964807 := bstep (se 1 (by rfl) ⟨1473605, by rfl⟩ : syracuseStep 1964807 = 2947211) B2947211
theorem B18874205 : Blo 774336 18874205 := bstep (se 3 (by rfl) ⟨3538913, by rfl⟩ : syracuseStep 18874205 = 7077827) B7077827
theorem B2621375 : Blo 774336 2621375 := bstep (se 1 (by rfl) ⟨1966031, by rfl⟩ : syracuseStep 2621375 = 3932063) B3932063
theorem B5603489 : Blo 774336 5603489 := bstep (se 2 (by rfl) ⟨2101308, by rfl⟩ : syracuseStep 5603489 = 4202617) B4202617
theorem B1869263 : Blo 774336 1869263 := bstep (se 1 (by rfl) ⟨1401947, by rfl⟩ : syracuseStep 1869263 = 2803895) B2803895
theorem B1967591 : Blo 774336 1967591 := bstep (se 1 (by rfl) ⟨1475693, by rfl⟩ : syracuseStep 1967591 = 2951387) B2951387
theorem B14944013 : Blo 774336 14944013 := bstep (se 3 (by rfl) ⟨2802002, by rfl⟩ : syracuseStep 14944013 = 5604005) B5604005
theorem B2623535 : Blo 774336 2623535 := bstep (se 1 (by rfl) ⟨1967651, by rfl⟩ : syracuseStep 2623535 = 3935303) B3935303
theorem B1312895 : Blo 774336 1312895 := bstep (se 1 (by rfl) ⟨984671, by rfl⟩ : syracuseStep 1312895 = 1969343) B1969343
theorem B6621689 : Blo 774336 6621689 := bstep (se 2 (by rfl) ⟨2483133, by rfl⟩ : syracuseStep 6621689 = 4966267) B4966267
theorem B1313435 : Blo 774336 1313435 := bstep (se 1 (by rfl) ⟨985076, by rfl⟩ : syracuseStep 1313435 = 1970153) B1970153
theorem B5606171 : Blo 774336 5606171 := bstep (se 1 (by rfl) ⟨4204628, by rfl⟩ : syracuseStep 5606171 = 8409257) B8409257
theorem B6295103 : Blo 774336 6295103 := bstep (se 1 (by rfl) ⟨4721327, by rfl⟩ : syracuseStep 6295103 = 9442655) B9442655
theorem B4984415 : Blo 774336 4984415 := bstep (se 1 (by rfl) ⟨3738311, by rfl⟩ : syracuseStep 4984415 = 7476623) B7476623
theorem B2953057 : Blo 774336 2953057 := bstep (se 2 (by rfl) ⟨1107396, by rfl⟩ : syracuseStep 2953057 = 2214793) B2214793
theorem B6623329 : Blo 774336 6623329 := bstep (se 2 (by rfl) ⟨2483748, by rfl⟩ : syracuseStep 6623329 = 4967497) B4967497
theorem B4428539 : Blo 774336 4428539 := bstep (se 1 (by rfl) ⟨3321404, by rfl⟩ : syracuseStep 4428539 = 6642809) B6642809
theorem B10622441 : Blo 774336 10622441 := bstep (se 2 (by rfl) ⟨3983415, by rfl⟩ : syracuseStep 10622441 = 7966831) B7966831
theorem B34117139 : Blo 774336 34117139 := bstep (se 1 (by rfl) ⟨25587854, by rfl⟩ : syracuseStep 34117139 = 51175709) B51175709
theorem B3937895 : Blo 774336 3937895 := bstep (se 1 (by rfl) ⟨2953421, by rfl⟩ : syracuseStep 3937895 = 5906843) B5906843
theorem B5315003 : Blo 774336 5315003 := bstep (se 1 (by rfl) ⟨3986252, by rfl⟩ : syracuseStep 5315003 = 7972505) B7972505
theorem B7444943 : Blo 774336 7444943 := bstep (se 1 (by rfl) ⟨5583707, by rfl⟩ : syracuseStep 7444943 = 11167415) B11167415
theorem B4430497 : Blo 774336 4430497 := bstep (se 2 (by rfl) ⟨1661436, by rfl⟩ : syracuseStep 4430497 = 3322873) B3322873
theorem B2792603 : Blo 774336 2792603 := bstep (se 1 (by rfl) ⟨2094452, by rfl⟩ : syracuseStep 2792603 = 4188905) B4188905
theorem B2237161 : Blo 774336 2237161 := bstep (se 2 (by rfl) ⟨838935, by rfl⟩ : syracuseStep 2237161 = 1677871) B1677871
theorem B4039931 : Blo 774336 4039931 := bstep (se 1 (by rfl) ⟨3029948, by rfl⟩ : syracuseStep 4039931 = 6059897) B6059897
theorem B1746287 : Blo 774336 1746287 := bstep (se 1 (by rfl) ⟨1309715, by rfl⟩ : syracuseStep 1746287 = 2619431) B2619431
theorem B1747583 : Blo 774336 1747583 := bstep (se 1 (by rfl) ⟨1310687, by rfl⟩ : syracuseStep 1747583 = 2621375) B2621375
theorem B3549851 : Blo 774336 3549851 := bstep (se 1 (by rfl) ⟨2662388, by rfl⟩ : syracuseStep 3549851 = 5324777) B5324777
theorem B5909273 : Blo 774336 5909273 := bstep (se 2 (by rfl) ⟨2215977, by rfl⟩ : syracuseStep 5909273 = 4431955) B4431955
theorem B8400473 : Blo 774336 8400473 := bstep (se 2 (by rfl) ⟨3150177, by rfl⟩ : syracuseStep 8400473 = 6300355) B6300355
theorem B6632351 : Blo 774336 6632351 := bstep (se 1 (by rfl) ⟨4974263, by rfl⟩ : syracuseStep 6632351 = 9948527) B9948527
theorem B37827809 : Blo 774336 37827809 := bstep (se 2 (by rfl) ⟨14185428, by rfl⟩ : syracuseStep 37827809 = 28370857) B28370857
theorem B1161551 : Blo 774336 1161551 := bstep (se 1 (by rfl) ⟨871163, by rfl⟩ : syracuseStep 1161551 = 1742327) B1742327
theorem B1161593 : Blo 774336 1161593 := bstep (se 2 (by rfl) ⟨435597, by rfl⟩ : syracuseStep 1161593 = 871195) B871195
theorem B8829647 : Blo 774336 8829647 := bstep (se 1 (by rfl) ⟨6622235, by rfl⟩ : syracuseStep 8829647 = 13244471) B13244471
theorem B1162367 : Blo 774336 1162367 := bstep (se 1 (by rfl) ⟨871775, by rfl⟩ : syracuseStep 1162367 = 1743551) B1743551
theorem B1162475 : Blo 774336 1162475 := bstep (se 1 (by rfl) ⟨871856, by rfl⟩ : syracuseStep 1162475 = 1743713) B1743713
theorem B2014471 : Blo 774336 2014471 := bstep (se 1 (by rfl) ⟨1510853, by rfl⟩ : syracuseStep 2014471 = 3021707) B3021707
theorem B1162523 : Blo 774336 1162523 := bstep (se 1 (by rfl) ⟨871892, by rfl⟩ : syracuseStep 1162523 = 1743785) B1743785
theorem B12566137 : Blo 774336 12566137 := bstep (se 2 (by rfl) ⟨4712301, by rfl⟩ : syracuseStep 12566137 = 9424603) B9424603
theorem B2212265 : Blo 774336 2212265 := bstep (se 2 (by rfl) ⟨829599, by rfl⟩ : syracuseStep 2212265 = 1659199) B1659199
theorem B2212447 : Blo 774336 2212447 := bstep (se 1 (by rfl) ⟨1659335, by rfl⟩ : syracuseStep 2212447 = 3318671) B3318671
theorem B1164071 : Blo 774336 1164071 := bstep (se 1 (by rfl) ⟨873053, by rfl⟩ : syracuseStep 1164071 = 1746107) B1746107
theorem B11191121 : Blo 774336 11191121 := bstep (se 2 (by rfl) ⟨4196670, by rfl⟩ : syracuseStep 11191121 = 8393341) B8393341
theorem B20202601 : Blo 774336 20202601 := bstep (se 2 (by rfl) ⟨7575975, by rfl⟩ : syracuseStep 20202601 = 15151951) B15151951
theorem B1656551 : Blo 774336 1656551 := bstep (se 1 (by rfl) ⟨1242413, by rfl⟩ : syracuseStep 1656551 = 2484827) B2484827
theorem B17942269 : Blo 774336 17942269 := bstep (se 3 (by rfl) ⟨3364175, by rfl⟩ : syracuseStep 17942269 = 6728351) B6728351
theorem B1165127 : Blo 774336 1165127 := bstep (se 1 (by rfl) ⟨873845, by rfl⟩ : syracuseStep 1165127 = 1747691) B1747691
theorem B1165223 : Blo 774336 1165223 := bstep (se 1 (by rfl) ⟨873917, by rfl⟩ : syracuseStep 1165223 = 1747835) B1747835
theorem B1165727 : Blo 774336 1165727 := bstep (se 1 (by rfl) ⟨874295, by rfl⟩ : syracuseStep 1165727 = 1748591) B1748591
theorem B1165823 : Blo 774336 1165823 := bstep (se 1 (by rfl) ⟨874367, by rfl⟩ : syracuseStep 1165823 = 1748735) B1748735
theorem B1166057 : Blo 774336 1166057 := bstep (se 2 (by rfl) ⟨437271, by rfl⟩ : syracuseStep 1166057 = 874543) B874543
theorem B1166279 : Blo 774336 1166279 := bstep (se 1 (by rfl) ⟨874709, by rfl⟩ : syracuseStep 1166279 = 1749419) B1749419
theorem B871519 : Blo 774336 871519 := bstep (se 1 (by rfl) ⟨653639, by rfl⟩ : syracuseStep 871519 = 1307279) B1307279
theorem B1166591 : Blo 774336 1166591 := bstep (se 1 (by rfl) ⟨874943, by rfl⟩ : syracuseStep 1166591 = 1749887) B1749887
theorem B1167401 : Blo 774336 1167401 := bstep (se 2 (by rfl) ⟨437775, by rfl⟩ : syracuseStep 1167401 = 875551) B875551
theorem B45961339 : Blo 774336 45961339 := bstep (se 1 (by rfl) ⟨34471004, by rfl⟩ : syracuseStep 45961339 = 68942009) B68942009
theorem B872671 : Blo 774336 872671 := bstep (se 1 (by rfl) ⟨654503, by rfl⟩ : syracuseStep 872671 = 1309007) B1309007
theorem B8835479 : Blo 774336 8835479 := bstep (se 1 (by rfl) ⟨6626609, by rfl⟩ : syracuseStep 8835479 = 13253219) B13253219
theorem B774631 : Blo 774336 774631 := bstep (se 1 (by rfl) ⟨580973, by rfl⟩ : syracuseStep 774631 = 1161947) B1161947
theorem B774895 : Blo 774336 774895 := bstep (se 1 (by rfl) ⟨581171, by rfl⟩ : syracuseStep 774895 = 1162343) B1162343
theorem B775807 : Blo 774336 775807 := bstep (se 1 (by rfl) ⟨581855, by rfl⟩ : syracuseStep 775807 = 1163711) B1163711
theorem B776399 : Blo 774336 776399 := bstep (se 1 (by rfl) ⟨582299, by rfl⟩ : syracuseStep 776399 = 1164599) B1164599
theorem B776443 : Blo 774336 776443 := bstep (se 1 (by rfl) ⟨582332, by rfl⟩ : syracuseStep 776443 = 1164665) B1164665
theorem B776447 : Blo 774336 776447 := bstep (se 1 (by rfl) ⟨582335, by rfl⟩ : syracuseStep 776447 = 1164671) B1164671
theorem B874831 : Blo 774336 874831 := bstep (se 1 (by rfl) ⟨656123, by rfl⟩ : syracuseStep 874831 = 1312247) B1312247
theorem B776959 : Blo 774336 776959 := bstep (se 1 (by rfl) ⟨582719, by rfl⟩ : syracuseStep 776959 = 1165439) B1165439
theorem B777199 : Blo 774336 777199 := bstep (se 1 (by rfl) ⟨582899, by rfl⟩ : syracuseStep 777199 = 1165799) B1165799
theorem B2940239 : Blo 774336 2940239 := bstep (se 1 (by rfl) ⟨2205179, by rfl⟩ : syracuseStep 2940239 = 4410359) B4410359
theorem B777711 : Blo 774336 777711 := bstep (se 1 (by rfl) ⟨583283, by rfl⟩ : syracuseStep 777711 = 1166567) B1166567
theorem B20143997 : Blo 774336 20143997 := bstep (se 3 (by rfl) ⟨3776999, by rfl⟩ : syracuseStep 20143997 = 7553999) B7553999
theorem B23879785 : Blo 774336 23879785 := bstep (se 2 (by rfl) ⟨8954919, by rfl⟩ : syracuseStep 23879785 = 17909839) B17909839
theorem B4416443 : Blo 774336 4416443 := bstep (se 1 (by rfl) ⟨3312332, by rfl⟩ : syracuseStep 4416443 = 6624665) B6624665
theorem B6645473 : Blo 774336 6645473 := bstep (se 2 (by rfl) ⟨2492052, by rfl⟩ : syracuseStep 6645473 = 4984105) B4984105
theorem B2615165 : Blo 774336 2615165 := bstep (se 3 (by rfl) ⟨490343, by rfl⟩ : syracuseStep 2615165 = 980687) B980687
theorem B8841311 : Blo 774336 8841311 := bstep (se 1 (by rfl) ⟨6630983, by rfl⟩ : syracuseStep 8841311 = 13261967) B13261967
theorem B2484391 : Blo 774336 2484391 := bstep (se 1 (by rfl) ⟨1863293, by rfl⟩ : syracuseStep 2484391 = 3726587) B3726587
theorem B33646859 : Blo 774336 33646859 := bstep (se 1 (by rfl) ⟨25235144, by rfl⟩ : syracuseStep 33646859 = 50470289) B50470289
theorem B4975343 : Blo 774336 4975343 := bstep (se 1 (by rfl) ⟨3731507, by rfl⟩ : syracuseStep 4975343 = 7463015) B7463015
theorem B1863119 : Blo 774336 1863119 := bstep (se 1 (by rfl) ⟨1397339, by rfl⟩ : syracuseStep 1863119 = 2794679) B2794679
theorem B2616839 : Blo 774336 2616839 := bstep (se 1 (by rfl) ⟨1962629, by rfl⟩ : syracuseStep 2616839 = 3925259) B3925259
theorem B23359013 : Blo 774336 23359013 := bstep (se 4 (by rfl) ⟨2189907, by rfl⟩ : syracuseStep 23359013 = 4379815) B4379815
theorem B1994665 : Blo 774336 1994665 := bstep (se 2 (by rfl) ⟨747999, by rfl⟩ : syracuseStep 1994665 = 1495999) B1495999
theorem B1307515 : Blo 774336 1307515 := bstep (se 1 (by rfl) ⟨980636, by rfl⟩ : syracuseStep 1307515 = 1961273) B1961273
theorem B2946239 : Blo 774336 2946239 := bstep (se 1 (by rfl) ⟨2209679, by rfl⟩ : syracuseStep 2946239 = 4419359) B4419359
theorem B980191 : Blo 774336 980191 := bstep (se 1 (by rfl) ⟨735143, by rfl⟩ : syracuseStep 980191 = 1470287) B1470287
theorem B2356553 : Blo 774336 2356553 := bstep (se 2 (by rfl) ⟨883707, by rfl⟩ : syracuseStep 2356553 = 1767415) B1767415
theorem B2618783 : Blo 774336 2618783 := bstep (se 1 (by rfl) ⟨1964087, by rfl⟩ : syracuseStep 2618783 = 3928175) B3928175
theorem B1243387 : Blo 774336 1243387 := bstep (se 1 (by rfl) ⟨932540, by rfl⟩ : syracuseStep 1243387 = 1865081) B1865081
theorem B1964351 : Blo 774336 1964351 := bstep (se 1 (by rfl) ⟨1473263, by rfl⟩ : syracuseStep 1964351 = 2946527) B2946527
theorem B2488927 : Blo 774336 2488927 := bstep (se 1 (by rfl) ⟨1866695, by rfl⟩ : syracuseStep 2488927 = 3733391) B3733391
theorem B248117903 : Blo 774336 248117903 := bstep (se 1 (by rfl) ⟨186088427, by rfl⟩ : syracuseStep 248117903 = 372176855) B372176855
theorem B1309871 : Blo 774336 1309871 := bstep (se 1 (by rfl) ⟨982403, by rfl⟩ : syracuseStep 1309871 = 1964807) B1964807
theorem B12582803 : Blo 774336 12582803 := bstep (se 1 (by rfl) ⟨9437102, by rfl⟩ : syracuseStep 12582803 = 18874205) B18874205
theorem B3735659 : Blo 774336 3735659 := bstep (se 1 (by rfl) ⟨2801744, by rfl⟩ : syracuseStep 3735659 = 5603489) B5603489
theorem B1474843 : Blo 774336 1474843 := bstep (se 1 (by rfl) ⟨1106132, by rfl⟩ : syracuseStep 1474843 = 2212265) B2212265
theorem B2949929 : Blo 774336 2949929 := bstep (se 2 (by rfl) ⟨1106223, by rfl⟩ : syracuseStep 2949929 = 2212447) B2212447
theorem B1246175 : Blo 774336 1246175 := bstep (se 1 (by rfl) ⟨934631, by rfl⟩ : syracuseStep 1246175 = 1869263) B1869263
theorem B2982881 : Blo 774336 2982881 := bstep (se 2 (by rfl) ⟨1118580, by rfl⟩ : syracuseStep 2982881 = 2237161) B2237161
theorem B1311727 : Blo 774336 1311727 := bstep (se 1 (by rfl) ⟨983795, by rfl⟩ : syracuseStep 1311727 = 1967591) B1967591
theorem B9962675 : Blo 774336 9962675 := bstep (se 1 (by rfl) ⟨7472006, by rfl⟩ : syracuseStep 9962675 = 14944013) B14944013
theorem B26936801 : Blo 774336 26936801 := bstep (se 2 (by rfl) ⟨10101300, by rfl⟩ : syracuseStep 26936801 = 20202601) B20202601
theorem B3737447 : Blo 774336 3737447 := bstep (se 1 (by rfl) ⟨2803085, by rfl⟩ : syracuseStep 3737447 = 5606171) B5606171
theorem B23923025 : Blo 774336 23923025 := bstep (se 2 (by rfl) ⟨8971134, by rfl⟩ : syracuseStep 23923025 = 17942269) B17942269
theorem B4196735 : Blo 774336 4196735 := bstep (se 1 (by rfl) ⟨3147551, by rfl⟩ : syracuseStep 4196735 = 6295103) B6295103
theorem B3312521 : Blo 774336 3312521 := bstep (se 2 (by rfl) ⟨1242195, by rfl⟩ : syracuseStep 3312521 = 2484391) B2484391
theorem B2952359 : Blo 774336 2952359 := bstep (se 1 (by rfl) ⟨2214269, by rfl⟩ : syracuseStep 2952359 = 4428539) B4428539
theorem B7081627 : Blo 774336 7081627 := bstep (se 1 (by rfl) ⟨5311220, by rfl⟩ : syracuseStep 7081627 = 10622441) B10622441
theorem B22744759 : Blo 774336 22744759 := bstep (se 1 (by rfl) ⟨17058569, by rfl⟩ : syracuseStep 22744759 = 34117139) B34117139
theorem B2625263 : Blo 774336 2625263 := bstep (se 1 (by rfl) ⟨1968947, by rfl⟩ : syracuseStep 2625263 = 3937895) B3937895
theorem B3543335 : Blo 774336 3543335 := bstep (se 1 (by rfl) ⟨2657501, by rfl⟩ : syracuseStep 3543335 = 5315003) B5315003
theorem B3937409 : Blo 774336 3937409 := bstep (se 2 (by rfl) ⟨1476528, by rfl⟩ : syracuseStep 3937409 = 2953057) B2953057
theorem B2659553 : Blo 774336 2659553 := bstep (se 2 (by rfl) ⟨997332, by rfl⟩ : syracuseStep 2659553 = 1994665) B1994665
theorem B61281785 : Blo 774336 61281785 := bstep (se 2 (by rfl) ⟨22980669, by rfl⟩ : syracuseStep 61281785 = 45961339) B45961339
theorem B2693287 : Blo 774336 2693287 := bstep (se 1 (by rfl) ⟨2019965, by rfl⟩ : syracuseStep 2693287 = 4039931) B4039931
theorem B4430315 : Blo 774336 4430315 := bstep (se 1 (by rfl) ⟨3322736, by rfl⟩ : syracuseStep 4430315 = 6645473) B6645473
theorem B1743353 : Blo 774336 1743353 := bstep (se 2 (by rfl) ⟨653757, by rfl⟩ : syracuseStep 1743353 = 1307515) B1307515
theorem B1743443 : Blo 774336 1743443 := bstep (se 1 (by rfl) ⟨1307582, by rfl⟩ : syracuseStep 1743443 = 2615165) B2615165
theorem B2366567 : Blo 774336 2366567 := bstep (se 1 (by rfl) ⟨1774925, by rfl⟩ : syracuseStep 2366567 = 3549851) B3549851
theorem B3316895 : Blo 774336 3316895 := bstep (se 1 (by rfl) ⟨2487671, by rfl⟩ : syracuseStep 3316895 = 4975343) B4975343
theorem B3939515 : Blo 774336 3939515 := bstep (se 1 (by rfl) ⟨2954636, by rfl⟩ : syracuseStep 3939515 = 5909273) B5909273
theorem B1744559 : Blo 774336 1744559 := bstep (se 1 (by rfl) ⟨1308419, by rfl⟩ : syracuseStep 1744559 = 2616839) B2616839
theorem B15572675 : Blo 774336 15572675 := bstep (se 1 (by rfl) ⟨11679506, by rfl⟩ : syracuseStep 15572675 = 23359013) B23359013
theorem B7446941 : Blo 774336 7446941 := bstep (se 3 (by rfl) ⟨1396301, by rfl⟩ : syracuseStep 7446941 = 2792603) B2792603
theorem B3318569 : Blo 774336 3318569 := bstep (se 2 (by rfl) ⟨1244463, by rfl⟩ : syracuseStep 3318569 = 2488927) B2488927
theorem B5907329 : Blo 774336 5907329 := bstep (se 2 (by rfl) ⟨2215248, by rfl⟩ : syracuseStep 5907329 = 4430497) B4430497
theorem B1745855 : Blo 774336 1745855 := bstep (se 1 (by rfl) ⟨1309391, by rfl⟩ : syracuseStep 1745855 = 2618783) B2618783
theorem B16754849 : Blo 774336 16754849 := bstep (se 2 (by rfl) ⟨6283068, by rfl⟩ : syracuseStep 16754849 = 12566137) B12566137
theorem B1749023 : Blo 774336 1749023 := bstep (se 1 (by rfl) ⟨1311767, by rfl⟩ : syracuseStep 1749023 = 2623535) B2623535
theorem B3322943 : Blo 774336 3322943 := bstep (se 1 (by rfl) ⟨2492207, by rfl⟩ : syracuseStep 3322943 = 4984415) B4984415
theorem B1162025 : Blo 774336 1162025 := bstep (se 2 (by rfl) ⟨435759, by rfl⟩ : syracuseStep 1162025 = 871519) B871519
theorem B4963295 : Blo 774336 4963295 := bstep (se 1 (by rfl) ⟨3722471, by rfl⟩ : syracuseStep 4963295 = 7444943) B7444943
theorem B8831105 : Blo 774336 8831105 := bstep (se 2 (by rfl) ⟨3311664, by rfl⟩ : syracuseStep 8831105 = 6623329) B6623329
theorem B1163561 : Blo 774336 1163561 := bstep (se 2 (by rfl) ⟨436335, by rfl⟩ : syracuseStep 1163561 = 872671) B872671
theorem B1164191 : Blo 774336 1164191 := bstep (se 1 (by rfl) ⟨873143, by rfl⟩ : syracuseStep 1164191 = 1746287) B1746287
theorem B22431239 : Blo 774336 22431239 := bstep (se 1 (by rfl) ⟨16823429, by rfl⟩ : syracuseStep 22431239 = 33646859) B33646859
theorem B1165055 : Blo 774336 1165055 := bstep (se 1 (by rfl) ⟨873791, by rfl⟩ : syracuseStep 1165055 = 1747583) B1747583
theorem B1657849 : Blo 774336 1657849 := bstep (se 2 (by rfl) ⟨621693, by rfl⟩ : syracuseStep 1657849 = 1243387) B1243387
theorem B1166441 : Blo 774336 1166441 := bstep (se 2 (by rfl) ⟨437415, by rfl⟩ : syracuseStep 1166441 = 874831) B874831
theorem B25218539 : Blo 774336 25218539 := bstep (se 1 (by rfl) ⟨18913904, by rfl⟩ : syracuseStep 25218539 = 37827809) B37827809
theorem B4968317 : Blo 774336 4968317 := bstep (se 3 (by rfl) ⟨931559, by rfl⟩ : syracuseStep 4968317 = 1863119) B1863119
theorem B774367 : Blo 774336 774367 := bstep (se 1 (by rfl) ⟨580775, by rfl⟩ : syracuseStep 774367 = 1161551) B1161551
theorem B774395 : Blo 774336 774395 := bstep (se 1 (by rfl) ⟨580796, by rfl⟩ : syracuseStep 774395 = 1161593) B1161593
theorem B5886431 : Blo 774336 5886431 := bstep (se 1 (by rfl) ⟨4414823, by rfl⟩ : syracuseStep 5886431 = 8829647) B8829647
theorem B774911 : Blo 774336 774911 := bstep (se 1 (by rfl) ⟨581183, by rfl⟩ : syracuseStep 774911 = 1162367) B1162367
theorem B873247 : Blo 774336 873247 := bstep (se 1 (by rfl) ⟨654935, by rfl⟩ : syracuseStep 873247 = 1309871) B1309871
theorem B774983 : Blo 774336 774983 := bstep (se 1 (by rfl) ⟨581237, by rfl⟩ : syracuseStep 774983 = 1162475) B1162475
theorem B775015 : Blo 774336 775015 := bstep (se 1 (by rfl) ⟨581261, by rfl⟩ : syracuseStep 775015 = 1162523) B1162523
theorem B31839713 : Blo 774336 31839713 := bstep (se 2 (by rfl) ⟨11939892, by rfl⟩ : syracuseStep 31839713 = 23879785) B23879785
theorem B776047 : Blo 774336 776047 := bstep (se 1 (by rfl) ⟨582035, by rfl⟩ : syracuseStep 776047 = 1164071) B1164071
theorem B7460747 : Blo 774336 7460747 := bstep (se 1 (by rfl) ⟨5595560, by rfl⟩ : syracuseStep 7460747 = 11191121) B11191121
theorem B1104367 : Blo 774336 1104367 := bstep (se 1 (by rfl) ⟨828275, by rfl⟩ : syracuseStep 1104367 = 1656551) B1656551
theorem B776751 : Blo 774336 776751 := bstep (se 1 (by rfl) ⟨582563, by rfl⟩ : syracuseStep 776751 = 1165127) B1165127
theorem B776815 : Blo 774336 776815 := bstep (se 1 (by rfl) ⟨582611, by rfl⟩ : syracuseStep 776815 = 1165223) B1165223
theorem B875263 : Blo 774336 875263 := bstep (se 1 (by rfl) ⟨656447, by rfl⟩ : syracuseStep 875263 = 1312895) B1312895
theorem B777151 : Blo 774336 777151 := bstep (se 1 (by rfl) ⟨582863, by rfl⟩ : syracuseStep 777151 = 1165727) B1165727
theorem B4414459 : Blo 774336 4414459 := bstep (se 1 (by rfl) ⟨3310844, by rfl⟩ : syracuseStep 4414459 = 6621689) B6621689
theorem B777215 : Blo 774336 777215 := bstep (se 1 (by rfl) ⟨582911, by rfl⟩ : syracuseStep 777215 = 1165823) B1165823
theorem B875623 : Blo 774336 875623 := bstep (se 1 (by rfl) ⟨656717, by rfl⟩ : syracuseStep 875623 = 1313435) B1313435
theorem B777371 : Blo 774336 777371 := bstep (se 1 (by rfl) ⟨583028, by rfl⟩ : syracuseStep 777371 = 1166057) B1166057
theorem B777519 : Blo 774336 777519 := bstep (se 1 (by rfl) ⟨583139, by rfl⟩ : syracuseStep 777519 = 1166279) B1166279
theorem B777727 : Blo 774336 777727 := bstep (se 1 (by rfl) ⟨583295, by rfl⟩ : syracuseStep 777727 = 1166591) B1166591
theorem B778267 : Blo 774336 778267 := bstep (se 1 (by rfl) ⟨583700, by rfl⟩ : syracuseStep 778267 = 1167401) B1167401
theorem B5890319 : Blo 774336 5890319 := bstep (se 1 (by rfl) ⟨4417739, by rfl⟩ : syracuseStep 5890319 = 8835479) B8835479
theorem B6284141 : Blo 774336 6284141 := bstep (se 3 (by rfl) ⟨1178276, by rfl⟩ : syracuseStep 6284141 = 2356553) B2356553
theorem B1960159 : Blo 774336 1960159 := bstep (se 1 (by rfl) ⟨1470119, by rfl⟩ : syracuseStep 1960159 = 2940239) B2940239
theorem B13429331 : Blo 774336 13429331 := bstep (se 1 (by rfl) ⟨10071998, by rfl⟩ : syracuseStep 13429331 = 20143997) B20143997
theorem B2944295 : Blo 774336 2944295 := bstep (se 1 (by rfl) ⟨2208221, by rfl⟩ : syracuseStep 2944295 = 4416443) B4416443
theorem B5894207 : Blo 774336 5894207 := bstep (se 1 (by rfl) ⟨4420655, by rfl⟩ : syracuseStep 5894207 = 8841311) B8841311
theorem B1306921 : Blo 774336 1306921 := bstep (se 2 (by rfl) ⟨490095, by rfl⟩ : syracuseStep 1306921 = 980191) B980191
theorem B5600315 : Blo 774336 5600315 := bstep (se 1 (by rfl) ⟨4200236, by rfl⟩ : syracuseStep 5600315 = 8400473) B8400473
theorem B4421567 : Blo 774336 4421567 := bstep (se 1 (by rfl) ⟨3316175, by rfl⟩ : syracuseStep 4421567 = 6632351) B6632351
theorem B1964159 : Blo 774336 1964159 := bstep (se 1 (by rfl) ⟨1473119, by rfl⟩ : syracuseStep 1964159 = 2946239) B2946239
theorem B1309567 : Blo 774336 1309567 := bstep (se 1 (by rfl) ⟨982175, by rfl⟩ : syracuseStep 1309567 = 1964351) B1964351
theorem B2685961 : Blo 774336 2685961 := bstep (se 2 (by rfl) ⟨1007235, by rfl⟩ : syracuseStep 2685961 = 2014471) B2014471
theorem B165411935 : Blo 774336 165411935 := bstep (se 1 (by rfl) ⟨124058951, by rfl⟩ : syracuseStep 165411935 = 248117903) B248117903
theorem B8388535 : Blo 774336 8388535 := bstep (se 1 (by rfl) ⟨6291401, by rfl⟩ : syracuseStep 8388535 = 12582803) B12582803
theorem B2490439 : Blo 774336 2490439 := bstep (se 1 (by rfl) ⟨1867829, by rfl⟩ : syracuseStep 2490439 = 3735659) B3735659
theorem B1966457 : Blo 774336 1966457 := bstep (se 2 (by rfl) ⟨737421, by rfl⟩ : syracuseStep 1966457 = 1474843) B1474843
theorem B1966619 : Blo 774336 1966619 := bstep (se 1 (by rfl) ⟨1474964, by rfl⟩ : syracuseStep 1966619 = 2949929) B2949929
theorem B17957867 : Blo 774336 17957867 := bstep (se 1 (by rfl) ⟨13468400, by rfl⟩ : syracuseStep 17957867 = 26936801) B26936801
theorem B2491631 : Blo 774336 2491631 := bstep (se 1 (by rfl) ⟨1868723, by rfl⟩ : syracuseStep 2491631 = 3737447) B3737447
theorem B1968239 : Blo 774336 1968239 := bstep (se 1 (by rfl) ⟨1476179, by rfl⟩ : syracuseStep 1968239 = 2952359) B2952359
theorem B16812359 : Blo 774336 16812359 := bstep (se 1 (by rfl) ⟨12609269, by rfl⟩ : syracuseStep 16812359 = 25218539) B25218539
theorem B2362223 : Blo 774336 2362223 := bstep (se 1 (by rfl) ⟨1771667, by rfl⟩ : syracuseStep 2362223 = 3543335) B3543335
theorem B2624939 : Blo 774336 2624939 := bstep (se 1 (by rfl) ⟨1968704, by rfl⟩ : syracuseStep 2624939 = 3937409) B3937409
theorem B1773035 : Blo 774336 1773035 := bstep (se 1 (by rfl) ⟨1329776, by rfl⟩ : syracuseStep 1773035 = 2659553) B2659553
theorem B163418093 : Blo 774336 163418093 := bstep (se 3 (by rfl) ⟨30640892, by rfl⟩ : syracuseStep 163418093 = 61281785) B61281785
theorem B2953543 : Blo 774336 2953543 := bstep (se 1 (by rfl) ⟨2215157, by rfl⟩ : syracuseStep 2953543 = 4430315) B4430315
theorem B1577711 : Blo 774336 1577711 := bstep (se 1 (by rfl) ⟨1183283, by rfl⟩ : syracuseStep 1577711 = 2366567) B2366567
theorem B2626343 : Blo 774336 2626343 := bstep (se 1 (by rfl) ⟨1969757, by rfl⟩ : syracuseStep 2626343 = 3939515) B3939515
theorem B9442169 : Blo 774336 9442169 := bstep (se 2 (by rfl) ⟨3540813, by rfl⟩ : syracuseStep 9442169 = 7081627) B7081627
theorem B1742561 : Blo 774336 1742561 := bstep (se 2 (by rfl) ⟨653460, by rfl⟩ : syracuseStep 1742561 = 1306921) B1306921
theorem B3938219 : Blo 774336 3938219 := bstep (se 1 (by rfl) ⟨2953664, by rfl⟩ : syracuseStep 3938219 = 5907329) B5907329
theorem B8952887 : Blo 774336 8952887 := bstep (se 1 (by rfl) ⟨6714665, by rfl⟩ : syracuseStep 8952887 = 13429331) B13429331
theorem B1746089 : Blo 774336 1746089 := bstep (se 2 (by rfl) ⟨654783, by rfl⟩ : syracuseStep 1746089 = 1309567) B1309567
theorem B3581281 : Blo 774336 3581281 := bstep (se 2 (by rfl) ⟨1342980, by rfl⟩ : syracuseStep 3581281 = 2685961) B2685961
theorem B41527133 : Blo 774336 41527133 := bstep (se 3 (by rfl) ⟨7786337, by rfl⟩ : syracuseStep 41527133 = 15572675) B15572675
theorem B110274623 : Blo 774336 110274623 := bstep (se 1 (by rfl) ⟨82705967, by rfl⟩ : syracuseStep 110274623 = 165411935) B165411935
theorem B13248845 : Blo 774336 13248845 := bstep (se 3 (by rfl) ⟨2484158, by rfl⟩ : syracuseStep 13248845 = 4968317) B4968317
theorem B11184713 : Blo 774336 11184713 := bstep (se 2 (by rfl) ⟨4194267, by rfl⟩ : syracuseStep 11184713 = 8388535) B8388535
theorem B830783 : Blo 774336 830783 := bstep (se 1 (by rfl) ⟨623087, by rfl⟩ : syracuseStep 830783 = 1246175) B1246175
theorem B14954159 : Blo 774336 14954159 := bstep (se 1 (by rfl) ⟨11215619, by rfl⟩ : syracuseStep 14954159 = 22431239) B22431239
theorem B1748969 : Blo 774336 1748969 := bstep (se 2 (by rfl) ⟨655863, by rfl⟩ : syracuseStep 1748969 = 1311727) B1311727
theorem B2797823 : Blo 774336 2797823 := bstep (se 1 (by rfl) ⟨2098367, by rfl⟩ : syracuseStep 2797823 = 4196735) B4196735
theorem B2208347 : Blo 774336 2208347 := bstep (se 1 (by rfl) ⟨1656260, by rfl⟩ : syracuseStep 2208347 = 3312521) B3312521
theorem B1750175 : Blo 774336 1750175 := bstep (se 1 (by rfl) ⟨1312631, by rfl⟩ : syracuseStep 1750175 = 2625263) B2625263
theorem B2210465 : Blo 774336 2210465 := bstep (se 2 (by rfl) ⟨828924, by rfl⟩ : syracuseStep 2210465 = 1657849) B1657849
theorem B1162235 : Blo 774336 1162235 := bstep (se 1 (by rfl) ⟨871676, by rfl⟩ : syracuseStep 1162235 = 1743353) B1743353
theorem B1162295 : Blo 774336 1162295 := bstep (se 1 (by rfl) ⟨871721, by rfl⟩ : syracuseStep 1162295 = 1743443) B1743443
theorem B2211263 : Blo 774336 2211263 := bstep (se 1 (by rfl) ⟨1658447, by rfl⟩ : syracuseStep 2211263 = 3316895) B3316895
theorem B30326345 : Blo 774336 30326345 := bstep (se 2 (by rfl) ⟨11372379, by rfl⟩ : syracuseStep 30326345 = 22744759) B22744759
theorem B1163039 : Blo 774336 1163039 := bstep (se 1 (by rfl) ⟨872279, by rfl⟩ : syracuseStep 1163039 = 1744559) B1744559
theorem B4964627 : Blo 774336 4964627 := bstep (se 1 (by rfl) ⟨3723470, by rfl⟩ : syracuseStep 4964627 = 7446941) B7446941
theorem B2212379 : Blo 774336 2212379 := bstep (se 1 (by rfl) ⟨1659284, by rfl⟩ : syracuseStep 2212379 = 3318569) B3318569
theorem B1163903 : Blo 774336 1163903 := bstep (se 1 (by rfl) ⟨872927, by rfl⟩ : syracuseStep 1163903 = 1745855) B1745855
theorem B1164329 : Blo 774336 1164329 := bstep (se 2 (by rfl) ⟨436623, by rfl⟩ : syracuseStep 1164329 = 873247) B873247
theorem B1166015 : Blo 774336 1166015 := bstep (se 1 (by rfl) ⟨874511, by rfl⟩ : syracuseStep 1166015 = 1749023) B1749023
theorem B3591049 : Blo 774336 3591049 := bstep (se 2 (by rfl) ⟨1346643, by rfl⟩ : syracuseStep 3591049 = 2693287) B2693287
theorem B2215295 : Blo 774336 2215295 := bstep (se 1 (by rfl) ⟨1661471, by rfl⟩ : syracuseStep 2215295 = 3322943) B3322943
theorem B1167017 : Blo 774336 1167017 := bstep (se 2 (by rfl) ⟨437631, by rfl⟩ : syracuseStep 1167017 = 875263) B875263
theorem B5885945 : Blo 774336 5885945 := bstep (se 2 (by rfl) ⟨2207229, by rfl⟩ : syracuseStep 5885945 = 4414459) B4414459
theorem B1167497 : Blo 774336 1167497 := bstep (se 2 (by rfl) ⟨437811, by rfl⟩ : syracuseStep 1167497 = 875623) B875623
theorem B774683 : Blo 774336 774683 := bstep (se 1 (by rfl) ⟨581012, by rfl⟩ : syracuseStep 774683 = 1162025) B1162025
theorem B5887403 : Blo 774336 5887403 := bstep (se 1 (by rfl) ⟨4415552, by rfl⟩ : syracuseStep 5887403 = 8831105) B8831105
theorem B775707 : Blo 774336 775707 := bstep (se 1 (by rfl) ⟨581780, by rfl⟩ : syracuseStep 775707 = 1163561) B1163561
theorem B776127 : Blo 774336 776127 := bstep (se 1 (by rfl) ⟨582095, by rfl⟩ : syracuseStep 776127 = 1164191) B1164191
theorem B1988587 : Blo 774336 1988587 := bstep (se 1 (by rfl) ⟨1491440, by rfl⟩ : syracuseStep 1988587 = 2982881) B2982881
theorem B6641783 : Blo 774336 6641783 := bstep (se 1 (by rfl) ⟨4981337, by rfl⟩ : syracuseStep 6641783 = 9962675) B9962675
theorem B776703 : Blo 774336 776703 := bstep (se 1 (by rfl) ⟨582527, by rfl⟩ : syracuseStep 776703 = 1165055) B1165055
theorem B15948683 : Blo 774336 15948683 := bstep (se 1 (by rfl) ⟨11961512, by rfl⟩ : syracuseStep 15948683 = 23923025) B23923025
theorem B777627 : Blo 774336 777627 := bstep (se 1 (by rfl) ⟨583220, by rfl⟩ : syracuseStep 777627 = 1166441) B1166441
theorem B2613545 : Blo 774336 2613545 := bstep (se 2 (by rfl) ⟨980079, by rfl⟩ : syracuseStep 2613545 = 1960159) B1960159
theorem B3924287 : Blo 774336 3924287 := bstep (se 1 (by rfl) ⟨2943215, by rfl⟩ : syracuseStep 3924287 = 5886431) B5886431
theorem B21226475 : Blo 774336 21226475 := bstep (se 1 (by rfl) ⟨15919856, by rfl⟩ : syracuseStep 21226475 = 31839713) B31839713
theorem B4973831 : Blo 774336 4973831 := bstep (se 1 (by rfl) ⟨3730373, by rfl⟩ : syracuseStep 4973831 = 7460747) B7460747
theorem B3926879 : Blo 774336 3926879 := bstep (se 1 (by rfl) ⟨2945159, by rfl⟩ : syracuseStep 3926879 = 5890319) B5890319
theorem B4189427 : Blo 774336 4189427 := bstep (se 1 (by rfl) ⟨3142070, by rfl⟩ : syracuseStep 4189427 = 6284141) B6284141
theorem B11169899 : Blo 774336 11169899 := bstep (se 1 (by rfl) ⟨8377424, by rfl⟩ : syracuseStep 11169899 = 16754849) B16754849
theorem B1962863 : Blo 774336 1962863 := bstep (se 1 (by rfl) ⟨1472147, by rfl⟩ : syracuseStep 1962863 = 2944295) B2944295
theorem B3929471 : Blo 774336 3929471 := bstep (se 1 (by rfl) ⟨2947103, by rfl⟩ : syracuseStep 3929471 = 5894207) B5894207
theorem B1472489 : Blo 774336 1472489 := bstep (se 2 (by rfl) ⟨552183, by rfl⟩ : syracuseStep 1472489 = 1104367) B1104367
theorem B3733543 : Blo 774336 3733543 := bstep (se 1 (by rfl) ⟨2800157, by rfl⟩ : syracuseStep 3733543 = 5600315) B5600315
theorem B2947711 : Blo 774336 2947711 := bstep (se 1 (by rfl) ⟨2210783, by rfl⟩ : syracuseStep 2947711 = 4421567) B4421567
theorem B1309439 : Blo 774336 1309439 := bstep (se 1 (by rfl) ⟨982079, by rfl⟩ : syracuseStep 1309439 = 1964159) B1964159
theorem B3308863 : Blo 774336 3308863 := bstep (se 1 (by rfl) ⟨2481647, by rfl⟩ : syracuseStep 3308863 = 4963295) B4963295
theorem B3309751 : Blo 774336 3309751 := bstep (se 1 (by rfl) ⟨2482313, by rfl⟩ : syracuseStep 3309751 = 4964627) B4964627
theorem B1310971 : Blo 774336 1310971 := bstep (se 1 (by rfl) ⟨983228, by rfl⟩ : syracuseStep 1310971 = 1966457) B1966457
theorem B1474919 : Blo 774336 1474919 := bstep (se 1 (by rfl) ⟨1106189, by rfl⟩ : syracuseStep 1474919 = 2212379) B2212379
theorem B1311079 : Blo 774336 1311079 := bstep (se 1 (by rfl) ⟨983309, by rfl⟩ : syracuseStep 1311079 = 1966619) B1966619
theorem B1312159 : Blo 774336 1312159 := bstep (se 1 (by rfl) ⟨984119, by rfl⟩ : syracuseStep 1312159 = 1968239) B1968239
theorem B11208239 : Blo 774336 11208239 := bstep (se 1 (by rfl) ⟨8406179, by rfl⟩ : syracuseStep 11208239 = 16812359) B16812359
theorem B1574815 : Blo 774336 1574815 := bstep (se 1 (by rfl) ⟨1181111, by rfl⟩ : syracuseStep 1574815 = 2362223) B2362223
theorem B1476863 : Blo 774336 1476863 := bstep (se 1 (by rfl) ⟨1107647, by rfl⟩ : syracuseStep 1476863 = 2215295) B2215295
theorem B1182023 : Blo 774336 1182023 := bstep (se 1 (by rfl) ⟨886517, by rfl⟩ : syracuseStep 1182023 = 1773035) B1773035
theorem B1051807 : Blo 774336 1051807 := bstep (se 1 (by rfl) ⟨788855, by rfl⟩ : syracuseStep 1051807 = 1577711) B1577711
theorem B6294779 : Blo 774336 6294779 := bstep (se 1 (by rfl) ⟨4721084, by rfl⟩ : syracuseStep 6294779 = 9442169) B9442169
theorem B4788065 : Blo 774336 4788065 := bstep (se 2 (by rfl) ⟨1795524, by rfl⟩ : syracuseStep 4788065 = 3591049) B3591049
theorem B2625479 : Blo 774336 2625479 := bstep (se 1 (by rfl) ⟨1969109, by rfl⟩ : syracuseStep 2625479 = 3938219) B3938219
theorem B4427855 : Blo 774336 4427855 := bstep (se 1 (by rfl) ⟨3320891, by rfl⟩ : syracuseStep 4427855 = 6641783) B6641783
theorem B1742363 : Blo 774336 1742363 := bstep (se 1 (by rfl) ⟨1306772, by rfl⟩ : syracuseStep 1742363 = 2613545) B2613545
theorem B3938057 : Blo 774336 3938057 := bstep (se 2 (by rfl) ⟨1476771, by rfl⟩ : syracuseStep 3938057 = 2953543) B2953543
theorem B3315887 : Blo 774336 3315887 := bstep (se 1 (by rfl) ⟨2486915, by rfl⟩ : syracuseStep 3315887 = 4973831) B4973831
theorem B2792951 : Blo 774336 2792951 := bstep (se 1 (by rfl) ⟨2094713, by rfl⟩ : syracuseStep 2792951 = 4189427) B4189427
theorem B9969439 : Blo 774336 9969439 := bstep (se 1 (by rfl) ⟨7477079, by rfl⟩ : syracuseStep 9969439 = 14954159) B14954159
theorem B7446599 : Blo 774336 7446599 := bstep (se 1 (by rfl) ⟨5584949, by rfl⟩ : syracuseStep 7446599 = 11169899) B11169899
theorem B3320585 : Blo 774336 3320585 := bstep (se 2 (by rfl) ⟨1245219, by rfl⟩ : syracuseStep 3320585 = 2490439) B2490439
theorem B1749959 : Blo 774336 1749959 := bstep (se 1 (by rfl) ⟨1312469, by rfl⟩ : syracuseStep 1749959 = 2624939) B2624939
theorem B56603933 : Blo 774336 56603933 := bstep (se 3 (by rfl) ⟨10613237, by rfl⟩ : syracuseStep 56603933 = 21226475) B21226475
theorem B1750895 : Blo 774336 1750895 := bstep (se 1 (by rfl) ⟨1313171, by rfl⟩ : syracuseStep 1750895 = 2626343) B2626343
theorem B1161707 : Blo 774336 1161707 := bstep (se 1 (by rfl) ⟨871280, by rfl⟩ : syracuseStep 1161707 = 1742561) B1742561
theorem B10632455 : Blo 774336 10632455 := bstep (se 1 (by rfl) ⟨7974341, by rfl⟩ : syracuseStep 10632455 = 15948683) B15948683
theorem B1164059 : Blo 774336 1164059 := bstep (se 1 (by rfl) ⟨873044, by rfl⟩ : syracuseStep 1164059 = 1746089) B1746089
theorem B73516415 : Blo 774336 73516415 := bstep (se 1 (by rfl) ⟨55137311, by rfl⟩ : syracuseStep 73516415 = 110274623) B110274623
theorem B8832563 : Blo 774336 8832563 := bstep (se 1 (by rfl) ⟨6624422, by rfl⟩ : syracuseStep 8832563 = 13248845) B13248845
theorem B7456475 : Blo 774336 7456475 := bstep (se 1 (by rfl) ⟨5592356, by rfl⟩ : syracuseStep 7456475 = 11184713) B11184713
theorem B1165979 : Blo 774336 1165979 := bstep (se 1 (by rfl) ⟨874484, by rfl⟩ : syracuseStep 1165979 = 1748969) B1748969
theorem B23874365 : Blo 774336 23874365 := bstep (se 3 (by rfl) ⟨4476443, by rfl⟩ : syracuseStep 23874365 = 8952887) B8952887
theorem B1166783 : Blo 774336 1166783 := bstep (se 1 (by rfl) ⟨875087, by rfl⟩ : syracuseStep 1166783 = 1750175) B1750175
theorem B2215421 : Blo 774336 2215421 := bstep (se 3 (by rfl) ⟨415391, by rfl⟩ : syracuseStep 2215421 = 830783) B830783
theorem B4411817 : Blo 774336 4411817 := bstep (se 2 (by rfl) ⟨1654431, by rfl⟩ : syracuseStep 4411817 = 3308863) B3308863
theorem B872959 : Blo 774336 872959 := bstep (se 1 (by rfl) ⟨654719, by rfl⟩ : syracuseStep 872959 = 1309439) B1309439
theorem B774823 : Blo 774336 774823 := bstep (se 1 (by rfl) ⟨581117, by rfl⟩ : syracuseStep 774823 = 1162235) B1162235
theorem B774863 : Blo 774336 774863 := bstep (se 1 (by rfl) ⟨581147, by rfl⟩ : syracuseStep 774863 = 1162295) B1162295
theorem B191550581 : Blo 774336 191550581 := bstep (se 5 (by rfl) ⟨8978933, by rfl⟩ : syracuseStep 191550581 = 17957867) B17957867
theorem B775359 : Blo 774336 775359 := bstep (se 1 (by rfl) ⟨581519, by rfl⟩ : syracuseStep 775359 = 1163039) B1163039
theorem B775935 : Blo 774336 775935 := bstep (se 1 (by rfl) ⟨581951, by rfl⟩ : syracuseStep 775935 = 1163903) B1163903
theorem B776219 : Blo 774336 776219 := bstep (se 1 (by rfl) ⟨582164, by rfl⟩ : syracuseStep 776219 = 1164329) B1164329
theorem B1661087 : Blo 774336 1661087 := bstep (se 1 (by rfl) ⟨1245815, by rfl⟩ : syracuseStep 1661087 = 2491631) B2491631
theorem B777343 : Blo 774336 777343 := bstep (se 1 (by rfl) ⟨583007, by rfl⟩ : syracuseStep 777343 = 1166015) B1166015
theorem B4775041 : Blo 774336 4775041 := bstep (se 2 (by rfl) ⟨1790640, by rfl⟩ : syracuseStep 4775041 = 3581281) B3581281
theorem B778011 : Blo 774336 778011 := bstep (se 1 (by rfl) ⟨583508, by rfl⟩ : syracuseStep 778011 = 1167017) B1167017
theorem B108945395 : Blo 774336 108945395 := bstep (se 1 (by rfl) ⟨81709046, by rfl⟩ : syracuseStep 108945395 = 163418093) B163418093
theorem B3923963 : Blo 774336 3923963 := bstep (se 1 (by rfl) ⟨2942972, by rfl⟩ : syracuseStep 3923963 = 5885945) B5885945
theorem B778331 : Blo 774336 778331 := bstep (se 1 (by rfl) ⟨583748, by rfl⟩ : syracuseStep 778331 = 1167497) B1167497
theorem B3924935 : Blo 774336 3924935 := bstep (se 1 (by rfl) ⟨2943701, by rfl⟩ : syracuseStep 3924935 = 5887403) B5887403
theorem B2616191 : Blo 774336 2616191 := bstep (se 1 (by rfl) ⟨1962143, by rfl⟩ : syracuseStep 2616191 = 3924287) B3924287
theorem B27684755 : Blo 774336 27684755 := bstep (se 1 (by rfl) ⟨20763566, by rfl⟩ : syracuseStep 27684755 = 41527133) B41527133
theorem B2617919 : Blo 774336 2617919 := bstep (se 1 (by rfl) ⟨1963439, by rfl⟩ : syracuseStep 2617919 = 3926879) B3926879
theorem B2651449 : Blo 774336 2651449 := bstep (se 2 (by rfl) ⟨994293, by rfl⟩ : syracuseStep 2651449 = 1988587) B1988587
theorem B4978057 : Blo 774336 4978057 := bstep (se 2 (by rfl) ⟨1866771, by rfl⟩ : syracuseStep 4978057 = 3733543) B3733543
theorem B1865215 : Blo 774336 1865215 := bstep (se 1 (by rfl) ⟨1398911, by rfl⟩ : syracuseStep 1865215 = 2797823) B2797823
theorem B1472231 : Blo 774336 1472231 := bstep (se 1 (by rfl) ⟨1104173, by rfl⟩ : syracuseStep 1472231 = 2208347) B2208347
theorem B1308575 : Blo 774336 1308575 := bstep (se 1 (by rfl) ⟨981431, by rfl⟩ : syracuseStep 1308575 = 1962863) B1962863
theorem B3930281 : Blo 774336 3930281 := bstep (se 2 (by rfl) ⟨1473855, by rfl⟩ : syracuseStep 3930281 = 2947711) B2947711
theorem B2619647 : Blo 774336 2619647 := bstep (se 1 (by rfl) ⟨1964735, by rfl⟩ : syracuseStep 2619647 = 3929471) B3929471
theorem B981659 : Blo 774336 981659 := bstep (se 1 (by rfl) ⟨736244, by rfl⟩ : syracuseStep 981659 = 1472489) B1472489
theorem B1473643 : Blo 774336 1473643 := bstep (se 1 (by rfl) ⟨1105232, by rfl⟩ : syracuseStep 1473643 = 2210465) B2210465
theorem B1474175 : Blo 774336 1474175 := bstep (se 1 (by rfl) ⟨1105631, by rfl⟩ : syracuseStep 1474175 = 2211263) B2211263
theorem B20217563 : Blo 774336 20217563 := bstep (se 1 (by rfl) ⟨15163172, by rfl⟩ : syracuseStep 20217563 = 30326345) B30326345
theorem B983279 : Blo 774336 983279 := bstep (se 1 (by rfl) ⟨737459, by rfl⟩ : syracuseStep 983279 = 1474919) B1474919
theorem B7472159 : Blo 774336 7472159 := bstep (se 1 (by rfl) ⟨5604119, by rfl⟩ : syracuseStep 7472159 = 11208239) B11208239
theorem B984575 : Blo 774336 984575 := bstep (se 1 (by rfl) ⟨738431, by rfl⟩ : syracuseStep 984575 = 1476863) B1476863
theorem B788015 : Blo 774336 788015 := bstep (se 1 (by rfl) ⟨591011, by rfl⟩ : syracuseStep 788015 = 1182023) B1182023
theorem B4196519 : Blo 774336 4196519 := bstep (se 1 (by rfl) ⟨3147389, by rfl⟩ : syracuseStep 4196519 = 6294779) B6294779
theorem B1476947 : Blo 774336 1476947 := bstep (se 1 (by rfl) ⟨1107710, by rfl⟩ : syracuseStep 1476947 = 2215421) B2215421
theorem B2099753 : Blo 774336 2099753 := bstep (se 2 (by rfl) ⟨787407, by rfl⟩ : syracuseStep 2099753 = 1574815) B1574815
theorem B2951903 : Blo 774336 2951903 := bstep (se 1 (by rfl) ⟨2213927, by rfl⟩ : syracuseStep 2951903 = 4427855) B4427855
theorem B127700387 : Blo 774336 127700387 := bstep (se 1 (by rfl) ⟨95775290, by rfl⟩ : syracuseStep 127700387 = 191550581) B191550581
theorem B2625371 : Blo 774336 2625371 := bstep (se 1 (by rfl) ⟨1969028, by rfl⟩ : syracuseStep 2625371 = 3938057) B3938057
theorem B4429565 : Blo 774336 4429565 := bstep (se 3 (by rfl) ⟨830543, by rfl⟩ : syracuseStep 4429565 = 1661087) B1661087
theorem B1744127 : Blo 774336 1744127 := bstep (se 1 (by rfl) ⟨1308095, by rfl⟩ : syracuseStep 1744127 = 2616191) B2616191
theorem B18456503 : Blo 774336 18456503 := bstep (se 1 (by rfl) ⟨13842377, by rfl⟩ : syracuseStep 18456503 = 27684755) B27684755
theorem B1745279 : Blo 774336 1745279 := bstep (se 1 (by rfl) ⟨1308959, by rfl⟩ : syracuseStep 1745279 = 2617919) B2617919
theorem B1746431 : Blo 774336 1746431 := bstep (se 1 (by rfl) ⟨1309823, by rfl⟩ : syracuseStep 1746431 = 2619647) B2619647
theorem B6366721 : Blo 774336 6366721 := bstep (se 2 (by rfl) ⟨2387520, by rfl⟩ : syracuseStep 6366721 = 4775041) B4775041
theorem B7088303 : Blo 774336 7088303 := bstep (se 1 (by rfl) ⟨5316227, by rfl⟩ : syracuseStep 7088303 = 10632455) B10632455
theorem B13478375 : Blo 774336 13478375 := bstep (se 1 (by rfl) ⟨10108781, by rfl⟩ : syracuseStep 13478375 = 20217563) B20217563
theorem B1747961 : Blo 774336 1747961 := bstep (se 2 (by rfl) ⟨655485, by rfl⟩ : syracuseStep 1747961 = 1310971) B1310971
theorem B1748105 : Blo 774336 1748105 := bstep (se 2 (by rfl) ⟨655539, by rfl⟩ : syracuseStep 1748105 = 1311079) B1311079
theorem B1749545 : Blo 774336 1749545 := bstep (se 2 (by rfl) ⟨656079, by rfl⟩ : syracuseStep 1749545 = 1312159) B1312159
theorem B3192043 : Blo 774336 3192043 := bstep (se 1 (by rfl) ⟨2394032, by rfl⟩ : syracuseStep 3192043 = 4788065) B4788065
theorem B1750319 : Blo 774336 1750319 := bstep (se 1 (by rfl) ⟨1312739, by rfl⟩ : syracuseStep 1750319 = 2625479) B2625479
theorem B1161575 : Blo 774336 1161575 := bstep (se 1 (by rfl) ⟨871181, by rfl⟩ : syracuseStep 1161575 = 1742363) B1742363
theorem B2210591 : Blo 774336 2210591 := bstep (se 1 (by rfl) ⟨1657943, by rfl⟩ : syracuseStep 2210591 = 3315887) B3315887
theorem B72630263 : Blo 774336 72630263 := bstep (se 1 (by rfl) ⟨54472697, by rfl⟩ : syracuseStep 72630263 = 108945395) B108945395
theorem B4964399 : Blo 774336 4964399 := bstep (se 1 (by rfl) ⟨3723299, by rfl⟩ : syracuseStep 4964399 = 7446599) B7446599
theorem B1163945 : Blo 774336 1163945 := bstep (se 2 (by rfl) ⟨436479, by rfl⟩ : syracuseStep 1163945 = 872959) B872959
theorem B2213723 : Blo 774336 2213723 := bstep (se 1 (by rfl) ⟨1660292, by rfl⟩ : syracuseStep 2213723 = 3320585) B3320585
theorem B6637409 : Blo 774336 6637409 := bstep (se 2 (by rfl) ⟨2489028, by rfl⟩ : syracuseStep 6637409 = 4978057) B4978057
theorem B1166639 : Blo 774336 1166639 := bstep (se 1 (by rfl) ⟨874979, by rfl⟩ : syracuseStep 1166639 = 1749959) B1749959
theorem B37735955 : Blo 774336 37735955 := bstep (se 1 (by rfl) ⟨28301966, by rfl⟩ : syracuseStep 37735955 = 56603933) B56603933
theorem B1167263 : Blo 774336 1167263 := bstep (se 1 (by rfl) ⟨875447, by rfl⟩ : syracuseStep 1167263 = 1750895) B1750895
theorem B872383 : Blo 774336 872383 := bstep (se 1 (by rfl) ⟨654287, by rfl⟩ : syracuseStep 872383 = 1308575) B1308575
theorem B774471 : Blo 774336 774471 := bstep (se 1 (by rfl) ⟨580853, by rfl⟩ : syracuseStep 774471 = 1161707) B1161707
theorem B13292585 : Blo 774336 13292585 := bstep (se 2 (by rfl) ⟨4984719, by rfl⟩ : syracuseStep 13292585 = 9969439) B9969439
theorem B4413001 : Blo 774336 4413001 := bstep (se 2 (by rfl) ⟨1654875, by rfl⟩ : syracuseStep 4413001 = 3309751) B3309751
theorem B776039 : Blo 774336 776039 := bstep (se 1 (by rfl) ⟨582029, by rfl⟩ : syracuseStep 776039 = 1164059) B1164059
theorem B5888375 : Blo 774336 5888375 := bstep (se 1 (by rfl) ⟨4416281, by rfl⟩ : syracuseStep 5888375 = 8832563) B8832563
theorem B4970983 : Blo 774336 4970983 := bstep (se 1 (by rfl) ⟨3728237, by rfl⟩ : syracuseStep 4970983 = 7456475) B7456475
theorem B777319 : Blo 774336 777319 := bstep (se 1 (by rfl) ⟨582989, by rfl⟩ : syracuseStep 777319 = 1165979) B1165979
theorem B777855 : Blo 774336 777855 := bstep (se 1 (by rfl) ⟨583391, by rfl⟩ : syracuseStep 777855 = 1166783) B1166783
theorem B2941211 : Blo 774336 2941211 := bstep (se 1 (by rfl) ⟨2205908, by rfl⟩ : syracuseStep 2941211 = 4411817) B4411817
theorem B196043773 : Blo 774336 196043773 := bstep (se 3 (by rfl) ⟨36758207, by rfl⟩ : syracuseStep 196043773 = 73516415) B73516415
theorem B1402409 : Blo 774336 1402409 := bstep (se 2 (by rfl) ⟨525903, by rfl⟩ : syracuseStep 1402409 = 1051807) B1051807
theorem B1861967 : Blo 774336 1861967 := bstep (se 1 (by rfl) ⟨1396475, by rfl⟩ : syracuseStep 1861967 = 2792951) B2792951
theorem B2615975 : Blo 774336 2615975 := bstep (se 1 (by rfl) ⟨1961981, by rfl⟩ : syracuseStep 2615975 = 3923963) B3923963
theorem B2616623 : Blo 774336 2616623 := bstep (se 1 (by rfl) ⟨1962467, by rfl⟩ : syracuseStep 2616623 = 3924935) B3924935
theorem B2617757 : Blo 774336 2617757 := bstep (se 3 (by rfl) ⟨490829, by rfl⟩ : syracuseStep 2617757 = 981659) B981659
theorem B3535265 : Blo 774336 3535265 := bstep (se 2 (by rfl) ⟨1325724, by rfl⟩ : syracuseStep 3535265 = 2651449) B2651449
theorem B2486953 : Blo 774336 2486953 := bstep (se 2 (by rfl) ⟨932607, by rfl⟩ : syracuseStep 2486953 = 1865215) B1865215
theorem B63664973 : Blo 774336 63664973 := bstep (se 3 (by rfl) ⟨11937182, by rfl⟩ : syracuseStep 63664973 = 23874365) B23874365
theorem B981487 : Blo 774336 981487 := bstep (se 1 (by rfl) ⟨736115, by rfl⟩ : syracuseStep 981487 = 1472231) B1472231
theorem B2620187 : Blo 774336 2620187 := bstep (se 1 (by rfl) ⟨1965140, by rfl⟩ : syracuseStep 2620187 = 3930281) B3930281
theorem B1964857 : Blo 774336 1964857 := bstep (se 2 (by rfl) ⟨736821, by rfl⟩ : syracuseStep 1964857 = 1473643) B1473643
theorem B982783 : Blo 774336 982783 := bstep (se 1 (by rfl) ⟨737087, by rfl⟩ : syracuseStep 982783 = 1474175) B1474175
theorem B3309599 : Blo 774336 3309599 := bstep (se 1 (by rfl) ⟨2482199, by rfl⟩ : syracuseStep 3309599 = 4964399) B4964399
theorem B2622077 : Blo 774336 2622077 := bstep (se 3 (by rfl) ⟨491639, by rfl⟩ : syracuseStep 2622077 = 983279) B983279
theorem B4981439 : Blo 774336 4981439 := bstep (se 1 (by rfl) ⟨3736079, by rfl⟩ : syracuseStep 4981439 = 7472159) B7472159
theorem B1475815 : Blo 774336 1475815 := bstep (se 1 (by rfl) ⟨1106861, by rfl⟩ : syracuseStep 1475815 = 2213723) B2213723
theorem B4424939 : Blo 774336 4424939 := bstep (se 1 (by rfl) ⟨3318704, by rfl⟩ : syracuseStep 4424939 = 6637409) B6637409
theorem B261391697 : Blo 774336 261391697 := bstep (se 2 (by rfl) ⟨98021886, by rfl⟩ : syracuseStep 261391697 = 196043773) B196043773
theorem B984631 : Blo 774336 984631 := bstep (se 1 (by rfl) ⟨738473, by rfl⟩ : syracuseStep 984631 = 1476947) B1476947
theorem B1967935 : Blo 774336 1967935 := bstep (se 1 (by rfl) ⟨1475951, by rfl⟩ : syracuseStep 1967935 = 2951903) B2951903
theorem B8488961 : Blo 774336 8488961 := bstep (se 2 (by rfl) ⟨3183360, by rfl⟩ : syracuseStep 8488961 = 6366721) B6366721
theorem B85133591 : Blo 774336 85133591 := bstep (se 1 (by rfl) ⟨63850193, by rfl⟩ : syracuseStep 85133591 = 127700387) B127700387
theorem B2953043 : Blo 774336 2953043 := bstep (se 1 (by rfl) ⟨2214782, by rfl⟩ : syracuseStep 2953043 = 4429565) B4429565
theorem B2625533 : Blo 774336 2625533 := bstep (se 3 (by rfl) ⟨492287, by rfl⟩ : syracuseStep 2625533 = 984575) B984575
theorem B2101373 : Blo 774336 2101373 := bstep (se 3 (by rfl) ⟨394007, by rfl⟩ : syracuseStep 2101373 = 788015) B788015
theorem B3315937 : Blo 774336 3315937 := bstep (se 2 (by rfl) ⟨1243476, by rfl⟩ : syracuseStep 3315937 = 2486953) B2486953
theorem B4725535 : Blo 774336 4725535 := bstep (se 1 (by rfl) ⟨3544151, by rfl⟩ : syracuseStep 4725535 = 7088303) B7088303
theorem B8985583 : Blo 774336 8985583 := bstep (se 1 (by rfl) ⟨6739187, by rfl⟩ : syracuseStep 8985583 = 13478375) B13478375
theorem B1743983 : Blo 774336 1743983 := bstep (se 1 (by rfl) ⟨1307987, by rfl⟩ : syracuseStep 1743983 = 2615975) B2615975
theorem B1744415 : Blo 774336 1744415 := bstep (se 1 (by rfl) ⟨1308311, by rfl⟩ : syracuseStep 1744415 = 2616623) B2616623
theorem B1745171 : Blo 774336 1745171 := bstep (se 1 (by rfl) ⟨1308878, by rfl⟩ : syracuseStep 1745171 = 2617757) B2617757
theorem B42443315 : Blo 774336 42443315 := bstep (se 1 (by rfl) ⟨31832486, by rfl⟩ : syracuseStep 42443315 = 63664973) B63664973
theorem B6627977 : Blo 774336 6627977 := bstep (se 2 (by rfl) ⟨2485491, by rfl⟩ : syracuseStep 6627977 = 4970983) B4970983
theorem B1746791 : Blo 774336 1746791 := bstep (se 1 (by rfl) ⟨1310093, by rfl⟩ : syracuseStep 1746791 = 2620187) B2620187
theorem B2797679 : Blo 774336 2797679 := bstep (se 1 (by rfl) ⟨2098259, by rfl⟩ : syracuseStep 2797679 = 4196519) B4196519
theorem B1750247 : Blo 774336 1750247 := bstep (se 1 (by rfl) ⟨1312685, by rfl⟩ : syracuseStep 1750247 = 2625371) B2625371
theorem B8861723 : Blo 774336 8861723 := bstep (se 1 (by rfl) ⟨6646292, by rfl⟩ : syracuseStep 8861723 = 13292585) B13292585
theorem B1162751 : Blo 774336 1162751 := bstep (se 1 (by rfl) ⟨872063, by rfl⟩ : syracuseStep 1162751 = 1744127) B1744127
theorem B1163177 : Blo 774336 1163177 := bstep (se 2 (by rfl) ⟨436191, by rfl⟩ : syracuseStep 1163177 = 872383) B872383
theorem B1163519 : Blo 774336 1163519 := bstep (se 1 (by rfl) ⟨872639, by rfl⟩ : syracuseStep 1163519 = 1745279) B1745279
theorem B1164287 : Blo 774336 1164287 := bstep (se 1 (by rfl) ⟨873215, by rfl⟩ : syracuseStep 1164287 = 1746431) B1746431
theorem B934939 : Blo 774336 934939 := bstep (se 1 (by rfl) ⟨701204, by rfl⟩ : syracuseStep 934939 = 1402409) B1402409
theorem B1165307 : Blo 774336 1165307 := bstep (se 1 (by rfl) ⟨873980, by rfl⟩ : syracuseStep 1165307 = 1747961) B1747961
theorem B1165403 : Blo 774336 1165403 := bstep (se 1 (by rfl) ⟨874052, by rfl⟩ : syracuseStep 1165403 = 1748105) B1748105
theorem B5884001 : Blo 774336 5884001 := bstep (se 2 (by rfl) ⟨2206500, by rfl⟩ : syracuseStep 5884001 = 4413001) B4413001
theorem B1166363 : Blo 774336 1166363 := bstep (se 1 (by rfl) ⟨874772, by rfl⟩ : syracuseStep 1166363 = 1749545) B1749545
theorem B1166879 : Blo 774336 1166879 := bstep (se 1 (by rfl) ⟨875159, by rfl⟩ : syracuseStep 1166879 = 1750319) B1750319
theorem B774383 : Blo 774336 774383 := bstep (se 1 (by rfl) ⟨580787, by rfl⟩ : syracuseStep 774383 = 1161575) B1161575
theorem B48420175 : Blo 774336 48420175 := bstep (se 1 (by rfl) ⟨36315131, by rfl⟩ : syracuseStep 48420175 = 72630263) B72630263
theorem B775963 : Blo 774336 775963 := bstep (se 1 (by rfl) ⟨581972, by rfl⟩ : syracuseStep 775963 = 1163945) B1163945
theorem B9427373 : Blo 774336 9427373 := bstep (se 3 (by rfl) ⟨1767632, by rfl⟩ : syracuseStep 9427373 = 3535265) B3535265
theorem B1399835 : Blo 774336 1399835 := bstep (se 1 (by rfl) ⟨1049876, by rfl⟩ : syracuseStep 1399835 = 2099753) B2099753
theorem B777759 : Blo 774336 777759 := bstep (se 1 (by rfl) ⟨583319, by rfl⟩ : syracuseStep 777759 = 1166639) B1166639
theorem B25157303 : Blo 774336 25157303 := bstep (se 1 (by rfl) ⟨18867977, by rfl⟩ : syracuseStep 25157303 = 37735955) B37735955
theorem B778175 : Blo 774336 778175 := bstep (se 1 (by rfl) ⟨583631, by rfl⟩ : syracuseStep 778175 = 1167263) B1167263
theorem B3925583 : Blo 774336 3925583 := bstep (se 1 (by rfl) ⟨2944187, by rfl⟩ : syracuseStep 3925583 = 5888375) B5888375
theorem B1960807 : Blo 774336 1960807 := bstep (se 1 (by rfl) ⟨1470605, by rfl⟩ : syracuseStep 1960807 = 2941211) B2941211
theorem B1241311 : Blo 774336 1241311 := bstep (se 1 (by rfl) ⟨930983, by rfl⟩ : syracuseStep 1241311 = 1861967) B1861967
theorem B4256057 : Blo 774336 4256057 := bstep (se 2 (by rfl) ⟨1596021, by rfl⟩ : syracuseStep 4256057 = 3192043) B3192043
theorem B1308649 : Blo 774336 1308649 := bstep (se 2 (by rfl) ⟨490743, by rfl⟩ : syracuseStep 1308649 = 981487) B981487
theorem B2619809 : Blo 774336 2619809 := bstep (se 2 (by rfl) ⟨982428, by rfl⟩ : syracuseStep 2619809 = 1964857) B1964857
theorem B1473727 : Blo 774336 1473727 := bstep (se 1 (by rfl) ⟨1105295, by rfl⟩ : syracuseStep 1473727 = 2210591) B2210591
theorem B1310377 : Blo 774336 1310377 := bstep (se 2 (by rfl) ⟨491391, by rfl⟩ : syracuseStep 1310377 = 982783) B982783
theorem B49217341 : Blo 774336 49217341 := bstep (se 3 (by rfl) ⟨9228251, by rfl⟩ : syracuseStep 49217341 = 18456503) B18456503
theorem B2949959 : Blo 774336 2949959 := bstep (se 1 (by rfl) ⟨2212469, by rfl⟩ : syracuseStep 2949959 = 4424939) B4424939
theorem B174261131 : Blo 774336 174261131 := bstep (se 1 (by rfl) ⟨130695848, by rfl⟩ : syracuseStep 174261131 = 261391697) B261391697
theorem B1246585 : Blo 774336 1246585 := bstep (se 2 (by rfl) ⟨467469, by rfl⟩ : syracuseStep 1246585 = 934939) B934939
theorem B56755727 : Blo 774336 56755727 := bstep (se 1 (by rfl) ⟨42566795, by rfl⟩ : syracuseStep 56755727 = 85133591) B85133591
theorem B1967753 : Blo 774336 1967753 := bstep (se 2 (by rfl) ⟨737907, by rfl⟩ : syracuseStep 1967753 = 1475815) B1475815
theorem B1312841 : Blo 774336 1312841 := bstep (se 2 (by rfl) ⟨492315, by rfl⟩ : syracuseStep 1312841 = 984631) B984631
theorem B2623913 : Blo 774336 2623913 := bstep (se 2 (by rfl) ⟨983967, by rfl⟩ : syracuseStep 2623913 = 1967935) B1967935
theorem B1968695 : Blo 774336 1968695 := bstep (se 1 (by rfl) ⟨1476521, by rfl⟩ : syracuseStep 1968695 = 2953043) B2953043
theorem B64560233 : Blo 774336 64560233 := bstep (se 2 (by rfl) ⟨24210087, by rfl⟩ : syracuseStep 64560233 = 48420175) B48420175
theorem B1744865 : Blo 774336 1744865 := bstep (se 2 (by rfl) ⟨654324, by rfl⟩ : syracuseStep 1744865 = 1308649) B1308649
theorem B6300713 : Blo 774336 6300713 := bstep (se 2 (by rfl) ⟨2362767, by rfl⟩ : syracuseStep 6300713 = 4725535) B4725535
theorem B5907815 : Blo 774336 5907815 := bstep (se 1 (by rfl) ⟨4430861, by rfl⟩ : syracuseStep 5907815 = 8861723) B8861723
theorem B1746539 : Blo 774336 1746539 := bstep (se 1 (by rfl) ⟨1309904, by rfl⟩ : syracuseStep 1746539 = 2619809) B2619809
theorem B1747169 : Blo 774336 1747169 := bstep (se 2 (by rfl) ⟨655188, by rfl⟩ : syracuseStep 1747169 = 1310377) B1310377
theorem B2206399 : Blo 774336 2206399 := bstep (se 1 (by rfl) ⟨1654799, by rfl⟩ : syracuseStep 2206399 = 3309599) B3309599
theorem B1748051 : Blo 774336 1748051 := bstep (se 1 (by rfl) ⟨1311038, by rfl⟩ : syracuseStep 1748051 = 2622077) B2622077
theorem B13283837 : Blo 774336 13283837 := bstep (se 3 (by rfl) ⟨2490719, by rfl⟩ : syracuseStep 13283837 = 4981439) B4981439
theorem B1750355 : Blo 774336 1750355 := bstep (se 1 (by rfl) ⟨1312766, by rfl⟩ : syracuseStep 1750355 = 2625533) B2625533
theorem B933223 : Blo 774336 933223 := bstep (se 1 (by rfl) ⟨699917, by rfl⟩ : syracuseStep 933223 = 1399835) B1399835
theorem B1162655 : Blo 774336 1162655 := bstep (se 1 (by rfl) ⟨871991, by rfl⟩ : syracuseStep 1162655 = 1743983) B1743983
theorem B1162943 : Blo 774336 1162943 := bstep (se 1 (by rfl) ⟨872207, by rfl⟩ : syracuseStep 1162943 = 1744415) B1744415
theorem B47923109 : Blo 774336 47923109 := bstep (se 4 (by rfl) ⟨4492791, by rfl⟩ : syracuseStep 47923109 = 8985583) B8985583
theorem B1163447 : Blo 774336 1163447 := bstep (se 1 (by rfl) ⟨872585, by rfl⟩ : syracuseStep 1163447 = 1745171) B1745171
theorem B1655081 : Blo 774336 1655081 := bstep (se 2 (by rfl) ⟨620655, by rfl⟩ : syracuseStep 1655081 = 1241311) B1241311
theorem B28295543 : Blo 774336 28295543 := bstep (se 1 (by rfl) ⟨21221657, by rfl⟩ : syracuseStep 28295543 = 42443315) B42443315
theorem B1164527 : Blo 774336 1164527 := bstep (se 1 (by rfl) ⟨873395, by rfl⟩ : syracuseStep 1164527 = 1746791) B1746791
theorem B2837371 : Blo 774336 2837371 := bstep (se 1 (by rfl) ⟨2128028, by rfl⟩ : syracuseStep 2837371 = 4256057) B4256057
theorem B1166831 : Blo 774336 1166831 := bstep (se 1 (by rfl) ⟨875123, by rfl⟩ : syracuseStep 1166831 = 1750247) B1750247
theorem B775167 : Blo 774336 775167 := bstep (se 1 (by rfl) ⟨581375, by rfl⟩ : syracuseStep 775167 = 1162751) B1162751
theorem B65623121 : Blo 774336 65623121 := bstep (se 2 (by rfl) ⟨24608670, by rfl⟩ : syracuseStep 65623121 = 49217341) B49217341
theorem B775451 : Blo 774336 775451 := bstep (se 1 (by rfl) ⟨581588, by rfl⟩ : syracuseStep 775451 = 1163177) B1163177
theorem B775679 : Blo 774336 775679 := bstep (se 1 (by rfl) ⟨581759, by rfl⟩ : syracuseStep 775679 = 1163519) B1163519
theorem B776191 : Blo 774336 776191 := bstep (se 1 (by rfl) ⟨582143, by rfl⟩ : syracuseStep 776191 = 1164287) B1164287
theorem B776871 : Blo 774336 776871 := bstep (se 1 (by rfl) ⟨582653, by rfl⟩ : syracuseStep 776871 = 1165307) B1165307
theorem B5659307 : Blo 774336 5659307 := bstep (se 1 (by rfl) ⟨4244480, by rfl⟩ : syracuseStep 5659307 = 8488961) B8488961
theorem B776935 : Blo 774336 776935 := bstep (se 1 (by rfl) ⟨582701, by rfl⟩ : syracuseStep 776935 = 1165403) B1165403
theorem B3922667 : Blo 774336 3922667 := bstep (se 1 (by rfl) ⟨2942000, by rfl⟩ : syracuseStep 3922667 = 5884001) B5884001
theorem B777575 : Blo 774336 777575 := bstep (se 1 (by rfl) ⟨583181, by rfl⟩ : syracuseStep 777575 = 1166363) B1166363
theorem B777919 : Blo 774336 777919 := bstep (se 1 (by rfl) ⟨583439, by rfl⟩ : syracuseStep 777919 = 1166879) B1166879
theorem B1400915 : Blo 774336 1400915 := bstep (se 1 (by rfl) ⟨1050686, by rfl⟩ : syracuseStep 1400915 = 2101373) B2101373
theorem B2614409 : Blo 774336 2614409 := bstep (se 2 (by rfl) ⟨980403, by rfl⟩ : syracuseStep 2614409 = 1960807) B1960807
theorem B6284915 : Blo 774336 6284915 := bstep (se 1 (by rfl) ⟨4713686, by rfl⟩ : syracuseStep 6284915 = 9427373) B9427373
theorem B16771535 : Blo 774336 16771535 := bstep (se 1 (by rfl) ⟨12578651, by rfl⟩ : syracuseStep 16771535 = 25157303) B25157303
theorem B4418651 : Blo 774336 4418651 := bstep (se 1 (by rfl) ⟨3313988, by rfl⟩ : syracuseStep 4418651 = 6627977) B6627977
theorem B2617055 : Blo 774336 2617055 := bstep (se 1 (by rfl) ⟨1962791, by rfl⟩ : syracuseStep 2617055 = 3925583) B3925583
theorem B1865119 : Blo 774336 1865119 := bstep (se 1 (by rfl) ⟨1398839, by rfl⟩ : syracuseStep 1865119 = 2797679) B2797679
theorem B4421249 : Blo 774336 4421249 := bstep (se 2 (by rfl) ⟨1657968, by rfl⟩ : syracuseStep 4421249 = 3315937) B3315937
theorem B1964969 : Blo 774336 1964969 := bstep (se 2 (by rfl) ⟨736863, by rfl⟩ : syracuseStep 1964969 = 1473727) B1473727
theorem B3735773 : Blo 774336 3735773 := bstep (se 3 (by rfl) ⟨700457, by rfl⟩ : syracuseStep 3735773 = 1400915) B1400915
theorem B1966639 : Blo 774336 1966639 := bstep (se 1 (by rfl) ⟨1474979, by rfl⟩ : syracuseStep 1966639 = 2949959) B2949959
theorem B1311835 : Blo 774336 1311835 := bstep (se 1 (by rfl) ⟨983876, by rfl⟩ : syracuseStep 1311835 = 1967753) B1967753
theorem B1312463 : Blo 774336 1312463 := bstep (se 1 (by rfl) ⟨984347, by rfl⟩ : syracuseStep 1312463 = 1968695) B1968695
theorem B43748747 : Blo 774336 43748747 := bstep (se 1 (by rfl) ⟨32811560, by rfl⟩ : syracuseStep 43748747 = 65623121) B65623121
theorem B3772871 : Blo 774336 3772871 := bstep (se 1 (by rfl) ⟨2829653, by rfl⟩ : syracuseStep 3772871 = 5659307) B5659307
theorem B1742939 : Blo 774336 1742939 := bstep (se 1 (by rfl) ⟨1307204, by rfl⟩ : syracuseStep 1742939 = 2614409) B2614409
theorem B3938543 : Blo 774336 3938543 := bstep (se 1 (by rfl) ⟨2953907, by rfl⟩ : syracuseStep 3938543 = 5907815) B5907815
theorem B11181023 : Blo 774336 11181023 := bstep (se 1 (by rfl) ⟨8385767, by rfl⟩ : syracuseStep 11181023 = 16771535) B16771535
theorem B1744703 : Blo 774336 1744703 := bstep (se 1 (by rfl) ⟨1308527, by rfl⟩ : syracuseStep 1744703 = 2617055) B2617055
theorem B8855891 : Blo 774336 8855891 := bstep (se 1 (by rfl) ⟨6641918, by rfl⟩ : syracuseStep 8855891 = 13283837) B13283837
theorem B116174087 : Blo 774336 116174087 := bstep (se 1 (by rfl) ⟨87130565, by rfl⟩ : syracuseStep 116174087 = 174261131) B174261131
theorem B1749275 : Blo 774336 1749275 := bstep (se 1 (by rfl) ⟨1311956, by rfl⟩ : syracuseStep 1749275 = 2623913) B2623913
theorem B3783161 : Blo 774336 3783161 := bstep (se 2 (by rfl) ⟨1418685, by rfl⟩ : syracuseStep 3783161 = 2837371) B2837371
theorem B43040155 : Blo 774336 43040155 := bstep (se 1 (by rfl) ⟨32280116, by rfl⟩ : syracuseStep 43040155 = 64560233) B64560233
theorem B1163243 : Blo 774336 1163243 := bstep (se 1 (by rfl) ⟨872432, by rfl⟩ : syracuseStep 1163243 = 1744865) B1744865
theorem B1164359 : Blo 774336 1164359 := bstep (se 1 (by rfl) ⟨873269, by rfl⟩ : syracuseStep 1164359 = 1746539) B1746539
theorem B1164779 : Blo 774336 1164779 := bstep (se 1 (by rfl) ⟨873584, by rfl⟩ : syracuseStep 1164779 = 1747169) B1747169
theorem B1165367 : Blo 774336 1165367 := bstep (se 1 (by rfl) ⟨874025, by rfl⟩ : syracuseStep 1165367 = 1748051) B1748051
theorem B1166903 : Blo 774336 1166903 := bstep (se 1 (by rfl) ⟨875177, by rfl⟩ : syracuseStep 1166903 = 1750355) B1750355
theorem B775103 : Blo 774336 775103 := bstep (se 1 (by rfl) ⟨581327, by rfl⟩ : syracuseStep 775103 = 1162655) B1162655
theorem B775295 : Blo 774336 775295 := bstep (se 1 (by rfl) ⟨581471, by rfl⟩ : syracuseStep 775295 = 1162943) B1162943
theorem B775631 : Blo 774336 775631 := bstep (se 1 (by rfl) ⟨581723, by rfl⟩ : syracuseStep 775631 = 1163447) B1163447
theorem B1103387 : Blo 774336 1103387 := bstep (se 1 (by rfl) ⟨827540, by rfl⟩ : syracuseStep 1103387 = 1655081) B1655081
theorem B18863695 : Blo 774336 18863695 := bstep (se 1 (by rfl) ⟨14147771, by rfl⟩ : syracuseStep 18863695 = 28295543) B28295543
theorem B776351 : Blo 774336 776351 := bstep (se 1 (by rfl) ⟨582263, by rfl⟩ : syracuseStep 776351 = 1164527) B1164527
theorem B37837151 : Blo 774336 37837151 := bstep (se 1 (by rfl) ⟨28377863, by rfl⟩ : syracuseStep 37837151 = 56755727) B56755727
theorem B875227 : Blo 774336 875227 := bstep (se 1 (by rfl) ⟨656420, by rfl⟩ : syracuseStep 875227 = 1312841) B1312841
theorem B1662113 : Blo 774336 1662113 := bstep (se 2 (by rfl) ⟨623292, by rfl⟩ : syracuseStep 1662113 = 1246585) B1246585
theorem B777887 : Blo 774336 777887 := bstep (se 1 (by rfl) ⟨583415, by rfl⟩ : syracuseStep 777887 = 1166831) B1166831
theorem B16801901 : Blo 774336 16801901 := bstep (se 3 (by rfl) ⟨3150356, by rfl⟩ : syracuseStep 16801901 = 6300713) B6300713
theorem B2941865 : Blo 774336 2941865 := bstep (se 2 (by rfl) ⟨1103199, by rfl⟩ : syracuseStep 2941865 = 2206399) B2206399
theorem B2615111 : Blo 774336 2615111 := bstep (se 1 (by rfl) ⟨1961333, by rfl⟩ : syracuseStep 2615111 = 3922667) B3922667
theorem B4189943 : Blo 774336 4189943 := bstep (se 1 (by rfl) ⟨3142457, by rfl⟩ : syracuseStep 4189943 = 6284915) B6284915
theorem B2486825 : Blo 774336 2486825 := bstep (se 2 (by rfl) ⟨932559, by rfl⟩ : syracuseStep 2486825 = 1865119) B1865119
theorem B2945767 : Blo 774336 2945767 := bstep (se 1 (by rfl) ⟨2209325, by rfl⟩ : syracuseStep 2945767 = 4418651) B4418651
theorem B2947499 : Blo 774336 2947499 := bstep (se 1 (by rfl) ⟨2210624, by rfl⟩ : syracuseStep 2947499 = 4421249) B4421249
theorem B1244297 : Blo 774336 1244297 := bstep (se 2 (by rfl) ⟨466611, by rfl⟩ : syracuseStep 1244297 = 933223) B933223
theorem B1309979 : Blo 774336 1309979 := bstep (se 1 (by rfl) ⟨982484, by rfl⟩ : syracuseStep 1309979 = 1964969) B1964969
theorem B31948739 : Blo 774336 31948739 := bstep (se 1 (by rfl) ⟨23961554, by rfl⟩ : syracuseStep 31948739 = 47923109) B47923109
theorem B2490515 : Blo 774336 2490515 := bstep (se 1 (by rfl) ⟨1867886, by rfl⟩ : syracuseStep 2490515 = 3735773) B3735773
theorem B2622185 : Blo 774336 2622185 := bstep (se 2 (by rfl) ⟨983319, by rfl⟩ : syracuseStep 2622185 = 1966639) B1966639
theorem B29165831 : Blo 774336 29165831 := bstep (se 1 (by rfl) ⟨21874373, by rfl⟩ : syracuseStep 29165831 = 43748747) B43748747
theorem B2625695 : Blo 774336 2625695 := bstep (se 1 (by rfl) ⟨1969271, by rfl⟩ : syracuseStep 2625695 = 3938543) B3938543
theorem B5903927 : Blo 774336 5903927 := bstep (se 1 (by rfl) ⟨4427945, by rfl⟩ : syracuseStep 5903927 = 8855891) B8855891
theorem B1743407 : Blo 774336 1743407 := bstep (se 1 (by rfl) ⟨1307555, by rfl⟩ : syracuseStep 1743407 = 2615111) B2615111
theorem B2793295 : Blo 774336 2793295 := bstep (se 1 (by rfl) ⟨2094971, by rfl⟩ : syracuseStep 2793295 = 4189943) B4189943
theorem B57386873 : Blo 774336 57386873 := bstep (se 2 (by rfl) ⟨21520077, by rfl⟩ : syracuseStep 57386873 = 43040155) B43040155
theorem B829531 : Blo 774336 829531 := bstep (se 1 (by rfl) ⟨622148, by rfl⟩ : syracuseStep 829531 = 1244297) B1244297
theorem B1749113 : Blo 774336 1749113 := bstep (se 2 (by rfl) ⟨655917, by rfl⟩ : syracuseStep 1749113 = 1311835) B1311835
theorem B1161959 : Blo 774336 1161959 := bstep (se 1 (by rfl) ⟨871469, by rfl⟩ : syracuseStep 1161959 = 1742939) B1742939
theorem B7454015 : Blo 774336 7454015 := bstep (se 1 (by rfl) ⟨5590511, by rfl⟩ : syracuseStep 7454015 = 11181023) B11181023
theorem B1163135 : Blo 774336 1163135 := bstep (se 1 (by rfl) ⟨872351, by rfl⟩ : syracuseStep 1163135 = 1744703) B1744703
theorem B25151593 : Blo 774336 25151593 := bstep (se 2 (by rfl) ⟨9431847, by rfl⟩ : syracuseStep 25151593 = 18863695) B18863695
theorem B77449391 : Blo 774336 77449391 := bstep (se 1 (by rfl) ⟨58087043, by rfl⟩ : syracuseStep 77449391 = 116174087) B116174087
theorem B1166183 : Blo 774336 1166183 := bstep (se 1 (by rfl) ⟨874637, by rfl⟩ : syracuseStep 1166183 = 1749275) B1749275
theorem B1657883 : Blo 774336 1657883 := bstep (se 1 (by rfl) ⟨1243412, by rfl⟩ : syracuseStep 1657883 = 2486825) B2486825
theorem B1166969 : Blo 774336 1166969 := bstep (se 2 (by rfl) ⟨437613, by rfl⟩ : syracuseStep 1166969 = 875227) B875227
theorem B873319 : Blo 774336 873319 := bstep (se 1 (by rfl) ⟨654989, by rfl⟩ : syracuseStep 873319 = 1309979) B1309979
theorem B775495 : Blo 774336 775495 := bstep (se 1 (by rfl) ⟨581621, by rfl⟩ : syracuseStep 775495 = 1163243) B1163243
theorem B776239 : Blo 774336 776239 := bstep (se 1 (by rfl) ⟨582179, by rfl⟩ : syracuseStep 776239 = 1164359) B1164359
theorem B776519 : Blo 774336 776519 := bstep (se 1 (by rfl) ⟨582389, by rfl⟩ : syracuseStep 776519 = 1164779) B1164779
theorem B874975 : Blo 774336 874975 := bstep (se 1 (by rfl) ⟨656231, by rfl⟩ : syracuseStep 874975 = 1312463) B1312463
theorem B776911 : Blo 774336 776911 := bstep (se 1 (by rfl) ⟨582683, by rfl⟩ : syracuseStep 776911 = 1165367) B1165367
theorem B777935 : Blo 774336 777935 := bstep (se 1 (by rfl) ⟨583451, by rfl⟩ : syracuseStep 777935 = 1166903) B1166903
theorem B2515247 : Blo 774336 2515247 := bstep (se 1 (by rfl) ⟨1886435, by rfl⟩ : syracuseStep 2515247 = 3772871) B3772871
theorem B2942365 : Blo 774336 2942365 := bstep (se 3 (by rfl) ⟨551693, by rfl⟩ : syracuseStep 2942365 = 1103387) B1103387
theorem B25224767 : Blo 774336 25224767 := bstep (se 1 (by rfl) ⟨18918575, by rfl⟩ : syracuseStep 25224767 = 37837151) B37837151
theorem B1108075 : Blo 774336 1108075 := bstep (se 1 (by rfl) ⟨831056, by rfl⟩ : syracuseStep 1108075 = 1662113) B1662113
theorem B11201267 : Blo 774336 11201267 := bstep (se 1 (by rfl) ⟨8400950, by rfl⟩ : syracuseStep 11201267 = 16801901) B16801901
theorem B1961243 : Blo 774336 1961243 := bstep (se 1 (by rfl) ⟨1470932, by rfl⟩ : syracuseStep 1961243 = 2941865) B2941865
theorem B3927689 : Blo 774336 3927689 := bstep (se 2 (by rfl) ⟨1472883, by rfl⟩ : syracuseStep 3927689 = 2945767) B2945767
theorem B1964999 : Blo 774336 1964999 := bstep (se 1 (by rfl) ⟨1473749, by rfl⟩ : syracuseStep 1964999 = 2947499) B2947499
theorem B2522107 : Blo 774336 2522107 := bstep (se 1 (by rfl) ⟨1891580, by rfl⟩ : syracuseStep 2522107 = 3783161) B3783161
theorem B21299159 : Blo 774336 21299159 := bstep (se 1 (by rfl) ⟨15974369, by rfl⟩ : syracuseStep 21299159 = 31948739) B31948739
theorem B4424165 : Blo 774336 4424165 := bstep (se 4 (by rfl) ⟨414765, by rfl⟩ : syracuseStep 4424165 = 829531) B829531
theorem B1477433 : Blo 774336 1477433 := bstep (se 2 (by rfl) ⟨554037, by rfl⟩ : syracuseStep 1477433 = 1108075) B1108075
theorem B3935951 : Blo 774336 3935951 := bstep (se 1 (by rfl) ⟨2951963, by rfl⟩ : syracuseStep 3935951 = 5903927) B5903927
theorem B1676831 : Blo 774336 1676831 := bstep (se 1 (by rfl) ⟨1257623, by rfl⟩ : syracuseStep 1676831 = 2515247) B2515247
theorem B16816511 : Blo 774336 16816511 := bstep (se 1 (by rfl) ⟨12612383, by rfl⟩ : syracuseStep 16816511 = 25224767) B25224767
theorem B56797757 : Blo 774336 56797757 := bstep (se 3 (by rfl) ⟨10649579, by rfl⟩ : syracuseStep 56797757 = 21299159) B21299159
theorem B1748123 : Blo 774336 1748123 := bstep (se 1 (by rfl) ⟨1311092, by rfl⟩ : syracuseStep 1748123 = 2622185) B2622185
theorem B19443887 : Blo 774336 19443887 := bstep (se 1 (by rfl) ⟨14582915, by rfl⟩ : syracuseStep 19443887 = 29165831) B29165831
theorem B1750463 : Blo 774336 1750463 := bstep (se 1 (by rfl) ⟨1312847, by rfl⟩ : syracuseStep 1750463 = 2625695) B2625695
theorem B33535457 : Blo 774336 33535457 := bstep (se 2 (by rfl) ⟨12575796, by rfl⟩ : syracuseStep 33535457 = 25151593) B25151593
theorem B1162271 : Blo 774336 1162271 := bstep (se 1 (by rfl) ⟨871703, by rfl⟩ : syracuseStep 1162271 = 1743407) B1743407
theorem B1164425 : Blo 774336 1164425 := bstep (se 2 (by rfl) ⟨436659, by rfl⟩ : syracuseStep 1164425 = 873319) B873319
theorem B38257915 : Blo 774336 38257915 := bstep (se 1 (by rfl) ⟨28693436, by rfl⟩ : syracuseStep 38257915 = 57386873) B57386873
theorem B1166075 : Blo 774336 1166075 := bstep (se 1 (by rfl) ⟨874556, by rfl⟩ : syracuseStep 1166075 = 1749113) B1749113
theorem B1166633 : Blo 774336 1166633 := bstep (se 2 (by rfl) ⟨437487, by rfl⟩ : syracuseStep 1166633 = 874975) B874975
theorem B3362809 : Blo 774336 3362809 := bstep (se 2 (by rfl) ⟨1261053, by rfl⟩ : syracuseStep 3362809 = 2522107) B2522107
theorem B774639 : Blo 774336 774639 := bstep (se 1 (by rfl) ⟨580979, by rfl⟩ : syracuseStep 774639 = 1161959) B1161959
theorem B4969343 : Blo 774336 4969343 := bstep (se 1 (by rfl) ⟨3727007, by rfl⟩ : syracuseStep 4969343 = 7454015) B7454015
theorem B3724393 : Blo 774336 3724393 := bstep (se 2 (by rfl) ⟨1396647, by rfl⟩ : syracuseStep 3724393 = 2793295) B2793295
theorem B775423 : Blo 774336 775423 := bstep (se 1 (by rfl) ⟨581567, by rfl⟩ : syracuseStep 775423 = 1163135) B1163135
theorem B1660343 : Blo 774336 1660343 := bstep (se 1 (by rfl) ⟨1245257, by rfl⟩ : syracuseStep 1660343 = 2490515) B2490515
theorem B51632927 : Blo 774336 51632927 := bstep (se 1 (by rfl) ⟨38724695, by rfl⟩ : syracuseStep 51632927 = 77449391) B77449391
theorem B3923153 : Blo 774336 3923153 := bstep (se 2 (by rfl) ⟨1471182, by rfl⟩ : syracuseStep 3923153 = 2942365) B2942365
theorem B777455 : Blo 774336 777455 := bstep (se 1 (by rfl) ⟨583091, by rfl⟩ : syracuseStep 777455 = 1166183) B1166183
theorem B1105255 : Blo 774336 1105255 := bstep (se 1 (by rfl) ⟨828941, by rfl⟩ : syracuseStep 1105255 = 1657883) B1657883
theorem B777979 : Blo 774336 777979 := bstep (se 1 (by rfl) ⟨583484, by rfl⟩ : syracuseStep 777979 = 1166969) B1166969
theorem B7467511 : Blo 774336 7467511 := bstep (se 1 (by rfl) ⟨5600633, by rfl⟩ : syracuseStep 7467511 = 11201267) B11201267
theorem B1307495 : Blo 774336 1307495 := bstep (se 1 (by rfl) ⟨980621, by rfl⟩ : syracuseStep 1307495 = 1961243) B1961243
theorem B2618459 : Blo 774336 2618459 := bstep (se 1 (by rfl) ⟨1963844, by rfl⟩ : syracuseStep 2618459 = 3927689) B3927689
theorem B1309999 : Blo 774336 1309999 := bstep (se 1 (by rfl) ⟨982499, by rfl⟩ : syracuseStep 1309999 = 1964999) B1964999
theorem B2949443 : Blo 774336 2949443 := bstep (se 1 (by rfl) ⟨2212082, by rfl⟩ : syracuseStep 2949443 = 4424165) B4424165
theorem B984955 : Blo 774336 984955 := bstep (se 1 (by rfl) ⟨738716, by rfl⟩ : syracuseStep 984955 = 1477433) B1477433
theorem B2623967 : Blo 774336 2623967 := bstep (se 1 (by rfl) ⟨1967975, by rfl⟩ : syracuseStep 2623967 = 3935951) B3935951
theorem B3312895 : Blo 774336 3312895 := bstep (se 1 (by rfl) ⟨2484671, by rfl⟩ : syracuseStep 3312895 = 4969343) B4969343
theorem B4427581 : Blo 774336 4427581 := bstep (se 3 (by rfl) ⟨830171, by rfl⟩ : syracuseStep 4427581 = 1660343) B1660343
theorem B11211007 : Blo 774336 11211007 := bstep (se 1 (by rfl) ⟨8408255, by rfl⟩ : syracuseStep 11211007 = 16816511) B16816511
theorem B1745639 : Blo 774336 1745639 := bstep (se 1 (by rfl) ⟨1309229, by rfl⟩ : syracuseStep 1745639 = 2618459) B2618459
theorem B22356971 : Blo 774336 22356971 := bstep (se 1 (by rfl) ⟨16767728, by rfl⟩ : syracuseStep 22356971 = 33535457) B33535457
theorem B1746665 : Blo 774336 1746665 := bstep (se 2 (by rfl) ⟨654999, by rfl⟩ : syracuseStep 1746665 = 1309999) B1309999
theorem B34421951 : Blo 774336 34421951 := bstep (se 1 (by rfl) ⟨25816463, by rfl⟩ : syracuseStep 34421951 = 51632927) B51632927
theorem B4965857 : Blo 774336 4965857 := bstep (se 2 (by rfl) ⟨1862196, by rfl⟩ : syracuseStep 4965857 = 3724393) B3724393
theorem B37865171 : Blo 774336 37865171 := bstep (se 1 (by rfl) ⟨28398878, by rfl⟩ : syracuseStep 37865171 = 56797757) B56797757
theorem B1165415 : Blo 774336 1165415 := bstep (se 1 (by rfl) ⟨874061, by rfl⟩ : syracuseStep 1165415 = 1748123) B1748123
theorem B12962591 : Blo 774336 12962591 := bstep (se 1 (by rfl) ⟨9721943, by rfl⟩ : syracuseStep 12962591 = 19443887) B19443887
theorem B871663 : Blo 774336 871663 := bstep (se 1 (by rfl) ⟨653747, by rfl⟩ : syracuseStep 871663 = 1307495) B1307495
theorem B1166975 : Blo 774336 1166975 := bstep (se 1 (by rfl) ⟨875231, by rfl⟩ : syracuseStep 1166975 = 1750463) B1750463
theorem B774847 : Blo 774336 774847 := bstep (se 1 (by rfl) ⟨581135, by rfl⟩ : syracuseStep 774847 = 1162271) B1162271
theorem B776283 : Blo 774336 776283 := bstep (se 1 (by rfl) ⟨582212, by rfl⟩ : syracuseStep 776283 = 1164425) B1164425
theorem B51010553 : Blo 774336 51010553 := bstep (se 2 (by rfl) ⟨19128957, by rfl⟩ : syracuseStep 51010553 = 38257915) B38257915
theorem B777383 : Blo 774336 777383 := bstep (se 1 (by rfl) ⟨583037, by rfl⟩ : syracuseStep 777383 = 1166075) B1166075
theorem B777755 : Blo 774336 777755 := bstep (se 1 (by rfl) ⟨583316, by rfl⟩ : syracuseStep 777755 = 1166633) B1166633
theorem B2615435 : Blo 774336 2615435 := bstep (se 1 (by rfl) ⟨1961576, by rfl⟩ : syracuseStep 2615435 = 3923153) B3923153
theorem B4483745 : Blo 774336 4483745 := bstep (se 2 (by rfl) ⟨1681404, by rfl⟩ : syracuseStep 4483745 = 3362809) B3362809
theorem B17886197 : Blo 774336 17886197 := bstep (se 5 (by rfl) ⟨838415, by rfl⟩ : syracuseStep 17886197 = 1676831) B1676831
theorem B9956681 : Blo 774336 9956681 := bstep (se 2 (by rfl) ⟨3733755, by rfl⟩ : syracuseStep 9956681 = 7467511) B7467511
theorem B5894693 : Blo 774336 5894693 := bstep (se 4 (by rfl) ⟨552627, by rfl⟩ : syracuseStep 5894693 = 1105255) B1105255
theorem B1966295 : Blo 774336 1966295 := bstep (se 1 (by rfl) ⟨1474721, by rfl⟩ : syracuseStep 1966295 = 2949443) B2949443
theorem B3310571 : Blo 774336 3310571 := bstep (se 1 (by rfl) ⟨2482928, by rfl⟩ : syracuseStep 3310571 = 4965857) B4965857
theorem B1313273 : Blo 774336 1313273 := bstep (se 2 (by rfl) ⟨492477, by rfl⟩ : syracuseStep 1313273 = 984955) B984955
theorem B5903441 : Blo 774336 5903441 := bstep (se 2 (by rfl) ⟨2213790, by rfl⟩ : syracuseStep 5903441 = 4427581) B4427581
theorem B14948009 : Blo 774336 14948009 := bstep (se 2 (by rfl) ⟨5605503, by rfl⟩ : syracuseStep 14948009 = 11211007) B11211007
theorem B1743623 : Blo 774336 1743623 := bstep (se 1 (by rfl) ⟨1307717, by rfl⟩ : syracuseStep 1743623 = 2615435) B2615435
theorem B2989163 : Blo 774336 2989163 := bstep (se 1 (by rfl) ⟨2241872, by rfl⟩ : syracuseStep 2989163 = 4483745) B4483745
theorem B22947967 : Blo 774336 22947967 := bstep (se 1 (by rfl) ⟨17210975, by rfl⟩ : syracuseStep 22947967 = 34421951) B34421951
theorem B1749311 : Blo 774336 1749311 := bstep (se 1 (by rfl) ⟨1311983, by rfl⟩ : syracuseStep 1749311 = 2623967) B2623967
theorem B1162217 : Blo 774336 1162217 := bstep (se 2 (by rfl) ⟨435831, by rfl⟩ : syracuseStep 1162217 = 871663) B871663
theorem B100973789 : Blo 774336 100973789 := bstep (se 3 (by rfl) ⟨18932585, by rfl⟩ : syracuseStep 100973789 = 37865171) B37865171
theorem B1163759 : Blo 774336 1163759 := bstep (se 1 (by rfl) ⟨872819, by rfl⟩ : syracuseStep 1163759 = 1745639) B1745639
theorem B1164443 : Blo 774336 1164443 := bstep (se 1 (by rfl) ⟨873332, by rfl⟩ : syracuseStep 1164443 = 1746665) B1746665
theorem B6637787 : Blo 774336 6637787 := bstep (se 1 (by rfl) ⟨4978340, by rfl⟩ : syracuseStep 6637787 = 9956681) B9956681
theorem B47696525 : Blo 774336 47696525 := bstep (se 3 (by rfl) ⟨8943098, by rfl⟩ : syracuseStep 47696525 = 17886197) B17886197
theorem B776943 : Blo 774336 776943 := bstep (se 1 (by rfl) ⟨582707, by rfl⟩ : syracuseStep 776943 = 1165415) B1165415
theorem B8641727 : Blo 774336 8641727 := bstep (se 1 (by rfl) ⟨6481295, by rfl⟩ : syracuseStep 8641727 = 12962591) B12962591
theorem B777983 : Blo 774336 777983 := bstep (se 1 (by rfl) ⟨583487, by rfl⟩ : syracuseStep 777983 = 1166975) B1166975
theorem B4417193 : Blo 774336 4417193 := bstep (se 2 (by rfl) ⟨1656447, by rfl⟩ : syracuseStep 4417193 = 3312895) B3312895
theorem B34007035 : Blo 774336 34007035 := bstep (se 1 (by rfl) ⟨25505276, by rfl⟩ : syracuseStep 34007035 = 51010553) B51010553
theorem B14904647 : Blo 774336 14904647 := bstep (se 1 (by rfl) ⟨11178485, by rfl⟩ : syracuseStep 14904647 = 22356971) B22356971
theorem B3929795 : Blo 774336 3929795 := bstep (se 1 (by rfl) ⟨2947346, by rfl⟩ : syracuseStep 3929795 = 5894693) B5894693
theorem B1310863 : Blo 774336 1310863 := bstep (se 1 (by rfl) ⟨983147, by rfl⟩ : syracuseStep 1310863 = 1966295) B1966295
theorem B122389157 : Blo 774336 122389157 := bstep (se 4 (by rfl) ⟨11473983, by rfl⟩ : syracuseStep 122389157 = 22947967) B22947967
theorem B4425191 : Blo 774336 4425191 := bstep (se 1 (by rfl) ⟨3318893, by rfl⟩ : syracuseStep 4425191 = 6637787) B6637787
theorem B3935627 : Blo 774336 3935627 := bstep (se 1 (by rfl) ⟨2951720, by rfl⟩ : syracuseStep 3935627 = 5903441) B5903441
theorem B9965339 : Blo 774336 9965339 := bstep (se 1 (by rfl) ⟨7474004, by rfl⟩ : syracuseStep 9965339 = 14948009) B14948009
theorem B9936431 : Blo 774336 9936431 := bstep (se 1 (by rfl) ⟨7452323, by rfl⟩ : syracuseStep 9936431 = 14904647) B14904647
theorem B67315859 : Blo 774336 67315859 := bstep (se 1 (by rfl) ⟨50486894, by rfl⟩ : syracuseStep 67315859 = 100973789) B100973789
theorem B31797683 : Blo 774336 31797683 := bstep (se 1 (by rfl) ⟨23848262, by rfl⟩ : syracuseStep 31797683 = 47696525) B47696525
theorem B8828189 : Blo 774336 8828189 := bstep (se 3 (by rfl) ⟨1655285, by rfl⟩ : syracuseStep 8828189 = 3310571) B3310571
theorem B1162415 : Blo 774336 1162415 := bstep (se 1 (by rfl) ⟨871811, by rfl⟩ : syracuseStep 1162415 = 1743623) B1743623
theorem B1166207 : Blo 774336 1166207 := bstep (se 1 (by rfl) ⟨874655, by rfl⟩ : syracuseStep 1166207 = 1749311) B1749311
theorem B774811 : Blo 774336 774811 := bstep (se 1 (by rfl) ⟨581108, by rfl⟩ : syracuseStep 774811 = 1162217) B1162217
theorem B775839 : Blo 774336 775839 := bstep (se 1 (by rfl) ⟨581879, by rfl⟩ : syracuseStep 775839 = 1163759) B1163759
theorem B776295 : Blo 774336 776295 := bstep (se 1 (by rfl) ⟨582221, by rfl⟩ : syracuseStep 776295 = 1164443) B1164443
theorem B875515 : Blo 774336 875515 := bstep (se 1 (by rfl) ⟨656636, by rfl⟩ : syracuseStep 875515 = 1313273) B1313273
theorem B45342713 : Blo 774336 45342713 := bstep (se 2 (by rfl) ⟨17003517, by rfl⟩ : syracuseStep 45342713 = 34007035) B34007035
theorem B1992775 : Blo 774336 1992775 := bstep (se 1 (by rfl) ⟨1494581, by rfl⟩ : syracuseStep 1992775 = 2989163) B2989163
theorem B5761151 : Blo 774336 5761151 := bstep (se 1 (by rfl) ⟨4320863, by rfl⟩ : syracuseStep 5761151 = 8641727) B8641727
theorem B2944795 : Blo 774336 2944795 := bstep (se 1 (by rfl) ⟨2208596, by rfl⟩ : syracuseStep 2944795 = 4417193) B4417193
theorem B2619863 : Blo 774336 2619863 := bstep (se 1 (by rfl) ⟨1964897, by rfl⟩ : syracuseStep 2619863 = 3929795) B3929795
theorem B81592771 : Blo 774336 81592771 := bstep (se 1 (by rfl) ⟨61194578, by rfl⟩ : syracuseStep 81592771 = 122389157) B122389157
theorem B2950127 : Blo 774336 2950127 := bstep (se 1 (by rfl) ⟨2212595, by rfl⟩ : syracuseStep 2950127 = 4425191) B4425191
theorem B2623751 : Blo 774336 2623751 := bstep (se 1 (by rfl) ⟨1967813, by rfl⟩ : syracuseStep 2623751 = 3935627) B3935627
theorem B2657033 : Blo 774336 2657033 := bstep (se 2 (by rfl) ⟨996387, by rfl⟩ : syracuseStep 2657033 = 1992775) B1992775
theorem B6624287 : Blo 774336 6624287 := bstep (se 1 (by rfl) ⟨4968215, by rfl⟩ : syracuseStep 6624287 = 9936431) B9936431
theorem B3840767 : Blo 774336 3840767 := bstep (se 1 (by rfl) ⟨2880575, by rfl⟩ : syracuseStep 3840767 = 5761151) B5761151
theorem B1746575 : Blo 774336 1746575 := bstep (se 1 (by rfl) ⟨1309931, by rfl⟩ : syracuseStep 1746575 = 2619863) B2619863
theorem B1747817 : Blo 774336 1747817 := bstep (se 2 (by rfl) ⟨655431, by rfl⟩ : syracuseStep 1747817 = 1310863) B1310863
theorem B30228475 : Blo 774336 30228475 := bstep (se 1 (by rfl) ⟨22671356, by rfl⟩ : syracuseStep 30228475 = 45342713) B45342713
theorem B44877239 : Blo 774336 44877239 := bstep (se 1 (by rfl) ⟨33657929, by rfl⟩ : syracuseStep 44877239 = 67315859) B67315859
theorem B5885459 : Blo 774336 5885459 := bstep (se 1 (by rfl) ⟨4414094, by rfl⟩ : syracuseStep 5885459 = 8828189) B8828189
theorem B1167353 : Blo 774336 1167353 := bstep (se 2 (by rfl) ⟨437757, by rfl⟩ : syracuseStep 1167353 = 875515) B875515
theorem B774943 : Blo 774336 774943 := bstep (se 1 (by rfl) ⟨581207, by rfl⟩ : syracuseStep 774943 = 1162415) B1162415
theorem B777471 : Blo 774336 777471 := bstep (se 1 (by rfl) ⟨583103, by rfl⟩ : syracuseStep 777471 = 1166207) B1166207
theorem B6643559 : Blo 774336 6643559 := bstep (se 1 (by rfl) ⟨4982669, by rfl⟩ : syracuseStep 6643559 = 9965339) B9965339
theorem B3926393 : Blo 774336 3926393 := bstep (se 2 (by rfl) ⟨1472397, by rfl⟩ : syracuseStep 3926393 = 2944795) B2944795
theorem B21198455 : Blo 774336 21198455 := bstep (se 1 (by rfl) ⟨15898841, by rfl⟩ : syracuseStep 21198455 = 31797683) B31797683
theorem B108790361 : Blo 774336 108790361 := bstep (se 2 (by rfl) ⟨40796385, by rfl⟩ : syracuseStep 108790361 = 81592771) B81592771
theorem B1966751 : Blo 774336 1966751 := bstep (se 1 (by rfl) ⟨1475063, by rfl⟩ : syracuseStep 1966751 = 2950127) B2950127
theorem B29918159 : Blo 774336 29918159 := bstep (se 1 (by rfl) ⟨22438619, by rfl⟩ : syracuseStep 29918159 = 44877239) B44877239
theorem B1771355 : Blo 774336 1771355 := bstep (se 1 (by rfl) ⟨1328516, by rfl⟩ : syracuseStep 1771355 = 2657033) B2657033
theorem B2560511 : Blo 774336 2560511 := bstep (se 1 (by rfl) ⟨1920383, by rfl⟩ : syracuseStep 2560511 = 3840767) B3840767
theorem B4429039 : Blo 774336 4429039 := bstep (se 1 (by rfl) ⟨3321779, by rfl⟩ : syracuseStep 4429039 = 6643559) B6643559
theorem B14132303 : Blo 774336 14132303 := bstep (se 1 (by rfl) ⟨10599227, by rfl⟩ : syracuseStep 14132303 = 21198455) B21198455
theorem B1749167 : Blo 774336 1749167 := bstep (se 1 (by rfl) ⟨1311875, by rfl⟩ : syracuseStep 1749167 = 2623751) B2623751
theorem B1164383 : Blo 774336 1164383 := bstep (se 1 (by rfl) ⟨873287, by rfl⟩ : syracuseStep 1164383 = 1746575) B1746575
theorem B1165211 : Blo 774336 1165211 := bstep (se 1 (by rfl) ⟨873908, by rfl⟩ : syracuseStep 1165211 = 1747817) B1747817
theorem B3923639 : Blo 774336 3923639 := bstep (se 1 (by rfl) ⟨2942729, by rfl⟩ : syracuseStep 3923639 = 5885459) B5885459
theorem B778235 : Blo 774336 778235 := bstep (se 1 (by rfl) ⟨583676, by rfl⟩ : syracuseStep 778235 = 1167353) B1167353
theorem B4416191 : Blo 774336 4416191 := bstep (se 1 (by rfl) ⟨3312143, by rfl⟩ : syracuseStep 4416191 = 6624287) B6624287
theorem B2617595 : Blo 774336 2617595 := bstep (se 1 (by rfl) ⟨1963196, by rfl⟩ : syracuseStep 2617595 = 3926393) B3926393
theorem B40304633 : Blo 774336 40304633 := bstep (se 2 (by rfl) ⟨15114237, by rfl⟩ : syracuseStep 40304633 = 30228475) B30228475
theorem B1311167 : Blo 774336 1311167 := bstep (se 1 (by rfl) ⟨983375, by rfl⟩ : syracuseStep 1311167 = 1966751) B1966751
theorem B1707007 : Blo 774336 1707007 := bstep (se 1 (by rfl) ⟨1280255, by rfl⟩ : syracuseStep 1707007 = 2560511) B2560511
theorem B4723613 : Blo 774336 4723613 := bstep (se 3 (by rfl) ⟨885677, by rfl⟩ : syracuseStep 4723613 = 1771355) B1771355
theorem B5905385 : Blo 774336 5905385 := bstep (se 2 (by rfl) ⟨2214519, by rfl⟩ : syracuseStep 5905385 = 4429039) B4429039
theorem B1745063 : Blo 774336 1745063 := bstep (se 1 (by rfl) ⟨1308797, by rfl⟩ : syracuseStep 1745063 = 2617595) B2617595
theorem B72526907 : Blo 774336 72526907 := bstep (se 1 (by rfl) ⟨54395180, by rfl⟩ : syracuseStep 72526907 = 108790361) B108790361
theorem B9421535 : Blo 774336 9421535 := bstep (se 1 (by rfl) ⟨7066151, by rfl⟩ : syracuseStep 9421535 = 14132303) B14132303
theorem B1166111 : Blo 774336 1166111 := bstep (se 1 (by rfl) ⟨874583, by rfl⟩ : syracuseStep 1166111 = 1749167) B1749167
theorem B19945439 : Blo 774336 19945439 := bstep (se 1 (by rfl) ⟨14959079, by rfl⟩ : syracuseStep 19945439 = 29918159) B29918159
theorem B776255 : Blo 774336 776255 := bstep (se 1 (by rfl) ⟨582191, by rfl⟩ : syracuseStep 776255 = 1164383) B1164383
theorem B776807 : Blo 774336 776807 := bstep (se 1 (by rfl) ⟨582605, by rfl⟩ : syracuseStep 776807 = 1165211) B1165211
theorem B2615759 : Blo 774336 2615759 := bstep (se 1 (by rfl) ⟨1961819, by rfl⟩ : syracuseStep 2615759 = 3923639) B3923639
theorem B2944127 : Blo 774336 2944127 := bstep (se 1 (by rfl) ⟨2208095, by rfl⟩ : syracuseStep 2944127 = 4416191) B4416191
theorem B107479021 : Blo 774336 107479021 := bstep (se 3 (by rfl) ⟨20152316, by rfl⟩ : syracuseStep 107479021 = 40304633) B40304633
theorem B3149075 : Blo 774336 3149075 := bstep (se 1 (by rfl) ⟨2361806, by rfl⟩ : syracuseStep 3149075 = 4723613) B4723613
theorem B3936923 : Blo 774336 3936923 := bstep (se 1 (by rfl) ⟨2952692, by rfl⟩ : syracuseStep 3936923 = 5905385) B5905385
theorem B1743839 : Blo 774336 1743839 := bstep (se 1 (by rfl) ⟨1307879, by rfl⟩ : syracuseStep 1743839 = 2615759) B2615759
theorem B143305361 : Blo 774336 143305361 := bstep (se 2 (by rfl) ⟨53739510, by rfl⟩ : syracuseStep 143305361 = 107479021) B107479021
theorem B2276009 : Blo 774336 2276009 := bstep (se 2 (by rfl) ⟨853503, by rfl⟩ : syracuseStep 2276009 = 1707007) B1707007
theorem B1163375 : Blo 774336 1163375 := bstep (se 1 (by rfl) ⟨872531, by rfl⟩ : syracuseStep 1163375 = 1745063) B1745063
theorem B48351271 : Blo 774336 48351271 := bstep (se 1 (by rfl) ⟨36263453, by rfl⟩ : syracuseStep 48351271 = 72526907) B72526907
theorem B874111 : Blo 774336 874111 := bstep (se 1 (by rfl) ⟨655583, by rfl⟩ : syracuseStep 874111 = 1311167) B1311167
theorem B6281023 : Blo 774336 6281023 := bstep (se 1 (by rfl) ⟨4710767, by rfl⟩ : syracuseStep 6281023 = 9421535) B9421535
theorem B777407 : Blo 774336 777407 := bstep (se 1 (by rfl) ⟨583055, by rfl⟩ : syracuseStep 777407 = 1166111) B1166111
theorem B13296959 : Blo 774336 13296959 := bstep (se 1 (by rfl) ⟨9972719, by rfl⟩ : syracuseStep 13296959 = 19945439) B19945439
theorem B1962751 : Blo 774336 1962751 := bstep (se 1 (by rfl) ⟨1472063, by rfl⟩ : syracuseStep 1962751 = 2944127) B2944127
theorem B2624615 : Blo 774336 2624615 := bstep (se 1 (by rfl) ⟨1968461, by rfl⟩ : syracuseStep 2624615 = 3936923) B3936923
theorem B8397533 : Blo 774336 8397533 := bstep (se 3 (by rfl) ⟨1574537, by rfl⟩ : syracuseStep 8397533 = 3149075) B3149075
theorem B1517339 : Blo 774336 1517339 := bstep (se 1 (by rfl) ⟨1138004, by rfl⟩ : syracuseStep 1517339 = 2276009) B2276009
theorem B64468361 : Blo 774336 64468361 := bstep (se 2 (by rfl) ⟨24175635, by rfl⟩ : syracuseStep 64468361 = 48351271) B48351271
theorem B1162559 : Blo 774336 1162559 := bstep (se 1 (by rfl) ⟨871919, by rfl⟩ : syracuseStep 1162559 = 1743839) B1743839
theorem B8864639 : Blo 774336 8864639 := bstep (se 1 (by rfl) ⟨6648479, by rfl⟩ : syracuseStep 8864639 = 13296959) B13296959
theorem B95536907 : Blo 774336 95536907 := bstep (se 1 (by rfl) ⟨71652680, by rfl⟩ : syracuseStep 95536907 = 143305361) B143305361
theorem B1165481 : Blo 774336 1165481 := bstep (se 2 (by rfl) ⟨437055, by rfl⟩ : syracuseStep 1165481 = 874111) B874111
theorem B8374697 : Blo 774336 8374697 := bstep (se 2 (by rfl) ⟨3140511, by rfl⟩ : syracuseStep 8374697 = 6281023) B6281023
theorem B775583 : Blo 774336 775583 := bstep (se 1 (by rfl) ⟨581687, by rfl⟩ : syracuseStep 775583 = 1163375) B1163375
theorem B2617001 : Blo 774336 2617001 := bstep (se 2 (by rfl) ⟨981375, by rfl⟩ : syracuseStep 2617001 = 1962751) B1962751
theorem B1744667 : Blo 774336 1744667 := bstep (se 1 (by rfl) ⟨1308500, by rfl⟩ : syracuseStep 1744667 = 2617001) B2617001
theorem B5909759 : Blo 774336 5909759 := bstep (se 1 (by rfl) ⟨4432319, by rfl⟩ : syracuseStep 5909759 = 8864639) B8864639
theorem B5583131 : Blo 774336 5583131 := bstep (se 1 (by rfl) ⟨4187348, by rfl⟩ : syracuseStep 5583131 = 8374697) B8374697
theorem B1749743 : Blo 774336 1749743 := bstep (se 1 (by rfl) ⟨1312307, by rfl⟩ : syracuseStep 1749743 = 2624615) B2624615
theorem B42978907 : Blo 774336 42978907 := bstep (se 1 (by rfl) ⟨32234180, by rfl⟩ : syracuseStep 42978907 = 64468361) B64468361
theorem B775039 : Blo 774336 775039 := bstep (se 1 (by rfl) ⟨581279, by rfl⟩ : syracuseStep 775039 = 1162559) B1162559
theorem B63691271 : Blo 774336 63691271 := bstep (se 1 (by rfl) ⟨47768453, by rfl⟩ : syracuseStep 63691271 = 95536907) B95536907
theorem B776987 : Blo 774336 776987 := bstep (se 1 (by rfl) ⟨582740, by rfl⟩ : syracuseStep 776987 = 1165481) B1165481
theorem B5598355 : Blo 774336 5598355 := bstep (se 1 (by rfl) ⟨4198766, by rfl⟩ : syracuseStep 5598355 = 8397533) B8397533
theorem B1011559 : Blo 774336 1011559 := bstep (se 1 (by rfl) ⟨758669, by rfl⟩ : syracuseStep 1011559 = 1517339) B1517339
theorem B1348745 : Blo 774336 1348745 := bstep (se 2 (by rfl) ⟨505779, by rfl⟩ : syracuseStep 1348745 = 1011559) B1011559
theorem B3939839 : Blo 774336 3939839 := bstep (se 1 (by rfl) ⟨2954879, by rfl⟩ : syracuseStep 3939839 = 5909759) B5909759
theorem B229220837 : Blo 774336 229220837 := bstep (se 4 (by rfl) ⟨21489453, by rfl⟩ : syracuseStep 229220837 = 42978907) B42978907
theorem B1163111 : Blo 774336 1163111 := bstep (se 1 (by rfl) ⟨872333, by rfl⟩ : syracuseStep 1163111 = 1744667) B1744667
theorem B3722087 : Blo 774336 3722087 := bstep (se 1 (by rfl) ⟨2791565, by rfl⟩ : syracuseStep 3722087 = 5583131) B5583131
theorem B1166495 : Blo 774336 1166495 := bstep (se 1 (by rfl) ⟨874871, by rfl⟩ : syracuseStep 1166495 = 1749743) B1749743
theorem B7464473 : Blo 774336 7464473 := bstep (se 2 (by rfl) ⟨2799177, by rfl⟩ : syracuseStep 7464473 = 5598355) B5598355
theorem B42460847 : Blo 774336 42460847 := bstep (se 1 (by rfl) ⟨31845635, by rfl⟩ : syracuseStep 42460847 = 63691271) B63691271
theorem B2626559 : Blo 774336 2626559 := bstep (se 1 (by rfl) ⟨1969919, by rfl⟩ : syracuseStep 2626559 = 3939839) B3939839
theorem B152813891 : Blo 774336 152813891 := bstep (se 1 (by rfl) ⟨114610418, by rfl⟩ : syracuseStep 152813891 = 229220837) B229220837
theorem B775407 : Blo 774336 775407 := bstep (se 1 (by rfl) ⟨581555, by rfl⟩ : syracuseStep 775407 = 1163111) B1163111
theorem B2481391 : Blo 774336 2481391 := bstep (se 1 (by rfl) ⟨1861043, by rfl⟩ : syracuseStep 2481391 = 3722087) B3722087
theorem B777663 : Blo 774336 777663 := bstep (se 1 (by rfl) ⟨583247, by rfl⟩ : syracuseStep 777663 = 1166495) B1166495
theorem B3596653 : Blo 774336 3596653 := bstep (se 3 (by rfl) ⟨674372, by rfl⟩ : syracuseStep 3596653 = 1348745) B1348745
theorem B4976315 : Blo 774336 4976315 := bstep (se 1 (by rfl) ⟨3732236, by rfl⟩ : syracuseStep 4976315 = 7464473) B7464473
theorem B28307231 : Blo 774336 28307231 := bstep (se 1 (by rfl) ⟨21230423, by rfl⟩ : syracuseStep 28307231 = 42460847) B42460847
theorem B101875927 : Blo 774336 101875927 := bstep (se 1 (by rfl) ⟨76406945, by rfl⟩ : syracuseStep 101875927 = 152813891) B152813891
theorem B3317543 : Blo 774336 3317543 := bstep (se 1 (by rfl) ⟨2488157, by rfl⟩ : syracuseStep 3317543 = 4976315) B4976315
theorem B4795537 : Blo 774336 4795537 := bstep (se 2 (by rfl) ⟨1798326, by rfl⟩ : syracuseStep 4795537 = 3596653) B3596653
theorem B1751039 : Blo 774336 1751039 := bstep (se 1 (by rfl) ⟨1313279, by rfl⟩ : syracuseStep 1751039 = 2626559) B2626559
theorem B18871487 : Blo 774336 18871487 := bstep (se 1 (by rfl) ⟨14153615, by rfl⟩ : syracuseStep 18871487 = 28307231) B28307231
theorem B3308521 : Blo 774336 3308521 := bstep (se 2 (by rfl) ⟨1240695, by rfl⟩ : syracuseStep 3308521 = 2481391) B2481391
theorem B6394049 : Blo 774336 6394049 := bstep (se 2 (by rfl) ⟨2397768, by rfl⟩ : syracuseStep 6394049 = 4795537) B4795537
theorem B135834569 : Blo 774336 135834569 := bstep (se 2 (by rfl) ⟨50937963, by rfl⟩ : syracuseStep 135834569 = 101875927) B101875927
theorem B2211695 : Blo 774336 2211695 := bstep (se 1 (by rfl) ⟨1658771, by rfl⟩ : syracuseStep 2211695 = 3317543) B3317543
theorem B4411361 : Blo 774336 4411361 := bstep (se 2 (by rfl) ⟨1654260, by rfl⟩ : syracuseStep 4411361 = 3308521) B3308521
theorem B1167359 : Blo 774336 1167359 := bstep (se 1 (by rfl) ⟨875519, by rfl⟩ : syracuseStep 1167359 = 1751039) B1751039
theorem B12580991 : Blo 774336 12580991 := bstep (se 1 (by rfl) ⟨9435743, by rfl⟩ : syracuseStep 12580991 = 18871487) B18871487
theorem B4262699 : Blo 774336 4262699 := bstep (se 1 (by rfl) ⟨3197024, by rfl⟩ : syracuseStep 4262699 = 6394049) B6394049
theorem B90556379 : Blo 774336 90556379 := bstep (se 1 (by rfl) ⟨67917284, by rfl⟩ : syracuseStep 90556379 = 135834569) B135834569
theorem B2940907 : Blo 774336 2940907 := bstep (se 1 (by rfl) ⟨2205680, by rfl⟩ : syracuseStep 2940907 = 4411361) B4411361
theorem B778239 : Blo 774336 778239 := bstep (se 1 (by rfl) ⟨583679, by rfl⟩ : syracuseStep 778239 = 1167359) B1167359
theorem B8387327 : Blo 774336 8387327 := bstep (se 1 (by rfl) ⟨6290495, by rfl⟩ : syracuseStep 8387327 = 12580991) B12580991
theorem B1474463 : Blo 774336 1474463 := bstep (se 1 (by rfl) ⟨1105847, by rfl⟩ : syracuseStep 1474463 = 2211695) B2211695
theorem B60370919 : Blo 774336 60370919 := bstep (se 1 (by rfl) ⟨45278189, by rfl⟩ : syracuseStep 60370919 = 90556379) B90556379
theorem B5591551 : Blo 774336 5591551 := bstep (se 1 (by rfl) ⟨4193663, by rfl⟩ : syracuseStep 5591551 = 8387327) B8387327
theorem B3921209 : Blo 774336 3921209 := bstep (se 2 (by rfl) ⟨1470453, by rfl⟩ : syracuseStep 3921209 = 2940907) B2940907
theorem B2841799 : Blo 774336 2841799 := bstep (se 1 (by rfl) ⟨2131349, by rfl⟩ : syracuseStep 2841799 = 4262699) B4262699
theorem B3931901 : Blo 774336 3931901 := bstep (se 3 (by rfl) ⟨737231, by rfl⟩ : syracuseStep 3931901 = 1474463) B1474463
theorem B40247279 : Blo 774336 40247279 := bstep (se 1 (by rfl) ⟨30185459, by rfl⟩ : syracuseStep 40247279 = 60370919) B60370919
theorem B7455401 : Blo 774336 7455401 := bstep (se 2 (by rfl) ⟨2795775, by rfl⟩ : syracuseStep 7455401 = 5591551) B5591551
theorem B3789065 : Blo 774336 3789065 := bstep (se 2 (by rfl) ⟨1420899, by rfl⟩ : syracuseStep 3789065 = 2841799) B2841799
theorem B2614139 : Blo 774336 2614139 := bstep (se 1 (by rfl) ⟨1960604, by rfl⟩ : syracuseStep 2614139 = 3921209) B3921209
theorem B2621267 : Blo 774336 2621267 := bstep (se 1 (by rfl) ⟨1965950, by rfl⟩ : syracuseStep 2621267 = 3931901) B3931901
theorem B1742759 : Blo 774336 1742759 := bstep (se 1 (by rfl) ⟨1307069, by rfl⟩ : syracuseStep 1742759 = 2614139) B2614139
theorem B1747511 : Blo 774336 1747511 := bstep (se 1 (by rfl) ⟨1310633, by rfl⟩ : syracuseStep 1747511 = 2621267) B2621267
theorem B10104173 : Blo 774336 10104173 := bstep (se 3 (by rfl) ⟨1894532, by rfl⟩ : syracuseStep 10104173 = 3789065) B3789065
theorem B4970267 : Blo 774336 4970267 := bstep (se 1 (by rfl) ⟨3727700, by rfl⟩ : syracuseStep 4970267 = 7455401) B7455401
theorem B26831519 : Blo 774336 26831519 := bstep (se 1 (by rfl) ⟨20123639, by rfl⟩ : syracuseStep 26831519 = 40247279) B40247279
theorem B3313511 : Blo 774336 3313511 := bstep (se 1 (by rfl) ⟨2485133, by rfl⟩ : syracuseStep 3313511 = 4970267) B4970267
theorem B1161839 : Blo 774336 1161839 := bstep (se 1 (by rfl) ⟨871379, by rfl⟩ : syracuseStep 1161839 = 1742759) B1742759
theorem B1165007 : Blo 774336 1165007 := bstep (se 1 (by rfl) ⟨873755, by rfl⟩ : syracuseStep 1165007 = 1747511) B1747511
theorem B6736115 : Blo 774336 6736115 := bstep (se 1 (by rfl) ⟨5052086, by rfl⟩ : syracuseStep 6736115 = 10104173) B10104173
theorem B17887679 : Blo 774336 17887679 := bstep (se 1 (by rfl) ⟨13415759, by rfl⟩ : syracuseStep 17887679 = 26831519) B26831519
theorem B4490743 : Blo 774336 4490743 := bstep (se 1 (by rfl) ⟨3368057, by rfl⟩ : syracuseStep 4490743 = 6736115) B6736115
theorem B2209007 : Blo 774336 2209007 := bstep (se 1 (by rfl) ⟨1656755, by rfl⟩ : syracuseStep 2209007 = 3313511) B3313511
theorem B774559 : Blo 774336 774559 := bstep (se 1 (by rfl) ⟨580919, by rfl⟩ : syracuseStep 774559 = 1161839) B1161839
theorem B776671 : Blo 774336 776671 := bstep (se 1 (by rfl) ⟨582503, by rfl⟩ : syracuseStep 776671 = 1165007) B1165007
theorem B11925119 : Blo 774336 11925119 := bstep (se 1 (by rfl) ⟨8943839, by rfl⟩ : syracuseStep 11925119 = 17887679) B17887679
theorem B7950079 : Blo 774336 7950079 := bstep (se 1 (by rfl) ⟨5962559, by rfl⟩ : syracuseStep 7950079 = 11925119) B11925119
theorem B5987657 : Blo 774336 5987657 := bstep (se 2 (by rfl) ⟨2245371, by rfl⟩ : syracuseStep 5987657 = 4490743) B4490743
theorem B1472671 : Blo 774336 1472671 := bstep (se 1 (by rfl) ⟨1104503, by rfl⟩ : syracuseStep 1472671 = 2209007) B2209007
theorem B10600105 : Blo 774336 10600105 := bstep (se 2 (by rfl) ⟨3975039, by rfl⟩ : syracuseStep 10600105 = 7950079) B7950079
theorem B3991771 : Blo 774336 3991771 := bstep (se 1 (by rfl) ⟨2993828, by rfl⟩ : syracuseStep 3991771 = 5987657) B5987657
theorem B1963561 : Blo 774336 1963561 := bstep (se 2 (by rfl) ⟨736335, by rfl⟩ : syracuseStep 1963561 = 1472671) B1472671
theorem B14133473 : Blo 774336 14133473 := bstep (se 2 (by rfl) ⟨5300052, by rfl⟩ : syracuseStep 14133473 = 10600105) B10600105
theorem B5322361 : Blo 774336 5322361 := bstep (se 2 (by rfl) ⟨1995885, by rfl⟩ : syracuseStep 5322361 = 3991771) B3991771
theorem B2618081 : Blo 774336 2618081 := bstep (se 2 (by rfl) ⟨981780, by rfl⟩ : syracuseStep 2618081 = 1963561) B1963561
theorem B1745387 : Blo 774336 1745387 := bstep (se 1 (by rfl) ⟨1309040, by rfl⟩ : syracuseStep 1745387 = 2618081) B2618081
theorem B9422315 : Blo 774336 9422315 := bstep (se 1 (by rfl) ⟨7066736, by rfl⟩ : syracuseStep 9422315 = 14133473) B14133473
theorem B7096481 : Blo 774336 7096481 := bstep (se 2 (by rfl) ⟨2661180, by rfl⟩ : syracuseStep 7096481 = 5322361) B5322361
theorem B4730987 : Blo 774336 4730987 := bstep (se 1 (by rfl) ⟨3548240, by rfl⟩ : syracuseStep 4730987 = 7096481) B7096481
theorem B1163591 : Blo 774336 1163591 := bstep (se 1 (by rfl) ⟨872693, by rfl⟩ : syracuseStep 1163591 = 1745387) B1745387
theorem B6281543 : Blo 774336 6281543 := bstep (se 1 (by rfl) ⟨4711157, by rfl⟩ : syracuseStep 6281543 = 9422315) B9422315
theorem B3153991 : Blo 774336 3153991 := bstep (se 1 (by rfl) ⟨2365493, by rfl⟩ : syracuseStep 3153991 = 4730987) B4730987
theorem B775727 : Blo 774336 775727 := bstep (se 1 (by rfl) ⟨581795, by rfl⟩ : syracuseStep 775727 = 1163591) B1163591
theorem B4187695 : Blo 774336 4187695 := bstep (se 1 (by rfl) ⟨3140771, by rfl⟩ : syracuseStep 4187695 = 6281543) B6281543
theorem B4205321 : Blo 774336 4205321 := bstep (se 2 (by rfl) ⟨1576995, by rfl⟩ : syracuseStep 4205321 = 3153991) B3153991
theorem B5583593 : Blo 774336 5583593 := bstep (se 2 (by rfl) ⟨2093847, by rfl⟩ : syracuseStep 5583593 = 4187695) B4187695
theorem B2803547 : Blo 774336 2803547 := bstep (se 1 (by rfl) ⟨2102660, by rfl⟩ : syracuseStep 2803547 = 4205321) B4205321
theorem B3722395 : Blo 774336 3722395 := bstep (se 1 (by rfl) ⟨2791796, by rfl⟩ : syracuseStep 3722395 = 5583593) B5583593
theorem B1869031 : Blo 774336 1869031 := bstep (se 1 (by rfl) ⟨1401773, by rfl⟩ : syracuseStep 1869031 = 2803547) B2803547
theorem B4963193 : Blo 774336 4963193 := bstep (se 2 (by rfl) ⟨1861197, by rfl⟩ : syracuseStep 4963193 = 3722395) B3722395
theorem B2492041 : Blo 774336 2492041 := bstep (se 2 (by rfl) ⟨934515, by rfl⟩ : syracuseStep 2492041 = 1869031) B1869031
theorem B3308795 : Blo 774336 3308795 := bstep (se 1 (by rfl) ⟨2481596, by rfl⟩ : syracuseStep 3308795 = 4963193) B4963193
theorem B2205863 : Blo 774336 2205863 := bstep (se 1 (by rfl) ⟨1654397, by rfl⟩ : syracuseStep 2205863 = 3308795) B3308795
theorem B3322721 : Blo 774336 3322721 := bstep (se 2 (by rfl) ⟨1246020, by rfl⟩ : syracuseStep 3322721 = 2492041) B2492041
theorem B2215147 : Blo 774336 2215147 := bstep (se 1 (by rfl) ⟨1661360, by rfl⟩ : syracuseStep 2215147 = 3322721) B3322721
theorem B1470575 : Blo 774336 1470575 := bstep (se 1 (by rfl) ⟨1102931, by rfl⟩ : syracuseStep 1470575 = 2205863) B2205863
theorem B2953529 : Blo 774336 2953529 := bstep (se 2 (by rfl) ⟨1107573, by rfl⟩ : syracuseStep 2953529 = 2215147) B2215147
theorem B3921533 : Blo 774336 3921533 := bstep (se 3 (by rfl) ⟨735287, by rfl⟩ : syracuseStep 3921533 = 1470575) B1470575
theorem B1969019 : Blo 774336 1969019 := bstep (se 1 (by rfl) ⟨1476764, by rfl⟩ : syracuseStep 1969019 = 2953529) B2953529
theorem B2614355 : Blo 774336 2614355 := bstep (se 1 (by rfl) ⟨1960766, by rfl⟩ : syracuseStep 2614355 = 3921533) B3921533
theorem B1312679 : Blo 774336 1312679 := bstep (se 1 (by rfl) ⟨984509, by rfl⟩ : syracuseStep 1312679 = 1969019) B1969019
theorem B1742903 : Blo 774336 1742903 := bstep (se 1 (by rfl) ⟨1307177, by rfl⟩ : syracuseStep 1742903 = 2614355) B2614355
theorem B1161935 : Blo 774336 1161935 := bstep (se 1 (by rfl) ⟨871451, by rfl⟩ : syracuseStep 1161935 = 1742903) B1742903
theorem B875119 : Blo 774336 875119 := bstep (se 1 (by rfl) ⟨656339, by rfl⟩ : syracuseStep 875119 = 1312679) B1312679
theorem B1166825 : Blo 774336 1166825 := bstep (se 2 (by rfl) ⟨437559, by rfl⟩ : syracuseStep 1166825 = 875119) B875119
theorem B774623 : Blo 774336 774623 := bstep (se 1 (by rfl) ⟨580967, by rfl⟩ : syracuseStep 774623 = 1161935) B1161935
theorem B777883 : Blo 774336 777883 := bstep (se 1 (by rfl) ⟨583412, by rfl⟩ : syracuseStep 777883 = 1166825) B1166825

theorem C0 (j : ℕ) (h1 : 193584 ≤ j) (h2 : j ≤ 194283) : Blo 774336 (4 * j + 3) := by
  interval_cases j
  · exact B774339
  · exact B774343
  · exact B774347
  · exact B774351
  · exact B774355
  · exact B774359
  · exact B774363
  · exact B774367
  · exact B774371
  · exact B774375
  · exact B774379
  · exact B774383
  · exact B774387
  · exact B774391
  · exact B774395
  · exact B774399
  · exact B774403
  · exact B774407
  · exact B774411
  · exact B774415
  · exact B774419
  · exact B774423
  · exact B774427
  · exact B774431
  · exact B774435
  · exact B774439
  · exact B774443
  · exact B774447
  · exact B774451
  · exact B774455
  · exact B774459
  · exact B774463
  · exact B774467
  · exact B774471
  · exact B774475
  · exact B774479
  · exact B774483
  · exact B774487
  · exact B774491
  · exact B774495
  · exact B774499
  · exact B774503
  · exact B774507
  · exact B774511
  · exact B774515
  · exact B774519
  · exact B774523
  · exact B774527
  · exact B774531
  · exact B774535
  · exact B774539
  · exact B774543
  · exact B774547
  · exact B774551
  · exact B774555
  · exact B774559
  · exact B774563
  · exact B774567
  · exact B774571
  · exact B774575
  · exact B774579
  · exact B774583
  · exact B774587
  · exact B774591
  · exact B774595
  · exact B774599
  · exact B774603
  · exact B774607
  · exact B774611
  · exact B774615
  · exact B774619
  · exact B774623
  · exact B774627
  · exact B774631
  · exact B774635
  · exact B774639
  · exact B774643
  · exact B774647
  · exact B774651
  · exact B774655
  · exact B774659
  · exact B774663
  · exact B774667
  · exact B774671
  · exact B774675
  · exact B774679
  · exact B774683
  · exact B774687
  · exact B774691
  · exact B774695
  · exact B774699
  · exact B774703
  · exact B774707
  · exact B774711
  · exact B774715
  · exact B774719
  · exact B774723
  · exact B774727
  · exact B774731
  · exact B774735
  · exact B774739
  · exact B774743
  · exact B774747
  · exact B774751
  · exact B774755
  · exact B774759
  · exact B774763
  · exact B774767
  · exact B774771
  · exact B774775
  · exact B774779
  · exact B774783
  · exact B774787
  · exact B774791
  · exact B774795
  · exact B774799
  · exact B774803
  · exact B774807
  · exact B774811
  · exact B774815
  · exact B774819
  · exact B774823
  · exact B774827
  · exact B774831
  · exact B774835
  · exact B774839
  · exact B774843
  · exact B774847
  · exact B774851
  · exact B774855
  · exact B774859
  · exact B774863
  · exact B774867
  · exact B774871
  · exact B774875
  · exact B774879
  · exact B774883
  · exact B774887
  · exact B774891
  · exact B774895
  · exact B774899
  · exact B774903
  · exact B774907
  · exact B774911
  · exact B774915
  · exact B774919
  · exact B774923
  · exact B774927
  · exact B774931
  · exact B774935
  · exact B774939
  · exact B774943
  · exact B774947
  · exact B774951
  · exact B774955
  · exact B774959
  · exact B774963
  · exact B774967
  · exact B774971
  · exact B774975
  · exact B774979
  · exact B774983
  · exact B774987
  · exact B774991
  · exact B774995
  · exact B774999
  · exact B775003
  · exact B775007
  · exact B775011
  · exact B775015
  · exact B775019
  · exact B775023
  · exact B775027
  · exact B775031
  · exact B775035
  · exact B775039
  · exact B775043
  · exact B775047
  · exact B775051
  · exact B775055
  · exact B775059
  · exact B775063
  · exact B775067
  · exact B775071
  · exact B775075
  · exact B775079
  · exact B775083
  · exact B775087
  · exact B775091
  · exact B775095
  · exact B775099
  · exact B775103
  · exact B775107
  · exact B775111
  · exact B775115
  · exact B775119
  · exact B775123
  · exact B775127
  · exact B775131
  · exact B775135
  · exact B775139
  · exact B775143
  · exact B775147
  · exact B775151
  · exact B775155
  · exact B775159
  · exact B775163
  · exact B775167
  · exact B775171
  · exact B775175
  · exact B775179
  · exact B775183
  · exact B775187
  · exact B775191
  · exact B775195
  · exact B775199
  · exact B775203
  · exact B775207
  · exact B775211
  · exact B775215
  · exact B775219
  · exact B775223
  · exact B775227
  · exact B775231
  · exact B775235
  · exact B775239
  · exact B775243
  · exact B775247
  · exact B775251
  · exact B775255
  · exact B775259
  · exact B775263
  · exact B775267
  · exact B775271
  · exact B775275
  · exact B775279
  · exact B775283
  · exact B775287
  · exact B775291
  · exact B775295
  · exact B775299
  · exact B775303
  · exact B775307
  · exact B775311
  · exact B775315
  · exact B775319
  · exact B775323
  · exact B775327
  · exact B775331
  · exact B775335
  · exact B775339
  · exact B775343
  · exact B775347
  · exact B775351
  · exact B775355
  · exact B775359
  · exact B775363
  · exact B775367
  · exact B775371
  · exact B775375
  · exact B775379
  · exact B775383
  · exact B775387
  · exact B775391
  · exact B775395
  · exact B775399
  · exact B775403
  · exact B775407
  · exact B775411
  · exact B775415
  · exact B775419
  · exact B775423
  · exact B775427
  · exact B775431
  · exact B775435
  · exact B775439
  · exact B775443
  · exact B775447
  · exact B775451
  · exact B775455
  · exact B775459
  · exact B775463
  · exact B775467
  · exact B775471
  · exact B775475
  · exact B775479
  · exact B775483
  · exact B775487
  · exact B775491
  · exact B775495
  · exact B775499
  · exact B775503
  · exact B775507
  · exact B775511
  · exact B775515
  · exact B775519
  · exact B775523
  · exact B775527
  · exact B775531
  · exact B775535
  · exact B775539
  · exact B775543
  · exact B775547
  · exact B775551
  · exact B775555
  · exact B775559
  · exact B775563
  · exact B775567
  · exact B775571
  · exact B775575
  · exact B775579
  · exact B775583
  · exact B775587
  · exact B775591
  · exact B775595
  · exact B775599
  · exact B775603
  · exact B775607
  · exact B775611
  · exact B775615
  · exact B775619
  · exact B775623
  · exact B775627
  · exact B775631
  · exact B775635
  · exact B775639
  · exact B775643
  · exact B775647
  · exact B775651
  · exact B775655
  · exact B775659
  · exact B775663
  · exact B775667
  · exact B775671
  · exact B775675
  · exact B775679
  · exact B775683
  · exact B775687
  · exact B775691
  · exact B775695
  · exact B775699
  · exact B775703
  · exact B775707
  · exact B775711
  · exact B775715
  · exact B775719
  · exact B775723
  · exact B775727
  · exact B775731
  · exact B775735
  · exact B775739
  · exact B775743
  · exact B775747
  · exact B775751
  · exact B775755
  · exact B775759
  · exact B775763
  · exact B775767
  · exact B775771
  · exact B775775
  · exact B775779
  · exact B775783
  · exact B775787
  · exact B775791
  · exact B775795
  · exact B775799
  · exact B775803
  · exact B775807
  · exact B775811
  · exact B775815
  · exact B775819
  · exact B775823
  · exact B775827
  · exact B775831
  · exact B775835
  · exact B775839
  · exact B775843
  · exact B775847
  · exact B775851
  · exact B775855
  · exact B775859
  · exact B775863
  · exact B775867
  · exact B775871
  · exact B775875
  · exact B775879
  · exact B775883
  · exact B775887
  · exact B775891
  · exact B775895
  · exact B775899
  · exact B775903
  · exact B775907
  · exact B775911
  · exact B775915
  · exact B775919
  · exact B775923
  · exact B775927
  · exact B775931
  · exact B775935
  · exact B775939
  · exact B775943
  · exact B775947
  · exact B775951
  · exact B775955
  · exact B775959
  · exact B775963
  · exact B775967
  · exact B775971
  · exact B775975
  · exact B775979
  · exact B775983
  · exact B775987
  · exact B775991
  · exact B775995
  · exact B775999
  · exact B776003
  · exact B776007
  · exact B776011
  · exact B776015
  · exact B776019
  · exact B776023
  · exact B776027
  · exact B776031
  · exact B776035
  · exact B776039
  · exact B776043
  · exact B776047
  · exact B776051
  · exact B776055
  · exact B776059
  · exact B776063
  · exact B776067
  · exact B776071
  · exact B776075
  · exact B776079
  · exact B776083
  · exact B776087
  · exact B776091
  · exact B776095
  · exact B776099
  · exact B776103
  · exact B776107
  · exact B776111
  · exact B776115
  · exact B776119
  · exact B776123
  · exact B776127
  · exact B776131
  · exact B776135
  · exact B776139
  · exact B776143
  · exact B776147
  · exact B776151
  · exact B776155
  · exact B776159
  · exact B776163
  · exact B776167
  · exact B776171
  · exact B776175
  · exact B776179
  · exact B776183
  · exact B776187
  · exact B776191
  · exact B776195
  · exact B776199
  · exact B776203
  · exact B776207
  · exact B776211
  · exact B776215
  · exact B776219
  · exact B776223
  · exact B776227
  · exact B776231
  · exact B776235
  · exact B776239
  · exact B776243
  · exact B776247
  · exact B776251
  · exact B776255
  · exact B776259
  · exact B776263
  · exact B776267
  · exact B776271
  · exact B776275
  · exact B776279
  · exact B776283
  · exact B776287
  · exact B776291
  · exact B776295
  · exact B776299
  · exact B776303
  · exact B776307
  · exact B776311
  · exact B776315
  · exact B776319
  · exact B776323
  · exact B776327
  · exact B776331
  · exact B776335
  · exact B776339
  · exact B776343
  · exact B776347
  · exact B776351
  · exact B776355
  · exact B776359
  · exact B776363
  · exact B776367
  · exact B776371
  · exact B776375
  · exact B776379
  · exact B776383
  · exact B776387
  · exact B776391
  · exact B776395
  · exact B776399
  · exact B776403
  · exact B776407
  · exact B776411
  · exact B776415
  · exact B776419
  · exact B776423
  · exact B776427
  · exact B776431
  · exact B776435
  · exact B776439
  · exact B776443
  · exact B776447
  · exact B776451
  · exact B776455
  · exact B776459
  · exact B776463
  · exact B776467
  · exact B776471
  · exact B776475
  · exact B776479
  · exact B776483
  · exact B776487
  · exact B776491
  · exact B776495
  · exact B776499
  · exact B776503
  · exact B776507
  · exact B776511
  · exact B776515
  · exact B776519
  · exact B776523
  · exact B776527
  · exact B776531
  · exact B776535
  · exact B776539
  · exact B776543
  · exact B776547
  · exact B776551
  · exact B776555
  · exact B776559
  · exact B776563
  · exact B776567
  · exact B776571
  · exact B776575
  · exact B776579
  · exact B776583
  · exact B776587
  · exact B776591
  · exact B776595
  · exact B776599
  · exact B776603
  · exact B776607
  · exact B776611
  · exact B776615
  · exact B776619
  · exact B776623
  · exact B776627
  · exact B776631
  · exact B776635
  · exact B776639
  · exact B776643
  · exact B776647
  · exact B776651
  · exact B776655
  · exact B776659
  · exact B776663
  · exact B776667
  · exact B776671
  · exact B776675
  · exact B776679
  · exact B776683
  · exact B776687
  · exact B776691
  · exact B776695
  · exact B776699
  · exact B776703
  · exact B776707
  · exact B776711
  · exact B776715
  · exact B776719
  · exact B776723
  · exact B776727
  · exact B776731
  · exact B776735
  · exact B776739
  · exact B776743
  · exact B776747
  · exact B776751
  · exact B776755
  · exact B776759
  · exact B776763
  · exact B776767
  · exact B776771
  · exact B776775
  · exact B776779
  · exact B776783
  · exact B776787
  · exact B776791
  · exact B776795
  · exact B776799
  · exact B776803
  · exact B776807
  · exact B776811
  · exact B776815
  · exact B776819
  · exact B776823
  · exact B776827
  · exact B776831
  · exact B776835
  · exact B776839
  · exact B776843
  · exact B776847
  · exact B776851
  · exact B776855
  · exact B776859
  · exact B776863
  · exact B776867
  · exact B776871
  · exact B776875
  · exact B776879
  · exact B776883
  · exact B776887
  · exact B776891
  · exact B776895
  · exact B776899
  · exact B776903
  · exact B776907
  · exact B776911
  · exact B776915
  · exact B776919
  · exact B776923
  · exact B776927
  · exact B776931
  · exact B776935
  · exact B776939
  · exact B776943
  · exact B776947
  · exact B776951
  · exact B776955
  · exact B776959
  · exact B776963
  · exact B776967
  · exact B776971
  · exact B776975
  · exact B776979
  · exact B776983
  · exact B776987
  · exact B776991
  · exact B776995
  · exact B776999
  · exact B777003
  · exact B777007
  · exact B777011
  · exact B777015
  · exact B777019
  · exact B777023
  · exact B777027
  · exact B777031
  · exact B777035
  · exact B777039
  · exact B777043
  · exact B777047
  · exact B777051
  · exact B777055
  · exact B777059
  · exact B777063
  · exact B777067
  · exact B777071
  · exact B777075
  · exact B777079
  · exact B777083
  · exact B777087
  · exact B777091
  · exact B777095
  · exact B777099
  · exact B777103
  · exact B777107
  · exact B777111
  · exact B777115
  · exact B777119
  · exact B777123
  · exact B777127
  · exact B777131
  · exact B777135

theorem C1 (j : ℕ) (h1 : 194284 ≤ j) (h2 : j ≤ 194583) : Blo 774336 (4 * j + 3) := by
  interval_cases j
  · exact B777139
  · exact B777143
  · exact B777147
  · exact B777151
  · exact B777155
  · exact B777159
  · exact B777163
  · exact B777167
  · exact B777171
  · exact B777175
  · exact B777179
  · exact B777183
  · exact B777187
  · exact B777191
  · exact B777195
  · exact B777199
  · exact B777203
  · exact B777207
  · exact B777211
  · exact B777215
  · exact B777219
  · exact B777223
  · exact B777227
  · exact B777231
  · exact B777235
  · exact B777239
  · exact B777243
  · exact B777247
  · exact B777251
  · exact B777255
  · exact B777259
  · exact B777263
  · exact B777267
  · exact B777271
  · exact B777275
  · exact B777279
  · exact B777283
  · exact B777287
  · exact B777291
  · exact B777295
  · exact B777299
  · exact B777303
  · exact B777307
  · exact B777311
  · exact B777315
  · exact B777319
  · exact B777323
  · exact B777327
  · exact B777331
  · exact B777335
  · exact B777339
  · exact B777343
  · exact B777347
  · exact B777351
  · exact B777355
  · exact B777359
  · exact B777363
  · exact B777367
  · exact B777371
  · exact B777375
  · exact B777379
  · exact B777383
  · exact B777387
  · exact B777391
  · exact B777395
  · exact B777399
  · exact B777403
  · exact B777407
  · exact B777411
  · exact B777415
  · exact B777419
  · exact B777423
  · exact B777427
  · exact B777431
  · exact B777435
  · exact B777439
  · exact B777443
  · exact B777447
  · exact B777451
  · exact B777455
  · exact B777459
  · exact B777463
  · exact B777467
  · exact B777471
  · exact B777475
  · exact B777479
  · exact B777483
  · exact B777487
  · exact B777491
  · exact B777495
  · exact B777499
  · exact B777503
  · exact B777507
  · exact B777511
  · exact B777515
  · exact B777519
  · exact B777523
  · exact B777527
  · exact B777531
  · exact B777535
  · exact B777539
  · exact B777543
  · exact B777547
  · exact B777551
  · exact B777555
  · exact B777559
  · exact B777563
  · exact B777567
  · exact B777571
  · exact B777575
  · exact B777579
  · exact B777583
  · exact B777587
  · exact B777591
  · exact B777595
  · exact B777599
  · exact B777603
  · exact B777607
  · exact B777611
  · exact B777615
  · exact B777619
  · exact B777623
  · exact B777627
  · exact B777631
  · exact B777635
  · exact B777639
  · exact B777643
  · exact B777647
  · exact B777651
  · exact B777655
  · exact B777659
  · exact B777663
  · exact B777667
  · exact B777671
  · exact B777675
  · exact B777679
  · exact B777683
  · exact B777687
  · exact B777691
  · exact B777695
  · exact B777699
  · exact B777703
  · exact B777707
  · exact B777711
  · exact B777715
  · exact B777719
  · exact B777723
  · exact B777727
  · exact B777731
  · exact B777735
  · exact B777739
  · exact B777743
  · exact B777747
  · exact B777751
  · exact B777755
  · exact B777759
  · exact B777763
  · exact B777767
  · exact B777771
  · exact B777775
  · exact B777779
  · exact B777783
  · exact B777787
  · exact B777791
  · exact B777795
  · exact B777799
  · exact B777803
  · exact B777807
  · exact B777811
  · exact B777815
  · exact B777819
  · exact B777823
  · exact B777827
  · exact B777831
  · exact B777835
  · exact B777839
  · exact B777843
  · exact B777847
  · exact B777851
  · exact B777855
  · exact B777859
  · exact B777863
  · exact B777867
  · exact B777871
  · exact B777875
  · exact B777879
  · exact B777883
  · exact B777887
  · exact B777891
  · exact B777895
  · exact B777899
  · exact B777903
  · exact B777907
  · exact B777911
  · exact B777915
  · exact B777919
  · exact B777923
  · exact B777927
  · exact B777931
  · exact B777935
  · exact B777939
  · exact B777943
  · exact B777947
  · exact B777951
  · exact B777955
  · exact B777959
  · exact B777963
  · exact B777967
  · exact B777971
  · exact B777975
  · exact B777979
  · exact B777983
  · exact B777987
  · exact B777991
  · exact B777995
  · exact B777999
  · exact B778003
  · exact B778007
  · exact B778011
  · exact B778015
  · exact B778019
  · exact B778023
  · exact B778027
  · exact B778031
  · exact B778035
  · exact B778039
  · exact B778043
  · exact B778047
  · exact B778051
  · exact B778055
  · exact B778059
  · exact B778063
  · exact B778067
  · exact B778071
  · exact B778075
  · exact B778079
  · exact B778083
  · exact B778087
  · exact B778091
  · exact B778095
  · exact B778099
  · exact B778103
  · exact B778107
  · exact B778111
  · exact B778115
  · exact B778119
  · exact B778123
  · exact B778127
  · exact B778131
  · exact B778135
  · exact B778139
  · exact B778143
  · exact B778147
  · exact B778151
  · exact B778155
  · exact B778159
  · exact B778163
  · exact B778167
  · exact B778171
  · exact B778175
  · exact B778179
  · exact B778183
  · exact B778187
  · exact B778191
  · exact B778195
  · exact B778199
  · exact B778203
  · exact B778207
  · exact B778211
  · exact B778215
  · exact B778219
  · exact B778223
  · exact B778227
  · exact B778231
  · exact B778235
  · exact B778239
  · exact B778243
  · exact B778247
  · exact B778251
  · exact B778255
  · exact B778259
  · exact B778263
  · exact B778267
  · exact B778271
  · exact B778275
  · exact B778279
  · exact B778283
  · exact B778287
  · exact B778291
  · exact B778295
  · exact B778299
  · exact B778303
  · exact B778307
  · exact B778311
  · exact B778315
  · exact B778319
  · exact B778323
  · exact B778327
  · exact B778331
  · exact B778335

theorem solution (m : ℕ) (hlo : 774336 ≤ m) (hhi : m ≤ 778336) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 193584 ≤ j := by omega
    have hj2 : j ≤ 194583 := by omega
    have hb : Blo 774336 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 194284 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
