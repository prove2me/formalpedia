-- Prove2me | solution 1 for syracuse_descends_range_1211423_1213423
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:10:51.155432+00:00
-- url     : https://prove2.me/submissions/5ff28358-a2f9-4b93-84b2-cf7de585450c

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


theorem B1294337 : Blo 1211423 1294337 := bbase (se 2 (by rfl) ⟨485376, by rfl⟩ : syracuseStep 1294337 = 970753) (by norm_num)
theorem B1818629 : Blo 1211423 1818629 := bbase (se 4 (by rfl) ⟨170496, by rfl⟩ : syracuseStep 1818629 = 340993) (by norm_num)
theorem B1818653 : Blo 1211423 1818653 := bbase (se 3 (by rfl) ⟨340997, by rfl⟩ : syracuseStep 1818653 = 681995) (by norm_num)
theorem B2727989 : Blo 1211423 2727989 := bbase (se 5 (by rfl) ⟨127874, by rfl⟩ : syracuseStep 2727989 = 255749) (by norm_num)
theorem B1818677 : Blo 1211423 1818677 := bbase (se 5 (by rfl) ⟨85250, by rfl⟩ : syracuseStep 1818677 = 170501) (by norm_num)
theorem B1228861 : Blo 1211423 1228861 := bbase (se 3 (by rfl) ⟨230411, by rfl⟩ : syracuseStep 1228861 = 460823) (by norm_num)
theorem B1818701 : Blo 1211423 1818701 := bbase (se 3 (by rfl) ⟨341006, by rfl⟩ : syracuseStep 1818701 = 682013) (by norm_num)
theorem B29491285 : Blo 1211423 29491285 := bbase (se 8 (by rfl) ⟨172800, by rfl⟩ : syracuseStep 29491285 = 345601) (by norm_num)
theorem B3686485 : Blo 1211423 3686485 := bbase (se 8 (by rfl) ⟨21600, by rfl⟩ : syracuseStep 3686485 = 43201) (by norm_num)
theorem B1818725 : Blo 1211423 1818725 := bbase (se 4 (by rfl) ⟨170505, by rfl⟩ : syracuseStep 1818725 = 341011) (by norm_num)
theorem B2728061 : Blo 1211423 2728061 := bbase (se 3 (by rfl) ⟨511511, by rfl⟩ : syracuseStep 2728061 = 1023023) (by norm_num)
theorem B1818749 : Blo 1211423 1818749 := bbase (se 3 (by rfl) ⟨341015, by rfl⟩ : syracuseStep 1818749 = 682031) (by norm_num)
theorem B1294465 : Blo 1211423 1294465 := bbase (se 2 (by rfl) ⟨485424, by rfl⟩ : syracuseStep 1294465 = 970849) (by norm_num)
theorem B1818773 : Blo 1211423 1818773 := bbase (se 6 (by rfl) ⟨42627, by rfl⟩ : syracuseStep 1818773 = 85255) (by norm_num)
theorem B1818797 : Blo 1211423 1818797 := bbase (se 3 (by rfl) ⟨341024, by rfl⟩ : syracuseStep 1818797 = 682049) (by norm_num)
theorem B2728133 : Blo 1211423 2728133 := bbase (se 4 (by rfl) ⟨255762, by rfl⟩ : syracuseStep 2728133 = 511525) (by norm_num)
theorem B1818821 : Blo 1211423 1818821 := bbase (se 4 (by rfl) ⟨170514, by rfl⟩ : syracuseStep 1818821 = 341029) (by norm_num)
theorem B1818845 : Blo 1211423 1818845 := bbase (se 3 (by rfl) ⟨341033, by rfl⟩ : syracuseStep 1818845 = 682067) (by norm_num)
theorem B1941749 : Blo 1211423 1941749 := bbase (se 5 (by rfl) ⟨91019, by rfl⟩ : syracuseStep 1941749 = 182039) (by norm_num)
theorem B1818869 : Blo 1211423 1818869 := bbase (se 5 (by rfl) ⟨85259, by rfl⟩ : syracuseStep 1818869 = 170519) (by norm_num)
theorem B2728205 : Blo 1211423 2728205 := bbase (se 3 (by rfl) ⟨511538, by rfl⟩ : syracuseStep 2728205 = 1023077) (by norm_num)
theorem B1818893 : Blo 1211423 1818893 := bbase (se 3 (by rfl) ⟨341042, by rfl⟩ : syracuseStep 1818893 = 682085) (by norm_num)
theorem B5177621 : Blo 1211423 5177621 := bbase (se 6 (by rfl) ⟨121350, by rfl⟩ : syracuseStep 5177621 = 242701) (by norm_num)
theorem B1818917 : Blo 1211423 1818917 := bbase (se 4 (by rfl) ⟨170523, by rfl⟩ : syracuseStep 1818917 = 341047) (by norm_num)
theorem B1818941 : Blo 1211423 1818941 := bbase (se 3 (by rfl) ⟨341051, by rfl⟩ : syracuseStep 1818941 = 682103) (by norm_num)
theorem B2728277 : Blo 1211423 2728277 := bbase (se 10 (by rfl) ⟨3996, by rfl⟩ : syracuseStep 2728277 = 7993) (by norm_num)
theorem B1818965 : Blo 1211423 1818965 := bbase (se 10 (by rfl) ⟨2664, by rfl⟩ : syracuseStep 1818965 = 5329) (by norm_num)
theorem B1818989 : Blo 1211423 1818989 := bbase (se 3 (by rfl) ⟨341060, by rfl⟩ : syracuseStep 1818989 = 682121) (by norm_num)
theorem B2457973 : Blo 1211423 2457973 := bbase (se 5 (by rfl) ⟨115217, by rfl⟩ : syracuseStep 2457973 = 230435) (by norm_num)
theorem B1819013 : Blo 1211423 1819013 := bbase (se 4 (by rfl) ⟨170532, by rfl⟩ : syracuseStep 1819013 = 341065) (by norm_num)
theorem B2302357 : Blo 1211423 2302357 := bbase (se 6 (by rfl) ⟨53961, by rfl⟩ : syracuseStep 2302357 = 107923) (by norm_num)
theorem B2728349 : Blo 1211423 2728349 := bbase (se 3 (by rfl) ⟨511565, by rfl⟩ : syracuseStep 2728349 = 1023131) (by norm_num)
theorem B1819037 : Blo 1211423 1819037 := bbase (se 3 (by rfl) ⟨341069, by rfl⟩ : syracuseStep 1819037 = 682139) (by norm_num)
theorem B2589101 : Blo 1211423 2589101 := bbase (se 3 (by rfl) ⟨485456, by rfl⟩ : syracuseStep 2589101 = 970913) (by norm_num)
theorem B1819061 : Blo 1211423 1819061 := bbase (se 5 (by rfl) ⟨85268, by rfl⟩ : syracuseStep 1819061 = 170537) (by norm_num)
theorem B1819085 : Blo 1211423 1819085 := bbase (se 3 (by rfl) ⟨341078, by rfl⟩ : syracuseStep 1819085 = 682157) (by norm_num)
theorem B2728421 : Blo 1211423 2728421 := bbase (se 4 (by rfl) ⟨255789, by rfl⟩ : syracuseStep 2728421 = 511579) (by norm_num)
theorem B1819109 : Blo 1211423 1819109 := bbase (se 4 (by rfl) ⟨170541, by rfl⟩ : syracuseStep 1819109 = 341083) (by norm_num)
theorem B1819133 : Blo 1211423 1819133 := bbase (se 3 (by rfl) ⟨341087, by rfl⟩ : syracuseStep 1819133 = 682175) (by norm_num)
theorem B1819157 : Blo 1211423 1819157 := bbase (se 6 (by rfl) ⟨42636, by rfl⟩ : syracuseStep 1819157 = 85273) (by norm_num)
theorem B2589221 : Blo 1211423 2589221 := bbase (se 4 (by rfl) ⟨242739, by rfl⟩ : syracuseStep 2589221 = 485479) (by norm_num)
theorem B2302501 : Blo 1211423 2302501 := bbase (se 4 (by rfl) ⟨215859, by rfl⟩ : syracuseStep 2302501 = 431719) (by norm_num)
theorem B2728493 : Blo 1211423 2728493 := bbase (se 3 (by rfl) ⟨511592, by rfl⟩ : syracuseStep 2728493 = 1023185) (by norm_num)
theorem B1819181 : Blo 1211423 1819181 := bbase (se 3 (by rfl) ⟨341096, by rfl⟩ : syracuseStep 1819181 = 682193) (by norm_num)
theorem B1294909 : Blo 1211423 1294909 := bbase (se 3 (by rfl) ⟨242795, by rfl⟩ : syracuseStep 1294909 = 485591) (by norm_num)
theorem B3883589 : Blo 1211423 3883589 := bbase (se 4 (by rfl) ⟨364086, by rfl⟩ : syracuseStep 3883589 = 728173) (by norm_num)
theorem B4604485 : Blo 1211423 4604485 := bbase (se 4 (by rfl) ⟨431670, by rfl⟩ : syracuseStep 4604485 = 863341) (by norm_num)
theorem B1819205 : Blo 1211423 1819205 := bbase (se 4 (by rfl) ⟨170550, by rfl⟩ : syracuseStep 1819205 = 341101) (by norm_num)
theorem B1819229 : Blo 1211423 1819229 := bbase (se 3 (by rfl) ⟨341105, by rfl⟩ : syracuseStep 1819229 = 682211) (by norm_num)
theorem B2728565 : Blo 1211423 2728565 := bbase (se 5 (by rfl) ⟨127901, by rfl⟩ : syracuseStep 2728565 = 255803) (by norm_num)
theorem B1819253 : Blo 1211423 1819253 := bbase (se 5 (by rfl) ⟨85277, by rfl⟩ : syracuseStep 1819253 = 170555) (by norm_num)
theorem B1311373 : Blo 1211423 1311373 := bbase (se 3 (by rfl) ⟨245882, by rfl⟩ : syracuseStep 1311373 = 491765) (by norm_num)
theorem B1819277 : Blo 1211423 1819277 := bbase (se 3 (by rfl) ⟨341114, by rfl⟩ : syracuseStep 1819277 = 682229) (by norm_num)
theorem B1819301 : Blo 1211423 1819301 := bbase (se 4 (by rfl) ⟨170559, by rfl⟩ : syracuseStep 1819301 = 341119) (by norm_num)
theorem B1401517 : Blo 1211423 1401517 := bbase (se 3 (by rfl) ⟨262784, by rfl⟩ : syracuseStep 1401517 = 525569) (by norm_num)
theorem B1295029 : Blo 1211423 1295029 := bbase (se 5 (by rfl) ⟨60704, by rfl⟩ : syracuseStep 1295029 = 121409) (by norm_num)
theorem B2728637 : Blo 1211423 2728637 := bbase (se 3 (by rfl) ⟨511619, by rfl⟩ : syracuseStep 2728637 = 1023239) (by norm_num)
theorem B1819325 : Blo 1211423 1819325 := bbase (se 3 (by rfl) ⟨341123, by rfl⟩ : syracuseStep 1819325 = 682247) (by norm_num)
theorem B2302661 : Blo 1211423 2302661 := bbase (se 4 (by rfl) ⟨215874, by rfl⟩ : syracuseStep 2302661 = 431749) (by norm_num)
theorem B1819349 : Blo 1211423 1819349 := bbase (se 7 (by rfl) ⟨21320, by rfl⟩ : syracuseStep 1819349 = 42641) (by norm_num)
theorem B1819373 : Blo 1211423 1819373 := bbase (se 3 (by rfl) ⟨341132, by rfl⟩ : syracuseStep 1819373 = 682265) (by norm_num)
theorem B6554357 : Blo 1211423 6554357 := bbase (se 5 (by rfl) ⟨307235, by rfl⟩ : syracuseStep 6554357 = 614471) (by norm_num)
theorem B1942261 : Blo 1211423 1942261 := bbase (se 5 (by rfl) ⟨91043, by rfl⟩ : syracuseStep 1942261 = 182087) (by norm_num)
theorem B8741621 : Blo 1211423 8741621 := bbase (se 5 (by rfl) ⟨409763, by rfl⟩ : syracuseStep 8741621 = 819527) (by norm_num)
theorem B2728709 : Blo 1211423 2728709 := bbase (se 4 (by rfl) ⟨255816, by rfl⟩ : syracuseStep 2728709 = 511633) (by norm_num)
theorem B1819397 : Blo 1211423 1819397 := bbase (se 4 (by rfl) ⟨170568, by rfl⟩ : syracuseStep 1819397 = 341137) (by norm_num)
theorem B3498773 : Blo 1211423 3498773 := bbase (se 6 (by rfl) ⟨82002, by rfl⟩ : syracuseStep 3498773 = 164005) (by norm_num)
theorem B1819421 : Blo 1211423 1819421 := bbase (se 3 (by rfl) ⟨341141, by rfl⟩ : syracuseStep 1819421 = 682283) (by norm_num)
theorem B1819445 : Blo 1211423 1819445 := bbase (se 5 (by rfl) ⟨85286, by rfl⟩ : syracuseStep 1819445 = 170573) (by norm_num)
theorem B2728781 : Blo 1211423 2728781 := bbase (se 3 (by rfl) ⟨511646, by rfl⟩ : syracuseStep 2728781 = 1023293) (by norm_num)
theorem B1819469 : Blo 1211423 1819469 := bbase (se 3 (by rfl) ⟨341150, by rfl⟩ : syracuseStep 1819469 = 682301) (by norm_num)
theorem B19653461 : Blo 1211423 19653461 := bbase (se 9 (by rfl) ⟨57578, by rfl⟩ : syracuseStep 19653461 = 115157) (by norm_num)
theorem B2302805 : Blo 1211423 2302805 := bbase (se 9 (by rfl) ⟨6746, by rfl⟩ : syracuseStep 2302805 = 13493) (by norm_num)
theorem B59024213 : Blo 1211423 59024213 := bbase (se 9 (by rfl) ⟨172922, by rfl⟩ : syracuseStep 59024213 = 345845) (by norm_num)
theorem B1819493 : Blo 1211423 1819493 := bbase (se 4 (by rfl) ⟨170577, by rfl⟩ : syracuseStep 1819493 = 341155) (by norm_num)
theorem B4604789 : Blo 1211423 4604789 := bbase (se 5 (by rfl) ⟨215849, by rfl⟩ : syracuseStep 4604789 = 431699) (by norm_num)
theorem B1819517 : Blo 1211423 1819517 := bbase (se 3 (by rfl) ⟨341159, by rfl⟩ : syracuseStep 1819517 = 682319) (by norm_num)
theorem B2728853 : Blo 1211423 2728853 := bbase (se 6 (by rfl) ⟨63957, by rfl⟩ : syracuseStep 2728853 = 127915) (by norm_num)
theorem B1819541 : Blo 1211423 1819541 := bbase (se 6 (by rfl) ⟨42645, by rfl⟩ : syracuseStep 1819541 = 85291) (by norm_num)
theorem B3449765 : Blo 1211423 3449765 := bbase (se 4 (by rfl) ⟨323415, by rfl⟩ : syracuseStep 3449765 = 646831) (by norm_num)
theorem B1819565 : Blo 1211423 1819565 := bbase (se 3 (by rfl) ⟨341168, by rfl⟩ : syracuseStep 1819565 = 682337) (by norm_num)
theorem B1295281 : Blo 1211423 1295281 := bbase (se 2 (by rfl) ⟨485730, by rfl⟩ : syracuseStep 1295281 = 971461) (by norm_num)
theorem B1295285 : Blo 1211423 1295285 := bbase (se 5 (by rfl) ⟨60716, by rfl⟩ : syracuseStep 1295285 = 121433) (by norm_num)
theorem B1819589 : Blo 1211423 1819589 := bbase (se 4 (by rfl) ⟨170586, by rfl⟩ : syracuseStep 1819589 = 341173) (by norm_num)
theorem B2728925 : Blo 1211423 2728925 := bbase (se 3 (by rfl) ⟨511673, by rfl⟩ : syracuseStep 2728925 = 1023347) (by norm_num)
theorem B1819613 : Blo 1211423 1819613 := bbase (se 3 (by rfl) ⟨341177, by rfl⟩ : syracuseStep 1819613 = 682355) (by norm_num)
theorem B1819637 : Blo 1211423 1819637 := bbase (se 5 (by rfl) ⟨85295, by rfl⟩ : syracuseStep 1819637 = 170591) (by norm_num)
theorem B1819661 : Blo 1211423 1819661 := bbase (se 3 (by rfl) ⟨341186, by rfl⟩ : syracuseStep 1819661 = 682373) (by norm_num)
theorem B2728997 : Blo 1211423 2728997 := bbase (se 4 (by rfl) ⟨255843, by rfl⟩ : syracuseStep 2728997 = 511687) (by norm_num)
theorem B1819685 : Blo 1211423 1819685 := bbase (se 4 (by rfl) ⟨170595, by rfl⟩ : syracuseStep 1819685 = 341191) (by norm_num)
theorem B1819709 : Blo 1211423 1819709 := bbase (se 3 (by rfl) ⟨341195, by rfl⟩ : syracuseStep 1819709 = 682391) (by norm_num)
theorem B1819733 : Blo 1211423 1819733 := bbase (se 8 (by rfl) ⟨10662, by rfl⟩ : syracuseStep 1819733 = 21325) (by norm_num)
theorem B4088933 : Blo 1211423 4088933 := bbase (se 4 (by rfl) ⟨383337, by rfl⟩ : syracuseStep 4088933 = 766675) (by norm_num)
theorem B2729069 : Blo 1211423 2729069 := bbase (se 3 (by rfl) ⟨511700, by rfl⟩ : syracuseStep 2729069 = 1023401) (by norm_num)
theorem B1819757 : Blo 1211423 1819757 := bbase (se 3 (by rfl) ⟨341204, by rfl⟩ : syracuseStep 1819757 = 682409) (by norm_num)
theorem B2303093 : Blo 1211423 2303093 := bbase (se 5 (by rfl) ⟨107957, by rfl⟩ : syracuseStep 2303093 = 215915) (by norm_num)
theorem B1819781 : Blo 1211423 1819781 := bbase (se 4 (by rfl) ⟨170604, by rfl⟩ : syracuseStep 1819781 = 341209) (by norm_num)
theorem B2589853 : Blo 1211423 2589853 := bbase (se 3 (by rfl) ⟨485597, by rfl⟩ : syracuseStep 2589853 = 971195) (by norm_num)
theorem B1819805 : Blo 1211423 1819805 := bbase (se 3 (by rfl) ⟨341213, by rfl⟩ : syracuseStep 1819805 = 682427) (by norm_num)
theorem B2729141 : Blo 1211423 2729141 := bbase (se 5 (by rfl) ⟨127928, by rfl⟩ : syracuseStep 2729141 = 255857) (by norm_num)
theorem B1819829 : Blo 1211423 1819829 := bbase (se 5 (by rfl) ⟨85304, by rfl⟩ : syracuseStep 1819829 = 170609) (by norm_num)
theorem B1942717 : Blo 1211423 1942717 := bbase (se 3 (by rfl) ⟨364259, by rfl⟩ : syracuseStep 1942717 = 728519) (by norm_num)
theorem B1819853 : Blo 1211423 1819853 := bbase (se 3 (by rfl) ⟨341222, by rfl⟩ : syracuseStep 1819853 = 682445) (by norm_num)
theorem B6137045 : Blo 1211423 6137045 := bbase (se 7 (by rfl) ⟨71918, by rfl⟩ : syracuseStep 6137045 = 143837) (by norm_num)
theorem B1819877 : Blo 1211423 1819877 := bbase (se 4 (by rfl) ⟨170613, by rfl⟩ : syracuseStep 1819877 = 341227) (by norm_num)
theorem B2729213 : Blo 1211423 2729213 := bbase (se 3 (by rfl) ⟨511727, by rfl⟩ : syracuseStep 2729213 = 1023455) (by norm_num)
theorem B1819901 : Blo 1211423 1819901 := bbase (se 3 (by rfl) ⟨341231, by rfl⟩ : syracuseStep 1819901 = 682463) (by norm_num)
theorem B2303245 : Blo 1211423 2303245 := bbase (se 3 (by rfl) ⟨431858, by rfl⟩ : syracuseStep 2303245 = 863717) (by norm_num)
theorem B1819925 : Blo 1211423 1819925 := bbase (se 6 (by rfl) ⟨42654, by rfl⟩ : syracuseStep 1819925 = 85309) (by norm_num)
theorem B1819949 : Blo 1211423 1819949 := bbase (se 3 (by rfl) ⟨341240, by rfl⟩ : syracuseStep 1819949 = 682481) (by norm_num)
theorem B5825861 : Blo 1211423 5825861 := bbase (se 4 (by rfl) ⟨546174, by rfl⟩ : syracuseStep 5825861 = 1092349) (by norm_num)
theorem B2729285 : Blo 1211423 2729285 := bbase (se 4 (by rfl) ⟨255870, by rfl⟩ : syracuseStep 2729285 = 511741) (by norm_num)
theorem B1819973 : Blo 1211423 1819973 := bbase (se 4 (by rfl) ⟨170622, by rfl⟩ : syracuseStep 1819973 = 341245) (by norm_num)
theorem B1533269 : Blo 1211423 1533269 := bbase (se 12 (by rfl) ⟨561, by rfl⟩ : syracuseStep 1533269 = 1123) (by norm_num)
theorem B1819997 : Blo 1211423 1819997 := bbase (se 3 (by rfl) ⟨341249, by rfl⟩ : syracuseStep 1819997 = 682499) (by norm_num)
theorem B1820021 : Blo 1211423 1820021 := bbase (se 5 (by rfl) ⟨85313, by rfl⟩ : syracuseStep 1820021 = 170627) (by norm_num)
theorem B1533325 : Blo 1211423 1533325 := bbase (se 3 (by rfl) ⟨287498, by rfl⟩ : syracuseStep 1533325 = 574997) (by norm_num)
theorem B2729357 : Blo 1211423 2729357 := bbase (se 3 (by rfl) ⟨511754, by rfl⟩ : syracuseStep 2729357 = 1023509) (by norm_num)
theorem B1820045 : Blo 1211423 1820045 := bbase (se 3 (by rfl) ⟨341258, by rfl⟩ : syracuseStep 1820045 = 682517) (by norm_num)
theorem B1820069 : Blo 1211423 1820069 := bbase (se 4 (by rfl) ⟨170631, by rfl⟩ : syracuseStep 1820069 = 341263) (by norm_num)
theorem B1820093 : Blo 1211423 1820093 := bbase (se 3 (by rfl) ⟨341267, by rfl⟩ : syracuseStep 1820093 = 682535) (by norm_num)
theorem B2729429 : Blo 1211423 2729429 := bbase (se 7 (by rfl) ⟨31985, by rfl⟩ : syracuseStep 2729429 = 63971) (by norm_num)
theorem B1820117 : Blo 1211423 1820117 := bbase (se 7 (by rfl) ⟨21329, by rfl⟩ : syracuseStep 1820117 = 42659) (by norm_num)
theorem B1533421 : Blo 1211423 1533421 := bbase (se 3 (by rfl) ⟨287516, by rfl⟩ : syracuseStep 1533421 = 575033) (by norm_num)
theorem B1476085 : Blo 1211423 1476085 := bbase (se 5 (by rfl) ⟨69191, by rfl⟩ : syracuseStep 1476085 = 138383) (by norm_num)
theorem B4089365 : Blo 1211423 4089365 := bbase (se 6 (by rfl) ⟨95844, by rfl⟩ : syracuseStep 4089365 = 191689) (by norm_num)
theorem B2729501 : Blo 1211423 2729501 := bbase (se 3 (by rfl) ⟨511781, by rfl⟩ : syracuseStep 2729501 = 1023563) (by norm_num)
theorem B5678629 : Blo 1211423 5678629 := bbase (se 4 (by rfl) ⟨532371, by rfl⟩ : syracuseStep 5678629 = 1064743) (by norm_num)
theorem B1639973 : Blo 1211423 1639973 := bbase (se 4 (by rfl) ⟨153747, by rfl⟩ : syracuseStep 1639973 = 307495) (by norm_num)
theorem B2303549 : Blo 1211423 2303549 := bbase (se 3 (by rfl) ⟨431915, by rfl⟩ : syracuseStep 2303549 = 863831) (by norm_num)
theorem B30721621 : Blo 1211423 30721621 := bbase (se 8 (by rfl) ⟨180009, by rfl⟩ : syracuseStep 30721621 = 360019) (by norm_num)
theorem B2729573 : Blo 1211423 2729573 := bbase (se 4 (by rfl) ⟨255897, by rfl⟩ : syracuseStep 2729573 = 511795) (by norm_num)
theorem B2950805 : Blo 1211423 2950805 := bbase (se 6 (by rfl) ⟨69159, by rfl⟩ : syracuseStep 2950805 = 138319) (by norm_num)
theorem B1533593 : Blo 1211423 1533593 := bbase (se 2 (by rfl) ⟨575097, by rfl⟩ : syracuseStep 1533593 = 1150195) (by norm_num)
theorem B2729645 : Blo 1211423 2729645 := bbase (se 3 (by rfl) ⟨511808, by rfl⟩ : syracuseStep 2729645 = 1023617) (by norm_num)
theorem B5531333 : Blo 1211423 5531333 := bbase (se 4 (by rfl) ⟨518562, by rfl⟩ : syracuseStep 5531333 = 1037125) (by norm_num)
theorem B1533649 : Blo 1211423 1533649 := bbase (se 2 (by rfl) ⟨575118, by rfl⟩ : syracuseStep 1533649 = 1150237) (by norm_num)
theorem B2729717 : Blo 1211423 2729717 := bbase (se 5 (by rfl) ⟨127955, by rfl⟩ : syracuseStep 2729717 = 255911) (by norm_num)
theorem B1533745 : Blo 1211423 1533745 := bbase (se 2 (by rfl) ⟨575154, by rfl⟩ : syracuseStep 1533745 = 1150309) (by norm_num)
theorem B2729789 : Blo 1211423 2729789 := bbase (se 3 (by rfl) ⟨511835, by rfl⟩ : syracuseStep 2729789 = 1023671) (by norm_num)
theorem B3499861 : Blo 1211423 3499861 := bbase (se 9 (by rfl) ⟨10253, by rfl⟩ : syracuseStep 3499861 = 20507) (by norm_num)
theorem B1943389 : Blo 1211423 1943389 := bbase (se 3 (by rfl) ⟨364385, by rfl⟩ : syracuseStep 1943389 = 728771) (by norm_num)
theorem B2729861 : Blo 1211423 2729861 := bbase (se 4 (by rfl) ⟨255924, by rfl⟩ : syracuseStep 2729861 = 511849) (by norm_num)
theorem B4089797 : Blo 1211423 4089797 := bbase (se 4 (by rfl) ⟨383418, by rfl⟩ : syracuseStep 4089797 = 766837) (by norm_num)
theorem B2729933 : Blo 1211423 2729933 := bbase (se 3 (by rfl) ⟨511862, by rfl⟩ : syracuseStep 2729933 = 1023725) (by norm_num)
theorem B1533917 : Blo 1211423 1533917 := bbase (se 3 (by rfl) ⟨287609, by rfl⟩ : syracuseStep 1533917 = 575219) (by norm_num)
theorem B1533973 : Blo 1211423 1533973 := bbase (se 6 (by rfl) ⟨35952, by rfl⟩ : syracuseStep 1533973 = 71905) (by norm_num)
theorem B20719637 : Blo 1211423 20719637 := bbase (se 6 (by rfl) ⟨485616, by rfl⟩ : syracuseStep 20719637 = 971233) (by norm_num)
theorem B2590741 : Blo 1211423 2590741 := bbase (se 6 (by rfl) ⟨60720, by rfl⟩ : syracuseStep 2590741 = 121441) (by norm_num)
theorem B2730005 : Blo 1211423 2730005 := bbase (se 6 (by rfl) ⟨63984, by rfl⟩ : syracuseStep 2730005 = 127969) (by norm_num)
theorem B5826613 : Blo 1211423 5826613 := bbase (se 5 (by rfl) ⟨273122, by rfl⟩ : syracuseStep 5826613 = 546245) (by norm_num)
theorem B2730077 : Blo 1211423 2730077 := bbase (se 3 (by rfl) ⟨511889, by rfl⟩ : syracuseStep 2730077 = 1023779) (by norm_num)
theorem B1534069 : Blo 1211423 1534069 := bbase (se 5 (by rfl) ⟨71909, by rfl⟩ : syracuseStep 1534069 = 143819) (by norm_num)
theorem B2590861 : Blo 1211423 2590861 := bbase (se 3 (by rfl) ⟨485786, by rfl⟩ : syracuseStep 2590861 = 971573) (by norm_num)
theorem B2730149 : Blo 1211423 2730149 := bbase (se 4 (by rfl) ⟨255951, by rfl⟩ : syracuseStep 2730149 = 511903) (by norm_num)
theorem B2074901 : Blo 1211423 2074901 := bbase (se 6 (by rfl) ⟨48630, by rfl⟩ : syracuseStep 2074901 = 97261) (by norm_num)
theorem B1534241 : Blo 1211423 1534241 := bbase (se 2 (by rfl) ⟨575340, by rfl⟩ : syracuseStep 1534241 = 1150681) (by norm_num)
theorem B1534297 : Blo 1211423 1534297 := bbase (se 2 (by rfl) ⟨575361, by rfl⟩ : syracuseStep 1534297 = 1150723) (by norm_num)
theorem B4090229 : Blo 1211423 4090229 := bbase (se 5 (by rfl) ⟨191729, by rfl⟩ : syracuseStep 4090229 = 383459) (by norm_num)
theorem B3885445 : Blo 1211423 3885445 := bbase (se 4 (by rfl) ⟨364260, by rfl⟩ : syracuseStep 3885445 = 728521) (by norm_num)
theorem B1477001 : Blo 1211423 1477001 := bbase (se 2 (by rfl) ⟨553875, by rfl⟩ : syracuseStep 1477001 = 1107751) (by norm_num)
theorem B2591117 : Blo 1211423 2591117 := bbase (se 3 (by rfl) ⟨485834, by rfl⟩ : syracuseStep 2591117 = 971669) (by norm_num)
theorem B3279253 : Blo 1211423 3279253 := bbase (se 6 (by rfl) ⟨76857, by rfl⟩ : syracuseStep 3279253 = 153715) (by norm_num)
theorem B1534393 : Blo 1211423 1534393 := bbase (se 2 (by rfl) ⟨575397, by rfl⟩ : syracuseStep 1534393 = 1150795) (by norm_num)
theorem B3451349 : Blo 1211423 3451349 := bbase (se 7 (by rfl) ⟨40445, by rfl⟩ : syracuseStep 3451349 = 80891) (by norm_num)
theorem B6138341 : Blo 1211423 6138341 := bbase (se 4 (by rfl) ⟨575469, by rfl⟩ : syracuseStep 6138341 = 1150939) (by norm_num)
theorem B2910701 : Blo 1211423 2910701 := bbase (se 3 (by rfl) ⟨545756, by rfl⟩ : syracuseStep 2910701 = 1091513) (by norm_num)
theorem B3066437 : Blo 1211423 3066437 := bbase (se 4 (by rfl) ⟨287478, by rfl⟩ : syracuseStep 3066437 = 574957) (by norm_num)
theorem B1534565 : Blo 1211423 1534565 := bbase (se 4 (by rfl) ⟨143865, by rfl⟩ : syracuseStep 1534565 = 287731) (by norm_num)
theorem B1534621 : Blo 1211423 1534621 := bbase (se 3 (by rfl) ⟨287741, by rfl⟩ : syracuseStep 1534621 = 575483) (by norm_num)
theorem B6908597 : Blo 1211423 6908597 := bbase (se 5 (by rfl) ⟨323840, by rfl⟩ : syracuseStep 6908597 = 647681) (by norm_num)
theorem B1534717 : Blo 1211423 1534717 := bbase (se 3 (by rfl) ⟨287759, by rfl⟩ : syracuseStep 1534717 = 575519) (by norm_num)
theorem B4983557 : Blo 1211423 4983557 := bbase (se 4 (by rfl) ⟨467208, by rfl⟩ : syracuseStep 4983557 = 934417) (by norm_num)
theorem B17705749 : Blo 1211423 17705749 := bbase (se 6 (by rfl) ⟨414978, by rfl⟩ : syracuseStep 17705749 = 829957) (by norm_num)
theorem B13814549 : Blo 1211423 13814549 := bbase (se 6 (by rfl) ⟨323778, by rfl⟩ : syracuseStep 13814549 = 647557) (by norm_num)
theorem B4090661 : Blo 1211423 4090661 := bbase (se 4 (by rfl) ⟨383499, by rfl⟩ : syracuseStep 4090661 = 766999) (by norm_num)
theorem B1477477 : Blo 1211423 1477477 := bbase (se 4 (by rfl) ⟨138513, by rfl⟩ : syracuseStep 1477477 = 277027) (by norm_num)
theorem B3066781 : Blo 1211423 3066781 := bbase (se 3 (by rfl) ⟨575021, by rfl⟩ : syracuseStep 3066781 = 1150043) (by norm_num)
theorem B1534889 : Blo 1211423 1534889 := bbase (se 2 (by rfl) ⟨575583, by rfl⟩ : syracuseStep 1534889 = 1151167) (by norm_num)
theorem B1362865 : Blo 1211423 1362865 := bbase (se 2 (by rfl) ⟨511074, by rfl⟩ : syracuseStep 1362865 = 1022149) (by norm_num)
theorem B4606901 : Blo 1211423 4606901 := bbase (se 5 (by rfl) ⟨215948, by rfl⟩ : syracuseStep 4606901 = 431897) (by norm_num)
theorem B1362901 : Blo 1211423 1362901 := bbase (se 7 (by rfl) ⟨15971, by rfl⟩ : syracuseStep 1362901 = 31943) (by norm_num)
theorem B1534945 : Blo 1211423 1534945 := bbase (se 2 (by rfl) ⟨575604, by rfl⟩ : syracuseStep 1534945 = 1151209) (by norm_num)
theorem B1362937 : Blo 1211423 1362937 := bbase (se 2 (by rfl) ⟨511101, by rfl⟩ : syracuseStep 1362937 = 1022203) (by norm_num)
theorem B3066893 : Blo 1211423 3066893 := bbase (se 3 (by rfl) ⟨575042, by rfl⟩ : syracuseStep 3066893 = 1150085) (by norm_num)
theorem B1362973 : Blo 1211423 1362973 := bbase (se 3 (by rfl) ⟨255557, by rfl⟩ : syracuseStep 1362973 = 511115) (by norm_num)
theorem B1363009 : Blo 1211423 1363009 := bbase (se 2 (by rfl) ⟨511128, by rfl⟩ : syracuseStep 1363009 = 1022257) (by norm_num)
theorem B1535041 : Blo 1211423 1535041 := bbase (se 2 (by rfl) ⟨575640, by rfl⟩ : syracuseStep 1535041 = 1151281) (by norm_num)
theorem B4148309 : Blo 1211423 4148309 := bbase (se 8 (by rfl) ⟨24306, by rfl⟩ : syracuseStep 4148309 = 48613) (by norm_num)
theorem B1363045 : Blo 1211423 1363045 := bbase (se 4 (by rfl) ⟨127785, by rfl⟩ : syracuseStep 1363045 = 255571) (by norm_num)
theorem B3452021 : Blo 1211423 3452021 := bbase (se 5 (by rfl) ⟨161813, by rfl⟩ : syracuseStep 3452021 = 323627) (by norm_num)
theorem B1363081 : Blo 1211423 1363081 := bbase (se 2 (by rfl) ⟨511155, by rfl⟩ : syracuseStep 1363081 = 1022311) (by norm_num)
theorem B1363117 : Blo 1211423 1363117 := bbase (se 3 (by rfl) ⟨255584, by rfl⟩ : syracuseStep 1363117 = 511169) (by norm_num)
theorem B3067085 : Blo 1211423 3067085 := bbase (se 3 (by rfl) ⟨575078, by rfl⟩ : syracuseStep 3067085 = 1150157) (by norm_num)
theorem B1363153 : Blo 1211423 1363153 := bbase (se 2 (by rfl) ⟨511182, by rfl⟩ : syracuseStep 1363153 = 1022365) (by norm_num)
theorem B4091093 : Blo 1211423 4091093 := bbase (se 7 (by rfl) ⟨47942, by rfl⟩ : syracuseStep 4091093 = 95885) (by norm_num)
theorem B3501269 : Blo 1211423 3501269 := bbase (se 7 (by rfl) ⟨41030, by rfl⟩ : syracuseStep 3501269 = 82061) (by norm_num)
theorem B4607189 : Blo 1211423 4607189 := bbase (se 7 (by rfl) ⟨53990, by rfl⟩ : syracuseStep 4607189 = 107981) (by norm_num)
theorem B1535213 : Blo 1211423 1535213 := bbase (se 3 (by rfl) ⟨287852, by rfl⟩ : syracuseStep 1535213 = 575705) (by norm_num)
theorem B9325813 : Blo 1211423 9325813 := bbase (se 5 (by rfl) ⟨437147, by rfl⟩ : syracuseStep 9325813 = 874295) (by norm_num)
theorem B1363189 : Blo 1211423 1363189 := bbase (se 5 (by rfl) ⟨63899, by rfl⟩ : syracuseStep 1363189 = 127799) (by norm_num)
theorem B9211157 : Blo 1211423 9211157 := bbase (se 6 (by rfl) ⟨215886, by rfl⟩ : syracuseStep 9211157 = 431773) (by norm_num)
theorem B1363225 : Blo 1211423 1363225 := bbase (se 2 (by rfl) ⟨511209, by rfl⟩ : syracuseStep 1363225 = 1022419) (by norm_num)
theorem B2764061 : Blo 1211423 2764061 := bbase (se 3 (by rfl) ⟨518261, by rfl⟩ : syracuseStep 2764061 = 1036523) (by norm_num)
theorem B1535269 : Blo 1211423 1535269 := bbase (se 4 (by rfl) ⟨143931, by rfl⟩ : syracuseStep 1535269 = 287863) (by norm_num)
theorem B1363261 : Blo 1211423 1363261 := bbase (se 3 (by rfl) ⟨255611, by rfl⟩ : syracuseStep 1363261 = 511223) (by norm_num)
theorem B1363297 : Blo 1211423 1363297 := bbase (se 2 (by rfl) ⟨511236, by rfl⟩ : syracuseStep 1363297 = 1022473) (by norm_num)
theorem B2805101 : Blo 1211423 2805101 := bbase (se 3 (by rfl) ⟨525956, by rfl⟩ : syracuseStep 2805101 = 1051913) (by norm_num)
theorem B4148597 : Blo 1211423 4148597 := bbase (se 5 (by rfl) ⟨194465, by rfl⟩ : syracuseStep 4148597 = 388931) (by norm_num)
theorem B1363333 : Blo 1211423 1363333 := bbase (se 4 (by rfl) ⟨127812, by rfl⟩ : syracuseStep 1363333 = 255625) (by norm_num)
theorem B1535365 : Blo 1211423 1535365 := bbase (se 4 (by rfl) ⟨143940, by rfl⟩ : syracuseStep 1535365 = 287881) (by norm_num)
theorem B1363369 : Blo 1211423 1363369 := bbase (se 2 (by rfl) ⟨511263, by rfl⟩ : syracuseStep 1363369 = 1022527) (by norm_num)
theorem B1363405 : Blo 1211423 1363405 := bbase (se 3 (by rfl) ⟨255638, by rfl⟩ : syracuseStep 1363405 = 511277) (by norm_num)
theorem B1363441 : Blo 1211423 1363441 := bbase (se 2 (by rfl) ⟨511290, by rfl⟩ : syracuseStep 1363441 = 1022581) (by norm_num)
theorem B1363477 : Blo 1211423 1363477 := bbase (se 6 (by rfl) ⟨31956, by rfl⟩ : syracuseStep 1363477 = 63913) (by norm_num)
theorem B3067429 : Blo 1211423 3067429 := bbase (se 4 (by rfl) ⟨287571, by rfl⟩ : syracuseStep 3067429 = 575143) (by norm_num)
theorem B3452453 : Blo 1211423 3452453 := bbase (se 4 (by rfl) ⟨323667, by rfl⟩ : syracuseStep 3452453 = 647335) (by norm_num)
theorem B1535537 : Blo 1211423 1535537 := bbase (se 2 (by rfl) ⟨575826, by rfl⟩ : syracuseStep 1535537 = 1151653) (by norm_num)
theorem B1363513 : Blo 1211423 1363513 := bbase (se 2 (by rfl) ⟨511317, by rfl⟩ : syracuseStep 1363513 = 1022635) (by norm_num)
theorem B1363549 : Blo 1211423 1363549 := bbase (se 3 (by rfl) ⟨255665, by rfl⟩ : syracuseStep 1363549 = 511331) (by norm_num)
theorem B1535593 : Blo 1211423 1535593 := bbase (se 2 (by rfl) ⟨575847, by rfl⟩ : syracuseStep 1535593 = 1151695) (by norm_num)
theorem B3935861 : Blo 1211423 3935861 := bbase (se 5 (by rfl) ⟨184493, by rfl⟩ : syracuseStep 3935861 = 368987) (by norm_num)
theorem B1363585 : Blo 1211423 1363585 := bbase (se 2 (by rfl) ⟨511344, by rfl⟩ : syracuseStep 1363585 = 1022689) (by norm_num)
theorem B4091525 : Blo 1211423 4091525 := bbase (se 4 (by rfl) ⟨383580, by rfl⟩ : syracuseStep 4091525 = 767161) (by norm_num)
theorem B3067541 : Blo 1211423 3067541 := bbase (se 6 (by rfl) ⟨71895, by rfl⟩ : syracuseStep 3067541 = 143791) (by norm_num)
theorem B1363621 : Blo 1211423 1363621 := bbase (se 4 (by rfl) ⟨127839, by rfl⟩ : syracuseStep 1363621 = 255679) (by norm_num)
theorem B9203381 : Blo 1211423 9203381 := bbase (se 5 (by rfl) ⟨431408, by rfl⟩ : syracuseStep 9203381 = 862817) (by norm_num)
theorem B1363657 : Blo 1211423 1363657 := bbase (se 2 (by rfl) ⟨511371, by rfl⟩ : syracuseStep 1363657 = 1022743) (by norm_num)
theorem B1535689 : Blo 1211423 1535689 := bbase (se 2 (by rfl) ⟨575883, by rfl⟩ : syracuseStep 1535689 = 1151767) (by norm_num)
theorem B3886805 : Blo 1211423 3886805 := bbase (se 7 (by rfl) ⟨45548, by rfl⟩ : syracuseStep 3886805 = 91097) (by norm_num)
theorem B1363693 : Blo 1211423 1363693 := bbase (se 3 (by rfl) ⟨255692, by rfl⟩ : syracuseStep 1363693 = 511385) (by norm_num)
theorem B6139637 : Blo 1211423 6139637 := bbase (se 5 (by rfl) ⟨287795, by rfl⟩ : syracuseStep 6139637 = 575591) (by norm_num)
theorem B1363729 : Blo 1211423 1363729 := bbase (se 2 (by rfl) ⟨511398, by rfl⟩ : syracuseStep 1363729 = 1022797) (by norm_num)
theorem B1363765 : Blo 1211423 1363765 := bbase (se 5 (by rfl) ⟨63926, by rfl⟩ : syracuseStep 1363765 = 127853) (by norm_num)
theorem B3067733 : Blo 1211423 3067733 := bbase (se 9 (by rfl) ⟨8987, by rfl⟩ : syracuseStep 3067733 = 17975) (by norm_num)
theorem B1363801 : Blo 1211423 1363801 := bbase (se 2 (by rfl) ⟨511425, by rfl⟩ : syracuseStep 1363801 = 1022851) (by norm_num)
theorem B4665205 : Blo 1211423 4665205 := bbase (se 5 (by rfl) ⟨218681, by rfl⟩ : syracuseStep 4665205 = 437363) (by norm_num)
theorem B1363837 : Blo 1211423 1363837 := bbase (se 3 (by rfl) ⟨255719, by rfl⟩ : syracuseStep 1363837 = 511439) (by norm_num)
theorem B1363873 : Blo 1211423 1363873 := bbase (se 2 (by rfl) ⟨511452, by rfl⟩ : syracuseStep 1363873 = 1022905) (by norm_num)
theorem B2215853 : Blo 1211423 2215853 := bbase (se 3 (by rfl) ⟨415472, by rfl⟩ : syracuseStep 2215853 = 830945) (by norm_num)
theorem B1363909 : Blo 1211423 1363909 := bbase (se 4 (by rfl) ⟨127866, by rfl⟩ : syracuseStep 1363909 = 255733) (by norm_num)
theorem B6221765 : Blo 1211423 6221765 := bbase (se 4 (by rfl) ⟨583290, by rfl⟩ : syracuseStep 6221765 = 1166581) (by norm_num)
theorem B1363945 : Blo 1211423 1363945 := bbase (se 2 (by rfl) ⟨511479, by rfl⟩ : syracuseStep 1363945 = 1022959) (by norm_num)
theorem B5246981 : Blo 1211423 5246981 := bbase (se 4 (by rfl) ⟨491904, by rfl⟩ : syracuseStep 5246981 = 983809) (by norm_num)
theorem B1363981 : Blo 1211423 1363981 := bbase (se 3 (by rfl) ⟨255746, by rfl⟩ : syracuseStep 1363981 = 511493) (by norm_num)
theorem B1364017 : Blo 1211423 1364017 := bbase (se 2 (by rfl) ⟨511506, by rfl⟩ : syracuseStep 1364017 = 1023013) (by norm_num)
theorem B11808821 : Blo 1211423 11808821 := bbase (se 5 (by rfl) ⟨553538, by rfl⟩ : syracuseStep 11808821 = 1107077) (by norm_num)
theorem B4091957 : Blo 1211423 4091957 := bbase (se 5 (by rfl) ⟨191810, by rfl⟩ : syracuseStep 4091957 = 383621) (by norm_num)
theorem B1364053 : Blo 1211423 1364053 := bbase (se 8 (by rfl) ⟨7992, by rfl⟩ : syracuseStep 1364053 = 15985) (by norm_num)
theorem B1364089 : Blo 1211423 1364089 := bbase (se 2 (by rfl) ⟨511533, by rfl⟩ : syracuseStep 1364089 = 1023067) (by norm_num)
theorem B1364125 : Blo 1211423 1364125 := bbase (se 3 (by rfl) ⟨255773, by rfl⟩ : syracuseStep 1364125 = 511547) (by norm_num)
theorem B3068077 : Blo 1211423 3068077 := bbase (se 3 (by rfl) ⟨575264, by rfl⟩ : syracuseStep 3068077 = 1150529) (by norm_num)
theorem B1364161 : Blo 1211423 1364161 := bbase (se 2 (by rfl) ⟨511560, by rfl⟩ : syracuseStep 1364161 = 1023121) (by norm_num)
theorem B1364197 : Blo 1211423 1364197 := bbase (se 4 (by rfl) ⟨127893, by rfl⟩ : syracuseStep 1364197 = 255787) (by norm_num)
theorem B1364233 : Blo 1211423 1364233 := bbase (se 2 (by rfl) ⟨511587, by rfl⟩ : syracuseStep 1364233 = 1023175) (by norm_num)
theorem B3453205 : Blo 1211423 3453205 := bbase (se 6 (by rfl) ⟨80934, by rfl⟩ : syracuseStep 3453205 = 161869) (by norm_num)
theorem B3068189 : Blo 1211423 3068189 := bbase (se 3 (by rfl) ⟨575285, by rfl⟩ : syracuseStep 3068189 = 1150571) (by norm_num)
theorem B1364269 : Blo 1211423 1364269 := bbase (se 3 (by rfl) ⟨255800, by rfl⟩ : syracuseStep 1364269 = 511601) (by norm_num)
theorem B1364305 : Blo 1211423 1364305 := bbase (se 2 (by rfl) ⟨511614, by rfl⟩ : syracuseStep 1364305 = 1023229) (by norm_num)
theorem B1364341 : Blo 1211423 1364341 := bbase (se 5 (by rfl) ⟨63953, by rfl⟩ : syracuseStep 1364341 = 127907) (by norm_num)
theorem B1364377 : Blo 1211423 1364377 := bbase (se 2 (by rfl) ⟨511641, by rfl⟩ : syracuseStep 1364377 = 1023283) (by norm_num)
theorem B2044325 : Blo 1211423 2044325 := bbase (se 4 (by rfl) ⟨191655, by rfl⟩ : syracuseStep 2044325 = 383311) (by norm_num)
theorem B1364413 : Blo 1211423 1364413 := bbase (se 3 (by rfl) ⟨255827, by rfl⟩ : syracuseStep 1364413 = 511655) (by norm_num)
theorem B5181893 : Blo 1211423 5181893 := bbase (se 4 (by rfl) ⟨485802, by rfl⟩ : syracuseStep 5181893 = 971605) (by norm_num)
theorem B3068381 : Blo 1211423 3068381 := bbase (se 3 (by rfl) ⟨575321, by rfl⟩ : syracuseStep 3068381 = 1150643) (by norm_num)
theorem B1364449 : Blo 1211423 1364449 := bbase (se 2 (by rfl) ⟨511668, by rfl⟩ : syracuseStep 1364449 = 1023337) (by norm_num)
theorem B4092389 : Blo 1211423 4092389 := bbase (se 4 (by rfl) ⟨383661, by rfl⟩ : syracuseStep 4092389 = 767323) (by norm_num)
theorem B1724917 : Blo 1211423 1724917 := bbase (se 5 (by rfl) ⟨80855, by rfl⟩ : syracuseStep 1724917 = 161711) (by norm_num)
theorem B1364485 : Blo 1211423 1364485 := bbase (se 4 (by rfl) ⟨127920, by rfl⟩ : syracuseStep 1364485 = 255841) (by norm_num)
theorem B2044453 : Blo 1211423 2044453 := bbase (se 4 (by rfl) ⟨191667, by rfl⟩ : syracuseStep 2044453 = 383335) (by norm_num)
theorem B1364521 : Blo 1211423 1364521 := bbase (se 2 (by rfl) ⟨511695, by rfl⟩ : syracuseStep 1364521 = 1023391) (by norm_num)
theorem B1364557 : Blo 1211423 1364557 := bbase (se 3 (by rfl) ⟨255854, by rfl⟩ : syracuseStep 1364557 = 511709) (by norm_num)
theorem B1364593 : Blo 1211423 1364593 := bbase (se 2 (by rfl) ⟨511722, by rfl⟩ : syracuseStep 1364593 = 1023445) (by norm_num)
theorem B2044541 : Blo 1211423 2044541 := bbase (se 3 (by rfl) ⟨383351, by rfl⟩ : syracuseStep 2044541 = 766703) (by norm_num)
theorem B1364629 : Blo 1211423 1364629 := bbase (se 6 (by rfl) ⟨31983, by rfl⟩ : syracuseStep 1364629 = 63967) (by norm_num)
theorem B1364665 : Blo 1211423 1364665 := bbase (se 2 (by rfl) ⟨511749, by rfl⟩ : syracuseStep 1364665 = 1023499) (by norm_num)
theorem B1725133 : Blo 1211423 1725133 := bbase (se 3 (by rfl) ⟨323462, by rfl⟩ : syracuseStep 1725133 = 646925) (by norm_num)
theorem B1364701 : Blo 1211423 1364701 := bbase (se 3 (by rfl) ⟨255881, by rfl⟩ : syracuseStep 1364701 = 511763) (by norm_num)
theorem B2044669 : Blo 1211423 2044669 := bbase (se 3 (by rfl) ⟨383375, by rfl⟩ : syracuseStep 2044669 = 766751) (by norm_num)
theorem B1364737 : Blo 1211423 1364737 := bbase (se 2 (by rfl) ⟨511776, by rfl⟩ : syracuseStep 1364737 = 1023553) (by norm_num)
theorem B4600597 : Blo 1211423 4600597 := bbase (se 6 (by rfl) ⟨107826, by rfl⟩ : syracuseStep 4600597 = 215653) (by norm_num)
theorem B1364773 : Blo 1211423 1364773 := bbase (se 4 (by rfl) ⟨127947, by rfl⟩ : syracuseStep 1364773 = 255895) (by norm_num)
theorem B2331437 : Blo 1211423 2331437 := bbase (se 3 (by rfl) ⟨437144, by rfl⟩ : syracuseStep 2331437 = 874289) (by norm_num)
theorem B3068725 : Blo 1211423 3068725 := bbase (se 5 (by rfl) ⟨143846, by rfl⟩ : syracuseStep 3068725 = 287693) (by norm_num)
theorem B2913077 : Blo 1211423 2913077 := bbase (se 5 (by rfl) ⟨136550, by rfl⟩ : syracuseStep 2913077 = 273101) (by norm_num)
theorem B4911941 : Blo 1211423 4911941 := bbase (se 4 (by rfl) ⟨460494, by rfl⟩ : syracuseStep 4911941 = 920989) (by norm_num)
theorem B1364809 : Blo 1211423 1364809 := bbase (se 2 (by rfl) ⟨511803, by rfl⟩ : syracuseStep 1364809 = 1023607) (by norm_num)
theorem B2044757 : Blo 1211423 2044757 := bbase (se 9 (by rfl) ⟨5990, by rfl⟩ : syracuseStep 2044757 = 11981) (by norm_num)
theorem B2274149 : Blo 1211423 2274149 := bbase (se 4 (by rfl) ⟨213201, by rfl⟩ : syracuseStep 2274149 = 426403) (by norm_num)
theorem B1364845 : Blo 1211423 1364845 := bbase (se 3 (by rfl) ⟨255908, by rfl⟩ : syracuseStep 1364845 = 511817) (by norm_num)
theorem B1364881 : Blo 1211423 1364881 := bbase (se 2 (by rfl) ⟨511830, by rfl⟩ : syracuseStep 1364881 = 1023661) (by norm_num)
theorem B4092821 : Blo 1211423 4092821 := bbase (se 6 (by rfl) ⟨95925, by rfl⟩ : syracuseStep 4092821 = 191851) (by norm_num)
theorem B3068837 : Blo 1211423 3068837 := bbase (se 4 (by rfl) ⟨287703, by rfl⟩ : syracuseStep 3068837 = 575407) (by norm_num)
theorem B1364917 : Blo 1211423 1364917 := bbase (se 5 (by rfl) ⟨63980, by rfl⟩ : syracuseStep 1364917 = 127961) (by norm_num)
theorem B2044885 : Blo 1211423 2044885 := bbase (se 7 (by rfl) ⟨23963, by rfl⟩ : syracuseStep 2044885 = 47927) (by norm_num)
theorem B1364953 : Blo 1211423 1364953 := bbase (se 2 (by rfl) ⟨511857, by rfl⟩ : syracuseStep 1364953 = 1023715) (by norm_num)
theorem B2184173 : Blo 1211423 2184173 := bbase (se 3 (by rfl) ⟨409532, by rfl⟩ : syracuseStep 2184173 = 819065) (by norm_num)
theorem B1364989 : Blo 1211423 1364989 := bbase (se 3 (by rfl) ⟨255935, by rfl⟩ : syracuseStep 1364989 = 511871) (by norm_num)
theorem B6140933 : Blo 1211423 6140933 := bbase (se 4 (by rfl) ⟨575712, by rfl⟩ : syracuseStep 6140933 = 1151425) (by norm_num)
theorem B1365025 : Blo 1211423 1365025 := bbase (se 2 (by rfl) ⟨511884, by rfl⟩ : syracuseStep 1365025 = 1023769) (by norm_num)
theorem B2044973 : Blo 1211423 2044973 := bbase (se 3 (by rfl) ⟨383432, by rfl⟩ : syracuseStep 2044973 = 766865) (by norm_num)
theorem B4600901 : Blo 1211423 4600901 := bbase (se 4 (by rfl) ⟨431334, by rfl⟩ : syracuseStep 4600901 = 862669) (by norm_num)
theorem B1725509 : Blo 1211423 1725509 := bbase (se 4 (by rfl) ⟨161766, by rfl⟩ : syracuseStep 1725509 = 323533) (by norm_num)
theorem B1365061 : Blo 1211423 1365061 := bbase (se 4 (by rfl) ⟨127974, by rfl⟩ : syracuseStep 1365061 = 255949) (by norm_num)
theorem B3069029 : Blo 1211423 3069029 := bbase (se 4 (by rfl) ⟨287721, by rfl⟩ : syracuseStep 3069029 = 575443) (by norm_num)
theorem B1365097 : Blo 1211423 1365097 := bbase (se 2 (by rfl) ⟨511911, by rfl⟩ : syracuseStep 1365097 = 1023823) (by norm_num)
theorem B5534837 : Blo 1211423 5534837 := bbase (se 5 (by rfl) ⟨259445, by rfl⟩ : syracuseStep 5534837 = 518891) (by norm_num)
theorem B2045101 : Blo 1211423 2045101 := bbase (se 3 (by rfl) ⟨383456, by rfl⟩ : syracuseStep 2045101 = 766913) (by norm_num)
theorem B2913461 : Blo 1211423 2913461 := bbase (se 5 (by rfl) ⟨136568, by rfl⟩ : syracuseStep 2913461 = 273137) (by norm_num)
theorem B2045189 : Blo 1211423 2045189 := bbase (se 4 (by rfl) ⟨191736, by rfl⟩ : syracuseStep 2045189 = 383473) (by norm_num)
theorem B4093253 : Blo 1211423 4093253 := bbase (se 4 (by rfl) ⟨383742, by rfl⟩ : syracuseStep 4093253 = 767485) (by norm_num)
theorem B2463053 : Blo 1211423 2463053 := bbase (se 3 (by rfl) ⟨461822, by rfl⟩ : syracuseStep 2463053 = 923645) (by norm_num)
theorem B8295797 : Blo 1211423 8295797 := bbase (se 5 (by rfl) ⟨388865, by rfl⟩ : syracuseStep 8295797 = 777731) (by norm_num)
theorem B1381757 : Blo 1211423 1381757 := bbase (se 3 (by rfl) ⟨259079, by rfl⟩ : syracuseStep 1381757 = 518159) (by norm_num)
theorem B2913661 : Blo 1211423 2913661 := bbase (se 3 (by rfl) ⟨546311, by rfl⟩ : syracuseStep 2913661 = 1092623) (by norm_num)
theorem B2045317 : Blo 1211423 2045317 := bbase (se 4 (by rfl) ⟨191748, by rfl⟩ : syracuseStep 2045317 = 383497) (by norm_num)
theorem B6133157 : Blo 1211423 6133157 := bbase (se 4 (by rfl) ⟨574983, by rfl⟩ : syracuseStep 6133157 = 1149967) (by norm_num)
theorem B3069373 : Blo 1211423 3069373 := bbase (se 3 (by rfl) ⟨575507, by rfl⟩ : syracuseStep 3069373 = 1151015) (by norm_num)
theorem B2045405 : Blo 1211423 2045405 := bbase (se 3 (by rfl) ⟨383513, by rfl⟩ : syracuseStep 2045405 = 767027) (by norm_num)
theorem B3069485 : Blo 1211423 3069485 := bbase (se 3 (by rfl) ⟨575528, by rfl⟩ : syracuseStep 3069485 = 1151057) (by norm_num)
theorem B5174837 : Blo 1211423 5174837 := bbase (se 5 (by rfl) ⟨242570, by rfl⟩ : syracuseStep 5174837 = 485141) (by norm_num)
theorem B2045533 : Blo 1211423 2045533 := bbase (se 3 (by rfl) ⟨383537, by rfl⟩ : syracuseStep 2045533 = 767075) (by norm_num)
theorem B2045621 : Blo 1211423 2045621 := bbase (se 5 (by rfl) ⟨95888, by rfl⟩ : syracuseStep 2045621 = 191777) (by norm_num)
theorem B39319253 : Blo 1211423 39319253 := bbase (se 7 (by rfl) ⟨460772, by rfl⟩ : syracuseStep 39319253 = 921545) (by norm_num)
theorem B1382113 : Blo 1211423 1382113 := bbase (se 2 (by rfl) ⟨518292, by rfl⟩ : syracuseStep 1382113 = 1036585) (by norm_num)
theorem B3069677 : Blo 1211423 3069677 := bbase (se 3 (by rfl) ⟨575564, by rfl⟩ : syracuseStep 3069677 = 1151129) (by norm_num)
theorem B8296181 : Blo 1211423 8296181 := bbase (se 5 (by rfl) ⟨388883, by rfl⟩ : syracuseStep 8296181 = 777767) (by norm_num)
theorem B4093685 : Blo 1211423 4093685 := bbase (se 5 (by rfl) ⟨191891, by rfl⟩ : syracuseStep 4093685 = 383783) (by norm_num)
theorem B1455889 : Blo 1211423 1455889 := bbase (se 2 (by rfl) ⟨545958, by rfl⟩ : syracuseStep 1455889 = 1091917) (by norm_num)
theorem B3684149 : Blo 1211423 3684149 := bbase (se 5 (by rfl) ⟨172694, by rfl⟩ : syracuseStep 3684149 = 345389) (by norm_num)
theorem B2045749 : Blo 1211423 2045749 := bbase (se 5 (by rfl) ⟨95894, by rfl⟩ : syracuseStep 2045749 = 191789) (by norm_num)
theorem B4372309 : Blo 1211423 4372309 := bbase (se 9 (by rfl) ⟨12809, by rfl⟩ : syracuseStep 4372309 = 25619) (by norm_num)
theorem B1455985 : Blo 1211423 1455985 := bbase (se 2 (by rfl) ⟨545994, by rfl⟩ : syracuseStep 1455985 = 1091989) (by norm_num)
theorem B2725757 : Blo 1211423 2725757 := bbase (se 3 (by rfl) ⟨511079, by rfl⟩ : syracuseStep 2725757 = 1022159) (by norm_num)
theorem B2045837 : Blo 1211423 2045837 := bbase (se 3 (by rfl) ⟨383594, by rfl⟩ : syracuseStep 2045837 = 767189) (by norm_num)
theorem B2725829 : Blo 1211423 2725829 := bbase (se 4 (by rfl) ⟨255546, by rfl⟩ : syracuseStep 2725829 = 511093) (by norm_num)
theorem B2725901 : Blo 1211423 2725901 := bbase (se 3 (by rfl) ⟨511106, by rfl⟩ : syracuseStep 2725901 = 1022213) (by norm_num)
theorem B2045965 : Blo 1211423 2045965 := bbase (se 3 (by rfl) ⟨383618, by rfl⟩ : syracuseStep 2045965 = 767237) (by norm_num)
theorem B3070021 : Blo 1211423 3070021 := bbase (se 4 (by rfl) ⟨287814, by rfl⟩ : syracuseStep 3070021 = 575629) (by norm_num)
theorem B2725973 : Blo 1211423 2725973 := bbase (se 8 (by rfl) ⟨15972, by rfl⟩ : syracuseStep 2725973 = 31945) (by norm_num)
theorem B4913237 : Blo 1211423 4913237 := bbase (se 8 (by rfl) ⟨28788, by rfl⟩ : syracuseStep 4913237 = 57577) (by norm_num)
theorem B2046053 : Blo 1211423 2046053 := bbase (se 4 (by rfl) ⟨191817, by rfl⟩ : syracuseStep 2046053 = 383635) (by norm_num)
theorem B2726045 : Blo 1211423 2726045 := bbase (se 3 (by rfl) ⟨511133, by rfl⟩ : syracuseStep 2726045 = 1022267) (by norm_num)
theorem B4094117 : Blo 1211423 4094117 := bbase (se 4 (by rfl) ⟨383823, by rfl⟩ : syracuseStep 4094117 = 767647) (by norm_num)
theorem B3070133 : Blo 1211423 3070133 := bbase (se 5 (by rfl) ⟨143912, by rfl⟩ : syracuseStep 3070133 = 287825) (by norm_num)
theorem B2726117 : Blo 1211423 2726117 := bbase (se 4 (by rfl) ⟨255573, by rfl⟩ : syracuseStep 2726117 = 511147) (by norm_num)
theorem B2046181 : Blo 1211423 2046181 := bbase (se 4 (by rfl) ⟨191829, by rfl⟩ : syracuseStep 2046181 = 383659) (by norm_num)
theorem B11655413 : Blo 1211423 11655413 := bbase (se 5 (by rfl) ⟨546347, by rfl⟩ : syracuseStep 11655413 = 1092695) (by norm_num)
theorem B6142229 : Blo 1211423 6142229 := bbase (se 6 (by rfl) ⟨143958, by rfl⟩ : syracuseStep 6142229 = 287917) (by norm_num)
theorem B2726189 : Blo 1211423 2726189 := bbase (se 3 (by rfl) ⟨511160, by rfl⟩ : syracuseStep 2726189 = 1022321) (by norm_num)
theorem B2046269 : Blo 1211423 2046269 := bbase (se 3 (by rfl) ⟨383675, by rfl⟩ : syracuseStep 2046269 = 767351) (by norm_num)
theorem B3881333 : Blo 1211423 3881333 := bbase (se 5 (by rfl) ⟨181937, by rfl⟩ : syracuseStep 3881333 = 363875) (by norm_num)
theorem B2726261 : Blo 1211423 2726261 := bbase (se 5 (by rfl) ⟨127793, by rfl⟩ : syracuseStep 2726261 = 255587) (by norm_num)
theorem B3070325 : Blo 1211423 3070325 := bbase (se 5 (by rfl) ⟨143921, by rfl⟩ : syracuseStep 3070325 = 287843) (by norm_num)
theorem B5527973 : Blo 1211423 5527973 := bbase (se 4 (by rfl) ⟨518247, by rfl⟩ : syracuseStep 5527973 = 1036495) (by norm_num)
theorem B1661357 : Blo 1211423 1661357 := bbase (se 3 (by rfl) ⟨311504, by rfl⟩ : syracuseStep 1661357 = 623009) (by norm_num)
theorem B2726333 : Blo 1211423 2726333 := bbase (se 3 (by rfl) ⟨511187, by rfl⟩ : syracuseStep 2726333 = 1022375) (by norm_num)
theorem B2046397 : Blo 1211423 2046397 := bbase (se 3 (by rfl) ⟨383699, by rfl⟩ : syracuseStep 2046397 = 767399) (by norm_num)
theorem B2365901 : Blo 1211423 2365901 := bbase (se 3 (by rfl) ⟨443606, by rfl⟩ : syracuseStep 2365901 = 887213) (by norm_num)
theorem B3275221 : Blo 1211423 3275221 := bbase (se 7 (by rfl) ⟨38381, by rfl⟩ : syracuseStep 3275221 = 76763) (by norm_num)
theorem B1726933 : Blo 1211423 1726933 := bbase (se 7 (by rfl) ⟨20237, by rfl⟩ : syracuseStep 1726933 = 40475) (by norm_num)
theorem B2300413 : Blo 1211423 2300413 := bbase (se 3 (by rfl) ⟨431327, by rfl⟩ : syracuseStep 2300413 = 862655) (by norm_num)
theorem B2726405 : Blo 1211423 2726405 := bbase (se 4 (by rfl) ⟨255600, by rfl⟩ : syracuseStep 2726405 = 511201) (by norm_num)
theorem B2046485 : Blo 1211423 2046485 := bbase (se 6 (by rfl) ⟨47964, by rfl⟩ : syracuseStep 2046485 = 95929) (by norm_num)
theorem B5175845 : Blo 1211423 5175845 := bbase (se 4 (by rfl) ⟨485235, by rfl⟩ : syracuseStep 5175845 = 970471) (by norm_num)
theorem B1817141 : Blo 1211423 1817141 := bbase (se 5 (by rfl) ⟨85178, by rfl⟩ : syracuseStep 1817141 = 170357) (by norm_num)
theorem B1817165 : Blo 1211423 1817165 := bbase (se 3 (by rfl) ⟨340718, by rfl⟩ : syracuseStep 1817165 = 681437) (by norm_num)
theorem B2726477 : Blo 1211423 2726477 := bbase (se 3 (by rfl) ⟨511214, by rfl⟩ : syracuseStep 2726477 = 1022429) (by norm_num)
theorem B1382989 : Blo 1211423 1382989 := bbase (se 3 (by rfl) ⟨259310, by rfl⟩ : syracuseStep 1382989 = 518621) (by norm_num)
theorem B4094549 : Blo 1211423 4094549 := bbase (se 8 (by rfl) ⟨23991, by rfl⟩ : syracuseStep 4094549 = 47983) (by norm_num)
theorem B1817189 : Blo 1211423 1817189 := bbase (se 4 (by rfl) ⟨170361, by rfl⟩ : syracuseStep 1817189 = 340723) (by norm_num)
theorem B1817213 : Blo 1211423 1817213 := bbase (se 3 (by rfl) ⟨340727, by rfl⟩ : syracuseStep 1817213 = 681455) (by norm_num)
theorem B2300557 : Blo 1211423 2300557 := bbase (se 3 (by rfl) ⟨431354, by rfl⟩ : syracuseStep 2300557 = 862709) (by norm_num)
theorem B1817237 : Blo 1211423 1817237 := bbase (se 6 (by rfl) ⟨42591, by rfl⟩ : syracuseStep 1817237 = 85183) (by norm_num)
theorem B2726549 : Blo 1211423 2726549 := bbase (se 6 (by rfl) ⟨63903, by rfl⟩ : syracuseStep 2726549 = 127807) (by norm_num)
theorem B2046613 : Blo 1211423 2046613 := bbase (se 6 (by rfl) ⟨47967, by rfl⟩ : syracuseStep 2046613 = 95935) (by norm_num)
theorem B1817261 : Blo 1211423 1817261 := bbase (se 3 (by rfl) ⟨340736, by rfl⟩ : syracuseStep 1817261 = 681473) (by norm_num)
theorem B6134453 : Blo 1211423 6134453 := bbase (se 5 (by rfl) ⟨287552, by rfl⟩ : syracuseStep 6134453 = 575105) (by norm_num)
theorem B1817285 : Blo 1211423 1817285 := bbase (se 4 (by rfl) ⟨170370, by rfl⟩ : syracuseStep 1817285 = 340741) (by norm_num)
theorem B3070669 : Blo 1211423 3070669 := bbase (se 3 (by rfl) ⟨575750, by rfl⟩ : syracuseStep 3070669 = 1151501) (by norm_num)
theorem B1817309 : Blo 1211423 1817309 := bbase (se 3 (by rfl) ⟨340745, by rfl⟩ : syracuseStep 1817309 = 681491) (by norm_num)
theorem B2726621 : Blo 1211423 2726621 := bbase (se 3 (by rfl) ⟨511241, by rfl⟩ : syracuseStep 2726621 = 1022483) (by norm_num)
theorem B2046701 : Blo 1211423 2046701 := bbase (se 3 (by rfl) ⟨383756, by rfl⟩ : syracuseStep 2046701 = 767513) (by norm_num)
theorem B1817333 : Blo 1211423 1817333 := bbase (se 5 (by rfl) ⟨85187, by rfl⟩ : syracuseStep 1817333 = 170375) (by norm_num)
theorem B1383161 : Blo 1211423 1383161 := bbase (se 2 (by rfl) ⟨518685, by rfl⟩ : syracuseStep 1383161 = 1037371) (by norm_num)
theorem B1817357 : Blo 1211423 1817357 := bbase (se 3 (by rfl) ⟨340754, by rfl⟩ : syracuseStep 1817357 = 681509) (by norm_num)
theorem B1817381 : Blo 1211423 1817381 := bbase (se 4 (by rfl) ⟨170379, by rfl⟩ : syracuseStep 1817381 = 340759) (by norm_num)
theorem B2726693 : Blo 1211423 2726693 := bbase (se 4 (by rfl) ⟨255627, by rfl⟩ : syracuseStep 2726693 = 511255) (by norm_num)
theorem B2300717 : Blo 1211423 2300717 := bbase (se 3 (by rfl) ⟨431384, by rfl⟩ : syracuseStep 2300717 = 862769) (by norm_num)
theorem B1817405 : Blo 1211423 1817405 := bbase (se 3 (by rfl) ⟨340763, by rfl⟩ : syracuseStep 1817405 = 681527) (by norm_num)
theorem B3070781 : Blo 1211423 3070781 := bbase (se 3 (by rfl) ⟨575771, by rfl⟩ : syracuseStep 3070781 = 1151543) (by norm_num)
theorem B1817429 : Blo 1211423 1817429 := bbase (se 9 (by rfl) ⟨5324, by rfl⟩ : syracuseStep 1817429 = 10649) (by norm_num)
theorem B1817453 : Blo 1211423 1817453 := bbase (se 3 (by rfl) ⟨340772, by rfl⟩ : syracuseStep 1817453 = 681545) (by norm_num)
theorem B2726765 : Blo 1211423 2726765 := bbase (se 3 (by rfl) ⟨511268, by rfl⟩ : syracuseStep 2726765 = 1022537) (by norm_num)
theorem B2046829 : Blo 1211423 2046829 := bbase (se 3 (by rfl) ⟨383780, by rfl⟩ : syracuseStep 2046829 = 767561) (by norm_num)
theorem B1817477 : Blo 1211423 1817477 := bbase (se 4 (by rfl) ⟨170388, by rfl⟩ : syracuseStep 1817477 = 340777) (by norm_num)
theorem B1817501 : Blo 1211423 1817501 := bbase (se 3 (by rfl) ⟨340781, by rfl⟩ : syracuseStep 1817501 = 681563) (by norm_num)
theorem B2915237 : Blo 1211423 2915237 := bbase (se 4 (by rfl) ⟨273303, by rfl⟩ : syracuseStep 2915237 = 546607) (by norm_num)
theorem B1817525 : Blo 1211423 1817525 := bbase (se 5 (by rfl) ⟨85196, by rfl⟩ : syracuseStep 1817525 = 170393) (by norm_num)
theorem B2726837 : Blo 1211423 2726837 := bbase (se 5 (by rfl) ⟨127820, by rfl⟩ : syracuseStep 2726837 = 255641) (by norm_num)
theorem B2300861 : Blo 1211423 2300861 := bbase (se 3 (by rfl) ⟨431411, by rfl⟩ : syracuseStep 2300861 = 862823) (by norm_num)
theorem B2046917 : Blo 1211423 2046917 := bbase (se 4 (by rfl) ⟨191898, by rfl⟩ : syracuseStep 2046917 = 383797) (by norm_num)
theorem B1817549 : Blo 1211423 1817549 := bbase (se 3 (by rfl) ⟨340790, by rfl⟩ : syracuseStep 1817549 = 681581) (by norm_num)
theorem B2186197 : Blo 1211423 2186197 := bbase (se 7 (by rfl) ⟨25619, by rfl⟩ : syracuseStep 2186197 = 51239) (by norm_num)
theorem B1817573 : Blo 1211423 1817573 := bbase (se 4 (by rfl) ⟨170397, by rfl⟩ : syracuseStep 1817573 = 340795) (by norm_num)
theorem B1457129 : Blo 1211423 1457129 := bbase (se 2 (by rfl) ⟨546423, by rfl⟩ : syracuseStep 1457129 = 1092847) (by norm_num)
theorem B1817597 : Blo 1211423 1817597 := bbase (se 3 (by rfl) ⟨340799, by rfl⟩ : syracuseStep 1817597 = 681599) (by norm_num)
theorem B2726909 : Blo 1211423 2726909 := bbase (se 3 (by rfl) ⟨511295, by rfl⟩ : syracuseStep 2726909 = 1022591) (by norm_num)
theorem B3070973 : Blo 1211423 3070973 := bbase (se 3 (by rfl) ⟨575807, by rfl⟩ : syracuseStep 3070973 = 1151615) (by norm_num)
theorem B4094981 : Blo 1211423 4094981 := bbase (se 4 (by rfl) ⟨383904, by rfl⟩ : syracuseStep 4094981 = 767809) (by norm_num)
theorem B3111949 : Blo 1211423 3111949 := bbase (se 3 (by rfl) ⟨583490, by rfl⟩ : syracuseStep 3111949 = 1166981) (by norm_num)
theorem B1817621 : Blo 1211423 1817621 := bbase (se 6 (by rfl) ⟨42600, by rfl⟩ : syracuseStep 1817621 = 85201) (by norm_num)
theorem B1727525 : Blo 1211423 1727525 := bbase (se 4 (by rfl) ⟨161955, by rfl⟩ : syracuseStep 1727525 = 323911) (by norm_num)
theorem B1817645 : Blo 1211423 1817645 := bbase (se 3 (by rfl) ⟨340808, by rfl⟩ : syracuseStep 1817645 = 681617) (by norm_num)
theorem B2587717 : Blo 1211423 2587717 := bbase (se 4 (by rfl) ⟨242598, by rfl⟩ : syracuseStep 2587717 = 485197) (by norm_num)
theorem B1842245 : Blo 1211423 1842245 := bbase (se 4 (by rfl) ⟨172710, by rfl⟩ : syracuseStep 1842245 = 345421) (by norm_num)
theorem B1817669 : Blo 1211423 1817669 := bbase (se 4 (by rfl) ⟨170406, by rfl⟩ : syracuseStep 1817669 = 340813) (by norm_num)
theorem B2726981 : Blo 1211423 2726981 := bbase (se 4 (by rfl) ⟨255654, by rfl⟩ : syracuseStep 2726981 = 511309) (by norm_num)
theorem B2047045 : Blo 1211423 2047045 := bbase (se 4 (by rfl) ⟨191910, by rfl⟩ : syracuseStep 2047045 = 383821) (by norm_num)
theorem B1817693 : Blo 1211423 1817693 := bbase (se 3 (by rfl) ⟨340817, by rfl⟩ : syracuseStep 1817693 = 681635) (by norm_num)
theorem B1817717 : Blo 1211423 1817717 := bbase (se 5 (by rfl) ⟨85205, by rfl⟩ : syracuseStep 1817717 = 170411) (by norm_num)
theorem B1727605 : Blo 1211423 1727605 := bbase (se 5 (by rfl) ⟨80981, by rfl⟩ : syracuseStep 1727605 = 161963) (by norm_num)
theorem B2186365 : Blo 1211423 2186365 := bbase (se 3 (by rfl) ⟨409943, by rfl⟩ : syracuseStep 2186365 = 819887) (by norm_num)
theorem B4603013 : Blo 1211423 4603013 := bbase (se 4 (by rfl) ⟨431532, by rfl⟩ : syracuseStep 4603013 = 863065) (by norm_num)
theorem B6225029 : Blo 1211423 6225029 := bbase (se 4 (by rfl) ⟨583596, by rfl⟩ : syracuseStep 6225029 = 1167193) (by norm_num)
theorem B1817741 : Blo 1211423 1817741 := bbase (se 3 (by rfl) ⟨340826, by rfl⟩ : syracuseStep 1817741 = 681653) (by norm_num)
theorem B2727053 : Blo 1211423 2727053 := bbase (se 3 (by rfl) ⟨511322, by rfl⟩ : syracuseStep 2727053 = 1022645) (by norm_num)
theorem B2047133 : Blo 1211423 2047133 := bbase (se 3 (by rfl) ⟨383837, by rfl⟩ : syracuseStep 2047133 = 767675) (by norm_num)
theorem B1817765 : Blo 1211423 1817765 := bbase (se 4 (by rfl) ⟨170415, by rfl⟩ : syracuseStep 1817765 = 340831) (by norm_num)
theorem B1817789 : Blo 1211423 1817789 := bbase (se 3 (by rfl) ⟨340835, by rfl⟩ : syracuseStep 1817789 = 681671) (by norm_num)
theorem B1817813 : Blo 1211423 1817813 := bbase (se 7 (by rfl) ⟨21302, by rfl⟩ : syracuseStep 1817813 = 42605) (by norm_num)
theorem B2727125 : Blo 1211423 2727125 := bbase (se 7 (by rfl) ⟨31958, by rfl⟩ : syracuseStep 2727125 = 63917) (by norm_num)
theorem B1383637 : Blo 1211423 1383637 := bbase (se 7 (by rfl) ⟨16214, by rfl⟩ : syracuseStep 1383637 = 32429) (by norm_num)
theorem B2301149 : Blo 1211423 2301149 := bbase (se 3 (by rfl) ⟨431465, by rfl⟩ : syracuseStep 2301149 = 862931) (by norm_num)
theorem B1817837 : Blo 1211423 1817837 := bbase (se 3 (by rfl) ⟨340844, by rfl⟩ : syracuseStep 1817837 = 681689) (by norm_num)
theorem B1817861 : Blo 1211423 1817861 := bbase (se 4 (by rfl) ⟨170424, by rfl⟩ : syracuseStep 1817861 = 340849) (by norm_num)
theorem B1817885 : Blo 1211423 1817885 := bbase (se 3 (by rfl) ⟨340853, by rfl⟩ : syracuseStep 1817885 = 681707) (by norm_num)
theorem B2727197 : Blo 1211423 2727197 := bbase (se 3 (by rfl) ⟨511349, by rfl⟩ : syracuseStep 2727197 = 1022699) (by norm_num)
theorem B2047261 : Blo 1211423 2047261 := bbase (se 3 (by rfl) ⟨383861, by rfl⟩ : syracuseStep 2047261 = 767723) (by norm_num)
theorem B1817909 : Blo 1211423 1817909 := bbase (se 5 (by rfl) ⟨85214, by rfl⟩ : syracuseStep 1817909 = 170429) (by norm_num)
theorem B1457461 : Blo 1211423 1457461 := bbase (se 5 (by rfl) ⟨68318, by rfl⟩ : syracuseStep 1457461 = 136637) (by norm_num)
theorem B1817933 : Blo 1211423 1817933 := bbase (se 3 (by rfl) ⟨340862, by rfl⟩ : syracuseStep 1817933 = 681725) (by norm_num)
theorem B3071317 : Blo 1211423 3071317 := bbase (se 11 (by rfl) ⟨2249, by rfl⟩ : syracuseStep 3071317 = 4499) (by norm_num)
theorem B5823845 : Blo 1211423 5823845 := bbase (se 4 (by rfl) ⟨545985, by rfl⟩ : syracuseStep 5823845 = 1091971) (by norm_num)
theorem B1817957 : Blo 1211423 1817957 := bbase (se 4 (by rfl) ⟨170433, by rfl⟩ : syracuseStep 1817957 = 340867) (by norm_num)
theorem B4914533 : Blo 1211423 4914533 := bbase (se 4 (by rfl) ⟨460737, by rfl⟩ : syracuseStep 4914533 = 921475) (by norm_num)
theorem B2727269 : Blo 1211423 2727269 := bbase (se 4 (by rfl) ⟨255681, by rfl⟩ : syracuseStep 2727269 = 511363) (by norm_num)
theorem B2301301 : Blo 1211423 2301301 := bbase (se 5 (by rfl) ⟨107873, by rfl⟩ : syracuseStep 2301301 = 215747) (by norm_num)
theorem B2047349 : Blo 1211423 2047349 := bbase (se 5 (by rfl) ⟨95969, by rfl⟩ : syracuseStep 2047349 = 191939) (by norm_num)
theorem B1817981 : Blo 1211423 1817981 := bbase (se 3 (by rfl) ⟨340871, by rfl⟩ : syracuseStep 1817981 = 681743) (by norm_num)
theorem B1818005 : Blo 1211423 1818005 := bbase (se 6 (by rfl) ⟨42609, by rfl⟩ : syracuseStep 1818005 = 85219) (by norm_num)
theorem B4603301 : Blo 1211423 4603301 := bbase (se 4 (by rfl) ⟨431559, by rfl⟩ : syracuseStep 4603301 = 863119) (by norm_num)
theorem B1818029 : Blo 1211423 1818029 := bbase (se 3 (by rfl) ⟨340880, by rfl⟩ : syracuseStep 1818029 = 681761) (by norm_num)
theorem B2727341 : Blo 1211423 2727341 := bbase (se 3 (by rfl) ⟨511376, by rfl⟩ : syracuseStep 2727341 = 1022753) (by norm_num)
theorem B3882421 : Blo 1211423 3882421 := bbase (se 5 (by rfl) ⟨181988, by rfl⟩ : syracuseStep 3882421 = 363977) (by norm_num)
theorem B1818053 : Blo 1211423 1818053 := bbase (se 4 (by rfl) ⟨170442, by rfl⟩ : syracuseStep 1818053 = 340885) (by norm_num)
theorem B3071429 : Blo 1211423 3071429 := bbase (se 4 (by rfl) ⟨287946, by rfl⟩ : syracuseStep 3071429 = 575893) (by norm_num)
theorem B1818077 : Blo 1211423 1818077 := bbase (se 3 (by rfl) ⟨340889, by rfl⟩ : syracuseStep 1818077 = 681779) (by norm_num)
theorem B4144613 : Blo 1211423 4144613 := bbase (se 4 (by rfl) ⟨388557, by rfl⟩ : syracuseStep 4144613 = 777115) (by norm_num)
theorem B1818101 : Blo 1211423 1818101 := bbase (se 5 (by rfl) ⟨85223, by rfl⟩ : syracuseStep 1818101 = 170447) (by norm_num)
theorem B2727413 : Blo 1211423 2727413 := bbase (se 5 (by rfl) ⟨127847, by rfl⟩ : syracuseStep 2727413 = 255695) (by norm_num)
theorem B2047477 : Blo 1211423 2047477 := bbase (se 5 (by rfl) ⟨95975, by rfl⟩ : syracuseStep 2047477 = 191951) (by norm_num)
theorem B1228285 : Blo 1211423 1228285 := bbase (se 3 (by rfl) ⟨230303, by rfl⟩ : syracuseStep 1228285 = 460607) (by norm_num)
theorem B1293833 : Blo 1211423 1293833 := bbase (se 2 (by rfl) ⟨485187, by rfl⟩ : syracuseStep 1293833 = 970375) (by norm_num)
theorem B1818125 : Blo 1211423 1818125 := bbase (se 3 (by rfl) ⟨340898, by rfl⟩ : syracuseStep 1818125 = 681797) (by norm_num)
theorem B1818149 : Blo 1211423 1818149 := bbase (se 4 (by rfl) ⟨170451, by rfl⟩ : syracuseStep 1818149 = 340903) (by norm_num)
theorem B2588213 : Blo 1211423 2588213 := bbase (se 5 (by rfl) ⟨121322, by rfl⟩ : syracuseStep 2588213 = 242645) (by norm_num)
theorem B1818173 : Blo 1211423 1818173 := bbase (se 3 (by rfl) ⟨340907, by rfl⟩ : syracuseStep 1818173 = 681815) (by norm_num)
theorem B2727485 : Blo 1211423 2727485 := bbase (se 3 (by rfl) ⟨511403, by rfl⟩ : syracuseStep 2727485 = 1022807) (by norm_num)
theorem B2047565 : Blo 1211423 2047565 := bbase (se 3 (by rfl) ⟨383918, by rfl⟩ : syracuseStep 2047565 = 767837) (by norm_num)
theorem B1941077 : Blo 1211423 1941077 := bbase (se 8 (by rfl) ⟨11373, by rfl⟩ : syracuseStep 1941077 = 22747) (by norm_num)
theorem B1818197 : Blo 1211423 1818197 := bbase (se 8 (by rfl) ⟨10653, by rfl⟩ : syracuseStep 1818197 = 21307) (by norm_num)
theorem B1818221 : Blo 1211423 1818221 := bbase (se 3 (by rfl) ⟨340916, by rfl⟩ : syracuseStep 1818221 = 681833) (by norm_num)
theorem B1818245 : Blo 1211423 1818245 := bbase (se 4 (by rfl) ⟨170460, by rfl⟩ : syracuseStep 1818245 = 340921) (by norm_num)
theorem B2727557 : Blo 1211423 2727557 := bbase (se 4 (by rfl) ⟨255708, by rfl⟩ : syracuseStep 2727557 = 511417) (by norm_num)
theorem B1818269 : Blo 1211423 1818269 := bbase (se 3 (by rfl) ⟨340925, by rfl⟩ : syracuseStep 1818269 = 681851) (by norm_num)
theorem B2301605 : Blo 1211423 2301605 := bbase (se 4 (by rfl) ⟨215775, by rfl⟩ : syracuseStep 2301605 = 431551) (by norm_num)
theorem B1818293 : Blo 1211423 1818293 := bbase (se 5 (by rfl) ⟨85232, by rfl⟩ : syracuseStep 1818293 = 170465) (by norm_num)
theorem B1818317 : Blo 1211423 1818317 := bbase (se 3 (by rfl) ⟨340934, by rfl⟩ : syracuseStep 1818317 = 681869) (by norm_num)
theorem B2727629 : Blo 1211423 2727629 := bbase (se 3 (by rfl) ⟨511430, by rfl⟩ : syracuseStep 2727629 = 1022861) (by norm_num)
theorem B1818341 : Blo 1211423 1818341 := bbase (se 4 (by rfl) ⟨170469, by rfl⟩ : syracuseStep 1818341 = 340939) (by norm_num)
theorem B1818365 : Blo 1211423 1818365 := bbase (se 3 (by rfl) ⟨340943, by rfl⟩ : syracuseStep 1818365 = 681887) (by norm_num)
theorem B1556221 : Blo 1211423 1556221 := bbase (se 3 (by rfl) ⟨291791, by rfl⟩ : syracuseStep 1556221 = 583583) (by norm_num)
theorem B1818389 : Blo 1211423 1818389 := bbase (se 6 (by rfl) ⟨42618, by rfl⟩ : syracuseStep 1818389 = 85237) (by norm_num)
theorem B2727701 : Blo 1211423 2727701 := bbase (se 6 (by rfl) ⟨63930, by rfl⟩ : syracuseStep 2727701 = 127861) (by norm_num)
theorem B1818413 : Blo 1211423 1818413 := bbase (se 3 (by rfl) ⟨340952, by rfl⟩ : syracuseStep 1818413 = 681905) (by norm_num)
theorem B1228601 : Blo 1211423 1228601 := bbase (se 2 (by rfl) ⟨460725, by rfl⟩ : syracuseStep 1228601 = 921451) (by norm_num)
theorem B1818437 : Blo 1211423 1818437 := bbase (se 4 (by rfl) ⟨170478, by rfl⟩ : syracuseStep 1818437 = 340957) (by norm_num)
theorem B1818461 : Blo 1211423 1818461 := bbase (se 3 (by rfl) ⟨340961, by rfl⟩ : syracuseStep 1818461 = 681923) (by norm_num)
theorem B2727773 : Blo 1211423 2727773 := bbase (se 3 (by rfl) ⟨511457, by rfl⟩ : syracuseStep 2727773 = 1022915) (by norm_num)
theorem B1818485 : Blo 1211423 1818485 := bbase (se 5 (by rfl) ⟨85241, by rfl⟩ : syracuseStep 1818485 = 170483) (by norm_num)
theorem B1818509 : Blo 1211423 1818509 := bbase (se 3 (by rfl) ⟨340970, by rfl⟩ : syracuseStep 1818509 = 681941) (by norm_num)
theorem B2662301 : Blo 1211423 2662301 := bbase (se 3 (by rfl) ⟨499181, by rfl⟩ : syracuseStep 2662301 = 998363) (by norm_num)
theorem B1818533 : Blo 1211423 1818533 := bbase (se 4 (by rfl) ⟨170487, by rfl⟩ : syracuseStep 1818533 = 340975) (by norm_num)
theorem B2727845 : Blo 1211423 2727845 := bbase (se 4 (by rfl) ⟨255735, by rfl⟩ : syracuseStep 2727845 = 511471) (by norm_num)
theorem B1818557 : Blo 1211423 1818557 := bbase (se 3 (by rfl) ⟨340979, by rfl⟩ : syracuseStep 1818557 = 681959) (by norm_num)
theorem B6135749 : Blo 1211423 6135749 := bbase (se 4 (by rfl) ⟨575226, by rfl⟩ : syracuseStep 6135749 = 1150453) (by norm_num)
theorem B1294277 : Blo 1211423 1294277 := bbase (se 4 (by rfl) ⟨121338, by rfl⟩ : syracuseStep 1294277 = 242677) (by norm_num)
theorem B1818581 : Blo 1211423 1818581 := bbase (se 7 (by rfl) ⟨21311, by rfl⟩ : syracuseStep 1818581 = 42623) (by norm_num)
theorem B1818605 : Blo 1211423 1818605 := bbase (se 3 (by rfl) ⟨340988, by rfl⟩ : syracuseStep 1818605 = 681977) (by norm_num)
theorem B2727917 : Blo 1211423 2727917 := bbase (se 3 (by rfl) ⟨511484, by rfl⟩ : syracuseStep 2727917 = 1022969) (by norm_num)
theorem B3497987 : Blo 1211423 3497987 := bstep (se 1 (by rfl) ⟨2623490, by rfl⟩ : syracuseStep 3497987 = 5246981) B5246981
theorem B1212419 : Blo 1211423 1212419 := bstep (se 1 (by rfl) ⟨909314, by rfl⟩ : syracuseStep 1212419 = 1818629) B1818629
theorem B2727953 : Blo 1211423 2727953 := bstep (se 2 (by rfl) ⟨1022982, by rfl⟩ : syracuseStep 2727953 = 2045965) B2045965
theorem B1818641 : Blo 1211423 1818641 := bstep (se 2 (by rfl) ⟨681990, by rfl⟩ : syracuseStep 1818641 = 1363981) B1363981
theorem B1212435 : Blo 1211423 1212435 := bstep (se 1 (by rfl) ⟨909326, by rfl⟩ : syracuseStep 1212435 = 1818653) B1818653
theorem B7872547 : Blo 1211423 7872547 := bstep (se 1 (by rfl) ⟨5904410, by rfl⟩ : syracuseStep 7872547 = 11808821) B11808821
theorem B2727971 : Blo 1211423 2727971 := bstep (se 1 (by rfl) ⟨2045978, by rfl⟩ : syracuseStep 2727971 = 4091957) B4091957
theorem B1818659 : Blo 1211423 1818659 := bstep (se 1 (by rfl) ⟨1363994, by rfl⟩ : syracuseStep 1818659 = 2727989) B2727989
theorem B1212451 : Blo 1211423 1212451 := bstep (se 1 (by rfl) ⟨909338, by rfl⟩ : syracuseStep 1212451 = 1818677) B1818677
theorem B1212467 : Blo 1211423 1212467 := bstep (se 1 (by rfl) ⟨909350, by rfl⟩ : syracuseStep 1212467 = 1818701) B1818701
theorem B53157941 : Blo 1211423 53157941 := bstep (se 5 (by rfl) ⟨2491778, by rfl⟩ : syracuseStep 53157941 = 4983557) B4983557
theorem B1818689 : Blo 1211423 1818689 := bstep (se 2 (by rfl) ⟨682008, by rfl⟩ : syracuseStep 1818689 = 1364017) B1364017
theorem B1212483 : Blo 1211423 1212483 := bstep (se 1 (by rfl) ⟨909362, by rfl⟩ : syracuseStep 1212483 = 1818725) B1818725
theorem B16597061 : Blo 1211423 16597061 := bstep (se 4 (by rfl) ⟨1555974, by rfl⟩ : syracuseStep 16597061 = 3111949) B3111949
theorem B1638481 : Blo 1211423 1638481 := bstep (se 2 (by rfl) ⟨614430, by rfl⟩ : syracuseStep 1638481 = 1228861) B1228861
theorem B1818707 : Blo 1211423 1818707 := bstep (se 1 (by rfl) ⟨1364030, by rfl⟩ : syracuseStep 1818707 = 2728061) B2728061
theorem B1212499 : Blo 1211423 1212499 := bstep (se 1 (by rfl) ⟨909374, by rfl⟩ : syracuseStep 1212499 = 1818749) B1818749
theorem B1212515 : Blo 1211423 1212515 := bstep (se 1 (by rfl) ⟨909386, by rfl⟩ : syracuseStep 1212515 = 1818773) B1818773
theorem B39321713 : Blo 1211423 39321713 := bstep (se 2 (by rfl) ⟨14745642, by rfl⟩ : syracuseStep 39321713 = 29491285) B29491285
theorem B4915313 : Blo 1211423 4915313 := bstep (se 2 (by rfl) ⟨1843242, by rfl⟩ : syracuseStep 4915313 = 3686485) B3686485
theorem B1818737 : Blo 1211423 1818737 := bstep (se 2 (by rfl) ⟨682026, by rfl⟩ : syracuseStep 1818737 = 1364053) B1364053
theorem B1212531 : Blo 1211423 1212531 := bstep (se 1 (by rfl) ⟨909398, by rfl⟩ : syracuseStep 1212531 = 1818797) B1818797
theorem B1818755 : Blo 1211423 1818755 := bstep (se 1 (by rfl) ⟨1364066, by rfl⟩ : syracuseStep 1818755 = 2728133) B2728133
theorem B1212547 : Blo 1211423 1212547 := bstep (se 1 (by rfl) ⟨909410, by rfl⟩ : syracuseStep 1212547 = 1818821) B1818821
theorem B1212563 : Blo 1211423 1212563 := bstep (se 1 (by rfl) ⟨909422, by rfl⟩ : syracuseStep 1212563 = 1818845) B1818845
theorem B1818785 : Blo 1211423 1818785 := bstep (se 2 (by rfl) ⟨682044, by rfl⟩ : syracuseStep 1818785 = 1364089) B1364089
theorem B1294499 : Blo 1211423 1294499 := bstep (se 1 (by rfl) ⟨970874, by rfl⟩ : syracuseStep 1294499 = 1941749) B1941749
theorem B1212579 : Blo 1211423 1212579 := bstep (se 1 (by rfl) ⟨909434, by rfl⟩ : syracuseStep 1212579 = 1818869) B1818869
theorem B1818803 : Blo 1211423 1818803 := bstep (se 1 (by rfl) ⟨1364102, by rfl⟩ : syracuseStep 1818803 = 2728205) B2728205
theorem B1212595 : Blo 1211423 1212595 := bstep (se 1 (by rfl) ⟨909446, by rfl⟩ : syracuseStep 1212595 = 1818893) B1818893
theorem B1212611 : Blo 1211423 1212611 := bstep (se 1 (by rfl) ⟨909458, by rfl⟩ : syracuseStep 1212611 = 1818917) B1818917
theorem B30286021 : Blo 1211423 30286021 := bstep (se 4 (by rfl) ⟨2839314, by rfl⟩ : syracuseStep 30286021 = 5678629) B5678629
theorem B1818833 : Blo 1211423 1818833 := bstep (se 2 (by rfl) ⟨682062, by rfl⟩ : syracuseStep 1818833 = 1364125) B1364125
theorem B1212627 : Blo 1211423 1212627 := bstep (se 1 (by rfl) ⟨909470, by rfl⟩ : syracuseStep 1212627 = 1818941) B1818941
theorem B1818851 : Blo 1211423 1818851 := bstep (se 1 (by rfl) ⟨1364138, by rfl⟩ : syracuseStep 1818851 = 2728277) B2728277
theorem B1212643 : Blo 1211423 1212643 := bstep (se 1 (by rfl) ⟨909482, by rfl⟩ : syracuseStep 1212643 = 1818965) B1818965
theorem B1212659 : Blo 1211423 1212659 := bstep (se 1 (by rfl) ⟨909494, by rfl⟩ : syracuseStep 1212659 = 1818989) B1818989
theorem B1818881 : Blo 1211423 1818881 := bstep (se 2 (by rfl) ⟨682080, by rfl⟩ : syracuseStep 1818881 = 1364161) B1364161
theorem B1212675 : Blo 1211423 1212675 := bstep (se 1 (by rfl) ⟨909506, by rfl⟩ : syracuseStep 1212675 = 1819013) B1819013
theorem B1818899 : Blo 1211423 1818899 := bstep (se 1 (by rfl) ⟨1364174, by rfl⟩ : syracuseStep 1818899 = 2728349) B2728349
theorem B1212691 : Blo 1211423 1212691 := bstep (se 1 (by rfl) ⟨909518, by rfl⟩ : syracuseStep 1212691 = 1819037) B1819037
theorem B1212707 : Blo 1211423 1212707 := bstep (se 1 (by rfl) ⟨909530, by rfl⟩ : syracuseStep 1212707 = 1819061) B1819061
theorem B2728241 : Blo 1211423 2728241 := bstep (se 2 (by rfl) ⟨1023090, by rfl⟩ : syracuseStep 2728241 = 2046181) B2046181
theorem B1818929 : Blo 1211423 1818929 := bstep (se 2 (by rfl) ⟨682098, by rfl⟩ : syracuseStep 1818929 = 1364197) B1364197
theorem B1212723 : Blo 1211423 1212723 := bstep (se 1 (by rfl) ⟨909542, by rfl⟩ : syracuseStep 1212723 = 1819085) B1819085
theorem B2728259 : Blo 1211423 2728259 := bstep (se 1 (by rfl) ⟨2046194, by rfl⟩ : syracuseStep 2728259 = 4092389) B4092389
theorem B1818947 : Blo 1211423 1818947 := bstep (se 1 (by rfl) ⟨1364210, by rfl⟩ : syracuseStep 1818947 = 2728421) B2728421
theorem B6906181 : Blo 1211423 6906181 := bstep (se 4 (by rfl) ⟨647454, by rfl⟩ : syracuseStep 6906181 = 1294909) B1294909
theorem B1212739 : Blo 1211423 1212739 := bstep (se 1 (by rfl) ⟨909554, by rfl⟩ : syracuseStep 1212739 = 1819109) B1819109
theorem B1212755 : Blo 1211423 1212755 := bstep (se 1 (by rfl) ⟨909566, by rfl⟩ : syracuseStep 1212755 = 1819133) B1819133
theorem B1818977 : Blo 1211423 1818977 := bstep (se 2 (by rfl) ⟨682116, by rfl⟩ : syracuseStep 1818977 = 1364233) B1364233
theorem B1212771 : Blo 1211423 1212771 := bstep (se 1 (by rfl) ⟨909578, by rfl⟩ : syracuseStep 1212771 = 1819157) B1819157
theorem B4604273 : Blo 1211423 4604273 := bstep (se 2 (by rfl) ⟨1726602, by rfl⟩ : syracuseStep 4604273 = 3453205) B3453205
theorem B1818995 : Blo 1211423 1818995 := bstep (se 1 (by rfl) ⟨1364246, by rfl⟩ : syracuseStep 1818995 = 2728493) B2728493
theorem B1212787 : Blo 1211423 1212787 := bstep (se 1 (by rfl) ⟨909590, by rfl⟩ : syracuseStep 1212787 = 1819181) B1819181
theorem B2589059 : Blo 1211423 2589059 := bstep (se 1 (by rfl) ⟨1941794, by rfl⟩ : syracuseStep 2589059 = 3883589) B3883589
theorem B1212803 : Blo 1211423 1212803 := bstep (se 1 (by rfl) ⟨909602, by rfl⟩ : syracuseStep 1212803 = 1819205) B1819205
theorem B1819025 : Blo 1211423 1819025 := bstep (se 2 (by rfl) ⟨682134, by rfl⟩ : syracuseStep 1819025 = 1364269) B1364269
theorem B1212819 : Blo 1211423 1212819 := bstep (se 1 (by rfl) ⟨909614, by rfl⟩ : syracuseStep 1212819 = 1819229) B1819229
theorem B1819043 : Blo 1211423 1819043 := bstep (se 1 (by rfl) ⟨1364282, by rfl⟩ : syracuseStep 1819043 = 2728565) B2728565
theorem B1212835 : Blo 1211423 1212835 := bstep (se 1 (by rfl) ⟨909626, by rfl⟩ : syracuseStep 1212835 = 1819253) B1819253
theorem B1212851 : Blo 1211423 1212851 := bstep (se 1 (by rfl) ⟨909638, by rfl⟩ : syracuseStep 1212851 = 1819277) B1819277
theorem B1819073 : Blo 1211423 1819073 := bstep (se 2 (by rfl) ⟨682152, by rfl⟩ : syracuseStep 1819073 = 1364305) B1364305
theorem B1212867 : Blo 1211423 1212867 := bstep (se 1 (by rfl) ⟨909650, by rfl⟩ : syracuseStep 1212867 = 1819301) B1819301
theorem B1819091 : Blo 1211423 1819091 := bstep (se 1 (by rfl) ⟨1364318, by rfl⟩ : syracuseStep 1819091 = 2728637) B2728637
theorem B1212883 : Blo 1211423 1212883 := bstep (se 1 (by rfl) ⟨909662, by rfl⟩ : syracuseStep 1212883 = 1819325) B1819325
theorem B1212899 : Blo 1211423 1212899 := bstep (se 1 (by rfl) ⟨909674, by rfl⟩ : syracuseStep 1212899 = 1819349) B1819349
theorem B3277297 : Blo 1211423 3277297 := bstep (se 2 (by rfl) ⟨1228986, by rfl⟩ : syracuseStep 3277297 = 2457973) B2457973
theorem B1819121 : Blo 1211423 1819121 := bstep (se 2 (by rfl) ⟨682170, by rfl⟩ : syracuseStep 1819121 = 1364341) B1364341
theorem B1212915 : Blo 1211423 1212915 := bstep (se 1 (by rfl) ⟨909686, by rfl⟩ : syracuseStep 1212915 = 1819373) B1819373
theorem B1819139 : Blo 1211423 1819139 := bstep (se 1 (by rfl) ⟨1364354, by rfl⟩ : syracuseStep 1819139 = 2728709) B2728709
theorem B1212931 : Blo 1211423 1212931 := bstep (se 1 (by rfl) ⟨909698, by rfl⟩ : syracuseStep 1212931 = 1819397) B1819397
theorem B1212947 : Blo 1211423 1212947 := bstep (se 1 (by rfl) ⟨909710, by rfl⟩ : syracuseStep 1212947 = 1819421) B1819421
theorem B1819169 : Blo 1211423 1819169 := bstep (se 2 (by rfl) ⟨682188, by rfl⟩ : syracuseStep 1819169 = 1364377) B1364377
theorem B1942051 : Blo 1211423 1942051 := bstep (se 1 (by rfl) ⟨1456538, by rfl⟩ : syracuseStep 1942051 = 2913077) B2913077
theorem B1212963 : Blo 1211423 1212963 := bstep (se 1 (by rfl) ⟨909722, by rfl⟩ : syracuseStep 1212963 = 1819445) B1819445
theorem B1819187 : Blo 1211423 1819187 := bstep (se 1 (by rfl) ⟨1364390, by rfl⟩ : syracuseStep 1819187 = 2728781) B2728781
theorem B1212979 : Blo 1211423 1212979 := bstep (se 1 (by rfl) ⟨909734, by rfl⟩ : syracuseStep 1212979 = 1819469) B1819469
theorem B1516099 : Blo 1211423 1516099 := bstep (se 1 (by rfl) ⟨1137074, by rfl⟩ : syracuseStep 1516099 = 2274149) B2274149
theorem B1212995 : Blo 1211423 1212995 := bstep (se 1 (by rfl) ⟨909746, by rfl⟩ : syracuseStep 1212995 = 1819493) B1819493
theorem B6136397 : Blo 1211423 6136397 := bstep (se 3 (by rfl) ⟨1150574, by rfl⟩ : syracuseStep 6136397 = 2301149) B2301149
theorem B2728529 : Blo 1211423 2728529 := bstep (se 2 (by rfl) ⟨1023198, by rfl⟩ : syracuseStep 2728529 = 2046397) B2046397
theorem B1819217 : Blo 1211423 1819217 := bstep (se 2 (by rfl) ⟨682206, by rfl⟩ : syracuseStep 1819217 = 1364413) B1364413
theorem B1213011 : Blo 1211423 1213011 := bstep (se 1 (by rfl) ⟨909758, by rfl⟩ : syracuseStep 1213011 = 1819517) B1819517
theorem B2728547 : Blo 1211423 2728547 := bstep (se 1 (by rfl) ⟨2046410, by rfl⟩ : syracuseStep 2728547 = 4092821) B4092821
theorem B1819235 : Blo 1211423 1819235 := bstep (se 1 (by rfl) ⟨1364426, by rfl⟩ : syracuseStep 1819235 = 2728853) B2728853
theorem B1213027 : Blo 1211423 1213027 := bstep (se 1 (by rfl) ⟨909770, by rfl⟩ : syracuseStep 1213027 = 1819541) B1819541
theorem B4366961 : Blo 1211423 4366961 := bstep (se 2 (by rfl) ⟨1637610, by rfl⟩ : syracuseStep 4366961 = 3275221) B3275221
theorem B2302577 : Blo 1211423 2302577 := bstep (se 2 (by rfl) ⟨863466, by rfl⟩ : syracuseStep 2302577 = 1726933) B1726933
theorem B1213043 : Blo 1211423 1213043 := bstep (se 1 (by rfl) ⟨909782, by rfl⟩ : syracuseStep 1213043 = 1819565) B1819565
theorem B1819265 : Blo 1211423 1819265 := bstep (se 2 (by rfl) ⟨682224, by rfl⟩ : syracuseStep 1819265 = 1364449) B1364449
theorem B1213059 : Blo 1211423 1213059 := bstep (se 1 (by rfl) ⟨909794, by rfl⟩ : syracuseStep 1213059 = 1819589) B1819589
theorem B1819283 : Blo 1211423 1819283 := bstep (se 1 (by rfl) ⟨1364462, by rfl⟩ : syracuseStep 1819283 = 2728925) B2728925
theorem B1213075 : Blo 1211423 1213075 := bstep (se 1 (by rfl) ⟨909806, by rfl⟩ : syracuseStep 1213075 = 1819613) B1819613
theorem B1213091 : Blo 1211423 1213091 := bstep (se 1 (by rfl) ⟨909818, by rfl⟩ : syracuseStep 1213091 = 1819637) B1819637
theorem B1819313 : Blo 1211423 1819313 := bstep (se 2 (by rfl) ⟨682242, by rfl⟩ : syracuseStep 1819313 = 1364485) B1364485
theorem B1213107 : Blo 1211423 1213107 := bstep (se 1 (by rfl) ⟨909830, by rfl⟩ : syracuseStep 1213107 = 1819661) B1819661
theorem B1819331 : Blo 1211423 1819331 := bstep (se 1 (by rfl) ⟨1364498, by rfl⟩ : syracuseStep 1819331 = 2728997) B2728997
theorem B1213123 : Blo 1211423 1213123 := bstep (se 1 (by rfl) ⟨909842, by rfl⟩ : syracuseStep 1213123 = 1819685) B1819685
theorem B1213139 : Blo 1211423 1213139 := bstep (se 1 (by rfl) ⟨909854, by rfl⟩ : syracuseStep 1213139 = 1819709) B1819709
theorem B1819361 : Blo 1211423 1819361 := bstep (se 2 (by rfl) ⟨682260, by rfl⟩ : syracuseStep 1819361 = 1364521) B1364521
theorem B1213155 : Blo 1211423 1213155 := bstep (se 1 (by rfl) ⟨909866, by rfl⟩ : syracuseStep 1213155 = 1819733) B1819733
theorem B1819379 : Blo 1211423 1819379 := bstep (se 1 (by rfl) ⟨1364534, by rfl⟩ : syracuseStep 1819379 = 2729069) B2729069
theorem B1213171 : Blo 1211423 1213171 := bstep (se 1 (by rfl) ⟨909878, by rfl⟩ : syracuseStep 1213171 = 1819757) B1819757
theorem B1213187 : Blo 1211423 1213187 := bstep (se 1 (by rfl) ⟨909890, by rfl⟩ : syracuseStep 1213187 = 1819781) B1819781
theorem B1843985 : Blo 1211423 1843985 := bstep (se 2 (by rfl) ⟨691494, by rfl⟩ : syracuseStep 1843985 = 1382989) B1382989
theorem B1819409 : Blo 1211423 1819409 := bstep (se 2 (by rfl) ⟨682278, by rfl⟩ : syracuseStep 1819409 = 1364557) B1364557
theorem B1213203 : Blo 1211423 1213203 := bstep (se 1 (by rfl) ⟨909902, by rfl⟩ : syracuseStep 1213203 = 1819805) B1819805
theorem B1942307 : Blo 1211423 1942307 := bstep (se 1 (by rfl) ⟨1456730, by rfl⟩ : syracuseStep 1942307 = 2913461) B2913461
theorem B1819427 : Blo 1211423 1819427 := bstep (se 1 (by rfl) ⟨1364570, by rfl⟩ : syracuseStep 1819427 = 2729141) B2729141
theorem B1213219 : Blo 1211423 1213219 := bstep (se 1 (by rfl) ⟨909914, by rfl⟩ : syracuseStep 1213219 = 1819829) B1819829
theorem B1213235 : Blo 1211423 1213235 := bstep (se 1 (by rfl) ⟨909926, by rfl⟩ : syracuseStep 1213235 = 1819853) B1819853
theorem B26272565 : Blo 1211423 26272565 := bstep (se 5 (by rfl) ⟨1231526, by rfl⟩ : syracuseStep 26272565 = 2463053) B2463053
theorem B1819457 : Blo 1211423 1819457 := bstep (se 2 (by rfl) ⟨682296, by rfl⟩ : syracuseStep 1819457 = 1364593) B1364593
theorem B1213251 : Blo 1211423 1213251 := bstep (se 1 (by rfl) ⟨909938, by rfl⟩ : syracuseStep 1213251 = 1819877) B1819877
theorem B1819475 : Blo 1211423 1819475 := bstep (se 1 (by rfl) ⟨1364606, by rfl⟩ : syracuseStep 1819475 = 2729213) B2729213
theorem B1213267 : Blo 1211423 1213267 := bstep (se 1 (by rfl) ⟨909950, by rfl⟩ : syracuseStep 1213267 = 1819901) B1819901
theorem B1213283 : Blo 1211423 1213283 := bstep (se 1 (by rfl) ⟨909962, by rfl⟩ : syracuseStep 1213283 = 1819925) B1819925
theorem B2728817 : Blo 1211423 2728817 := bstep (se 2 (by rfl) ⟨1023306, by rfl⟩ : syracuseStep 2728817 = 2046613) B2046613
theorem B1819505 : Blo 1211423 1819505 := bstep (se 2 (by rfl) ⟨682314, by rfl⟩ : syracuseStep 1819505 = 1364629) B1364629
theorem B1213299 : Blo 1211423 1213299 := bstep (se 1 (by rfl) ⟨909974, by rfl⟩ : syracuseStep 1213299 = 1819949) B1819949
theorem B3883907 : Blo 1211423 3883907 := bstep (se 1 (by rfl) ⟨2912930, by rfl⟩ : syracuseStep 3883907 = 5825861) B5825861
theorem B2728835 : Blo 1211423 2728835 := bstep (se 1 (by rfl) ⟨2046626, by rfl⟩ : syracuseStep 2728835 = 4093253) B4093253
theorem B1819523 : Blo 1211423 1819523 := bstep (se 1 (by rfl) ⟨1364642, by rfl⟩ : syracuseStep 1819523 = 2729285) B2729285
theorem B1213315 : Blo 1211423 1213315 := bstep (se 1 (by rfl) ⟨909986, by rfl⟩ : syracuseStep 1213315 = 1819973) B1819973
theorem B4088717 : Blo 1211423 4088717 := bstep (se 3 (by rfl) ⟨766634, by rfl⟩ : syracuseStep 4088717 = 1533269) B1533269
theorem B1868689 : Blo 1211423 1868689 := bstep (se 2 (by rfl) ⟨700758, by rfl⟩ : syracuseStep 1868689 = 1401517) B1401517
theorem B1213331 : Blo 1211423 1213331 := bstep (se 1 (by rfl) ⟨909998, by rfl⟩ : syracuseStep 1213331 = 1819997) B1819997
theorem B1819553 : Blo 1211423 1819553 := bstep (se 2 (by rfl) ⟨682332, by rfl⟩ : syracuseStep 1819553 = 1364665) B1364665
theorem B5530531 : Blo 1211423 5530531 := bstep (se 1 (by rfl) ⟨4147898, by rfl⟩ : syracuseStep 5530531 = 8295797) B8295797
theorem B1213347 : Blo 1211423 1213347 := bstep (se 1 (by rfl) ⟨910010, by rfl⟩ : syracuseStep 1213347 = 1820021) B1820021
theorem B1819571 : Blo 1211423 1819571 := bstep (se 1 (by rfl) ⟨1364678, by rfl⟩ : syracuseStep 1819571 = 2729357) B2729357
theorem B1213363 : Blo 1211423 1213363 := bstep (se 1 (by rfl) ⟨910022, by rfl⟩ : syracuseStep 1213363 = 1820045) B1820045
theorem B4088771 : Blo 1211423 4088771 := bstep (se 1 (by rfl) ⟨3066578, by rfl⟩ : syracuseStep 4088771 = 6133157) B6133157
theorem B1213379 : Blo 1211423 1213379 := bstep (se 1 (by rfl) ⟨910034, by rfl⟩ : syracuseStep 1213379 = 1820069) B1820069
theorem B1819601 : Blo 1211423 1819601 := bstep (se 2 (by rfl) ⟨682350, by rfl⟩ : syracuseStep 1819601 = 1364701) B1364701
theorem B1213395 : Blo 1211423 1213395 := bstep (se 1 (by rfl) ⟨910046, by rfl⟩ : syracuseStep 1213395 = 1820093) B1820093
theorem B1819619 : Blo 1211423 1819619 := bstep (se 1 (by rfl) ⟨1364714, by rfl⟩ : syracuseStep 1819619 = 2729429) B2729429
theorem B1213411 : Blo 1211423 1213411 := bstep (se 1 (by rfl) ⟨910058, by rfl⟩ : syracuseStep 1213411 = 1820117) B1820117
theorem B1819649 : Blo 1211423 1819649 := bstep (se 2 (by rfl) ⟨682368, by rfl⟩ : syracuseStep 1819649 = 1364737) B1364737
theorem B1819667 : Blo 1211423 1819667 := bstep (se 1 (by rfl) ⟨1364750, by rfl⟩ : syracuseStep 1819667 = 2729501) B2729501
theorem B3449891 : Blo 1211423 3449891 := bstep (se 1 (by rfl) ⟨2587418, by rfl⟩ : syracuseStep 3449891 = 5174837) B5174837
theorem B1819697 : Blo 1211423 1819697 := bstep (se 2 (by rfl) ⟨682386, by rfl⟩ : syracuseStep 1819697 = 1364773) B1364773
theorem B1819715 : Blo 1211423 1819715 := bstep (se 1 (by rfl) ⟨1364786, by rfl⟩ : syracuseStep 1819715 = 2729573) B2729573
theorem B1819745 : Blo 1211423 1819745 := bstep (se 2 (by rfl) ⟨682404, by rfl⟩ : syracuseStep 1819745 = 1364809) B1364809
theorem B1967203 : Blo 1211423 1967203 := bstep (se 1 (by rfl) ⟨1475402, by rfl⟩ : syracuseStep 1967203 = 2950805) B2950805
theorem B1819763 : Blo 1211423 1819763 := bstep (se 1 (by rfl) ⟨1364822, by rfl⟩ : syracuseStep 1819763 = 2729645) B2729645
theorem B2729105 : Blo 1211423 2729105 := bstep (se 2 (by rfl) ⟨1023414, by rfl⟩ : syracuseStep 2729105 = 2046829) B2046829
theorem B1819793 : Blo 1211423 1819793 := bstep (se 2 (by rfl) ⟨682422, by rfl⟩ : syracuseStep 1819793 = 1364845) B1364845
theorem B5530787 : Blo 1211423 5530787 := bstep (se 1 (by rfl) ⟨4148090, by rfl⟩ : syracuseStep 5530787 = 8296181) B8296181
theorem B2729123 : Blo 1211423 2729123 := bstep (se 1 (by rfl) ⟨2046842, by rfl⟩ : syracuseStep 2729123 = 4093685) B4093685
theorem B1819811 : Blo 1211423 1819811 := bstep (se 1 (by rfl) ⟨1364858, by rfl⟩ : syracuseStep 1819811 = 2729717) B2729717
theorem B1819841 : Blo 1211423 1819841 := bstep (se 2 (by rfl) ⟨682440, by rfl⟩ : syracuseStep 1819841 = 1364881) B1364881
theorem B4089041 : Blo 1211423 4089041 := bstep (se 2 (by rfl) ⟨1533390, by rfl⟩ : syracuseStep 4089041 = 3066781) B3066781
theorem B1819859 : Blo 1211423 1819859 := bstep (se 1 (by rfl) ⟨1364894, by rfl⟩ : syracuseStep 1819859 = 2729789) B2729789
theorem B1819889 : Blo 1211423 1819889 := bstep (se 2 (by rfl) ⟨682458, by rfl⟩ : syracuseStep 1819889 = 1364917) B1364917
theorem B1819907 : Blo 1211423 1819907 := bstep (se 1 (by rfl) ⟨1364930, by rfl⟩ : syracuseStep 1819907 = 2729861) B2729861
theorem B11052301 : Blo 1211423 11052301 := bstep (se 3 (by rfl) ⟨2072306, by rfl⟩ : syracuseStep 11052301 = 4144613) B4144613
theorem B1819937 : Blo 1211423 1819937 := bstep (se 2 (by rfl) ⟨682476, by rfl⟩ : syracuseStep 1819937 = 1364953) B1364953
theorem B1819955 : Blo 1211423 1819955 := bstep (se 1 (by rfl) ⟨1364966, by rfl⟩ : syracuseStep 1819955 = 2729933) B2729933
theorem B1819985 : Blo 1211423 1819985 := bstep (se 2 (by rfl) ⟨682494, by rfl⟩ : syracuseStep 1819985 = 1364989) B1364989
theorem B13813091 : Blo 1211423 13813091 := bstep (se 1 (by rfl) ⟨10359818, by rfl⟩ : syracuseStep 13813091 = 20719637) B20719637
theorem B1820003 : Blo 1211423 1820003 := bstep (se 1 (by rfl) ⟨1365002, by rfl⟩ : syracuseStep 1820003 = 2730005) B2730005
theorem B3450221 : Blo 1211423 3450221 := bstep (se 3 (by rfl) ⟨646916, by rfl⟩ : syracuseStep 3450221 = 1293833) B1293833
theorem B1820033 : Blo 1211423 1820033 := bstep (se 2 (by rfl) ⟨682512, by rfl⟩ : syracuseStep 1820033 = 1365025) B1365025
theorem B1820051 : Blo 1211423 1820051 := bstep (se 1 (by rfl) ⟨1365038, by rfl⟩ : syracuseStep 1820051 = 2730077) B2730077
theorem B3450289 : Blo 1211423 3450289 := bstep (se 2 (by rfl) ⟨1293858, by rfl⟩ : syracuseStep 3450289 = 2587717) B2587717
theorem B2729393 : Blo 1211423 2729393 := bstep (se 2 (by rfl) ⟨1023522, by rfl⟩ : syracuseStep 2729393 = 2047045) B2047045
theorem B1820081 : Blo 1211423 1820081 := bstep (se 2 (by rfl) ⟨682530, by rfl⟩ : syracuseStep 1820081 = 1365061) B1365061
theorem B2729411 : Blo 1211423 2729411 := bstep (se 1 (by rfl) ⟨2047058, by rfl⟩ : syracuseStep 2729411 = 4094117) B4094117
theorem B1820099 : Blo 1211423 1820099 := bstep (se 1 (by rfl) ⟨1365074, by rfl⟩ : syracuseStep 1820099 = 2730149) B2730149
theorem B1820129 : Blo 1211423 1820129 := bstep (se 2 (by rfl) ⟨682548, by rfl⟩ : syracuseStep 1820129 = 1365097) B1365097
theorem B2303473 : Blo 1211423 2303473 := bstep (se 2 (by rfl) ⟨863802, by rfl⟩ : syracuseStep 2303473 = 1727605) B1727605
theorem B2590289 : Blo 1211423 2590289 := bstep (se 2 (by rfl) ⟨971358, by rfl⟩ : syracuseStep 2590289 = 1942717) B1942717
theorem B1844849 : Blo 1211423 1844849 := bstep (se 2 (by rfl) ⟨691818, by rfl⟩ : syracuseStep 1844849 = 1383637) B1383637
theorem B3450563 : Blo 1211423 3450563 := bstep (se 1 (by rfl) ⟨2587922, by rfl⟩ : syracuseStep 3450563 = 5175845) B5175845
theorem B2729681 : Blo 1211423 2729681 := bstep (se 2 (by rfl) ⟨1023630, by rfl⟩ : syracuseStep 2729681 = 2047261) B2047261
theorem B2729699 : Blo 1211423 2729699 := bstep (se 1 (by rfl) ⟨2047274, by rfl⟩ : syracuseStep 2729699 = 4094549) B4094549
theorem B4089581 : Blo 1211423 4089581 := bstep (se 3 (by rfl) ⟨766796, by rfl⟩ : syracuseStep 4089581 = 1533593) B1533593
theorem B1943281 : Blo 1211423 1943281 := bstep (se 2 (by rfl) ⟨728730, by rfl⟩ : syracuseStep 1943281 = 1457461) B1457461
theorem B4089635 : Blo 1211423 4089635 := bstep (se 1 (by rfl) ⟨3067226, by rfl⟩ : syracuseStep 4089635 = 6134453) B6134453
theorem B4605731 : Blo 1211423 4605731 := bstep (se 1 (by rfl) ⟨3454298, by rfl⟩ : syracuseStep 4605731 = 6908597) B6908597
theorem B9209699 : Blo 1211423 9209699 := bstep (se 1 (by rfl) ⟨6907274, by rfl⟩ : syracuseStep 9209699 = 13814549) B13814549
theorem B1533811 : Blo 1211423 1533811 := bstep (se 1 (by rfl) ⟨1150358, by rfl⟩ : syracuseStep 1533811 = 2300717) B2300717
theorem B1533907 : Blo 1211423 1533907 := bstep (se 1 (by rfl) ⟨1150430, by rfl⟩ : syracuseStep 1533907 = 2300861) B2300861
theorem B1968113 : Blo 1211423 1968113 := bstep (se 2 (by rfl) ⟨738042, by rfl⟩ : syracuseStep 1968113 = 1476085) B1476085
theorem B2729969 : Blo 1211423 2729969 := bstep (se 2 (by rfl) ⟨1023738, by rfl⟩ : syracuseStep 2729969 = 2047477) B2047477
theorem B2729987 : Blo 1211423 2729987 := bstep (se 1 (by rfl) ⟨2047490, by rfl⟩ : syracuseStep 2729987 = 4094981) B4094981
theorem B4089905 : Blo 1211423 4089905 := bstep (se 2 (by rfl) ⟨1533714, by rfl⟩ : syracuseStep 4089905 = 3067429) B3067429
theorem B40962161 : Blo 1211423 40962161 := bstep (se 2 (by rfl) ⟨15360810, by rfl⟩ : syracuseStep 40962161 = 30721621) B30721621
theorem B1870067 : Blo 1211423 1870067 := bstep (se 1 (by rfl) ⟨1402550, by rfl⟩ : syracuseStep 1870067 = 2805101) B2805101
theorem B6908165 : Blo 1211423 6908165 := bstep (se 4 (by rfl) ⟨647640, by rfl⟩ : syracuseStep 6908165 = 1295281) B1295281
theorem B2074961 : Blo 1211423 2074961 := bstep (se 2 (by rfl) ⟨778110, by rfl⟩ : syracuseStep 2074961 = 1556221) B1556221
theorem B2623907 : Blo 1211423 2623907 := bstep (se 1 (by rfl) ⟨1967930, by rfl⟩ : syracuseStep 2623907 = 3935861) B3935861
theorem B1534403 : Blo 1211423 1534403 := bstep (se 1 (by rfl) ⟨1150802, by rfl⟩ : syracuseStep 1534403 = 2301605) B2301605
theorem B11659717 : Blo 1211423 11659717 := bstep (se 4 (by rfl) ⟨1093098, by rfl⟩ : syracuseStep 11659717 = 2186197) B2186197
theorem B2591185 : Blo 1211423 2591185 := bstep (se 2 (by rfl) ⟨971694, by rfl⟩ : syracuseStep 2591185 = 1943389) B1943389
theorem B2591203 : Blo 1211423 2591203 := bstep (se 1 (by rfl) ⟨1943402, by rfl⟩ : syracuseStep 2591203 = 3886805) B3886805
theorem B6220273 : Blo 1211423 6220273 := bstep (se 2 (by rfl) ⟨2332602, by rfl⟩ : syracuseStep 6220273 = 4665205) B4665205
theorem B3451405 : Blo 1211423 3451405 := bstep (se 3 (by rfl) ⟨647138, by rfl⟩ : syracuseStep 3451405 = 1294277) B1294277
theorem B4090445 : Blo 1211423 4090445 := bstep (se 3 (by rfl) ⟨766958, by rfl⟩ : syracuseStep 4090445 = 1533917) B1533917
theorem B3885677 : Blo 1211423 3885677 := bstep (se 3 (by rfl) ⟨728564, by rfl⟩ : syracuseStep 3885677 = 1457129) B1457129
theorem B1477235 : Blo 1211423 1477235 := bstep (se 1 (by rfl) ⟨1107926, by rfl⟩ : syracuseStep 1477235 = 2215853) B2215853
theorem B4090499 : Blo 1211423 4090499 := bstep (se 1 (by rfl) ⟨3067874, by rfl⟩ : syracuseStep 4090499 = 6135749) B6135749
theorem B4147843 : Blo 1211423 4147843 := bstep (se 1 (by rfl) ⟨3110882, by rfl⟩ : syracuseStep 4147843 = 6221765) B6221765
theorem B3451565 : Blo 1211423 3451565 := bstep (se 3 (by rfl) ⟨647168, by rfl⟩ : syracuseStep 3451565 = 1294337) B1294337
theorem B7768817 : Blo 1211423 7768817 := bstep (se 2 (by rfl) ⟨2913306, by rfl⟩ : syracuseStep 7768817 = 5826613) B5826613
theorem B4606733 : Blo 1211423 4606733 := bstep (se 3 (by rfl) ⟨863762, by rfl⟩ : syracuseStep 4606733 = 1727525) B1727525
theorem B3451747 : Blo 1211423 3451747 := bstep (se 1 (by rfl) ⟨2588810, by rfl⟩ : syracuseStep 3451747 = 5177621) B5177621
theorem B4090769 : Blo 1211423 4090769 := bstep (se 2 (by rfl) ⟨1534038, by rfl⟩ : syracuseStep 4090769 = 3068077) B3068077
theorem B1362883 : Blo 1211423 1362883 := bstep (se 1 (by rfl) ⟨1022162, by rfl⟩ : syracuseStep 1362883 = 2044325) B2044325
theorem B1363027 : Blo 1211423 1363027 := bstep (se 1 (by rfl) ⟨1022270, by rfl⟩ : syracuseStep 1363027 = 2044541) B2044541
theorem B1535107 : Blo 1211423 1535107 := bstep (se 1 (by rfl) ⟨1151330, by rfl⟩ : syracuseStep 1535107 = 2302661) B2302661
theorem B4369571 : Blo 1211423 4369571 := bstep (se 1 (by rfl) ⟨3277178, by rfl⟩ : syracuseStep 4369571 = 6554357) B6554357
theorem B5827747 : Blo 1211423 5827747 := bstep (se 1 (by rfl) ⟨4370810, by rfl⟩ : syracuseStep 5827747 = 8741621) B8741621
theorem B5180593 : Blo 1211423 5180593 := bstep (se 2 (by rfl) ⟨1942722, by rfl⟩ : syracuseStep 5180593 = 3885445) B3885445
theorem B1363171 : Blo 1211423 1363171 := bstep (se 1 (by rfl) ⟨1022378, by rfl⟩ : syracuseStep 1363171 = 2044757) B2044757
theorem B13102307 : Blo 1211423 13102307 := bstep (se 1 (by rfl) ⟨9826730, by rfl⟩ : syracuseStep 13102307 = 19653461) B19653461
theorem B1535203 : Blo 1211423 1535203 := bstep (se 1 (by rfl) ⟨1151402, by rfl⟩ : syracuseStep 1535203 = 2302805) B2302805
theorem B39349475 : Blo 1211423 39349475 := bstep (se 1 (by rfl) ⟨29512106, by rfl⟩ : syracuseStep 39349475 = 59024213) B59024213
theorem B3067217 : Blo 1211423 3067217 := bstep (se 2 (by rfl) ⟨1150206, by rfl⟩ : syracuseStep 3067217 = 2300413) B2300413
theorem B1363315 : Blo 1211423 1363315 := bstep (se 1 (by rfl) ⟨1022486, by rfl⟩ : syracuseStep 1363315 = 2044973) B2044973
theorem B3067267 : Blo 1211423 3067267 := bstep (se 1 (by rfl) ⟨2300450, by rfl⟩ : syracuseStep 3067267 = 4600901) B4600901
theorem B5533069 : Blo 1211423 5533069 := bstep (se 3 (by rfl) ⟨1037450, by rfl⟩ : syracuseStep 5533069 = 2074901) B2074901
theorem B3689891 : Blo 1211423 3689891 := bstep (se 1 (by rfl) ⟨2767418, by rfl⟩ : syracuseStep 3689891 = 5534837) B5534837
theorem B4091309 : Blo 1211423 4091309 := bstep (se 3 (by rfl) ⟨767120, by rfl⟩ : syracuseStep 4091309 = 1534241) B1534241
theorem B6139313 : Blo 1211423 6139313 := bstep (se 2 (by rfl) ⟨2302242, by rfl⟩ : syracuseStep 6139313 = 4604485) B4604485
theorem B4091363 : Blo 1211423 4091363 := bstep (se 1 (by rfl) ⟨3068522, by rfl⟩ : syracuseStep 4091363 = 6137045) B6137045
theorem B1363459 : Blo 1211423 1363459 := bstep (se 1 (by rfl) ⟨1022594, by rfl⟩ : syracuseStep 1363459 = 2045189) B2045189
theorem B3067409 : Blo 1211423 3067409 := bstep (se 2 (by rfl) ⟨1150278, by rfl⟩ : syracuseStep 3067409 = 2300557) B2300557
theorem B11062925 : Blo 1211423 11062925 := bstep (se 3 (by rfl) ⟨2074298, by rfl⟩ : syracuseStep 11062925 = 4148597) B4148597
theorem B1363603 : Blo 1211423 1363603 := bstep (se 1 (by rfl) ⟨1022702, by rfl⟩ : syracuseStep 1363603 = 2045405) B2045405
theorem B1535699 : Blo 1211423 1535699 := bstep (se 1 (by rfl) ⟨1151774, by rfl⟩ : syracuseStep 1535699 = 2303549) B2303549
theorem B4091633 : Blo 1211423 4091633 := bstep (se 2 (by rfl) ⟨1534362, by rfl⟩ : syracuseStep 4091633 = 3068725) B3068725
theorem B14741261 : Blo 1211423 14741261 := bstep (se 3 (by rfl) ⟨2763986, by rfl⟩ : syracuseStep 14741261 = 5527973) B5527973
theorem B1363747 : Blo 1211423 1363747 := bstep (se 1 (by rfl) ⟨1022810, by rfl⟩ : syracuseStep 1363747 = 2045621) B2045621
theorem B1969969 : Blo 1211423 1969969 := bstep (se 2 (by rfl) ⟨738738, by rfl⟩ : syracuseStep 1969969 = 1477477) B1477477
theorem B1363891 : Blo 1211423 1363891 := bstep (se 1 (by rfl) ⟨1022918, by rfl⟩ : syracuseStep 1363891 = 2045837) B2045837
theorem B10358725 : Blo 1211423 10358725 := bstep (se 4 (by rfl) ⟨971130, by rfl⟩ : syracuseStep 10358725 = 1942261) B1942261
theorem B7761869 : Blo 1211423 7761869 := bstep (se 3 (by rfl) ⟨1455350, by rfl⟩ : syracuseStep 7761869 = 2910701) B2910701
theorem B1364035 : Blo 1211423 1364035 := bstep (se 1 (by rfl) ⟨1023026, by rfl⟩ : syracuseStep 1364035 = 2046053) B2046053
theorem B7770275 : Blo 1211423 7770275 := bstep (se 1 (by rfl) ⟨5827706, by rfl⟩ : syracuseStep 7770275 = 11655413) B11655413
theorem B3453137 : Blo 1211423 3453137 := bstep (se 2 (by rfl) ⟨1294926, by rfl⟩ : syracuseStep 3453137 = 2589853) B2589853
theorem B1364179 : Blo 1211423 1364179 := bstep (se 1 (by rfl) ⟨1023134, by rfl⟩ : syracuseStep 1364179 = 2046269) B2046269
theorem B4092173 : Blo 1211423 4092173 := bstep (se 3 (by rfl) ⟨767282, by rfl⟩ : syracuseStep 4092173 = 1534565) B1534565
theorem B1577267 : Blo 1211423 1577267 := bstep (se 1 (by rfl) ⟨1182950, by rfl⟩ : syracuseStep 1577267 = 2365901) B2365901
theorem B4092227 : Blo 1211423 4092227 := bstep (se 1 (by rfl) ⟨3069170, by rfl⟩ : syracuseStep 4092227 = 6138341) B6138341
theorem B1364323 : Blo 1211423 1364323 := bstep (se 1 (by rfl) ⟨1023242, by rfl⟩ : syracuseStep 1364323 = 2046485) B2046485
theorem B2044291 : Blo 1211423 2044291 := bstep (se 1 (by rfl) ⟨1533218, by rfl⟩ : syracuseStep 2044291 = 3066437) B3066437
theorem B3068401 : Blo 1211423 3068401 := bstep (se 2 (by rfl) ⟨1150650, by rfl⟩ : syracuseStep 3068401 = 2301301) B2301301
theorem B1364467 : Blo 1211423 1364467 := bstep (se 1 (by rfl) ⟨1023350, by rfl⟩ : syracuseStep 1364467 = 2046701) B2046701
theorem B14750221 : Blo 1211423 14750221 := bstep (se 3 (by rfl) ⟨2765666, by rfl⟩ : syracuseStep 14750221 = 5531333) B5531333
theorem B2044433 : Blo 1211423 2044433 := bstep (se 2 (by rfl) ⟨766662, by rfl⟩ : syracuseStep 2044433 = 1533325) B1533325
theorem B4092497 : Blo 1211423 4092497 := bstep (se 2 (by rfl) ⟨1534686, by rfl⟩ : syracuseStep 4092497 = 3069373) B3069373
theorem B1364611 : Blo 1211423 1364611 := bstep (se 1 (by rfl) ⟨1023458, by rfl⟩ : syracuseStep 1364611 = 2046917) B2046917
theorem B2044561 : Blo 1211423 2044561 := bstep (se 2 (by rfl) ⟨766710, by rfl⟩ : syracuseStep 2044561 = 1533421) B1533421
theorem B2044595 : Blo 1211423 2044595 := bstep (se 1 (by rfl) ⟨1533446, by rfl⟩ : syracuseStep 2044595 = 3066893) B3066893
theorem B2765539 : Blo 1211423 2765539 := bstep (se 1 (by rfl) ⟨2074154, by rfl⟩ : syracuseStep 2765539 = 4148309) B4148309
theorem B3068675 : Blo 1211423 3068675 := bstep (se 1 (by rfl) ⟨2301506, by rfl⟩ : syracuseStep 3068675 = 4603013) B4603013
theorem B4150019 : Blo 1211423 4150019 := bstep (se 1 (by rfl) ⟨3112514, by rfl⟩ : syracuseStep 4150019 = 6225029) B6225029
theorem B1364755 : Blo 1211423 1364755 := bstep (se 1 (by rfl) ⟨1023566, by rfl⟩ : syracuseStep 1364755 = 2047133) B2047133
theorem B2044723 : Blo 1211423 2044723 := bstep (se 1 (by rfl) ⟨1533542, by rfl⟩ : syracuseStep 2044723 = 3067085) B3067085
theorem B6140771 : Blo 1211423 6140771 := bstep (se 1 (by rfl) ⟨4605578, by rfl⟩ : syracuseStep 6140771 = 9211157) B9211157
theorem B1364899 : Blo 1211423 1364899 := bstep (se 1 (by rfl) ⟨1023674, by rfl⟩ : syracuseStep 1364899 = 2047349) B2047349
theorem B2044865 : Blo 1211423 2044865 := bstep (se 2 (by rfl) ⟨766824, by rfl⟩ : syracuseStep 2044865 = 1533649) B1533649
theorem B3068867 : Blo 1211423 3068867 := bstep (se 1 (by rfl) ⟨2301650, by rfl⟩ : syracuseStep 3068867 = 4603301) B4603301
theorem B1725475 : Blo 1211423 1725475 := bstep (se 1 (by rfl) ⟨1294106, by rfl⟩ : syracuseStep 1725475 = 2588213) B2588213
theorem B1365043 : Blo 1211423 1365043 := bstep (se 1 (by rfl) ⟨1023782, by rfl⟩ : syracuseStep 1365043 = 2047565) B2047565
theorem B2044993 : Blo 1211423 2044993 := bstep (se 2 (by rfl) ⟨766872, by rfl⟩ : syracuseStep 2044993 = 1533745) B1533745
theorem B2045027 : Blo 1211423 2045027 := bstep (se 1 (by rfl) ⟨1533770, by rfl⟩ : syracuseStep 2045027 = 3067541) B3067541
theorem B4093037 : Blo 1211423 4093037 := bstep (se 3 (by rfl) ⟨767444, by rfl⟩ : syracuseStep 4093037 = 1534889) B1534889
theorem B4666481 : Blo 1211423 4666481 := bstep (se 2 (by rfl) ⟨1749930, by rfl⟩ : syracuseStep 4666481 = 3499861) B3499861
theorem B5829745 : Blo 1211423 5829745 := bstep (se 2 (by rfl) ⟨2186154, by rfl⟩ : syracuseStep 5829745 = 4372309) B4372309
theorem B3454093 : Blo 1211423 3454093 := bstep (se 3 (by rfl) ⟨647642, by rfl⟩ : syracuseStep 3454093 = 1295285) B1295285
theorem B4093091 : Blo 1211423 4093091 := bstep (se 1 (by rfl) ⟨3069818, by rfl⟩ : syracuseStep 4093091 = 6139637) B6139637
theorem B2045155 : Blo 1211423 2045155 := bstep (se 1 (by rfl) ⟨1533866, by rfl⟩ : syracuseStep 2045155 = 3067733) B3067733
theorem B1774867 : Blo 1211423 1774867 := bstep (se 1 (by rfl) ⟨1331150, by rfl⟩ : syracuseStep 1774867 = 2662301) B2662301
theorem B2045297 : Blo 1211423 2045297 := bstep (se 2 (by rfl) ⟨766986, by rfl⟩ : syracuseStep 2045297 = 1533973) B1533973
theorem B3454321 : Blo 1211423 3454321 := bstep (se 2 (by rfl) ⟨1295370, by rfl⟩ : syracuseStep 3454321 = 2590741) B2590741
theorem B4093361 : Blo 1211423 4093361 := bstep (se 2 (by rfl) ⟨1535010, by rfl⟩ : syracuseStep 4093361 = 3070021) B3070021
theorem B2045425 : Blo 1211423 2045425 := bstep (se 2 (by rfl) ⟨767034, by rfl⟩ : syracuseStep 2045425 = 1534069) B1534069
theorem B1725953 : Blo 1211423 1725953 := bstep (se 2 (by rfl) ⟨647232, by rfl⟩ : syracuseStep 1725953 = 1294465) B1294465
theorem B4601357 : Blo 1211423 4601357 := bstep (se 3 (by rfl) ⟨862754, by rfl⟩ : syracuseStep 4601357 = 1725509) B1725509
theorem B3454481 : Blo 1211423 3454481 := bstep (se 2 (by rfl) ⟨1295430, by rfl⟩ : syracuseStep 3454481 = 2590861) B2590861
theorem B2045459 : Blo 1211423 2045459 := bstep (se 1 (by rfl) ⟨1534094, by rfl⟩ : syracuseStep 2045459 = 3068189) B3068189
theorem B1726067 : Blo 1211423 1726067 := bstep (se 1 (by rfl) ⟨1294550, by rfl⟩ : syracuseStep 1726067 = 2589101) B2589101
theorem B3454595 : Blo 1211423 3454595 := bstep (se 1 (by rfl) ⟨2590946, by rfl⟩ : syracuseStep 3454595 = 5181893) B5181893
theorem B6141581 : Blo 1211423 6141581 := bstep (se 3 (by rfl) ⟨1151546, by rfl⟩ : syracuseStep 6141581 = 2303093) B2303093
theorem B2045587 : Blo 1211423 2045587 := bstep (se 1 (by rfl) ⟨1534190, by rfl⟩ : syracuseStep 2045587 = 3068381) B3068381
theorem B1726147 : Blo 1211423 1726147 := bstep (se 1 (by rfl) ⟨1294610, by rfl⟩ : syracuseStep 1726147 = 2589221) B2589221
theorem B2045729 : Blo 1211423 2045729 := bstep (se 2 (by rfl) ⟨767148, by rfl⟩ : syracuseStep 2045729 = 1534297) B1534297
theorem B3069809 : Blo 1211423 3069809 := bstep (se 2 (by rfl) ⟨1151178, by rfl⟩ : syracuseStep 3069809 = 2302357) B2302357
theorem B4372337 : Blo 1211423 4372337 := bstep (se 2 (by rfl) ⟨1639626, by rfl⟩ : syracuseStep 4372337 = 3279253) B3279253
theorem B3274627 : Blo 1211423 3274627 := bstep (se 1 (by rfl) ⟨2455970, by rfl⟩ : syracuseStep 3274627 = 4911941) B4911941
theorem B2045857 : Blo 1211423 2045857 := bstep (se 2 (by rfl) ⟨767196, by rfl⟩ : syracuseStep 2045857 = 1534393) B1534393
theorem B3069859 : Blo 1211423 3069859 := bstep (se 1 (by rfl) ⟨2302394, by rfl⟩ : syracuseStep 3069859 = 4604789) B4604789
theorem B2299843 : Blo 1211423 2299843 := bstep (se 1 (by rfl) ⟨1724882, by rfl⟩ : syracuseStep 2299843 = 3449765) B3449765
theorem B2045891 : Blo 1211423 2045891 := bstep (se 1 (by rfl) ⟨1534418, by rfl⟩ : syracuseStep 2045891 = 3068837) B3068837
theorem B4093901 : Blo 1211423 4093901 := bstep (se 3 (by rfl) ⟨767606, by rfl⟩ : syracuseStep 4093901 = 1535213) B1535213
theorem B2299889 : Blo 1211423 2299889 := bstep (se 2 (by rfl) ⟨862458, by rfl⟩ : syracuseStep 2299889 = 1724917) B1724917
theorem B1456115 : Blo 1211423 1456115 := bstep (se 1 (by rfl) ⟨1092086, by rfl⟩ : syracuseStep 1456115 = 2184173) B2184173
theorem B4093955 : Blo 1211423 4093955 := bstep (se 1 (by rfl) ⟨3070466, by rfl⟩ : syracuseStep 4093955 = 6140933) B6140933
theorem B2725937 : Blo 1211423 2725937 := bstep (se 2 (by rfl) ⟨1022226, by rfl⟩ : syracuseStep 2725937 = 2044453) B2044453
theorem B3070001 : Blo 1211423 3070001 := bstep (se 2 (by rfl) ⟨1151250, by rfl⟩ : syracuseStep 3070001 = 2302501) B2302501
theorem B2725955 : Blo 1211423 2725955 := bstep (se 1 (by rfl) ⟨2044466, by rfl⟩ : syracuseStep 2725955 = 4088933) B4088933
theorem B2046019 : Blo 1211423 2046019 := bstep (se 1 (by rfl) ⟨1534514, by rfl⟩ : syracuseStep 2046019 = 3069029) B3069029
theorem B6993989 : Blo 1211423 6993989 := bstep (se 4 (by rfl) ⟨655686, by rfl⟩ : syracuseStep 6993989 = 1311373) B1311373
theorem B2046161 : Blo 1211423 2046161 := bstep (se 2 (by rfl) ⟨767310, by rfl⟩ : syracuseStep 2046161 = 1534621) B1534621
theorem B1726705 : Blo 1211423 1726705 := bstep (se 2 (by rfl) ⟨647514, by rfl⟩ : syracuseStep 1726705 = 1295029) B1295029
theorem B13105421 : Blo 1211423 13105421 := bstep (se 3 (by rfl) ⟨2457266, by rfl⟩ : syracuseStep 13105421 = 4914533) B4914533
theorem B2300177 : Blo 1211423 2300177 := bstep (se 2 (by rfl) ⟨862566, by rfl⟩ : syracuseStep 2300177 = 1725133) B1725133
theorem B4094225 : Blo 1211423 4094225 := bstep (se 2 (by rfl) ⟨1535334, by rfl⟩ : syracuseStep 4094225 = 3070669) B3070669
theorem B3684685 : Blo 1211423 3684685 := bstep (se 3 (by rfl) ⟨690878, by rfl⟩ : syracuseStep 3684685 = 1381757) B1381757
theorem B2726225 : Blo 1211423 2726225 := bstep (se 2 (by rfl) ⟨1022334, by rfl⟩ : syracuseStep 2726225 = 2044669) B2044669
theorem B2046289 : Blo 1211423 2046289 := bstep (se 2 (by rfl) ⟨767358, by rfl⟩ : syracuseStep 2046289 = 1534717) B1534717
theorem B2726243 : Blo 1211423 2726243 := bstep (se 1 (by rfl) ⟨2044682, by rfl⟩ : syracuseStep 2726243 = 4089365) B4089365
theorem B3938669 : Blo 1211423 3938669 := bstep (se 3 (by rfl) ⟨738500, by rfl⟩ : syracuseStep 3938669 = 1477001) B1477001
theorem B23607665 : Blo 1211423 23607665 := bstep (se 2 (by rfl) ⟨8852874, by rfl⟩ : syracuseStep 23607665 = 17705749) B17705749
theorem B6134129 : Blo 1211423 6134129 := bstep (se 2 (by rfl) ⟨2300298, by rfl⟩ : syracuseStep 6134129 = 4600597) B4600597
theorem B2046323 : Blo 1211423 2046323 := bstep (se 1 (by rfl) ⟨1534742, by rfl⟩ : syracuseStep 2046323 = 3069485) B3069485
theorem B4430285 : Blo 1211423 4430285 := bstep (se 3 (by rfl) ⟨830678, by rfl⟩ : syracuseStep 4430285 = 1661357) B1661357
theorem B26212835 : Blo 1211423 26212835 := bstep (se 1 (by rfl) ⟨19659626, by rfl⟩ : syracuseStep 26212835 = 39319253) B39319253
theorem B2046451 : Blo 1211423 2046451 := bstep (se 1 (by rfl) ⟨1534838, by rfl⟩ : syracuseStep 2046451 = 3069677) B3069677
theorem B7371269 : Blo 1211423 7371269 := bstep (se 4 (by rfl) ⟨691056, by rfl⟩ : syracuseStep 7371269 = 1382113) B1382113
theorem B2456099 : Blo 1211423 2456099 := bstep (se 1 (by rfl) ⟨1842074, by rfl⟩ : syracuseStep 2456099 = 3684149) B3684149
theorem B1817153 : Blo 1211423 1817153 := bstep (se 2 (by rfl) ⟨681432, by rfl⟩ : syracuseStep 1817153 = 1362865) B1362865
theorem B1817171 : Blo 1211423 1817171 := bstep (se 1 (by rfl) ⟨1362878, by rfl⟩ : syracuseStep 1817171 = 2725757) B2725757
theorem B1817201 : Blo 1211423 1817201 := bstep (se 2 (by rfl) ⟨681450, by rfl⟩ : syracuseStep 1817201 = 1362901) B1362901
theorem B2726513 : Blo 1211423 2726513 := bstep (se 2 (by rfl) ⟨1022442, by rfl⟩ : syracuseStep 2726513 = 2044885) B2044885
theorem B2046593 : Blo 1211423 2046593 := bstep (se 2 (by rfl) ⟨767472, by rfl⟩ : syracuseStep 2046593 = 1534945) B1534945
theorem B1817219 : Blo 1211423 1817219 := bstep (se 1 (by rfl) ⟨1362914, by rfl⟩ : syracuseStep 1817219 = 2725829) B2725829
theorem B2726531 : Blo 1211423 2726531 := bstep (se 1 (by rfl) ⟨2044898, by rfl⟩ : syracuseStep 2726531 = 4089797) B4089797
theorem B1817249 : Blo 1211423 1817249 := bstep (se 2 (by rfl) ⟨681468, by rfl⟩ : syracuseStep 1817249 = 1362937) B1362937
theorem B1817267 : Blo 1211423 1817267 := bstep (se 1 (by rfl) ⟨1362950, by rfl⟩ : syracuseStep 1817267 = 2725901) B2725901
theorem B1817297 : Blo 1211423 1817297 := bstep (se 2 (by rfl) ⟨681486, by rfl⟩ : syracuseStep 1817297 = 1362973) B1362973
theorem B1817315 : Blo 1211423 1817315 := bstep (se 1 (by rfl) ⟨1362986, by rfl⟩ : syracuseStep 1817315 = 2725973) B2725973
theorem B3275491 : Blo 1211423 3275491 := bstep (se 1 (by rfl) ⟨2456618, by rfl⟩ : syracuseStep 3275491 = 4913237) B4913237
theorem B1817345 : Blo 1211423 1817345 := bstep (se 2 (by rfl) ⟨681504, by rfl⟩ : syracuseStep 1817345 = 1363009) B1363009
theorem B2046721 : Blo 1211423 2046721 := bstep (se 2 (by rfl) ⟨767520, by rfl⟩ : syracuseStep 2046721 = 1535041) B1535041
theorem B4373261 : Blo 1211423 4373261 := bstep (se 3 (by rfl) ⟨819986, by rfl⟩ : syracuseStep 4373261 = 1639973) B1639973
theorem B1817363 : Blo 1211423 1817363 := bstep (se 1 (by rfl) ⟨1363022, by rfl⟩ : syracuseStep 1817363 = 2726045) B2726045
theorem B2046755 : Blo 1211423 2046755 := bstep (se 1 (by rfl) ⟨1535066, by rfl⟩ : syracuseStep 2046755 = 3070133) B3070133
theorem B4094765 : Blo 1211423 4094765 := bstep (se 3 (by rfl) ⟨767768, by rfl⟩ : syracuseStep 4094765 = 1535537) B1535537
theorem B1817393 : Blo 1211423 1817393 := bstep (se 2 (by rfl) ⟨681522, by rfl⟩ : syracuseStep 1817393 = 1363045) B1363045
theorem B1817411 : Blo 1211423 1817411 := bstep (se 1 (by rfl) ⟨1363058, by rfl⟩ : syracuseStep 1817411 = 2726117) B2726117
theorem B2915153 : Blo 1211423 2915153 := bstep (se 2 (by rfl) ⟨1093182, by rfl⟩ : syracuseStep 2915153 = 2186365) B2186365
theorem B1817441 : Blo 1211423 1817441 := bstep (se 2 (by rfl) ⟨681540, by rfl⟩ : syracuseStep 1817441 = 1363081) B1363081
theorem B4094819 : Blo 1211423 4094819 := bstep (se 1 (by rfl) ⟨3071114, by rfl⟩ : syracuseStep 4094819 = 6142229) B6142229
theorem B1817459 : Blo 1211423 1817459 := bstep (se 1 (by rfl) ⟨1363094, by rfl⟩ : syracuseStep 1817459 = 2726189) B2726189
theorem B1817489 : Blo 1211423 1817489 := bstep (se 2 (by rfl) ⟨681558, by rfl⟩ : syracuseStep 1817489 = 1363117) B1363117
theorem B2726801 : Blo 1211423 2726801 := bstep (se 2 (by rfl) ⟨1022550, by rfl⟩ : syracuseStep 2726801 = 2045101) B2045101
theorem B2587555 : Blo 1211423 2587555 := bstep (se 1 (by rfl) ⟨1940666, by rfl⟩ : syracuseStep 2587555 = 3881333) B3881333
theorem B1817507 : Blo 1211423 1817507 := bstep (se 1 (by rfl) ⟨1363130, by rfl⟩ : syracuseStep 1817507 = 2726261) B2726261
theorem B2726819 : Blo 1211423 2726819 := bstep (se 1 (by rfl) ⟨2045114, by rfl⟩ : syracuseStep 2726819 = 4090229) B4090229
theorem B2046883 : Blo 1211423 2046883 := bstep (se 1 (by rfl) ⟨1535162, by rfl⟩ : syracuseStep 2046883 = 3070325) B3070325
theorem B1727411 : Blo 1211423 1727411 := bstep (se 1 (by rfl) ⟨1295558, by rfl⟩ : syracuseStep 1727411 = 2591117) B2591117
theorem B1817537 : Blo 1211423 1817537 := bstep (se 2 (by rfl) ⟨681576, by rfl⟩ : syracuseStep 1817537 = 1363153) B1363153
theorem B1817555 : Blo 1211423 1817555 := bstep (se 1 (by rfl) ⟨1363166, by rfl⟩ : syracuseStep 1817555 = 2726333) B2726333
theorem B2300899 : Blo 1211423 2300899 := bstep (se 1 (by rfl) ⟨1725674, by rfl⟩ : syracuseStep 2300899 = 3451349) B3451349
theorem B12434417 : Blo 1211423 12434417 := bstep (se 2 (by rfl) ⟨4662906, by rfl⟩ : syracuseStep 12434417 = 9325813) B9325813
theorem B1817585 : Blo 1211423 1817585 := bstep (se 2 (by rfl) ⟨681594, by rfl⟩ : syracuseStep 1817585 = 1363189) B1363189
theorem B1817603 : Blo 1211423 1817603 := bstep (se 1 (by rfl) ⟨1363202, by rfl⟩ : syracuseStep 1817603 = 2726405) B2726405
theorem B3070993 : Blo 1211423 3070993 := bstep (se 2 (by rfl) ⟨1151622, by rfl⟩ : syracuseStep 3070993 = 2303245) B2303245
theorem B1817633 : Blo 1211423 1817633 := bstep (se 2 (by rfl) ⟨681612, by rfl⟩ : syracuseStep 1817633 = 1363225) B1363225
theorem B1211427 : Blo 1211423 1211427 := bstep (se 1 (by rfl) ⟨908570, by rfl⟩ : syracuseStep 1211427 = 1817141) B1817141
theorem B2047025 : Blo 1211423 2047025 := bstep (se 2 (by rfl) ⟨767634, by rfl⟩ : syracuseStep 2047025 = 1535269) B1535269
theorem B1211443 : Blo 1211423 1211443 := bstep (se 1 (by rfl) ⟨908582, by rfl⟩ : syracuseStep 1211443 = 1817165) B1817165
theorem B1817651 : Blo 1211423 1817651 := bstep (se 1 (by rfl) ⟨1363238, by rfl⟩ : syracuseStep 1817651 = 2726477) B2726477
theorem B1211459 : Blo 1211423 1211459 := bstep (se 1 (by rfl) ⟨908594, by rfl⟩ : syracuseStep 1211459 = 1817189) B1817189
theorem B1817681 : Blo 1211423 1817681 := bstep (se 2 (by rfl) ⟨681630, by rfl⟩ : syracuseStep 1817681 = 1363261) B1363261
theorem B1211475 : Blo 1211423 1211475 := bstep (se 1 (by rfl) ⟨908606, by rfl⟩ : syracuseStep 1211475 = 1817213) B1817213
theorem B1211491 : Blo 1211423 1211491 := bstep (se 1 (by rfl) ⟨908618, by rfl⟩ : syracuseStep 1211491 = 1817237) B1817237
theorem B1817699 : Blo 1211423 1817699 := bstep (se 1 (by rfl) ⟨1363274, by rfl⟩ : syracuseStep 1817699 = 2726549) B2726549
theorem B4095089 : Blo 1211423 4095089 := bstep (se 2 (by rfl) ⟨1535658, by rfl⟩ : syracuseStep 4095089 = 3071317) B3071317
theorem B1211507 : Blo 1211423 1211507 := bstep (se 1 (by rfl) ⟨908630, by rfl⟩ : syracuseStep 1211507 = 1817261) B1817261
theorem B1817729 : Blo 1211423 1817729 := bstep (se 2 (by rfl) ⟨681648, by rfl⟩ : syracuseStep 1817729 = 1363297) B1363297
theorem B1211523 : Blo 1211423 1211523 := bstep (se 1 (by rfl) ⟨908642, by rfl⟩ : syracuseStep 1211523 = 1817285) B1817285
theorem B1211539 : Blo 1211423 1211539 := bstep (se 1 (by rfl) ⟨908654, by rfl⟩ : syracuseStep 1211539 = 1817309) B1817309
theorem B1817747 : Blo 1211423 1817747 := bstep (se 1 (by rfl) ⟨1363310, by rfl⟩ : syracuseStep 1817747 = 2726621) B2726621
theorem B1211555 : Blo 1211423 1211555 := bstep (se 1 (by rfl) ⟨908666, by rfl⟩ : syracuseStep 1211555 = 1817333) B1817333
theorem B1817777 : Blo 1211423 1817777 := bstep (se 2 (by rfl) ⟨681666, by rfl⟩ : syracuseStep 1817777 = 1363333) B1363333
theorem B2727089 : Blo 1211423 2727089 := bstep (se 2 (by rfl) ⟨1022658, by rfl⟩ : syracuseStep 2727089 = 2045317) B2045317
theorem B1211571 : Blo 1211423 1211571 := bstep (se 1 (by rfl) ⟨908678, by rfl⟩ : syracuseStep 1211571 = 1817357) B1817357
theorem B2047153 : Blo 1211423 2047153 := bstep (se 2 (by rfl) ⟨767682, by rfl⟩ : syracuseStep 2047153 = 1535365) B1535365
theorem B1211587 : Blo 1211423 1211587 := bstep (se 1 (by rfl) ⟨908690, by rfl⟩ : syracuseStep 1211587 = 1817381) B1817381
theorem B1817795 : Blo 1211423 1817795 := bstep (se 1 (by rfl) ⟨1363346, by rfl⟩ : syracuseStep 1817795 = 2726693) B2726693
theorem B2727107 : Blo 1211423 2727107 := bstep (se 1 (by rfl) ⟨2045330, by rfl⟩ : syracuseStep 2727107 = 4090661) B4090661
theorem B1211603 : Blo 1211423 1211603 := bstep (se 1 (by rfl) ⟨908702, by rfl⟩ : syracuseStep 1211603 = 1817405) B1817405
theorem B2047187 : Blo 1211423 2047187 := bstep (se 1 (by rfl) ⟨1535390, by rfl⟩ : syracuseStep 2047187 = 3070781) B3070781
theorem B1817825 : Blo 1211423 1817825 := bstep (se 2 (by rfl) ⟨681684, by rfl⟩ : syracuseStep 1817825 = 1363369) B1363369
theorem B1211619 : Blo 1211423 1211619 := bstep (se 1 (by rfl) ⟨908714, by rfl⟩ : syracuseStep 1211619 = 1817429) B1817429
theorem B5176561 : Blo 1211423 5176561 := bstep (se 2 (by rfl) ⟨1941210, by rfl⟩ : syracuseStep 5176561 = 3882421) B3882421
theorem B1211635 : Blo 1211423 1211635 := bstep (se 1 (by rfl) ⟨908726, by rfl⟩ : syracuseStep 1211635 = 1817453) B1817453
theorem B1817843 : Blo 1211423 1817843 := bstep (se 1 (by rfl) ⟨1363382, by rfl⟩ : syracuseStep 1817843 = 2726765) B2726765
theorem B1211651 : Blo 1211423 1211651 := bstep (se 1 (by rfl) ⟨908738, by rfl⟩ : syracuseStep 1211651 = 1817477) B1817477
theorem B7765253 : Blo 1211423 7765253 := bstep (se 4 (by rfl) ⟨727992, by rfl⟩ : syracuseStep 7765253 = 1455985) B1455985
theorem B1817873 : Blo 1211423 1817873 := bstep (se 2 (by rfl) ⟨681702, by rfl⟩ : syracuseStep 1817873 = 1363405) B1363405
theorem B1211667 : Blo 1211423 1211667 := bstep (se 1 (by rfl) ⟨908750, by rfl⟩ : syracuseStep 1211667 = 1817501) B1817501
theorem B1211683 : Blo 1211423 1211683 := bstep (se 1 (by rfl) ⟨908762, by rfl⟩ : syracuseStep 1211683 = 1817525) B1817525
theorem B1817891 : Blo 1211423 1817891 := bstep (se 1 (by rfl) ⟨1363418, by rfl⟩ : syracuseStep 1817891 = 2726837) B2726837
theorem B3071267 : Blo 1211423 3071267 := bstep (se 1 (by rfl) ⟨2303450, by rfl⟩ : syracuseStep 3071267 = 4606901) B4606901
theorem B1211699 : Blo 1211423 1211699 := bstep (se 1 (by rfl) ⟨908774, by rfl⟩ : syracuseStep 1211699 = 1817549) B1817549
theorem B1817921 : Blo 1211423 1817921 := bstep (se 2 (by rfl) ⟨681720, by rfl⟩ : syracuseStep 1817921 = 1363441) B1363441
theorem B1211715 : Blo 1211423 1211715 := bstep (se 1 (by rfl) ⟨908786, by rfl⟩ : syracuseStep 1211715 = 1817573) B1817573
theorem B15539525 : Blo 1211423 15539525 := bstep (se 4 (by rfl) ⟨1456830, by rfl⟩ : syracuseStep 15539525 = 2913661) B2913661
theorem B1637713 : Blo 1211423 1637713 := bstep (se 2 (by rfl) ⟨614142, by rfl⟩ : syracuseStep 1637713 = 1228285) B1228285
theorem B1211731 : Blo 1211423 1211731 := bstep (se 1 (by rfl) ⟨908798, by rfl⟩ : syracuseStep 1211731 = 1817597) B1817597
theorem B1817939 : Blo 1211423 1817939 := bstep (se 1 (by rfl) ⟨1363454, by rfl⟩ : syracuseStep 1817939 = 2726909) B2726909
theorem B2047315 : Blo 1211423 2047315 := bstep (se 1 (by rfl) ⟨1535486, by rfl⟩ : syracuseStep 2047315 = 3070973) B3070973
theorem B1211747 : Blo 1211423 1211747 := bstep (se 1 (by rfl) ⟨908810, by rfl⟩ : syracuseStep 1211747 = 1817621) B1817621
theorem B1817969 : Blo 1211423 1817969 := bstep (se 2 (by rfl) ⟨681738, by rfl⟩ : syracuseStep 1817969 = 1363477) B1363477
theorem B1211763 : Blo 1211423 1211763 := bstep (se 1 (by rfl) ⟨908822, by rfl⟩ : syracuseStep 1211763 = 1817645) B1817645
theorem B1228163 : Blo 1211423 1228163 := bstep (se 1 (by rfl) ⟨921122, by rfl⟩ : syracuseStep 1228163 = 1842245) B1842245
theorem B1211779 : Blo 1211423 1211779 := bstep (se 1 (by rfl) ⟨908834, by rfl⟩ : syracuseStep 1211779 = 1817669) B1817669
theorem B1817987 : Blo 1211423 1817987 := bstep (se 1 (by rfl) ⟨1363490, by rfl⟩ : syracuseStep 1817987 = 2726981) B2726981
theorem B9330061 : Blo 1211423 9330061 := bstep (se 3 (by rfl) ⟨1749386, by rfl⟩ : syracuseStep 9330061 = 3498773) B3498773
theorem B1211795 : Blo 1211423 1211795 := bstep (se 1 (by rfl) ⟨908846, by rfl⟩ : syracuseStep 1211795 = 1817693) B1817693
theorem B1818017 : Blo 1211423 1818017 := bstep (se 2 (by rfl) ⟨681756, by rfl⟩ : syracuseStep 1818017 = 1363513) B1363513
theorem B1211811 : Blo 1211423 1211811 := bstep (se 1 (by rfl) ⟨908858, by rfl⟩ : syracuseStep 1211811 = 1817717) B1817717
theorem B2301347 : Blo 1211423 2301347 := bstep (se 1 (by rfl) ⟨1726010, by rfl⟩ : syracuseStep 2301347 = 3452021) B3452021
theorem B1211827 : Blo 1211423 1211827 := bstep (se 1 (by rfl) ⟨908870, by rfl⟩ : syracuseStep 1211827 = 1817741) B1817741
theorem B1818035 : Blo 1211423 1818035 := bstep (se 1 (by rfl) ⟨1363526, by rfl⟩ : syracuseStep 1818035 = 2727053) B2727053
theorem B1211843 : Blo 1211423 1211843 := bstep (se 1 (by rfl) ⟨908882, by rfl⟩ : syracuseStep 1211843 = 1817765) B1817765
theorem B6217165 : Blo 1211423 6217165 := bstep (se 3 (by rfl) ⟨1165718, by rfl⟩ : syracuseStep 6217165 = 2331437) B2331437
theorem B1818065 : Blo 1211423 1818065 := bstep (se 2 (by rfl) ⟨681774, by rfl⟩ : syracuseStep 1818065 = 1363549) B1363549
theorem B2727377 : Blo 1211423 2727377 := bstep (se 2 (by rfl) ⟨1022766, by rfl⟩ : syracuseStep 2727377 = 2045533) B2045533
theorem B1211859 : Blo 1211423 1211859 := bstep (se 1 (by rfl) ⟨908894, by rfl⟩ : syracuseStep 1211859 = 1817789) B1817789
theorem B2047457 : Blo 1211423 2047457 := bstep (se 2 (by rfl) ⟨767796, by rfl⟩ : syracuseStep 2047457 = 1535593) B1535593
theorem B1211875 : Blo 1211423 1211875 := bstep (se 1 (by rfl) ⟨908906, by rfl⟩ : syracuseStep 1211875 = 1817813) B1817813
theorem B1818083 : Blo 1211423 1818083 := bstep (se 1 (by rfl) ⟨1363562, by rfl⟩ : syracuseStep 1818083 = 2727125) B2727125
theorem B2727395 : Blo 1211423 2727395 := bstep (se 1 (by rfl) ⟨2045546, by rfl⟩ : syracuseStep 2727395 = 4091093) B4091093
theorem B2334179 : Blo 1211423 2334179 := bstep (se 1 (by rfl) ⟨1750634, by rfl⟩ : syracuseStep 2334179 = 3501269) B3501269
theorem B3071459 : Blo 1211423 3071459 := bstep (se 1 (by rfl) ⟨2303594, by rfl⟩ : syracuseStep 3071459 = 4607189) B4607189
theorem B3276269 : Blo 1211423 3276269 := bstep (se 3 (by rfl) ⟨614300, by rfl⟩ : syracuseStep 3276269 = 1228601) B1228601
theorem B1211891 : Blo 1211423 1211891 := bstep (se 1 (by rfl) ⟨908918, by rfl⟩ : syracuseStep 1211891 = 1817837) B1817837
theorem B1818113 : Blo 1211423 1818113 := bstep (se 2 (by rfl) ⟨681792, by rfl⟩ : syracuseStep 1818113 = 1363585) B1363585
theorem B1211907 : Blo 1211423 1211907 := bstep (se 1 (by rfl) ⟨908930, by rfl⟩ : syracuseStep 1211907 = 1817861) B1817861
theorem B1211923 : Blo 1211423 1211923 := bstep (se 1 (by rfl) ⟨908942, by rfl⟩ : syracuseStep 1211923 = 1817885) B1817885
theorem B1842707 : Blo 1211423 1842707 := bstep (se 1 (by rfl) ⟨1382030, by rfl⟩ : syracuseStep 1842707 = 2764061) B2764061
theorem B1818131 : Blo 1211423 1818131 := bstep (se 1 (by rfl) ⟨1363598, by rfl⟩ : syracuseStep 1818131 = 2727197) B2727197
theorem B1211939 : Blo 1211423 1211939 := bstep (se 1 (by rfl) ⟨908954, by rfl⟩ : syracuseStep 1211939 = 1817909) B1817909
theorem B1818161 : Blo 1211423 1818161 := bstep (se 2 (by rfl) ⟨681810, by rfl⟩ : syracuseStep 1818161 = 1363621) B1363621
theorem B1211955 : Blo 1211423 1211955 := bstep (se 1 (by rfl) ⟨908966, by rfl⟩ : syracuseStep 1211955 = 1817933) B1817933
theorem B3882563 : Blo 1211423 3882563 := bstep (se 1 (by rfl) ⟨2911922, by rfl⟩ : syracuseStep 3882563 = 5823845) B5823845
theorem B1211971 : Blo 1211423 1211971 := bstep (se 1 (by rfl) ⟨908978, by rfl⟩ : syracuseStep 1211971 = 1817957) B1817957
theorem B1818179 : Blo 1211423 1818179 := bstep (se 1 (by rfl) ⟨1363634, by rfl⟩ : syracuseStep 1818179 = 2727269) B2727269
theorem B1211987 : Blo 1211423 1211987 := bstep (se 1 (by rfl) ⟨908990, by rfl⟩ : syracuseStep 1211987 = 1817981) B1817981
theorem B1818209 : Blo 1211423 1818209 := bstep (se 2 (by rfl) ⟨681828, by rfl⟩ : syracuseStep 1818209 = 1363657) B1363657
theorem B1212003 : Blo 1211423 1212003 := bstep (se 1 (by rfl) ⟨909002, by rfl⟩ : syracuseStep 1212003 = 1818005) B1818005
theorem B2047585 : Blo 1211423 2047585 := bstep (se 2 (by rfl) ⟨767844, by rfl⟩ : syracuseStep 2047585 = 1535689) B1535689
theorem B1212019 : Blo 1211423 1212019 := bstep (se 1 (by rfl) ⟨909014, by rfl⟩ : syracuseStep 1212019 = 1818029) B1818029
theorem B1818227 : Blo 1211423 1818227 := bstep (se 1 (by rfl) ⟨1363670, by rfl⟩ : syracuseStep 1818227 = 2727341) B2727341
theorem B1212035 : Blo 1211423 1212035 := bstep (se 1 (by rfl) ⟨909026, by rfl⟩ : syracuseStep 1212035 = 1818053) B1818053
theorem B2047619 : Blo 1211423 2047619 := bstep (se 1 (by rfl) ⟨1535714, by rfl⟩ : syracuseStep 2047619 = 3071429) B3071429
theorem B1818257 : Blo 1211423 1818257 := bstep (se 2 (by rfl) ⟨681846, by rfl⟩ : syracuseStep 1818257 = 1363693) B1363693
theorem B1212051 : Blo 1211423 1212051 := bstep (se 1 (by rfl) ⟨909038, by rfl⟩ : syracuseStep 1212051 = 1818077) B1818077
theorem B1212067 : Blo 1211423 1212067 := bstep (se 1 (by rfl) ⟨909050, by rfl⟩ : syracuseStep 1212067 = 1818101) B1818101
theorem B1818275 : Blo 1211423 1818275 := bstep (se 1 (by rfl) ⟨1363706, by rfl⟩ : syracuseStep 1818275 = 2727413) B2727413
theorem B1212083 : Blo 1211423 1212083 := bstep (se 1 (by rfl) ⟨909062, by rfl⟩ : syracuseStep 1212083 = 1818125) B1818125
theorem B1941185 : Blo 1211423 1941185 := bstep (se 2 (by rfl) ⟨727944, by rfl⟩ : syracuseStep 1941185 = 1455889) B1455889
theorem B1818305 : Blo 1211423 1818305 := bstep (se 2 (by rfl) ⟨681864, by rfl⟩ : syracuseStep 1818305 = 1363729) B1363729
theorem B1212099 : Blo 1211423 1212099 := bstep (se 1 (by rfl) ⟨909074, by rfl⟩ : syracuseStep 1212099 = 1818149) B1818149
theorem B2301635 : Blo 1211423 2301635 := bstep (se 1 (by rfl) ⟨1726226, by rfl⟩ : syracuseStep 2301635 = 3452453) B3452453
theorem B1212115 : Blo 1211423 1212115 := bstep (se 1 (by rfl) ⟨909086, by rfl⟩ : syracuseStep 1212115 = 1818173) B1818173
theorem B1818323 : Blo 1211423 1818323 := bstep (se 1 (by rfl) ⟨1363742, by rfl⟩ : syracuseStep 1818323 = 2727485) B2727485
theorem B1294051 : Blo 1211423 1294051 := bstep (se 1 (by rfl) ⟨970538, by rfl⟩ : syracuseStep 1294051 = 1941077) B1941077
theorem B1212131 : Blo 1211423 1212131 := bstep (se 1 (by rfl) ⟨909098, by rfl⟩ : syracuseStep 1212131 = 1818197) B1818197
theorem B1818353 : Blo 1211423 1818353 := bstep (se 2 (by rfl) ⟨681882, by rfl⟩ : syracuseStep 1818353 = 1363765) B1363765
theorem B2727665 : Blo 1211423 2727665 := bstep (se 2 (by rfl) ⟨1022874, by rfl⟩ : syracuseStep 2727665 = 2045749) B2045749
theorem B1212147 : Blo 1211423 1212147 := bstep (se 1 (by rfl) ⟨909110, by rfl⟩ : syracuseStep 1212147 = 1818221) B1818221
theorem B1212163 : Blo 1211423 1212163 := bstep (se 1 (by rfl) ⟨909122, by rfl⟩ : syracuseStep 1212163 = 1818245) B1818245
theorem B1818371 : Blo 1211423 1818371 := bstep (se 1 (by rfl) ⟨1363778, by rfl⟩ : syracuseStep 1818371 = 2727557) B2727557
theorem B2727683 : Blo 1211423 2727683 := bstep (se 1 (by rfl) ⟨2045762, by rfl⟩ : syracuseStep 2727683 = 4091525) B4091525
theorem B7773965 : Blo 1211423 7773965 := bstep (se 3 (by rfl) ⟨1457618, by rfl⟩ : syracuseStep 7773965 = 2915237) B2915237
theorem B1212179 : Blo 1211423 1212179 := bstep (se 1 (by rfl) ⟨909134, by rfl⟩ : syracuseStep 1212179 = 1818269) B1818269
theorem B1818401 : Blo 1211423 1818401 := bstep (se 2 (by rfl) ⟨681900, by rfl⟩ : syracuseStep 1818401 = 1363801) B1363801
theorem B6135587 : Blo 1211423 6135587 := bstep (se 1 (by rfl) ⟨4601690, by rfl⟩ : syracuseStep 6135587 = 9203381) B9203381
theorem B1212195 : Blo 1211423 1212195 := bstep (se 1 (by rfl) ⟨909146, by rfl⟩ : syracuseStep 1212195 = 1818293) B1818293
theorem B1212211 : Blo 1211423 1212211 := bstep (se 1 (by rfl) ⟨909158, by rfl⟩ : syracuseStep 1212211 = 1818317) B1818317
theorem B1818419 : Blo 1211423 1818419 := bstep (se 1 (by rfl) ⟨1363814, by rfl⟩ : syracuseStep 1818419 = 2727629) B2727629
theorem B1212227 : Blo 1211423 1212227 := bstep (se 1 (by rfl) ⟨909170, by rfl⟩ : syracuseStep 1212227 = 1818341) B1818341
theorem B1818449 : Blo 1211423 1818449 := bstep (se 2 (by rfl) ⟨681918, by rfl⟩ : syracuseStep 1818449 = 1363837) B1363837
theorem B1212243 : Blo 1211423 1212243 := bstep (se 1 (by rfl) ⟨909182, by rfl⟩ : syracuseStep 1212243 = 1818365) B1818365
theorem B1212259 : Blo 1211423 1212259 := bstep (se 1 (by rfl) ⟨909194, by rfl⟩ : syracuseStep 1212259 = 1818389) B1818389
theorem B1818467 : Blo 1211423 1818467 := bstep (se 1 (by rfl) ⟨1363850, by rfl⟩ : syracuseStep 1818467 = 2727701) B2727701
theorem B1212275 : Blo 1211423 1212275 := bstep (se 1 (by rfl) ⟨909206, by rfl⟩ : syracuseStep 1212275 = 1818413) B1818413
theorem B1818497 : Blo 1211423 1818497 := bstep (se 2 (by rfl) ⟨681936, by rfl⟩ : syracuseStep 1818497 = 1363873) B1363873
theorem B1212291 : Blo 1211423 1212291 := bstep (se 1 (by rfl) ⟨909218, by rfl⟩ : syracuseStep 1212291 = 1818437) B1818437
theorem B1212307 : Blo 1211423 1212307 := bstep (se 1 (by rfl) ⟨909230, by rfl⟩ : syracuseStep 1212307 = 1818461) B1818461
theorem B1818515 : Blo 1211423 1818515 := bstep (se 1 (by rfl) ⟨1363886, by rfl⟩ : syracuseStep 1818515 = 2727773) B2727773
theorem B1212323 : Blo 1211423 1212323 := bstep (se 1 (by rfl) ⟨909242, by rfl⟩ : syracuseStep 1212323 = 1818485) B1818485
theorem B1818545 : Blo 1211423 1818545 := bstep (se 2 (by rfl) ⟨681954, by rfl⟩ : syracuseStep 1818545 = 1363909) B1363909
theorem B1212339 : Blo 1211423 1212339 := bstep (se 1 (by rfl) ⟨909254, by rfl⟩ : syracuseStep 1212339 = 1818509) B1818509
theorem B14753717 : Blo 1211423 14753717 := bstep (se 5 (by rfl) ⟨691580, by rfl⟩ : syracuseStep 14753717 = 1383161) B1383161
theorem B1212355 : Blo 1211423 1212355 := bstep (se 1 (by rfl) ⟨909266, by rfl⟩ : syracuseStep 1212355 = 1818533) B1818533
theorem B1818563 : Blo 1211423 1818563 := bstep (se 1 (by rfl) ⟨1363922, by rfl⟩ : syracuseStep 1818563 = 2727845) B2727845
theorem B1212371 : Blo 1211423 1212371 := bstep (se 1 (by rfl) ⟨909278, by rfl⟩ : syracuseStep 1212371 = 1818557) B1818557
theorem B1818593 : Blo 1211423 1818593 := bstep (se 2 (by rfl) ⟨681972, by rfl⟩ : syracuseStep 1818593 = 1363945) B1363945
theorem B1212387 : Blo 1211423 1212387 := bstep (se 1 (by rfl) ⟨909290, by rfl⟩ : syracuseStep 1212387 = 1818581) B1818581
theorem B1212403 : Blo 1211423 1212403 := bstep (se 1 (by rfl) ⟨909302, by rfl⟩ : syracuseStep 1212403 = 1818605) B1818605
theorem B1818611 : Blo 1211423 1818611 := bstep (se 1 (by rfl) ⟨1363958, by rfl⟩ : syracuseStep 1818611 = 2727917) B2727917
theorem B1818635 : Blo 1211423 1818635 := bstep (se 1 (by rfl) ⟨1363976, by rfl⟩ : syracuseStep 1818635 = 2727953) B2727953
theorem B1212427 : Blo 1211423 1212427 := bstep (se 1 (by rfl) ⟨909320, by rfl⟩ : syracuseStep 1212427 = 1818641) B1818641
theorem B1818647 : Blo 1211423 1818647 := bstep (se 1 (by rfl) ⟨1363985, by rfl⟩ : syracuseStep 1818647 = 2727971) B2727971
theorem B1212439 : Blo 1211423 1212439 := bstep (se 1 (by rfl) ⟨909329, by rfl⟩ : syracuseStep 1212439 = 1818659) B1818659
theorem B35438627 : Blo 1211423 35438627 := bstep (se 1 (by rfl) ⟨26578970, by rfl⟩ : syracuseStep 35438627 = 53157941) B53157941
theorem B1212459 : Blo 1211423 1212459 := bstep (se 1 (by rfl) ⟨909344, by rfl⟩ : syracuseStep 1212459 = 1818689) B1818689
theorem B1212471 : Blo 1211423 1212471 := bstep (se 1 (by rfl) ⟨909353, by rfl⟩ : syracuseStep 1212471 = 1818707) B1818707
theorem B26214475 : Blo 1211423 26214475 := bstep (se 1 (by rfl) ⟨19660856, by rfl⟩ : syracuseStep 26214475 = 39321713) B39321713
theorem B3276875 : Blo 1211423 3276875 := bstep (se 1 (by rfl) ⟨2457656, by rfl⟩ : syracuseStep 3276875 = 4915313) B4915313
theorem B1212491 : Blo 1211423 1212491 := bstep (se 1 (by rfl) ⟨909368, by rfl⟩ : syracuseStep 1212491 = 1818737) B1818737
theorem B1212503 : Blo 1211423 1212503 := bstep (se 1 (by rfl) ⟨909377, by rfl⟩ : syracuseStep 1212503 = 1818755) B1818755
theorem B2728025 : Blo 1211423 2728025 := bstep (se 2 (by rfl) ⟨1023009, by rfl⟩ : syracuseStep 2728025 = 2046019) B2046019
theorem B1818713 : Blo 1211423 1818713 := bstep (se 2 (by rfl) ⟨682017, by rfl⟩ : syracuseStep 1818713 = 1364035) B1364035
theorem B1212523 : Blo 1211423 1212523 := bstep (se 1 (by rfl) ⟨909392, by rfl⟩ : syracuseStep 1212523 = 1818785) B1818785
theorem B1212535 : Blo 1211423 1212535 := bstep (se 1 (by rfl) ⟨909401, by rfl⟩ : syracuseStep 1212535 = 1818803) B1818803
theorem B1212555 : Blo 1211423 1212555 := bstep (se 1 (by rfl) ⟨909416, by rfl⟩ : syracuseStep 1212555 = 1818833) B1818833
theorem B2302091 : Blo 1211423 2302091 := bstep (se 1 (by rfl) ⟨1726568, by rfl⟩ : syracuseStep 2302091 = 3453137) B3453137
theorem B1212567 : Blo 1211423 1212567 := bstep (se 1 (by rfl) ⟨909425, by rfl⟩ : syracuseStep 1212567 = 1818851) B1818851
theorem B1212587 : Blo 1211423 1212587 := bstep (se 1 (by rfl) ⟨909440, by rfl⟩ : syracuseStep 1212587 = 1818881) B1818881
theorem B2728115 : Blo 1211423 2728115 := bstep (se 1 (by rfl) ⟨2046086, by rfl⟩ : syracuseStep 2728115 = 4092173) B4092173
theorem B1212599 : Blo 1211423 1212599 := bstep (se 1 (by rfl) ⟨909449, by rfl⟩ : syracuseStep 1212599 = 1818899) B1818899
theorem B1818827 : Blo 1211423 1818827 := bstep (se 1 (by rfl) ⟨1364120, by rfl⟩ : syracuseStep 1818827 = 2728241) B2728241
theorem B1212619 : Blo 1211423 1212619 := bstep (se 1 (by rfl) ⟨909464, by rfl⟩ : syracuseStep 1212619 = 1818929) B1818929
theorem B2728151 : Blo 1211423 2728151 := bstep (se 1 (by rfl) ⟨2046113, by rfl⟩ : syracuseStep 2728151 = 4092227) B4092227
theorem B1818839 : Blo 1211423 1818839 := bstep (se 1 (by rfl) ⟨1364129, by rfl⟩ : syracuseStep 1818839 = 2728259) B2728259
theorem B1212631 : Blo 1211423 1212631 := bstep (se 1 (by rfl) ⟨909473, by rfl⟩ : syracuseStep 1212631 = 1818947) B1818947
theorem B1212651 : Blo 1211423 1212651 := bstep (se 1 (by rfl) ⟨909488, by rfl⟩ : syracuseStep 1212651 = 1818977) B1818977
theorem B1212663 : Blo 1211423 1212663 := bstep (se 1 (by rfl) ⟨909497, by rfl⟩ : syracuseStep 1212663 = 1818995) B1818995
theorem B1212683 : Blo 1211423 1212683 := bstep (se 1 (by rfl) ⟨909512, by rfl⟩ : syracuseStep 1212683 = 1819025) B1819025
theorem B1212695 : Blo 1211423 1212695 := bstep (se 1 (by rfl) ⟨909521, by rfl⟩ : syracuseStep 1212695 = 1819043) B1819043
theorem B1818905 : Blo 1211423 1818905 := bstep (se 2 (by rfl) ⟨682089, by rfl⟩ : syracuseStep 1818905 = 1364179) B1364179
theorem B1212715 : Blo 1211423 1212715 := bstep (se 1 (by rfl) ⟨909536, by rfl⟩ : syracuseStep 1212715 = 1819073) B1819073
theorem B1212727 : Blo 1211423 1212727 := bstep (se 1 (by rfl) ⟨909545, by rfl⟩ : syracuseStep 1212727 = 1819091) B1819091
theorem B2302273 : Blo 1211423 2302273 := bstep (se 2 (by rfl) ⟨863352, by rfl⟩ : syracuseStep 2302273 = 1726705) B1726705
theorem B1212747 : Blo 1211423 1212747 := bstep (se 1 (by rfl) ⟨909560, by rfl⟩ : syracuseStep 1212747 = 1819121) B1819121
theorem B1212759 : Blo 1211423 1212759 := bstep (se 1 (by rfl) ⟨909569, by rfl⟩ : syracuseStep 1212759 = 1819139) B1819139
theorem B1212779 : Blo 1211423 1212779 := bstep (se 1 (by rfl) ⟨909584, by rfl⟩ : syracuseStep 1212779 = 1819169) B1819169
theorem B1212791 : Blo 1211423 1212791 := bstep (se 1 (by rfl) ⟨909593, by rfl⟩ : syracuseStep 1212791 = 1819187) B1819187
theorem B2728331 : Blo 1211423 2728331 := bstep (se 1 (by rfl) ⟨2046248, by rfl⟩ : syracuseStep 2728331 = 4092497) B4092497
theorem B1819019 : Blo 1211423 1819019 := bstep (se 1 (by rfl) ⟨1364264, by rfl⟩ : syracuseStep 1819019 = 2728529) B2728529
theorem B1212811 : Blo 1211423 1212811 := bstep (se 1 (by rfl) ⟨909608, by rfl⟩ : syracuseStep 1212811 = 1819217) B1819217
theorem B1819031 : Blo 1211423 1819031 := bstep (se 1 (by rfl) ⟨1364273, by rfl⟩ : syracuseStep 1819031 = 2728547) B2728547
theorem B1212823 : Blo 1211423 1212823 := bstep (se 1 (by rfl) ⟨909617, by rfl⟩ : syracuseStep 1212823 = 1819235) B1819235
theorem B1212843 : Blo 1211423 1212843 := bstep (se 1 (by rfl) ⟨909632, by rfl⟩ : syracuseStep 1212843 = 1819265) B1819265
theorem B9208241 : Blo 1211423 9208241 := bstep (se 2 (by rfl) ⟨3453090, by rfl⟩ : syracuseStep 9208241 = 6906181) B6906181
theorem B1212855 : Blo 1211423 1212855 := bstep (se 1 (by rfl) ⟨909641, by rfl⟩ : syracuseStep 1212855 = 1819283) B1819283
theorem B2728385 : Blo 1211423 2728385 := bstep (se 2 (by rfl) ⟨1023144, by rfl⟩ : syracuseStep 2728385 = 2046289) B2046289
theorem B1212875 : Blo 1211423 1212875 := bstep (se 1 (by rfl) ⟨909656, by rfl⟩ : syracuseStep 1212875 = 1819313) B1819313
theorem B1212887 : Blo 1211423 1212887 := bstep (se 1 (by rfl) ⟨909665, by rfl⟩ : syracuseStep 1212887 = 1819331) B1819331
theorem B1819097 : Blo 1211423 1819097 := bstep (se 2 (by rfl) ⟨682161, by rfl⟩ : syracuseStep 1819097 = 1364323) B1364323
theorem B1212907 : Blo 1211423 1212907 := bstep (se 1 (by rfl) ⟨909680, by rfl⟩ : syracuseStep 1212907 = 1819361) B1819361
theorem B1212919 : Blo 1211423 1212919 := bstep (se 1 (by rfl) ⟨909689, by rfl⟩ : syracuseStep 1212919 = 1819379) B1819379
theorem B1212939 : Blo 1211423 1212939 := bstep (se 1 (by rfl) ⟨909704, by rfl⟩ : syracuseStep 1212939 = 1819409) B1819409
theorem B1294871 : Blo 1211423 1294871 := bstep (se 1 (by rfl) ⟨971153, by rfl⟩ : syracuseStep 1294871 = 1942307) B1942307
theorem B1212951 : Blo 1211423 1212951 := bstep (se 1 (by rfl) ⟨909713, by rfl⟩ : syracuseStep 1212951 = 1819427) B1819427
theorem B17515043 : Blo 1211423 17515043 := bstep (se 1 (by rfl) ⟨13136282, by rfl⟩ : syracuseStep 17515043 = 26272565) B26272565
theorem B1212971 : Blo 1211423 1212971 := bstep (se 1 (by rfl) ⟨909728, by rfl⟩ : syracuseStep 1212971 = 1819457) B1819457
theorem B1212983 : Blo 1211423 1212983 := bstep (se 1 (by rfl) ⟨909737, by rfl⟩ : syracuseStep 1212983 = 1819475) B1819475
theorem B1819211 : Blo 1211423 1819211 := bstep (se 1 (by rfl) ⟨1364408, by rfl⟩ : syracuseStep 1819211 = 2728817) B2728817
theorem B1213003 : Blo 1211423 1213003 := bstep (se 1 (by rfl) ⟨909752, by rfl⟩ : syracuseStep 1213003 = 1819505) B1819505
theorem B1819223 : Blo 1211423 1819223 := bstep (se 1 (by rfl) ⟨1364417, by rfl⟩ : syracuseStep 1819223 = 2728835) B2728835
theorem B1213015 : Blo 1211423 1213015 := bstep (se 1 (by rfl) ⟨909761, by rfl⟩ : syracuseStep 1213015 = 1819523) B1819523
theorem B1213035 : Blo 1211423 1213035 := bstep (se 1 (by rfl) ⟨909776, by rfl⟩ : syracuseStep 1213035 = 1819553) B1819553
theorem B1213047 : Blo 1211423 1213047 := bstep (se 1 (by rfl) ⟨909785, by rfl⟩ : syracuseStep 1213047 = 1819571) B1819571
theorem B1213067 : Blo 1211423 1213067 := bstep (se 1 (by rfl) ⟨909800, by rfl⟩ : syracuseStep 1213067 = 1819601) B1819601
theorem B1213079 : Blo 1211423 1213079 := bstep (se 1 (by rfl) ⟨909809, by rfl⟩ : syracuseStep 1213079 = 1819619) B1819619
theorem B2728601 : Blo 1211423 2728601 := bstep (se 2 (by rfl) ⟨1023225, by rfl⟩ : syracuseStep 2728601 = 2046451) B2046451
theorem B1819289 : Blo 1211423 1819289 := bstep (se 2 (by rfl) ⟨682233, by rfl⟩ : syracuseStep 1819289 = 1364467) B1364467
theorem B1213099 : Blo 1211423 1213099 := bstep (se 1 (by rfl) ⟨909824, by rfl⟩ : syracuseStep 1213099 = 1819649) B1819649
theorem B1213111 : Blo 1211423 1213111 := bstep (se 1 (by rfl) ⟨909833, by rfl⟩ : syracuseStep 1213111 = 1819667) B1819667
theorem B1213131 : Blo 1211423 1213131 := bstep (se 1 (by rfl) ⟨909848, by rfl⟩ : syracuseStep 1213131 = 1819697) B1819697
theorem B1213143 : Blo 1211423 1213143 := bstep (se 1 (by rfl) ⟨909857, by rfl⟩ : syracuseStep 1213143 = 1819715) B1819715
theorem B2589401 : Blo 1211423 2589401 := bstep (se 2 (by rfl) ⟨971025, by rfl⟩ : syracuseStep 2589401 = 1942051) B1942051
theorem B1213163 : Blo 1211423 1213163 := bstep (se 1 (by rfl) ⟨909872, by rfl⟩ : syracuseStep 1213163 = 1819745) B1819745
theorem B2728691 : Blo 1211423 2728691 := bstep (se 1 (by rfl) ⟨2046518, by rfl⟩ : syracuseStep 2728691 = 4093037) B4093037
theorem B1213175 : Blo 1211423 1213175 := bstep (se 1 (by rfl) ⟨909881, by rfl⟩ : syracuseStep 1213175 = 1819763) B1819763
theorem B1819403 : Blo 1211423 1819403 := bstep (se 1 (by rfl) ⟨1364552, by rfl⟩ : syracuseStep 1819403 = 2729105) B2729105
theorem B1213195 : Blo 1211423 1213195 := bstep (se 1 (by rfl) ⟨909896, by rfl⟩ : syracuseStep 1213195 = 1819793) B1819793
theorem B3687191 : Blo 1211423 3687191 := bstep (se 1 (by rfl) ⟨2765393, by rfl⟩ : syracuseStep 3687191 = 5530787) B5530787
theorem B2728727 : Blo 1211423 2728727 := bstep (se 1 (by rfl) ⟨2046545, by rfl⟩ : syracuseStep 2728727 = 4093091) B4093091
theorem B1819415 : Blo 1211423 1819415 := bstep (se 1 (by rfl) ⟨1364561, by rfl⟩ : syracuseStep 1819415 = 2729123) B2729123
theorem B1213207 : Blo 1211423 1213207 := bstep (se 1 (by rfl) ⟨909905, by rfl⟩ : syracuseStep 1213207 = 1819811) B1819811
theorem B1213227 : Blo 1211423 1213227 := bstep (se 1 (by rfl) ⟨909920, by rfl⟩ : syracuseStep 1213227 = 1819841) B1819841
theorem B1213239 : Blo 1211423 1213239 := bstep (se 1 (by rfl) ⟨909929, by rfl⟩ : syracuseStep 1213239 = 1819859) B1819859
theorem B1213259 : Blo 1211423 1213259 := bstep (se 1 (by rfl) ⟨909944, by rfl⟩ : syracuseStep 1213259 = 1819889) B1819889
theorem B5530457 : Blo 1211423 5530457 := bstep (se 2 (by rfl) ⟨2073921, by rfl⟩ : syracuseStep 5530457 = 4147843) B4147843
theorem B1819481 : Blo 1211423 1819481 := bstep (se 2 (by rfl) ⟨682305, by rfl⟩ : syracuseStep 1819481 = 1364611) B1364611
theorem B1213271 : Blo 1211423 1213271 := bstep (se 1 (by rfl) ⟨909953, by rfl⟩ : syracuseStep 1213271 = 1819907) B1819907
theorem B1213291 : Blo 1211423 1213291 := bstep (se 1 (by rfl) ⟨909968, by rfl⟩ : syracuseStep 1213291 = 1819937) B1819937
theorem B1213303 : Blo 1211423 1213303 := bstep (se 1 (by rfl) ⟨909977, by rfl⟩ : syracuseStep 1213303 = 1819955) B1819955
theorem B1213323 : Blo 1211423 1213323 := bstep (se 1 (by rfl) ⟨909992, by rfl⟩ : syracuseStep 1213323 = 1819985) B1819985
theorem B9208727 : Blo 1211423 9208727 := bstep (se 1 (by rfl) ⟨6906545, by rfl⟩ : syracuseStep 9208727 = 13813091) B13813091
theorem B1213335 : Blo 1211423 1213335 := bstep (se 1 (by rfl) ⟨910001, by rfl⟩ : syracuseStep 1213335 = 1820003) B1820003
theorem B1213355 : Blo 1211423 1213355 := bstep (se 1 (by rfl) ⟨910016, by rfl⟩ : syracuseStep 1213355 = 1820033) B1820033
theorem B1213367 : Blo 1211423 1213367 := bstep (se 1 (by rfl) ⟨910025, by rfl⟩ : syracuseStep 1213367 = 1820051) B1820051
theorem B2728907 : Blo 1211423 2728907 := bstep (se 1 (by rfl) ⟨2046680, by rfl⟩ : syracuseStep 2728907 = 4093361) B4093361
theorem B1819595 : Blo 1211423 1819595 := bstep (se 1 (by rfl) ⟨1364696, by rfl⟩ : syracuseStep 1819595 = 2729393) B2729393
theorem B1213387 : Blo 1211423 1213387 := bstep (se 1 (by rfl) ⟨910040, by rfl⟩ : syracuseStep 1213387 = 1820081) B1820081
theorem B1819607 : Blo 1211423 1819607 := bstep (se 1 (by rfl) ⟨1364705, by rfl⟩ : syracuseStep 1819607 = 2729411) B2729411
theorem B1213399 : Blo 1211423 1213399 := bstep (se 1 (by rfl) ⟨910049, by rfl⟩ : syracuseStep 1213399 = 1820099) B1820099
theorem B4367321 : Blo 1211423 4367321 := bstep (se 2 (by rfl) ⟨1637745, by rfl⟩ : syracuseStep 4367321 = 3275491) B3275491
theorem B3687385 : Blo 1211423 3687385 := bstep (se 2 (by rfl) ⟨1382769, by rfl⟩ : syracuseStep 3687385 = 2765539) B2765539
theorem B1213419 : Blo 1211423 1213419 := bstep (se 1 (by rfl) ⟨910064, by rfl⟩ : syracuseStep 1213419 = 1820129) B1820129
theorem B2728961 : Blo 1211423 2728961 := bstep (se 2 (by rfl) ⟨1023360, by rfl⟩ : syracuseStep 2728961 = 2046721) B2046721
theorem B2302987 : Blo 1211423 2302987 := bstep (se 1 (by rfl) ⟨1727240, by rfl⟩ : syracuseStep 2302987 = 3454481) B3454481
theorem B1819673 : Blo 1211423 1819673 := bstep (se 2 (by rfl) ⟨682377, by rfl⟩ : syracuseStep 1819673 = 1364755) B1364755
theorem B1229899 : Blo 1211423 1229899 := bstep (se 1 (by rfl) ⟨922424, by rfl⟩ : syracuseStep 1229899 = 1844849) B1844849
theorem B2303063 : Blo 1211423 2303063 := bstep (se 1 (by rfl) ⟨1727297, by rfl⟩ : syracuseStep 2303063 = 3454595) B3454595
theorem B1819787 : Blo 1211423 1819787 := bstep (se 1 (by rfl) ⟨1364840, by rfl⟩ : syracuseStep 1819787 = 2729681) B2729681
theorem B1819799 : Blo 1211423 1819799 := bstep (se 1 (by rfl) ⟨1364849, by rfl⟩ : syracuseStep 1819799 = 2729699) B2729699
theorem B3450073 : Blo 1211423 3450073 := bstep (se 2 (by rfl) ⟨1293777, by rfl⟩ : syracuseStep 3450073 = 2587555) B2587555
theorem B7374041 : Blo 1211423 7374041 := bstep (se 2 (by rfl) ⟨2765265, by rfl⟩ : syracuseStep 7374041 = 5530531) B5530531
theorem B2729177 : Blo 1211423 2729177 := bstep (se 2 (by rfl) ⟨1023441, by rfl⟩ : syracuseStep 2729177 = 2046883) B2046883
theorem B1819865 : Blo 1211423 1819865 := bstep (se 2 (by rfl) ⟨682449, by rfl⟩ : syracuseStep 1819865 = 1364899) B1364899
theorem B2729267 : Blo 1211423 2729267 := bstep (se 1 (by rfl) ⟨2046950, by rfl⟩ : syracuseStep 2729267 = 4093901) B4093901
theorem B1312075 : Blo 1211423 1312075 := bstep (se 1 (by rfl) ⟨984056, by rfl⟩ : syracuseStep 1312075 = 1968113) B1968113
theorem B1533259 : Blo 1211423 1533259 := bstep (se 1 (by rfl) ⟨1149944, by rfl⟩ : syracuseStep 1533259 = 2299889) B2299889
theorem B1819979 : Blo 1211423 1819979 := bstep (se 1 (by rfl) ⟨1364984, by rfl⟩ : syracuseStep 1819979 = 2729969) B2729969
theorem B2729303 : Blo 1211423 2729303 := bstep (se 1 (by rfl) ⟨2046977, by rfl⟩ : syracuseStep 2729303 = 4093955) B4093955
theorem B1819991 : Blo 1211423 1819991 := bstep (se 1 (by rfl) ⟨1364993, by rfl⟩ : syracuseStep 1819991 = 2729987) B2729987
theorem B4662659 : Blo 1211423 4662659 := bstep (se 1 (by rfl) ⟨3496994, by rfl⟩ : syracuseStep 4662659 = 6993989) B6993989
theorem B1820057 : Blo 1211423 1820057 := bstep (se 2 (by rfl) ⟨682521, by rfl⟩ : syracuseStep 1820057 = 1365043) B1365043
theorem B2622937 : Blo 1211423 2622937 := bstep (se 2 (by rfl) ⟨983601, by rfl⟩ : syracuseStep 2622937 = 1967203) B1967203
theorem B4605443 : Blo 1211423 4605443 := bstep (se 1 (by rfl) ⟨3454082, by rfl⟩ : syracuseStep 4605443 = 6908165) B6908165
theorem B2729483 : Blo 1211423 2729483 := bstep (se 1 (by rfl) ⟨2047112, by rfl⟩ : syracuseStep 2729483 = 4094225) B4094225
theorem B4605457 : Blo 1211423 4605457 := bstep (se 2 (by rfl) ⟨1727046, by rfl⟩ : syracuseStep 4605457 = 3454093) B3454093
theorem B6907457 : Blo 1211423 6907457 := bstep (se 2 (by rfl) ⟨2590296, by rfl⟩ : syracuseStep 6907457 = 5180593) B5180593
theorem B2729537 : Blo 1211423 2729537 := bstep (se 2 (by rfl) ⟨1023576, by rfl⟩ : syracuseStep 2729537 = 2047153) B2047153
theorem B15738443 : Blo 1211423 15738443 := bstep (se 1 (by rfl) ⟨11803832, by rfl⟩ : syracuseStep 15738443 = 23607665) B23607665
theorem B4089419 : Blo 1211423 4089419 := bstep (se 1 (by rfl) ⟨3067064, by rfl⟩ : syracuseStep 4089419 = 6134129) B6134129
theorem B17475223 : Blo 1211423 17475223 := bstep (se 1 (by rfl) ⟨13106417, by rfl⟩ : syracuseStep 17475223 = 26212835) B26212835
theorem B2590451 : Blo 1211423 2590451 := bstep (se 1 (by rfl) ⟨1942838, by rfl⟩ : syracuseStep 2590451 = 3885677) B3885677
theorem B2729753 : Blo 1211423 2729753 := bstep (se 2 (by rfl) ⟨1023657, by rfl⟩ : syracuseStep 2729753 = 2047315) B2047315
theorem B4605761 : Blo 1211423 4605761 := bstep (se 2 (by rfl) ⟨1727160, by rfl⟩ : syracuseStep 4605761 = 3454321) B3454321
theorem B5179211 : Blo 1211423 5179211 := bstep (se 1 (by rfl) ⟨3884408, by rfl⟩ : syracuseStep 5179211 = 7768817) B7768817
theorem B4089689 : Blo 1211423 4089689 := bstep (se 2 (by rfl) ⟨1533633, by rfl⟩ : syracuseStep 4089689 = 3067267) B3067267
theorem B6137693 : Blo 1211423 6137693 := bstep (se 3 (by rfl) ⟨1150817, by rfl⟩ : syracuseStep 6137693 = 2301635) B2301635
theorem B2729843 : Blo 1211423 2729843 := bstep (se 1 (by rfl) ⟨2047382, by rfl⟩ : syracuseStep 2729843 = 4094765) B4094765
theorem B1943435 : Blo 1211423 1943435 := bstep (se 1 (by rfl) ⟨1457576, by rfl⟩ : syracuseStep 1943435 = 2915153) B2915153
theorem B2729879 : Blo 1211423 2729879 := bstep (se 1 (by rfl) ⟨2047409, by rfl⟩ : syracuseStep 2729879 = 4094819) B4094819
theorem B4917293 : Blo 1211423 4917293 := bstep (se 3 (by rfl) ⟨921992, by rfl⟩ : syracuseStep 4917293 = 1843985) B1843985
theorem B2730059 : Blo 1211423 2730059 := bstep (se 1 (by rfl) ⟨2047544, by rfl⟩ : syracuseStep 2730059 = 4095089) B4095089
theorem B2730113 : Blo 1211423 2730113 := bstep (se 2 (by rfl) ⟨1023792, by rfl⟩ : syracuseStep 2730113 = 2047585) B2047585
theorem B8734871 : Blo 1211423 8734871 := bstep (se 1 (by rfl) ⟨6551153, by rfl⟩ : syracuseStep 8734871 = 13102307) B13102307
theorem B26232983 : Blo 1211423 26232983 := bstep (se 1 (by rfl) ⟨19674737, by rfl⟩ : syracuseStep 26232983 = 39349475) B39349475
theorem B1534231 : Blo 1211423 1534231 := bstep (se 1 (by rfl) ⟨1150673, by rfl⟩ : syracuseStep 1534231 = 2301347) B2301347
theorem B2459927 : Blo 1211423 2459927 := bstep (se 1 (by rfl) ⟨1844945, by rfl⟩ : syracuseStep 2459927 = 3689891) B3689891
theorem B11659565 : Blo 1211423 11659565 := bstep (se 3 (by rfl) ⟨2186168, by rfl⟩ : syracuseStep 11659565 = 4372337) B4372337
theorem B2591041 : Blo 1211423 2591041 := bstep (se 2 (by rfl) ⟨971640, by rfl⟩ : syracuseStep 2591041 = 1943281) B1943281
theorem B10357085 : Blo 1211423 10357085 := bstep (se 3 (by rfl) ⟨1941953, by rfl⟩ : syracuseStep 10357085 = 3883907) B3883907
theorem B7375283 : Blo 1211423 7375283 := bstep (se 1 (by rfl) ⟨5531462, by rfl⟩ : syracuseStep 7375283 = 11062925) B11062925
theorem B4606429 : Blo 1211423 4606429 := bstep (se 3 (by rfl) ⟨863705, by rfl⟩ : syracuseStep 4606429 = 1727411) B1727411
theorem B4090391 : Blo 1211423 4090391 := bstep (se 1 (by rfl) ⟨3067793, by rfl⟩ : syracuseStep 4090391 = 6135587) B6135587
theorem B3066457 : Blo 1211423 3066457 := bstep (se 2 (by rfl) ⟨1149921, by rfl⟩ : syracuseStep 3066457 = 2299843) B2299843
theorem B10496729 : Blo 1211423 10496729 := bstep (se 2 (by rfl) ⟨3936273, by rfl⟩ : syracuseStep 10496729 = 7872547) B7872547
theorem B5180183 : Blo 1211423 5180183 := bstep (se 1 (by rfl) ⟨3885137, by rfl⟩ : syracuseStep 5180183 = 7770275) B7770275
theorem B40381361 : Blo 1211423 40381361 := bstep (se 2 (by rfl) ⟨15143010, by rfl⟩ : syracuseStep 40381361 = 30286021) B30286021
theorem B1362955 : Blo 1211423 1362955 := bstep (se 1 (by rfl) ⟨1022216, by rfl⟩ : syracuseStep 1362955 = 2044433) B2044433
theorem B4090931 : Blo 1211423 4090931 := bstep (se 1 (by rfl) ⟨3068198, by rfl⟩ : syracuseStep 4090931 = 6136397) B6136397
theorem B2911307 : Blo 1211423 2911307 := bstep (se 1 (by rfl) ⟨2183480, by rfl⟩ : syracuseStep 2911307 = 4366961) B4366961
theorem B1535051 : Blo 1211423 1535051 := bstep (se 1 (by rfl) ⟨1151288, by rfl⟩ : syracuseStep 1535051 = 2302577) B2302577
theorem B3451997 : Blo 1211423 3451997 := bstep (se 3 (by rfl) ⟨647249, by rfl⟩ : syracuseStep 3451997 = 1294499) B1294499
theorem B1363063 : Blo 1211423 1363063 := bstep (se 1 (by rfl) ⟨1022297, by rfl⟩ : syracuseStep 1363063 = 2044595) B2044595
theorem B1363243 : Blo 1211423 1363243 := bstep (se 1 (by rfl) ⟨1022432, by rfl⟩ : syracuseStep 1363243 = 2044865) B2044865
theorem B8293697 : Blo 1211423 8293697 := bstep (se 2 (by rfl) ⟨3110136, by rfl⟩ : syracuseStep 8293697 = 6220273) B6220273
theorem B4091201 : Blo 1211423 4091201 := bstep (se 2 (by rfl) ⟨1534200, by rfl⟩ : syracuseStep 4091201 = 3068401) B3068401
theorem B4369729 : Blo 1211423 4369729 := bstep (se 2 (by rfl) ⟨1638648, by rfl⟩ : syracuseStep 4369729 = 3277297) B3277297
theorem B1363351 : Blo 1211423 1363351 := bstep (se 1 (by rfl) ⟨1022513, by rfl⟩ : syracuseStep 1363351 = 2045027) B2045027
theorem B1363531 : Blo 1211423 1363531 := bstep (se 1 (by rfl) ⟨1022648, by rfl⟩ : syracuseStep 1363531 = 2045297) B2045297
theorem B3067571 : Blo 1211423 3067571 := bstep (se 1 (by rfl) ⟨2300678, by rfl⟩ : syracuseStep 3067571 = 4601357) B4601357
theorem B1363639 : Blo 1211423 1363639 := bstep (se 1 (by rfl) ⟨1022729, by rfl⟩ : syracuseStep 1363639 = 2045459) B2045459
theorem B4091741 : Blo 1211423 4091741 := bstep (se 3 (by rfl) ⟨767201, by rfl⟩ : syracuseStep 4091741 = 1534403) B1534403
theorem B1363819 : Blo 1211423 1363819 := bstep (se 1 (by rfl) ⟨1022864, by rfl⟩ : syracuseStep 1363819 = 2045729) B2045729
theorem B6139799 : Blo 1211423 6139799 := bstep (se 1 (by rfl) ⟨4604849, by rfl⟩ : syracuseStep 6139799 = 9209699) B9209699
theorem B1363927 : Blo 1211423 1363927 := bstep (se 1 (by rfl) ⟨1022945, by rfl⟩ : syracuseStep 1363927 = 2045891) B2045891
theorem B3067865 : Blo 1211423 3067865 := bstep (se 2 (by rfl) ⟨1150449, by rfl⟩ : syracuseStep 3067865 = 2300899) B2300899
theorem B27308107 : Blo 1211423 27308107 := bstep (se 1 (by rfl) ⟨20481080, by rfl⟩ : syracuseStep 27308107 = 40962161) B40962161
theorem B1364107 : Blo 1211423 1364107 := bstep (se 1 (by rfl) ⟨1023080, by rfl⟩ : syracuseStep 1364107 = 2046161) B2046161
theorem B8736947 : Blo 1211423 8736947 := bstep (se 1 (by rfl) ⟨6552710, by rfl⟩ : syracuseStep 8736947 = 13105421) B13105421
theorem B7770329 : Blo 1211423 7770329 := bstep (se 2 (by rfl) ⟨2913873, by rfl⟩ : syracuseStep 7770329 = 5827747) B5827747
theorem B2625779 : Blo 1211423 2625779 := bstep (se 1 (by rfl) ⟨1969334, by rfl⟩ : syracuseStep 2625779 = 3938669) B3938669
theorem B1364215 : Blo 1211423 1364215 := bstep (se 1 (by rfl) ⟨1023161, by rfl⟩ : syracuseStep 1364215 = 2046323) B2046323
theorem B1749271 : Blo 1211423 1749271 := bstep (se 1 (by rfl) ⟨1311953, by rfl⟩ : syracuseStep 1749271 = 2623907) B2623907
theorem B2953523 : Blo 1211423 2953523 := bstep (se 1 (by rfl) ⟨2215142, by rfl⟩ : syracuseStep 2953523 = 4430285) B4430285
theorem B6902081 : Blo 1211423 6902081 := bstep (se 2 (by rfl) ⟨2588280, by rfl⟩ : syracuseStep 6902081 = 5176561) B5176561
theorem B1364395 : Blo 1211423 1364395 := bstep (se 1 (by rfl) ⟨1023296, by rfl⟩ : syracuseStep 1364395 = 2046593) B2046593
theorem B2183617 : Blo 1211423 2183617 := bstep (se 2 (by rfl) ⟨818856, by rfl⟩ : syracuseStep 2183617 = 1637713) B1637713
theorem B12440081 : Blo 1211423 12440081 := bstep (se 2 (by rfl) ⟨4665030, by rfl⟩ : syracuseStep 12440081 = 9330061) B9330061
theorem B7377425 : Blo 1211423 7377425 := bstep (se 2 (by rfl) ⟨2766534, by rfl⟩ : syracuseStep 7377425 = 5533069) B5533069
theorem B1364503 : Blo 1211423 1364503 := bstep (se 1 (by rfl) ⟨1023377, by rfl⟩ : syracuseStep 1364503 = 2046755) B2046755
theorem B4600385 : Blo 1211423 4600385 := bstep (se 2 (by rfl) ⟨1725144, by rfl⟩ : syracuseStep 4600385 = 3450289) B3450289
theorem B1364683 : Blo 1211423 1364683 := bstep (se 1 (by rfl) ⟨1023512, by rfl⟩ : syracuseStep 1364683 = 2047025) B2047025
theorem B9966341 : Blo 1211423 9966341 := bstep (se 4 (by rfl) ⟨934344, by rfl⟩ : syracuseStep 9966341 = 1868689) B1868689
theorem B2913047 : Blo 1211423 2913047 := bstep (se 1 (by rfl) ⟨2184785, by rfl⟩ : syracuseStep 2913047 = 4369571) B4369571
theorem B1364791 : Blo 1211423 1364791 := bstep (se 1 (by rfl) ⟨1023593, by rfl⟩ : syracuseStep 1364791 = 2047187) B2047187
theorem B10359683 : Blo 1211423 10359683 := bstep (se 1 (by rfl) ⟨7769762, by rfl⟩ : syracuseStep 10359683 = 15539525) B15539525
theorem B2044811 : Blo 1211423 2044811 := bstep (se 1 (by rfl) ⟨1533608, by rfl⟩ : syracuseStep 2044811 = 3067217) B3067217
theorem B4092875 : Blo 1211423 4092875 := bstep (se 1 (by rfl) ⟨3069656, by rfl⟩ : syracuseStep 4092875 = 6139313) B6139313
theorem B1725401 : Blo 1211423 1725401 := bstep (se 2 (by rfl) ⟨647025, by rfl⟩ : syracuseStep 1725401 = 1294051) B1294051
theorem B1364971 : Blo 1211423 1364971 := bstep (se 1 (by rfl) ⟨1023728, by rfl⟩ : syracuseStep 1364971 = 2047457) B2047457
theorem B2184179 : Blo 1211423 2184179 := bstep (se 1 (by rfl) ⟨1638134, by rfl⟩ : syracuseStep 2184179 = 3276269) B3276269
theorem B2044939 : Blo 1211423 2044939 := bstep (se 1 (by rfl) ⟨1533704, by rfl⟩ : syracuseStep 2044939 = 3067409) B3067409
theorem B2626625 : Blo 1211423 2626625 := bstep (se 2 (by rfl) ⟨984984, by rfl⟩ : syracuseStep 2626625 = 1969969) B1969969
theorem B1365079 : Blo 1211423 1365079 := bstep (se 1 (by rfl) ⟨1023809, by rfl⟩ : syracuseStep 1365079 = 2047619) B2047619
theorem B2045081 : Blo 1211423 2045081 := bstep (se 2 (by rfl) ⟨766905, by rfl⟩ : syracuseStep 2045081 = 1533811) B1533811
theorem B9827507 : Blo 1211423 9827507 := bstep (se 1 (by rfl) ⟨7370630, by rfl⟩ : syracuseStep 9827507 = 14741261) B14741261
theorem B5182643 : Blo 1211423 5182643 := bstep (se 1 (by rfl) ⟨3886982, by rfl⟩ : syracuseStep 5182643 = 7773965) B7773965
theorem B4093145 : Blo 1211423 4093145 := bstep (se 2 (by rfl) ⟨1534929, by rfl⟩ : syracuseStep 4093145 = 3069859) B3069859
theorem B2045209 : Blo 1211423 2045209 := bstep (se 2 (by rfl) ⟨766953, by rfl⟩ : syracuseStep 2045209 = 1533907) B1533907
theorem B9835811 : Blo 1211423 9835811 := bstep (se 1 (by rfl) ⟨7376858, by rfl⟩ : syracuseStep 9835811 = 14753717) B14753717
theorem B5174579 : Blo 1211423 5174579 := bstep (se 1 (by rfl) ⟨3880934, by rfl⟩ : syracuseStep 5174579 = 7761869) B7761869
theorem B2331991 : Blo 1211423 2331991 := bstep (se 1 (by rfl) ⟨1748993, by rfl⟩ : syracuseStep 2331991 = 3497987) B3497987
theorem B11064707 : Blo 1211423 11064707 := bstep (se 1 (by rfl) ⟨8298530, by rfl⟩ : syracuseStep 11064707 = 16597061) B16597061
theorem B2184641 : Blo 1211423 2184641 := bstep (se 2 (by rfl) ⟨819240, by rfl⟩ : syracuseStep 2184641 = 1638481) B1638481
theorem B3069515 : Blo 1211423 3069515 := bstep (se 1 (by rfl) ⟨2302136, by rfl⟩ : syracuseStep 3069515 = 4604273) B4604273
theorem B1726039 : Blo 1211423 1726039 := bstep (se 1 (by rfl) ⟨1294529, by rfl⟩ : syracuseStep 1726039 = 2589059) B2589059
theorem B4912913 : Blo 1211423 4912913 := bstep (se 2 (by rfl) ⟨1842342, by rfl⟩ : syracuseStep 4912913 = 3684685) B3684685
theorem B2045783 : Blo 1211423 2045783 := bstep (se 1 (by rfl) ⟨1534337, by rfl⟩ : syracuseStep 2045783 = 3068675) B3068675
theorem B2766679 : Blo 1211423 2766679 := bstep (se 1 (by rfl) ⟨2075009, by rfl⟩ : syracuseStep 2766679 = 4150019) B4150019
theorem B2725721 : Blo 1211423 2725721 := bstep (se 2 (by rfl) ⟨1022145, by rfl⟩ : syracuseStep 2725721 = 2044291) B2044291
theorem B16824181 : Blo 1211423 16824181 := bstep (se 5 (by rfl) ⟨788633, by rfl⟩ : syracuseStep 16824181 = 1577267) B1577267
theorem B4093847 : Blo 1211423 4093847 := bstep (se 1 (by rfl) ⟨3070385, by rfl⟩ : syracuseStep 4093847 = 6140771) B6140771
theorem B15546289 : Blo 1211423 15546289 := bstep (se 2 (by rfl) ⟨5829858, by rfl⟩ : syracuseStep 15546289 = 11659717) B11659717
theorem B2725811 : Blo 1211423 2725811 := bstep (se 1 (by rfl) ⟨2044358, by rfl⟩ : syracuseStep 2725811 = 4088717) B4088717
theorem B3454913 : Blo 1211423 3454913 := bstep (se 2 (by rfl) ⟨1295592, by rfl⟩ : syracuseStep 3454913 = 2591185) B2591185
theorem B2725847 : Blo 1211423 2725847 := bstep (se 1 (by rfl) ⟨2044385, by rfl⟩ : syracuseStep 2725847 = 4088771) B4088771
theorem B2045911 : Blo 1211423 2045911 := bstep (se 1 (by rfl) ⟨1534433, by rfl⟩ : syracuseStep 2045911 = 3068867) B3068867
theorem B3454937 : Blo 1211423 3454937 := bstep (se 2 (by rfl) ⟨1295601, by rfl⟩ : syracuseStep 3454937 = 2591203) B2591203
theorem B4986845 : Blo 1211423 4986845 := bstep (se 3 (by rfl) ⟨935033, by rfl⟩ : syracuseStep 4986845 = 1870067) B1870067
theorem B4601873 : Blo 1211423 4601873 := bstep (se 2 (by rfl) ⟨1725702, by rfl⟩ : syracuseStep 4601873 = 3451405) B3451405
theorem B19666961 : Blo 1211423 19666961 := bstep (se 2 (by rfl) ⟨7375110, by rfl⟩ : syracuseStep 19666961 = 14750221) B14750221
theorem B2299927 : Blo 1211423 2299927 := bstep (se 1 (by rfl) ⟨1724945, by rfl⟩ : syracuseStep 2299927 = 3449891) B3449891
theorem B6133805 : Blo 1211423 6133805 := bstep (se 3 (by rfl) ⟨1150088, by rfl⟩ : syracuseStep 6133805 = 2300177) B2300177
theorem B3110987 : Blo 1211423 3110987 := bstep (se 1 (by rfl) ⟨2333240, by rfl⟩ : syracuseStep 3110987 = 4666481) B4666481
theorem B2021465 : Blo 1211423 2021465 := bstep (se 2 (by rfl) ⟨758049, by rfl⟩ : syracuseStep 2021465 = 1516099) B1516099
theorem B2726027 : Blo 1211423 2726027 := bstep (se 1 (by rfl) ⟨2044520, by rfl⟩ : syracuseStep 2726027 = 4089041) B4089041
theorem B2726081 : Blo 1211423 2726081 := bstep (se 2 (by rfl) ⟨1022280, by rfl⟩ : syracuseStep 2726081 = 2044561) B2044561
theorem B2300147 : Blo 1211423 2300147 := bstep (se 1 (by rfl) ⟨1725110, by rfl⟩ : syracuseStep 2300147 = 3450221) B3450221
theorem B3275101 : Blo 1211423 3275101 := bstep (se 3 (by rfl) ⟨614081, by rfl⟩ : syracuseStep 3275101 = 1228163) B1228163
theorem B1726859 : Blo 1211423 1726859 := bstep (se 1 (by rfl) ⟨1295144, by rfl⟩ : syracuseStep 1726859 = 2590289) B2590289
theorem B2726297 : Blo 1211423 2726297 := bstep (se 2 (by rfl) ⟨1022361, by rfl⟩ : syracuseStep 2726297 = 2044723) B2044723
theorem B4094387 : Blo 1211423 4094387 := bstep (se 1 (by rfl) ⟨3070790, by rfl⟩ : syracuseStep 4094387 = 6141581) B6141581
theorem B2300375 : Blo 1211423 2300375 := bstep (se 1 (by rfl) ⟨1725281, by rfl⟩ : syracuseStep 2300375 = 3450563) B3450563
theorem B4602329 : Blo 1211423 4602329 := bstep (se 2 (by rfl) ⟨1725873, by rfl⟩ : syracuseStep 4602329 = 3451747) B3451747
theorem B2726387 : Blo 1211423 2726387 := bstep (se 1 (by rfl) ⟨2044790, by rfl⟩ : syracuseStep 2726387 = 4089581) B4089581
theorem B2726423 : Blo 1211423 2726423 := bstep (se 1 (by rfl) ⟨2044817, by rfl⟩ : syracuseStep 2726423 = 4089635) B4089635
theorem B3070487 : Blo 1211423 3070487 := bstep (se 1 (by rfl) ⟨2302865, by rfl⟩ : syracuseStep 3070487 = 4605731) B4605731
theorem B2046539 : Blo 1211423 2046539 := bstep (se 1 (by rfl) ⟨1534904, by rfl⟩ : syracuseStep 2046539 = 3069809) B3069809
theorem B1817177 : Blo 1211423 1817177 := bstep (se 2 (by rfl) ⟨681441, by rfl⟩ : syracuseStep 1817177 = 1362883) B1362883
theorem B4602541 : Blo 1211423 4602541 := bstep (se 3 (by rfl) ⟨862976, by rfl⟩ : syracuseStep 4602541 = 1725953) B1725953
theorem B4094657 : Blo 1211423 4094657 := bstep (se 2 (by rfl) ⟨1535496, by rfl⟩ : syracuseStep 4094657 = 3070993) B3070993
theorem B1817291 : Blo 1211423 1817291 := bstep (se 1 (by rfl) ⟨1362968, by rfl⟩ : syracuseStep 1817291 = 2725937) B2725937
theorem B2726603 : Blo 1211423 2726603 := bstep (se 1 (by rfl) ⟨2044952, by rfl⟩ : syracuseStep 2726603 = 4089905) B4089905
theorem B2046667 : Blo 1211423 2046667 := bstep (se 1 (by rfl) ⟨1535000, by rfl⟩ : syracuseStep 2046667 = 3070001) B3070001
theorem B1817303 : Blo 1211423 1817303 := bstep (se 1 (by rfl) ⟨1362977, by rfl⟩ : syracuseStep 1817303 = 2725955) B2725955
theorem B2300633 : Blo 1211423 2300633 := bstep (se 2 (by rfl) ⟨862737, by rfl⟩ : syracuseStep 2300633 = 1725475) B1725475
theorem B4913885 : Blo 1211423 4913885 := bstep (se 3 (by rfl) ⟨921353, by rfl⟩ : syracuseStep 4913885 = 1842707) B1842707
theorem B2726657 : Blo 1211423 2726657 := bstep (se 2 (by rfl) ⟨1022496, by rfl⟩ : syracuseStep 2726657 = 2044993) B2044993
theorem B1817369 : Blo 1211423 1817369 := bstep (se 2 (by rfl) ⟨681513, by rfl⟩ : syracuseStep 1817369 = 1363027) B1363027
theorem B7772993 : Blo 1211423 7772993 := bstep (se 2 (by rfl) ⟨2914872, by rfl⟩ : syracuseStep 7772993 = 5829745) B5829745
theorem B2046809 : Blo 1211423 2046809 := bstep (se 2 (by rfl) ⟨767553, by rfl⟩ : syracuseStep 2046809 = 1535107) B1535107
theorem B1817483 : Blo 1211423 1817483 := bstep (se 1 (by rfl) ⟨1363112, by rfl⟩ : syracuseStep 1817483 = 2726225) B2726225
theorem B1383307 : Blo 1211423 1383307 := bstep (se 1 (by rfl) ⟨1037480, by rfl⟩ : syracuseStep 1383307 = 2074961) B2074961
theorem B1817495 : Blo 1211423 1817495 := bstep (se 1 (by rfl) ⟨1363121, by rfl⟩ : syracuseStep 1817495 = 2726243) B2726243
theorem B1817561 : Blo 1211423 1817561 := bstep (se 2 (by rfl) ⟨681585, by rfl⟩ : syracuseStep 1817561 = 1363171) B1363171
theorem B2726873 : Blo 1211423 2726873 := bstep (se 2 (by rfl) ⟨1022577, by rfl⟩ : syracuseStep 2726873 = 2045155) B2045155
theorem B2046937 : Blo 1211423 2046937 := bstep (se 2 (by rfl) ⟨767601, by rfl⟩ : syracuseStep 2046937 = 1535203) B1535203
theorem B4602845 : Blo 1211423 4602845 := bstep (se 3 (by rfl) ⟨863033, by rfl⟩ : syracuseStep 4602845 = 1726067) B1726067
theorem B3939293 : Blo 1211423 3939293 := bstep (se 3 (by rfl) ⟨738617, by rfl⟩ : syracuseStep 3939293 = 1477235) B1477235
theorem B4914179 : Blo 1211423 4914179 := bstep (se 1 (by rfl) ⟨3685634, by rfl⟩ : syracuseStep 4914179 = 7371269) B7371269
theorem B14736401 : Blo 1211423 14736401 := bstep (se 2 (by rfl) ⟨5526150, by rfl⟩ : syracuseStep 14736401 = 11052301) B11052301
theorem B1637399 : Blo 1211423 1637399 := bstep (se 1 (by rfl) ⟨1228049, by rfl⟩ : syracuseStep 1637399 = 2456099) B2456099
theorem B2366489 : Blo 1211423 2366489 := bstep (se 2 (by rfl) ⟨887433, by rfl⟩ : syracuseStep 2366489 = 1774867) B1774867
theorem B1211435 : Blo 1211423 1211435 := bstep (se 1 (by rfl) ⟨908576, by rfl⟩ : syracuseStep 1211435 = 1817153) B1817153
theorem B2726963 : Blo 1211423 2726963 := bstep (se 1 (by rfl) ⟨2045222, by rfl⟩ : syracuseStep 2726963 = 4090445) B4090445
theorem B1211447 : Blo 1211423 1211447 := bstep (se 1 (by rfl) ⟨908585, by rfl⟩ : syracuseStep 1211447 = 1817171) B1817171
theorem B1211467 : Blo 1211423 1211467 := bstep (se 1 (by rfl) ⟨908600, by rfl⟩ : syracuseStep 1211467 = 1817201) B1817201
theorem B1817675 : Blo 1211423 1817675 := bstep (se 1 (by rfl) ⟨1363256, by rfl⟩ : syracuseStep 1817675 = 2726513) B2726513
theorem B1211479 : Blo 1211423 1211479 := bstep (se 1 (by rfl) ⟨908609, by rfl⟩ : syracuseStep 1211479 = 1817219) B1817219
theorem B1817687 : Blo 1211423 1817687 := bstep (se 1 (by rfl) ⟨1363265, by rfl⟩ : syracuseStep 1817687 = 2726531) B2726531
theorem B2726999 : Blo 1211423 2726999 := bstep (se 1 (by rfl) ⟨2045249, by rfl⟩ : syracuseStep 2726999 = 4090499) B4090499
theorem B1211499 : Blo 1211423 1211499 := bstep (se 1 (by rfl) ⟨908624, by rfl⟩ : syracuseStep 1211499 = 1817249) B1817249
theorem B2301043 : Blo 1211423 2301043 := bstep (se 1 (by rfl) ⟨1725782, by rfl⟩ : syracuseStep 2301043 = 3451565) B3451565
theorem B1211511 : Blo 1211423 1211511 := bstep (se 1 (by rfl) ⟨908633, by rfl⟩ : syracuseStep 1211511 = 1817267) B1817267
theorem B1211531 : Blo 1211423 1211531 := bstep (se 1 (by rfl) ⟨908648, by rfl⟩ : syracuseStep 1211531 = 1817297) B1817297
theorem B1211543 : Blo 1211423 1211543 := bstep (se 1 (by rfl) ⟨908657, by rfl⟩ : syracuseStep 1211543 = 1817315) B1817315
theorem B1817753 : Blo 1211423 1817753 := bstep (se 2 (by rfl) ⟨681657, by rfl⟩ : syracuseStep 1817753 = 1363315) B1363315
theorem B1211563 : Blo 1211423 1211563 := bstep (se 1 (by rfl) ⟨908672, by rfl⟩ : syracuseStep 1211563 = 1817345) B1817345
theorem B5176493 : Blo 1211423 5176493 := bstep (se 3 (by rfl) ⟨970592, by rfl⟩ : syracuseStep 5176493 = 1941185) B1941185
theorem B3071155 : Blo 1211423 3071155 := bstep (se 1 (by rfl) ⟨2303366, by rfl⟩ : syracuseStep 3071155 = 4606733) B4606733
theorem B2915507 : Blo 1211423 2915507 := bstep (se 1 (by rfl) ⟨2186630, by rfl⟩ : syracuseStep 2915507 = 4373261) B4373261
theorem B1211575 : Blo 1211423 1211575 := bstep (se 1 (by rfl) ⟨908681, by rfl⟩ : syracuseStep 1211575 = 1817363) B1817363
theorem B1211595 : Blo 1211423 1211595 := bstep (se 1 (by rfl) ⟨908696, by rfl⟩ : syracuseStep 1211595 = 1817393) B1817393
theorem B1211607 : Blo 1211423 1211607 := bstep (se 1 (by rfl) ⟨908705, by rfl⟩ : syracuseStep 1211607 = 1817411) B1817411
theorem B4095197 : Blo 1211423 4095197 := bstep (se 3 (by rfl) ⟨767849, by rfl⟩ : syracuseStep 4095197 = 1535699) B1535699
theorem B1211627 : Blo 1211423 1211627 := bstep (se 1 (by rfl) ⟨908720, by rfl⟩ : syracuseStep 1211627 = 1817441) B1817441
theorem B1211639 : Blo 1211423 1211639 := bstep (se 1 (by rfl) ⟨908729, by rfl⟩ : syracuseStep 1211639 = 1817459) B1817459
theorem B1211659 : Blo 1211423 1211659 := bstep (se 1 (by rfl) ⟨908744, by rfl⟩ : syracuseStep 1211659 = 1817489) B1817489
theorem B1817867 : Blo 1211423 1817867 := bstep (se 1 (by rfl) ⟨1363400, by rfl⟩ : syracuseStep 1817867 = 2726801) B2726801
theorem B2727179 : Blo 1211423 2727179 := bstep (se 1 (by rfl) ⟨2045384, by rfl⟩ : syracuseStep 2727179 = 4090769) B4090769
theorem B8289553 : Blo 1211423 8289553 := bstep (se 2 (by rfl) ⟨3108582, by rfl⟩ : syracuseStep 8289553 = 6217165) B6217165
theorem B1211671 : Blo 1211423 1211671 := bstep (se 1 (by rfl) ⟨908753, by rfl⟩ : syracuseStep 1211671 = 1817507) B1817507
theorem B1817879 : Blo 1211423 1817879 := bstep (se 1 (by rfl) ⟨1363409, by rfl⟩ : syracuseStep 1817879 = 2726819) B2726819
theorem B1211691 : Blo 1211423 1211691 := bstep (se 1 (by rfl) ⟨908768, by rfl⟩ : syracuseStep 1211691 = 1817537) B1817537
theorem B1211703 : Blo 1211423 1211703 := bstep (se 1 (by rfl) ⟨908777, by rfl⟩ : syracuseStep 1211703 = 1817555) B1817555
theorem B2727233 : Blo 1211423 2727233 := bstep (se 2 (by rfl) ⟨1022712, by rfl⟩ : syracuseStep 2727233 = 2045425) B2045425
theorem B3071297 : Blo 1211423 3071297 := bstep (se 2 (by rfl) ⟨1151736, by rfl⟩ : syracuseStep 3071297 = 2303473) B2303473
theorem B8289611 : Blo 1211423 8289611 := bstep (se 1 (by rfl) ⟨6217208, by rfl⟩ : syracuseStep 8289611 = 12434417) B12434417
theorem B1211723 : Blo 1211423 1211723 := bstep (se 1 (by rfl) ⟨908792, by rfl⟩ : syracuseStep 1211723 = 1817585) B1817585
theorem B1211735 : Blo 1211423 1211735 := bstep (se 1 (by rfl) ⟨908801, by rfl⟩ : syracuseStep 1211735 = 1817603) B1817603
theorem B1817945 : Blo 1211423 1817945 := bstep (se 2 (by rfl) ⟨681729, by rfl⟩ : syracuseStep 1817945 = 1363459) B1363459
theorem B1211755 : Blo 1211423 1211755 := bstep (se 1 (by rfl) ⟨908816, by rfl⟩ : syracuseStep 1211755 = 1817633) B1817633
theorem B1211767 : Blo 1211423 1211767 := bstep (se 1 (by rfl) ⟨908825, by rfl⟩ : syracuseStep 1211767 = 1817651) B1817651
theorem B1211787 : Blo 1211423 1211787 := bstep (se 1 (by rfl) ⟨908840, by rfl⟩ : syracuseStep 1211787 = 1817681) B1817681
theorem B1211799 : Blo 1211423 1211799 := bstep (se 1 (by rfl) ⟨908849, by rfl⟩ : syracuseStep 1211799 = 1817699) B1817699
theorem B1211819 : Blo 1211423 1211819 := bstep (se 1 (by rfl) ⟨908864, by rfl⟩ : syracuseStep 1211819 = 1817729) B1817729
theorem B1211831 : Blo 1211423 1211831 := bstep (se 1 (by rfl) ⟨908873, by rfl⟩ : syracuseStep 1211831 = 1817747) B1817747
theorem B1211851 : Blo 1211423 1211851 := bstep (se 1 (by rfl) ⟨908888, by rfl⟩ : syracuseStep 1211851 = 1817777) B1817777
theorem B1818059 : Blo 1211423 1818059 := bstep (se 1 (by rfl) ⟨1363544, by rfl⟩ : syracuseStep 1818059 = 2727089) B2727089
theorem B1211863 : Blo 1211423 1211863 := bstep (se 1 (by rfl) ⟨908897, by rfl⟩ : syracuseStep 1211863 = 1817795) B1817795
theorem B1818071 : Blo 1211423 1818071 := bstep (se 1 (by rfl) ⟨1363553, by rfl⟩ : syracuseStep 1818071 = 2727107) B2727107
theorem B1211883 : Blo 1211423 1211883 := bstep (se 1 (by rfl) ⟨908912, by rfl⟩ : syracuseStep 1211883 = 1817825) B1817825
theorem B1211895 : Blo 1211423 1211895 := bstep (se 1 (by rfl) ⟨908921, by rfl⟩ : syracuseStep 1211895 = 1817843) B1817843
theorem B5176835 : Blo 1211423 5176835 := bstep (se 1 (by rfl) ⟨3882626, by rfl⟩ : syracuseStep 5176835 = 7765253) B7765253
theorem B1211915 : Blo 1211423 1211915 := bstep (se 1 (by rfl) ⟨908936, by rfl⟩ : syracuseStep 1211915 = 1817873) B1817873
theorem B1211927 : Blo 1211423 1211927 := bstep (se 1 (by rfl) ⟨908945, by rfl⟩ : syracuseStep 1211927 = 1817891) B1817891
theorem B2047511 : Blo 1211423 2047511 := bstep (se 1 (by rfl) ⟨1535633, by rfl⟩ : syracuseStep 2047511 = 3071267) B3071267
theorem B1818137 : Blo 1211423 1818137 := bstep (se 2 (by rfl) ⟨681801, by rfl⟩ : syracuseStep 1818137 = 1363603) B1363603
theorem B2727449 : Blo 1211423 2727449 := bstep (se 2 (by rfl) ⟨1022793, by rfl⟩ : syracuseStep 2727449 = 2045587) B2045587
theorem B1211947 : Blo 1211423 1211947 := bstep (se 1 (by rfl) ⟨908960, by rfl⟩ : syracuseStep 1211947 = 1817921) B1817921
theorem B1211959 : Blo 1211423 1211959 := bstep (se 1 (by rfl) ⟨908969, by rfl⟩ : syracuseStep 1211959 = 1817939) B1817939
theorem B1211979 : Blo 1211423 1211979 := bstep (se 1 (by rfl) ⟨908984, by rfl⟩ : syracuseStep 1211979 = 1817969) B1817969
theorem B1211991 : Blo 1211423 1211991 := bstep (se 1 (by rfl) ⟨908993, by rfl⟩ : syracuseStep 1211991 = 1817987) B1817987
theorem B2301529 : Blo 1211423 2301529 := bstep (se 2 (by rfl) ⟨863073, by rfl⟩ : syracuseStep 2301529 = 1726147) B1726147
theorem B1212011 : Blo 1211423 1212011 := bstep (se 1 (by rfl) ⟨909008, by rfl⟩ : syracuseStep 1212011 = 1818017) B1818017
theorem B2727539 : Blo 1211423 2727539 := bstep (se 1 (by rfl) ⟨2045654, by rfl⟩ : syracuseStep 2727539 = 4091309) B4091309
theorem B1212023 : Blo 1211423 1212023 := bstep (se 1 (by rfl) ⟨909017, by rfl⟩ : syracuseStep 1212023 = 1818035) B1818035
theorem B1212043 : Blo 1211423 1212043 := bstep (se 1 (by rfl) ⟨909032, by rfl⟩ : syracuseStep 1212043 = 1818065) B1818065
theorem B1818251 : Blo 1211423 1818251 := bstep (se 1 (by rfl) ⟨1363688, by rfl⟩ : syracuseStep 1818251 = 2727377) B2727377
theorem B1212055 : Blo 1211423 1212055 := bstep (se 1 (by rfl) ⟨909041, by rfl⟩ : syracuseStep 1212055 = 1818083) B1818083
theorem B1818263 : Blo 1211423 1818263 := bstep (se 1 (by rfl) ⟨1363697, by rfl⟩ : syracuseStep 1818263 = 2727395) B2727395
theorem B2727575 : Blo 1211423 2727575 := bstep (se 1 (by rfl) ⟨2045681, by rfl⟩ : syracuseStep 2727575 = 4091363) B4091363
theorem B1556119 : Blo 1211423 1556119 := bstep (se 1 (by rfl) ⟨1167089, by rfl⟩ : syracuseStep 1556119 = 2334179) B2334179
theorem B2047639 : Blo 1211423 2047639 := bstep (se 1 (by rfl) ⟨1535729, by rfl⟩ : syracuseStep 2047639 = 3071459) B3071459
theorem B1212075 : Blo 1211423 1212075 := bstep (se 1 (by rfl) ⟨909056, by rfl⟩ : syracuseStep 1212075 = 1818113) B1818113
theorem B1212087 : Blo 1211423 1212087 := bstep (se 1 (by rfl) ⟨909065, by rfl⟩ : syracuseStep 1212087 = 1818131) B1818131
theorem B1212107 : Blo 1211423 1212107 := bstep (se 1 (by rfl) ⟨909080, by rfl⟩ : syracuseStep 1212107 = 1818161) B1818161
theorem B2588375 : Blo 1211423 2588375 := bstep (se 1 (by rfl) ⟨1941281, by rfl⟩ : syracuseStep 2588375 = 3882563) B3882563
theorem B1212119 : Blo 1211423 1212119 := bstep (se 1 (by rfl) ⟨909089, by rfl⟩ : syracuseStep 1212119 = 1818179) B1818179
theorem B1818329 : Blo 1211423 1818329 := bstep (se 2 (by rfl) ⟨681873, by rfl⟩ : syracuseStep 1818329 = 1363747) B1363747
theorem B1212139 : Blo 1211423 1212139 := bstep (se 1 (by rfl) ⟨909104, by rfl⟩ : syracuseStep 1212139 = 1818209) B1818209
theorem B1212151 : Blo 1211423 1212151 := bstep (se 1 (by rfl) ⟨909113, by rfl⟩ : syracuseStep 1212151 = 1818227) B1818227
theorem B1212171 : Blo 1211423 1212171 := bstep (se 1 (by rfl) ⟨909128, by rfl⟩ : syracuseStep 1212171 = 1818257) B1818257
theorem B1212183 : Blo 1211423 1212183 := bstep (se 1 (by rfl) ⟨909137, by rfl⟩ : syracuseStep 1212183 = 1818275) B1818275
theorem B1212203 : Blo 1211423 1212203 := bstep (se 1 (by rfl) ⟨909152, by rfl⟩ : syracuseStep 1212203 = 1818305) B1818305
theorem B1212215 : Blo 1211423 1212215 := bstep (se 1 (by rfl) ⟨909161, by rfl⟩ : syracuseStep 1212215 = 1818323) B1818323
theorem B1212235 : Blo 1211423 1212235 := bstep (se 1 (by rfl) ⟨909176, by rfl⟩ : syracuseStep 1212235 = 1818353) B1818353
theorem B1818443 : Blo 1211423 1818443 := bstep (se 1 (by rfl) ⟨1363832, by rfl⟩ : syracuseStep 1818443 = 2727665) B2727665
theorem B2727755 : Blo 1211423 2727755 := bstep (se 1 (by rfl) ⟨2045816, by rfl⟩ : syracuseStep 2727755 = 4091633) B4091633
theorem B1212247 : Blo 1211423 1212247 := bstep (se 1 (by rfl) ⟨909185, by rfl⟩ : syracuseStep 1212247 = 1818371) B1818371
theorem B1818455 : Blo 1211423 1818455 := bstep (se 1 (by rfl) ⟨1363841, by rfl⟩ : syracuseStep 1818455 = 2727683) B2727683
theorem B4366169 : Blo 1211423 4366169 := bstep (se 2 (by rfl) ⟨1637313, by rfl⟩ : syracuseStep 4366169 = 3274627) B3274627
theorem B1212267 : Blo 1211423 1212267 := bstep (se 1 (by rfl) ⟨909200, by rfl⟩ : syracuseStep 1212267 = 1818401) B1818401
theorem B1212279 : Blo 1211423 1212279 := bstep (se 1 (by rfl) ⟨909209, by rfl⟩ : syracuseStep 1212279 = 1818419) B1818419
theorem B2727809 : Blo 1211423 2727809 := bstep (se 2 (by rfl) ⟨1022928, by rfl⟩ : syracuseStep 2727809 = 2045857) B2045857
theorem B1212299 : Blo 1211423 1212299 := bstep (se 1 (by rfl) ⟨909224, by rfl⟩ : syracuseStep 1212299 = 1818449) B1818449
theorem B1212311 : Blo 1211423 1212311 := bstep (se 1 (by rfl) ⟨909233, by rfl⟩ : syracuseStep 1212311 = 1818467) B1818467
theorem B1818521 : Blo 1211423 1818521 := bstep (se 2 (by rfl) ⟨681945, by rfl⟩ : syracuseStep 1818521 = 1363891) B1363891
theorem B1212331 : Blo 1211423 1212331 := bstep (se 1 (by rfl) ⟨909248, by rfl⟩ : syracuseStep 1212331 = 1818497) B1818497
theorem B13811633 : Blo 1211423 13811633 := bstep (se 2 (by rfl) ⟨5179362, by rfl⟩ : syracuseStep 13811633 = 10358725) B10358725
theorem B1212343 : Blo 1211423 1212343 := bstep (se 1 (by rfl) ⟨909257, by rfl⟩ : syracuseStep 1212343 = 1818515) B1818515
theorem B1212363 : Blo 1211423 1212363 := bstep (se 1 (by rfl) ⟨909272, by rfl⟩ : syracuseStep 1212363 = 1818545) B1818545
theorem B1212375 : Blo 1211423 1212375 := bstep (se 1 (by rfl) ⟨909281, by rfl⟩ : syracuseStep 1212375 = 1818563) B1818563
theorem B3882973 : Blo 1211423 3882973 := bstep (se 3 (by rfl) ⟨728057, by rfl⟩ : syracuseStep 3882973 = 1456115) B1456115
theorem B1212395 : Blo 1211423 1212395 := bstep (se 1 (by rfl) ⟨909296, by rfl⟩ : syracuseStep 1212395 = 1818593) B1818593
theorem B1212407 : Blo 1211423 1212407 := bstep (se 1 (by rfl) ⟨909305, by rfl⟩ : syracuseStep 1212407 = 1818611) B1818611
theorem B1212423 : Blo 1211423 1212423 := bstep (se 1 (by rfl) ⟨909317, by rfl⟩ : syracuseStep 1212423 = 1818635) B1818635
theorem B1212431 : Blo 1211423 1212431 := bstep (se 1 (by rfl) ⟨909323, by rfl⟩ : syracuseStep 1212431 = 1818647) B1818647
theorem B23625751 : Blo 1211423 23625751 := bstep (se 1 (by rfl) ⟨17719313, by rfl⟩ : syracuseStep 23625751 = 35438627) B35438627
theorem B1818683 : Blo 1211423 1818683 := bstep (se 1 (by rfl) ⟨1364012, by rfl⟩ : syracuseStep 1818683 = 2728025) B2728025
theorem B1212475 : Blo 1211423 1212475 := bstep (se 1 (by rfl) ⟨909356, by rfl⟩ : syracuseStep 1212475 = 1818713) B1818713
theorem B4366397 : Blo 1211423 4366397 := bstep (se 3 (by rfl) ⟨818699, by rfl⟩ : syracuseStep 4366397 = 1637399) B1637399
theorem B5824631 : Blo 1211423 5824631 := bstep (se 1 (by rfl) ⟨4368473, by rfl⟩ : syracuseStep 5824631 = 8736947) B8736947
theorem B1818743 : Blo 1211423 1818743 := bstep (se 1 (by rfl) ⟨1364057, by rfl⟩ : syracuseStep 1818743 = 2728115) B2728115
theorem B1212551 : Blo 1211423 1212551 := bstep (se 1 (by rfl) ⟨909413, by rfl⟩ : syracuseStep 1212551 = 1818827) B1818827
theorem B1818767 : Blo 1211423 1818767 := bstep (se 1 (by rfl) ⟨1364075, by rfl⟩ : syracuseStep 1818767 = 2728151) B2728151
theorem B1212559 : Blo 1211423 1212559 := bstep (se 1 (by rfl) ⟨909419, by rfl⟩ : syracuseStep 1212559 = 1818839) B1818839
theorem B7004333 : Blo 1211423 7004333 := bstep (se 3 (by rfl) ⟨1313312, by rfl⟩ : syracuseStep 7004333 = 2626625) B2626625
theorem B1818809 : Blo 1211423 1818809 := bstep (se 2 (by rfl) ⟨682053, by rfl⟩ : syracuseStep 1818809 = 1364107) B1364107
theorem B1212603 : Blo 1211423 1212603 := bstep (se 1 (by rfl) ⟨909452, by rfl⟩ : syracuseStep 1212603 = 1818905) B1818905
theorem B1818887 : Blo 1211423 1818887 := bstep (se 1 (by rfl) ⟨1364165, by rfl⟩ : syracuseStep 1818887 = 2728331) B2728331
theorem B1212679 : Blo 1211423 1212679 := bstep (se 1 (by rfl) ⟨909509, by rfl⟩ : syracuseStep 1212679 = 1819019) B1819019
theorem B1212687 : Blo 1211423 1212687 := bstep (se 1 (by rfl) ⟨909515, by rfl⟩ : syracuseStep 1212687 = 1819031) B1819031
theorem B1818923 : Blo 1211423 1818923 := bstep (se 1 (by rfl) ⟨1364192, by rfl⟩ : syracuseStep 1818923 = 2728385) B2728385
theorem B1212731 : Blo 1211423 1212731 := bstep (se 1 (by rfl) ⟨909548, by rfl⟩ : syracuseStep 1212731 = 1819097) B1819097
theorem B1818953 : Blo 1211423 1818953 := bstep (se 2 (by rfl) ⟨682107, by rfl⟩ : syracuseStep 1818953 = 1364215) B1364215
theorem B1212807 : Blo 1211423 1212807 := bstep (se 1 (by rfl) ⟨909605, by rfl⟩ : syracuseStep 1212807 = 1819211) B1819211
theorem B1212815 : Blo 1211423 1212815 := bstep (se 1 (by rfl) ⟨909611, by rfl⟩ : syracuseStep 1212815 = 1819223) B1819223
theorem B1819067 : Blo 1211423 1819067 := bstep (se 1 (by rfl) ⟨1364300, by rfl⟩ : syracuseStep 1819067 = 2728601) B2728601
theorem B1212859 : Blo 1211423 1212859 := bstep (se 1 (by rfl) ⟨909644, by rfl⟩ : syracuseStep 1212859 = 1819289) B1819289
theorem B4366801 : Blo 1211423 4366801 := bstep (se 2 (by rfl) ⟨1637550, by rfl⟩ : syracuseStep 4366801 = 3275101) B3275101
theorem B26206685 : Blo 1211423 26206685 := bstep (se 3 (by rfl) ⟨4913753, by rfl⟩ : syracuseStep 26206685 = 9827507) B9827507
theorem B13820381 : Blo 1211423 13820381 := bstep (se 3 (by rfl) ⟨2591321, by rfl⟩ : syracuseStep 13820381 = 5182643) B5182643
theorem B1819127 : Blo 1211423 1819127 := bstep (se 1 (by rfl) ⟨1364345, by rfl⟩ : syracuseStep 1819127 = 2728691) B2728691
theorem B6644227 : Blo 1211423 6644227 := bstep (se 1 (by rfl) ⟨4983170, by rfl⟩ : syracuseStep 6644227 = 9966341) B9966341
theorem B1212935 : Blo 1211423 1212935 := bstep (se 1 (by rfl) ⟨909701, by rfl⟩ : syracuseStep 1212935 = 1819403) B1819403
theorem B1942031 : Blo 1211423 1942031 := bstep (se 1 (by rfl) ⟨1456523, by rfl⟩ : syracuseStep 1942031 = 2913047) B2913047
theorem B2458127 : Blo 1211423 2458127 := bstep (se 1 (by rfl) ⟨1843595, by rfl⟩ : syracuseStep 2458127 = 3687191) B3687191
theorem B1819151 : Blo 1211423 1819151 := bstep (se 1 (by rfl) ⟨1364363, by rfl⟩ : syracuseStep 1819151 = 2728727) B2728727
theorem B1212943 : Blo 1211423 1212943 := bstep (se 1 (by rfl) ⟨909707, by rfl⟩ : syracuseStep 1212943 = 1819415) B1819415
theorem B1819193 : Blo 1211423 1819193 := bstep (se 2 (by rfl) ⟨682197, by rfl⟩ : syracuseStep 1819193 = 1364395) B1364395
theorem B3686971 : Blo 1211423 3686971 := bstep (se 1 (by rfl) ⟨2765228, by rfl⟩ : syracuseStep 3686971 = 5530457) B5530457
theorem B1212987 : Blo 1211423 1212987 := bstep (se 1 (by rfl) ⟨909740, by rfl⟩ : syracuseStep 1212987 = 1819481) B1819481
theorem B6906455 : Blo 1211423 6906455 := bstep (se 1 (by rfl) ⟨5179841, by rfl⟩ : syracuseStep 6906455 = 10359683) B10359683
theorem B2728583 : Blo 1211423 2728583 := bstep (se 1 (by rfl) ⟨2046437, by rfl⟩ : syracuseStep 2728583 = 4092875) B4092875
theorem B1819271 : Blo 1211423 1819271 := bstep (se 1 (by rfl) ⟨1364453, by rfl⟩ : syracuseStep 1819271 = 2728907) B2728907
theorem B1213063 : Blo 1211423 1213063 := bstep (se 1 (by rfl) ⟨909797, by rfl⟩ : syracuseStep 1213063 = 1819595) B1819595
theorem B1213071 : Blo 1211423 1213071 := bstep (se 1 (by rfl) ⟨909803, by rfl⟩ : syracuseStep 1213071 = 1819607) B1819607
theorem B1819307 : Blo 1211423 1819307 := bstep (se 1 (by rfl) ⟨1364480, by rfl⟩ : syracuseStep 1819307 = 2728961) B2728961
theorem B1213115 : Blo 1211423 1213115 := bstep (se 1 (by rfl) ⟨909836, by rfl⟩ : syracuseStep 1213115 = 1819673) B1819673
theorem B1819337 : Blo 1211423 1819337 := bstep (se 2 (by rfl) ⟨682251, by rfl⟩ : syracuseStep 1819337 = 1364503) B1364503
theorem B1213191 : Blo 1211423 1213191 := bstep (se 1 (by rfl) ⟨909893, by rfl⟩ : syracuseStep 1213191 = 1819787) B1819787
theorem B1213199 : Blo 1211423 1213199 := bstep (se 1 (by rfl) ⟨909899, by rfl⟩ : syracuseStep 1213199 = 1819799) B1819799
theorem B4088609 : Blo 1211423 4088609 := bstep (se 2 (by rfl) ⟨1533228, by rfl⟩ : syracuseStep 4088609 = 3066457) B3066457
theorem B4916027 : Blo 1211423 4916027 := bstep (se 1 (by rfl) ⟨3687020, by rfl⟩ : syracuseStep 4916027 = 7374041) B7374041
theorem B2728763 : Blo 1211423 2728763 := bstep (se 1 (by rfl) ⟨2046572, by rfl⟩ : syracuseStep 2728763 = 4093145) B4093145
theorem B1819451 : Blo 1211423 1819451 := bstep (se 1 (by rfl) ⟨1364588, by rfl⟩ : syracuseStep 1819451 = 2729177) B2729177
theorem B1213243 : Blo 1211423 1213243 := bstep (se 1 (by rfl) ⟨909932, by rfl⟩ : syracuseStep 1213243 = 1819865) B1819865
theorem B3449719 : Blo 1211423 3449719 := bstep (se 1 (by rfl) ⟨2587289, by rfl⟩ : syracuseStep 3449719 = 5174579) B5174579
theorem B1819511 : Blo 1211423 1819511 := bstep (se 1 (by rfl) ⟨1364633, by rfl⟩ : syracuseStep 1819511 = 2729267) B2729267
theorem B1213319 : Blo 1211423 1213319 := bstep (se 1 (by rfl) ⟨909989, by rfl⟩ : syracuseStep 1213319 = 1819979) B1819979
theorem B1819535 : Blo 1211423 1819535 := bstep (se 1 (by rfl) ⟨1364651, by rfl⟩ : syracuseStep 1819535 = 2729303) B2729303
theorem B1213327 : Blo 1211423 1213327 := bstep (se 1 (by rfl) ⟨909995, by rfl⟩ : syracuseStep 1213327 = 1819991) B1819991
theorem B6136721 : Blo 1211423 6136721 := bstep (se 2 (by rfl) ⟨2301270, by rfl⟩ : syracuseStep 6136721 = 4602541) B4602541
theorem B2728889 : Blo 1211423 2728889 := bstep (se 2 (by rfl) ⟨1023333, by rfl⟩ : syracuseStep 2728889 = 2046667) B2046667
theorem B1819577 : Blo 1211423 1819577 := bstep (se 2 (by rfl) ⟨682341, by rfl⟩ : syracuseStep 1819577 = 1364683) B1364683
theorem B1213371 : Blo 1211423 1213371 := bstep (se 1 (by rfl) ⟨910028, by rfl⟩ : syracuseStep 1213371 = 1820057) B1820057
theorem B1819655 : Blo 1211423 1819655 := bstep (se 1 (by rfl) ⟨1364741, by rfl⟩ : syracuseStep 1819655 = 2729483) B2729483
theorem B4604957 : Blo 1211423 4604957 := bstep (se 3 (by rfl) ⟨863429, by rfl⟩ : syracuseStep 4604957 = 1726859) B1726859
theorem B4604971 : Blo 1211423 4604971 := bstep (se 1 (by rfl) ⟨3453728, by rfl⟩ : syracuseStep 4604971 = 6907457) B6907457
theorem B1819691 : Blo 1211423 1819691 := bstep (se 1 (by rfl) ⟨1364768, by rfl⟩ : syracuseStep 1819691 = 2729537) B2729537
theorem B1819721 : Blo 1211423 1819721 := bstep (se 2 (by rfl) ⟨682395, by rfl⟩ : syracuseStep 1819721 = 1364791) B1364791
theorem B1819835 : Blo 1211423 1819835 := bstep (se 1 (by rfl) ⟨1364876, by rfl⟩ : syracuseStep 1819835 = 2729753) B2729753
theorem B1819895 : Blo 1211423 1819895 := bstep (se 1 (by rfl) ⟨1364921, by rfl⟩ : syracuseStep 1819895 = 2729843) B2729843
theorem B1295623 : Blo 1211423 1295623 := bstep (se 1 (by rfl) ⟨971717, by rfl⟩ : syracuseStep 1295623 = 1943435) B1943435
theorem B2729231 : Blo 1211423 2729231 := bstep (se 1 (by rfl) ⟨2046923, by rfl⟩ : syracuseStep 2729231 = 4093847) B4093847
theorem B1819919 : Blo 1211423 1819919 := bstep (se 1 (by rfl) ⟨1364939, by rfl⟩ : syracuseStep 1819919 = 2729879) B2729879
theorem B4916513 : Blo 1211423 4916513 := bstep (se 2 (by rfl) ⟨1843692, by rfl⟩ : syracuseStep 4916513 = 3687385) B3687385
theorem B2729249 : Blo 1211423 2729249 := bstep (se 2 (by rfl) ⟨1023468, by rfl⟩ : syracuseStep 2729249 = 2046937) B2046937
theorem B1819961 : Blo 1211423 1819961 := bstep (se 2 (by rfl) ⟨682485, by rfl⟩ : syracuseStep 1819961 = 1364971) B1364971
theorem B2303291 : Blo 1211423 2303291 := bstep (se 1 (by rfl) ⟨1727468, by rfl⟩ : syracuseStep 2303291 = 3454937) B3454937
theorem B4089203 : Blo 1211423 4089203 := bstep (se 1 (by rfl) ⟨3066902, by rfl⟩ : syracuseStep 4089203 = 6133805) B6133805
theorem B3278195 : Blo 1211423 3278195 := bstep (se 1 (by rfl) ⟨2458646, by rfl⟩ : syracuseStep 3278195 = 4917293) B4917293
theorem B1820039 : Blo 1211423 1820039 := bstep (se 1 (by rfl) ⟨1365029, by rfl⟩ : syracuseStep 1820039 = 2730059) B2730059
theorem B1820075 : Blo 1211423 1820075 := bstep (se 1 (by rfl) ⟨1365056, by rfl⟩ : syracuseStep 1820075 = 2730113) B2730113
theorem B1639865 : Blo 1211423 1639865 := bstep (se 2 (by rfl) ⟨614949, by rfl⟩ : syracuseStep 1639865 = 1229899) B1229899
theorem B1820105 : Blo 1211423 1820105 := bstep (se 2 (by rfl) ⟨682539, by rfl⟩ : syracuseStep 1820105 = 1365079) B1365079
theorem B1533431 : Blo 1211423 1533431 := bstep (se 1 (by rfl) ⟨1150073, by rfl⟩ : syracuseStep 1533431 = 2300147) B2300147
theorem B4916855 : Blo 1211423 4916855 := bstep (se 1 (by rfl) ⟨3687641, by rfl⟩ : syracuseStep 4916855 = 7375283) B7375283
theorem B2729591 : Blo 1211423 2729591 := bstep (se 1 (by rfl) ⟨2047193, by rfl⟩ : syracuseStep 2729591 = 4094387) B4094387
theorem B1533583 : Blo 1211423 1533583 := bstep (se 1 (by rfl) ⟨1150187, by rfl⟩ : syracuseStep 1533583 = 2300375) B2300375
theorem B11052737 : Blo 1211423 11052737 := bstep (se 2 (by rfl) ⟨4144776, by rfl⟩ : syracuseStep 11052737 = 8289553) B8289553
theorem B5826305 : Blo 1211423 5826305 := bstep (se 2 (by rfl) ⟨2184864, by rfl⟩ : syracuseStep 5826305 = 4369729) B4369729
theorem B14755621 : Blo 1211423 14755621 := bstep (se 4 (by rfl) ⟨1383339, by rfl⟩ : syracuseStep 14755621 = 2766679) B2766679
theorem B2729771 : Blo 1211423 2729771 := bstep (se 1 (by rfl) ⟨2047328, by rfl⟩ : syracuseStep 2729771 = 4094657) B4094657
theorem B1533755 : Blo 1211423 1533755 := bstep (se 1 (by rfl) ⟨1150316, by rfl⟩ : syracuseStep 1533755 = 2300633) B2300633
theorem B6997819 : Blo 1211423 6997819 := bstep (se 1 (by rfl) ⟨5248364, by rfl⟩ : syracuseStep 6997819 = 10496729) B10496729
theorem B26920907 : Blo 1211423 26920907 := bstep (se 1 (by rfl) ⟨20190680, by rfl⟩ : syracuseStep 26920907 = 40381361) B40381361
theorem B9824267 : Blo 1211423 9824267 := bstep (se 1 (by rfl) ⟨7368200, by rfl⟩ : syracuseStep 9824267 = 14736401) B14736401
theorem B13101101 : Blo 1211423 13101101 := bstep (se 3 (by rfl) ⟨2456456, by rfl⟩ : syracuseStep 13101101 = 4912913) B4912913
theorem B3450995 : Blo 1211423 3450995 := bstep (se 1 (by rfl) ⟨2588246, by rfl⟩ : syracuseStep 3450995 = 5176493) B5176493
theorem B1943671 : Blo 1211423 1943671 := bstep (se 1 (by rfl) ⟨1457753, by rfl⟩ : syracuseStep 1943671 = 2915507) B2915507
theorem B2730131 : Blo 1211423 2730131 := bstep (se 1 (by rfl) ⟨2047598, by rfl⟩ : syracuseStep 2730131 = 4095197) B4095197
theorem B23300297 : Blo 1211423 23300297 := bstep (se 2 (by rfl) ⟨8737611, by rfl⟩ : syracuseStep 23300297 = 17475223) B17475223
theorem B2074825 : Blo 1211423 2074825 := bstep (se 2 (by rfl) ⟨778059, by rfl⟩ : syracuseStep 2074825 = 1556119) B1556119
theorem B2730185 : Blo 1211423 2730185 := bstep (se 2 (by rfl) ⟨1023819, by rfl⟩ : syracuseStep 2730185 = 2047639) B2047639
theorem B3451223 : Blo 1211423 3451223 := bstep (se 1 (by rfl) ⟨2588417, by rfl⟩ : syracuseStep 3451223 = 5176835) B5176835
theorem B22432241 : Blo 1211423 22432241 := bstep (se 2 (by rfl) ⟨8412090, by rfl⟩ : syracuseStep 22432241 = 16824181) B16824181
theorem B2910779 : Blo 1211423 2910779 := bstep (se 1 (by rfl) ⟨2183084, by rfl⟩ : syracuseStep 2910779 = 4366169) B4366169
theorem B20728385 : Blo 1211423 20728385 := bstep (se 2 (by rfl) ⟨7773144, by rfl⟩ : syracuseStep 20728385 = 15546289) B15546289
theorem B3066569 : Blo 1211423 3066569 := bstep (se 2 (by rfl) ⟨1149963, by rfl⟩ : syracuseStep 3066569 = 2299927) B2299927
theorem B1534727 : Blo 1211423 1534727 := bstep (se 1 (by rfl) ⟨1151045, by rfl⟩ : syracuseStep 1534727 = 2302091) B2302091
theorem B5180219 : Blo 1211423 5180219 := bstep (se 1 (by rfl) ⟨3885164, by rfl⟩ : syracuseStep 5180219 = 7770329) B7770329
theorem B6138827 : Blo 1211423 6138827 := bstep (se 1 (by rfl) ⟨4604120, by rfl⟩ : syracuseStep 6138827 = 9208241) B9208241
theorem B8293387 : Blo 1211423 8293387 := bstep (se 1 (by rfl) ⟨6220040, by rfl⟩ : syracuseStep 8293387 = 12440081) B12440081
theorem B4918283 : Blo 1211423 4918283 := bstep (se 1 (by rfl) ⟨3688712, by rfl⟩ : syracuseStep 4918283 = 7377425) B7377425
theorem B11676695 : Blo 1211423 11676695 := bstep (se 1 (by rfl) ⟨8757521, by rfl⟩ : syracuseStep 11676695 = 17515043) B17515043
theorem B3066923 : Blo 1211423 3066923 := bstep (se 1 (by rfl) ⟨2300192, by rfl⟩ : syracuseStep 3066923 = 4600385) B4600385
theorem B1363207 : Blo 1211423 1363207 := bstep (se 1 (by rfl) ⟨1022405, by rfl⟩ : syracuseStep 1363207 = 2044811) B2044811
theorem B6139151 : Blo 1211423 6139151 := bstep (se 1 (by rfl) ⟨4604363, by rfl⟩ : syracuseStep 6139151 = 9208727) B9208727
theorem B2911547 : Blo 1211423 2911547 := bstep (se 1 (by rfl) ⟨2183660, by rfl⟩ : syracuseStep 2911547 = 4367321) B4367321
theorem B1535375 : Blo 1211423 1535375 := bstep (se 1 (by rfl) ⟨1151531, by rfl⟩ : syracuseStep 1535375 = 2303063) B2303063
theorem B1363387 : Blo 1211423 1363387 := bstep (se 1 (by rfl) ⟨1022540, by rfl⟩ : syracuseStep 1363387 = 2045081) B2045081
theorem B7876061 : Blo 1211423 7876061 := bstep (se 3 (by rfl) ⟨1476761, by rfl⟩ : syracuseStep 7876061 = 2953523) B2953523
theorem B6557207 : Blo 1211423 6557207 := bstep (se 1 (by rfl) ⟨4917905, by rfl⟩ : syracuseStep 6557207 = 9835811) B9835811
theorem B3108439 : Blo 1211423 3108439 := bstep (se 1 (by rfl) ⟨2331329, by rfl⟩ : syracuseStep 3108439 = 4662659) B4662659
theorem B7376471 : Blo 1211423 7376471 := bstep (se 1 (by rfl) ⟨5532353, by rfl⟩ : syracuseStep 7376471 = 11064707) B11064707
theorem B3452807 : Blo 1211423 3452807 := bstep (se 1 (by rfl) ⟨2589605, by rfl⟩ : syracuseStep 3452807 = 5179211) B5179211
theorem B1363855 : Blo 1211423 1363855 := bstep (se 1 (by rfl) ⟨1022891, by rfl⟩ : syracuseStep 1363855 = 2045783) B2045783
theorem B4091795 : Blo 1211423 4091795 := bstep (se 1 (by rfl) ⟨3068846, by rfl⟩ : syracuseStep 4091795 = 6137693) B6137693
theorem B3067915 : Blo 1211423 3067915 := bstep (se 1 (by rfl) ⟨2300936, by rfl⟩ : syracuseStep 3067915 = 4601873) B4601873
theorem B13111307 : Blo 1211423 13111307 := bstep (se 1 (by rfl) ⟨9833480, by rfl⟩ : syracuseStep 13111307 = 19666961) B19666961
theorem B1347643 : Blo 1211423 1347643 := bstep (se 1 (by rfl) ⟨1010732, by rfl⟩ : syracuseStep 1347643 = 2021465) B2021465
theorem B3452989 : Blo 1211423 3452989 := bstep (se 3 (by rfl) ⟨647435, by rfl⟩ : syracuseStep 3452989 = 1294871) B1294871
theorem B3068057 : Blo 1211423 3068057 := bstep (se 2 (by rfl) ⟨1150521, by rfl⟩ : syracuseStep 3068057 = 2301043) B2301043
theorem B4600097 : Blo 1211423 4600097 := bstep (se 2 (by rfl) ⟨1725036, by rfl⟩ : syracuseStep 4600097 = 3450073) B3450073
theorem B3068219 : Blo 1211423 3068219 := bstep (se 1 (by rfl) ⟨2301164, by rfl⟩ : syracuseStep 3068219 = 4602329) B4602329
theorem B1364359 : Blo 1211423 1364359 := bstep (se 1 (by rfl) ⟨1023269, by rfl⟩ : syracuseStep 1364359 = 2046539) B2046539
theorem B2044345 : Blo 1211423 2044345 := bstep (se 2 (by rfl) ⟨766629, by rfl⟩ : syracuseStep 2044345 = 1533259) B1533259
theorem B1749433 : Blo 1211423 1749433 := bstep (se 2 (by rfl) ⟨656037, by rfl⟩ : syracuseStep 1749433 = 1312075) B1312075
theorem B3109321 : Blo 1211423 3109321 := bstep (se 2 (by rfl) ⟨1165995, by rfl⟩ : syracuseStep 3109321 = 2331991) B2331991
theorem B3453455 : Blo 1211423 3453455 := bstep (se 1 (by rfl) ⟨2590091, by rfl⟩ : syracuseStep 3453455 = 5180183) B5180183
theorem B5181995 : Blo 1211423 5181995 := bstep (se 1 (by rfl) ⟨3886496, by rfl⟩ : syracuseStep 5181995 = 7772993) B7772993
theorem B1364539 : Blo 1211423 1364539 := bstep (se 1 (by rfl) ⟨1023404, by rfl⟩ : syracuseStep 1364539 = 2046809) B2046809
theorem B6902333 : Blo 1211423 6902333 := bstep (se 3 (by rfl) ⟨1294187, by rfl⟩ : syracuseStep 6902333 = 2588375) B2588375
theorem B13103693 : Blo 1211423 13103693 := bstep (se 3 (by rfl) ⟨2456942, by rfl⟩ : syracuseStep 13103693 = 4913885) B4913885
theorem B3068563 : Blo 1211423 3068563 := bstep (se 1 (by rfl) ⟨2301422, by rfl⟩ : syracuseStep 3068563 = 4602845) B4602845
theorem B2626195 : Blo 1211423 2626195 := bstep (se 1 (by rfl) ⟨1969646, by rfl⟩ : syracuseStep 2626195 = 3939293) B3939293
theorem B1577659 : Blo 1211423 1577659 := bstep (se 1 (by rfl) ⟨1183244, by rfl⟩ : syracuseStep 1577659 = 2366489) B2366489
theorem B6140609 : Blo 1211423 6140609 := bstep (se 2 (by rfl) ⟨2302728, by rfl⟩ : syracuseStep 6140609 = 4605457) B4605457
theorem B7377637 : Blo 1211423 7377637 := bstep (se 4 (by rfl) ⟨691653, by rfl⟩ : syracuseStep 7377637 = 1383307) B1383307
theorem B3068705 : Blo 1211423 3068705 := bstep (se 2 (by rfl) ⟨1150764, by rfl⟩ : syracuseStep 3068705 = 2301529) B2301529
theorem B5526407 : Blo 1211423 5526407 := bstep (se 1 (by rfl) ⟨4144805, by rfl⟩ : syracuseStep 5526407 = 8289611) B8289611
theorem B11645957 : Blo 1211423 11645957 := bstep (se 4 (by rfl) ⟨1091808, by rfl⟩ : syracuseStep 11645957 = 2183617) B2183617
theorem B1365007 : Blo 1211423 1365007 := bstep (se 1 (by rfl) ⟨1023755, by rfl⟩ : syracuseStep 1365007 = 2047511) B2047511
theorem B2045047 : Blo 1211423 2045047 := bstep (se 1 (by rfl) ⟨1533785, by rfl⟩ : syracuseStep 2045047 = 3067571) B3067571
theorem B9213101 : Blo 1211423 9213101 := bstep (se 3 (by rfl) ⟨1727456, by rfl⟩ : syracuseStep 9213101 = 3454913) B3454913
theorem B4601069 : Blo 1211423 4601069 := bstep (se 3 (by rfl) ⟨862700, by rfl⟩ : syracuseStep 4601069 = 1725401) B1725401
theorem B4093199 : Blo 1211423 4093199 := bstep (se 1 (by rfl) ⟨3069899, by rfl⟩ : syracuseStep 4093199 = 6139799) B6139799
theorem B2045243 : Blo 1211423 2045243 := bstep (se 1 (by rfl) ⟨1533932, by rfl⟩ : syracuseStep 2045243 = 3067865) B3067865
theorem B2184583 : Blo 1211423 2184583 := bstep (se 1 (by rfl) ⟨1638437, by rfl⟩ : syracuseStep 2184583 = 3276875) B3276875
theorem B34952633 : Blo 1211423 34952633 := bstep (se 2 (by rfl) ⟨13107237, by rfl⟩ : syracuseStep 34952633 = 26214475) B26214475
theorem B36410809 : Blo 1211423 36410809 := bstep (se 2 (by rfl) ⟨13654053, by rfl⟩ : syracuseStep 36410809 = 27308107) B27308107
theorem B1750519 : Blo 1211423 1750519 := bstep (se 1 (by rfl) ⟨1312889, by rfl⟩ : syracuseStep 1750519 = 2625779) B2625779
theorem B7763485 : Blo 1211423 7763485 := bstep (se 3 (by rfl) ⟨1455653, by rfl⟩ : syracuseStep 7763485 = 2911307) B2911307
theorem B8295965 : Blo 1211423 8295965 := bstep (se 3 (by rfl) ⟨1555493, by rfl⟩ : syracuseStep 8295965 = 3110987) B3110987
theorem B4093469 : Blo 1211423 4093469 := bstep (se 3 (by rfl) ⟨767525, by rfl⟩ : syracuseStep 4093469 = 1535051) B1535051
theorem B4601387 : Blo 1211423 4601387 := bstep (se 1 (by rfl) ⟨3451040, by rfl⟩ : syracuseStep 4601387 = 6902081) B6902081
theorem B9205325 : Blo 1211423 9205325 := bstep (se 3 (by rfl) ⟨1725998, by rfl⟩ : syracuseStep 9205325 = 3451997) B3451997
theorem B2332361 : Blo 1211423 2332361 := bstep (se 2 (by rfl) ⟨874635, by rfl⟩ : syracuseStep 2332361 = 1749271) B1749271
theorem B2045641 : Blo 1211423 2045641 := bstep (se 2 (by rfl) ⟨767115, by rfl⟩ : syracuseStep 2045641 = 1534231) B1534231
theorem B3069697 : Blo 1211423 3069697 := bstep (se 2 (by rfl) ⟨1151136, by rfl⟩ : syracuseStep 3069697 = 2302273) B2302273
theorem B3454721 : Blo 1211423 3454721 := bstep (se 2 (by rfl) ⟨1295520, by rfl⟩ : syracuseStep 3454721 = 2591041) B2591041
theorem B1726267 : Blo 1211423 1726267 := bstep (se 1 (by rfl) ⟨1294700, by rfl⟩ : syracuseStep 1726267 = 2589401) B2589401
theorem B6141905 : Blo 1211423 6141905 := bstep (se 2 (by rfl) ⟨2303214, by rfl⟩ : syracuseStep 6141905 = 4606429) B4606429
theorem B6559805 : Blo 1211423 6559805 := bstep (se 3 (by rfl) ⟨1229963, by rfl⟩ : syracuseStep 6559805 = 2459927) B2459927
theorem B1456427 : Blo 1211423 1456427 := bstep (se 1 (by rfl) ⟨1092320, by rfl⟩ : syracuseStep 1456427 = 2184641) B2184641
theorem B3070295 : Blo 1211423 3070295 := bstep (se 1 (by rfl) ⟨2302721, by rfl⟩ : syracuseStep 3070295 = 4605443) B4605443
theorem B10492295 : Blo 1211423 10492295 := bstep (se 1 (by rfl) ⟨7869221, by rfl⟩ : syracuseStep 10492295 = 15738443) B15738443
theorem B2726279 : Blo 1211423 2726279 := bstep (se 1 (by rfl) ⟨2044709, by rfl⟩ : syracuseStep 2726279 = 4089419) B4089419
theorem B2046343 : Blo 1211423 2046343 := bstep (se 1 (by rfl) ⟨1534757, by rfl⟩ : syracuseStep 2046343 = 3069515) B3069515
theorem B1726967 : Blo 1211423 1726967 := bstep (se 1 (by rfl) ⟨1295225, by rfl⟩ : syracuseStep 1726967 = 2590451) B2590451
theorem B3070507 : Blo 1211423 3070507 := bstep (se 1 (by rfl) ⟨2302880, by rfl⟩ : syracuseStep 3070507 = 4605761) B4605761
theorem B1817147 : Blo 1211423 1817147 := bstep (se 1 (by rfl) ⟨1362860, by rfl⟩ : syracuseStep 1817147 = 2725721) B2725721
theorem B2726459 : Blo 1211423 2726459 := bstep (se 1 (by rfl) ⟨2044844, by rfl⟩ : syracuseStep 2726459 = 4089689) B4089689
theorem B1817207 : Blo 1211423 1817207 := bstep (se 1 (by rfl) ⟨1362905, by rfl⟩ : syracuseStep 1817207 = 2725811) B2725811
theorem B1817231 : Blo 1211423 1817231 := bstep (se 1 (by rfl) ⟨1362923, by rfl⟩ : syracuseStep 1817231 = 2725847) B2725847
theorem B3324563 : Blo 1211423 3324563 := bstep (se 1 (by rfl) ⟨2493422, by rfl⟩ : syracuseStep 3324563 = 4986845) B4986845
theorem B1817273 : Blo 1211423 1817273 := bstep (se 2 (by rfl) ⟨681477, by rfl⟩ : syracuseStep 1817273 = 1362955) B1362955
theorem B2726585 : Blo 1211423 2726585 := bstep (se 2 (by rfl) ⟨1022469, by rfl⟩ : syracuseStep 2726585 = 2044939) B2044939
theorem B3070649 : Blo 1211423 3070649 := bstep (se 2 (by rfl) ⟨1151493, by rfl⟩ : syracuseStep 3070649 = 2302987) B2302987
theorem B1817351 : Blo 1211423 1817351 := bstep (se 1 (by rfl) ⟨1363013, by rfl⟩ : syracuseStep 1817351 = 2726027) B2726027
theorem B5823247 : Blo 1211423 5823247 := bstep (se 1 (by rfl) ⟨4367435, by rfl⟩ : syracuseStep 5823247 = 8734871) B8734871
theorem B17488655 : Blo 1211423 17488655 := bstep (se 1 (by rfl) ⟨13116491, by rfl⟩ : syracuseStep 17488655 = 26232983) B26232983
theorem B1817387 : Blo 1211423 1817387 := bstep (se 1 (by rfl) ⟨1363040, by rfl⟩ : syracuseStep 1817387 = 2726081) B2726081
theorem B1817417 : Blo 1211423 1817417 := bstep (se 2 (by rfl) ⟨681531, by rfl⟩ : syracuseStep 1817417 = 1363063) B1363063
theorem B7773043 : Blo 1211423 7773043 := bstep (se 1 (by rfl) ⟨5829782, by rfl⟩ : syracuseStep 7773043 = 11659565) B11659565
theorem B6904723 : Blo 1211423 6904723 := bstep (se 1 (by rfl) ⟨5178542, by rfl⟩ : syracuseStep 6904723 = 10357085) B10357085
theorem B4094873 : Blo 1211423 4094873 := bstep (se 2 (by rfl) ⟨1535577, by rfl⟩ : syracuseStep 4094873 = 3071155) B3071155
theorem B1817531 : Blo 1211423 1817531 := bstep (se 1 (by rfl) ⟨1363148, by rfl⟩ : syracuseStep 1817531 = 2726297) B2726297
theorem B1817591 : Blo 1211423 1817591 := bstep (se 1 (by rfl) ⟨1363193, by rfl⟩ : syracuseStep 1817591 = 2726387) B2726387
theorem B1817615 : Blo 1211423 1817615 := bstep (se 1 (by rfl) ⟨1363211, by rfl⟩ : syracuseStep 1817615 = 2726423) B2726423
theorem B2726927 : Blo 1211423 2726927 := bstep (se 1 (by rfl) ⟨2045195, by rfl⟩ : syracuseStep 2726927 = 4090391) B4090391
theorem B2046991 : Blo 1211423 2046991 := bstep (se 1 (by rfl) ⟨1535243, by rfl⟩ : syracuseStep 2046991 = 3070487) B3070487
theorem B2726945 : Blo 1211423 2726945 := bstep (se 2 (by rfl) ⟨1022604, by rfl⟩ : syracuseStep 2726945 = 2045209) B2045209
theorem B1817657 : Blo 1211423 1817657 := bstep (se 2 (by rfl) ⟨681621, by rfl⟩ : syracuseStep 1817657 = 1363243) B1363243
theorem B1211451 : Blo 1211423 1211451 := bstep (se 1 (by rfl) ⟨908588, by rfl⟩ : syracuseStep 1211451 = 1817177) B1817177
theorem B1211527 : Blo 1211423 1211527 := bstep (se 1 (by rfl) ⟨908645, by rfl⟩ : syracuseStep 1211527 = 1817291) B1817291
theorem B1817735 : Blo 1211423 1817735 := bstep (se 1 (by rfl) ⟨1363301, by rfl⟩ : syracuseStep 1817735 = 2726603) B2726603
theorem B1211535 : Blo 1211423 1211535 := bstep (se 1 (by rfl) ⟨908651, by rfl⟩ : syracuseStep 1211535 = 1817303) B1817303
theorem B1817771 : Blo 1211423 1817771 := bstep (se 1 (by rfl) ⟨1363328, by rfl⟩ : syracuseStep 1817771 = 2726657) B2726657
theorem B1211579 : Blo 1211423 1211579 := bstep (se 1 (by rfl) ⟨908684, by rfl⟩ : syracuseStep 1211579 = 1817369) B1817369
theorem B1817801 : Blo 1211423 1817801 := bstep (se 2 (by rfl) ⟨681675, by rfl⟩ : syracuseStep 1817801 = 1363351) B1363351
theorem B1211655 : Blo 1211423 1211655 := bstep (se 1 (by rfl) ⟨908741, by rfl⟩ : syracuseStep 1211655 = 1817483) B1817483
theorem B1211663 : Blo 1211423 1211663 := bstep (se 1 (by rfl) ⟨908747, by rfl⟩ : syracuseStep 1211663 = 1817495) B1817495
theorem B3497249 : Blo 1211423 3497249 := bstep (se 2 (by rfl) ⟨1311468, by rfl⟩ : syracuseStep 3497249 = 2622937) B2622937
theorem B1211707 : Blo 1211423 1211707 := bstep (se 1 (by rfl) ⟨908780, by rfl⟩ : syracuseStep 1211707 = 1817561) B1817561
theorem B1817915 : Blo 1211423 1817915 := bstep (se 1 (by rfl) ⟨1363436, by rfl⟩ : syracuseStep 1817915 = 2726873) B2726873
theorem B3276119 : Blo 1211423 3276119 := bstep (se 1 (by rfl) ⟨2457089, by rfl⟩ : syracuseStep 3276119 = 4914179) B4914179
theorem B1817975 : Blo 1211423 1817975 := bstep (se 1 (by rfl) ⟨1363481, by rfl⟩ : syracuseStep 1817975 = 2726963) B2726963
theorem B2727287 : Blo 1211423 2727287 := bstep (se 1 (by rfl) ⟨2045465, by rfl⟩ : syracuseStep 2727287 = 4090931) B4090931
theorem B1211783 : Blo 1211423 1211783 := bstep (se 1 (by rfl) ⟨908837, by rfl⟩ : syracuseStep 1211783 = 1817675) B1817675
theorem B1211791 : Blo 1211423 1211791 := bstep (se 1 (by rfl) ⟨908843, by rfl⟩ : syracuseStep 1211791 = 1817687) B1817687
theorem B1817999 : Blo 1211423 1817999 := bstep (se 1 (by rfl) ⟨1363499, by rfl⟩ : syracuseStep 1817999 = 2726999) B2726999
theorem B1818041 : Blo 1211423 1818041 := bstep (se 2 (by rfl) ⟨681765, by rfl⟩ : syracuseStep 1818041 = 1363531) B1363531
theorem B1211835 : Blo 1211423 1211835 := bstep (se 1 (by rfl) ⟨908876, by rfl⟩ : syracuseStep 1211835 = 1817753) B1817753
theorem B2301385 : Blo 1211423 2301385 := bstep (se 2 (by rfl) ⟨863019, by rfl⟩ : syracuseStep 2301385 = 1726039) B1726039
theorem B1211911 : Blo 1211423 1211911 := bstep (se 1 (by rfl) ⟨908933, by rfl⟩ : syracuseStep 1211911 = 1817867) B1817867
theorem B1818119 : Blo 1211423 1818119 := bstep (se 1 (by rfl) ⟨1363589, by rfl⟩ : syracuseStep 1818119 = 2727179) B2727179
theorem B1211919 : Blo 1211423 1211919 := bstep (se 1 (by rfl) ⟨908939, by rfl⟩ : syracuseStep 1211919 = 1817879) B1817879
theorem B2727467 : Blo 1211423 2727467 := bstep (se 1 (by rfl) ⟨2045600, by rfl⟩ : syracuseStep 2727467 = 4091201) B4091201
theorem B1818155 : Blo 1211423 1818155 := bstep (se 1 (by rfl) ⟨1363616, by rfl⟩ : syracuseStep 1818155 = 2727233) B2727233
theorem B5529131 : Blo 1211423 5529131 := bstep (se 1 (by rfl) ⟨4146848, by rfl⟩ : syracuseStep 5529131 = 8293697) B8293697
theorem B2047531 : Blo 1211423 2047531 := bstep (se 1 (by rfl) ⟨1535648, by rfl⟩ : syracuseStep 2047531 = 3071297) B3071297
theorem B1211963 : Blo 1211423 1211963 := bstep (se 1 (by rfl) ⟨908972, by rfl⟩ : syracuseStep 1211963 = 1817945) B1817945
theorem B1818185 : Blo 1211423 1818185 := bstep (se 2 (by rfl) ⟨681819, by rfl⟩ : syracuseStep 1818185 = 1363639) B1363639
theorem B1212039 : Blo 1211423 1212039 := bstep (se 1 (by rfl) ⟨909029, by rfl⟩ : syracuseStep 1212039 = 1818059) B1818059
theorem B1212047 : Blo 1211423 1212047 := bstep (se 1 (by rfl) ⟨909035, by rfl⟩ : syracuseStep 1212047 = 1818071) B1818071
theorem B1212091 : Blo 1211423 1212091 := bstep (se 1 (by rfl) ⟨909068, by rfl⟩ : syracuseStep 1212091 = 1818137) B1818137
theorem B1818299 : Blo 1211423 1818299 := bstep (se 1 (by rfl) ⟨1363724, by rfl⟩ : syracuseStep 1818299 = 2727449) B2727449
theorem B1818359 : Blo 1211423 1818359 := bstep (se 1 (by rfl) ⟨1363769, by rfl⟩ : syracuseStep 1818359 = 2727539) B2727539
theorem B1212167 : Blo 1211423 1212167 := bstep (se 1 (by rfl) ⟨909125, by rfl⟩ : syracuseStep 1212167 = 1818251) B1818251
theorem B1212175 : Blo 1211423 1212175 := bstep (se 1 (by rfl) ⟨909131, by rfl⟩ : syracuseStep 1212175 = 1818263) B1818263
theorem B1818383 : Blo 1211423 1818383 := bstep (se 1 (by rfl) ⟨1363787, by rfl⟩ : syracuseStep 1818383 = 2727575) B2727575
theorem B1818425 : Blo 1211423 1818425 := bstep (se 2 (by rfl) ⟨681909, by rfl⟩ : syracuseStep 1818425 = 1363819) B1363819
theorem B1212219 : Blo 1211423 1212219 := bstep (se 1 (by rfl) ⟨909164, by rfl⟩ : syracuseStep 1212219 = 1818329) B1818329
theorem B1212295 : Blo 1211423 1212295 := bstep (se 1 (by rfl) ⟨909221, by rfl⟩ : syracuseStep 1212295 = 1818443) B1818443
theorem B1818503 : Blo 1211423 1818503 := bstep (se 1 (by rfl) ⟨1363877, by rfl⟩ : syracuseStep 1818503 = 2727755) B2727755
theorem B1212303 : Blo 1211423 1212303 := bstep (se 1 (by rfl) ⟨909227, by rfl⟩ : syracuseStep 1212303 = 1818455) B1818455
theorem B2727827 : Blo 1211423 2727827 := bstep (se 1 (by rfl) ⟨2045870, by rfl⟩ : syracuseStep 2727827 = 4091741) B4091741
theorem B1818539 : Blo 1211423 1818539 := bstep (se 1 (by rfl) ⟨1363904, by rfl⟩ : syracuseStep 1818539 = 2727809) B2727809
theorem B1212347 : Blo 1211423 1212347 := bstep (se 1 (by rfl) ⟨909260, by rfl⟩ : syracuseStep 1212347 = 1818521) B1818521
theorem B1818569 : Blo 1211423 1818569 := bstep (se 2 (by rfl) ⟨681963, by rfl⟩ : syracuseStep 1818569 = 1363927) B1363927
theorem B2727881 : Blo 1211423 2727881 := bstep (se 2 (by rfl) ⟨1022955, by rfl⟩ : syracuseStep 2727881 = 2045911) B2045911
theorem B9207755 : Blo 1211423 9207755 := bstep (se 1 (by rfl) ⟨6905816, by rfl⟩ : syracuseStep 9207755 = 13811633) B13811633
theorem B5177297 : Blo 1211423 5177297 := bstep (se 2 (by rfl) ⟨1941486, by rfl⟩ : syracuseStep 5177297 = 3882973) B3882973
theorem B5824477 : Blo 1211423 5824477 := bstep (se 3 (by rfl) ⟨1092089, by rfl⟩ : syracuseStep 5824477 = 2184179) B2184179
theorem B8740871 : Blo 1211423 8740871 := bstep (se 1 (by rfl) ⟨6555653, by rfl⟩ : syracuseStep 8740871 = 13111307) B13111307
theorem B1212455 : Blo 1211423 1212455 := bstep (se 1 (by rfl) ⟨909341, by rfl⟩ : syracuseStep 1212455 = 1818683) B1818683
theorem B31137853 : Blo 1211423 31137853 := bstep (se 3 (by rfl) ⟨5838347, by rfl⟩ : syracuseStep 31137853 = 11676695) B11676695
theorem B3883087 : Blo 1211423 3883087 := bstep (se 1 (by rfl) ⟨2912315, by rfl⟩ : syracuseStep 3883087 = 5824631) B5824631
theorem B1212495 : Blo 1211423 1212495 := bstep (se 1 (by rfl) ⟨909371, by rfl⟩ : syracuseStep 1212495 = 1818743) B1818743
theorem B4603985 : Blo 1211423 4603985 := bstep (se 2 (by rfl) ⟨1726494, by rfl⟩ : syracuseStep 4603985 = 3452989) B3452989
theorem B1212511 : Blo 1211423 1212511 := bstep (se 1 (by rfl) ⟨909383, by rfl⟩ : syracuseStep 1212511 = 1818767) B1818767
theorem B1212539 : Blo 1211423 1212539 := bstep (se 1 (by rfl) ⟨909404, by rfl⟩ : syracuseStep 1212539 = 1818809) B1818809
theorem B1212591 : Blo 1211423 1212591 := bstep (se 1 (by rfl) ⟨909443, by rfl⟩ : syracuseStep 1212591 = 1818887) B1818887
theorem B1212615 : Blo 1211423 1212615 := bstep (se 1 (by rfl) ⟨909461, by rfl⟩ : syracuseStep 1212615 = 1818923) B1818923
theorem B1212635 : Blo 1211423 1212635 := bstep (se 1 (by rfl) ⟨909476, by rfl⟩ : syracuseStep 1212635 = 1818953) B1818953
theorem B1212711 : Blo 1211423 1212711 := bstep (se 1 (by rfl) ⟨909533, by rfl⟩ : syracuseStep 1212711 = 1819067) B1819067
theorem B1212751 : Blo 1211423 1212751 := bstep (se 1 (by rfl) ⟨909563, by rfl⟩ : syracuseStep 1212751 = 1819127) B1819127
theorem B1294687 : Blo 1211423 1294687 := bstep (se 1 (by rfl) ⟨971015, by rfl⟩ : syracuseStep 1294687 = 1942031) B1942031
theorem B1212767 : Blo 1211423 1212767 := bstep (se 1 (by rfl) ⟨909575, by rfl⟩ : syracuseStep 1212767 = 1819151) B1819151
theorem B1212795 : Blo 1211423 1212795 := bstep (se 1 (by rfl) ⟨909596, by rfl⟩ : syracuseStep 1212795 = 1819193) B1819193
theorem B4604303 : Blo 1211423 4604303 := bstep (se 1 (by rfl) ⟨3453227, by rfl⟩ : syracuseStep 4604303 = 6906455) B6906455
theorem B1819055 : Blo 1211423 1819055 := bstep (se 1 (by rfl) ⟨1364291, by rfl⟩ : syracuseStep 1819055 = 2728583) B2728583
theorem B1212847 : Blo 1211423 1212847 := bstep (se 1 (by rfl) ⟨909635, by rfl⟩ : syracuseStep 1212847 = 1819271) B1819271
theorem B1212871 : Blo 1211423 1212871 := bstep (se 1 (by rfl) ⟨909653, by rfl⟩ : syracuseStep 1212871 = 1819307) B1819307
theorem B18678221 : Blo 1211423 18678221 := bstep (se 3 (by rfl) ⟨3502166, by rfl⟩ : syracuseStep 18678221 = 7004333) B7004333
theorem B1212891 : Blo 1211423 1212891 := bstep (se 1 (by rfl) ⟨909668, by rfl⟩ : syracuseStep 1212891 = 1819337) B1819337
theorem B2728457 : Blo 1211423 2728457 := bstep (se 2 (by rfl) ⟨1023171, by rfl⟩ : syracuseStep 2728457 = 2046343) B2046343
theorem B1819145 : Blo 1211423 1819145 := bstep (se 2 (by rfl) ⟨682179, by rfl⟩ : syracuseStep 1819145 = 1364359) B1364359
theorem B3277351 : Blo 1211423 3277351 := bstep (se 1 (by rfl) ⟨2458013, by rfl⟩ : syracuseStep 3277351 = 4916027) B4916027
theorem B1819175 : Blo 1211423 1819175 := bstep (se 1 (by rfl) ⟨1364381, by rfl⟩ : syracuseStep 1819175 = 2728763) B2728763
theorem B1212967 : Blo 1211423 1212967 := bstep (se 1 (by rfl) ⟨909725, by rfl⟩ : syracuseStep 1212967 = 1819451) B1819451
theorem B1213007 : Blo 1211423 1213007 := bstep (se 1 (by rfl) ⟨909755, by rfl⟩ : syracuseStep 1213007 = 1819511) B1819511
theorem B1213023 : Blo 1211423 1213023 := bstep (se 1 (by rfl) ⟨909767, by rfl⟩ : syracuseStep 1213023 = 1819535) B1819535
theorem B4145761 : Blo 1211423 4145761 := bstep (se 2 (by rfl) ⟨1554660, by rfl⟩ : syracuseStep 4145761 = 3109321) B3109321
theorem B1819259 : Blo 1211423 1819259 := bstep (se 1 (by rfl) ⟨1364444, by rfl⟩ : syracuseStep 1819259 = 2728889) B2728889
theorem B1213051 : Blo 1211423 1213051 := bstep (se 1 (by rfl) ⟨909788, by rfl⟩ : syracuseStep 1213051 = 1819577) B1819577
theorem B1213103 : Blo 1211423 1213103 := bstep (se 1 (by rfl) ⟨909827, by rfl⟩ : syracuseStep 1213103 = 1819655) B1819655
theorem B1213127 : Blo 1211423 1213127 := bstep (se 1 (by rfl) ⟨909845, by rfl⟩ : syracuseStep 1213127 = 1819691) B1819691
theorem B1213147 : Blo 1211423 1213147 := bstep (se 1 (by rfl) ⟨909860, by rfl⟩ : syracuseStep 1213147 = 1819721) B1819721
theorem B4915961 : Blo 1211423 4915961 := bstep (se 2 (by rfl) ⟨1843485, by rfl⟩ : syracuseStep 4915961 = 3686971) B3686971
theorem B1819385 : Blo 1211423 1819385 := bstep (se 2 (by rfl) ⟨682269, by rfl⟩ : syracuseStep 1819385 = 1364539) B1364539
theorem B3883805 : Blo 1211423 3883805 := bstep (se 3 (by rfl) ⟨728213, by rfl⟩ : syracuseStep 3883805 = 1456427) B1456427
theorem B1213223 : Blo 1211423 1213223 := bstep (se 1 (by rfl) ⟨909917, by rfl⟩ : syracuseStep 1213223 = 1819835) B1819835
theorem B1213263 : Blo 1211423 1213263 := bstep (se 1 (by rfl) ⟨909947, by rfl⟩ : syracuseStep 1213263 = 1819895) B1819895
theorem B2728799 : Blo 1211423 2728799 := bstep (se 1 (by rfl) ⟨2046599, by rfl⟩ : syracuseStep 2728799 = 4093199) B4093199
theorem B1819487 : Blo 1211423 1819487 := bstep (se 1 (by rfl) ⟨1364615, by rfl⟩ : syracuseStep 1819487 = 2729231) B2729231
theorem B1213279 : Blo 1211423 1213279 := bstep (se 1 (by rfl) ⟨909959, by rfl⟩ : syracuseStep 1213279 = 1819919) B1819919
theorem B3277675 : Blo 1211423 3277675 := bstep (se 1 (by rfl) ⟨2458256, by rfl⟩ : syracuseStep 3277675 = 4916513) B4916513
theorem B1819499 : Blo 1211423 1819499 := bstep (se 1 (by rfl) ⟨1364624, by rfl⟩ : syracuseStep 1819499 = 2729249) B2729249
theorem B1213307 : Blo 1211423 1213307 := bstep (se 1 (by rfl) ⟨909980, by rfl⟩ : syracuseStep 1213307 = 1819961) B1819961
theorem B1213359 : Blo 1211423 1213359 := bstep (se 1 (by rfl) ⟨910019, by rfl⟩ : syracuseStep 1213359 = 1820039) B1820039
theorem B1213383 : Blo 1211423 1213383 := bstep (se 1 (by rfl) ⟨910037, by rfl⟩ : syracuseStep 1213383 = 1820075) B1820075
theorem B1213403 : Blo 1211423 1213403 := bstep (se 1 (by rfl) ⟨910052, by rfl⟩ : syracuseStep 1213403 = 1820105) B1820105
theorem B5530643 : Blo 1211423 5530643 := bstep (se 1 (by rfl) ⟨4147982, by rfl⟩ : syracuseStep 5530643 = 8295965) B8295965
theorem B2728979 : Blo 1211423 2728979 := bstep (se 1 (by rfl) ⟨2046734, by rfl⟩ : syracuseStep 2728979 = 4093469) B4093469
theorem B6136883 : Blo 1211423 6136883 := bstep (se 1 (by rfl) ⟨4602662, by rfl⟩ : syracuseStep 6136883 = 9205325) B9205325
theorem B3277903 : Blo 1211423 3277903 := bstep (se 1 (by rfl) ⟨2458427, by rfl⟩ : syracuseStep 3277903 = 4916855) B4916855
theorem B1819727 : Blo 1211423 1819727 := bstep (se 1 (by rfl) ⟨1364795, by rfl⟩ : syracuseStep 1819727 = 2729591) B2729591
theorem B10364057 : Blo 1211423 10364057 := bstep (se 2 (by rfl) ⟨3886521, by rfl⟩ : syracuseStep 10364057 = 7773043) B7773043
theorem B3884203 : Blo 1211423 3884203 := bstep (se 1 (by rfl) ⟨2913152, by rfl⟩ : syracuseStep 3884203 = 5826305) B5826305
theorem B2303147 : Blo 1211423 2303147 := bstep (se 1 (by rfl) ⟨1727360, by rfl⟩ : syracuseStep 2303147 = 3454721) B3454721
theorem B1819847 : Blo 1211423 1819847 := bstep (se 1 (by rfl) ⟨1364885, by rfl⟩ : syracuseStep 1819847 = 2729771) B2729771
theorem B4089149 : Blo 1211423 4089149 := bstep (se 3 (by rfl) ⟨766715, by rfl⟩ : syracuseStep 4089149 = 1533431) B1533431
theorem B4605245 : Blo 1211423 4605245 := bstep (se 3 (by rfl) ⟨863483, by rfl⟩ : syracuseStep 4605245 = 1726967) B1726967
theorem B2729321 : Blo 1211423 2729321 := bstep (se 2 (by rfl) ⟨1023495, by rfl⟩ : syracuseStep 2729321 = 2046991) B2046991
theorem B1820009 : Blo 1211423 1820009 := bstep (se 2 (by rfl) ⟨682503, by rfl⟩ : syracuseStep 1820009 = 1365007) B1365007
theorem B8734067 : Blo 1211423 8734067 := bstep (se 1 (by rfl) ⟨6550550, by rfl⟩ : syracuseStep 8734067 = 13101101) B13101101
theorem B6555005 : Blo 1211423 6555005 := bstep (se 3 (by rfl) ⟨1229063, by rfl⟩ : syracuseStep 6555005 = 2458127) B2458127
theorem B9209213 : Blo 1211423 9209213 := bstep (se 3 (by rfl) ⟨1726727, by rfl⟩ : syracuseStep 9209213 = 3453455) B3453455
theorem B1820087 : Blo 1211423 1820087 := bstep (se 1 (by rfl) ⟨1365065, by rfl⟩ : syracuseStep 1820087 = 2730131) B2730131
theorem B15533531 : Blo 1211423 15533531 := bstep (se 1 (by rfl) ⟨11650148, by rfl⟩ : syracuseStep 15533531 = 23300297) B23300297
theorem B1820123 : Blo 1211423 1820123 := bstep (se 1 (by rfl) ⟨1365092, by rfl⟩ : syracuseStep 1820123 = 2730185) B2730185
theorem B11659103 : Blo 1211423 11659103 := bstep (se 1 (by rfl) ⟨8744327, by rfl⟩ : syracuseStep 11659103 = 17488655) B17488655
theorem B48547745 : Blo 1211423 48547745 := bstep (se 2 (by rfl) ⟨18205404, by rfl⟩ : syracuseStep 48547745 = 36410809) B36410809
theorem B2729915 : Blo 1211423 2729915 := bstep (se 1 (by rfl) ⟨2047436, by rfl⟩ : syracuseStep 2729915 = 4094873) B4094873
theorem B3278855 : Blo 1211423 3278855 := bstep (se 1 (by rfl) ⟨2459141, by rfl⟩ : syracuseStep 3278855 = 4918283) B4918283
theorem B2730041 : Blo 1211423 2730041 := bstep (se 2 (by rfl) ⟨1023765, by rfl⟩ : syracuseStep 2730041 = 2047531) B2047531
theorem B4090013 : Blo 1211423 4090013 := bstep (se 3 (by rfl) ⟨766877, by rfl⟩ : syracuseStep 4090013 = 1533755) B1533755
theorem B4917647 : Blo 1211423 4917647 := bstep (se 1 (by rfl) ⟨3688235, by rfl⟩ : syracuseStep 4917647 = 7376471) B7376471
theorem B6138503 : Blo 1211423 6138503 := bstep (se 1 (by rfl) ⟨4603877, by rfl⟩ : syracuseStep 6138503 = 9207755) B9207755
theorem B3451531 : Blo 1211423 3451531 := bstep (se 1 (by rfl) ⟨2588648, by rfl⟩ : syracuseStep 3451531 = 5177297) B5177297
theorem B4090553 : Blo 1211423 4090553 := bstep (se 2 (by rfl) ⟨1533957, by rfl⟩ : syracuseStep 4090553 = 3067915) B3067915
theorem B31501001 : Blo 1211423 31501001 := bstep (se 2 (by rfl) ⟨11812875, by rfl⟩ : syracuseStep 31501001 = 23625751) B23625751
theorem B2591561 : Blo 1211423 2591561 := bstep (se 2 (by rfl) ⟨971835, by rfl⟩ : syracuseStep 2591561 = 1943671) B1943671
theorem B11643725 : Blo 1211423 11643725 := bstep (se 3 (by rfl) ⟨2183198, by rfl⟩ : syracuseStep 11643725 = 4366397) B4366397
theorem B3066731 : Blo 1211423 3066731 := bstep (se 1 (by rfl) ⟨2300048, by rfl⟩ : syracuseStep 3066731 = 4600097) B4600097
theorem B7187429 : Blo 1211423 7187429 := bstep (se 4 (by rfl) ⟨673821, by rfl⟩ : syracuseStep 7187429 = 1347643) B1347643
theorem B8735795 : Blo 1211423 8735795 := bstep (se 1 (by rfl) ⟨6551846, by rfl⟩ : syracuseStep 8735795 = 13103693) B13103693
theorem B4091147 : Blo 1211423 4091147 := bstep (se 1 (by rfl) ⟨3068360, by rfl⟩ : syracuseStep 4091147 = 6136721) B6136721
theorem B8858969 : Blo 1211423 8858969 := bstep (se 2 (by rfl) ⟨3322113, by rfl⟩ : syracuseStep 8858969 = 6644227) B6644227
theorem B3067379 : Blo 1211423 3067379 := bstep (se 1 (by rfl) ⟨2300534, by rfl⟩ : syracuseStep 3067379 = 4601069) B4601069
theorem B4091417 : Blo 1211423 4091417 := bstep (se 2 (by rfl) ⟨1534281, by rfl⟩ : syracuseStep 4091417 = 3068563) B3068563
theorem B3501593 : Blo 1211423 3501593 := bstep (se 2 (by rfl) ⟨1313097, by rfl⟩ : syracuseStep 3501593 = 2626195) B2626195
theorem B1363495 : Blo 1211423 1363495 := bstep (se 1 (by rfl) ⟨1022621, by rfl⟩ : syracuseStep 1363495 = 2045243) B2045243
theorem B1535527 : Blo 1211423 1535527 := bstep (se 1 (by rfl) ⟨1151645, by rfl⟩ : syracuseStep 1535527 = 2303291) B2303291
theorem B23301755 : Blo 1211423 23301755 := bstep (se 1 (by rfl) ⟨17476316, by rfl⟩ : syracuseStep 23301755 = 34952633) B34952633
theorem B27979453 : Blo 1211423 27979453 := bstep (se 3 (by rfl) ⟨5246147, by rfl⟩ : syracuseStep 27979453 = 10492295) B10492295
theorem B3067591 : Blo 1211423 3067591 := bstep (se 1 (by rfl) ⟨2300693, by rfl⟩ : syracuseStep 3067591 = 4601387) B4601387
theorem B7368491 : Blo 1211423 7368491 := bstep (se 1 (by rfl) ⟨5526368, by rfl⟩ : syracuseStep 7368491 = 11052737) B11052737
theorem B4599625 : Blo 1211423 4599625 := bstep (se 2 (by rfl) ⟨1724859, by rfl⟩ : syracuseStep 4599625 = 3449719) B3449719
theorem B6549511 : Blo 1211423 6549511 := bstep (se 1 (by rfl) ⟨4912133, by rfl⟩ : syracuseStep 6549511 = 9824267) B9824267
theorem B6139961 : Blo 1211423 6139961 := bstep (se 2 (by rfl) ⟨2302485, by rfl⟩ : syracuseStep 6139961 = 4604971) B4604971
theorem B17485885 : Blo 1211423 17485885 := bstep (se 3 (by rfl) ⟨3278603, by rfl⟩ : syracuseStep 17485885 = 6557207) B6557207
theorem B14954827 : Blo 1211423 14954827 := bstep (se 1 (by rfl) ⟨11216120, by rfl⟩ : syracuseStep 14954827 = 22432241) B22432241
theorem B2216375 : Blo 1211423 2216375 := bstep (se 1 (by rfl) ⟨1662281, by rfl⟩ : syracuseStep 2216375 = 3324563) B3324563
theorem B2044379 : Blo 1211423 2044379 := bstep (se 1 (by rfl) ⟨1533284, by rfl⟩ : syracuseStep 2044379 = 3066569) B3066569
theorem B2912777 : Blo 1211423 2912777 := bstep (se 2 (by rfl) ⟨1092291, by rfl⟩ : syracuseStep 2912777 = 2184583) B2184583
theorem B3453479 : Blo 1211423 3453479 := bstep (se 1 (by rfl) ⟨2590109, by rfl⟩ : syracuseStep 3453479 = 5180219) B5180219
theorem B3068513 : Blo 1211423 3068513 := bstep (se 2 (by rfl) ⟨1150692, by rfl⟩ : syracuseStep 3068513 = 2301385) B2301385
theorem B4092551 : Blo 1211423 4092551 := bstep (se 1 (by rfl) ⟨3069413, by rfl⟩ : syracuseStep 4092551 = 6138827) B6138827
theorem B4092605 : Blo 1211423 4092605 := bstep (se 3 (by rfl) ⟨767363, by rfl⟩ : syracuseStep 4092605 = 1534727) B1534727
theorem B2044615 : Blo 1211423 2044615 := bstep (se 1 (by rfl) ⟨1533461, by rfl⟩ : syracuseStep 2044615 = 3066923) B3066923
theorem B10351313 : Blo 1211423 10351313 := bstep (se 2 (by rfl) ⟨3881742, by rfl⟩ : syracuseStep 10351313 = 7763485) B7763485
theorem B4092767 : Blo 1211423 4092767 := bstep (se 1 (by rfl) ⟨3069575, by rfl⟩ : syracuseStep 4092767 = 6139151) B6139151
theorem B2044777 : Blo 1211423 2044777 := bstep (se 2 (by rfl) ⟨766791, by rfl⟩ : syracuseStep 2044777 = 1533583) B1533583
theorem B2331499 : Blo 1211423 2331499 := bstep (se 1 (by rfl) ⟨1748624, by rfl⟩ : syracuseStep 2331499 = 3497249) B3497249
theorem B2184079 : Blo 1211423 2184079 := bstep (se 1 (by rfl) ⟨1638059, by rfl⟩ : syracuseStep 2184079 = 3276119) B3276119
theorem B4092929 : Blo 1211423 4092929 := bstep (se 2 (by rfl) ⟨1534848, by rfl⟩ : syracuseStep 4092929 = 3069697) B3069697
theorem B19674161 : Blo 1211423 19674161 := bstep (se 2 (by rfl) ⟨7377810, by rfl⟩ : syracuseStep 19674161 = 14755621) B14755621
theorem B2045371 : Blo 1211423 2045371 := bstep (se 1 (by rfl) ⟨1534028, by rfl⟩ : syracuseStep 2045371 = 3068057) B3068057
theorem B2045479 : Blo 1211423 2045479 := bstep (se 1 (by rfl) ⟨1534109, by rfl⟩ : syracuseStep 2045479 = 3068219) B3068219
theorem B17471123 : Blo 1211423 17471123 := bstep (se 1 (by rfl) ⟨13103342, by rfl⟩ : syracuseStep 17471123 = 26206685) B26206685
theorem B9213587 : Blo 1211423 9213587 := bstep (se 1 (by rfl) ⟨6910190, by rfl⟩ : syracuseStep 9213587 = 13820381) B13820381
theorem B3454663 : Blo 1211423 3454663 := bstep (se 1 (by rfl) ⟨2590997, by rfl⟩ : syracuseStep 3454663 = 5181995) B5181995
theorem B4601555 : Blo 1211423 4601555 := bstep (se 1 (by rfl) ⟨3451166, by rfl⟩ : syracuseStep 4601555 = 6902333) B6902333
theorem B16578341 : Blo 1211423 16578341 := bstep (se 4 (by rfl) ⟨1554219, by rfl⟩ : syracuseStep 16578341 = 3108439) B3108439
theorem B4093739 : Blo 1211423 4093739 := bstep (se 1 (by rfl) ⟨3070304, by rfl⟩ : syracuseStep 4093739 = 6140609) B6140609
theorem B2725739 : Blo 1211423 2725739 := bstep (se 1 (by rfl) ⟨2044304, by rfl⟩ : syracuseStep 2725739 = 4088609) B4088609
theorem B2045803 : Blo 1211423 2045803 := bstep (se 1 (by rfl) ⟨1534352, by rfl⟩ : syracuseStep 2045803 = 3068705) B3068705
theorem B2725793 : Blo 1211423 2725793 := bstep (se 2 (by rfl) ⟨1022172, by rfl⟩ : syracuseStep 2725793 = 2044345) B2044345
theorem B2332577 : Blo 1211423 2332577 := bstep (se 2 (by rfl) ⟨874716, by rfl⟩ : syracuseStep 2332577 = 1749433) B1749433
theorem B7763971 : Blo 1211423 7763971 := bstep (se 1 (by rfl) ⟨5822978, by rfl⟩ : syracuseStep 7763971 = 11645957) B11645957
theorem B3069971 : Blo 1211423 3069971 := bstep (se 1 (by rfl) ⟨2302478, by rfl⟩ : syracuseStep 3069971 = 4604957) B4604957
theorem B4094009 : Blo 1211423 4094009 := bstep (se 2 (by rfl) ⟨1535253, by rfl⟩ : syracuseStep 4094009 = 3070507) B3070507
theorem B6142067 : Blo 1211423 6142067 := bstep (se 1 (by rfl) ⟨4606550, by rfl⟩ : syracuseStep 6142067 = 9213101) B9213101
theorem B2726135 : Blo 1211423 2726135 := bstep (se 1 (by rfl) ⟨2044601, by rfl⟩ : syracuseStep 2726135 = 4089203) B4089203
theorem B2185463 : Blo 1211423 2185463 := bstep (se 1 (by rfl) ⟨1639097, by rfl⟩ : syracuseStep 2185463 = 3278195) B3278195
theorem B2103545 : Blo 1211423 2103545 := bstep (se 2 (by rfl) ⟨788829, by rfl⟩ : syracuseStep 2103545 = 1577659) B1577659
theorem B9836849 : Blo 1211423 9836849 := bstep (se 2 (by rfl) ⟨3688818, by rfl⟩ : syracuseStep 9836849 = 7377637) B7377637
theorem B7764329 : Blo 1211423 7764329 := bstep (se 2 (by rfl) ⟨2911623, by rfl⟩ : syracuseStep 7764329 = 5823247) B5823247
theorem B4094333 : Blo 1211423 4094333 := bstep (se 3 (by rfl) ⟨767687, by rfl⟩ : syracuseStep 4094333 = 1535375) B1535375
theorem B11065733 : Blo 1211423 11065733 := bstep (se 4 (by rfl) ⟨1037412, by rfl⟩ : syracuseStep 11065733 = 2074825) B2074825
theorem B1554907 : Blo 1211423 1554907 := bstep (se 1 (by rfl) ⟨1166180, by rfl⟩ : syracuseStep 1554907 = 2332361) B2332361
theorem B4372973 : Blo 1211423 4372973 := bstep (se 3 (by rfl) ⟨819932, by rfl⟩ : syracuseStep 4372973 = 1639865) B1639865
theorem B9206297 : Blo 1211423 9206297 := bstep (se 2 (by rfl) ⟨3452361, by rfl⟩ : syracuseStep 9206297 = 6904723) B6904723
theorem B17947271 : Blo 1211423 17947271 := bstep (se 1 (by rfl) ⟨13460453, by rfl⟩ : syracuseStep 17947271 = 26920907) B26920907
theorem B4094603 : Blo 1211423 4094603 := bstep (se 1 (by rfl) ⟨3070952, by rfl⟩ : syracuseStep 4094603 = 6141905) B6141905
theorem B11057849 : Blo 1211423 11057849 := bstep (se 2 (by rfl) ⟨4146693, by rfl⟩ : syracuseStep 11057849 = 8293387) B8293387
theorem B4373203 : Blo 1211423 4373203 := bstep (se 1 (by rfl) ⟨3279902, by rfl⟩ : syracuseStep 4373203 = 6559805) B6559805
theorem B2300663 : Blo 1211423 2300663 := bstep (se 1 (by rfl) ⟨1725497, by rfl⟩ : syracuseStep 2300663 = 3450995) B3450995
theorem B2726729 : Blo 1211423 2726729 := bstep (se 2 (by rfl) ⟨1022523, by rfl⟩ : syracuseStep 2726729 = 2045047) B2045047
theorem B2300815 : Blo 1211423 2300815 := bstep (se 1 (by rfl) ⟨1725611, by rfl⟩ : syracuseStep 2300815 = 3451223) B3451223
theorem B2046863 : Blo 1211423 2046863 := bstep (se 1 (by rfl) ⟨1535147, by rfl⟩ : syracuseStep 2046863 = 3070295) B3070295
theorem B1817519 : Blo 1211423 1817519 := bstep (se 1 (by rfl) ⟨1363139, by rfl⟩ : syracuseStep 1817519 = 2726279) B2726279
theorem B1817609 : Blo 1211423 1817609 := bstep (se 2 (by rfl) ⟨681603, by rfl⟩ : syracuseStep 1817609 = 1363207) B1363207
theorem B1727497 : Blo 1211423 1727497 := bstep (se 2 (by rfl) ⟨647811, by rfl⟩ : syracuseStep 1727497 = 1295623) B1295623
theorem B1211431 : Blo 1211423 1211431 := bstep (se 1 (by rfl) ⟨908573, by rfl⟩ : syracuseStep 1211431 = 1817147) B1817147
theorem B1940519 : Blo 1211423 1940519 := bstep (se 1 (by rfl) ⟨1455389, by rfl⟩ : syracuseStep 1940519 = 2910779) B2910779
theorem B1817639 : Blo 1211423 1817639 := bstep (se 1 (by rfl) ⟨1363229, by rfl⟩ : syracuseStep 1817639 = 2726459) B2726459
theorem B13818923 : Blo 1211423 13818923 := bstep (se 1 (by rfl) ⟨10364192, by rfl⟩ : syracuseStep 13818923 = 20728385) B20728385
theorem B1211471 : Blo 1211423 1211471 := bstep (se 1 (by rfl) ⟨908603, by rfl⟩ : syracuseStep 1211471 = 1817207) B1817207
theorem B1211487 : Blo 1211423 1211487 := bstep (se 1 (by rfl) ⟨908615, by rfl⟩ : syracuseStep 1211487 = 1817231) B1817231
theorem B1211515 : Blo 1211423 1211515 := bstep (se 1 (by rfl) ⟨908636, by rfl⟩ : syracuseStep 1211515 = 1817273) B1817273
theorem B1817723 : Blo 1211423 1817723 := bstep (se 1 (by rfl) ⟨1363292, by rfl⟩ : syracuseStep 1817723 = 2726585) B2726585
theorem B2047099 : Blo 1211423 2047099 := bstep (se 1 (by rfl) ⟨1535324, by rfl⟩ : syracuseStep 2047099 = 3070649) B3070649
theorem B1211567 : Blo 1211423 1211567 := bstep (se 1 (by rfl) ⟨908675, by rfl⟩ : syracuseStep 1211567 = 1817351) B1817351
theorem B1211591 : Blo 1211423 1211591 := bstep (se 1 (by rfl) ⟨908693, by rfl⟩ : syracuseStep 1211591 = 1817387) B1817387
theorem B1211611 : Blo 1211423 1211611 := bstep (se 1 (by rfl) ⟨908708, by rfl⟩ : syracuseStep 1211611 = 1817417) B1817417
theorem B1817849 : Blo 1211423 1817849 := bstep (se 2 (by rfl) ⟨681693, by rfl⟩ : syracuseStep 1817849 = 1363387) B1363387
theorem B1211687 : Blo 1211423 1211687 := bstep (se 1 (by rfl) ⟨908765, by rfl⟩ : syracuseStep 1211687 = 1817531) B1817531
theorem B2334025 : Blo 1211423 2334025 := bstep (se 2 (by rfl) ⟨875259, by rfl⟩ : syracuseStep 2334025 = 1750519) B1750519
theorem B1211727 : Blo 1211423 1211727 := bstep (se 1 (by rfl) ⟨908795, by rfl⟩ : syracuseStep 1211727 = 1817591) B1817591
theorem B1211743 : Blo 1211423 1211743 := bstep (se 1 (by rfl) ⟨908807, by rfl⟩ : syracuseStep 1211743 = 1817615) B1817615
theorem B1817951 : Blo 1211423 1817951 := bstep (se 1 (by rfl) ⟨1363463, by rfl⟩ : syracuseStep 1817951 = 2726927) B2726927
theorem B1817963 : Blo 1211423 1817963 := bstep (se 1 (by rfl) ⟨1363472, by rfl⟩ : syracuseStep 1817963 = 2726945) B2726945
theorem B1211771 : Blo 1211423 1211771 := bstep (se 1 (by rfl) ⟨908828, by rfl⟩ : syracuseStep 1211771 = 1817657) B1817657
theorem B1211823 : Blo 1211423 1211823 := bstep (se 1 (by rfl) ⟨908867, by rfl⟩ : syracuseStep 1211823 = 1817735) B1817735
theorem B1211847 : Blo 1211423 1211847 := bstep (se 1 (by rfl) ⟨908885, by rfl⟩ : syracuseStep 1211847 = 1817771) B1817771
theorem B1211867 : Blo 1211423 1211867 := bstep (se 1 (by rfl) ⟨908900, by rfl⟩ : syracuseStep 1211867 = 1817801) B1817801
theorem B1941031 : Blo 1211423 1941031 := bstep (se 1 (by rfl) ⟨1455773, by rfl⟩ : syracuseStep 1941031 = 2911547) B2911547
theorem B1211943 : Blo 1211423 1211943 := bstep (se 1 (by rfl) ⟨908957, by rfl⟩ : syracuseStep 1211943 = 1817915) B1817915
theorem B1211983 : Blo 1211423 1211983 := bstep (se 1 (by rfl) ⟨908987, by rfl⟩ : syracuseStep 1211983 = 1817975) B1817975
theorem B1818191 : Blo 1211423 1818191 := bstep (se 1 (by rfl) ⟨1363643, by rfl⟩ : syracuseStep 1818191 = 2727287) B2727287
theorem B1211999 : Blo 1211423 1211999 := bstep (se 1 (by rfl) ⟨908999, by rfl⟩ : syracuseStep 1211999 = 1817999) B1817999
theorem B2727521 : Blo 1211423 2727521 := bstep (se 2 (by rfl) ⟨1022820, by rfl⟩ : syracuseStep 2727521 = 2045641) B2045641
theorem B1212027 : Blo 1211423 1212027 := bstep (se 1 (by rfl) ⟨909020, by rfl⟩ : syracuseStep 1212027 = 1818041) B1818041
theorem B5250707 : Blo 1211423 5250707 := bstep (se 1 (by rfl) ⟨3938030, by rfl⟩ : syracuseStep 5250707 = 7876061) B7876061
theorem B1212079 : Blo 1211423 1212079 := bstep (se 1 (by rfl) ⟨909059, by rfl⟩ : syracuseStep 1212079 = 1818119) B1818119
theorem B14737085 : Blo 1211423 14737085 := bstep (se 3 (by rfl) ⟨2763203, by rfl⟩ : syracuseStep 14737085 = 5526407) B5526407
theorem B1212103 : Blo 1211423 1212103 := bstep (se 1 (by rfl) ⟨909077, by rfl⟩ : syracuseStep 1212103 = 1818155) B1818155
theorem B3686087 : Blo 1211423 3686087 := bstep (se 1 (by rfl) ⟨2764565, by rfl⟩ : syracuseStep 3686087 = 5529131) B5529131
theorem B1818311 : Blo 1211423 1818311 := bstep (se 1 (by rfl) ⟨1363733, by rfl⟩ : syracuseStep 1818311 = 2727467) B2727467
theorem B1212123 : Blo 1211423 1212123 := bstep (se 1 (by rfl) ⟨909092, by rfl⟩ : syracuseStep 1212123 = 1818185) B1818185
theorem B9330425 : Blo 1211423 9330425 := bstep (se 2 (by rfl) ⟨3498909, by rfl⟩ : syracuseStep 9330425 = 6997819) B6997819
theorem B2301689 : Blo 1211423 2301689 := bstep (se 2 (by rfl) ⟨863133, by rfl⟩ : syracuseStep 2301689 = 1726267) B1726267
theorem B23289605 : Blo 1211423 23289605 := bstep (se 4 (by rfl) ⟨2183400, by rfl⟩ : syracuseStep 23289605 = 4366801) B4366801
theorem B1212199 : Blo 1211423 1212199 := bstep (se 1 (by rfl) ⟨909149, by rfl⟩ : syracuseStep 1212199 = 1818299) B1818299
theorem B1212239 : Blo 1211423 1212239 := bstep (se 1 (by rfl) ⟨909179, by rfl⟩ : syracuseStep 1212239 = 1818359) B1818359
theorem B1212255 : Blo 1211423 1212255 := bstep (se 1 (by rfl) ⟨909191, by rfl⟩ : syracuseStep 1212255 = 1818383) B1818383
theorem B1818473 : Blo 1211423 1818473 := bstep (se 2 (by rfl) ⟨681927, by rfl⟩ : syracuseStep 1818473 = 1363855) B1363855
theorem B1212283 : Blo 1211423 1212283 := bstep (se 1 (by rfl) ⟨909212, by rfl⟩ : syracuseStep 1212283 = 1818425) B1818425
theorem B1212335 : Blo 1211423 1212335 := bstep (se 1 (by rfl) ⟨909251, by rfl⟩ : syracuseStep 1212335 = 1818503) B1818503
theorem B2301871 : Blo 1211423 2301871 := bstep (se 1 (by rfl) ⟨1726403, by rfl⟩ : syracuseStep 2301871 = 3452807) B3452807
theorem B1818551 : Blo 1211423 1818551 := bstep (se 1 (by rfl) ⟨1363913, by rfl⟩ : syracuseStep 1818551 = 2727827) B2727827
theorem B2727863 : Blo 1211423 2727863 := bstep (se 1 (by rfl) ⟨2045897, by rfl⟩ : syracuseStep 2727863 = 4091795) B4091795
theorem B1212359 : Blo 1211423 1212359 := bstep (se 1 (by rfl) ⟨909269, by rfl⟩ : syracuseStep 1212359 = 1818539) B1818539
theorem B7765969 : Blo 1211423 7765969 := bstep (se 2 (by rfl) ⟨2912238, by rfl⟩ : syracuseStep 7765969 = 5824477) B5824477
theorem B1212379 : Blo 1211423 1212379 := bstep (se 1 (by rfl) ⟨909284, by rfl⟩ : syracuseStep 1212379 = 1818569) B1818569
theorem B1818587 : Blo 1211423 1818587 := bstep (se 1 (by rfl) ⟨1363940, by rfl⟩ : syracuseStep 1818587 = 2727881) B2727881
theorem B8732681 : Blo 1211423 8732681 := bstep (se 2 (by rfl) ⟨3274755, by rfl⟩ : syracuseStep 8732681 = 6549511) B6549511
theorem B41517137 : Blo 1211423 41517137 := bstep (se 2 (by rfl) ⟨15568926, by rfl⟩ : syracuseStep 41517137 = 31137853) B31137853
theorem B5177449 : Blo 1211423 5177449 := bstep (se 2 (by rfl) ⟨1941543, by rfl⟩ : syracuseStep 5177449 = 3883087) B3883087
theorem B1212703 : Blo 1211423 1212703 := bstep (se 1 (by rfl) ⟨909527, by rfl⟩ : syracuseStep 1212703 = 1819055) B1819055
theorem B12452147 : Blo 1211423 12452147 := bstep (se 1 (by rfl) ⟨9339110, by rfl⟩ : syracuseStep 12452147 = 18678221) B18678221
theorem B1941851 : Blo 1211423 1941851 := bstep (se 1 (by rfl) ⟨1456388, by rfl⟩ : syracuseStep 1941851 = 2912777) B2912777
theorem B1818971 : Blo 1211423 1818971 := bstep (se 1 (by rfl) ⟨1364228, by rfl⟩ : syracuseStep 1818971 = 2728457) B2728457
theorem B1212763 : Blo 1211423 1212763 := bstep (se 1 (by rfl) ⟨909572, by rfl⟩ : syracuseStep 1212763 = 1819145) B1819145
theorem B2302319 : Blo 1211423 2302319 := bstep (se 1 (by rfl) ⟨1726739, by rfl⟩ : syracuseStep 2302319 = 3453479) B3453479
theorem B1212783 : Blo 1211423 1212783 := bstep (se 1 (by rfl) ⟨909587, by rfl⟩ : syracuseStep 1212783 = 1819175) B1819175
theorem B1212839 : Blo 1211423 1212839 := bstep (se 1 (by rfl) ⟨909629, by rfl⟩ : syracuseStep 1212839 = 1819259) B1819259
theorem B2728367 : Blo 1211423 2728367 := bstep (se 1 (by rfl) ⟨2046275, by rfl⟩ : syracuseStep 2728367 = 4092551) B4092551
theorem B19939769 : Blo 1211423 19939769 := bstep (se 2 (by rfl) ⟨7477413, by rfl⟩ : syracuseStep 19939769 = 14954827) B14954827
theorem B2728403 : Blo 1211423 2728403 := bstep (se 1 (by rfl) ⟨2046302, by rfl⟩ : syracuseStep 2728403 = 4092605) B4092605
theorem B3277307 : Blo 1211423 3277307 := bstep (se 1 (by rfl) ⟨2457980, by rfl⟩ : syracuseStep 3277307 = 4915961) B4915961
theorem B1212923 : Blo 1211423 1212923 := bstep (se 1 (by rfl) ⟨909692, by rfl⟩ : syracuseStep 1212923 = 1819385) B1819385
theorem B22110725 : Blo 1211423 22110725 := bstep (se 4 (by rfl) ⟨2072880, by rfl⟩ : syracuseStep 22110725 = 4145761) B4145761
theorem B2589203 : Blo 1211423 2589203 := bstep (se 1 (by rfl) ⟨1941902, by rfl⟩ : syracuseStep 2589203 = 3883805) B3883805
theorem B2728511 : Blo 1211423 2728511 := bstep (se 1 (by rfl) ⟨2046383, by rfl⟩ : syracuseStep 2728511 = 4092767) B4092767
theorem B1819199 : Blo 1211423 1819199 := bstep (se 1 (by rfl) ⟨1364399, by rfl⟩ : syracuseStep 1819199 = 2728799) B2728799
theorem B1212991 : Blo 1211423 1212991 := bstep (se 1 (by rfl) ⟨909743, by rfl⟩ : syracuseStep 1212991 = 1819487) B1819487
theorem B1212999 : Blo 1211423 1212999 := bstep (se 1 (by rfl) ⟨909749, by rfl⟩ : syracuseStep 1212999 = 1819499) B1819499
theorem B2073209 : Blo 1211423 2073209 := bstep (se 2 (by rfl) ⟨777453, by rfl⟩ : syracuseStep 2073209 = 1554907) B1554907
theorem B2728619 : Blo 1211423 2728619 := bstep (se 1 (by rfl) ⟨2046464, by rfl⟩ : syracuseStep 2728619 = 4092929) B4092929
theorem B3687095 : Blo 1211423 3687095 := bstep (se 1 (by rfl) ⟨2765321, by rfl⟩ : syracuseStep 3687095 = 5530643) B5530643
theorem B1819319 : Blo 1211423 1819319 := bstep (se 1 (by rfl) ⟨1364489, by rfl⟩ : syracuseStep 1819319 = 2728979) B2728979
theorem B13116107 : Blo 1211423 13116107 := bstep (se 1 (by rfl) ⟨9837080, by rfl⟩ : syracuseStep 13116107 = 19674161) B19674161
theorem B1213151 : Blo 1211423 1213151 := bstep (se 1 (by rfl) ⟨909863, by rfl⟩ : syracuseStep 1213151 = 1819727) B1819727
theorem B26231597 : Blo 1211423 26231597 := bstep (se 3 (by rfl) ⟨4918424, by rfl⟩ : syracuseStep 26231597 = 9836849) B9836849
theorem B1213231 : Blo 1211423 1213231 := bstep (se 1 (by rfl) ⟨909923, by rfl⟩ : syracuseStep 1213231 = 1819847) B1819847
theorem B1819547 : Blo 1211423 1819547 := bstep (se 1 (by rfl) ⟨1364660, by rfl⟩ : syracuseStep 1819547 = 2729321) B2729321
theorem B1213339 : Blo 1211423 1213339 := bstep (se 1 (by rfl) ⟨910004, by rfl⟩ : syracuseStep 1213339 = 1820009) B1820009
theorem B1213391 : Blo 1211423 1213391 := bstep (se 1 (by rfl) ⟨910043, by rfl⟩ : syracuseStep 1213391 = 1820087) B1820087
theorem B10355687 : Blo 1211423 10355687 := bstep (se 1 (by rfl) ⟨7766765, by rfl⟩ : syracuseStep 10355687 = 15533531) B15533531
theorem B1213415 : Blo 1211423 1213415 := bstep (se 1 (by rfl) ⟨910061, by rfl⟩ : syracuseStep 1213415 = 1820123) B1820123
theorem B11052227 : Blo 1211423 11052227 := bstep (se 1 (by rfl) ⟨8289170, by rfl⟩ : syracuseStep 11052227 = 16578341) B16578341
theorem B2729159 : Blo 1211423 2729159 := bstep (se 1 (by rfl) ⟨2046869, by rfl⟩ : syracuseStep 2729159 = 4093739) B4093739
theorem B1819943 : Blo 1211423 1819943 := bstep (se 1 (by rfl) ⟨1364957, by rfl⟩ : syracuseStep 1819943 = 2729915) B2729915
theorem B2303329 : Blo 1211423 2303329 := bstep (se 2 (by rfl) ⟨863748, by rfl⟩ : syracuseStep 2303329 = 1727497) B1727497
theorem B2729339 : Blo 1211423 2729339 := bstep (se 1 (by rfl) ⟨2047004, by rfl⟩ : syracuseStep 2729339 = 4094009) B4094009
theorem B1820027 : Blo 1211423 1820027 := bstep (se 1 (by rfl) ⟨1365020, by rfl⟩ : syracuseStep 1820027 = 2730041) B2730041
theorem B2729465 : Blo 1211423 2729465 := bstep (se 2 (by rfl) ⟨1023549, by rfl⟩ : syracuseStep 2729465 = 2047099) B2047099
theorem B1402363 : Blo 1211423 1402363 := bstep (se 1 (by rfl) ⟨1051772, by rfl⟩ : syracuseStep 1402363 = 2103545) B2103545
theorem B5178937 : Blo 1211423 5178937 := bstep (se 2 (by rfl) ⟨1942101, by rfl⟩ : syracuseStep 5178937 = 3884203) B3884203
theorem B2729555 : Blo 1211423 2729555 := bstep (se 1 (by rfl) ⟨2047166, by rfl⟩ : syracuseStep 2729555 = 4094333) B4094333
theorem B3278431 : Blo 1211423 3278431 := bstep (se 1 (by rfl) ⟨2458823, by rfl⟩ : syracuseStep 3278431 = 4917647) B4917647
theorem B6137531 : Blo 1211423 6137531 := bstep (se 1 (by rfl) ⟨4603148, by rfl⟩ : syracuseStep 6137531 = 9206297) B9206297
theorem B2729735 : Blo 1211423 2729735 := bstep (se 1 (by rfl) ⟨2047301, by rfl⟩ : syracuseStep 2729735 = 4094603) B4094603
theorem B84002669 : Blo 1211423 84002669 := bstep (se 3 (by rfl) ⟨15750500, by rfl⟩ : syracuseStep 84002669 = 31501001) B31501001
theorem B4090121 : Blo 1211423 4090121 := bstep (se 2 (by rfl) ⟨1533795, by rfl⟩ : syracuseStep 4090121 = 3067591) B3067591
theorem B4606217 : Blo 1211423 4606217 := bstep (se 2 (by rfl) ⟨1727331, by rfl⟩ : syracuseStep 4606217 = 3454663) B3454663
theorem B15534503 : Blo 1211423 15534503 := bstep (se 1 (by rfl) ⟨11650877, by rfl⟩ : syracuseStep 15534503 = 23301755) B23301755
theorem B6220205 : Blo 1211423 6220205 := bstep (se 3 (by rfl) ⟨1166288, by rfl⟩ : syracuseStep 6220205 = 2332577) B2332577
theorem B3500471 : Blo 1211423 3500471 := bstep (se 1 (by rfl) ⟨2625353, by rfl⟩ : syracuseStep 3500471 = 5250707) B5250707
theorem B9824723 : Blo 1211423 9824723 := bstep (se 1 (by rfl) ⟨7368542, by rfl⟩ : syracuseStep 9824723 = 14737085) B14737085
theorem B6220283 : Blo 1211423 6220283 := bstep (se 1 (by rfl) ⟨4665212, by rfl⟩ : syracuseStep 6220283 = 9330425) B9330425
theorem B1534459 : Blo 1211423 1534459 := bstep (se 1 (by rfl) ⟨1150844, by rfl⟩ : syracuseStep 1534459 = 2301689) B2301689
theorem B15526403 : Blo 1211423 15526403 := bstep (se 1 (by rfl) ⟨11644802, by rfl⟩ : syracuseStep 15526403 = 23289605) B23289605
theorem B5827247 : Blo 1211423 5827247 := bstep (se 1 (by rfl) ⟨4370435, by rfl⟩ : syracuseStep 5827247 = 8740871) B8740871
theorem B1362919 : Blo 1211423 1362919 := bstep (se 1 (by rfl) ⟨1022189, by rfl⟩ : syracuseStep 1362919 = 2044379) B2044379
theorem B6900875 : Blo 1211423 6900875 := bstep (se 1 (by rfl) ⟨5175656, by rfl⟩ : syracuseStep 6900875 = 10351313) B10351313
theorem B4091255 : Blo 1211423 4091255 := bstep (se 1 (by rfl) ⟨3068441, by rfl⟩ : syracuseStep 4091255 = 6136883) B6136883
theorem B4369801 : Blo 1211423 4369801 := bstep (se 2 (by rfl) ⟨1638675, by rfl⟩ : syracuseStep 4369801 = 3277351) B3277351
theorem B6909371 : Blo 1211423 6909371 := bstep (se 1 (by rfl) ⟨5182028, by rfl⟩ : syracuseStep 6909371 = 10364057) B10364057
theorem B1535431 : Blo 1211423 1535431 := bstep (se 1 (by rfl) ⟨1151573, by rfl⟩ : syracuseStep 1535431 = 2303147) B2303147
theorem B4370003 : Blo 1211423 4370003 := bstep (se 1 (by rfl) ⟨3277502, by rfl⟩ : syracuseStep 4370003 = 6555005) B6555005
theorem B6139475 : Blo 1211423 6139475 := bstep (se 1 (by rfl) ⟨4604606, by rfl⟩ : syracuseStep 6139475 = 9209213) B9209213
theorem B3067703 : Blo 1211423 3067703 := bstep (se 1 (by rfl) ⟨2300777, by rfl⟩ : syracuseStep 3067703 = 4601555) B4601555
theorem B3108665 : Blo 1211423 3108665 := bstep (se 2 (by rfl) ⟨1165749, by rfl⟩ : syracuseStep 3108665 = 2331499) B2331499
theorem B3067753 : Blo 1211423 3067753 := bstep (se 2 (by rfl) ⟨1150407, by rfl⟩ : syracuseStep 3067753 = 2300815) B2300815
theorem B2912105 : Blo 1211423 2912105 := bstep (se 2 (by rfl) ⟨1092039, by rfl⟩ : syracuseStep 2912105 = 2184079) B2184079
theorem B4370537 : Blo 1211423 4370537 := bstep (se 2 (by rfl) ⟨1638951, by rfl⟩ : syracuseStep 4370537 = 3277903) B3277903
theorem B7377155 : Blo 1211423 7377155 := bstep (se 1 (by rfl) ⟨5532866, by rfl⟩ : syracuseStep 7377155 = 11065733) B11065733
theorem B11964847 : Blo 1211423 11964847 := bstep (se 1 (by rfl) ⟨8973635, by rfl⟩ : syracuseStep 11964847 = 17947271) B17947271
theorem B4092335 : Blo 1211423 4092335 := bstep (se 1 (by rfl) ⟨3069251, by rfl⟩ : syracuseStep 4092335 = 6138503) B6138503
theorem B7762483 : Blo 1211423 7762483 := bstep (se 1 (by rfl) ⟨5821862, by rfl⟩ : syracuseStep 7762483 = 11643725) B11643725
theorem B2044487 : Blo 1211423 2044487 := bstep (se 1 (by rfl) ⟨1533365, by rfl⟩ : syracuseStep 2044487 = 3066731) B3066731
theorem B1364575 : Blo 1211423 1364575 := bstep (se 1 (by rfl) ⟨1023431, by rfl⟩ : syracuseStep 1364575 = 2046863) B2046863
theorem B9212615 : Blo 1211423 9212615 := bstep (se 1 (by rfl) ⟨6909461, by rfl⟩ : syracuseStep 9212615 = 13818923) B13818923
theorem B6910829 : Blo 1211423 6910829 := bstep (se 3 (by rfl) ⟨1295780, by rfl⟩ : syracuseStep 6910829 = 2591561) B2591561
theorem B94565333 : Blo 1211423 94565333 := bstep (se 7 (by rfl) ⟨1108187, by rfl⟩ : syracuseStep 94565333 = 2216375) B2216375
theorem B2044919 : Blo 1211423 2044919 := bstep (se 1 (by rfl) ⟨1533689, by rfl⟩ : syracuseStep 2044919 = 3067379) B3067379
theorem B6132833 : Blo 1211423 6132833 := bstep (se 2 (by rfl) ⟨2299812, by rfl⟩ : syracuseStep 6132833 = 4599625) B4599625
theorem B4912327 : Blo 1211423 4912327 := bstep (se 1 (by rfl) ⟨3684245, by rfl⟩ : syracuseStep 4912327 = 7368491) B7368491
theorem B3069161 : Blo 1211423 3069161 := bstep (se 2 (by rfl) ⟨1150935, by rfl⟩ : syracuseStep 3069161 = 2301871) B2301871
theorem B10351961 : Blo 1211423 10351961 := bstep (se 2 (by rfl) ⟨3881985, by rfl⟩ : syracuseStep 10351961 = 7763971) B7763971
theorem B4093307 : Blo 1211423 4093307 := bstep (se 1 (by rfl) ⟨3069980, by rfl⟩ : syracuseStep 4093307 = 6139961) B6139961
theorem B3069323 : Blo 1211423 3069323 := bstep (se 1 (by rfl) ⟨2301992, by rfl⟩ : syracuseStep 3069323 = 4603985) B4603985
theorem B3069535 : Blo 1211423 3069535 := bstep (se 1 (by rfl) ⟨2302151, by rfl⟩ : syracuseStep 3069535 = 4604303) B4604303
theorem B2045675 : Blo 1211423 2045675 := bstep (se 1 (by rfl) ⟨1534256, by rfl⟩ : syracuseStep 2045675 = 3068513) B3068513
theorem B4602041 : Blo 1211423 4602041 := bstep (se 2 (by rfl) ⟨1725765, by rfl⟩ : syracuseStep 4602041 = 3451531) B3451531
theorem B2726099 : Blo 1211423 2726099 := bstep (se 1 (by rfl) ⟨2044574, by rfl⟩ : syracuseStep 2726099 = 4089149) B4089149
theorem B3070163 : Blo 1211423 3070163 := bstep (se 1 (by rfl) ⟨2302622, by rfl⟩ : syracuseStep 3070163 = 4605245) B4605245
theorem B5822711 : Blo 1211423 5822711 := bstep (se 1 (by rfl) ⟨4367033, by rfl⟩ : syracuseStep 5822711 = 8734067) B8734067
theorem B2726153 : Blo 1211423 2726153 := bstep (se 2 (by rfl) ⟨1022307, by rfl⟩ : syracuseStep 2726153 = 2044615) B2044615
theorem B5830937 : Blo 1211423 5830937 := bstep (se 2 (by rfl) ⟨2186601, by rfl⟩ : syracuseStep 5830937 = 4373203) B4373203
theorem B11647415 : Blo 1211423 11647415 := bstep (se 1 (by rfl) ⟨8735561, by rfl⟩ : syracuseStep 11647415 = 17471123) B17471123
theorem B6142391 : Blo 1211423 6142391 := bstep (se 1 (by rfl) ⟨4606793, by rfl⟩ : syracuseStep 6142391 = 9213587) B9213587
theorem B2726369 : Blo 1211423 2726369 := bstep (se 2 (by rfl) ⟨1022388, by rfl⟩ : syracuseStep 2726369 = 2044777) B2044777
theorem B7772735 : Blo 1211423 7772735 := bstep (se 1 (by rfl) ⟨5829551, by rfl⟩ : syracuseStep 7772735 = 11659103) B11659103
theorem B1817159 : Blo 1211423 1817159 := bstep (se 1 (by rfl) ⟨1362869, by rfl⟩ : syracuseStep 1817159 = 2725739) B2725739
theorem B1817195 : Blo 1211423 1817195 := bstep (se 1 (by rfl) ⟨1362896, by rfl⟩ : syracuseStep 1817195 = 2725793) B2725793
theorem B32365163 : Blo 1211423 32365163 := bstep (se 1 (by rfl) ⟨24273872, by rfl⟩ : syracuseStep 32365163 = 48547745) B48547745
theorem B2185903 : Blo 1211423 2185903 := bstep (se 1 (by rfl) ⟨1639427, by rfl⟩ : syracuseStep 2185903 = 3278855) B3278855
theorem B2046647 : Blo 1211423 2046647 := bstep (se 1 (by rfl) ⟨1534985, by rfl⟩ : syracuseStep 2046647 = 3069971) B3069971
theorem B4094711 : Blo 1211423 4094711 := bstep (se 1 (by rfl) ⟨3071033, by rfl⟩ : syracuseStep 4094711 = 6142067) B6142067
theorem B2726675 : Blo 1211423 2726675 := bstep (se 1 (by rfl) ⟨2045006, by rfl⟩ : syracuseStep 2726675 = 4090013) B4090013
theorem B1817423 : Blo 1211423 1817423 := bstep (se 1 (by rfl) ⟨1363067, by rfl⟩ : syracuseStep 1817423 = 2726135) B2726135
theorem B1456975 : Blo 1211423 1456975 := bstep (se 1 (by rfl) ⟨1092731, by rfl⟩ : syracuseStep 1456975 = 2185463) B2185463
theorem B5176219 : Blo 1211423 5176219 := bstep (se 1 (by rfl) ⟨3882164, by rfl⟩ : syracuseStep 5176219 = 7764329) B7764329
theorem B2915315 : Blo 1211423 2915315 := bstep (se 1 (by rfl) ⟨2186486, by rfl⟩ : syracuseStep 2915315 = 4372973) B4372973
theorem B3112033 : Blo 1211423 3112033 := bstep (se 2 (by rfl) ⟨1167012, by rfl⟩ : syracuseStep 3112033 = 2334025) B2334025
theorem B2727035 : Blo 1211423 2727035 := bstep (se 1 (by rfl) ⟨2045276, by rfl⟩ : syracuseStep 2727035 = 4090553) B4090553
theorem B7371899 : Blo 1211423 7371899 := bstep (se 1 (by rfl) ⟨5528924, by rfl⟩ : syracuseStep 7371899 = 11057849) B11057849
theorem B6904997 : Blo 1211423 6904997 := bstep (se 4 (by rfl) ⟨647343, by rfl⟩ : syracuseStep 6904997 = 1294687) B1294687
theorem B1817819 : Blo 1211423 1817819 := bstep (se 1 (by rfl) ⟨1363364, by rfl⟩ : syracuseStep 1817819 = 2726729) B2726729
theorem B17480933 : Blo 1211423 17480933 := bstep (se 4 (by rfl) ⟨1638837, by rfl⟩ : syracuseStep 17480933 = 3277675) B3277675
theorem B2727161 : Blo 1211423 2727161 := bstep (se 2 (by rfl) ⟨1022685, by rfl⟩ : syracuseStep 2727161 = 2045371) B2045371
theorem B1211679 : Blo 1211423 1211679 := bstep (se 1 (by rfl) ⟨908759, by rfl⟩ : syracuseStep 1211679 = 1817519) B1817519
theorem B6135101 : Blo 1211423 6135101 := bstep (se 3 (by rfl) ⟨1150331, by rfl⟩ : syracuseStep 6135101 = 2300663) B2300663
theorem B4791619 : Blo 1211423 4791619 := bstep (se 1 (by rfl) ⟨3593714, by rfl⟩ : syracuseStep 4791619 = 7187429) B7187429
theorem B1211739 : Blo 1211423 1211739 := bstep (se 1 (by rfl) ⟨908804, by rfl⟩ : syracuseStep 1211739 = 1817609) B1817609
theorem B1293679 : Blo 1211423 1293679 := bstep (se 1 (by rfl) ⟨970259, by rfl⟩ : syracuseStep 1293679 = 1940519) B1940519
theorem B1211759 : Blo 1211423 1211759 := bstep (se 1 (by rfl) ⟨908819, by rfl⟩ : syracuseStep 1211759 = 1817639) B1817639
theorem B5823863 : Blo 1211423 5823863 := bstep (se 1 (by rfl) ⟨4367897, by rfl⟩ : syracuseStep 5823863 = 8735795) B8735795
theorem B2588041 : Blo 1211423 2588041 := bstep (se 2 (by rfl) ⟨970515, by rfl⟩ : syracuseStep 2588041 = 1941031) B1941031
theorem B1817993 : Blo 1211423 1817993 := bstep (se 2 (by rfl) ⟨681747, by rfl⟩ : syracuseStep 1817993 = 1363495) B1363495
theorem B2727305 : Blo 1211423 2727305 := bstep (se 2 (by rfl) ⟨1022739, by rfl⟩ : syracuseStep 2727305 = 2045479) B2045479
theorem B2047369 : Blo 1211423 2047369 := bstep (se 2 (by rfl) ⟨767763, by rfl⟩ : syracuseStep 2047369 = 1535527) B1535527
theorem B1211815 : Blo 1211423 1211815 := bstep (se 1 (by rfl) ⟨908861, by rfl⟩ : syracuseStep 1211815 = 1817723) B1817723
theorem B1211899 : Blo 1211423 1211899 := bstep (se 1 (by rfl) ⟨908924, by rfl⟩ : syracuseStep 1211899 = 1817849) B1817849
theorem B2727431 : Blo 1211423 2727431 := bstep (se 1 (by rfl) ⟨2045573, by rfl⟩ : syracuseStep 2727431 = 4091147) B4091147
theorem B5905979 : Blo 1211423 5905979 := bstep (se 1 (by rfl) ⟨4429484, by rfl⟩ : syracuseStep 5905979 = 8858969) B8858969
theorem B1211967 : Blo 1211423 1211967 := bstep (se 1 (by rfl) ⟨908975, by rfl⟩ : syracuseStep 1211967 = 1817951) B1817951
theorem B1211975 : Blo 1211423 1211975 := bstep (se 1 (by rfl) ⟨908981, by rfl⟩ : syracuseStep 1211975 = 1817963) B1817963
theorem B37305937 : Blo 1211423 37305937 := bstep (se 2 (by rfl) ⟨13989726, by rfl⟩ : syracuseStep 37305937 = 27979453) B27979453
theorem B2727611 : Blo 1211423 2727611 := bstep (se 1 (by rfl) ⟨2045708, by rfl⟩ : syracuseStep 2727611 = 4091417) B4091417
theorem B2334395 : Blo 1211423 2334395 := bstep (se 1 (by rfl) ⟨1750796, by rfl⟩ : syracuseStep 2334395 = 3501593) B3501593
theorem B1212127 : Blo 1211423 1212127 := bstep (se 1 (by rfl) ⟨909095, by rfl⟩ : syracuseStep 1212127 = 1818191) B1818191
theorem B1818347 : Blo 1211423 1818347 := bstep (se 1 (by rfl) ⟨1363760, by rfl⟩ : syracuseStep 1818347 = 2727521) B2727521
theorem B2457391 : Blo 1211423 2457391 := bstep (se 1 (by rfl) ⟨1843043, by rfl⟩ : syracuseStep 2457391 = 3686087) B3686087
theorem B1212207 : Blo 1211423 1212207 := bstep (se 1 (by rfl) ⟨909155, by rfl⟩ : syracuseStep 1212207 = 1818311) B1818311
theorem B2727737 : Blo 1211423 2727737 := bstep (se 2 (by rfl) ⟨1022901, by rfl⟩ : syracuseStep 2727737 = 2045803) B2045803
theorem B23314513 : Blo 1211423 23314513 := bstep (se 2 (by rfl) ⟨8742942, by rfl⟩ : syracuseStep 23314513 = 17485885) B17485885
theorem B1212315 : Blo 1211423 1212315 := bstep (se 1 (by rfl) ⟨909236, by rfl⟩ : syracuseStep 1212315 = 1818473) B1818473
theorem B10354625 : Blo 1211423 10354625 := bstep (se 2 (by rfl) ⟨3882984, by rfl⟩ : syracuseStep 10354625 = 7765969) B7765969
theorem B1212367 : Blo 1211423 1212367 := bstep (se 1 (by rfl) ⟨909275, by rfl⟩ : syracuseStep 1212367 = 1818551) B1818551
theorem B1818575 : Blo 1211423 1818575 := bstep (se 1 (by rfl) ⟨1363931, by rfl⟩ : syracuseStep 1818575 = 2727863) B2727863
theorem B1212391 : Blo 1211423 1212391 := bstep (se 1 (by rfl) ⟨909293, by rfl⟩ : syracuseStep 1212391 = 1818587) B1818587
theorem B1212647 : Blo 1211423 1212647 := bstep (se 1 (by rfl) ⟨909485, by rfl⟩ : syracuseStep 1212647 = 1818971) B1818971
theorem B2728223 : Blo 1211423 2728223 := bstep (se 1 (by rfl) ⟨2046167, by rfl⟩ : syracuseStep 2728223 = 4092335) B4092335
theorem B1818911 : Blo 1211423 1818911 := bstep (se 1 (by rfl) ⟨1364183, by rfl⟩ : syracuseStep 1818911 = 2728367) B2728367
theorem B1818935 : Blo 1211423 1818935 := bstep (se 1 (by rfl) ⟨1364201, by rfl⟩ : syracuseStep 1818935 = 2728403) B2728403
theorem B1819007 : Blo 1211423 1819007 := bstep (se 1 (by rfl) ⟨1364255, by rfl⟩ : syracuseStep 1819007 = 2728511) B2728511
theorem B1212799 : Blo 1211423 1212799 := bstep (se 1 (by rfl) ⟨909599, by rfl⟩ : syracuseStep 1212799 = 1819199) B1819199
theorem B1819079 : Blo 1211423 1819079 := bstep (se 1 (by rfl) ⟨1364309, by rfl⟩ : syracuseStep 1819079 = 2728619) B2728619
theorem B2458063 : Blo 1211423 2458063 := bstep (se 1 (by rfl) ⟨1843547, by rfl⟩ : syracuseStep 2458063 = 3687095) B3687095
theorem B1212879 : Blo 1211423 1212879 := bstep (se 1 (by rfl) ⟨909659, by rfl⟩ : syracuseStep 1212879 = 1819319) B1819319
theorem B1213031 : Blo 1211423 1213031 := bstep (se 1 (by rfl) ⟨909773, by rfl⟩ : syracuseStep 1213031 = 1819547) B1819547
theorem B4088555 : Blo 1211423 4088555 := bstep (se 1 (by rfl) ⟨3066416, by rfl⟩ : syracuseStep 4088555 = 6132833) B6132833
theorem B1819433 : Blo 1211423 1819433 := bstep (se 2 (by rfl) ⟨682287, by rfl⟩ : syracuseStep 1819433 = 1364575) B1364575
theorem B1819439 : Blo 1211423 1819439 := bstep (se 1 (by rfl) ⟨1364579, by rfl⟩ : syracuseStep 1819439 = 2729159) B2729159
theorem B1213295 : Blo 1211423 1213295 := bstep (se 1 (by rfl) ⟨909971, by rfl⟩ : syracuseStep 1213295 = 1819943) B1819943
theorem B5178269 : Blo 1211423 5178269 := bstep (se 3 (by rfl) ⟨970925, by rfl⟩ : syracuseStep 5178269 = 1941851) B1941851
theorem B2728871 : Blo 1211423 2728871 := bstep (se 1 (by rfl) ⟨2046653, by rfl⟩ : syracuseStep 2728871 = 4093307) B4093307
theorem B1819559 : Blo 1211423 1819559 := bstep (se 1 (by rfl) ⟨1364669, by rfl⟩ : syracuseStep 1819559 = 2729339) B2729339
theorem B1213351 : Blo 1211423 1213351 := bstep (se 1 (by rfl) ⟨910013, by rfl⟩ : syracuseStep 1213351 = 1820027) B1820027
theorem B1819643 : Blo 1211423 1819643 := bstep (se 1 (by rfl) ⟨1364732, by rfl⟩ : syracuseStep 1819643 = 2729465) B2729465
theorem B1819703 : Blo 1211423 1819703 := bstep (se 1 (by rfl) ⟨1364777, by rfl⟩ : syracuseStep 1819703 = 2729555) B2729555
theorem B1942633 : Blo 1211423 1942633 := bstep (se 2 (by rfl) ⟨728487, by rfl⟩ : syracuseStep 1942633 = 1456975) B1456975
theorem B1819823 : Blo 1211423 1819823 := bstep (se 1 (by rfl) ⟨1364867, by rfl⟩ : syracuseStep 1819823 = 2729735) B2729735
theorem B56001779 : Blo 1211423 56001779 := bstep (se 1 (by rfl) ⟨42001334, by rfl⟩ : syracuseStep 56001779 = 84002669) B84002669
theorem B10356335 : Blo 1211423 10356335 := bstep (se 1 (by rfl) ⟨7767251, by rfl⟩ : syracuseStep 10356335 = 15534503) B15534503
theorem B4146803 : Blo 1211423 4146803 := bstep (se 1 (by rfl) ⟨3110102, by rfl⟩ : syracuseStep 4146803 = 6220205) B6220205
theorem B3884831 : Blo 1211423 3884831 := bstep (se 1 (by rfl) ⟨2913623, by rfl⟩ : syracuseStep 3884831 = 5827247) B5827247
theorem B2729807 : Blo 1211423 2729807 := bstep (se 1 (by rfl) ⟨2047355, by rfl⟩ : syracuseStep 2729807 = 4094711) B4094711
theorem B5826401 : Blo 1211423 5826401 := bstep (se 2 (by rfl) ⟨2184900, by rfl⟩ : syracuseStep 5826401 = 4369801) B4369801
theorem B2729825 : Blo 1211423 2729825 := bstep (se 2 (by rfl) ⟨1023684, by rfl⟩ : syracuseStep 2729825 = 2047369) B2047369
theorem B1943543 : Blo 1211423 1943543 := bstep (se 1 (by rfl) ⟨1457657, by rfl⟩ : syracuseStep 1943543 = 2915315) B2915315
theorem B1869817 : Blo 1211423 1869817 := bstep (se 2 (by rfl) ⟨701181, by rfl⟩ : syracuseStep 1869817 = 1402363) B1402363
theorem B4090067 : Blo 1211423 4090067 := bstep (se 1 (by rfl) ⟨3067550, by rfl⟩ : syracuseStep 4090067 = 6135101) B6135101
theorem B4606247 : Blo 1211423 4606247 := bstep (se 1 (by rfl) ⟨3454685, by rfl⟩ : syracuseStep 4606247 = 6909371) B6909371
theorem B4090337 : Blo 1211423 4090337 := bstep (se 2 (by rfl) ⟨1533876, by rfl⟩ : syracuseStep 4090337 = 3067753) B3067753
theorem B66349685 : Blo 1211423 66349685 := bstep (se 5 (by rfl) ⟨3110141, by rfl⟩ : syracuseStep 66349685 = 6220283) B6220283
theorem B4918103 : Blo 1211423 4918103 := bstep (se 1 (by rfl) ⟨3688577, by rfl⟩ : syracuseStep 4918103 = 7377155) B7377155
theorem B8301431 : Blo 1211423 8301431 := bstep (se 1 (by rfl) ⟨6226073, by rfl⟩ : syracuseStep 8301431 = 12452147) B12452147
theorem B1534879 : Blo 1211423 1534879 := bstep (se 1 (by rfl) ⟨1151159, by rfl⟩ : syracuseStep 1534879 = 2302319) B2302319
theorem B14740483 : Blo 1211423 14740483 := bstep (se 1 (by rfl) ⟨11055362, by rfl⟩ : syracuseStep 14740483 = 22110725) B22110725
theorem B1362991 : Blo 1211423 1362991 := bstep (se 1 (by rfl) ⟨1022243, by rfl⟩ : syracuseStep 1362991 = 2044487) B2044487
theorem B8744071 : Blo 1211423 8744071 := bstep (se 1 (by rfl) ⟨6558053, by rfl⟩ : syracuseStep 8744071 = 13116107) B13116107
theorem B15953129 : Blo 1211423 15953129 := bstep (se 2 (by rfl) ⟨5982423, by rfl⟩ : syracuseStep 15953129 = 11964847) B11964847
theorem B4607219 : Blo 1211423 4607219 := bstep (se 1 (by rfl) ⟨3455414, by rfl⟩ : syracuseStep 4607219 = 6910829) B6910829
theorem B1363279 : Blo 1211423 1363279 := bstep (se 1 (by rfl) ⟨1022459, by rfl⟩ : syracuseStep 1363279 = 2044919) B2044919
theorem B10349977 : Blo 1211423 10349977 := bstep (se 2 (by rfl) ⟨3881241, by rfl⟩ : syracuseStep 10349977 = 7762483) B7762483
theorem B6901307 : Blo 1211423 6901307 := bstep (se 1 (by rfl) ⟨5175980, by rfl⟩ : syracuseStep 6901307 = 10351961) B10351961
theorem B4091687 : Blo 1211423 4091687 := bstep (se 1 (by rfl) ⟨3068765, by rfl⟩ : syracuseStep 4091687 = 6137531) B6137531
theorem B31059773 : Blo 1211423 31059773 := bstep (se 3 (by rfl) ⟨5823707, by rfl⟩ : syracuseStep 31059773 = 11647415) B11647415
theorem B1363783 : Blo 1211423 1363783 := bstep (se 1 (by rfl) ⟨1022837, by rfl⟩ : syracuseStep 1363783 = 2045675) B2045675
theorem B6901625 : Blo 1211423 6901625 := bstep (se 2 (by rfl) ⟨2588109, by rfl⟩ : syracuseStep 6901625 = 5176219) B5176219
theorem B3068027 : Blo 1211423 3068027 := bstep (se 1 (by rfl) ⟨2301020, by rfl⟩ : syracuseStep 3068027 = 4602041) B4602041
theorem B4149377 : Blo 1211423 4149377 := bstep (se 2 (by rfl) ⟨1556016, by rfl⟩ : syracuseStep 4149377 = 3112033) B3112033
theorem B3887291 : Blo 1211423 3887291 := bstep (se 1 (by rfl) ⟨2915468, by rfl⟩ : syracuseStep 3887291 = 5830937) B5830937
theorem B6549769 : Blo 1211423 6549769 := bstep (se 2 (by rfl) ⟨2456163, by rfl⟩ : syracuseStep 6549769 = 4912327) B4912327
theorem B6549815 : Blo 1211423 6549815 := bstep (se 1 (by rfl) ⟨4912361, by rfl⟩ : syracuseStep 6549815 = 9824723) B9824723
theorem B10350935 : Blo 1211423 10350935 := bstep (se 1 (by rfl) ⟨7763201, by rfl⟩ : syracuseStep 10350935 = 15526403) B15526403
theorem B25555301 : Blo 1211423 25555301 := bstep (se 4 (by rfl) ⟨2395809, by rfl⟩ : syracuseStep 25555301 = 4791619) B4791619
theorem B5181823 : Blo 1211423 5181823 := bstep (se 1 (by rfl) ⟨3886367, by rfl⟩ : syracuseStep 5181823 = 7772735) B7772735
theorem B1364431 : Blo 1211423 1364431 := bstep (se 1 (by rfl) ⟨1023323, by rfl⟩ : syracuseStep 1364431 = 2046647) B2046647
theorem B1724905 : Blo 1211423 1724905 := bstep (se 2 (by rfl) ⟨646839, by rfl⟩ : syracuseStep 1724905 = 1293679) B1293679
theorem B4600583 : Blo 1211423 4600583 := bstep (se 1 (by rfl) ⟨3450437, by rfl⟩ : syracuseStep 4600583 = 6900875) B6900875
theorem B4092713 : Blo 1211423 4092713 := bstep (se 2 (by rfl) ⟨1534767, by rfl⟩ : syracuseStep 4092713 = 3069535) B3069535
theorem B4371241 : Blo 1211423 4371241 := bstep (se 2 (by rfl) ⟨1639215, by rfl⟩ : syracuseStep 4371241 = 3278431) B3278431
theorem B11653955 : Blo 1211423 11653955 := bstep (se 1 (by rfl) ⟨8740466, by rfl⟩ : syracuseStep 11653955 = 17480933) B17480933
theorem B3937319 : Blo 1211423 3937319 := bstep (se 1 (by rfl) ⟨2952989, by rfl⟩ : syracuseStep 3937319 = 5905979) B5905979
theorem B2913335 : Blo 1211423 2913335 := bstep (se 1 (by rfl) ⟨2185001, by rfl⟩ : syracuseStep 2913335 = 4370003) B4370003
theorem B4092983 : Blo 1211423 4092983 := bstep (se 1 (by rfl) ⟨3069737, by rfl⟩ : syracuseStep 4092983 = 6139475) B6139475
theorem B2045135 : Blo 1211423 2045135 := bstep (se 1 (by rfl) ⟨1533851, by rfl⟩ : syracuseStep 2045135 = 3067703) B3067703
theorem B6903083 : Blo 1211423 6903083 := bstep (se 1 (by rfl) ⟨5177312, by rfl⟩ : syracuseStep 6903083 = 10354625) B10354625
theorem B5821787 : Blo 1211423 5821787 := bstep (se 1 (by rfl) ⟨4366340, by rfl⟩ : syracuseStep 5821787 = 8732681) B8732681
theorem B31086017 : Blo 1211423 31086017 := bstep (se 2 (by rfl) ⟨11657256, by rfl⟩ : syracuseStep 31086017 = 23314513) B23314513
theorem B6903265 : Blo 1211423 6903265 := bstep (se 2 (by rfl) ⟨2588724, by rfl⟩ : syracuseStep 6903265 = 5177449) B5177449
theorem B110712365 : Blo 1211423 110712365 := bstep (se 3 (by rfl) ⟨20758568, by rfl⟩ : syracuseStep 110712365 = 41517137) B41517137
theorem B11654765 : Blo 1211423 11654765 := bstep (se 3 (by rfl) ⟨2185268, by rfl⟩ : syracuseStep 11654765 = 4370537) B4370537
theorem B13293179 : Blo 1211423 13293179 := bstep (se 1 (by rfl) ⟨9969884, by rfl⟩ : syracuseStep 13293179 = 19939769) B19939769
theorem B6141743 : Blo 1211423 6141743 := bstep (se 1 (by rfl) ⟨4606307, by rfl⟩ : syracuseStep 6141743 = 9212615) B9212615
theorem B29472605 : Blo 1211423 29472605 := bstep (se 3 (by rfl) ⟨5526113, by rfl⟩ : syracuseStep 29472605 = 11052227) B11052227
theorem B17487731 : Blo 1211423 17487731 := bstep (se 1 (by rfl) ⟨13115798, by rfl⟩ : syracuseStep 17487731 = 26231597) B26231597
theorem B6903791 : Blo 1211423 6903791 := bstep (se 1 (by rfl) ⟨5177843, by rfl⟩ : syracuseStep 6903791 = 10355687) B10355687
theorem B2045945 : Blo 1211423 2045945 := bstep (se 2 (by rfl) ⟨767229, by rfl⟩ : syracuseStep 2045945 = 1534459) B1534459
theorem B2046107 : Blo 1211423 2046107 := bstep (se 1 (by rfl) ⟨1534580, by rfl⟩ : syracuseStep 2046107 = 3069161) B3069161
theorem B2914537 : Blo 1211423 2914537 := bstep (se 2 (by rfl) ⟨1092951, by rfl⟩ : syracuseStep 2914537 = 2185903) B2185903
theorem B2046215 : Blo 1211423 2046215 := bstep (se 1 (by rfl) ⟨1534661, by rfl⟩ : syracuseStep 2046215 = 3069323) B3069323
theorem B1817225 : Blo 1211423 1817225 := bstep (se 2 (by rfl) ⟨681459, by rfl⟩ : syracuseStep 1817225 = 1362919) B1362919
theorem B8739485 : Blo 1211423 8739485 := bstep (se 3 (by rfl) ⟨1638653, by rfl⟩ : syracuseStep 8739485 = 3277307) B3277307
theorem B6904541 : Blo 1211423 6904541 := bstep (se 3 (by rfl) ⟨1294601, by rfl⟩ : syracuseStep 6904541 = 2589203) B2589203
theorem B1817399 : Blo 1211423 1817399 := bstep (se 1 (by rfl) ⟨1363049, by rfl⟩ : syracuseStep 1817399 = 2726099) B2726099
theorem B2046775 : Blo 1211423 2046775 := bstep (se 1 (by rfl) ⟨1535081, by rfl⟩ : syracuseStep 2046775 = 3070163) B3070163
theorem B3881807 : Blo 1211423 3881807 := bstep (se 1 (by rfl) ⟨2911355, by rfl⟩ : syracuseStep 3881807 = 5822711) B5822711
theorem B1817435 : Blo 1211423 1817435 := bstep (se 1 (by rfl) ⟨1363076, by rfl⟩ : syracuseStep 1817435 = 2726153) B2726153
theorem B2726747 : Blo 1211423 2726747 := bstep (se 1 (by rfl) ⟨2045060, by rfl⟩ : syracuseStep 2726747 = 4090121) B4090121
theorem B3070811 : Blo 1211423 3070811 := bstep (se 1 (by rfl) ⟨2303108, by rfl⟩ : syracuseStep 3070811 = 4606217) B4606217
theorem B2333647 : Blo 1211423 2333647 := bstep (se 1 (by rfl) ⟨1750235, by rfl⟩ : syracuseStep 2333647 = 3500471) B3500471
theorem B4094927 : Blo 1211423 4094927 := bstep (se 1 (by rfl) ⟨3071195, by rfl⟩ : syracuseStep 4094927 = 6142391) B6142391
theorem B1817579 : Blo 1211423 1817579 := bstep (se 1 (by rfl) ⟨1363184, by rfl⟩ : syracuseStep 1817579 = 2726369) B2726369
theorem B5528557 : Blo 1211423 5528557 := bstep (se 3 (by rfl) ⟨1036604, by rfl⟩ : syracuseStep 5528557 = 2073209) B2073209
theorem B1211439 : Blo 1211423 1211439 := bstep (se 1 (by rfl) ⟨908579, by rfl⟩ : syracuseStep 1211439 = 1817159) B1817159
theorem B1211463 : Blo 1211423 1211463 := bstep (se 1 (by rfl) ⟨908597, by rfl⟩ : syracuseStep 1211463 = 1817195) B1817195
theorem B21576775 : Blo 1211423 21576775 := bstep (se 1 (by rfl) ⟨16182581, by rfl⟩ : syracuseStep 21576775 = 32365163) B32365163
theorem B3071105 : Blo 1211423 3071105 := bstep (se 2 (by rfl) ⟨1151664, by rfl⟩ : syracuseStep 3071105 = 2303329) B2303329
theorem B1817783 : Blo 1211423 1817783 := bstep (se 1 (by rfl) ⟨1363337, by rfl⟩ : syracuseStep 1817783 = 2726675) B2726675
theorem B1211615 : Blo 1211423 1211615 := bstep (se 1 (by rfl) ⟨908711, by rfl⟩ : syracuseStep 1211615 = 1817423) B1817423
theorem B2047241 : Blo 1211423 2047241 := bstep (se 2 (by rfl) ⟨767715, by rfl⟩ : syracuseStep 2047241 = 1535431) B1535431
theorem B13802885 : Blo 1211423 13802885 := bstep (se 4 (by rfl) ⟨1294020, by rfl⟩ : syracuseStep 13802885 = 2588041) B2588041
theorem B6905249 : Blo 1211423 6905249 := bstep (se 2 (by rfl) ⟨2589468, by rfl⟩ : syracuseStep 6905249 = 5178937) B5178937
theorem B1818023 : Blo 1211423 1818023 := bstep (se 1 (by rfl) ⟨1363517, by rfl⟩ : syracuseStep 1818023 = 2727035) B2727035
theorem B4914599 : Blo 1211423 4914599 := bstep (se 1 (by rfl) ⟨3685949, by rfl⟩ : syracuseStep 4914599 = 7371899) B7371899
theorem B49741249 : Blo 1211423 49741249 := bstep (se 2 (by rfl) ⟨18652968, by rfl⟩ : syracuseStep 49741249 = 37305937) B37305937
theorem B4603331 : Blo 1211423 4603331 := bstep (se 1 (by rfl) ⟨3452498, by rfl⟩ : syracuseStep 4603331 = 6904997) B6904997
theorem B1211879 : Blo 1211423 1211879 := bstep (se 1 (by rfl) ⟨908909, by rfl⟩ : syracuseStep 1211879 = 1817819) B1817819
theorem B8289773 : Blo 1211423 8289773 := bstep (se 3 (by rfl) ⟨1554332, by rfl⟩ : syracuseStep 8289773 = 3108665) B3108665
theorem B1818107 : Blo 1211423 1818107 := bstep (se 1 (by rfl) ⟨1363580, by rfl⟩ : syracuseStep 1818107 = 2727161) B2727161
theorem B3882575 : Blo 1211423 3882575 := bstep (se 1 (by rfl) ⟨2911931, by rfl⟩ : syracuseStep 3882575 = 5823863) B5823863
theorem B2727503 : Blo 1211423 2727503 := bstep (se 1 (by rfl) ⟨2045627, by rfl⟩ : syracuseStep 2727503 = 4091255) B4091255
theorem B1211995 : Blo 1211423 1211995 := bstep (se 1 (by rfl) ⟨908996, by rfl⟩ : syracuseStep 1211995 = 1817993) B1817993
theorem B1818203 : Blo 1211423 1818203 := bstep (se 1 (by rfl) ⟨1363652, by rfl⟩ : syracuseStep 1818203 = 2727305) B2727305
theorem B1818287 : Blo 1211423 1818287 := bstep (se 1 (by rfl) ⟨1363715, by rfl⟩ : syracuseStep 1818287 = 2727431) B2727431
theorem B3276521 : Blo 1211423 3276521 := bstep (se 2 (by rfl) ⟨1228695, by rfl⟩ : syracuseStep 3276521 = 2457391) B2457391
theorem B1818407 : Blo 1211423 1818407 := bstep (se 1 (by rfl) ⟨1363805, by rfl⟩ : syracuseStep 1818407 = 2727611) B2727611
theorem B1556263 : Blo 1211423 1556263 := bstep (se 1 (by rfl) ⟨1167197, by rfl⟩ : syracuseStep 1556263 = 2334395) B2334395
theorem B1212231 : Blo 1211423 1212231 := bstep (se 1 (by rfl) ⟨909173, by rfl⟩ : syracuseStep 1212231 = 1818347) B1818347
theorem B1818491 : Blo 1211423 1818491 := bstep (se 1 (by rfl) ⟨1363868, by rfl⟩ : syracuseStep 1818491 = 2727737) B2727737
theorem B252174221 : Blo 1211423 252174221 := bstep (se 3 (by rfl) ⟨47282666, by rfl⟩ : syracuseStep 252174221 = 94565333) B94565333
theorem B1941403 : Blo 1211423 1941403 := bstep (se 1 (by rfl) ⟨1456052, by rfl⟩ : syracuseStep 1941403 = 2912105) B2912105
theorem B1212383 : Blo 1211423 1212383 := bstep (se 1 (by rfl) ⟨909287, by rfl⟩ : syracuseStep 1212383 = 1818575) B1818575
theorem B1818815 : Blo 1211423 1818815 := bstep (se 1 (by rfl) ⟨1364111, by rfl⟩ : syracuseStep 1818815 = 2728223) B2728223
theorem B1212607 : Blo 1211423 1212607 := bstep (se 1 (by rfl) ⟨909455, by rfl⟩ : syracuseStep 1212607 = 1818911) B1818911
theorem B4366543 : Blo 1211423 4366543 := bstep (se 1 (by rfl) ⟨3274907, by rfl⟩ : syracuseStep 4366543 = 6549815) B6549815
theorem B1212623 : Blo 1211423 1212623 := bstep (se 1 (by rfl) ⟨909467, by rfl⟩ : syracuseStep 1212623 = 1818935) B1818935
theorem B1212671 : Blo 1211423 1212671 := bstep (se 1 (by rfl) ⟨909503, by rfl⟩ : syracuseStep 1212671 = 1819007) B1819007
theorem B1212719 : Blo 1211423 1212719 := bstep (se 1 (by rfl) ⟨909539, by rfl⟩ : syracuseStep 1212719 = 1819079) B1819079
theorem B8733025 : Blo 1211423 8733025 := bstep (se 2 (by rfl) ⟨3274884, by rfl⟩ : syracuseStep 8733025 = 6549769) B6549769
theorem B2728475 : Blo 1211423 2728475 := bstep (se 1 (by rfl) ⟨2046356, by rfl⟩ : syracuseStep 2728475 = 4092713) B4092713
theorem B1212955 : Blo 1211423 1212955 := bstep (se 1 (by rfl) ⟨909716, by rfl⟩ : syracuseStep 1212955 = 1819433) B1819433
theorem B1212959 : Blo 1211423 1212959 := bstep (se 1 (by rfl) ⟨909719, by rfl⟩ : syracuseStep 1212959 = 1819439) B1819439
theorem B3277417 : Blo 1211423 3277417 := bstep (se 2 (by rfl) ⟨1229031, by rfl⟩ : syracuseStep 3277417 = 2458063) B2458063
theorem B1819241 : Blo 1211423 1819241 := bstep (se 2 (by rfl) ⟨682215, by rfl⟩ : syracuseStep 1819241 = 1364431) B1364431
theorem B1819247 : Blo 1211423 1819247 := bstep (se 1 (by rfl) ⟨1364435, by rfl⟩ : syracuseStep 1819247 = 2728871) B2728871
theorem B1213039 : Blo 1211423 1213039 := bstep (se 1 (by rfl) ⟨909779, by rfl⟩ : syracuseStep 1213039 = 1819559) B1819559
theorem B1213095 : Blo 1211423 1213095 := bstep (se 1 (by rfl) ⟨909821, by rfl⟩ : syracuseStep 1213095 = 1819643) B1819643
theorem B1942223 : Blo 1211423 1942223 := bstep (se 1 (by rfl) ⟨1456667, by rfl⟩ : syracuseStep 1942223 = 2913335) B2913335
theorem B2728655 : Blo 1211423 2728655 := bstep (se 1 (by rfl) ⟨2046491, by rfl⟩ : syracuseStep 2728655 = 4092983) B4092983
theorem B1213135 : Blo 1211423 1213135 := bstep (se 1 (by rfl) ⟨909851, by rfl⟩ : syracuseStep 1213135 = 1819703) B1819703
theorem B1213215 : Blo 1211423 1213215 := bstep (se 1 (by rfl) ⟨909911, by rfl⟩ : syracuseStep 1213215 = 1819823) B1819823
theorem B2729033 : Blo 1211423 2729033 := bstep (se 2 (by rfl) ⟨1023387, by rfl⟩ : syracuseStep 2729033 = 2046775) B2046775
theorem B2589887 : Blo 1211423 2589887 := bstep (se 1 (by rfl) ⟨1942415, by rfl⟩ : syracuseStep 2589887 = 3884831) B3884831
theorem B1819871 : Blo 1211423 1819871 := bstep (se 1 (by rfl) ⟨1364903, by rfl⟩ : syracuseStep 1819871 = 2729807) B2729807
theorem B3884267 : Blo 1211423 3884267 := bstep (se 1 (by rfl) ⟨2913200, by rfl⟩ : syracuseStep 3884267 = 5826401) B5826401
theorem B1819883 : Blo 1211423 1819883 := bstep (se 1 (by rfl) ⟨1364912, by rfl⟩ : syracuseStep 1819883 = 2729825) B2729825
theorem B11658487 : Blo 1211423 11658487 := bstep (se 1 (by rfl) ⟨8743865, by rfl⟩ : syracuseStep 11658487 = 17487731) B17487731
theorem B1295695 : Blo 1211423 1295695 := bstep (se 1 (by rfl) ⟨971771, by rfl⟩ : syracuseStep 1295695 = 1943543) B1943543
theorem B19653977 : Blo 1211423 19653977 := bstep (se 2 (by rfl) ⟨7370241, by rfl⟩ : syracuseStep 19653977 = 14740483) B14740483
theorem B11658761 : Blo 1211423 11658761 := bstep (se 2 (by rfl) ⟨4372035, by rfl⟩ : syracuseStep 11658761 = 8744071) B8744071
theorem B5826323 : Blo 1211423 5826323 := bstep (se 1 (by rfl) ⟨4369742, by rfl⟩ : syracuseStep 5826323 = 8739485) B8739485
theorem B3278735 : Blo 1211423 3278735 := bstep (se 1 (by rfl) ⟨2459051, by rfl⟩ : syracuseStep 3278735 = 4918103) B4918103
theorem B2729951 : Blo 1211423 2729951 := bstep (se 1 (by rfl) ⟨2047463, by rfl⟩ : syracuseStep 2729951 = 4094927) B4094927
theorem B10635419 : Blo 1211423 10635419 := bstep (se 1 (by rfl) ⟨7976564, by rfl⟩ : syracuseStep 10635419 = 15953129) B15953129
theorem B9201923 : Blo 1211423 9201923 := bstep (se 1 (by rfl) ⟨6901442, by rfl⟩ : syracuseStep 9201923 = 13802885) B13802885
theorem B2075017 : Blo 1211423 2075017 := bstep (se 2 (by rfl) ⟨778131, by rfl⟩ : syracuseStep 2075017 = 1556263) B1556263
theorem B2493089 : Blo 1211423 2493089 := bstep (se 2 (by rfl) ⟨934908, by rfl⟩ : syracuseStep 2493089 = 1869817) B1869817
theorem B2591527 : Blo 1211423 2591527 := bstep (se 1 (by rfl) ⟨1943645, by rfl⟩ : syracuseStep 2591527 = 3887291) B3887291
theorem B6900623 : Blo 1211423 6900623 := bstep (se 1 (by rfl) ⟨5175467, by rfl⟩ : syracuseStep 6900623 = 10350935) B10350935
theorem B3886049 : Blo 1211423 3886049 := bstep (se 2 (by rfl) ⟨1457268, by rfl⟩ : syracuseStep 3886049 = 2914537) B2914537
theorem B6909097 : Blo 1211423 6909097 := bstep (se 2 (by rfl) ⟨2590911, by rfl⟩ : syracuseStep 6909097 = 5181823) B5181823
theorem B3067055 : Blo 1211423 3067055 := bstep (se 1 (by rfl) ⟨2300291, by rfl⟩ : syracuseStep 3067055 = 4600583) B4600583
theorem B7769303 : Blo 1211423 7769303 := bstep (se 1 (by rfl) ⟨5826977, by rfl⟩ : syracuseStep 7769303 = 11653955) B11653955
theorem B2624879 : Blo 1211423 2624879 := bstep (se 1 (by rfl) ⟨1968659, by rfl⟩ : syracuseStep 2624879 = 3937319) B3937319
theorem B1363423 : Blo 1211423 1363423 := bstep (se 1 (by rfl) ⟨1022567, by rfl⟩ : syracuseStep 1363423 = 2045135) B2045135
theorem B37334519 : Blo 1211423 37334519 := bstep (se 1 (by rfl) ⟨28000889, by rfl⟩ : syracuseStep 37334519 = 56001779) B56001779
theorem B5828321 : Blo 1211423 5828321 := bstep (se 2 (by rfl) ⟨2185620, by rfl⟩ : syracuseStep 5828321 = 4371241) B4371241
theorem B7769843 : Blo 1211423 7769843 := bstep (se 1 (by rfl) ⟨5827382, by rfl⟩ : syracuseStep 7769843 = 11654765) B11654765
theorem B2764535 : Blo 1211423 2764535 := bstep (se 1 (by rfl) ⟨2073401, by rfl⟩ : syracuseStep 2764535 = 4146803) B4146803
theorem B19648403 : Blo 1211423 19648403 := bstep (se 1 (by rfl) ⟨14736302, by rfl⟩ : syracuseStep 19648403 = 29472605) B29472605
theorem B1363963 : Blo 1211423 1363963 := bstep (se 1 (by rfl) ⟨1022972, by rfl⟩ : syracuseStep 1363963 = 2045945) B2045945
theorem B1364071 : Blo 1211423 1364071 := bstep (se 1 (by rfl) ⟨1023053, by rfl⟩ : syracuseStep 1364071 = 2046107) B2046107
theorem B1364143 : Blo 1211423 1364143 := bstep (se 1 (by rfl) ⟨1023107, by rfl⟩ : syracuseStep 1364143 = 2046215) B2046215
theorem B44233123 : Blo 1211423 44233123 := bstep (se 1 (by rfl) ⟨33174842, by rfl⟩ : syracuseStep 44233123 = 66349685) B66349685
theorem B13799969 : Blo 1211423 13799969 := bstep (se 2 (by rfl) ⟨5174988, by rfl⟩ : syracuseStep 13799969 = 10349977) B10349977
theorem B5534287 : Blo 1211423 5534287 := bstep (se 1 (by rfl) ⟨4150715, by rfl⟩ : syracuseStep 5534287 = 8301431) B8301431
theorem B9204353 : Blo 1211423 9204353 := bstep (se 2 (by rfl) ⟨3451632, by rfl⟩ : syracuseStep 9204353 = 6903265) B6903265
theorem B1364827 : Blo 1211423 1364827 := bstep (se 1 (by rfl) ⟨1023620, by rfl⟩ : syracuseStep 1364827 = 2047241) B2047241
theorem B3068887 : Blo 1211423 3068887 := bstep (se 1 (by rfl) ⟨2301665, by rfl⟩ : syracuseStep 3068887 = 4603331) B4603331
theorem B5526515 : Blo 1211423 5526515 := bstep (se 1 (by rfl) ⟨4144886, by rfl⟩ : syracuseStep 5526515 = 8289773) B8289773
theorem B4600871 : Blo 1211423 4600871 := bstep (se 1 (by rfl) ⟨3450653, by rfl⟩ : syracuseStep 4600871 = 6901307) B6901307
theorem B13808717 : Blo 1211423 13808717 := bstep (se 3 (by rfl) ⟨2589134, by rfl⟩ : syracuseStep 13808717 = 5178269) B5178269
theorem B2184347 : Blo 1211423 2184347 := bstep (se 1 (by rfl) ⟨1638260, by rfl⟩ : syracuseStep 2184347 = 3276521) B3276521
theorem B20706515 : Blo 1211423 20706515 := bstep (se 1 (by rfl) ⟨15529886, by rfl⟩ : syracuseStep 20706515 = 31059773) B31059773
theorem B4601083 : Blo 1211423 4601083 := bstep (se 1 (by rfl) ⟨3450812, by rfl⟩ : syracuseStep 4601083 = 6901625) B6901625
theorem B2045351 : Blo 1211423 2045351 := bstep (se 1 (by rfl) ⟨1534013, by rfl⟩ : syracuseStep 2045351 = 3068027) B3068027
theorem B2766251 : Blo 1211423 2766251 := bstep (se 1 (by rfl) ⟨2074688, by rfl⟩ : syracuseStep 2766251 = 4149377) B4149377
theorem B17036867 : Blo 1211423 17036867 := bstep (se 1 (by rfl) ⟨12777650, by rfl⟩ : syracuseStep 17036867 = 25555301) B25555301
theorem B2725703 : Blo 1211423 2725703 := bstep (se 1 (by rfl) ⟨2044277, by rfl⟩ : syracuseStep 2725703 = 4088555) B4088555
theorem B10360709 : Blo 1211423 10360709 := bstep (se 4 (by rfl) ⟨971316, by rfl⟩ : syracuseStep 10360709 = 1942633) B1942633
theorem B4602055 : Blo 1211423 4602055 := bstep (se 1 (by rfl) ⟨3451541, by rfl⟩ : syracuseStep 4602055 = 6903083) B6903083
theorem B3881191 : Blo 1211423 3881191 := bstep (se 1 (by rfl) ⟨2910893, by rfl⟩ : syracuseStep 3881191 = 5821787) B5821787
theorem B20724011 : Blo 1211423 20724011 := bstep (se 1 (by rfl) ⟨15543008, by rfl⟩ : syracuseStep 20724011 = 31086017) B31086017
theorem B73808243 : Blo 1211423 73808243 := bstep (se 1 (by rfl) ⟨55356182, by rfl⟩ : syracuseStep 73808243 = 110712365) B110712365
theorem B6904223 : Blo 1211423 6904223 := bstep (se 1 (by rfl) ⟨5178167, by rfl⟩ : syracuseStep 6904223 = 10356335) B10356335
theorem B8862119 : Blo 1211423 8862119 := bstep (se 1 (by rfl) ⟨6646589, by rfl⟩ : syracuseStep 8862119 = 13293179) B13293179
theorem B13105597 : Blo 1211423 13105597 := bstep (se 3 (by rfl) ⟨2457299, by rfl⟩ : syracuseStep 13105597 = 4914599) B4914599
theorem B4094495 : Blo 1211423 4094495 := bstep (se 1 (by rfl) ⟨3070871, by rfl⟩ : syracuseStep 4094495 = 6141743) B6141743
theorem B2046505 : Blo 1211423 2046505 := bstep (se 2 (by rfl) ⟨767439, by rfl⟩ : syracuseStep 2046505 = 1534879) B1534879
theorem B3111529 : Blo 1211423 3111529 := bstep (se 2 (by rfl) ⟨1166823, by rfl⟩ : syracuseStep 3111529 = 2333647) B2333647
theorem B7371409 : Blo 1211423 7371409 := bstep (se 2 (by rfl) ⟨2764278, by rfl⟩ : syracuseStep 7371409 = 5528557) B5528557
theorem B4602527 : Blo 1211423 4602527 := bstep (se 1 (by rfl) ⟨3451895, by rfl⟩ : syracuseStep 4602527 = 6903791) B6903791
theorem B1817321 : Blo 1211423 1817321 := bstep (se 2 (by rfl) ⟨681495, by rfl⟩ : syracuseStep 1817321 = 1362991) B1362991
theorem B28769033 : Blo 1211423 28769033 := bstep (se 2 (by rfl) ⟨10788387, by rfl⟩ : syracuseStep 28769033 = 21576775) B21576775
theorem B2726711 : Blo 1211423 2726711 := bstep (se 1 (by rfl) ⟨2045033, by rfl⟩ : syracuseStep 2726711 = 4090067) B4090067
theorem B3070831 : Blo 1211423 3070831 := bstep (se 1 (by rfl) ⟨2303123, by rfl⟩ : syracuseStep 3070831 = 4606247) B4606247
theorem B2726891 : Blo 1211423 2726891 := bstep (se 1 (by rfl) ⟨2045168, by rfl⟩ : syracuseStep 2726891 = 4090337) B4090337
theorem B1211483 : Blo 1211423 1211483 := bstep (se 1 (by rfl) ⟨908612, by rfl⟩ : syracuseStep 1211483 = 1817225) B1817225
theorem B1817705 : Blo 1211423 1817705 := bstep (se 2 (by rfl) ⟨681639, by rfl⟩ : syracuseStep 1817705 = 1363279) B1363279
theorem B4603027 : Blo 1211423 4603027 := bstep (se 1 (by rfl) ⟨3452270, by rfl⟩ : syracuseStep 4603027 = 6904541) B6904541
theorem B1211599 : Blo 1211423 1211599 := bstep (se 1 (by rfl) ⟨908699, by rfl⟩ : syracuseStep 1211599 = 1817399) B1817399
theorem B2587871 : Blo 1211423 2587871 := bstep (se 1 (by rfl) ⟨1940903, by rfl⟩ : syracuseStep 2587871 = 3881807) B3881807
theorem B1211623 : Blo 1211423 1211623 := bstep (se 1 (by rfl) ⟨908717, by rfl⟩ : syracuseStep 1211623 = 1817435) B1817435
theorem B1817831 : Blo 1211423 1817831 := bstep (se 1 (by rfl) ⟨1363373, by rfl⟩ : syracuseStep 1817831 = 2726747) B2726747
theorem B2047207 : Blo 1211423 2047207 := bstep (se 1 (by rfl) ⟨1535405, by rfl⟩ : syracuseStep 2047207 = 3070811) B3070811
theorem B66321665 : Blo 1211423 66321665 := bstep (se 2 (by rfl) ⟨24870624, by rfl⟩ : syracuseStep 66321665 = 49741249) B49741249
theorem B1211719 : Blo 1211423 1211719 := bstep (se 1 (by rfl) ⟨908789, by rfl⟩ : syracuseStep 1211719 = 1817579) B1817579
theorem B2047403 : Blo 1211423 2047403 := bstep (se 1 (by rfl) ⟨1535552, by rfl⟩ : syracuseStep 2047403 = 3071105) B3071105
theorem B1211855 : Blo 1211423 1211855 := bstep (se 1 (by rfl) ⟨908891, by rfl⟩ : syracuseStep 1211855 = 1817783) B1817783
theorem B3071479 : Blo 1211423 3071479 := bstep (se 1 (by rfl) ⟨2303609, by rfl⟩ : syracuseStep 3071479 = 4607219) B4607219
theorem B4603499 : Blo 1211423 4603499 := bstep (se 1 (by rfl) ⟨3452624, by rfl⟩ : syracuseStep 4603499 = 6905249) B6905249
theorem B1212015 : Blo 1211423 1212015 := bstep (se 1 (by rfl) ⟨909011, by rfl⟩ : syracuseStep 1212015 = 1818023) B1818023
theorem B1212071 : Blo 1211423 1212071 := bstep (se 1 (by rfl) ⟨909053, by rfl⟩ : syracuseStep 1212071 = 1818107) B1818107
theorem B2588383 : Blo 1211423 2588383 := bstep (se 1 (by rfl) ⟨1941287, by rfl⟩ : syracuseStep 2588383 = 3882575) B3882575
theorem B1818335 : Blo 1211423 1818335 := bstep (se 1 (by rfl) ⟨1363751, by rfl⟩ : syracuseStep 1818335 = 2727503) B2727503
theorem B1212135 : Blo 1211423 1212135 := bstep (se 1 (by rfl) ⟨909101, by rfl⟩ : syracuseStep 1212135 = 1818203) B1818203
theorem B1818377 : Blo 1211423 1818377 := bstep (se 2 (by rfl) ⟨681891, by rfl⟩ : syracuseStep 1818377 = 1363783) B1363783
theorem B1212191 : Blo 1211423 1212191 := bstep (se 1 (by rfl) ⟨909143, by rfl⟩ : syracuseStep 1212191 = 1818287) B1818287
theorem B1212271 : Blo 1211423 1212271 := bstep (se 1 (by rfl) ⟨909203, by rfl⟩ : syracuseStep 1212271 = 1818407) B1818407
theorem B2727791 : Blo 1211423 2727791 := bstep (se 1 (by rfl) ⟨2045843, by rfl⟩ : syracuseStep 2727791 = 4091687) B4091687
theorem B2588537 : Blo 1211423 2588537 := bstep (se 2 (by rfl) ⟨970701, by rfl⟩ : syracuseStep 2588537 = 1941403) B1941403
theorem B9199493 : Blo 1211423 9199493 := bstep (se 4 (by rfl) ⟨862452, by rfl⟩ : syracuseStep 9199493 = 1724905) B1724905
theorem B1212327 : Blo 1211423 1212327 := bstep (se 1 (by rfl) ⟨909245, by rfl⟩ : syracuseStep 1212327 = 1818491) B1818491
theorem B168116147 : Blo 1211423 168116147 := bstep (se 1 (by rfl) ⟨126087110, by rfl⟩ : syracuseStep 168116147 = 252174221) B252174221
theorem B1212543 : Blo 1211423 1212543 := bstep (se 1 (by rfl) ⟨909407, by rfl⟩ : syracuseStep 1212543 = 1818815) B1818815
theorem B1818761 : Blo 1211423 1818761 := bstep (se 2 (by rfl) ⟨682035, by rfl⟩ : syracuseStep 1818761 = 1364071) B1364071
theorem B1818857 : Blo 1211423 1818857 := bstep (se 2 (by rfl) ⟨682071, by rfl⟩ : syracuseStep 1818857 = 1364143) B1364143
theorem B6136073 : Blo 1211423 6136073 := bstep (se 2 (by rfl) ⟨2301027, by rfl⟩ : syracuseStep 6136073 = 4602055) B4602055
theorem B1818983 : Blo 1211423 1818983 := bstep (se 1 (by rfl) ⟨1364237, by rfl⟩ : syracuseStep 1818983 = 2728475) B2728475
theorem B9199979 : Blo 1211423 9199979 := bstep (se 1 (by rfl) ⟨6899984, by rfl⟩ : syracuseStep 9199979 = 13799969) B13799969
theorem B1212827 : Blo 1211423 1212827 := bstep (se 1 (by rfl) ⟨909620, by rfl⟩ : syracuseStep 1212827 = 1819241) B1819241
theorem B28361117 : Blo 1211423 28361117 := bstep (se 3 (by rfl) ⟨5317709, by rfl⟩ : syracuseStep 28361117 = 10635419) B10635419
theorem B1212831 : Blo 1211423 1212831 := bstep (se 1 (by rfl) ⟨909623, by rfl⟩ : syracuseStep 1212831 = 1819247) B1819247
theorem B29516197 : Blo 1211423 29516197 := bstep (se 4 (by rfl) ⟨2767143, by rfl⟩ : syracuseStep 29516197 = 5534287) B5534287
theorem B6136235 : Blo 1211423 6136235 := bstep (se 1 (by rfl) ⟨4602176, by rfl⟩ : syracuseStep 6136235 = 9204353) B9204353
theorem B1819103 : Blo 1211423 1819103 := bstep (se 1 (by rfl) ⟨1364327, by rfl⟩ : syracuseStep 1819103 = 2728655) B2728655
theorem B17474129 : Blo 1211423 17474129 := bstep (se 2 (by rfl) ⟨6552798, by rfl⟩ : syracuseStep 17474129 = 13105597) B13105597
theorem B1819355 : Blo 1211423 1819355 := bstep (se 1 (by rfl) ⟨1364516, by rfl⟩ : syracuseStep 1819355 = 2729033) B2729033
theorem B2728673 : Blo 1211423 2728673 := bstep (se 2 (by rfl) ⟨1023252, by rfl⟩ : syracuseStep 2728673 = 2046505) B2046505
theorem B13804343 : Blo 1211423 13804343 := bstep (se 1 (by rfl) ⟨10353257, by rfl⟩ : syracuseStep 13804343 = 20706515) B20706515
theorem B1213247 : Blo 1211423 1213247 := bstep (se 1 (by rfl) ⟨909935, by rfl⟩ : syracuseStep 1213247 = 1819871) B1819871
theorem B2589511 : Blo 1211423 2589511 := bstep (se 1 (by rfl) ⟨1942133, by rfl⟩ : syracuseStep 2589511 = 3884267) B3884267
theorem B1213255 : Blo 1211423 1213255 := bstep (se 1 (by rfl) ⟨909941, by rfl⟩ : syracuseStep 1213255 = 1819883) B1819883
theorem B1819769 : Blo 1211423 1819769 := bstep (se 2 (by rfl) ⟨682413, by rfl⟩ : syracuseStep 1819769 = 1364827) B1364827
theorem B3884215 : Blo 1211423 3884215 := bstep (se 1 (by rfl) ⟨2913161, by rfl⟩ : syracuseStep 3884215 = 5826323) B5826323
theorem B6907139 : Blo 1211423 6907139 := bstep (se 1 (by rfl) ⟨5180354, by rfl⟩ : syracuseStep 6907139 = 10360709) B10360709
theorem B1819967 : Blo 1211423 1819967 := bstep (se 1 (by rfl) ⟨1364975, by rfl⟩ : syracuseStep 1819967 = 2729951) B2729951
theorem B6137369 : Blo 1211423 6137369 := bstep (se 2 (by rfl) ⟨2301513, by rfl⟩ : syracuseStep 6137369 = 4603027) B4603027
theorem B5908079 : Blo 1211423 5908079 := bstep (se 1 (by rfl) ⟨4431059, by rfl⟩ : syracuseStep 5908079 = 8862119) B8862119
theorem B2729609 : Blo 1211423 2729609 := bstep (se 2 (by rfl) ⟨1023603, by rfl⟩ : syracuseStep 2729609 = 2047207) B2047207
theorem B2729663 : Blo 1211423 2729663 := bstep (se 1 (by rfl) ⟨2047247, by rfl⟩ : syracuseStep 2729663 = 4094495) B4094495
theorem B19179355 : Blo 1211423 19179355 := bstep (se 1 (by rfl) ⟨14384516, by rfl⟩ : syracuseStep 19179355 = 28769033) B28769033
theorem B5179261 : Blo 1211423 5179261 := bstep (se 3 (by rfl) ⟨971111, by rfl⟩ : syracuseStep 5179261 = 1942223) B1942223
theorem B15542189 : Blo 1211423 15542189 := bstep (se 3 (by rfl) ⟨2914160, by rfl⟩ : syracuseStep 15542189 = 5828321) B5828321
theorem B2590699 : Blo 1211423 2590699 := bstep (se 1 (by rfl) ⟨1943024, by rfl⟩ : syracuseStep 2590699 = 3886049) B3886049
theorem B5179535 : Blo 1211423 5179535 := bstep (se 1 (by rfl) ⟨3884651, by rfl⟩ : syracuseStep 5179535 = 7769303) B7769303
theorem B44214443 : Blo 1211423 44214443 := bstep (se 1 (by rfl) ⟨33160832, by rfl⟩ : syracuseStep 44214443 = 66321665) B66321665
theorem B3451177 : Blo 1211423 3451177 := bstep (se 2 (by rfl) ⟨1294191, by rfl⟩ : syracuseStep 3451177 = 2588383) B2588383
theorem B24889679 : Blo 1211423 24889679 := bstep (se 1 (by rfl) ⟨18667259, by rfl⟩ : syracuseStep 24889679 = 37334519) B37334519
theorem B5179895 : Blo 1211423 5179895 := bstep (se 1 (by rfl) ⟨3884921, by rfl⟩ : syracuseStep 5179895 = 7769843) B7769843
theorem B112077431 : Blo 1211423 112077431 := bstep (se 1 (by rfl) ⟨84058073, by rfl⟩ : syracuseStep 112077431 = 168116147) B168116147
theorem B11644033 : Blo 1211423 11644033 := bstep (se 2 (by rfl) ⟨4366512, by rfl⟩ : syracuseStep 11644033 = 8733025) B8733025
theorem B58977497 : Blo 1211423 58977497 := bstep (se 2 (by rfl) ⟨22116561, by rfl⟩ : syracuseStep 58977497 = 44233123) B44233123
theorem B3067247 : Blo 1211423 3067247 := bstep (se 1 (by rfl) ⟨2300435, by rfl⟩ : syracuseStep 3067247 = 4600871) B4600871
theorem B4369889 : Blo 1211423 4369889 := bstep (se 2 (by rfl) ⟨1638708, by rfl⟩ : syracuseStep 4369889 = 3277417) B3277417
theorem B4148705 : Blo 1211423 4148705 := bstep (se 2 (by rfl) ⟨1555764, by rfl⟩ : syracuseStep 4148705 = 3111529) B3111529
theorem B13102651 : Blo 1211423 13102651 := bstep (se 1 (by rfl) ⟨9826988, by rfl⟩ : syracuseStep 13102651 = 19653977) B19653977
theorem B1363567 : Blo 1211423 1363567 := bstep (se 1 (by rfl) ⟨1022675, by rfl⟩ : syracuseStep 1363567 = 2045351) B2045351
theorem B11357911 : Blo 1211423 11357911 := bstep (se 1 (by rfl) ⟨8518433, by rfl⟩ : syracuseStep 11357911 = 17036867) B17036867
theorem B7376669 : Blo 1211423 7376669 := bstep (se 3 (by rfl) ⟨1383125, by rfl⟩ : syracuseStep 7376669 = 2766251) B2766251
theorem B4091849 : Blo 1211423 4091849 := bstep (se 2 (by rfl) ⟨1534443, by rfl⟩ : syracuseStep 4091849 = 3068887) B3068887
theorem B13816007 : Blo 1211423 13816007 := bstep (se 1 (by rfl) ⟨10362005, by rfl⟩ : syracuseStep 13816007 = 20724011) B20724011
theorem B9212129 : Blo 1211423 9212129 := bstep (se 2 (by rfl) ⟨3454548, by rfl⟩ : syracuseStep 9212129 = 6909097) B6909097
theorem B49205495 : Blo 1211423 49205495 := bstep (se 1 (by rfl) ⟨36904121, by rfl⟩ : syracuseStep 49205495 = 73808243) B73808243
theorem B15544649 : Blo 1211423 15544649 := bstep (se 2 (by rfl) ⟨5829243, by rfl⟩ : syracuseStep 15544649 = 11658487) B11658487
theorem B6910373 : Blo 1211423 6910373 := bstep (se 4 (by rfl) ⟨647847, by rfl⟩ : syracuseStep 6910373 = 1295695) B1295695
theorem B3068351 : Blo 1211423 3068351 := bstep (se 1 (by rfl) ⟨2301263, by rfl⟩ : syracuseStep 3068351 = 4602527) B4602527
theorem B4600415 : Blo 1211423 4600415 := bstep (se 1 (by rfl) ⟨3450311, by rfl⟩ : syracuseStep 4600415 = 6900623) B6900623
theorem B2044703 : Blo 1211423 2044703 := bstep (se 1 (by rfl) ⟨1533527, by rfl⟩ : syracuseStep 2044703 = 3067055) B3067055
theorem B1725247 : Blo 1211423 1725247 := bstep (se 1 (by rfl) ⟨1293935, by rfl⟩ : syracuseStep 1725247 = 2587871) B2587871
theorem B1749919 : Blo 1211423 1749919 := bstep (se 1 (by rfl) ⟨1312439, by rfl⟩ : syracuseStep 1749919 = 2624879) B2624879
theorem B1364935 : Blo 1211423 1364935 := bstep (se 1 (by rfl) ⟨1023701, by rfl⟩ : syracuseStep 1364935 = 2047403) B2047403
theorem B6902765 : Blo 1211423 6902765 := bstep (se 3 (by rfl) ⟨1294268, by rfl⟩ : syracuseStep 6902765 = 2588537) B2588537
theorem B3068999 : Blo 1211423 3068999 := bstep (se 1 (by rfl) ⟨2301749, by rfl⟩ : syracuseStep 3068999 = 4603499) B4603499
theorem B6132995 : Blo 1211423 6132995 := bstep (se 1 (by rfl) ⟨4599746, by rfl⟩ : syracuseStep 6132995 = 9199493) B9199493
theorem B5822057 : Blo 1211423 5822057 := bstep (se 2 (by rfl) ⟨2183271, by rfl⟩ : syracuseStep 5822057 = 4366543) B4366543
theorem B5174921 : Blo 1211423 5174921 := bstep (se 2 (by rfl) ⟨1940595, by rfl⟩ : syracuseStep 5174921 = 3881191) B3881191
theorem B2766689 : Blo 1211423 2766689 := bstep (se 2 (by rfl) ⟨1037508, by rfl⟩ : syracuseStep 2766689 = 2075017) B2075017
theorem B9205811 : Blo 1211423 9205811 := bstep (se 1 (by rfl) ⟨6904358, by rfl⟩ : syracuseStep 9205811 = 13808717) B13808717
theorem B1456231 : Blo 1211423 1456231 := bstep (se 1 (by rfl) ⟨1092173, by rfl⟩ : syracuseStep 1456231 = 2184347) B2184347
theorem B1726591 : Blo 1211423 1726591 := bstep (se 1 (by rfl) ⟨1294943, by rfl⟩ : syracuseStep 1726591 = 2589887) B2589887
theorem B9828545 : Blo 1211423 9828545 := bstep (se 2 (by rfl) ⟨3685704, by rfl⟩ : syracuseStep 9828545 = 7371409) B7371409
theorem B7772507 : Blo 1211423 7772507 := bstep (se 1 (by rfl) ⟨5829380, by rfl⟩ : syracuseStep 7772507 = 11658761) B11658761
theorem B3455369 : Blo 1211423 3455369 := bstep (se 2 (by rfl) ⟨1295763, by rfl⟩ : syracuseStep 3455369 = 2591527) B2591527
theorem B4094441 : Blo 1211423 4094441 := bstep (se 2 (by rfl) ⟨1535415, by rfl⟩ : syracuseStep 4094441 = 3070831) B3070831
theorem B1817135 : Blo 1211423 1817135 := bstep (se 1 (by rfl) ⟨1362851, by rfl⟩ : syracuseStep 1817135 = 2725703) B2725703
theorem B2185823 : Blo 1211423 2185823 := bstep (se 1 (by rfl) ⟨1639367, by rfl⟩ : syracuseStep 2185823 = 3278735) B3278735
theorem B6134615 : Blo 1211423 6134615 := bstep (se 1 (by rfl) ⟨4600961, by rfl⟩ : syracuseStep 6134615 = 9201923) B9201923
theorem B4602815 : Blo 1211423 4602815 := bstep (se 1 (by rfl) ⟨3452111, by rfl⟩ : syracuseStep 4602815 = 6904223) B6904223
theorem B6134777 : Blo 1211423 6134777 := bstep (se 2 (by rfl) ⟨2300541, by rfl⟩ : syracuseStep 6134777 = 4601083) B4601083
theorem B1662059 : Blo 1211423 1662059 := bstep (se 1 (by rfl) ⟨1246544, by rfl⟩ : syracuseStep 1662059 = 2493089) B2493089
theorem B1211547 : Blo 1211423 1211547 := bstep (se 1 (by rfl) ⟨908660, by rfl⟩ : syracuseStep 1211547 = 1817321) B1817321
theorem B1817807 : Blo 1211423 1817807 := bstep (se 1 (by rfl) ⟨1363355, by rfl⟩ : syracuseStep 1817807 = 2726711) B2726711
theorem B1817897 : Blo 1211423 1817897 := bstep (se 2 (by rfl) ⟨681711, by rfl⟩ : syracuseStep 1817897 = 1363423) B1363423
theorem B7372093 : Blo 1211423 7372093 := bstep (se 3 (by rfl) ⟨1382267, by rfl⟩ : syracuseStep 7372093 = 2764535) B2764535
theorem B1817927 : Blo 1211423 1817927 := bstep (se 1 (by rfl) ⟨1363445, by rfl⟩ : syracuseStep 1817927 = 2726891) B2726891
theorem B4095305 : Blo 1211423 4095305 := bstep (se 2 (by rfl) ⟨1535739, by rfl⟩ : syracuseStep 4095305 = 3071479) B3071479
theorem B1211803 : Blo 1211423 1211803 := bstep (se 1 (by rfl) ⟨908852, by rfl⟩ : syracuseStep 1211803 = 1817705) B1817705
theorem B1211887 : Blo 1211423 1211887 := bstep (se 1 (by rfl) ⟨908915, by rfl⟩ : syracuseStep 1211887 = 1817831) B1817831
theorem B1212223 : Blo 1211423 1212223 := bstep (se 1 (by rfl) ⟨909167, by rfl⟩ : syracuseStep 1212223 = 1818335) B1818335
theorem B1212251 : Blo 1211423 1212251 := bstep (se 1 (by rfl) ⟨909188, by rfl⟩ : syracuseStep 1212251 = 1818377) B1818377
theorem B1818527 : Blo 1211423 1818527 := bstep (se 1 (by rfl) ⟨1363895, by rfl⟩ : syracuseStep 1818527 = 2727791) B2727791
theorem B13098935 : Blo 1211423 13098935 := bstep (se 1 (by rfl) ⟨9824201, by rfl⟩ : syracuseStep 13098935 = 19648403) B19648403
theorem B14737373 : Blo 1211423 14737373 := bstep (se 3 (by rfl) ⟨2763257, by rfl⟩ : syracuseStep 14737373 = 5526515) B5526515
theorem B1818617 : Blo 1211423 1818617 := bstep (se 2 (by rfl) ⟨681981, by rfl⟩ : syracuseStep 1818617 = 1363963) B1363963
theorem B1212507 : Blo 1211423 1212507 := bstep (se 1 (by rfl) ⟨909380, by rfl⟩ : syracuseStep 1212507 = 1818761) B1818761
theorem B1941641 : Blo 1211423 1941641 := bstep (se 2 (by rfl) ⟨728115, by rfl⟩ : syracuseStep 1941641 = 1456231) B1456231
theorem B1212571 : Blo 1211423 1212571 := bstep (se 1 (by rfl) ⟨909428, by rfl⟩ : syracuseStep 1212571 = 1818857) B1818857
theorem B2302121 : Blo 1211423 2302121 := bstep (se 2 (by rfl) ⟨863295, by rfl⟩ : syracuseStep 2302121 = 1726591) B1726591
theorem B10363099 : Blo 1211423 10363099 := bstep (se 1 (by rfl) ⟨7772324, by rfl⟩ : syracuseStep 10363099 = 15544649) B15544649
theorem B1212655 : Blo 1211423 1212655 := bstep (se 1 (by rfl) ⟨909491, by rfl⟩ : syracuseStep 1212655 = 1818983) B1818983
theorem B18907411 : Blo 1211423 18907411 := bstep (se 1 (by rfl) ⟨14180558, by rfl⟩ : syracuseStep 18907411 = 28361117) B28361117
theorem B4432157 : Blo 1211423 4432157 := bstep (se 3 (by rfl) ⟨831029, by rfl⟩ : syracuseStep 4432157 = 1662059) B1662059
theorem B1212735 : Blo 1211423 1212735 := bstep (se 1 (by rfl) ⟨909551, by rfl⟩ : syracuseStep 1212735 = 1819103) B1819103
theorem B11649419 : Blo 1211423 11649419 := bstep (se 1 (by rfl) ⟨8737064, by rfl⟩ : syracuseStep 11649419 = 17474129) B17474129
theorem B1212903 : Blo 1211423 1212903 := bstep (se 1 (by rfl) ⟨909677, by rfl⟩ : syracuseStep 1212903 = 1819355) B1819355
theorem B1819115 : Blo 1211423 1819115 := bstep (se 1 (by rfl) ⟨1364336, by rfl⟩ : syracuseStep 1819115 = 2728673) B2728673
theorem B39354929 : Blo 1211423 39354929 := bstep (se 2 (by rfl) ⟨14758098, by rfl⟩ : syracuseStep 39354929 = 29516197) B29516197
theorem B1213179 : Blo 1211423 1213179 := bstep (se 1 (by rfl) ⟨909884, by rfl⟩ : syracuseStep 1213179 = 1819769) B1819769
theorem B4088663 : Blo 1211423 4088663 := bstep (se 1 (by rfl) ⟨3066497, by rfl⟩ : syracuseStep 4088663 = 6132995) B6132995
theorem B4604759 : Blo 1211423 4604759 := bstep (se 1 (by rfl) ⟨3453569, by rfl⟩ : syracuseStep 4604759 = 6907139) B6907139
theorem B1213311 : Blo 1211423 1213311 := bstep (se 1 (by rfl) ⟨909983, by rfl⟩ : syracuseStep 1213311 = 1819967) B1819967
theorem B3449947 : Blo 1211423 3449947 := bstep (se 1 (by rfl) ⟨2587460, by rfl⟩ : syracuseStep 3449947 = 5174921) B5174921
theorem B1819739 : Blo 1211423 1819739 := bstep (se 1 (by rfl) ⟨1364804, by rfl⟩ : syracuseStep 1819739 = 2729609) B2729609
theorem B1819775 : Blo 1211423 1819775 := bstep (se 1 (by rfl) ⟨1364831, by rfl⟩ : syracuseStep 1819775 = 2729663) B2729663
theorem B1844459 : Blo 1211423 1844459 := bstep (se 1 (by rfl) ⟨1383344, by rfl⟩ : syracuseStep 1844459 = 2766689) B2766689
theorem B1819913 : Blo 1211423 1819913 := bstep (se 2 (by rfl) ⟨682467, by rfl⟩ : syracuseStep 1819913 = 1364935) B1364935
theorem B6137207 : Blo 1211423 6137207 := bstep (se 1 (by rfl) ⟨4602905, by rfl⟩ : syracuseStep 6137207 = 9205811) B9205811
theorem B29476295 : Blo 1211423 29476295 := bstep (se 1 (by rfl) ⟨22107221, by rfl⟩ : syracuseStep 29476295 = 44214443) B44214443
theorem B15525377 : Blo 1211423 15525377 := bstep (se 2 (by rfl) ⟨5822016, by rfl⟩ : syracuseStep 15525377 = 11644033) B11644033
theorem B5178953 : Blo 1211423 5178953 := bstep (se 2 (by rfl) ⟨1942107, by rfl⟩ : syracuseStep 5178953 = 3884215) B3884215
theorem B2303579 : Blo 1211423 2303579 := bstep (se 1 (by rfl) ⟨1727684, by rfl⟩ : syracuseStep 2303579 = 3455369) B3455369
theorem B2729627 : Blo 1211423 2729627 := bstep (se 1 (by rfl) ⟨2047220, by rfl⟩ : syracuseStep 2729627 = 4094441) B4094441
theorem B4089743 : Blo 1211423 4089743 := bstep (se 1 (by rfl) ⟨3067307, by rfl⟩ : syracuseStep 4089743 = 6134615) B6134615
theorem B4089851 : Blo 1211423 4089851 := bstep (se 1 (by rfl) ⟨3067388, by rfl⟩ : syracuseStep 4089851 = 6134777) B6134777
theorem B2730203 : Blo 1211423 2730203 := bstep (se 1 (by rfl) ⟨2047652, by rfl⟩ : syracuseStep 2730203 = 4095305) B4095305
theorem B4917779 : Blo 1211423 4917779 := bstep (se 1 (by rfl) ⟨3688334, by rfl⟩ : syracuseStep 4917779 = 7376669) B7376669
theorem B9824915 : Blo 1211423 9824915 := bstep (se 1 (by rfl) ⟨7368686, by rfl⟩ : syracuseStep 9824915 = 14737373) B14737373
theorem B9210671 : Blo 1211423 9210671 := bstep (se 1 (by rfl) ⟨6908003, by rfl⟩ : syracuseStep 9210671 = 13816007) B13816007
theorem B32803663 : Blo 1211423 32803663 := bstep (se 1 (by rfl) ⟨24602747, by rfl⟩ : syracuseStep 32803663 = 49205495) B49205495
theorem B4090715 : Blo 1211423 4090715 := bstep (se 1 (by rfl) ⟨3068036, by rfl⟩ : syracuseStep 4090715 = 6136073) B6136073
theorem B4606915 : Blo 1211423 4606915 := bstep (se 1 (by rfl) ⟨3455186, by rfl⟩ : syracuseStep 4606915 = 6910373) B6910373
theorem B4090823 : Blo 1211423 4090823 := bstep (se 1 (by rfl) ⟨3068117, by rfl⟩ : syracuseStep 4090823 = 6136235) B6136235
theorem B3066943 : Blo 1211423 3066943 := bstep (se 1 (by rfl) ⟨2300207, by rfl⟩ : syracuseStep 3066943 = 4600415) B4600415
theorem B26209453 : Blo 1211423 26209453 := bstep (se 3 (by rfl) ⟨4914272, by rfl⟩ : syracuseStep 26209453 = 9828545) B9828545
theorem B1363135 : Blo 1211423 1363135 := bstep (se 1 (by rfl) ⟨1022351, by rfl⟩ : syracuseStep 1363135 = 2044703) B2044703
theorem B9202895 : Blo 1211423 9202895 := bstep (se 1 (by rfl) ⟨6902171, by rfl⟩ : syracuseStep 9202895 = 13804343) B13804343
theorem B4091579 : Blo 1211423 4091579 := bstep (se 1 (by rfl) ⟨3068684, by rfl⟩ : syracuseStep 4091579 = 6137369) B6137369
theorem B3452681 : Blo 1211423 3452681 := bstep (se 2 (by rfl) ⟨1294755, by rfl⟩ : syracuseStep 3452681 = 2589511) B2589511
theorem B11063213 : Blo 1211423 11063213 := bstep (se 3 (by rfl) ⟨2074352, by rfl⟩ : syracuseStep 11063213 = 4148705) B4148705
theorem B3453023 : Blo 1211423 3453023 := bstep (se 1 (by rfl) ⟨2589767, by rfl⟩ : syracuseStep 3453023 = 5179535) B5179535
theorem B16593119 : Blo 1211423 16593119 := bstep (se 1 (by rfl) ⟨12444839, by rfl⟩ : syracuseStep 16593119 = 24889679) B24889679
theorem B5181671 : Blo 1211423 5181671 := bstep (se 1 (by rfl) ⟨3886253, by rfl⟩ : syracuseStep 5181671 = 7772507) B7772507
theorem B5828861 : Blo 1211423 5828861 := bstep (se 3 (by rfl) ⟨1092911, by rfl⟩ : syracuseStep 5828861 = 2185823) B2185823
theorem B3453263 : Blo 1211423 3453263 := bstep (se 1 (by rfl) ⟨2589947, by rfl⟩ : syracuseStep 3453263 = 5179895) B5179895
theorem B3068543 : Blo 1211423 3068543 := bstep (se 1 (by rfl) ⟨2301407, by rfl⟩ : syracuseStep 3068543 = 4602815) B4602815
theorem B17470201 : Blo 1211423 17470201 := bstep (se 2 (by rfl) ⟨6551325, by rfl⟩ : syracuseStep 17470201 = 13102651) B13102651
theorem B39318331 : Blo 1211423 39318331 := bstep (se 1 (by rfl) ⟨29488748, by rfl⟩ : syracuseStep 39318331 = 58977497) B58977497
theorem B2044831 : Blo 1211423 2044831 := bstep (se 1 (by rfl) ⟨1533623, by rfl⟩ : syracuseStep 2044831 = 3067247) B3067247
theorem B15143881 : Blo 1211423 15143881 := bstep (se 2 (by rfl) ⟨5678955, by rfl⟩ : syracuseStep 15143881 = 11357911) B11357911
theorem B2913259 : Blo 1211423 2913259 := bstep (se 1 (by rfl) ⟨2184944, by rfl⟩ : syracuseStep 2913259 = 4369889) B4369889
theorem B25572473 : Blo 1211423 25572473 := bstep (se 2 (by rfl) ⟨9589677, by rfl⟩ : syracuseStep 25572473 = 19179355) B19179355
theorem B3454265 : Blo 1211423 3454265 := bstep (se 2 (by rfl) ⟨1295349, by rfl⟩ : syracuseStep 3454265 = 2590699) B2590699
theorem B6141419 : Blo 1211423 6141419 := bstep (se 1 (by rfl) ⟨4606064, by rfl⟩ : syracuseStep 6141419 = 9212129) B9212129
theorem B6133319 : Blo 1211423 6133319 := bstep (se 1 (by rfl) ⟨4599989, by rfl⟩ : syracuseStep 6133319 = 9199979) B9199979
theorem B2045567 : Blo 1211423 2045567 := bstep (se 1 (by rfl) ⟨1534175, by rfl⟩ : syracuseStep 2045567 = 3068351) B3068351
theorem B4601569 : Blo 1211423 4601569 := bstep (se 2 (by rfl) ⟨1725588, by rfl⟩ : syracuseStep 4601569 = 3451177) B3451177
theorem B4601843 : Blo 1211423 4601843 := bstep (se 1 (by rfl) ⟨3451382, by rfl⟩ : syracuseStep 4601843 = 6902765) B6902765
theorem B2045999 : Blo 1211423 2045999 := bstep (se 1 (by rfl) ⟨1534499, by rfl⟩ : syracuseStep 2045999 = 3068999) B3068999
theorem B3881371 : Blo 1211423 3881371 := bstep (se 1 (by rfl) ⟨2911028, by rfl⟩ : syracuseStep 3881371 = 5822057) B5822057
theorem B3938719 : Blo 1211423 3938719 := bstep (se 1 (by rfl) ⟨2954039, by rfl⟩ : syracuseStep 3938719 = 5908079) B5908079
theorem B2300329 : Blo 1211423 2300329 := bstep (se 2 (by rfl) ⟨862623, by rfl⟩ : syracuseStep 2300329 = 1725247) B1725247
theorem B2333225 : Blo 1211423 2333225 := bstep (se 2 (by rfl) ⟨874959, by rfl⟩ : syracuseStep 2333225 = 1749919) B1749919
theorem B10361459 : Blo 1211423 10361459 := bstep (se 1 (by rfl) ⟨7771094, by rfl⟩ : syracuseStep 10361459 = 15542189) B15542189
theorem B1211423 : Blo 1211423 1211423 := bstep (se 1 (by rfl) ⟨908567, by rfl⟩ : syracuseStep 1211423 = 1817135) B1817135
theorem B74718287 : Blo 1211423 74718287 := bstep (se 1 (by rfl) ⟨56038715, by rfl⟩ : syracuseStep 74718287 = 112077431) B112077431
theorem B9829457 : Blo 1211423 9829457 := bstep (se 2 (by rfl) ⟨3686046, by rfl⟩ : syracuseStep 9829457 = 7372093) B7372093
theorem B1211871 : Blo 1211423 1211871 := bstep (se 1 (by rfl) ⟨908903, by rfl⟩ : syracuseStep 1211871 = 1817807) B1817807
theorem B1818089 : Blo 1211423 1818089 := bstep (se 2 (by rfl) ⟨681783, by rfl⟩ : syracuseStep 1818089 = 1363567) B1363567
theorem B1211931 : Blo 1211423 1211931 := bstep (se 1 (by rfl) ⟨908948, by rfl⟩ : syracuseStep 1211931 = 1817897) B1817897
theorem B1211951 : Blo 1211423 1211951 := bstep (se 1 (by rfl) ⟨908963, by rfl⟩ : syracuseStep 1211951 = 1817927) B1817927
theorem B6905681 : Blo 1211423 6905681 := bstep (se 2 (by rfl) ⟨2589630, by rfl⟩ : syracuseStep 6905681 = 5179261) B5179261
theorem B1212351 : Blo 1211423 1212351 := bstep (se 1 (by rfl) ⟨909263, by rfl⟩ : syracuseStep 1212351 = 1818527) B1818527
theorem B8732623 : Blo 1211423 8732623 := bstep (se 1 (by rfl) ⟨6549467, by rfl⟩ : syracuseStep 8732623 = 13098935) B13098935
theorem B2727899 : Blo 1211423 2727899 := bstep (se 1 (by rfl) ⟨2045924, by rfl⟩ : syracuseStep 2727899 = 4091849) B4091849
theorem B1212411 : Blo 1211423 1212411 := bstep (se 1 (by rfl) ⟨909308, by rfl⟩ : syracuseStep 1212411 = 1818617) B1818617
theorem B2302015 : Blo 1211423 2302015 := bstep (se 1 (by rfl) ⟨1726511, by rfl⟩ : syracuseStep 2302015 = 3453023) B3453023
theorem B1294427 : Blo 1211423 1294427 := bstep (se 1 (by rfl) ⟨970820, by rfl⟩ : syracuseStep 1294427 = 1941641) B1941641
theorem B2302175 : Blo 1211423 2302175 := bstep (se 1 (by rfl) ⟨1726631, by rfl⟩ : syracuseStep 2302175 = 3453263) B3453263
theorem B7766279 : Blo 1211423 7766279 := bstep (se 1 (by rfl) ⟨5824709, by rfl⟩ : syracuseStep 7766279 = 11649419) B11649419
theorem B1212743 : Blo 1211423 1212743 := bstep (se 1 (by rfl) ⟨909557, by rfl⟩ : syracuseStep 1212743 = 1819115) B1819115
theorem B5251625 : Blo 1211423 5251625 := bstep (se 2 (by rfl) ⟨1969359, by rfl⟩ : syracuseStep 5251625 = 3938719) B3938719
theorem B1213159 : Blo 1211423 1213159 := bstep (se 1 (by rfl) ⟨909869, by rfl⟩ : syracuseStep 1213159 = 1819739) B1819739
theorem B17048315 : Blo 1211423 17048315 := bstep (se 1 (by rfl) ⟨12786236, by rfl⟩ : syracuseStep 17048315 = 25572473) B25572473
theorem B1213183 : Blo 1211423 1213183 := bstep (se 1 (by rfl) ⟨909887, by rfl⟩ : syracuseStep 1213183 = 1819775) B1819775
theorem B1229639 : Blo 1211423 1229639 := bstep (se 1 (by rfl) ⟨922229, by rfl⟩ : syracuseStep 1229639 = 1844459) B1844459
theorem B1213275 : Blo 1211423 1213275 := bstep (se 1 (by rfl) ⟨909956, by rfl⟩ : syracuseStep 1213275 = 1819913) B1819913
theorem B2302843 : Blo 1211423 2302843 := bstep (se 1 (by rfl) ⟨1727132, by rfl⟩ : syracuseStep 2302843 = 3454265) B3454265
theorem B4088879 : Blo 1211423 4088879 := bstep (se 1 (by rfl) ⟨3066659, by rfl⟩ : syracuseStep 4088879 = 6133319) B6133319
theorem B1819751 : Blo 1211423 1819751 := bstep (se 1 (by rfl) ⟨1364813, by rfl⟩ : syracuseStep 1819751 = 2729627) B2729627
theorem B43738217 : Blo 1211423 43738217 := bstep (se 2 (by rfl) ⟨16401831, by rfl⟩ : syracuseStep 43738217 = 32803663) B32803663
theorem B3884345 : Blo 1211423 3884345 := bstep (se 2 (by rfl) ⟨1456629, by rfl⟩ : syracuseStep 3884345 = 2913259) B2913259
theorem B4089257 : Blo 1211423 4089257 := bstep (se 2 (by rfl) ⟨1533471, by rfl⟩ : syracuseStep 4089257 = 3066943) B3066943
theorem B1820135 : Blo 1211423 1820135 := bstep (se 1 (by rfl) ⟨1365101, by rfl⟩ : syracuseStep 1820135 = 2730203) B2730203
theorem B3278519 : Blo 1211423 3278519 := bstep (se 1 (by rfl) ⟨2458889, by rfl⟩ : syracuseStep 3278519 = 4917779) B4917779
theorem B6907639 : Blo 1211423 6907639 := bstep (se 1 (by rfl) ⟨5180729, by rfl⟩ : syracuseStep 6907639 = 10361459) B10361459
theorem B11643497 : Blo 1211423 11643497 := bstep (se 2 (by rfl) ⟨4366311, by rfl⟩ : syracuseStep 11643497 = 8732623) B8732623
theorem B7375475 : Blo 1211423 7375475 := bstep (se 1 (by rfl) ⟨5531606, by rfl⟩ : syracuseStep 7375475 = 11063213) B11063213
theorem B11062079 : Blo 1211423 11062079 := bstep (se 1 (by rfl) ⟨8296559, by rfl⟩ : syracuseStep 11062079 = 16593119) B16593119
theorem B3885907 : Blo 1211423 3885907 := bstep (se 1 (by rfl) ⟨2914430, by rfl⟩ : syracuseStep 3885907 = 5828861) B5828861
theorem B25209881 : Blo 1211423 25209881 := bstep (se 2 (by rfl) ⟨9453705, by rfl⟩ : syracuseStep 25209881 = 18907411) B18907411
theorem B6138989 : Blo 1211423 6138989 := bstep (se 3 (by rfl) ⟨1151060, by rfl⟩ : syracuseStep 6138989 = 2302121) B2302121
theorem B3067105 : Blo 1211423 3067105 := bstep (se 2 (by rfl) ⟨1150164, by rfl⟩ : syracuseStep 3067105 = 2300329) B2300329
theorem B4091471 : Blo 1211423 4091471 := bstep (se 1 (by rfl) ⟨3068603, by rfl⟩ : syracuseStep 4091471 = 6137207) B6137207
theorem B23293601 : Blo 1211423 23293601 := bstep (se 2 (by rfl) ⟨8735100, by rfl⟩ : syracuseStep 23293601 = 17470201) B17470201
theorem B10350251 : Blo 1211423 10350251 := bstep (se 1 (by rfl) ⟨7762688, by rfl⟩ : syracuseStep 10350251 = 15525377) B15525377
theorem B3452635 : Blo 1211423 3452635 := bstep (se 1 (by rfl) ⟨2589476, by rfl⟩ : syracuseStep 3452635 = 5178953) B5178953
theorem B52424441 : Blo 1211423 52424441 := bstep (se 2 (by rfl) ⟨19659165, by rfl⟩ : syracuseStep 52424441 = 39318331) B39318331
theorem B1363711 : Blo 1211423 1363711 := bstep (se 1 (by rfl) ⟨1022783, by rfl⟩ : syracuseStep 1363711 = 2045567) B2045567
theorem B3067895 : Blo 1211423 3067895 := bstep (se 1 (by rfl) ⟨2300921, by rfl⟩ : syracuseStep 3067895 = 4601843) B4601843
theorem B1363999 : Blo 1211423 1363999 := bstep (se 1 (by rfl) ⟨1022999, by rfl⟩ : syracuseStep 1363999 = 2045999) B2045999
theorem B6221933 : Blo 1211423 6221933 := bstep (se 3 (by rfl) ⟨1166612, by rfl⟩ : syracuseStep 6221933 = 2333225) B2333225
theorem B4599929 : Blo 1211423 4599929 := bstep (se 2 (by rfl) ⟨1724973, by rfl⟩ : syracuseStep 4599929 = 3449947) B3449947
theorem B6549943 : Blo 1211423 6549943 := bstep (se 1 (by rfl) ⟨4912457, by rfl⟩ : syracuseStep 6549943 = 9824915) B9824915
theorem B6140447 : Blo 1211423 6140447 := bstep (se 1 (by rfl) ⟨4605335, by rfl⟩ : syracuseStep 6140447 = 9210671) B9210671
theorem B49812191 : Blo 1211423 49812191 := bstep (se 1 (by rfl) ⟨37359143, by rfl⟩ : syracuseStep 49812191 = 74718287) B74718287
theorem B3454447 : Blo 1211423 3454447 := bstep (se 1 (by rfl) ⟨2590835, by rfl⟩ : syracuseStep 3454447 = 5181671) B5181671
theorem B2954771 : Blo 1211423 2954771 := bstep (se 1 (by rfl) ⟨2216078, by rfl⟩ : syracuseStep 2954771 = 4432157) B4432157
theorem B13817465 : Blo 1211423 13817465 := bstep (se 2 (by rfl) ⟨5181549, by rfl⟩ : syracuseStep 13817465 = 10363099) B10363099
theorem B26236619 : Blo 1211423 26236619 := bstep (se 1 (by rfl) ⟨19677464, by rfl⟩ : syracuseStep 26236619 = 39354929) B39354929
theorem B2045695 : Blo 1211423 2045695 := bstep (se 1 (by rfl) ⟨1534271, by rfl⟩ : syracuseStep 2045695 = 3068543) B3068543
theorem B5175161 : Blo 1211423 5175161 := bstep (se 2 (by rfl) ⟨1940685, by rfl⟩ : syracuseStep 5175161 = 3881371) B3881371
theorem B2725775 : Blo 1211423 2725775 := bstep (se 1 (by rfl) ⟨2044331, by rfl⟩ : syracuseStep 2725775 = 4088663) B4088663
theorem B3069839 : Blo 1211423 3069839 := bstep (se 1 (by rfl) ⟨2302379, by rfl⟩ : syracuseStep 3069839 = 4604759) B4604759
theorem B19650863 : Blo 1211423 19650863 := bstep (se 1 (by rfl) ⟨14738147, by rfl⟩ : syracuseStep 19650863 = 29476295) B29476295
theorem B4094279 : Blo 1211423 4094279 := bstep (se 1 (by rfl) ⟨3070709, by rfl⟩ : syracuseStep 4094279 = 6141419) B6141419
theorem B2726441 : Blo 1211423 2726441 := bstep (se 2 (by rfl) ⟨1022415, by rfl⟩ : syracuseStep 2726441 = 2044831) B2044831
theorem B6142553 : Blo 1211423 6142553 := bstep (se 2 (by rfl) ⟨2303457, by rfl⟩ : syracuseStep 6142553 = 4606915) B4606915
theorem B2726495 : Blo 1211423 2726495 := bstep (se 1 (by rfl) ⟨2044871, by rfl⟩ : syracuseStep 2726495 = 4089743) B4089743
theorem B20191841 : Blo 1211423 20191841 := bstep (se 2 (by rfl) ⟨7571940, by rfl⟩ : syracuseStep 20191841 = 15143881) B15143881
theorem B2726567 : Blo 1211423 2726567 := bstep (se 1 (by rfl) ⟨2044925, by rfl⟩ : syracuseStep 2726567 = 4089851) B4089851
theorem B34945937 : Blo 1211423 34945937 := bstep (se 2 (by rfl) ⟨13104726, by rfl⟩ : syracuseStep 34945937 = 26209453) B26209453
theorem B6142877 : Blo 1211423 6142877 := bstep (se 3 (by rfl) ⟨1151789, by rfl⟩ : syracuseStep 6142877 = 2303579) B2303579
theorem B1817513 : Blo 1211423 1817513 := bstep (se 2 (by rfl) ⟨681567, by rfl⟩ : syracuseStep 1817513 = 1363135) B1363135
theorem B2727143 : Blo 1211423 2727143 := bstep (se 1 (by rfl) ⟨2045357, by rfl⟩ : syracuseStep 2727143 = 4090715) B4090715
theorem B2727215 : Blo 1211423 2727215 := bstep (se 1 (by rfl) ⟨2045411, by rfl⟩ : syracuseStep 2727215 = 4090823) B4090823
theorem B6552971 : Blo 1211423 6552971 := bstep (se 1 (by rfl) ⟨4914728, by rfl⟩ : syracuseStep 6552971 = 9829457) B9829457
theorem B6135263 : Blo 1211423 6135263 := bstep (se 1 (by rfl) ⟨4601447, by rfl⟩ : syracuseStep 6135263 = 9202895) B9202895
theorem B6135425 : Blo 1211423 6135425 := bstep (se 2 (by rfl) ⟨2300784, by rfl⟩ : syracuseStep 6135425 = 4601569) B4601569
theorem B1212059 : Blo 1211423 1212059 := bstep (se 1 (by rfl) ⟨909044, by rfl⟩ : syracuseStep 1212059 = 1818089) B1818089
theorem B2727719 : Blo 1211423 2727719 := bstep (se 1 (by rfl) ⟨2045789, by rfl⟩ : syracuseStep 2727719 = 4091579) B4091579
theorem B2301787 : Blo 1211423 2301787 := bstep (se 1 (by rfl) ⟨1726340, by rfl⟩ : syracuseStep 2301787 = 3452681) B3452681
theorem B4603787 : Blo 1211423 4603787 := bstep (se 1 (by rfl) ⟨3452840, by rfl⟩ : syracuseStep 4603787 = 6905681) B6905681
theorem B1818599 : Blo 1211423 1818599 := bstep (se 1 (by rfl) ⟨1363949, by rfl⟩ : syracuseStep 1818599 = 2727899) B2727899
theorem B1818665 : Blo 1211423 1818665 := bstep (se 2 (by rfl) ⟨681999, by rfl⟩ : syracuseStep 1818665 = 1363999) B1363999
theorem B5177519 : Blo 1211423 5177519 := bstep (se 1 (by rfl) ⟨3883139, by rfl⟩ : syracuseStep 5177519 = 7766279) B7766279
theorem B8733257 : Blo 1211423 8733257 := bstep (se 2 (by rfl) ⟨3274971, by rfl⟩ : syracuseStep 8733257 = 6549943) B6549943
theorem B1213167 : Blo 1211423 1213167 := bstep (se 1 (by rfl) ⟨909875, by rfl⟩ : syracuseStep 1213167 = 1819751) B1819751
theorem B2589563 : Blo 1211423 2589563 := bstep (se 1 (by rfl) ⟨1942172, by rfl⟩ : syracuseStep 2589563 = 3884345) B3884345
theorem B1213423 : Blo 1211423 1213423 := bstep (se 1 (by rfl) ⟨910067, by rfl⟩ : syracuseStep 1213423 = 1820135) B1820135
theorem B17491079 : Blo 1211423 17491079 := bstep (se 1 (by rfl) ⟨13118309, by rfl⟩ : syracuseStep 17491079 = 26236619) B26236619
theorem B3450107 : Blo 1211423 3450107 := bstep (se 1 (by rfl) ⟨2587580, by rfl⟩ : syracuseStep 3450107 = 5175161) B5175161
theorem B13100575 : Blo 1211423 13100575 := bstep (se 1 (by rfl) ⟨9825431, by rfl⟩ : syracuseStep 13100575 = 19650863) B19650863
theorem B2729519 : Blo 1211423 2729519 := bstep (se 1 (by rfl) ⟨2047139, by rfl⟩ : syracuseStep 2729519 = 4094279) B4094279
theorem B4089473 : Blo 1211423 4089473 := bstep (se 2 (by rfl) ⟨1533552, by rfl⟩ : syracuseStep 4089473 = 3067105) B3067105
theorem B13461227 : Blo 1211423 13461227 := bstep (se 1 (by rfl) ⟨10095920, by rfl⟩ : syracuseStep 13461227 = 20191841) B20191841
theorem B7374719 : Blo 1211423 7374719 := bstep (se 1 (by rfl) ⟨5531039, by rfl⟩ : syracuseStep 7374719 = 11062079) B11062079
theorem B4605929 : Blo 1211423 4605929 := bstep (se 2 (by rfl) ⟨1727223, by rfl⟩ : syracuseStep 4605929 = 3454447) B3454447
theorem B3279037 : Blo 1211423 3279037 := bstep (se 3 (by rfl) ⟨614819, by rfl⟩ : syracuseStep 3279037 = 1229639) B1229639
theorem B4368647 : Blo 1211423 4368647 := bstep (se 1 (by rfl) ⟨3276485, by rfl⟩ : syracuseStep 4368647 = 6552971) B6552971
theorem B4090175 : Blo 1211423 4090175 := bstep (se 1 (by rfl) ⟨3067631, by rfl⟩ : syracuseStep 4090175 = 6135263) B6135263
theorem B9210185 : Blo 1211423 9210185 := bstep (se 2 (by rfl) ⟨3453819, by rfl⟩ : syracuseStep 9210185 = 6907639) B6907639
theorem B4090283 : Blo 1211423 4090283 := bstep (se 1 (by rfl) ⟨3067712, by rfl⟩ : syracuseStep 4090283 = 6135425) B6135425
theorem B6900167 : Blo 1211423 6900167 := bstep (se 1 (by rfl) ⟨5175125, by rfl⟩ : syracuseStep 6900167 = 10350251) B10350251
theorem B34949627 : Blo 1211423 34949627 := bstep (se 1 (by rfl) ⟨26212220, by rfl⟩ : syracuseStep 34949627 = 52424441) B52424441
theorem B4147955 : Blo 1211423 4147955 := bstep (se 1 (by rfl) ⟨3110966, by rfl⟩ : syracuseStep 4147955 = 6221933) B6221933
theorem B3066619 : Blo 1211423 3066619 := bstep (se 1 (by rfl) ⟨2299964, by rfl⟩ : syracuseStep 3066619 = 4599929) B4599929
theorem B1534783 : Blo 1211423 1534783 := bstep (se 1 (by rfl) ⟨1151087, by rfl⟩ : syracuseStep 1534783 = 2302175) B2302175
theorem B3451805 : Blo 1211423 3451805 := bstep (se 3 (by rfl) ⟨647213, by rfl⟩ : syracuseStep 3451805 = 1294427) B1294427
theorem B3501083 : Blo 1211423 3501083 := bstep (se 1 (by rfl) ⟨2625812, by rfl⟩ : syracuseStep 3501083 = 5251625) B5251625
theorem B11365543 : Blo 1211423 11365543 := bstep (se 1 (by rfl) ⟨8524157, by rfl⟩ : syracuseStep 11365543 = 17048315) B17048315
theorem B29158811 : Blo 1211423 29158811 := bstep (se 1 (by rfl) ⟨21869108, by rfl⟩ : syracuseStep 29158811 = 43738217) B43738217
theorem B1969847 : Blo 1211423 1969847 := bstep (se 1 (by rfl) ⟨1477385, by rfl⟩ : syracuseStep 1969847 = 2954771) B2954771
theorem B9211643 : Blo 1211423 9211643 := bstep (se 1 (by rfl) ⟨6908732, by rfl⟩ : syracuseStep 9211643 = 13817465) B13817465
theorem B5181209 : Blo 1211423 5181209 := bstep (se 2 (by rfl) ⟨1942953, by rfl⟩ : syracuseStep 5181209 = 3885907) B3885907
theorem B7762331 : Blo 1211423 7762331 := bstep (se 1 (by rfl) ⟨5821748, by rfl⟩ : syracuseStep 7762331 = 11643497) B11643497
theorem B16806587 : Blo 1211423 16806587 := bstep (se 1 (by rfl) ⟨12604940, by rfl⟩ : syracuseStep 16806587 = 25209881) B25209881
theorem B4092659 : Blo 1211423 4092659 := bstep (se 1 (by rfl) ⟨3069494, by rfl⟩ : syracuseStep 4092659 = 6138989) B6138989
theorem B15529067 : Blo 1211423 15529067 := bstep (se 1 (by rfl) ⟨11646800, by rfl⟩ : syracuseStep 15529067 = 23293601) B23293601
theorem B3069049 : Blo 1211423 3069049 := bstep (se 2 (by rfl) ⟨1150893, by rfl⟩ : syracuseStep 3069049 = 2301787) B2301787
theorem B3069191 : Blo 1211423 3069191 := bstep (se 1 (by rfl) ⟨2301893, by rfl⟩ : syracuseStep 3069191 = 4603787) B4603787
theorem B2045263 : Blo 1211423 2045263 := bstep (se 1 (by rfl) ⟨1533947, by rfl⟩ : syracuseStep 2045263 = 3067895) B3067895
theorem B3069353 : Blo 1211423 3069353 := bstep (se 2 (by rfl) ⟨1151007, by rfl⟩ : syracuseStep 3069353 = 2302015) B2302015
theorem B4093631 : Blo 1211423 4093631 := bstep (se 1 (by rfl) ⟨3070223, by rfl⟩ : syracuseStep 4093631 = 6140447) B6140447
theorem B33208127 : Blo 1211423 33208127 := bstep (se 1 (by rfl) ⟨24906095, by rfl⟩ : syracuseStep 33208127 = 49812191) B49812191
theorem B2725919 : Blo 1211423 2725919 := bstep (se 1 (by rfl) ⟨2044439, by rfl⟩ : syracuseStep 2725919 = 4088879) B4088879
theorem B2726171 : Blo 1211423 2726171 := bstep (se 1 (by rfl) ⟨2044628, by rfl⟩ : syracuseStep 2726171 = 4089257) B4089257
theorem B2185679 : Blo 1211423 2185679 := bstep (se 1 (by rfl) ⟨1639259, by rfl⟩ : syracuseStep 2185679 = 3278519) B3278519
theorem B3070457 : Blo 1211423 3070457 := bstep (se 2 (by rfl) ⟨1151421, by rfl⟩ : syracuseStep 3070457 = 2302843) B2302843
theorem B1817183 : Blo 1211423 1817183 := bstep (se 1 (by rfl) ⟨1362887, by rfl⟩ : syracuseStep 1817183 = 2725775) B2725775
theorem B2046559 : Blo 1211423 2046559 := bstep (se 1 (by rfl) ⟨1534919, by rfl⟩ : syracuseStep 2046559 = 3069839) B3069839
theorem B19667933 : Blo 1211423 19667933 := bstep (se 3 (by rfl) ⟨3687737, by rfl⟩ : syracuseStep 19667933 = 7375475) B7375475
theorem B1817627 : Blo 1211423 1817627 := bstep (se 1 (by rfl) ⟨1363220, by rfl⟩ : syracuseStep 1817627 = 2726441) B2726441
theorem B4095035 : Blo 1211423 4095035 := bstep (se 1 (by rfl) ⟨3071276, by rfl⟩ : syracuseStep 4095035 = 6142553) B6142553
theorem B1817663 : Blo 1211423 1817663 := bstep (se 1 (by rfl) ⟨1363247, by rfl⟩ : syracuseStep 1817663 = 2726495) B2726495
theorem B1817711 : Blo 1211423 1817711 := bstep (se 1 (by rfl) ⟨1363283, by rfl⟩ : syracuseStep 1817711 = 2726567) B2726567
theorem B23297291 : Blo 1211423 23297291 := bstep (se 1 (by rfl) ⟨17472968, by rfl⟩ : syracuseStep 23297291 = 34945937) B34945937
theorem B4095251 : Blo 1211423 4095251 := bstep (se 1 (by rfl) ⟨3071438, by rfl⟩ : syracuseStep 4095251 = 6142877) B6142877
theorem B1211675 : Blo 1211423 1211675 := bstep (se 1 (by rfl) ⟨908756, by rfl⟩ : syracuseStep 1211675 = 1817513) B1817513
theorem B1818095 : Blo 1211423 1818095 := bstep (se 1 (by rfl) ⟨1363571, by rfl⟩ : syracuseStep 1818095 = 2727143) B2727143
theorem B1818143 : Blo 1211423 1818143 := bstep (se 1 (by rfl) ⟨1363607, by rfl⟩ : syracuseStep 1818143 = 2727215) B2727215
theorem B4603513 : Blo 1211423 4603513 := bstep (se 2 (by rfl) ⟨1726317, by rfl⟩ : syracuseStep 4603513 = 3452635) B3452635
theorem B1818281 : Blo 1211423 1818281 := bstep (se 2 (by rfl) ⟨681855, by rfl⟩ : syracuseStep 1818281 = 1363711) B1363711
theorem B2727593 : Blo 1211423 2727593 := bstep (se 2 (by rfl) ⟨1022847, by rfl⟩ : syracuseStep 2727593 = 2045695) B2045695
theorem B2727647 : Blo 1211423 2727647 := bstep (se 1 (by rfl) ⟨2045735, by rfl⟩ : syracuseStep 2727647 = 4091471) B4091471
theorem B1818479 : Blo 1211423 1818479 := bstep (se 1 (by rfl) ⟨1363859, by rfl⟩ : syracuseStep 1818479 = 2727719) B2727719
theorem B1212399 : Blo 1211423 1212399 := bstep (se 1 (by rfl) ⟨909299, by rfl⟩ : syracuseStep 1212399 = 1818599) B1818599
theorem B1212443 : Blo 1211423 1212443 := bstep (se 1 (by rfl) ⟨909332, by rfl⟩ : syracuseStep 1212443 = 1818665) B1818665
theorem B2728439 : Blo 1211423 2728439 := bstep (se 1 (by rfl) ⟨2046329, by rfl⟩ : syracuseStep 2728439 = 4092659) B4092659
theorem B2728745 : Blo 1211423 2728745 := bstep (se 2 (by rfl) ⟨1023279, by rfl⟩ : syracuseStep 2728745 = 2046559) B2046559
theorem B4088825 : Blo 1211423 4088825 := bstep (se 2 (by rfl) ⟨1533309, by rfl⟩ : syracuseStep 4088825 = 3066619) B3066619
theorem B1819679 : Blo 1211423 1819679 := bstep (se 1 (by rfl) ⟨1364759, by rfl⟩ : syracuseStep 1819679 = 2729519) B2729519
theorem B2729087 : Blo 1211423 2729087 := bstep (se 1 (by rfl) ⟨2046815, by rfl⟩ : syracuseStep 2729087 = 4093631) B4093631
theorem B4916479 : Blo 1211423 4916479 := bstep (se 1 (by rfl) ⟨3687359, by rfl⟩ : syracuseStep 4916479 = 7374719) B7374719
theorem B23299751 : Blo 1211423 23299751 := bstep (se 1 (by rfl) ⟨17474813, by rfl⟩ : syracuseStep 23299751 = 34949627) B34949627
theorem B2730023 : Blo 1211423 2730023 := bstep (se 1 (by rfl) ⟨2047517, by rfl⟩ : syracuseStep 2730023 = 4095035) B4095035
theorem B17467433 : Blo 1211423 17467433 := bstep (se 2 (by rfl) ⟨6550287, by rfl⟩ : syracuseStep 17467433 = 13100575) B13100575
theorem B6138017 : Blo 1211423 6138017 := bstep (se 2 (by rfl) ⟨2301756, by rfl⟩ : syracuseStep 6138017 = 4603513) B4603513
theorem B2730167 : Blo 1211423 2730167 := bstep (se 1 (by rfl) ⟨2047625, by rfl⟩ : syracuseStep 2730167 = 4095251) B4095251
theorem B1313231 : Blo 1211423 1313231 := bstep (se 1 (by rfl) ⟨984923, by rfl⟩ : syracuseStep 1313231 = 1969847) B1969847
theorem B3451679 : Blo 1211423 3451679 := bstep (se 1 (by rfl) ⟨2588759, by rfl⟩ : syracuseStep 3451679 = 5177519) B5177519
theorem B11660719 : Blo 1211423 11660719 := bstep (se 1 (by rfl) ⟨8745539, by rfl⟩ : syracuseStep 11660719 = 17491079) B17491079
theorem B8974151 : Blo 1211423 8974151 := bstep (se 1 (by rfl) ⟨6730613, by rfl⟩ : syracuseStep 8974151 = 13461227) B13461227
theorem B22138751 : Blo 1211423 22138751 := bstep (se 1 (by rfl) ⟨16604063, by rfl⟩ : syracuseStep 22138751 = 33208127) B33208127
theorem B4092065 : Blo 1211423 4092065 := bstep (se 2 (by rfl) ⟨1534524, by rfl⟩ : syracuseStep 4092065 = 3069049) B3069049
theorem B2912431 : Blo 1211423 2912431 := bstep (se 1 (by rfl) ⟨2184323, by rfl⟩ : syracuseStep 2912431 = 4368647) B4368647
theorem B6140123 : Blo 1211423 6140123 := bstep (se 1 (by rfl) ⟨4605092, by rfl⟩ : syracuseStep 6140123 = 9210185) B9210185
theorem B4600111 : Blo 1211423 4600111 := bstep (se 1 (by rfl) ⟨3450083, by rfl⟩ : syracuseStep 4600111 = 6900167) B6900167
theorem B2765303 : Blo 1211423 2765303 := bstep (se 1 (by rfl) ⟨2073977, by rfl⟩ : syracuseStep 2765303 = 4147955) B4147955
theorem B13111955 : Blo 1211423 13111955 := bstep (se 1 (by rfl) ⟨9833966, by rfl⟩ : syracuseStep 13111955 = 19667933) B19667933
theorem B6141095 : Blo 1211423 6141095 := bstep (se 1 (by rfl) ⟨4605821, by rfl⟩ : syracuseStep 6141095 = 9211643) B9211643
theorem B3454139 : Blo 1211423 3454139 := bstep (se 1 (by rfl) ⟨2590604, by rfl⟩ : syracuseStep 3454139 = 5181209) B5181209
theorem B9336221 : Blo 1211423 9336221 := bstep (se 3 (by rfl) ⟨1750541, by rfl⟩ : syracuseStep 9336221 = 3501083) B3501083
theorem B4372049 : Blo 1211423 4372049 := bstep (se 2 (by rfl) ⟨1639518, by rfl⟩ : syracuseStep 4372049 = 3279037) B3279037
theorem B5174887 : Blo 1211423 5174887 := bstep (se 1 (by rfl) ⟨3881165, by rfl⟩ : syracuseStep 5174887 = 7762331) B7762331
theorem B5822171 : Blo 1211423 5822171 := bstep (se 1 (by rfl) ⟨4366628, by rfl⟩ : syracuseStep 5822171 = 8733257) B8733257
theorem B1726375 : Blo 1211423 1726375 := bstep (se 1 (by rfl) ⟨1294781, by rfl⟩ : syracuseStep 1726375 = 2589563) B2589563
theorem B10352711 : Blo 1211423 10352711 := bstep (se 1 (by rfl) ⟨7764533, by rfl⟩ : syracuseStep 10352711 = 15529067) B15529067
theorem B2300071 : Blo 1211423 2300071 := bstep (se 1 (by rfl) ⟨1725053, by rfl⟩ : syracuseStep 2300071 = 3450107) B3450107
theorem B2046127 : Blo 1211423 2046127 := bstep (se 1 (by rfl) ⟨1534595, by rfl⟩ : syracuseStep 2046127 = 3069191) B3069191
theorem B2046235 : Blo 1211423 2046235 := bstep (se 1 (by rfl) ⟨1534676, by rfl⟩ : syracuseStep 2046235 = 3069353) B3069353
theorem B2046377 : Blo 1211423 2046377 := bstep (se 2 (by rfl) ⟨767391, by rfl⟩ : syracuseStep 2046377 = 1534783) B1534783
theorem B2726315 : Blo 1211423 2726315 := bstep (se 1 (by rfl) ⟨2044736, by rfl⟩ : syracuseStep 2726315 = 4089473) B4089473
theorem B3070619 : Blo 1211423 3070619 := bstep (se 1 (by rfl) ⟨2302964, by rfl⟩ : syracuseStep 3070619 = 4605929) B4605929
theorem B1817279 : Blo 1211423 1817279 := bstep (se 1 (by rfl) ⟨1362959, by rfl⟩ : syracuseStep 1817279 = 2725919) B2725919
theorem B1817447 : Blo 1211423 1817447 := bstep (se 1 (by rfl) ⟨1363085, by rfl⟩ : syracuseStep 1817447 = 2726171) B2726171
theorem B2726783 : Blo 1211423 2726783 := bstep (se 1 (by rfl) ⟨2045087, by rfl⟩ : syracuseStep 2726783 = 4090175) B4090175
theorem B15154057 : Blo 1211423 15154057 := bstep (se 2 (by rfl) ⟨5682771, by rfl⟩ : syracuseStep 15154057 = 11365543) B11365543
theorem B2726855 : Blo 1211423 2726855 := bstep (se 1 (by rfl) ⟨2045141, by rfl⟩ : syracuseStep 2726855 = 4090283) B4090283
theorem B1457119 : Blo 1211423 1457119 := bstep (se 1 (by rfl) ⟨1092839, by rfl⟩ : syracuseStep 1457119 = 2185679) B2185679
theorem B2046971 : Blo 1211423 2046971 := bstep (se 1 (by rfl) ⟨1535228, by rfl⟩ : syracuseStep 2046971 = 3070457) B3070457
theorem B1211455 : Blo 1211423 1211455 := bstep (se 1 (by rfl) ⟨908591, by rfl⟩ : syracuseStep 1211455 = 1817183) B1817183
theorem B2727017 : Blo 1211423 2727017 := bstep (se 2 (by rfl) ⟨1022631, by rfl⟩ : syracuseStep 2727017 = 2045263) B2045263
theorem B44817565 : Blo 1211423 44817565 := bstep (se 3 (by rfl) ⟨8403293, by rfl⟩ : syracuseStep 44817565 = 16806587) B16806587
theorem B2301203 : Blo 1211423 2301203 := bstep (se 1 (by rfl) ⟨1725902, by rfl⟩ : syracuseStep 2301203 = 3451805) B3451805
theorem B1211751 : Blo 1211423 1211751 := bstep (se 1 (by rfl) ⟨908813, by rfl⟩ : syracuseStep 1211751 = 1817627) B1817627
theorem B1211775 : Blo 1211423 1211775 := bstep (se 1 (by rfl) ⟨908831, by rfl⟩ : syracuseStep 1211775 = 1817663) B1817663
theorem B1211807 : Blo 1211423 1211807 := bstep (se 1 (by rfl) ⟨908855, by rfl⟩ : syracuseStep 1211807 = 1817711) B1817711
theorem B15531527 : Blo 1211423 15531527 := bstep (se 1 (by rfl) ⟨11648645, by rfl⟩ : syracuseStep 15531527 = 23297291) B23297291
theorem B19439207 : Blo 1211423 19439207 := bstep (se 1 (by rfl) ⟨14579405, by rfl⟩ : syracuseStep 19439207 = 29158811) B29158811
theorem B1212063 : Blo 1211423 1212063 := bstep (se 1 (by rfl) ⟨909047, by rfl⟩ : syracuseStep 1212063 = 1818095) B1818095
theorem B1212095 : Blo 1211423 1212095 := bstep (se 1 (by rfl) ⟨909071, by rfl⟩ : syracuseStep 1212095 = 1818143) B1818143
theorem B1212187 : Blo 1211423 1212187 := bstep (se 1 (by rfl) ⟨909140, by rfl⟩ : syracuseStep 1212187 = 1818281) B1818281
theorem B1818395 : Blo 1211423 1818395 := bstep (se 1 (by rfl) ⟨1363796, by rfl⟩ : syracuseStep 1818395 = 2727593) B2727593
theorem B1818431 : Blo 1211423 1818431 := bstep (se 1 (by rfl) ⟨1363823, by rfl⟩ : syracuseStep 1818431 = 2727647) B2727647
theorem B1212319 : Blo 1211423 1212319 := bstep (se 1 (by rfl) ⟨909239, by rfl⟩ : syracuseStep 1212319 = 1818479) B1818479
theorem B2728043 : Blo 1211423 2728043 := bstep (se 1 (by rfl) ⟨2046032, by rfl⟩ : syracuseStep 2728043 = 4092065) B4092065
theorem B3883241 : Blo 1211423 3883241 := bstep (se 2 (by rfl) ⟨1456215, by rfl⟩ : syracuseStep 3883241 = 2912431) B2912431
theorem B2728169 : Blo 1211423 2728169 := bstep (se 2 (by rfl) ⟨1023063, by rfl⟩ : syracuseStep 2728169 = 2046127) B2046127
theorem B1843535 : Blo 1211423 1843535 := bstep (se 1 (by rfl) ⟨1382651, by rfl⟩ : syracuseStep 1843535 = 2765303) B2765303
theorem B1818959 : Blo 1211423 1818959 := bstep (se 1 (by rfl) ⟨1364219, by rfl⟩ : syracuseStep 1818959 = 2728439) B2728439
theorem B2728313 : Blo 1211423 2728313 := bstep (se 2 (by rfl) ⟨1023117, by rfl⟩ : syracuseStep 2728313 = 2046235) B2046235
theorem B8741303 : Blo 1211423 8741303 := bstep (se 1 (by rfl) ⟨6555977, by rfl⟩ : syracuseStep 8741303 = 13111955) B13111955
theorem B1819163 : Blo 1211423 1819163 := bstep (se 1 (by rfl) ⟨1364372, by rfl⟩ : syracuseStep 1819163 = 2728745) B2728745
theorem B1213119 : Blo 1211423 1213119 := bstep (se 1 (by rfl) ⟨909839, by rfl⟩ : syracuseStep 1213119 = 1819679) B1819679
theorem B1819391 : Blo 1211423 1819391 := bstep (se 1 (by rfl) ⟨1364543, by rfl⟩ : syracuseStep 1819391 = 2729087) B2729087
theorem B2302759 : Blo 1211423 2302759 := bstep (se 1 (by rfl) ⟨1727069, by rfl⟩ : syracuseStep 2302759 = 3454139) B3454139
theorem B15533167 : Blo 1211423 15533167 := bstep (se 1 (by rfl) ⟨11649875, by rfl⟩ : syracuseStep 15533167 = 23299751) B23299751
theorem B1820015 : Blo 1211423 1820015 := bstep (se 1 (by rfl) ⟨1365011, by rfl⟩ : syracuseStep 1820015 = 2730023) B2730023
theorem B1820111 : Blo 1211423 1820111 := bstep (se 1 (by rfl) ⟨1365083, by rfl⟩ : syracuseStep 1820111 = 2730167) B2730167
theorem B6555305 : Blo 1211423 6555305 := bstep (se 2 (by rfl) ⟨2458239, by rfl⟩ : syracuseStep 6555305 = 4916479) B4916479
theorem B6899849 : Blo 1211423 6899849 := bstep (se 2 (by rfl) ⟨2587443, by rfl⟩ : syracuseStep 6899849 = 5174887) B5174887
theorem B1534135 : Blo 1211423 1534135 := bstep (se 1 (by rfl) ⟨1150601, by rfl⟩ : syracuseStep 1534135 = 2301203) B2301203
theorem B5982767 : Blo 1211423 5982767 := bstep (se 1 (by rfl) ⟨4487075, by rfl⟩ : syracuseStep 5982767 = 8974151) B8974151
theorem B3066761 : Blo 1211423 3066761 := bstep (se 2 (by rfl) ⟨1150035, by rfl⟩ : syracuseStep 3066761 = 2300071) B2300071
theorem B20205409 : Blo 1211423 20205409 := bstep (se 2 (by rfl) ⟨7577028, by rfl⟩ : syracuseStep 20205409 = 15154057) B15154057
theorem B3501949 : Blo 1211423 3501949 := bstep (se 3 (by rfl) ⟨656615, by rfl⟩ : syracuseStep 3501949 = 1313231) B1313231
theorem B11644955 : Blo 1211423 11644955 := bstep (se 1 (by rfl) ⟨8733716, by rfl⟩ : syracuseStep 11644955 = 17467433) B17467433
theorem B6901807 : Blo 1211423 6901807 := bstep (se 1 (by rfl) ⟨5176355, by rfl⟩ : syracuseStep 6901807 = 10352711) B10352711
theorem B4092011 : Blo 1211423 4092011 := bstep (se 1 (by rfl) ⟨3069008, by rfl⟩ : syracuseStep 4092011 = 6138017) B6138017
theorem B59756753 : Blo 1211423 59756753 := bstep (se 2 (by rfl) ⟨22408782, by rfl⟩ : syracuseStep 59756753 = 44817565) B44817565
theorem B1364251 : Blo 1211423 1364251 := bstep (se 1 (by rfl) ⟨1023188, by rfl⟩ : syracuseStep 1364251 = 2046377) B2046377
theorem B1364647 : Blo 1211423 1364647 := bstep (se 1 (by rfl) ⟨1023485, by rfl⟩ : syracuseStep 1364647 = 2046971) B2046971
theorem B7771301 : Blo 1211423 7771301 := bstep (se 4 (by rfl) ⟨728559, by rfl⟩ : syracuseStep 7771301 = 1457119) B1457119
theorem B14759167 : Blo 1211423 14759167 := bstep (se 1 (by rfl) ⟨11069375, by rfl⟩ : syracuseStep 14759167 = 22138751) B22138751
theorem B4093415 : Blo 1211423 4093415 := bstep (se 1 (by rfl) ⟨3070061, by rfl⟩ : syracuseStep 4093415 = 6140123) B6140123
theorem B6133481 : Blo 1211423 6133481 := bstep (se 2 (by rfl) ⟨2300055, by rfl⟩ : syracuseStep 6133481 = 4600111) B4600111
theorem B2725883 : Blo 1211423 2725883 := bstep (se 1 (by rfl) ⟨2044412, by rfl⟩ : syracuseStep 2725883 = 4088825) B4088825
theorem B4094063 : Blo 1211423 4094063 := bstep (se 1 (by rfl) ⟨3070547, by rfl⟩ : syracuseStep 4094063 = 6141095) B6141095
theorem B6224147 : Blo 1211423 6224147 := bstep (se 1 (by rfl) ⟨4668110, by rfl⟩ : syracuseStep 6224147 = 9336221) B9336221
theorem B2914699 : Blo 1211423 2914699 := bstep (se 1 (by rfl) ⟨2186024, by rfl⟩ : syracuseStep 2914699 = 4372049) B4372049
theorem B3881447 : Blo 1211423 3881447 := bstep (se 1 (by rfl) ⟨2911085, by rfl⟩ : syracuseStep 3881447 = 5822171) B5822171
theorem B1817543 : Blo 1211423 1817543 := bstep (se 1 (by rfl) ⟨1363157, by rfl⟩ : syracuseStep 1817543 = 2726315) B2726315
theorem B2047079 : Blo 1211423 2047079 := bstep (se 1 (by rfl) ⟨1535309, by rfl⟩ : syracuseStep 2047079 = 3070619) B3070619
theorem B1211519 : Blo 1211423 1211519 := bstep (se 1 (by rfl) ⟨908639, by rfl⟩ : syracuseStep 1211519 = 1817279) B1817279
theorem B2301119 : Blo 1211423 2301119 := bstep (se 1 (by rfl) ⟨1725839, by rfl⟩ : syracuseStep 2301119 = 3451679) B3451679
theorem B15547625 : Blo 1211423 15547625 := bstep (se 2 (by rfl) ⟨5830359, by rfl⟩ : syracuseStep 15547625 = 11660719) B11660719
theorem B1211631 : Blo 1211423 1211631 := bstep (se 1 (by rfl) ⟨908723, by rfl⟩ : syracuseStep 1211631 = 1817447) B1817447
theorem B1817855 : Blo 1211423 1817855 := bstep (se 1 (by rfl) ⟨1363391, by rfl⟩ : syracuseStep 1817855 = 2726783) B2726783
theorem B1817903 : Blo 1211423 1817903 := bstep (se 1 (by rfl) ⟨1363427, by rfl⟩ : syracuseStep 1817903 = 2726855) B2726855
theorem B1818011 : Blo 1211423 1818011 := bstep (se 1 (by rfl) ⟨1363508, by rfl⟩ : syracuseStep 1818011 = 2727017) B2727017
theorem B10354351 : Blo 1211423 10354351 := bstep (se 1 (by rfl) ⟨7765763, by rfl⟩ : syracuseStep 10354351 = 15531527) B15531527
theorem B12959471 : Blo 1211423 12959471 := bstep (se 1 (by rfl) ⟨9719603, by rfl⟩ : syracuseStep 12959471 = 19439207) B19439207
theorem B1212263 : Blo 1211423 1212263 := bstep (se 1 (by rfl) ⟨909197, by rfl⟩ : syracuseStep 1212263 = 1818395) B1818395
theorem B1212287 : Blo 1211423 1212287 := bstep (se 1 (by rfl) ⟨909215, by rfl⟩ : syracuseStep 1212287 = 1818431) B1818431
theorem B2301833 : Blo 1211423 2301833 := bstep (se 2 (by rfl) ⟨863187, by rfl⟩ : syracuseStep 2301833 = 1726375) B1726375
theorem B2728007 : Blo 1211423 2728007 := bstep (se 1 (by rfl) ⟨2046005, by rfl⟩ : syracuseStep 2728007 = 4092011) B4092011
theorem B1818695 : Blo 1211423 1818695 := bstep (se 1 (by rfl) ⟨1364021, by rfl⟩ : syracuseStep 1818695 = 2728043) B2728043
theorem B39837835 : Blo 1211423 39837835 := bstep (se 1 (by rfl) ⟨29878376, by rfl⟩ : syracuseStep 39837835 = 59756753) B59756753
theorem B1818779 : Blo 1211423 1818779 := bstep (se 1 (by rfl) ⟨1364084, by rfl⟩ : syracuseStep 1818779 = 2728169) B2728169
theorem B1229023 : Blo 1211423 1229023 := bstep (se 1 (by rfl) ⟨921767, by rfl⟩ : syracuseStep 1229023 = 1843535) B1843535
theorem B1212639 : Blo 1211423 1212639 := bstep (se 1 (by rfl) ⟨909479, by rfl⟩ : syracuseStep 1212639 = 1818959) B1818959
theorem B1818875 : Blo 1211423 1818875 := bstep (se 1 (by rfl) ⟨1364156, by rfl⟩ : syracuseStep 1818875 = 2728313) B2728313
theorem B1212775 : Blo 1211423 1212775 := bstep (se 1 (by rfl) ⟨909581, by rfl⟩ : syracuseStep 1212775 = 1819163) B1819163
theorem B1819001 : Blo 1211423 1819001 := bstep (se 2 (by rfl) ⟨682125, by rfl⟩ : syracuseStep 1819001 = 1364251) B1364251
theorem B1212927 : Blo 1211423 1212927 := bstep (se 1 (by rfl) ⟨909695, by rfl⟩ : syracuseStep 1212927 = 1819391) B1819391
theorem B10355309 : Blo 1211423 10355309 := bstep (se 3 (by rfl) ⟨1941620, by rfl⟩ : syracuseStep 10355309 = 3883241) B3883241
theorem B1819529 : Blo 1211423 1819529 := bstep (se 2 (by rfl) ⟨682323, by rfl⟩ : syracuseStep 1819529 = 1364647) B1364647
theorem B1213343 : Blo 1211423 1213343 := bstep (se 1 (by rfl) ⟨910007, by rfl⟩ : syracuseStep 1213343 = 1820015) B1820015
theorem B1213407 : Blo 1211423 1213407 := bstep (se 1 (by rfl) ⟨910055, by rfl⟩ : syracuseStep 1213407 = 1820111) B1820111
theorem B2728943 : Blo 1211423 2728943 := bstep (se 1 (by rfl) ⟨2046707, by rfl⟩ : syracuseStep 2728943 = 4093415) B4093415
theorem B4088987 : Blo 1211423 4088987 := bstep (se 1 (by rfl) ⟨3066740, by rfl⟩ : syracuseStep 4088987 = 6133481) B6133481
theorem B2729375 : Blo 1211423 2729375 := bstep (se 1 (by rfl) ⟨2047031, by rfl⟩ : syracuseStep 2729375 = 4094063) B4094063
theorem B20710889 : Blo 1211423 20710889 := bstep (se 2 (by rfl) ⟨7766583, by rfl⟩ : syracuseStep 20710889 = 15533167) B15533167
theorem B19678889 : Blo 1211423 19678889 := bstep (se 2 (by rfl) ⟨7379583, by rfl⟩ : syracuseStep 19678889 = 14759167) B14759167
theorem B1534079 : Blo 1211423 1534079 := bstep (se 1 (by rfl) ⟨1150559, by rfl⟩ : syracuseStep 1534079 = 2301119) B2301119
theorem B10365083 : Blo 1211423 10365083 := bstep (se 1 (by rfl) ⟨7773812, by rfl⟩ : syracuseStep 10365083 = 15547625) B15547625
theorem B13805801 : Blo 1211423 13805801 := bstep (se 2 (by rfl) ⟨5177175, by rfl⟩ : syracuseStep 13805801 = 10354351) B10354351
theorem B1534555 : Blo 1211423 1534555 := bstep (se 1 (by rfl) ⟨1150916, by rfl⟩ : syracuseStep 1534555 = 2301833) B2301833
theorem B9202409 : Blo 1211423 9202409 := bstep (se 2 (by rfl) ⟨3450903, by rfl⟩ : syracuseStep 9202409 = 6901807) B6901807
theorem B5827535 : Blo 1211423 5827535 := bstep (se 1 (by rfl) ⟨4370651, by rfl⟩ : syracuseStep 5827535 = 8741303) B8741303
theorem B3886265 : Blo 1211423 3886265 := bstep (se 2 (by rfl) ⟨1457349, by rfl⟩ : syracuseStep 3886265 = 2914699) B2914699
theorem B5180867 : Blo 1211423 5180867 := bstep (se 1 (by rfl) ⟨3885650, by rfl⟩ : syracuseStep 5180867 = 7771301) B7771301
theorem B4370203 : Blo 1211423 4370203 := bstep (se 1 (by rfl) ⟨3277652, by rfl⟩ : syracuseStep 4370203 = 6555305) B6555305
theorem B4599899 : Blo 1211423 4599899 := bstep (se 1 (by rfl) ⟨3449924, by rfl⟩ : syracuseStep 4599899 = 6899849) B6899849
theorem B4149431 : Blo 1211423 4149431 := bstep (se 1 (by rfl) ⟨3112073, by rfl⟩ : syracuseStep 4149431 = 6224147) B6224147
theorem B2044507 : Blo 1211423 2044507 := bstep (se 1 (by rfl) ⟨1533380, by rfl⟩ : syracuseStep 2044507 = 3066761) B3066761
theorem B34558589 : Blo 1211423 34558589 := bstep (se 3 (by rfl) ⟨6479735, by rfl⟩ : syracuseStep 34558589 = 12959471) B12959471
theorem B1364719 : Blo 1211423 1364719 := bstep (se 1 (by rfl) ⟨1023539, by rfl⟩ : syracuseStep 1364719 = 2047079) B2047079
theorem B26940545 : Blo 1211423 26940545 := bstep (se 2 (by rfl) ⟨10102704, by rfl⟩ : syracuseStep 26940545 = 20205409) B20205409
theorem B7763303 : Blo 1211423 7763303 := bstep (se 1 (by rfl) ⟨5822477, by rfl⟩ : syracuseStep 7763303 = 11644955) B11644955
theorem B2045513 : Blo 1211423 2045513 := bstep (se 2 (by rfl) ⟨767067, by rfl⟩ : syracuseStep 2045513 = 1534135) B1534135
theorem B3070345 : Blo 1211423 3070345 := bstep (se 2 (by rfl) ⟨1151379, by rfl⟩ : syracuseStep 3070345 = 2302759) B2302759
theorem B1817255 : Blo 1211423 1817255 := bstep (se 1 (by rfl) ⟨1362941, by rfl⟩ : syracuseStep 1817255 = 2725883) B2725883
theorem B2587631 : Blo 1211423 2587631 := bstep (se 1 (by rfl) ⟨1940723, by rfl⟩ : syracuseStep 2587631 = 3881447) B3881447
theorem B3988511 : Blo 1211423 3988511 := bstep (se 1 (by rfl) ⟨2991383, by rfl⟩ : syracuseStep 3988511 = 5982767) B5982767
theorem B1211695 : Blo 1211423 1211695 := bstep (se 1 (by rfl) ⟨908771, by rfl⟩ : syracuseStep 1211695 = 1817543) B1817543
theorem B1211903 : Blo 1211423 1211903 := bstep (se 1 (by rfl) ⟨908927, by rfl⟩ : syracuseStep 1211903 = 1817855) B1817855
theorem B1211935 : Blo 1211423 1211935 := bstep (se 1 (by rfl) ⟨908951, by rfl⟩ : syracuseStep 1211935 = 1817903) B1817903
theorem B1212007 : Blo 1211423 1212007 := bstep (se 1 (by rfl) ⟨909005, by rfl⟩ : syracuseStep 1212007 = 1818011) B1818011
theorem B4669265 : Blo 1211423 4669265 := bstep (se 2 (by rfl) ⟨1750974, by rfl⟩ : syracuseStep 4669265 = 3501949) B3501949
theorem B1818671 : Blo 1211423 1818671 := bstep (se 1 (by rfl) ⟨1364003, by rfl⟩ : syracuseStep 1818671 = 2728007) B2728007
theorem B1212463 : Blo 1211423 1212463 := bstep (se 1 (by rfl) ⟨909347, by rfl⟩ : syracuseStep 1212463 = 1818695) B1818695
theorem B1212519 : Blo 1211423 1212519 := bstep (se 1 (by rfl) ⟨909389, by rfl⟩ : syracuseStep 1212519 = 1818779) B1818779
theorem B1212583 : Blo 1211423 1212583 := bstep (se 1 (by rfl) ⟨909437, by rfl⟩ : syracuseStep 1212583 = 1818875) B1818875
theorem B1212667 : Blo 1211423 1212667 := bstep (se 1 (by rfl) ⟨909500, by rfl⟩ : syracuseStep 1212667 = 1819001) B1819001
theorem B10363373 : Blo 1211423 10363373 := bstep (se 3 (by rfl) ⟨1943132, by rfl⟩ : syracuseStep 10363373 = 3886265) B3886265
theorem B1213019 : Blo 1211423 1213019 := bstep (se 1 (by rfl) ⟨909764, by rfl⟩ : syracuseStep 1213019 = 1819529) B1819529
theorem B1819295 : Blo 1211423 1819295 := bstep (se 1 (by rfl) ⟨1364471, by rfl⟩ : syracuseStep 1819295 = 2728943) B2728943
theorem B212468453 : Blo 1211423 212468453 := bstep (se 4 (by rfl) ⟨19918917, by rfl⟩ : syracuseStep 212468453 = 39837835) B39837835
theorem B20702141 : Blo 1211423 20702141 := bstep (se 3 (by rfl) ⟨3881651, by rfl⟩ : syracuseStep 20702141 = 7763303) B7763303
theorem B1819583 : Blo 1211423 1819583 := bstep (se 1 (by rfl) ⟨1364687, by rfl⟩ : syracuseStep 1819583 = 2729375) B2729375
theorem B1819625 : Blo 1211423 1819625 := bstep (se 2 (by rfl) ⟨682359, by rfl⟩ : syracuseStep 1819625 = 1364719) B1364719
theorem B6554789 : Blo 1211423 6554789 := bstep (se 4 (by rfl) ⟨614511, by rfl⟩ : syracuseStep 6554789 = 1229023) B1229023
theorem B23307749 : Blo 1211423 23307749 := bstep (se 4 (by rfl) ⟨2185101, by rfl⟩ : syracuseStep 23307749 = 4370203) B4370203
theorem B3885023 : Blo 1211423 3885023 := bstep (se 1 (by rfl) ⟨2913767, by rfl⟩ : syracuseStep 3885023 = 5827535) B5827535
theorem B6900349 : Blo 1211423 6900349 := bstep (se 3 (by rfl) ⟨1293815, by rfl⟩ : syracuseStep 6900349 = 2587631) B2587631
theorem B3066599 : Blo 1211423 3066599 := bstep (se 1 (by rfl) ⟨2299949, by rfl⟩ : syracuseStep 3066599 = 4599899) B4599899
theorem B4090877 : Blo 1211423 4090877 := bstep (se 3 (by rfl) ⟨767039, by rfl⟩ : syracuseStep 4090877 = 1534079) B1534079
theorem B17960363 : Blo 1211423 17960363 := bstep (se 1 (by rfl) ⟨13470272, by rfl⟩ : syracuseStep 17960363 = 26940545) B26940545
theorem B13807259 : Blo 1211423 13807259 := bstep (se 1 (by rfl) ⟨10355444, by rfl⟩ : syracuseStep 13807259 = 20710889) B20710889
theorem B1363675 : Blo 1211423 1363675 := bstep (se 1 (by rfl) ⟨1022756, by rfl⟩ : syracuseStep 1363675 = 2045513) B2045513
theorem B13119259 : Blo 1211423 13119259 := bstep (se 1 (by rfl) ⟨9839444, by rfl⟩ : syracuseStep 13119259 = 19678889) B19678889
theorem B6910055 : Blo 1211423 6910055 := bstep (se 1 (by rfl) ⟨5182541, by rfl⟩ : syracuseStep 6910055 = 10365083) B10365083
theorem B9203867 : Blo 1211423 9203867 := bstep (se 1 (by rfl) ⟨6902900, by rfl⟩ : syracuseStep 9203867 = 13805801) B13805801
theorem B92156237 : Blo 1211423 92156237 := bstep (se 3 (by rfl) ⟨17279294, by rfl⟩ : syracuseStep 92156237 = 34558589) B34558589
theorem B2659007 : Blo 1211423 2659007 := bstep (se 1 (by rfl) ⟨1994255, by rfl⟩ : syracuseStep 2659007 = 3988511) B3988511
theorem B3453911 : Blo 1211423 3453911 := bstep (se 1 (by rfl) ⟨2590433, by rfl⟩ : syracuseStep 3453911 = 5180867) B5180867
theorem B2766287 : Blo 1211423 2766287 := bstep (se 1 (by rfl) ⟨2074715, by rfl⟩ : syracuseStep 2766287 = 4149431) B4149431
theorem B6903539 : Blo 1211423 6903539 := bstep (se 1 (by rfl) ⟨5177654, by rfl⟩ : syracuseStep 6903539 = 10355309) B10355309
theorem B4093793 : Blo 1211423 4093793 := bstep (se 2 (by rfl) ⟨1535172, by rfl⟩ : syracuseStep 4093793 = 3070345) B3070345
theorem B2725991 : Blo 1211423 2725991 := bstep (se 1 (by rfl) ⟨2044493, by rfl⟩ : syracuseStep 2725991 = 4088987) B4088987
theorem B2726009 : Blo 1211423 2726009 := bstep (se 2 (by rfl) ⟨1022253, by rfl⟩ : syracuseStep 2726009 = 2044507) B2044507
theorem B2046073 : Blo 1211423 2046073 := bstep (se 2 (by rfl) ⟨767277, by rfl⟩ : syracuseStep 2046073 = 1534555) B1534555
theorem B1211503 : Blo 1211423 1211503 := bstep (se 1 (by rfl) ⟨908627, by rfl⟩ : syracuseStep 1211503 = 1817255) B1817255
theorem B6134939 : Blo 1211423 6134939 := bstep (se 1 (by rfl) ⟨4601204, by rfl⟩ : syracuseStep 6134939 = 9202409) B9202409
theorem B3112843 : Blo 1211423 3112843 := bstep (se 1 (by rfl) ⟨2334632, by rfl⟩ : syracuseStep 3112843 = 4669265) B4669265
theorem B1212447 : Blo 1211423 1212447 := bstep (se 1 (by rfl) ⟨909335, by rfl⟩ : syracuseStep 1212447 = 1818671) B1818671
theorem B6135911 : Blo 1211423 6135911 := bstep (se 1 (by rfl) ⟨4601933, by rfl⟩ : syracuseStep 6135911 = 9203867) B9203867
theorem B2728097 : Blo 1211423 2728097 := bstep (se 2 (by rfl) ⟨1023036, by rfl⟩ : syracuseStep 2728097 = 2046073) B2046073
theorem B1212863 : Blo 1211423 1212863 := bstep (se 1 (by rfl) ⟨909647, by rfl⟩ : syracuseStep 1212863 = 1819295) B1819295
theorem B1213055 : Blo 1211423 1213055 := bstep (se 1 (by rfl) ⟨909791, by rfl⟩ : syracuseStep 1213055 = 1819583) B1819583
theorem B2302607 : Blo 1211423 2302607 := bstep (se 1 (by rfl) ⟨1726955, by rfl⟩ : syracuseStep 2302607 = 3453911) B3453911
theorem B1213083 : Blo 1211423 1213083 := bstep (se 1 (by rfl) ⟨909812, by rfl⟩ : syracuseStep 1213083 = 1819625) B1819625
theorem B9200465 : Blo 1211423 9200465 := bstep (se 2 (by rfl) ⟨3450174, by rfl⟩ : syracuseStep 9200465 = 6900349) B6900349
theorem B1844191 : Blo 1211423 1844191 := bstep (se 1 (by rfl) ⟨1383143, by rfl⟩ : syracuseStep 1844191 = 2766287) B2766287
theorem B2729195 : Blo 1211423 2729195 := bstep (se 1 (by rfl) ⟨2046896, by rfl⟩ : syracuseStep 2729195 = 4093793) B4093793
theorem B4089959 : Blo 1211423 4089959 := bstep (se 1 (by rfl) ⟨3067469, by rfl⟩ : syracuseStep 4089959 = 6134939) B6134939
theorem B17492345 : Blo 1211423 17492345 := bstep (se 2 (by rfl) ⟨6559629, by rfl⟩ : syracuseStep 17492345 = 13119259) B13119259
theorem B4606703 : Blo 1211423 4606703 := bstep (se 1 (by rfl) ⟨3455027, by rfl⟩ : syracuseStep 4606703 = 6910055) B6910055
theorem B6908915 : Blo 1211423 6908915 := bstep (se 1 (by rfl) ⟨5181686, by rfl⟩ : syracuseStep 6908915 = 10363373) B10363373
theorem B1772671 : Blo 1211423 1772671 := bstep (se 1 (by rfl) ⟨1329503, by rfl⟩ : syracuseStep 1772671 = 2659007) B2659007
theorem B4369859 : Blo 1211423 4369859 := bstep (se 1 (by rfl) ⟨3277394, by rfl⟩ : syracuseStep 4369859 = 6554789) B6554789
theorem B2044399 : Blo 1211423 2044399 := bstep (se 1 (by rfl) ⟨1533299, by rfl⟩ : syracuseStep 2044399 = 3066599) B3066599
theorem B11973575 : Blo 1211423 11973575 := bstep (se 1 (by rfl) ⟨8980181, by rfl⟩ : syracuseStep 11973575 = 17960363) B17960363
theorem B9204839 : Blo 1211423 9204839 := bstep (se 1 (by rfl) ⟨6903629, by rfl⟩ : syracuseStep 9204839 = 13807259) B13807259
theorem B4150457 : Blo 1211423 4150457 := bstep (se 2 (by rfl) ⟨1556421, by rfl⟩ : syracuseStep 4150457 = 3112843) B3112843
theorem B10360061 : Blo 1211423 10360061 := bstep (se 3 (by rfl) ⟨1942511, by rfl⟩ : syracuseStep 10360061 = 3885023) B3885023
theorem B61437491 : Blo 1211423 61437491 := bstep (se 1 (by rfl) ⟨46078118, by rfl⟩ : syracuseStep 61437491 = 92156237) B92156237
theorem B141645635 : Blo 1211423 141645635 := bstep (se 1 (by rfl) ⟨106234226, by rfl⟩ : syracuseStep 141645635 = 212468453) B212468453
theorem B13801427 : Blo 1211423 13801427 := bstep (se 1 (by rfl) ⟨10351070, by rfl⟩ : syracuseStep 13801427 = 20702141) B20702141
theorem B15538499 : Blo 1211423 15538499 := bstep (se 1 (by rfl) ⟨11653874, by rfl⟩ : syracuseStep 15538499 = 23307749) B23307749
theorem B4602359 : Blo 1211423 4602359 := bstep (se 1 (by rfl) ⟨3451769, by rfl⟩ : syracuseStep 4602359 = 6903539) B6903539
theorem B1817327 : Blo 1211423 1817327 := bstep (se 1 (by rfl) ⟨1362995, by rfl⟩ : syracuseStep 1817327 = 2725991) B2725991
theorem B1817339 : Blo 1211423 1817339 := bstep (se 1 (by rfl) ⟨1363004, by rfl⟩ : syracuseStep 1817339 = 2726009) B2726009
theorem B2727251 : Blo 1211423 2727251 := bstep (se 1 (by rfl) ⟨2045438, by rfl⟩ : syracuseStep 2727251 = 4090877) B4090877
theorem B1818233 : Blo 1211423 1818233 := bstep (se 2 (by rfl) ⟨681837, by rfl⟩ : syracuseStep 1818233 = 1363675) B1363675
theorem B1818731 : Blo 1211423 1818731 := bstep (se 1 (by rfl) ⟨1364048, by rfl⟩ : syracuseStep 1818731 = 2728097) B2728097
theorem B6136559 : Blo 1211423 6136559 := bstep (se 1 (by rfl) ⟨4602419, by rfl⟩ : syracuseStep 6136559 = 9204839) B9204839
theorem B1819463 : Blo 1211423 1819463 := bstep (se 1 (by rfl) ⟨1364597, by rfl⟩ : syracuseStep 1819463 = 2729195) B2729195
theorem B6906707 : Blo 1211423 6906707 := bstep (se 1 (by rfl) ⟨5180030, by rfl⟩ : syracuseStep 6906707 = 10360061) B10360061
theorem B94430423 : Blo 1211423 94430423 := bstep (se 1 (by rfl) ⟨70822817, by rfl⟩ : syracuseStep 94430423 = 141645635) B141645635
theorem B2458921 : Blo 1211423 2458921 := bstep (se 2 (by rfl) ⟨922095, by rfl⟩ : syracuseStep 2458921 = 1844191) B1844191
theorem B9200951 : Blo 1211423 9200951 := bstep (se 1 (by rfl) ⟨6900713, by rfl⟩ : syracuseStep 9200951 = 13801427) B13801427
theorem B4605943 : Blo 1211423 4605943 := bstep (se 1 (by rfl) ⟨3454457, by rfl⟩ : syracuseStep 4605943 = 6908915) B6908915
theorem B4090607 : Blo 1211423 4090607 := bstep (se 1 (by rfl) ⟨3067955, by rfl⟩ : syracuseStep 4090607 = 6135911) B6135911
theorem B7982383 : Blo 1211423 7982383 := bstep (se 1 (by rfl) ⟨5986787, by rfl⟩ : syracuseStep 7982383 = 11973575) B11973575
theorem B2363561 : Blo 1211423 2363561 := bstep (se 2 (by rfl) ⟨886335, by rfl⟩ : syracuseStep 2363561 = 1772671) B1772671
theorem B10358999 : Blo 1211423 10358999 := bstep (se 1 (by rfl) ⟨7769249, by rfl⟩ : syracuseStep 10358999 = 15538499) B15538499
theorem B11661563 : Blo 1211423 11661563 := bstep (se 1 (by rfl) ⟨8746172, by rfl⟩ : syracuseStep 11661563 = 17492345) B17492345
theorem B3068239 : Blo 1211423 3068239 := bstep (se 1 (by rfl) ⟨2301179, by rfl⟩ : syracuseStep 3068239 = 4602359) B4602359
theorem B6140285 : Blo 1211423 6140285 := bstep (se 3 (by rfl) ⟨1151303, by rfl⟩ : syracuseStep 6140285 = 2302607) B2302607
theorem B2913239 : Blo 1211423 2913239 := bstep (se 1 (by rfl) ⟨2184929, by rfl⟩ : syracuseStep 2913239 = 4369859) B4369859
theorem B6133643 : Blo 1211423 6133643 := bstep (se 1 (by rfl) ⟨4600232, by rfl⟩ : syracuseStep 6133643 = 9200465) B9200465
theorem B2725865 : Blo 1211423 2725865 := bstep (se 2 (by rfl) ⟨1022199, by rfl⟩ : syracuseStep 2725865 = 2044399) B2044399
theorem B2766971 : Blo 1211423 2766971 := bstep (se 1 (by rfl) ⟨2075228, by rfl⟩ : syracuseStep 2766971 = 4150457) B4150457
theorem B40958327 : Blo 1211423 40958327 := bstep (se 1 (by rfl) ⟨30718745, by rfl⟩ : syracuseStep 40958327 = 61437491) B61437491
theorem B2726639 : Blo 1211423 2726639 := bstep (se 1 (by rfl) ⟨2044979, by rfl⟩ : syracuseStep 2726639 = 4089959) B4089959
theorem B1211551 : Blo 1211423 1211551 := bstep (se 1 (by rfl) ⟨908663, by rfl⟩ : syracuseStep 1211551 = 1817327) B1817327
theorem B3071135 : Blo 1211423 3071135 := bstep (se 1 (by rfl) ⟨2303351, by rfl⟩ : syracuseStep 3071135 = 4606703) B4606703
theorem B1211559 : Blo 1211423 1211559 := bstep (se 1 (by rfl) ⟨908669, by rfl⟩ : syracuseStep 1211559 = 1817339) B1817339
theorem B1818167 : Blo 1211423 1818167 := bstep (se 1 (by rfl) ⟨1363625, by rfl⟩ : syracuseStep 1818167 = 2727251) B2727251
theorem B1212155 : Blo 1211423 1212155 := bstep (se 1 (by rfl) ⟨909116, by rfl⟩ : syracuseStep 1212155 = 1818233) B1818233
theorem B1212487 : Blo 1211423 1212487 := bstep (se 1 (by rfl) ⟨909365, by rfl⟩ : syracuseStep 1212487 = 1818731) B1818731
theorem B6905999 : Blo 1211423 6905999 := bstep (se 1 (by rfl) ⟨5179499, by rfl⟩ : syracuseStep 6905999 = 10358999) B10358999
theorem B7774375 : Blo 1211423 7774375 := bstep (se 1 (by rfl) ⟨5830781, by rfl⟩ : syracuseStep 7774375 = 11661563) B11661563
theorem B1212975 : Blo 1211423 1212975 := bstep (se 1 (by rfl) ⟨909731, by rfl⟩ : syracuseStep 1212975 = 1819463) B1819463
theorem B4604471 : Blo 1211423 4604471 := bstep (se 1 (by rfl) ⟨3453353, by rfl⟩ : syracuseStep 4604471 = 6906707) B6906707
theorem B1942159 : Blo 1211423 1942159 := bstep (se 1 (by rfl) ⟨1456619, by rfl⟩ : syracuseStep 1942159 = 2913239) B2913239
theorem B4089095 : Blo 1211423 4089095 := bstep (se 1 (by rfl) ⟨3066821, by rfl⟩ : syracuseStep 4089095 = 6133643) B6133643
theorem B27305551 : Blo 1211423 27305551 := bstep (se 1 (by rfl) ⟨20479163, by rfl⟩ : syracuseStep 27305551 = 40958327) B40958327
theorem B3278561 : Blo 1211423 3278561 := bstep (se 2 (by rfl) ⟨1229460, by rfl⟩ : syracuseStep 3278561 = 2458921) B2458921
theorem B10643177 : Blo 1211423 10643177 := bstep (se 2 (by rfl) ⟨3991191, by rfl⟩ : syracuseStep 10643177 = 7982383) B7982383
theorem B1575707 : Blo 1211423 1575707 := bstep (se 1 (by rfl) ⟨1181780, by rfl⟩ : syracuseStep 1575707 = 2363561) B2363561
theorem B4090985 : Blo 1211423 4090985 := bstep (se 2 (by rfl) ⟨1534119, by rfl⟩ : syracuseStep 4090985 = 3068239) B3068239
theorem B4091039 : Blo 1211423 4091039 := bstep (se 1 (by rfl) ⟨3068279, by rfl⟩ : syracuseStep 4091039 = 6136559) B6136559
theorem B6141257 : Blo 1211423 6141257 := bstep (se 2 (by rfl) ⟨2302971, by rfl⟩ : syracuseStep 6141257 = 4605943) B4605943
theorem B4093523 : Blo 1211423 4093523 := bstep (se 1 (by rfl) ⟨3070142, by rfl⟩ : syracuseStep 4093523 = 6140285) B6140285
theorem B7378589 : Blo 1211423 7378589 := bstep (se 3 (by rfl) ⟨1383485, by rfl⟩ : syracuseStep 7378589 = 2766971) B2766971
theorem B62953615 : Blo 1211423 62953615 := bstep (se 1 (by rfl) ⟨47215211, by rfl⟩ : syracuseStep 62953615 = 94430423) B94430423
theorem B6133967 : Blo 1211423 6133967 := bstep (se 1 (by rfl) ⟨4600475, by rfl⟩ : syracuseStep 6133967 = 9200951) B9200951
theorem B1817243 : Blo 1211423 1817243 := bstep (se 1 (by rfl) ⟨1362932, by rfl⟩ : syracuseStep 1817243 = 2725865) B2725865
theorem B1817759 : Blo 1211423 1817759 := bstep (se 1 (by rfl) ⟨1363319, by rfl⟩ : syracuseStep 1817759 = 2726639) B2726639
theorem B2727071 : Blo 1211423 2727071 := bstep (se 1 (by rfl) ⟨2045303, by rfl⟩ : syracuseStep 2727071 = 4090607) B4090607
theorem B2047423 : Blo 1211423 2047423 := bstep (se 1 (by rfl) ⟨1535567, by rfl⟩ : syracuseStep 2047423 = 3071135) B3071135
theorem B1212111 : Blo 1211423 1212111 := bstep (se 1 (by rfl) ⟨909083, by rfl⟩ : syracuseStep 1212111 = 1818167) B1818167
theorem B4603999 : Blo 1211423 4603999 := bstep (se 1 (by rfl) ⟨3452999, by rfl⟩ : syracuseStep 4603999 = 6905999) B6905999
theorem B2589545 : Blo 1211423 2589545 := bstep (se 2 (by rfl) ⟨971079, by rfl⟩ : syracuseStep 2589545 = 1942159) B1942159
theorem B2729015 : Blo 1211423 2729015 := bstep (se 1 (by rfl) ⟨2046761, by rfl⟩ : syracuseStep 2729015 = 4093523) B4093523
theorem B7095451 : Blo 1211423 7095451 := bstep (se 1 (by rfl) ⟨5321588, by rfl⟩ : syracuseStep 7095451 = 10643177) B10643177
theorem B4089311 : Blo 1211423 4089311 := bstep (se 1 (by rfl) ⟨3066983, by rfl⟩ : syracuseStep 4089311 = 6133967) B6133967
theorem B2729897 : Blo 1211423 2729897 := bstep (se 2 (by rfl) ⟨1023711, by rfl⟩ : syracuseStep 2729897 = 2047423) B2047423
theorem B8742829 : Blo 1211423 8742829 := bstep (se 3 (by rfl) ⟨1639280, by rfl⟩ : syracuseStep 8742829 = 3278561) B3278561
theorem B36407401 : Blo 1211423 36407401 := bstep (se 2 (by rfl) ⟨13652775, by rfl⟩ : syracuseStep 36407401 = 27305551) B27305551
theorem B83938153 : Blo 1211423 83938153 := bstep (se 2 (by rfl) ⟨31476807, by rfl⟩ : syracuseStep 83938153 = 62953615) B62953615
theorem B10365833 : Blo 1211423 10365833 := bstep (se 2 (by rfl) ⟨3887187, by rfl⟩ : syracuseStep 10365833 = 7774375) B7774375
theorem B4919059 : Blo 1211423 4919059 := bstep (se 1 (by rfl) ⟨3689294, by rfl⟩ : syracuseStep 4919059 = 7378589) B7378589
theorem B3069647 : Blo 1211423 3069647 := bstep (se 1 (by rfl) ⟨2302235, by rfl⟩ : syracuseStep 3069647 = 4604471) B4604471
theorem B2726063 : Blo 1211423 2726063 := bstep (se 1 (by rfl) ⟨2044547, by rfl⟩ : syracuseStep 2726063 = 4089095) B4089095
theorem B4094171 : Blo 1211423 4094171 := bstep (se 1 (by rfl) ⟨3070628, by rfl⟩ : syracuseStep 4094171 = 6141257) B6141257
theorem B1211495 : Blo 1211423 1211495 := bstep (se 1 (by rfl) ⟨908621, by rfl⟩ : syracuseStep 1211495 = 1817243) B1817243
theorem B4201885 : Blo 1211423 4201885 := bstep (se 3 (by rfl) ⟨787853, by rfl⟩ : syracuseStep 4201885 = 1575707) B1575707
theorem B2727323 : Blo 1211423 2727323 := bstep (se 1 (by rfl) ⟨2045492, by rfl⟩ : syracuseStep 2727323 = 4090985) B4090985
theorem B1211839 : Blo 1211423 1211839 := bstep (se 1 (by rfl) ⟨908879, by rfl⟩ : syracuseStep 1211839 = 1817759) B1817759
theorem B1818047 : Blo 1211423 1818047 := bstep (se 1 (by rfl) ⟨1363535, by rfl⟩ : syracuseStep 1818047 = 2727071) B2727071
theorem B2727359 : Blo 1211423 2727359 := bstep (se 1 (by rfl) ⟨2045519, by rfl⟩ : syracuseStep 2727359 = 4091039) B4091039
theorem B1819343 : Blo 1211423 1819343 := bstep (se 1 (by rfl) ⟨1364507, by rfl⟩ : syracuseStep 1819343 = 2729015) B2729015
theorem B1819931 : Blo 1211423 1819931 := bstep (se 1 (by rfl) ⟨1364948, by rfl⟩ : syracuseStep 1819931 = 2729897) B2729897
theorem B2729447 : Blo 1211423 2729447 := bstep (se 1 (by rfl) ⟨2047085, by rfl⟩ : syracuseStep 2729447 = 4094171) B4094171
theorem B6138665 : Blo 1211423 6138665 := bstep (se 2 (by rfl) ⟨2301999, by rfl⟩ : syracuseStep 6138665 = 4603999) B4603999
theorem B6910555 : Blo 1211423 6910555 := bstep (se 1 (by rfl) ⟨5182916, by rfl⟩ : syracuseStep 6910555 = 10365833) B10365833
theorem B22410053 : Blo 1211423 22410053 := bstep (se 4 (by rfl) ⟨2100942, by rfl⟩ : syracuseStep 22410053 = 4201885) B4201885
theorem B6558745 : Blo 1211423 6558745 := bstep (se 2 (by rfl) ⟨2459529, by rfl⟩ : syracuseStep 6558745 = 4919059) B4919059
theorem B194172805 : Blo 1211423 194172805 := bstep (se 4 (by rfl) ⟨18203700, by rfl⟩ : syracuseStep 194172805 = 36407401) B36407401
theorem B1726363 : Blo 1211423 1726363 := bstep (se 1 (by rfl) ⟨1294772, by rfl⟩ : syracuseStep 1726363 = 2589545) B2589545
theorem B2726207 : Blo 1211423 2726207 := bstep (se 1 (by rfl) ⟨2044655, by rfl⟩ : syracuseStep 2726207 = 4089311) B4089311
theorem B2046431 : Blo 1211423 2046431 := bstep (se 1 (by rfl) ⟨1534823, by rfl⟩ : syracuseStep 2046431 = 3069647) B3069647
theorem B111917537 : Blo 1211423 111917537 := bstep (se 2 (by rfl) ⟨41969076, by rfl⟩ : syracuseStep 111917537 = 83938153) B83938153
theorem B1817375 : Blo 1211423 1817375 := bstep (se 1 (by rfl) ⟨1363031, by rfl⟩ : syracuseStep 1817375 = 2726063) B2726063
theorem B9460601 : Blo 1211423 9460601 := bstep (se 2 (by rfl) ⟨3547725, by rfl⟩ : syracuseStep 9460601 = 7095451) B7095451
theorem B1818215 : Blo 1211423 1818215 := bstep (se 1 (by rfl) ⟨1363661, by rfl⟩ : syracuseStep 1818215 = 2727323) B2727323
theorem B1212031 : Blo 1211423 1212031 := bstep (se 1 (by rfl) ⟨909023, by rfl⟩ : syracuseStep 1212031 = 1818047) B1818047
theorem B1818239 : Blo 1211423 1818239 := bstep (se 1 (by rfl) ⟨1363679, by rfl⟩ : syracuseStep 1818239 = 2727359) B2727359
theorem B11657105 : Blo 1211423 11657105 := bstep (se 2 (by rfl) ⟨4371414, by rfl⟩ : syracuseStep 11657105 = 8742829) B8742829
theorem B1212895 : Blo 1211423 1212895 := bstep (se 1 (by rfl) ⟨909671, by rfl⟩ : syracuseStep 1212895 = 1819343) B1819343
theorem B1213287 : Blo 1211423 1213287 := bstep (se 1 (by rfl) ⟨909965, by rfl⟩ : syracuseStep 1213287 = 1819931) B1819931
theorem B1819631 : Blo 1211423 1819631 := bstep (se 1 (by rfl) ⟨1364723, by rfl⟩ : syracuseStep 1819631 = 2729447) B2729447
theorem B8744993 : Blo 1211423 8744993 := bstep (se 2 (by rfl) ⟨3279372, by rfl⟩ : syracuseStep 8744993 = 6558745) B6558745
theorem B1364287 : Blo 1211423 1364287 := bstep (se 1 (by rfl) ⟨1023215, by rfl⟩ : syracuseStep 1364287 = 2046431) B2046431
theorem B4092443 : Blo 1211423 4092443 := bstep (se 1 (by rfl) ⟨3069332, by rfl⟩ : syracuseStep 4092443 = 6138665) B6138665
theorem B258897073 : Blo 1211423 258897073 := bstep (se 2 (by rfl) ⟨97086402, by rfl⟩ : syracuseStep 258897073 = 194172805) B194172805
theorem B7771403 : Blo 1211423 7771403 := bstep (se 1 (by rfl) ⟨5828552, by rfl⟩ : syracuseStep 7771403 = 11657105) B11657105
theorem B14940035 : Blo 1211423 14940035 := bstep (se 1 (by rfl) ⟨11205026, by rfl⟩ : syracuseStep 14940035 = 22410053) B22410053
theorem B9214073 : Blo 1211423 9214073 := bstep (se 2 (by rfl) ⟨3455277, by rfl⟩ : syracuseStep 9214073 = 6910555) B6910555
theorem B1817471 : Blo 1211423 1817471 := bstep (se 1 (by rfl) ⟨1363103, by rfl⟩ : syracuseStep 1817471 = 2726207) B2726207
theorem B74611691 : Blo 1211423 74611691 := bstep (se 1 (by rfl) ⟨55958768, by rfl⟩ : syracuseStep 74611691 = 111917537) B111917537
theorem B1211583 : Blo 1211423 1211583 := bstep (se 1 (by rfl) ⟨908687, by rfl⟩ : syracuseStep 1211583 = 1817375) B1817375
theorem B6307067 : Blo 1211423 6307067 := bstep (se 1 (by rfl) ⟨4730300, by rfl⟩ : syracuseStep 6307067 = 9460601) B9460601
theorem B9207269 : Blo 1211423 9207269 := bstep (se 4 (by rfl) ⟨863181, by rfl⟩ : syracuseStep 9207269 = 1726363) B1726363
theorem B1212143 : Blo 1211423 1212143 := bstep (se 1 (by rfl) ⟨909107, by rfl⟩ : syracuseStep 1212143 = 1818215) B1818215
theorem B1212159 : Blo 1211423 1212159 := bstep (se 1 (by rfl) ⟨909119, by rfl⟩ : syracuseStep 1212159 = 1818239) B1818239
theorem B2728295 : Blo 1211423 2728295 := bstep (se 1 (by rfl) ⟨2046221, by rfl⟩ : syracuseStep 2728295 = 4092443) B4092443
theorem B1819049 : Blo 1211423 1819049 := bstep (se 2 (by rfl) ⟨682143, by rfl⟩ : syracuseStep 1819049 = 1364287) B1364287
theorem B1213087 : Blo 1211423 1213087 := bstep (se 1 (by rfl) ⟨909815, by rfl⟩ : syracuseStep 1213087 = 1819631) B1819631
theorem B345196097 : Blo 1211423 345196097 := bstep (se 2 (by rfl) ⟨129448536, by rfl⟩ : syracuseStep 345196097 = 258897073) B258897073
theorem B4204711 : Blo 1211423 4204711 := bstep (se 1 (by rfl) ⟨3153533, by rfl⟩ : syracuseStep 4204711 = 6307067) B6307067
theorem B6138179 : Blo 1211423 6138179 := bstep (se 1 (by rfl) ⟨4603634, by rfl⟩ : syracuseStep 6138179 = 9207269) B9207269
theorem B5180935 : Blo 1211423 5180935 := bstep (se 1 (by rfl) ⟨3885701, by rfl⟩ : syracuseStep 5180935 = 7771403) B7771403
theorem B5829995 : Blo 1211423 5829995 := bstep (se 1 (by rfl) ⟨4372496, by rfl⟩ : syracuseStep 5829995 = 8744993) B8744993
theorem B9960023 : Blo 1211423 9960023 := bstep (se 1 (by rfl) ⟨7470017, by rfl⟩ : syracuseStep 9960023 = 14940035) B14940035
theorem B6142715 : Blo 1211423 6142715 := bstep (se 1 (by rfl) ⟨4607036, by rfl⟩ : syracuseStep 6142715 = 9214073) B9214073
theorem B1211647 : Blo 1211423 1211647 := bstep (se 1 (by rfl) ⟨908735, by rfl⟩ : syracuseStep 1211647 = 1817471) B1817471
theorem B49741127 : Blo 1211423 49741127 := bstep (se 1 (by rfl) ⟨37305845, by rfl⟩ : syracuseStep 49741127 = 74611691) B74611691
theorem B1818863 : Blo 1211423 1818863 := bstep (se 1 (by rfl) ⟨1364147, by rfl⟩ : syracuseStep 1818863 = 2728295) B2728295
theorem B1212699 : Blo 1211423 1212699 := bstep (se 1 (by rfl) ⟨909524, by rfl⟩ : syracuseStep 1212699 = 1819049) B1819049
theorem B230130731 : Blo 1211423 230130731 := bstep (se 1 (by rfl) ⟨172598048, by rfl⟩ : syracuseStep 230130731 = 345196097) B345196097
theorem B6907913 : Blo 1211423 6907913 := bstep (se 2 (by rfl) ⟨2590467, by rfl⟩ : syracuseStep 6907913 = 5180935) B5180935
theorem B5606281 : Blo 1211423 5606281 := bstep (se 2 (by rfl) ⟨2102355, by rfl⟩ : syracuseStep 5606281 = 4204711) B4204711
theorem B4092119 : Blo 1211423 4092119 := bstep (se 1 (by rfl) ⟨3069089, by rfl⟩ : syracuseStep 4092119 = 6138179) B6138179
theorem B6640015 : Blo 1211423 6640015 := bstep (se 1 (by rfl) ⟨4980011, by rfl⟩ : syracuseStep 6640015 = 9960023) B9960023
theorem B15546653 : Blo 1211423 15546653 := bstep (se 3 (by rfl) ⟨2914997, by rfl⟩ : syracuseStep 15546653 = 5829995) B5829995
theorem B4095143 : Blo 1211423 4095143 := bstep (se 1 (by rfl) ⟨3071357, by rfl⟩ : syracuseStep 4095143 = 6142715) B6142715
theorem B33160751 : Blo 1211423 33160751 := bstep (se 1 (by rfl) ⟨24870563, by rfl⟩ : syracuseStep 33160751 = 49741127) B49741127
theorem B2728079 : Blo 1211423 2728079 := bstep (se 1 (by rfl) ⟨2046059, by rfl⟩ : syracuseStep 2728079 = 4092119) B4092119
theorem B1212575 : Blo 1211423 1212575 := bstep (se 1 (by rfl) ⟨909431, by rfl⟩ : syracuseStep 1212575 = 1818863) B1818863
theorem B4605275 : Blo 1211423 4605275 := bstep (se 1 (by rfl) ⟨3453956, by rfl⟩ : syracuseStep 4605275 = 6907913) B6907913
theorem B10364435 : Blo 1211423 10364435 := bstep (se 1 (by rfl) ⟨7773326, by rfl⟩ : syracuseStep 10364435 = 15546653) B15546653
theorem B2730095 : Blo 1211423 2730095 := bstep (se 1 (by rfl) ⟨2047571, by rfl⟩ : syracuseStep 2730095 = 4095143) B4095143
theorem B613681949 : Blo 1211423 613681949 := bstep (se 3 (by rfl) ⟨115065365, by rfl⟩ : syracuseStep 613681949 = 230130731) B230130731
theorem B7475041 : Blo 1211423 7475041 := bstep (se 2 (by rfl) ⟨2803140, by rfl⟩ : syracuseStep 7475041 = 5606281) B5606281
theorem B22107167 : Blo 1211423 22107167 := bstep (se 1 (by rfl) ⟨16580375, by rfl⟩ : syracuseStep 22107167 = 33160751) B33160751
theorem B8853353 : Blo 1211423 8853353 := bstep (se 2 (by rfl) ⟨3320007, by rfl⟩ : syracuseStep 8853353 = 6640015) B6640015
theorem B1818719 : Blo 1211423 1818719 := bstep (se 1 (by rfl) ⟨1364039, by rfl⟩ : syracuseStep 1818719 = 2728079) B2728079
theorem B14738111 : Blo 1211423 14738111 := bstep (se 1 (by rfl) ⟨11053583, by rfl⟩ : syracuseStep 14738111 = 22107167) B22107167
theorem B1820063 : Blo 1211423 1820063 := bstep (se 1 (by rfl) ⟨1365047, by rfl⟩ : syracuseStep 1820063 = 2730095) B2730095
theorem B1636485197 : Blo 1211423 1636485197 := bstep (se 3 (by rfl) ⟨306840974, by rfl⟩ : syracuseStep 1636485197 = 613681949) B613681949
theorem B6909623 : Blo 1211423 6909623 := bstep (se 1 (by rfl) ⟨5182217, by rfl⟩ : syracuseStep 6909623 = 10364435) B10364435
theorem B5902235 : Blo 1211423 5902235 := bstep (se 1 (by rfl) ⟨4426676, by rfl⟩ : syracuseStep 5902235 = 8853353) B8853353
theorem B9966721 : Blo 1211423 9966721 := bstep (se 2 (by rfl) ⟨3737520, by rfl⟩ : syracuseStep 9966721 = 7475041) B7475041
theorem B3070183 : Blo 1211423 3070183 := bstep (se 1 (by rfl) ⟨2302637, by rfl⟩ : syracuseStep 3070183 = 4605275) B4605275
theorem B1212479 : Blo 1211423 1212479 := bstep (se 1 (by rfl) ⟨909359, by rfl⟩ : syracuseStep 1212479 = 1818719) B1818719
theorem B17455842101 : Blo 1211423 17455842101 := bstep (se 5 (by rfl) ⟨818242598, by rfl⟩ : syracuseStep 17455842101 = 1636485197) B1636485197
theorem B1213375 : Blo 1211423 1213375 := bstep (se 1 (by rfl) ⟨910031, by rfl⟩ : syracuseStep 1213375 = 1820063) B1820063
theorem B13288961 : Blo 1211423 13288961 := bstep (se 2 (by rfl) ⟨4983360, by rfl⟩ : syracuseStep 13288961 = 9966721) B9966721
theorem B4606415 : Blo 1211423 4606415 := bstep (se 1 (by rfl) ⟨3454811, by rfl⟩ : syracuseStep 4606415 = 6909623) B6909623
theorem B3934823 : Blo 1211423 3934823 := bstep (se 1 (by rfl) ⟨2951117, by rfl⟩ : syracuseStep 3934823 = 5902235) B5902235
theorem B9825407 : Blo 1211423 9825407 := bstep (se 1 (by rfl) ⟨7369055, by rfl⟩ : syracuseStep 9825407 = 14738111) B14738111
theorem B4093577 : Blo 1211423 4093577 := bstep (se 2 (by rfl) ⟨1535091, by rfl⟩ : syracuseStep 4093577 = 3070183) B3070183
theorem B2729051 : Blo 1211423 2729051 := bstep (se 1 (by rfl) ⟨2046788, by rfl⟩ : syracuseStep 2729051 = 4093577) B4093577
theorem B46548912269 : Blo 1211423 46548912269 := bstep (se 3 (by rfl) ⟨8727921050, by rfl⟩ : syracuseStep 46548912269 = 17455842101) B17455842101
theorem B8859307 : Blo 1211423 8859307 := bstep (se 1 (by rfl) ⟨6644480, by rfl⟩ : syracuseStep 8859307 = 13288961) B13288961
theorem B6550271 : Blo 1211423 6550271 := bstep (se 1 (by rfl) ⟨4912703, by rfl⟩ : syracuseStep 6550271 = 9825407) B9825407
theorem B10492861 : Blo 1211423 10492861 := bstep (se 3 (by rfl) ⟨1967411, by rfl⟩ : syracuseStep 10492861 = 3934823) B3934823
theorem B3070943 : Blo 1211423 3070943 := bstep (se 1 (by rfl) ⟨2303207, by rfl⟩ : syracuseStep 3070943 = 4606415) B4606415
theorem B4366847 : Blo 1211423 4366847 := bstep (se 1 (by rfl) ⟨3275135, by rfl⟩ : syracuseStep 4366847 = 6550271) B6550271
theorem B1819367 : Blo 1211423 1819367 := bstep (se 1 (by rfl) ⟨1364525, by rfl⟩ : syracuseStep 1819367 = 2729051) B2729051
theorem B31032608179 : Blo 1211423 31032608179 := bstep (se 1 (by rfl) ⟨23274456134, by rfl⟩ : syracuseStep 31032608179 = 46548912269) B46548912269
theorem B13990481 : Blo 1211423 13990481 := bstep (se 2 (by rfl) ⟨5246430, by rfl⟩ : syracuseStep 13990481 = 10492861) B10492861
theorem B2047295 : Blo 1211423 2047295 := bstep (se 1 (by rfl) ⟨1535471, by rfl⟩ : syracuseStep 2047295 = 3070943) B3070943
theorem B11812409 : Blo 1211423 11812409 := bstep (se 2 (by rfl) ⟨4429653, by rfl⟩ : syracuseStep 11812409 = 8859307) B8859307
theorem B1212911 : Blo 1211423 1212911 := bstep (se 1 (by rfl) ⟨909683, by rfl⟩ : syracuseStep 1212911 = 1819367) B1819367
theorem B41376810905 : Blo 1211423 41376810905 := bstep (se 2 (by rfl) ⟨15516304089, by rfl⟩ : syracuseStep 41376810905 = 31032608179) B31032608179
theorem B7874939 : Blo 1211423 7874939 := bstep (se 1 (by rfl) ⟨5906204, by rfl⟩ : syracuseStep 7874939 = 11812409) B11812409
theorem B2911231 : Blo 1211423 2911231 := bstep (se 1 (by rfl) ⟨2183423, by rfl⟩ : syracuseStep 2911231 = 4366847) B4366847
theorem B9326987 : Blo 1211423 9326987 := bstep (se 1 (by rfl) ⟨6995240, by rfl⟩ : syracuseStep 9326987 = 13990481) B13990481
theorem B1364863 : Blo 1211423 1364863 := bstep (se 1 (by rfl) ⟨1023647, by rfl⟩ : syracuseStep 1364863 = 2047295) B2047295
theorem B6217991 : Blo 1211423 6217991 := bstep (se 1 (by rfl) ⟨4663493, by rfl⟩ : syracuseStep 6217991 = 9326987) B9326987
theorem B1819817 : Blo 1211423 1819817 := bstep (se 2 (by rfl) ⟨682431, by rfl⟩ : syracuseStep 1819817 = 1364863) B1364863
theorem B20999837 : Blo 1211423 20999837 := bstep (se 3 (by rfl) ⟨3937469, by rfl⟩ : syracuseStep 20999837 = 7874939) B7874939
theorem B27584540603 : Blo 1211423 27584540603 := bstep (se 1 (by rfl) ⟨20688405452, by rfl⟩ : syracuseStep 27584540603 = 41376810905) B41376810905
theorem B3881641 : Blo 1211423 3881641 := bstep (se 2 (by rfl) ⟨1455615, by rfl⟩ : syracuseStep 3881641 = 2911231) B2911231
theorem B4145327 : Blo 1211423 4145327 := bstep (se 1 (by rfl) ⟨3108995, by rfl⟩ : syracuseStep 4145327 = 6217991) B6217991
theorem B1213211 : Blo 1211423 1213211 := bstep (se 1 (by rfl) ⟨909908, by rfl⟩ : syracuseStep 1213211 = 1819817) B1819817
theorem B18389693735 : Blo 1211423 18389693735 := bstep (se 1 (by rfl) ⟨13792270301, by rfl⟩ : syracuseStep 18389693735 = 27584540603) B27584540603
theorem B5175521 : Blo 1211423 5175521 := bstep (se 2 (by rfl) ⟨1940820, by rfl⟩ : syracuseStep 5175521 = 3881641) B3881641
theorem B13999891 : Blo 1211423 13999891 := bstep (se 1 (by rfl) ⟨10499918, by rfl⟩ : syracuseStep 13999891 = 20999837) B20999837
theorem B12259795823 : Blo 1211423 12259795823 := bstep (se 1 (by rfl) ⟨9194846867, by rfl⟩ : syracuseStep 12259795823 = 18389693735) B18389693735
theorem B3450347 : Blo 1211423 3450347 := bstep (se 1 (by rfl) ⟨2587760, by rfl⟩ : syracuseStep 3450347 = 5175521) B5175521
theorem B2763551 : Blo 1211423 2763551 := bstep (se 1 (by rfl) ⟨2072663, by rfl⟩ : syracuseStep 2763551 = 4145327) B4145327
theorem B18666521 : Blo 1211423 18666521 := bstep (se 2 (by rfl) ⟨6999945, by rfl⟩ : syracuseStep 18666521 = 13999891) B13999891
theorem B12444347 : Blo 1211423 12444347 := bstep (se 1 (by rfl) ⟨9333260, by rfl⟩ : syracuseStep 12444347 = 18666521) B18666521
theorem B8173197215 : Blo 1211423 8173197215 := bstep (se 1 (by rfl) ⟨6129897911, by rfl⟩ : syracuseStep 8173197215 = 12259795823) B12259795823
theorem B2300231 : Blo 1211423 2300231 := bstep (se 1 (by rfl) ⟨1725173, by rfl⟩ : syracuseStep 2300231 = 3450347) B3450347
theorem B1842367 : Blo 1211423 1842367 := bstep (se 1 (by rfl) ⟨1381775, by rfl⟩ : syracuseStep 1842367 = 2763551) B2763551
theorem B1533487 : Blo 1211423 1533487 := bstep (se 1 (by rfl) ⟨1150115, by rfl⟩ : syracuseStep 1533487 = 2300231) B2300231
theorem B5448798143 : Blo 1211423 5448798143 := bstep (se 1 (by rfl) ⟨4086598607, by rfl⟩ : syracuseStep 5448798143 = 8173197215) B8173197215
theorem B8296231 : Blo 1211423 8296231 := bstep (se 1 (by rfl) ⟨6222173, by rfl⟩ : syracuseStep 8296231 = 12444347) B12444347
theorem B2456489 : Blo 1211423 2456489 := bstep (se 2 (by rfl) ⟨921183, by rfl⟩ : syracuseStep 2456489 = 1842367) B1842367
theorem B11061641 : Blo 1211423 11061641 := bstep (se 2 (by rfl) ⟨4148115, by rfl⟩ : syracuseStep 11061641 = 8296231) B8296231
theorem B3632532095 : Blo 1211423 3632532095 := bstep (se 1 (by rfl) ⟨2724399071, by rfl⟩ : syracuseStep 3632532095 = 5448798143) B5448798143
theorem B2044649 : Blo 1211423 2044649 := bstep (se 2 (by rfl) ⟨766743, by rfl⟩ : syracuseStep 2044649 = 1533487) B1533487
theorem B1637659 : Blo 1211423 1637659 := bstep (se 1 (by rfl) ⟨1228244, by rfl⟩ : syracuseStep 1637659 = 2456489) B2456489
theorem B1363099 : Blo 1211423 1363099 := bstep (se 1 (by rfl) ⟨1022324, by rfl⟩ : syracuseStep 1363099 = 2044649) B2044649
theorem B2183545 : Blo 1211423 2183545 := bstep (se 2 (by rfl) ⟨818829, by rfl⟩ : syracuseStep 2183545 = 1637659) B1637659
theorem B29497709 : Blo 1211423 29497709 := bstep (se 3 (by rfl) ⟨5530820, by rfl⟩ : syracuseStep 29497709 = 11061641) B11061641
theorem B9686752253 : Blo 1211423 9686752253 := bstep (se 3 (by rfl) ⟨1816266047, by rfl⟩ : syracuseStep 9686752253 = 3632532095) B3632532095
theorem B2911393 : Blo 1211423 2911393 := bstep (se 2 (by rfl) ⟨1091772, by rfl⟩ : syracuseStep 2911393 = 2183545) B2183545
theorem B19665139 : Blo 1211423 19665139 := bstep (se 1 (by rfl) ⟨14748854, by rfl⟩ : syracuseStep 19665139 = 29497709) B29497709
theorem B1817465 : Blo 1211423 1817465 := bstep (se 2 (by rfl) ⟨681549, by rfl⟩ : syracuseStep 1817465 = 1363099) B1363099
theorem B6457834835 : Blo 1211423 6457834835 := bstep (se 1 (by rfl) ⟨4843376126, by rfl⟩ : syracuseStep 6457834835 = 9686752253) B9686752253
theorem B26220185 : Blo 1211423 26220185 := bstep (se 2 (by rfl) ⟨9832569, by rfl⟩ : syracuseStep 26220185 = 19665139) B19665139
theorem B3881857 : Blo 1211423 3881857 := bstep (se 2 (by rfl) ⟨1455696, by rfl⟩ : syracuseStep 3881857 = 2911393) B2911393
theorem B1211643 : Blo 1211423 1211643 := bstep (se 1 (by rfl) ⟨908732, by rfl⟩ : syracuseStep 1211643 = 1817465) B1817465
theorem B4305223223 : Blo 1211423 4305223223 := bstep (se 1 (by rfl) ⟨3228917417, by rfl⟩ : syracuseStep 4305223223 = 6457834835) B6457834835
theorem B17480123 : Blo 1211423 17480123 := bstep (se 1 (by rfl) ⟨13110092, by rfl⟩ : syracuseStep 17480123 = 26220185) B26220185
theorem B5175809 : Blo 1211423 5175809 := bstep (se 2 (by rfl) ⟨1940928, by rfl⟩ : syracuseStep 5175809 = 3881857) B3881857
theorem B2870148815 : Blo 1211423 2870148815 := bstep (se 1 (by rfl) ⟨2152611611, by rfl⟩ : syracuseStep 2870148815 = 4305223223) B4305223223
theorem B3450539 : Blo 1211423 3450539 := bstep (se 1 (by rfl) ⟨2587904, by rfl⟩ : syracuseStep 3450539 = 5175809) B5175809
theorem B1913432543 : Blo 1211423 1913432543 := bstep (se 1 (by rfl) ⟨1435074407, by rfl⟩ : syracuseStep 1913432543 = 2870148815) B2870148815
theorem B11653415 : Blo 1211423 11653415 := bstep (se 1 (by rfl) ⟨8740061, by rfl⟩ : syracuseStep 11653415 = 17480123) B17480123
theorem B9201437 : Blo 1211423 9201437 := bstep (se 3 (by rfl) ⟨1725269, by rfl⟩ : syracuseStep 9201437 = 3450539) B3450539
theorem B7768943 : Blo 1211423 7768943 := bstep (se 1 (by rfl) ⟨5826707, by rfl⟩ : syracuseStep 7768943 = 11653415) B11653415
theorem B1275621695 : Blo 1211423 1275621695 := bstep (se 1 (by rfl) ⟨956716271, by rfl⟩ : syracuseStep 1275621695 = 1913432543) B1913432543
theorem B5179295 : Blo 1211423 5179295 := bstep (se 1 (by rfl) ⟨3884471, by rfl⟩ : syracuseStep 5179295 = 7768943) B7768943
theorem B850414463 : Blo 1211423 850414463 := bstep (se 1 (by rfl) ⟨637810847, by rfl⟩ : syracuseStep 850414463 = 1275621695) B1275621695
theorem B6134291 : Blo 1211423 6134291 := bstep (se 1 (by rfl) ⟨4600718, by rfl⟩ : syracuseStep 6134291 = 9201437) B9201437
theorem B4089527 : Blo 1211423 4089527 := bstep (se 1 (by rfl) ⟨3067145, by rfl⟩ : syracuseStep 4089527 = 6134291) B6134291
theorem B3452863 : Blo 1211423 3452863 := bstep (se 1 (by rfl) ⟨2589647, by rfl⟩ : syracuseStep 3452863 = 5179295) B5179295
theorem B566942975 : Blo 1211423 566942975 := bstep (se 1 (by rfl) ⟨425207231, by rfl⟩ : syracuseStep 566942975 = 850414463) B850414463
theorem B2726351 : Blo 1211423 2726351 := bstep (se 1 (by rfl) ⟨2044763, by rfl⟩ : syracuseStep 2726351 = 4089527) B4089527
theorem B377961983 : Blo 1211423 377961983 := bstep (se 1 (by rfl) ⟨283471487, by rfl⟩ : syracuseStep 377961983 = 566942975) B566942975
theorem B4603817 : Blo 1211423 4603817 := bstep (se 2 (by rfl) ⟨1726431, by rfl⟩ : syracuseStep 4603817 = 3452863) B3452863
theorem B251974655 : Blo 1211423 251974655 := bstep (se 1 (by rfl) ⟨188980991, by rfl⟩ : syracuseStep 251974655 = 377961983) B377961983
theorem B3069211 : Blo 1211423 3069211 := bstep (se 1 (by rfl) ⟨2301908, by rfl⟩ : syracuseStep 3069211 = 4603817) B4603817
theorem B1817567 : Blo 1211423 1817567 := bstep (se 1 (by rfl) ⟨1363175, by rfl⟩ : syracuseStep 1817567 = 2726351) B2726351
theorem B4092281 : Blo 1211423 4092281 := bstep (se 2 (by rfl) ⟨1534605, by rfl⟩ : syracuseStep 4092281 = 3069211) B3069211
theorem B167983103 : Blo 1211423 167983103 := bstep (se 1 (by rfl) ⟨125987327, by rfl⟩ : syracuseStep 167983103 = 251974655) B251974655
theorem B1211711 : Blo 1211423 1211711 := bstep (se 1 (by rfl) ⟨908783, by rfl⟩ : syracuseStep 1211711 = 1817567) B1817567
theorem B2728187 : Blo 1211423 2728187 := bstep (se 1 (by rfl) ⟨2046140, by rfl⟩ : syracuseStep 2728187 = 4092281) B4092281
theorem B447954941 : Blo 1211423 447954941 := bstep (se 3 (by rfl) ⟨83991551, by rfl⟩ : syracuseStep 447954941 = 167983103) B167983103
theorem B1818791 : Blo 1211423 1818791 := bstep (se 1 (by rfl) ⟨1364093, by rfl⟩ : syracuseStep 1818791 = 2728187) B2728187
theorem B298636627 : Blo 1211423 298636627 := bstep (se 1 (by rfl) ⟨223977470, by rfl⟩ : syracuseStep 298636627 = 447954941) B447954941
theorem B1212527 : Blo 1211423 1212527 := bstep (se 1 (by rfl) ⟨909395, by rfl⟩ : syracuseStep 1212527 = 1818791) B1818791
theorem B398182169 : Blo 1211423 398182169 := bstep (se 2 (by rfl) ⟨149318313, by rfl⟩ : syracuseStep 398182169 = 298636627) B298636627
theorem B265454779 : Blo 1211423 265454779 := bstep (se 1 (by rfl) ⟨199091084, by rfl⟩ : syracuseStep 265454779 = 398182169) B398182169
theorem B353939705 : Blo 1211423 353939705 := bstep (se 2 (by rfl) ⟨132727389, by rfl⟩ : syracuseStep 353939705 = 265454779) B265454779
theorem B235959803 : Blo 1211423 235959803 := bstep (se 1 (by rfl) ⟨176969852, by rfl⟩ : syracuseStep 235959803 = 353939705) B353939705
theorem B157306535 : Blo 1211423 157306535 := bstep (se 1 (by rfl) ⟨117979901, by rfl⟩ : syracuseStep 157306535 = 235959803) B235959803
theorem B104871023 : Blo 1211423 104871023 := bstep (se 1 (by rfl) ⟨78653267, by rfl⟩ : syracuseStep 104871023 = 157306535) B157306535
theorem B69914015 : Blo 1211423 69914015 := bstep (se 1 (by rfl) ⟨52435511, by rfl⟩ : syracuseStep 69914015 = 104871023) B104871023
theorem B46609343 : Blo 1211423 46609343 := bstep (se 1 (by rfl) ⟨34957007, by rfl⟩ : syracuseStep 46609343 = 69914015) B69914015
theorem B31072895 : Blo 1211423 31072895 := bstep (se 1 (by rfl) ⟨23304671, by rfl⟩ : syracuseStep 31072895 = 46609343) B46609343
theorem B20715263 : Blo 1211423 20715263 := bstep (se 1 (by rfl) ⟨15536447, by rfl⟩ : syracuseStep 20715263 = 31072895) B31072895
theorem B13810175 : Blo 1211423 13810175 := bstep (se 1 (by rfl) ⟨10357631, by rfl⟩ : syracuseStep 13810175 = 20715263) B20715263
theorem B9206783 : Blo 1211423 9206783 := bstep (se 1 (by rfl) ⟨6905087, by rfl⟩ : syracuseStep 9206783 = 13810175) B13810175
theorem B6137855 : Blo 1211423 6137855 := bstep (se 1 (by rfl) ⟨4603391, by rfl⟩ : syracuseStep 6137855 = 9206783) B9206783
theorem B4091903 : Blo 1211423 4091903 := bstep (se 1 (by rfl) ⟨3068927, by rfl⟩ : syracuseStep 4091903 = 6137855) B6137855
theorem B2727935 : Blo 1211423 2727935 := bstep (se 1 (by rfl) ⟨2045951, by rfl⟩ : syracuseStep 2727935 = 4091903) B4091903
theorem B1818623 : Blo 1211423 1818623 := bstep (se 1 (by rfl) ⟨1363967, by rfl⟩ : syracuseStep 1818623 = 2727935) B2727935
theorem B1212415 : Blo 1211423 1212415 := bstep (se 1 (by rfl) ⟨909311, by rfl⟩ : syracuseStep 1212415 = 1818623) B1818623

theorem C0 (j : ℕ) (h1 : 302855 ≤ j) (h2 : j ≤ 303355) : Blo 1211423 (4 * j + 3) := by
  interval_cases j
  · exact B1211423
  · exact B1211427
  · exact B1211431
  · exact B1211435
  · exact B1211439
  · exact B1211443
  · exact B1211447
  · exact B1211451
  · exact B1211455
  · exact B1211459
  · exact B1211463
  · exact B1211467
  · exact B1211471
  · exact B1211475
  · exact B1211479
  · exact B1211483
  · exact B1211487
  · exact B1211491
  · exact B1211495
  · exact B1211499
  · exact B1211503
  · exact B1211507
  · exact B1211511
  · exact B1211515
  · exact B1211519
  · exact B1211523
  · exact B1211527
  · exact B1211531
  · exact B1211535
  · exact B1211539
  · exact B1211543
  · exact B1211547
  · exact B1211551
  · exact B1211555
  · exact B1211559
  · exact B1211563
  · exact B1211567
  · exact B1211571
  · exact B1211575
  · exact B1211579
  · exact B1211583
  · exact B1211587
  · exact B1211591
  · exact B1211595
  · exact B1211599
  · exact B1211603
  · exact B1211607
  · exact B1211611
  · exact B1211615
  · exact B1211619
  · exact B1211623
  · exact B1211627
  · exact B1211631
  · exact B1211635
  · exact B1211639
  · exact B1211643
  · exact B1211647
  · exact B1211651
  · exact B1211655
  · exact B1211659
  · exact B1211663
  · exact B1211667
  · exact B1211671
  · exact B1211675
  · exact B1211679
  · exact B1211683
  · exact B1211687
  · exact B1211691
  · exact B1211695
  · exact B1211699
  · exact B1211703
  · exact B1211707
  · exact B1211711
  · exact B1211715
  · exact B1211719
  · exact B1211723
  · exact B1211727
  · exact B1211731
  · exact B1211735
  · exact B1211739
  · exact B1211743
  · exact B1211747
  · exact B1211751
  · exact B1211755
  · exact B1211759
  · exact B1211763
  · exact B1211767
  · exact B1211771
  · exact B1211775
  · exact B1211779
  · exact B1211783
  · exact B1211787
  · exact B1211791
  · exact B1211795
  · exact B1211799
  · exact B1211803
  · exact B1211807
  · exact B1211811
  · exact B1211815
  · exact B1211819
  · exact B1211823
  · exact B1211827
  · exact B1211831
  · exact B1211835
  · exact B1211839
  · exact B1211843
  · exact B1211847
  · exact B1211851
  · exact B1211855
  · exact B1211859
  · exact B1211863
  · exact B1211867
  · exact B1211871
  · exact B1211875
  · exact B1211879
  · exact B1211883
  · exact B1211887
  · exact B1211891
  · exact B1211895
  · exact B1211899
  · exact B1211903
  · exact B1211907
  · exact B1211911
  · exact B1211915
  · exact B1211919
  · exact B1211923
  · exact B1211927
  · exact B1211931
  · exact B1211935
  · exact B1211939
  · exact B1211943
  · exact B1211947
  · exact B1211951
  · exact B1211955
  · exact B1211959
  · exact B1211963
  · exact B1211967
  · exact B1211971
  · exact B1211975
  · exact B1211979
  · exact B1211983
  · exact B1211987
  · exact B1211991
  · exact B1211995
  · exact B1211999
  · exact B1212003
  · exact B1212007
  · exact B1212011
  · exact B1212015
  · exact B1212019
  · exact B1212023
  · exact B1212027
  · exact B1212031
  · exact B1212035
  · exact B1212039
  · exact B1212043
  · exact B1212047
  · exact B1212051
  · exact B1212055
  · exact B1212059
  · exact B1212063
  · exact B1212067
  · exact B1212071
  · exact B1212075
  · exact B1212079
  · exact B1212083
  · exact B1212087
  · exact B1212091
  · exact B1212095
  · exact B1212099
  · exact B1212103
  · exact B1212107
  · exact B1212111
  · exact B1212115
  · exact B1212119
  · exact B1212123
  · exact B1212127
  · exact B1212131
  · exact B1212135
  · exact B1212139
  · exact B1212143
  · exact B1212147
  · exact B1212151
  · exact B1212155
  · exact B1212159
  · exact B1212163
  · exact B1212167
  · exact B1212171
  · exact B1212175
  · exact B1212179
  · exact B1212183
  · exact B1212187
  · exact B1212191
  · exact B1212195
  · exact B1212199
  · exact B1212203
  · exact B1212207
  · exact B1212211
  · exact B1212215
  · exact B1212219
  · exact B1212223
  · exact B1212227
  · exact B1212231
  · exact B1212235
  · exact B1212239
  · exact B1212243
  · exact B1212247
  · exact B1212251
  · exact B1212255
  · exact B1212259
  · exact B1212263
  · exact B1212267
  · exact B1212271
  · exact B1212275
  · exact B1212279
  · exact B1212283
  · exact B1212287
  · exact B1212291
  · exact B1212295
  · exact B1212299
  · exact B1212303
  · exact B1212307
  · exact B1212311
  · exact B1212315
  · exact B1212319
  · exact B1212323
  · exact B1212327
  · exact B1212331
  · exact B1212335
  · exact B1212339
  · exact B1212343
  · exact B1212347
  · exact B1212351
  · exact B1212355
  · exact B1212359
  · exact B1212363
  · exact B1212367
  · exact B1212371
  · exact B1212375
  · exact B1212379
  · exact B1212383
  · exact B1212387
  · exact B1212391
  · exact B1212395
  · exact B1212399
  · exact B1212403
  · exact B1212407
  · exact B1212411
  · exact B1212415
  · exact B1212419
  · exact B1212423
  · exact B1212427
  · exact B1212431
  · exact B1212435
  · exact B1212439
  · exact B1212443
  · exact B1212447
  · exact B1212451
  · exact B1212455
  · exact B1212459
  · exact B1212463
  · exact B1212467
  · exact B1212471
  · exact B1212475
  · exact B1212479
  · exact B1212483
  · exact B1212487
  · exact B1212491
  · exact B1212495
  · exact B1212499
  · exact B1212503
  · exact B1212507
  · exact B1212511
  · exact B1212515
  · exact B1212519
  · exact B1212523
  · exact B1212527
  · exact B1212531
  · exact B1212535
  · exact B1212539
  · exact B1212543
  · exact B1212547
  · exact B1212551
  · exact B1212555
  · exact B1212559
  · exact B1212563
  · exact B1212567
  · exact B1212571
  · exact B1212575
  · exact B1212579
  · exact B1212583
  · exact B1212587
  · exact B1212591
  · exact B1212595
  · exact B1212599
  · exact B1212603
  · exact B1212607
  · exact B1212611
  · exact B1212615
  · exact B1212619
  · exact B1212623
  · exact B1212627
  · exact B1212631
  · exact B1212635
  · exact B1212639
  · exact B1212643
  · exact B1212647
  · exact B1212651
  · exact B1212655
  · exact B1212659
  · exact B1212663
  · exact B1212667
  · exact B1212671
  · exact B1212675
  · exact B1212679
  · exact B1212683
  · exact B1212687
  · exact B1212691
  · exact B1212695
  · exact B1212699
  · exact B1212703
  · exact B1212707
  · exact B1212711
  · exact B1212715
  · exact B1212719
  · exact B1212723
  · exact B1212727
  · exact B1212731
  · exact B1212735
  · exact B1212739
  · exact B1212743
  · exact B1212747
  · exact B1212751
  · exact B1212755
  · exact B1212759
  · exact B1212763
  · exact B1212767
  · exact B1212771
  · exact B1212775
  · exact B1212779
  · exact B1212783
  · exact B1212787
  · exact B1212791
  · exact B1212795
  · exact B1212799
  · exact B1212803
  · exact B1212807
  · exact B1212811
  · exact B1212815
  · exact B1212819
  · exact B1212823
  · exact B1212827
  · exact B1212831
  · exact B1212835
  · exact B1212839
  · exact B1212843
  · exact B1212847
  · exact B1212851
  · exact B1212855
  · exact B1212859
  · exact B1212863
  · exact B1212867
  · exact B1212871
  · exact B1212875
  · exact B1212879
  · exact B1212883
  · exact B1212887
  · exact B1212891
  · exact B1212895
  · exact B1212899
  · exact B1212903
  · exact B1212907
  · exact B1212911
  · exact B1212915
  · exact B1212919
  · exact B1212923
  · exact B1212927
  · exact B1212931
  · exact B1212935
  · exact B1212939
  · exact B1212943
  · exact B1212947
  · exact B1212951
  · exact B1212955
  · exact B1212959
  · exact B1212963
  · exact B1212967
  · exact B1212971
  · exact B1212975
  · exact B1212979
  · exact B1212983
  · exact B1212987
  · exact B1212991
  · exact B1212995
  · exact B1212999
  · exact B1213003
  · exact B1213007
  · exact B1213011
  · exact B1213015
  · exact B1213019
  · exact B1213023
  · exact B1213027
  · exact B1213031
  · exact B1213035
  · exact B1213039
  · exact B1213043
  · exact B1213047
  · exact B1213051
  · exact B1213055
  · exact B1213059
  · exact B1213063
  · exact B1213067
  · exact B1213071
  · exact B1213075
  · exact B1213079
  · exact B1213083
  · exact B1213087
  · exact B1213091
  · exact B1213095
  · exact B1213099
  · exact B1213103
  · exact B1213107
  · exact B1213111
  · exact B1213115
  · exact B1213119
  · exact B1213123
  · exact B1213127
  · exact B1213131
  · exact B1213135
  · exact B1213139
  · exact B1213143
  · exact B1213147
  · exact B1213151
  · exact B1213155
  · exact B1213159
  · exact B1213163
  · exact B1213167
  · exact B1213171
  · exact B1213175
  · exact B1213179
  · exact B1213183
  · exact B1213187
  · exact B1213191
  · exact B1213195
  · exact B1213199
  · exact B1213203
  · exact B1213207
  · exact B1213211
  · exact B1213215
  · exact B1213219
  · exact B1213223
  · exact B1213227
  · exact B1213231
  · exact B1213235
  · exact B1213239
  · exact B1213243
  · exact B1213247
  · exact B1213251
  · exact B1213255
  · exact B1213259
  · exact B1213263
  · exact B1213267
  · exact B1213271
  · exact B1213275
  · exact B1213279
  · exact B1213283
  · exact B1213287
  · exact B1213291
  · exact B1213295
  · exact B1213299
  · exact B1213303
  · exact B1213307
  · exact B1213311
  · exact B1213315
  · exact B1213319
  · exact B1213323
  · exact B1213327
  · exact B1213331
  · exact B1213335
  · exact B1213339
  · exact B1213343
  · exact B1213347
  · exact B1213351
  · exact B1213355
  · exact B1213359
  · exact B1213363
  · exact B1213367
  · exact B1213371
  · exact B1213375
  · exact B1213379
  · exact B1213383
  · exact B1213387
  · exact B1213391
  · exact B1213395
  · exact B1213399
  · exact B1213403
  · exact B1213407
  · exact B1213411
  · exact B1213415
  · exact B1213419
  · exact B1213423

theorem solution (m : ℕ) (hlo : 1211423 ≤ m) (hhi : m ≤ 1213423) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 302855 ≤ j := by omega
    have hj2 : j ≤ 303355 := by omega
    have hb : Blo 1211423 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
