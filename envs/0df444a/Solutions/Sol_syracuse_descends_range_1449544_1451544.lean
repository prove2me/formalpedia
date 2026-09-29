-- Prove2me | solution 1 for syracuse_descends_range_1449544_1451544
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:43:24.047436+00:00
-- url     : https://prove2.me/submissions/b1793d49-98b6-431a-9d6f-593a87914070

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


theorem B5505029 : Blo 1449544 5505029 := bbase (se 4 (by rfl) ⟨516096, by rfl⟩ : syracuseStep 5505029 = 1032193) (by norm_num)
theorem B3096605 : Blo 1449544 3096605 := bbase (se 3 (by rfl) ⟨580613, by rfl⟩ : syracuseStep 3096605 = 1161227) (by norm_num)
theorem B2449453 : Blo 1449544 2449453 := bbase (se 3 (by rfl) ⟨459272, by rfl⟩ : syracuseStep 2449453 = 918545) (by norm_num)
theorem B3670069 : Blo 1449544 3670069 := bbase (se 5 (by rfl) ⟨172034, by rfl⟩ : syracuseStep 3670069 = 344069) (by norm_num)
theorem B1835065 : Blo 1449544 1835065 := bbase (se 2 (by rfl) ⟨688149, by rfl⟩ : syracuseStep 1835065 = 1376299) (by norm_num)
theorem B18595925 : Blo 1449544 18595925 := bbase (se 8 (by rfl) ⟨108960, by rfl⟩ : syracuseStep 18595925 = 217921) (by norm_num)
theorem B1859681 : Blo 1449544 1859681 := bbase (se 2 (by rfl) ⟨697380, by rfl⟩ : syracuseStep 1859681 = 1394761) (by norm_num)
theorem B2752613 : Blo 1449544 2752613 := bbase (se 4 (by rfl) ⟨258057, by rfl⟩ : syracuseStep 2752613 = 516115) (by norm_num)
theorem B2515045 : Blo 1449544 2515045 := bbase (se 4 (by rfl) ⟨235785, by rfl⟩ : syracuseStep 2515045 = 471571) (by norm_num)
theorem B4898933 : Blo 1449544 4898933 := bbase (se 5 (by rfl) ⟨229637, by rfl⟩ : syracuseStep 4898933 = 459275) (by norm_num)
theorem B1654921 : Blo 1449544 1654921 := bbase (se 2 (by rfl) ⟨620595, by rfl⟩ : syracuseStep 1654921 = 1241191) (by norm_num)
theorem B2941085 : Blo 1449544 2941085 := bbase (se 3 (by rfl) ⟨551453, by rfl⟩ : syracuseStep 2941085 = 1102907) (by norm_num)
theorem B3670181 : Blo 1449544 3670181 := bbase (se 4 (by rfl) ⟨344079, by rfl⟩ : syracuseStep 3670181 = 688159) (by norm_num)
theorem B4128965 : Blo 1449544 4128965 := bbase (se 4 (by rfl) ⟨387090, by rfl⟩ : syracuseStep 4128965 = 774181) (by norm_num)
theorem B1835237 : Blo 1449544 1835237 := bbase (se 4 (by rfl) ⟨172053, by rfl⟩ : syracuseStep 1835237 = 344107) (by norm_num)
theorem B1835293 : Blo 1449544 1835293 := bbase (se 3 (by rfl) ⟨344117, by rfl⟩ : syracuseStep 1835293 = 688235) (by norm_num)
theorem B5505317 : Blo 1449544 5505317 := bbase (se 4 (by rfl) ⟨516123, by rfl⟩ : syracuseStep 5505317 = 1032247) (by norm_num)
theorem B1548601 : Blo 1449544 1548601 := bbase (se 2 (by rfl) ⟨580725, by rfl⟩ : syracuseStep 1548601 = 1161451) (by norm_num)
theorem B7946581 : Blo 1449544 7946581 := bbase (se 10 (by rfl) ⟨11640, by rfl⟩ : syracuseStep 7946581 = 23281) (by norm_num)
theorem B3670373 : Blo 1449544 3670373 := bbase (se 4 (by rfl) ⟨344097, by rfl⟩ : syracuseStep 3670373 = 688195) (by norm_num)
theorem B1835389 : Blo 1449544 1835389 := bbase (se 3 (by rfl) ⟨344135, by rfl⟩ : syracuseStep 1835389 = 688271) (by norm_num)
theorem B1548721 : Blo 1449544 1548721 := bbase (se 2 (by rfl) ⟨580770, by rfl⟩ : syracuseStep 1548721 = 1161541) (by norm_num)
theorem B1630741 : Blo 1449544 1630741 := bbase (se 6 (by rfl) ⟨38220, by rfl⟩ : syracuseStep 1630741 = 76441) (by norm_num)
theorem B1835561 : Blo 1449544 1835561 := bbase (se 2 (by rfl) ⟨688335, by rfl⟩ : syracuseStep 1835561 = 1376671) (by norm_num)
theorem B1630777 : Blo 1449544 1630777 := bbase (se 2 (by rfl) ⟨611541, by rfl⟩ : syracuseStep 1630777 = 1223083) (by norm_num)
theorem B1630813 : Blo 1449544 1630813 := bbase (se 3 (by rfl) ⟨305777, by rfl⟩ : syracuseStep 1630813 = 611555) (by norm_num)
theorem B1835617 : Blo 1449544 1835617 := bbase (se 2 (by rfl) ⟨688356, by rfl⟩ : syracuseStep 1835617 = 1376713) (by norm_num)
theorem B1630849 : Blo 1449544 1630849 := bbase (se 2 (by rfl) ⟨611568, by rfl⟩ : syracuseStep 1630849 = 1223137) (by norm_num)
theorem B3097237 : Blo 1449544 3097237 := bbase (se 6 (by rfl) ⟨72591, by rfl⟩ : syracuseStep 3097237 = 145183) (by norm_num)
theorem B1630885 : Blo 1449544 1630885 := bbase (se 4 (by rfl) ⟨152895, by rfl⟩ : syracuseStep 1630885 = 305791) (by norm_num)
theorem B1548973 : Blo 1449544 1548973 := bbase (se 3 (by rfl) ⟨290432, by rfl⟩ : syracuseStep 1548973 = 580865) (by norm_num)
theorem B1548977 : Blo 1449544 1548977 := bbase (se 2 (by rfl) ⟨580866, by rfl⟩ : syracuseStep 1548977 = 1161733) (by norm_num)
theorem B3670717 : Blo 1449544 3670717 := bbase (se 3 (by rfl) ⟨688259, by rfl⟩ : syracuseStep 3670717 = 1376519) (by norm_num)
theorem B1835713 : Blo 1449544 1835713 := bbase (se 2 (by rfl) ⟨688392, by rfl⟩ : syracuseStep 1835713 = 1376785) (by norm_num)
theorem B1630921 : Blo 1449544 1630921 := bbase (se 2 (by rfl) ⟨611595, by rfl⟩ : syracuseStep 1630921 = 1223191) (by norm_num)
theorem B1630957 : Blo 1449544 1630957 := bbase (se 3 (by rfl) ⟨305804, by rfl⟩ : syracuseStep 1630957 = 611609) (by norm_num)
theorem B5300981 : Blo 1449544 5300981 := bbase (se 5 (by rfl) ⟨248483, by rfl⟩ : syracuseStep 5300981 = 496967) (by norm_num)
theorem B1630993 : Blo 1449544 1630993 := bbase (se 2 (by rfl) ⟨611622, by rfl⟩ : syracuseStep 1630993 = 1223245) (by norm_num)
theorem B2065189 : Blo 1449544 2065189 := bbase (se 4 (by rfl) ⟨193611, by rfl⟩ : syracuseStep 2065189 = 387223) (by norm_num)
theorem B3670829 : Blo 1449544 3670829 := bbase (se 3 (by rfl) ⟨688280, by rfl⟩ : syracuseStep 3670829 = 1376561) (by norm_num)
theorem B1631029 : Blo 1449544 1631029 := bbase (se 5 (by rfl) ⟨76454, by rfl⟩ : syracuseStep 1631029 = 152909) (by norm_num)
theorem B2753365 : Blo 1449544 2753365 := bbase (se 9 (by rfl) ⟨8066, by rfl⟩ : syracuseStep 2753365 = 16133) (by norm_num)
theorem B1631065 : Blo 1449544 1631065 := bbase (se 2 (by rfl) ⟨611649, by rfl⟩ : syracuseStep 1631065 = 1223299) (by norm_num)
theorem B1835885 : Blo 1449544 1835885 := bbase (se 3 (by rfl) ⟨344228, by rfl⟩ : syracuseStep 1835885 = 688457) (by norm_num)
theorem B1631101 : Blo 1449544 1631101 := bbase (se 3 (by rfl) ⟨305831, by rfl⟩ : syracuseStep 1631101 = 611663) (by norm_num)
theorem B1631137 : Blo 1449544 1631137 := bbase (se 2 (by rfl) ⟨611676, by rfl⟩ : syracuseStep 1631137 = 1223353) (by norm_num)
theorem B1835941 : Blo 1449544 1835941 := bbase (se 4 (by rfl) ⟨172119, by rfl⟩ : syracuseStep 1835941 = 344239) (by norm_num)
theorem B4129717 : Blo 1449544 4129717 := bbase (se 5 (by rfl) ⟨193580, by rfl⟩ : syracuseStep 4129717 = 387161) (by norm_num)
theorem B1631173 : Blo 1449544 1631173 := bbase (se 4 (by rfl) ⟨152922, by rfl⟩ : syracuseStep 1631173 = 305845) (by norm_num)
theorem B7341029 : Blo 1449544 7341029 := bbase (se 4 (by rfl) ⟨688221, by rfl⟩ : syracuseStep 7341029 = 1376443) (by norm_num)
theorem B2753509 : Blo 1449544 2753509 := bbase (se 4 (by rfl) ⟨258141, by rfl⟩ : syracuseStep 2753509 = 516283) (by norm_num)
theorem B1631209 : Blo 1449544 1631209 := bbase (se 2 (by rfl) ⟨611703, by rfl⟩ : syracuseStep 1631209 = 1223407) (by norm_num)
theorem B3671021 : Blo 1449544 3671021 := bbase (se 3 (by rfl) ⟨688316, by rfl⟩ : syracuseStep 3671021 = 1376633) (by norm_num)
theorem B1836037 : Blo 1449544 1836037 := bbase (se 4 (by rfl) ⟨172128, by rfl⟩ : syracuseStep 1836037 = 344257) (by norm_num)
theorem B1631245 : Blo 1449544 1631245 := bbase (se 3 (by rfl) ⟨305858, by rfl⟩ : syracuseStep 1631245 = 611717) (by norm_num)
theorem B1631281 : Blo 1449544 1631281 := bbase (se 2 (by rfl) ⟨611730, by rfl⟩ : syracuseStep 1631281 = 1223461) (by norm_num)
theorem B3261509 : Blo 1449544 3261509 := bbase (se 4 (by rfl) ⟨305766, by rfl⟩ : syracuseStep 3261509 = 611533) (by norm_num)
theorem B2204749 : Blo 1449544 2204749 := bbase (se 3 (by rfl) ⟨413390, by rfl⟩ : syracuseStep 2204749 = 826781) (by norm_num)
theorem B1631317 : Blo 1449544 1631317 := bbase (se 8 (by rfl) ⟨9558, by rfl⟩ : syracuseStep 1631317 = 19117) (by norm_num)
theorem B1631353 : Blo 1449544 1631353 := bbase (se 2 (by rfl) ⟨611757, by rfl⟩ : syracuseStep 1631353 = 1223515) (by norm_num)
theorem B2753669 : Blo 1449544 2753669 := bbase (se 4 (by rfl) ⟨258156, by rfl⟩ : syracuseStep 2753669 = 516313) (by norm_num)
theorem B3261581 : Blo 1449544 3261581 := bbase (se 3 (by rfl) ⟨611546, by rfl⟩ : syracuseStep 3261581 = 1223093) (by norm_num)
theorem B2204821 : Blo 1449544 2204821 := bbase (se 6 (by rfl) ⟨51675, by rfl⟩ : syracuseStep 2204821 = 103351) (by norm_num)
theorem B1631389 : Blo 1449544 1631389 := bbase (se 3 (by rfl) ⟨305885, by rfl⟩ : syracuseStep 1631389 = 611771) (by norm_num)
theorem B1836209 : Blo 1449544 1836209 := bbase (se 2 (by rfl) ⟨688578, by rfl⟩ : syracuseStep 1836209 = 1377157) (by norm_num)
theorem B1631425 : Blo 1449544 1631425 := bbase (se 2 (by rfl) ⟨611784, by rfl⟩ : syracuseStep 1631425 = 1223569) (by norm_num)
theorem B3261653 : Blo 1449544 3261653 := bbase (se 7 (by rfl) ⟨38222, by rfl⟩ : syracuseStep 3261653 = 76445) (by norm_num)
theorem B1631461 : Blo 1449544 1631461 := bbase (se 4 (by rfl) ⟨152949, by rfl⟩ : syracuseStep 1631461 = 305899) (by norm_num)
theorem B1836265 : Blo 1449544 1836265 := bbase (se 2 (by rfl) ⟨688599, by rfl⟩ : syracuseStep 1836265 = 1377199) (by norm_num)
theorem B1549541 : Blo 1449544 1549541 := bbase (se 4 (by rfl) ⟨145269, by rfl⟩ : syracuseStep 1549541 = 290539) (by norm_num)
theorem B1631497 : Blo 1449544 1631497 := bbase (se 2 (by rfl) ⟨611811, by rfl⟩ : syracuseStep 1631497 = 1223623) (by norm_num)
theorem B2753813 : Blo 1449544 2753813 := bbase (se 6 (by rfl) ⟨64542, by rfl⟩ : syracuseStep 2753813 = 129085) (by norm_num)
theorem B3261725 : Blo 1449544 3261725 := bbase (se 3 (by rfl) ⟨611573, by rfl⟩ : syracuseStep 3261725 = 1223147) (by norm_num)
theorem B1631533 : Blo 1449544 1631533 := bbase (se 3 (by rfl) ⟨305912, by rfl⟩ : syracuseStep 1631533 = 611825) (by norm_num)
theorem B10462517 : Blo 1449544 10462517 := bbase (se 5 (by rfl) ⟨490430, by rfl⟩ : syracuseStep 10462517 = 980861) (by norm_num)
theorem B3671365 : Blo 1449544 3671365 := bbase (se 4 (by rfl) ⟨344190, by rfl⟩ : syracuseStep 3671365 = 688381) (by norm_num)
theorem B1836361 : Blo 1449544 1836361 := bbase (se 2 (by rfl) ⟨688635, by rfl⟩ : syracuseStep 1836361 = 1377271) (by norm_num)
theorem B1631569 : Blo 1449544 1631569 := bbase (se 2 (by rfl) ⟨611838, by rfl⟩ : syracuseStep 1631569 = 1223677) (by norm_num)
theorem B50275669 : Blo 1449544 50275669 := bbase (se 12 (by rfl) ⟨18411, by rfl⟩ : syracuseStep 50275669 = 36823) (by norm_num)
theorem B3261797 : Blo 1449544 3261797 := bbase (se 4 (by rfl) ⟨305793, by rfl⟩ : syracuseStep 3261797 = 611587) (by norm_num)
theorem B1631605 : Blo 1449544 1631605 := bbase (se 5 (by rfl) ⟨76481, by rfl⟩ : syracuseStep 1631605 = 152963) (by norm_num)
theorem B2065781 : Blo 1449544 2065781 := bbase (se 5 (by rfl) ⟨96833, by rfl⟩ : syracuseStep 2065781 = 193667) (by norm_num)
theorem B1631641 : Blo 1449544 1631641 := bbase (se 2 (by rfl) ⟨611865, by rfl⟩ : syracuseStep 1631641 = 1223731) (by norm_num)
theorem B3483037 : Blo 1449544 3483037 := bbase (se 3 (by rfl) ⟨653069, by rfl⟩ : syracuseStep 3483037 = 1306139) (by norm_num)
theorem B1549729 : Blo 1449544 1549729 := bbase (se 2 (by rfl) ⟨581148, by rfl⟩ : syracuseStep 1549729 = 1162297) (by norm_num)
theorem B3261869 : Blo 1449544 3261869 := bbase (se 3 (by rfl) ⟨611600, by rfl⟩ : syracuseStep 3261869 = 1223201) (by norm_num)
theorem B3671477 : Blo 1449544 3671477 := bbase (se 5 (by rfl) ⟨172100, by rfl⟩ : syracuseStep 3671477 = 344201) (by norm_num)
theorem B1631677 : Blo 1449544 1631677 := bbase (se 3 (by rfl) ⟨305939, by rfl⟩ : syracuseStep 1631677 = 611879) (by norm_num)
theorem B5506501 : Blo 1449544 5506501 := bbase (se 4 (by rfl) ⟨516234, by rfl⟩ : syracuseStep 5506501 = 1032469) (by norm_num)
theorem B2065861 : Blo 1449544 2065861 := bbase (se 4 (by rfl) ⟨193674, by rfl⟩ : syracuseStep 2065861 = 387349) (by norm_num)
theorem B5883349 : Blo 1449544 5883349 := bbase (se 7 (by rfl) ⟨68945, by rfl⟩ : syracuseStep 5883349 = 137891) (by norm_num)
theorem B1631713 : Blo 1449544 1631713 := bbase (se 2 (by rfl) ⟨611892, by rfl⟩ : syracuseStep 1631713 = 1223785) (by norm_num)
theorem B4408805 : Blo 1449544 4408805 := bbase (se 4 (by rfl) ⟨413325, by rfl⟩ : syracuseStep 4408805 = 826651) (by norm_num)
theorem B3261941 : Blo 1449544 3261941 := bbase (se 5 (by rfl) ⟨152903, by rfl⟩ : syracuseStep 3261941 = 305807) (by norm_num)
theorem B1836533 : Blo 1449544 1836533 := bbase (se 5 (by rfl) ⟨86087, by rfl⟩ : syracuseStep 1836533 = 172175) (by norm_num)
theorem B2942453 : Blo 1449544 2942453 := bbase (se 5 (by rfl) ⟨137927, by rfl⟩ : syracuseStep 2942453 = 275855) (by norm_num)
theorem B1631749 : Blo 1449544 1631749 := bbase (se 4 (by rfl) ⟨152976, by rfl⟩ : syracuseStep 1631749 = 305953) (by norm_num)
theorem B2041357 : Blo 1449544 2041357 := bbase (se 3 (by rfl) ⟨382754, by rfl⟩ : syracuseStep 2041357 = 765509) (by norm_num)
theorem B3098125 : Blo 1449544 3098125 := bbase (se 3 (by rfl) ⟨580898, by rfl⟩ : syracuseStep 3098125 = 1161797) (by norm_num)
theorem B1631785 : Blo 1449544 1631785 := bbase (se 2 (by rfl) ⟨611919, by rfl⟩ : syracuseStep 1631785 = 1223839) (by norm_num)
theorem B1836589 : Blo 1449544 1836589 := bbase (se 3 (by rfl) ⟨344360, by rfl⟩ : syracuseStep 1836589 = 688721) (by norm_num)
theorem B2754101 : Blo 1449544 2754101 := bbase (se 5 (by rfl) ⟨129098, by rfl⟩ : syracuseStep 2754101 = 258197) (by norm_num)
theorem B3262013 : Blo 1449544 3262013 := bbase (se 3 (by rfl) ⟨611627, by rfl⟩ : syracuseStep 3262013 = 1223255) (by norm_num)
theorem B2065981 : Blo 1449544 2065981 := bbase (se 3 (by rfl) ⟨387371, by rfl⟩ : syracuseStep 2065981 = 774743) (by norm_num)
theorem B1631821 : Blo 1449544 1631821 := bbase (se 3 (by rfl) ⟨305966, by rfl⟩ : syracuseStep 1631821 = 611933) (by norm_num)
theorem B1631857 : Blo 1449544 1631857 := bbase (se 2 (by rfl) ⟨611946, by rfl⟩ : syracuseStep 1631857 = 1223893) (by norm_num)
theorem B3671669 : Blo 1449544 3671669 := bbase (se 5 (by rfl) ⟨172109, by rfl⟩ : syracuseStep 3671669 = 344219) (by norm_num)
theorem B3483269 : Blo 1449544 3483269 := bbase (se 4 (by rfl) ⟨326556, by rfl⟩ : syracuseStep 3483269 = 653113) (by norm_num)
theorem B3262085 : Blo 1449544 3262085 := bbase (se 4 (by rfl) ⟨305820, by rfl⟩ : syracuseStep 3262085 = 611641) (by norm_num)
theorem B3098245 : Blo 1449544 3098245 := bbase (se 4 (by rfl) ⟨290460, by rfl⟩ : syracuseStep 3098245 = 580921) (by norm_num)
theorem B1836685 : Blo 1449544 1836685 := bbase (se 3 (by rfl) ⟨344378, by rfl⟩ : syracuseStep 1836685 = 688757) (by norm_num)
theorem B1631893 : Blo 1449544 1631893 := bbase (se 6 (by rfl) ⟨38247, by rfl⟩ : syracuseStep 1631893 = 76495) (by norm_num)
theorem B2066077 : Blo 1449544 2066077 := bbase (se 3 (by rfl) ⟨387389, by rfl⟩ : syracuseStep 2066077 = 774779) (by norm_num)
theorem B1631929 : Blo 1449544 1631929 := bbase (se 2 (by rfl) ⟨611973, by rfl⟩ : syracuseStep 1631929 = 1223947) (by norm_num)
theorem B3262157 : Blo 1449544 3262157 := bbase (se 3 (by rfl) ⟨611654, by rfl⟩ : syracuseStep 3262157 = 1223309) (by norm_num)
theorem B2754253 : Blo 1449544 2754253 := bbase (se 3 (by rfl) ⟨516422, by rfl⟩ : syracuseStep 2754253 = 1032845) (by norm_num)
theorem B1631965 : Blo 1449544 1631965 := bbase (se 3 (by rfl) ⟨305993, by rfl⟩ : syracuseStep 1631965 = 611987) (by norm_num)
theorem B5506805 : Blo 1449544 5506805 := bbase (se 5 (by rfl) ⟨258131, by rfl⟩ : syracuseStep 5506805 = 516263) (by norm_num)
theorem B1632001 : Blo 1449544 1632001 := bbase (se 2 (by rfl) ⟨612000, by rfl⟩ : syracuseStep 1632001 = 1224001) (by norm_num)
theorem B4187909 : Blo 1449544 4187909 := bbase (se 4 (by rfl) ⟨392616, by rfl⟩ : syracuseStep 4187909 = 785233) (by norm_num)
theorem B3262229 : Blo 1449544 3262229 := bbase (se 6 (by rfl) ⟨76458, by rfl⟩ : syracuseStep 3262229 = 152917) (by norm_num)
theorem B4892453 : Blo 1449544 4892453 := bbase (se 4 (by rfl) ⟨458667, by rfl⟩ : syracuseStep 4892453 = 917335) (by norm_num)
theorem B1632037 : Blo 1449544 1632037 := bbase (se 4 (by rfl) ⟨153003, by rfl⟩ : syracuseStep 1632037 = 306007) (by norm_num)
theorem B1836857 : Blo 1449544 1836857 := bbase (se 2 (by rfl) ⟨688821, by rfl⟩ : syracuseStep 1836857 = 1377643) (by norm_num)
theorem B1632073 : Blo 1449544 1632073 := bbase (se 2 (by rfl) ⟨612027, by rfl⟩ : syracuseStep 1632073 = 1224055) (by norm_num)
theorem B3262301 : Blo 1449544 3262301 := bbase (se 3 (by rfl) ⟨611681, by rfl⟩ : syracuseStep 3262301 = 1223363) (by norm_num)
theorem B1632109 : Blo 1449544 1632109 := bbase (se 3 (by rfl) ⟨306020, by rfl⟩ : syracuseStep 1632109 = 612041) (by norm_num)
theorem B1836913 : Blo 1449544 1836913 := bbase (se 2 (by rfl) ⟨688842, by rfl⟩ : syracuseStep 1836913 = 1377685) (by norm_num)
theorem B10594165 : Blo 1449544 10594165 := bbase (se 5 (by rfl) ⟨496601, by rfl⟩ : syracuseStep 10594165 = 993203) (by norm_num)
theorem B3098501 : Blo 1449544 3098501 := bbase (se 4 (by rfl) ⟨290484, by rfl⟩ : syracuseStep 3098501 = 580969) (by norm_num)
theorem B1632145 : Blo 1449544 1632145 := bbase (se 2 (by rfl) ⟨612054, by rfl⟩ : syracuseStep 1632145 = 1224109) (by norm_num)
theorem B3262373 : Blo 1449544 3262373 := bbase (se 4 (by rfl) ⟨305847, by rfl⟩ : syracuseStep 3262373 = 611695) (by norm_num)
theorem B1632181 : Blo 1449544 1632181 := bbase (se 5 (by rfl) ⟨76508, by rfl⟩ : syracuseStep 1632181 = 153017) (by norm_num)
theorem B3672013 : Blo 1449544 3672013 := bbase (se 3 (by rfl) ⟨688502, by rfl⟩ : syracuseStep 3672013 = 1377005) (by norm_num)
theorem B1837009 : Blo 1449544 1837009 := bbase (se 2 (by rfl) ⟨688878, by rfl⟩ : syracuseStep 1837009 = 1377757) (by norm_num)
theorem B1632217 : Blo 1449544 1632217 := bbase (se 2 (by rfl) ⟨612081, by rfl⟩ : syracuseStep 1632217 = 1224163) (by norm_num)
theorem B3262445 : Blo 1449544 3262445 := bbase (se 3 (by rfl) ⟨611708, by rfl⟩ : syracuseStep 3262445 = 1223417) (by norm_num)
theorem B1632253 : Blo 1449544 1632253 := bbase (se 3 (by rfl) ⟨306047, by rfl⟩ : syracuseStep 1632253 = 612095) (by norm_num)
theorem B2754557 : Blo 1449544 2754557 := bbase (se 3 (by rfl) ⟨516479, by rfl⟩ : syracuseStep 2754557 = 1032959) (by norm_num)
theorem B3483661 : Blo 1449544 3483661 := bbase (se 3 (by rfl) ⟨653186, by rfl⟩ : syracuseStep 3483661 = 1306373) (by norm_num)
theorem B1632289 : Blo 1449544 1632289 := bbase (se 2 (by rfl) ⟨612108, by rfl⟩ : syracuseStep 1632289 = 1224217) (by norm_num)
theorem B2615341 : Blo 1449544 2615341 := bbase (se 3 (by rfl) ⟨490376, by rfl⟩ : syracuseStep 2615341 = 980753) (by norm_num)
theorem B3262517 : Blo 1449544 3262517 := bbase (se 5 (by rfl) ⟨152930, by rfl⟩ : syracuseStep 3262517 = 305861) (by norm_num)
theorem B3672125 : Blo 1449544 3672125 := bbase (se 3 (by rfl) ⟨688523, by rfl⟩ : syracuseStep 3672125 = 1377047) (by norm_num)
theorem B1632325 : Blo 1449544 1632325 := bbase (se 4 (by rfl) ⟨153030, by rfl⟩ : syracuseStep 1632325 = 306061) (by norm_num)
theorem B3139661 : Blo 1449544 3139661 := bbase (se 3 (by rfl) ⟨588686, by rfl⟩ : syracuseStep 3139661 = 1177373) (by norm_num)
theorem B1632361 : Blo 1449544 1632361 := bbase (se 2 (by rfl) ⟨612135, by rfl⟩ : syracuseStep 1632361 = 1224271) (by norm_num)
theorem B2615413 : Blo 1449544 2615413 := bbase (se 5 (by rfl) ⟨122597, by rfl⟩ : syracuseStep 2615413 = 245195) (by norm_num)
theorem B3262589 : Blo 1449544 3262589 := bbase (se 3 (by rfl) ⟨611735, by rfl⟩ : syracuseStep 3262589 = 1223471) (by norm_num)
theorem B1632397 : Blo 1449544 1632397 := bbase (se 3 (by rfl) ⟨306074, by rfl⟩ : syracuseStep 1632397 = 612149) (by norm_num)
theorem B2066573 : Blo 1449544 2066573 := bbase (se 3 (by rfl) ⟨387482, by rfl⟩ : syracuseStep 2066573 = 774965) (by norm_num)
theorem B1632433 : Blo 1449544 1632433 := bbase (se 2 (by rfl) ⟨612162, by rfl⟩ : syracuseStep 1632433 = 1224325) (by norm_num)
theorem B3582133 : Blo 1449544 3582133 := bbase (se 5 (by rfl) ⟨167912, by rfl⟩ : syracuseStep 3582133 = 335825) (by norm_num)
theorem B3262661 : Blo 1449544 3262661 := bbase (se 4 (by rfl) ⟨305874, by rfl⟩ : syracuseStep 3262661 = 611749) (by norm_num)
theorem B1960133 : Blo 1449544 1960133 := bbase (se 4 (by rfl) ⟨183762, by rfl⟩ : syracuseStep 1960133 = 367525) (by norm_num)
theorem B4892885 : Blo 1449544 4892885 := bbase (se 7 (by rfl) ⟨57338, by rfl⟩ : syracuseStep 4892885 = 114677) (by norm_num)
theorem B4647125 : Blo 1449544 4647125 := bbase (se 7 (by rfl) ⟨54458, by rfl⟩ : syracuseStep 4647125 = 108917) (by norm_num)
theorem B1632469 : Blo 1449544 1632469 := bbase (se 7 (by rfl) ⟨19130, by rfl⟩ : syracuseStep 1632469 = 38261) (by norm_num)
theorem B7342325 : Blo 1449544 7342325 := bbase (se 5 (by rfl) ⟨344171, by rfl⟩ : syracuseStep 7342325 = 688343) (by norm_num)
theorem B1632505 : Blo 1449544 1632505 := bbase (se 2 (by rfl) ⟨612189, by rfl⟩ : syracuseStep 1632505 = 1224379) (by norm_num)
theorem B3672317 : Blo 1449544 3672317 := bbase (se 3 (by rfl) ⟨688559, by rfl⟩ : syracuseStep 3672317 = 1377119) (by norm_num)
theorem B3262733 : Blo 1449544 3262733 := bbase (se 3 (by rfl) ⟨611762, by rfl⟩ : syracuseStep 3262733 = 1223525) (by norm_num)
theorem B1632541 : Blo 1449544 1632541 := bbase (se 3 (by rfl) ⟨306101, by rfl⟩ : syracuseStep 1632541 = 612203) (by norm_num)
theorem B5228837 : Blo 1449544 5228837 := bbase (se 4 (by rfl) ⟨490203, by rfl⟩ : syracuseStep 5228837 = 980407) (by norm_num)
theorem B1632577 : Blo 1449544 1632577 := bbase (se 2 (by rfl) ⟨612216, by rfl⟩ : syracuseStep 1632577 = 1224433) (by norm_num)
theorem B3262805 : Blo 1449544 3262805 := bbase (se 10 (by rfl) ⟨4779, by rfl⟩ : syracuseStep 3262805 = 9559) (by norm_num)
theorem B2615645 : Blo 1449544 2615645 := bbase (se 3 (by rfl) ⟨490433, by rfl⟩ : syracuseStep 2615645 = 980867) (by norm_num)
theorem B1632613 : Blo 1449544 1632613 := bbase (se 4 (by rfl) ⟨153057, by rfl⟩ : syracuseStep 1632613 = 306115) (by norm_num)
theorem B1632649 : Blo 1449544 1632649 := bbase (se 2 (by rfl) ⟨612243, by rfl⟩ : syracuseStep 1632649 = 1224487) (by norm_num)
theorem B3721621 : Blo 1449544 3721621 := bbase (se 6 (by rfl) ⟨87225, by rfl⟩ : syracuseStep 3721621 = 174451) (by norm_num)
theorem B3262877 : Blo 1449544 3262877 := bbase (se 3 (by rfl) ⟨611789, by rfl⟩ : syracuseStep 3262877 = 1223579) (by norm_num)
theorem B1632685 : Blo 1449544 1632685 := bbase (se 3 (by rfl) ⟨306128, by rfl⟩ : syracuseStep 1632685 = 612257) (by norm_num)
theorem B3721661 : Blo 1449544 3721661 := bbase (se 3 (by rfl) ⟨697811, by rfl⟩ : syracuseStep 3721661 = 1395623) (by norm_num)
theorem B1632721 : Blo 1449544 1632721 := bbase (se 2 (by rfl) ⟨612270, by rfl⟩ : syracuseStep 1632721 = 1224541) (by norm_num)
theorem B3262949 : Blo 1449544 3262949 := bbase (se 4 (by rfl) ⟨305901, by rfl⟩ : syracuseStep 3262949 = 611803) (by norm_num)
theorem B9415157 : Blo 1449544 9415157 := bbase (se 5 (by rfl) ⟨441335, by rfl⟩ : syracuseStep 9415157 = 882671) (by norm_num)
theorem B1632757 : Blo 1449544 1632757 := bbase (se 5 (by rfl) ⟨76535, by rfl⟩ : syracuseStep 1632757 = 153071) (by norm_num)
theorem B1632793 : Blo 1449544 1632793 := bbase (se 2 (by rfl) ⟨612297, by rfl⟩ : syracuseStep 1632793 = 1224595) (by norm_num)
theorem B2648621 : Blo 1449544 2648621 := bbase (se 3 (by rfl) ⟨496616, by rfl⟩ : syracuseStep 2648621 = 993233) (by norm_num)
theorem B3263021 : Blo 1449544 3263021 := bbase (se 3 (by rfl) ⟨611816, by rfl⟩ : syracuseStep 3263021 = 1223633) (by norm_num)
theorem B1632829 : Blo 1449544 1632829 := bbase (se 3 (by rfl) ⟨306155, by rfl⟩ : syracuseStep 1632829 = 612311) (by norm_num)
theorem B3672661 : Blo 1449544 3672661 := bbase (se 8 (by rfl) ⟨21519, by rfl⟩ : syracuseStep 3672661 = 43039) (by norm_num)
theorem B1632865 : Blo 1449544 1632865 := bbase (se 2 (by rfl) ⟨612324, by rfl⟩ : syracuseStep 1632865 = 1224649) (by norm_num)
theorem B3263093 : Blo 1449544 3263093 := bbase (se 5 (by rfl) ⟨152957, by rfl⟩ : syracuseStep 3263093 = 305915) (by norm_num)
theorem B4893317 : Blo 1449544 4893317 := bbase (se 4 (by rfl) ⟨458748, by rfl⟩ : syracuseStep 4893317 = 917497) (by norm_num)
theorem B1632901 : Blo 1449544 1632901 := bbase (se 4 (by rfl) ⟨153084, by rfl⟩ : syracuseStep 1632901 = 306169) (by norm_num)
theorem B2206349 : Blo 1449544 2206349 := bbase (se 3 (by rfl) ⟨413690, by rfl⟩ : syracuseStep 2206349 = 827381) (by norm_num)
theorem B1632937 : Blo 1449544 1632937 := bbase (se 2 (by rfl) ⟨612351, by rfl⟩ : syracuseStep 1632937 = 1224703) (by norm_num)
theorem B3263165 : Blo 1449544 3263165 := bbase (se 3 (by rfl) ⟨611843, by rfl⟩ : syracuseStep 3263165 = 1223687) (by norm_num)
theorem B3672773 : Blo 1449544 3672773 := bbase (se 4 (by rfl) ⟨344322, by rfl⟩ : syracuseStep 3672773 = 688645) (by norm_num)
theorem B1632973 : Blo 1449544 1632973 := bbase (se 3 (by rfl) ⟨306182, by rfl⟩ : syracuseStep 1632973 = 612365) (by norm_num)
theorem B2755309 : Blo 1449544 2755309 := bbase (se 3 (by rfl) ⟨516620, by rfl⟩ : syracuseStep 2755309 = 1033241) (by norm_num)
theorem B3099389 : Blo 1449544 3099389 := bbase (se 3 (by rfl) ⟨581135, by rfl⟩ : syracuseStep 3099389 = 1162271) (by norm_num)
theorem B3263237 : Blo 1449544 3263237 := bbase (se 4 (by rfl) ⟨305928, by rfl⟩ : syracuseStep 3263237 = 611857) (by norm_num)
theorem B3263309 : Blo 1449544 3263309 := bbase (se 3 (by rfl) ⟨611870, by rfl⟩ : syracuseStep 3263309 = 1223741) (by norm_num)
theorem B2755453 : Blo 1449544 2755453 := bbase (se 3 (by rfl) ⟨516647, by rfl⟩ : syracuseStep 2755453 = 1033295) (by norm_num)
theorem B3672965 : Blo 1449544 3672965 := bbase (se 4 (by rfl) ⟨344340, by rfl⟩ : syracuseStep 3672965 = 688681) (by norm_num)
theorem B2206597 : Blo 1449544 2206597 := bbase (se 4 (by rfl) ⟨206868, by rfl⟩ : syracuseStep 2206597 = 413737) (by norm_num)
theorem B3263381 : Blo 1449544 3263381 := bbase (se 6 (by rfl) ⟨76485, by rfl⟩ : syracuseStep 3263381 = 152971) (by norm_num)
theorem B3263453 : Blo 1449544 3263453 := bbase (se 3 (by rfl) ⟨611897, by rfl⟩ : syracuseStep 3263453 = 1223795) (by norm_num)
theorem B6966245 : Blo 1449544 6966245 := bbase (se 4 (by rfl) ⟨653085, by rfl⟩ : syracuseStep 6966245 = 1306171) (by norm_num)
theorem B3099629 : Blo 1449544 3099629 := bbase (se 3 (by rfl) ⟨581180, by rfl⟩ : syracuseStep 3099629 = 1162361) (by norm_num)
theorem B14887957 : Blo 1449544 14887957 := bbase (se 6 (by rfl) ⟨348936, by rfl⟩ : syracuseStep 14887957 = 697873) (by norm_num)
theorem B2755613 : Blo 1449544 2755613 := bbase (se 3 (by rfl) ⟨516677, by rfl⟩ : syracuseStep 2755613 = 1033355) (by norm_num)
theorem B3263525 : Blo 1449544 3263525 := bbase (se 4 (by rfl) ⟨305955, by rfl⟩ : syracuseStep 3263525 = 611911) (by norm_num)
theorem B4893749 : Blo 1449544 4893749 := bbase (se 5 (by rfl) ⟨229394, by rfl⟩ : syracuseStep 4893749 = 458789) (by norm_num)
theorem B3484757 : Blo 1449544 3484757 := bbase (se 8 (by rfl) ⟨20418, by rfl⟩ : syracuseStep 3484757 = 40837) (by norm_num)
theorem B6974549 : Blo 1449544 6974549 := bbase (se 8 (by rfl) ⟨40866, by rfl⟩ : syracuseStep 6974549 = 81733) (by norm_num)
theorem B3263597 : Blo 1449544 3263597 := bbase (se 3 (by rfl) ⟨611924, by rfl⟩ : syracuseStep 3263597 = 1223849) (by norm_num)
theorem B3263669 : Blo 1449544 3263669 := bbase (se 5 (by rfl) ⟨152984, by rfl⟩ : syracuseStep 3263669 = 305969) (by norm_num)
theorem B3673309 : Blo 1449544 3673309 := bbase (se 3 (by rfl) ⟨688745, by rfl⟩ : syracuseStep 3673309 = 1377491) (by norm_num)
theorem B7843061 : Blo 1449544 7843061 := bbase (se 5 (by rfl) ⟨367643, by rfl⟩ : syracuseStep 7843061 = 735287) (by norm_num)
theorem B3263741 : Blo 1449544 3263741 := bbase (se 3 (by rfl) ⟨611951, by rfl⟩ : syracuseStep 3263741 = 1223903) (by norm_num)
theorem B3263813 : Blo 1449544 3263813 := bbase (se 4 (by rfl) ⟨305982, by rfl⟩ : syracuseStep 3263813 = 611965) (by norm_num)
theorem B3673421 : Blo 1449544 3673421 := bbase (se 3 (by rfl) ⟨688766, by rfl⟩ : syracuseStep 3673421 = 1377533) (by norm_num)
theorem B3919205 : Blo 1449544 3919205 := bbase (se 4 (by rfl) ⟨367425, by rfl⟩ : syracuseStep 3919205 = 734851) (by norm_num)
theorem B3485045 : Blo 1449544 3485045 := bbase (se 5 (by rfl) ⟨163361, by rfl⟩ : syracuseStep 3485045 = 326723) (by norm_num)
theorem B2174333 : Blo 1449544 2174333 := bbase (se 3 (by rfl) ⟨407687, by rfl⟩ : syracuseStep 2174333 = 815375) (by norm_num)
theorem B3263885 : Blo 1449544 3263885 := bbase (se 3 (by rfl) ⟨611978, by rfl⟩ : syracuseStep 3263885 = 1223957) (by norm_num)
theorem B2174357 : Blo 1449544 2174357 := bbase (se 6 (by rfl) ⟨50961, by rfl⟩ : syracuseStep 2174357 = 101923) (by norm_num)
theorem B5229989 : Blo 1449544 5229989 := bbase (se 4 (by rfl) ⟨490311, by rfl⟩ : syracuseStep 5229989 = 980623) (by norm_num)
theorem B2174381 : Blo 1449544 2174381 := bbase (se 3 (by rfl) ⟨407696, by rfl⟩ : syracuseStep 2174381 = 815393) (by norm_num)
theorem B1469873 : Blo 1449544 1469873 := bbase (se 2 (by rfl) ⟨551202, by rfl⟩ : syracuseStep 1469873 = 1102405) (by norm_num)
theorem B6196661 : Blo 1449544 6196661 := bbase (se 5 (by rfl) ⟨290468, by rfl⟩ : syracuseStep 6196661 = 580937) (by norm_num)
theorem B2174405 : Blo 1449544 2174405 := bbase (se 4 (by rfl) ⟨203850, by rfl⟩ : syracuseStep 2174405 = 407701) (by norm_num)
theorem B3263957 : Blo 1449544 3263957 := bbase (se 7 (by rfl) ⟨38249, by rfl⟩ : syracuseStep 3263957 = 76499) (by norm_num)
theorem B2174429 : Blo 1449544 2174429 := bbase (se 3 (by rfl) ⟨407705, by rfl⟩ : syracuseStep 2174429 = 815411) (by norm_num)
theorem B4894181 : Blo 1449544 4894181 := bbase (se 4 (by rfl) ⟨458829, by rfl⟩ : syracuseStep 4894181 = 917659) (by norm_num)
theorem B2174453 : Blo 1449544 2174453 := bbase (se 5 (by rfl) ⟨101927, by rfl⟩ : syracuseStep 2174453 = 203855) (by norm_num)
theorem B7343621 : Blo 1449544 7343621 := bbase (se 4 (by rfl) ⟨688464, by rfl⟩ : syracuseStep 7343621 = 1376929) (by norm_num)
theorem B2174477 : Blo 1449544 2174477 := bbase (se 3 (by rfl) ⟨407714, by rfl⟩ : syracuseStep 2174477 = 815429) (by norm_num)
theorem B3673613 : Blo 1449544 3673613 := bbase (se 3 (by rfl) ⟨688802, by rfl⟩ : syracuseStep 3673613 = 1377605) (by norm_num)
theorem B2321941 : Blo 1449544 2321941 := bbase (se 6 (by rfl) ⟨54420, by rfl⟩ : syracuseStep 2321941 = 108841) (by norm_num)
theorem B3264029 : Blo 1449544 3264029 := bbase (se 3 (by rfl) ⟨612005, by rfl⟩ : syracuseStep 3264029 = 1224011) (by norm_num)
theorem B2174501 : Blo 1449544 2174501 := bbase (se 4 (by rfl) ⟨203859, by rfl⟩ : syracuseStep 2174501 = 407719) (by norm_num)
theorem B2174525 : Blo 1449544 2174525 := bbase (se 3 (by rfl) ⟨407723, by rfl⟩ : syracuseStep 2174525 = 815447) (by norm_num)
theorem B2174549 : Blo 1449544 2174549 := bbase (se 8 (by rfl) ⟨12741, by rfl⟩ : syracuseStep 2174549 = 25483) (by norm_num)
theorem B3264101 : Blo 1449544 3264101 := bbase (se 4 (by rfl) ⟨306009, by rfl⟩ : syracuseStep 3264101 = 612019) (by norm_num)
theorem B2174573 : Blo 1449544 2174573 := bbase (se 3 (by rfl) ⟨407732, by rfl⟩ : syracuseStep 2174573 = 815465) (by norm_num)
theorem B2174597 : Blo 1449544 2174597 := bbase (se 4 (by rfl) ⟨203868, by rfl⟩ : syracuseStep 2174597 = 407737) (by norm_num)
theorem B2174621 : Blo 1449544 2174621 := bbase (se 3 (by rfl) ⟨407741, by rfl⟩ : syracuseStep 2174621 = 815483) (by norm_num)
theorem B3264173 : Blo 1449544 3264173 := bbase (se 3 (by rfl) ⟨612032, by rfl⟩ : syracuseStep 3264173 = 1224065) (by norm_num)
theorem B2174645 : Blo 1449544 2174645 := bbase (se 5 (by rfl) ⟨101936, by rfl⟩ : syracuseStep 2174645 = 203873) (by norm_num)
theorem B8171189 : Blo 1449544 8171189 := bbase (se 5 (by rfl) ⟨383024, by rfl⟩ : syracuseStep 8171189 = 766049) (by norm_num)
theorem B2174669 : Blo 1449544 2174669 := bbase (se 3 (by rfl) ⟨407750, by rfl⟩ : syracuseStep 2174669 = 815501) (by norm_num)
theorem B4132565 : Blo 1449544 4132565 := bbase (se 7 (by rfl) ⟨48428, by rfl⟩ : syracuseStep 4132565 = 96857) (by norm_num)
theorem B2174693 : Blo 1449544 2174693 := bbase (se 4 (by rfl) ⟨203877, by rfl⟩ : syracuseStep 2174693 = 407755) (by norm_num)
theorem B3264245 : Blo 1449544 3264245 := bbase (se 5 (by rfl) ⟨153011, by rfl⟩ : syracuseStep 3264245 = 306023) (by norm_num)
theorem B2174717 : Blo 1449544 2174717 := bbase (se 3 (by rfl) ⟨407759, by rfl⟩ : syracuseStep 2174717 = 815519) (by norm_num)
theorem B2174741 : Blo 1449544 2174741 := bbase (se 6 (by rfl) ⟨50970, by rfl⟩ : syracuseStep 2174741 = 101941) (by norm_num)
theorem B2174765 : Blo 1449544 2174765 := bbase (se 3 (by rfl) ⟨407768, by rfl⟩ : syracuseStep 2174765 = 815537) (by norm_num)
theorem B5959477 : Blo 1449544 5959477 := bbase (se 5 (by rfl) ⟨279350, by rfl⟩ : syracuseStep 5959477 = 558701) (by norm_num)
theorem B5508917 : Blo 1449544 5508917 := bbase (se 5 (by rfl) ⟨258230, by rfl⟩ : syracuseStep 5508917 = 516461) (by norm_num)
theorem B3264317 : Blo 1449544 3264317 := bbase (se 3 (by rfl) ⟨612059, by rfl⟩ : syracuseStep 3264317 = 1224119) (by norm_num)
theorem B2174789 : Blo 1449544 2174789 := bbase (se 4 (by rfl) ⟨203886, by rfl⟩ : syracuseStep 2174789 = 407773) (by norm_num)
theorem B2174813 : Blo 1449544 2174813 := bbase (se 3 (by rfl) ⟨407777, by rfl⟩ : syracuseStep 2174813 = 815555) (by norm_num)
theorem B3673957 : Blo 1449544 3673957 := bbase (se 4 (by rfl) ⟨344433, by rfl⟩ : syracuseStep 3673957 = 688867) (by norm_num)
theorem B2174837 : Blo 1449544 2174837 := bbase (se 5 (by rfl) ⟨101945, by rfl⟩ : syracuseStep 2174837 = 203891) (by norm_num)
theorem B3264389 : Blo 1449544 3264389 := bbase (se 4 (by rfl) ⟨306036, by rfl⟩ : syracuseStep 3264389 = 612073) (by norm_num)
theorem B2174861 : Blo 1449544 2174861 := bbase (se 3 (by rfl) ⟨407786, by rfl⟩ : syracuseStep 2174861 = 815573) (by norm_num)
theorem B4894613 : Blo 1449544 4894613 := bbase (se 6 (by rfl) ⟨114717, by rfl⟩ : syracuseStep 4894613 = 229435) (by norm_num)
theorem B2174885 : Blo 1449544 2174885 := bbase (se 4 (by rfl) ⟨203895, by rfl⟩ : syracuseStep 2174885 = 407791) (by norm_num)
theorem B2174909 : Blo 1449544 2174909 := bbase (se 3 (by rfl) ⟨407795, by rfl⟩ : syracuseStep 2174909 = 815591) (by norm_num)
theorem B3264461 : Blo 1449544 3264461 := bbase (se 3 (by rfl) ⟨612086, by rfl⟩ : syracuseStep 3264461 = 1224173) (by norm_num)
theorem B2322389 : Blo 1449544 2322389 := bbase (se 7 (by rfl) ⟨27215, by rfl⟩ : syracuseStep 2322389 = 54431) (by norm_num)
theorem B2174933 : Blo 1449544 2174933 := bbase (se 7 (by rfl) ⟨25487, by rfl⟩ : syracuseStep 2174933 = 50975) (by norm_num)
theorem B3674069 : Blo 1449544 3674069 := bbase (se 7 (by rfl) ⟨43055, by rfl⟩ : syracuseStep 3674069 = 86111) (by norm_num)
theorem B2174957 : Blo 1449544 2174957 := bbase (se 3 (by rfl) ⟨407804, by rfl⟩ : syracuseStep 2174957 = 815609) (by norm_num)
theorem B8261621 : Blo 1449544 8261621 := bbase (se 5 (by rfl) ⟨387263, by rfl⟩ : syracuseStep 8261621 = 774527) (by norm_num)
theorem B2174981 : Blo 1449544 2174981 := bbase (se 4 (by rfl) ⟨203904, by rfl⟩ : syracuseStep 2174981 = 407809) (by norm_num)
theorem B3264533 : Blo 1449544 3264533 := bbase (se 6 (by rfl) ⟨76512, by rfl⟩ : syracuseStep 3264533 = 153025) (by norm_num)
theorem B2175005 : Blo 1449544 2175005 := bbase (se 3 (by rfl) ⟨407813, by rfl⟩ : syracuseStep 2175005 = 815627) (by norm_num)
theorem B2175029 : Blo 1449544 2175029 := bbase (se 5 (by rfl) ⟨101954, by rfl⟩ : syracuseStep 2175029 = 203909) (by norm_num)
theorem B2175053 : Blo 1449544 2175053 := bbase (se 3 (by rfl) ⟨407822, by rfl⟩ : syracuseStep 2175053 = 815645) (by norm_num)
theorem B5509205 : Blo 1449544 5509205 := bbase (se 8 (by rfl) ⟨32280, by rfl⟩ : syracuseStep 5509205 = 64561) (by norm_num)
theorem B3264605 : Blo 1449544 3264605 := bbase (se 3 (by rfl) ⟨612113, by rfl⟩ : syracuseStep 3264605 = 1224227) (by norm_num)
theorem B2175077 : Blo 1449544 2175077 := bbase (se 4 (by rfl) ⟨203913, by rfl⟩ : syracuseStep 2175077 = 407827) (by norm_num)
theorem B2175101 : Blo 1449544 2175101 := bbase (se 3 (by rfl) ⟨407831, by rfl⟩ : syracuseStep 2175101 = 815663) (by norm_num)
theorem B2175125 : Blo 1449544 2175125 := bbase (se 6 (by rfl) ⟨50979, by rfl⟩ : syracuseStep 2175125 = 101959) (by norm_num)
theorem B2322589 : Blo 1449544 2322589 := bbase (se 3 (by rfl) ⟨435485, by rfl⟩ : syracuseStep 2322589 = 870971) (by norm_num)
theorem B3264677 : Blo 1449544 3264677 := bbase (se 4 (by rfl) ⟨306063, by rfl⟩ : syracuseStep 3264677 = 612127) (by norm_num)
theorem B2175149 : Blo 1449544 2175149 := bbase (se 3 (by rfl) ⟨407840, by rfl⟩ : syracuseStep 2175149 = 815681) (by norm_num)
theorem B2175173 : Blo 1449544 2175173 := bbase (se 4 (by rfl) ⟨203922, by rfl⟩ : syracuseStep 2175173 = 407845) (by norm_num)
theorem B2175197 : Blo 1449544 2175197 := bbase (se 3 (by rfl) ⟨407849, by rfl⟩ : syracuseStep 2175197 = 815699) (by norm_num)
theorem B2093293 : Blo 1449544 2093293 := bbase (se 3 (by rfl) ⟨392492, by rfl⟩ : syracuseStep 2093293 = 784985) (by norm_num)
theorem B3264749 : Blo 1449544 3264749 := bbase (se 3 (by rfl) ⟨612140, by rfl⟩ : syracuseStep 3264749 = 1224281) (by norm_num)
theorem B4903157 : Blo 1449544 4903157 := bbase (se 5 (by rfl) ⟨229835, by rfl⟩ : syracuseStep 4903157 = 459671) (by norm_num)
theorem B2175221 : Blo 1449544 2175221 := bbase (se 5 (by rfl) ⟨101963, by rfl⟩ : syracuseStep 2175221 = 203927) (by norm_num)
theorem B2175245 : Blo 1449544 2175245 := bbase (se 3 (by rfl) ⟨407858, by rfl⟩ : syracuseStep 2175245 = 815717) (by norm_num)
theorem B18583829 : Blo 1449544 18583829 := bbase (se 6 (by rfl) ⟨435558, by rfl⟩ : syracuseStep 18583829 = 871117) (by norm_num)
theorem B2175269 : Blo 1449544 2175269 := bbase (se 4 (by rfl) ⟨203931, by rfl⟩ : syracuseStep 2175269 = 407863) (by norm_num)
theorem B3264821 : Blo 1449544 3264821 := bbase (se 5 (by rfl) ⟨153038, by rfl⟩ : syracuseStep 3264821 = 306077) (by norm_num)
theorem B2175293 : Blo 1449544 2175293 := bbase (se 3 (by rfl) ⟨407867, by rfl⟩ : syracuseStep 2175293 = 815735) (by norm_num)
theorem B4895045 : Blo 1449544 4895045 := bbase (se 4 (by rfl) ⟨458910, by rfl⟩ : syracuseStep 4895045 = 917821) (by norm_num)
theorem B2175317 : Blo 1449544 2175317 := bbase (se 10 (by rfl) ⟨3186, by rfl⟩ : syracuseStep 2175317 = 6373) (by norm_num)
theorem B2175341 : Blo 1449544 2175341 := bbase (se 3 (by rfl) ⟨407876, by rfl⟩ : syracuseStep 2175341 = 815753) (by norm_num)
theorem B3264893 : Blo 1449544 3264893 := bbase (se 3 (by rfl) ⟨612167, by rfl⟩ : syracuseStep 3264893 = 1224335) (by norm_num)
theorem B2175365 : Blo 1449544 2175365 := bbase (se 4 (by rfl) ⟨203940, by rfl⟩ : syracuseStep 2175365 = 407881) (by norm_num)
theorem B2322845 : Blo 1449544 2322845 := bbase (se 3 (by rfl) ⟨435533, by rfl⟩ : syracuseStep 2322845 = 871067) (by norm_num)
theorem B2175389 : Blo 1449544 2175389 := bbase (se 3 (by rfl) ⟨407885, by rfl⟩ : syracuseStep 2175389 = 815771) (by norm_num)
theorem B2175413 : Blo 1449544 2175413 := bbase (se 5 (by rfl) ⟨101972, by rfl⟩ : syracuseStep 2175413 = 203945) (by norm_num)
theorem B3264965 : Blo 1449544 3264965 := bbase (se 4 (by rfl) ⟨306090, by rfl⟩ : syracuseStep 3264965 = 612181) (by norm_num)
theorem B2175437 : Blo 1449544 2175437 := bbase (se 3 (by rfl) ⟨407894, by rfl⟩ : syracuseStep 2175437 = 815789) (by norm_num)
theorem B2175461 : Blo 1449544 2175461 := bbase (se 4 (by rfl) ⟨203949, by rfl⟩ : syracuseStep 2175461 = 407899) (by norm_num)
theorem B2175485 : Blo 1449544 2175485 := bbase (se 3 (by rfl) ⟨407903, by rfl⟩ : syracuseStep 2175485 = 815807) (by norm_num)
theorem B2789893 : Blo 1449544 2789893 := bbase (se 4 (by rfl) ⟨261552, by rfl⟩ : syracuseStep 2789893 = 523105) (by norm_num)
theorem B3265037 : Blo 1449544 3265037 := bbase (se 3 (by rfl) ⟨612194, by rfl⟩ : syracuseStep 3265037 = 1224389) (by norm_num)
theorem B2175509 : Blo 1449544 2175509 := bbase (se 6 (by rfl) ⟨50988, by rfl⟩ : syracuseStep 2175509 = 101977) (by norm_num)
theorem B2175533 : Blo 1449544 2175533 := bbase (se 3 (by rfl) ⟨407912, by rfl⟩ : syracuseStep 2175533 = 815825) (by norm_num)
theorem B2175557 : Blo 1449544 2175557 := bbase (se 4 (by rfl) ⟨203958, by rfl⟩ : syracuseStep 2175557 = 407917) (by norm_num)
theorem B2388557 : Blo 1449544 2388557 := bbase (se 3 (by rfl) ⟨447854, by rfl⟩ : syracuseStep 2388557 = 895709) (by norm_num)
theorem B3265109 : Blo 1449544 3265109 := bbase (se 8 (by rfl) ⟨19131, by rfl⟩ : syracuseStep 3265109 = 38263) (by norm_num)
theorem B2175581 : Blo 1449544 2175581 := bbase (se 3 (by rfl) ⟨407921, by rfl⟩ : syracuseStep 2175581 = 815843) (by norm_num)
theorem B2175605 : Blo 1449544 2175605 := bbase (se 5 (by rfl) ⟨101981, by rfl⟩ : syracuseStep 2175605 = 203963) (by norm_num)
theorem B2175629 : Blo 1449544 2175629 := bbase (se 3 (by rfl) ⟨407930, by rfl⟩ : syracuseStep 2175629 = 815861) (by norm_num)
theorem B3265181 : Blo 1449544 3265181 := bbase (se 3 (by rfl) ⟨612221, by rfl⟩ : syracuseStep 3265181 = 1224443) (by norm_num)
theorem B2175653 : Blo 1449544 2175653 := bbase (se 4 (by rfl) ⟨203967, by rfl⟩ : syracuseStep 2175653 = 407935) (by norm_num)
theorem B8819381 : Blo 1449544 8819381 := bbase (se 5 (by rfl) ⟨413408, by rfl⟩ : syracuseStep 8819381 = 826817) (by norm_num)
theorem B2175677 : Blo 1449544 2175677 := bbase (se 3 (by rfl) ⟨407939, by rfl⟩ : syracuseStep 2175677 = 815879) (by norm_num)
theorem B2175701 : Blo 1449544 2175701 := bbase (se 7 (by rfl) ⟨25496, by rfl⟩ : syracuseStep 2175701 = 50993) (by norm_num)
theorem B3265253 : Blo 1449544 3265253 := bbase (se 4 (by rfl) ⟨306117, by rfl⟩ : syracuseStep 3265253 = 612235) (by norm_num)
theorem B2175725 : Blo 1449544 2175725 := bbase (se 3 (by rfl) ⟨407948, by rfl⟩ : syracuseStep 2175725 = 815897) (by norm_num)
theorem B4895477 : Blo 1449544 4895477 := bbase (se 5 (by rfl) ⟨229475, by rfl⟩ : syracuseStep 4895477 = 458951) (by norm_num)
theorem B2175749 : Blo 1449544 2175749 := bbase (se 4 (by rfl) ⟨203976, by rfl⟩ : syracuseStep 2175749 = 407953) (by norm_num)
theorem B7344917 : Blo 1449544 7344917 := bbase (se 6 (by rfl) ⟨172146, by rfl⟩ : syracuseStep 7344917 = 344293) (by norm_num)
theorem B2175773 : Blo 1449544 2175773 := bbase (se 3 (by rfl) ⟨407957, by rfl⟩ : syracuseStep 2175773 = 815915) (by norm_num)
theorem B3265325 : Blo 1449544 3265325 := bbase (se 3 (by rfl) ⟨612248, by rfl⟩ : syracuseStep 3265325 = 1224497) (by norm_num)
theorem B2175797 : Blo 1449544 2175797 := bbase (se 5 (by rfl) ⟨101990, by rfl⟩ : syracuseStep 2175797 = 203981) (by norm_num)
theorem B2175821 : Blo 1449544 2175821 := bbase (se 3 (by rfl) ⟨407966, by rfl⟩ : syracuseStep 2175821 = 815933) (by norm_num)
theorem B2175845 : Blo 1449544 2175845 := bbase (se 4 (by rfl) ⟨203985, by rfl⟩ : syracuseStep 2175845 = 407971) (by norm_num)
theorem B3265397 : Blo 1449544 3265397 := bbase (se 5 (by rfl) ⟨153065, by rfl⟩ : syracuseStep 3265397 = 306131) (by norm_num)
theorem B2175869 : Blo 1449544 2175869 := bbase (se 3 (by rfl) ⟨407975, by rfl⟩ : syracuseStep 2175869 = 815951) (by norm_num)
theorem B2446213 : Blo 1449544 2446213 := bbase (se 4 (by rfl) ⟨229332, by rfl⟩ : syracuseStep 2446213 = 458665) (by norm_num)
theorem B2175893 : Blo 1449544 2175893 := bbase (se 6 (by rfl) ⟨50997, by rfl⟩ : syracuseStep 2175893 = 101995) (by norm_num)
theorem B2175917 : Blo 1449544 2175917 := bbase (se 3 (by rfl) ⟨407984, by rfl⟩ : syracuseStep 2175917 = 815969) (by norm_num)
theorem B3265469 : Blo 1449544 3265469 := bbase (se 3 (by rfl) ⟨612275, by rfl⟩ : syracuseStep 3265469 = 1224551) (by norm_num)
theorem B2175941 : Blo 1449544 2175941 := bbase (se 4 (by rfl) ⟨203994, by rfl⟩ : syracuseStep 2175941 = 407989) (by norm_num)
theorem B2446301 : Blo 1449544 2446301 := bbase (se 3 (by rfl) ⟨458681, by rfl⟩ : syracuseStep 2446301 = 917363) (by norm_num)
theorem B2175965 : Blo 1449544 2175965 := bbase (se 3 (by rfl) ⟨407993, by rfl⟩ : syracuseStep 2175965 = 815987) (by norm_num)
theorem B4649957 : Blo 1449544 4649957 := bbase (se 4 (by rfl) ⟨435933, by rfl⟩ : syracuseStep 4649957 = 871867) (by norm_num)
theorem B2175989 : Blo 1449544 2175989 := bbase (se 5 (by rfl) ⟨101999, by rfl⟩ : syracuseStep 2175989 = 203999) (by norm_num)
theorem B3265541 : Blo 1449544 3265541 := bbase (se 4 (by rfl) ⟨306144, by rfl⟩ : syracuseStep 3265541 = 612289) (by norm_num)
theorem B2176013 : Blo 1449544 2176013 := bbase (se 3 (by rfl) ⟨408002, by rfl⟩ : syracuseStep 2176013 = 816005) (by norm_num)
theorem B11015189 : Blo 1449544 11015189 := bbase (se 6 (by rfl) ⟨258168, by rfl⟩ : syracuseStep 11015189 = 516337) (by norm_num)
theorem B2176037 : Blo 1449544 2176037 := bbase (se 4 (by rfl) ⟨204003, by rfl⟩ : syracuseStep 2176037 = 408007) (by norm_num)
theorem B2176061 : Blo 1449544 2176061 := bbase (se 3 (by rfl) ⟨408011, by rfl⟩ : syracuseStep 2176061 = 816023) (by norm_num)
theorem B3265613 : Blo 1449544 3265613 := bbase (se 3 (by rfl) ⟨612302, by rfl⟩ : syracuseStep 3265613 = 1224605) (by norm_num)
theorem B2176085 : Blo 1449544 2176085 := bbase (se 8 (by rfl) ⟨12750, by rfl⟩ : syracuseStep 2176085 = 25501) (by norm_num)
theorem B2446429 : Blo 1449544 2446429 := bbase (se 3 (by rfl) ⟨458705, by rfl⟩ : syracuseStep 2446429 = 917411) (by norm_num)
theorem B2176109 : Blo 1449544 2176109 := bbase (se 3 (by rfl) ⟨408020, by rfl⟩ : syracuseStep 2176109 = 816041) (by norm_num)
theorem B6616181 : Blo 1449544 6616181 := bbase (se 5 (by rfl) ⟨310133, by rfl⟩ : syracuseStep 6616181 = 620267) (by norm_num)
theorem B3306629 : Blo 1449544 3306629 := bbase (se 4 (by rfl) ⟨309996, by rfl⟩ : syracuseStep 3306629 = 619993) (by norm_num)
theorem B2176133 : Blo 1449544 2176133 := bbase (se 4 (by rfl) ⟨204012, by rfl⟩ : syracuseStep 2176133 = 408025) (by norm_num)
theorem B3265685 : Blo 1449544 3265685 := bbase (se 6 (by rfl) ⟨76539, by rfl⟩ : syracuseStep 3265685 = 153079) (by norm_num)
theorem B2176157 : Blo 1449544 2176157 := bbase (se 3 (by rfl) ⟨408029, by rfl⟩ : syracuseStep 2176157 = 816059) (by norm_num)
theorem B4895909 : Blo 1449544 4895909 := bbase (se 4 (by rfl) ⟨458991, by rfl⟩ : syracuseStep 4895909 = 917983) (by norm_num)
theorem B6198437 : Blo 1449544 6198437 := bbase (se 4 (by rfl) ⟨581103, by rfl⟩ : syracuseStep 6198437 = 1162207) (by norm_num)
theorem B7836853 : Blo 1449544 7836853 := bbase (se 5 (by rfl) ⟨367352, by rfl⟩ : syracuseStep 7836853 = 734705) (by norm_num)
theorem B2446517 : Blo 1449544 2446517 := bbase (se 5 (by rfl) ⟨114680, by rfl⟩ : syracuseStep 2446517 = 229361) (by norm_num)
theorem B2176181 : Blo 1449544 2176181 := bbase (se 5 (by rfl) ⟨102008, by rfl⟩ : syracuseStep 2176181 = 204017) (by norm_num)
theorem B2176205 : Blo 1449544 2176205 := bbase (se 3 (by rfl) ⟨408038, by rfl⟩ : syracuseStep 2176205 = 816077) (by norm_num)
theorem B1742033 : Blo 1449544 1742033 := bbase (se 2 (by rfl) ⟨653262, by rfl⟩ : syracuseStep 1742033 = 1306525) (by norm_num)
theorem B3265757 : Blo 1449544 3265757 := bbase (se 3 (by rfl) ⟨612329, by rfl⟩ : syracuseStep 3265757 = 1224659) (by norm_num)
theorem B2176229 : Blo 1449544 2176229 := bbase (se 4 (by rfl) ⟨204021, by rfl⟩ : syracuseStep 2176229 = 408043) (by norm_num)
theorem B5510389 : Blo 1449544 5510389 := bbase (se 5 (by rfl) ⟨258299, by rfl⟩ : syracuseStep 5510389 = 516599) (by norm_num)
theorem B2176253 : Blo 1449544 2176253 := bbase (se 3 (by rfl) ⟨408047, by rfl⟩ : syracuseStep 2176253 = 816095) (by norm_num)
theorem B2176277 : Blo 1449544 2176277 := bbase (se 6 (by rfl) ⟨51006, by rfl⟩ : syracuseStep 2176277 = 102013) (by norm_num)
theorem B3265829 : Blo 1449544 3265829 := bbase (se 4 (by rfl) ⟨306171, by rfl⟩ : syracuseStep 3265829 = 612343) (by norm_num)
theorem B2176301 : Blo 1449544 2176301 := bbase (se 3 (by rfl) ⟨408056, by rfl⟩ : syracuseStep 2176301 = 816113) (by norm_num)
theorem B2446645 : Blo 1449544 2446645 := bbase (se 5 (by rfl) ⟨114686, by rfl⟩ : syracuseStep 2446645 = 229373) (by norm_num)
theorem B2176325 : Blo 1449544 2176325 := bbase (se 4 (by rfl) ⟨204030, by rfl⟩ : syracuseStep 2176325 = 408061) (by norm_num)
theorem B2176349 : Blo 1449544 2176349 := bbase (se 3 (by rfl) ⟨408065, by rfl⟩ : syracuseStep 2176349 = 816131) (by norm_num)
theorem B3265901 : Blo 1449544 3265901 := bbase (se 3 (by rfl) ⟨612356, by rfl⟩ : syracuseStep 3265901 = 1224713) (by norm_num)
theorem B2176373 : Blo 1449544 2176373 := bbase (se 5 (by rfl) ⟨102017, by rfl⟩ : syracuseStep 2176373 = 204035) (by norm_num)
theorem B2446733 : Blo 1449544 2446733 := bbase (se 3 (by rfl) ⟨458762, by rfl⟩ : syracuseStep 2446733 = 917525) (by norm_num)
theorem B2176397 : Blo 1449544 2176397 := bbase (se 3 (by rfl) ⟨408074, by rfl⟩ : syracuseStep 2176397 = 816149) (by norm_num)
theorem B16520597 : Blo 1449544 16520597 := bbase (se 6 (by rfl) ⟨387201, by rfl⟩ : syracuseStep 16520597 = 774403) (by norm_num)
theorem B6198677 : Blo 1449544 6198677 := bbase (se 6 (by rfl) ⟨145281, by rfl⟩ : syracuseStep 6198677 = 290563) (by norm_num)
theorem B2176421 : Blo 1449544 2176421 := bbase (se 4 (by rfl) ⟨204039, by rfl⟩ : syracuseStep 2176421 = 408079) (by norm_num)
theorem B3487141 : Blo 1449544 3487141 := bbase (se 4 (by rfl) ⟨326919, by rfl⟩ : syracuseStep 3487141 = 653839) (by norm_num)
theorem B3265973 : Blo 1449544 3265973 := bbase (se 5 (by rfl) ⟨153092, by rfl⟩ : syracuseStep 3265973 = 306185) (by norm_num)
theorem B2176445 : Blo 1449544 2176445 := bbase (se 3 (by rfl) ⟨408083, by rfl⟩ : syracuseStep 2176445 = 816167) (by norm_num)
theorem B2176469 : Blo 1449544 2176469 := bbase (se 7 (by rfl) ⟨25505, by rfl⟩ : syracuseStep 2176469 = 51011) (by norm_num)
theorem B2176493 : Blo 1449544 2176493 := bbase (se 3 (by rfl) ⟨408092, by rfl⟩ : syracuseStep 2176493 = 816185) (by norm_num)
theorem B2323973 : Blo 1449544 2323973 := bbase (se 4 (by rfl) ⟨217872, by rfl⟩ : syracuseStep 2323973 = 435745) (by norm_num)
theorem B2176517 : Blo 1449544 2176517 := bbase (se 4 (by rfl) ⟨204048, by rfl⟩ : syracuseStep 2176517 = 408097) (by norm_num)
theorem B2446861 : Blo 1449544 2446861 := bbase (se 3 (by rfl) ⟨458786, by rfl⟩ : syracuseStep 2446861 = 917573) (by norm_num)
theorem B2176541 : Blo 1449544 2176541 := bbase (se 3 (by rfl) ⟨408101, by rfl⟩ : syracuseStep 2176541 = 816203) (by norm_num)
theorem B5510693 : Blo 1449544 5510693 := bbase (se 4 (by rfl) ⟨516627, by rfl⟩ : syracuseStep 5510693 = 1033255) (by norm_num)
theorem B2176565 : Blo 1449544 2176565 := bbase (se 5 (by rfl) ⟨102026, by rfl⟩ : syracuseStep 2176565 = 204053) (by norm_num)
theorem B2176589 : Blo 1449544 2176589 := bbase (se 3 (by rfl) ⟨408110, by rfl⟩ : syracuseStep 2176589 = 816221) (by norm_num)
theorem B4896341 : Blo 1449544 4896341 := bbase (se 8 (by rfl) ⟨28689, by rfl⟩ : syracuseStep 4896341 = 57379) (by norm_num)
theorem B2446949 : Blo 1449544 2446949 := bbase (se 4 (by rfl) ⟨229401, by rfl⟩ : syracuseStep 2446949 = 458803) (by norm_num)
theorem B2176613 : Blo 1449544 2176613 := bbase (se 4 (by rfl) ⟨204057, by rfl⟩ : syracuseStep 2176613 = 408115) (by norm_num)
theorem B3397229 : Blo 1449544 3397229 := bbase (se 3 (by rfl) ⟨636980, by rfl⟩ : syracuseStep 3397229 = 1273961) (by norm_num)
theorem B2176637 : Blo 1449544 2176637 := bbase (se 3 (by rfl) ⟨408119, by rfl⟩ : syracuseStep 2176637 = 816239) (by norm_num)
theorem B1570433 : Blo 1449544 1570433 := bbase (se 2 (by rfl) ⟨588912, by rfl⟩ : syracuseStep 1570433 = 1177825) (by norm_num)
theorem B2176661 : Blo 1449544 2176661 := bbase (se 6 (by rfl) ⟨51015, by rfl⟩ : syracuseStep 2176661 = 102031) (by norm_num)
theorem B2176685 : Blo 1449544 2176685 := bbase (se 3 (by rfl) ⟨408128, by rfl⟩ : syracuseStep 2176685 = 816257) (by norm_num)
theorem B2176709 : Blo 1449544 2176709 := bbase (se 4 (by rfl) ⟨204066, by rfl⟩ : syracuseStep 2176709 = 408133) (by norm_num)
theorem B7845589 : Blo 1449544 7845589 := bbase (se 7 (by rfl) ⟨91940, by rfl⟩ : syracuseStep 7845589 = 183881) (by norm_num)
theorem B2176733 : Blo 1449544 2176733 := bbase (se 3 (by rfl) ⟨408137, by rfl⟩ : syracuseStep 2176733 = 816275) (by norm_num)
theorem B2447077 : Blo 1449544 2447077 := bbase (se 4 (by rfl) ⟨229413, by rfl⟩ : syracuseStep 2447077 = 458827) (by norm_num)
theorem B2176757 : Blo 1449544 2176757 := bbase (se 5 (by rfl) ⟨102035, by rfl⟩ : syracuseStep 2176757 = 204071) (by norm_num)
theorem B2176781 : Blo 1449544 2176781 := bbase (se 3 (by rfl) ⟨408146, by rfl⟩ : syracuseStep 2176781 = 816293) (by norm_num)
theorem B2176805 : Blo 1449544 2176805 := bbase (se 4 (by rfl) ⟨204075, by rfl⟩ : syracuseStep 2176805 = 408151) (by norm_num)
theorem B2447165 : Blo 1449544 2447165 := bbase (se 3 (by rfl) ⟨458843, by rfl⟩ : syracuseStep 2447165 = 917687) (by norm_num)
theorem B2176829 : Blo 1449544 2176829 := bbase (se 3 (by rfl) ⟨408155, by rfl⟩ : syracuseStep 2176829 = 816311) (by norm_num)
theorem B2176853 : Blo 1449544 2176853 := bbase (se 9 (by rfl) ⟨6377, by rfl⟩ : syracuseStep 2176853 = 12755) (by norm_num)
theorem B2176877 : Blo 1449544 2176877 := bbase (se 3 (by rfl) ⟨408164, by rfl⟩ : syracuseStep 2176877 = 816329) (by norm_num)
theorem B2176901 : Blo 1449544 2176901 := bbase (se 4 (by rfl) ⟨204084, by rfl⟩ : syracuseStep 2176901 = 408169) (by norm_num)
theorem B2176925 : Blo 1449544 2176925 := bbase (se 3 (by rfl) ⟨408173, by rfl⟩ : syracuseStep 2176925 = 816347) (by norm_num)
theorem B1742753 : Blo 1449544 1742753 := bbase (se 2 (by rfl) ⟨653532, by rfl⟩ : syracuseStep 1742753 = 1307065) (by norm_num)
theorem B2176949 : Blo 1449544 2176949 := bbase (se 5 (by rfl) ⟨102044, by rfl⟩ : syracuseStep 2176949 = 204089) (by norm_num)
theorem B2447293 : Blo 1449544 2447293 := bbase (se 3 (by rfl) ⟨458867, by rfl⟩ : syracuseStep 2447293 = 917735) (by norm_num)
theorem B2176973 : Blo 1449544 2176973 := bbase (se 3 (by rfl) ⟨408182, by rfl⟩ : syracuseStep 2176973 = 816365) (by norm_num)
theorem B24778709 : Blo 1449544 24778709 := bbase (se 7 (by rfl) ⟨290375, by rfl⟩ : syracuseStep 24778709 = 580751) (by norm_num)
theorem B2176997 : Blo 1449544 2176997 := bbase (se 4 (by rfl) ⟨204093, by rfl⟩ : syracuseStep 2176997 = 408187) (by norm_num)
theorem B2177021 : Blo 1449544 2177021 := bbase (se 3 (by rfl) ⟨408191, by rfl⟩ : syracuseStep 2177021 = 816383) (by norm_num)
theorem B4896773 : Blo 1449544 4896773 := bbase (se 4 (by rfl) ⟨459072, by rfl⟩ : syracuseStep 4896773 = 918145) (by norm_num)
theorem B2324485 : Blo 1449544 2324485 := bbase (se 4 (by rfl) ⟨217920, by rfl⟩ : syracuseStep 2324485 = 435841) (by norm_num)
theorem B2447381 : Blo 1449544 2447381 := bbase (se 6 (by rfl) ⟨57360, by rfl⟩ : syracuseStep 2447381 = 114721) (by norm_num)
theorem B2177045 : Blo 1449544 2177045 := bbase (se 6 (by rfl) ⟨51024, by rfl⟩ : syracuseStep 2177045 = 102049) (by norm_num)
theorem B7346213 : Blo 1449544 7346213 := bbase (se 4 (by rfl) ⟨688707, by rfl⟩ : syracuseStep 7346213 = 1377415) (by norm_num)
theorem B2177069 : Blo 1449544 2177069 := bbase (se 3 (by rfl) ⟨408200, by rfl⟩ : syracuseStep 2177069 = 816401) (by norm_num)
theorem B2177093 : Blo 1449544 2177093 := bbase (se 4 (by rfl) ⟨204102, by rfl⟩ : syracuseStep 2177093 = 408205) (by norm_num)
theorem B2177117 : Blo 1449544 2177117 := bbase (se 3 (by rfl) ⟨408209, by rfl⟩ : syracuseStep 2177117 = 816419) (by norm_num)
theorem B2177141 : Blo 1449544 2177141 := bbase (se 5 (by rfl) ⟨102053, by rfl⟩ : syracuseStep 2177141 = 204107) (by norm_num)
theorem B2177165 : Blo 1449544 2177165 := bbase (se 3 (by rfl) ⟨408218, by rfl⟩ : syracuseStep 2177165 = 816437) (by norm_num)
theorem B2447509 : Blo 1449544 2447509 := bbase (se 6 (by rfl) ⟨57363, by rfl⟩ : syracuseStep 2447509 = 114727) (by norm_num)
theorem B2177189 : Blo 1449544 2177189 := bbase (se 4 (by rfl) ⟨204111, by rfl⟩ : syracuseStep 2177189 = 408223) (by norm_num)
theorem B2177213 : Blo 1449544 2177213 := bbase (se 3 (by rfl) ⟨408227, by rfl⟩ : syracuseStep 2177213 = 816455) (by norm_num)
theorem B1743061 : Blo 1449544 1743061 := bbase (se 7 (by rfl) ⟨20426, by rfl⟩ : syracuseStep 1743061 = 40853) (by norm_num)
theorem B2177237 : Blo 1449544 2177237 := bbase (se 7 (by rfl) ⟨25514, by rfl⟩ : syracuseStep 2177237 = 51029) (by norm_num)
theorem B2447597 : Blo 1449544 2447597 := bbase (se 3 (by rfl) ⟨458924, by rfl⟩ : syracuseStep 2447597 = 917849) (by norm_num)
theorem B2177261 : Blo 1449544 2177261 := bbase (se 3 (by rfl) ⟨408236, by rfl⟩ : syracuseStep 2177261 = 816473) (by norm_num)
theorem B9296117 : Blo 1449544 9296117 := bbase (se 5 (by rfl) ⟨435755, by rfl⟩ : syracuseStep 9296117 = 871511) (by norm_num)
theorem B2177285 : Blo 1449544 2177285 := bbase (se 4 (by rfl) ⟨204120, by rfl⟩ : syracuseStep 2177285 = 408241) (by norm_num)
theorem B2791693 : Blo 1449544 2791693 := bbase (se 3 (by rfl) ⟨523442, by rfl⟩ : syracuseStep 2791693 = 1046885) (by norm_num)
theorem B2177309 : Blo 1449544 2177309 := bbase (se 3 (by rfl) ⟨408245, by rfl⟩ : syracuseStep 2177309 = 816491) (by norm_num)
theorem B6617381 : Blo 1449544 6617381 := bbase (se 4 (by rfl) ⟨620379, by rfl⟩ : syracuseStep 6617381 = 1240759) (by norm_num)
theorem B1743157 : Blo 1449544 1743157 := bbase (se 5 (by rfl) ⟨81710, by rfl⟩ : syracuseStep 1743157 = 163421) (by norm_num)
theorem B2447725 : Blo 1449544 2447725 := bbase (se 3 (by rfl) ⟨458948, by rfl⟩ : syracuseStep 2447725 = 917897) (by norm_num)
theorem B1571185 : Blo 1449544 1571185 := bbase (se 2 (by rfl) ⟨589194, by rfl⟩ : syracuseStep 1571185 = 1178389) (by norm_num)
theorem B3307925 : Blo 1449544 3307925 := bbase (se 6 (by rfl) ⟨77529, by rfl⟩ : syracuseStep 3307925 = 155059) (by norm_num)
theorem B4897205 : Blo 1449544 4897205 := bbase (se 5 (by rfl) ⟨229556, by rfl⟩ : syracuseStep 4897205 = 459113) (by norm_num)
theorem B7338437 : Blo 1449544 7338437 := bbase (se 4 (by rfl) ⟨687978, by rfl⟩ : syracuseStep 7338437 = 1375957) (by norm_num)
theorem B2447813 : Blo 1449544 2447813 := bbase (se 4 (by rfl) ⟨229482, by rfl⟩ : syracuseStep 2447813 = 458965) (by norm_num)
theorem B1743301 : Blo 1449544 1743301 := bbase (se 4 (by rfl) ⟨163434, by rfl⟩ : syracuseStep 1743301 = 326869) (by norm_num)
theorem B3307997 : Blo 1449544 3307997 := bbase (se 3 (by rfl) ⟨620249, by rfl⟩ : syracuseStep 3307997 = 1240499) (by norm_num)
theorem B2325029 : Blo 1449544 2325029 := bbase (se 4 (by rfl) ⟨217971, by rfl⟩ : syracuseStep 2325029 = 435943) (by norm_num)
theorem B2447941 : Blo 1449544 2447941 := bbase (se 4 (by rfl) ⟨229494, by rfl⟩ : syracuseStep 2447941 = 458989) (by norm_num)
theorem B2448029 : Blo 1449544 2448029 := bbase (se 3 (by rfl) ⟨459005, by rfl⟩ : syracuseStep 2448029 = 918011) (by norm_num)
theorem B2448157 : Blo 1449544 2448157 := bbase (se 3 (by rfl) ⟨459029, by rfl⟩ : syracuseStep 2448157 = 918059) (by norm_num)
theorem B4897637 : Blo 1449544 4897637 := bbase (se 4 (by rfl) ⟨459153, by rfl⟩ : syracuseStep 4897637 = 918307) (by norm_num)
theorem B2448245 : Blo 1449544 2448245 := bbase (se 5 (by rfl) ⟨114761, by rfl⟩ : syracuseStep 2448245 = 229523) (by norm_num)
theorem B21199765 : Blo 1449544 21199765 := bbase (se 6 (by rfl) ⟨496869, by rfl⟩ : syracuseStep 21199765 = 993739) (by norm_num)
theorem B3308501 : Blo 1449544 3308501 := bbase (se 7 (by rfl) ⟨38771, by rfl⟩ : syracuseStep 3308501 = 77543) (by norm_num)
theorem B12246005 : Blo 1449544 12246005 := bbase (se 5 (by rfl) ⟨574031, by rfl⟩ : syracuseStep 12246005 = 1148063) (by norm_num)
theorem B2448373 : Blo 1449544 2448373 := bbase (se 5 (by rfl) ⟨114767, by rfl⟩ : syracuseStep 2448373 = 229535) (by norm_num)
theorem B3308581 : Blo 1449544 3308581 := bbase (se 4 (by rfl) ⟨310179, by rfl⟩ : syracuseStep 3308581 = 620359) (by norm_num)
theorem B2448461 : Blo 1449544 2448461 := bbase (se 3 (by rfl) ⟨459086, by rfl⟩ : syracuseStep 2448461 = 918173) (by norm_num)
theorem B2939989 : Blo 1449544 2939989 := bbase (se 8 (by rfl) ⟨17226, by rfl⟩ : syracuseStep 2939989 = 34453) (by norm_num)
theorem B1653853 : Blo 1449544 1653853 := bbase (se 3 (by rfl) ⟨310097, by rfl⟩ : syracuseStep 1653853 = 620195) (by norm_num)
theorem B4127861 : Blo 1449544 4127861 := bbase (se 5 (by rfl) ⟨193493, by rfl⟩ : syracuseStep 4127861 = 386987) (by norm_num)
theorem B7445621 : Blo 1449544 7445621 := bbase (se 5 (by rfl) ⟨349013, by rfl⟩ : syracuseStep 7445621 = 698027) (by norm_num)
theorem B2612429 : Blo 1449544 2612429 := bbase (se 3 (by rfl) ⟨489830, by rfl⟩ : syracuseStep 2612429 = 979661) (by norm_num)
theorem B2448589 : Blo 1449544 2448589 := bbase (se 3 (by rfl) ⟨459110, by rfl⟩ : syracuseStep 2448589 = 918221) (by norm_num)
theorem B6192389 : Blo 1449544 6192389 := bbase (se 4 (by rfl) ⟨580536, by rfl⟩ : syracuseStep 6192389 = 1161073) (by norm_num)
theorem B4898069 : Blo 1449544 4898069 := bbase (se 6 (by rfl) ⟨114798, by rfl⟩ : syracuseStep 4898069 = 229597) (by norm_num)
theorem B2448677 : Blo 1449544 2448677 := bbase (se 4 (by rfl) ⟨229563, by rfl⟩ : syracuseStep 2448677 = 459127) (by norm_num)
theorem B7347509 : Blo 1449544 7347509 := bbase (se 5 (by rfl) ⟨344414, by rfl⟩ : syracuseStep 7347509 = 688829) (by norm_num)
theorem B10452341 : Blo 1449544 10452341 := bbase (se 5 (by rfl) ⟨489953, by rfl⟩ : syracuseStep 10452341 = 979907) (by norm_num)
theorem B2448805 : Blo 1449544 2448805 := bbase (se 4 (by rfl) ⟨229575, by rfl⟩ : syracuseStep 2448805 = 459151) (by norm_num)
theorem B3669421 : Blo 1449544 3669421 := bbase (se 3 (by rfl) ⟨688016, by rfl⟩ : syracuseStep 3669421 = 1376033) (by norm_num)
theorem B2448893 : Blo 1449544 2448893 := bbase (se 3 (by rfl) ⟨459167, by rfl⟩ : syracuseStep 2448893 = 918335) (by norm_num)
theorem B3669533 : Blo 1449544 3669533 := bbase (se 3 (by rfl) ⟨688037, by rfl⟩ : syracuseStep 3669533 = 1376075) (by norm_num)
theorem B1834589 : Blo 1449544 1834589 := bbase (se 3 (by rfl) ⟨343985, by rfl⟩ : syracuseStep 1834589 = 687971) (by norm_num)
theorem B2449021 : Blo 1449544 2449021 := bbase (se 3 (by rfl) ⟨459191, by rfl⟩ : syracuseStep 2449021 = 918383) (by norm_num)
theorem B1834645 : Blo 1449544 1834645 := bbase (se 6 (by rfl) ⟨42999, by rfl⟩ : syracuseStep 1834645 = 85999) (by norm_num)
theorem B2752157 : Blo 1449544 2752157 := bbase (se 3 (by rfl) ⟨516029, by rfl⟩ : syracuseStep 2752157 = 1032059) (by norm_num)
theorem B1547969 : Blo 1449544 1547969 := bbase (se 2 (by rfl) ⟨580488, by rfl⟩ : syracuseStep 1547969 = 1160977) (by norm_num)
theorem B4898501 : Blo 1449544 4898501 := bbase (se 4 (by rfl) ⟨459234, by rfl⟩ : syracuseStep 4898501 = 918469) (by norm_num)
theorem B7339733 : Blo 1449544 7339733 := bbase (se 7 (by rfl) ⟨86012, by rfl⟩ : syracuseStep 7339733 = 172025) (by norm_num)
theorem B2449109 : Blo 1449544 2449109 := bbase (se 7 (by rfl) ⟨28700, by rfl⟩ : syracuseStep 2449109 = 57401) (by norm_num)
theorem B3669725 : Blo 1449544 3669725 := bbase (se 3 (by rfl) ⟨688073, by rfl⟩ : syracuseStep 3669725 = 1376147) (by norm_num)
theorem B1834741 : Blo 1449544 1834741 := bbase (se 5 (by rfl) ⟨86003, by rfl⟩ : syracuseStep 1834741 = 172007) (by norm_num)
theorem B1548029 : Blo 1449544 1548029 := bbase (se 3 (by rfl) ⟨290255, by rfl⟩ : syracuseStep 1548029 = 580511) (by norm_num)
theorem B4128533 : Blo 1449544 4128533 := bbase (se 6 (by rfl) ⟨96762, by rfl⟩ : syracuseStep 4128533 = 193525) (by norm_num)
theorem B4185877 : Blo 1449544 4185877 := bbase (se 6 (by rfl) ⟨98106, by rfl⟩ : syracuseStep 4185877 = 196213) (by norm_num)
theorem B2752309 : Blo 1449544 2752309 := bbase (se 5 (by rfl) ⟨129014, by rfl⟩ : syracuseStep 2752309 = 258029) (by norm_num)
theorem B7446325 : Blo 1449544 7446325 := bbase (se 5 (by rfl) ⟨349046, by rfl⟩ : syracuseStep 7446325 = 698093) (by norm_num)
theorem B2449237 : Blo 1449544 2449237 := bbase (se 9 (by rfl) ⟨7175, by rfl⟩ : syracuseStep 2449237 = 14351) (by norm_num)
theorem B2236261 : Blo 1449544 2236261 := bbase (se 4 (by rfl) ⟨209649, by rfl⟩ : syracuseStep 2236261 = 419299) (by norm_num)
theorem B1548157 : Blo 1449544 1548157 := bbase (se 3 (by rfl) ⟨290279, by rfl⟩ : syracuseStep 1548157 = 580559) (by norm_num)
theorem B1834913 : Blo 1449544 1834913 := bbase (se 2 (by rfl) ⟨688092, by rfl⟩ : syracuseStep 1834913 = 1376185) (by norm_num)
theorem B3096485 : Blo 1449544 3096485 := bbase (se 4 (by rfl) ⟨290295, by rfl⟩ : syracuseStep 3096485 = 580591) (by norm_num)
theorem B2449325 : Blo 1449544 2449325 := bbase (se 3 (by rfl) ⟨459248, by rfl⟩ : syracuseStep 2449325 = 918497) (by norm_num)
theorem B2654165 : Blo 1449544 2654165 := bbase (se 7 (by rfl) ⟨31103, by rfl⟩ : syracuseStep 2654165 = 62207) (by norm_num)
theorem B1834969 : Blo 1449544 1834969 := bbase (se 2 (by rfl) ⟨688113, by rfl⟩ : syracuseStep 1834969 = 1376227) (by norm_num)
theorem B3670019 : Blo 1449544 3670019 := bstep (se 1 (by rfl) ⟨2752514, by rfl⟩ : syracuseStep 3670019 = 5505029) B5505029
theorem B1449987 : Blo 1449544 1449987 := bstep (se 1 (by rfl) ⟨1087490, by rfl⟩ : syracuseStep 1449987 = 2174981) B2174981
theorem B4644881 : Blo 1449544 4644881 := bstep (se 2 (by rfl) ⟨1741830, by rfl⟩ : syracuseStep 4644881 = 3483661) B3483661
theorem B2064403 : Blo 1449544 2064403 := bstep (se 1 (by rfl) ⟨1548302, by rfl⟩ : syracuseStep 2064403 = 3096605) B3096605
theorem B1450003 : Blo 1449544 1450003 := bstep (se 1 (by rfl) ⟨1087502, by rfl⟩ : syracuseStep 1450003 = 2175005) B2175005
theorem B1450019 : Blo 1449544 1450019 := bstep (se 1 (by rfl) ⟨1087514, by rfl⟩ : syracuseStep 1450019 = 2175029) B2175029
theorem B1450035 : Blo 1449544 1450035 := bstep (se 1 (by rfl) ⟨1087526, by rfl⟩ : syracuseStep 1450035 = 2175053) B2175053
theorem B1835075 : Blo 1449544 1835075 := bstep (se 1 (by rfl) ⟨1376306, by rfl⟩ : syracuseStep 1835075 = 2752613) B2752613
theorem B1450051 : Blo 1449544 1450051 := bstep (se 1 (by rfl) ⟨1087538, by rfl⟩ : syracuseStep 1450051 = 2175077) B2175077
theorem B1450067 : Blo 1449544 1450067 := bstep (se 1 (by rfl) ⟨1087550, by rfl⟩ : syracuseStep 1450067 = 2175101) B2175101
theorem B1450083 : Blo 1449544 1450083 := bstep (se 1 (by rfl) ⟨1087562, by rfl⟩ : syracuseStep 1450083 = 2175125) B2175125
theorem B1450099 : Blo 1449544 1450099 := bstep (se 1 (by rfl) ⟨1087574, by rfl⟩ : syracuseStep 1450099 = 2175149) B2175149
theorem B2752643 : Blo 1449544 2752643 := bstep (se 1 (by rfl) ⟨2064482, by rfl⟩ : syracuseStep 2752643 = 4128965) B4128965
theorem B1450115 : Blo 1449544 1450115 := bstep (se 1 (by rfl) ⟨1087586, by rfl⟩ : syracuseStep 1450115 = 2175173) B2175173
theorem B1450131 : Blo 1449544 1450131 := bstep (se 1 (by rfl) ⟨1087598, by rfl⟩ : syracuseStep 1450131 = 2175197) B2175197
theorem B1450147 : Blo 1449544 1450147 := bstep (se 1 (by rfl) ⟨1087610, by rfl⟩ : syracuseStep 1450147 = 2175221) B2175221
theorem B1450163 : Blo 1449544 1450163 := bstep (se 1 (by rfl) ⟨1087622, by rfl⟩ : syracuseStep 1450163 = 2175245) B2175245
theorem B3670211 : Blo 1449544 3670211 := bstep (se 1 (by rfl) ⟨2752658, by rfl⟩ : syracuseStep 3670211 = 5505317) B5505317
theorem B1450179 : Blo 1449544 1450179 := bstep (se 1 (by rfl) ⟨1087634, by rfl⟩ : syracuseStep 1450179 = 2175269) B2175269
theorem B8372429 : Blo 1449544 8372429 := bstep (se 3 (by rfl) ⟨1569830, by rfl⟩ : syracuseStep 8372429 = 3139661) B3139661
theorem B3096785 : Blo 1449544 3096785 := bstep (se 2 (by rfl) ⟨1161294, by rfl⟩ : syracuseStep 3096785 = 2322589) B2322589
theorem B1450195 : Blo 1449544 1450195 := bstep (se 1 (by rfl) ⟨1087646, by rfl⟩ : syracuseStep 1450195 = 2175293) B2175293
theorem B1450211 : Blo 1449544 1450211 := bstep (se 1 (by rfl) ⟨1087658, by rfl⟩ : syracuseStep 1450211 = 2175317) B2175317
theorem B1450227 : Blo 1449544 1450227 := bstep (se 1 (by rfl) ⟨1087670, by rfl⟩ : syracuseStep 1450227 = 2175341) B2175341
theorem B1450243 : Blo 1449544 1450243 := bstep (se 1 (by rfl) ⟨1087682, by rfl⟩ : syracuseStep 1450243 = 2175365) B2175365
theorem B1548563 : Blo 1449544 1548563 := bstep (se 1 (by rfl) ⟨1161422, by rfl⟩ : syracuseStep 1548563 = 2322845) B2322845
theorem B1450259 : Blo 1449544 1450259 := bstep (se 1 (by rfl) ⟨1087694, by rfl⟩ : syracuseStep 1450259 = 2175389) B2175389
theorem B1450275 : Blo 1449544 1450275 := bstep (se 1 (by rfl) ⟨1087706, by rfl⟩ : syracuseStep 1450275 = 2175413) B2175413
theorem B1450291 : Blo 1449544 1450291 := bstep (se 1 (by rfl) ⟨1087718, by rfl⟩ : syracuseStep 1450291 = 2175437) B2175437
theorem B1450307 : Blo 1449544 1450307 := bstep (se 1 (by rfl) ⟨1087730, by rfl⟩ : syracuseStep 1450307 = 2175461) B2175461
theorem B1450323 : Blo 1449544 1450323 := bstep (se 1 (by rfl) ⟨1087742, by rfl⟩ : syracuseStep 1450323 = 2175485) B2175485
theorem B1450339 : Blo 1449544 1450339 := bstep (se 1 (by rfl) ⟨1087754, by rfl⟩ : syracuseStep 1450339 = 2175509) B2175509
theorem B1450355 : Blo 1449544 1450355 := bstep (se 1 (by rfl) ⟨1087766, by rfl⟩ : syracuseStep 1450355 = 2175533) B2175533
theorem B1450371 : Blo 1449544 1450371 := bstep (se 1 (by rfl) ⟨1087778, by rfl⟩ : syracuseStep 1450371 = 2175557) B2175557
theorem B1450387 : Blo 1449544 1450387 := bstep (se 1 (by rfl) ⟨1087790, by rfl⟩ : syracuseStep 1450387 = 2175581) B2175581
theorem B1450403 : Blo 1449544 1450403 := bstep (se 1 (by rfl) ⟨1087802, by rfl⟩ : syracuseStep 1450403 = 2175605) B2175605
theorem B1450419 : Blo 1449544 1450419 := bstep (se 1 (by rfl) ⟨1087814, by rfl⟩ : syracuseStep 1450419 = 2175629) B2175629
theorem B1450435 : Blo 1449544 1450435 := bstep (se 1 (by rfl) ⟨1087826, by rfl⟩ : syracuseStep 1450435 = 2175653) B2175653
theorem B1450451 : Blo 1449544 1450451 := bstep (se 1 (by rfl) ⟨1087838, by rfl⟩ : syracuseStep 1450451 = 2175677) B2175677
theorem B1450467 : Blo 1449544 1450467 := bstep (se 1 (by rfl) ⟨1087850, by rfl⟩ : syracuseStep 1450467 = 2175701) B2175701
theorem B1450483 : Blo 1449544 1450483 := bstep (se 1 (by rfl) ⟨1087862, by rfl⟩ : syracuseStep 1450483 = 2175725) B2175725
theorem B1450499 : Blo 1449544 1450499 := bstep (se 1 (by rfl) ⟨1087874, by rfl⟩ : syracuseStep 1450499 = 2175749) B2175749
theorem B5227021 : Blo 1449544 5227021 := bstep (se 3 (by rfl) ⟨980066, by rfl⟩ : syracuseStep 5227021 = 1960133) B1960133
theorem B1450515 : Blo 1449544 1450515 := bstep (se 1 (by rfl) ⟨1087886, by rfl⟩ : syracuseStep 1450515 = 2175773) B2175773
theorem B1450531 : Blo 1449544 1450531 := bstep (se 1 (by rfl) ⟨1087898, by rfl⟩ : syracuseStep 1450531 = 2175797) B2175797
theorem B4645421 : Blo 1449544 4645421 := bstep (se 3 (by rfl) ⟨871016, by rfl⟩ : syracuseStep 4645421 = 1742033) B1742033
theorem B1450547 : Blo 1449544 1450547 := bstep (se 1 (by rfl) ⟨1087910, by rfl⟩ : syracuseStep 1450547 = 2175821) B2175821
theorem B2064961 : Blo 1449544 2064961 := bstep (se 2 (by rfl) ⟨774360, by rfl⟩ : syracuseStep 2064961 = 1548721) B1548721
theorem B1450563 : Blo 1449544 1450563 := bstep (se 1 (by rfl) ⟨1087922, by rfl⟩ : syracuseStep 1450563 = 2175845) B2175845
theorem B1450579 : Blo 1449544 1450579 := bstep (se 1 (by rfl) ⟨1087934, by rfl⟩ : syracuseStep 1450579 = 2175869) B2175869
theorem B1450595 : Blo 1449544 1450595 := bstep (se 1 (by rfl) ⟨1087946, by rfl⟩ : syracuseStep 1450595 = 2175893) B2175893
theorem B1450611 : Blo 1449544 1450611 := bstep (se 1 (by rfl) ⟨1087958, by rfl⟩ : syracuseStep 1450611 = 2175917) B2175917
theorem B1450627 : Blo 1449544 1450627 := bstep (se 1 (by rfl) ⟨1087970, by rfl⟩ : syracuseStep 1450627 = 2175941) B2175941
theorem B13075085 : Blo 1449544 13075085 := bstep (se 3 (by rfl) ⟨2451578, by rfl⟩ : syracuseStep 13075085 = 4903157) B4903157
theorem B1630867 : Blo 1449544 1630867 := bstep (se 1 (by rfl) ⟨1223150, by rfl⟩ : syracuseStep 1630867 = 2446301) B2446301
theorem B1450643 : Blo 1449544 1450643 := bstep (se 1 (by rfl) ⟨1087982, by rfl⟩ : syracuseStep 1450643 = 2175965) B2175965
theorem B1450659 : Blo 1449544 1450659 := bstep (se 1 (by rfl) ⟨1087994, by rfl⟩ : syracuseStep 1450659 = 2175989) B2175989
theorem B3719857 : Blo 1449544 3719857 := bstep (se 2 (by rfl) ⟨1394946, by rfl⟩ : syracuseStep 3719857 = 2789893) B2789893
theorem B1450675 : Blo 1449544 1450675 := bstep (se 1 (by rfl) ⟨1088006, by rfl⟩ : syracuseStep 1450675 = 2176013) B2176013
theorem B1450691 : Blo 1449544 1450691 := bstep (se 1 (by rfl) ⟨1088018, by rfl⟩ : syracuseStep 1450691 = 2176037) B2176037
theorem B1450707 : Blo 1449544 1450707 := bstep (se 1 (by rfl) ⟨1088030, by rfl⟩ : syracuseStep 1450707 = 2176061) B2176061
theorem B1450723 : Blo 1449544 1450723 := bstep (se 1 (by rfl) ⟨1088042, by rfl⟩ : syracuseStep 1450723 = 2176085) B2176085
theorem B1450739 : Blo 1449544 1450739 := bstep (se 1 (by rfl) ⟨1088054, by rfl⟩ : syracuseStep 1450739 = 2176109) B2176109
theorem B1835779 : Blo 1449544 1835779 := bstep (se 1 (by rfl) ⟨1376834, by rfl⟩ : syracuseStep 1835779 = 2753669) B2753669
theorem B1450755 : Blo 1449544 1450755 := bstep (se 1 (by rfl) ⟨1088066, by rfl⟩ : syracuseStep 1450755 = 2176133) B2176133
theorem B17646349 : Blo 1449544 17646349 := bstep (se 3 (by rfl) ⟨3308690, by rfl⟩ : syracuseStep 17646349 = 6617381) B6617381
theorem B1450771 : Blo 1449544 1450771 := bstep (se 1 (by rfl) ⟨1088078, by rfl⟩ : syracuseStep 1450771 = 2176157) B2176157
theorem B1631011 : Blo 1449544 1631011 := bstep (se 1 (by rfl) ⟨1223258, by rfl⟩ : syracuseStep 1631011 = 2446517) B2446517
theorem B1450787 : Blo 1449544 1450787 := bstep (se 1 (by rfl) ⟨1088090, by rfl⟩ : syracuseStep 1450787 = 2176181) B2176181
theorem B1450803 : Blo 1449544 1450803 := bstep (se 1 (by rfl) ⟨1088102, by rfl⟩ : syracuseStep 1450803 = 2176205) B2176205
theorem B1450819 : Blo 1449544 1450819 := bstep (se 1 (by rfl) ⟨1088114, by rfl⟩ : syracuseStep 1450819 = 2176229) B2176229
theorem B11019077 : Blo 1449544 11019077 := bstep (se 4 (by rfl) ⟨1033038, by rfl⟩ : syracuseStep 11019077 = 2066077) B2066077
theorem B1450835 : Blo 1449544 1450835 := bstep (se 1 (by rfl) ⟨1088126, by rfl⟩ : syracuseStep 1450835 = 2176253) B2176253
theorem B1835875 : Blo 1449544 1835875 := bstep (se 1 (by rfl) ⟨1376906, by rfl⟩ : syracuseStep 1835875 = 2753813) B2753813
theorem B1450851 : Blo 1449544 1450851 := bstep (se 1 (by rfl) ⟨1088138, by rfl⟩ : syracuseStep 1450851 = 2176277) B2176277
theorem B4129649 : Blo 1449544 4129649 := bstep (se 2 (by rfl) ⟨1548618, by rfl⟩ : syracuseStep 4129649 = 3097237) B3097237
theorem B1450867 : Blo 1449544 1450867 := bstep (se 1 (by rfl) ⟨1088150, by rfl⟩ : syracuseStep 1450867 = 2176301) B2176301
theorem B1450883 : Blo 1449544 1450883 := bstep (se 1 (by rfl) ⟨1088162, by rfl⟩ : syracuseStep 1450883 = 2176325) B2176325
theorem B1450899 : Blo 1449544 1450899 := bstep (se 1 (by rfl) ⟨1088174, by rfl⟩ : syracuseStep 1450899 = 2176349) B2176349
theorem B1450915 : Blo 1449544 1450915 := bstep (se 1 (by rfl) ⟨1088186, by rfl⟩ : syracuseStep 1450915 = 2176373) B2176373
theorem B1631155 : Blo 1449544 1631155 := bstep (se 1 (by rfl) ⟨1223366, by rfl⟩ : syracuseStep 1631155 = 2446733) B2446733
theorem B1450931 : Blo 1449544 1450931 := bstep (se 1 (by rfl) ⟨1088198, by rfl⟩ : syracuseStep 1450931 = 2176397) B2176397
theorem B1450947 : Blo 1449544 1450947 := bstep (se 1 (by rfl) ⟨1088210, by rfl⟩ : syracuseStep 1450947 = 2176421) B2176421
theorem B19104709 : Blo 1449544 19104709 := bstep (se 4 (by rfl) ⟨1791066, by rfl⟩ : syracuseStep 19104709 = 3582133) B3582133
theorem B1450963 : Blo 1449544 1450963 := bstep (se 1 (by rfl) ⟨1088222, by rfl⟩ : syracuseStep 1450963 = 2176445) B2176445
theorem B1450979 : Blo 1449544 1450979 := bstep (se 1 (by rfl) ⟨1088234, by rfl⟩ : syracuseStep 1450979 = 2176469) B2176469
theorem B1450995 : Blo 1449544 1450995 := bstep (se 1 (by rfl) ⟨1088246, by rfl⟩ : syracuseStep 1450995 = 2176493) B2176493
theorem B1549315 : Blo 1449544 1549315 := bstep (se 1 (by rfl) ⟨1161986, by rfl⟩ : syracuseStep 1549315 = 2323973) B2323973
theorem B1451011 : Blo 1449544 1451011 := bstep (se 1 (by rfl) ⟨1088258, by rfl⟩ : syracuseStep 1451011 = 2176517) B2176517
theorem B1451027 : Blo 1449544 1451027 := bstep (se 1 (by rfl) ⟨1088270, by rfl⟩ : syracuseStep 1451027 = 2176541) B2176541
theorem B1451043 : Blo 1449544 1451043 := bstep (se 1 (by rfl) ⟨1088282, by rfl⟩ : syracuseStep 1451043 = 2176565) B2176565
theorem B2753585 : Blo 1449544 2753585 := bstep (se 2 (by rfl) ⟨1032594, by rfl⟩ : syracuseStep 2753585 = 2065189) B2065189
theorem B1451059 : Blo 1449544 1451059 := bstep (se 1 (by rfl) ⟨1088294, by rfl⟩ : syracuseStep 1451059 = 2176589) B2176589
theorem B1631299 : Blo 1449544 1631299 := bstep (se 1 (by rfl) ⟨1223474, by rfl⟩ : syracuseStep 1631299 = 2446949) B2446949
theorem B1451075 : Blo 1449544 1451075 := bstep (se 1 (by rfl) ⟨1088306, by rfl⟩ : syracuseStep 1451075 = 2176613) B2176613
theorem B1451091 : Blo 1449544 1451091 := bstep (se 1 (by rfl) ⟨1088318, by rfl⟩ : syracuseStep 1451091 = 2176637) B2176637
theorem B1451107 : Blo 1449544 1451107 := bstep (se 1 (by rfl) ⟨1088330, by rfl⟩ : syracuseStep 1451107 = 2176661) B2176661
theorem B3671153 : Blo 1449544 3671153 := bstep (se 2 (by rfl) ⟨1376682, by rfl⟩ : syracuseStep 3671153 = 2753365) B2753365
theorem B1451123 : Blo 1449544 1451123 := bstep (se 1 (by rfl) ⟨1088342, by rfl⟩ : syracuseStep 1451123 = 2176685) B2176685
theorem B1451139 : Blo 1449544 1451139 := bstep (se 1 (by rfl) ⟨1088354, by rfl⟩ : syracuseStep 1451139 = 2176709) B2176709
theorem B1451155 : Blo 1449544 1451155 := bstep (se 1 (by rfl) ⟨1088366, by rfl⟩ : syracuseStep 1451155 = 2176733) B2176733
theorem B3671203 : Blo 1449544 3671203 := bstep (se 1 (by rfl) ⟨2753402, by rfl⟩ : syracuseStep 3671203 = 5506805) B5506805
theorem B1451171 : Blo 1449544 1451171 := bstep (se 1 (by rfl) ⟨1088378, by rfl⟩ : syracuseStep 1451171 = 2176757) B2176757
theorem B3261617 : Blo 1449544 3261617 := bstep (se 2 (by rfl) ⟨1223106, by rfl⟩ : syracuseStep 3261617 = 2446213) B2446213
theorem B1451187 : Blo 1449544 1451187 := bstep (se 1 (by rfl) ⟨1088390, by rfl⟩ : syracuseStep 1451187 = 2176781) B2176781
theorem B2942129 : Blo 1449544 2942129 := bstep (se 2 (by rfl) ⟨1103298, by rfl⟩ : syracuseStep 2942129 = 2206597) B2206597
theorem B3261635 : Blo 1449544 3261635 := bstep (se 1 (by rfl) ⟨2446226, by rfl⟩ : syracuseStep 3261635 = 4892453) B4892453
theorem B1451203 : Blo 1449544 1451203 := bstep (se 1 (by rfl) ⟨1088402, by rfl⟩ : syracuseStep 1451203 = 2176805) B2176805
theorem B1631443 : Blo 1449544 1631443 := bstep (se 1 (by rfl) ⟨1223582, by rfl⟩ : syracuseStep 1631443 = 2447165) B2447165
theorem B1451219 : Blo 1449544 1451219 := bstep (se 1 (by rfl) ⟨1088414, by rfl⟩ : syracuseStep 1451219 = 2176829) B2176829
theorem B1451235 : Blo 1449544 1451235 := bstep (se 1 (by rfl) ⟨1088426, by rfl⟩ : syracuseStep 1451235 = 2176853) B2176853
theorem B5506289 : Blo 1449544 5506289 := bstep (se 2 (by rfl) ⟨2064858, by rfl⟩ : syracuseStep 5506289 = 4129717) B4129717
theorem B1451251 : Blo 1449544 1451251 := bstep (se 1 (by rfl) ⟨1088438, by rfl⟩ : syracuseStep 1451251 = 2176877) B2176877
theorem B2065667 : Blo 1449544 2065667 := bstep (se 1 (by rfl) ⟨1549250, by rfl⟩ : syracuseStep 2065667 = 3098501) B3098501
theorem B1451267 : Blo 1449544 1451267 := bstep (se 1 (by rfl) ⟨1088450, by rfl⟩ : syracuseStep 1451267 = 2176901) B2176901
theorem B1451283 : Blo 1449544 1451283 := bstep (se 1 (by rfl) ⟨1088462, by rfl⟩ : syracuseStep 1451283 = 2176925) B2176925
theorem B1451299 : Blo 1449544 1451299 := bstep (se 1 (by rfl) ⟨1088474, by rfl⟩ : syracuseStep 1451299 = 2176949) B2176949
theorem B3671345 : Blo 1449544 3671345 := bstep (se 2 (by rfl) ⟨1376754, by rfl⟩ : syracuseStep 3671345 = 2753509) B2753509
theorem B1451315 : Blo 1449544 1451315 := bstep (se 1 (by rfl) ⟨1088486, by rfl⟩ : syracuseStep 1451315 = 2176973) B2176973
theorem B1451331 : Blo 1449544 1451331 := bstep (se 1 (by rfl) ⟨1088498, by rfl⟩ : syracuseStep 1451331 = 2176997) B2176997
theorem B1836371 : Blo 1449544 1836371 := bstep (se 1 (by rfl) ⟨1377278, by rfl⟩ : syracuseStep 1836371 = 2754557) B2754557
theorem B1451347 : Blo 1449544 1451347 := bstep (se 1 (by rfl) ⟨1088510, by rfl⟩ : syracuseStep 1451347 = 2177021) B2177021
theorem B1631587 : Blo 1449544 1631587 := bstep (se 1 (by rfl) ⟨1223690, by rfl⟩ : syracuseStep 1631587 = 2447381) B2447381
theorem B1451363 : Blo 1449544 1451363 := bstep (se 1 (by rfl) ⟨1088522, by rfl⟩ : syracuseStep 1451363 = 2177045) B2177045
theorem B19850609 : Blo 1449544 19850609 := bstep (se 2 (by rfl) ⟨7443978, by rfl⟩ : syracuseStep 19850609 = 14887957) B14887957
theorem B1451379 : Blo 1449544 1451379 := bstep (se 1 (by rfl) ⟨1088534, by rfl⟩ : syracuseStep 1451379 = 2177069) B2177069
theorem B1451395 : Blo 1449544 1451395 := bstep (se 1 (by rfl) ⟨1088546, by rfl⟩ : syracuseStep 1451395 = 2177093) B2177093
theorem B1451411 : Blo 1449544 1451411 := bstep (se 1 (by rfl) ⟨1088558, by rfl⟩ : syracuseStep 1451411 = 2177117) B2177117
theorem B1451427 : Blo 1449544 1451427 := bstep (se 1 (by rfl) ⟨1088570, by rfl⟩ : syracuseStep 1451427 = 2177141) B2177141
theorem B1451443 : Blo 1449544 1451443 := bstep (se 1 (by rfl) ⟨1088582, by rfl⟩ : syracuseStep 1451443 = 2177165) B2177165
theorem B1451459 : Blo 1449544 1451459 := bstep (se 1 (by rfl) ⟨1088594, by rfl⟩ : syracuseStep 1451459 = 2177189) B2177189
theorem B3261905 : Blo 1449544 3261905 := bstep (se 2 (by rfl) ⟨1223214, by rfl⟩ : syracuseStep 3261905 = 2446429) B2446429
theorem B2205137 : Blo 1449544 2205137 := bstep (se 2 (by rfl) ⟨826926, by rfl⟩ : syracuseStep 2205137 = 1653853) B1653853
theorem B1451475 : Blo 1449544 1451475 := bstep (se 1 (by rfl) ⟨1088606, by rfl⟩ : syracuseStep 1451475 = 2177213) B2177213
theorem B3261923 : Blo 1449544 3261923 := bstep (se 1 (by rfl) ⟨2446442, by rfl⟩ : syracuseStep 3261923 = 4892885) B4892885
theorem B3098083 : Blo 1449544 3098083 := bstep (se 1 (by rfl) ⟨2323562, by rfl⟩ : syracuseStep 3098083 = 4647125) B4647125
theorem B1451491 : Blo 1449544 1451491 := bstep (se 1 (by rfl) ⟨1088618, by rfl⟩ : syracuseStep 1451491 = 2177237) B2177237
theorem B1631731 : Blo 1449544 1631731 := bstep (se 1 (by rfl) ⟨1223798, by rfl⟩ : syracuseStep 1631731 = 2447597) B2447597
theorem B1451507 : Blo 1449544 1451507 := bstep (se 1 (by rfl) ⟨1088630, by rfl⟩ : syracuseStep 1451507 = 2177261) B2177261
theorem B1451523 : Blo 1449544 1451523 := bstep (se 1 (by rfl) ⟨1088642, by rfl⟩ : syracuseStep 1451523 = 2177285) B2177285
theorem B1451539 : Blo 1449544 1451539 := bstep (se 1 (by rfl) ⟨1088654, by rfl⟩ : syracuseStep 1451539 = 2177309) B2177309
theorem B4892237 : Blo 1449544 4892237 := bstep (se 3 (by rfl) ⟨917294, by rfl⟩ : syracuseStep 4892237 = 1834589) B1834589
theorem B4892291 : Blo 1449544 4892291 := bstep (se 1 (by rfl) ⟨3669218, by rfl⟩ : syracuseStep 4892291 = 7338437) B7338437
theorem B1631875 : Blo 1449544 1631875 := bstep (se 1 (by rfl) ⟨1223906, by rfl⟩ : syracuseStep 1631875 = 2447813) B2447813
theorem B8259205 : Blo 1449544 8259205 := bstep (se 4 (by rfl) ⟨774300, by rfl⟩ : syracuseStep 8259205 = 1548601) B1548601
theorem B4187821 : Blo 1449544 4187821 := bstep (se 3 (by rfl) ⟨785216, by rfl⟩ : syracuseStep 4187821 = 1570433) B1570433
theorem B3262193 : Blo 1449544 3262193 := bstep (se 2 (by rfl) ⟨1223322, by rfl⟩ : syracuseStep 3262193 = 2446645) B2446645
theorem B3262211 : Blo 1449544 3262211 := bstep (se 1 (by rfl) ⟨2446658, by rfl⟩ : syracuseStep 3262211 = 4893317) B4893317
theorem B1632019 : Blo 1449544 1632019 := bstep (se 1 (by rfl) ⟨1224014, by rfl⟩ : syracuseStep 1632019 = 2448029) B2448029
theorem B4130605 : Blo 1449544 4130605 := bstep (se 3 (by rfl) ⟨774488, by rfl⟩ : syracuseStep 4130605 = 1548977) B1548977
theorem B2066305 : Blo 1449544 2066305 := bstep (se 2 (by rfl) ⟨774864, by rfl⟩ : syracuseStep 2066305 = 1549729) B1549729
theorem B4892561 : Blo 1449544 4892561 := bstep (se 2 (by rfl) ⟨1834710, by rfl⟩ : syracuseStep 4892561 = 3669421) B3669421
theorem B1632163 : Blo 1449544 1632163 := bstep (se 1 (by rfl) ⟨1224122, by rfl⟩ : syracuseStep 1632163 = 2448245) B2448245
theorem B7342001 : Blo 1449544 7342001 := bstep (se 2 (by rfl) ⟨2753250, by rfl⟩ : syracuseStep 7342001 = 5506501) B5506501
theorem B2754481 : Blo 1449544 2754481 := bstep (se 2 (by rfl) ⟨1032930, by rfl⟩ : syracuseStep 2754481 = 2065861) B2065861
theorem B2205667 : Blo 1449544 2205667 := bstep (se 1 (by rfl) ⟨1654250, by rfl⟩ : syracuseStep 2205667 = 3308501) B3308501
theorem B2066419 : Blo 1449544 2066419 := bstep (se 1 (by rfl) ⟨1549814, by rfl⟩ : syracuseStep 2066419 = 3099629) B3099629
theorem B11167757 : Blo 1449544 11167757 := bstep (se 3 (by rfl) ⟨2093954, by rfl⟩ : syracuseStep 11167757 = 4187909) B4187909
theorem B3262481 : Blo 1449544 3262481 := bstep (se 2 (by rfl) ⟨1223430, by rfl⟩ : syracuseStep 3262481 = 2446861) B2446861
theorem B2721809 : Blo 1449544 2721809 := bstep (se 2 (by rfl) ⟨1020678, by rfl⟩ : syracuseStep 2721809 = 2041357) B2041357
theorem B4130833 : Blo 1449544 4130833 := bstep (se 2 (by rfl) ⟨1549062, by rfl⟩ : syracuseStep 4130833 = 3098125) B3098125
theorem B1837075 : Blo 1449544 1837075 := bstep (se 1 (by rfl) ⟨1377806, by rfl⟩ : syracuseStep 1837075 = 2755613) B2755613
theorem B3262499 : Blo 1449544 3262499 := bstep (se 1 (by rfl) ⟨2446874, by rfl⟩ : syracuseStep 3262499 = 4893749) B4893749
theorem B1632307 : Blo 1449544 1632307 := bstep (se 1 (by rfl) ⟨1224230, by rfl⟩ : syracuseStep 1632307 = 2448461) B2448461
theorem B2754641 : Blo 1449544 2754641 := bstep (se 2 (by rfl) ⟨1032990, by rfl⟩ : syracuseStep 2754641 = 2065981) B2065981
theorem B5228707 : Blo 1449544 5228707 := bstep (se 1 (by rfl) ⟨3921530, by rfl⟩ : syracuseStep 5228707 = 7843061) B7843061
theorem B4130993 : Blo 1449544 4130993 := bstep (se 2 (by rfl) ⟨1549122, by rfl⟩ : syracuseStep 4130993 = 3098245) B3098245
theorem B1632451 : Blo 1449544 1632451 := bstep (se 1 (by rfl) ⟨1224338, by rfl⟩ : syracuseStep 1632451 = 2448677) B2448677
theorem B3672337 : Blo 1449544 3672337 := bstep (se 2 (by rfl) ⟨1377126, by rfl⟩ : syracuseStep 3672337 = 2754253) B2754253
theorem B4131107 : Blo 1449544 4131107 := bstep (se 1 (by rfl) ⟨3098330, by rfl⟩ : syracuseStep 4131107 = 6196661) B6196661
theorem B3262769 : Blo 1449544 3262769 := bstep (se 2 (by rfl) ⟨1223538, by rfl⟩ : syracuseStep 3262769 = 2447077) B2447077
theorem B3262787 : Blo 1449544 3262787 := bstep (se 1 (by rfl) ⟨2447090, by rfl⟩ : syracuseStep 3262787 = 4894181) B4894181
theorem B1632595 : Blo 1449544 1632595 := bstep (se 1 (by rfl) ⟨1224446, by rfl⟩ : syracuseStep 1632595 = 2448893) B2448893
theorem B5581169 : Blo 1449544 5581169 := bstep (se 2 (by rfl) ⟨2092938, by rfl⟩ : syracuseStep 5581169 = 4185877) B4185877
theorem B4893101 : Blo 1449544 4893101 := bstep (se 3 (by rfl) ⟨917456, by rfl⟩ : syracuseStep 4893101 = 1834913) B1834913
theorem B4647341 : Blo 1449544 4647341 := bstep (se 3 (by rfl) ⟨871376, by rfl⟩ : syracuseStep 4647341 = 1742753) B1742753
theorem B4893155 : Blo 1449544 4893155 := bstep (se 1 (by rfl) ⟨3669866, by rfl⟩ : syracuseStep 4893155 = 7339733) B7339733
theorem B2755043 : Blo 1449544 2755043 := bstep (se 1 (by rfl) ⟨2066282, by rfl⟩ : syracuseStep 2755043 = 4132565) B4132565
theorem B1632739 : Blo 1449544 1632739 := bstep (se 1 (by rfl) ⟨1224554, by rfl⟩ : syracuseStep 1632739 = 2449109) B2449109
theorem B14125553 : Blo 1449544 14125553 := bstep (se 2 (by rfl) ⟨5297082, by rfl⟩ : syracuseStep 14125553 = 10594165) B10594165
theorem B3672611 : Blo 1449544 3672611 := bstep (se 1 (by rfl) ⟨2754458, by rfl⟩ : syracuseStep 3672611 = 5508917) B5508917
theorem B3263057 : Blo 1449544 3263057 := bstep (se 2 (by rfl) ⟨1223646, by rfl⟩ : syracuseStep 3263057 = 2447293) B2447293
theorem B3263075 : Blo 1449544 3263075 := bstep (se 1 (by rfl) ⟨2447306, by rfl⟩ : syracuseStep 3263075 = 4894613) B4894613
theorem B1632883 : Blo 1449544 1632883 := bstep (se 1 (by rfl) ⟨1224662, by rfl⟩ : syracuseStep 1632883 = 2449325) B2449325
theorem B5507747 : Blo 1449544 5507747 := bstep (se 1 (by rfl) ⟨4130810, by rfl⟩ : syracuseStep 5507747 = 8261621) B8261621
theorem B3099313 : Blo 1449544 3099313 := bstep (se 2 (by rfl) ⟨1162242, by rfl⟩ : syracuseStep 3099313 = 2324485) B2324485
theorem B3672803 : Blo 1449544 3672803 := bstep (se 1 (by rfl) ⟨2754602, by rfl⟩ : syracuseStep 3672803 = 5509205) B5509205
theorem B12397283 : Blo 1449544 12397283 := bstep (se 1 (by rfl) ⟨9297962, by rfl⟩ : syracuseStep 12397283 = 18595925) B18595925
theorem B4893425 : Blo 1449544 4893425 := bstep (se 2 (by rfl) ⟨1835034, by rfl⟩ : syracuseStep 4893425 = 3670069) B3670069
theorem B1960723 : Blo 1449544 1960723 := bstep (se 1 (by rfl) ⟨1470542, by rfl⟩ : syracuseStep 1960723 = 2941085) B2941085
theorem B3353393 : Blo 1449544 3353393 := bstep (se 2 (by rfl) ⟨1257522, by rfl⟩ : syracuseStep 3353393 = 2515045) B2515045
theorem B12389219 : Blo 1449544 12389219 := bstep (se 1 (by rfl) ⟨9291914, by rfl⟩ : syracuseStep 12389219 = 18583829) B18583829
theorem B3263345 : Blo 1449544 3263345 := bstep (se 2 (by rfl) ⟨1223754, by rfl⟩ : syracuseStep 3263345 = 2447509) B2447509
theorem B3263363 : Blo 1449544 3263363 := bstep (se 1 (by rfl) ⟨2447522, by rfl⟩ : syracuseStep 3263363 = 4895045) B4895045
theorem B4959149 : Blo 1449544 4959149 := bstep (se 3 (by rfl) ⟨929840, by rfl⟩ : syracuseStep 4959149 = 1859681) B1859681
theorem B8817677 : Blo 1449544 8817677 := bstep (se 3 (by rfl) ⟨1653314, by rfl⟩ : syracuseStep 8817677 = 3306629) B3306629
theorem B3722257 : Blo 1449544 3722257 := bstep (se 2 (by rfl) ⟨1395846, by rfl⟩ : syracuseStep 3722257 = 2791693) B2791693
theorem B1592371 : Blo 1449544 1592371 := bstep (se 1 (by rfl) ⟨1194278, by rfl⟩ : syracuseStep 1592371 = 2388557) B2388557
theorem B10595441 : Blo 1449544 10595441 := bstep (se 2 (by rfl) ⟨3973290, by rfl⟩ : syracuseStep 10595441 = 7946581) B7946581
theorem B3263633 : Blo 1449544 3263633 := bstep (se 2 (by rfl) ⟨1223862, by rfl⟩ : syracuseStep 3263633 = 2447725) B2447725
theorem B3263651 : Blo 1449544 3263651 := bstep (se 1 (by rfl) ⟨2447738, by rfl⟩ : syracuseStep 3263651 = 4895477) B4895477
theorem B3533987 : Blo 1449544 3533987 := bstep (se 1 (by rfl) ⟨2650490, by rfl⟩ : syracuseStep 3533987 = 5300981) B5300981
theorem B4893965 : Blo 1449544 4893965 := bstep (se 3 (by rfl) ⟨917618, by rfl⟩ : syracuseStep 4893965 = 1835237) B1835237
theorem B4132109 : Blo 1449544 4132109 := bstep (se 3 (by rfl) ⟨774770, by rfl⟩ : syracuseStep 4132109 = 1549541) B1549541
theorem B4894019 : Blo 1449544 4894019 := bstep (se 1 (by rfl) ⟨3670514, by rfl⟩ : syracuseStep 4894019 = 7341029) B7341029
theorem B3099971 : Blo 1449544 3099971 := bstep (se 1 (by rfl) ⟨2324978, by rfl⟩ : syracuseStep 3099971 = 4649957) B4649957
theorem B7343459 : Blo 1449544 7343459 := bstep (se 1 (by rfl) ⟨5507594, by rfl⟩ : syracuseStep 7343459 = 11015189) B11015189
theorem B2174321 : Blo 1449544 2174321 := bstep (se 2 (by rfl) ⟨815370, by rfl⟩ : syracuseStep 2174321 = 1630741) B1630741
theorem B2174339 : Blo 1449544 2174339 := bstep (se 1 (by rfl) ⟨1630754, by rfl⟩ : syracuseStep 2174339 = 3261509) B3261509
theorem B8826245 : Blo 1449544 8826245 := bstep (se 4 (by rfl) ⟨827460, by rfl⟩ : syracuseStep 8826245 = 1654921) B1654921
theorem B2174369 : Blo 1449544 2174369 := bstep (se 2 (by rfl) ⟨815388, by rfl⟩ : syracuseStep 2174369 = 1630777) B1630777
theorem B4410787 : Blo 1449544 4410787 := bstep (se 1 (by rfl) ⟨3308090, by rfl⟩ : syracuseStep 4410787 = 6616181) B6616181
theorem B3263921 : Blo 1449544 3263921 := bstep (se 2 (by rfl) ⟨1223970, by rfl⟩ : syracuseStep 3263921 = 2447941) B2447941
theorem B2174387 : Blo 1449544 2174387 := bstep (se 1 (by rfl) ⟨1630790, by rfl⟩ : syracuseStep 2174387 = 3261581) B3261581
theorem B3263939 : Blo 1449544 3263939 := bstep (se 1 (by rfl) ⟨2447954, by rfl⟩ : syracuseStep 3263939 = 4895909) B4895909
theorem B4132291 : Blo 1449544 4132291 := bstep (se 1 (by rfl) ⟨3099218, by rfl⟩ : syracuseStep 4132291 = 6198437) B6198437
theorem B2174417 : Blo 1449544 2174417 := bstep (se 2 (by rfl) ⟨815406, by rfl⟩ : syracuseStep 2174417 = 1630813) B1630813
theorem B2174435 : Blo 1449544 2174435 := bstep (se 1 (by rfl) ⟨1630826, by rfl⟩ : syracuseStep 2174435 = 3261653) B3261653
theorem B2174465 : Blo 1449544 2174465 := bstep (se 2 (by rfl) ⟨815424, by rfl⟩ : syracuseStep 2174465 = 1630849) B1630849
theorem B2174483 : Blo 1449544 2174483 := bstep (se 1 (by rfl) ⟨1630862, by rfl⟩ : syracuseStep 2174483 = 3261725) B3261725
theorem B6975011 : Blo 1449544 6975011 := bstep (se 1 (by rfl) ⟨5231258, by rfl⟩ : syracuseStep 6975011 = 10462517) B10462517
theorem B2174513 : Blo 1449544 2174513 := bstep (se 2 (by rfl) ⟨815442, by rfl⟩ : syracuseStep 2174513 = 1630885) B1630885
theorem B2174531 : Blo 1449544 2174531 := bstep (se 1 (by rfl) ⟨1630898, by rfl⟩ : syracuseStep 2174531 = 3261797) B3261797
theorem B8261189 : Blo 1449544 8261189 := bstep (se 4 (by rfl) ⟨774486, by rfl⟩ : syracuseStep 8261189 = 1548973) B1548973
theorem B4894289 : Blo 1449544 4894289 := bstep (se 2 (by rfl) ⟨1835358, by rfl⟩ : syracuseStep 4894289 = 3670717) B3670717
theorem B2174561 : Blo 1449544 2174561 := bstep (se 2 (by rfl) ⟨815460, by rfl⟩ : syracuseStep 2174561 = 1630921) B1630921
theorem B11013731 : Blo 1449544 11013731 := bstep (se 1 (by rfl) ⟨8260298, by rfl⟩ : syracuseStep 11013731 = 16520597) B16520597
theorem B4132451 : Blo 1449544 4132451 := bstep (se 1 (by rfl) ⟨3099338, by rfl⟩ : syracuseStep 4132451 = 6198677) B6198677
theorem B2174579 : Blo 1449544 2174579 := bstep (se 1 (by rfl) ⟨1630934, by rfl⟩ : syracuseStep 2174579 = 3261869) B3261869
theorem B9293453 : Blo 1449544 9293453 := bstep (se 3 (by rfl) ⟨1742522, by rfl⟩ : syracuseStep 9293453 = 3485045) B3485045
theorem B5508749 : Blo 1449544 5508749 := bstep (se 3 (by rfl) ⟨1032890, by rfl⟩ : syracuseStep 5508749 = 2065781) B2065781
theorem B2174609 : Blo 1449544 2174609 := bstep (se 2 (by rfl) ⟨815478, by rfl⟩ : syracuseStep 2174609 = 1630957) B1630957
theorem B3673745 : Blo 1449544 3673745 := bstep (se 2 (by rfl) ⟨1377654, by rfl⟩ : syracuseStep 3673745 = 2755309) B2755309
theorem B2174627 : Blo 1449544 2174627 := bstep (se 1 (by rfl) ⟨1630970, by rfl⟩ : syracuseStep 2174627 = 3261941) B3261941
theorem B2174657 : Blo 1449544 2174657 := bstep (se 2 (by rfl) ⟨815496, by rfl⟩ : syracuseStep 2174657 = 1630993) B1630993
theorem B3673795 : Blo 1449544 3673795 := bstep (se 1 (by rfl) ⟨2755346, by rfl⟩ : syracuseStep 3673795 = 5510693) B5510693
theorem B3264209 : Blo 1449544 3264209 := bstep (se 2 (by rfl) ⟨1224078, by rfl⟩ : syracuseStep 3264209 = 2448157) B2448157
theorem B2174675 : Blo 1449544 2174675 := bstep (se 1 (by rfl) ⟨1631006, by rfl⟩ : syracuseStep 2174675 = 3262013) B3262013
theorem B3264227 : Blo 1449544 3264227 := bstep (se 1 (by rfl) ⟨2448170, by rfl⟩ : syracuseStep 3264227 = 4896341) B4896341
theorem B2174705 : Blo 1449544 2174705 := bstep (se 2 (by rfl) ⟨815514, by rfl⟩ : syracuseStep 2174705 = 1631029) B1631029
theorem B2264819 : Blo 1449544 2264819 := bstep (se 1 (by rfl) ⟨1698614, by rfl⟩ : syracuseStep 2264819 = 3397229) B3397229
theorem B2322179 : Blo 1449544 2322179 := bstep (se 1 (by rfl) ⟨1741634, by rfl⟩ : syracuseStep 2322179 = 3483269) B3483269
theorem B2174723 : Blo 1449544 2174723 := bstep (se 1 (by rfl) ⟨1631042, by rfl⟩ : syracuseStep 2174723 = 3262085) B3262085
theorem B2174753 : Blo 1449544 2174753 := bstep (se 2 (by rfl) ⟨815532, by rfl⟩ : syracuseStep 2174753 = 1631065) B1631065
theorem B3919661 : Blo 1449544 3919661 := bstep (se 3 (by rfl) ⟨734936, by rfl⟩ : syracuseStep 3919661 = 1469873) B1469873
theorem B2174771 : Blo 1449544 2174771 := bstep (se 1 (by rfl) ⟨1631078, by rfl⟩ : syracuseStep 2174771 = 3262157) B3262157
theorem B2174801 : Blo 1449544 2174801 := bstep (se 2 (by rfl) ⟨815550, by rfl⟩ : syracuseStep 2174801 = 1631101) B1631101
theorem B3673937 : Blo 1449544 3673937 := bstep (se 2 (by rfl) ⟨1377726, by rfl⟩ : syracuseStep 3673937 = 2755453) B2755453
theorem B2174819 : Blo 1449544 2174819 := bstep (se 1 (by rfl) ⟨1631114, by rfl⟩ : syracuseStep 2174819 = 3262229) B3262229
theorem B28266353 : Blo 1449544 28266353 := bstep (se 2 (by rfl) ⟨10599882, by rfl⟩ : syracuseStep 28266353 = 21199765) B21199765
theorem B2174849 : Blo 1449544 2174849 := bstep (se 2 (by rfl) ⟨815568, by rfl⟩ : syracuseStep 2174849 = 1631137) B1631137
theorem B2174867 : Blo 1449544 2174867 := bstep (se 1 (by rfl) ⟨1631150, by rfl⟩ : syracuseStep 2174867 = 3262301) B3262301
theorem B2174897 : Blo 1449544 2174897 := bstep (se 2 (by rfl) ⟨815586, by rfl⟩ : syracuseStep 2174897 = 1631173) B1631173
theorem B2174915 : Blo 1449544 2174915 := bstep (se 1 (by rfl) ⟨1631186, by rfl⟩ : syracuseStep 2174915 = 3262373) B3262373
theorem B2174945 : Blo 1449544 2174945 := bstep (se 2 (by rfl) ⟨815604, by rfl⟩ : syracuseStep 2174945 = 1631209) B1631209
theorem B16519139 : Blo 1449544 16519139 := bstep (se 1 (by rfl) ⟨12389354, by rfl⟩ : syracuseStep 16519139 = 24778709) B24778709
theorem B3264497 : Blo 1449544 3264497 := bstep (se 2 (by rfl) ⟨1224186, by rfl⟩ : syracuseStep 3264497 = 2448373) B2448373
theorem B2174963 : Blo 1449544 2174963 := bstep (se 1 (by rfl) ⟨1631222, by rfl⟩ : syracuseStep 2174963 = 3262445) B3262445
theorem B3264515 : Blo 1449544 3264515 := bstep (se 1 (by rfl) ⟨2448386, by rfl⟩ : syracuseStep 3264515 = 4896773) B4896773
theorem B2174993 : Blo 1449544 2174993 := bstep (se 2 (by rfl) ⟨815622, by rfl⟩ : syracuseStep 2174993 = 1631245) B1631245
theorem B2175011 : Blo 1449544 2175011 := bstep (se 1 (by rfl) ⟨1631258, by rfl⟩ : syracuseStep 2175011 = 3262517) B3262517
theorem B4411441 : Blo 1449544 4411441 := bstep (se 2 (by rfl) ⟨1654290, by rfl⟩ : syracuseStep 4411441 = 3308581) B3308581
theorem B2175041 : Blo 1449544 2175041 := bstep (se 2 (by rfl) ⟨815640, by rfl⟩ : syracuseStep 2175041 = 1631281) B1631281
theorem B2175059 : Blo 1449544 2175059 := bstep (se 1 (by rfl) ⟨1631294, by rfl⟩ : syracuseStep 2175059 = 3262589) B3262589
theorem B4894829 : Blo 1449544 4894829 := bstep (se 3 (by rfl) ⟨917780, by rfl⟩ : syracuseStep 4894829 = 1835561) B1835561
theorem B2175089 : Blo 1449544 2175089 := bstep (se 2 (by rfl) ⟨815658, by rfl⟩ : syracuseStep 2175089 = 1631317) B1631317
theorem B3919985 : Blo 1449544 3919985 := bstep (se 2 (by rfl) ⟨1469994, by rfl⟩ : syracuseStep 3919985 = 2939989) B2939989
theorem B2175107 : Blo 1449544 2175107 := bstep (se 1 (by rfl) ⟨1631330, by rfl⟩ : syracuseStep 2175107 = 3262661) B3262661
theorem B7344269 : Blo 1449544 7344269 := bstep (se 3 (by rfl) ⟨1377050, by rfl⟩ : syracuseStep 7344269 = 2754101) B2754101
theorem B2175137 : Blo 1449544 2175137 := bstep (se 2 (by rfl) ⟨815676, by rfl⟩ : syracuseStep 2175137 = 1631353) B1631353
theorem B4894883 : Blo 1449544 4894883 := bstep (se 1 (by rfl) ⟨3671162, by rfl⟩ : syracuseStep 4894883 = 7342325) B7342325
theorem B6197411 : Blo 1449544 6197411 := bstep (se 1 (by rfl) ⟨4648058, by rfl⟩ : syracuseStep 6197411 = 9296117) B9296117
theorem B2175155 : Blo 1449544 2175155 := bstep (se 1 (by rfl) ⟨1631366, by rfl⟩ : syracuseStep 2175155 = 3262733) B3262733
theorem B3485891 : Blo 1449544 3485891 := bstep (se 1 (by rfl) ⟨2614418, by rfl⟩ : syracuseStep 3485891 = 5228837) B5228837
theorem B2175185 : Blo 1449544 2175185 := bstep (se 2 (by rfl) ⟨815694, by rfl⟩ : syracuseStep 2175185 = 1631389) B1631389
theorem B2175203 : Blo 1449544 2175203 := bstep (se 1 (by rfl) ⟨1631402, by rfl⟩ : syracuseStep 2175203 = 3262805) B3262805
theorem B10449137 : Blo 1449544 10449137 := bstep (se 2 (by rfl) ⟨3918426, by rfl⟩ : syracuseStep 10449137 = 7836853) B7836853
theorem B2175233 : Blo 1449544 2175233 := bstep (se 2 (by rfl) ⟨815712, by rfl⟩ : syracuseStep 2175233 = 1631425) B1631425
theorem B3264785 : Blo 1449544 3264785 := bstep (se 2 (by rfl) ⟨1224294, by rfl⟩ : syracuseStep 3264785 = 2448589) B2448589
theorem B2175251 : Blo 1449544 2175251 := bstep (se 1 (by rfl) ⟨1631438, by rfl⟩ : syracuseStep 2175251 = 3262877) B3262877
theorem B3264803 : Blo 1449544 3264803 := bstep (se 1 (by rfl) ⟨2448602, by rfl⟩ : syracuseStep 3264803 = 4897205) B4897205
theorem B2175281 : Blo 1449544 2175281 := bstep (se 2 (by rfl) ⟨815730, by rfl⟩ : syracuseStep 2175281 = 1631461) B1631461
theorem B2175299 : Blo 1449544 2175299 := bstep (se 1 (by rfl) ⟨1631474, by rfl⟩ : syracuseStep 2175299 = 3262949) B3262949
theorem B2175329 : Blo 1449544 2175329 := bstep (se 2 (by rfl) ⟨815748, by rfl⟩ : syracuseStep 2175329 = 1631497) B1631497
theorem B1765747 : Blo 1449544 1765747 := bstep (se 1 (by rfl) ⟨1324310, by rfl⟩ : syracuseStep 1765747 = 2648621) B2648621
theorem B2175347 : Blo 1449544 2175347 := bstep (se 1 (by rfl) ⟨1631510, by rfl⟩ : syracuseStep 2175347 = 3263021) B3263021
theorem B2175377 : Blo 1449544 2175377 := bstep (se 2 (by rfl) ⟨815766, by rfl⟩ : syracuseStep 2175377 = 1631533) B1631533
theorem B2175395 : Blo 1449544 2175395 := bstep (se 1 (by rfl) ⟨1631546, by rfl⟩ : syracuseStep 2175395 = 3263093) B3263093
theorem B4895153 : Blo 1449544 4895153 := bstep (se 2 (by rfl) ⟨1835682, by rfl⟩ : syracuseStep 4895153 = 3671365) B3671365
theorem B1470899 : Blo 1449544 1470899 := bstep (se 1 (by rfl) ⟨1103174, by rfl⟩ : syracuseStep 1470899 = 2206349) B2206349
theorem B2175425 : Blo 1449544 2175425 := bstep (se 2 (by rfl) ⟨815784, by rfl⟩ : syracuseStep 2175425 = 1631569) B1631569
theorem B2175443 : Blo 1449544 2175443 := bstep (se 1 (by rfl) ⟨1631582, by rfl⟩ : syracuseStep 2175443 = 3263165) B3263165
theorem B2175473 : Blo 1449544 2175473 := bstep (se 2 (by rfl) ⟨815802, by rfl⟩ : syracuseStep 2175473 = 1631605) B1631605
theorem B2175491 : Blo 1449544 2175491 := bstep (se 1 (by rfl) ⟨1631618, by rfl⟩ : syracuseStep 2175491 = 3263237) B3263237
theorem B2175521 : Blo 1449544 2175521 := bstep (se 2 (by rfl) ⟨815820, by rfl⟩ : syracuseStep 2175521 = 1631641) B1631641
theorem B3265073 : Blo 1449544 3265073 := bstep (se 2 (by rfl) ⟨1224402, by rfl⟩ : syracuseStep 3265073 = 2448805) B2448805
theorem B4649521 : Blo 1449544 4649521 := bstep (se 2 (by rfl) ⟨1743570, by rfl⟩ : syracuseStep 4649521 = 3487141) B3487141
theorem B2175539 : Blo 1449544 2175539 := bstep (se 1 (by rfl) ⟨1631654, by rfl⟩ : syracuseStep 2175539 = 3263309) B3263309
theorem B3265091 : Blo 1449544 3265091 := bstep (se 1 (by rfl) ⟨2448818, by rfl⟩ : syracuseStep 3265091 = 4897637) B4897637
theorem B2175569 : Blo 1449544 2175569 := bstep (se 2 (by rfl) ⟨815838, by rfl⟩ : syracuseStep 2175569 = 1631677) B1631677
theorem B2175587 : Blo 1449544 2175587 := bstep (se 1 (by rfl) ⟨1631690, by rfl⟩ : syracuseStep 2175587 = 3263381) B3263381
theorem B7844465 : Blo 1449544 7844465 := bstep (se 2 (by rfl) ⟨2941674, by rfl⟩ : syracuseStep 7844465 = 5883349) B5883349
theorem B2175617 : Blo 1449544 2175617 := bstep (se 2 (by rfl) ⟨815856, by rfl⟩ : syracuseStep 2175617 = 1631713) B1631713
theorem B2175635 : Blo 1449544 2175635 := bstep (se 1 (by rfl) ⟨1631726, by rfl⟩ : syracuseStep 2175635 = 3263453) B3263453
theorem B8164003 : Blo 1449544 8164003 := bstep (se 1 (by rfl) ⟨6123002, by rfl⟩ : syracuseStep 8164003 = 12246005) B12246005
theorem B2175665 : Blo 1449544 2175665 := bstep (se 2 (by rfl) ⟨815874, by rfl⟩ : syracuseStep 2175665 = 1631749) B1631749
theorem B2175683 : Blo 1449544 2175683 := bstep (se 1 (by rfl) ⟨1631762, by rfl⟩ : syracuseStep 2175683 = 3263525) B3263525
theorem B2175713 : Blo 1449544 2175713 := bstep (se 2 (by rfl) ⟨815892, by rfl⟩ : syracuseStep 2175713 = 1631785) B1631785
theorem B2323171 : Blo 1449544 2323171 := bstep (se 1 (by rfl) ⟨1742378, by rfl⟩ : syracuseStep 2323171 = 3484757) B3484757
theorem B4649699 : Blo 1449544 4649699 := bstep (se 1 (by rfl) ⟨3487274, by rfl⟩ : syracuseStep 4649699 = 6974549) B6974549
theorem B2175731 : Blo 1449544 2175731 := bstep (se 1 (by rfl) ⟨1631798, by rfl⟩ : syracuseStep 2175731 = 3263597) B3263597
theorem B2175761 : Blo 1449544 2175761 := bstep (se 2 (by rfl) ⟨815910, by rfl⟩ : syracuseStep 2175761 = 1631821) B1631821
theorem B2175779 : Blo 1449544 2175779 := bstep (se 1 (by rfl) ⟨1631834, by rfl⟩ : syracuseStep 2175779 = 3263669) B3263669
theorem B1741619 : Blo 1449544 1741619 := bstep (se 1 (by rfl) ⟨1306214, by rfl⟩ : syracuseStep 1741619 = 2612429) B2612429
theorem B2175809 : Blo 1449544 2175809 := bstep (se 2 (by rfl) ⟨815928, by rfl⟩ : syracuseStep 2175809 = 1631857) B1631857
theorem B2175827 : Blo 1449544 2175827 := bstep (se 1 (by rfl) ⟨1631870, by rfl⟩ : syracuseStep 2175827 = 3263741) B3263741
theorem B3265361 : Blo 1449544 3265361 := bstep (se 2 (by rfl) ⟨1224510, by rfl⟩ : syracuseStep 3265361 = 2449021) B2449021
theorem B3265379 : Blo 1449544 3265379 := bstep (se 1 (by rfl) ⟨2449034, by rfl⟩ : syracuseStep 3265379 = 4898069) B4898069
theorem B2446193 : Blo 1449544 2446193 := bstep (se 2 (by rfl) ⟨917322, by rfl⟩ : syracuseStep 2446193 = 1834645) B1834645
theorem B2175857 : Blo 1449544 2175857 := bstep (se 2 (by rfl) ⟨815946, by rfl⟩ : syracuseStep 2175857 = 1631893) B1631893
theorem B2175875 : Blo 1449544 2175875 := bstep (se 1 (by rfl) ⟨1631906, by rfl⟩ : syracuseStep 2175875 = 3263813) B3263813
theorem B2175905 : Blo 1449544 2175905 := bstep (se 2 (by rfl) ⟨815964, by rfl⟩ : syracuseStep 2175905 = 1631929) B1631929
theorem B6968227 : Blo 1449544 6968227 := bstep (se 1 (by rfl) ⟨5226170, by rfl⟩ : syracuseStep 6968227 = 10452341) B10452341
theorem B2175923 : Blo 1449544 2175923 := bstep (se 1 (by rfl) ⟨1631942, by rfl⟩ : syracuseStep 2175923 = 3263885) B3263885
theorem B3486659 : Blo 1449544 3486659 := bstep (se 1 (by rfl) ⟨2614994, by rfl⟩ : syracuseStep 3486659 = 5229989) B5229989
theorem B4895693 : Blo 1449544 4895693 := bstep (se 3 (by rfl) ⟨917942, by rfl⟩ : syracuseStep 4895693 = 1835885) B1835885
theorem B2175953 : Blo 1449544 2175953 := bstep (se 2 (by rfl) ⟨815982, by rfl⟩ : syracuseStep 2175953 = 1631965) B1631965
theorem B2175971 : Blo 1449544 2175971 := bstep (se 1 (by rfl) ⟨1631978, by rfl⟩ : syracuseStep 2175971 = 3263957) B3263957
theorem B2446321 : Blo 1449544 2446321 := bstep (se 2 (by rfl) ⟨917370, by rfl⟩ : syracuseStep 2446321 = 1834741) B1834741
theorem B2176001 : Blo 1449544 2176001 := bstep (se 2 (by rfl) ⟨816000, by rfl⟩ : syracuseStep 2176001 = 1632001) B1632001
theorem B4895747 : Blo 1449544 4895747 := bstep (se 1 (by rfl) ⟨3671810, by rfl⟩ : syracuseStep 4895747 = 7343621) B7343621
theorem B2446355 : Blo 1449544 2446355 := bstep (se 1 (by rfl) ⟨1834766, by rfl⟩ : syracuseStep 2446355 = 3669533) B3669533
theorem B2176019 : Blo 1449544 2176019 := bstep (se 1 (by rfl) ⟨1632014, by rfl⟩ : syracuseStep 2176019 = 3264029) B3264029
theorem B2176049 : Blo 1449544 2176049 := bstep (se 2 (by rfl) ⟨816018, by rfl⟩ : syracuseStep 2176049 = 1632037) B1632037
theorem B2176067 : Blo 1449544 2176067 := bstep (se 1 (by rfl) ⟨1632050, by rfl⟩ : syracuseStep 2176067 = 3264101) B3264101
theorem B2176097 : Blo 1449544 2176097 := bstep (se 2 (by rfl) ⟨816036, by rfl⟩ : syracuseStep 2176097 = 1632073) B1632073
theorem B3265649 : Blo 1449544 3265649 := bstep (se 2 (by rfl) ⟨1224618, by rfl⟩ : syracuseStep 3265649 = 2449237) B2449237
theorem B2176115 : Blo 1449544 2176115 := bstep (se 1 (by rfl) ⟨1632086, by rfl⟩ : syracuseStep 2176115 = 3264173) B3264173
theorem B3265667 : Blo 1449544 3265667 := bstep (se 1 (by rfl) ⟨2449250, by rfl⟩ : syracuseStep 3265667 = 4898501) B4898501
theorem B2176145 : Blo 1449544 2176145 := bstep (se 2 (by rfl) ⟨816054, by rfl⟩ : syracuseStep 2176145 = 1632109) B1632109
theorem B2446483 : Blo 1449544 2446483 := bstep (se 1 (by rfl) ⟨1834862, by rfl⟩ : syracuseStep 2446483 = 3669725) B3669725
theorem B2176163 : Blo 1449544 2176163 := bstep (se 1 (by rfl) ⟨1632122, by rfl⟩ : syracuseStep 2176163 = 3264245) B3264245
theorem B2176193 : Blo 1449544 2176193 := bstep (se 2 (by rfl) ⟨816072, by rfl⟩ : syracuseStep 2176193 = 1632145) B1632145
theorem B2176211 : Blo 1449544 2176211 := bstep (se 1 (by rfl) ⟨1632158, by rfl⟩ : syracuseStep 2176211 = 3264317) B3264317
theorem B2176241 : Blo 1449544 2176241 := bstep (se 2 (by rfl) ⟨816090, by rfl⟩ : syracuseStep 2176241 = 1632181) B1632181
theorem B2176259 : Blo 1449544 2176259 := bstep (se 1 (by rfl) ⟨1632194, by rfl⟩ : syracuseStep 2176259 = 3264389) B3264389
theorem B4896017 : Blo 1449544 4896017 := bstep (se 2 (by rfl) ⟨1836006, by rfl⟩ : syracuseStep 4896017 = 3672013) B3672013
theorem B2446625 : Blo 1449544 2446625 := bstep (se 2 (by rfl) ⟨917484, by rfl⟩ : syracuseStep 2446625 = 1834969) B1834969
theorem B2176289 : Blo 1449544 2176289 := bstep (se 2 (by rfl) ⟨816108, by rfl⟩ : syracuseStep 2176289 = 1632217) B1632217
theorem B2176307 : Blo 1449544 2176307 := bstep (se 1 (by rfl) ⟨1632230, by rfl⟩ : syracuseStep 2176307 = 3264461) B3264461
theorem B2176337 : Blo 1449544 2176337 := bstep (se 2 (by rfl) ⟨816126, by rfl⟩ : syracuseStep 2176337 = 1632253) B1632253
theorem B2176355 : Blo 1449544 2176355 := bstep (se 1 (by rfl) ⟨1632266, by rfl⟩ : syracuseStep 2176355 = 3264533) B3264533
theorem B2176385 : Blo 1449544 2176385 := bstep (se 2 (by rfl) ⟨816144, by rfl⟩ : syracuseStep 2176385 = 1632289) B1632289
theorem B3487121 : Blo 1449544 3487121 := bstep (se 2 (by rfl) ⟨1307670, by rfl⟩ : syracuseStep 3487121 = 2615341) B2615341
theorem B3265937 : Blo 1449544 3265937 := bstep (se 2 (by rfl) ⟨1224726, by rfl⟩ : syracuseStep 3265937 = 2449453) B2449453
theorem B2176403 : Blo 1449544 2176403 := bstep (se 1 (by rfl) ⟨1632302, by rfl⟩ : syracuseStep 2176403 = 3264605) B3264605
theorem B2446753 : Blo 1449544 2446753 := bstep (se 2 (by rfl) ⟨917532, by rfl⟩ : syracuseStep 2446753 = 1835065) B1835065
theorem B3265955 : Blo 1449544 3265955 := bstep (se 1 (by rfl) ⟨2449466, by rfl⟩ : syracuseStep 3265955 = 4898933) B4898933
theorem B2176433 : Blo 1449544 2176433 := bstep (se 2 (by rfl) ⟨816162, by rfl⟩ : syracuseStep 2176433 = 1632325) B1632325
theorem B2446787 : Blo 1449544 2446787 := bstep (se 1 (by rfl) ⟨1835090, by rfl⟩ : syracuseStep 2446787 = 3670181) B3670181
theorem B2176451 : Blo 1449544 2176451 := bstep (se 1 (by rfl) ⟨1632338, by rfl⟩ : syracuseStep 2176451 = 3264677) B3264677
theorem B2176481 : Blo 1449544 2176481 := bstep (se 2 (by rfl) ⟨816180, by rfl⟩ : syracuseStep 2176481 = 1632361) B1632361
theorem B3487217 : Blo 1449544 3487217 := bstep (se 2 (by rfl) ⟨1307706, by rfl⟩ : syracuseStep 3487217 = 2615413) B2615413
theorem B2176499 : Blo 1449544 2176499 := bstep (se 1 (by rfl) ⟨1632374, by rfl⟩ : syracuseStep 2176499 = 3264749) B3264749
theorem B2176529 : Blo 1449544 2176529 := bstep (se 2 (by rfl) ⟨816198, by rfl⟩ : syracuseStep 2176529 = 1632397) B1632397
theorem B2176547 : Blo 1449544 2176547 := bstep (se 1 (by rfl) ⟨1632410, by rfl⟩ : syracuseStep 2176547 = 3264821) B3264821
theorem B2176577 : Blo 1449544 2176577 := bstep (se 2 (by rfl) ⟨816216, by rfl⟩ : syracuseStep 2176577 = 1632433) B1632433
theorem B2446915 : Blo 1449544 2446915 := bstep (se 1 (by rfl) ⟨1835186, by rfl⟩ : syracuseStep 2446915 = 3670373) B3670373
theorem B2176595 : Blo 1449544 2176595 := bstep (se 1 (by rfl) ⟨1632446, by rfl⟩ : syracuseStep 2176595 = 3264893) B3264893
theorem B2324081 : Blo 1449544 2324081 := bstep (se 2 (by rfl) ⟨871530, by rfl⟩ : syracuseStep 2324081 = 1743061) B1743061
theorem B2176625 : Blo 1449544 2176625 := bstep (se 2 (by rfl) ⟨816234, by rfl⟩ : syracuseStep 2176625 = 1632469) B1632469
theorem B2176643 : Blo 1449544 2176643 := bstep (se 1 (by rfl) ⟨1632482, by rfl⟩ : syracuseStep 2176643 = 3264965) B3264965
theorem B19854989 : Blo 1449544 19854989 := bstep (se 3 (by rfl) ⟨3722810, by rfl⟩ : syracuseStep 19854989 = 7445621) B7445621
theorem B2791057 : Blo 1449544 2791057 := bstep (se 2 (by rfl) ⟨1046646, by rfl⟩ : syracuseStep 2791057 = 2093293) B2093293
theorem B2176673 : Blo 1449544 2176673 := bstep (se 2 (by rfl) ⟨816252, by rfl⟩ : syracuseStep 2176673 = 1632505) B1632505
theorem B2176691 : Blo 1449544 2176691 := bstep (se 1 (by rfl) ⟨1632518, by rfl⟩ : syracuseStep 2176691 = 3265037) B3265037
theorem B5510861 : Blo 1449544 5510861 := bstep (se 3 (by rfl) ⟨1033286, by rfl⟩ : syracuseStep 5510861 = 2066573) B2066573
theorem B2447057 : Blo 1449544 2447057 := bstep (se 2 (by rfl) ⟨917646, by rfl⟩ : syracuseStep 2447057 = 1835293) B1835293
theorem B2176721 : Blo 1449544 2176721 := bstep (se 2 (by rfl) ⟨816270, by rfl⟩ : syracuseStep 2176721 = 1632541) B1632541
theorem B2176739 : Blo 1449544 2176739 := bstep (se 1 (by rfl) ⟨1632554, by rfl⟩ : syracuseStep 2176739 = 3265109) B3265109
theorem B2324209 : Blo 1449544 2324209 := bstep (se 2 (by rfl) ⟨871578, by rfl⟩ : syracuseStep 2324209 = 1743157) B1743157
theorem B2176769 : Blo 1449544 2176769 := bstep (se 2 (by rfl) ⟨816288, by rfl⟩ : syracuseStep 2176769 = 1632577) B1632577
theorem B2176787 : Blo 1449544 2176787 := bstep (se 1 (by rfl) ⟨1632590, by rfl⟩ : syracuseStep 2176787 = 3265181) B3265181
theorem B5879587 : Blo 1449544 5879587 := bstep (se 1 (by rfl) ⟨4409690, by rfl⟩ : syracuseStep 5879587 = 8819381) B8819381
theorem B4896557 : Blo 1449544 4896557 := bstep (se 3 (by rfl) ⟨918104, by rfl⟩ : syracuseStep 4896557 = 1836209) B1836209
theorem B2176817 : Blo 1449544 2176817 := bstep (se 2 (by rfl) ⟨816306, by rfl⟩ : syracuseStep 2176817 = 1632613) B1632613
theorem B2094913 : Blo 1449544 2094913 := bstep (se 2 (by rfl) ⟨785592, by rfl⟩ : syracuseStep 2094913 = 1571185) B1571185
theorem B2176835 : Blo 1449544 2176835 := bstep (se 1 (by rfl) ⟨1632626, by rfl⟩ : syracuseStep 2176835 = 3265253) B3265253
theorem B2447185 : Blo 1449544 2447185 := bstep (se 2 (by rfl) ⟨917694, by rfl⟩ : syracuseStep 2447185 = 1835389) B1835389
theorem B2176865 : Blo 1449544 2176865 := bstep (se 2 (by rfl) ⟨816324, by rfl⟩ : syracuseStep 2176865 = 1632649) B1632649
theorem B4896611 : Blo 1449544 4896611 := bstep (se 1 (by rfl) ⟨3672458, by rfl⟩ : syracuseStep 4896611 = 7344917) B7344917
theorem B4962161 : Blo 1449544 4962161 := bstep (se 2 (by rfl) ⟨1860810, by rfl⟩ : syracuseStep 4962161 = 3721621) B3721621
theorem B2447219 : Blo 1449544 2447219 := bstep (se 1 (by rfl) ⟨1835414, by rfl⟩ : syracuseStep 2447219 = 3670829) B3670829
theorem B2176883 : Blo 1449544 2176883 := bstep (se 1 (by rfl) ⟨1632662, by rfl⟩ : syracuseStep 2176883 = 3265325) B3265325
theorem B2176913 : Blo 1449544 2176913 := bstep (se 2 (by rfl) ⟨816342, by rfl⟩ : syracuseStep 2176913 = 1632685) B1632685
theorem B2176931 : Blo 1449544 2176931 := bstep (se 1 (by rfl) ⟨1632698, by rfl⟩ : syracuseStep 2176931 = 3265397) B3265397
theorem B2176961 : Blo 1449544 2176961 := bstep (se 2 (by rfl) ⟨816360, by rfl⟩ : syracuseStep 2176961 = 1632721) B1632721
theorem B2176979 : Blo 1449544 2176979 := bstep (se 1 (by rfl) ⟨1632734, by rfl⟩ : syracuseStep 2176979 = 3265469) B3265469
theorem B2177009 : Blo 1449544 2177009 := bstep (se 2 (by rfl) ⟨816378, by rfl⟩ : syracuseStep 2177009 = 1632757) B1632757
theorem B2447347 : Blo 1449544 2447347 := bstep (se 1 (by rfl) ⟨1835510, by rfl⟩ : syracuseStep 2447347 = 3671021) B3671021
theorem B2177027 : Blo 1449544 2177027 := bstep (se 1 (by rfl) ⟨1632770, by rfl⟩ : syracuseStep 2177027 = 3265541) B3265541
theorem B2177057 : Blo 1449544 2177057 := bstep (se 2 (by rfl) ⟨816396, by rfl⟩ : syracuseStep 2177057 = 1632793) B1632793
theorem B2177075 : Blo 1449544 2177075 := bstep (se 1 (by rfl) ⟨1632806, by rfl⟩ : syracuseStep 2177075 = 3265613) B3265613
theorem B2177105 : Blo 1449544 2177105 := bstep (se 2 (by rfl) ⟨816414, by rfl⟩ : syracuseStep 2177105 = 1632829) B1632829
theorem B2177123 : Blo 1449544 2177123 := bstep (se 1 (by rfl) ⟨1632842, by rfl⟩ : syracuseStep 2177123 = 3265685) B3265685
theorem B4896881 : Blo 1449544 4896881 := bstep (se 2 (by rfl) ⟨1836330, by rfl⟩ : syracuseStep 4896881 = 3672661) B3672661
theorem B2447489 : Blo 1449544 2447489 := bstep (se 2 (by rfl) ⟨917808, by rfl⟩ : syracuseStep 2447489 = 1835617) B1835617
theorem B2177153 : Blo 1449544 2177153 := bstep (se 2 (by rfl) ⟨816432, by rfl⟩ : syracuseStep 2177153 = 1632865) B1632865
theorem B2177171 : Blo 1449544 2177171 := bstep (se 1 (by rfl) ⟨1632878, by rfl⟩ : syracuseStep 2177171 = 3265757) B3265757
theorem B2177201 : Blo 1449544 2177201 := bstep (se 2 (by rfl) ⟨816450, by rfl⟩ : syracuseStep 2177201 = 1632901) B1632901
theorem B2177219 : Blo 1449544 2177219 := bstep (se 1 (by rfl) ⟨1632914, by rfl⟩ : syracuseStep 2177219 = 3265829) B3265829
theorem B2177249 : Blo 1449544 2177249 := bstep (se 2 (by rfl) ⟨816468, by rfl⟩ : syracuseStep 2177249 = 1632937) B1632937
theorem B2177267 : Blo 1449544 2177267 := bstep (se 1 (by rfl) ⟨1632950, by rfl⟩ : syracuseStep 2177267 = 3265901) B3265901
theorem B2447617 : Blo 1449544 2447617 := bstep (se 2 (by rfl) ⟨917856, by rfl⟩ : syracuseStep 2447617 = 1835713) B1835713
theorem B10451213 : Blo 1449544 10451213 := bstep (se 3 (by rfl) ⟨1959602, by rfl⟩ : syracuseStep 10451213 = 3919205) B3919205
theorem B2177297 : Blo 1449544 2177297 := bstep (se 2 (by rfl) ⟨816486, by rfl⟩ : syracuseStep 2177297 = 1632973) B1632973
theorem B2447651 : Blo 1449544 2447651 := bstep (se 1 (by rfl) ⟨1835738, by rfl⟩ : syracuseStep 2447651 = 3671477) B3671477
theorem B2177315 : Blo 1449544 2177315 := bstep (se 1 (by rfl) ⟨1632986, by rfl⟩ : syracuseStep 2177315 = 3265973) B3265973
theorem B2939203 : Blo 1449544 2939203 := bstep (se 1 (by rfl) ⟨2204402, by rfl⟩ : syracuseStep 2939203 = 4408805) B4408805
theorem B8821133 : Blo 1449544 8821133 := bstep (se 3 (by rfl) ⟨1653962, by rfl⟩ : syracuseStep 8821133 = 3307925) B3307925
theorem B2447779 : Blo 1449544 2447779 := bstep (se 1 (by rfl) ⟨1835834, by rfl⟩ : syracuseStep 2447779 = 3671669) B3671669
theorem B41843141 : Blo 1449544 41843141 := bstep (se 4 (by rfl) ⟨3922794, by rfl⟩ : syracuseStep 41843141 = 7845589) B7845589
theorem B2447921 : Blo 1449544 2447921 := bstep (se 2 (by rfl) ⟨917970, by rfl⟩ : syracuseStep 2447921 = 1835941) B1835941
theorem B8821325 : Blo 1449544 8821325 := bstep (se 3 (by rfl) ⟨1653998, by rfl⟩ : syracuseStep 8821325 = 3307997) B3307997
theorem B25107085 : Blo 1449544 25107085 := bstep (se 3 (by rfl) ⟨4707578, by rfl⟩ : syracuseStep 25107085 = 9415157) B9415157
theorem B4897421 : Blo 1449544 4897421 := bstep (se 3 (by rfl) ⟨918266, by rfl⟩ : syracuseStep 4897421 = 1836533) B1836533
theorem B7846541 : Blo 1449544 7846541 := bstep (se 3 (by rfl) ⟨1471226, by rfl⟩ : syracuseStep 7846541 = 2942453) B2942453
theorem B2448049 : Blo 1449544 2448049 := bstep (se 2 (by rfl) ⟨918018, by rfl⟩ : syracuseStep 2448049 = 1836037) B1836037
theorem B4897475 : Blo 1449544 4897475 := bstep (se 1 (by rfl) ⟨3673106, by rfl⟩ : syracuseStep 4897475 = 7346213) B7346213
theorem B2448083 : Blo 1449544 2448083 := bstep (se 1 (by rfl) ⟨1836062, by rfl⟩ : syracuseStep 2448083 = 3672125) B3672125
theorem B6200077 : Blo 1449544 6200077 := bstep (se 3 (by rfl) ⟨1162514, by rfl⟩ : syracuseStep 6200077 = 2325029) B2325029
theorem B2939665 : Blo 1449544 2939665 := bstep (se 2 (by rfl) ⟨1102374, by rfl⟩ : syracuseStep 2939665 = 2204749) B2204749
theorem B2448211 : Blo 1449544 2448211 := bstep (se 1 (by rfl) ⟨1836158, by rfl⟩ : syracuseStep 2448211 = 3672317) B3672317
theorem B2939761 : Blo 1449544 2939761 := bstep (se 2 (by rfl) ⟨1102410, by rfl⟩ : syracuseStep 2939761 = 2204821) B2204821
theorem B1743763 : Blo 1449544 1743763 := bstep (se 1 (by rfl) ⟨1307822, by rfl⟩ : syracuseStep 1743763 = 2615645) B2615645
theorem B31783877 : Blo 1449544 31783877 := bstep (se 4 (by rfl) ⟨2979738, by rfl⟩ : syracuseStep 31783877 = 5959477) B5959477
theorem B4897745 : Blo 1449544 4897745 := bstep (se 2 (by rfl) ⟨1836654, by rfl⟩ : syracuseStep 4897745 = 3673309) B3673309
theorem B2481107 : Blo 1449544 2481107 := bstep (se 1 (by rfl) ⟨1860830, by rfl⟩ : syracuseStep 2481107 = 3721661) B3721661
theorem B2448353 : Blo 1449544 2448353 := bstep (se 2 (by rfl) ⟨918132, by rfl⟩ : syracuseStep 2448353 = 1836265) B1836265
theorem B7347185 : Blo 1449544 7347185 := bstep (se 2 (by rfl) ⟨2755194, by rfl⟩ : syracuseStep 7347185 = 5510389) B5510389
theorem B7339085 : Blo 1449544 7339085 := bstep (se 3 (by rfl) ⟨1376078, by rfl⟩ : syracuseStep 7339085 = 2752157) B2752157
theorem B2448481 : Blo 1449544 2448481 := bstep (se 2 (by rfl) ⟨918180, by rfl⟩ : syracuseStep 2448481 = 1836361) B1836361
theorem B67034225 : Blo 1449544 67034225 := bstep (se 2 (by rfl) ⟨25137834, by rfl⟩ : syracuseStep 67034225 = 50275669) B50275669
theorem B2448515 : Blo 1449544 2448515 := bstep (se 1 (by rfl) ⟨1836386, by rfl⟩ : syracuseStep 2448515 = 3672773) B3672773
theorem B4127917 : Blo 1449544 4127917 := bstep (se 3 (by rfl) ⟨773984, by rfl⟩ : syracuseStep 4127917 = 1547969) B1547969
theorem B4644049 : Blo 1449544 4644049 := bstep (se 2 (by rfl) ⟨1741518, by rfl⟩ : syracuseStep 4644049 = 3483037) B3483037
theorem B2448643 : Blo 1449544 2448643 := bstep (se 1 (by rfl) ⟨1836482, by rfl⟩ : syracuseStep 2448643 = 3672965) B3672965
theorem B4644163 : Blo 1449544 4644163 := bstep (se 1 (by rfl) ⟨3483122, by rfl⟩ : syracuseStep 4644163 = 6966245) B6966245
theorem B4128077 : Blo 1449544 4128077 := bstep (se 3 (by rfl) ⟨774014, by rfl⟩ : syracuseStep 4128077 = 1548029) B1548029
theorem B8265037 : Blo 1449544 8265037 := bstep (se 3 (by rfl) ⟨1549694, by rfl⟩ : syracuseStep 8265037 = 3099389) B3099389
theorem B3095921 : Blo 1449544 3095921 := bstep (se 2 (by rfl) ⟨1160970, by rfl⟩ : syracuseStep 3095921 = 2321941) B2321941
theorem B2448785 : Blo 1449544 2448785 := bstep (se 2 (by rfl) ⟨918294, by rfl⟩ : syracuseStep 2448785 = 1836589) B1836589
theorem B2751907 : Blo 1449544 2751907 := bstep (se 1 (by rfl) ⟨2063930, by rfl⟩ : syracuseStep 2751907 = 4127861) B4127861
theorem B4898285 : Blo 1449544 4898285 := bstep (se 3 (by rfl) ⟨918428, by rfl⟩ : syracuseStep 4898285 = 1836857) B1836857
theorem B4128259 : Blo 1449544 4128259 := bstep (se 1 (by rfl) ⟨3096194, by rfl⟩ : syracuseStep 4128259 = 6192389) B6192389
theorem B2448913 : Blo 1449544 2448913 := bstep (se 2 (by rfl) ⟨918342, by rfl⟩ : syracuseStep 2448913 = 1836685) B1836685
theorem B4898339 : Blo 1449544 4898339 := bstep (se 1 (by rfl) ⟨3673754, by rfl⟩ : syracuseStep 4898339 = 7347509) B7347509
theorem B2448947 : Blo 1449544 2448947 := bstep (se 1 (by rfl) ⟨1836710, by rfl⟩ : syracuseStep 2448947 = 3673421) B3673421
theorem B1449555 : Blo 1449544 1449555 := bstep (se 1 (by rfl) ⟨1087166, by rfl⟩ : syracuseStep 1449555 = 2174333) B2174333
theorem B1449571 : Blo 1449544 1449571 := bstep (se 1 (by rfl) ⟨1087178, by rfl⟩ : syracuseStep 1449571 = 2174357) B2174357
theorem B1449587 : Blo 1449544 1449587 := bstep (se 1 (by rfl) ⟨1087190, by rfl⟩ : syracuseStep 1449587 = 2174381) B2174381
theorem B1449603 : Blo 1449544 1449603 := bstep (se 1 (by rfl) ⟨1087202, by rfl⟩ : syracuseStep 1449603 = 2174405) B2174405
theorem B1449619 : Blo 1449544 1449619 := bstep (se 1 (by rfl) ⟨1087214, by rfl⟩ : syracuseStep 1449619 = 2174429) B2174429
theorem B1449635 : Blo 1449544 1449635 := bstep (se 1 (by rfl) ⟨1087226, by rfl⟩ : syracuseStep 1449635 = 2174453) B2174453
theorem B1449651 : Blo 1449544 1449651 := bstep (se 1 (by rfl) ⟨1087238, by rfl⟩ : syracuseStep 1449651 = 2174477) B2174477
theorem B2449075 : Blo 1449544 2449075 := bstep (se 1 (by rfl) ⟨1836806, by rfl⟩ : syracuseStep 2449075 = 3673613) B3673613
theorem B1449667 : Blo 1449544 1449667 := bstep (se 1 (by rfl) ⟨1087250, by rfl⟩ : syracuseStep 1449667 = 2174501) B2174501
theorem B9297605 : Blo 1449544 9297605 := bstep (se 4 (by rfl) ⟨871650, by rfl⟩ : syracuseStep 9297605 = 1743301) B1743301
theorem B1449683 : Blo 1449544 1449683 := bstep (se 1 (by rfl) ⟨1087262, by rfl⟩ : syracuseStep 1449683 = 2174525) B2174525
theorem B1449699 : Blo 1449544 1449699 := bstep (se 1 (by rfl) ⟨1087274, by rfl⟩ : syracuseStep 1449699 = 2174549) B2174549
theorem B3669745 : Blo 1449544 3669745 := bstep (se 2 (by rfl) ⟨1376154, by rfl⟩ : syracuseStep 3669745 = 2752309) B2752309
theorem B9928433 : Blo 1449544 9928433 := bstep (se 2 (by rfl) ⟨3723162, by rfl⟩ : syracuseStep 9928433 = 7446325) B7446325
theorem B1449715 : Blo 1449544 1449715 := bstep (se 1 (by rfl) ⟨1087286, by rfl⟩ : syracuseStep 1449715 = 2174573) B2174573
theorem B1449731 : Blo 1449544 1449731 := bstep (se 1 (by rfl) ⟨1087298, by rfl⟩ : syracuseStep 1449731 = 2174597) B2174597
theorem B1449747 : Blo 1449544 1449747 := bstep (se 1 (by rfl) ⟨1087310, by rfl⟩ : syracuseStep 1449747 = 2174621) B2174621
theorem B1449763 : Blo 1449544 1449763 := bstep (se 1 (by rfl) ⟨1087322, by rfl⟩ : syracuseStep 1449763 = 2174645) B2174645
theorem B5447459 : Blo 1449544 5447459 := bstep (se 1 (by rfl) ⟨4085594, by rfl⟩ : syracuseStep 5447459 = 8171189) B8171189
theorem B2981681 : Blo 1449544 2981681 := bstep (se 2 (by rfl) ⟨1118130, by rfl⟩ : syracuseStep 2981681 = 2236261) B2236261
theorem B4898609 : Blo 1449544 4898609 := bstep (se 2 (by rfl) ⟨1836978, by rfl⟩ : syracuseStep 4898609 = 3673957) B3673957
theorem B1449779 : Blo 1449544 1449779 := bstep (se 1 (by rfl) ⟨1087334, by rfl⟩ : syracuseStep 1449779 = 2174669) B2174669
theorem B2449217 : Blo 1449544 2449217 := bstep (se 2 (by rfl) ⟨918456, by rfl⟩ : syracuseStep 2449217 = 1836913) B1836913
theorem B1449795 : Blo 1449544 1449795 := bstep (se 1 (by rfl) ⟨1087346, by rfl⟩ : syracuseStep 1449795 = 2174693) B2174693
theorem B2064209 : Blo 1449544 2064209 := bstep (se 2 (by rfl) ⟨774078, by rfl⟩ : syracuseStep 2064209 = 1548157) B1548157
theorem B1449811 : Blo 1449544 1449811 := bstep (se 1 (by rfl) ⟨1087358, by rfl⟩ : syracuseStep 1449811 = 2174717) B2174717
theorem B2752355 : Blo 1449544 2752355 := bstep (se 1 (by rfl) ⟨2064266, by rfl⟩ : syracuseStep 2752355 = 4128533) B4128533
theorem B1449827 : Blo 1449544 1449827 := bstep (se 1 (by rfl) ⟨1087370, by rfl⟩ : syracuseStep 1449827 = 2174741) B2174741
theorem B1449843 : Blo 1449544 1449843 := bstep (se 1 (by rfl) ⟨1087382, by rfl⟩ : syracuseStep 1449843 = 2174765) B2174765
theorem B1449859 : Blo 1449544 1449859 := bstep (se 1 (by rfl) ⟨1087394, by rfl⟩ : syracuseStep 1449859 = 2174789) B2174789
theorem B6193037 : Blo 1449544 6193037 := bstep (se 3 (by rfl) ⟨1161194, by rfl⟩ : syracuseStep 6193037 = 2322389) B2322389
theorem B7077773 : Blo 1449544 7077773 := bstep (se 3 (by rfl) ⟨1327082, by rfl⟩ : syracuseStep 7077773 = 2654165) B2654165
theorem B1449875 : Blo 1449544 1449875 := bstep (se 1 (by rfl) ⟨1087406, by rfl⟩ : syracuseStep 1449875 = 2174813) B2174813
theorem B1449891 : Blo 1449544 1449891 := bstep (se 1 (by rfl) ⟨1087418, by rfl⟩ : syracuseStep 1449891 = 2174837) B2174837
theorem B1449907 : Blo 1449544 1449907 := bstep (se 1 (by rfl) ⟨1087430, by rfl⟩ : syracuseStep 1449907 = 2174861) B2174861
theorem B2449345 : Blo 1449544 2449345 := bstep (se 2 (by rfl) ⟨918504, by rfl⟩ : syracuseStep 2449345 = 1837009) B1837009
theorem B2064323 : Blo 1449544 2064323 := bstep (se 1 (by rfl) ⟨1548242, by rfl⟩ : syracuseStep 2064323 = 3096485) B3096485
theorem B1449923 : Blo 1449544 1449923 := bstep (se 1 (by rfl) ⟨1087442, by rfl⟩ : syracuseStep 1449923 = 2174885) B2174885
theorem B1449939 : Blo 1449544 1449939 := bstep (se 1 (by rfl) ⟨1087454, by rfl⟩ : syracuseStep 1449939 = 2174909) B2174909
theorem B1449955 : Blo 1449544 1449955 := bstep (se 1 (by rfl) ⟨1087466, by rfl⟩ : syracuseStep 1449955 = 2174933) B2174933
theorem B2449379 : Blo 1449544 2449379 := bstep (se 1 (by rfl) ⟨1837034, by rfl⟩ : syracuseStep 2449379 = 3674069) B3674069
theorem B1449971 : Blo 1449544 1449971 := bstep (se 1 (by rfl) ⟨1087478, by rfl⟩ : syracuseStep 1449971 = 2174957) B2174957
theorem B3096587 : Blo 1449544 3096587 := bstep (se 1 (by rfl) ⟨2322440, by rfl⟩ : syracuseStep 3096587 = 4644881) B4644881
theorem B1449995 : Blo 1449544 1449995 := bstep (se 1 (by rfl) ⟨1087496, by rfl⟩ : syracuseStep 1449995 = 2174993) B2174993
theorem B1450007 : Blo 1449544 1450007 := bstep (se 1 (by rfl) ⟨1087505, by rfl⟩ : syracuseStep 1450007 = 2175011) B2175011
theorem B2752537 : Blo 1449544 2752537 := bstep (se 2 (by rfl) ⟨1032201, by rfl⟩ : syracuseStep 2752537 = 2064403) B2064403
theorem B2449433 : Blo 1449544 2449433 := bstep (se 2 (by rfl) ⟨918537, by rfl⟩ : syracuseStep 2449433 = 1837075) B1837075
theorem B1450027 : Blo 1449544 1450027 := bstep (se 1 (by rfl) ⟨1087520, by rfl⟩ : syracuseStep 1450027 = 2175041) B2175041
theorem B7258157 : Blo 1449544 7258157 := bstep (se 3 (by rfl) ⟨1360904, by rfl⟩ : syracuseStep 7258157 = 2721809) B2721809
theorem B1450039 : Blo 1449544 1450039 := bstep (se 1 (by rfl) ⟨1087529, by rfl⟩ : syracuseStep 1450039 = 2175059) B2175059
theorem B1450059 : Blo 1449544 1450059 := bstep (se 1 (by rfl) ⟨1087544, by rfl⟩ : syracuseStep 1450059 = 2175089) B2175089
theorem B2613323 : Blo 1449544 2613323 := bstep (se 1 (by rfl) ⟨1959992, by rfl⟩ : syracuseStep 2613323 = 3919985) B3919985
theorem B1450071 : Blo 1449544 1450071 := bstep (se 1 (by rfl) ⟨1087553, by rfl⟩ : syracuseStep 1450071 = 2175107) B2175107
theorem B1450091 : Blo 1449544 1450091 := bstep (se 1 (by rfl) ⟨1087568, by rfl⟩ : syracuseStep 1450091 = 2175137) B2175137
theorem B1450103 : Blo 1449544 1450103 := bstep (se 1 (by rfl) ⟨1087577, by rfl⟩ : syracuseStep 1450103 = 2175155) B2175155
theorem B2064523 : Blo 1449544 2064523 := bstep (se 1 (by rfl) ⟨1548392, by rfl⟩ : syracuseStep 2064523 = 3096785) B3096785
theorem B1450123 : Blo 1449544 1450123 := bstep (se 1 (by rfl) ⟨1087592, by rfl⟩ : syracuseStep 1450123 = 2175185) B2175185
theorem B1450135 : Blo 1449544 1450135 := bstep (se 1 (by rfl) ⟨1087601, by rfl⟩ : syracuseStep 1450135 = 2175203) B2175203
theorem B1450155 : Blo 1449544 1450155 := bstep (se 1 (by rfl) ⟨1087616, by rfl⟩ : syracuseStep 1450155 = 2175233) B2175233
theorem B1450167 : Blo 1449544 1450167 := bstep (se 1 (by rfl) ⟨1087625, by rfl⟩ : syracuseStep 1450167 = 2175251) B2175251
theorem B1450187 : Blo 1449544 1450187 := bstep (se 1 (by rfl) ⟨1087640, by rfl⟩ : syracuseStep 1450187 = 2175281) B2175281
theorem B1450199 : Blo 1449544 1450199 := bstep (se 1 (by rfl) ⟨1087649, by rfl⟩ : syracuseStep 1450199 = 2175299) B2175299
theorem B6971609 : Blo 1449544 6971609 := bstep (se 2 (by rfl) ⟨2614353, by rfl⟩ : syracuseStep 6971609 = 5228707) B5228707
theorem B1450219 : Blo 1449544 1450219 := bstep (se 1 (by rfl) ⟨1087664, by rfl⟩ : syracuseStep 1450219 = 2175329) B2175329
theorem B1450231 : Blo 1449544 1450231 := bstep (se 1 (by rfl) ⟨1087673, by rfl⟩ : syracuseStep 1450231 = 2175347) B2175347
theorem B23527685 : Blo 1449544 23527685 := bstep (se 4 (by rfl) ⟨2205720, by rfl⟩ : syracuseStep 23527685 = 4411441) B4411441
theorem B1450251 : Blo 1449544 1450251 := bstep (se 1 (by rfl) ⟨1087688, by rfl⟩ : syracuseStep 1450251 = 2175377) B2175377
theorem B1450263 : Blo 1449544 1450263 := bstep (se 1 (by rfl) ⟨1087697, by rfl⟩ : syracuseStep 1450263 = 2175395) B2175395
theorem B1450283 : Blo 1449544 1450283 := bstep (se 1 (by rfl) ⟨1087712, by rfl⟩ : syracuseStep 1450283 = 2175425) B2175425
theorem B1450295 : Blo 1449544 1450295 := bstep (se 1 (by rfl) ⟨1087721, by rfl⟩ : syracuseStep 1450295 = 2175443) B2175443
theorem B1450315 : Blo 1449544 1450315 := bstep (se 1 (by rfl) ⟨1087736, by rfl⟩ : syracuseStep 1450315 = 2175473) B2175473
theorem B1450327 : Blo 1449544 1450327 := bstep (se 1 (by rfl) ⟨1087745, by rfl⟩ : syracuseStep 1450327 = 2175491) B2175491
theorem B7340381 : Blo 1449544 7340381 := bstep (se 3 (by rfl) ⟨1376321, by rfl⟩ : syracuseStep 7340381 = 2752643) B2752643
theorem B1450347 : Blo 1449544 1450347 := bstep (se 1 (by rfl) ⟨1087760, by rfl⟩ : syracuseStep 1450347 = 2175521) B2175521
theorem B3096947 : Blo 1449544 3096947 := bstep (se 1 (by rfl) ⟨2322710, by rfl⟩ : syracuseStep 3096947 = 4645421) B4645421
theorem B1450359 : Blo 1449544 1450359 := bstep (se 1 (by rfl) ⟨1087769, by rfl⟩ : syracuseStep 1450359 = 2175539) B2175539
theorem B1450379 : Blo 1449544 1450379 := bstep (se 1 (by rfl) ⟨1087784, by rfl⟩ : syracuseStep 1450379 = 2175569) B2175569
theorem B1450391 : Blo 1449544 1450391 := bstep (se 1 (by rfl) ⟨1087793, by rfl⟩ : syracuseStep 1450391 = 2175587) B2175587
theorem B1450411 : Blo 1449544 1450411 := bstep (se 1 (by rfl) ⟨1087808, by rfl⟩ : syracuseStep 1450411 = 2175617) B2175617
theorem B1450423 : Blo 1449544 1450423 := bstep (se 1 (by rfl) ⟨1087817, by rfl⟩ : syracuseStep 1450423 = 2175635) B2175635
theorem B1450443 : Blo 1449544 1450443 := bstep (se 1 (by rfl) ⟨1087832, by rfl⟩ : syracuseStep 1450443 = 2175665) B2175665
theorem B1450455 : Blo 1449544 1450455 := bstep (se 1 (by rfl) ⟨1087841, by rfl⟩ : syracuseStep 1450455 = 2175683) B2175683
theorem B1450475 : Blo 1449544 1450475 := bstep (se 1 (by rfl) ⟨1087856, by rfl⟩ : syracuseStep 1450475 = 2175713) B2175713
theorem B1450487 : Blo 1449544 1450487 := bstep (se 1 (by rfl) ⟨1087865, by rfl⟩ : syracuseStep 1450487 = 2175731) B2175731
theorem B1450507 : Blo 1449544 1450507 := bstep (se 1 (by rfl) ⟨1087880, by rfl⟩ : syracuseStep 1450507 = 2175761) B2175761
theorem B1450519 : Blo 1449544 1450519 := bstep (se 1 (by rfl) ⟨1087889, by rfl⟩ : syracuseStep 1450519 = 2175779) B2175779
theorem B1450539 : Blo 1449544 1450539 := bstep (se 1 (by rfl) ⟨1087904, by rfl⟩ : syracuseStep 1450539 = 2175809) B2175809
theorem B1450551 : Blo 1449544 1450551 := bstep (se 1 (by rfl) ⟨1087913, by rfl⟩ : syracuseStep 1450551 = 2175827) B2175827
theorem B1630795 : Blo 1449544 1630795 := bstep (se 1 (by rfl) ⟨1223096, by rfl⟩ : syracuseStep 1630795 = 2446193) B2446193
theorem B2753099 : Blo 1449544 2753099 := bstep (se 1 (by rfl) ⟨2064824, by rfl⟩ : syracuseStep 2753099 = 4129649) B4129649
theorem B1450571 : Blo 1449544 1450571 := bstep (se 1 (by rfl) ⟨1087928, by rfl⟩ : syracuseStep 1450571 = 2175857) B2175857
theorem B1450583 : Blo 1449544 1450583 := bstep (se 1 (by rfl) ⟨1087937, by rfl⟩ : syracuseStep 1450583 = 2175875) B2175875
theorem B1450603 : Blo 1449544 1450603 := bstep (se 1 (by rfl) ⟨1087952, by rfl⟩ : syracuseStep 1450603 = 2175905) B2175905
theorem B1450615 : Blo 1449544 1450615 := bstep (se 1 (by rfl) ⟨1087961, by rfl⟩ : syracuseStep 1450615 = 2175923) B2175923
theorem B1450635 : Blo 1449544 1450635 := bstep (se 1 (by rfl) ⟨1087976, by rfl⟩ : syracuseStep 1450635 = 2175953) B2175953
theorem B1450647 : Blo 1449544 1450647 := bstep (se 1 (by rfl) ⟨1087985, by rfl⟩ : syracuseStep 1450647 = 2175971) B2175971
theorem B1450667 : Blo 1449544 1450667 := bstep (se 1 (by rfl) ⟨1088000, by rfl⟩ : syracuseStep 1450667 = 2176001) B2176001
theorem B1630903 : Blo 1449544 1630903 := bstep (se 1 (by rfl) ⟨1223177, by rfl⟩ : syracuseStep 1630903 = 2446355) B2446355
theorem B1450679 : Blo 1449544 1450679 := bstep (se 1 (by rfl) ⟨1088009, by rfl⟩ : syracuseStep 1450679 = 2176019) B2176019
theorem B1835723 : Blo 1449544 1835723 := bstep (se 1 (by rfl) ⟨1376792, by rfl⟩ : syracuseStep 1835723 = 2753585) B2753585
theorem B1450699 : Blo 1449544 1450699 := bstep (se 1 (by rfl) ⟨1088024, by rfl⟩ : syracuseStep 1450699 = 2176049) B2176049
theorem B1450711 : Blo 1449544 1450711 := bstep (se 1 (by rfl) ⟨1088033, by rfl⟩ : syracuseStep 1450711 = 2176067) B2176067
theorem B4129501 : Blo 1449544 4129501 := bstep (se 3 (by rfl) ⟨774281, by rfl⟩ : syracuseStep 4129501 = 1548563) B1548563
theorem B1450731 : Blo 1449544 1450731 := bstep (se 1 (by rfl) ⟨1088048, by rfl⟩ : syracuseStep 1450731 = 2176097) B2176097
theorem B1450743 : Blo 1449544 1450743 := bstep (se 1 (by rfl) ⟨1088057, by rfl⟩ : syracuseStep 1450743 = 2176115) B2176115
theorem B2753281 : Blo 1449544 2753281 := bstep (se 2 (by rfl) ⟨1032480, by rfl⟩ : syracuseStep 2753281 = 2064961) B2064961
theorem B1450763 : Blo 1449544 1450763 := bstep (se 1 (by rfl) ⟨1088072, by rfl⟩ : syracuseStep 1450763 = 2176145) B2176145
theorem B1450775 : Blo 1449544 1450775 := bstep (se 1 (by rfl) ⟨1088081, by rfl⟩ : syracuseStep 1450775 = 2176163) B2176163
theorem B1450795 : Blo 1449544 1450795 := bstep (se 1 (by rfl) ⟨1088096, by rfl⟩ : syracuseStep 1450795 = 2176193) B2176193
theorem B1450807 : Blo 1449544 1450807 := bstep (se 1 (by rfl) ⟨1088105, by rfl⟩ : syracuseStep 1450807 = 2176211) B2176211
theorem B3670859 : Blo 1449544 3670859 := bstep (se 1 (by rfl) ⟨2753144, by rfl⟩ : syracuseStep 3670859 = 5506289) B5506289
theorem B1450827 : Blo 1449544 1450827 := bstep (se 1 (by rfl) ⟨1088120, by rfl⟩ : syracuseStep 1450827 = 2176241) B2176241
theorem B1450839 : Blo 1449544 1450839 := bstep (se 1 (by rfl) ⟨1088129, by rfl⟩ : syracuseStep 1450839 = 2176259) B2176259
theorem B1631083 : Blo 1449544 1631083 := bstep (se 1 (by rfl) ⟨1223312, by rfl⟩ : syracuseStep 1631083 = 2446625) B2446625
theorem B1450859 : Blo 1449544 1450859 := bstep (se 1 (by rfl) ⟨1088144, by rfl⟩ : syracuseStep 1450859 = 2176289) B2176289
theorem B1450871 : Blo 1449544 1450871 := bstep (se 1 (by rfl) ⟨1088153, by rfl⟩ : syracuseStep 1450871 = 2176307) B2176307
theorem B1450891 : Blo 1449544 1450891 := bstep (se 1 (by rfl) ⟨1088168, by rfl⟩ : syracuseStep 1450891 = 2176337) B2176337
theorem B1450903 : Blo 1449544 1450903 := bstep (se 1 (by rfl) ⟨1088177, by rfl⟩ : syracuseStep 1450903 = 2176355) B2176355
theorem B1450923 : Blo 1449544 1450923 := bstep (se 1 (by rfl) ⟨1088192, by rfl⟩ : syracuseStep 1450923 = 2176385) B2176385
theorem B1450935 : Blo 1449544 1450935 := bstep (se 1 (by rfl) ⟨1088201, by rfl⟩ : syracuseStep 1450935 = 2176403) B2176403
theorem B1450955 : Blo 1449544 1450955 := bstep (se 1 (by rfl) ⟨1088216, by rfl⟩ : syracuseStep 1450955 = 2176433) B2176433
theorem B1631191 : Blo 1449544 1631191 := bstep (se 1 (by rfl) ⟨1223393, by rfl⟩ : syracuseStep 1631191 = 2446787) B2446787
theorem B1450967 : Blo 1449544 1450967 := bstep (se 1 (by rfl) ⟨1088225, by rfl⟩ : syracuseStep 1450967 = 2176451) B2176451
theorem B1450987 : Blo 1449544 1450987 := bstep (se 1 (by rfl) ⟨1088240, by rfl⟩ : syracuseStep 1450987 = 2176481) B2176481
theorem B1450999 : Blo 1449544 1450999 := bstep (se 1 (by rfl) ⟨1088249, by rfl⟩ : syracuseStep 1450999 = 2176499) B2176499
theorem B1451019 : Blo 1449544 1451019 := bstep (se 1 (by rfl) ⟨1088264, by rfl⟩ : syracuseStep 1451019 = 2176529) B2176529
theorem B23528465 : Blo 1449544 23528465 := bstep (se 2 (by rfl) ⟨8823174, by rfl⟩ : syracuseStep 23528465 = 17646349) B17646349
theorem B8266769 : Blo 1449544 8266769 := bstep (se 2 (by rfl) ⟨3100038, by rfl⟩ : syracuseStep 8266769 = 6200077) B6200077
theorem B1451031 : Blo 1449544 1451031 := bstep (se 1 (by rfl) ⟨1088273, by rfl⟩ : syracuseStep 1451031 = 2176547) B2176547
theorem B2614297 : Blo 1449544 2614297 := bstep (se 2 (by rfl) ⟨980361, by rfl⟩ : syracuseStep 2614297 = 1960723) B1960723
theorem B1451051 : Blo 1449544 1451051 := bstep (se 1 (by rfl) ⟨1088288, by rfl⟩ : syracuseStep 1451051 = 2176577) B2176577
theorem B3261491 : Blo 1449544 3261491 := bstep (se 1 (by rfl) ⟨2446118, by rfl⟩ : syracuseStep 3261491 = 4892237) B4892237
theorem B1451063 : Blo 1449544 1451063 := bstep (se 1 (by rfl) ⟨1088297, by rfl⟩ : syracuseStep 1451063 = 2176595) B2176595
theorem B1549387 : Blo 1449544 1549387 := bstep (se 1 (by rfl) ⟨1162040, by rfl⟩ : syracuseStep 1549387 = 2324081) B2324081
theorem B1451083 : Blo 1449544 1451083 := bstep (se 1 (by rfl) ⟨1088312, by rfl⟩ : syracuseStep 1451083 = 2176625) B2176625
theorem B3261527 : Blo 1449544 3261527 := bstep (se 1 (by rfl) ⟨2446145, by rfl⟩ : syracuseStep 3261527 = 4892291) B4892291
theorem B1451095 : Blo 1449544 1451095 := bstep (se 1 (by rfl) ⟨1088321, by rfl⟩ : syracuseStep 1451095 = 2176643) B2176643
theorem B1451115 : Blo 1449544 1451115 := bstep (se 1 (by rfl) ⟨1088336, by rfl⟩ : syracuseStep 1451115 = 2176673) B2176673
theorem B1451127 : Blo 1449544 1451127 := bstep (se 1 (by rfl) ⟨1088345, by rfl⟩ : syracuseStep 1451127 = 2176691) B2176691
theorem B1631371 : Blo 1449544 1631371 := bstep (se 1 (by rfl) ⟨1223528, by rfl⟩ : syracuseStep 1631371 = 2447057) B2447057
theorem B1451147 : Blo 1449544 1451147 := bstep (se 1 (by rfl) ⟨1088360, by rfl⟩ : syracuseStep 1451147 = 2176721) B2176721
theorem B1451159 : Blo 1449544 1451159 := bstep (se 1 (by rfl) ⟨1088369, by rfl⟩ : syracuseStep 1451159 = 2176739) B2176739
theorem B1451179 : Blo 1449544 1451179 := bstep (se 1 (by rfl) ⟨1088384, by rfl⟩ : syracuseStep 1451179 = 2176769) B2176769
theorem B1451191 : Blo 1449544 1451191 := bstep (se 1 (by rfl) ⟨1088393, by rfl⟩ : syracuseStep 1451191 = 2176787) B2176787
theorem B1451211 : Blo 1449544 1451211 := bstep (se 1 (by rfl) ⟨1088408, by rfl⟩ : syracuseStep 1451211 = 2176817) B2176817
theorem B1451223 : Blo 1449544 1451223 := bstep (se 1 (by rfl) ⟨1088417, by rfl⟩ : syracuseStep 1451223 = 2176835) B2176835
theorem B9290969 : Blo 1449544 9290969 := bstep (se 2 (by rfl) ⟨3484113, by rfl⟩ : syracuseStep 9290969 = 6968227) B6968227
theorem B1451243 : Blo 1449544 1451243 := bstep (se 1 (by rfl) ⟨1088432, by rfl⟩ : syracuseStep 1451243 = 2176865) B2176865
theorem B1631479 : Blo 1449544 1631479 := bstep (se 1 (by rfl) ⟨1223609, by rfl⟩ : syracuseStep 1631479 = 2447219) B2447219
theorem B1451255 : Blo 1449544 1451255 := bstep (se 1 (by rfl) ⟨1088441, by rfl⟩ : syracuseStep 1451255 = 2176883) B2176883
theorem B3261707 : Blo 1449544 3261707 := bstep (se 1 (by rfl) ⟨2446280, by rfl⟩ : syracuseStep 3261707 = 4892561) B4892561
theorem B1451275 : Blo 1449544 1451275 := bstep (se 1 (by rfl) ⟨1088456, by rfl⟩ : syracuseStep 1451275 = 2176913) B2176913
theorem B1451287 : Blo 1449544 1451287 := bstep (se 1 (by rfl) ⟨1088465, by rfl⟩ : syracuseStep 1451287 = 2176931) B2176931
theorem B1451307 : Blo 1449544 1451307 := bstep (se 1 (by rfl) ⟨1088480, by rfl⟩ : syracuseStep 1451307 = 2176961) B2176961
theorem B9299245 : Blo 1449544 9299245 := bstep (se 3 (by rfl) ⟨1743608, by rfl⟩ : syracuseStep 9299245 = 3487217) B3487217
theorem B1451319 : Blo 1449544 1451319 := bstep (se 1 (by rfl) ⟨1088489, by rfl⟩ : syracuseStep 1451319 = 2176979) B2176979
theorem B3261761 : Blo 1449544 3261761 := bstep (se 2 (by rfl) ⟨1223160, by rfl⟩ : syracuseStep 3261761 = 2446321) B2446321
theorem B1451339 : Blo 1449544 1451339 := bstep (se 1 (by rfl) ⟨1088504, by rfl⟩ : syracuseStep 1451339 = 2177009) B2177009
theorem B1451351 : Blo 1449544 1451351 := bstep (se 1 (by rfl) ⟨1088513, by rfl⟩ : syracuseStep 1451351 = 2177027) B2177027
theorem B2065753 : Blo 1449544 2065753 := bstep (se 2 (by rfl) ⟨774657, by rfl⟩ : syracuseStep 2065753 = 1549315) B1549315
theorem B1451371 : Blo 1449544 1451371 := bstep (se 1 (by rfl) ⟨1088528, by rfl⟩ : syracuseStep 1451371 = 2177057) B2177057
theorem B1451383 : Blo 1449544 1451383 := bstep (se 1 (by rfl) ⟨1088537, by rfl⟩ : syracuseStep 1451383 = 2177075) B2177075
theorem B1836427 : Blo 1449544 1836427 := bstep (se 1 (by rfl) ⟨1377320, by rfl⟩ : syracuseStep 1836427 = 2754641) B2754641
theorem B1451403 : Blo 1449544 1451403 := bstep (se 1 (by rfl) ⟨1088552, by rfl⟩ : syracuseStep 1451403 = 2177105) B2177105
theorem B1451415 : Blo 1449544 1451415 := bstep (se 1 (by rfl) ⟨1088561, by rfl⟩ : syracuseStep 1451415 = 2177123) B2177123
theorem B1631659 : Blo 1449544 1631659 := bstep (se 1 (by rfl) ⟨1223744, by rfl⟩ : syracuseStep 1631659 = 2447489) B2447489
theorem B1451435 : Blo 1449544 1451435 := bstep (se 1 (by rfl) ⟨1088576, by rfl⟩ : syracuseStep 1451435 = 2177153) B2177153
theorem B1451447 : Blo 1449544 1451447 := bstep (se 1 (by rfl) ⟨1088585, by rfl⟩ : syracuseStep 1451447 = 2177171) B2177171
theorem B2753995 : Blo 1449544 2753995 := bstep (se 1 (by rfl) ⟨2065496, by rfl⟩ : syracuseStep 2753995 = 4130993) B4130993
theorem B1451467 : Blo 1449544 1451467 := bstep (se 1 (by rfl) ⟨1088600, by rfl⟩ : syracuseStep 1451467 = 2177201) B2177201
theorem B1451479 : Blo 1449544 1451479 := bstep (se 1 (by rfl) ⟨1088609, by rfl⟩ : syracuseStep 1451479 = 2177219) B2177219
theorem B1451499 : Blo 1449544 1451499 := bstep (se 1 (by rfl) ⟨1088624, by rfl⟩ : syracuseStep 1451499 = 2177249) B2177249
theorem B1451511 : Blo 1449544 1451511 := bstep (se 1 (by rfl) ⟨1088633, by rfl⟩ : syracuseStep 1451511 = 2177267) B2177267
theorem B1451531 : Blo 1449544 1451531 := bstep (se 1 (by rfl) ⟨1088648, by rfl⟩ : syracuseStep 1451531 = 2177297) B2177297
theorem B1631767 : Blo 1449544 1631767 := bstep (se 1 (by rfl) ⟨1223825, by rfl⟩ : syracuseStep 1631767 = 2447651) B2447651
theorem B3261977 : Blo 1449544 3261977 := bstep (se 2 (by rfl) ⟨1223241, by rfl⟩ : syracuseStep 3261977 = 2446483) B2446483
theorem B2754071 : Blo 1449544 2754071 := bstep (se 1 (by rfl) ⟨2065553, by rfl⟩ : syracuseStep 2754071 = 4131107) B4131107
theorem B1451543 : Blo 1449544 1451543 := bstep (se 1 (by rfl) ⟨1088657, by rfl⟩ : syracuseStep 1451543 = 2177315) B2177315
theorem B3720779 : Blo 1449544 3720779 := bstep (se 1 (by rfl) ⟨2790584, by rfl⟩ : syracuseStep 3720779 = 5581169) B5581169
theorem B3262067 : Blo 1449544 3262067 := bstep (se 1 (by rfl) ⟨2446550, by rfl⟩ : syracuseStep 3262067 = 4893101) B4893101
theorem B27895427 : Blo 1449544 27895427 := bstep (se 1 (by rfl) ⟨20921570, by rfl⟩ : syracuseStep 27895427 = 41843141) B41843141
theorem B3262103 : Blo 1449544 3262103 := bstep (se 1 (by rfl) ⟨2446577, by rfl⟩ : syracuseStep 3262103 = 4893155) B4893155
theorem B1836695 : Blo 1449544 1836695 := bstep (se 1 (by rfl) ⟨1377521, by rfl⟩ : syracuseStep 1836695 = 2755043) B2755043
theorem B1631947 : Blo 1449544 1631947 := bstep (se 1 (by rfl) ⟨1223960, by rfl⟩ : syracuseStep 1631947 = 2447921) B2447921
theorem B34866893 : Blo 1449544 34866893 := bstep (se 3 (by rfl) ⟨6537542, by rfl⟩ : syracuseStep 34866893 = 13075085) B13075085
theorem B11020049 : Blo 1449544 11020049 := bstep (se 2 (by rfl) ⟨4132518, by rfl⟩ : syracuseStep 11020049 = 8265037) B8265037
theorem B3671831 : Blo 1449544 3671831 := bstep (se 1 (by rfl) ⟨2753873, by rfl⟩ : syracuseStep 3671831 = 5507747) B5507747
theorem B1632055 : Blo 1449544 1632055 := bstep (se 1 (by rfl) ⟨1224041, by rfl⟩ : syracuseStep 1632055 = 2448083) B2448083
theorem B3262283 : Blo 1449544 3262283 := bstep (se 1 (by rfl) ⟨2446712, by rfl⟩ : syracuseStep 3262283 = 4893425) B4893425
theorem B3262337 : Blo 1449544 3262337 := bstep (se 2 (by rfl) ⟨1223376, by rfl⟩ : syracuseStep 3262337 = 2446753) B2446753
theorem B8259479 : Blo 1449544 8259479 := bstep (se 1 (by rfl) ⟨6194609, by rfl⟩ : syracuseStep 8259479 = 12389219) B12389219
theorem B4130777 : Blo 1449544 4130777 := bstep (se 2 (by rfl) ⟨1549041, by rfl⟩ : syracuseStep 4130777 = 3098083) B3098083
theorem B6039517 : Blo 1449544 6039517 := bstep (se 3 (by rfl) ⟨1132409, by rfl⟩ : syracuseStep 6039517 = 2264819) B2264819
theorem B1632235 : Blo 1449544 1632235 := bstep (se 1 (by rfl) ⟨1224176, by rfl⟩ : syracuseStep 1632235 = 2448353) B2448353
theorem B4892723 : Blo 1449544 4892723 := bstep (se 1 (by rfl) ⟨3669542, by rfl⟩ : syracuseStep 4892723 = 7339085) B7339085
theorem B7063627 : Blo 1449544 7063627 := bstep (se 1 (by rfl) ⟨5297720, by rfl⟩ : syracuseStep 7063627 = 10595441) B10595441
theorem B44689483 : Blo 1449544 44689483 := bstep (se 1 (by rfl) ⟨33517112, by rfl⟩ : syracuseStep 44689483 = 67034225) B67034225
theorem B1632343 : Blo 1449544 1632343 := bstep (se 1 (by rfl) ⟨1224257, by rfl⟩ : syracuseStep 1632343 = 2448515) B2448515
theorem B3262553 : Blo 1449544 3262553 := bstep (se 2 (by rfl) ⟨1223457, by rfl⟩ : syracuseStep 3262553 = 2446915) B2446915
theorem B11012273 : Blo 1449544 11012273 := bstep (se 2 (by rfl) ⟨4129602, by rfl⟩ : syracuseStep 11012273 = 8259205) B8259205
theorem B3262643 : Blo 1449544 3262643 := bstep (se 1 (by rfl) ⟨2446982, by rfl⟩ : syracuseStep 3262643 = 4893965) B4893965
theorem B2754739 : Blo 1449544 2754739 := bstep (se 1 (by rfl) ⟨2066054, by rfl⟩ : syracuseStep 2754739 = 4132109) B4132109
theorem B3721409 : Blo 1449544 3721409 := bstep (se 2 (by rfl) ⟨1395528, by rfl⟩ : syracuseStep 3721409 = 2791057) B2791057
theorem B3262679 : Blo 1449544 3262679 := bstep (se 1 (by rfl) ⟨2447009, by rfl⟩ : syracuseStep 3262679 = 4894019) B4894019
theorem B2066647 : Blo 1449544 2066647 := bstep (se 1 (by rfl) ⟨1549985, by rfl⟩ : syracuseStep 2066647 = 3099971) B3099971
theorem B5884163 : Blo 1449544 5884163 := bstep (se 1 (by rfl) ⟨4413122, by rfl⟩ : syracuseStep 5884163 = 8826245) B8826245
theorem B1632523 : Blo 1449544 1632523 := bstep (se 1 (by rfl) ⟨1224392, by rfl⟩ : syracuseStep 1632523 = 2448785) B2448785
theorem B13232429 : Blo 1449544 13232429 := bstep (se 3 (by rfl) ⟨2481080, by rfl⟩ : syracuseStep 13232429 = 4962161) B4962161
theorem B4892993 : Blo 1449544 4892993 := bstep (se 2 (by rfl) ⟨1834872, by rfl⟩ : syracuseStep 4892993 = 3669745) B3669745
theorem B3098945 : Blo 1449544 3098945 := bstep (se 2 (by rfl) ⟨1162104, by rfl⟩ : syracuseStep 3098945 = 2324209) B2324209
theorem B1632631 : Blo 1449544 1632631 := bstep (se 1 (by rfl) ⟨1224473, by rfl⟩ : syracuseStep 1632631 = 2448947) B2448947
theorem B5507459 : Blo 1449544 5507459 := bstep (se 1 (by rfl) ⟨4130594, by rfl⟩ : syracuseStep 5507459 = 8261189) B8261189
theorem B3262859 : Blo 1449544 3262859 := bstep (se 1 (by rfl) ⟨2447144, by rfl⟩ : syracuseStep 3262859 = 4894289) B4894289
theorem B5507473 : Blo 1449544 5507473 := bstep (se 2 (by rfl) ⟨2065302, by rfl⟩ : syracuseStep 5507473 = 4130605) B4130605
theorem B7342487 : Blo 1449544 7342487 := bstep (se 1 (by rfl) ⟨5506865, by rfl⟩ : syracuseStep 7342487 = 11013731) B11013731
theorem B2754967 : Blo 1449544 2754967 := bstep (se 1 (by rfl) ⟨2066225, by rfl⟩ : syracuseStep 2754967 = 4132451) B4132451
theorem B6195635 : Blo 1449544 6195635 := bstep (se 1 (by rfl) ⟨4646726, by rfl⟩ : syracuseStep 6195635 = 9293453) B9293453
theorem B3672499 : Blo 1449544 3672499 := bstep (se 1 (by rfl) ⟨2754374, by rfl⟩ : syracuseStep 3672499 = 5508749) B5508749
theorem B3262913 : Blo 1449544 3262913 := bstep (se 2 (by rfl) ⟨1223592, by rfl⟩ : syracuseStep 3262913 = 2447185) B2447185
theorem B13224397 : Blo 1449544 13224397 := bstep (se 3 (by rfl) ⟨2479574, by rfl⟩ : syracuseStep 13224397 = 4959149) B4959149
theorem B2755073 : Blo 1449544 2755073 := bstep (se 2 (by rfl) ⟨1033152, by rfl⟩ : syracuseStep 2755073 = 2066305) B2066305
theorem B3631639 : Blo 1449544 3631639 := bstep (se 1 (by rfl) ⟨2723729, by rfl⟩ : syracuseStep 3631639 = 5447459) B5447459
theorem B1632811 : Blo 1449544 1632811 := bstep (se 1 (by rfl) ⟨1224608, by rfl⟩ : syracuseStep 1632811 = 2449217) B2449217
theorem B3672641 : Blo 1449544 3672641 := bstep (se 2 (by rfl) ⟨1377240, by rfl⟩ : syracuseStep 3672641 = 2754481) B2754481
theorem B18844235 : Blo 1449544 18844235 := bstep (se 1 (by rfl) ⟨14133176, by rfl⟩ : syracuseStep 18844235 = 28266353) B28266353
theorem B11012759 : Blo 1449544 11012759 := bstep (se 1 (by rfl) ⟨8259569, by rfl⟩ : syracuseStep 11012759 = 16519139) B16519139
theorem B1632919 : Blo 1449544 1632919 := bstep (se 1 (by rfl) ⟨1224689, by rfl⟩ : syracuseStep 1632919 = 2449379) B2449379
theorem B3263129 : Blo 1449544 3263129 := bstep (se 2 (by rfl) ⟨1223673, by rfl⟩ : syracuseStep 3263129 = 2447347) B2447347
theorem B2755225 : Blo 1449544 2755225 := bstep (se 2 (by rfl) ⟨1033209, by rfl⟩ : syracuseStep 2755225 = 2066419) B2066419
theorem B5507777 : Blo 1449544 5507777 := bstep (se 2 (by rfl) ⟨2065416, by rfl⟩ : syracuseStep 5507777 = 4130833) B4130833
theorem B3263219 : Blo 1449544 3263219 := bstep (se 1 (by rfl) ⟨2447414, by rfl⟩ : syracuseStep 3263219 = 4894829) B4894829
theorem B19852037 : Blo 1449544 19852037 := bstep (se 4 (by rfl) ⟨1861128, by rfl⟩ : syracuseStep 19852037 = 3722257) B3722257
theorem B3263255 : Blo 1449544 3263255 := bstep (se 1 (by rfl) ⟨2447441, by rfl⟩ : syracuseStep 3263255 = 4894883) B4894883
theorem B5581619 : Blo 1449544 5581619 := bstep (se 1 (by rfl) ⟨4186214, by rfl⟩ : syracuseStep 5581619 = 8372429) B8372429
theorem B6966091 : Blo 1449544 6966091 := bstep (se 1 (by rfl) ⟨5224568, by rfl⟩ : syracuseStep 6966091 = 10449137) B10449137
theorem B4893533 : Blo 1449544 4893533 := bstep (se 3 (by rfl) ⟨917537, by rfl⟩ : syracuseStep 4893533 = 1835075) B1835075
theorem B3263435 : Blo 1449544 3263435 := bstep (se 1 (by rfl) ⟨2447576, by rfl⟩ : syracuseStep 3263435 = 4895153) B4895153
theorem B3263489 : Blo 1449544 3263489 := bstep (se 2 (by rfl) ⟨1223808, by rfl⟩ : syracuseStep 3263489 = 2447617) B2447617
theorem B3918937 : Blo 1449544 3918937 := bstep (se 2 (by rfl) ⟨1469601, by rfl⟩ : syracuseStep 3918937 = 2939203) B2939203
theorem B16526429 : Blo 1449544 16526429 := bstep (se 3 (by rfl) ⟨3098705, by rfl⟩ : syracuseStep 16526429 = 6197411) B6197411
theorem B9423965 : Blo 1449544 9423965 := bstep (se 3 (by rfl) ⟨1766993, by rfl⟩ : syracuseStep 9423965 = 3533987) B3533987
theorem B3099799 : Blo 1449544 3099799 := bstep (se 1 (by rfl) ⟨2324849, by rfl⟩ : syracuseStep 3099799 = 4649699) B4649699
theorem B2354329 : Blo 1449544 2354329 := bstep (se 2 (by rfl) ⟨882873, by rfl⟩ : syracuseStep 2354329 = 1765747) B1765747
theorem B3263705 : Blo 1449544 3263705 := bstep (se 2 (by rfl) ⟨1223889, by rfl⟩ : syracuseStep 3263705 = 2447779) B2447779
theorem B3263795 : Blo 1449544 3263795 := bstep (se 1 (by rfl) ⟨2447846, by rfl⟩ : syracuseStep 3263795 = 4895693) B4895693
theorem B3263831 : Blo 1449544 3263831 := bstep (se 1 (by rfl) ⟨2447873, by rfl⟩ : syracuseStep 3263831 = 4895747) B4895747
theorem B5508445 : Blo 1449544 5508445 := bstep (se 3 (by rfl) ⟨1032833, by rfl⟩ : syracuseStep 5508445 = 2065667) B2065667
theorem B2174411 : Blo 1449544 2174411 := bstep (se 1 (by rfl) ⟨1630808, by rfl⟩ : syracuseStep 2174411 = 3261617) B3261617
theorem B1961419 : Blo 1449544 1961419 := bstep (se 1 (by rfl) ⟨1471064, by rfl⟩ : syracuseStep 1961419 = 2942129) B2942129
theorem B2174423 : Blo 1449544 2174423 := bstep (se 1 (by rfl) ⟨1630817, by rfl⟩ : syracuseStep 2174423 = 3261635) B3261635
theorem B3264011 : Blo 1449544 3264011 := bstep (se 1 (by rfl) ⟨2448008, by rfl⟩ : syracuseStep 3264011 = 4896017) B4896017
theorem B33476113 : Blo 1449544 33476113 := bstep (se 2 (by rfl) ⟨12553542, by rfl⟩ : syracuseStep 33476113 = 25107085) B25107085
theorem B2174489 : Blo 1449544 2174489 := bstep (se 2 (by rfl) ⟨815433, by rfl⟩ : syracuseStep 2174489 = 1630867) B1630867
theorem B4959809 : Blo 1449544 4959809 := bstep (se 2 (by rfl) ⟨1859928, by rfl⟩ : syracuseStep 4959809 = 3719857) B3719857
theorem B3264065 : Blo 1449544 3264065 := bstep (se 2 (by rfl) ⟨1224024, by rfl⟩ : syracuseStep 3264065 = 2448049) B2448049
theorem B4132417 : Blo 1449544 4132417 := bstep (se 2 (by rfl) ⟨1549656, by rfl⟩ : syracuseStep 4132417 = 3099313) B3099313
theorem B13233739 : Blo 1449544 13233739 := bstep (se 1 (by rfl) ⟨9925304, by rfl⟩ : syracuseStep 13233739 = 19850609) B19850609
theorem B2174603 : Blo 1449544 2174603 := bstep (se 1 (by rfl) ⟨1630952, by rfl⟩ : syracuseStep 2174603 = 3261905) B3261905
theorem B2174615 : Blo 1449544 2174615 := bstep (se 1 (by rfl) ⟨1630961, by rfl⟩ : syracuseStep 2174615 = 3261923) B3261923
theorem B3919553 : Blo 1449544 3919553 := bstep (se 2 (by rfl) ⟨1469832, by rfl⟩ : syracuseStep 3919553 = 2939665) B2939665
theorem B2174681 : Blo 1449544 2174681 := bstep (se 2 (by rfl) ⟨815505, by rfl⟩ : syracuseStep 2174681 = 1631011) B1631011
theorem B3264281 : Blo 1449544 3264281 := bstep (se 2 (by rfl) ⟨1224105, by rfl⟩ : syracuseStep 3264281 = 2448211) B2448211
theorem B3673907 : Blo 1449544 3673907 := bstep (se 1 (by rfl) ⟨2755430, by rfl⟩ : syracuseStep 3673907 = 5510861) B5510861
theorem B3919681 : Blo 1449544 3919681 := bstep (se 2 (by rfl) ⟨1469880, by rfl⟩ : syracuseStep 3919681 = 2939761) B2939761
theorem B2174795 : Blo 1449544 2174795 := bstep (se 1 (by rfl) ⟨1631096, by rfl⟩ : syracuseStep 2174795 = 3262193) B3262193
theorem B2174807 : Blo 1449544 2174807 := bstep (se 1 (by rfl) ⟨1631105, by rfl⟩ : syracuseStep 2174807 = 3262211) B3262211
theorem B12390245 : Blo 1449544 12390245 := bstep (se 4 (by rfl) ⟨1161585, by rfl⟩ : syracuseStep 12390245 = 2323171) B2323171
theorem B3264371 : Blo 1449544 3264371 := bstep (se 1 (by rfl) ⟨2448278, by rfl⟩ : syracuseStep 3264371 = 4896557) B4896557
theorem B3264407 : Blo 1449544 3264407 := bstep (se 1 (by rfl) ⟨2448305, by rfl⟩ : syracuseStep 3264407 = 4896611) B4896611
theorem B2174873 : Blo 1449544 2174873 := bstep (se 2 (by rfl) ⟨815577, by rfl⟩ : syracuseStep 2174873 = 1631155) B1631155
theorem B25472945 : Blo 1449544 25472945 := bstep (se 2 (by rfl) ⟨9552354, by rfl⟩ : syracuseStep 25472945 = 19104709) B19104709
theorem B4894667 : Blo 1449544 4894667 := bstep (se 1 (by rfl) ⟨3671000, by rfl⟩ : syracuseStep 4894667 = 7342001) B7342001
theorem B2174987 : Blo 1449544 2174987 := bstep (se 1 (by rfl) ⟨1631240, by rfl⟩ : syracuseStep 2174987 = 3262481) B3262481
theorem B2174999 : Blo 1449544 2174999 := bstep (se 1 (by rfl) ⟨1631249, by rfl⟩ : syracuseStep 2174999 = 3262499) B3262499
theorem B3264587 : Blo 1449544 3264587 := bstep (se 1 (by rfl) ⟨2448440, by rfl⟩ : syracuseStep 3264587 = 4896881) B4896881
theorem B2175065 : Blo 1449544 2175065 := bstep (se 2 (by rfl) ⟨815649, by rfl⟩ : syracuseStep 2175065 = 1631299) B1631299
theorem B3264641 : Blo 1449544 3264641 := bstep (se 2 (by rfl) ⟨1224240, by rfl⟩ : syracuseStep 3264641 = 2448481) B2448481
theorem B6967475 : Blo 1449544 6967475 := bstep (se 1 (by rfl) ⟨5225606, by rfl⟩ : syracuseStep 6967475 = 10451213) B10451213
theorem B2175179 : Blo 1449544 2175179 := bstep (se 1 (by rfl) ⟨1631384, by rfl⟩ : syracuseStep 2175179 = 3262769) B3262769
theorem B23523533 : Blo 1449544 23523533 := bstep (se 3 (by rfl) ⟨4410662, by rfl⟩ : syracuseStep 23523533 = 8821325) B8821325
theorem B2175191 : Blo 1449544 2175191 := bstep (se 1 (by rfl) ⟨1631393, by rfl⟩ : syracuseStep 2175191 = 3262787) B3262787
theorem B4894937 : Blo 1449544 4894937 := bstep (se 2 (by rfl) ⟨1835601, by rfl⟩ : syracuseStep 4894937 = 3671203) B3671203
theorem B2175257 : Blo 1449544 2175257 := bstep (se 2 (by rfl) ⟨815721, by rfl⟩ : syracuseStep 2175257 = 1631443) B1631443
theorem B20918573 : Blo 1449544 20918573 := bstep (se 3 (by rfl) ⟨3922232, by rfl⟩ : syracuseStep 20918573 = 7844465) B7844465
theorem B9417035 : Blo 1449544 9417035 := bstep (se 1 (by rfl) ⟨7062776, by rfl⟩ : syracuseStep 9417035 = 14125553) B14125553
theorem B3264857 : Blo 1449544 3264857 := bstep (se 2 (by rfl) ⟨1224321, by rfl⟩ : syracuseStep 3264857 = 2448643) B2448643
theorem B2175371 : Blo 1449544 2175371 := bstep (se 1 (by rfl) ⟨1631528, by rfl⟩ : syracuseStep 2175371 = 3263057) B3263057
theorem B2175383 : Blo 1449544 2175383 := bstep (se 1 (by rfl) ⟨1631537, by rfl⟩ : syracuseStep 2175383 = 3263075) B3263075
theorem B3264947 : Blo 1449544 3264947 := bstep (se 1 (by rfl) ⟨2448710, by rfl⟩ : syracuseStep 3264947 = 4897421) B4897421
theorem B5231027 : Blo 1449544 5231027 := bstep (se 1 (by rfl) ⟨3923270, by rfl⟩ : syracuseStep 5231027 = 7846541) B7846541
theorem B3264983 : Blo 1449544 3264983 := bstep (se 1 (by rfl) ⟨2448737, by rfl⟩ : syracuseStep 3264983 = 4897475) B4897475
theorem B2175449 : Blo 1449544 2175449 := bstep (se 2 (by rfl) ⟨815793, by rfl⟩ : syracuseStep 2175449 = 1631587) B1631587
theorem B2175563 : Blo 1449544 2175563 := bstep (se 1 (by rfl) ⟨1631672, by rfl⟩ : syracuseStep 2175563 = 3263345) B3263345
theorem B2175575 : Blo 1449544 2175575 := bstep (se 1 (by rfl) ⟨1631681, by rfl⟩ : syracuseStep 2175575 = 3263363) B3263363
theorem B5509721 : Blo 1449544 5509721 := bstep (se 2 (by rfl) ⟨2066145, by rfl⟩ : syracuseStep 5509721 = 4132291) B4132291
theorem B21189251 : Blo 1449544 21189251 := bstep (se 1 (by rfl) ⟨15891938, by rfl⟩ : syracuseStep 21189251 = 31783877) B31783877
theorem B3265163 : Blo 1449544 3265163 := bstep (se 1 (by rfl) ⟨2448872, by rfl⟩ : syracuseStep 3265163 = 4897745) B4897745
theorem B2175641 : Blo 1449544 2175641 := bstep (se 2 (by rfl) ⟨815865, by rfl⟩ : syracuseStep 2175641 = 1631731) B1631731
theorem B5878451 : Blo 1449544 5878451 := bstep (se 1 (by rfl) ⟨4408838, by rfl⟩ : syracuseStep 5878451 = 8817677) B8817677
theorem B3265217 : Blo 1449544 3265217 := bstep (se 2 (by rfl) ⟨1224456, by rfl⟩ : syracuseStep 3265217 = 2448913) B2448913
theorem B2175755 : Blo 1449544 2175755 := bstep (se 1 (by rfl) ⟨1631816, by rfl⟩ : syracuseStep 2175755 = 3263633) B3263633
theorem B2175767 : Blo 1449544 2175767 := bstep (se 1 (by rfl) ⟨1631825, by rfl⟩ : syracuseStep 2175767 = 3263651) B3263651
theorem B2175833 : Blo 1449544 2175833 := bstep (se 2 (by rfl) ⟨815937, by rfl⟩ : syracuseStep 2175833 = 1631875) B1631875
theorem B5583761 : Blo 1449544 5583761 := bstep (se 2 (by rfl) ⟨2093910, by rfl⟩ : syracuseStep 5583761 = 4187821) B4187821
theorem B4895639 : Blo 1449544 4895639 := bstep (se 1 (by rfl) ⟨3671729, by rfl⟩ : syracuseStep 4895639 = 7343459) B7343459
theorem B3265433 : Blo 1449544 3265433 := bstep (se 2 (by rfl) ⟨1224537, by rfl⟩ : syracuseStep 3265433 = 2449075) B2449075
theorem B2175947 : Blo 1449544 2175947 := bstep (se 1 (by rfl) ⟨1631960, by rfl⟩ : syracuseStep 2175947 = 3263921) B3263921
theorem B2175959 : Blo 1449544 2175959 := bstep (se 1 (by rfl) ⟨1631969, by rfl⟩ : syracuseStep 2175959 = 3263939) B3263939
theorem B3265523 : Blo 1449544 3265523 := bstep (se 1 (by rfl) ⟨2449142, by rfl⟩ : syracuseStep 3265523 = 4898285) B4898285
theorem B3265559 : Blo 1449544 3265559 := bstep (se 1 (by rfl) ⟨2449169, by rfl⟩ : syracuseStep 3265559 = 4898339) B4898339
theorem B4650007 : Blo 1449544 4650007 := bstep (se 1 (by rfl) ⟨3487505, by rfl⟩ : syracuseStep 4650007 = 6975011) B6975011
theorem B2176025 : Blo 1449544 2176025 := bstep (se 2 (by rfl) ⟨816009, by rfl⟩ : syracuseStep 2176025 = 1632019) B1632019
theorem B6198403 : Blo 1449544 6198403 := bstep (se 1 (by rfl) ⟨4648802, by rfl⟩ : syracuseStep 6198403 = 9297605) B9297605
theorem B2176139 : Blo 1449544 2176139 := bstep (se 1 (by rfl) ⟨1632104, by rfl⟩ : syracuseStep 2176139 = 3264209) B3264209
theorem B2176151 : Blo 1449544 2176151 := bstep (se 1 (by rfl) ⟨1632113, by rfl⟩ : syracuseStep 2176151 = 3264227) B3264227
theorem B1987787 : Blo 1449544 1987787 := bstep (se 1 (by rfl) ⟨1490840, by rfl⟩ : syracuseStep 1987787 = 2981681) B2981681
theorem B3265739 : Blo 1449544 3265739 := bstep (se 1 (by rfl) ⟨2449304, by rfl⟩ : syracuseStep 3265739 = 4898609) B4898609
theorem B2176217 : Blo 1449544 2176217 := bstep (se 2 (by rfl) ⟨816081, by rfl⟩ : syracuseStep 2176217 = 1632163) B1632163
theorem B6616285 : Blo 1449544 6616285 := bstep (se 3 (by rfl) ⟨1240553, by rfl⟩ : syracuseStep 6616285 = 2481107) B2481107
theorem B3265793 : Blo 1449544 3265793 := bstep (se 2 (by rfl) ⟨1224672, by rfl⟩ : syracuseStep 3265793 = 2449345) B2449345
theorem B2176331 : Blo 1449544 2176331 := bstep (se 1 (by rfl) ⟨1632248, by rfl⟩ : syracuseStep 2176331 = 3264497) B3264497
theorem B2446679 : Blo 1449544 2446679 := bstep (se 1 (by rfl) ⟨1835009, by rfl⟩ : syracuseStep 2446679 = 3670019) B3670019
theorem B2176343 : Blo 1449544 2176343 := bstep (se 1 (by rfl) ⟨1632257, by rfl⟩ : syracuseStep 2176343 = 3264515) B3264515
theorem B2176409 : Blo 1449544 2176409 := bstep (se 2 (by rfl) ⟨816153, by rfl⟩ : syracuseStep 2176409 = 1632307) B1632307
theorem B4896179 : Blo 1449544 4896179 := bstep (se 1 (by rfl) ⟨3672134, by rfl⟩ : syracuseStep 4896179 = 7344269) B7344269
theorem B2446807 : Blo 1449544 2446807 := bstep (se 1 (by rfl) ⟨1835105, by rfl⟩ : syracuseStep 2446807 = 3670211) B3670211
theorem B2323927 : Blo 1449544 2323927 := bstep (se 1 (by rfl) ⟨1742945, by rfl⟩ : syracuseStep 2323927 = 3485891) B3485891
theorem B2176523 : Blo 1449544 2176523 := bstep (se 1 (by rfl) ⟨1632392, by rfl⟩ : syracuseStep 2176523 = 3264785) B3264785
theorem B2176535 : Blo 1449544 2176535 := bstep (se 1 (by rfl) ⟨1632401, by rfl⟩ : syracuseStep 2176535 = 3264803) B3264803
theorem B2176601 : Blo 1449544 2176601 := bstep (se 2 (by rfl) ⟨816225, by rfl⟩ : syracuseStep 2176601 = 1632451) B1632451
theorem B8492645 : Blo 1449544 8492645 := bstep (se 4 (by rfl) ⟨796185, by rfl⟩ : syracuseStep 8492645 = 1592371) B1592371
theorem B4896449 : Blo 1449544 4896449 := bstep (se 2 (by rfl) ⟨1836168, by rfl⟩ : syracuseStep 4896449 = 3672337) B3672337
theorem B2176715 : Blo 1449544 2176715 := bstep (se 1 (by rfl) ⟨1632536, by rfl⟩ : syracuseStep 2176715 = 3265073) B3265073
theorem B2176727 : Blo 1449544 2176727 := bstep (se 1 (by rfl) ⟨1632545, by rfl⟩ : syracuseStep 2176727 = 3265091) B3265091
theorem B2176793 : Blo 1449544 2176793 := bstep (se 2 (by rfl) ⟨816297, by rfl⟩ : syracuseStep 2176793 = 1632595) B1632595
theorem B7346051 : Blo 1449544 7346051 := bstep (se 1 (by rfl) ⟨5509538, by rfl⟩ : syracuseStep 7346051 = 11019077) B11019077
theorem B2176907 : Blo 1449544 2176907 := bstep (se 1 (by rfl) ⟨1632680, by rfl⟩ : syracuseStep 2176907 = 3265361) B3265361
theorem B2176919 : Blo 1449544 2176919 := bstep (se 1 (by rfl) ⟨1632689, by rfl⟩ : syracuseStep 2176919 = 3265379) B3265379
theorem B2176985 : Blo 1449544 2176985 := bstep (se 2 (by rfl) ⟨816369, by rfl⟩ : syracuseStep 2176985 = 1632739) B1632739
theorem B6969361 : Blo 1449544 6969361 := bstep (se 2 (by rfl) ⟨2613510, by rfl⟩ : syracuseStep 6969361 = 5227021) B5227021
theorem B6199361 : Blo 1449544 6199361 := bstep (se 2 (by rfl) ⟨2324760, by rfl⟩ : syracuseStep 6199361 = 4649521) B4649521
theorem B2447435 : Blo 1449544 2447435 := bstep (se 1 (by rfl) ⟨1835576, by rfl⟩ : syracuseStep 2447435 = 3671153) B3671153
theorem B2177099 : Blo 1449544 2177099 := bstep (se 1 (by rfl) ⟨1632824, by rfl⟩ : syracuseStep 2177099 = 3265649) B3265649
theorem B2177111 : Blo 1449544 2177111 := bstep (se 1 (by rfl) ⟨1632833, by rfl⟩ : syracuseStep 2177111 = 3265667) B3265667
theorem B2177177 : Blo 1449544 2177177 := bstep (se 2 (by rfl) ⟨816441, by rfl⟩ : syracuseStep 2177177 = 1632883) B1632883
theorem B2447563 : Blo 1449544 2447563 := bstep (se 1 (by rfl) ⟨1835672, by rfl⟩ : syracuseStep 2447563 = 3671345) B3671345
theorem B10885337 : Blo 1449544 10885337 := bstep (se 2 (by rfl) ⟨4082001, by rfl⟩ : syracuseStep 10885337 = 8164003) B8164003
theorem B4896989 : Blo 1449544 4896989 := bstep (se 3 (by rfl) ⟨918185, by rfl⟩ : syracuseStep 4896989 = 1836371) B1836371
theorem B2324747 : Blo 1449544 2324747 := bstep (se 1 (by rfl) ⟨1743560, by rfl⟩ : syracuseStep 2324747 = 3487121) B3487121
theorem B2177291 : Blo 1449544 2177291 := bstep (se 1 (by rfl) ⟨1632968, by rfl⟩ : syracuseStep 2177291 = 3265937) B3265937
theorem B2177303 : Blo 1449544 2177303 := bstep (se 1 (by rfl) ⟨1632977, by rfl⟩ : syracuseStep 2177303 = 3265955) B3265955
theorem B8255789 : Blo 1449544 8255789 := bstep (se 3 (by rfl) ⟨1547960, by rfl⟩ : syracuseStep 8255789 = 3095921) B3095921
theorem B2447705 : Blo 1449544 2447705 := bstep (se 2 (by rfl) ⟨917889, by rfl⟩ : syracuseStep 2447705 = 1835779) B1835779
theorem B13236659 : Blo 1449544 13236659 := bstep (se 1 (by rfl) ⟨9927494, by rfl⟩ : syracuseStep 13236659 = 19854989) B19854989
theorem B12392909 : Blo 1449544 12392909 := bstep (se 3 (by rfl) ⟨2323670, by rfl⟩ : syracuseStep 12392909 = 4647341) B4647341
theorem B2447833 : Blo 1449544 2447833 := bstep (se 2 (by rfl) ⟨917937, by rfl⟩ : syracuseStep 2447833 = 1835875) B1835875
theorem B3922397 : Blo 1449544 3922397 := bstep (se 3 (by rfl) ⟨735449, by rfl⟩ : syracuseStep 3922397 = 1470899) B1470899
theorem B2325017 : Blo 1449544 2325017 := bstep (se 2 (by rfl) ⟨871881, by rfl⟩ : syracuseStep 2325017 = 1743763) B1743763
theorem B5880365 : Blo 1449544 5880365 := bstep (se 3 (by rfl) ⟨1102568, by rfl⟩ : syracuseStep 5880365 = 2205137) B2205137
theorem B7445171 : Blo 1449544 7445171 := bstep (se 1 (by rfl) ⟨5583878, by rfl⟩ : syracuseStep 7445171 = 11167757) B11167757
theorem B5503889 : Blo 1449544 5503889 := bstep (se 2 (by rfl) ⟨2063958, by rfl⟩ : syracuseStep 5503889 = 4127917) B4127917
theorem B5880755 : Blo 1449544 5880755 := bstep (se 1 (by rfl) ⟨4410566, by rfl⟩ : syracuseStep 5880755 = 8821133) B8821133
theorem B6192065 : Blo 1449544 6192065 := bstep (se 2 (by rfl) ⟨2322024, by rfl⟩ : syracuseStep 6192065 = 4644049) B4644049
theorem B2448407 : Blo 1449544 2448407 := bstep (se 1 (by rfl) ⟨1836305, by rfl⟩ : syracuseStep 2448407 = 3672611) B3672611
theorem B6192217 : Blo 1449544 6192217 := bstep (se 2 (by rfl) ⟨2322081, by rfl⟩ : syracuseStep 6192217 = 4644163) B4644163
theorem B2448535 : Blo 1449544 2448535 := bstep (se 1 (by rfl) ⟨1836401, by rfl⟩ : syracuseStep 2448535 = 3672803) B3672803
theorem B8264855 : Blo 1449544 8264855 := bstep (se 1 (by rfl) ⟨6198641, by rfl⟩ : syracuseStep 8264855 = 12397283) B12397283
theorem B2235595 : Blo 1449544 2235595 := bstep (se 1 (by rfl) ⟨1676696, by rfl⟩ : syracuseStep 2235595 = 3353393) B3353393
theorem B3669209 : Blo 1449544 3669209 := bstep (se 2 (by rfl) ⟨1375953, by rfl⟩ : syracuseStep 3669209 = 2751907) B2751907
theorem B5881049 : Blo 1449544 5881049 := bstep (se 2 (by rfl) ⟨2205393, by rfl⟩ : syracuseStep 5881049 = 4410787) B4410787
theorem B26475821 : Blo 1449544 26475821 := bstep (se 3 (by rfl) ⟨4964216, by rfl⟩ : syracuseStep 26475821 = 9928433) B9928433
theorem B4898123 : Blo 1449544 4898123 := bstep (se 1 (by rfl) ⟨3673592, by rfl⟩ : syracuseStep 4898123 = 7347185) B7347185
theorem B5504345 : Blo 1449544 5504345 := bstep (se 2 (by rfl) ⟨2064129, by rfl⟩ : syracuseStep 5504345 = 4128259) B4128259
theorem B4644317 : Blo 1449544 4644317 := bstep (se 3 (by rfl) ⟨870809, by rfl⟩ : syracuseStep 4644317 = 1741619) B1741619
theorem B5504557 : Blo 1449544 5504557 := bstep (se 3 (by rfl) ⟨1032104, by rfl⟩ : syracuseStep 5504557 = 2064209) B2064209
theorem B2752051 : Blo 1449544 2752051 := bstep (se 1 (by rfl) ⟨2064038, by rfl⟩ : syracuseStep 2752051 = 4128077) B4128077
theorem B1449547 : Blo 1449544 1449547 := bstep (se 1 (by rfl) ⟨1087160, by rfl⟩ : syracuseStep 1449547 = 2174321) B2174321
theorem B1449559 : Blo 1449544 1449559 := bstep (se 1 (by rfl) ⟨1087169, by rfl⟩ : syracuseStep 1449559 = 2174339) B2174339
theorem B4898393 : Blo 1449544 4898393 := bstep (se 2 (by rfl) ⟨1836897, by rfl⟩ : syracuseStep 4898393 = 3673795) B3673795
theorem B1449579 : Blo 1449544 1449579 := bstep (se 1 (by rfl) ⟨1087184, by rfl⟩ : syracuseStep 1449579 = 2174369) B2174369
theorem B1449591 : Blo 1449544 1449591 := bstep (se 1 (by rfl) ⟨1087193, by rfl⟩ : syracuseStep 1449591 = 2174387) B2174387
theorem B1449611 : Blo 1449544 1449611 := bstep (se 1 (by rfl) ⟨1087208, by rfl⟩ : syracuseStep 1449611 = 2174417) B2174417
theorem B1449623 : Blo 1449544 1449623 := bstep (se 1 (by rfl) ⟨1087217, by rfl⟩ : syracuseStep 1449623 = 2174435) B2174435
theorem B1449643 : Blo 1449544 1449643 := bstep (se 1 (by rfl) ⟨1087232, by rfl⟩ : syracuseStep 1449643 = 2174465) B2174465
theorem B1449655 : Blo 1449544 1449655 := bstep (se 1 (by rfl) ⟨1087241, by rfl⟩ : syracuseStep 1449655 = 2174483) B2174483
theorem B1449675 : Blo 1449544 1449675 := bstep (se 1 (by rfl) ⟨1087256, by rfl⟩ : syracuseStep 1449675 = 2174513) B2174513
theorem B16514765 : Blo 1449544 16514765 := bstep (se 3 (by rfl) ⟨3096518, by rfl⟩ : syracuseStep 16514765 = 6193037) B6193037
theorem B1449687 : Blo 1449544 1449687 := bstep (se 1 (by rfl) ⟨1087265, by rfl⟩ : syracuseStep 1449687 = 2174531) B2174531
theorem B7839449 : Blo 1449544 7839449 := bstep (se 2 (by rfl) ⟨2939793, by rfl⟩ : syracuseStep 7839449 = 5879587) B5879587
theorem B1449707 : Blo 1449544 1449707 := bstep (se 1 (by rfl) ⟨1087280, by rfl⟩ : syracuseStep 1449707 = 2174561) B2174561
theorem B1449719 : Blo 1449544 1449719 := bstep (se 1 (by rfl) ⟨1087289, by rfl⟩ : syracuseStep 1449719 = 2174579) B2174579
theorem B2793217 : Blo 1449544 2793217 := bstep (se 2 (by rfl) ⟨1047456, by rfl⟩ : syracuseStep 2793217 = 2094913) B2094913
theorem B1449739 : Blo 1449544 1449739 := bstep (se 1 (by rfl) ⟨1087304, by rfl⟩ : syracuseStep 1449739 = 2174609) B2174609
theorem B2449163 : Blo 1449544 2449163 := bstep (se 1 (by rfl) ⟨1836872, by rfl⟩ : syracuseStep 2449163 = 3673745) B3673745
theorem B1449751 : Blo 1449544 1449751 := bstep (se 1 (by rfl) ⟨1087313, by rfl⟩ : syracuseStep 1449751 = 2174627) B2174627
theorem B1449771 : Blo 1449544 1449771 := bstep (se 1 (by rfl) ⟨1087328, by rfl⟩ : syracuseStep 1449771 = 2174657) B2174657
theorem B1449783 : Blo 1449544 1449783 := bstep (se 1 (by rfl) ⟨1087337, by rfl⟩ : syracuseStep 1449783 = 2174675) B2174675
theorem B1449803 : Blo 1449544 1449803 := bstep (se 1 (by rfl) ⟨1087352, by rfl⟩ : syracuseStep 1449803 = 2174705) B2174705
theorem B1548119 : Blo 1449544 1548119 := bstep (se 1 (by rfl) ⟨1161089, by rfl⟩ : syracuseStep 1548119 = 2322179) B2322179
theorem B1449815 : Blo 1449544 1449815 := bstep (se 1 (by rfl) ⟨1087361, by rfl⟩ : syracuseStep 1449815 = 2174723) B2174723
theorem B5504861 : Blo 1449544 5504861 := bstep (se 3 (by rfl) ⟨1032161, by rfl⟩ : syracuseStep 5504861 = 2064323) B2064323
theorem B9297757 : Blo 1449544 9297757 := bstep (se 3 (by rfl) ⟨1743329, by rfl⟩ : syracuseStep 9297757 = 3486659) B3486659
theorem B1449835 : Blo 1449544 1449835 := bstep (se 1 (by rfl) ⟨1087376, by rfl⟩ : syracuseStep 1449835 = 2174753) B2174753
theorem B2613107 : Blo 1449544 2613107 := bstep (se 1 (by rfl) ⟨1959830, by rfl⟩ : syracuseStep 2613107 = 3919661) B3919661
theorem B1449847 : Blo 1449544 1449847 := bstep (se 1 (by rfl) ⟨1087385, by rfl⟩ : syracuseStep 1449847 = 2174771) B2174771
theorem B1449867 : Blo 1449544 1449867 := bstep (se 1 (by rfl) ⟨1087400, by rfl⟩ : syracuseStep 1449867 = 2174801) B2174801
theorem B2449291 : Blo 1449544 2449291 := bstep (se 1 (by rfl) ⟨1836968, by rfl⟩ : syracuseStep 2449291 = 3673937) B3673937
theorem B1834903 : Blo 1449544 1834903 := bstep (se 1 (by rfl) ⟨1376177, by rfl⟩ : syracuseStep 1834903 = 2752355) B2752355
theorem B1449879 : Blo 1449544 1449879 := bstep (se 1 (by rfl) ⟨1087409, by rfl⟩ : syracuseStep 1449879 = 2174819) B2174819
theorem B1449899 : Blo 1449544 1449899 := bstep (se 1 (by rfl) ⟨1087424, by rfl⟩ : syracuseStep 1449899 = 2174849) B2174849
theorem B4718515 : Blo 1449544 4718515 := bstep (se 1 (by rfl) ⟨3538886, by rfl⟩ : syracuseStep 4718515 = 7077773) B7077773
theorem B1449911 : Blo 1449544 1449911 := bstep (se 1 (by rfl) ⟨1087433, by rfl⟩ : syracuseStep 1449911 = 2174867) B2174867
theorem B1449931 : Blo 1449544 1449931 := bstep (se 1 (by rfl) ⟨1087448, by rfl⟩ : syracuseStep 1449931 = 2174897) B2174897
theorem B1449943 : Blo 1449544 1449943 := bstep (se 1 (by rfl) ⟨1087457, by rfl⟩ : syracuseStep 1449943 = 2174915) B2174915
theorem B2940889 : Blo 1449544 2940889 := bstep (se 2 (by rfl) ⟨1102833, by rfl⟩ : syracuseStep 2940889 = 2205667) B2205667
theorem B1449963 : Blo 1449544 1449963 := bstep (se 1 (by rfl) ⟨1087472, by rfl⟩ : syracuseStep 1449963 = 2174945) B2174945
theorem B1449975 : Blo 1449544 1449975 := bstep (se 1 (by rfl) ⟨1087481, by rfl⟩ : syracuseStep 1449975 = 2174963) B2174963
theorem B1449991 : Blo 1449544 1449991 := bstep (se 1 (by rfl) ⟨1087493, by rfl⟩ : syracuseStep 1449991 = 2174987) B2174987
theorem B1449999 : Blo 1449544 1449999 := bstep (se 1 (by rfl) ⟨1087499, by rfl⟩ : syracuseStep 1449999 = 2174999) B2174999
theorem B8257565 : Blo 1449544 8257565 := bstep (se 3 (by rfl) ⟨1548293, by rfl⟩ : syracuseStep 8257565 = 3096587) B3096587
theorem B3670049 : Blo 1449544 3670049 := bstep (se 2 (by rfl) ⟨1376268, by rfl⟩ : syracuseStep 3670049 = 2752537) B2752537
theorem B1450043 : Blo 1449544 1450043 := bstep (se 1 (by rfl) ⟨1087532, by rfl⟩ : syracuseStep 1450043 = 2175065) B2175065
theorem B4644983 : Blo 1449544 4644983 := bstep (se 1 (by rfl) ⟨3483737, by rfl⟩ : syracuseStep 4644983 = 6967475) B6967475
theorem B1450119 : Blo 1449544 1450119 := bstep (se 1 (by rfl) ⟨1087589, by rfl⟩ : syracuseStep 1450119 = 2175179) B2175179
theorem B1450127 : Blo 1449544 1450127 := bstep (se 1 (by rfl) ⟨1087595, by rfl⟩ : syracuseStep 1450127 = 2175191) B2175191
theorem B2752697 : Blo 1449544 2752697 := bstep (se 2 (by rfl) ⟨1032261, by rfl⟩ : syracuseStep 2752697 = 2064523) B2064523
theorem B1450171 : Blo 1449544 1450171 := bstep (se 1 (by rfl) ⟨1087628, by rfl⟩ : syracuseStep 1450171 = 2175257) B2175257
theorem B2064631 : Blo 1449544 2064631 := bstep (se 1 (by rfl) ⟨1548473, by rfl⟩ : syracuseStep 2064631 = 3096947) B3096947
theorem B1450247 : Blo 1449544 1450247 := bstep (se 1 (by rfl) ⟨1087685, by rfl⟩ : syracuseStep 1450247 = 2175371) B2175371
theorem B1450255 : Blo 1449544 1450255 := bstep (se 1 (by rfl) ⟨1087691, by rfl⟩ : syracuseStep 1450255 = 2175383) B2175383
theorem B1450299 : Blo 1449544 1450299 := bstep (se 1 (by rfl) ⟨1087724, by rfl⟩ : syracuseStep 1450299 = 2175449) B2175449
theorem B1835399 : Blo 1449544 1835399 := bstep (se 1 (by rfl) ⟨1376549, by rfl⟩ : syracuseStep 1835399 = 2753099) B2753099
theorem B1450375 : Blo 1449544 1450375 := bstep (se 1 (by rfl) ⟨1087781, by rfl⟩ : syracuseStep 1450375 = 2175563) B2175563
theorem B1450383 : Blo 1449544 1450383 := bstep (se 1 (by rfl) ⟨1087787, by rfl⟩ : syracuseStep 1450383 = 2175575) B2175575
theorem B1450427 : Blo 1449544 1450427 := bstep (se 1 (by rfl) ⟨1087820, by rfl⟩ : syracuseStep 1450427 = 2175641) B2175641
theorem B1450503 : Blo 1449544 1450503 := bstep (se 1 (by rfl) ⟨1087877, by rfl⟩ : syracuseStep 1450503 = 2175755) B2175755
theorem B1450511 : Blo 1449544 1450511 := bstep (se 1 (by rfl) ⟨1087883, by rfl⟩ : syracuseStep 1450511 = 2175767) B2175767
theorem B5300765 : Blo 1449544 5300765 := bstep (se 3 (by rfl) ⟨993893, by rfl⟩ : syracuseStep 5300765 = 1987787) B1987787
theorem B1450555 : Blo 1449544 1450555 := bstep (se 1 (by rfl) ⟨1087916, by rfl⟩ : syracuseStep 1450555 = 2175833) B2175833
theorem B1450631 : Blo 1449544 1450631 := bstep (se 1 (by rfl) ⟨1087973, by rfl⟩ : syracuseStep 1450631 = 2175947) B2175947
theorem B1450639 : Blo 1449544 1450639 := bstep (se 1 (by rfl) ⟨1087979, by rfl⟩ : syracuseStep 1450639 = 2175959) B2175959
theorem B1450683 : Blo 1449544 1450683 := bstep (se 1 (by rfl) ⟨1088012, by rfl⟩ : syracuseStep 1450683 = 2176025) B2176025
theorem B4842185 : Blo 1449544 4842185 := bstep (se 2 (by rfl) ⟨1815819, by rfl⟩ : syracuseStep 4842185 = 3631639) B3631639
theorem B1450759 : Blo 1449544 1450759 := bstep (se 1 (by rfl) ⟨1088069, by rfl⟩ : syracuseStep 1450759 = 2176139) B2176139
theorem B1450767 : Blo 1449544 1450767 := bstep (se 1 (by rfl) ⟨1088075, by rfl⟩ : syracuseStep 1450767 = 2176151) B2176151
theorem B16532261 : Blo 1449544 16532261 := bstep (se 4 (by rfl) ⟨1549899, by rfl⟩ : syracuseStep 16532261 = 3099799) B3099799
theorem B6193979 : Blo 1449544 6193979 := bstep (se 1 (by rfl) ⟨4645484, by rfl⟩ : syracuseStep 6193979 = 9290969) B9290969
theorem B1450811 : Blo 1449544 1450811 := bstep (se 1 (by rfl) ⟨1088108, by rfl⟩ : syracuseStep 1450811 = 2176217) B2176217
theorem B1450887 : Blo 1449544 1450887 := bstep (se 1 (by rfl) ⟨1088165, by rfl⟩ : syracuseStep 1450887 = 2176331) B2176331
theorem B1631119 : Blo 1449544 1631119 := bstep (se 1 (by rfl) ⟨1223339, by rfl⟩ : syracuseStep 1631119 = 2446679) B2446679
theorem B1450895 : Blo 1449544 1450895 := bstep (se 1 (by rfl) ⟨1088171, by rfl⟩ : syracuseStep 1450895 = 2176343) B2176343
theorem B1450939 : Blo 1449544 1450939 := bstep (se 1 (by rfl) ⟨1088204, by rfl⟩ : syracuseStep 1450939 = 2176409) B2176409
theorem B5506001 : Blo 1449544 5506001 := bstep (se 2 (by rfl) ⟨2064750, by rfl⟩ : syracuseStep 5506001 = 4129501) B4129501
theorem B3671041 : Blo 1449544 3671041 := bstep (se 2 (by rfl) ⟨1376640, by rfl⟩ : syracuseStep 3671041 = 2753281) B2753281
theorem B1451015 : Blo 1449544 1451015 := bstep (se 1 (by rfl) ⟨1088261, by rfl⟩ : syracuseStep 1451015 = 2176523) B2176523
theorem B1836047 : Blo 1449544 1836047 := bstep (se 1 (by rfl) ⟨1377035, by rfl⟩ : syracuseStep 1836047 = 2754071) B2754071
theorem B1451023 : Blo 1449544 1451023 := bstep (se 1 (by rfl) ⟨1088267, by rfl⟩ : syracuseStep 1451023 = 2176535) B2176535
theorem B1451067 : Blo 1449544 1451067 := bstep (se 1 (by rfl) ⟨1088300, by rfl⟩ : syracuseStep 1451067 = 2176601) B2176601
theorem B18596951 : Blo 1449544 18596951 := bstep (se 1 (by rfl) ⟨13947713, by rfl⟩ : syracuseStep 18596951 = 27895427) B27895427
theorem B1451143 : Blo 1449544 1451143 := bstep (se 1 (by rfl) ⟨1088357, by rfl⟩ : syracuseStep 1451143 = 2176715) B2176715
theorem B1451151 : Blo 1449544 1451151 := bstep (se 1 (by rfl) ⟨1088363, by rfl⟩ : syracuseStep 1451151 = 2176727) B2176727
theorem B1451195 : Blo 1449544 1451195 := bstep (se 1 (by rfl) ⟨1088396, by rfl⟩ : syracuseStep 1451195 = 2176793) B2176793
theorem B1451271 : Blo 1449544 1451271 := bstep (se 1 (by rfl) ⟨1088453, by rfl⟩ : syracuseStep 1451271 = 2176907) B2176907
theorem B5506319 : Blo 1449544 5506319 := bstep (se 1 (by rfl) ⟨4129739, by rfl⟩ : syracuseStep 5506319 = 8259479) B8259479
theorem B1451279 : Blo 1449544 1451279 := bstep (se 1 (by rfl) ⟨1088459, by rfl⟩ : syracuseStep 1451279 = 2176919) B2176919
theorem B2753851 : Blo 1449544 2753851 := bstep (se 1 (by rfl) ⟨2065388, by rfl⟩ : syracuseStep 2753851 = 4130777) B4130777
theorem B1451323 : Blo 1449544 1451323 := bstep (se 1 (by rfl) ⟨1088492, by rfl⟩ : syracuseStep 1451323 = 2176985) B2176985
theorem B3261815 : Blo 1449544 3261815 := bstep (se 1 (by rfl) ⟨2446361, by rfl⟩ : syracuseStep 3261815 = 4892723) B4892723
theorem B1631623 : Blo 1449544 1631623 := bstep (se 1 (by rfl) ⟨1223717, by rfl⟩ : syracuseStep 1631623 = 2447435) B2447435
theorem B1451399 : Blo 1449544 1451399 := bstep (se 1 (by rfl) ⟨1088549, by rfl⟩ : syracuseStep 1451399 = 2177099) B2177099
theorem B1451407 : Blo 1449544 1451407 := bstep (se 1 (by rfl) ⟨1088555, by rfl⟩ : syracuseStep 1451407 = 2177111) B2177111
theorem B1451451 : Blo 1449544 1451451 := bstep (se 1 (by rfl) ⟨1088588, by rfl⟩ : syracuseStep 1451451 = 2177177) B2177177
theorem B7341515 : Blo 1449544 7341515 := bstep (se 1 (by rfl) ⟨5506136, by rfl⟩ : syracuseStep 7341515 = 11012273) B11012273
theorem B1451527 : Blo 1449544 1451527 := bstep (se 1 (by rfl) ⟨1088645, by rfl⟩ : syracuseStep 1451527 = 2177291) B2177291
theorem B1451535 : Blo 1449544 1451535 := bstep (se 1 (by rfl) ⟨1088651, by rfl⟩ : syracuseStep 1451535 = 2177303) B2177303
theorem B3139105 : Blo 1449544 3139105 := bstep (se 2 (by rfl) ⟨1177164, by rfl⟩ : syracuseStep 3139105 = 2354329) B2354329
theorem B3261995 : Blo 1449544 3261995 := bstep (se 1 (by rfl) ⟨2446496, by rfl⟩ : syracuseStep 3261995 = 4892993) B4892993
theorem B1631803 : Blo 1449544 1631803 := bstep (se 1 (by rfl) ⟨1223852, by rfl⟩ : syracuseStep 1631803 = 2447705) B2447705
theorem B3671639 : Blo 1449544 3671639 := bstep (se 1 (by rfl) ⟨2753729, by rfl⟩ : syracuseStep 3671639 = 5507459) B5507459
theorem B4130423 : Blo 1449544 4130423 := bstep (se 1 (by rfl) ⟨3097817, by rfl⟩ : syracuseStep 4130423 = 6195635) B6195635
theorem B8824439 : Blo 1449544 8824439 := bstep (se 1 (by rfl) ⟨6618329, by rfl⟩ : syracuseStep 8824439 = 13236659) B13236659
theorem B2614931 : Blo 1449544 2614931 := bstep (se 1 (by rfl) ⟨1961198, by rfl⟩ : syracuseStep 2614931 = 3922397) B3922397
theorem B1550011 : Blo 1449544 1550011 := bstep (se 1 (by rfl) ⟨1162508, by rfl⟩ : syracuseStep 1550011 = 2325017) B2325017
theorem B7341839 : Blo 1449544 7341839 := bstep (se 1 (by rfl) ⟨5506379, by rfl⟩ : syracuseStep 7341839 = 11012759) B11012759
theorem B2754337 : Blo 1449544 2754337 := bstep (se 2 (by rfl) ⟨1032876, by rfl⟩ : syracuseStep 2754337 = 2065753) B2065753
theorem B3671851 : Blo 1449544 3671851 := bstep (se 1 (by rfl) ⟨2753888, by rfl⟩ : syracuseStep 3671851 = 5507777) B5507777
theorem B3721079 : Blo 1449544 3721079 := bstep (se 1 (by rfl) ⟨2790809, by rfl⟩ : syracuseStep 3721079 = 5581619) B5581619
theorem B3262355 : Blo 1449544 3262355 := bstep (se 1 (by rfl) ⟨2446766, by rfl⟩ : syracuseStep 3262355 = 4893533) B4893533
theorem B3671993 : Blo 1449544 3671993 := bstep (se 2 (by rfl) ⟨1376997, by rfl⟩ : syracuseStep 3671993 = 2753995) B2753995
theorem B2615225 : Blo 1449544 2615225 := bstep (se 2 (by rfl) ⟨980709, by rfl⟩ : syracuseStep 2615225 = 1961419) B1961419
theorem B3262409 : Blo 1449544 3262409 := bstep (se 2 (by rfl) ⟨1223403, by rfl⟩ : syracuseStep 3262409 = 2446807) B2446807
theorem B3098569 : Blo 1449544 3098569 := bstep (se 2 (by rfl) ⟨1161963, by rfl⟩ : syracuseStep 3098569 = 2323927) B2323927
theorem B1632271 : Blo 1449544 1632271 := bstep (se 1 (by rfl) ⟨1224203, by rfl⟩ : syracuseStep 1632271 = 2448407) B2448407
theorem B12397009 : Blo 1449544 12397009 := bstep (se 2 (by rfl) ⟨4648878, by rfl⟩ : syracuseStep 12397009 = 9297757) B9297757
theorem B1632775 : Blo 1449544 1632775 := bstep (se 1 (by rfl) ⟨1224581, by rfl⟩ : syracuseStep 1632775 = 2449163) B2449163
theorem B8260163 : Blo 1449544 8260163 := bstep (se 1 (by rfl) ⟨6195122, by rfl⟩ : syracuseStep 8260163 = 12390245) B12390245
theorem B3263111 : Blo 1449544 3263111 := bstep (se 1 (by rfl) ⟨2447333, by rfl⟩ : syracuseStep 3263111 = 4894667) B4894667
theorem B1632955 : Blo 1449544 1632955 := bstep (se 1 (by rfl) ⟨1224716, by rfl⟩ : syracuseStep 1632955 = 2449433) B2449433
theorem B9292481 : Blo 1449544 9292481 := bstep (se 2 (by rfl) ⟨3484680, by rfl⟩ : syracuseStep 9292481 = 6969361) B6969361
theorem B15682355 : Blo 1449544 15682355 := bstep (se 1 (by rfl) ⟨11761766, by rfl⟩ : syracuseStep 15682355 = 23523533) B23523533
theorem B3263291 : Blo 1449544 3263291 := bstep (se 1 (by rfl) ⟨2447468, by rfl⟩ : syracuseStep 3263291 = 4894937) B4894937
theorem B13945715 : Blo 1449544 13945715 := bstep (se 1 (by rfl) ⟨10459286, by rfl⟩ : syracuseStep 13945715 = 20918573) B20918573
theorem B6278023 : Blo 1449544 6278023 := bstep (se 1 (by rfl) ⟨4708517, by rfl⟩ : syracuseStep 6278023 = 9417035) B9417035
theorem B4893587 : Blo 1449544 4893587 := bstep (se 1 (by rfl) ⟨3670190, by rfl⟩ : syracuseStep 4893587 = 7340381) B7340381
theorem B3672985 : Blo 1449544 3672985 := bstep (se 2 (by rfl) ⟨1377369, by rfl⟩ : syracuseStep 3672985 = 2754739) B2754739
theorem B3263417 : Blo 1449544 3263417 := bstep (se 2 (by rfl) ⟨1223781, by rfl⟩ : syracuseStep 3263417 = 2447563) B2447563
theorem B2755529 : Blo 1449544 2755529 := bstep (se 2 (by rfl) ⟨1033323, by rfl⟩ : syracuseStep 2755529 = 2066647) B2066647
theorem B3673147 : Blo 1449544 3673147 := bstep (se 1 (by rfl) ⟨2754860, by rfl⟩ : syracuseStep 3673147 = 5509721) B5509721
theorem B14126167 : Blo 1449544 14126167 := bstep (se 1 (by rfl) ⟨10594625, by rfl⟩ : syracuseStep 14126167 = 21189251) B21189251
theorem B7343297 : Blo 1449544 7343297 := bstep (se 2 (by rfl) ⟨2753736, by rfl⟩ : syracuseStep 7343297 = 5507473) B5507473
theorem B3673289 : Blo 1449544 3673289 := bstep (se 2 (by rfl) ⟨1377483, by rfl⟩ : syracuseStep 3673289 = 2754967) B2754967
theorem B18590957 : Blo 1449544 18590957 := bstep (se 3 (by rfl) ⟨3485804, by rfl⟩ : syracuseStep 18590957 = 6971609) B6971609
theorem B3722507 : Blo 1449544 3722507 := bstep (se 1 (by rfl) ⟨2791880, by rfl⟩ : syracuseStep 3722507 = 5583761) B5583761
theorem B3263759 : Blo 1449544 3263759 := bstep (se 1 (by rfl) ⟨2447819, by rfl⟩ : syracuseStep 3263759 = 4895639) B4895639
theorem B17632529 : Blo 1449544 17632529 := bstep (se 2 (by rfl) ⟨6612198, by rfl⟩ : syracuseStep 17632529 = 13224397) B13224397
theorem B3263777 : Blo 1449544 3263777 := bstep (se 2 (by rfl) ⟨1223916, by rfl⟩ : syracuseStep 3263777 = 2447833) B2447833
theorem B2174327 : Blo 1449544 2174327 := bstep (se 1 (by rfl) ⟨1630745, by rfl⟩ : syracuseStep 2174327 = 3261491) B3261491
theorem B2174351 : Blo 1449544 2174351 := bstep (se 1 (by rfl) ⟨1630763, by rfl⟩ : syracuseStep 2174351 = 3261527) B3261527
theorem B2174393 : Blo 1449544 2174393 := bstep (se 2 (by rfl) ⟨815397, by rfl⟩ : syracuseStep 2174393 = 1630795) B1630795
theorem B2174471 : Blo 1449544 2174471 := bstep (se 1 (by rfl) ⟨1630853, by rfl⟩ : syracuseStep 2174471 = 3261707) B3261707
theorem B3673633 : Blo 1449544 3673633 := bstep (se 2 (by rfl) ⟨1377612, by rfl⟩ : syracuseStep 3673633 = 2755225) B2755225
theorem B2174507 : Blo 1449544 2174507 := bstep (se 1 (by rfl) ⟨1630880, by rfl⟩ : syracuseStep 2174507 = 3261761) B3261761
theorem B2174537 : Blo 1449544 2174537 := bstep (se 2 (by rfl) ⟨815451, by rfl⟩ : syracuseStep 2174537 = 1630903) B1630903
theorem B3264119 : Blo 1449544 3264119 := bstep (se 1 (by rfl) ⟨2448089, by rfl⟩ : syracuseStep 3264119 = 4896179) B4896179
theorem B2174651 : Blo 1449544 2174651 := bstep (se 1 (by rfl) ⟨1630988, by rfl⟩ : syracuseStep 2174651 = 3261977) B3261977
theorem B2174711 : Blo 1449544 2174711 := bstep (se 1 (by rfl) ⟨1631033, by rfl⟩ : syracuseStep 2174711 = 3262067) B3262067
theorem B2174735 : Blo 1449544 2174735 := bstep (se 1 (by rfl) ⟨1631051, by rfl⟩ : syracuseStep 2174735 = 3262103) B3262103
theorem B3264299 : Blo 1449544 3264299 := bstep (se 1 (by rfl) ⟨2448224, by rfl⟩ : syracuseStep 3264299 = 4896449) B4896449
theorem B2174777 : Blo 1449544 2174777 := bstep (se 2 (by rfl) ⟨815541, by rfl⟩ : syracuseStep 2174777 = 1631083) B1631083
theorem B35286853 : Blo 1449544 35286853 := bstep (se 4 (by rfl) ⟨3308142, by rfl⟩ : syracuseStep 35286853 = 6616285) B6616285
theorem B2174855 : Blo 1449544 2174855 := bstep (se 1 (by rfl) ⟨1631141, by rfl⟩ : syracuseStep 2174855 = 3262283) B3262283
theorem B2174891 : Blo 1449544 2174891 := bstep (se 1 (by rfl) ⟨1631168, by rfl⟩ : syracuseStep 2174891 = 3262337) B3262337
theorem B2174921 : Blo 1449544 2174921 := bstep (se 2 (by rfl) ⟨815595, by rfl⟩ : syracuseStep 2174921 = 1631191) B1631191
theorem B3485729 : Blo 1449544 3485729 := bstep (se 2 (by rfl) ⟨1307148, by rfl⟩ : syracuseStep 3485729 = 2614297) B2614297
theorem B4132907 : Blo 1449544 4132907 := bstep (se 1 (by rfl) ⟨3099680, by rfl⟩ : syracuseStep 4132907 = 6199361) B6199361
theorem B2175035 : Blo 1449544 2175035 := bstep (se 1 (by rfl) ⟨1631276, by rfl⟩ : syracuseStep 2175035 = 3262553) B3262553
theorem B2175095 : Blo 1449544 2175095 := bstep (se 1 (by rfl) ⟨1631321, by rfl⟩ : syracuseStep 2175095 = 3262643) B3262643
theorem B2175119 : Blo 1449544 2175119 := bstep (se 1 (by rfl) ⟨1631339, by rfl⟩ : syracuseStep 2175119 = 3262679) B3262679
theorem B3264659 : Blo 1449544 3264659 := bstep (se 1 (by rfl) ⟨2448494, by rfl⟩ : syracuseStep 3264659 = 4896989) B4896989
theorem B2175161 : Blo 1449544 2175161 := bstep (se 2 (by rfl) ⟨815685, by rfl⟩ : syracuseStep 2175161 = 1631371) B1631371
theorem B3264713 : Blo 1449544 3264713 := bstep (se 2 (by rfl) ⟨1224267, by rfl⟩ : syracuseStep 3264713 = 2448535) B2448535
theorem B2175239 : Blo 1449544 2175239 := bstep (se 1 (by rfl) ⟨1631429, by rfl⟩ : syracuseStep 2175239 = 3262859) B3262859
theorem B22647053 : Blo 1449544 22647053 := bstep (se 3 (by rfl) ⟨4246322, by rfl⟩ : syracuseStep 22647053 = 8492645) B8492645
theorem B4894991 : Blo 1449544 4894991 := bstep (se 1 (by rfl) ⟨3671243, by rfl⟩ : syracuseStep 4894991 = 7342487) B7342487
theorem B2175275 : Blo 1449544 2175275 := bstep (se 1 (by rfl) ⟨1631456, by rfl⟩ : syracuseStep 2175275 = 3262913) B3262913
theorem B8261939 : Blo 1449544 8261939 := bstep (se 1 (by rfl) ⟨6196454, by rfl⟩ : syracuseStep 8261939 = 12392909) B12392909
theorem B2175305 : Blo 1449544 2175305 := bstep (se 2 (by rfl) ⟨815739, by rfl⟩ : syracuseStep 2175305 = 1631479) B1631479
theorem B3920243 : Blo 1449544 3920243 := bstep (se 1 (by rfl) ⟨2940182, by rfl⟩ : syracuseStep 3920243 = 5880365) B5880365
theorem B12562823 : Blo 1449544 12562823 := bstep (se 1 (by rfl) ⟨9422117, by rfl⟩ : syracuseStep 12562823 = 18844235) B18844235
theorem B12398993 : Blo 1449544 12398993 := bstep (se 2 (by rfl) ⟨4649622, by rfl⟩ : syracuseStep 12398993 = 9299245) B9299245
theorem B2175419 : Blo 1449544 2175419 := bstep (se 1 (by rfl) ⟨1631564, by rfl⟩ : syracuseStep 2175419 = 3263129) B3263129
theorem B7344593 : Blo 1449544 7344593 := bstep (se 2 (by rfl) ⟨2754222, by rfl⟩ : syracuseStep 7344593 = 5508445) B5508445
theorem B15675869 : Blo 1449544 15675869 := bstep (se 3 (by rfl) ⟨2939225, by rfl⟩ : syracuseStep 15675869 = 5878451) B5878451
theorem B2175479 : Blo 1449544 2175479 := bstep (se 1 (by rfl) ⟨1631609, by rfl⟩ : syracuseStep 2175479 = 3263219) B3263219
theorem B13234691 : Blo 1449544 13234691 := bstep (se 1 (by rfl) ⟨9926018, by rfl⟩ : syracuseStep 13234691 = 19852037) B19852037
theorem B2175503 : Blo 1449544 2175503 := bstep (se 1 (by rfl) ⟨1631627, by rfl⟩ : syracuseStep 2175503 = 3263255) B3263255
theorem B4895261 : Blo 1449544 4895261 := bstep (se 3 (by rfl) ⟨917861, by rfl⟩ : syracuseStep 4895261 = 1835723) B1835723
theorem B2175545 : Blo 1449544 2175545 := bstep (se 2 (by rfl) ⟨815829, by rfl⟩ : syracuseStep 2175545 = 1631659) B1631659
theorem B3920503 : Blo 1449544 3920503 := bstep (se 1 (by rfl) ⟨2940377, by rfl⟩ : syracuseStep 3920503 = 5880755) B5880755
theorem B2175623 : Blo 1449544 2175623 := bstep (se 1 (by rfl) ⟨1631717, by rfl⟩ : syracuseStep 2175623 = 3263435) B3263435
theorem B2175659 : Blo 1449544 2175659 := bstep (se 1 (by rfl) ⟨1631744, by rfl⟩ : syracuseStep 2175659 = 3263489) B3263489
theorem B44634817 : Blo 1449544 44634817 := bstep (se 2 (by rfl) ⟨16738056, by rfl⟩ : syracuseStep 44634817 = 33476113) B33476113
theorem B2175689 : Blo 1449544 2175689 := bstep (se 2 (by rfl) ⟨815883, by rfl⟩ : syracuseStep 2175689 = 1631767) B1631767
theorem B5509889 : Blo 1449544 5509889 := bstep (se 2 (by rfl) ⟨2066208, by rfl⟩ : syracuseStep 5509889 = 4132417) B4132417
theorem B5509903 : Blo 1449544 5509903 := bstep (se 1 (by rfl) ⟨4132427, by rfl⟩ : syracuseStep 5509903 = 8264855) B8264855
theorem B2446139 : Blo 1449544 2446139 := bstep (se 1 (by rfl) ⟨1834604, by rfl⟩ : syracuseStep 2446139 = 3669209) B3669209
theorem B3920699 : Blo 1449544 3920699 := bstep (se 1 (by rfl) ⟨2940524, by rfl⟩ : syracuseStep 3920699 = 5881049) B5881049
theorem B2175803 : Blo 1449544 2175803 := bstep (se 1 (by rfl) ⟨1631852, by rfl⟩ : syracuseStep 2175803 = 3263705) B3263705
theorem B17650547 : Blo 1449544 17650547 := bstep (se 1 (by rfl) ⟨13237910, by rfl⟩ : syracuseStep 17650547 = 26475821) B26475821
theorem B2175863 : Blo 1449544 2175863 := bstep (se 1 (by rfl) ⟨1631897, by rfl⟩ : syracuseStep 2175863 = 3263795) B3263795
theorem B3265415 : Blo 1449544 3265415 := bstep (se 1 (by rfl) ⟨2449061, by rfl⟩ : syracuseStep 3265415 = 4898123) B4898123
theorem B2175887 : Blo 1449544 2175887 := bstep (se 1 (by rfl) ⟨1631915, by rfl⟩ : syracuseStep 2175887 = 3263831) B3263831
theorem B2175929 : Blo 1449544 2175929 := bstep (se 2 (by rfl) ⟨815973, by rfl⟩ : syracuseStep 2175929 = 1631947) B1631947
theorem B3724289 : Blo 1449544 3724289 := bstep (se 2 (by rfl) ⟨1396608, by rfl⟩ : syracuseStep 3724289 = 2793217) B2793217
theorem B2176007 : Blo 1449544 2176007 := bstep (se 1 (by rfl) ⟨1632005, by rfl⟩ : syracuseStep 2176007 = 3264011) B3264011
theorem B3306539 : Blo 1449544 3306539 := bstep (se 1 (by rfl) ⟨2479904, by rfl⟩ : syracuseStep 3306539 = 4959809) B4959809
theorem B2176043 : Blo 1449544 2176043 := bstep (se 1 (by rfl) ⟨1632032, by rfl⟩ : syracuseStep 2176043 = 3264065) B3264065
theorem B3265595 : Blo 1449544 3265595 := bstep (se 1 (by rfl) ⟨2449196, by rfl⟩ : syracuseStep 3265595 = 4898393) B4898393
theorem B2176073 : Blo 1449544 2176073 := bstep (se 2 (by rfl) ⟨816027, by rfl⟩ : syracuseStep 2176073 = 1632055) B1632055
theorem B3265721 : Blo 1449544 3265721 := bstep (se 2 (by rfl) ⟨1224645, by rfl⟩ : syracuseStep 3265721 = 2449291) B2449291
theorem B2176187 : Blo 1449544 2176187 := bstep (se 1 (by rfl) ⟨1632140, by rfl⟩ : syracuseStep 2176187 = 3264281) B3264281
theorem B2446537 : Blo 1449544 2446537 := bstep (se 2 (by rfl) ⟨917451, by rfl⟩ : syracuseStep 2446537 = 1834903) B1834903
theorem B1742071 : Blo 1449544 1742071 := bstep (se 1 (by rfl) ⟨1306553, by rfl⟩ : syracuseStep 1742071 = 2613107) B2613107
theorem B2176247 : Blo 1449544 2176247 := bstep (se 1 (by rfl) ⟨1632185, by rfl⟩ : syracuseStep 2176247 = 3264371) B3264371
theorem B2176271 : Blo 1449544 2176271 := bstep (se 1 (by rfl) ⟨1632203, by rfl⟩ : syracuseStep 2176271 = 3264407) B3264407
theorem B3921185 : Blo 1449544 3921185 := bstep (se 2 (by rfl) ⟨1470444, by rfl⟩ : syracuseStep 3921185 = 2940889) B2940889
theorem B2176313 : Blo 1449544 2176313 := bstep (se 2 (by rfl) ⟨816117, by rfl⟩ : syracuseStep 2176313 = 1632235) B1632235
theorem B4838771 : Blo 1449544 4838771 := bstep (se 1 (by rfl) ⟨3629078, by rfl⟩ : syracuseStep 4838771 = 7258157) B7258157
theorem B2176391 : Blo 1449544 2176391 := bstep (se 1 (by rfl) ⟨1632293, by rfl⟩ : syracuseStep 2176391 = 3264587) B3264587
theorem B2176427 : Blo 1449544 2176427 := bstep (se 1 (by rfl) ⟨1632320, by rfl⟩ : syracuseStep 2176427 = 3264641) B3264641
theorem B9418169 : Blo 1449544 9418169 := bstep (se 2 (by rfl) ⟨3531813, by rfl⟩ : syracuseStep 9418169 = 7063627) B7063627
theorem B59585977 : Blo 1449544 59585977 := bstep (se 2 (by rfl) ⟨22344741, by rfl⟩ : syracuseStep 59585977 = 44689483) B44689483
theorem B2176457 : Blo 1449544 2176457 := bstep (se 2 (by rfl) ⟨816171, by rfl⟩ : syracuseStep 2176457 = 1632343) B1632343
theorem B15685123 : Blo 1449544 15685123 := bstep (se 1 (by rfl) ⟨11763842, by rfl⟩ : syracuseStep 15685123 = 23527685) B23527685
theorem B6968861 : Blo 1449544 6968861 := bstep (se 3 (by rfl) ⟨1306661, by rfl⟩ : syracuseStep 6968861 = 2613323) B2613323
theorem B2176571 : Blo 1449544 2176571 := bstep (se 1 (by rfl) ⟨1632428, by rfl⟩ : syracuseStep 2176571 = 3264857) B3264857
theorem B25130573 : Blo 1449544 25130573 := bstep (se 3 (by rfl) ⟨4711982, by rfl⟩ : syracuseStep 25130573 = 9423965) B9423965
theorem B2176631 : Blo 1449544 2176631 := bstep (se 1 (by rfl) ⟨1632473, by rfl⟩ : syracuseStep 2176631 = 3264947) B3264947
theorem B2176655 : Blo 1449544 2176655 := bstep (se 1 (by rfl) ⟨1632491, by rfl⟩ : syracuseStep 2176655 = 3264983) B3264983
theorem B2176697 : Blo 1449544 2176697 := bstep (se 2 (by rfl) ⟨816261, by rfl⟩ : syracuseStep 2176697 = 1632523) B1632523
theorem B8263397 : Blo 1449544 8263397 := bstep (se 4 (by rfl) ⟨774693, by rfl⟩ : syracuseStep 8263397 = 1549387) B1549387
theorem B2176775 : Blo 1449544 2176775 := bstep (se 1 (by rfl) ⟨1632581, by rfl⟩ : syracuseStep 2176775 = 3265163) B3265163
theorem B2176811 : Blo 1449544 2176811 := bstep (se 1 (by rfl) ⟨1632608, by rfl⟩ : syracuseStep 2176811 = 3265217) B3265217
theorem B2176841 : Blo 1449544 2176841 := bstep (se 2 (by rfl) ⟨816315, by rfl⟩ : syracuseStep 2176841 = 1632631) B1632631
theorem B2447239 : Blo 1449544 2447239 := bstep (se 1 (by rfl) ⟨1835429, by rfl⟩ : syracuseStep 2447239 = 3670859) B3670859
theorem B4896665 : Blo 1449544 4896665 := bstep (se 2 (by rfl) ⟨1836249, by rfl⟩ : syracuseStep 4896665 = 3672499) B3672499
theorem B2176955 : Blo 1449544 2176955 := bstep (se 1 (by rfl) ⟨1632716, by rfl⟩ : syracuseStep 2176955 = 3265433) B3265433
theorem B2177015 : Blo 1449544 2177015 := bstep (se 1 (by rfl) ⟨1632761, by rfl⟩ : syracuseStep 2177015 = 3265523) B3265523
theorem B15685643 : Blo 1449544 15685643 := bstep (se 1 (by rfl) ⟨11764232, by rfl⟩ : syracuseStep 15685643 = 23528465) B23528465
theorem B5511179 : Blo 1449544 5511179 := bstep (se 1 (by rfl) ⟨4133384, by rfl⟩ : syracuseStep 5511179 = 8266769) B8266769
theorem B2177039 : Blo 1449544 2177039 := bstep (se 1 (by rfl) ⟨1632779, by rfl⟩ : syracuseStep 2177039 = 3265559) B3265559
theorem B6199325 : Blo 1449544 6199325 := bstep (se 3 (by rfl) ⟨1162373, by rfl⟩ : syracuseStep 6199325 = 2324747) B2324747
theorem B2177081 : Blo 1449544 2177081 := bstep (se 2 (by rfl) ⟨816405, by rfl⟩ : syracuseStep 2177081 = 1632811) B1632811
theorem B39688309 : Blo 1449544 39688309 := bstep (se 5 (by rfl) ⟨1860389, by rfl⟩ : syracuseStep 39688309 = 3720779) B3720779
theorem B2177159 : Blo 1449544 2177159 := bstep (se 1 (by rfl) ⟨1632869, by rfl⟩ : syracuseStep 2177159 = 3265739) B3265739
theorem B2177195 : Blo 1449544 2177195 := bstep (se 1 (by rfl) ⟨1632896, by rfl⟩ : syracuseStep 2177195 = 3265793) B3265793
theorem B8263853 : Blo 1449544 8263853 := bstep (se 3 (by rfl) ⟨1549472, by rfl⟩ : syracuseStep 8263853 = 3098945) B3098945
theorem B2177225 : Blo 1449544 2177225 := bstep (se 2 (by rfl) ⟨816459, by rfl⟩ : syracuseStep 2177225 = 1632919) B1632919
theorem B9288121 : Blo 1449544 9288121 := bstep (se 2 (by rfl) ⟨3483045, by rfl⟩ : syracuseStep 9288121 = 6966091) B6966091
theorem B13949405 : Blo 1449544 13949405 := bstep (se 3 (by rfl) ⟨2615513, by rfl⟩ : syracuseStep 13949405 = 5231027) B5231027
theorem B7346699 : Blo 1449544 7346699 := bstep (se 1 (by rfl) ⟨5510024, by rfl⟩ : syracuseStep 7346699 = 11020049) B11020049
theorem B2447887 : Blo 1449544 2447887 := bstep (se 1 (by rfl) ⟨1835915, by rfl⟩ : syracuseStep 2447887 = 3671831) B3671831
theorem B12384845 : Blo 1449544 12384845 := bstep (se 3 (by rfl) ⟨2322158, by rfl⟩ : syracuseStep 12384845 = 4644317) B4644317
theorem B4897367 : Blo 1449544 4897367 := bstep (se 1 (by rfl) ⟨3673025, by rfl⟩ : syracuseStep 4897367 = 7346051) B7346051
theorem B7346861 : Blo 1449544 7346861 := bstep (se 3 (by rfl) ⟨1377536, by rfl⟩ : syracuseStep 7346861 = 2755073) B2755073
theorem B6200009 : Blo 1449544 6200009 := bstep (se 2 (by rfl) ⟨2325003, by rfl⟩ : syracuseStep 6200009 = 4650007) B4650007
theorem B8256289 : Blo 1449544 8256289 := bstep (se 2 (by rfl) ⟨3096108, by rfl⟩ : syracuseStep 8256289 = 6192217) B6192217
theorem B5225249 : Blo 1449544 5225249 := bstep (se 2 (by rfl) ⟨1959468, by rfl⟩ : syracuseStep 5225249 = 3918937) B3918937
theorem B2480939 : Blo 1449544 2480939 := bstep (se 1 (by rfl) ⟨1860704, by rfl⟩ : syracuseStep 2480939 = 3721409) B3721409
theorem B7256891 : Blo 1449544 7256891 := bstep (se 1 (by rfl) ⟨5442668, by rfl⟩ : syracuseStep 7256891 = 10885337) B10885337
theorem B3922775 : Blo 1449544 3922775 := bstep (se 1 (by rfl) ⟨2942081, by rfl⟩ : syracuseStep 3922775 = 5884163) B5884163
theorem B8264537 : Blo 1449544 8264537 := bstep (se 2 (by rfl) ⟨3099201, by rfl⟩ : syracuseStep 8264537 = 6198403) B6198403
theorem B5503859 : Blo 1449544 5503859 := bstep (se 1 (by rfl) ⟨4127894, by rfl⟩ : syracuseStep 5503859 = 8255789) B8255789
theorem B8821619 : Blo 1449544 8821619 := bstep (se 1 (by rfl) ⟨6616214, by rfl⟩ : syracuseStep 8821619 = 13232429) B13232429
theorem B2980793 : Blo 1449544 2980793 := bstep (se 2 (by rfl) ⟨1117797, by rfl⟩ : syracuseStep 2980793 = 2235595) B2235595
theorem B20904965 : Blo 1449544 20904965 := bstep (se 4 (by rfl) ⟨1959840, by rfl⟩ : syracuseStep 20904965 = 3919681) B3919681
theorem B2448427 : Blo 1449544 2448427 := bstep (se 1 (by rfl) ⟨1836320, by rfl⟩ : syracuseStep 2448427 = 3672641) B3672641
theorem B4897853 : Blo 1449544 4897853 := bstep (se 3 (by rfl) ⟨918347, by rfl⟩ : syracuseStep 4897853 = 1836695) B1836695
theorem B4963447 : Blo 1449544 4963447 := bstep (se 1 (by rfl) ⟨3722585, by rfl⟩ : syracuseStep 4963447 = 7445171) B7445171
theorem B2448569 : Blo 1449544 2448569 := bstep (se 2 (by rfl) ⟨918213, by rfl⟩ : syracuseStep 2448569 = 1836427) B1836427
theorem B92978381 : Blo 1449544 92978381 := bstep (se 3 (by rfl) ⟨17433446, by rfl⟩ : syracuseStep 92978381 = 34866893) B34866893
theorem B3669259 : Blo 1449544 3669259 := bstep (se 1 (by rfl) ⟨2751944, by rfl⟩ : syracuseStep 3669259 = 5503889) B5503889
theorem B4128043 : Blo 1449544 4128043 := bstep (se 1 (by rfl) ⟨3096032, by rfl⟩ : syracuseStep 4128043 = 6192065) B6192065
theorem B7339409 : Blo 1449544 7339409 := bstep (se 2 (by rfl) ⟨2752278, by rfl⟩ : syracuseStep 7339409 = 5504557) B5504557
theorem B11017619 : Blo 1449544 11017619 := bstep (se 1 (by rfl) ⟨8263214, by rfl⟩ : syracuseStep 11017619 = 16526429) B16526429
theorem B3669401 : Blo 1449544 3669401 := bstep (se 2 (by rfl) ⟨1376025, by rfl⟩ : syracuseStep 3669401 = 2752051) B2752051
theorem B17644985 : Blo 1449544 17644985 := bstep (se 2 (by rfl) ⟨6616869, by rfl⟩ : syracuseStep 17644985 = 13233739) B13233739
theorem B3669563 : Blo 1449544 3669563 := bstep (se 1 (by rfl) ⟨2752172, by rfl⟩ : syracuseStep 3669563 = 5504345) B5504345
theorem B4128317 : Blo 1449544 4128317 := bstep (se 3 (by rfl) ⟨774059, by rfl⟩ : syracuseStep 4128317 = 1548119) B1548119
theorem B1449607 : Blo 1449544 1449607 := bstep (se 1 (by rfl) ⟨1087205, by rfl⟩ : syracuseStep 1449607 = 2174411) B2174411
theorem B1449615 : Blo 1449544 1449615 := bstep (se 1 (by rfl) ⟨1087211, by rfl⟩ : syracuseStep 1449615 = 2174423) B2174423
theorem B1449659 : Blo 1449544 1449659 := bstep (se 1 (by rfl) ⟨1087244, by rfl⟩ : syracuseStep 1449659 = 2174489) B2174489
theorem B1449735 : Blo 1449544 1449735 := bstep (se 1 (by rfl) ⟨1087301, by rfl⟩ : syracuseStep 1449735 = 2174603) B2174603
theorem B1449743 : Blo 1449544 1449743 := bstep (se 1 (by rfl) ⟨1087307, by rfl⟩ : syracuseStep 1449743 = 2174615) B2174615
theorem B2613035 : Blo 1449544 2613035 := bstep (se 1 (by rfl) ⟨1959776, by rfl⟩ : syracuseStep 2613035 = 3919553) B3919553
theorem B67927853 : Blo 1449544 67927853 := bstep (se 3 (by rfl) ⟨12736472, by rfl⟩ : syracuseStep 67927853 = 25472945) B25472945
theorem B11009843 : Blo 1449544 11009843 := bstep (se 1 (by rfl) ⟨8257382, by rfl⟩ : syracuseStep 11009843 = 16514765) B16514765
theorem B1449787 : Blo 1449544 1449787 := bstep (se 1 (by rfl) ⟨1087340, by rfl⟩ : syracuseStep 1449787 = 2174681) B2174681
theorem B5226299 : Blo 1449544 5226299 := bstep (se 1 (by rfl) ⟨3919724, by rfl⟩ : syracuseStep 5226299 = 7839449) B7839449
theorem B2449271 : Blo 1449544 2449271 := bstep (se 1 (by rfl) ⟨1836953, by rfl⟩ : syracuseStep 2449271 = 3673907) B3673907
theorem B1449863 : Blo 1449544 1449863 := bstep (se 1 (by rfl) ⟨1087397, by rfl⟩ : syracuseStep 1449863 = 2174795) B2174795
theorem B1449871 : Blo 1449544 1449871 := bstep (se 1 (by rfl) ⟨1087403, by rfl⟩ : syracuseStep 1449871 = 2174807) B2174807
theorem B3669907 : Blo 1449544 3669907 := bstep (se 1 (by rfl) ⟨2752430, by rfl⟩ : syracuseStep 3669907 = 5504861) B5504861
theorem B6291353 : Blo 1449544 6291353 := bstep (se 2 (by rfl) ⟨2359257, by rfl⟩ : syracuseStep 6291353 = 4718515) B4718515
theorem B1449915 : Blo 1449544 1449915 := bstep (se 1 (by rfl) ⟨1087436, by rfl⟩ : syracuseStep 1449915 = 2174873) B2174873
theorem B8052689 : Blo 1449544 8052689 := bstep (se 2 (by rfl) ⟨3019758, by rfl⟩ : syracuseStep 8052689 = 6039517) B6039517
theorem B5505043 : Blo 1449544 5505043 := bstep (se 1 (by rfl) ⟨4128782, by rfl⟩ : syracuseStep 5505043 = 8257565) B8257565
theorem B1450023 : Blo 1449544 1450023 := bstep (se 1 (by rfl) ⟨1087517, by rfl⟩ : syracuseStep 1450023 = 2175035) B2175035
theorem B1450063 : Blo 1449544 1450063 := bstep (se 1 (by rfl) ⟨1087547, by rfl⟩ : syracuseStep 1450063 = 2175095) B2175095
theorem B1450079 : Blo 1449544 1450079 := bstep (se 1 (by rfl) ⟨1087559, by rfl⟩ : syracuseStep 1450079 = 2175119) B2175119
theorem B1835131 : Blo 1449544 1835131 := bstep (se 1 (by rfl) ⟨1376348, by rfl⟩ : syracuseStep 1835131 = 2752697) B2752697
theorem B1450107 : Blo 1449544 1450107 := bstep (se 1 (by rfl) ⟨1087580, by rfl⟩ : syracuseStep 1450107 = 2175161) B2175161
theorem B1450159 : Blo 1449544 1450159 := bstep (se 1 (by rfl) ⟨1087619, by rfl⟩ : syracuseStep 1450159 = 2175239) B2175239
theorem B15098035 : Blo 1449544 15098035 := bstep (se 1 (by rfl) ⟨11323526, by rfl⟩ : syracuseStep 15098035 = 22647053) B22647053
theorem B1450183 : Blo 1449544 1450183 := bstep (se 1 (by rfl) ⟨1087637, by rfl⟩ : syracuseStep 1450183 = 2175275) B2175275
theorem B1450203 : Blo 1449544 1450203 := bstep (se 1 (by rfl) ⟨1087652, by rfl⟩ : syracuseStep 1450203 = 2175305) B2175305
theorem B8265995 : Blo 1449544 8265995 := bstep (se 1 (by rfl) ⟨6199496, by rfl⟩ : syracuseStep 8265995 = 12398993) B12398993
theorem B1450279 : Blo 1449544 1450279 := bstep (se 1 (by rfl) ⟨1087709, by rfl⟩ : syracuseStep 1450279 = 2175419) B2175419
theorem B12386621 : Blo 1449544 12386621 := bstep (se 3 (by rfl) ⟨2322491, by rfl⟩ : syracuseStep 12386621 = 4644983) B4644983
theorem B2752841 : Blo 1449544 2752841 := bstep (se 2 (by rfl) ⟨1032315, by rfl⟩ : syracuseStep 2752841 = 2064631) B2064631
theorem B1450319 : Blo 1449544 1450319 := bstep (se 1 (by rfl) ⟨1087739, by rfl⟩ : syracuseStep 1450319 = 2175479) B2175479
theorem B1450335 : Blo 1449544 1450335 := bstep (se 1 (by rfl) ⟨1087751, by rfl⟩ : syracuseStep 1450335 = 2175503) B2175503
theorem B1450363 : Blo 1449544 1450363 := bstep (se 1 (by rfl) ⟨1087772, by rfl⟩ : syracuseStep 1450363 = 2175545) B2175545
theorem B1450415 : Blo 1449544 1450415 := bstep (se 1 (by rfl) ⟨1087811, by rfl⟩ : syracuseStep 1450415 = 2175623) B2175623
theorem B1450439 : Blo 1449544 1450439 := bstep (se 1 (by rfl) ⟨1087829, by rfl⟩ : syracuseStep 1450439 = 2175659) B2175659
theorem B1450459 : Blo 1449544 1450459 := bstep (se 1 (by rfl) ⟨1087844, by rfl⟩ : syracuseStep 1450459 = 2175689) B2175689
theorem B1630759 : Blo 1449544 1630759 := bstep (se 1 (by rfl) ⟨1223069, by rfl⟩ : syracuseStep 1630759 = 2446139) B2446139
theorem B4129319 : Blo 1449544 4129319 := bstep (se 1 (by rfl) ⟨3096989, by rfl⟩ : syracuseStep 4129319 = 6193979) B6193979
theorem B2613799 : Blo 1449544 2613799 := bstep (se 1 (by rfl) ⟨1960349, by rfl⟩ : syracuseStep 2613799 = 3920699) B3920699
theorem B1450535 : Blo 1449544 1450535 := bstep (se 1 (by rfl) ⟨1087901, by rfl⟩ : syracuseStep 1450535 = 2175803) B2175803
theorem B1450575 : Blo 1449544 1450575 := bstep (se 1 (by rfl) ⟨1087931, by rfl⟩ : syracuseStep 1450575 = 2175863) B2175863
theorem B1450591 : Blo 1449544 1450591 := bstep (se 1 (by rfl) ⟨1087943, by rfl⟩ : syracuseStep 1450591 = 2175887) B2175887
theorem B1450619 : Blo 1449544 1450619 := bstep (se 1 (by rfl) ⟨1087964, by rfl⟩ : syracuseStep 1450619 = 2175929) B2175929
theorem B3670667 : Blo 1449544 3670667 := bstep (se 1 (by rfl) ⟨2753000, by rfl⟩ : syracuseStep 3670667 = 5506001) B5506001
theorem B2482859 : Blo 1449544 2482859 := bstep (se 1 (by rfl) ⟨1862144, by rfl⟩ : syracuseStep 2482859 = 3724289) B3724289
theorem B1450671 : Blo 1449544 1450671 := bstep (se 1 (by rfl) ⟨1088003, by rfl⟩ : syracuseStep 1450671 = 2176007) B2176007
theorem B1450695 : Blo 1449544 1450695 := bstep (se 1 (by rfl) ⟨1088021, by rfl⟩ : syracuseStep 1450695 = 2176043) B2176043
theorem B1450715 : Blo 1449544 1450715 := bstep (se 1 (by rfl) ⟨1088036, by rfl⟩ : syracuseStep 1450715 = 2176073) B2176073
theorem B1450791 : Blo 1449544 1450791 := bstep (se 1 (by rfl) ⟨1088093, by rfl⟩ : syracuseStep 1450791 = 2176187) B2176187
theorem B5227337 : Blo 1449544 5227337 := bstep (se 2 (by rfl) ⟨1960251, by rfl⟩ : syracuseStep 5227337 = 3920503) B3920503
theorem B1450831 : Blo 1449544 1450831 := bstep (se 1 (by rfl) ⟨1088123, by rfl⟩ : syracuseStep 1450831 = 2176247) B2176247
theorem B3670879 : Blo 1449544 3670879 := bstep (se 1 (by rfl) ⟨2753159, by rfl⟩ : syracuseStep 3670879 = 5506319) B5506319
theorem B1450847 : Blo 1449544 1450847 := bstep (se 1 (by rfl) ⟨1088135, by rfl⟩ : syracuseStep 1450847 = 2176271) B2176271
theorem B2614123 : Blo 1449544 2614123 := bstep (se 1 (by rfl) ⟨1960592, by rfl⟩ : syracuseStep 2614123 = 3921185) B3921185
theorem B1450875 : Blo 1449544 1450875 := bstep (se 1 (by rfl) ⟨1088156, by rfl⟩ : syracuseStep 1450875 = 2176313) B2176313
theorem B1450927 : Blo 1449544 1450927 := bstep (se 1 (by rfl) ⟨1088195, by rfl⟩ : syracuseStep 1450927 = 2176391) B2176391
theorem B1450951 : Blo 1449544 1450951 := bstep (se 1 (by rfl) ⟨1088213, by rfl⟩ : syracuseStep 1450951 = 2176427) B2176427
theorem B1450971 : Blo 1449544 1450971 := bstep (se 1 (by rfl) ⟨1088228, by rfl⟩ : syracuseStep 1450971 = 2176457) B2176457
theorem B10453981 : Blo 1449544 10453981 := bstep (se 3 (by rfl) ⟨1960121, by rfl⟩ : syracuseStep 10453981 = 3920243) B3920243
theorem B4645907 : Blo 1449544 4645907 := bstep (se 1 (by rfl) ⟨3484430, by rfl⟩ : syracuseStep 4645907 = 6968861) B6968861
theorem B1451047 : Blo 1449544 1451047 := bstep (se 1 (by rfl) ⟨1088285, by rfl⟩ : syracuseStep 1451047 = 2176571) B2176571
theorem B16753715 : Blo 1449544 16753715 := bstep (se 1 (by rfl) ⟨12565286, by rfl⟩ : syracuseStep 16753715 = 25130573) B25130573
theorem B2753615 : Blo 1449544 2753615 := bstep (se 1 (by rfl) ⟨2065211, by rfl⟩ : syracuseStep 2753615 = 4130423) B4130423
theorem B5882959 : Blo 1449544 5882959 := bstep (se 1 (by rfl) ⟨4412219, by rfl⟩ : syracuseStep 5882959 = 8824439) B8824439
theorem B1451087 : Blo 1449544 1451087 := bstep (se 1 (by rfl) ⟨1088315, by rfl⟩ : syracuseStep 1451087 = 2176631) B2176631
theorem B1451103 : Blo 1449544 1451103 := bstep (se 1 (by rfl) ⟨1088327, by rfl⟩ : syracuseStep 1451103 = 2176655) B2176655
theorem B1451131 : Blo 1449544 1451131 := bstep (se 1 (by rfl) ⟨1088348, by rfl⟩ : syracuseStep 1451131 = 2176697) B2176697
theorem B1451183 : Blo 1449544 1451183 := bstep (se 1 (by rfl) ⟨1088387, by rfl⟩ : syracuseStep 1451183 = 2176775) B2176775
theorem B1451207 : Blo 1449544 1451207 := bstep (se 1 (by rfl) ⟨1088405, by rfl⟩ : syracuseStep 1451207 = 2176811) B2176811
theorem B1451227 : Blo 1449544 1451227 := bstep (se 1 (by rfl) ⟨1088420, by rfl⟩ : syracuseStep 1451227 = 2176841) B2176841
theorem B1451303 : Blo 1449544 1451303 := bstep (se 1 (by rfl) ⟨1088477, by rfl⟩ : syracuseStep 1451303 = 2176955) B2176955
theorem B1451343 : Blo 1449544 1451343 := bstep (se 1 (by rfl) ⟨1088507, by rfl⟩ : syracuseStep 1451343 = 2177015) B2177015
theorem B35292509 : Blo 1449544 35292509 := bstep (se 3 (by rfl) ⟨6617345, by rfl⟩ : syracuseStep 35292509 = 13234691) B13234691
theorem B1451359 : Blo 1449544 1451359 := bstep (se 1 (by rfl) ⟨1088519, by rfl⟩ : syracuseStep 1451359 = 2177039) B2177039
theorem B1451387 : Blo 1449544 1451387 := bstep (se 1 (by rfl) ⟨1088540, by rfl⟩ : syracuseStep 1451387 = 2177081) B2177081
theorem B1451439 : Blo 1449544 1451439 := bstep (se 1 (by rfl) ⟨1088579, by rfl⟩ : syracuseStep 1451439 = 2177159) B2177159
theorem B1451463 : Blo 1449544 1451463 := bstep (se 1 (by rfl) ⟨1088597, by rfl⟩ : syracuseStep 1451463 = 2177195) B2177195
theorem B18834889 : Blo 1449544 18834889 := bstep (se 2 (by rfl) ⟨7063083, by rfl⟩ : syracuseStep 18834889 = 14126167) B14126167
theorem B1451483 : Blo 1449544 1451483 := bstep (se 1 (by rfl) ⟨1088612, by rfl⟩ : syracuseStep 1451483 = 2177225) B2177225
theorem B3262049 : Blo 1449544 3262049 := bstep (se 2 (by rfl) ⟨1223268, by rfl⟩ : syracuseStep 3262049 = 2446537) B2446537
theorem B9299603 : Blo 1449544 9299603 := bstep (se 1 (by rfl) ⟨6974702, by rfl⟩ : syracuseStep 9299603 = 13949405) B13949405
theorem B4892345 : Blo 1449544 4892345 := bstep (se 2 (by rfl) ⟨1834629, by rfl⟩ : syracuseStep 4892345 = 3669259) B3669259
theorem B5506775 : Blo 1449544 5506775 := bstep (se 1 (by rfl) ⟨4130081, by rfl⟩ : syracuseStep 5506775 = 8260163) B8260163
theorem B3671801 : Blo 1449544 3671801 := bstep (se 2 (by rfl) ⟨1376925, by rfl⟩ : syracuseStep 3671801 = 2753851) B2753851
theorem B6194987 : Blo 1449544 6194987 := bstep (se 1 (by rfl) ⟨4646240, by rfl⟩ : syracuseStep 6194987 = 9292481) B9292481
theorem B3483499 : Blo 1449544 3483499 := bstep (se 1 (by rfl) ⟨2612624, by rfl⟩ : syracuseStep 3483499 = 5225249) B5225249
theorem B12912493 : Blo 1449544 12912493 := bstep (se 3 (by rfl) ⟨2421092, by rfl⟩ : syracuseStep 12912493 = 4842185) B4842185
theorem B10454903 : Blo 1449544 10454903 := bstep (se 1 (by rfl) ⟨7841177, by rfl⟩ : syracuseStep 10454903 = 15682355) B15682355
theorem B2615183 : Blo 1449544 2615183 := bstep (se 1 (by rfl) ⟨1961387, by rfl⟩ : syracuseStep 2615183 = 3922775) B3922775
theorem B79447969 : Blo 1449544 79447969 := bstep (se 2 (by rfl) ⟨29792988, by rfl⟩ : syracuseStep 79447969 = 59585977) B59585977
theorem B3262391 : Blo 1449544 3262391 := bstep (se 1 (by rfl) ⟨2446793, by rfl⟩ : syracuseStep 3262391 = 4893587) B4893587
theorem B1837019 : Blo 1449544 1837019 := bstep (se 1 (by rfl) ⟨1377764, by rfl⟩ : syracuseStep 1837019 = 2755529) B2755529
theorem B13936643 : Blo 1449544 13936643 := bstep (se 1 (by rfl) ⟨10452482, by rfl⟩ : syracuseStep 13936643 = 20904965) B20904965
theorem B1632379 : Blo 1449544 1632379 := bstep (se 1 (by rfl) ⟨1224284, by rfl⟩ : syracuseStep 1632379 = 2448569) B2448569
theorem B2066681 : Blo 1449544 2066681 := bstep (se 2 (by rfl) ⟨775005, by rfl⟩ : syracuseStep 2066681 = 1550011) B1550011
theorem B4892939 : Blo 1449544 4892939 := bstep (se 1 (by rfl) ⟨3669704, by rfl⟩ : syracuseStep 4892939 = 7339409) B7339409
theorem B3672449 : Blo 1449544 3672449 := bstep (se 2 (by rfl) ⟨1377168, by rfl⟩ : syracuseStep 3672449 = 2754337) B2754337
theorem B47049137 : Blo 1449544 47049137 := bstep (se 2 (by rfl) ⟨17643426, by rfl⟩ : syracuseStep 47049137 = 35286853) B35286853
theorem B6973933 : Blo 1449544 6973933 := bstep (se 3 (by rfl) ⟨1307612, by rfl⟩ : syracuseStep 6973933 = 2615225) B2615225
theorem B3262985 : Blo 1449544 3262985 := bstep (se 2 (by rfl) ⟨1223619, by rfl⟩ : syracuseStep 3262985 = 2447239) B2447239
theorem B4893209 : Blo 1449544 4893209 := bstep (se 2 (by rfl) ⟨1834953, by rfl⟩ : syracuseStep 4893209 = 3669907) B3669907
theorem B3484199 : Blo 1449544 3484199 := bstep (se 1 (by rfl) ⟨2613149, by rfl⟩ : syracuseStep 3484199 = 5226299) B5226299
theorem B1632847 : Blo 1449544 1632847 := bstep (se 1 (by rfl) ⟨1224635, by rfl⟩ : syracuseStep 1632847 = 2449271) B2449271
theorem B4131425 : Blo 1449544 4131425 := bstep (se 2 (by rfl) ⟨1549284, by rfl⟩ : syracuseStep 4131425 = 3098569) B3098569
theorem B5368459 : Blo 1449544 5368459 := bstep (se 1 (by rfl) ⟨4026344, by rfl⟩ : syracuseStep 5368459 = 8052689) B8052689
theorem B2755271 : Blo 1449544 2755271 := bstep (se 1 (by rfl) ⟨2066453, by rfl⟩ : syracuseStep 2755271 = 4132907) B4132907
theorem B8817437 : Blo 1449544 8817437 := bstep (se 3 (by rfl) ⟨1653269, by rfl⟩ : syracuseStep 8817437 = 3306539) B3306539
theorem B3263327 : Blo 1449544 3263327 := bstep (se 1 (by rfl) ⟨2447495, by rfl⟩ : syracuseStep 3263327 = 4894991) B4894991
theorem B5507959 : Blo 1449544 5507959 := bstep (se 1 (by rfl) ⟨4130969, by rfl⟩ : syracuseStep 5507959 = 8261939) B8261939
theorem B3263507 : Blo 1449544 3263507 := bstep (se 1 (by rfl) ⟨2447630, by rfl⟩ : syracuseStep 3263507 = 4895261) B4895261
theorem B3533843 : Blo 1449544 3533843 := bstep (se 1 (by rfl) ⟨2650382, by rfl⟩ : syracuseStep 3533843 = 5300765) B5300765
theorem B3673259 : Blo 1449544 3673259 := bstep (se 1 (by rfl) ⟨2754944, by rfl⟩ : syracuseStep 3673259 = 5509889) B5509889
theorem B11021507 : Blo 1449544 11021507 := bstep (se 1 (by rfl) ⟨8266130, by rfl⟩ : syracuseStep 11021507 = 16532261) B16532261
theorem B11767031 : Blo 1449544 11767031 := bstep (se 1 (by rfl) ⟨8825273, by rfl⟩ : syracuseStep 11767031 = 17650547) B17650547
theorem B3263849 : Blo 1449544 3263849 := bstep (se 2 (by rfl) ⟨1223943, by rfl⟩ : syracuseStep 3263849 = 2447887) B2447887
theorem B12397967 : Blo 1449544 12397967 := bstep (se 1 (by rfl) ⟨9298475, by rfl⟩ : syracuseStep 12397967 = 18596951) B18596951
theorem B2174543 : Blo 1449544 2174543 := bstep (se 1 (by rfl) ⟨1630907, by rfl⟩ : syracuseStep 2174543 = 3261815) B3261815
theorem B6278779 : Blo 1449544 6278779 := bstep (se 1 (by rfl) ⟨4709084, by rfl⟩ : syracuseStep 6278779 = 9418169) B9418169
theorem B4894343 : Blo 1449544 4894343 := bstep (se 1 (by rfl) ⟨3670757, by rfl⟩ : syracuseStep 4894343 = 7341515) B7341515
theorem B4894397 : Blo 1449544 4894397 := bstep (se 3 (by rfl) ⟨917699, by rfl⟩ : syracuseStep 4894397 = 1835399) B1835399
theorem B33500861 : Blo 1449544 33500861 := bstep (se 3 (by rfl) ⟨6281411, by rfl⟩ : syracuseStep 33500861 = 12562823) B12562823
theorem B2174663 : Blo 1449544 2174663 := bstep (se 1 (by rfl) ⟨1630997, by rfl⟩ : syracuseStep 2174663 = 3261995) B3261995
theorem B5508931 : Blo 1449544 5508931 := bstep (se 1 (by rfl) ⟨4131698, by rfl⟩ : syracuseStep 5508931 = 8263397) B8263397
theorem B4894559 : Blo 1449544 4894559 := bstep (se 1 (by rfl) ⟨3670919, by rfl⟩ : syracuseStep 4894559 = 7341839) B7341839
theorem B2174825 : Blo 1449544 2174825 := bstep (se 2 (by rfl) ⟨815559, by rfl⟩ : syracuseStep 2174825 = 1631119) B1631119
theorem B2174903 : Blo 1449544 2174903 := bstep (se 1 (by rfl) ⟨1631177, by rfl⟩ : syracuseStep 2174903 = 3262355) B3262355
theorem B3264443 : Blo 1449544 3264443 := bstep (se 1 (by rfl) ⟨2448332, by rfl⟩ : syracuseStep 3264443 = 4896665) B4896665
theorem B2174939 : Blo 1449544 2174939 := bstep (se 1 (by rfl) ⟨1631204, by rfl⟩ : syracuseStep 2174939 = 3262409) B3262409
theorem B4894721 : Blo 1449544 4894721 := bstep (se 2 (by rfl) ⟨1835520, by rfl⟩ : syracuseStep 4894721 = 3671041) B3671041
theorem B10457095 : Blo 1449544 10457095 := bstep (se 1 (by rfl) ⟨7842821, by rfl⟩ : syracuseStep 10457095 = 15685643) B15685643
theorem B3674119 : Blo 1449544 3674119 := bstep (se 1 (by rfl) ⟨2755589, by rfl⟩ : syracuseStep 3674119 = 5511179) B5511179
theorem B4132883 : Blo 1449544 4132883 := bstep (se 1 (by rfl) ⟨3099662, by rfl⟩ : syracuseStep 4132883 = 6199325) B6199325
theorem B3264569 : Blo 1449544 3264569 := bstep (se 2 (by rfl) ⟨1224213, by rfl⟩ : syracuseStep 3264569 = 2448427) B2448427
theorem B5509235 : Blo 1449544 5509235 := bstep (se 1 (by rfl) ⟨4131926, by rfl⟩ : syracuseStep 5509235 = 8263853) B8263853
theorem B2322761 : Blo 1449544 2322761 := bstep (se 2 (by rfl) ⟨871035, by rfl⟩ : syracuseStep 2322761 = 1742071) B1742071
theorem B3264911 : Blo 1449544 3264911 := bstep (se 1 (by rfl) ⟨2448683, by rfl⟩ : syracuseStep 3264911 = 4897367) B4897367
theorem B2175407 : Blo 1449544 2175407 := bstep (se 1 (by rfl) ⟨1631555, by rfl⟩ : syracuseStep 2175407 = 3263111) B3263111
theorem B4133339 : Blo 1449544 4133339 := bstep (se 1 (by rfl) ⟨3100004, by rfl⟩ : syracuseStep 4133339 = 6200009) B6200009
theorem B2175497 : Blo 1449544 2175497 := bstep (se 2 (by rfl) ⟨815811, by rfl⟩ : syracuseStep 2175497 = 1631623) B1631623
theorem B4837927 : Blo 1449544 4837927 := bstep (se 1 (by rfl) ⟨3628445, by rfl⟩ : syracuseStep 4837927 = 7256891) B7256891
theorem B2175527 : Blo 1449544 2175527 := bstep (se 1 (by rfl) ⟨1631645, by rfl⟩ : syracuseStep 2175527 = 3263291) B3263291
theorem B5509691 : Blo 1449544 5509691 := bstep (se 1 (by rfl) ⟨4132268, by rfl⟩ : syracuseStep 5509691 = 8264537) B8264537
theorem B2175611 : Blo 1449544 2175611 := bstep (se 1 (by rfl) ⟨1631708, by rfl⟩ : syracuseStep 2175611 = 3263417) B3263417
theorem B1987195 : Blo 1449544 1987195 := bstep (se 1 (by rfl) ⟨1490396, by rfl⟩ : syracuseStep 1987195 = 2980793) B2980793
theorem B3265235 : Blo 1449544 3265235 := bstep (se 1 (by rfl) ⟨2448926, by rfl⟩ : syracuseStep 3265235 = 4897853) B4897853
theorem B2175737 : Blo 1449544 2175737 := bstep (se 2 (by rfl) ⟨815901, by rfl⟩ : syracuseStep 2175737 = 1631803) B1631803
theorem B4895531 : Blo 1449544 4895531 := bstep (se 1 (by rfl) ⟨3671648, by rfl⟩ : syracuseStep 4895531 = 7343297) B7343297
theorem B61985587 : Blo 1449544 61985587 := bstep (se 1 (by rfl) ⟨46489190, by rfl⟩ : syracuseStep 61985587 = 92978381) B92978381
theorem B2175839 : Blo 1449544 2175839 := bstep (se 1 (by rfl) ⟨1631879, by rfl⟩ : syracuseStep 2175839 = 3263759) B3263759
theorem B2175851 : Blo 1449544 2175851 := bstep (se 1 (by rfl) ⟨1631888, by rfl⟩ : syracuseStep 2175851 = 3263777) B3263777
theorem B7345079 : Blo 1449544 7345079 := bstep (se 1 (by rfl) ⟨5508809, by rfl⟩ : syracuseStep 7345079 = 11017619) B11017619
theorem B2446267 : Blo 1449544 2446267 := bstep (se 1 (by rfl) ⟨1834700, by rfl⟩ : syracuseStep 2446267 = 3669401) B3669401
theorem B2446375 : Blo 1449544 2446375 := bstep (se 1 (by rfl) ⟨1834781, by rfl⟩ : syracuseStep 2446375 = 3669563) B3669563
theorem B4895801 : Blo 1449544 4895801 := bstep (se 2 (by rfl) ⟨1835925, by rfl⟩ : syracuseStep 4895801 = 3671851) B3671851
theorem B2176079 : Blo 1449544 2176079 := bstep (se 1 (by rfl) ⟨1632059, by rfl⟩ : syracuseStep 2176079 = 3264119) B3264119
theorem B1742023 : Blo 1449544 1742023 := bstep (se 1 (by rfl) ⟨1306517, by rfl⟩ : syracuseStep 1742023 = 2613035) B2613035
theorem B2176199 : Blo 1449544 2176199 := bstep (se 1 (by rfl) ⟨1632149, by rfl⟩ : syracuseStep 2176199 = 3264299) B3264299
theorem B2176361 : Blo 1449544 2176361 := bstep (se 2 (by rfl) ⟨816135, by rfl⟩ : syracuseStep 2176361 = 1632271) B1632271
theorem B2446699 : Blo 1449544 2446699 := bstep (se 1 (by rfl) ⟨1835024, by rfl⟩ : syracuseStep 2446699 = 3670049) B3670049
theorem B2323819 : Blo 1449544 2323819 := bstep (se 1 (by rfl) ⟨1742864, by rfl⟩ : syracuseStep 2323819 = 3485729) B3485729
theorem B4896125 : Blo 1449544 4896125 := bstep (se 3 (by rfl) ⟨918023, by rfl⟩ : syracuseStep 4896125 = 1836047) B1836047
theorem B2176439 : Blo 1449544 2176439 := bstep (se 1 (by rfl) ⟨1632329, by rfl⟩ : syracuseStep 2176439 = 3264659) B3264659
theorem B2176475 : Blo 1449544 2176475 := bstep (se 1 (by rfl) ⟨1632356, by rfl⟩ : syracuseStep 2176475 = 3264713) B3264713
theorem B52917745 : Blo 1449544 52917745 := bstep (se 2 (by rfl) ⟨19844154, by rfl⟩ : syracuseStep 52917745 = 39688309) B39688309
theorem B4896395 : Blo 1449544 4896395 := bstep (se 1 (by rfl) ⟨3672296, by rfl⟩ : syracuseStep 4896395 = 7344593) B7344593
theorem B12384161 : Blo 1449544 12384161 := bstep (se 2 (by rfl) ⟨4644060, by rfl⟩ : syracuseStep 12384161 = 9288121) B9288121
theorem B2176943 : Blo 1449544 2176943 := bstep (se 1 (by rfl) ⟨1632707, by rfl⟩ : syracuseStep 2176943 = 3265415) B3265415
theorem B16529345 : Blo 1449544 16529345 := bstep (se 2 (by rfl) ⟨6198504, by rfl⟩ : syracuseStep 16529345 = 12397009) B12397009
theorem B2177033 : Blo 1449544 2177033 := bstep (se 2 (by rfl) ⟨816387, by rfl⟩ : syracuseStep 2177033 = 1632775) B1632775
theorem B2177063 : Blo 1449544 2177063 := bstep (se 1 (by rfl) ⟨1632797, by rfl⟩ : syracuseStep 2177063 = 3265595) B3265595
theorem B2177147 : Blo 1449544 2177147 := bstep (se 1 (by rfl) ⟨1632860, by rfl⟩ : syracuseStep 2177147 = 3265721) B3265721
theorem B3225847 : Blo 1449544 3225847 := bstep (se 1 (by rfl) ⟨2419385, by rfl⟩ : syracuseStep 3225847 = 4838771) B4838771
theorem B2177273 : Blo 1449544 2177273 := bstep (se 2 (by rfl) ⟨816477, by rfl⟩ : syracuseStep 2177273 = 1632955) B1632955
theorem B59513089 : Blo 1449544 59513089 := bstep (se 2 (by rfl) ⟨22317408, by rfl⟩ : syracuseStep 59513089 = 44634817) B44634817
theorem B7346537 : Blo 1449544 7346537 := bstep (se 2 (by rfl) ⟨2754951, by rfl⟩ : syracuseStep 7346537 = 5509903) B5509903
theorem B11008385 : Blo 1449544 11008385 := bstep (se 2 (by rfl) ⟨4128144, by rfl⟩ : syracuseStep 11008385 = 8256289) B8256289
theorem B2447759 : Blo 1449544 2447759 := bstep (se 1 (by rfl) ⟨1835819, by rfl⟩ : syracuseStep 2447759 = 3671639) B3671639
theorem B1743287 : Blo 1449544 1743287 := bstep (se 1 (by rfl) ⟨1307465, by rfl⟩ : syracuseStep 1743287 = 2614931) B2614931
theorem B8370697 : Blo 1449544 8370697 := bstep (se 2 (by rfl) ⟨3139011, by rfl⟩ : syracuseStep 8370697 = 6278023) B6278023
theorem B4897313 : Blo 1449544 4897313 := bstep (se 2 (by rfl) ⟨1836492, by rfl⟩ : syracuseStep 4897313 = 3672985) B3672985
theorem B41802317 : Blo 1449544 41802317 := bstep (se 3 (by rfl) ⟨7837934, by rfl⟩ : syracuseStep 41802317 = 15675869) B15675869
theorem B2480719 : Blo 1449544 2480719 := bstep (se 1 (by rfl) ⟨1860539, by rfl⟩ : syracuseStep 2480719 = 3721079) B3721079
theorem B2447995 : Blo 1449544 2447995 := bstep (se 1 (by rfl) ⟨1835996, by rfl⟩ : syracuseStep 2447995 = 3671993) B3671993
theorem B4897529 : Blo 1449544 4897529 := bstep (se 2 (by rfl) ⟨1836573, by rfl⟩ : syracuseStep 4897529 = 3673147) B3673147
theorem B6617929 : Blo 1449544 6617929 := bstep (se 2 (by rfl) ⟨2481723, by rfl⟩ : syracuseStep 6617929 = 4963447) B4963447
theorem B1073724245 : Blo 1449544 1073724245 := bstep (se 9 (by rfl) ⟨3145676, by rfl⟩ : syracuseStep 1073724245 = 6291353) B6291353
theorem B4897799 : Blo 1449544 4897799 := bstep (se 1 (by rfl) ⟨3673349, by rfl⟩ : syracuseStep 4897799 = 7346699) B7346699
theorem B8256563 : Blo 1449544 8256563 := bstep (se 1 (by rfl) ⟨6192422, by rfl⟩ : syracuseStep 8256563 = 12384845) B12384845
theorem B5504057 : Blo 1449544 5504057 := bstep (se 2 (by rfl) ⟨2064021, by rfl⟩ : syracuseStep 5504057 = 4128043) B4128043
theorem B4897907 : Blo 1449544 4897907 := bstep (se 1 (by rfl) ⟨3673430, by rfl⟩ : syracuseStep 4897907 = 7346861) B7346861
theorem B1653959 : Blo 1449544 1653959 := bstep (se 1 (by rfl) ⟨1240469, by rfl⟩ : syracuseStep 1653959 = 2480939) B2480939
theorem B3669239 : Blo 1449544 3669239 := bstep (se 1 (by rfl) ⟨2751929, by rfl⟩ : syracuseStep 3669239 = 5503859) B5503859
theorem B5881079 : Blo 1449544 5881079 := bstep (se 1 (by rfl) ⟨4410809, by rfl⟩ : syracuseStep 5881079 = 8821619) B8821619
theorem B9297143 : Blo 1449544 9297143 := bstep (se 1 (by rfl) ⟨6972857, by rfl⟩ : syracuseStep 9297143 = 13945715) B13945715
theorem B20913497 : Blo 1449544 20913497 := bstep (se 2 (by rfl) ⟨7842561, by rfl⟩ : syracuseStep 20913497 = 15685123) B15685123
theorem B4185473 : Blo 1449544 4185473 := bstep (se 2 (by rfl) ⟨1569552, by rfl⟩ : syracuseStep 4185473 = 3139105) B3139105
theorem B4898177 : Blo 1449544 4898177 := bstep (se 2 (by rfl) ⟨1836816, by rfl⟩ : syracuseStep 4898177 = 3673633) B3673633
theorem B181140941 : Blo 1449544 181140941 := bstep (se 3 (by rfl) ⟨33963926, by rfl⟩ : syracuseStep 181140941 = 67927853) B67927853
theorem B2448859 : Blo 1449544 2448859 := bstep (se 1 (by rfl) ⟨1836644, by rfl⟩ : syracuseStep 2448859 = 3673289) B3673289
theorem B12393971 : Blo 1449544 12393971 := bstep (se 1 (by rfl) ⟨9295478, by rfl⟩ : syracuseStep 12393971 = 18590957) B18590957
theorem B2481671 : Blo 1449544 2481671 := bstep (se 1 (by rfl) ⟨1861253, by rfl⟩ : syracuseStep 2481671 = 3722507) B3722507
theorem B11755019 : Blo 1449544 11755019 := bstep (se 1 (by rfl) ⟨8816264, by rfl⟩ : syracuseStep 11755019 = 17632529) B17632529
theorem B1449551 : Blo 1449544 1449551 := bstep (se 1 (by rfl) ⟨1087163, by rfl⟩ : syracuseStep 1449551 = 2174327) B2174327
theorem B1449567 : Blo 1449544 1449567 := bstep (se 1 (by rfl) ⟨1087175, by rfl⟩ : syracuseStep 1449567 = 2174351) B2174351
theorem B1449595 : Blo 1449544 1449595 := bstep (se 1 (by rfl) ⟨1087196, by rfl⟩ : syracuseStep 1449595 = 2174393) B2174393
theorem B11763323 : Blo 1449544 11763323 := bstep (se 1 (by rfl) ⟨8822492, by rfl⟩ : syracuseStep 11763323 = 17644985) B17644985
theorem B1449647 : Blo 1449544 1449647 := bstep (se 1 (by rfl) ⟨1087235, by rfl⟩ : syracuseStep 1449647 = 2174471) B2174471
theorem B1449671 : Blo 1449544 1449671 := bstep (se 1 (by rfl) ⟨1087253, by rfl⟩ : syracuseStep 1449671 = 2174507) B2174507
theorem B2752211 : Blo 1449544 2752211 := bstep (se 1 (by rfl) ⟨2064158, by rfl⟩ : syracuseStep 2752211 = 4128317) B4128317
theorem B1449691 : Blo 1449544 1449691 := bstep (se 1 (by rfl) ⟨1087268, by rfl⟩ : syracuseStep 1449691 = 2174537) B2174537
theorem B1449767 : Blo 1449544 1449767 := bstep (se 1 (by rfl) ⟨1087325, by rfl⟩ : syracuseStep 1449767 = 2174651) B2174651
theorem B1449807 : Blo 1449544 1449807 := bstep (se 1 (by rfl) ⟨1087355, by rfl⟩ : syracuseStep 1449807 = 2174711) B2174711
theorem B1449823 : Blo 1449544 1449823 := bstep (se 1 (by rfl) ⟨1087367, by rfl⟩ : syracuseStep 1449823 = 2174735) B2174735
theorem B7339895 : Blo 1449544 7339895 := bstep (se 1 (by rfl) ⟨5504921, by rfl⟩ : syracuseStep 7339895 = 11009843) B11009843
theorem B1449851 : Blo 1449544 1449851 := bstep (se 1 (by rfl) ⟨1087388, by rfl⟩ : syracuseStep 1449851 = 2174777) B2174777
theorem B1449903 : Blo 1449544 1449903 := bstep (se 1 (by rfl) ⟨1087427, by rfl⟩ : syracuseStep 1449903 = 2174855) B2174855
theorem B1449927 : Blo 1449544 1449927 := bstep (se 1 (by rfl) ⟨1087445, by rfl⟩ : syracuseStep 1449927 = 2174891) B2174891
theorem B1449947 : Blo 1449544 1449947 := bstep (se 1 (by rfl) ⟨1087460, by rfl⟩ : syracuseStep 1449947 = 2174921) B2174921
theorem B13942793 : Blo 1449544 13942793 := bstep (se 2 (by rfl) ⟨5228547, by rfl⟩ : syracuseStep 13942793 = 10457095) B10457095
theorem B4898825 : Blo 1449544 4898825 := bstep (se 2 (by rfl) ⟨1837059, by rfl⟩ : syracuseStep 4898825 = 3674119) B3674119
theorem B7340057 : Blo 1449544 7340057 := bstep (se 2 (by rfl) ⟨2752521, by rfl⟩ : syracuseStep 7340057 = 5505043) B5505043
theorem B8257747 : Blo 1449544 8257747 := bstep (se 1 (by rfl) ⟨6193310, by rfl⟩ : syracuseStep 8257747 = 12386621) B12386621
theorem B1835227 : Blo 1449544 1835227 := bstep (se 1 (by rfl) ⟨1376420, by rfl⟩ : syracuseStep 1835227 = 2752841) B2752841
theorem B1450271 : Blo 1449544 1450271 := bstep (se 1 (by rfl) ⟨1087703, by rfl⟩ : syracuseStep 1450271 = 2175407) B2175407
theorem B4301129 : Blo 1449544 4301129 := bstep (se 2 (by rfl) ⟨1612923, by rfl⟩ : syracuseStep 4301129 = 3225847) B3225847
theorem B1450331 : Blo 1449544 1450331 := bstep (se 1 (by rfl) ⟨1087748, by rfl⟩ : syracuseStep 1450331 = 2175497) B2175497
theorem B2752879 : Blo 1449544 2752879 := bstep (se 1 (by rfl) ⟨2064659, by rfl⟩ : syracuseStep 2752879 = 4129319) B4129319
theorem B1450351 : Blo 1449544 1450351 := bstep (se 1 (by rfl) ⟨1087763, by rfl⟩ : syracuseStep 1450351 = 2175527) B2175527
theorem B31375781 : Blo 1449544 31375781 := bstep (se 4 (by rfl) ⟨2941479, by rfl⟩ : syracuseStep 31375781 = 5882959) B5882959
theorem B1450407 : Blo 1449544 1450407 := bstep (se 1 (by rfl) ⟨1087805, by rfl⟩ : syracuseStep 1450407 = 2175611) B2175611
theorem B1450491 : Blo 1449544 1450491 := bstep (se 1 (by rfl) ⟨1087868, by rfl⟩ : syracuseStep 1450491 = 2175737) B2175737
theorem B1450559 : Blo 1449544 1450559 := bstep (se 1 (by rfl) ⟨1087919, by rfl⟩ : syracuseStep 1450559 = 2175839) B2175839
theorem B1450567 : Blo 1449544 1450567 := bstep (se 1 (by rfl) ⟨1087925, by rfl⟩ : syracuseStep 1450567 = 2175851) B2175851
theorem B9298577 : Blo 1449544 9298577 := bstep (se 2 (by rfl) ⟨3486966, by rfl⟩ : syracuseStep 9298577 = 6973933) B6973933
theorem B3097271 : Blo 1449544 3097271 := bstep (se 1 (by rfl) ⟨2322953, by rfl⟩ : syracuseStep 3097271 = 4645907) B4645907
theorem B1450719 : Blo 1449544 1450719 := bstep (se 1 (by rfl) ⟨1088039, by rfl⟩ : syracuseStep 1450719 = 2176079) B2176079
theorem B1450799 : Blo 1449544 1450799 := bstep (se 1 (by rfl) ⟨1088099, by rfl⟩ : syracuseStep 1450799 = 2176199) B2176199
theorem B6194029 : Blo 1449544 6194029 := bstep (se 3 (by rfl) ⟨1161380, by rfl⟩ : syracuseStep 6194029 = 2322761) B2322761
theorem B23528339 : Blo 1449544 23528339 := bstep (se 1 (by rfl) ⟨17646254, by rfl⟩ : syracuseStep 23528339 = 35292509) B35292509
theorem B1450907 : Blo 1449544 1450907 := bstep (se 1 (by rfl) ⟨1088180, by rfl⟩ : syracuseStep 1450907 = 2176361) B2176361
theorem B1450959 : Blo 1449544 1450959 := bstep (se 1 (by rfl) ⟨1088219, by rfl⟩ : syracuseStep 1450959 = 2176439) B2176439
theorem B1450983 : Blo 1449544 1450983 := bstep (se 1 (by rfl) ⟨1088237, by rfl⟩ : syracuseStep 1450983 = 2176475) B2176475
theorem B8823905 : Blo 1449544 8823905 := bstep (se 2 (by rfl) ⟨3308964, by rfl⟩ : syracuseStep 8823905 = 6617929) B6617929
theorem B3261563 : Blo 1449544 3261563 := bstep (se 1 (by rfl) ⟨2446172, by rfl⟩ : syracuseStep 3261563 = 4892345) B4892345
theorem B3671183 : Blo 1449544 3671183 := bstep (se 1 (by rfl) ⟨2753387, by rfl⟩ : syracuseStep 3671183 = 5506775) B5506775
theorem B4129991 : Blo 1449544 4129991 := bstep (se 1 (by rfl) ⟨3097493, by rfl⟩ : syracuseStep 4129991 = 6194987) B6194987
theorem B3261689 : Blo 1449544 3261689 := bstep (se 2 (by rfl) ⟨1223133, by rfl⟩ : syracuseStep 3261689 = 2446267) B2446267
theorem B1451295 : Blo 1449544 1451295 := bstep (se 1 (by rfl) ⟨1088471, by rfl⟩ : syracuseStep 1451295 = 2176943) B2176943
theorem B11019563 : Blo 1449544 11019563 := bstep (se 1 (by rfl) ⟨8264672, by rfl⟩ : syracuseStep 11019563 = 16529345) B16529345
theorem B9291095 : Blo 1449544 9291095 := bstep (se 1 (by rfl) ⟨6968321, by rfl⟩ : syracuseStep 9291095 = 13936643) B13936643
theorem B1451355 : Blo 1449544 1451355 := bstep (se 1 (by rfl) ⟨1088516, by rfl⟩ : syracuseStep 1451355 = 2177033) B2177033
theorem B1451375 : Blo 1449544 1451375 := bstep (se 1 (by rfl) ⟨1088531, by rfl⟩ : syracuseStep 1451375 = 2177063) B2177063
theorem B3261833 : Blo 1449544 3261833 := bstep (se 2 (by rfl) ⟨1223187, by rfl⟩ : syracuseStep 3261833 = 2446375) B2446375
theorem B1451431 : Blo 1449544 1451431 := bstep (se 1 (by rfl) ⟨1088573, by rfl⟩ : syracuseStep 1451431 = 2177147) B2177147
theorem B1451515 : Blo 1449544 1451515 := bstep (se 1 (by rfl) ⟨1088636, by rfl⟩ : syracuseStep 1451515 = 2177273) B2177273
theorem B3261959 : Blo 1449544 3261959 := bstep (se 1 (by rfl) ⟨2446469, by rfl⟩ : syracuseStep 3261959 = 4892939) B4892939
theorem B1631839 : Blo 1449544 1631839 := bstep (se 1 (by rfl) ⟨1223879, by rfl⟩ : syracuseStep 1631839 = 2447759) B2447759
theorem B3262139 : Blo 1449544 3262139 := bstep (se 1 (by rfl) ⟨2446604, by rfl⟩ : syracuseStep 3262139 = 4893209) B4893209
theorem B6620957 : Blo 1449544 6620957 := bstep (se 3 (by rfl) ⟨1241429, by rfl⟩ : syracuseStep 6620957 = 2482859) B2482859
theorem B1836847 : Blo 1449544 1836847 := bstep (se 1 (by rfl) ⟨1377635, by rfl⟩ : syracuseStep 1836847 = 2755271) B2755271
theorem B3262265 : Blo 1449544 3262265 := bstep (se 2 (by rfl) ⟨1223349, by rfl⟩ : syracuseStep 3262265 = 2446699) B2446699
theorem B3098425 : Blo 1449544 3098425 := bstep (se 2 (by rfl) ⟨1161909, by rfl⟩ : syracuseStep 3098425 = 2323819) B2323819
theorem B120760627 : Blo 1449544 120760627 := bstep (se 1 (by rfl) ⟨90570470, by rfl⟩ : syracuseStep 120760627 = 181140941) B181140941
theorem B7842215 : Blo 1449544 7842215 := bstep (se 1 (by rfl) ⟨5881661, by rfl⟩ : syracuseStep 7842215 = 11763323) B11763323
theorem B3262895 : Blo 1449544 3262895 := bstep (se 1 (by rfl) ⟨2447171, by rfl⟩ : syracuseStep 3262895 = 4894343) B4894343
theorem B3262931 : Blo 1449544 3262931 := bstep (se 1 (by rfl) ⟨2447198, by rfl⟩ : syracuseStep 3262931 = 4894397) B4894397
theorem B22333907 : Blo 1449544 22333907 := bstep (se 1 (by rfl) ⟨16750430, by rfl⟩ : syracuseStep 22333907 = 33500861) B33500861
theorem B3263039 : Blo 1449544 3263039 := bstep (se 1 (by rfl) ⟨2447279, by rfl⟩ : syracuseStep 3263039 = 4894559) B4894559
theorem B4893263 : Blo 1449544 4893263 := bstep (se 1 (by rfl) ⟨3669947, by rfl⟩ : syracuseStep 4893263 = 7339895) B7339895
theorem B3263147 : Blo 1449544 3263147 := bstep (se 1 (by rfl) ⟨2447360, by rfl⟩ : syracuseStep 3263147 = 4894721) B4894721
theorem B11021021 : Blo 1449544 11021021 := bstep (se 3 (by rfl) ⟨2066441, by rfl⟩ : syracuseStep 11021021 = 4132883) B4132883
theorem B3672823 : Blo 1449544 3672823 := bstep (se 1 (by rfl) ⟨2754617, by rfl⟩ : syracuseStep 3672823 = 5509235) B5509235
theorem B7342973 : Blo 1449544 7342973 := bstep (se 3 (by rfl) ⟨1376807, by rfl⟩ : syracuseStep 7342973 = 2753615) B2753615
theorem B20130713 : Blo 1449544 20130713 := bstep (se 2 (by rfl) ⟨7549017, by rfl⟩ : syracuseStep 20130713 = 15098035) B15098035
theorem B2755559 : Blo 1449544 2755559 := bstep (se 1 (by rfl) ⟨2066669, by rfl⟩ : syracuseStep 2755559 = 4133339) B4133339
theorem B79350785 : Blo 1449544 79350785 := bstep (se 2 (by rfl) ⟨29756544, by rfl⟩ : syracuseStep 79350785 = 59513089) B59513089
theorem B3673127 : Blo 1449544 3673127 := bstep (se 1 (by rfl) ⟨2754845, by rfl⟩ : syracuseStep 3673127 = 5509691) B5509691
theorem B4410557 : Blo 1449544 4410557 := bstep (se 3 (by rfl) ⟨826979, by rfl⟩ : syracuseStep 4410557 = 1653959) B1653959
theorem B3263687 : Blo 1449544 3263687 := bstep (se 1 (by rfl) ⟨2447765, by rfl⟩ : syracuseStep 3263687 = 4895531) B4895531
theorem B3484891 : Blo 1449544 3484891 := bstep (se 1 (by rfl) ⟨2613668, by rfl⟩ : syracuseStep 3484891 = 5227337) B5227337
theorem B11160929 : Blo 1449544 11160929 := bstep (se 2 (by rfl) ⟨4185348, by rfl⟩ : syracuseStep 11160929 = 8370697) B8370697
theorem B11169143 : Blo 1449544 11169143 := bstep (se 1 (by rfl) ⟨8376857, by rfl⟩ : syracuseStep 11169143 = 16753715) B16753715
theorem B3263867 : Blo 1449544 3263867 := bstep (se 1 (by rfl) ⟨2447900, by rfl⟩ : syracuseStep 3263867 = 4895801) B4895801
theorem B2174345 : Blo 1449544 2174345 := bstep (se 2 (by rfl) ⟨815379, by rfl⟩ : syracuseStep 2174345 = 1630759) B1630759
theorem B6450569 : Blo 1449544 6450569 := bstep (se 2 (by rfl) ⟨2418963, by rfl⟩ : syracuseStep 6450569 = 4837927) B4837927
theorem B3485065 : Blo 1449544 3485065 := bstep (se 2 (by rfl) ⟨1306899, by rfl⟩ : syracuseStep 3485065 = 2613799) B2613799
theorem B2649593 : Blo 1449544 2649593 := bstep (se 2 (by rfl) ⟨993597, by rfl⟩ : syracuseStep 2649593 = 1987195) B1987195
theorem B3263993 : Blo 1449544 3263993 := bstep (se 2 (by rfl) ⟨1223997, by rfl⟩ : syracuseStep 3263993 = 2447995) B2447995
theorem B3264083 : Blo 1449544 3264083 := bstep (se 1 (by rfl) ⟨2448062, by rfl⟩ : syracuseStep 3264083 = 4896125) B4896125
theorem B11161261 : Blo 1449544 11161261 := bstep (se 3 (by rfl) ⟨2092736, by rfl⟩ : syracuseStep 11161261 = 4185473) B4185473
theorem B2174699 : Blo 1449544 2174699 := bstep (se 1 (by rfl) ⟨1631024, by rfl⟩ : syracuseStep 2174699 = 3262049) B3262049
theorem B3264263 : Blo 1449544 3264263 := bstep (se 1 (by rfl) ⟨2448197, by rfl⟩ : syracuseStep 3264263 = 4896395) B4896395
theorem B4894505 : Blo 1449544 4894505 := bstep (se 2 (by rfl) ⟨1835439, by rfl⟩ : syracuseStep 4894505 = 3670879) B3670879
theorem B4648765 : Blo 1449544 4648765 := bstep (se 3 (by rfl) ⟨871643, by rfl⟩ : syracuseStep 4648765 = 1743287) B1743287
theorem B7343945 : Blo 1449544 7343945 := bstep (se 2 (by rfl) ⟨2753979, by rfl⟩ : syracuseStep 7343945 = 5507959) B5507959
theorem B2174927 : Blo 1449544 2174927 := bstep (se 1 (by rfl) ⟨1631195, by rfl⟩ : syracuseStep 2174927 = 3262391) B3262391
theorem B13938641 : Blo 1449544 13938641 := bstep (se 2 (by rfl) ⟨5226990, by rfl⟩ : syracuseStep 13938641 = 10453981) B10453981
theorem B2322697 : Blo 1449544 2322697 := bstep (se 2 (by rfl) ⟨871011, by rfl⟩ : syracuseStep 2322697 = 1742023) B1742023
theorem B2175323 : Blo 1449544 2175323 := bstep (se 1 (by rfl) ⟨1631492, by rfl⟩ : syracuseStep 2175323 = 3262985) B3262985
theorem B3264875 : Blo 1449544 3264875 := bstep (se 1 (by rfl) ⟨2448656, by rfl⟩ : syracuseStep 3264875 = 4897313) B4897313
theorem B2322799 : Blo 1449544 2322799 := bstep (se 1 (by rfl) ⟨1742099, by rfl⟩ : syracuseStep 2322799 = 3484199) B3484199
theorem B3265019 : Blo 1449544 3265019 := bstep (se 1 (by rfl) ⟨2448764, by rfl⟩ : syracuseStep 3265019 = 4897529) B4897529
theorem B5878291 : Blo 1449544 5878291 := bstep (se 1 (by rfl) ⟨4408718, by rfl⟩ : syracuseStep 5878291 = 8817437) B8817437
theorem B2175551 : Blo 1449544 2175551 := bstep (se 1 (by rfl) ⟨1631663, by rfl⟩ : syracuseStep 2175551 = 3263327) B3263327
theorem B25113185 : Blo 1449544 25113185 := bstep (se 2 (by rfl) ⟨9417444, by rfl⟩ : syracuseStep 25113185 = 18834889) B18834889
theorem B3265145 : Blo 1449544 3265145 := bstep (se 2 (by rfl) ⟨1224429, by rfl⟩ : syracuseStep 3265145 = 2448859) B2448859
theorem B3265199 : Blo 1449544 3265199 := bstep (se 1 (by rfl) ⟨2448899, by rfl⟩ : syracuseStep 3265199 = 4897799) B4897799
theorem B2175671 : Blo 1449544 2175671 := bstep (se 1 (by rfl) ⟨1631753, by rfl⟩ : syracuseStep 2175671 = 3263507) B3263507
theorem B2355895 : Blo 1449544 2355895 := bstep (se 1 (by rfl) ⟨1766921, by rfl⟩ : syracuseStep 2355895 = 3533843) B3533843
theorem B3265271 : Blo 1449544 3265271 := bstep (se 1 (by rfl) ⟨2448953, by rfl⟩ : syracuseStep 3265271 = 4897907) B4897907
theorem B2446159 : Blo 1449544 2446159 := bstep (se 1 (by rfl) ⟨1834619, by rfl⟩ : syracuseStep 2446159 = 3669239) B3669239
theorem B3920719 : Blo 1449544 3920719 := bstep (se 1 (by rfl) ⟨2940539, by rfl⟩ : syracuseStep 3920719 = 5881079) B5881079
theorem B6198095 : Blo 1449544 6198095 := bstep (se 1 (by rfl) ⟨4648571, by rfl⟩ : syracuseStep 6198095 = 9297143) B9297143
theorem B7844687 : Blo 1449544 7844687 := bstep (se 1 (by rfl) ⟨5883515, by rfl⟩ : syracuseStep 7844687 = 11767031) B11767031
theorem B2175899 : Blo 1449544 2175899 := bstep (se 1 (by rfl) ⟨1631924, by rfl⟩ : syracuseStep 2175899 = 3263849) B3263849
theorem B3265451 : Blo 1449544 3265451 := bstep (se 1 (by rfl) ⟨2449088, by rfl⟩ : syracuseStep 3265451 = 4898177) B4898177
theorem B8262647 : Blo 1449544 8262647 := bstep (se 1 (by rfl) ⟨6196985, by rfl⟩ : syracuseStep 8262647 = 12393971) B12393971
theorem B7836679 : Blo 1449544 7836679 := bstep (se 1 (by rfl) ⟨5877509, by rfl⟩ : syracuseStep 7836679 = 11755019) B11755019
theorem B7345241 : Blo 1449544 7345241 := bstep (se 2 (by rfl) ⟨2754465, by rfl⟩ : syracuseStep 7345241 = 5508931) B5508931
theorem B17216657 : Blo 1449544 17216657 := bstep (se 2 (by rfl) ⟨6456246, by rfl⟩ : syracuseStep 17216657 = 12912493) B12912493
theorem B2176295 : Blo 1449544 2176295 := bstep (se 1 (by rfl) ⟨1632221, by rfl⟩ : syracuseStep 2176295 = 3264443) B3264443
theorem B2176379 : Blo 1449544 2176379 := bstep (se 1 (by rfl) ⟨1632284, by rfl⟩ : syracuseStep 2176379 = 3264569) B3264569
theorem B2446841 : Blo 1449544 2446841 := bstep (se 2 (by rfl) ⟨917565, by rfl⟩ : syracuseStep 2446841 = 1835131) B1835131
theorem B2176505 : Blo 1449544 2176505 := bstep (se 2 (by rfl) ⟨816189, by rfl⟩ : syracuseStep 2176505 = 1632379) B1632379
theorem B5510663 : Blo 1449544 5510663 := bstep (se 1 (by rfl) ⟨4132997, by rfl⟩ : syracuseStep 5510663 = 8265995) B8265995
theorem B2176607 : Blo 1449544 2176607 := bstep (se 1 (by rfl) ⟨1632455, by rfl⟩ : syracuseStep 2176607 = 3264911) B3264911
theorem B2447111 : Blo 1449544 2447111 := bstep (se 1 (by rfl) ⟨1835333, by rfl⟩ : syracuseStep 2447111 = 3670667) B3670667
theorem B2176823 : Blo 1449544 2176823 := bstep (se 1 (by rfl) ⟨1632617, by rfl⟩ : syracuseStep 2176823 = 3265235) B3265235
theorem B4896719 : Blo 1449544 4896719 := bstep (se 1 (by rfl) ⟨3672539, by rfl⟩ : syracuseStep 4896719 = 7345079) B7345079
theorem B33486821 : Blo 1449544 33486821 := bstep (se 4 (by rfl) ⟨3139389, by rfl⟩ : syracuseStep 33486821 = 6278779) B6278779
theorem B5511149 : Blo 1449544 5511149 := bstep (se 3 (by rfl) ⟨1033340, by rfl⟩ : syracuseStep 5511149 = 2066681) B2066681
theorem B3307625 : Blo 1449544 3307625 := bstep (se 2 (by rfl) ⟨1240359, by rfl⟩ : syracuseStep 3307625 = 2480719) B2480719
theorem B2177129 : Blo 1449544 2177129 := bstep (se 2 (by rfl) ⟨816423, by rfl⟩ : syracuseStep 2177129 = 1632847) B1632847
theorem B7157945 : Blo 1449544 7157945 := bstep (se 2 (by rfl) ⟨2684229, by rfl⟩ : syracuseStep 7157945 = 5368459) B5368459
theorem B82647449 : Blo 1449544 82647449 := bstep (se 2 (by rfl) ⟨30992793, by rfl⟩ : syracuseStep 82647449 = 61985587) B61985587
theorem B6199735 : Blo 1449544 6199735 := bstep (se 1 (by rfl) ⟨4649801, by rfl⟩ : syracuseStep 6199735 = 9299603) B9299603
theorem B2447867 : Blo 1449544 2447867 := bstep (se 1 (by rfl) ⟨1835900, by rfl⟩ : syracuseStep 2447867 = 3671801) B3671801
theorem B6969935 : Blo 1449544 6969935 := bstep (se 1 (by rfl) ⟨5227451, by rfl⟩ : syracuseStep 6969935 = 10454903) B10454903
theorem B1743455 : Blo 1449544 1743455 := bstep (se 1 (by rfl) ⟨1307591, by rfl⟩ : syracuseStep 1743455 = 2615183) B2615183
theorem B8256107 : Blo 1449544 8256107 := bstep (se 1 (by rfl) ⟨6192080, by rfl⟩ : syracuseStep 8256107 = 12384161) B12384161
theorem B4897691 : Blo 1449544 4897691 := bstep (se 1 (by rfl) ⟨3673268, by rfl⟩ : syracuseStep 4897691 = 7346537) B7346537
theorem B7338923 : Blo 1449544 7338923 := bstep (se 1 (by rfl) ⟨5504192, by rfl⟩ : syracuseStep 7338923 = 11008385) B11008385
theorem B2448299 : Blo 1449544 2448299 := bstep (se 1 (by rfl) ⟨1836224, by rfl⟩ : syracuseStep 2448299 = 3672449) B3672449
theorem B11017133 : Blo 1449544 11017133 := bstep (se 3 (by rfl) ⟨2065712, by rfl⟩ : syracuseStep 11017133 = 4131425) B4131425
theorem B31366091 : Blo 1449544 31366091 := bstep (se 1 (by rfl) ⟨23524568, by rfl⟩ : syracuseStep 31366091 = 47049137) B47049137
theorem B27868211 : Blo 1449544 27868211 := bstep (se 1 (by rfl) ⟨20901158, by rfl⟩ : syracuseStep 27868211 = 41802317) B41802317
theorem B715816163 : Blo 1449544 715816163 := bstep (se 1 (by rfl) ⟨536862122, by rfl⟩ : syracuseStep 715816163 = 1073724245) B1073724245
theorem B13941989 : Blo 1449544 13941989 := bstep (se 4 (by rfl) ⟨1307061, by rfl⟩ : syracuseStep 13941989 = 2614123) B2614123
theorem B70556993 : Blo 1449544 70556993 := bstep (se 2 (by rfl) ⟨26458872, by rfl⟩ : syracuseStep 70556993 = 52917745) B52917745
theorem B5504375 : Blo 1449544 5504375 := bstep (se 1 (by rfl) ⟨4128281, by rfl⟩ : syracuseStep 5504375 = 8256563) B8256563
theorem B3669371 : Blo 1449544 3669371 := bstep (se 1 (by rfl) ⟨2752028, by rfl⟩ : syracuseStep 3669371 = 5504057) B5504057
theorem B2448839 : Blo 1449544 2448839 := bstep (se 1 (by rfl) ⟨1836629, by rfl⟩ : syracuseStep 2448839 = 3673259) B3673259
theorem B7347671 : Blo 1449544 7347671 := bstep (se 1 (by rfl) ⟨5510753, by rfl⟩ : syracuseStep 7347671 = 11021507) B11021507
theorem B13942331 : Blo 1449544 13942331 := bstep (se 1 (by rfl) ⟨10456748, by rfl⟩ : syracuseStep 13942331 = 20913497) B20913497
theorem B8265311 : Blo 1449544 8265311 := bstep (se 1 (by rfl) ⟨6198983, by rfl⟩ : syracuseStep 8265311 = 12397967) B12397967
theorem B1654447 : Blo 1449544 1654447 := bstep (se 1 (by rfl) ⟨1240835, by rfl⟩ : syracuseStep 1654447 = 2481671) B2481671
theorem B1449695 : Blo 1449544 1449695 := bstep (se 1 (by rfl) ⟨1087271, by rfl⟩ : syracuseStep 1449695 = 2174543) B2174543
theorem B1449775 : Blo 1449544 1449775 := bstep (se 1 (by rfl) ⟨1087331, by rfl⟩ : syracuseStep 1449775 = 2174663) B2174663
theorem B1834807 : Blo 1449544 1834807 := bstep (se 1 (by rfl) ⟨1376105, by rfl⟩ : syracuseStep 1834807 = 2752211) B2752211
theorem B4644665 : Blo 1449544 4644665 := bstep (se 2 (by rfl) ⟨1741749, by rfl⟩ : syracuseStep 4644665 = 3483499) B3483499
theorem B105930625 : Blo 1449544 105930625 := bstep (se 2 (by rfl) ⟨39723984, by rfl⟩ : syracuseStep 105930625 = 79447969) B79447969
theorem B1449883 : Blo 1449544 1449883 := bstep (se 1 (by rfl) ⟨1087412, by rfl⟩ : syracuseStep 1449883 = 2174825) B2174825
theorem B4898717 : Blo 1449544 4898717 := bstep (se 3 (by rfl) ⟨918509, by rfl⟩ : syracuseStep 4898717 = 1837019) B1837019
theorem B1449935 : Blo 1449544 1449935 := bstep (se 1 (by rfl) ⟨1087451, by rfl⟩ : syracuseStep 1449935 = 2174903) B2174903
theorem B1449959 : Blo 1449544 1449959 := bstep (se 1 (by rfl) ⟨1087469, by rfl⟩ : syracuseStep 1449959 = 2174939) B2174939
theorem B41795621 : Blo 1449544 41795621 := bstep (se 4 (by rfl) ⟨3918339, by rfl⟩ : syracuseStep 41795621 = 7836679) B7836679
theorem B2867419 : Blo 1449544 2867419 := bstep (se 1 (by rfl) ⟨2150564, by rfl⟩ : syracuseStep 2867419 = 4301129) B4301129
theorem B1450215 : Blo 1449544 1450215 := bstep (se 1 (by rfl) ⟨1087661, by rfl⟩ : syracuseStep 1450215 = 2175323) B2175323
theorem B11010329 : Blo 1449544 11010329 := bstep (se 2 (by rfl) ⟨4128873, by rfl⟩ : syracuseStep 11010329 = 8257747) B8257747
theorem B3096929 : Blo 1449544 3096929 := bstep (se 2 (by rfl) ⟨1161348, by rfl⟩ : syracuseStep 3096929 = 2322697) B2322697
theorem B1450367 : Blo 1449544 1450367 := bstep (se 1 (by rfl) ⟨1087775, by rfl⟩ : syracuseStep 1450367 = 2175551) B2175551
theorem B161014169 : Blo 1449544 161014169 := bstep (se 2 (by rfl) ⟨60380313, by rfl⟩ : syracuseStep 161014169 = 120760627) B120760627
theorem B2064847 : Blo 1449544 2064847 := bstep (se 1 (by rfl) ⟨1548635, by rfl⟩ : syracuseStep 2064847 = 3097271) B3097271
theorem B1450447 : Blo 1449544 1450447 := bstep (se 1 (by rfl) ⟨1087835, by rfl⟩ : syracuseStep 1450447 = 2175671) B2175671
theorem B3670505 : Blo 1449544 3670505 := bstep (se 2 (by rfl) ⟨1376439, by rfl⟩ : syracuseStep 3670505 = 2752879) B2752879
theorem B8266313 : Blo 1449544 8266313 := bstep (se 2 (by rfl) ⟨3099867, by rfl⟩ : syracuseStep 8266313 = 6199735) B6199735
theorem B1450599 : Blo 1449544 1450599 := bstep (se 1 (by rfl) ⟨1087949, by rfl⟩ : syracuseStep 1450599 = 2175899) B2175899
theorem B5882603 : Blo 1449544 5882603 := bstep (se 1 (by rfl) ⟨4411952, by rfl⟩ : syracuseStep 5882603 = 8823905) B8823905
theorem B11477771 : Blo 1449544 11477771 := bstep (se 1 (by rfl) ⟨8608328, by rfl⟩ : syracuseStep 11477771 = 17216657) B17216657
theorem B2753327 : Blo 1449544 2753327 := bstep (se 1 (by rfl) ⟨2064995, by rfl⟩ : syracuseStep 2753327 = 4129991) B4129991
theorem B1450863 : Blo 1449544 1450863 := bstep (se 1 (by rfl) ⟨1088147, by rfl⟩ : syracuseStep 1450863 = 2176295) B2176295
theorem B6194063 : Blo 1449544 6194063 := bstep (se 1 (by rfl) ⟨4645547, by rfl⟩ : syracuseStep 6194063 = 9291095) B9291095
theorem B1450919 : Blo 1449544 1450919 := bstep (se 1 (by rfl) ⟨1088189, by rfl⟩ : syracuseStep 1450919 = 2176379) B2176379
theorem B1631227 : Blo 1449544 1631227 := bstep (se 1 (by rfl) ⟨1223420, by rfl⟩ : syracuseStep 1631227 = 2446841) B2446841
theorem B1451003 : Blo 1449544 1451003 := bstep (se 1 (by rfl) ⟨1088252, by rfl⟩ : syracuseStep 1451003 = 2176505) B2176505
theorem B1451071 : Blo 1449544 1451071 := bstep (se 1 (by rfl) ⟨1088303, by rfl⟩ : syracuseStep 1451071 = 2176607) B2176607
theorem B3261545 : Blo 1449544 3261545 := bstep (se 2 (by rfl) ⟨1223079, by rfl⟩ : syracuseStep 3261545 = 2446159) B2446159
theorem B5227625 : Blo 1449544 5227625 := bstep (se 2 (by rfl) ⟨1960359, by rfl⟩ : syracuseStep 5227625 = 3920719) B3920719
theorem B8258705 : Blo 1449544 8258705 := bstep (se 2 (by rfl) ⟨3097014, by rfl⟩ : syracuseStep 8258705 = 6194029) B6194029
theorem B1631407 : Blo 1449544 1631407 := bstep (se 1 (by rfl) ⟨1223555, by rfl⟩ : syracuseStep 1631407 = 2447111) B2447111
theorem B1451215 : Blo 1449544 1451215 := bstep (se 1 (by rfl) ⟨1088411, by rfl⟩ : syracuseStep 1451215 = 2176823) B2176823
theorem B22324547 : Blo 1449544 22324547 := bstep (se 1 (by rfl) ⟨16743410, by rfl⟩ : syracuseStep 22324547 = 33486821) B33486821
theorem B2205083 : Blo 1449544 2205083 := bstep (se 1 (by rfl) ⟨1653812, by rfl⟩ : syracuseStep 2205083 = 3307625) B3307625
theorem B1451419 : Blo 1449544 1451419 := bstep (se 1 (by rfl) ⟨1088564, by rfl⟩ : syracuseStep 1451419 = 2177129) B2177129
theorem B4646521 : Blo 1449544 4646521 := bstep (se 2 (by rfl) ⟨1742445, by rfl⟩ : syracuseStep 4646521 = 3484891) B3484891
theorem B1631911 : Blo 1449544 1631911 := bstep (se 1 (by rfl) ⟨1223933, by rfl⟩ : syracuseStep 1631911 = 2447867) B2447867
theorem B3262175 : Blo 1449544 3262175 := bstep (se 1 (by rfl) ⟨2446631, by rfl⟩ : syracuseStep 3262175 = 4893263) B4893263
theorem B4646753 : Blo 1449544 4646753 := bstep (se 2 (by rfl) ⟨1742532, by rfl⟩ : syracuseStep 4646753 = 3485065) B3485065
theorem B12388261 : Blo 1449544 12388261 := bstep (se 4 (by rfl) ⟨1161399, by rfl⟩ : syracuseStep 12388261 = 2322799) B2322799
theorem B13420475 : Blo 1449544 13420475 := bstep (se 1 (by rfl) ⟨10065356, by rfl⟩ : syracuseStep 13420475 = 20130713) B20130713
theorem B4892615 : Blo 1449544 4892615 := bstep (se 1 (by rfl) ⟨3669461, by rfl⟩ : syracuseStep 4892615 = 7338923) B7338923
theorem B1632199 : Blo 1449544 1632199 := bstep (se 1 (by rfl) ⟨1224149, by rfl⟩ : syracuseStep 1632199 = 2448299) B2448299
theorem B477210775 : Blo 1449544 477210775 := bstep (se 1 (by rfl) ⟨357908081, by rfl⟩ : syracuseStep 477210775 = 715816163) B715816163
theorem B2205929 : Blo 1449544 2205929 := bstep (se 2 (by rfl) ⟨827223, by rfl⟩ : syracuseStep 2205929 = 1654447) B1654447
theorem B7440619 : Blo 1449544 7440619 := bstep (se 1 (by rfl) ⟨5580464, by rfl⟩ : syracuseStep 7440619 = 11160929) B11160929
theorem B1632559 : Blo 1449544 1632559 := bstep (se 1 (by rfl) ⟨1224419, by rfl⟩ : syracuseStep 1632559 = 2448839) B2448839
theorem B4131233 : Blo 1449544 4131233 := bstep (se 2 (by rfl) ⟨1549212, by rfl⟩ : syracuseStep 4131233 = 3098425) B3098425
theorem B141240833 : Blo 1449544 141240833 := bstep (se 2 (by rfl) ⟨52965312, by rfl⟩ : syracuseStep 141240833 = 105930625) B105930625
theorem B3263003 : Blo 1449544 3263003 := bstep (se 1 (by rfl) ⟨2447252, by rfl⟩ : syracuseStep 3263003 = 4894505) B4894505
theorem B9292427 : Blo 1449544 9292427 := bstep (se 1 (by rfl) ⟨6969320, by rfl⟩ : syracuseStep 9292427 = 13938641) B13938641
theorem B4893371 : Blo 1449544 4893371 := bstep (se 1 (by rfl) ⟨3670028, by rfl⟩ : syracuseStep 4893371 = 7340057) B7340057
theorem B20917187 : Blo 1449544 20917187 := bstep (se 1 (by rfl) ⟨15687890, by rfl⟩ : syracuseStep 20917187 = 31375781) B31375781
theorem B4132063 : Blo 1449544 4132063 := bstep (se 1 (by rfl) ⟨3099047, by rfl⟩ : syracuseStep 4132063 = 6198095) B6198095
theorem B5229791 : Blo 1449544 5229791 := bstep (se 1 (by rfl) ⟨3922343, by rfl⟩ : syracuseStep 5229791 = 7844687) B7844687
theorem B5508431 : Blo 1449544 5508431 := bstep (se 1 (by rfl) ⟨4131323, by rfl⟩ : syracuseStep 5508431 = 8262647) B8262647
theorem B2174375 : Blo 1449544 2174375 := bstep (se 1 (by rfl) ⟨1630781, by rfl⟩ : syracuseStep 2174375 = 3261563) B3261563
theorem B2174459 : Blo 1449544 2174459 := bstep (se 1 (by rfl) ⟨1630844, by rfl⟩ : syracuseStep 2174459 = 3261689) B3261689
theorem B3141193 : Blo 1449544 3141193 := bstep (se 2 (by rfl) ⟨1177947, by rfl⟩ : syracuseStep 3141193 = 2355895) B2355895
theorem B2174555 : Blo 1449544 2174555 := bstep (se 1 (by rfl) ⟨1630916, by rfl⟩ : syracuseStep 2174555 = 3261833) B3261833
theorem B2174639 : Blo 1449544 2174639 := bstep (se 1 (by rfl) ⟨1630979, by rfl⟩ : syracuseStep 2174639 = 3261959) B3261959
theorem B3673775 : Blo 1449544 3673775 := bstep (se 1 (by rfl) ⟨2755331, by rfl⟩ : syracuseStep 3673775 = 5510663) B5510663
theorem B2174759 : Blo 1449544 2174759 := bstep (se 1 (by rfl) ⟨1631069, by rfl⟩ : syracuseStep 2174759 = 3262139) B3262139
theorem B2174843 : Blo 1449544 2174843 := bstep (se 1 (by rfl) ⟨1631132, by rfl⟩ : syracuseStep 2174843 = 3262265) B3262265
theorem B3264479 : Blo 1449544 3264479 := bstep (se 1 (by rfl) ⟨2448359, by rfl⟩ : syracuseStep 3264479 = 4896719) B4896719
theorem B3674099 : Blo 1449544 3674099 := bstep (se 1 (by rfl) ⟨2755574, by rfl⟩ : syracuseStep 3674099 = 5511149) B5511149
theorem B4771963 : Blo 1449544 4771963 := bstep (se 1 (by rfl) ⟨3578972, by rfl⟩ : syracuseStep 4771963 = 7157945) B7157945
theorem B4649213 : Blo 1449544 4649213 := bstep (se 3 (by rfl) ⟨871727, by rfl⟩ : syracuseStep 4649213 = 1743455) B1743455
theorem B2175263 : Blo 1449544 2175263 := bstep (se 1 (by rfl) ⟨1631447, by rfl⟩ : syracuseStep 2175263 = 3262895) B3262895
theorem B2175287 : Blo 1449544 2175287 := bstep (se 1 (by rfl) ⟨1631465, by rfl⟩ : syracuseStep 2175287 = 3262931) B3262931
theorem B14889271 : Blo 1449544 14889271 := bstep (se 1 (by rfl) ⟨11166953, by rfl⟩ : syracuseStep 14889271 = 22333907) B22333907
theorem B2175359 : Blo 1449544 2175359 := bstep (se 1 (by rfl) ⟨1631519, by rfl⟩ : syracuseStep 2175359 = 3263039) B3263039
theorem B2175431 : Blo 1449544 2175431 := bstep (se 1 (by rfl) ⟨1631573, by rfl⟩ : syracuseStep 2175431 = 3263147) B3263147
theorem B4895315 : Blo 1449544 4895315 := bstep (se 1 (by rfl) ⟨3671486, by rfl⟩ : syracuseStep 4895315 = 7342973) B7342973
theorem B3265127 : Blo 1449544 3265127 := bstep (se 1 (by rfl) ⟨2448845, by rfl⟩ : syracuseStep 3265127 = 4897691) B4897691
theorem B7344755 : Blo 1449544 7344755 := bstep (se 1 (by rfl) ⟨5508566, by rfl⟩ : syracuseStep 7344755 = 11017133) B11017133
theorem B20910727 : Blo 1449544 20910727 := bstep (se 1 (by rfl) ⟨15683045, by rfl⟩ : syracuseStep 20910727 = 31366091) B31366091
theorem B52900523 : Blo 1449544 52900523 := bstep (se 1 (by rfl) ⟨39675392, by rfl⟩ : syracuseStep 52900523 = 79350785) B79350785
theorem B2175785 : Blo 1449544 2175785 := bstep (se 2 (by rfl) ⟨815919, by rfl⟩ : syracuseStep 2175785 = 1631839) B1631839
theorem B2175791 : Blo 1449544 2175791 := bstep (se 1 (by rfl) ⟨1631843, by rfl⟩ : syracuseStep 2175791 = 3263687) B3263687
theorem B9294659 : Blo 1449544 9294659 := bstep (se 1 (by rfl) ⟨6970994, by rfl⟩ : syracuseStep 9294659 = 13941989) B13941989
theorem B14881681 : Blo 1449544 14881681 := bstep (se 2 (by rfl) ⟨5580630, by rfl⟩ : syracuseStep 14881681 = 11161261) B11161261
theorem B2446247 : Blo 1449544 2446247 := bstep (se 1 (by rfl) ⟨1834685, by rfl⟩ : syracuseStep 2446247 = 3669371) B3669371
theorem B2175911 : Blo 1449544 2175911 := bstep (se 1 (by rfl) ⟨1631933, by rfl⟩ : syracuseStep 2175911 = 3263867) B3263867
theorem B1766395 : Blo 1449544 1766395 := bstep (se 1 (by rfl) ⟨1324796, by rfl⟩ : syracuseStep 1766395 = 2649593) B2649593
theorem B2175995 : Blo 1449544 2175995 := bstep (se 1 (by rfl) ⟨1631996, by rfl⟩ : syracuseStep 2175995 = 3263993) B3263993
theorem B9294887 : Blo 1449544 9294887 := bstep (se 1 (by rfl) ⟨6971165, by rfl⟩ : syracuseStep 9294887 = 13942331) B13942331
theorem B2176055 : Blo 1449544 2176055 := bstep (se 1 (by rfl) ⟨1632041, by rfl⟩ : syracuseStep 2176055 = 3264083) B3264083
theorem B5510207 : Blo 1449544 5510207 := bstep (se 1 (by rfl) ⟨4132655, by rfl⟩ : syracuseStep 5510207 = 8265311) B8265311
theorem B2446409 : Blo 1449544 2446409 := bstep (se 2 (by rfl) ⟨917403, by rfl⟩ : syracuseStep 2446409 = 1834807) B1834807
theorem B6198353 : Blo 1449544 6198353 := bstep (se 2 (by rfl) ⟨2324382, by rfl⟩ : syracuseStep 6198353 = 4648765) B4648765
theorem B2176175 : Blo 1449544 2176175 := bstep (se 1 (by rfl) ⟨1632131, by rfl⟩ : syracuseStep 2176175 = 3264263) B3264263
theorem B4895963 : Blo 1449544 4895963 := bstep (se 1 (by rfl) ⟨3671972, by rfl⟩ : syracuseStep 4895963 = 7343945) B7343945
theorem B3265811 : Blo 1449544 3265811 := bstep (se 1 (by rfl) ⟨2449358, by rfl⟩ : syracuseStep 3265811 = 4898717) B4898717
theorem B9295195 : Blo 1449544 9295195 := bstep (se 1 (by rfl) ⟨6971396, by rfl⟩ : syracuseStep 9295195 = 13942793) B13942793
theorem B3265883 : Blo 1449544 3265883 := bstep (se 1 (by rfl) ⟨2449412, by rfl⟩ : syracuseStep 3265883 = 4898825) B4898825
theorem B2176583 : Blo 1449544 2176583 := bstep (se 1 (by rfl) ⟨1632437, by rfl⟩ : syracuseStep 2176583 = 3264875) B3264875
theorem B2446969 : Blo 1449544 2446969 := bstep (se 2 (by rfl) ⟨917613, by rfl⟩ : syracuseStep 2446969 = 1835227) B1835227
theorem B2176679 : Blo 1449544 2176679 := bstep (se 1 (by rfl) ⟨1632509, by rfl⟩ : syracuseStep 2176679 = 3265019) B3265019
theorem B16742123 : Blo 1449544 16742123 := bstep (se 1 (by rfl) ⟨12556592, by rfl⟩ : syracuseStep 16742123 = 25113185) B25113185
theorem B2176763 : Blo 1449544 2176763 := bstep (se 1 (by rfl) ⟨1632572, by rfl⟩ : syracuseStep 2176763 = 3265145) B3265145
theorem B2176799 : Blo 1449544 2176799 := bstep (se 1 (by rfl) ⟨1632599, by rfl⟩ : syracuseStep 2176799 = 3265199) B3265199
theorem B2176847 : Blo 1449544 2176847 := bstep (se 1 (by rfl) ⟨1632635, by rfl⟩ : syracuseStep 2176847 = 3265271) B3265271
theorem B15685559 : Blo 1449544 15685559 := bstep (se 1 (by rfl) ⟨11764169, by rfl⟩ : syracuseStep 15685559 = 23528339) B23528339
theorem B2176967 : Blo 1449544 2176967 := bstep (se 1 (by rfl) ⟨1632725, by rfl⟩ : syracuseStep 2176967 = 3265451) B3265451
theorem B7837721 : Blo 1449544 7837721 := bstep (se 2 (by rfl) ⟨2939145, by rfl⟩ : syracuseStep 7837721 = 5878291) B5878291
theorem B4896827 : Blo 1449544 4896827 := bstep (se 1 (by rfl) ⟨3672620, by rfl⟩ : syracuseStep 4896827 = 7345241) B7345241
theorem B2447455 : Blo 1449544 2447455 := bstep (se 1 (by rfl) ⟨1835591, by rfl⟩ : syracuseStep 2447455 = 3671183) B3671183
theorem B7346375 : Blo 1449544 7346375 := bstep (se 1 (by rfl) ⟨5509781, by rfl⟩ : syracuseStep 7346375 = 11019563) B11019563
theorem B4897097 : Blo 1449544 4897097 := bstep (se 2 (by rfl) ⟨1836411, by rfl⟩ : syracuseStep 4897097 = 3672823) B3672823
theorem B20912573 : Blo 1449544 20912573 := bstep (se 3 (by rfl) ⟨3921107, by rfl⟩ : syracuseStep 20912573 = 7842215) B7842215
theorem B4413971 : Blo 1449544 4413971 := bstep (se 1 (by rfl) ⟨3310478, by rfl⟩ : syracuseStep 4413971 = 6620957) B6620957
theorem B18586493 : Blo 1449544 18586493 := bstep (se 3 (by rfl) ⟨3484967, by rfl⟩ : syracuseStep 18586493 = 6969935) B6969935
theorem B55098299 : Blo 1449544 55098299 := bstep (se 1 (by rfl) ⟨41323724, by rfl⟩ : syracuseStep 55098299 = 82647449) B82647449
theorem B24796205 : Blo 1449544 24796205 := bstep (se 3 (by rfl) ⟨4649288, by rfl⟩ : syracuseStep 24796205 = 9298577) B9298577
theorem B5504071 : Blo 1449544 5504071 := bstep (se 1 (by rfl) ⟨4128053, by rfl⟩ : syracuseStep 5504071 = 8256107) B8256107
theorem B7347347 : Blo 1449544 7347347 := bstep (se 1 (by rfl) ⟨5510510, by rfl⟩ : syracuseStep 7347347 = 11021021) B11021021
theorem B2448751 : Blo 1449544 2448751 := bstep (se 1 (by rfl) ⟨1836563, by rfl⟩ : syracuseStep 2448751 = 3673127) B3673127
theorem B18578807 : Blo 1449544 18578807 := bstep (se 1 (by rfl) ⟨13934105, by rfl⟩ : syracuseStep 18578807 = 27868211) B27868211
theorem B2940371 : Blo 1449544 2940371 := bstep (se 1 (by rfl) ⟨2205278, by rfl⟩ : syracuseStep 2940371 = 4410557) B4410557
theorem B47037995 : Blo 1449544 47037995 := bstep (se 1 (by rfl) ⟨35278496, by rfl⟩ : syracuseStep 47037995 = 70556993) B70556993
theorem B3669583 : Blo 1449544 3669583 := bstep (se 1 (by rfl) ⟨2752187, by rfl⟩ : syracuseStep 3669583 = 5504375) B5504375
theorem B7446095 : Blo 1449544 7446095 := bstep (se 1 (by rfl) ⟨5584571, by rfl⟩ : syracuseStep 7446095 = 11169143) B11169143
theorem B1449563 : Blo 1449544 1449563 := bstep (se 1 (by rfl) ⟨1087172, by rfl⟩ : syracuseStep 1449563 = 2174345) B2174345
theorem B4300379 : Blo 1449544 4300379 := bstep (se 1 (by rfl) ⟨3225284, by rfl⟩ : syracuseStep 4300379 = 6450569) B6450569
theorem B4898447 : Blo 1449544 4898447 := bstep (se 1 (by rfl) ⟨3673835, by rfl⟩ : syracuseStep 4898447 = 7347671) B7347671
theorem B2449129 : Blo 1449544 2449129 := bstep (se 2 (by rfl) ⟨918423, by rfl⟩ : syracuseStep 2449129 = 1836847) B1836847
theorem B1449799 : Blo 1449544 1449799 := bstep (se 1 (by rfl) ⟨1087349, by rfl⟩ : syracuseStep 1449799 = 2174699) B2174699
theorem B3096443 : Blo 1449544 3096443 := bstep (se 1 (by rfl) ⟨2322332, by rfl⟩ : syracuseStep 3096443 = 4644665) B4644665
theorem B7348157 : Blo 1449544 7348157 := bstep (se 3 (by rfl) ⟨1377779, by rfl⟩ : syracuseStep 7348157 = 2755559) B2755559
theorem B1449951 : Blo 1449544 1449951 := bstep (se 1 (by rfl) ⟨1087463, by rfl⟩ : syracuseStep 1449951 = 2174927) B2174927
theorem B7340219 : Blo 1449544 7340219 := bstep (se 1 (by rfl) ⟨5505164, by rfl⟩ : syracuseStep 7340219 = 11010329) B11010329
theorem B1450175 : Blo 1449544 1450175 := bstep (se 1 (by rfl) ⟨1087631, by rfl⟩ : syracuseStep 1450175 = 2175263) B2175263
theorem B636281033 : Blo 1449544 636281033 := bstep (se 2 (by rfl) ⟨238605387, by rfl⟩ : syracuseStep 636281033 = 477210775) B477210775
theorem B1450191 : Blo 1449544 1450191 := bstep (se 1 (by rfl) ⟨1087643, by rfl⟩ : syracuseStep 1450191 = 2175287) B2175287
theorem B2064619 : Blo 1449544 2064619 := bstep (se 1 (by rfl) ⟨1548464, by rfl⟩ : syracuseStep 2064619 = 3096929) B3096929
theorem B1450239 : Blo 1449544 1450239 := bstep (se 1 (by rfl) ⟨1087679, by rfl⟩ : syracuseStep 1450239 = 2175359) B2175359
theorem B1450287 : Blo 1449544 1450287 := bstep (se 1 (by rfl) ⟨1087715, by rfl⟩ : syracuseStep 1450287 = 2175431) B2175431
theorem B9920825 : Blo 1449544 9920825 := bstep (se 2 (by rfl) ⟨3720309, by rfl⟩ : syracuseStep 9920825 = 7440619) B7440619
theorem B35267015 : Blo 1449544 35267015 := bstep (se 1 (by rfl) ⟨26450261, by rfl⟩ : syracuseStep 35267015 = 52900523) B52900523
theorem B7651847 : Blo 1449544 7651847 := bstep (se 1 (by rfl) ⟨5738885, by rfl⟩ : syracuseStep 7651847 = 11477771) B11477771
theorem B1450523 : Blo 1449544 1450523 := bstep (se 1 (by rfl) ⟨1087892, by rfl⟩ : syracuseStep 1450523 = 2175785) B2175785
theorem B1835551 : Blo 1449544 1835551 := bstep (se 1 (by rfl) ⟨1376663, by rfl⟩ : syracuseStep 1835551 = 2753327) B2753327
theorem B1450527 : Blo 1449544 1450527 := bstep (se 1 (by rfl) ⟨1087895, by rfl⟩ : syracuseStep 1450527 = 2175791) B2175791
theorem B4129375 : Blo 1449544 4129375 := bstep (se 1 (by rfl) ⟨3097031, by rfl⟩ : syracuseStep 4129375 = 6194063) B6194063
theorem B2753129 : Blo 1449544 2753129 := bstep (se 2 (by rfl) ⟨1032423, by rfl⟩ : syracuseStep 2753129 = 2064847) B2064847
theorem B1630831 : Blo 1449544 1630831 := bstep (se 1 (by rfl) ⟨1223123, by rfl⟩ : syracuseStep 1630831 = 2446247) B2446247
theorem B1450607 : Blo 1449544 1450607 := bstep (se 1 (by rfl) ⟨1087955, by rfl⟩ : syracuseStep 1450607 = 2175911) B2175911
theorem B1450663 : Blo 1449544 1450663 := bstep (se 1 (by rfl) ⟨1087997, by rfl⟩ : syracuseStep 1450663 = 2175995) B2175995
theorem B1450703 : Blo 1449544 1450703 := bstep (se 1 (by rfl) ⟨1088027, by rfl⟩ : syracuseStep 1450703 = 2176055) B2176055
theorem B1630939 : Blo 1449544 1630939 := bstep (se 1 (by rfl) ⟨1223204, by rfl⟩ : syracuseStep 1630939 = 2446409) B2446409
theorem B5505803 : Blo 1449544 5505803 := bstep (se 1 (by rfl) ⟨4129352, by rfl⟩ : syracuseStep 5505803 = 8258705) B8258705
theorem B1450783 : Blo 1449544 1450783 := bstep (se 1 (by rfl) ⟨1088087, by rfl⟩ : syracuseStep 1450783 = 2176175) B2176175
theorem B1451055 : Blo 1449544 1451055 := bstep (se 1 (by rfl) ⟨1088291, by rfl⟩ : syracuseStep 1451055 = 2176583) B2176583
theorem B1451119 : Blo 1449544 1451119 := bstep (se 1 (by rfl) ⟨1088339, by rfl⟩ : syracuseStep 1451119 = 2176679) B2176679
theorem B1451175 : Blo 1449544 1451175 := bstep (se 1 (by rfl) ⟨1088381, by rfl⟩ : syracuseStep 1451175 = 2176763) B2176763
theorem B1451199 : Blo 1449544 1451199 := bstep (se 1 (by rfl) ⟨1088399, by rfl⟩ : syracuseStep 1451199 = 2176799) B2176799
theorem B19842241 : Blo 1449544 19842241 := bstep (se 2 (by rfl) ⟨7440840, by rfl⟩ : syracuseStep 19842241 = 14881681) B14881681
theorem B1451231 : Blo 1449544 1451231 := bstep (se 1 (by rfl) ⟨1088423, by rfl⟩ : syracuseStep 1451231 = 2176847) B2176847
theorem B3097835 : Blo 1449544 3097835 := bstep (se 1 (by rfl) ⟨2323376, by rfl⟩ : syracuseStep 3097835 = 4646753) B4646753
theorem B8946983 : Blo 1449544 8946983 := bstep (se 1 (by rfl) ⟨6710237, by rfl⟩ : syracuseStep 8946983 = 13420475) B13420475
theorem B3261743 : Blo 1449544 3261743 := bstep (se 1 (by rfl) ⟨2446307, by rfl⟩ : syracuseStep 3261743 = 4892615) B4892615
theorem B1451311 : Blo 1449544 1451311 := bstep (se 1 (by rfl) ⟨1088483, by rfl⟩ : syracuseStep 1451311 = 2176967) B2176967
theorem B2754155 : Blo 1449544 2754155 := bstep (se 1 (by rfl) ⟨2065616, by rfl⟩ : syracuseStep 2754155 = 4131233) B4131233
theorem B94160555 : Blo 1449544 94160555 := bstep (se 1 (by rfl) ⟨70620416, by rfl⟩ : syracuseStep 94160555 = 141240833) B141240833
theorem B6194951 : Blo 1449544 6194951 := bstep (se 1 (by rfl) ⟨4646213, by rfl⟩ : syracuseStep 6194951 = 9292427) B9292427
theorem B3262247 : Blo 1449544 3262247 := bstep (se 1 (by rfl) ⟨2446685, by rfl⟩ : syracuseStep 3262247 = 4893371) B4893371
theorem B13944791 : Blo 1449544 13944791 := bstep (se 1 (by rfl) ⟨10458593, by rfl⟩ : syracuseStep 13944791 = 20917187) B20917187
theorem B4188257 : Blo 1449544 4188257 := bstep (se 2 (by rfl) ⟨1570596, by rfl⟩ : syracuseStep 4188257 = 3141193) B3141193
theorem B4892777 : Blo 1449544 4892777 := bstep (se 2 (by rfl) ⟨1834791, by rfl⟩ : syracuseStep 4892777 = 3669583) B3669583
theorem B3262625 : Blo 1449544 3262625 := bstep (se 2 (by rfl) ⟨1223484, by rfl⟩ : syracuseStep 3262625 = 2446969) B2446969
theorem B6195361 : Blo 1449544 6195361 := bstep (se 2 (by rfl) ⟨2323260, by rfl⟩ : syracuseStep 6195361 = 4646521) B4646521
theorem B3672287 : Blo 1449544 3672287 := bstep (se 1 (by rfl) ⟨2754215, by rfl⟩ : syracuseStep 3672287 = 5508431) B5508431
theorem B1960247 : Blo 1449544 1960247 := bstep (se 1 (by rfl) ⟨1470185, by rfl⟩ : syracuseStep 1960247 = 2940371) B2940371
theorem B16517681 : Blo 1449544 16517681 := bstep (se 2 (by rfl) ⟨6194130, by rfl⟩ : syracuseStep 16517681 = 12388261) B12388261
theorem B27863747 : Blo 1449544 27863747 := bstep (se 1 (by rfl) ⟨20897810, by rfl⟩ : syracuseStep 27863747 = 41795621) B41795621
theorem B2449399 : Blo 1449544 2449399 := bstep (se 1 (by rfl) ⟨1837049, by rfl⟩ : syracuseStep 2449399 = 3674099) B3674099
theorem B3263273 : Blo 1449544 3263273 := bstep (se 2 (by rfl) ⟨1223727, by rfl⟩ : syracuseStep 3263273 = 2447455) B2447455
theorem B3099475 : Blo 1449544 3099475 := bstep (se 1 (by rfl) ⟨2324606, by rfl⟩ : syracuseStep 3099475 = 4649213) B4649213
theorem B107342779 : Blo 1449544 107342779 := bstep (se 1 (by rfl) ⟨80507084, by rfl⟩ : syracuseStep 107342779 = 161014169) B161014169
theorem B3263543 : Blo 1449544 3263543 := bstep (se 1 (by rfl) ⟨2447657, by rfl⟩ : syracuseStep 3263543 = 4895315) B4895315
theorem B19852361 : Blo 1449544 19852361 := bstep (se 2 (by rfl) ⟨7444635, by rfl⟩ : syracuseStep 19852361 = 14889271) B14889271
theorem B6196439 : Blo 1449544 6196439 := bstep (se 1 (by rfl) ⟨4647329, by rfl⟩ : syracuseStep 6196439 = 9294659) B9294659
theorem B6196591 : Blo 1449544 6196591 := bstep (se 1 (by rfl) ⟨4647443, by rfl⟩ : syracuseStep 6196591 = 9294887) B9294887
theorem B3673471 : Blo 1449544 3673471 := bstep (se 1 (by rfl) ⟨2755103, by rfl⟩ : syracuseStep 3673471 = 5510207) B5510207
theorem B4132235 : Blo 1449544 4132235 := bstep (se 1 (by rfl) ⟨3099176, by rfl⟩ : syracuseStep 4132235 = 6198353) B6198353
theorem B2174363 : Blo 1449544 2174363 := bstep (se 1 (by rfl) ⟨1630772, by rfl⟩ : syracuseStep 2174363 = 3261545) B3261545
theorem B3263975 : Blo 1449544 3263975 := bstep (se 1 (by rfl) ⟨2447981, by rfl⟩ : syracuseStep 3263975 = 4895963) B4895963
theorem B27880969 : Blo 1449544 27880969 := bstep (se 2 (by rfl) ⟨10455363, by rfl⟩ : syracuseStep 27880969 = 20910727) B20910727
theorem B2174783 : Blo 1449544 2174783 := bstep (se 1 (by rfl) ⟨1631087, by rfl⟩ : syracuseStep 2174783 = 3262175) B3262175
theorem B11161415 : Blo 1449544 11161415 := bstep (se 1 (by rfl) ⟨8371061, by rfl⟩ : syracuseStep 11161415 = 16742123) B16742123
theorem B10457039 : Blo 1449544 10457039 := bstep (se 1 (by rfl) ⟨7842779, by rfl⟩ : syracuseStep 10457039 = 15685559) B15685559
theorem B2174969 : Blo 1449544 2174969 := bstep (se 2 (by rfl) ⟨815613, by rfl⟩ : syracuseStep 2174969 = 1631227) B1631227
theorem B2355193 : Blo 1449544 2355193 := bstep (se 2 (by rfl) ⟨883197, by rfl⟩ : syracuseStep 2355193 = 1766395) B1766395
theorem B3264551 : Blo 1449544 3264551 := bstep (se 1 (by rfl) ⟨2448413, by rfl⟩ : syracuseStep 3264551 = 4896827) B4896827
theorem B1470619 : Blo 1449544 1470619 := bstep (se 1 (by rfl) ⟨1102964, by rfl⟩ : syracuseStep 1470619 = 2205929) B2205929
theorem B3264731 : Blo 1449544 3264731 := bstep (se 1 (by rfl) ⟨2448548, by rfl⟩ : syracuseStep 3264731 = 4897097) B4897097
theorem B2175209 : Blo 1449544 2175209 := bstep (se 2 (by rfl) ⟨815703, by rfl⟩ : syracuseStep 2175209 = 1631407) B1631407
theorem B5509417 : Blo 1449544 5509417 := bstep (se 2 (by rfl) ⟨2066031, by rfl⟩ : syracuseStep 5509417 = 4132063) B4132063
theorem B2175335 : Blo 1449544 2175335 := bstep (se 1 (by rfl) ⟨1631501, by rfl⟩ : syracuseStep 2175335 = 3263003) B3263003
theorem B3265001 : Blo 1449544 3265001 := bstep (se 2 (by rfl) ⟨1224375, by rfl⟩ : syracuseStep 3265001 = 2448751) B2448751
theorem B12390995 : Blo 1449544 12390995 := bstep (se 1 (by rfl) ⟨9293246, by rfl⟩ : syracuseStep 12390995 = 18586493) B18586493
theorem B3486527 : Blo 1449544 3486527 := bstep (se 1 (by rfl) ⟨2614895, by rfl⟩ : syracuseStep 3486527 = 5229791) B5229791
theorem B2175881 : Blo 1449544 2175881 := bstep (se 2 (by rfl) ⟨815955, by rfl⟩ : syracuseStep 2175881 = 1631911) B1631911
theorem B3265505 : Blo 1449544 3265505 := bstep (se 2 (by rfl) ⟨1224564, by rfl⟩ : syracuseStep 3265505 = 2449129) B2449129
theorem B3265631 : Blo 1449544 3265631 := bstep (se 1 (by rfl) ⟨2449223, by rfl⟩ : syracuseStep 3265631 = 4898447) B4898447
theorem B2176265 : Blo 1449544 2176265 := bstep (se 2 (by rfl) ⟨816099, by rfl⟩ : syracuseStep 2176265 = 1632199) B1632199
theorem B2176319 : Blo 1449544 2176319 := bstep (se 1 (by rfl) ⟨1632239, by rfl⟩ : syracuseStep 2176319 = 3264479) B3264479
theorem B13940333 : Blo 1449544 13940333 := bstep (se 3 (by rfl) ⟨2613812, by rfl⟩ : syracuseStep 13940333 = 5227625) B5227625
theorem B2447003 : Blo 1449544 2447003 := bstep (se 1 (by rfl) ⟨1835252, by rfl⟩ : syracuseStep 2447003 = 3670505) B3670505
theorem B5510875 : Blo 1449544 5510875 := bstep (se 1 (by rfl) ⟨4133156, by rfl⟩ : syracuseStep 5510875 = 8266313) B8266313
theorem B2176745 : Blo 1449544 2176745 := bstep (se 2 (by rfl) ⟨816279, by rfl⟩ : syracuseStep 2176745 = 1632559) B1632559
theorem B2176751 : Blo 1449544 2176751 := bstep (se 1 (by rfl) ⟨1632563, by rfl⟩ : syracuseStep 2176751 = 3265127) B3265127
theorem B4896503 : Blo 1449544 4896503 := bstep (se 1 (by rfl) ⟨3672377, by rfl⟩ : syracuseStep 4896503 = 7344755) B7344755
theorem B25450469 : Blo 1449544 25450469 := bstep (se 4 (by rfl) ⟨2385981, by rfl⟩ : syracuseStep 25450469 = 4771963) B4771963
theorem B2177207 : Blo 1449544 2177207 := bstep (se 1 (by rfl) ⟨1632905, by rfl⟩ : syracuseStep 2177207 = 3265811) B3265811
theorem B14883031 : Blo 1449544 14883031 := bstep (se 1 (by rfl) ⟨11162273, by rfl⟩ : syracuseStep 14883031 = 22324547) B22324547
theorem B2177255 : Blo 1449544 2177255 := bstep (se 1 (by rfl) ⟨1632941, by rfl⟩ : syracuseStep 2177255 = 3265883) B3265883
theorem B5880221 : Blo 1449544 5880221 := bstep (se 3 (by rfl) ⟨1102541, by rfl⟩ : syracuseStep 5880221 = 2205083) B2205083
theorem B15292901 : Blo 1449544 15292901 := bstep (se 4 (by rfl) ⟨1433709, by rfl⟩ : syracuseStep 15292901 = 2867419) B2867419
theorem B5225147 : Blo 1449544 5225147 := bstep (se 1 (by rfl) ⟨3918860, by rfl⟩ : syracuseStep 5225147 = 7837721) B7837721
theorem B11770589 : Blo 1449544 11770589 := bstep (se 3 (by rfl) ⟨2206985, by rfl⟩ : syracuseStep 11770589 = 4413971) B4413971
theorem B7338761 : Blo 1449544 7338761 := bstep (se 2 (by rfl) ⟨2752035, by rfl⟩ : syracuseStep 7338761 = 5504071) B5504071
theorem B4897583 : Blo 1449544 4897583 := bstep (se 1 (by rfl) ⟨3673187, by rfl⟩ : syracuseStep 4897583 = 7346375) B7346375
theorem B13941715 : Blo 1449544 13941715 := bstep (se 1 (by rfl) ⟨10456286, by rfl⟩ : syracuseStep 13941715 = 20912573) B20912573
theorem B12393593 : Blo 1449544 12393593 := bstep (se 2 (by rfl) ⟨4647597, by rfl⟩ : syracuseStep 12393593 = 9295195) B9295195
theorem B15686941 : Blo 1449544 15686941 := bstep (se 3 (by rfl) ⟨2941301, by rfl⟩ : syracuseStep 15686941 = 5882603) B5882603
theorem B36732199 : Blo 1449544 36732199 := bstep (se 1 (by rfl) ⟨27549149, by rfl⟩ : syracuseStep 36732199 = 55098299) B55098299
theorem B16530803 : Blo 1449544 16530803 := bstep (se 1 (by rfl) ⟨12398102, by rfl⟩ : syracuseStep 16530803 = 24796205) B24796205
theorem B4898231 : Blo 1449544 4898231 := bstep (se 1 (by rfl) ⟨3673673, by rfl⟩ : syracuseStep 4898231 = 7347347) B7347347
theorem B12385871 : Blo 1449544 12385871 := bstep (se 1 (by rfl) ⟨9289403, by rfl⟩ : syracuseStep 12385871 = 18578807) B18578807
theorem B1449583 : Blo 1449544 1449583 := bstep (se 1 (by rfl) ⟨1087187, by rfl⟩ : syracuseStep 1449583 = 2174375) B2174375
theorem B1449639 : Blo 1449544 1449639 := bstep (se 1 (by rfl) ⟨1087229, by rfl⟩ : syracuseStep 1449639 = 2174459) B2174459
theorem B31358663 : Blo 1449544 31358663 := bstep (se 1 (by rfl) ⟨23518997, by rfl⟩ : syracuseStep 31358663 = 47037995) B47037995
theorem B4964063 : Blo 1449544 4964063 := bstep (se 1 (by rfl) ⟨3723047, by rfl⟩ : syracuseStep 4964063 = 7446095) B7446095
theorem B1449703 : Blo 1449544 1449703 := bstep (se 1 (by rfl) ⟨1087277, by rfl⟩ : syracuseStep 1449703 = 2174555) B2174555
theorem B2866919 : Blo 1449544 2866919 := bstep (se 1 (by rfl) ⟨2150189, by rfl⟩ : syracuseStep 2866919 = 4300379) B4300379
theorem B1449759 : Blo 1449544 1449759 := bstep (se 1 (by rfl) ⟨1087319, by rfl⟩ : syracuseStep 1449759 = 2174639) B2174639
theorem B2449183 : Blo 1449544 2449183 := bstep (se 1 (by rfl) ⟨1836887, by rfl⟩ : syracuseStep 2449183 = 3673775) B3673775
theorem B1449839 : Blo 1449544 1449839 := bstep (se 1 (by rfl) ⟨1087379, by rfl⟩ : syracuseStep 1449839 = 2174759) B2174759
theorem B2064295 : Blo 1449544 2064295 := bstep (se 1 (by rfl) ⟨1548221, by rfl⟩ : syracuseStep 2064295 = 3096443) B3096443
theorem B1449895 : Blo 1449544 1449895 := bstep (se 1 (by rfl) ⟨1087421, by rfl⟩ : syracuseStep 1449895 = 2174843) B2174843
theorem B4898771 : Blo 1449544 4898771 := bstep (se 1 (by rfl) ⟨3674078, by rfl⟩ : syracuseStep 4898771 = 7348157) B7348157
theorem B1450139 : Blo 1449544 1450139 := bstep (se 1 (by rfl) ⟨1087604, by rfl⟩ : syracuseStep 1450139 = 2175209) B2175209
theorem B1450223 : Blo 1449544 1450223 := bstep (se 1 (by rfl) ⟨1087667, by rfl⟩ : syracuseStep 1450223 = 2175335) B2175335
theorem B23511343 : Blo 1449544 23511343 := bstep (se 1 (by rfl) ⟨17633507, by rfl⟩ : syracuseStep 23511343 = 35267015) B35267015
theorem B3670535 : Blo 1449544 3670535 := bstep (se 1 (by rfl) ⟨2752901, by rfl⟩ : syracuseStep 3670535 = 5505803) B5505803
theorem B1450587 : Blo 1449544 1450587 := bstep (se 1 (by rfl) ⟨1087940, by rfl⟩ : syracuseStep 1450587 = 2175881) B2175881
theorem B5505833 : Blo 1449544 5505833 := bstep (se 2 (by rfl) ⟨2064687, by rfl⟩ : syracuseStep 5505833 = 4129375) B4129375
theorem B5227325 : Blo 1449544 5227325 := bstep (se 3 (by rfl) ⟨980123, by rfl⟩ : syracuseStep 5227325 = 1960247) B1960247
theorem B2065223 : Blo 1449544 2065223 := bstep (se 1 (by rfl) ⟨1548917, by rfl⟩ : syracuseStep 2065223 = 3097835) B3097835
theorem B1450843 : Blo 1449544 1450843 := bstep (se 1 (by rfl) ⟨1088132, by rfl⟩ : syracuseStep 1450843 = 2176265) B2176265
theorem B1450879 : Blo 1449544 1450879 := bstep (se 1 (by rfl) ⟨1088159, by rfl⟩ : syracuseStep 1450879 = 2176319) B2176319
theorem B1836103 : Blo 1449544 1836103 := bstep (se 1 (by rfl) ⟨1377077, by rfl⟩ : syracuseStep 1836103 = 2754155) B2754155
theorem B1631335 : Blo 1449544 1631335 := bstep (se 1 (by rfl) ⟨1223501, by rfl⟩ : syracuseStep 1631335 = 2447003) B2447003
theorem B1451163 : Blo 1449544 1451163 := bstep (se 1 (by rfl) ⟨1088372, by rfl⟩ : syracuseStep 1451163 = 2176745) B2176745
theorem B1451167 : Blo 1449544 1451167 := bstep (se 1 (by rfl) ⟨1088375, by rfl⟩ : syracuseStep 1451167 = 2176751) B2176751
theorem B4129967 : Blo 1449544 4129967 := bstep (se 1 (by rfl) ⟨3097475, by rfl⟩ : syracuseStep 4129967 = 6194951) B6194951
theorem B11011301 : Blo 1449544 11011301 := bstep (se 4 (by rfl) ⟨1032309, by rfl⟩ : syracuseStep 11011301 = 2064619) B2064619
theorem B143123705 : Blo 1449544 143123705 := bstep (se 2 (by rfl) ⟨53671389, by rfl⟩ : syracuseStep 143123705 = 107342779) B107342779
theorem B18588953 : Blo 1449544 18588953 := bstep (se 2 (by rfl) ⟨6970857, by rfl⟩ : syracuseStep 18588953 = 13941715) B13941715
theorem B16966979 : Blo 1449544 16966979 := bstep (se 1 (by rfl) ⟨12725234, by rfl⟩ : syracuseStep 16966979 = 25450469) B25450469
theorem B3261851 : Blo 1449544 3261851 := bstep (se 1 (by rfl) ⟨2446388, by rfl⟩ : syracuseStep 3261851 = 4892777) B4892777
theorem B1451471 : Blo 1449544 1451471 := bstep (se 1 (by rfl) ⟨1088603, by rfl⟩ : syracuseStep 1451471 = 2177207) B2177207
theorem B1451503 : Blo 1449544 1451503 := bstep (se 1 (by rfl) ⟨1088627, by rfl⟩ : syracuseStep 1451503 = 2177255) B2177255
theorem B7341677 : Blo 1449544 7341677 := bstep (se 3 (by rfl) ⟨1376564, by rfl⟩ : syracuseStep 7341677 = 2753129) B2753129
theorem B11011787 : Blo 1449544 11011787 := bstep (se 1 (by rfl) ⟨8258840, by rfl⟩ : syracuseStep 11011787 = 16517681) B16517681
theorem B20915921 : Blo 1449544 20915921 := bstep (se 2 (by rfl) ⟨7843470, by rfl⟩ : syracuseStep 20915921 = 15686941) B15686941
theorem B3483431 : Blo 1449544 3483431 := bstep (se 1 (by rfl) ⟨2612573, by rfl⟩ : syracuseStep 3483431 = 5225147) B5225147
theorem B4892507 : Blo 1449544 4892507 := bstep (se 1 (by rfl) ⟨3669380, by rfl⟩ : syracuseStep 4892507 = 7338761) B7338761
theorem B7645117 : Blo 1449544 7645117 := bstep (se 3 (by rfl) ⟨1433459, by rfl⟩ : syracuseStep 7645117 = 2866919) B2866919
theorem B4130959 : Blo 1449544 4130959 := bstep (se 1 (by rfl) ⟨3098219, by rfl⟩ : syracuseStep 4130959 = 6196439) B6196439
theorem B29763773 : Blo 1449544 29763773 := bstep (se 3 (by rfl) ⟨5580707, by rfl⟩ : syracuseStep 29763773 = 11161415) B11161415
theorem B11020535 : Blo 1449544 11020535 := bstep (se 1 (by rfl) ⟨8265401, by rfl⟩ : syracuseStep 11020535 = 16530803) B16530803
theorem B2754823 : Blo 1449544 2754823 := bstep (se 1 (by rfl) ⟨2066117, by rfl⟩ : syracuseStep 2754823 = 4132235) B4132235
theorem B3140257 : Blo 1449544 3140257 := bstep (se 2 (by rfl) ⟨1177596, by rfl⟩ : syracuseStep 3140257 = 2355193) B2355193
theorem B4893479 : Blo 1449544 4893479 := bstep (se 1 (by rfl) ⟨3670109, by rfl⟩ : syracuseStep 4893479 = 7340219) B7340219
theorem B6613883 : Blo 1449544 6613883 := bstep (se 1 (by rfl) ⟨4960412, by rfl⟩ : syracuseStep 6613883 = 9920825) B9920825
theorem B8260481 : Blo 1449544 8260481 := bstep (se 2 (by rfl) ⟨3097680, by rfl⟩ : syracuseStep 8260481 = 6195361) B6195361
theorem B19844041 : Blo 1449544 19844041 := bstep (se 2 (by rfl) ⟨7441515, by rfl⟩ : syracuseStep 19844041 = 14883031) B14883031
theorem B8260663 : Blo 1449544 8260663 := bstep (se 1 (by rfl) ⟨6195497, by rfl⟩ : syracuseStep 8260663 = 12390995) B12390995
theorem B23858621 : Blo 1449544 23858621 := bstep (se 3 (by rfl) ⟨4473491, by rfl⟩ : syracuseStep 23858621 = 8946983) B8946983
theorem B7843301 : Blo 1449544 7843301 := bstep (se 4 (by rfl) ⟨735309, by rfl⟩ : syracuseStep 7843301 = 1470619) B1470619
theorem B2174441 : Blo 1449544 2174441 := bstep (se 2 (by rfl) ⟨815415, by rfl⟩ : syracuseStep 2174441 = 1630831) B1630831
theorem B2174495 : Blo 1449544 2174495 := bstep (se 1 (by rfl) ⟨1630871, by rfl⟩ : syracuseStep 2174495 = 3261743) B3261743
theorem B2174585 : Blo 1449544 2174585 := bstep (se 2 (by rfl) ⟨815469, by rfl⟩ : syracuseStep 2174585 = 1630939) B1630939
theorem B9293555 : Blo 1449544 9293555 := bstep (se 1 (by rfl) ⟨6970166, by rfl⟩ : syracuseStep 9293555 = 13940333) B13940333
theorem B4132633 : Blo 1449544 4132633 := bstep (se 2 (by rfl) ⟨1549737, by rfl⟩ : syracuseStep 4132633 = 3099475) B3099475
theorem B3264335 : Blo 1449544 3264335 := bstep (se 1 (by rfl) ⟨2448251, by rfl⟩ : syracuseStep 3264335 = 4896503) B4896503
theorem B2174831 : Blo 1449544 2174831 := bstep (se 1 (by rfl) ⟨1631123, by rfl⟩ : syracuseStep 2174831 = 3262247) B3262247
theorem B2175083 : Blo 1449544 2175083 := bstep (se 1 (by rfl) ⟨1631312, by rfl⟩ : syracuseStep 2175083 = 3262625) B3262625
theorem B26456321 : Blo 1449544 26456321 := bstep (se 2 (by rfl) ⟨9921120, by rfl⟩ : syracuseStep 26456321 = 19842241) B19842241
theorem B3920147 : Blo 1449544 3920147 := bstep (se 1 (by rfl) ⟨2940110, by rfl⟩ : syracuseStep 3920147 = 5880221) B5880221
theorem B10195267 : Blo 1449544 10195267 := bstep (se 1 (by rfl) ⟨7646450, by rfl⟩ : syracuseStep 10195267 = 15292901) B15292901
theorem B48976265 : Blo 1449544 48976265 := bstep (se 2 (by rfl) ⟨18366099, by rfl⟩ : syracuseStep 48976265 = 36732199) B36732199
theorem B18575831 : Blo 1449544 18575831 := bstep (se 1 (by rfl) ⟨13931873, by rfl⟩ : syracuseStep 18575831 = 27863747) B27863747
theorem B8262121 : Blo 1449544 8262121 := bstep (se 2 (by rfl) ⟨3098295, by rfl⟩ : syracuseStep 8262121 = 6196591) B6196591
theorem B2175515 : Blo 1449544 2175515 := bstep (se 1 (by rfl) ⟨1631636, by rfl⟩ : syracuseStep 2175515 = 3263273) B3263273
theorem B3265055 : Blo 1449544 3265055 := bstep (se 1 (by rfl) ⟨2448791, by rfl⟩ : syracuseStep 3265055 = 4897583) B4897583
theorem B2175695 : Blo 1449544 2175695 := bstep (se 1 (by rfl) ⟨1631771, by rfl⟩ : syracuseStep 2175695 = 3263543) B3263543
theorem B13234907 : Blo 1449544 13234907 := bstep (se 1 (by rfl) ⟨9926180, by rfl⟩ : syracuseStep 13234907 = 19852361) B19852361
theorem B8262395 : Blo 1449544 8262395 := bstep (se 1 (by rfl) ⟨6196796, by rfl⟩ : syracuseStep 8262395 = 12393593) B12393593
theorem B3265487 : Blo 1449544 3265487 := bstep (se 1 (by rfl) ⟨2449115, by rfl⟩ : syracuseStep 3265487 = 4898231) B4898231
theorem B2175983 : Blo 1449544 2175983 := bstep (se 1 (by rfl) ⟨1631987, by rfl⟩ : syracuseStep 2175983 = 3263975) B3263975
theorem B3265577 : Blo 1449544 3265577 := bstep (se 2 (by rfl) ⟨1224591, by rfl⟩ : syracuseStep 3265577 = 2449183) B2449183
theorem B3265847 : Blo 1449544 3265847 := bstep (se 1 (by rfl) ⟨2449385, by rfl⟩ : syracuseStep 3265847 = 4898771) B4898771
theorem B3265865 : Blo 1449544 3265865 := bstep (se 2 (by rfl) ⟨1224699, by rfl⟩ : syracuseStep 3265865 = 2449399) B2449399
theorem B2176367 : Blo 1449544 2176367 := bstep (se 1 (by rfl) ⟨1632275, by rfl⟩ : syracuseStep 2176367 = 3264551) B3264551
theorem B2176487 : Blo 1449544 2176487 := bstep (se 1 (by rfl) ⟨1632365, by rfl⟩ : syracuseStep 2176487 = 3264731) B3264731
theorem B2176667 : Blo 1449544 2176667 := bstep (se 1 (by rfl) ⟨1632500, by rfl⟩ : syracuseStep 2176667 = 3265001) B3265001
theorem B5101231 : Blo 1449544 5101231 := bstep (se 1 (by rfl) ⟨3825923, by rfl⟩ : syracuseStep 5101231 = 7651847) B7651847
theorem B7345889 : Blo 1449544 7345889 := bstep (se 2 (by rfl) ⟨2754708, by rfl⟩ : syracuseStep 7345889 = 5509417) B5509417
theorem B2324351 : Blo 1449544 2324351 := bstep (se 1 (by rfl) ⟨1743263, by rfl⟩ : syracuseStep 2324351 = 3486527) B3486527
theorem B2177003 : Blo 1449544 2177003 := bstep (se 1 (by rfl) ⟨1632752, by rfl⟩ : syracuseStep 2177003 = 3265505) B3265505
theorem B2447401 : Blo 1449544 2447401 := bstep (se 2 (by rfl) ⟨917775, by rfl⟩ : syracuseStep 2447401 = 1835551) B1835551
theorem B2177087 : Blo 1449544 2177087 := bstep (se 1 (by rfl) ⟨1632815, by rfl⟩ : syracuseStep 2177087 = 3265631) B3265631
theorem B62773703 : Blo 1449544 62773703 := bstep (se 1 (by rfl) ⟨47080277, by rfl⟩ : syracuseStep 62773703 = 94160555) B94160555
theorem B9296527 : Blo 1449544 9296527 := bstep (se 1 (by rfl) ⟨6972395, by rfl⟩ : syracuseStep 9296527 = 13944791) B13944791
theorem B2792171 : Blo 1449544 2792171 := bstep (se 1 (by rfl) ⟨2094128, by rfl⟩ : syracuseStep 2792171 = 4188257) B4188257
theorem B2448191 : Blo 1449544 2448191 := bstep (se 1 (by rfl) ⟨1836143, by rfl⟩ : syracuseStep 2448191 = 3672287) B3672287
theorem B7847059 : Blo 1449544 7847059 := bstep (se 1 (by rfl) ⟨5885294, by rfl⟩ : syracuseStep 7847059 = 11770589) B11770589
theorem B4897961 : Blo 1449544 4897961 := bstep (se 2 (by rfl) ⟨1836735, by rfl⟩ : syracuseStep 4897961 = 3673471) B3673471
theorem B13237501 : Blo 1449544 13237501 := bstep (se 3 (by rfl) ⟨2482031, by rfl⟩ : syracuseStep 13237501 = 4964063) B4964063
theorem B37174625 : Blo 1449544 37174625 := bstep (se 2 (by rfl) ⟨13940484, by rfl⟩ : syracuseStep 37174625 = 27880969) B27880969
theorem B6786997685 : Blo 1449544 6786997685 := bstep (se 5 (by rfl) ⟨318140516, by rfl⟩ : syracuseStep 6786997685 = 636281033) B636281033
theorem B1449575 : Blo 1449544 1449575 := bstep (se 1 (by rfl) ⟨1087181, by rfl⟩ : syracuseStep 1449575 = 2174363) B2174363
theorem B7347833 : Blo 1449544 7347833 := bstep (se 2 (by rfl) ⟨2755437, by rfl⟩ : syracuseStep 7347833 = 5510875) B5510875
theorem B8257247 : Blo 1449544 8257247 := bstep (se 1 (by rfl) ⟨6192935, by rfl⟩ : syracuseStep 8257247 = 12385871) B12385871
theorem B20905775 : Blo 1449544 20905775 := bstep (se 1 (by rfl) ⟨15679331, by rfl⟩ : syracuseStep 20905775 = 31358663) B31358663
theorem B1449855 : Blo 1449544 1449855 := bstep (se 1 (by rfl) ⟨1087391, by rfl⟩ : syracuseStep 1449855 = 2174783) B2174783
theorem B2752393 : Blo 1449544 2752393 := bstep (se 2 (by rfl) ⟨1032147, by rfl⟩ : syracuseStep 2752393 = 2064295) B2064295
theorem B6971359 : Blo 1449544 6971359 := bstep (se 1 (by rfl) ⟨5228519, by rfl⟩ : syracuseStep 6971359 = 10457039) B10457039
theorem B1449979 : Blo 1449544 1449979 := bstep (se 1 (by rfl) ⟨1087484, by rfl⟩ : syracuseStep 1449979 = 2174969) B2174969
theorem B1450055 : Blo 1449544 1450055 := bstep (se 1 (by rfl) ⟨1087541, by rfl⟩ : syracuseStep 1450055 = 2175083) B2175083
theorem B17637547 : Blo 1449544 17637547 := bstep (se 1 (by rfl) ⟨13228160, by rfl⟩ : syracuseStep 17637547 = 26456321) B26456321
theorem B2613431 : Blo 1449544 2613431 := bstep (se 1 (by rfl) ⟨1960073, by rfl⟩ : syracuseStep 2613431 = 3920147) B3920147
theorem B1450343 : Blo 1449544 1450343 := bstep (se 1 (by rfl) ⟨1087757, by rfl⟩ : syracuseStep 1450343 = 2175515) B2175515
theorem B1450463 : Blo 1449544 1450463 := bstep (se 1 (by rfl) ⟨1087847, by rfl⟩ : syracuseStep 1450463 = 2175695) B2175695
theorem B8823271 : Blo 1449544 8823271 := bstep (se 1 (by rfl) ⟨6617453, by rfl⟩ : syracuseStep 8823271 = 13234907) B13234907
theorem B3670555 : Blo 1449544 3670555 := bstep (se 1 (by rfl) ⟨2752916, by rfl⟩ : syracuseStep 3670555 = 5505833) B5505833
theorem B1450655 : Blo 1449544 1450655 := bstep (se 1 (by rfl) ⟨1087991, by rfl⟩ : syracuseStep 1450655 = 2175983) B2175983
theorem B7340867 : Blo 1449544 7340867 := bstep (se 1 (by rfl) ⟨5505650, by rfl⟩ : syracuseStep 7340867 = 11011301) B11011301
theorem B12395369 : Blo 1449544 12395369 := bstep (se 2 (by rfl) ⟨4648263, by rfl⟩ : syracuseStep 12395369 = 9296527) B9296527
theorem B4187009 : Blo 1449544 4187009 := bstep (se 2 (by rfl) ⟨1570128, by rfl⟩ : syracuseStep 4187009 = 3140257) B3140257
theorem B1450911 : Blo 1449544 1450911 := bstep (se 1 (by rfl) ⟨1088183, by rfl⟩ : syracuseStep 1450911 = 2176367) B2176367
theorem B1450991 : Blo 1449544 1450991 := bstep (se 1 (by rfl) ⟨1088243, by rfl⟩ : syracuseStep 1450991 = 2176487) B2176487
theorem B1451111 : Blo 1449544 1451111 := bstep (se 1 (by rfl) ⟨1088333, by rfl⟩ : syracuseStep 1451111 = 2176667) B2176667
theorem B7341191 : Blo 1449544 7341191 := bstep (se 1 (by rfl) ⟨5505893, by rfl⟩ : syracuseStep 7341191 = 11011787) B11011787
theorem B13943947 : Blo 1449544 13943947 := bstep (se 1 (by rfl) ⟨10457960, by rfl⟩ : syracuseStep 13943947 = 20915921) B20915921
theorem B3261671 : Blo 1449544 3261671 := bstep (se 1 (by rfl) ⟨2446253, by rfl⟩ : syracuseStep 3261671 = 4892507) B4892507
theorem B1549567 : Blo 1449544 1549567 := bstep (se 1 (by rfl) ⟨1162175, by rfl⟩ : syracuseStep 1549567 = 2324351) B2324351
theorem B1451335 : Blo 1449544 1451335 := bstep (se 1 (by rfl) ⟨1088501, by rfl⟩ : syracuseStep 1451335 = 2177003) B2177003
theorem B1451391 : Blo 1449544 1451391 := bstep (se 1 (by rfl) ⟨1088543, by rfl⟩ : syracuseStep 1451391 = 2177087) B2177087
theorem B19842515 : Blo 1449544 19842515 := bstep (se 1 (by rfl) ⟨14881886, by rfl⟩ : syracuseStep 19842515 = 29763773) B29763773
theorem B10462745 : Blo 1449544 10462745 := bstep (se 2 (by rfl) ⟨3923529, by rfl⟩ : syracuseStep 10462745 = 7847059) B7847059
theorem B3262319 : Blo 1449544 3262319 := bstep (se 1 (by rfl) ⟨2446739, by rfl⟩ : syracuseStep 3262319 = 4893479) B4893479
theorem B1632127 : Blo 1449544 1632127 := bstep (se 1 (by rfl) ⟨1224095, by rfl⟩ : syracuseStep 1632127 = 2448191) B2448191
theorem B4409255 : Blo 1449544 4409255 := bstep (se 1 (by rfl) ⟨3306941, by rfl⟩ : syracuseStep 4409255 = 6613883) B6613883
theorem B5506987 : Blo 1449544 5506987 := bstep (se 1 (by rfl) ⟨4130240, by rfl⟩ : syracuseStep 5506987 = 8260481) B8260481
theorem B5507261 : Blo 1449544 5507261 := bstep (se 3 (by rfl) ⟨1032611, by rfl⟩ : syracuseStep 5507261 = 2065223) B2065223
theorem B24783083 : Blo 1449544 24783083 := bstep (se 1 (by rfl) ⟨18587312, by rfl⟩ : syracuseStep 24783083 = 37174625) B37174625
theorem B6801641 : Blo 1449544 6801641 := bstep (se 2 (by rfl) ⟨2550615, by rfl⟩ : syracuseStep 6801641 = 5101231) B5101231
theorem B4524665123 : Blo 1449544 4524665123 := bstep (se 1 (by rfl) ⟨3393498842, by rfl⟩ : syracuseStep 4524665123 = 6786997685) B6786997685
theorem B5228867 : Blo 1449544 5228867 := bstep (se 1 (by rfl) ⟨3921650, by rfl⟩ : syracuseStep 5228867 = 7843301) B7843301
theorem B6195703 : Blo 1449544 6195703 := bstep (se 1 (by rfl) ⟨4646777, by rfl⟩ : syracuseStep 6195703 = 9293555) B9293555
theorem B13937183 : Blo 1449544 13937183 := bstep (se 1 (by rfl) ⟨10452887, by rfl⟩ : syracuseStep 13937183 = 20905775) B20905775
theorem B10193489 : Blo 1449544 10193489 := bstep (se 2 (by rfl) ⟨3822558, by rfl⟩ : syracuseStep 10193489 = 7645117) B7645117
theorem B3263201 : Blo 1449544 3263201 := bstep (se 2 (by rfl) ⟨1223700, by rfl⟩ : syracuseStep 3263201 = 2447401) B2447401
theorem B5507945 : Blo 1449544 5507945 := bstep (se 2 (by rfl) ⟨2065479, by rfl⟩ : syracuseStep 5507945 = 4130959) B4130959
theorem B3673097 : Blo 1449544 3673097 := bstep (se 2 (by rfl) ⟨1377411, by rfl⟩ : syracuseStep 3673097 = 2754823) B2754823
theorem B13593689 : Blo 1449544 13593689 := bstep (se 2 (by rfl) ⟨5097633, by rfl⟩ : syracuseStep 13593689 = 10195267) B10195267
theorem B11013245 : Blo 1449544 11013245 := bstep (se 3 (by rfl) ⟨2064983, by rfl⟩ : syracuseStep 11013245 = 4129967) B4129967
theorem B5508263 : Blo 1449544 5508263 := bstep (se 1 (by rfl) ⟨4131197, by rfl⟩ : syracuseStep 5508263 = 8262395) B8262395
theorem B3484883 : Blo 1449544 3484883 := bstep (se 1 (by rfl) ⟨2613662, by rfl⟩ : syracuseStep 3484883 = 5227325) B5227325
theorem B95415803 : Blo 1449544 95415803 := bstep (se 1 (by rfl) ⟨71561852, by rfl⟩ : syracuseStep 95415803 = 143123705) B143123705
theorem B2174567 : Blo 1449544 2174567 := bstep (se 1 (by rfl) ⟨1630925, by rfl⟩ : syracuseStep 2174567 = 3261851) B3261851
theorem B4894451 : Blo 1449544 4894451 := bstep (se 1 (by rfl) ⟨3670838, by rfl⟩ : syracuseStep 4894451 = 7341677) B7341677
theorem B2322287 : Blo 1449544 2322287 := bstep (se 1 (by rfl) ⟨1741715, by rfl⟩ : syracuseStep 2322287 = 3483431) B3483431
theorem B11014217 : Blo 1449544 11014217 := bstep (se 2 (by rfl) ⟨4130331, by rfl⟩ : syracuseStep 11014217 = 8260663) B8260663
theorem B2175113 : Blo 1449544 2175113 := bstep (se 2 (by rfl) ⟨815667, by rfl⟩ : syracuseStep 2175113 = 1631335) B1631335
theorem B41849135 : Blo 1449544 41849135 := bstep (se 1 (by rfl) ⟨31386851, by rfl⟩ : syracuseStep 41849135 = 62773703) B62773703
theorem B17650001 : Blo 1449544 17650001 := bstep (se 2 (by rfl) ⟨6618750, by rfl⟩ : syracuseStep 17650001 = 13237501) B13237501
theorem B3265307 : Blo 1449544 3265307 := bstep (se 1 (by rfl) ⟨2448980, by rfl⟩ : syracuseStep 3265307 = 4897961) B4897961
theorem B15905747 : Blo 1449544 15905747 := bstep (se 1 (by rfl) ⟨11929310, by rfl⟩ : syracuseStep 15905747 = 23858621) B23858621
theorem B5510177 : Blo 1449544 5510177 := bstep (se 2 (by rfl) ⟨2066316, by rfl⟩ : syracuseStep 5510177 = 4132633) B4132633
theorem B2176223 : Blo 1449544 2176223 := bstep (se 1 (by rfl) ⟨1632167, by rfl⟩ : syracuseStep 2176223 = 3264335) B3264335
theorem B9295145 : Blo 1449544 9295145 := bstep (se 2 (by rfl) ⟨3485679, by rfl⟩ : syracuseStep 9295145 = 6971359) B6971359
theorem B12383887 : Blo 1449544 12383887 := bstep (se 1 (by rfl) ⟨9287915, by rfl⟩ : syracuseStep 12383887 = 18575831) B18575831
theorem B2447023 : Blo 1449544 2447023 := bstep (se 1 (by rfl) ⟨1835267, by rfl⟩ : syracuseStep 2447023 = 3670535) B3670535
theorem B2176703 : Blo 1449544 2176703 := bstep (se 1 (by rfl) ⟨1632527, by rfl⟩ : syracuseStep 2176703 = 3265055) B3265055
theorem B31348457 : Blo 1449544 31348457 := bstep (se 2 (by rfl) ⟨11755671, by rfl⟩ : syracuseStep 31348457 = 23511343) B23511343
theorem B2176991 : Blo 1449544 2176991 := bstep (se 1 (by rfl) ⟨1632743, by rfl⟩ : syracuseStep 2176991 = 3265487) B3265487
theorem B11016161 : Blo 1449544 11016161 := bstep (se 2 (by rfl) ⟨4131060, by rfl⟩ : syracuseStep 11016161 = 8262121) B8262121
theorem B2177051 : Blo 1449544 2177051 := bstep (se 1 (by rfl) ⟨1632788, by rfl⟩ : syracuseStep 2177051 = 3265577) B3265577
theorem B12392635 : Blo 1449544 12392635 := bstep (se 1 (by rfl) ⟨9294476, by rfl⟩ : syracuseStep 12392635 = 18588953) B18588953
theorem B2177231 : Blo 1449544 2177231 := bstep (se 1 (by rfl) ⟨1632923, by rfl⟩ : syracuseStep 2177231 = 3265847) B3265847
theorem B11311319 : Blo 1449544 11311319 := bstep (se 1 (by rfl) ⟨8483489, by rfl⟩ : syracuseStep 11311319 = 16966979) B16966979
theorem B2177243 : Blo 1449544 2177243 := bstep (se 1 (by rfl) ⟨1632932, by rfl⟩ : syracuseStep 2177243 = 3265865) B3265865
theorem B130603373 : Blo 1449544 130603373 := bstep (se 3 (by rfl) ⟨24488132, by rfl⟩ : syracuseStep 130603373 = 48976265) B48976265
theorem B4897259 : Blo 1449544 4897259 := bstep (se 1 (by rfl) ⟨3672944, by rfl⟩ : syracuseStep 4897259 = 7345889) B7345889
theorem B26458721 : Blo 1449544 26458721 := bstep (se 2 (by rfl) ⟨9922020, by rfl⟩ : syracuseStep 26458721 = 19844041) B19844041
theorem B2448137 : Blo 1449544 2448137 := bstep (se 2 (by rfl) ⟨918051, by rfl⟩ : syracuseStep 2448137 = 1836103) B1836103
theorem B7347023 : Blo 1449544 7347023 := bstep (se 1 (by rfl) ⟨5510267, by rfl⟩ : syracuseStep 7347023 = 11020535) B11020535
theorem B7445789 : Blo 1449544 7445789 := bstep (se 3 (by rfl) ⟨1396085, by rfl⟩ : syracuseStep 7445789 = 2792171) B2792171
theorem B1449627 : Blo 1449544 1449627 := bstep (se 1 (by rfl) ⟨1087220, by rfl⟩ : syracuseStep 1449627 = 2174441) B2174441
theorem B1449663 : Blo 1449544 1449663 := bstep (se 1 (by rfl) ⟨1087247, by rfl⟩ : syracuseStep 1449663 = 2174495) B2174495
theorem B1449723 : Blo 1449544 1449723 := bstep (se 1 (by rfl) ⟨1087292, by rfl⟩ : syracuseStep 1449723 = 2174585) B2174585
theorem B4898555 : Blo 1449544 4898555 := bstep (se 1 (by rfl) ⟨3673916, by rfl⟩ : syracuseStep 4898555 = 7347833) B7347833
theorem B5504831 : Blo 1449544 5504831 := bstep (se 1 (by rfl) ⟨4128623, by rfl⟩ : syracuseStep 5504831 = 8257247) B8257247
theorem B3669857 : Blo 1449544 3669857 := bstep (se 2 (by rfl) ⟨1376196, by rfl⟩ : syracuseStep 3669857 = 2752393) B2752393
theorem B1449887 : Blo 1449544 1449887 := bstep (se 1 (by rfl) ⟨1087415, by rfl⟩ : syracuseStep 1449887 = 2174831) B2174831
theorem B1450075 : Blo 1449544 1450075 := bstep (se 1 (by rfl) ⟨1087556, by rfl⟩ : syracuseStep 1450075 = 2175113) B2175113
theorem B16523513 : Blo 1449544 16523513 := bstep (se 2 (by rfl) ⟨6196317, by rfl⟩ : syracuseStep 16523513 = 12392635) B12392635
theorem B11764361 : Blo 1449544 11764361 := bstep (se 2 (by rfl) ⟨4411635, by rfl⟩ : syracuseStep 11764361 = 8823271) B8823271
theorem B1450815 : Blo 1449544 1450815 := bstep (se 1 (by rfl) ⟨1088111, by rfl⟩ : syracuseStep 1450815 = 2176223) B2176223
theorem B1451135 : Blo 1449544 1451135 := bstep (se 1 (by rfl) ⟨1088351, by rfl⟩ : syracuseStep 1451135 = 2176703) B2176703
theorem B20898971 : Blo 1449544 20898971 := bstep (se 1 (by rfl) ⟨15674228, by rfl⟩ : syracuseStep 20898971 = 31348457) B31348457
theorem B1451327 : Blo 1449544 1451327 := bstep (se 1 (by rfl) ⟨1088495, by rfl⟩ : syracuseStep 1451327 = 2176991) B2176991
theorem B1451367 : Blo 1449544 1451367 := bstep (se 1 (by rfl) ⟨1088525, by rfl⟩ : syracuseStep 1451367 = 2177051) B2177051
theorem B3671507 : Blo 1449544 3671507 := bstep (se 1 (by rfl) ⟨2753630, by rfl⟩ : syracuseStep 3671507 = 5507261) B5507261
theorem B1451487 : Blo 1449544 1451487 := bstep (se 1 (by rfl) ⟨1088615, by rfl⟩ : syracuseStep 1451487 = 2177231) B2177231
theorem B1451495 : Blo 1449544 1451495 := bstep (se 1 (by rfl) ⟨1088621, by rfl⟩ : syracuseStep 1451495 = 2177243) B2177243
theorem B3016443415 : Blo 1449544 3016443415 := bstep (se 1 (by rfl) ⟨2262332561, by rfl⟩ : syracuseStep 3016443415 = 4524665123) B4524665123
theorem B2066089 : Blo 1449544 2066089 := bstep (se 2 (by rfl) ⟨774783, by rfl⟩ : syracuseStep 2066089 = 1549567) B1549567
theorem B9291455 : Blo 1449544 9291455 := bstep (se 1 (by rfl) ⟨6968591, by rfl⟩ : syracuseStep 9291455 = 13937183) B13937183
theorem B17639147 : Blo 1449544 17639147 := bstep (se 1 (by rfl) ⟨13229360, by rfl⟩ : syracuseStep 17639147 = 26458721) B26458721
theorem B1632091 : Blo 1449544 1632091 := bstep (se 1 (by rfl) ⟨1224068, by rfl⟩ : syracuseStep 1632091 = 2448137) B2448137
theorem B3671963 : Blo 1449544 3671963 := bstep (se 1 (by rfl) ⟨2753972, by rfl⟩ : syracuseStep 3671963 = 5507945) B5507945
theorem B9062459 : Blo 1449544 9062459 := bstep (se 1 (by rfl) ⟨6796844, by rfl⟩ : syracuseStep 9062459 = 13593689) B13593689
theorem B7342163 : Blo 1449544 7342163 := bstep (se 1 (by rfl) ⟨5506622, by rfl⟩ : syracuseStep 7342163 = 11013245) B11013245
theorem B3672175 : Blo 1449544 3672175 := bstep (se 1 (by rfl) ⟨2754131, by rfl⟩ : syracuseStep 3672175 = 5508263) B5508263
theorem B3262697 : Blo 1449544 3262697 := bstep (se 2 (by rfl) ⟨1223511, by rfl⟩ : syracuseStep 3262697 = 2447023) B2447023
theorem B3262967 : Blo 1449544 3262967 := bstep (se 1 (by rfl) ⟨2447225, by rfl⟩ : syracuseStep 3262967 = 4894451) B4894451
theorem B7342649 : Blo 1449544 7342649 := bstep (se 2 (by rfl) ⟨2753493, by rfl⟩ : syracuseStep 7342649 = 5506987) B5506987
theorem B7342811 : Blo 1449544 7342811 := bstep (se 1 (by rfl) ⟨5507108, by rfl⟩ : syracuseStep 7342811 = 11014217) B11014217
theorem B4893911 : Blo 1449544 4893911 := bstep (se 1 (by rfl) ⟨3670433, by rfl⟩ : syracuseStep 4893911 = 7340867) B7340867
theorem B10603831 : Blo 1449544 10603831 := bstep (se 1 (by rfl) ⟨7952873, by rfl⟩ : syracuseStep 10603831 = 15905747) B15905747
theorem B8260937 : Blo 1449544 8260937 := bstep (se 2 (by rfl) ⟨3097851, by rfl⟩ : syracuseStep 8260937 = 6195703) B6195703
theorem B3673451 : Blo 1449544 3673451 := bstep (se 1 (by rfl) ⟨2755088, by rfl⟩ : syracuseStep 3673451 = 5510177) B5510177
theorem B4894073 : Blo 1449544 4894073 := bstep (se 2 (by rfl) ⟨1835277, by rfl⟩ : syracuseStep 4894073 = 3670555) B3670555
theorem B4894127 : Blo 1449544 4894127 := bstep (se 1 (by rfl) ⟨3670595, by rfl⟩ : syracuseStep 4894127 = 7341191) B7341191
theorem B2174447 : Blo 1449544 2174447 := bstep (se 1 (by rfl) ⟨1630835, by rfl⟩ : syracuseStep 2174447 = 3261671) B3261671
theorem B6196763 : Blo 1449544 6196763 := bstep (se 1 (by rfl) ⟨4647572, by rfl⟩ : syracuseStep 6196763 = 9295145) B9295145
theorem B47066669 : Blo 1449544 47066669 := bstep (se 3 (by rfl) ⟨8825000, by rfl⟩ : syracuseStep 47066669 = 17650001) B17650001
theorem B6975163 : Blo 1449544 6975163 := bstep (se 1 (by rfl) ⟨5231372, by rfl⟩ : syracuseStep 6975163 = 10462745) B10462745
theorem B2174879 : Blo 1449544 2174879 := bstep (se 1 (by rfl) ⟨1631159, by rfl⟩ : syracuseStep 2174879 = 3262319) B3262319
theorem B7344107 : Blo 1449544 7344107 := bstep (se 1 (by rfl) ⟨5508080, by rfl⟩ : syracuseStep 7344107 = 11016161) B11016161
theorem B7540879 : Blo 1449544 7540879 := bstep (se 1 (by rfl) ⟨5655659, by rfl⟩ : syracuseStep 7540879 = 11311319) B11311319
theorem B4534427 : Blo 1449544 4534427 := bstep (se 1 (by rfl) ⟨3400820, by rfl⟩ : syracuseStep 4534427 = 6801641) B6801641
theorem B18591929 : Blo 1449544 18591929 := bstep (se 2 (by rfl) ⟨6971973, by rfl⟩ : syracuseStep 18591929 = 13943947) B13943947
theorem B3485911 : Blo 1449544 3485911 := bstep (se 1 (by rfl) ⟨2614433, by rfl⟩ : syracuseStep 3485911 = 5228867) B5228867
theorem B87068915 : Blo 1449544 87068915 := bstep (se 1 (by rfl) ⟨65301686, by rfl⟩ : syracuseStep 87068915 = 130603373) B130603373
theorem B3264839 : Blo 1449544 3264839 := bstep (se 1 (by rfl) ⟨2448629, by rfl⟩ : syracuseStep 3264839 = 4897259) B4897259
theorem B6795659 : Blo 1449544 6795659 := bstep (se 1 (by rfl) ⟨5096744, by rfl⟩ : syracuseStep 6795659 = 10193489) B10193489
theorem B2175467 : Blo 1449544 2175467 := bstep (se 1 (by rfl) ⟨1631600, by rfl⟩ : syracuseStep 2175467 = 3263201) B3263201
theorem B2323255 : Blo 1449544 2323255 := bstep (se 1 (by rfl) ⟨1742441, by rfl⟩ : syracuseStep 2323255 = 3484883) B3484883
theorem B16511849 : Blo 1449544 16511849 := bstep (se 2 (by rfl) ⟨6191943, by rfl⟩ : syracuseStep 16511849 = 12383887) B12383887
theorem B3265703 : Blo 1449544 3265703 := bstep (se 1 (by rfl) ⟨2449277, by rfl⟩ : syracuseStep 3265703 = 4898555) B4898555
theorem B2176169 : Blo 1449544 2176169 := bstep (se 2 (by rfl) ⟨816063, by rfl⟩ : syracuseStep 2176169 = 1632127) B1632127
theorem B2446571 : Blo 1449544 2446571 := bstep (se 1 (by rfl) ⟨1834928, by rfl⟩ : syracuseStep 2446571 = 3669857) B3669857
theorem B27899423 : Blo 1449544 27899423 := bstep (se 1 (by rfl) ⟨20924567, by rfl⟩ : syracuseStep 27899423 = 41849135) B41849135
theorem B23516729 : Blo 1449544 23516729 := bstep (se 2 (by rfl) ⟨8818773, by rfl⟩ : syracuseStep 23516729 = 17637547) B17637547
theorem B6969149 : Blo 1449544 6969149 := bstep (se 3 (by rfl) ⟨1306715, by rfl⟩ : syracuseStep 6969149 = 2613431) B2613431
theorem B2176871 : Blo 1449544 2176871 := bstep (se 1 (by rfl) ⟨1632653, by rfl⟩ : syracuseStep 2176871 = 3265307) B3265307
theorem B8263579 : Blo 1449544 8263579 := bstep (se 1 (by rfl) ⟨6197684, by rfl⟩ : syracuseStep 8263579 = 12395369) B12395369
theorem B13228343 : Blo 1449544 13228343 := bstep (se 1 (by rfl) ⟨9921257, by rfl⟩ : syracuseStep 13228343 = 19842515) B19842515
theorem B2939503 : Blo 1449544 2939503 := bstep (se 1 (by rfl) ⟨2204627, by rfl⟩ : syracuseStep 2939503 = 4409255) B4409255
theorem B16522055 : Blo 1449544 16522055 := bstep (se 1 (by rfl) ⟨12391541, by rfl⟩ : syracuseStep 16522055 = 24783083) B24783083
theorem B4898015 : Blo 1449544 4898015 := bstep (se 1 (by rfl) ⟨3673511, by rfl⟩ : syracuseStep 4898015 = 7347023) B7347023
theorem B2448731 : Blo 1449544 2448731 := bstep (se 1 (by rfl) ⟨1836548, by rfl⟩ : syracuseStep 2448731 = 3673097) B3673097
theorem B4963859 : Blo 1449544 4963859 := bstep (se 1 (by rfl) ⟨3722894, by rfl⟩ : syracuseStep 4963859 = 7445789) B7445789
theorem B63610535 : Blo 1449544 63610535 := bstep (se 1 (by rfl) ⟨47707901, by rfl⟩ : syracuseStep 63610535 = 95415803) B95415803
theorem B11165357 : Blo 1449544 11165357 := bstep (se 3 (by rfl) ⟨2093504, by rfl⟩ : syracuseStep 11165357 = 4187009) B4187009
theorem B1449711 : Blo 1449544 1449711 := bstep (se 1 (by rfl) ⟨1087283, by rfl⟩ : syracuseStep 1449711 = 2174567) B2174567
theorem B3669887 : Blo 1449544 3669887 := bstep (se 1 (by rfl) ⟨2752415, by rfl⟩ : syracuseStep 3669887 = 5504831) B5504831
theorem B1548191 : Blo 1449544 1548191 := bstep (se 1 (by rfl) ⟨1161143, by rfl⟩ : syracuseStep 1548191 = 2322287) B2322287
theorem B3022951 : Blo 1449544 3022951 := bstep (se 1 (by rfl) ⟨2267213, by rfl⟩ : syracuseStep 3022951 = 4534427) B4534427
theorem B12394619 : Blo 1449544 12394619 := bstep (se 1 (by rfl) ⟨9295964, by rfl⟩ : syracuseStep 12394619 = 18591929) B18591929
theorem B4530439 : Blo 1449544 4530439 := bstep (se 1 (by rfl) ⟨3397829, by rfl⟩ : syracuseStep 4530439 = 6795659) B6795659
theorem B1450311 : Blo 1449544 1450311 := bstep (se 1 (by rfl) ⟨1087733, by rfl⟩ : syracuseStep 1450311 = 2175467) B2175467
theorem B1450779 : Blo 1449544 1450779 := bstep (se 1 (by rfl) ⟨1088084, by rfl⟩ : syracuseStep 1450779 = 2176169) B2176169
theorem B1631047 : Blo 1449544 1631047 := bstep (se 1 (by rfl) ⟨1223285, by rfl⟩ : syracuseStep 1631047 = 2446571) B2446571
theorem B37200869 : Blo 1449544 37200869 := bstep (se 4 (by rfl) ⟨3487581, by rfl⟩ : syracuseStep 37200869 = 6975163) B6975163
theorem B3097673 : Blo 1449544 3097673 := bstep (se 2 (by rfl) ⟨1161627, by rfl⟩ : syracuseStep 3097673 = 2323255) B2323255
theorem B6194303 : Blo 1449544 6194303 := bstep (se 1 (by rfl) ⟨4645727, by rfl⟩ : syracuseStep 6194303 = 9291455) B9291455
theorem B4646099 : Blo 1449544 4646099 := bstep (se 1 (by rfl) ⟨3484574, by rfl⟩ : syracuseStep 4646099 = 6969149) B6969149
theorem B1451247 : Blo 1449544 1451247 := bstep (se 1 (by rfl) ⟨1088435, by rfl⟩ : syracuseStep 1451247 = 2176871) B2176871
theorem B3262607 : Blo 1449544 3262607 := bstep (se 1 (by rfl) ⟨2446955, by rfl⟩ : syracuseStep 3262607 = 4893911) B4893911
theorem B5507291 : Blo 1449544 5507291 := bstep (se 1 (by rfl) ⟨4130468, by rfl⟩ : syracuseStep 5507291 = 8260937) B8260937
theorem B2754785 : Blo 1449544 2754785 := bstep (se 2 (by rfl) ⟨1033044, by rfl⟩ : syracuseStep 2754785 = 2066089) B2066089
theorem B1632487 : Blo 1449544 1632487 := bstep (se 1 (by rfl) ⟨1224365, by rfl⟩ : syracuseStep 1632487 = 2448731) B2448731
theorem B3262715 : Blo 1449544 3262715 := bstep (se 1 (by rfl) ⟨2447036, by rfl⟩ : syracuseStep 3262715 = 4894073) B4894073
theorem B3262751 : Blo 1449544 3262751 := bstep (se 1 (by rfl) ⟨2447063, by rfl⟩ : syracuseStep 3262751 = 4894127) B4894127
theorem B4131175 : Blo 1449544 4131175 := bstep (se 1 (by rfl) ⟨3098381, by rfl⟩ : syracuseStep 4131175 = 6196763) B6196763
theorem B31377779 : Blo 1449544 31377779 := bstep (se 1 (by rfl) ⟨23533334, by rfl⟩ : syracuseStep 31377779 = 47066669) B47066669
theorem B10054505 : Blo 1449544 10054505 := bstep (se 2 (by rfl) ⟨3770439, by rfl⟩ : syracuseStep 10054505 = 7540879) B7540879
theorem B4647881 : Blo 1449544 4647881 := bstep (se 2 (by rfl) ⟨1742955, by rfl⟩ : syracuseStep 4647881 = 3485911) B3485911
theorem B7842907 : Blo 1449544 7842907 := bstep (se 1 (by rfl) ⟨5882180, by rfl⟩ : syracuseStep 7842907 = 11764361) B11764361
theorem B3919337 : Blo 1449544 3919337 := bstep (se 2 (by rfl) ⟨1469751, by rfl⟩ : syracuseStep 3919337 = 2939503) B2939503
theorem B18599615 : Blo 1449544 18599615 := bstep (se 1 (by rfl) ⟨13949711, by rfl⟩ : syracuseStep 18599615 = 27899423) B27899423
theorem B11759431 : Blo 1449544 11759431 := bstep (se 1 (by rfl) ⟨8819573, by rfl⟩ : syracuseStep 11759431 = 17639147) B17639147
theorem B6041639 : Blo 1449544 6041639 := bstep (se 1 (by rfl) ⟨4531229, by rfl⟩ : syracuseStep 6041639 = 9062459) B9062459
theorem B4894775 : Blo 1449544 4894775 := bstep (se 1 (by rfl) ⟨3671081, by rfl⟩ : syracuseStep 4894775 = 7342163) B7342163
theorem B2175131 : Blo 1449544 2175131 := bstep (se 1 (by rfl) ⟨1631348, by rfl⟩ : syracuseStep 2175131 = 3262697) B3262697
theorem B8818895 : Blo 1449544 8818895 := bstep (se 1 (by rfl) ⟨6614171, by rfl⟩ : syracuseStep 8818895 = 13228343) B13228343
theorem B2175311 : Blo 1449544 2175311 := bstep (se 1 (by rfl) ⟨1631483, by rfl⟩ : syracuseStep 2175311 = 3262967) B3262967
theorem B4895099 : Blo 1449544 4895099 := bstep (se 1 (by rfl) ⟨3671324, by rfl⟩ : syracuseStep 4895099 = 7342649) B7342649
theorem B4895207 : Blo 1449544 4895207 := bstep (se 1 (by rfl) ⟨3671405, by rfl⟩ : syracuseStep 4895207 = 7342811) B7342811
theorem B11014703 : Blo 1449544 11014703 := bstep (se 1 (by rfl) ⟨8261027, by rfl⟩ : syracuseStep 11014703 = 16522055) B16522055
theorem B4021924553 : Blo 1449544 4021924553 := bstep (se 2 (by rfl) ⟨1508221707, by rfl⟩ : syracuseStep 4021924553 = 3016443415) B3016443415
theorem B3265343 : Blo 1449544 3265343 := bstep (se 1 (by rfl) ⟨2449007, by rfl⟩ : syracuseStep 3265343 = 4898015) B4898015
theorem B42407023 : Blo 1449544 42407023 := bstep (se 1 (by rfl) ⟨31805267, by rfl⟩ : syracuseStep 42407023 = 63610535) B63610535
theorem B7443571 : Blo 1449544 7443571 := bstep (se 1 (by rfl) ⟨5582678, by rfl⟩ : syracuseStep 7443571 = 11165357) B11165357
theorem B2176121 : Blo 1449544 2176121 := bstep (se 2 (by rfl) ⟨816045, by rfl⟩ : syracuseStep 2176121 = 1632091) B1632091
theorem B2446591 : Blo 1449544 2446591 := bstep (se 1 (by rfl) ⟨1834943, by rfl⟩ : syracuseStep 2446591 = 3669887) B3669887
theorem B4896071 : Blo 1449544 4896071 := bstep (se 1 (by rfl) ⟨3672053, by rfl⟩ : syracuseStep 4896071 = 7344107) B7344107
theorem B4896233 : Blo 1449544 4896233 := bstep (se 2 (by rfl) ⟨1836087, by rfl⟩ : syracuseStep 4896233 = 3672175) B3672175
theorem B58045943 : Blo 1449544 58045943 := bstep (se 1 (by rfl) ⟨43534457, by rfl⟩ : syracuseStep 58045943 = 87068915) B87068915
theorem B11015675 : Blo 1449544 11015675 := bstep (se 1 (by rfl) ⟨8261756, by rfl⟩ : syracuseStep 11015675 = 16523513) B16523513
theorem B2176559 : Blo 1449544 2176559 := bstep (se 1 (by rfl) ⟨1632419, by rfl⟩ : syracuseStep 2176559 = 3264839) B3264839
theorem B11007899 : Blo 1449544 11007899 := bstep (se 1 (by rfl) ⟨8255924, by rfl⟩ : syracuseStep 11007899 = 16511849) B16511849
theorem B13932647 : Blo 1449544 13932647 := bstep (se 1 (by rfl) ⟨10449485, by rfl⟩ : syracuseStep 13932647 = 20898971) B20898971
theorem B2177135 : Blo 1449544 2177135 := bstep (se 1 (by rfl) ⟨1632851, by rfl⟩ : syracuseStep 2177135 = 3265703) B3265703
theorem B2447671 : Blo 1449544 2447671 := bstep (se 1 (by rfl) ⟨1835753, by rfl⟩ : syracuseStep 2447671 = 3671507) B3671507
theorem B15677819 : Blo 1449544 15677819 := bstep (se 1 (by rfl) ⟨11758364, by rfl⟩ : syracuseStep 15677819 = 23516729) B23516729
theorem B2447975 : Blo 1449544 2447975 := bstep (se 1 (by rfl) ⟨1835981, by rfl⟩ : syracuseStep 2447975 = 3671963) B3671963
theorem B14138441 : Blo 1449544 14138441 := bstep (se 2 (by rfl) ⟨5301915, by rfl⟩ : syracuseStep 14138441 = 10603831) B10603831
theorem B2448967 : Blo 1449544 2448967 := bstep (se 1 (by rfl) ⟨1836725, by rfl⟩ : syracuseStep 2448967 = 3673451) B3673451
theorem B1449631 : Blo 1449544 1449631 := bstep (se 1 (by rfl) ⟨1087223, by rfl⟩ : syracuseStep 1449631 = 2174447) B2174447
theorem B3309239 : Blo 1449544 3309239 := bstep (se 1 (by rfl) ⟨2481929, by rfl⟩ : syracuseStep 3309239 = 4963859) B4963859
theorem B4128509 : Blo 1449544 4128509 := bstep (se 3 (by rfl) ⟨774095, by rfl⟩ : syracuseStep 4128509 = 1548191) B1548191
theorem B11018105 : Blo 1449544 11018105 := bstep (se 2 (by rfl) ⟨4131789, by rfl⟩ : syracuseStep 11018105 = 8263579) B8263579
theorem B1449919 : Blo 1449544 1449919 := bstep (se 1 (by rfl) ⟨1087439, by rfl⟩ : syracuseStep 1449919 = 2174879) B2174879
theorem B1450087 : Blo 1449544 1450087 := bstep (se 1 (by rfl) ⟨1087565, by rfl⟩ : syracuseStep 1450087 = 2175131) B2175131
theorem B4030601 : Blo 1449544 4030601 := bstep (se 2 (by rfl) ⟨1511475, by rfl⟩ : syracuseStep 4030601 = 3022951) B3022951
theorem B1450207 : Blo 1449544 1450207 := bstep (se 1 (by rfl) ⟨1087655, by rfl⟩ : syracuseStep 1450207 = 2175311) B2175311
theorem B2681283035 : Blo 1449544 2681283035 := bstep (se 1 (by rfl) ⟨2010962276, by rfl⟩ : syracuseStep 2681283035 = 4021924553) B4021924553
theorem B2065115 : Blo 1449544 2065115 := bstep (se 1 (by rfl) ⟨1548836, by rfl⟩ : syracuseStep 2065115 = 3097673) B3097673
theorem B1450747 : Blo 1449544 1450747 := bstep (se 1 (by rfl) ⟨1088060, by rfl⟩ : syracuseStep 1450747 = 2176121) B2176121
theorem B4129535 : Blo 1449544 4129535 := bstep (se 1 (by rfl) ⟨3097151, by rfl⟩ : syracuseStep 4129535 = 6194303) B6194303
theorem B1451039 : Blo 1449544 1451039 := bstep (se 1 (by rfl) ⟨1088279, by rfl⟩ : syracuseStep 1451039 = 2176559) B2176559
theorem B154789181 : Blo 1449544 154789181 := bstep (se 3 (by rfl) ⟨29022971, by rfl⟩ : syracuseStep 154789181 = 58045943) B58045943
theorem B1451423 : Blo 1449544 1451423 := bstep (se 1 (by rfl) ⟨1088567, by rfl⟩ : syracuseStep 1451423 = 2177135) B2177135
theorem B3671527 : Blo 1449544 3671527 := bstep (se 1 (by rfl) ⟨2753645, by rfl⟩ : syracuseStep 3671527 = 5507291) B5507291
theorem B56542697 : Blo 1449544 56542697 := bstep (se 2 (by rfl) ⟨21203511, by rfl⟩ : syracuseStep 56542697 = 42407023) B42407023
theorem B1836523 : Blo 1449544 1836523 := bstep (se 1 (by rfl) ⟨1377392, by rfl⟩ : syracuseStep 1836523 = 2754785) B2754785
theorem B3262121 : Blo 1449544 3262121 := bstep (se 2 (by rfl) ⟨1223295, by rfl⟩ : syracuseStep 3262121 = 2446591) B2446591
theorem B1631983 : Blo 1449544 1631983 := bstep (se 1 (by rfl) ⟨1223987, by rfl⟩ : syracuseStep 1631983 = 2447975) B2447975
theorem B6703003 : Blo 1449544 6703003 := bstep (se 1 (by rfl) ⟨5027252, by rfl⟩ : syracuseStep 6703003 = 10054505) B10054505
theorem B3098587 : Blo 1449544 3098587 := bstep (se 1 (by rfl) ⟨2323940, by rfl⟩ : syracuseStep 3098587 = 4647881) B4647881
theorem B2206159 : Blo 1449544 2206159 := bstep (se 1 (by rfl) ⟨1654619, by rfl⟩ : syracuseStep 2206159 = 3309239) B3309239
theorem B3263183 : Blo 1449544 3263183 := bstep (se 1 (by rfl) ⟨2447387, by rfl⟩ : syracuseStep 3263183 = 4894775) B4894775
theorem B3263399 : Blo 1449544 3263399 := bstep (se 1 (by rfl) ⟨2447549, by rfl⟩ : syracuseStep 3263399 = 4895099) B4895099
theorem B3263471 : Blo 1449544 3263471 := bstep (se 1 (by rfl) ⟨2447603, by rfl⟩ : syracuseStep 3263471 = 4895207) B4895207
theorem B6040585 : Blo 1449544 6040585 := bstep (se 2 (by rfl) ⟨2265219, by rfl⟩ : syracuseStep 6040585 = 4530439) B4530439
theorem B7343135 : Blo 1449544 7343135 := bstep (se 1 (by rfl) ⟨5507351, by rfl⟩ : syracuseStep 7343135 = 11014703) B11014703
theorem B3263561 : Blo 1449544 3263561 := bstep (se 2 (by rfl) ⟨1223835, by rfl⟩ : syracuseStep 3263561 = 2447671) B2447671
theorem B5508233 : Blo 1449544 5508233 := bstep (se 2 (by rfl) ⟨2065587, by rfl⟩ : syracuseStep 5508233 = 4131175) B4131175
theorem B12389597 : Blo 1449544 12389597 := bstep (se 3 (by rfl) ⟨2323049, by rfl⟩ : syracuseStep 12389597 = 4646099) B4646099
theorem B24800579 : Blo 1449544 24800579 := bstep (se 1 (by rfl) ⟨18600434, by rfl⟩ : syracuseStep 24800579 = 37200869) B37200869
theorem B3264047 : Blo 1449544 3264047 := bstep (se 1 (by rfl) ⟨2448035, by rfl⟩ : syracuseStep 3264047 = 4896071) B4896071
theorem B3264155 : Blo 1449544 3264155 := bstep (se 1 (by rfl) ⟨2448116, by rfl⟩ : syracuseStep 3264155 = 4896233) B4896233
theorem B7343783 : Blo 1449544 7343783 := bstep (se 1 (by rfl) ⟨5507837, by rfl⟩ : syracuseStep 7343783 = 11015675) B11015675
theorem B2174729 : Blo 1449544 2174729 := bstep (se 2 (by rfl) ⟨815523, by rfl⟩ : syracuseStep 2174729 = 1631047) B1631047
theorem B2175071 : Blo 1449544 2175071 := bstep (se 1 (by rfl) ⟨1631303, by rfl⟩ : syracuseStep 2175071 = 3262607) B3262607
theorem B10457209 : Blo 1449544 10457209 := bstep (se 2 (by rfl) ⟨3921453, by rfl⟩ : syracuseStep 10457209 = 7842907) B7842907
theorem B9924761 : Blo 1449544 9924761 := bstep (se 2 (by rfl) ⟨3721785, by rfl⟩ : syracuseStep 9924761 = 7443571) B7443571
theorem B2175143 : Blo 1449544 2175143 := bstep (se 1 (by rfl) ⟨1631357, by rfl⟩ : syracuseStep 2175143 = 3262715) B3262715
theorem B2175167 : Blo 1449544 2175167 := bstep (se 1 (by rfl) ⟨1631375, by rfl⟩ : syracuseStep 2175167 = 3262751) B3262751
theorem B20918519 : Blo 1449544 20918519 := bstep (se 1 (by rfl) ⟨15688889, by rfl⟩ : syracuseStep 20918519 = 31377779) B31377779
theorem B9425627 : Blo 1449544 9425627 := bstep (se 1 (by rfl) ⟨7069220, by rfl⟩ : syracuseStep 9425627 = 14138441) B14138441
theorem B3265289 : Blo 1449544 3265289 := bstep (se 2 (by rfl) ⟨1224483, by rfl⟩ : syracuseStep 3265289 = 2448967) B2448967
theorem B12399743 : Blo 1449544 12399743 := bstep (se 1 (by rfl) ⟨9299807, by rfl⟩ : syracuseStep 12399743 = 18599615) B18599615
theorem B7345403 : Blo 1449544 7345403 := bstep (se 1 (by rfl) ⟨5509052, by rfl⟩ : syracuseStep 7345403 = 11018105) B11018105
theorem B8263079 : Blo 1449544 8263079 := bstep (se 1 (by rfl) ⟨6197309, by rfl⟩ : syracuseStep 8263079 = 12394619) B12394619
theorem B16111037 : Blo 1449544 16111037 := bstep (se 3 (by rfl) ⟨3020819, by rfl⟩ : syracuseStep 16111037 = 6041639) B6041639
theorem B2176649 : Blo 1449544 2176649 := bstep (se 2 (by rfl) ⟨816243, by rfl⟩ : syracuseStep 2176649 = 1632487) B1632487
theorem B23517053 : Blo 1449544 23517053 := bstep (se 3 (by rfl) ⟨4409447, by rfl⟩ : syracuseStep 23517053 = 8818895) B8818895
theorem B2176895 : Blo 1449544 2176895 := bstep (se 1 (by rfl) ⟨1632671, by rfl⟩ : syracuseStep 2176895 = 3265343) B3265343
theorem B7338599 : Blo 1449544 7338599 := bstep (se 1 (by rfl) ⟨5503949, by rfl⟩ : syracuseStep 7338599 = 11007899) B11007899
theorem B9288431 : Blo 1449544 9288431 := bstep (se 1 (by rfl) ⟨6966323, by rfl⟩ : syracuseStep 9288431 = 13932647) B13932647
theorem B10451879 : Blo 1449544 10451879 := bstep (se 1 (by rfl) ⟨7838909, by rfl⟩ : syracuseStep 10451879 = 15677819) B15677819
theorem B11009357 : Blo 1449544 11009357 := bstep (se 3 (by rfl) ⟨2064254, by rfl⟩ : syracuseStep 11009357 = 4128509) B4128509
theorem B2612891 : Blo 1449544 2612891 := bstep (se 1 (by rfl) ⟨1959668, by rfl⟩ : syracuseStep 2612891 = 3919337) B3919337
theorem B15679241 : Blo 1449544 15679241 := bstep (se 2 (by rfl) ⟨5879715, by rfl⟩ : syracuseStep 15679241 = 11759431) B11759431
theorem B1450047 : Blo 1449544 1450047 := bstep (se 1 (by rfl) ⟨1087535, by rfl⟩ : syracuseStep 1450047 = 2175071) B2175071
theorem B1450095 : Blo 1449544 1450095 := bstep (se 1 (by rfl) ⟨1087571, by rfl⟩ : syracuseStep 1450095 = 2175143) B2175143
theorem B1450111 : Blo 1449544 1450111 := bstep (se 1 (by rfl) ⟨1087583, by rfl⟩ : syracuseStep 1450111 = 2175167) B2175167
theorem B13942945 : Blo 1449544 13942945 := bstep (se 2 (by rfl) ⟨5228604, by rfl⟩ : syracuseStep 13942945 = 10457209) B10457209
theorem B6283751 : Blo 1449544 6283751 := bstep (se 1 (by rfl) ⟨4712813, by rfl⟩ : syracuseStep 6283751 = 9425627) B9425627
theorem B2753023 : Blo 1449544 2753023 := bstep (se 1 (by rfl) ⟨2064767, by rfl⟩ : syracuseStep 2753023 = 4129535) B4129535
theorem B8266495 : Blo 1449544 8266495 := bstep (se 1 (by rfl) ⟨6199871, by rfl⟩ : syracuseStep 8266495 = 12399743) B12399743
theorem B10740691 : Blo 1449544 10740691 := bstep (se 1 (by rfl) ⟨8055518, by rfl⟩ : syracuseStep 10740691 = 16111037) B16111037
theorem B1451099 : Blo 1449544 1451099 := bstep (se 1 (by rfl) ⟨1088324, by rfl⟩ : syracuseStep 1451099 = 2176649) B2176649
theorem B1451263 : Blo 1449544 1451263 := bstep (se 1 (by rfl) ⟨1088447, by rfl⟩ : syracuseStep 1451263 = 2176895) B2176895
theorem B42993077 : Blo 1449544 42993077 := bstep (se 5 (by rfl) ⟨2015300, by rfl⟩ : syracuseStep 42993077 = 4030601) B4030601
theorem B4892399 : Blo 1449544 4892399 := bstep (se 1 (by rfl) ⟨3669299, by rfl⟩ : syracuseStep 4892399 = 7338599) B7338599
theorem B5506973 : Blo 1449544 5506973 := bstep (se 3 (by rfl) ⟨1032557, by rfl⟩ : syracuseStep 5506973 = 2065115) B2065115
theorem B3672155 : Blo 1449544 3672155 := bstep (se 1 (by rfl) ⟨2754116, by rfl⟩ : syracuseStep 3672155 = 5508233) B5508233
theorem B8259731 : Blo 1449544 8259731 := bstep (se 1 (by rfl) ⟨6194798, by rfl⟩ : syracuseStep 8259731 = 12389597) B12389597
theorem B16533719 : Blo 1449544 16533719 := bstep (se 1 (by rfl) ⟨12400289, by rfl⟩ : syracuseStep 16533719 = 24800579) B24800579
theorem B11766181 : Blo 1449544 11766181 := bstep (se 4 (by rfl) ⟨1103079, by rfl⟩ : syracuseStep 11766181 = 2206159) B2206159
theorem B4131449 : Blo 1449544 4131449 := bstep (se 2 (by rfl) ⟨1549293, by rfl⟩ : syracuseStep 4131449 = 3098587) B3098587
theorem B13945679 : Blo 1449544 13945679 := bstep (se 1 (by rfl) ⟨10459259, by rfl⟩ : syracuseStep 13945679 = 20918519) B20918519
theorem B1787522023 : Blo 1449544 1787522023 := bstep (se 1 (by rfl) ⟨1340641517, by rfl⟩ : syracuseStep 1787522023 = 2681283035) B2681283035
theorem B5508719 : Blo 1449544 5508719 := bstep (se 1 (by rfl) ⟨4131539, by rfl⟩ : syracuseStep 5508719 = 8263079) B8263079
theorem B37695131 : Blo 1449544 37695131 := bstep (se 1 (by rfl) ⟨28271348, by rfl⟩ : syracuseStep 37695131 = 56542697) B56542697
theorem B2174747 : Blo 1449544 2174747 := bstep (se 1 (by rfl) ⟨1631060, by rfl⟩ : syracuseStep 2174747 = 3262121) B3262121
theorem B2175455 : Blo 1449544 2175455 := bstep (se 1 (by rfl) ⟨1631591, by rfl⟩ : syracuseStep 2175455 = 3263183) B3263183
theorem B6967919 : Blo 1449544 6967919 := bstep (se 1 (by rfl) ⟨5225939, by rfl⟩ : syracuseStep 6967919 = 10451879) B10451879
theorem B2175599 : Blo 1449544 2175599 := bstep (se 1 (by rfl) ⟨1631699, by rfl⟩ : syracuseStep 2175599 = 3263399) B3263399
theorem B4895369 : Blo 1449544 4895369 := bstep (se 2 (by rfl) ⟨1835763, by rfl⟩ : syracuseStep 4895369 = 3671527) B3671527
theorem B2175647 : Blo 1449544 2175647 := bstep (se 1 (by rfl) ⟨1631735, by rfl⟩ : syracuseStep 2175647 = 3263471) B3263471
theorem B4895423 : Blo 1449544 4895423 := bstep (se 1 (by rfl) ⟨3671567, by rfl⟩ : syracuseStep 4895423 = 7343135) B7343135
theorem B2175707 : Blo 1449544 2175707 := bstep (se 1 (by rfl) ⟨1631780, by rfl⟩ : syracuseStep 2175707 = 3263561) B3263561
theorem B2175977 : Blo 1449544 2175977 := bstep (se 2 (by rfl) ⟨815991, by rfl⟩ : syracuseStep 2175977 = 1631983) B1631983
theorem B2176031 : Blo 1449544 2176031 := bstep (se 1 (by rfl) ⟨1632023, by rfl⟩ : syracuseStep 2176031 = 3264047) B3264047
theorem B1741927 : Blo 1449544 1741927 := bstep (se 1 (by rfl) ⟨1306445, by rfl⟩ : syracuseStep 1741927 = 2612891) B2612891
theorem B2176103 : Blo 1449544 2176103 := bstep (se 1 (by rfl) ⟨1632077, by rfl⟩ : syracuseStep 2176103 = 3264155) B3264155
theorem B4895855 : Blo 1449544 4895855 := bstep (se 1 (by rfl) ⟨3671891, by rfl⟩ : syracuseStep 4895855 = 7343783) B7343783
theorem B32216453 : Blo 1449544 32216453 := bstep (se 4 (by rfl) ⟨3020292, by rfl⟩ : syracuseStep 32216453 = 6040585) B6040585
theorem B6616507 : Blo 1449544 6616507 := bstep (se 1 (by rfl) ⟨4962380, by rfl⟩ : syracuseStep 6616507 = 9924761) B9924761
theorem B2176859 : Blo 1449544 2176859 := bstep (se 1 (by rfl) ⟨1632644, by rfl⟩ : syracuseStep 2176859 = 3265289) B3265289
theorem B4896935 : Blo 1449544 4896935 := bstep (se 1 (by rfl) ⟨3672701, by rfl⟩ : syracuseStep 4896935 = 7345403) B7345403
theorem B103192787 : Blo 1449544 103192787 := bstep (se 1 (by rfl) ⟨77394590, by rfl⟩ : syracuseStep 103192787 = 154789181) B154789181
theorem B15678035 : Blo 1449544 15678035 := bstep (se 1 (by rfl) ⟨11758526, by rfl⟩ : syracuseStep 15678035 = 23517053) B23517053
theorem B6192287 : Blo 1449544 6192287 := bstep (se 1 (by rfl) ⟨4644215, by rfl⟩ : syracuseStep 6192287 = 9288431) B9288431
theorem B2448697 : Blo 1449544 2448697 := bstep (se 2 (by rfl) ⟨918261, by rfl⟩ : syracuseStep 2448697 = 1836523) B1836523
theorem B35749349 : Blo 1449544 35749349 := bstep (se 4 (by rfl) ⟨3351501, by rfl⟩ : syracuseStep 35749349 = 6703003) B6703003
theorem B7339571 : Blo 1449544 7339571 := bstep (se 1 (by rfl) ⟨5504678, by rfl⟩ : syracuseStep 7339571 = 11009357) B11009357
theorem B1449819 : Blo 1449544 1449819 := bstep (se 1 (by rfl) ⟨1087364, by rfl⟩ : syracuseStep 1449819 = 2174729) B2174729
theorem B10452827 : Blo 1449544 10452827 := bstep (se 1 (by rfl) ⟨7839620, by rfl⟩ : syracuseStep 10452827 = 15679241) B15679241
theorem B1450303 : Blo 1449544 1450303 := bstep (se 1 (by rfl) ⟨1087727, by rfl⟩ : syracuseStep 1450303 = 2175455) B2175455
theorem B4645279 : Blo 1449544 4645279 := bstep (se 1 (by rfl) ⟨3483959, by rfl⟩ : syracuseStep 4645279 = 6967919) B6967919
theorem B1450399 : Blo 1449544 1450399 := bstep (se 1 (by rfl) ⟨1087799, by rfl⟩ : syracuseStep 1450399 = 2175599) B2175599
theorem B1450431 : Blo 1449544 1450431 := bstep (se 1 (by rfl) ⟨1087823, by rfl⟩ : syracuseStep 1450431 = 2175647) B2175647
theorem B1450471 : Blo 1449544 1450471 := bstep (se 1 (by rfl) ⟨1087853, by rfl⟩ : syracuseStep 1450471 = 2175707) B2175707
theorem B15688241 : Blo 1449544 15688241 := bstep (se 2 (by rfl) ⟨5883090, by rfl⟩ : syracuseStep 15688241 = 11766181) B11766181
theorem B1450651 : Blo 1449544 1450651 := bstep (se 1 (by rfl) ⟨1087988, by rfl⟩ : syracuseStep 1450651 = 2175977) B2175977
theorem B3670697 : Blo 1449544 3670697 := bstep (se 2 (by rfl) ⟨1376511, by rfl⟩ : syracuseStep 3670697 = 2753023) B2753023
theorem B1450687 : Blo 1449544 1450687 := bstep (se 1 (by rfl) ⟨1088015, by rfl⟩ : syracuseStep 1450687 = 2176031) B2176031
theorem B1450735 : Blo 1449544 1450735 := bstep (se 1 (by rfl) ⟨1088051, by rfl⟩ : syracuseStep 1450735 = 2176103) B2176103
theorem B114648205 : Blo 1449544 114648205 := bstep (se 3 (by rfl) ⟨21496538, by rfl⟩ : syracuseStep 114648205 = 42993077) B42993077
theorem B3261599 : Blo 1449544 3261599 := bstep (se 1 (by rfl) ⟨2446199, by rfl⟩ : syracuseStep 3261599 = 4892399) B4892399
theorem B1451239 : Blo 1449544 1451239 := bstep (se 1 (by rfl) ⟨1088429, by rfl⟩ : syracuseStep 1451239 = 2176859) B2176859
theorem B3671315 : Blo 1449544 3671315 := bstep (se 1 (by rfl) ⟨2753486, by rfl⟩ : syracuseStep 3671315 = 5506973) B5506973
theorem B14320921 : Blo 1449544 14320921 := bstep (se 2 (by rfl) ⟨5370345, by rfl⟩ : syracuseStep 14320921 = 10740691) B10740691
theorem B5506487 : Blo 1449544 5506487 := bstep (se 1 (by rfl) ⟨4129865, by rfl⟩ : syracuseStep 5506487 = 8259731) B8259731
theorem B2754299 : Blo 1449544 2754299 := bstep (se 1 (by rfl) ⟨2065724, by rfl⟩ : syracuseStep 2754299 = 4131449) B4131449
theorem B23832899 : Blo 1449544 23832899 := bstep (se 1 (by rfl) ⟨17874674, by rfl⟩ : syracuseStep 23832899 = 35749349) B35749349
theorem B4893047 : Blo 1449544 4893047 := bstep (se 1 (by rfl) ⟨3669785, by rfl⟩ : syracuseStep 4893047 = 7339571) B7339571
theorem B3672479 : Blo 1449544 3672479 := bstep (se 1 (by rfl) ⟨2754359, by rfl⟩ : syracuseStep 3672479 = 5508719) B5508719
theorem B9533450789 : Blo 1449544 9533450789 := bstep (se 4 (by rfl) ⟨893761011, by rfl⟩ : syracuseStep 9533450789 = 1787522023) B1787522023
theorem B18590593 : Blo 1449544 18590593 := bstep (se 2 (by rfl) ⟨6971472, by rfl⟩ : syracuseStep 18590593 = 13942945) B13942945
theorem B3263579 : Blo 1449544 3263579 := bstep (se 1 (by rfl) ⟨2447684, by rfl⟩ : syracuseStep 3263579 = 4895369) B4895369
theorem B3263615 : Blo 1449544 3263615 := bstep (se 1 (by rfl) ⟨2447711, by rfl⟩ : syracuseStep 3263615 = 4895423) B4895423
theorem B3263903 : Blo 1449544 3263903 := bstep (se 1 (by rfl) ⟨2447927, by rfl⟩ : syracuseStep 3263903 = 4895855) B4895855
theorem B11021993 : Blo 1449544 11021993 := bstep (se 2 (by rfl) ⟨4133247, by rfl⟩ : syracuseStep 11021993 = 8266495) B8266495
theorem B16756669 : Blo 1449544 16756669 := bstep (se 3 (by rfl) ⟨3141875, by rfl⟩ : syracuseStep 16756669 = 6283751) B6283751
theorem B3264623 : Blo 1449544 3264623 := bstep (se 1 (by rfl) ⟨2448467, by rfl⟩ : syracuseStep 3264623 = 4896935) B4896935
theorem B2322569 : Blo 1449544 2322569 := bstep (se 2 (by rfl) ⟨870963, by rfl⟩ : syracuseStep 2322569 = 1741927) B1741927
theorem B11022479 : Blo 1449544 11022479 := bstep (se 1 (by rfl) ⟨8266859, by rfl⟩ : syracuseStep 11022479 = 16533719) B16533719
theorem B3264929 : Blo 1449544 3264929 := bstep (se 2 (by rfl) ⟨1224348, by rfl⟩ : syracuseStep 3264929 = 2448697) B2448697
theorem B27874205 : Blo 1449544 27874205 := bstep (se 3 (by rfl) ⟨5226413, by rfl⟩ : syracuseStep 27874205 = 10452827) B10452827
theorem B25130087 : Blo 1449544 25130087 := bstep (se 1 (by rfl) ⟨18847565, by rfl⟩ : syracuseStep 25130087 = 37695131) B37695131
theorem B21477635 : Blo 1449544 21477635 := bstep (se 1 (by rfl) ⟨16108226, by rfl⟩ : syracuseStep 21477635 = 32216453) B32216453
theorem B2448103 : Blo 1449544 2448103 := bstep (se 1 (by rfl) ⟨1836077, by rfl⟩ : syracuseStep 2448103 = 3672155) B3672155
theorem B68795191 : Blo 1449544 68795191 := bstep (se 1 (by rfl) ⟨51596393, by rfl⟩ : syracuseStep 68795191 = 103192787) B103192787
theorem B10452023 : Blo 1449544 10452023 := bstep (se 1 (by rfl) ⟨7839017, by rfl⟩ : syracuseStep 10452023 = 15678035) B15678035
theorem B9297119 : Blo 1449544 9297119 := bstep (se 1 (by rfl) ⟨6972839, by rfl⟩ : syracuseStep 9297119 = 13945679) B13945679
theorem B8822009 : Blo 1449544 8822009 := bstep (se 2 (by rfl) ⟨3308253, by rfl⟩ : syracuseStep 8822009 = 6616507) B6616507
theorem B4128191 : Blo 1449544 4128191 := bstep (se 1 (by rfl) ⟨3096143, by rfl⟩ : syracuseStep 4128191 = 6192287) B6192287
theorem B1449831 : Blo 1449544 1449831 := bstep (se 1 (by rfl) ⟨1087373, by rfl⟩ : syracuseStep 1449831 = 2174747) B2174747
theorem B1548379 : Blo 1449544 1548379 := bstep (se 1 (by rfl) ⟨1161284, by rfl⟩ : syracuseStep 1548379 = 2322569) B2322569
theorem B7348319 : Blo 1449544 7348319 := bstep (se 1 (by rfl) ⟨5511239, by rfl⟩ : syracuseStep 7348319 = 11022479) B11022479
theorem B6193705 : Blo 1449544 6193705 := bstep (se 2 (by rfl) ⟨2322639, by rfl⟩ : syracuseStep 6193705 = 4645279) B4645279
theorem B16753391 : Blo 1449544 16753391 := bstep (se 1 (by rfl) ⟨12565043, by rfl⟩ : syracuseStep 16753391 = 25130087) B25130087
theorem B3670991 : Blo 1449544 3670991 := bstep (se 1 (by rfl) ⟨2753243, by rfl⟩ : syracuseStep 3670991 = 5506487) B5506487
theorem B91726921 : Blo 1449544 91726921 := bstep (se 2 (by rfl) ⟨34397595, by rfl⟩ : syracuseStep 91726921 = 68795191) B68795191
theorem B1836199 : Blo 1449544 1836199 := bstep (se 1 (by rfl) ⟨1377149, by rfl⟩ : syracuseStep 1836199 = 2754299) B2754299
theorem B152864273 : Blo 1449544 152864273 := bstep (se 2 (by rfl) ⟨57324102, by rfl⟩ : syracuseStep 152864273 = 114648205) B114648205
theorem B3262031 : Blo 1449544 3262031 := bstep (se 1 (by rfl) ⟨2446523, by rfl⟩ : syracuseStep 3262031 = 4893047) B4893047
theorem B6355633859 : Blo 1449544 6355633859 := bstep (se 1 (by rfl) ⟨4766725394, by rfl⟩ : syracuseStep 6355633859 = 9533450789) B9533450789
theorem B22342225 : Blo 1449544 22342225 := bstep (se 2 (by rfl) ⟨8378334, by rfl⟩ : syracuseStep 22342225 = 16756669) B16756669
theorem B18582803 : Blo 1449544 18582803 := bstep (se 1 (by rfl) ⟨13937102, by rfl⟩ : syracuseStep 18582803 = 27874205) B27874205
theorem B2174399 : Blo 1449544 2174399 := bstep (se 1 (by rfl) ⟨1630799, by rfl⟩ : syracuseStep 2174399 = 3261599) B3261599
theorem B3264137 : Blo 1449544 3264137 := bstep (se 2 (by rfl) ⟨1224051, by rfl⟩ : syracuseStep 3264137 = 2448103) B2448103
theorem B15888599 : Blo 1449544 15888599 := bstep (se 1 (by rfl) ⟨11916449, by rfl⟩ : syracuseStep 15888599 = 23832899) B23832899
theorem B6968015 : Blo 1449544 6968015 := bstep (se 1 (by rfl) ⟨5226011, by rfl⟩ : syracuseStep 6968015 = 10452023) B10452023
theorem B2175719 : Blo 1449544 2175719 := bstep (se 1 (by rfl) ⟨1631789, by rfl⟩ : syracuseStep 2175719 = 3263579) B3263579
theorem B2175743 : Blo 1449544 2175743 := bstep (se 1 (by rfl) ⟨1631807, by rfl⟩ : syracuseStep 2175743 = 3263615) B3263615
theorem B6198079 : Blo 1449544 6198079 := bstep (se 1 (by rfl) ⟨4648559, by rfl⟩ : syracuseStep 6198079 = 9297119) B9297119
theorem B2175935 : Blo 1449544 2175935 := bstep (se 1 (by rfl) ⟨1631951, by rfl⟩ : syracuseStep 2175935 = 3263903) B3263903
theorem B2176415 : Blo 1449544 2176415 := bstep (se 1 (by rfl) ⟨1632311, by rfl⟩ : syracuseStep 2176415 = 3264623) B3264623
theorem B2176619 : Blo 1449544 2176619 := bstep (se 1 (by rfl) ⟨1632464, by rfl⟩ : syracuseStep 2176619 = 3264929) B3264929
theorem B10458827 : Blo 1449544 10458827 := bstep (se 1 (by rfl) ⟨7844120, by rfl⟩ : syracuseStep 10458827 = 15688241) B15688241
theorem B2447131 : Blo 1449544 2447131 := bstep (se 1 (by rfl) ⟨1835348, by rfl⟩ : syracuseStep 2447131 = 3670697) B3670697
theorem B2447543 : Blo 1449544 2447543 := bstep (se 1 (by rfl) ⟨1835657, by rfl⟩ : syracuseStep 2447543 = 3671315) B3671315
theorem B24787457 : Blo 1449544 24787457 := bstep (se 2 (by rfl) ⟨9295296, by rfl⟩ : syracuseStep 24787457 = 18590593) B18590593
theorem B14318423 : Blo 1449544 14318423 := bstep (se 1 (by rfl) ⟨10738817, by rfl⟩ : syracuseStep 14318423 = 21477635) B21477635
theorem B2448319 : Blo 1449544 2448319 := bstep (se 1 (by rfl) ⟨1836239, by rfl⟩ : syracuseStep 2448319 = 3672479) B3672479
theorem B19094561 : Blo 1449544 19094561 := bstep (se 2 (by rfl) ⟨7160460, by rfl⟩ : syracuseStep 19094561 = 14320921) B14320921
theorem B5881339 : Blo 1449544 5881339 := bstep (se 1 (by rfl) ⟨4411004, by rfl⟩ : syracuseStep 5881339 = 8822009) B8822009
theorem B2752127 : Blo 1449544 2752127 := bstep (se 1 (by rfl) ⟨2064095, by rfl⟩ : syracuseStep 2752127 = 4128191) B4128191
theorem B7347995 : Blo 1449544 7347995 := bstep (se 1 (by rfl) ⟨5510996, by rfl⟩ : syracuseStep 7347995 = 11021993) B11021993
theorem B4898879 : Blo 1449544 4898879 := bstep (se 1 (by rfl) ⟨3674159, by rfl⟩ : syracuseStep 4898879 = 7348319) B7348319
theorem B10592399 : Blo 1449544 10592399 := bstep (se 1 (by rfl) ⟨7944299, by rfl⟩ : syracuseStep 10592399 = 15888599) B15888599
theorem B4645343 : Blo 1449544 4645343 := bstep (se 1 (by rfl) ⟨3484007, by rfl⟩ : syracuseStep 4645343 = 6968015) B6968015
theorem B8258021 : Blo 1449544 8258021 := bstep (se 4 (by rfl) ⟨774189, by rfl⟩ : syracuseStep 8258021 = 1548379) B1548379
theorem B1450479 : Blo 1449544 1450479 := bstep (se 1 (by rfl) ⟨1087859, by rfl⟩ : syracuseStep 1450479 = 2175719) B2175719
theorem B1450495 : Blo 1449544 1450495 := bstep (se 1 (by rfl) ⟨1087871, by rfl⟩ : syracuseStep 1450495 = 2175743) B2175743
theorem B1450623 : Blo 1449544 1450623 := bstep (se 1 (by rfl) ⟨1087967, by rfl⟩ : syracuseStep 1450623 = 2175935) B2175935
theorem B8258273 : Blo 1449544 8258273 := bstep (se 2 (by rfl) ⟨3096852, by rfl⟩ : syracuseStep 8258273 = 6193705) B6193705
theorem B1450943 : Blo 1449544 1450943 := bstep (se 1 (by rfl) ⟨1088207, by rfl⟩ : syracuseStep 1450943 = 2176415) B2176415
theorem B101909515 : Blo 1449544 101909515 := bstep (se 1 (by rfl) ⟨76432136, by rfl⟩ : syracuseStep 101909515 = 152864273) B152864273
theorem B1451079 : Blo 1449544 1451079 := bstep (se 1 (by rfl) ⟨1088309, by rfl⟩ : syracuseStep 1451079 = 2176619) B2176619
theorem B6972551 : Blo 1449544 6972551 := bstep (se 1 (by rfl) ⟨5229413, by rfl⟩ : syracuseStep 6972551 = 10458827) B10458827
theorem B1631695 : Blo 1449544 1631695 := bstep (se 1 (by rfl) ⟨1223771, by rfl⟩ : syracuseStep 1631695 = 2447543) B2447543
theorem B16524971 : Blo 1449544 16524971 := bstep (se 1 (by rfl) ⟨12393728, by rfl⟩ : syracuseStep 16524971 = 24787457) B24787457
theorem B9545615 : Blo 1449544 9545615 := bstep (se 1 (by rfl) ⟨7159211, by rfl⟩ : syracuseStep 9545615 = 14318423) B14318423
theorem B7841785 : Blo 1449544 7841785 := bstep (se 2 (by rfl) ⟨2940669, by rfl⟩ : syracuseStep 7841785 = 5881339) B5881339
theorem B12388535 : Blo 1449544 12388535 := bstep (se 1 (by rfl) ⟨9291401, by rfl⟩ : syracuseStep 12388535 = 18582803) B18582803
theorem B3262841 : Blo 1449544 3262841 := bstep (se 2 (by rfl) ⟨1223565, by rfl⟩ : syracuseStep 3262841 = 2447131) B2447131
theorem B11168927 : Blo 1449544 11168927 := bstep (se 1 (by rfl) ⟨8376695, by rfl⟩ : syracuseStep 11168927 = 16753391) B16753391
theorem B29789633 : Blo 1449544 29789633 := bstep (se 2 (by rfl) ⟨11171112, by rfl⟩ : syracuseStep 29789633 = 22342225) B22342225
theorem B2174687 : Blo 1449544 2174687 := bstep (se 1 (by rfl) ⟨1631015, by rfl⟩ : syracuseStep 2174687 = 3262031) B3262031
theorem B3264425 : Blo 1449544 3264425 := bstep (se 2 (by rfl) ⟨1224159, by rfl⟩ : syracuseStep 3264425 = 2448319) B2448319
theorem B122302561 : Blo 1449544 122302561 := bstep (se 2 (by rfl) ⟨45863460, by rfl⟩ : syracuseStep 122302561 = 91726921) B91726921
theorem B2176091 : Blo 1449544 2176091 := bstep (se 1 (by rfl) ⟨1632068, by rfl⟩ : syracuseStep 2176091 = 3264137) B3264137
theorem B2447327 : Blo 1449544 2447327 := bstep (se 1 (by rfl) ⟨1835495, by rfl⟩ : syracuseStep 2447327 = 3670991) B3670991
theorem B8264105 : Blo 1449544 8264105 := bstep (se 2 (by rfl) ⟨3099039, by rfl⟩ : syracuseStep 8264105 = 6198079) B6198079
theorem B4237089239 : Blo 1449544 4237089239 := bstep (se 1 (by rfl) ⟨3177816929, by rfl⟩ : syracuseStep 4237089239 = 6355633859) B6355633859
theorem B2448265 : Blo 1449544 2448265 := bstep (se 2 (by rfl) ⟨918099, by rfl⟩ : syracuseStep 2448265 = 1836199) B1836199
theorem B12729707 : Blo 1449544 12729707 := bstep (se 1 (by rfl) ⟨9547280, by rfl⟩ : syracuseStep 12729707 = 19094561) B19094561
theorem B1449599 : Blo 1449544 1449599 := bstep (se 1 (by rfl) ⟨1087199, by rfl⟩ : syracuseStep 1449599 = 2174399) B2174399
theorem B1834751 : Blo 1449544 1834751 := bstep (se 1 (by rfl) ⟨1376063, by rfl⟩ : syracuseStep 1834751 = 2752127) B2752127
theorem B4898663 : Blo 1449544 4898663 := bstep (se 1 (by rfl) ⟨3673997, by rfl⟩ : syracuseStep 4898663 = 7347995) B7347995
theorem B7061599 : Blo 1449544 7061599 := bstep (se 1 (by rfl) ⟨5296199, by rfl⟩ : syracuseStep 7061599 = 10592399) B10592399
theorem B163070081 : Blo 1449544 163070081 := bstep (se 2 (by rfl) ⟨61151280, by rfl⟩ : syracuseStep 163070081 = 122302561) B122302561
theorem B3096895 : Blo 1449544 3096895 := bstep (se 1 (by rfl) ⟨2322671, by rfl⟩ : syracuseStep 3096895 = 4645343) B4645343
theorem B5505347 : Blo 1449544 5505347 := bstep (se 1 (by rfl) ⟨4129010, by rfl⟩ : syracuseStep 5505347 = 8258021) B8258021
theorem B5505515 : Blo 1449544 5505515 := bstep (se 1 (by rfl) ⟨4129136, by rfl⟩ : syracuseStep 5505515 = 8258273) B8258273
theorem B1450727 : Blo 1449544 1450727 := bstep (se 1 (by rfl) ⟨1088045, by rfl⟩ : syracuseStep 1450727 = 2176091) B2176091
theorem B1631551 : Blo 1449544 1631551 := bstep (se 1 (by rfl) ⟨1223663, by rfl⟩ : syracuseStep 1631551 = 2447327) B2447327
theorem B8259023 : Blo 1449544 8259023 := bstep (se 1 (by rfl) ⟨6194267, by rfl⟩ : syracuseStep 8259023 = 12388535) B12388535
theorem B2824726159 : Blo 1449544 2824726159 := bstep (se 1 (by rfl) ⟨2118544619, by rfl⟩ : syracuseStep 2824726159 = 4237089239) B4237089239
theorem B4892669 : Blo 1449544 4892669 := bstep (se 3 (by rfl) ⟨917375, by rfl⟩ : syracuseStep 4892669 = 1834751) B1834751
theorem B19859755 : Blo 1449544 19859755 := bstep (se 1 (by rfl) ⟨14894816, by rfl⟩ : syracuseStep 19859755 = 29789633) B29789633
theorem B10455713 : Blo 1449544 10455713 := bstep (se 2 (by rfl) ⟨3920892, by rfl⟩ : syracuseStep 10455713 = 7841785) B7841785
theorem B4648367 : Blo 1449544 4648367 := bstep (se 1 (by rfl) ⟨3486275, by rfl⟩ : syracuseStep 4648367 = 6972551) B6972551
theorem B3264353 : Blo 1449544 3264353 := bstep (se 2 (by rfl) ⟨1224132, by rfl⟩ : syracuseStep 3264353 = 2448265) B2448265
theorem B2175227 : Blo 1449544 2175227 := bstep (se 1 (by rfl) ⟨1631420, by rfl⟩ : syracuseStep 2175227 = 3262841) B3262841
theorem B5509403 : Blo 1449544 5509403 := bstep (se 1 (by rfl) ⟨4132052, by rfl⟩ : syracuseStep 5509403 = 8264105) B8264105
theorem B2175593 : Blo 1449544 2175593 := bstep (se 2 (by rfl) ⟨815847, by rfl⟩ : syracuseStep 2175593 = 1631695) B1631695
theorem B3265775 : Blo 1449544 3265775 := bstep (se 1 (by rfl) ⟨2449331, by rfl⟩ : syracuseStep 3265775 = 4898663) B4898663
theorem B2176283 : Blo 1449544 2176283 := bstep (se 1 (by rfl) ⟨1632212, by rfl⟩ : syracuseStep 2176283 = 3264425) B3264425
theorem B3265919 : Blo 1449544 3265919 := bstep (se 1 (by rfl) ⟨2449439, by rfl⟩ : syracuseStep 3265919 = 4898879) B4898879
theorem B11016647 : Blo 1449544 11016647 := bstep (se 1 (by rfl) ⟨8262485, by rfl⟩ : syracuseStep 11016647 = 16524971) B16524971
theorem B6363743 : Blo 1449544 6363743 := bstep (se 1 (by rfl) ⟨4772807, by rfl⟩ : syracuseStep 6363743 = 9545615) B9545615
theorem B135879353 : Blo 1449544 135879353 := bstep (se 2 (by rfl) ⟨50954757, by rfl⟩ : syracuseStep 135879353 = 101909515) B101909515
theorem B7445951 : Blo 1449544 7445951 := bstep (se 1 (by rfl) ⟨5584463, by rfl⟩ : syracuseStep 7445951 = 11168927) B11168927
theorem B8486471 : Blo 1449544 8486471 := bstep (se 1 (by rfl) ⟨6364853, by rfl⟩ : syracuseStep 8486471 = 12729707) B12729707
theorem B1449791 : Blo 1449544 1449791 := bstep (se 1 (by rfl) ⟨1087343, by rfl⟩ : syracuseStep 1449791 = 2174687) B2174687
theorem B1450151 : Blo 1449544 1450151 := bstep (se 1 (by rfl) ⟨1087613, by rfl⟩ : syracuseStep 1450151 = 2175227) B2175227
theorem B3670231 : Blo 1449544 3670231 := bstep (se 1 (by rfl) ⟨2752673, by rfl⟩ : syracuseStep 3670231 = 5505347) B5505347
theorem B3670343 : Blo 1449544 3670343 := bstep (se 1 (by rfl) ⟨2752757, by rfl⟩ : syracuseStep 3670343 = 5505515) B5505515
theorem B1450395 : Blo 1449544 1450395 := bstep (se 1 (by rfl) ⟨1087796, by rfl⟩ : syracuseStep 1450395 = 2175593) B2175593
theorem B4129193 : Blo 1449544 4129193 := bstep (se 2 (by rfl) ⟨1548447, by rfl⟩ : syracuseStep 4129193 = 3096895) B3096895
theorem B1450855 : Blo 1449544 1450855 := bstep (se 1 (by rfl) ⟨1088141, by rfl⟩ : syracuseStep 1450855 = 2176283) B2176283
theorem B5506015 : Blo 1449544 5506015 := bstep (se 1 (by rfl) ⟨4129511, by rfl⟩ : syracuseStep 5506015 = 8259023) B8259023
theorem B3261779 : Blo 1449544 3261779 := bstep (se 1 (by rfl) ⟨2446334, by rfl⟩ : syracuseStep 3261779 = 4892669) B4892669
theorem B3098911 : Blo 1449544 3098911 := bstep (se 1 (by rfl) ⟨2324183, by rfl⟩ : syracuseStep 3098911 = 4648367) B4648367
theorem B3672935 : Blo 1449544 3672935 := bstep (se 1 (by rfl) ⟨2754701, by rfl⟩ : syracuseStep 3672935 = 5509403) B5509403
theorem B26479673 : Blo 1449544 26479673 := bstep (se 2 (by rfl) ⟨9929877, by rfl⟩ : syracuseStep 26479673 = 19859755) B19859755
theorem B37661861 : Blo 1449544 37661861 := bstep (se 4 (by rfl) ⟨3530799, by rfl⟩ : syracuseStep 37661861 = 7061599) B7061599
theorem B16969981 : Blo 1449544 16969981 := bstep (se 3 (by rfl) ⟨3181871, by rfl⟩ : syracuseStep 16969981 = 6363743) B6363743
theorem B7344431 : Blo 1449544 7344431 := bstep (se 1 (by rfl) ⟨5508323, by rfl⟩ : syracuseStep 7344431 = 11016647) B11016647
theorem B2175401 : Blo 1449544 2175401 := bstep (se 2 (by rfl) ⟨815775, by rfl⟩ : syracuseStep 2175401 = 1631551) B1631551
theorem B3766301545 : Blo 1449544 3766301545 := bstep (se 2 (by rfl) ⟨1412363079, by rfl⟩ : syracuseStep 3766301545 = 2824726159) B2824726159
theorem B5657647 : Blo 1449544 5657647 := bstep (se 1 (by rfl) ⟨4243235, by rfl⟩ : syracuseStep 5657647 = 8486471) B8486471
theorem B2176235 : Blo 1449544 2176235 := bstep (se 1 (by rfl) ⟨1632176, by rfl⟩ : syracuseStep 2176235 = 3264353) B3264353
theorem B108713387 : Blo 1449544 108713387 := bstep (se 1 (by rfl) ⟨81535040, by rfl⟩ : syracuseStep 108713387 = 163070081) B163070081
theorem B2177183 : Blo 1449544 2177183 := bstep (se 1 (by rfl) ⟨1632887, by rfl⟩ : syracuseStep 2177183 = 3265775) B3265775
theorem B2177279 : Blo 1449544 2177279 := bstep (se 1 (by rfl) ⟨1632959, by rfl⟩ : syracuseStep 2177279 = 3265919) B3265919
theorem B6970475 : Blo 1449544 6970475 := bstep (se 1 (by rfl) ⟨5227856, by rfl⟩ : syracuseStep 6970475 = 10455713) B10455713
theorem B90586235 : Blo 1449544 90586235 := bstep (se 1 (by rfl) ⟨67939676, by rfl⟩ : syracuseStep 90586235 = 135879353) B135879353
theorem B4963967 : Blo 1449544 4963967 := bstep (se 1 (by rfl) ⟨3722975, by rfl⟩ : syracuseStep 4963967 = 7445951) B7445951
theorem B2752795 : Blo 1449544 2752795 := bstep (se 1 (by rfl) ⟨2064596, by rfl⟩ : syracuseStep 2752795 = 4129193) B4129193
theorem B1450267 : Blo 1449544 1450267 := bstep (se 1 (by rfl) ⟨1087700, by rfl⟩ : syracuseStep 1450267 = 2175401) B2175401
theorem B22626641 : Blo 1449544 22626641 := bstep (se 2 (by rfl) ⟨8484990, by rfl⟩ : syracuseStep 22626641 = 16969981) B16969981
theorem B1450823 : Blo 1449544 1450823 := bstep (se 1 (by rfl) ⟨1088117, by rfl⟩ : syracuseStep 1450823 = 2176235) B2176235
theorem B7341353 : Blo 1449544 7341353 := bstep (se 2 (by rfl) ⟨2753007, by rfl⟩ : syracuseStep 7341353 = 5506015) B5506015
theorem B1451455 : Blo 1449544 1451455 := bstep (se 1 (by rfl) ⟨1088591, by rfl⟩ : syracuseStep 1451455 = 2177183) B2177183
theorem B1451519 : Blo 1449544 1451519 := bstep (se 1 (by rfl) ⟨1088639, by rfl⟩ : syracuseStep 1451519 = 2177279) B2177279
theorem B4646983 : Blo 1449544 4646983 := bstep (se 1 (by rfl) ⟨3485237, by rfl⟩ : syracuseStep 4646983 = 6970475) B6970475
theorem B4893641 : Blo 1449544 4893641 := bstep (se 2 (by rfl) ⟨1835115, by rfl⟩ : syracuseStep 4893641 = 3670231) B3670231
theorem B4131881 : Blo 1449544 4131881 := bstep (se 2 (by rfl) ⟨1549455, by rfl⟩ : syracuseStep 4131881 = 3098911) B3098911
theorem B2174519 : Blo 1449544 2174519 := bstep (se 1 (by rfl) ⟨1630889, by rfl⟩ : syracuseStep 2174519 = 3261779) B3261779
theorem B289902365 : Blo 1449544 289902365 := bstep (se 3 (by rfl) ⟨54356693, by rfl⟩ : syracuseStep 289902365 = 108713387) B108713387
theorem B4896287 : Blo 1449544 4896287 := bstep (se 1 (by rfl) ⟨3672215, by rfl⟩ : syracuseStep 4896287 = 7344431) B7344431
theorem B2446895 : Blo 1449544 2446895 := bstep (se 1 (by rfl) ⟨1835171, by rfl⟩ : syracuseStep 2446895 = 3670343) B3670343
theorem B241563293 : Blo 1449544 241563293 := bstep (se 3 (by rfl) ⟨45293117, by rfl⟩ : syracuseStep 241563293 = 90586235) B90586235
theorem B5021735393 : Blo 1449544 5021735393 := bstep (se 2 (by rfl) ⟨1883150772, by rfl⟩ : syracuseStep 5021735393 = 3766301545) B3766301545
theorem B7543529 : Blo 1449544 7543529 := bstep (se 2 (by rfl) ⟨2828823, by rfl⟩ : syracuseStep 7543529 = 5657647) B5657647
theorem B2448623 : Blo 1449544 2448623 := bstep (se 1 (by rfl) ⟨1836467, by rfl⟩ : syracuseStep 2448623 = 3672935) B3672935
theorem B17653115 : Blo 1449544 17653115 := bstep (se 1 (by rfl) ⟨13239836, by rfl⟩ : syracuseStep 17653115 = 26479673) B26479673
theorem B25107907 : Blo 1449544 25107907 := bstep (se 1 (by rfl) ⟨18830930, by rfl⟩ : syracuseStep 25107907 = 37661861) B37661861
theorem B3309311 : Blo 1449544 3309311 := bstep (se 1 (by rfl) ⟨2481983, by rfl⟩ : syracuseStep 3309311 = 4963967) B4963967
theorem B3670393 : Blo 1449544 3670393 := bstep (se 2 (by rfl) ⟨1376397, by rfl⟩ : syracuseStep 3670393 = 2752795) B2752795
theorem B1631263 : Blo 1449544 1631263 := bstep (se 1 (by rfl) ⟨1223447, by rfl⟩ : syracuseStep 1631263 = 2446895) B2446895
theorem B3262427 : Blo 1449544 3262427 := bstep (se 1 (by rfl) ⟨2446820, by rfl⟩ : syracuseStep 3262427 = 4893641) B4893641
theorem B2754587 : Blo 1449544 2754587 := bstep (se 1 (by rfl) ⟨2065940, by rfl⟩ : syracuseStep 2754587 = 4131881) B4131881
theorem B1632415 : Blo 1449544 1632415 := bstep (se 1 (by rfl) ⟨1224311, by rfl⟩ : syracuseStep 1632415 = 2448623) B2448623
theorem B2206207 : Blo 1449544 2206207 := bstep (se 1 (by rfl) ⟨1654655, by rfl⟩ : syracuseStep 2206207 = 3309311) B3309311
theorem B193268243 : Blo 1449544 193268243 := bstep (se 1 (by rfl) ⟨144951182, by rfl⟩ : syracuseStep 193268243 = 289902365) B289902365
theorem B6195977 : Blo 1449544 6195977 := bstep (se 2 (by rfl) ⟨2323491, by rfl⟩ : syracuseStep 6195977 = 4646983) B4646983
theorem B15084427 : Blo 1449544 15084427 := bstep (se 1 (by rfl) ⟨11313320, by rfl⟩ : syracuseStep 15084427 = 22626641) B22626641
theorem B4894235 : Blo 1449544 4894235 := bstep (se 1 (by rfl) ⟨3670676, by rfl⟩ : syracuseStep 4894235 = 7341353) B7341353
theorem B3264191 : Blo 1449544 3264191 := bstep (se 1 (by rfl) ⟨2448143, by rfl⟩ : syracuseStep 3264191 = 4896287) B4896287
theorem B161042195 : Blo 1449544 161042195 := bstep (se 1 (by rfl) ⟨120781646, by rfl⟩ : syracuseStep 161042195 = 241563293) B241563293
theorem B33477209 : Blo 1449544 33477209 := bstep (se 2 (by rfl) ⟨12553953, by rfl⟩ : syracuseStep 33477209 = 25107907) B25107907
theorem B11768743 : Blo 1449544 11768743 := bstep (se 1 (by rfl) ⟨8826557, by rfl⟩ : syracuseStep 11768743 = 17653115) B17653115
theorem B3347823595 : Blo 1449544 3347823595 := bstep (se 1 (by rfl) ⟨2510867696, by rfl⟩ : syracuseStep 3347823595 = 5021735393) B5021735393
theorem B5029019 : Blo 1449544 5029019 := bstep (se 1 (by rfl) ⟨3771764, by rfl⟩ : syracuseStep 5029019 = 7543529) B7543529
theorem B1449679 : Blo 1449544 1449679 := bstep (se 1 (by rfl) ⟨1087259, by rfl⟩ : syracuseStep 1449679 = 2174519) B2174519
theorem B20112569 : Blo 1449544 20112569 := bstep (se 2 (by rfl) ⟨7542213, by rfl⟩ : syracuseStep 20112569 = 15084427) B15084427
theorem B4463764793 : Blo 1449544 4463764793 := bstep (se 2 (by rfl) ⟨1673911797, by rfl⟩ : syracuseStep 4463764793 = 3347823595) B3347823595
theorem B128845495 : Blo 1449544 128845495 := bstep (se 1 (by rfl) ⟨96634121, by rfl⟩ : syracuseStep 128845495 = 193268243) B193268243
theorem B4130651 : Blo 1449544 4130651 := bstep (se 1 (by rfl) ⟨3097988, by rfl⟩ : syracuseStep 4130651 = 6195977) B6195977
theorem B3352679 : Blo 1449544 3352679 := bstep (se 1 (by rfl) ⟨2514509, by rfl⟩ : syracuseStep 3352679 = 5029019) B5029019
theorem B3262823 : Blo 1449544 3262823 := bstep (se 1 (by rfl) ⟨2447117, by rfl⟩ : syracuseStep 3262823 = 4894235) B4894235
theorem B11766437 : Blo 1449544 11766437 := bstep (se 4 (by rfl) ⟨1103103, by rfl⟩ : syracuseStep 11766437 = 2206207) B2206207
theorem B22318139 : Blo 1449544 22318139 := bstep (se 1 (by rfl) ⟨16738604, by rfl⟩ : syracuseStep 22318139 = 33477209) B33477209
theorem B4893857 : Blo 1449544 4893857 := bstep (se 2 (by rfl) ⟨1835196, by rfl⟩ : syracuseStep 4893857 = 3670393) B3670393
theorem B15691657 : Blo 1449544 15691657 := bstep (se 2 (by rfl) ⟨5884371, by rfl⟩ : syracuseStep 15691657 = 11768743) B11768743
theorem B2174951 : Blo 1449544 2174951 := bstep (se 1 (by rfl) ⟨1631213, by rfl⟩ : syracuseStep 2174951 = 3262427) B3262427
theorem B2175017 : Blo 1449544 2175017 := bstep (se 2 (by rfl) ⟨815631, by rfl⟩ : syracuseStep 2175017 = 1631263) B1631263
theorem B2176127 : Blo 1449544 2176127 := bstep (se 1 (by rfl) ⟨1632095, by rfl⟩ : syracuseStep 2176127 = 3264191) B3264191
theorem B107361463 : Blo 1449544 107361463 := bstep (se 1 (by rfl) ⟨80521097, by rfl⟩ : syracuseStep 107361463 = 161042195) B161042195
theorem B7345565 : Blo 1449544 7345565 := bstep (se 3 (by rfl) ⟨1377293, by rfl⟩ : syracuseStep 7345565 = 2754587) B2754587
theorem B2176553 : Blo 1449544 2176553 := bstep (se 2 (by rfl) ⟨816207, by rfl⟩ : syracuseStep 2176553 = 1632415) B1632415
theorem B1450011 : Blo 1449544 1450011 := bstep (se 1 (by rfl) ⟨1087508, by rfl⟩ : syracuseStep 1450011 = 2175017) B2175017
theorem B59515037 : Blo 1449544 59515037 := bstep (se 3 (by rfl) ⟨11159069, by rfl⟩ : syracuseStep 59515037 = 22318139) B22318139
theorem B1450751 : Blo 1449544 1450751 := bstep (se 1 (by rfl) ⟨1088063, by rfl⟩ : syracuseStep 1450751 = 2176127) B2176127
theorem B2975843195 : Blo 1449544 2975843195 := bstep (se 1 (by rfl) ⟨2231882396, by rfl⟩ : syracuseStep 2975843195 = 4463764793) B4463764793
theorem B1451035 : Blo 1449544 1451035 := bstep (se 1 (by rfl) ⟨1088276, by rfl⟩ : syracuseStep 1451035 = 2176553) B2176553
theorem B2753767 : Blo 1449544 2753767 := bstep (se 1 (by rfl) ⟨2065325, by rfl⟩ : syracuseStep 2753767 = 4130651) B4130651
theorem B143148617 : Blo 1449544 143148617 := bstep (se 2 (by rfl) ⟨53680731, by rfl⟩ : syracuseStep 143148617 = 107361463) B107361463
theorem B3262571 : Blo 1449544 3262571 := bstep (se 1 (by rfl) ⟨2446928, by rfl⟩ : syracuseStep 3262571 = 4893857) B4893857
theorem B2175215 : Blo 1449544 2175215 := bstep (se 1 (by rfl) ⟨1631411, by rfl⟩ : syracuseStep 2175215 = 3262823) B3262823
theorem B7844291 : Blo 1449544 7844291 := bstep (se 1 (by rfl) ⟨5883218, by rfl⟩ : syracuseStep 7844291 = 11766437) B11766437
theorem B13408379 : Blo 1449544 13408379 := bstep (se 1 (by rfl) ⟨10056284, by rfl⟩ : syracuseStep 13408379 = 20112569) B20112569
theorem B4897043 : Blo 1449544 4897043 := bstep (se 1 (by rfl) ⟨3672782, by rfl⟩ : syracuseStep 4897043 = 7345565) B7345565
theorem B687175973 : Blo 1449544 687175973 := bstep (se 4 (by rfl) ⟨64422747, by rfl⟩ : syracuseStep 687175973 = 128845495) B128845495
theorem B2235119 : Blo 1449544 2235119 := bstep (se 1 (by rfl) ⟨1676339, by rfl⟩ : syracuseStep 2235119 = 3352679) B3352679
theorem B20922209 : Blo 1449544 20922209 := bstep (se 2 (by rfl) ⟨7845828, by rfl⟩ : syracuseStep 20922209 = 15691657) B15691657
theorem B1449967 : Blo 1449544 1449967 := bstep (se 1 (by rfl) ⟨1087475, by rfl⟩ : syracuseStep 1449967 = 2174951) B2174951
theorem B1450143 : Blo 1449544 1450143 := bstep (se 1 (by rfl) ⟨1087607, by rfl⟩ : syracuseStep 1450143 = 2175215) B2175215
theorem B8938919 : Blo 1449544 8938919 := bstep (se 1 (by rfl) ⟨6704189, by rfl⟩ : syracuseStep 8938919 = 13408379) B13408379
theorem B3671689 : Blo 1449544 3671689 := bstep (se 2 (by rfl) ⟨1376883, by rfl⟩ : syracuseStep 3671689 = 2753767) B2753767
theorem B39676691 : Blo 1449544 39676691 := bstep (se 1 (by rfl) ⟨29757518, by rfl⟩ : syracuseStep 39676691 = 59515037) B59515037
theorem B5229527 : Blo 1449544 5229527 := bstep (se 1 (by rfl) ⟨3922145, by rfl⟩ : syracuseStep 5229527 = 7844291) B7844291
theorem B95432411 : Blo 1449544 95432411 := bstep (se 1 (by rfl) ⟨71574308, by rfl⟩ : syracuseStep 95432411 = 143148617) B143148617
theorem B2175047 : Blo 1449544 2175047 := bstep (se 1 (by rfl) ⟨1631285, by rfl⟩ : syracuseStep 2175047 = 3262571) B3262571
theorem B3264695 : Blo 1449544 3264695 := bstep (se 1 (by rfl) ⟨2448521, by rfl⟩ : syracuseStep 3264695 = 4897043) B4897043
theorem B458117315 : Blo 1449544 458117315 := bstep (se 1 (by rfl) ⟨343587986, by rfl⟩ : syracuseStep 458117315 = 687175973) B687175973
theorem B5960317 : Blo 1449544 5960317 := bstep (se 3 (by rfl) ⟨1117559, by rfl⟩ : syracuseStep 5960317 = 2235119) B2235119
theorem B13948139 : Blo 1449544 13948139 := bstep (se 1 (by rfl) ⟨10461104, by rfl⟩ : syracuseStep 13948139 = 20922209) B20922209
theorem B1983895463 : Blo 1449544 1983895463 := bstep (se 1 (by rfl) ⟨1487921597, by rfl⟩ : syracuseStep 1983895463 = 2975843195) B2975843195
theorem B1450031 : Blo 1449544 1450031 := bstep (se 1 (by rfl) ⟨1087523, by rfl⟩ : syracuseStep 1450031 = 2175047) B2175047
theorem B9298759 : Blo 1449544 9298759 := bstep (se 1 (by rfl) ⟨6974069, by rfl⟩ : syracuseStep 9298759 = 13948139) B13948139
theorem B7947089 : Blo 1449544 7947089 := bstep (se 2 (by rfl) ⟨2980158, by rfl⟩ : syracuseStep 7947089 = 5960317) B5960317
theorem B55781621 : Blo 1449544 55781621 := bstep (se 5 (by rfl) ⟨2614763, by rfl⟩ : syracuseStep 55781621 = 5229527) B5229527
theorem B5290387901 : Blo 1449544 5290387901 := bstep (se 3 (by rfl) ⟨991947731, by rfl⟩ : syracuseStep 5290387901 = 1983895463) B1983895463
theorem B63621607 : Blo 1449544 63621607 := bstep (se 1 (by rfl) ⟨47716205, by rfl⟩ : syracuseStep 63621607 = 95432411) B95432411
theorem B5959279 : Blo 1449544 5959279 := bstep (se 1 (by rfl) ⟨4469459, by rfl⟩ : syracuseStep 5959279 = 8938919) B8938919
theorem B4895585 : Blo 1449544 4895585 := bstep (se 2 (by rfl) ⟨1835844, by rfl⟩ : syracuseStep 4895585 = 3671689) B3671689
theorem B2176463 : Blo 1449544 2176463 := bstep (se 1 (by rfl) ⟨1632347, by rfl⟩ : syracuseStep 2176463 = 3264695) B3264695
theorem B305411543 : Blo 1449544 305411543 := bstep (se 1 (by rfl) ⟨229058657, by rfl⟩ : syracuseStep 305411543 = 458117315) B458117315
theorem B26451127 : Blo 1449544 26451127 := bstep (se 1 (by rfl) ⟨19838345, by rfl⟩ : syracuseStep 26451127 = 39676691) B39676691
theorem B84828809 : Blo 1449544 84828809 := bstep (se 2 (by rfl) ⟨31810803, by rfl⟩ : syracuseStep 84828809 = 63621607) B63621607
theorem B1450975 : Blo 1449544 1450975 := bstep (se 1 (by rfl) ⟨1088231, by rfl⟩ : syracuseStep 1450975 = 2176463) B2176463
theorem B3263723 : Blo 1449544 3263723 := bstep (se 1 (by rfl) ⟨2447792, by rfl⟩ : syracuseStep 3263723 = 4895585) B4895585
theorem B203607695 : Blo 1449544 203607695 := bstep (se 1 (by rfl) ⟨152705771, by rfl⟩ : syracuseStep 203607695 = 305411543) B305411543
theorem B12398345 : Blo 1449544 12398345 := bstep (se 2 (by rfl) ⟨4649379, by rfl⟩ : syracuseStep 12398345 = 9298759) B9298759
theorem B37187747 : Blo 1449544 37187747 := bstep (se 1 (by rfl) ⟨27890810, by rfl⟩ : syracuseStep 37187747 = 55781621) B55781621
theorem B5298059 : Blo 1449544 5298059 := bstep (se 1 (by rfl) ⟨3973544, by rfl⟩ : syracuseStep 5298059 = 7947089) B7947089
theorem B141072677 : Blo 1449544 141072677 := bstep (se 4 (by rfl) ⟨13225563, by rfl⟩ : syracuseStep 141072677 = 26451127) B26451127
theorem B3526925267 : Blo 1449544 3526925267 := bstep (se 1 (by rfl) ⟨2645193950, by rfl⟩ : syracuseStep 3526925267 = 5290387901) B5290387901
theorem B7945705 : Blo 1449544 7945705 := bstep (se 2 (by rfl) ⟨2979639, by rfl⟩ : syracuseStep 7945705 = 5959279) B5959279
theorem B10594273 : Blo 1449544 10594273 := bstep (se 2 (by rfl) ⟨3972852, by rfl⟩ : syracuseStep 10594273 = 7945705) B7945705
theorem B24791831 : Blo 1449544 24791831 := bstep (se 1 (by rfl) ⟨18593873, by rfl⟩ : syracuseStep 24791831 = 37187747) B37187747
theorem B94048451 : Blo 1449544 94048451 := bstep (se 1 (by rfl) ⟨70536338, by rfl⟩ : syracuseStep 94048451 = 141072677) B141072677
theorem B226210157 : Blo 1449544 226210157 := bstep (se 3 (by rfl) ⟨42414404, by rfl⟩ : syracuseStep 226210157 = 84828809) B84828809
theorem B2175815 : Blo 1449544 2175815 := bstep (se 1 (by rfl) ⟨1631861, by rfl⟩ : syracuseStep 2175815 = 3263723) B3263723
theorem B14128157 : Blo 1449544 14128157 := bstep (se 3 (by rfl) ⟨2649029, by rfl⟩ : syracuseStep 14128157 = 5298059) B5298059
theorem B135738463 : Blo 1449544 135738463 := bstep (se 1 (by rfl) ⟨101803847, by rfl⟩ : syracuseStep 135738463 = 203607695) B203607695
theorem B2351283511 : Blo 1449544 2351283511 := bstep (se 1 (by rfl) ⟨1763462633, by rfl⟩ : syracuseStep 2351283511 = 3526925267) B3526925267
theorem B8265563 : Blo 1449544 8265563 := bstep (se 1 (by rfl) ⟨6199172, by rfl⟩ : syracuseStep 8265563 = 12398345) B12398345
theorem B150806771 : Blo 1449544 150806771 := bstep (se 1 (by rfl) ⟨113105078, by rfl⟩ : syracuseStep 150806771 = 226210157) B226210157
theorem B1450543 : Blo 1449544 1450543 := bstep (se 1 (by rfl) ⟨1087907, by rfl⟩ : syracuseStep 1450543 = 2175815) B2175815
theorem B14125697 : Blo 1449544 14125697 := bstep (se 2 (by rfl) ⟨5297136, by rfl⟩ : syracuseStep 14125697 = 10594273) B10594273
theorem B16527887 : Blo 1449544 16527887 := bstep (se 1 (by rfl) ⟨12395915, by rfl⟩ : syracuseStep 16527887 = 24791831) B24791831
theorem B5510375 : Blo 1449544 5510375 := bstep (se 1 (by rfl) ⟨4132781, by rfl⟩ : syracuseStep 5510375 = 8265563) B8265563
theorem B62698967 : Blo 1449544 62698967 := bstep (se 1 (by rfl) ⟨47024225, by rfl⟩ : syracuseStep 62698967 = 94048451) B94048451
theorem B9418771 : Blo 1449544 9418771 := bstep (se 1 (by rfl) ⟨7064078, by rfl⟩ : syracuseStep 9418771 = 14128157) B14128157
theorem B180984617 : Blo 1449544 180984617 := bstep (se 2 (by rfl) ⟨67869231, by rfl⟩ : syracuseStep 180984617 = 135738463) B135738463
theorem B3135044681 : Blo 1449544 3135044681 := bstep (se 2 (by rfl) ⟨1175641755, by rfl⟩ : syracuseStep 3135044681 = 2351283511) B2351283511
theorem B50233445 : Blo 1449544 50233445 := bstep (se 4 (by rfl) ⟨4709385, by rfl⟩ : syracuseStep 50233445 = 9418771) B9418771
theorem B11018591 : Blo 1449544 11018591 := bstep (se 1 (by rfl) ⟨8263943, by rfl⟩ : syracuseStep 11018591 = 16527887) B16527887
theorem B3673583 : Blo 1449544 3673583 := bstep (se 1 (by rfl) ⟨2755187, by rfl⟩ : syracuseStep 3673583 = 5510375) B5510375
theorem B41799311 : Blo 1449544 41799311 := bstep (se 1 (by rfl) ⟨31349483, by rfl⟩ : syracuseStep 41799311 = 62698967) B62698967
theorem B9417131 : Blo 1449544 9417131 := bstep (se 1 (by rfl) ⟨7062848, by rfl⟩ : syracuseStep 9417131 = 14125697) B14125697
theorem B120656411 : Blo 1449544 120656411 := bstep (se 1 (by rfl) ⟨90492308, by rfl⟩ : syracuseStep 120656411 = 180984617) B180984617
theorem B2090029787 : Blo 1449544 2090029787 := bstep (se 1 (by rfl) ⟨1567522340, by rfl⟩ : syracuseStep 2090029787 = 3135044681) B3135044681
theorem B100537847 : Blo 1449544 100537847 := bstep (se 1 (by rfl) ⟨75403385, by rfl⟩ : syracuseStep 100537847 = 150806771) B150806771
theorem B33488963 : Blo 1449544 33488963 := bstep (se 1 (by rfl) ⟨25116722, by rfl⟩ : syracuseStep 33488963 = 50233445) B50233445
theorem B80437607 : Blo 1449544 80437607 := bstep (se 1 (by rfl) ⟨60328205, by rfl⟩ : syracuseStep 80437607 = 120656411) B120656411
theorem B1393353191 : Blo 1449544 1393353191 := bstep (se 1 (by rfl) ⟨1045014893, by rfl⟩ : syracuseStep 1393353191 = 2090029787) B2090029787
theorem B6278087 : Blo 1449544 6278087 := bstep (se 1 (by rfl) ⟨4708565, by rfl⟩ : syracuseStep 6278087 = 9417131) B9417131
theorem B27866207 : Blo 1449544 27866207 := bstep (se 1 (by rfl) ⟨20899655, by rfl⟩ : syracuseStep 27866207 = 41799311) B41799311
theorem B7345727 : Blo 1449544 7345727 := bstep (se 1 (by rfl) ⟨5509295, by rfl⟩ : syracuseStep 7345727 = 11018591) B11018591
theorem B67025231 : Blo 1449544 67025231 := bstep (se 1 (by rfl) ⟨50268923, by rfl⟩ : syracuseStep 67025231 = 100537847) B100537847
theorem B2449055 : Blo 1449544 2449055 := bstep (se 1 (by rfl) ⟨1836791, by rfl⟩ : syracuseStep 2449055 = 3673583) B3673583
theorem B53625071 : Blo 1449544 53625071 := bstep (se 1 (by rfl) ⟨40218803, by rfl⟩ : syracuseStep 53625071 = 80437607) B80437607
theorem B1632703 : Blo 1449544 1632703 := bstep (se 1 (by rfl) ⟨1224527, by rfl⟩ : syracuseStep 1632703 = 2449055) B2449055
theorem B22325975 : Blo 1449544 22325975 := bstep (se 1 (by rfl) ⟨16744481, by rfl⟩ : syracuseStep 22325975 = 33488963) B33488963
theorem B928902127 : Blo 1449544 928902127 := bstep (se 1 (by rfl) ⟨696676595, by rfl⟩ : syracuseStep 928902127 = 1393353191) B1393353191
theorem B44683487 : Blo 1449544 44683487 := bstep (se 1 (by rfl) ⟨33512615, by rfl⟩ : syracuseStep 44683487 = 67025231) B67025231
theorem B18577471 : Blo 1449544 18577471 := bstep (se 1 (by rfl) ⟨13933103, by rfl⟩ : syracuseStep 18577471 = 27866207) B27866207
theorem B4897151 : Blo 1449544 4897151 := bstep (se 1 (by rfl) ⟨3672863, by rfl⟩ : syracuseStep 4897151 = 7345727) B7345727
theorem B4185391 : Blo 1449544 4185391 := bstep (se 1 (by rfl) ⟨3139043, by rfl⟩ : syracuseStep 4185391 = 6278087) B6278087
theorem B35750047 : Blo 1449544 35750047 := bstep (se 1 (by rfl) ⟨26812535, by rfl⟩ : syracuseStep 35750047 = 53625071) B53625071
theorem B5580521 : Blo 1449544 5580521 := bstep (se 2 (by rfl) ⟨2092695, by rfl⟩ : syracuseStep 5580521 = 4185391) B4185391
theorem B29788991 : Blo 1449544 29788991 := bstep (se 1 (by rfl) ⟨22341743, by rfl⟩ : syracuseStep 29788991 = 44683487) B44683487
theorem B1238536169 : Blo 1449544 1238536169 := bstep (se 2 (by rfl) ⟨464451063, by rfl⟩ : syracuseStep 1238536169 = 928902127) B928902127
theorem B3264767 : Blo 1449544 3264767 := bstep (se 1 (by rfl) ⟨2448575, by rfl⟩ : syracuseStep 3264767 = 4897151) B4897151
theorem B24769961 : Blo 1449544 24769961 := bstep (se 2 (by rfl) ⟨9288735, by rfl⟩ : syracuseStep 24769961 = 18577471) B18577471
theorem B2176937 : Blo 1449544 2176937 := bstep (se 2 (by rfl) ⟨816351, by rfl⟩ : syracuseStep 2176937 = 1632703) B1632703
theorem B14883983 : Blo 1449544 14883983 := bstep (se 1 (by rfl) ⟨11162987, by rfl⟩ : syracuseStep 14883983 = 22325975) B22325975
theorem B3720347 : Blo 1449544 3720347 := bstep (se 1 (by rfl) ⟨2790260, by rfl⟩ : syracuseStep 3720347 = 5580521) B5580521
theorem B1451291 : Blo 1449544 1451291 := bstep (se 1 (by rfl) ⟨1088468, by rfl⟩ : syracuseStep 1451291 = 2176937) B2176937
theorem B19859327 : Blo 1449544 19859327 := bstep (se 1 (by rfl) ⟨14894495, by rfl⟩ : syracuseStep 19859327 = 29788991) B29788991
theorem B9922655 : Blo 1449544 9922655 := bstep (se 1 (by rfl) ⟨7441991, by rfl⟩ : syracuseStep 9922655 = 14883983) B14883983
theorem B825690779 : Blo 1449544 825690779 := bstep (se 1 (by rfl) ⟨619268084, by rfl⟩ : syracuseStep 825690779 = 1238536169) B1238536169
theorem B2176511 : Blo 1449544 2176511 := bstep (se 1 (by rfl) ⟨1632383, by rfl⟩ : syracuseStep 2176511 = 3264767) B3264767
theorem B47666729 : Blo 1449544 47666729 := bstep (se 2 (by rfl) ⟨17875023, by rfl⟩ : syracuseStep 47666729 = 35750047) B35750047
theorem B16513307 : Blo 1449544 16513307 := bstep (se 1 (by rfl) ⟨12384980, by rfl⟩ : syracuseStep 16513307 = 24769961) B24769961
theorem B1451007 : Blo 1449544 1451007 := bstep (se 1 (by rfl) ⟨1088255, by rfl⟩ : syracuseStep 1451007 = 2176511) B2176511
theorem B13239551 : Blo 1449544 13239551 := bstep (se 1 (by rfl) ⟨9929663, by rfl⟩ : syracuseStep 13239551 = 19859327) B19859327
theorem B6615103 : Blo 1449544 6615103 := bstep (se 1 (by rfl) ⟨4961327, by rfl⟩ : syracuseStep 6615103 = 9922655) B9922655
theorem B127111277 : Blo 1449544 127111277 := bstep (se 3 (by rfl) ⟨23833364, by rfl⟩ : syracuseStep 127111277 = 47666729) B47666729
theorem B2480231 : Blo 1449544 2480231 := bstep (se 1 (by rfl) ⟨1860173, by rfl⟩ : syracuseStep 2480231 = 3720347) B3720347
theorem B11008871 : Blo 1449544 11008871 := bstep (se 1 (by rfl) ⟨8256653, by rfl⟩ : syracuseStep 11008871 = 16513307) B16513307
theorem B550460519 : Blo 1449544 550460519 := bstep (se 1 (by rfl) ⟨412845389, by rfl⟩ : syracuseStep 550460519 = 825690779) B825690779
theorem B84740851 : Blo 1449544 84740851 := bstep (se 1 (by rfl) ⟨63555638, by rfl⟩ : syracuseStep 84740851 = 127111277) B127111277
theorem B8826367 : Blo 1449544 8826367 := bstep (se 1 (by rfl) ⟨6619775, by rfl⟩ : syracuseStep 8826367 = 13239551) B13239551
theorem B366973679 : Blo 1449544 366973679 := bstep (se 1 (by rfl) ⟨275230259, by rfl⟩ : syracuseStep 366973679 = 550460519) B550460519
theorem B8820137 : Blo 1449544 8820137 := bstep (se 2 (by rfl) ⟨3307551, by rfl⟩ : syracuseStep 8820137 = 6615103) B6615103
theorem B105823189 : Blo 1449544 105823189 := bstep (se 7 (by rfl) ⟨1240115, by rfl⟩ : syracuseStep 105823189 = 2480231) B2480231
theorem B7339247 : Blo 1449544 7339247 := bstep (se 1 (by rfl) ⟨5504435, by rfl⟩ : syracuseStep 7339247 = 11008871) B11008871
theorem B23520365 : Blo 1449544 23520365 := bstep (se 3 (by rfl) ⟨4410068, by rfl⟩ : syracuseStep 23520365 = 8820137) B8820137
theorem B4892831 : Blo 1449544 4892831 := bstep (se 1 (by rfl) ⟨3669623, by rfl⟩ : syracuseStep 4892831 = 7339247) B7339247
theorem B112987801 : Blo 1449544 112987801 := bstep (se 2 (by rfl) ⟨42370425, by rfl⟩ : syracuseStep 112987801 = 84740851) B84740851
theorem B978596477 : Blo 1449544 978596477 := bstep (se 3 (by rfl) ⟨183486839, by rfl⟩ : syracuseStep 978596477 = 366973679) B366973679
theorem B11768489 : Blo 1449544 11768489 := bstep (se 2 (by rfl) ⟨4413183, by rfl⟩ : syracuseStep 11768489 = 8826367) B8826367
theorem B141097585 : Blo 1449544 141097585 := bstep (se 2 (by rfl) ⟨52911594, by rfl⟩ : syracuseStep 141097585 = 105823189) B105823189
theorem B15680243 : Blo 1449544 15680243 := bstep (se 1 (by rfl) ⟨11760182, by rfl⟩ : syracuseStep 15680243 = 23520365) B23520365
theorem B188130113 : Blo 1449544 188130113 := bstep (se 2 (by rfl) ⟨70548792, by rfl⟩ : syracuseStep 188130113 = 141097585) B141097585
theorem B3261887 : Blo 1449544 3261887 := bstep (se 1 (by rfl) ⟨2446415, by rfl⟩ : syracuseStep 3261887 = 4892831) B4892831
theorem B652397651 : Blo 1449544 652397651 := bstep (se 1 (by rfl) ⟨489298238, by rfl⟩ : syracuseStep 652397651 = 978596477) B978596477
theorem B7845659 : Blo 1449544 7845659 := bstep (se 1 (by rfl) ⟨5884244, by rfl⟩ : syracuseStep 7845659 = 11768489) B11768489
theorem B150650401 : Blo 1449544 150650401 := bstep (se 2 (by rfl) ⟨56493900, by rfl⟩ : syracuseStep 150650401 = 112987801) B112987801
theorem B10453495 : Blo 1449544 10453495 := bstep (se 1 (by rfl) ⟨7840121, by rfl⟩ : syracuseStep 10453495 = 15680243) B15680243
theorem B125420075 : Blo 1449544 125420075 := bstep (se 1 (by rfl) ⟨94065056, by rfl⟩ : syracuseStep 125420075 = 188130113) B188130113
theorem B434931767 : Blo 1449544 434931767 := bstep (se 1 (by rfl) ⟨326198825, by rfl⟩ : syracuseStep 434931767 = 652397651) B652397651
theorem B2174591 : Blo 1449544 2174591 := bstep (se 1 (by rfl) ⟨1630943, by rfl⟩ : syracuseStep 2174591 = 3261887) B3261887
theorem B5230439 : Blo 1449544 5230439 := bstep (se 1 (by rfl) ⟨3922829, by rfl⟩ : syracuseStep 5230439 = 7845659) B7845659
theorem B200867201 : Blo 1449544 200867201 := bstep (se 2 (by rfl) ⟨75325200, by rfl⟩ : syracuseStep 200867201 = 150650401) B150650401
theorem B13937993 : Blo 1449544 13937993 := bstep (se 2 (by rfl) ⟨5226747, by rfl⟩ : syracuseStep 13937993 = 10453495) B10453495
theorem B133911467 : Blo 1449544 133911467 := bstep (se 1 (by rfl) ⟨100433600, by rfl⟩ : syracuseStep 133911467 = 200867201) B200867201
theorem B3486959 : Blo 1449544 3486959 := bstep (se 1 (by rfl) ⟨2615219, by rfl⟩ : syracuseStep 3486959 = 5230439) B5230439
theorem B83613383 : Blo 1449544 83613383 := bstep (se 1 (by rfl) ⟨62710037, by rfl⟩ : syracuseStep 83613383 = 125420075) B125420075
theorem B289954511 : Blo 1449544 289954511 := bstep (se 1 (by rfl) ⟨217465883, by rfl⟩ : syracuseStep 289954511 = 434931767) B434931767
theorem B1449727 : Blo 1449544 1449727 := bstep (se 1 (by rfl) ⟨1087295, by rfl⟩ : syracuseStep 1449727 = 2174591) B2174591
theorem B9291995 : Blo 1449544 9291995 := bstep (se 1 (by rfl) ⟨6968996, by rfl⟩ : syracuseStep 9291995 = 13937993) B13937993
theorem B55742255 : Blo 1449544 55742255 := bstep (se 1 (by rfl) ⟨41806691, by rfl⟩ : syracuseStep 55742255 = 83613383) B83613383
theorem B193303007 : Blo 1449544 193303007 := bstep (se 1 (by rfl) ⟨144977255, by rfl⟩ : syracuseStep 193303007 = 289954511) B289954511
theorem B89274311 : Blo 1449544 89274311 := bstep (se 1 (by rfl) ⟨66955733, by rfl⟩ : syracuseStep 89274311 = 133911467) B133911467
theorem B2324639 : Blo 1449544 2324639 := bstep (se 1 (by rfl) ⟨1743479, by rfl⟩ : syracuseStep 2324639 = 3486959) B3486959
theorem B128868671 : Blo 1449544 128868671 := bstep (se 1 (by rfl) ⟨96651503, by rfl⟩ : syracuseStep 128868671 = 193303007) B193303007
theorem B59516207 : Blo 1449544 59516207 := bstep (se 1 (by rfl) ⟨44637155, by rfl⟩ : syracuseStep 59516207 = 89274311) B89274311
theorem B6194663 : Blo 1449544 6194663 := bstep (se 1 (by rfl) ⟨4645997, by rfl⟩ : syracuseStep 6194663 = 9291995) B9291995
theorem B37161503 : Blo 1449544 37161503 := bstep (se 1 (by rfl) ⟨27871127, by rfl⟩ : syracuseStep 37161503 = 55742255) B55742255
theorem B6199037 : Blo 1449544 6199037 := bstep (se 3 (by rfl) ⟨1162319, by rfl⟩ : syracuseStep 6199037 = 2324639) B2324639
theorem B4129775 : Blo 1449544 4129775 := bstep (se 1 (by rfl) ⟨3097331, by rfl⟩ : syracuseStep 4129775 = 6194663) B6194663
theorem B24774335 : Blo 1449544 24774335 := bstep (se 1 (by rfl) ⟨18580751, by rfl⟩ : syracuseStep 24774335 = 37161503) B37161503
theorem B343649789 : Blo 1449544 343649789 := bstep (se 3 (by rfl) ⟨64434335, by rfl⟩ : syracuseStep 343649789 = 128868671) B128868671
theorem B39677471 : Blo 1449544 39677471 := bstep (se 1 (by rfl) ⟨29758103, by rfl⟩ : syracuseStep 39677471 = 59516207) B59516207
theorem B4132691 : Blo 1449544 4132691 := bstep (se 1 (by rfl) ⟨3099518, by rfl⟩ : syracuseStep 4132691 = 6199037) B6199037
theorem B2753183 : Blo 1449544 2753183 := bstep (se 1 (by rfl) ⟨2064887, by rfl⟩ : syracuseStep 2753183 = 4129775) B4129775
theorem B16516223 : Blo 1449544 16516223 := bstep (se 1 (by rfl) ⟨12387167, by rfl⟩ : syracuseStep 16516223 = 24774335) B24774335
theorem B229099859 : Blo 1449544 229099859 := bstep (se 1 (by rfl) ⟨171824894, by rfl⟩ : syracuseStep 229099859 = 343649789) B343649789
theorem B2755127 : Blo 1449544 2755127 := bstep (se 1 (by rfl) ⟨2066345, by rfl⟩ : syracuseStep 2755127 = 4132691) B4132691
theorem B26451647 : Blo 1449544 26451647 := bstep (se 1 (by rfl) ⟨19838735, by rfl⟩ : syracuseStep 26451647 = 39677471) B39677471
theorem B1835455 : Blo 1449544 1835455 := bstep (se 1 (by rfl) ⟨1376591, by rfl⟩ : syracuseStep 1835455 = 2753183) B2753183
theorem B11010815 : Blo 1449544 11010815 := bstep (se 1 (by rfl) ⟨8258111, by rfl⟩ : syracuseStep 11010815 = 16516223) B16516223
theorem B152733239 : Blo 1449544 152733239 := bstep (se 1 (by rfl) ⟨114549929, by rfl⟩ : syracuseStep 152733239 = 229099859) B229099859
theorem B1836751 : Blo 1449544 1836751 := bstep (se 1 (by rfl) ⟨1377563, by rfl⟩ : syracuseStep 1836751 = 2755127) B2755127
theorem B17634431 : Blo 1449544 17634431 := bstep (se 1 (by rfl) ⟨13225823, by rfl⟩ : syracuseStep 17634431 = 26451647) B26451647
theorem B7340543 : Blo 1449544 7340543 := bstep (se 1 (by rfl) ⟨5505407, by rfl⟩ : syracuseStep 7340543 = 11010815) B11010815
theorem B11756287 : Blo 1449544 11756287 := bstep (se 1 (by rfl) ⟨8817215, by rfl⟩ : syracuseStep 11756287 = 17634431) B17634431
theorem B101822159 : Blo 1449544 101822159 := bstep (se 1 (by rfl) ⟨76366619, by rfl⟩ : syracuseStep 101822159 = 152733239) B152733239
theorem B2447273 : Blo 1449544 2447273 := bstep (se 2 (by rfl) ⟨917727, by rfl⟩ : syracuseStep 2447273 = 1835455) B1835455
theorem B2449001 : Blo 1449544 2449001 := bstep (se 2 (by rfl) ⟨918375, by rfl⟩ : syracuseStep 2449001 = 1836751) B1836751
theorem B1631515 : Blo 1449544 1631515 := bstep (se 1 (by rfl) ⟨1223636, by rfl⟩ : syracuseStep 1631515 = 2447273) B2447273
theorem B1632667 : Blo 1449544 1632667 := bstep (se 1 (by rfl) ⟨1224500, by rfl⟩ : syracuseStep 1632667 = 2449001) B2449001
theorem B67881439 : Blo 1449544 67881439 := bstep (se 1 (by rfl) ⟨50911079, by rfl⟩ : syracuseStep 67881439 = 101822159) B101822159
theorem B4893695 : Blo 1449544 4893695 := bstep (se 1 (by rfl) ⟨3670271, by rfl⟩ : syracuseStep 4893695 = 7340543) B7340543
theorem B15675049 : Blo 1449544 15675049 := bstep (se 2 (by rfl) ⟨5878143, by rfl⟩ : syracuseStep 15675049 = 11756287) B11756287
theorem B3262463 : Blo 1449544 3262463 := bstep (se 1 (by rfl) ⟨2446847, by rfl⟩ : syracuseStep 3262463 = 4893695) B4893695
theorem B20900065 : Blo 1449544 20900065 := bstep (se 2 (by rfl) ⟨7837524, by rfl⟩ : syracuseStep 20900065 = 15675049) B15675049
theorem B90508585 : Blo 1449544 90508585 := bstep (se 2 (by rfl) ⟨33940719, by rfl⟩ : syracuseStep 90508585 = 67881439) B67881439
theorem B2175353 : Blo 1449544 2175353 := bstep (se 2 (by rfl) ⟨815757, by rfl⟩ : syracuseStep 2175353 = 1631515) B1631515
theorem B2176889 : Blo 1449544 2176889 := bstep (se 2 (by rfl) ⟨816333, by rfl⟩ : syracuseStep 2176889 = 1632667) B1632667
theorem B1450235 : Blo 1449544 1450235 := bstep (se 1 (by rfl) ⟨1087676, by rfl⟩ : syracuseStep 1450235 = 2175353) B2175353
theorem B1451259 : Blo 1449544 1451259 := bstep (se 1 (by rfl) ⟨1088444, by rfl⟩ : syracuseStep 1451259 = 2176889) B2176889
theorem B120678113 : Blo 1449544 120678113 := bstep (se 2 (by rfl) ⟨45254292, by rfl⟩ : syracuseStep 120678113 = 90508585) B90508585
theorem B2174975 : Blo 1449544 2174975 := bstep (se 1 (by rfl) ⟨1631231, by rfl⟩ : syracuseStep 2174975 = 3262463) B3262463
theorem B27866753 : Blo 1449544 27866753 := bstep (se 2 (by rfl) ⟨10450032, by rfl⟩ : syracuseStep 27866753 = 20900065) B20900065
theorem B18577835 : Blo 1449544 18577835 := bstep (se 1 (by rfl) ⟨13933376, by rfl⟩ : syracuseStep 18577835 = 27866753) B27866753
theorem B80452075 : Blo 1449544 80452075 := bstep (se 1 (by rfl) ⟨60339056, by rfl⟩ : syracuseStep 80452075 = 120678113) B120678113
theorem B1449983 : Blo 1449544 1449983 := bstep (se 1 (by rfl) ⟨1087487, by rfl⟩ : syracuseStep 1449983 = 2174975) B2174975
theorem B107269433 : Blo 1449544 107269433 := bstep (se 2 (by rfl) ⟨40226037, by rfl⟩ : syracuseStep 107269433 = 80452075) B80452075
theorem B12385223 : Blo 1449544 12385223 := bstep (se 1 (by rfl) ⟨9288917, by rfl⟩ : syracuseStep 12385223 = 18577835) B18577835
theorem B71512955 : Blo 1449544 71512955 := bstep (se 1 (by rfl) ⟨53634716, by rfl⟩ : syracuseStep 71512955 = 107269433) B107269433
theorem B8256815 : Blo 1449544 8256815 := bstep (se 1 (by rfl) ⟨6192611, by rfl⟩ : syracuseStep 8256815 = 12385223) B12385223
theorem B47675303 : Blo 1449544 47675303 := bstep (se 1 (by rfl) ⟨35756477, by rfl⟩ : syracuseStep 47675303 = 71512955) B71512955
theorem B5504543 : Blo 1449544 5504543 := bstep (se 1 (by rfl) ⟨4128407, by rfl⟩ : syracuseStep 5504543 = 8256815) B8256815
theorem B31783535 : Blo 1449544 31783535 := bstep (se 1 (by rfl) ⟨23837651, by rfl⟩ : syracuseStep 31783535 = 47675303) B47675303
theorem B3669695 : Blo 1449544 3669695 := bstep (se 1 (by rfl) ⟨2752271, by rfl⟩ : syracuseStep 3669695 = 5504543) B5504543
theorem B21189023 : Blo 1449544 21189023 := bstep (se 1 (by rfl) ⟨15891767, by rfl⟩ : syracuseStep 21189023 = 31783535) B31783535
theorem B2446463 : Blo 1449544 2446463 := bstep (se 1 (by rfl) ⟨1834847, by rfl⟩ : syracuseStep 2446463 = 3669695) B3669695
theorem B1630975 : Blo 1449544 1630975 := bstep (se 1 (by rfl) ⟨1223231, by rfl⟩ : syracuseStep 1630975 = 2446463) B2446463
theorem B14126015 : Blo 1449544 14126015 := bstep (se 1 (by rfl) ⟨10594511, by rfl⟩ : syracuseStep 14126015 = 21189023) B21189023
theorem B2174633 : Blo 1449544 2174633 := bstep (se 2 (by rfl) ⟨815487, by rfl⟩ : syracuseStep 2174633 = 1630975) B1630975
theorem B9417343 : Blo 1449544 9417343 := bstep (se 1 (by rfl) ⟨7063007, by rfl⟩ : syracuseStep 9417343 = 14126015) B14126015
theorem B12556457 : Blo 1449544 12556457 := bstep (se 2 (by rfl) ⟨4708671, by rfl⟩ : syracuseStep 12556457 = 9417343) B9417343
theorem B1449755 : Blo 1449544 1449755 := bstep (se 1 (by rfl) ⟨1087316, by rfl⟩ : syracuseStep 1449755 = 2174633) B2174633
theorem B8370971 : Blo 1449544 8370971 := bstep (se 1 (by rfl) ⟨6278228, by rfl⟩ : syracuseStep 8370971 = 12556457) B12556457
theorem B5580647 : Blo 1449544 5580647 := bstep (se 1 (by rfl) ⟨4185485, by rfl⟩ : syracuseStep 5580647 = 8370971) B8370971
theorem B3720431 : Blo 1449544 3720431 := bstep (se 1 (by rfl) ⟨2790323, by rfl⟩ : syracuseStep 3720431 = 5580647) B5580647
theorem B9921149 : Blo 1449544 9921149 := bstep (se 3 (by rfl) ⟨1860215, by rfl⟩ : syracuseStep 9921149 = 3720431) B3720431
theorem B6614099 : Blo 1449544 6614099 := bstep (se 1 (by rfl) ⟨4960574, by rfl⟩ : syracuseStep 6614099 = 9921149) B9921149
theorem B4409399 : Blo 1449544 4409399 := bstep (se 1 (by rfl) ⟨3307049, by rfl⟩ : syracuseStep 4409399 = 6614099) B6614099
theorem B2939599 : Blo 1449544 2939599 := bstep (se 1 (by rfl) ⟨2204699, by rfl⟩ : syracuseStep 2939599 = 4409399) B4409399
theorem B3919465 : Blo 1449544 3919465 := bstep (se 2 (by rfl) ⟨1469799, by rfl⟩ : syracuseStep 3919465 = 2939599) B2939599
theorem B5225953 : Blo 1449544 5225953 := bstep (se 2 (by rfl) ⟨1959732, by rfl⟩ : syracuseStep 5225953 = 3919465) B3919465
theorem B6967937 : Blo 1449544 6967937 := bstep (se 2 (by rfl) ⟨2612976, by rfl⟩ : syracuseStep 6967937 = 5225953) B5225953
theorem B4645291 : Blo 1449544 4645291 := bstep (se 1 (by rfl) ⟨3483968, by rfl⟩ : syracuseStep 4645291 = 6967937) B6967937
theorem B6193721 : Blo 1449544 6193721 := bstep (se 2 (by rfl) ⟨2322645, by rfl⟩ : syracuseStep 6193721 = 4645291) B4645291
theorem B4129147 : Blo 1449544 4129147 := bstep (se 1 (by rfl) ⟨3096860, by rfl⟩ : syracuseStep 4129147 = 6193721) B6193721
theorem B5505529 : Blo 1449544 5505529 := bstep (se 2 (by rfl) ⟨2064573, by rfl⟩ : syracuseStep 5505529 = 4129147) B4129147
theorem B7340705 : Blo 1449544 7340705 := bstep (se 2 (by rfl) ⟨2752764, by rfl⟩ : syracuseStep 7340705 = 5505529) B5505529
theorem B4893803 : Blo 1449544 4893803 := bstep (se 1 (by rfl) ⟨3670352, by rfl⟩ : syracuseStep 4893803 = 7340705) B7340705
theorem B3262535 : Blo 1449544 3262535 := bstep (se 1 (by rfl) ⟨2446901, by rfl⟩ : syracuseStep 3262535 = 4893803) B4893803
theorem B2175023 : Blo 1449544 2175023 := bstep (se 1 (by rfl) ⟨1631267, by rfl⟩ : syracuseStep 2175023 = 3262535) B3262535
theorem B1450015 : Blo 1449544 1450015 := bstep (se 1 (by rfl) ⟨1087511, by rfl⟩ : syracuseStep 1450015 = 2175023) B2175023

theorem C0 (j : ℕ) (h1 : 362386 ≤ j) (h2 : j ≤ 362885) : Blo 1449544 (4 * j + 3) := by
  interval_cases j
  · exact B1449547
  · exact B1449551
  · exact B1449555
  · exact B1449559
  · exact B1449563
  · exact B1449567
  · exact B1449571
  · exact B1449575
  · exact B1449579
  · exact B1449583
  · exact B1449587
  · exact B1449591
  · exact B1449595
  · exact B1449599
  · exact B1449603
  · exact B1449607
  · exact B1449611
  · exact B1449615
  · exact B1449619
  · exact B1449623
  · exact B1449627
  · exact B1449631
  · exact B1449635
  · exact B1449639
  · exact B1449643
  · exact B1449647
  · exact B1449651
  · exact B1449655
  · exact B1449659
  · exact B1449663
  · exact B1449667
  · exact B1449671
  · exact B1449675
  · exact B1449679
  · exact B1449683
  · exact B1449687
  · exact B1449691
  · exact B1449695
  · exact B1449699
  · exact B1449703
  · exact B1449707
  · exact B1449711
  · exact B1449715
  · exact B1449719
  · exact B1449723
  · exact B1449727
  · exact B1449731
  · exact B1449735
  · exact B1449739
  · exact B1449743
  · exact B1449747
  · exact B1449751
  · exact B1449755
  · exact B1449759
  · exact B1449763
  · exact B1449767
  · exact B1449771
  · exact B1449775
  · exact B1449779
  · exact B1449783
  · exact B1449787
  · exact B1449791
  · exact B1449795
  · exact B1449799
  · exact B1449803
  · exact B1449807
  · exact B1449811
  · exact B1449815
  · exact B1449819
  · exact B1449823
  · exact B1449827
  · exact B1449831
  · exact B1449835
  · exact B1449839
  · exact B1449843
  · exact B1449847
  · exact B1449851
  · exact B1449855
  · exact B1449859
  · exact B1449863
  · exact B1449867
  · exact B1449871
  · exact B1449875
  · exact B1449879
  · exact B1449883
  · exact B1449887
  · exact B1449891
  · exact B1449895
  · exact B1449899
  · exact B1449903
  · exact B1449907
  · exact B1449911
  · exact B1449915
  · exact B1449919
  · exact B1449923
  · exact B1449927
  · exact B1449931
  · exact B1449935
  · exact B1449939
  · exact B1449943
  · exact B1449947
  · exact B1449951
  · exact B1449955
  · exact B1449959
  · exact B1449963
  · exact B1449967
  · exact B1449971
  · exact B1449975
  · exact B1449979
  · exact B1449983
  · exact B1449987
  · exact B1449991
  · exact B1449995
  · exact B1449999
  · exact B1450003
  · exact B1450007
  · exact B1450011
  · exact B1450015
  · exact B1450019
  · exact B1450023
  · exact B1450027
  · exact B1450031
  · exact B1450035
  · exact B1450039
  · exact B1450043
  · exact B1450047
  · exact B1450051
  · exact B1450055
  · exact B1450059
  · exact B1450063
  · exact B1450067
  · exact B1450071
  · exact B1450075
  · exact B1450079
  · exact B1450083
  · exact B1450087
  · exact B1450091
  · exact B1450095
  · exact B1450099
  · exact B1450103
  · exact B1450107
  · exact B1450111
  · exact B1450115
  · exact B1450119
  · exact B1450123
  · exact B1450127
  · exact B1450131
  · exact B1450135
  · exact B1450139
  · exact B1450143
  · exact B1450147
  · exact B1450151
  · exact B1450155
  · exact B1450159
  · exact B1450163
  · exact B1450167
  · exact B1450171
  · exact B1450175
  · exact B1450179
  · exact B1450183
  · exact B1450187
  · exact B1450191
  · exact B1450195
  · exact B1450199
  · exact B1450203
  · exact B1450207
  · exact B1450211
  · exact B1450215
  · exact B1450219
  · exact B1450223
  · exact B1450227
  · exact B1450231
  · exact B1450235
  · exact B1450239
  · exact B1450243
  · exact B1450247
  · exact B1450251
  · exact B1450255
  · exact B1450259
  · exact B1450263
  · exact B1450267
  · exact B1450271
  · exact B1450275
  · exact B1450279
  · exact B1450283
  · exact B1450287
  · exact B1450291
  · exact B1450295
  · exact B1450299
  · exact B1450303
  · exact B1450307
  · exact B1450311
  · exact B1450315
  · exact B1450319
  · exact B1450323
  · exact B1450327
  · exact B1450331
  · exact B1450335
  · exact B1450339
  · exact B1450343
  · exact B1450347
  · exact B1450351
  · exact B1450355
  · exact B1450359
  · exact B1450363
  · exact B1450367
  · exact B1450371
  · exact B1450375
  · exact B1450379
  · exact B1450383
  · exact B1450387
  · exact B1450391
  · exact B1450395
  · exact B1450399
  · exact B1450403
  · exact B1450407
  · exact B1450411
  · exact B1450415
  · exact B1450419
  · exact B1450423
  · exact B1450427
  · exact B1450431
  · exact B1450435
  · exact B1450439
  · exact B1450443
  · exact B1450447
  · exact B1450451
  · exact B1450455
  · exact B1450459
  · exact B1450463
  · exact B1450467
  · exact B1450471
  · exact B1450475
  · exact B1450479
  · exact B1450483
  · exact B1450487
  · exact B1450491
  · exact B1450495
  · exact B1450499
  · exact B1450503
  · exact B1450507
  · exact B1450511
  · exact B1450515
  · exact B1450519
  · exact B1450523
  · exact B1450527
  · exact B1450531
  · exact B1450535
  · exact B1450539
  · exact B1450543
  · exact B1450547
  · exact B1450551
  · exact B1450555
  · exact B1450559
  · exact B1450563
  · exact B1450567
  · exact B1450571
  · exact B1450575
  · exact B1450579
  · exact B1450583
  · exact B1450587
  · exact B1450591
  · exact B1450595
  · exact B1450599
  · exact B1450603
  · exact B1450607
  · exact B1450611
  · exact B1450615
  · exact B1450619
  · exact B1450623
  · exact B1450627
  · exact B1450631
  · exact B1450635
  · exact B1450639
  · exact B1450643
  · exact B1450647
  · exact B1450651
  · exact B1450655
  · exact B1450659
  · exact B1450663
  · exact B1450667
  · exact B1450671
  · exact B1450675
  · exact B1450679
  · exact B1450683
  · exact B1450687
  · exact B1450691
  · exact B1450695
  · exact B1450699
  · exact B1450703
  · exact B1450707
  · exact B1450711
  · exact B1450715
  · exact B1450719
  · exact B1450723
  · exact B1450727
  · exact B1450731
  · exact B1450735
  · exact B1450739
  · exact B1450743
  · exact B1450747
  · exact B1450751
  · exact B1450755
  · exact B1450759
  · exact B1450763
  · exact B1450767
  · exact B1450771
  · exact B1450775
  · exact B1450779
  · exact B1450783
  · exact B1450787
  · exact B1450791
  · exact B1450795
  · exact B1450799
  · exact B1450803
  · exact B1450807
  · exact B1450811
  · exact B1450815
  · exact B1450819
  · exact B1450823
  · exact B1450827
  · exact B1450831
  · exact B1450835
  · exact B1450839
  · exact B1450843
  · exact B1450847
  · exact B1450851
  · exact B1450855
  · exact B1450859
  · exact B1450863
  · exact B1450867
  · exact B1450871
  · exact B1450875
  · exact B1450879
  · exact B1450883
  · exact B1450887
  · exact B1450891
  · exact B1450895
  · exact B1450899
  · exact B1450903
  · exact B1450907
  · exact B1450911
  · exact B1450915
  · exact B1450919
  · exact B1450923
  · exact B1450927
  · exact B1450931
  · exact B1450935
  · exact B1450939
  · exact B1450943
  · exact B1450947
  · exact B1450951
  · exact B1450955
  · exact B1450959
  · exact B1450963
  · exact B1450967
  · exact B1450971
  · exact B1450975
  · exact B1450979
  · exact B1450983
  · exact B1450987
  · exact B1450991
  · exact B1450995
  · exact B1450999
  · exact B1451003
  · exact B1451007
  · exact B1451011
  · exact B1451015
  · exact B1451019
  · exact B1451023
  · exact B1451027
  · exact B1451031
  · exact B1451035
  · exact B1451039
  · exact B1451043
  · exact B1451047
  · exact B1451051
  · exact B1451055
  · exact B1451059
  · exact B1451063
  · exact B1451067
  · exact B1451071
  · exact B1451075
  · exact B1451079
  · exact B1451083
  · exact B1451087
  · exact B1451091
  · exact B1451095
  · exact B1451099
  · exact B1451103
  · exact B1451107
  · exact B1451111
  · exact B1451115
  · exact B1451119
  · exact B1451123
  · exact B1451127
  · exact B1451131
  · exact B1451135
  · exact B1451139
  · exact B1451143
  · exact B1451147
  · exact B1451151
  · exact B1451155
  · exact B1451159
  · exact B1451163
  · exact B1451167
  · exact B1451171
  · exact B1451175
  · exact B1451179
  · exact B1451183
  · exact B1451187
  · exact B1451191
  · exact B1451195
  · exact B1451199
  · exact B1451203
  · exact B1451207
  · exact B1451211
  · exact B1451215
  · exact B1451219
  · exact B1451223
  · exact B1451227
  · exact B1451231
  · exact B1451235
  · exact B1451239
  · exact B1451243
  · exact B1451247
  · exact B1451251
  · exact B1451255
  · exact B1451259
  · exact B1451263
  · exact B1451267
  · exact B1451271
  · exact B1451275
  · exact B1451279
  · exact B1451283
  · exact B1451287
  · exact B1451291
  · exact B1451295
  · exact B1451299
  · exact B1451303
  · exact B1451307
  · exact B1451311
  · exact B1451315
  · exact B1451319
  · exact B1451323
  · exact B1451327
  · exact B1451331
  · exact B1451335
  · exact B1451339
  · exact B1451343
  · exact B1451347
  · exact B1451351
  · exact B1451355
  · exact B1451359
  · exact B1451363
  · exact B1451367
  · exact B1451371
  · exact B1451375
  · exact B1451379
  · exact B1451383
  · exact B1451387
  · exact B1451391
  · exact B1451395
  · exact B1451399
  · exact B1451403
  · exact B1451407
  · exact B1451411
  · exact B1451415
  · exact B1451419
  · exact B1451423
  · exact B1451427
  · exact B1451431
  · exact B1451435
  · exact B1451439
  · exact B1451443
  · exact B1451447
  · exact B1451451
  · exact B1451455
  · exact B1451459
  · exact B1451463
  · exact B1451467
  · exact B1451471
  · exact B1451475
  · exact B1451479
  · exact B1451483
  · exact B1451487
  · exact B1451491
  · exact B1451495
  · exact B1451499
  · exact B1451503
  · exact B1451507
  · exact B1451511
  · exact B1451515
  · exact B1451519
  · exact B1451523
  · exact B1451527
  · exact B1451531
  · exact B1451535
  · exact B1451539
  · exact B1451543

theorem solution (m : ℕ) (hlo : 1449544 ≤ m) (hhi : m ≤ 1451544) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 362386 ≤ j := by omega
    have hj2 : j ≤ 362885 := by omega
    have hb : Blo 1449544 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
