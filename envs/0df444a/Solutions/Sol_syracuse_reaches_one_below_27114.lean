-- Prove2me | solution 1 for syracuse_reaches_one_below_27114
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T05:09:51.026923+00:00
-- url     : https://prove2.me/submissions/dc63a6be-cb62-40a1-9cc7-cc10e825b370

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_reaches_one_below_23501

set_option maxHeartbeats 1000000

open Nat

abbrev Reach (n : ℕ) : Prop := ∃ j : ℕ, syracuseStep^[j] n = 1

theorem se (a : ℕ) {y z : ℕ} (h : 3 * y + 1 = 2 ^ a * z) (hz : Odd z) :
    syracuseStep y = z := by
  have hz0 : z ≠ 0 := by rintro rfl; simp [Nat.odd_iff] at hz
  have hfac : (3 * y + 1).factorization 2 = a := by
    rw [h, Nat.factorization_mul (by positivity) hz0]
    simp [Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by rwa [Nat.two_dvd_ne_zero, ← Nat.odd_iff])]
  show ordCompl[2] (3 * y + 1) = z
  rw [hfac, h, Nat.mul_div_cancel_left _ (by positivity)]

theorem rs {x y : ℕ} (h : syracuseStep x = y) (hy : Reach y) : Reach x := by
  obtain ⟨j, hj⟩ := hy
  exact ⟨j + 1, by rw [Function.iterate_add_apply, Function.iterate_one, h]; exact hj⟩

/-- Everything below the previously verified bound is already known to reach 1. -/
theorem B (n : ℕ) (h1 : 0 < n) (h2 : Odd n) (h3 : n ≤ 23500) : Reach n :=
  syracuse_reaches_one_below_23501 n h1 h2 h3
theorem R65605 : Reach 65605 := rs (se 4 (by rfl) ⟨6150, by rfl⟩) (B 12301 (by norm_num) ⟨6150, by rfl⟩ (by norm_num))
theorem R98597 : Reach 98597 := rs (se 4 (by rfl) ⟨9243, by rfl⟩) (B 18487 (by norm_num) ⟨9243, by rfl⟩ (by norm_num))
theorem R131381 : Reach 131381 := rs (se 5 (by rfl) ⟨6158, by rfl⟩) (B 12317 (by norm_num) ⟨6158, by rfl⟩ (by norm_num))
theorem R65893 : Reach 65893 := rs (se 4 (by rfl) ⟨6177, by rfl⟩) (B 12355 (by norm_num) ⟨6177, by rfl⟩ (by norm_num))
theorem R33149 : Reach 33149 := rs (se 3 (by rfl) ⟨6215, by rfl⟩) (B 12431 (by norm_num) ⟨6215, by rfl⟩ (by norm_num))
theorem R33205 : Reach 33205 := rs (se 5 (by rfl) ⟨1556, by rfl⟩) (B 3113 (by norm_num) ⟨1556, by rfl⟩ (by norm_num))
theorem R66005 : Reach 66005 := rs (se 7 (by rfl) ⟨773, by rfl⟩) (B 1547 (by norm_num) ⟨773, by rfl⟩ (by norm_num))
theorem R33253 : Reach 33253 := rs (se 4 (by rfl) ⟨3117, by rfl⟩) (B 6235 (by norm_num) ⟨3117, by rfl⟩ (by norm_num))
theorem R229877 : Reach 229877 := rs (se 5 (by rfl) ⟨10775, by rfl⟩) (B 21551 (by norm_num) ⟨10775, by rfl⟩ (by norm_num))
theorem R33301 : Reach 33301 := rs (se 6 (by rfl) ⟨780, by rfl⟩) (B 1561 (by norm_num) ⟨780, by rfl⟩ (by norm_num))
theorem R164501 : Reach 164501 := rs (se 6 (by rfl) ⟨3855, by rfl⟩) (B 7711 (by norm_num) ⟨3855, by rfl⟩ (by norm_num))
theorem R66197 : Reach 66197 := rs (se 6 (by rfl) ⟨1551, by rfl⟩) (B 3103 (by norm_num) ⟨1551, by rfl⟩ (by norm_num))
theorem R164693 : Reach 164693 := rs (se 9 (by rfl) ⟨482, by rfl⟩) (B 965 (by norm_num) ⟨482, by rfl⟩ (by norm_num))
theorem R33637 : Reach 33637 := rs (se 4 (by rfl) ⟨3153, by rfl⟩) (B 6307 (by norm_num) ⟨3153, by rfl⟩ (by norm_num))
theorem R33797 : Reach 33797 := rs (se 4 (by rfl) ⟨3168, by rfl⟩) (B 6337 (by norm_num) ⟨3168, by rfl⟩ (by norm_num))
theorem R33853 : Reach 33853 := rs (se 3 (by rfl) ⟨6347, by rfl⟩) (B 12695 (by norm_num) ⟨6347, by rfl⟩ (by norm_num))
theorem R984149 : Reach 984149 := rs (se 8 (by rfl) ⟨5766, by rfl⟩) (B 11533 (by norm_num) ⟨5766, by rfl⟩ (by norm_num))
theorem R33949 : Reach 33949 := rs (se 3 (by rfl) ⟨6365, by rfl⟩) (B 12731 (by norm_num) ⟨6365, by rfl⟩ (by norm_num))
theorem R34229 : Reach 34229 := rs (se 5 (by rfl) ⟨1604, by rfl⟩) (B 3209 (by norm_num) ⟨1604, by rfl⟩ (by norm_num))
theorem R67189 : Reach 67189 := rs (se 5 (by rfl) ⟨3149, by rfl⟩) (B 6299 (by norm_num) ⟨3149, by rfl⟩ (by norm_num))
theorem R67205 : Reach 67205 := rs (se 4 (by rfl) ⟨6300, by rfl⟩) (B 12601 (by norm_num) ⟨6300, by rfl⟩ (by norm_num))
theorem R67301 : Reach 67301 := rs (se 4 (by rfl) ⟨6309, by rfl⟩) (B 12619 (by norm_num) ⟨6309, by rfl⟩ (by norm_num))
theorem R67493 : Reach 67493 := rs (se 4 (by rfl) ⟨6327, by rfl⟩) (B 12655 (by norm_num) ⟨6327, by rfl⟩ (by norm_num))
theorem R198773 : Reach 198773 := rs (se 5 (by rfl) ⟨9317, by rfl⟩) (B 18635 (by norm_num) ⟨9317, by rfl⟩ (by norm_num))
theorem R100709 : Reach 100709 := rs (se 4 (by rfl) ⟨9441, by rfl⟩) (B 18883 (by norm_num) ⟨9441, by rfl⟩ (by norm_num))
theorem R35261 : Reach 35261 := rs (se 3 (by rfl) ⟨6611, by rfl⟩) (B 13223 (by norm_num) ⟨6611, by rfl⟩ (by norm_num))
theorem R35285 : Reach 35285 := rs (se 7 (by rfl) ⟨413, by rfl⟩) (B 827 (by norm_num) ⟨413, by rfl⟩ (by norm_num))
theorem R35309 : Reach 35309 := rs (se 3 (by rfl) ⟨6620, by rfl⟩) (B 13241 (by norm_num) ⟨6620, by rfl⟩ (by norm_num))
theorem R35333 : Reach 35333 := rs (se 4 (by rfl) ⟨3312, by rfl⟩) (B 6625 (by norm_num) ⟨3312, by rfl⟩ (by norm_num))
theorem R68117 : Reach 68117 := rs (se 6 (by rfl) ⟨1596, by rfl⟩) (B 3193 (by norm_num) ⟨1596, by rfl⟩ (by norm_num))
theorem R35357 : Reach 35357 := rs (se 3 (by rfl) ⟨6629, by rfl⟩) (B 13259 (by norm_num) ⟨6629, by rfl⟩ (by norm_num))
theorem R35381 : Reach 35381 := rs (se 5 (by rfl) ⟨1658, by rfl⟩) (B 3317 (by norm_num) ⟨1658, by rfl⟩ (by norm_num))
theorem R35405 : Reach 35405 := rs (se 3 (by rfl) ⟨6638, by rfl⟩) (B 13277 (by norm_num) ⟨6638, by rfl⟩ (by norm_num))
theorem R35429 : Reach 35429 := rs (se 4 (by rfl) ⟨3321, by rfl⟩) (B 6643 (by norm_num) ⟨3321, by rfl⟩ (by norm_num))
theorem R35453 : Reach 35453 := rs (se 3 (by rfl) ⟨6647, by rfl⟩) (B 13295 (by norm_num) ⟨6647, by rfl⟩ (by norm_num))
theorem R100997 : Reach 100997 := rs (se 4 (by rfl) ⟨9468, by rfl⟩) (B 18937 (by norm_num) ⟨9468, by rfl⟩ (by norm_num))
theorem R35477 : Reach 35477 := rs (se 6 (by rfl) ⟨831, by rfl⟩) (B 1663 (by norm_num) ⟨831, by rfl⟩ (by norm_num))
theorem R35501 : Reach 35501 := rs (se 3 (by rfl) ⟨6656, by rfl⟩) (B 13313 (by norm_num) ⟨6656, by rfl⟩ (by norm_num))
theorem R35525 : Reach 35525 := rs (se 4 (by rfl) ⟨3330, by rfl⟩) (B 6661 (by norm_num) ⟨3330, by rfl⟩ (by norm_num))
theorem R35549 : Reach 35549 := rs (se 3 (by rfl) ⟨6665, by rfl⟩) (B 13331 (by norm_num) ⟨6665, by rfl⟩ (by norm_num))
theorem R35573 : Reach 35573 := rs (se 5 (by rfl) ⟨1667, by rfl⟩) (B 3335 (by norm_num) ⟨1667, by rfl⟩ (by norm_num))
theorem R35597 : Reach 35597 := rs (se 3 (by rfl) ⟨6674, by rfl⟩) (B 13349 (by norm_num) ⟨6674, by rfl⟩ (by norm_num))
theorem R35621 : Reach 35621 := rs (se 4 (by rfl) ⟨3339, by rfl⟩) (B 6679 (by norm_num) ⟨3339, by rfl⟩ (by norm_num))
theorem R35645 : Reach 35645 := rs (se 3 (by rfl) ⟨6683, by rfl⟩) (B 13367 (by norm_num) ⟨6683, by rfl⟩ (by norm_num))
theorem R35653 : Reach 35653 := rs (se 4 (by rfl) ⟨3342, by rfl⟩) (B 6685 (by norm_num) ⟨3342, by rfl⟩ (by norm_num))
theorem R35669 : Reach 35669 := rs (se 9 (by rfl) ⟨104, by rfl⟩) (B 209 (by norm_num) ⟨104, by rfl⟩ (by norm_num))
theorem R133973 : Reach 133973 := rs (se 9 (by rfl) ⟨392, by rfl⟩) (B 785 (by norm_num) ⟨392, by rfl⟩ (by norm_num))
theorem R35693 : Reach 35693 := rs (se 3 (by rfl) ⟨6692, by rfl⟩) (B 13385 (by norm_num) ⟨6692, by rfl⟩ (by norm_num))
theorem R35717 : Reach 35717 := rs (se 4 (by rfl) ⟨3348, by rfl⟩) (B 6697 (by norm_num) ⟨3348, by rfl⟩ (by norm_num))
theorem R68485 : Reach 68485 := rs (se 4 (by rfl) ⟨6420, by rfl⟩) (B 12841 (by norm_num) ⟨6420, by rfl⟩ (by norm_num))
theorem R35741 : Reach 35741 := rs (se 3 (by rfl) ⟨6701, by rfl⟩) (B 13403 (by norm_num) ⟨6701, by rfl⟩ (by norm_num))
theorem R35765 : Reach 35765 := rs (se 5 (by rfl) ⟨1676, by rfl⟩) (B 3353 (by norm_num) ⟨1676, by rfl⟩ (by norm_num))
theorem R35789 : Reach 35789 := rs (se 3 (by rfl) ⟨6710, by rfl⟩) (B 13421 (by norm_num) ⟨6710, by rfl⟩ (by norm_num))
theorem R35813 : Reach 35813 := rs (se 4 (by rfl) ⟨3357, by rfl⟩) (B 6715 (by norm_num) ⟨3357, by rfl⟩ (by norm_num))
theorem R68597 : Reach 68597 := rs (se 5 (by rfl) ⟨3215, by rfl⟩) (B 6431 (by norm_num) ⟨3215, by rfl⟩ (by norm_num))
theorem R35837 : Reach 35837 := rs (se 3 (by rfl) ⟨6719, by rfl⟩) (B 13439 (by norm_num) ⟨6719, by rfl⟩ (by norm_num))
theorem R35861 : Reach 35861 := rs (se 6 (by rfl) ⟨840, by rfl⟩) (B 1681 (by norm_num) ⟨840, by rfl⟩ (by norm_num))
theorem R35885 : Reach 35885 := rs (se 3 (by rfl) ⟨6728, by rfl⟩) (B 13457 (by norm_num) ⟨6728, by rfl⟩ (by norm_num))
theorem R68677 : Reach 68677 := rs (se 4 (by rfl) ⟨6438, by rfl⟩) (B 12877 (by norm_num) ⟨6438, by rfl⟩ (by norm_num))
theorem R35909 : Reach 35909 := rs (se 4 (by rfl) ⟨3366, by rfl⟩) (B 6733 (by norm_num) ⟨3366, by rfl⟩ (by norm_num))
theorem R35933 : Reach 35933 := rs (se 3 (by rfl) ⟨6737, by rfl⟩) (B 13475 (by norm_num) ⟨6737, by rfl⟩ (by norm_num))
theorem R35957 : Reach 35957 := rs (se 5 (by rfl) ⟨1685, by rfl⟩) (B 3371 (by norm_num) ⟨1685, by rfl⟩ (by norm_num))
theorem R35981 : Reach 35981 := rs (se 3 (by rfl) ⟨6746, by rfl⟩) (B 13493 (by norm_num) ⟨6746, by rfl⟩ (by norm_num))
theorem R36005 : Reach 36005 := rs (se 4 (by rfl) ⟨3375, by rfl⟩) (B 6751 (by norm_num) ⟨3375, by rfl⟩ (by norm_num))
theorem R68789 : Reach 68789 := rs (se 5 (by rfl) ⟨3224, by rfl⟩) (B 6449 (by norm_num) ⟨3224, by rfl⟩ (by norm_num))
theorem R36029 : Reach 36029 := rs (se 3 (by rfl) ⟨6755, by rfl⟩) (B 13511 (by norm_num) ⟨6755, by rfl⟩ (by norm_num))
theorem R36053 : Reach 36053 := rs (se 7 (by rfl) ⟨422, by rfl⟩) (B 845 (by norm_num) ⟨422, by rfl⟩ (by norm_num))
theorem R36077 : Reach 36077 := rs (se 3 (by rfl) ⟨6764, by rfl⟩) (B 13529 (by norm_num) ⟨6764, by rfl⟩ (by norm_num))
theorem R36101 : Reach 36101 := rs (se 4 (by rfl) ⟨3384, by rfl⟩) (B 6769 (by norm_num) ⟨3384, by rfl⟩ (by norm_num))
theorem R36125 : Reach 36125 := rs (se 3 (by rfl) ⟨6773, by rfl⟩) (B 13547 (by norm_num) ⟨6773, by rfl⟩ (by norm_num))
theorem R36149 : Reach 36149 := rs (se 5 (by rfl) ⟨1694, by rfl⟩) (B 3389 (by norm_num) ⟨1694, by rfl⟩ (by norm_num))
theorem R36173 : Reach 36173 := rs (se 3 (by rfl) ⟨6782, by rfl⟩) (B 13565 (by norm_num) ⟨6782, by rfl⟩ (by norm_num))
theorem R36197 : Reach 36197 := rs (se 4 (by rfl) ⟨3393, by rfl⟩) (B 6787 (by norm_num) ⟨3393, by rfl⟩ (by norm_num))
theorem R36221 : Reach 36221 := rs (se 3 (by rfl) ⟨6791, by rfl⟩) (B 13583 (by norm_num) ⟨6791, by rfl⟩ (by norm_num))
theorem R36245 : Reach 36245 := rs (se 6 (by rfl) ⟨849, by rfl⟩) (B 1699 (by norm_num) ⟨849, by rfl⟩ (by norm_num))
theorem R36269 : Reach 36269 := rs (se 3 (by rfl) ⟨6800, by rfl⟩) (B 13601 (by norm_num) ⟨6800, by rfl⟩ (by norm_num))
theorem R36293 : Reach 36293 := rs (se 4 (by rfl) ⟨3402, by rfl⟩) (B 6805 (by norm_num) ⟨3402, by rfl⟩ (by norm_num))
theorem R36317 : Reach 36317 := rs (se 3 (by rfl) ⟨6809, by rfl⟩) (B 13619 (by norm_num) ⟨6809, by rfl⟩ (by norm_num))
theorem R36325 : Reach 36325 := rs (se 4 (by rfl) ⟨3405, by rfl⟩) (B 6811 (by norm_num) ⟨3405, by rfl⟩ (by norm_num))
theorem R36341 : Reach 36341 := rs (se 5 (by rfl) ⟨1703, by rfl⟩) (B 3407 (by norm_num) ⟨1703, by rfl⟩ (by norm_num))
theorem R36365 : Reach 36365 := rs (se 3 (by rfl) ⟨6818, by rfl⟩) (B 13637 (by norm_num) ⟨6818, by rfl⟩ (by norm_num))
theorem R36389 : Reach 36389 := rs (se 4 (by rfl) ⟨3411, by rfl⟩) (B 6823 (by norm_num) ⟨3411, by rfl⟩ (by norm_num))
theorem R36413 : Reach 36413 := rs (se 3 (by rfl) ⟨6827, by rfl⟩) (B 13655 (by norm_num) ⟨6827, by rfl⟩ (by norm_num))
theorem R36437 : Reach 36437 := rs (se 8 (by rfl) ⟨213, by rfl⟩) (B 427 (by norm_num) ⟨213, by rfl⟩ (by norm_num))
theorem R36445 : Reach 36445 := rs (se 3 (by rfl) ⟨6833, by rfl⟩) (B 13667 (by norm_num) ⟨6833, by rfl⟩ (by norm_num))
theorem R36461 : Reach 36461 := rs (se 3 (by rfl) ⟨6836, by rfl⟩) (B 13673 (by norm_num) ⟨6836, by rfl⟩ (by norm_num))
theorem R102005 : Reach 102005 := rs (se 5 (by rfl) ⟨4781, by rfl⟩) (B 9563 (by norm_num) ⟨4781, by rfl⟩ (by norm_num))
theorem R36485 : Reach 36485 := rs (se 4 (by rfl) ⟨3420, by rfl⟩) (B 6841 (by norm_num) ⟨3420, by rfl⟩ (by norm_num))
theorem R36509 : Reach 36509 := rs (se 3 (by rfl) ⟨6845, by rfl⟩) (B 13691 (by norm_num) ⟨6845, by rfl⟩ (by norm_num))
theorem R36533 : Reach 36533 := rs (se 5 (by rfl) ⟨1712, by rfl⟩) (B 3425 (by norm_num) ⟨1712, by rfl⟩ (by norm_num))
theorem R36541 : Reach 36541 := rs (se 3 (by rfl) ⟨6851, by rfl⟩) (B 13703 (by norm_num) ⟨6851, by rfl⟩ (by norm_num))
theorem R36557 : Reach 36557 := rs (se 3 (by rfl) ⟨6854, by rfl⟩) (B 13709 (by norm_num) ⟨6854, by rfl⟩ (by norm_num))
theorem R36581 : Reach 36581 := rs (se 4 (by rfl) ⟨3429, by rfl⟩) (B 6859 (by norm_num) ⟨3429, by rfl⟩ (by norm_num))
theorem R36605 : Reach 36605 := rs (se 3 (by rfl) ⟨6863, by rfl⟩) (B 13727 (by norm_num) ⟨6863, by rfl⟩ (by norm_num))
theorem R36629 : Reach 36629 := rs (se 6 (by rfl) ⟨858, by rfl⟩) (B 1717 (by norm_num) ⟨858, by rfl⟩ (by norm_num))
theorem R102181 : Reach 102181 := rs (se 4 (by rfl) ⟨9579, by rfl⟩) (B 19159 (by norm_num) ⟨9579, by rfl⟩ (by norm_num))
theorem R36653 : Reach 36653 := rs (se 3 (by rfl) ⟨6872, by rfl⟩) (B 13745 (by norm_num) ⟨6872, by rfl⟩ (by norm_num))
theorem R36677 : Reach 36677 := rs (se 4 (by rfl) ⟨3438, by rfl⟩) (B 6877 (by norm_num) ⟨3438, by rfl⟩ (by norm_num))
theorem R69461 : Reach 69461 := rs (se 9 (by rfl) ⟨203, by rfl⟩) (B 407 (by norm_num) ⟨203, by rfl⟩ (by norm_num))
theorem R36701 : Reach 36701 := rs (se 3 (by rfl) ⟨6881, by rfl⟩) (B 13763 (by norm_num) ⟨6881, by rfl⟩ (by norm_num))
theorem R36725 : Reach 36725 := rs (se 5 (by rfl) ⟨1721, by rfl⟩) (B 3443 (by norm_num) ⟨1721, by rfl⟩ (by norm_num))
theorem R36749 : Reach 36749 := rs (se 3 (by rfl) ⟨6890, by rfl⟩) (B 13781 (by norm_num) ⟨6890, by rfl⟩ (by norm_num))
theorem R36773 : Reach 36773 := rs (se 4 (by rfl) ⟨3447, by rfl⟩) (B 6895 (by norm_num) ⟨3447, by rfl⟩ (by norm_num))
theorem R36797 : Reach 36797 := rs (se 3 (by rfl) ⟨6899, by rfl⟩) (B 13799 (by norm_num) ⟨6899, by rfl⟩ (by norm_num))
theorem R36821 : Reach 36821 := rs (se 7 (by rfl) ⟨431, by rfl⟩) (B 863 (by norm_num) ⟨431, by rfl⟩ (by norm_num))
theorem R36845 : Reach 36845 := rs (se 3 (by rfl) ⟨6908, by rfl⟩) (B 13817 (by norm_num) ⟨6908, by rfl⟩ (by norm_num))
theorem R36869 : Reach 36869 := rs (se 4 (by rfl) ⟨3456, by rfl⟩) (B 6913 (by norm_num) ⟨3456, by rfl⟩ (by norm_num))
theorem R36893 : Reach 36893 := rs (se 3 (by rfl) ⟨6917, by rfl⟩) (B 13835 (by norm_num) ⟨6917, by rfl⟩ (by norm_num))
theorem R36917 : Reach 36917 := rs (se 5 (by rfl) ⟨1730, by rfl⟩) (B 3461 (by norm_num) ⟨1730, by rfl⟩ (by norm_num))
theorem R36941 : Reach 36941 := rs (se 3 (by rfl) ⟨6926, by rfl⟩) (B 13853 (by norm_num) ⟨6926, by rfl⟩ (by norm_num))
theorem R102485 : Reach 102485 := rs (se 8 (by rfl) ⟨600, by rfl⟩) (B 1201 (by norm_num) ⟨600, by rfl⟩ (by norm_num))
theorem R36965 : Reach 36965 := rs (se 4 (by rfl) ⟨3465, by rfl⟩) (B 6931 (by norm_num) ⟨3465, by rfl⟩ (by norm_num))
theorem R36989 : Reach 36989 := rs (se 3 (by rfl) ⟨6935, by rfl⟩) (B 13871 (by norm_num) ⟨6935, by rfl⟩ (by norm_num))
theorem R37013 : Reach 37013 := rs (se 6 (by rfl) ⟨867, by rfl⟩) (B 1735 (by norm_num) ⟨867, by rfl⟩ (by norm_num))
theorem R37037 : Reach 37037 := rs (se 3 (by rfl) ⟨6944, by rfl⟩) (B 13889 (by norm_num) ⟨6944, by rfl⟩ (by norm_num))
theorem R37061 : Reach 37061 := rs (se 4 (by rfl) ⟨3474, by rfl⟩) (B 6949 (by norm_num) ⟨3474, by rfl⟩ (by norm_num))
theorem R37085 : Reach 37085 := rs (se 3 (by rfl) ⟨6953, by rfl⟩) (B 13907 (by norm_num) ⟨6953, by rfl⟩ (by norm_num))
theorem R37109 : Reach 37109 := rs (se 5 (by rfl) ⟨1739, by rfl⟩) (B 3479 (by norm_num) ⟨1739, by rfl⟩ (by norm_num))
theorem R69893 : Reach 69893 := rs (se 4 (by rfl) ⟨6552, by rfl⟩) (B 13105 (by norm_num) ⟨6552, by rfl⟩ (by norm_num))
theorem R37133 : Reach 37133 := rs (se 3 (by rfl) ⟨6962, by rfl⟩) (B 13925 (by norm_num) ⟨6962, by rfl⟩ (by norm_num))
theorem R299285 : Reach 299285 := rs (se 6 (by rfl) ⟨7014, by rfl⟩) (B 14029 (by norm_num) ⟨7014, by rfl⟩ (by norm_num))
theorem R69925 : Reach 69925 := rs (se 4 (by rfl) ⟨6555, by rfl⟩) (B 13111 (by norm_num) ⟨6555, by rfl⟩ (by norm_num))
theorem R37157 : Reach 37157 := rs (se 4 (by rfl) ⟨3483, by rfl⟩) (B 6967 (by norm_num) ⟨3483, by rfl⟩ (by norm_num))
theorem R37181 : Reach 37181 := rs (se 3 (by rfl) ⟨6971, by rfl⟩) (B 13943 (by norm_num) ⟨6971, by rfl⟩ (by norm_num))
theorem R37205 : Reach 37205 := rs (se 10 (by rfl) ⟨54, by rfl⟩) (B 109 (by norm_num) ⟨54, by rfl⟩ (by norm_num))
theorem R37229 : Reach 37229 := rs (se 3 (by rfl) ⟨6980, by rfl⟩) (B 13961 (by norm_num) ⟨6980, by rfl⟩ (by norm_num))
theorem R37253 : Reach 37253 := rs (se 4 (by rfl) ⟨3492, by rfl⟩) (B 6985 (by norm_num) ⟨3492, by rfl⟩ (by norm_num))
theorem R37277 : Reach 37277 := rs (se 3 (by rfl) ⟨6989, by rfl⟩) (B 13979 (by norm_num) ⟨6989, by rfl⟩ (by norm_num))
theorem R37301 : Reach 37301 := rs (se 5 (by rfl) ⟨1748, by rfl⟩) (B 3497 (by norm_num) ⟨1748, by rfl⟩ (by norm_num))
theorem R37325 : Reach 37325 := rs (se 3 (by rfl) ⟨6998, by rfl⟩) (B 13997 (by norm_num) ⟨6998, by rfl⟩ (by norm_num))
theorem R37349 : Reach 37349 := rs (se 4 (by rfl) ⟨3501, by rfl⟩) (B 7003 (by norm_num) ⟨3501, by rfl⟩ (by norm_num))
theorem R37373 : Reach 37373 := rs (se 3 (by rfl) ⟨7007, by rfl⟩) (B 14015 (by norm_num) ⟨7007, by rfl⟩ (by norm_num))
theorem R37397 : Reach 37397 := rs (se 6 (by rfl) ⟨876, by rfl⟩) (B 1753 (by norm_num) ⟨876, by rfl⟩ (by norm_num))
theorem R37421 : Reach 37421 := rs (se 3 (by rfl) ⟨7016, by rfl⟩) (B 14033 (by norm_num) ⟨7016, by rfl⟩ (by norm_num))
theorem R37445 : Reach 37445 := rs (se 4 (by rfl) ⟨3510, by rfl⟩) (B 7021 (by norm_num) ⟨3510, by rfl⟩ (by norm_num))
theorem R37469 : Reach 37469 := rs (se 3 (by rfl) ⟨7025, by rfl⟩) (B 14051 (by norm_num) ⟨7025, by rfl⟩ (by norm_num))
theorem R37493 : Reach 37493 := rs (se 5 (by rfl) ⟨1757, by rfl⟩) (B 3515 (by norm_num) ⟨1757, by rfl⟩ (by norm_num))
theorem R37517 : Reach 37517 := rs (se 3 (by rfl) ⟨7034, by rfl⟩) (B 14069 (by norm_num) ⟨7034, by rfl⟩ (by norm_num))
theorem R37541 : Reach 37541 := rs (se 4 (by rfl) ⟨3519, by rfl⟩) (B 7039 (by norm_num) ⟨3519, by rfl⟩ (by norm_num))
theorem R37565 : Reach 37565 := rs (se 3 (by rfl) ⟨7043, by rfl⟩) (B 14087 (by norm_num) ⟨7043, by rfl⟩ (by norm_num))
theorem R37589 : Reach 37589 := rs (se 7 (by rfl) ⟨440, by rfl⟩) (B 881 (by norm_num) ⟨440, by rfl⟩ (by norm_num))
theorem R37613 : Reach 37613 := rs (se 3 (by rfl) ⟨7052, by rfl⟩) (B 14105 (by norm_num) ⟨7052, by rfl⟩ (by norm_num))
theorem R37637 : Reach 37637 := rs (se 4 (by rfl) ⟨3528, by rfl⟩) (B 7057 (by norm_num) ⟨3528, by rfl⟩ (by norm_num))
theorem R37661 : Reach 37661 := rs (se 3 (by rfl) ⟨7061, by rfl⟩) (B 14123 (by norm_num) ⟨7061, by rfl⟩ (by norm_num))
theorem R37685 : Reach 37685 := rs (se 5 (by rfl) ⟨1766, by rfl⟩) (B 3533 (by norm_num) ⟨1766, by rfl⟩ (by norm_num))
theorem R37709 : Reach 37709 := rs (se 3 (by rfl) ⟨7070, by rfl⟩) (B 14141 (by norm_num) ⟨7070, by rfl⟩ (by norm_num))
theorem R37733 : Reach 37733 := rs (se 4 (by rfl) ⟨3537, by rfl⟩) (B 7075 (by norm_num) ⟨3537, by rfl⟩ (by norm_num))
theorem R37757 : Reach 37757 := rs (se 3 (by rfl) ⟨7079, by rfl⟩) (B 14159 (by norm_num) ⟨7079, by rfl⟩ (by norm_num))
theorem R37781 : Reach 37781 := rs (se 6 (by rfl) ⟨885, by rfl⟩) (B 1771 (by norm_num) ⟨885, by rfl⟩ (by norm_num))
theorem R37805 : Reach 37805 := rs (se 3 (by rfl) ⟨7088, by rfl⟩) (B 14177 (by norm_num) ⟨7088, by rfl⟩ (by norm_num))
theorem R37829 : Reach 37829 := rs (se 4 (by rfl) ⟨3546, by rfl⟩) (B 7093 (by norm_num) ⟨3546, by rfl⟩ (by norm_num))
theorem R37853 : Reach 37853 := rs (se 3 (by rfl) ⟨7097, by rfl⟩) (B 14195 (by norm_num) ⟨7097, by rfl⟩ (by norm_num))
theorem R37877 : Reach 37877 := rs (se 5 (by rfl) ⟨1775, by rfl⟩) (B 3551 (by norm_num) ⟨1775, by rfl⟩ (by norm_num))
theorem R70645 : Reach 70645 := rs (se 5 (by rfl) ⟨3311, by rfl⟩) (B 6623 (by norm_num) ⟨3311, by rfl⟩ (by norm_num))
theorem R37901 : Reach 37901 := rs (se 3 (by rfl) ⟨7106, by rfl⟩) (B 14213 (by norm_num) ⟨7106, by rfl⟩ (by norm_num))
theorem R37925 : Reach 37925 := rs (se 4 (by rfl) ⟨3555, by rfl⟩) (B 7111 (by norm_num) ⟨3555, by rfl⟩ (by norm_num))
theorem R37949 : Reach 37949 := rs (se 3 (by rfl) ⟨7115, by rfl⟩) (B 14231 (by norm_num) ⟨7115, by rfl⟩ (by norm_num))
theorem R37973 : Reach 37973 := rs (se 8 (by rfl) ⟨222, by rfl⟩) (B 445 (by norm_num) ⟨222, by rfl⟩ (by norm_num))
theorem R37997 : Reach 37997 := rs (se 3 (by rfl) ⟨7124, by rfl⟩) (B 14249 (by norm_num) ⟨7124, by rfl⟩ (by norm_num))
theorem R38021 : Reach 38021 := rs (se 4 (by rfl) ⟨3564, by rfl⟩) (B 7129 (by norm_num) ⟨3564, by rfl⟩ (by norm_num))
theorem R38045 : Reach 38045 := rs (se 3 (by rfl) ⟨7133, by rfl⟩) (B 14267 (by norm_num) ⟨7133, by rfl⟩ (by norm_num))
theorem R38069 : Reach 38069 := rs (se 5 (by rfl) ⟨1784, by rfl⟩) (B 3569 (by norm_num) ⟨1784, by rfl⟩ (by norm_num))
theorem R38093 : Reach 38093 := rs (se 3 (by rfl) ⟨7142, by rfl⟩) (B 14285 (by norm_num) ⟨7142, by rfl⟩ (by norm_num))
theorem R38117 : Reach 38117 := rs (se 4 (by rfl) ⟨3573, by rfl⟩) (B 7147 (by norm_num) ⟨3573, by rfl⟩ (by norm_num))
theorem R38141 : Reach 38141 := rs (se 3 (by rfl) ⟨7151, by rfl⟩) (B 14303 (by norm_num) ⟨7151, by rfl⟩ (by norm_num))
theorem R38165 : Reach 38165 := rs (se 6 (by rfl) ⟨894, by rfl⟩) (B 1789 (by norm_num) ⟨894, by rfl⟩ (by norm_num))
theorem R38189 : Reach 38189 := rs (se 3 (by rfl) ⟨7160, by rfl⟩) (B 14321 (by norm_num) ⟨7160, by rfl⟩ (by norm_num))
theorem R38213 : Reach 38213 := rs (se 4 (by rfl) ⟨3582, by rfl⟩) (B 7165 (by norm_num) ⟨3582, by rfl⟩ (by norm_num))
theorem R38237 : Reach 38237 := rs (se 3 (by rfl) ⟨7169, by rfl⟩) (B 14339 (by norm_num) ⟨7169, by rfl⟩ (by norm_num))
theorem R103781 : Reach 103781 := rs (se 4 (by rfl) ⟨9729, by rfl⟩) (B 19459 (by norm_num) ⟨9729, by rfl⟩ (by norm_num))
theorem R38261 : Reach 38261 := rs (se 5 (by rfl) ⟨1793, by rfl⟩) (B 3587 (by norm_num) ⟨1793, by rfl⟩ (by norm_num))
theorem R136565 : Reach 136565 := rs (se 5 (by rfl) ⟨6401, by rfl⟩) (B 12803 (by norm_num) ⟨6401, by rfl⟩ (by norm_num))
theorem R38285 : Reach 38285 := rs (se 3 (by rfl) ⟨7178, by rfl⟩) (B 14357 (by norm_num) ⟨7178, by rfl⟩ (by norm_num))
theorem R38309 : Reach 38309 := rs (se 4 (by rfl) ⟨3591, by rfl⟩) (B 7183 (by norm_num) ⟨3591, by rfl⟩ (by norm_num))
theorem R38333 : Reach 38333 := rs (se 3 (by rfl) ⟨7187, by rfl⟩) (B 14375 (by norm_num) ⟨7187, by rfl⟩ (by norm_num))
theorem R38341 : Reach 38341 := rs (se 4 (by rfl) ⟨3594, by rfl⟩) (B 7189 (by norm_num) ⟨3594, by rfl⟩ (by norm_num))
theorem R38357 : Reach 38357 := rs (se 7 (by rfl) ⟨449, by rfl⟩) (B 899 (by norm_num) ⟨449, by rfl⟩ (by norm_num))
theorem R38381 : Reach 38381 := rs (se 3 (by rfl) ⟨7196, by rfl⟩) (B 14393 (by norm_num) ⟨7196, by rfl⟩ (by norm_num))
theorem R38405 : Reach 38405 := rs (se 4 (by rfl) ⟨3600, by rfl⟩) (B 7201 (by norm_num) ⟨3600, by rfl⟩ (by norm_num))
theorem R38429 : Reach 38429 := rs (se 3 (by rfl) ⟨7205, by rfl⟩) (B 14411 (by norm_num) ⟨7205, by rfl⟩ (by norm_num))
theorem R38453 : Reach 38453 := rs (se 5 (by rfl) ⟨1802, by rfl⟩) (B 3605 (by norm_num) ⟨1802, by rfl⟩ (by norm_num))
theorem R38477 : Reach 38477 := rs (se 3 (by rfl) ⟨7214, by rfl⟩) (B 14429 (by norm_num) ⟨7214, by rfl⟩ (by norm_num))
theorem R38501 : Reach 38501 := rs (se 4 (by rfl) ⟨3609, by rfl⟩) (B 7219 (by norm_num) ⟨3609, by rfl⟩ (by norm_num))
theorem R38525 : Reach 38525 := rs (se 3 (by rfl) ⟨7223, by rfl⟩) (B 14447 (by norm_num) ⟨7223, by rfl⟩ (by norm_num))
theorem R38549 : Reach 38549 := rs (se 6 (by rfl) ⟨903, by rfl⟩) (B 1807 (by norm_num) ⟨903, by rfl⟩ (by norm_num))
theorem R38573 : Reach 38573 := rs (se 3 (by rfl) ⟨7232, by rfl⟩) (B 14465 (by norm_num) ⟨7232, by rfl⟩ (by norm_num))
theorem R136885 : Reach 136885 := rs (se 5 (by rfl) ⟨6416, by rfl⟩) (B 12833 (by norm_num) ⟨6416, by rfl⟩ (by norm_num))
theorem R38597 : Reach 38597 := rs (se 4 (by rfl) ⟨3618, by rfl⟩) (B 7237 (by norm_num) ⟨3618, by rfl⟩ (by norm_num))
theorem R38621 : Reach 38621 := rs (se 3 (by rfl) ⟨7241, by rfl⟩) (B 14483 (by norm_num) ⟨7241, by rfl⟩ (by norm_num))
theorem R104165 : Reach 104165 := rs (se 4 (by rfl) ⟨9765, by rfl⟩) (B 19531 (by norm_num) ⟨9765, by rfl⟩ (by norm_num))
theorem R38645 : Reach 38645 := rs (se 5 (by rfl) ⟨1811, by rfl⟩) (B 3623 (by norm_num) ⟨1811, by rfl⟩ (by norm_num))
theorem R38669 : Reach 38669 := rs (se 3 (by rfl) ⟨7250, by rfl⟩) (B 14501 (by norm_num) ⟨7250, by rfl⟩ (by norm_num))
theorem R38693 : Reach 38693 := rs (se 4 (by rfl) ⟨3627, by rfl⟩) (B 7255 (by norm_num) ⟨3627, by rfl⟩ (by norm_num))
theorem R38717 : Reach 38717 := rs (se 3 (by rfl) ⟨7259, by rfl⟩) (B 14519 (by norm_num) ⟨7259, by rfl⟩ (by norm_num))
theorem R38741 : Reach 38741 := rs (se 9 (by rfl) ⟨113, by rfl⟩) (B 227 (by norm_num) ⟨113, by rfl⟩ (by norm_num))
theorem R38765 : Reach 38765 := rs (se 3 (by rfl) ⟨7268, by rfl⟩) (B 14537 (by norm_num) ⟨7268, by rfl⟩ (by norm_num))
theorem R38789 : Reach 38789 := rs (se 4 (by rfl) ⟨3636, by rfl⟩) (B 7273 (by norm_num) ⟨3636, by rfl⟩ (by norm_num))
theorem R38813 : Reach 38813 := rs (se 3 (by rfl) ⟨7277, by rfl⟩) (B 14555 (by norm_num) ⟨7277, by rfl⟩ (by norm_num))
theorem R38837 : Reach 38837 := rs (se 5 (by rfl) ⟨1820, by rfl⟩) (B 3641 (by norm_num) ⟨1820, by rfl⟩ (by norm_num))
theorem R71621 : Reach 71621 := rs (se 4 (by rfl) ⟨6714, by rfl⟩) (B 13429 (by norm_num) ⟨6714, by rfl⟩ (by norm_num))
theorem R38861 : Reach 38861 := rs (se 3 (by rfl) ⟨7286, by rfl⟩) (B 14573 (by norm_num) ⟨7286, by rfl⟩ (by norm_num))
theorem R38885 : Reach 38885 := rs (se 4 (by rfl) ⟨3645, by rfl⟩) (B 7291 (by norm_num) ⟨3645, by rfl⟩ (by norm_num))
theorem R38909 : Reach 38909 := rs (se 3 (by rfl) ⟨7295, by rfl⟩) (B 14591 (by norm_num) ⟨7295, by rfl⟩ (by norm_num))
theorem R38933 : Reach 38933 := rs (se 6 (by rfl) ⟨912, by rfl⟩) (B 1825 (by norm_num) ⟨912, by rfl⟩ (by norm_num))
theorem R38957 : Reach 38957 := rs (se 3 (by rfl) ⟨7304, by rfl⟩) (B 14609 (by norm_num) ⟨7304, by rfl⟩ (by norm_num))
theorem R38981 : Reach 38981 := rs (se 4 (by rfl) ⟨3654, by rfl⟩) (B 7309 (by norm_num) ⟨3654, by rfl⟩ (by norm_num))
theorem R39005 : Reach 39005 := rs (se 3 (by rfl) ⟨7313, by rfl⟩) (B 14627 (by norm_num) ⟨7313, by rfl⟩ (by norm_num))
theorem R39029 : Reach 39029 := rs (se 5 (by rfl) ⟨1829, by rfl⟩) (B 3659 (by norm_num) ⟨1829, by rfl⟩ (by norm_num))
theorem R39053 : Reach 39053 := rs (se 3 (by rfl) ⟨7322, by rfl⟩) (B 14645 (by norm_num) ⟨7322, by rfl⟩ (by norm_num))
theorem R39077 : Reach 39077 := rs (se 4 (by rfl) ⟨3663, by rfl⟩) (B 7327 (by norm_num) ⟨3663, by rfl⟩ (by norm_num))
theorem R39101 : Reach 39101 := rs (se 3 (by rfl) ⟨7331, by rfl⟩) (B 14663 (by norm_num) ⟨7331, by rfl⟩ (by norm_num))
theorem R39125 : Reach 39125 := rs (se 7 (by rfl) ⟨458, by rfl⟩) (B 917 (by norm_num) ⟨458, by rfl⟩ (by norm_num))
theorem R39149 : Reach 39149 := rs (se 3 (by rfl) ⟨7340, by rfl⟩) (B 14681 (by norm_num) ⟨7340, by rfl⟩ (by norm_num))
theorem R39173 : Reach 39173 := rs (se 4 (by rfl) ⟨3672, by rfl⟩) (B 7345 (by norm_num) ⟨3672, by rfl⟩ (by norm_num))
theorem R366869 : Reach 366869 := rs (se 6 (by rfl) ⟨8598, by rfl⟩) (B 17197 (by norm_num) ⟨8598, by rfl⟩ (by norm_num))
theorem R39197 : Reach 39197 := rs (se 3 (by rfl) ⟨7349, by rfl⟩) (B 14699 (by norm_num) ⟨7349, by rfl⟩ (by norm_num))
theorem R39221 : Reach 39221 := rs (se 5 (by rfl) ⟨1838, by rfl⟩) (B 3677 (by norm_num) ⟨1838, by rfl⟩ (by norm_num))
theorem R39245 : Reach 39245 := rs (se 3 (by rfl) ⟨7358, by rfl⟩) (B 14717 (by norm_num) ⟨7358, by rfl⟩ (by norm_num))
theorem R39269 : Reach 39269 := rs (se 4 (by rfl) ⟨3681, by rfl⟩) (B 7363 (by norm_num) ⟨3681, by rfl⟩ (by norm_num))
theorem R39293 : Reach 39293 := rs (se 3 (by rfl) ⟨7367, by rfl⟩) (B 14735 (by norm_num) ⟨7367, by rfl⟩ (by norm_num))
theorem R39317 : Reach 39317 := rs (se 6 (by rfl) ⟨921, by rfl⟩) (B 1843 (by norm_num) ⟨921, by rfl⟩ (by norm_num))
theorem R39341 : Reach 39341 := rs (se 3 (by rfl) ⟨7376, by rfl⟩) (B 14753 (by norm_num) ⟨7376, by rfl⟩ (by norm_num))
theorem R39365 : Reach 39365 := rs (se 4 (by rfl) ⟨3690, by rfl⟩) (B 7381 (by norm_num) ⟨3690, by rfl⟩ (by norm_num))
theorem R39389 : Reach 39389 := rs (se 3 (by rfl) ⟨7385, by rfl⟩) (B 14771 (by norm_num) ⟨7385, by rfl⟩ (by norm_num))
theorem R39413 : Reach 39413 := rs (se 5 (by rfl) ⟨1847, by rfl⟩) (B 3695 (by norm_num) ⟨1847, by rfl⟩ (by norm_num))
theorem R39437 : Reach 39437 := rs (se 3 (by rfl) ⟨7394, by rfl⟩) (B 14789 (by norm_num) ⟨7394, by rfl⟩ (by norm_num))
theorem R39461 : Reach 39461 := rs (se 4 (by rfl) ⟨3699, by rfl⟩) (B 7399 (by norm_num) ⟨3699, by rfl⟩ (by norm_num))
theorem R39469 : Reach 39469 := rs (se 3 (by rfl) ⟨7400, by rfl⟩) (B 14801 (by norm_num) ⟨7400, by rfl⟩ (by norm_num))
theorem R39485 : Reach 39485 := rs (se 3 (by rfl) ⟨7403, by rfl⟩) (B 14807 (by norm_num) ⟨7403, by rfl⟩ (by norm_num))
theorem R39509 : Reach 39509 := rs (se 8 (by rfl) ⟨231, by rfl⟩) (B 463 (by norm_num) ⟨231, by rfl⟩ (by norm_num))
theorem R39533 : Reach 39533 := rs (se 3 (by rfl) ⟨7412, by rfl⟩) (B 14825 (by norm_num) ⟨7412, by rfl⟩ (by norm_num))
theorem R39557 : Reach 39557 := rs (se 4 (by rfl) ⟨3708, by rfl⟩) (B 7417 (by norm_num) ⟨3708, by rfl⟩ (by norm_num))
theorem R72325 : Reach 72325 := rs (se 4 (by rfl) ⟨6780, by rfl⟩) (B 13561 (by norm_num) ⟨6780, by rfl⟩ (by norm_num))
theorem R39581 : Reach 39581 := rs (se 3 (by rfl) ⟨7421, by rfl⟩) (B 14843 (by norm_num) ⟨7421, by rfl⟩ (by norm_num))
theorem R39605 : Reach 39605 := rs (se 5 (by rfl) ⟨1856, by rfl⟩) (B 3713 (by norm_num) ⟨1856, by rfl⟩ (by norm_num))
theorem R39629 : Reach 39629 := rs (se 3 (by rfl) ⟨7430, by rfl⟩) (B 14861 (by norm_num) ⟨7430, by rfl⟩ (by norm_num))
theorem R400085 : Reach 400085 := rs (se 7 (by rfl) ⟨4688, by rfl⟩) (B 9377 (by norm_num) ⟨4688, by rfl⟩ (by norm_num))
theorem R39653 : Reach 39653 := rs (se 4 (by rfl) ⟨3717, by rfl⟩) (B 7435 (by norm_num) ⟨3717, by rfl⟩ (by norm_num))
theorem R39677 : Reach 39677 := rs (se 3 (by rfl) ⟨7439, by rfl⟩) (B 14879 (by norm_num) ⟨7439, by rfl⟩ (by norm_num))
theorem R39701 : Reach 39701 := rs (se 6 (by rfl) ⟨930, by rfl⟩) (B 1861 (by norm_num) ⟨930, by rfl⟩ (by norm_num))
theorem R39725 : Reach 39725 := rs (se 3 (by rfl) ⟨7448, by rfl⟩) (B 14897 (by norm_num) ⟨7448, by rfl⟩ (by norm_num))
theorem R39749 : Reach 39749 := rs (se 4 (by rfl) ⟨3726, by rfl⟩) (B 7453 (by norm_num) ⟨3726, by rfl⟩ (by norm_num))
theorem R39757 : Reach 39757 := rs (se 3 (by rfl) ⟨7454, by rfl⟩) (B 14909 (by norm_num) ⟨7454, by rfl⟩ (by norm_num))
theorem R105301 : Reach 105301 := rs (se 9 (by rfl) ⟨308, by rfl⟩) (B 617 (by norm_num) ⟨308, by rfl⟩ (by norm_num))
theorem R39773 : Reach 39773 := rs (se 3 (by rfl) ⟨7457, by rfl⟩) (B 14915 (by norm_num) ⟨7457, by rfl⟩ (by norm_num))
theorem R39797 : Reach 39797 := rs (se 5 (by rfl) ⟨1865, by rfl⟩) (B 3731 (by norm_num) ⟨1865, by rfl⟩ (by norm_num))
theorem R39821 : Reach 39821 := rs (se 3 (by rfl) ⟨7466, by rfl⟩) (B 14933 (by norm_num) ⟨7466, by rfl⟩ (by norm_num))
theorem R39845 : Reach 39845 := rs (se 4 (by rfl) ⟨3735, by rfl⟩) (B 7471 (by norm_num) ⟨3735, by rfl⟩ (by norm_num))
theorem R39869 : Reach 39869 := rs (se 3 (by rfl) ⟨7475, by rfl⟩) (B 14951 (by norm_num) ⟨7475, by rfl⟩ (by norm_num))
theorem R39893 : Reach 39893 := rs (se 7 (by rfl) ⟨467, by rfl⟩) (B 935 (by norm_num) ⟨467, by rfl⟩ (by norm_num))
theorem R39917 : Reach 39917 := rs (se 3 (by rfl) ⟨7484, by rfl⟩) (B 14969 (by norm_num) ⟨7484, by rfl⟩ (by norm_num))
theorem R39941 : Reach 39941 := rs (se 4 (by rfl) ⟨3744, by rfl⟩) (B 7489 (by norm_num) ⟨3744, by rfl⟩ (by norm_num))
theorem R39965 : Reach 39965 := rs (se 3 (by rfl) ⟨7493, by rfl⟩) (B 14987 (by norm_num) ⟨7493, by rfl⟩ (by norm_num))
theorem R39973 : Reach 39973 := rs (se 4 (by rfl) ⟨3747, by rfl⟩) (B 7495 (by norm_num) ⟨3747, by rfl⟩ (by norm_num))
theorem R39989 : Reach 39989 := rs (se 5 (by rfl) ⟨1874, by rfl⟩) (B 3749 (by norm_num) ⟨1874, by rfl⟩ (by norm_num))
theorem R40013 : Reach 40013 := rs (se 3 (by rfl) ⟨7502, by rfl⟩) (B 15005 (by norm_num) ⟨7502, by rfl⟩ (by norm_num))
theorem R40037 : Reach 40037 := rs (se 4 (by rfl) ⟨3753, by rfl⟩) (B 7507 (by norm_num) ⟨3753, by rfl⟩ (by norm_num))
theorem R40061 : Reach 40061 := rs (se 3 (by rfl) ⟨7511, by rfl⟩) (B 15023 (by norm_num) ⟨7511, by rfl⟩ (by norm_num))
theorem R40085 : Reach 40085 := rs (se 6 (by rfl) ⟨939, by rfl⟩) (B 1879 (by norm_num) ⟨939, by rfl⟩ (by norm_num))
theorem R40109 : Reach 40109 := rs (se 3 (by rfl) ⟨7520, by rfl⟩) (B 15041 (by norm_num) ⟨7520, by rfl⟩ (by norm_num))
theorem R40133 : Reach 40133 := rs (se 4 (by rfl) ⟨3762, by rfl⟩) (B 7525 (by norm_num) ⟨3762, by rfl⟩ (by norm_num))
theorem R40157 : Reach 40157 := rs (se 3 (by rfl) ⟨7529, by rfl⟩) (B 15059 (by norm_num) ⟨7529, by rfl⟩ (by norm_num))
theorem R40181 : Reach 40181 := rs (se 5 (by rfl) ⟨1883, by rfl⟩) (B 3767 (by norm_num) ⟨1883, by rfl⟩ (by norm_num))
theorem R40189 : Reach 40189 := rs (se 3 (by rfl) ⟨7535, by rfl⟩) (B 15071 (by norm_num) ⟨7535, by rfl⟩ (by norm_num))
theorem R40205 : Reach 40205 := rs (se 3 (by rfl) ⟨7538, by rfl⟩) (B 15077 (by norm_num) ⟨7538, by rfl⟩ (by norm_num))
theorem R40229 : Reach 40229 := rs (se 4 (by rfl) ⟨3771, by rfl⟩) (B 7543 (by norm_num) ⟨3771, by rfl⟩ (by norm_num))
theorem R40253 : Reach 40253 := rs (se 3 (by rfl) ⟨7547, by rfl⟩) (B 15095 (by norm_num) ⟨7547, by rfl⟩ (by norm_num))
theorem R40277 : Reach 40277 := rs (se 11 (by rfl) ⟨29, by rfl⟩) (B 59 (by norm_num) ⟨29, by rfl⟩ (by norm_num))
theorem R40301 : Reach 40301 := rs (se 3 (by rfl) ⟨7556, by rfl⟩) (B 15113 (by norm_num) ⟨7556, by rfl⟩ (by norm_num))
theorem R40325 : Reach 40325 := rs (se 4 (by rfl) ⟨3780, by rfl⟩) (B 7561 (by norm_num) ⟨3780, by rfl⟩ (by norm_num))
theorem R40349 : Reach 40349 := rs (se 3 (by rfl) ⟨7565, by rfl⟩) (B 15131 (by norm_num) ⟨7565, by rfl⟩ (by norm_num))
theorem R40373 : Reach 40373 := rs (se 5 (by rfl) ⟨1892, by rfl⟩) (B 3785 (by norm_num) ⟨1892, by rfl⟩ (by norm_num))
theorem R40397 : Reach 40397 := rs (se 3 (by rfl) ⟨7574, by rfl⟩) (B 15149 (by norm_num) ⟨7574, by rfl⟩ (by norm_num))
theorem R40405 : Reach 40405 := rs (se 7 (by rfl) ⟨473, by rfl⟩) (B 947 (by norm_num) ⟨473, by rfl⟩ (by norm_num))
theorem R40421 : Reach 40421 := rs (se 4 (by rfl) ⟨3789, by rfl⟩) (B 7579 (by norm_num) ⟨3789, by rfl⟩ (by norm_num))
theorem R40445 : Reach 40445 := rs (se 3 (by rfl) ⟨7583, by rfl⟩) (B 15167 (by norm_num) ⟨7583, by rfl⟩ (by norm_num))
theorem R40469 : Reach 40469 := rs (se 6 (by rfl) ⟨948, by rfl⟩) (B 1897 (by norm_num) ⟨948, by rfl⟩ (by norm_num))
theorem R40493 : Reach 40493 := rs (se 3 (by rfl) ⟨7592, by rfl⟩) (B 15185 (by norm_num) ⟨7592, by rfl⟩ (by norm_num))
theorem R40517 : Reach 40517 := rs (se 4 (by rfl) ⟨3798, by rfl⟩) (B 7597 (by norm_num) ⟨3798, by rfl⟩ (by norm_num))
theorem R40541 : Reach 40541 := rs (se 3 (by rfl) ⟨7601, by rfl⟩) (B 15203 (by norm_num) ⟨7601, by rfl⟩ (by norm_num))
theorem R40565 : Reach 40565 := rs (se 5 (by rfl) ⟨1901, by rfl⟩) (B 3803 (by norm_num) ⟨1901, by rfl⟩ (by norm_num))
theorem R40589 : Reach 40589 := rs (se 3 (by rfl) ⟨7610, by rfl⟩) (B 15221 (by norm_num) ⟨7610, by rfl⟩ (by norm_num))
theorem R40613 : Reach 40613 := rs (se 4 (by rfl) ⟨3807, by rfl⟩) (B 7615 (by norm_num) ⟨3807, by rfl⟩ (by norm_num))
theorem R40621 : Reach 40621 := rs (se 3 (by rfl) ⟨7616, by rfl⟩) (B 15233 (by norm_num) ⟨7616, by rfl⟩ (by norm_num))
theorem R40637 : Reach 40637 := rs (se 3 (by rfl) ⟨7619, by rfl⟩) (B 15239 (by norm_num) ⟨7619, by rfl⟩ (by norm_num))
theorem R40661 : Reach 40661 := rs (se 7 (by rfl) ⟨476, by rfl⟩) (B 953 (by norm_num) ⟨476, by rfl⟩ (by norm_num))
theorem R40709 : Reach 40709 := rs (se 4 (by rfl) ⟨3816, by rfl⟩) (B 7633 (by norm_num) ⟨3816, by rfl⟩ (by norm_num))
theorem R73493 : Reach 73493 := rs (se 6 (by rfl) ⟨1722, by rfl⟩) (B 3445 (by norm_num) ⟨1722, by rfl⟩ (by norm_num))
theorem R40837 : Reach 40837 := rs (se 4 (by rfl) ⟨3828, by rfl⟩) (B 7657 (by norm_num) ⟨3828, by rfl⟩ (by norm_num))
theorem R40853 : Reach 40853 := rs (se 6 (by rfl) ⟨957, by rfl⟩) (B 1915 (by norm_num) ⟨957, by rfl⟩ (by norm_num))
theorem R434069 : Reach 434069 := rs (se 6 (by rfl) ⟨10173, by rfl⟩) (B 20347 (by norm_num) ⟨10173, by rfl⟩ (by norm_num))
theorem R171989 : Reach 171989 := rs (se 7 (by rfl) ⟨2015, by rfl⟩) (B 4031 (by norm_num) ⟨2015, by rfl⟩ (by norm_num))
theorem R40925 : Reach 40925 := rs (se 3 (by rfl) ⟨7673, by rfl⟩) (B 15347 (by norm_num) ⟨7673, by rfl⟩ (by norm_num))
theorem R40981 : Reach 40981 := rs (se 6 (by rfl) ⟨960, by rfl⟩) (B 1921 (by norm_num) ⟨960, by rfl⟩ (by norm_num))
theorem R41029 : Reach 41029 := rs (se 4 (by rfl) ⟨3846, by rfl⟩) (B 7693 (by norm_num) ⟨3846, by rfl⟩ (by norm_num))
theorem R41053 : Reach 41053 := rs (se 3 (by rfl) ⟨7697, by rfl⟩) (B 15395 (by norm_num) ⟨7697, by rfl⟩ (by norm_num))
theorem R41141 : Reach 41141 := rs (se 5 (by rfl) ⟨1928, by rfl⟩) (B 3857 (by norm_num) ⟨1928, by rfl⟩ (by norm_num))
theorem R41269 : Reach 41269 := rs (se 5 (by rfl) ⟨1934, by rfl⟩) (B 3869 (by norm_num) ⟨1934, by rfl⟩ (by norm_num))
theorem R41357 : Reach 41357 := rs (se 3 (by rfl) ⟨7754, by rfl⟩) (B 15509 (by norm_num) ⟨7754, by rfl⟩ (by norm_num))
theorem R41405 : Reach 41405 := rs (se 3 (by rfl) ⟨7763, by rfl⟩) (B 15527 (by norm_num) ⟨7763, by rfl⟩ (by norm_num))
theorem R41485 : Reach 41485 := rs (se 3 (by rfl) ⟨7778, by rfl⟩) (B 15557 (by norm_num) ⟨7778, by rfl⟩ (by norm_num))
theorem R41573 : Reach 41573 := rs (se 4 (by rfl) ⟨3897, by rfl⟩) (B 7795 (by norm_num) ⟨3897, by rfl⟩ (by norm_num))
theorem R107189 : Reach 107189 := rs (se 5 (by rfl) ⟨5024, by rfl⟩) (B 10049 (by norm_num) ⟨5024, by rfl⟩ (by norm_num))
theorem R41701 : Reach 41701 := rs (se 4 (by rfl) ⟨3909, by rfl⟩) (B 7819 (by norm_num) ⟨3909, by rfl⟩ (by norm_num))
theorem R41789 : Reach 41789 := rs (se 3 (by rfl) ⟨7835, by rfl⟩) (B 15671 (by norm_num) ⟨7835, by rfl⟩ (by norm_num))
theorem R74677 : Reach 74677 := rs (se 5 (by rfl) ⟨3500, by rfl⟩) (B 7001 (by norm_num) ⟨3500, by rfl⟩ (by norm_num))
theorem R41917 : Reach 41917 := rs (se 3 (by rfl) ⟨7859, by rfl⟩) (B 15719 (by norm_num) ⟨7859, by rfl⟩ (by norm_num))
theorem R42005 : Reach 42005 := rs (se 6 (by rfl) ⟨984, by rfl⟩) (B 1969 (by norm_num) ⟨984, by rfl⟩ (by norm_num))
theorem R74837 : Reach 74837 := rs (se 8 (by rfl) ⟨438, by rfl⟩) (B 877 (by norm_num) ⟨438, by rfl⟩ (by norm_num))
theorem R42077 : Reach 42077 := rs (se 3 (by rfl) ⟨7889, by rfl⟩) (B 15779 (by norm_num) ⟨7889, by rfl⟩ (by norm_num))
theorem R42133 : Reach 42133 := rs (se 6 (by rfl) ⟨987, by rfl⟩) (B 1975 (by norm_num) ⟨987, by rfl⟩ (by norm_num))
theorem R42221 : Reach 42221 := rs (se 3 (by rfl) ⟨7916, by rfl⟩) (B 15833 (by norm_num) ⟨7916, by rfl⟩ (by norm_num))
theorem R75077 : Reach 75077 := rs (se 4 (by rfl) ⟨7038, by rfl⟩) (B 14077 (by norm_num) ⟨7038, by rfl⟩ (by norm_num))
theorem R42349 : Reach 42349 := rs (se 3 (by rfl) ⟨7940, by rfl⟩) (B 15881 (by norm_num) ⟨7940, by rfl⟩ (by norm_num))
theorem R42437 : Reach 42437 := rs (se 4 (by rfl) ⟨3978, by rfl⟩) (B 7957 (by norm_num) ⟨3978, by rfl⟩ (by norm_num))
theorem R42493 : Reach 42493 := rs (se 3 (by rfl) ⟨7967, by rfl⟩) (B 15935 (by norm_num) ⟨7967, by rfl⟩ (by norm_num))
theorem R75269 : Reach 75269 := rs (se 4 (by rfl) ⟨7056, by rfl⟩) (B 14113 (by norm_num) ⟨7056, by rfl⟩ (by norm_num))
theorem R108053 : Reach 108053 := rs (se 6 (by rfl) ⟨2532, by rfl⟩) (B 5065 (by norm_num) ⟨2532, by rfl⟩ (by norm_num))
theorem R42565 : Reach 42565 := rs (se 4 (by rfl) ⟨3990, by rfl⟩) (B 7981 (by norm_num) ⟨3990, by rfl⟩ (by norm_num))
theorem R42653 : Reach 42653 := rs (se 3 (by rfl) ⟨7997, by rfl⟩) (B 15995 (by norm_num) ⟨7997, by rfl⟩ (by norm_num))
theorem R206549 : Reach 206549 := rs (se 7 (by rfl) ⟨2420, by rfl⟩) (B 4841 (by norm_num) ⟨2420, by rfl⟩ (by norm_num))
theorem R42781 : Reach 42781 := rs (se 3 (by rfl) ⟨8021, by rfl⟩) (B 16043 (by norm_num) ⟨8021, by rfl⟩ (by norm_num))
theorem R108325 : Reach 108325 := rs (se 4 (by rfl) ⟨10155, by rfl⟩) (B 20311 (by norm_num) ⟨10155, by rfl⟩ (by norm_num))
theorem R42805 : Reach 42805 := rs (se 5 (by rfl) ⟨2006, by rfl⟩) (B 4013 (by norm_num) ⟨2006, by rfl⟩ (by norm_num))
theorem R108373 : Reach 108373 := rs (se 9 (by rfl) ⟨317, by rfl⟩) (B 635 (by norm_num) ⟨317, by rfl⟩ (by norm_num))
theorem R42869 : Reach 42869 := rs (se 5 (by rfl) ⟨2009, by rfl⟩) (B 4019 (by norm_num) ⟨2009, by rfl⟩ (by norm_num))
theorem R108469 : Reach 108469 := rs (se 5 (by rfl) ⟨5084, by rfl⟩) (B 10169 (by norm_num) ⟨5084, by rfl⟩ (by norm_num))
theorem R42997 : Reach 42997 := rs (se 5 (by rfl) ⟨2015, by rfl⟩) (B 4031 (by norm_num) ⟨2015, by rfl⟩ (by norm_num))
theorem R43085 : Reach 43085 := rs (se 3 (by rfl) ⟨8078, by rfl⟩) (B 16157 (by norm_num) ⟨8078, by rfl⟩ (by norm_num))
theorem R43133 : Reach 43133 := rs (se 3 (by rfl) ⟨8087, by rfl⟩) (B 16175 (by norm_num) ⟨8087, by rfl⟩ (by norm_num))
theorem R43213 : Reach 43213 := rs (se 3 (by rfl) ⟨8102, by rfl⟩) (B 16205 (by norm_num) ⟨8102, by rfl⟩ (by norm_num))
theorem R43301 : Reach 43301 := rs (se 4 (by rfl) ⟨4059, by rfl⟩) (B 8119 (by norm_num) ⟨4059, by rfl⟩ (by norm_num))
theorem R43429 : Reach 43429 := rs (se 4 (by rfl) ⟨4071, by rfl⟩) (B 8143 (by norm_num) ⟨4071, by rfl⟩ (by norm_num))
theorem R76261 : Reach 76261 := rs (se 4 (by rfl) ⟨7149, by rfl⟩) (B 14299 (by norm_num) ⟨7149, by rfl⟩ (by norm_num))
theorem R43517 : Reach 43517 := rs (se 3 (by rfl) ⟨8159, by rfl⟩) (B 16319 (by norm_num) ⟨8159, by rfl⟩ (by norm_num))
theorem R43645 : Reach 43645 := rs (se 3 (by rfl) ⟨8183, by rfl⟩) (B 16367 (by norm_num) ⟨8183, by rfl⟩ (by norm_num))
theorem R43733 : Reach 43733 := rs (se 7 (by rfl) ⟨512, by rfl⟩) (B 1025 (by norm_num) ⟨512, by rfl⟩ (by norm_num))
theorem R43861 : Reach 43861 := rs (se 9 (by rfl) ⟨128, by rfl⟩) (B 257 (by norm_num) ⟨128, by rfl⟩ (by norm_num))
theorem R43949 : Reach 43949 := rs (se 3 (by rfl) ⟨8240, by rfl⟩) (B 16481 (by norm_num) ⟨8240, by rfl⟩ (by norm_num))
theorem R44077 : Reach 44077 := rs (se 3 (by rfl) ⟨8264, by rfl⟩) (B 16529 (by norm_num) ⟨8264, by rfl⟩ (by norm_num))
theorem R44165 : Reach 44165 := rs (se 4 (by rfl) ⟨4140, by rfl⟩) (B 8281 (by norm_num) ⟨4140, by rfl⟩ (by norm_num))
theorem R109829 : Reach 109829 := rs (se 4 (by rfl) ⟨10296, by rfl⟩) (B 20593 (by norm_num) ⟨10296, by rfl⟩ (by norm_num))
theorem R44293 : Reach 44293 := rs (se 4 (by rfl) ⟨4152, by rfl⟩) (B 8305 (by norm_num) ⟨4152, by rfl⟩ (by norm_num))
theorem R44381 : Reach 44381 := rs (se 3 (by rfl) ⟨8321, by rfl⟩) (B 16643 (by norm_num) ⟨8321, by rfl⟩ (by norm_num))
theorem R142805 : Reach 142805 := rs (se 7 (by rfl) ⟨1673, by rfl⟩) (B 3347 (by norm_num) ⟨1673, by rfl⟩ (by norm_num))
theorem R44509 : Reach 44509 := rs (se 3 (by rfl) ⟨8345, by rfl⟩) (B 16691 (by norm_num) ⟨8345, by rfl⟩ (by norm_num))
theorem R110069 : Reach 110069 := rs (se 5 (by rfl) ⟨5159, by rfl⟩) (B 10319 (by norm_num) ⟨5159, by rfl⟩ (by norm_num))
theorem R44597 : Reach 44597 := rs (se 5 (by rfl) ⟨2090, by rfl⟩) (B 4181 (by norm_num) ⟨2090, by rfl⟩ (by norm_num))
theorem R44621 : Reach 44621 := rs (se 3 (by rfl) ⟨8366, by rfl⟩) (B 16733 (by norm_num) ⟨8366, by rfl⟩ (by norm_num))
theorem R44725 : Reach 44725 := rs (se 5 (by rfl) ⟨2096, by rfl⟩) (B 4193 (by norm_num) ⟨2096, by rfl⟩ (by norm_num))
theorem R44813 : Reach 44813 := rs (se 3 (by rfl) ⟨8402, by rfl⟩) (B 16805 (by norm_num) ⟨8402, by rfl⟩ (by norm_num))
theorem R306965 : Reach 306965 := rs (se 6 (by rfl) ⟨7194, by rfl⟩) (B 14389 (by norm_num) ⟨7194, by rfl⟩ (by norm_num))
theorem R44941 : Reach 44941 := rs (se 3 (by rfl) ⟨8426, by rfl⟩) (B 16853 (by norm_num) ⟨8426, by rfl⟩ (by norm_num))
theorem R45029 : Reach 45029 := rs (se 4 (by rfl) ⟨4221, by rfl⟩) (B 8443 (by norm_num) ⟨4221, by rfl⟩ (by norm_num))
theorem R45037 : Reach 45037 := rs (se 3 (by rfl) ⟨8444, by rfl⟩) (B 16889 (by norm_num) ⟨8444, by rfl⟩ (by norm_num))
theorem R77861 : Reach 77861 := rs (se 4 (by rfl) ⟨7299, by rfl⟩) (B 14599 (by norm_num) ⟨7299, by rfl⟩ (by norm_num))
theorem R110645 : Reach 110645 := rs (se 5 (by rfl) ⟨5186, by rfl⟩) (B 10373 (by norm_num) ⟨5186, by rfl⟩ (by norm_num))
theorem R45157 : Reach 45157 := rs (se 4 (by rfl) ⟨4233, by rfl⟩) (B 8467 (by norm_num) ⟨4233, by rfl⟩ (by norm_num))
theorem R143477 : Reach 143477 := rs (se 5 (by rfl) ⟨6725, by rfl⟩) (B 13451 (by norm_num) ⟨6725, by rfl⟩ (by norm_num))
theorem R45181 : Reach 45181 := rs (se 3 (by rfl) ⟨8471, by rfl⟩) (B 16943 (by norm_num) ⟨8471, by rfl⟩ (by norm_num))
theorem R45245 : Reach 45245 := rs (se 3 (by rfl) ⟨8483, by rfl⟩) (B 16967 (by norm_num) ⟨8483, by rfl⟩ (by norm_num))
theorem R45293 : Reach 45293 := rs (se 3 (by rfl) ⟨8492, by rfl⟩) (B 16985 (by norm_num) ⟨8492, by rfl⟩ (by norm_num))
theorem R45373 : Reach 45373 := rs (se 3 (by rfl) ⟨8507, by rfl⟩) (B 17015 (by norm_num) ⟨8507, by rfl⟩ (by norm_num))
theorem R45461 : Reach 45461 := rs (se 6 (by rfl) ⟨1065, by rfl⟩) (B 2131 (by norm_num) ⟨1065, by rfl⟩ (by norm_num))
theorem R45517 : Reach 45517 := rs (se 3 (by rfl) ⟨8534, by rfl⟩) (B 17069 (by norm_num) ⟨8534, by rfl⟩ (by norm_num))
theorem R45589 : Reach 45589 := rs (se 6 (by rfl) ⟨1068, by rfl⟩) (B 2137 (by norm_num) ⟨1068, by rfl⟩ (by norm_num))
theorem R45677 : Reach 45677 := rs (se 3 (by rfl) ⟨8564, by rfl⟩) (B 17129 (by norm_num) ⟨8564, by rfl⟩ (by norm_num))
theorem R45821 : Reach 45821 := rs (se 3 (by rfl) ⟨8591, by rfl⟩) (B 17183 (by norm_num) ⟨8591, by rfl⟩ (by norm_num))
theorem R46109 : Reach 46109 := rs (se 3 (by rfl) ⟨8645, by rfl⟩) (B 17291 (by norm_num) ⟨8645, by rfl⟩ (by norm_num))
theorem R78965 : Reach 78965 := rs (se 5 (by rfl) ⟨3701, by rfl⟩) (B 7403 (by norm_num) ⟨3701, by rfl⟩ (by norm_num))
theorem R46261 : Reach 46261 := rs (se 5 (by rfl) ⟨2168, by rfl⟩) (B 4337 (by norm_num) ⟨2168, by rfl⟩ (by norm_num))
theorem R46421 : Reach 46421 := rs (se 13 (by rfl) ⟨8, by rfl⟩) (B 17 (by norm_num) ⟨8, by rfl⟩ (by norm_num))
theorem R46565 : Reach 46565 := rs (se 4 (by rfl) ⟨4365, by rfl⟩) (B 8731 (by norm_num) ⟨4365, by rfl⟩ (by norm_num))
theorem R79541 : Reach 79541 := rs (se 5 (by rfl) ⟨3728, by rfl⟩) (B 7457 (by norm_num) ⟨3728, by rfl⟩ (by norm_num))
theorem R112357 : Reach 112357 := rs (se 4 (by rfl) ⟨10533, by rfl⟩) (B 21067 (by norm_num) ⟨10533, by rfl⟩ (by norm_num))
theorem R79973 : Reach 79973 := rs (se 4 (by rfl) ⟨7497, by rfl⟩) (B 14995 (by norm_num) ⟨7497, by rfl⟩ (by norm_num))
theorem R47317 : Reach 47317 := rs (se 7 (by rfl) ⟨554, by rfl⟩) (B 1109 (by norm_num) ⟨554, by rfl⟩ (by norm_num))
theorem R47461 : Reach 47461 := rs (se 4 (by rfl) ⟨4449, by rfl⟩) (B 8899 (by norm_num) ⟨4449, by rfl⟩ (by norm_num))
theorem R47509 : Reach 47509 := rs (se 6 (by rfl) ⟨1113, by rfl⟩) (B 2227 (by norm_num) ⟨1113, by rfl⟩ (by norm_num))
theorem R47621 : Reach 47621 := rs (se 4 (by rfl) ⟨4464, by rfl⟩) (B 8929 (by norm_num) ⟨4464, by rfl⟩ (by norm_num))
theorem R80405 : Reach 80405 := rs (se 6 (by rfl) ⟨1884, by rfl⟩) (B 3769 (by norm_num) ⟨1884, by rfl⟩ (by norm_num))
theorem R113269 : Reach 113269 := rs (se 5 (by rfl) ⟨5309, by rfl⟩) (B 10619 (by norm_num) ⟨5309, by rfl⟩ (by norm_num))
theorem R47765 : Reach 47765 := rs (se 6 (by rfl) ⟨1119, by rfl⟩) (B 2239 (by norm_num) ⟨1119, by rfl⟩ (by norm_num))
theorem R277141 : Reach 277141 := rs (se 6 (by rfl) ⟨6495, by rfl⟩) (B 12991 (by norm_num) ⟨6495, by rfl⟩ (by norm_num))
theorem R48053 : Reach 48053 := rs (se 5 (by rfl) ⟨2252, by rfl⟩) (B 4505 (by norm_num) ⟨2252, by rfl⟩ (by norm_num))
theorem R80837 : Reach 80837 := rs (se 4 (by rfl) ⟨7578, by rfl⟩) (B 15157 (by norm_num) ⟨7578, by rfl⟩ (by norm_num))
theorem R506837 : Reach 506837 := rs (se 7 (by rfl) ⟨5939, by rfl⟩) (B 11879 (by norm_num) ⟨5939, by rfl⟩ (by norm_num))
theorem R48109 : Reach 48109 := rs (se 3 (by rfl) ⟨9020, by rfl⟩) (B 18041 (by norm_num) ⟨9020, by rfl⟩ (by norm_num))
theorem R80885 : Reach 80885 := rs (se 5 (by rfl) ⟨3791, by rfl⟩) (B 7583 (by norm_num) ⟨3791, by rfl⟩ (by norm_num))
theorem R113717 : Reach 113717 := rs (se 5 (by rfl) ⟨5330, by rfl⟩) (B 10661 (by norm_num) ⟨5330, by rfl⟩ (by norm_num))
theorem R48205 : Reach 48205 := rs (se 3 (by rfl) ⟨9038, by rfl⟩) (B 18077 (by norm_num) ⟨9038, by rfl⟩ (by norm_num))
theorem R113845 : Reach 113845 := rs (se 5 (by rfl) ⟨5336, by rfl⟩) (B 10673 (by norm_num) ⟨5336, by rfl⟩ (by norm_num))
theorem R113861 : Reach 113861 := rs (se 4 (by rfl) ⟨10674, by rfl⟩) (B 21349 (by norm_num) ⟨10674, by rfl⟩ (by norm_num))
theorem R48365 : Reach 48365 := rs (se 3 (by rfl) ⟨9068, by rfl⟩) (B 18137 (by norm_num) ⟨9068, by rfl⟩ (by norm_num))
theorem R48397 : Reach 48397 := rs (se 3 (by rfl) ⟨9074, by rfl⟩) (B 18149 (by norm_num) ⟨9074, by rfl⟩ (by norm_num))
theorem R81269 : Reach 81269 := rs (se 5 (by rfl) ⟨3809, by rfl⟩) (B 7619 (by norm_num) ⟨3809, by rfl⟩ (by norm_num))
theorem R48509 : Reach 48509 := rs (se 3 (by rfl) ⟨9095, by rfl⟩) (B 18191 (by norm_num) ⟨9095, by rfl⟩ (by norm_num))
theorem R114101 : Reach 114101 := rs (se 5 (by rfl) ⟨5348, by rfl⟩) (B 10697 (by norm_num) ⟨5348, by rfl⟩ (by norm_num))
theorem R704213 : Reach 704213 := rs (se 7 (by rfl) ⟨8252, by rfl⟩) (B 16505 (by norm_num) ⟨8252, by rfl⟩ (by norm_num))
theorem R114437 : Reach 114437 := rs (se 4 (by rfl) ⟨10728, by rfl⟩) (B 21457 (by norm_num) ⟨10728, by rfl⟩ (by norm_num))
theorem R81701 : Reach 81701 := rs (se 4 (by rfl) ⟨7659, by rfl⟩) (B 15319 (by norm_num) ⟨7659, by rfl⟩ (by norm_num))
theorem R49261 : Reach 49261 := rs (se 3 (by rfl) ⟨9236, by rfl⟩) (B 18473 (by norm_num) ⟨9236, by rfl⟩ (by norm_num))
theorem R82133 : Reach 82133 := rs (se 7 (by rfl) ⟨962, by rfl⟩) (B 1925 (by norm_num) ⟨962, by rfl⟩ (by norm_num))
theorem R49405 : Reach 49405 := rs (se 3 (by rfl) ⟨9263, by rfl⟩) (B 18527 (by norm_num) ⟨9263, by rfl⟩ (by norm_num))
theorem R49493 : Reach 49493 := rs (se 10 (by rfl) ⟨72, by rfl⟩) (B 145 (by norm_num) ⟨72, by rfl⟩ (by norm_num))
theorem R82309 : Reach 82309 := rs (se 4 (by rfl) ⟨7716, by rfl⟩) (B 15433 (by norm_num) ⟨7716, by rfl⟩ (by norm_num))
theorem R82325 : Reach 82325 := rs (se 6 (by rfl) ⟨1929, by rfl⟩) (B 3859 (by norm_num) ⟨1929, by rfl⟩ (by norm_num))
theorem R49565 : Reach 49565 := rs (se 3 (by rfl) ⟨9293, by rfl⟩) (B 18587 (by norm_num) ⟨9293, by rfl⟩ (by norm_num))
theorem R49709 : Reach 49709 := rs (se 3 (by rfl) ⟨9320, by rfl⟩) (B 18641 (by norm_num) ⟨9320, by rfl⟩ (by norm_num))
theorem R148085 : Reach 148085 := rs (se 5 (by rfl) ⟨6941, by rfl⟩) (B 13883 (by norm_num) ⟨6941, by rfl⟩ (by norm_num))
theorem R82565 : Reach 82565 := rs (se 4 (by rfl) ⟨7740, by rfl⟩) (B 15481 (by norm_num) ⟨7740, by rfl⟩ (by norm_num))
theorem R377621 : Reach 377621 := rs (se 6 (by rfl) ⟨8850, by rfl⟩) (B 17701 (by norm_num) ⟨8850, by rfl⟩ (by norm_num))
theorem R82757 : Reach 82757 := rs (se 4 (by rfl) ⟨7758, by rfl⟩) (B 15517 (by norm_num) ⟨7758, by rfl⟩ (by norm_num))
theorem R49997 : Reach 49997 := rs (se 3 (by rfl) ⟨9374, by rfl⟩) (B 18749 (by norm_num) ⟨9374, by rfl⟩ (by norm_num))
theorem R50149 : Reach 50149 := rs (se 4 (by rfl) ⟨4701, by rfl⟩) (B 9403 (by norm_num) ⟨4701, by rfl⟩ (by norm_num))
theorem R82997 : Reach 82997 := rs (se 5 (by rfl) ⟨3890, by rfl⟩) (B 7781 (by norm_num) ⟨3890, by rfl⟩ (by norm_num))
theorem R50453 : Reach 50453 := rs (se 6 (by rfl) ⟨1182, by rfl⟩) (B 2365 (by norm_num) ⟨1182, by rfl⟩ (by norm_num))
theorem R50573 : Reach 50573 := rs (se 3 (by rfl) ⟨9482, by rfl⟩) (B 18965 (by norm_num) ⟨9482, by rfl⟩ (by norm_num))
theorem R83429 : Reach 83429 := rs (se 4 (by rfl) ⟨7821, by rfl⟩) (B 15643 (by norm_num) ⟨7821, by rfl⟩ (by norm_num))
theorem R50797 : Reach 50797 := rs (se 3 (by rfl) ⟨9524, by rfl⟩) (B 19049 (by norm_num) ⟨9524, by rfl⟩ (by norm_num))
theorem R345941 : Reach 345941 := rs (se 9 (by rfl) ⟨1013, by rfl⟩) (B 2027 (by norm_num) ⟨1013, by rfl⟩ (by norm_num))
theorem R83861 : Reach 83861 := rs (se 6 (by rfl) ⟨1965, by rfl⟩) (B 3931 (by norm_num) ⟨1965, by rfl⟩ (by norm_num))
theorem R51205 : Reach 51205 := rs (se 4 (by rfl) ⟨4800, by rfl⟩) (B 9601 (by norm_num) ⟨4800, by rfl⟩ (by norm_num))
theorem R51293 : Reach 51293 := rs (se 3 (by rfl) ⟨9617, by rfl⟩) (B 19235 (by norm_num) ⟨9617, by rfl⟩ (by norm_num))
theorem R51349 : Reach 51349 := rs (se 6 (by rfl) ⟨1203, by rfl⟩) (B 2407 (by norm_num) ⟨1203, by rfl⟩ (by norm_num))
theorem R84293 : Reach 84293 := rs (se 4 (by rfl) ⟨7902, by rfl⟩) (B 15805 (by norm_num) ⟨7902, by rfl⟩ (by norm_num))
theorem R84725 : Reach 84725 := rs (se 5 (by rfl) ⟨3971, by rfl⟩) (B 7943 (by norm_num) ⟨3971, by rfl⟩ (by norm_num))
theorem R183221 : Reach 183221 := rs (se 5 (by rfl) ⟨8588, by rfl⟩) (B 17177 (by norm_num) ⟨8588, by rfl⟩ (by norm_num))
theorem R52181 : Reach 52181 := rs (se 7 (by rfl) ⟨611, by rfl⟩) (B 1223 (by norm_num) ⟨611, by rfl⟩ (by norm_num))
theorem R85013 : Reach 85013 := rs (se 6 (by rfl) ⟨1992, by rfl⟩) (B 3985 (by norm_num) ⟨1992, by rfl⟩ (by norm_num))
theorem R52301 : Reach 52301 := rs (se 3 (by rfl) ⟨9806, by rfl⟩) (B 19613 (by norm_num) ⟨9806, by rfl⟩ (by norm_num))
theorem R85157 : Reach 85157 := rs (se 4 (by rfl) ⟨7983, by rfl⟩) (B 15967 (by norm_num) ⟨7983, by rfl⟩ (by norm_num))
theorem R85589 : Reach 85589 := rs (se 8 (by rfl) ⟨501, by rfl⟩) (B 1003 (by norm_num) ⟨501, by rfl⟩ (by norm_num))
theorem R52901 : Reach 52901 := rs (se 4 (by rfl) ⟨4959, by rfl⟩) (B 9919 (by norm_num) ⟨4959, by rfl⟩ (by norm_num))
theorem R52933 : Reach 52933 := rs (se 4 (by rfl) ⟨4962, by rfl⟩) (B 9925 (by norm_num) ⟨4962, by rfl⟩ (by norm_num))
theorem R52973 : Reach 52973 := rs (se 3 (by rfl) ⟨9932, by rfl⟩) (B 19865 (by norm_num) ⟨9932, by rfl⟩ (by norm_num))
theorem R53045 : Reach 53045 := rs (se 5 (by rfl) ⟨2486, by rfl⟩) (B 4973 (by norm_num) ⟨2486, by rfl⟩ (by norm_num))
theorem R53117 : Reach 53117 := rs (se 3 (by rfl) ⟨9959, by rfl⟩) (B 19919 (by norm_num) ⟨9959, by rfl⟩ (by norm_num))
theorem R53149 : Reach 53149 := rs (se 3 (by rfl) ⟨9965, by rfl⟩) (B 19931 (by norm_num) ⟨9965, by rfl⟩ (by norm_num))
theorem R53189 : Reach 53189 := rs (se 4 (by rfl) ⟨4986, by rfl⟩) (B 9973 (by norm_num) ⟨4986, by rfl⟩ (by norm_num))
theorem R151541 : Reach 151541 := rs (se 5 (by rfl) ⟨7103, by rfl⟩) (B 14207 (by norm_num) ⟨7103, by rfl⟩ (by norm_num))
theorem R86021 : Reach 86021 := rs (se 4 (by rfl) ⟨8064, by rfl⟩) (B 16129 (by norm_num) ⟨8064, by rfl⟩ (by norm_num))
theorem R53261 : Reach 53261 := rs (se 3 (by rfl) ⟨9986, by rfl⟩) (B 19973 (by norm_num) ⟨9986, by rfl⟩ (by norm_num))
theorem R1527893 : Reach 1527893 := rs (se 8 (by rfl) ⟨8952, by rfl⟩) (B 17905 (by norm_num) ⟨8952, by rfl⟩ (by norm_num))
theorem R53333 : Reach 53333 := rs (se 8 (by rfl) ⟨312, by rfl⟩) (B 625 (by norm_num) ⟨312, by rfl⟩ (by norm_num))
theorem R53405 : Reach 53405 := rs (se 3 (by rfl) ⟨10013, by rfl⟩) (B 20027 (by norm_num) ⟨10013, by rfl⟩ (by norm_num))
theorem R250037 : Reach 250037 := rs (se 5 (by rfl) ⟨11720, by rfl⟩) (B 23441 (by norm_num) ⟨11720, by rfl⟩ (by norm_num))
theorem R53477 : Reach 53477 := rs (se 4 (by rfl) ⟨5013, by rfl⟩) (B 10027 (by norm_num) ⟨5013, by rfl⟩ (by norm_num))
theorem R53549 : Reach 53549 := rs (se 3 (by rfl) ⟨10040, by rfl⟩) (B 20081 (by norm_num) ⟨10040, by rfl⟩ (by norm_num))
theorem R53621 : Reach 53621 := rs (se 5 (by rfl) ⟨2513, by rfl⟩) (B 5027 (by norm_num) ⟨2513, by rfl⟩ (by norm_num))
theorem R86453 : Reach 86453 := rs (se 5 (by rfl) ⟨4052, by rfl⟩) (B 8105 (by norm_num) ⟨4052, by rfl⟩ (by norm_num))
theorem R53693 : Reach 53693 := rs (se 3 (by rfl) ⟨10067, by rfl⟩) (B 20135 (by norm_num) ⟨10067, by rfl⟩ (by norm_num))
theorem R53765 : Reach 53765 := rs (se 4 (by rfl) ⟨5040, by rfl⟩) (B 10081 (by norm_num) ⟨5040, by rfl⟩ (by norm_num))
theorem R53821 : Reach 53821 := rs (se 3 (by rfl) ⟨10091, by rfl⟩) (B 20183 (by norm_num) ⟨10091, by rfl⟩ (by norm_num))
theorem R53837 : Reach 53837 := rs (se 3 (by rfl) ⟨10094, by rfl⟩) (B 20189 (by norm_num) ⟨10094, by rfl⟩ (by norm_num))
theorem R53909 : Reach 53909 := rs (se 6 (by rfl) ⟨1263, by rfl⟩) (B 2527 (by norm_num) ⟨1263, by rfl⟩ (by norm_num))
theorem R53941 : Reach 53941 := rs (se 5 (by rfl) ⟨2528, by rfl⟩) (B 5057 (by norm_num) ⟨2528, by rfl⟩ (by norm_num))
theorem R53981 : Reach 53981 := rs (se 3 (by rfl) ⟨10121, by rfl⟩) (B 20243 (by norm_num) ⟨10121, by rfl⟩ (by norm_num))
theorem R53989 : Reach 53989 := rs (se 4 (by rfl) ⟨5061, by rfl⟩) (B 10123 (by norm_num) ⟨5061, by rfl⟩ (by norm_num))
theorem R54053 : Reach 54053 := rs (se 4 (by rfl) ⟨5067, by rfl⟩) (B 10135 (by norm_num) ⟨5067, by rfl⟩ (by norm_num))
theorem R54101 : Reach 54101 := rs (se 9 (by rfl) ⟨158, by rfl⟩) (B 317 (by norm_num) ⟨158, by rfl⟩ (by norm_num))
theorem R86885 : Reach 86885 := rs (se 4 (by rfl) ⟨8145, by rfl⟩) (B 16291 (by norm_num) ⟨8145, by rfl⟩ (by norm_num))
theorem R54125 : Reach 54125 := rs (se 3 (by rfl) ⟨10148, by rfl⟩) (B 20297 (by norm_num) ⟨10148, by rfl⟩ (by norm_num))
theorem R119717 : Reach 119717 := rs (se 4 (by rfl) ⟨11223, by rfl⟩) (B 22447 (by norm_num) ⟨11223, by rfl⟩ (by norm_num))
theorem R54197 : Reach 54197 := rs (se 5 (by rfl) ⟨2540, by rfl⟩) (B 5081 (by norm_num) ⟨2540, by rfl⟩ (by norm_num))
theorem R807893 : Reach 807893 := rs (se 7 (by rfl) ⟨9467, by rfl⟩) (B 18935 (by norm_num) ⟨9467, by rfl⟩ (by norm_num))
theorem R54269 : Reach 54269 := rs (se 3 (by rfl) ⟨10175, by rfl⟩) (B 20351 (by norm_num) ⟨10175, by rfl⟩ (by norm_num))
theorem R54317 : Reach 54317 := rs (se 3 (by rfl) ⟨10184, by rfl⟩) (B 20369 (by norm_num) ⟨10184, by rfl⟩ (by norm_num))
theorem R54341 : Reach 54341 := rs (se 4 (by rfl) ⟨5094, by rfl⟩) (B 10189 (by norm_num) ⟨5094, by rfl⟩ (by norm_num))
theorem R119893 : Reach 119893 := rs (se 8 (by rfl) ⟨702, by rfl⟩) (B 1405 (by norm_num) ⟨702, by rfl⟩ (by norm_num))
theorem R54413 : Reach 54413 := rs (se 3 (by rfl) ⟨10202, by rfl⟩) (B 20405 (by norm_num) ⟨10202, by rfl⟩ (by norm_num))
theorem R152725 : Reach 152725 := rs (se 6 (by rfl) ⟨3579, by rfl⟩) (B 7159 (by norm_num) ⟨3579, by rfl⟩ (by norm_num))
theorem R54485 : Reach 54485 := rs (se 7 (by rfl) ⟨638, by rfl⟩) (B 1277 (by norm_num) ⟨638, by rfl⟩ (by norm_num))
theorem R87317 : Reach 87317 := rs (se 6 (by rfl) ⟨2046, by rfl⟩) (B 4093 (by norm_num) ⟨2046, by rfl⟩ (by norm_num))
theorem R54557 : Reach 54557 := rs (se 3 (by rfl) ⟨10229, by rfl⟩) (B 20459 (by norm_num) ⟨10229, by rfl⟩ (by norm_num))
theorem R54629 : Reach 54629 := rs (se 4 (by rfl) ⟨5121, by rfl⟩) (B 10243 (by norm_num) ⟨5121, by rfl⟩ (by norm_num))
theorem R54701 : Reach 54701 := rs (se 3 (by rfl) ⟨10256, by rfl⟩) (B 20513 (by norm_num) ⟨10256, by rfl⟩ (by norm_num))
theorem R54773 : Reach 54773 := rs (se 5 (by rfl) ⟨2567, by rfl⟩) (B 5135 (by norm_num) ⟨2567, by rfl⟩ (by norm_num))
theorem R54845 : Reach 54845 := rs (se 3 (by rfl) ⟨10283, by rfl⟩) (B 20567 (by norm_num) ⟨10283, by rfl⟩ (by norm_num))
theorem R54917 : Reach 54917 := rs (se 4 (by rfl) ⟨5148, by rfl⟩) (B 10297 (by norm_num) ⟨5148, by rfl⟩ (by norm_num))
theorem R284309 : Reach 284309 := rs (se 6 (by rfl) ⟨6663, by rfl⟩) (B 13327 (by norm_num) ⟨6663, by rfl⟩ (by norm_num))
theorem R87749 : Reach 87749 := rs (se 4 (by rfl) ⟨8226, by rfl⟩) (B 16453 (by norm_num) ⟨8226, by rfl⟩ (by norm_num))
theorem R54989 : Reach 54989 := rs (se 3 (by rfl) ⟨10310, by rfl⟩) (B 20621 (by norm_num) ⟨10310, by rfl⟩ (by norm_num))
theorem R55061 : Reach 55061 := rs (se 6 (by rfl) ⟨1290, by rfl⟩) (B 2581 (by norm_num) ⟨1290, by rfl⟩ (by norm_num))
theorem R55085 : Reach 55085 := rs (se 3 (by rfl) ⟨10328, by rfl⟩) (B 20657 (by norm_num) ⟨10328, by rfl⟩ (by norm_num))
theorem R55133 : Reach 55133 := rs (se 3 (by rfl) ⟨10337, by rfl⟩) (B 20675 (by norm_num) ⟨10337, by rfl⟩ (by norm_num))
theorem R55205 : Reach 55205 := rs (se 4 (by rfl) ⟨5175, by rfl⟩) (B 10351 (by norm_num) ⟨5175, by rfl⟩ (by norm_num))
theorem R55277 : Reach 55277 := rs (se 3 (by rfl) ⟨10364, by rfl⟩) (B 20729 (by norm_num) ⟨10364, by rfl⟩ (by norm_num))
theorem R55325 : Reach 55325 := rs (se 3 (by rfl) ⟨10373, by rfl⟩) (B 20747 (by norm_num) ⟨10373, by rfl⟩ (by norm_num))
theorem R55349 : Reach 55349 := rs (se 5 (by rfl) ⟨2594, by rfl⟩) (B 5189 (by norm_num) ⟨2594, by rfl⟩ (by norm_num))
theorem R88181 : Reach 88181 := rs (se 5 (by rfl) ⟨4133, by rfl⟩) (B 8267 (by norm_num) ⟨4133, by rfl⟩ (by norm_num))
theorem R55421 : Reach 55421 := rs (se 3 (by rfl) ⟨10391, by rfl⟩) (B 20783 (by norm_num) ⟨10391, by rfl⟩ (by norm_num))
theorem R88229 : Reach 88229 := rs (se 4 (by rfl) ⟨8271, by rfl⟩) (B 16543 (by norm_num) ⟨8271, by rfl⟩ (by norm_num))
theorem R121013 : Reach 121013 := rs (se 5 (by rfl) ⟨5672, by rfl⟩) (B 11345 (by norm_num) ⟨5672, by rfl⟩ (by norm_num))
theorem R55493 : Reach 55493 := rs (se 4 (by rfl) ⟨5202, by rfl⟩) (B 10405 (by norm_num) ⟨5202, by rfl⟩ (by norm_num))
theorem R55565 : Reach 55565 := rs (se 3 (by rfl) ⟨10418, by rfl⟩) (B 20837 (by norm_num) ⟨10418, by rfl⟩ (by norm_num))
theorem R55637 : Reach 55637 := rs (se 10 (by rfl) ⟨81, by rfl⟩) (B 163 (by norm_num) ⟨81, by rfl⟩ (by norm_num))
theorem R55709 : Reach 55709 := rs (se 3 (by rfl) ⟨10445, by rfl⟩) (B 20891 (by norm_num) ⟨10445, by rfl⟩ (by norm_num))
theorem R55781 : Reach 55781 := rs (se 4 (by rfl) ⟨5229, by rfl⟩) (B 10459 (by norm_num) ⟨5229, by rfl⟩ (by norm_num))
theorem R55829 : Reach 55829 := rs (se 6 (by rfl) ⟨1308, by rfl⟩) (B 2617 (by norm_num) ⟨1308, by rfl⟩ (by norm_num))
theorem R55837 : Reach 55837 := rs (se 3 (by rfl) ⟨10469, by rfl⟩) (B 20939 (by norm_num) ⟨10469, by rfl⟩ (by norm_num))
theorem R88613 : Reach 88613 := rs (se 4 (by rfl) ⟨8307, by rfl⟩) (B 16615 (by norm_num) ⟨8307, by rfl⟩ (by norm_num))
theorem R55853 : Reach 55853 := rs (se 3 (by rfl) ⟨10472, by rfl⟩) (B 20945 (by norm_num) ⟨10472, by rfl⟩ (by norm_num))
theorem R55925 : Reach 55925 := rs (se 5 (by rfl) ⟨2621, by rfl⟩) (B 5243 (by norm_num) ⟨2621, by rfl⟩ (by norm_num))
theorem R55997 : Reach 55997 := rs (se 3 (by rfl) ⟨10499, by rfl⟩) (B 20999 (by norm_num) ⟨10499, by rfl⟩ (by norm_num))
theorem R56069 : Reach 56069 := rs (se 4 (by rfl) ⟨5256, by rfl⟩) (B 10513 (by norm_num) ⟨5256, by rfl⟩ (by norm_num))
theorem R56141 : Reach 56141 := rs (se 3 (by rfl) ⟨10526, by rfl⟩) (B 21053 (by norm_num) ⟨10526, by rfl⟩ (by norm_num))
theorem R56213 : Reach 56213 := rs (se 6 (by rfl) ⟨1317, by rfl⟩) (B 2635 (by norm_num) ⟨1317, by rfl⟩ (by norm_num))
theorem R23501 : Reach 23501 := rs (se 3 (by rfl) ⟨4406, by rfl⟩) (B 8813 (by norm_num) ⟨4406, by rfl⟩ (by norm_num))
theorem R23505 : Reach 23505 := rs (se 2 (by rfl) ⟨8814, by rfl⟩) (B 17629 (by norm_num) ⟨8814, by rfl⟩ (by norm_num))
theorem R23509 : Reach 23509 := rs (se 7 (by rfl) ⟨275, by rfl⟩) (B 551 (by norm_num) ⟨275, by rfl⟩ (by norm_num))
theorem R89045 : Reach 89045 := rs (se 7 (by rfl) ⟨1043, by rfl⟩) (B 2087 (by norm_num) ⟨1043, by rfl⟩ (by norm_num))
theorem R23513 : Reach 23513 := rs (se 2 (by rfl) ⟨8817, by rfl⟩) (B 17635 (by norm_num) ⟨8817, by rfl⟩ (by norm_num))
theorem R23517 : Reach 23517 := rs (se 3 (by rfl) ⟨4409, by rfl⟩) (B 8819 (by norm_num) ⟨4409, by rfl⟩ (by norm_num))
theorem R56285 : Reach 56285 := rs (se 3 (by rfl) ⟨10553, by rfl⟩) (B 21107 (by norm_num) ⟨10553, by rfl⟩ (by norm_num))
theorem R23521 : Reach 23521 := rs (se 2 (by rfl) ⟨8820, by rfl⟩) (B 17641 (by norm_num) ⟨8820, by rfl⟩ (by norm_num))
theorem R23525 : Reach 23525 := rs (se 4 (by rfl) ⟨2205, by rfl⟩) (B 4411 (by norm_num) ⟨2205, by rfl⟩ (by norm_num))
theorem R23529 : Reach 23529 := rs (se 2 (by rfl) ⟨8823, by rfl⟩) (B 17647 (by norm_num) ⟨8823, by rfl⟩ (by norm_num))
theorem R23533 : Reach 23533 := rs (se 3 (by rfl) ⟨4412, by rfl⟩) (B 8825 (by norm_num) ⟨4412, by rfl⟩ (by norm_num))
theorem R23537 : Reach 23537 := rs (se 2 (by rfl) ⟨8826, by rfl⟩) (B 17653 (by norm_num) ⟨8826, by rfl⟩ (by norm_num))
theorem R23541 : Reach 23541 := rs (se 5 (by rfl) ⟨1103, by rfl⟩) (B 2207 (by norm_num) ⟨1103, by rfl⟩ (by norm_num))
theorem R23545 : Reach 23545 := rs (se 2 (by rfl) ⟨8829, by rfl⟩) (B 17659 (by norm_num) ⟨8829, by rfl⟩ (by norm_num))
theorem R23549 : Reach 23549 := rs (se 3 (by rfl) ⟨4415, by rfl⟩) (B 8831 (by norm_num) ⟨4415, by rfl⟩ (by norm_num))
theorem R23553 : Reach 23553 := rs (se 2 (by rfl) ⟨8832, by rfl⟩) (B 17665 (by norm_num) ⟨8832, by rfl⟩ (by norm_num))
theorem R23557 : Reach 23557 := rs (se 4 (by rfl) ⟨2208, by rfl⟩) (B 4417 (by norm_num) ⟨2208, by rfl⟩ (by norm_num))
theorem R23561 : Reach 23561 := rs (se 2 (by rfl) ⟨8835, by rfl⟩) (B 17671 (by norm_num) ⟨8835, by rfl⟩ (by norm_num))
theorem R23565 : Reach 23565 := rs (se 3 (by rfl) ⟨4418, by rfl⟩) (B 8837 (by norm_num) ⟨4418, by rfl⟩ (by norm_num))
theorem R23569 : Reach 23569 := rs (se 2 (by rfl) ⟨8838, by rfl⟩) (B 17677 (by norm_num) ⟨8838, by rfl⟩ (by norm_num))
theorem R23573 : Reach 23573 := rs (se 6 (by rfl) ⟨552, by rfl⟩) (B 1105 (by norm_num) ⟨552, by rfl⟩ (by norm_num))
theorem R23577 : Reach 23577 := rs (se 2 (by rfl) ⟨8841, by rfl⟩) (B 17683 (by norm_num) ⟨8841, by rfl⟩ (by norm_num))
theorem R23581 : Reach 23581 := rs (se 3 (by rfl) ⟨4421, by rfl⟩) (B 8843 (by norm_num) ⟨4421, by rfl⟩ (by norm_num))
theorem R23585 : Reach 23585 := rs (se 2 (by rfl) ⟨8844, by rfl⟩) (B 17689 (by norm_num) ⟨8844, by rfl⟩ (by norm_num))
theorem R23589 : Reach 23589 := rs (se 4 (by rfl) ⟨2211, by rfl⟩) (B 4423 (by norm_num) ⟨2211, by rfl⟩ (by norm_num))
theorem R56357 : Reach 56357 := rs (se 4 (by rfl) ⟨5283, by rfl⟩) (B 10567 (by norm_num) ⟨5283, by rfl⟩ (by norm_num))
theorem R23593 : Reach 23593 := rs (se 2 (by rfl) ⟨8847, by rfl⟩) (B 17695 (by norm_num) ⟨8847, by rfl⟩ (by norm_num))
theorem R23597 : Reach 23597 := rs (se 3 (by rfl) ⟨4424, by rfl⟩) (B 8849 (by norm_num) ⟨4424, by rfl⟩ (by norm_num))
theorem R23601 : Reach 23601 := rs (se 2 (by rfl) ⟨8850, by rfl⟩) (B 17701 (by norm_num) ⟨8850, by rfl⟩ (by norm_num))
theorem R23605 : Reach 23605 := rs (se 5 (by rfl) ⟨1106, by rfl⟩) (B 2213 (by norm_num) ⟨1106, by rfl⟩ (by norm_num))
theorem R23609 : Reach 23609 := rs (se 2 (by rfl) ⟨8853, by rfl⟩) (B 17707 (by norm_num) ⟨8853, by rfl⟩ (by norm_num))
theorem R23613 : Reach 23613 := rs (se 3 (by rfl) ⟨4427, by rfl⟩) (B 8855 (by norm_num) ⟨4427, by rfl⟩ (by norm_num))
theorem R23617 : Reach 23617 := rs (se 2 (by rfl) ⟨8856, by rfl⟩) (B 17713 (by norm_num) ⟨8856, by rfl⟩ (by norm_num))
theorem R23621 : Reach 23621 := rs (se 4 (by rfl) ⟨2214, by rfl⟩) (B 4429 (by norm_num) ⟨2214, by rfl⟩ (by norm_num))
theorem R121925 : Reach 121925 := rs (se 4 (by rfl) ⟨11430, by rfl⟩) (B 22861 (by norm_num) ⟨11430, by rfl⟩ (by norm_num))
theorem R23625 : Reach 23625 := rs (se 2 (by rfl) ⟨8859, by rfl⟩) (B 17719 (by norm_num) ⟨8859, by rfl⟩ (by norm_num))
theorem R23629 : Reach 23629 := rs (se 3 (by rfl) ⟨4430, by rfl⟩) (B 8861 (by norm_num) ⟨4430, by rfl⟩ (by norm_num))
theorem R23633 : Reach 23633 := rs (se 2 (by rfl) ⟨8862, by rfl⟩) (B 17725 (by norm_num) ⟨8862, by rfl⟩ (by norm_num))
theorem R23637 : Reach 23637 := rs (se 8 (by rfl) ⟨138, by rfl⟩) (B 277 (by norm_num) ⟨138, by rfl⟩ (by norm_num))
theorem R154709 : Reach 154709 := rs (se 8 (by rfl) ⟨906, by rfl⟩) (B 1813 (by norm_num) ⟨906, by rfl⟩ (by norm_num))
theorem R23641 : Reach 23641 := rs (se 2 (by rfl) ⟨8865, by rfl⟩) (B 17731 (by norm_num) ⟨8865, by rfl⟩ (by norm_num))
theorem R23645 : Reach 23645 := rs (se 3 (by rfl) ⟨4433, by rfl⟩) (B 8867 (by norm_num) ⟨4433, by rfl⟩ (by norm_num))
theorem R23649 : Reach 23649 := rs (se 2 (by rfl) ⟨8868, by rfl⟩) (B 17737 (by norm_num) ⟨8868, by rfl⟩ (by norm_num))
theorem R23653 : Reach 23653 := rs (se 4 (by rfl) ⟨2217, by rfl⟩) (B 4435 (by norm_num) ⟨2217, by rfl⟩ (by norm_num))
theorem R23657 : Reach 23657 := rs (se 2 (by rfl) ⟨8871, by rfl⟩) (B 17743 (by norm_num) ⟨8871, by rfl⟩ (by norm_num))
theorem R23661 : Reach 23661 := rs (se 3 (by rfl) ⟨4436, by rfl⟩) (B 8873 (by norm_num) ⟨4436, by rfl⟩ (by norm_num))
theorem R56429 : Reach 56429 := rs (se 3 (by rfl) ⟨10580, by rfl⟩) (B 21161 (by norm_num) ⟨10580, by rfl⟩ (by norm_num))
theorem R23665 : Reach 23665 := rs (se 2 (by rfl) ⟨8874, by rfl⟩) (B 17749 (by norm_num) ⟨8874, by rfl⟩ (by norm_num))
theorem R23669 : Reach 23669 := rs (se 5 (by rfl) ⟨1109, by rfl⟩) (B 2219 (by norm_num) ⟨1109, by rfl⟩ (by norm_num))
theorem R23673 : Reach 23673 := rs (se 2 (by rfl) ⟨8877, by rfl⟩) (B 17755 (by norm_num) ⟨8877, by rfl⟩ (by norm_num))
theorem R23677 : Reach 23677 := rs (se 3 (by rfl) ⟨4439, by rfl⟩) (B 8879 (by norm_num) ⟨4439, by rfl⟩ (by norm_num))
theorem R23681 : Reach 23681 := rs (se 2 (by rfl) ⟨8880, by rfl⟩) (B 17761 (by norm_num) ⟨8880, by rfl⟩ (by norm_num))
theorem R23685 : Reach 23685 := rs (se 4 (by rfl) ⟨2220, by rfl⟩) (B 4441 (by norm_num) ⟨2220, by rfl⟩ (by norm_num))
theorem R23689 : Reach 23689 := rs (se 2 (by rfl) ⟨8883, by rfl⟩) (B 17767 (by norm_num) ⟨8883, by rfl⟩ (by norm_num))
theorem R23693 : Reach 23693 := rs (se 3 (by rfl) ⟨4442, by rfl⟩) (B 8885 (by norm_num) ⟨4442, by rfl⟩ (by norm_num))
theorem R23697 : Reach 23697 := rs (se 2 (by rfl) ⟨8886, by rfl⟩) (B 17773 (by norm_num) ⟨8886, by rfl⟩ (by norm_num))
theorem R23701 : Reach 23701 := rs (se 6 (by rfl) ⟨555, by rfl⟩) (B 1111 (by norm_num) ⟨555, by rfl⟩ (by norm_num))
theorem R23705 : Reach 23705 := rs (se 2 (by rfl) ⟨8889, by rfl⟩) (B 17779 (by norm_num) ⟨8889, by rfl⟩ (by norm_num))
theorem R23709 : Reach 23709 := rs (se 3 (by rfl) ⟨4445, by rfl⟩) (B 8891 (by norm_num) ⟨4445, by rfl⟩ (by norm_num))
theorem R23713 : Reach 23713 := rs (se 2 (by rfl) ⟨8892, by rfl⟩) (B 17785 (by norm_num) ⟨8892, by rfl⟩ (by norm_num))
theorem R23717 : Reach 23717 := rs (se 4 (by rfl) ⟨2223, by rfl⟩) (B 4447 (by norm_num) ⟨2223, by rfl⟩ (by norm_num))
theorem R23721 : Reach 23721 := rs (se 2 (by rfl) ⟨8895, by rfl⟩) (B 17791 (by norm_num) ⟨8895, by rfl⟩ (by norm_num))
theorem R23725 : Reach 23725 := rs (se 3 (by rfl) ⟨4448, by rfl⟩) (B 8897 (by norm_num) ⟨4448, by rfl⟩ (by norm_num))
theorem R23729 : Reach 23729 := rs (se 2 (by rfl) ⟨8898, by rfl⟩) (B 17797 (by norm_num) ⟨8898, by rfl⟩ (by norm_num))
theorem R23733 : Reach 23733 := rs (se 5 (by rfl) ⟨1112, by rfl⟩) (B 2225 (by norm_num) ⟨1112, by rfl⟩ (by norm_num))
theorem R56501 : Reach 56501 := rs (se 5 (by rfl) ⟨2648, by rfl⟩) (B 5297 (by norm_num) ⟨2648, by rfl⟩ (by norm_num))
theorem R23737 : Reach 23737 := rs (se 2 (by rfl) ⟨8901, by rfl⟩) (B 17803 (by norm_num) ⟨8901, by rfl⟩ (by norm_num))
theorem R23741 : Reach 23741 := rs (se 3 (by rfl) ⟨4451, by rfl⟩) (B 8903 (by norm_num) ⟨4451, by rfl⟩ (by norm_num))
theorem R23745 : Reach 23745 := rs (se 2 (by rfl) ⟨8904, by rfl⟩) (B 17809 (by norm_num) ⟨8904, by rfl⟩ (by norm_num))
theorem R23749 : Reach 23749 := rs (se 4 (by rfl) ⟨2226, by rfl⟩) (B 4453 (by norm_num) ⟨2226, by rfl⟩ (by norm_num))
theorem R23753 : Reach 23753 := rs (se 2 (by rfl) ⟨8907, by rfl⟩) (B 17815 (by norm_num) ⟨8907, by rfl⟩ (by norm_num))
theorem R23757 : Reach 23757 := rs (se 3 (by rfl) ⟨4454, by rfl⟩) (B 8909 (by norm_num) ⟨4454, by rfl⟩ (by norm_num))
theorem R23761 : Reach 23761 := rs (se 2 (by rfl) ⟨8910, by rfl⟩) (B 17821 (by norm_num) ⟨8910, by rfl⟩ (by norm_num))
theorem R23765 : Reach 23765 := rs (se 7 (by rfl) ⟨278, by rfl⟩) (B 557 (by norm_num) ⟨278, by rfl⟩ (by norm_num))
theorem R23769 : Reach 23769 := rs (se 2 (by rfl) ⟨8913, by rfl⟩) (B 17827 (by norm_num) ⟨8913, by rfl⟩ (by norm_num))
theorem R23773 : Reach 23773 := rs (se 3 (by rfl) ⟨4457, by rfl⟩) (B 8915 (by norm_num) ⟨4457, by rfl⟩ (by norm_num))
theorem R23777 : Reach 23777 := rs (se 2 (by rfl) ⟨8916, by rfl⟩) (B 17833 (by norm_num) ⟨8916, by rfl⟩ (by norm_num))
theorem R23781 : Reach 23781 := rs (se 4 (by rfl) ⟨2229, by rfl⟩) (B 4459 (by norm_num) ⟨2229, by rfl⟩ (by norm_num))
theorem R23785 : Reach 23785 := rs (se 2 (by rfl) ⟨8919, by rfl⟩) (B 17839 (by norm_num) ⟨8919, by rfl⟩ (by norm_num))
theorem R23789 : Reach 23789 := rs (se 3 (by rfl) ⟨4460, by rfl⟩) (B 8921 (by norm_num) ⟨4460, by rfl⟩ (by norm_num))
theorem R23793 : Reach 23793 := rs (se 2 (by rfl) ⟨8922, by rfl⟩) (B 17845 (by norm_num) ⟨8922, by rfl⟩ (by norm_num))
theorem R89333 : Reach 89333 := rs (se 5 (by rfl) ⟨4187, by rfl⟩) (B 8375 (by norm_num) ⟨4187, by rfl⟩ (by norm_num))
theorem R23797 : Reach 23797 := rs (se 5 (by rfl) ⟨1115, by rfl⟩) (B 2231 (by norm_num) ⟨1115, by rfl⟩ (by norm_num))
theorem R23801 : Reach 23801 := rs (se 2 (by rfl) ⟨8925, by rfl⟩) (B 17851 (by norm_num) ⟨8925, by rfl⟩ (by norm_num))
theorem R23805 : Reach 23805 := rs (se 3 (by rfl) ⟨4463, by rfl⟩) (B 8927 (by norm_num) ⟨4463, by rfl⟩ (by norm_num))
theorem R56573 : Reach 56573 := rs (se 3 (by rfl) ⟨10607, by rfl⟩) (B 21215 (by norm_num) ⟨10607, by rfl⟩ (by norm_num))
theorem R23809 : Reach 23809 := rs (se 2 (by rfl) ⟨8928, by rfl⟩) (B 17857 (by norm_num) ⟨8928, by rfl⟩ (by norm_num))
theorem R23813 : Reach 23813 := rs (se 4 (by rfl) ⟨2232, by rfl⟩) (B 4465 (by norm_num) ⟨2232, by rfl⟩ (by norm_num))
theorem R23817 : Reach 23817 := rs (se 2 (by rfl) ⟨8931, by rfl⟩) (B 17863 (by norm_num) ⟨8931, by rfl⟩ (by norm_num))
theorem R23821 : Reach 23821 := rs (se 3 (by rfl) ⟨4466, by rfl⟩) (B 8933 (by norm_num) ⟨4466, by rfl⟩ (by norm_num))
theorem R23825 : Reach 23825 := rs (se 2 (by rfl) ⟨8934, by rfl⟩) (B 17869 (by norm_num) ⟨8934, by rfl⟩ (by norm_num))
theorem R23829 : Reach 23829 := rs (se 6 (by rfl) ⟨558, by rfl⟩) (B 1117 (by norm_num) ⟨558, by rfl⟩ (by norm_num))
theorem R23833 : Reach 23833 := rs (se 2 (by rfl) ⟨8937, by rfl⟩) (B 17875 (by norm_num) ⟨8937, by rfl⟩ (by norm_num))
theorem R23837 : Reach 23837 := rs (se 3 (by rfl) ⟨4469, by rfl⟩) (B 8939 (by norm_num) ⟨4469, by rfl⟩ (by norm_num))
theorem R23841 : Reach 23841 := rs (se 2 (by rfl) ⟨8940, by rfl⟩) (B 17881 (by norm_num) ⟨8940, by rfl⟩ (by norm_num))
theorem R23845 : Reach 23845 := rs (se 4 (by rfl) ⟨2235, by rfl⟩) (B 4471 (by norm_num) ⟨2235, by rfl⟩ (by norm_num))
theorem R23849 : Reach 23849 := rs (se 2 (by rfl) ⟨8943, by rfl⟩) (B 17887 (by norm_num) ⟨8943, by rfl⟩ (by norm_num))
theorem R23853 : Reach 23853 := rs (se 3 (by rfl) ⟨4472, by rfl⟩) (B 8945 (by norm_num) ⟨4472, by rfl⟩ (by norm_num))
theorem R23857 : Reach 23857 := rs (se 2 (by rfl) ⟨8946, by rfl⟩) (B 17893 (by norm_num) ⟨8946, by rfl⟩ (by norm_num))
theorem R23861 : Reach 23861 := rs (se 5 (by rfl) ⟨1118, by rfl⟩) (B 2237 (by norm_num) ⟨1118, by rfl⟩ (by norm_num))
theorem R23865 : Reach 23865 := rs (se 2 (by rfl) ⟨8949, by rfl⟩) (B 17899 (by norm_num) ⟨8949, by rfl⟩ (by norm_num))
theorem R23869 : Reach 23869 := rs (se 3 (by rfl) ⟨4475, by rfl⟩) (B 8951 (by norm_num) ⟨4475, by rfl⟩ (by norm_num))
theorem R23873 : Reach 23873 := rs (se 2 (by rfl) ⟨8952, by rfl⟩) (B 17905 (by norm_num) ⟨8952, by rfl⟩ (by norm_num))
theorem R23877 : Reach 23877 := rs (se 4 (by rfl) ⟨2238, by rfl⟩) (B 4477 (by norm_num) ⟨2238, by rfl⟩ (by norm_num))
theorem R56645 : Reach 56645 := rs (se 4 (by rfl) ⟨5310, by rfl⟩) (B 10621 (by norm_num) ⟨5310, by rfl⟩ (by norm_num))
theorem R23881 : Reach 23881 := rs (se 2 (by rfl) ⟨8955, by rfl⟩) (B 17911 (by norm_num) ⟨8955, by rfl⟩ (by norm_num))
theorem R23885 : Reach 23885 := rs (se 3 (by rfl) ⟨4478, by rfl⟩) (B 8957 (by norm_num) ⟨4478, by rfl⟩ (by norm_num))
theorem R23889 : Reach 23889 := rs (se 2 (by rfl) ⟨8958, by rfl⟩) (B 17917 (by norm_num) ⟨8958, by rfl⟩ (by norm_num))
theorem R23893 : Reach 23893 := rs (se 11 (by rfl) ⟨17, by rfl⟩) (B 35 (by norm_num) ⟨17, by rfl⟩ (by norm_num))
theorem R23897 : Reach 23897 := rs (se 2 (by rfl) ⟨8961, by rfl⟩) (B 17923 (by norm_num) ⟨8961, by rfl⟩ (by norm_num))
theorem R23901 : Reach 23901 := rs (se 3 (by rfl) ⟨4481, by rfl⟩) (B 8963 (by norm_num) ⟨4481, by rfl⟩ (by norm_num))
theorem R23905 : Reach 23905 := rs (se 2 (by rfl) ⟨8964, by rfl⟩) (B 17929 (by norm_num) ⟨8964, by rfl⟩ (by norm_num))
theorem R23909 : Reach 23909 := rs (se 4 (by rfl) ⟨2241, by rfl⟩) (B 4483 (by norm_num) ⟨2241, by rfl⟩ (by norm_num))
theorem R23913 : Reach 23913 := rs (se 2 (by rfl) ⟨8967, by rfl⟩) (B 17935 (by norm_num) ⟨8967, by rfl⟩ (by norm_num))
theorem R23917 : Reach 23917 := rs (se 3 (by rfl) ⟨4484, by rfl⟩) (B 8969 (by norm_num) ⟨4484, by rfl⟩ (by norm_num))
theorem R23921 : Reach 23921 := rs (se 2 (by rfl) ⟨8970, by rfl⟩) (B 17941 (by norm_num) ⟨8970, by rfl⟩ (by norm_num))
theorem R23925 : Reach 23925 := rs (se 5 (by rfl) ⟨1121, by rfl⟩) (B 2243 (by norm_num) ⟨1121, by rfl⟩ (by norm_num))
theorem R23929 : Reach 23929 := rs (se 2 (by rfl) ⟨8973, by rfl⟩) (B 17947 (by norm_num) ⟨8973, by rfl⟩ (by norm_num))
theorem R23933 : Reach 23933 := rs (se 3 (by rfl) ⟨4487, by rfl⟩) (B 8975 (by norm_num) ⟨4487, by rfl⟩ (by norm_num))
theorem R23937 : Reach 23937 := rs (se 2 (by rfl) ⟨8976, by rfl⟩) (B 17953 (by norm_num) ⟨8976, by rfl⟩ (by norm_num))
theorem R23941 : Reach 23941 := rs (se 4 (by rfl) ⟨2244, by rfl⟩) (B 4489 (by norm_num) ⟨2244, by rfl⟩ (by norm_num))
theorem R89477 : Reach 89477 := rs (se 4 (by rfl) ⟨8388, by rfl⟩) (B 16777 (by norm_num) ⟨8388, by rfl⟩ (by norm_num))
theorem R23945 : Reach 23945 := rs (se 2 (by rfl) ⟨8979, by rfl⟩) (B 17959 (by norm_num) ⟨8979, by rfl⟩ (by norm_num))
theorem R23949 : Reach 23949 := rs (se 3 (by rfl) ⟨4490, by rfl⟩) (B 8981 (by norm_num) ⟨4490, by rfl⟩ (by norm_num))
theorem R56717 : Reach 56717 := rs (se 3 (by rfl) ⟨10634, by rfl⟩) (B 21269 (by norm_num) ⟨10634, by rfl⟩ (by norm_num))
theorem R23953 : Reach 23953 := rs (se 2 (by rfl) ⟨8982, by rfl⟩) (B 17965 (by norm_num) ⟨8982, by rfl⟩ (by norm_num))
theorem R23957 : Reach 23957 := rs (se 6 (by rfl) ⟨561, by rfl⟩) (B 1123 (by norm_num) ⟨561, by rfl⟩ (by norm_num))
theorem R23961 : Reach 23961 := rs (se 2 (by rfl) ⟨8985, by rfl⟩) (B 17971 (by norm_num) ⟨8985, by rfl⟩ (by norm_num))
theorem R23965 : Reach 23965 := rs (se 3 (by rfl) ⟨4493, by rfl⟩) (B 8987 (by norm_num) ⟨4493, by rfl⟩ (by norm_num))
theorem R23969 : Reach 23969 := rs (se 2 (by rfl) ⟨8988, by rfl⟩) (B 17977 (by norm_num) ⟨8988, by rfl⟩ (by norm_num))
theorem R23973 : Reach 23973 := rs (se 4 (by rfl) ⟨2247, by rfl⟩) (B 4495 (by norm_num) ⟨2247, by rfl⟩ (by norm_num))
theorem R23977 : Reach 23977 := rs (se 2 (by rfl) ⟨8991, by rfl⟩) (B 17983 (by norm_num) ⟨8991, by rfl⟩ (by norm_num))
theorem R23981 : Reach 23981 := rs (se 3 (by rfl) ⟨4496, by rfl⟩) (B 8993 (by norm_num) ⟨4496, by rfl⟩ (by norm_num))
theorem R23985 : Reach 23985 := rs (se 2 (by rfl) ⟨8994, by rfl⟩) (B 17989 (by norm_num) ⟨8994, by rfl⟩ (by norm_num))
theorem R23989 : Reach 23989 := rs (se 5 (by rfl) ⟨1124, by rfl⟩) (B 2249 (by norm_num) ⟨1124, by rfl⟩ (by norm_num))
theorem R23993 : Reach 23993 := rs (se 2 (by rfl) ⟨8997, by rfl⟩) (B 17995 (by norm_num) ⟨8997, by rfl⟩ (by norm_num))
theorem R23997 : Reach 23997 := rs (se 3 (by rfl) ⟨4499, by rfl⟩) (B 8999 (by norm_num) ⟨4499, by rfl⟩ (by norm_num))
theorem R24001 : Reach 24001 := rs (se 2 (by rfl) ⟨9000, by rfl⟩) (B 18001 (by norm_num) ⟨9000, by rfl⟩ (by norm_num))
theorem R122309 : Reach 122309 := rs (se 4 (by rfl) ⟨11466, by rfl⟩) (B 22933 (by norm_num) ⟨11466, by rfl⟩ (by norm_num))
theorem R24005 : Reach 24005 := rs (se 4 (by rfl) ⟨2250, by rfl⟩) (B 4501 (by norm_num) ⟨2250, by rfl⟩ (by norm_num))
theorem R24009 : Reach 24009 := rs (se 2 (by rfl) ⟨9003, by rfl⟩) (B 18007 (by norm_num) ⟨9003, by rfl⟩ (by norm_num))
theorem R24013 : Reach 24013 := rs (se 3 (by rfl) ⟨4502, by rfl⟩) (B 9005 (by norm_num) ⟨4502, by rfl⟩ (by norm_num))
theorem R24017 : Reach 24017 := rs (se 2 (by rfl) ⟨9006, by rfl⟩) (B 18013 (by norm_num) ⟨9006, by rfl⟩ (by norm_num))
theorem R24021 : Reach 24021 := rs (se 7 (by rfl) ⟨281, by rfl⟩) (B 563 (by norm_num) ⟨281, by rfl⟩ (by norm_num))
theorem R56789 : Reach 56789 := rs (se 7 (by rfl) ⟨665, by rfl⟩) (B 1331 (by norm_num) ⟨665, by rfl⟩ (by norm_num))
theorem R24025 : Reach 24025 := rs (se 2 (by rfl) ⟨9009, by rfl⟩) (B 18019 (by norm_num) ⟨9009, by rfl⟩ (by norm_num))
theorem R24029 : Reach 24029 := rs (se 3 (by rfl) ⟨4505, by rfl⟩) (B 9011 (by norm_num) ⟨4505, by rfl⟩ (by norm_num))
theorem R24033 : Reach 24033 := rs (se 2 (by rfl) ⟨9012, by rfl⟩) (B 18025 (by norm_num) ⟨9012, by rfl⟩ (by norm_num))
theorem R24037 : Reach 24037 := rs (se 4 (by rfl) ⟨2253, by rfl⟩) (B 4507 (by norm_num) ⟨2253, by rfl⟩ (by norm_num))
theorem R24041 : Reach 24041 := rs (se 2 (by rfl) ⟨9015, by rfl⟩) (B 18031 (by norm_num) ⟨9015, by rfl⟩ (by norm_num))
theorem R24045 : Reach 24045 := rs (se 3 (by rfl) ⟨4508, by rfl⟩) (B 9017 (by norm_num) ⟨4508, by rfl⟩ (by norm_num))
theorem R24049 : Reach 24049 := rs (se 2 (by rfl) ⟨9018, by rfl⟩) (B 18037 (by norm_num) ⟨9018, by rfl⟩ (by norm_num))
theorem R24053 : Reach 24053 := rs (se 5 (by rfl) ⟨1127, by rfl⟩) (B 2255 (by norm_num) ⟨1127, by rfl⟩ (by norm_num))
theorem R24057 : Reach 24057 := rs (se 2 (by rfl) ⟨9021, by rfl⟩) (B 18043 (by norm_num) ⟨9021, by rfl⟩ (by norm_num))
theorem R24061 : Reach 24061 := rs (se 3 (by rfl) ⟨4511, by rfl⟩) (B 9023 (by norm_num) ⟨4511, by rfl⟩ (by norm_num))
theorem R24065 : Reach 24065 := rs (se 2 (by rfl) ⟨9024, by rfl⟩) (B 18049 (by norm_num) ⟨9024, by rfl⟩ (by norm_num))
theorem R24069 : Reach 24069 := rs (se 4 (by rfl) ⟨2256, by rfl⟩) (B 4513 (by norm_num) ⟨2256, by rfl⟩ (by norm_num))
theorem R24073 : Reach 24073 := rs (se 2 (by rfl) ⟨9027, by rfl⟩) (B 18055 (by norm_num) ⟨9027, by rfl⟩ (by norm_num))
theorem R24077 : Reach 24077 := rs (se 3 (by rfl) ⟨4514, by rfl⟩) (B 9029 (by norm_num) ⟨4514, by rfl⟩ (by norm_num))
theorem R24081 : Reach 24081 := rs (se 2 (by rfl) ⟨9030, by rfl⟩) (B 18061 (by norm_num) ⟨9030, by rfl⟩ (by norm_num))
theorem R24085 : Reach 24085 := rs (se 6 (by rfl) ⟨564, by rfl⟩) (B 1129 (by norm_num) ⟨564, by rfl⟩ (by norm_num))
theorem R24089 : Reach 24089 := rs (se 2 (by rfl) ⟨9033, by rfl⟩) (B 18067 (by norm_num) ⟨9033, by rfl⟩ (by norm_num))
theorem R24093 : Reach 24093 := rs (se 3 (by rfl) ⟨4517, by rfl⟩) (B 9035 (by norm_num) ⟨4517, by rfl⟩ (by norm_num))
theorem R56861 : Reach 56861 := rs (se 3 (by rfl) ⟨10661, by rfl⟩) (B 21323 (by norm_num) ⟨10661, by rfl⟩ (by norm_num))
theorem R24097 : Reach 24097 := rs (se 2 (by rfl) ⟨9036, by rfl⟩) (B 18073 (by norm_num) ⟨9036, by rfl⟩ (by norm_num))
theorem R24101 : Reach 24101 := rs (se 4 (by rfl) ⟨2259, by rfl⟩) (B 4519 (by norm_num) ⟨2259, by rfl⟩ (by norm_num))
theorem R24105 : Reach 24105 := rs (se 2 (by rfl) ⟨9039, by rfl⟩) (B 18079 (by norm_num) ⟨9039, by rfl⟩ (by norm_num))
theorem R24109 : Reach 24109 := rs (se 3 (by rfl) ⟨4520, by rfl⟩) (B 9041 (by norm_num) ⟨4520, by rfl⟩ (by norm_num))
theorem R24113 : Reach 24113 := rs (se 2 (by rfl) ⟨9042, by rfl⟩) (B 18085 (by norm_num) ⟨9042, by rfl⟩ (by norm_num))
theorem R24117 : Reach 24117 := rs (se 5 (by rfl) ⟨1130, by rfl⟩) (B 2261 (by norm_num) ⟨1130, by rfl⟩ (by norm_num))
theorem R24121 : Reach 24121 := rs (se 2 (by rfl) ⟨9045, by rfl⟩) (B 18091 (by norm_num) ⟨9045, by rfl⟩ (by norm_num))
theorem R24125 : Reach 24125 := rs (se 3 (by rfl) ⟨4523, by rfl⟩) (B 9047 (by norm_num) ⟨4523, by rfl⟩ (by norm_num))
theorem R24129 : Reach 24129 := rs (se 2 (by rfl) ⟨9048, by rfl⟩) (B 18097 (by norm_num) ⟨9048, by rfl⟩ (by norm_num))
theorem R24133 : Reach 24133 := rs (se 4 (by rfl) ⟨2262, by rfl⟩) (B 4525 (by norm_num) ⟨2262, by rfl⟩ (by norm_num))
theorem R24137 : Reach 24137 := rs (se 2 (by rfl) ⟨9051, by rfl⟩) (B 18103 (by norm_num) ⟨9051, by rfl⟩ (by norm_num))
theorem R24141 : Reach 24141 := rs (se 3 (by rfl) ⟨4526, by rfl⟩) (B 9053 (by norm_num) ⟨4526, by rfl⟩ (by norm_num))
theorem R24145 : Reach 24145 := rs (se 2 (by rfl) ⟨9054, by rfl⟩) (B 18109 (by norm_num) ⟨9054, by rfl⟩ (by norm_num))
theorem R24149 : Reach 24149 := rs (se 8 (by rfl) ⟨141, by rfl⟩) (B 283 (by norm_num) ⟨141, by rfl⟩ (by norm_num))
theorem R24153 : Reach 24153 := rs (se 2 (by rfl) ⟨9057, by rfl⟩) (B 18115 (by norm_num) ⟨9057, by rfl⟩ (by norm_num))
theorem R24157 : Reach 24157 := rs (se 3 (by rfl) ⟨4529, by rfl⟩) (B 9059 (by norm_num) ⟨4529, by rfl⟩ (by norm_num))
theorem R24161 : Reach 24161 := rs (se 2 (by rfl) ⟨9060, by rfl⟩) (B 18121 (by norm_num) ⟨9060, by rfl⟩ (by norm_num))
theorem R24165 : Reach 24165 := rs (se 4 (by rfl) ⟨2265, by rfl⟩) (B 4531 (by norm_num) ⟨2265, by rfl⟩ (by norm_num))
theorem R56933 : Reach 56933 := rs (se 4 (by rfl) ⟨5337, by rfl⟩) (B 10675 (by norm_num) ⟨5337, by rfl⟩ (by norm_num))
theorem R24169 : Reach 24169 := rs (se 2 (by rfl) ⟨9063, by rfl⟩) (B 18127 (by norm_num) ⟨9063, by rfl⟩ (by norm_num))
theorem R24173 : Reach 24173 := rs (se 3 (by rfl) ⟨4532, by rfl⟩) (B 9065 (by norm_num) ⟨4532, by rfl⟩ (by norm_num))
theorem R24177 : Reach 24177 := rs (se 2 (by rfl) ⟨9066, by rfl⟩) (B 18133 (by norm_num) ⟨9066, by rfl⟩ (by norm_num))
theorem R24181 : Reach 24181 := rs (se 5 (by rfl) ⟨1133, by rfl⟩) (B 2267 (by norm_num) ⟨1133, by rfl⟩ (by norm_num))
theorem R24185 : Reach 24185 := rs (se 2 (by rfl) ⟨9069, by rfl⟩) (B 18139 (by norm_num) ⟨9069, by rfl⟩ (by norm_num))
theorem R24189 : Reach 24189 := rs (se 3 (by rfl) ⟨4535, by rfl⟩) (B 9071 (by norm_num) ⟨4535, by rfl⟩ (by norm_num))
theorem R24193 : Reach 24193 := rs (se 2 (by rfl) ⟨9072, by rfl⟩) (B 18145 (by norm_num) ⟨9072, by rfl⟩ (by norm_num))
theorem R56965 : Reach 56965 := rs (se 4 (by rfl) ⟨5340, by rfl⟩) (B 10681 (by norm_num) ⟨5340, by rfl⟩ (by norm_num))
theorem R24197 : Reach 24197 := rs (se 4 (by rfl) ⟨2268, by rfl⟩) (B 4537 (by norm_num) ⟨2268, by rfl⟩ (by norm_num))
theorem R24201 : Reach 24201 := rs (se 2 (by rfl) ⟨9075, by rfl⟩) (B 18151 (by norm_num) ⟨9075, by rfl⟩ (by norm_num))
theorem R24205 : Reach 24205 := rs (se 3 (by rfl) ⟨4538, by rfl⟩) (B 9077 (by norm_num) ⟨4538, by rfl⟩ (by norm_num))
theorem R24209 : Reach 24209 := rs (se 2 (by rfl) ⟨9078, by rfl⟩) (B 18157 (by norm_num) ⟨9078, by rfl⟩ (by norm_num))
theorem R24213 : Reach 24213 := rs (se 6 (by rfl) ⟨567, by rfl⟩) (B 1135 (by norm_num) ⟨567, by rfl⟩ (by norm_num))
theorem R24217 : Reach 24217 := rs (se 2 (by rfl) ⟨9081, by rfl⟩) (B 18163 (by norm_num) ⟨9081, by rfl⟩ (by norm_num))
theorem R24221 : Reach 24221 := rs (se 3 (by rfl) ⟨4541, by rfl⟩) (B 9083 (by norm_num) ⟨4541, by rfl⟩ (by norm_num))
theorem R24225 : Reach 24225 := rs (se 2 (by rfl) ⟨9084, by rfl⟩) (B 18169 (by norm_num) ⟨9084, by rfl⟩ (by norm_num))
theorem R24229 : Reach 24229 := rs (se 4 (by rfl) ⟨2271, by rfl⟩) (B 4543 (by norm_num) ⟨2271, by rfl⟩ (by norm_num))
theorem R24233 : Reach 24233 := rs (se 2 (by rfl) ⟨9087, by rfl⟩) (B 18175 (by norm_num) ⟨9087, by rfl⟩ (by norm_num))
theorem R24237 : Reach 24237 := rs (se 3 (by rfl) ⟨4544, by rfl⟩) (B 9089 (by norm_num) ⟨4544, by rfl⟩ (by norm_num))
theorem R57005 : Reach 57005 := rs (se 3 (by rfl) ⟨10688, by rfl⟩) (B 21377 (by norm_num) ⟨10688, by rfl⟩ (by norm_num))
theorem R24241 : Reach 24241 := rs (se 2 (by rfl) ⟨9090, by rfl⟩) (B 18181 (by norm_num) ⟨9090, by rfl⟩ (by norm_num))
theorem R24245 : Reach 24245 := rs (se 5 (by rfl) ⟨1136, by rfl⟩) (B 2273 (by norm_num) ⟨1136, by rfl⟩ (by norm_num))
theorem R24249 : Reach 24249 := rs (se 2 (by rfl) ⟨9093, by rfl⟩) (B 18187 (by norm_num) ⟨9093, by rfl⟩ (by norm_num))
theorem R24253 : Reach 24253 := rs (se 3 (by rfl) ⟨4547, by rfl⟩) (B 9095 (by norm_num) ⟨4547, by rfl⟩ (by norm_num))
theorem R24257 : Reach 24257 := rs (se 2 (by rfl) ⟨9096, by rfl⟩) (B 18193 (by norm_num) ⟨9096, by rfl⟩ (by norm_num))
theorem R24261 : Reach 24261 := rs (se 4 (by rfl) ⟨2274, by rfl⟩) (B 4549 (by norm_num) ⟨2274, by rfl⟩ (by norm_num))
theorem R24265 : Reach 24265 := rs (se 2 (by rfl) ⟨9099, by rfl⟩) (B 18199 (by norm_num) ⟨9099, by rfl⟩ (by norm_num))
theorem R24269 : Reach 24269 := rs (se 3 (by rfl) ⟨4550, by rfl⟩) (B 9101 (by norm_num) ⟨4550, by rfl⟩ (by norm_num))
theorem R24273 : Reach 24273 := rs (se 2 (by rfl) ⟨9102, by rfl⟩) (B 18205 (by norm_num) ⟨9102, by rfl⟩ (by norm_num))
theorem R24277 : Reach 24277 := rs (se 7 (by rfl) ⟨284, by rfl⟩) (B 569 (by norm_num) ⟨284, by rfl⟩ (by norm_num))
theorem R24281 : Reach 24281 := rs (se 2 (by rfl) ⟨9105, by rfl⟩) (B 18211 (by norm_num) ⟨9105, by rfl⟩ (by norm_num))
theorem R24285 : Reach 24285 := rs (se 3 (by rfl) ⟨4553, by rfl⟩) (B 9107 (by norm_num) ⟨4553, by rfl⟩ (by norm_num))
theorem R24289 : Reach 24289 := rs (se 2 (by rfl) ⟨9108, by rfl⟩) (B 18217 (by norm_num) ⟨9108, by rfl⟩ (by norm_num))
theorem R24293 : Reach 24293 := rs (se 4 (by rfl) ⟨2277, by rfl⟩) (B 4555 (by norm_num) ⟨2277, by rfl⟩ (by norm_num))
theorem R24297 : Reach 24297 := rs (se 2 (by rfl) ⟨9111, by rfl⟩) (B 18223 (by norm_num) ⟨9111, by rfl⟩ (by norm_num))
theorem R24301 : Reach 24301 := rs (se 3 (by rfl) ⟨4556, by rfl⟩) (B 9113 (by norm_num) ⟨4556, by rfl⟩ (by norm_num))
theorem R24305 : Reach 24305 := rs (se 2 (by rfl) ⟨9114, by rfl⟩) (B 18229 (by norm_num) ⟨9114, by rfl⟩ (by norm_num))
theorem R24309 : Reach 24309 := rs (se 5 (by rfl) ⟨1139, by rfl⟩) (B 2279 (by norm_num) ⟨1139, by rfl⟩ (by norm_num))
theorem R57077 : Reach 57077 := rs (se 5 (by rfl) ⟨2675, by rfl⟩) (B 5351 (by norm_num) ⟨2675, by rfl⟩ (by norm_num))
theorem R24313 : Reach 24313 := rs (se 2 (by rfl) ⟨9117, by rfl⟩) (B 18235 (by norm_num) ⟨9117, by rfl⟩ (by norm_num))
theorem R24317 : Reach 24317 := rs (se 3 (by rfl) ⟨4559, by rfl⟩) (B 9119 (by norm_num) ⟨4559, by rfl⟩ (by norm_num))
theorem R24321 : Reach 24321 := rs (se 2 (by rfl) ⟨9120, by rfl⟩) (B 18241 (by norm_num) ⟨9120, by rfl⟩ (by norm_num))
theorem R24325 : Reach 24325 := rs (se 4 (by rfl) ⟨2280, by rfl⟩) (B 4561 (by norm_num) ⟨2280, by rfl⟩ (by norm_num))
theorem R24329 : Reach 24329 := rs (se 2 (by rfl) ⟨9123, by rfl⟩) (B 18247 (by norm_num) ⟨9123, by rfl⟩ (by norm_num))
theorem R24333 : Reach 24333 := rs (se 3 (by rfl) ⟨4562, by rfl⟩) (B 9125 (by norm_num) ⟨4562, by rfl⟩ (by norm_num))
theorem R24337 : Reach 24337 := rs (se 2 (by rfl) ⟨9126, by rfl⟩) (B 18253 (by norm_num) ⟨9126, by rfl⟩ (by norm_num))
theorem R24341 : Reach 24341 := rs (se 6 (by rfl) ⟨570, by rfl⟩) (B 1141 (by norm_num) ⟨570, by rfl⟩ (by norm_num))
theorem R24345 : Reach 24345 := rs (se 2 (by rfl) ⟨9129, by rfl⟩) (B 18259 (by norm_num) ⟨9129, by rfl⟩ (by norm_num))
theorem R24349 : Reach 24349 := rs (se 3 (by rfl) ⟨4565, by rfl⟩) (B 9131 (by norm_num) ⟨4565, by rfl⟩ (by norm_num))
theorem R24353 : Reach 24353 := rs (se 2 (by rfl) ⟨9132, by rfl⟩) (B 18265 (by norm_num) ⟨9132, by rfl⟩ (by norm_num))
theorem R24357 : Reach 24357 := rs (se 4 (by rfl) ⟨2283, by rfl⟩) (B 4567 (by norm_num) ⟨2283, by rfl⟩ (by norm_num))
theorem R24361 : Reach 24361 := rs (se 2 (by rfl) ⟨9135, by rfl⟩) (B 18271 (by norm_num) ⟨9135, by rfl⟩ (by norm_num))
theorem R24365 : Reach 24365 := rs (se 3 (by rfl) ⟨4568, by rfl⟩) (B 9137 (by norm_num) ⟨4568, by rfl⟩ (by norm_num))
theorem R24369 : Reach 24369 := rs (se 2 (by rfl) ⟨9138, by rfl⟩) (B 18277 (by norm_num) ⟨9138, by rfl⟩ (by norm_num))
theorem R24373 : Reach 24373 := rs (se 5 (by rfl) ⟨1142, by rfl⟩) (B 2285 (by norm_num) ⟨1142, by rfl⟩ (by norm_num))
theorem R89909 : Reach 89909 := rs (se 5 (by rfl) ⟨4214, by rfl⟩) (B 8429 (by norm_num) ⟨4214, by rfl⟩ (by norm_num))
theorem R24377 : Reach 24377 := rs (se 2 (by rfl) ⟨9141, by rfl⟩) (B 18283 (by norm_num) ⟨9141, by rfl⟩ (by norm_num))
theorem R24381 : Reach 24381 := rs (se 3 (by rfl) ⟨4571, by rfl⟩) (B 9143 (by norm_num) ⟨4571, by rfl⟩ (by norm_num))
theorem R57149 : Reach 57149 := rs (se 3 (by rfl) ⟨10715, by rfl⟩) (B 21431 (by norm_num) ⟨10715, by rfl⟩ (by norm_num))
theorem R24385 : Reach 24385 := rs (se 2 (by rfl) ⟨9144, by rfl⟩) (B 18289 (by norm_num) ⟨9144, by rfl⟩ (by norm_num))
theorem R24389 : Reach 24389 := rs (se 4 (by rfl) ⟨2286, by rfl⟩) (B 4573 (by norm_num) ⟨2286, by rfl⟩ (by norm_num))
theorem R24393 : Reach 24393 := rs (se 2 (by rfl) ⟨9147, by rfl⟩) (B 18295 (by norm_num) ⟨9147, by rfl⟩ (by norm_num))
theorem R24397 : Reach 24397 := rs (se 3 (by rfl) ⟨4574, by rfl⟩) (B 9149 (by norm_num) ⟨4574, by rfl⟩ (by norm_num))
theorem R24401 : Reach 24401 := rs (se 2 (by rfl) ⟨9150, by rfl⟩) (B 18301 (by norm_num) ⟨9150, by rfl⟩ (by norm_num))
theorem R24405 : Reach 24405 := rs (se 9 (by rfl) ⟨71, by rfl⟩) (B 143 (by norm_num) ⟨71, by rfl⟩ (by norm_num))
theorem R24409 : Reach 24409 := rs (se 2 (by rfl) ⟨9153, by rfl⟩) (B 18307 (by norm_num) ⟨9153, by rfl⟩ (by norm_num))
theorem R24413 : Reach 24413 := rs (se 3 (by rfl) ⟨4577, by rfl⟩) (B 9155 (by norm_num) ⟨4577, by rfl⟩ (by norm_num))
theorem R24417 : Reach 24417 := rs (se 2 (by rfl) ⟨9156, by rfl⟩) (B 18313 (by norm_num) ⟨9156, by rfl⟩ (by norm_num))
theorem R24421 : Reach 24421 := rs (se 4 (by rfl) ⟨2289, by rfl⟩) (B 4579 (by norm_num) ⟨2289, by rfl⟩ (by norm_num))
theorem R24425 : Reach 24425 := rs (se 2 (by rfl) ⟨9159, by rfl⟩) (B 18319 (by norm_num) ⟨9159, by rfl⟩ (by norm_num))
theorem R24429 : Reach 24429 := rs (se 3 (by rfl) ⟨4580, by rfl⟩) (B 9161 (by norm_num) ⟨4580, by rfl⟩ (by norm_num))
theorem R24433 : Reach 24433 := rs (se 2 (by rfl) ⟨9162, by rfl⟩) (B 18325 (by norm_num) ⟨9162, by rfl⟩ (by norm_num))
theorem R24437 : Reach 24437 := rs (se 5 (by rfl) ⟨1145, by rfl⟩) (B 2291 (by norm_num) ⟨1145, by rfl⟩ (by norm_num))
theorem R24441 : Reach 24441 := rs (se 2 (by rfl) ⟨9165, by rfl⟩) (B 18331 (by norm_num) ⟨9165, by rfl⟩ (by norm_num))
theorem R24445 : Reach 24445 := rs (se 3 (by rfl) ⟨4583, by rfl⟩) (B 9167 (by norm_num) ⟨4583, by rfl⟩ (by norm_num))
theorem R24449 : Reach 24449 := rs (se 2 (by rfl) ⟨9168, by rfl⟩) (B 18337 (by norm_num) ⟨9168, by rfl⟩ (by norm_num))
theorem R24453 : Reach 24453 := rs (se 4 (by rfl) ⟨2292, by rfl⟩) (B 4585 (by norm_num) ⟨2292, by rfl⟩ (by norm_num))
theorem R57221 : Reach 57221 := rs (se 4 (by rfl) ⟨5364, by rfl⟩) (B 10729 (by norm_num) ⟨5364, by rfl⟩ (by norm_num))
theorem R24457 : Reach 24457 := rs (se 2 (by rfl) ⟨9171, by rfl⟩) (B 18343 (by norm_num) ⟨9171, by rfl⟩ (by norm_num))
theorem R24461 : Reach 24461 := rs (se 3 (by rfl) ⟨4586, by rfl⟩) (B 9173 (by norm_num) ⟨4586, by rfl⟩ (by norm_num))
theorem R24465 : Reach 24465 := rs (se 2 (by rfl) ⟨9174, by rfl⟩) (B 18349 (by norm_num) ⟨9174, by rfl⟩ (by norm_num))
theorem R24469 : Reach 24469 := rs (se 6 (by rfl) ⟨573, by rfl⟩) (B 1147 (by norm_num) ⟨573, by rfl⟩ (by norm_num))
theorem R24473 : Reach 24473 := rs (se 2 (by rfl) ⟨9177, by rfl⟩) (B 18355 (by norm_num) ⟨9177, by rfl⟩ (by norm_num))
theorem R24477 : Reach 24477 := rs (se 3 (by rfl) ⟨4589, by rfl⟩) (B 9179 (by norm_num) ⟨4589, by rfl⟩ (by norm_num))
theorem R24481 : Reach 24481 := rs (se 2 (by rfl) ⟨9180, by rfl⟩) (B 18361 (by norm_num) ⟨9180, by rfl⟩ (by norm_num))
theorem R24485 : Reach 24485 := rs (se 4 (by rfl) ⟨2295, by rfl⟩) (B 4591 (by norm_num) ⟨2295, by rfl⟩ (by norm_num))
theorem R24489 : Reach 24489 := rs (se 2 (by rfl) ⟨9183, by rfl⟩) (B 18367 (by norm_num) ⟨9183, by rfl⟩ (by norm_num))
theorem R24493 : Reach 24493 := rs (se 3 (by rfl) ⟨4592, by rfl⟩) (B 9185 (by norm_num) ⟨4592, by rfl⟩ (by norm_num))
theorem R24497 : Reach 24497 := rs (se 2 (by rfl) ⟨9186, by rfl⟩) (B 18373 (by norm_num) ⟨9186, by rfl⟩ (by norm_num))
theorem R24501 : Reach 24501 := rs (se 5 (by rfl) ⟨1148, by rfl⟩) (B 2297 (by norm_num) ⟨1148, by rfl⟩ (by norm_num))
theorem R24505 : Reach 24505 := rs (se 2 (by rfl) ⟨9189, by rfl⟩) (B 18379 (by norm_num) ⟨9189, by rfl⟩ (by norm_num))
theorem R24509 : Reach 24509 := rs (se 3 (by rfl) ⟨4595, by rfl⟩) (B 9191 (by norm_num) ⟨4595, by rfl⟩ (by norm_num))
theorem R24513 : Reach 24513 := rs (se 2 (by rfl) ⟨9192, by rfl⟩) (B 18385 (by norm_num) ⟨9192, by rfl⟩ (by norm_num))
theorem R24517 : Reach 24517 := rs (se 4 (by rfl) ⟨2298, by rfl⟩) (B 4597 (by norm_num) ⟨2298, by rfl⟩ (by norm_num))
theorem R24521 : Reach 24521 := rs (se 2 (by rfl) ⟨9195, by rfl⟩) (B 18391 (by norm_num) ⟨9195, by rfl⟩ (by norm_num))
theorem R24525 : Reach 24525 := rs (se 3 (by rfl) ⟨4598, by rfl⟩) (B 9197 (by norm_num) ⟨4598, by rfl⟩ (by norm_num))
theorem R57293 : Reach 57293 := rs (se 3 (by rfl) ⟨10742, by rfl⟩) (B 21485 (by norm_num) ⟨10742, by rfl⟩ (by norm_num))
theorem R24529 : Reach 24529 := rs (se 2 (by rfl) ⟨9198, by rfl⟩) (B 18397 (by norm_num) ⟨9198, by rfl⟩ (by norm_num))
theorem R24533 : Reach 24533 := rs (se 7 (by rfl) ⟨287, by rfl⟩) (B 575 (by norm_num) ⟨287, by rfl⟩ (by norm_num))
theorem R24537 : Reach 24537 := rs (se 2 (by rfl) ⟨9201, by rfl⟩) (B 18403 (by norm_num) ⟨9201, by rfl⟩ (by norm_num))
theorem R24541 : Reach 24541 := rs (se 3 (by rfl) ⟨4601, by rfl⟩) (B 9203 (by norm_num) ⟨4601, by rfl⟩ (by norm_num))
theorem R24545 : Reach 24545 := rs (se 2 (by rfl) ⟨9204, by rfl⟩) (B 18409 (by norm_num) ⟨9204, by rfl⟩ (by norm_num))
theorem R24549 : Reach 24549 := rs (se 4 (by rfl) ⟨2301, by rfl⟩) (B 4603 (by norm_num) ⟨2301, by rfl⟩ (by norm_num))
theorem R24553 : Reach 24553 := rs (se 2 (by rfl) ⟨9207, by rfl⟩) (B 18415 (by norm_num) ⟨9207, by rfl⟩ (by norm_num))
theorem R24557 : Reach 24557 := rs (se 3 (by rfl) ⟨4604, by rfl⟩) (B 9209 (by norm_num) ⟨4604, by rfl⟩ (by norm_num))
theorem R24561 : Reach 24561 := rs (se 2 (by rfl) ⟨9210, by rfl⟩) (B 18421 (by norm_num) ⟨9210, by rfl⟩ (by norm_num))
theorem R24565 : Reach 24565 := rs (se 5 (by rfl) ⟨1151, by rfl⟩) (B 2303 (by norm_num) ⟨1151, by rfl⟩ (by norm_num))
theorem R24569 : Reach 24569 := rs (se 2 (by rfl) ⟨9213, by rfl⟩) (B 18427 (by norm_num) ⟨9213, by rfl⟩ (by norm_num))
theorem R24573 : Reach 24573 := rs (se 3 (by rfl) ⟨4607, by rfl⟩) (B 9215 (by norm_num) ⟨4607, by rfl⟩ (by norm_num))
theorem R57341 : Reach 57341 := rs (se 3 (by rfl) ⟨10751, by rfl⟩) (B 21503 (by norm_num) ⟨10751, by rfl⟩ (by norm_num))
theorem R24577 : Reach 24577 := rs (se 2 (by rfl) ⟨9216, by rfl⟩) (B 18433 (by norm_num) ⟨9216, by rfl⟩ (by norm_num))
theorem R24581 : Reach 24581 := rs (se 4 (by rfl) ⟨2304, by rfl⟩) (B 4609 (by norm_num) ⟨2304, by rfl⟩ (by norm_num))
theorem R24585 : Reach 24585 := rs (se 2 (by rfl) ⟨9219, by rfl⟩) (B 18439 (by norm_num) ⟨9219, by rfl⟩ (by norm_num))
theorem R24589 : Reach 24589 := rs (se 3 (by rfl) ⟨4610, by rfl⟩) (B 9221 (by norm_num) ⟨4610, by rfl⟩ (by norm_num))
theorem R24593 : Reach 24593 := rs (se 2 (by rfl) ⟨9222, by rfl⟩) (B 18445 (by norm_num) ⟨9222, by rfl⟩ (by norm_num))
theorem R24597 : Reach 24597 := rs (se 6 (by rfl) ⟨576, by rfl⟩) (B 1153 (by norm_num) ⟨576, by rfl⟩ (by norm_num))
theorem R57365 : Reach 57365 := rs (se 6 (by rfl) ⟨1344, by rfl⟩) (B 2689 (by norm_num) ⟨1344, by rfl⟩ (by norm_num))
theorem R24601 : Reach 24601 := rs (se 2 (by rfl) ⟨9225, by rfl⟩) (B 18451 (by norm_num) ⟨9225, by rfl⟩ (by norm_num))
theorem R24605 : Reach 24605 := rs (se 3 (by rfl) ⟨4613, by rfl⟩) (B 9227 (by norm_num) ⟨4613, by rfl⟩ (by norm_num))
theorem R24609 : Reach 24609 := rs (se 2 (by rfl) ⟨9228, by rfl⟩) (B 18457 (by norm_num) ⟨9228, by rfl⟩ (by norm_num))
theorem R24613 : Reach 24613 := rs (se 4 (by rfl) ⟨2307, by rfl⟩) (B 4615 (by norm_num) ⟨2307, by rfl⟩ (by norm_num))
theorem R24617 : Reach 24617 := rs (se 2 (by rfl) ⟨9231, by rfl⟩) (B 18463 (by norm_num) ⟨9231, by rfl⟩ (by norm_num))
theorem R24621 : Reach 24621 := rs (se 3 (by rfl) ⟨4616, by rfl⟩) (B 9233 (by norm_num) ⟨4616, by rfl⟩ (by norm_num))
theorem R24625 : Reach 24625 := rs (se 2 (by rfl) ⟨9234, by rfl⟩) (B 18469 (by norm_num) ⟨9234, by rfl⟩ (by norm_num))
theorem R24629 : Reach 24629 := rs (se 5 (by rfl) ⟨1154, by rfl⟩) (B 2309 (by norm_num) ⟨1154, by rfl⟩ (by norm_num))
theorem R24633 : Reach 24633 := rs (se 2 (by rfl) ⟨9237, by rfl⟩) (B 18475 (by norm_num) ⟨9237, by rfl⟩ (by norm_num))
theorem R24637 : Reach 24637 := rs (se 3 (by rfl) ⟨4619, by rfl⟩) (B 9239 (by norm_num) ⟨4619, by rfl⟩ (by norm_num))
theorem R24641 : Reach 24641 := rs (se 2 (by rfl) ⟨9240, by rfl⟩) (B 18481 (by norm_num) ⟨9240, by rfl⟩ (by norm_num))
theorem R24645 : Reach 24645 := rs (se 4 (by rfl) ⟨2310, by rfl⟩) (B 4621 (by norm_num) ⟨2310, by rfl⟩ (by norm_num))
theorem R24649 : Reach 24649 := rs (se 2 (by rfl) ⟨9243, by rfl⟩) (B 18487 (by norm_num) ⟨9243, by rfl⟩ (by norm_num))
theorem R24653 : Reach 24653 := rs (se 3 (by rfl) ⟨4622, by rfl⟩) (B 9245 (by norm_num) ⟨4622, by rfl⟩ (by norm_num))
theorem R24657 : Reach 24657 := rs (se 2 (by rfl) ⟨9246, by rfl⟩) (B 18493 (by norm_num) ⟨9246, by rfl⟩ (by norm_num))
theorem R680021 : Reach 680021 := rs (se 8 (by rfl) ⟨3984, by rfl⟩) (B 7969 (by norm_num) ⟨3984, by rfl⟩ (by norm_num))
theorem R24661 : Reach 24661 := rs (se 8 (by rfl) ⟨144, by rfl⟩) (B 289 (by norm_num) ⟨144, by rfl⟩ (by norm_num))
theorem R24665 : Reach 24665 := rs (se 2 (by rfl) ⟨9249, by rfl⟩) (B 18499 (by norm_num) ⟨9249, by rfl⟩ (by norm_num))
theorem R24669 : Reach 24669 := rs (se 3 (by rfl) ⟨4625, by rfl⟩) (B 9251 (by norm_num) ⟨4625, by rfl⟩ (by norm_num))
theorem R57437 : Reach 57437 := rs (se 3 (by rfl) ⟨10769, by rfl⟩) (B 21539 (by norm_num) ⟨10769, by rfl⟩ (by norm_num))
theorem R24673 : Reach 24673 := rs (se 2 (by rfl) ⟨9252, by rfl⟩) (B 18505 (by norm_num) ⟨9252, by rfl⟩ (by norm_num))
theorem R24677 : Reach 24677 := rs (se 4 (by rfl) ⟨2313, by rfl⟩) (B 4627 (by norm_num) ⟨2313, by rfl⟩ (by norm_num))
theorem R24681 : Reach 24681 := rs (se 2 (by rfl) ⟨9255, by rfl⟩) (B 18511 (by norm_num) ⟨9255, by rfl⟩ (by norm_num))
theorem R24685 : Reach 24685 := rs (se 3 (by rfl) ⟨4628, by rfl⟩) (B 9257 (by norm_num) ⟨4628, by rfl⟩ (by norm_num))
theorem R24689 : Reach 24689 := rs (se 2 (by rfl) ⟨9258, by rfl⟩) (B 18517 (by norm_num) ⟨9258, by rfl⟩ (by norm_num))
theorem R24693 : Reach 24693 := rs (se 5 (by rfl) ⟨1157, by rfl⟩) (B 2315 (by norm_num) ⟨1157, by rfl⟩ (by norm_num))
theorem R24697 : Reach 24697 := rs (se 2 (by rfl) ⟨9261, by rfl⟩) (B 18523 (by norm_num) ⟨9261, by rfl⟩ (by norm_num))
theorem R24701 : Reach 24701 := rs (se 3 (by rfl) ⟨4631, by rfl⟩) (B 9263 (by norm_num) ⟨4631, by rfl⟩ (by norm_num))
theorem R24705 : Reach 24705 := rs (se 2 (by rfl) ⟨9264, by rfl⟩) (B 18529 (by norm_num) ⟨9264, by rfl⟩ (by norm_num))
theorem R24709 : Reach 24709 := rs (se 4 (by rfl) ⟨2316, by rfl⟩) (B 4633 (by norm_num) ⟨2316, by rfl⟩ (by norm_num))
theorem R24713 : Reach 24713 := rs (se 2 (by rfl) ⟨9267, by rfl⟩) (B 18535 (by norm_num) ⟨9267, by rfl⟩ (by norm_num))
theorem R24717 : Reach 24717 := rs (se 3 (by rfl) ⟨4634, by rfl⟩) (B 9269 (by norm_num) ⟨4634, by rfl⟩ (by norm_num))
theorem R24721 : Reach 24721 := rs (se 2 (by rfl) ⟨9270, by rfl⟩) (B 18541 (by norm_num) ⟨9270, by rfl⟩ (by norm_num))
theorem R24725 : Reach 24725 := rs (se 6 (by rfl) ⟨579, by rfl⟩) (B 1159 (by norm_num) ⟨579, by rfl⟩ (by norm_num))
theorem R24729 : Reach 24729 := rs (se 2 (by rfl) ⟨9273, by rfl⟩) (B 18547 (by norm_num) ⟨9273, by rfl⟩ (by norm_num))
theorem R24733 : Reach 24733 := rs (se 3 (by rfl) ⟨4637, by rfl⟩) (B 9275 (by norm_num) ⟨4637, by rfl⟩ (by norm_num))
theorem R24737 : Reach 24737 := rs (se 2 (by rfl) ⟨9276, by rfl⟩) (B 18553 (by norm_num) ⟨9276, by rfl⟩ (by norm_num))
theorem R24741 : Reach 24741 := rs (se 4 (by rfl) ⟨2319, by rfl⟩) (B 4639 (by norm_num) ⟨2319, by rfl⟩ (by norm_num))
theorem R57509 : Reach 57509 := rs (se 4 (by rfl) ⟨5391, by rfl⟩) (B 10783 (by norm_num) ⟨5391, by rfl⟩ (by norm_num))
theorem R24745 : Reach 24745 := rs (se 2 (by rfl) ⟨9279, by rfl⟩) (B 18559 (by norm_num) ⟨9279, by rfl⟩ (by norm_num))
theorem R24749 : Reach 24749 := rs (se 3 (by rfl) ⟨4640, by rfl⟩) (B 9281 (by norm_num) ⟨4640, by rfl⟩ (by norm_num))
theorem R24753 : Reach 24753 := rs (se 2 (by rfl) ⟨9282, by rfl⟩) (B 18565 (by norm_num) ⟨9282, by rfl⟩ (by norm_num))
theorem R24757 : Reach 24757 := rs (se 5 (by rfl) ⟨1160, by rfl⟩) (B 2321 (by norm_num) ⟨1160, by rfl⟩ (by norm_num))
theorem R24761 : Reach 24761 := rs (se 2 (by rfl) ⟨9285, by rfl⟩) (B 18571 (by norm_num) ⟨9285, by rfl⟩ (by norm_num))
theorem R24765 : Reach 24765 := rs (se 3 (by rfl) ⟨4643, by rfl⟩) (B 9287 (by norm_num) ⟨4643, by rfl⟩ (by norm_num))
theorem R24769 : Reach 24769 := rs (se 2 (by rfl) ⟨9288, by rfl⟩) (B 18577 (by norm_num) ⟨9288, by rfl⟩ (by norm_num))
theorem R24773 : Reach 24773 := rs (se 4 (by rfl) ⟨2322, by rfl⟩) (B 4645 (by norm_num) ⟨2322, by rfl⟩ (by norm_num))
theorem R24777 : Reach 24777 := rs (se 2 (by rfl) ⟨9291, by rfl⟩) (B 18583 (by norm_num) ⟨9291, by rfl⟩ (by norm_num))
theorem R24781 : Reach 24781 := rs (se 3 (by rfl) ⟨4646, by rfl⟩) (B 9293 (by norm_num) ⟨4646, by rfl⟩ (by norm_num))
theorem R24785 : Reach 24785 := rs (se 2 (by rfl) ⟨9294, by rfl⟩) (B 18589 (by norm_num) ⟨9294, by rfl⟩ (by norm_num))
theorem R24789 : Reach 24789 := rs (se 7 (by rfl) ⟨290, by rfl⟩) (B 581 (by norm_num) ⟨290, by rfl⟩ (by norm_num))
theorem R24793 : Reach 24793 := rs (se 2 (by rfl) ⟨9297, by rfl⟩) (B 18595 (by norm_num) ⟨9297, by rfl⟩ (by norm_num))
theorem R24797 : Reach 24797 := rs (se 3 (by rfl) ⟨4649, by rfl⟩) (B 9299 (by norm_num) ⟨4649, by rfl⟩ (by norm_num))
theorem R24801 : Reach 24801 := rs (se 2 (by rfl) ⟨9300, by rfl⟩) (B 18601 (by norm_num) ⟨9300, by rfl⟩ (by norm_num))
theorem R24805 : Reach 24805 := rs (se 4 (by rfl) ⟨2325, by rfl⟩) (B 4651 (by norm_num) ⟨2325, by rfl⟩ (by norm_num))
theorem R90341 : Reach 90341 := rs (se 4 (by rfl) ⟨8469, by rfl⟩) (B 16939 (by norm_num) ⟨8469, by rfl⟩ (by norm_num))
theorem R24809 : Reach 24809 := rs (se 2 (by rfl) ⟨9303, by rfl⟩) (B 18607 (by norm_num) ⟨9303, by rfl⟩ (by norm_num))
theorem R57581 : Reach 57581 := rs (se 3 (by rfl) ⟨10796, by rfl⟩) (B 21593 (by norm_num) ⟨10796, by rfl⟩ (by norm_num))
theorem R24813 : Reach 24813 := rs (se 3 (by rfl) ⟨4652, by rfl⟩) (B 9305 (by norm_num) ⟨4652, by rfl⟩ (by norm_num))
theorem R24817 : Reach 24817 := rs (se 2 (by rfl) ⟨9306, by rfl⟩) (B 18613 (by norm_num) ⟨9306, by rfl⟩ (by norm_num))
theorem R24821 : Reach 24821 := rs (se 5 (by rfl) ⟨1163, by rfl⟩) (B 2327 (by norm_num) ⟨1163, by rfl⟩ (by norm_num))
theorem R24825 : Reach 24825 := rs (se 2 (by rfl) ⟨9309, by rfl⟩) (B 18619 (by norm_num) ⟨9309, by rfl⟩ (by norm_num))
theorem R24829 : Reach 24829 := rs (se 3 (by rfl) ⟨4655, by rfl⟩) (B 9311 (by norm_num) ⟨4655, by rfl⟩ (by norm_num))
theorem R24833 : Reach 24833 := rs (se 2 (by rfl) ⟨9312, by rfl⟩) (B 18625 (by norm_num) ⟨9312, by rfl⟩ (by norm_num))
theorem R24837 : Reach 24837 := rs (se 4 (by rfl) ⟨2328, by rfl⟩) (B 4657 (by norm_num) ⟨2328, by rfl⟩ (by norm_num))
theorem R24841 : Reach 24841 := rs (se 2 (by rfl) ⟨9315, by rfl⟩) (B 18631 (by norm_num) ⟨9315, by rfl⟩ (by norm_num))
theorem R24845 : Reach 24845 := rs (se 3 (by rfl) ⟨4658, by rfl⟩) (B 9317 (by norm_num) ⟨4658, by rfl⟩ (by norm_num))
theorem R24849 : Reach 24849 := rs (se 2 (by rfl) ⟨9318, by rfl⟩) (B 18637 (by norm_num) ⟨9318, by rfl⟩ (by norm_num))
theorem R24853 : Reach 24853 := rs (se 6 (by rfl) ⟨582, by rfl⟩) (B 1165 (by norm_num) ⟨582, by rfl⟩ (by norm_num))
theorem R24857 : Reach 24857 := rs (se 2 (by rfl) ⟨9321, by rfl⟩) (B 18643 (by norm_num) ⟨9321, by rfl⟩ (by norm_num))
theorem R24861 : Reach 24861 := rs (se 3 (by rfl) ⟨4661, by rfl⟩) (B 9323 (by norm_num) ⟨4661, by rfl⟩ (by norm_num))
theorem R24865 : Reach 24865 := rs (se 2 (by rfl) ⟨9324, by rfl⟩) (B 18649 (by norm_num) ⟨9324, by rfl⟩ (by norm_num))
theorem R24869 : Reach 24869 := rs (se 4 (by rfl) ⟨2331, by rfl⟩) (B 4663 (by norm_num) ⟨2331, by rfl⟩ (by norm_num))
theorem R24873 : Reach 24873 := rs (se 2 (by rfl) ⟨9327, by rfl⟩) (B 18655 (by norm_num) ⟨9327, by rfl⟩ (by norm_num))
theorem R24877 : Reach 24877 := rs (se 3 (by rfl) ⟨4664, by rfl⟩) (B 9329 (by norm_num) ⟨4664, by rfl⟩ (by norm_num))
theorem R24881 : Reach 24881 := rs (se 2 (by rfl) ⟨9330, by rfl⟩) (B 18661 (by norm_num) ⟨9330, by rfl⟩ (by norm_num))
theorem R24885 : Reach 24885 := rs (se 5 (by rfl) ⟨1166, by rfl⟩) (B 2333 (by norm_num) ⟨1166, by rfl⟩ (by norm_num))
theorem R57653 : Reach 57653 := rs (se 5 (by rfl) ⟨2702, by rfl⟩) (B 5405 (by norm_num) ⟨2702, by rfl⟩ (by norm_num))
theorem R24889 : Reach 24889 := rs (se 2 (by rfl) ⟨9333, by rfl⟩) (B 18667 (by norm_num) ⟨9333, by rfl⟩ (by norm_num))
theorem R24893 : Reach 24893 := rs (se 3 (by rfl) ⟨4667, by rfl⟩) (B 9335 (by norm_num) ⟨4667, by rfl⟩ (by norm_num))
theorem R24897 : Reach 24897 := rs (se 2 (by rfl) ⟨9336, by rfl⟩) (B 18673 (by norm_num) ⟨9336, by rfl⟩ (by norm_num))
theorem R24901 : Reach 24901 := rs (se 4 (by rfl) ⟨2334, by rfl⟩) (B 4669 (by norm_num) ⟨2334, by rfl⟩ (by norm_num))
theorem R24905 : Reach 24905 := rs (se 2 (by rfl) ⟨9339, by rfl⟩) (B 18679 (by norm_num) ⟨9339, by rfl⟩ (by norm_num))
theorem R24909 : Reach 24909 := rs (se 3 (by rfl) ⟨4670, by rfl⟩) (B 9341 (by norm_num) ⟨4670, by rfl⟩ (by norm_num))
theorem R24913 : Reach 24913 := rs (se 2 (by rfl) ⟨9342, by rfl⟩) (B 18685 (by norm_num) ⟨9342, by rfl⟩ (by norm_num))
theorem R24917 : Reach 24917 := rs (se 10 (by rfl) ⟨36, by rfl⟩) (B 73 (by norm_num) ⟨36, by rfl⟩ (by norm_num))
theorem R24921 : Reach 24921 := rs (se 2 (by rfl) ⟨9345, by rfl⟩) (B 18691 (by norm_num) ⟨9345, by rfl⟩ (by norm_num))
theorem R24925 : Reach 24925 := rs (se 3 (by rfl) ⟨4673, by rfl⟩) (B 9347 (by norm_num) ⟨4673, by rfl⟩ (by norm_num))
theorem R24929 : Reach 24929 := rs (se 2 (by rfl) ⟨9348, by rfl⟩) (B 18697 (by norm_num) ⟨9348, by rfl⟩ (by norm_num))
theorem R24933 : Reach 24933 := rs (se 4 (by rfl) ⟨2337, by rfl⟩) (B 4675 (by norm_num) ⟨2337, by rfl⟩ (by norm_num))
theorem R24937 : Reach 24937 := rs (se 2 (by rfl) ⟨9351, by rfl⟩) (B 18703 (by norm_num) ⟨9351, by rfl⟩ (by norm_num))
theorem R24941 : Reach 24941 := rs (se 3 (by rfl) ⟨4676, by rfl⟩) (B 9353 (by norm_num) ⟨4676, by rfl⟩ (by norm_num))
theorem R24945 : Reach 24945 := rs (se 2 (by rfl) ⟨9354, by rfl⟩) (B 18709 (by norm_num) ⟨9354, by rfl⟩ (by norm_num))
theorem R24949 : Reach 24949 := rs (se 5 (by rfl) ⟨1169, by rfl⟩) (B 2339 (by norm_num) ⟨1169, by rfl⟩ (by norm_num))
theorem R24953 : Reach 24953 := rs (se 2 (by rfl) ⟨9357, by rfl⟩) (B 18715 (by norm_num) ⟨9357, by rfl⟩ (by norm_num))
theorem R24957 : Reach 24957 := rs (se 3 (by rfl) ⟨4679, by rfl⟩) (B 9359 (by norm_num) ⟨4679, by rfl⟩ (by norm_num))
theorem R57725 : Reach 57725 := rs (se 3 (by rfl) ⟨10823, by rfl⟩) (B 21647 (by norm_num) ⟨10823, by rfl⟩ (by norm_num))
theorem R24961 : Reach 24961 := rs (se 2 (by rfl) ⟨9360, by rfl⟩) (B 18721 (by norm_num) ⟨9360, by rfl⟩ (by norm_num))
theorem R24965 : Reach 24965 := rs (se 4 (by rfl) ⟨2340, by rfl⟩) (B 4681 (by norm_num) ⟨2340, by rfl⟩ (by norm_num))
theorem R24969 : Reach 24969 := rs (se 2 (by rfl) ⟨9363, by rfl⟩) (B 18727 (by norm_num) ⟨9363, by rfl⟩ (by norm_num))
theorem R24973 : Reach 24973 := rs (se 3 (by rfl) ⟨4682, by rfl⟩) (B 9365 (by norm_num) ⟨4682, by rfl⟩ (by norm_num))
theorem R24977 : Reach 24977 := rs (se 2 (by rfl) ⟨9366, by rfl⟩) (B 18733 (by norm_num) ⟨9366, by rfl⟩ (by norm_num))
theorem R90517 : Reach 90517 := rs (se 6 (by rfl) ⟨2121, by rfl⟩) (B 4243 (by norm_num) ⟨2121, by rfl⟩ (by norm_num))
theorem R24981 : Reach 24981 := rs (se 6 (by rfl) ⟨585, by rfl⟩) (B 1171 (by norm_num) ⟨585, by rfl⟩ (by norm_num))
theorem R24985 : Reach 24985 := rs (se 2 (by rfl) ⟨9369, by rfl⟩) (B 18739 (by norm_num) ⟨9369, by rfl⟩ (by norm_num))
theorem R24989 : Reach 24989 := rs (se 3 (by rfl) ⟨4685, by rfl⟩) (B 9371 (by norm_num) ⟨4685, by rfl⟩ (by norm_num))
theorem R24993 : Reach 24993 := rs (se 2 (by rfl) ⟨9372, by rfl⟩) (B 18745 (by norm_num) ⟨9372, by rfl⟩ (by norm_num))
theorem R24997 : Reach 24997 := rs (se 4 (by rfl) ⟨2343, by rfl⟩) (B 4687 (by norm_num) ⟨2343, by rfl⟩ (by norm_num))
theorem R25001 : Reach 25001 := rs (se 2 (by rfl) ⟨9375, by rfl⟩) (B 18751 (by norm_num) ⟨9375, by rfl⟩ (by norm_num))
theorem R25005 : Reach 25005 := rs (se 3 (by rfl) ⟨4688, by rfl⟩) (B 9377 (by norm_num) ⟨4688, by rfl⟩ (by norm_num))
theorem R25009 : Reach 25009 := rs (se 2 (by rfl) ⟨9378, by rfl⟩) (B 18757 (by norm_num) ⟨9378, by rfl⟩ (by norm_num))
theorem R57781 : Reach 57781 := rs (se 5 (by rfl) ⟨2708, by rfl⟩) (B 5417 (by norm_num) ⟨2708, by rfl⟩ (by norm_num))
theorem R25013 : Reach 25013 := rs (se 5 (by rfl) ⟨1172, by rfl⟩) (B 2345 (by norm_num) ⟨1172, by rfl⟩ (by norm_num))
theorem R25017 : Reach 25017 := rs (se 2 (by rfl) ⟨9381, by rfl⟩) (B 18763 (by norm_num) ⟨9381, by rfl⟩ (by norm_num))
theorem R25021 : Reach 25021 := rs (se 3 (by rfl) ⟨4691, by rfl⟩) (B 9383 (by norm_num) ⟨4691, by rfl⟩ (by norm_num))
theorem R25025 : Reach 25025 := rs (se 2 (by rfl) ⟨9384, by rfl⟩) (B 18769 (by norm_num) ⟨9384, by rfl⟩ (by norm_num))
theorem R25029 : Reach 25029 := rs (se 4 (by rfl) ⟨2346, by rfl⟩) (B 4693 (by norm_num) ⟨2346, by rfl⟩ (by norm_num))
theorem R57797 : Reach 57797 := rs (se 4 (by rfl) ⟨5418, by rfl⟩) (B 10837 (by norm_num) ⟨5418, by rfl⟩ (by norm_num))
theorem R25033 : Reach 25033 := rs (se 2 (by rfl) ⟨9387, by rfl⟩) (B 18775 (by norm_num) ⟨9387, by rfl⟩ (by norm_num))
theorem R25037 : Reach 25037 := rs (se 3 (by rfl) ⟨4694, by rfl⟩) (B 9389 (by norm_num) ⟨4694, by rfl⟩ (by norm_num))
theorem R25041 : Reach 25041 := rs (se 2 (by rfl) ⟨9390, by rfl⟩) (B 18781 (by norm_num) ⟨9390, by rfl⟩ (by norm_num))
theorem R25045 : Reach 25045 := rs (se 7 (by rfl) ⟨293, by rfl⟩) (B 587 (by norm_num) ⟨293, by rfl⟩ (by norm_num))
theorem R25049 : Reach 25049 := rs (se 2 (by rfl) ⟨9393, by rfl⟩) (B 18787 (by norm_num) ⟨9393, by rfl⟩ (by norm_num))
theorem R25053 : Reach 25053 := rs (se 3 (by rfl) ⟨4697, by rfl⟩) (B 9395 (by norm_num) ⟨4697, by rfl⟩ (by norm_num))
theorem R25057 : Reach 25057 := rs (se 2 (by rfl) ⟨9396, by rfl⟩) (B 18793 (by norm_num) ⟨9396, by rfl⟩ (by norm_num))
theorem R25061 : Reach 25061 := rs (se 4 (by rfl) ⟨2349, by rfl⟩) (B 4699 (by norm_num) ⟨2349, by rfl⟩ (by norm_num))
theorem R25065 : Reach 25065 := rs (se 2 (by rfl) ⟨9399, by rfl⟩) (B 18799 (by norm_num) ⟨9399, by rfl⟩ (by norm_num))
theorem R25069 : Reach 25069 := rs (se 3 (by rfl) ⟨4700, by rfl⟩) (B 9401 (by norm_num) ⟨4700, by rfl⟩ (by norm_num))
theorem R25073 : Reach 25073 := rs (se 2 (by rfl) ⟨9402, by rfl⟩) (B 18805 (by norm_num) ⟨9402, by rfl⟩ (by norm_num))
theorem R25077 : Reach 25077 := rs (se 5 (by rfl) ⟨1175, by rfl⟩) (B 2351 (by norm_num) ⟨1175, by rfl⟩ (by norm_num))
theorem R25081 : Reach 25081 := rs (se 2 (by rfl) ⟨9405, by rfl⟩) (B 18811 (by norm_num) ⟨9405, by rfl⟩ (by norm_num))
theorem R25085 : Reach 25085 := rs (se 3 (by rfl) ⟨4703, by rfl⟩) (B 9407 (by norm_num) ⟨4703, by rfl⟩ (by norm_num))
theorem R25089 : Reach 25089 := rs (se 2 (by rfl) ⟨9408, by rfl⟩) (B 18817 (by norm_num) ⟨9408, by rfl⟩ (by norm_num))
theorem R25093 : Reach 25093 := rs (se 4 (by rfl) ⟨2352, by rfl⟩) (B 4705 (by norm_num) ⟨2352, by rfl⟩ (by norm_num))
theorem R25097 : Reach 25097 := rs (se 2 (by rfl) ⟨9411, by rfl⟩) (B 18823 (by norm_num) ⟨9411, by rfl⟩ (by norm_num))
theorem R25101 : Reach 25101 := rs (se 3 (by rfl) ⟨4706, by rfl⟩) (B 9413 (by norm_num) ⟨4706, by rfl⟩ (by norm_num))
theorem R57869 : Reach 57869 := rs (se 3 (by rfl) ⟨10850, by rfl⟩) (B 21701 (by norm_num) ⟨10850, by rfl⟩ (by norm_num))
theorem R25105 : Reach 25105 := rs (se 2 (by rfl) ⟨9414, by rfl⟩) (B 18829 (by norm_num) ⟨9414, by rfl⟩ (by norm_num))
theorem R25109 : Reach 25109 := rs (se 6 (by rfl) ⟨588, by rfl⟩) (B 1177 (by norm_num) ⟨588, by rfl⟩ (by norm_num))
theorem R25113 : Reach 25113 := rs (se 2 (by rfl) ⟨9417, by rfl⟩) (B 18835 (by norm_num) ⟨9417, by rfl⟩ (by norm_num))
theorem R25117 : Reach 25117 := rs (se 3 (by rfl) ⟨4709, by rfl⟩) (B 9419 (by norm_num) ⟨4709, by rfl⟩ (by norm_num))
theorem R25121 : Reach 25121 := rs (se 2 (by rfl) ⟨9420, by rfl⟩) (B 18841 (by norm_num) ⟨9420, by rfl⟩ (by norm_num))
theorem R25125 : Reach 25125 := rs (se 4 (by rfl) ⟨2355, by rfl⟩) (B 4711 (by norm_num) ⟨2355, by rfl⟩ (by norm_num))
theorem R25129 : Reach 25129 := rs (se 2 (by rfl) ⟨9423, by rfl⟩) (B 18847 (by norm_num) ⟨9423, by rfl⟩ (by norm_num))
theorem R25133 : Reach 25133 := rs (se 3 (by rfl) ⟨4712, by rfl⟩) (B 9425 (by norm_num) ⟨4712, by rfl⟩ (by norm_num))
theorem R25137 : Reach 25137 := rs (se 2 (by rfl) ⟨9426, by rfl⟩) (B 18853 (by norm_num) ⟨9426, by rfl⟩ (by norm_num))
theorem R25141 : Reach 25141 := rs (se 5 (by rfl) ⟨1178, by rfl⟩) (B 2357 (by norm_num) ⟨1178, by rfl⟩ (by norm_num))
theorem R25145 : Reach 25145 := rs (se 2 (by rfl) ⟨9429, by rfl⟩) (B 18859 (by norm_num) ⟨9429, by rfl⟩ (by norm_num))
theorem R25149 : Reach 25149 := rs (se 3 (by rfl) ⟨4715, by rfl⟩) (B 9431 (by norm_num) ⟨4715, by rfl⟩ (by norm_num))
theorem R25153 : Reach 25153 := rs (se 2 (by rfl) ⟨9432, by rfl⟩) (B 18865 (by norm_num) ⟨9432, by rfl⟩ (by norm_num))
theorem R25157 : Reach 25157 := rs (se 4 (by rfl) ⟨2358, by rfl⟩) (B 4717 (by norm_num) ⟨2358, by rfl⟩ (by norm_num))
theorem R25161 : Reach 25161 := rs (se 2 (by rfl) ⟨9435, by rfl⟩) (B 18871 (by norm_num) ⟨9435, by rfl⟩ (by norm_num))
theorem R25165 : Reach 25165 := rs (se 3 (by rfl) ⟨4718, by rfl⟩) (B 9437 (by norm_num) ⟨4718, by rfl⟩ (by norm_num))
theorem R25169 : Reach 25169 := rs (se 2 (by rfl) ⟨9438, by rfl⟩) (B 18877 (by norm_num) ⟨9438, by rfl⟩ (by norm_num))
theorem R25173 : Reach 25173 := rs (se 8 (by rfl) ⟨147, by rfl⟩) (B 295 (by norm_num) ⟨147, by rfl⟩ (by norm_num))
theorem R57941 : Reach 57941 := rs (se 8 (by rfl) ⟨339, by rfl⟩) (B 679 (by norm_num) ⟨339, by rfl⟩ (by norm_num))
theorem R25177 : Reach 25177 := rs (se 2 (by rfl) ⟨9441, by rfl⟩) (B 18883 (by norm_num) ⟨9441, by rfl⟩ (by norm_num))
theorem R25181 : Reach 25181 := rs (se 3 (by rfl) ⟨4721, by rfl⟩) (B 9443 (by norm_num) ⟨4721, by rfl⟩ (by norm_num))
theorem R25185 : Reach 25185 := rs (se 2 (by rfl) ⟨9444, by rfl⟩) (B 18889 (by norm_num) ⟨9444, by rfl⟩ (by norm_num))
theorem R25189 : Reach 25189 := rs (se 4 (by rfl) ⟨2361, by rfl⟩) (B 4723 (by norm_num) ⟨2361, by rfl⟩ (by norm_num))
theorem R25193 : Reach 25193 := rs (se 2 (by rfl) ⟨9447, by rfl⟩) (B 18895 (by norm_num) ⟨9447, by rfl⟩ (by norm_num))
theorem R25197 : Reach 25197 := rs (se 3 (by rfl) ⟨4724, by rfl⟩) (B 9449 (by norm_num) ⟨4724, by rfl⟩ (by norm_num))
theorem R25201 : Reach 25201 := rs (se 2 (by rfl) ⟨9450, by rfl⟩) (B 18901 (by norm_num) ⟨9450, by rfl⟩ (by norm_num))
theorem R25205 : Reach 25205 := rs (se 5 (by rfl) ⟨1181, by rfl⟩) (B 2363 (by norm_num) ⟨1181, by rfl⟩ (by norm_num))
theorem R25209 : Reach 25209 := rs (se 2 (by rfl) ⟨9453, by rfl⟩) (B 18907 (by norm_num) ⟨9453, by rfl⟩ (by norm_num))
theorem R25213 : Reach 25213 := rs (se 3 (by rfl) ⟨4727, by rfl⟩) (B 9455 (by norm_num) ⟨4727, by rfl⟩ (by norm_num))
theorem R25217 : Reach 25217 := rs (se 2 (by rfl) ⟨9456, by rfl⟩) (B 18913 (by norm_num) ⟨9456, by rfl⟩ (by norm_num))
theorem R25221 : Reach 25221 := rs (se 4 (by rfl) ⟨2364, by rfl⟩) (B 4729 (by norm_num) ⟨2364, by rfl⟩ (by norm_num))
theorem R25225 : Reach 25225 := rs (se 2 (by rfl) ⟨9459, by rfl⟩) (B 18919 (by norm_num) ⟨9459, by rfl⟩ (by norm_num))
theorem R25229 : Reach 25229 := rs (se 3 (by rfl) ⟨4730, by rfl⟩) (B 9461 (by norm_num) ⟨4730, by rfl⟩ (by norm_num))
theorem R25233 : Reach 25233 := rs (se 2 (by rfl) ⟨9462, by rfl⟩) (B 18925 (by norm_num) ⟨9462, by rfl⟩ (by norm_num))
theorem R25237 : Reach 25237 := rs (se 6 (by rfl) ⟨591, by rfl⟩) (B 1183 (by norm_num) ⟨591, by rfl⟩ (by norm_num))
theorem R90773 : Reach 90773 := rs (se 6 (by rfl) ⟨2127, by rfl⟩) (B 4255 (by norm_num) ⟨2127, by rfl⟩ (by norm_num))
theorem R25241 : Reach 25241 := rs (se 2 (by rfl) ⟨9465, by rfl⟩) (B 18931 (by norm_num) ⟨9465, by rfl⟩ (by norm_num))
theorem R25245 : Reach 25245 := rs (se 3 (by rfl) ⟨4733, by rfl⟩) (B 9467 (by norm_num) ⟨4733, by rfl⟩ (by norm_num))
theorem R58013 : Reach 58013 := rs (se 3 (by rfl) ⟨10877, by rfl⟩) (B 21755 (by norm_num) ⟨10877, by rfl⟩ (by norm_num))
theorem R25249 : Reach 25249 := rs (se 2 (by rfl) ⟨9468, by rfl⟩) (B 18937 (by norm_num) ⟨9468, by rfl⟩ (by norm_num))
theorem R25253 : Reach 25253 := rs (se 4 (by rfl) ⟨2367, by rfl⟩) (B 4735 (by norm_num) ⟨2367, by rfl⟩ (by norm_num))
theorem R25257 : Reach 25257 := rs (se 2 (by rfl) ⟨9471, by rfl⟩) (B 18943 (by norm_num) ⟨9471, by rfl⟩ (by norm_num))
theorem R25261 : Reach 25261 := rs (se 3 (by rfl) ⟨4736, by rfl⟩) (B 9473 (by norm_num) ⟨4736, by rfl⟩ (by norm_num))
theorem R25265 : Reach 25265 := rs (se 2 (by rfl) ⟨9474, by rfl⟩) (B 18949 (by norm_num) ⟨9474, by rfl⟩ (by norm_num))
theorem R25269 : Reach 25269 := rs (se 5 (by rfl) ⟨1184, by rfl⟩) (B 2369 (by norm_num) ⟨1184, by rfl⟩ (by norm_num))
theorem R25273 : Reach 25273 := rs (se 2 (by rfl) ⟨9477, by rfl⟩) (B 18955 (by norm_num) ⟨9477, by rfl⟩ (by norm_num))
theorem R25277 : Reach 25277 := rs (se 3 (by rfl) ⟨4739, by rfl⟩) (B 9479 (by norm_num) ⟨4739, by rfl⟩ (by norm_num))
theorem R25281 : Reach 25281 := rs (se 2 (by rfl) ⟨9480, by rfl⟩) (B 18961 (by norm_num) ⟨9480, by rfl⟩ (by norm_num))
theorem R90821 : Reach 90821 := rs (se 4 (by rfl) ⟨8514, by rfl⟩) (B 17029 (by norm_num) ⟨8514, by rfl⟩ (by norm_num))
theorem R25285 : Reach 25285 := rs (se 4 (by rfl) ⟨2370, by rfl⟩) (B 4741 (by norm_num) ⟨2370, by rfl⟩ (by norm_num))
theorem R25289 : Reach 25289 := rs (se 2 (by rfl) ⟨9483, by rfl⟩) (B 18967 (by norm_num) ⟨9483, by rfl⟩ (by norm_num))
theorem R25293 : Reach 25293 := rs (se 3 (by rfl) ⟨4742, by rfl⟩) (B 9485 (by norm_num) ⟨4742, by rfl⟩ (by norm_num))
theorem R25297 : Reach 25297 := rs (se 2 (by rfl) ⟨9486, by rfl⟩) (B 18973 (by norm_num) ⟨9486, by rfl⟩ (by norm_num))
theorem R123605 : Reach 123605 := rs (se 7 (by rfl) ⟨1448, by rfl⟩) (B 2897 (by norm_num) ⟨1448, by rfl⟩ (by norm_num))
theorem R25301 : Reach 25301 := rs (se 7 (by rfl) ⟨296, by rfl⟩) (B 593 (by norm_num) ⟨296, by rfl⟩ (by norm_num))
theorem R25305 : Reach 25305 := rs (se 2 (by rfl) ⟨9489, by rfl⟩) (B 18979 (by norm_num) ⟨9489, by rfl⟩ (by norm_num))
theorem R25309 : Reach 25309 := rs (se 3 (by rfl) ⟨4745, by rfl⟩) (B 9491 (by norm_num) ⟨4745, by rfl⟩ (by norm_num))
theorem R25313 : Reach 25313 := rs (se 2 (by rfl) ⟨9492, by rfl⟩) (B 18985 (by norm_num) ⟨9492, by rfl⟩ (by norm_num))
theorem R25317 : Reach 25317 := rs (se 4 (by rfl) ⟨2373, by rfl⟩) (B 4747 (by norm_num) ⟨2373, by rfl⟩ (by norm_num))
theorem R58085 : Reach 58085 := rs (se 4 (by rfl) ⟨5445, by rfl⟩) (B 10891 (by norm_num) ⟨5445, by rfl⟩ (by norm_num))
theorem R25321 : Reach 25321 := rs (se 2 (by rfl) ⟨9495, by rfl⟩) (B 18991 (by norm_num) ⟨9495, by rfl⟩ (by norm_num))
theorem R25325 : Reach 25325 := rs (se 3 (by rfl) ⟨4748, by rfl⟩) (B 9497 (by norm_num) ⟨4748, by rfl⟩ (by norm_num))
theorem R25329 : Reach 25329 := rs (se 2 (by rfl) ⟨9498, by rfl⟩) (B 18997 (by norm_num) ⟨9498, by rfl⟩ (by norm_num))
theorem R25333 : Reach 25333 := rs (se 5 (by rfl) ⟨1187, by rfl⟩) (B 2375 (by norm_num) ⟨1187, by rfl⟩ (by norm_num))
theorem R25337 : Reach 25337 := rs (se 2 (by rfl) ⟨9501, by rfl⟩) (B 19003 (by norm_num) ⟨9501, by rfl⟩ (by norm_num))
theorem R25341 : Reach 25341 := rs (se 3 (by rfl) ⟨4751, by rfl⟩) (B 9503 (by norm_num) ⟨4751, by rfl⟩ (by norm_num))
theorem R25345 : Reach 25345 := rs (se 2 (by rfl) ⟨9504, by rfl⟩) (B 19009 (by norm_num) ⟨9504, by rfl⟩ (by norm_num))
theorem R25349 : Reach 25349 := rs (se 4 (by rfl) ⟨2376, by rfl⟩) (B 4753 (by norm_num) ⟨2376, by rfl⟩ (by norm_num))
theorem R25353 : Reach 25353 := rs (se 2 (by rfl) ⟨9507, by rfl⟩) (B 19015 (by norm_num) ⟨9507, by rfl⟩ (by norm_num))
theorem R25357 : Reach 25357 := rs (se 3 (by rfl) ⟨4754, by rfl⟩) (B 9509 (by norm_num) ⟨4754, by rfl⟩ (by norm_num))
theorem R25361 : Reach 25361 := rs (se 2 (by rfl) ⟨9510, by rfl⟩) (B 19021 (by norm_num) ⟨9510, by rfl⟩ (by norm_num))
theorem R25365 : Reach 25365 := rs (se 6 (by rfl) ⟨594, by rfl⟩) (B 1189 (by norm_num) ⟨594, by rfl⟩ (by norm_num))
theorem R25369 : Reach 25369 := rs (se 2 (by rfl) ⟨9513, by rfl⟩) (B 19027 (by norm_num) ⟨9513, by rfl⟩ (by norm_num))
theorem R25373 : Reach 25373 := rs (se 3 (by rfl) ⟨4757, by rfl⟩) (B 9515 (by norm_num) ⟨4757, by rfl⟩ (by norm_num))
theorem R25377 : Reach 25377 := rs (se 2 (by rfl) ⟨9516, by rfl⟩) (B 19033 (by norm_num) ⟨9516, by rfl⟩ (by norm_num))
theorem R25381 : Reach 25381 := rs (se 4 (by rfl) ⟨2379, by rfl⟩) (B 4759 (by norm_num) ⟨2379, by rfl⟩ (by norm_num))
theorem R25385 : Reach 25385 := rs (se 2 (by rfl) ⟨9519, by rfl⟩) (B 19039 (by norm_num) ⟨9519, by rfl⟩ (by norm_num))
theorem R25389 : Reach 25389 := rs (se 3 (by rfl) ⟨4760, by rfl⟩) (B 9521 (by norm_num) ⟨4760, by rfl⟩ (by norm_num))
theorem R58157 : Reach 58157 := rs (se 3 (by rfl) ⟨10904, by rfl⟩) (B 21809 (by norm_num) ⟨10904, by rfl⟩ (by norm_num))
theorem R25393 : Reach 25393 := rs (se 2 (by rfl) ⟨9522, by rfl⟩) (B 19045 (by norm_num) ⟨9522, by rfl⟩ (by norm_num))
theorem R25397 : Reach 25397 := rs (se 5 (by rfl) ⟨1190, by rfl⟩) (B 2381 (by norm_num) ⟨1190, by rfl⟩ (by norm_num))
theorem R25401 : Reach 25401 := rs (se 2 (by rfl) ⟨9525, by rfl⟩) (B 19051 (by norm_num) ⟨9525, by rfl⟩ (by norm_num))
theorem R25405 : Reach 25405 := rs (se 3 (by rfl) ⟨4763, by rfl⟩) (B 9527 (by norm_num) ⟨4763, by rfl⟩ (by norm_num))
theorem R25409 : Reach 25409 := rs (se 2 (by rfl) ⟨9528, by rfl⟩) (B 19057 (by norm_num) ⟨9528, by rfl⟩ (by norm_num))
theorem R25413 : Reach 25413 := rs (se 4 (by rfl) ⟨2382, by rfl⟩) (B 4765 (by norm_num) ⟨2382, by rfl⟩ (by norm_num))
theorem R25417 : Reach 25417 := rs (se 2 (by rfl) ⟨9531, by rfl⟩) (B 19063 (by norm_num) ⟨9531, by rfl⟩ (by norm_num))
theorem R25421 : Reach 25421 := rs (se 3 (by rfl) ⟨4766, by rfl⟩) (B 9533 (by norm_num) ⟨4766, by rfl⟩ (by norm_num))
theorem R25425 : Reach 25425 := rs (se 2 (by rfl) ⟨9534, by rfl⟩) (B 19069 (by norm_num) ⟨9534, by rfl⟩ (by norm_num))
theorem R25429 : Reach 25429 := rs (se 9 (by rfl) ⟨74, by rfl⟩) (B 149 (by norm_num) ⟨74, by rfl⟩ (by norm_num))
theorem R25433 : Reach 25433 := rs (se 2 (by rfl) ⟨9537, by rfl⟩) (B 19075 (by norm_num) ⟨9537, by rfl⟩ (by norm_num))
theorem R25437 : Reach 25437 := rs (se 3 (by rfl) ⟨4769, by rfl⟩) (B 9539 (by norm_num) ⟨4769, by rfl⟩ (by norm_num))
theorem R25441 : Reach 25441 := rs (se 2 (by rfl) ⟨9540, by rfl⟩) (B 19081 (by norm_num) ⟨9540, by rfl⟩ (by norm_num))
theorem R25445 : Reach 25445 := rs (se 4 (by rfl) ⟨2385, by rfl⟩) (B 4771 (by norm_num) ⟨2385, by rfl⟩ (by norm_num))
theorem R25449 : Reach 25449 := rs (se 2 (by rfl) ⟨9543, by rfl⟩) (B 19087 (by norm_num) ⟨9543, by rfl⟩ (by norm_num))
theorem R25453 : Reach 25453 := rs (se 3 (by rfl) ⟨4772, by rfl⟩) (B 9545 (by norm_num) ⟨4772, by rfl⟩ (by norm_num))
theorem R25457 : Reach 25457 := rs (se 2 (by rfl) ⟨9546, by rfl⟩) (B 19093 (by norm_num) ⟨9546, by rfl⟩ (by norm_num))
theorem R25461 : Reach 25461 := rs (se 5 (by rfl) ⟨1193, by rfl⟩) (B 2387 (by norm_num) ⟨1193, by rfl⟩ (by norm_num))
theorem R58229 : Reach 58229 := rs (se 5 (by rfl) ⟨2729, by rfl⟩) (B 5459 (by norm_num) ⟨2729, by rfl⟩ (by norm_num))
theorem R25465 : Reach 25465 := rs (se 2 (by rfl) ⟨9549, by rfl⟩) (B 19099 (by norm_num) ⟨9549, by rfl⟩ (by norm_num))
theorem R25469 : Reach 25469 := rs (se 3 (by rfl) ⟨4775, by rfl⟩) (B 9551 (by norm_num) ⟨4775, by rfl⟩ (by norm_num))
theorem R25473 : Reach 25473 := rs (se 2 (by rfl) ⟨9552, by rfl⟩) (B 19105 (by norm_num) ⟨9552, by rfl⟩ (by norm_num))
theorem R25477 : Reach 25477 := rs (se 4 (by rfl) ⟨2388, by rfl⟩) (B 4777 (by norm_num) ⟨2388, by rfl⟩ (by norm_num))
theorem R25481 : Reach 25481 := rs (se 2 (by rfl) ⟨9555, by rfl⟩) (B 19111 (by norm_num) ⟨9555, by rfl⟩ (by norm_num))
theorem R25485 : Reach 25485 := rs (se 3 (by rfl) ⟨4778, by rfl⟩) (B 9557 (by norm_num) ⟨4778, by rfl⟩ (by norm_num))
theorem R25489 : Reach 25489 := rs (se 2 (by rfl) ⟨9558, by rfl⟩) (B 19117 (by norm_num) ⟨9558, by rfl⟩ (by norm_num))
theorem R25493 : Reach 25493 := rs (se 6 (by rfl) ⟨597, by rfl⟩) (B 1195 (by norm_num) ⟨597, by rfl⟩ (by norm_num))
theorem R25497 : Reach 25497 := rs (se 2 (by rfl) ⟨9561, by rfl⟩) (B 19123 (by norm_num) ⟨9561, by rfl⟩ (by norm_num))
theorem R25501 : Reach 25501 := rs (se 3 (by rfl) ⟨4781, by rfl⟩) (B 9563 (by norm_num) ⟨4781, by rfl⟩ (by norm_num))
theorem R25505 : Reach 25505 := rs (se 2 (by rfl) ⟨9564, by rfl⟩) (B 19129 (by norm_num) ⟨9564, by rfl⟩ (by norm_num))
theorem R25509 : Reach 25509 := rs (se 4 (by rfl) ⟨2391, by rfl⟩) (B 4783 (by norm_num) ⟨2391, by rfl⟩ (by norm_num))
theorem R25513 : Reach 25513 := rs (se 2 (by rfl) ⟨9567, by rfl⟩) (B 19135 (by norm_num) ⟨9567, by rfl⟩ (by norm_num))
theorem R25517 : Reach 25517 := rs (se 3 (by rfl) ⟨4784, by rfl⟩) (B 9569 (by norm_num) ⟨4784, by rfl⟩ (by norm_num))
theorem R25521 : Reach 25521 := rs (se 2 (by rfl) ⟨9570, by rfl⟩) (B 19141 (by norm_num) ⟨9570, by rfl⟩ (by norm_num))
theorem R25525 : Reach 25525 := rs (se 5 (by rfl) ⟨1196, by rfl⟩) (B 2393 (by norm_num) ⟨1196, by rfl⟩ (by norm_num))
theorem R25529 : Reach 25529 := rs (se 2 (by rfl) ⟨9573, by rfl⟩) (B 19147 (by norm_num) ⟨9573, by rfl⟩ (by norm_num))
theorem R25533 : Reach 25533 := rs (se 3 (by rfl) ⟨4787, by rfl⟩) (B 9575 (by norm_num) ⟨4787, by rfl⟩ (by norm_num))
theorem R58301 : Reach 58301 := rs (se 3 (by rfl) ⟨10931, by rfl⟩) (B 21863 (by norm_num) ⟨10931, by rfl⟩ (by norm_num))
theorem R25537 : Reach 25537 := rs (se 2 (by rfl) ⟨9576, by rfl⟩) (B 19153 (by norm_num) ⟨9576, by rfl⟩ (by norm_num))
theorem R25541 : Reach 25541 := rs (se 4 (by rfl) ⟨2394, by rfl⟩) (B 4789 (by norm_num) ⟨2394, by rfl⟩ (by norm_num))
theorem R25545 : Reach 25545 := rs (se 2 (by rfl) ⟨9579, by rfl⟩) (B 19159 (by norm_num) ⟨9579, by rfl⟩ (by norm_num))
theorem R25549 : Reach 25549 := rs (se 3 (by rfl) ⟨4790, by rfl⟩) (B 9581 (by norm_num) ⟨4790, by rfl⟩ (by norm_num))
theorem R25553 : Reach 25553 := rs (se 2 (by rfl) ⟨9582, by rfl⟩) (B 19165 (by norm_num) ⟨9582, by rfl⟩ (by norm_num))
theorem R25557 : Reach 25557 := rs (se 7 (by rfl) ⟨299, by rfl⟩) (B 599 (by norm_num) ⟨299, by rfl⟩ (by norm_num))
theorem R25561 : Reach 25561 := rs (se 2 (by rfl) ⟨9585, by rfl⟩) (B 19171 (by norm_num) ⟨9585, by rfl⟩ (by norm_num))
theorem R25565 : Reach 25565 := rs (se 3 (by rfl) ⟨4793, by rfl⟩) (B 9587 (by norm_num) ⟨4793, by rfl⟩ (by norm_num))
theorem R25569 : Reach 25569 := rs (se 2 (by rfl) ⟨9588, by rfl⟩) (B 19177 (by norm_num) ⟨9588, by rfl⟩ (by norm_num))
theorem R25573 : Reach 25573 := rs (se 4 (by rfl) ⟨2397, by rfl⟩) (B 4795 (by norm_num) ⟨2397, by rfl⟩ (by norm_num))
theorem R25577 : Reach 25577 := rs (se 2 (by rfl) ⟨9591, by rfl⟩) (B 19183 (by norm_num) ⟨9591, by rfl⟩ (by norm_num))
theorem R25581 : Reach 25581 := rs (se 3 (by rfl) ⟨4796, by rfl⟩) (B 9593 (by norm_num) ⟨4796, by rfl⟩ (by norm_num))
theorem R25585 : Reach 25585 := rs (se 2 (by rfl) ⟨9594, by rfl⟩) (B 19189 (by norm_num) ⟨9594, by rfl⟩ (by norm_num))
theorem R25589 : Reach 25589 := rs (se 5 (by rfl) ⟨1199, by rfl⟩) (B 2399 (by norm_num) ⟨1199, by rfl⟩ (by norm_num))
theorem R25593 : Reach 25593 := rs (se 2 (by rfl) ⟨9597, by rfl⟩) (B 19195 (by norm_num) ⟨9597, by rfl⟩ (by norm_num))
theorem R25597 : Reach 25597 := rs (se 3 (by rfl) ⟨4799, by rfl⟩) (B 9599 (by norm_num) ⟨4799, by rfl⟩ (by norm_num))
theorem R25601 : Reach 25601 := rs (se 2 (by rfl) ⟨9600, by rfl⟩) (B 19201 (by norm_num) ⟨9600, by rfl⟩ (by norm_num))
theorem R25605 : Reach 25605 := rs (se 4 (by rfl) ⟨2400, by rfl⟩) (B 4801 (by norm_num) ⟨2400, by rfl⟩ (by norm_num))
theorem R58373 : Reach 58373 := rs (se 4 (by rfl) ⟨5472, by rfl⟩) (B 10945 (by norm_num) ⟨5472, by rfl⟩ (by norm_num))
theorem R25609 : Reach 25609 := rs (se 2 (by rfl) ⟨9603, by rfl⟩) (B 19207 (by norm_num) ⟨9603, by rfl⟩ (by norm_num))
theorem R25613 : Reach 25613 := rs (se 3 (by rfl) ⟨4802, by rfl⟩) (B 9605 (by norm_num) ⟨4802, by rfl⟩ (by norm_num))
theorem R25617 : Reach 25617 := rs (se 2 (by rfl) ⟨9606, by rfl⟩) (B 19213 (by norm_num) ⟨9606, by rfl⟩ (by norm_num))
theorem R25621 : Reach 25621 := rs (se 6 (by rfl) ⟨600, by rfl⟩) (B 1201 (by norm_num) ⟨600, by rfl⟩ (by norm_num))
theorem R25625 : Reach 25625 := rs (se 2 (by rfl) ⟨9609, by rfl⟩) (B 19219 (by norm_num) ⟨9609, by rfl⟩ (by norm_num))
theorem R25629 : Reach 25629 := rs (se 3 (by rfl) ⟨4805, by rfl⟩) (B 9611 (by norm_num) ⟨4805, by rfl⟩ (by norm_num))
theorem R25633 : Reach 25633 := rs (se 2 (by rfl) ⟨9612, by rfl⟩) (B 19225 (by norm_num) ⟨9612, by rfl⟩ (by norm_num))
theorem R25637 : Reach 25637 := rs (se 4 (by rfl) ⟨2403, by rfl⟩) (B 4807 (by norm_num) ⟨2403, by rfl⟩ (by norm_num))
theorem R25641 : Reach 25641 := rs (se 2 (by rfl) ⟨9615, by rfl⟩) (B 19231 (by norm_num) ⟨9615, by rfl⟩ (by norm_num))
theorem R25645 : Reach 25645 := rs (se 3 (by rfl) ⟨4808, by rfl⟩) (B 9617 (by norm_num) ⟨4808, by rfl⟩ (by norm_num))
theorem R25649 : Reach 25649 := rs (se 2 (by rfl) ⟨9618, by rfl⟩) (B 19237 (by norm_num) ⟨9618, by rfl⟩ (by norm_num))
theorem R25653 : Reach 25653 := rs (se 5 (by rfl) ⟨1202, by rfl⟩) (B 2405 (by norm_num) ⟨1202, by rfl⟩ (by norm_num))
theorem R25657 : Reach 25657 := rs (se 2 (by rfl) ⟨9621, by rfl⟩) (B 19243 (by norm_num) ⟨9621, by rfl⟩ (by norm_num))
theorem R25661 : Reach 25661 := rs (se 3 (by rfl) ⟨4811, by rfl⟩) (B 9623 (by norm_num) ⟨4811, by rfl⟩ (by norm_num))
theorem R25665 : Reach 25665 := rs (se 2 (by rfl) ⟨9624, by rfl⟩) (B 19249 (by norm_num) ⟨9624, by rfl⟩ (by norm_num))
theorem R25669 : Reach 25669 := rs (se 4 (by rfl) ⟨2406, by rfl⟩) (B 4813 (by norm_num) ⟨2406, by rfl⟩ (by norm_num))
theorem R91205 : Reach 91205 := rs (se 4 (by rfl) ⟨8550, by rfl⟩) (B 17101 (by norm_num) ⟨8550, by rfl⟩ (by norm_num))
theorem R25673 : Reach 25673 := rs (se 2 (by rfl) ⟨9627, by rfl⟩) (B 19255 (by norm_num) ⟨9627, by rfl⟩ (by norm_num))
theorem R25677 : Reach 25677 := rs (se 3 (by rfl) ⟨4814, by rfl⟩) (B 9629 (by norm_num) ⟨4814, by rfl⟩ (by norm_num))
theorem R58445 : Reach 58445 := rs (se 3 (by rfl) ⟨10958, by rfl⟩) (B 21917 (by norm_num) ⟨10958, by rfl⟩ (by norm_num))
theorem R25681 : Reach 25681 := rs (se 2 (by rfl) ⟨9630, by rfl⟩) (B 19261 (by norm_num) ⟨9630, by rfl⟩ (by norm_num))
theorem R25685 : Reach 25685 := rs (se 8 (by rfl) ⟨150, by rfl⟩) (B 301 (by norm_num) ⟨150, by rfl⟩ (by norm_num))
theorem R25689 : Reach 25689 := rs (se 2 (by rfl) ⟨9633, by rfl⟩) (B 19267 (by norm_num) ⟨9633, by rfl⟩ (by norm_num))
theorem R25693 : Reach 25693 := rs (se 3 (by rfl) ⟨4817, by rfl⟩) (B 9635 (by norm_num) ⟨4817, by rfl⟩ (by norm_num))
theorem R25697 : Reach 25697 := rs (se 2 (by rfl) ⟨9636, by rfl⟩) (B 19273 (by norm_num) ⟨9636, by rfl⟩ (by norm_num))
theorem R25701 : Reach 25701 := rs (se 4 (by rfl) ⟨2409, by rfl⟩) (B 4819 (by norm_num) ⟨2409, by rfl⟩ (by norm_num))
theorem R25705 : Reach 25705 := rs (se 2 (by rfl) ⟨9639, by rfl⟩) (B 19279 (by norm_num) ⟨9639, by rfl⟩ (by norm_num))
theorem R25709 : Reach 25709 := rs (se 3 (by rfl) ⟨4820, by rfl⟩) (B 9641 (by norm_num) ⟨4820, by rfl⟩ (by norm_num))
theorem R25713 : Reach 25713 := rs (se 2 (by rfl) ⟨9642, by rfl⟩) (B 19285 (by norm_num) ⟨9642, by rfl⟩ (by norm_num))
theorem R25717 : Reach 25717 := rs (se 5 (by rfl) ⟨1205, by rfl⟩) (B 2411 (by norm_num) ⟨1205, by rfl⟩ (by norm_num))
theorem R25721 : Reach 25721 := rs (se 2 (by rfl) ⟨9645, by rfl⟩) (B 19291 (by norm_num) ⟨9645, by rfl⟩ (by norm_num))
theorem R25725 : Reach 25725 := rs (se 3 (by rfl) ⟨4823, by rfl⟩) (B 9647 (by norm_num) ⟨4823, by rfl⟩ (by norm_num))
theorem R25729 : Reach 25729 := rs (se 2 (by rfl) ⟨9648, by rfl⟩) (B 19297 (by norm_num) ⟨9648, by rfl⟩ (by norm_num))
theorem R25733 : Reach 25733 := rs (se 4 (by rfl) ⟨2412, by rfl⟩) (B 4825 (by norm_num) ⟨2412, by rfl⟩ (by norm_num))
theorem R25737 : Reach 25737 := rs (se 2 (by rfl) ⟨9651, by rfl⟩) (B 19303 (by norm_num) ⟨9651, by rfl⟩ (by norm_num))
theorem R25741 : Reach 25741 := rs (se 3 (by rfl) ⟨4826, by rfl⟩) (B 9653 (by norm_num) ⟨4826, by rfl⟩ (by norm_num))
theorem R25745 : Reach 25745 := rs (se 2 (by rfl) ⟨9654, by rfl⟩) (B 19309 (by norm_num) ⟨9654, by rfl⟩ (by norm_num))
theorem R25749 : Reach 25749 := rs (se 6 (by rfl) ⟨603, by rfl⟩) (B 1207 (by norm_num) ⟨603, by rfl⟩ (by norm_num))
theorem R58517 : Reach 58517 := rs (se 6 (by rfl) ⟨1371, by rfl⟩) (B 2743 (by norm_num) ⟨1371, by rfl⟩ (by norm_num))
theorem R25753 : Reach 25753 := rs (se 2 (by rfl) ⟨9657, by rfl⟩) (B 19315 (by norm_num) ⟨9657, by rfl⟩ (by norm_num))
theorem R25757 : Reach 25757 := rs (se 3 (by rfl) ⟨4829, by rfl⟩) (B 9659 (by norm_num) ⟨4829, by rfl⟩ (by norm_num))
theorem R25761 : Reach 25761 := rs (se 2 (by rfl) ⟨9660, by rfl⟩) (B 19321 (by norm_num) ⟨9660, by rfl⟩ (by norm_num))
theorem R25765 : Reach 25765 := rs (se 4 (by rfl) ⟨2415, by rfl⟩) (B 4831 (by norm_num) ⟨2415, by rfl⟩ (by norm_num))
theorem R25769 : Reach 25769 := rs (se 2 (by rfl) ⟨9663, by rfl⟩) (B 19327 (by norm_num) ⟨9663, by rfl⟩ (by norm_num))
theorem R25773 : Reach 25773 := rs (se 3 (by rfl) ⟨4832, by rfl⟩) (B 9665 (by norm_num) ⟨4832, by rfl⟩ (by norm_num))
theorem R25777 : Reach 25777 := rs (se 2 (by rfl) ⟨9666, by rfl⟩) (B 19333 (by norm_num) ⟨9666, by rfl⟩ (by norm_num))
theorem R25781 : Reach 25781 := rs (se 5 (by rfl) ⟨1208, by rfl⟩) (B 2417 (by norm_num) ⟨1208, by rfl⟩ (by norm_num))
theorem R25785 : Reach 25785 := rs (se 2 (by rfl) ⟨9669, by rfl⟩) (B 19339 (by norm_num) ⟨9669, by rfl⟩ (by norm_num))
theorem R25789 : Reach 25789 := rs (se 3 (by rfl) ⟨4835, by rfl⟩) (B 9671 (by norm_num) ⟨4835, by rfl⟩ (by norm_num))
theorem R25793 : Reach 25793 := rs (se 2 (by rfl) ⟨9672, by rfl⟩) (B 19345 (by norm_num) ⟨9672, by rfl⟩ (by norm_num))
theorem R25797 : Reach 25797 := rs (se 4 (by rfl) ⟨2418, by rfl⟩) (B 4837 (by norm_num) ⟨2418, by rfl⟩ (by norm_num))
theorem R25801 : Reach 25801 := rs (se 2 (by rfl) ⟨9675, by rfl⟩) (B 19351 (by norm_num) ⟨9675, by rfl⟩ (by norm_num))
theorem R25805 : Reach 25805 := rs (se 3 (by rfl) ⟨4838, by rfl⟩) (B 9677 (by norm_num) ⟨4838, by rfl⟩ (by norm_num))
theorem R25809 : Reach 25809 := rs (se 2 (by rfl) ⟨9678, by rfl⟩) (B 19357 (by norm_num) ⟨9678, by rfl⟩ (by norm_num))
theorem R25813 : Reach 25813 := rs (se 7 (by rfl) ⟨302, by rfl⟩) (B 605 (by norm_num) ⟨302, by rfl⟩ (by norm_num))
theorem R25817 : Reach 25817 := rs (se 2 (by rfl) ⟨9681, by rfl⟩) (B 19363 (by norm_num) ⟨9681, by rfl⟩ (by norm_num))
theorem R58589 : Reach 58589 := rs (se 3 (by rfl) ⟨10985, by rfl⟩) (B 21971 (by norm_num) ⟨10985, by rfl⟩ (by norm_num))
theorem R25821 : Reach 25821 := rs (se 3 (by rfl) ⟨4841, by rfl⟩) (B 9683 (by norm_num) ⟨4841, by rfl⟩ (by norm_num))
theorem R25825 : Reach 25825 := rs (se 2 (by rfl) ⟨9684, by rfl⟩) (B 19369 (by norm_num) ⟨9684, by rfl⟩ (by norm_num))
theorem R25829 : Reach 25829 := rs (se 4 (by rfl) ⟨2421, by rfl⟩) (B 4843 (by norm_num) ⟨2421, by rfl⟩ (by norm_num))
theorem R25833 : Reach 25833 := rs (se 2 (by rfl) ⟨9687, by rfl⟩) (B 19375 (by norm_num) ⟨9687, by rfl⟩ (by norm_num))
theorem R25837 : Reach 25837 := rs (se 3 (by rfl) ⟨4844, by rfl⟩) (B 9689 (by norm_num) ⟨4844, by rfl⟩ (by norm_num))
theorem R25841 : Reach 25841 := rs (se 2 (by rfl) ⟨9690, by rfl⟩) (B 19381 (by norm_num) ⟨9690, by rfl⟩ (by norm_num))
theorem R25845 : Reach 25845 := rs (se 5 (by rfl) ⟨1211, by rfl⟩) (B 2423 (by norm_num) ⟨1211, by rfl⟩ (by norm_num))
theorem R25849 : Reach 25849 := rs (se 2 (by rfl) ⟨9693, by rfl⟩) (B 19387 (by norm_num) ⟨9693, by rfl⟩ (by norm_num))
theorem R25853 : Reach 25853 := rs (se 3 (by rfl) ⟨4847, by rfl⟩) (B 9695 (by norm_num) ⟨4847, by rfl⟩ (by norm_num))
theorem R25857 : Reach 25857 := rs (se 2 (by rfl) ⟨9696, by rfl⟩) (B 19393 (by norm_num) ⟨9696, by rfl⟩ (by norm_num))
theorem R25861 : Reach 25861 := rs (se 4 (by rfl) ⟨2424, by rfl⟩) (B 4849 (by norm_num) ⟨2424, by rfl⟩ (by norm_num))
theorem R25865 : Reach 25865 := rs (se 2 (by rfl) ⟨9699, by rfl⟩) (B 19399 (by norm_num) ⟨9699, by rfl⟩ (by norm_num))
theorem R25869 : Reach 25869 := rs (se 3 (by rfl) ⟨4850, by rfl⟩) (B 9701 (by norm_num) ⟨4850, by rfl⟩ (by norm_num))
theorem R25873 : Reach 25873 := rs (se 2 (by rfl) ⟨9702, by rfl⟩) (B 19405 (by norm_num) ⟨9702, by rfl⟩ (by norm_num))
theorem R25877 : Reach 25877 := rs (se 6 (by rfl) ⟨606, by rfl⟩) (B 1213 (by norm_num) ⟨606, by rfl⟩ (by norm_num))
theorem R25881 : Reach 25881 := rs (se 2 (by rfl) ⟨9705, by rfl⟩) (B 19411 (by norm_num) ⟨9705, by rfl⟩ (by norm_num))
theorem R25885 : Reach 25885 := rs (se 3 (by rfl) ⟨4853, by rfl⟩) (B 9707 (by norm_num) ⟨4853, by rfl⟩ (by norm_num))
theorem R25889 : Reach 25889 := rs (se 2 (by rfl) ⟨9708, by rfl⟩) (B 19417 (by norm_num) ⟨9708, by rfl⟩ (by norm_num))
theorem R25893 : Reach 25893 := rs (se 4 (by rfl) ⟨2427, by rfl⟩) (B 4855 (by norm_num) ⟨2427, by rfl⟩ (by norm_num))
theorem R58661 : Reach 58661 := rs (se 4 (by rfl) ⟨5499, by rfl⟩) (B 10999 (by norm_num) ⟨5499, by rfl⟩ (by norm_num))
theorem R25897 : Reach 25897 := rs (se 2 (by rfl) ⟨9711, by rfl⟩) (B 19423 (by norm_num) ⟨9711, by rfl⟩ (by norm_num))
theorem R25901 : Reach 25901 := rs (se 3 (by rfl) ⟨4856, by rfl⟩) (B 9713 (by norm_num) ⟨4856, by rfl⟩ (by norm_num))
theorem R25905 : Reach 25905 := rs (se 2 (by rfl) ⟨9714, by rfl⟩) (B 19429 (by norm_num) ⟨9714, by rfl⟩ (by norm_num))
theorem R25909 : Reach 25909 := rs (se 5 (by rfl) ⟨1214, by rfl⟩) (B 2429 (by norm_num) ⟨1214, by rfl⟩ (by norm_num))
theorem R25913 : Reach 25913 := rs (se 2 (by rfl) ⟨9717, by rfl⟩) (B 19435 (by norm_num) ⟨9717, by rfl⟩ (by norm_num))
theorem R25917 : Reach 25917 := rs (se 3 (by rfl) ⟨4859, by rfl⟩) (B 9719 (by norm_num) ⟨4859, by rfl⟩ (by norm_num))
theorem R25921 : Reach 25921 := rs (se 2 (by rfl) ⟨9720, by rfl⟩) (B 19441 (by norm_num) ⟨9720, by rfl⟩ (by norm_num))
theorem R25925 : Reach 25925 := rs (se 4 (by rfl) ⟨2430, by rfl⟩) (B 4861 (by norm_num) ⟨2430, by rfl⟩ (by norm_num))
theorem R25929 : Reach 25929 := rs (se 2 (by rfl) ⟨9723, by rfl⟩) (B 19447 (by norm_num) ⟨9723, by rfl⟩ (by norm_num))
theorem R25933 : Reach 25933 := rs (se 3 (by rfl) ⟨4862, by rfl⟩) (B 9725 (by norm_num) ⟨4862, by rfl⟩ (by norm_num))
theorem R25937 : Reach 25937 := rs (se 2 (by rfl) ⟨9726, by rfl⟩) (B 19453 (by norm_num) ⟨9726, by rfl⟩ (by norm_num))
theorem R25941 : Reach 25941 := rs (se 12 (by rfl) ⟨9, by rfl⟩) (B 19 (by norm_num) ⟨9, by rfl⟩ (by norm_num))
theorem R25945 : Reach 25945 := rs (se 2 (by rfl) ⟨9729, by rfl⟩) (B 19459 (by norm_num) ⟨9729, by rfl⟩ (by norm_num))
theorem R25949 : Reach 25949 := rs (se 3 (by rfl) ⟨4865, by rfl⟩) (B 9731 (by norm_num) ⟨4865, by rfl⟩ (by norm_num))
theorem R25953 : Reach 25953 := rs (se 2 (by rfl) ⟨9732, by rfl⟩) (B 19465 (by norm_num) ⟨9732, by rfl⟩ (by norm_num))
theorem R25957 : Reach 25957 := rs (se 4 (by rfl) ⟨2433, by rfl⟩) (B 4867 (by norm_num) ⟨2433, by rfl⟩ (by norm_num))
theorem R25961 : Reach 25961 := rs (se 2 (by rfl) ⟨9735, by rfl⟩) (B 19471 (by norm_num) ⟨9735, by rfl⟩ (by norm_num))
theorem R25965 : Reach 25965 := rs (se 3 (by rfl) ⟨4868, by rfl⟩) (B 9737 (by norm_num) ⟨4868, by rfl⟩ (by norm_num))
theorem R58733 : Reach 58733 := rs (se 3 (by rfl) ⟨11012, by rfl⟩) (B 22025 (by norm_num) ⟨11012, by rfl⟩ (by norm_num))
theorem R25969 : Reach 25969 := rs (se 2 (by rfl) ⟨9738, by rfl⟩) (B 19477 (by norm_num) ⟨9738, by rfl⟩ (by norm_num))
theorem R25973 : Reach 25973 := rs (se 5 (by rfl) ⟨1217, by rfl⟩) (B 2435 (by norm_num) ⟨1217, by rfl⟩ (by norm_num))
theorem R25977 : Reach 25977 := rs (se 2 (by rfl) ⟨9741, by rfl⟩) (B 19483 (by norm_num) ⟨9741, by rfl⟩ (by norm_num))
theorem R25981 : Reach 25981 := rs (se 3 (by rfl) ⟨4871, by rfl⟩) (B 9743 (by norm_num) ⟨4871, by rfl⟩ (by norm_num))
theorem R25985 : Reach 25985 := rs (se 2 (by rfl) ⟨9744, by rfl⟩) (B 19489 (by norm_num) ⟨9744, by rfl⟩ (by norm_num))
theorem R25989 : Reach 25989 := rs (se 4 (by rfl) ⟨2436, by rfl⟩) (B 4873 (by norm_num) ⟨2436, by rfl⟩ (by norm_num))
theorem R25993 : Reach 25993 := rs (se 2 (by rfl) ⟨9747, by rfl⟩) (B 19495 (by norm_num) ⟨9747, by rfl⟩ (by norm_num))
theorem R25997 : Reach 25997 := rs (se 3 (by rfl) ⟨4874, by rfl⟩) (B 9749 (by norm_num) ⟨4874, by rfl⟩ (by norm_num))
theorem R26001 : Reach 26001 := rs (se 2 (by rfl) ⟨9750, by rfl⟩) (B 19501 (by norm_num) ⟨9750, by rfl⟩ (by norm_num))
theorem R26005 : Reach 26005 := rs (se 6 (by rfl) ⟨609, by rfl⟩) (B 1219 (by norm_num) ⟨609, by rfl⟩ (by norm_num))
theorem R26009 : Reach 26009 := rs (se 2 (by rfl) ⟨9753, by rfl⟩) (B 19507 (by norm_num) ⟨9753, by rfl⟩ (by norm_num))
theorem R26013 : Reach 26013 := rs (se 3 (by rfl) ⟨4877, by rfl⟩) (B 9755 (by norm_num) ⟨4877, by rfl⟩ (by norm_num))
theorem R26017 : Reach 26017 := rs (se 2 (by rfl) ⟨9756, by rfl⟩) (B 19513 (by norm_num) ⟨9756, by rfl⟩ (by norm_num))
theorem R26021 : Reach 26021 := rs (se 4 (by rfl) ⟨2439, by rfl⟩) (B 4879 (by norm_num) ⟨2439, by rfl⟩ (by norm_num))
theorem R26025 : Reach 26025 := rs (se 2 (by rfl) ⟨9759, by rfl⟩) (B 19519 (by norm_num) ⟨9759, by rfl⟩ (by norm_num))
theorem R26029 : Reach 26029 := rs (se 3 (by rfl) ⟨4880, by rfl⟩) (B 9761 (by norm_num) ⟨4880, by rfl⟩ (by norm_num))
theorem R26033 : Reach 26033 := rs (se 2 (by rfl) ⟨9762, by rfl⟩) (B 19525 (by norm_num) ⟨9762, by rfl⟩ (by norm_num))
theorem R26037 : Reach 26037 := rs (se 5 (by rfl) ⟨1220, by rfl⟩) (B 2441 (by norm_num) ⟨1220, by rfl⟩ (by norm_num))
theorem R58805 : Reach 58805 := rs (se 5 (by rfl) ⟨2756, by rfl⟩) (B 5513 (by norm_num) ⟨2756, by rfl⟩ (by norm_num))
theorem R26041 : Reach 26041 := rs (se 2 (by rfl) ⟨9765, by rfl⟩) (B 19531 (by norm_num) ⟨9765, by rfl⟩ (by norm_num))
theorem R26045 : Reach 26045 := rs (se 3 (by rfl) ⟨4883, by rfl⟩) (B 9767 (by norm_num) ⟨4883, by rfl⟩ (by norm_num))
theorem R26049 : Reach 26049 := rs (se 2 (by rfl) ⟨9768, by rfl⟩) (B 19537 (by norm_num) ⟨9768, by rfl⟩ (by norm_num))
theorem R26053 : Reach 26053 := rs (se 4 (by rfl) ⟨2442, by rfl⟩) (B 4885 (by norm_num) ⟨2442, by rfl⟩ (by norm_num))
theorem R26057 : Reach 26057 := rs (se 2 (by rfl) ⟨9771, by rfl⟩) (B 19543 (by norm_num) ⟨9771, by rfl⟩ (by norm_num))
theorem R26061 : Reach 26061 := rs (se 3 (by rfl) ⟨4886, by rfl⟩) (B 9773 (by norm_num) ⟨4886, by rfl⟩ (by norm_num))
theorem R26065 : Reach 26065 := rs (se 2 (by rfl) ⟨9774, by rfl⟩) (B 19549 (by norm_num) ⟨9774, by rfl⟩ (by norm_num))
theorem R26069 : Reach 26069 := rs (se 7 (by rfl) ⟨305, by rfl⟩) (B 611 (by norm_num) ⟨305, by rfl⟩ (by norm_num))
theorem R26073 : Reach 26073 := rs (se 2 (by rfl) ⟨9777, by rfl⟩) (B 19555 (by norm_num) ⟨9777, by rfl⟩ (by norm_num))
theorem R26077 : Reach 26077 := rs (se 3 (by rfl) ⟨4889, by rfl⟩) (B 9779 (by norm_num) ⟨4889, by rfl⟩ (by norm_num))
theorem R26081 : Reach 26081 := rs (se 2 (by rfl) ⟨9780, by rfl⟩) (B 19561 (by norm_num) ⟨9780, by rfl⟩ (by norm_num))
theorem R26085 : Reach 26085 := rs (se 4 (by rfl) ⟨2445, by rfl⟩) (B 4891 (by norm_num) ⟨2445, by rfl⟩ (by norm_num))
theorem R26089 : Reach 26089 := rs (se 2 (by rfl) ⟨9783, by rfl⟩) (B 19567 (by norm_num) ⟨9783, by rfl⟩ (by norm_num))
theorem R26093 : Reach 26093 := rs (se 3 (by rfl) ⟨4892, by rfl⟩) (B 9785 (by norm_num) ⟨4892, by rfl⟩ (by norm_num))
theorem R26097 : Reach 26097 := rs (se 2 (by rfl) ⟨9786, by rfl⟩) (B 19573 (by norm_num) ⟨9786, by rfl⟩ (by norm_num))
theorem R26101 : Reach 26101 := rs (se 5 (by rfl) ⟨1223, by rfl⟩) (B 2447 (by norm_num) ⟨1223, by rfl⟩ (by norm_num))
theorem R26105 : Reach 26105 := rs (se 2 (by rfl) ⟨9789, by rfl⟩) (B 19579 (by norm_num) ⟨9789, by rfl⟩ (by norm_num))
theorem R26109 : Reach 26109 := rs (se 3 (by rfl) ⟨4895, by rfl⟩) (B 9791 (by norm_num) ⟨4895, by rfl⟩ (by norm_num))
theorem R58877 : Reach 58877 := rs (se 3 (by rfl) ⟨11039, by rfl⟩) (B 22079 (by norm_num) ⟨11039, by rfl⟩ (by norm_num))
theorem R26113 : Reach 26113 := rs (se 2 (by rfl) ⟨9792, by rfl⟩) (B 19585 (by norm_num) ⟨9792, by rfl⟩ (by norm_num))
theorem R26117 : Reach 26117 := rs (se 4 (by rfl) ⟨2448, by rfl⟩) (B 4897 (by norm_num) ⟨2448, by rfl⟩ (by norm_num))
theorem R26121 : Reach 26121 := rs (se 2 (by rfl) ⟨9795, by rfl⟩) (B 19591 (by norm_num) ⟨9795, by rfl⟩ (by norm_num))
theorem R26125 : Reach 26125 := rs (se 3 (by rfl) ⟨4898, by rfl⟩) (B 9797 (by norm_num) ⟨4898, by rfl⟩ (by norm_num))
theorem R26129 : Reach 26129 := rs (se 2 (by rfl) ⟨9798, by rfl⟩) (B 19597 (by norm_num) ⟨9798, by rfl⟩ (by norm_num))
theorem R26133 : Reach 26133 := rs (se 6 (by rfl) ⟨612, by rfl⟩) (B 1225 (by norm_num) ⟨612, by rfl⟩ (by norm_num))
theorem R26137 : Reach 26137 := rs (se 2 (by rfl) ⟨9801, by rfl⟩) (B 19603 (by norm_num) ⟨9801, by rfl⟩ (by norm_num))
theorem R26141 : Reach 26141 := rs (se 3 (by rfl) ⟨4901, by rfl⟩) (B 9803 (by norm_num) ⟨4901, by rfl⟩ (by norm_num))
theorem R26145 : Reach 26145 := rs (se 2 (by rfl) ⟨9804, by rfl⟩) (B 19609 (by norm_num) ⟨9804, by rfl⟩ (by norm_num))
theorem R26149 : Reach 26149 := rs (se 4 (by rfl) ⟨2451, by rfl⟩) (B 4903 (by norm_num) ⟨2451, by rfl⟩ (by norm_num))
theorem R26153 : Reach 26153 := rs (se 2 (by rfl) ⟨9807, by rfl⟩) (B 19615 (by norm_num) ⟨9807, by rfl⟩ (by norm_num))
theorem R26157 : Reach 26157 := rs (se 3 (by rfl) ⟨4904, by rfl⟩) (B 9809 (by norm_num) ⟨4904, by rfl⟩ (by norm_num))
theorem R26161 : Reach 26161 := rs (se 2 (by rfl) ⟨9810, by rfl⟩) (B 19621 (by norm_num) ⟨9810, by rfl⟩ (by norm_num))
theorem R26165 : Reach 26165 := rs (se 5 (by rfl) ⟨1226, by rfl⟩) (B 2453 (by norm_num) ⟨1226, by rfl⟩ (by norm_num))
theorem R26169 : Reach 26169 := rs (se 2 (by rfl) ⟨9813, by rfl⟩) (B 19627 (by norm_num) ⟨9813, by rfl⟩ (by norm_num))
theorem R26173 : Reach 26173 := rs (se 3 (by rfl) ⟨4907, by rfl⟩) (B 9815 (by norm_num) ⟨4907, by rfl⟩ (by norm_num))
theorem R26177 : Reach 26177 := rs (se 2 (by rfl) ⟨9816, by rfl⟩) (B 19633 (by norm_num) ⟨9816, by rfl⟩ (by norm_num))
theorem R26181 : Reach 26181 := rs (se 4 (by rfl) ⟨2454, by rfl⟩) (B 4909 (by norm_num) ⟨2454, by rfl⟩ (by norm_num))
theorem R58949 : Reach 58949 := rs (se 4 (by rfl) ⟨5526, by rfl⟩) (B 11053 (by norm_num) ⟨5526, by rfl⟩ (by norm_num))
theorem R26185 : Reach 26185 := rs (se 2 (by rfl) ⟨9819, by rfl⟩) (B 19639 (by norm_num) ⟨9819, by rfl⟩ (by norm_num))
theorem R26189 : Reach 26189 := rs (se 3 (by rfl) ⟨4910, by rfl⟩) (B 9821 (by norm_num) ⟨4910, by rfl⟩ (by norm_num))
theorem R26193 : Reach 26193 := rs (se 2 (by rfl) ⟨9822, by rfl⟩) (B 19645 (by norm_num) ⟨9822, by rfl⟩ (by norm_num))
theorem R26197 : Reach 26197 := rs (se 8 (by rfl) ⟨153, by rfl⟩) (B 307 (by norm_num) ⟨153, by rfl⟩ (by norm_num))
theorem R26201 : Reach 26201 := rs (se 2 (by rfl) ⟨9825, by rfl⟩) (B 19651 (by norm_num) ⟨9825, by rfl⟩ (by norm_num))
theorem R26205 : Reach 26205 := rs (se 3 (by rfl) ⟨4913, by rfl⟩) (B 9827 (by norm_num) ⟨4913, by rfl⟩ (by norm_num))
theorem R26209 : Reach 26209 := rs (se 2 (by rfl) ⟨9828, by rfl⟩) (B 19657 (by norm_num) ⟨9828, by rfl⟩ (by norm_num))
theorem R26213 : Reach 26213 := rs (se 4 (by rfl) ⟨2457, by rfl⟩) (B 4915 (by norm_num) ⟨2457, by rfl⟩ (by norm_num))
theorem R26217 : Reach 26217 := rs (se 2 (by rfl) ⟨9831, by rfl⟩) (B 19663 (by norm_num) ⟨9831, by rfl⟩ (by norm_num))
theorem R26221 : Reach 26221 := rs (se 3 (by rfl) ⟨4916, by rfl⟩) (B 9833 (by norm_num) ⟨4916, by rfl⟩ (by norm_num))
theorem R26225 : Reach 26225 := rs (se 2 (by rfl) ⟨9834, by rfl⟩) (B 19669 (by norm_num) ⟨9834, by rfl⟩ (by norm_num))
theorem R26229 : Reach 26229 := rs (se 5 (by rfl) ⟨1229, by rfl⟩) (B 2459 (by norm_num) ⟨1229, by rfl⟩ (by norm_num))
theorem R26233 : Reach 26233 := rs (se 2 (by rfl) ⟨9837, by rfl⟩) (B 19675 (by norm_num) ⟨9837, by rfl⟩ (by norm_num))
theorem R26237 : Reach 26237 := rs (se 3 (by rfl) ⟨4919, by rfl⟩) (B 9839 (by norm_num) ⟨4919, by rfl⟩ (by norm_num))
theorem R26241 : Reach 26241 := rs (se 2 (by rfl) ⟨9840, by rfl⟩) (B 19681 (by norm_num) ⟨9840, by rfl⟩ (by norm_num))
theorem R26245 : Reach 26245 := rs (se 4 (by rfl) ⟨2460, by rfl⟩) (B 4921 (by norm_num) ⟨2460, by rfl⟩ (by norm_num))
theorem R26249 : Reach 26249 := rs (se 2 (by rfl) ⟨9843, by rfl⟩) (B 19687 (by norm_num) ⟨9843, by rfl⟩ (by norm_num))
theorem R59021 : Reach 59021 := rs (se 3 (by rfl) ⟨11066, by rfl⟩) (B 22133 (by norm_num) ⟨11066, by rfl⟩ (by norm_num))
theorem R26253 : Reach 26253 := rs (se 3 (by rfl) ⟨4922, by rfl⟩) (B 9845 (by norm_num) ⟨4922, by rfl⟩ (by norm_num))
theorem R26257 : Reach 26257 := rs (se 2 (by rfl) ⟨9846, by rfl⟩) (B 19693 (by norm_num) ⟨9846, by rfl⟩ (by norm_num))
theorem R26261 : Reach 26261 := rs (se 6 (by rfl) ⟨615, by rfl⟩) (B 1231 (by norm_num) ⟨615, by rfl⟩ (by norm_num))
theorem R26265 : Reach 26265 := rs (se 2 (by rfl) ⟨9849, by rfl⟩) (B 19699 (by norm_num) ⟨9849, by rfl⟩ (by norm_num))
theorem R26269 : Reach 26269 := rs (se 3 (by rfl) ⟨4925, by rfl⟩) (B 9851 (by norm_num) ⟨4925, by rfl⟩ (by norm_num))
theorem R26273 : Reach 26273 := rs (se 2 (by rfl) ⟨9852, by rfl⟩) (B 19705 (by norm_num) ⟨9852, by rfl⟩ (by norm_num))
theorem R26277 : Reach 26277 := rs (se 4 (by rfl) ⟨2463, by rfl⟩) (B 4927 (by norm_num) ⟨2463, by rfl⟩ (by norm_num))
theorem R26281 : Reach 26281 := rs (se 2 (by rfl) ⟨9855, by rfl⟩) (B 19711 (by norm_num) ⟨9855, by rfl⟩ (by norm_num))
theorem R26285 : Reach 26285 := rs (se 3 (by rfl) ⟨4928, by rfl⟩) (B 9857 (by norm_num) ⟨4928, by rfl⟩ (by norm_num))
theorem R26289 : Reach 26289 := rs (se 2 (by rfl) ⟨9858, by rfl⟩) (B 19717 (by norm_num) ⟨9858, by rfl⟩ (by norm_num))
theorem R26293 : Reach 26293 := rs (se 5 (by rfl) ⟨1232, by rfl⟩) (B 2465 (by norm_num) ⟨1232, by rfl⟩ (by norm_num))
theorem R26297 : Reach 26297 := rs (se 2 (by rfl) ⟨9861, by rfl⟩) (B 19723 (by norm_num) ⟨9861, by rfl⟩ (by norm_num))
theorem R26301 : Reach 26301 := rs (se 3 (by rfl) ⟨4931, by rfl⟩) (B 9863 (by norm_num) ⟨4931, by rfl⟩ (by norm_num))
theorem R26305 : Reach 26305 := rs (se 2 (by rfl) ⟨9864, by rfl⟩) (B 19729 (by norm_num) ⟨9864, by rfl⟩ (by norm_num))
theorem R26309 : Reach 26309 := rs (se 4 (by rfl) ⟨2466, by rfl⟩) (B 4933 (by norm_num) ⟨2466, by rfl⟩ (by norm_num))
theorem R26313 : Reach 26313 := rs (se 2 (by rfl) ⟨9867, by rfl⟩) (B 19735 (by norm_num) ⟨9867, by rfl⟩ (by norm_num))
theorem R26317 : Reach 26317 := rs (se 3 (by rfl) ⟨4934, by rfl⟩) (B 9869 (by norm_num) ⟨4934, by rfl⟩ (by norm_num))
theorem R26321 : Reach 26321 := rs (se 2 (by rfl) ⟨9870, by rfl⟩) (B 19741 (by norm_num) ⟨9870, by rfl⟩ (by norm_num))
theorem R59093 : Reach 59093 := rs (se 7 (by rfl) ⟨692, by rfl⟩) (B 1385 (by norm_num) ⟨692, by rfl⟩ (by norm_num))
theorem R26325 : Reach 26325 := rs (se 7 (by rfl) ⟨308, by rfl⟩) (B 617 (by norm_num) ⟨308, by rfl⟩ (by norm_num))
theorem R26329 : Reach 26329 := rs (se 2 (by rfl) ⟨9873, by rfl⟩) (B 19747 (by norm_num) ⟨9873, by rfl⟩ (by norm_num))
theorem R26333 : Reach 26333 := rs (se 3 (by rfl) ⟨4937, by rfl⟩) (B 9875 (by norm_num) ⟨4937, by rfl⟩ (by norm_num))
theorem R26337 : Reach 26337 := rs (se 2 (by rfl) ⟨9876, by rfl⟩) (B 19753 (by norm_num) ⟨9876, by rfl⟩ (by norm_num))
theorem R26341 : Reach 26341 := rs (se 4 (by rfl) ⟨2469, by rfl⟩) (B 4939 (by norm_num) ⟨2469, by rfl⟩ (by norm_num))
theorem R26345 : Reach 26345 := rs (se 2 (by rfl) ⟨9879, by rfl⟩) (B 19759 (by norm_num) ⟨9879, by rfl⟩ (by norm_num))
theorem R26349 : Reach 26349 := rs (se 3 (by rfl) ⟨4940, by rfl⟩) (B 9881 (by norm_num) ⟨4940, by rfl⟩ (by norm_num))
theorem R26353 : Reach 26353 := rs (se 2 (by rfl) ⟨9882, by rfl⟩) (B 19765 (by norm_num) ⟨9882, by rfl⟩ (by norm_num))
theorem R26357 : Reach 26357 := rs (se 5 (by rfl) ⟨1235, by rfl⟩) (B 2471 (by norm_num) ⟨1235, by rfl⟩ (by norm_num))
theorem R26361 : Reach 26361 := rs (se 2 (by rfl) ⟨9885, by rfl⟩) (B 19771 (by norm_num) ⟨9885, by rfl⟩ (by norm_num))
theorem R26365 : Reach 26365 := rs (se 3 (by rfl) ⟨4943, by rfl⟩) (B 9887 (by norm_num) ⟨4943, by rfl⟩ (by norm_num))
theorem R26369 : Reach 26369 := rs (se 2 (by rfl) ⟨9888, by rfl⟩) (B 19777 (by norm_num) ⟨9888, by rfl⟩ (by norm_num))
theorem R26373 : Reach 26373 := rs (se 4 (by rfl) ⟨2472, by rfl⟩) (B 4945 (by norm_num) ⟨2472, by rfl⟩ (by norm_num))
theorem R26377 : Reach 26377 := rs (se 2 (by rfl) ⟨9891, by rfl⟩) (B 19783 (by norm_num) ⟨9891, by rfl⟩ (by norm_num))
theorem R26381 : Reach 26381 := rs (se 3 (by rfl) ⟨4946, by rfl⟩) (B 9893 (by norm_num) ⟨4946, by rfl⟩ (by norm_num))
theorem R26385 : Reach 26385 := rs (se 2 (by rfl) ⟨9894, by rfl⟩) (B 19789 (by norm_num) ⟨9894, by rfl⟩ (by norm_num))
theorem R26389 : Reach 26389 := rs (se 6 (by rfl) ⟨618, by rfl⟩) (B 1237 (by norm_num) ⟨618, by rfl⟩ (by norm_num))
theorem R26393 : Reach 26393 := rs (se 2 (by rfl) ⟨9897, by rfl⟩) (B 19795 (by norm_num) ⟨9897, by rfl⟩ (by norm_num))
theorem R59165 : Reach 59165 := rs (se 3 (by rfl) ⟨11093, by rfl⟩) (B 22187 (by norm_num) ⟨11093, by rfl⟩ (by norm_num))
theorem R26397 : Reach 26397 := rs (se 3 (by rfl) ⟨4949, by rfl⟩) (B 9899 (by norm_num) ⟨4949, by rfl⟩ (by norm_num))
theorem R26401 : Reach 26401 := rs (se 2 (by rfl) ⟨9900, by rfl⟩) (B 19801 (by norm_num) ⟨9900, by rfl⟩ (by norm_num))
theorem R26405 : Reach 26405 := rs (se 4 (by rfl) ⟨2475, by rfl⟩) (B 4951 (by norm_num) ⟨2475, by rfl⟩ (by norm_num))
theorem R26409 : Reach 26409 := rs (se 2 (by rfl) ⟨9903, by rfl⟩) (B 19807 (by norm_num) ⟨9903, by rfl⟩ (by norm_num))
theorem R26413 : Reach 26413 := rs (se 3 (by rfl) ⟨4952, by rfl⟩) (B 9905 (by norm_num) ⟨4952, by rfl⟩ (by norm_num))
theorem R26417 : Reach 26417 := rs (se 2 (by rfl) ⟨9906, by rfl⟩) (B 19813 (by norm_num) ⟨9906, by rfl⟩ (by norm_num))
theorem R26421 : Reach 26421 := rs (se 5 (by rfl) ⟨1238, by rfl⟩) (B 2477 (by norm_num) ⟨1238, by rfl⟩ (by norm_num))
theorem R26425 : Reach 26425 := rs (se 2 (by rfl) ⟨9909, by rfl⟩) (B 19819 (by norm_num) ⟨9909, by rfl⟩ (by norm_num))
theorem R26429 : Reach 26429 := rs (se 3 (by rfl) ⟨4955, by rfl⟩) (B 9911 (by norm_num) ⟨4955, by rfl⟩ (by norm_num))
theorem R26433 : Reach 26433 := rs (se 2 (by rfl) ⟨9912, by rfl⟩) (B 19825 (by norm_num) ⟨9912, by rfl⟩ (by norm_num))
theorem R26437 : Reach 26437 := rs (se 4 (by rfl) ⟨2478, by rfl⟩) (B 4957 (by norm_num) ⟨2478, by rfl⟩ (by norm_num))
theorem R26441 : Reach 26441 := rs (se 2 (by rfl) ⟨9915, by rfl⟩) (B 19831 (by norm_num) ⟨9915, by rfl⟩ (by norm_num))
theorem R26445 : Reach 26445 := rs (se 3 (by rfl) ⟨4958, by rfl⟩) (B 9917 (by norm_num) ⟨4958, by rfl⟩ (by norm_num))
theorem R26449 : Reach 26449 := rs (se 2 (by rfl) ⟨9918, by rfl⟩) (B 19837 (by norm_num) ⟨9918, by rfl⟩ (by norm_num))
theorem R26453 : Reach 26453 := rs (se 9 (by rfl) ⟨77, by rfl⟩) (B 155 (by norm_num) ⟨77, by rfl⟩ (by norm_num))
theorem R26457 : Reach 26457 := rs (se 2 (by rfl) ⟨9921, by rfl⟩) (B 19843 (by norm_num) ⟨9921, by rfl⟩ (by norm_num))
theorem R26461 : Reach 26461 := rs (se 3 (by rfl) ⟨4961, by rfl⟩) (B 9923 (by norm_num) ⟨4961, by rfl⟩ (by norm_num))
theorem R26465 : Reach 26465 := rs (se 2 (by rfl) ⟨9924, by rfl⟩) (B 19849 (by norm_num) ⟨9924, by rfl⟩ (by norm_num))
theorem R59237 : Reach 59237 := rs (se 4 (by rfl) ⟨5553, by rfl⟩) (B 11107 (by norm_num) ⟨5553, by rfl⟩ (by norm_num))
theorem R26469 : Reach 26469 := rs (se 4 (by rfl) ⟨2481, by rfl⟩) (B 4963 (by norm_num) ⟨2481, by rfl⟩ (by norm_num))
theorem R26473 : Reach 26473 := rs (se 2 (by rfl) ⟨9927, by rfl⟩) (B 19855 (by norm_num) ⟨9927, by rfl⟩ (by norm_num))
theorem R26477 : Reach 26477 := rs (se 3 (by rfl) ⟨4964, by rfl⟩) (B 9929 (by norm_num) ⟨4964, by rfl⟩ (by norm_num))
theorem R26481 : Reach 26481 := rs (se 2 (by rfl) ⟨9930, by rfl⟩) (B 19861 (by norm_num) ⟨9930, by rfl⟩ (by norm_num))
theorem R26485 : Reach 26485 := rs (se 5 (by rfl) ⟨1241, by rfl⟩) (B 2483 (by norm_num) ⟨1241, by rfl⟩ (by norm_num))
theorem R26489 : Reach 26489 := rs (se 2 (by rfl) ⟨9933, by rfl⟩) (B 19867 (by norm_num) ⟨9933, by rfl⟩ (by norm_num))
theorem R26493 : Reach 26493 := rs (se 3 (by rfl) ⟨4967, by rfl⟩) (B 9935 (by norm_num) ⟨4967, by rfl⟩ (by norm_num))
theorem R26497 : Reach 26497 := rs (se 2 (by rfl) ⟨9936, by rfl⟩) (B 19873 (by norm_num) ⟨9936, by rfl⟩ (by norm_num))
theorem R26501 : Reach 26501 := rs (se 4 (by rfl) ⟨2484, by rfl⟩) (B 4969 (by norm_num) ⟨2484, by rfl⟩ (by norm_num))
theorem R26505 : Reach 26505 := rs (se 2 (by rfl) ⟨9939, by rfl⟩) (B 19879 (by norm_num) ⟨9939, by rfl⟩ (by norm_num))
theorem R26509 : Reach 26509 := rs (se 3 (by rfl) ⟨4970, by rfl⟩) (B 9941 (by norm_num) ⟨4970, by rfl⟩ (by norm_num))
theorem R26513 : Reach 26513 := rs (se 2 (by rfl) ⟨9942, by rfl⟩) (B 19885 (by norm_num) ⟨9942, by rfl⟩ (by norm_num))
theorem R26517 : Reach 26517 := rs (se 6 (by rfl) ⟨621, by rfl⟩) (B 1243 (by norm_num) ⟨621, by rfl⟩ (by norm_num))
theorem R26521 : Reach 26521 := rs (se 2 (by rfl) ⟨9945, by rfl⟩) (B 19891 (by norm_num) ⟨9945, by rfl⟩ (by norm_num))
theorem R26525 : Reach 26525 := rs (se 3 (by rfl) ⟨4973, by rfl⟩) (B 9947 (by norm_num) ⟨4973, by rfl⟩ (by norm_num))
theorem R26529 : Reach 26529 := rs (se 2 (by rfl) ⟨9948, by rfl⟩) (B 19897 (by norm_num) ⟨9948, by rfl⟩ (by norm_num))
theorem R26533 : Reach 26533 := rs (se 4 (by rfl) ⟨2487, by rfl⟩) (B 4975 (by norm_num) ⟨2487, by rfl⟩ (by norm_num))
theorem R26537 : Reach 26537 := rs (se 2 (by rfl) ⟨9951, by rfl⟩) (B 19903 (by norm_num) ⟨9951, by rfl⟩ (by norm_num))
theorem R59309 : Reach 59309 := rs (se 3 (by rfl) ⟨11120, by rfl⟩) (B 22241 (by norm_num) ⟨11120, by rfl⟩ (by norm_num))
theorem R26541 : Reach 26541 := rs (se 3 (by rfl) ⟨4976, by rfl⟩) (B 9953 (by norm_num) ⟨4976, by rfl⟩ (by norm_num))
theorem R26545 : Reach 26545 := rs (se 2 (by rfl) ⟨9954, by rfl⟩) (B 19909 (by norm_num) ⟨9954, by rfl⟩ (by norm_num))
theorem R26549 : Reach 26549 := rs (se 5 (by rfl) ⟨1244, by rfl⟩) (B 2489 (by norm_num) ⟨1244, by rfl⟩ (by norm_num))
theorem R26553 : Reach 26553 := rs (se 2 (by rfl) ⟨9957, by rfl⟩) (B 19915 (by norm_num) ⟨9957, by rfl⟩ (by norm_num))
theorem R26557 : Reach 26557 := rs (se 3 (by rfl) ⟨4979, by rfl⟩) (B 9959 (by norm_num) ⟨4979, by rfl⟩ (by norm_num))
theorem R26561 : Reach 26561 := rs (se 2 (by rfl) ⟨9960, by rfl⟩) (B 19921 (by norm_num) ⟨9960, by rfl⟩ (by norm_num))
theorem R26565 : Reach 26565 := rs (se 4 (by rfl) ⟨2490, by rfl⟩) (B 4981 (by norm_num) ⟨2490, by rfl⟩ (by norm_num))
theorem R26569 : Reach 26569 := rs (se 2 (by rfl) ⟨9963, by rfl⟩) (B 19927 (by norm_num) ⟨9963, by rfl⟩ (by norm_num))
theorem R26573 : Reach 26573 := rs (se 3 (by rfl) ⟨4982, by rfl⟩) (B 9965 (by norm_num) ⟨4982, by rfl⟩ (by norm_num))
theorem R26577 : Reach 26577 := rs (se 2 (by rfl) ⟨9966, by rfl⟩) (B 19933 (by norm_num) ⟨9966, by rfl⟩ (by norm_num))
theorem R26581 : Reach 26581 := rs (se 7 (by rfl) ⟨311, by rfl⟩) (B 623 (by norm_num) ⟨311, by rfl⟩ (by norm_num))
theorem R26585 : Reach 26585 := rs (se 2 (by rfl) ⟨9969, by rfl⟩) (B 19939 (by norm_num) ⟨9969, by rfl⟩ (by norm_num))
theorem R59357 : Reach 59357 := rs (se 3 (by rfl) ⟨11129, by rfl⟩) (B 22259 (by norm_num) ⟨11129, by rfl⟩ (by norm_num))
theorem R26589 : Reach 26589 := rs (se 3 (by rfl) ⟨4985, by rfl⟩) (B 9971 (by norm_num) ⟨4985, by rfl⟩ (by norm_num))
theorem R26593 : Reach 26593 := rs (se 2 (by rfl) ⟨9972, by rfl⟩) (B 19945 (by norm_num) ⟨9972, by rfl⟩ (by norm_num))
theorem R124901 : Reach 124901 := rs (se 4 (by rfl) ⟨11709, by rfl⟩) (B 23419 (by norm_num) ⟨11709, by rfl⟩ (by norm_num))
theorem R26597 : Reach 26597 := rs (se 4 (by rfl) ⟨2493, by rfl⟩) (B 4987 (by norm_num) ⟨2493, by rfl⟩ (by norm_num))
theorem R26601 : Reach 26601 := rs (se 2 (by rfl) ⟨9975, by rfl⟩) (B 19951 (by norm_num) ⟨9975, by rfl⟩ (by norm_num))
theorem R26605 : Reach 26605 := rs (se 3 (by rfl) ⟨4988, by rfl⟩) (B 9977 (by norm_num) ⟨4988, by rfl⟩ (by norm_num))
theorem R26609 : Reach 26609 := rs (se 2 (by rfl) ⟨9978, by rfl⟩) (B 19957 (by norm_num) ⟨9978, by rfl⟩ (by norm_num))
theorem R59381 : Reach 59381 := rs (se 5 (by rfl) ⟨2783, by rfl⟩) (B 5567 (by norm_num) ⟨2783, by rfl⟩ (by norm_num))
theorem R26613 : Reach 26613 := rs (se 5 (by rfl) ⟨1247, by rfl⟩) (B 2495 (by norm_num) ⟨1247, by rfl⟩ (by norm_num))
theorem R26617 : Reach 26617 := rs (se 2 (by rfl) ⟨9981, by rfl⟩) (B 19963 (by norm_num) ⟨9981, by rfl⟩ (by norm_num))
theorem R26621 : Reach 26621 := rs (se 3 (by rfl) ⟨4991, by rfl⟩) (B 9983 (by norm_num) ⟨4991, by rfl⟩ (by norm_num))
theorem R26625 : Reach 26625 := rs (se 2 (by rfl) ⟨9984, by rfl⟩) (B 19969 (by norm_num) ⟨9984, by rfl⟩ (by norm_num))
theorem R26629 : Reach 26629 := rs (se 4 (by rfl) ⟨2496, by rfl⟩) (B 4993 (by norm_num) ⟨2496, by rfl⟩ (by norm_num))
theorem R26633 : Reach 26633 := rs (se 2 (by rfl) ⟨9987, by rfl⟩) (B 19975 (by norm_num) ⟨9987, by rfl⟩ (by norm_num))
theorem R26637 : Reach 26637 := rs (se 3 (by rfl) ⟨4994, by rfl⟩) (B 9989 (by norm_num) ⟨4994, by rfl⟩ (by norm_num))
theorem R26641 : Reach 26641 := rs (se 2 (by rfl) ⟨9990, by rfl⟩) (B 19981 (by norm_num) ⟨9990, by rfl⟩ (by norm_num))
theorem R26645 : Reach 26645 := rs (se 6 (by rfl) ⟨624, by rfl⟩) (B 1249 (by norm_num) ⟨624, by rfl⟩ (by norm_num))
theorem R26649 : Reach 26649 := rs (se 2 (by rfl) ⟨9993, by rfl⟩) (B 19987 (by norm_num) ⟨9993, by rfl⟩ (by norm_num))
theorem R26653 : Reach 26653 := rs (se 3 (by rfl) ⟨4997, by rfl⟩) (B 9995 (by norm_num) ⟨4997, by rfl⟩ (by norm_num))
theorem R26657 : Reach 26657 := rs (se 2 (by rfl) ⟨9996, by rfl⟩) (B 19993 (by norm_num) ⟨9996, by rfl⟩ (by norm_num))
theorem R26661 : Reach 26661 := rs (se 4 (by rfl) ⟨2499, by rfl⟩) (B 4999 (by norm_num) ⟨2499, by rfl⟩ (by norm_num))
theorem R26665 : Reach 26665 := rs (se 2 (by rfl) ⟨9999, by rfl⟩) (B 19999 (by norm_num) ⟨9999, by rfl⟩ (by norm_num))
theorem R26669 : Reach 26669 := rs (se 3 (by rfl) ⟨5000, by rfl⟩) (B 10001 (by norm_num) ⟨5000, by rfl⟩ (by norm_num))
theorem R26673 : Reach 26673 := rs (se 2 (by rfl) ⟨10002, by rfl⟩) (B 20005 (by norm_num) ⟨10002, by rfl⟩ (by norm_num))
theorem R26677 : Reach 26677 := rs (se 5 (by rfl) ⟨1250, by rfl⟩) (B 2501 (by norm_num) ⟨1250, by rfl⟩ (by norm_num))
theorem R26681 : Reach 26681 := rs (se 2 (by rfl) ⟨10005, by rfl⟩) (B 20011 (by norm_num) ⟨10005, by rfl⟩ (by norm_num))
theorem R59453 : Reach 59453 := rs (se 3 (by rfl) ⟨11147, by rfl⟩) (B 22295 (by norm_num) ⟨11147, by rfl⟩ (by norm_num))
theorem R26685 : Reach 26685 := rs (se 3 (by rfl) ⟨5003, by rfl⟩) (B 10007 (by norm_num) ⟨5003, by rfl⟩ (by norm_num))
theorem R26689 : Reach 26689 := rs (se 2 (by rfl) ⟨10008, by rfl⟩) (B 20017 (by norm_num) ⟨10008, by rfl⟩ (by norm_num))
theorem R26693 : Reach 26693 := rs (se 4 (by rfl) ⟨2502, by rfl⟩) (B 5005 (by norm_num) ⟨2502, by rfl⟩ (by norm_num))
theorem R26697 : Reach 26697 := rs (se 2 (by rfl) ⟨10011, by rfl⟩) (B 20023 (by norm_num) ⟨10011, by rfl⟩ (by norm_num))
theorem R26701 : Reach 26701 := rs (se 3 (by rfl) ⟨5006, by rfl⟩) (B 10013 (by norm_num) ⟨5006, by rfl⟩ (by norm_num))
theorem R26705 : Reach 26705 := rs (se 2 (by rfl) ⟨10014, by rfl⟩) (B 20029 (by norm_num) ⟨10014, by rfl⟩ (by norm_num))
theorem R26709 : Reach 26709 := rs (se 8 (by rfl) ⟨156, by rfl⟩) (B 313 (by norm_num) ⟨156, by rfl⟩ (by norm_num))
theorem R26713 : Reach 26713 := rs (se 2 (by rfl) ⟨10017, by rfl⟩) (B 20035 (by norm_num) ⟨10017, by rfl⟩ (by norm_num))
theorem R26717 : Reach 26717 := rs (se 3 (by rfl) ⟨5009, by rfl⟩) (B 10019 (by norm_num) ⟨5009, by rfl⟩ (by norm_num))
theorem R26721 : Reach 26721 := rs (se 2 (by rfl) ⟨10020, by rfl⟩) (B 20041 (by norm_num) ⟨10020, by rfl⟩ (by norm_num))
theorem R26725 : Reach 26725 := rs (se 4 (by rfl) ⟨2505, by rfl⟩) (B 5011 (by norm_num) ⟨2505, by rfl⟩ (by norm_num))
theorem R26729 : Reach 26729 := rs (se 2 (by rfl) ⟨10023, by rfl⟩) (B 20047 (by norm_num) ⟨10023, by rfl⟩ (by norm_num))
theorem R26733 : Reach 26733 := rs (se 3 (by rfl) ⟨5012, by rfl⟩) (B 10025 (by norm_num) ⟨5012, by rfl⟩ (by norm_num))
theorem R26737 : Reach 26737 := rs (se 2 (by rfl) ⟨10026, by rfl⟩) (B 20053 (by norm_num) ⟨10026, by rfl⟩ (by norm_num))
theorem R26741 : Reach 26741 := rs (se 5 (by rfl) ⟨1253, by rfl⟩) (B 2507 (by norm_num) ⟨1253, by rfl⟩ (by norm_num))
theorem R26745 : Reach 26745 := rs (se 2 (by rfl) ⟨10029, by rfl⟩) (B 20059 (by norm_num) ⟨10029, by rfl⟩ (by norm_num))
theorem R26749 : Reach 26749 := rs (se 3 (by rfl) ⟨5015, by rfl⟩) (B 10031 (by norm_num) ⟨5015, by rfl⟩ (by norm_num))
theorem R26753 : Reach 26753 := rs (se 2 (by rfl) ⟨10032, by rfl⟩) (B 20065 (by norm_num) ⟨10032, by rfl⟩ (by norm_num))
theorem R59525 : Reach 59525 := rs (se 4 (by rfl) ⟨5580, by rfl⟩) (B 11161 (by norm_num) ⟨5580, by rfl⟩ (by norm_num))
theorem R26757 : Reach 26757 := rs (se 4 (by rfl) ⟨2508, by rfl⟩) (B 5017 (by norm_num) ⟨2508, by rfl⟩ (by norm_num))
theorem R26761 : Reach 26761 := rs (se 2 (by rfl) ⟨10035, by rfl⟩) (B 20071 (by norm_num) ⟨10035, by rfl⟩ (by norm_num))
theorem R26765 : Reach 26765 := rs (se 3 (by rfl) ⟨5018, by rfl⟩) (B 10037 (by norm_num) ⟨5018, by rfl⟩ (by norm_num))
theorem R26769 : Reach 26769 := rs (se 2 (by rfl) ⟨10038, by rfl⟩) (B 20077 (by norm_num) ⟨10038, by rfl⟩ (by norm_num))
theorem R26773 : Reach 26773 := rs (se 6 (by rfl) ⟨627, by rfl⟩) (B 1255 (by norm_num) ⟨627, by rfl⟩ (by norm_num))
theorem R26777 : Reach 26777 := rs (se 2 (by rfl) ⟨10041, by rfl⟩) (B 20083 (by norm_num) ⟨10041, by rfl⟩ (by norm_num))
theorem R59549 : Reach 59549 := rs (se 3 (by rfl) ⟨11165, by rfl⟩) (B 22331 (by norm_num) ⟨11165, by rfl⟩ (by norm_num))
theorem R26781 : Reach 26781 := rs (se 3 (by rfl) ⟨5021, by rfl⟩) (B 10043 (by norm_num) ⟨5021, by rfl⟩ (by norm_num))
theorem R26785 : Reach 26785 := rs (se 2 (by rfl) ⟨10044, by rfl⟩) (B 20089 (by norm_num) ⟨10044, by rfl⟩ (by norm_num))
theorem R26789 : Reach 26789 := rs (se 4 (by rfl) ⟨2511, by rfl⟩) (B 5023 (by norm_num) ⟨2511, by rfl⟩ (by norm_num))
theorem R26793 : Reach 26793 := rs (se 2 (by rfl) ⟨10047, by rfl⟩) (B 20095 (by norm_num) ⟨10047, by rfl⟩ (by norm_num))
theorem R26797 : Reach 26797 := rs (se 3 (by rfl) ⟨5024, by rfl⟩) (B 10049 (by norm_num) ⟨5024, by rfl⟩ (by norm_num))
theorem R26801 : Reach 26801 := rs (se 2 (by rfl) ⟨10050, by rfl⟩) (B 20101 (by norm_num) ⟨10050, by rfl⟩ (by norm_num))
theorem R26805 : Reach 26805 := rs (se 5 (by rfl) ⟨1256, by rfl⟩) (B 2513 (by norm_num) ⟨1256, by rfl⟩ (by norm_num))
theorem R26809 : Reach 26809 := rs (se 2 (by rfl) ⟨10053, by rfl⟩) (B 20107 (by norm_num) ⟨10053, by rfl⟩ (by norm_num))
theorem R26813 : Reach 26813 := rs (se 3 (by rfl) ⟨5027, by rfl⟩) (B 10055 (by norm_num) ⟨5027, by rfl⟩ (by norm_num))
theorem R26817 : Reach 26817 := rs (se 2 (by rfl) ⟨10056, by rfl⟩) (B 20113 (by norm_num) ⟨10056, by rfl⟩ (by norm_num))
theorem R26821 : Reach 26821 := rs (se 4 (by rfl) ⟨2514, by rfl⟩) (B 5029 (by norm_num) ⟨2514, by rfl⟩ (by norm_num))
theorem R26825 : Reach 26825 := rs (se 2 (by rfl) ⟨10059, by rfl⟩) (B 20119 (by norm_num) ⟨10059, by rfl⟩ (by norm_num))
theorem R59597 : Reach 59597 := rs (se 3 (by rfl) ⟨11174, by rfl⟩) (B 22349 (by norm_num) ⟨11174, by rfl⟩ (by norm_num))
theorem R26829 : Reach 26829 := rs (se 3 (by rfl) ⟨5030, by rfl⟩) (B 10061 (by norm_num) ⟨5030, by rfl⟩ (by norm_num))
theorem R26833 : Reach 26833 := rs (se 2 (by rfl) ⟨10062, by rfl⟩) (B 20125 (by norm_num) ⟨10062, by rfl⟩ (by norm_num))
theorem R26837 : Reach 26837 := rs (se 7 (by rfl) ⟨314, by rfl⟩) (B 629 (by norm_num) ⟨314, by rfl⟩ (by norm_num))
theorem R26841 : Reach 26841 := rs (se 2 (by rfl) ⟨10065, by rfl⟩) (B 20131 (by norm_num) ⟨10065, by rfl⟩ (by norm_num))
theorem R26845 : Reach 26845 := rs (se 3 (by rfl) ⟨5033, by rfl⟩) (B 10067 (by norm_num) ⟨5033, by rfl⟩ (by norm_num))
theorem R26849 : Reach 26849 := rs (se 2 (by rfl) ⟨10068, by rfl⟩) (B 20137 (by norm_num) ⟨10068, by rfl⟩ (by norm_num))
theorem R26853 : Reach 26853 := rs (se 4 (by rfl) ⟨2517, by rfl⟩) (B 5035 (by norm_num) ⟨2517, by rfl⟩ (by norm_num))
theorem R26857 : Reach 26857 := rs (se 2 (by rfl) ⟨10071, by rfl⟩) (B 20143 (by norm_num) ⟨10071, by rfl⟩ (by norm_num))
theorem R26861 : Reach 26861 := rs (se 3 (by rfl) ⟨5036, by rfl⟩) (B 10073 (by norm_num) ⟨5036, by rfl⟩ (by norm_num))
theorem R26865 : Reach 26865 := rs (se 2 (by rfl) ⟨10074, by rfl⟩) (B 20149 (by norm_num) ⟨10074, by rfl⟩ (by norm_num))
theorem R26869 : Reach 26869 := rs (se 5 (by rfl) ⟨1259, by rfl⟩) (B 2519 (by norm_num) ⟨1259, by rfl⟩ (by norm_num))
theorem R26873 : Reach 26873 := rs (se 2 (by rfl) ⟨10077, by rfl⟩) (B 20155 (by norm_num) ⟨10077, by rfl⟩ (by norm_num))
theorem R26877 : Reach 26877 := rs (se 3 (by rfl) ⟨5039, by rfl⟩) (B 10079 (by norm_num) ⟨5039, by rfl⟩ (by norm_num))
theorem R26881 : Reach 26881 := rs (se 2 (by rfl) ⟨10080, by rfl⟩) (B 20161 (by norm_num) ⟨10080, by rfl⟩ (by norm_num))
theorem R26885 : Reach 26885 := rs (se 4 (by rfl) ⟨2520, by rfl⟩) (B 5041 (by norm_num) ⟨2520, by rfl⟩ (by norm_num))
theorem R26889 : Reach 26889 := rs (se 2 (by rfl) ⟨10083, by rfl⟩) (B 20167 (by norm_num) ⟨10083, by rfl⟩ (by norm_num))
theorem R26893 : Reach 26893 := rs (se 3 (by rfl) ⟨5042, by rfl⟩) (B 10085 (by norm_num) ⟨5042, by rfl⟩ (by norm_num))
theorem R26897 : Reach 26897 := rs (se 2 (by rfl) ⟨10086, by rfl⟩) (B 20173 (by norm_num) ⟨10086, by rfl⟩ (by norm_num))
theorem R59669 : Reach 59669 := rs (se 6 (by rfl) ⟨1398, by rfl⟩) (B 2797 (by norm_num) ⟨1398, by rfl⟩ (by norm_num))
theorem R26901 : Reach 26901 := rs (se 6 (by rfl) ⟨630, by rfl⟩) (B 1261 (by norm_num) ⟨630, by rfl⟩ (by norm_num))
theorem R26905 : Reach 26905 := rs (se 2 (by rfl) ⟨10089, by rfl⟩) (B 20179 (by norm_num) ⟨10089, by rfl⟩ (by norm_num))
theorem R26909 : Reach 26909 := rs (se 3 (by rfl) ⟨5045, by rfl⟩) (B 10091 (by norm_num) ⟨5045, by rfl⟩ (by norm_num))
theorem R26913 : Reach 26913 := rs (se 2 (by rfl) ⟨10092, by rfl⟩) (B 20185 (by norm_num) ⟨10092, by rfl⟩ (by norm_num))
theorem R26917 : Reach 26917 := rs (se 4 (by rfl) ⟨2523, by rfl⟩) (B 5047 (by norm_num) ⟨2523, by rfl⟩ (by norm_num))
theorem R26921 : Reach 26921 := rs (se 2 (by rfl) ⟨10095, by rfl⟩) (B 20191 (by norm_num) ⟨10095, by rfl⟩ (by norm_num))
theorem R26925 : Reach 26925 := rs (se 3 (by rfl) ⟨5048, by rfl⟩) (B 10097 (by norm_num) ⟨5048, by rfl⟩ (by norm_num))
theorem R26929 : Reach 26929 := rs (se 2 (by rfl) ⟨10098, by rfl⟩) (B 20197 (by norm_num) ⟨10098, by rfl⟩ (by norm_num))
theorem R26933 : Reach 26933 := rs (se 5 (by rfl) ⟨1262, by rfl⟩) (B 2525 (by norm_num) ⟨1262, by rfl⟩ (by norm_num))
theorem R26937 : Reach 26937 := rs (se 2 (by rfl) ⟨10101, by rfl⟩) (B 20203 (by norm_num) ⟨10101, by rfl⟩ (by norm_num))
theorem R26941 : Reach 26941 := rs (se 3 (by rfl) ⟨5051, by rfl⟩) (B 10103 (by norm_num) ⟨5051, by rfl⟩ (by norm_num))
theorem R26945 : Reach 26945 := rs (se 2 (by rfl) ⟨10104, by rfl⟩) (B 20209 (by norm_num) ⟨10104, by rfl⟩ (by norm_num))
theorem R59717 : Reach 59717 := rs (se 4 (by rfl) ⟨5598, by rfl⟩) (B 11197 (by norm_num) ⟨5598, by rfl⟩ (by norm_num))
theorem R26949 : Reach 26949 := rs (se 4 (by rfl) ⟨2526, by rfl⟩) (B 5053 (by norm_num) ⟨2526, by rfl⟩ (by norm_num))
theorem R26953 : Reach 26953 := rs (se 2 (by rfl) ⟨10107, by rfl⟩) (B 20215 (by norm_num) ⟨10107, by rfl⟩ (by norm_num))
theorem R26957 : Reach 26957 := rs (se 3 (by rfl) ⟨5054, by rfl⟩) (B 10109 (by norm_num) ⟨5054, by rfl⟩ (by norm_num))
theorem R26961 : Reach 26961 := rs (se 2 (by rfl) ⟨10110, by rfl⟩) (B 20221 (by norm_num) ⟨10110, by rfl⟩ (by norm_num))
theorem R26965 : Reach 26965 := rs (se 10 (by rfl) ⟨39, by rfl⟩) (B 79 (by norm_num) ⟨39, by rfl⟩ (by norm_num))
theorem R26969 : Reach 26969 := rs (se 2 (by rfl) ⟨10113, by rfl⟩) (B 20227 (by norm_num) ⟨10113, by rfl⟩ (by norm_num))
theorem R59741 : Reach 59741 := rs (se 3 (by rfl) ⟨11201, by rfl⟩) (B 22403 (by norm_num) ⟨11201, by rfl⟩ (by norm_num))
theorem R26973 : Reach 26973 := rs (se 3 (by rfl) ⟨5057, by rfl⟩) (B 10115 (by norm_num) ⟨5057, by rfl⟩ (by norm_num))
theorem R26977 : Reach 26977 := rs (se 2 (by rfl) ⟨10116, by rfl⟩) (B 20233 (by norm_num) ⟨10116, by rfl⟩ (by norm_num))
theorem R26981 : Reach 26981 := rs (se 4 (by rfl) ⟨2529, by rfl⟩) (B 5059 (by norm_num) ⟨2529, by rfl⟩ (by norm_num))
theorem R26985 : Reach 26985 := rs (se 2 (by rfl) ⟨10119, by rfl⟩) (B 20239 (by norm_num) ⟨10119, by rfl⟩ (by norm_num))
theorem R26989 : Reach 26989 := rs (se 3 (by rfl) ⟨5060, by rfl⟩) (B 10121 (by norm_num) ⟨5060, by rfl⟩ (by norm_num))
theorem R26993 : Reach 26993 := rs (se 2 (by rfl) ⟨10122, by rfl⟩) (B 20245 (by norm_num) ⟨10122, by rfl⟩ (by norm_num))
theorem R26997 : Reach 26997 := rs (se 5 (by rfl) ⟨1265, by rfl⟩) (B 2531 (by norm_num) ⟨1265, by rfl⟩ (by norm_num))
theorem R27001 : Reach 27001 := rs (se 2 (by rfl) ⟨10125, by rfl⟩) (B 20251 (by norm_num) ⟨10125, by rfl⟩ (by norm_num))
theorem R27005 : Reach 27005 := rs (se 3 (by rfl) ⟨5063, by rfl⟩) (B 10127 (by norm_num) ⟨5063, by rfl⟩ (by norm_num))
theorem R27009 : Reach 27009 := rs (se 2 (by rfl) ⟨10128, by rfl⟩) (B 20257 (by norm_num) ⟨10128, by rfl⟩ (by norm_num))
theorem R27013 : Reach 27013 := rs (se 4 (by rfl) ⟨2532, by rfl⟩) (B 5065 (by norm_num) ⟨2532, by rfl⟩ (by norm_num))
theorem R27017 : Reach 27017 := rs (se 2 (by rfl) ⟨10131, by rfl⟩) (B 20263 (by norm_num) ⟨10131, by rfl⟩ (by norm_num))
theorem R27021 : Reach 27021 := rs (se 3 (by rfl) ⟨5066, by rfl⟩) (B 10133 (by norm_num) ⟨5066, by rfl⟩ (by norm_num))
theorem R27025 : Reach 27025 := rs (se 2 (by rfl) ⟨10134, by rfl⟩) (B 20269 (by norm_num) ⟨10134, by rfl⟩ (by norm_num))
theorem R27029 : Reach 27029 := rs (se 6 (by rfl) ⟨633, by rfl⟩) (B 1267 (by norm_num) ⟨633, by rfl⟩ (by norm_num))
theorem R27033 : Reach 27033 := rs (se 2 (by rfl) ⟨10137, by rfl⟩) (B 20275 (by norm_num) ⟨10137, by rfl⟩ (by norm_num))
theorem R27037 : Reach 27037 := rs (se 3 (by rfl) ⟨5069, by rfl⟩) (B 10139 (by norm_num) ⟨5069, by rfl⟩ (by norm_num))
theorem R27041 : Reach 27041 := rs (se 2 (by rfl) ⟨10140, by rfl⟩) (B 20281 (by norm_num) ⟨10140, by rfl⟩ (by norm_num))
theorem R59813 : Reach 59813 := rs (se 4 (by rfl) ⟨5607, by rfl⟩) (B 11215 (by norm_num) ⟨5607, by rfl⟩ (by norm_num))
theorem R27045 : Reach 27045 := rs (se 4 (by rfl) ⟨2535, by rfl⟩) (B 5071 (by norm_num) ⟨2535, by rfl⟩ (by norm_num))
theorem R27049 : Reach 27049 := rs (se 2 (by rfl) ⟨10143, by rfl⟩) (B 20287 (by norm_num) ⟨10143, by rfl⟩ (by norm_num))
theorem R27053 : Reach 27053 := rs (se 3 (by rfl) ⟨5072, by rfl⟩) (B 10145 (by norm_num) ⟨5072, by rfl⟩ (by norm_num))
theorem R27057 : Reach 27057 := rs (se 2 (by rfl) ⟨10146, by rfl⟩) (B 20293 (by norm_num) ⟨10146, by rfl⟩ (by norm_num))
theorem R27061 : Reach 27061 := rs (se 5 (by rfl) ⟨1268, by rfl⟩) (B 2537 (by norm_num) ⟨1268, by rfl⟩ (by norm_num))
theorem R27065 : Reach 27065 := rs (se 2 (by rfl) ⟨10149, by rfl⟩) (B 20299 (by norm_num) ⟨10149, by rfl⟩ (by norm_num))
theorem R27069 : Reach 27069 := rs (se 3 (by rfl) ⟨5075, by rfl⟩) (B 10151 (by norm_num) ⟨5075, by rfl⟩ (by norm_num))
theorem R27073 : Reach 27073 := rs (se 2 (by rfl) ⟨10152, by rfl⟩) (B 20305 (by norm_num) ⟨10152, by rfl⟩ (by norm_num))
theorem R27077 : Reach 27077 := rs (se 4 (by rfl) ⟨2538, by rfl⟩) (B 5077 (by norm_num) ⟨2538, by rfl⟩ (by norm_num))
theorem R27081 : Reach 27081 := rs (se 2 (by rfl) ⟨10155, by rfl⟩) (B 20311 (by norm_num) ⟨10155, by rfl⟩ (by norm_num))
theorem R27085 : Reach 27085 := rs (se 3 (by rfl) ⟨5078, by rfl⟩) (B 10157 (by norm_num) ⟨5078, by rfl⟩ (by norm_num))
theorem R27089 : Reach 27089 := rs (se 2 (by rfl) ⟨10158, by rfl⟩) (B 20317 (by norm_num) ⟨10158, by rfl⟩ (by norm_num))
theorem R27093 : Reach 27093 := rs (se 7 (by rfl) ⟨317, by rfl⟩) (B 635 (by norm_num) ⟨317, by rfl⟩ (by norm_num))
theorem R27097 : Reach 27097 := rs (se 2 (by rfl) ⟨10161, by rfl⟩) (B 20323 (by norm_num) ⟨10161, by rfl⟩ (by norm_num))
theorem R27101 : Reach 27101 := rs (se 3 (by rfl) ⟨5081, by rfl⟩) (B 10163 (by norm_num) ⟨5081, by rfl⟩ (by norm_num))
theorem R27105 : Reach 27105 := rs (se 2 (by rfl) ⟨10164, by rfl⟩) (B 20329 (by norm_num) ⟨10164, by rfl⟩ (by norm_num))
theorem R27109 : Reach 27109 := rs (se 4 (by rfl) ⟨2541, by rfl⟩) (B 5083 (by norm_num) ⟨2541, by rfl⟩ (by norm_num))
theorem R27113 : Reach 27113 := rs (se 2 (by rfl) ⟨10167, by rfl⟩) (B 20335 (by norm_num) ⟨10167, by rfl⟩ (by norm_num))
theorem R59885 : Reach 59885 := rs (se 3 (by rfl) ⟨11228, by rfl⟩) (B 22457 (by norm_num) ⟨11228, by rfl⟩ (by norm_num))
theorem R27121 : Reach 27121 := rs (se 2 (by rfl) ⟨10170, by rfl⟩) (B 20341 (by norm_num) ⟨10170, by rfl⟩ (by norm_num))
theorem R27157 : Reach 27157 := rs (se 6 (by rfl) ⟨636, by rfl⟩) (B 1273 (by norm_num) ⟨636, by rfl⟩ (by norm_num))
theorem R190997 : Reach 190997 := rs (se 6 (by rfl) ⟨4476, by rfl⟩) (B 8953 (by norm_num) ⟨4476, by rfl⟩ (by norm_num))
theorem R59957 : Reach 59957 := rs (se 5 (by rfl) ⟨2810, by rfl⟩) (B 5621 (by norm_num) ⟨2810, by rfl⟩ (by norm_num))
theorem R27193 : Reach 27193 := rs (se 2 (by rfl) ⟨10197, by rfl⟩) (B 20395 (by norm_num) ⟨10197, by rfl⟩ (by norm_num))
theorem R27229 : Reach 27229 := rs (se 3 (by rfl) ⟨5105, by rfl⟩) (B 10211 (by norm_num) ⟨5105, by rfl⟩ (by norm_num))
theorem R60029 : Reach 60029 := rs (se 3 (by rfl) ⟨11255, by rfl⟩) (B 22511 (by norm_num) ⟨11255, by rfl⟩ (by norm_num))
theorem R27265 : Reach 27265 := rs (se 2 (by rfl) ⟨10224, by rfl⟩) (B 20449 (by norm_num) ⟨10224, by rfl⟩ (by norm_num))
theorem R60061 : Reach 60061 := rs (se 3 (by rfl) ⟨11261, by rfl⟩) (B 22523 (by norm_num) ⟨11261, by rfl⟩ (by norm_num))
theorem R27301 : Reach 27301 := rs (se 4 (by rfl) ⟨2559, by rfl⟩) (B 5119 (by norm_num) ⟨2559, by rfl⟩ (by norm_num))
theorem R60101 : Reach 60101 := rs (se 4 (by rfl) ⟨5634, by rfl⟩) (B 11269 (by norm_num) ⟨5634, by rfl⟩ (by norm_num))
theorem R27337 : Reach 27337 := rs (se 2 (by rfl) ⟨10251, by rfl⟩) (B 20503 (by norm_num) ⟨10251, by rfl⟩ (by norm_num))
theorem R27373 : Reach 27373 := rs (se 3 (by rfl) ⟨5132, by rfl⟩) (B 10265 (by norm_num) ⟨5132, by rfl⟩ (by norm_num))
theorem R27389 : Reach 27389 := rs (se 3 (by rfl) ⟨5135, by rfl⟩) (B 10271 (by norm_num) ⟨5135, by rfl⟩ (by norm_num))
theorem R92933 : Reach 92933 := rs (se 4 (by rfl) ⟨8712, by rfl⟩) (B 17425 (by norm_num) ⟨8712, by rfl⟩ (by norm_num))
theorem R60173 : Reach 60173 := rs (se 3 (by rfl) ⟨11282, by rfl⟩) (B 22565 (by norm_num) ⟨11282, by rfl⟩ (by norm_num))
theorem R27409 : Reach 27409 := rs (se 2 (by rfl) ⟨10278, by rfl⟩) (B 20557 (by norm_num) ⟨10278, by rfl⟩ (by norm_num))
theorem R27445 : Reach 27445 := rs (se 5 (by rfl) ⟨1286, by rfl⟩) (B 2573 (by norm_num) ⟨1286, by rfl⟩ (by norm_num))
theorem R60245 : Reach 60245 := rs (se 9 (by rfl) ⟨176, by rfl⟩) (B 353 (by norm_num) ⟨176, by rfl⟩ (by norm_num))
theorem R27481 : Reach 27481 := rs (se 2 (by rfl) ⟨10305, by rfl⟩) (B 20611 (by norm_num) ⟨10305, by rfl⟩ (by norm_num))
theorem R27497 : Reach 27497 := rs (se 2 (by rfl) ⟨10311, by rfl⟩) (B 20623 (by norm_num) ⟨10311, by rfl⟩ (by norm_num))
theorem R27517 : Reach 27517 := rs (se 3 (by rfl) ⟨5159, by rfl⟩) (B 10319 (by norm_num) ⟨5159, by rfl⟩ (by norm_num))
theorem R60317 : Reach 60317 := rs (se 3 (by rfl) ⟨11309, by rfl⟩) (B 22619 (by norm_num) ⟨11309, by rfl⟩ (by norm_num))
theorem R27553 : Reach 27553 := rs (se 2 (by rfl) ⟨10332, by rfl⟩) (B 20665 (by norm_num) ⟨10332, by rfl⟩ (by norm_num))
theorem R93109 : Reach 93109 := rs (se 5 (by rfl) ⟨4364, by rfl⟩) (B 8729 (by norm_num) ⟨4364, by rfl⟩ (by norm_num))
theorem R27577 : Reach 27577 := rs (se 2 (by rfl) ⟨10341, by rfl⟩) (B 20683 (by norm_num) ⟨10341, by rfl⟩ (by norm_num))
theorem R27589 : Reach 27589 := rs (se 4 (by rfl) ⟨2586, by rfl⟩) (B 5173 (by norm_num) ⟨2586, by rfl⟩ (by norm_num))
theorem R60365 : Reach 60365 := rs (se 3 (by rfl) ⟨11318, by rfl⟩) (B 22637 (by norm_num) ⟨11318, by rfl⟩ (by norm_num))
theorem R60389 : Reach 60389 := rs (se 4 (by rfl) ⟨5661, by rfl⟩) (B 11323 (by norm_num) ⟨5661, by rfl⟩ (by norm_num))
theorem R27625 : Reach 27625 := rs (se 2 (by rfl) ⟨10359, by rfl⟩) (B 20719 (by norm_num) ⟨10359, by rfl⟩ (by norm_num))
theorem R27661 : Reach 27661 := rs (se 3 (by rfl) ⟨5186, by rfl⟩) (B 10373 (by norm_num) ⟨5186, by rfl⟩ (by norm_num))
theorem R93221 : Reach 93221 := rs (se 4 (by rfl) ⟨8739, by rfl⟩) (B 17479 (by norm_num) ⟨8739, by rfl⟩ (by norm_num))
theorem R60461 : Reach 60461 := rs (se 3 (by rfl) ⟨11336, by rfl⟩) (B 22673 (by norm_num) ⟨11336, by rfl⟩ (by norm_num))
theorem R27697 : Reach 27697 := rs (se 2 (by rfl) ⟨10386, by rfl⟩) (B 20773 (by norm_num) ⟨10386, by rfl⟩ (by norm_num))
theorem R27733 : Reach 27733 := rs (se 8 (by rfl) ⟨162, by rfl⟩) (B 325 (by norm_num) ⟨162, by rfl⟩ (by norm_num))
theorem R60533 : Reach 60533 := rs (se 5 (by rfl) ⟨2837, by rfl⟩) (B 5675 (by norm_num) ⟨2837, by rfl⟩ (by norm_num))
theorem R27769 : Reach 27769 := rs (se 2 (by rfl) ⟨10413, by rfl⟩) (B 20827 (by norm_num) ⟨10413, by rfl⟩ (by norm_num))
theorem R27805 : Reach 27805 := rs (se 3 (by rfl) ⟨5213, by rfl⟩) (B 10427 (by norm_num) ⟨5213, by rfl⟩ (by norm_num))
theorem R60605 : Reach 60605 := rs (se 3 (by rfl) ⟨11363, by rfl⟩) (B 22727 (by norm_num) ⟨11363, by rfl⟩ (by norm_num))
theorem R27841 : Reach 27841 := rs (se 2 (by rfl) ⟨10440, by rfl⟩) (B 20881 (by norm_num) ⟨10440, by rfl⟩ (by norm_num))
theorem R27877 : Reach 27877 := rs (se 4 (by rfl) ⟨2613, by rfl⟩) (B 5227 (by norm_num) ⟨2613, by rfl⟩ (by norm_num))
theorem R126197 : Reach 126197 := rs (se 5 (by rfl) ⟨5915, by rfl⟩) (B 11831 (by norm_num) ⟨5915, by rfl⟩ (by norm_num))
theorem R60677 : Reach 60677 := rs (se 4 (by rfl) ⟨5688, by rfl⟩) (B 11377 (by norm_num) ⟨5688, by rfl⟩ (by norm_num))
theorem R27913 : Reach 27913 := rs (se 2 (by rfl) ⟨10467, by rfl⟩) (B 20935 (by norm_num) ⟨10467, by rfl⟩ (by norm_num))
theorem R60709 : Reach 60709 := rs (se 4 (by rfl) ⟨5691, by rfl⟩) (B 11383 (by norm_num) ⟨5691, by rfl⟩ (by norm_num))
theorem R27949 : Reach 27949 := rs (se 3 (by rfl) ⟨5240, by rfl⟩) (B 10481 (by norm_num) ⟨5240, by rfl⟩ (by norm_num))
theorem R60749 : Reach 60749 := rs (se 3 (by rfl) ⟨11390, by rfl⟩) (B 22781 (by norm_num) ⟨11390, by rfl⟩ (by norm_num))
theorem R27985 : Reach 27985 := rs (se 2 (by rfl) ⟨10494, by rfl⟩) (B 20989 (by norm_num) ⟨10494, by rfl⟩ (by norm_num))
theorem R28021 : Reach 28021 := rs (se 5 (by rfl) ⟨1313, by rfl⟩) (B 2627 (by norm_num) ⟨1313, by rfl⟩ (by norm_num))
theorem R60821 : Reach 60821 := rs (se 6 (by rfl) ⟨1425, by rfl⟩) (B 2851 (by norm_num) ⟨1425, by rfl⟩ (by norm_num))
theorem R28057 : Reach 28057 := rs (se 2 (by rfl) ⟨10521, by rfl⟩) (B 21043 (by norm_num) ⟨10521, by rfl⟩ (by norm_num))
theorem R28081 : Reach 28081 := rs (se 2 (by rfl) ⟨10530, by rfl⟩) (B 21061 (by norm_num) ⟨10530, by rfl⟩ (by norm_num))
theorem R28093 : Reach 28093 := rs (se 3 (by rfl) ⟨5267, by rfl⟩) (B 10535 (by norm_num) ⟨5267, by rfl⟩ (by norm_num))
theorem R60869 : Reach 60869 := rs (se 4 (by rfl) ⟨5706, by rfl⟩) (B 11413 (by norm_num) ⟨5706, by rfl⟩ (by norm_num))
theorem R60893 : Reach 60893 := rs (se 3 (by rfl) ⟨11417, by rfl⟩) (B 22835 (by norm_num) ⟨11417, by rfl⟩ (by norm_num))
theorem R28129 : Reach 28129 := rs (se 2 (by rfl) ⟨10548, by rfl⟩) (B 21097 (by norm_num) ⟨10548, by rfl⟩ (by norm_num))
theorem R28165 : Reach 28165 := rs (se 4 (by rfl) ⟨2640, by rfl⟩) (B 5281 (by norm_num) ⟨2640, by rfl⟩ (by norm_num))
theorem R60965 : Reach 60965 := rs (se 4 (by rfl) ⟨5715, by rfl⟩) (B 11431 (by norm_num) ⟨5715, by rfl⟩ (by norm_num))
theorem R28201 : Reach 28201 := rs (se 2 (by rfl) ⟨10575, by rfl⟩) (B 21151 (by norm_num) ⟨10575, by rfl⟩ (by norm_num))
theorem R28237 : Reach 28237 := rs (se 3 (by rfl) ⟨5294, by rfl⟩) (B 10589 (by norm_num) ⟨5294, by rfl⟩ (by norm_num))
theorem R61013 : Reach 61013 := rs (se 8 (by rfl) ⟨357, by rfl⟩) (B 715 (by norm_num) ⟨357, by rfl⟩ (by norm_num))
theorem R28273 : Reach 28273 := rs (se 2 (by rfl) ⟨10602, by rfl⟩) (B 21205 (by norm_num) ⟨10602, by rfl⟩ (by norm_num))
theorem R61069 : Reach 61069 := rs (se 3 (by rfl) ⟨11450, by rfl⟩) (B 22901 (by norm_num) ⟨11450, by rfl⟩ (by norm_num))
theorem R28309 : Reach 28309 := rs (se 6 (by rfl) ⟨663, by rfl⟩) (B 1327 (by norm_num) ⟨663, by rfl⟩ (by norm_num))
theorem R28333 : Reach 28333 := rs (se 3 (by rfl) ⟨5312, by rfl⟩) (B 10625 (by norm_num) ⟨5312, by rfl⟩ (by norm_num))
theorem R28345 : Reach 28345 := rs (se 2 (by rfl) ⟨10629, by rfl⟩) (B 21259 (by norm_num) ⟨10629, by rfl⟩ (by norm_num))
theorem R28381 : Reach 28381 := rs (se 3 (by rfl) ⟨5321, by rfl⟩) (B 10643 (by norm_num) ⟨5321, by rfl⟩ (by norm_num))
theorem R28397 : Reach 28397 := rs (se 3 (by rfl) ⟨5324, by rfl⟩) (B 10649 (by norm_num) ⟨5324, by rfl⟩ (by norm_num))
theorem R28417 : Reach 28417 := rs (se 2 (by rfl) ⟨10656, by rfl⟩) (B 21313 (by norm_num) ⟨10656, by rfl⟩ (by norm_num))
theorem R28453 : Reach 28453 := rs (se 4 (by rfl) ⟨2667, by rfl⟩) (B 5335 (by norm_num) ⟨2667, by rfl⟩ (by norm_num))
theorem R28489 : Reach 28489 := rs (se 2 (by rfl) ⟨10683, by rfl⟩) (B 21367 (by norm_num) ⟨10683, by rfl⟩ (by norm_num))
theorem R28525 : Reach 28525 := rs (se 3 (by rfl) ⟨5348, by rfl⟩) (B 10697 (by norm_num) ⟨5348, by rfl⟩ (by norm_num))
theorem R28561 : Reach 28561 := rs (se 2 (by rfl) ⟨10710, by rfl⟩) (B 21421 (by norm_num) ⟨10710, by rfl⟩ (by norm_num))
theorem R61357 : Reach 61357 := rs (se 3 (by rfl) ⟨11504, by rfl⟩) (B 23009 (by norm_num) ⟨11504, by rfl⟩ (by norm_num))
theorem R28597 : Reach 28597 := rs (se 5 (by rfl) ⟨1340, by rfl⟩) (B 2681 (by norm_num) ⟨1340, by rfl⟩ (by norm_num))
theorem R28633 : Reach 28633 := rs (se 2 (by rfl) ⟨10737, by rfl⟩) (B 21475 (by norm_num) ⟨10737, by rfl⟩ (by norm_num))
theorem R28669 : Reach 28669 := rs (se 3 (by rfl) ⟨5375, by rfl⟩) (B 10751 (by norm_num) ⟨5375, by rfl⟩ (by norm_num))
theorem R61469 : Reach 61469 := rs (se 3 (by rfl) ⟨11525, by rfl⟩) (B 23051 (by norm_num) ⟨11525, by rfl⟩ (by norm_num))
theorem R28705 : Reach 28705 := rs (se 2 (by rfl) ⟨10764, by rfl⟩) (B 21529 (by norm_num) ⟨10764, by rfl⟩ (by norm_num))
theorem R28741 : Reach 28741 := rs (se 4 (by rfl) ⟨2694, by rfl⟩) (B 5389 (by norm_num) ⟨2694, by rfl⟩ (by norm_num))
theorem R28777 : Reach 28777 := rs (se 2 (by rfl) ⟨10791, by rfl⟩) (B 21583 (by norm_num) ⟨10791, by rfl⟩ (by norm_num))
theorem R28813 : Reach 28813 := rs (se 3 (by rfl) ⟨5402, by rfl⟩) (B 10805 (by norm_num) ⟨5402, by rfl⟩ (by norm_num))
theorem R28841 : Reach 28841 := rs (se 2 (by rfl) ⟨10815, by rfl⟩) (B 21631 (by norm_num) ⟨10815, by rfl⟩ (by norm_num))
theorem R28849 : Reach 28849 := rs (se 2 (by rfl) ⟨10818, by rfl⟩) (B 21637 (by norm_num) ⟨10818, by rfl⟩ (by norm_num))
theorem R94405 : Reach 94405 := rs (se 4 (by rfl) ⟨8850, by rfl⟩) (B 17701 (by norm_num) ⟨8850, by rfl⟩ (by norm_num))
theorem R28885 : Reach 28885 := rs (se 7 (by rfl) ⟨338, by rfl⟩) (B 677 (by norm_num) ⟨338, by rfl⟩ (by norm_num))
theorem R61661 : Reach 61661 := rs (se 3 (by rfl) ⟨11561, by rfl⟩) (B 23123 (by norm_num) ⟨11561, by rfl⟩ (by norm_num))
theorem R61685 : Reach 61685 := rs (se 5 (by rfl) ⟨2891, by rfl⟩) (B 5783 (by norm_num) ⟨2891, by rfl⟩ (by norm_num))
theorem R28921 : Reach 28921 := rs (se 2 (by rfl) ⟨10845, by rfl⟩) (B 21691 (by norm_num) ⟨10845, by rfl⟩ (by norm_num))
theorem R28957 : Reach 28957 := rs (se 3 (by rfl) ⟨5429, by rfl⟩) (B 10859 (by norm_num) ⟨5429, by rfl⟩ (by norm_num))
theorem R28993 : Reach 28993 := rs (se 2 (by rfl) ⟨10872, by rfl⟩) (B 21745 (by norm_num) ⟨10872, by rfl⟩ (by norm_num))
theorem R29029 : Reach 29029 := rs (se 4 (by rfl) ⟨2721, by rfl⟩) (B 5443 (by norm_num) ⟨2721, by rfl⟩ (by norm_num))
theorem R94565 : Reach 94565 := rs (se 4 (by rfl) ⟨8865, by rfl⟩) (B 17731 (by norm_num) ⟨8865, by rfl⟩ (by norm_num))
theorem R61829 : Reach 61829 := rs (se 4 (by rfl) ⟨5796, by rfl⟩) (B 11593 (by norm_num) ⟨5796, by rfl⟩ (by norm_num))
theorem R29065 : Reach 29065 := rs (se 2 (by rfl) ⟨10899, by rfl⟩) (B 21799 (by norm_num) ⟨10899, by rfl⟩ (by norm_num))
theorem R29101 : Reach 29101 := rs (se 3 (by rfl) ⟨5456, by rfl⟩) (B 10913 (by norm_num) ⟨5456, by rfl⟩ (by norm_num))
theorem R29137 : Reach 29137 := rs (se 2 (by rfl) ⟨10926, by rfl⟩) (B 21853 (by norm_num) ⟨10926, by rfl⟩ (by norm_num))
theorem R94709 : Reach 94709 := rs (se 5 (by rfl) ⟨4439, by rfl⟩) (B 8879 (by norm_num) ⟨4439, by rfl⟩ (by norm_num))
theorem R29173 : Reach 29173 := rs (se 5 (by rfl) ⟨1367, by rfl⟩) (B 2735 (by norm_num) ⟨1367, by rfl⟩ (by norm_num))
theorem R29209 : Reach 29209 := rs (se 2 (by rfl) ⟨10953, by rfl⟩) (B 21907 (by norm_num) ⟨10953, by rfl⟩ (by norm_num))
theorem R62005 : Reach 62005 := rs (se 5 (by rfl) ⟨2906, by rfl⟩) (B 5813 (by norm_num) ⟨2906, by rfl⟩ (by norm_num))
theorem R29245 : Reach 29245 := rs (se 3 (by rfl) ⟨5483, by rfl⟩) (B 10967 (by norm_num) ⟨5483, by rfl⟩ (by norm_num))
theorem R29281 : Reach 29281 := rs (se 2 (by rfl) ⟨10980, by rfl⟩) (B 21961 (by norm_num) ⟨10980, by rfl⟩ (by norm_num))
theorem R29317 : Reach 29317 := rs (se 4 (by rfl) ⟨2748, by rfl⟩) (B 5497 (by norm_num) ⟨2748, by rfl⟩ (by norm_num))
theorem R62117 : Reach 62117 := rs (se 4 (by rfl) ⟨5823, by rfl⟩) (B 11647 (by norm_num) ⟨5823, by rfl⟩ (by norm_num))
theorem R29353 : Reach 29353 := rs (se 2 (by rfl) ⟨11007, by rfl⟩) (B 22015 (by norm_num) ⟨11007, by rfl⟩ (by norm_num))
theorem R29389 : Reach 29389 := rs (se 3 (by rfl) ⟨5510, by rfl⟩) (B 11021 (by norm_num) ⟨5510, by rfl⟩ (by norm_num))
theorem R29425 : Reach 29425 := rs (se 2 (by rfl) ⟨11034, by rfl⟩) (B 22069 (by norm_num) ⟨11034, by rfl⟩ (by norm_num))
theorem R29461 : Reach 29461 := rs (se 6 (by rfl) ⟨690, by rfl⟩) (B 1381 (by norm_num) ⟨690, by rfl⟩ (by norm_num))
theorem R29497 : Reach 29497 := rs (se 2 (by rfl) ⟨11061, by rfl⟩) (B 22123 (by norm_num) ⟨11061, by rfl⟩ (by norm_num))
theorem R29521 : Reach 29521 := rs (se 2 (by rfl) ⟨11070, by rfl⟩) (B 22141 (by norm_num) ⟨11070, by rfl⟩ (by norm_num))
theorem R29533 : Reach 29533 := rs (se 3 (by rfl) ⟨5537, by rfl⟩) (B 11075 (by norm_num) ⟨5537, by rfl⟩ (by norm_num))
theorem R62309 : Reach 62309 := rs (se 4 (by rfl) ⟨5841, by rfl⟩) (B 11683 (by norm_num) ⟨5841, by rfl⟩ (by norm_num))
theorem R29569 : Reach 29569 := rs (se 2 (by rfl) ⟨11088, by rfl⟩) (B 22177 (by norm_num) ⟨11088, by rfl⟩ (by norm_num))
theorem R29605 : Reach 29605 := rs (se 4 (by rfl) ⟨2775, by rfl⟩) (B 5551 (by norm_num) ⟨2775, by rfl⟩ (by norm_num))
theorem R127925 : Reach 127925 := rs (se 5 (by rfl) ⟨5996, by rfl⟩) (B 11993 (by norm_num) ⟨5996, by rfl⟩ (by norm_num))
theorem R29641 : Reach 29641 := rs (se 2 (by rfl) ⟨11115, by rfl⟩) (B 22231 (by norm_num) ⟨11115, by rfl⟩ (by norm_num))
theorem R29677 : Reach 29677 := rs (se 3 (by rfl) ⟨5564, by rfl⟩) (B 11129 (by norm_num) ⟨5564, by rfl⟩ (by norm_num))
theorem R29713 : Reach 29713 := rs (se 2 (by rfl) ⟨11142, by rfl⟩) (B 22285 (by norm_num) ⟨11142, by rfl⟩ (by norm_num))
theorem R29741 : Reach 29741 := rs (se 3 (by rfl) ⟨5576, by rfl⟩) (B 11153 (by norm_num) ⟨5576, by rfl⟩ (by norm_num))
theorem R29749 : Reach 29749 := rs (se 5 (by rfl) ⟨1394, by rfl⟩) (B 2789 (by norm_num) ⟨1394, by rfl⟩ (by norm_num))
theorem R29777 : Reach 29777 := rs (se 2 (by rfl) ⟨11166, by rfl⟩) (B 22333 (by norm_num) ⟨11166, by rfl⟩ (by norm_num))
theorem R29785 : Reach 29785 := rs (se 2 (by rfl) ⟨11169, by rfl⟩) (B 22339 (by norm_num) ⟨11169, by rfl⟩ (by norm_num))
theorem R29813 : Reach 29813 := rs (se 5 (by rfl) ⟨1397, by rfl⟩) (B 2795 (by norm_num) ⟨1397, by rfl⟩ (by norm_num))
theorem R29821 : Reach 29821 := rs (se 3 (by rfl) ⟨5591, by rfl⟩) (B 11183 (by norm_num) ⟨5591, by rfl⟩ (by norm_num))
theorem R29857 : Reach 29857 := rs (se 2 (by rfl) ⟨11196, by rfl⟩) (B 22393 (by norm_num) ⟨11196, by rfl⟩ (by norm_num))
theorem R62653 : Reach 62653 := rs (se 3 (by rfl) ⟨11747, by rfl⟩) (B 23495 (by norm_num) ⟨11747, by rfl⟩ (by norm_num))
theorem R29893 : Reach 29893 := rs (se 4 (by rfl) ⟨2802, by rfl⟩) (B 5605 (by norm_num) ⟨2802, by rfl⟩ (by norm_num))
theorem R29909 : Reach 29909 := rs (se 7 (by rfl) ⟨350, by rfl⟩) (B 701 (by norm_num) ⟨350, by rfl⟩ (by norm_num))
theorem R29929 : Reach 29929 := rs (se 2 (by rfl) ⟨11223, by rfl⟩) (B 22447 (by norm_num) ⟨11223, by rfl⟩ (by norm_num))
theorem R29965 : Reach 29965 := rs (se 3 (by rfl) ⟨5618, by rfl⟩) (B 11237 (by norm_num) ⟨5618, by rfl⟩ (by norm_num))
theorem R30001 : Reach 30001 := rs (se 2 (by rfl) ⟨11250, by rfl⟩) (B 22501 (by norm_num) ⟨11250, by rfl⟩ (by norm_num))
theorem R30037 : Reach 30037 := rs (se 13 (by rfl) ⟨5, by rfl⟩) (B 11 (by norm_num) ⟨5, by rfl⟩ (by norm_num))
theorem R30061 : Reach 30061 := rs (se 3 (by rfl) ⟨5636, by rfl⟩) (B 11273 (by norm_num) ⟨5636, by rfl⟩ (by norm_num))
theorem R193909 : Reach 193909 := rs (se 5 (by rfl) ⟨9089, by rfl⟩) (B 18179 (by norm_num) ⟨9089, by rfl⟩ (by norm_num))
theorem R30073 : Reach 30073 := rs (se 2 (by rfl) ⟨11277, by rfl⟩) (B 22555 (by norm_num) ⟨11277, by rfl⟩ (by norm_num))
theorem R30109 : Reach 30109 := rs (se 3 (by rfl) ⟨5645, by rfl⟩) (B 11291 (by norm_num) ⟨5645, by rfl⟩ (by norm_num))
theorem R30145 : Reach 30145 := rs (se 2 (by rfl) ⟨11304, by rfl⟩) (B 22609 (by norm_num) ⟨11304, by rfl⟩ (by norm_num))
theorem R30181 : Reach 30181 := rs (se 4 (by rfl) ⟨2829, by rfl⟩) (B 5659 (by norm_num) ⟨2829, by rfl⟩ (by norm_num))
theorem R30217 : Reach 30217 := rs (se 2 (by rfl) ⟨11331, by rfl⟩) (B 22663 (by norm_num) ⟨11331, by rfl⟩ (by norm_num))
theorem R30233 : Reach 30233 := rs (se 2 (by rfl) ⟨11337, by rfl⟩) (B 22675 (by norm_num) ⟨11337, by rfl⟩ (by norm_num))
theorem R30253 : Reach 30253 := rs (se 3 (by rfl) ⟨5672, by rfl⟩) (B 11345 (by norm_num) ⟨5672, by rfl⟩ (by norm_num))
theorem R30289 : Reach 30289 := rs (se 2 (by rfl) ⟨11358, by rfl⟩) (B 22717 (by norm_num) ⟨11358, by rfl⟩ (by norm_num))
theorem R1799765 : Reach 1799765 := rs (se 8 (by rfl) ⟨10545, by rfl⟩) (B 21091 (by norm_num) ⟨10545, by rfl⟩ (by norm_num))
theorem R226901 : Reach 226901 := rs (se 8 (by rfl) ⟨1329, by rfl⟩) (B 2659 (by norm_num) ⟨1329, by rfl⟩ (by norm_num))
theorem R30325 : Reach 30325 := rs (se 5 (by rfl) ⟨1421, by rfl⟩) (B 2843 (by norm_num) ⟨1421, by rfl⟩ (by norm_num))
theorem R30361 : Reach 30361 := rs (se 2 (by rfl) ⟨11385, by rfl⟩) (B 22771 (by norm_num) ⟨11385, by rfl⟩ (by norm_num))
theorem R30385 : Reach 30385 := rs (se 2 (by rfl) ⟨11394, by rfl⟩) (B 22789 (by norm_num) ⟨11394, by rfl⟩ (by norm_num))
theorem R30397 : Reach 30397 := rs (se 3 (by rfl) ⟨5699, by rfl⟩) (B 11399 (by norm_num) ⟨5699, by rfl⟩ (by norm_num))
theorem R30433 : Reach 30433 := rs (se 2 (by rfl) ⟨11412, by rfl⟩) (B 22825 (by norm_num) ⟨11412, by rfl⟩ (by norm_num))
theorem R30469 : Reach 30469 := rs (se 4 (by rfl) ⟨2856, by rfl⟩) (B 5713 (by norm_num) ⟨2856, by rfl⟩ (by norm_num))
theorem R128789 : Reach 128789 := rs (se 6 (by rfl) ⟨3018, by rfl⟩) (B 6037 (by norm_num) ⟨3018, by rfl⟩ (by norm_num))
theorem R63301 : Reach 63301 := rs (se 4 (by rfl) ⟨5934, by rfl⟩) (B 11869 (by norm_num) ⟨5934, by rfl⟩ (by norm_num))
theorem R63317 : Reach 63317 := rs (se 9 (by rfl) ⟨185, by rfl⟩) (B 371 (by norm_num) ⟨185, by rfl⟩ (by norm_num))
theorem R30557 : Reach 30557 := rs (se 3 (by rfl) ⟨5729, by rfl⟩) (B 11459 (by norm_num) ⟨5729, by rfl⟩ (by norm_num))
theorem R30601 : Reach 30601 := rs (se 2 (by rfl) ⟨11475, by rfl⟩) (B 22951 (by norm_num) ⟨11475, by rfl⟩ (by norm_num))
theorem R30613 : Reach 30613 := rs (se 6 (by rfl) ⟨717, by rfl⟩) (B 1435 (by norm_num) ⟨717, by rfl⟩ (by norm_num))
theorem R63413 : Reach 63413 := rs (se 5 (by rfl) ⟨2972, by rfl⟩) (B 5945 (by norm_num) ⟨2972, by rfl⟩ (by norm_num))
theorem R30649 : Reach 30649 := rs (se 2 (by rfl) ⟨11493, by rfl⟩) (B 22987 (by norm_num) ⟨11493, by rfl⟩ (by norm_num))
theorem R30709 : Reach 30709 := rs (se 5 (by rfl) ⟨1439, by rfl⟩) (B 2879 (by norm_num) ⟨1439, by rfl⟩ (by norm_num))
theorem R30749 : Reach 30749 := rs (se 3 (by rfl) ⟨5765, by rfl⟩) (B 11531 (by norm_num) ⟨5765, by rfl⟩ (by norm_num))
theorem R63605 : Reach 63605 := rs (se 5 (by rfl) ⟨2981, by rfl⟩) (B 5963 (by norm_num) ⟨2981, by rfl⟩ (by norm_num))
theorem R30881 : Reach 30881 := rs (se 2 (by rfl) ⟨11580, by rfl⟩) (B 23161 (by norm_num) ⟨11580, by rfl⟩ (by norm_num))
theorem R30937 : Reach 30937 := rs (se 2 (by rfl) ⟨11601, by rfl⟩) (B 23203 (by norm_num) ⟨11601, by rfl⟩ (by norm_num))
theorem R31033 : Reach 31033 := rs (se 2 (by rfl) ⟨11637, by rfl⟩) (B 23275 (by norm_num) ⟨11637, by rfl⟩ (by norm_num))
theorem R424277 : Reach 424277 := rs (se 10 (by rfl) ⟨621, by rfl⟩) (B 1243 (by norm_num) ⟨621, by rfl⟩ (by norm_num))
theorem R31205 : Reach 31205 := rs (se 4 (by rfl) ⟨2925, by rfl⟩) (B 5851 (by norm_num) ⟨2925, by rfl⟩ (by norm_num))
theorem R31261 : Reach 31261 := rs (se 3 (by rfl) ⟨5861, by rfl⟩) (B 11723 (by norm_num) ⟨5861, by rfl⟩ (by norm_num))
theorem R227893 : Reach 227893 := rs (se 5 (by rfl) ⟨10682, by rfl⟩) (B 21365 (by norm_num) ⟨10682, by rfl⟩ (by norm_num))
theorem R96821 : Reach 96821 := rs (se 5 (by rfl) ⟨4538, by rfl⟩) (B 9077 (by norm_num) ⟨4538, by rfl⟩ (by norm_num))
theorem R31313 : Reach 31313 := rs (se 2 (by rfl) ⟨11742, by rfl⟩) (B 23485 (by norm_num) ⟨11742, by rfl⟩ (by norm_num))
theorem R31357 : Reach 31357 := rs (se 3 (by rfl) ⟨5879, by rfl⟩) (B 11759 (by norm_num) ⟨5879, by rfl⟩ (by norm_num))
theorem R97109 : Reach 97109 := rs (se 9 (by rfl) ⟨284, by rfl⟩) (B 569 (by norm_num) ⟨284, by rfl⟩ (by norm_num))
theorem R31765 : Reach 31765 := rs (se 6 (by rfl) ⟨744, by rfl⟩) (B 1489 (by norm_num) ⟨744, by rfl⟩ (by norm_num))
theorem R31789 : Reach 31789 := rs (se 3 (by rfl) ⟨5960, by rfl⟩) (B 11921 (by norm_num) ⟨5960, by rfl⟩ (by norm_num))
theorem R64597 : Reach 64597 := rs (se 8 (by rfl) ⟨378, by rfl⟩) (B 757 (by norm_num) ⟨378, by rfl⟩ (by norm_num))
theorem R31853 : Reach 31853 := rs (se 3 (by rfl) ⟨5972, by rfl⟩) (B 11945 (by norm_num) ⟨5972, by rfl⟩ (by norm_num))
theorem R31909 : Reach 31909 := rs (se 4 (by rfl) ⟨2991, by rfl⟩) (B 5983 (by norm_num) ⟨2991, by rfl⟩ (by norm_num))
theorem R64709 : Reach 64709 := rs (se 4 (by rfl) ⟨6066, by rfl⟩) (B 12133 (by norm_num) ⟨6066, by rfl⟩ (by norm_num))
theorem R32005 : Reach 32005 := rs (se 4 (by rfl) ⟨3000, by rfl⟩) (B 6001 (by norm_num) ⟨3000, by rfl⟩ (by norm_num))
theorem R64901 : Reach 64901 := rs (se 4 (by rfl) ⟨6084, by rfl⟩) (B 12169 (by norm_num) ⟨6084, by rfl⟩ (by norm_num))
theorem R32485 : Reach 32485 := rs (se 4 (by rfl) ⟨3045, by rfl⟩) (B 6091 (by norm_num) ⟨3045, by rfl⟩ (by norm_num))
theorem R32501 : Reach 32501 := rs (se 5 (by rfl) ⟨1523, by rfl⟩) (B 3047 (by norm_num) ⟨1523, by rfl⟩ (by norm_num))
theorem R32557 : Reach 32557 := rs (se 3 (by rfl) ⟨6104, by rfl⟩) (B 12209 (by norm_num) ⟨6104, by rfl⟩ (by norm_num))
theorem R32653 : Reach 32653 := rs (se 3 (by rfl) ⟨6122, by rfl⟩) (B 12245 (by norm_num) ⟨6122, by rfl⟩ (by norm_num))
theorem R98293 : Reach 98293 := rs (se 5 (by rfl) ⟨4607, by rfl⟩) (B 9215 (by norm_num) ⟨4607, by rfl⟩ (by norm_num))
theorem R65549 : Reach 65549 := rs (se 3 (by rfl) ⟨12290, by rfl⟩) R24581
theorem R32881 : Reach 32881 := rs (se 2 (by rfl) ⟨12330, by rfl⟩) R24661
theorem R65681 : Reach 65681 := rs (se 2 (by rfl) ⟨24630, by rfl⟩) R49261
theorem R65731 : Reach 65731 := rs (se 1 (by rfl) ⟨49298, by rfl⟩) R98597
theorem R32977 : Reach 32977 := rs (se 2 (by rfl) ⟨12366, by rfl⟩) R24733
theorem R32995 : Reach 32995 := rs (se 1 (by rfl) ⟨24746, by rfl⟩) R49493
theorem R33043 : Reach 33043 := rs (se 1 (by rfl) ⟨24782, by rfl⟩) R49565
theorem R327989 : Reach 327989 := rs (se 5 (by rfl) ⟨15374, by rfl⟩) R30749
theorem R65873 : Reach 65873 := rs (se 2 (by rfl) ⟨24702, by rfl⟩) R49405
theorem R33139 : Reach 33139 := rs (se 1 (by rfl) ⟨24854, by rfl⟩) R49709
theorem R98723 : Reach 98723 := rs (se 1 (by rfl) ⟨74042, by rfl⟩) R148085
theorem R98765 : Reach 98765 := rs (se 3 (by rfl) ⟨18518, by rfl⟩) R37037
theorem R33473 : Reach 33473 := rs (se 2 (by rfl) ⟨12552, by rfl⟩) R25105
theorem R656099 : Reach 656099 := rs (se 1 (by rfl) ⟨492074, by rfl⟩) R984149
theorem R33635 : Reach 33635 := rs (se 1 (by rfl) ⟨25226, by rfl⟩) R50453
theorem R33715 : Reach 33715 := rs (se 1 (by rfl) ⟨25286, by rfl⟩) R50573
theorem R66541 : Reach 66541 := rs (se 3 (by rfl) ⟨12476, by rfl⟩) R24953
theorem R230627 : Reach 230627 := rs (se 1 (by rfl) ⟨172970, by rfl⟩) R345941
theorem R34033 : Reach 34033 := rs (se 2 (by rfl) ⟨12762, by rfl⟩) R25525
theorem R99569 : Reach 99569 := rs (se 2 (by rfl) ⟨37338, by rfl⟩) R74677
theorem R66865 : Reach 66865 := rs (se 2 (by rfl) ⟨25074, by rfl⟩) R50149
theorem R34177 : Reach 34177 := rs (se 2 (by rfl) ⟨12816, by rfl⟩) R25633
theorem R34195 : Reach 34195 := rs (se 1 (by rfl) ⟨25646, by rfl⟩) R51293
theorem R132515 : Reach 132515 := rs (se 1 (by rfl) ⟨99386, by rfl⟩) R198773
theorem R34273 : Reach 34273 := rs (se 2 (by rfl) ⟨12852, by rfl⟩) R25705
theorem R67139 : Reach 67139 := rs (se 1 (by rfl) ⟨50354, by rfl⟩) R100709
theorem R132677 : Reach 132677 := rs (se 4 (by rfl) ⟨12438, by rfl⟩) R24877
theorem R67331 : Reach 67331 := rs (se 1 (by rfl) ⟨50498, by rfl⟩) R100997
theorem R67405 : Reach 67405 := rs (se 3 (by rfl) ⟨12638, by rfl⟩) R25277
theorem R34673 : Reach 34673 := rs (se 2 (by rfl) ⟨13002, by rfl⟩) R26005
theorem R100237 : Reach 100237 := rs (se 3 (by rfl) ⟨18794, by rfl⟩) R37589
theorem R34753 : Reach 34753 := rs (se 2 (by rfl) ⟨13032, by rfl⟩) R26065
theorem R34787 : Reach 34787 := rs (se 1 (by rfl) ⟨26090, by rfl⟩) R52181
theorem R34867 : Reach 34867 := rs (se 1 (by rfl) ⟨26150, by rfl⟩) R52301
theorem R67661 : Reach 67661 := rs (se 3 (by rfl) ⟨12686, by rfl⟩) R25373
theorem R67729 : Reach 67729 := rs (se 2 (by rfl) ⟨25398, by rfl⟩) R50797
theorem R133325 : Reach 133325 := rs (se 3 (by rfl) ⟨24998, by rfl⟩) R49997
theorem R35057 : Reach 35057 := rs (se 2 (by rfl) ⟨13146, by rfl⟩) R26293
theorem R67949 : Reach 67949 := rs (se 3 (by rfl) ⟨12740, by rfl⟩) R25481
theorem R68003 : Reach 68003 := rs (se 1 (by rfl) ⟨51002, by rfl⟩) R102005
theorem R35267 : Reach 35267 := rs (se 1 (by rfl) ⟨26450, by rfl⟩) R52901
theorem R35297 : Reach 35297 := rs (se 2 (by rfl) ⟨13236, by rfl⟩) R26473
theorem R35315 : Reach 35315 := rs (se 1 (by rfl) ⟨26486, by rfl⟩) R52973
theorem R35345 : Reach 35345 := rs (se 2 (by rfl) ⟨13254, by rfl⟩) R26509
theorem R35363 : Reach 35363 := rs (se 1 (by rfl) ⟨26522, by rfl⟩) R53045
theorem R68141 : Reach 68141 := rs (se 3 (by rfl) ⟨12776, by rfl⟩) R25553
theorem R35393 : Reach 35393 := rs (se 2 (by rfl) ⟨13272, by rfl⟩) R26545
theorem R35411 : Reach 35411 := rs (se 1 (by rfl) ⟨26558, by rfl⟩) R53117
theorem R35425 : Reach 35425 := rs (se 2 (by rfl) ⟨13284, by rfl⟩) R26569
theorem R35441 : Reach 35441 := rs (se 2 (by rfl) ⟨13290, by rfl⟩) R26581
theorem R35459 : Reach 35459 := rs (se 1 (by rfl) ⟨26594, by rfl⟩) R53189
theorem R35489 : Reach 35489 := rs (se 2 (by rfl) ⟨13308, by rfl⟩) R26617
theorem R101027 : Reach 101027 := rs (se 1 (by rfl) ⟨75770, by rfl⟩) R151541
theorem R68273 : Reach 68273 := rs (se 2 (by rfl) ⟨25602, by rfl⟩) R51205
theorem R35507 : Reach 35507 := rs (se 1 (by rfl) ⟨26630, by rfl⟩) R53261
theorem R35537 : Reach 35537 := rs (se 2 (by rfl) ⟨13326, by rfl⟩) R26653
theorem R1018595 : Reach 1018595 := rs (se 1 (by rfl) ⟨763946, by rfl⟩) R1527893
theorem R35555 : Reach 35555 := rs (se 1 (by rfl) ⟨26666, by rfl⟩) R53333
theorem R68323 : Reach 68323 := rs (se 1 (by rfl) ⟨51242, by rfl⟩) R102485
theorem R35585 : Reach 35585 := rs (se 2 (by rfl) ⟨13344, by rfl⟩) R26689
theorem R35603 : Reach 35603 := rs (se 1 (by rfl) ⟨26702, by rfl⟩) R53405
theorem R166691 : Reach 166691 := rs (se 1 (by rfl) ⟨125018, by rfl⟩) R250037
theorem R35633 : Reach 35633 := rs (se 2 (by rfl) ⟨13362, by rfl⟩) R26725
theorem R35651 : Reach 35651 := rs (se 1 (by rfl) ⟨26738, by rfl⟩) R53477
theorem R35681 : Reach 35681 := rs (se 2 (by rfl) ⟨13380, by rfl⟩) R26761
theorem R199523 : Reach 199523 := rs (se 1 (by rfl) ⟨149642, by rfl⟩) R299285
theorem R68465 : Reach 68465 := rs (se 2 (by rfl) ⟨25674, by rfl⟩) R51349
theorem R35699 : Reach 35699 := rs (se 1 (by rfl) ⟨26774, by rfl⟩) R53549
theorem R35729 : Reach 35729 := rs (se 2 (by rfl) ⟨13398, by rfl⟩) R26797
theorem R35747 : Reach 35747 := rs (se 1 (by rfl) ⟨26810, by rfl⟩) R53621
theorem R35777 : Reach 35777 := rs (se 2 (by rfl) ⟨13416, by rfl⟩) R26833
theorem R35795 : Reach 35795 := rs (se 1 (by rfl) ⟨26846, by rfl⟩) R53693
theorem R35825 : Reach 35825 := rs (se 2 (by rfl) ⟨13434, by rfl⟩) R26869
theorem R35843 : Reach 35843 := rs (se 1 (by rfl) ⟨26882, by rfl⟩) R53765
theorem R35873 : Reach 35873 := rs (se 2 (by rfl) ⟨13452, by rfl⟩) R26905
theorem R35891 : Reach 35891 := rs (se 1 (by rfl) ⟨26918, by rfl⟩) R53837
theorem R35921 : Reach 35921 := rs (se 2 (by rfl) ⟨13470, by rfl⟩) R26941
theorem R35939 : Reach 35939 := rs (se 1 (by rfl) ⟨26954, by rfl⟩) R53909
theorem R35969 : Reach 35969 := rs (se 2 (by rfl) ⟨13488, by rfl⟩) R26977
theorem R35987 : Reach 35987 := rs (se 1 (by rfl) ⟨26990, by rfl⟩) R53981
theorem R36017 : Reach 36017 := rs (se 2 (by rfl) ⟨13506, by rfl⟩) R27013
theorem R36035 : Reach 36035 := rs (se 1 (by rfl) ⟨27026, by rfl⟩) R54053
theorem R36065 : Reach 36065 := rs (se 2 (by rfl) ⟨13524, by rfl⟩) R27049
theorem R36067 : Reach 36067 := rs (se 1 (by rfl) ⟨27050, by rfl⟩) R54101
theorem R68845 : Reach 68845 := rs (se 3 (by rfl) ⟨12908, by rfl⟩) R25817
theorem R36083 : Reach 36083 := rs (se 1 (by rfl) ⟨27062, by rfl⟩) R54125
theorem R36113 : Reach 36113 := rs (se 2 (by rfl) ⟨13542, by rfl⟩) R27085
theorem R36131 : Reach 36131 := rs (se 1 (by rfl) ⟨27098, by rfl⟩) R54197
theorem R101681 : Reach 101681 := rs (se 2 (by rfl) ⟨38130, by rfl⟩) R76261
theorem R36161 : Reach 36161 := rs (se 2 (by rfl) ⟨13560, by rfl⟩) R27121
theorem R36179 : Reach 36179 := rs (se 1 (by rfl) ⟨27134, by rfl⟩) R54269
theorem R36209 : Reach 36209 := rs (se 2 (by rfl) ⟨13578, by rfl⟩) R27157
theorem R36211 : Reach 36211 := rs (se 1 (by rfl) ⟨27158, by rfl⟩) R54317
theorem R36227 : Reach 36227 := rs (se 1 (by rfl) ⟨27170, by rfl⟩) R54341
theorem R69005 : Reach 69005 := rs (se 3 (by rfl) ⟨12938, by rfl⟩) R25877
theorem R36257 : Reach 36257 := rs (se 2 (by rfl) ⟨13596, by rfl⟩) R27193
theorem R36275 : Reach 36275 := rs (se 1 (by rfl) ⟨27206, by rfl⟩) R54413
theorem R36305 : Reach 36305 := rs (se 2 (by rfl) ⟨13614, by rfl⟩) R27229
theorem R36323 : Reach 36323 := rs (se 1 (by rfl) ⟨27242, by rfl⟩) R54485
theorem R36353 : Reach 36353 := rs (se 2 (by rfl) ⟨13632, by rfl⟩) R27265
theorem R36371 : Reach 36371 := rs (se 1 (by rfl) ⟨27278, by rfl⟩) R54557
theorem R36401 : Reach 36401 := rs (se 2 (by rfl) ⟨13650, by rfl⟩) R27301
theorem R36419 : Reach 36419 := rs (se 1 (by rfl) ⟨27314, by rfl⟩) R54629
theorem R69187 : Reach 69187 := rs (se 1 (by rfl) ⟨51890, by rfl⟩) R103781
theorem R36449 : Reach 36449 := rs (se 2 (by rfl) ⟨13668, by rfl⟩) R27337
theorem R36467 : Reach 36467 := rs (se 1 (by rfl) ⟨27350, by rfl⟩) R54701
theorem R36497 : Reach 36497 := rs (se 2 (by rfl) ⟨13686, by rfl⟩) R27373
theorem R36515 : Reach 36515 := rs (se 1 (by rfl) ⟨27386, by rfl⟩) R54773
theorem R36545 : Reach 36545 := rs (se 2 (by rfl) ⟨13704, by rfl⟩) R27409
theorem R36563 : Reach 36563 := rs (se 1 (by rfl) ⟨27422, by rfl⟩) R54845
theorem R36593 : Reach 36593 := rs (se 2 (by rfl) ⟨13722, by rfl⟩) R27445
theorem R36611 : Reach 36611 := rs (se 1 (by rfl) ⟨27458, by rfl⟩) R54917
theorem R36641 : Reach 36641 := rs (se 2 (by rfl) ⟨13740, by rfl⟩) R27481
theorem R36659 : Reach 36659 := rs (se 1 (by rfl) ⟨27494, by rfl⟩) R54989
theorem R69443 : Reach 69443 := rs (se 1 (by rfl) ⟨52082, by rfl⟩) R104165
theorem R36689 : Reach 36689 := rs (se 2 (by rfl) ⟨13758, by rfl⟩) R27517
theorem R36707 : Reach 36707 := rs (se 1 (by rfl) ⟨27530, by rfl⟩) R55061
theorem R36737 : Reach 36737 := rs (se 2 (by rfl) ⟨13776, by rfl⟩) R27553
theorem R36755 : Reach 36755 := rs (se 1 (by rfl) ⟨27566, by rfl⟩) R55133
theorem R36769 : Reach 36769 := rs (se 2 (by rfl) ⟨13788, by rfl⟩) R27577
theorem R36785 : Reach 36785 := rs (se 2 (by rfl) ⟨13794, by rfl⟩) R27589
theorem R36803 : Reach 36803 := rs (se 1 (by rfl) ⟨27602, by rfl⟩) R55205
theorem R36833 : Reach 36833 := rs (se 2 (by rfl) ⟨13812, by rfl⟩) R27625
theorem R36851 : Reach 36851 := rs (se 1 (by rfl) ⟨27638, by rfl⟩) R55277
theorem R200717 : Reach 200717 := rs (se 3 (by rfl) ⟨37634, by rfl⟩) R75269
theorem R36881 : Reach 36881 := rs (se 2 (by rfl) ⟨13830, by rfl⟩) R27661
theorem R36883 : Reach 36883 := rs (se 1 (by rfl) ⟨27662, by rfl⟩) R55325
theorem R36899 : Reach 36899 := rs (se 1 (by rfl) ⟨27674, by rfl⟩) R55349
theorem R36929 : Reach 36929 := rs (se 2 (by rfl) ⟨13848, by rfl⟩) R27697
theorem R36947 : Reach 36947 := rs (se 1 (by rfl) ⟨27710, by rfl⟩) R55421
theorem R36977 : Reach 36977 := rs (se 2 (by rfl) ⟨13866, by rfl⟩) R27733
theorem R36995 : Reach 36995 := rs (se 1 (by rfl) ⟨27746, by rfl⟩) R55493
theorem R37025 : Reach 37025 := rs (se 2 (by rfl) ⟨13884, by rfl⟩) R27769
theorem R37043 : Reach 37043 := rs (se 1 (by rfl) ⟨27782, by rfl⟩) R55565
theorem R37073 : Reach 37073 := rs (se 2 (by rfl) ⟨13902, by rfl⟩) R27805
theorem R37091 : Reach 37091 := rs (se 1 (by rfl) ⟨27818, by rfl⟩) R55637
theorem R37121 : Reach 37121 := rs (se 2 (by rfl) ⟨13920, by rfl⟩) R27841
theorem R37139 : Reach 37139 := rs (se 1 (by rfl) ⟨27854, by rfl⟩) R55709
theorem R37169 : Reach 37169 := rs (se 2 (by rfl) ⟨13938, by rfl⟩) R27877
theorem R37187 : Reach 37187 := rs (se 1 (by rfl) ⟨27890, by rfl⟩) R55781
theorem R37217 : Reach 37217 := rs (se 2 (by rfl) ⟨13956, by rfl⟩) R27913
theorem R37235 : Reach 37235 := rs (se 1 (by rfl) ⟨27926, by rfl⟩) R55853
theorem R37265 : Reach 37265 := rs (se 2 (by rfl) ⟨13974, by rfl⟩) R27949
theorem R37283 : Reach 37283 := rs (se 1 (by rfl) ⟨27962, by rfl⟩) R55925
theorem R37313 : Reach 37313 := rs (se 2 (by rfl) ⟨13992, by rfl⟩) R27985
theorem R37331 : Reach 37331 := rs (se 1 (by rfl) ⟨27998, by rfl⟩) R55997
theorem R266723 : Reach 266723 := rs (se 1 (by rfl) ⟨200042, by rfl⟩) R400085
theorem R37361 : Reach 37361 := rs (se 2 (by rfl) ⟨14010, by rfl⟩) R28021
theorem R37379 : Reach 37379 := rs (se 1 (by rfl) ⟨28034, by rfl⟩) R56069
theorem R37409 : Reach 37409 := rs (se 2 (by rfl) ⟨14028, by rfl⟩) R28057
theorem R70189 : Reach 70189 := rs (se 3 (by rfl) ⟨13160, by rfl⟩) R26321
theorem R37427 : Reach 37427 := rs (se 1 (by rfl) ⟨28070, by rfl⟩) R56141
theorem R37441 : Reach 37441 := rs (se 2 (by rfl) ⟨14040, by rfl⟩) R28081
theorem R37457 : Reach 37457 := rs (se 2 (by rfl) ⟨14046, by rfl⟩) R28093
theorem R37475 : Reach 37475 := rs (se 1 (by rfl) ⟨28106, by rfl⟩) R56213
theorem R37505 : Reach 37505 := rs (se 2 (by rfl) ⟨14064, by rfl⟩) R28129
theorem R37523 : Reach 37523 := rs (se 1 (by rfl) ⟨28142, by rfl⟩) R56285
theorem R37553 : Reach 37553 := rs (se 2 (by rfl) ⟨14082, by rfl⟩) R28165
theorem R37571 : Reach 37571 := rs (se 1 (by rfl) ⟨28178, by rfl⟩) R56357
theorem R37601 : Reach 37601 := rs (se 2 (by rfl) ⟨14100, by rfl⟩) R28201
theorem R103139 : Reach 103139 := rs (se 1 (by rfl) ⟨77354, by rfl⟩) R154709
theorem R37619 : Reach 37619 := rs (se 1 (by rfl) ⟨28214, by rfl⟩) R56429
theorem R37649 : Reach 37649 := rs (se 2 (by rfl) ⟨14118, by rfl⟩) R28237
theorem R1151765 : Reach 1151765 := rs (se 6 (by rfl) ⟨26994, by rfl⟩) R53989
theorem R37667 : Reach 37667 := rs (se 1 (by rfl) ⟨28250, by rfl⟩) R56501
theorem R37697 : Reach 37697 := rs (se 2 (by rfl) ⟨14136, by rfl⟩) R28273
theorem R37715 : Reach 37715 := rs (se 1 (by rfl) ⟨28286, by rfl⟩) R56573
theorem R37745 : Reach 37745 := rs (se 2 (by rfl) ⟨14154, by rfl⟩) R28309
theorem R37763 : Reach 37763 := rs (se 1 (by rfl) ⟨28322, by rfl⟩) R56645
theorem R70541 : Reach 70541 := rs (se 3 (by rfl) ⟨13226, by rfl⟩) R26453
theorem R37793 : Reach 37793 := rs (se 2 (by rfl) ⟨14172, by rfl⟩) R28345
theorem R70577 : Reach 70577 := rs (se 2 (by rfl) ⟨26466, by rfl⟩) R52933
theorem R37811 : Reach 37811 := rs (se 1 (by rfl) ⟨28358, by rfl⟩) R56717
theorem R37841 : Reach 37841 := rs (se 2 (by rfl) ⟨14190, by rfl⟩) R28381
theorem R37859 : Reach 37859 := rs (se 1 (by rfl) ⟨28394, by rfl⟩) R56789
theorem R37889 : Reach 37889 := rs (se 2 (by rfl) ⟨14208, by rfl⟩) R28417
theorem R37907 : Reach 37907 := rs (se 1 (by rfl) ⟨28430, by rfl⟩) R56861
theorem R37937 : Reach 37937 := rs (se 2 (by rfl) ⟨14226, by rfl⟩) R28453
theorem R136241 : Reach 136241 := rs (se 2 (by rfl) ⟨51090, by rfl⟩) R102181
theorem R37955 : Reach 37955 := rs (se 1 (by rfl) ⟨28466, by rfl⟩) R56933
theorem R37985 : Reach 37985 := rs (se 2 (by rfl) ⟨14244, by rfl⟩) R28489
theorem R38003 : Reach 38003 := rs (se 1 (by rfl) ⟨28502, by rfl⟩) R57005
theorem R38033 : Reach 38033 := rs (se 2 (by rfl) ⟨14262, by rfl⟩) R28525
theorem R38051 : Reach 38051 := rs (se 1 (by rfl) ⟨28538, by rfl⟩) R57077
theorem R38081 : Reach 38081 := rs (se 2 (by rfl) ⟨14280, by rfl⟩) R28561
theorem R70865 : Reach 70865 := rs (se 2 (by rfl) ⟨26574, by rfl⟩) R53149
theorem R38099 : Reach 38099 := rs (se 1 (by rfl) ⟨28574, by rfl⟩) R57149
theorem R38129 : Reach 38129 := rs (se 2 (by rfl) ⟨14298, by rfl⟩) R28597
theorem R38147 : Reach 38147 := rs (se 1 (by rfl) ⟨28610, by rfl⟩) R57221
theorem R38177 : Reach 38177 := rs (se 2 (by rfl) ⟨14316, by rfl⟩) R28633
theorem R38195 : Reach 38195 := rs (se 1 (by rfl) ⟨28646, by rfl⟩) R57293
theorem R38225 : Reach 38225 := rs (se 2 (by rfl) ⟨14334, by rfl⟩) R28669
theorem R38227 : Reach 38227 := rs (se 1 (by rfl) ⟨28670, by rfl⟩) R57341
theorem R38243 : Reach 38243 := rs (se 1 (by rfl) ⟨28682, by rfl⟩) R57365
theorem R38273 : Reach 38273 := rs (se 2 (by rfl) ⟨14352, by rfl⟩) R28705
theorem R38291 : Reach 38291 := rs (se 1 (by rfl) ⟨28718, by rfl⟩) R57437
theorem R38321 : Reach 38321 := rs (se 2 (by rfl) ⟨14370, by rfl⟩) R28741
theorem R38339 : Reach 38339 := rs (se 1 (by rfl) ⟨28754, by rfl⟩) R57509
theorem R38369 : Reach 38369 := rs (se 2 (by rfl) ⟨14388, by rfl⟩) R28777
theorem R38387 : Reach 38387 := rs (se 1 (by rfl) ⟨28790, by rfl⟩) R57581
theorem R38417 : Reach 38417 := rs (se 2 (by rfl) ⟨14406, by rfl⟩) R28813
theorem R38435 : Reach 38435 := rs (se 1 (by rfl) ⟨28826, by rfl⟩) R57653
theorem R38465 : Reach 38465 := rs (se 2 (by rfl) ⟨14424, by rfl⟩) R28849
theorem R38483 : Reach 38483 := rs (se 1 (by rfl) ⟨28862, by rfl⟩) R57725
theorem R38513 : Reach 38513 := rs (se 2 (by rfl) ⟨14442, by rfl⟩) R28885
theorem R38531 : Reach 38531 := rs (se 1 (by rfl) ⟨28898, by rfl⟩) R57797
theorem R38561 : Reach 38561 := rs (se 2 (by rfl) ⟨14460, by rfl⟩) R28921
theorem R38579 : Reach 38579 := rs (se 1 (by rfl) ⟨28934, by rfl⟩) R57869
theorem R366277 : Reach 366277 := rs (se 4 (by rfl) ⟨34338, by rfl⟩) R68677
theorem R38609 : Reach 38609 := rs (se 2 (by rfl) ⟨14478, by rfl⟩) R28957
theorem R38627 : Reach 38627 := rs (se 1 (by rfl) ⟨28970, by rfl⟩) R57941
theorem R38657 : Reach 38657 := rs (se 2 (by rfl) ⟨14496, by rfl⟩) R28993
theorem R38675 : Reach 38675 := rs (se 1 (by rfl) ⟨29006, by rfl⟩) R58013
theorem R71459 : Reach 71459 := rs (se 1 (by rfl) ⟨53594, by rfl⟩) R107189
theorem R38705 : Reach 38705 := rs (se 2 (by rfl) ⟨14514, by rfl⟩) R29029
theorem R38723 : Reach 38723 := rs (se 1 (by rfl) ⟨29042, by rfl⟩) R58085
theorem R38753 : Reach 38753 := rs (se 2 (by rfl) ⟨14532, by rfl⟩) R29065
theorem R71533 : Reach 71533 := rs (se 3 (by rfl) ⟨13412, by rfl⟩) R26825
theorem R38771 : Reach 38771 := rs (se 1 (by rfl) ⟨29078, by rfl⟩) R58157
theorem R38801 : Reach 38801 := rs (se 2 (by rfl) ⟨14550, by rfl⟩) R29101
theorem R38819 : Reach 38819 := rs (se 1 (by rfl) ⟨29114, by rfl⟩) R58229
theorem R38849 : Reach 38849 := rs (se 2 (by rfl) ⟨14568, by rfl⟩) R29137
theorem R38867 : Reach 38867 := rs (se 1 (by rfl) ⟨29150, by rfl⟩) R58301
theorem R38897 : Reach 38897 := rs (se 2 (by rfl) ⟨14586, by rfl⟩) R29173
theorem R38915 : Reach 38915 := rs (se 1 (by rfl) ⟨29186, by rfl⟩) R58373
theorem R38945 : Reach 38945 := rs (se 2 (by rfl) ⟨14604, by rfl⟩) R29209
theorem R38963 : Reach 38963 := rs (se 1 (by rfl) ⟨29222, by rfl⟩) R58445
theorem R71761 : Reach 71761 := rs (se 2 (by rfl) ⟨26910, by rfl⟩) R53821
theorem R38993 : Reach 38993 := rs (se 2 (by rfl) ⟨14622, by rfl⟩) R29245
theorem R39011 : Reach 39011 := rs (se 1 (by rfl) ⟨29258, by rfl⟩) R58517
theorem R39041 : Reach 39041 := rs (se 2 (by rfl) ⟨14640, by rfl⟩) R29281
theorem R39059 : Reach 39059 := rs (se 1 (by rfl) ⟨29294, by rfl⟩) R58589
theorem R39089 : Reach 39089 := rs (se 2 (by rfl) ⟨14658, by rfl⟩) R29317
theorem R39107 : Reach 39107 := rs (se 1 (by rfl) ⟨29330, by rfl⟩) R58661
theorem R39137 : Reach 39137 := rs (se 2 (by rfl) ⟨14676, by rfl⟩) R29353
theorem R71921 : Reach 71921 := rs (se 2 (by rfl) ⟨26970, by rfl⟩) R53941
theorem R39155 : Reach 39155 := rs (se 1 (by rfl) ⟨29366, by rfl⟩) R58733
theorem R39185 : Reach 39185 := rs (se 2 (by rfl) ⟨14694, by rfl⟩) R29389
theorem R39203 : Reach 39203 := rs (se 1 (by rfl) ⟨29402, by rfl⟩) R58805
theorem R39233 : Reach 39233 := rs (se 2 (by rfl) ⟨14712, by rfl⟩) R29425
theorem R39251 : Reach 39251 := rs (se 1 (by rfl) ⟨29438, by rfl⟩) R58877
theorem R72035 : Reach 72035 := rs (se 1 (by rfl) ⟨54026, by rfl⟩) R108053
theorem R39281 : Reach 39281 := rs (se 2 (by rfl) ⟨14730, by rfl⟩) R29461
theorem R39299 : Reach 39299 := rs (se 1 (by rfl) ⟨29474, by rfl⟩) R58949
theorem R39329 : Reach 39329 := rs (se 2 (by rfl) ⟨14748, by rfl⟩) R29497
theorem R39347 : Reach 39347 := rs (se 1 (by rfl) ⟨29510, by rfl⟩) R59021
theorem R39361 : Reach 39361 := rs (se 2 (by rfl) ⟨14760, by rfl⟩) R29521
theorem R39377 : Reach 39377 := rs (se 2 (by rfl) ⟨14766, by rfl⟩) R29533
theorem R39395 : Reach 39395 := rs (se 1 (by rfl) ⟨29546, by rfl⟩) R59093
theorem R137699 : Reach 137699 := rs (se 1 (by rfl) ⟨103274, by rfl⟩) R206549
theorem R39425 : Reach 39425 := rs (se 2 (by rfl) ⟨14784, by rfl⟩) R29569
theorem R39443 : Reach 39443 := rs (se 1 (by rfl) ⟨29582, by rfl⟩) R59165
theorem R39473 : Reach 39473 := rs (se 2 (by rfl) ⟨14802, by rfl⟩) R29605
theorem R39491 : Reach 39491 := rs (se 1 (by rfl) ⟨29618, by rfl⟩) R59237
theorem R39521 : Reach 39521 := rs (se 2 (by rfl) ⟨14820, by rfl⟩) R29641
theorem R39539 : Reach 39539 := rs (se 1 (by rfl) ⟨29654, by rfl⟩) R59309
theorem R39569 : Reach 39569 := rs (se 2 (by rfl) ⟨14838, by rfl⟩) R29677
theorem R39571 : Reach 39571 := rs (se 1 (by rfl) ⟨29678, by rfl⟩) R59357
theorem R39587 : Reach 39587 := rs (se 1 (by rfl) ⟨29690, by rfl⟩) R59381
theorem R39617 : Reach 39617 := rs (se 2 (by rfl) ⟨14856, by rfl⟩) R29713
theorem R39635 : Reach 39635 := rs (se 1 (by rfl) ⟨29726, by rfl⟩) R59453
theorem R39665 : Reach 39665 := rs (se 2 (by rfl) ⟨14874, by rfl⟩) R29749
theorem R39683 : Reach 39683 := rs (se 1 (by rfl) ⟨29762, by rfl⟩) R59525
theorem R39713 : Reach 39713 := rs (se 2 (by rfl) ⟨14892, by rfl⟩) R29785
theorem R39731 : Reach 39731 := rs (se 1 (by rfl) ⟨29798, by rfl⟩) R59597
theorem R39761 : Reach 39761 := rs (se 2 (by rfl) ⟨14910, by rfl⟩) R29821
theorem R39779 : Reach 39779 := rs (se 1 (by rfl) ⟨29834, by rfl⟩) R59669
theorem R203633 : Reach 203633 := rs (se 2 (by rfl) ⟨76362, by rfl⟩) R152725
theorem R39809 : Reach 39809 := rs (se 2 (by rfl) ⟨14928, by rfl⟩) R29857
theorem R39811 : Reach 39811 := rs (se 1 (by rfl) ⟨29858, by rfl⟩) R59717
theorem R39827 : Reach 39827 := rs (se 1 (by rfl) ⟨29870, by rfl⟩) R59741
theorem R39857 : Reach 39857 := rs (se 2 (by rfl) ⟨14946, by rfl⟩) R29893
theorem R39875 : Reach 39875 := rs (se 1 (by rfl) ⟨29906, by rfl⟩) R59813
theorem R105421 : Reach 105421 := rs (se 3 (by rfl) ⟨19766, by rfl⟩) R39533
theorem R39905 : Reach 39905 := rs (se 2 (by rfl) ⟨14964, by rfl⟩) R29929
theorem R39923 : Reach 39923 := rs (se 1 (by rfl) ⟨29942, by rfl⟩) R59885
theorem R39953 : Reach 39953 := rs (se 2 (by rfl) ⟨14982, by rfl⟩) R29965
theorem R39971 : Reach 39971 := rs (se 1 (by rfl) ⟨29978, by rfl⟩) R59957
theorem R40001 : Reach 40001 := rs (se 2 (by rfl) ⟨15000, by rfl⟩) R30001
theorem R40019 : Reach 40019 := rs (se 1 (by rfl) ⟨30014, by rfl⟩) R60029
theorem R40049 : Reach 40049 := rs (se 2 (by rfl) ⟨15018, by rfl⟩) R30037
theorem R40067 : Reach 40067 := rs (se 1 (by rfl) ⟨30050, by rfl⟩) R60101
theorem R40081 : Reach 40081 := rs (se 2 (by rfl) ⟨15030, by rfl⟩) R30061
theorem R40097 : Reach 40097 := rs (se 2 (by rfl) ⟨15036, by rfl⟩) R30073
theorem R40115 : Reach 40115 := rs (se 1 (by rfl) ⟨30086, by rfl⟩) R60173
theorem R40145 : Reach 40145 := rs (se 2 (by rfl) ⟨15054, by rfl⟩) R30109
theorem R40163 : Reach 40163 := rs (se 1 (by rfl) ⟨30122, by rfl⟩) R60245
theorem R40193 : Reach 40193 := rs (se 2 (by rfl) ⟨15072, by rfl⟩) R30145
theorem R40211 : Reach 40211 := rs (se 1 (by rfl) ⟨30158, by rfl⟩) R60317
theorem R40241 : Reach 40241 := rs (se 2 (by rfl) ⟨15090, by rfl⟩) R30181
theorem R40243 : Reach 40243 := rs (se 1 (by rfl) ⟨30182, by rfl⟩) R60365
theorem R40259 : Reach 40259 := rs (se 1 (by rfl) ⟨30194, by rfl⟩) R60389
theorem R73037 : Reach 73037 := rs (se 3 (by rfl) ⟨13694, by rfl⟩) R27389
theorem R40289 : Reach 40289 := rs (se 2 (by rfl) ⟨15108, by rfl⟩) R30217
theorem R40307 : Reach 40307 := rs (se 1 (by rfl) ⟨30230, by rfl⟩) R60461
theorem R40337 : Reach 40337 := rs (se 2 (by rfl) ⟨15126, by rfl⟩) R30253
theorem R40355 : Reach 40355 := rs (se 1 (by rfl) ⟨30266, by rfl⟩) R60533
theorem R40385 : Reach 40385 := rs (se 2 (by rfl) ⟨15144, by rfl⟩) R30289
theorem R40403 : Reach 40403 := rs (se 1 (by rfl) ⟨30302, by rfl⟩) R60605
theorem R40433 : Reach 40433 := rs (se 2 (by rfl) ⟨15162, by rfl⟩) R30325
theorem R73219 : Reach 73219 := rs (se 1 (by rfl) ⟨54914, by rfl⟩) R109829
theorem R40451 : Reach 40451 := rs (se 1 (by rfl) ⟨30338, by rfl⟩) R60677
theorem R40481 : Reach 40481 := rs (se 2 (by rfl) ⟨15180, by rfl⟩) R30361
theorem R40499 : Reach 40499 := rs (se 1 (by rfl) ⟨30374, by rfl⟩) R60749
theorem R40513 : Reach 40513 := rs (se 2 (by rfl) ⟨15192, by rfl⟩) R30385
theorem R40529 : Reach 40529 := rs (se 2 (by rfl) ⟨15198, by rfl⟩) R30397
theorem R40547 : Reach 40547 := rs (se 1 (by rfl) ⟨30410, by rfl⟩) R60821
theorem R73325 : Reach 73325 := rs (se 3 (by rfl) ⟨13748, by rfl⟩) R27497
theorem R40577 : Reach 40577 := rs (se 2 (by rfl) ⟨15216, by rfl⟩) R30433
theorem R40595 : Reach 40595 := rs (se 1 (by rfl) ⟨30446, by rfl⟩) R60893
theorem R73379 : Reach 73379 := rs (se 1 (by rfl) ⟨55034, by rfl⟩) R110069
theorem R40625 : Reach 40625 := rs (se 2 (by rfl) ⟨15234, by rfl⟩) R30469
theorem R40643 : Reach 40643 := rs (se 1 (by rfl) ⟨30482, by rfl⟩) R60965
theorem R40675 : Reach 40675 := rs (se 1 (by rfl) ⟨30506, by rfl⟩) R61013
theorem R204643 : Reach 204643 := rs (se 1 (by rfl) ⟨153482, by rfl⟩) R306965
theorem R40817 : Reach 40817 := rs (se 2 (by rfl) ⟨15306, by rfl⟩) R30613
theorem R40865 : Reach 40865 := rs (se 2 (by rfl) ⟨15324, by rfl⟩) R30649
theorem R40945 : Reach 40945 := rs (se 2 (by rfl) ⟨15354, by rfl⟩) R30709
theorem R40979 : Reach 40979 := rs (se 1 (by rfl) ⟨30734, by rfl⟩) R61469
theorem R73763 : Reach 73763 := rs (se 1 (by rfl) ⟨55322, by rfl⟩) R110645
theorem R41107 : Reach 41107 := rs (se 1 (by rfl) ⟨30830, by rfl⟩) R61661
theorem R41123 : Reach 41123 := rs (se 1 (by rfl) ⟨30842, by rfl⟩) R61685
theorem R41219 : Reach 41219 := rs (se 1 (by rfl) ⟨30914, by rfl⟩) R61829
theorem R41249 : Reach 41249 := rs (se 2 (by rfl) ⟨15468, by rfl⟩) R30937
theorem R41377 : Reach 41377 := rs (se 2 (by rfl) ⟨15516, by rfl⟩) R31033
theorem R41411 : Reach 41411 := rs (se 1 (by rfl) ⟨31058, by rfl⟩) R62117
theorem R139781 : Reach 139781 := rs (se 4 (by rfl) ⟨13104, by rfl⟩) R26209
theorem R41539 : Reach 41539 := rs (se 1 (by rfl) ⟨31154, by rfl⟩) R62309
theorem R41681 : Reach 41681 := rs (se 2 (by rfl) ⟨15630, by rfl⟩) R31261
theorem R74449 : Reach 74449 := rs (se 2 (by rfl) ⟨27918, by rfl⟩) R55837
theorem R303857 : Reach 303857 := rs (se 2 (by rfl) ⟨113946, by rfl⟩) R227893
theorem R41809 : Reach 41809 := rs (se 2 (by rfl) ⟨15678, by rfl⟩) R31357
theorem R369521 : Reach 369521 := rs (se 2 (by rfl) ⟨138570, by rfl⟩) R277141
theorem R140401 : Reach 140401 := rs (se 2 (by rfl) ⟨52650, by rfl⟩) R105301
theorem R42211 : Reach 42211 := rs (se 1 (by rfl) ⟨31658, by rfl⟩) R63317
theorem R42275 : Reach 42275 := rs (se 1 (by rfl) ⟨31706, by rfl⟩) R63413
theorem R42353 : Reach 42353 := rs (se 2 (by rfl) ⟨15882, by rfl⟩) R31765
theorem R42385 : Reach 42385 := rs (se 2 (by rfl) ⟨15894, by rfl⟩) R31789
theorem R42403 : Reach 42403 := rs (se 1 (by rfl) ⟨31802, by rfl⟩) R63605
theorem R42545 : Reach 42545 := rs (se 2 (by rfl) ⟨15954, by rfl⟩) R31909
theorem R42673 : Reach 42673 := rs (se 2 (by rfl) ⟨16002, by rfl⟩) R32005
theorem R141061 : Reach 141061 := rs (se 4 (by rfl) ⟨13224, by rfl⟩) R26449
theorem R75725 : Reach 75725 := rs (se 3 (by rfl) ⟨14198, by rfl⟩) R28397
theorem R337891 : Reach 337891 := rs (se 1 (by rfl) ⟨253418, by rfl⟩) R506837
theorem R75811 : Reach 75811 := rs (se 1 (by rfl) ⟨56858, by rfl⟩) R113717
theorem R43139 : Reach 43139 := rs (se 1 (by rfl) ⟨32354, by rfl⟩) R64709
theorem R75907 : Reach 75907 := rs (se 1 (by rfl) ⟨56930, by rfl⟩) R113861
theorem R75953 : Reach 75953 := rs (se 2 (by rfl) ⟨28482, by rfl⟩) R56965
theorem R43267 : Reach 43267 := rs (se 1 (by rfl) ⟨32450, by rfl⟩) R64901
theorem R76067 : Reach 76067 := rs (se 1 (by rfl) ⟨57050, by rfl⟩) R114101
theorem R43313 : Reach 43313 := rs (se 2 (by rfl) ⟨16242, by rfl⟩) R32485
theorem R43409 : Reach 43409 := rs (se 2 (by rfl) ⟨16278, by rfl⟩) R32557
theorem R469475 : Reach 469475 := rs (se 1 (by rfl) ⟨352106, by rfl⟩) R704213
theorem R76291 : Reach 76291 := rs (se 1 (by rfl) ⟨57218, by rfl⟩) R114437
theorem R43537 : Reach 43537 := rs (se 2 (by rfl) ⟨16326, by rfl⟩) R32653
theorem R404021 : Reach 404021 := rs (se 5 (by rfl) ⟨18938, by rfl⟩) R37877
theorem R207629 : Reach 207629 := rs (se 3 (by rfl) ⟨38930, by rfl⟩) R77861
theorem R44003 : Reach 44003 := rs (se 1 (by rfl) ⟨33002, by rfl⟩) R66005
theorem R109667 : Reach 109667 := rs (se 1 (by rfl) ⟨82250, by rfl⟩) R164501
theorem R44131 : Reach 44131 := rs (se 1 (by rfl) ⟨33098, by rfl⟩) R66197
theorem R109745 : Reach 109745 := rs (se 2 (by rfl) ⟨41154, by rfl⟩) R82309
theorem R109795 : Reach 109795 := rs (se 1 (by rfl) ⟨82346, by rfl⟩) R164693
theorem R77041 : Reach 77041 := rs (se 2 (by rfl) ⟨28890, by rfl⟩) R57781
theorem R44273 : Reach 44273 := rs (se 2 (by rfl) ⟨16602, by rfl⟩) R33205
theorem R240965 : Reach 240965 := rs (se 4 (by rfl) ⟨22590, by rfl⟩) R45181
theorem R44401 : Reach 44401 := rs (se 2 (by rfl) ⟨16650, by rfl⟩) R33301
theorem R143045 : Reach 143045 := rs (se 4 (by rfl) ⟨13410, by rfl⟩) R26821
theorem R44803 : Reach 44803 := rs (se 1 (by rfl) ⟨33602, by rfl⟩) R67205
theorem R44849 : Reach 44849 := rs (se 2 (by rfl) ⟨16818, by rfl⟩) R33637
theorem R44867 : Reach 44867 := rs (se 1 (by rfl) ⟨33650, by rfl⟩) R67301
theorem R110413 : Reach 110413 := rs (se 3 (by rfl) ⟨20702, by rfl⟩) R41405
theorem R44995 : Reach 44995 := rs (se 1 (by rfl) ⟨33746, by rfl⟩) R67493
theorem R45137 : Reach 45137 := rs (se 2 (by rfl) ⟨16926, by rfl⟩) R33853
theorem R45265 : Reach 45265 := rs (se 2 (by rfl) ⟨16974, by rfl⟩) R33949
theorem R307637 : Reach 307637 := rs (se 5 (by rfl) ⟨14420, by rfl⟩) R28841
theorem R45731 : Reach 45731 := rs (se 1 (by rfl) ⟨34298, by rfl⟩) R68597
theorem R45859 : Reach 45859 := rs (se 1 (by rfl) ⟨34394, by rfl⟩) R68789
theorem R144433 : Reach 144433 := rs (se 2 (by rfl) ⟨54162, by rfl⟩) R108325
theorem R144497 : Reach 144497 := rs (se 2 (by rfl) ⟨54186, by rfl⟩) R108373
theorem R177349 : Reach 177349 := rs (se 4 (by rfl) ⟨16626, by rfl⟩) R33253
theorem R46307 : Reach 46307 := rs (se 1 (by rfl) ⟨34730, by rfl⟩) R69461
theorem R144625 : Reach 144625 := rs (se 2 (by rfl) ⟨54234, by rfl⟩) R108469
theorem R79309 : Reach 79309 := rs (se 3 (by rfl) ⟨14870, by rfl⟩) R29741
theorem R46595 : Reach 46595 := rs (se 1 (by rfl) ⟨34946, by rfl⟩) R69893
theorem R112205 : Reach 112205 := rs (se 3 (by rfl) ⟨21038, by rfl⟩) R42077
theorem R79757 : Reach 79757 := rs (se 3 (by rfl) ⟨14954, by rfl⟩) R29909
theorem R79811 : Reach 79811 := rs (se 1 (by rfl) ⟨59858, by rfl⟩) R119717
theorem R538595 : Reach 538595 := rs (se 1 (by rfl) ⟨403946, by rfl⟩) R807893
theorem R80081 : Reach 80081 := rs (se 2 (by rfl) ⟨30030, by rfl⟩) R60061
theorem R47537 : Reach 47537 := rs (se 2 (by rfl) ⟨17826, by rfl⟩) R35653
theorem R47747 : Reach 47747 := rs (se 1 (by rfl) ⟨35810, by rfl⟩) R71621
theorem R80621 : Reach 80621 := rs (se 3 (by rfl) ⟨15116, by rfl⟩) R30233
theorem R80675 : Reach 80675 := rs (se 1 (by rfl) ⟨60506, by rfl⟩) R121013
theorem R244579 : Reach 244579 := rs (se 1 (by rfl) ⟨183434, by rfl⟩) R366869
theorem R80945 : Reach 80945 := rs (se 2 (by rfl) ⟨30354, by rfl⟩) R60709
theorem R48433 : Reach 48433 := rs (se 2 (by rfl) ⟨18162, by rfl⟩) R36325
theorem R146893 : Reach 146893 := rs (se 3 (by rfl) ⟨27542, by rfl⟩) R55085
theorem R48593 : Reach 48593 := rs (se 2 (by rfl) ⟨18222, by rfl⟩) R36445
theorem R81425 : Reach 81425 := rs (se 2 (by rfl) ⟨30534, by rfl⟩) R61069
theorem R81485 : Reach 81485 := rs (se 3 (by rfl) ⟨15278, by rfl⟩) R30557
theorem R81539 : Reach 81539 := rs (se 1 (by rfl) ⟨61154, by rfl⟩) R122309
theorem R48995 : Reach 48995 := rs (se 1 (by rfl) ⟨36746, by rfl⟩) R73493
theorem R81809 : Reach 81809 := rs (se 2 (by rfl) ⟨30678, by rfl⟩) R61357
theorem R114659 : Reach 114659 := rs (se 1 (by rfl) ⟨85994, by rfl⟩) R171989
theorem R115021 : Reach 115021 := rs (se 3 (by rfl) ⟨21566, by rfl⟩) R43133
theorem R82349 : Reach 82349 := rs (se 3 (by rfl) ⟨15440, by rfl⟩) R30881
theorem R82403 : Reach 82403 := rs (se 1 (by rfl) ⟨61802, by rfl⟩) R123605
theorem R49891 : Reach 49891 := rs (se 1 (by rfl) ⟨37418, by rfl⟩) R74837
theorem R82673 : Reach 82673 := rs (se 2 (by rfl) ⟨31002, by rfl⟩) R62005
theorem R50051 : Reach 50051 := rs (se 1 (by rfl) ⟨37538, by rfl⟩) R75077
theorem R83213 : Reach 83213 := rs (se 3 (by rfl) ⟨15602, by rfl⟩) R31205
theorem R83267 : Reach 83267 := rs (se 1 (by rfl) ⟨62450, by rfl⟩) R124901
theorem R181645 : Reach 181645 := rs (se 3 (by rfl) ⟨34058, by rfl⟩) R68117
theorem R148877 : Reach 148877 := rs (se 3 (by rfl) ⟨27914, by rfl⟩) R55829
theorem R83501 : Reach 83501 := rs (se 3 (by rfl) ⟨15656, by rfl⟩) R31313
theorem R83537 : Reach 83537 := rs (se 2 (by rfl) ⟨31326, by rfl⟩) R62653
theorem R51121 : Reach 51121 := rs (se 2 (by rfl) ⟨19170, by rfl⟩) R38341
theorem R84131 : Reach 84131 := rs (se 1 (by rfl) ⟨63098, by rfl⟩) R126197
theorem R182513 : Reach 182513 := rs (se 2 (by rfl) ⟨68442, by rfl⟩) R136885
theorem R149809 : Reach 149809 := rs (se 2 (by rfl) ⟨56178, by rfl⟩) R112357
theorem R84401 : Reach 84401 := rs (se 2 (by rfl) ⟨31650, by rfl⟩) R63301
theorem R215693 : Reach 215693 := rs (se 3 (by rfl) ⟨40442, by rfl⟩) R80885
theorem R84941 : Reach 84941 := rs (se 3 (by rfl) ⟨15926, by rfl⟩) R31853
theorem R117773 : Reach 117773 := rs (se 3 (by rfl) ⟨22082, by rfl⟩) R44165
theorem R85283 : Reach 85283 := rs (se 1 (by rfl) ⟨63962, by rfl⟩) R127925
theorem R52625 : Reach 52625 := rs (se 2 (by rfl) ⟨19734, by rfl⟩) R39469
theorem R52643 : Reach 52643 := rs (se 1 (by rfl) ⟨39482, by rfl⟩) R78965
theorem R151025 : Reach 151025 := rs (se 2 (by rfl) ⟨56634, by rfl⟩) R113269
theorem R151109 : Reach 151109 := rs (se 4 (by rfl) ⟨14166, by rfl⟩) R28333
theorem R1199843 : Reach 1199843 := rs (se 1 (by rfl) ⟨899882, by rfl⟩) R1799765
theorem R151267 : Reach 151267 := rs (se 1 (by rfl) ⟨113450, by rfl⟩) R226901
theorem R53009 : Reach 53009 := rs (se 2 (by rfl) ⟨19878, by rfl⟩) R39757
theorem R53027 : Reach 53027 := rs (se 1 (by rfl) ⟨39770, by rfl⟩) R79541
theorem R85859 : Reach 85859 := rs (se 1 (by rfl) ⟨64394, by rfl⟩) R128789
theorem R53297 : Reach 53297 := rs (se 2 (by rfl) ⟨19986, by rfl⟩) R39973
theorem R53315 : Reach 53315 := rs (se 1 (by rfl) ⟨39986, by rfl⟩) R79973
theorem R86129 : Reach 86129 := rs (se 2 (by rfl) ⟨32298, by rfl⟩) R64597
theorem R282851 : Reach 282851 := rs (se 1 (by rfl) ⟨212138, by rfl⟩) R424277
theorem R151793 : Reach 151793 := rs (se 2 (by rfl) ⟨56922, by rfl⟩) R113845
theorem R53585 : Reach 53585 := rs (se 2 (by rfl) ⟨20094, by rfl⟩) R40189
theorem R53603 : Reach 53603 := rs (se 1 (by rfl) ⟨40202, by rfl⟩) R80405
theorem R53873 : Reach 53873 := rs (se 2 (by rfl) ⟨20202, by rfl⟩) R40405
theorem R53891 : Reach 53891 := rs (se 1 (by rfl) ⟨40418, by rfl⟩) R80837
theorem R86669 : Reach 86669 := rs (se 3 (by rfl) ⟨16250, by rfl⟩) R32501
theorem R54161 : Reach 54161 := rs (se 2 (by rfl) ⟨20310, by rfl⟩) R40621
theorem R54179 : Reach 54179 := rs (se 1 (by rfl) ⟨40634, by rfl⟩) R81269
theorem R54449 : Reach 54449 := rs (se 2 (by rfl) ⟨20418, by rfl⟩) R40837
theorem R54467 : Reach 54467 := rs (se 1 (by rfl) ⟨40850, by rfl⟩) R81701
theorem R54641 : Reach 54641 := rs (se 2 (by rfl) ⟨20490, by rfl⟩) R40981
theorem R87473 : Reach 87473 := rs (se 2 (by rfl) ⟨32802, by rfl⟩) R65605
theorem R54737 : Reach 54737 := rs (se 2 (by rfl) ⟨20526, by rfl⟩) R41053
theorem R54755 : Reach 54755 := rs (se 1 (by rfl) ⟨41066, by rfl⟩) R82133
theorem R87587 : Reach 87587 := rs (se 1 (by rfl) ⟨65690, by rfl⟩) R131381
theorem R54883 : Reach 54883 := rs (se 1 (by rfl) ⟨41162, by rfl⟩) R82325
theorem R153251 : Reach 153251 := rs (se 1 (by rfl) ⟨114938, by rfl⟩) R229877
theorem R218821 : Reach 218821 := rs (se 4 (by rfl) ⟨20514, by rfl⟩) R41029
theorem R55025 : Reach 55025 := rs (se 2 (by rfl) ⟨20634, by rfl⟩) R41269
theorem R55043 : Reach 55043 := rs (se 1 (by rfl) ⟨41282, by rfl⟩) R82565
theorem R87857 : Reach 87857 := rs (se 2 (by rfl) ⟨32946, by rfl⟩) R65893
theorem R251747 : Reach 251747 := rs (se 1 (by rfl) ⟨188810, by rfl⟩) R377621
theorem R120689 : Reach 120689 := rs (se 2 (by rfl) ⟨45258, by rfl⟩) R90517
theorem R55171 : Reach 55171 := rs (se 1 (by rfl) ⟨41378, by rfl⟩) R82757
theorem R120781 : Reach 120781 := rs (se 3 (by rfl) ⟨22646, by rfl⟩) R45293
theorem R55313 : Reach 55313 := rs (se 2 (by rfl) ⟨20742, by rfl⟩) R41485
theorem R55331 : Reach 55331 := rs (se 1 (by rfl) ⟨41498, by rfl⟩) R82997
theorem R317621 : Reach 317621 := rs (se 5 (by rfl) ⟨14888, by rfl⟩) R29777
theorem R252173 : Reach 252173 := rs (se 3 (by rfl) ⟨47282, by rfl⟩) R94565
theorem R55601 : Reach 55601 := rs (se 2 (by rfl) ⟨20850, by rfl⟩) R41701
theorem R55619 : Reach 55619 := rs (se 1 (by rfl) ⟨41714, by rfl⟩) R83429
theorem R88397 : Reach 88397 := rs (se 3 (by rfl) ⟨16574, by rfl⟩) R33149
theorem R318005 : Reach 318005 := rs (se 5 (by rfl) ⟨14906, by rfl⟩) R29813
theorem R55889 : Reach 55889 := rs (se 2 (by rfl) ⟨20958, by rfl⟩) R41917
theorem R55907 : Reach 55907 := rs (se 1 (by rfl) ⟨41930, by rfl⟩) R83861
theorem R56177 : Reach 56177 := rs (se 2 (by rfl) ⟨21066, by rfl⟩) R42133
theorem R56195 : Reach 56195 := rs (se 1 (by rfl) ⟨42146, by rfl⟩) R84293
theorem R23507 : Reach 23507 := rs (se 1 (by rfl) ⟨17630, by rfl⟩) R35261
theorem R23523 : Reach 23523 := rs (se 1 (by rfl) ⟨17642, by rfl⟩) R35285
theorem R23539 : Reach 23539 := rs (se 1 (by rfl) ⟨17654, by rfl⟩) R35309
theorem R23555 : Reach 23555 := rs (se 1 (by rfl) ⟨17666, by rfl⟩) R35333
theorem R23571 : Reach 23571 := rs (se 1 (by rfl) ⟨17678, by rfl⟩) R35357
theorem R23587 : Reach 23587 := rs (se 1 (by rfl) ⟨17690, by rfl⟩) R35381
theorem R23603 : Reach 23603 := rs (se 1 (by rfl) ⟨17702, by rfl⟩) R35405
theorem R23619 : Reach 23619 := rs (se 1 (by rfl) ⟨17714, by rfl⟩) R35429
theorem R23635 : Reach 23635 := rs (se 1 (by rfl) ⟨17726, by rfl⟩) R35453
theorem R23651 : Reach 23651 := rs (se 1 (by rfl) ⟨17738, by rfl⟩) R35477
theorem R23667 : Reach 23667 := rs (se 1 (by rfl) ⟨17750, by rfl⟩) R35501
theorem R23683 : Reach 23683 := rs (se 1 (by rfl) ⟨17762, by rfl⟩) R35525
theorem R56465 : Reach 56465 := rs (se 2 (by rfl) ⟨21174, by rfl⟩) R42349
theorem R23699 : Reach 23699 := rs (se 1 (by rfl) ⟨17774, by rfl⟩) R35549
theorem R23715 : Reach 23715 := rs (se 1 (by rfl) ⟨17786, by rfl⟩) R35573
theorem R56483 : Reach 56483 := rs (se 1 (by rfl) ⟨42362, by rfl⟩) R84725
theorem R23731 : Reach 23731 := rs (se 1 (by rfl) ⟨17798, by rfl⟩) R35597
theorem R23747 : Reach 23747 := rs (se 1 (by rfl) ⟨17810, by rfl⟩) R35621
theorem R23763 : Reach 23763 := rs (se 1 (by rfl) ⟨17822, by rfl⟩) R35645
theorem R23779 : Reach 23779 := rs (se 1 (by rfl) ⟨17834, by rfl⟩) R35669
theorem R89315 : Reach 89315 := rs (se 1 (by rfl) ⟨66986, by rfl⟩) R133973
theorem R23795 : Reach 23795 := rs (se 1 (by rfl) ⟨17846, by rfl⟩) R35693
theorem R23811 : Reach 23811 := rs (se 1 (by rfl) ⟨17858, by rfl⟩) R35717
theorem R23827 : Reach 23827 := rs (se 1 (by rfl) ⟨17870, by rfl⟩) R35741
theorem R23843 : Reach 23843 := rs (se 1 (by rfl) ⟨17882, by rfl⟩) R35765
theorem R122147 : Reach 122147 := rs (se 1 (by rfl) ⟨91610, by rfl⟩) R183221
theorem R23859 : Reach 23859 := rs (se 1 (by rfl) ⟨17894, by rfl⟩) R35789
theorem R23875 : Reach 23875 := rs (se 1 (by rfl) ⟨17906, by rfl⟩) R35813
theorem R56657 : Reach 56657 := rs (se 2 (by rfl) ⟨21246, by rfl⟩) R42493
theorem R23891 : Reach 23891 := rs (se 1 (by rfl) ⟨17918, by rfl⟩) R35837
theorem R23907 : Reach 23907 := rs (se 1 (by rfl) ⟨17930, by rfl⟩) R35861
theorem R56675 : Reach 56675 := rs (se 1 (by rfl) ⟨42506, by rfl⟩) R85013
theorem R23923 : Reach 23923 := rs (se 1 (by rfl) ⟨17942, by rfl⟩) R35885
theorem R23939 : Reach 23939 := rs (se 1 (by rfl) ⟨17954, by rfl⟩) R35909
theorem R23955 : Reach 23955 := rs (se 1 (by rfl) ⟨17966, by rfl⟩) R35933
theorem R23971 : Reach 23971 := rs (se 1 (by rfl) ⟨17978, by rfl⟩) R35957
theorem R56753 : Reach 56753 := rs (se 2 (by rfl) ⟨21282, by rfl⟩) R42565
theorem R23987 : Reach 23987 := rs (se 1 (by rfl) ⟨17990, by rfl⟩) R35981
theorem R24003 : Reach 24003 := rs (se 1 (by rfl) ⟨18002, by rfl⟩) R36005
theorem R56771 : Reach 56771 := rs (se 1 (by rfl) ⟨42578, by rfl⟩) R85157
theorem R253381 : Reach 253381 := rs (se 4 (by rfl) ⟨23754, by rfl⟩) R47509
theorem R24019 : Reach 24019 := rs (se 1 (by rfl) ⟨18014, by rfl⟩) R36029
theorem R24035 : Reach 24035 := rs (se 1 (by rfl) ⟨18026, by rfl⟩) R36053
theorem R89585 : Reach 89585 := rs (se 2 (by rfl) ⟨33594, by rfl⟩) R67189
theorem R24051 : Reach 24051 := rs (se 1 (by rfl) ⟨18038, by rfl⟩) R36077
theorem R24067 : Reach 24067 := rs (se 1 (by rfl) ⟨18050, by rfl⟩) R36101
theorem R24083 : Reach 24083 := rs (se 1 (by rfl) ⟨18062, by rfl⟩) R36125
theorem R24099 : Reach 24099 := rs (se 1 (by rfl) ⟨18074, by rfl⟩) R36149
theorem R24115 : Reach 24115 := rs (se 1 (by rfl) ⟨18086, by rfl⟩) R36173
theorem R24131 : Reach 24131 := rs (se 1 (by rfl) ⟨18098, by rfl⟩) R36197
theorem R24147 : Reach 24147 := rs (se 1 (by rfl) ⟨18110, by rfl⟩) R36221
theorem R24163 : Reach 24163 := rs (se 1 (by rfl) ⟨18122, by rfl⟩) R36245
theorem R24179 : Reach 24179 := rs (se 1 (by rfl) ⟨18134, by rfl⟩) R36269
theorem R24195 : Reach 24195 := rs (se 1 (by rfl) ⟨18146, by rfl⟩) R36293
theorem R24211 : Reach 24211 := rs (se 1 (by rfl) ⟨18158, by rfl⟩) R36317
theorem R24227 : Reach 24227 := rs (se 1 (by rfl) ⟨18170, by rfl⟩) R36341
theorem R24243 : Reach 24243 := rs (se 1 (by rfl) ⟨18182, by rfl⟩) R36365
theorem R24259 : Reach 24259 := rs (se 1 (by rfl) ⟨18194, by rfl⟩) R36389
theorem R57041 : Reach 57041 := rs (se 2 (by rfl) ⟨21390, by rfl⟩) R42781
theorem R24275 : Reach 24275 := rs (se 1 (by rfl) ⟨18206, by rfl⟩) R36413
theorem R24291 : Reach 24291 := rs (se 1 (by rfl) ⟨18218, by rfl⟩) R36437
theorem R57059 : Reach 57059 := rs (se 1 (by rfl) ⟨42794, by rfl⟩) R85589
theorem R57073 : Reach 57073 := rs (se 2 (by rfl) ⟨21402, by rfl⟩) R42805
theorem R24307 : Reach 24307 := rs (se 1 (by rfl) ⟨18230, by rfl⟩) R36461
theorem R24323 : Reach 24323 := rs (se 1 (by rfl) ⟨18242, by rfl⟩) R36485
theorem R24339 : Reach 24339 := rs (se 1 (by rfl) ⟨18254, by rfl⟩) R36509
theorem R24355 : Reach 24355 := rs (se 1 (by rfl) ⟨18266, by rfl⟩) R36533
theorem R24371 : Reach 24371 := rs (se 1 (by rfl) ⟨18278, by rfl⟩) R36557
theorem R24387 : Reach 24387 := rs (se 1 (by rfl) ⟨18290, by rfl⟩) R36581
theorem R24403 : Reach 24403 := rs (se 1 (by rfl) ⟨18302, by rfl⟩) R36605
theorem R24419 : Reach 24419 := rs (se 1 (by rfl) ⟨18314, by rfl⟩) R36629
theorem R24435 : Reach 24435 := rs (se 1 (by rfl) ⟨18326, by rfl⟩) R36653
theorem R24451 : Reach 24451 := rs (se 1 (by rfl) ⟨18338, by rfl⟩) R36677
theorem R24467 : Reach 24467 := rs (se 1 (by rfl) ⟨18350, by rfl⟩) R36701
theorem R24483 : Reach 24483 := rs (se 1 (by rfl) ⟨18362, by rfl⟩) R36725
theorem R24499 : Reach 24499 := rs (se 1 (by rfl) ⟨18374, by rfl⟩) R36749
theorem R24515 : Reach 24515 := rs (se 1 (by rfl) ⟨18386, by rfl⟩) R36773
theorem R24531 : Reach 24531 := rs (se 1 (by rfl) ⟨18398, by rfl⟩) R36797
theorem R24547 : Reach 24547 := rs (se 1 (by rfl) ⟨18410, by rfl⟩) R36821
theorem R57329 : Reach 57329 := rs (se 2 (by rfl) ⟨21498, by rfl⟩) R42997
theorem R24563 : Reach 24563 := rs (se 1 (by rfl) ⟨18422, by rfl⟩) R36845
theorem R24579 : Reach 24579 := rs (se 1 (by rfl) ⟨18434, by rfl⟩) R36869
theorem R57347 : Reach 57347 := rs (se 1 (by rfl) ⟨43010, by rfl⟩) R86021
theorem R90125 : Reach 90125 := rs (se 3 (by rfl) ⟨16898, by rfl⟩) R33797
theorem R24595 : Reach 24595 := rs (se 1 (by rfl) ⟨18446, by rfl⟩) R36893
theorem R24611 : Reach 24611 := rs (se 1 (by rfl) ⟨18458, by rfl⟩) R36917
theorem R24627 : Reach 24627 := rs (se 1 (by rfl) ⟨18470, by rfl⟩) R36941
theorem R24643 : Reach 24643 := rs (se 1 (by rfl) ⟨18482, by rfl⟩) R36965
theorem R122957 : Reach 122957 := rs (se 3 (by rfl) ⟨23054, by rfl⟩) R46109
theorem R24659 : Reach 24659 := rs (se 1 (by rfl) ⟨18494, by rfl⟩) R36989
theorem R24675 : Reach 24675 := rs (se 1 (by rfl) ⟨18506, by rfl⟩) R37013
theorem R24691 : Reach 24691 := rs (se 1 (by rfl) ⟨18518, by rfl⟩) R37037
theorem R24707 : Reach 24707 := rs (se 1 (by rfl) ⟨18530, by rfl⟩) R37061
theorem R24723 : Reach 24723 := rs (se 1 (by rfl) ⟨18542, by rfl⟩) R37085
theorem R24739 : Reach 24739 := rs (se 1 (by rfl) ⟨18554, by rfl⟩) R37109
theorem R24755 : Reach 24755 := rs (se 1 (by rfl) ⟨18566, by rfl⟩) R37133
theorem R24771 : Reach 24771 := rs (se 1 (by rfl) ⟨18578, by rfl⟩) R37157
theorem R24787 : Reach 24787 := rs (se 1 (by rfl) ⟨18590, by rfl⟩) R37181
theorem R24803 : Reach 24803 := rs (se 1 (by rfl) ⟨18602, by rfl⟩) R37205
theorem R24819 : Reach 24819 := rs (se 1 (by rfl) ⟨18614, by rfl⟩) R37229
theorem R24835 : Reach 24835 := rs (se 1 (by rfl) ⟨18626, by rfl⟩) R37253
theorem R57617 : Reach 57617 := rs (se 2 (by rfl) ⟨21606, by rfl⟩) R43213
theorem R24851 : Reach 24851 := rs (se 1 (by rfl) ⟨18638, by rfl⟩) R37277
theorem R24867 : Reach 24867 := rs (se 1 (by rfl) ⟨18650, by rfl⟩) R37301
theorem R57635 : Reach 57635 := rs (se 1 (by rfl) ⟨43226, by rfl⟩) R86453
theorem R24883 : Reach 24883 := rs (se 1 (by rfl) ⟨18662, by rfl⟩) R37325
theorem R24899 : Reach 24899 := rs (se 1 (by rfl) ⟨18674, by rfl⟩) R37349
theorem R24915 : Reach 24915 := rs (se 1 (by rfl) ⟨18686, by rfl⟩) R37373
theorem R24931 : Reach 24931 := rs (se 1 (by rfl) ⟨18698, by rfl⟩) R37397
theorem R24947 : Reach 24947 := rs (se 1 (by rfl) ⟨18710, by rfl⟩) R37421
theorem R24963 : Reach 24963 := rs (se 1 (by rfl) ⟨18722, by rfl⟩) R37445
theorem R24979 : Reach 24979 := rs (se 1 (by rfl) ⟨18734, by rfl⟩) R37469
theorem R24995 : Reach 24995 := rs (se 1 (by rfl) ⟨18746, by rfl⟩) R37493
theorem R25011 : Reach 25011 := rs (se 1 (by rfl) ⟨18758, by rfl⟩) R37517
theorem R25027 : Reach 25027 := rs (se 1 (by rfl) ⟨18770, by rfl⟩) R37541
theorem R25043 : Reach 25043 := rs (se 1 (by rfl) ⟨18782, by rfl⟩) R37565
theorem R25059 : Reach 25059 := rs (se 1 (by rfl) ⟨18794, by rfl⟩) R37589
theorem R25075 : Reach 25075 := rs (se 1 (by rfl) ⟨18806, by rfl⟩) R37613
theorem R25091 : Reach 25091 := rs (se 1 (by rfl) ⟨18818, by rfl⟩) R37637
theorem R25107 : Reach 25107 := rs (se 1 (by rfl) ⟨18830, by rfl⟩) R37661
theorem R25123 : Reach 25123 := rs (se 1 (by rfl) ⟨18842, by rfl⟩) R37685
theorem R57905 : Reach 57905 := rs (se 2 (by rfl) ⟨21714, by rfl⟩) R43429
theorem R25139 : Reach 25139 := rs (se 1 (by rfl) ⟨18854, by rfl⟩) R37709
theorem R25155 : Reach 25155 := rs (se 1 (by rfl) ⟨18866, by rfl⟩) R37733
theorem R57923 : Reach 57923 := rs (se 1 (by rfl) ⟨43442, by rfl⟩) R86885
theorem R25171 : Reach 25171 := rs (se 1 (by rfl) ⟨18878, by rfl⟩) R37757
theorem R25187 : Reach 25187 := rs (se 1 (by rfl) ⟨18890, by rfl⟩) R37781
theorem R25203 : Reach 25203 := rs (se 1 (by rfl) ⟨18902, by rfl⟩) R37805
theorem R25219 : Reach 25219 := rs (se 1 (by rfl) ⟨18914, by rfl⟩) R37829
theorem R25235 : Reach 25235 := rs (se 1 (by rfl) ⟨18926, by rfl⟩) R37853
theorem R25251 : Reach 25251 := rs (se 1 (by rfl) ⟨18938, by rfl⟩) R37877
theorem R25267 : Reach 25267 := rs (se 1 (by rfl) ⟨18950, by rfl⟩) R37901
theorem R25283 : Reach 25283 := rs (se 1 (by rfl) ⟨18962, by rfl⟩) R37925
theorem R25299 : Reach 25299 := rs (se 1 (by rfl) ⟨18974, by rfl⟩) R37949
theorem R25315 : Reach 25315 := rs (se 1 (by rfl) ⟨18986, by rfl⟩) R37973
theorem R25331 : Reach 25331 := rs (se 1 (by rfl) ⟨18998, by rfl⟩) R37997
theorem R25347 : Reach 25347 := rs (se 1 (by rfl) ⟨19010, by rfl⟩) R38021
theorem R25363 : Reach 25363 := rs (se 1 (by rfl) ⟨19022, by rfl⟩) R38045
theorem R25379 : Reach 25379 := rs (se 1 (by rfl) ⟨19034, by rfl⟩) R38069
theorem R25395 : Reach 25395 := rs (se 1 (by rfl) ⟨19046, by rfl⟩) R38093
theorem R25411 : Reach 25411 := rs (se 1 (by rfl) ⟨19058, by rfl⟩) R38117
theorem R58193 : Reach 58193 := rs (se 2 (by rfl) ⟨21822, by rfl⟩) R43645
theorem R25427 : Reach 25427 := rs (se 1 (by rfl) ⟨19070, by rfl⟩) R38141
theorem R25443 : Reach 25443 := rs (se 1 (by rfl) ⟨19082, by rfl⟩) R38165
theorem R58211 : Reach 58211 := rs (se 1 (by rfl) ⟨43658, by rfl⟩) R87317
theorem R25459 : Reach 25459 := rs (se 1 (by rfl) ⟨19094, by rfl⟩) R38189
theorem R25475 : Reach 25475 := rs (se 1 (by rfl) ⟨19106, by rfl⟩) R38213
theorem R25491 : Reach 25491 := rs (se 1 (by rfl) ⟨19118, by rfl⟩) R38237
theorem R25507 : Reach 25507 := rs (se 1 (by rfl) ⟨19130, by rfl⟩) R38261
theorem R91043 : Reach 91043 := rs (se 1 (by rfl) ⟨68282, by rfl⟩) R136565
theorem R25523 : Reach 25523 := rs (se 1 (by rfl) ⟨19142, by rfl⟩) R38285
theorem R25539 : Reach 25539 := rs (se 1 (by rfl) ⟨19154, by rfl⟩) R38309
theorem R25555 : Reach 25555 := rs (se 1 (by rfl) ⟨19166, by rfl⟩) R38333
theorem R25571 : Reach 25571 := rs (se 1 (by rfl) ⟨19178, by rfl⟩) R38357
theorem R25587 : Reach 25587 := rs (se 1 (by rfl) ⟨19190, by rfl⟩) R38381
theorem R25603 : Reach 25603 := rs (se 1 (by rfl) ⟨19202, by rfl⟩) R38405
theorem R25619 : Reach 25619 := rs (se 1 (by rfl) ⟨19214, by rfl⟩) R38429
theorem R25635 : Reach 25635 := rs (se 1 (by rfl) ⟨19226, by rfl⟩) R38453
theorem R25651 : Reach 25651 := rs (se 1 (by rfl) ⟨19238, by rfl⟩) R38477
theorem R25667 : Reach 25667 := rs (se 1 (by rfl) ⟨19250, by rfl⟩) R38501
theorem R25683 : Reach 25683 := rs (se 1 (by rfl) ⟨19262, by rfl⟩) R38525
theorem R189539 : Reach 189539 := rs (se 1 (by rfl) ⟨142154, by rfl⟩) R284309
theorem R25699 : Reach 25699 := rs (se 1 (by rfl) ⟨19274, by rfl⟩) R38549
theorem R58481 : Reach 58481 := rs (se 2 (by rfl) ⟨21930, by rfl⟩) R43861
theorem R25715 : Reach 25715 := rs (se 1 (by rfl) ⟨19286, by rfl⟩) R38573
theorem R25731 : Reach 25731 := rs (se 1 (by rfl) ⟨19298, by rfl⟩) R38597
theorem R58499 : Reach 58499 := rs (se 1 (by rfl) ⟨43874, by rfl⟩) R87749
theorem R91277 : Reach 91277 := rs (se 3 (by rfl) ⟨17114, by rfl⟩) R34229
theorem R25747 : Reach 25747 := rs (se 1 (by rfl) ⟨19310, by rfl⟩) R38621
theorem R25763 : Reach 25763 := rs (se 1 (by rfl) ⟨19322, by rfl⟩) R38645
theorem R91313 : Reach 91313 := rs (se 2 (by rfl) ⟨34242, by rfl⟩) R68485
theorem R25779 : Reach 25779 := rs (se 1 (by rfl) ⟨19334, by rfl⟩) R38669
theorem R25795 : Reach 25795 := rs (se 1 (by rfl) ⟨19346, by rfl⟩) R38693
theorem R25811 : Reach 25811 := rs (se 1 (by rfl) ⟨19358, by rfl⟩) R38717
theorem R25827 : Reach 25827 := rs (se 1 (by rfl) ⟨19370, by rfl⟩) R38741
theorem R124145 : Reach 124145 := rs (se 2 (by rfl) ⟨46554, by rfl⟩) R93109
theorem R25843 : Reach 25843 := rs (se 1 (by rfl) ⟨19382, by rfl⟩) R38765
theorem R25859 : Reach 25859 := rs (se 1 (by rfl) ⟨19394, by rfl⟩) R38789
theorem R25875 : Reach 25875 := rs (se 1 (by rfl) ⟨19406, by rfl⟩) R38813
theorem R25891 : Reach 25891 := rs (se 1 (by rfl) ⟨19418, by rfl⟩) R38837
theorem R25907 : Reach 25907 := rs (se 1 (by rfl) ⟨19430, by rfl⟩) R38861
theorem R25923 : Reach 25923 := rs (se 1 (by rfl) ⟨19442, by rfl⟩) R38885
theorem R25939 : Reach 25939 := rs (se 1 (by rfl) ⟨19454, by rfl⟩) R38909
theorem R25955 : Reach 25955 := rs (se 1 (by rfl) ⟨19466, by rfl⟩) R38933
theorem R25971 : Reach 25971 := rs (se 1 (by rfl) ⟨19478, by rfl⟩) R38957
theorem R25987 : Reach 25987 := rs (se 1 (by rfl) ⟨19490, by rfl⟩) R38981
theorem R58769 : Reach 58769 := rs (se 2 (by rfl) ⟨22038, by rfl⟩) R44077
theorem R26003 : Reach 26003 := rs (se 1 (by rfl) ⟨19502, by rfl⟩) R39005
theorem R26019 : Reach 26019 := rs (se 1 (by rfl) ⟨19514, by rfl⟩) R39029
theorem R58787 : Reach 58787 := rs (se 1 (by rfl) ⟨44090, by rfl⟩) R88181
theorem R26035 : Reach 26035 := rs (se 1 (by rfl) ⟨19526, by rfl⟩) R39053
theorem R58819 : Reach 58819 := rs (se 1 (by rfl) ⟨44114, by rfl⟩) R88229
theorem R26051 : Reach 26051 := rs (se 1 (by rfl) ⟨19538, by rfl⟩) R39077
theorem R26067 : Reach 26067 := rs (se 1 (by rfl) ⟨19550, by rfl⟩) R39101
theorem R26083 : Reach 26083 := rs (se 1 (by rfl) ⟨19562, by rfl⟩) R39125
theorem R26099 : Reach 26099 := rs (se 1 (by rfl) ⟨19574, by rfl⟩) R39149
theorem R26115 : Reach 26115 := rs (se 1 (by rfl) ⟨19586, by rfl⟩) R39173
theorem R26131 : Reach 26131 := rs (se 1 (by rfl) ⟨19598, by rfl⟩) R39197
theorem R26147 : Reach 26147 := rs (se 1 (by rfl) ⟨19610, by rfl⟩) R39221
theorem R26163 : Reach 26163 := rs (se 1 (by rfl) ⟨19622, by rfl⟩) R39245
theorem R26179 : Reach 26179 := rs (se 1 (by rfl) ⟨19634, by rfl⟩) R39269
theorem R26195 : Reach 26195 := rs (se 1 (by rfl) ⟨19646, by rfl⟩) R39293
theorem R26211 : Reach 26211 := rs (se 1 (by rfl) ⟨19658, by rfl⟩) R39317
theorem R26227 : Reach 26227 := rs (se 1 (by rfl) ⟨19670, by rfl⟩) R39341
theorem R26243 : Reach 26243 := rs (se 1 (by rfl) ⟨19682, by rfl⟩) R39365
theorem R26259 : Reach 26259 := rs (se 1 (by rfl) ⟨19694, by rfl⟩) R39389
theorem R26275 : Reach 26275 := rs (se 1 (by rfl) ⟨19706, by rfl⟩) R39413
theorem R59057 : Reach 59057 := rs (se 2 (by rfl) ⟨22146, by rfl⟩) R44293
theorem R26291 : Reach 26291 := rs (se 1 (by rfl) ⟨19718, by rfl⟩) R39437
theorem R59075 : Reach 59075 := rs (se 1 (by rfl) ⟨44306, by rfl⟩) R88613
theorem R26307 : Reach 26307 := rs (se 1 (by rfl) ⟨19730, by rfl⟩) R39461
theorem R26323 : Reach 26323 := rs (se 1 (by rfl) ⟨19742, by rfl⟩) R39485
theorem R26339 : Reach 26339 := rs (se 1 (by rfl) ⟨19754, by rfl⟩) R39509
theorem R26355 : Reach 26355 := rs (se 1 (by rfl) ⟨19766, by rfl⟩) R39533
theorem R26371 : Reach 26371 := rs (se 1 (by rfl) ⟨19778, by rfl⟩) R39557
theorem R26387 : Reach 26387 := rs (se 1 (by rfl) ⟨19790, by rfl⟩) R39581
theorem R26403 : Reach 26403 := rs (se 1 (by rfl) ⟨19802, by rfl⟩) R39605
theorem R26419 : Reach 26419 := rs (se 1 (by rfl) ⟨19814, by rfl⟩) R39629
theorem R26435 : Reach 26435 := rs (se 1 (by rfl) ⟨19826, by rfl⟩) R39653
theorem R26451 : Reach 26451 := rs (se 1 (by rfl) ⟨19838, by rfl⟩) R39677
theorem R26467 : Reach 26467 := rs (se 1 (by rfl) ⟨19850, by rfl⟩) R39701
theorem R26483 : Reach 26483 := rs (se 1 (by rfl) ⟨19862, by rfl⟩) R39725
theorem R26499 : Reach 26499 := rs (se 1 (by rfl) ⟨19874, by rfl⟩) R39749
theorem R26515 : Reach 26515 := rs (se 1 (by rfl) ⟨19886, by rfl⟩) R39773
theorem R26531 : Reach 26531 := rs (se 1 (by rfl) ⟨19898, by rfl⟩) R39797
theorem R26547 : Reach 26547 := rs (se 1 (by rfl) ⟨19910, by rfl⟩) R39821
theorem R26563 : Reach 26563 := rs (se 1 (by rfl) ⟨19922, by rfl⟩) R39845
theorem R59345 : Reach 59345 := rs (se 2 (by rfl) ⟨22254, by rfl⟩) R44509
theorem R26579 : Reach 26579 := rs (se 1 (by rfl) ⟨19934, by rfl⟩) R39869
theorem R59363 : Reach 59363 := rs (se 1 (by rfl) ⟨44522, by rfl⟩) R89045
theorem R26595 : Reach 26595 := rs (se 1 (by rfl) ⟨19946, by rfl⟩) R39893
theorem R26611 : Reach 26611 := rs (se 1 (by rfl) ⟨19958, by rfl⟩) R39917
theorem R26627 : Reach 26627 := rs (se 1 (by rfl) ⟨19970, by rfl⟩) R39941
theorem R26643 : Reach 26643 := rs (se 1 (by rfl) ⟨19982, by rfl⟩) R39965
theorem R26659 : Reach 26659 := rs (se 1 (by rfl) ⟨19994, by rfl⟩) R39989
theorem R26675 : Reach 26675 := rs (se 1 (by rfl) ⟨20006, by rfl⟩) R40013
theorem R26691 : Reach 26691 := rs (se 1 (by rfl) ⟨20018, by rfl⟩) R40037
theorem R26707 : Reach 26707 := rs (se 1 (by rfl) ⟨20030, by rfl⟩) R40061
theorem R26723 : Reach 26723 := rs (se 1 (by rfl) ⟨20042, by rfl⟩) R40085
theorem R26739 : Reach 26739 := rs (se 1 (by rfl) ⟨20054, by rfl⟩) R40109
theorem R26755 : Reach 26755 := rs (se 1 (by rfl) ⟨20066, by rfl⟩) R40133
theorem R26771 : Reach 26771 := rs (se 1 (by rfl) ⟨20078, by rfl⟩) R40157
theorem R59555 : Reach 59555 := rs (se 1 (by rfl) ⟨44666, by rfl⟩) R89333
theorem R26787 : Reach 26787 := rs (se 1 (by rfl) ⟨20090, by rfl⟩) R40181
theorem R26803 : Reach 26803 := rs (se 1 (by rfl) ⟨20102, by rfl⟩) R40205
theorem R26819 : Reach 26819 := rs (se 1 (by rfl) ⟨20114, by rfl⟩) R40229
theorem R26835 : Reach 26835 := rs (se 1 (by rfl) ⟨20126, by rfl⟩) R40253
theorem R26851 : Reach 26851 := rs (se 1 (by rfl) ⟨20138, by rfl⟩) R40277
theorem R59633 : Reach 59633 := rs (se 2 (by rfl) ⟨22362, by rfl⟩) R44725
theorem R26867 : Reach 26867 := rs (se 1 (by rfl) ⟨20150, by rfl⟩) R40301
theorem R59651 : Reach 59651 := rs (se 1 (by rfl) ⟨44738, by rfl⟩) R89477
theorem R26883 : Reach 26883 := rs (se 1 (by rfl) ⟨20162, by rfl⟩) R40325
theorem R26899 : Reach 26899 := rs (se 1 (by rfl) ⟨20174, by rfl⟩) R40349
theorem R26915 : Reach 26915 := rs (se 1 (by rfl) ⟨20186, by rfl⟩) R40373
theorem R26931 : Reach 26931 := rs (se 1 (by rfl) ⟨20198, by rfl⟩) R40397
theorem R26947 : Reach 26947 := rs (se 1 (by rfl) ⟨20210, by rfl⟩) R40421
theorem R26963 : Reach 26963 := rs (se 1 (by rfl) ⟨20222, by rfl⟩) R40445
theorem R26979 : Reach 26979 := rs (se 1 (by rfl) ⟨20234, by rfl⟩) R40469
theorem R26995 : Reach 26995 := rs (se 1 (by rfl) ⟨20246, by rfl⟩) R40493
theorem R27011 : Reach 27011 := rs (se 1 (by rfl) ⟨20258, by rfl⟩) R40517
theorem R27027 : Reach 27027 := rs (se 1 (by rfl) ⟨20270, by rfl⟩) R40541
theorem R27043 : Reach 27043 := rs (se 1 (by rfl) ⟨20282, by rfl⟩) R40565
theorem R27059 : Reach 27059 := rs (se 1 (by rfl) ⟨20294, by rfl⟩) R40589
theorem R27075 : Reach 27075 := rs (se 1 (by rfl) ⟨20306, by rfl⟩) R40613
theorem R27091 : Reach 27091 := rs (se 1 (by rfl) ⟨20318, by rfl⟩) R40637
theorem R27107 : Reach 27107 := rs (se 1 (by rfl) ⟨20330, by rfl⟩) R40661
theorem R27139 : Reach 27139 := rs (se 1 (by rfl) ⟨20354, by rfl⟩) R40709
theorem R59921 : Reach 59921 := rs (se 2 (by rfl) ⟨22470, by rfl⟩) R44941
theorem R59939 : Reach 59939 := rs (se 1 (by rfl) ⟨44954, by rfl⟩) R89909
theorem R27235 : Reach 27235 := rs (se 1 (by rfl) ⟨20426, by rfl⟩) R40853
theorem R289379 : Reach 289379 := rs (se 1 (by rfl) ⟨217034, by rfl⟩) R434069
theorem R60049 : Reach 60049 := rs (se 2 (by rfl) ⟨22518, by rfl⟩) R45037
theorem R27283 : Reach 27283 := rs (se 1 (by rfl) ⟨20462, by rfl⟩) R40925
theorem R453347 : Reach 453347 := rs (se 1 (by rfl) ⟨340010, by rfl⟩) R680021
theorem R27427 : Reach 27427 := rs (se 1 (by rfl) ⟨20570, by rfl⟩) R41141
theorem R60209 : Reach 60209 := rs (se 2 (by rfl) ⟨22578, by rfl⟩) R45157
theorem R60227 : Reach 60227 := rs (se 1 (by rfl) ⟨45170, by rfl⟩) R90341
theorem R125873 : Reach 125873 := rs (se 2 (by rfl) ⟨47202, by rfl⟩) R94405
theorem R27571 : Reach 27571 := rs (se 1 (by rfl) ⟨20678, by rfl⟩) R41357
theorem R93233 : Reach 93233 := rs (se 2 (by rfl) ⟨34962, by rfl⟩) R69925
theorem R27715 : Reach 27715 := rs (se 1 (by rfl) ⟨20786, by rfl⟩) R41573
theorem R158797 : Reach 158797 := rs (se 3 (by rfl) ⟨29774, by rfl⟩) R59549
theorem R60497 : Reach 60497 := rs (se 2 (by rfl) ⟨22686, by rfl⟩) R45373
theorem R60515 : Reach 60515 := rs (se 1 (by rfl) ⟨45386, by rfl⟩) R90773
theorem R60547 : Reach 60547 := rs (se 1 (by rfl) ⟨45410, by rfl⟩) R90821
theorem R27859 : Reach 27859 := rs (se 1 (by rfl) ⟨20894, by rfl⟩) R41789
theorem R60689 : Reach 60689 := rs (se 2 (by rfl) ⟨22758, by rfl⟩) R45517
theorem R28003 : Reach 28003 := rs (se 1 (by rfl) ⟨21002, by rfl⟩) R42005
theorem R60785 : Reach 60785 := rs (se 2 (by rfl) ⟨22794, by rfl⟩) R45589
theorem R60803 : Reach 60803 := rs (se 1 (by rfl) ⟨45602, by rfl⟩) R91205
theorem R28147 : Reach 28147 := rs (se 1 (by rfl) ⟨21110, by rfl⟩) R42221
theorem R28291 : Reach 28291 := rs (se 1 (by rfl) ⟨21218, by rfl⟩) R42437
theorem R28435 : Reach 28435 := rs (se 1 (by rfl) ⟨21326, by rfl⟩) R42653
theorem R28579 : Reach 28579 := rs (se 1 (by rfl) ⟨21434, by rfl⟩) R42869
theorem R94193 : Reach 94193 := rs (se 2 (by rfl) ⟨35322, by rfl⟩) R70645
theorem R28723 : Reach 28723 := rs (se 1 (by rfl) ⟨21542, by rfl⟩) R43085
theorem R159857 : Reach 159857 := rs (se 2 (by rfl) ⟨59946, by rfl⟩) R119893
theorem R28867 : Reach 28867 := rs (se 1 (by rfl) ⟨21650, by rfl⟩) R43301
theorem R61681 : Reach 61681 := rs (se 2 (by rfl) ⟨23130, by rfl⟩) R46261
theorem R29011 : Reach 29011 := rs (se 1 (by rfl) ⟨21758, by rfl⟩) R43517
theorem R127331 : Reach 127331 := rs (se 1 (by rfl) ⟨95498, by rfl⟩) R190997
theorem R29155 : Reach 29155 := rs (se 1 (by rfl) ⟨21866, by rfl⟩) R43733
theorem R258545 : Reach 258545 := rs (se 2 (by rfl) ⟨96954, by rfl⟩) R193909
theorem R61955 : Reach 61955 := rs (se 1 (by rfl) ⟨46466, by rfl⟩) R92933
theorem R127493 : Reach 127493 := rs (se 4 (by rfl) ⟨11952, by rfl⟩) R23905
theorem R29299 : Reach 29299 := rs (se 1 (by rfl) ⟨21974, by rfl⟩) R43949
theorem R94861 : Reach 94861 := rs (se 3 (by rfl) ⟨17786, by rfl⟩) R35573
theorem R62147 : Reach 62147 := rs (se 1 (by rfl) ⟨46610, by rfl⟩) R93221
theorem R29443 : Reach 29443 := rs (se 1 (by rfl) ⟨22082, by rfl⟩) R44165
theorem R29587 : Reach 29587 := rs (se 1 (by rfl) ⟨22190, by rfl⟩) R44381
theorem R95203 : Reach 95203 := rs (se 1 (by rfl) ⟨71402, by rfl⟩) R142805
theorem R29731 : Reach 29731 := rs (se 1 (by rfl) ⟨22298, by rfl⟩) R44597
theorem R29747 : Reach 29747 := rs (se 1 (by rfl) ⟨22310, by rfl⟩) R44621
theorem R128141 : Reach 128141 := rs (se 3 (by rfl) ⟨24026, by rfl⟩) R48053
theorem R29875 : Reach 29875 := rs (se 1 (by rfl) ⟨22406, by rfl⟩) R44813
theorem R62765 : Reach 62765 := rs (se 3 (by rfl) ⟨11768, by rfl⟩) R23537
theorem R30019 : Reach 30019 := rs (se 1 (by rfl) ⟨22514, by rfl⟩) R45029
theorem R95651 : Reach 95651 := rs (se 1 (by rfl) ⟨71738, by rfl⟩) R143477
theorem R30163 : Reach 30163 := rs (se 1 (by rfl) ⟨22622, by rfl⟩) R45245
theorem R62957 : Reach 62957 := rs (se 3 (by rfl) ⟨11804, by rfl⟩) R23609
theorem R325133 : Reach 325133 := rs (se 3 (by rfl) ⟨60962, by rfl⟩) R121925
theorem R30307 : Reach 30307 := rs (se 1 (by rfl) ⟨22730, by rfl⟩) R45461
theorem R63089 : Reach 63089 := rs (se 2 (by rfl) ⟨23658, by rfl⟩) R47317
theorem R63139 : Reach 63139 := rs (se 1 (by rfl) ⟨47354, by rfl⟩) R94709
theorem R30451 : Reach 30451 := rs (se 1 (by rfl) ⟨22838, by rfl⟩) R45677
theorem R96013 : Reach 96013 := rs (se 3 (by rfl) ⟨18002, by rfl⟩) R36005
theorem R63281 : Reach 63281 := rs (se 2 (by rfl) ⟨23730, by rfl⟩) R47461
theorem R30547 : Reach 30547 := rs (se 1 (by rfl) ⟨22910, by rfl⟩) R45821
theorem R96433 : Reach 96433 := rs (se 2 (by rfl) ⟨36162, by rfl⟩) R72325
theorem R30947 : Reach 30947 := rs (se 1 (by rfl) ⟨23210, by rfl⟩) R46421
theorem R31043 : Reach 31043 := rs (se 1 (by rfl) ⟨23282, by rfl⟩) R46565
theorem R194885 : Reach 194885 := rs (se 4 (by rfl) ⟨18270, by rfl⟩) R36541
theorem R96653 : Reach 96653 := rs (se 3 (by rfl) ⟨18122, by rfl⟩) R36245
theorem R63949 : Reach 63949 := rs (se 3 (by rfl) ⟨11990, by rfl⟩) R23981
theorem R162317 : Reach 162317 := rs (se 3 (by rfl) ⟨30434, by rfl⟩) R60869
theorem R64145 : Reach 64145 := rs (se 2 (by rfl) ⟨24054, by rfl⟩) R48109
theorem R64273 : Reach 64273 := rs (se 2 (by rfl) ⟨24102, by rfl⟩) R48205
theorem R31585 : Reach 31585 := rs (se 2 (by rfl) ⟨11844, by rfl⟩) R23689
theorem R31649 : Reach 31649 := rs (se 2 (by rfl) ⟨11868, by rfl⟩) R23737
theorem R31681 : Reach 31681 := rs (se 2 (by rfl) ⟨11880, by rfl⟩) R23761
theorem R31745 : Reach 31745 := rs (se 2 (by rfl) ⟨11904, by rfl⟩) R23809
theorem R31747 : Reach 31747 := rs (se 1 (by rfl) ⟨23810, by rfl⟩) R47621
theorem R64529 : Reach 64529 := rs (se 2 (by rfl) ⟨24198, by rfl⟩) R48397
theorem R64547 : Reach 64547 := rs (se 1 (by rfl) ⟨48410, by rfl⟩) R96821
theorem R31843 : Reach 31843 := rs (se 1 (by rfl) ⟨23882, by rfl⟩) R47765
theorem R64739 : Reach 64739 := rs (se 1 (by rfl) ⟨48554, by rfl⟩) R97109
theorem R163205 : Reach 163205 := rs (se 4 (by rfl) ⟨15300, by rfl⟩) R30601
theorem R32177 : Reach 32177 := rs (se 2 (by rfl) ⟨12066, by rfl⟩) R24133
theorem R32243 : Reach 32243 := rs (se 1 (by rfl) ⟨24182, by rfl⟩) R48365
theorem R32339 : Reach 32339 := rs (se 1 (by rfl) ⟨24254, by rfl⟩) R48509
theorem R65357 : Reach 65357 := rs (se 3 (by rfl) ⟨12254, by rfl⟩) R24509
theorem R131057 : Reach 131057 := rs (se 2 (by rfl) ⟨49146, by rfl⟩) R98293
theorem R65815 : Reach 65815 := rs (se 1 (by rfl) ⟨49361, by rfl⟩) R98723
theorem R65843 : Reach 65843 := rs (se 1 (by rfl) ⟨49382, by rfl⟩) R98765
theorem R33305 : Reach 33305 := rs (se 2 (by rfl) ⟨12489, by rfl⟩) R24979
theorem R33367 : Reach 33367 := rs (se 1 (by rfl) ⟨25025, by rfl⟩) R50051
theorem R66379 : Reach 66379 := rs (se 1 (by rfl) ⟨49784, by rfl⟩) R99569
theorem R33625 : Reach 33625 := rs (se 2 (by rfl) ⟨12609, by rfl⟩) R25219
theorem R99251 : Reach 99251 := rs (se 1 (by rfl) ⟨74438, by rfl⟩) R148877
theorem R99265 : Reach 99265 := rs (se 2 (by rfl) ⟨37224, by rfl⟩) R74449
theorem R66521 : Reach 66521 := rs (se 2 (by rfl) ⟨24945, by rfl⟩) R49891
theorem R66653 : Reach 66653 := rs (se 3 (by rfl) ⟨12497, by rfl⟩) R24995
theorem R67351 : Reach 67351 := rs (se 1 (by rfl) ⟨50513, by rfl⟩) R101027
theorem R165725 : Reach 165725 := rs (se 3 (by rfl) ⟨31073, by rfl⟩) R62147
theorem R133015 : Reach 133015 := rs (se 1 (by rfl) ⟨99761, by rfl⟩) R199523
theorem R67787 : Reach 67787 := rs (se 1 (by rfl) ⟨50840, by rfl⟩) R101681
theorem R35083 : Reach 35083 := rs (se 1 (by rfl) ⟨26312, by rfl⟩) R52625
theorem R35095 : Reach 35095 := rs (se 1 (by rfl) ⟨26321, by rfl⟩) R52643
theorem R330101 : Reach 330101 := rs (se 5 (by rfl) ⟨15473, by rfl⟩) R30947
theorem R100739 : Reach 100739 := rs (se 1 (by rfl) ⟨75554, by rfl⟩) R151109
theorem R35339 : Reach 35339 := rs (se 1 (by rfl) ⟨26504, by rfl⟩) R53009
theorem R133649 : Reach 133649 := rs (se 2 (by rfl) ⟨50118, by rfl⟩) R100237
theorem R35351 : Reach 35351 := rs (se 1 (by rfl) ⟨26513, by rfl⟩) R53027
theorem R68161 : Reach 68161 := rs (se 2 (by rfl) ⟨25560, by rfl⟩) R51121
theorem R35417 : Reach 35417 := rs (se 2 (by rfl) ⟨13281, by rfl⟩) R26563
theorem R133811 : Reach 133811 := rs (se 1 (by rfl) ⟨100358, by rfl⟩) R200717
theorem R35531 : Reach 35531 := rs (se 1 (by rfl) ⟨26648, by rfl⟩) R53297
theorem R35543 : Reach 35543 := rs (se 1 (by rfl) ⟨26657, by rfl⟩) R53315
theorem R101081 : Reach 101081 := rs (se 2 (by rfl) ⟨37905, by rfl⟩) R75811
theorem R35609 : Reach 35609 := rs (se 2 (by rfl) ⟨13353, by rfl⟩) R26707
theorem R101195 : Reach 101195 := rs (se 1 (by rfl) ⟨75896, by rfl⟩) R151793
theorem R101209 : Reach 101209 := rs (se 2 (by rfl) ⟨37953, by rfl⟩) R75907
theorem R35723 : Reach 35723 := rs (se 1 (by rfl) ⟨26792, by rfl⟩) R53585
theorem R35735 : Reach 35735 := rs (se 1 (by rfl) ⟨26801, by rfl⟩) R53603
theorem R35801 : Reach 35801 := rs (se 2 (by rfl) ⟨13425, by rfl⟩) R26851
theorem R199685 : Reach 199685 := rs (se 4 (by rfl) ⟨18720, by rfl⟩) R37441
theorem R199745 : Reach 199745 := rs (se 2 (by rfl) ⟨74904, by rfl⟩) R149809
theorem R35915 : Reach 35915 := rs (se 1 (by rfl) ⟨26936, by rfl⟩) R53873
theorem R35927 : Reach 35927 := rs (se 1 (by rfl) ⟨26945, by rfl⟩) R53891
theorem R68759 : Reach 68759 := rs (se 1 (by rfl) ⟨51569, by rfl⟩) R103139
theorem R35993 : Reach 35993 := rs (se 2 (by rfl) ⟨13497, by rfl⟩) R26995
theorem R36107 : Reach 36107 := rs (se 1 (by rfl) ⟨27080, by rfl⟩) R54161
theorem R36119 : Reach 36119 := rs (se 1 (by rfl) ⟨27089, by rfl⟩) R54179
theorem R36185 : Reach 36185 := rs (se 2 (by rfl) ⟨13569, by rfl⟩) R27139
theorem R36299 : Reach 36299 := rs (se 1 (by rfl) ⟨27224, by rfl⟩) R54449
theorem R36311 : Reach 36311 := rs (se 1 (by rfl) ⟨27233, by rfl⟩) R54467
theorem R36377 : Reach 36377 := rs (se 2 (by rfl) ⟨13641, by rfl⟩) R27283
theorem R36491 : Reach 36491 := rs (se 1 (by rfl) ⟨27368, by rfl⟩) R54737
theorem R36503 : Reach 36503 := rs (se 1 (by rfl) ⟨27377, by rfl⟩) R54755
theorem R36569 : Reach 36569 := rs (se 2 (by rfl) ⟨13713, by rfl⟩) R27427
theorem R102167 : Reach 102167 := rs (se 1 (by rfl) ⟨76625, by rfl⟩) R153251
theorem R36683 : Reach 36683 := rs (se 1 (by rfl) ⟨27512, by rfl⟩) R55025
theorem R36695 : Reach 36695 := rs (se 1 (by rfl) ⟨27521, by rfl⟩) R55043
theorem R167831 : Reach 167831 := rs (se 1 (by rfl) ⟨125873, by rfl⟩) R251747
theorem R36761 : Reach 36761 := rs (se 2 (by rfl) ⟨13785, by rfl⟩) R27571
theorem R36875 : Reach 36875 := rs (se 1 (by rfl) ⟨27656, by rfl⟩) R55313
theorem R36887 : Reach 36887 := rs (se 1 (by rfl) ⟨27665, by rfl⟩) R55331
theorem R36953 : Reach 36953 := rs (se 2 (by rfl) ⟨13857, by rfl⟩) R27715
theorem R135269 : Reach 135269 := rs (se 4 (by rfl) ⟨12681, by rfl⟩) R25363
theorem R168115 : Reach 168115 := rs (se 1 (by rfl) ⟨126086, by rfl⟩) R252173
theorem R37067 : Reach 37067 := rs (se 1 (by rfl) ⟨27800, by rfl⟩) R55601
theorem R37079 : Reach 37079 := rs (se 1 (by rfl) ⟨27809, by rfl⟩) R55619
theorem R37145 : Reach 37145 := rs (se 2 (by rfl) ⟨13929, by rfl⟩) R27859
theorem R102721 : Reach 102721 := rs (se 2 (by rfl) ⟨38520, by rfl⟩) R77041
theorem R37259 : Reach 37259 := rs (se 1 (by rfl) ⟨27944, by rfl⟩) R55889
theorem R37271 : Reach 37271 := rs (se 1 (by rfl) ⟨27953, by rfl⟩) R55907
theorem R37337 : Reach 37337 := rs (se 2 (by rfl) ⟨14001, by rfl⟩) R28003
theorem R135755 : Reach 135755 := rs (se 1 (by rfl) ⟨101816, by rfl⟩) R203633
theorem R37451 : Reach 37451 := rs (se 1 (by rfl) ⟨28088, by rfl⟩) R56177
theorem R37463 : Reach 37463 := rs (se 1 (by rfl) ⟨28097, by rfl⟩) R56195
theorem R70237 : Reach 70237 := rs (se 3 (by rfl) ⟨13169, by rfl⟩) R26339
theorem R37529 : Reach 37529 := rs (se 2 (by rfl) ⟨14073, by rfl⟩) R28147
theorem R103085 : Reach 103085 := rs (se 3 (by rfl) ⟨19328, by rfl⟩) R38657
theorem R37643 : Reach 37643 := rs (se 1 (by rfl) ⟨28232, by rfl⟩) R56465
theorem R37655 : Reach 37655 := rs (se 1 (by rfl) ⟨28241, by rfl⟩) R56483
theorem R37721 : Reach 37721 := rs (se 2 (by rfl) ⟨14145, by rfl⟩) R28291
theorem R37783 : Reach 37783 := rs (se 1 (by rfl) ⟨28337, by rfl⟩) R56675
theorem R37835 : Reach 37835 := rs (se 1 (by rfl) ⟨28376, by rfl⟩) R56753
theorem R37847 : Reach 37847 := rs (se 1 (by rfl) ⟨28385, by rfl⟩) R56771
theorem R201689 : Reach 201689 := rs (se 2 (by rfl) ⟨75633, by rfl⟩) R151267
theorem R37913 : Reach 37913 := rs (se 2 (by rfl) ⟨14217, by rfl⟩) R28435
theorem R38027 : Reach 38027 := rs (se 1 (by rfl) ⟨28520, by rfl⟩) R57041
theorem R38039 : Reach 38039 := rs (se 1 (by rfl) ⟨28529, by rfl⟩) R57059
theorem R38105 : Reach 38105 := rs (se 2 (by rfl) ⟨14289, by rfl⟩) R28579
theorem R38219 : Reach 38219 := rs (se 1 (by rfl) ⟨28664, by rfl⟩) R57329
theorem R38231 : Reach 38231 := rs (se 1 (by rfl) ⟨28673, by rfl⟩) R57347
theorem R38297 : Reach 38297 := rs (se 2 (by rfl) ⟨14361, by rfl⟩) R28723
theorem R38411 : Reach 38411 := rs (se 1 (by rfl) ⟨28808, by rfl⟩) R57617
theorem R38423 : Reach 38423 := rs (se 1 (by rfl) ⟨28817, by rfl⟩) R57635
theorem R38489 : Reach 38489 := rs (se 2 (by rfl) ⟨14433, by rfl⟩) R28867
theorem R38603 : Reach 38603 := rs (se 1 (by rfl) ⟨28952, by rfl⟩) R57905
theorem R38615 : Reach 38615 := rs (se 1 (by rfl) ⟨28961, by rfl⟩) R57923
theorem R38681 : Reach 38681 := rs (se 2 (by rfl) ⟨14505, by rfl⟩) R29011
theorem R202571 : Reach 202571 := rs (se 1 (by rfl) ⟨151928, by rfl⟩) R303857
theorem R38795 : Reach 38795 := rs (se 1 (by rfl) ⟨29096, by rfl⟩) R58193
theorem R38807 : Reach 38807 := rs (se 1 (by rfl) ⟨29105, by rfl⟩) R58211
theorem R38873 : Reach 38873 := rs (se 2 (by rfl) ⟨14577, by rfl⟩) R29155
theorem R38987 : Reach 38987 := rs (se 1 (by rfl) ⟨29240, by rfl⟩) R58481
theorem R38999 : Reach 38999 := rs (se 1 (by rfl) ⟨29249, by rfl⟩) R58499
theorem R39065 : Reach 39065 := rs (se 2 (by rfl) ⟨14649, by rfl⟩) R29299
theorem R39179 : Reach 39179 := rs (se 1 (by rfl) ⟨29384, by rfl⟩) R58769
theorem R39191 : Reach 39191 := rs (se 1 (by rfl) ⟨29393, by rfl⟩) R58787
theorem R39257 : Reach 39257 := rs (se 2 (by rfl) ⟨14721, by rfl⟩) R29443
theorem R39371 : Reach 39371 := rs (se 1 (by rfl) ⟨29528, by rfl⟩) R59057
theorem R39383 : Reach 39383 := rs (se 1 (by rfl) ⟨29537, by rfl⟩) R59075
theorem R39449 : Reach 39449 := rs (se 2 (by rfl) ⟨14793, by rfl⟩) R29587
theorem R39563 : Reach 39563 := rs (se 1 (by rfl) ⟨29672, by rfl⟩) R59345
theorem R39575 : Reach 39575 := rs (se 1 (by rfl) ⟨29681, by rfl⟩) R59363
theorem R39641 : Reach 39641 := rs (se 2 (by rfl) ⟨14865, by rfl⟩) R29731
theorem R39703 : Reach 39703 := rs (se 1 (by rfl) ⟨29777, by rfl⟩) R59555
theorem R39755 : Reach 39755 := rs (se 1 (by rfl) ⟨29816, by rfl⟩) R59633
theorem R39767 : Reach 39767 := rs (se 1 (by rfl) ⟨29825, by rfl⟩) R59651
theorem R39833 : Reach 39833 := rs (se 2 (by rfl) ⟨14937, by rfl⟩) R29875
theorem R236465 : Reach 236465 := rs (se 2 (by rfl) ⟨88674, by rfl⟩) R177349
theorem R39947 : Reach 39947 := rs (se 1 (by rfl) ⟨29960, by rfl⟩) R59921
theorem R39959 : Reach 39959 := rs (se 1 (by rfl) ⟨29969, by rfl⟩) R59939
theorem R269347 : Reach 269347 := rs (se 1 (by rfl) ⟨202010, by rfl⟩) R404021
theorem R40025 : Reach 40025 := rs (se 2 (by rfl) ⟨15009, by rfl⟩) R30019
theorem R302231 : Reach 302231 := rs (se 1 (by rfl) ⟨226673, by rfl⟩) R453347
theorem R138419 : Reach 138419 := rs (se 1 (by rfl) ⟨103814, by rfl⟩) R207629
theorem R40139 : Reach 40139 := rs (se 1 (by rfl) ⟨30104, by rfl⟩) R60209
theorem R40151 : Reach 40151 := rs (se 1 (by rfl) ⟨30113, by rfl⟩) R60227
theorem R40217 : Reach 40217 := rs (se 2 (by rfl) ⟨15081, by rfl⟩) R30163
theorem R40331 : Reach 40331 := rs (se 1 (by rfl) ⟨30248, by rfl⟩) R60497
theorem R73111 : Reach 73111 := rs (se 1 (by rfl) ⟨54833, by rfl⟩) R109667
theorem R40343 : Reach 40343 := rs (se 1 (by rfl) ⟨30257, by rfl⟩) R60515
theorem R73163 : Reach 73163 := rs (se 1 (by rfl) ⟨54872, by rfl⟩) R109745
theorem R40409 : Reach 40409 := rs (se 2 (by rfl) ⟨15153, by rfl⟩) R30307
theorem R40459 : Reach 40459 := rs (se 1 (by rfl) ⟨30344, by rfl⟩) R60689
theorem R40523 : Reach 40523 := rs (se 1 (by rfl) ⟨30392, by rfl⟩) R60785
theorem R40535 : Reach 40535 := rs (se 1 (by rfl) ⟨30401, by rfl⟩) R60803
theorem R40601 : Reach 40601 := rs (se 2 (by rfl) ⟨15225, by rfl⟩) R30451
theorem R40729 : Reach 40729 := rs (se 2 (by rfl) ⟨15273, by rfl⟩) R30547
theorem R73561 : Reach 73561 := rs (se 2 (by rfl) ⟨27585, by rfl⟩) R55171
theorem R106571 : Reach 106571 := rs (se 1 (by rfl) ⟨79928, by rfl⟩) R159857
theorem R205091 : Reach 205091 := rs (se 1 (by rfl) ⟨153818, by rfl⟩) R307637
theorem R172363 : Reach 172363 := rs (se 1 (by rfl) ⟨129272, by rfl⟩) R258545
theorem R41303 : Reach 41303 := rs (se 1 (by rfl) ⟨30977, by rfl⟩) R61955
theorem R41431 : Reach 41431 := rs (se 1 (by rfl) ⟨31073, by rfl⟩) R62147
theorem R172637 : Reach 172637 := rs (se 3 (by rfl) ⟨32369, by rfl⟩) R64739
theorem R139877 : Reach 139877 := rs (se 4 (by rfl) ⟨13113, by rfl⟩) R26227
theorem R41843 : Reach 41843 := rs (se 1 (by rfl) ⟨31382, by rfl⟩) R62765
theorem R41971 : Reach 41971 := rs (se 1 (by rfl) ⟨31478, by rfl⟩) R62957
theorem R74803 : Reach 74803 := rs (se 1 (by rfl) ⟨56102, by rfl⟩) R112205
theorem R42059 : Reach 42059 := rs (se 1 (by rfl) ⟨31544, by rfl⟩) R63089
theorem R42113 : Reach 42113 := rs (se 2 (by rfl) ⟨15792, by rfl⟩) R31585
theorem R42187 : Reach 42187 := rs (se 1 (by rfl) ⟨31640, by rfl⟩) R63281
theorem R42241 : Reach 42241 := rs (se 2 (by rfl) ⟨15840, by rfl⟩) R31681
theorem R140561 : Reach 140561 := rs (se 2 (by rfl) ⟨52710, by rfl⟩) R105421
theorem R402733 : Reach 402733 := rs (se 3 (by rfl) ⟨75512, by rfl⟩) R151025
theorem R42329 : Reach 42329 := rs (se 2 (by rfl) ⟨15873, by rfl⟩) R31747
theorem R42457 : Reach 42457 := rs (se 2 (by rfl) ⟨15921, by rfl⟩) R31843
theorem R108211 : Reach 108211 := rs (se 1 (by rfl) ⟨81158, by rfl⟩) R162317
theorem R42763 : Reach 42763 := rs (se 1 (by rfl) ⟨32072, by rfl⟩) R64145
theorem R337841 : Reach 337841 := rs (se 2 (by rfl) ⟨126690, by rfl⟩) R253381
theorem R43019 : Reach 43019 := rs (se 1 (by rfl) ⟨32264, by rfl⟩) R64529
theorem R43031 : Reach 43031 := rs (se 1 (by rfl) ⟨32273, by rfl⟩) R64547
theorem R43159 : Reach 43159 := rs (se 1 (by rfl) ⟨32369, by rfl⟩) R64739
theorem R108803 : Reach 108803 := rs (se 1 (by rfl) ⟨81602, by rfl⟩) R163205
theorem R272645 : Reach 272645 := rs (se 4 (by rfl) ⟨25560, by rfl⟩) R51121
theorem R76097 : Reach 76097 := rs (se 2 (by rfl) ⟨28536, by rfl⟩) R57073
theorem R108973 : Reach 108973 := rs (se 3 (by rfl) ⟨20432, by rfl⟩) R40865
theorem R272857 : Reach 272857 := rs (se 2 (by rfl) ⟨102321, by rfl⟩) R204643
theorem R43571 : Reach 43571 := rs (se 1 (by rfl) ⟨32678, by rfl⟩) R65357
theorem R76439 : Reach 76439 := rs (se 1 (by rfl) ⟨57329, by rfl⟩) R114659
theorem R43699 : Reach 43699 := rs (se 1 (by rfl) ⟨32774, by rfl⟩) R65549
theorem R43787 : Reach 43787 := rs (se 1 (by rfl) ⟨32840, by rfl⟩) R65681
theorem R43841 : Reach 43841 := rs (se 2 (by rfl) ⟨16440, by rfl⟩) R32881
theorem R43915 : Reach 43915 := rs (se 1 (by rfl) ⟨32936, by rfl⟩) R65873
theorem R43969 : Reach 43969 := rs (se 2 (by rfl) ⟨16488, by rfl⟩) R32977
theorem R43993 : Reach 43993 := rs (se 2 (by rfl) ⟨16497, by rfl⟩) R32995
theorem R44057 : Reach 44057 := rs (se 2 (by rfl) ⟨16521, by rfl⟩) R33043
theorem R437399 : Reach 437399 := rs (se 1 (by rfl) ⟨328049, by rfl⟩) R656099
theorem R44185 : Reach 44185 := rs (se 2 (by rfl) ⟨16569, by rfl⟩) R33139
theorem R44759 : Reach 44759 := rs (se 1 (by rfl) ⟨33569, by rfl⟩) R67139
theorem R44887 : Reach 44887 := rs (se 1 (by rfl) ⟨33665, by rfl⟩) R67331
theorem R110429 : Reach 110429 := rs (se 3 (by rfl) ⟨20705, by rfl⟩) R41411
theorem R45107 : Reach 45107 := rs (se 1 (by rfl) ⟨33830, by rfl⟩) R67661
theorem R45299 : Reach 45299 := rs (se 1 (by rfl) ⟨33974, by rfl⟩) R67949
theorem R45335 : Reach 45335 := rs (se 1 (by rfl) ⟨34001, by rfl⟩) R68003
theorem R45377 : Reach 45377 := rs (se 2 (by rfl) ⟨17016, by rfl⟩) R34033
theorem R45427 : Reach 45427 := rs (se 1 (by rfl) ⟨34070, by rfl⟩) R68141
theorem R143795 : Reach 143795 := rs (se 1 (by rfl) ⟨107846, by rfl⟩) R215693
theorem R45515 : Reach 45515 := rs (se 1 (by rfl) ⟨34136, by rfl⟩) R68273
theorem R45569 : Reach 45569 := rs (se 2 (by rfl) ⟨17088, by rfl⟩) R34177
theorem R111127 : Reach 111127 := rs (se 1 (by rfl) ⟨83345, by rfl⟩) R166691
theorem R45593 : Reach 45593 := rs (se 2 (by rfl) ⟨17097, by rfl⟩) R34195
theorem R45643 : Reach 45643 := rs (se 1 (by rfl) ⟨34232, by rfl⟩) R68465
theorem R78425 : Reach 78425 := rs (se 2 (by rfl) ⟨29409, by rfl⟩) R58819
theorem R45697 : Reach 45697 := rs (se 2 (by rfl) ⟨17136, by rfl⟩) R34273
theorem R78515 : Reach 78515 := rs (se 1 (by rfl) ⟨58886, by rfl⟩) R117773
theorem R46003 : Reach 46003 := rs (se 1 (by rfl) ⟨34502, by rfl⟩) R69005
theorem R799895 : Reach 799895 := rs (se 1 (by rfl) ⟨599921, by rfl⟩) R1199843
theorem R46295 : Reach 46295 := rs (se 1 (by rfl) ⟨34721, by rfl⟩) R69443
theorem R46337 : Reach 46337 := rs (se 2 (by rfl) ⟨17376, by rfl⟩) R34753
theorem R406885 : Reach 406885 := rs (se 4 (by rfl) ⟨38145, by rfl⟩) R76291
theorem R46489 : Reach 46489 := rs (se 2 (by rfl) ⟨17433, by rfl⟩) R34867
theorem R79325 : Reach 79325 := rs (se 3 (by rfl) ⟨14873, by rfl⟩) R29747
theorem R374341 : Reach 374341 := rs (se 4 (by rfl) ⟨35094, by rfl⟩) R70189
theorem R177815 : Reach 177815 := rs (se 1 (by rfl) ⟨133361, by rfl⟩) R266723
theorem R767843 : Reach 767843 := rs (se 1 (by rfl) ⟨575882, by rfl⟩) R1151765
theorem R145253 : Reach 145253 := rs (se 4 (by rfl) ⟨13617, by rfl⟩) R27235
theorem R47027 : Reach 47027 := rs (se 1 (by rfl) ⟨35270, by rfl⟩) R70541
theorem R47051 : Reach 47051 := rs (se 1 (by rfl) ⟨35288, by rfl⟩) R70577
theorem R211045 : Reach 211045 := rs (se 4 (by rfl) ⟨19785, by rfl⟩) R39571
theorem R47233 : Reach 47233 := rs (se 2 (by rfl) ⟨17712, by rfl⟩) R35425
theorem R47243 : Reach 47243 := rs (se 1 (by rfl) ⟨35432, by rfl⟩) R70865
theorem R80065 : Reach 80065 := rs (se 2 (by rfl) ⟨30024, by rfl⟩) R60049
theorem R145709 : Reach 145709 := rs (se 3 (by rfl) ⟨27320, by rfl⟩) R54641
theorem R47639 : Reach 47639 := rs (se 1 (by rfl) ⟨35729, by rfl⟩) R71459
theorem R80459 : Reach 80459 := rs (se 1 (by rfl) ⟨60344, by rfl⟩) R120689
theorem R211729 : Reach 211729 := rs (se 2 (by rfl) ⟨79398, by rfl⟩) R158797
theorem R211747 : Reach 211747 := rs (se 1 (by rfl) ⟨158810, by rfl⟩) R317621
theorem R47947 : Reach 47947 := rs (se 1 (by rfl) ⟨35960, by rfl⟩) R71921
theorem R80729 : Reach 80729 := rs (se 2 (by rfl) ⟨30273, by rfl⟩) R60547
theorem R48023 : Reach 48023 := rs (se 1 (by rfl) ⟨36017, by rfl⟩) R72035
theorem R48089 : Reach 48089 := rs (se 2 (by rfl) ⟨18033, by rfl⟩) R36067
theorem R146393 : Reach 146393 := rs (se 2 (by rfl) ⟨54897, by rfl⟩) R109795
theorem R212003 : Reach 212003 := rs (se 1 (by rfl) ⟨159002, by rfl⟩) R318005
theorem R48281 : Reach 48281 := rs (se 2 (by rfl) ⟨18105, by rfl⟩) R36211
theorem R81431 : Reach 81431 := rs (se 1 (by rfl) ⟨61073, by rfl⟩) R122147
theorem R48691 : Reach 48691 := rs (se 1 (by rfl) ⟨36518, by rfl⟩) R73037
theorem R179813 : Reach 179813 := rs (se 4 (by rfl) ⟨16857, by rfl⟩) R33715
theorem R147217 : Reach 147217 := rs (se 2 (by rfl) ⟨55206, by rfl⟩) R110413
theorem R48919 : Reach 48919 := rs (se 1 (by rfl) ⟨36689, by rfl⟩) R73379
theorem R49025 : Reach 49025 := rs (se 2 (by rfl) ⟨18384, by rfl⟩) R36769
theorem R49175 : Reach 49175 := rs (se 1 (by rfl) ⟨36881, by rfl⟩) R73763
theorem R49177 : Reach 49177 := rs (se 2 (by rfl) ⟨18441, by rfl⟩) R36883
theorem R81971 : Reach 81971 := rs (se 1 (by rfl) ⟨61478, by rfl⟩) R122957
theorem R82241 : Reach 82241 := rs (se 2 (by rfl) ⟨30840, by rfl⟩) R61681
theorem R246347 : Reach 246347 := rs (se 1 (by rfl) ⟨184760, by rfl⟩) R369521
theorem R115501 : Reach 115501 := rs (se 3 (by rfl) ⟨21656, by rfl⟩) R43313
theorem R82763 : Reach 82763 := rs (se 1 (by rfl) ⟨62072, by rfl⟩) R124145
theorem R82781 : Reach 82781 := rs (se 3 (by rfl) ⟨15521, by rfl⟩) R31043
theorem R50483 : Reach 50483 := rs (se 1 (by rfl) ⟨37862, by rfl⟩) R75725
theorem R50635 : Reach 50635 := rs (se 1 (by rfl) ⟨37976, by rfl⟩) R75953
theorem R50711 : Reach 50711 := rs (se 1 (by rfl) ⟨38033, by rfl⟩) R76067
theorem R771677 : Reach 771677 := rs (se 3 (by rfl) ⟨144689, by rfl⟩) R289379
theorem R312983 : Reach 312983 := rs (se 1 (by rfl) ⟨234737, by rfl⟩) R469475
theorem R50969 : Reach 50969 := rs (se 2 (by rfl) ⟨19113, by rfl⟩) R38227
theorem R83915 : Reach 83915 := rs (se 1 (by rfl) ⟨62936, by rfl⟩) R125873
theorem R968773 : Reach 968773 := rs (se 4 (by rfl) ⟨90822, by rfl⟩) R181645
theorem R84185 : Reach 84185 := rs (se 2 (by rfl) ⟨31569, by rfl⟩) R63139
theorem R84397 : Reach 84397 := rs (se 3 (by rfl) ⟨15824, by rfl⟩) R31649
theorem R84653 : Reach 84653 := rs (se 3 (by rfl) ⟨15872, by rfl⟩) R31745
theorem R84887 : Reach 84887 := rs (se 1 (by rfl) ⟨63665, by rfl⟩) R127331
theorem R84995 : Reach 84995 := rs (se 1 (by rfl) ⟨63746, by rfl⟩) R127493
theorem R52481 : Reach 52481 := rs (se 2 (by rfl) ⟨19680, by rfl⟩) R39361
theorem R85265 : Reach 85265 := rs (se 2 (by rfl) ⟨31974, by rfl⟩) R63949
theorem R85427 : Reach 85427 := rs (se 1 (by rfl) ⟨64070, by rfl⟩) R128141
theorem R151085 : Reach 151085 := rs (se 3 (by rfl) ⟨28328, by rfl⟩) R56657
theorem R216755 : Reach 216755 := rs (se 1 (by rfl) ⟨162566, by rfl⟩) R325133
theorem R85697 : Reach 85697 := rs (se 2 (by rfl) ⟨32136, by rfl⟩) R64273
theorem R85805 : Reach 85805 := rs (se 3 (by rfl) ⟨16088, by rfl⟩) R32177
theorem R53081 : Reach 53081 := rs (se 2 (by rfl) ⟨19905, by rfl⟩) R39811
theorem R53171 : Reach 53171 := rs (se 1 (by rfl) ⟨39878, by rfl⟩) R79757
theorem R53207 : Reach 53207 := rs (se 1 (by rfl) ⟨39905, by rfl⟩) R79811
theorem R85981 : Reach 85981 := rs (se 3 (by rfl) ⟨16121, by rfl⟩) R32243
theorem R53387 : Reach 53387 := rs (se 1 (by rfl) ⟨40040, by rfl⟩) R80081
theorem R53441 : Reach 53441 := rs (se 2 (by rfl) ⟨20040, by rfl⟩) R40081
theorem R86237 : Reach 86237 := rs (se 3 (by rfl) ⟨16169, by rfl⟩) R32339
theorem R53657 : Reach 53657 := rs (se 2 (by rfl) ⟨20121, by rfl⟩) R40243
theorem R53747 : Reach 53747 := rs (se 1 (by rfl) ⟨40310, by rfl⟩) R80621
theorem R53783 : Reach 53783 := rs (se 1 (by rfl) ⟨40337, by rfl⟩) R80675
theorem R53963 : Reach 53963 := rs (se 1 (by rfl) ⟨40472, by rfl⟩) R80945
theorem R54017 : Reach 54017 := rs (se 2 (by rfl) ⟨20256, by rfl⟩) R40513
theorem R54233 : Reach 54233 := rs (se 2 (by rfl) ⟨20337, by rfl⟩) R40675
theorem R54283 : Reach 54283 := rs (se 1 (by rfl) ⟨40712, by rfl⟩) R81425
theorem R54323 : Reach 54323 := rs (se 1 (by rfl) ⟨40742, by rfl⟩) R81485
theorem R54359 : Reach 54359 := rs (se 1 (by rfl) ⟨40769, by rfl⟩) R81539
theorem R54539 : Reach 54539 := rs (se 1 (by rfl) ⟨40904, by rfl⟩) R81809
theorem R54593 : Reach 54593 := rs (se 2 (by rfl) ⟨20472, by rfl⟩) R40945
theorem R87371 : Reach 87371 := rs (se 1 (by rfl) ⟨65528, by rfl⟩) R131057
theorem R54809 : Reach 54809 := rs (se 2 (by rfl) ⟨20553, by rfl⟩) R41107
theorem R218659 : Reach 218659 := rs (se 1 (by rfl) ⟨163994, by rfl⟩) R327989
theorem R120365 : Reach 120365 := rs (se 3 (by rfl) ⟨22568, by rfl⟩) R45137
theorem R87641 : Reach 87641 := rs (se 2 (by rfl) ⟨32865, by rfl⟩) R65731
theorem R54899 : Reach 54899 := rs (se 1 (by rfl) ⟨41174, by rfl⟩) R82349
theorem R54935 : Reach 54935 := rs (se 1 (by rfl) ⟨41201, by rfl⟩) R82403
theorem R153361 : Reach 153361 := rs (se 2 (by rfl) ⟨57510, by rfl⟩) R115021
theorem R55115 : Reach 55115 := rs (se 1 (by rfl) ⟨41336, by rfl⟩) R82673
theorem R55169 : Reach 55169 := rs (se 2 (by rfl) ⟨20688, by rfl⟩) R41377
theorem R55385 : Reach 55385 := rs (se 2 (by rfl) ⟨20769, by rfl⟩) R41539
theorem R153751 : Reach 153751 := rs (se 1 (by rfl) ⟨115313, by rfl⟩) R230627
theorem R55475 : Reach 55475 := rs (se 1 (by rfl) ⟨41606, by rfl⟩) R83213
theorem R55511 : Reach 55511 := rs (se 1 (by rfl) ⟨41633, by rfl⟩) R83267
theorem R88343 : Reach 88343 := rs (se 1 (by rfl) ⟨66257, by rfl⟩) R132515
theorem R55667 : Reach 55667 := rs (se 1 (by rfl) ⟨41750, by rfl⟩) R83501
theorem R88451 : Reach 88451 := rs (se 1 (by rfl) ⟨66338, by rfl⟩) R132677
theorem R55691 : Reach 55691 := rs (se 1 (by rfl) ⟨41768, by rfl⟩) R83537
theorem R55745 : Reach 55745 := rs (se 2 (by rfl) ⟨20904, by rfl⟩) R41809
theorem R88721 : Reach 88721 := rs (se 2 (by rfl) ⟨33270, by rfl⟩) R66541
theorem R56087 : Reach 56087 := rs (se 1 (by rfl) ⟨42065, by rfl⟩) R84131
theorem R88883 : Reach 88883 := rs (se 1 (by rfl) ⟨66662, by rfl⟩) R133325
theorem R187201 : Reach 187201 := rs (se 2 (by rfl) ⟨70200, by rfl⟩) R140401
theorem R121675 : Reach 121675 := rs (se 1 (by rfl) ⟨91256, by rfl⟩) R182513
theorem R56267 : Reach 56267 := rs (se 1 (by rfl) ⟨42200, by rfl⟩) R84401
theorem R23511 : Reach 23511 := rs (se 1 (by rfl) ⟨17633, by rfl⟩) R35267
theorem R23531 : Reach 23531 := rs (se 1 (by rfl) ⟨17648, by rfl⟩) R35297
theorem R23543 : Reach 23543 := rs (se 1 (by rfl) ⟨17657, by rfl⟩) R35315
theorem R23563 : Reach 23563 := rs (se 1 (by rfl) ⟨17672, by rfl⟩) R35345
theorem R23575 : Reach 23575 := rs (se 1 (by rfl) ⟨17681, by rfl⟩) R35363
theorem R23595 : Reach 23595 := rs (se 1 (by rfl) ⟨17696, by rfl⟩) R35393
theorem R23607 : Reach 23607 := rs (se 1 (by rfl) ⟨17705, by rfl⟩) R35411
theorem R89153 : Reach 89153 := rs (se 2 (by rfl) ⟨33432, by rfl⟩) R66865
theorem R23627 : Reach 23627 := rs (se 1 (by rfl) ⟨17720, by rfl⟩) R35441
theorem R23639 : Reach 23639 := rs (se 1 (by rfl) ⟨17729, by rfl⟩) R35459
theorem R23659 : Reach 23659 := rs (se 1 (by rfl) ⟨17744, by rfl⟩) R35489
theorem R23671 : Reach 23671 := rs (se 1 (by rfl) ⟨17753, by rfl⟩) R35507
theorem R23691 : Reach 23691 := rs (se 1 (by rfl) ⟨17768, by rfl⟩) R35537
theorem R679063 : Reach 679063 := rs (se 1 (by rfl) ⟨509297, by rfl⟩) R1018595
theorem R23703 : Reach 23703 := rs (se 1 (by rfl) ⟨17777, by rfl⟩) R35555
theorem R23723 : Reach 23723 := rs (se 1 (by rfl) ⟨17792, by rfl⟩) R35585
theorem R89261 : Reach 89261 := rs (se 3 (by rfl) ⟨16736, by rfl⟩) R33473
theorem R23735 : Reach 23735 := rs (se 1 (by rfl) ⟨17801, by rfl⟩) R35603
theorem R56513 : Reach 56513 := rs (se 2 (by rfl) ⟨21192, by rfl⟩) R42385
theorem R23755 : Reach 23755 := rs (se 1 (by rfl) ⟨17816, by rfl⟩) R35633
theorem R23767 : Reach 23767 := rs (se 1 (by rfl) ⟨17825, by rfl⟩) R35651
theorem R56537 : Reach 56537 := rs (se 2 (by rfl) ⟨21201, by rfl⟩) R42403
theorem R23787 : Reach 23787 := rs (se 1 (by rfl) ⟨17840, by rfl⟩) R35681
theorem R23799 : Reach 23799 := rs (se 1 (by rfl) ⟨17849, by rfl⟩) R35699
theorem R23819 : Reach 23819 := rs (se 1 (by rfl) ⟨17864, by rfl⟩) R35729
theorem R23831 : Reach 23831 := rs (se 1 (by rfl) ⟨17873, by rfl⟩) R35747
theorem R23851 : Reach 23851 := rs (se 1 (by rfl) ⟨17888, by rfl⟩) R35777
theorem R56627 : Reach 56627 := rs (se 1 (by rfl) ⟨42470, by rfl⟩) R84941
theorem R23863 : Reach 23863 := rs (se 1 (by rfl) ⟨17897, by rfl⟩) R35795
theorem R23883 : Reach 23883 := rs (se 1 (by rfl) ⟨17912, by rfl⟩) R35825
theorem R23895 : Reach 23895 := rs (se 1 (by rfl) ⟨17921, by rfl⟩) R35843
theorem R23915 : Reach 23915 := rs (se 1 (by rfl) ⟨17936, by rfl⟩) R35873
theorem R23927 : Reach 23927 := rs (se 1 (by rfl) ⟨17945, by rfl⟩) R35891
theorem R23947 : Reach 23947 := rs (se 1 (by rfl) ⟨17960, by rfl⟩) R35921
theorem R23959 : Reach 23959 := rs (se 1 (by rfl) ⟨17969, by rfl⟩) R35939
theorem R23979 : Reach 23979 := rs (se 1 (by rfl) ⟨17984, by rfl⟩) R35969
theorem R23991 : Reach 23991 := rs (se 1 (by rfl) ⟨17993, by rfl⟩) R35987
theorem R24011 : Reach 24011 := rs (se 1 (by rfl) ⟨18008, by rfl⟩) R36017
theorem R24023 : Reach 24023 := rs (se 1 (by rfl) ⟨18017, by rfl⟩) R36035
theorem R24043 : Reach 24043 := rs (se 1 (by rfl) ⟨18032, by rfl⟩) R36065
theorem R24055 : Reach 24055 := rs (se 1 (by rfl) ⟨18041, by rfl⟩) R36083
theorem R24075 : Reach 24075 := rs (se 1 (by rfl) ⟨18056, by rfl⟩) R36113
theorem R24087 : Reach 24087 := rs (se 1 (by rfl) ⟨18065, by rfl⟩) R36131
theorem R56855 : Reach 56855 := rs (se 1 (by rfl) ⟨42641, by rfl⟩) R85283
theorem R24107 : Reach 24107 := rs (se 1 (by rfl) ⟨18080, by rfl⟩) R36161
theorem R24119 : Reach 24119 := rs (se 1 (by rfl) ⟨18089, by rfl⟩) R36179
theorem R56897 : Reach 56897 := rs (se 2 (by rfl) ⟨21336, by rfl⟩) R42673
theorem R24139 : Reach 24139 := rs (se 1 (by rfl) ⟨18104, by rfl⟩) R36209
theorem R24151 : Reach 24151 := rs (se 1 (by rfl) ⟨18113, by rfl⟩) R36227
theorem R89693 : Reach 89693 := rs (se 3 (by rfl) ⟨16817, by rfl⟩) R33635
theorem R24171 : Reach 24171 := rs (se 1 (by rfl) ⟨18128, by rfl⟩) R36257
theorem R24183 : Reach 24183 := rs (se 1 (by rfl) ⟨18137, by rfl⟩) R36275
theorem R24203 : Reach 24203 := rs (se 1 (by rfl) ⟨18152, by rfl⟩) R36305
theorem R24215 : Reach 24215 := rs (se 1 (by rfl) ⟨18161, by rfl⟩) R36323
theorem R24235 : Reach 24235 := rs (se 1 (by rfl) ⟨18176, by rfl⟩) R36353
theorem R188081 : Reach 188081 := rs (se 2 (by rfl) ⟨70530, by rfl⟩) R141061
theorem R24247 : Reach 24247 := rs (se 1 (by rfl) ⟨18185, by rfl⟩) R36371
theorem R24267 : Reach 24267 := rs (se 1 (by rfl) ⟨18200, by rfl⟩) R36401
theorem R24279 : Reach 24279 := rs (se 1 (by rfl) ⟨18209, by rfl⟩) R36419
theorem R24299 : Reach 24299 := rs (se 1 (by rfl) ⟨18224, by rfl⟩) R36449
theorem R24311 : Reach 24311 := rs (se 1 (by rfl) ⟨18233, by rfl⟩) R36467
theorem R24331 : Reach 24331 := rs (se 1 (by rfl) ⟨18248, by rfl⟩) R36497
theorem R89873 : Reach 89873 := rs (se 2 (by rfl) ⟨33702, by rfl⟩) R67405
theorem R24343 : Reach 24343 := rs (se 1 (by rfl) ⟨18257, by rfl⟩) R36515
theorem R24363 : Reach 24363 := rs (se 1 (by rfl) ⟨18272, by rfl⟩) R36545
theorem R24375 : Reach 24375 := rs (se 1 (by rfl) ⟨18281, by rfl⟩) R36563
theorem R24395 : Reach 24395 := rs (se 1 (by rfl) ⟨18296, by rfl⟩) R36593
theorem R24407 : Reach 24407 := rs (se 1 (by rfl) ⟨18305, by rfl⟩) R36611
theorem R24427 : Reach 24427 := rs (se 1 (by rfl) ⟨18320, by rfl⟩) R36641
theorem R24439 : Reach 24439 := rs (se 1 (by rfl) ⟨18329, by rfl⟩) R36659
theorem R24459 : Reach 24459 := rs (se 1 (by rfl) ⟨18344, by rfl⟩) R36689
theorem R24471 : Reach 24471 := rs (se 1 (by rfl) ⟨18353, by rfl⟩) R36707
theorem R57239 : Reach 57239 := rs (se 1 (by rfl) ⟨42929, by rfl⟩) R85859
theorem R24491 : Reach 24491 := rs (se 1 (by rfl) ⟨18368, by rfl⟩) R36737
theorem R24503 : Reach 24503 := rs (se 1 (by rfl) ⟨18377, by rfl⟩) R36755
theorem R24523 : Reach 24523 := rs (se 1 (by rfl) ⟨18392, by rfl⟩) R36785
theorem R24535 : Reach 24535 := rs (se 1 (by rfl) ⟨18401, by rfl⟩) R36803
theorem R450521 : Reach 450521 := rs (se 2 (by rfl) ⟨168945, by rfl⟩) R337891
theorem R24555 : Reach 24555 := rs (se 1 (by rfl) ⟨18416, by rfl⟩) R36833
theorem R24567 : Reach 24567 := rs (se 1 (by rfl) ⟨18425, by rfl⟩) R36851
theorem R24587 : Reach 24587 := rs (se 1 (by rfl) ⟨18440, by rfl⟩) R36881
theorem R24599 : Reach 24599 := rs (se 1 (by rfl) ⟨18449, by rfl⟩) R36899
theorem R24619 : Reach 24619 := rs (se 1 (by rfl) ⟨18464, by rfl⟩) R36929
theorem R24631 : Reach 24631 := rs (se 1 (by rfl) ⟨18473, by rfl⟩) R36947
theorem R24651 : Reach 24651 := rs (se 1 (by rfl) ⟨18488, by rfl⟩) R36977
theorem R57419 : Reach 57419 := rs (se 1 (by rfl) ⟨43064, by rfl⟩) R86129
theorem R24663 : Reach 24663 := rs (se 1 (by rfl) ⟨18497, by rfl⟩) R36995
theorem R24683 : Reach 24683 := rs (se 1 (by rfl) ⟨18512, by rfl⟩) R37025
theorem R24695 : Reach 24695 := rs (se 1 (by rfl) ⟨18521, by rfl⟩) R37043
theorem R24715 : Reach 24715 := rs (se 1 (by rfl) ⟨18536, by rfl⟩) R37073
theorem R24727 : Reach 24727 := rs (se 1 (by rfl) ⟨18545, by rfl⟩) R37091
theorem R188567 : Reach 188567 := rs (se 1 (by rfl) ⟨141425, by rfl⟩) R282851
theorem R24747 : Reach 24747 := rs (se 1 (by rfl) ⟨18560, by rfl⟩) R37121
theorem R24759 : Reach 24759 := rs (se 1 (by rfl) ⟨18569, by rfl⟩) R37139
theorem R90305 : Reach 90305 := rs (se 2 (by rfl) ⟨33864, by rfl⟩) R67729
theorem R24779 : Reach 24779 := rs (se 1 (by rfl) ⟨18584, by rfl⟩) R37169
theorem R24791 : Reach 24791 := rs (se 1 (by rfl) ⟨18593, by rfl⟩) R37187
theorem R24811 : Reach 24811 := rs (se 1 (by rfl) ⟨18608, by rfl⟩) R37217
theorem R24823 : Reach 24823 := rs (se 1 (by rfl) ⟨18617, by rfl⟩) R37235
theorem R24843 : Reach 24843 := rs (se 1 (by rfl) ⟨18632, by rfl⟩) R37265
theorem R24855 : Reach 24855 := rs (se 1 (by rfl) ⟨18641, by rfl⟩) R37283
theorem R24875 : Reach 24875 := rs (se 1 (by rfl) ⟨18656, by rfl⟩) R37313
theorem R24887 : Reach 24887 := rs (se 1 (by rfl) ⟨18665, by rfl⟩) R37331
theorem R24907 : Reach 24907 := rs (se 1 (by rfl) ⟨18680, by rfl⟩) R37361
theorem R24919 : Reach 24919 := rs (se 1 (by rfl) ⟨18689, by rfl⟩) R37379
theorem R57689 : Reach 57689 := rs (se 2 (by rfl) ⟨21633, by rfl⟩) R43267
theorem R24939 : Reach 24939 := rs (se 1 (by rfl) ⟨18704, by rfl⟩) R37409
theorem R24951 : Reach 24951 := rs (se 1 (by rfl) ⟨18713, by rfl⟩) R37427
theorem R24971 : Reach 24971 := rs (se 1 (by rfl) ⟨18728, by rfl⟩) R37457
theorem R24983 : Reach 24983 := rs (se 1 (by rfl) ⟨18737, by rfl⟩) R37475
theorem R25003 : Reach 25003 := rs (se 1 (by rfl) ⟨18752, by rfl⟩) R37505
theorem R57779 : Reach 57779 := rs (se 1 (by rfl) ⟨43334, by rfl⟩) R86669
theorem R25015 : Reach 25015 := rs (se 1 (by rfl) ⟨18761, by rfl⟩) R37523
theorem R25035 : Reach 25035 := rs (se 1 (by rfl) ⟨18776, by rfl⟩) R37553
theorem R25047 : Reach 25047 := rs (se 1 (by rfl) ⟨18785, by rfl⟩) R37571
theorem R25067 : Reach 25067 := rs (se 1 (by rfl) ⟨18800, by rfl⟩) R37601
theorem R25079 : Reach 25079 := rs (se 1 (by rfl) ⟨18809, by rfl⟩) R37619
theorem R25099 : Reach 25099 := rs (se 1 (by rfl) ⟨18824, by rfl⟩) R37649
theorem R25111 : Reach 25111 := rs (se 1 (by rfl) ⟨18833, by rfl⟩) R37667
theorem R25131 : Reach 25131 := rs (se 1 (by rfl) ⟨18848, by rfl⟩) R37697
theorem R25143 : Reach 25143 := rs (se 1 (by rfl) ⟨18857, by rfl⟩) R37715
theorem R25163 : Reach 25163 := rs (se 1 (by rfl) ⟨18872, by rfl⟩) R37745
theorem R25175 : Reach 25175 := rs (se 1 (by rfl) ⟨18881, by rfl⟩) R37763
theorem R25195 : Reach 25195 := rs (se 1 (by rfl) ⟨18896, by rfl⟩) R37793
theorem R25207 : Reach 25207 := rs (se 1 (by rfl) ⟨18905, by rfl⟩) R37811
theorem R25227 : Reach 25227 := rs (se 1 (by rfl) ⟨18920, by rfl⟩) R37841
theorem R25239 : Reach 25239 := rs (se 1 (by rfl) ⟨18929, by rfl⟩) R37859
theorem R25259 : Reach 25259 := rs (se 1 (by rfl) ⟨18944, by rfl⟩) R37889
theorem R25271 : Reach 25271 := rs (se 1 (by rfl) ⟨18953, by rfl⟩) R37907
theorem R58049 : Reach 58049 := rs (se 2 (by rfl) ⟨21768, by rfl⟩) R43537
theorem R25291 : Reach 25291 := rs (se 1 (by rfl) ⟨18968, by rfl⟩) R37937
theorem R90827 : Reach 90827 := rs (se 1 (by rfl) ⟨68120, by rfl⟩) R136241
theorem R25303 : Reach 25303 := rs (se 1 (by rfl) ⟨18977, by rfl⟩) R37955
theorem R25323 : Reach 25323 := rs (se 1 (by rfl) ⟨18992, by rfl⟩) R37985
theorem R25335 : Reach 25335 := rs (se 1 (by rfl) ⟨19001, by rfl⟩) R38003
theorem R25355 : Reach 25355 := rs (se 1 (by rfl) ⟨19016, by rfl⟩) R38033
theorem R25367 : Reach 25367 := rs (se 1 (by rfl) ⟨19025, by rfl⟩) R38051
theorem R25387 : Reach 25387 := rs (se 1 (by rfl) ⟨19040, by rfl⟩) R38081
theorem R25399 : Reach 25399 := rs (se 1 (by rfl) ⟨19049, by rfl⟩) R38099
theorem R25419 : Reach 25419 := rs (se 1 (by rfl) ⟨19064, by rfl⟩) R38129
theorem R25431 : Reach 25431 := rs (se 1 (by rfl) ⟨19073, by rfl⟩) R38147
theorem R25451 : Reach 25451 := rs (se 1 (by rfl) ⟨19088, by rfl⟩) R38177
theorem R25463 : Reach 25463 := rs (se 1 (by rfl) ⟨19097, by rfl⟩) R38195
theorem R25483 : Reach 25483 := rs (se 1 (by rfl) ⟨19112, by rfl⟩) R38225
theorem R25495 : Reach 25495 := rs (se 1 (by rfl) ⟨19121, by rfl⟩) R38243
theorem R25515 : Reach 25515 := rs (se 1 (by rfl) ⟨19136, by rfl⟩) R38273
theorem R25527 : Reach 25527 := rs (se 1 (by rfl) ⟨19145, by rfl⟩) R38291
theorem R25547 : Reach 25547 := rs (se 1 (by rfl) ⟨19160, by rfl⟩) R38321
theorem R58315 : Reach 58315 := rs (se 1 (by rfl) ⟨43736, by rfl⟩) R87473
theorem R25559 : Reach 25559 := rs (se 1 (by rfl) ⟨19169, by rfl⟩) R38339
theorem R91097 : Reach 91097 := rs (se 2 (by rfl) ⟨34161, by rfl⟩) R68323
theorem R25579 : Reach 25579 := rs (se 1 (by rfl) ⟨19184, by rfl⟩) R38369
theorem R25591 : Reach 25591 := rs (se 1 (by rfl) ⟨19193, by rfl⟩) R38387
theorem R25611 : Reach 25611 := rs (se 1 (by rfl) ⟨19208, by rfl⟩) R38417
theorem R2057237 : Reach 2057237 := rs (se 6 (by rfl) ⟨48216, by rfl⟩) R96433
theorem R25623 : Reach 25623 := rs (se 1 (by rfl) ⟨19217, by rfl⟩) R38435
theorem R58391 : Reach 58391 := rs (se 1 (by rfl) ⟨43793, by rfl⟩) R87587
theorem R25643 : Reach 25643 := rs (se 1 (by rfl) ⟨19232, by rfl⟩) R38465
theorem R25655 : Reach 25655 := rs (se 1 (by rfl) ⟨19241, by rfl⟩) R38483
theorem R25675 : Reach 25675 := rs (se 1 (by rfl) ⟨19256, by rfl⟩) R38513
theorem R25687 : Reach 25687 := rs (se 1 (by rfl) ⟨19265, by rfl⟩) R38531
theorem R25707 : Reach 25707 := rs (se 1 (by rfl) ⟨19280, by rfl⟩) R38561
theorem R25719 : Reach 25719 := rs (se 1 (by rfl) ⟨19289, by rfl⟩) R38579
theorem R25739 : Reach 25739 := rs (se 1 (by rfl) ⟨19304, by rfl⟩) R38609
theorem R25751 : Reach 25751 := rs (se 1 (by rfl) ⟨19313, by rfl⟩) R38627
theorem R25771 : Reach 25771 := rs (se 1 (by rfl) ⟨19328, by rfl⟩) R38657
theorem R25783 : Reach 25783 := rs (se 1 (by rfl) ⟨19337, by rfl⟩) R38675
theorem R25803 : Reach 25803 := rs (se 1 (by rfl) ⟨19352, by rfl⟩) R38705
theorem R58571 : Reach 58571 := rs (se 1 (by rfl) ⟨43928, by rfl⟩) R87857
theorem R25815 : Reach 25815 := rs (se 1 (by rfl) ⟨19361, by rfl⟩) R38723
theorem R25835 : Reach 25835 := rs (se 1 (by rfl) ⟨19376, by rfl⟩) R38753
theorem R25847 : Reach 25847 := rs (se 1 (by rfl) ⟨19385, by rfl⟩) R38771
theorem R25867 : Reach 25867 := rs (se 1 (by rfl) ⟨19400, by rfl⟩) R38801
theorem R25879 : Reach 25879 := rs (se 1 (by rfl) ⟨19409, by rfl⟩) R38819
theorem R25899 : Reach 25899 := rs (se 1 (by rfl) ⟨19424, by rfl⟩) R38849
theorem R25911 : Reach 25911 := rs (se 1 (by rfl) ⟨19433, by rfl⟩) R38867
theorem R25931 : Reach 25931 := rs (se 1 (by rfl) ⟨19448, by rfl⟩) R38897
theorem R25943 : Reach 25943 := rs (se 1 (by rfl) ⟨19457, by rfl⟩) R38915
theorem R124253 : Reach 124253 := rs (se 3 (by rfl) ⟨23297, by rfl⟩) R46595
theorem R25963 : Reach 25963 := rs (se 1 (by rfl) ⟨19472, by rfl⟩) R38945
theorem R25975 : Reach 25975 := rs (se 1 (by rfl) ⟨19481, by rfl⟩) R38963
theorem R25995 : Reach 25995 := rs (se 1 (by rfl) ⟨19496, by rfl⟩) R38993
theorem R26007 : Reach 26007 := rs (se 1 (by rfl) ⟨19505, by rfl⟩) R39011
theorem R26027 : Reach 26027 := rs (se 1 (by rfl) ⟨19520, by rfl⟩) R39041
theorem R26039 : Reach 26039 := rs (se 1 (by rfl) ⟨19529, by rfl⟩) R39059
theorem R26059 : Reach 26059 := rs (se 1 (by rfl) ⟨19544, by rfl⟩) R39089
theorem R26071 : Reach 26071 := rs (se 1 (by rfl) ⟨19553, by rfl⟩) R39107
theorem R58841 : Reach 58841 := rs (se 2 (by rfl) ⟨22065, by rfl⟩) R44131
theorem R26091 : Reach 26091 := rs (se 1 (by rfl) ⟨19568, by rfl⟩) R39137
theorem R26103 : Reach 26103 := rs (se 1 (by rfl) ⟨19577, by rfl⟩) R39155
theorem R26123 : Reach 26123 := rs (se 1 (by rfl) ⟨19592, by rfl⟩) R39185
theorem R26135 : Reach 26135 := rs (se 1 (by rfl) ⟨19601, by rfl⟩) R39203
theorem R26155 : Reach 26155 := rs (se 1 (by rfl) ⟨19616, by rfl⟩) R39233
theorem R58931 : Reach 58931 := rs (se 1 (by rfl) ⟨44198, by rfl⟩) R88397
theorem R26167 : Reach 26167 := rs (se 1 (by rfl) ⟨19625, by rfl⟩) R39251
theorem R26187 : Reach 26187 := rs (se 1 (by rfl) ⟨19640, by rfl⟩) R39281
theorem R26199 : Reach 26199 := rs (se 1 (by rfl) ⟨19649, by rfl⟩) R39299
theorem R26219 : Reach 26219 := rs (se 1 (by rfl) ⟨19664, by rfl⟩) R39329
theorem R26231 : Reach 26231 := rs (se 1 (by rfl) ⟨19673, by rfl⟩) R39347
theorem R26251 : Reach 26251 := rs (se 1 (by rfl) ⟨19688, by rfl⟩) R39377
theorem R91793 : Reach 91793 := rs (se 2 (by rfl) ⟨34422, by rfl⟩) R68845
theorem R26263 : Reach 26263 := rs (se 1 (by rfl) ⟨19697, by rfl⟩) R39395
theorem R91799 : Reach 91799 := rs (se 1 (by rfl) ⟨68849, by rfl⟩) R137699
theorem R26283 : Reach 26283 := rs (se 1 (by rfl) ⟨19712, by rfl⟩) R39425
theorem R26295 : Reach 26295 := rs (se 1 (by rfl) ⟨19721, by rfl⟩) R39443
theorem R26315 : Reach 26315 := rs (se 1 (by rfl) ⟨19736, by rfl⟩) R39473
theorem R26327 : Reach 26327 := rs (se 1 (by rfl) ⟨19745, by rfl⟩) R39491
theorem R26347 : Reach 26347 := rs (se 1 (by rfl) ⟨19760, by rfl⟩) R39521
theorem R26359 : Reach 26359 := rs (se 1 (by rfl) ⟨19769, by rfl⟩) R39539
theorem R26379 : Reach 26379 := rs (se 1 (by rfl) ⟨19784, by rfl⟩) R39569
theorem R26391 : Reach 26391 := rs (se 1 (by rfl) ⟨19793, by rfl⟩) R39587
theorem R26411 : Reach 26411 := rs (se 1 (by rfl) ⟨19808, by rfl⟩) R39617
theorem R26423 : Reach 26423 := rs (se 1 (by rfl) ⟨19817, by rfl⟩) R39635
theorem R59201 : Reach 59201 := rs (se 2 (by rfl) ⟨22200, by rfl⟩) R44401
theorem R26443 : Reach 26443 := rs (se 1 (by rfl) ⟨19832, by rfl⟩) R39665
theorem R26455 : Reach 26455 := rs (se 1 (by rfl) ⟨19841, by rfl⟩) R39683
theorem R26475 : Reach 26475 := rs (se 1 (by rfl) ⟨19856, by rfl⟩) R39713
theorem R26487 : Reach 26487 := rs (se 1 (by rfl) ⟨19865, by rfl⟩) R39731
theorem R26507 : Reach 26507 := rs (se 1 (by rfl) ⟨19880, by rfl⟩) R39761
theorem R26519 : Reach 26519 := rs (se 1 (by rfl) ⟨19889, by rfl⟩) R39779
theorem R26539 : Reach 26539 := rs (se 1 (by rfl) ⟨19904, by rfl⟩) R39809
theorem R26551 : Reach 26551 := rs (se 1 (by rfl) ⟨19913, by rfl⟩) R39827
theorem R26571 : Reach 26571 := rs (se 1 (by rfl) ⟨19928, by rfl⟩) R39857
theorem R26583 : Reach 26583 := rs (se 1 (by rfl) ⟨19937, by rfl⟩) R39875
theorem R26603 : Reach 26603 := rs (se 1 (by rfl) ⟨19952, by rfl⟩) R39905
theorem R26615 : Reach 26615 := rs (se 1 (by rfl) ⟨19961, by rfl⟩) R39923
theorem R26635 : Reach 26635 := rs (se 1 (by rfl) ⟨19976, by rfl⟩) R39953
theorem R26647 : Reach 26647 := rs (se 1 (by rfl) ⟨19985, by rfl⟩) R39971
theorem R26667 : Reach 26667 := rs (se 1 (by rfl) ⟨20000, by rfl⟩) R40001
theorem R26679 : Reach 26679 := rs (se 1 (by rfl) ⟨20009, by rfl⟩) R40019
theorem R26699 : Reach 26699 := rs (se 1 (by rfl) ⟨20024, by rfl⟩) R40049
theorem R26711 : Reach 26711 := rs (se 1 (by rfl) ⟨20033, by rfl⟩) R40067
theorem R92249 : Reach 92249 := rs (se 2 (by rfl) ⟨34593, by rfl⟩) R69187
theorem R26731 : Reach 26731 := rs (se 1 (by rfl) ⟨20048, by rfl⟩) R40097
theorem R26743 : Reach 26743 := rs (se 1 (by rfl) ⟨20057, by rfl⟩) R40115
theorem R26763 : Reach 26763 := rs (se 1 (by rfl) ⟨20072, by rfl⟩) R40145
theorem R59543 : Reach 59543 := rs (se 1 (by rfl) ⟨44657, by rfl⟩) R89315
theorem R26775 : Reach 26775 := rs (se 1 (by rfl) ⟨20081, by rfl⟩) R40163
theorem R26795 : Reach 26795 := rs (se 1 (by rfl) ⟨20096, by rfl⟩) R40193
theorem R583861 : Reach 583861 := rs (se 5 (by rfl) ⟨27368, by rfl⟩) R54737
theorem R26807 : Reach 26807 := rs (se 1 (by rfl) ⟨20105, by rfl⟩) R40211
theorem R26827 : Reach 26827 := rs (se 1 (by rfl) ⟨20120, by rfl⟩) R40241
theorem R26839 : Reach 26839 := rs (se 1 (by rfl) ⟨20129, by rfl⟩) R40259
theorem R26859 : Reach 26859 := rs (se 1 (by rfl) ⟨20144, by rfl⟩) R40289
theorem R26871 : Reach 26871 := rs (se 1 (by rfl) ⟨20153, by rfl⟩) R40307
theorem R26891 : Reach 26891 := rs (se 1 (by rfl) ⟨20168, by rfl⟩) R40337
theorem R26903 : Reach 26903 := rs (se 1 (by rfl) ⟨20177, by rfl⟩) R40355
theorem R26923 : Reach 26923 := rs (se 1 (by rfl) ⟨20192, by rfl⟩) R40385
theorem R92461 : Reach 92461 := rs (se 3 (by rfl) ⟨17336, by rfl⟩) R34673
theorem R26935 : Reach 26935 := rs (se 1 (by rfl) ⟨20201, by rfl⟩) R40403
theorem R59723 : Reach 59723 := rs (se 1 (by rfl) ⟨44792, by rfl⟩) R89585
theorem R26955 : Reach 26955 := rs (se 1 (by rfl) ⟨20216, by rfl⟩) R40433
theorem R26967 : Reach 26967 := rs (se 1 (by rfl) ⟨20225, by rfl⟩) R40451
theorem R59737 : Reach 59737 := rs (se 2 (by rfl) ⟨22401, by rfl⟩) R44803
theorem R26987 : Reach 26987 := rs (se 1 (by rfl) ⟨20240, by rfl⟩) R40481
theorem R26999 : Reach 26999 := rs (se 1 (by rfl) ⟨20249, by rfl⟩) R40499
theorem R27019 : Reach 27019 := rs (se 1 (by rfl) ⟨20264, by rfl⟩) R40529
theorem R27031 : Reach 27031 := rs (se 1 (by rfl) ⟨20273, by rfl⟩) R40547
theorem R27051 : Reach 27051 := rs (se 1 (by rfl) ⟨20288, by rfl⟩) R40577
theorem R27063 : Reach 27063 := rs (se 1 (by rfl) ⟨20297, by rfl⟩) R40595
theorem R27083 : Reach 27083 := rs (se 1 (by rfl) ⟨20312, by rfl⟩) R40625
theorem R27095 : Reach 27095 := rs (se 1 (by rfl) ⟨20321, by rfl⟩) R40643
theorem R27211 : Reach 27211 := rs (se 1 (by rfl) ⟨20408, by rfl⟩) R40817
theorem R59993 : Reach 59993 := rs (se 2 (by rfl) ⟨22497, by rfl⟩) R44995
theorem R92765 : Reach 92765 := rs (se 3 (by rfl) ⟨17393, by rfl⟩) R34787
theorem R60083 : Reach 60083 := rs (se 1 (by rfl) ⟨45062, by rfl⟩) R90125
theorem R27319 : Reach 27319 := rs (se 1 (by rfl) ⟨20489, by rfl⟩) R40979
theorem R27415 : Reach 27415 := rs (se 1 (by rfl) ⟨20561, by rfl⟩) R41123
theorem R27479 : Reach 27479 := rs (se 1 (by rfl) ⟨20609, by rfl⟩) R41219
theorem R27499 : Reach 27499 := rs (se 1 (by rfl) ⟨20624, by rfl⟩) R41249
theorem R60353 : Reach 60353 := rs (se 2 (by rfl) ⟨22632, by rfl⟩) R45265
theorem R27607 : Reach 27607 := rs (se 1 (by rfl) ⟨20705, by rfl⟩) R41411
theorem R93187 : Reach 93187 := rs (se 1 (by rfl) ⟨69890, by rfl⟩) R139781
theorem R27787 : Reach 27787 := rs (se 1 (by rfl) ⟨20840, by rfl⟩) R41681
theorem R60695 : Reach 60695 := rs (se 1 (by rfl) ⟨45521, by rfl⟩) R91043
theorem R93485 : Reach 93485 := rs (se 3 (by rfl) ⟨17528, by rfl⟩) R35057
theorem R126359 : Reach 126359 := rs (se 1 (by rfl) ⟨94769, by rfl⟩) R189539
theorem R60851 : Reach 60851 := rs (se 1 (by rfl) ⟨45638, by rfl⟩) R91277
theorem R60875 : Reach 60875 := rs (se 1 (by rfl) ⟨45656, by rfl⟩) R91313
theorem R126481 : Reach 126481 := rs (se 2 (by rfl) ⟨47430, by rfl⟩) R94861
theorem R28183 : Reach 28183 := rs (se 1 (by rfl) ⟨21137, by rfl⟩) R42275
theorem R28235 : Reach 28235 := rs (se 1 (by rfl) ⟨21176, by rfl⟩) R42353
theorem R28363 : Reach 28363 := rs (se 1 (by rfl) ⟨21272, by rfl⟩) R42545
theorem R61145 : Reach 61145 := rs (se 2 (by rfl) ⟨22929, by rfl⟩) R45859
theorem R225125 : Reach 225125 := rs (se 4 (by rfl) ⟨21105, by rfl⟩) R42211
theorem R126937 : Reach 126937 := rs (se 2 (by rfl) ⟨47601, by rfl⟩) R95203
theorem R192577 : Reach 192577 := rs (se 2 (by rfl) ⟨72216, by rfl⟩) R144433
theorem R28759 : Reach 28759 := rs (se 1 (by rfl) ⟨21569, by rfl⟩) R43139
theorem R28939 : Reach 28939 := rs (se 1 (by rfl) ⟨21704, by rfl⟩) R43409
theorem R192833 : Reach 192833 := rs (se 2 (by rfl) ⟨72312, by rfl⟩) R144625
theorem R127325 : Reach 127325 := rs (se 3 (by rfl) ⟨23873, by rfl⟩) R47747
theorem R29335 : Reach 29335 := rs (se 1 (by rfl) ⟨22001, by rfl⟩) R44003
theorem R62155 : Reach 62155 := rs (se 1 (by rfl) ⟨46616, by rfl⟩) R93233
theorem R29515 : Reach 29515 := rs (se 1 (by rfl) ⟨22136, by rfl⟩) R44273
theorem R160643 : Reach 160643 := rs (se 1 (by rfl) ⟨120482, by rfl⟩) R240965
theorem R488369 : Reach 488369 := rs (se 2 (by rfl) ⟨183138, by rfl⟩) R366277
theorem R291761 : Reach 291761 := rs (se 2 (by rfl) ⟨109410, by rfl⟩) R218821
theorem R128017 : Reach 128017 := rs (se 2 (by rfl) ⟨48006, by rfl⟩) R96013
theorem R422981 : Reach 422981 := rs (se 4 (by rfl) ⟨39654, by rfl⟩) R79309
theorem R95363 : Reach 95363 := rs (se 1 (by rfl) ⟨71522, by rfl⟩) R143045
theorem R95377 : Reach 95377 := rs (se 2 (by rfl) ⟨35766, by rfl⟩) R71533
theorem R29899 : Reach 29899 := rs (se 1 (by rfl) ⟨22424, by rfl⟩) R44849
theorem R29911 : Reach 29911 := rs (se 1 (by rfl) ⟨22433, by rfl⟩) R44867
theorem R161041 : Reach 161041 := rs (se 2 (by rfl) ⟨60390, by rfl⟩) R120781
theorem R62795 : Reach 62795 := rs (se 1 (by rfl) ⟨47096, by rfl⟩) R94193
theorem R30091 : Reach 30091 := rs (se 1 (by rfl) ⟨22568, by rfl⟩) R45137
theorem R95681 : Reach 95681 := rs (se 2 (by rfl) ⟨35880, by rfl⟩) R71761
theorem R95917 : Reach 95917 := rs (se 3 (by rfl) ⟨17984, by rfl⟩) R35969
theorem R30487 : Reach 30487 := rs (se 1 (by rfl) ⟨22865, by rfl⟩) R45731
theorem R292709 : Reach 292709 := rs (se 4 (by rfl) ⟨27441, by rfl⟩) R54883
theorem R96331 : Reach 96331 := rs (se 1 (by rfl) ⟨72248, by rfl⟩) R144497
theorem R96349 : Reach 96349 := rs (se 3 (by rfl) ⟨18065, by rfl⟩) R36131
theorem R30871 : Reach 30871 := rs (se 1 (by rfl) ⟨23153, by rfl⟩) R46307
theorem R63767 : Reach 63767 := rs (se 1 (by rfl) ⟨47825, by rfl⟩) R95651
theorem R326105 : Reach 326105 := rs (se 2 (by rfl) ⟨122289, by rfl⟩) R244579
theorem R359063 : Reach 359063 := rs (se 1 (by rfl) ⟨269297, by rfl⟩) R538595
theorem R129923 : Reach 129923 := rs (se 1 (by rfl) ⟨97442, by rfl⟩) R194885
theorem R64435 : Reach 64435 := rs (se 1 (by rfl) ⟨48326, by rfl⟩) R96653
theorem R31691 : Reach 31691 := rs (se 1 (by rfl) ⟨23768, by rfl⟩) R47537
theorem R195533 : Reach 195533 := rs (se 3 (by rfl) ⟨36662, by rfl⟩) R73325
theorem R64577 : Reach 64577 := rs (se 2 (by rfl) ⟨24216, by rfl⟩) R48433
theorem R195857 : Reach 195857 := rs (se 2 (by rfl) ⟨73446, by rfl⟩) R146893
theorem R97625 : Reach 97625 := rs (se 2 (by rfl) ⟨36609, by rfl⟩) R73219
theorem R65117 : Reach 65117 := rs (se 3 (by rfl) ⟨12209, by rfl⟩) R24419
theorem R32395 : Reach 32395 := rs (se 1 (by rfl) ⟨24296, by rfl⟩) R48593
theorem R65245 : Reach 65245 := rs (se 3 (by rfl) ⟨12233, by rfl⟩) R24467
theorem R32663 : Reach 32663 := rs (se 1 (by rfl) ⟨24497, by rfl⟩) R48995
theorem R32665 : Reach 32665 := rs (se 2 (by rfl) ⟨12249, by rfl⟩) R24499
theorem R32783 : Reach 32783 := rs (se 1 (by rfl) ⟨24587, by rfl⟩) R49175
theorem R65569 : Reach 65569 := rs (se 2 (by rfl) ⟨24588, by rfl⟩) R49177
theorem R32825 : Reach 32825 := rs (se 2 (by rfl) ⟨12309, by rfl⟩) R24619
theorem R164231 : Reach 164231 := rs (se 1 (by rfl) ⟨123173, by rfl⟩) R246347
theorem R229817 : Reach 229817 := rs (se 2 (by rfl) ⟨86181, by rfl⟩) R172363
theorem R66167 : Reach 66167 := rs (se 1 (by rfl) ⟨49625, by rfl⟩) R99251
theorem R99053 : Reach 99053 := rs (se 3 (by rfl) ⟨18572, by rfl⟩) R37145
theorem R132353 : Reach 132353 := rs (se 2 (by rfl) ⟨49632, by rfl⟩) R99265
theorem R66845 : Reach 66845 := rs (se 3 (by rfl) ⟨12533, by rfl⟩) R25067
theorem R34121 : Reach 34121 := rs (se 2 (by rfl) ⟨12795, by rfl⟩) R25591
theorem R99737 : Reach 99737 := rs (se 2 (by rfl) ⟨37401, by rfl⟩) R74803
theorem R67159 : Reach 67159 := rs (se 1 (by rfl) ⟨50369, by rfl⟩) R100739
theorem R67387 : Reach 67387 := rs (se 1 (by rfl) ⟨50540, by rfl⟩) R101081
theorem R67463 : Reach 67463 := rs (se 1 (by rfl) ⟨50597, by rfl⟩) R101195
theorem R67513 : Reach 67513 := rs (se 2 (by rfl) ⟨25317, by rfl⟩) R50635
theorem R133123 : Reach 133123 := rs (se 1 (by rfl) ⟨99842, by rfl⟩) R199685
theorem R133163 : Reach 133163 := rs (se 1 (by rfl) ⟨99872, by rfl⟩) R199745
theorem R34987 : Reach 34987 := rs (se 1 (by rfl) ⟨26240, by rfl⟩) R52481
theorem R100723 : Reach 100723 := rs (se 1 (by rfl) ⟨75542, by rfl⟩) R151085
theorem R35273 : Reach 35273 := rs (se 2 (by rfl) ⟨13227, by rfl⟩) R26455
theorem R68111 : Reach 68111 := rs (se 1 (by rfl) ⟨51083, by rfl⟩) R102167
theorem R35387 : Reach 35387 := rs (se 1 (by rfl) ⟨26540, by rfl⟩) R53081
theorem R35447 : Reach 35447 := rs (se 1 (by rfl) ⟨26585, by rfl⟩) R53171
theorem R35471 : Reach 35471 := rs (se 1 (by rfl) ⟨26603, by rfl⟩) R53207
theorem R494261 : Reach 494261 := rs (se 5 (by rfl) ⟨23168, by rfl⟩) R46337
theorem R35513 : Reach 35513 := rs (se 2 (by rfl) ⟨13317, by rfl⟩) R26635
theorem R35591 : Reach 35591 := rs (se 1 (by rfl) ⟨26693, by rfl⟩) R53387
theorem R35627 : Reach 35627 := rs (se 1 (by rfl) ⟨26720, by rfl⟩) R53441
theorem R35657 : Reach 35657 := rs (se 2 (by rfl) ⟨13371, by rfl⟩) R26743
theorem R35771 : Reach 35771 := rs (se 1 (by rfl) ⟨26828, by rfl⟩) R53657
theorem R35831 : Reach 35831 := rs (se 1 (by rfl) ⟨26873, by rfl⟩) R53747
theorem R35855 : Reach 35855 := rs (se 1 (by rfl) ⟨26891, by rfl⟩) R53783
theorem R35897 : Reach 35897 := rs (se 2 (by rfl) ⟨13461, by rfl⟩) R26923
theorem R68723 : Reach 68723 := rs (se 1 (by rfl) ⟨51542, by rfl⟩) R103085
theorem R35975 : Reach 35975 := rs (se 1 (by rfl) ⟨26981, by rfl⟩) R53963
theorem R36011 : Reach 36011 := rs (se 1 (by rfl) ⟨27008, by rfl⟩) R54017
theorem R36041 : Reach 36041 := rs (se 2 (by rfl) ⟨13515, by rfl⟩) R27031
theorem R363809 : Reach 363809 := rs (se 2 (by rfl) ⟨136428, by rfl⟩) R272857
theorem R36155 : Reach 36155 := rs (se 1 (by rfl) ⟨27116, by rfl⟩) R54233
theorem R134459 : Reach 134459 := rs (se 1 (by rfl) ⟨100844, by rfl⟩) R201689
theorem R36215 : Reach 36215 := rs (se 1 (by rfl) ⟨27161, by rfl⟩) R54323
theorem R36239 : Reach 36239 := rs (se 1 (by rfl) ⟨27179, by rfl⟩) R54359
theorem R36281 : Reach 36281 := rs (se 2 (by rfl) ⟨13605, by rfl⟩) R27211
theorem R134621 : Reach 134621 := rs (se 3 (by rfl) ⟨25241, by rfl⟩) R50483
theorem R36359 : Reach 36359 := rs (se 1 (by rfl) ⟨27269, by rfl⟩) R54539
theorem R36395 : Reach 36395 := rs (se 1 (by rfl) ⟨27296, by rfl⟩) R54593
theorem R36425 : Reach 36425 := rs (se 2 (by rfl) ⟨13659, by rfl⟩) R27319
theorem R36539 : Reach 36539 := rs (se 1 (by rfl) ⟨27404, by rfl⟩) R54809
theorem R36553 : Reach 36553 := rs (se 2 (by rfl) ⟨13707, by rfl⟩) R27415
theorem R36599 : Reach 36599 := rs (se 1 (by rfl) ⟨27449, by rfl⟩) R54899
theorem R36623 : Reach 36623 := rs (se 1 (by rfl) ⟨27467, by rfl⟩) R54935
theorem R134945 : Reach 134945 := rs (se 2 (by rfl) ⟨50604, by rfl⟩) R101209
theorem R36665 : Reach 36665 := rs (se 2 (by rfl) ⟨13749, by rfl⟩) R27499
theorem R69437 : Reach 69437 := rs (se 3 (by rfl) ⟨13019, by rfl⟩) R26039
theorem R135047 : Reach 135047 := rs (se 1 (by rfl) ⟨101285, by rfl⟩) R202571
theorem R36743 : Reach 36743 := rs (se 1 (by rfl) ⟨27557, by rfl⟩) R55115
theorem R36779 : Reach 36779 := rs (se 1 (by rfl) ⟨27584, by rfl⟩) R55169
theorem R36809 : Reach 36809 := rs (se 2 (by rfl) ⟨13803, by rfl⟩) R27607
theorem R36923 : Reach 36923 := rs (se 1 (by rfl) ⟨27692, by rfl⟩) R55385
theorem R135229 : Reach 135229 := rs (se 3 (by rfl) ⟨25355, by rfl⟩) R50711
theorem R36983 : Reach 36983 := rs (se 1 (by rfl) ⟨27737, by rfl⟩) R55475
theorem R37007 : Reach 37007 := rs (se 1 (by rfl) ⟨27755, by rfl⟩) R55511
theorem R37049 : Reach 37049 := rs (se 2 (by rfl) ⟨13893, by rfl⟩) R27787
theorem R37111 : Reach 37111 := rs (se 1 (by rfl) ⟨27833, by rfl⟩) R55667
theorem R37127 : Reach 37127 := rs (se 1 (by rfl) ⟨27845, by rfl⟩) R55691
theorem R37163 : Reach 37163 := rs (se 1 (by rfl) ⟨27872, by rfl⟩) R55745
theorem R37391 : Reach 37391 := rs (se 1 (by rfl) ⟨28043, by rfl⟩) R56087
theorem R102941 : Reach 102941 := rs (se 3 (by rfl) ⟨19301, by rfl⟩) R38603
theorem R37511 : Reach 37511 := rs (se 1 (by rfl) ⟨28133, by rfl⟩) R56267
theorem R168641 : Reach 168641 := rs (se 2 (by rfl) ⟨63240, by rfl⟩) R126481
theorem R37577 : Reach 37577 := rs (se 2 (by rfl) ⟨14091, by rfl⟩) R28183
theorem R135917 : Reach 135917 := rs (se 3 (by rfl) ⟨25484, by rfl⟩) R50969
theorem R70429 : Reach 70429 := rs (se 3 (by rfl) ⟨13205, by rfl⟩) R26411
theorem R37675 : Reach 37675 := rs (se 1 (by rfl) ⟨28256, by rfl⟩) R56513
theorem R37691 : Reach 37691 := rs (se 1 (by rfl) ⟨28268, by rfl⟩) R56537
theorem R37751 : Reach 37751 := rs (se 1 (by rfl) ⟨28313, by rfl⟩) R56627
theorem R37817 : Reach 37817 := rs (se 2 (by rfl) ⟨14181, by rfl⟩) R28363
theorem R37903 : Reach 37903 := rs (se 1 (by rfl) ⟨28427, by rfl⟩) R56855
theorem R37931 : Reach 37931 := rs (se 1 (by rfl) ⟨28448, by rfl⟩) R56897
theorem R38159 : Reach 38159 := rs (se 1 (by rfl) ⟨28619, by rfl⟩) R57239
theorem R169249 : Reach 169249 := rs (se 2 (by rfl) ⟨63468, by rfl⟩) R126937
theorem R300347 : Reach 300347 := rs (se 1 (by rfl) ⟨225260, by rfl⟩) R450521
theorem R38279 : Reach 38279 := rs (se 1 (by rfl) ⟨28709, by rfl⟩) R57419
theorem R71047 : Reach 71047 := rs (se 1 (by rfl) ⟨53285, by rfl⟩) R106571
theorem R38345 : Reach 38345 := rs (se 2 (by rfl) ⟨14379, by rfl⟩) R28759
theorem R136727 : Reach 136727 := rs (se 1 (by rfl) ⟨102545, by rfl⟩) R205091
theorem R38459 : Reach 38459 := rs (se 1 (by rfl) ⟨28844, by rfl⟩) R57689
theorem R38519 : Reach 38519 := rs (se 1 (by rfl) ⟨28889, by rfl⟩) R57779
theorem R38585 : Reach 38585 := rs (se 2 (by rfl) ⟨14469, by rfl⟩) R28939
theorem R136961 : Reach 136961 := rs (se 2 (by rfl) ⟨51360, by rfl⟩) R102721
theorem R136997 : Reach 136997 := rs (se 4 (by rfl) ⟨12843, by rfl⟩) R25687
theorem R38699 : Reach 38699 := rs (se 1 (by rfl) ⟨29024, by rfl⟩) R58049
theorem R38927 : Reach 38927 := rs (se 1 (by rfl) ⟨29195, by rfl⟩) R58391
theorem R39047 : Reach 39047 := rs (se 1 (by rfl) ⟨29285, by rfl⟩) R58571
theorem R202925 : Reach 202925 := rs (se 3 (by rfl) ⟨38048, by rfl⟩) R76097
theorem R39113 : Reach 39113 := rs (se 2 (by rfl) ⟨14667, by rfl⟩) R29335
theorem R39227 : Reach 39227 := rs (se 1 (by rfl) ⟨29420, by rfl⟩) R58841
theorem R39287 : Reach 39287 := rs (se 1 (by rfl) ⟨29465, by rfl⟩) R58931
theorem R39353 : Reach 39353 := rs (se 2 (by rfl) ⟨14757, by rfl⟩) R29515
theorem R39467 : Reach 39467 := rs (se 1 (by rfl) ⟨29600, by rfl⟩) R59201
theorem R72377 : Reach 72377 := rs (se 2 (by rfl) ⟨27141, by rfl⟩) R54283
theorem R170689 : Reach 170689 := rs (se 2 (by rfl) ⟨64008, by rfl⟩) R128017
theorem R39695 : Reach 39695 := rs (se 1 (by rfl) ⟨29771, by rfl⟩) R59543
theorem R39815 : Reach 39815 := rs (se 1 (by rfl) ⟨29861, by rfl⟩) R59723
theorem R39865 : Reach 39865 := rs (se 2 (by rfl) ⟨14949, by rfl⟩) R29899
theorem R39881 : Reach 39881 := rs (se 2 (by rfl) ⟨14955, by rfl⟩) R29911
theorem R39995 : Reach 39995 := rs (se 1 (by rfl) ⟨29996, by rfl⟩) R59993
theorem R40055 : Reach 40055 := rs (se 1 (by rfl) ⟨30041, by rfl⟩) R60083
theorem R40121 : Reach 40121 := rs (se 2 (by rfl) ⟨15045, by rfl⟩) R30091
theorem R40235 : Reach 40235 := rs (se 1 (by rfl) ⟨30176, by rfl⟩) R60353
theorem R499121 : Reach 499121 := rs (se 2 (by rfl) ⟨187170, by rfl⟩) R374341
theorem R40463 : Reach 40463 := rs (se 1 (by rfl) ⟨30347, by rfl⟩) R60695
theorem R73277 : Reach 73277 := rs (se 3 (by rfl) ⟨13739, by rfl⟩) R27479
theorem R40567 : Reach 40567 := rs (se 1 (by rfl) ⟨30425, by rfl⟩) R60851
theorem R40583 : Reach 40583 := rs (se 1 (by rfl) ⟨30437, by rfl⟩) R60875
theorem R204481 : Reach 204481 := rs (se 2 (by rfl) ⟨76680, by rfl⟩) R153361
theorem R40649 : Reach 40649 := rs (se 2 (by rfl) ⟨15243, by rfl⟩) R30487
theorem R40763 : Reach 40763 := rs (se 1 (by rfl) ⟨30572, by rfl⟩) R61145
theorem R73619 : Reach 73619 := rs (se 1 (by rfl) ⟨55214, by rfl⟩) R110429
theorem R172205 : Reach 172205 := rs (se 3 (by rfl) ⟨32288, by rfl⟩) R64577
theorem R41161 : Reach 41161 := rs (se 2 (by rfl) ⟨15435, by rfl⟩) R30871
theorem R205001 : Reach 205001 := rs (se 2 (by rfl) ⟨76875, by rfl⟩) R153751
theorem R106753 : Reach 106753 := rs (se 2 (by rfl) ⟨40032, by rfl⟩) R80065
theorem R107095 : Reach 107095 := rs (se 1 (by rfl) ⟨80321, by rfl⟩) R160643
theorem R533263 : Reach 533263 := rs (se 1 (by rfl) ⟨399947, by rfl⟩) R799895
theorem R41863 : Reach 41863 := rs (se 1 (by rfl) ⟨31397, by rfl⟩) R62795
theorem R42511 : Reach 42511 := rs (se 1 (by rfl) ⟨31883, by rfl⟩) R63767
theorem R75293 : Reach 75293 := rs (se 3 (by rfl) ⟨14117, by rfl⟩) R28235
theorem R173645 : Reach 173645 := rs (se 3 (by rfl) ⟨32558, by rfl⟩) R65117
theorem R239375 : Reach 239375 := rs (se 1 (by rfl) ⟨179531, by rfl⟩) R359063
theorem R141335 : Reach 141335 := rs (se 1 (by rfl) ⟨106001, by rfl⟩) R212003
theorem R43051 : Reach 43051 := rs (se 1 (by rfl) ⟨32288, by rfl⟩) R64577
theorem R43193 : Reach 43193 := rs (se 2 (by rfl) ⟨16197, by rfl⟩) R32395
theorem R43553 : Reach 43553 := rs (se 2 (by rfl) ⟨16332, by rfl⟩) R32665
theorem R43895 : Reach 43895 := rs (se 1 (by rfl) ⟨32921, by rfl⟩) R65843
theorem R44347 : Reach 44347 := rs (se 1 (by rfl) ⟨33260, by rfl⟩) R66521
theorem R44435 : Reach 44435 := rs (se 1 (by rfl) ⟨33326, by rfl⟩) R66653
theorem R44489 : Reach 44489 := rs (se 2 (by rfl) ⟨16683, by rfl⟩) R33367
theorem R208655 : Reach 208655 := rs (se 1 (by rfl) ⟨156491, by rfl⟩) R312983
theorem R44833 : Reach 44833 := rs (se 2 (by rfl) ⟨16812, by rfl⟩) R33625
theorem R110483 : Reach 110483 := rs (se 1 (by rfl) ⟨82862, by rfl⟩) R165725
theorem R77753 : Reach 77753 := rs (se 2 (by rfl) ⟨29157, by rfl⟩) R58315
theorem R45191 : Reach 45191 := rs (se 1 (by rfl) ⟨33893, by rfl⟩) R67787
theorem R536977 : Reach 536977 := rs (se 2 (by rfl) ⟨201366, by rfl⟩) R402733
theorem R45839 : Reach 45839 := rs (se 1 (by rfl) ⟨34379, by rfl⟩) R68759
theorem R144281 : Reach 144281 := rs (se 2 (by rfl) ⟨54105, by rfl⟩) R108211
theorem R144503 : Reach 144503 := rs (se 1 (by rfl) ⟨108377, by rfl⟩) R216755
theorem R177353 : Reach 177353 := rs (se 2 (by rfl) ⟨66507, by rfl⟩) R133015
theorem R111887 : Reach 111887 := rs (se 1 (by rfl) ⟨83915, by rfl⟩) R167831
theorem R1291697 : Reach 1291697 := rs (se 2 (by rfl) ⟨484386, by rfl⟩) R968773
theorem R46793 : Reach 46793 := rs (se 2 (by rfl) ⟨17547, by rfl⟩) R35095
theorem R79649 : Reach 79649 := rs (se 2 (by rfl) ⟨29868, by rfl⟩) R59737
theorem R145297 : Reach 145297 := rs (se 2 (by rfl) ⟨54486, by rfl⟩) R108973
theorem R112529 : Reach 112529 := rs (se 2 (by rfl) ⟨42198, by rfl⟩) R84397
theorem R80243 : Reach 80243 := rs (se 1 (by rfl) ⟨60182, by rfl⟩) R120365
theorem R179333 : Reach 179333 := rs (se 4 (by rfl) ⟨16812, by rfl⟩) R33625
theorem R48775 : Reach 48775 := rs (se 1 (by rfl) ⟨36581, by rfl⟩) R73163
theorem R114641 : Reach 114641 := rs (se 2 (by rfl) ⟨42990, by rfl⟩) R85981
theorem R115091 : Reach 115091 := rs (se 1 (by rfl) ⟨86318, by rfl⟩) R172637
theorem R148169 : Reach 148169 := rs (se 2 (by rfl) ⟨55563, by rfl⟩) R111127
theorem R82835 : Reach 82835 := rs (se 1 (by rfl) ⟨62126, by rfl⟩) R124253
theorem R82873 : Reach 82873 := rs (se 2 (by rfl) ⟨31077, by rfl⟩) R62155
theorem R50377 : Reach 50377 := rs (se 2 (by rfl) ⟨18891, by rfl⟩) R37783
theorem R181763 : Reach 181763 := rs (se 1 (by rfl) ⟨136322, by rfl⟩) R272645
theorem R214721 : Reach 214721 := rs (se 2 (by rfl) ⟨80520, by rfl⟩) R161041
theorem R50959 : Reach 50959 := rs (se 1 (by rfl) ⟨38219, by rfl⟩) R76439
theorem R542513 : Reach 542513 := rs (se 2 (by rfl) ⟨203442, by rfl⟩) R406885
theorem R84239 : Reach 84239 := rs (se 1 (by rfl) ⟨63179, by rfl⟩) R126359
theorem R84509 : Reach 84509 := rs (se 3 (by rfl) ⟨15845, by rfl⟩) R31691
theorem R150083 : Reach 150083 := rs (se 1 (by rfl) ⟨112562, by rfl⟩) R225125
theorem R281393 : Reach 281393 := rs (se 2 (by rfl) ⟨105522, by rfl⟩) R211045
theorem R84883 : Reach 84883 := rs (se 1 (by rfl) ⟨63662, by rfl⟩) R127325
theorem R52283 : Reach 52283 := rs (se 1 (by rfl) ⟨39212, by rfl⟩) R78425
theorem R805949 : Reach 805949 := rs (se 3 (by rfl) ⟨151115, by rfl⟩) R302231
theorem R52343 : Reach 52343 := rs (se 1 (by rfl) ⟨39257, by rfl⟩) R78515
theorem R281987 : Reach 281987 := rs (se 1 (by rfl) ⟨211490, by rfl⟩) R422981
theorem R249293 : Reach 249293 := rs (se 3 (by rfl) ⟨46742, by rfl⟩) R93485
theorem R52883 : Reach 52883 := rs (se 1 (by rfl) ⟨39662, by rfl⟩) R79325
theorem R282305 : Reach 282305 := rs (se 2 (by rfl) ⟨105864, by rfl⟩) R211729
theorem R52937 : Reach 52937 := rs (se 2 (by rfl) ⟨19851, by rfl⟩) R39703
theorem R282329 : Reach 282329 := rs (se 2 (by rfl) ⟨105873, by rfl⟩) R211747
theorem R249601 : Reach 249601 := rs (se 2 (by rfl) ⟨93600, by rfl⟩) R187201
theorem R118543 : Reach 118543 := rs (se 1 (by rfl) ⟨88907, by rfl⟩) R177815
theorem R511895 : Reach 511895 := rs (se 1 (by rfl) ⟨383921, by rfl⟩) R767843
theorem R85913 : Reach 85913 := rs (se 2 (by rfl) ⟨32217, by rfl⟩) R64435
theorem R905417 : Reach 905417 := rs (se 2 (by rfl) ⟨339531, by rfl⟩) R679063
theorem R217403 : Reach 217403 := rs (se 1 (by rfl) ⟨163052, by rfl⟩) R326105
theorem R53639 : Reach 53639 := rs (se 1 (by rfl) ⟨40229, by rfl⟩) R80459
theorem R53819 : Reach 53819 := rs (se 1 (by rfl) ⟨40364, by rfl⟩) R80729
theorem R86615 : Reach 86615 := rs (se 1 (by rfl) ⟨64961, by rfl⟩) R129923
theorem R53945 : Reach 53945 := rs (se 2 (by rfl) ⟨20229, by rfl⟩) R40459
theorem R86993 : Reach 86993 := rs (se 2 (by rfl) ⟨32622, by rfl⟩) R65245
theorem R54287 : Reach 54287 := rs (se 1 (by rfl) ⟨40715, by rfl⟩) R81431
theorem R54305 : Reach 54305 := rs (se 2 (by rfl) ⟨20364, by rfl⟩) R40729
theorem R87101 : Reach 87101 := rs (se 3 (by rfl) ⟨16331, by rfl⟩) R32663
theorem R119875 : Reach 119875 := rs (se 1 (by rfl) ⟨89906, by rfl⟩) R179813
theorem R54647 : Reach 54647 := rs (se 1 (by rfl) ⟨40985, by rfl⟩) R81971
theorem R54827 : Reach 54827 := rs (se 1 (by rfl) ⟨41120, by rfl⟩) R82241
theorem R55175 : Reach 55175 := rs (se 1 (by rfl) ⟨41381, by rfl⟩) R82763
theorem R55187 : Reach 55187 := rs (se 1 (by rfl) ⟨41390, by rfl⟩) R82781
theorem R55241 : Reach 55241 := rs (se 2 (by rfl) ⟨20715, by rfl⟩) R41431
theorem R154001 : Reach 154001 := rs (se 2 (by rfl) ⟨57750, by rfl⟩) R115501
theorem R514451 : Reach 514451 := rs (se 1 (by rfl) ⟨385838, by rfl⟩) R771677
theorem R88505 : Reach 88505 := rs (se 2 (by rfl) ⟨33189, by rfl⟩) R66379
theorem R383453 : Reach 383453 := rs (se 3 (by rfl) ⟨71897, by rfl⟩) R143795
theorem R55943 : Reach 55943 := rs (se 1 (by rfl) ⟨41957, by rfl⟩) R83915
theorem R55961 : Reach 55961 := rs (se 2 (by rfl) ⟨20985, by rfl⟩) R41971
theorem R187109 : Reach 187109 := rs (se 4 (by rfl) ⟨17541, by rfl⟩) R35083
theorem R88813 : Reach 88813 := rs (se 3 (by rfl) ⟨16652, by rfl⟩) R33305
theorem R351013 : Reach 351013 := rs (se 4 (by rfl) ⟨32907, by rfl⟩) R65815
theorem R56123 : Reach 56123 := rs (se 1 (by rfl) ⟨42092, by rfl⟩) R84185
theorem R220067 : Reach 220067 := rs (se 1 (by rfl) ⟨165050, by rfl⟩) R330101
theorem R56249 : Reach 56249 := rs (se 2 (by rfl) ⟨21093, by rfl⟩) R42187
theorem R56321 : Reach 56321 := rs (se 2 (by rfl) ⟨21120, by rfl⟩) R42241
theorem R23559 : Reach 23559 := rs (se 1 (by rfl) ⟨17669, by rfl⟩) R35339
theorem R89099 : Reach 89099 := rs (se 1 (by rfl) ⟨66824, by rfl⟩) R133649
theorem R23567 : Reach 23567 := rs (se 1 (by rfl) ⟨17675, by rfl⟩) R35351
theorem R23611 : Reach 23611 := rs (se 1 (by rfl) ⟨17708, by rfl⟩) R35417
theorem R56435 : Reach 56435 := rs (se 1 (by rfl) ⟨42326, by rfl⟩) R84653
theorem R89207 : Reach 89207 := rs (se 1 (by rfl) ⟨66905, by rfl⟩) R133811
theorem R23687 : Reach 23687 := rs (se 1 (by rfl) ⟨17765, by rfl⟩) R35531
theorem R23695 : Reach 23695 := rs (se 1 (by rfl) ⟨17771, by rfl⟩) R35543
theorem R23739 : Reach 23739 := rs (se 1 (by rfl) ⟨17804, by rfl⟩) R35609
theorem R23815 : Reach 23815 := rs (se 1 (by rfl) ⟨17861, by rfl⟩) R35723
theorem R23823 : Reach 23823 := rs (se 1 (by rfl) ⟨17867, by rfl⟩) R35735
theorem R56591 : Reach 56591 := rs (se 1 (by rfl) ⟨42443, by rfl⟩) R84887
theorem R56609 : Reach 56609 := rs (se 2 (by rfl) ⟨21228, by rfl⟩) R42457
theorem R23867 : Reach 23867 := rs (se 1 (by rfl) ⟨17900, by rfl⟩) R35801
theorem R56663 : Reach 56663 := rs (se 1 (by rfl) ⟨42497, by rfl⟩) R84995
theorem R23943 : Reach 23943 := rs (se 1 (by rfl) ⟨17957, by rfl⟩) R35915
theorem R23951 : Reach 23951 := rs (se 1 (by rfl) ⟨17963, by rfl⟩) R35927
theorem R23995 : Reach 23995 := rs (se 1 (by rfl) ⟨17996, by rfl⟩) R35993
theorem R24071 : Reach 24071 := rs (se 1 (by rfl) ⟨18053, by rfl⟩) R36107
theorem R56843 : Reach 56843 := rs (se 1 (by rfl) ⟨42632, by rfl⟩) R85265
theorem R24079 : Reach 24079 := rs (se 1 (by rfl) ⟨18059, by rfl⟩) R36119
theorem R24123 : Reach 24123 := rs (se 1 (by rfl) ⟨18092, by rfl⟩) R36185
theorem R56951 : Reach 56951 := rs (se 1 (by rfl) ⟨42713, by rfl⟩) R85427
theorem R24199 : Reach 24199 := rs (se 1 (by rfl) ⟨18149, by rfl⟩) R36299
theorem R24207 : Reach 24207 := rs (se 1 (by rfl) ⟨18155, by rfl⟩) R36311
theorem R57017 : Reach 57017 := rs (se 2 (by rfl) ⟨21381, by rfl⟩) R42763
theorem R24251 : Reach 24251 := rs (se 1 (by rfl) ⟨18188, by rfl⟩) R36377
theorem R89801 : Reach 89801 := rs (se 2 (by rfl) ⟨33675, by rfl⟩) R67351
theorem R24327 : Reach 24327 := rs (se 1 (by rfl) ⟨18245, by rfl⟩) R36491
theorem R24335 : Reach 24335 := rs (se 1 (by rfl) ⟨18251, by rfl⟩) R36503
theorem R57131 : Reach 57131 := rs (se 1 (by rfl) ⟨42848, by rfl⟩) R85697
theorem R24379 : Reach 24379 := rs (se 1 (by rfl) ⟨18284, by rfl⟩) R36569
theorem R57203 : Reach 57203 := rs (se 1 (by rfl) ⟨42902, by rfl⟩) R85805
theorem R24455 : Reach 24455 := rs (se 1 (by rfl) ⟨18341, by rfl⟩) R36683
theorem R24463 : Reach 24463 := rs (se 1 (by rfl) ⟨18347, by rfl⟩) R36695
theorem R24507 : Reach 24507 := rs (se 1 (by rfl) ⟨18380, by rfl⟩) R36761
theorem R24583 : Reach 24583 := rs (se 1 (by rfl) ⟨18437, by rfl⟩) R36875
theorem R24591 : Reach 24591 := rs (se 1 (by rfl) ⟨18443, by rfl⟩) R36887
theorem R24635 : Reach 24635 := rs (se 1 (by rfl) ⟨18476, by rfl⟩) R36953
theorem R90179 : Reach 90179 := rs (se 1 (by rfl) ⟨67634, by rfl⟩) R135269
theorem R24711 : Reach 24711 := rs (se 1 (by rfl) ⟨18533, by rfl⟩) R37067
theorem R24719 : Reach 24719 := rs (se 1 (by rfl) ⟨18539, by rfl⟩) R37079
theorem R57491 : Reach 57491 := rs (se 1 (by rfl) ⟨43118, by rfl⟩) R86237
theorem R24763 : Reach 24763 := rs (se 1 (by rfl) ⟨18572, by rfl⟩) R37145
theorem R57545 : Reach 57545 := rs (se 2 (by rfl) ⟨21579, by rfl⟩) R43159
theorem R778481 : Reach 778481 := rs (se 2 (by rfl) ⟨291930, by rfl⟩) R583861
theorem R24839 : Reach 24839 := rs (se 1 (by rfl) ⟨18629, by rfl⟩) R37259
theorem R24847 : Reach 24847 := rs (se 1 (by rfl) ⟨18635, by rfl⟩) R37271
theorem R24891 : Reach 24891 := rs (se 1 (by rfl) ⟨18668, by rfl⟩) R37337
theorem R90503 : Reach 90503 := rs (se 1 (by rfl) ⟨67877, by rfl⟩) R135755
theorem R24967 : Reach 24967 := rs (se 1 (by rfl) ⟨18725, by rfl⟩) R37451
theorem R24975 : Reach 24975 := rs (se 1 (by rfl) ⟨18731, by rfl⟩) R37463
theorem R123281 : Reach 123281 := rs (se 2 (by rfl) ⟨46230, by rfl⟩) R92461
theorem R25019 : Reach 25019 := rs (se 1 (by rfl) ⟨18764, by rfl⟩) R37529
theorem R25095 : Reach 25095 := rs (se 1 (by rfl) ⟨18821, by rfl⟩) R37643
theorem R25103 : Reach 25103 := rs (se 1 (by rfl) ⟨18827, by rfl⟩) R37655
theorem R25147 : Reach 25147 := rs (se 1 (by rfl) ⟨18860, by rfl⟩) R37721
theorem R25223 : Reach 25223 := rs (se 1 (by rfl) ⟨18917, by rfl⟩) R37835
theorem R25231 : Reach 25231 := rs (se 1 (by rfl) ⟨18923, by rfl⟩) R37847
theorem R25275 : Reach 25275 := rs (se 1 (by rfl) ⟨18956, by rfl⟩) R37913
theorem R90881 : Reach 90881 := rs (se 2 (by rfl) ⟨34080, by rfl⟩) R68161
theorem R25351 : Reach 25351 := rs (se 1 (by rfl) ⟨19013, by rfl⟩) R38027
theorem R25359 : Reach 25359 := rs (se 1 (by rfl) ⟨19019, by rfl⟩) R38039
theorem R25403 : Reach 25403 := rs (se 1 (by rfl) ⟨19052, by rfl⟩) R38105
theorem R25479 : Reach 25479 := rs (se 1 (by rfl) ⟨19109, by rfl⟩) R38219
theorem R58247 : Reach 58247 := rs (se 1 (by rfl) ⟨43685, by rfl⟩) R87371
theorem R25487 : Reach 25487 := rs (se 1 (by rfl) ⟨19115, by rfl⟩) R38231
theorem R58265 : Reach 58265 := rs (se 2 (by rfl) ⟨21849, by rfl⟩) R43699
theorem R25531 : Reach 25531 := rs (se 1 (by rfl) ⟨19148, by rfl⟩) R38297
theorem R25607 : Reach 25607 := rs (se 1 (by rfl) ⟨19205, by rfl⟩) R38411
theorem R25615 : Reach 25615 := rs (se 1 (by rfl) ⟨19211, by rfl⟩) R38423
theorem R58427 : Reach 58427 := rs (se 1 (by rfl) ⟨43820, by rfl⟩) R87641
theorem R25659 : Reach 25659 := rs (se 1 (by rfl) ⟨19244, by rfl⟩) R38489
theorem R25735 : Reach 25735 := rs (se 1 (by rfl) ⟨19301, by rfl⟩) R38603
theorem R25743 : Reach 25743 := rs (se 1 (by rfl) ⟨19307, by rfl⟩) R38615
theorem R58553 : Reach 58553 := rs (se 2 (by rfl) ⟨21957, by rfl⟩) R43915
theorem R25787 : Reach 25787 := rs (se 1 (by rfl) ⟨19340, by rfl⟩) R38681
theorem R58625 : Reach 58625 := rs (se 2 (by rfl) ⟨21984, by rfl⟩) R43969
theorem R25863 : Reach 25863 := rs (se 1 (by rfl) ⟨19397, by rfl⟩) R38795
theorem R25871 : Reach 25871 := rs (se 1 (by rfl) ⟨19403, by rfl⟩) R38807
theorem R58657 : Reach 58657 := rs (se 2 (by rfl) ⟨21996, by rfl⟩) R43993
theorem R25915 : Reach 25915 := rs (se 1 (by rfl) ⟨19436, by rfl⟩) R38873
theorem R124249 : Reach 124249 := rs (se 2 (by rfl) ⟨46593, by rfl⟩) R93187
theorem R25991 : Reach 25991 := rs (se 1 (by rfl) ⟨19493, by rfl⟩) R38987
theorem R25999 : Reach 25999 := rs (se 1 (by rfl) ⟨19499, by rfl⟩) R38999
theorem R26043 : Reach 26043 := rs (se 1 (by rfl) ⟨19532, by rfl⟩) R39065
theorem R26119 : Reach 26119 := rs (se 1 (by rfl) ⟨19589, by rfl⟩) R39179
theorem R26127 : Reach 26127 := rs (se 1 (by rfl) ⟨19595, by rfl⟩) R39191
theorem R58895 : Reach 58895 := rs (se 1 (by rfl) ⟨44171, by rfl⟩) R88343
theorem R58913 : Reach 58913 := rs (se 2 (by rfl) ⟨22092, by rfl⟩) R44185
theorem R26171 : Reach 26171 := rs (se 1 (by rfl) ⟨19628, by rfl⟩) R39257
theorem R58967 : Reach 58967 := rs (se 1 (by rfl) ⟨44225, by rfl⟩) R88451
theorem R26247 : Reach 26247 := rs (se 1 (by rfl) ⟨19685, by rfl⟩) R39371
theorem R26255 : Reach 26255 := rs (se 1 (by rfl) ⟨19691, by rfl⟩) R39383
theorem R26299 : Reach 26299 := rs (se 1 (by rfl) ⟨19724, by rfl⟩) R39449
theorem R26375 : Reach 26375 := rs (se 1 (by rfl) ⟨19781, by rfl⟩) R39563
theorem R59147 : Reach 59147 := rs (se 1 (by rfl) ⟨44360, by rfl⟩) R88721
theorem R26383 : Reach 26383 := rs (se 1 (by rfl) ⟨19787, by rfl⟩) R39575
theorem R26427 : Reach 26427 := rs (se 1 (by rfl) ⟨19820, by rfl⟩) R39641
theorem R59255 : Reach 59255 := rs (se 1 (by rfl) ⟨44441, by rfl⟩) R88883
theorem R26503 : Reach 26503 := rs (se 1 (by rfl) ⟨19877, by rfl⟩) R39755
theorem R26511 : Reach 26511 := rs (se 1 (by rfl) ⟨19883, by rfl⟩) R39767
theorem R26555 : Reach 26555 := rs (se 1 (by rfl) ⟨19916, by rfl⟩) R39833
theorem R157643 : Reach 157643 := rs (se 1 (by rfl) ⟨118232, by rfl⟩) R236465
theorem R26631 : Reach 26631 := rs (se 1 (by rfl) ⟨19973, by rfl⟩) R39947
theorem R26639 : Reach 26639 := rs (se 1 (by rfl) ⟨19979, by rfl⟩) R39959
theorem R59435 : Reach 59435 := rs (se 1 (by rfl) ⟨44576, by rfl⟩) R89153
theorem R26683 : Reach 26683 := rs (se 1 (by rfl) ⟨20012, by rfl⟩) R40025
theorem R59507 : Reach 59507 := rs (se 1 (by rfl) ⟨44630, by rfl⟩) R89261
theorem R92279 : Reach 92279 := rs (se 1 (by rfl) ⟨69209, by rfl⟩) R138419
theorem R26759 : Reach 26759 := rs (se 1 (by rfl) ⟨20069, by rfl⟩) R40139
theorem R26767 : Reach 26767 := rs (se 1 (by rfl) ⟨20075, by rfl⟩) R40151
theorem R26811 : Reach 26811 := rs (se 1 (by rfl) ⟨20108, by rfl⟩) R40217
theorem R26887 : Reach 26887 := rs (se 1 (by rfl) ⟨20165, by rfl⟩) R40331
theorem R26895 : Reach 26895 := rs (se 1 (by rfl) ⟨20171, by rfl⟩) R40343
theorem R26939 : Reach 26939 := rs (se 1 (by rfl) ⟨20204, by rfl⟩) R40409
theorem R27015 : Reach 27015 := rs (se 1 (by rfl) ⟨20261, by rfl⟩) R40523
theorem R27023 : Reach 27023 := rs (se 1 (by rfl) ⟨20267, by rfl⟩) R40535
theorem R59795 : Reach 59795 := rs (se 1 (by rfl) ⟨44846, by rfl⟩) R89693
theorem R27067 : Reach 27067 := rs (se 1 (by rfl) ⟨20300, by rfl⟩) R40601
theorem R59849 : Reach 59849 := rs (se 2 (by rfl) ⟨22443, by rfl⟩) R44887
theorem R125387 : Reach 125387 := rs (se 1 (by rfl) ⟨94040, by rfl⟩) R188081
theorem R59915 : Reach 59915 := rs (se 1 (by rfl) ⟨44936, by rfl⟩) R89873
theorem R256769 : Reach 256769 := rs (se 2 (by rfl) ⟨96288, by rfl⟩) R192577
theorem R125711 : Reach 125711 := rs (se 1 (by rfl) ⟨94283, by rfl⟩) R188567
theorem R60203 : Reach 60203 := rs (se 1 (by rfl) ⟨45152, by rfl⟩) R90305
theorem R27535 : Reach 27535 := rs (se 1 (by rfl) ⟨20651, by rfl⟩) R41303
theorem R224153 : Reach 224153 := rs (se 2 (by rfl) ⟨84057, by rfl⟩) R168115
theorem R125981 : Reach 125981 := rs (se 3 (by rfl) ⟨23621, by rfl⟩) R47243
theorem R93251 : Reach 93251 := rs (se 1 (by rfl) ⟨69938, by rfl⟩) R139877
theorem R60551 : Reach 60551 := rs (se 1 (by rfl) ⟨45413, by rfl⟩) R90827
theorem R60569 : Reach 60569 := rs (se 2 (by rfl) ⟨22713, by rfl⟩) R45427
theorem R27895 : Reach 27895 := rs (se 1 (by rfl) ⟨20921, by rfl⟩) R41843
theorem R60731 : Reach 60731 := rs (se 1 (by rfl) ⟨45548, by rfl⟩) R91097
theorem R290141 : Reach 290141 := rs (se 3 (by rfl) ⟨54401, by rfl⟩) R108803
theorem R1371491 : Reach 1371491 := rs (se 1 (by rfl) ⟨1028618, by rfl⟩) R2057237
theorem R28039 : Reach 28039 := rs (se 1 (by rfl) ⟨21029, by rfl⟩) R42059
theorem R28075 : Reach 28075 := rs (se 1 (by rfl) ⟨21056, by rfl⟩) R42113
theorem R60857 : Reach 60857 := rs (se 2 (by rfl) ⟨22821, by rfl⟩) R45643
theorem R93649 : Reach 93649 := rs (se 2 (by rfl) ⟨35118, by rfl⟩) R70237
theorem R60929 : Reach 60929 := rs (se 2 (by rfl) ⟨22848, by rfl⟩) R45697
theorem R93707 : Reach 93707 := rs (se 1 (by rfl) ⟨70280, by rfl⟩) R140561
theorem R28219 : Reach 28219 := rs (se 1 (by rfl) ⟨21164, by rfl⟩) R42329
theorem R61195 : Reach 61195 := rs (se 1 (by rfl) ⟨45896, by rfl⟩) R91793
theorem R61199 : Reach 61199 := rs (se 1 (by rfl) ⟨45899, by rfl⟩) R91799
theorem R61337 : Reach 61337 := rs (se 2 (by rfl) ⟨23001, by rfl⟩) R46003
theorem R225227 : Reach 225227 := rs (se 1 (by rfl) ⟨168920, by rfl⟩) R337841
theorem R28679 : Reach 28679 := rs (se 1 (by rfl) ⟨21509, by rfl⟩) R43019
theorem R28687 : Reach 28687 := rs (se 1 (by rfl) ⟨21515, by rfl⟩) R43031
theorem R61499 : Reach 61499 := rs (se 1 (by rfl) ⟨46124, by rfl⟩) R92249
theorem R127037 : Reach 127037 := rs (se 3 (by rfl) ⟨23819, by rfl⟩) R47639
theorem R127169 : Reach 127169 := rs (se 2 (by rfl) ⟨47688, by rfl⟩) R95377
theorem R94445 : Reach 94445 := rs (se 3 (by rfl) ⟨17708, by rfl⟩) R35417
theorem R29047 : Reach 29047 := rs (se 1 (by rfl) ⟨21785, by rfl⟩) R43571
theorem R61843 : Reach 61843 := rs (se 1 (by rfl) ⟨46382, by rfl⟩) R92765
theorem R29191 : Reach 29191 := rs (se 1 (by rfl) ⟨21893, by rfl⟩) R43787
theorem R61985 : Reach 61985 := rs (se 2 (by rfl) ⟨23244, by rfl⟩) R46489
theorem R29227 : Reach 29227 := rs (se 1 (by rfl) ⟨21920, by rfl⟩) R43841
theorem R29371 : Reach 29371 := rs (se 1 (by rfl) ⟨22028, by rfl⟩) R44057
theorem R291545 : Reach 291545 := rs (se 2 (by rfl) ⟨109329, by rfl⟩) R218659
theorem R291599 : Reach 291599 := rs (se 1 (by rfl) ⟨218699, by rfl⟩) R437399
theorem R127889 : Reach 127889 := rs (se 2 (by rfl) ⟨47958, by rfl⟩) R95917
theorem R29839 : Reach 29839 := rs (se 1 (by rfl) ⟨22379, by rfl⟩) R44759
theorem R30071 : Reach 30071 := rs (se 1 (by rfl) ⟨22553, by rfl⟩) R45107
theorem R128441 : Reach 128441 := rs (se 2 (by rfl) ⟨48165, by rfl⟩) R96331
theorem R128465 : Reach 128465 := rs (se 2 (by rfl) ⟨48174, by rfl⟩) R96349
theorem R30199 : Reach 30199 := rs (se 1 (by rfl) ⟨22649, by rfl⟩) R45299
theorem R62977 : Reach 62977 := rs (se 2 (by rfl) ⟨23616, by rfl⟩) R47233
theorem R30223 : Reach 30223 := rs (se 1 (by rfl) ⟨22667, by rfl⟩) R45335
theorem R30251 : Reach 30251 := rs (se 1 (by rfl) ⟨22688, by rfl⟩) R45377
theorem R128555 : Reach 128555 := rs (se 1 (by rfl) ⟨96416, by rfl⟩) R192833
theorem R95863 : Reach 95863 := rs (se 1 (by rfl) ⟨71897, by rfl⟩) R143795
theorem R30343 : Reach 30343 := rs (se 1 (by rfl) ⟨22757, by rfl⟩) R45515
theorem R30379 : Reach 30379 := rs (se 1 (by rfl) ⟨22784, by rfl⟩) R45569
theorem R30395 : Reach 30395 := rs (se 1 (by rfl) ⟨22796, by rfl⟩) R45593
theorem R128749 : Reach 128749 := rs (se 3 (by rfl) ⟨24140, by rfl⟩) R48281
theorem R325579 : Reach 325579 := rs (se 1 (by rfl) ⟨244184, by rfl⟩) R488369
theorem R194507 : Reach 194507 := rs (se 1 (by rfl) ⟨145880, by rfl⟩) R291761
theorem R63575 : Reach 63575 := rs (se 1 (by rfl) ⟨47681, by rfl⟩) R95363
theorem R30863 : Reach 30863 := rs (se 1 (by rfl) ⟨23147, by rfl⟩) R46295
theorem R63787 : Reach 63787 := rs (se 1 (by rfl) ⟨47840, by rfl⟩) R95681
theorem R63929 : Reach 63929 := rs (se 2 (by rfl) ⟨23973, by rfl⟩) R47947
theorem R162233 : Reach 162233 := rs (se 2 (by rfl) ⟨60837, by rfl⟩) R121675
theorem R64061 : Reach 64061 := rs (se 3 (by rfl) ⟨12011, by rfl⟩) R24023
theorem R195139 : Reach 195139 := rs (se 1 (by rfl) ⟨146354, by rfl⟩) R292709
theorem R96835 : Reach 96835 := rs (se 1 (by rfl) ⟨72626, by rfl⟩) R145253
theorem R31351 : Reach 31351 := rs (se 1 (by rfl) ⟨23513, by rfl⟩) R47027
theorem R31367 : Reach 31367 := rs (se 1 (by rfl) ⟨23525, by rfl⟩) R47051
theorem R359129 : Reach 359129 := rs (se 2 (by rfl) ⟨134673, by rfl⟩) R269347
theorem R97139 : Reach 97139 := rs (se 1 (by rfl) ⟨72854, by rfl⟩) R145709
theorem R31817 : Reach 31817 := rs (se 2 (by rfl) ⟨11931, by rfl⟩) R23863
theorem R97481 : Reach 97481 := rs (se 2 (by rfl) ⟨36555, by rfl⟩) R73111
theorem R32015 : Reach 32015 := rs (se 1 (by rfl) ⟨24011, by rfl⟩) R48023
theorem R130355 : Reach 130355 := rs (se 1 (by rfl) ⟨97766, by rfl⟩) R195533
theorem R32059 : Reach 32059 := rs (se 1 (by rfl) ⟨24044, by rfl⟩) R48089
theorem R97595 : Reach 97595 := rs (se 1 (by rfl) ⟨73196, by rfl⟩) R146393
theorem R64921 : Reach 64921 := rs (se 2 (by rfl) ⟨24345, by rfl⟩) R48691
theorem R130571 : Reach 130571 := rs (se 1 (by rfl) ⟨97928, by rfl⟩) R195857
theorem R65083 : Reach 65083 := rs (se 1 (by rfl) ⟨48812, by rfl⟩) R97625
theorem R32329 : Reach 32329 := rs (se 2 (by rfl) ⟨12123, by rfl⟩) R24247
theorem R130733 : Reach 130733 := rs (se 3 (by rfl) ⟨24512, by rfl⟩) R49025
theorem R196289 : Reach 196289 := rs (se 2 (by rfl) ⟨73608, by rfl⟩) R147217
theorem R65225 : Reach 65225 := rs (se 2 (by rfl) ⟨24459, by rfl⟩) R48919
theorem R98081 : Reach 98081 := rs (se 2 (by rfl) ⟨36780, by rfl⟩) R73561
theorem R98779 : Reach 98779 := rs (se 1 (by rfl) ⟨74084, by rfl⟩) R148169
theorem R66035 : Reach 66035 := rs (se 1 (by rfl) ⟨49526, by rfl⟩) R99053
theorem R33529 : Reach 33529 := rs (se 2 (by rfl) ⟨12573, by rfl⟩) R25147
theorem R66491 : Reach 66491 := rs (se 1 (by rfl) ⟨49868, by rfl⟩) R99737
theorem R361675 : Reach 361675 := rs (se 1 (by rfl) ⟨271256, by rfl⟩) R542513
theorem R67169 : Reach 67169 := rs (se 2 (by rfl) ⟨25188, by rfl⟩) R50377
theorem R100055 : Reach 100055 := rs (se 1 (by rfl) ⟨75041, by rfl⟩) R150083
theorem R165665 : Reach 165665 := rs (se 2 (by rfl) ⟨62124, by rfl⟩) R124249
theorem R329507 : Reach 329507 := rs (se 1 (by rfl) ⟨247130, by rfl⟩) R494261
theorem R34895 : Reach 34895 := rs (se 1 (by rfl) ⟨26171, by rfl⟩) R52343
theorem R166195 : Reach 166195 := rs (se 1 (by rfl) ⟨124646, by rfl⟩) R249293
theorem R35255 : Reach 35255 := rs (se 1 (by rfl) ⟨26441, by rfl⟩) R52883
theorem R35291 : Reach 35291 := rs (se 1 (by rfl) ⟨26468, by rfl⟩) R52937
theorem R35759 : Reach 35759 := rs (se 1 (by rfl) ⟨26819, by rfl⟩) R53639
theorem R35849 : Reach 35849 := rs (se 2 (by rfl) ⟨13443, by rfl⟩) R26887
theorem R68627 : Reach 68627 := rs (se 1 (by rfl) ⟨51470, by rfl⟩) R102941
theorem R35879 : Reach 35879 := rs (se 1 (by rfl) ⟨26909, by rfl⟩) R53819
theorem R35963 : Reach 35963 := rs (se 1 (by rfl) ⟨26972, by rfl⟩) R53945
theorem R134297 : Reach 134297 := rs (se 2 (by rfl) ⟨50361, by rfl⟩) R100723
theorem R36089 : Reach 36089 := rs (se 2 (by rfl) ⟨13533, by rfl⟩) R27067
theorem R36191 : Reach 36191 := rs (se 1 (by rfl) ⟨27143, by rfl⟩) R54287
theorem R36203 : Reach 36203 := rs (se 1 (by rfl) ⟨27152, by rfl⟩) R54305
theorem R200231 : Reach 200231 := rs (se 1 (by rfl) ⟨150173, by rfl⟩) R300347
theorem R36431 : Reach 36431 := rs (se 1 (by rfl) ⟨27323, by rfl⟩) R54647
theorem R36551 : Reach 36551 := rs (se 1 (by rfl) ⟨27413, by rfl⟩) R54827
theorem R36713 : Reach 36713 := rs (se 2 (by rfl) ⟨13767, by rfl⟩) R27535
theorem R36791 : Reach 36791 := rs (se 1 (by rfl) ⟨27593, by rfl⟩) R55187
theorem R36827 : Reach 36827 := rs (se 1 (by rfl) ⟨27620, by rfl⟩) R55241
theorem R135283 : Reach 135283 := rs (se 1 (by rfl) ⟨101462, by rfl⟩) R202925
theorem R102667 : Reach 102667 := rs (se 1 (by rfl) ⟨77000, by rfl⟩) R154001
theorem R37193 : Reach 37193 := rs (se 2 (by rfl) ⟨13947, by rfl⟩) R27895
theorem R37295 : Reach 37295 := rs (se 1 (by rfl) ⟨27971, by rfl⟩) R55943
theorem R37307 : Reach 37307 := rs (se 1 (by rfl) ⟨27980, by rfl⟩) R55961
theorem R37385 : Reach 37385 := rs (se 2 (by rfl) ⟨14019, by rfl⟩) R28039
theorem R37415 : Reach 37415 := rs (se 1 (by rfl) ⟨28061, by rfl⟩) R56123
theorem R37433 : Reach 37433 := rs (se 2 (by rfl) ⟨14037, by rfl⟩) R28075
theorem R37499 : Reach 37499 := rs (se 1 (by rfl) ⟨28124, by rfl⟩) R56249
theorem R37547 : Reach 37547 := rs (se 1 (by rfl) ⟨28160, by rfl⟩) R56321
theorem R37625 : Reach 37625 := rs (se 2 (by rfl) ⟨14109, by rfl⟩) R28219
theorem R37727 : Reach 37727 := rs (se 1 (by rfl) ⟨28295, by rfl⟩) R56591
theorem R37739 : Reach 37739 := rs (se 1 (by rfl) ⟨28304, by rfl⟩) R56609
theorem R37775 : Reach 37775 := rs (se 1 (by rfl) ⟨28331, by rfl⟩) R56663
theorem R332747 : Reach 332747 := rs (se 1 (by rfl) ⟨249560, by rfl⟩) R499121
theorem R332801 : Reach 332801 := rs (se 2 (by rfl) ⟨124800, by rfl⟩) R249601
theorem R37895 : Reach 37895 := rs (se 1 (by rfl) ⟨28421, by rfl⟩) R56843
theorem R37967 : Reach 37967 := rs (se 1 (by rfl) ⟨28475, by rfl⟩) R56951
theorem R38011 : Reach 38011 := rs (se 1 (by rfl) ⟨28508, by rfl⟩) R57017
theorem R38087 : Reach 38087 := rs (se 1 (by rfl) ⟨28565, by rfl⟩) R57131
theorem R38135 : Reach 38135 := rs (se 1 (by rfl) ⟨28601, by rfl⟩) R57203
theorem R38249 : Reach 38249 := rs (se 2 (by rfl) ⟨14343, by rfl⟩) R28687
theorem R38327 : Reach 38327 := rs (se 1 (by rfl) ⟨28745, by rfl⟩) R57491
theorem R136667 : Reach 136667 := rs (se 1 (by rfl) ⟨102500, by rfl⟩) R205001
theorem R38363 : Reach 38363 := rs (se 1 (by rfl) ⟨28772, by rfl⟩) R57545
theorem R38729 : Reach 38729 := rs (se 2 (by rfl) ⟨14523, by rfl⟩) R29047
theorem R38831 : Reach 38831 := rs (se 1 (by rfl) ⟨29123, by rfl⟩) R58247
theorem R38843 : Reach 38843 := rs (se 1 (by rfl) ⟨29132, by rfl⟩) R58265
theorem R38921 : Reach 38921 := rs (se 2 (by rfl) ⟨14595, by rfl⟩) R29191
theorem R38951 : Reach 38951 := rs (se 1 (by rfl) ⟨29213, by rfl⟩) R58427
theorem R38969 : Reach 38969 := rs (se 2 (by rfl) ⟨14613, by rfl⟩) R29227
theorem R39035 : Reach 39035 := rs (se 1 (by rfl) ⟨29276, by rfl⟩) R58553
theorem R39083 : Reach 39083 := rs (se 1 (by rfl) ⟨29312, by rfl⟩) R58625
theorem R39161 : Reach 39161 := rs (se 2 (by rfl) ⟨14685, by rfl⟩) R29371
theorem R39263 : Reach 39263 := rs (se 1 (by rfl) ⟨29447, by rfl⟩) R58895
theorem R39275 : Reach 39275 := rs (se 1 (by rfl) ⟨29456, by rfl⟩) R58913
theorem R39311 : Reach 39311 := rs (se 1 (by rfl) ⟨29483, by rfl⟩) R58967
theorem R39431 : Reach 39431 := rs (se 1 (by rfl) ⟨29573, by rfl⟩) R59147
theorem R39503 : Reach 39503 := rs (se 1 (by rfl) ⟨29627, by rfl⟩) R59255
theorem R105095 : Reach 105095 := rs (se 1 (by rfl) ⟨78821, by rfl⟩) R157643
theorem R39623 : Reach 39623 := rs (se 1 (by rfl) ⟨29717, by rfl⟩) R59435
theorem R39671 : Reach 39671 := rs (se 1 (by rfl) ⟨29753, by rfl⟩) R59507
theorem R39785 : Reach 39785 := rs (se 2 (by rfl) ⟨14919, by rfl⟩) R29839
theorem R39863 : Reach 39863 := rs (se 1 (by rfl) ⟨29897, by rfl⟩) R59795
theorem R39899 : Reach 39899 := rs (se 1 (by rfl) ⟨29924, by rfl⟩) R59849
theorem R170981 : Reach 170981 := rs (se 4 (by rfl) ⟨16029, by rfl⟩) R32059
theorem R39943 : Reach 39943 := rs (se 1 (by rfl) ⟨29957, by rfl⟩) R59915
theorem R171179 : Reach 171179 := rs (se 1 (by rfl) ⟨128384, by rfl⟩) R256769
theorem R40135 : Reach 40135 := rs (se 1 (by rfl) ⟨30101, by rfl⟩) R60203
theorem R40265 : Reach 40265 := rs (se 2 (by rfl) ⟨15099, by rfl⟩) R30199
theorem R40297 : Reach 40297 := rs (se 2 (by rfl) ⟨15111, by rfl⟩) R30223
theorem R40367 : Reach 40367 := rs (se 1 (by rfl) ⟨30275, by rfl⟩) R60551
theorem R40379 : Reach 40379 := rs (se 1 (by rfl) ⟨30284, by rfl⟩) R60569
theorem R40457 : Reach 40457 := rs (se 2 (by rfl) ⟨15171, by rfl⟩) R30343
theorem R40487 : Reach 40487 := rs (se 1 (by rfl) ⟨30365, by rfl⟩) R60731
theorem R40505 : Reach 40505 := rs (se 2 (by rfl) ⟨15189, by rfl⟩) R30379
theorem R40571 : Reach 40571 := rs (se 1 (by rfl) ⟨30428, by rfl⟩) R60857
theorem R171665 : Reach 171665 := rs (se 2 (by rfl) ⟨64374, by rfl⟩) R128749
theorem R40619 : Reach 40619 := rs (se 1 (by rfl) ⟨30464, by rfl⟩) R60929
theorem R139103 : Reach 139103 := rs (se 1 (by rfl) ⟨104327, by rfl⟩) R208655
theorem R40799 : Reach 40799 := rs (se 1 (by rfl) ⟨30599, by rfl⟩) R61199
theorem R73655 : Reach 73655 := rs (se 1 (by rfl) ⟨55241, by rfl⟩) R110483
theorem R434105 : Reach 434105 := rs (se 2 (by rfl) ⟨162789, by rfl⟩) R325579
theorem R40891 : Reach 40891 := rs (se 1 (by rfl) ⟨30668, by rfl⟩) R61337
theorem R40999 : Reach 40999 := rs (se 1 (by rfl) ⟨30749, by rfl⟩) R61499
theorem R139421 : Reach 139421 := rs (se 3 (by rfl) ⟨26141, by rfl⟩) R52283
theorem R41323 : Reach 41323 := rs (se 1 (by rfl) ⟨30992, by rfl⟩) R61985
theorem R41801 : Reach 41801 := rs (se 2 (by rfl) ⟨15675, by rfl⟩) R31351
theorem R74591 : Reach 74591 := rs (se 1 (by rfl) ⟨55943, by rfl⟩) R111887
theorem R861131 : Reach 861131 := rs (se 1 (by rfl) ⟨645848, by rfl⟩) R1291697
theorem R468017 : Reach 468017 := rs (se 2 (by rfl) ⟨175506, by rfl⟩) R351013
theorem R75019 : Reach 75019 := rs (se 1 (by rfl) ⟨56264, by rfl⟩) R112529
theorem R42383 : Reach 42383 := rs (se 1 (by rfl) ⟨31787, by rfl⟩) R63575
theorem R271781 : Reach 271781 := rs (se 4 (by rfl) ⟨25479, by rfl⟩) R50959
theorem R42619 : Reach 42619 := rs (se 1 (by rfl) ⟨31964, by rfl⟩) R63929
theorem R108155 : Reach 108155 := rs (se 1 (by rfl) ⟨81116, by rfl⟩) R162233
theorem R42707 : Reach 42707 := rs (se 1 (by rfl) ⟨32030, by rfl⟩) R64061
theorem R239419 : Reach 239419 := rs (se 1 (by rfl) ⟨179564, by rfl⟩) R359129
theorem R43105 : Reach 43105 := rs (se 2 (by rfl) ⟨16164, by rfl⟩) R32329
theorem R272641 : Reach 272641 := rs (se 2 (by rfl) ⟨102240, by rfl⟩) R204481
theorem R43483 : Reach 43483 := rs (se 1 (by rfl) ⟨32612, by rfl⟩) R65225
theorem R600605 : Reach 600605 := rs (se 3 (by rfl) ⟨112613, by rfl⟩) R225227
theorem R76427 : Reach 76427 := rs (se 1 (by rfl) ⟨57320, by rfl⟩) R114641
theorem R76477 : Reach 76477 := rs (se 3 (by rfl) ⟨14339, by rfl⟩) R28679
theorem R109487 : Reach 109487 := rs (se 1 (by rfl) ⟨82115, by rfl⟩) R164231
theorem R76727 : Reach 76727 := rs (se 1 (by rfl) ⟨57545, by rfl⟩) R115091
theorem R142337 : Reach 142337 := rs (se 2 (by rfl) ⟨53376, by rfl⟩) R106753
theorem R44111 : Reach 44111 := rs (se 1 (by rfl) ⟨33083, by rfl⟩) R66167
theorem R142793 : Reach 142793 := rs (se 2 (by rfl) ⟨53547, by rfl⟩) R107095
theorem R44563 : Reach 44563 := rs (se 1 (by rfl) ⟨33422, by rfl⟩) R66845
theorem R143147 : Reach 143147 := rs (se 1 (by rfl) ⟨107360, by rfl⟩) R214721
theorem R110497 : Reach 110497 := rs (se 2 (by rfl) ⟨41436, by rfl⟩) R82873
theorem R44975 : Reach 44975 := rs (se 1 (by rfl) ⟨33731, by rfl⟩) R67463
theorem R45407 : Reach 45407 := rs (se 1 (by rfl) ⟨34055, by rfl⟩) R68111
theorem R78209 : Reach 78209 := rs (se 2 (by rfl) ⟨29328, by rfl⟩) R58657
theorem R537299 : Reach 537299 := rs (se 1 (by rfl) ⟨402974, by rfl⟩) R805949
theorem R45815 : Reach 45815 := rs (se 1 (by rfl) ⟨34361, by rfl⟩) R68723
theorem R341263 : Reach 341263 := rs (se 1 (by rfl) ⟨255947, by rfl⟩) R511895
theorem R177497 : Reach 177497 := rs (se 2 (by rfl) ⟨66561, by rfl⟩) R133123
theorem R603611 : Reach 603611 := rs (se 1 (by rfl) ⟨452708, by rfl⟩) R905417
theorem R144935 : Reach 144935 := rs (se 1 (by rfl) ⟨108701, by rfl⟩) R217403
theorem R46649 : Reach 46649 := rs (se 2 (by rfl) ⟨17493, by rfl⟩) R34987
theorem R112427 : Reach 112427 := rs (se 1 (by rfl) ⟨84320, by rfl⟩) R168641
theorem R80189 : Reach 80189 := rs (se 3 (by rfl) ⟨15035, by rfl⟩) R30071
theorem R113177 : Reach 113177 := rs (se 2 (by rfl) ⟨42441, by rfl⟩) R84883
theorem R80669 : Reach 80669 := rs (se 3 (by rfl) ⟨15125, by rfl⟩) R30251
theorem R342967 : Reach 342967 := rs (se 1 (by rfl) ⟨257225, by rfl⟩) R514451
theorem R48251 : Reach 48251 := rs (se 1 (by rfl) ⟨36188, by rfl⟩) R72377
theorem R81053 : Reach 81053 := rs (se 3 (by rfl) ⟨15197, by rfl⟩) R30395
theorem R146711 : Reach 146711 := rs (se 1 (by rfl) ⟨110033, by rfl⟩) R220067
theorem R48737 : Reach 48737 := rs (se 2 (by rfl) ⟨18276, by rfl⟩) R36553
theorem R81593 : Reach 81593 := rs (se 2 (by rfl) ⟨30597, by rfl⟩) R61195
theorem R147133 : Reach 147133 := rs (se 3 (by rfl) ⟨27587, by rfl⟩) R55175
theorem R48851 : Reach 48851 := rs (se 1 (by rfl) ⟨36638, by rfl⟩) R73277
theorem R49079 : Reach 49079 := rs (se 1 (by rfl) ⟨36809, by rfl⟩) R73619
theorem R180305 : Reach 180305 := rs (se 2 (by rfl) ⟨67614, by rfl⟩) R135229
theorem R114803 : Reach 114803 := rs (se 1 (by rfl) ⟨86102, by rfl⟩) R172205
theorem R82187 : Reach 82187 := rs (se 1 (by rfl) ⟨61640, by rfl⟩) R123281
theorem R49481 : Reach 49481 := rs (se 2 (by rfl) ⟨18555, by rfl⟩) R37111
theorem R82301 : Reach 82301 := rs (se 3 (by rfl) ⟨15431, by rfl⟩) R30863
theorem R82457 : Reach 82457 := rs (se 2 (by rfl) ⟨30921, by rfl⟩) R61843
theorem R50195 : Reach 50195 := rs (se 1 (by rfl) ⟨37646, by rfl⟩) R75293
theorem R115763 : Reach 115763 := rs (se 1 (by rfl) ⟨86822, by rfl⟩) R173645
theorem R50233 : Reach 50233 := rs (se 2 (by rfl) ⟨18837, by rfl⟩) R37675
theorem R50537 : Reach 50537 := rs (se 2 (by rfl) ⟨18951, by rfl⟩) R37903
theorem R83591 : Reach 83591 := rs (se 1 (by rfl) ⟨62693, by rfl⟩) R125387
theorem R83645 : Reach 83645 := rs (se 3 (by rfl) ⟨15683, by rfl⟩) R31367
theorem R83807 : Reach 83807 := rs (se 1 (by rfl) ⟨62855, by rfl⟩) R125711
theorem R149435 : Reach 149435 := rs (se 1 (by rfl) ⟨112076, by rfl⟩) R224153
theorem R83969 : Reach 83969 := rs (se 2 (by rfl) ⟨31488, by rfl⟩) R62977
theorem R83987 : Reach 83987 := rs (se 1 (by rfl) ⟨62990, by rfl⟩) R125981
theorem R51835 : Reach 51835 := rs (se 1 (by rfl) ⟨38876, by rfl⟩) R77753
theorem R84691 : Reach 84691 := rs (se 1 (by rfl) ⟨63518, by rfl⟩) R127037
theorem R84779 : Reach 84779 := rs (se 1 (by rfl) ⟨63584, by rfl⟩) R127169
theorem R84845 : Reach 84845 := rs (se 3 (by rfl) ⟨15908, by rfl⟩) R31817
theorem R150493 : Reach 150493 := rs (se 3 (by rfl) ⟨28217, by rfl⟩) R56435
theorem R85049 : Reach 85049 := rs (se 2 (by rfl) ⟨31893, by rfl⟩) R63787
theorem R85259 : Reach 85259 := rs (se 1 (by rfl) ⟨63944, by rfl⟩) R127889
theorem R85373 : Reach 85373 := rs (se 3 (by rfl) ⟨16007, by rfl⟩) R32015
theorem R970157 : Reach 970157 := rs (se 3 (by rfl) ⟨181904, by rfl⟩) R363809
theorem R118235 : Reach 118235 := rs (se 1 (by rfl) ⟨88676, by rfl⟩) R177353
theorem R85627 : Reach 85627 := rs (se 1 (by rfl) ⟨64220, by rfl⟩) R128441
theorem R85643 : Reach 85643 := rs (se 1 (by rfl) ⟨64232, by rfl⟩) R128465
theorem R118417 : Reach 118417 := rs (se 2 (by rfl) ⟨44406, by rfl⟩) R88813
theorem R85703 : Reach 85703 := rs (se 1 (by rfl) ⟨64277, by rfl⟩) R128555
theorem R53099 : Reach 53099 := rs (se 1 (by rfl) ⟨39824, by rfl⟩) R79649
theorem R53153 : Reach 53153 := rs (se 2 (by rfl) ⟨19932, by rfl⟩) R39865
theorem R53495 : Reach 53495 := rs (se 1 (by rfl) ⟨40121, by rfl⟩) R80243
theorem R86561 : Reach 86561 := rs (se 2 (by rfl) ⟨32460, by rfl⟩) R64921
theorem R86777 : Reach 86777 := rs (se 2 (by rfl) ⟨32541, by rfl⟩) R65083
theorem R119555 : Reach 119555 := rs (se 1 (by rfl) ⟨89666, by rfl⟩) R179333
theorem R774917 : Reach 774917 := rs (se 4 (by rfl) ⟨72648, by rfl⟩) R145297
theorem R54089 : Reach 54089 := rs (se 2 (by rfl) ⟨20283, by rfl⟩) R40567
theorem R185165 : Reach 185165 := rs (se 3 (by rfl) ⟨34718, by rfl⟩) R69437
theorem R86903 : Reach 86903 := rs (se 1 (by rfl) ⟨65177, by rfl⟩) R130355
theorem R87047 : Reach 87047 := rs (se 1 (by rfl) ⟨65285, by rfl⟩) R130571
theorem R87155 : Reach 87155 := rs (se 1 (by rfl) ⟨65366, by rfl⟩) R130733
theorem R87421 : Reach 87421 := rs (se 3 (by rfl) ⟨16391, by rfl⟩) R32783
theorem R87425 : Reach 87425 := rs (se 2 (by rfl) ⟨32784, by rfl⟩) R65569
theorem R87533 : Reach 87533 := rs (se 3 (by rfl) ⟨16412, by rfl⟩) R32825
theorem R54881 : Reach 54881 := rs (se 2 (by rfl) ⟨20580, by rfl⟩) R41161
theorem R153211 : Reach 153211 := rs (se 1 (by rfl) ⟨114908, by rfl⟩) R229817
theorem R55223 : Reach 55223 := rs (se 1 (by rfl) ⟨41417, by rfl⟩) R82835
theorem R88235 : Reach 88235 := rs (se 1 (by rfl) ⟨66176, by rfl⟩) R132353
theorem R121175 : Reach 121175 := rs (se 1 (by rfl) ⟨90881, by rfl⟩) R181763
theorem R711017 : Reach 711017 := rs (se 2 (by rfl) ⟨266631, by rfl⟩) R533263
theorem R55817 : Reach 55817 := rs (se 2 (by rfl) ⟨20931, by rfl⟩) R41863
theorem R88775 : Reach 88775 := rs (se 1 (by rfl) ⟨66581, by rfl⟩) R133163
theorem R56159 : Reach 56159 := rs (se 1 (by rfl) ⟨42119, by rfl⟩) R84239
theorem R23515 : Reach 23515 := rs (se 1 (by rfl) ⟨17636, by rfl⟩) R35273
theorem R56339 : Reach 56339 := rs (se 1 (by rfl) ⟨42254, by rfl⟩) R84509
theorem R23591 : Reach 23591 := rs (se 1 (by rfl) ⟨17693, by rfl⟩) R35387
theorem R23631 : Reach 23631 := rs (se 1 (by rfl) ⟨17723, by rfl⟩) R35447
theorem R23647 : Reach 23647 := rs (se 1 (by rfl) ⟨17735, by rfl⟩) R35471
theorem R23675 : Reach 23675 := rs (se 1 (by rfl) ⟨17756, by rfl⟩) R35513
theorem R23727 : Reach 23727 := rs (se 1 (by rfl) ⟨17795, by rfl⟩) R35591
theorem R23751 : Reach 23751 := rs (se 1 (by rfl) ⟨17813, by rfl⟩) R35627
theorem R187595 : Reach 187595 := rs (se 1 (by rfl) ⟨140696, by rfl⟩) R281393
theorem R23771 : Reach 23771 := rs (se 1 (by rfl) ⟨17828, by rfl⟩) R35657
theorem R23847 : Reach 23847 := rs (se 1 (by rfl) ⟨17885, by rfl⟩) R35771
theorem R23887 : Reach 23887 := rs (se 1 (by rfl) ⟨17915, by rfl⟩) R35831
theorem R23903 : Reach 23903 := rs (se 1 (by rfl) ⟨17927, by rfl⟩) R35855
theorem R56681 : Reach 56681 := rs (se 2 (by rfl) ⟨21255, by rfl⟩) R42511
theorem R23931 : Reach 23931 := rs (se 1 (by rfl) ⟨17948, by rfl⟩) R35897
theorem R23983 : Reach 23983 := rs (se 1 (by rfl) ⟨17987, by rfl⟩) R35975
theorem R24007 : Reach 24007 := rs (se 1 (by rfl) ⟨18005, by rfl⟩) R36011
theorem R89545 : Reach 89545 := rs (se 2 (by rfl) ⟨33579, by rfl⟩) R67159
theorem R24027 : Reach 24027 := rs (se 1 (by rfl) ⟨18020, by rfl⟩) R36041
theorem R24103 : Reach 24103 := rs (se 1 (by rfl) ⟨18077, by rfl⟩) R36155
theorem R89639 : Reach 89639 := rs (se 1 (by rfl) ⟨67229, by rfl⟩) R134459
theorem R24143 : Reach 24143 := rs (se 1 (by rfl) ⟨18107, by rfl⟩) R36215
theorem R187991 : Reach 187991 := rs (se 1 (by rfl) ⟨140993, by rfl⟩) R281987
theorem R24159 : Reach 24159 := rs (se 1 (by rfl) ⟨18119, by rfl⟩) R36239
theorem R24187 : Reach 24187 := rs (se 1 (by rfl) ⟨18140, by rfl⟩) R36281
theorem R89747 : Reach 89747 := rs (se 1 (by rfl) ⟨67310, by rfl⟩) R134621
theorem R24239 : Reach 24239 := rs (se 1 (by rfl) ⟨18179, by rfl⟩) R36359
theorem R24263 : Reach 24263 := rs (se 1 (by rfl) ⟨18197, by rfl⟩) R36395
theorem R24283 : Reach 24283 := rs (se 1 (by rfl) ⟨18212, by rfl⟩) R36425
theorem R89849 : Reach 89849 := rs (se 2 (by rfl) ⟨33693, by rfl⟩) R67387
theorem R24359 : Reach 24359 := rs (se 1 (by rfl) ⟨18269, by rfl⟩) R36539
theorem R188203 : Reach 188203 := rs (se 1 (by rfl) ⟨141152, by rfl⟩) R282305
theorem R188219 : Reach 188219 := rs (se 1 (by rfl) ⟨141164, by rfl⟩) R282329
theorem R24399 : Reach 24399 := rs (se 1 (by rfl) ⟨18299, by rfl⟩) R36599
theorem R24415 : Reach 24415 := rs (se 1 (by rfl) ⟨18311, by rfl⟩) R36623
theorem R89963 : Reach 89963 := rs (se 1 (by rfl) ⟨67472, by rfl⟩) R134945
theorem R24443 : Reach 24443 := rs (se 1 (by rfl) ⟨18332, by rfl⟩) R36665
theorem R90017 : Reach 90017 := rs (se 2 (by rfl) ⟨33756, by rfl⟩) R67513
theorem R90031 : Reach 90031 := rs (se 1 (by rfl) ⟨67523, by rfl⟩) R135047
theorem R24495 : Reach 24495 := rs (se 1 (by rfl) ⟨18371, by rfl⟩) R36743
theorem R57275 : Reach 57275 := rs (se 1 (by rfl) ⟨42956, by rfl⟩) R85913
theorem R24519 : Reach 24519 := rs (se 1 (by rfl) ⟨18389, by rfl⟩) R36779
theorem R24539 : Reach 24539 := rs (se 1 (by rfl) ⟨18404, by rfl⟩) R36809
theorem R24615 : Reach 24615 := rs (se 1 (by rfl) ⟨18461, by rfl⟩) R36923
theorem R57401 : Reach 57401 := rs (se 2 (by rfl) ⟨21525, by rfl⟩) R43051
theorem R24655 : Reach 24655 := rs (se 1 (by rfl) ⟨18491, by rfl⟩) R36983
theorem R24671 : Reach 24671 := rs (se 1 (by rfl) ⟨18503, by rfl⟩) R37007
theorem R24699 : Reach 24699 := rs (se 1 (by rfl) ⟨18524, by rfl⟩) R37049
theorem R24751 : Reach 24751 := rs (se 1 (by rfl) ⟨18563, by rfl⟩) R37127
theorem R24775 : Reach 24775 := rs (se 1 (by rfl) ⟨18581, by rfl⟩) R37163
theorem R24927 : Reach 24927 := rs (se 1 (by rfl) ⟨18695, by rfl⟩) R37391
theorem R57743 : Reach 57743 := rs (se 1 (by rfl) ⟨43307, by rfl⟩) R86615
theorem R25007 : Reach 25007 := rs (se 1 (by rfl) ⟨18755, by rfl⟩) R37511
theorem R25051 : Reach 25051 := rs (se 1 (by rfl) ⟨18788, by rfl⟩) R37577
theorem R90611 : Reach 90611 := rs (se 1 (by rfl) ⟨67958, by rfl⟩) R135917
theorem R25127 : Reach 25127 := rs (se 1 (by rfl) ⟨18845, by rfl⟩) R37691
theorem R25167 : Reach 25167 := rs (se 1 (by rfl) ⟨18875, by rfl⟩) R37751
theorem R25211 : Reach 25211 := rs (se 1 (by rfl) ⟨18908, by rfl⟩) R37817
theorem R57995 : Reach 57995 := rs (se 1 (by rfl) ⟨43496, by rfl⟩) R86993
theorem R25287 : Reach 25287 := rs (se 1 (by rfl) ⟨18965, by rfl⟩) R37931
theorem R58067 : Reach 58067 := rs (se 1 (by rfl) ⟨43550, by rfl⟩) R87101
theorem R25439 : Reach 25439 := rs (se 1 (by rfl) ⟨19079, by rfl⟩) R38159
theorem R90989 : Reach 90989 := rs (se 3 (by rfl) ⟨17060, by rfl⟩) R34121
theorem R25519 : Reach 25519 := rs (se 1 (by rfl) ⟨19139, by rfl⟩) R38279
theorem R25563 : Reach 25563 := rs (se 1 (by rfl) ⟨19172, by rfl⟩) R38345
theorem R91151 : Reach 91151 := rs (se 1 (by rfl) ⟨68363, by rfl⟩) R136727
theorem R25639 : Reach 25639 := rs (se 1 (by rfl) ⟨19229, by rfl⟩) R38459
theorem R25679 : Reach 25679 := rs (se 1 (by rfl) ⟨19259, by rfl⟩) R38519
theorem R25723 : Reach 25723 := rs (se 1 (by rfl) ⟨19292, by rfl⟩) R38585
theorem R91307 : Reach 91307 := rs (se 1 (by rfl) ⟨68480, by rfl⟩) R136961
theorem R91331 : Reach 91331 := rs (se 1 (by rfl) ⟨68498, by rfl⟩) R136997
theorem R25799 : Reach 25799 := rs (se 1 (by rfl) ⟨19349, by rfl⟩) R38699
theorem R25951 : Reach 25951 := rs (se 1 (by rfl) ⟨19463, by rfl⟩) R38927
theorem R26031 : Reach 26031 := rs (se 1 (by rfl) ⟨19523, by rfl⟩) R39047
theorem R26075 : Reach 26075 := rs (se 1 (by rfl) ⟨19556, by rfl⟩) R39113
theorem R26151 : Reach 26151 := rs (se 1 (by rfl) ⟨19613, by rfl⟩) R39227
theorem R26191 : Reach 26191 := rs (se 1 (by rfl) ⟨19643, by rfl⟩) R39287
theorem R59003 : Reach 59003 := rs (se 1 (by rfl) ⟨44252, by rfl⟩) R88505
theorem R26235 : Reach 26235 := rs (se 1 (by rfl) ⟨19676, by rfl⟩) R39353
theorem R255635 : Reach 255635 := rs (se 1 (by rfl) ⟨191726, by rfl⟩) R383453
theorem R26311 : Reach 26311 := rs (se 1 (by rfl) ⟨19733, by rfl⟩) R39467
theorem R59129 : Reach 59129 := rs (se 2 (by rfl) ⟨22173, by rfl⟩) R44347
theorem R124739 : Reach 124739 := rs (se 1 (by rfl) ⟨93554, by rfl⟩) R187109
theorem R26463 : Reach 26463 := rs (se 1 (by rfl) ⟨19847, by rfl⟩) R39695
theorem R26543 : Reach 26543 := rs (se 1 (by rfl) ⟨19907, by rfl⟩) R39815
theorem R124865 : Reach 124865 := rs (se 2 (by rfl) ⟨46824, by rfl⟩) R93649
theorem R26587 : Reach 26587 := rs (se 1 (by rfl) ⟨19940, by rfl⟩) R39881
theorem R59399 : Reach 59399 := rs (se 1 (by rfl) ⟨44549, by rfl⟩) R89099
theorem R26663 : Reach 26663 := rs (se 1 (by rfl) ⟨19997, by rfl⟩) R39995
theorem R59471 : Reach 59471 := rs (se 1 (by rfl) ⟨44603, by rfl⟩) R89207
theorem R26703 : Reach 26703 := rs (se 1 (by rfl) ⟨20027, by rfl⟩) R40055
theorem R26747 : Reach 26747 := rs (se 1 (by rfl) ⟨20060, by rfl⟩) R40121
theorem R26823 : Reach 26823 := rs (se 1 (by rfl) ⟨20117, by rfl⟩) R40235
theorem R26975 : Reach 26975 := rs (se 1 (by rfl) ⟨20231, by rfl⟩) R40463
theorem R158057 : Reach 158057 := rs (se 2 (by rfl) ⟨59271, by rfl⟩) R118543
theorem R59777 : Reach 59777 := rs (se 2 (by rfl) ⟨22416, by rfl⟩) R44833
theorem R27055 : Reach 27055 := rs (se 1 (by rfl) ⟨20291, by rfl⟩) R40583
theorem R59867 : Reach 59867 := rs (se 1 (by rfl) ⟨44900, by rfl⟩) R89801
theorem R27099 : Reach 27099 := rs (se 1 (by rfl) ⟨20324, by rfl⟩) R40649
theorem R27175 : Reach 27175 := rs (se 1 (by rfl) ⟨20381, by rfl⟩) R40763
theorem R60119 : Reach 60119 := rs (se 1 (by rfl) ⟨45089, by rfl⟩) R90179
theorem R518987 : Reach 518987 := rs (se 1 (by rfl) ⟨389240, by rfl⟩) R778481
theorem R60335 : Reach 60335 := rs (se 1 (by rfl) ⟨45251, by rfl⟩) R90503
theorem R60587 : Reach 60587 := rs (se 1 (by rfl) ⟨45440, by rfl⟩) R90881
theorem R715969 : Reach 715969 := rs (se 2 (by rfl) ⟨268488, by rfl⟩) R536977
theorem R93905 : Reach 93905 := rs (se 2 (by rfl) ⟨35214, by rfl⟩) R70429
theorem R159583 : Reach 159583 := rs (se 1 (by rfl) ⟨119687, by rfl⟩) R239375
theorem R94223 : Reach 94223 := rs (se 1 (by rfl) ⟨70667, by rfl⟩) R141335
theorem R61519 : Reach 61519 := rs (se 1 (by rfl) ⟨46139, by rfl⟩) R92279
theorem R159833 : Reach 159833 := rs (se 2 (by rfl) ⟨59937, by rfl⟩) R119875
theorem R28795 : Reach 28795 := rs (se 1 (by rfl) ⟨21596, by rfl⟩) R43193
theorem R29035 : Reach 29035 := rs (se 1 (by rfl) ⟨21776, by rfl⟩) R43553
theorem R225665 : Reach 225665 := rs (se 2 (by rfl) ⟨84624, by rfl⟩) R169249
theorem R94729 : Reach 94729 := rs (se 2 (by rfl) ⟨35523, by rfl⟩) R71047
theorem R29263 : Reach 29263 := rs (se 1 (by rfl) ⟨21947, by rfl⟩) R43895
theorem R62167 : Reach 62167 := rs (se 1 (by rfl) ⟨46625, by rfl⟩) R93251
theorem R160541 : Reach 160541 := rs (se 3 (by rfl) ⟨30101, by rfl⟩) R60203
theorem R127817 : Reach 127817 := rs (se 2 (by rfl) ⟨47931, by rfl⟩) R95863
theorem R193427 : Reach 193427 := rs (se 1 (by rfl) ⟨145070, by rfl⟩) R290141
theorem R914327 : Reach 914327 := rs (se 1 (by rfl) ⟨685745, by rfl⟩) R1371491
theorem R29623 : Reach 29623 := rs (se 1 (by rfl) ⟨22217, by rfl⟩) R44435
theorem R29659 : Reach 29659 := rs (se 1 (by rfl) ⟨22244, by rfl⟩) R44489
theorem R259037 : Reach 259037 := rs (se 3 (by rfl) ⟨48569, by rfl⟩) R97139
theorem R62471 : Reach 62471 := rs (se 1 (by rfl) ⟨46853, by rfl⟩) R93707
theorem R30127 : Reach 30127 := rs (se 1 (by rfl) ⟨22595, by rfl⟩) R45191
theorem R62963 : Reach 62963 := rs (se 1 (by rfl) ⟨47222, by rfl⟩) R94445
theorem R194363 : Reach 194363 := rs (se 1 (by rfl) ⟨145772, by rfl⟩) R291545
theorem R30559 : Reach 30559 := rs (se 1 (by rfl) ⟨22919, by rfl⟩) R45839
theorem R194399 : Reach 194399 := rs (se 1 (by rfl) ⟨145799, by rfl⟩) R291599
theorem R259949 : Reach 259949 := rs (se 3 (by rfl) ⟨48740, by rfl⟩) R97481
theorem R96187 : Reach 96187 := rs (se 1 (by rfl) ⟨72140, by rfl⟩) R144281
theorem R96335 : Reach 96335 := rs (se 1 (by rfl) ⟨72251, by rfl⟩) R144503
theorem R260185 : Reach 260185 := rs (se 2 (by rfl) ⟨97569, by rfl⟩) R195139
theorem R129113 : Reach 129113 := rs (se 2 (by rfl) ⟨48417, by rfl⟩) R96835
theorem R227585 : Reach 227585 := rs (se 2 (by rfl) ⟨85344, by rfl⟩) R170689
theorem R31195 : Reach 31195 := rs (se 1 (by rfl) ⟨23396, by rfl⟩) R46793
theorem R129671 : Reach 129671 := rs (se 1 (by rfl) ⟨97253, by rfl⟩) R194507
theorem R64759 : Reach 64759 := rs (se 1 (by rfl) ⟨48569, by rfl⟩) R97139
theorem R65033 : Reach 65033 := rs (se 2 (by rfl) ⟨24387, by rfl⟩) R48775
theorem R65063 : Reach 65063 := rs (se 1 (by rfl) ⟨48797, by rfl⟩) R97595
theorem R130859 : Reach 130859 := rs (se 1 (by rfl) ⟨98144, by rfl⟩) R196289
theorem R65387 : Reach 65387 := rs (se 1 (by rfl) ⟨49040, by rfl⟩) R98081
theorem R32987 : Reach 32987 := rs (se 1 (by rfl) ⟨24740, by rfl⟩) R49481
theorem R131705 : Reach 131705 := rs (se 2 (by rfl) ⟨49389, by rfl⟩) R98779
theorem R33463 : Reach 33463 := rs (se 1 (by rfl) ⟨25097, by rfl⟩) R50195
theorem R33691 : Reach 33691 := rs (se 1 (by rfl) ⟨25268, by rfl⟩) R50537
theorem R66703 : Reach 66703 := rs (se 1 (by rfl) ⟨50027, by rfl⟩) R100055
theorem R99623 : Reach 99623 := rs (se 1 (by rfl) ⟨74717, by rfl⟩) R149435
theorem R66977 : Reach 66977 := rs (se 2 (by rfl) ⟨25116, by rfl⟩) R50233
theorem R886373 : Reach 886373 := rs (se 4 (by rfl) ⟨83097, by rfl⟩) R166195
theorem R100025 : Reach 100025 := rs (se 2 (by rfl) ⟨37509, by rfl⟩) R75019
theorem R67837 : Reach 67837 := rs (se 3 (by rfl) ⟨12719, by rfl⟩) R25439
theorem R133487 : Reach 133487 := rs (se 1 (by rfl) ⟨100115, by rfl⟩) R200231
theorem R2296349 : Reach 2296349 := rs (se 3 (by rfl) ⟨430565, by rfl⟩) R861131
theorem R35399 : Reach 35399 := rs (se 1 (by rfl) ⟨26549, by rfl⟩) R53099
theorem R35435 : Reach 35435 := rs (se 1 (by rfl) ⟨26576, by rfl⟩) R53153
theorem R35663 : Reach 35663 := rs (se 1 (by rfl) ⟨26747, by rfl⟩) R53495
theorem R363521 : Reach 363521 := rs (se 2 (by rfl) ⟨136320, by rfl⟩) R272641
theorem R36059 : Reach 36059 := rs (se 1 (by rfl) ⟨27044, by rfl⟩) R54089
theorem R36233 : Reach 36233 := rs (se 2 (by rfl) ⟨13587, by rfl⟩) R27175
theorem R69113 : Reach 69113 := rs (se 2 (by rfl) ⟨25917, by rfl⟩) R51835
theorem R101969 : Reach 101969 := rs (se 2 (by rfl) ⟨38238, by rfl⟩) R76477
theorem R36587 : Reach 36587 := rs (se 1 (by rfl) ⟨27440, by rfl⟩) R54881
theorem R364445 : Reach 364445 := rs (se 3 (by rfl) ⟨68333, by rfl⟩) R136667
theorem R36815 : Reach 36815 := rs (se 1 (by rfl) ⟨27611, by rfl⟩) R55223
theorem R200657 : Reach 200657 := rs (se 2 (by rfl) ⟨75246, by rfl⟩) R150493
theorem R954625 : Reach 954625 := rs (se 2 (by rfl) ⟨357984, by rfl⟩) R715969
theorem R37211 : Reach 37211 := rs (se 1 (by rfl) ⟨27908, by rfl⟩) R55817
theorem R37439 : Reach 37439 := rs (se 1 (by rfl) ⟨28079, by rfl⟩) R56159
theorem R37559 : Reach 37559 := rs (se 1 (by rfl) ⟨28169, by rfl⟩) R56339
theorem R37787 : Reach 37787 := rs (se 1 (by rfl) ⟨28340, by rfl⟩) R56681
theorem R693197 : Reach 693197 := rs (se 3 (by rfl) ⟨129974, by rfl⟩) R259949
theorem R38183 : Reach 38183 := rs (se 1 (by rfl) ⟨28637, by rfl⟩) R57275
theorem R38267 : Reach 38267 := rs (se 1 (by rfl) ⟨28700, by rfl⟩) R57401
theorem R38393 : Reach 38393 := rs (se 2 (by rfl) ⟨14397, by rfl⟩) R28795
theorem R38495 : Reach 38495 := rs (se 1 (by rfl) ⟨28871, by rfl⟩) R57743
theorem R136889 : Reach 136889 := rs (se 2 (by rfl) ⟨51333, by rfl⟩) R102667
theorem R38663 : Reach 38663 := rs (se 1 (by rfl) ⟨28997, by rfl⟩) R57995
theorem R38711 : Reach 38711 := rs (se 1 (by rfl) ⟨29033, by rfl⟩) R58067
theorem R38713 : Reach 38713 := rs (se 2 (by rfl) ⟨14517, by rfl⟩) R29035
theorem R104429 : Reach 104429 := rs (se 3 (by rfl) ⟨19580, by rfl⟩) R39161
theorem R39017 : Reach 39017 := rs (se 2 (by rfl) ⟨14631, by rfl⟩) R29263
theorem R72103 : Reach 72103 := rs (se 1 (by rfl) ⟨54077, by rfl⟩) R108155
theorem R39335 : Reach 39335 := rs (se 1 (by rfl) ⟨29501, by rfl⟩) R59003
theorem R170423 : Reach 170423 := rs (se 1 (by rfl) ⟨127817, by rfl⟩) R255635
theorem R39419 : Reach 39419 := rs (se 1 (by rfl) ⟨29564, by rfl⟩) R59129
theorem R39497 : Reach 39497 := rs (se 2 (by rfl) ⟨14811, by rfl⟩) R29623
theorem R39545 : Reach 39545 := rs (se 2 (by rfl) ⟨14829, by rfl⟩) R29659
theorem R39599 : Reach 39599 := rs (se 1 (by rfl) ⟨29699, by rfl⟩) R59399
theorem R39647 : Reach 39647 := rs (se 1 (by rfl) ⟨29735, by rfl⟩) R59471
theorem R301805 : Reach 301805 := rs (se 3 (by rfl) ⟨56588, by rfl⟩) R113177
theorem R105371 : Reach 105371 := rs (se 1 (by rfl) ⟨79028, by rfl⟩) R158057
theorem R39851 : Reach 39851 := rs (se 1 (by rfl) ⟨29888, by rfl⟩) R59777
theorem R39911 : Reach 39911 := rs (se 1 (by rfl) ⟨29933, by rfl⟩) R59867
theorem R400403 : Reach 400403 := rs (se 1 (by rfl) ⟨300302, by rfl⟩) R600605
theorem R40079 : Reach 40079 := rs (se 1 (by rfl) ⟨30059, by rfl⟩) R60119
theorem R40169 : Reach 40169 := rs (se 2 (by rfl) ⟨15063, by rfl⟩) R30127
theorem R40223 : Reach 40223 := rs (se 1 (by rfl) ⟨30167, by rfl⟩) R60335
theorem R72991 : Reach 72991 := rs (se 1 (by rfl) ⟨54743, by rfl⟩) R109487
theorem R40391 : Reach 40391 := rs (se 1 (by rfl) ⟨30293, by rfl⟩) R60587
theorem R204281 : Reach 204281 := rs (se 2 (by rfl) ⟨76605, by rfl⟩) R153211
theorem R40745 : Reach 40745 := rs (se 2 (by rfl) ⟨15279, by rfl⟩) R30559
theorem R204605 : Reach 204605 := rs (se 3 (by rfl) ⟨38363, by rfl⟩) R76727
theorem R106555 : Reach 106555 := rs (se 1 (by rfl) ⟨79916, by rfl⟩) R159833
theorem R107027 : Reach 107027 := rs (se 1 (by rfl) ⟨80270, by rfl⟩) R160541
theorem R41593 : Reach 41593 := rs (se 2 (by rfl) ⟨15597, by rfl⟩) R31195
theorem R172691 : Reach 172691 := rs (se 1 (by rfl) ⟨129518, by rfl⟩) R259037
theorem R41647 : Reach 41647 := rs (se 1 (by rfl) ⟨31235, by rfl⟩) R62471
theorem R402407 : Reach 402407 := rs (se 1 (by rfl) ⟨301805, by rfl⟩) R603611
theorem R41975 : Reach 41975 := rs (se 1 (by rfl) ⟨31481, by rfl⟩) R62963
theorem R74951 : Reach 74951 := rs (se 1 (by rfl) ⟨56213, by rfl⟩) R112427
theorem R43355 : Reach 43355 := rs (se 1 (by rfl) ⟨32516, by rfl⟩) R65033
theorem R43375 : Reach 43375 := rs (se 1 (by rfl) ⟨32531, by rfl⟩) R65063
theorem R43591 : Reach 43591 := rs (se 1 (by rfl) ⟨32693, by rfl⟩) R65387
theorem R76535 : Reach 76535 := rs (se 1 (by rfl) ⟨57401, by rfl⟩) R114803
theorem R44023 : Reach 44023 := rs (se 1 (by rfl) ⟨33017, by rfl⟩) R66035
theorem R44327 : Reach 44327 := rs (se 1 (by rfl) ⟨33245, by rfl⟩) R66491
theorem R44705 : Reach 44705 := rs (se 2 (by rfl) ⟨16764, by rfl⟩) R33529
theorem R44779 : Reach 44779 := rs (se 1 (by rfl) ⟨33584, by rfl⟩) R67169
theorem R45751 : Reach 45751 := rs (se 1 (by rfl) ⟨34313, by rfl⟩) R68627
theorem R111469 : Reach 111469 := rs (se 3 (by rfl) ⟨20900, by rfl⟩) R41801
theorem R78823 : Reach 78823 := rs (se 1 (by rfl) ⟨59117, by rfl⟩) R118235
theorem R308701 : Reach 308701 := rs (se 3 (by rfl) ⟨57881, by rfl⟩) R115763
theorem R79703 : Reach 79703 := rs (se 1 (by rfl) ⟨59777, by rfl⟩) R119555
theorem R112921 : Reach 112921 := rs (se 2 (by rfl) ⟨42345, by rfl⟩) R84691
theorem R80783 : Reach 80783 := rs (se 1 (by rfl) ⟨60587, by rfl⟩) R121175
theorem R474011 : Reach 474011 := rs (se 1 (by rfl) ⟨355508, by rfl⟩) R711017
theorem R113987 : Reach 113987 := rs (se 1 (by rfl) ⟨85490, by rfl⟩) R170981
theorem R441773 : Reach 441773 := rs (se 3 (by rfl) ⟨82832, by rfl⟩) R165665
theorem R114119 : Reach 114119 := rs (se 1 (by rfl) ⟨85589, by rfl⟩) R171179
theorem R114169 : Reach 114169 := rs (se 2 (by rfl) ⟨42813, by rfl⟩) R85627
theorem R114443 : Reach 114443 := rs (se 1 (by rfl) ⟨85832, by rfl⟩) R171665
theorem R212777 : Reach 212777 := rs (se 2 (by rfl) ⟨79791, by rfl⟩) R159583
theorem R147329 : Reach 147329 := rs (se 2 (by rfl) ⟨55248, by rfl⟩) R110497
theorem R49103 : Reach 49103 := rs (se 1 (by rfl) ⟨36827, by rfl⟩) R73655
theorem R213029 : Reach 213029 := rs (se 4 (by rfl) ⟨19971, by rfl⟩) R39943
theorem R82025 : Reach 82025 := rs (se 2 (by rfl) ⟨30759, by rfl⟩) R61519
theorem R180377 : Reach 180377 := rs (se 2 (by rfl) ⟨67641, by rfl⟩) R135283
theorem R49727 : Reach 49727 := rs (se 1 (by rfl) ⟨37295, by rfl⟩) R74591
theorem R312011 : Reach 312011 := rs (se 1 (by rfl) ⟨234008, by rfl⟩) R468017
theorem R181187 : Reach 181187 := rs (se 1 (by rfl) ⟨135890, by rfl⟩) R271781
theorem R82889 : Reach 82889 := rs (se 2 (by rfl) ⟨31083, by rfl⟩) R62167
theorem R83159 : Reach 83159 := rs (se 1 (by rfl) ⟨62369, by rfl⟩) R124739
theorem R83243 : Reach 83243 := rs (se 1 (by rfl) ⟨62432, by rfl⟩) R124865
theorem R50681 : Reach 50681 := rs (se 2 (by rfl) ⟨19005, by rfl⟩) R38011
theorem R280253 : Reach 280253 := rs (se 3 (by rfl) ⟨52547, by rfl⟩) R105095
theorem R50951 : Reach 50951 := rs (se 1 (by rfl) ⟨38213, by rfl⟩) R76427
theorem R116561 : Reach 116561 := rs (se 2 (by rfl) ⟨43710, by rfl⟩) R87421
theorem R345991 : Reach 345991 := rs (se 1 (by rfl) ⟨259493, by rfl⟩) R518987
theorem R346913 : Reach 346913 := rs (se 2 (by rfl) ⟨130092, by rfl⟩) R260185
theorem R52139 : Reach 52139 := rs (se 1 (by rfl) ⟨39104, by rfl⟩) R78209
theorem R150443 : Reach 150443 := rs (se 1 (by rfl) ⟨112832, by rfl⟩) R225665
theorem R85211 : Reach 85211 := rs (se 1 (by rfl) ⟨63908, by rfl⟩) R127817
theorem R609551 : Reach 609551 := rs (se 1 (by rfl) ⟨457163, by rfl⟩) R914327
theorem R118331 : Reach 118331 := rs (se 1 (by rfl) ⟨88748, by rfl⟩) R177497
theorem R86075 : Reach 86075 := rs (se 1 (by rfl) ⟨64556, by rfl⟩) R129113
theorem R151723 : Reach 151723 := rs (se 1 (by rfl) ⟨113792, by rfl⟩) R227585
theorem R53459 : Reach 53459 := rs (se 1 (by rfl) ⟨40094, by rfl⟩) R80189
theorem R53513 : Reach 53513 := rs (se 2 (by rfl) ⟨20067, by rfl⟩) R40135
theorem R86345 : Reach 86345 := rs (se 2 (by rfl) ⟨32379, by rfl⟩) R64759
theorem R86447 : Reach 86447 := rs (se 1 (by rfl) ⟨64835, by rfl⟩) R129671
theorem R53729 : Reach 53729 := rs (se 2 (by rfl) ⟨20148, by rfl⟩) R40297
theorem R53779 : Reach 53779 := rs (se 1 (by rfl) ⟨40334, by rfl⟩) R80669
theorem R119393 : Reach 119393 := rs (se 2 (by rfl) ⟨44772, by rfl⟩) R89545
theorem R54035 : Reach 54035 := rs (se 1 (by rfl) ⟨40526, by rfl⟩) R81053
theorem R250937 : Reach 250937 := rs (se 2 (by rfl) ⟨94101, by rfl⟩) R188203
theorem R54395 : Reach 54395 := rs (se 1 (by rfl) ⟨40796, by rfl⟩) R81593
theorem R87239 : Reach 87239 := rs (se 1 (by rfl) ⟨65429, by rfl⟩) R130859
theorem R120041 : Reach 120041 := rs (se 2 (by rfl) ⟨45015, by rfl⟩) R90031
theorem R54521 : Reach 54521 := rs (se 2 (by rfl) ⟨20445, by rfl⟩) R40891
theorem R54665 : Reach 54665 := rs (se 2 (by rfl) ⟨20499, by rfl⟩) R40999
theorem R120203 : Reach 120203 := rs (se 1 (by rfl) ⟨90152, by rfl⟩) R180305
theorem R54791 : Reach 54791 := rs (se 1 (by rfl) ⟨41093, by rfl⟩) R82187
theorem R54971 : Reach 54971 := rs (se 1 (by rfl) ⟨41228, by rfl⟩) R82457
theorem R55097 : Reach 55097 := rs (se 2 (by rfl) ⟨20661, by rfl⟩) R41323
theorem R55727 : Reach 55727 := rs (se 1 (by rfl) ⟨41795, by rfl⟩) R83591
theorem R55763 : Reach 55763 := rs (se 1 (by rfl) ⟨41822, by rfl⟩) R83645
theorem R219671 : Reach 219671 := rs (se 1 (by rfl) ⟨164753, by rfl⟩) R329507
theorem R55871 : Reach 55871 := rs (se 1 (by rfl) ⟨41903, by rfl⟩) R83807
theorem R55979 : Reach 55979 := rs (se 1 (by rfl) ⟨41984, by rfl⟩) R83969
theorem R55991 : Reach 55991 := rs (se 1 (by rfl) ⟨41993, by rfl⟩) R83987
theorem R482233 : Reach 482233 := rs (se 2 (by rfl) ⟨180837, by rfl⟩) R361675
theorem R23503 : Reach 23503 := rs (se 1 (by rfl) ⟨17627, by rfl⟩) R35255
theorem R23527 : Reach 23527 := rs (se 1 (by rfl) ⟨17645, by rfl⟩) R35291
theorem R56519 : Reach 56519 := rs (se 1 (by rfl) ⟨42389, by rfl⟩) R84779
theorem R23839 : Reach 23839 := rs (se 1 (by rfl) ⟨17879, by rfl⟩) R35759
theorem R23899 : Reach 23899 := rs (se 1 (by rfl) ⟨17924, by rfl⟩) R35849
theorem R23919 : Reach 23919 := rs (se 1 (by rfl) ⟨17939, by rfl⟩) R35879
theorem R56699 : Reach 56699 := rs (se 1 (by rfl) ⟨42524, by rfl⟩) R85049
theorem R23975 : Reach 23975 := rs (se 1 (by rfl) ⟨17981, by rfl⟩) R35963
theorem R89531 : Reach 89531 := rs (se 1 (by rfl) ⟨67148, by rfl⟩) R134297
theorem R56825 : Reach 56825 := rs (se 2 (by rfl) ⟨21309, by rfl⟩) R42619
theorem R24059 : Reach 24059 := rs (se 1 (by rfl) ⟨18044, by rfl⟩) R36089
theorem R24127 : Reach 24127 := rs (se 1 (by rfl) ⟨18095, by rfl⟩) R36191
theorem R24135 : Reach 24135 := rs (se 1 (by rfl) ⟨18101, by rfl⟩) R36203
theorem R56915 : Reach 56915 := rs (se 1 (by rfl) ⟨42686, by rfl⟩) R85373
theorem R24287 : Reach 24287 := rs (se 1 (by rfl) ⟨18215, by rfl⟩) R36431
theorem R57095 : Reach 57095 := rs (se 1 (by rfl) ⟨42821, by rfl⟩) R85643
theorem R24367 : Reach 24367 := rs (se 1 (by rfl) ⟨18275, by rfl⟩) R36551
theorem R24475 : Reach 24475 := rs (se 1 (by rfl) ⟨18356, by rfl⟩) R36713
theorem R24527 : Reach 24527 := rs (se 1 (by rfl) ⟨18395, by rfl⟩) R36791
theorem R24551 : Reach 24551 := rs (se 1 (by rfl) ⟨18413, by rfl⟩) R36827
theorem R57473 : Reach 57473 := rs (se 2 (by rfl) ⟨21552, by rfl⟩) R43105
theorem R24795 : Reach 24795 := rs (se 1 (by rfl) ⟨18596, by rfl⟩) R37193
theorem R24863 : Reach 24863 := rs (se 1 (by rfl) ⟨18647, by rfl⟩) R37295
theorem R24871 : Reach 24871 := rs (se 1 (by rfl) ⟨18653, by rfl⟩) R37307
theorem R24923 : Reach 24923 := rs (se 1 (by rfl) ⟨18692, by rfl⟩) R37385
theorem R57707 : Reach 57707 := rs (se 1 (by rfl) ⟨43280, by rfl⟩) R86561
theorem R24943 : Reach 24943 := rs (se 1 (by rfl) ⟨18707, by rfl⟩) R37415
theorem R24955 : Reach 24955 := rs (se 1 (by rfl) ⟨18716, by rfl⟩) R37433
theorem R24999 : Reach 24999 := rs (se 1 (by rfl) ⟨18749, by rfl⟩) R37499
theorem R25031 : Reach 25031 := rs (se 1 (by rfl) ⟨18773, by rfl⟩) R37547
theorem R25083 : Reach 25083 := rs (se 1 (by rfl) ⟨18812, by rfl⟩) R37625
theorem R57851 : Reach 57851 := rs (se 1 (by rfl) ⟨43388, by rfl⟩) R86777
theorem R516611 : Reach 516611 := rs (se 1 (by rfl) ⟨387458, by rfl⟩) R774917
theorem R123443 : Reach 123443 := rs (se 1 (by rfl) ⟨92582, by rfl⟩) R185165
theorem R25151 : Reach 25151 := rs (se 1 (by rfl) ⟨18863, by rfl⟩) R37727
theorem R25159 : Reach 25159 := rs (se 1 (by rfl) ⟨18869, by rfl⟩) R37739
theorem R57935 : Reach 57935 := rs (se 1 (by rfl) ⟨43451, by rfl⟩) R86903
theorem R25183 : Reach 25183 := rs (se 1 (by rfl) ⟨18887, by rfl⟩) R37775
theorem R57977 : Reach 57977 := rs (se 2 (by rfl) ⟨21741, by rfl⟩) R43483
theorem R221831 : Reach 221831 := rs (se 1 (by rfl) ⟨166373, by rfl⟩) R332747
theorem R221867 : Reach 221867 := rs (se 1 (by rfl) ⟨166400, by rfl⟩) R332801
theorem R25263 : Reach 25263 := rs (se 1 (by rfl) ⟨18947, by rfl⟩) R37895
theorem R58031 : Reach 58031 := rs (se 1 (by rfl) ⟨43523, by rfl⟩) R87047
theorem R25311 : Reach 25311 := rs (se 1 (by rfl) ⟨18983, by rfl⟩) R37967
theorem R58103 : Reach 58103 := rs (se 1 (by rfl) ⟨43577, by rfl⟩) R87155
theorem R25391 : Reach 25391 := rs (se 1 (by rfl) ⟨19043, by rfl⟩) R38087
theorem R25423 : Reach 25423 := rs (se 1 (by rfl) ⟨19067, by rfl⟩) R38135
theorem R25499 : Reach 25499 := rs (se 1 (by rfl) ⟨19124, by rfl⟩) R38249
theorem R58283 : Reach 58283 := rs (se 1 (by rfl) ⟨43712, by rfl⟩) R87425
theorem R25551 : Reach 25551 := rs (se 1 (by rfl) ⟨19163, by rfl⟩) R38327
theorem R25575 : Reach 25575 := rs (se 1 (by rfl) ⟨19181, by rfl⟩) R38363
theorem R58355 : Reach 58355 := rs (se 1 (by rfl) ⟨43766, by rfl⟩) R87533
theorem R25819 : Reach 25819 := rs (se 1 (by rfl) ⟨19364, by rfl⟩) R38729
theorem R25887 : Reach 25887 := rs (se 1 (by rfl) ⟨19415, by rfl⟩) R38831
theorem R25895 : Reach 25895 := rs (se 1 (by rfl) ⟨19421, by rfl⟩) R38843
theorem R877877 : Reach 877877 := rs (se 5 (by rfl) ⟨41150, by rfl⟩) R82301
theorem R25947 : Reach 25947 := rs (se 1 (by rfl) ⟨19460, by rfl⟩) R38921
theorem R25967 : Reach 25967 := rs (se 1 (by rfl) ⟨19475, by rfl⟩) R38951
theorem R25979 : Reach 25979 := rs (se 1 (by rfl) ⟨19484, by rfl⟩) R38969
theorem R26023 : Reach 26023 := rs (se 1 (by rfl) ⟨19517, by rfl⟩) R39035
theorem R26055 : Reach 26055 := rs (se 1 (by rfl) ⟨19541, by rfl⟩) R39083
theorem R58823 : Reach 58823 := rs (se 1 (by rfl) ⟨44117, by rfl⟩) R88235
theorem R26107 : Reach 26107 := rs (se 1 (by rfl) ⟨19580, by rfl⟩) R39161
theorem R26175 : Reach 26175 := rs (se 1 (by rfl) ⟨19631, by rfl⟩) R39263
theorem R26183 : Reach 26183 := rs (se 1 (by rfl) ⟨19637, by rfl⟩) R39275
theorem R26207 : Reach 26207 := rs (se 1 (by rfl) ⟨19655, by rfl⟩) R39311
theorem R26287 : Reach 26287 := rs (se 1 (by rfl) ⟨19715, by rfl⟩) R39431
theorem R26335 : Reach 26335 := rs (se 1 (by rfl) ⟨19751, by rfl⟩) R39503
theorem R59183 : Reach 59183 := rs (se 1 (by rfl) ⟨44387, by rfl⟩) R88775
theorem R26415 : Reach 26415 := rs (se 1 (by rfl) ⟨19811, by rfl⟩) R39623
theorem R26447 : Reach 26447 := rs (se 1 (by rfl) ⟨19835, by rfl⟩) R39671
theorem R26523 : Reach 26523 := rs (se 1 (by rfl) ⟨19892, by rfl⟩) R39785
theorem R26575 : Reach 26575 := rs (se 1 (by rfl) ⟨19931, by rfl⟩) R39863
theorem R26599 : Reach 26599 := rs (se 1 (by rfl) ⟨19949, by rfl⟩) R39899
theorem R59417 : Reach 59417 := rs (se 2 (by rfl) ⟨22281, by rfl⟩) R44563
theorem R125063 : Reach 125063 := rs (se 1 (by rfl) ⟨93797, by rfl⟩) R187595
theorem R157889 : Reach 157889 := rs (se 2 (by rfl) ⟨59208, by rfl⟩) R118417
theorem R26843 : Reach 26843 := rs (se 1 (by rfl) ⟨20132, by rfl⟩) R40265
theorem R26911 : Reach 26911 := rs (se 1 (by rfl) ⟨20183, by rfl⟩) R40367
theorem R26919 : Reach 26919 := rs (se 1 (by rfl) ⟨20189, by rfl⟩) R40379
theorem R26971 : Reach 26971 := rs (se 1 (by rfl) ⟨20228, by rfl⟩) R40457
theorem R59759 : Reach 59759 := rs (se 1 (by rfl) ⟨44819, by rfl⟩) R89639
theorem R26991 : Reach 26991 := rs (se 1 (by rfl) ⟨20243, by rfl⟩) R40487
theorem R27003 : Reach 27003 := rs (se 1 (by rfl) ⟨20252, by rfl⟩) R40505
theorem R125327 : Reach 125327 := rs (se 1 (by rfl) ⟨93995, by rfl⟩) R187991
theorem R27047 : Reach 27047 := rs (se 1 (by rfl) ⟨20285, by rfl⟩) R40571
theorem R59831 : Reach 59831 := rs (se 1 (by rfl) ⟨44873, by rfl⟩) R89747
theorem R27079 : Reach 27079 := rs (se 1 (by rfl) ⟨20309, by rfl⟩) R40619
theorem R59899 : Reach 59899 := rs (se 1 (by rfl) ⟨44924, by rfl⟩) R89849
theorem R125479 : Reach 125479 := rs (se 1 (by rfl) ⟨94109, by rfl⟩) R188219
theorem R92735 : Reach 92735 := rs (se 1 (by rfl) ⟨69551, by rfl⟩) R139103
theorem R27199 : Reach 27199 := rs (se 1 (by rfl) ⟨20399, by rfl⟩) R40799
theorem R59975 : Reach 59975 := rs (se 1 (by rfl) ⟨44981, by rfl⟩) R89963
theorem R60011 : Reach 60011 := rs (se 1 (by rfl) ⟨45008, by rfl⟩) R90017
theorem R289403 : Reach 289403 := rs (se 1 (by rfl) ⟨217052, by rfl⟩) R434105
theorem R92947 : Reach 92947 := rs (se 1 (by rfl) ⟨69710, by rfl⟩) R139421
theorem R93053 : Reach 93053 := rs (se 3 (by rfl) ⟨17447, by rfl⟩) R34895
theorem R60407 : Reach 60407 := rs (se 1 (by rfl) ⟨45305, by rfl⟩) R90611
theorem R60659 : Reach 60659 := rs (se 1 (by rfl) ⟨45494, by rfl⟩) R90989
theorem R60767 : Reach 60767 := rs (se 1 (by rfl) ⟨45575, by rfl⟩) R91151
theorem R126305 : Reach 126305 := rs (se 2 (by rfl) ⟨47364, by rfl⟩) R94729
theorem R60871 : Reach 60871 := rs (se 1 (by rfl) ⟨45653, by rfl⟩) R91307
theorem R60887 : Reach 60887 := rs (se 1 (by rfl) ⟨45665, by rfl⟩) R91331
theorem R28255 : Reach 28255 := rs (se 1 (by rfl) ⟨21191, by rfl⟩) R42383
theorem R28471 : Reach 28471 := rs (se 1 (by rfl) ⟨21353, by rfl⟩) R42707
theorem R455017 : Reach 455017 := rs (se 2 (by rfl) ⟨170631, by rfl⟩) R341263
theorem R94891 : Reach 94891 := rs (se 1 (by rfl) ⟨71168, by rfl⟩) R142337
theorem R29407 : Reach 29407 := rs (se 1 (by rfl) ⟨22055, by rfl⟩) R44111
theorem R226253 : Reach 226253 := rs (se 3 (by rfl) ⟨42422, by rfl⟩) R84845
theorem R95195 : Reach 95195 := rs (se 1 (by rfl) ⟨71396, by rfl⟩) R142793
theorem R62603 : Reach 62603 := rs (se 1 (by rfl) ⟨46952, by rfl⟩) R93905
theorem R95431 : Reach 95431 := rs (se 1 (by rfl) ⟨71573, by rfl⟩) R143147
theorem R488693 : Reach 488693 := rs (se 5 (by rfl) ⟨22907, by rfl⟩) R45815
theorem R128249 : Reach 128249 := rs (se 2 (by rfl) ⟨48093, by rfl⟩) R96187
theorem R29983 : Reach 29983 := rs (se 1 (by rfl) ⟨22487, by rfl⟩) R44975
theorem R62815 : Reach 62815 := rs (se 1 (by rfl) ⟨47111, by rfl⟩) R94223
theorem R30271 : Reach 30271 := rs (se 1 (by rfl) ⟨22703, by rfl⟩) R45407
theorem R358199 : Reach 358199 := rs (se 1 (by rfl) ⟨268649, by rfl⟩) R537299
theorem R128951 : Reach 128951 := rs (se 1 (by rfl) ⟨96713, by rfl⟩) R193427
theorem R227357 : Reach 227357 := rs (se 3 (by rfl) ⟨42629, by rfl⟩) R85259
theorem R96623 : Reach 96623 := rs (se 1 (by rfl) ⟨72467, by rfl⟩) R144935
theorem R31099 : Reach 31099 := rs (se 1 (by rfl) ⟨23324, by rfl⟩) R46649
theorem R2587085 : Reach 2587085 := rs (se 3 (by rfl) ⟨485078, by rfl⟩) R970157
theorem R129575 : Reach 129575 := rs (se 1 (by rfl) ⟨97181, by rfl⟩) R194363
theorem R129599 : Reach 129599 := rs (se 1 (by rfl) ⟨97199, by rfl⟩) R194399
theorem R457289 : Reach 457289 := rs (se 2 (by rfl) ⟨171483, by rfl⟩) R342967
theorem R64223 : Reach 64223 := rs (se 1 (by rfl) ⟨48167, by rfl⟩) R96335
theorem R31529 : Reach 31529 := rs (se 2 (by rfl) ⟨11823, by rfl⟩) R23647
theorem R1276901 : Reach 1276901 := rs (se 4 (by rfl) ⟨119709, by rfl⟩) R239419
theorem R228541 : Reach 228541 := rs (se 3 (by rfl) ⟨42851, by rfl⟩) R85703
theorem R32167 : Reach 32167 := rs (se 1 (by rfl) ⟨24125, by rfl⟩) R48251
theorem R97807 : Reach 97807 := rs (se 1 (by rfl) ⟨73355, by rfl⟩) R146711
theorem R196177 : Reach 196177 := rs (se 2 (by rfl) ⟨73566, by rfl⟩) R147133
theorem R32491 : Reach 32491 := rs (se 1 (by rfl) ⟨24368, by rfl⟩) R48737
theorem R32567 : Reach 32567 := rs (se 1 (by rfl) ⟨24425, by rfl⟩) R48851
theorem R32719 : Reach 32719 := rs (se 1 (by rfl) ⟨24539, by rfl⟩) R49079
theorem R33151 : Reach 33151 := rs (se 1 (by rfl) ⟨24863, by rfl⟩) R49727
theorem R66415 : Reach 66415 := rs (se 1 (by rfl) ⟨49811, by rfl⟩) R99623
theorem R33787 : Reach 33787 := rs (se 1 (by rfl) ⟨25340, by rfl⟩) R50681
theorem R590915 : Reach 590915 := rs (se 1 (by rfl) ⟨443186, by rfl⟩) R886373
theorem R66683 : Reach 66683 := rs (se 1 (by rfl) ⟨50012, by rfl⟩) R100025
theorem R230525 : Reach 230525 := rs (se 3 (by rfl) ⟨43223, by rfl⟩) R86447
theorem R33967 : Reach 33967 := rs (se 1 (by rfl) ⟨25475, by rfl⟩) R50951
theorem R231275 : Reach 231275 := rs (se 1 (by rfl) ⟨173456, by rfl⟩) R346913
theorem R34759 : Reach 34759 := rs (se 1 (by rfl) ⟨26069, by rfl⟩) R52139
theorem R100295 : Reach 100295 := rs (se 1 (by rfl) ⟨75221, by rfl⟩) R150443
theorem R67979 : Reach 67979 := rs (se 1 (by rfl) ⟨50984, by rfl⟩) R101969
theorem R461321 : Reach 461321 := rs (se 2 (by rfl) ⟨172995, by rfl⟩) R345991
theorem R35465 : Reach 35465 := rs (se 2 (by rfl) ⟨13299, by rfl⟩) R26599
theorem R35639 : Reach 35639 := rs (se 1 (by rfl) ⟨26729, by rfl⟩) R53459
theorem R35675 : Reach 35675 := rs (se 1 (by rfl) ⟨26756, by rfl⟩) R53513
theorem R35819 : Reach 35819 := rs (se 1 (by rfl) ⟨26864, by rfl⟩) R53729
theorem R36023 : Reach 36023 := rs (se 1 (by rfl) ⟨27017, by rfl⟩) R54035
theorem R462131 : Reach 462131 := rs (se 1 (by rfl) ⟨346598, by rfl⟩) R693197
theorem R167291 : Reach 167291 := rs (se 1 (by rfl) ⟨125468, by rfl⟩) R250937
theorem R36263 : Reach 36263 := rs (se 1 (by rfl) ⟨27197, by rfl⟩) R54395
theorem R36347 : Reach 36347 := rs (se 1 (by rfl) ⟨27260, by rfl⟩) R54521
theorem R36443 : Reach 36443 := rs (se 1 (by rfl) ⟨27332, by rfl⟩) R54665
theorem R69245 : Reach 69245 := rs (se 3 (by rfl) ⟨12983, by rfl⟩) R25967
theorem R36527 : Reach 36527 := rs (se 1 (by rfl) ⟨27395, by rfl⟩) R54791
theorem R36647 : Reach 36647 := rs (se 1 (by rfl) ⟨27485, by rfl⟩) R54971
theorem R36731 : Reach 36731 := rs (se 1 (by rfl) ⟨27548, by rfl⟩) R55097
theorem R102653 : Reach 102653 := rs (se 3 (by rfl) ⟨19247, by rfl⟩) R38495
theorem R37151 : Reach 37151 := rs (se 1 (by rfl) ⟨27863, by rfl⟩) R55727
theorem R37175 : Reach 37175 := rs (se 1 (by rfl) ⟨27881, by rfl⟩) R55763
theorem R37247 : Reach 37247 := rs (se 1 (by rfl) ⟨27935, by rfl⟩) R55871
theorem R37319 : Reach 37319 := rs (se 1 (by rfl) ⟨27989, by rfl⟩) R55979
theorem R201203 : Reach 201203 := rs (se 1 (by rfl) ⟨150902, by rfl⟩) R301805
theorem R70247 : Reach 70247 := rs (se 1 (by rfl) ⟨52685, by rfl⟩) R105371
theorem R266935 : Reach 266935 := rs (se 1 (by rfl) ⟨200201, by rfl⟩) R400403
theorem R37673 : Reach 37673 := rs (se 2 (by rfl) ⟨14127, by rfl⟩) R28255
theorem R37679 : Reach 37679 := rs (se 1 (by rfl) ⟨28259, by rfl⟩) R56519
theorem R37799 : Reach 37799 := rs (se 1 (by rfl) ⟨28349, by rfl⟩) R56699
theorem R136187 : Reach 136187 := rs (se 1 (by rfl) ⟨102140, by rfl⟩) R204281
theorem R37883 : Reach 37883 := rs (se 1 (by rfl) ⟨28412, by rfl⟩) R56825
theorem R37943 : Reach 37943 := rs (se 1 (by rfl) ⟨28457, by rfl⟩) R56915
theorem R37961 : Reach 37961 := rs (se 2 (by rfl) ⟨14235, by rfl⟩) R28471
theorem R38063 : Reach 38063 := rs (se 1 (by rfl) ⟨28547, by rfl⟩) R57095
theorem R136403 : Reach 136403 := rs (se 1 (by rfl) ⟨102302, by rfl⟩) R204605
theorem R38315 : Reach 38315 := rs (se 1 (by rfl) ⟨28736, by rfl⟩) R57473
theorem R202297 : Reach 202297 := rs (se 2 (by rfl) ⟨75861, by rfl⟩) R151723
theorem R38471 : Reach 38471 := rs (se 1 (by rfl) ⟨28853, by rfl⟩) R57707
theorem R38567 : Reach 38567 := rs (se 1 (by rfl) ⟨28925, by rfl⟩) R57851
theorem R71351 : Reach 71351 := rs (se 1 (by rfl) ⟨53513, by rfl⟩) R107027
theorem R38651 : Reach 38651 := rs (se 1 (by rfl) ⟨28988, by rfl⟩) R57977
theorem R38687 : Reach 38687 := rs (se 1 (by rfl) ⟨29015, by rfl⟩) R58031
theorem R38735 : Reach 38735 := rs (se 1 (by rfl) ⟨29051, by rfl⟩) R58103
theorem R38855 : Reach 38855 := rs (se 1 (by rfl) ⟨29141, by rfl⟩) R58283
theorem R268271 : Reach 268271 := rs (se 1 (by rfl) ⟨201203, by rfl⟩) R402407
theorem R38903 : Reach 38903 := rs (se 1 (by rfl) ⟨29177, by rfl⟩) R58355
theorem R71705 : Reach 71705 := rs (se 2 (by rfl) ⟨26889, by rfl⟩) R53779
theorem R39209 : Reach 39209 := rs (se 2 (by rfl) ⟨14703, by rfl⟩) R29407
theorem R39215 : Reach 39215 := rs (se 1 (by rfl) ⟨29411, by rfl⟩) R58823
theorem R39455 : Reach 39455 := rs (se 1 (by rfl) ⟨29591, by rfl⟩) R59183
theorem R105097 : Reach 105097 := rs (se 2 (by rfl) ⟨39411, by rfl⟩) R78823
theorem R39611 : Reach 39611 := rs (se 1 (by rfl) ⟨29708, by rfl⟩) R59417
theorem R105259 : Reach 105259 := rs (se 1 (by rfl) ⟨78944, by rfl⟩) R157889
theorem R39839 : Reach 39839 := rs (se 1 (by rfl) ⟨29879, by rfl⟩) R59759
theorem R39887 : Reach 39887 := rs (se 1 (by rfl) ⟨29915, by rfl⟩) R59831
theorem R39977 : Reach 39977 := rs (se 2 (by rfl) ⟨14991, by rfl⟩) R29983
theorem R39983 : Reach 39983 := rs (se 1 (by rfl) ⟨29987, by rfl⟩) R59975
theorem R40007 : Reach 40007 := rs (se 1 (by rfl) ⟨30005, by rfl⟩) R60011
theorem R40271 : Reach 40271 := rs (se 1 (by rfl) ⟨30203, by rfl⟩) R60407
theorem R40361 : Reach 40361 := rs (se 2 (by rfl) ⟨15135, by rfl⟩) R30271
theorem R40439 : Reach 40439 := rs (se 1 (by rfl) ⟨30329, by rfl⟩) R60659
theorem R40511 : Reach 40511 := rs (se 1 (by rfl) ⟨30383, by rfl⟩) R60767
theorem R40591 : Reach 40591 := rs (se 1 (by rfl) ⟨30443, by rfl⟩) R60887
theorem R41465 : Reach 41465 := rs (se 2 (by rfl) ⟨15549, by rfl⟩) R31099
theorem R41735 : Reach 41735 := rs (se 1 (by rfl) ⟨31301, by rfl⟩) R62603
theorem R238799 : Reach 238799 := rs (se 1 (by rfl) ⟨179099, by rfl⟩) R358199
theorem R304721 : Reach 304721 := rs (se 2 (by rfl) ⟨114270, by rfl⟩) R228541
theorem R304859 : Reach 304859 := rs (se 1 (by rfl) ⟨228644, by rfl⟩) R457289
theorem R42815 : Reach 42815 := rs (se 1 (by rfl) ⟨32111, by rfl⟩) R64223
theorem R42889 : Reach 42889 := rs (se 2 (by rfl) ⟨16083, by rfl⟩) R32167
theorem R75991 : Reach 75991 := rs (se 1 (by rfl) ⟨56993, by rfl⟩) R113987
theorem R76079 : Reach 76079 := rs (se 1 (by rfl) ⟨57059, by rfl⟩) R114119
theorem R43321 : Reach 43321 := rs (se 2 (by rfl) ⟨16245, by rfl⟩) R32491
theorem R76295 : Reach 76295 := rs (se 1 (by rfl) ⟨57221, by rfl⟩) R114443
theorem R141851 : Reach 141851 := rs (se 1 (by rfl) ⟨106388, by rfl⟩) R212777
theorem R535085 : Reach 535085 := rs (se 3 (by rfl) ⟨100328, by rfl⟩) R200657
theorem R43625 : Reach 43625 := rs (se 2 (by rfl) ⟨16359, by rfl⟩) R32719
theorem R142019 : Reach 142019 := rs (se 1 (by rfl) ⟨106514, by rfl⟩) R213029
theorem R142073 : Reach 142073 := rs (se 2 (by rfl) ⟨53277, by rfl⟩) R106555
theorem R208007 : Reach 208007 := rs (se 1 (by rfl) ⟨156005, by rfl⟩) R312011
theorem R44617 : Reach 44617 := rs (se 2 (by rfl) ⟨16731, by rfl⟩) R33463
theorem R44651 : Reach 44651 := rs (se 1 (by rfl) ⟨33488, by rfl⟩) R66977
theorem R44921 : Reach 44921 := rs (se 2 (by rfl) ⟨16845, by rfl⟩) R33691
theorem R77707 : Reach 77707 := rs (se 1 (by rfl) ⟨58280, by rfl⟩) R116561
theorem R602245 : Reach 602245 := rs (se 4 (by rfl) ⟨56460, by rfl⟩) R112921
theorem R242347 : Reach 242347 := rs (se 1 (by rfl) ⟨181760, by rfl⟩) R363521
theorem R406367 : Reach 406367 := rs (se 1 (by rfl) ⟨304775, by rfl⟩) R609551
theorem R78887 : Reach 78887 := rs (se 1 (by rfl) ⟨59165, by rfl⟩) R118331
theorem R242963 : Reach 242963 := rs (se 1 (by rfl) ⟨182222, by rfl⟩) R364445
theorem R669221 : Reach 669221 := rs (se 4 (by rfl) ⟨62739, by rfl⟩) R125479
theorem R145061 : Reach 145061 := rs (se 4 (by rfl) ⟨13599, by rfl⟩) R27199
theorem R79595 : Reach 79595 := rs (se 1 (by rfl) ⟨59696, by rfl⟩) R119393
theorem R79865 : Reach 79865 := rs (se 2 (by rfl) ⟨29949, by rfl⟩) R59899
theorem R80027 : Reach 80027 := rs (se 1 (by rfl) ⟨60020, by rfl⟩) R120041
theorem R80135 : Reach 80135 := rs (se 1 (by rfl) ⟨60101, by rfl⟩) R120203
theorem R113615 : Reach 113615 := rs (se 1 (by rfl) ⟨85211, by rfl⟩) R170423
theorem R146447 : Reach 146447 := rs (se 1 (by rfl) ⟨109835, by rfl⟩) R219671
theorem R81161 : Reach 81161 := rs (se 2 (by rfl) ⟨30435, by rfl⟩) R60871
theorem R278477 : Reach 278477 := rs (se 3 (by rfl) ⟨52214, by rfl⟩) R104429
theorem R344407 : Reach 344407 := rs (se 1 (by rfl) ⟨258305, by rfl⟩) R516611
theorem R82295 : Reach 82295 := rs (se 1 (by rfl) ⟨61721, by rfl⟩) R123443
theorem R147887 : Reach 147887 := rs (se 1 (by rfl) ⟨110915, by rfl⟩) R221831
theorem R115127 : Reach 115127 := rs (se 1 (by rfl) ⟨86345, by rfl⟩) R172691
theorem R147911 : Reach 147911 := rs (se 1 (by rfl) ⟨110933, by rfl⟩) R221867
theorem R606689 : Reach 606689 := rs (se 2 (by rfl) ⟨227508, by rfl⟩) R455017
theorem R49967 : Reach 49967 := rs (se 1 (by rfl) ⟨37475, by rfl⟩) R74951
theorem R148625 : Reach 148625 := rs (se 2 (by rfl) ⟨55734, by rfl⟩) R111469
theorem R83375 : Reach 83375 := rs (se 1 (by rfl) ⟨62531, by rfl⟩) R125063
theorem R83551 : Reach 83551 := rs (se 1 (by rfl) ⟨62663, by rfl⟩) R125327
theorem R83753 : Reach 83753 := rs (se 2 (by rfl) ⟨31407, by rfl⟩) R62815
theorem R149309 : Reach 149309 := rs (se 3 (by rfl) ⟨27995, by rfl⟩) R55991
theorem R51023 : Reach 51023 := rs (se 1 (by rfl) ⟨38267, by rfl⟩) R76535
theorem R411601 : Reach 411601 := rs (se 2 (by rfl) ⟨154350, by rfl⟩) R308701
theorem R84077 : Reach 84077 := rs (se 3 (by rfl) ⟨15764, by rfl⟩) R31529
theorem R84203 : Reach 84203 := rs (se 1 (by rfl) ⟨63152, by rfl⟩) R126305
theorem R248141 : Reach 248141 := rs (se 3 (by rfl) ⟨46526, by rfl⟩) R93053
theorem R51617 : Reach 51617 := rs (se 2 (by rfl) ⟨19356, by rfl⟩) R38713
theorem R150835 : Reach 150835 := rs (se 1 (by rfl) ⟨113126, by rfl⟩) R226253
theorem R85499 : Reach 85499 := rs (se 1 (by rfl) ⟨64124, by rfl⟩) R128249
theorem R53135 : Reach 53135 := rs (se 1 (by rfl) ⟨39851, by rfl⟩) R79703
theorem R642977 : Reach 642977 := rs (se 2 (by rfl) ⟨241116, by rfl⟩) R482233
theorem R85967 : Reach 85967 := rs (se 1 (by rfl) ⟨64475, by rfl⟩) R128951
theorem R184301 : Reach 184301 := rs (se 3 (by rfl) ⟨34556, by rfl⟩) R69113
theorem R151571 : Reach 151571 := rs (se 1 (by rfl) ⟨113678, by rfl⟩) R227357
theorem R1724723 : Reach 1724723 := rs (se 1 (by rfl) ⟨1293542, by rfl⟩) R2587085
theorem R86383 : Reach 86383 := rs (se 1 (by rfl) ⟨64787, by rfl⟩) R129575
theorem R86399 : Reach 86399 := rs (se 1 (by rfl) ⟨64799, by rfl⟩) R129599
theorem R53855 : Reach 53855 := rs (se 1 (by rfl) ⟨40391, by rfl⟩) R80783
theorem R316007 : Reach 316007 := rs (se 1 (by rfl) ⟨237005, by rfl⟩) R474011
theorem R152225 : Reach 152225 := rs (se 2 (by rfl) ⟨57084, by rfl⟩) R114169
theorem R86845 : Reach 86845 := rs (se 3 (by rfl) ⟨16283, by rfl⟩) R32567
theorem R54683 : Reach 54683 := rs (se 1 (by rfl) ⟨41012, by rfl⟩) R82025
theorem R120251 : Reach 120251 := rs (se 1 (by rfl) ⟨90188, by rfl⟩) R180377
theorem R87803 : Reach 87803 := rs (se 1 (by rfl) ⟨65852, by rfl⟩) R131705
theorem R87965 : Reach 87965 := rs (se 3 (by rfl) ⟨16493, by rfl⟩) R32987
theorem R120791 : Reach 120791 := rs (se 1 (by rfl) ⟨90593, by rfl⟩) R181187
theorem R55259 : Reach 55259 := rs (se 1 (by rfl) ⟨41444, by rfl⟩) R82889
theorem R55439 : Reach 55439 := rs (se 1 (by rfl) ⟨41579, by rfl⟩) R83159
theorem R55457 : Reach 55457 := rs (se 2 (by rfl) ⟨20796, by rfl⟩) R41593
theorem R55495 : Reach 55495 := rs (se 1 (by rfl) ⟨41621, by rfl⟩) R83243
theorem R55529 : Reach 55529 := rs (se 2 (by rfl) ⟨20823, by rfl⟩) R41647
theorem R186835 : Reach 186835 := rs (se 1 (by rfl) ⟨140126, by rfl⟩) R280253
theorem R88937 : Reach 88937 := rs (se 2 (by rfl) ⟨33351, by rfl⟩) R66703
theorem R154493 : Reach 154493 := rs (se 3 (by rfl) ⟨28967, by rfl⟩) R57935
theorem R88991 : Reach 88991 := rs (se 1 (by rfl) ⟨66743, by rfl⟩) R133487
theorem R1530899 : Reach 1530899 := rs (se 1 (by rfl) ⟨1148174, by rfl⟩) R2296349
theorem R23599 : Reach 23599 := rs (se 1 (by rfl) ⟨17699, by rfl⟩) R35399
theorem R23623 : Reach 23623 := rs (se 1 (by rfl) ⟨17717, by rfl⟩) R35435
theorem R23775 : Reach 23775 := rs (se 1 (by rfl) ⟨17831, by rfl⟩) R35663
theorem R24039 : Reach 24039 := rs (se 1 (by rfl) ⟨18029, by rfl⟩) R36059
theorem R56807 : Reach 56807 := rs (se 1 (by rfl) ⟨42605, by rfl⟩) R85211
theorem R24155 : Reach 24155 := rs (se 1 (by rfl) ⟨18116, by rfl⟩) R36233
theorem R24391 : Reach 24391 := rs (se 1 (by rfl) ⟨18293, by rfl⟩) R36587
theorem R24543 : Reach 24543 := rs (se 1 (by rfl) ⟨18407, by rfl⟩) R36815
theorem R57383 : Reach 57383 := rs (se 1 (by rfl) ⟨43037, by rfl⟩) R86075
theorem R57563 : Reach 57563 := rs (se 1 (by rfl) ⟨43172, by rfl⟩) R86345
theorem R24807 : Reach 24807 := rs (se 1 (by rfl) ⟨18605, by rfl⟩) R37211
theorem R90449 : Reach 90449 := rs (se 2 (by rfl) ⟨33918, by rfl⟩) R67837
theorem R24959 : Reach 24959 := rs (se 1 (by rfl) ⟨18719, by rfl⟩) R37439
theorem R25039 : Reach 25039 := rs (se 1 (by rfl) ⟨18779, by rfl⟩) R37559
theorem R57833 : Reach 57833 := rs (se 2 (by rfl) ⟨21687, by rfl⟩) R43375
theorem R25191 : Reach 25191 := rs (se 1 (by rfl) ⟨18893, by rfl⟩) R37787
theorem R58121 : Reach 58121 := rs (se 2 (by rfl) ⟨21795, by rfl⟩) R43591
theorem R58159 : Reach 58159 := rs (se 1 (by rfl) ⟨43619, by rfl⟩) R87239
theorem R25455 : Reach 25455 := rs (se 1 (by rfl) ⟨19091, by rfl⟩) R38183
theorem R25511 : Reach 25511 := rs (se 1 (by rfl) ⟨19133, by rfl⟩) R38267
theorem R25595 : Reach 25595 := rs (se 1 (by rfl) ⟨19196, by rfl⟩) R38393
theorem R123929 : Reach 123929 := rs (se 2 (by rfl) ⟨46473, by rfl⟩) R92947
theorem R25663 : Reach 25663 := rs (se 1 (by rfl) ⟨19247, by rfl⟩) R38495
theorem R91259 : Reach 91259 := rs (se 1 (by rfl) ⟨68444, by rfl⟩) R136889
theorem R25775 : Reach 25775 := rs (se 1 (by rfl) ⟨19331, by rfl⟩) R38663
theorem R25807 : Reach 25807 := rs (se 1 (by rfl) ⟨19355, by rfl⟩) R38711
theorem R58697 : Reach 58697 := rs (se 2 (by rfl) ⟨22011, by rfl⟩) R44023
theorem R26011 : Reach 26011 := rs (se 1 (by rfl) ⟨19508, by rfl⟩) R39017
theorem R26223 : Reach 26223 := rs (se 1 (by rfl) ⟨19667, by rfl⟩) R39335
theorem R26279 : Reach 26279 := rs (se 1 (by rfl) ⟨19709, by rfl⟩) R39419
theorem R26331 : Reach 26331 := rs (se 1 (by rfl) ⟨19748, by rfl⟩) R39497
theorem R26363 : Reach 26363 := rs (se 1 (by rfl) ⟨19772, by rfl⟩) R39545
theorem R26399 : Reach 26399 := rs (se 1 (by rfl) ⟨19799, by rfl⟩) R39599
theorem R26431 : Reach 26431 := rs (se 1 (by rfl) ⟨19823, by rfl⟩) R39647
theorem R26567 : Reach 26567 := rs (se 1 (by rfl) ⟨19925, by rfl⟩) R39851
theorem R26607 : Reach 26607 := rs (se 1 (by rfl) ⟨19955, by rfl⟩) R39911
theorem R26719 : Reach 26719 := rs (se 1 (by rfl) ⟨20039, by rfl⟩) R40079
theorem R26779 : Reach 26779 := rs (se 1 (by rfl) ⟨20084, by rfl⟩) R40169
theorem R26815 : Reach 26815 := rs (se 1 (by rfl) ⟨20111, by rfl⟩) R40223
theorem R59687 : Reach 59687 := rs (se 1 (by rfl) ⟨44765, by rfl⟩) R89531
theorem R26927 : Reach 26927 := rs (se 1 (by rfl) ⟨20195, by rfl⟩) R40391
theorem R59705 : Reach 59705 := rs (se 2 (by rfl) ⟨22389, by rfl⟩) R44779
theorem R27163 : Reach 27163 := rs (se 1 (by rfl) ⟨20372, by rfl⟩) R40745
theorem R1272833 : Reach 1272833 := rs (se 2 (by rfl) ⟨477312, by rfl⟩) R954625
theorem R27983 : Reach 27983 := rs (se 1 (by rfl) ⟨20987, by rfl⟩) R41975
theorem R585251 : Reach 585251 := rs (se 1 (by rfl) ⟨438938, by rfl⟩) R877877
theorem R126521 : Reach 126521 := rs (se 2 (by rfl) ⟨47445, by rfl⟩) R94891
theorem R61001 : Reach 61001 := rs (se 2 (by rfl) ⟨22875, by rfl⟩) R45751
theorem R28903 : Reach 28903 := rs (se 1 (by rfl) ⟨21677, by rfl⟩) R43355
theorem R127241 : Reach 127241 := rs (se 2 (by rfl) ⟨47715, by rfl⟩) R95431
theorem R61823 : Reach 61823 := rs (se 1 (by rfl) ⟨46367, by rfl⟩) R92735
theorem R192935 : Reach 192935 := rs (se 1 (by rfl) ⟨144701, by rfl⟩) R289403
theorem R29551 : Reach 29551 := rs (se 1 (by rfl) ⟨22163, by rfl⟩) R44327
theorem R29803 : Reach 29803 := rs (se 1 (by rfl) ⟨22352, by rfl⟩) R44705
theorem R96137 : Reach 96137 := rs (se 2 (by rfl) ⟨36051, by rfl⟩) R72103
theorem R63463 : Reach 63463 := rs (se 1 (by rfl) ⟨47597, by rfl⟩) R95195
theorem R325795 : Reach 325795 := rs (se 1 (by rfl) ⟨244346, by rfl⟩) R488693
theorem R64415 : Reach 64415 := rs (se 1 (by rfl) ⟨48311, by rfl⟩) R96623
theorem R97321 : Reach 97321 := rs (se 2 (by rfl) ⟨36495, by rfl⟩) R72991
theorem R851267 : Reach 851267 := rs (se 1 (by rfl) ⟨638450, by rfl⟩) R1276901
theorem R130409 : Reach 130409 := rs (se 2 (by rfl) ⟨48903, by rfl⟩) R97807
theorem R261569 : Reach 261569 := rs (se 2 (by rfl) ⟨98088, by rfl⟩) R196177
theorem R294515 : Reach 294515 := rs (se 1 (by rfl) ⟨220886, by rfl⟩) R441773
theorem R98219 : Reach 98219 := rs (se 1 (by rfl) ⟨73664, by rfl⟩) R147329
theorem R32735 : Reach 32735 := rs (se 1 (by rfl) ⟨24551, by rfl⟩) R49103
theorem R98591 : Reach 98591 := rs (se 1 (by rfl) ⟨73943, by rfl⟩) R147887
theorem R459209 : Reach 459209 := rs (se 2 (by rfl) ⟨172203, by rfl⟩) R344407
theorem R33311 : Reach 33311 := rs (se 1 (by rfl) ⟨24983, by rfl⟩) R49967
theorem R3211973 : Reach 3211973 := rs (se 4 (by rfl) ⟨301122, by rfl⟩) R602245
theorem R393943 : Reach 393943 := rs (se 1 (by rfl) ⟨295457, by rfl⟩) R590915
theorem R99083 : Reach 99083 := rs (se 1 (by rfl) ⟨74312, by rfl⟩) R148625
theorem R295973 : Reach 295973 := rs (se 4 (by rfl) ⟨27747, by rfl⟩) R55495
theorem R99539 : Reach 99539 := rs (se 1 (by rfl) ⟨74654, by rfl⟩) R149309
theorem R34015 : Reach 34015 := rs (se 1 (by rfl) ⟨25511, by rfl⟩) R51023
theorem R66863 : Reach 66863 := rs (se 1 (by rfl) ⟨50147, by rfl⟩) R100295
theorem R35423 : Reach 35423 := rs (se 1 (by rfl) ⟨26567, by rfl⟩) R53135
theorem R428651 : Reach 428651 := rs (se 1 (by rfl) ⟨321488, by rfl⟩) R642977
theorem R101047 : Reach 101047 := rs (se 1 (by rfl) ⟨75785, by rfl⟩) R151571
theorem R68435 : Reach 68435 := rs (se 1 (by rfl) ⟨51326, by rfl⟩) R102653
theorem R1149815 : Reach 1149815 := rs (se 1 (by rfl) ⟨862361, by rfl⟩) R1724723
theorem R35705 : Reach 35705 := rs (se 2 (by rfl) ⟨13389, by rfl⟩) R26779
theorem R35753 : Reach 35753 := rs (se 2 (by rfl) ⟨13407, by rfl⟩) R26815
theorem R101321 : Reach 101321 := rs (se 2 (by rfl) ⟨37995, by rfl⟩) R75991
theorem R134135 : Reach 134135 := rs (se 1 (by rfl) ⟨100601, by rfl⟩) R201203
theorem R35903 : Reach 35903 := rs (se 1 (by rfl) ⟨26927, by rfl⟩) R53855
theorem R101483 : Reach 101483 := rs (se 1 (by rfl) ⟨76112, by rfl⟩) R152225
theorem R36217 : Reach 36217 := rs (se 2 (by rfl) ⟨13581, by rfl⟩) R27163
theorem R36455 : Reach 36455 := rs (se 1 (by rfl) ⟨27341, by rfl⟩) R54683
theorem R36839 : Reach 36839 := rs (se 1 (by rfl) ⟨27629, by rfl⟩) R55259
theorem R36959 : Reach 36959 := rs (se 1 (by rfl) ⟨27719, by rfl⟩) R55439
theorem R36971 : Reach 36971 := rs (se 1 (by rfl) ⟨27728, by rfl⟩) R55457
theorem R37019 : Reach 37019 := rs (se 1 (by rfl) ⟨27764, by rfl⟩) R55529
theorem R201113 : Reach 201113 := rs (se 2 (by rfl) ⟨75417, by rfl⟩) R150835
theorem R102995 : Reach 102995 := rs (se 1 (by rfl) ⟨77246, by rfl⟩) R154493
theorem R1020599 : Reach 1020599 := rs (se 1 (by rfl) ⟨765449, by rfl⟩) R1530899
theorem R1577717 : Reach 1577717 := rs (se 5 (by rfl) ⟨73955, by rfl⟩) R147911
theorem R37871 : Reach 37871 := rs (se 1 (by rfl) ⟨28403, by rfl⟩) R56807
theorem R103609 : Reach 103609 := rs (se 2 (by rfl) ⟨38853, by rfl⟩) R77707
theorem R38255 : Reach 38255 := rs (se 1 (by rfl) ⟨28691, by rfl⟩) R57383
theorem R38375 : Reach 38375 := rs (se 1 (by rfl) ⟨28781, by rfl⟩) R57563
theorem R38537 : Reach 38537 := rs (se 2 (by rfl) ⟨14451, by rfl⟩) R28903
theorem R38555 : Reach 38555 := rs (se 1 (by rfl) ⟨28916, by rfl⟩) R57833
theorem R38747 : Reach 38747 := rs (se 1 (by rfl) ⟨29060, by rfl⟩) R58121
theorem R661709 : Reach 661709 := rs (se 3 (by rfl) ⟨124070, by rfl⟩) R248141
theorem R39131 : Reach 39131 := rs (se 1 (by rfl) ⟨29348, by rfl⟩) R58697
theorem R203147 : Reach 203147 := rs (se 1 (by rfl) ⟨152360, by rfl⟩) R304721
theorem R137645 : Reach 137645 := rs (se 3 (by rfl) ⟨25808, by rfl⟩) R51617
theorem R203239 : Reach 203239 := rs (se 1 (by rfl) ⟨152429, by rfl⟩) R304859
theorem R39401 : Reach 39401 := rs (se 2 (by rfl) ⟨14775, by rfl⟩) R29551
theorem R39737 : Reach 39737 := rs (se 2 (by rfl) ⟨14901, by rfl⟩) R29803
theorem R39791 : Reach 39791 := rs (se 1 (by rfl) ⟨29843, by rfl⟩) R59687
theorem R39803 : Reach 39803 := rs (se 1 (by rfl) ⟨29852, by rfl⟩) R59705
theorem R269729 : Reach 269729 := rs (se 2 (by rfl) ⟨101148, by rfl⟩) R202297
theorem R138671 : Reach 138671 := rs (se 1 (by rfl) ⟨104003, by rfl⟩) R208007
theorem R40667 : Reach 40667 := rs (se 1 (by rfl) ⟨30500, by rfl⟩) R61001
theorem R434393 : Reach 434393 := rs (se 2 (by rfl) ⟨162897, by rfl⟩) R325795
theorem R41215 : Reach 41215 := rs (se 1 (by rfl) ⟨30911, by rfl⟩) R61823
theorem R270911 : Reach 270911 := rs (se 1 (by rfl) ⟨203183, by rfl⟩) R406367
theorem R2270045 : Reach 2270045 := rs (se 3 (by rfl) ⟨425633, by rfl⟩) R851267
theorem R140129 : Reach 140129 := rs (se 2 (by rfl) ⟨52548, by rfl⟩) R105097
theorem R74621 : Reach 74621 := rs (se 3 (by rfl) ⟨13991, by rfl⟩) R27983
theorem R140345 : Reach 140345 := rs (se 2 (by rfl) ⟨52629, by rfl⟩) R105259
theorem R697517 : Reach 697517 := rs (se 3 (by rfl) ⟨130784, by rfl⟩) R261569
theorem R107837 : Reach 107837 := rs (se 3 (by rfl) ⟨20219, by rfl⟩) R40439
theorem R42943 : Reach 42943 := rs (se 1 (by rfl) ⟨32207, by rfl⟩) R64415
theorem R75743 : Reach 75743 := rs (se 1 (by rfl) ⟨56807, by rfl⟩) R113615
theorem R76751 : Reach 76751 := rs (se 1 (by rfl) ⟨57563, by rfl⟩) R115127
theorem R404459 : Reach 404459 := rs (se 1 (by rfl) ⟨303344, by rfl⟩) R606689
theorem R44201 : Reach 44201 := rs (se 2 (by rfl) ⟨16575, by rfl⟩) R33151
theorem R44455 : Reach 44455 := rs (se 1 (by rfl) ⟨33341, by rfl⟩) R66683
theorem R77545 : Reach 77545 := rs (se 2 (by rfl) ⟨29079, by rfl⟩) R58159
theorem R45049 : Reach 45049 := rs (se 2 (by rfl) ⟨16893, by rfl⟩) R33787
theorem R45289 : Reach 45289 := rs (se 2 (by rfl) ⟨16983, by rfl⟩) R33967
theorem R45319 : Reach 45319 := rs (se 1 (by rfl) ⟨33989, by rfl⟩) R67979
theorem R307547 : Reach 307547 := rs (se 1 (by rfl) ⟨230660, by rfl⟩) R461321
theorem R111401 : Reach 111401 := rs (se 2 (by rfl) ⟨41775, by rfl⟩) R83551
theorem R308087 : Reach 308087 := rs (se 1 (by rfl) ⟨231065, by rfl⟩) R462131
theorem R111527 : Reach 111527 := rs (se 1 (by rfl) ⟨83645, by rfl⟩) R167291
theorem R46163 : Reach 46163 := rs (se 1 (by rfl) ⟨34622, by rfl⟩) R69245
theorem R46345 : Reach 46345 := rs (se 2 (by rfl) ⟨17379, by rfl⟩) R34759
theorem R46831 : Reach 46831 := rs (se 1 (by rfl) ⟨35123, by rfl⟩) R70247
theorem R210671 : Reach 210671 := rs (se 1 (by rfl) ⟨158003, by rfl⟩) R316007
theorem R636797 : Reach 636797 := rs (se 3 (by rfl) ⟨119399, by rfl⟩) R238799
theorem R47567 : Reach 47567 := rs (se 1 (by rfl) ⟨35675, by rfl⟩) R71351
theorem R80527 : Reach 80527 := rs (se 1 (by rfl) ⟨60395, by rfl⟩) R120791
theorem R178847 : Reach 178847 := rs (se 1 (by rfl) ⟨134135, by rfl⟩) R268271
theorem R47803 : Reach 47803 := rs (se 1 (by rfl) ⟨35852, by rfl⟩) R71705
theorem R115177 : Reach 115177 := rs (se 2 (by rfl) ⟨43191, by rfl⟩) R86383
theorem R82619 : Reach 82619 := rs (se 1 (by rfl) ⟨61964, by rfl⟩) R123929
theorem R181277 : Reach 181277 := rs (se 3 (by rfl) ⟨33989, by rfl⟩) R67979
theorem R115793 : Reach 115793 := rs (se 2 (by rfl) ⟨43422, by rfl⟩) R86845
theorem R378269 : Reach 378269 := rs (se 3 (by rfl) ⟨70925, by rfl⟩) R141851
theorem R50719 : Reach 50719 := rs (se 1 (by rfl) ⟨38039, by rfl⟩) R76079
theorem R50863 : Reach 50863 := rs (se 1 (by rfl) ⟨38147, by rfl⟩) R76295
theorem R84347 : Reach 84347 := rs (se 1 (by rfl) ⟨63260, by rfl⟩) R126521
theorem R84617 : Reach 84617 := rs (se 2 (by rfl) ⟨31731, by rfl⟩) R63463
theorem R84827 : Reach 84827 := rs (se 1 (by rfl) ⟨63620, by rfl⟩) R127241
theorem R249113 : Reach 249113 := rs (se 2 (by rfl) ⟨93417, by rfl⟩) R186835
theorem R52591 : Reach 52591 := rs (se 1 (by rfl) ⟨39443, by rfl⟩) R78887
theorem R446147 : Reach 446147 := rs (se 1 (by rfl) ⟨334610, by rfl⟩) R669221
theorem R53063 : Reach 53063 := rs (se 1 (by rfl) ⟨39797, by rfl⟩) R79595
theorem R53243 : Reach 53243 := rs (se 1 (by rfl) ⟨39932, by rfl⟩) R79865
theorem R53351 : Reach 53351 := rs (se 1 (by rfl) ⟨40013, by rfl⟩) R80027
theorem R53423 : Reach 53423 := rs (se 1 (by rfl) ⟨40067, by rfl⟩) R80135
theorem R119069 : Reach 119069 := rs (se 3 (by rfl) ⟨22325, by rfl⟩) R44651
theorem R54107 : Reach 54107 := rs (se 1 (by rfl) ⟨40580, by rfl⟩) R81161
theorem R54121 : Reach 54121 := rs (se 2 (by rfl) ⟨20295, by rfl⟩) R40591
theorem R86939 : Reach 86939 := rs (se 1 (by rfl) ⟨65204, by rfl⟩) R130409
theorem R87293 : Reach 87293 := rs (se 3 (by rfl) ⟨16367, by rfl⟩) R32735
theorem R185651 : Reach 185651 := rs (se 1 (by rfl) ⟨139238, by rfl⟩) R278477
theorem R54863 : Reach 54863 := rs (se 1 (by rfl) ⟨41147, by rfl⟩) R82295
theorem R153683 : Reach 153683 := rs (se 1 (by rfl) ⟨115262, by rfl⟩) R230525
theorem R55583 : Reach 55583 := rs (se 1 (by rfl) ⟨41687, by rfl⟩) R83375
theorem R88553 : Reach 88553 := rs (se 2 (by rfl) ⟨33207, by rfl⟩) R66415
theorem R55835 : Reach 55835 := rs (se 1 (by rfl) ⟨41876, by rfl⟩) R83753
theorem R154183 : Reach 154183 := rs (se 1 (by rfl) ⟨115637, by rfl⟩) R231275
theorem R56051 : Reach 56051 := rs (se 1 (by rfl) ⟨42038, by rfl⟩) R84077
theorem R56135 : Reach 56135 := rs (se 1 (by rfl) ⟨42101, by rfl⟩) R84203
theorem R23643 : Reach 23643 := rs (se 1 (by rfl) ⟨17732, by rfl⟩) R35465
theorem R23759 : Reach 23759 := rs (se 1 (by rfl) ⟨17819, by rfl⟩) R35639
theorem R23783 : Reach 23783 := rs (se 1 (by rfl) ⟨17837, by rfl⟩) R35675
theorem R23879 : Reach 23879 := rs (se 1 (by rfl) ⟨17909, by rfl⟩) R35819
theorem R24015 : Reach 24015 := rs (se 1 (by rfl) ⟨18011, by rfl⟩) R36023
theorem R24175 : Reach 24175 := rs (se 1 (by rfl) ⟨18131, by rfl⟩) R36263
theorem R24231 : Reach 24231 := rs (se 1 (by rfl) ⟨18173, by rfl⟩) R36347
theorem R56999 : Reach 56999 := rs (se 1 (by rfl) ⟨42749, by rfl⟩) R85499
theorem R24295 : Reach 24295 := rs (se 1 (by rfl) ⟨18221, by rfl⟩) R36443
theorem R24351 : Reach 24351 := rs (se 1 (by rfl) ⟨18263, by rfl⟩) R36527
theorem R57185 : Reach 57185 := rs (se 2 (by rfl) ⟨21444, by rfl⟩) R42889
theorem R24431 : Reach 24431 := rs (se 1 (by rfl) ⟨18323, by rfl⟩) R36647
theorem R24487 : Reach 24487 := rs (se 1 (by rfl) ⟨18365, by rfl⟩) R36731
theorem R548801 : Reach 548801 := rs (se 2 (by rfl) ⟨205800, by rfl⟩) R411601
theorem R57311 : Reach 57311 := rs (se 1 (by rfl) ⟨42983, by rfl⟩) R85967
theorem R122867 : Reach 122867 := rs (se 1 (by rfl) ⟨92150, by rfl⟩) R184301
theorem R24767 : Reach 24767 := rs (se 1 (by rfl) ⟨18575, by rfl⟩) R37151
theorem R24783 : Reach 24783 := rs (se 1 (by rfl) ⟨18587, by rfl⟩) R37175
theorem R24831 : Reach 24831 := rs (se 1 (by rfl) ⟨18623, by rfl⟩) R37247
theorem R57599 : Reach 57599 := rs (se 1 (by rfl) ⟨43199, by rfl⟩) R86399
theorem R24879 : Reach 24879 := rs (se 1 (by rfl) ⟨18659, by rfl⟩) R37319
theorem R57761 : Reach 57761 := rs (se 2 (by rfl) ⟨21660, by rfl⟩) R43321
theorem R25115 : Reach 25115 := rs (se 1 (by rfl) ⟨18836, by rfl⟩) R37673
theorem R25119 : Reach 25119 := rs (se 1 (by rfl) ⟨18839, by rfl⟩) R37679
theorem R25199 : Reach 25199 := rs (se 1 (by rfl) ⟨18899, by rfl⟩) R37799
theorem R90791 : Reach 90791 := rs (se 1 (by rfl) ⟨68093, by rfl⟩) R136187
theorem R25255 : Reach 25255 := rs (se 1 (by rfl) ⟨18941, by rfl⟩) R37883
theorem R25295 : Reach 25295 := rs (se 1 (by rfl) ⟨18971, by rfl⟩) R37943
theorem R25307 : Reach 25307 := rs (se 1 (by rfl) ⟨18980, by rfl⟩) R37961
theorem R25375 : Reach 25375 := rs (se 1 (by rfl) ⟨19031, by rfl⟩) R38063
theorem R90935 : Reach 90935 := rs (se 1 (by rfl) ⟨68201, by rfl⟩) R136403
theorem R25543 : Reach 25543 := rs (se 1 (by rfl) ⟨19157, by rfl⟩) R38315
theorem R25647 : Reach 25647 := rs (se 1 (by rfl) ⟨19235, by rfl⟩) R38471
theorem R25711 : Reach 25711 := rs (se 1 (by rfl) ⟨19283, by rfl⟩) R38567
theorem R320669 : Reach 320669 := rs (se 3 (by rfl) ⟨60125, by rfl⟩) R120251
theorem R25767 : Reach 25767 := rs (se 1 (by rfl) ⟨19325, by rfl⟩) R38651
theorem R58535 : Reach 58535 := rs (se 1 (by rfl) ⟨43901, by rfl⟩) R87803
theorem R25791 : Reach 25791 := rs (se 1 (by rfl) ⟨19343, by rfl⟩) R38687
theorem R25823 : Reach 25823 := rs (se 1 (by rfl) ⟨19367, by rfl⟩) R38735
theorem R58643 : Reach 58643 := rs (se 1 (by rfl) ⟨43982, by rfl⟩) R87965
theorem R25903 : Reach 25903 := rs (se 1 (by rfl) ⟨19427, by rfl⟩) R38855
theorem R25935 : Reach 25935 := rs (se 1 (by rfl) ⟨19451, by rfl⟩) R38903
theorem R26139 : Reach 26139 := rs (se 1 (by rfl) ⟨19604, by rfl⟩) R39209
theorem R26143 : Reach 26143 := rs (se 1 (by rfl) ⟨19607, by rfl⟩) R39215
theorem R26303 : Reach 26303 := rs (se 1 (by rfl) ⟨19727, by rfl⟩) R39455
theorem R26407 : Reach 26407 := rs (se 1 (by rfl) ⟨19805, by rfl⟩) R39611
theorem R59291 : Reach 59291 := rs (se 1 (by rfl) ⟨44468, by rfl⟩) R88937
theorem R59327 : Reach 59327 := rs (se 1 (by rfl) ⟨44495, by rfl⟩) R88991
theorem R26559 : Reach 26559 := rs (se 1 (by rfl) ⟨19919, by rfl⟩) R39839
theorem R26591 : Reach 26591 := rs (se 1 (by rfl) ⟨19943, by rfl⟩) R39887
theorem R26651 : Reach 26651 := rs (se 1 (by rfl) ⟨19988, by rfl⟩) R39977
theorem R26655 : Reach 26655 := rs (se 1 (by rfl) ⟨19991, by rfl⟩) R39983
theorem R26671 : Reach 26671 := rs (se 1 (by rfl) ⟨20003, by rfl⟩) R40007
theorem R59489 : Reach 59489 := rs (se 2 (by rfl) ⟨22308, by rfl⟩) R44617
theorem R26847 : Reach 26847 := rs (se 1 (by rfl) ⟨20135, by rfl⟩) R40271
theorem R26907 : Reach 26907 := rs (se 1 (by rfl) ⟨20180, by rfl⟩) R40361
theorem R616733 : Reach 616733 := rs (se 3 (by rfl) ⟨115637, by rfl⟩) R231275
theorem R26959 : Reach 26959 := rs (se 1 (by rfl) ⟨20219, by rfl⟩) R40439
theorem R27007 : Reach 27007 := rs (se 1 (by rfl) ⟨20255, by rfl⟩) R40511
theorem R60299 : Reach 60299 := rs (se 1 (by rfl) ⟨45224, by rfl⟩) R90449
theorem R27643 : Reach 27643 := rs (se 1 (by rfl) ⟨20732, by rfl⟩) R41465
theorem R27823 : Reach 27823 := rs (se 1 (by rfl) ⟨20867, by rfl⟩) R41735
theorem R60839 : Reach 60839 := rs (se 1 (by rfl) ⟨45629, by rfl⟩) R91259
theorem R323129 : Reach 323129 := rs (se 2 (by rfl) ⟨121173, by rfl⟩) R242347
theorem R355913 : Reach 355913 := rs (se 2 (by rfl) ⟨133467, by rfl⟩) R266935
theorem R28543 : Reach 28543 := rs (se 1 (by rfl) ⟨21407, by rfl⟩) R42815
theorem R356723 : Reach 356723 := rs (se 1 (by rfl) ⟨267542, by rfl⟩) R535085
theorem R29083 : Reach 29083 := rs (se 1 (by rfl) ⟨21812, by rfl⟩) R43625
theorem R94679 : Reach 94679 := rs (se 1 (by rfl) ⟨71009, by rfl⟩) R142019
theorem R94715 : Reach 94715 := rs (se 1 (by rfl) ⟨71036, by rfl⟩) R142073
theorem R848555 : Reach 848555 := rs (se 1 (by rfl) ⟨636416, by rfl⟩) R1272833
theorem R390167 : Reach 390167 := rs (se 1 (by rfl) ⟨292625, by rfl⟩) R585251
theorem R29767 : Reach 29767 := rs (se 1 (by rfl) ⟨22325, by rfl⟩) R44651
theorem R29947 : Reach 29947 := rs (se 1 (by rfl) ⟨22460, by rfl⟩) R44921
theorem R128623 : Reach 128623 := rs (se 1 (by rfl) ⟨96467, by rfl⟩) R192935
theorem R161975 : Reach 161975 := rs (se 1 (by rfl) ⟨121481, by rfl⟩) R242963
theorem R96707 : Reach 96707 := rs (se 1 (by rfl) ⟨72530, by rfl⟩) R145061
theorem R64091 : Reach 64091 := rs (se 1 (by rfl) ⟨48068, by rfl⟩) R96137
theorem R129761 : Reach 129761 := rs (se 2 (by rfl) ⟨48660, by rfl⟩) R97321
theorem R130085 : Reach 130085 := rs (se 4 (by rfl) ⟨12195, by rfl⟩) R24391
theorem R97631 : Reach 97631 := rs (se 1 (by rfl) ⟨73223, by rfl⟩) R146447
theorem R196343 : Reach 196343 := rs (se 1 (by rfl) ⟨147257, by rfl⟩) R294515
theorem R261917 : Reach 261917 := rs (se 3 (by rfl) ⟨49109, by rfl⟩) R98219
theorem R66055 : Reach 66055 := rs (se 1 (by rfl) ⟨49541, by rfl⟩) R99083
theorem R197315 : Reach 197315 := rs (se 1 (by rfl) ⟨147986, by rfl⟩) R295973
theorem R262909 : Reach 262909 := rs (se 3 (by rfl) ⟨49295, by rfl⟩) R98591
theorem R66359 : Reach 66359 := rs (se 1 (by rfl) ⟨49769, by rfl⟩) R99539
theorem R525257 : Reach 525257 := rs (se 2 (by rfl) ⟨196971, by rfl⟩) R393943
theorem R722429 : Reach 722429 := rs (se 3 (by rfl) ⟨135455, by rfl⟩) R270911
theorem R67547 : Reach 67547 := rs (se 1 (by rfl) ⟨50660, by rfl⟩) R101321
theorem R67625 : Reach 67625 := rs (se 2 (by rfl) ⟨25359, by rfl⟩) R50719
theorem R67655 : Reach 67655 := rs (se 1 (by rfl) ⟨50741, by rfl⟩) R101483
theorem R67817 : Reach 67817 := rs (se 2 (by rfl) ⟨25431, by rfl⟩) R50863
theorem R297431 : Reach 297431 := rs (se 1 (by rfl) ⟨223073, by rfl⟩) R446147
theorem R1083941 : Reach 1083941 := rs (se 4 (by rfl) ⟨101619, by rfl⟩) R203239
theorem R35375 : Reach 35375 := rs (se 1 (by rfl) ⟨26531, by rfl⟩) R53063
theorem R35495 : Reach 35495 := rs (se 1 (by rfl) ⟨26621, by rfl⟩) R53243
theorem R35561 : Reach 35561 := rs (se 2 (by rfl) ⟨13335, by rfl⟩) R26671
theorem R35567 : Reach 35567 := rs (se 1 (by rfl) ⟨26675, by rfl⟩) R53351
theorem R35615 : Reach 35615 := rs (se 1 (by rfl) ⟨26711, by rfl⟩) R53423
theorem R134075 : Reach 134075 := rs (se 1 (by rfl) ⟨100556, by rfl⟩) R201113
theorem R68663 : Reach 68663 := rs (se 1 (by rfl) ⟨51497, by rfl⟩) R102995
theorem R35945 : Reach 35945 := rs (se 2 (by rfl) ⟨13479, by rfl⟩) R26959
theorem R1051811 : Reach 1051811 := rs (se 1 (by rfl) ⟨788858, by rfl⟩) R1577717
theorem R36071 : Reach 36071 := rs (se 1 (by rfl) ⟨27053, by rfl⟩) R54107
theorem R134729 : Reach 134729 := rs (se 2 (by rfl) ⟨50523, by rfl⟩) R101047
theorem R36575 : Reach 36575 := rs (se 1 (by rfl) ⟨27431, by rfl⟩) R54863
theorem R36857 : Reach 36857 := rs (se 2 (by rfl) ⟨13821, by rfl⟩) R27643
theorem R102455 : Reach 102455 := rs (se 1 (by rfl) ⟨76841, by rfl⟩) R153683
theorem R37055 : Reach 37055 := rs (se 1 (by rfl) ⟨27791, by rfl⟩) R55583
theorem R37097 : Reach 37097 := rs (se 2 (by rfl) ⟨13911, by rfl⟩) R27823
theorem R135431 : Reach 135431 := rs (se 1 (by rfl) ⟨101573, by rfl⟩) R203147
theorem R37223 : Reach 37223 := rs (se 1 (by rfl) ⟨27917, by rfl⟩) R55835
theorem R70121 : Reach 70121 := rs (se 2 (by rfl) ⟨26295, by rfl⟩) R52591
theorem R37367 : Reach 37367 := rs (se 1 (by rfl) ⟨28025, by rfl⟩) R56051
theorem R37423 : Reach 37423 := rs (se 1 (by rfl) ⟨28067, by rfl⟩) R56135
theorem R103393 : Reach 103393 := rs (se 2 (by rfl) ⟨38772, by rfl⟩) R77545
theorem R37999 : Reach 37999 := rs (se 1 (by rfl) ⟨28499, by rfl⟩) R56999
theorem R38057 : Reach 38057 := rs (se 2 (by rfl) ⟨14271, by rfl⟩) R28543
theorem R38123 : Reach 38123 := rs (se 1 (by rfl) ⟨28592, by rfl⟩) R57185
theorem R365867 : Reach 365867 := rs (se 1 (by rfl) ⟨274400, by rfl⟩) R548801
theorem R38207 : Reach 38207 := rs (se 1 (by rfl) ⟨28655, by rfl⟩) R57311
theorem R38399 : Reach 38399 := rs (se 1 (by rfl) ⟨28799, by rfl⟩) R57599
theorem R38507 : Reach 38507 := rs (se 1 (by rfl) ⟨28880, by rfl⟩) R57761
theorem R38777 : Reach 38777 := rs (se 2 (by rfl) ⟨14541, by rfl⟩) R29083
theorem R1513363 : Reach 1513363 := rs (se 1 (by rfl) ⟨1135022, by rfl⟩) R2270045
theorem R39023 : Reach 39023 := rs (se 1 (by rfl) ⟨29267, by rfl⟩) R58535
theorem R465011 : Reach 465011 := rs (se 1 (by rfl) ⟨348758, by rfl⟩) R697517
theorem R39095 : Reach 39095 := rs (se 1 (by rfl) ⟨29321, by rfl⟩) R58643
theorem R71891 : Reach 71891 := rs (se 1 (by rfl) ⟨53918, by rfl⟩) R107837
theorem R72161 : Reach 72161 := rs (se 2 (by rfl) ⟨27060, by rfl⟩) R54121
theorem R39527 : Reach 39527 := rs (se 1 (by rfl) ⟨29645, by rfl⟩) R59291
theorem R236141 : Reach 236141 := rs (se 3 (by rfl) ⟨44276, by rfl⟩) R88553
theorem R39551 : Reach 39551 := rs (se 1 (by rfl) ⟨29663, by rfl⟩) R59327
theorem R39659 : Reach 39659 := rs (se 1 (by rfl) ⟨29744, by rfl⟩) R59489
theorem R39689 : Reach 39689 := rs (se 2 (by rfl) ⟨14883, by rfl⟩) R29767
theorem R138145 : Reach 138145 := rs (se 2 (by rfl) ⟨51804, by rfl⟩) R103609
theorem R39929 : Reach 39929 := rs (se 2 (by rfl) ⟨14973, by rfl⟩) R29947
theorem R40199 : Reach 40199 := rs (se 1 (by rfl) ⟨30149, by rfl⟩) R60299
theorem R269639 : Reach 269639 := rs (se 1 (by rfl) ⟨202229, by rfl⟩) R404459
theorem R171497 : Reach 171497 := rs (se 2 (by rfl) ⟨64311, by rfl⟩) R128623
theorem R40559 : Reach 40559 := rs (se 1 (by rfl) ⟨30419, by rfl⟩) R60839
theorem R237275 : Reach 237275 := rs (se 1 (by rfl) ⟨177956, by rfl⟩) R355913
theorem R205031 : Reach 205031 := rs (se 1 (by rfl) ⟨153773, by rfl⟩) R307547
theorem R237815 : Reach 237815 := rs (se 1 (by rfl) ⟨178361, by rfl⟩) R356723
theorem R565703 : Reach 565703 := rs (se 1 (by rfl) ⟨424277, by rfl⟩) R848555
theorem R74267 : Reach 74267 := rs (se 1 (by rfl) ⟨55700, by rfl⟩) R111401
theorem R205391 : Reach 205391 := rs (se 1 (by rfl) ⟨154043, by rfl⟩) R308087
theorem R74351 : Reach 74351 := rs (se 1 (by rfl) ⟨55763, by rfl⟩) R111527
theorem R664301 : Reach 664301 := rs (se 3 (by rfl) ⟨124556, by rfl⟩) R249113
theorem R205577 : Reach 205577 := rs (se 2 (by rfl) ⟨77091, by rfl⟩) R154183
theorem R107369 : Reach 107369 := rs (se 2 (by rfl) ⟨40263, by rfl⟩) R80527
theorem R140447 : Reach 140447 := rs (se 1 (by rfl) ⟨105335, by rfl⟩) R210671
theorem R107983 : Reach 107983 := rs (se 1 (by rfl) ⟨80987, by rfl⟩) R161975
theorem R42727 : Reach 42727 := rs (se 1 (by rfl) ⟨32045, by rfl⟩) R64091
theorem R174611 : Reach 174611 := rs (se 1 (by rfl) ⟨130958, by rfl⟩) R261917
theorem R306139 : Reach 306139 := rs (se 1 (by rfl) ⟨229604, by rfl⟩) R459209
theorem R2141315 : Reach 2141315 := rs (se 1 (by rfl) ⟨1605986, by rfl⟩) R3211973
theorem R77195 : Reach 77195 := rs (se 1 (by rfl) ⟨57896, by rfl⟩) R115793
theorem R45353 : Reach 45353 := rs (se 2 (by rfl) ⟨17007, by rfl⟩) R34015
theorem R45623 : Reach 45623 := rs (se 1 (by rfl) ⟨34217, by rfl⟩) R68435
theorem R79379 : Reach 79379 := rs (se 1 (by rfl) ⟨59534, by rfl⟩) R119069
theorem R178301 : Reach 178301 := rs (se 3 (by rfl) ⟨33431, by rfl⟩) R66863
theorem R441139 : Reach 441139 := rs (se 1 (by rfl) ⟨330854, by rfl⟩) R661709
theorem R48289 : Reach 48289 := rs (se 2 (by rfl) ⟨18108, by rfl⟩) R36217
theorem R179819 : Reach 179819 := rs (se 1 (by rfl) ⟨134864, by rfl⟩) R269729
theorem R81911 : Reach 81911 := rs (se 1 (by rfl) ⟨61433, by rfl⟩) R122867
theorem R49747 : Reach 49747 := rs (se 1 (by rfl) ⟨37310, by rfl⟩) R74621
theorem R213779 : Reach 213779 := rs (se 1 (by rfl) ⟨160334, by rfl⟩) R320669
theorem R50495 : Reach 50495 := rs (se 1 (by rfl) ⟨37871, by rfl⟩) R75743
theorem R411155 : Reach 411155 := rs (se 1 (by rfl) ⟨308366, by rfl⟩) R616733
theorem R51167 : Reach 51167 := rs (se 1 (by rfl) ⟨38375, by rfl⟩) R76751
theorem R3066173 : Reach 3066173 := rs (se 3 (by rfl) ⟨574907, by rfl⟩) R1149815
theorem R215419 : Reach 215419 := rs (se 1 (by rfl) ⟨161564, by rfl⟩) R323129
theorem R119231 : Reach 119231 := rs (se 1 (by rfl) ⟨89423, by rfl⟩) R178847
theorem R86507 : Reach 86507 := rs (se 1 (by rfl) ⟨64880, by rfl⟩) R129761
theorem R86723 : Reach 86723 := rs (se 1 (by rfl) ⟨65042, by rfl⟩) R130085
theorem R54953 : Reach 54953 := rs (se 2 (by rfl) ⟨20607, by rfl⟩) R41215
theorem R55079 : Reach 55079 := rs (se 1 (by rfl) ⟨41309, by rfl⟩) R82619
theorem R153569 : Reach 153569 := rs (se 2 (by rfl) ⟨57588, by rfl⟩) R115177
theorem R120851 : Reach 120851 := rs (se 1 (by rfl) ⟨90638, by rfl⟩) R181277
theorem R252179 : Reach 252179 := rs (se 1 (by rfl) ⟨189134, by rfl⟩) R378269
theorem R88829 : Reach 88829 := rs (se 3 (by rfl) ⟨16655, by rfl⟩) R33311
theorem R56231 : Reach 56231 := rs (se 1 (by rfl) ⟨42173, by rfl⟩) R84347
theorem R23615 : Reach 23615 := rs (se 1 (by rfl) ⟨17711, by rfl⟩) R35423
theorem R285767 : Reach 285767 := rs (se 1 (by rfl) ⟨214325, by rfl⟩) R428651
theorem R56411 : Reach 56411 := rs (se 1 (by rfl) ⟨42308, by rfl⟩) R84617
theorem R56551 : Reach 56551 := rs (se 1 (by rfl) ⟨42413, by rfl⟩) R84827
theorem R23803 : Reach 23803 := rs (se 1 (by rfl) ⟨17852, by rfl⟩) R35705
theorem R23835 : Reach 23835 := rs (se 1 (by rfl) ⟨17876, by rfl⟩) R35753
theorem R89423 : Reach 89423 := rs (se 1 (by rfl) ⟨67067, by rfl⟩) R134135
theorem R23935 : Reach 23935 := rs (se 1 (by rfl) ⟨17951, by rfl⟩) R35903
theorem R24303 : Reach 24303 := rs (se 1 (by rfl) ⟨18227, by rfl⟩) R36455
theorem R57257 : Reach 57257 := rs (se 2 (by rfl) ⟨21471, by rfl⟩) R42943
theorem R24559 : Reach 24559 := rs (se 1 (by rfl) ⟨18419, by rfl⟩) R36839
theorem R24639 : Reach 24639 := rs (se 1 (by rfl) ⟨18479, by rfl⟩) R36959
theorem R24647 : Reach 24647 := rs (se 1 (by rfl) ⟨18485, by rfl⟩) R36971
theorem R24679 : Reach 24679 := rs (se 1 (by rfl) ⟨18509, by rfl⟩) R37019
theorem R680399 : Reach 680399 := rs (se 1 (by rfl) ⟨510299, by rfl⟩) R1020599
theorem R57959 : Reach 57959 := rs (se 1 (by rfl) ⟨43469, by rfl⟩) R86939
theorem R25247 : Reach 25247 := rs (se 1 (by rfl) ⟨18935, by rfl⟩) R37871
theorem R58195 : Reach 58195 := rs (se 1 (by rfl) ⟨43646, by rfl⟩) R87293
theorem R123767 : Reach 123767 := rs (se 1 (by rfl) ⟨92825, by rfl⟩) R185651
theorem R25503 : Reach 25503 := rs (se 1 (by rfl) ⟨19127, by rfl⟩) R38255
theorem R25583 : Reach 25583 := rs (se 1 (by rfl) ⟨19187, by rfl⟩) R38375
theorem R25691 : Reach 25691 := rs (se 1 (by rfl) ⟨19268, by rfl⟩) R38537
theorem R25703 : Reach 25703 := rs (se 1 (by rfl) ⟨19277, by rfl⟩) R38555
theorem R25831 : Reach 25831 := rs (se 1 (by rfl) ⟨19373, by rfl⟩) R38747
theorem R26087 : Reach 26087 := rs (se 1 (by rfl) ⟨19565, by rfl⟩) R39131
theorem R91763 : Reach 91763 := rs (se 1 (by rfl) ⟨68822, by rfl⟩) R137645
theorem R26267 : Reach 26267 := rs (se 1 (by rfl) ⟨19700, by rfl⟩) R39401
theorem R26491 : Reach 26491 := rs (se 1 (by rfl) ⟨19868, by rfl⟩) R39737
theorem R59273 : Reach 59273 := rs (se 2 (by rfl) ⟨22227, by rfl⟩) R44455
theorem R26527 : Reach 26527 := rs (se 1 (by rfl) ⟨19895, by rfl⟩) R39791
theorem R26535 : Reach 26535 := rs (se 1 (by rfl) ⟨19901, by rfl⟩) R39803
theorem R92447 : Reach 92447 := rs (se 1 (by rfl) ⟨69335, by rfl⟩) R138671
theorem R27111 : Reach 27111 := rs (se 1 (by rfl) ⟨20333, by rfl⟩) R40667
theorem R60065 : Reach 60065 := rs (se 2 (by rfl) ⟨22524, by rfl⟩) R45049
theorem R289595 : Reach 289595 := rs (se 1 (by rfl) ⟨217196, by rfl⟩) R434393
theorem R60385 : Reach 60385 := rs (se 2 (by rfl) ⟨22644, by rfl⟩) R45289
theorem R60425 : Reach 60425 := rs (se 2 (by rfl) ⟨22659, by rfl⟩) R45319
theorem R60527 : Reach 60527 := rs (se 1 (by rfl) ⟨45395, by rfl⟩) R90791
theorem R60623 : Reach 60623 := rs (se 1 (by rfl) ⟨45467, by rfl⟩) R90935
theorem R93419 : Reach 93419 := rs (se 1 (by rfl) ⟨70064, by rfl⟩) R140129
theorem R93563 : Reach 93563 := rs (se 1 (by rfl) ⟨70172, by rfl⟩) R140345
theorem R126845 : Reach 126845 := rs (se 3 (by rfl) ⟨23783, by rfl⟩) R47567
theorem R61793 : Reach 61793 := rs (se 2 (by rfl) ⟨23172, by rfl⟩) R46345
theorem R29467 : Reach 29467 := rs (se 1 (by rfl) ⟨22100, by rfl⟩) R44201
theorem R62441 : Reach 62441 := rs (se 2 (by rfl) ⟨23415, by rfl⟩) R46831
theorem R63119 : Reach 63119 := rs (se 1 (by rfl) ⟨47339, by rfl⟩) R94679
theorem R63143 : Reach 63143 := rs (se 1 (by rfl) ⟨47357, by rfl⟩) R94715
theorem R260111 : Reach 260111 := rs (se 1 (by rfl) ⟨195083, by rfl⟩) R390167
theorem R30775 : Reach 30775 := rs (se 1 (by rfl) ⟨23081, by rfl⟩) R46163
theorem R63737 : Reach 63737 := rs (se 2 (by rfl) ⟨23901, by rfl⟩) R47803
theorem R424531 : Reach 424531 := rs (se 1 (by rfl) ⟨318398, by rfl⟩) R636797
theorem R64471 : Reach 64471 := rs (se 1 (by rfl) ⟨48353, by rfl⟩) R96707
theorem R32233 : Reach 32233 := rs (se 2 (by rfl) ⟨12087, by rfl⟩) R24175
theorem R65087 : Reach 65087 := rs (se 1 (by rfl) ⟨48815, by rfl⟩) R97631
theorem R130895 : Reach 130895 := rs (se 1 (by rfl) ⟨98171, by rfl⟩) R196343
theorem R131543 : Reach 131543 := rs (se 1 (by rfl) ⟨98657, by rfl⟩) R197315
theorem R66329 : Reach 66329 := rs (se 2 (by rfl) ⟨24873, by rfl⟩) R49747
theorem R34111 : Reach 34111 := rs (se 1 (by rfl) ⟨25583, by rfl⟩) R51167
theorem R198287 : Reach 198287 := rs (se 1 (by rfl) ⟨148715, by rfl⟩) R297431
theorem R722627 : Reach 722627 := rs (se 1 (by rfl) ⟨541970, by rfl⟩) R1083941
theorem R1771469 : Reach 1771469 := rs (se 3 (by rfl) ⟨332150, by rfl⟩) R664301
theorem R35321 : Reach 35321 := rs (se 2 (by rfl) ⟨13245, by rfl⟩) R26491
theorem R35369 : Reach 35369 := rs (se 2 (by rfl) ⟨13263, by rfl⟩) R26527
theorem R68303 : Reach 68303 := rs (se 1 (by rfl) ⟨51227, by rfl⟩) R102455
theorem R36635 : Reach 36635 := rs (se 1 (by rfl) ⟨27476, by rfl⟩) R54953
theorem R36719 : Reach 36719 := rs (se 1 (by rfl) ⟨27539, by rfl⟩) R55079
theorem R102379 : Reach 102379 := rs (se 1 (by rfl) ⟨76784, by rfl⟩) R153569
theorem R168119 : Reach 168119 := rs (se 1 (by rfl) ⟨126089, by rfl⟩) R252179
theorem R37487 : Reach 37487 := rs (se 1 (by rfl) ⟨28115, by rfl⟩) R56231
theorem R37607 : Reach 37607 := rs (se 1 (by rfl) ⟨28205, by rfl⟩) R56411
theorem R38171 : Reach 38171 := rs (se 1 (by rfl) ⟨28628, by rfl⟩) R57257
theorem R693629 : Reach 693629 := rs (se 3 (by rfl) ⟨130055, by rfl⟩) R260111
theorem R136687 : Reach 136687 := rs (se 1 (by rfl) ⟨102515, by rfl⟩) R205031
theorem R136927 : Reach 136927 := rs (se 1 (by rfl) ⟨102695, by rfl⟩) R205391
theorem R38639 : Reach 38639 := rs (se 1 (by rfl) ⟨28979, by rfl⟩) R57959
theorem R137051 : Reach 137051 := rs (se 1 (by rfl) ⟨102788, by rfl⟩) R205577
theorem R71579 : Reach 71579 := rs (se 1 (by rfl) ⟨53684, by rfl⟩) R107369
theorem R202661 : Reach 202661 := rs (se 4 (by rfl) ⟨18999, by rfl⟩) R37999
theorem R39515 : Reach 39515 := rs (se 1 (by rfl) ⟨29636, by rfl⟩) R59273
theorem R137857 : Reach 137857 := rs (se 2 (by rfl) ⟨51696, by rfl⟩) R103393
theorem R40043 : Reach 40043 := rs (se 1 (by rfl) ⟨30032, by rfl⟩) R60065
theorem R40283 : Reach 40283 := rs (se 1 (by rfl) ⟨30212, by rfl⟩) R60425
theorem R40351 : Reach 40351 := rs (se 1 (by rfl) ⟨30263, by rfl⟩) R60527
theorem R40415 : Reach 40415 := rs (se 1 (by rfl) ⟨30311, by rfl⟩) R60623
theorem R41033 : Reach 41033 := rs (se 2 (by rfl) ⟨15387, by rfl⟩) R30775
theorem R41195 : Reach 41195 := rs (se 1 (by rfl) ⟨30896, by rfl⟩) R61793
theorem R41627 : Reach 41627 := rs (se 1 (by rfl) ⟨31220, by rfl⟩) R62441
theorem R566041 : Reach 566041 := rs (se 2 (by rfl) ⟨212265, by rfl⟩) R424531
theorem R42079 : Reach 42079 := rs (se 1 (by rfl) ⟨31559, by rfl⟩) R63119
theorem R42095 : Reach 42095 := rs (se 1 (by rfl) ⟨31571, by rfl⟩) R63143
theorem R42491 : Reach 42491 := rs (se 1 (by rfl) ⟨31868, by rfl⟩) R63737
theorem R75401 : Reach 75401 := rs (se 2 (by rfl) ⟨28275, by rfl⟩) R56551
theorem R42977 : Reach 42977 := rs (se 2 (by rfl) ⟨16116, by rfl⟩) R32233
theorem R43391 : Reach 43391 := rs (se 1 (by rfl) ⟨32543, by rfl⟩) R65087
theorem R142519 : Reach 142519 := rs (se 1 (by rfl) ⟨106889, by rfl⟩) R213779
theorem R44239 : Reach 44239 := rs (se 1 (by rfl) ⟨33179, by rfl⟩) R66359
theorem R274103 : Reach 274103 := rs (se 1 (by rfl) ⟨205577, by rfl⟩) R411155
theorem R77593 : Reach 77593 := rs (se 2 (by rfl) ⟨29097, by rfl⟩) R58195
theorem R45031 : Reach 45031 := rs (se 1 (by rfl) ⟨33773, by rfl⟩) R67547
theorem R45083 : Reach 45083 := rs (se 1 (by rfl) ⟨33812, by rfl⟩) R67625
theorem R45103 : Reach 45103 := rs (se 1 (by rfl) ⟨33827, by rfl⟩) R67655
theorem R45211 : Reach 45211 := rs (se 1 (by rfl) ⟨33908, by rfl⟩) R67817
theorem R2044115 : Reach 2044115 := rs (se 1 (by rfl) ⟨1533086, by rfl⟩) R3066173
theorem R143977 : Reach 143977 := rs (se 2 (by rfl) ⟨53991, by rfl⟩) R107983
theorem R45775 : Reach 45775 := rs (se 1 (by rfl) ⟨34331, by rfl⟩) R68663
theorem R701207 : Reach 701207 := rs (se 1 (by rfl) ⟨525905, by rfl⟩) R1051811
theorem R79487 : Reach 79487 := rs (se 1 (by rfl) ⟨59615, by rfl⟩) R119231
theorem R46747 : Reach 46747 := rs (se 1 (by rfl) ⟨35060, by rfl⟩) R70121
theorem R538613 : Reach 538613 := rs (se 5 (by rfl) ⟨25247, by rfl⟩) R50495
theorem R243911 : Reach 243911 := rs (se 1 (by rfl) ⟨182933, by rfl⟩) R365867
theorem R408185 : Reach 408185 := rs (se 2 (by rfl) ⟨153069, by rfl⟩) R306139
theorem R80513 : Reach 80513 := rs (se 2 (by rfl) ⟨30192, by rfl⟩) R60385
theorem R80567 : Reach 80567 := rs (se 1 (by rfl) ⟨60425, by rfl⟩) R120851
theorem R310007 : Reach 310007 := rs (se 1 (by rfl) ⟨232505, by rfl⟩) R465011
theorem R47927 : Reach 47927 := rs (se 1 (by rfl) ⟨35945, by rfl⟩) R71891
theorem R48107 : Reach 48107 := rs (se 1 (by rfl) ⟨36080, by rfl⟩) R72161
theorem R179759 : Reach 179759 := rs (se 1 (by rfl) ⟨134819, by rfl⟩) R269639
theorem R377135 : Reach 377135 := rs (se 1 (by rfl) ⟨282851, by rfl⟩) R565703
theorem R475469 : Reach 475469 := rs (se 3 (by rfl) ⟨89150, by rfl⟩) R178301
theorem R49511 : Reach 49511 := rs (se 1 (by rfl) ⟨37133, by rfl⟩) R74267
theorem R49567 : Reach 49567 := rs (se 1 (by rfl) ⟨37175, by rfl⟩) R74351
theorem R82511 : Reach 82511 := rs (se 1 (by rfl) ⟨61883, by rfl⟩) R123767
theorem R49897 : Reach 49897 := rs (se 2 (by rfl) ⟨18711, by rfl⟩) R37423
theorem R116407 : Reach 116407 := rs (se 1 (by rfl) ⟨87305, by rfl⟩) R174611
theorem R1427543 : Reach 1427543 := rs (se 1 (by rfl) ⟨1070657, by rfl⟩) R2141315
theorem R772253 : Reach 772253 := rs (se 3 (by rfl) ⟨144797, by rfl⟩) R289595
theorem R51463 : Reach 51463 := rs (se 1 (by rfl) ⟨38597, by rfl⟩) R77195
theorem R2017817 : Reach 2017817 := rs (se 2 (by rfl) ⟨756681, by rfl⟩) R1513363
theorem R84563 : Reach 84563 := rs (se 1 (by rfl) ⟨63422, by rfl⟩) R126845
theorem R52919 : Reach 52919 := rs (se 1 (by rfl) ⟨39689, by rfl⟩) R79379
theorem R184193 : Reach 184193 := rs (se 2 (by rfl) ⟨69072, by rfl⟩) R138145
theorem R85961 : Reach 85961 := rs (se 2 (by rfl) ⟨32235, by rfl⟩) R64471
theorem R119879 : Reach 119879 := rs (se 1 (by rfl) ⟨89909, by rfl⟩) R179819
theorem R87263 : Reach 87263 := rs (se 1 (by rfl) ⟨65447, by rfl⟩) R130895
theorem R54607 : Reach 54607 := rs (se 1 (by rfl) ⟨40955, by rfl⟩) R81911
theorem R350171 : Reach 350171 := rs (se 1 (by rfl) ⟨262628, by rfl⟩) R525257
theorem R88073 : Reach 88073 := rs (se 2 (by rfl) ⟨33027, by rfl⟩) R66055
theorem R481619 : Reach 481619 := rs (se 1 (by rfl) ⟨361214, by rfl⟩) R722429
theorem R121661 : Reach 121661 := rs (se 3 (by rfl) ⟨22811, by rfl⟩) R45623
theorem R23583 : Reach 23583 := rs (se 1 (by rfl) ⟨17687, by rfl⟩) R35375
theorem R23663 : Reach 23663 := rs (se 1 (by rfl) ⟨17747, by rfl⟩) R35495
theorem R23707 : Reach 23707 := rs (se 1 (by rfl) ⟨17780, by rfl⟩) R35561
theorem R23711 : Reach 23711 := rs (se 1 (by rfl) ⟨17783, by rfl⟩) R35567
theorem R23743 : Reach 23743 := rs (se 1 (by rfl) ⟨17807, by rfl⟩) R35615
theorem R89383 : Reach 89383 := rs (se 1 (by rfl) ⟨67037, by rfl⟩) R134075
theorem R23963 : Reach 23963 := rs (se 1 (by rfl) ⟨17972, by rfl⟩) R35945
theorem R24047 : Reach 24047 := rs (se 1 (by rfl) ⟨18035, by rfl⟩) R36071
theorem R56969 : Reach 56969 := rs (se 2 (by rfl) ⟨21363, by rfl⟩) R42727
theorem R89819 : Reach 89819 := rs (se 1 (by rfl) ⟨67364, by rfl⟩) R134729
theorem R24383 : Reach 24383 := rs (se 1 (by rfl) ⟨18287, by rfl⟩) R36575
theorem R24571 : Reach 24571 := rs (se 1 (by rfl) ⟨18428, by rfl⟩) R36857
theorem R24703 : Reach 24703 := rs (se 1 (by rfl) ⟨18527, by rfl⟩) R37055
theorem R24731 : Reach 24731 := rs (se 1 (by rfl) ⟨18548, by rfl⟩) R37097
theorem R90287 : Reach 90287 := rs (se 1 (by rfl) ⟨67715, by rfl⟩) R135431
theorem R24815 : Reach 24815 := rs (se 1 (by rfl) ⟨18611, by rfl⟩) R37223
theorem R57671 : Reach 57671 := rs (se 1 (by rfl) ⟨43253, by rfl⟩) R86507
theorem R24911 : Reach 24911 := rs (se 1 (by rfl) ⟨18683, by rfl⟩) R37367
theorem R57815 : Reach 57815 := rs (se 1 (by rfl) ⟨43361, by rfl⟩) R86723
theorem R287225 : Reach 287225 := rs (se 2 (by rfl) ⟨107709, by rfl⟩) R215419
theorem R25371 : Reach 25371 := rs (se 1 (by rfl) ⟨19028, by rfl⟩) R38057
theorem R25415 : Reach 25415 := rs (se 1 (by rfl) ⟨19061, by rfl⟩) R38123
theorem R25471 : Reach 25471 := rs (se 1 (by rfl) ⟨19103, by rfl⟩) R38207
theorem R25599 : Reach 25599 := rs (se 1 (by rfl) ⟨19199, by rfl⟩) R38399
theorem R25671 : Reach 25671 := rs (se 1 (by rfl) ⟨19253, by rfl⟩) R38507
theorem R25851 : Reach 25851 := rs (se 1 (by rfl) ⟨19388, by rfl⟩) R38777
theorem R1402181 : Reach 1402181 := rs (se 4 (by rfl) ⟨131454, by rfl⟩) R262909
theorem R26015 : Reach 26015 := rs (se 1 (by rfl) ⟨19511, by rfl⟩) R39023
theorem R26063 : Reach 26063 := rs (se 1 (by rfl) ⟨19547, by rfl⟩) R39095
theorem R157157 : Reach 157157 := rs (se 4 (by rfl) ⟨14733, by rfl⟩) R29467
theorem R26351 : Reach 26351 := rs (se 1 (by rfl) ⟨19763, by rfl⟩) R39527
theorem R157427 : Reach 157427 := rs (se 1 (by rfl) ⟨118070, by rfl⟩) R236141
theorem R26367 : Reach 26367 := rs (se 1 (by rfl) ⟨19775, by rfl⟩) R39551
theorem R26439 : Reach 26439 := rs (se 1 (by rfl) ⟨19829, by rfl⟩) R39659
theorem R59219 : Reach 59219 := rs (se 1 (by rfl) ⟨44414, by rfl⟩) R88829
theorem R26459 : Reach 26459 := rs (se 1 (by rfl) ⟨19844, by rfl⟩) R39689
theorem R26619 : Reach 26619 := rs (se 1 (by rfl) ⟨19964, by rfl⟩) R39929
theorem R190511 : Reach 190511 := rs (se 1 (by rfl) ⟨142883, by rfl⟩) R285767
theorem R26799 : Reach 26799 := rs (se 1 (by rfl) ⟨20099, by rfl⟩) R40199
theorem R59615 : Reach 59615 := rs (se 1 (by rfl) ⟨44711, by rfl⟩) R89423
theorem R27039 : Reach 27039 := rs (se 1 (by rfl) ⟨20279, by rfl⟩) R40559
theorem R158183 : Reach 158183 := rs (se 1 (by rfl) ⟨118637, by rfl⟩) R237275
theorem R158543 : Reach 158543 := rs (se 1 (by rfl) ⟨118907, by rfl⟩) R237815
theorem R453599 : Reach 453599 := rs (se 1 (by rfl) ⟨340199, by rfl⟩) R680399
theorem R93631 : Reach 93631 := rs (se 1 (by rfl) ⟨70223, by rfl⟩) R140447
theorem R61175 : Reach 61175 := rs (se 1 (by rfl) ⟨45881, by rfl⟩) R91763
theorem R61631 : Reach 61631 := rs (se 1 (by rfl) ⟨46223, by rfl⟩) R92447
theorem R62279 : Reach 62279 := rs (se 1 (by rfl) ⟨46709, by rfl⟩) R93419
theorem R62375 : Reach 62375 := rs (se 1 (by rfl) ⟨46781, by rfl⟩) R93563
theorem R30235 : Reach 30235 := rs (se 1 (by rfl) ⟨22676, by rfl⟩) R45353
theorem R30415 : Reach 30415 := rs (se 1 (by rfl) ⟨22811, by rfl⟩) R45623
theorem R588185 : Reach 588185 := rs (se 2 (by rfl) ⟨220569, by rfl⟩) R441139
theorem R457325 : Reach 457325 := rs (se 3 (by rfl) ⟨85748, by rfl⟩) R171497
theorem R64385 : Reach 64385 := rs (se 2 (by rfl) ⟨24144, by rfl⟩) R48289
theorem R66089 : Reach 66089 := rs (se 2 (by rfl) ⟨24783, by rfl⟩) R49567
theorem R132029 : Reach 132029 := rs (se 3 (by rfl) ⟨24755, by rfl⟩) R49511
theorem R66529 : Reach 66529 := rs (se 2 (by rfl) ⟨24948, by rfl⟩) R49897
theorem R754721 : Reach 754721 := rs (se 2 (by rfl) ⟨283020, by rfl⟩) R566041
theorem R132191 : Reach 132191 := rs (se 1 (by rfl) ⟨99143, by rfl⟩) R198287
theorem R1180979 : Reach 1180979 := rs (se 1 (by rfl) ⟨885734, by rfl⟩) R1771469
theorem R951695 : Reach 951695 := rs (se 1 (by rfl) ⟨713771, by rfl⟩) R1427543
theorem R1345211 : Reach 1345211 := rs (se 1 (by rfl) ⟨1008908, by rfl⟩) R2017817
theorem R166333 : Reach 166333 := rs (se 3 (by rfl) ⟨31187, by rfl⟩) R62375
theorem R35279 : Reach 35279 := rs (se 1 (by rfl) ⟨26459, by rfl⟩) R52919
theorem R68617 : Reach 68617 := rs (se 2 (by rfl) ⟨25731, by rfl⟩) R51463
theorem R462419 : Reach 462419 := rs (se 1 (by rfl) ⟨346814, by rfl⟩) R693629
theorem R135107 : Reach 135107 := rs (se 1 (by rfl) ⟨101330, by rfl⟩) R202661
theorem R233447 : Reach 233447 := rs (se 1 (by rfl) ⟨175085, by rfl⟩) R350171
theorem R103457 : Reach 103457 := rs (se 2 (by rfl) ⟨38796, by rfl⟩) R77593
theorem R37979 : Reach 37979 := rs (se 1 (by rfl) ⟨28484, by rfl⟩) R56969
theorem R136505 : Reach 136505 := rs (se 2 (by rfl) ⟨51189, by rfl⟩) R102379
theorem R38447 : Reach 38447 := rs (se 1 (by rfl) ⟨28835, by rfl⟩) R57671
theorem R38543 : Reach 38543 := rs (se 1 (by rfl) ⟨28907, by rfl⟩) R57815
theorem R104771 : Reach 104771 := rs (se 1 (by rfl) ⟨78578, by rfl⟩) R157157
theorem R104951 : Reach 104951 := rs (se 1 (by rfl) ⟨78713, by rfl⟩) R157427
theorem R39479 : Reach 39479 := rs (se 1 (by rfl) ⟨29609, by rfl⟩) R59219
theorem R39743 : Reach 39743 := rs (se 1 (by rfl) ⟨29807, by rfl⟩) R59615
theorem R105455 : Reach 105455 := rs (se 1 (by rfl) ⟨79091, by rfl⟩) R158183
theorem R72809 : Reach 72809 := rs (se 2 (by rfl) ⟨27303, by rfl⟩) R54607
theorem R105695 : Reach 105695 := rs (se 1 (by rfl) ⟨79271, by rfl⟩) R158543
theorem R302399 : Reach 302399 := rs (se 1 (by rfl) ⟨226799, by rfl⟩) R453599
theorem R40313 : Reach 40313 := rs (se 2 (by rfl) ⟨15117, by rfl⟩) R30235
theorem R40553 : Reach 40553 := rs (se 2 (by rfl) ⟨15207, by rfl⟩) R30415
theorem R40783 : Reach 40783 := rs (se 1 (by rfl) ⟨30587, by rfl⟩) R61175
theorem R41087 : Reach 41087 := rs (se 1 (by rfl) ⟨30815, by rfl⟩) R61631
theorem R467471 : Reach 467471 := rs (se 1 (by rfl) ⟨350603, by rfl⟩) R701207
theorem R41519 : Reach 41519 := rs (se 1 (by rfl) ⟨31139, by rfl⟩) R62279
theorem R304883 : Reach 304883 := rs (se 1 (by rfl) ⟨228662, by rfl⟩) R457325
theorem R272123 : Reach 272123 := rs (se 1 (by rfl) ⟨204092, by rfl⟩) R408185
theorem R206671 : Reach 206671 := rs (se 1 (by rfl) ⟨155003, by rfl⟩) R310007
theorem R42923 : Reach 42923 := rs (se 1 (by rfl) ⟨32192, by rfl⟩) R64385
theorem R44219 : Reach 44219 := rs (se 1 (by rfl) ⟨33164, by rfl⟩) R66329
theorem R45481 : Reach 45481 := rs (se 2 (by rfl) ⟨17055, by rfl⟩) R34111
theorem R45535 : Reach 45535 := rs (se 1 (by rfl) ⟨34151, by rfl⟩) R68303
theorem R112079 : Reach 112079 := rs (se 1 (by rfl) ⟨84059, by rfl⟩) R168119
theorem R79919 : Reach 79919 := rs (se 1 (by rfl) ⟨59939, by rfl⟩) R119879
theorem R14956597 : Reach 14956597 := rs (se 5 (by rfl) ⟨701090, by rfl⟩) R1402181
theorem R47719 : Reach 47719 := rs (se 1 (by rfl) ⟨35789, by rfl⟩) R71579
theorem R81107 : Reach 81107 := rs (se 1 (by rfl) ⟨60830, by rfl⟩) R121661
theorem R50267 : Reach 50267 := rs (se 1 (by rfl) ⟨37700, by rfl⟩) R75401
theorem R182249 : Reach 182249 := rs (se 2 (by rfl) ⟨68343, by rfl⟩) R136687
theorem R182569 : Reach 182569 := rs (se 2 (by rfl) ⟨68463, by rfl⟩) R136927
theorem R182735 : Reach 182735 := rs (se 1 (by rfl) ⟨137051, by rfl⟩) R274103
theorem R1362743 : Reach 1362743 := rs (se 1 (by rfl) ⟨1022057, by rfl⟩) R2044115
theorem R183809 : Reach 183809 := rs (se 2 (by rfl) ⟨68928, by rfl⟩) R137857
theorem R52991 : Reach 52991 := rs (se 1 (by rfl) ⟨39743, by rfl⟩) R79487
theorem R119177 : Reach 119177 := rs (se 2 (by rfl) ⟨44691, by rfl⟩) R89383
theorem R53675 : Reach 53675 := rs (se 1 (by rfl) ⟨40256, by rfl⟩) R80513
theorem R53711 : Reach 53711 := rs (se 1 (by rfl) ⟨40283, by rfl⟩) R80567
theorem R53801 : Reach 53801 := rs (se 2 (by rfl) ⟨20175, by rfl⟩) R40351
theorem R119839 : Reach 119839 := rs (se 1 (by rfl) ⟨89879, by rfl⟩) R179759
theorem R251423 : Reach 251423 := rs (se 1 (by rfl) ⟨188567, by rfl⟩) R377135
theorem R316979 : Reach 316979 := rs (se 1 (by rfl) ⟨237734, by rfl⟩) R475469
theorem R87695 : Reach 87695 := rs (se 1 (by rfl) ⟨65771, by rfl⟩) R131543
theorem R55007 : Reach 55007 := rs (se 1 (by rfl) ⟨41255, by rfl⟩) R82511
theorem R481751 : Reach 481751 := rs (se 1 (by rfl) ⟨361313, by rfl⟩) R722627
theorem R514835 : Reach 514835 := rs (se 1 (by rfl) ⟨386126, by rfl⟩) R772253
theorem R56105 : Reach 56105 := rs (se 2 (by rfl) ⟨21039, by rfl⟩) R42079
theorem R23547 : Reach 23547 := rs (se 1 (by rfl) ⟨17660, by rfl⟩) R35321
theorem R23579 : Reach 23579 := rs (se 1 (by rfl) ⟨17684, by rfl⟩) R35369
theorem R56375 : Reach 56375 := rs (se 1 (by rfl) ⟨42281, by rfl⟩) R84563
theorem R155209 : Reach 155209 := rs (se 2 (by rfl) ⟨58203, by rfl⟩) R116407
theorem R24423 : Reach 24423 := rs (se 1 (by rfl) ⟨18317, by rfl⟩) R36635
theorem R24479 : Reach 24479 := rs (se 1 (by rfl) ⟨18359, by rfl⟩) R36719
theorem R122795 : Reach 122795 := rs (se 1 (by rfl) ⟨92096, by rfl⟩) R184193
theorem R57307 : Reach 57307 := rs (se 1 (by rfl) ⟨42980, by rfl⟩) R85961
theorem R24991 : Reach 24991 := rs (se 1 (by rfl) ⟨18743, by rfl⟩) R37487
theorem R25071 : Reach 25071 := rs (se 1 (by rfl) ⟨18803, by rfl⟩) R37607
theorem R58175 : Reach 58175 := rs (se 1 (by rfl) ⟨43631, by rfl⟩) R87263
theorem R25447 : Reach 25447 := rs (se 1 (by rfl) ⟨19085, by rfl⟩) R38171
theorem R25759 : Reach 25759 := rs (se 1 (by rfl) ⟨19319, by rfl⟩) R38639
theorem R91367 : Reach 91367 := rs (se 1 (by rfl) ⟨68525, by rfl⟩) R137051
theorem R58715 : Reach 58715 := rs (se 1 (by rfl) ⟨44036, by rfl⟩) R88073
theorem R321079 : Reach 321079 := rs (se 1 (by rfl) ⟨240809, by rfl⟩) R481619
theorem R190025 : Reach 190025 := rs (se 2 (by rfl) ⟨71259, by rfl⟩) R142519
theorem R58985 : Reach 58985 := rs (se 2 (by rfl) ⟨22119, by rfl⟩) R44239
theorem R26343 : Reach 26343 := rs (se 1 (by rfl) ⟨19757, by rfl⟩) R39515
theorem R124841 : Reach 124841 := rs (se 2 (by rfl) ⟨46815, by rfl⟩) R93631
theorem R26695 : Reach 26695 := rs (se 1 (by rfl) ⟨20021, by rfl⟩) R40043
theorem R26855 : Reach 26855 := rs (se 1 (by rfl) ⟨20141, by rfl⟩) R40283
theorem R26943 : Reach 26943 := rs (se 1 (by rfl) ⟨20207, by rfl⟩) R40415
theorem R59879 : Reach 59879 := rs (se 1 (by rfl) ⟨44909, by rfl⟩) R89819
theorem R60041 : Reach 60041 := rs (se 2 (by rfl) ⟨22515, by rfl⟩) R45031
theorem R27355 : Reach 27355 := rs (se 1 (by rfl) ⟨20516, by rfl⟩) R41033
theorem R60137 : Reach 60137 := rs (se 2 (by rfl) ⟨22551, by rfl⟩) R45103
theorem R60191 : Reach 60191 := rs (se 1 (by rfl) ⟨45143, by rfl⟩) R90287
theorem R27463 : Reach 27463 := rs (se 1 (by rfl) ⟨20597, by rfl⟩) R41195
theorem R60281 : Reach 60281 := rs (se 2 (by rfl) ⟨22605, by rfl⟩) R45211
theorem R191483 : Reach 191483 := rs (se 1 (by rfl) ⟨143612, by rfl⟩) R287225
theorem R27751 : Reach 27751 := rs (se 1 (by rfl) ⟨20813, by rfl⟩) R41627
theorem R650429 : Reach 650429 := rs (se 3 (by rfl) ⟨121955, by rfl⟩) R243911
theorem R28063 : Reach 28063 := rs (se 1 (by rfl) ⟨21047, by rfl⟩) R42095
theorem R191969 : Reach 191969 := rs (se 2 (by rfl) ⟨71988, by rfl⟩) R143977
theorem R61033 : Reach 61033 := rs (se 2 (by rfl) ⟨22887, by rfl⟩) R45775
theorem R28327 : Reach 28327 := rs (se 1 (by rfl) ⟨21245, by rfl⟩) R42491
theorem R28651 : Reach 28651 := rs (se 1 (by rfl) ⟨21488, by rfl⟩) R42977
theorem R127007 : Reach 127007 := rs (se 1 (by rfl) ⟨95255, by rfl⟩) R190511
theorem R28927 : Reach 28927 := rs (se 1 (by rfl) ⟨21695, by rfl⟩) R43391
theorem R62329 : Reach 62329 := rs (se 2 (by rfl) ⟨23373, by rfl⟩) R46747
theorem R30055 : Reach 30055 := rs (se 1 (by rfl) ⟨22541, by rfl⟩) R45083
theorem R359075 : Reach 359075 := rs (se 1 (by rfl) ⟨269306, by rfl⟩) R538613
theorem R392123 : Reach 392123 := rs (se 1 (by rfl) ⟨294092, by rfl⟩) R588185
theorem R31951 : Reach 31951 := rs (se 1 (by rfl) ⟨23963, by rfl⟩) R47927
theorem R32071 : Reach 32071 := rs (se 1 (by rfl) ⟨24053, by rfl⟩) R48107
theorem R787319 : Reach 787319 := rs (se 1 (by rfl) ⟨590489, by rfl⟩) R1180979
theorem R428105 : Reach 428105 := rs (se 2 (by rfl) ⟨160539, by rfl⟩) R321079
theorem R35327 : Reach 35327 := rs (se 1 (by rfl) ⟨26495, by rfl⟩) R52991
theorem R134045 : Reach 134045 := rs (se 3 (by rfl) ⟨25133, by rfl⟩) R50267
theorem R35783 : Reach 35783 := rs (se 1 (by rfl) ⟨26837, by rfl⟩) R53675
theorem R35807 : Reach 35807 := rs (se 1 (by rfl) ⟨26855, by rfl⟩) R53711
theorem R35867 : Reach 35867 := rs (se 1 (by rfl) ⟨26900, by rfl⟩) R53801
theorem R68971 : Reach 68971 := rs (se 1 (by rfl) ⟨51728, by rfl⟩) R103457
theorem R36473 : Reach 36473 := rs (se 2 (by rfl) ⟨13677, by rfl⟩) R27355
theorem R167615 : Reach 167615 := rs (se 1 (by rfl) ⟨125711, by rfl⟩) R251423
theorem R36617 : Reach 36617 := rs (se 2 (by rfl) ⟨13731, by rfl⟩) R27463
theorem R36671 : Reach 36671 := rs (se 1 (by rfl) ⟨27503, by rfl⟩) R55007
theorem R37001 : Reach 37001 := rs (se 2 (by rfl) ⟨13875, by rfl⟩) R27751
theorem R69967 : Reach 69967 := rs (se 1 (by rfl) ⟨52475, by rfl⟩) R104951
theorem R37403 : Reach 37403 := rs (se 1 (by rfl) ⟨28052, by rfl⟩) R56105
theorem R37417 : Reach 37417 := rs (se 2 (by rfl) ⟨14031, by rfl⟩) R28063
theorem R70303 : Reach 70303 := rs (se 1 (by rfl) ⟨52727, by rfl⟩) R105455
theorem R37583 : Reach 37583 := rs (se 1 (by rfl) ⟨28187, by rfl⟩) R56375
theorem R70463 : Reach 70463 := rs (se 1 (by rfl) ⟨52847, by rfl⟩) R105695
theorem R201599 : Reach 201599 := rs (se 1 (by rfl) ⟨151199, by rfl⟩) R302399
theorem R37769 : Reach 37769 := rs (se 2 (by rfl) ⟨14163, by rfl⟩) R28327
theorem R38201 : Reach 38201 := rs (se 2 (by rfl) ⟨14325, by rfl⟩) R28651
theorem R38569 : Reach 38569 := rs (se 2 (by rfl) ⟨14463, by rfl⟩) R28927
theorem R38783 : Reach 38783 := rs (se 1 (by rfl) ⟨29087, by rfl⟩) R58175
theorem R39143 : Reach 39143 := rs (se 1 (by rfl) ⟨29357, by rfl⟩) R58715
theorem R39323 : Reach 39323 := rs (se 1 (by rfl) ⟨29492, by rfl⟩) R58985
theorem R203255 : Reach 203255 := rs (se 1 (by rfl) ⟨152441, by rfl⟩) R304883
theorem R39919 : Reach 39919 := rs (se 1 (by rfl) ⟨29939, by rfl⟩) R59879
theorem R40027 : Reach 40027 := rs (se 1 (by rfl) ⟨30020, by rfl⟩) R60041
theorem R40073 : Reach 40073 := rs (se 2 (by rfl) ⟨15027, by rfl⟩) R30055
theorem R40091 : Reach 40091 := rs (se 1 (by rfl) ⟨30068, by rfl⟩) R60137
theorem R40127 : Reach 40127 := rs (se 1 (by rfl) ⟨30095, by rfl⟩) R60191
theorem R40187 : Reach 40187 := rs (se 1 (by rfl) ⟨30140, by rfl⟩) R60281
theorem R433619 : Reach 433619 := rs (se 1 (by rfl) ⟨325214, by rfl⟩) R650429
theorem R74719 : Reach 74719 := rs (se 1 (by rfl) ⟨56039, by rfl⟩) R112079
theorem R42601 : Reach 42601 := rs (se 2 (by rfl) ⟨15975, by rfl⟩) R31951
theorem R42761 : Reach 42761 := rs (se 2 (by rfl) ⟨16035, by rfl⟩) R32071
theorem R239383 : Reach 239383 := rs (se 1 (by rfl) ⟨179537, by rfl⟩) R359075
theorem R206945 : Reach 206945 := rs (se 2 (by rfl) ⟨77604, by rfl⟩) R155209
theorem R76409 : Reach 76409 := rs (se 2 (by rfl) ⟨28653, by rfl⟩) R57307
theorem R44059 : Reach 44059 := rs (se 1 (by rfl) ⟨33044, by rfl⟩) R66089
theorem R503147 : Reach 503147 := rs (se 1 (by rfl) ⟨377360, by rfl⟩) R754721
theorem R634463 : Reach 634463 := rs (se 1 (by rfl) ⟨475847, by rfl⟩) R951695
theorem R896807 : Reach 896807 := rs (se 1 (by rfl) ⟨672605, by rfl⟩) R1345211
theorem R110717 : Reach 110717 := rs (se 3 (by rfl) ⟨20759, by rfl⟩) R41519
theorem R308279 : Reach 308279 := rs (se 1 (by rfl) ⟨231209, by rfl⟩) R462419
theorem R275561 : Reach 275561 := rs (se 2 (by rfl) ⟨103335, by rfl⟩) R206671
theorem R79451 : Reach 79451 := rs (se 1 (by rfl) ⟨59588, by rfl⟩) R119177
theorem R243425 : Reach 243425 := rs (se 2 (by rfl) ⟨91284, by rfl⟩) R182569
theorem R211319 : Reach 211319 := rs (se 1 (by rfl) ⟨158489, by rfl⟩) R316979
theorem R343223 : Reach 343223 := rs (se 1 (by rfl) ⟨257417, by rfl⟩) R514835
theorem R48539 : Reach 48539 := rs (se 1 (by rfl) ⟨36404, by rfl⟩) R72809
theorem R81377 : Reach 81377 := rs (se 2 (by rfl) ⟨30516, by rfl⟩) R61033
theorem R81863 : Reach 81863 := rs (se 1 (by rfl) ⟨61397, by rfl⟩) R122795
theorem R311647 : Reach 311647 := rs (se 1 (by rfl) ⟨233735, by rfl⟩) R467471
theorem R279389 : Reach 279389 := rs (se 3 (by rfl) ⟨52385, by rfl⟩) R104771
theorem R83105 : Reach 83105 := rs (se 2 (by rfl) ⟨31164, by rfl⟩) R62329
theorem R181415 : Reach 181415 := rs (se 1 (by rfl) ⟨136061, by rfl⟩) R272123
theorem R83227 : Reach 83227 := rs (se 1 (by rfl) ⟨62420, by rfl⟩) R124841
theorem R84671 : Reach 84671 := rs (se 1 (by rfl) ⟨63503, by rfl⟩) R127007
theorem R19942129 : Reach 19942129 := rs (se 2 (by rfl) ⟨7478298, by rfl⟩) R14956597
theorem R53279 : Reach 53279 := rs (se 1 (by rfl) ⟨39959, by rfl⟩) R79919
theorem R54071 : Reach 54071 := rs (se 1 (by rfl) ⟨40553, by rfl⟩) R81107
theorem R54377 : Reach 54377 := rs (se 2 (by rfl) ⟨20391, by rfl⟩) R40783
theorem R88019 : Reach 88019 := rs (se 1 (by rfl) ⟨66014, by rfl⟩) R132029
theorem R88127 : Reach 88127 := rs (se 1 (by rfl) ⟨66095, by rfl⟩) R132191
theorem R88705 : Reach 88705 := rs (se 2 (by rfl) ⟨33264, by rfl⟩) R66529
theorem R121499 : Reach 121499 := rs (se 1 (by rfl) ⟨91124, by rfl⟩) R182249
theorem R121823 : Reach 121823 := rs (se 1 (by rfl) ⟨91367, by rfl⟩) R182735
theorem R23519 : Reach 23519 := rs (se 1 (by rfl) ⟨17639, by rfl⟩) R35279
theorem R908495 : Reach 908495 := rs (se 1 (by rfl) ⟨681371, by rfl⟩) R1362743
theorem R122539 : Reach 122539 := rs (se 1 (by rfl) ⟨91904, by rfl⟩) R183809
theorem R90071 : Reach 90071 := rs (se 1 (by rfl) ⟨67553, by rfl⟩) R135107
theorem R221777 : Reach 221777 := rs (se 2 (by rfl) ⟨83166, by rfl⟩) R166333
theorem R25319 : Reach 25319 := rs (se 1 (by rfl) ⟨18989, by rfl⟩) R37979
theorem R91003 : Reach 91003 := rs (se 1 (by rfl) ⟨68252, by rfl⟩) R136505
theorem R25631 : Reach 25631 := rs (se 1 (by rfl) ⟨19223, by rfl⟩) R38447
theorem R25695 : Reach 25695 := rs (se 1 (by rfl) ⟨19271, by rfl⟩) R38543
theorem R58463 : Reach 58463 := rs (se 1 (by rfl) ⟨43847, by rfl⟩) R87695
theorem R91489 : Reach 91489 := rs (se 2 (by rfl) ⟨34308, by rfl⟩) R68617
theorem R321167 : Reach 321167 := rs (se 1 (by rfl) ⟨240875, by rfl⟩) R481751
theorem R26319 : Reach 26319 := rs (se 1 (by rfl) ⟨19739, by rfl⟩) R39479
theorem R26495 : Reach 26495 := rs (se 1 (by rfl) ⟨19871, by rfl⟩) R39743
theorem R26875 : Reach 26875 := rs (se 1 (by rfl) ⟨20156, by rfl⟩) R40313
theorem R27035 : Reach 27035 := rs (se 1 (by rfl) ⟨20276, by rfl⟩) R40553
theorem R27391 : Reach 27391 := rs (se 1 (by rfl) ⟨20543, by rfl⟩) R41087
theorem R27679 : Reach 27679 := rs (se 1 (by rfl) ⟨20759, by rfl⟩) R41519
theorem R60641 : Reach 60641 := rs (se 2 (by rfl) ⟨22740, by rfl⟩) R45481
theorem R60713 : Reach 60713 := rs (se 2 (by rfl) ⟨22767, by rfl⟩) R45535
theorem R60911 : Reach 60911 := rs (se 1 (by rfl) ⟨45683, by rfl⟩) R91367
theorem R126683 : Reach 126683 := rs (se 1 (by rfl) ⟨95012, by rfl⟩) R190025
theorem R28615 : Reach 28615 := rs (se 1 (by rfl) ⟨21461, by rfl⟩) R42923
theorem R159785 : Reach 159785 := rs (se 2 (by rfl) ⟨59919, by rfl⟩) R119839
theorem R127655 : Reach 127655 := rs (se 1 (by rfl) ⟨95741, by rfl⟩) R191483
theorem R29479 : Reach 29479 := rs (se 1 (by rfl) ⟨22109, by rfl⟩) R44219
theorem R127979 : Reach 127979 := rs (se 1 (by rfl) ⟨95984, by rfl⟩) R191969
theorem R63625 : Reach 63625 := rs (se 2 (by rfl) ⟨23859, by rfl⟩) R47719
theorem R261415 : Reach 261415 := rs (se 1 (by rfl) ⟨196061, by rfl⟩) R392123
theorem R622525 : Reach 622525 := rs (se 3 (by rfl) ⟨116723, by rfl⟩) R233447
theorem R524879 : Reach 524879 := rs (se 1 (by rfl) ⟨393659, by rfl⟩) R787319
theorem R99625 : Reach 99625 := rs (se 2 (by rfl) ⟨37359, by rfl⟩) R74719
theorem R35519 : Reach 35519 := rs (se 1 (by rfl) ⟨26639, by rfl⟩) R53279
theorem R36047 : Reach 36047 := rs (se 1 (by rfl) ⟨27035, by rfl⟩) R54071
theorem R134399 : Reach 134399 := rs (se 1 (by rfl) ⟨100799, by rfl⟩) R201599
theorem R36251 : Reach 36251 := rs (se 1 (by rfl) ⟨27188, by rfl⟩) R54377
theorem R36521 : Reach 36521 := rs (se 2 (by rfl) ⟨13695, by rfl⟩) R27391
theorem R36905 : Reach 36905 := rs (se 2 (by rfl) ⟨13839, by rfl⟩) R27679
theorem R135503 : Reach 135503 := rs (se 1 (by rfl) ⟨101627, by rfl⟩) R203255
theorem R38153 : Reach 38153 := rs (se 2 (by rfl) ⟨14307, by rfl⟩) R28615
theorem R38975 : Reach 38975 := rs (se 1 (by rfl) ⟨29231, by rfl⟩) R58463
theorem R39305 : Reach 39305 := rs (se 2 (by rfl) ⟨14739, by rfl⟩) R29479
theorem R137963 : Reach 137963 := rs (se 1 (by rfl) ⟨103472, by rfl⟩) R206945
theorem R40427 : Reach 40427 := rs (se 1 (by rfl) ⟨30320, by rfl⟩) R60641
theorem R40475 : Reach 40475 := rs (se 1 (by rfl) ⟨30356, by rfl⟩) R60713
theorem R335431 : Reach 335431 := rs (se 1 (by rfl) ⟨251573, by rfl⟩) R503147
theorem R40607 : Reach 40607 := rs (se 1 (by rfl) ⟨30455, by rfl⟩) R60911
theorem R597871 : Reach 597871 := rs (se 1 (by rfl) ⟨448403, by rfl⟩) R896807
theorem R106523 : Reach 106523 := rs (se 1 (by rfl) ⟨79892, by rfl⟩) R159785
theorem R73811 : Reach 73811 := rs (se 1 (by rfl) ⟨55358, by rfl⟩) R110717
theorem R205519 : Reach 205519 := rs (se 1 (by rfl) ⟨154139, by rfl⟩) R308279
theorem R140879 : Reach 140879 := rs (se 1 (by rfl) ⟨105659, by rfl⟩) R211319
theorem R830033 : Reach 830033 := rs (se 2 (by rfl) ⟨311262, by rfl⟩) R622525
theorem R110969 : Reach 110969 := rs (se 2 (by rfl) ⟨41613, by rfl⟩) R83227
theorem R373157 : Reach 373157 := rs (se 4 (by rfl) ⟨34983, by rfl⟩) R69967
theorem R111743 : Reach 111743 := rs (se 1 (by rfl) ⟨83807, by rfl⟩) R167615
theorem R46975 : Reach 46975 := rs (se 1 (by rfl) ⟨35231, by rfl⟩) R70463
theorem R26589505 : Reach 26589505 := rs (se 2 (by rfl) ⟨9971064, by rfl⟩) R19942129
theorem R80999 : Reach 80999 := rs (se 1 (by rfl) ⟨60749, by rfl⟩) R121499
theorem R81215 : Reach 81215 := rs (se 1 (by rfl) ⟨60911, by rfl⟩) R121823
theorem R605663 : Reach 605663 := rs (se 1 (by rfl) ⟨454247, by rfl⟩) R908495
theorem R147851 : Reach 147851 := rs (se 1 (by rfl) ⟨110888, by rfl⟩) R221777
theorem R49889 : Reach 49889 := rs (se 2 (by rfl) ⟨18708, by rfl⟩) R37417
theorem R214111 : Reach 214111 := rs (se 1 (by rfl) ⟨160583, by rfl⟩) R321167
theorem R50939 : Reach 50939 := rs (se 1 (by rfl) ⟨38204, by rfl⟩) R76409
theorem R51425 : Reach 51425 := rs (se 2 (by rfl) ⟨19284, by rfl⟩) R38569
theorem R84455 : Reach 84455 := rs (se 1 (by rfl) ⟨63341, by rfl⟩) R126683
theorem R84833 : Reach 84833 := rs (se 2 (by rfl) ⟨31812, by rfl⟩) R63625
theorem R85103 : Reach 85103 := rs (se 1 (by rfl) ⟨63827, by rfl⟩) R127655
theorem R85319 : Reach 85319 := rs (se 1 (by rfl) ⟨63989, by rfl⟩) R127979
theorem R183707 : Reach 183707 := rs (se 1 (by rfl) ⟨137780, by rfl⟩) R275561
theorem R118273 : Reach 118273 := rs (se 2 (by rfl) ⟨44352, by rfl⟩) R88705
theorem R52967 : Reach 52967 := rs (se 1 (by rfl) ⟨39725, by rfl⟩) R79451
theorem R53225 : Reach 53225 := rs (se 2 (by rfl) ⟨19959, by rfl⟩) R39919
theorem R53369 : Reach 53369 := rs (se 2 (by rfl) ⟨20013, by rfl⟩) R40027
theorem R348553 : Reach 348553 := rs (se 2 (by rfl) ⟨130707, by rfl⟩) R261415
theorem R54251 : Reach 54251 := rs (se 1 (by rfl) ⟨40688, by rfl⟩) R81377
theorem R54575 : Reach 54575 := rs (se 1 (by rfl) ⟨40931, by rfl⟩) R81863
theorem R415529 : Reach 415529 := rs (se 2 (by rfl) ⟨155823, by rfl⟩) R311647
theorem R55403 : Reach 55403 := rs (se 1 (by rfl) ⟨41552, by rfl⟩) R83105
theorem R120943 : Reach 120943 := rs (se 1 (by rfl) ⟨90707, by rfl⟩) R181415
theorem R121337 : Reach 121337 := rs (se 2 (by rfl) ⟨45501, by rfl⟩) R91003
theorem R23551 : Reach 23551 := rs (se 1 (by rfl) ⟨17663, by rfl⟩) R35327
theorem R56447 : Reach 56447 := rs (se 1 (by rfl) ⟨42335, by rfl⟩) R84671
theorem R121985 : Reach 121985 := rs (se 2 (by rfl) ⟨45744, by rfl⟩) R91489
theorem R89363 : Reach 89363 := rs (se 1 (by rfl) ⟨67022, by rfl⟩) R134045
theorem R23855 : Reach 23855 := rs (se 1 (by rfl) ⟨17891, by rfl⟩) R35783
theorem R23871 : Reach 23871 := rs (se 1 (by rfl) ⟨17903, by rfl⟩) R35807
theorem R23911 : Reach 23911 := rs (se 1 (by rfl) ⟨17933, by rfl⟩) R35867
theorem R56801 : Reach 56801 := rs (se 2 (by rfl) ⟨21300, by rfl⟩) R42601
theorem R745037 : Reach 745037 := rs (se 3 (by rfl) ⟨139694, by rfl⟩) R279389
theorem R319177 : Reach 319177 := rs (se 2 (by rfl) ⟨119691, by rfl⟩) R239383
theorem R24315 : Reach 24315 := rs (se 1 (by rfl) ⟨18236, by rfl⟩) R36473
theorem R24411 : Reach 24411 := rs (se 1 (by rfl) ⟨18308, by rfl⟩) R36617
theorem R24447 : Reach 24447 := rs (se 1 (by rfl) ⟨18335, by rfl⟩) R36671
theorem R24667 : Reach 24667 := rs (se 1 (by rfl) ⟨18500, by rfl⟩) R37001
theorem R24935 : Reach 24935 := rs (se 1 (by rfl) ⟨18701, by rfl⟩) R37403
theorem R25055 : Reach 25055 := rs (se 1 (by rfl) ⟨18791, by rfl⟩) R37583
theorem R25179 : Reach 25179 := rs (se 1 (by rfl) ⟨18884, by rfl⟩) R37769
theorem R25467 : Reach 25467 := rs (se 1 (by rfl) ⟨19100, by rfl⟩) R38201
theorem R25855 : Reach 25855 := rs (se 1 (by rfl) ⟨19391, by rfl⟩) R38783
theorem R58679 : Reach 58679 := rs (se 1 (by rfl) ⟨44009, by rfl⟩) R88019
theorem R58745 : Reach 58745 := rs (se 2 (by rfl) ⟨22029, by rfl⟩) R44059
theorem R58751 : Reach 58751 := rs (se 1 (by rfl) ⟨44063, by rfl⟩) R88127
theorem R26095 : Reach 26095 := rs (se 1 (by rfl) ⟨19571, by rfl⟩) R39143
theorem R26215 : Reach 26215 := rs (se 1 (by rfl) ⟨19661, by rfl⟩) R39323
theorem R91961 : Reach 91961 := rs (se 2 (by rfl) ⟨34485, by rfl⟩) R68971
theorem R26715 : Reach 26715 := rs (se 1 (by rfl) ⟨20036, by rfl⟩) R40073
theorem R26727 : Reach 26727 := rs (se 1 (by rfl) ⟨20045, by rfl⟩) R40091
theorem R26751 : Reach 26751 := rs (se 1 (by rfl) ⟨20063, by rfl⟩) R40127
theorem R26791 : Reach 26791 := rs (se 1 (by rfl) ⟨20093, by rfl⟩) R40187
theorem R289079 : Reach 289079 := rs (se 1 (by rfl) ⟨216809, by rfl⟩) R433619
theorem R60047 : Reach 60047 := rs (se 1 (by rfl) ⟨45035, by rfl⟩) R90071
theorem R1141613 : Reach 1141613 := rs (se 3 (by rfl) ⟨214052, by rfl⟩) R428105
theorem R93737 : Reach 93737 := rs (se 2 (by rfl) ⟨35151, by rfl⟩) R70303
theorem R28507 : Reach 28507 := rs (se 1 (by rfl) ⟨21380, by rfl⟩) R42761
theorem R422975 : Reach 422975 := rs (se 1 (by rfl) ⟨317231, by rfl⟩) R634463
theorem R129437 : Reach 129437 := rs (se 3 (by rfl) ⟨24269, by rfl⟩) R48539
theorem R162283 : Reach 162283 := rs (se 1 (by rfl) ⟨121712, by rfl⟩) R243425
theorem R228815 : Reach 228815 := rs (se 1 (by rfl) ⟨171611, by rfl⟩) R343223
theorem R163385 : Reach 163385 := rs (se 2 (by rfl) ⟨61269, by rfl⟩) R122539
theorem R196829 : Reach 196829 := rs (se 3 (by rfl) ⟨36905, by rfl⟩) R73811
theorem R98567 : Reach 98567 := rs (se 1 (by rfl) ⟨73925, by rfl⟩) R147851
theorem R33259 : Reach 33259 := rs (se 1 (by rfl) ⟨24944, by rfl⟩) R49889
theorem R33959 : Reach 33959 := rs (se 1 (by rfl) ⟨25469, by rfl⟩) R50939
theorem R34283 : Reach 34283 := rs (se 1 (by rfl) ⟨25712, by rfl⟩) R51425
theorem R132833 : Reach 132833 := rs (se 2 (by rfl) ⟨49812, by rfl⟩) R99625
theorem R35311 : Reach 35311 := rs (se 1 (by rfl) ⟨26483, by rfl⟩) R52967
theorem R35483 : Reach 35483 := rs (se 1 (by rfl) ⟨26612, by rfl⟩) R53225
theorem R35579 : Reach 35579 := rs (se 1 (by rfl) ⟨26684, by rfl⟩) R53369
theorem R36167 : Reach 36167 := rs (se 1 (by rfl) ⟨27125, by rfl⟩) R54251
theorem R36383 : Reach 36383 := rs (se 1 (by rfl) ⟨27287, by rfl⟩) R54575
theorem R36935 : Reach 36935 := rs (se 1 (by rfl) ⟨27701, by rfl⟩) R55403
theorem R37631 : Reach 37631 := rs (se 1 (by rfl) ⟨28223, by rfl⟩) R56447
theorem R496691 : Reach 496691 := rs (se 1 (by rfl) ⟨372518, by rfl⟩) R745037
theorem R38009 : Reach 38009 := rs (se 2 (by rfl) ⟨14253, by rfl⟩) R28507
theorem R71015 : Reach 71015 := rs (se 1 (by rfl) ⟨53261, by rfl⟩) R106523
theorem R464737 : Reach 464737 := rs (se 2 (by rfl) ⟨174276, by rfl⟩) R348553
theorem R39119 : Reach 39119 := rs (se 1 (by rfl) ⟨29339, by rfl⟩) R58679
theorem R39167 : Reach 39167 := rs (se 1 (by rfl) ⟨29375, by rfl⟩) R58751
theorem R40031 : Reach 40031 := rs (se 1 (by rfl) ⟨30023, by rfl⟩) R60047
theorem R761075 : Reach 761075 := rs (se 1 (by rfl) ⟨570806, by rfl⟩) R1141613
theorem R73979 : Reach 73979 := rs (se 1 (by rfl) ⟨55484, by rfl⟩) R110969
theorem R74495 : Reach 74495 := rs (se 1 (by rfl) ⟨55871, by rfl⟩) R111743
theorem R3188645 : Reach 3188645 := rs (se 4 (by rfl) ⟨298935, by rfl⟩) R597871
theorem R403775 : Reach 403775 := rs (se 1 (by rfl) ⟨302831, by rfl⟩) R605663
theorem R108923 : Reach 108923 := rs (se 1 (by rfl) ⟨81692, by rfl⟩) R163385
theorem R274025 : Reach 274025 := rs (se 2 (by rfl) ⟨102759, by rfl⟩) R205519
theorem R277019 : Reach 277019 := rs (se 1 (by rfl) ⟨207764, by rfl⟩) R415529
theorem R80891 : Reach 80891 := rs (se 1 (by rfl) ⟨60668, by rfl⟩) R121337
theorem R81323 : Reach 81323 := rs (se 1 (by rfl) ⟨60992, by rfl⟩) R121985
theorem R248771 : Reach 248771 := rs (se 1 (by rfl) ⟨186578, by rfl⟩) R373157
theorem R216377 : Reach 216377 := rs (se 2 (by rfl) ⟨81141, by rfl⟩) R162283
theorem R281983 : Reach 281983 := rs (se 1 (by rfl) ⟨211487, by rfl⟩) R422975
theorem R151469 : Reach 151469 := rs (se 3 (by rfl) ⟨28400, by rfl⟩) R56801
theorem R86291 : Reach 86291 := rs (se 1 (by rfl) ⟨64718, by rfl⟩) R129437
theorem R53999 : Reach 53999 := rs (se 1 (by rfl) ⟨40499, by rfl⟩) R80999
theorem R447241 : Reach 447241 := rs (se 2 (by rfl) ⟨167715, by rfl⟩) R335431
theorem R54143 : Reach 54143 := rs (se 1 (by rfl) ⟨40607, by rfl⟩) R81215
theorem R152543 : Reach 152543 := rs (se 1 (by rfl) ⟨114407, by rfl⟩) R228815
theorem R349919 : Reach 349919 := rs (se 1 (by rfl) ⟨262439, by rfl⟩) R524879
theorem R645029 : Reach 645029 := rs (se 4 (by rfl) ⟨60471, by rfl⟩) R120943
theorem R285481 : Reach 285481 := rs (se 2 (by rfl) ⟨107055, by rfl⟩) R214111
theorem R56303 : Reach 56303 := rs (se 1 (by rfl) ⟨42227, by rfl⟩) R84455
theorem R23679 : Reach 23679 := rs (se 1 (by rfl) ⟨17759, by rfl⟩) R35519
theorem R56555 : Reach 56555 := rs (se 1 (by rfl) ⟨42416, by rfl⟩) R84833
theorem R56735 : Reach 56735 := rs (se 1 (by rfl) ⟨42551, by rfl⟩) R85103
theorem R24031 : Reach 24031 := rs (se 1 (by rfl) ⟨18023, by rfl⟩) R36047
theorem R89599 : Reach 89599 := rs (se 1 (by rfl) ⟨67199, by rfl⟩) R134399
theorem R56879 : Reach 56879 := rs (se 1 (by rfl) ⟨42659, by rfl⟩) R85319
theorem R24167 : Reach 24167 := rs (se 1 (by rfl) ⟨18125, by rfl⟩) R36251
theorem R122471 : Reach 122471 := rs (se 1 (by rfl) ⟨91853, by rfl⟩) R183707
theorem R24347 : Reach 24347 := rs (se 1 (by rfl) ⟨18260, by rfl⟩) R36521
theorem R24603 : Reach 24603 := rs (se 1 (by rfl) ⟨18452, by rfl⟩) R36905
theorem R90335 : Reach 90335 := rs (se 1 (by rfl) ⟨67751, by rfl⟩) R135503
theorem R25435 : Reach 25435 := rs (se 1 (by rfl) ⟨19076, by rfl⟩) R38153
theorem R156653 : Reach 156653 := rs (se 3 (by rfl) ⟨29372, by rfl⟩) R58745
theorem R25983 : Reach 25983 := rs (se 1 (by rfl) ⟨19487, by rfl⟩) R38975
theorem R26203 : Reach 26203 := rs (se 1 (by rfl) ⟨19652, by rfl⟩) R39305
theorem R91975 : Reach 91975 := rs (se 1 (by rfl) ⟨68981, by rfl⟩) R137963
theorem R157697 : Reach 157697 := rs (se 2 (by rfl) ⟨59136, by rfl⟩) R118273
theorem R59575 : Reach 59575 := rs (se 1 (by rfl) ⟨44681, by rfl⟩) R89363
theorem R26951 : Reach 26951 := rs (se 1 (by rfl) ⟨20213, by rfl⟩) R40427
theorem R26983 : Reach 26983 := rs (se 1 (by rfl) ⟨20237, by rfl⟩) R40475
theorem R27071 : Reach 27071 := rs (se 1 (by rfl) ⟨20303, by rfl⟩) R40607
theorem R93919 : Reach 93919 := rs (se 1 (by rfl) ⟨70439, by rfl⟩) R140879
theorem R61307 : Reach 61307 := rs (se 1 (by rfl) ⟨45980, by rfl⟩) R91961
theorem R192719 : Reach 192719 := rs (se 1 (by rfl) ⟨144539, by rfl⟩) R289079
theorem R553355 : Reach 553355 := rs (se 1 (by rfl) ⟨415016, by rfl⟩) R830033
theorem R62491 : Reach 62491 := rs (se 1 (by rfl) ⟨46868, by rfl⟩) R93737
theorem R62633 : Reach 62633 := rs (se 2 (by rfl) ⟨23487, by rfl⟩) R46975
theorem R35452673 : Reach 35452673 := rs (se 2 (by rfl) ⟨13294752, by rfl⟩) R26589505
theorem R425569 : Reach 425569 := rs (se 2 (by rfl) ⟨159588, by rfl⟩) R319177
theorem R131219 : Reach 131219 := rs (se 1 (by rfl) ⟨98414, by rfl⟩) R196829
theorem R65711 : Reach 65711 := rs (se 1 (by rfl) ⟨49283, by rfl⟩) R98567
theorem R165847 : Reach 165847 := rs (se 1 (by rfl) ⟨124385, by rfl⟩) R248771
theorem R100979 : Reach 100979 := rs (se 1 (by rfl) ⟨75734, by rfl⟩) R151469
theorem R35999 : Reach 35999 := rs (se 1 (by rfl) ⟨26999, by rfl⟩) R53999
theorem R36095 : Reach 36095 := rs (se 1 (by rfl) ⟨27071, by rfl⟩) R54143
theorem R101695 : Reach 101695 := rs (se 1 (by rfl) ⟨76271, by rfl⟩) R152543
theorem R331127 : Reach 331127 := rs (se 1 (by rfl) ⟨248345, by rfl⟩) R496691
theorem R233279 : Reach 233279 := rs (se 1 (by rfl) ⟨174959, by rfl⟩) R349919
theorem R430019 : Reach 430019 := rs (se 1 (by rfl) ⟨322514, by rfl⟩) R645029
theorem R37535 : Reach 37535 := rs (se 1 (by rfl) ⟨28151, by rfl⟩) R56303
theorem R37703 : Reach 37703 := rs (se 1 (by rfl) ⟨28277, by rfl⟩) R56555
theorem R37823 : Reach 37823 := rs (se 1 (by rfl) ⟨28367, by rfl⟩) R56735
theorem R37919 : Reach 37919 := rs (se 1 (by rfl) ⟨28439, by rfl⟩) R56879
theorem R104435 : Reach 104435 := rs (se 1 (by rfl) ⟨78326, by rfl⟩) R156653
theorem R596321 : Reach 596321 := rs (se 2 (by rfl) ⟨223620, by rfl⟩) R447241
theorem R105131 : Reach 105131 := rs (se 1 (by rfl) ⟨78848, by rfl⟩) R157697
theorem R269183 : Reach 269183 := rs (se 1 (by rfl) ⟨201887, by rfl⟩) R403775
theorem R40871 : Reach 40871 := rs (se 1 (by rfl) ⟨30653, by rfl⟩) R61307
theorem R368903 : Reach 368903 := rs (se 1 (by rfl) ⟨276677, by rfl⟩) R553355
theorem R41755 : Reach 41755 := rs (se 1 (by rfl) ⟨31316, by rfl⟩) R62633
theorem R23635115 : Reach 23635115 := rs (se 1 (by rfl) ⟨17726336, by rfl⟩) R35452673
theorem R567425 : Reach 567425 := rs (se 2 (by rfl) ⟨212784, by rfl⟩) R425569
theorem R44345 : Reach 44345 := rs (se 2 (by rfl) ⟨16629, by rfl⟩) R33259
theorem R144251 : Reach 144251 := rs (se 1 (by rfl) ⟨108188, by rfl⟩) R216377
theorem R406781 : Reach 406781 := rs (se 3 (by rfl) ⟨76271, by rfl⟩) R152543
theorem R79433 : Reach 79433 := rs (se 2 (by rfl) ⟨29787, by rfl⟩) R59575
theorem R47081 : Reach 47081 := rs (se 2 (by rfl) ⟨17655, by rfl⟩) R35311
theorem R375977 : Reach 375977 := rs (se 2 (by rfl) ⟨140991, by rfl⟩) R281983
theorem R507383 : Reach 507383 := rs (se 1 (by rfl) ⟨380537, by rfl⟩) R761075
theorem R81647 : Reach 81647 := rs (se 1 (by rfl) ⟨61235, by rfl⟩) R122471
theorem R49319 : Reach 49319 := rs (se 1 (by rfl) ⟨36989, by rfl⟩) R73979
theorem R49663 : Reach 49663 := rs (se 1 (by rfl) ⟨37247, by rfl⟩) R74495
theorem R83321 : Reach 83321 := rs (se 2 (by rfl) ⟨31245, by rfl⟩) R62491
theorem R182683 : Reach 182683 := rs (se 1 (by rfl) ⟨137012, by rfl⟩) R274025
theorem R380641 : Reach 380641 := rs (se 2 (by rfl) ⟨142740, by rfl⟩) R285481
theorem R184679 : Reach 184679 := rs (se 1 (by rfl) ⟨138509, by rfl⟩) R277019
theorem R53927 : Reach 53927 := rs (se 1 (by rfl) ⟨40445, by rfl⟩) R80891
theorem R119465 : Reach 119465 := rs (se 2 (by rfl) ⟨44799, by rfl⟩) R89599
theorem R54215 : Reach 54215 := rs (se 1 (by rfl) ⟨40661, by rfl⟩) R81323
theorem R88555 : Reach 88555 := rs (se 1 (by rfl) ⟨66416, by rfl⟩) R132833
theorem R23655 : Reach 23655 := rs (se 1 (by rfl) ⟨17741, by rfl⟩) R35483
theorem R23719 : Reach 23719 := rs (se 1 (by rfl) ⟨17789, by rfl⟩) R35579
theorem R24111 : Reach 24111 := rs (se 1 (by rfl) ⟨18083, by rfl⟩) R36167
theorem R24255 : Reach 24255 := rs (se 1 (by rfl) ⟨18191, by rfl⟩) R36383
theorem R122633 : Reach 122633 := rs (se 2 (by rfl) ⟨45987, by rfl⟩) R91975
theorem R24623 : Reach 24623 := rs (se 1 (by rfl) ⟨18467, by rfl⟩) R36935
theorem R57527 : Reach 57527 := rs (se 1 (by rfl) ⟨43145, by rfl⟩) R86291
theorem R90557 : Reach 90557 := rs (se 3 (by rfl) ⟨16979, by rfl⟩) R33959
theorem R25087 : Reach 25087 := rs (se 1 (by rfl) ⟨18815, by rfl⟩) R37631
theorem R25339 : Reach 25339 := rs (se 1 (by rfl) ⟨19004, by rfl⟩) R38009
theorem R189373 : Reach 189373 := rs (se 3 (by rfl) ⟨35507, by rfl⟩) R71015
theorem R91421 : Reach 91421 := rs (se 3 (by rfl) ⟨17141, by rfl⟩) R34283
theorem R26079 : Reach 26079 := rs (se 1 (by rfl) ⟨19559, by rfl⟩) R39119
theorem R26111 : Reach 26111 := rs (se 1 (by rfl) ⟨19583, by rfl⟩) R39167
theorem R26687 : Reach 26687 := rs (se 1 (by rfl) ⟨20015, by rfl⟩) R40031
theorem R125225 : Reach 125225 := rs (se 2 (by rfl) ⟨46959, by rfl⟩) R93919
theorem R60223 : Reach 60223 := rs (se 1 (by rfl) ⟨45167, by rfl⟩) R90335
theorem R290461 : Reach 290461 := rs (se 3 (by rfl) ⟨54461, by rfl⟩) R108923
theorem R2125763 : Reach 2125763 := rs (se 1 (by rfl) ⟨1594322, by rfl⟩) R3188645
theorem R94877 : Reach 94877 := rs (se 3 (by rfl) ⟨17789, by rfl⟩) R35579
theorem R619649 : Reach 619649 := rs (se 2 (by rfl) ⟨232368, by rfl⟩) R464737
theorem R128479 : Reach 128479 := rs (se 1 (by rfl) ⟨96359, by rfl⟩) R192719
theorem R32879 : Reach 32879 := rs (se 1 (by rfl) ⟨24659, by rfl⟩) R49319
theorem R66217 : Reach 66217 := rs (se 2 (by rfl) ⟨24831, by rfl⟩) R49663
theorem R67319 : Reach 67319 := rs (se 1 (by rfl) ⟨50489, by rfl⟩) R100979
theorem R100541 : Reach 100541 := rs (se 3 (by rfl) ⟨18851, by rfl⟩) R37703
theorem R35951 : Reach 35951 := rs (se 1 (by rfl) ⟨26963, by rfl⟩) R53927
theorem R36143 : Reach 36143 := rs (se 1 (by rfl) ⟨27107, by rfl⟩) R54215
theorem R69623 : Reach 69623 := rs (se 1 (by rfl) ⟨52217, by rfl⟩) R104435
theorem R397547 : Reach 397547 := rs (se 1 (by rfl) ⟨298160, by rfl⟩) R596321
theorem R135593 : Reach 135593 := rs (se 2 (by rfl) ⟨50847, by rfl⟩) R101695
theorem R70087 : Reach 70087 := rs (se 1 (by rfl) ⟨52565, by rfl⟩) R105131
theorem R38351 : Reach 38351 := rs (se 1 (by rfl) ⟨28763, by rfl⟩) R57527
theorem R171305 : Reach 171305 := rs (se 2 (by rfl) ⟨64239, by rfl⟩) R128479
theorem R1417175 : Reach 1417175 := rs (se 1 (by rfl) ⟨1062881, by rfl⟩) R2125763
theorem R271187 : Reach 271187 := rs (se 1 (by rfl) ⟨203390, by rfl⟩) R406781
theorem R338255 : Reach 338255 := rs (se 1 (by rfl) ⟨253691, by rfl⟩) R507383
theorem R108989 : Reach 108989 := rs (se 3 (by rfl) ⟨20435, by rfl⟩) R40871
theorem R43807 : Reach 43807 := rs (se 1 (by rfl) ⟨32855, by rfl⟩) R65711
theorem R79643 : Reach 79643 := rs (se 1 (by rfl) ⟨59732, by rfl⟩) R119465
theorem R243577 : Reach 243577 := rs (se 2 (by rfl) ⟨91341, by rfl⟩) R182683
theorem R80297 : Reach 80297 := rs (se 2 (by rfl) ⟨30111, by rfl⟩) R60223
theorem R179455 : Reach 179455 := rs (se 1 (by rfl) ⟨134591, by rfl⟩) R269183
theorem R507521 : Reach 507521 := rs (se 2 (by rfl) ⟨190320, by rfl⟩) R380641
theorem R81755 : Reach 81755 := rs (se 1 (by rfl) ⟨61316, by rfl⟩) R122633
theorem R245935 : Reach 245935 := rs (se 1 (by rfl) ⟨184451, by rfl⟩) R368903
theorem R378283 : Reach 378283 := rs (se 1 (by rfl) ⟨283712, by rfl⟩) R567425
theorem R83483 : Reach 83483 := rs (se 1 (by rfl) ⟨62612, by rfl⟩) R125225
theorem R118073 : Reach 118073 := rs (se 2 (by rfl) ⟨44277, by rfl⟩) R88555
theorem R413099 : Reach 413099 := rs (se 1 (by rfl) ⟨309824, by rfl⟩) R619649
theorem R118253 : Reach 118253 := rs (se 3 (by rfl) ⟨22172, by rfl⟩) R44345
theorem R52955 : Reach 52955 := rs (se 1 (by rfl) ⟨39716, by rfl⟩) R79433
theorem R250651 : Reach 250651 := rs (se 1 (by rfl) ⟨187988, by rfl⟩) R375977
theorem R54431 : Reach 54431 := rs (se 1 (by rfl) ⟨40823, by rfl⟩) R81647
theorem R87479 : Reach 87479 := rs (se 1 (by rfl) ⟨65609, by rfl⟩) R131219
theorem R55547 : Reach 55547 := rs (se 1 (by rfl) ⟨41660, by rfl⟩) R83321
theorem R55673 : Reach 55673 := rs (se 2 (by rfl) ⟨20877, by rfl⟩) R41755
theorem R252497 : Reach 252497 := rs (se 2 (by rfl) ⟨94686, by rfl⟩) R189373
theorem R23999 : Reach 23999 := rs (se 1 (by rfl) ⟨17999, by rfl⟩) R35999
theorem R24063 : Reach 24063 := rs (se 1 (by rfl) ⟨18047, by rfl⟩) R36095
theorem R220751 : Reach 220751 := rs (se 1 (by rfl) ⟨165563, by rfl⟩) R331127
theorem R155519 : Reach 155519 := rs (se 1 (by rfl) ⟨116639, by rfl⟩) R233279
theorem R221129 : Reach 221129 := rs (se 2 (by rfl) ⟨82923, by rfl⟩) R165847
theorem R286679 : Reach 286679 := rs (se 1 (by rfl) ⟨215009, by rfl⟩) R430019
theorem R123119 : Reach 123119 := rs (se 1 (by rfl) ⟨92339, by rfl⟩) R184679
theorem R25023 : Reach 25023 := rs (se 1 (by rfl) ⟨18767, by rfl⟩) R37535
theorem R25135 : Reach 25135 := rs (se 1 (by rfl) ⟨18851, by rfl⟩) R37703
theorem R25215 : Reach 25215 := rs (se 1 (by rfl) ⟨18911, by rfl⟩) R37823
theorem R25279 : Reach 25279 := rs (se 1 (by rfl) ⟨18959, by rfl⟩) R37919
theorem R387281 : Reach 387281 := rs (se 2 (by rfl) ⟨145230, by rfl⟩) R290461
theorem R125549 : Reach 125549 := rs (se 3 (by rfl) ⟨23540, by rfl⟩) R47081
theorem R27247 : Reach 27247 := rs (se 1 (by rfl) ⟨20435, by rfl⟩) R40871
theorem R60371 : Reach 60371 := rs (se 1 (by rfl) ⟨45278, by rfl⟩) R90557
theorem R15756743 : Reach 15756743 := rs (se 1 (by rfl) ⟨11817557, by rfl⟩) R23635115
theorem R60947 : Reach 60947 := rs (se 1 (by rfl) ⟨45710, by rfl⟩) R91421
theorem R63251 : Reach 63251 := rs (se 1 (by rfl) ⟨47438, by rfl⟩) R94877
theorem R96167 : Reach 96167 := rs (se 1 (by rfl) ⟨72125, by rfl⟩) R144251
theorem R1311653 : Reach 1311653 := rs (se 4 (by rfl) ⟨122967, by rfl⟩) R245935
theorem R67027 : Reach 67027 := rs (se 1 (by rfl) ⟨50270, by rfl⟩) R100541
theorem R35303 : Reach 35303 := rs (se 1 (by rfl) ⟨26477, by rfl⟩) R52955
theorem R265031 : Reach 265031 := rs (se 1 (by rfl) ⟨198773, by rfl⟩) R397547
theorem R36287 : Reach 36287 := rs (se 1 (by rfl) ⟨27215, by rfl⟩) R54431
theorem R36329 : Reach 36329 := rs (se 2 (by rfl) ⟨13623, by rfl⟩) R27247
theorem R37031 : Reach 37031 := rs (se 1 (by rfl) ⟨27773, by rfl⟩) R55547
theorem R37115 : Reach 37115 := rs (se 1 (by rfl) ⟨27836, by rfl⟩) R55673
theorem R168331 : Reach 168331 := rs (se 1 (by rfl) ⟨126248, by rfl⟩) R252497
theorem R103679 : Reach 103679 := rs (se 1 (by rfl) ⟨77759, by rfl⟩) R155519
theorem R334201 : Reach 334201 := rs (se 2 (by rfl) ⟨125325, by rfl⟩) R250651
theorem R72659 : Reach 72659 := rs (se 1 (by rfl) ⟨54494, by rfl⟩) R108989
theorem R40247 : Reach 40247 := rs (se 1 (by rfl) ⟨30185, by rfl⟩) R60371
theorem R40631 : Reach 40631 := rs (se 1 (by rfl) ⟨30473, by rfl⟩) R60947
theorem R42167 : Reach 42167 := rs (se 1 (by rfl) ⟨31625, by rfl⟩) R63251
theorem R239273 : Reach 239273 := rs (se 2 (by rfl) ⟨89727, by rfl⟩) R179455
theorem R338347 : Reach 338347 := rs (se 1 (by rfl) ⟨253760, by rfl⟩) R507521
theorem R44879 : Reach 44879 := rs (se 1 (by rfl) ⟨33659, by rfl⟩) R67319
theorem R504377 : Reach 504377 := rs (se 2 (by rfl) ⟨189141, by rfl⟩) R378283
theorem R78715 : Reach 78715 := rs (se 1 (by rfl) ⟨59036, by rfl⟩) R118073
theorem R275399 : Reach 275399 := rs (se 1 (by rfl) ⟨206549, by rfl⟩) R413099
theorem R78835 : Reach 78835 := rs (se 1 (by rfl) ⟨59126, by rfl⟩) R118253
theorem R46415 : Reach 46415 := rs (se 1 (by rfl) ⟨34811, by rfl⟩) R69623
theorem R212381 : Reach 212381 := rs (se 3 (by rfl) ⟨39821, by rfl⟩) R79643
theorem R114203 : Reach 114203 := rs (se 1 (by rfl) ⟨85652, by rfl⟩) R171305
theorem R147167 : Reach 147167 := rs (se 1 (by rfl) ⟨110375, by rfl⟩) R220751
theorem R147419 : Reach 147419 := rs (se 1 (by rfl) ⟨110564, by rfl⟩) R221129
theorem R82079 : Reach 82079 := rs (se 1 (by rfl) ⟨61559, by rfl⟩) R123119
theorem R180791 : Reach 180791 := rs (se 1 (by rfl) ⟨135593, by rfl⟩) R271187
theorem R83699 : Reach 83699 := rs (se 1 (by rfl) ⟨62774, by rfl⟩) R125549
theorem R10504495 : Reach 10504495 := rs (se 1 (by rfl) ⟨7878371, by rfl⟩) R15756743
theorem R53531 : Reach 53531 := rs (se 1 (by rfl) ⟨40148, by rfl⟩) R80297
theorem R54503 : Reach 54503 := rs (se 1 (by rfl) ⟨40877, by rfl⟩) R81755
theorem R87677 : Reach 87677 := rs (se 3 (by rfl) ⟨16439, by rfl⟩) R32879
theorem R88289 : Reach 88289 := rs (se 2 (by rfl) ⟨33108, by rfl⟩) R66217
theorem R55655 : Reach 55655 := rs (se 1 (by rfl) ⟨41741, by rfl⟩) R83483
theorem R23967 : Reach 23967 := rs (se 1 (by rfl) ⟨17975, by rfl⟩) R35951
theorem R24095 : Reach 24095 := rs (se 1 (by rfl) ⟨18071, by rfl⟩) R36143
theorem R90395 : Reach 90395 := rs (se 1 (by rfl) ⟨67796, by rfl⟩) R135593
theorem R58319 : Reach 58319 := rs (se 1 (by rfl) ⟨43739, by rfl⟩) R87479
theorem R25567 : Reach 25567 := rs (se 1 (by rfl) ⟨19175, by rfl⟩) R38351
theorem R58409 : Reach 58409 := rs (se 2 (by rfl) ⟨21903, by rfl⟩) R43807
theorem R944783 : Reach 944783 := rs (se 1 (by rfl) ⟨708587, by rfl⟩) R1417175
theorem R191119 : Reach 191119 := rs (se 1 (by rfl) ⟨143339, by rfl⟩) R286679
theorem R93449 : Reach 93449 := rs (se 2 (by rfl) ⟨35043, by rfl⟩) R70087
theorem R258187 : Reach 258187 := rs (se 1 (by rfl) ⟨193640, by rfl⟩) R387281
theorem R225503 : Reach 225503 := rs (se 1 (by rfl) ⟨169127, by rfl⟩) R338255
theorem R324769 : Reach 324769 := rs (se 2 (by rfl) ⟨121788, by rfl⟩) R243577
theorem R64111 : Reach 64111 := rs (se 1 (by rfl) ⟨48083, by rfl⟩) R96167
theorem R1804517 : Reach 1804517 := rs (se 4 (by rfl) ⟨169173, by rfl⟩) R338347
theorem R35687 : Reach 35687 := rs (se 1 (by rfl) ⟨26765, by rfl⟩) R53531
theorem R36335 : Reach 36335 := rs (se 1 (by rfl) ⟨27251, by rfl⟩) R54503
theorem R69119 : Reach 69119 := rs (se 1 (by rfl) ⟨51839, by rfl⟩) R103679
theorem R37103 : Reach 37103 := rs (se 1 (by rfl) ⟨27827, by rfl⟩) R55655
theorem R38879 : Reach 38879 := rs (se 1 (by rfl) ⟨29159, by rfl⟩) R58319
theorem R38939 : Reach 38939 := rs (se 1 (by rfl) ⟨29204, by rfl⟩) R58409
theorem R105113 : Reach 105113 := rs (se 2 (by rfl) ⟨39417, by rfl⟩) R78835
theorem R433025 : Reach 433025 := rs (se 2 (by rfl) ⟨162384, by rfl⟩) R324769
theorem R629855 : Reach 629855 := rs (se 1 (by rfl) ⟨472391, by rfl⟩) R944783
theorem R336251 : Reach 336251 := rs (se 1 (by rfl) ⟨252188, by rfl⟩) R504377
theorem R141587 : Reach 141587 := rs (se 1 (by rfl) ⟨106190, by rfl⟩) R212381
theorem R76135 : Reach 76135 := rs (se 1 (by rfl) ⟨57101, by rfl⟩) R114203
theorem R176687 : Reach 176687 := rs (se 1 (by rfl) ⟨132515, by rfl⟩) R265031
theorem R14005993 : Reach 14005993 := rs (se 2 (by rfl) ⟨5252247, by rfl⟩) R10504495
theorem R48439 : Reach 48439 := rs (se 1 (by rfl) ⟨36329, by rfl⟩) R72659
theorem R344249 : Reach 344249 := rs (se 2 (by rfl) ⟨129093, by rfl⟩) R258187
theorem R150335 : Reach 150335 := rs (se 1 (by rfl) ⟨112751, by rfl⟩) R225503
theorem R445601 : Reach 445601 := rs (se 2 (by rfl) ⟨167100, by rfl⟩) R334201
theorem R183599 : Reach 183599 := rs (se 1 (by rfl) ⟨137699, by rfl⟩) R275399
theorem R85481 : Reach 85481 := rs (se 2 (by rfl) ⟨32055, by rfl⟩) R64111
theorem R119677 : Reach 119677 := rs (se 3 (by rfl) ⟨22439, by rfl⟩) R44879
theorem R54719 : Reach 54719 := rs (se 1 (by rfl) ⟨41039, by rfl⟩) R82079
theorem R120527 : Reach 120527 := rs (se 1 (by rfl) ⟨90395, by rfl⟩) R180791
theorem R874435 : Reach 874435 := rs (se 1 (by rfl) ⟨655826, by rfl⟩) R1311653
theorem R55799 : Reach 55799 := rs (se 1 (by rfl) ⟨41849, by rfl⟩) R83699
theorem R23535 : Reach 23535 := rs (se 1 (by rfl) ⟨17651, by rfl⟩) R35303
theorem R89369 : Reach 89369 := rs (se 2 (by rfl) ⟨33513, by rfl⟩) R67027
theorem R24191 : Reach 24191 := rs (se 1 (by rfl) ⟨18143, by rfl⟩) R36287
theorem R24219 : Reach 24219 := rs (se 1 (by rfl) ⟨18164, by rfl⟩) R36329
theorem R24687 : Reach 24687 := rs (se 1 (by rfl) ⟨18515, by rfl⟩) R37031
theorem R24743 : Reach 24743 := rs (se 1 (by rfl) ⟨18557, by rfl⟩) R37115
theorem R254825 : Reach 254825 := rs (se 2 (by rfl) ⟨95559, by rfl⟩) R191119
theorem R58451 : Reach 58451 := rs (se 1 (by rfl) ⟨43838, by rfl⟩) R87677
theorem R58859 : Reach 58859 := rs (se 1 (by rfl) ⟨44144, by rfl⟩) R88289
theorem R419813 : Reach 419813 := rs (se 4 (by rfl) ⟨39357, by rfl⟩) R78715
theorem R26831 : Reach 26831 := rs (se 1 (by rfl) ⟨20123, by rfl⟩) R40247
theorem R27087 : Reach 27087 := rs (se 1 (by rfl) ⟨20315, by rfl⟩) R40631
theorem R60263 : Reach 60263 := rs (se 1 (by rfl) ⟨45197, by rfl⟩) R90395
theorem R224441 : Reach 224441 := rs (se 2 (by rfl) ⟨84165, by rfl⟩) R168331
theorem R28111 : Reach 28111 := rs (se 1 (by rfl) ⟨21083, by rfl⟩) R42167
theorem R159515 : Reach 159515 := rs (se 1 (by rfl) ⟨119636, by rfl⟩) R239273
theorem R62299 : Reach 62299 := rs (se 1 (by rfl) ⟨46724, by rfl⟩) R93449
theorem R30943 : Reach 30943 := rs (se 1 (by rfl) ⟨23207, by rfl⟩) R46415
theorem R64253 : Reach 64253 := rs (se 3 (by rfl) ⟨12047, by rfl⟩) R24095
theorem R98111 : Reach 98111 := rs (se 1 (by rfl) ⟨73583, by rfl⟩) R147167
theorem R98279 : Reach 98279 := rs (se 1 (by rfl) ⟨73709, by rfl⟩) R147419
theorem R229499 : Reach 229499 := rs (se 1 (by rfl) ⟨172124, by rfl⟩) R344249
theorem R623477 : Reach 623477 := rs (se 5 (by rfl) ⟨29225, by rfl⟩) R58451
theorem R100223 : Reach 100223 := rs (se 1 (by rfl) ⟨75167, by rfl⟩) R150335
theorem R297067 : Reach 297067 := rs (se 1 (by rfl) ⟨222800, by rfl⟩) R445601
theorem R101513 : Reach 101513 := rs (se 2 (by rfl) ⟨38067, by rfl⟩) R76135
theorem R36479 : Reach 36479 := rs (se 1 (by rfl) ⟨27359, by rfl⟩) R54719
theorem R37199 : Reach 37199 := rs (se 1 (by rfl) ⟨27899, by rfl⟩) R55799
theorem R70075 : Reach 70075 := rs (se 1 (by rfl) ⟨52556, by rfl⟩) R105113
theorem R37481 : Reach 37481 := rs (se 2 (by rfl) ⟨14055, by rfl⟩) R28111
theorem R169883 : Reach 169883 := rs (se 1 (by rfl) ⟨127412, by rfl⟩) R254825
theorem R39239 : Reach 39239 := rs (se 1 (by rfl) ⟨29429, by rfl⟩) R58859
theorem R40175 : Reach 40175 := rs (se 1 (by rfl) ⟨30131, by rfl⟩) R60263
theorem R106343 : Reach 106343 := rs (se 1 (by rfl) ⟨79757, by rfl⟩) R159515
theorem R41257 : Reach 41257 := rs (se 2 (by rfl) ⟨15471, by rfl⟩) R30943
theorem R42835 : Reach 42835 := rs (se 1 (by rfl) ⟨32126, by rfl⟩) R64253
theorem R46079 : Reach 46079 := rs (se 1 (by rfl) ⟨34559, by rfl⟩) R69119
theorem R80351 : Reach 80351 := rs (se 1 (by rfl) ⟨60263, by rfl⟩) R120527
theorem R83065 : Reach 83065 := rs (se 2 (by rfl) ⟨31149, by rfl⟩) R62299
theorem R279875 : Reach 279875 := rs (se 1 (by rfl) ⟨209906, by rfl⟩) R419813
theorem R149627 : Reach 149627 := rs (se 1 (by rfl) ⟨112220, by rfl⟩) R224441
theorem R1165913 : Reach 1165913 := rs (se 2 (by rfl) ⟨437217, by rfl⟩) R874435
theorem R117791 : Reach 117791 := rs (se 1 (by rfl) ⟨88343, by rfl⟩) R176687
theorem R1203011 : Reach 1203011 := rs (se 1 (by rfl) ⟨902258, by rfl⟩) R1804517
theorem R23791 : Reach 23791 := rs (se 1 (by rfl) ⟨17843, by rfl⟩) R35687
theorem R122399 : Reach 122399 := rs (se 1 (by rfl) ⟨91799, by rfl⟩) R183599
theorem R56987 : Reach 56987 := rs (se 1 (by rfl) ⟨42740, by rfl⟩) R85481
theorem R24223 : Reach 24223 := rs (se 1 (by rfl) ⟨18167, by rfl⟩) R36335
theorem R24735 : Reach 24735 := rs (se 1 (by rfl) ⟨18551, by rfl⟩) R37103
theorem R25919 : Reach 25919 := rs (se 1 (by rfl) ⟨19439, by rfl⟩) R38879
theorem R25959 : Reach 25959 := rs (se 1 (by rfl) ⟨19469, by rfl⟩) R38939
theorem R288683 : Reach 288683 := rs (se 1 (by rfl) ⟨216512, by rfl⟩) R433025
theorem R419903 : Reach 419903 := rs (se 1 (by rfl) ⟨314927, by rfl⟩) R629855
theorem R59579 : Reach 59579 := rs (se 1 (by rfl) ⟨44684, by rfl⟩) R89369
theorem R224167 : Reach 224167 := rs (se 1 (by rfl) ⟨168125, by rfl⟩) R336251
theorem R159569 : Reach 159569 := rs (se 2 (by rfl) ⟨59838, by rfl⟩) R119677
theorem R94391 : Reach 94391 := rs (se 1 (by rfl) ⟨70793, by rfl⟩) R141587
theorem R95165 : Reach 95165 := rs (se 3 (by rfl) ⟨17843, by rfl⟩) R35687
theorem R18674657 : Reach 18674657 := rs (se 2 (by rfl) ⟨7002996, by rfl⟩) R14005993
theorem R64585 : Reach 64585 := rs (se 2 (by rfl) ⟨24219, by rfl⟩) R48439
theorem R65407 : Reach 65407 := rs (se 1 (by rfl) ⟨49055, by rfl⟩) R98111
theorem R65519 : Reach 65519 := rs (se 1 (by rfl) ⟨49139, by rfl⟩) R98279
theorem R66815 : Reach 66815 := rs (se 1 (by rfl) ⟨50111, by rfl⟩) R100223
theorem R99751 : Reach 99751 := rs (se 1 (by rfl) ⟨74813, by rfl⟩) R149627
theorem R67675 : Reach 67675 := rs (se 1 (by rfl) ⟨50756, by rfl⟩) R101513
theorem R396089 : Reach 396089 := rs (se 2 (by rfl) ⟨148533, by rfl⟩) R297067
theorem R298889 : Reach 298889 := rs (se 2 (by rfl) ⟨112083, by rfl⟩) R224167
theorem R37991 : Reach 37991 := rs (se 1 (by rfl) ⟨28493, by rfl⟩) R56987
theorem R70895 : Reach 70895 := rs (se 1 (by rfl) ⟨53171, by rfl⟩) R106343
theorem R39719 : Reach 39719 := rs (se 1 (by rfl) ⟨29789, by rfl⟩) R59579
theorem R106379 : Reach 106379 := rs (se 1 (by rfl) ⟨79784, by rfl⟩) R159569
theorem R43679 : Reach 43679 := rs (se 1 (by rfl) ⟨32759, by rfl⟩) R65519
theorem R110753 : Reach 110753 := rs (se 2 (by rfl) ⟨41532, by rfl⟩) R83065
theorem R78527 : Reach 78527 := rs (se 1 (by rfl) ⟨58895, by rfl⟩) R117791
theorem R113255 : Reach 113255 := rs (se 1 (by rfl) ⟨84941, by rfl⟩) R169883
theorem R802007 : Reach 802007 := rs (se 1 (by rfl) ⟨601505, by rfl⟩) R1203011
theorem R81599 : Reach 81599 := rs (se 1 (by rfl) ⟨61199, by rfl⟩) R122399
theorem R279935 : Reach 279935 := rs (se 1 (by rfl) ⟨209951, by rfl⟩) R419903
theorem R86113 : Reach 86113 := rs (se 2 (by rfl) ⟨32292, by rfl⟩) R64585
theorem R53567 : Reach 53567 := rs (se 1 (by rfl) ⟨40175, by rfl⟩) R80351
theorem R87209 : Reach 87209 := rs (se 2 (by rfl) ⟨32703, by rfl⟩) R65407
theorem R152999 : Reach 152999 := rs (se 1 (by rfl) ⟨114749, by rfl⟩) R229499
theorem R55009 : Reach 55009 := rs (se 2 (by rfl) ⟨20628, by rfl⟩) R41257
theorem R415651 : Reach 415651 := rs (se 1 (by rfl) ⟨311738, by rfl⟩) R623477
theorem R186583 : Reach 186583 := rs (se 1 (by rfl) ⟨139937, by rfl⟩) R279875
theorem R777275 : Reach 777275 := rs (se 1 (by rfl) ⟨582956, by rfl⟩) R1165913
theorem R24319 : Reach 24319 := rs (se 1 (by rfl) ⟨18239, by rfl⟩) R36479
theorem R57113 : Reach 57113 := rs (se 2 (by rfl) ⟨21417, by rfl⟩) R42835
theorem R24799 : Reach 24799 := rs (se 1 (by rfl) ⟨18599, by rfl⟩) R37199
theorem R24987 : Reach 24987 := rs (se 1 (by rfl) ⟨18740, by rfl⟩) R37481
theorem R26159 : Reach 26159 := rs (se 1 (by rfl) ⟨19619, by rfl⟩) R39239
theorem R26783 : Reach 26783 := rs (se 1 (by rfl) ⟨20087, by rfl⟩) R40175
theorem R93433 : Reach 93433 := rs (se 2 (by rfl) ⟨35037, by rfl⟩) R70075
theorem R192455 : Reach 192455 := rs (se 1 (by rfl) ⟨144341, by rfl⟩) R288683
theorem R62927 : Reach 62927 := rs (se 1 (by rfl) ⟨47195, by rfl⟩) R94391
theorem R63443 : Reach 63443 := rs (se 1 (by rfl) ⟨47582, by rfl⟩) R95165
theorem R12449771 : Reach 12449771 := rs (se 1 (by rfl) ⟨9337328, by rfl⟩) R18674657
theorem R30719 : Reach 30719 := rs (se 1 (by rfl) ⟨23039, by rfl⟩) R46079
theorem R459269 : Reach 459269 := rs (se 4 (by rfl) ⟨43056, by rfl⟩) R86113
theorem R264059 : Reach 264059 := rs (se 1 (by rfl) ⟨198044, by rfl⟩) R396089
theorem R133001 : Reach 133001 := rs (se 2 (by rfl) ⟨49875, by rfl⟩) R99751
theorem R199259 : Reach 199259 := rs (se 1 (by rfl) ⟨149444, by rfl⟩) R298889
theorem R35711 : Reach 35711 := rs (se 1 (by rfl) ⟨26783, by rfl⟩) R53567
theorem R101999 : Reach 101999 := rs (se 1 (by rfl) ⟨76499, by rfl⟩) R152999
theorem R38075 : Reach 38075 := rs (se 1 (by rfl) ⟨28556, by rfl⟩) R57113
theorem R70919 : Reach 70919 := rs (se 1 (by rfl) ⟨53189, by rfl⟩) R106379
theorem R73345 : Reach 73345 := rs (se 2 (by rfl) ⟨27504, by rfl⟩) R55009
theorem R73835 : Reach 73835 := rs (se 1 (by rfl) ⟨55376, by rfl⟩) R110753
theorem R41951 : Reach 41951 := rs (se 1 (by rfl) ⟨31463, by rfl⟩) R62927
theorem R42295 : Reach 42295 := rs (se 1 (by rfl) ⟨31721, by rfl⟩) R63443
theorem R8299847 : Reach 8299847 := rs (se 1 (by rfl) ⟨6224885, by rfl⟩) R12449771
theorem R75503 : Reach 75503 := rs (se 1 (by rfl) ⟨56627, by rfl⟩) R113255
theorem R534671 : Reach 534671 := rs (se 1 (by rfl) ⟨401003, by rfl⟩) R802007
theorem R44543 : Reach 44543 := rs (se 1 (by rfl) ⟨33407, by rfl⟩) R66815
theorem R209405 : Reach 209405 := rs (se 3 (by rfl) ⟨39263, by rfl⟩) R78527
theorem R81917 : Reach 81917 := rs (se 3 (by rfl) ⟨15359, by rfl⟩) R30719
theorem R870389 : Reach 870389 := rs (se 5 (by rfl) ⟨40799, by rfl⟩) R81599
theorem R248777 : Reach 248777 := rs (se 2 (by rfl) ⟨93291, by rfl⟩) R186583
theorem R186623 : Reach 186623 := rs (se 1 (by rfl) ⟨139967, by rfl⟩) R279935
theorem R90233 : Reach 90233 := rs (se 2 (by rfl) ⟨33837, by rfl⟩) R67675
theorem R189053 : Reach 189053 := rs (se 3 (by rfl) ⟨35447, by rfl⟩) R70895
theorem R25327 : Reach 25327 := rs (se 1 (by rfl) ⟨18995, by rfl⟩) R37991
theorem R58139 : Reach 58139 := rs (se 1 (by rfl) ⟨43604, by rfl⟩) R87209
theorem R124577 : Reach 124577 := rs (se 2 (by rfl) ⟨46716, by rfl⟩) R93433
theorem R26479 : Reach 26479 := rs (se 1 (by rfl) ⟨19859, by rfl⟩) R39719
theorem R518183 : Reach 518183 := rs (se 1 (by rfl) ⟨388637, by rfl⟩) R777275
theorem R29119 : Reach 29119 := rs (se 1 (by rfl) ⟨21839, by rfl⟩) R43679
theorem R554201 : Reach 554201 := rs (se 2 (by rfl) ⟨207825, by rfl⟩) R415651
theorem R128303 : Reach 128303 := rs (se 1 (by rfl) ⟨96227, by rfl⟩) R192455
theorem R132839 : Reach 132839 := rs (se 1 (by rfl) ⟨99629, by rfl⟩) R199259
theorem R165851 : Reach 165851 := rs (se 1 (by rfl) ⟨124388, by rfl⟩) R248777
theorem R67999 : Reach 67999 := rs (se 1 (by rfl) ⟨50999, by rfl⟩) R101999
theorem R201341 : Reach 201341 := rs (se 3 (by rfl) ⟨37751, by rfl⟩) R75503
theorem R38759 : Reach 38759 := rs (se 1 (by rfl) ⟨29069, by rfl⟩) R58139
theorem R38825 : Reach 38825 := rs (se 2 (by rfl) ⟨14559, by rfl⟩) R29119
theorem R139603 : Reach 139603 := rs (se 1 (by rfl) ⟨104702, by rfl⟩) R209405
theorem R369467 : Reach 369467 := rs (se 1 (by rfl) ⟨277100, by rfl⟩) R554201
theorem R306179 : Reach 306179 := rs (se 1 (by rfl) ⟨229634, by rfl⟩) R459269
theorem R176039 : Reach 176039 := rs (se 1 (by rfl) ⟨132029, by rfl⟩) R264059
theorem R47279 : Reach 47279 := rs (se 1 (by rfl) ⟨35459, by rfl⟩) R70919
theorem R49223 : Reach 49223 := rs (se 1 (by rfl) ⟨36917, by rfl⟩) R73835
theorem R83051 : Reach 83051 := rs (se 1 (by rfl) ⟨62288, by rfl⟩) R124577
theorem R345455 : Reach 345455 := rs (se 1 (by rfl) ⟨259091, by rfl⟩) R518183
theorem R85535 : Reach 85535 := rs (se 1 (by rfl) ⟨64151, by rfl⟩) R128303
theorem R54611 : Reach 54611 := rs (se 1 (by rfl) ⟨40958, by rfl⟩) R81917
theorem R88667 : Reach 88667 := rs (se 1 (by rfl) ⟨66500, by rfl⟩) R133001
theorem R580259 : Reach 580259 := rs (se 1 (by rfl) ⟨435194, by rfl⟩) R870389
theorem R56393 : Reach 56393 := rs (se 2 (by rfl) ⟨21147, by rfl⟩) R42295
theorem R23807 : Reach 23807 := rs (se 1 (by rfl) ⟨17855, by rfl⟩) R35711
theorem R25383 : Reach 25383 := rs (se 1 (by rfl) ⟨19037, by rfl⟩) R38075
theorem R124415 : Reach 124415 := rs (se 1 (by rfl) ⟨93311, by rfl⟩) R186623
theorem R60155 : Reach 60155 := rs (se 1 (by rfl) ⟨45116, by rfl⟩) R90233
theorem R126035 : Reach 126035 := rs (se 1 (by rfl) ⟨94526, by rfl⟩) R189053
theorem R27967 : Reach 27967 := rs (se 1 (by rfl) ⟨20975, by rfl⟩) R41951
theorem R5533231 : Reach 5533231 := rs (se 1 (by rfl) ⟨4149923, by rfl⟩) R8299847
theorem R356447 : Reach 356447 := rs (se 1 (by rfl) ⟨267335, by rfl⟩) R534671
theorem R29695 : Reach 29695 := rs (se 1 (by rfl) ⟨22271, by rfl⟩) R44543
theorem R97793 : Reach 97793 := rs (se 2 (by rfl) ⟨36672, by rfl⟩) R73345
theorem R32815 : Reach 32815 := rs (se 1 (by rfl) ⟨24611, by rfl⟩) R49223
theorem R950525 : Reach 950525 := rs (se 3 (by rfl) ⟨178223, by rfl⟩) R356447
theorem R230303 : Reach 230303 := rs (se 1 (by rfl) ⟨172727, by rfl⟩) R345455
theorem R134227 : Reach 134227 := rs (se 1 (by rfl) ⟨100670, by rfl⟩) R201341
theorem R36407 : Reach 36407 := rs (se 1 (by rfl) ⟨27305, by rfl⟩) R54611
theorem R37289 : Reach 37289 := rs (se 2 (by rfl) ⟨13983, by rfl⟩) R27967
theorem R37595 : Reach 37595 := rs (se 1 (by rfl) ⟨28196, by rfl⟩) R56393
theorem R7377641 : Reach 7377641 := rs (se 2 (by rfl) ⟨2766615, by rfl⟩) R5533231
theorem R39593 : Reach 39593 := rs (se 2 (by rfl) ⟨14847, by rfl⟩) R29695
theorem R40103 : Reach 40103 := rs (se 1 (by rfl) ⟨30077, by rfl⟩) R60155
theorem R204119 : Reach 204119 := rs (se 1 (by rfl) ⟨153089, by rfl⟩) R306179
theorem R110567 : Reach 110567 := rs (se 1 (by rfl) ⟨82925, by rfl⟩) R165851
theorem R246311 : Reach 246311 := rs (se 1 (by rfl) ⟨184733, by rfl⟩) R369467
theorem R82943 : Reach 82943 := rs (se 1 (by rfl) ⟨62207, by rfl⟩) R124415
theorem R84023 : Reach 84023 := rs (se 1 (by rfl) ⟨63017, by rfl⟩) R126035
theorem R117359 : Reach 117359 := rs (se 1 (by rfl) ⟨88019, by rfl⟩) R176039
theorem R186137 : Reach 186137 := rs (se 2 (by rfl) ⟨69801, by rfl⟩) R139603
theorem R55367 : Reach 55367 := rs (se 1 (by rfl) ⟨41525, by rfl⟩) R83051
theorem R88559 : Reach 88559 := rs (se 1 (by rfl) ⟨66419, by rfl⟩) R132839
theorem R57023 : Reach 57023 := rs (se 1 (by rfl) ⟨42767, by rfl⟩) R85535
theorem R90665 : Reach 90665 := rs (se 2 (by rfl) ⟨33999, by rfl⟩) R67999
theorem R25839 : Reach 25839 := rs (se 1 (by rfl) ⟨19379, by rfl⟩) R38759
theorem R25883 : Reach 25883 := rs (se 1 (by rfl) ⟨19412, by rfl⟩) R38825
theorem R59111 : Reach 59111 := rs (se 1 (by rfl) ⟨44333, by rfl⟩) R88667
theorem R386839 : Reach 386839 := rs (se 1 (by rfl) ⟨290129, by rfl⟩) R580259
theorem R31519 : Reach 31519 := rs (se 1 (by rfl) ⟨23639, by rfl⟩) R47279
theorem R65195 : Reach 65195 := rs (se 1 (by rfl) ⟨48896, by rfl⟩) R97793
theorem R164207 : Reach 164207 := rs (se 1 (by rfl) ⟨123155, by rfl⟩) R246311
theorem R4918427 : Reach 4918427 := rs (se 1 (by rfl) ⟨3688820, by rfl⟩) R7377641
theorem R36911 : Reach 36911 := rs (se 1 (by rfl) ⟨27683, by rfl⟩) R55367
theorem R136079 : Reach 136079 := rs (se 1 (by rfl) ⟨102059, by rfl⟩) R204119
theorem R38015 : Reach 38015 := rs (se 1 (by rfl) ⟨28511, by rfl⟩) R57023
theorem R39407 : Reach 39407 := rs (se 1 (by rfl) ⟨29555, by rfl⟩) R59111
theorem R73711 : Reach 73711 := rs (se 1 (by rfl) ⟨55283, by rfl⟩) R110567
theorem R42025 : Reach 42025 := rs (se 2 (by rfl) ⟨15759, by rfl⟩) R31519
theorem R43463 : Reach 43463 := rs (se 1 (by rfl) ⟨32597, by rfl⟩) R65195
theorem R43753 : Reach 43753 := rs (se 2 (by rfl) ⟨16407, by rfl⟩) R32815
theorem R633683 : Reach 633683 := rs (se 1 (by rfl) ⟨475262, by rfl⟩) R950525
theorem R78239 : Reach 78239 := rs (se 1 (by rfl) ⟨58679, by rfl⟩) R117359
theorem R178969 : Reach 178969 := rs (se 2 (by rfl) ⟨67113, by rfl⟩) R134227
theorem R153535 : Reach 153535 := rs (se 1 (by rfl) ⟨115151, by rfl⟩) R230303
theorem R55295 : Reach 55295 := rs (se 1 (by rfl) ⟨41471, by rfl⟩) R82943
theorem R56015 : Reach 56015 := rs (se 1 (by rfl) ⟨42011, by rfl⟩) R84023
theorem R24271 : Reach 24271 := rs (se 1 (by rfl) ⟨18203, by rfl⟩) R36407
theorem R24859 : Reach 24859 := rs (se 1 (by rfl) ⟨18644, by rfl⟩) R37289
theorem R25063 : Reach 25063 := rs (se 1 (by rfl) ⟨18797, by rfl⟩) R37595
theorem R124091 : Reach 124091 := rs (se 1 (by rfl) ⟨93068, by rfl⟩) R186137
theorem R59039 : Reach 59039 := rs (se 1 (by rfl) ⟨44279, by rfl⟩) R88559
theorem R26395 : Reach 26395 := rs (se 1 (by rfl) ⟨19796, by rfl⟩) R39593
theorem R26735 : Reach 26735 := rs (se 1 (by rfl) ⟨20051, by rfl⟩) R40103
theorem R60443 : Reach 60443 := rs (se 1 (by rfl) ⟨45332, by rfl⟩) R90665
theorem R2063141 : Reach 2063141 := rs (se 4 (by rfl) ⟨193419, by rfl⟩) R386839
theorem R3278951 : Reach 3278951 := rs (se 1 (by rfl) ⟨2459213, by rfl⟩) R4918427
theorem R36863 : Reach 36863 := rs (se 1 (by rfl) ⟨27647, by rfl⟩) R55295
theorem R37343 : Reach 37343 := rs (se 1 (by rfl) ⟨28007, by rfl⟩) R56015
theorem R39359 : Reach 39359 := rs (se 1 (by rfl) ⟨29519, by rfl⟩) R59039
theorem R40295 : Reach 40295 := rs (se 1 (by rfl) ⟨30221, by rfl⟩) R60443
theorem R204713 : Reach 204713 := rs (se 2 (by rfl) ⟨76767, by rfl⟩) R153535
theorem R238625 : Reach 238625 := rs (se 2 (by rfl) ⟨89484, by rfl⟩) R178969
theorem R109471 : Reach 109471 := rs (se 1 (by rfl) ⟨82103, by rfl⟩) R164207
theorem R82727 : Reach 82727 := rs (se 1 (by rfl) ⟨62045, by rfl⟩) R124091
theorem R115901 : Reach 115901 := rs (se 3 (by rfl) ⟨21731, by rfl⟩) R43463
theorem R1689821 : Reach 1689821 := rs (se 3 (by rfl) ⟨316841, by rfl⟩) R633683
theorem R52159 : Reach 52159 := rs (se 1 (by rfl) ⟨39119, by rfl⟩) R78239
theorem R56033 : Reach 56033 := rs (se 2 (by rfl) ⟨21012, by rfl⟩) R42025
theorem R24607 : Reach 24607 := rs (se 1 (by rfl) ⟨18455, by rfl⟩) R36911
theorem R90719 : Reach 90719 := rs (se 1 (by rfl) ⟨68039, by rfl⟩) R136079
theorem R25343 : Reach 25343 := rs (se 1 (by rfl) ⟨19007, by rfl⟩) R38015
theorem R58337 : Reach 58337 := rs (se 2 (by rfl) ⟨21876, by rfl⟩) R43753
theorem R26271 : Reach 26271 := rs (se 1 (by rfl) ⟨19703, by rfl⟩) R39407
theorem R28975 : Reach 28975 := rs (se 1 (by rfl) ⟨21731, by rfl⟩) R43463
theorem R1375427 : Reach 1375427 := rs (se 1 (by rfl) ⟨1031570, by rfl⟩) R2063141
theorem R98281 : Reach 98281 := rs (se 2 (by rfl) ⟨36855, by rfl⟩) R73711
theorem R69545 : Reach 69545 := rs (se 2 (by rfl) ⟨26079, by rfl⟩) R52159
theorem R37355 : Reach 37355 := rs (se 1 (by rfl) ⟨28016, by rfl⟩) R56033
theorem R136475 : Reach 136475 := rs (se 1 (by rfl) ⟨102356, by rfl⟩) R204713
theorem R38633 : Reach 38633 := rs (se 2 (by rfl) ⟨14487, by rfl⟩) R28975
theorem R38891 : Reach 38891 := rs (se 1 (by rfl) ⟨29168, by rfl⟩) R58337
theorem R77267 : Reach 77267 := rs (se 1 (by rfl) ⟨57950, by rfl⟩) R115901
theorem R1126547 : Reach 1126547 := rs (se 1 (by rfl) ⟨844910, by rfl⟩) R1689821
theorem R145961 : Reach 145961 := rs (se 2 (by rfl) ⟨54735, by rfl⟩) R109471
theorem R55151 : Reach 55151 := rs (se 1 (by rfl) ⟨41363, by rfl⟩) R82727
theorem R2185967 : Reach 2185967 := rs (se 1 (by rfl) ⟨1639475, by rfl⟩) R3278951
theorem R24575 : Reach 24575 := rs (se 1 (by rfl) ⟨18431, by rfl⟩) R36863
theorem R24895 : Reach 24895 := rs (se 1 (by rfl) ⟨18671, by rfl⟩) R37343
theorem R26239 : Reach 26239 := rs (se 1 (by rfl) ⟨19679, by rfl⟩) R39359
theorem R26863 : Reach 26863 := rs (se 1 (by rfl) ⟨20147, by rfl⟩) R40295
theorem R60479 : Reach 60479 := rs (se 1 (by rfl) ⟨45359, by rfl⟩) R90719
theorem R159083 : Reach 159083 := rs (se 1 (by rfl) ⟨119312, by rfl⟩) R238625
theorem R3667805 : Reach 3667805 := rs (se 3 (by rfl) ⟨687713, by rfl⟩) R1375427
theorem R131041 : Reach 131041 := rs (se 2 (by rfl) ⟨49140, by rfl⟩) R98281
theorem R36767 : Reach 36767 := rs (se 1 (by rfl) ⟨27575, by rfl⟩) R55151
theorem R40319 : Reach 40319 := rs (se 1 (by rfl) ⟨30239, by rfl⟩) R60479
theorem R106055 : Reach 106055 := rs (se 1 (by rfl) ⟨79541, by rfl⟩) R159083
theorem R174721 : Reach 174721 := rs (se 2 (by rfl) ⟨65520, by rfl⟩) R131041
theorem R46363 : Reach 46363 := rs (se 1 (by rfl) ⟨34772, by rfl⟩) R69545
theorem R51511 : Reach 51511 := rs (se 1 (by rfl) ⟨38633, by rfl⟩) R77267
theorem R2445203 : Reach 2445203 := rs (se 1 (by rfl) ⟨1833902, by rfl⟩) R3667805
theorem R24903 : Reach 24903 := rs (se 1 (by rfl) ⟨18677, by rfl⟩) R37355
theorem R90983 : Reach 90983 := rs (se 1 (by rfl) ⟨68237, by rfl⟩) R136475
theorem R25755 : Reach 25755 := rs (se 1 (by rfl) ⟨19316, by rfl⟩) R38633
theorem R25927 : Reach 25927 := rs (se 1 (by rfl) ⟨19445, by rfl⟩) R38891
theorem R5829245 : Reach 5829245 := rs (se 3 (by rfl) ⟨1092983, by rfl⟩) R2185967
theorem R751031 : Reach 751031 := rs (se 1 (by rfl) ⟨563273, by rfl⟩) R1126547
theorem R97307 : Reach 97307 := rs (se 1 (by rfl) ⟨72980, by rfl⟩) R145961
theorem R68681 : Reach 68681 := rs (se 2 (by rfl) ⟨25755, by rfl⟩) R51511
theorem R232961 : Reach 232961 := rs (se 2 (by rfl) ⟨87360, by rfl⟩) R174721
theorem R70703 : Reach 70703 := rs (se 1 (by rfl) ⟨53027, by rfl⟩) R106055
theorem R500687 : Reach 500687 := rs (se 1 (by rfl) ⟨375515, by rfl⟩) R751031
theorem R242621 : Reach 242621 := rs (se 3 (by rfl) ⟨45491, by rfl⟩) R90983
theorem R3886163 : Reach 3886163 := rs (se 1 (by rfl) ⟨2914622, by rfl⟩) R5829245
theorem R1630135 : Reach 1630135 := rs (se 1 (by rfl) ⟨1222601, by rfl⟩) R2445203
theorem R24511 : Reach 24511 := rs (se 1 (by rfl) ⟨18383, by rfl⟩) R36767
theorem R26879 : Reach 26879 := rs (se 1 (by rfl) ⟨20159, by rfl⟩) R40319
theorem R61817 : Reach 61817 := rs (se 2 (by rfl) ⟨23181, by rfl⟩) R46363
theorem R64871 : Reach 64871 := rs (se 1 (by rfl) ⟨48653, by rfl⟩) R97307
theorem R164845 : Reach 164845 := rs (se 3 (by rfl) ⟨30908, by rfl⟩) R61817
theorem R2590775 : Reach 2590775 := rs (se 1 (by rfl) ⟨1943081, by rfl⟩) R3886163
theorem R333791 : Reach 333791 := rs (se 1 (by rfl) ⟨250343, by rfl⟩) R500687
theorem R43247 : Reach 43247 := rs (se 1 (by rfl) ⟨32435, by rfl⟩) R64871
theorem R2173513 : Reach 2173513 := rs (se 2 (by rfl) ⟨815067, by rfl⟩) R1630135
theorem R45787 : Reach 45787 := rs (se 1 (by rfl) ⟨34340, by rfl⟩) R68681
theorem R47135 : Reach 47135 := rs (se 1 (by rfl) ⟨35351, by rfl⟩) R70703
theorem R161747 : Reach 161747 := rs (se 1 (by rfl) ⟨121310, by rfl⟩) R242621
theorem R621229 : Reach 621229 := rs (se 3 (by rfl) ⟨116480, by rfl⟩) R232961
theorem R828305 : Reach 828305 := rs (se 2 (by rfl) ⟨310614, by rfl⟩) R621229
theorem R107831 : Reach 107831 := rs (se 1 (by rfl) ⟨80873, by rfl⟩) R161747
theorem R2898017 : Reach 2898017 := rs (se 2 (by rfl) ⟨1086756, by rfl⟩) R2173513
theorem R219793 : Reach 219793 := rs (se 2 (by rfl) ⟨82422, by rfl⟩) R164845
theorem R1727183 : Reach 1727183 := rs (se 1 (by rfl) ⟨1295387, by rfl⟩) R2590775
theorem R222527 : Reach 222527 := rs (se 1 (by rfl) ⟨166895, by rfl⟩) R333791
theorem R879173 : Reach 879173 := rs (se 4 (by rfl) ⟨82422, by rfl⟩) R164845
theorem R61049 : Reach 61049 := rs (se 2 (by rfl) ⟨22893, by rfl⟩) R45787
theorem R28831 : Reach 28831 := rs (se 1 (by rfl) ⟨21623, by rfl⟩) R43247
theorem R31423 : Reach 31423 := rs (se 1 (by rfl) ⟨23567, by rfl⟩) R47135
theorem R1151455 : Reach 1151455 := rs (se 1 (by rfl) ⟨863591, by rfl⟩) R1727183
theorem R38441 : Reach 38441 := rs (se 2 (by rfl) ⟨14415, by rfl⟩) R28831
theorem R71887 : Reach 71887 := rs (se 1 (by rfl) ⟨53915, by rfl⟩) R107831
theorem R40699 : Reach 40699 := rs (se 1 (by rfl) ⟨30524, by rfl⟩) R61049
theorem R41897 : Reach 41897 := rs (se 2 (by rfl) ⟨15711, by rfl⟩) R31423
theorem R148351 : Reach 148351 := rs (se 1 (by rfl) ⟨111263, by rfl⟩) R222527
theorem R552203 : Reach 552203 := rs (se 1 (by rfl) ⟨414152, by rfl⟩) R828305
theorem R586115 : Reach 586115 := rs (se 1 (by rfl) ⟨439586, by rfl⟩) R879173
theorem R293057 : Reach 293057 := rs (se 2 (by rfl) ⟨109896, by rfl⟩) R219793
theorem R1932011 : Reach 1932011 := rs (se 1 (by rfl) ⟨1449008, by rfl⟩) R2898017
theorem R197801 : Reach 197801 := rs (se 2 (by rfl) ⟨74175, by rfl⟩) R148351
theorem R368135 : Reach 368135 := rs (se 1 (by rfl) ⟨276101, by rfl⟩) R552203
theorem R1288007 : Reach 1288007 := rs (se 1 (by rfl) ⟨966005, by rfl⟩) R1932011
theorem R54265 : Reach 54265 := rs (se 2 (by rfl) ⟨20349, by rfl⟩) R40699
theorem R25627 : Reach 25627 := rs (se 1 (by rfl) ⟨19220, by rfl⟩) R38441
theorem R27931 : Reach 27931 := rs (se 1 (by rfl) ⟨20948, by rfl⟩) R41897
theorem R1535273 : Reach 1535273 := rs (se 2 (by rfl) ⟨575727, by rfl⟩) R1151455
theorem R390743 : Reach 390743 := rs (se 1 (by rfl) ⟨293057, by rfl⟩) R586115
theorem R95849 : Reach 95849 := rs (se 2 (by rfl) ⟨35943, by rfl⟩) R71887
theorem R195371 : Reach 195371 := rs (se 1 (by rfl) ⟨146528, by rfl⟩) R293057
theorem R131867 : Reach 131867 := rs (se 1 (by rfl) ⟨98900, by rfl⟩) R197801
theorem R37241 : Reach 37241 := rs (se 2 (by rfl) ⟨13965, by rfl⟩) R27931
theorem R858671 : Reach 858671 := rs (se 1 (by rfl) ⟨644003, by rfl⟩) R1288007
theorem R72353 : Reach 72353 := rs (se 2 (by rfl) ⟨27132, by rfl⟩) R54265
theorem R1023515 : Reach 1023515 := rs (se 1 (by rfl) ⟨767636, by rfl⟩) R1535273
theorem R245423 : Reach 245423 := rs (se 1 (by rfl) ⟨184067, by rfl⟩) R368135
theorem R260495 : Reach 260495 := rs (se 1 (by rfl) ⟨195371, by rfl⟩) R390743
theorem R63899 : Reach 63899 := rs (se 1 (by rfl) ⟨47924, by rfl⟩) R95849
theorem R130247 : Reach 130247 := rs (se 1 (by rfl) ⟨97685, by rfl⟩) R195371
theorem R173663 : Reach 173663 := rs (se 1 (by rfl) ⟨130247, by rfl⟩) R260495
theorem R42599 : Reach 42599 := rs (se 1 (by rfl) ⟨31949, by rfl⟩) R63899
theorem R572447 : Reach 572447 := rs (se 1 (by rfl) ⟨429335, by rfl⟩) R858671
theorem R86831 : Reach 86831 := rs (se 1 (by rfl) ⟨65123, by rfl⟩) R130247
theorem R87911 : Reach 87911 := rs (se 1 (by rfl) ⟨65933, by rfl⟩) R131867
theorem R24827 : Reach 24827 := rs (se 1 (by rfl) ⟨18620, by rfl⟩) R37241
theorem R682343 : Reach 682343 := rs (se 1 (by rfl) ⟨511757, by rfl⟩) R1023515
theorem R192941 : Reach 192941 := rs (se 3 (by rfl) ⟨36176, by rfl⟩) R72353
theorem R163615 : Reach 163615 := rs (se 1 (by rfl) ⟨122711, by rfl⟩) R245423
theorem R115775 : Reach 115775 := rs (se 1 (by rfl) ⟨86831, by rfl⟩) R173663
theorem R381631 : Reach 381631 := rs (se 1 (by rfl) ⟨286223, by rfl⟩) R572447
theorem R218153 : Reach 218153 := rs (se 2 (by rfl) ⟨81807, by rfl⟩) R163615
theorem R57887 : Reach 57887 := rs (se 1 (by rfl) ⟨43415, by rfl⟩) R86831
theorem R58607 : Reach 58607 := rs (se 1 (by rfl) ⟨43955, by rfl⟩) R87911
theorem R28399 : Reach 28399 := rs (se 1 (by rfl) ⟨21299, by rfl⟩) R42599
theorem R454895 : Reach 454895 := rs (se 1 (by rfl) ⟨341171, by rfl⟩) R682343
theorem R128627 : Reach 128627 := rs (se 1 (by rfl) ⟨96470, by rfl⟩) R192941
theorem R37865 : Reach 37865 := rs (se 2 (by rfl) ⟨14199, by rfl⟩) R28399
theorem R38591 : Reach 38591 := rs (se 1 (by rfl) ⟨28943, by rfl⟩) R57887
theorem R39071 : Reach 39071 := rs (se 1 (by rfl) ⟨29303, by rfl⟩) R58607
theorem R303263 : Reach 303263 := rs (se 1 (by rfl) ⟨227447, by rfl⟩) R454895
theorem R77183 : Reach 77183 := rs (se 1 (by rfl) ⟨57887, by rfl⟩) R115775
theorem R145435 : Reach 145435 := rs (se 1 (by rfl) ⟨109076, by rfl⟩) R218153
theorem R508841 : Reach 508841 := rs (se 2 (by rfl) ⟨190815, by rfl⟩) R381631
theorem R85751 : Reach 85751 := rs (se 1 (by rfl) ⟨64313, by rfl⟩) R128627
theorem R202175 : Reach 202175 := rs (se 1 (by rfl) ⟨151631, by rfl⟩) R303263
theorem R339227 : Reach 339227 := rs (se 1 (by rfl) ⟨254420, by rfl⟩) R508841
theorem R51455 : Reach 51455 := rs (se 1 (by rfl) ⟨38591, by rfl⟩) R77183
theorem R57167 : Reach 57167 := rs (se 1 (by rfl) ⟨42875, by rfl⟩) R85751
theorem R25243 : Reach 25243 := rs (se 1 (by rfl) ⟨18932, by rfl⟩) R37865
theorem R25727 : Reach 25727 := rs (se 1 (by rfl) ⟨19295, by rfl⟩) R38591
theorem R26047 : Reach 26047 := rs (se 1 (by rfl) ⟨19535, by rfl⟩) R39071
theorem R193913 : Reach 193913 := rs (se 2 (by rfl) ⟨72717, by rfl⟩) R145435
theorem R134783 : Reach 134783 := rs (se 1 (by rfl) ⟨101087, by rfl⟩) R202175
theorem R38111 : Reach 38111 := rs (se 1 (by rfl) ⟨28583, by rfl⟩) R57167
theorem R137213 : Reach 137213 := rs (se 3 (by rfl) ⟨25727, by rfl⟩) R51455
theorem R226151 : Reach 226151 := rs (se 1 (by rfl) ⟨169613, by rfl⟩) R339227
theorem R129275 : Reach 129275 := rs (se 1 (by rfl) ⟨96956, by rfl⟩) R193913
theorem R150767 : Reach 150767 := rs (se 1 (by rfl) ⟨113075, by rfl⟩) R226151
theorem R86183 : Reach 86183 := rs (se 1 (by rfl) ⟨64637, by rfl⟩) R129275
theorem R89855 : Reach 89855 := rs (se 1 (by rfl) ⟨67391, by rfl⟩) R134783
theorem R25407 : Reach 25407 := rs (se 1 (by rfl) ⟨19055, by rfl⟩) R38111
theorem R91475 : Reach 91475 := rs (se 1 (by rfl) ⟨68606, by rfl⟩) R137213
theorem R100511 : Reach 100511 := rs (se 1 (by rfl) ⟨75383, by rfl⟩) R150767
theorem R57455 : Reach 57455 := rs (se 1 (by rfl) ⟨43091, by rfl⟩) R86183
theorem R59903 : Reach 59903 := rs (se 1 (by rfl) ⟨44927, by rfl⟩) R89855
theorem R60983 : Reach 60983 := rs (se 1 (by rfl) ⟨45737, by rfl⟩) R91475
theorem R67007 : Reach 67007 := rs (se 1 (by rfl) ⟨50255, by rfl⟩) R100511
theorem R38303 : Reach 38303 := rs (se 1 (by rfl) ⟨28727, by rfl⟩) R57455
theorem R39935 : Reach 39935 := rs (se 1 (by rfl) ⟨29951, by rfl⟩) R59903
theorem R40655 : Reach 40655 := rs (se 1 (by rfl) ⟨30491, by rfl⟩) R60983
theorem R44671 : Reach 44671 := rs (se 1 (by rfl) ⟨33503, by rfl⟩) R67007
theorem R25535 : Reach 25535 := rs (se 1 (by rfl) ⟨19151, by rfl⟩) R38303
theorem R26623 : Reach 26623 := rs (se 1 (by rfl) ⟨19967, by rfl⟩) R39935
theorem R27103 : Reach 27103 := rs (se 1 (by rfl) ⟨20327, by rfl⟩) R40655
theorem R36137 : Reach 36137 := rs (se 2 (by rfl) ⟨13551, by rfl⟩) R27103
theorem R59561 : Reach 59561 := rs (se 2 (by rfl) ⟨22335, by rfl⟩) R44671
theorem R39707 : Reach 39707 := rs (se 1 (by rfl) ⟨29780, by rfl⟩) R59561
theorem R24091 : Reach 24091 := rs (se 1 (by rfl) ⟨18068, by rfl⟩) R36137
theorem R26471 : Reach 26471 := rs (se 1 (by rfl) ⟨19853, by rfl⟩) R39707

theorem C0 (j : ℕ) (h1 : 11750 ≤ j) (h2 : j ≤ 12449) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R23501
  · exact R23503
  · exact R23505
  · exact R23507
  · exact R23509
  · exact R23511
  · exact R23513
  · exact R23515
  · exact R23517
  · exact R23519
  · exact R23521
  · exact R23523
  · exact R23525
  · exact R23527
  · exact R23529
  · exact R23531
  · exact R23533
  · exact R23535
  · exact R23537
  · exact R23539
  · exact R23541
  · exact R23543
  · exact R23545
  · exact R23547
  · exact R23549
  · exact R23551
  · exact R23553
  · exact R23555
  · exact R23557
  · exact R23559
  · exact R23561
  · exact R23563
  · exact R23565
  · exact R23567
  · exact R23569
  · exact R23571
  · exact R23573
  · exact R23575
  · exact R23577
  · exact R23579
  · exact R23581
  · exact R23583
  · exact R23585
  · exact R23587
  · exact R23589
  · exact R23591
  · exact R23593
  · exact R23595
  · exact R23597
  · exact R23599
  · exact R23601
  · exact R23603
  · exact R23605
  · exact R23607
  · exact R23609
  · exact R23611
  · exact R23613
  · exact R23615
  · exact R23617
  · exact R23619
  · exact R23621
  · exact R23623
  · exact R23625
  · exact R23627
  · exact R23629
  · exact R23631
  · exact R23633
  · exact R23635
  · exact R23637
  · exact R23639
  · exact R23641
  · exact R23643
  · exact R23645
  · exact R23647
  · exact R23649
  · exact R23651
  · exact R23653
  · exact R23655
  · exact R23657
  · exact R23659
  · exact R23661
  · exact R23663
  · exact R23665
  · exact R23667
  · exact R23669
  · exact R23671
  · exact R23673
  · exact R23675
  · exact R23677
  · exact R23679
  · exact R23681
  · exact R23683
  · exact R23685
  · exact R23687
  · exact R23689
  · exact R23691
  · exact R23693
  · exact R23695
  · exact R23697
  · exact R23699
  · exact R23701
  · exact R23703
  · exact R23705
  · exact R23707
  · exact R23709
  · exact R23711
  · exact R23713
  · exact R23715
  · exact R23717
  · exact R23719
  · exact R23721
  · exact R23723
  · exact R23725
  · exact R23727
  · exact R23729
  · exact R23731
  · exact R23733
  · exact R23735
  · exact R23737
  · exact R23739
  · exact R23741
  · exact R23743
  · exact R23745
  · exact R23747
  · exact R23749
  · exact R23751
  · exact R23753
  · exact R23755
  · exact R23757
  · exact R23759
  · exact R23761
  · exact R23763
  · exact R23765
  · exact R23767
  · exact R23769
  · exact R23771
  · exact R23773
  · exact R23775
  · exact R23777
  · exact R23779
  · exact R23781
  · exact R23783
  · exact R23785
  · exact R23787
  · exact R23789
  · exact R23791
  · exact R23793
  · exact R23795
  · exact R23797
  · exact R23799
  · exact R23801
  · exact R23803
  · exact R23805
  · exact R23807
  · exact R23809
  · exact R23811
  · exact R23813
  · exact R23815
  · exact R23817
  · exact R23819
  · exact R23821
  · exact R23823
  · exact R23825
  · exact R23827
  · exact R23829
  · exact R23831
  · exact R23833
  · exact R23835
  · exact R23837
  · exact R23839
  · exact R23841
  · exact R23843
  · exact R23845
  · exact R23847
  · exact R23849
  · exact R23851
  · exact R23853
  · exact R23855
  · exact R23857
  · exact R23859
  · exact R23861
  · exact R23863
  · exact R23865
  · exact R23867
  · exact R23869
  · exact R23871
  · exact R23873
  · exact R23875
  · exact R23877
  · exact R23879
  · exact R23881
  · exact R23883
  · exact R23885
  · exact R23887
  · exact R23889
  · exact R23891
  · exact R23893
  · exact R23895
  · exact R23897
  · exact R23899
  · exact R23901
  · exact R23903
  · exact R23905
  · exact R23907
  · exact R23909
  · exact R23911
  · exact R23913
  · exact R23915
  · exact R23917
  · exact R23919
  · exact R23921
  · exact R23923
  · exact R23925
  · exact R23927
  · exact R23929
  · exact R23931
  · exact R23933
  · exact R23935
  · exact R23937
  · exact R23939
  · exact R23941
  · exact R23943
  · exact R23945
  · exact R23947
  · exact R23949
  · exact R23951
  · exact R23953
  · exact R23955
  · exact R23957
  · exact R23959
  · exact R23961
  · exact R23963
  · exact R23965
  · exact R23967
  · exact R23969
  · exact R23971
  · exact R23973
  · exact R23975
  · exact R23977
  · exact R23979
  · exact R23981
  · exact R23983
  · exact R23985
  · exact R23987
  · exact R23989
  · exact R23991
  · exact R23993
  · exact R23995
  · exact R23997
  · exact R23999
  · exact R24001
  · exact R24003
  · exact R24005
  · exact R24007
  · exact R24009
  · exact R24011
  · exact R24013
  · exact R24015
  · exact R24017
  · exact R24019
  · exact R24021
  · exact R24023
  · exact R24025
  · exact R24027
  · exact R24029
  · exact R24031
  · exact R24033
  · exact R24035
  · exact R24037
  · exact R24039
  · exact R24041
  · exact R24043
  · exact R24045
  · exact R24047
  · exact R24049
  · exact R24051
  · exact R24053
  · exact R24055
  · exact R24057
  · exact R24059
  · exact R24061
  · exact R24063
  · exact R24065
  · exact R24067
  · exact R24069
  · exact R24071
  · exact R24073
  · exact R24075
  · exact R24077
  · exact R24079
  · exact R24081
  · exact R24083
  · exact R24085
  · exact R24087
  · exact R24089
  · exact R24091
  · exact R24093
  · exact R24095
  · exact R24097
  · exact R24099
  · exact R24101
  · exact R24103
  · exact R24105
  · exact R24107
  · exact R24109
  · exact R24111
  · exact R24113
  · exact R24115
  · exact R24117
  · exact R24119
  · exact R24121
  · exact R24123
  · exact R24125
  · exact R24127
  · exact R24129
  · exact R24131
  · exact R24133
  · exact R24135
  · exact R24137
  · exact R24139
  · exact R24141
  · exact R24143
  · exact R24145
  · exact R24147
  · exact R24149
  · exact R24151
  · exact R24153
  · exact R24155
  · exact R24157
  · exact R24159
  · exact R24161
  · exact R24163
  · exact R24165
  · exact R24167
  · exact R24169
  · exact R24171
  · exact R24173
  · exact R24175
  · exact R24177
  · exact R24179
  · exact R24181
  · exact R24183
  · exact R24185
  · exact R24187
  · exact R24189
  · exact R24191
  · exact R24193
  · exact R24195
  · exact R24197
  · exact R24199
  · exact R24201
  · exact R24203
  · exact R24205
  · exact R24207
  · exact R24209
  · exact R24211
  · exact R24213
  · exact R24215
  · exact R24217
  · exact R24219
  · exact R24221
  · exact R24223
  · exact R24225
  · exact R24227
  · exact R24229
  · exact R24231
  · exact R24233
  · exact R24235
  · exact R24237
  · exact R24239
  · exact R24241
  · exact R24243
  · exact R24245
  · exact R24247
  · exact R24249
  · exact R24251
  · exact R24253
  · exact R24255
  · exact R24257
  · exact R24259
  · exact R24261
  · exact R24263
  · exact R24265
  · exact R24267
  · exact R24269
  · exact R24271
  · exact R24273
  · exact R24275
  · exact R24277
  · exact R24279
  · exact R24281
  · exact R24283
  · exact R24285
  · exact R24287
  · exact R24289
  · exact R24291
  · exact R24293
  · exact R24295
  · exact R24297
  · exact R24299
  · exact R24301
  · exact R24303
  · exact R24305
  · exact R24307
  · exact R24309
  · exact R24311
  · exact R24313
  · exact R24315
  · exact R24317
  · exact R24319
  · exact R24321
  · exact R24323
  · exact R24325
  · exact R24327
  · exact R24329
  · exact R24331
  · exact R24333
  · exact R24335
  · exact R24337
  · exact R24339
  · exact R24341
  · exact R24343
  · exact R24345
  · exact R24347
  · exact R24349
  · exact R24351
  · exact R24353
  · exact R24355
  · exact R24357
  · exact R24359
  · exact R24361
  · exact R24363
  · exact R24365
  · exact R24367
  · exact R24369
  · exact R24371
  · exact R24373
  · exact R24375
  · exact R24377
  · exact R24379
  · exact R24381
  · exact R24383
  · exact R24385
  · exact R24387
  · exact R24389
  · exact R24391
  · exact R24393
  · exact R24395
  · exact R24397
  · exact R24399
  · exact R24401
  · exact R24403
  · exact R24405
  · exact R24407
  · exact R24409
  · exact R24411
  · exact R24413
  · exact R24415
  · exact R24417
  · exact R24419
  · exact R24421
  · exact R24423
  · exact R24425
  · exact R24427
  · exact R24429
  · exact R24431
  · exact R24433
  · exact R24435
  · exact R24437
  · exact R24439
  · exact R24441
  · exact R24443
  · exact R24445
  · exact R24447
  · exact R24449
  · exact R24451
  · exact R24453
  · exact R24455
  · exact R24457
  · exact R24459
  · exact R24461
  · exact R24463
  · exact R24465
  · exact R24467
  · exact R24469
  · exact R24471
  · exact R24473
  · exact R24475
  · exact R24477
  · exact R24479
  · exact R24481
  · exact R24483
  · exact R24485
  · exact R24487
  · exact R24489
  · exact R24491
  · exact R24493
  · exact R24495
  · exact R24497
  · exact R24499
  · exact R24501
  · exact R24503
  · exact R24505
  · exact R24507
  · exact R24509
  · exact R24511
  · exact R24513
  · exact R24515
  · exact R24517
  · exact R24519
  · exact R24521
  · exact R24523
  · exact R24525
  · exact R24527
  · exact R24529
  · exact R24531
  · exact R24533
  · exact R24535
  · exact R24537
  · exact R24539
  · exact R24541
  · exact R24543
  · exact R24545
  · exact R24547
  · exact R24549
  · exact R24551
  · exact R24553
  · exact R24555
  · exact R24557
  · exact R24559
  · exact R24561
  · exact R24563
  · exact R24565
  · exact R24567
  · exact R24569
  · exact R24571
  · exact R24573
  · exact R24575
  · exact R24577
  · exact R24579
  · exact R24581
  · exact R24583
  · exact R24585
  · exact R24587
  · exact R24589
  · exact R24591
  · exact R24593
  · exact R24595
  · exact R24597
  · exact R24599
  · exact R24601
  · exact R24603
  · exact R24605
  · exact R24607
  · exact R24609
  · exact R24611
  · exact R24613
  · exact R24615
  · exact R24617
  · exact R24619
  · exact R24621
  · exact R24623
  · exact R24625
  · exact R24627
  · exact R24629
  · exact R24631
  · exact R24633
  · exact R24635
  · exact R24637
  · exact R24639
  · exact R24641
  · exact R24643
  · exact R24645
  · exact R24647
  · exact R24649
  · exact R24651
  · exact R24653
  · exact R24655
  · exact R24657
  · exact R24659
  · exact R24661
  · exact R24663
  · exact R24665
  · exact R24667
  · exact R24669
  · exact R24671
  · exact R24673
  · exact R24675
  · exact R24677
  · exact R24679
  · exact R24681
  · exact R24683
  · exact R24685
  · exact R24687
  · exact R24689
  · exact R24691
  · exact R24693
  · exact R24695
  · exact R24697
  · exact R24699
  · exact R24701
  · exact R24703
  · exact R24705
  · exact R24707
  · exact R24709
  · exact R24711
  · exact R24713
  · exact R24715
  · exact R24717
  · exact R24719
  · exact R24721
  · exact R24723
  · exact R24725
  · exact R24727
  · exact R24729
  · exact R24731
  · exact R24733
  · exact R24735
  · exact R24737
  · exact R24739
  · exact R24741
  · exact R24743
  · exact R24745
  · exact R24747
  · exact R24749
  · exact R24751
  · exact R24753
  · exact R24755
  · exact R24757
  · exact R24759
  · exact R24761
  · exact R24763
  · exact R24765
  · exact R24767
  · exact R24769
  · exact R24771
  · exact R24773
  · exact R24775
  · exact R24777
  · exact R24779
  · exact R24781
  · exact R24783
  · exact R24785
  · exact R24787
  · exact R24789
  · exact R24791
  · exact R24793
  · exact R24795
  · exact R24797
  · exact R24799
  · exact R24801
  · exact R24803
  · exact R24805
  · exact R24807
  · exact R24809
  · exact R24811
  · exact R24813
  · exact R24815
  · exact R24817
  · exact R24819
  · exact R24821
  · exact R24823
  · exact R24825
  · exact R24827
  · exact R24829
  · exact R24831
  · exact R24833
  · exact R24835
  · exact R24837
  · exact R24839
  · exact R24841
  · exact R24843
  · exact R24845
  · exact R24847
  · exact R24849
  · exact R24851
  · exact R24853
  · exact R24855
  · exact R24857
  · exact R24859
  · exact R24861
  · exact R24863
  · exact R24865
  · exact R24867
  · exact R24869
  · exact R24871
  · exact R24873
  · exact R24875
  · exact R24877
  · exact R24879
  · exact R24881
  · exact R24883
  · exact R24885
  · exact R24887
  · exact R24889
  · exact R24891
  · exact R24893
  · exact R24895
  · exact R24897
  · exact R24899

theorem C1 (j : ℕ) (h1 : 12450 ≤ j) (h2 : j ≤ 13149) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R24901
  · exact R24903
  · exact R24905
  · exact R24907
  · exact R24909
  · exact R24911
  · exact R24913
  · exact R24915
  · exact R24917
  · exact R24919
  · exact R24921
  · exact R24923
  · exact R24925
  · exact R24927
  · exact R24929
  · exact R24931
  · exact R24933
  · exact R24935
  · exact R24937
  · exact R24939
  · exact R24941
  · exact R24943
  · exact R24945
  · exact R24947
  · exact R24949
  · exact R24951
  · exact R24953
  · exact R24955
  · exact R24957
  · exact R24959
  · exact R24961
  · exact R24963
  · exact R24965
  · exact R24967
  · exact R24969
  · exact R24971
  · exact R24973
  · exact R24975
  · exact R24977
  · exact R24979
  · exact R24981
  · exact R24983
  · exact R24985
  · exact R24987
  · exact R24989
  · exact R24991
  · exact R24993
  · exact R24995
  · exact R24997
  · exact R24999
  · exact R25001
  · exact R25003
  · exact R25005
  · exact R25007
  · exact R25009
  · exact R25011
  · exact R25013
  · exact R25015
  · exact R25017
  · exact R25019
  · exact R25021
  · exact R25023
  · exact R25025
  · exact R25027
  · exact R25029
  · exact R25031
  · exact R25033
  · exact R25035
  · exact R25037
  · exact R25039
  · exact R25041
  · exact R25043
  · exact R25045
  · exact R25047
  · exact R25049
  · exact R25051
  · exact R25053
  · exact R25055
  · exact R25057
  · exact R25059
  · exact R25061
  · exact R25063
  · exact R25065
  · exact R25067
  · exact R25069
  · exact R25071
  · exact R25073
  · exact R25075
  · exact R25077
  · exact R25079
  · exact R25081
  · exact R25083
  · exact R25085
  · exact R25087
  · exact R25089
  · exact R25091
  · exact R25093
  · exact R25095
  · exact R25097
  · exact R25099
  · exact R25101
  · exact R25103
  · exact R25105
  · exact R25107
  · exact R25109
  · exact R25111
  · exact R25113
  · exact R25115
  · exact R25117
  · exact R25119
  · exact R25121
  · exact R25123
  · exact R25125
  · exact R25127
  · exact R25129
  · exact R25131
  · exact R25133
  · exact R25135
  · exact R25137
  · exact R25139
  · exact R25141
  · exact R25143
  · exact R25145
  · exact R25147
  · exact R25149
  · exact R25151
  · exact R25153
  · exact R25155
  · exact R25157
  · exact R25159
  · exact R25161
  · exact R25163
  · exact R25165
  · exact R25167
  · exact R25169
  · exact R25171
  · exact R25173
  · exact R25175
  · exact R25177
  · exact R25179
  · exact R25181
  · exact R25183
  · exact R25185
  · exact R25187
  · exact R25189
  · exact R25191
  · exact R25193
  · exact R25195
  · exact R25197
  · exact R25199
  · exact R25201
  · exact R25203
  · exact R25205
  · exact R25207
  · exact R25209
  · exact R25211
  · exact R25213
  · exact R25215
  · exact R25217
  · exact R25219
  · exact R25221
  · exact R25223
  · exact R25225
  · exact R25227
  · exact R25229
  · exact R25231
  · exact R25233
  · exact R25235
  · exact R25237
  · exact R25239
  · exact R25241
  · exact R25243
  · exact R25245
  · exact R25247
  · exact R25249
  · exact R25251
  · exact R25253
  · exact R25255
  · exact R25257
  · exact R25259
  · exact R25261
  · exact R25263
  · exact R25265
  · exact R25267
  · exact R25269
  · exact R25271
  · exact R25273
  · exact R25275
  · exact R25277
  · exact R25279
  · exact R25281
  · exact R25283
  · exact R25285
  · exact R25287
  · exact R25289
  · exact R25291
  · exact R25293
  · exact R25295
  · exact R25297
  · exact R25299
  · exact R25301
  · exact R25303
  · exact R25305
  · exact R25307
  · exact R25309
  · exact R25311
  · exact R25313
  · exact R25315
  · exact R25317
  · exact R25319
  · exact R25321
  · exact R25323
  · exact R25325
  · exact R25327
  · exact R25329
  · exact R25331
  · exact R25333
  · exact R25335
  · exact R25337
  · exact R25339
  · exact R25341
  · exact R25343
  · exact R25345
  · exact R25347
  · exact R25349
  · exact R25351
  · exact R25353
  · exact R25355
  · exact R25357
  · exact R25359
  · exact R25361
  · exact R25363
  · exact R25365
  · exact R25367
  · exact R25369
  · exact R25371
  · exact R25373
  · exact R25375
  · exact R25377
  · exact R25379
  · exact R25381
  · exact R25383
  · exact R25385
  · exact R25387
  · exact R25389
  · exact R25391
  · exact R25393
  · exact R25395
  · exact R25397
  · exact R25399
  · exact R25401
  · exact R25403
  · exact R25405
  · exact R25407
  · exact R25409
  · exact R25411
  · exact R25413
  · exact R25415
  · exact R25417
  · exact R25419
  · exact R25421
  · exact R25423
  · exact R25425
  · exact R25427
  · exact R25429
  · exact R25431
  · exact R25433
  · exact R25435
  · exact R25437
  · exact R25439
  · exact R25441
  · exact R25443
  · exact R25445
  · exact R25447
  · exact R25449
  · exact R25451
  · exact R25453
  · exact R25455
  · exact R25457
  · exact R25459
  · exact R25461
  · exact R25463
  · exact R25465
  · exact R25467
  · exact R25469
  · exact R25471
  · exact R25473
  · exact R25475
  · exact R25477
  · exact R25479
  · exact R25481
  · exact R25483
  · exact R25485
  · exact R25487
  · exact R25489
  · exact R25491
  · exact R25493
  · exact R25495
  · exact R25497
  · exact R25499
  · exact R25501
  · exact R25503
  · exact R25505
  · exact R25507
  · exact R25509
  · exact R25511
  · exact R25513
  · exact R25515
  · exact R25517
  · exact R25519
  · exact R25521
  · exact R25523
  · exact R25525
  · exact R25527
  · exact R25529
  · exact R25531
  · exact R25533
  · exact R25535
  · exact R25537
  · exact R25539
  · exact R25541
  · exact R25543
  · exact R25545
  · exact R25547
  · exact R25549
  · exact R25551
  · exact R25553
  · exact R25555
  · exact R25557
  · exact R25559
  · exact R25561
  · exact R25563
  · exact R25565
  · exact R25567
  · exact R25569
  · exact R25571
  · exact R25573
  · exact R25575
  · exact R25577
  · exact R25579
  · exact R25581
  · exact R25583
  · exact R25585
  · exact R25587
  · exact R25589
  · exact R25591
  · exact R25593
  · exact R25595
  · exact R25597
  · exact R25599
  · exact R25601
  · exact R25603
  · exact R25605
  · exact R25607
  · exact R25609
  · exact R25611
  · exact R25613
  · exact R25615
  · exact R25617
  · exact R25619
  · exact R25621
  · exact R25623
  · exact R25625
  · exact R25627
  · exact R25629
  · exact R25631
  · exact R25633
  · exact R25635
  · exact R25637
  · exact R25639
  · exact R25641
  · exact R25643
  · exact R25645
  · exact R25647
  · exact R25649
  · exact R25651
  · exact R25653
  · exact R25655
  · exact R25657
  · exact R25659
  · exact R25661
  · exact R25663
  · exact R25665
  · exact R25667
  · exact R25669
  · exact R25671
  · exact R25673
  · exact R25675
  · exact R25677
  · exact R25679
  · exact R25681
  · exact R25683
  · exact R25685
  · exact R25687
  · exact R25689
  · exact R25691
  · exact R25693
  · exact R25695
  · exact R25697
  · exact R25699
  · exact R25701
  · exact R25703
  · exact R25705
  · exact R25707
  · exact R25709
  · exact R25711
  · exact R25713
  · exact R25715
  · exact R25717
  · exact R25719
  · exact R25721
  · exact R25723
  · exact R25725
  · exact R25727
  · exact R25729
  · exact R25731
  · exact R25733
  · exact R25735
  · exact R25737
  · exact R25739
  · exact R25741
  · exact R25743
  · exact R25745
  · exact R25747
  · exact R25749
  · exact R25751
  · exact R25753
  · exact R25755
  · exact R25757
  · exact R25759
  · exact R25761
  · exact R25763
  · exact R25765
  · exact R25767
  · exact R25769
  · exact R25771
  · exact R25773
  · exact R25775
  · exact R25777
  · exact R25779
  · exact R25781
  · exact R25783
  · exact R25785
  · exact R25787
  · exact R25789
  · exact R25791
  · exact R25793
  · exact R25795
  · exact R25797
  · exact R25799
  · exact R25801
  · exact R25803
  · exact R25805
  · exact R25807
  · exact R25809
  · exact R25811
  · exact R25813
  · exact R25815
  · exact R25817
  · exact R25819
  · exact R25821
  · exact R25823
  · exact R25825
  · exact R25827
  · exact R25829
  · exact R25831
  · exact R25833
  · exact R25835
  · exact R25837
  · exact R25839
  · exact R25841
  · exact R25843
  · exact R25845
  · exact R25847
  · exact R25849
  · exact R25851
  · exact R25853
  · exact R25855
  · exact R25857
  · exact R25859
  · exact R25861
  · exact R25863
  · exact R25865
  · exact R25867
  · exact R25869
  · exact R25871
  · exact R25873
  · exact R25875
  · exact R25877
  · exact R25879
  · exact R25881
  · exact R25883
  · exact R25885
  · exact R25887
  · exact R25889
  · exact R25891
  · exact R25893
  · exact R25895
  · exact R25897
  · exact R25899
  · exact R25901
  · exact R25903
  · exact R25905
  · exact R25907
  · exact R25909
  · exact R25911
  · exact R25913
  · exact R25915
  · exact R25917
  · exact R25919
  · exact R25921
  · exact R25923
  · exact R25925
  · exact R25927
  · exact R25929
  · exact R25931
  · exact R25933
  · exact R25935
  · exact R25937
  · exact R25939
  · exact R25941
  · exact R25943
  · exact R25945
  · exact R25947
  · exact R25949
  · exact R25951
  · exact R25953
  · exact R25955
  · exact R25957
  · exact R25959
  · exact R25961
  · exact R25963
  · exact R25965
  · exact R25967
  · exact R25969
  · exact R25971
  · exact R25973
  · exact R25975
  · exact R25977
  · exact R25979
  · exact R25981
  · exact R25983
  · exact R25985
  · exact R25987
  · exact R25989
  · exact R25991
  · exact R25993
  · exact R25995
  · exact R25997
  · exact R25999
  · exact R26001
  · exact R26003
  · exact R26005
  · exact R26007
  · exact R26009
  · exact R26011
  · exact R26013
  · exact R26015
  · exact R26017
  · exact R26019
  · exact R26021
  · exact R26023
  · exact R26025
  · exact R26027
  · exact R26029
  · exact R26031
  · exact R26033
  · exact R26035
  · exact R26037
  · exact R26039
  · exact R26041
  · exact R26043
  · exact R26045
  · exact R26047
  · exact R26049
  · exact R26051
  · exact R26053
  · exact R26055
  · exact R26057
  · exact R26059
  · exact R26061
  · exact R26063
  · exact R26065
  · exact R26067
  · exact R26069
  · exact R26071
  · exact R26073
  · exact R26075
  · exact R26077
  · exact R26079
  · exact R26081
  · exact R26083
  · exact R26085
  · exact R26087
  · exact R26089
  · exact R26091
  · exact R26093
  · exact R26095
  · exact R26097
  · exact R26099
  · exact R26101
  · exact R26103
  · exact R26105
  · exact R26107
  · exact R26109
  · exact R26111
  · exact R26113
  · exact R26115
  · exact R26117
  · exact R26119
  · exact R26121
  · exact R26123
  · exact R26125
  · exact R26127
  · exact R26129
  · exact R26131
  · exact R26133
  · exact R26135
  · exact R26137
  · exact R26139
  · exact R26141
  · exact R26143
  · exact R26145
  · exact R26147
  · exact R26149
  · exact R26151
  · exact R26153
  · exact R26155
  · exact R26157
  · exact R26159
  · exact R26161
  · exact R26163
  · exact R26165
  · exact R26167
  · exact R26169
  · exact R26171
  · exact R26173
  · exact R26175
  · exact R26177
  · exact R26179
  · exact R26181
  · exact R26183
  · exact R26185
  · exact R26187
  · exact R26189
  · exact R26191
  · exact R26193
  · exact R26195
  · exact R26197
  · exact R26199
  · exact R26201
  · exact R26203
  · exact R26205
  · exact R26207
  · exact R26209
  · exact R26211
  · exact R26213
  · exact R26215
  · exact R26217
  · exact R26219
  · exact R26221
  · exact R26223
  · exact R26225
  · exact R26227
  · exact R26229
  · exact R26231
  · exact R26233
  · exact R26235
  · exact R26237
  · exact R26239
  · exact R26241
  · exact R26243
  · exact R26245
  · exact R26247
  · exact R26249
  · exact R26251
  · exact R26253
  · exact R26255
  · exact R26257
  · exact R26259
  · exact R26261
  · exact R26263
  · exact R26265
  · exact R26267
  · exact R26269
  · exact R26271
  · exact R26273
  · exact R26275
  · exact R26277
  · exact R26279
  · exact R26281
  · exact R26283
  · exact R26285
  · exact R26287
  · exact R26289
  · exact R26291
  · exact R26293
  · exact R26295
  · exact R26297
  · exact R26299

theorem C2 (j : ℕ) (h1 : 13150 ≤ j) (h2 : j ≤ 13556) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R26301
  · exact R26303
  · exact R26305
  · exact R26307
  · exact R26309
  · exact R26311
  · exact R26313
  · exact R26315
  · exact R26317
  · exact R26319
  · exact R26321
  · exact R26323
  · exact R26325
  · exact R26327
  · exact R26329
  · exact R26331
  · exact R26333
  · exact R26335
  · exact R26337
  · exact R26339
  · exact R26341
  · exact R26343
  · exact R26345
  · exact R26347
  · exact R26349
  · exact R26351
  · exact R26353
  · exact R26355
  · exact R26357
  · exact R26359
  · exact R26361
  · exact R26363
  · exact R26365
  · exact R26367
  · exact R26369
  · exact R26371
  · exact R26373
  · exact R26375
  · exact R26377
  · exact R26379
  · exact R26381
  · exact R26383
  · exact R26385
  · exact R26387
  · exact R26389
  · exact R26391
  · exact R26393
  · exact R26395
  · exact R26397
  · exact R26399
  · exact R26401
  · exact R26403
  · exact R26405
  · exact R26407
  · exact R26409
  · exact R26411
  · exact R26413
  · exact R26415
  · exact R26417
  · exact R26419
  · exact R26421
  · exact R26423
  · exact R26425
  · exact R26427
  · exact R26429
  · exact R26431
  · exact R26433
  · exact R26435
  · exact R26437
  · exact R26439
  · exact R26441
  · exact R26443
  · exact R26445
  · exact R26447
  · exact R26449
  · exact R26451
  · exact R26453
  · exact R26455
  · exact R26457
  · exact R26459
  · exact R26461
  · exact R26463
  · exact R26465
  · exact R26467
  · exact R26469
  · exact R26471
  · exact R26473
  · exact R26475
  · exact R26477
  · exact R26479
  · exact R26481
  · exact R26483
  · exact R26485
  · exact R26487
  · exact R26489
  · exact R26491
  · exact R26493
  · exact R26495
  · exact R26497
  · exact R26499
  · exact R26501
  · exact R26503
  · exact R26505
  · exact R26507
  · exact R26509
  · exact R26511
  · exact R26513
  · exact R26515
  · exact R26517
  · exact R26519
  · exact R26521
  · exact R26523
  · exact R26525
  · exact R26527
  · exact R26529
  · exact R26531
  · exact R26533
  · exact R26535
  · exact R26537
  · exact R26539
  · exact R26541
  · exact R26543
  · exact R26545
  · exact R26547
  · exact R26549
  · exact R26551
  · exact R26553
  · exact R26555
  · exact R26557
  · exact R26559
  · exact R26561
  · exact R26563
  · exact R26565
  · exact R26567
  · exact R26569
  · exact R26571
  · exact R26573
  · exact R26575
  · exact R26577
  · exact R26579
  · exact R26581
  · exact R26583
  · exact R26585
  · exact R26587
  · exact R26589
  · exact R26591
  · exact R26593
  · exact R26595
  · exact R26597
  · exact R26599
  · exact R26601
  · exact R26603
  · exact R26605
  · exact R26607
  · exact R26609
  · exact R26611
  · exact R26613
  · exact R26615
  · exact R26617
  · exact R26619
  · exact R26621
  · exact R26623
  · exact R26625
  · exact R26627
  · exact R26629
  · exact R26631
  · exact R26633
  · exact R26635
  · exact R26637
  · exact R26639
  · exact R26641
  · exact R26643
  · exact R26645
  · exact R26647
  · exact R26649
  · exact R26651
  · exact R26653
  · exact R26655
  · exact R26657
  · exact R26659
  · exact R26661
  · exact R26663
  · exact R26665
  · exact R26667
  · exact R26669
  · exact R26671
  · exact R26673
  · exact R26675
  · exact R26677
  · exact R26679
  · exact R26681
  · exact R26683
  · exact R26685
  · exact R26687
  · exact R26689
  · exact R26691
  · exact R26693
  · exact R26695
  · exact R26697
  · exact R26699
  · exact R26701
  · exact R26703
  · exact R26705
  · exact R26707
  · exact R26709
  · exact R26711
  · exact R26713
  · exact R26715
  · exact R26717
  · exact R26719
  · exact R26721
  · exact R26723
  · exact R26725
  · exact R26727
  · exact R26729
  · exact R26731
  · exact R26733
  · exact R26735
  · exact R26737
  · exact R26739
  · exact R26741
  · exact R26743
  · exact R26745
  · exact R26747
  · exact R26749
  · exact R26751
  · exact R26753
  · exact R26755
  · exact R26757
  · exact R26759
  · exact R26761
  · exact R26763
  · exact R26765
  · exact R26767
  · exact R26769
  · exact R26771
  · exact R26773
  · exact R26775
  · exact R26777
  · exact R26779
  · exact R26781
  · exact R26783
  · exact R26785
  · exact R26787
  · exact R26789
  · exact R26791
  · exact R26793
  · exact R26795
  · exact R26797
  · exact R26799
  · exact R26801
  · exact R26803
  · exact R26805
  · exact R26807
  · exact R26809
  · exact R26811
  · exact R26813
  · exact R26815
  · exact R26817
  · exact R26819
  · exact R26821
  · exact R26823
  · exact R26825
  · exact R26827
  · exact R26829
  · exact R26831
  · exact R26833
  · exact R26835
  · exact R26837
  · exact R26839
  · exact R26841
  · exact R26843
  · exact R26845
  · exact R26847
  · exact R26849
  · exact R26851
  · exact R26853
  · exact R26855
  · exact R26857
  · exact R26859
  · exact R26861
  · exact R26863
  · exact R26865
  · exact R26867
  · exact R26869
  · exact R26871
  · exact R26873
  · exact R26875
  · exact R26877
  · exact R26879
  · exact R26881
  · exact R26883
  · exact R26885
  · exact R26887
  · exact R26889
  · exact R26891
  · exact R26893
  · exact R26895
  · exact R26897
  · exact R26899
  · exact R26901
  · exact R26903
  · exact R26905
  · exact R26907
  · exact R26909
  · exact R26911
  · exact R26913
  · exact R26915
  · exact R26917
  · exact R26919
  · exact R26921
  · exact R26923
  · exact R26925
  · exact R26927
  · exact R26929
  · exact R26931
  · exact R26933
  · exact R26935
  · exact R26937
  · exact R26939
  · exact R26941
  · exact R26943
  · exact R26945
  · exact R26947
  · exact R26949
  · exact R26951
  · exact R26953
  · exact R26955
  · exact R26957
  · exact R26959
  · exact R26961
  · exact R26963
  · exact R26965
  · exact R26967
  · exact R26969
  · exact R26971
  · exact R26973
  · exact R26975
  · exact R26977
  · exact R26979
  · exact R26981
  · exact R26983
  · exact R26985
  · exact R26987
  · exact R26989
  · exact R26991
  · exact R26993
  · exact R26995
  · exact R26997
  · exact R26999
  · exact R27001
  · exact R27003
  · exact R27005
  · exact R27007
  · exact R27009
  · exact R27011
  · exact R27013
  · exact R27015
  · exact R27017
  · exact R27019
  · exact R27021
  · exact R27023
  · exact R27025
  · exact R27027
  · exact R27029
  · exact R27031
  · exact R27033
  · exact R27035
  · exact R27037
  · exact R27039
  · exact R27041
  · exact R27043
  · exact R27045
  · exact R27047
  · exact R27049
  · exact R27051
  · exact R27053
  · exact R27055
  · exact R27057
  · exact R27059
  · exact R27061
  · exact R27063
  · exact R27065
  · exact R27067
  · exact R27069
  · exact R27071
  · exact R27073
  · exact R27075
  · exact R27077
  · exact R27079
  · exact R27081
  · exact R27083
  · exact R27085
  · exact R27087
  · exact R27089
  · exact R27091
  · exact R27093
  · exact R27095
  · exact R27097
  · exact R27099
  · exact R27101
  · exact R27103
  · exact R27105
  · exact R27107
  · exact R27109
  · exact R27111
  · exact R27113

theorem solution (m : ℕ) (hm : 0 < m) (hodd : Odd m) (hle : m ≤ 27113) :
    ∃ k : ℕ, syracuseStep^[k] m = 1 := by
  rcases Nat.lt_or_ge m 23501 with hlo | hlo
  · exact syracuse_reaches_one_below_23501 m hm hodd (by omega)
  obtain ⟨j, rfl⟩ : ∃ j, m = 2 * j + 1 := by obtain ⟨t, ht⟩ := hodd; exact ⟨t, by omega⟩
  rcases Nat.lt_or_ge j 12450 with h0 | h0
  · exact C0 j (by omega) (by omega)
  rcases Nat.lt_or_ge j 13150 with h1 | h1
  · exact C1 j (by omega) (by omega)
  exact C2 j (by omega) (by omega)
