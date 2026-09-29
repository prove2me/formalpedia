-- Prove2me | solution 1 for syracuse_reaches_one_below_20001
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T04:43:14.061817+00:00
-- url     : https://prove2.me/submissions/36f3584d-0d0c-4d83-b2c1-3182d550e72f

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_reaches_one_below_12825

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
theorem B (n : ℕ) (h1 : 0 < n) (h2 : Odd n) (h3 : n ≤ 12824) : Reach n :=
  syracuse_reaches_one_below_12825 n h1 h2 h3
theorem R32813 : Reach 32813 := rs (se 3 (by rfl) ⟨6152, by rfl⟩) (B 12305 (by norm_num) ⟨6152, by rfl⟩ (by norm_num))
theorem R65605 : Reach 65605 := rs (se 4 (by rfl) ⟨6150, by rfl⟩) (B 12301 (by norm_num) ⟨6150, by rfl⟩ (by norm_num))
theorem R32845 : Reach 32845 := rs (se 3 (by rfl) ⟨6158, by rfl⟩) (B 12317 (by norm_num) ⟨6158, by rfl⟩ (by norm_num))
theorem R32885 : Reach 32885 := rs (se 5 (by rfl) ⟨1541, by rfl⟩) (B 3083 (by norm_num) ⟨1541, by rfl⟩ (by norm_num))
theorem R65701 : Reach 65701 := rs (se 4 (by rfl) ⟨6159, by rfl⟩) (B 12319 (by norm_num) ⟨6159, by rfl⟩ (by norm_num))
theorem R32933 : Reach 32933 := rs (se 4 (by rfl) ⟨3087, by rfl⟩) (B 6175 (by norm_num) ⟨3087, by rfl⟩ (by norm_num))
theorem R65717 : Reach 65717 := rs (se 5 (by rfl) ⟨3080, by rfl⟩) (B 6161 (by norm_num) ⟨3080, by rfl⟩ (by norm_num))
theorem R32957 : Reach 32957 := rs (se 3 (by rfl) ⟨6179, by rfl⟩) (B 12359 (by norm_num) ⟨6179, by rfl⟩ (by norm_num))
theorem R33029 : Reach 33029 := rs (se 4 (by rfl) ⟨3096, by rfl⟩) (B 6193 (by norm_num) ⟨3096, by rfl⟩ (by norm_num))
theorem R33061 : Reach 33061 := rs (se 4 (by rfl) ⟨3099, by rfl⟩) (B 6199 (by norm_num) ⟨3099, by rfl⟩ (by norm_num))
theorem R33101 : Reach 33101 := rs (se 3 (by rfl) ⟨6206, by rfl⟩) (B 12413 (by norm_num) ⟨6206, by rfl⟩ (by norm_num))
theorem R33149 : Reach 33149 := rs (se 3 (by rfl) ⟨6215, by rfl⟩) (B 12431 (by norm_num) ⟨6215, by rfl⟩ (by norm_num))
theorem R33173 : Reach 33173 := rs (se 6 (by rfl) ⟨777, by rfl⟩) (B 1555 (by norm_num) ⟨777, by rfl⟩ (by norm_num))
theorem R66005 : Reach 66005 := rs (se 7 (by rfl) ⟨773, by rfl⟩) (B 1547 (by norm_num) ⟨773, by rfl⟩ (by norm_num))
theorem R33245 : Reach 33245 := rs (se 3 (by rfl) ⟨6233, by rfl⟩) (B 12467 (by norm_num) ⟨6233, by rfl⟩ (by norm_num))
theorem R33253 : Reach 33253 := rs (se 4 (by rfl) ⟨3117, by rfl⟩) (B 6235 (by norm_num) ⟨3117, by rfl⟩ (by norm_num))
theorem R33277 : Reach 33277 := rs (se 3 (by rfl) ⟨6239, by rfl⟩) (B 12479 (by norm_num) ⟨6239, by rfl⟩ (by norm_num))
theorem R33293 : Reach 33293 := rs (se 3 (by rfl) ⟨6242, by rfl⟩) (B 12485 (by norm_num) ⟨6242, by rfl⟩ (by norm_num))
theorem R33301 : Reach 33301 := rs (se 6 (by rfl) ⟨780, by rfl⟩) (B 1561 (by norm_num) ⟨780, by rfl⟩ (by norm_num))
theorem R33317 : Reach 33317 := rs (se 4 (by rfl) ⟨3123, by rfl⟩) (B 6247 (by norm_num) ⟨3123, by rfl⟩ (by norm_num))
theorem R33365 : Reach 33365 := rs (se 8 (by rfl) ⟨195, by rfl⟩) (B 391 (by norm_num) ⟨195, by rfl⟩ (by norm_num))
theorem R66149 : Reach 66149 := rs (se 4 (by rfl) ⟨6201, by rfl⟩) (B 12403 (by norm_num) ⟨6201, by rfl⟩ (by norm_num))
theorem R33389 : Reach 33389 := rs (se 3 (by rfl) ⟨6260, by rfl⟩) (B 12521 (by norm_num) ⟨6260, by rfl⟩ (by norm_num))
theorem R33461 : Reach 33461 := rs (se 5 (by rfl) ⟨1568, by rfl⟩) (B 3137 (by norm_num) ⟨1568, by rfl⟩ (by norm_num))
theorem R33493 : Reach 33493 := rs (se 7 (by rfl) ⟨392, by rfl⟩) (B 785 (by norm_num) ⟨392, by rfl⟩ (by norm_num))
theorem R33533 : Reach 33533 := rs (se 3 (by rfl) ⟨6287, by rfl⟩) (B 12575 (by norm_num) ⟨6287, by rfl⟩ (by norm_num))
theorem R33581 : Reach 33581 := rs (se 3 (by rfl) ⟨6296, by rfl⟩) (B 12593 (by norm_num) ⟨6296, by rfl⟩ (by norm_num))
theorem R33605 : Reach 33605 := rs (se 4 (by rfl) ⟨3150, by rfl⟩) (B 6301 (by norm_num) ⟨3150, by rfl⟩ (by norm_num))
theorem R164693 : Reach 164693 := rs (se 9 (by rfl) ⟨482, by rfl⟩) (B 965 (by norm_num) ⟨482, by rfl⟩ (by norm_num))
theorem R33677 : Reach 33677 := rs (se 3 (by rfl) ⟨6314, by rfl⟩) (B 12629 (by norm_num) ⟨6314, by rfl⟩ (by norm_num))
theorem R33709 : Reach 33709 := rs (se 3 (by rfl) ⟨6320, by rfl⟩) (B 12641 (by norm_num) ⟨6320, by rfl⟩ (by norm_num))
theorem R33749 : Reach 33749 := rs (se 7 (by rfl) ⟨395, by rfl⟩) (B 791 (by norm_num) ⟨395, by rfl⟩ (by norm_num))
theorem R33797 : Reach 33797 := rs (se 4 (by rfl) ⟨3168, by rfl⟩) (B 6337 (by norm_num) ⟨3168, by rfl⟩ (by norm_num))
theorem R66581 : Reach 66581 := rs (se 6 (by rfl) ⟨1560, by rfl⟩) (B 3121 (by norm_num) ⟨1560, by rfl⟩ (by norm_num))
theorem R33821 : Reach 33821 := rs (se 3 (by rfl) ⟨6341, by rfl⟩) (B 12683 (by norm_num) ⟨6341, by rfl⟩ (by norm_num))
theorem R33853 : Reach 33853 := rs (se 3 (by rfl) ⟨6347, by rfl⟩) (B 12695 (by norm_num) ⟨6347, by rfl⟩ (by norm_num))
theorem R33893 : Reach 33893 := rs (se 4 (by rfl) ⟨3177, by rfl⟩) (B 6355 (by norm_num) ⟨3177, by rfl⟩ (by norm_num))
theorem R33965 : Reach 33965 := rs (se 3 (by rfl) ⟨6368, by rfl⟩) (B 12737 (by norm_num) ⟨6368, by rfl⟩ (by norm_num))
theorem R34013 : Reach 34013 := rs (se 3 (by rfl) ⟨6377, by rfl⟩) (B 12755 (by norm_num) ⟨6377, by rfl⟩ (by norm_num))
theorem R34037 : Reach 34037 := rs (se 5 (by rfl) ⟨1595, by rfl⟩) (B 3191 (by norm_num) ⟨1595, by rfl⟩ (by norm_num))
theorem R197909 : Reach 197909 := rs (se 6 (by rfl) ⟨4638, by rfl⟩) (B 9277 (by norm_num) ⟨4638, by rfl⟩ (by norm_num))
theorem R34109 : Reach 34109 := rs (se 3 (by rfl) ⟨6395, by rfl⟩) (B 12791 (by norm_num) ⟨6395, by rfl⟩ (by norm_num))
theorem R34141 : Reach 34141 := rs (se 3 (by rfl) ⟨6401, by rfl⟩) (B 12803 (by norm_num) ⟨6401, by rfl⟩ (by norm_num))
theorem R34157 : Reach 34157 := rs (se 3 (by rfl) ⟨6404, by rfl⟩) (B 12809 (by norm_num) ⟨6404, by rfl⟩ (by norm_num))
theorem R34181 : Reach 34181 := rs (se 4 (by rfl) ⟨3204, by rfl⟩) (B 6409 (by norm_num) ⟨3204, by rfl⟩ (by norm_num))
theorem R99733 : Reach 99733 := rs (se 6 (by rfl) ⟨2337, by rfl⟩) (B 4675 (by norm_num) ⟨2337, by rfl⟩ (by norm_num))
theorem R67013 : Reach 67013 := rs (se 4 (by rfl) ⟨6282, by rfl⟩) (B 12565 (by norm_num) ⟨6282, by rfl⟩ (by norm_num))
theorem R34325 : Reach 34325 := rs (se 6 (by rfl) ⟨804, by rfl⟩) (B 1609 (by norm_num) ⟨804, by rfl⟩ (by norm_num))
theorem R67189 : Reach 67189 := rs (se 5 (by rfl) ⟨3149, by rfl⟩) (B 6299 (by norm_num) ⟨3149, by rfl⟩ (by norm_num))
theorem R34469 : Reach 34469 := rs (se 4 (by rfl) ⟨3231, by rfl⟩) (B 6463 (by norm_num) ⟨3231, by rfl⟩ (by norm_num))
theorem R34597 : Reach 34597 := rs (se 4 (by rfl) ⟨3243, by rfl⟩) (B 6487 (by norm_num) ⟨3243, by rfl⟩ (by norm_num))
theorem R34613 : Reach 34613 := rs (se 5 (by rfl) ⟨1622, by rfl⟩) (B 3245 (by norm_num) ⟨1622, by rfl⟩ (by norm_num))
theorem R67445 : Reach 67445 := rs (se 5 (by rfl) ⟨3161, by rfl⟩) (B 6323 (by norm_num) ⟨3161, by rfl⟩ (by norm_num))
theorem R67493 : Reach 67493 := rs (se 4 (by rfl) ⟨6327, by rfl⟩) (B 12655 (by norm_num) ⟨6327, by rfl⟩ (by norm_num))
theorem R100277 : Reach 100277 := rs (se 5 (by rfl) ⟨4700, by rfl⟩) (B 9401 (by norm_num) ⟨4700, by rfl⟩ (by norm_num))
theorem R34757 : Reach 34757 := rs (se 4 (by rfl) ⟨3258, by rfl⟩) (B 6517 (by norm_num) ⟨3258, by rfl⟩ (by norm_num))
theorem R165845 : Reach 165845 := rs (se 7 (by rfl) ⟨1943, by rfl⟩) (B 3887 (by norm_num) ⟨1943, by rfl⟩ (by norm_num))
theorem R34789 : Reach 34789 := rs (se 4 (by rfl) ⟨3261, by rfl⟩) (B 6523 (by norm_num) ⟨3261, by rfl⟩ (by norm_num))
theorem R34805 : Reach 34805 := rs (se 5 (by rfl) ⟨1631, by rfl⟩) (B 3263 (by norm_num) ⟨1631, by rfl⟩ (by norm_num))
theorem R34901 : Reach 34901 := rs (se 8 (by rfl) ⟨204, by rfl⟩) (B 409 (by norm_num) ⟨204, by rfl⟩ (by norm_num))
theorem R34933 : Reach 34933 := rs (se 5 (by rfl) ⟨1637, by rfl⟩) (B 3275 (by norm_num) ⟨1637, by rfl⟩ (by norm_num))
theorem R35045 : Reach 35045 := rs (se 4 (by rfl) ⟨3285, by rfl⟩) (B 6571 (by norm_num) ⟨3285, by rfl⟩ (by norm_num))
theorem R35093 : Reach 35093 := rs (se 6 (by rfl) ⟨822, by rfl⟩) (B 1645 (by norm_num) ⟨822, by rfl⟩ (by norm_num))
theorem R67877 : Reach 67877 := rs (se 4 (by rfl) ⟨6363, by rfl⟩) (B 12727 (by norm_num) ⟨6363, by rfl⟩ (by norm_num))
theorem R35189 : Reach 35189 := rs (se 5 (by rfl) ⟨1649, by rfl⟩) (B 3299 (by norm_num) ⟨1649, by rfl⟩ (by norm_num))
theorem R35333 : Reach 35333 := rs (se 4 (by rfl) ⟨3312, by rfl⟩) (B 6625 (by norm_num) ⟨3312, by rfl⟩ (by norm_num))
theorem R68117 : Reach 68117 := rs (se 6 (by rfl) ⟨1596, by rfl⟩) (B 3193 (by norm_num) ⟨1596, by rfl⟩ (by norm_num))
theorem R35477 : Reach 35477 := rs (se 6 (by rfl) ⟨831, by rfl⟩) (B 1663 (by norm_num) ⟨831, by rfl⟩ (by norm_num))
theorem R35573 : Reach 35573 := rs (se 5 (by rfl) ⟨1667, by rfl⟩) (B 3335 (by norm_num) ⟨1667, by rfl⟩ (by norm_num))
theorem R35621 : Reach 35621 := rs (se 4 (by rfl) ⟨3339, by rfl⟩) (B 6679 (by norm_num) ⟨3339, by rfl⟩ (by norm_num))
theorem R35653 : Reach 35653 := rs (se 4 (by rfl) ⟨3342, by rfl⟩) (B 6685 (by norm_num) ⟨3342, by rfl⟩ (by norm_num))
theorem R35765 : Reach 35765 := rs (se 5 (by rfl) ⟨1676, by rfl⟩) (B 3353 (by norm_num) ⟨1676, by rfl⟩ (by norm_num))
theorem R35797 : Reach 35797 := rs (se 7 (by rfl) ⟨419, by rfl⟩) (B 839 (by norm_num) ⟨419, by rfl⟩ (by norm_num))
theorem R35909 : Reach 35909 := rs (se 4 (by rfl) ⟨3366, by rfl⟩) (B 6733 (by norm_num) ⟨3366, by rfl⟩ (by norm_num))
theorem R35957 : Reach 35957 := rs (se 5 (by rfl) ⟨1685, by rfl⟩) (B 3371 (by norm_num) ⟨1685, by rfl⟩ (by norm_num))
theorem R68789 : Reach 68789 := rs (se 5 (by rfl) ⟨3224, by rfl⟩) (B 6449 (by norm_num) ⟨3224, by rfl⟩ (by norm_num))
theorem R36053 : Reach 36053 := rs (se 7 (by rfl) ⟨422, by rfl⟩) (B 845 (by norm_num) ⟨422, by rfl⟩ (by norm_num))
theorem R36085 : Reach 36085 := rs (se 5 (by rfl) ⟨1691, by rfl⟩) (B 3383 (by norm_num) ⟨1691, by rfl⟩ (by norm_num))
theorem R36101 : Reach 36101 := rs (se 4 (by rfl) ⟨3384, by rfl⟩) (B 6769 (by norm_num) ⟨3384, by rfl⟩ (by norm_num))
theorem R36197 : Reach 36197 := rs (se 4 (by rfl) ⟨3393, by rfl⟩) (B 6787 (by norm_num) ⟨3393, by rfl⟩ (by norm_num))
theorem R36325 : Reach 36325 := rs (se 4 (by rfl) ⟨3405, by rfl⟩) (B 6811 (by norm_num) ⟨3405, by rfl⟩ (by norm_num))
theorem R36341 : Reach 36341 := rs (se 5 (by rfl) ⟨1703, by rfl⟩) (B 3407 (by norm_num) ⟨1703, by rfl⟩ (by norm_num))
theorem R36389 : Reach 36389 := rs (se 4 (by rfl) ⟨3411, by rfl⟩) (B 6823 (by norm_num) ⟨3411, by rfl⟩ (by norm_num))
theorem R69173 : Reach 69173 := rs (se 5 (by rfl) ⟨3242, by rfl⟩) (B 6485 (by norm_num) ⟨3242, by rfl⟩ (by norm_num))
theorem R102005 : Reach 102005 := rs (se 5 (by rfl) ⟨4781, by rfl⟩) (B 9563 (by norm_num) ⟨4781, by rfl⟩ (by norm_num))
theorem R36485 : Reach 36485 := rs (se 4 (by rfl) ⟨3420, by rfl⟩) (B 6841 (by norm_num) ⟨3420, by rfl⟩ (by norm_num))
theorem R36629 : Reach 36629 := rs (se 6 (by rfl) ⟨858, by rfl⟩) (B 1717 (by norm_num) ⟨858, by rfl⟩ (by norm_num))
theorem R69461 : Reach 69461 := rs (se 9 (by rfl) ⟨203, by rfl⟩) (B 407 (by norm_num) ⟨203, by rfl⟩ (by norm_num))
theorem R36773 : Reach 36773 := rs (se 4 (by rfl) ⟨3447, by rfl⟩) (B 6895 (by norm_num) ⟨3447, by rfl⟩ (by norm_num))
theorem R36917 : Reach 36917 := rs (se 5 (by rfl) ⟨1730, by rfl⟩) (B 3461 (by norm_num) ⟨1730, by rfl⟩ (by norm_num))
theorem R37061 : Reach 37061 := rs (se 4 (by rfl) ⟨3474, by rfl⟩) (B 6949 (by norm_num) ⟨3474, by rfl⟩ (by norm_num))
theorem R37205 : Reach 37205 := rs (se 10 (by rfl) ⟨54, by rfl⟩) (B 109 (by norm_num) ⟨54, by rfl⟩ (by norm_num))
theorem R37349 : Reach 37349 := rs (se 4 (by rfl) ⟨3501, by rfl⟩) (B 7003 (by norm_num) ⟨3501, by rfl⟩ (by norm_num))
theorem R37381 : Reach 37381 := rs (se 4 (by rfl) ⟨3504, by rfl⟩) (B 7009 (by norm_num) ⟨3504, by rfl⟩ (by norm_num))
theorem R37493 : Reach 37493 := rs (se 5 (by rfl) ⟨1757, by rfl⟩) (B 3515 (by norm_num) ⟨1757, by rfl⟩ (by norm_num))
theorem R37589 : Reach 37589 := rs (se 7 (by rfl) ⟨440, by rfl⟩) (B 881 (by norm_num) ⟨440, by rfl⟩ (by norm_num))
theorem R37637 : Reach 37637 := rs (se 4 (by rfl) ⟨3528, by rfl⟩) (B 7057 (by norm_num) ⟨3528, by rfl⟩ (by norm_num))
theorem R37685 : Reach 37685 := rs (se 5 (by rfl) ⟨1766, by rfl⟩) (B 3533 (by norm_num) ⟨1766, by rfl⟩ (by norm_num))
theorem R299861 : Reach 299861 := rs (se 9 (by rfl) ⟨878, by rfl⟩) (B 1757 (by norm_num) ⟨878, by rfl⟩ (by norm_num))
theorem R37781 : Reach 37781 := rs (se 6 (by rfl) ⟨885, by rfl⟩) (B 1771 (by norm_num) ⟨885, by rfl⟩ (by norm_num))
theorem R37829 : Reach 37829 := rs (se 4 (by rfl) ⟨3546, by rfl⟩) (B 7093 (by norm_num) ⟨3546, by rfl⟩ (by norm_num))
theorem R37877 : Reach 37877 := rs (se 5 (by rfl) ⟨1775, by rfl⟩) (B 3551 (by norm_num) ⟨1775, by rfl⟩ (by norm_num))
theorem R37925 : Reach 37925 := rs (se 4 (by rfl) ⟨3555, by rfl⟩) (B 7111 (by norm_num) ⟨3555, by rfl⟩ (by norm_num))
theorem R38069 : Reach 38069 := rs (se 5 (by rfl) ⟨1784, by rfl⟩) (B 3569 (by norm_num) ⟨1784, by rfl⟩ (by norm_num))
theorem R38117 : Reach 38117 := rs (se 4 (by rfl) ⟨3573, by rfl⟩) (B 7147 (by norm_num) ⟨3573, by rfl⟩ (by norm_num))
theorem R38213 : Reach 38213 := rs (se 4 (by rfl) ⟨3582, by rfl⟩) (B 7165 (by norm_num) ⟨3582, by rfl⟩ (by norm_num))
theorem R136565 : Reach 136565 := rs (se 5 (by rfl) ⟨6401, by rfl⟩) (B 12803 (by norm_num) ⟨6401, by rfl⟩ (by norm_num))
theorem R38341 : Reach 38341 := rs (se 4 (by rfl) ⟨3594, by rfl⟩) (B 7189 (by norm_num) ⟨3594, by rfl⟩ (by norm_num))
theorem R38357 : Reach 38357 := rs (se 7 (by rfl) ⟨449, by rfl⟩) (B 899 (by norm_num) ⟨449, by rfl⟩ (by norm_num))
theorem R38501 : Reach 38501 := rs (se 4 (by rfl) ⟨3609, by rfl⟩) (B 7219 (by norm_num) ⟨3609, by rfl⟩ (by norm_num))
theorem R71381 : Reach 71381 := rs (se 7 (by rfl) ⟨836, by rfl⟩) (B 1673 (by norm_num) ⟨836, by rfl⟩ (by norm_num))
theorem R38645 : Reach 38645 := rs (se 5 (by rfl) ⟨1811, by rfl⟩) (B 3623 (by norm_num) ⟨1811, by rfl⟩ (by norm_num))
theorem R38677 : Reach 38677 := rs (se 6 (by rfl) ⟨906, by rfl⟩) (B 1813 (by norm_num) ⟨906, by rfl⟩ (by norm_num))
theorem R38789 : Reach 38789 := rs (se 4 (by rfl) ⟨3636, by rfl⟩) (B 7273 (by norm_num) ⟨3636, by rfl⟩ (by norm_num))
theorem R268181 : Reach 268181 := rs (se 6 (by rfl) ⟨6285, by rfl⟩) (B 12571 (by norm_num) ⟨6285, by rfl⟩ (by norm_num))
theorem R38933 : Reach 38933 := rs (se 6 (by rfl) ⟨912, by rfl⟩) (B 1825 (by norm_num) ⟨912, by rfl⟩ (by norm_num))
theorem R38981 : Reach 38981 := rs (se 4 (by rfl) ⟨3654, by rfl⟩) (B 7309 (by norm_num) ⟨3654, by rfl⟩ (by norm_num))
theorem R71765 : Reach 71765 := rs (se 8 (by rfl) ⟨420, by rfl⟩) (B 841 (by norm_num) ⟨420, by rfl⟩ (by norm_num))
theorem R39077 : Reach 39077 := rs (se 4 (by rfl) ⟨3663, by rfl⟩) (B 7327 (by norm_num) ⟨3663, by rfl⟩ (by norm_num))
theorem R39221 : Reach 39221 := rs (se 5 (by rfl) ⟨1838, by rfl⟩) (B 3677 (by norm_num) ⟨1838, by rfl⟩ (by norm_num))
theorem R104885 : Reach 104885 := rs (se 5 (by rfl) ⟨4916, by rfl⟩) (B 9833 (by norm_num) ⟨4916, by rfl⟩ (by norm_num))
theorem R39365 : Reach 39365 := rs (se 4 (by rfl) ⟨3690, by rfl⟩) (B 7381 (by norm_num) ⟨3690, by rfl⟩ (by norm_num))
theorem R39509 : Reach 39509 := rs (se 8 (by rfl) ⟨231, by rfl⟩) (B 463 (by norm_num) ⟨231, by rfl⟩ (by norm_num))
theorem R39541 : Reach 39541 := rs (se 5 (by rfl) ⟨1853, by rfl⟩) (B 3707 (by norm_num) ⟨1853, by rfl⟩ (by norm_num))
theorem R39653 : Reach 39653 := rs (se 4 (by rfl) ⟨3717, by rfl⟩) (B 7435 (by norm_num) ⟨3717, by rfl⟩ (by norm_num))
theorem R39685 : Reach 39685 := rs (se 4 (by rfl) ⟨3720, by rfl⟩) (B 7441 (by norm_num) ⟨3720, by rfl⟩ (by norm_num))
theorem R39797 : Reach 39797 := rs (se 5 (by rfl) ⟨1865, by rfl⟩) (B 3731 (by norm_num) ⟨1865, by rfl⟩ (by norm_num))
theorem R39845 : Reach 39845 := rs (se 4 (by rfl) ⟨3735, by rfl⟩) (B 7471 (by norm_num) ⟨3735, by rfl⟩ (by norm_num))
theorem R105461 : Reach 105461 := rs (se 5 (by rfl) ⟨4943, by rfl⟩) (B 9887 (by norm_num) ⟨4943, by rfl⟩ (by norm_num))
theorem R39941 : Reach 39941 := rs (se 4 (by rfl) ⟨3744, by rfl⟩) (B 7489 (by norm_num) ⟨3744, by rfl⟩ (by norm_num))
theorem R39973 : Reach 39973 := rs (se 4 (by rfl) ⟨3747, by rfl⟩) (B 7495 (by norm_num) ⟨3747, by rfl⟩ (by norm_num))
theorem R40085 : Reach 40085 := rs (se 6 (by rfl) ⟨939, by rfl⟩) (B 1879 (by norm_num) ⟨939, by rfl⟩ (by norm_num))
theorem R40229 : Reach 40229 := rs (se 4 (by rfl) ⟨3771, by rfl⟩) (B 7543 (by norm_num) ⟨3771, by rfl⟩ (by norm_num))
theorem R40277 : Reach 40277 := rs (se 11 (by rfl) ⟨29, by rfl⟩) (B 59 (by norm_num) ⟨29, by rfl⟩ (by norm_num))
theorem R40373 : Reach 40373 := rs (se 5 (by rfl) ⟨1892, by rfl⟩) (B 3785 (by norm_num) ⟨1892, by rfl⟩ (by norm_num))
theorem R40517 : Reach 40517 := rs (se 4 (by rfl) ⟨3798, by rfl⟩) (B 7597 (by norm_num) ⟨3798, by rfl⟩ (by norm_num))
theorem R106069 : Reach 106069 := rs (se 8 (by rfl) ⟨621, by rfl⟩) (B 1243 (by norm_num) ⟨621, by rfl⟩ (by norm_num))
theorem R40661 : Reach 40661 := rs (se 7 (by rfl) ⟨476, by rfl⟩) (B 953 (by norm_num) ⟨476, by rfl⟩ (by norm_num))
theorem R73493 : Reach 73493 := rs (se 6 (by rfl) ⟨1722, by rfl⟩) (B 3445 (by norm_num) ⟨1722, by rfl⟩ (by norm_num))
theorem R40805 : Reach 40805 := rs (se 4 (by rfl) ⟨3825, by rfl⟩) (B 7651 (by norm_num) ⟨3825, by rfl⟩ (by norm_num))
theorem R40949 : Reach 40949 := rs (se 5 (by rfl) ⟨1919, by rfl⟩) (B 3839 (by norm_num) ⟨1919, by rfl⟩ (by norm_num))
theorem R40981 : Reach 40981 := rs (se 6 (by rfl) ⟨960, by rfl⟩) (B 1921 (by norm_num) ⟨960, by rfl⟩ (by norm_num))
theorem R73781 : Reach 73781 := rs (se 5 (by rfl) ⟨3458, by rfl⟩) (B 6917 (by norm_num) ⟨3458, by rfl⟩ (by norm_num))
theorem R41093 : Reach 41093 := rs (se 4 (by rfl) ⟨3852, by rfl⟩) (B 7705 (by norm_num) ⟨3852, by rfl⟩ (by norm_num))
theorem R41237 : Reach 41237 := rs (se 6 (by rfl) ⟨966, by rfl⟩) (B 1933 (by norm_num) ⟨966, by rfl⟩ (by norm_num))
theorem R41269 : Reach 41269 := rs (se 5 (by rfl) ⟨1934, by rfl⟩) (B 3869 (by norm_num) ⟨1934, by rfl⟩ (by norm_num))
theorem R41381 : Reach 41381 := rs (se 4 (by rfl) ⟨3879, by rfl⟩) (B 7759 (by norm_num) ⟨3879, by rfl⟩ (by norm_num))
theorem R41525 : Reach 41525 := rs (se 5 (by rfl) ⟨1946, by rfl⟩) (B 3893 (by norm_num) ⟨1946, by rfl⟩ (by norm_num))
theorem R41573 : Reach 41573 := rs (se 4 (by rfl) ⟨3897, by rfl⟩) (B 7795 (by norm_num) ⟨3897, by rfl⟩ (by norm_num))
theorem R74357 : Reach 74357 := rs (se 5 (by rfl) ⟨3485, by rfl⟩) (B 6971 (by norm_num) ⟨3485, by rfl⟩ (by norm_num))
theorem R107189 : Reach 107189 := rs (se 5 (by rfl) ⟨5024, by rfl⟩) (B 10049 (by norm_num) ⟨5024, by rfl⟩ (by norm_num))
theorem R41669 : Reach 41669 := rs (se 4 (by rfl) ⟨3906, by rfl⟩) (B 7813 (by norm_num) ⟨3906, by rfl⟩ (by norm_num))
theorem R41813 : Reach 41813 := rs (se 9 (by rfl) ⟨122, by rfl⟩) (B 245 (by norm_num) ⟨122, by rfl⟩ (by norm_num))
theorem R41957 : Reach 41957 := rs (se 4 (by rfl) ⟨3933, by rfl⟩) (B 7867 (by norm_num) ⟨3933, by rfl⟩ (by norm_num))
theorem R74837 : Reach 74837 := rs (se 8 (by rfl) ⟨438, by rfl⟩) (B 877 (by norm_num) ⟨438, by rfl⟩ (by norm_num))
theorem R42101 : Reach 42101 := rs (se 5 (by rfl) ⟨1973, by rfl⟩) (B 3947 (by norm_num) ⟨1973, by rfl⟩ (by norm_num))
theorem R74965 : Reach 74965 := rs (se 7 (by rfl) ⟨878, by rfl⟩) (B 1757 (by norm_num) ⟨878, by rfl⟩ (by norm_num))
theorem R42245 : Reach 42245 := rs (se 4 (by rfl) ⟨3960, by rfl⟩) (B 7921 (by norm_num) ⟨3960, by rfl⟩ (by norm_num))
theorem R42277 : Reach 42277 := rs (se 4 (by rfl) ⟨3963, by rfl⟩) (B 7927 (by norm_num) ⟨3963, by rfl⟩ (by norm_num))
theorem R42373 : Reach 42373 := rs (se 4 (by rfl) ⟨3972, by rfl⟩) (B 7945 (by norm_num) ⟨3972, by rfl⟩ (by norm_num))
theorem R42389 : Reach 42389 := rs (se 6 (by rfl) ⟨993, by rfl⟩) (B 1987 (by norm_num) ⟨993, by rfl⟩ (by norm_num))
theorem R108053 : Reach 108053 := rs (se 6 (by rfl) ⟨2532, by rfl⟩) (B 5065 (by norm_num) ⟨2532, by rfl⟩ (by norm_num))
theorem R42533 : Reach 42533 := rs (se 4 (by rfl) ⟨3987, by rfl⟩) (B 7975 (by norm_num) ⟨3987, by rfl⟩ (by norm_num))
theorem R42565 : Reach 42565 := rs (se 4 (by rfl) ⟨3990, by rfl⟩) (B 7981 (by norm_num) ⟨3990, by rfl⟩ (by norm_num))
theorem R42677 : Reach 42677 := rs (se 5 (by rfl) ⟨2000, by rfl⟩) (B 4001 (by norm_num) ⟨2000, by rfl⟩ (by norm_num))
theorem R206549 : Reach 206549 := rs (se 7 (by rfl) ⟨2420, by rfl⟩) (B 4841 (by norm_num) ⟨2420, by rfl⟩ (by norm_num))
theorem R42821 : Reach 42821 := rs (se 4 (by rfl) ⟨4014, by rfl⟩) (B 8029 (by norm_num) ⟨4014, by rfl⟩ (by norm_num))
theorem R42869 : Reach 42869 := rs (se 5 (by rfl) ⟨2009, by rfl⟩) (B 4019 (by norm_num) ⟨2009, by rfl⟩ (by norm_num))
theorem R42965 : Reach 42965 := rs (se 7 (by rfl) ⟨503, by rfl⟩) (B 1007 (by norm_num) ⟨503, by rfl⟩ (by norm_num))
theorem R43109 : Reach 43109 := rs (se 4 (by rfl) ⟨4041, by rfl⟩) (B 8083 (by norm_num) ⟨4041, by rfl⟩ (by norm_num))
theorem R43253 : Reach 43253 := rs (se 5 (by rfl) ⟨2027, by rfl⟩) (B 4055 (by norm_num) ⟨2027, by rfl⟩ (by norm_num))
theorem R43397 : Reach 43397 := rs (se 4 (by rfl) ⟨4068, by rfl⟩) (B 8137 (by norm_num) ⟨4068, by rfl⟩ (by norm_num))
theorem R43541 : Reach 43541 := rs (se 6 (by rfl) ⟨1020, by rfl⟩) (B 2041 (by norm_num) ⟨1020, by rfl⟩ (by norm_num))
theorem R43573 : Reach 43573 := rs (se 5 (by rfl) ⟨2042, by rfl⟩) (B 4085 (by norm_num) ⟨2042, by rfl⟩ (by norm_num))
theorem R43685 : Reach 43685 := rs (se 4 (by rfl) ⟨4095, by rfl⟩) (B 8191 (by norm_num) ⟨4095, by rfl⟩ (by norm_num))
theorem R43829 : Reach 43829 := rs (se 5 (by rfl) ⟨2054, by rfl⟩) (B 4109 (by norm_num) ⟨2054, by rfl⟩ (by norm_num))
theorem R43861 : Reach 43861 := rs (se 9 (by rfl) ⟨128, by rfl⟩) (B 257 (by norm_num) ⟨128, by rfl⟩ (by norm_num))
theorem R43877 : Reach 43877 := rs (se 4 (by rfl) ⟨4113, by rfl⟩) (B 8227 (by norm_num) ⟨4113, by rfl⟩ (by norm_num))
theorem R43973 : Reach 43973 := rs (se 4 (by rfl) ⟨4122, by rfl⟩) (B 8245 (by norm_num) ⟨4122, by rfl⟩ (by norm_num))
theorem R44117 : Reach 44117 := rs (se 8 (by rfl) ⟨258, by rfl⟩) (B 517 (by norm_num) ⟨258, by rfl⟩ (by norm_num))
theorem R44165 : Reach 44165 := rs (se 4 (by rfl) ⟨4140, by rfl⟩) (B 8281 (by norm_num) ⟨4140, by rfl⟩ (by norm_num))
theorem R76949 : Reach 76949 := rs (se 6 (by rfl) ⟨1803, by rfl⟩) (B 3607 (by norm_num) ⟨1803, by rfl⟩ (by norm_num))
theorem R44261 : Reach 44261 := rs (se 4 (by rfl) ⟨4149, by rfl⟩) (B 8299 (by norm_num) ⟨4149, by rfl⟩ (by norm_num))
theorem R44405 : Reach 44405 := rs (se 5 (by rfl) ⟨2081, by rfl⟩) (B 4163 (by norm_num) ⟨2081, by rfl⟩ (by norm_num))
theorem R44549 : Reach 44549 := rs (se 4 (by rfl) ⟨4176, by rfl⟩) (B 8353 (by norm_num) ⟨4176, by rfl⟩ (by norm_num))
theorem R77365 : Reach 77365 := rs (se 5 (by rfl) ⟨3626, by rfl⟩) (B 7253 (by norm_num) ⟨3626, by rfl⟩ (by norm_num))
theorem R77429 : Reach 77429 := rs (se 5 (by rfl) ⟨3629, by rfl⟩) (B 7259 (by norm_num) ⟨3629, by rfl⟩ (by norm_num))
theorem R44693 : Reach 44693 := rs (se 6 (by rfl) ⟨1047, by rfl⟩) (B 2095 (by norm_num) ⟨1047, by rfl⟩ (by norm_num))
theorem R110261 : Reach 110261 := rs (se 5 (by rfl) ⟨5168, by rfl⟩) (B 10337 (by norm_num) ⟨5168, by rfl⟩ (by norm_num))
theorem R44837 : Reach 44837 := rs (se 4 (by rfl) ⟨4203, by rfl⟩) (B 8407 (by norm_num) ⟨4203, by rfl⟩ (by norm_num))
theorem R44981 : Reach 44981 := rs (se 5 (by rfl) ⟨2108, by rfl⟩) (B 4217 (by norm_num) ⟨2108, by rfl⟩ (by norm_num))
theorem R45157 : Reach 45157 := rs (se 4 (by rfl) ⟨4233, by rfl⟩) (B 8467 (by norm_num) ⟨4233, by rfl⟩ (by norm_num))
theorem R45269 : Reach 45269 := rs (se 7 (by rfl) ⟨530, by rfl⟩) (B 1061 (by norm_num) ⟨530, by rfl⟩ (by norm_num))
theorem R45413 : Reach 45413 := rs (se 4 (by rfl) ⟨4257, by rfl⟩) (B 8515 (by norm_num) ⟨4257, by rfl⟩ (by norm_num))
theorem R45461 : Reach 45461 := rs (se 6 (by rfl) ⟨1065, by rfl⟩) (B 2131 (by norm_num) ⟨1065, by rfl⟩ (by norm_num))
theorem R12825 : Reach 12825 := rs (se 2 (by rfl) ⟨4809, by rfl⟩) (B 9619 (by norm_num) ⟨4809, by rfl⟩ (by norm_num))
theorem R12829 : Reach 12829 := rs (se 3 (by rfl) ⟨2405, by rfl⟩) (B 4811 (by norm_num) ⟨2405, by rfl⟩ (by norm_num))
theorem R12833 : Reach 12833 := rs (se 2 (by rfl) ⟨4812, by rfl⟩) (B 9625 (by norm_num) ⟨4812, by rfl⟩ (by norm_num))
theorem R12837 : Reach 12837 := rs (se 4 (by rfl) ⟨1203, by rfl⟩) (B 2407 (by norm_num) ⟨1203, by rfl⟩ (by norm_num))
theorem R12841 : Reach 12841 := rs (se 2 (by rfl) ⟨4815, by rfl⟩) (B 9631 (by norm_num) ⟨4815, by rfl⟩ (by norm_num))
theorem R12845 : Reach 12845 := rs (se 3 (by rfl) ⟨2408, by rfl⟩) (B 4817 (by norm_num) ⟨2408, by rfl⟩ (by norm_num))
theorem R12849 : Reach 12849 := rs (se 2 (by rfl) ⟨4818, by rfl⟩) (B 9637 (by norm_num) ⟨4818, by rfl⟩ (by norm_num))
theorem R12853 : Reach 12853 := rs (se 5 (by rfl) ⟨602, by rfl⟩) (B 1205 (by norm_num) ⟨602, by rfl⟩ (by norm_num))
theorem R12857 : Reach 12857 := rs (se 2 (by rfl) ⟨4821, by rfl⟩) (B 9643 (by norm_num) ⟨4821, by rfl⟩ (by norm_num))
theorem R12861 : Reach 12861 := rs (se 3 (by rfl) ⟨2411, by rfl⟩) (B 4823 (by norm_num) ⟨2411, by rfl⟩ (by norm_num))
theorem R12865 : Reach 12865 := rs (se 2 (by rfl) ⟨4824, by rfl⟩) (B 9649 (by norm_num) ⟨4824, by rfl⟩ (by norm_num))
theorem R12869 : Reach 12869 := rs (se 4 (by rfl) ⟨1206, by rfl⟩) (B 2413 (by norm_num) ⟨1206, by rfl⟩ (by norm_num))
theorem R12873 : Reach 12873 := rs (se 2 (by rfl) ⟨4827, by rfl⟩) (B 9655 (by norm_num) ⟨4827, by rfl⟩ (by norm_num))
theorem R12877 : Reach 12877 := rs (se 3 (by rfl) ⟨2414, by rfl⟩) (B 4829 (by norm_num) ⟨2414, by rfl⟩ (by norm_num))
theorem R12881 : Reach 12881 := rs (se 2 (by rfl) ⟨4830, by rfl⟩) (B 9661 (by norm_num) ⟨4830, by rfl⟩ (by norm_num))
theorem R12885 : Reach 12885 := rs (se 8 (by rfl) ⟨75, by rfl⟩) (B 151 (by norm_num) ⟨75, by rfl⟩ (by norm_num))
theorem R12889 : Reach 12889 := rs (se 2 (by rfl) ⟨4833, by rfl⟩) (B 9667 (by norm_num) ⟨4833, by rfl⟩ (by norm_num))
theorem R12893 : Reach 12893 := rs (se 3 (by rfl) ⟨2417, by rfl⟩) (B 4835 (by norm_num) ⟨2417, by rfl⟩ (by norm_num))
theorem R12897 : Reach 12897 := rs (se 2 (by rfl) ⟨4836, by rfl⟩) (B 9673 (by norm_num) ⟨4836, by rfl⟩ (by norm_num))
theorem R12901 : Reach 12901 := rs (se 4 (by rfl) ⟨1209, by rfl⟩) (B 2419 (by norm_num) ⟨1209, by rfl⟩ (by norm_num))
theorem R12905 : Reach 12905 := rs (se 2 (by rfl) ⟨4839, by rfl⟩) (B 9679 (by norm_num) ⟨4839, by rfl⟩ (by norm_num))
theorem R12909 : Reach 12909 := rs (se 3 (by rfl) ⟨2420, by rfl⟩) (B 4841 (by norm_num) ⟨2420, by rfl⟩ (by norm_num))
theorem R12913 : Reach 12913 := rs (se 2 (by rfl) ⟨4842, by rfl⟩) (B 9685 (by norm_num) ⟨4842, by rfl⟩ (by norm_num))
theorem R12917 : Reach 12917 := rs (se 5 (by rfl) ⟨605, by rfl⟩) (B 1211 (by norm_num) ⟨605, by rfl⟩ (by norm_num))
theorem R12921 : Reach 12921 := rs (se 2 (by rfl) ⟨4845, by rfl⟩) (B 9691 (by norm_num) ⟨4845, by rfl⟩ (by norm_num))
theorem R12925 : Reach 12925 := rs (se 3 (by rfl) ⟨2423, by rfl⟩) (B 4847 (by norm_num) ⟨2423, by rfl⟩ (by norm_num))
theorem R12929 : Reach 12929 := rs (se 2 (by rfl) ⟨4848, by rfl⟩) (B 9697 (by norm_num) ⟨4848, by rfl⟩ (by norm_num))
theorem R12933 : Reach 12933 := rs (se 4 (by rfl) ⟨1212, by rfl⟩) (B 2425 (by norm_num) ⟨1212, by rfl⟩ (by norm_num))
theorem R12937 : Reach 12937 := rs (se 2 (by rfl) ⟨4851, by rfl⟩) (B 9703 (by norm_num) ⟨4851, by rfl⟩ (by norm_num))
theorem R12941 : Reach 12941 := rs (se 3 (by rfl) ⟨2426, by rfl⟩) (B 4853 (by norm_num) ⟨2426, by rfl⟩ (by norm_num))
theorem R12945 : Reach 12945 := rs (se 2 (by rfl) ⟨4854, by rfl⟩) (B 9709 (by norm_num) ⟨4854, by rfl⟩ (by norm_num))
theorem R12949 : Reach 12949 := rs (se 6 (by rfl) ⟨303, by rfl⟩) (B 607 (by norm_num) ⟨303, by rfl⟩ (by norm_num))
theorem R12953 : Reach 12953 := rs (se 2 (by rfl) ⟨4857, by rfl⟩) (B 9715 (by norm_num) ⟨4857, by rfl⟩ (by norm_num))
theorem R12957 : Reach 12957 := rs (se 3 (by rfl) ⟨2429, by rfl⟩) (B 4859 (by norm_num) ⟨2429, by rfl⟩ (by norm_num))
theorem R12961 : Reach 12961 := rs (se 2 (by rfl) ⟨4860, by rfl⟩) (B 9721 (by norm_num) ⟨4860, by rfl⟩ (by norm_num))
theorem R12965 : Reach 12965 := rs (se 4 (by rfl) ⟨1215, by rfl⟩) (B 2431 (by norm_num) ⟨1215, by rfl⟩ (by norm_num))
theorem R12969 : Reach 12969 := rs (se 2 (by rfl) ⟨4863, by rfl⟩) (B 9727 (by norm_num) ⟨4863, by rfl⟩ (by norm_num))
theorem R12973 : Reach 12973 := rs (se 3 (by rfl) ⟨2432, by rfl⟩) (B 4865 (by norm_num) ⟨2432, by rfl⟩ (by norm_num))
theorem R12977 : Reach 12977 := rs (se 2 (by rfl) ⟨4866, by rfl⟩) (B 9733 (by norm_num) ⟨4866, by rfl⟩ (by norm_num))
theorem R12981 : Reach 12981 := rs (se 5 (by rfl) ⟨608, by rfl⟩) (B 1217 (by norm_num) ⟨608, by rfl⟩ (by norm_num))
theorem R12985 : Reach 12985 := rs (se 2 (by rfl) ⟨4869, by rfl⟩) (B 9739 (by norm_num) ⟨4869, by rfl⟩ (by norm_num))
theorem R12989 : Reach 12989 := rs (se 3 (by rfl) ⟨2435, by rfl⟩) (B 4871 (by norm_num) ⟨2435, by rfl⟩ (by norm_num))
theorem R12993 : Reach 12993 := rs (se 2 (by rfl) ⟨4872, by rfl⟩) (B 9745 (by norm_num) ⟨4872, by rfl⟩ (by norm_num))
theorem R12997 : Reach 12997 := rs (se 4 (by rfl) ⟨1218, by rfl⟩) (B 2437 (by norm_num) ⟨1218, by rfl⟩ (by norm_num))
theorem R13001 : Reach 13001 := rs (se 2 (by rfl) ⟨4875, by rfl⟩) (B 9751 (by norm_num) ⟨4875, by rfl⟩ (by norm_num))
theorem R13005 : Reach 13005 := rs (se 3 (by rfl) ⟨2438, by rfl⟩) (B 4877 (by norm_num) ⟨2438, by rfl⟩ (by norm_num))
theorem R13009 : Reach 13009 := rs (se 2 (by rfl) ⟨4878, by rfl⟩) (B 9757 (by norm_num) ⟨4878, by rfl⟩ (by norm_num))
theorem R13013 : Reach 13013 := rs (se 7 (by rfl) ⟨152, by rfl⟩) (B 305 (by norm_num) ⟨152, by rfl⟩ (by norm_num))
theorem R13017 : Reach 13017 := rs (se 2 (by rfl) ⟨4881, by rfl⟩) (B 9763 (by norm_num) ⟨4881, by rfl⟩ (by norm_num))
theorem R13021 : Reach 13021 := rs (se 3 (by rfl) ⟨2441, by rfl⟩) (B 4883 (by norm_num) ⟨2441, by rfl⟩ (by norm_num))
theorem R13025 : Reach 13025 := rs (se 2 (by rfl) ⟨4884, by rfl⟩) (B 9769 (by norm_num) ⟨4884, by rfl⟩ (by norm_num))
theorem R13029 : Reach 13029 := rs (se 4 (by rfl) ⟨1221, by rfl⟩) (B 2443 (by norm_num) ⟨1221, by rfl⟩ (by norm_num))
theorem R13033 : Reach 13033 := rs (se 2 (by rfl) ⟨4887, by rfl⟩) (B 9775 (by norm_num) ⟨4887, by rfl⟩ (by norm_num))
theorem R13037 : Reach 13037 := rs (se 3 (by rfl) ⟨2444, by rfl⟩) (B 4889 (by norm_num) ⟨2444, by rfl⟩ (by norm_num))
theorem R13041 : Reach 13041 := rs (se 2 (by rfl) ⟨4890, by rfl⟩) (B 9781 (by norm_num) ⟨4890, by rfl⟩ (by norm_num))
theorem R13045 : Reach 13045 := rs (se 5 (by rfl) ⟨611, by rfl⟩) (B 1223 (by norm_num) ⟨611, by rfl⟩ (by norm_num))
theorem R13049 : Reach 13049 := rs (se 2 (by rfl) ⟨4893, by rfl⟩) (B 9787 (by norm_num) ⟨4893, by rfl⟩ (by norm_num))
theorem R13053 : Reach 13053 := rs (se 3 (by rfl) ⟨2447, by rfl⟩) (B 4895 (by norm_num) ⟨2447, by rfl⟩ (by norm_num))
theorem R13057 : Reach 13057 := rs (se 2 (by rfl) ⟨4896, by rfl⟩) (B 9793 (by norm_num) ⟨4896, by rfl⟩ (by norm_num))
theorem R13061 : Reach 13061 := rs (se 4 (by rfl) ⟨1224, by rfl⟩) (B 2449 (by norm_num) ⟨1224, by rfl⟩ (by norm_num))
theorem R13065 : Reach 13065 := rs (se 2 (by rfl) ⟨4899, by rfl⟩) (B 9799 (by norm_num) ⟨4899, by rfl⟩ (by norm_num))
theorem R13069 : Reach 13069 := rs (se 3 (by rfl) ⟨2450, by rfl⟩) (B 4901 (by norm_num) ⟨2450, by rfl⟩ (by norm_num))
theorem R13073 : Reach 13073 := rs (se 2 (by rfl) ⟨4902, by rfl⟩) (B 9805 (by norm_num) ⟨4902, by rfl⟩ (by norm_num))
theorem R13077 : Reach 13077 := rs (se 6 (by rfl) ⟨306, by rfl⟩) (B 613 (by norm_num) ⟨306, by rfl⟩ (by norm_num))
theorem R45845 : Reach 45845 := rs (se 6 (by rfl) ⟨1074, by rfl⟩) (B 2149 (by norm_num) ⟨1074, by rfl⟩ (by norm_num))
theorem R13081 : Reach 13081 := rs (se 2 (by rfl) ⟨4905, by rfl⟩) (B 9811 (by norm_num) ⟨4905, by rfl⟩ (by norm_num))
theorem R13085 : Reach 13085 := rs (se 3 (by rfl) ⟨2453, by rfl⟩) (B 4907 (by norm_num) ⟨2453, by rfl⟩ (by norm_num))
theorem R13089 : Reach 13089 := rs (se 2 (by rfl) ⟨4908, by rfl⟩) (B 9817 (by norm_num) ⟨4908, by rfl⟩ (by norm_num))
theorem R13093 : Reach 13093 := rs (se 4 (by rfl) ⟨1227, by rfl⟩) (B 2455 (by norm_num) ⟨1227, by rfl⟩ (by norm_num))
theorem R13097 : Reach 13097 := rs (se 2 (by rfl) ⟨4911, by rfl⟩) (B 9823 (by norm_num) ⟨4911, by rfl⟩ (by norm_num))
theorem R13101 : Reach 13101 := rs (se 3 (by rfl) ⟨2456, by rfl⟩) (B 4913 (by norm_num) ⟨2456, by rfl⟩ (by norm_num))
theorem R13105 : Reach 13105 := rs (se 2 (by rfl) ⟨4914, by rfl⟩) (B 9829 (by norm_num) ⟨4914, by rfl⟩ (by norm_num))
theorem R13109 : Reach 13109 := rs (se 5 (by rfl) ⟨614, by rfl⟩) (B 1229 (by norm_num) ⟨614, by rfl⟩ (by norm_num))
theorem R13113 : Reach 13113 := rs (se 2 (by rfl) ⟨4917, by rfl⟩) (B 9835 (by norm_num) ⟨4917, by rfl⟩ (by norm_num))
theorem R13117 : Reach 13117 := rs (se 3 (by rfl) ⟨2459, by rfl⟩) (B 4919 (by norm_num) ⟨2459, by rfl⟩ (by norm_num))
theorem R13121 : Reach 13121 := rs (se 2 (by rfl) ⟨4920, by rfl⟩) (B 9841 (by norm_num) ⟨4920, by rfl⟩ (by norm_num))
theorem R13125 : Reach 13125 := rs (se 4 (by rfl) ⟨1230, by rfl⟩) (B 2461 (by norm_num) ⟨1230, by rfl⟩ (by norm_num))
theorem R45893 : Reach 45893 := rs (se 4 (by rfl) ⟨4302, by rfl⟩) (B 8605 (by norm_num) ⟨4302, by rfl⟩ (by norm_num))
theorem R13129 : Reach 13129 := rs (se 2 (by rfl) ⟨4923, by rfl⟩) (B 9847 (by norm_num) ⟨4923, by rfl⟩ (by norm_num))
theorem R13133 : Reach 13133 := rs (se 3 (by rfl) ⟨2462, by rfl⟩) (B 4925 (by norm_num) ⟨2462, by rfl⟩ (by norm_num))
theorem R13137 : Reach 13137 := rs (se 2 (by rfl) ⟨4926, by rfl⟩) (B 9853 (by norm_num) ⟨4926, by rfl⟩ (by norm_num))
theorem R13141 : Reach 13141 := rs (se 9 (by rfl) ⟨38, by rfl⟩) (B 77 (by norm_num) ⟨38, by rfl⟩ (by norm_num))
theorem R13145 : Reach 13145 := rs (se 2 (by rfl) ⟨4929, by rfl⟩) (B 9859 (by norm_num) ⟨4929, by rfl⟩ (by norm_num))
theorem R13149 : Reach 13149 := rs (se 3 (by rfl) ⟨2465, by rfl⟩) (B 4931 (by norm_num) ⟨2465, by rfl⟩ (by norm_num))
theorem R13153 : Reach 13153 := rs (se 2 (by rfl) ⟨4932, by rfl⟩) (B 9865 (by norm_num) ⟨4932, by rfl⟩ (by norm_num))
theorem R13157 : Reach 13157 := rs (se 4 (by rfl) ⟨1233, by rfl⟩) (B 2467 (by norm_num) ⟨1233, by rfl⟩ (by norm_num))
theorem R13161 : Reach 13161 := rs (se 2 (by rfl) ⟨4935, by rfl⟩) (B 9871 (by norm_num) ⟨4935, by rfl⟩ (by norm_num))
theorem R13165 : Reach 13165 := rs (se 3 (by rfl) ⟨2468, by rfl⟩) (B 4937 (by norm_num) ⟨2468, by rfl⟩ (by norm_num))
theorem R13169 : Reach 13169 := rs (se 2 (by rfl) ⟨4938, by rfl⟩) (B 9877 (by norm_num) ⟨4938, by rfl⟩ (by norm_num))
theorem R13173 : Reach 13173 := rs (se 5 (by rfl) ⟨617, by rfl⟩) (B 1235 (by norm_num) ⟨617, by rfl⟩ (by norm_num))
theorem R13177 : Reach 13177 := rs (se 2 (by rfl) ⟨4941, by rfl⟩) (B 9883 (by norm_num) ⟨4941, by rfl⟩ (by norm_num))
theorem R13181 : Reach 13181 := rs (se 3 (by rfl) ⟨2471, by rfl⟩) (B 4943 (by norm_num) ⟨2471, by rfl⟩ (by norm_num))
theorem R13185 : Reach 13185 := rs (se 2 (by rfl) ⟨4944, by rfl⟩) (B 9889 (by norm_num) ⟨4944, by rfl⟩ (by norm_num))
theorem R13189 : Reach 13189 := rs (se 4 (by rfl) ⟨1236, by rfl⟩) (B 2473 (by norm_num) ⟨1236, by rfl⟩ (by norm_num))
theorem R13193 : Reach 13193 := rs (se 2 (by rfl) ⟨4947, by rfl⟩) (B 9895 (by norm_num) ⟨4947, by rfl⟩ (by norm_num))
theorem R13197 : Reach 13197 := rs (se 3 (by rfl) ⟨2474, by rfl⟩) (B 4949 (by norm_num) ⟨2474, by rfl⟩ (by norm_num))
theorem R13201 : Reach 13201 := rs (se 2 (by rfl) ⟨4950, by rfl⟩) (B 9901 (by norm_num) ⟨4950, by rfl⟩ (by norm_num))
theorem R13205 : Reach 13205 := rs (se 6 (by rfl) ⟨309, by rfl⟩) (B 619 (by norm_num) ⟨309, by rfl⟩ (by norm_num))
theorem R13209 : Reach 13209 := rs (se 2 (by rfl) ⟨4953, by rfl⟩) (B 9907 (by norm_num) ⟨4953, by rfl⟩ (by norm_num))
theorem R13213 : Reach 13213 := rs (se 3 (by rfl) ⟨2477, by rfl⟩) (B 4955 (by norm_num) ⟨2477, by rfl⟩ (by norm_num))
theorem R13217 : Reach 13217 := rs (se 2 (by rfl) ⟨4956, by rfl⟩) (B 9913 (by norm_num) ⟨4956, by rfl⟩ (by norm_num))
theorem R13221 : Reach 13221 := rs (se 4 (by rfl) ⟨1239, by rfl⟩) (B 2479 (by norm_num) ⟨1239, by rfl⟩ (by norm_num))
theorem R13225 : Reach 13225 := rs (se 2 (by rfl) ⟨4959, by rfl⟩) (B 9919 (by norm_num) ⟨4959, by rfl⟩ (by norm_num))
theorem R13229 : Reach 13229 := rs (se 3 (by rfl) ⟨2480, by rfl⟩) (B 4961 (by norm_num) ⟨2480, by rfl⟩ (by norm_num))
theorem R13233 : Reach 13233 := rs (se 2 (by rfl) ⟨4962, by rfl⟩) (B 9925 (by norm_num) ⟨4962, by rfl⟩ (by norm_num))
theorem R13237 : Reach 13237 := rs (se 5 (by rfl) ⟨620, by rfl⟩) (B 1241 (by norm_num) ⟨620, by rfl⟩ (by norm_num))
theorem R13241 : Reach 13241 := rs (se 2 (by rfl) ⟨4965, by rfl⟩) (B 9931 (by norm_num) ⟨4965, by rfl⟩ (by norm_num))
theorem R13245 : Reach 13245 := rs (se 3 (by rfl) ⟨2483, by rfl⟩) (B 4967 (by norm_num) ⟨2483, by rfl⟩ (by norm_num))
theorem R13249 : Reach 13249 := rs (se 2 (by rfl) ⟨4968, by rfl⟩) (B 9937 (by norm_num) ⟨4968, by rfl⟩ (by norm_num))
theorem R13253 : Reach 13253 := rs (se 4 (by rfl) ⟨1242, by rfl⟩) (B 2485 (by norm_num) ⟨1242, by rfl⟩ (by norm_num))
theorem R13257 : Reach 13257 := rs (se 2 (by rfl) ⟨4971, by rfl⟩) (B 9943 (by norm_num) ⟨4971, by rfl⟩ (by norm_num))
theorem R13261 : Reach 13261 := rs (se 3 (by rfl) ⟨2486, by rfl⟩) (B 4973 (by norm_num) ⟨2486, by rfl⟩ (by norm_num))
theorem R13265 : Reach 13265 := rs (se 2 (by rfl) ⟨4974, by rfl⟩) (B 9949 (by norm_num) ⟨4974, by rfl⟩ (by norm_num))
theorem R13269 : Reach 13269 := rs (se 7 (by rfl) ⟨155, by rfl⟩) (B 311 (by norm_num) ⟨155, by rfl⟩ (by norm_num))
theorem R144341 : Reach 144341 := rs (se 7 (by rfl) ⟨1691, by rfl⟩) (B 3383 (by norm_num) ⟨1691, by rfl⟩ (by norm_num))
theorem R13273 : Reach 13273 := rs (se 2 (by rfl) ⟨4977, by rfl⟩) (B 9955 (by norm_num) ⟨4977, by rfl⟩ (by norm_num))
theorem R13277 : Reach 13277 := rs (se 3 (by rfl) ⟨2489, by rfl⟩) (B 4979 (by norm_num) ⟨2489, by rfl⟩ (by norm_num))
theorem R13281 : Reach 13281 := rs (se 2 (by rfl) ⟨4980, by rfl⟩) (B 9961 (by norm_num) ⟨4980, by rfl⟩ (by norm_num))
theorem R13285 : Reach 13285 := rs (se 4 (by rfl) ⟨1245, by rfl⟩) (B 2491 (by norm_num) ⟨1245, by rfl⟩ (by norm_num))
theorem R13289 : Reach 13289 := rs (se 2 (by rfl) ⟨4983, by rfl⟩) (B 9967 (by norm_num) ⟨4983, by rfl⟩ (by norm_num))
theorem R13293 : Reach 13293 := rs (se 3 (by rfl) ⟨2492, by rfl⟩) (B 4985 (by norm_num) ⟨2492, by rfl⟩ (by norm_num))
theorem R13297 : Reach 13297 := rs (se 2 (by rfl) ⟨4986, by rfl⟩) (B 9973 (by norm_num) ⟨4986, by rfl⟩ (by norm_num))
theorem R13301 : Reach 13301 := rs (se 5 (by rfl) ⟨623, by rfl⟩) (B 1247 (by norm_num) ⟨623, by rfl⟩ (by norm_num))
theorem R13305 : Reach 13305 := rs (se 2 (by rfl) ⟨4989, by rfl⟩) (B 9979 (by norm_num) ⟨4989, by rfl⟩ (by norm_num))
theorem R13309 : Reach 13309 := rs (se 3 (by rfl) ⟨2495, by rfl⟩) (B 4991 (by norm_num) ⟨2495, by rfl⟩ (by norm_num))
theorem R13313 : Reach 13313 := rs (se 2 (by rfl) ⟨4992, by rfl⟩) (B 9985 (by norm_num) ⟨4992, by rfl⟩ (by norm_num))
theorem R13317 : Reach 13317 := rs (se 4 (by rfl) ⟨1248, by rfl⟩) (B 2497 (by norm_num) ⟨1248, by rfl⟩ (by norm_num))
theorem R13321 : Reach 13321 := rs (se 2 (by rfl) ⟨4995, by rfl⟩) (B 9991 (by norm_num) ⟨4995, by rfl⟩ (by norm_num))
theorem R13325 : Reach 13325 := rs (se 3 (by rfl) ⟨2498, by rfl⟩) (B 4997 (by norm_num) ⟨2498, by rfl⟩ (by norm_num))
theorem R13329 : Reach 13329 := rs (se 2 (by rfl) ⟨4998, by rfl⟩) (B 9997 (by norm_num) ⟨4998, by rfl⟩ (by norm_num))
theorem R13333 : Reach 13333 := rs (se 6 (by rfl) ⟨312, by rfl⟩) (B 625 (by norm_num) ⟨312, by rfl⟩ (by norm_num))
theorem R78869 : Reach 78869 := rs (se 6 (by rfl) ⟨1848, by rfl⟩) (B 3697 (by norm_num) ⟨1848, by rfl⟩ (by norm_num))
theorem R13337 : Reach 13337 := rs (se 2 (by rfl) ⟨5001, by rfl⟩) (B 10003 (by norm_num) ⟨5001, by rfl⟩ (by norm_num))
theorem R13341 : Reach 13341 := rs (se 3 (by rfl) ⟨2501, by rfl⟩) (B 5003 (by norm_num) ⟨2501, by rfl⟩ (by norm_num))
theorem R13345 : Reach 13345 := rs (se 2 (by rfl) ⟨5004, by rfl⟩) (B 10009 (by norm_num) ⟨5004, by rfl⟩ (by norm_num))
theorem R13349 : Reach 13349 := rs (se 4 (by rfl) ⟨1251, by rfl⟩) (B 2503 (by norm_num) ⟨1251, by rfl⟩ (by norm_num))
theorem R13353 : Reach 13353 := rs (se 2 (by rfl) ⟨5007, by rfl⟩) (B 10015 (by norm_num) ⟨5007, by rfl⟩ (by norm_num))
theorem R13357 : Reach 13357 := rs (se 3 (by rfl) ⟨2504, by rfl⟩) (B 5009 (by norm_num) ⟨2504, by rfl⟩ (by norm_num))
theorem R13361 : Reach 13361 := rs (se 2 (by rfl) ⟨5010, by rfl⟩) (B 10021 (by norm_num) ⟨5010, by rfl⟩ (by norm_num))
theorem R13365 : Reach 13365 := rs (se 5 (by rfl) ⟨626, by rfl⟩) (B 1253 (by norm_num) ⟨626, by rfl⟩ (by norm_num))
theorem R46133 : Reach 46133 := rs (se 5 (by rfl) ⟨2162, by rfl⟩) (B 4325 (by norm_num) ⟨2162, by rfl⟩ (by norm_num))
theorem R13369 : Reach 13369 := rs (se 2 (by rfl) ⟨5013, by rfl⟩) (B 10027 (by norm_num) ⟨5013, by rfl⟩ (by norm_num))
theorem R13373 : Reach 13373 := rs (se 3 (by rfl) ⟨2507, by rfl⟩) (B 5015 (by norm_num) ⟨2507, by rfl⟩ (by norm_num))
theorem R13377 : Reach 13377 := rs (se 2 (by rfl) ⟨5016, by rfl⟩) (B 10033 (by norm_num) ⟨5016, by rfl⟩ (by norm_num))
theorem R13381 : Reach 13381 := rs (se 4 (by rfl) ⟨1254, by rfl⟩) (B 2509 (by norm_num) ⟨1254, by rfl⟩ (by norm_num))
theorem R13385 : Reach 13385 := rs (se 2 (by rfl) ⟨5019, by rfl⟩) (B 10039 (by norm_num) ⟨5019, by rfl⟩ (by norm_num))
theorem R13389 : Reach 13389 := rs (se 3 (by rfl) ⟨2510, by rfl⟩) (B 5021 (by norm_num) ⟨2510, by rfl⟩ (by norm_num))
theorem R13393 : Reach 13393 := rs (se 2 (by rfl) ⟨5022, by rfl⟩) (B 10045 (by norm_num) ⟨5022, by rfl⟩ (by norm_num))
theorem R13397 : Reach 13397 := rs (se 8 (by rfl) ⟨78, by rfl⟩) (B 157 (by norm_num) ⟨78, by rfl⟩ (by norm_num))
theorem R13401 : Reach 13401 := rs (se 2 (by rfl) ⟨5025, by rfl⟩) (B 10051 (by norm_num) ⟨5025, by rfl⟩ (by norm_num))
theorem R13405 : Reach 13405 := rs (se 3 (by rfl) ⟨2513, by rfl⟩) (B 5027 (by norm_num) ⟨2513, by rfl⟩ (by norm_num))
theorem R13409 : Reach 13409 := rs (se 2 (by rfl) ⟨5028, by rfl⟩) (B 10057 (by norm_num) ⟨5028, by rfl⟩ (by norm_num))
theorem R13413 : Reach 13413 := rs (se 4 (by rfl) ⟨1257, by rfl⟩) (B 2515 (by norm_num) ⟨1257, by rfl⟩ (by norm_num))
theorem R13417 : Reach 13417 := rs (se 2 (by rfl) ⟨5031, by rfl⟩) (B 10063 (by norm_num) ⟨5031, by rfl⟩ (by norm_num))
theorem R13421 : Reach 13421 := rs (se 3 (by rfl) ⟨2516, by rfl⟩) (B 5033 (by norm_num) ⟨2516, by rfl⟩ (by norm_num))
theorem R13425 : Reach 13425 := rs (se 2 (by rfl) ⟨5034, by rfl⟩) (B 10069 (by norm_num) ⟨5034, by rfl⟩ (by norm_num))
theorem R13429 : Reach 13429 := rs (se 5 (by rfl) ⟨629, by rfl⟩) (B 1259 (by norm_num) ⟨629, by rfl⟩ (by norm_num))
theorem R78965 : Reach 78965 := rs (se 5 (by rfl) ⟨3701, by rfl⟩) (B 7403 (by norm_num) ⟨3701, by rfl⟩ (by norm_num))
theorem R13433 : Reach 13433 := rs (se 2 (by rfl) ⟨5037, by rfl⟩) (B 10075 (by norm_num) ⟨5037, by rfl⟩ (by norm_num))
theorem R13437 : Reach 13437 := rs (se 3 (by rfl) ⟨2519, by rfl⟩) (B 5039 (by norm_num) ⟨2519, by rfl⟩ (by norm_num))
theorem R13441 : Reach 13441 := rs (se 2 (by rfl) ⟨5040, by rfl⟩) (B 10081 (by norm_num) ⟨5040, by rfl⟩ (by norm_num))
theorem R13445 : Reach 13445 := rs (se 4 (by rfl) ⟨1260, by rfl⟩) (B 2521 (by norm_num) ⟨1260, by rfl⟩ (by norm_num))
theorem R13449 : Reach 13449 := rs (se 2 (by rfl) ⟨5043, by rfl⟩) (B 10087 (by norm_num) ⟨5043, by rfl⟩ (by norm_num))
theorem R13453 : Reach 13453 := rs (se 3 (by rfl) ⟨2522, by rfl⟩) (B 5045 (by norm_num) ⟨2522, by rfl⟩ (by norm_num))
theorem R13457 : Reach 13457 := rs (se 2 (by rfl) ⟨5046, by rfl⟩) (B 10093 (by norm_num) ⟨5046, by rfl⟩ (by norm_num))
theorem R13461 : Reach 13461 := rs (se 6 (by rfl) ⟨315, by rfl⟩) (B 631 (by norm_num) ⟨315, by rfl⟩ (by norm_num))
theorem R13465 : Reach 13465 := rs (se 2 (by rfl) ⟨5049, by rfl⟩) (B 10099 (by norm_num) ⟨5049, by rfl⟩ (by norm_num))
theorem R13469 : Reach 13469 := rs (se 3 (by rfl) ⟨2525, by rfl⟩) (B 5051 (by norm_num) ⟨2525, by rfl⟩ (by norm_num))
theorem R13473 : Reach 13473 := rs (se 2 (by rfl) ⟨5052, by rfl⟩) (B 10105 (by norm_num) ⟨5052, by rfl⟩ (by norm_num))
theorem R13477 : Reach 13477 := rs (se 4 (by rfl) ⟨1263, by rfl⟩) (B 2527 (by norm_num) ⟨1263, by rfl⟩ (by norm_num))
theorem R13481 : Reach 13481 := rs (se 2 (by rfl) ⟨5055, by rfl⟩) (B 10111 (by norm_num) ⟨5055, by rfl⟩ (by norm_num))
theorem R13485 : Reach 13485 := rs (se 3 (by rfl) ⟨2528, by rfl⟩) (B 5057 (by norm_num) ⟨2528, by rfl⟩ (by norm_num))
theorem R13489 : Reach 13489 := rs (se 2 (by rfl) ⟨5058, by rfl⟩) (B 10117 (by norm_num) ⟨5058, by rfl⟩ (by norm_num))
theorem R13493 : Reach 13493 := rs (se 5 (by rfl) ⟨632, by rfl⟩) (B 1265 (by norm_num) ⟨632, by rfl⟩ (by norm_num))
theorem R46261 : Reach 46261 := rs (se 5 (by rfl) ⟨2168, by rfl⟩) (B 4337 (by norm_num) ⟨2168, by rfl⟩ (by norm_num))
theorem R13497 : Reach 13497 := rs (se 2 (by rfl) ⟨5061, by rfl⟩) (B 10123 (by norm_num) ⟨5061, by rfl⟩ (by norm_num))
theorem R13501 : Reach 13501 := rs (se 3 (by rfl) ⟨2531, by rfl⟩) (B 5063 (by norm_num) ⟨2531, by rfl⟩ (by norm_num))
theorem R13505 : Reach 13505 := rs (se 2 (by rfl) ⟨5064, by rfl⟩) (B 10129 (by norm_num) ⟨5064, by rfl⟩ (by norm_num))
theorem R13509 : Reach 13509 := rs (se 4 (by rfl) ⟨1266, by rfl⟩) (B 2533 (by norm_num) ⟨1266, by rfl⟩ (by norm_num))
theorem R46277 : Reach 46277 := rs (se 4 (by rfl) ⟨4338, by rfl⟩) (B 8677 (by norm_num) ⟨4338, by rfl⟩ (by norm_num))
theorem R13513 : Reach 13513 := rs (se 2 (by rfl) ⟨5067, by rfl⟩) (B 10135 (by norm_num) ⟨5067, by rfl⟩ (by norm_num))
theorem R13517 : Reach 13517 := rs (se 3 (by rfl) ⟨2534, by rfl⟩) (B 5069 (by norm_num) ⟨2534, by rfl⟩ (by norm_num))
theorem R13521 : Reach 13521 := rs (se 2 (by rfl) ⟨5070, by rfl⟩) (B 10141 (by norm_num) ⟨5070, by rfl⟩ (by norm_num))
theorem R13525 : Reach 13525 := rs (se 7 (by rfl) ⟨158, by rfl⟩) (B 317 (by norm_num) ⟨158, by rfl⟩ (by norm_num))
theorem R13529 : Reach 13529 := rs (se 2 (by rfl) ⟨5073, by rfl⟩) (B 10147 (by norm_num) ⟨5073, by rfl⟩ (by norm_num))
theorem R13533 : Reach 13533 := rs (se 3 (by rfl) ⟨2537, by rfl⟩) (B 5075 (by norm_num) ⟨2537, by rfl⟩ (by norm_num))
theorem R13537 : Reach 13537 := rs (se 2 (by rfl) ⟨5076, by rfl⟩) (B 10153 (by norm_num) ⟨5076, by rfl⟩ (by norm_num))
theorem R13541 : Reach 13541 := rs (se 4 (by rfl) ⟨1269, by rfl⟩) (B 2539 (by norm_num) ⟨1269, by rfl⟩ (by norm_num))
theorem R13545 : Reach 13545 := rs (se 2 (by rfl) ⟨5079, by rfl⟩) (B 10159 (by norm_num) ⟨5079, by rfl⟩ (by norm_num))
theorem R13549 : Reach 13549 := rs (se 3 (by rfl) ⟨2540, by rfl⟩) (B 5081 (by norm_num) ⟨2540, by rfl⟩ (by norm_num))
theorem R13553 : Reach 13553 := rs (se 2 (by rfl) ⟨5082, by rfl⟩) (B 10165 (by norm_num) ⟨5082, by rfl⟩ (by norm_num))
theorem R13557 : Reach 13557 := rs (se 5 (by rfl) ⟨635, by rfl⟩) (B 1271 (by norm_num) ⟨635, by rfl⟩ (by norm_num))
theorem R13561 : Reach 13561 := rs (se 2 (by rfl) ⟨5085, by rfl⟩) (B 10171 (by norm_num) ⟨5085, by rfl⟩ (by norm_num))
theorem R13565 : Reach 13565 := rs (se 3 (by rfl) ⟨2543, by rfl⟩) (B 5087 (by norm_num) ⟨2543, by rfl⟩ (by norm_num))
theorem R13569 : Reach 13569 := rs (se 2 (by rfl) ⟨5088, by rfl⟩) (B 10177 (by norm_num) ⟨5088, by rfl⟩ (by norm_num))
theorem R13573 : Reach 13573 := rs (se 4 (by rfl) ⟨1272, by rfl⟩) (B 2545 (by norm_num) ⟨1272, by rfl⟩ (by norm_num))
theorem R13577 : Reach 13577 := rs (se 2 (by rfl) ⟨5091, by rfl⟩) (B 10183 (by norm_num) ⟨5091, by rfl⟩ (by norm_num))
theorem R13581 : Reach 13581 := rs (se 3 (by rfl) ⟨2546, by rfl⟩) (B 5093 (by norm_num) ⟨2546, by rfl⟩ (by norm_num))
theorem R13585 : Reach 13585 := rs (se 2 (by rfl) ⟨5094, by rfl⟩) (B 10189 (by norm_num) ⟨5094, by rfl⟩ (by norm_num))
theorem R13589 : Reach 13589 := rs (se 6 (by rfl) ⟨318, by rfl⟩) (B 637 (by norm_num) ⟨318, by rfl⟩ (by norm_num))
theorem R13593 : Reach 13593 := rs (se 2 (by rfl) ⟨5097, by rfl⟩) (B 10195 (by norm_num) ⟨5097, by rfl⟩ (by norm_num))
theorem R13597 : Reach 13597 := rs (se 3 (by rfl) ⟨2549, by rfl⟩) (B 5099 (by norm_num) ⟨2549, by rfl⟩ (by norm_num))
theorem R13601 : Reach 13601 := rs (se 2 (by rfl) ⟨5100, by rfl⟩) (B 10201 (by norm_num) ⟨5100, by rfl⟩ (by norm_num))
theorem R13605 : Reach 13605 := rs (se 4 (by rfl) ⟨1275, by rfl⟩) (B 2551 (by norm_num) ⟨1275, by rfl⟩ (by norm_num))
theorem R13609 : Reach 13609 := rs (se 2 (by rfl) ⟨5103, by rfl⟩) (B 10207 (by norm_num) ⟨5103, by rfl⟩ (by norm_num))
theorem R13613 : Reach 13613 := rs (se 3 (by rfl) ⟨2552, by rfl⟩) (B 5105 (by norm_num) ⟨2552, by rfl⟩ (by norm_num))
theorem R13617 : Reach 13617 := rs (se 2 (by rfl) ⟨5106, by rfl⟩) (B 10213 (by norm_num) ⟨5106, by rfl⟩ (by norm_num))
theorem R13621 : Reach 13621 := rs (se 5 (by rfl) ⟨638, by rfl⟩) (B 1277 (by norm_num) ⟨638, by rfl⟩ (by norm_num))
theorem R13625 : Reach 13625 := rs (se 2 (by rfl) ⟨5109, by rfl⟩) (B 10219 (by norm_num) ⟨5109, by rfl⟩ (by norm_num))
theorem R13629 : Reach 13629 := rs (se 3 (by rfl) ⟨2555, by rfl⟩) (B 5111 (by norm_num) ⟨2555, by rfl⟩ (by norm_num))
theorem R13633 : Reach 13633 := rs (se 2 (by rfl) ⟨5112, by rfl⟩) (B 10225 (by norm_num) ⟨5112, by rfl⟩ (by norm_num))
theorem R13637 : Reach 13637 := rs (se 4 (by rfl) ⟨1278, by rfl⟩) (B 2557 (by norm_num) ⟨1278, by rfl⟩ (by norm_num))
theorem R13641 : Reach 13641 := rs (se 2 (by rfl) ⟨5115, by rfl⟩) (B 10231 (by norm_num) ⟨5115, by rfl⟩ (by norm_num))
theorem R13645 : Reach 13645 := rs (se 3 (by rfl) ⟨2558, by rfl⟩) (B 5117 (by norm_num) ⟨2558, by rfl⟩ (by norm_num))
theorem R13649 : Reach 13649 := rs (se 2 (by rfl) ⟨5118, by rfl⟩) (B 10237 (by norm_num) ⟨5118, by rfl⟩ (by norm_num))
theorem R13653 : Reach 13653 := rs (se 13 (by rfl) ⟨2, by rfl⟩) (B 5 (by norm_num) ⟨2, by rfl⟩ (by norm_num))
theorem R13657 : Reach 13657 := rs (se 2 (by rfl) ⟨5121, by rfl⟩) (B 10243 (by norm_num) ⟨5121, by rfl⟩ (by norm_num))
theorem R13661 : Reach 13661 := rs (se 3 (by rfl) ⟨2561, by rfl⟩) (B 5123 (by norm_num) ⟨2561, by rfl⟩ (by norm_num))
theorem R13665 : Reach 13665 := rs (se 2 (by rfl) ⟨5124, by rfl⟩) (B 10249 (by norm_num) ⟨5124, by rfl⟩ (by norm_num))
theorem R13669 : Reach 13669 := rs (se 4 (by rfl) ⟨1281, by rfl⟩) (B 2563 (by norm_num) ⟨1281, by rfl⟩ (by norm_num))
theorem R13673 : Reach 13673 := rs (se 2 (by rfl) ⟨5127, by rfl⟩) (B 10255 (by norm_num) ⟨5127, by rfl⟩ (by norm_num))
theorem R13677 : Reach 13677 := rs (se 3 (by rfl) ⟨2564, by rfl⟩) (B 5129 (by norm_num) ⟨2564, by rfl⟩ (by norm_num))
theorem R13681 : Reach 13681 := rs (se 2 (by rfl) ⟨5130, by rfl⟩) (B 10261 (by norm_num) ⟨5130, by rfl⟩ (by norm_num))
theorem R13685 : Reach 13685 := rs (se 5 (by rfl) ⟨641, by rfl⟩) (B 1283 (by norm_num) ⟨641, by rfl⟩ (by norm_num))
theorem R46453 : Reach 46453 := rs (se 5 (by rfl) ⟨2177, by rfl⟩) (B 4355 (by norm_num) ⟨2177, by rfl⟩ (by norm_num))
theorem R13689 : Reach 13689 := rs (se 2 (by rfl) ⟨5133, by rfl⟩) (B 10267 (by norm_num) ⟨5133, by rfl⟩ (by norm_num))
theorem R13693 : Reach 13693 := rs (se 3 (by rfl) ⟨2567, by rfl⟩) (B 5135 (by norm_num) ⟨2567, by rfl⟩ (by norm_num))
theorem R13697 : Reach 13697 := rs (se 2 (by rfl) ⟨5136, by rfl⟩) (B 10273 (by norm_num) ⟨5136, by rfl⟩ (by norm_num))
theorem R13701 : Reach 13701 := rs (se 4 (by rfl) ⟨1284, by rfl⟩) (B 2569 (by norm_num) ⟨1284, by rfl⟩ (by norm_num))
theorem R13705 : Reach 13705 := rs (se 2 (by rfl) ⟨5139, by rfl⟩) (B 10279 (by norm_num) ⟨5139, by rfl⟩ (by norm_num))
theorem R13709 : Reach 13709 := rs (se 3 (by rfl) ⟨2570, by rfl⟩) (B 5141 (by norm_num) ⟨2570, by rfl⟩ (by norm_num))
theorem R13713 : Reach 13713 := rs (se 2 (by rfl) ⟨5142, by rfl⟩) (B 10285 (by norm_num) ⟨5142, by rfl⟩ (by norm_num))
theorem R13717 : Reach 13717 := rs (se 6 (by rfl) ⟨321, by rfl⟩) (B 643 (by norm_num) ⟨321, by rfl⟩ (by norm_num))
theorem R13721 : Reach 13721 := rs (se 2 (by rfl) ⟨5145, by rfl⟩) (B 10291 (by norm_num) ⟨5145, by rfl⟩ (by norm_num))
theorem R13725 : Reach 13725 := rs (se 3 (by rfl) ⟨2573, by rfl⟩) (B 5147 (by norm_num) ⟨2573, by rfl⟩ (by norm_num))
theorem R13729 : Reach 13729 := rs (se 2 (by rfl) ⟨5148, by rfl⟩) (B 10297 (by norm_num) ⟨5148, by rfl⟩ (by norm_num))
theorem R13733 : Reach 13733 := rs (se 4 (by rfl) ⟨1287, by rfl⟩) (B 2575 (by norm_num) ⟨1287, by rfl⟩ (by norm_num))
theorem R13737 : Reach 13737 := rs (se 2 (by rfl) ⟨5151, by rfl⟩) (B 10303 (by norm_num) ⟨5151, by rfl⟩ (by norm_num))
theorem R13741 : Reach 13741 := rs (se 3 (by rfl) ⟨2576, by rfl⟩) (B 5153 (by norm_num) ⟨2576, by rfl⟩ (by norm_num))
theorem R13745 : Reach 13745 := rs (se 2 (by rfl) ⟨5154, by rfl⟩) (B 10309 (by norm_num) ⟨5154, by rfl⟩ (by norm_num))
theorem R13749 : Reach 13749 := rs (se 5 (by rfl) ⟨644, by rfl⟩) (B 1289 (by norm_num) ⟨644, by rfl⟩ (by norm_num))
theorem R13753 : Reach 13753 := rs (se 2 (by rfl) ⟨5157, by rfl⟩) (B 10315 (by norm_num) ⟨5157, by rfl⟩ (by norm_num))
theorem R13757 : Reach 13757 := rs (se 3 (by rfl) ⟨2579, by rfl⟩) (B 5159 (by norm_num) ⟨2579, by rfl⟩ (by norm_num))
theorem R13761 : Reach 13761 := rs (se 2 (by rfl) ⟨5160, by rfl⟩) (B 10321 (by norm_num) ⟨5160, by rfl⟩ (by norm_num))
theorem R13765 : Reach 13765 := rs (se 4 (by rfl) ⟨1290, by rfl⟩) (B 2581 (by norm_num) ⟨1290, by rfl⟩ (by norm_num))
theorem R13769 : Reach 13769 := rs (se 2 (by rfl) ⟨5163, by rfl⟩) (B 10327 (by norm_num) ⟨5163, by rfl⟩ (by norm_num))
theorem R13773 : Reach 13773 := rs (se 3 (by rfl) ⟨2582, by rfl⟩) (B 5165 (by norm_num) ⟨2582, by rfl⟩ (by norm_num))
theorem R13777 : Reach 13777 := rs (se 2 (by rfl) ⟨5166, by rfl⟩) (B 10333 (by norm_num) ⟨5166, by rfl⟩ (by norm_num))
theorem R13781 : Reach 13781 := rs (se 7 (by rfl) ⟨161, by rfl⟩) (B 323 (by norm_num) ⟨161, by rfl⟩ (by norm_num))
theorem R13785 : Reach 13785 := rs (se 2 (by rfl) ⟨5169, by rfl⟩) (B 10339 (by norm_num) ⟨5169, by rfl⟩ (by norm_num))
theorem R13789 : Reach 13789 := rs (se 3 (by rfl) ⟨2585, by rfl⟩) (B 5171 (by norm_num) ⟨2585, by rfl⟩ (by norm_num))
theorem R13793 : Reach 13793 := rs (se 2 (by rfl) ⟨5172, by rfl⟩) (B 10345 (by norm_num) ⟨5172, by rfl⟩ (by norm_num))
theorem R13797 : Reach 13797 := rs (se 4 (by rfl) ⟨1293, by rfl⟩) (B 2587 (by norm_num) ⟨1293, by rfl⟩ (by norm_num))
theorem R46565 : Reach 46565 := rs (se 4 (by rfl) ⟨4365, by rfl⟩) (B 8731 (by norm_num) ⟨4365, by rfl⟩ (by norm_num))
theorem R13801 : Reach 13801 := rs (se 2 (by rfl) ⟨5175, by rfl⟩) (B 10351 (by norm_num) ⟨5175, by rfl⟩ (by norm_num))
theorem R13805 : Reach 13805 := rs (se 3 (by rfl) ⟨2588, by rfl⟩) (B 5177 (by norm_num) ⟨2588, by rfl⟩ (by norm_num))
theorem R13809 : Reach 13809 := rs (se 2 (by rfl) ⟨5178, by rfl⟩) (B 10357 (by norm_num) ⟨5178, by rfl⟩ (by norm_num))
theorem R13813 : Reach 13813 := rs (se 5 (by rfl) ⟨647, by rfl⟩) (B 1295 (by norm_num) ⟨647, by rfl⟩ (by norm_num))
theorem R13817 : Reach 13817 := rs (se 2 (by rfl) ⟨5181, by rfl⟩) (B 10363 (by norm_num) ⟨5181, by rfl⟩ (by norm_num))
theorem R13821 : Reach 13821 := rs (se 3 (by rfl) ⟨2591, by rfl⟩) (B 5183 (by norm_num) ⟨2591, by rfl⟩ (by norm_num))
theorem R13825 : Reach 13825 := rs (se 2 (by rfl) ⟨5184, by rfl⟩) (B 10369 (by norm_num) ⟨5184, by rfl⟩ (by norm_num))
theorem R13829 : Reach 13829 := rs (se 4 (by rfl) ⟨1296, by rfl⟩) (B 2593 (by norm_num) ⟨1296, by rfl⟩ (by norm_num))
theorem R13833 : Reach 13833 := rs (se 2 (by rfl) ⟨5187, by rfl⟩) (B 10375 (by norm_num) ⟨5187, by rfl⟩ (by norm_num))
theorem R13837 : Reach 13837 := rs (se 3 (by rfl) ⟨2594, by rfl⟩) (B 5189 (by norm_num) ⟨2594, by rfl⟩ (by norm_num))
theorem R13841 : Reach 13841 := rs (se 2 (by rfl) ⟨5190, by rfl⟩) (B 10381 (by norm_num) ⟨5190, by rfl⟩ (by norm_num))
theorem R13845 : Reach 13845 := rs (se 6 (by rfl) ⟨324, by rfl⟩) (B 649 (by norm_num) ⟨324, by rfl⟩ (by norm_num))
theorem R13849 : Reach 13849 := rs (se 2 (by rfl) ⟨5193, by rfl⟩) (B 10387 (by norm_num) ⟨5193, by rfl⟩ (by norm_num))
theorem R13853 : Reach 13853 := rs (se 3 (by rfl) ⟨2597, by rfl⟩) (B 5195 (by norm_num) ⟨2597, by rfl⟩ (by norm_num))
theorem R13857 : Reach 13857 := rs (se 2 (by rfl) ⟨5196, by rfl⟩) (B 10393 (by norm_num) ⟨5196, by rfl⟩ (by norm_num))
theorem R13861 : Reach 13861 := rs (se 4 (by rfl) ⟨1299, by rfl⟩) (B 2599 (by norm_num) ⟨1299, by rfl⟩ (by norm_num))
theorem R13865 : Reach 13865 := rs (se 2 (by rfl) ⟨5199, by rfl⟩) (B 10399 (by norm_num) ⟨5199, by rfl⟩ (by norm_num))
theorem R13869 : Reach 13869 := rs (se 3 (by rfl) ⟨2600, by rfl⟩) (B 5201 (by norm_num) ⟨2600, by rfl⟩ (by norm_num))
theorem R13873 : Reach 13873 := rs (se 2 (by rfl) ⟨5202, by rfl⟩) (B 10405 (by norm_num) ⟨5202, by rfl⟩ (by norm_num))
theorem R13877 : Reach 13877 := rs (se 5 (by rfl) ⟨650, by rfl⟩) (B 1301 (by norm_num) ⟨650, by rfl⟩ (by norm_num))
theorem R13881 : Reach 13881 := rs (se 2 (by rfl) ⟨5205, by rfl⟩) (B 10411 (by norm_num) ⟨5205, by rfl⟩ (by norm_num))
theorem R13885 : Reach 13885 := rs (se 3 (by rfl) ⟨2603, by rfl⟩) (B 5207 (by norm_num) ⟨2603, by rfl⟩ (by norm_num))
theorem R13889 : Reach 13889 := rs (se 2 (by rfl) ⟨5208, by rfl⟩) (B 10417 (by norm_num) ⟨5208, by rfl⟩ (by norm_num))
theorem R13893 : Reach 13893 := rs (se 4 (by rfl) ⟨1302, by rfl⟩) (B 2605 (by norm_num) ⟨1302, by rfl⟩ (by norm_num))
theorem R13897 : Reach 13897 := rs (se 2 (by rfl) ⟨5211, by rfl⟩) (B 10423 (by norm_num) ⟨5211, by rfl⟩ (by norm_num))
theorem R13901 : Reach 13901 := rs (se 3 (by rfl) ⟨2606, by rfl⟩) (B 5213 (by norm_num) ⟨2606, by rfl⟩ (by norm_num))
theorem R13905 : Reach 13905 := rs (se 2 (by rfl) ⟨5214, by rfl⟩) (B 10429 (by norm_num) ⟨5214, by rfl⟩ (by norm_num))
theorem R13909 : Reach 13909 := rs (se 8 (by rfl) ⟨81, by rfl⟩) (B 163 (by norm_num) ⟨81, by rfl⟩ (by norm_num))
theorem R13913 : Reach 13913 := rs (se 2 (by rfl) ⟨5217, by rfl⟩) (B 10435 (by norm_num) ⟨5217, by rfl⟩ (by norm_num))
theorem R13917 : Reach 13917 := rs (se 3 (by rfl) ⟨2609, by rfl⟩) (B 5219 (by norm_num) ⟨2609, by rfl⟩ (by norm_num))
theorem R13921 : Reach 13921 := rs (se 2 (by rfl) ⟨5220, by rfl⟩) (B 10441 (by norm_num) ⟨5220, by rfl⟩ (by norm_num))
theorem R13925 : Reach 13925 := rs (se 4 (by rfl) ⟨1305, by rfl⟩) (B 2611 (by norm_num) ⟨1305, by rfl⟩ (by norm_num))
theorem R13929 : Reach 13929 := rs (se 2 (by rfl) ⟨5223, by rfl⟩) (B 10447 (by norm_num) ⟨5223, by rfl⟩ (by norm_num))
theorem R13933 : Reach 13933 := rs (se 3 (by rfl) ⟨2612, by rfl⟩) (B 5225 (by norm_num) ⟨2612, by rfl⟩ (by norm_num))
theorem R13937 : Reach 13937 := rs (se 2 (by rfl) ⟨5226, by rfl⟩) (B 10453 (by norm_num) ⟨5226, by rfl⟩ (by norm_num))
theorem R46709 : Reach 46709 := rs (se 5 (by rfl) ⟨2189, by rfl⟩) (B 4379 (by norm_num) ⟨2189, by rfl⟩ (by norm_num))
theorem R13941 : Reach 13941 := rs (se 5 (by rfl) ⟨653, by rfl⟩) (B 1307 (by norm_num) ⟨653, by rfl⟩ (by norm_num))
theorem R13945 : Reach 13945 := rs (se 2 (by rfl) ⟨5229, by rfl⟩) (B 10459 (by norm_num) ⟨5229, by rfl⟩ (by norm_num))
theorem R13949 : Reach 13949 := rs (se 3 (by rfl) ⟨2615, by rfl⟩) (B 5231 (by norm_num) ⟨2615, by rfl⟩ (by norm_num))
theorem R13953 : Reach 13953 := rs (se 2 (by rfl) ⟨5232, by rfl⟩) (B 10465 (by norm_num) ⟨5232, by rfl⟩ (by norm_num))
theorem R13957 : Reach 13957 := rs (se 4 (by rfl) ⟨1308, by rfl⟩) (B 2617 (by norm_num) ⟨1308, by rfl⟩ (by norm_num))
theorem R13961 : Reach 13961 := rs (se 2 (by rfl) ⟨5235, by rfl⟩) (B 10471 (by norm_num) ⟨5235, by rfl⟩ (by norm_num))
theorem R13965 : Reach 13965 := rs (se 3 (by rfl) ⟨2618, by rfl⟩) (B 5237 (by norm_num) ⟨2618, by rfl⟩ (by norm_num))
theorem R13969 : Reach 13969 := rs (se 2 (by rfl) ⟨5238, by rfl⟩) (B 10477 (by norm_num) ⟨5238, by rfl⟩ (by norm_num))
theorem R13973 : Reach 13973 := rs (se 6 (by rfl) ⟨327, by rfl⟩) (B 655 (by norm_num) ⟨327, by rfl⟩ (by norm_num))
theorem R13977 : Reach 13977 := rs (se 2 (by rfl) ⟨5241, by rfl⟩) (B 10483 (by norm_num) ⟨5241, by rfl⟩ (by norm_num))
theorem R13981 : Reach 13981 := rs (se 3 (by rfl) ⟨2621, by rfl⟩) (B 5243 (by norm_num) ⟨2621, by rfl⟩ (by norm_num))
theorem R13985 : Reach 13985 := rs (se 2 (by rfl) ⟨5244, by rfl⟩) (B 10489 (by norm_num) ⟨5244, by rfl⟩ (by norm_num))
theorem R13989 : Reach 13989 := rs (se 4 (by rfl) ⟨1311, by rfl⟩) (B 2623 (by norm_num) ⟨1311, by rfl⟩ (by norm_num))
theorem R46757 : Reach 46757 := rs (se 4 (by rfl) ⟨4383, by rfl⟩) (B 8767 (by norm_num) ⟨4383, by rfl⟩ (by norm_num))
theorem R13993 : Reach 13993 := rs (se 2 (by rfl) ⟨5247, by rfl⟩) (B 10495 (by norm_num) ⟨5247, by rfl⟩ (by norm_num))
theorem R13997 : Reach 13997 := rs (se 3 (by rfl) ⟨2624, by rfl⟩) (B 5249 (by norm_num) ⟨2624, by rfl⟩ (by norm_num))
theorem R14001 : Reach 14001 := rs (se 2 (by rfl) ⟨5250, by rfl⟩) (B 10501 (by norm_num) ⟨5250, by rfl⟩ (by norm_num))
theorem R14005 : Reach 14005 := rs (se 5 (by rfl) ⟨656, by rfl⟩) (B 1313 (by norm_num) ⟨656, by rfl⟩ (by norm_num))
theorem R79541 : Reach 79541 := rs (se 5 (by rfl) ⟨3728, by rfl⟩) (B 7457 (by norm_num) ⟨3728, by rfl⟩ (by norm_num))
theorem R14009 : Reach 14009 := rs (se 2 (by rfl) ⟨5253, by rfl⟩) (B 10507 (by norm_num) ⟨5253, by rfl⟩ (by norm_num))
theorem R14013 : Reach 14013 := rs (se 3 (by rfl) ⟨2627, by rfl⟩) (B 5255 (by norm_num) ⟨2627, by rfl⟩ (by norm_num))
theorem R14017 : Reach 14017 := rs (se 2 (by rfl) ⟨5256, by rfl⟩) (B 10513 (by norm_num) ⟨5256, by rfl⟩ (by norm_num))
theorem R14021 : Reach 14021 := rs (se 4 (by rfl) ⟨1314, by rfl⟩) (B 2629 (by norm_num) ⟨1314, by rfl⟩ (by norm_num))
theorem R14025 : Reach 14025 := rs (se 2 (by rfl) ⟨5259, by rfl⟩) (B 10519 (by norm_num) ⟨5259, by rfl⟩ (by norm_num))
theorem R14029 : Reach 14029 := rs (se 3 (by rfl) ⟨2630, by rfl⟩) (B 5261 (by norm_num) ⟨2630, by rfl⟩ (by norm_num))
theorem R14033 : Reach 14033 := rs (se 2 (by rfl) ⟨5262, by rfl⟩) (B 10525 (by norm_num) ⟨5262, by rfl⟩ (by norm_num))
theorem R14037 : Reach 14037 := rs (se 7 (by rfl) ⟨164, by rfl⟩) (B 329 (by norm_num) ⟨164, by rfl⟩ (by norm_num))
theorem R14041 : Reach 14041 := rs (se 2 (by rfl) ⟨5265, by rfl⟩) (B 10531 (by norm_num) ⟨5265, by rfl⟩ (by norm_num))
theorem R14045 : Reach 14045 := rs (se 3 (by rfl) ⟨2633, by rfl⟩) (B 5267 (by norm_num) ⟨2633, by rfl⟩ (by norm_num))
theorem R14049 : Reach 14049 := rs (se 2 (by rfl) ⟨5268, by rfl⟩) (B 10537 (by norm_num) ⟨5268, by rfl⟩ (by norm_num))
theorem R14053 : Reach 14053 := rs (se 4 (by rfl) ⟨1317, by rfl⟩) (B 2635 (by norm_num) ⟨1317, by rfl⟩ (by norm_num))
theorem R14057 : Reach 14057 := rs (se 2 (by rfl) ⟨5271, by rfl⟩) (B 10543 (by norm_num) ⟨5271, by rfl⟩ (by norm_num))
theorem R14061 : Reach 14061 := rs (se 3 (by rfl) ⟨2636, by rfl⟩) (B 5273 (by norm_num) ⟨2636, by rfl⟩ (by norm_num))
theorem R14065 : Reach 14065 := rs (se 2 (by rfl) ⟨5274, by rfl⟩) (B 10549 (by norm_num) ⟨5274, by rfl⟩ (by norm_num))
theorem R14069 : Reach 14069 := rs (se 5 (by rfl) ⟨659, by rfl⟩) (B 1319 (by norm_num) ⟨659, by rfl⟩ (by norm_num))
theorem R14073 : Reach 14073 := rs (se 2 (by rfl) ⟨5277, by rfl⟩) (B 10555 (by norm_num) ⟨5277, by rfl⟩ (by norm_num))
theorem R14077 : Reach 14077 := rs (se 3 (by rfl) ⟨2639, by rfl⟩) (B 5279 (by norm_num) ⟨2639, by rfl⟩ (by norm_num))
theorem R14081 : Reach 14081 := rs (se 2 (by rfl) ⟨5280, by rfl⟩) (B 10561 (by norm_num) ⟨5280, by rfl⟩ (by norm_num))
theorem R14085 : Reach 14085 := rs (se 4 (by rfl) ⟨1320, by rfl⟩) (B 2641 (by norm_num) ⟨1320, by rfl⟩ (by norm_num))
theorem R14089 : Reach 14089 := rs (se 2 (by rfl) ⟨5283, by rfl⟩) (B 10567 (by norm_num) ⟨5283, by rfl⟩ (by norm_num))
theorem R14093 : Reach 14093 := rs (se 3 (by rfl) ⟨2642, by rfl⟩) (B 5285 (by norm_num) ⟨2642, by rfl⟩ (by norm_num))
theorem R14097 : Reach 14097 := rs (se 2 (by rfl) ⟨5286, by rfl⟩) (B 10573 (by norm_num) ⟨5286, by rfl⟩ (by norm_num))
theorem R14101 : Reach 14101 := rs (se 6 (by rfl) ⟨330, by rfl⟩) (B 661 (by norm_num) ⟨330, by rfl⟩ (by norm_num))
theorem R14105 : Reach 14105 := rs (se 2 (by rfl) ⟨5289, by rfl⟩) (B 10579 (by norm_num) ⟨5289, by rfl⟩ (by norm_num))
theorem R14109 : Reach 14109 := rs (se 3 (by rfl) ⟨2645, by rfl⟩) (B 5291 (by norm_num) ⟨2645, by rfl⟩ (by norm_num))
theorem R14113 : Reach 14113 := rs (se 2 (by rfl) ⟨5292, by rfl⟩) (B 10585 (by norm_num) ⟨5292, by rfl⟩ (by norm_num))
theorem R14117 : Reach 14117 := rs (se 4 (by rfl) ⟨1323, by rfl⟩) (B 2647 (by norm_num) ⟨1323, by rfl⟩ (by norm_num))
theorem R14121 : Reach 14121 := rs (se 2 (by rfl) ⟨5295, by rfl⟩) (B 10591 (by norm_num) ⟨5295, by rfl⟩ (by norm_num))
theorem R14125 : Reach 14125 := rs (se 3 (by rfl) ⟨2648, by rfl⟩) (B 5297 (by norm_num) ⟨2648, by rfl⟩ (by norm_num))
theorem R14129 : Reach 14129 := rs (se 2 (by rfl) ⟨5298, by rfl⟩) (B 10597 (by norm_num) ⟨5298, by rfl⟩ (by norm_num))
theorem R14133 : Reach 14133 := rs (se 5 (by rfl) ⟨662, by rfl⟩) (B 1325 (by norm_num) ⟨662, by rfl⟩ (by norm_num))
theorem R14137 : Reach 14137 := rs (se 2 (by rfl) ⟨5301, by rfl⟩) (B 10603 (by norm_num) ⟨5301, by rfl⟩ (by norm_num))
theorem R14141 : Reach 14141 := rs (se 3 (by rfl) ⟨2651, by rfl⟩) (B 5303 (by norm_num) ⟨2651, by rfl⟩ (by norm_num))
theorem R14145 : Reach 14145 := rs (se 2 (by rfl) ⟨5304, by rfl⟩) (B 10609 (by norm_num) ⟨5304, by rfl⟩ (by norm_num))
theorem R14149 : Reach 14149 := rs (se 4 (by rfl) ⟨1326, by rfl⟩) (B 2653 (by norm_num) ⟨1326, by rfl⟩ (by norm_num))
theorem R14153 : Reach 14153 := rs (se 2 (by rfl) ⟨5307, by rfl⟩) (B 10615 (by norm_num) ⟨5307, by rfl⟩ (by norm_num))
theorem R14157 : Reach 14157 := rs (se 3 (by rfl) ⟨2654, by rfl⟩) (B 5309 (by norm_num) ⟨2654, by rfl⟩ (by norm_num))
theorem R14161 : Reach 14161 := rs (se 2 (by rfl) ⟨5310, by rfl⟩) (B 10621 (by norm_num) ⟨5310, by rfl⟩ (by norm_num))
theorem R14165 : Reach 14165 := rs (se 9 (by rfl) ⟨41, by rfl⟩) (B 83 (by norm_num) ⟨41, by rfl⟩ (by norm_num))
theorem R14169 : Reach 14169 := rs (se 2 (by rfl) ⟨5313, by rfl⟩) (B 10627 (by norm_num) ⟨5313, by rfl⟩ (by norm_num))
theorem R14173 : Reach 14173 := rs (se 3 (by rfl) ⟨2657, by rfl⟩) (B 5315 (by norm_num) ⟨2657, by rfl⟩ (by norm_num))
theorem R14177 : Reach 14177 := rs (se 2 (by rfl) ⟨5316, by rfl⟩) (B 10633 (by norm_num) ⟨5316, by rfl⟩ (by norm_num))
theorem R14181 : Reach 14181 := rs (se 4 (by rfl) ⟨1329, by rfl⟩) (B 2659 (by norm_num) ⟨1329, by rfl⟩ (by norm_num))
theorem R14185 : Reach 14185 := rs (se 2 (by rfl) ⟨5319, by rfl⟩) (B 10639 (by norm_num) ⟨5319, by rfl⟩ (by norm_num))
theorem R14189 : Reach 14189 := rs (se 3 (by rfl) ⟨2660, by rfl⟩) (B 5321 (by norm_num) ⟨2660, by rfl⟩ (by norm_num))
theorem R14193 : Reach 14193 := rs (se 2 (by rfl) ⟨5322, by rfl⟩) (B 10645 (by norm_num) ⟨5322, by rfl⟩ (by norm_num))
theorem R14197 : Reach 14197 := rs (se 5 (by rfl) ⟨665, by rfl⟩) (B 1331 (by norm_num) ⟨665, by rfl⟩ (by norm_num))
theorem R14201 : Reach 14201 := rs (se 2 (by rfl) ⟨5325, by rfl⟩) (B 10651 (by norm_num) ⟨5325, by rfl⟩ (by norm_num))
theorem R14205 : Reach 14205 := rs (se 3 (by rfl) ⟨2663, by rfl⟩) (B 5327 (by norm_num) ⟨2663, by rfl⟩ (by norm_num))
theorem R14209 : Reach 14209 := rs (se 2 (by rfl) ⟨5328, by rfl⟩) (B 10657 (by norm_num) ⟨5328, by rfl⟩ (by norm_num))
theorem R14213 : Reach 14213 := rs (se 4 (by rfl) ⟨1332, by rfl⟩) (B 2665 (by norm_num) ⟨1332, by rfl⟩ (by norm_num))
theorem R14217 : Reach 14217 := rs (se 2 (by rfl) ⟨5331, by rfl⟩) (B 10663 (by norm_num) ⟨5331, by rfl⟩ (by norm_num))
theorem R14221 : Reach 14221 := rs (se 3 (by rfl) ⟨2666, by rfl⟩) (B 5333 (by norm_num) ⟨2666, by rfl⟩ (by norm_num))
theorem R14225 : Reach 14225 := rs (se 2 (by rfl) ⟨5334, by rfl⟩) (B 10669 (by norm_num) ⟨5334, by rfl⟩ (by norm_num))
theorem R14229 : Reach 14229 := rs (se 6 (by rfl) ⟨333, by rfl⟩) (B 667 (by norm_num) ⟨333, by rfl⟩ (by norm_num))
theorem R14233 : Reach 14233 := rs (se 2 (by rfl) ⟨5337, by rfl⟩) (B 10675 (by norm_num) ⟨5337, by rfl⟩ (by norm_num))
theorem R14237 : Reach 14237 := rs (se 3 (by rfl) ⟨2669, by rfl⟩) (B 5339 (by norm_num) ⟨2669, by rfl⟩ (by norm_num))
theorem R14241 : Reach 14241 := rs (se 2 (by rfl) ⟨5340, by rfl⟩) (B 10681 (by norm_num) ⟨5340, by rfl⟩ (by norm_num))
theorem R14245 : Reach 14245 := rs (se 4 (by rfl) ⟨1335, by rfl⟩) (B 2671 (by norm_num) ⟨1335, by rfl⟩ (by norm_num))
theorem R14249 : Reach 14249 := rs (se 2 (by rfl) ⟨5343, by rfl⟩) (B 10687 (by norm_num) ⟨5343, by rfl⟩ (by norm_num))
theorem R14253 : Reach 14253 := rs (se 3 (by rfl) ⟨2672, by rfl⟩) (B 5345 (by norm_num) ⟨2672, by rfl⟩ (by norm_num))
theorem R14257 : Reach 14257 := rs (se 2 (by rfl) ⟨5346, by rfl⟩) (B 10693 (by norm_num) ⟨5346, by rfl⟩ (by norm_num))
theorem R14261 : Reach 14261 := rs (se 5 (by rfl) ⟨668, by rfl⟩) (B 1337 (by norm_num) ⟨668, by rfl⟩ (by norm_num))
theorem R14265 : Reach 14265 := rs (se 2 (by rfl) ⟨5349, by rfl⟩) (B 10699 (by norm_num) ⟨5349, by rfl⟩ (by norm_num))
theorem R14269 : Reach 14269 := rs (se 3 (by rfl) ⟨2675, by rfl⟩) (B 5351 (by norm_num) ⟨2675, by rfl⟩ (by norm_num))
theorem R14273 : Reach 14273 := rs (se 2 (by rfl) ⟨5352, by rfl⟩) (B 10705 (by norm_num) ⟨5352, by rfl⟩ (by norm_num))
theorem R14277 : Reach 14277 := rs (se 4 (by rfl) ⟨1338, by rfl⟩) (B 2677 (by norm_num) ⟨1338, by rfl⟩ (by norm_num))
theorem R14281 : Reach 14281 := rs (se 2 (by rfl) ⟨5355, by rfl⟩) (B 10711 (by norm_num) ⟨5355, by rfl⟩ (by norm_num))
theorem R14285 : Reach 14285 := rs (se 3 (by rfl) ⟨2678, by rfl⟩) (B 5357 (by norm_num) ⟨2678, by rfl⟩ (by norm_num))
theorem R14289 : Reach 14289 := rs (se 2 (by rfl) ⟨5358, by rfl⟩) (B 10717 (by norm_num) ⟨5358, by rfl⟩ (by norm_num))
theorem R14293 : Reach 14293 := rs (se 7 (by rfl) ⟨167, by rfl⟩) (B 335 (by norm_num) ⟨167, by rfl⟩ (by norm_num))
theorem R14297 : Reach 14297 := rs (se 2 (by rfl) ⟨5361, by rfl⟩) (B 10723 (by norm_num) ⟨5361, by rfl⟩ (by norm_num))
theorem R14301 : Reach 14301 := rs (se 3 (by rfl) ⟨2681, by rfl⟩) (B 5363 (by norm_num) ⟨2681, by rfl⟩ (by norm_num))
theorem R14305 : Reach 14305 := rs (se 2 (by rfl) ⟨5364, by rfl⟩) (B 10729 (by norm_num) ⟨5364, by rfl⟩ (by norm_num))
theorem R14309 : Reach 14309 := rs (se 4 (by rfl) ⟨1341, by rfl⟩) (B 2683 (by norm_num) ⟨1341, by rfl⟩ (by norm_num))
theorem R14313 : Reach 14313 := rs (se 2 (by rfl) ⟨5367, by rfl⟩) (B 10735 (by norm_num) ⟨5367, by rfl⟩ (by norm_num))
theorem R14317 : Reach 14317 := rs (se 3 (by rfl) ⟨2684, by rfl⟩) (B 5369 (by norm_num) ⟨2684, by rfl⟩ (by norm_num))
theorem R14321 : Reach 14321 := rs (se 2 (by rfl) ⟨5370, by rfl⟩) (B 10741 (by norm_num) ⟨5370, by rfl⟩ (by norm_num))
theorem R14325 : Reach 14325 := rs (se 5 (by rfl) ⟨671, by rfl⟩) (B 1343 (by norm_num) ⟨671, by rfl⟩ (by norm_num))
theorem R14329 : Reach 14329 := rs (se 2 (by rfl) ⟨5373, by rfl⟩) (B 10747 (by norm_num) ⟨5373, by rfl⟩ (by norm_num))
theorem R14333 : Reach 14333 := rs (se 3 (by rfl) ⟨2687, by rfl⟩) (B 5375 (by norm_num) ⟨2687, by rfl⟩ (by norm_num))
theorem R14337 : Reach 14337 := rs (se 2 (by rfl) ⟨5376, by rfl⟩) (B 10753 (by norm_num) ⟨5376, by rfl⟩ (by norm_num))
theorem R14341 : Reach 14341 := rs (se 4 (by rfl) ⟨1344, by rfl⟩) (B 2689 (by norm_num) ⟨1344, by rfl⟩ (by norm_num))
theorem R14345 : Reach 14345 := rs (se 2 (by rfl) ⟨5379, by rfl⟩) (B 10759 (by norm_num) ⟨5379, by rfl⟩ (by norm_num))
theorem R14349 : Reach 14349 := rs (se 3 (by rfl) ⟨2690, by rfl⟩) (B 5381 (by norm_num) ⟨2690, by rfl⟩ (by norm_num))
theorem R14353 : Reach 14353 := rs (se 2 (by rfl) ⟨5382, by rfl⟩) (B 10765 (by norm_num) ⟨5382, by rfl⟩ (by norm_num))
theorem R14357 : Reach 14357 := rs (se 6 (by rfl) ⟨336, by rfl⟩) (B 673 (by norm_num) ⟨336, by rfl⟩ (by norm_num))
theorem R14361 : Reach 14361 := rs (se 2 (by rfl) ⟨5385, by rfl⟩) (B 10771 (by norm_num) ⟨5385, by rfl⟩ (by norm_num))
theorem R14365 : Reach 14365 := rs (se 3 (by rfl) ⟨2693, by rfl⟩) (B 5387 (by norm_num) ⟨2693, by rfl⟩ (by norm_num))
theorem R14369 : Reach 14369 := rs (se 2 (by rfl) ⟨5388, by rfl⟩) (B 10777 (by norm_num) ⟨5388, by rfl⟩ (by norm_num))
theorem R47141 : Reach 47141 := rs (se 4 (by rfl) ⟨4419, by rfl⟩) (B 8839 (by norm_num) ⟨4419, by rfl⟩ (by norm_num))
theorem R14373 : Reach 14373 := rs (se 4 (by rfl) ⟨1347, by rfl⟩) (B 2695 (by norm_num) ⟨1347, by rfl⟩ (by norm_num))
theorem R14377 : Reach 14377 := rs (se 2 (by rfl) ⟨5391, by rfl⟩) (B 10783 (by norm_num) ⟨5391, by rfl⟩ (by norm_num))
theorem R14381 : Reach 14381 := rs (se 3 (by rfl) ⟨2696, by rfl⟩) (B 5393 (by norm_num) ⟨2696, by rfl⟩ (by norm_num))
theorem R14385 : Reach 14385 := rs (se 2 (by rfl) ⟨5394, by rfl⟩) (B 10789 (by norm_num) ⟨5394, by rfl⟩ (by norm_num))
theorem R14389 : Reach 14389 := rs (se 5 (by rfl) ⟨674, by rfl⟩) (B 1349 (by norm_num) ⟨674, by rfl⟩ (by norm_num))
theorem R14393 : Reach 14393 := rs (se 2 (by rfl) ⟨5397, by rfl⟩) (B 10795 (by norm_num) ⟨5397, by rfl⟩ (by norm_num))
theorem R14397 : Reach 14397 := rs (se 3 (by rfl) ⟨2699, by rfl⟩) (B 5399 (by norm_num) ⟨2699, by rfl⟩ (by norm_num))
theorem R14401 : Reach 14401 := rs (se 2 (by rfl) ⟨5400, by rfl⟩) (B 10801 (by norm_num) ⟨5400, by rfl⟩ (by norm_num))
theorem R14405 : Reach 14405 := rs (se 4 (by rfl) ⟨1350, by rfl⟩) (B 2701 (by norm_num) ⟨1350, by rfl⟩ (by norm_num))
theorem R14409 : Reach 14409 := rs (se 2 (by rfl) ⟨5403, by rfl⟩) (B 10807 (by norm_num) ⟨5403, by rfl⟩ (by norm_num))
theorem R14413 : Reach 14413 := rs (se 3 (by rfl) ⟨2702, by rfl⟩) (B 5405 (by norm_num) ⟨2702, by rfl⟩ (by norm_num))
theorem R14417 : Reach 14417 := rs (se 2 (by rfl) ⟨5406, by rfl⟩) (B 10813 (by norm_num) ⟨5406, by rfl⟩ (by norm_num))
theorem R14421 : Reach 14421 := rs (se 8 (by rfl) ⟨84, by rfl⟩) (B 169 (by norm_num) ⟨84, by rfl⟩ (by norm_num))
theorem R14425 : Reach 14425 := rs (se 2 (by rfl) ⟨5409, by rfl⟩) (B 10819 (by norm_num) ⟨5409, by rfl⟩ (by norm_num))
theorem R14429 : Reach 14429 := rs (se 3 (by rfl) ⟨2705, by rfl⟩) (B 5411 (by norm_num) ⟨2705, by rfl⟩ (by norm_num))
theorem R14433 : Reach 14433 := rs (se 2 (by rfl) ⟨5412, by rfl⟩) (B 10825 (by norm_num) ⟨5412, by rfl⟩ (by norm_num))
theorem R14437 : Reach 14437 := rs (se 4 (by rfl) ⟨1353, by rfl⟩) (B 2707 (by norm_num) ⟨1353, by rfl⟩ (by norm_num))
theorem R14441 : Reach 14441 := rs (se 2 (by rfl) ⟨5415, by rfl⟩) (B 10831 (by norm_num) ⟨5415, by rfl⟩ (by norm_num))
theorem R14445 : Reach 14445 := rs (se 3 (by rfl) ⟨2708, by rfl⟩) (B 5417 (by norm_num) ⟨2708, by rfl⟩ (by norm_num))
theorem R14449 : Reach 14449 := rs (se 2 (by rfl) ⟨5418, by rfl⟩) (B 10837 (by norm_num) ⟨5418, by rfl⟩ (by norm_num))
theorem R14453 : Reach 14453 := rs (se 5 (by rfl) ⟨677, by rfl⟩) (B 1355 (by norm_num) ⟨677, by rfl⟩ (by norm_num))
theorem R14457 : Reach 14457 := rs (se 2 (by rfl) ⟨5421, by rfl⟩) (B 10843 (by norm_num) ⟨5421, by rfl⟩ (by norm_num))
theorem R14461 : Reach 14461 := rs (se 3 (by rfl) ⟨2711, by rfl⟩) (B 5423 (by norm_num) ⟨2711, by rfl⟩ (by norm_num))
theorem R14465 : Reach 14465 := rs (se 2 (by rfl) ⟨5424, by rfl⟩) (B 10849 (by norm_num) ⟨5424, by rfl⟩ (by norm_num))
theorem R14469 : Reach 14469 := rs (se 4 (by rfl) ⟨1356, by rfl⟩) (B 2713 (by norm_num) ⟨1356, by rfl⟩ (by norm_num))
theorem R14473 : Reach 14473 := rs (se 2 (by rfl) ⟨5427, by rfl⟩) (B 10855 (by norm_num) ⟨5427, by rfl⟩ (by norm_num))
theorem R14477 : Reach 14477 := rs (se 3 (by rfl) ⟨2714, by rfl⟩) (B 5429 (by norm_num) ⟨2714, by rfl⟩ (by norm_num))
theorem R14481 : Reach 14481 := rs (se 2 (by rfl) ⟨5430, by rfl⟩) (B 10861 (by norm_num) ⟨5430, by rfl⟩ (by norm_num))
theorem R14485 : Reach 14485 := rs (se 6 (by rfl) ⟨339, by rfl⟩) (B 679 (by norm_num) ⟨339, by rfl⟩ (by norm_num))
theorem R14489 : Reach 14489 := rs (se 2 (by rfl) ⟨5433, by rfl⟩) (B 10867 (by norm_num) ⟨5433, by rfl⟩ (by norm_num))
theorem R14493 : Reach 14493 := rs (se 3 (by rfl) ⟨2717, by rfl⟩) (B 5435 (by norm_num) ⟨2717, by rfl⟩ (by norm_num))
theorem R14497 : Reach 14497 := rs (se 2 (by rfl) ⟨5436, by rfl⟩) (B 10873 (by norm_num) ⟨5436, by rfl⟩ (by norm_num))
theorem R14501 : Reach 14501 := rs (se 4 (by rfl) ⟨1359, by rfl⟩) (B 2719 (by norm_num) ⟨1359, by rfl⟩ (by norm_num))
theorem R14505 : Reach 14505 := rs (se 2 (by rfl) ⟨5439, by rfl⟩) (B 10879 (by norm_num) ⟨5439, by rfl⟩ (by norm_num))
theorem R14509 : Reach 14509 := rs (se 3 (by rfl) ⟨2720, by rfl⟩) (B 5441 (by norm_num) ⟨2720, by rfl⟩ (by norm_num))
theorem R14513 : Reach 14513 := rs (se 2 (by rfl) ⟨5442, by rfl⟩) (B 10885 (by norm_num) ⟨5442, by rfl⟩ (by norm_num))
theorem R14517 : Reach 14517 := rs (se 5 (by rfl) ⟨680, by rfl⟩) (B 1361 (by norm_num) ⟨680, by rfl⟩ (by norm_num))
theorem R14521 : Reach 14521 := rs (se 2 (by rfl) ⟨5445, by rfl⟩) (B 10891 (by norm_num) ⟨5445, by rfl⟩ (by norm_num))
theorem R14525 : Reach 14525 := rs (se 3 (by rfl) ⟨2723, by rfl⟩) (B 5447 (by norm_num) ⟨2723, by rfl⟩ (by norm_num))
theorem R14529 : Reach 14529 := rs (se 2 (by rfl) ⟨5448, by rfl⟩) (B 10897 (by norm_num) ⟨5448, by rfl⟩ (by norm_num))
theorem R14533 : Reach 14533 := rs (se 4 (by rfl) ⟨1362, by rfl⟩) (B 2725 (by norm_num) ⟨1362, by rfl⟩ (by norm_num))
theorem R14537 : Reach 14537 := rs (se 2 (by rfl) ⟨5451, by rfl⟩) (B 10903 (by norm_num) ⟨5451, by rfl⟩ (by norm_num))
theorem R14541 : Reach 14541 := rs (se 3 (by rfl) ⟨2726, by rfl⟩) (B 5453 (by norm_num) ⟨2726, by rfl⟩ (by norm_num))
theorem R14545 : Reach 14545 := rs (se 2 (by rfl) ⟨5454, by rfl⟩) (B 10909 (by norm_num) ⟨5454, by rfl⟩ (by norm_num))
theorem R47317 : Reach 47317 := rs (se 7 (by rfl) ⟨554, by rfl⟩) (B 1109 (by norm_num) ⟨554, by rfl⟩ (by norm_num))
theorem R14549 : Reach 14549 := rs (se 7 (by rfl) ⟨170, by rfl⟩) (B 341 (by norm_num) ⟨170, by rfl⟩ (by norm_num))
theorem R14553 : Reach 14553 := rs (se 2 (by rfl) ⟨5457, by rfl⟩) (B 10915 (by norm_num) ⟨5457, by rfl⟩ (by norm_num))
theorem R14557 : Reach 14557 := rs (se 3 (by rfl) ⟨2729, by rfl⟩) (B 5459 (by norm_num) ⟨2729, by rfl⟩ (by norm_num))
theorem R14561 : Reach 14561 := rs (se 2 (by rfl) ⟨5460, by rfl⟩) (B 10921 (by norm_num) ⟨5460, by rfl⟩ (by norm_num))
theorem R14565 : Reach 14565 := rs (se 4 (by rfl) ⟨1365, by rfl⟩) (B 2731 (by norm_num) ⟨1365, by rfl⟩ (by norm_num))
theorem R14569 : Reach 14569 := rs (se 2 (by rfl) ⟨5463, by rfl⟩) (B 10927 (by norm_num) ⟨5463, by rfl⟩ (by norm_num))
theorem R14573 : Reach 14573 := rs (se 3 (by rfl) ⟨2732, by rfl⟩) (B 5465 (by norm_num) ⟨2732, by rfl⟩ (by norm_num))
theorem R14577 : Reach 14577 := rs (se 2 (by rfl) ⟨5466, by rfl⟩) (B 10933 (by norm_num) ⟨5466, by rfl⟩ (by norm_num))
theorem R14581 : Reach 14581 := rs (se 5 (by rfl) ⟨683, by rfl⟩) (B 1367 (by norm_num) ⟨683, by rfl⟩ (by norm_num))
theorem R14585 : Reach 14585 := rs (se 2 (by rfl) ⟨5469, by rfl⟩) (B 10939 (by norm_num) ⟨5469, by rfl⟩ (by norm_num))
theorem R14589 : Reach 14589 := rs (se 3 (by rfl) ⟨2735, by rfl⟩) (B 5471 (by norm_num) ⟨2735, by rfl⟩ (by norm_num))
theorem R14593 : Reach 14593 := rs (se 2 (by rfl) ⟨5472, by rfl⟩) (B 10945 (by norm_num) ⟨5472, by rfl⟩ (by norm_num))
theorem R14597 : Reach 14597 := rs (se 4 (by rfl) ⟨1368, by rfl⟩) (B 2737 (by norm_num) ⟨1368, by rfl⟩ (by norm_num))
theorem R14601 : Reach 14601 := rs (se 2 (by rfl) ⟨5475, by rfl⟩) (B 10951 (by norm_num) ⟨5475, by rfl⟩ (by norm_num))
theorem R14605 : Reach 14605 := rs (se 3 (by rfl) ⟨2738, by rfl⟩) (B 5477 (by norm_num) ⟨2738, by rfl⟩ (by norm_num))
theorem R14609 : Reach 14609 := rs (se 2 (by rfl) ⟨5478, by rfl⟩) (B 10957 (by norm_num) ⟨5478, by rfl⟩ (by norm_num))
theorem R14613 : Reach 14613 := rs (se 6 (by rfl) ⟨342, by rfl⟩) (B 685 (by norm_num) ⟨342, by rfl⟩ (by norm_num))
theorem R14617 : Reach 14617 := rs (se 2 (by rfl) ⟨5481, by rfl⟩) (B 10963 (by norm_num) ⟨5481, by rfl⟩ (by norm_num))
theorem R14621 : Reach 14621 := rs (se 3 (by rfl) ⟨2741, by rfl⟩) (B 5483 (by norm_num) ⟨2741, by rfl⟩ (by norm_num))
theorem R14625 : Reach 14625 := rs (se 2 (by rfl) ⟨5484, by rfl⟩) (B 10969 (by norm_num) ⟨5484, by rfl⟩ (by norm_num))
theorem R14629 : Reach 14629 := rs (se 4 (by rfl) ⟨1371, by rfl⟩) (B 2743 (by norm_num) ⟨1371, by rfl⟩ (by norm_num))
theorem R14633 : Reach 14633 := rs (se 2 (by rfl) ⟨5487, by rfl⟩) (B 10975 (by norm_num) ⟨5487, by rfl⟩ (by norm_num))
theorem R14637 : Reach 14637 := rs (se 3 (by rfl) ⟨2744, by rfl⟩) (B 5489 (by norm_num) ⟨2744, by rfl⟩ (by norm_num))
theorem R14641 : Reach 14641 := rs (se 2 (by rfl) ⟨5490, by rfl⟩) (B 10981 (by norm_num) ⟨5490, by rfl⟩ (by norm_num))
theorem R14645 : Reach 14645 := rs (se 5 (by rfl) ⟨686, by rfl⟩) (B 1373 (by norm_num) ⟨686, by rfl⟩ (by norm_num))
theorem R14649 : Reach 14649 := rs (se 2 (by rfl) ⟨5493, by rfl⟩) (B 10987 (by norm_num) ⟨5493, by rfl⟩ (by norm_num))
theorem R14653 : Reach 14653 := rs (se 3 (by rfl) ⟨2747, by rfl⟩) (B 5495 (by norm_num) ⟨2747, by rfl⟩ (by norm_num))
theorem R14657 : Reach 14657 := rs (se 2 (by rfl) ⟨5496, by rfl⟩) (B 10993 (by norm_num) ⟨5496, by rfl⟩ (by norm_num))
theorem R14661 : Reach 14661 := rs (se 4 (by rfl) ⟨1374, by rfl⟩) (B 2749 (by norm_num) ⟨1374, by rfl⟩ (by norm_num))
theorem R14665 : Reach 14665 := rs (se 2 (by rfl) ⟨5499, by rfl⟩) (B 10999 (by norm_num) ⟨5499, by rfl⟩ (by norm_num))
theorem R14669 : Reach 14669 := rs (se 3 (by rfl) ⟨2750, by rfl⟩) (B 5501 (by norm_num) ⟨2750, by rfl⟩ (by norm_num))
theorem R14673 : Reach 14673 := rs (se 2 (by rfl) ⟨5502, by rfl⟩) (B 11005 (by norm_num) ⟨5502, by rfl⟩ (by norm_num))
theorem R14677 : Reach 14677 := rs (se 10 (by rfl) ⟨21, by rfl⟩) (B 43 (by norm_num) ⟨21, by rfl⟩ (by norm_num))
theorem R14681 : Reach 14681 := rs (se 2 (by rfl) ⟨5505, by rfl⟩) (B 11011 (by norm_num) ⟨5505, by rfl⟩ (by norm_num))
theorem R14685 : Reach 14685 := rs (se 3 (by rfl) ⟨2753, by rfl⟩) (B 5507 (by norm_num) ⟨2753, by rfl⟩ (by norm_num))
theorem R14689 : Reach 14689 := rs (se 2 (by rfl) ⟨5508, by rfl⟩) (B 11017 (by norm_num) ⟨5508, by rfl⟩ (by norm_num))
theorem R14693 : Reach 14693 := rs (se 4 (by rfl) ⟨1377, by rfl⟩) (B 2755 (by norm_num) ⟨1377, by rfl⟩ (by norm_num))
theorem R14697 : Reach 14697 := rs (se 2 (by rfl) ⟨5511, by rfl⟩) (B 11023 (by norm_num) ⟨5511, by rfl⟩ (by norm_num))
theorem R14701 : Reach 14701 := rs (se 3 (by rfl) ⟨2756, by rfl⟩) (B 5513 (by norm_num) ⟨2756, by rfl⟩ (by norm_num))
theorem R14705 : Reach 14705 := rs (se 2 (by rfl) ⟨5514, by rfl⟩) (B 11029 (by norm_num) ⟨5514, by rfl⟩ (by norm_num))
theorem R14709 : Reach 14709 := rs (se 5 (by rfl) ⟨689, by rfl⟩) (B 1379 (by norm_num) ⟨689, by rfl⟩ (by norm_num))
theorem R14713 : Reach 14713 := rs (se 2 (by rfl) ⟨5517, by rfl⟩) (B 11035 (by norm_num) ⟨5517, by rfl⟩ (by norm_num))
theorem R14717 : Reach 14717 := rs (se 3 (by rfl) ⟨2759, by rfl⟩) (B 5519 (by norm_num) ⟨2759, by rfl⟩ (by norm_num))
theorem R14721 : Reach 14721 := rs (se 2 (by rfl) ⟨5520, by rfl⟩) (B 11041 (by norm_num) ⟨5520, by rfl⟩ (by norm_num))
theorem R14725 : Reach 14725 := rs (se 4 (by rfl) ⟨1380, by rfl⟩) (B 2761 (by norm_num) ⟨1380, by rfl⟩ (by norm_num))
theorem R14729 : Reach 14729 := rs (se 2 (by rfl) ⟨5523, by rfl⟩) (B 11047 (by norm_num) ⟨5523, by rfl⟩ (by norm_num))
theorem R14733 : Reach 14733 := rs (se 3 (by rfl) ⟨2762, by rfl⟩) (B 5525 (by norm_num) ⟨2762, by rfl⟩ (by norm_num))
theorem R14737 : Reach 14737 := rs (se 2 (by rfl) ⟨5526, by rfl⟩) (B 11053 (by norm_num) ⟨5526, by rfl⟩ (by norm_num))
theorem R14741 : Reach 14741 := rs (se 6 (by rfl) ⟨345, by rfl⟩) (B 691 (by norm_num) ⟨345, by rfl⟩ (by norm_num))
theorem R14745 : Reach 14745 := rs (se 2 (by rfl) ⟨5529, by rfl⟩) (B 11059 (by norm_num) ⟨5529, by rfl⟩ (by norm_num))
theorem R14749 : Reach 14749 := rs (se 3 (by rfl) ⟨2765, by rfl⟩) (B 5531 (by norm_num) ⟨2765, by rfl⟩ (by norm_num))
theorem R14753 : Reach 14753 := rs (se 2 (by rfl) ⟨5532, by rfl⟩) (B 11065 (by norm_num) ⟨5532, by rfl⟩ (by norm_num))
theorem R14757 : Reach 14757 := rs (se 4 (by rfl) ⟨1383, by rfl⟩) (B 2767 (by norm_num) ⟨1383, by rfl⟩ (by norm_num))
theorem R14761 : Reach 14761 := rs (se 2 (by rfl) ⟨5535, by rfl⟩) (B 11071 (by norm_num) ⟨5535, by rfl⟩ (by norm_num))
theorem R14765 : Reach 14765 := rs (se 3 (by rfl) ⟨2768, by rfl⟩) (B 5537 (by norm_num) ⟨2768, by rfl⟩ (by norm_num))
theorem R14769 : Reach 14769 := rs (se 2 (by rfl) ⟨5538, by rfl⟩) (B 11077 (by norm_num) ⟨5538, by rfl⟩ (by norm_num))
theorem R14773 : Reach 14773 := rs (se 5 (by rfl) ⟨692, by rfl⟩) (B 1385 (by norm_num) ⟨692, by rfl⟩ (by norm_num))
theorem R14777 : Reach 14777 := rs (se 2 (by rfl) ⟨5541, by rfl⟩) (B 11083 (by norm_num) ⟨5541, by rfl⟩ (by norm_num))
theorem R14781 : Reach 14781 := rs (se 3 (by rfl) ⟨2771, by rfl⟩) (B 5543 (by norm_num) ⟨2771, by rfl⟩ (by norm_num))
theorem R14785 : Reach 14785 := rs (se 2 (by rfl) ⟨5544, by rfl⟩) (B 11089 (by norm_num) ⟨5544, by rfl⟩ (by norm_num))
theorem R14789 : Reach 14789 := rs (se 4 (by rfl) ⟨1386, by rfl⟩) (B 2773 (by norm_num) ⟨1386, by rfl⟩ (by norm_num))
theorem R14793 : Reach 14793 := rs (se 2 (by rfl) ⟨5547, by rfl⟩) (B 11095 (by norm_num) ⟨5547, by rfl⟩ (by norm_num))
theorem R14797 : Reach 14797 := rs (se 3 (by rfl) ⟨2774, by rfl⟩) (B 5549 (by norm_num) ⟨2774, by rfl⟩ (by norm_num))
theorem R14801 : Reach 14801 := rs (se 2 (by rfl) ⟨5550, by rfl⟩) (B 11101 (by norm_num) ⟨5550, by rfl⟩ (by norm_num))
theorem R47573 : Reach 47573 := rs (se 7 (by rfl) ⟨557, by rfl⟩) (B 1115 (by norm_num) ⟨557, by rfl⟩ (by norm_num))
theorem R14805 : Reach 14805 := rs (se 7 (by rfl) ⟨173, by rfl⟩) (B 347 (by norm_num) ⟨173, by rfl⟩ (by norm_num))
theorem R14809 : Reach 14809 := rs (se 2 (by rfl) ⟨5553, by rfl⟩) (B 11107 (by norm_num) ⟨5553, by rfl⟩ (by norm_num))
theorem R14813 : Reach 14813 := rs (se 3 (by rfl) ⟨2777, by rfl⟩) (B 5555 (by norm_num) ⟨2777, by rfl⟩ (by norm_num))
theorem R14817 : Reach 14817 := rs (se 2 (by rfl) ⟨5556, by rfl⟩) (B 11113 (by norm_num) ⟨5556, by rfl⟩ (by norm_num))
theorem R14821 : Reach 14821 := rs (se 4 (by rfl) ⟨1389, by rfl⟩) (B 2779 (by norm_num) ⟨1389, by rfl⟩ (by norm_num))
theorem R14825 : Reach 14825 := rs (se 2 (by rfl) ⟨5559, by rfl⟩) (B 11119 (by norm_num) ⟨5559, by rfl⟩ (by norm_num))
theorem R14829 : Reach 14829 := rs (se 3 (by rfl) ⟨2780, by rfl⟩) (B 5561 (by norm_num) ⟨2780, by rfl⟩ (by norm_num))
theorem R14833 : Reach 14833 := rs (se 2 (by rfl) ⟨5562, by rfl⟩) (B 11125 (by norm_num) ⟨5562, by rfl⟩ (by norm_num))
theorem R14837 : Reach 14837 := rs (se 5 (by rfl) ⟨695, by rfl⟩) (B 1391 (by norm_num) ⟨695, by rfl⟩ (by norm_num))
theorem R14841 : Reach 14841 := rs (se 2 (by rfl) ⟨5565, by rfl⟩) (B 11131 (by norm_num) ⟨5565, by rfl⟩ (by norm_num))
theorem R14845 : Reach 14845 := rs (se 3 (by rfl) ⟨2783, by rfl⟩) (B 5567 (by norm_num) ⟨2783, by rfl⟩ (by norm_num))
theorem R14849 : Reach 14849 := rs (se 2 (by rfl) ⟨5568, by rfl⟩) (B 11137 (by norm_num) ⟨5568, by rfl⟩ (by norm_num))
theorem R14853 : Reach 14853 := rs (se 4 (by rfl) ⟨1392, by rfl⟩) (B 2785 (by norm_num) ⟨1392, by rfl⟩ (by norm_num))
theorem R14857 : Reach 14857 := rs (se 2 (by rfl) ⟨5571, by rfl⟩) (B 11143 (by norm_num) ⟨5571, by rfl⟩ (by norm_num))
theorem R14861 : Reach 14861 := rs (se 3 (by rfl) ⟨2786, by rfl⟩) (B 5573 (by norm_num) ⟨2786, by rfl⟩ (by norm_num))
theorem R14865 : Reach 14865 := rs (se 2 (by rfl) ⟨5574, by rfl⟩) (B 11149 (by norm_num) ⟨5574, by rfl⟩ (by norm_num))
theorem R14869 : Reach 14869 := rs (se 6 (by rfl) ⟨348, by rfl⟩) (B 697 (by norm_num) ⟨348, by rfl⟩ (by norm_num))
theorem R14873 : Reach 14873 := rs (se 2 (by rfl) ⟨5577, by rfl⟩) (B 11155 (by norm_num) ⟨5577, by rfl⟩ (by norm_num))
theorem R14877 : Reach 14877 := rs (se 3 (by rfl) ⟨2789, by rfl⟩) (B 5579 (by norm_num) ⟨2789, by rfl⟩ (by norm_num))
theorem R14881 : Reach 14881 := rs (se 2 (by rfl) ⟨5580, by rfl⟩) (B 11161 (by norm_num) ⟨5580, by rfl⟩ (by norm_num))
theorem R14885 : Reach 14885 := rs (se 4 (by rfl) ⟨1395, by rfl⟩) (B 2791 (by norm_num) ⟨1395, by rfl⟩ (by norm_num))
theorem R14889 : Reach 14889 := rs (se 2 (by rfl) ⟨5583, by rfl⟩) (B 11167 (by norm_num) ⟨5583, by rfl⟩ (by norm_num))
theorem R14893 : Reach 14893 := rs (se 3 (by rfl) ⟨2792, by rfl⟩) (B 5585 (by norm_num) ⟨2792, by rfl⟩ (by norm_num))
theorem R14897 : Reach 14897 := rs (se 2 (by rfl) ⟨5586, by rfl⟩) (B 11173 (by norm_num) ⟨5586, by rfl⟩ (by norm_num))
theorem R14901 : Reach 14901 := rs (se 5 (by rfl) ⟨698, by rfl⟩) (B 1397 (by norm_num) ⟨698, by rfl⟩ (by norm_num))
theorem R14905 : Reach 14905 := rs (se 2 (by rfl) ⟨5589, by rfl⟩) (B 11179 (by norm_num) ⟨5589, by rfl⟩ (by norm_num))
theorem R14909 : Reach 14909 := rs (se 3 (by rfl) ⟨2795, by rfl⟩) (B 5591 (by norm_num) ⟨2795, by rfl⟩ (by norm_num))
theorem R14913 : Reach 14913 := rs (se 2 (by rfl) ⟨5592, by rfl⟩) (B 11185 (by norm_num) ⟨5592, by rfl⟩ (by norm_num))
theorem R14917 : Reach 14917 := rs (se 4 (by rfl) ⟨1398, by rfl⟩) (B 2797 (by norm_num) ⟨1398, by rfl⟩ (by norm_num))
theorem R14921 : Reach 14921 := rs (se 2 (by rfl) ⟨5595, by rfl⟩) (B 11191 (by norm_num) ⟨5595, by rfl⟩ (by norm_num))
theorem R14925 : Reach 14925 := rs (se 3 (by rfl) ⟨2798, by rfl⟩) (B 5597 (by norm_num) ⟨2798, by rfl⟩ (by norm_num))
theorem R14929 : Reach 14929 := rs (se 2 (by rfl) ⟨5598, by rfl⟩) (B 11197 (by norm_num) ⟨5598, by rfl⟩ (by norm_num))
theorem R113237 : Reach 113237 := rs (se 8 (by rfl) ⟨663, by rfl⟩) (B 1327 (by norm_num) ⟨663, by rfl⟩ (by norm_num))
theorem R14933 : Reach 14933 := rs (se 8 (by rfl) ⟨87, by rfl⟩) (B 175 (by norm_num) ⟨87, by rfl⟩ (by norm_num))
theorem R14937 : Reach 14937 := rs (se 2 (by rfl) ⟨5601, by rfl⟩) (B 11203 (by norm_num) ⟨5601, by rfl⟩ (by norm_num))
theorem R14941 : Reach 14941 := rs (se 3 (by rfl) ⟨2801, by rfl⟩) (B 5603 (by norm_num) ⟨2801, by rfl⟩ (by norm_num))
theorem R14945 : Reach 14945 := rs (se 2 (by rfl) ⟨5604, by rfl⟩) (B 11209 (by norm_num) ⟨5604, by rfl⟩ (by norm_num))
theorem R47717 : Reach 47717 := rs (se 4 (by rfl) ⟨4473, by rfl⟩) (B 8947 (by norm_num) ⟨4473, by rfl⟩ (by norm_num))
theorem R14949 : Reach 14949 := rs (se 4 (by rfl) ⟨1401, by rfl⟩) (B 2803 (by norm_num) ⟨1401, by rfl⟩ (by norm_num))
theorem R14953 : Reach 14953 := rs (se 2 (by rfl) ⟨5607, by rfl⟩) (B 11215 (by norm_num) ⟨5607, by rfl⟩ (by norm_num))
theorem R14957 : Reach 14957 := rs (se 3 (by rfl) ⟨2804, by rfl⟩) (B 5609 (by norm_num) ⟨2804, by rfl⟩ (by norm_num))
theorem R14961 : Reach 14961 := rs (se 2 (by rfl) ⟨5610, by rfl⟩) (B 11221 (by norm_num) ⟨5610, by rfl⟩ (by norm_num))
theorem R14965 : Reach 14965 := rs (se 5 (by rfl) ⟨701, by rfl⟩) (B 1403 (by norm_num) ⟨701, by rfl⟩ (by norm_num))
theorem R113269 : Reach 113269 := rs (se 5 (by rfl) ⟨5309, by rfl⟩) (B 10619 (by norm_num) ⟨5309, by rfl⟩ (by norm_num))
theorem R14969 : Reach 14969 := rs (se 2 (by rfl) ⟨5613, by rfl⟩) (B 11227 (by norm_num) ⟨5613, by rfl⟩ (by norm_num))
theorem R14973 : Reach 14973 := rs (se 3 (by rfl) ⟨2807, by rfl⟩) (B 5615 (by norm_num) ⟨2807, by rfl⟩ (by norm_num))
theorem R14977 : Reach 14977 := rs (se 2 (by rfl) ⟨5616, by rfl⟩) (B 11233 (by norm_num) ⟨5616, by rfl⟩ (by norm_num))
theorem R14981 : Reach 14981 := rs (se 4 (by rfl) ⟨1404, by rfl⟩) (B 2809 (by norm_num) ⟨1404, by rfl⟩ (by norm_num))
theorem R47749 : Reach 47749 := rs (se 4 (by rfl) ⟨4476, by rfl⟩) (B 8953 (by norm_num) ⟨4476, by rfl⟩ (by norm_num))
theorem R14985 : Reach 14985 := rs (se 2 (by rfl) ⟨5619, by rfl⟩) (B 11239 (by norm_num) ⟨5619, by rfl⟩ (by norm_num))
theorem R14989 : Reach 14989 := rs (se 3 (by rfl) ⟨2810, by rfl⟩) (B 5621 (by norm_num) ⟨2810, by rfl⟩ (by norm_num))
theorem R14993 : Reach 14993 := rs (se 2 (by rfl) ⟨5622, by rfl⟩) (B 11245 (by norm_num) ⟨5622, by rfl⟩ (by norm_num))
theorem R14997 : Reach 14997 := rs (se 6 (by rfl) ⟨351, by rfl⟩) (B 703 (by norm_num) ⟨351, by rfl⟩ (by norm_num))
theorem R15001 : Reach 15001 := rs (se 2 (by rfl) ⟨5625, by rfl⟩) (B 11251 (by norm_num) ⟨5625, by rfl⟩ (by norm_num))
theorem R15005 : Reach 15005 := rs (se 3 (by rfl) ⟨2813, by rfl⟩) (B 5627 (by norm_num) ⟨2813, by rfl⟩ (by norm_num))
theorem R15009 : Reach 15009 := rs (se 2 (by rfl) ⟨5628, by rfl⟩) (B 11257 (by norm_num) ⟨5628, by rfl⟩ (by norm_num))
theorem R15013 : Reach 15013 := rs (se 4 (by rfl) ⟨1407, by rfl⟩) (B 2815 (by norm_num) ⟨1407, by rfl⟩ (by norm_num))
theorem R15017 : Reach 15017 := rs (se 2 (by rfl) ⟨5631, by rfl⟩) (B 11263 (by norm_num) ⟨5631, by rfl⟩ (by norm_num))
theorem R15021 : Reach 15021 := rs (se 3 (by rfl) ⟨2816, by rfl⟩) (B 5633 (by norm_num) ⟨2816, by rfl⟩ (by norm_num))
theorem R15025 : Reach 15025 := rs (se 2 (by rfl) ⟨5634, by rfl⟩) (B 11269 (by norm_num) ⟨5634, by rfl⟩ (by norm_num))
theorem R15029 : Reach 15029 := rs (se 5 (by rfl) ⟨704, by rfl⟩) (B 1409 (by norm_num) ⟨704, by rfl⟩ (by norm_num))
theorem R15033 : Reach 15033 := rs (se 2 (by rfl) ⟨5637, by rfl⟩) (B 11275 (by norm_num) ⟨5637, by rfl⟩ (by norm_num))
theorem R15037 : Reach 15037 := rs (se 3 (by rfl) ⟨2819, by rfl⟩) (B 5639 (by norm_num) ⟨2819, by rfl⟩ (by norm_num))
theorem R15041 : Reach 15041 := rs (se 2 (by rfl) ⟨5640, by rfl⟩) (B 11281 (by norm_num) ⟨5640, by rfl⟩ (by norm_num))
theorem R15045 : Reach 15045 := rs (se 4 (by rfl) ⟨1410, by rfl⟩) (B 2821 (by norm_num) ⟨1410, by rfl⟩ (by norm_num))
theorem R15049 : Reach 15049 := rs (se 2 (by rfl) ⟨5643, by rfl⟩) (B 11287 (by norm_num) ⟨5643, by rfl⟩ (by norm_num))
theorem R15053 : Reach 15053 := rs (se 3 (by rfl) ⟨2822, by rfl⟩) (B 5645 (by norm_num) ⟨2822, by rfl⟩ (by norm_num))
theorem R15057 : Reach 15057 := rs (se 2 (by rfl) ⟨5646, by rfl⟩) (B 11293 (by norm_num) ⟨5646, by rfl⟩ (by norm_num))
theorem R15061 : Reach 15061 := rs (se 7 (by rfl) ⟨176, by rfl⟩) (B 353 (by norm_num) ⟨176, by rfl⟩ (by norm_num))
theorem R15065 : Reach 15065 := rs (se 2 (by rfl) ⟨5649, by rfl⟩) (B 11299 (by norm_num) ⟨5649, by rfl⟩ (by norm_num))
theorem R15069 : Reach 15069 := rs (se 3 (by rfl) ⟨2825, by rfl⟩) (B 5651 (by norm_num) ⟨2825, by rfl⟩ (by norm_num))
theorem R15073 : Reach 15073 := rs (se 2 (by rfl) ⟨5652, by rfl⟩) (B 11305 (by norm_num) ⟨5652, by rfl⟩ (by norm_num))
theorem R15077 : Reach 15077 := rs (se 4 (by rfl) ⟨1413, by rfl⟩) (B 2827 (by norm_num) ⟨1413, by rfl⟩ (by norm_num))
theorem R15081 : Reach 15081 := rs (se 2 (by rfl) ⟨5655, by rfl⟩) (B 11311 (by norm_num) ⟨5655, by rfl⟩ (by norm_num))
theorem R15085 : Reach 15085 := rs (se 3 (by rfl) ⟨2828, by rfl⟩) (B 5657 (by norm_num) ⟨2828, by rfl⟩ (by norm_num))
theorem R15089 : Reach 15089 := rs (se 2 (by rfl) ⟨5658, by rfl⟩) (B 11317 (by norm_num) ⟨5658, by rfl⟩ (by norm_num))
theorem R15093 : Reach 15093 := rs (se 5 (by rfl) ⟨707, by rfl⟩) (B 1415 (by norm_num) ⟨707, by rfl⟩ (by norm_num))
theorem R47861 : Reach 47861 := rs (se 5 (by rfl) ⟨2243, by rfl⟩) (B 4487 (by norm_num) ⟨2243, by rfl⟩ (by norm_num))
theorem R15097 : Reach 15097 := rs (se 2 (by rfl) ⟨5661, by rfl⟩) (B 11323 (by norm_num) ⟨5661, by rfl⟩ (by norm_num))
theorem R15101 : Reach 15101 := rs (se 3 (by rfl) ⟨2831, by rfl⟩) (B 5663 (by norm_num) ⟨2831, by rfl⟩ (by norm_num))
theorem R15105 : Reach 15105 := rs (se 2 (by rfl) ⟨5664, by rfl⟩) (B 11329 (by norm_num) ⟨5664, by rfl⟩ (by norm_num))
theorem R15109 : Reach 15109 := rs (se 4 (by rfl) ⟨1416, by rfl⟩) (B 2833 (by norm_num) ⟨1416, by rfl⟩ (by norm_num))
theorem R15113 : Reach 15113 := rs (se 2 (by rfl) ⟨5667, by rfl⟩) (B 11335 (by norm_num) ⟨5667, by rfl⟩ (by norm_num))
theorem R15117 : Reach 15117 := rs (se 3 (by rfl) ⟨2834, by rfl⟩) (B 5669 (by norm_num) ⟨2834, by rfl⟩ (by norm_num))
theorem R15121 : Reach 15121 := rs (se 2 (by rfl) ⟨5670, by rfl⟩) (B 11341 (by norm_num) ⟨5670, by rfl⟩ (by norm_num))
theorem R15125 : Reach 15125 := rs (se 6 (by rfl) ⟨354, by rfl⟩) (B 709 (by norm_num) ⟨354, by rfl⟩ (by norm_num))
theorem R15129 : Reach 15129 := rs (se 2 (by rfl) ⟨5673, by rfl⟩) (B 11347 (by norm_num) ⟨5673, by rfl⟩ (by norm_num))
theorem R15133 : Reach 15133 := rs (se 3 (by rfl) ⟨2837, by rfl⟩) (B 5675 (by norm_num) ⟨2837, by rfl⟩ (by norm_num))
theorem R15137 : Reach 15137 := rs (se 2 (by rfl) ⟨5676, by rfl⟩) (B 11353 (by norm_num) ⟨5676, by rfl⟩ (by norm_num))
theorem R15141 : Reach 15141 := rs (se 4 (by rfl) ⟨1419, by rfl⟩) (B 2839 (by norm_num) ⟨1419, by rfl⟩ (by norm_num))
theorem R15145 : Reach 15145 := rs (se 2 (by rfl) ⟨5679, by rfl⟩) (B 11359 (by norm_num) ⟨5679, by rfl⟩ (by norm_num))
theorem R15149 : Reach 15149 := rs (se 3 (by rfl) ⟨2840, by rfl⟩) (B 5681 (by norm_num) ⟨2840, by rfl⟩ (by norm_num))
theorem R15153 : Reach 15153 := rs (se 2 (by rfl) ⟨5682, by rfl⟩) (B 11365 (by norm_num) ⟨5682, by rfl⟩ (by norm_num))
theorem R15157 : Reach 15157 := rs (se 5 (by rfl) ⟨710, by rfl⟩) (B 1421 (by norm_num) ⟨710, by rfl⟩ (by norm_num))
theorem R15161 : Reach 15161 := rs (se 2 (by rfl) ⟨5685, by rfl⟩) (B 11371 (by norm_num) ⟨5685, by rfl⟩ (by norm_num))
theorem R15165 : Reach 15165 := rs (se 3 (by rfl) ⟨2843, by rfl⟩) (B 5687 (by norm_num) ⟨2843, by rfl⟩ (by norm_num))
theorem R15169 : Reach 15169 := rs (se 2 (by rfl) ⟨5688, by rfl⟩) (B 11377 (by norm_num) ⟨5688, by rfl⟩ (by norm_num))
theorem R15173 : Reach 15173 := rs (se 4 (by rfl) ⟨1422, by rfl⟩) (B 2845 (by norm_num) ⟨1422, by rfl⟩ (by norm_num))
theorem R15177 : Reach 15177 := rs (se 2 (by rfl) ⟨5691, by rfl⟩) (B 11383 (by norm_num) ⟨5691, by rfl⟩ (by norm_num))
theorem R15181 : Reach 15181 := rs (se 3 (by rfl) ⟨2846, by rfl⟩) (B 5693 (by norm_num) ⟨2846, by rfl⟩ (by norm_num))
theorem R15185 : Reach 15185 := rs (se 2 (by rfl) ⟨5694, by rfl⟩) (B 11389 (by norm_num) ⟨5694, by rfl⟩ (by norm_num))
theorem R15189 : Reach 15189 := rs (se 9 (by rfl) ⟨44, by rfl⟩) (B 89 (by norm_num) ⟨44, by rfl⟩ (by norm_num))
theorem R15193 : Reach 15193 := rs (se 2 (by rfl) ⟨5697, by rfl⟩) (B 11395 (by norm_num) ⟨5697, by rfl⟩ (by norm_num))
theorem R15197 : Reach 15197 := rs (se 3 (by rfl) ⟨2849, by rfl⟩) (B 5699 (by norm_num) ⟨2849, by rfl⟩ (by norm_num))
theorem R15201 : Reach 15201 := rs (se 2 (by rfl) ⟨5700, by rfl⟩) (B 11401 (by norm_num) ⟨5700, by rfl⟩ (by norm_num))
theorem R15205 : Reach 15205 := rs (se 4 (by rfl) ⟨1425, by rfl⟩) (B 2851 (by norm_num) ⟨1425, by rfl⟩ (by norm_num))
theorem R15209 : Reach 15209 := rs (se 2 (by rfl) ⟨5703, by rfl⟩) (B 11407 (by norm_num) ⟨5703, by rfl⟩ (by norm_num))
theorem R15213 : Reach 15213 := rs (se 3 (by rfl) ⟨2852, by rfl⟩) (B 5705 (by norm_num) ⟨2852, by rfl⟩ (by norm_num))
theorem R15217 : Reach 15217 := rs (se 2 (by rfl) ⟨5706, by rfl⟩) (B 11413 (by norm_num) ⟨5706, by rfl⟩ (by norm_num))
theorem R15221 : Reach 15221 := rs (se 5 (by rfl) ⟨713, by rfl⟩) (B 1427 (by norm_num) ⟨713, by rfl⟩ (by norm_num))
theorem R15225 : Reach 15225 := rs (se 2 (by rfl) ⟨5709, by rfl⟩) (B 11419 (by norm_num) ⟨5709, by rfl⟩ (by norm_num))
theorem R15229 : Reach 15229 := rs (se 3 (by rfl) ⟨2855, by rfl⟩) (B 5711 (by norm_num) ⟨2855, by rfl⟩ (by norm_num))
theorem R15233 : Reach 15233 := rs (se 2 (by rfl) ⟨5712, by rfl⟩) (B 11425 (by norm_num) ⟨5712, by rfl⟩ (by norm_num))
theorem R48005 : Reach 48005 := rs (se 4 (by rfl) ⟨4500, by rfl⟩) (B 9001 (by norm_num) ⟨4500, by rfl⟩ (by norm_num))
theorem R15237 : Reach 15237 := rs (se 4 (by rfl) ⟨1428, by rfl⟩) (B 2857 (by norm_num) ⟨1428, by rfl⟩ (by norm_num))
theorem R15241 : Reach 15241 := rs (se 2 (by rfl) ⟨5715, by rfl⟩) (B 11431 (by norm_num) ⟨5715, by rfl⟩ (by norm_num))
theorem R15245 : Reach 15245 := rs (se 3 (by rfl) ⟨2858, by rfl⟩) (B 5717 (by norm_num) ⟨2858, by rfl⟩ (by norm_num))
theorem R15249 : Reach 15249 := rs (se 2 (by rfl) ⟨5718, by rfl⟩) (B 11437 (by norm_num) ⟨5718, by rfl⟩ (by norm_num))
theorem R15253 : Reach 15253 := rs (se 6 (by rfl) ⟨357, by rfl⟩) (B 715 (by norm_num) ⟨357, by rfl⟩ (by norm_num))
theorem R15257 : Reach 15257 := rs (se 2 (by rfl) ⟨5721, by rfl⟩) (B 11443 (by norm_num) ⟨5721, by rfl⟩ (by norm_num))
theorem R15261 : Reach 15261 := rs (se 3 (by rfl) ⟨2861, by rfl⟩) (B 5723 (by norm_num) ⟨2861, by rfl⟩ (by norm_num))
theorem R15265 : Reach 15265 := rs (se 2 (by rfl) ⟨5724, by rfl⟩) (B 11449 (by norm_num) ⟨5724, by rfl⟩ (by norm_num))
theorem R15269 : Reach 15269 := rs (se 4 (by rfl) ⟨1431, by rfl⟩) (B 2863 (by norm_num) ⟨1431, by rfl⟩ (by norm_num))
theorem R15273 : Reach 15273 := rs (se 2 (by rfl) ⟨5727, by rfl⟩) (B 11455 (by norm_num) ⟨5727, by rfl⟩ (by norm_num))
theorem R15277 : Reach 15277 := rs (se 3 (by rfl) ⟨2864, by rfl⟩) (B 5729 (by norm_num) ⟨2864, by rfl⟩ (by norm_num))
theorem R15281 : Reach 15281 := rs (se 2 (by rfl) ⟨5730, by rfl⟩) (B 11461 (by norm_num) ⟨5730, by rfl⟩ (by norm_num))
theorem R15285 : Reach 15285 := rs (se 5 (by rfl) ⟨716, by rfl⟩) (B 1433 (by norm_num) ⟨716, by rfl⟩ (by norm_num))
theorem R48053 : Reach 48053 := rs (se 5 (by rfl) ⟨2252, by rfl⟩) (B 4505 (by norm_num) ⟨2252, by rfl⟩ (by norm_num))
theorem R15289 : Reach 15289 := rs (se 2 (by rfl) ⟨5733, by rfl⟩) (B 11467 (by norm_num) ⟨5733, by rfl⟩ (by norm_num))
theorem R15293 : Reach 15293 := rs (se 3 (by rfl) ⟨2867, by rfl⟩) (B 5735 (by norm_num) ⟨2867, by rfl⟩ (by norm_num))
theorem R15297 : Reach 15297 := rs (se 2 (by rfl) ⟨5736, by rfl⟩) (B 11473 (by norm_num) ⟨5736, by rfl⟩ (by norm_num))
theorem R15301 : Reach 15301 := rs (se 4 (by rfl) ⟨1434, by rfl⟩) (B 2869 (by norm_num) ⟨1434, by rfl⟩ (by norm_num))
theorem R15305 : Reach 15305 := rs (se 2 (by rfl) ⟨5739, by rfl⟩) (B 11479 (by norm_num) ⟨5739, by rfl⟩ (by norm_num))
theorem R15309 : Reach 15309 := rs (se 3 (by rfl) ⟨2870, by rfl⟩) (B 5741 (by norm_num) ⟨2870, by rfl⟩ (by norm_num))
theorem R15313 : Reach 15313 := rs (se 2 (by rfl) ⟨5742, by rfl⟩) (B 11485 (by norm_num) ⟨5742, by rfl⟩ (by norm_num))
theorem R15317 : Reach 15317 := rs (se 7 (by rfl) ⟨179, by rfl⟩) (B 359 (by norm_num) ⟨179, by rfl⟩ (by norm_num))
theorem R15321 : Reach 15321 := rs (se 2 (by rfl) ⟨5745, by rfl⟩) (B 11491 (by norm_num) ⟨5745, by rfl⟩ (by norm_num))
theorem R15325 : Reach 15325 := rs (se 3 (by rfl) ⟨2873, by rfl⟩) (B 5747 (by norm_num) ⟨2873, by rfl⟩ (by norm_num))
theorem R15329 : Reach 15329 := rs (se 2 (by rfl) ⟨5748, by rfl⟩) (B 11497 (by norm_num) ⟨5748, by rfl⟩ (by norm_num))
theorem R15333 : Reach 15333 := rs (se 4 (by rfl) ⟨1437, by rfl⟩) (B 2875 (by norm_num) ⟨1437, by rfl⟩ (by norm_num))
theorem R15337 : Reach 15337 := rs (se 2 (by rfl) ⟨5751, by rfl⟩) (B 11503 (by norm_num) ⟨5751, by rfl⟩ (by norm_num))
theorem R15341 : Reach 15341 := rs (se 3 (by rfl) ⟨2876, by rfl⟩) (B 5753 (by norm_num) ⟨2876, by rfl⟩ (by norm_num))
theorem R15345 : Reach 15345 := rs (se 2 (by rfl) ⟨5754, by rfl⟩) (B 11509 (by norm_num) ⟨5754, by rfl⟩ (by norm_num))
theorem R15349 : Reach 15349 := rs (se 5 (by rfl) ⟨719, by rfl⟩) (B 1439 (by norm_num) ⟨719, by rfl⟩ (by norm_num))
theorem R80885 : Reach 80885 := rs (se 5 (by rfl) ⟨3791, by rfl⟩) (B 7583 (by norm_num) ⟨3791, by rfl⟩ (by norm_num))
theorem R15353 : Reach 15353 := rs (se 2 (by rfl) ⟨5757, by rfl⟩) (B 11515 (by norm_num) ⟨5757, by rfl⟩ (by norm_num))
theorem R15357 : Reach 15357 := rs (se 3 (by rfl) ⟨2879, by rfl⟩) (B 5759 (by norm_num) ⟨2879, by rfl⟩ (by norm_num))
theorem R15361 : Reach 15361 := rs (se 2 (by rfl) ⟨5760, by rfl⟩) (B 11521 (by norm_num) ⟨5760, by rfl⟩ (by norm_num))
theorem R15365 : Reach 15365 := rs (se 4 (by rfl) ⟨1440, by rfl⟩) (B 2881 (by norm_num) ⟨1440, by rfl⟩ (by norm_num))
theorem R15369 : Reach 15369 := rs (se 2 (by rfl) ⟨5763, by rfl⟩) (B 11527 (by norm_num) ⟨5763, by rfl⟩ (by norm_num))
theorem R15373 : Reach 15373 := rs (se 3 (by rfl) ⟨2882, by rfl⟩) (B 5765 (by norm_num) ⟨2882, by rfl⟩ (by norm_num))
theorem R15377 : Reach 15377 := rs (se 2 (by rfl) ⟨5766, by rfl⟩) (B 11533 (by norm_num) ⟨5766, by rfl⟩ (by norm_num))
theorem R15381 : Reach 15381 := rs (se 6 (by rfl) ⟨360, by rfl⟩) (B 721 (by norm_num) ⟨360, by rfl⟩ (by norm_num))
theorem R15385 : Reach 15385 := rs (se 2 (by rfl) ⟨5769, by rfl⟩) (B 11539 (by norm_num) ⟨5769, by rfl⟩ (by norm_num))
theorem R15389 : Reach 15389 := rs (se 3 (by rfl) ⟨2885, by rfl⟩) (B 5771 (by norm_num) ⟨2885, by rfl⟩ (by norm_num))
theorem R15393 : Reach 15393 := rs (se 2 (by rfl) ⟨5772, by rfl⟩) (B 11545 (by norm_num) ⟨5772, by rfl⟩ (by norm_num))
theorem R15397 : Reach 15397 := rs (se 4 (by rfl) ⟨1443, by rfl⟩) (B 2887 (by norm_num) ⟨1443, by rfl⟩ (by norm_num))
theorem R15401 : Reach 15401 := rs (se 2 (by rfl) ⟨5775, by rfl⟩) (B 11551 (by norm_num) ⟨5775, by rfl⟩ (by norm_num))
theorem R15405 : Reach 15405 := rs (se 3 (by rfl) ⟨2888, by rfl⟩) (B 5777 (by norm_num) ⟨2888, by rfl⟩ (by norm_num))
theorem R15409 : Reach 15409 := rs (se 2 (by rfl) ⟨5778, by rfl⟩) (B 11557 (by norm_num) ⟨5778, by rfl⟩ (by norm_num))
theorem R15413 : Reach 15413 := rs (se 5 (by rfl) ⟨722, by rfl⟩) (B 1445 (by norm_num) ⟨722, by rfl⟩ (by norm_num))
theorem R113717 : Reach 113717 := rs (se 5 (by rfl) ⟨5330, by rfl⟩) (B 10661 (by norm_num) ⟨5330, by rfl⟩ (by norm_num))
theorem R15417 : Reach 15417 := rs (se 2 (by rfl) ⟨5781, by rfl⟩) (B 11563 (by norm_num) ⟨5781, by rfl⟩ (by norm_num))
theorem R15421 : Reach 15421 := rs (se 3 (by rfl) ⟨2891, by rfl⟩) (B 5783 (by norm_num) ⟨2891, by rfl⟩ (by norm_num))
theorem R15425 : Reach 15425 := rs (se 2 (by rfl) ⟨5784, by rfl⟩) (B 11569 (by norm_num) ⟨5784, by rfl⟩ (by norm_num))
theorem R15429 : Reach 15429 := rs (se 4 (by rfl) ⟨1446, by rfl⟩) (B 2893 (by norm_num) ⟨1446, by rfl⟩ (by norm_num))
theorem R15433 : Reach 15433 := rs (se 2 (by rfl) ⟨5787, by rfl⟩) (B 11575 (by norm_num) ⟨5787, by rfl⟩ (by norm_num))
theorem R15437 : Reach 15437 := rs (se 3 (by rfl) ⟨2894, by rfl⟩) (B 5789 (by norm_num) ⟨2894, by rfl⟩ (by norm_num))
theorem R15441 : Reach 15441 := rs (se 2 (by rfl) ⟨5790, by rfl⟩) (B 11581 (by norm_num) ⟨5790, by rfl⟩ (by norm_num))
theorem R15445 : Reach 15445 := rs (se 8 (by rfl) ⟨90, by rfl⟩) (B 181 (by norm_num) ⟨90, by rfl⟩ (by norm_num))
theorem R15449 : Reach 15449 := rs (se 2 (by rfl) ⟨5793, by rfl⟩) (B 11587 (by norm_num) ⟨5793, by rfl⟩ (by norm_num))
theorem R15453 : Reach 15453 := rs (se 3 (by rfl) ⟨2897, by rfl⟩) (B 5795 (by norm_num) ⟨2897, by rfl⟩ (by norm_num))
theorem R15457 : Reach 15457 := rs (se 2 (by rfl) ⟨5796, by rfl⟩) (B 11593 (by norm_num) ⟨5796, by rfl⟩ (by norm_num))
theorem R15461 : Reach 15461 := rs (se 4 (by rfl) ⟨1449, by rfl⟩) (B 2899 (by norm_num) ⟨1449, by rfl⟩ (by norm_num))
theorem R15465 : Reach 15465 := rs (se 2 (by rfl) ⟨5799, by rfl⟩) (B 11599 (by norm_num) ⟨5799, by rfl⟩ (by norm_num))
theorem R15469 : Reach 15469 := rs (se 3 (by rfl) ⟨2900, by rfl⟩) (B 5801 (by norm_num) ⟨2900, by rfl⟩ (by norm_num))
theorem R15473 : Reach 15473 := rs (se 2 (by rfl) ⟨5802, by rfl⟩) (B 11605 (by norm_num) ⟨5802, by rfl⟩ (by norm_num))
theorem R15477 : Reach 15477 := rs (se 5 (by rfl) ⟨725, by rfl⟩) (B 1451 (by norm_num) ⟨725, by rfl⟩ (by norm_num))
theorem R15481 : Reach 15481 := rs (se 2 (by rfl) ⟨5805, by rfl⟩) (B 11611 (by norm_num) ⟨5805, by rfl⟩ (by norm_num))
theorem R15485 : Reach 15485 := rs (se 3 (by rfl) ⟨2903, by rfl⟩) (B 5807 (by norm_num) ⟨2903, by rfl⟩ (by norm_num))
theorem R15489 : Reach 15489 := rs (se 2 (by rfl) ⟨5808, by rfl⟩) (B 11617 (by norm_num) ⟨5808, by rfl⟩ (by norm_num))
theorem R15493 : Reach 15493 := rs (se 4 (by rfl) ⟨1452, by rfl⟩) (B 2905 (by norm_num) ⟨1452, by rfl⟩ (by norm_num))
theorem R15497 : Reach 15497 := rs (se 2 (by rfl) ⟨5811, by rfl⟩) (B 11623 (by norm_num) ⟨5811, by rfl⟩ (by norm_num))
theorem R15501 : Reach 15501 := rs (se 3 (by rfl) ⟨2906, by rfl⟩) (B 5813 (by norm_num) ⟨2906, by rfl⟩ (by norm_num))
theorem R15505 : Reach 15505 := rs (se 2 (by rfl) ⟨5814, by rfl⟩) (B 11629 (by norm_num) ⟨5814, by rfl⟩ (by norm_num))
theorem R15509 : Reach 15509 := rs (se 6 (by rfl) ⟨363, by rfl⟩) (B 727 (by norm_num) ⟨363, by rfl⟩ (by norm_num))
theorem R15513 : Reach 15513 := rs (se 2 (by rfl) ⟨5817, by rfl⟩) (B 11635 (by norm_num) ⟨5817, by rfl⟩ (by norm_num))
theorem R15517 : Reach 15517 := rs (se 3 (by rfl) ⟨2909, by rfl⟩) (B 5819 (by norm_num) ⟨2909, by rfl⟩ (by norm_num))
theorem R15521 : Reach 15521 := rs (se 2 (by rfl) ⟨5820, by rfl⟩) (B 11641 (by norm_num) ⟨5820, by rfl⟩ (by norm_num))
theorem R15525 : Reach 15525 := rs (se 4 (by rfl) ⟨1455, by rfl⟩) (B 2911 (by norm_num) ⟨1455, by rfl⟩ (by norm_num))
theorem R15529 : Reach 15529 := rs (se 2 (by rfl) ⟨5823, by rfl⟩) (B 11647 (by norm_num) ⟨5823, by rfl⟩ (by norm_num))
theorem R15533 : Reach 15533 := rs (se 3 (by rfl) ⟨2912, by rfl⟩) (B 5825 (by norm_num) ⟨2912, by rfl⟩ (by norm_num))
theorem R15537 : Reach 15537 := rs (se 2 (by rfl) ⟨5826, by rfl⟩) (B 11653 (by norm_num) ⟨5826, by rfl⟩ (by norm_num))
theorem R15541 : Reach 15541 := rs (se 5 (by rfl) ⟨728, by rfl⟩) (B 1457 (by norm_num) ⟨728, by rfl⟩ (by norm_num))
theorem R113845 : Reach 113845 := rs (se 5 (by rfl) ⟨5336, by rfl⟩) (B 10673 (by norm_num) ⟨5336, by rfl⟩ (by norm_num))
theorem R15545 : Reach 15545 := rs (se 2 (by rfl) ⟨5829, by rfl⟩) (B 11659 (by norm_num) ⟨5829, by rfl⟩ (by norm_num))
theorem R15549 : Reach 15549 := rs (se 3 (by rfl) ⟨2915, by rfl⟩) (B 5831 (by norm_num) ⟨2915, by rfl⟩ (by norm_num))
theorem R15553 : Reach 15553 := rs (se 2 (by rfl) ⟨5832, by rfl⟩) (B 11665 (by norm_num) ⟨5832, by rfl⟩ (by norm_num))
theorem R15557 : Reach 15557 := rs (se 4 (by rfl) ⟨1458, by rfl⟩) (B 2917 (by norm_num) ⟨1458, by rfl⟩ (by norm_num))
theorem R15561 : Reach 15561 := rs (se 2 (by rfl) ⟨5835, by rfl⟩) (B 11671 (by norm_num) ⟨5835, by rfl⟩ (by norm_num))
theorem R15565 : Reach 15565 := rs (se 3 (by rfl) ⟨2918, by rfl⟩) (B 5837 (by norm_num) ⟨2918, by rfl⟩ (by norm_num))
theorem R15569 : Reach 15569 := rs (se 2 (by rfl) ⟨5838, by rfl⟩) (B 11677 (by norm_num) ⟨5838, by rfl⟩ (by norm_num))
theorem R15573 : Reach 15573 := rs (se 7 (by rfl) ⟨182, by rfl⟩) (B 365 (by norm_num) ⟨182, by rfl⟩ (by norm_num))
theorem R15577 : Reach 15577 := rs (se 2 (by rfl) ⟨5841, by rfl⟩) (B 11683 (by norm_num) ⟨5841, by rfl⟩ (by norm_num))
theorem R15581 : Reach 15581 := rs (se 3 (by rfl) ⟨2921, by rfl⟩) (B 5843 (by norm_num) ⟨2921, by rfl⟩ (by norm_num))
theorem R15585 : Reach 15585 := rs (se 2 (by rfl) ⟨5844, by rfl⟩) (B 11689 (by norm_num) ⟨5844, by rfl⟩ (by norm_num))
theorem R15589 : Reach 15589 := rs (se 4 (by rfl) ⟨1461, by rfl⟩) (B 2923 (by norm_num) ⟨1461, by rfl⟩ (by norm_num))
theorem R15593 : Reach 15593 := rs (se 2 (by rfl) ⟨5847, by rfl⟩) (B 11695 (by norm_num) ⟨5847, by rfl⟩ (by norm_num))
theorem R15597 : Reach 15597 := rs (se 3 (by rfl) ⟨2924, by rfl⟩) (B 5849 (by norm_num) ⟨2924, by rfl⟩ (by norm_num))
theorem R15601 : Reach 15601 := rs (se 2 (by rfl) ⟨5850, by rfl⟩) (B 11701 (by norm_num) ⟨5850, by rfl⟩ (by norm_num))
theorem R15605 : Reach 15605 := rs (se 5 (by rfl) ⟨731, by rfl⟩) (B 1463 (by norm_num) ⟨731, by rfl⟩ (by norm_num))
theorem R15609 : Reach 15609 := rs (se 2 (by rfl) ⟨5853, by rfl⟩) (B 11707 (by norm_num) ⟨5853, by rfl⟩ (by norm_num))
theorem R15613 : Reach 15613 := rs (se 3 (by rfl) ⟨2927, by rfl⟩) (B 5855 (by norm_num) ⟨2927, by rfl⟩ (by norm_num))
theorem R15617 : Reach 15617 := rs (se 2 (by rfl) ⟨5856, by rfl⟩) (B 11713 (by norm_num) ⟨5856, by rfl⟩ (by norm_num))
theorem R15621 : Reach 15621 := rs (se 4 (by rfl) ⟨1464, by rfl⟩) (B 2929 (by norm_num) ⟨1464, by rfl⟩ (by norm_num))
theorem R15625 : Reach 15625 := rs (se 2 (by rfl) ⟨5859, by rfl⟩) (B 11719 (by norm_num) ⟨5859, by rfl⟩ (by norm_num))
theorem R15629 : Reach 15629 := rs (se 3 (by rfl) ⟨2930, by rfl⟩) (B 5861 (by norm_num) ⟨2930, by rfl⟩ (by norm_num))
theorem R15633 : Reach 15633 := rs (se 2 (by rfl) ⟨5862, by rfl⟩) (B 11725 (by norm_num) ⟨5862, by rfl⟩ (by norm_num))
theorem R15637 : Reach 15637 := rs (se 6 (by rfl) ⟨366, by rfl⟩) (B 733 (by norm_num) ⟨366, by rfl⟩ (by norm_num))
theorem R15641 : Reach 15641 := rs (se 2 (by rfl) ⟨5865, by rfl⟩) (B 11731 (by norm_num) ⟨5865, by rfl⟩ (by norm_num))
theorem R15645 : Reach 15645 := rs (se 3 (by rfl) ⟨2933, by rfl⟩) (B 5867 (by norm_num) ⟨2933, by rfl⟩ (by norm_num))
theorem R15649 : Reach 15649 := rs (se 2 (by rfl) ⟨5868, by rfl⟩) (B 11737 (by norm_num) ⟨5868, by rfl⟩ (by norm_num))
theorem R15653 : Reach 15653 := rs (se 4 (by rfl) ⟨1467, by rfl⟩) (B 2935 (by norm_num) ⟨1467, by rfl⟩ (by norm_num))
theorem R15657 : Reach 15657 := rs (se 2 (by rfl) ⟨5871, by rfl⟩) (B 11743 (by norm_num) ⟨5871, by rfl⟩ (by norm_num))
theorem R15661 : Reach 15661 := rs (se 3 (by rfl) ⟨2936, by rfl⟩) (B 5873 (by norm_num) ⟨2936, by rfl⟩ (by norm_num))
theorem R15665 : Reach 15665 := rs (se 2 (by rfl) ⟨5874, by rfl⟩) (B 11749 (by norm_num) ⟨5874, by rfl⟩ (by norm_num))
theorem R48437 : Reach 48437 := rs (se 5 (by rfl) ⟨2270, by rfl⟩) (B 4541 (by norm_num) ⟨2270, by rfl⟩ (by norm_num))
theorem R15669 : Reach 15669 := rs (se 5 (by rfl) ⟨734, by rfl⟩) (B 1469 (by norm_num) ⟨734, by rfl⟩ (by norm_num))
theorem R15673 : Reach 15673 := rs (se 2 (by rfl) ⟨5877, by rfl⟩) (B 11755 (by norm_num) ⟨5877, by rfl⟩ (by norm_num))
theorem R15677 : Reach 15677 := rs (se 3 (by rfl) ⟨2939, by rfl⟩) (B 5879 (by norm_num) ⟨2939, by rfl⟩ (by norm_num))
theorem R15681 : Reach 15681 := rs (se 2 (by rfl) ⟨5880, by rfl⟩) (B 11761 (by norm_num) ⟨5880, by rfl⟩ (by norm_num))
theorem R15685 : Reach 15685 := rs (se 4 (by rfl) ⟨1470, by rfl⟩) (B 2941 (by norm_num) ⟨1470, by rfl⟩ (by norm_num))
theorem R15689 : Reach 15689 := rs (se 2 (by rfl) ⟨5883, by rfl⟩) (B 11767 (by norm_num) ⟨5883, by rfl⟩ (by norm_num))
theorem R15693 : Reach 15693 := rs (se 3 (by rfl) ⟨2942, by rfl⟩) (B 5885 (by norm_num) ⟨2942, by rfl⟩ (by norm_num))
theorem R15697 : Reach 15697 := rs (se 2 (by rfl) ⟨5886, by rfl⟩) (B 11773 (by norm_num) ⟨5886, by rfl⟩ (by norm_num))
theorem R15701 : Reach 15701 := rs (se 11 (by rfl) ⟨11, by rfl⟩) (B 23 (by norm_num) ⟨11, by rfl⟩ (by norm_num))
theorem R15705 : Reach 15705 := rs (se 2 (by rfl) ⟨5889, by rfl⟩) (B 11779 (by norm_num) ⟨5889, by rfl⟩ (by norm_num))
theorem R15709 : Reach 15709 := rs (se 3 (by rfl) ⟨2945, by rfl⟩) (B 5891 (by norm_num) ⟨2945, by rfl⟩ (by norm_num))
theorem R15713 : Reach 15713 := rs (se 2 (by rfl) ⟨5892, by rfl⟩) (B 11785 (by norm_num) ⟨5892, by rfl⟩ (by norm_num))
theorem R15717 : Reach 15717 := rs (se 4 (by rfl) ⟨1473, by rfl⟩) (B 2947 (by norm_num) ⟨1473, by rfl⟩ (by norm_num))
theorem R15721 : Reach 15721 := rs (se 2 (by rfl) ⟨5895, by rfl⟩) (B 11791 (by norm_num) ⟨5895, by rfl⟩ (by norm_num))
theorem R15725 : Reach 15725 := rs (se 3 (by rfl) ⟨2948, by rfl⟩) (B 5897 (by norm_num) ⟨2948, by rfl⟩ (by norm_num))
theorem R15729 : Reach 15729 := rs (se 2 (by rfl) ⟨5898, by rfl⟩) (B 11797 (by norm_num) ⟨5898, by rfl⟩ (by norm_num))
theorem R15733 : Reach 15733 := rs (se 5 (by rfl) ⟨737, by rfl⟩) (B 1475 (by norm_num) ⟨737, by rfl⟩ (by norm_num))
theorem R15737 : Reach 15737 := rs (se 2 (by rfl) ⟨5901, by rfl⟩) (B 11803 (by norm_num) ⟨5901, by rfl⟩ (by norm_num))
theorem R15741 : Reach 15741 := rs (se 3 (by rfl) ⟨2951, by rfl⟩) (B 5903 (by norm_num) ⟨2951, by rfl⟩ (by norm_num))
theorem R15745 : Reach 15745 := rs (se 2 (by rfl) ⟨5904, by rfl⟩) (B 11809 (by norm_num) ⟨5904, by rfl⟩ (by norm_num))
theorem R15749 : Reach 15749 := rs (se 4 (by rfl) ⟨1476, by rfl⟩) (B 2953 (by norm_num) ⟨1476, by rfl⟩ (by norm_num))
theorem R15753 : Reach 15753 := rs (se 2 (by rfl) ⟨5907, by rfl⟩) (B 11815 (by norm_num) ⟨5907, by rfl⟩ (by norm_num))
theorem R15757 : Reach 15757 := rs (se 3 (by rfl) ⟨2954, by rfl⟩) (B 5909 (by norm_num) ⟨2954, by rfl⟩ (by norm_num))
theorem R15761 : Reach 15761 := rs (se 2 (by rfl) ⟨5910, by rfl⟩) (B 11821 (by norm_num) ⟨5910, by rfl⟩ (by norm_num))
theorem R15765 : Reach 15765 := rs (se 6 (by rfl) ⟨369, by rfl⟩) (B 739 (by norm_num) ⟨369, by rfl⟩ (by norm_num))
theorem R15769 : Reach 15769 := rs (se 2 (by rfl) ⟨5913, by rfl⟩) (B 11827 (by norm_num) ⟨5913, by rfl⟩ (by norm_num))
theorem R15773 : Reach 15773 := rs (se 3 (by rfl) ⟨2957, by rfl⟩) (B 5915 (by norm_num) ⟨2957, by rfl⟩ (by norm_num))
theorem R15777 : Reach 15777 := rs (se 2 (by rfl) ⟨5916, by rfl⟩) (B 11833 (by norm_num) ⟨5916, by rfl⟩ (by norm_num))
theorem R15781 : Reach 15781 := rs (se 4 (by rfl) ⟨1479, by rfl⟩) (B 2959 (by norm_num) ⟨1479, by rfl⟩ (by norm_num))
theorem R15785 : Reach 15785 := rs (se 2 (by rfl) ⟨5919, by rfl⟩) (B 11839 (by norm_num) ⟨5919, by rfl⟩ (by norm_num))
theorem R15789 : Reach 15789 := rs (se 3 (by rfl) ⟨2960, by rfl⟩) (B 5921 (by norm_num) ⟨2960, by rfl⟩ (by norm_num))
theorem R15793 : Reach 15793 := rs (se 2 (by rfl) ⟨5922, by rfl⟩) (B 11845 (by norm_num) ⟨5922, by rfl⟩ (by norm_num))
theorem R15797 : Reach 15797 := rs (se 5 (by rfl) ⟨740, by rfl⟩) (B 1481 (by norm_num) ⟨740, by rfl⟩ (by norm_num))
theorem R114101 : Reach 114101 := rs (se 5 (by rfl) ⟨5348, by rfl⟩) (B 10697 (by norm_num) ⟨5348, by rfl⟩ (by norm_num))
theorem R15801 : Reach 15801 := rs (se 2 (by rfl) ⟨5925, by rfl⟩) (B 11851 (by norm_num) ⟨5925, by rfl⟩ (by norm_num))
theorem R15805 : Reach 15805 := rs (se 3 (by rfl) ⟨2963, by rfl⟩) (B 5927 (by norm_num) ⟨2963, by rfl⟩ (by norm_num))
theorem R15809 : Reach 15809 := rs (se 2 (by rfl) ⟨5928, by rfl⟩) (B 11857 (by norm_num) ⟨5928, by rfl⟩ (by norm_num))
theorem R15813 : Reach 15813 := rs (se 4 (by rfl) ⟨1482, by rfl⟩) (B 2965 (by norm_num) ⟨1482, by rfl⟩ (by norm_num))
theorem R15817 : Reach 15817 := rs (se 2 (by rfl) ⟨5931, by rfl⟩) (B 11863 (by norm_num) ⟨5931, by rfl⟩ (by norm_num))
theorem R15821 : Reach 15821 := rs (se 3 (by rfl) ⟨2966, by rfl⟩) (B 5933 (by norm_num) ⟨2966, by rfl⟩ (by norm_num))
theorem R15825 : Reach 15825 := rs (se 2 (by rfl) ⟨5934, by rfl⟩) (B 11869 (by norm_num) ⟨5934, by rfl⟩ (by norm_num))
theorem R15829 : Reach 15829 := rs (se 7 (by rfl) ⟨185, by rfl⟩) (B 371 (by norm_num) ⟨185, by rfl⟩ (by norm_num))
theorem R15833 : Reach 15833 := rs (se 2 (by rfl) ⟨5937, by rfl⟩) (B 11875 (by norm_num) ⟨5937, by rfl⟩ (by norm_num))
theorem R15837 : Reach 15837 := rs (se 3 (by rfl) ⟨2969, by rfl⟩) (B 5939 (by norm_num) ⟨2969, by rfl⟩ (by norm_num))
theorem R15841 : Reach 15841 := rs (se 2 (by rfl) ⟨5940, by rfl⟩) (B 11881 (by norm_num) ⟨5940, by rfl⟩ (by norm_num))
theorem R15845 : Reach 15845 := rs (se 4 (by rfl) ⟨1485, by rfl⟩) (B 2971 (by norm_num) ⟨1485, by rfl⟩ (by norm_num))
theorem R15849 : Reach 15849 := rs (se 2 (by rfl) ⟨5943, by rfl⟩) (B 11887 (by norm_num) ⟨5943, by rfl⟩ (by norm_num))
theorem R15853 : Reach 15853 := rs (se 3 (by rfl) ⟨2972, by rfl⟩) (B 5945 (by norm_num) ⟨2972, by rfl⟩ (by norm_num))
theorem R15857 : Reach 15857 := rs (se 2 (by rfl) ⟨5946, by rfl⟩) (B 11893 (by norm_num) ⟨5946, by rfl⟩ (by norm_num))
theorem R15861 : Reach 15861 := rs (se 5 (by rfl) ⟨743, by rfl⟩) (B 1487 (by norm_num) ⟨743, by rfl⟩ (by norm_num))
theorem R15865 : Reach 15865 := rs (se 2 (by rfl) ⟨5949, by rfl⟩) (B 11899 (by norm_num) ⟨5949, by rfl⟩ (by norm_num))
theorem R15869 : Reach 15869 := rs (se 3 (by rfl) ⟨2975, by rfl⟩) (B 5951 (by norm_num) ⟨2975, by rfl⟩ (by norm_num))
theorem R15873 : Reach 15873 := rs (se 2 (by rfl) ⟨5952, by rfl⟩) (B 11905 (by norm_num) ⟨5952, by rfl⟩ (by norm_num))
theorem R15877 : Reach 15877 := rs (se 4 (by rfl) ⟨1488, by rfl⟩) (B 2977 (by norm_num) ⟨1488, by rfl⟩ (by norm_num))
theorem R15881 : Reach 15881 := rs (se 2 (by rfl) ⟨5955, by rfl⟩) (B 11911 (by norm_num) ⟨5955, by rfl⟩ (by norm_num))
theorem R15885 : Reach 15885 := rs (se 3 (by rfl) ⟨2978, by rfl⟩) (B 5957 (by norm_num) ⟨2978, by rfl⟩ (by norm_num))
theorem R15889 : Reach 15889 := rs (se 2 (by rfl) ⟨5958, by rfl⟩) (B 11917 (by norm_num) ⟨5958, by rfl⟩ (by norm_num))
theorem R15893 : Reach 15893 := rs (se 6 (by rfl) ⟨372, by rfl⟩) (B 745 (by norm_num) ⟨372, by rfl⟩ (by norm_num))
theorem R15897 : Reach 15897 := rs (se 2 (by rfl) ⟨5961, by rfl⟩) (B 11923 (by norm_num) ⟨5961, by rfl⟩ (by norm_num))
theorem R15901 : Reach 15901 := rs (se 3 (by rfl) ⟨2981, by rfl⟩) (B 5963 (by norm_num) ⟨2981, by rfl⟩ (by norm_num))
theorem R15905 : Reach 15905 := rs (se 2 (by rfl) ⟨5964, by rfl⟩) (B 11929 (by norm_num) ⟨5964, by rfl⟩ (by norm_num))
theorem R15909 : Reach 15909 := rs (se 4 (by rfl) ⟨1491, by rfl⟩) (B 2983 (by norm_num) ⟨1491, by rfl⟩ (by norm_num))
theorem R15913 : Reach 15913 := rs (se 2 (by rfl) ⟨5967, by rfl⟩) (B 11935 (by norm_num) ⟨5967, by rfl⟩ (by norm_num))
theorem R15917 : Reach 15917 := rs (se 3 (by rfl) ⟨2984, by rfl⟩) (B 5969 (by norm_num) ⟨2984, by rfl⟩ (by norm_num))
theorem R15921 : Reach 15921 := rs (se 2 (by rfl) ⟨5970, by rfl⟩) (B 11941 (by norm_num) ⟨5970, by rfl⟩ (by norm_num))
theorem R15925 : Reach 15925 := rs (se 5 (by rfl) ⟨746, by rfl⟩) (B 1493 (by norm_num) ⟨746, by rfl⟩ (by norm_num))
theorem R15929 : Reach 15929 := rs (se 2 (by rfl) ⟨5973, by rfl⟩) (B 11947 (by norm_num) ⟨5973, by rfl⟩ (by norm_num))
theorem R15933 : Reach 15933 := rs (se 3 (by rfl) ⟨2987, by rfl⟩) (B 5975 (by norm_num) ⟨2987, by rfl⟩ (by norm_num))
theorem R15937 : Reach 15937 := rs (se 2 (by rfl) ⟨5976, by rfl⟩) (B 11953 (by norm_num) ⟨5976, by rfl⟩ (by norm_num))
theorem R15941 : Reach 15941 := rs (se 4 (by rfl) ⟨1494, by rfl⟩) (B 2989 (by norm_num) ⟨1494, by rfl⟩ (by norm_num))
theorem R15945 : Reach 15945 := rs (se 2 (by rfl) ⟨5979, by rfl⟩) (B 11959 (by norm_num) ⟨5979, by rfl⟩ (by norm_num))
theorem R15949 : Reach 15949 := rs (se 3 (by rfl) ⟨2990, by rfl⟩) (B 5981 (by norm_num) ⟨2990, by rfl⟩ (by norm_num))
theorem R15953 : Reach 15953 := rs (se 2 (by rfl) ⟨5982, by rfl⟩) (B 11965 (by norm_num) ⟨5982, by rfl⟩ (by norm_num))
theorem R15957 : Reach 15957 := rs (se 8 (by rfl) ⟨93, by rfl⟩) (B 187 (by norm_num) ⟨93, by rfl⟩ (by norm_num))
theorem R15961 : Reach 15961 := rs (se 2 (by rfl) ⟨5985, by rfl⟩) (B 11971 (by norm_num) ⟨5985, by rfl⟩ (by norm_num))
theorem R15965 : Reach 15965 := rs (se 3 (by rfl) ⟨2993, by rfl⟩) (B 5987 (by norm_num) ⟨2993, by rfl⟩ (by norm_num))
theorem R15969 : Reach 15969 := rs (se 2 (by rfl) ⟨5988, by rfl⟩) (B 11977 (by norm_num) ⟨5988, by rfl⟩ (by norm_num))
theorem R15973 : Reach 15973 := rs (se 4 (by rfl) ⟨1497, by rfl⟩) (B 2995 (by norm_num) ⟨1497, by rfl⟩ (by norm_num))
theorem R15977 : Reach 15977 := rs (se 2 (by rfl) ⟨5991, by rfl⟩) (B 11983 (by norm_num) ⟨5991, by rfl⟩ (by norm_num))
theorem R15981 : Reach 15981 := rs (se 3 (by rfl) ⟨2996, by rfl⟩) (B 5993 (by norm_num) ⟨2996, by rfl⟩ (by norm_num))
theorem R15985 : Reach 15985 := rs (se 2 (by rfl) ⟨5994, by rfl⟩) (B 11989 (by norm_num) ⟨5994, by rfl⟩ (by norm_num))
theorem R15989 : Reach 15989 := rs (se 5 (by rfl) ⟨749, by rfl⟩) (B 1499 (by norm_num) ⟨749, by rfl⟩ (by norm_num))
theorem R15993 : Reach 15993 := rs (se 2 (by rfl) ⟨5997, by rfl⟩) (B 11995 (by norm_num) ⟨5997, by rfl⟩ (by norm_num))
theorem R15997 : Reach 15997 := rs (se 3 (by rfl) ⟨2999, by rfl⟩) (B 5999 (by norm_num) ⟨2999, by rfl⟩ (by norm_num))
theorem R16001 : Reach 16001 := rs (se 2 (by rfl) ⟨6000, by rfl⟩) (B 12001 (by norm_num) ⟨6000, by rfl⟩ (by norm_num))
theorem R16005 : Reach 16005 := rs (se 4 (by rfl) ⟨1500, by rfl⟩) (B 3001 (by norm_num) ⟨1500, by rfl⟩ (by norm_num))
theorem R16009 : Reach 16009 := rs (se 2 (by rfl) ⟨6003, by rfl⟩) (B 12007 (by norm_num) ⟨6003, by rfl⟩ (by norm_num))
theorem R16013 : Reach 16013 := rs (se 3 (by rfl) ⟨3002, by rfl⟩) (B 6005 (by norm_num) ⟨3002, by rfl⟩ (by norm_num))
theorem R16017 : Reach 16017 := rs (se 2 (by rfl) ⟨6006, by rfl⟩) (B 12013 (by norm_num) ⟨6006, by rfl⟩ (by norm_num))
theorem R81557 : Reach 81557 := rs (se 6 (by rfl) ⟨1911, by rfl⟩) (B 3823 (by norm_num) ⟨1911, by rfl⟩ (by norm_num))
theorem R16021 : Reach 16021 := rs (se 6 (by rfl) ⟨375, by rfl⟩) (B 751 (by norm_num) ⟨375, by rfl⟩ (by norm_num))
theorem R16025 : Reach 16025 := rs (se 2 (by rfl) ⟨6009, by rfl⟩) (B 12019 (by norm_num) ⟨6009, by rfl⟩ (by norm_num))
theorem R16029 : Reach 16029 := rs (se 3 (by rfl) ⟨3005, by rfl⟩) (B 6011 (by norm_num) ⟨3005, by rfl⟩ (by norm_num))
theorem R16033 : Reach 16033 := rs (se 2 (by rfl) ⟨6012, by rfl⟩) (B 12025 (by norm_num) ⟨6012, by rfl⟩ (by norm_num))
theorem R16037 : Reach 16037 := rs (se 4 (by rfl) ⟨1503, by rfl⟩) (B 3007 (by norm_num) ⟨1503, by rfl⟩ (by norm_num))
theorem R16041 : Reach 16041 := rs (se 2 (by rfl) ⟨6015, by rfl⟩) (B 12031 (by norm_num) ⟨6015, by rfl⟩ (by norm_num))
theorem R16045 : Reach 16045 := rs (se 3 (by rfl) ⟨3008, by rfl⟩) (B 6017 (by norm_num) ⟨3008, by rfl⟩ (by norm_num))
theorem R16049 : Reach 16049 := rs (se 2 (by rfl) ⟨6018, by rfl⟩) (B 12037 (by norm_num) ⟨6018, by rfl⟩ (by norm_num))
theorem R16053 : Reach 16053 := rs (se 5 (by rfl) ⟨752, by rfl⟩) (B 1505 (by norm_num) ⟨752, by rfl⟩ (by norm_num))
theorem R16057 : Reach 16057 := rs (se 2 (by rfl) ⟨6021, by rfl⟩) (B 12043 (by norm_num) ⟨6021, by rfl⟩ (by norm_num))
theorem R16061 : Reach 16061 := rs (se 3 (by rfl) ⟨3011, by rfl⟩) (B 6023 (by norm_num) ⟨3011, by rfl⟩ (by norm_num))
theorem R16065 : Reach 16065 := rs (se 2 (by rfl) ⟨6024, by rfl⟩) (B 12049 (by norm_num) ⟨6024, by rfl⟩ (by norm_num))
theorem R16069 : Reach 16069 := rs (se 4 (by rfl) ⟨1506, by rfl⟩) (B 3013 (by norm_num) ⟨1506, by rfl⟩ (by norm_num))
theorem R16073 : Reach 16073 := rs (se 2 (by rfl) ⟨6027, by rfl⟩) (B 12055 (by norm_num) ⟨6027, by rfl⟩ (by norm_num))
theorem R16077 : Reach 16077 := rs (se 3 (by rfl) ⟨3014, by rfl⟩) (B 6029 (by norm_num) ⟨3014, by rfl⟩ (by norm_num))
theorem R16081 : Reach 16081 := rs (se 2 (by rfl) ⟨6030, by rfl⟩) (B 12061 (by norm_num) ⟨6030, by rfl⟩ (by norm_num))
theorem R16085 : Reach 16085 := rs (se 7 (by rfl) ⟨188, by rfl⟩) (B 377 (by norm_num) ⟨188, by rfl⟩ (by norm_num))
theorem R16089 : Reach 16089 := rs (se 2 (by rfl) ⟨6033, by rfl⟩) (B 12067 (by norm_num) ⟨6033, by rfl⟩ (by norm_num))
theorem R16093 : Reach 16093 := rs (se 3 (by rfl) ⟨3017, by rfl⟩) (B 6035 (by norm_num) ⟨3017, by rfl⟩ (by norm_num))
theorem R16097 : Reach 16097 := rs (se 2 (by rfl) ⟨6036, by rfl⟩) (B 12073 (by norm_num) ⟨6036, by rfl⟩ (by norm_num))
theorem R48869 : Reach 48869 := rs (se 4 (by rfl) ⟨4581, by rfl⟩) (B 9163 (by norm_num) ⟨4581, by rfl⟩ (by norm_num))
theorem R16101 : Reach 16101 := rs (se 4 (by rfl) ⟨1509, by rfl⟩) (B 3019 (by norm_num) ⟨1509, by rfl⟩ (by norm_num))
theorem R16105 : Reach 16105 := rs (se 2 (by rfl) ⟨6039, by rfl⟩) (B 12079 (by norm_num) ⟨6039, by rfl⟩ (by norm_num))
theorem R16109 : Reach 16109 := rs (se 3 (by rfl) ⟨3020, by rfl⟩) (B 6041 (by norm_num) ⟨3020, by rfl⟩ (by norm_num))
theorem R16113 : Reach 16113 := rs (se 2 (by rfl) ⟨6042, by rfl⟩) (B 12085 (by norm_num) ⟨6042, by rfl⟩ (by norm_num))
theorem R16117 : Reach 16117 := rs (se 5 (by rfl) ⟨755, by rfl⟩) (B 1511 (by norm_num) ⟨755, by rfl⟩ (by norm_num))
theorem R16121 : Reach 16121 := rs (se 2 (by rfl) ⟨6045, by rfl⟩) (B 12091 (by norm_num) ⟨6045, by rfl⟩ (by norm_num))
theorem R16125 : Reach 16125 := rs (se 3 (by rfl) ⟨3023, by rfl⟩) (B 6047 (by norm_num) ⟨3023, by rfl⟩ (by norm_num))
theorem R16129 : Reach 16129 := rs (se 2 (by rfl) ⟨6048, by rfl⟩) (B 12097 (by norm_num) ⟨6048, by rfl⟩ (by norm_num))
theorem R16133 : Reach 16133 := rs (se 4 (by rfl) ⟨1512, by rfl⟩) (B 3025 (by norm_num) ⟨1512, by rfl⟩ (by norm_num))
theorem R16137 : Reach 16137 := rs (se 2 (by rfl) ⟨6051, by rfl⟩) (B 12103 (by norm_num) ⟨6051, by rfl⟩ (by norm_num))
theorem R16141 : Reach 16141 := rs (se 3 (by rfl) ⟨3026, by rfl⟩) (B 6053 (by norm_num) ⟨3026, by rfl⟩ (by norm_num))
theorem R16145 : Reach 16145 := rs (se 2 (by rfl) ⟨6054, by rfl⟩) (B 12109 (by norm_num) ⟨6054, by rfl⟩ (by norm_num))
theorem R16149 : Reach 16149 := rs (se 6 (by rfl) ⟨378, by rfl⟩) (B 757 (by norm_num) ⟨378, by rfl⟩ (by norm_num))
theorem R16153 : Reach 16153 := rs (se 2 (by rfl) ⟨6057, by rfl⟩) (B 12115 (by norm_num) ⟨6057, by rfl⟩ (by norm_num))
theorem R16157 : Reach 16157 := rs (se 3 (by rfl) ⟨3029, by rfl⟩) (B 6059 (by norm_num) ⟨3029, by rfl⟩ (by norm_num))
theorem R16161 : Reach 16161 := rs (se 2 (by rfl) ⟨6060, by rfl⟩) (B 12121 (by norm_num) ⟨6060, by rfl⟩ (by norm_num))
theorem R16165 : Reach 16165 := rs (se 4 (by rfl) ⟨1515, by rfl⟩) (B 3031 (by norm_num) ⟨1515, by rfl⟩ (by norm_num))
theorem R16169 : Reach 16169 := rs (se 2 (by rfl) ⟨6063, by rfl⟩) (B 12127 (by norm_num) ⟨6063, by rfl⟩ (by norm_num))
theorem R16173 : Reach 16173 := rs (se 3 (by rfl) ⟨3032, by rfl⟩) (B 6065 (by norm_num) ⟨3032, by rfl⟩ (by norm_num))
theorem R16177 : Reach 16177 := rs (se 2 (by rfl) ⟨6066, by rfl⟩) (B 12133 (by norm_num) ⟨6066, by rfl⟩ (by norm_num))
theorem R16181 : Reach 16181 := rs (se 5 (by rfl) ⟨758, by rfl⟩) (B 1517 (by norm_num) ⟨758, by rfl⟩ (by norm_num))
theorem R16185 : Reach 16185 := rs (se 2 (by rfl) ⟨6069, by rfl⟩) (B 12139 (by norm_num) ⟨6069, by rfl⟩ (by norm_num))
theorem R16189 : Reach 16189 := rs (se 3 (by rfl) ⟨3035, by rfl⟩) (B 6071 (by norm_num) ⟨3035, by rfl⟩ (by norm_num))
theorem R16193 : Reach 16193 := rs (se 2 (by rfl) ⟨6072, by rfl⟩) (B 12145 (by norm_num) ⟨6072, by rfl⟩ (by norm_num))
theorem R16197 : Reach 16197 := rs (se 4 (by rfl) ⟨1518, by rfl⟩) (B 3037 (by norm_num) ⟨1518, by rfl⟩ (by norm_num))
theorem R16201 : Reach 16201 := rs (se 2 (by rfl) ⟨6075, by rfl⟩) (B 12151 (by norm_num) ⟨6075, by rfl⟩ (by norm_num))
theorem R16205 : Reach 16205 := rs (se 3 (by rfl) ⟨3038, by rfl⟩) (B 6077 (by norm_num) ⟨3038, by rfl⟩ (by norm_num))
theorem R16209 : Reach 16209 := rs (se 2 (by rfl) ⟨6078, by rfl⟩) (B 12157 (by norm_num) ⟨6078, by rfl⟩ (by norm_num))
theorem R16213 : Reach 16213 := rs (se 9 (by rfl) ⟨47, by rfl⟩) (B 95 (by norm_num) ⟨47, by rfl⟩ (by norm_num))
theorem R16217 : Reach 16217 := rs (se 2 (by rfl) ⟨6081, by rfl⟩) (B 12163 (by norm_num) ⟨6081, by rfl⟩ (by norm_num))
theorem R16221 : Reach 16221 := rs (se 3 (by rfl) ⟨3041, by rfl⟩) (B 6083 (by norm_num) ⟨3041, by rfl⟩ (by norm_num))
theorem R16225 : Reach 16225 := rs (se 2 (by rfl) ⟨6084, by rfl⟩) (B 12169 (by norm_num) ⟨6084, by rfl⟩ (by norm_num))
theorem R16229 : Reach 16229 := rs (se 4 (by rfl) ⟨1521, by rfl⟩) (B 3043 (by norm_num) ⟨1521, by rfl⟩ (by norm_num))
theorem R16233 : Reach 16233 := rs (se 2 (by rfl) ⟨6087, by rfl⟩) (B 12175 (by norm_num) ⟨6087, by rfl⟩ (by norm_num))
theorem R16237 : Reach 16237 := rs (se 3 (by rfl) ⟨3044, by rfl⟩) (B 6089 (by norm_num) ⟨3044, by rfl⟩ (by norm_num))
theorem R16241 : Reach 16241 := rs (se 2 (by rfl) ⟨6090, by rfl⟩) (B 12181 (by norm_num) ⟨6090, by rfl⟩ (by norm_num))
theorem R16245 : Reach 16245 := rs (se 5 (by rfl) ⟨761, by rfl⟩) (B 1523 (by norm_num) ⟨761, by rfl⟩ (by norm_num))
theorem R16249 : Reach 16249 := rs (se 2 (by rfl) ⟨6093, by rfl⟩) (B 12187 (by norm_num) ⟨6093, by rfl⟩ (by norm_num))
theorem R16253 : Reach 16253 := rs (se 3 (by rfl) ⟨3047, by rfl⟩) (B 6095 (by norm_num) ⟨3047, by rfl⟩ (by norm_num))
theorem R16257 : Reach 16257 := rs (se 2 (by rfl) ⟨6096, by rfl⟩) (B 12193 (by norm_num) ⟨6096, by rfl⟩ (by norm_num))
theorem R16261 : Reach 16261 := rs (se 4 (by rfl) ⟨1524, by rfl⟩) (B 3049 (by norm_num) ⟨1524, by rfl⟩ (by norm_num))
theorem R16265 : Reach 16265 := rs (se 2 (by rfl) ⟨6099, by rfl⟩) (B 12199 (by norm_num) ⟨6099, by rfl⟩ (by norm_num))
theorem R16269 : Reach 16269 := rs (se 3 (by rfl) ⟨3050, by rfl⟩) (B 6101 (by norm_num) ⟨3050, by rfl⟩ (by norm_num))
theorem R16273 : Reach 16273 := rs (se 2 (by rfl) ⟨6102, by rfl⟩) (B 12205 (by norm_num) ⟨6102, by rfl⟩ (by norm_num))
theorem R16277 : Reach 16277 := rs (se 6 (by rfl) ⟨381, by rfl⟩) (B 763 (by norm_num) ⟨381, by rfl⟩ (by norm_num))
theorem R49045 : Reach 49045 := rs (se 6 (by rfl) ⟨1149, by rfl⟩) (B 2299 (by norm_num) ⟨1149, by rfl⟩ (by norm_num))
theorem R16281 : Reach 16281 := rs (se 2 (by rfl) ⟨6105, by rfl⟩) (B 12211 (by norm_num) ⟨6105, by rfl⟩ (by norm_num))
theorem R16285 : Reach 16285 := rs (se 3 (by rfl) ⟨3053, by rfl⟩) (B 6107 (by norm_num) ⟨3053, by rfl⟩ (by norm_num))
theorem R16289 : Reach 16289 := rs (se 2 (by rfl) ⟨6108, by rfl⟩) (B 12217 (by norm_num) ⟨6108, by rfl⟩ (by norm_num))
theorem R16293 : Reach 16293 := rs (se 4 (by rfl) ⟨1527, by rfl⟩) (B 3055 (by norm_num) ⟨1527, by rfl⟩ (by norm_num))
theorem R16297 : Reach 16297 := rs (se 2 (by rfl) ⟨6111, by rfl⟩) (B 12223 (by norm_num) ⟨6111, by rfl⟩ (by norm_num))
theorem R16301 : Reach 16301 := rs (se 3 (by rfl) ⟨3056, by rfl⟩) (B 6113 (by norm_num) ⟨3056, by rfl⟩ (by norm_num))
theorem R16305 : Reach 16305 := rs (se 2 (by rfl) ⟨6114, by rfl⟩) (B 12229 (by norm_num) ⟨6114, by rfl⟩ (by norm_num))
theorem R16309 : Reach 16309 := rs (se 5 (by rfl) ⟨764, by rfl⟩) (B 1529 (by norm_num) ⟨764, by rfl⟩ (by norm_num))
theorem R16313 : Reach 16313 := rs (se 2 (by rfl) ⟨6117, by rfl⟩) (B 12235 (by norm_num) ⟨6117, by rfl⟩ (by norm_num))
theorem R16317 : Reach 16317 := rs (se 3 (by rfl) ⟨3059, by rfl⟩) (B 6119 (by norm_num) ⟨3059, by rfl⟩ (by norm_num))
theorem R16321 : Reach 16321 := rs (se 2 (by rfl) ⟨6120, by rfl⟩) (B 12241 (by norm_num) ⟨6120, by rfl⟩ (by norm_num))
theorem R16325 : Reach 16325 := rs (se 4 (by rfl) ⟨1530, by rfl⟩) (B 3061 (by norm_num) ⟨1530, by rfl⟩ (by norm_num))
theorem R16329 : Reach 16329 := rs (se 2 (by rfl) ⟨6123, by rfl⟩) (B 12247 (by norm_num) ⟨6123, by rfl⟩ (by norm_num))
theorem R16333 : Reach 16333 := rs (se 3 (by rfl) ⟨3062, by rfl⟩) (B 6125 (by norm_num) ⟨3062, by rfl⟩ (by norm_num))
theorem R16337 : Reach 16337 := rs (se 2 (by rfl) ⟨6126, by rfl⟩) (B 12253 (by norm_num) ⟨6126, by rfl⟩ (by norm_num))
theorem R16341 : Reach 16341 := rs (se 7 (by rfl) ⟨191, by rfl⟩) (B 383 (by norm_num) ⟨191, by rfl⟩ (by norm_num))
theorem R16345 : Reach 16345 := rs (se 2 (by rfl) ⟨6129, by rfl⟩) (B 12259 (by norm_num) ⟨6129, by rfl⟩ (by norm_num))
theorem R16349 : Reach 16349 := rs (se 3 (by rfl) ⟨3065, by rfl⟩) (B 6131 (by norm_num) ⟨3065, by rfl⟩ (by norm_num))
theorem R16353 : Reach 16353 := rs (se 2 (by rfl) ⟨6132, by rfl⟩) (B 12265 (by norm_num) ⟨6132, by rfl⟩ (by norm_num))
theorem R16357 : Reach 16357 := rs (se 4 (by rfl) ⟨1533, by rfl⟩) (B 3067 (by norm_num) ⟨1533, by rfl⟩ (by norm_num))
theorem R16361 : Reach 16361 := rs (se 2 (by rfl) ⟨6135, by rfl⟩) (B 12271 (by norm_num) ⟨6135, by rfl⟩ (by norm_num))
theorem R16365 : Reach 16365 := rs (se 3 (by rfl) ⟨3068, by rfl⟩) (B 6137 (by norm_num) ⟨3068, by rfl⟩ (by norm_num))
theorem R16369 : Reach 16369 := rs (se 2 (by rfl) ⟨6138, by rfl⟩) (B 12277 (by norm_num) ⟨6138, by rfl⟩ (by norm_num))
theorem R16373 : Reach 16373 := rs (se 5 (by rfl) ⟨767, by rfl⟩) (B 1535 (by norm_num) ⟨767, by rfl⟩ (by norm_num))
theorem R16377 : Reach 16377 := rs (se 2 (by rfl) ⟨6141, by rfl⟩) (B 12283 (by norm_num) ⟨6141, by rfl⟩ (by norm_num))
theorem R16381 : Reach 16381 := rs (se 3 (by rfl) ⟨3071, by rfl⟩) (B 6143 (by norm_num) ⟨3071, by rfl⟩ (by norm_num))
theorem R16385 : Reach 16385 := rs (se 2 (by rfl) ⟨6144, by rfl⟩) (B 12289 (by norm_num) ⟨6144, by rfl⟩ (by norm_num))
theorem R49157 : Reach 49157 := rs (se 4 (by rfl) ⟨4608, by rfl⟩) (B 9217 (by norm_num) ⟨4608, by rfl⟩ (by norm_num))
theorem R16389 : Reach 16389 := rs (se 4 (by rfl) ⟨1536, by rfl⟩) (B 3073 (by norm_num) ⟨1536, by rfl⟩ (by norm_num))
theorem R16393 : Reach 16393 := rs (se 2 (by rfl) ⟨6147, by rfl⟩) (B 12295 (by norm_num) ⟨6147, by rfl⟩ (by norm_num))
theorem R16397 : Reach 16397 := rs (se 3 (by rfl) ⟨3074, by rfl⟩) (B 6149 (by norm_num) ⟨3074, by rfl⟩ (by norm_num))
theorem R16401 : Reach 16401 := rs (se 2 (by rfl) ⟨6150, by rfl⟩) (B 12301 (by norm_num) ⟨6150, by rfl⟩ (by norm_num))
theorem R16405 : Reach 16405 := rs (se 6 (by rfl) ⟨384, by rfl⟩) (B 769 (by norm_num) ⟨384, by rfl⟩ (by norm_num))
theorem R16409 : Reach 16409 := rs (se 2 (by rfl) ⟨6153, by rfl⟩) (B 12307 (by norm_num) ⟨6153, by rfl⟩ (by norm_num))
theorem R16413 : Reach 16413 := rs (se 3 (by rfl) ⟨3077, by rfl⟩) (B 6155 (by norm_num) ⟨3077, by rfl⟩ (by norm_num))
theorem R16417 : Reach 16417 := rs (se 2 (by rfl) ⟨6156, by rfl⟩) (B 12313 (by norm_num) ⟨6156, by rfl⟩ (by norm_num))
theorem R16421 : Reach 16421 := rs (se 4 (by rfl) ⟨1539, by rfl⟩) (B 3079 (by norm_num) ⟨1539, by rfl⟩ (by norm_num))
theorem R16425 : Reach 16425 := rs (se 2 (by rfl) ⟨6159, by rfl⟩) (B 12319 (by norm_num) ⟨6159, by rfl⟩ (by norm_num))
theorem R16429 : Reach 16429 := rs (se 3 (by rfl) ⟨3080, by rfl⟩) (B 6161 (by norm_num) ⟨3080, by rfl⟩ (by norm_num))
theorem R16433 : Reach 16433 := rs (se 2 (by rfl) ⟨6162, by rfl⟩) (B 12325 (by norm_num) ⟨6162, by rfl⟩ (by norm_num))
theorem R16437 : Reach 16437 := rs (se 5 (by rfl) ⟨770, by rfl⟩) (B 1541 (by norm_num) ⟨770, by rfl⟩ (by norm_num))
theorem R16441 : Reach 16441 := rs (se 2 (by rfl) ⟨6165, by rfl⟩) (B 12331 (by norm_num) ⟨6165, by rfl⟩ (by norm_num))
theorem R16445 : Reach 16445 := rs (se 3 (by rfl) ⟨3083, by rfl⟩) (B 6167 (by norm_num) ⟨3083, by rfl⟩ (by norm_num))
theorem R16449 : Reach 16449 := rs (se 2 (by rfl) ⟨6168, by rfl⟩) (B 12337 (by norm_num) ⟨6168, by rfl⟩ (by norm_num))
theorem R16453 : Reach 16453 := rs (se 4 (by rfl) ⟨1542, by rfl⟩) (B 3085 (by norm_num) ⟨1542, by rfl⟩ (by norm_num))
theorem R16457 : Reach 16457 := rs (se 2 (by rfl) ⟨6171, by rfl⟩) (B 12343 (by norm_num) ⟨6171, by rfl⟩ (by norm_num))
theorem R16461 : Reach 16461 := rs (se 3 (by rfl) ⟨3086, by rfl⟩) (B 6173 (by norm_num) ⟨3086, by rfl⟩ (by norm_num))
theorem R16465 : Reach 16465 := rs (se 2 (by rfl) ⟨6174, by rfl⟩) (B 12349 (by norm_num) ⟨6174, by rfl⟩ (by norm_num))
theorem R16469 : Reach 16469 := rs (se 8 (by rfl) ⟨96, by rfl⟩) (B 193 (by norm_num) ⟨96, by rfl⟩ (by norm_num))
theorem R16473 : Reach 16473 := rs (se 2 (by rfl) ⟨6177, by rfl⟩) (B 12355 (by norm_num) ⟨6177, by rfl⟩ (by norm_num))
theorem R16477 : Reach 16477 := rs (se 3 (by rfl) ⟨3089, by rfl⟩) (B 6179 (by norm_num) ⟨3089, by rfl⟩ (by norm_num))
theorem R16481 : Reach 16481 := rs (se 2 (by rfl) ⟨6180, by rfl⟩) (B 12361 (by norm_num) ⟨6180, by rfl⟩ (by norm_num))
theorem R16485 : Reach 16485 := rs (se 4 (by rfl) ⟨1545, by rfl⟩) (B 3091 (by norm_num) ⟨1545, by rfl⟩ (by norm_num))
theorem R16489 : Reach 16489 := rs (se 2 (by rfl) ⟨6183, by rfl⟩) (B 12367 (by norm_num) ⟨6183, by rfl⟩ (by norm_num))
theorem R16493 : Reach 16493 := rs (se 3 (by rfl) ⟨3092, by rfl⟩) (B 6185 (by norm_num) ⟨3092, by rfl⟩ (by norm_num))
theorem R16497 : Reach 16497 := rs (se 2 (by rfl) ⟨6186, by rfl⟩) (B 12373 (by norm_num) ⟨6186, by rfl⟩ (by norm_num))
theorem R16501 : Reach 16501 := rs (se 5 (by rfl) ⟨773, by rfl⟩) (B 1547 (by norm_num) ⟨773, by rfl⟩ (by norm_num))
theorem R16505 : Reach 16505 := rs (se 2 (by rfl) ⟨6189, by rfl⟩) (B 12379 (by norm_num) ⟨6189, by rfl⟩ (by norm_num))
theorem R16509 : Reach 16509 := rs (se 3 (by rfl) ⟨3095, by rfl⟩) (B 6191 (by norm_num) ⟨3095, by rfl⟩ (by norm_num))
theorem R16513 : Reach 16513 := rs (se 2 (by rfl) ⟨6192, by rfl⟩) (B 12385 (by norm_num) ⟨6192, by rfl⟩ (by norm_num))
theorem R16517 : Reach 16517 := rs (se 4 (by rfl) ⟨1548, by rfl⟩) (B 3097 (by norm_num) ⟨1548, by rfl⟩ (by norm_num))
theorem R16521 : Reach 16521 := rs (se 2 (by rfl) ⟨6195, by rfl⟩) (B 12391 (by norm_num) ⟨6195, by rfl⟩ (by norm_num))
theorem R16525 : Reach 16525 := rs (se 3 (by rfl) ⟨3098, by rfl⟩) (B 6197 (by norm_num) ⟨3098, by rfl⟩ (by norm_num))
theorem R16529 : Reach 16529 := rs (se 2 (by rfl) ⟨6198, by rfl⟩) (B 12397 (by norm_num) ⟨6198, by rfl⟩ (by norm_num))
theorem R49301 : Reach 49301 := rs (se 6 (by rfl) ⟨1155, by rfl⟩) (B 2311 (by norm_num) ⟨1155, by rfl⟩ (by norm_num))
theorem R16533 : Reach 16533 := rs (se 6 (by rfl) ⟨387, by rfl⟩) (B 775 (by norm_num) ⟨387, by rfl⟩ (by norm_num))
theorem R16537 : Reach 16537 := rs (se 2 (by rfl) ⟨6201, by rfl⟩) (B 12403 (by norm_num) ⟨6201, by rfl⟩ (by norm_num))
theorem R16541 : Reach 16541 := rs (se 3 (by rfl) ⟨3101, by rfl⟩) (B 6203 (by norm_num) ⟨3101, by rfl⟩ (by norm_num))
theorem R16545 : Reach 16545 := rs (se 2 (by rfl) ⟨6204, by rfl⟩) (B 12409 (by norm_num) ⟨6204, by rfl⟩ (by norm_num))
theorem R16549 : Reach 16549 := rs (se 4 (by rfl) ⟨1551, by rfl⟩) (B 3103 (by norm_num) ⟨1551, by rfl⟩ (by norm_num))
theorem R16553 : Reach 16553 := rs (se 2 (by rfl) ⟨6207, by rfl⟩) (B 12415 (by norm_num) ⟨6207, by rfl⟩ (by norm_num))
theorem R16557 : Reach 16557 := rs (se 3 (by rfl) ⟨3104, by rfl⟩) (B 6209 (by norm_num) ⟨3104, by rfl⟩ (by norm_num))
theorem R16561 : Reach 16561 := rs (se 2 (by rfl) ⟨6210, by rfl⟩) (B 12421 (by norm_num) ⟨6210, by rfl⟩ (by norm_num))
theorem R16565 : Reach 16565 := rs (se 5 (by rfl) ⟨776, by rfl⟩) (B 1553 (by norm_num) ⟨776, by rfl⟩ (by norm_num))
theorem R16569 : Reach 16569 := rs (se 2 (by rfl) ⟨6213, by rfl⟩) (B 12427 (by norm_num) ⟨6213, by rfl⟩ (by norm_num))
theorem R16573 : Reach 16573 := rs (se 3 (by rfl) ⟨3107, by rfl⟩) (B 6215 (by norm_num) ⟨3107, by rfl⟩ (by norm_num))
theorem R16577 : Reach 16577 := rs (se 2 (by rfl) ⟨6216, by rfl⟩) (B 12433 (by norm_num) ⟨6216, by rfl⟩ (by norm_num))
theorem R16581 : Reach 16581 := rs (se 4 (by rfl) ⟨1554, by rfl⟩) (B 3109 (by norm_num) ⟨1554, by rfl⟩ (by norm_num))
theorem R49349 : Reach 49349 := rs (se 4 (by rfl) ⟨4626, by rfl⟩) (B 9253 (by norm_num) ⟨4626, by rfl⟩ (by norm_num))
theorem R16585 : Reach 16585 := rs (se 2 (by rfl) ⟨6219, by rfl⟩) (B 12439 (by norm_num) ⟨6219, by rfl⟩ (by norm_num))
theorem R16589 : Reach 16589 := rs (se 3 (by rfl) ⟨3110, by rfl⟩) (B 6221 (by norm_num) ⟨3110, by rfl⟩ (by norm_num))
theorem R16593 : Reach 16593 := rs (se 2 (by rfl) ⟨6222, by rfl⟩) (B 12445 (by norm_num) ⟨6222, by rfl⟩ (by norm_num))
theorem R82133 : Reach 82133 := rs (se 7 (by rfl) ⟨962, by rfl⟩) (B 1925 (by norm_num) ⟨962, by rfl⟩ (by norm_num))
theorem R16597 : Reach 16597 := rs (se 7 (by rfl) ⟨194, by rfl⟩) (B 389 (by norm_num) ⟨194, by rfl⟩ (by norm_num))
theorem R16601 : Reach 16601 := rs (se 2 (by rfl) ⟨6225, by rfl⟩) (B 12451 (by norm_num) ⟨6225, by rfl⟩ (by norm_num))
theorem R16605 : Reach 16605 := rs (se 3 (by rfl) ⟨3113, by rfl⟩) (B 6227 (by norm_num) ⟨3113, by rfl⟩ (by norm_num))
theorem R16609 : Reach 16609 := rs (se 2 (by rfl) ⟨6228, by rfl⟩) (B 12457 (by norm_num) ⟨6228, by rfl⟩ (by norm_num))
theorem R16613 : Reach 16613 := rs (se 4 (by rfl) ⟨1557, by rfl⟩) (B 3115 (by norm_num) ⟨1557, by rfl⟩ (by norm_num))
theorem R16617 : Reach 16617 := rs (se 2 (by rfl) ⟨6231, by rfl⟩) (B 12463 (by norm_num) ⟨6231, by rfl⟩ (by norm_num))
theorem R16621 : Reach 16621 := rs (se 3 (by rfl) ⟨3116, by rfl⟩) (B 6233 (by norm_num) ⟨3116, by rfl⟩ (by norm_num))
theorem R16625 : Reach 16625 := rs (se 2 (by rfl) ⟨6234, by rfl⟩) (B 12469 (by norm_num) ⟨6234, by rfl⟩ (by norm_num))
theorem R16629 : Reach 16629 := rs (se 5 (by rfl) ⟨779, by rfl⟩) (B 1559 (by norm_num) ⟨779, by rfl⟩ (by norm_num))
theorem R16633 : Reach 16633 := rs (se 2 (by rfl) ⟨6237, by rfl⟩) (B 12475 (by norm_num) ⟨6237, by rfl⟩ (by norm_num))
theorem R16637 : Reach 16637 := rs (se 3 (by rfl) ⟨3119, by rfl⟩) (B 6239 (by norm_num) ⟨3119, by rfl⟩ (by norm_num))
theorem R16641 : Reach 16641 := rs (se 2 (by rfl) ⟨6240, by rfl⟩) (B 12481 (by norm_num) ⟨6240, by rfl⟩ (by norm_num))
theorem R16645 : Reach 16645 := rs (se 4 (by rfl) ⟨1560, by rfl⟩) (B 3121 (by norm_num) ⟨1560, by rfl⟩ (by norm_num))
theorem R16649 : Reach 16649 := rs (se 2 (by rfl) ⟨6243, by rfl⟩) (B 12487 (by norm_num) ⟨6243, by rfl⟩ (by norm_num))
theorem R16653 : Reach 16653 := rs (se 3 (by rfl) ⟨3122, by rfl⟩) (B 6245 (by norm_num) ⟨3122, by rfl⟩ (by norm_num))
theorem R16657 : Reach 16657 := rs (se 2 (by rfl) ⟨6246, by rfl⟩) (B 12493 (by norm_num) ⟨6246, by rfl⟩ (by norm_num))
theorem R16661 : Reach 16661 := rs (se 6 (by rfl) ⟨390, by rfl⟩) (B 781 (by norm_num) ⟨390, by rfl⟩ (by norm_num))
theorem R246037 : Reach 246037 := rs (se 6 (by rfl) ⟨5766, by rfl⟩) (B 11533 (by norm_num) ⟨5766, by rfl⟩ (by norm_num))
theorem R16665 : Reach 16665 := rs (se 2 (by rfl) ⟨6249, by rfl⟩) (B 12499 (by norm_num) ⟨6249, by rfl⟩ (by norm_num))
theorem R16669 : Reach 16669 := rs (se 3 (by rfl) ⟨3125, by rfl⟩) (B 6251 (by norm_num) ⟨3125, by rfl⟩ (by norm_num))
theorem R16673 : Reach 16673 := rs (se 2 (by rfl) ⟨6252, by rfl⟩) (B 12505 (by norm_num) ⟨6252, by rfl⟩ (by norm_num))
theorem R16677 : Reach 16677 := rs (se 4 (by rfl) ⟨1563, by rfl⟩) (B 3127 (by norm_num) ⟨1563, by rfl⟩ (by norm_num))
theorem R16681 : Reach 16681 := rs (se 2 (by rfl) ⟨6255, by rfl⟩) (B 12511 (by norm_num) ⟨6255, by rfl⟩ (by norm_num))
theorem R16685 : Reach 16685 := rs (se 3 (by rfl) ⟨3128, by rfl⟩) (B 6257 (by norm_num) ⟨3128, by rfl⟩ (by norm_num))
theorem R16689 : Reach 16689 := rs (se 2 (by rfl) ⟨6258, by rfl⟩) (B 12517 (by norm_num) ⟨6258, by rfl⟩ (by norm_num))
theorem R16693 : Reach 16693 := rs (se 5 (by rfl) ⟨782, by rfl⟩) (B 1565 (by norm_num) ⟨782, by rfl⟩ (by norm_num))
theorem R16697 : Reach 16697 := rs (se 2 (by rfl) ⟨6261, by rfl⟩) (B 12523 (by norm_num) ⟨6261, by rfl⟩ (by norm_num))
theorem R16701 : Reach 16701 := rs (se 3 (by rfl) ⟨3131, by rfl⟩) (B 6263 (by norm_num) ⟨3131, by rfl⟩ (by norm_num))
theorem R16705 : Reach 16705 := rs (se 2 (by rfl) ⟨6264, by rfl⟩) (B 12529 (by norm_num) ⟨6264, by rfl⟩ (by norm_num))
theorem R16709 : Reach 16709 := rs (se 4 (by rfl) ⟨1566, by rfl⟩) (B 3133 (by norm_num) ⟨1566, by rfl⟩ (by norm_num))
theorem R16713 : Reach 16713 := rs (se 2 (by rfl) ⟨6267, by rfl⟩) (B 12535 (by norm_num) ⟨6267, by rfl⟩ (by norm_num))
theorem R16717 : Reach 16717 := rs (se 3 (by rfl) ⟨3134, by rfl⟩) (B 6269 (by norm_num) ⟨3134, by rfl⟩ (by norm_num))
theorem R16721 : Reach 16721 := rs (se 2 (by rfl) ⟨6270, by rfl⟩) (B 12541 (by norm_num) ⟨6270, by rfl⟩ (by norm_num))
theorem R16725 : Reach 16725 := rs (se 10 (by rfl) ⟨24, by rfl⟩) (B 49 (by norm_num) ⟨24, by rfl⟩ (by norm_num))
theorem R16729 : Reach 16729 := rs (se 2 (by rfl) ⟨6273, by rfl⟩) (B 12547 (by norm_num) ⟨6273, by rfl⟩ (by norm_num))
theorem R16733 : Reach 16733 := rs (se 3 (by rfl) ⟨3137, by rfl⟩) (B 6275 (by norm_num) ⟨3137, by rfl⟩ (by norm_num))
theorem R16737 : Reach 16737 := rs (se 2 (by rfl) ⟨6276, by rfl⟩) (B 12553 (by norm_num) ⟨6276, by rfl⟩ (by norm_num))
theorem R16741 : Reach 16741 := rs (se 4 (by rfl) ⟨1569, by rfl⟩) (B 3139 (by norm_num) ⟨1569, by rfl⟩ (by norm_num))
theorem R16745 : Reach 16745 := rs (se 2 (by rfl) ⟨6279, by rfl⟩) (B 12559 (by norm_num) ⟨6279, by rfl⟩ (by norm_num))
theorem R16749 : Reach 16749 := rs (se 3 (by rfl) ⟨3140, by rfl⟩) (B 6281 (by norm_num) ⟨3140, by rfl⟩ (by norm_num))
theorem R16753 : Reach 16753 := rs (se 2 (by rfl) ⟨6282, by rfl⟩) (B 12565 (by norm_num) ⟨6282, by rfl⟩ (by norm_num))
theorem R16757 : Reach 16757 := rs (se 5 (by rfl) ⟨785, by rfl⟩) (B 1571 (by norm_num) ⟨785, by rfl⟩ (by norm_num))
theorem R16761 : Reach 16761 := rs (se 2 (by rfl) ⟨6285, by rfl⟩) (B 12571 (by norm_num) ⟨6285, by rfl⟩ (by norm_num))
theorem R16765 : Reach 16765 := rs (se 3 (by rfl) ⟨3143, by rfl⟩) (B 6287 (by norm_num) ⟨3143, by rfl⟩ (by norm_num))
theorem R16769 : Reach 16769 := rs (se 2 (by rfl) ⟨6288, by rfl⟩) (B 12577 (by norm_num) ⟨6288, by rfl⟩ (by norm_num))
theorem R16773 : Reach 16773 := rs (se 4 (by rfl) ⟨1572, by rfl⟩) (B 3145 (by norm_num) ⟨1572, by rfl⟩ (by norm_num))
theorem R16777 : Reach 16777 := rs (se 2 (by rfl) ⟨6291, by rfl⟩) (B 12583 (by norm_num) ⟨6291, by rfl⟩ (by norm_num))
theorem R16781 : Reach 16781 := rs (se 3 (by rfl) ⟨3146, by rfl⟩) (B 6293 (by norm_num) ⟨3146, by rfl⟩ (by norm_num))
theorem R16785 : Reach 16785 := rs (se 2 (by rfl) ⟨6294, by rfl⟩) (B 12589 (by norm_num) ⟨6294, by rfl⟩ (by norm_num))
theorem R16789 : Reach 16789 := rs (se 6 (by rfl) ⟨393, by rfl⟩) (B 787 (by norm_num) ⟨393, by rfl⟩ (by norm_num))
theorem R82325 : Reach 82325 := rs (se 6 (by rfl) ⟨1929, by rfl⟩) (B 3859 (by norm_num) ⟨1929, by rfl⟩ (by norm_num))
theorem R16793 : Reach 16793 := rs (se 2 (by rfl) ⟨6297, by rfl⟩) (B 12595 (by norm_num) ⟨6297, by rfl⟩ (by norm_num))
theorem R16797 : Reach 16797 := rs (se 3 (by rfl) ⟨3149, by rfl⟩) (B 6299 (by norm_num) ⟨3149, by rfl⟩ (by norm_num))
theorem R16801 : Reach 16801 := rs (se 2 (by rfl) ⟨6300, by rfl⟩) (B 12601 (by norm_num) ⟨6300, by rfl⟩ (by norm_num))
theorem R16805 : Reach 16805 := rs (se 4 (by rfl) ⟨1575, by rfl⟩) (B 3151 (by norm_num) ⟨1575, by rfl⟩ (by norm_num))
theorem R16809 : Reach 16809 := rs (se 2 (by rfl) ⟨6303, by rfl⟩) (B 12607 (by norm_num) ⟨6303, by rfl⟩ (by norm_num))
theorem R16813 : Reach 16813 := rs (se 3 (by rfl) ⟨3152, by rfl⟩) (B 6305 (by norm_num) ⟨3152, by rfl⟩ (by norm_num))
theorem R16817 : Reach 16817 := rs (se 2 (by rfl) ⟨6306, by rfl⟩) (B 12613 (by norm_num) ⟨6306, by rfl⟩ (by norm_num))
theorem R16821 : Reach 16821 := rs (se 5 (by rfl) ⟨788, by rfl⟩) (B 1577 (by norm_num) ⟨788, by rfl⟩ (by norm_num))
theorem R16825 : Reach 16825 := rs (se 2 (by rfl) ⟨6309, by rfl⟩) (B 12619 (by norm_num) ⟨6309, by rfl⟩ (by norm_num))
theorem R16829 : Reach 16829 := rs (se 3 (by rfl) ⟨3155, by rfl⟩) (B 6311 (by norm_num) ⟨3155, by rfl⟩ (by norm_num))
theorem R16833 : Reach 16833 := rs (se 2 (by rfl) ⟨6312, by rfl⟩) (B 12625 (by norm_num) ⟨6312, by rfl⟩ (by norm_num))
theorem R16837 : Reach 16837 := rs (se 4 (by rfl) ⟨1578, by rfl⟩) (B 3157 (by norm_num) ⟨1578, by rfl⟩ (by norm_num))
theorem R16841 : Reach 16841 := rs (se 2 (by rfl) ⟨6315, by rfl⟩) (B 12631 (by norm_num) ⟨6315, by rfl⟩ (by norm_num))
theorem R16845 : Reach 16845 := rs (se 3 (by rfl) ⟨3158, by rfl⟩) (B 6317 (by norm_num) ⟨3158, by rfl⟩ (by norm_num))
theorem R16849 : Reach 16849 := rs (se 2 (by rfl) ⟨6318, by rfl⟩) (B 12637 (by norm_num) ⟨6318, by rfl⟩ (by norm_num))
theorem R16853 : Reach 16853 := rs (se 7 (by rfl) ⟨197, by rfl⟩) (B 395 (by norm_num) ⟨197, by rfl⟩ (by norm_num))
theorem R16857 : Reach 16857 := rs (se 2 (by rfl) ⟨6321, by rfl⟩) (B 12643 (by norm_num) ⟨6321, by rfl⟩ (by norm_num))
theorem R16861 : Reach 16861 := rs (se 3 (by rfl) ⟨3161, by rfl⟩) (B 6323 (by norm_num) ⟨3161, by rfl⟩ (by norm_num))
theorem R16865 : Reach 16865 := rs (se 2 (by rfl) ⟨6324, by rfl⟩) (B 12649 (by norm_num) ⟨6324, by rfl⟩ (by norm_num))
theorem R16869 : Reach 16869 := rs (se 4 (by rfl) ⟨1581, by rfl⟩) (B 3163 (by norm_num) ⟨1581, by rfl⟩ (by norm_num))
theorem R16873 : Reach 16873 := rs (se 2 (by rfl) ⟨6327, by rfl⟩) (B 12655 (by norm_num) ⟨6327, by rfl⟩ (by norm_num))
theorem R16877 : Reach 16877 := rs (se 3 (by rfl) ⟨3164, by rfl⟩) (B 6329 (by norm_num) ⟨3164, by rfl⟩ (by norm_num))
theorem R16881 : Reach 16881 := rs (se 2 (by rfl) ⟨6330, by rfl⟩) (B 12661 (by norm_num) ⟨6330, by rfl⟩ (by norm_num))
theorem R16885 : Reach 16885 := rs (se 5 (by rfl) ⟨791, by rfl⟩) (B 1583 (by norm_num) ⟨791, by rfl⟩ (by norm_num))
theorem R16889 : Reach 16889 := rs (se 2 (by rfl) ⟨6333, by rfl⟩) (B 12667 (by norm_num) ⟨6333, by rfl⟩ (by norm_num))
theorem R16893 : Reach 16893 := rs (se 3 (by rfl) ⟨3167, by rfl⟩) (B 6335 (by norm_num) ⟨3167, by rfl⟩ (by norm_num))
theorem R16897 : Reach 16897 := rs (se 2 (by rfl) ⟨6336, by rfl⟩) (B 12673 (by norm_num) ⟨6336, by rfl⟩ (by norm_num))
theorem R16901 : Reach 16901 := rs (se 4 (by rfl) ⟨1584, by rfl⟩) (B 3169 (by norm_num) ⟨1584, by rfl⟩ (by norm_num))
theorem R16905 : Reach 16905 := rs (se 2 (by rfl) ⟨6339, by rfl⟩) (B 12679 (by norm_num) ⟨6339, by rfl⟩ (by norm_num))
theorem R16909 : Reach 16909 := rs (se 3 (by rfl) ⟨3170, by rfl⟩) (B 6341 (by norm_num) ⟨3170, by rfl⟩ (by norm_num))
theorem R16913 : Reach 16913 := rs (se 2 (by rfl) ⟨6342, by rfl⟩) (B 12685 (by norm_num) ⟨6342, by rfl⟩ (by norm_num))
theorem R16917 : Reach 16917 := rs (se 6 (by rfl) ⟨396, by rfl⟩) (B 793 (by norm_num) ⟨396, by rfl⟩ (by norm_num))
theorem R16921 : Reach 16921 := rs (se 2 (by rfl) ⟨6345, by rfl⟩) (B 12691 (by norm_num) ⟨6345, by rfl⟩ (by norm_num))
theorem R16925 : Reach 16925 := rs (se 3 (by rfl) ⟨3173, by rfl⟩) (B 6347 (by norm_num) ⟨3173, by rfl⟩ (by norm_num))
theorem R16929 : Reach 16929 := rs (se 2 (by rfl) ⟨6348, by rfl⟩) (B 12697 (by norm_num) ⟨6348, by rfl⟩ (by norm_num))
theorem R16933 : Reach 16933 := rs (se 4 (by rfl) ⟨1587, by rfl⟩) (B 3175 (by norm_num) ⟨1587, by rfl⟩ (by norm_num))
theorem R16937 : Reach 16937 := rs (se 2 (by rfl) ⟨6351, by rfl⟩) (B 12703 (by norm_num) ⟨6351, by rfl⟩ (by norm_num))
theorem R16941 : Reach 16941 := rs (se 3 (by rfl) ⟨3176, by rfl⟩) (B 6353 (by norm_num) ⟨3176, by rfl⟩ (by norm_num))
theorem R16945 : Reach 16945 := rs (se 2 (by rfl) ⟨6354, by rfl⟩) (B 12709 (by norm_num) ⟨6354, by rfl⟩ (by norm_num))
theorem R16949 : Reach 16949 := rs (se 5 (by rfl) ⟨794, by rfl⟩) (B 1589 (by norm_num) ⟨794, by rfl⟩ (by norm_num))
theorem R16953 : Reach 16953 := rs (se 2 (by rfl) ⟨6357, by rfl⟩) (B 12715 (by norm_num) ⟨6357, by rfl⟩ (by norm_num))
theorem R16957 : Reach 16957 := rs (se 3 (by rfl) ⟨3179, by rfl⟩) (B 6359 (by norm_num) ⟨3179, by rfl⟩ (by norm_num))
theorem R16961 : Reach 16961 := rs (se 2 (by rfl) ⟨6360, by rfl⟩) (B 12721 (by norm_num) ⟨6360, by rfl⟩ (by norm_num))
theorem R49733 : Reach 49733 := rs (se 4 (by rfl) ⟨4662, by rfl⟩) (B 9325 (by norm_num) ⟨4662, by rfl⟩ (by norm_num))
theorem R16965 : Reach 16965 := rs (se 4 (by rfl) ⟨1590, by rfl⟩) (B 3181 (by norm_num) ⟨1590, by rfl⟩ (by norm_num))
theorem R16969 : Reach 16969 := rs (se 2 (by rfl) ⟨6363, by rfl⟩) (B 12727 (by norm_num) ⟨6363, by rfl⟩ (by norm_num))
theorem R16973 : Reach 16973 := rs (se 3 (by rfl) ⟨3182, by rfl⟩) (B 6365 (by norm_num) ⟨3182, by rfl⟩ (by norm_num))
theorem R16977 : Reach 16977 := rs (se 2 (by rfl) ⟨6366, by rfl⟩) (B 12733 (by norm_num) ⟨6366, by rfl⟩ (by norm_num))
theorem R16981 : Reach 16981 := rs (se 8 (by rfl) ⟨99, by rfl⟩) (B 199 (by norm_num) ⟨99, by rfl⟩ (by norm_num))
theorem R16985 : Reach 16985 := rs (se 2 (by rfl) ⟨6369, by rfl⟩) (B 12739 (by norm_num) ⟨6369, by rfl⟩ (by norm_num))
theorem R16989 : Reach 16989 := rs (se 3 (by rfl) ⟨3185, by rfl⟩) (B 6371 (by norm_num) ⟨3185, by rfl⟩ (by norm_num))
theorem R16993 : Reach 16993 := rs (se 2 (by rfl) ⟨6372, by rfl⟩) (B 12745 (by norm_num) ⟨6372, by rfl⟩ (by norm_num))
theorem R16997 : Reach 16997 := rs (se 4 (by rfl) ⟨1593, by rfl⟩) (B 3187 (by norm_num) ⟨1593, by rfl⟩ (by norm_num))
theorem R17001 : Reach 17001 := rs (se 2 (by rfl) ⟨6375, by rfl⟩) (B 12751 (by norm_num) ⟨6375, by rfl⟩ (by norm_num))
theorem R17005 : Reach 17005 := rs (se 3 (by rfl) ⟨3188, by rfl⟩) (B 6377 (by norm_num) ⟨3188, by rfl⟩ (by norm_num))
theorem R17009 : Reach 17009 := rs (se 2 (by rfl) ⟨6378, by rfl⟩) (B 12757 (by norm_num) ⟨6378, by rfl⟩ (by norm_num))
theorem R17013 : Reach 17013 := rs (se 5 (by rfl) ⟨797, by rfl⟩) (B 1595 (by norm_num) ⟨797, by rfl⟩ (by norm_num))
theorem R17017 : Reach 17017 := rs (se 2 (by rfl) ⟨6381, by rfl⟩) (B 12763 (by norm_num) ⟨6381, by rfl⟩ (by norm_num))
theorem R17021 : Reach 17021 := rs (se 3 (by rfl) ⟨3191, by rfl⟩) (B 6383 (by norm_num) ⟨3191, by rfl⟩ (by norm_num))
theorem R17025 : Reach 17025 := rs (se 2 (by rfl) ⟨6384, by rfl⟩) (B 12769 (by norm_num) ⟨6384, by rfl⟩ (by norm_num))
theorem R17029 : Reach 17029 := rs (se 4 (by rfl) ⟨1596, by rfl⟩) (B 3193 (by norm_num) ⟨1596, by rfl⟩ (by norm_num))
theorem R17033 : Reach 17033 := rs (se 2 (by rfl) ⟨6387, by rfl⟩) (B 12775 (by norm_num) ⟨6387, by rfl⟩ (by norm_num))
theorem R17037 : Reach 17037 := rs (se 3 (by rfl) ⟨3194, by rfl⟩) (B 6389 (by norm_num) ⟨3194, by rfl⟩ (by norm_num))
theorem R17041 : Reach 17041 := rs (se 2 (by rfl) ⟨6390, by rfl⟩) (B 12781 (by norm_num) ⟨6390, by rfl⟩ (by norm_num))
theorem R17045 : Reach 17045 := rs (se 6 (by rfl) ⟨399, by rfl⟩) (B 799 (by norm_num) ⟨399, by rfl⟩ (by norm_num))
theorem R17049 : Reach 17049 := rs (se 2 (by rfl) ⟨6393, by rfl⟩) (B 12787 (by norm_num) ⟨6393, by rfl⟩ (by norm_num))
theorem R17053 : Reach 17053 := rs (se 3 (by rfl) ⟨3197, by rfl⟩) (B 6395 (by norm_num) ⟨3197, by rfl⟩ (by norm_num))
theorem R17057 : Reach 17057 := rs (se 2 (by rfl) ⟨6396, by rfl⟩) (B 12793 (by norm_num) ⟨6396, by rfl⟩ (by norm_num))
theorem R17061 : Reach 17061 := rs (se 4 (by rfl) ⟨1599, by rfl⟩) (B 3199 (by norm_num) ⟨1599, by rfl⟩ (by norm_num))
theorem R17065 : Reach 17065 := rs (se 2 (by rfl) ⟨6399, by rfl⟩) (B 12799 (by norm_num) ⟨6399, by rfl⟩ (by norm_num))
theorem R17069 : Reach 17069 := rs (se 3 (by rfl) ⟨3200, by rfl⟩) (B 6401 (by norm_num) ⟨3200, by rfl⟩ (by norm_num))
theorem R17073 : Reach 17073 := rs (se 2 (by rfl) ⟨6402, by rfl⟩) (B 12805 (by norm_num) ⟨6402, by rfl⟩ (by norm_num))
theorem R17077 : Reach 17077 := rs (se 5 (by rfl) ⟨800, by rfl⟩) (B 1601 (by norm_num) ⟨800, by rfl⟩ (by norm_num))
theorem R17081 : Reach 17081 := rs (se 2 (by rfl) ⟨6405, by rfl⟩) (B 12811 (by norm_num) ⟨6405, by rfl⟩ (by norm_num))
theorem R17085 : Reach 17085 := rs (se 3 (by rfl) ⟨3203, by rfl⟩) (B 6407 (by norm_num) ⟨3203, by rfl⟩ (by norm_num))
theorem R17089 : Reach 17089 := rs (se 2 (by rfl) ⟨6408, by rfl⟩) (B 12817 (by norm_num) ⟨6408, by rfl⟩ (by norm_num))
theorem R17093 : Reach 17093 := rs (se 4 (by rfl) ⟨1602, by rfl⟩) (B 3205 (by norm_num) ⟨1602, by rfl⟩ (by norm_num))
theorem R17097 : Reach 17097 := rs (se 2 (by rfl) ⟨6411, by rfl⟩) (B 12823 (by norm_num) ⟨6411, by rfl⟩ (by norm_num))
theorem R17101 : Reach 17101 := rs (se 3 (by rfl) ⟨3206, by rfl⟩) (B 6413 (by norm_num) ⟨3206, by rfl⟩ (by norm_num))
theorem R17109 : Reach 17109 := rs (se 7 (by rfl) ⟨200, by rfl⟩) (B 401 (by norm_num) ⟨200, by rfl⟩ (by norm_num))
theorem R17117 : Reach 17117 := rs (se 3 (by rfl) ⟨3209, by rfl⟩) (B 6419 (by norm_num) ⟨3209, by rfl⟩ (by norm_num))
theorem R17125 : Reach 17125 := rs (se 4 (by rfl) ⟨1605, by rfl⟩) (B 3211 (by norm_num) ⟨1605, by rfl⟩ (by norm_num))
theorem R17133 : Reach 17133 := rs (se 3 (by rfl) ⟨3212, by rfl⟩) (B 6425 (by norm_num) ⟨3212, by rfl⟩ (by norm_num))
theorem R17141 : Reach 17141 := rs (se 5 (by rfl) ⟨803, by rfl⟩) (B 1607 (by norm_num) ⟨803, by rfl⟩ (by norm_num))
theorem R17149 : Reach 17149 := rs (se 3 (by rfl) ⟨3215, by rfl⟩) (B 6431 (by norm_num) ⟨3215, by rfl⟩ (by norm_num))
theorem R17157 : Reach 17157 := rs (se 4 (by rfl) ⟨1608, by rfl⟩) (B 3217 (by norm_num) ⟨1608, by rfl⟩ (by norm_num))
theorem R17165 : Reach 17165 := rs (se 3 (by rfl) ⟨3218, by rfl⟩) (B 6437 (by norm_num) ⟨3218, by rfl⟩ (by norm_num))
theorem R17173 : Reach 17173 := rs (se 6 (by rfl) ⟨402, by rfl⟩) (B 805 (by norm_num) ⟨402, by rfl⟩ (by norm_num))
theorem R17181 : Reach 17181 := rs (se 3 (by rfl) ⟨3221, by rfl⟩) (B 6443 (by norm_num) ⟨3221, by rfl⟩ (by norm_num))
theorem R17189 : Reach 17189 := rs (se 4 (by rfl) ⟨1611, by rfl⟩) (B 3223 (by norm_num) ⟨1611, by rfl⟩ (by norm_num))
theorem R17197 : Reach 17197 := rs (se 3 (by rfl) ⟨3224, by rfl⟩) (B 6449 (by norm_num) ⟨3224, by rfl⟩ (by norm_num))
theorem R82741 : Reach 82741 := rs (se 5 (by rfl) ⟨3878, by rfl⟩) (B 7757 (by norm_num) ⟨3878, by rfl⟩ (by norm_num))
theorem R17205 : Reach 17205 := rs (se 5 (by rfl) ⟨806, by rfl⟩) (B 1613 (by norm_num) ⟨806, by rfl⟩ (by norm_num))
theorem R17213 : Reach 17213 := rs (se 3 (by rfl) ⟨3227, by rfl⟩) (B 6455 (by norm_num) ⟨3227, by rfl⟩ (by norm_num))
theorem R17221 : Reach 17221 := rs (se 4 (by rfl) ⟨1614, by rfl⟩) (B 3229 (by norm_num) ⟨1614, by rfl⟩ (by norm_num))
theorem R17229 : Reach 17229 := rs (se 3 (by rfl) ⟨3230, by rfl⟩) (B 6461 (by norm_num) ⟨3230, by rfl⟩ (by norm_num))
theorem R17237 : Reach 17237 := rs (se 9 (by rfl) ⟨50, by rfl⟩) (B 101 (by norm_num) ⟨50, by rfl⟩ (by norm_num))
theorem R17245 : Reach 17245 := rs (se 3 (by rfl) ⟨3233, by rfl⟩) (B 6467 (by norm_num) ⟨3233, by rfl⟩ (by norm_num))
theorem R50021 : Reach 50021 := rs (se 4 (by rfl) ⟨4689, by rfl⟩) (B 9379 (by norm_num) ⟨4689, by rfl⟩ (by norm_num))
theorem R17253 : Reach 17253 := rs (se 4 (by rfl) ⟨1617, by rfl⟩) (B 3235 (by norm_num) ⟨1617, by rfl⟩ (by norm_num))
theorem R17261 : Reach 17261 := rs (se 3 (by rfl) ⟨3236, by rfl⟩) (B 6473 (by norm_num) ⟨3236, by rfl⟩ (by norm_num))
theorem R17269 : Reach 17269 := rs (se 5 (by rfl) ⟨809, by rfl⟩) (B 1619 (by norm_num) ⟨809, by rfl⟩ (by norm_num))
theorem R17277 : Reach 17277 := rs (se 3 (by rfl) ⟨3239, by rfl⟩) (B 6479 (by norm_num) ⟨3239, by rfl⟩ (by norm_num))
theorem R17285 : Reach 17285 := rs (se 4 (by rfl) ⟨1620, by rfl⟩) (B 3241 (by norm_num) ⟨1620, by rfl⟩ (by norm_num))
theorem R17293 : Reach 17293 := rs (se 3 (by rfl) ⟨3242, by rfl⟩) (B 6485 (by norm_num) ⟨3242, by rfl⟩ (by norm_num))
theorem R17301 : Reach 17301 := rs (se 6 (by rfl) ⟨405, by rfl⟩) (B 811 (by norm_num) ⟨405, by rfl⟩ (by norm_num))
theorem R17309 : Reach 17309 := rs (se 3 (by rfl) ⟨3245, by rfl⟩) (B 6491 (by norm_num) ⟨3245, by rfl⟩ (by norm_num))
theorem R17317 : Reach 17317 := rs (se 4 (by rfl) ⟨1623, by rfl⟩) (B 3247 (by norm_num) ⟨1623, by rfl⟩ (by norm_num))
theorem R17325 : Reach 17325 := rs (se 3 (by rfl) ⟨3248, by rfl⟩) (B 6497 (by norm_num) ⟨3248, by rfl⟩ (by norm_num))
theorem R17333 : Reach 17333 := rs (se 5 (by rfl) ⟨812, by rfl⟩) (B 1625 (by norm_num) ⟨812, by rfl⟩ (by norm_num))
theorem R17341 : Reach 17341 := rs (se 3 (by rfl) ⟨3251, by rfl⟩) (B 6503 (by norm_num) ⟨3251, by rfl⟩ (by norm_num))
theorem R17349 : Reach 17349 := rs (se 4 (by rfl) ⟨1626, by rfl⟩) (B 3253 (by norm_num) ⟨1626, by rfl⟩ (by norm_num))
theorem R17357 : Reach 17357 := rs (se 3 (by rfl) ⟨3254, by rfl⟩) (B 6509 (by norm_num) ⟨3254, by rfl⟩ (by norm_num))
theorem R17365 : Reach 17365 := rs (se 7 (by rfl) ⟨203, by rfl⟩) (B 407 (by norm_num) ⟨203, by rfl⟩ (by norm_num))
theorem R17373 : Reach 17373 := rs (se 3 (by rfl) ⟨3257, by rfl⟩) (B 6515 (by norm_num) ⟨3257, by rfl⟩ (by norm_num))
theorem R17381 : Reach 17381 := rs (se 4 (by rfl) ⟨1629, by rfl⟩) (B 3259 (by norm_num) ⟨1629, by rfl⟩ (by norm_num))
theorem R17389 : Reach 17389 := rs (se 3 (by rfl) ⟨3260, by rfl⟩) (B 6521 (by norm_num) ⟨3260, by rfl⟩ (by norm_num))
theorem R50165 : Reach 50165 := rs (se 5 (by rfl) ⟨2351, by rfl⟩) (B 4703 (by norm_num) ⟨2351, by rfl⟩ (by norm_num))
theorem R17397 : Reach 17397 := rs (se 5 (by rfl) ⟨815, by rfl⟩) (B 1631 (by norm_num) ⟨815, by rfl⟩ (by norm_num))
theorem R17405 : Reach 17405 := rs (se 3 (by rfl) ⟨3263, by rfl⟩) (B 6527 (by norm_num) ⟨3263, by rfl⟩ (by norm_num))
theorem R17413 : Reach 17413 := rs (se 4 (by rfl) ⟨1632, by rfl⟩) (B 3265 (by norm_num) ⟨1632, by rfl⟩ (by norm_num))
theorem R17421 : Reach 17421 := rs (se 3 (by rfl) ⟨3266, by rfl⟩) (B 6533 (by norm_num) ⟨3266, by rfl⟩ (by norm_num))
theorem R17429 : Reach 17429 := rs (se 6 (by rfl) ⟨408, by rfl⟩) (B 817 (by norm_num) ⟨408, by rfl⟩ (by norm_num))
theorem R17437 : Reach 17437 := rs (se 3 (by rfl) ⟨3269, by rfl⟩) (B 6539 (by norm_num) ⟨3269, by rfl⟩ (by norm_num))
theorem R17445 : Reach 17445 := rs (se 4 (by rfl) ⟨1635, by rfl⟩) (B 3271 (by norm_num) ⟨1635, by rfl⟩ (by norm_num))
theorem R17453 : Reach 17453 := rs (se 3 (by rfl) ⟨3272, by rfl⟩) (B 6545 (by norm_num) ⟨3272, by rfl⟩ (by norm_num))
theorem R17461 : Reach 17461 := rs (se 5 (by rfl) ⟨818, by rfl⟩) (B 1637 (by norm_num) ⟨818, by rfl⟩ (by norm_num))
theorem R17469 : Reach 17469 := rs (se 3 (by rfl) ⟨3275, by rfl⟩) (B 6551 (by norm_num) ⟨3275, by rfl⟩ (by norm_num))
theorem R17477 : Reach 17477 := rs (se 4 (by rfl) ⟨1638, by rfl⟩) (B 3277 (by norm_num) ⟨1638, by rfl⟩ (by norm_num))
theorem R17485 : Reach 17485 := rs (se 3 (by rfl) ⟨3278, by rfl⟩) (B 6557 (by norm_num) ⟨3278, by rfl⟩ (by norm_num))
theorem R17493 : Reach 17493 := rs (se 8 (by rfl) ⟨102, by rfl⟩) (B 205 (by norm_num) ⟨102, by rfl⟩ (by norm_num))
theorem R17501 : Reach 17501 := rs (se 3 (by rfl) ⟨3281, by rfl⟩) (B 6563 (by norm_num) ⟨3281, by rfl⟩ (by norm_num))
theorem R17509 : Reach 17509 := rs (se 4 (by rfl) ⟨1641, by rfl⟩) (B 3283 (by norm_num) ⟨1641, by rfl⟩ (by norm_num))
theorem R17517 : Reach 17517 := rs (se 3 (by rfl) ⟨3284, by rfl⟩) (B 6569 (by norm_num) ⟨3284, by rfl⟩ (by norm_num))
theorem R17525 : Reach 17525 := rs (se 5 (by rfl) ⟨821, by rfl⟩) (B 1643 (by norm_num) ⟨821, by rfl⟩ (by norm_num))
theorem R17533 : Reach 17533 := rs (se 3 (by rfl) ⟨3287, by rfl⟩) (B 6575 (by norm_num) ⟨3287, by rfl⟩ (by norm_num))
theorem R17541 : Reach 17541 := rs (se 4 (by rfl) ⟨1644, by rfl⟩) (B 3289 (by norm_num) ⟨1644, by rfl⟩ (by norm_num))
theorem R17549 : Reach 17549 := rs (se 3 (by rfl) ⟨3290, by rfl⟩) (B 6581 (by norm_num) ⟨3290, by rfl⟩ (by norm_num))
theorem R181397 : Reach 181397 := rs (se 6 (by rfl) ⟨4251, by rfl⟩) (B 8503 (by norm_num) ⟨4251, by rfl⟩ (by norm_num))
theorem R17557 : Reach 17557 := rs (se 6 (by rfl) ⟨411, by rfl⟩) (B 823 (by norm_num) ⟨411, by rfl⟩ (by norm_num))
theorem R17565 : Reach 17565 := rs (se 3 (by rfl) ⟨3293, by rfl⟩) (B 6587 (by norm_num) ⟨3293, by rfl⟩ (by norm_num))
theorem R17573 : Reach 17573 := rs (se 4 (by rfl) ⟨1647, by rfl⟩) (B 3295 (by norm_num) ⟨1647, by rfl⟩ (by norm_num))
theorem R50341 : Reach 50341 := rs (se 4 (by rfl) ⟨4719, by rfl⟩) (B 9439 (by norm_num) ⟨4719, by rfl⟩ (by norm_num))
theorem R17581 : Reach 17581 := rs (se 3 (by rfl) ⟨3296, by rfl⟩) (B 6593 (by norm_num) ⟨3296, by rfl⟩ (by norm_num))
theorem R17589 : Reach 17589 := rs (se 5 (by rfl) ⟨824, by rfl⟩) (B 1649 (by norm_num) ⟨824, by rfl⟩ (by norm_num))
theorem R17597 : Reach 17597 := rs (se 3 (by rfl) ⟨3299, by rfl⟩) (B 6599 (by norm_num) ⟨3299, by rfl⟩ (by norm_num))
theorem R17605 : Reach 17605 := rs (se 4 (by rfl) ⟨1650, by rfl⟩) (B 3301 (by norm_num) ⟨1650, by rfl⟩ (by norm_num))
theorem R17613 : Reach 17613 := rs (se 3 (by rfl) ⟨3302, by rfl⟩) (B 6605 (by norm_num) ⟨3302, by rfl⟩ (by norm_num))
theorem R17621 : Reach 17621 := rs (se 7 (by rfl) ⟨206, by rfl⟩) (B 413 (by norm_num) ⟨206, by rfl⟩ (by norm_num))
theorem R17629 : Reach 17629 := rs (se 3 (by rfl) ⟨3305, by rfl⟩) (B 6611 (by norm_num) ⟨3305, by rfl⟩ (by norm_num))
theorem R17637 : Reach 17637 := rs (se 4 (by rfl) ⟨1653, by rfl⟩) (B 3307 (by norm_num) ⟨1653, by rfl⟩ (by norm_num))
theorem R17645 : Reach 17645 := rs (se 3 (by rfl) ⟨3308, by rfl⟩) (B 6617 (by norm_num) ⟨3308, by rfl⟩ (by norm_num))
theorem R17653 : Reach 17653 := rs (se 5 (by rfl) ⟨827, by rfl⟩) (B 1655 (by norm_num) ⟨827, by rfl⟩ (by norm_num))
theorem R17661 : Reach 17661 := rs (se 3 (by rfl) ⟨3311, by rfl⟩) (B 6623 (by norm_num) ⟨3311, by rfl⟩ (by norm_num))
theorem R17669 : Reach 17669 := rs (se 4 (by rfl) ⟨1656, by rfl⟩) (B 3313 (by norm_num) ⟨1656, by rfl⟩ (by norm_num))
theorem R17677 : Reach 17677 := rs (se 3 (by rfl) ⟨3314, by rfl⟩) (B 6629 (by norm_num) ⟨3314, by rfl⟩ (by norm_num))
theorem R50453 : Reach 50453 := rs (se 6 (by rfl) ⟨1182, by rfl⟩) (B 2365 (by norm_num) ⟨1182, by rfl⟩ (by norm_num))
theorem R17685 : Reach 17685 := rs (se 6 (by rfl) ⟨414, by rfl⟩) (B 829 (by norm_num) ⟨414, by rfl⟩ (by norm_num))
theorem R17693 : Reach 17693 := rs (se 3 (by rfl) ⟨3317, by rfl⟩) (B 6635 (by norm_num) ⟨3317, by rfl⟩ (by norm_num))
theorem R17701 : Reach 17701 := rs (se 4 (by rfl) ⟨1659, by rfl⟩) (B 3319 (by norm_num) ⟨1659, by rfl⟩ (by norm_num))
theorem R17709 : Reach 17709 := rs (se 3 (by rfl) ⟨3320, by rfl⟩) (B 6641 (by norm_num) ⟨3320, by rfl⟩ (by norm_num))
theorem R17717 : Reach 17717 := rs (se 5 (by rfl) ⟨830, by rfl⟩) (B 1661 (by norm_num) ⟨830, by rfl⟩ (by norm_num))
theorem R17725 : Reach 17725 := rs (se 3 (by rfl) ⟨3323, by rfl⟩) (B 6647 (by norm_num) ⟨3323, by rfl⟩ (by norm_num))
theorem R17733 : Reach 17733 := rs (se 4 (by rfl) ⟨1662, by rfl⟩) (B 3325 (by norm_num) ⟨1662, by rfl⟩ (by norm_num))
theorem R17741 : Reach 17741 := rs (se 3 (by rfl) ⟨3326, by rfl⟩) (B 6653 (by norm_num) ⟨3326, by rfl⟩ (by norm_num))
theorem R17749 : Reach 17749 := rs (se 12 (by rfl) ⟨6, by rfl⟩) (B 13 (by norm_num) ⟨6, by rfl⟩ (by norm_num))
theorem R17757 : Reach 17757 := rs (se 3 (by rfl) ⟨3329, by rfl⟩) (B 6659 (by norm_num) ⟨3329, by rfl⟩ (by norm_num))
theorem R17765 : Reach 17765 := rs (se 4 (by rfl) ⟨1665, by rfl⟩) (B 3331 (by norm_num) ⟨1665, by rfl⟩ (by norm_num))
theorem R17773 : Reach 17773 := rs (se 3 (by rfl) ⟨3332, by rfl⟩) (B 6665 (by norm_num) ⟨3332, by rfl⟩ (by norm_num))
theorem R17781 : Reach 17781 := rs (se 5 (by rfl) ⟨833, by rfl⟩) (B 1667 (by norm_num) ⟨833, by rfl⟩ (by norm_num))
theorem R17789 : Reach 17789 := rs (se 3 (by rfl) ⟨3335, by rfl⟩) (B 6671 (by norm_num) ⟨3335, by rfl⟩ (by norm_num))
theorem R17797 : Reach 17797 := rs (se 4 (by rfl) ⟨1668, by rfl⟩) (B 3337 (by norm_num) ⟨1668, by rfl⟩ (by norm_num))
theorem R17805 : Reach 17805 := rs (se 3 (by rfl) ⟨3338, by rfl⟩) (B 6677 (by norm_num) ⟨3338, by rfl⟩ (by norm_num))
theorem R17813 : Reach 17813 := rs (se 6 (by rfl) ⟨417, by rfl⟩) (B 835 (by norm_num) ⟨417, by rfl⟩ (by norm_num))
theorem R17821 : Reach 17821 := rs (se 3 (by rfl) ⟨3341, by rfl⟩) (B 6683 (by norm_num) ⟨3341, by rfl⟩ (by norm_num))
theorem R50597 : Reach 50597 := rs (se 4 (by rfl) ⟨4743, by rfl⟩) (B 9487 (by norm_num) ⟨4743, by rfl⟩ (by norm_num))
theorem R17829 : Reach 17829 := rs (se 4 (by rfl) ⟨1671, by rfl⟩) (B 3343 (by norm_num) ⟨1671, by rfl⟩ (by norm_num))
theorem R17837 : Reach 17837 := rs (se 3 (by rfl) ⟨3344, by rfl⟩) (B 6689 (by norm_num) ⟨3344, by rfl⟩ (by norm_num))
theorem R17845 : Reach 17845 := rs (se 5 (by rfl) ⟨836, by rfl⟩) (B 1673 (by norm_num) ⟨836, by rfl⟩ (by norm_num))
theorem R17853 : Reach 17853 := rs (se 3 (by rfl) ⟨3347, by rfl⟩) (B 6695 (by norm_num) ⟨3347, by rfl⟩ (by norm_num))
theorem R17861 : Reach 17861 := rs (se 4 (by rfl) ⟨1674, by rfl⟩) (B 3349 (by norm_num) ⟨1674, by rfl⟩ (by norm_num))
theorem R17869 : Reach 17869 := rs (se 3 (by rfl) ⟨3350, by rfl⟩) (B 6701 (by norm_num) ⟨3350, by rfl⟩ (by norm_num))
theorem R17877 : Reach 17877 := rs (se 7 (by rfl) ⟨209, by rfl⟩) (B 419 (by norm_num) ⟨209, by rfl⟩ (by norm_num))
theorem R17885 : Reach 17885 := rs (se 3 (by rfl) ⟨3353, by rfl⟩) (B 6707 (by norm_num) ⟨3353, by rfl⟩ (by norm_num))
theorem R17893 : Reach 17893 := rs (se 4 (by rfl) ⟨1677, by rfl⟩) (B 3355 (by norm_num) ⟨1677, by rfl⟩ (by norm_num))
theorem R17901 : Reach 17901 := rs (se 3 (by rfl) ⟨3356, by rfl⟩) (B 6713 (by norm_num) ⟨3356, by rfl⟩ (by norm_num))
theorem R17909 : Reach 17909 := rs (se 5 (by rfl) ⟨839, by rfl⟩) (B 1679 (by norm_num) ⟨839, by rfl⟩ (by norm_num))
theorem R17917 : Reach 17917 := rs (se 3 (by rfl) ⟨3359, by rfl⟩) (B 6719 (by norm_num) ⟨3359, by rfl⟩ (by norm_num))
theorem R17925 : Reach 17925 := rs (se 4 (by rfl) ⟨1680, by rfl⟩) (B 3361 (by norm_num) ⟨1680, by rfl⟩ (by norm_num))
theorem R17933 : Reach 17933 := rs (se 3 (by rfl) ⟨3362, by rfl⟩) (B 6725 (by norm_num) ⟨3362, by rfl⟩ (by norm_num))
theorem R17941 : Reach 17941 := rs (se 6 (by rfl) ⟨420, by rfl⟩) (B 841 (by norm_num) ⟨420, by rfl⟩ (by norm_num))
theorem R17949 : Reach 17949 := rs (se 3 (by rfl) ⟨3365, by rfl⟩) (B 6731 (by norm_num) ⟨3365, by rfl⟩ (by norm_num))
theorem R17957 : Reach 17957 := rs (se 4 (by rfl) ⟨1683, by rfl⟩) (B 3367 (by norm_num) ⟨1683, by rfl⟩ (by norm_num))
theorem R17965 : Reach 17965 := rs (se 3 (by rfl) ⟨3368, by rfl⟩) (B 6737 (by norm_num) ⟨3368, by rfl⟩ (by norm_num))
theorem R17973 : Reach 17973 := rs (se 5 (by rfl) ⟨842, by rfl⟩) (B 1685 (by norm_num) ⟨842, by rfl⟩ (by norm_num))
theorem R17981 : Reach 17981 := rs (se 3 (by rfl) ⟨3371, by rfl⟩) (B 6743 (by norm_num) ⟨3371, by rfl⟩ (by norm_num))
theorem R17989 : Reach 17989 := rs (se 4 (by rfl) ⟨1686, by rfl⟩) (B 3373 (by norm_num) ⟨1686, by rfl⟩ (by norm_num))
theorem R17997 : Reach 17997 := rs (se 3 (by rfl) ⟨3374, by rfl⟩) (B 6749 (by norm_num) ⟨3374, by rfl⟩ (by norm_num))
theorem R18005 : Reach 18005 := rs (se 8 (by rfl) ⟨105, by rfl⟩) (B 211 (by norm_num) ⟨105, by rfl⟩ (by norm_num))
theorem R18013 : Reach 18013 := rs (se 3 (by rfl) ⟨3377, by rfl⟩) (B 6755 (by norm_num) ⟨3377, by rfl⟩ (by norm_num))
theorem R18021 : Reach 18021 := rs (se 4 (by rfl) ⟨1689, by rfl⟩) (B 3379 (by norm_num) ⟨1689, by rfl⟩ (by norm_num))
theorem R18029 : Reach 18029 := rs (se 3 (by rfl) ⟨3380, by rfl⟩) (B 6761 (by norm_num) ⟨3380, by rfl⟩ (by norm_num))
theorem R18037 : Reach 18037 := rs (se 5 (by rfl) ⟨845, by rfl⟩) (B 1691 (by norm_num) ⟨845, by rfl⟩ (by norm_num))
theorem R18045 : Reach 18045 := rs (se 3 (by rfl) ⟨3383, by rfl⟩) (B 6767 (by norm_num) ⟨3383, by rfl⟩ (by norm_num))
theorem R18053 : Reach 18053 := rs (se 4 (by rfl) ⟨1692, by rfl⟩) (B 3385 (by norm_num) ⟨1692, by rfl⟩ (by norm_num))
theorem R18061 : Reach 18061 := rs (se 3 (by rfl) ⟨3386, by rfl⟩) (B 6773 (by norm_num) ⟨3386, by rfl⟩ (by norm_num))
theorem R18069 : Reach 18069 := rs (se 6 (by rfl) ⟨423, by rfl⟩) (B 847 (by norm_num) ⟨423, by rfl⟩ (by norm_num))
theorem R18077 : Reach 18077 := rs (se 3 (by rfl) ⟨3389, by rfl⟩) (B 6779 (by norm_num) ⟨3389, by rfl⟩ (by norm_num))
theorem R18085 : Reach 18085 := rs (se 4 (by rfl) ⟨1695, by rfl⟩) (B 3391 (by norm_num) ⟨1695, by rfl⟩ (by norm_num))
theorem R18093 : Reach 18093 := rs (se 3 (by rfl) ⟨3392, by rfl⟩) (B 6785 (by norm_num) ⟨3392, by rfl⟩ (by norm_num))
theorem R18101 : Reach 18101 := rs (se 5 (by rfl) ⟨848, by rfl⟩) (B 1697 (by norm_num) ⟨848, by rfl⟩ (by norm_num))
theorem R18109 : Reach 18109 := rs (se 3 (by rfl) ⟨3395, by rfl⟩) (B 6791 (by norm_num) ⟨3395, by rfl⟩ (by norm_num))
theorem R18117 : Reach 18117 := rs (se 4 (by rfl) ⟨1698, by rfl⟩) (B 3397 (by norm_num) ⟨1698, by rfl⟩ (by norm_num))
theorem R18125 : Reach 18125 := rs (se 3 (by rfl) ⟨3398, by rfl⟩) (B 6797 (by norm_num) ⟨3398, by rfl⟩ (by norm_num))
theorem R18133 : Reach 18133 := rs (se 7 (by rfl) ⟨212, by rfl⟩) (B 425 (by norm_num) ⟨212, by rfl⟩ (by norm_num))
theorem R18141 : Reach 18141 := rs (se 3 (by rfl) ⟨3401, by rfl⟩) (B 6803 (by norm_num) ⟨3401, by rfl⟩ (by norm_num))
theorem R18149 : Reach 18149 := rs (se 4 (by rfl) ⟨1701, by rfl⟩) (B 3403 (by norm_num) ⟨1701, by rfl⟩ (by norm_num))
theorem R18157 : Reach 18157 := rs (se 3 (by rfl) ⟨3404, by rfl⟩) (B 6809 (by norm_num) ⟨3404, by rfl⟩ (by norm_num))
theorem R18165 : Reach 18165 := rs (se 5 (by rfl) ⟨851, by rfl⟩) (B 1703 (by norm_num) ⟨851, by rfl⟩ (by norm_num))
theorem R18173 : Reach 18173 := rs (se 3 (by rfl) ⟨3407, by rfl⟩) (B 6815 (by norm_num) ⟨3407, by rfl⟩ (by norm_num))
theorem R18181 : Reach 18181 := rs (se 4 (by rfl) ⟨1704, by rfl⟩) (B 3409 (by norm_num) ⟨1704, by rfl⟩ (by norm_num))
theorem R18189 : Reach 18189 := rs (se 3 (by rfl) ⟨3410, by rfl⟩) (B 6821 (by norm_num) ⟨3410, by rfl⟩ (by norm_num))
theorem R18197 : Reach 18197 := rs (se 6 (by rfl) ⟨426, by rfl⟩) (B 853 (by norm_num) ⟨426, by rfl⟩ (by norm_num))
theorem R18205 : Reach 18205 := rs (se 3 (by rfl) ⟨3413, by rfl⟩) (B 6827 (by norm_num) ⟨3413, by rfl⟩ (by norm_num))
theorem R18213 : Reach 18213 := rs (se 4 (by rfl) ⟨1707, by rfl⟩) (B 3415 (by norm_num) ⟨1707, by rfl⟩ (by norm_num))
theorem R18221 : Reach 18221 := rs (se 3 (by rfl) ⟨3416, by rfl⟩) (B 6833 (by norm_num) ⟨3416, by rfl⟩ (by norm_num))
theorem R18229 : Reach 18229 := rs (se 5 (by rfl) ⟨854, by rfl⟩) (B 1709 (by norm_num) ⟨854, by rfl⟩ (by norm_num))
theorem R18237 : Reach 18237 := rs (se 3 (by rfl) ⟨3419, by rfl⟩) (B 6839 (by norm_num) ⟨3419, by rfl⟩ (by norm_num))
theorem R18245 : Reach 18245 := rs (se 4 (by rfl) ⟨1710, by rfl⟩) (B 3421 (by norm_num) ⟨1710, by rfl⟩ (by norm_num))
theorem R18253 : Reach 18253 := rs (se 3 (by rfl) ⟨3422, by rfl⟩) (B 6845 (by norm_num) ⟨3422, by rfl⟩ (by norm_num))
theorem R51029 : Reach 51029 := rs (se 9 (by rfl) ⟨149, by rfl⟩) (B 299 (by norm_num) ⟨149, by rfl⟩ (by norm_num))
theorem R18261 : Reach 18261 := rs (se 9 (by rfl) ⟨53, by rfl⟩) (B 107 (by norm_num) ⟨53, by rfl⟩ (by norm_num))
theorem R18269 : Reach 18269 := rs (se 3 (by rfl) ⟨3425, by rfl⟩) (B 6851 (by norm_num) ⟨3425, by rfl⟩ (by norm_num))
theorem R18277 : Reach 18277 := rs (se 4 (by rfl) ⟨1713, by rfl⟩) (B 3427 (by norm_num) ⟨1713, by rfl⟩ (by norm_num))
theorem R18285 : Reach 18285 := rs (se 3 (by rfl) ⟨3428, by rfl⟩) (B 6857 (by norm_num) ⟨3428, by rfl⟩ (by norm_num))
theorem R18293 : Reach 18293 := rs (se 5 (by rfl) ⟨857, by rfl⟩) (B 1715 (by norm_num) ⟨857, by rfl⟩ (by norm_num))
theorem R18301 : Reach 18301 := rs (se 3 (by rfl) ⟨3431, by rfl⟩) (B 6863 (by norm_num) ⟨3431, by rfl⟩ (by norm_num))
theorem R18309 : Reach 18309 := rs (se 4 (by rfl) ⟨1716, by rfl⟩) (B 3433 (by norm_num) ⟨1716, by rfl⟩ (by norm_num))
theorem R18317 : Reach 18317 := rs (se 3 (by rfl) ⟨3434, by rfl⟩) (B 6869 (by norm_num) ⟨3434, by rfl⟩ (by norm_num))
theorem R18325 : Reach 18325 := rs (se 6 (by rfl) ⟨429, by rfl⟩) (B 859 (by norm_num) ⟨429, by rfl⟩ (by norm_num))
theorem R18333 : Reach 18333 := rs (se 3 (by rfl) ⟨3437, by rfl⟩) (B 6875 (by norm_num) ⟨3437, by rfl⟩ (by norm_num))
theorem R18341 : Reach 18341 := rs (se 4 (by rfl) ⟨1719, by rfl⟩) (B 3439 (by norm_num) ⟨1719, by rfl⟩ (by norm_num))
theorem R18349 : Reach 18349 := rs (se 3 (by rfl) ⟨3440, by rfl⟩) (B 6881 (by norm_num) ⟨3440, by rfl⟩ (by norm_num))
theorem R18357 : Reach 18357 := rs (se 5 (by rfl) ⟨860, by rfl⟩) (B 1721 (by norm_num) ⟨860, by rfl⟩ (by norm_num))
theorem R18365 : Reach 18365 := rs (se 3 (by rfl) ⟨3443, by rfl⟩) (B 6887 (by norm_num) ⟨3443, by rfl⟩ (by norm_num))
theorem R18373 : Reach 18373 := rs (se 4 (by rfl) ⟨1722, by rfl⟩) (B 3445 (by norm_num) ⟨1722, by rfl⟩ (by norm_num))
theorem R18381 : Reach 18381 := rs (se 3 (by rfl) ⟨3446, by rfl⟩) (B 6893 (by norm_num) ⟨3446, by rfl⟩ (by norm_num))
theorem R18389 : Reach 18389 := rs (se 7 (by rfl) ⟨215, by rfl⟩) (B 431 (by norm_num) ⟨215, by rfl⟩ (by norm_num))
theorem R18397 : Reach 18397 := rs (se 3 (by rfl) ⟨3449, by rfl⟩) (B 6899 (by norm_num) ⟨3449, by rfl⟩ (by norm_num))
theorem R18405 : Reach 18405 := rs (se 4 (by rfl) ⟨1725, by rfl⟩) (B 3451 (by norm_num) ⟨1725, by rfl⟩ (by norm_num))
theorem R18413 : Reach 18413 := rs (se 3 (by rfl) ⟨3452, by rfl⟩) (B 6905 (by norm_num) ⟨3452, by rfl⟩ (by norm_num))
theorem R18421 : Reach 18421 := rs (se 5 (by rfl) ⟨863, by rfl⟩) (B 1727 (by norm_num) ⟨863, by rfl⟩ (by norm_num))
theorem R18429 : Reach 18429 := rs (se 3 (by rfl) ⟨3455, by rfl⟩) (B 6911 (by norm_num) ⟨3455, by rfl⟩ (by norm_num))
theorem R18437 : Reach 18437 := rs (se 4 (by rfl) ⟨1728, by rfl⟩) (B 3457 (by norm_num) ⟨1728, by rfl⟩ (by norm_num))
theorem R18445 : Reach 18445 := rs (se 3 (by rfl) ⟨3458, by rfl⟩) (B 6917 (by norm_num) ⟨3458, by rfl⟩ (by norm_num))
theorem R18453 : Reach 18453 := rs (se 6 (by rfl) ⟨432, by rfl⟩) (B 865 (by norm_num) ⟨432, by rfl⟩ (by norm_num))
theorem R18461 : Reach 18461 := rs (se 3 (by rfl) ⟨3461, by rfl⟩) (B 6923 (by norm_num) ⟨3461, by rfl⟩ (by norm_num))
theorem R18469 : Reach 18469 := rs (se 4 (by rfl) ⟨1731, by rfl⟩) (B 3463 (by norm_num) ⟨1731, by rfl⟩ (by norm_num))
theorem R18477 : Reach 18477 := rs (se 3 (by rfl) ⟨3464, by rfl⟩) (B 6929 (by norm_num) ⟨3464, by rfl⟩ (by norm_num))
theorem R18485 : Reach 18485 := rs (se 5 (by rfl) ⟨866, by rfl⟩) (B 1733 (by norm_num) ⟨866, by rfl⟩ (by norm_num))
theorem R18493 : Reach 18493 := rs (se 3 (by rfl) ⟨3467, by rfl⟩) (B 6935 (by norm_num) ⟨3467, by rfl⟩ (by norm_num))
theorem R18501 : Reach 18501 := rs (se 4 (by rfl) ⟨1734, by rfl⟩) (B 3469 (by norm_num) ⟨1734, by rfl⟩ (by norm_num))
theorem R18509 : Reach 18509 := rs (se 3 (by rfl) ⟨3470, by rfl⟩) (B 6941 (by norm_num) ⟨3470, by rfl⟩ (by norm_num))
theorem R18517 : Reach 18517 := rs (se 8 (by rfl) ⟨108, by rfl⟩) (B 217 (by norm_num) ⟨108, by rfl⟩ (by norm_num))
theorem R18525 : Reach 18525 := rs (se 3 (by rfl) ⟨3473, by rfl⟩) (B 6947 (by norm_num) ⟨3473, by rfl⟩ (by norm_num))
theorem R18533 : Reach 18533 := rs (se 4 (by rfl) ⟨1737, by rfl⟩) (B 3475 (by norm_num) ⟨1737, by rfl⟩ (by norm_num))
theorem R18541 : Reach 18541 := rs (se 3 (by rfl) ⟨3476, by rfl⟩) (B 6953 (by norm_num) ⟨3476, by rfl⟩ (by norm_num))
theorem R18549 : Reach 18549 := rs (se 5 (by rfl) ⟨869, by rfl⟩) (B 1739 (by norm_num) ⟨869, by rfl⟩ (by norm_num))
theorem R18557 : Reach 18557 := rs (se 3 (by rfl) ⟨3479, by rfl⟩) (B 6959 (by norm_num) ⟨3479, by rfl⟩ (by norm_num))
theorem R18565 : Reach 18565 := rs (se 4 (by rfl) ⟨1740, by rfl⟩) (B 3481 (by norm_num) ⟨1740, by rfl⟩ (by norm_num))
theorem R18573 : Reach 18573 := rs (se 3 (by rfl) ⟨3482, by rfl⟩) (B 6965 (by norm_num) ⟨3482, by rfl⟩ (by norm_num))
theorem R51349 : Reach 51349 := rs (se 6 (by rfl) ⟨1203, by rfl⟩) (B 2407 (by norm_num) ⟨1203, by rfl⟩ (by norm_num))
theorem R18581 : Reach 18581 := rs (se 6 (by rfl) ⟨435, by rfl⟩) (B 871 (by norm_num) ⟨435, by rfl⟩ (by norm_num))
theorem R18589 : Reach 18589 := rs (se 3 (by rfl) ⟨3485, by rfl⟩) (B 6971 (by norm_num) ⟨3485, by rfl⟩ (by norm_num))
theorem R18597 : Reach 18597 := rs (se 4 (by rfl) ⟨1743, by rfl⟩) (B 3487 (by norm_num) ⟨1743, by rfl⟩ (by norm_num))
theorem R18605 : Reach 18605 := rs (se 3 (by rfl) ⟨3488, by rfl⟩) (B 6977 (by norm_num) ⟨3488, by rfl⟩ (by norm_num))
theorem R18613 : Reach 18613 := rs (se 5 (by rfl) ⟨872, by rfl⟩) (B 1745 (by norm_num) ⟨872, by rfl⟩ (by norm_num))
theorem R18621 : Reach 18621 := rs (se 3 (by rfl) ⟨3491, by rfl⟩) (B 6983 (by norm_num) ⟨3491, by rfl⟩ (by norm_num))
theorem R18629 : Reach 18629 := rs (se 4 (by rfl) ⟨1746, by rfl⟩) (B 3493 (by norm_num) ⟨1746, by rfl⟩ (by norm_num))
theorem R18637 : Reach 18637 := rs (se 3 (by rfl) ⟨3494, by rfl⟩) (B 6989 (by norm_num) ⟨3494, by rfl⟩ (by norm_num))
theorem R18645 : Reach 18645 := rs (se 7 (by rfl) ⟨218, by rfl⟩) (B 437 (by norm_num) ⟨218, by rfl⟩ (by norm_num))
theorem R18653 : Reach 18653 := rs (se 3 (by rfl) ⟨3497, by rfl⟩) (B 6995 (by norm_num) ⟨3497, by rfl⟩ (by norm_num))
theorem R18661 : Reach 18661 := rs (se 4 (by rfl) ⟨1749, by rfl⟩) (B 3499 (by norm_num) ⟨1749, by rfl⟩ (by norm_num))
theorem R18669 : Reach 18669 := rs (se 3 (by rfl) ⟨3500, by rfl⟩) (B 7001 (by norm_num) ⟨3500, by rfl⟩ (by norm_num))
theorem R18677 : Reach 18677 := rs (se 5 (by rfl) ⟨875, by rfl⟩) (B 1751 (by norm_num) ⟨875, by rfl⟩ (by norm_num))
theorem R18685 : Reach 18685 := rs (se 3 (by rfl) ⟨3503, by rfl⟩) (B 7007 (by norm_num) ⟨3503, by rfl⟩ (by norm_num))
theorem R51461 : Reach 51461 := rs (se 4 (by rfl) ⟨4824, by rfl⟩) (B 9649 (by norm_num) ⟨4824, by rfl⟩ (by norm_num))
theorem R18693 : Reach 18693 := rs (se 4 (by rfl) ⟨1752, by rfl⟩) (B 3505 (by norm_num) ⟨1752, by rfl⟩ (by norm_num))
theorem R18701 : Reach 18701 := rs (se 3 (by rfl) ⟨3506, by rfl⟩) (B 7013 (by norm_num) ⟨3506, by rfl⟩ (by norm_num))
theorem R18709 : Reach 18709 := rs (se 6 (by rfl) ⟨438, by rfl⟩) (B 877 (by norm_num) ⟨438, by rfl⟩ (by norm_num))
theorem R18717 : Reach 18717 := rs (se 3 (by rfl) ⟨3509, by rfl⟩) (B 7019 (by norm_num) ⟨3509, by rfl⟩ (by norm_num))
theorem R18725 : Reach 18725 := rs (se 4 (by rfl) ⟨1755, by rfl⟩) (B 3511 (by norm_num) ⟨1755, by rfl⟩ (by norm_num))
theorem R18733 : Reach 18733 := rs (se 3 (by rfl) ⟨3512, by rfl⟩) (B 7025 (by norm_num) ⟨3512, by rfl⟩ (by norm_num))
theorem R51509 : Reach 51509 := rs (se 5 (by rfl) ⟨2414, by rfl⟩) (B 4829 (by norm_num) ⟨2414, by rfl⟩ (by norm_num))
theorem R18741 : Reach 18741 := rs (se 5 (by rfl) ⟨878, by rfl⟩) (B 1757 (by norm_num) ⟨878, by rfl⟩ (by norm_num))
theorem R18749 : Reach 18749 := rs (se 3 (by rfl) ⟨3515, by rfl⟩) (B 7031 (by norm_num) ⟨3515, by rfl⟩ (by norm_num))
theorem R18757 : Reach 18757 := rs (se 4 (by rfl) ⟨1758, by rfl⟩) (B 3517 (by norm_num) ⟨1758, by rfl⟩ (by norm_num))
theorem R18765 : Reach 18765 := rs (se 3 (by rfl) ⟨3518, by rfl⟩) (B 7037 (by norm_num) ⟨3518, by rfl⟩ (by norm_num))
theorem R18773 : Reach 18773 := rs (se 10 (by rfl) ⟨27, by rfl⟩) (B 55 (by norm_num) ⟨27, by rfl⟩ (by norm_num))
theorem R18781 : Reach 18781 := rs (se 3 (by rfl) ⟨3521, by rfl⟩) (B 7043 (by norm_num) ⟨3521, by rfl⟩ (by norm_num))
theorem R18789 : Reach 18789 := rs (se 4 (by rfl) ⟨1761, by rfl⟩) (B 3523 (by norm_num) ⟨1761, by rfl⟩ (by norm_num))
theorem R18797 : Reach 18797 := rs (se 3 (by rfl) ⟨3524, by rfl⟩) (B 7049 (by norm_num) ⟨3524, by rfl⟩ (by norm_num))
theorem R18805 : Reach 18805 := rs (se 5 (by rfl) ⟨881, by rfl⟩) (B 1763 (by norm_num) ⟨881, by rfl⟩ (by norm_num))
theorem R18813 : Reach 18813 := rs (se 3 (by rfl) ⟨3527, by rfl⟩) (B 7055 (by norm_num) ⟨3527, by rfl⟩ (by norm_num))
theorem R18821 : Reach 18821 := rs (se 4 (by rfl) ⟨1764, by rfl⟩) (B 3529 (by norm_num) ⟨1764, by rfl⟩ (by norm_num))
theorem R18829 : Reach 18829 := rs (se 3 (by rfl) ⟨3530, by rfl⟩) (B 7061 (by norm_num) ⟨3530, by rfl⟩ (by norm_num))
theorem R18837 : Reach 18837 := rs (se 6 (by rfl) ⟨441, by rfl⟩) (B 883 (by norm_num) ⟨441, by rfl⟩ (by norm_num))
theorem R18845 : Reach 18845 := rs (se 3 (by rfl) ⟨3533, by rfl⟩) (B 7067 (by norm_num) ⟨3533, by rfl⟩ (by norm_num))
theorem R18853 : Reach 18853 := rs (se 4 (by rfl) ⟨1767, by rfl⟩) (B 3535 (by norm_num) ⟨1767, by rfl⟩ (by norm_num))
theorem R18861 : Reach 18861 := rs (se 3 (by rfl) ⟨3536, by rfl⟩) (B 7073 (by norm_num) ⟨3536, by rfl⟩ (by norm_num))
theorem R51637 : Reach 51637 := rs (se 5 (by rfl) ⟨2420, by rfl⟩) (B 4841 (by norm_num) ⟨2420, by rfl⟩ (by norm_num))
theorem R18869 : Reach 18869 := rs (se 5 (by rfl) ⟨884, by rfl⟩) (B 1769 (by norm_num) ⟨884, by rfl⟩ (by norm_num))
theorem R18877 : Reach 18877 := rs (se 3 (by rfl) ⟨3539, by rfl⟩) (B 7079 (by norm_num) ⟨3539, by rfl⟩ (by norm_num))
theorem R18885 : Reach 18885 := rs (se 4 (by rfl) ⟨1770, by rfl⟩) (B 3541 (by norm_num) ⟨1770, by rfl⟩ (by norm_num))
theorem R18893 : Reach 18893 := rs (se 3 (by rfl) ⟨3542, by rfl⟩) (B 7085 (by norm_num) ⟨3542, by rfl⟩ (by norm_num))
theorem R18901 : Reach 18901 := rs (se 7 (by rfl) ⟨221, by rfl⟩) (B 443 (by norm_num) ⟨221, by rfl⟩ (by norm_num))
theorem R18909 : Reach 18909 := rs (se 3 (by rfl) ⟨3545, by rfl⟩) (B 7091 (by norm_num) ⟨3545, by rfl⟩ (by norm_num))
theorem R18917 : Reach 18917 := rs (se 4 (by rfl) ⟨1773, by rfl⟩) (B 3547 (by norm_num) ⟨1773, by rfl⟩ (by norm_num))
theorem R18925 : Reach 18925 := rs (se 3 (by rfl) ⟨3548, by rfl⟩) (B 7097 (by norm_num) ⟨3548, by rfl⟩ (by norm_num))
theorem R18933 : Reach 18933 := rs (se 5 (by rfl) ⟨887, by rfl⟩) (B 1775 (by norm_num) ⟨887, by rfl⟩ (by norm_num))
theorem R18941 : Reach 18941 := rs (se 3 (by rfl) ⟨3551, by rfl⟩) (B 7103 (by norm_num) ⟨3551, by rfl⟩ (by norm_num))
theorem R18949 : Reach 18949 := rs (se 4 (by rfl) ⟨1776, by rfl⟩) (B 3553 (by norm_num) ⟨1776, by rfl⟩ (by norm_num))
theorem R18957 : Reach 18957 := rs (se 3 (by rfl) ⟨3554, by rfl⟩) (B 7109 (by norm_num) ⟨3554, by rfl⟩ (by norm_num))
theorem R18965 : Reach 18965 := rs (se 6 (by rfl) ⟨444, by rfl⟩) (B 889 (by norm_num) ⟨444, by rfl⟩ (by norm_num))
theorem R18973 : Reach 18973 := rs (se 3 (by rfl) ⟨3557, by rfl⟩) (B 7115 (by norm_num) ⟨3557, by rfl⟩ (by norm_num))
theorem R51749 : Reach 51749 := rs (se 4 (by rfl) ⟨4851, by rfl⟩) (B 9703 (by norm_num) ⟨4851, by rfl⟩ (by norm_num))
theorem R18981 : Reach 18981 := rs (se 4 (by rfl) ⟨1779, by rfl⟩) (B 3559 (by norm_num) ⟨1779, by rfl⟩ (by norm_num))
theorem R18989 : Reach 18989 := rs (se 3 (by rfl) ⟨3560, by rfl⟩) (B 7121 (by norm_num) ⟨3560, by rfl⟩ (by norm_num))
theorem R18997 : Reach 18997 := rs (se 5 (by rfl) ⟨890, by rfl⟩) (B 1781 (by norm_num) ⟨890, by rfl⟩ (by norm_num))
theorem R19005 : Reach 19005 := rs (se 3 (by rfl) ⟨3563, by rfl⟩) (B 7127 (by norm_num) ⟨3563, by rfl⟩ (by norm_num))
theorem R19013 : Reach 19013 := rs (se 4 (by rfl) ⟨1782, by rfl⟩) (B 3565 (by norm_num) ⟨1782, by rfl⟩ (by norm_num))
theorem R19021 : Reach 19021 := rs (se 3 (by rfl) ⟨3566, by rfl⟩) (B 7133 (by norm_num) ⟨3566, by rfl⟩ (by norm_num))
theorem R19029 : Reach 19029 := rs (se 8 (by rfl) ⟨111, by rfl⟩) (B 223 (by norm_num) ⟨111, by rfl⟩ (by norm_num))
theorem R19037 : Reach 19037 := rs (se 3 (by rfl) ⟨3569, by rfl⟩) (B 7139 (by norm_num) ⟨3569, by rfl⟩ (by norm_num))
theorem R19045 : Reach 19045 := rs (se 4 (by rfl) ⟨1785, by rfl⟩) (B 3571 (by norm_num) ⟨1785, by rfl⟩ (by norm_num))
theorem R19053 : Reach 19053 := rs (se 3 (by rfl) ⟨3572, by rfl⟩) (B 7145 (by norm_num) ⟨3572, by rfl⟩ (by norm_num))
theorem R19061 : Reach 19061 := rs (se 5 (by rfl) ⟨893, by rfl⟩) (B 1787 (by norm_num) ⟨893, by rfl⟩ (by norm_num))
theorem R19069 : Reach 19069 := rs (se 3 (by rfl) ⟨3575, by rfl⟩) (B 7151 (by norm_num) ⟨3575, by rfl⟩ (by norm_num))
theorem R19077 : Reach 19077 := rs (se 4 (by rfl) ⟨1788, by rfl⟩) (B 3577 (by norm_num) ⟨1788, by rfl⟩ (by norm_num))
theorem R19085 : Reach 19085 := rs (se 3 (by rfl) ⟨3578, by rfl⟩) (B 7157 (by norm_num) ⟨3578, by rfl⟩ (by norm_num))
theorem R19093 : Reach 19093 := rs (se 6 (by rfl) ⟨447, by rfl⟩) (B 895 (by norm_num) ⟨447, by rfl⟩ (by norm_num))
theorem R19101 : Reach 19101 := rs (se 3 (by rfl) ⟨3581, by rfl⟩) (B 7163 (by norm_num) ⟨3581, by rfl⟩ (by norm_num))
theorem R19109 : Reach 19109 := rs (se 4 (by rfl) ⟨1791, by rfl⟩) (B 3583 (by norm_num) ⟨1791, by rfl⟩ (by norm_num))
theorem R19117 : Reach 19117 := rs (se 3 (by rfl) ⟨3584, by rfl⟩) (B 7169 (by norm_num) ⟨3584, by rfl⟩ (by norm_num))
theorem R51893 : Reach 51893 := rs (se 5 (by rfl) ⟨2432, by rfl⟩) (B 4865 (by norm_num) ⟨2432, by rfl⟩ (by norm_num))
theorem R19125 : Reach 19125 := rs (se 5 (by rfl) ⟨896, by rfl⟩) (B 1793 (by norm_num) ⟨896, by rfl⟩ (by norm_num))
theorem R19133 : Reach 19133 := rs (se 3 (by rfl) ⟨3587, by rfl⟩) (B 7175 (by norm_num) ⟨3587, by rfl⟩ (by norm_num))
theorem R19141 : Reach 19141 := rs (se 4 (by rfl) ⟨1794, by rfl⟩) (B 3589 (by norm_num) ⟨1794, by rfl⟩ (by norm_num))
theorem R19149 : Reach 19149 := rs (se 3 (by rfl) ⟨3590, by rfl⟩) (B 7181 (by norm_num) ⟨3590, by rfl⟩ (by norm_num))
theorem R19157 : Reach 19157 := rs (se 7 (by rfl) ⟨224, by rfl⟩) (B 449 (by norm_num) ⟨224, by rfl⟩ (by norm_num))
theorem R19165 : Reach 19165 := rs (se 3 (by rfl) ⟨3593, by rfl⟩) (B 7187 (by norm_num) ⟨3593, by rfl⟩ (by norm_num))
theorem R51941 : Reach 51941 := rs (se 4 (by rfl) ⟨4869, by rfl⟩) (B 9739 (by norm_num) ⟨4869, by rfl⟩ (by norm_num))
theorem R19173 : Reach 19173 := rs (se 4 (by rfl) ⟨1797, by rfl⟩) (B 3595 (by norm_num) ⟨1797, by rfl⟩ (by norm_num))
theorem R19181 : Reach 19181 := rs (se 3 (by rfl) ⟨3596, by rfl⟩) (B 7193 (by norm_num) ⟨3596, by rfl⟩ (by norm_num))
theorem R84725 : Reach 84725 := rs (se 5 (by rfl) ⟨3971, by rfl⟩) (B 7943 (by norm_num) ⟨3971, by rfl⟩ (by norm_num))
theorem R19189 : Reach 19189 := rs (se 5 (by rfl) ⟨899, by rfl⟩) (B 1799 (by norm_num) ⟨899, by rfl⟩ (by norm_num))
theorem R19197 : Reach 19197 := rs (se 3 (by rfl) ⟨3599, by rfl⟩) (B 7199 (by norm_num) ⟨3599, by rfl⟩ (by norm_num))
theorem R19205 : Reach 19205 := rs (se 4 (by rfl) ⟨1800, by rfl⟩) (B 3601 (by norm_num) ⟨1800, by rfl⟩ (by norm_num))
theorem R19213 : Reach 19213 := rs (se 3 (by rfl) ⟨3602, by rfl⟩) (B 7205 (by norm_num) ⟨3602, by rfl⟩ (by norm_num))
theorem R19221 : Reach 19221 := rs (se 6 (by rfl) ⟨450, by rfl⟩) (B 901 (by norm_num) ⟨450, by rfl⟩ (by norm_num))
theorem R19229 : Reach 19229 := rs (se 3 (by rfl) ⟨3605, by rfl⟩) (B 7211 (by norm_num) ⟨3605, by rfl⟩ (by norm_num))
theorem R19237 : Reach 19237 := rs (se 4 (by rfl) ⟨1803, by rfl⟩) (B 3607 (by norm_num) ⟨1803, by rfl⟩ (by norm_num))
theorem R19245 : Reach 19245 := rs (se 3 (by rfl) ⟨3608, by rfl⟩) (B 7217 (by norm_num) ⟨3608, by rfl⟩ (by norm_num))
theorem R19253 : Reach 19253 := rs (se 5 (by rfl) ⟨902, by rfl⟩) (B 1805 (by norm_num) ⟨902, by rfl⟩ (by norm_num))
theorem R19261 : Reach 19261 := rs (se 3 (by rfl) ⟨3611, by rfl⟩) (B 7223 (by norm_num) ⟨3611, by rfl⟩ (by norm_num))
theorem R19269 : Reach 19269 := rs (se 4 (by rfl) ⟨1806, by rfl⟩) (B 3613 (by norm_num) ⟨1806, by rfl⟩ (by norm_num))
theorem R19277 : Reach 19277 := rs (se 3 (by rfl) ⟨3614, by rfl⟩) (B 7229 (by norm_num) ⟨3614, by rfl⟩ (by norm_num))
theorem R19285 : Reach 19285 := rs (se 9 (by rfl) ⟨56, by rfl⟩) (B 113 (by norm_num) ⟨56, by rfl⟩ (by norm_num))
theorem R19293 : Reach 19293 := rs (se 3 (by rfl) ⟨3617, by rfl⟩) (B 7235 (by norm_num) ⟨3617, by rfl⟩ (by norm_num))
theorem R19301 : Reach 19301 := rs (se 4 (by rfl) ⟨1809, by rfl⟩) (B 3619 (by norm_num) ⟨1809, by rfl⟩ (by norm_num))
theorem R19309 : Reach 19309 := rs (se 3 (by rfl) ⟨3620, by rfl⟩) (B 7241 (by norm_num) ⟨3620, by rfl⟩ (by norm_num))
theorem R19317 : Reach 19317 := rs (se 5 (by rfl) ⟨905, by rfl⟩) (B 1811 (by norm_num) ⟨905, by rfl⟩ (by norm_num))
theorem R19325 : Reach 19325 := rs (se 3 (by rfl) ⟨3623, by rfl⟩) (B 7247 (by norm_num) ⟨3623, by rfl⟩ (by norm_num))
theorem R19333 : Reach 19333 := rs (se 4 (by rfl) ⟨1812, by rfl⟩) (B 3625 (by norm_num) ⟨1812, by rfl⟩ (by norm_num))
theorem R19341 : Reach 19341 := rs (se 3 (by rfl) ⟨3626, by rfl⟩) (B 7253 (by norm_num) ⟨3626, by rfl⟩ (by norm_num))
theorem R19349 : Reach 19349 := rs (se 6 (by rfl) ⟨453, by rfl⟩) (B 907 (by norm_num) ⟨453, by rfl⟩ (by norm_num))
theorem R19357 : Reach 19357 := rs (se 3 (by rfl) ⟨3629, by rfl⟩) (B 7259 (by norm_num) ⟨3629, by rfl⟩ (by norm_num))
theorem R19365 : Reach 19365 := rs (se 4 (by rfl) ⟨1815, by rfl⟩) (B 3631 (by norm_num) ⟨1815, by rfl⟩ (by norm_num))
theorem R19373 : Reach 19373 := rs (se 3 (by rfl) ⟨3632, by rfl⟩) (B 7265 (by norm_num) ⟨3632, by rfl⟩ (by norm_num))
theorem R19381 : Reach 19381 := rs (se 5 (by rfl) ⟨908, by rfl⟩) (B 1817 (by norm_num) ⟨908, by rfl⟩ (by norm_num))
theorem R19389 : Reach 19389 := rs (se 3 (by rfl) ⟨3635, by rfl⟩) (B 7271 (by norm_num) ⟨3635, by rfl⟩ (by norm_num))
theorem R19397 : Reach 19397 := rs (se 4 (by rfl) ⟨1818, by rfl⟩) (B 3637 (by norm_num) ⟨1818, by rfl⟩ (by norm_num))
theorem R19405 : Reach 19405 := rs (se 3 (by rfl) ⟨3638, by rfl⟩) (B 7277 (by norm_num) ⟨3638, by rfl⟩ (by norm_num))
theorem R52181 : Reach 52181 := rs (se 7 (by rfl) ⟨611, by rfl⟩) (B 1223 (by norm_num) ⟨611, by rfl⟩ (by norm_num))
theorem R19413 : Reach 19413 := rs (se 7 (by rfl) ⟨227, by rfl⟩) (B 455 (by norm_num) ⟨227, by rfl⟩ (by norm_num))
theorem R19421 : Reach 19421 := rs (se 3 (by rfl) ⟨3641, by rfl⟩) (B 7283 (by norm_num) ⟨3641, by rfl⟩ (by norm_num))
theorem R19429 : Reach 19429 := rs (se 4 (by rfl) ⟨1821, by rfl⟩) (B 3643 (by norm_num) ⟨1821, by rfl⟩ (by norm_num))
theorem R19437 : Reach 19437 := rs (se 3 (by rfl) ⟨3644, by rfl⟩) (B 7289 (by norm_num) ⟨3644, by rfl⟩ (by norm_num))
theorem R19445 : Reach 19445 := rs (se 5 (by rfl) ⟨911, by rfl⟩) (B 1823 (by norm_num) ⟨911, by rfl⟩ (by norm_num))
theorem R19453 : Reach 19453 := rs (se 3 (by rfl) ⟨3647, by rfl⟩) (B 7295 (by norm_num) ⟨3647, by rfl⟩ (by norm_num))
theorem R19461 : Reach 19461 := rs (se 4 (by rfl) ⟨1824, by rfl⟩) (B 3649 (by norm_num) ⟨1824, by rfl⟩ (by norm_num))
theorem R19469 : Reach 19469 := rs (se 3 (by rfl) ⟨3650, by rfl⟩) (B 7301 (by norm_num) ⟨3650, by rfl⟩ (by norm_num))
theorem R19477 : Reach 19477 := rs (se 6 (by rfl) ⟨456, by rfl⟩) (B 913 (by norm_num) ⟨456, by rfl⟩ (by norm_num))
theorem R19485 : Reach 19485 := rs (se 3 (by rfl) ⟨3653, by rfl⟩) (B 7307 (by norm_num) ⟨3653, by rfl⟩ (by norm_num))
theorem R19493 : Reach 19493 := rs (se 4 (by rfl) ⟨1827, by rfl⟩) (B 3655 (by norm_num) ⟨1827, by rfl⟩ (by norm_num))
theorem R19501 : Reach 19501 := rs (se 3 (by rfl) ⟨3656, by rfl⟩) (B 7313 (by norm_num) ⟨3656, by rfl⟩ (by norm_num))
theorem R19509 : Reach 19509 := rs (se 5 (by rfl) ⟨914, by rfl⟩) (B 1829 (by norm_num) ⟨914, by rfl⟩ (by norm_num))
theorem R19517 : Reach 19517 := rs (se 3 (by rfl) ⟨3659, by rfl⟩) (B 7319 (by norm_num) ⟨3659, by rfl⟩ (by norm_num))
theorem R19525 : Reach 19525 := rs (se 4 (by rfl) ⟨1830, by rfl⟩) (B 3661 (by norm_num) ⟨1830, by rfl⟩ (by norm_num))
theorem R19533 : Reach 19533 := rs (se 3 (by rfl) ⟨3662, by rfl⟩) (B 7325 (by norm_num) ⟨3662, by rfl⟩ (by norm_num))
theorem R19541 : Reach 19541 := rs (se 8 (by rfl) ⟨114, by rfl⟩) (B 229 (by norm_num) ⟨114, by rfl⟩ (by norm_num))
theorem R19549 : Reach 19549 := rs (se 3 (by rfl) ⟨3665, by rfl⟩) (B 7331 (by norm_num) ⟨3665, by rfl⟩ (by norm_num))
theorem R52325 : Reach 52325 := rs (se 4 (by rfl) ⟨4905, by rfl⟩) (B 9811 (by norm_num) ⟨4905, by rfl⟩ (by norm_num))
theorem R19557 : Reach 19557 := rs (se 4 (by rfl) ⟨1833, by rfl⟩) (B 3667 (by norm_num) ⟨1833, by rfl⟩ (by norm_num))
theorem R19565 : Reach 19565 := rs (se 3 (by rfl) ⟨3668, by rfl⟩) (B 7337 (by norm_num) ⟨3668, by rfl⟩ (by norm_num))
theorem R19573 : Reach 19573 := rs (se 5 (by rfl) ⟨917, by rfl⟩) (B 1835 (by norm_num) ⟨917, by rfl⟩ (by norm_num))
theorem R19581 : Reach 19581 := rs (se 3 (by rfl) ⟨3671, by rfl⟩) (B 7343 (by norm_num) ⟨3671, by rfl⟩ (by norm_num))
theorem R19589 : Reach 19589 := rs (se 4 (by rfl) ⟨1836, by rfl⟩) (B 3673 (by norm_num) ⟨1836, by rfl⟩ (by norm_num))
theorem R19597 : Reach 19597 := rs (se 3 (by rfl) ⟨3674, by rfl⟩) (B 7349 (by norm_num) ⟨3674, by rfl⟩ (by norm_num))
theorem R19605 : Reach 19605 := rs (se 6 (by rfl) ⟨459, by rfl⟩) (B 919 (by norm_num) ⟨459, by rfl⟩ (by norm_num))
theorem R19613 : Reach 19613 := rs (se 3 (by rfl) ⟨3677, by rfl⟩) (B 7355 (by norm_num) ⟨3677, by rfl⟩ (by norm_num))
theorem R19621 : Reach 19621 := rs (se 4 (by rfl) ⟨1839, by rfl⟩) (B 3679 (by norm_num) ⟨1839, by rfl⟩ (by norm_num))
theorem R19629 : Reach 19629 := rs (se 3 (by rfl) ⟨3680, by rfl⟩) (B 7361 (by norm_num) ⟨3680, by rfl⟩ (by norm_num))
theorem R19637 : Reach 19637 := rs (se 5 (by rfl) ⟨920, by rfl⟩) (B 1841 (by norm_num) ⟨920, by rfl⟩ (by norm_num))
theorem R19645 : Reach 19645 := rs (se 3 (by rfl) ⟨3683, by rfl⟩) (B 7367 (by norm_num) ⟨3683, by rfl⟩ (by norm_num))
theorem R19653 : Reach 19653 := rs (se 4 (by rfl) ⟨1842, by rfl⟩) (B 3685 (by norm_num) ⟨1842, by rfl⟩ (by norm_num))
theorem R19661 : Reach 19661 := rs (se 3 (by rfl) ⟨3686, by rfl⟩) (B 7373 (by norm_num) ⟨3686, by rfl⟩ (by norm_num))
theorem R19669 : Reach 19669 := rs (se 7 (by rfl) ⟨230, by rfl⟩) (B 461 (by norm_num) ⟨230, by rfl⟩ (by norm_num))
theorem R19677 : Reach 19677 := rs (se 3 (by rfl) ⟨3689, by rfl⟩) (B 7379 (by norm_num) ⟨3689, by rfl⟩ (by norm_num))
theorem R19685 : Reach 19685 := rs (se 4 (by rfl) ⟨1845, by rfl⟩) (B 3691 (by norm_num) ⟨1845, by rfl⟩ (by norm_num))
theorem R19693 : Reach 19693 := rs (se 3 (by rfl) ⟨3692, by rfl⟩) (B 7385 (by norm_num) ⟨3692, by rfl⟩ (by norm_num))
theorem R19701 : Reach 19701 := rs (se 5 (by rfl) ⟨923, by rfl⟩) (B 1847 (by norm_num) ⟨923, by rfl⟩ (by norm_num))
theorem R19709 : Reach 19709 := rs (se 3 (by rfl) ⟨3695, by rfl⟩) (B 7391 (by norm_num) ⟨3695, by rfl⟩ (by norm_num))
theorem R19717 : Reach 19717 := rs (se 4 (by rfl) ⟨1848, by rfl⟩) (B 3697 (by norm_num) ⟨1848, by rfl⟩ (by norm_num))
theorem R19725 : Reach 19725 := rs (se 3 (by rfl) ⟨3698, by rfl⟩) (B 7397 (by norm_num) ⟨3698, by rfl⟩ (by norm_num))
theorem R19733 : Reach 19733 := rs (se 6 (by rfl) ⟨462, by rfl⟩) (B 925 (by norm_num) ⟨462, by rfl⟩ (by norm_num))
theorem R19741 : Reach 19741 := rs (se 3 (by rfl) ⟨3701, by rfl⟩) (B 7403 (by norm_num) ⟨3701, by rfl⟩ (by norm_num))
theorem R19749 : Reach 19749 := rs (se 4 (by rfl) ⟨1851, by rfl⟩) (B 3703 (by norm_num) ⟨1851, by rfl⟩ (by norm_num))
theorem R19757 : Reach 19757 := rs (se 3 (by rfl) ⟨3704, by rfl⟩) (B 7409 (by norm_num) ⟨3704, by rfl⟩ (by norm_num))
theorem R19765 : Reach 19765 := rs (se 5 (by rfl) ⟨926, by rfl⟩) (B 1853 (by norm_num) ⟨926, by rfl⟩ (by norm_num))
theorem R19773 : Reach 19773 := rs (se 3 (by rfl) ⟨3707, by rfl⟩) (B 7415 (by norm_num) ⟨3707, by rfl⟩ (by norm_num))
theorem R19781 : Reach 19781 := rs (se 4 (by rfl) ⟨1854, by rfl⟩) (B 3709 (by norm_num) ⟨1854, by rfl⟩ (by norm_num))
theorem R19789 : Reach 19789 := rs (se 3 (by rfl) ⟨3710, by rfl⟩) (B 7421 (by norm_num) ⟨3710, by rfl⟩ (by norm_num))
theorem R19797 : Reach 19797 := rs (se 11 (by rfl) ⟨14, by rfl⟩) (B 29 (by norm_num) ⟨14, by rfl⟩ (by norm_num))
theorem R19805 : Reach 19805 := rs (se 3 (by rfl) ⟨3713, by rfl⟩) (B 7427 (by norm_num) ⟨3713, by rfl⟩ (by norm_num))
theorem R19813 : Reach 19813 := rs (se 4 (by rfl) ⟨1857, by rfl⟩) (B 3715 (by norm_num) ⟨1857, by rfl⟩ (by norm_num))
theorem R19821 : Reach 19821 := rs (se 3 (by rfl) ⟨3716, by rfl⟩) (B 7433 (by norm_num) ⟨3716, by rfl⟩ (by norm_num))
theorem R19829 : Reach 19829 := rs (se 5 (by rfl) ⟨929, by rfl⟩) (B 1859 (by norm_num) ⟨929, by rfl⟩ (by norm_num))
theorem R19837 : Reach 19837 := rs (se 3 (by rfl) ⟨3719, by rfl⟩) (B 7439 (by norm_num) ⟨3719, by rfl⟩ (by norm_num))
theorem R19845 : Reach 19845 := rs (se 4 (by rfl) ⟨1860, by rfl⟩) (B 3721 (by norm_num) ⟨1860, by rfl⟩ (by norm_num))
theorem R19853 : Reach 19853 := rs (se 3 (by rfl) ⟨3722, by rfl⟩) (B 7445 (by norm_num) ⟨3722, by rfl⟩ (by norm_num))
theorem R19861 : Reach 19861 := rs (se 6 (by rfl) ⟨465, by rfl⟩) (B 931 (by norm_num) ⟨465, by rfl⟩ (by norm_num))
theorem R19869 : Reach 19869 := rs (se 3 (by rfl) ⟨3725, by rfl⟩) (B 7451 (by norm_num) ⟨3725, by rfl⟩ (by norm_num))
theorem R19877 : Reach 19877 := rs (se 4 (by rfl) ⟨1863, by rfl⟩) (B 3727 (by norm_num) ⟨1863, by rfl⟩ (by norm_num))
theorem R19885 : Reach 19885 := rs (se 3 (by rfl) ⟨3728, by rfl⟩) (B 7457 (by norm_num) ⟨3728, by rfl⟩ (by norm_num))
theorem R19893 : Reach 19893 := rs (se 5 (by rfl) ⟨932, by rfl⟩) (B 1865 (by norm_num) ⟨932, by rfl⟩ (by norm_num))
theorem R19901 : Reach 19901 := rs (se 3 (by rfl) ⟨3731, by rfl⟩) (B 7463 (by norm_num) ⟨3731, by rfl⟩ (by norm_num))
theorem R19909 : Reach 19909 := rs (se 4 (by rfl) ⟨1866, by rfl⟩) (B 3733 (by norm_num) ⟨1866, by rfl⟩ (by norm_num))
theorem R19917 : Reach 19917 := rs (se 3 (by rfl) ⟨3734, by rfl⟩) (B 7469 (by norm_num) ⟨3734, by rfl⟩ (by norm_num))
theorem R19925 : Reach 19925 := rs (se 7 (by rfl) ⟨233, by rfl⟩) (B 467 (by norm_num) ⟨233, by rfl⟩ (by norm_num))
theorem R19933 : Reach 19933 := rs (se 3 (by rfl) ⟨3737, by rfl⟩) (B 7475 (by norm_num) ⟨3737, by rfl⟩ (by norm_num))
theorem R19941 : Reach 19941 := rs (se 4 (by rfl) ⟨1869, by rfl⟩) (B 3739 (by norm_num) ⟨1869, by rfl⟩ (by norm_num))
theorem R19949 : Reach 19949 := rs (se 3 (by rfl) ⟨3740, by rfl⟩) (B 7481 (by norm_num) ⟨3740, by rfl⟩ (by norm_num))
theorem R19957 : Reach 19957 := rs (se 5 (by rfl) ⟨935, by rfl⟩) (B 1871 (by norm_num) ⟨935, by rfl⟩ (by norm_num))
theorem R19965 : Reach 19965 := rs (se 3 (by rfl) ⟨3743, by rfl⟩) (B 7487 (by norm_num) ⟨3743, by rfl⟩ (by norm_num))
theorem R19973 : Reach 19973 := rs (se 4 (by rfl) ⟨1872, by rfl⟩) (B 3745 (by norm_num) ⟨1872, by rfl⟩ (by norm_num))
theorem R19981 : Reach 19981 := rs (se 3 (by rfl) ⟨3746, by rfl⟩) (B 7493 (by norm_num) ⟨3746, by rfl⟩ (by norm_num))
theorem R52757 : Reach 52757 := rs (se 6 (by rfl) ⟨1236, by rfl⟩) (B 2473 (by norm_num) ⟨1236, by rfl⟩ (by norm_num))
theorem R19989 : Reach 19989 := rs (se 6 (by rfl) ⟨468, by rfl⟩) (B 937 (by norm_num) ⟨468, by rfl⟩ (by norm_num))
theorem R19997 : Reach 19997 := rs (se 3 (by rfl) ⟨3749, by rfl⟩) (B 7499 (by norm_num) ⟨3749, by rfl⟩ (by norm_num))
theorem R20021 : Reach 20021 := rs (se 5 (by rfl) ⟨938, by rfl⟩) (B 1877 (by norm_num) ⟨938, by rfl⟩ (by norm_num))
theorem R20029 : Reach 20029 := rs (se 3 (by rfl) ⟨3755, by rfl⟩) (B 7511 (by norm_num) ⟨3755, by rfl⟩ (by norm_num))
theorem R20045 : Reach 20045 := rs (se 3 (by rfl) ⟨3758, by rfl⟩) (B 7517 (by norm_num) ⟨3758, by rfl⟩ (by norm_num))
theorem R20069 : Reach 20069 := rs (se 4 (by rfl) ⟨1881, by rfl⟩) (B 3763 (by norm_num) ⟨1881, by rfl⟩ (by norm_num))
theorem R20093 : Reach 20093 := rs (se 3 (by rfl) ⟨3767, by rfl⟩) (B 7535 (by norm_num) ⟨3767, by rfl⟩ (by norm_num))
theorem R20101 : Reach 20101 := rs (se 4 (by rfl) ⟨1884, by rfl⟩) (B 3769 (by norm_num) ⟨1884, by rfl⟩ (by norm_num))
theorem R20117 : Reach 20117 := rs (se 6 (by rfl) ⟨471, by rfl⟩) (B 943 (by norm_num) ⟨471, by rfl⟩ (by norm_num))
theorem R20141 : Reach 20141 := rs (se 3 (by rfl) ⟨3776, by rfl⟩) (B 7553 (by norm_num) ⟨3776, by rfl⟩ (by norm_num))
theorem R20165 : Reach 20165 := rs (se 4 (by rfl) ⟨1890, by rfl⟩) (B 3781 (by norm_num) ⟨1890, by rfl⟩ (by norm_num))
theorem R52933 : Reach 52933 := rs (se 4 (by rfl) ⟨4962, by rfl⟩) (B 9925 (by norm_num) ⟨4962, by rfl⟩ (by norm_num))
theorem R20173 : Reach 20173 := rs (se 3 (by rfl) ⟨3782, by rfl⟩) (B 7565 (by norm_num) ⟨3782, by rfl⟩ (by norm_num))
theorem R20189 : Reach 20189 := rs (se 3 (by rfl) ⟨3785, by rfl⟩) (B 7571 (by norm_num) ⟨3785, by rfl⟩ (by norm_num))
theorem R20213 : Reach 20213 := rs (se 5 (by rfl) ⟨947, by rfl⟩) (B 1895 (by norm_num) ⟨947, by rfl⟩ (by norm_num))
theorem R20237 : Reach 20237 := rs (se 3 (by rfl) ⟨3794, by rfl⟩) (B 7589 (by norm_num) ⟨3794, by rfl⟩ (by norm_num))
theorem R20245 : Reach 20245 := rs (se 6 (by rfl) ⟨474, by rfl⟩) (B 949 (by norm_num) ⟨474, by rfl⟩ (by norm_num))
theorem R20261 : Reach 20261 := rs (se 4 (by rfl) ⟨1899, by rfl⟩) (B 3799 (by norm_num) ⟨1899, by rfl⟩ (by norm_num))
theorem R20285 : Reach 20285 := rs (se 3 (by rfl) ⟨3803, by rfl⟩) (B 7607 (by norm_num) ⟨3803, by rfl⟩ (by norm_num))
theorem R20309 : Reach 20309 := rs (se 9 (by rfl) ⟨59, by rfl⟩) (B 119 (by norm_num) ⟨59, by rfl⟩ (by norm_num))
theorem R20317 : Reach 20317 := rs (se 3 (by rfl) ⟨3809, by rfl⟩) (B 7619 (by norm_num) ⟨3809, by rfl⟩ (by norm_num))
theorem R20333 : Reach 20333 := rs (se 3 (by rfl) ⟨3812, by rfl⟩) (B 7625 (by norm_num) ⟨3812, by rfl⟩ (by norm_num))
theorem R20341 : Reach 20341 := rs (se 5 (by rfl) ⟨953, by rfl⟩) (B 1907 (by norm_num) ⟨953, by rfl⟩ (by norm_num))
theorem R20357 : Reach 20357 := rs (se 4 (by rfl) ⟨1908, by rfl⟩) (B 3817 (by norm_num) ⟨1908, by rfl⟩ (by norm_num))
theorem R20381 : Reach 20381 := rs (se 3 (by rfl) ⟨3821, by rfl⟩) (B 7643 (by norm_num) ⟨3821, by rfl⟩ (by norm_num))
theorem R20389 : Reach 20389 := rs (se 4 (by rfl) ⟨1911, by rfl⟩) (B 3823 (by norm_num) ⟨1911, by rfl⟩ (by norm_num))
theorem R20405 : Reach 20405 := rs (se 5 (by rfl) ⟨956, by rfl⟩) (B 1913 (by norm_num) ⟨956, by rfl⟩ (by norm_num))
theorem R53189 : Reach 53189 := rs (se 4 (by rfl) ⟨4986, by rfl⟩) (B 9973 (by norm_num) ⟨4986, by rfl⟩ (by norm_num))
theorem R20429 : Reach 20429 := rs (se 3 (by rfl) ⟨3830, by rfl⟩) (B 7661 (by norm_num) ⟨3830, by rfl⟩ (by norm_num))
theorem R20453 : Reach 20453 := rs (se 4 (by rfl) ⟨1917, by rfl⟩) (B 3835 (by norm_num) ⟨1917, by rfl⟩ (by norm_num))
theorem R20461 : Reach 20461 := rs (se 3 (by rfl) ⟨3836, by rfl⟩) (B 7673 (by norm_num) ⟨3836, by rfl⟩ (by norm_num))
theorem R20477 : Reach 20477 := rs (se 3 (by rfl) ⟨3839, by rfl⟩) (B 7679 (by norm_num) ⟨3839, by rfl⟩ (by norm_num))
theorem R20501 : Reach 20501 := rs (se 6 (by rfl) ⟨480, by rfl⟩) (B 961 (by norm_num) ⟨480, by rfl⟩ (by norm_num))
theorem R20525 : Reach 20525 := rs (se 3 (by rfl) ⟨3848, by rfl⟩) (B 7697 (by norm_num) ⟨3848, by rfl⟩ (by norm_num))
theorem R20533 : Reach 20533 := rs (se 5 (by rfl) ⟨962, by rfl⟩) (B 1925 (by norm_num) ⟨962, by rfl⟩ (by norm_num))
theorem R20549 : Reach 20549 := rs (se 4 (by rfl) ⟨1926, by rfl⟩) (B 3853 (by norm_num) ⟨1926, by rfl⟩ (by norm_num))
theorem R20573 : Reach 20573 := rs (se 3 (by rfl) ⟨3857, by rfl⟩) (B 7715 (by norm_num) ⟨3857, by rfl⟩ (by norm_num))
theorem R20597 : Reach 20597 := rs (se 5 (by rfl) ⟨965, by rfl⟩) (B 1931 (by norm_num) ⟨965, by rfl⟩ (by norm_num))
theorem R20605 : Reach 20605 := rs (se 3 (by rfl) ⟨3863, by rfl⟩) (B 7727 (by norm_num) ⟨3863, by rfl⟩ (by norm_num))
theorem R20621 : Reach 20621 := rs (se 3 (by rfl) ⟨3866, by rfl⟩) (B 7733 (by norm_num) ⟨3866, by rfl⟩ (by norm_num))
theorem R20645 : Reach 20645 := rs (se 4 (by rfl) ⟨1935, by rfl⟩) (B 3871 (by norm_num) ⟨1935, by rfl⟩ (by norm_num))
theorem R20669 : Reach 20669 := rs (se 3 (by rfl) ⟨3875, by rfl⟩) (B 7751 (by norm_num) ⟨3875, by rfl⟩ (by norm_num))
theorem R20677 : Reach 20677 := rs (se 4 (by rfl) ⟨1938, by rfl⟩) (B 3877 (by norm_num) ⟨1938, by rfl⟩ (by norm_num))
theorem R20693 : Reach 20693 := rs (se 7 (by rfl) ⟨242, by rfl⟩) (B 485 (by norm_num) ⟨242, by rfl⟩ (by norm_num))
theorem R20717 : Reach 20717 := rs (se 3 (by rfl) ⟨3884, by rfl⟩) (B 7769 (by norm_num) ⟨3884, by rfl⟩ (by norm_num))
theorem R20741 : Reach 20741 := rs (se 4 (by rfl) ⟨1944, by rfl⟩) (B 3889 (by norm_num) ⟨1944, by rfl⟩ (by norm_num))
theorem R20749 : Reach 20749 := rs (se 3 (by rfl) ⟨3890, by rfl⟩) (B 7781 (by norm_num) ⟨3890, by rfl⟩ (by norm_num))
theorem R20765 : Reach 20765 := rs (se 3 (by rfl) ⟨3893, by rfl⟩) (B 7787 (by norm_num) ⟨3893, by rfl⟩ (by norm_num))
theorem R20773 : Reach 20773 := rs (se 4 (by rfl) ⟨1947, by rfl⟩) (B 3895 (by norm_num) ⟨1947, by rfl⟩ (by norm_num))
theorem R20789 : Reach 20789 := rs (se 5 (by rfl) ⟨974, by rfl⟩) (B 1949 (by norm_num) ⟨974, by rfl⟩ (by norm_num))
theorem R20813 : Reach 20813 := rs (se 3 (by rfl) ⟨3902, by rfl⟩) (B 7805 (by norm_num) ⟨3902, by rfl⟩ (by norm_num))
theorem R20821 : Reach 20821 := rs (se 10 (by rfl) ⟨30, by rfl⟩) (B 61 (by norm_num) ⟨30, by rfl⟩ (by norm_num))
theorem R20837 : Reach 20837 := rs (se 4 (by rfl) ⟨1953, by rfl⟩) (B 3907 (by norm_num) ⟨1953, by rfl⟩ (by norm_num))
theorem R20845 : Reach 20845 := rs (se 3 (by rfl) ⟨3908, by rfl⟩) (B 7817 (by norm_num) ⟨3908, by rfl⟩ (by norm_num))
theorem R53621 : Reach 53621 := rs (se 5 (by rfl) ⟨2513, by rfl⟩) (B 5027 (by norm_num) ⟨2513, by rfl⟩ (by norm_num))
theorem R20861 : Reach 20861 := rs (se 3 (by rfl) ⟨3911, by rfl⟩) (B 7823 (by norm_num) ⟨3911, by rfl⟩ (by norm_num))
theorem R20885 : Reach 20885 := rs (se 6 (by rfl) ⟨489, by rfl⟩) (B 979 (by norm_num) ⟨489, by rfl⟩ (by norm_num))
theorem R20893 : Reach 20893 := rs (se 3 (by rfl) ⟨3917, by rfl⟩) (B 7835 (by norm_num) ⟨3917, by rfl⟩ (by norm_num))
theorem R20909 : Reach 20909 := rs (se 3 (by rfl) ⟨3920, by rfl⟩) (B 7841 (by norm_num) ⟨3920, by rfl⟩ (by norm_num))
theorem R20933 : Reach 20933 := rs (se 4 (by rfl) ⟨1962, by rfl⟩) (B 3925 (by norm_num) ⟨1962, by rfl⟩ (by norm_num))
theorem R20957 : Reach 20957 := rs (se 3 (by rfl) ⟨3929, by rfl⟩) (B 7859 (by norm_num) ⟨3929, by rfl⟩ (by norm_num))
theorem R20965 : Reach 20965 := rs (se 4 (by rfl) ⟨1965, by rfl⟩) (B 3931 (by norm_num) ⟨1965, by rfl⟩ (by norm_num))
theorem R20981 : Reach 20981 := rs (se 5 (by rfl) ⟨983, by rfl⟩) (B 1967 (by norm_num) ⟨983, by rfl⟩ (by norm_num))
theorem R20989 : Reach 20989 := rs (se 3 (by rfl) ⟨3935, by rfl⟩) (B 7871 (by norm_num) ⟨3935, by rfl⟩ (by norm_num))
theorem R21005 : Reach 21005 := rs (se 3 (by rfl) ⟨3938, by rfl⟩) (B 7877 (by norm_num) ⟨3938, by rfl⟩ (by norm_num))
theorem R21029 : Reach 21029 := rs (se 4 (by rfl) ⟨1971, by rfl⟩) (B 3943 (by norm_num) ⟨1971, by rfl⟩ (by norm_num))
theorem R21037 : Reach 21037 := rs (se 3 (by rfl) ⟨3944, by rfl⟩) (B 7889 (by norm_num) ⟨3944, by rfl⟩ (by norm_num))
theorem R21053 : Reach 21053 := rs (se 3 (by rfl) ⟨3947, by rfl⟩) (B 7895 (by norm_num) ⟨3947, by rfl⟩ (by norm_num))
theorem R21061 : Reach 21061 := rs (se 4 (by rfl) ⟨1974, by rfl⟩) (B 3949 (by norm_num) ⟨1974, by rfl⟩ (by norm_num))
theorem R21077 : Reach 21077 := rs (se 8 (by rfl) ⟨123, by rfl⟩) (B 247 (by norm_num) ⟨123, by rfl⟩ (by norm_num))
theorem R21101 : Reach 21101 := rs (se 3 (by rfl) ⟨3956, by rfl⟩) (B 7913 (by norm_num) ⟨3956, by rfl⟩ (by norm_num))
theorem R21109 : Reach 21109 := rs (se 5 (by rfl) ⟨989, by rfl⟩) (B 1979 (by norm_num) ⟨989, by rfl⟩ (by norm_num))
theorem R21125 : Reach 21125 := rs (se 4 (by rfl) ⟨1980, by rfl⟩) (B 3961 (by norm_num) ⟨1980, by rfl⟩ (by norm_num))
theorem R21149 : Reach 21149 := rs (se 3 (by rfl) ⟨3965, by rfl⟩) (B 7931 (by norm_num) ⟨3965, by rfl⟩ (by norm_num))
theorem R21173 : Reach 21173 := rs (se 5 (by rfl) ⟨992, by rfl⟩) (B 1985 (by norm_num) ⟨992, by rfl⟩ (by norm_num))
theorem R21181 : Reach 21181 := rs (se 3 (by rfl) ⟨3971, by rfl⟩) (B 7943 (by norm_num) ⟨3971, by rfl⟩ (by norm_num))
theorem R21197 : Reach 21197 := rs (se 3 (by rfl) ⟨3974, by rfl⟩) (B 7949 (by norm_num) ⟨3974, by rfl⟩ (by norm_num))
theorem R21221 : Reach 21221 := rs (se 4 (by rfl) ⟨1989, by rfl⟩) (B 3979 (by norm_num) ⟨1989, by rfl⟩ (by norm_num))
theorem R21245 : Reach 21245 := rs (se 3 (by rfl) ⟨3983, by rfl⟩) (B 7967 (by norm_num) ⟨3983, by rfl⟩ (by norm_num))
theorem R21253 : Reach 21253 := rs (se 4 (by rfl) ⟨1992, by rfl⟩) (B 3985 (by norm_num) ⟨1992, by rfl⟩ (by norm_num))
theorem R21269 : Reach 21269 := rs (se 6 (by rfl) ⟨498, by rfl⟩) (B 997 (by norm_num) ⟨498, by rfl⟩ (by norm_num))
theorem R54037 : Reach 54037 := rs (se 6 (by rfl) ⟨1266, by rfl⟩) (B 2533 (by norm_num) ⟨1266, by rfl⟩ (by norm_num))
theorem R54053 : Reach 54053 := rs (se 4 (by rfl) ⟨5067, by rfl⟩) (B 10135 (by norm_num) ⟨5067, by rfl⟩ (by norm_num))
theorem R21293 : Reach 21293 := rs (se 3 (by rfl) ⟨3992, by rfl⟩) (B 7985 (by norm_num) ⟨3992, by rfl⟩ (by norm_num))
theorem R21317 : Reach 21317 := rs (se 4 (by rfl) ⟨1998, by rfl⟩) (B 3997 (by norm_num) ⟨1998, by rfl⟩ (by norm_num))
theorem R21325 : Reach 21325 := rs (se 3 (by rfl) ⟨3998, by rfl⟩) (B 7997 (by norm_num) ⟨3998, by rfl⟩ (by norm_num))
theorem R54101 : Reach 54101 := rs (se 9 (by rfl) ⟨158, by rfl⟩) (B 317 (by norm_num) ⟨158, by rfl⟩ (by norm_num))
theorem R21341 : Reach 21341 := rs (se 3 (by rfl) ⟨4001, by rfl⟩) (B 8003 (by norm_num) ⟨4001, by rfl⟩ (by norm_num))
theorem R21365 : Reach 21365 := rs (se 5 (by rfl) ⟨1001, by rfl⟩) (B 2003 (by norm_num) ⟨1001, by rfl⟩ (by norm_num))
theorem R21389 : Reach 21389 := rs (se 3 (by rfl) ⟨4010, by rfl⟩) (B 8021 (by norm_num) ⟨4010, by rfl⟩ (by norm_num))
theorem R86933 : Reach 86933 := rs (se 6 (by rfl) ⟨2037, by rfl⟩) (B 4075 (by norm_num) ⟨2037, by rfl⟩ (by norm_num))
theorem R21397 : Reach 21397 := rs (se 6 (by rfl) ⟨501, by rfl⟩) (B 1003 (by norm_num) ⟨501, by rfl⟩ (by norm_num))
theorem R21413 : Reach 21413 := rs (se 4 (by rfl) ⟨2007, by rfl⟩) (B 4015 (by norm_num) ⟨2007, by rfl⟩ (by norm_num))
theorem R21437 : Reach 21437 := rs (se 3 (by rfl) ⟨4019, by rfl⟩) (B 8039 (by norm_num) ⟨4019, by rfl⟩ (by norm_num))
theorem R21461 : Reach 21461 := rs (se 7 (by rfl) ⟨251, by rfl⟩) (B 503 (by norm_num) ⟨251, by rfl⟩ (by norm_num))
theorem R21469 : Reach 21469 := rs (se 3 (by rfl) ⟨4025, by rfl⟩) (B 8051 (by norm_num) ⟨4025, by rfl⟩ (by norm_num))
theorem R21485 : Reach 21485 := rs (se 3 (by rfl) ⟨4028, by rfl⟩) (B 8057 (by norm_num) ⟨4028, by rfl⟩ (by norm_num))
theorem R21509 : Reach 21509 := rs (se 4 (by rfl) ⟨2016, by rfl⟩) (B 4033 (by norm_num) ⟨2016, by rfl⟩ (by norm_num))
theorem R21533 : Reach 21533 := rs (se 3 (by rfl) ⟨4037, by rfl⟩) (B 8075 (by norm_num) ⟨4037, by rfl⟩ (by norm_num))
theorem R21541 : Reach 21541 := rs (se 4 (by rfl) ⟨2019, by rfl⟩) (B 4039 (by norm_num) ⟨2019, by rfl⟩ (by norm_num))
theorem R21557 : Reach 21557 := rs (se 5 (by rfl) ⟨1010, by rfl⟩) (B 2021 (by norm_num) ⟨1010, by rfl⟩ (by norm_num))
theorem R54341 : Reach 54341 := rs (se 4 (by rfl) ⟨5094, by rfl⟩) (B 10189 (by norm_num) ⟨5094, by rfl⟩ (by norm_num))
theorem R21581 : Reach 21581 := rs (se 3 (by rfl) ⟨4046, by rfl⟩) (B 8093 (by norm_num) ⟨4046, by rfl⟩ (by norm_num))
theorem R21605 : Reach 21605 := rs (se 4 (by rfl) ⟨2025, by rfl⟩) (B 4051 (by norm_num) ⟨2025, by rfl⟩ (by norm_num))
theorem R21613 : Reach 21613 := rs (se 3 (by rfl) ⟨4052, by rfl⟩) (B 8105 (by norm_num) ⟨4052, by rfl⟩ (by norm_num))
theorem R21629 : Reach 21629 := rs (se 3 (by rfl) ⟨4055, by rfl⟩) (B 8111 (by norm_num) ⟨4055, by rfl⟩ (by norm_num))
theorem R21637 : Reach 21637 := rs (se 4 (by rfl) ⟨2028, by rfl⟩) (B 4057 (by norm_num) ⟨2028, by rfl⟩ (by norm_num))
theorem R21653 : Reach 21653 := rs (se 6 (by rfl) ⟨507, by rfl⟩) (B 1015 (by norm_num) ⟨507, by rfl⟩ (by norm_num))
theorem R21677 : Reach 21677 := rs (se 3 (by rfl) ⟨4064, by rfl⟩) (B 8129 (by norm_num) ⟨4064, by rfl⟩ (by norm_num))
theorem R21685 : Reach 21685 := rs (se 5 (by rfl) ⟨1016, by rfl⟩) (B 2033 (by norm_num) ⟨1016, by rfl⟩ (by norm_num))
theorem R21701 : Reach 21701 := rs (se 4 (by rfl) ⟨2034, by rfl⟩) (B 4069 (by norm_num) ⟨2034, by rfl⟩ (by norm_num))
theorem R54485 : Reach 54485 := rs (se 7 (by rfl) ⟨638, by rfl⟩) (B 1277 (by norm_num) ⟨638, by rfl⟩ (by norm_num))
theorem R21725 : Reach 21725 := rs (se 3 (by rfl) ⟨4073, by rfl⟩) (B 8147 (by norm_num) ⟨4073, by rfl⟩ (by norm_num))
theorem R21749 : Reach 21749 := rs (se 5 (by rfl) ⟨1019, by rfl⟩) (B 2039 (by norm_num) ⟨1019, by rfl⟩ (by norm_num))
theorem R21757 : Reach 21757 := rs (se 3 (by rfl) ⟨4079, by rfl⟩) (B 8159 (by norm_num) ⟨4079, by rfl⟩ (by norm_num))
theorem R21773 : Reach 21773 := rs (se 3 (by rfl) ⟨4082, by rfl⟩) (B 8165 (by norm_num) ⟨4082, by rfl⟩ (by norm_num))
theorem R87317 : Reach 87317 := rs (se 6 (by rfl) ⟨2046, by rfl⟩) (B 4093 (by norm_num) ⟨2046, by rfl⟩ (by norm_num))
theorem R21797 : Reach 21797 := rs (se 4 (by rfl) ⟨2043, by rfl⟩) (B 4087 (by norm_num) ⟨2043, by rfl⟩ (by norm_num))
theorem R21821 : Reach 21821 := rs (se 3 (by rfl) ⟨4091, by rfl⟩) (B 8183 (by norm_num) ⟨4091, by rfl⟩ (by norm_num))
theorem R21829 : Reach 21829 := rs (se 4 (by rfl) ⟨2046, by rfl⟩) (B 4093 (by norm_num) ⟨2046, by rfl⟩ (by norm_num))
theorem R120149 : Reach 120149 := rs (se 15 (by rfl) ⟨5, by rfl⟩) (B 11 (by norm_num) ⟨5, by rfl⟩ (by norm_num))
theorem R21845 : Reach 21845 := rs (se 16 (by rfl) ⟨0, by rfl⟩) (B 1 (by norm_num) ⟨0, by rfl⟩ (by norm_num))
theorem R21869 : Reach 21869 := rs (se 3 (by rfl) ⟨4100, by rfl⟩) (B 8201 (by norm_num) ⟨4100, by rfl⟩ (by norm_num))
theorem R21893 : Reach 21893 := rs (se 4 (by rfl) ⟨2052, by rfl⟩) (B 4105 (by norm_num) ⟨2052, by rfl⟩ (by norm_num))
theorem R21901 : Reach 21901 := rs (se 3 (by rfl) ⟨4106, by rfl⟩) (B 8213 (by norm_num) ⟨4106, by rfl⟩ (by norm_num))
theorem R21917 : Reach 21917 := rs (se 3 (by rfl) ⟨4109, by rfl⟩) (B 8219 (by norm_num) ⟨4109, by rfl⟩ (by norm_num))
theorem R21941 : Reach 21941 := rs (se 5 (by rfl) ⟨1028, by rfl⟩) (B 2057 (by norm_num) ⟨1028, by rfl⟩ (by norm_num))
theorem R21965 : Reach 21965 := rs (se 3 (by rfl) ⟨4118, by rfl⟩) (B 8237 (by norm_num) ⟨4118, by rfl⟩ (by norm_num))
theorem R21973 : Reach 21973 := rs (se 7 (by rfl) ⟨257, by rfl⟩) (B 515 (by norm_num) ⟨257, by rfl⟩ (by norm_num))
theorem R185813 : Reach 185813 := rs (se 7 (by rfl) ⟨2177, by rfl⟩) (B 4355 (by norm_num) ⟨2177, by rfl⟩ (by norm_num))
theorem R21989 : Reach 21989 := rs (se 4 (by rfl) ⟨2061, by rfl⟩) (B 4123 (by norm_num) ⟨2061, by rfl⟩ (by norm_num))
theorem R22013 : Reach 22013 := rs (se 3 (by rfl) ⟨4127, by rfl⟩) (B 8255 (by norm_num) ⟨4127, by rfl⟩ (by norm_num))
theorem R22037 : Reach 22037 := rs (se 6 (by rfl) ⟨516, by rfl⟩) (B 1033 (by norm_num) ⟨516, by rfl⟩ (by norm_num))
theorem R22045 : Reach 22045 := rs (se 3 (by rfl) ⟨4133, by rfl⟩) (B 8267 (by norm_num) ⟨4133, by rfl⟩ (by norm_num))
theorem R22061 : Reach 22061 := rs (se 3 (by rfl) ⟨4136, by rfl⟩) (B 8273 (by norm_num) ⟨4136, by rfl⟩ (by norm_num))
theorem R22085 : Reach 22085 := rs (se 4 (by rfl) ⟨2070, by rfl⟩) (B 4141 (by norm_num) ⟨2070, by rfl⟩ (by norm_num))
theorem R22109 : Reach 22109 := rs (se 3 (by rfl) ⟨4145, by rfl⟩) (B 8291 (by norm_num) ⟨4145, by rfl⟩ (by norm_num))
theorem R22117 : Reach 22117 := rs (se 4 (by rfl) ⟨2073, by rfl⟩) (B 4147 (by norm_num) ⟨2073, by rfl⟩ (by norm_num))
theorem R22133 : Reach 22133 := rs (se 5 (by rfl) ⟨1037, by rfl⟩) (B 2075 (by norm_num) ⟨1037, by rfl⟩ (by norm_num))
theorem R54917 : Reach 54917 := rs (se 4 (by rfl) ⟨5148, by rfl⟩) (B 10297 (by norm_num) ⟨5148, by rfl⟩ (by norm_num))
theorem R22157 : Reach 22157 := rs (se 3 (by rfl) ⟨4154, by rfl⟩) (B 8309 (by norm_num) ⟨4154, by rfl⟩ (by norm_num))
theorem R22181 : Reach 22181 := rs (se 4 (by rfl) ⟨2079, by rfl⟩) (B 4159 (by norm_num) ⟨2079, by rfl⟩ (by norm_num))
theorem R22189 : Reach 22189 := rs (se 3 (by rfl) ⟨4160, by rfl⟩) (B 8321 (by norm_num) ⟨4160, by rfl⟩ (by norm_num))
theorem R22205 : Reach 22205 := rs (se 3 (by rfl) ⟨4163, by rfl⟩) (B 8327 (by norm_num) ⟨4163, by rfl⟩ (by norm_num))
theorem R22229 : Reach 22229 := rs (se 7 (by rfl) ⟨260, by rfl⟩) (B 521 (by norm_num) ⟨260, by rfl⟩ (by norm_num))
theorem R22253 : Reach 22253 := rs (se 3 (by rfl) ⟨4172, by rfl⟩) (B 8345 (by norm_num) ⟨4172, by rfl⟩ (by norm_num))
theorem R22261 : Reach 22261 := rs (se 5 (by rfl) ⟨1043, by rfl⟩) (B 2087 (by norm_num) ⟨1043, by rfl⟩ (by norm_num))
theorem R22277 : Reach 22277 := rs (se 4 (by rfl) ⟨2088, by rfl⟩) (B 4177 (by norm_num) ⟨2088, by rfl⟩ (by norm_num))
theorem R22285 : Reach 22285 := rs (se 3 (by rfl) ⟨4178, by rfl⟩) (B 8357 (by norm_num) ⟨4178, by rfl⟩ (by norm_num))
theorem R22301 : Reach 22301 := rs (se 3 (by rfl) ⟨4181, by rfl⟩) (B 8363 (by norm_num) ⟨4181, by rfl⟩ (by norm_num))
theorem R22325 : Reach 22325 := rs (se 5 (by rfl) ⟨1046, by rfl⟩) (B 2093 (by norm_num) ⟨1046, by rfl⟩ (by norm_num))
theorem R22333 : Reach 22333 := rs (se 3 (by rfl) ⟨4187, by rfl⟩) (B 8375 (by norm_num) ⟨4187, by rfl⟩ (by norm_num))
theorem R22349 : Reach 22349 := rs (se 3 (by rfl) ⟨4190, by rfl⟩) (B 8381 (by norm_num) ⟨4190, by rfl⟩ (by norm_num))
theorem R22373 : Reach 22373 := rs (se 4 (by rfl) ⟨2097, by rfl⟩) (B 4195 (by norm_num) ⟨2097, by rfl⟩ (by norm_num))
theorem R22397 : Reach 22397 := rs (se 3 (by rfl) ⟨4199, by rfl⟩) (B 8399 (by norm_num) ⟨4199, by rfl⟩ (by norm_num))
theorem R22405 : Reach 22405 := rs (se 4 (by rfl) ⟨2100, by rfl⟩) (B 4201 (by norm_num) ⟨2100, by rfl⟩ (by norm_num))
theorem R22421 : Reach 22421 := rs (se 6 (by rfl) ⟨525, by rfl⟩) (B 1051 (by norm_num) ⟨525, by rfl⟩ (by norm_num))
theorem R22445 : Reach 22445 := rs (se 3 (by rfl) ⟨4208, by rfl⟩) (B 8417 (by norm_num) ⟨4208, by rfl⟩ (by norm_num))
theorem R22469 : Reach 22469 := rs (se 4 (by rfl) ⟨2106, by rfl⟩) (B 4213 (by norm_num) ⟨2106, by rfl⟩ (by norm_num))
theorem R22477 : Reach 22477 := rs (se 3 (by rfl) ⟨4214, by rfl⟩) (B 8429 (by norm_num) ⟨4214, by rfl⟩ (by norm_num))
theorem R22493 : Reach 22493 := rs (se 3 (by rfl) ⟨4217, by rfl⟩) (B 8435 (by norm_num) ⟨4217, by rfl⟩ (by norm_num))
theorem R22517 : Reach 22517 := rs (se 5 (by rfl) ⟨1055, by rfl⟩) (B 2111 (by norm_num) ⟨1055, by rfl⟩ (by norm_num))
theorem R22541 : Reach 22541 := rs (se 3 (by rfl) ⟨4226, by rfl⟩) (B 8453 (by norm_num) ⟨4226, by rfl⟩ (by norm_num))
theorem R22565 : Reach 22565 := rs (se 4 (by rfl) ⟨2115, by rfl⟩) (B 4231 (by norm_num) ⟨2115, by rfl⟩ (by norm_num))
theorem R55349 : Reach 55349 := rs (se 5 (by rfl) ⟨2594, by rfl⟩) (B 5189 (by norm_num) ⟨2594, by rfl⟩ (by norm_num))
theorem R22589 : Reach 22589 := rs (se 3 (by rfl) ⟨4235, by rfl⟩) (B 8471 (by norm_num) ⟨4235, by rfl⟩ (by norm_num))
theorem R22613 : Reach 22613 := rs (se 8 (by rfl) ⟨132, by rfl⟩) (B 265 (by norm_num) ⟨132, by rfl⟩ (by norm_num))
theorem R22621 : Reach 22621 := rs (se 3 (by rfl) ⟨4241, by rfl⟩) (B 8483 (by norm_num) ⟨4241, by rfl⟩ (by norm_num))
theorem R22637 : Reach 22637 := rs (se 3 (by rfl) ⟨4244, by rfl⟩) (B 8489 (by norm_num) ⟨4244, by rfl⟩ (by norm_num))
theorem R22661 : Reach 22661 := rs (se 4 (by rfl) ⟨2124, by rfl⟩) (B 4249 (by norm_num) ⟨2124, by rfl⟩ (by norm_num))
theorem R22685 : Reach 22685 := rs (se 3 (by rfl) ⟨4253, by rfl⟩) (B 8507 (by norm_num) ⟨4253, by rfl⟩ (by norm_num))
theorem R22693 : Reach 22693 := rs (se 4 (by rfl) ⟨2127, by rfl⟩) (B 4255 (by norm_num) ⟨2127, by rfl⟩ (by norm_num))
theorem R121013 : Reach 121013 := rs (se 5 (by rfl) ⟨5672, by rfl⟩) (B 11345 (by norm_num) ⟨5672, by rfl⟩ (by norm_num))
theorem R22709 : Reach 22709 := rs (se 5 (by rfl) ⟨1064, by rfl⟩) (B 2129 (by norm_num) ⟨1064, by rfl⟩ (by norm_num))
theorem R22733 : Reach 22733 := rs (se 3 (by rfl) ⟨4262, by rfl⟩) (B 8525 (by norm_num) ⟨4262, by rfl⟩ (by norm_num))
theorem R55525 : Reach 55525 := rs (se 4 (by rfl) ⟨5205, by rfl⟩) (B 10411 (by norm_num) ⟨5205, by rfl⟩ (by norm_num))
theorem R22757 : Reach 22757 := rs (se 4 (by rfl) ⟨2133, by rfl⟩) (B 4267 (by norm_num) ⟨2133, by rfl⟩ (by norm_num))
theorem R55541 : Reach 55541 := rs (se 5 (by rfl) ⟨2603, by rfl⟩) (B 5207 (by norm_num) ⟨2603, by rfl⟩ (by norm_num))
theorem R22781 : Reach 22781 := rs (se 3 (by rfl) ⟨4271, by rfl⟩) (B 8543 (by norm_num) ⟨4271, by rfl⟩ (by norm_num))
theorem R22805 : Reach 22805 := rs (se 6 (by rfl) ⟨534, by rfl⟩) (B 1069 (by norm_num) ⟨534, by rfl⟩ (by norm_num))
theorem R22829 : Reach 22829 := rs (se 3 (by rfl) ⟨4280, by rfl⟩) (B 8561 (by norm_num) ⟨4280, by rfl⟩ (by norm_num))
theorem R22837 : Reach 22837 := rs (se 5 (by rfl) ⟨1070, by rfl⟩) (B 2141 (by norm_num) ⟨1070, by rfl⟩ (by norm_num))
theorem R22853 : Reach 22853 := rs (se 4 (by rfl) ⟨2142, by rfl⟩) (B 4285 (by norm_num) ⟨2142, by rfl⟩ (by norm_num))
theorem R22861 : Reach 22861 := rs (se 3 (by rfl) ⟨4286, by rfl⟩) (B 8573 (by norm_num) ⟨4286, by rfl⟩ (by norm_num))
theorem R22877 : Reach 22877 := rs (se 3 (by rfl) ⟨4289, by rfl⟩) (B 8579 (by norm_num) ⟨4289, by rfl⟩ (by norm_num))
theorem R22901 : Reach 22901 := rs (se 5 (by rfl) ⟨1073, by rfl⟩) (B 2147 (by norm_num) ⟨1073, by rfl⟩ (by norm_num))
theorem R22909 : Reach 22909 := rs (se 3 (by rfl) ⟨4295, by rfl⟩) (B 8591 (by norm_num) ⟨4295, by rfl⟩ (by norm_num))
theorem R22925 : Reach 22925 := rs (se 3 (by rfl) ⟨4298, by rfl⟩) (B 8597 (by norm_num) ⟨4298, by rfl⟩ (by norm_num))
theorem R22933 : Reach 22933 := rs (se 6 (by rfl) ⟨537, by rfl⟩) (B 1075 (by norm_num) ⟨537, by rfl⟩ (by norm_num))
theorem R22949 : Reach 22949 := rs (se 4 (by rfl) ⟨2151, by rfl⟩) (B 4303 (by norm_num) ⟨2151, by rfl⟩ (by norm_num))
theorem R22973 : Reach 22973 := rs (se 3 (by rfl) ⟨4307, by rfl⟩) (B 8615 (by norm_num) ⟨4307, by rfl⟩ (by norm_num))
theorem R22997 : Reach 22997 := rs (se 7 (by rfl) ⟨269, by rfl⟩) (B 539 (by norm_num) ⟨269, by rfl⟩ (by norm_num))
theorem R55781 : Reach 55781 := rs (se 4 (by rfl) ⟨5229, by rfl⟩) (B 10459 (by norm_num) ⟨5229, by rfl⟩ (by norm_num))
theorem R23021 : Reach 23021 := rs (se 3 (by rfl) ⟨4316, by rfl⟩) (B 8633 (by norm_num) ⟨4316, by rfl⟩ (by norm_num))
theorem R23045 : Reach 23045 := rs (se 4 (by rfl) ⟨2160, by rfl⟩) (B 4321 (by norm_num) ⟨2160, by rfl⟩ (by norm_num))
theorem R55829 : Reach 55829 := rs (se 6 (by rfl) ⟨1308, by rfl⟩) (B 2617 (by norm_num) ⟨1308, by rfl⟩ (by norm_num))
theorem R23069 : Reach 23069 := rs (se 3 (by rfl) ⟨4325, by rfl⟩) (B 8651 (by norm_num) ⟨4325, by rfl⟩ (by norm_num))
theorem R23093 : Reach 23093 := rs (se 5 (by rfl) ⟨1082, by rfl⟩) (B 2165 (by norm_num) ⟨1082, by rfl⟩ (by norm_num))
theorem R23117 : Reach 23117 := rs (se 3 (by rfl) ⟨4334, by rfl⟩) (B 8669 (by norm_num) ⟨4334, by rfl⟩ (by norm_num))
theorem R23125 : Reach 23125 := rs (se 8 (by rfl) ⟨135, by rfl⟩) (B 271 (by norm_num) ⟨135, by rfl⟩ (by norm_num))
theorem R23141 : Reach 23141 := rs (se 4 (by rfl) ⟨2169, by rfl⟩) (B 4339 (by norm_num) ⟨2169, by rfl⟩ (by norm_num))
theorem R23165 : Reach 23165 := rs (se 3 (by rfl) ⟨4343, by rfl⟩) (B 8687 (by norm_num) ⟨4343, by rfl⟩ (by norm_num))
theorem R23189 : Reach 23189 := rs (se 6 (by rfl) ⟨543, by rfl⟩) (B 1087 (by norm_num) ⟨543, by rfl⟩ (by norm_num))
theorem R23213 : Reach 23213 := rs (se 3 (by rfl) ⟨4352, by rfl⟩) (B 8705 (by norm_num) ⟨4352, by rfl⟩ (by norm_num))
theorem R23237 : Reach 23237 := rs (se 4 (by rfl) ⟨2178, by rfl⟩) (B 4357 (by norm_num) ⟨2178, by rfl⟩ (by norm_num))
theorem R23261 : Reach 23261 := rs (se 3 (by rfl) ⟨4361, by rfl⟩) (B 8723 (by norm_num) ⟨4361, by rfl⟩ (by norm_num))
theorem R23269 : Reach 23269 := rs (se 4 (by rfl) ⟨2181, by rfl⟩) (B 4363 (by norm_num) ⟨2181, by rfl⟩ (by norm_num))
theorem R23285 : Reach 23285 := rs (se 5 (by rfl) ⟨1091, by rfl⟩) (B 2183 (by norm_num) ⟨1091, by rfl⟩ (by norm_num))
theorem R23309 : Reach 23309 := rs (se 3 (by rfl) ⟨4370, by rfl⟩) (B 8741 (by norm_num) ⟨4370, by rfl⟩ (by norm_num))
theorem R23333 : Reach 23333 := rs (se 4 (by rfl) ⟨2187, by rfl⟩) (B 4375 (by norm_num) ⟨2187, by rfl⟩ (by norm_num))
theorem R23341 : Reach 23341 := rs (se 3 (by rfl) ⟨4376, by rfl⟩) (B 8753 (by norm_num) ⟨4376, by rfl⟩ (by norm_num))
theorem R23357 : Reach 23357 := rs (se 3 (by rfl) ⟨4379, by rfl⟩) (B 8759 (by norm_num) ⟨4379, by rfl⟩ (by norm_num))
theorem R23381 : Reach 23381 := rs (se 9 (by rfl) ⟨68, by rfl⟩) (B 137 (by norm_num) ⟨68, by rfl⟩ (by norm_num))
theorem R23405 : Reach 23405 := rs (se 3 (by rfl) ⟨4388, by rfl⟩) (B 8777 (by norm_num) ⟨4388, by rfl⟩ (by norm_num))
theorem R23429 : Reach 23429 := rs (se 4 (by rfl) ⟨2196, by rfl⟩) (B 4393 (by norm_num) ⟨2196, by rfl⟩ (by norm_num))
theorem R56213 : Reach 56213 := rs (se 6 (by rfl) ⟨1317, by rfl⟩) (B 2635 (by norm_num) ⟨1317, by rfl⟩ (by norm_num))
theorem R23453 : Reach 23453 := rs (se 3 (by rfl) ⟨4397, by rfl⟩) (B 8795 (by norm_num) ⟨4397, by rfl⟩ (by norm_num))
theorem R23477 : Reach 23477 := rs (se 5 (by rfl) ⟨1100, by rfl⟩) (B 2201 (by norm_num) ⟨1100, by rfl⟩ (by norm_num))
theorem R23485 : Reach 23485 := rs (se 3 (by rfl) ⟨4403, by rfl⟩) (B 8807 (by norm_num) ⟨4403, by rfl⟩ (by norm_num))
theorem R23501 : Reach 23501 := rs (se 3 (by rfl) ⟨4406, by rfl⟩) (B 8813 (by norm_num) ⟨4406, by rfl⟩ (by norm_num))
theorem R23525 : Reach 23525 := rs (se 4 (by rfl) ⟨2205, by rfl⟩) (B 4411 (by norm_num) ⟨2205, by rfl⟩ (by norm_num))
theorem R23549 : Reach 23549 := rs (se 3 (by rfl) ⟨4415, by rfl⟩) (B 8831 (by norm_num) ⟨4415, by rfl⟩ (by norm_num))
theorem R23557 : Reach 23557 := rs (se 4 (by rfl) ⟨2208, by rfl⟩) (B 4417 (by norm_num) ⟨2208, by rfl⟩ (by norm_num))
theorem R23573 : Reach 23573 := rs (se 6 (by rfl) ⟨552, by rfl⟩) (B 1105 (by norm_num) ⟨552, by rfl⟩ (by norm_num))
theorem R23581 : Reach 23581 := rs (se 3 (by rfl) ⟨4421, by rfl⟩) (B 8843 (by norm_num) ⟨4421, by rfl⟩ (by norm_num))
theorem R23597 : Reach 23597 := rs (se 3 (by rfl) ⟨4424, by rfl⟩) (B 8849 (by norm_num) ⟨4424, by rfl⟩ (by norm_num))
theorem R23621 : Reach 23621 := rs (se 4 (by rfl) ⟨2214, by rfl⟩) (B 4429 (by norm_num) ⟨2214, by rfl⟩ (by norm_num))
theorem R23645 : Reach 23645 := rs (se 3 (by rfl) ⟨4433, by rfl⟩) (B 8867 (by norm_num) ⟨4433, by rfl⟩ (by norm_num))
theorem R23653 : Reach 23653 := rs (se 4 (by rfl) ⟨2217, by rfl⟩) (B 4435 (by norm_num) ⟨2217, by rfl⟩ (by norm_num))
theorem R23669 : Reach 23669 := rs (se 5 (by rfl) ⟨1109, by rfl⟩) (B 2219 (by norm_num) ⟨1109, by rfl⟩ (by norm_num))
theorem R23693 : Reach 23693 := rs (se 3 (by rfl) ⟨4442, by rfl⟩) (B 8885 (by norm_num) ⟨4442, by rfl⟩ (by norm_num))
theorem R23701 : Reach 23701 := rs (se 6 (by rfl) ⟨555, by rfl⟩) (B 1111 (by norm_num) ⟨555, by rfl⟩ (by norm_num))
theorem R23717 : Reach 23717 := rs (se 4 (by rfl) ⟨2223, by rfl⟩) (B 4447 (by norm_num) ⟨2223, by rfl⟩ (by norm_num))
theorem R23741 : Reach 23741 := rs (se 3 (by rfl) ⟨4451, by rfl⟩) (B 8903 (by norm_num) ⟨4451, by rfl⟩ (by norm_num))
theorem R23765 : Reach 23765 := rs (se 7 (by rfl) ⟨278, by rfl⟩) (B 557 (by norm_num) ⟨278, by rfl⟩ (by norm_num))
theorem R23773 : Reach 23773 := rs (se 3 (by rfl) ⟨4457, by rfl⟩) (B 8915 (by norm_num) ⟨4457, by rfl⟩ (by norm_num))
theorem R23789 : Reach 23789 := rs (se 3 (by rfl) ⟨4460, by rfl⟩) (B 8921 (by norm_num) ⟨4460, by rfl⟩ (by norm_num))
theorem R23813 : Reach 23813 := rs (se 4 (by rfl) ⟨2232, by rfl⟩) (B 4465 (by norm_num) ⟨2232, by rfl⟩ (by norm_num))
theorem R23837 : Reach 23837 := rs (se 3 (by rfl) ⟨4469, by rfl⟩) (B 8939 (by norm_num) ⟨4469, by rfl⟩ (by norm_num))
theorem R23861 : Reach 23861 := rs (se 5 (by rfl) ⟨1118, by rfl⟩) (B 2237 (by norm_num) ⟨1118, by rfl⟩ (by norm_num))
theorem R56645 : Reach 56645 := rs (se 4 (by rfl) ⟨5310, by rfl⟩) (B 10621 (by norm_num) ⟨5310, by rfl⟩ (by norm_num))
theorem R23885 : Reach 23885 := rs (se 3 (by rfl) ⟨4478, by rfl⟩) (B 8957 (by norm_num) ⟨4478, by rfl⟩ (by norm_num))
theorem R23909 : Reach 23909 := rs (se 4 (by rfl) ⟨2241, by rfl⟩) (B 4483 (by norm_num) ⟨2241, by rfl⟩ (by norm_num))
theorem R23933 : Reach 23933 := rs (se 3 (by rfl) ⟨4487, by rfl⟩) (B 8975 (by norm_num) ⟨4487, by rfl⟩ (by norm_num))
theorem R23957 : Reach 23957 := rs (se 6 (by rfl) ⟨561, by rfl⟩) (B 1123 (by norm_num) ⟨561, by rfl⟩ (by norm_num))
theorem R23981 : Reach 23981 := rs (se 3 (by rfl) ⟨4496, by rfl⟩) (B 8993 (by norm_num) ⟨4496, by rfl⟩ (by norm_num))
theorem R23989 : Reach 23989 := rs (se 5 (by rfl) ⟨1124, by rfl⟩) (B 2249 (by norm_num) ⟨1124, by rfl⟩ (by norm_num))
theorem R24005 : Reach 24005 := rs (se 4 (by rfl) ⟨2250, by rfl⟩) (B 4501 (by norm_num) ⟨2250, by rfl⟩ (by norm_num))
theorem R24029 : Reach 24029 := rs (se 3 (by rfl) ⟨4505, by rfl⟩) (B 9011 (by norm_num) ⟨4505, by rfl⟩ (by norm_num))
theorem R24053 : Reach 24053 := rs (se 5 (by rfl) ⟨1127, by rfl⟩) (B 2255 (by norm_num) ⟨1127, by rfl⟩ (by norm_num))
theorem R56821 : Reach 56821 := rs (se 5 (by rfl) ⟨2663, by rfl⟩) (B 5327 (by norm_num) ⟨2663, by rfl⟩ (by norm_num))
theorem R24077 : Reach 24077 := rs (se 3 (by rfl) ⟨4514, by rfl⟩) (B 9029 (by norm_num) ⟨4514, by rfl⟩ (by norm_num))
theorem R24085 : Reach 24085 := rs (se 6 (by rfl) ⟨564, by rfl⟩) (B 1129 (by norm_num) ⟨564, by rfl⟩ (by norm_num))
theorem R24101 : Reach 24101 := rs (se 4 (by rfl) ⟨2259, by rfl⟩) (B 4519 (by norm_num) ⟨2259, by rfl⟩ (by norm_num))
theorem R24125 : Reach 24125 := rs (se 3 (by rfl) ⟨4523, by rfl⟩) (B 9047 (by norm_num) ⟨4523, by rfl⟩ (by norm_num))
theorem R24133 : Reach 24133 := rs (se 4 (by rfl) ⟨2262, by rfl⟩) (B 4525 (by norm_num) ⟨2262, by rfl⟩ (by norm_num))
theorem R24149 : Reach 24149 := rs (se 8 (by rfl) ⟨141, by rfl⟩) (B 283 (by norm_num) ⟨141, by rfl⟩ (by norm_num))
theorem R24173 : Reach 24173 := rs (se 3 (by rfl) ⟨4532, by rfl⟩) (B 9065 (by norm_num) ⟨4532, by rfl⟩ (by norm_num))
theorem R24181 : Reach 24181 := rs (se 5 (by rfl) ⟨1133, by rfl⟩) (B 2267 (by norm_num) ⟨1133, by rfl⟩ (by norm_num))
theorem R24197 : Reach 24197 := rs (se 4 (by rfl) ⟨2268, by rfl⟩) (B 4537 (by norm_num) ⟨2268, by rfl⟩ (by norm_num))
theorem R24205 : Reach 24205 := rs (se 3 (by rfl) ⟨4538, by rfl⟩) (B 9077 (by norm_num) ⟨4538, by rfl⟩ (by norm_num))
theorem R24221 : Reach 24221 := rs (se 3 (by rfl) ⟨4541, by rfl⟩) (B 9083 (by norm_num) ⟨4541, by rfl⟩ (by norm_num))
theorem R24229 : Reach 24229 := rs (se 4 (by rfl) ⟨2271, by rfl⟩) (B 4543 (by norm_num) ⟨2271, by rfl⟩ (by norm_num))
theorem R24245 : Reach 24245 := rs (se 5 (by rfl) ⟨1136, by rfl⟩) (B 2273 (by norm_num) ⟨1136, by rfl⟩ (by norm_num))
theorem R24269 : Reach 24269 := rs (se 3 (by rfl) ⟨4550, by rfl⟩) (B 9101 (by norm_num) ⟨4550, by rfl⟩ (by norm_num))
theorem R24293 : Reach 24293 := rs (se 4 (by rfl) ⟨2277, by rfl⟩) (B 4555 (by norm_num) ⟨2277, by rfl⟩ (by norm_num))
theorem R57077 : Reach 57077 := rs (se 5 (by rfl) ⟨2675, by rfl⟩) (B 5351 (by norm_num) ⟨2675, by rfl⟩ (by norm_num))
theorem R24317 : Reach 24317 := rs (se 3 (by rfl) ⟨4559, by rfl⟩) (B 9119 (by norm_num) ⟨4559, by rfl⟩ (by norm_num))
theorem R24341 : Reach 24341 := rs (se 6 (by rfl) ⟨570, by rfl⟩) (B 1141 (by norm_num) ⟨570, by rfl⟩ (by norm_num))
theorem R24365 : Reach 24365 := rs (se 3 (by rfl) ⟨4568, by rfl⟩) (B 9137 (by norm_num) ⟨4568, by rfl⟩ (by norm_num))
theorem R89909 : Reach 89909 := rs (se 5 (by rfl) ⟨4214, by rfl⟩) (B 8429 (by norm_num) ⟨4214, by rfl⟩ (by norm_num))
theorem R24389 : Reach 24389 := rs (se 4 (by rfl) ⟨2286, by rfl⟩) (B 4573 (by norm_num) ⟨2286, by rfl⟩ (by norm_num))
theorem R24413 : Reach 24413 := rs (se 3 (by rfl) ⟨4577, by rfl⟩) (B 9155 (by norm_num) ⟨4577, by rfl⟩ (by norm_num))
theorem R24421 : Reach 24421 := rs (se 4 (by rfl) ⟨2289, by rfl⟩) (B 4579 (by norm_num) ⟨2289, by rfl⟩ (by norm_num))
theorem R24437 : Reach 24437 := rs (se 5 (by rfl) ⟨1145, by rfl⟩) (B 2291 (by norm_num) ⟨1145, by rfl⟩ (by norm_num))
theorem R24461 : Reach 24461 := rs (se 3 (by rfl) ⟨4586, by rfl⟩) (B 9173 (by norm_num) ⟨4586, by rfl⟩ (by norm_num))
theorem R24485 : Reach 24485 := rs (se 4 (by rfl) ⟨2295, by rfl⟩) (B 4591 (by norm_num) ⟨2295, by rfl⟩ (by norm_num))
theorem R24509 : Reach 24509 := rs (se 3 (by rfl) ⟨4595, by rfl⟩) (B 9191 (by norm_num) ⟨4595, by rfl⟩ (by norm_num))
theorem R24533 : Reach 24533 := rs (se 7 (by rfl) ⟨287, by rfl⟩) (B 575 (by norm_num) ⟨287, by rfl⟩ (by norm_num))
theorem R24557 : Reach 24557 := rs (se 3 (by rfl) ⟨4604, by rfl⟩) (B 9209 (by norm_num) ⟨4604, by rfl⟩ (by norm_num))
theorem R24581 : Reach 24581 := rs (se 4 (by rfl) ⟨2304, by rfl⟩) (B 4609 (by norm_num) ⟨2304, by rfl⟩ (by norm_num))
theorem R24605 : Reach 24605 := rs (se 3 (by rfl) ⟨4613, by rfl⟩) (B 9227 (by norm_num) ⟨4613, by rfl⟩ (by norm_num))
theorem R24629 : Reach 24629 := rs (se 5 (by rfl) ⟨1154, by rfl⟩) (B 2309 (by norm_num) ⟨1154, by rfl⟩ (by norm_num))
theorem R24637 : Reach 24637 := rs (se 3 (by rfl) ⟨4619, by rfl⟩) (B 9239 (by norm_num) ⟨4619, by rfl⟩ (by norm_num))
theorem R24653 : Reach 24653 := rs (se 3 (by rfl) ⟨4622, by rfl⟩) (B 9245 (by norm_num) ⟨4622, by rfl⟩ (by norm_num))
theorem R24661 : Reach 24661 := rs (se 8 (by rfl) ⟨144, by rfl⟩) (B 289 (by norm_num) ⟨144, by rfl⟩ (by norm_num))
theorem R24677 : Reach 24677 := rs (se 4 (by rfl) ⟨2313, by rfl⟩) (B 4627 (by norm_num) ⟨2313, by rfl⟩ (by norm_num))
theorem R24701 : Reach 24701 := rs (se 3 (by rfl) ⟨4631, by rfl⟩) (B 9263 (by norm_num) ⟨4631, by rfl⟩ (by norm_num))
theorem R24725 : Reach 24725 := rs (se 6 (by rfl) ⟨579, by rfl⟩) (B 1159 (by norm_num) ⟨579, by rfl⟩ (by norm_num))
theorem R57509 : Reach 57509 := rs (se 4 (by rfl) ⟨5391, by rfl⟩) (B 10783 (by norm_num) ⟨5391, by rfl⟩ (by norm_num))
theorem R24749 : Reach 24749 := rs (se 3 (by rfl) ⟨4640, by rfl⟩) (B 9281 (by norm_num) ⟨4640, by rfl⟩ (by norm_num))
theorem R24773 : Reach 24773 := rs (se 4 (by rfl) ⟨2322, by rfl⟩) (B 4645 (by norm_num) ⟨2322, by rfl⟩ (by norm_num))
theorem R24781 : Reach 24781 := rs (se 3 (by rfl) ⟨4646, by rfl⟩) (B 9293 (by norm_num) ⟨4646, by rfl⟩ (by norm_num))
theorem R24797 : Reach 24797 := rs (se 3 (by rfl) ⟨4649, by rfl⟩) (B 9299 (by norm_num) ⟨4649, by rfl⟩ (by norm_num))
theorem R24821 : Reach 24821 := rs (se 5 (by rfl) ⟨1163, by rfl⟩) (B 2327 (by norm_num) ⟨1163, by rfl⟩ (by norm_num))
theorem R24845 : Reach 24845 := rs (se 3 (by rfl) ⟨4658, by rfl⟩) (B 9317 (by norm_num) ⟨4658, by rfl⟩ (by norm_num))
theorem R24853 : Reach 24853 := rs (se 6 (by rfl) ⟨582, by rfl⟩) (B 1165 (by norm_num) ⟨582, by rfl⟩ (by norm_num))
theorem R24869 : Reach 24869 := rs (se 4 (by rfl) ⟨2331, by rfl⟩) (B 4663 (by norm_num) ⟨2331, by rfl⟩ (by norm_num))
theorem R24877 : Reach 24877 := rs (se 3 (by rfl) ⟨4664, by rfl⟩) (B 9329 (by norm_num) ⟨4664, by rfl⟩ (by norm_num))
theorem R24893 : Reach 24893 := rs (se 3 (by rfl) ⟨4667, by rfl⟩) (B 9335 (by norm_num) ⟨4667, by rfl⟩ (by norm_num))
theorem R24917 : Reach 24917 := rs (se 10 (by rfl) ⟨36, by rfl⟩) (B 73 (by norm_num) ⟨36, by rfl⟩ (by norm_num))
theorem R24941 : Reach 24941 := rs (se 3 (by rfl) ⟨4676, by rfl⟩) (B 9353 (by norm_num) ⟨4676, by rfl⟩ (by norm_num))
theorem R24965 : Reach 24965 := rs (se 4 (by rfl) ⟨2340, by rfl⟩) (B 4681 (by norm_num) ⟨2340, by rfl⟩ (by norm_num))
theorem R24989 : Reach 24989 := rs (se 3 (by rfl) ⟨4685, by rfl⟩) (B 9371 (by norm_num) ⟨4685, by rfl⟩ (by norm_num))
theorem R57781 : Reach 57781 := rs (se 5 (by rfl) ⟨2708, by rfl⟩) (B 5417 (by norm_num) ⟨2708, by rfl⟩ (by norm_num))
theorem R25013 : Reach 25013 := rs (se 5 (by rfl) ⟨1172, by rfl⟩) (B 2345 (by norm_num) ⟨1172, by rfl⟩ (by norm_num))
theorem R57797 : Reach 57797 := rs (se 4 (by rfl) ⟨5418, by rfl⟩) (B 10837 (by norm_num) ⟨5418, by rfl⟩ (by norm_num))
theorem R25037 : Reach 25037 := rs (se 3 (by rfl) ⟨4694, by rfl⟩) (B 9389 (by norm_num) ⟨4694, by rfl⟩ (by norm_num))
theorem R25061 : Reach 25061 := rs (se 4 (by rfl) ⟨2349, by rfl⟩) (B 4699 (by norm_num) ⟨2349, by rfl⟩ (by norm_num))
theorem R25069 : Reach 25069 := rs (se 3 (by rfl) ⟨4700, by rfl⟩) (B 9401 (by norm_num) ⟨4700, by rfl⟩ (by norm_num))
theorem R25085 : Reach 25085 := rs (se 3 (by rfl) ⟨4703, by rfl⟩) (B 9407 (by norm_num) ⟨4703, by rfl⟩ (by norm_num))
theorem R25109 : Reach 25109 := rs (se 6 (by rfl) ⟨588, by rfl⟩) (B 1177 (by norm_num) ⟨588, by rfl⟩ (by norm_num))
theorem R221717 : Reach 221717 := rs (se 6 (by rfl) ⟨5196, by rfl⟩) (B 10393 (by norm_num) ⟨5196, by rfl⟩ (by norm_num))
theorem R25133 : Reach 25133 := rs (se 3 (by rfl) ⟨4712, by rfl⟩) (B 9425 (by norm_num) ⟨4712, by rfl⟩ (by norm_num))
theorem R25157 : Reach 25157 := rs (se 4 (by rfl) ⟨2358, by rfl⟩) (B 4717 (by norm_num) ⟨2358, by rfl⟩ (by norm_num))
theorem R57941 : Reach 57941 := rs (se 8 (by rfl) ⟨339, by rfl⟩) (B 679 (by norm_num) ⟨339, by rfl⟩ (by norm_num))
theorem R25181 : Reach 25181 := rs (se 3 (by rfl) ⟨4721, by rfl⟩) (B 9443 (by norm_num) ⟨4721, by rfl⟩ (by norm_num))
theorem R25205 : Reach 25205 := rs (se 5 (by rfl) ⟨1181, by rfl⟩) (B 2363 (by norm_num) ⟨1181, by rfl⟩ (by norm_num))
theorem R25229 : Reach 25229 := rs (se 3 (by rfl) ⟨4730, by rfl⟩) (B 9461 (by norm_num) ⟨4730, by rfl⟩ (by norm_num))
theorem R25253 : Reach 25253 := rs (se 4 (by rfl) ⟨2367, by rfl⟩) (B 4735 (by norm_num) ⟨2367, by rfl⟩ (by norm_num))
theorem R25277 : Reach 25277 := rs (se 3 (by rfl) ⟨4739, by rfl⟩) (B 9479 (by norm_num) ⟨4739, by rfl⟩ (by norm_num))
theorem R25285 : Reach 25285 := rs (se 4 (by rfl) ⟨2370, by rfl⟩) (B 4741 (by norm_num) ⟨2370, by rfl⟩ (by norm_num))
theorem R25301 : Reach 25301 := rs (se 7 (by rfl) ⟨296, by rfl⟩) (B 593 (by norm_num) ⟨296, by rfl⟩ (by norm_num))
theorem R25325 : Reach 25325 := rs (se 3 (by rfl) ⟨4748, by rfl⟩) (B 9497 (by norm_num) ⟨4748, by rfl⟩ (by norm_num))
theorem R25349 : Reach 25349 := rs (se 4 (by rfl) ⟨2376, by rfl⟩) (B 4753 (by norm_num) ⟨2376, by rfl⟩ (by norm_num))
theorem R25373 : Reach 25373 := rs (se 3 (by rfl) ⟨4757, by rfl⟩) (B 9515 (by norm_num) ⟨4757, by rfl⟩ (by norm_num))
theorem R25397 : Reach 25397 := rs (se 5 (by rfl) ⟨1190, by rfl⟩) (B 2381 (by norm_num) ⟨1190, by rfl⟩ (by norm_num))
theorem R25421 : Reach 25421 := rs (se 3 (by rfl) ⟨4766, by rfl⟩) (B 9533 (by norm_num) ⟨4766, by rfl⟩ (by norm_num))
theorem R25445 : Reach 25445 := rs (se 4 (by rfl) ⟨2385, by rfl⟩) (B 4771 (by norm_num) ⟨2385, by rfl⟩ (by norm_num))
theorem R58229 : Reach 58229 := rs (se 5 (by rfl) ⟨2729, by rfl⟩) (B 5459 (by norm_num) ⟨2729, by rfl⟩ (by norm_num))
theorem R25469 : Reach 25469 := rs (se 3 (by rfl) ⟨4775, by rfl⟩) (B 9551 (by norm_num) ⟨4775, by rfl⟩ (by norm_num))
theorem R25493 : Reach 25493 := rs (se 6 (by rfl) ⟨597, by rfl⟩) (B 1195 (by norm_num) ⟨597, by rfl⟩ (by norm_num))
theorem R25501 : Reach 25501 := rs (se 3 (by rfl) ⟨4781, by rfl⟩) (B 9563 (by norm_num) ⟨4781, by rfl⟩ (by norm_num))
theorem R25517 : Reach 25517 := rs (se 3 (by rfl) ⟨4784, by rfl⟩) (B 9569 (by norm_num) ⟨4784, by rfl⟩ (by norm_num))
theorem R25541 : Reach 25541 := rs (se 4 (by rfl) ⟨2394, by rfl⟩) (B 4789 (by norm_num) ⟨2394, by rfl⟩ (by norm_num))
theorem R25565 : Reach 25565 := rs (se 3 (by rfl) ⟨4793, by rfl⟩) (B 9587 (by norm_num) ⟨4793, by rfl⟩ (by norm_num))
theorem R25589 : Reach 25589 := rs (se 5 (by rfl) ⟨1199, by rfl⟩) (B 2399 (by norm_num) ⟨1199, by rfl⟩ (by norm_num))
theorem R58373 : Reach 58373 := rs (se 4 (by rfl) ⟨5472, by rfl⟩) (B 10945 (by norm_num) ⟨5472, by rfl⟩ (by norm_num))
theorem R25613 : Reach 25613 := rs (se 3 (by rfl) ⟨4802, by rfl⟩) (B 9605 (by norm_num) ⟨4802, by rfl⟩ (by norm_num))
theorem R25637 : Reach 25637 := rs (se 4 (by rfl) ⟨2403, by rfl⟩) (B 4807 (by norm_num) ⟨2403, by rfl⟩ (by norm_num))
theorem R25661 : Reach 25661 := rs (se 3 (by rfl) ⟨4811, by rfl⟩) (B 9623 (by norm_num) ⟨4811, by rfl⟩ (by norm_num))
theorem R25685 : Reach 25685 := rs (se 8 (by rfl) ⟨150, by rfl⟩) (B 301 (by norm_num) ⟨150, by rfl⟩ (by norm_num))
theorem R25709 : Reach 25709 := rs (se 3 (by rfl) ⟨4820, by rfl⟩) (B 9641 (by norm_num) ⟨4820, by rfl⟩ (by norm_num))
theorem R25717 : Reach 25717 := rs (se 5 (by rfl) ⟨1205, by rfl⟩) (B 2411 (by norm_num) ⟨1205, by rfl⟩ (by norm_num))
theorem R25733 : Reach 25733 := rs (se 4 (by rfl) ⟨2412, by rfl⟩) (B 4825 (by norm_num) ⟨2412, by rfl⟩ (by norm_num))
theorem R25757 : Reach 25757 := rs (se 3 (by rfl) ⟨4829, by rfl⟩) (B 9659 (by norm_num) ⟨4829, by rfl⟩ (by norm_num))
theorem R25781 : Reach 25781 := rs (se 5 (by rfl) ⟨1208, by rfl⟩) (B 2417 (by norm_num) ⟨1208, by rfl⟩ (by norm_num))
theorem R25805 : Reach 25805 := rs (se 3 (by rfl) ⟨4838, by rfl⟩) (B 9677 (by norm_num) ⟨4838, by rfl⟩ (by norm_num))
theorem R25829 : Reach 25829 := rs (se 4 (by rfl) ⟨2421, by rfl⟩) (B 4843 (by norm_num) ⟨2421, by rfl⟩ (by norm_num))
theorem R25853 : Reach 25853 := rs (se 3 (by rfl) ⟨4847, by rfl⟩) (B 9695 (by norm_num) ⟨4847, by rfl⟩ (by norm_num))
theorem R25861 : Reach 25861 := rs (se 4 (by rfl) ⟨2424, by rfl⟩) (B 4849 (by norm_num) ⟨2424, by rfl⟩ (by norm_num))
theorem R25877 : Reach 25877 := rs (se 6 (by rfl) ⟨606, by rfl⟩) (B 1213 (by norm_num) ⟨606, by rfl⟩ (by norm_num))
theorem R25901 : Reach 25901 := rs (se 3 (by rfl) ⟨4856, by rfl⟩) (B 9713 (by norm_num) ⟨4856, by rfl⟩ (by norm_num))
theorem R25925 : Reach 25925 := rs (se 4 (by rfl) ⟨2430, by rfl⟩) (B 4861 (by norm_num) ⟨2430, by rfl⟩ (by norm_num))
theorem R25933 : Reach 25933 := rs (se 3 (by rfl) ⟨4862, by rfl⟩) (B 9725 (by norm_num) ⟨4862, by rfl⟩ (by norm_num))
theorem R25949 : Reach 25949 := rs (se 3 (by rfl) ⟨4865, by rfl⟩) (B 9731 (by norm_num) ⟨4865, by rfl⟩ (by norm_num))
theorem R25973 : Reach 25973 := rs (se 5 (by rfl) ⟨1217, by rfl⟩) (B 2435 (by norm_num) ⟨1217, by rfl⟩ (by norm_num))
theorem R25997 : Reach 25997 := rs (se 3 (by rfl) ⟨4874, by rfl⟩) (B 9749 (by norm_num) ⟨4874, by rfl⟩ (by norm_num))
theorem R26021 : Reach 26021 := rs (se 4 (by rfl) ⟨2439, by rfl⟩) (B 4879 (by norm_num) ⟨2439, by rfl⟩ (by norm_num))
theorem R58805 : Reach 58805 := rs (se 5 (by rfl) ⟨2756, by rfl⟩) (B 5513 (by norm_num) ⟨2756, by rfl⟩ (by norm_num))
theorem R26045 : Reach 26045 := rs (se 3 (by rfl) ⟨4883, by rfl⟩) (B 9767 (by norm_num) ⟨4883, by rfl⟩ (by norm_num))
theorem R26069 : Reach 26069 := rs (se 7 (by rfl) ⟨305, by rfl⟩) (B 611 (by norm_num) ⟨305, by rfl⟩ (by norm_num))
theorem R26077 : Reach 26077 := rs (se 3 (by rfl) ⟨4889, by rfl⟩) (B 9779 (by norm_num) ⟨4889, by rfl⟩ (by norm_num))
theorem R26093 : Reach 26093 := rs (se 3 (by rfl) ⟨4892, by rfl⟩) (B 9785 (by norm_num) ⟨4892, by rfl⟩ (by norm_num))
theorem R26117 : Reach 26117 := rs (se 4 (by rfl) ⟨2448, by rfl⟩) (B 4897 (by norm_num) ⟨2448, by rfl⟩ (by norm_num))
theorem R26141 : Reach 26141 := rs (se 3 (by rfl) ⟨4901, by rfl⟩) (B 9803 (by norm_num) ⟨4901, by rfl⟩ (by norm_num))
theorem R26149 : Reach 26149 := rs (se 4 (by rfl) ⟨2451, by rfl⟩) (B 4903 (by norm_num) ⟨2451, by rfl⟩ (by norm_num))
theorem R26165 : Reach 26165 := rs (se 5 (by rfl) ⟨1226, by rfl⟩) (B 2453 (by norm_num) ⟨1226, by rfl⟩ (by norm_num))
theorem R26189 : Reach 26189 := rs (se 3 (by rfl) ⟨4910, by rfl⟩) (B 9821 (by norm_num) ⟨4910, by rfl⟩ (by norm_num))
theorem R58981 : Reach 58981 := rs (se 4 (by rfl) ⟨5529, by rfl⟩) (B 11059 (by norm_num) ⟨5529, by rfl⟩ (by norm_num))
theorem R26213 : Reach 26213 := rs (se 4 (by rfl) ⟨2457, by rfl⟩) (B 4915 (by norm_num) ⟨2457, by rfl⟩ (by norm_num))
theorem R26237 : Reach 26237 := rs (se 3 (by rfl) ⟨4919, by rfl⟩) (B 9839 (by norm_num) ⟨4919, by rfl⟩ (by norm_num))
theorem R26261 : Reach 26261 := rs (se 6 (by rfl) ⟨615, by rfl⟩) (B 1231 (by norm_num) ⟨615, by rfl⟩ (by norm_num))
theorem R26285 : Reach 26285 := rs (se 3 (by rfl) ⟨4928, by rfl⟩) (B 9857 (by norm_num) ⟨4928, by rfl⟩ (by norm_num))
theorem R26309 : Reach 26309 := rs (se 4 (by rfl) ⟨2466, by rfl⟩) (B 4933 (by norm_num) ⟨2466, by rfl⟩ (by norm_num))
theorem R26333 : Reach 26333 := rs (se 3 (by rfl) ⟨4937, by rfl⟩) (B 9875 (by norm_num) ⟨4937, by rfl⟩ (by norm_num))
theorem R26357 : Reach 26357 := rs (se 5 (by rfl) ⟨1235, by rfl⟩) (B 2471 (by norm_num) ⟨1235, by rfl⟩ (by norm_num))
theorem R26365 : Reach 26365 := rs (se 3 (by rfl) ⟨4943, by rfl⟩) (B 9887 (by norm_num) ⟨4943, by rfl⟩ (by norm_num))
theorem R26381 : Reach 26381 := rs (se 3 (by rfl) ⟨4946, by rfl⟩) (B 9893 (by norm_num) ⟨4946, by rfl⟩ (by norm_num))
theorem R26405 : Reach 26405 := rs (se 4 (by rfl) ⟨2475, by rfl⟩) (B 4951 (by norm_num) ⟨2475, by rfl⟩ (by norm_num))
theorem R91957 : Reach 91957 := rs (se 5 (by rfl) ⟨4310, by rfl⟩) (B 8621 (by norm_num) ⟨4310, by rfl⟩ (by norm_num))
theorem R26429 : Reach 26429 := rs (se 3 (by rfl) ⟨4955, by rfl⟩) (B 9911 (by norm_num) ⟨4955, by rfl⟩ (by norm_num))
theorem R26453 : Reach 26453 := rs (se 9 (by rfl) ⟨77, by rfl⟩) (B 155 (by norm_num) ⟨77, by rfl⟩ (by norm_num))
theorem R59237 : Reach 59237 := rs (se 4 (by rfl) ⟨5553, by rfl⟩) (B 11107 (by norm_num) ⟨5553, by rfl⟩ (by norm_num))
theorem R26477 : Reach 26477 := rs (se 3 (by rfl) ⟨4964, by rfl⟩) (B 9929 (by norm_num) ⟨4964, by rfl⟩ (by norm_num))
theorem R26501 : Reach 26501 := rs (se 4 (by rfl) ⟨2484, by rfl⟩) (B 4969 (by norm_num) ⟨2484, by rfl⟩ (by norm_num))
theorem R26525 : Reach 26525 := rs (se 3 (by rfl) ⟨4973, by rfl⟩) (B 9947 (by norm_num) ⟨4973, by rfl⟩ (by norm_num))
theorem R26549 : Reach 26549 := rs (se 5 (by rfl) ⟨1244, by rfl⟩) (B 2489 (by norm_num) ⟨1244, by rfl⟩ (by norm_num))
theorem R26573 : Reach 26573 := rs (se 3 (by rfl) ⟨4982, by rfl⟩) (B 9965 (by norm_num) ⟨4982, by rfl⟩ (by norm_num))
theorem R26581 : Reach 26581 := rs (se 7 (by rfl) ⟨311, by rfl⟩) (B 623 (by norm_num) ⟨311, by rfl⟩ (by norm_num))
theorem R26597 : Reach 26597 := rs (se 4 (by rfl) ⟨2493, by rfl⟩) (B 4987 (by norm_num) ⟨2493, by rfl⟩ (by norm_num))
theorem R26621 : Reach 26621 := rs (se 3 (by rfl) ⟨4991, by rfl⟩) (B 9983 (by norm_num) ⟨4991, by rfl⟩ (by norm_num))
theorem R59413 : Reach 59413 := rs (se 6 (by rfl) ⟨1392, by rfl⟩) (B 2785 (by norm_num) ⟨1392, by rfl⟩ (by norm_num))
theorem R26645 : Reach 26645 := rs (se 6 (by rfl) ⟨624, by rfl⟩) (B 1249 (by norm_num) ⟨624, by rfl⟩ (by norm_num))
theorem R26669 : Reach 26669 := rs (se 3 (by rfl) ⟨5000, by rfl⟩) (B 10001 (by norm_num) ⟨5000, by rfl⟩ (by norm_num))
theorem R26677 : Reach 26677 := rs (se 5 (by rfl) ⟨1250, by rfl⟩) (B 2501 (by norm_num) ⟨1250, by rfl⟩ (by norm_num))
theorem R26693 : Reach 26693 := rs (se 4 (by rfl) ⟨2502, by rfl⟩) (B 5005 (by norm_num) ⟨2502, by rfl⟩ (by norm_num))
theorem R26717 : Reach 26717 := rs (se 3 (by rfl) ⟨5009, by rfl⟩) (B 10019 (by norm_num) ⟨5009, by rfl⟩ (by norm_num))
theorem R26741 : Reach 26741 := rs (se 5 (by rfl) ⟨1253, by rfl⟩) (B 2507 (by norm_num) ⟨1253, by rfl⟩ (by norm_num))
theorem R26765 : Reach 26765 := rs (se 3 (by rfl) ⟨5018, by rfl⟩) (B 10037 (by norm_num) ⟨5018, by rfl⟩ (by norm_num))
theorem R125077 : Reach 125077 := rs (se 6 (by rfl) ⟨2931, by rfl⟩) (B 5863 (by norm_num) ⟨2931, by rfl⟩ (by norm_num))
theorem R26789 : Reach 26789 := rs (se 4 (by rfl) ⟨2511, by rfl⟩) (B 5023 (by norm_num) ⟨2511, by rfl⟩ (by norm_num))
theorem R26797 : Reach 26797 := rs (se 3 (by rfl) ⟨5024, by rfl⟩) (B 10049 (by norm_num) ⟨5024, by rfl⟩ (by norm_num))
theorem R26813 : Reach 26813 := rs (se 3 (by rfl) ⟨5027, by rfl⟩) (B 10055 (by norm_num) ⟨5027, by rfl⟩ (by norm_num))
theorem R26821 : Reach 26821 := rs (se 4 (by rfl) ⟨2514, by rfl⟩) (B 5029 (by norm_num) ⟨2514, by rfl⟩ (by norm_num))
theorem R26837 : Reach 26837 := rs (se 7 (by rfl) ⟨314, by rfl⟩) (B 629 (by norm_num) ⟨314, by rfl⟩ (by norm_num))
theorem R26861 : Reach 26861 := rs (se 3 (by rfl) ⟨5036, by rfl⟩) (B 10073 (by norm_num) ⟨5036, by rfl⟩ (by norm_num))
theorem R26885 : Reach 26885 := rs (se 4 (by rfl) ⟨2520, by rfl⟩) (B 5041 (by norm_num) ⟨2520, by rfl⟩ (by norm_num))
theorem R59669 : Reach 59669 := rs (se 6 (by rfl) ⟨1398, by rfl⟩) (B 2797 (by norm_num) ⟨1398, by rfl⟩ (by norm_num))
theorem R26909 : Reach 26909 := rs (se 3 (by rfl) ⟨5045, by rfl⟩) (B 10091 (by norm_num) ⟨5045, by rfl⟩ (by norm_num))
theorem R26933 : Reach 26933 := rs (se 5 (by rfl) ⟨1262, by rfl⟩) (B 2525 (by norm_num) ⟨1262, by rfl⟩ (by norm_num))
theorem R59717 : Reach 59717 := rs (se 4 (by rfl) ⟨5598, by rfl⟩) (B 11197 (by norm_num) ⟨5598, by rfl⟩ (by norm_num))
theorem R26957 : Reach 26957 := rs (se 3 (by rfl) ⟨5054, by rfl⟩) (B 10109 (by norm_num) ⟨5054, by rfl⟩ (by norm_num))
theorem R92501 : Reach 92501 := rs (se 10 (by rfl) ⟨135, by rfl⟩) (B 271 (by norm_num) ⟨135, by rfl⟩ (by norm_num))
theorem R26981 : Reach 26981 := rs (se 4 (by rfl) ⟨2529, by rfl⟩) (B 5059 (by norm_num) ⟨2529, by rfl⟩ (by norm_num))
theorem R27005 : Reach 27005 := rs (se 3 (by rfl) ⟨5063, by rfl⟩) (B 10127 (by norm_num) ⟨5063, by rfl⟩ (by norm_num))
theorem R27013 : Reach 27013 := rs (se 4 (by rfl) ⟨2532, by rfl⟩) (B 5065 (by norm_num) ⟨2532, by rfl⟩ (by norm_num))
theorem R27029 : Reach 27029 := rs (se 6 (by rfl) ⟨633, by rfl⟩) (B 1267 (by norm_num) ⟨633, by rfl⟩ (by norm_num))
theorem R27053 : Reach 27053 := rs (se 3 (by rfl) ⟨5072, by rfl⟩) (B 10145 (by norm_num) ⟨5072, by rfl⟩ (by norm_num))
theorem R27077 : Reach 27077 := rs (se 4 (by rfl) ⟨2538, by rfl⟩) (B 5077 (by norm_num) ⟨2538, by rfl⟩ (by norm_num))
theorem R27101 : Reach 27101 := rs (se 3 (by rfl) ⟨5081, by rfl⟩) (B 10163 (by norm_num) ⟨5081, by rfl⟩ (by norm_num))
theorem R27125 : Reach 27125 := rs (se 5 (by rfl) ⟨1271, by rfl⟩) (B 2543 (by norm_num) ⟨1271, by rfl⟩ (by norm_num))
theorem R27149 : Reach 27149 := rs (se 3 (by rfl) ⟨5090, by rfl⟩) (B 10181 (by norm_num) ⟨5090, by rfl⟩ (by norm_num))
theorem R190997 : Reach 190997 := rs (se 6 (by rfl) ⟨4476, by rfl⟩) (B 8953 (by norm_num) ⟨4476, by rfl⟩ (by norm_num))
theorem R27173 : Reach 27173 := rs (se 4 (by rfl) ⟨2547, by rfl⟩) (B 5095 (by norm_num) ⟨2547, by rfl⟩ (by norm_num))
theorem R27197 : Reach 27197 := rs (se 3 (by rfl) ⟨5099, by rfl⟩) (B 10199 (by norm_num) ⟨5099, by rfl⟩ (by norm_num))
theorem R27221 : Reach 27221 := rs (se 8 (by rfl) ⟨159, by rfl⟩) (B 319 (by norm_num) ⟨159, by rfl⟩ (by norm_num))
theorem R27229 : Reach 27229 := rs (se 3 (by rfl) ⟨5105, by rfl⟩) (B 10211 (by norm_num) ⟨5105, by rfl⟩ (by norm_num))
theorem R27245 : Reach 27245 := rs (se 3 (by rfl) ⟨5108, by rfl⟩) (B 10217 (by norm_num) ⟨5108, by rfl⟩ (by norm_num))
theorem R27269 : Reach 27269 := rs (se 4 (by rfl) ⟨2556, by rfl⟩) (B 5113 (by norm_num) ⟨2556, by rfl⟩ (by norm_num))
theorem R27293 : Reach 27293 := rs (se 3 (by rfl) ⟨5117, by rfl⟩) (B 10235 (by norm_num) ⟨5117, by rfl⟩ (by norm_num))
theorem R27317 : Reach 27317 := rs (se 5 (by rfl) ⟨1280, by rfl⟩) (B 2561 (by norm_num) ⟨1280, by rfl⟩ (by norm_num))
theorem R60101 : Reach 60101 := rs (se 4 (by rfl) ⟨5634, by rfl⟩) (B 11269 (by norm_num) ⟨5634, by rfl⟩ (by norm_num))
theorem R27341 : Reach 27341 := rs (se 3 (by rfl) ⟨5126, by rfl⟩) (B 10253 (by norm_num) ⟨5126, by rfl⟩ (by norm_num))
theorem R27365 : Reach 27365 := rs (se 4 (by rfl) ⟨2565, by rfl⟩) (B 5131 (by norm_num) ⟨2565, by rfl⟩ (by norm_num))
theorem R27389 : Reach 27389 := rs (se 3 (by rfl) ⟨5135, by rfl⟩) (B 10271 (by norm_num) ⟨5135, by rfl⟩ (by norm_num))
theorem R27413 : Reach 27413 := rs (se 6 (by rfl) ⟨642, by rfl⟩) (B 1285 (by norm_num) ⟨642, by rfl⟩ (by norm_num))
theorem R27437 : Reach 27437 := rs (se 3 (by rfl) ⟨5144, by rfl⟩) (B 10289 (by norm_num) ⟨5144, by rfl⟩ (by norm_num))
theorem R27445 : Reach 27445 := rs (se 5 (by rfl) ⟨1286, by rfl⟩) (B 2573 (by norm_num) ⟨1286, by rfl⟩ (by norm_num))
theorem R27461 : Reach 27461 := rs (se 4 (by rfl) ⟨2574, by rfl⟩) (B 5149 (by norm_num) ⟨2574, by rfl⟩ (by norm_num))
theorem R27469 : Reach 27469 := rs (se 3 (by rfl) ⟨5150, by rfl⟩) (B 10301 (by norm_num) ⟨5150, by rfl⟩ (by norm_num))
theorem R27485 : Reach 27485 := rs (se 3 (by rfl) ⟨5153, by rfl⟩) (B 10307 (by norm_num) ⟨5153, by rfl⟩ (by norm_num))
theorem R27509 : Reach 27509 := rs (se 5 (by rfl) ⟨1289, by rfl⟩) (B 2579 (by norm_num) ⟨1289, by rfl⟩ (by norm_num))
theorem R27533 : Reach 27533 := rs (se 3 (by rfl) ⟨5162, by rfl⟩) (B 10325 (by norm_num) ⟨5162, by rfl⟩ (by norm_num))
theorem R27557 : Reach 27557 := rs (se 4 (by rfl) ⟨2583, by rfl⟩) (B 5167 (by norm_num) ⟨2583, by rfl⟩ (by norm_num))
theorem R93109 : Reach 93109 := rs (se 5 (by rfl) ⟨4364, by rfl⟩) (B 8729 (by norm_num) ⟨4364, by rfl⟩ (by norm_num))
theorem R27581 : Reach 27581 := rs (se 3 (by rfl) ⟨5171, by rfl⟩) (B 10343 (by norm_num) ⟨5171, by rfl⟩ (by norm_num))
theorem R27605 : Reach 27605 := rs (se 7 (by rfl) ⟨323, by rfl⟩) (B 647 (by norm_num) ⟨323, by rfl⟩ (by norm_num))
theorem R27629 : Reach 27629 := rs (se 3 (by rfl) ⟨5180, by rfl⟩) (B 10361 (by norm_num) ⟨5180, by rfl⟩ (by norm_num))
theorem R27653 : Reach 27653 := rs (se 4 (by rfl) ⟨2592, by rfl⟩) (B 5185 (by norm_num) ⟨2592, by rfl⟩ (by norm_num))
theorem R27661 : Reach 27661 := rs (se 3 (by rfl) ⟨5186, by rfl⟩) (B 10373 (by norm_num) ⟨5186, by rfl⟩ (by norm_num))
theorem R27677 : Reach 27677 := rs (se 3 (by rfl) ⟨5189, by rfl⟩) (B 10379 (by norm_num) ⟨5189, by rfl⟩ (by norm_num))
theorem R27701 : Reach 27701 := rs (se 5 (by rfl) ⟨1298, by rfl⟩) (B 2597 (by norm_num) ⟨1298, by rfl⟩ (by norm_num))
theorem R27725 : Reach 27725 := rs (se 3 (by rfl) ⟨5198, by rfl⟩) (B 10397 (by norm_num) ⟨5198, by rfl⟩ (by norm_num))
theorem R27749 : Reach 27749 := rs (se 4 (by rfl) ⟨2601, by rfl⟩) (B 5203 (by norm_num) ⟨2601, by rfl⟩ (by norm_num))
theorem R60533 : Reach 60533 := rs (se 5 (by rfl) ⟨2837, by rfl⟩) (B 5675 (by norm_num) ⟨2837, by rfl⟩ (by norm_num))
theorem R27773 : Reach 27773 := rs (se 3 (by rfl) ⟨5207, by rfl⟩) (B 10415 (by norm_num) ⟨5207, by rfl⟩ (by norm_num))
theorem R27797 : Reach 27797 := rs (se 6 (by rfl) ⟨651, by rfl⟩) (B 1303 (by norm_num) ⟨651, by rfl⟩ (by norm_num))
theorem R27805 : Reach 27805 := rs (se 3 (by rfl) ⟨5213, by rfl⟩) (B 10427 (by norm_num) ⟨5213, by rfl⟩ (by norm_num))
theorem R27821 : Reach 27821 := rs (se 3 (by rfl) ⟨5216, by rfl⟩) (B 10433 (by norm_num) ⟨5216, by rfl⟩ (by norm_num))
theorem R27845 : Reach 27845 := rs (se 4 (by rfl) ⟨2610, by rfl⟩) (B 5221 (by norm_num) ⟨2610, by rfl⟩ (by norm_num))
theorem R27869 : Reach 27869 := rs (se 3 (by rfl) ⟨5225, by rfl⟩) (B 10451 (by norm_num) ⟨5225, by rfl⟩ (by norm_num))
theorem R27877 : Reach 27877 := rs (se 4 (by rfl) ⟨2613, by rfl⟩) (B 5227 (by norm_num) ⟨2613, by rfl⟩ (by norm_num))
theorem R27893 : Reach 27893 := rs (se 5 (by rfl) ⟨1307, by rfl⟩) (B 2615 (by norm_num) ⟨1307, by rfl⟩ (by norm_num))
theorem R27917 : Reach 27917 := rs (se 3 (by rfl) ⟨5234, by rfl⟩) (B 10469 (by norm_num) ⟨5234, by rfl⟩ (by norm_num))
theorem R27941 : Reach 27941 := rs (se 4 (by rfl) ⟨2619, by rfl⟩) (B 5239 (by norm_num) ⟨2619, by rfl⟩ (by norm_num))
theorem R27965 : Reach 27965 := rs (se 3 (by rfl) ⟨5243, by rfl⟩) (B 10487 (by norm_num) ⟨5243, by rfl⟩ (by norm_num))
theorem R27989 : Reach 27989 := rs (se 11 (by rfl) ⟨20, by rfl⟩) (B 41 (by norm_num) ⟨20, by rfl⟩ (by norm_num))
theorem R28013 : Reach 28013 := rs (se 3 (by rfl) ⟨5252, by rfl⟩) (B 10505 (by norm_num) ⟨5252, by rfl⟩ (by norm_num))
theorem R28021 : Reach 28021 := rs (se 5 (by rfl) ⟨1313, by rfl⟩) (B 2627 (by norm_num) ⟨1313, by rfl⟩ (by norm_num))
theorem R28037 : Reach 28037 := rs (se 4 (by rfl) ⟨2628, by rfl⟩) (B 5257 (by norm_num) ⟨2628, by rfl⟩ (by norm_num))
theorem R60821 : Reach 60821 := rs (se 6 (by rfl) ⟨1425, by rfl⟩) (B 2851 (by norm_num) ⟨1425, by rfl⟩ (by norm_num))
theorem R28061 : Reach 28061 := rs (se 3 (by rfl) ⟨5261, by rfl⟩) (B 10523 (by norm_num) ⟨5261, by rfl⟩ (by norm_num))
theorem R28085 : Reach 28085 := rs (se 5 (by rfl) ⟨1316, by rfl⟩) (B 2633 (by norm_num) ⟨1316, by rfl⟩ (by norm_num))
theorem R28093 : Reach 28093 := rs (se 3 (by rfl) ⟨5267, by rfl⟩) (B 10535 (by norm_num) ⟨5267, by rfl⟩ (by norm_num))
theorem R60869 : Reach 60869 := rs (se 4 (by rfl) ⟨5706, by rfl⟩) (B 11413 (by norm_num) ⟨5706, by rfl⟩ (by norm_num))
theorem R28109 : Reach 28109 := rs (se 3 (by rfl) ⟨5270, by rfl⟩) (B 10541 (by norm_num) ⟨5270, by rfl⟩ (by norm_num))
theorem R28133 : Reach 28133 := rs (se 4 (by rfl) ⟨2637, by rfl⟩) (B 5275 (by norm_num) ⟨2637, by rfl⟩ (by norm_num))
theorem R28157 : Reach 28157 := rs (se 3 (by rfl) ⟨5279, by rfl⟩) (B 10559 (by norm_num) ⟨5279, by rfl⟩ (by norm_num))
theorem R28181 : Reach 28181 := rs (se 6 (by rfl) ⟨660, by rfl⟩) (B 1321 (by norm_num) ⟨660, by rfl⟩ (by norm_num))
theorem R60965 : Reach 60965 := rs (se 4 (by rfl) ⟨5715, by rfl⟩) (B 11431 (by norm_num) ⟨5715, by rfl⟩ (by norm_num))
theorem R28205 : Reach 28205 := rs (se 3 (by rfl) ⟨5288, by rfl⟩) (B 10577 (by norm_num) ⟨5288, by rfl⟩ (by norm_num))
theorem R28229 : Reach 28229 := rs (se 4 (by rfl) ⟨2646, by rfl⟩) (B 5293 (by norm_num) ⟨2646, by rfl⟩ (by norm_num))
theorem R28253 : Reach 28253 := rs (se 3 (by rfl) ⟨5297, by rfl⟩) (B 10595 (by norm_num) ⟨5297, by rfl⟩ (by norm_num))
theorem R28277 : Reach 28277 := rs (se 5 (by rfl) ⟨1325, by rfl⟩) (B 2651 (by norm_num) ⟨1325, by rfl⟩ (by norm_num))
theorem R28301 : Reach 28301 := rs (se 3 (by rfl) ⟨5306, by rfl⟩) (B 10613 (by norm_num) ⟨5306, by rfl⟩ (by norm_num))
theorem R28309 : Reach 28309 := rs (se 6 (by rfl) ⟨663, by rfl⟩) (B 1327 (by norm_num) ⟨663, by rfl⟩ (by norm_num))
theorem R28325 : Reach 28325 := rs (se 4 (by rfl) ⟨2655, by rfl⟩) (B 5311 (by norm_num) ⟨2655, by rfl⟩ (by norm_num))
theorem R28349 : Reach 28349 := rs (se 3 (by rfl) ⟨5315, by rfl⟩) (B 10631 (by norm_num) ⟨5315, by rfl⟩ (by norm_num))
theorem R28373 : Reach 28373 := rs (se 7 (by rfl) ⟨332, by rfl⟩) (B 665 (by norm_num) ⟨332, by rfl⟩ (by norm_num))
theorem R28397 : Reach 28397 := rs (se 3 (by rfl) ⟨5324, by rfl⟩) (B 10649 (by norm_num) ⟨5324, by rfl⟩ (by norm_num))
theorem R28421 : Reach 28421 := rs (se 4 (by rfl) ⟨2664, by rfl⟩) (B 5329 (by norm_num) ⟨2664, by rfl⟩ (by norm_num))
theorem R28445 : Reach 28445 := rs (se 3 (by rfl) ⟨5333, by rfl⟩) (B 10667 (by norm_num) ⟨5333, by rfl⟩ (by norm_num))
theorem R28469 : Reach 28469 := rs (se 5 (by rfl) ⟨1334, by rfl⟩) (B 2669 (by norm_num) ⟨1334, by rfl⟩ (by norm_num))
theorem R28493 : Reach 28493 := rs (se 3 (by rfl) ⟨5342, by rfl⟩) (B 10685 (by norm_num) ⟨5342, by rfl⟩ (by norm_num))
theorem R28517 : Reach 28517 := rs (se 4 (by rfl) ⟨2673, by rfl⟩) (B 5347 (by norm_num) ⟨2673, by rfl⟩ (by norm_num))
theorem R28525 : Reach 28525 := rs (se 3 (by rfl) ⟨5348, by rfl⟩) (B 10697 (by norm_num) ⟨5348, by rfl⟩ (by norm_num))
theorem R28541 : Reach 28541 := rs (se 3 (by rfl) ⟨5351, by rfl⟩) (B 10703 (by norm_num) ⟨5351, by rfl⟩ (by norm_num))
theorem R28565 : Reach 28565 := rs (se 6 (by rfl) ⟨669, by rfl⟩) (B 1339 (by norm_num) ⟨669, by rfl⟩ (by norm_num))
theorem R28589 : Reach 28589 := rs (se 3 (by rfl) ⟨5360, by rfl⟩) (B 10721 (by norm_num) ⟨5360, by rfl⟩ (by norm_num))
theorem R28613 : Reach 28613 := rs (se 4 (by rfl) ⟨2682, by rfl⟩) (B 5365 (by norm_num) ⟨2682, by rfl⟩ (by norm_num))
theorem R61397 : Reach 61397 := rs (se 7 (by rfl) ⟨719, by rfl⟩) (B 1439 (by norm_num) ⟨719, by rfl⟩ (by norm_num))
theorem R28637 : Reach 28637 := rs (se 3 (by rfl) ⟨5369, by rfl⟩) (B 10739 (by norm_num) ⟨5369, by rfl⟩ (by norm_num))
theorem R28661 : Reach 28661 := rs (se 5 (by rfl) ⟨1343, by rfl⟩) (B 2687 (by norm_num) ⟨1343, by rfl⟩ (by norm_num))
theorem R28685 : Reach 28685 := rs (se 3 (by rfl) ⟨5378, by rfl⟩) (B 10757 (by norm_num) ⟨5378, by rfl⟩ (by norm_num))
theorem R28709 : Reach 28709 := rs (se 4 (by rfl) ⟨2691, by rfl⟩) (B 5383 (by norm_num) ⟨2691, by rfl⟩ (by norm_num))
theorem R28733 : Reach 28733 := rs (se 3 (by rfl) ⟨5387, by rfl⟩) (B 10775 (by norm_num) ⟨5387, by rfl⟩ (by norm_num))
theorem R28741 : Reach 28741 := rs (se 4 (by rfl) ⟨2694, by rfl⟩) (B 5389 (by norm_num) ⟨2694, by rfl⟩ (by norm_num))
theorem R28757 : Reach 28757 := rs (se 8 (by rfl) ⟨168, by rfl⟩) (B 337 (by norm_num) ⟨168, by rfl⟩ (by norm_num))
theorem R28765 : Reach 28765 := rs (se 3 (by rfl) ⟨5393, by rfl⟩) (B 10787 (by norm_num) ⟨5393, by rfl⟩ (by norm_num))
theorem R28781 : Reach 28781 := rs (se 3 (by rfl) ⟨5396, by rfl⟩) (B 10793 (by norm_num) ⟨5396, by rfl⟩ (by norm_num))
theorem R28805 : Reach 28805 := rs (se 4 (by rfl) ⟨2700, by rfl⟩) (B 5401 (by norm_num) ⟨2700, by rfl⟩ (by norm_num))
theorem R159893 : Reach 159893 := rs (se 6 (by rfl) ⟨3747, by rfl⟩) (B 7495 (by norm_num) ⟨3747, by rfl⟩ (by norm_num))
theorem R28829 : Reach 28829 := rs (se 3 (by rfl) ⟨5405, by rfl⟩) (B 10811 (by norm_num) ⟨5405, by rfl⟩ (by norm_num))
theorem R28853 : Reach 28853 := rs (se 5 (by rfl) ⟨1352, by rfl⟩) (B 2705 (by norm_num) ⟨1352, by rfl⟩ (by norm_num))
theorem R28877 : Reach 28877 := rs (se 3 (by rfl) ⟨5414, by rfl⟩) (B 10829 (by norm_num) ⟨5414, by rfl⟩ (by norm_num))
theorem R28901 : Reach 28901 := rs (se 4 (by rfl) ⟨2709, by rfl⟩) (B 5419 (by norm_num) ⟨2709, by rfl⟩ (by norm_num))
theorem R28925 : Reach 28925 := rs (se 3 (by rfl) ⟨5423, by rfl⟩) (B 10847 (by norm_num) ⟨5423, by rfl⟩ (by norm_num))
theorem R28949 : Reach 28949 := rs (se 6 (by rfl) ⟨678, by rfl⟩) (B 1357 (by norm_num) ⟨678, by rfl⟩ (by norm_num))
theorem R28957 : Reach 28957 := rs (se 3 (by rfl) ⟨5429, by rfl⟩) (B 10859 (by norm_num) ⟨5429, by rfl⟩ (by norm_num))
theorem R28973 : Reach 28973 := rs (se 3 (by rfl) ⟨5432, by rfl⟩) (B 10865 (by norm_num) ⟨5432, by rfl⟩ (by norm_num))
theorem R28997 : Reach 28997 := rs (se 4 (by rfl) ⟨2718, by rfl⟩) (B 5437 (by norm_num) ⟨2718, by rfl⟩ (by norm_num))
theorem R29021 : Reach 29021 := rs (se 3 (by rfl) ⟨5441, by rfl⟩) (B 10883 (by norm_num) ⟨5441, by rfl⟩ (by norm_num))
theorem R29045 : Reach 29045 := rs (se 5 (by rfl) ⟨1361, by rfl⟩) (B 2723 (by norm_num) ⟨1361, by rfl⟩ (by norm_num))
theorem R61829 : Reach 61829 := rs (se 4 (by rfl) ⟨5796, by rfl⟩) (B 11593 (by norm_num) ⟨5796, by rfl⟩ (by norm_num))
theorem R29069 : Reach 29069 := rs (se 3 (by rfl) ⟨5450, by rfl⟩) (B 10901 (by norm_num) ⟨5450, by rfl⟩ (by norm_num))
theorem R29093 : Reach 29093 := rs (se 4 (by rfl) ⟨2727, by rfl⟩) (B 5455 (by norm_num) ⟨2727, by rfl⟩ (by norm_num))
theorem R29117 : Reach 29117 := rs (se 3 (by rfl) ⟨5459, by rfl⟩) (B 10919 (by norm_num) ⟨5459, by rfl⟩ (by norm_num))
theorem R29141 : Reach 29141 := rs (se 7 (by rfl) ⟨341, by rfl⟩) (B 683 (by norm_num) ⟨341, by rfl⟩ (by norm_num))
theorem R29165 : Reach 29165 := rs (se 3 (by rfl) ⟨5468, by rfl⟩) (B 10937 (by norm_num) ⟨5468, by rfl⟩ (by norm_num))
theorem R29173 : Reach 29173 := rs (se 5 (by rfl) ⟨1367, by rfl⟩) (B 2735 (by norm_num) ⟨1367, by rfl⟩ (by norm_num))
theorem R94709 : Reach 94709 := rs (se 5 (by rfl) ⟨4439, by rfl⟩) (B 8879 (by norm_num) ⟨4439, by rfl⟩ (by norm_num))
theorem R29189 : Reach 29189 := rs (se 4 (by rfl) ⟨2736, by rfl⟩) (B 5473 (by norm_num) ⟨2736, by rfl⟩ (by norm_num))
theorem R29213 : Reach 29213 := rs (se 3 (by rfl) ⟨5477, by rfl⟩) (B 10955 (by norm_num) ⟨5477, by rfl⟩ (by norm_num))
theorem R29237 : Reach 29237 := rs (se 5 (by rfl) ⟨1370, by rfl⟩) (B 2741 (by norm_num) ⟨1370, by rfl⟩ (by norm_num))
theorem R29261 : Reach 29261 := rs (se 3 (by rfl) ⟨5486, by rfl⟩) (B 10973 (by norm_num) ⟨5486, by rfl⟩ (by norm_num))
theorem R29285 : Reach 29285 := rs (se 4 (by rfl) ⟨2745, by rfl⟩) (B 5491 (by norm_num) ⟨2745, by rfl⟩ (by norm_num))
theorem R29309 : Reach 29309 := rs (se 3 (by rfl) ⟨5495, by rfl⟩) (B 10991 (by norm_num) ⟨5495, by rfl⟩ (by norm_num))
theorem R29333 : Reach 29333 := rs (se 6 (by rfl) ⟨687, by rfl⟩) (B 1375 (by norm_num) ⟨687, by rfl⟩ (by norm_num))
theorem R62117 : Reach 62117 := rs (se 4 (by rfl) ⟨5823, by rfl⟩) (B 11647 (by norm_num) ⟨5823, by rfl⟩ (by norm_num))
theorem R29357 : Reach 29357 := rs (se 3 (by rfl) ⟨5504, by rfl⟩) (B 11009 (by norm_num) ⟨5504, by rfl⟩ (by norm_num))
theorem R29381 : Reach 29381 := rs (se 4 (by rfl) ⟨2754, by rfl⟩) (B 5509 (by norm_num) ⟨2754, by rfl⟩ (by norm_num))
theorem R29389 : Reach 29389 := rs (se 3 (by rfl) ⟨5510, by rfl⟩) (B 11021 (by norm_num) ⟨5510, by rfl⟩ (by norm_num))
theorem R29405 : Reach 29405 := rs (se 3 (by rfl) ⟨5513, by rfl⟩) (B 11027 (by norm_num) ⟨5513, by rfl⟩ (by norm_num))
theorem R29429 : Reach 29429 := rs (se 5 (by rfl) ⟨1379, by rfl⟩) (B 2759 (by norm_num) ⟨1379, by rfl⟩ (by norm_num))
theorem R29453 : Reach 29453 := rs (se 3 (by rfl) ⟨5522, by rfl⟩) (B 11045 (by norm_num) ⟨5522, by rfl⟩ (by norm_num))
theorem R29477 : Reach 29477 := rs (se 4 (by rfl) ⟨2763, by rfl⟩) (B 5527 (by norm_num) ⟨2763, by rfl⟩ (by norm_num))
theorem R62261 : Reach 62261 := rs (se 5 (by rfl) ⟨2918, by rfl⟩) (B 5837 (by norm_num) ⟨2918, by rfl⟩ (by norm_num))
theorem R29501 : Reach 29501 := rs (se 3 (by rfl) ⟨5531, by rfl⟩) (B 11063 (by norm_num) ⟨5531, by rfl⟩ (by norm_num))
theorem R29525 : Reach 29525 := rs (se 9 (by rfl) ⟨86, by rfl⟩) (B 173 (by norm_num) ⟨86, by rfl⟩ (by norm_num))
theorem R29549 : Reach 29549 := rs (se 3 (by rfl) ⟨5540, by rfl⟩) (B 11081 (by norm_num) ⟨5540, by rfl⟩ (by norm_num))
theorem R95093 : Reach 95093 := rs (se 5 (by rfl) ⟨4457, by rfl⟩) (B 8915 (by norm_num) ⟨4457, by rfl⟩ (by norm_num))
theorem R29573 : Reach 29573 := rs (se 4 (by rfl) ⟨2772, by rfl⟩) (B 5545 (by norm_num) ⟨2772, by rfl⟩ (by norm_num))
theorem R29597 : Reach 29597 := rs (se 3 (by rfl) ⟨5549, by rfl⟩) (B 11099 (by norm_num) ⟨5549, by rfl⟩ (by norm_num))
theorem R29605 : Reach 29605 := rs (se 4 (by rfl) ⟨2775, by rfl⟩) (B 5551 (by norm_num) ⟨2775, by rfl⟩ (by norm_num))
theorem R29621 : Reach 29621 := rs (se 5 (by rfl) ⟨1388, by rfl⟩) (B 2777 (by norm_num) ⟨1388, by rfl⟩ (by norm_num))
theorem R29645 : Reach 29645 := rs (se 3 (by rfl) ⟨5558, by rfl⟩) (B 11117 (by norm_num) ⟨5558, by rfl⟩ (by norm_num))
theorem R29669 : Reach 29669 := rs (se 4 (by rfl) ⟨2781, by rfl⟩) (B 5563 (by norm_num) ⟨2781, by rfl⟩ (by norm_num))
theorem R29693 : Reach 29693 := rs (se 3 (by rfl) ⟨5567, by rfl⟩) (B 11135 (by norm_num) ⟨5567, by rfl⟩ (by norm_num))
theorem R29717 : Reach 29717 := rs (se 6 (by rfl) ⟨696, by rfl⟩) (B 1393 (by norm_num) ⟨696, by rfl⟩ (by norm_num))
theorem R29741 : Reach 29741 := rs (se 3 (by rfl) ⟨5576, by rfl⟩) (B 11153 (by norm_num) ⟨5576, by rfl⟩ (by norm_num))
theorem R29765 : Reach 29765 := rs (se 4 (by rfl) ⟨2790, by rfl⟩) (B 5581 (by norm_num) ⟨2790, by rfl⟩ (by norm_num))
theorem R29789 : Reach 29789 := rs (se 3 (by rfl) ⟨5585, by rfl⟩) (B 11171 (by norm_num) ⟨5585, by rfl⟩ (by norm_num))
theorem R29813 : Reach 29813 := rs (se 5 (by rfl) ⟨1397, by rfl⟩) (B 2795 (by norm_num) ⟨1397, by rfl⟩ (by norm_num))
theorem R29821 : Reach 29821 := rs (se 3 (by rfl) ⟨5591, by rfl⟩) (B 11183 (by norm_num) ⟨5591, by rfl⟩ (by norm_num))
theorem R29837 : Reach 29837 := rs (se 3 (by rfl) ⟨5594, by rfl⟩) (B 11189 (by norm_num) ⟨5594, by rfl⟩ (by norm_num))
theorem R29861 : Reach 29861 := rs (se 4 (by rfl) ⟨2799, by rfl⟩) (B 5599 (by norm_num) ⟨2799, by rfl⟩ (by norm_num))
theorem R29885 : Reach 29885 := rs (se 3 (by rfl) ⟨5603, by rfl⟩) (B 11207 (by norm_num) ⟨5603, by rfl⟩ (by norm_num))
theorem R128213 : Reach 128213 := rs (se 7 (by rfl) ⟨1502, by rfl⟩) (B 3005 (by norm_num) ⟨1502, by rfl⟩ (by norm_num))
theorem R29909 : Reach 29909 := rs (se 7 (by rfl) ⟨350, by rfl⟩) (B 701 (by norm_num) ⟨350, by rfl⟩ (by norm_num))
theorem R62693 : Reach 62693 := rs (se 4 (by rfl) ⟨5877, by rfl⟩) (B 11755 (by norm_num) ⟨5877, by rfl⟩ (by norm_num))
theorem R29933 : Reach 29933 := rs (se 3 (by rfl) ⟨5612, by rfl⟩) (B 11225 (by norm_num) ⟨5612, by rfl⟩ (by norm_num))
theorem R29957 : Reach 29957 := rs (se 4 (by rfl) ⟨2808, by rfl⟩) (B 5617 (by norm_num) ⟨2808, by rfl⟩ (by norm_num))
theorem R29965 : Reach 29965 := rs (se 3 (by rfl) ⟨5618, by rfl⟩) (B 11237 (by norm_num) ⟨5618, by rfl⟩ (by norm_num))
theorem R29981 : Reach 29981 := rs (se 3 (by rfl) ⟨5621, by rfl⟩) (B 11243 (by norm_num) ⟨5621, by rfl⟩ (by norm_num))
theorem R30005 : Reach 30005 := rs (se 5 (by rfl) ⟨1406, by rfl⟩) (B 2813 (by norm_num) ⟨1406, by rfl⟩ (by norm_num))
theorem R30037 : Reach 30037 := rs (se 13 (by rfl) ⟨5, by rfl⟩) (B 11 (by norm_num) ⟨5, by rfl⟩ (by norm_num))
theorem R30077 : Reach 30077 := rs (se 3 (by rfl) ⟨5639, by rfl⟩) (B 11279 (by norm_num) ⟨5639, by rfl⟩ (by norm_num))
theorem R62869 : Reach 62869 := rs (se 6 (by rfl) ⟨1473, by rfl⟩) (B 2947 (by norm_num) ⟨1473, by rfl⟩ (by norm_num))
theorem R30125 : Reach 30125 := rs (se 3 (by rfl) ⟨5648, by rfl⟩) (B 11297 (by norm_num) ⟨5648, by rfl⟩ (by norm_num))
theorem R30149 : Reach 30149 := rs (se 4 (by rfl) ⟨2826, by rfl⟩) (B 5653 (by norm_num) ⟨2826, by rfl⟩ (by norm_num))
theorem R30197 : Reach 30197 := rs (se 5 (by rfl) ⟨1415, by rfl⟩) (B 2831 (by norm_num) ⟨1415, by rfl⟩ (by norm_num))
theorem R30221 : Reach 30221 := rs (se 3 (by rfl) ⟨5666, by rfl⟩) (B 11333 (by norm_num) ⟨5666, by rfl⟩ (by norm_num))
theorem R63013 : Reach 63013 := rs (se 4 (by rfl) ⟨5907, by rfl⟩) (B 11815 (by norm_num) ⟨5907, by rfl⟩ (by norm_num))
theorem R30253 : Reach 30253 := rs (se 3 (by rfl) ⟨5672, by rfl⟩) (B 11345 (by norm_num) ⟨5672, by rfl⟩ (by norm_num))
theorem R30269 : Reach 30269 := rs (se 3 (by rfl) ⟨5675, by rfl⟩) (B 11351 (by norm_num) ⟨5675, by rfl⟩ (by norm_num))
theorem R30293 : Reach 30293 := rs (se 8 (by rfl) ⟨177, by rfl⟩) (B 355 (by norm_num) ⟨177, by rfl⟩ (by norm_num))
theorem R30341 : Reach 30341 := rs (se 4 (by rfl) ⟨2844, by rfl⟩) (B 5689 (by norm_num) ⟨2844, by rfl⟩ (by norm_num))
theorem R63125 : Reach 63125 := rs (se 6 (by rfl) ⟨1479, by rfl⟩) (B 2959 (by norm_num) ⟨1479, by rfl⟩ (by norm_num))
theorem R30365 : Reach 30365 := rs (se 3 (by rfl) ⟨5693, by rfl⟩) (B 11387 (by norm_num) ⟨5693, by rfl⟩ (by norm_num))
theorem R30413 : Reach 30413 := rs (se 3 (by rfl) ⟨5702, by rfl⟩) (B 11405 (by norm_num) ⟨5702, by rfl⟩ (by norm_num))
theorem R30437 : Reach 30437 := rs (se 4 (by rfl) ⟨2853, by rfl⟩) (B 5707 (by norm_num) ⟨2853, by rfl⟩ (by norm_num))
theorem R30469 : Reach 30469 := rs (se 4 (by rfl) ⟨2856, by rfl⟩) (B 5713 (by norm_num) ⟨2856, by rfl⟩ (by norm_num))
theorem R128789 : Reach 128789 := rs (se 6 (by rfl) ⟨3018, by rfl⟩) (B 6037 (by norm_num) ⟨3018, by rfl⟩ (by norm_num))
theorem R30493 : Reach 30493 := rs (se 3 (by rfl) ⟨5717, by rfl⟩) (B 11435 (by norm_num) ⟨5717, by rfl⟩ (by norm_num))
theorem R30509 : Reach 30509 := rs (se 3 (by rfl) ⟨5720, by rfl⟩) (B 11441 (by norm_num) ⟨5720, by rfl⟩ (by norm_num))
theorem R63301 : Reach 63301 := rs (se 4 (by rfl) ⟨5934, by rfl⟩) (B 11869 (by norm_num) ⟨5934, by rfl⟩ (by norm_num))
theorem R63317 : Reach 63317 := rs (se 9 (by rfl) ⟨185, by rfl⟩) (B 371 (by norm_num) ⟨185, by rfl⟩ (by norm_num))
theorem R30557 : Reach 30557 := rs (se 3 (by rfl) ⟨5729, by rfl⟩) (B 11459 (by norm_num) ⟨5729, by rfl⟩ (by norm_num))
theorem R30581 : Reach 30581 := rs (se 5 (by rfl) ⟨1433, by rfl⟩) (B 2867 (by norm_num) ⟨1433, by rfl⟩ (by norm_num))
theorem R30653 : Reach 30653 := rs (se 3 (by rfl) ⟨5747, by rfl⟩) (B 11495 (by norm_num) ⟨5747, by rfl⟩ (by norm_num))
theorem R30685 : Reach 30685 := rs (se 3 (by rfl) ⟨5753, by rfl⟩) (B 11507 (by norm_num) ⟨5753, by rfl⟩ (by norm_num))
theorem R30709 : Reach 30709 := rs (se 5 (by rfl) ⟨1439, by rfl⟩) (B 2879 (by norm_num) ⟨1439, by rfl⟩ (by norm_num))
theorem R30725 : Reach 30725 := rs (se 4 (by rfl) ⟨2880, by rfl⟩) (B 5761 (by norm_num) ⟨2880, by rfl⟩ (by norm_num))
theorem R30773 : Reach 30773 := rs (se 5 (by rfl) ⟨1442, by rfl⟩) (B 2885 (by norm_num) ⟨1442, by rfl⟩ (by norm_num))
theorem R63557 : Reach 63557 := rs (se 4 (by rfl) ⟨5958, by rfl⟩) (B 11917 (by norm_num) ⟨5958, by rfl⟩ (by norm_num))
theorem R30797 : Reach 30797 := rs (se 3 (by rfl) ⟨5774, by rfl⟩) (B 11549 (by norm_num) ⟨5774, by rfl⟩ (by norm_num))
theorem R63605 : Reach 63605 := rs (se 5 (by rfl) ⟨2981, by rfl⟩) (B 5963 (by norm_num) ⟨2981, by rfl⟩ (by norm_num))
theorem R30869 : Reach 30869 := rs (se 6 (by rfl) ⟨723, by rfl⟩) (B 1447 (by norm_num) ⟨723, by rfl⟩ (by norm_num))
theorem R30901 : Reach 30901 := rs (se 5 (by rfl) ⟨1448, by rfl⟩) (B 2897 (by norm_num) ⟨1448, by rfl⟩ (by norm_num))
theorem R30941 : Reach 30941 := rs (se 3 (by rfl) ⟨5801, by rfl⟩) (B 11603 (by norm_num) ⟨5801, by rfl⟩ (by norm_num))
theorem R30989 : Reach 30989 := rs (se 3 (by rfl) ⟨5810, by rfl⟩) (B 11621 (by norm_num) ⟨5810, by rfl⟩ (by norm_num))
theorem R31013 : Reach 31013 := rs (se 4 (by rfl) ⟨2907, by rfl⟩) (B 5815 (by norm_num) ⟨2907, by rfl⟩ (by norm_num))
theorem R31085 : Reach 31085 := rs (se 3 (by rfl) ⟨5828, by rfl⟩) (B 11657 (by norm_num) ⟨5828, by rfl⟩ (by norm_num))
theorem R31117 : Reach 31117 := rs (se 3 (by rfl) ⟨5834, by rfl⟩) (B 11669 (by norm_num) ⟨5834, by rfl⟩ (by norm_num))
theorem R31157 : Reach 31157 := rs (se 5 (by rfl) ⟨1460, by rfl⟩) (B 2921 (by norm_num) ⟨1460, by rfl⟩ (by norm_num))
theorem R31205 : Reach 31205 := rs (se 4 (by rfl) ⟨2925, by rfl⟩) (B 5851 (by norm_num) ⟨2925, by rfl⟩ (by norm_num))
theorem R63989 : Reach 63989 := rs (se 5 (by rfl) ⟨2999, by rfl⟩) (B 5999 (by norm_num) ⟨2999, by rfl⟩ (by norm_num))
theorem R31229 : Reach 31229 := rs (se 3 (by rfl) ⟨5855, by rfl⟩) (B 11711 (by norm_num) ⟨5855, by rfl⟩ (by norm_num))
theorem R96821 : Reach 96821 := rs (se 5 (by rfl) ⟨4538, by rfl⟩) (B 9077 (by norm_num) ⟨4538, by rfl⟩ (by norm_num))
theorem R31301 : Reach 31301 := rs (se 4 (by rfl) ⟨2934, by rfl⟩) (B 5869 (by norm_num) ⟨2934, by rfl⟩ (by norm_num))
theorem R31333 : Reach 31333 := rs (se 4 (by rfl) ⟨2937, by rfl⟩) (B 5875 (by norm_num) ⟨2937, by rfl⟩ (by norm_num))
theorem R31373 : Reach 31373 := rs (se 3 (by rfl) ⟨5882, by rfl⟩) (B 11765 (by norm_num) ⟨5882, by rfl⟩ (by norm_num))
theorem R31421 : Reach 31421 := rs (se 3 (by rfl) ⟨5891, by rfl⟩) (B 11783 (by norm_num) ⟨5891, by rfl⟩ (by norm_num))
theorem R31445 : Reach 31445 := rs (se 7 (by rfl) ⟨368, by rfl⟩) (B 737 (by norm_num) ⟨368, by rfl⟩ (by norm_num))
theorem R31517 : Reach 31517 := rs (se 3 (by rfl) ⟨5909, by rfl⟩) (B 11819 (by norm_num) ⟨5909, by rfl⟩ (by norm_num))
theorem R31549 : Reach 31549 := rs (se 3 (by rfl) ⟨5915, by rfl⟩) (B 11831 (by norm_num) ⟨5915, by rfl⟩ (by norm_num))
theorem R97109 : Reach 97109 := rs (se 9 (by rfl) ⟨284, by rfl⟩) (B 569 (by norm_num) ⟨284, by rfl⟩ (by norm_num))
theorem R31589 : Reach 31589 := rs (se 4 (by rfl) ⟨2961, by rfl⟩) (B 5923 (by norm_num) ⟨2961, by rfl⟩ (by norm_num))
theorem R31637 : Reach 31637 := rs (se 6 (by rfl) ⟨741, by rfl⟩) (B 1483 (by norm_num) ⟨741, by rfl⟩ (by norm_num))
theorem R64421 : Reach 64421 := rs (se 4 (by rfl) ⟨6039, by rfl⟩) (B 12079 (by norm_num) ⟨6039, by rfl⟩ (by norm_num))
theorem R31661 : Reach 31661 := rs (se 3 (by rfl) ⟨5936, by rfl⟩) (B 11873 (by norm_num) ⟨5936, by rfl⟩ (by norm_num))
theorem R31733 : Reach 31733 := rs (se 5 (by rfl) ⟨1487, by rfl⟩) (B 2975 (by norm_num) ⟨1487, by rfl⟩ (by norm_num))
theorem R31757 : Reach 31757 := rs (se 3 (by rfl) ⟨5954, by rfl⟩) (B 11909 (by norm_num) ⟨5954, by rfl⟩ (by norm_num))
theorem R31765 : Reach 31765 := rs (se 6 (by rfl) ⟨744, by rfl⟩) (B 1489 (by norm_num) ⟨744, by rfl⟩ (by norm_num))
theorem R31789 : Reach 31789 := rs (se 3 (by rfl) ⟨5960, by rfl⟩) (B 11921 (by norm_num) ⟨5960, by rfl⟩ (by norm_num))
theorem R31805 : Reach 31805 := rs (se 3 (by rfl) ⟨5963, by rfl⟩) (B 11927 (by norm_num) ⟨5963, by rfl⟩ (by norm_num))
theorem R31853 : Reach 31853 := rs (se 3 (by rfl) ⟨5972, by rfl⟩) (B 11945 (by norm_num) ⟨5972, by rfl⟩ (by norm_num))
theorem R31877 : Reach 31877 := rs (se 4 (by rfl) ⟨2988, by rfl⟩) (B 5977 (by norm_num) ⟨2988, by rfl⟩ (by norm_num))
theorem R31909 : Reach 31909 := rs (se 4 (by rfl) ⟨2991, by rfl⟩) (B 5983 (by norm_num) ⟨2991, by rfl⟩ (by norm_num))
theorem R31949 : Reach 31949 := rs (se 3 (by rfl) ⟨5990, by rfl⟩) (B 11981 (by norm_num) ⟨5990, by rfl⟩ (by norm_num))
theorem R31981 : Reach 31981 := rs (se 3 (by rfl) ⟨5996, by rfl⟩) (B 11993 (by norm_num) ⟨5996, by rfl⟩ (by norm_num))
theorem R32021 : Reach 32021 := rs (se 6 (by rfl) ⟨750, by rfl⟩) (B 1501 (by norm_num) ⟨750, by rfl⟩ (by norm_num))
theorem R32069 : Reach 32069 := rs (se 4 (by rfl) ⟨3006, by rfl⟩) (B 6013 (by norm_num) ⟨3006, by rfl⟩ (by norm_num))
theorem R64853 : Reach 64853 := rs (se 11 (by rfl) ⟨47, by rfl⟩) (B 95 (by norm_num) ⟨47, by rfl⟩ (by norm_num))
theorem R32093 : Reach 32093 := rs (se 3 (by rfl) ⟨6017, by rfl⟩) (B 12035 (by norm_num) ⟨6017, by rfl⟩ (by norm_num))
theorem R97685 : Reach 97685 := rs (se 6 (by rfl) ⟨2289, by rfl⟩) (B 4579 (by norm_num) ⟨2289, by rfl⟩ (by norm_num))
theorem R32165 : Reach 32165 := rs (se 4 (by rfl) ⟨3015, by rfl⟩) (B 6031 (by norm_num) ⟨3015, by rfl⟩ (by norm_num))
theorem R32197 : Reach 32197 := rs (se 4 (by rfl) ⟨3018, by rfl⟩) (B 6037 (by norm_num) ⟨3018, by rfl⟩ (by norm_num))
theorem R32213 : Reach 32213 := rs (se 7 (by rfl) ⟨377, by rfl⟩) (B 755 (by norm_num) ⟨377, by rfl⟩ (by norm_num))
theorem R32237 : Reach 32237 := rs (se 3 (by rfl) ⟨6044, by rfl⟩) (B 12089 (by norm_num) ⟨6044, by rfl⟩ (by norm_num))
theorem R32285 : Reach 32285 := rs (se 3 (by rfl) ⟨6053, by rfl⟩) (B 12107 (by norm_num) ⟨6053, by rfl⟩ (by norm_num))
theorem R32309 : Reach 32309 := rs (se 5 (by rfl) ⟨1514, by rfl⟩) (B 3029 (by norm_num) ⟨1514, by rfl⟩ (by norm_num))
theorem R32381 : Reach 32381 := rs (se 3 (by rfl) ⟨6071, by rfl⟩) (B 12143 (by norm_num) ⟨6071, by rfl⟩ (by norm_num))
theorem R32413 : Reach 32413 := rs (se 3 (by rfl) ⟨6077, by rfl⟩) (B 12155 (by norm_num) ⟨6077, by rfl⟩ (by norm_num))
theorem R32453 : Reach 32453 := rs (se 4 (by rfl) ⟨3042, by rfl⟩) (B 6085 (by norm_num) ⟨3042, by rfl⟩ (by norm_num))
theorem R98005 : Reach 98005 := rs (se 7 (by rfl) ⟨1148, by rfl⟩) (B 2297 (by norm_num) ⟨1148, by rfl⟩ (by norm_num))
theorem R32501 : Reach 32501 := rs (se 5 (by rfl) ⟨1523, by rfl⟩) (B 3047 (by norm_num) ⟨1523, by rfl⟩ (by norm_num))
theorem R65285 : Reach 65285 := rs (se 4 (by rfl) ⟨6120, by rfl⟩) (B 12241 (by norm_num) ⟨6120, by rfl⟩ (by norm_num))
theorem R32525 : Reach 32525 := rs (se 3 (by rfl) ⟨6098, by rfl⟩) (B 12197 (by norm_num) ⟨6098, by rfl⟩ (by norm_num))
theorem R32581 : Reach 32581 := rs (se 4 (by rfl) ⟨3054, by rfl⟩) (B 6109 (by norm_num) ⟨3054, by rfl⟩ (by norm_num))
theorem R32597 : Reach 32597 := rs (se 9 (by rfl) ⟨95, by rfl⟩) (B 191 (by norm_num) ⟨95, by rfl⟩ (by norm_num))
theorem R32629 : Reach 32629 := rs (se 5 (by rfl) ⟨1529, by rfl⟩) (B 3059 (by norm_num) ⟨1529, by rfl⟩ (by norm_num))
theorem R32653 : Reach 32653 := rs (se 3 (by rfl) ⟨6122, by rfl⟩) (B 12245 (by norm_num) ⟨6122, by rfl⟩ (by norm_num))
theorem R32669 : Reach 32669 := rs (se 3 (by rfl) ⟨6125, by rfl⟩) (B 12251 (by norm_num) ⟨6125, by rfl⟩ (by norm_num))
theorem R32717 : Reach 32717 := rs (se 3 (by rfl) ⟨6134, by rfl⟩) (B 12269 (by norm_num) ⟨6134, by rfl⟩ (by norm_num))
theorem R32741 : Reach 32741 := rs (se 4 (by rfl) ⟨3069, by rfl⟩) (B 6139 (by norm_num) ⟨3069, by rfl⟩ (by norm_num))
theorem R32771 : Reach 32771 := rs (se 1 (by rfl) ⟨24578, by rfl⟩) R49157
theorem R65549 : Reach 65549 := rs (se 3 (by rfl) ⟨12290, by rfl⟩) R24581
theorem R32849 : Reach 32849 := rs (se 2 (by rfl) ⟨12318, by rfl⟩) R24637
theorem R32867 : Reach 32867 := rs (se 1 (by rfl) ⟨24650, by rfl⟩) R49301
theorem R32881 : Reach 32881 := rs (se 2 (by rfl) ⟨12330, by rfl⟩) R24661
theorem R32899 : Reach 32899 := rs (se 1 (by rfl) ⟨24674, by rfl⟩) R49349
theorem R33041 : Reach 33041 := rs (se 2 (by rfl) ⟨12390, by rfl⟩) R24781
theorem R33137 : Reach 33137 := rs (se 2 (by rfl) ⟨12426, by rfl⟩) R24853
theorem R328049 : Reach 328049 := rs (se 2 (by rfl) ⟨123018, by rfl⟩) R246037
theorem R33155 : Reach 33155 := rs (se 1 (by rfl) ⟨24866, by rfl⟩) R49733
theorem R65933 : Reach 65933 := rs (se 3 (by rfl) ⟨12362, by rfl⟩) R24725
theorem R33169 : Reach 33169 := rs (se 2 (by rfl) ⟨12438, by rfl⟩) R24877
theorem R33347 : Reach 33347 := rs (se 1 (by rfl) ⟨25010, by rfl⟩) R50021
theorem R33425 : Reach 33425 := rs (se 2 (by rfl) ⟨12534, by rfl⟩) R25069
theorem R33443 : Reach 33443 := rs (se 1 (by rfl) ⟨25082, by rfl⟩) R50165
theorem R33635 : Reach 33635 := rs (se 1 (by rfl) ⟨25226, by rfl⟩) R50453
theorem R131939 : Reach 131939 := rs (se 1 (by rfl) ⟨98954, by rfl⟩) R197909
theorem R33713 : Reach 33713 := rs (se 2 (by rfl) ⟨12642, by rfl⟩) R25285
theorem R33731 : Reach 33731 := rs (se 1 (by rfl) ⟨25298, by rfl⟩) R50597
theorem R34001 : Reach 34001 := rs (se 2 (by rfl) ⟨12750, by rfl⟩) R25501
theorem R34019 : Reach 34019 := rs (se 1 (by rfl) ⟨25514, by rfl⟩) R51029
theorem R66851 : Reach 66851 := rs (se 1 (by rfl) ⟨50138, by rfl⟩) R100277
theorem R34253 : Reach 34253 := rs (se 3 (by rfl) ⟨6422, by rfl⟩) R12845
theorem R34289 : Reach 34289 := rs (se 2 (by rfl) ⟨12858, by rfl⟩) R25717
theorem R34307 : Reach 34307 := rs (se 1 (by rfl) ⟨25730, by rfl⟩) R51461
theorem R34339 : Reach 34339 := rs (se 1 (by rfl) ⟨25754, by rfl⟩) R51509
theorem R67121 : Reach 67121 := rs (se 2 (by rfl) ⟨25170, by rfl⟩) R50341
theorem R132677 : Reach 132677 := rs (se 4 (by rfl) ⟨12438, by rfl⟩) R24877
theorem R99953 : Reach 99953 := rs (se 2 (by rfl) ⟨37482, by rfl⟩) R74965
theorem R34445 : Reach 34445 := rs (se 3 (by rfl) ⟨6458, by rfl⟩) R12917
theorem R34481 : Reach 34481 := rs (se 2 (by rfl) ⟨12930, by rfl⟩) R25861
theorem R34499 : Reach 34499 := rs (se 1 (by rfl) ⟨25874, by rfl⟩) R51749
theorem R34541 : Reach 34541 := rs (se 3 (by rfl) ⟨6476, by rfl⟩) R12953
theorem R34577 : Reach 34577 := rs (se 2 (by rfl) ⟨12966, by rfl⟩) R25933
theorem R34595 : Reach 34595 := rs (se 1 (by rfl) ⟨25946, by rfl⟩) R51893
theorem R34627 : Reach 34627 := rs (se 1 (by rfl) ⟨25970, by rfl⟩) R51941
theorem R67405 : Reach 67405 := rs (se 3 (by rfl) ⟨12638, by rfl⟩) R25277
theorem R132977 : Reach 132977 := rs (se 2 (by rfl) ⟨49866, by rfl⟩) R99733
theorem R100237 : Reach 100237 := rs (se 3 (by rfl) ⟨18794, by rfl⟩) R37589
theorem R34769 : Reach 34769 := rs (se 2 (by rfl) ⟨13038, by rfl⟩) R26077
theorem R34787 : Reach 34787 := rs (se 1 (by rfl) ⟨26090, by rfl⟩) R52181
theorem R34829 : Reach 34829 := rs (se 3 (by rfl) ⟨6530, by rfl⟩) R13061
theorem R34865 : Reach 34865 := rs (se 2 (by rfl) ⟨13074, by rfl⟩) R26149
theorem R34883 : Reach 34883 := rs (se 1 (by rfl) ⟨26162, by rfl⟩) R52325
theorem R67661 : Reach 67661 := rs (se 3 (by rfl) ⟨12686, by rfl⟩) R25373
theorem R35117 : Reach 35117 := rs (se 3 (by rfl) ⟨6584, by rfl⟩) R13169
theorem R35153 : Reach 35153 := rs (se 2 (by rfl) ⟨13182, by rfl⟩) R26365
theorem R35171 : Reach 35171 := rs (se 1 (by rfl) ⟨26378, by rfl⟩) R52757
theorem R231821 : Reach 231821 := rs (se 3 (by rfl) ⟨43466, by rfl⟩) R86933
theorem R68003 : Reach 68003 := rs (se 1 (by rfl) ⟨51002, by rfl⟩) R102005
theorem R68045 : Reach 68045 := rs (se 3 (by rfl) ⟨12758, by rfl⟩) R25517
theorem R35405 : Reach 35405 := rs (se 3 (by rfl) ⟨6638, by rfl⟩) R13277
theorem R35437 : Reach 35437 := rs (se 3 (by rfl) ⟨6644, by rfl⟩) R13289
theorem R35441 : Reach 35441 := rs (se 2 (by rfl) ⟨13290, by rfl⟩) R26581
theorem R35459 : Reach 35459 := rs (se 1 (by rfl) ⟨26594, by rfl⟩) R53189
theorem R35569 : Reach 35569 := rs (se 2 (by rfl) ⟨13338, by rfl⟩) R26677
theorem R35693 : Reach 35693 := rs (se 3 (by rfl) ⟨6692, by rfl⟩) R13385
theorem R68465 : Reach 68465 := rs (se 2 (by rfl) ⟨25674, by rfl⟩) R51349
theorem R166769 : Reach 166769 := rs (se 2 (by rfl) ⟨62538, by rfl⟩) R125077
theorem R35729 : Reach 35729 := rs (se 2 (by rfl) ⟨13398, by rfl⟩) R26797
theorem R35747 : Reach 35747 := rs (se 1 (by rfl) ⟨26810, by rfl⟩) R53621
theorem R35761 : Reach 35761 := rs (se 2 (by rfl) ⟨13410, by rfl⟩) R26821
theorem R68677 : Reach 68677 := rs (se 4 (by rfl) ⟨6438, by rfl⟩) R12877
theorem R35981 : Reach 35981 := rs (se 3 (by rfl) ⟨6746, by rfl⟩) R13493
theorem R36017 : Reach 36017 := rs (se 2 (by rfl) ⟨13506, by rfl⟩) R27013
theorem R36035 : Reach 36035 := rs (se 1 (by rfl) ⟨27026, by rfl⟩) R54053
theorem R101573 : Reach 101573 := rs (se 4 (by rfl) ⟨9522, by rfl⟩) R19045
theorem R36067 : Reach 36067 := rs (se 1 (by rfl) ⟨27050, by rfl⟩) R54101
theorem R199907 : Reach 199907 := rs (se 1 (by rfl) ⟨149930, by rfl⟩) R299861
theorem R68849 : Reach 68849 := rs (se 2 (by rfl) ⟨25818, by rfl⟩) R51637
theorem R101645 : Reach 101645 := rs (se 3 (by rfl) ⟨19058, by rfl⟩) R38117
theorem R36227 : Reach 36227 := rs (se 1 (by rfl) ⟨27170, by rfl⟩) R54341
theorem R36269 : Reach 36269 := rs (se 3 (by rfl) ⟨6800, by rfl⟩) R13601
theorem R36305 : Reach 36305 := rs (se 2 (by rfl) ⟨13614, by rfl⟩) R27229
theorem R36323 : Reach 36323 := rs (se 1 (by rfl) ⟨27242, by rfl⟩) R54485
theorem R69133 : Reach 69133 := rs (se 3 (by rfl) ⟨12962, by rfl⟩) R25925
theorem R36557 : Reach 36557 := rs (se 3 (by rfl) ⟨6854, by rfl⟩) R13709
theorem R36593 : Reach 36593 := rs (se 2 (by rfl) ⟨13722, by rfl⟩) R27445
theorem R36611 : Reach 36611 := rs (se 1 (by rfl) ⟨27458, by rfl⟩) R54917
theorem R36625 : Reach 36625 := rs (se 2 (by rfl) ⟨13734, by rfl⟩) R27469
theorem R36749 : Reach 36749 := rs (se 3 (by rfl) ⟨6890, by rfl⟩) R13781
theorem R36845 : Reach 36845 := rs (se 3 (by rfl) ⟨6908, by rfl⟩) R13817
theorem R36881 : Reach 36881 := rs (se 2 (by rfl) ⟨13830, by rfl⟩) R27661
theorem R36899 : Reach 36899 := rs (se 1 (by rfl) ⟨27674, by rfl⟩) R55349
theorem R37027 : Reach 37027 := rs (se 1 (by rfl) ⟨27770, by rfl⟩) R55541
theorem R37037 : Reach 37037 := rs (se 3 (by rfl) ⟨6944, by rfl⟩) R13889
theorem R37073 : Reach 37073 := rs (se 2 (by rfl) ⟨13902, by rfl⟩) R27805
theorem R69893 : Reach 69893 := rs (se 4 (by rfl) ⟨6552, by rfl⟩) R13105
theorem R37133 : Reach 37133 := rs (se 3 (by rfl) ⟨6962, by rfl⟩) R13925
theorem R299285 : Reach 299285 := rs (se 6 (by rfl) ⟨7014, by rfl⟩) R14029
theorem R69923 : Reach 69923 := rs (se 1 (by rfl) ⟨52442, by rfl⟩) R104885
theorem R37169 : Reach 37169 := rs (se 2 (by rfl) ⟨13938, by rfl⟩) R27877
theorem R37187 : Reach 37187 := rs (se 1 (by rfl) ⟨27890, by rfl⟩) R55781
theorem R37219 : Reach 37219 := rs (se 1 (by rfl) ⟨27914, by rfl⟩) R55829
theorem R37361 : Reach 37361 := rs (se 2 (by rfl) ⟨14010, by rfl⟩) R28021
theorem R37421 : Reach 37421 := rs (se 3 (by rfl) ⟨7016, by rfl⟩) R14033
theorem R37457 : Reach 37457 := rs (se 2 (by rfl) ⟨14046, by rfl⟩) R28093
theorem R37475 : Reach 37475 := rs (se 1 (by rfl) ⟨28106, by rfl⟩) R56213
theorem R70307 : Reach 70307 := rs (se 1 (by rfl) ⟨52730, by rfl⟩) R105461
theorem R103153 : Reach 103153 := rs (se 2 (by rfl) ⟨38682, by rfl⟩) R77365
theorem R70469 : Reach 70469 := rs (se 4 (by rfl) ⟨6606, by rfl⟩) R13213
theorem R37709 : Reach 37709 := rs (se 3 (by rfl) ⟨7070, by rfl⟩) R14141
theorem R37741 : Reach 37741 := rs (se 3 (by rfl) ⟨7076, by rfl⟩) R14153
theorem R37745 : Reach 37745 := rs (se 2 (by rfl) ⟨14154, by rfl⟩) R28309
theorem R37763 : Reach 37763 := rs (se 1 (by rfl) ⟨28322, by rfl⟩) R56645
theorem R70541 : Reach 70541 := rs (se 3 (by rfl) ⟨13226, by rfl⟩) R26453
theorem R70577 : Reach 70577 := rs (se 2 (by rfl) ⟨26466, by rfl⟩) R52933
theorem R37901 : Reach 37901 := rs (se 3 (by rfl) ⟨7106, by rfl⟩) R14213
theorem R37997 : Reach 37997 := rs (se 3 (by rfl) ⟨7124, by rfl⟩) R14249
theorem R38029 : Reach 38029 := rs (se 3 (by rfl) ⟨7130, by rfl⟩) R14261
theorem R38033 : Reach 38033 := rs (se 2 (by rfl) ⟨14262, by rfl⟩) R28525
theorem R38051 : Reach 38051 := rs (se 1 (by rfl) ⟨28538, by rfl⟩) R57077
theorem R38285 : Reach 38285 := rs (se 3 (by rfl) ⟨7178, by rfl⟩) R14357
theorem R38321 : Reach 38321 := rs (se 2 (by rfl) ⟨14370, by rfl⟩) R28741
theorem R38339 : Reach 38339 := rs (se 1 (by rfl) ⟨28754, by rfl⟩) R57509
theorem R71117 : Reach 71117 := rs (se 3 (by rfl) ⟨13334, by rfl⟩) R26669
theorem R38353 : Reach 38353 := rs (se 2 (by rfl) ⟨14382, by rfl⟩) R28765
theorem R38531 : Reach 38531 := rs (se 1 (by rfl) ⟨28898, by rfl⟩) R57797
theorem R38573 : Reach 38573 := rs (se 3 (by rfl) ⟨7232, by rfl⟩) R14465
theorem R136885 : Reach 136885 := rs (se 5 (by rfl) ⟨6416, by rfl⟩) R12833
theorem R38609 : Reach 38609 := rs (se 2 (by rfl) ⟨14478, by rfl⟩) R28957
theorem R38627 : Reach 38627 := rs (se 1 (by rfl) ⟨28970, by rfl⟩) R57941
theorem R71459 : Reach 71459 := rs (se 1 (by rfl) ⟨53594, by rfl⟩) R107189
theorem R38819 : Reach 38819 := rs (se 1 (by rfl) ⟨29114, by rfl⟩) R58229
theorem R71621 : Reach 71621 := rs (se 4 (by rfl) ⟨6714, by rfl⟩) R13429
theorem R38861 : Reach 38861 := rs (se 3 (by rfl) ⟨7286, by rfl⟩) R14573
theorem R38893 : Reach 38893 := rs (se 3 (by rfl) ⟨7292, by rfl⟩) R14585
theorem R38897 : Reach 38897 := rs (se 2 (by rfl) ⟨14586, by rfl⟩) R29173
theorem R38915 : Reach 38915 := rs (se 1 (by rfl) ⟨29186, by rfl⟩) R58373
theorem R39149 : Reach 39149 := rs (se 3 (by rfl) ⟨7340, by rfl⟩) R14681
theorem R39185 : Reach 39185 := rs (se 2 (by rfl) ⟨14694, by rfl⟩) R29389
theorem R366869 : Reach 366869 := rs (se 6 (by rfl) ⟨8598, by rfl⟩) R17197
theorem R39203 : Reach 39203 := rs (se 1 (by rfl) ⟨29402, by rfl⟩) R58805
theorem R72035 : Reach 72035 := rs (se 1 (by rfl) ⟨54026, by rfl⟩) R108053
theorem R72049 : Reach 72049 := rs (se 2 (by rfl) ⟨27018, by rfl⟩) R54037
theorem R137699 : Reach 137699 := rs (se 1 (by rfl) ⟨103274, by rfl⟩) R206549
theorem R39437 : Reach 39437 := rs (se 3 (by rfl) ⟨7394, by rfl⟩) R14789
theorem R39469 : Reach 39469 := rs (se 3 (by rfl) ⟨7400, by rfl⟩) R14801
theorem R39473 : Reach 39473 := rs (se 2 (by rfl) ⟨14802, by rfl⟩) R29605
theorem R39491 : Reach 39491 := rs (se 1 (by rfl) ⟨29618, by rfl⟩) R59237
theorem R72325 : Reach 72325 := rs (se 4 (by rfl) ⟨6780, by rfl⟩) R13561
theorem R39629 : Reach 39629 := rs (se 3 (by rfl) ⟨7430, by rfl⟩) R14861
theorem R39725 : Reach 39725 := rs (se 3 (by rfl) ⟨7448, by rfl⟩) R14897
theorem R39761 : Reach 39761 := rs (se 2 (by rfl) ⟨14910, by rfl⟩) R29821
theorem R39779 : Reach 39779 := rs (se 1 (by rfl) ⟨29834, by rfl⟩) R59669
theorem R39811 : Reach 39811 := rs (se 1 (by rfl) ⟨29858, by rfl⟩) R59717
theorem R72581 : Reach 72581 := rs (se 4 (by rfl) ⟨6804, by rfl⟩) R13609
theorem R39953 : Reach 39953 := rs (se 2 (by rfl) ⟨14982, by rfl⟩) R29965
theorem R40013 : Reach 40013 := rs (se 3 (by rfl) ⟨7502, by rfl⟩) R15005
theorem R40049 : Reach 40049 := rs (se 2 (by rfl) ⟨15018, by rfl⟩) R30037
theorem R40067 : Reach 40067 := rs (se 1 (by rfl) ⟨30050, by rfl⟩) R60101
theorem R138509 : Reach 138509 := rs (se 3 (by rfl) ⟨25970, by rfl⟩) R51941
theorem R40301 : Reach 40301 := rs (se 3 (by rfl) ⟨7556, by rfl⟩) R15113
theorem R40337 : Reach 40337 := rs (se 2 (by rfl) ⟨15126, by rfl⟩) R30253
theorem R40355 : Reach 40355 := rs (se 1 (by rfl) ⟨30266, by rfl⟩) R60533
theorem R40547 : Reach 40547 := rs (se 1 (by rfl) ⟨30410, by rfl⟩) R60821
theorem R40589 : Reach 40589 := rs (se 3 (by rfl) ⟨7610, by rfl⟩) R15221
theorem R40621 : Reach 40621 := rs (se 3 (by rfl) ⟨7616, by rfl⟩) R15233
theorem R40625 : Reach 40625 := rs (se 2 (by rfl) ⟨15234, by rfl⟩) R30469
theorem R40643 : Reach 40643 := rs (se 1 (by rfl) ⟨30482, by rfl⟩) R60965
theorem R40657 : Reach 40657 := rs (se 2 (by rfl) ⟨15246, by rfl⟩) R30493
theorem R73507 : Reach 73507 := rs (se 1 (by rfl) ⟨55130, by rfl⟩) R110261
theorem R40877 : Reach 40877 := rs (se 3 (by rfl) ⟨7664, by rfl⟩) R15329
theorem R40913 : Reach 40913 := rs (se 2 (by rfl) ⟨15342, by rfl⟩) R30685
theorem R40931 : Reach 40931 := rs (se 1 (by rfl) ⟨30698, by rfl⟩) R61397
theorem R40945 : Reach 40945 := rs (se 2 (by rfl) ⟨15354, by rfl⟩) R30709
theorem R106595 : Reach 106595 := rs (se 1 (by rfl) ⟨79946, by rfl⟩) R159893
theorem R41165 : Reach 41165 := rs (se 3 (by rfl) ⟨7718, by rfl⟩) R15437
theorem R41201 : Reach 41201 := rs (se 2 (by rfl) ⟨15450, by rfl⟩) R30901
theorem R41219 : Reach 41219 := rs (se 1 (by rfl) ⟨30914, by rfl⟩) R61829
theorem R74033 : Reach 74033 := rs (se 2 (by rfl) ⟨27762, by rfl⟩) R55525
theorem R41411 : Reach 41411 := rs (se 1 (by rfl) ⟨31058, by rfl⟩) R62117
theorem R41453 : Reach 41453 := rs (se 3 (by rfl) ⟨7772, by rfl⟩) R15545
theorem R41485 : Reach 41485 := rs (se 3 (by rfl) ⟨7778, by rfl⟩) R15557
theorem R41489 : Reach 41489 := rs (se 2 (by rfl) ⟨15558, by rfl⟩) R31117
theorem R41507 : Reach 41507 := rs (se 1 (by rfl) ⟨31130, by rfl⟩) R62261
theorem R41741 : Reach 41741 := rs (se 3 (by rfl) ⟨7826, by rfl⟩) R15653
theorem R41777 : Reach 41777 := rs (se 2 (by rfl) ⟨15666, by rfl⟩) R31333
theorem R41795 : Reach 41795 := rs (se 1 (by rfl) ⟨31346, by rfl⟩) R62693
theorem R107405 : Reach 107405 := rs (se 3 (by rfl) ⟨20138, by rfl⟩) R40277
theorem R42029 : Reach 42029 := rs (se 3 (by rfl) ⟨7880, by rfl⟩) R15761
theorem R42065 : Reach 42065 := rs (se 2 (by rfl) ⟨15774, by rfl⟩) R31549
theorem R42083 : Reach 42083 := rs (se 1 (by rfl) ⟨31562, by rfl⟩) R63125
theorem R42211 : Reach 42211 := rs (se 1 (by rfl) ⟨31658, by rfl⟩) R63317
theorem R42221 : Reach 42221 := rs (se 3 (by rfl) ⟨7916, by rfl⟩) R15833
theorem R75077 : Reach 75077 := rs (se 4 (by rfl) ⟨7038, by rfl⟩) R14077
theorem R42317 : Reach 42317 := rs (se 3 (by rfl) ⟨7934, by rfl⟩) R15869
theorem R42353 : Reach 42353 := rs (se 2 (by rfl) ⟨15882, by rfl⟩) R31765
theorem R42371 : Reach 42371 := rs (se 1 (by rfl) ⟨31778, by rfl⟩) R63557
theorem R42385 : Reach 42385 := rs (se 2 (by rfl) ⟨15894, by rfl⟩) R31789
theorem R42403 : Reach 42403 := rs (se 1 (by rfl) ⟨31802, by rfl⟩) R63605
theorem R75269 : Reach 75269 := rs (se 4 (by rfl) ⟨7056, by rfl⟩) R14113
theorem R42545 : Reach 42545 := rs (se 2 (by rfl) ⟨15954, by rfl⟩) R31909
theorem R42605 : Reach 42605 := rs (se 3 (by rfl) ⟨7988, by rfl⟩) R15977
theorem R42641 : Reach 42641 := rs (se 2 (by rfl) ⟨15990, by rfl⟩) R31981
theorem R42659 : Reach 42659 := rs (se 1 (by rfl) ⟨31994, by rfl⟩) R63989
theorem R173765 : Reach 173765 := rs (se 4 (by rfl) ⟨16290, by rfl⟩) R32581
theorem R75491 : Reach 75491 := rs (se 1 (by rfl) ⟨56618, by rfl⟩) R113237
theorem R75653 : Reach 75653 := rs (se 4 (by rfl) ⟨7092, by rfl⟩) R14185
theorem R42893 : Reach 42893 := rs (se 3 (by rfl) ⟨8042, by rfl⟩) R16085
theorem R42929 : Reach 42929 := rs (se 2 (by rfl) ⟨16098, by rfl⟩) R32197
theorem R42947 : Reach 42947 := rs (se 1 (by rfl) ⟨32210, by rfl⟩) R64421
theorem R108485 : Reach 108485 := rs (se 4 (by rfl) ⟨10170, by rfl⟩) R20341
theorem R75725 : Reach 75725 := rs (se 3 (by rfl) ⟨14198, by rfl⟩) R28397
theorem R75761 : Reach 75761 := rs (se 2 (by rfl) ⟨28410, by rfl⟩) R56821
theorem R75811 : Reach 75811 := rs (se 1 (by rfl) ⟨56858, by rfl⟩) R113717
theorem R141425 : Reach 141425 := rs (se 2 (by rfl) ⟨53034, by rfl⟩) R106069
theorem R43181 : Reach 43181 := rs (se 3 (by rfl) ⟨8096, by rfl⟩) R16193
theorem R43213 : Reach 43213 := rs (se 3 (by rfl) ⟨8102, by rfl⟩) R16205
theorem R43217 : Reach 43217 := rs (se 2 (by rfl) ⟨16206, by rfl⟩) R32413
theorem R43235 : Reach 43235 := rs (se 1 (by rfl) ⟨32426, by rfl⟩) R64853
theorem R76067 : Reach 76067 := rs (se 1 (by rfl) ⟨57050, by rfl⟩) R114101
theorem R43469 : Reach 43469 := rs (se 3 (by rfl) ⟨8150, by rfl⟩) R16301
theorem R43505 : Reach 43505 := rs (se 2 (by rfl) ⟨16314, by rfl⟩) R32629
theorem R43523 : Reach 43523 := rs (se 1 (by rfl) ⟨32642, by rfl⟩) R65285
theorem R76301 : Reach 76301 := rs (se 3 (by rfl) ⟨14306, by rfl⟩) R28613
theorem R43537 : Reach 43537 := rs (se 2 (by rfl) ⟨16326, by rfl⟩) R32653
theorem R404021 : Reach 404021 := rs (se 5 (by rfl) ⟨18938, by rfl⟩) R37877
theorem R43757 : Reach 43757 := rs (se 3 (by rfl) ⟨8204, by rfl⟩) R16409
theorem R43793 : Reach 43793 := rs (se 2 (by rfl) ⟨16422, by rfl⟩) R32845
theorem R43811 : Reach 43811 := rs (se 1 (by rfl) ⟨32858, by rfl⟩) R65717
theorem R44003 : Reach 44003 := rs (se 1 (by rfl) ⟨33002, by rfl⟩) R66005
theorem R44045 : Reach 44045 := rs (se 3 (by rfl) ⟨8258, by rfl⟩) R16517
theorem R44077 : Reach 44077 := rs (se 3 (by rfl) ⟨8264, by rfl⟩) R16529
theorem R44081 : Reach 44081 := rs (se 2 (by rfl) ⟨16530, by rfl⟩) R33061
theorem R44099 : Reach 44099 := rs (se 1 (by rfl) ⟨33074, by rfl⟩) R66149
theorem R109795 : Reach 109795 := rs (se 1 (by rfl) ⟨82346, by rfl⟩) R164693
theorem R77041 : Reach 77041 := rs (se 2 (by rfl) ⟨28890, by rfl⟩) R57781
theorem R44333 : Reach 44333 := rs (se 3 (by rfl) ⟨8312, by rfl⟩) R16625
theorem R44369 : Reach 44369 := rs (se 2 (by rfl) ⟨16638, by rfl⟩) R33277
theorem R44387 : Reach 44387 := rs (se 1 (by rfl) ⟨33290, by rfl⟩) R66581
theorem R44401 : Reach 44401 := rs (se 2 (by rfl) ⟨16650, by rfl⟩) R33301
theorem R44621 : Reach 44621 := rs (se 3 (by rfl) ⟨8366, by rfl⟩) R16733
theorem R44657 : Reach 44657 := rs (se 2 (by rfl) ⟨16746, by rfl⟩) R33493
theorem R44675 : Reach 44675 := rs (se 1 (by rfl) ⟨33506, by rfl⟩) R67013
theorem R143045 : Reach 143045 := rs (se 4 (by rfl) ⟨13410, by rfl⟩) R26821
theorem R110321 : Reach 110321 := rs (se 2 (by rfl) ⟨41370, by rfl⟩) R82741
theorem R44813 : Reach 44813 := rs (se 3 (by rfl) ⟨8402, by rfl⟩) R16805
theorem R306965 : Reach 306965 := rs (se 6 (by rfl) ⟨7194, by rfl⟩) R14389
theorem R44909 : Reach 44909 := rs (se 3 (by rfl) ⟨8420, by rfl⟩) R16841
theorem R44945 : Reach 44945 := rs (se 2 (by rfl) ⟨16854, by rfl⟩) R33709
theorem R44963 : Reach 44963 := rs (se 1 (by rfl) ⟨33722, by rfl⟩) R67445
theorem R44995 : Reach 44995 := rs (se 1 (by rfl) ⟨33746, by rfl⟩) R67493
theorem R45137 : Reach 45137 := rs (se 2 (by rfl) ⟨16926, by rfl⟩) R33853
theorem R45197 : Reach 45197 := rs (se 3 (by rfl) ⟨8474, by rfl⟩) R16949
theorem R45251 : Reach 45251 := rs (se 1 (by rfl) ⟨33938, by rfl⟩) R67877
theorem R45517 : Reach 45517 := rs (se 3 (by rfl) ⟨8534, by rfl⟩) R17069
theorem R45521 : Reach 45521 := rs (se 2 (by rfl) ⟨17070, by rfl⟩) R34141
theorem R12835 : Reach 12835 := rs (se 1 (by rfl) ⟨9626, by rfl⟩) R19253
theorem R12851 : Reach 12851 := rs (se 1 (by rfl) ⟨9638, by rfl⟩) R19277
theorem R12867 : Reach 12867 := rs (se 1 (by rfl) ⟨9650, by rfl⟩) R19301
theorem R12883 : Reach 12883 := rs (se 1 (by rfl) ⟨9662, by rfl⟩) R19325
theorem R12899 : Reach 12899 := rs (se 1 (by rfl) ⟨9674, by rfl⟩) R19349
theorem R12915 : Reach 12915 := rs (se 1 (by rfl) ⟨9686, by rfl⟩) R19373
theorem R12931 : Reach 12931 := rs (se 1 (by rfl) ⟨9698, by rfl⟩) R19397
theorem R12947 : Reach 12947 := rs (se 1 (by rfl) ⟨9710, by rfl⟩) R19421
theorem R12963 : Reach 12963 := rs (se 1 (by rfl) ⟨9722, by rfl⟩) R19445
theorem R12979 : Reach 12979 := rs (se 1 (by rfl) ⟨9734, by rfl⟩) R19469
theorem R12995 : Reach 12995 := rs (se 1 (by rfl) ⟨9746, by rfl⟩) R19493
theorem R13011 : Reach 13011 := rs (se 1 (by rfl) ⟨9758, by rfl⟩) R19517
theorem R13027 : Reach 13027 := rs (se 1 (by rfl) ⟨9770, by rfl⟩) R19541
theorem R13043 : Reach 13043 := rs (se 1 (by rfl) ⟨9782, by rfl⟩) R19565
theorem R13059 : Reach 13059 := rs (se 1 (by rfl) ⟨9794, by rfl⟩) R19589
theorem R13075 : Reach 13075 := rs (se 1 (by rfl) ⟨9806, by rfl⟩) R19613
theorem R13091 : Reach 13091 := rs (se 1 (by rfl) ⟨9818, by rfl⟩) R19637
theorem R45859 : Reach 45859 := rs (se 1 (by rfl) ⟨34394, by rfl⟩) R68789
theorem R78641 : Reach 78641 := rs (se 2 (by rfl) ⟨29490, by rfl⟩) R58981
theorem R13107 : Reach 13107 := rs (se 1 (by rfl) ⟨9830, by rfl⟩) R19661
theorem R13123 : Reach 13123 := rs (se 1 (by rfl) ⟨9842, by rfl⟩) R19685
theorem R13139 : Reach 13139 := rs (se 1 (by rfl) ⟨9854, by rfl⟩) R19709
theorem R13155 : Reach 13155 := rs (se 1 (by rfl) ⟨9866, by rfl⟩) R19733
theorem R13171 : Reach 13171 := rs (se 1 (by rfl) ⟨9878, by rfl⟩) R19757
theorem R13187 : Reach 13187 := rs (se 1 (by rfl) ⟨9890, by rfl⟩) R19781
theorem R13203 : Reach 13203 := rs (se 1 (by rfl) ⟨9902, by rfl⟩) R19805
theorem R13219 : Reach 13219 := rs (se 1 (by rfl) ⟨9914, by rfl⟩) R19829
theorem R13235 : Reach 13235 := rs (se 1 (by rfl) ⟨9926, by rfl⟩) R19853
theorem R13251 : Reach 13251 := rs (se 1 (by rfl) ⟨9938, by rfl⟩) R19877
theorem R13267 : Reach 13267 := rs (se 1 (by rfl) ⟨9950, by rfl⟩) R19901
theorem R13283 : Reach 13283 := rs (se 1 (by rfl) ⟨9962, by rfl⟩) R19925
theorem R13299 : Reach 13299 := rs (se 1 (by rfl) ⟨9974, by rfl⟩) R19949
theorem R13315 : Reach 13315 := rs (se 1 (by rfl) ⟨9986, by rfl⟩) R19973
theorem R78853 : Reach 78853 := rs (se 4 (by rfl) ⟨7392, by rfl⟩) R14785
theorem R13331 : Reach 13331 := rs (se 1 (by rfl) ⟨9998, by rfl⟩) R19997
theorem R13347 : Reach 13347 := rs (se 1 (by rfl) ⟨10010, by rfl⟩) R20021
theorem R46115 : Reach 46115 := rs (se 1 (by rfl) ⟨34586, by rfl⟩) R69173
theorem R46129 : Reach 46129 := rs (se 2 (by rfl) ⟨17298, by rfl⟩) R34597
theorem R13363 : Reach 13363 := rs (se 1 (by rfl) ⟨10022, by rfl⟩) R20045
theorem R13379 : Reach 13379 := rs (se 1 (by rfl) ⟨10034, by rfl⟩) R20069
theorem R13395 : Reach 13395 := rs (se 1 (by rfl) ⟨10046, by rfl⟩) R20093
theorem R13411 : Reach 13411 := rs (se 1 (by rfl) ⟨10058, by rfl⟩) R20117
theorem R13427 : Reach 13427 := rs (se 1 (by rfl) ⟨10070, by rfl⟩) R20141
theorem R13443 : Reach 13443 := rs (se 1 (by rfl) ⟨10082, by rfl⟩) R20165
theorem R13459 : Reach 13459 := rs (se 1 (by rfl) ⟨10094, by rfl⟩) R20189
theorem R13475 : Reach 13475 := rs (se 1 (by rfl) ⟨10106, by rfl⟩) R20213
theorem R13491 : Reach 13491 := rs (se 1 (by rfl) ⟨10118, by rfl⟩) R20237
theorem R13507 : Reach 13507 := rs (se 1 (by rfl) ⟨10130, by rfl⟩) R20261
theorem R177349 : Reach 177349 := rs (se 4 (by rfl) ⟨16626, by rfl⟩) R33253
theorem R13523 : Reach 13523 := rs (se 1 (by rfl) ⟨10142, by rfl⟩) R20285
theorem R46307 : Reach 46307 := rs (se 1 (by rfl) ⟨34730, by rfl⟩) R69461
theorem R13539 : Reach 13539 := rs (se 1 (by rfl) ⟨10154, by rfl⟩) R20309
theorem R13555 : Reach 13555 := rs (se 1 (by rfl) ⟨10166, by rfl⟩) R20333
theorem R13571 : Reach 13571 := rs (se 1 (by rfl) ⟨10178, by rfl⟩) R20357
theorem R13587 : Reach 13587 := rs (se 1 (by rfl) ⟨10190, by rfl⟩) R20381
theorem R13603 : Reach 13603 := rs (se 1 (by rfl) ⟨10202, by rfl⟩) R20405
theorem R46385 : Reach 46385 := rs (se 2 (by rfl) ⟨17394, by rfl⟩) R34789
theorem R13619 : Reach 13619 := rs (se 1 (by rfl) ⟨10214, by rfl⟩) R20429
theorem R13635 : Reach 13635 := rs (se 1 (by rfl) ⟨10226, by rfl⟩) R20453
theorem R13651 : Reach 13651 := rs (se 1 (by rfl) ⟨10238, by rfl⟩) R20477
theorem R13667 : Reach 13667 := rs (se 1 (by rfl) ⟨10250, by rfl⟩) R20501
theorem R79217 : Reach 79217 := rs (se 2 (by rfl) ⟨29706, by rfl⟩) R59413
theorem R13683 : Reach 13683 := rs (se 1 (by rfl) ⟨10262, by rfl⟩) R20525
theorem R13699 : Reach 13699 := rs (se 1 (by rfl) ⟨10274, by rfl⟩) R20549
theorem R13715 : Reach 13715 := rs (se 1 (by rfl) ⟨10286, by rfl⟩) R20573
theorem R13731 : Reach 13731 := rs (se 1 (by rfl) ⟨10298, by rfl⟩) R20597
theorem R13747 : Reach 13747 := rs (se 1 (by rfl) ⟨10310, by rfl⟩) R20621
theorem R13763 : Reach 13763 := rs (se 1 (by rfl) ⟨10322, by rfl⟩) R20645
theorem R79309 : Reach 79309 := rs (se 3 (by rfl) ⟨14870, by rfl⟩) R29741
theorem R13779 : Reach 13779 := rs (se 1 (by rfl) ⟨10334, by rfl⟩) R20669
theorem R13795 : Reach 13795 := rs (se 1 (by rfl) ⟨10346, by rfl⟩) R20693
theorem R46577 : Reach 46577 := rs (se 2 (by rfl) ⟨17466, by rfl⟩) R34933
theorem R13811 : Reach 13811 := rs (se 1 (by rfl) ⟨10358, by rfl⟩) R20717
theorem R13827 : Reach 13827 := rs (se 1 (by rfl) ⟨10370, by rfl⟩) R20741
theorem R13843 : Reach 13843 := rs (se 1 (by rfl) ⟨10382, by rfl⟩) R20765
theorem R13859 : Reach 13859 := rs (se 1 (by rfl) ⟨10394, by rfl⟩) R20789
theorem R13875 : Reach 13875 := rs (se 1 (by rfl) ⟨10406, by rfl⟩) R20813
theorem R13891 : Reach 13891 := rs (se 1 (by rfl) ⟨10418, by rfl⟩) R20837
theorem R13907 : Reach 13907 := rs (se 1 (by rfl) ⟨10430, by rfl⟩) R20861
theorem R13923 : Reach 13923 := rs (se 1 (by rfl) ⟨10442, by rfl⟩) R20885
theorem R13939 : Reach 13939 := rs (se 1 (by rfl) ⟨10454, by rfl⟩) R20909
theorem R13955 : Reach 13955 := rs (se 1 (by rfl) ⟨10466, by rfl⟩) R20933
theorem R13971 : Reach 13971 := rs (se 1 (by rfl) ⟨10478, by rfl⟩) R20957
theorem R13987 : Reach 13987 := rs (se 1 (by rfl) ⟨10490, by rfl⟩) R20981
theorem R14003 : Reach 14003 := rs (se 1 (by rfl) ⟨10502, by rfl⟩) R21005
theorem R14019 : Reach 14019 := rs (se 1 (by rfl) ⟨10514, by rfl⟩) R21029
theorem R14035 : Reach 14035 := rs (se 1 (by rfl) ⟨10526, by rfl⟩) R21053
theorem R14051 : Reach 14051 := rs (se 1 (by rfl) ⟨10538, by rfl⟩) R21077
theorem R14067 : Reach 14067 := rs (se 1 (by rfl) ⟨10550, by rfl⟩) R21101
theorem R14083 : Reach 14083 := rs (se 1 (by rfl) ⟨10562, by rfl⟩) R21125
theorem R14099 : Reach 14099 := rs (se 1 (by rfl) ⟨10574, by rfl⟩) R21149
theorem R14115 : Reach 14115 := rs (se 1 (by rfl) ⟨10586, by rfl⟩) R21173
theorem R14131 : Reach 14131 := rs (se 1 (by rfl) ⟨10598, by rfl⟩) R21197
theorem R14147 : Reach 14147 := rs (se 1 (by rfl) ⟨10610, by rfl⟩) R21221
theorem R46925 : Reach 46925 := rs (se 3 (by rfl) ⟨8798, by rfl⟩) R17597
theorem R14163 : Reach 14163 := rs (se 1 (by rfl) ⟨10622, by rfl⟩) R21245
theorem R14179 : Reach 14179 := rs (se 1 (by rfl) ⟨10634, by rfl⟩) R21269
theorem R14195 : Reach 14195 := rs (se 1 (by rfl) ⟨10646, by rfl⟩) R21293
theorem R14211 : Reach 14211 := rs (se 1 (by rfl) ⟨10658, by rfl⟩) R21317
theorem R14227 : Reach 14227 := rs (se 1 (by rfl) ⟨10670, by rfl⟩) R21341
theorem R14243 : Reach 14243 := rs (se 1 (by rfl) ⟨10682, by rfl⟩) R21365
theorem R14259 : Reach 14259 := rs (se 1 (by rfl) ⟨10694, by rfl⟩) R21389
theorem R14275 : Reach 14275 := rs (se 1 (by rfl) ⟨10706, by rfl⟩) R21413
theorem R14291 : Reach 14291 := rs (se 1 (by rfl) ⟨10718, by rfl⟩) R21437
theorem R14307 : Reach 14307 := rs (se 1 (by rfl) ⟨10730, by rfl⟩) R21461
theorem R14323 : Reach 14323 := rs (se 1 (by rfl) ⟨10742, by rfl⟩) R21485
theorem R14339 : Reach 14339 := rs (se 1 (by rfl) ⟨10754, by rfl⟩) R21509
theorem R14355 : Reach 14355 := rs (se 1 (by rfl) ⟨10766, by rfl⟩) R21533
theorem R14371 : Reach 14371 := rs (se 1 (by rfl) ⟨10778, by rfl⟩) R21557
theorem R14387 : Reach 14387 := rs (se 1 (by rfl) ⟨10790, by rfl⟩) R21581
theorem R14403 : Reach 14403 := rs (se 1 (by rfl) ⟨10802, by rfl⟩) R21605
theorem R14419 : Reach 14419 := rs (se 1 (by rfl) ⟨10814, by rfl⟩) R21629
theorem R14435 : Reach 14435 := rs (se 1 (by rfl) ⟨10826, by rfl⟩) R21653
theorem R14451 : Reach 14451 := rs (se 1 (by rfl) ⟨10838, by rfl⟩) R21677
theorem R14467 : Reach 14467 := rs (se 1 (by rfl) ⟨10850, by rfl⟩) R21701
theorem R14483 : Reach 14483 := rs (se 1 (by rfl) ⟨10862, by rfl⟩) R21725
theorem R14499 : Reach 14499 := rs (se 1 (by rfl) ⟨10874, by rfl⟩) R21749
theorem R14515 : Reach 14515 := rs (se 1 (by rfl) ⟨10886, by rfl⟩) R21773
theorem R14531 : Reach 14531 := rs (se 1 (by rfl) ⟨10898, by rfl⟩) R21797
theorem R14547 : Reach 14547 := rs (se 1 (by rfl) ⟨10910, by rfl⟩) R21821
theorem R80099 : Reach 80099 := rs (se 1 (by rfl) ⟨60074, by rfl⟩) R120149
theorem R14563 : Reach 14563 := rs (se 1 (by rfl) ⟨10922, by rfl⟩) R21845
theorem R14579 : Reach 14579 := rs (se 1 (by rfl) ⟨10934, by rfl⟩) R21869
theorem R14595 : Reach 14595 := rs (se 1 (by rfl) ⟨10946, by rfl⟩) R21893
theorem R14611 : Reach 14611 := rs (se 1 (by rfl) ⟨10958, by rfl⟩) R21917
theorem R14627 : Reach 14627 := rs (se 1 (by rfl) ⟨10970, by rfl⟩) R21941
theorem R14643 : Reach 14643 := rs (se 1 (by rfl) ⟨10982, by rfl⟩) R21965
theorem R14659 : Reach 14659 := rs (se 1 (by rfl) ⟨10994, by rfl⟩) R21989
theorem R14675 : Reach 14675 := rs (se 1 (by rfl) ⟨11006, by rfl⟩) R22013
theorem R14691 : Reach 14691 := rs (se 1 (by rfl) ⟨11018, by rfl⟩) R22037
theorem R14707 : Reach 14707 := rs (se 1 (by rfl) ⟨11030, by rfl⟩) R22061
theorem R14723 : Reach 14723 := rs (se 1 (by rfl) ⟨11042, by rfl⟩) R22085
theorem R14739 : Reach 14739 := rs (se 1 (by rfl) ⟨11054, by rfl⟩) R22109
theorem R14755 : Reach 14755 := rs (se 1 (by rfl) ⟨11066, by rfl⟩) R22133
theorem R47537 : Reach 47537 := rs (se 2 (by rfl) ⟨17826, by rfl⟩) R35653
theorem R14771 : Reach 14771 := rs (se 1 (by rfl) ⟨11078, by rfl⟩) R22157
theorem R14787 : Reach 14787 := rs (se 1 (by rfl) ⟨11090, by rfl⟩) R22181
theorem R14803 : Reach 14803 := rs (se 1 (by rfl) ⟨11102, by rfl⟩) R22205
theorem R14819 : Reach 14819 := rs (se 1 (by rfl) ⟨11114, by rfl⟩) R22229
theorem R47587 : Reach 47587 := rs (se 1 (by rfl) ⟨35690, by rfl⟩) R71381
theorem R14835 : Reach 14835 := rs (se 1 (by rfl) ⟨11126, by rfl⟩) R22253
theorem R14851 : Reach 14851 := rs (se 1 (by rfl) ⟨11138, by rfl⟩) R22277
theorem R14867 : Reach 14867 := rs (se 1 (by rfl) ⟨11150, by rfl⟩) R22301
theorem R14883 : Reach 14883 := rs (se 1 (by rfl) ⟨11162, by rfl⟩) R22325
theorem R14899 : Reach 14899 := rs (se 1 (by rfl) ⟨11174, by rfl⟩) R22349
theorem R14915 : Reach 14915 := rs (se 1 (by rfl) ⟨11186, by rfl⟩) R22373
theorem R14931 : Reach 14931 := rs (se 1 (by rfl) ⟨11198, by rfl⟩) R22397
theorem R178787 : Reach 178787 := rs (se 1 (by rfl) ⟨134090, by rfl⟩) R268181
theorem R14947 : Reach 14947 := rs (se 1 (by rfl) ⟨11210, by rfl⟩) R22421
theorem R47729 : Reach 47729 := rs (se 2 (by rfl) ⟨17898, by rfl⟩) R35797
theorem R14963 : Reach 14963 := rs (se 1 (by rfl) ⟨11222, by rfl⟩) R22445
theorem R14979 : Reach 14979 := rs (se 1 (by rfl) ⟨11234, by rfl⟩) R22469
theorem R14995 : Reach 14995 := rs (se 1 (by rfl) ⟨11246, by rfl⟩) R22493
theorem R15011 : Reach 15011 := rs (se 1 (by rfl) ⟨11258, by rfl⟩) R22517
theorem R15027 : Reach 15027 := rs (se 1 (by rfl) ⟨11270, by rfl⟩) R22541
theorem R15043 : Reach 15043 := rs (se 1 (by rfl) ⟨11282, by rfl⟩) R22565
theorem R15059 : Reach 15059 := rs (se 1 (by rfl) ⟨11294, by rfl⟩) R22589
theorem R47843 : Reach 47843 := rs (se 1 (by rfl) ⟨35882, by rfl⟩) R71765
theorem R15075 : Reach 15075 := rs (se 1 (by rfl) ⟨11306, by rfl⟩) R22613
theorem R15091 : Reach 15091 := rs (se 1 (by rfl) ⟨11318, by rfl⟩) R22637
theorem R15107 : Reach 15107 := rs (se 1 (by rfl) ⟨11330, by rfl⟩) R22661
theorem R15123 : Reach 15123 := rs (se 1 (by rfl) ⟨11342, by rfl⟩) R22685
theorem R80675 : Reach 80675 := rs (se 1 (by rfl) ⟨60506, by rfl⟩) R121013
theorem R15139 : Reach 15139 := rs (se 1 (by rfl) ⟨11354, by rfl⟩) R22709
theorem R15155 : Reach 15155 := rs (se 1 (by rfl) ⟨11366, by rfl⟩) R22733
theorem R15171 : Reach 15171 := rs (se 1 (by rfl) ⟨11378, by rfl⟩) R22757
theorem R15187 : Reach 15187 := rs (se 1 (by rfl) ⟨11390, by rfl⟩) R22781
theorem R15203 : Reach 15203 := rs (se 1 (by rfl) ⟨11402, by rfl⟩) R22805
theorem R15219 : Reach 15219 := rs (se 1 (by rfl) ⟨11414, by rfl⟩) R22829
theorem R15235 : Reach 15235 := rs (se 1 (by rfl) ⟨11426, by rfl⟩) R22853
theorem R15251 : Reach 15251 := rs (se 1 (by rfl) ⟨11438, by rfl⟩) R22877
theorem R15267 : Reach 15267 := rs (se 1 (by rfl) ⟨11450, by rfl⟩) R22901
theorem R15283 : Reach 15283 := rs (se 1 (by rfl) ⟨11462, by rfl⟩) R22925
theorem R15299 : Reach 15299 := rs (se 1 (by rfl) ⟨11474, by rfl⟩) R22949
theorem R80837 : Reach 80837 := rs (se 4 (by rfl) ⟨7578, by rfl⟩) R15157
theorem R15315 : Reach 15315 := rs (se 1 (by rfl) ⟨11486, by rfl⟩) R22973
theorem R15331 : Reach 15331 := rs (se 1 (by rfl) ⟨11498, by rfl⟩) R22997
theorem R48113 : Reach 48113 := rs (se 2 (by rfl) ⟨18042, by rfl⟩) R36085
theorem R15347 : Reach 15347 := rs (se 1 (by rfl) ⟨11510, by rfl⟩) R23021
theorem R15363 : Reach 15363 := rs (se 1 (by rfl) ⟨11522, by rfl⟩) R23045
theorem R15379 : Reach 15379 := rs (se 1 (by rfl) ⟨11534, by rfl⟩) R23069
theorem R15395 : Reach 15395 := rs (se 1 (by rfl) ⟨11546, by rfl⟩) R23093
theorem R15411 : Reach 15411 := rs (se 1 (by rfl) ⟨11558, by rfl⟩) R23117
theorem R15427 : Reach 15427 := rs (se 1 (by rfl) ⟨11570, by rfl⟩) R23141
theorem R48205 : Reach 48205 := rs (se 3 (by rfl) ⟨9038, by rfl⟩) R18077
theorem R15443 : Reach 15443 := rs (se 1 (by rfl) ⟨11582, by rfl⟩) R23165
theorem R15459 : Reach 15459 := rs (se 1 (by rfl) ⟨11594, by rfl⟩) R23189
theorem R15475 : Reach 15475 := rs (se 1 (by rfl) ⟨11606, by rfl⟩) R23213
theorem R15491 : Reach 15491 := rs (se 1 (by rfl) ⟨11618, by rfl⟩) R23237
theorem R15507 : Reach 15507 := rs (se 1 (by rfl) ⟨11630, by rfl⟩) R23261
theorem R15523 : Reach 15523 := rs (se 1 (by rfl) ⟨11642, by rfl⟩) R23285
theorem R15539 : Reach 15539 := rs (se 1 (by rfl) ⟨11654, by rfl⟩) R23309
theorem R15555 : Reach 15555 := rs (se 1 (by rfl) ⟨11666, by rfl⟩) R23333
theorem R81101 : Reach 81101 := rs (se 3 (by rfl) ⟨15206, by rfl⟩) R30413
theorem R15571 : Reach 15571 := rs (se 1 (by rfl) ⟨11678, by rfl⟩) R23357
theorem R15587 : Reach 15587 := rs (se 1 (by rfl) ⟨11690, by rfl⟩) R23381
theorem R15603 : Reach 15603 := rs (se 1 (by rfl) ⟨11702, by rfl⟩) R23405
theorem R15619 : Reach 15619 := rs (se 1 (by rfl) ⟨11714, by rfl⟩) R23429
theorem R48397 : Reach 48397 := rs (se 3 (by rfl) ⟨9074, by rfl⟩) R18149
theorem R15635 : Reach 15635 := rs (se 1 (by rfl) ⟨11726, by rfl⟩) R23453
theorem R15651 : Reach 15651 := rs (se 1 (by rfl) ⟨11738, by rfl⟩) R23477
theorem R48433 : Reach 48433 := rs (se 2 (by rfl) ⟨18162, by rfl⟩) R36325
theorem R15667 : Reach 15667 := rs (se 1 (by rfl) ⟨11750, by rfl⟩) R23501
theorem R15683 : Reach 15683 := rs (se 1 (by rfl) ⟨11762, by rfl⟩) R23525
theorem R15699 : Reach 15699 := rs (se 1 (by rfl) ⟨11774, by rfl⟩) R23549
theorem R15715 : Reach 15715 := rs (se 1 (by rfl) ⟨11786, by rfl⟩) R23573
theorem R15731 : Reach 15731 := rs (se 1 (by rfl) ⟨11798, by rfl⟩) R23597
theorem R15747 : Reach 15747 := rs (se 1 (by rfl) ⟨11810, by rfl⟩) R23621
theorem R15763 : Reach 15763 := rs (se 1 (by rfl) ⟨11822, by rfl⟩) R23645
theorem R15779 : Reach 15779 := rs (se 1 (by rfl) ⟨11834, by rfl⟩) R23669
theorem R15795 : Reach 15795 := rs (se 1 (by rfl) ⟨11846, by rfl⟩) R23693
theorem R15811 : Reach 15811 := rs (se 1 (by rfl) ⟨11858, by rfl⟩) R23717
theorem R15827 : Reach 15827 := rs (se 1 (by rfl) ⟨11870, by rfl⟩) R23741
theorem R15843 : Reach 15843 := rs (se 1 (by rfl) ⟨11882, by rfl⟩) R23765
theorem R15859 : Reach 15859 := rs (se 1 (by rfl) ⟨11894, by rfl⟩) R23789
theorem R15875 : Reach 15875 := rs (se 1 (by rfl) ⟨11906, by rfl⟩) R23813
theorem R48653 : Reach 48653 := rs (se 3 (by rfl) ⟨9122, by rfl⟩) R18245
theorem R15891 : Reach 15891 := rs (se 1 (by rfl) ⟨11918, by rfl⟩) R23837
theorem R15907 : Reach 15907 := rs (se 1 (by rfl) ⟨11930, by rfl⟩) R23861
theorem R15923 : Reach 15923 := rs (se 1 (by rfl) ⟨11942, by rfl⟩) R23885
theorem R15939 : Reach 15939 := rs (se 1 (by rfl) ⟨11954, by rfl⟩) R23909
theorem R81485 : Reach 81485 := rs (se 3 (by rfl) ⟨15278, by rfl⟩) R30557
theorem R15955 : Reach 15955 := rs (se 1 (by rfl) ⟨11966, by rfl⟩) R23933
theorem R15971 : Reach 15971 := rs (se 1 (by rfl) ⟨11978, by rfl⟩) R23957
theorem R15987 : Reach 15987 := rs (se 1 (by rfl) ⟨11990, by rfl⟩) R23981
theorem R16003 : Reach 16003 := rs (se 1 (by rfl) ⟨12002, by rfl⟩) R24005
theorem R16019 : Reach 16019 := rs (se 1 (by rfl) ⟨12014, by rfl⟩) R24029
theorem R16035 : Reach 16035 := rs (se 1 (by rfl) ⟨12026, by rfl⟩) R24053
theorem R16051 : Reach 16051 := rs (se 1 (by rfl) ⟨12038, by rfl⟩) R24077
theorem R16067 : Reach 16067 := rs (se 1 (by rfl) ⟨12050, by rfl⟩) R24101
theorem R16083 : Reach 16083 := rs (se 1 (by rfl) ⟨12062, by rfl⟩) R24125
theorem R16099 : Reach 16099 := rs (se 1 (by rfl) ⟨12074, by rfl⟩) R24149
theorem R16115 : Reach 16115 := rs (se 1 (by rfl) ⟨12086, by rfl⟩) R24173
theorem R16131 : Reach 16131 := rs (se 1 (by rfl) ⟨12098, by rfl⟩) R24197
theorem R16147 : Reach 16147 := rs (se 1 (by rfl) ⟨12110, by rfl⟩) R24221
theorem R16163 : Reach 16163 := rs (se 1 (by rfl) ⟨12122, by rfl⟩) R24245
theorem R16179 : Reach 16179 := rs (se 1 (by rfl) ⟨12134, by rfl⟩) R24269
theorem R16195 : Reach 16195 := rs (se 1 (by rfl) ⟨12146, by rfl⟩) R24293
theorem R16211 : Reach 16211 := rs (se 1 (by rfl) ⟨12158, by rfl⟩) R24317
theorem R48995 : Reach 48995 := rs (se 1 (by rfl) ⟨36746, by rfl⟩) R73493
theorem R16227 : Reach 16227 := rs (se 1 (by rfl) ⟨12170, by rfl⟩) R24341
theorem R16243 : Reach 16243 := rs (se 1 (by rfl) ⟨12182, by rfl⟩) R24365
theorem R16259 : Reach 16259 := rs (se 1 (by rfl) ⟨12194, by rfl⟩) R24389
theorem R442253 : Reach 442253 := rs (se 3 (by rfl) ⟨82922, by rfl⟩) R165845
theorem R16275 : Reach 16275 := rs (se 1 (by rfl) ⟨12206, by rfl⟩) R24413
theorem R16291 : Reach 16291 := rs (se 1 (by rfl) ⟨12218, by rfl⟩) R24437
theorem R16307 : Reach 16307 := rs (se 1 (by rfl) ⟨12230, by rfl⟩) R24461
theorem R16323 : Reach 16323 := rs (se 1 (by rfl) ⟨12242, by rfl⟩) R24485
theorem R16339 : Reach 16339 := rs (se 1 (by rfl) ⟨12254, by rfl⟩) R24509
theorem R16355 : Reach 16355 := rs (se 1 (by rfl) ⟨12266, by rfl⟩) R24533
theorem R16371 : Reach 16371 := rs (se 1 (by rfl) ⟨12278, by rfl⟩) R24557
theorem R16387 : Reach 16387 := rs (se 1 (by rfl) ⟨12290, by rfl⟩) R24581
theorem R16403 : Reach 16403 := rs (se 1 (by rfl) ⟨12302, by rfl⟩) R24605
theorem R16419 : Reach 16419 := rs (se 1 (by rfl) ⟨12314, by rfl⟩) R24629
theorem R49187 : Reach 49187 := rs (se 1 (by rfl) ⟨36890, by rfl⟩) R73781
theorem R16435 : Reach 16435 := rs (se 1 (by rfl) ⟨12326, by rfl⟩) R24653
theorem R16451 : Reach 16451 := rs (se 1 (by rfl) ⟨12338, by rfl⟩) R24677
theorem R16467 : Reach 16467 := rs (se 1 (by rfl) ⟨12350, by rfl⟩) R24701
theorem R16483 : Reach 16483 := rs (se 1 (by rfl) ⟨12362, by rfl⟩) R24725
theorem R16499 : Reach 16499 := rs (se 1 (by rfl) ⟨12374, by rfl⟩) R24749
theorem R16515 : Reach 16515 := rs (se 1 (by rfl) ⟨12386, by rfl⟩) R24773
theorem R16531 : Reach 16531 := rs (se 1 (by rfl) ⟨12398, by rfl⟩) R24797
theorem R16547 : Reach 16547 := rs (se 1 (by rfl) ⟨12410, by rfl⟩) R24821
theorem R16563 : Reach 16563 := rs (se 1 (by rfl) ⟨12422, by rfl⟩) R24845
theorem R16579 : Reach 16579 := rs (se 1 (by rfl) ⟨12434, by rfl⟩) R24869
theorem R16595 : Reach 16595 := rs (se 1 (by rfl) ⟨12446, by rfl⟩) R24893
theorem R16611 : Reach 16611 := rs (se 1 (by rfl) ⟨12458, by rfl⟩) R24917
theorem R16627 : Reach 16627 := rs (se 1 (by rfl) ⟨12470, by rfl⟩) R24941
theorem R16643 : Reach 16643 := rs (se 1 (by rfl) ⟨12482, by rfl⟩) R24965
theorem R16659 : Reach 16659 := rs (se 1 (by rfl) ⟨12494, by rfl⟩) R24989
theorem R16675 : Reach 16675 := rs (se 1 (by rfl) ⟨12506, by rfl⟩) R25013
theorem R16691 : Reach 16691 := rs (se 1 (by rfl) ⟨12518, by rfl⟩) R25037
theorem R16707 : Reach 16707 := rs (se 1 (by rfl) ⟨12530, by rfl⟩) R25061
theorem R16723 : Reach 16723 := rs (se 1 (by rfl) ⟨12542, by rfl⟩) R25085
theorem R16739 : Reach 16739 := rs (se 1 (by rfl) ⟨12554, by rfl⟩) R25109
theorem R147811 : Reach 147811 := rs (se 1 (by rfl) ⟨110858, by rfl⟩) R221717
theorem R16755 : Reach 16755 := rs (se 1 (by rfl) ⟨12566, by rfl⟩) R25133
theorem R16771 : Reach 16771 := rs (se 1 (by rfl) ⟨12578, by rfl⟩) R25157
theorem R82309 : Reach 82309 := rs (se 4 (by rfl) ⟨7716, by rfl⟩) R15433
theorem R16787 : Reach 16787 := rs (se 1 (by rfl) ⟨12590, by rfl⟩) R25181
theorem R49571 : Reach 49571 := rs (se 1 (by rfl) ⟨37178, by rfl⟩) R74357
theorem R16803 : Reach 16803 := rs (se 1 (by rfl) ⟨12602, by rfl⟩) R25205
theorem R16819 : Reach 16819 := rs (se 1 (by rfl) ⟨12614, by rfl⟩) R25229
theorem R16835 : Reach 16835 := rs (se 1 (by rfl) ⟨12626, by rfl⟩) R25253
theorem R16851 : Reach 16851 := rs (se 1 (by rfl) ⟨12638, by rfl⟩) R25277
theorem R16867 : Reach 16867 := rs (se 1 (by rfl) ⟨12650, by rfl⟩) R25301
theorem R16883 : Reach 16883 := rs (se 1 (by rfl) ⟨12662, by rfl⟩) R25325
theorem R16899 : Reach 16899 := rs (se 1 (by rfl) ⟨12674, by rfl⟩) R25349
theorem R16915 : Reach 16915 := rs (se 1 (by rfl) ⟨12686, by rfl⟩) R25373
theorem R16931 : Reach 16931 := rs (se 1 (by rfl) ⟨12698, by rfl⟩) R25397
theorem R16947 : Reach 16947 := rs (se 1 (by rfl) ⟨12710, by rfl⟩) R25421
theorem R16963 : Reach 16963 := rs (se 1 (by rfl) ⟨12722, by rfl⟩) R25445
theorem R16979 : Reach 16979 := rs (se 1 (by rfl) ⟨12734, by rfl⟩) R25469
theorem R16995 : Reach 16995 := rs (se 1 (by rfl) ⟨12746, by rfl⟩) R25493
theorem R17011 : Reach 17011 := rs (se 1 (by rfl) ⟨12758, by rfl⟩) R25517
theorem R17027 : Reach 17027 := rs (se 1 (by rfl) ⟨12770, by rfl⟩) R25541
theorem R49805 : Reach 49805 := rs (se 3 (by rfl) ⟨9338, by rfl⟩) R18677
theorem R17043 : Reach 17043 := rs (se 1 (by rfl) ⟨12782, by rfl⟩) R25565
theorem R17059 : Reach 17059 := rs (se 1 (by rfl) ⟨12794, by rfl⟩) R25589
theorem R49841 : Reach 49841 := rs (se 2 (by rfl) ⟨18690, by rfl⟩) R37381
theorem R17075 : Reach 17075 := rs (se 1 (by rfl) ⟨12806, by rfl⟩) R25613
theorem R17091 : Reach 17091 := rs (se 1 (by rfl) ⟨12818, by rfl⟩) R25637
theorem R17105 : Reach 17105 := rs (se 2 (by rfl) ⟨6414, by rfl⟩) R12829
theorem R17107 : Reach 17107 := rs (se 1 (by rfl) ⟨12830, by rfl⟩) R25661
theorem R17121 : Reach 17121 := rs (se 2 (by rfl) ⟨6420, by rfl⟩) R12841
theorem R17123 : Reach 17123 := rs (se 1 (by rfl) ⟨12842, by rfl⟩) R25685
theorem R49891 : Reach 49891 := rs (se 1 (by rfl) ⟨37418, by rfl⟩) R74837
theorem R17137 : Reach 17137 := rs (se 2 (by rfl) ⟨6426, by rfl⟩) R12853
theorem R17139 : Reach 17139 := rs (se 1 (by rfl) ⟨12854, by rfl⟩) R25709
theorem R17153 : Reach 17153 := rs (se 2 (by rfl) ⟨6432, by rfl⟩) R12865
theorem R17155 : Reach 17155 := rs (se 1 (by rfl) ⟨12866, by rfl⟩) R25733
theorem R17169 : Reach 17169 := rs (se 2 (by rfl) ⟨6438, by rfl⟩) R12877
theorem R17171 : Reach 17171 := rs (se 1 (by rfl) ⟨12878, by rfl⟩) R25757
theorem R17185 : Reach 17185 := rs (se 2 (by rfl) ⟨6444, by rfl⟩) R12889
theorem R17187 : Reach 17187 := rs (se 1 (by rfl) ⟨12890, by rfl⟩) R25781
theorem R17201 : Reach 17201 := rs (se 2 (by rfl) ⟨6450, by rfl⟩) R12901
theorem R17203 : Reach 17203 := rs (se 1 (by rfl) ⟨12902, by rfl⟩) R25805
theorem R17217 : Reach 17217 := rs (se 2 (by rfl) ⟨6456, by rfl⟩) R12913
theorem R17219 : Reach 17219 := rs (se 1 (by rfl) ⟨12914, by rfl⟩) R25829
theorem R49997 : Reach 49997 := rs (se 3 (by rfl) ⟨9374, by rfl⟩) R18749
theorem R17233 : Reach 17233 := rs (se 2 (by rfl) ⟨6462, by rfl⟩) R12925
theorem R17235 : Reach 17235 := rs (se 1 (by rfl) ⟨12926, by rfl⟩) R25853
theorem R17249 : Reach 17249 := rs (se 2 (by rfl) ⟨6468, by rfl⟩) R12937
theorem R17251 : Reach 17251 := rs (se 1 (by rfl) ⟨12938, by rfl⟩) R25877
theorem R17265 : Reach 17265 := rs (se 2 (by rfl) ⟨6474, by rfl⟩) R12949
theorem R17267 : Reach 17267 := rs (se 1 (by rfl) ⟨12950, by rfl⟩) R25901
theorem R17281 : Reach 17281 := rs (se 2 (by rfl) ⟨6480, by rfl⟩) R12961
theorem R17283 : Reach 17283 := rs (se 1 (by rfl) ⟨12962, by rfl⟩) R25925
theorem R17297 : Reach 17297 := rs (se 2 (by rfl) ⟨6486, by rfl⟩) R12973
theorem R17299 : Reach 17299 := rs (se 1 (by rfl) ⟨12974, by rfl⟩) R25949
theorem R17313 : Reach 17313 := rs (se 2 (by rfl) ⟨6492, by rfl⟩) R12985
theorem R17315 : Reach 17315 := rs (se 1 (by rfl) ⟨12986, by rfl⟩) R25973
theorem R17329 : Reach 17329 := rs (se 2 (by rfl) ⟨6498, by rfl⟩) R12997
theorem R17331 : Reach 17331 := rs (se 1 (by rfl) ⟨12998, by rfl⟩) R25997
theorem R17345 : Reach 17345 := rs (se 2 (by rfl) ⟨6504, by rfl⟩) R13009
theorem R17347 : Reach 17347 := rs (se 1 (by rfl) ⟨13010, by rfl⟩) R26021
theorem R17361 : Reach 17361 := rs (se 2 (by rfl) ⟨6510, by rfl⟩) R13021
theorem R17363 : Reach 17363 := rs (se 1 (by rfl) ⟨13022, by rfl⟩) R26045
theorem R17377 : Reach 17377 := rs (se 2 (by rfl) ⟨6516, by rfl⟩) R13033
theorem R17379 : Reach 17379 := rs (se 1 (by rfl) ⟨13034, by rfl⟩) R26069
theorem R17393 : Reach 17393 := rs (se 2 (by rfl) ⟨6522, by rfl⟩) R13045
theorem R17395 : Reach 17395 := rs (se 1 (by rfl) ⟨13046, by rfl⟩) R26093
theorem R17409 : Reach 17409 := rs (se 2 (by rfl) ⟨6528, by rfl⟩) R13057
theorem R17411 : Reach 17411 := rs (se 1 (by rfl) ⟨13058, by rfl⟩) R26117
theorem R17425 : Reach 17425 := rs (se 2 (by rfl) ⟨6534, by rfl⟩) R13069
theorem R17427 : Reach 17427 := rs (se 1 (by rfl) ⟨13070, by rfl⟩) R26141
theorem R17441 : Reach 17441 := rs (se 2 (by rfl) ⟨6540, by rfl⟩) R13081
theorem R17443 : Reach 17443 := rs (se 1 (by rfl) ⟨13082, by rfl⟩) R26165
theorem R17457 : Reach 17457 := rs (se 2 (by rfl) ⟨6546, by rfl⟩) R13093
theorem R17459 : Reach 17459 := rs (se 1 (by rfl) ⟨13094, by rfl⟩) R26189
theorem R17473 : Reach 17473 := rs (se 2 (by rfl) ⟨6552, by rfl⟩) R13105
theorem R17475 : Reach 17475 := rs (se 1 (by rfl) ⟨13106, by rfl⟩) R26213
theorem R17489 : Reach 17489 := rs (se 2 (by rfl) ⟨6558, by rfl⟩) R13117
theorem R17491 : Reach 17491 := rs (se 1 (by rfl) ⟨13118, by rfl⟩) R26237
theorem R17505 : Reach 17505 := rs (se 2 (by rfl) ⟨6564, by rfl⟩) R13129
theorem R17507 : Reach 17507 := rs (se 1 (by rfl) ⟨13130, by rfl⟩) R26261
theorem R17521 : Reach 17521 := rs (se 2 (by rfl) ⟨6570, by rfl⟩) R13141
theorem R17523 : Reach 17523 := rs (se 1 (by rfl) ⟨13142, by rfl⟩) R26285
theorem R17537 : Reach 17537 := rs (se 2 (by rfl) ⟨6576, by rfl⟩) R13153
theorem R17539 : Reach 17539 := rs (se 1 (by rfl) ⟨13154, by rfl⟩) R26309
theorem R17553 : Reach 17553 := rs (se 2 (by rfl) ⟨6582, by rfl⟩) R13165
theorem R17555 : Reach 17555 := rs (se 1 (by rfl) ⟨13166, by rfl⟩) R26333
theorem R17569 : Reach 17569 := rs (se 2 (by rfl) ⟨6588, by rfl⟩) R13177
theorem R17571 : Reach 17571 := rs (se 1 (by rfl) ⟨13178, by rfl⟩) R26357
theorem R17585 : Reach 17585 := rs (se 2 (by rfl) ⟨6594, by rfl⟩) R13189
theorem R17587 : Reach 17587 := rs (se 1 (by rfl) ⟨13190, by rfl⟩) R26381
theorem R17601 : Reach 17601 := rs (se 2 (by rfl) ⟨6600, by rfl⟩) R13201
theorem R17603 : Reach 17603 := rs (se 1 (by rfl) ⟨13202, by rfl⟩) R26405
theorem R50381 : Reach 50381 := rs (se 3 (by rfl) ⟨9446, by rfl⟩) R18893
theorem R17617 : Reach 17617 := rs (se 2 (by rfl) ⟨6606, by rfl⟩) R13213
theorem R17619 : Reach 17619 := rs (se 1 (by rfl) ⟨13214, by rfl⟩) R26429
theorem R17633 : Reach 17633 := rs (se 2 (by rfl) ⟨6612, by rfl⟩) R13225
theorem R17635 : Reach 17635 := rs (se 1 (by rfl) ⟨13226, by rfl⟩) R26453
theorem R17649 : Reach 17649 := rs (se 2 (by rfl) ⟨6618, by rfl⟩) R13237
theorem R17651 : Reach 17651 := rs (se 1 (by rfl) ⟨13238, by rfl⟩) R26477
theorem R17665 : Reach 17665 := rs (se 2 (by rfl) ⟨6624, by rfl⟩) R13249
theorem R17667 : Reach 17667 := rs (se 1 (by rfl) ⟨13250, by rfl⟩) R26501
theorem R83213 : Reach 83213 := rs (se 3 (by rfl) ⟨15602, by rfl⟩) R31205
theorem R17681 : Reach 17681 := rs (se 2 (by rfl) ⟨6630, by rfl⟩) R13261
theorem R17683 : Reach 17683 := rs (se 1 (by rfl) ⟨13262, by rfl⟩) R26525
theorem R17697 : Reach 17697 := rs (se 2 (by rfl) ⟨6636, by rfl⟩) R13273
theorem R17699 : Reach 17699 := rs (se 1 (by rfl) ⟨13274, by rfl⟩) R26549
theorem R17713 : Reach 17713 := rs (se 2 (by rfl) ⟨6642, by rfl⟩) R13285
theorem R17715 : Reach 17715 := rs (se 1 (by rfl) ⟨13286, by rfl⟩) R26573
theorem R214325 : Reach 214325 := rs (se 5 (by rfl) ⟨10046, by rfl⟩) R20093
theorem R17729 : Reach 17729 := rs (se 2 (by rfl) ⟨6648, by rfl⟩) R13297
theorem R17731 : Reach 17731 := rs (se 1 (by rfl) ⟨13298, by rfl⟩) R26597
theorem R17745 : Reach 17745 := rs (se 2 (by rfl) ⟨6654, by rfl⟩) R13309
theorem R17747 : Reach 17747 := rs (se 1 (by rfl) ⟨13310, by rfl⟩) R26621
theorem R17761 : Reach 17761 := rs (se 2 (by rfl) ⟨6660, by rfl⟩) R13321
theorem R17763 : Reach 17763 := rs (se 1 (by rfl) ⟨13322, by rfl⟩) R26645
theorem R17777 : Reach 17777 := rs (se 2 (by rfl) ⟨6666, by rfl⟩) R13333
theorem R17779 : Reach 17779 := rs (se 1 (by rfl) ⟨13334, by rfl⟩) R26669
theorem R17793 : Reach 17793 := rs (se 2 (by rfl) ⟨6672, by rfl⟩) R13345
theorem R17795 : Reach 17795 := rs (se 1 (by rfl) ⟨13346, by rfl⟩) R26693
theorem R181645 : Reach 181645 := rs (se 3 (by rfl) ⟨34058, by rfl⟩) R68117
theorem R17809 : Reach 17809 := rs (se 2 (by rfl) ⟨6678, by rfl⟩) R13357
theorem R17811 : Reach 17811 := rs (se 1 (by rfl) ⟨13358, by rfl⟩) R26717
theorem R17825 : Reach 17825 := rs (se 2 (by rfl) ⟨6684, by rfl⟩) R13369
theorem R17827 : Reach 17827 := rs (se 1 (by rfl) ⟨13370, by rfl⟩) R26741
theorem R17841 : Reach 17841 := rs (se 2 (by rfl) ⟨6690, by rfl⟩) R13381
theorem R17843 : Reach 17843 := rs (se 1 (by rfl) ⟨13382, by rfl⟩) R26765
theorem R17857 : Reach 17857 := rs (se 2 (by rfl) ⟨6696, by rfl⟩) R13393
theorem R17859 : Reach 17859 := rs (se 1 (by rfl) ⟨13394, by rfl⟩) R26789
theorem R17873 : Reach 17873 := rs (se 2 (by rfl) ⟨6702, by rfl⟩) R13405
theorem R17875 : Reach 17875 := rs (se 1 (by rfl) ⟨13406, by rfl⟩) R26813
theorem R17889 : Reach 17889 := rs (se 2 (by rfl) ⟨6708, by rfl⟩) R13417
theorem R17891 : Reach 17891 := rs (se 1 (by rfl) ⟨13418, by rfl⟩) R26837
theorem R17905 : Reach 17905 := rs (se 2 (by rfl) ⟨6714, by rfl⟩) R13429
theorem R17907 : Reach 17907 := rs (se 1 (by rfl) ⟨13430, by rfl⟩) R26861
theorem R17921 : Reach 17921 := rs (se 2 (by rfl) ⟨6720, by rfl⟩) R13441
theorem R17923 : Reach 17923 := rs (se 1 (by rfl) ⟨13442, by rfl⟩) R26885
theorem R17937 : Reach 17937 := rs (se 2 (by rfl) ⟨6726, by rfl⟩) R13453
theorem R17939 : Reach 17939 := rs (se 1 (by rfl) ⟨13454, by rfl⟩) R26909
theorem R17953 : Reach 17953 := rs (se 2 (by rfl) ⟨6732, by rfl⟩) R13465
theorem R17955 : Reach 17955 := rs (se 1 (by rfl) ⟨13466, by rfl⟩) R26933
theorem R17969 : Reach 17969 := rs (se 2 (by rfl) ⟨6738, by rfl⟩) R13477
theorem R17971 : Reach 17971 := rs (se 1 (by rfl) ⟨13478, by rfl⟩) R26957
theorem R17985 : Reach 17985 := rs (se 2 (by rfl) ⟨6744, by rfl⟩) R13489
theorem R17987 : Reach 17987 := rs (se 1 (by rfl) ⟨13490, by rfl⟩) R26981
theorem R18001 : Reach 18001 := rs (se 2 (by rfl) ⟨6750, by rfl⟩) R13501
theorem R18003 : Reach 18003 := rs (se 1 (by rfl) ⟨13502, by rfl⟩) R27005
theorem R18017 : Reach 18017 := rs (se 2 (by rfl) ⟨6756, by rfl⟩) R13513
theorem R18019 : Reach 18019 := rs (se 1 (by rfl) ⟨13514, by rfl⟩) R27029
theorem R18033 : Reach 18033 := rs (se 2 (by rfl) ⟨6762, by rfl⟩) R13525
theorem R18035 : Reach 18035 := rs (se 1 (by rfl) ⟨13526, by rfl⟩) R27053
theorem R18049 : Reach 18049 := rs (se 2 (by rfl) ⟨6768, by rfl⟩) R13537
theorem R18051 : Reach 18051 := rs (se 1 (by rfl) ⟨13538, by rfl⟩) R27077
theorem R18065 : Reach 18065 := rs (se 2 (by rfl) ⟨6774, by rfl⟩) R13549
theorem R18067 : Reach 18067 := rs (se 1 (by rfl) ⟨13550, by rfl⟩) R27101
theorem R18081 : Reach 18081 := rs (se 2 (by rfl) ⟨6780, by rfl⟩) R13561
theorem R18083 : Reach 18083 := rs (se 1 (by rfl) ⟨13562, by rfl⟩) R27125
theorem R18097 : Reach 18097 := rs (se 2 (by rfl) ⟨6786, by rfl⟩) R13573
theorem R18099 : Reach 18099 := rs (se 1 (by rfl) ⟨13574, by rfl⟩) R27149
theorem R18113 : Reach 18113 := rs (se 2 (by rfl) ⟨6792, by rfl⟩) R13585
theorem R18115 : Reach 18115 := rs (se 1 (by rfl) ⟨13586, by rfl⟩) R27173
theorem R18129 : Reach 18129 := rs (se 2 (by rfl) ⟨6798, by rfl⟩) R13597
theorem R18131 : Reach 18131 := rs (se 1 (by rfl) ⟨13598, by rfl⟩) R27197
theorem R18145 : Reach 18145 := rs (se 2 (by rfl) ⟨6804, by rfl⟩) R13609
theorem R18147 : Reach 18147 := rs (se 1 (by rfl) ⟨13610, by rfl⟩) R27221
theorem R18161 : Reach 18161 := rs (se 2 (by rfl) ⟨6810, by rfl⟩) R13621
theorem R18163 : Reach 18163 := rs (se 1 (by rfl) ⟨13622, by rfl⟩) R27245
theorem R18177 : Reach 18177 := rs (se 2 (by rfl) ⟨6816, by rfl⟩) R13633
theorem R18179 : Reach 18179 := rs (se 1 (by rfl) ⟨13634, by rfl⟩) R27269
theorem R18193 : Reach 18193 := rs (se 2 (by rfl) ⟨6822, by rfl⟩) R13645
theorem R18195 : Reach 18195 := rs (se 1 (by rfl) ⟨13646, by rfl⟩) R27293
theorem R18209 : Reach 18209 := rs (se 2 (by rfl) ⟨6828, by rfl⟩) R13657
theorem R18211 : Reach 18211 := rs (se 1 (by rfl) ⟨13658, by rfl⟩) R27317
theorem R18225 : Reach 18225 := rs (se 2 (by rfl) ⟨6834, by rfl⟩) R13669
theorem R18227 : Reach 18227 := rs (se 1 (by rfl) ⟨13670, by rfl⟩) R27341
theorem R18241 : Reach 18241 := rs (se 2 (by rfl) ⟨6840, by rfl⟩) R13681
theorem R18243 : Reach 18243 := rs (se 1 (by rfl) ⟨13682, by rfl⟩) R27365
theorem R18257 : Reach 18257 := rs (se 2 (by rfl) ⟨6846, by rfl⟩) R13693
theorem R18259 : Reach 18259 := rs (se 1 (by rfl) ⟨13694, by rfl⟩) R27389
theorem R18273 : Reach 18273 := rs (se 2 (by rfl) ⟨6852, by rfl⟩) R13705
theorem R18275 : Reach 18275 := rs (se 1 (by rfl) ⟨13706, by rfl⟩) R27413
theorem R18289 : Reach 18289 := rs (se 2 (by rfl) ⟨6858, by rfl⟩) R13717
theorem R83825 : Reach 83825 := rs (se 2 (by rfl) ⟨31434, by rfl⟩) R62869
theorem R18291 : Reach 18291 := rs (se 1 (by rfl) ⟨13718, by rfl⟩) R27437
theorem R18305 : Reach 18305 := rs (se 2 (by rfl) ⟨6864, by rfl⟩) R13729
theorem R18307 : Reach 18307 := rs (se 1 (by rfl) ⟨13730, by rfl⟩) R27461
theorem R18321 : Reach 18321 := rs (se 2 (by rfl) ⟨6870, by rfl⟩) R13741
theorem R18323 : Reach 18323 := rs (se 1 (by rfl) ⟨13742, by rfl⟩) R27485
theorem R18337 : Reach 18337 := rs (se 2 (by rfl) ⟨6876, by rfl⟩) R13753
theorem R18339 : Reach 18339 := rs (se 1 (by rfl) ⟨13754, by rfl⟩) R27509
theorem R51121 : Reach 51121 := rs (se 2 (by rfl) ⟨19170, by rfl⟩) R38341
theorem R18353 : Reach 18353 := rs (se 2 (by rfl) ⟨6882, by rfl⟩) R13765
theorem R18355 : Reach 18355 := rs (se 1 (by rfl) ⟨13766, by rfl⟩) R27533
theorem R18369 : Reach 18369 := rs (se 2 (by rfl) ⟨6888, by rfl⟩) R13777
theorem R18371 : Reach 18371 := rs (se 1 (by rfl) ⟨13778, by rfl⟩) R27557
theorem R18385 : Reach 18385 := rs (se 2 (by rfl) ⟨6894, by rfl⟩) R13789
theorem R18387 : Reach 18387 := rs (se 1 (by rfl) ⟨13790, by rfl⟩) R27581
theorem R18401 : Reach 18401 := rs (se 2 (by rfl) ⟨6900, by rfl⟩) R13801
theorem R18403 : Reach 18403 := rs (se 1 (by rfl) ⟨13802, by rfl⟩) R27605
theorem R18417 : Reach 18417 := rs (se 2 (by rfl) ⟨6906, by rfl⟩) R13813
theorem R18419 : Reach 18419 := rs (se 1 (by rfl) ⟨13814, by rfl⟩) R27629
theorem R18433 : Reach 18433 := rs (se 2 (by rfl) ⟨6912, by rfl⟩) R13825
theorem R18435 : Reach 18435 := rs (se 1 (by rfl) ⟨13826, by rfl⟩) R27653
theorem R18449 : Reach 18449 := rs (se 2 (by rfl) ⟨6918, by rfl⟩) R13837
theorem R18451 : Reach 18451 := rs (se 1 (by rfl) ⟨13838, by rfl⟩) R27677
theorem R18465 : Reach 18465 := rs (se 2 (by rfl) ⟨6924, by rfl⟩) R13849
theorem R18467 : Reach 18467 := rs (se 1 (by rfl) ⟨13850, by rfl⟩) R27701
theorem R84017 : Reach 84017 := rs (se 2 (by rfl) ⟨31506, by rfl⟩) R63013
theorem R18481 : Reach 18481 := rs (se 2 (by rfl) ⟨6930, by rfl⟩) R13861
theorem R18483 : Reach 18483 := rs (se 1 (by rfl) ⟨13862, by rfl⟩) R27725
theorem R18497 : Reach 18497 := rs (se 2 (by rfl) ⟨6936, by rfl⟩) R13873
theorem R18499 : Reach 18499 := rs (se 1 (by rfl) ⟨13874, by rfl⟩) R27749
theorem R18513 : Reach 18513 := rs (se 2 (by rfl) ⟨6942, by rfl⟩) R13885
theorem R18515 : Reach 18515 := rs (se 1 (by rfl) ⟨13886, by rfl⟩) R27773
theorem R18529 : Reach 18529 := rs (se 2 (by rfl) ⟨6948, by rfl⟩) R13897
theorem R51299 : Reach 51299 := rs (se 1 (by rfl) ⟨38474, by rfl⟩) R76949
theorem R18531 : Reach 18531 := rs (se 1 (by rfl) ⟨13898, by rfl⟩) R27797
theorem R18545 : Reach 18545 := rs (se 2 (by rfl) ⟨6954, by rfl⟩) R13909
theorem R18547 : Reach 18547 := rs (se 1 (by rfl) ⟨13910, by rfl⟩) R27821
theorem R18561 : Reach 18561 := rs (se 2 (by rfl) ⟨6960, by rfl⟩) R13921
theorem R18563 : Reach 18563 := rs (se 1 (by rfl) ⟨13922, by rfl⟩) R27845
theorem R18577 : Reach 18577 := rs (se 2 (by rfl) ⟨6966, by rfl⟩) R13933
theorem R18579 : Reach 18579 := rs (se 1 (by rfl) ⟨13934, by rfl⟩) R27869
theorem R18593 : Reach 18593 := rs (se 2 (by rfl) ⟨6972, by rfl⟩) R13945
theorem R18595 : Reach 18595 := rs (se 1 (by rfl) ⟨13946, by rfl⟩) R27893
theorem R18609 : Reach 18609 := rs (se 2 (by rfl) ⟨6978, by rfl⟩) R13957
theorem R18611 : Reach 18611 := rs (se 1 (by rfl) ⟨13958, by rfl⟩) R27917
theorem R18625 : Reach 18625 := rs (se 2 (by rfl) ⟨6984, by rfl⟩) R13969
theorem R18627 : Reach 18627 := rs (se 1 (by rfl) ⟨13970, by rfl⟩) R27941
theorem R18641 : Reach 18641 := rs (se 2 (by rfl) ⟨6990, by rfl⟩) R13981
theorem R18643 : Reach 18643 := rs (se 1 (by rfl) ⟨13982, by rfl⟩) R27965
theorem R18657 : Reach 18657 := rs (se 2 (by rfl) ⟨6996, by rfl⟩) R13993
theorem R18659 : Reach 18659 := rs (se 1 (by rfl) ⟨13994, by rfl⟩) R27989
theorem R18673 : Reach 18673 := rs (se 2 (by rfl) ⟨7002, by rfl⟩) R14005
theorem R18675 : Reach 18675 := rs (se 1 (by rfl) ⟨14006, by rfl⟩) R28013
theorem R18689 : Reach 18689 := rs (se 2 (by rfl) ⟨7008, by rfl⟩) R14017
theorem R18691 : Reach 18691 := rs (se 1 (by rfl) ⟨14018, by rfl⟩) R28037
theorem R18705 : Reach 18705 := rs (se 2 (by rfl) ⟨7014, by rfl⟩) R14029
theorem R18707 : Reach 18707 := rs (se 1 (by rfl) ⟨14030, by rfl⟩) R28061
theorem R18721 : Reach 18721 := rs (se 2 (by rfl) ⟨7020, by rfl⟩) R14041
theorem R18723 : Reach 18723 := rs (se 1 (by rfl) ⟨14042, by rfl⟩) R28085
theorem R18737 : Reach 18737 := rs (se 2 (by rfl) ⟨7026, by rfl⟩) R14053
theorem R18739 : Reach 18739 := rs (se 1 (by rfl) ⟨14054, by rfl⟩) R28109
theorem R18753 : Reach 18753 := rs (se 2 (by rfl) ⟨7032, by rfl⟩) R14065
theorem R18755 : Reach 18755 := rs (se 1 (by rfl) ⟨14066, by rfl⟩) R28133
theorem R18769 : Reach 18769 := rs (se 2 (by rfl) ⟨7038, by rfl⟩) R14077
theorem R18771 : Reach 18771 := rs (se 1 (by rfl) ⟨14078, by rfl⟩) R28157
theorem R18785 : Reach 18785 := rs (se 2 (by rfl) ⟨7044, by rfl⟩) R14089
theorem R18787 : Reach 18787 := rs (se 1 (by rfl) ⟨14090, by rfl⟩) R28181
theorem R51569 : Reach 51569 := rs (se 2 (by rfl) ⟨19338, by rfl⟩) R38677
theorem R18801 : Reach 18801 := rs (se 2 (by rfl) ⟨7050, by rfl⟩) R14101
theorem R18803 : Reach 18803 := rs (se 1 (by rfl) ⟨14102, by rfl⟩) R28205
theorem R18817 : Reach 18817 := rs (se 2 (by rfl) ⟨7056, by rfl⟩) R14113
theorem R18819 : Reach 18819 := rs (se 1 (by rfl) ⟨14114, by rfl⟩) R28229
theorem R18833 : Reach 18833 := rs (se 2 (by rfl) ⟨7062, by rfl⟩) R14125
theorem R18835 : Reach 18835 := rs (se 1 (by rfl) ⟨14126, by rfl⟩) R28253
theorem R18849 : Reach 18849 := rs (se 2 (by rfl) ⟨7068, by rfl⟩) R14137
theorem R51619 : Reach 51619 := rs (se 1 (by rfl) ⟨38714, by rfl⟩) R77429
theorem R18851 : Reach 18851 := rs (se 1 (by rfl) ⟨14138, by rfl⟩) R28277
theorem R84401 : Reach 84401 := rs (se 2 (by rfl) ⟨31650, by rfl⟩) R63301
theorem R18865 : Reach 18865 := rs (se 2 (by rfl) ⟨7074, by rfl⟩) R14149
theorem R18867 : Reach 18867 := rs (se 1 (by rfl) ⟨14150, by rfl⟩) R28301
theorem R18881 : Reach 18881 := rs (se 2 (by rfl) ⟨7080, by rfl⟩) R14161
theorem R18883 : Reach 18883 := rs (se 1 (by rfl) ⟨14162, by rfl⟩) R28325
theorem R18897 : Reach 18897 := rs (se 2 (by rfl) ⟨7086, by rfl⟩) R14173
theorem R18899 : Reach 18899 := rs (se 1 (by rfl) ⟨14174, by rfl⟩) R28349
theorem R18913 : Reach 18913 := rs (se 2 (by rfl) ⟨7092, by rfl⟩) R14185
theorem R18915 : Reach 18915 := rs (se 1 (by rfl) ⟨14186, by rfl⟩) R28373
theorem R18929 : Reach 18929 := rs (se 2 (by rfl) ⟨7098, by rfl⟩) R14197
theorem R18931 : Reach 18931 := rs (se 1 (by rfl) ⟨14198, by rfl⟩) R28397
theorem R18945 : Reach 18945 := rs (se 2 (by rfl) ⟨7104, by rfl⟩) R14209
theorem R18947 : Reach 18947 := rs (se 1 (by rfl) ⟨14210, by rfl⟩) R28421
theorem R18961 : Reach 18961 := rs (se 2 (by rfl) ⟨7110, by rfl⟩) R14221
theorem R18963 : Reach 18963 := rs (se 1 (by rfl) ⟨14222, by rfl⟩) R28445
theorem R18977 : Reach 18977 := rs (se 2 (by rfl) ⟨7116, by rfl⟩) R14233
theorem R18979 : Reach 18979 := rs (se 1 (by rfl) ⟨14234, by rfl⟩) R28469
theorem R18993 : Reach 18993 := rs (se 2 (by rfl) ⟨7122, by rfl⟩) R14245
theorem R18995 : Reach 18995 := rs (se 1 (by rfl) ⟨14246, by rfl⟩) R28493
theorem R19009 : Reach 19009 := rs (se 2 (by rfl) ⟨7128, by rfl⟩) R14257
theorem R19011 : Reach 19011 := rs (se 1 (by rfl) ⟨14258, by rfl⟩) R28517
theorem R19025 : Reach 19025 := rs (se 2 (by rfl) ⟨7134, by rfl⟩) R14269
theorem R19027 : Reach 19027 := rs (se 1 (by rfl) ⟨14270, by rfl⟩) R28541
theorem R19041 : Reach 19041 := rs (se 2 (by rfl) ⟨7140, by rfl⟩) R14281
theorem R19043 : Reach 19043 := rs (se 1 (by rfl) ⟨14282, by rfl⟩) R28565
theorem R19057 : Reach 19057 := rs (se 2 (by rfl) ⟨7146, by rfl⟩) R14293
theorem R19059 : Reach 19059 := rs (se 1 (by rfl) ⟨14294, by rfl⟩) R28589
theorem R19073 : Reach 19073 := rs (se 2 (by rfl) ⟨7152, by rfl⟩) R14305
theorem R19075 : Reach 19075 := rs (se 1 (by rfl) ⟨14306, by rfl⟩) R28613
theorem R215693 : Reach 215693 := rs (se 3 (by rfl) ⟨40442, by rfl⟩) R80885
theorem R19089 : Reach 19089 := rs (se 2 (by rfl) ⟨7158, by rfl⟩) R14317
theorem R19091 : Reach 19091 := rs (se 1 (by rfl) ⟨14318, by rfl⟩) R28637
theorem R19105 : Reach 19105 := rs (se 2 (by rfl) ⟨7164, by rfl⟩) R14329
theorem R19107 : Reach 19107 := rs (se 1 (by rfl) ⟨14330, by rfl⟩) R28661
theorem R19121 : Reach 19121 := rs (se 2 (by rfl) ⟨7170, by rfl⟩) R14341
theorem R19123 : Reach 19123 := rs (se 1 (by rfl) ⟨14342, by rfl⟩) R28685
theorem R19137 : Reach 19137 := rs (se 2 (by rfl) ⟨7176, by rfl⟩) R14353
theorem R19139 : Reach 19139 := rs (se 1 (by rfl) ⟨14354, by rfl⟩) R28709
theorem R84685 : Reach 84685 := rs (se 3 (by rfl) ⟨15878, by rfl⟩) R31757
theorem R19153 : Reach 19153 := rs (se 2 (by rfl) ⟨7182, by rfl⟩) R14365
theorem R19155 : Reach 19155 := rs (se 1 (by rfl) ⟨14366, by rfl⟩) R28733
theorem R19169 : Reach 19169 := rs (se 2 (by rfl) ⟨7188, by rfl⟩) R14377
theorem R19171 : Reach 19171 := rs (se 1 (by rfl) ⟨14378, by rfl⟩) R28757
theorem R19185 : Reach 19185 := rs (se 2 (by rfl) ⟨7194, by rfl⟩) R14389
theorem R19187 : Reach 19187 := rs (se 1 (by rfl) ⟨14390, by rfl⟩) R28781
theorem R19201 : Reach 19201 := rs (se 2 (by rfl) ⟨7200, by rfl⟩) R14401
theorem R19203 : Reach 19203 := rs (se 1 (by rfl) ⟨14402, by rfl⟩) R28805
theorem R19217 : Reach 19217 := rs (se 2 (by rfl) ⟨7206, by rfl⟩) R14413
theorem R19219 : Reach 19219 := rs (se 1 (by rfl) ⟨14414, by rfl⟩) R28829
theorem R19235 : Reach 19235 := rs (se 1 (by rfl) ⟨14426, by rfl⟩) R28853
theorem R19233 : Reach 19233 := rs (se 2 (by rfl) ⟨7212, by rfl⟩) R14425
theorem R19249 : Reach 19249 := rs (se 2 (by rfl) ⟨7218, by rfl⟩) R14437
theorem R19251 : Reach 19251 := rs (se 1 (by rfl) ⟨14438, by rfl⟩) R28877
theorem R19265 : Reach 19265 := rs (se 2 (by rfl) ⟨7224, by rfl⟩) R14449
theorem R19267 : Reach 19267 := rs (se 1 (by rfl) ⟨14450, by rfl⟩) R28901
theorem R19281 : Reach 19281 := rs (se 2 (by rfl) ⟨7230, by rfl⟩) R14461
theorem R19283 : Reach 19283 := rs (se 1 (by rfl) ⟨14462, by rfl⟩) R28925
theorem R19297 : Reach 19297 := rs (se 2 (by rfl) ⟨7236, by rfl⟩) R14473
theorem R19299 : Reach 19299 := rs (se 1 (by rfl) ⟨14474, by rfl⟩) R28949
theorem R19313 : Reach 19313 := rs (se 2 (by rfl) ⟨7242, by rfl⟩) R14485
theorem R19315 : Reach 19315 := rs (se 1 (by rfl) ⟨14486, by rfl⟩) R28973
theorem R19329 : Reach 19329 := rs (se 2 (by rfl) ⟨7248, by rfl⟩) R14497
theorem R19331 : Reach 19331 := rs (se 1 (by rfl) ⟨14498, by rfl⟩) R28997
theorem R52109 : Reach 52109 := rs (se 3 (by rfl) ⟨9770, by rfl⟩) R19541
theorem R19345 : Reach 19345 := rs (se 2 (by rfl) ⟨7254, by rfl⟩) R14509
theorem R19347 : Reach 19347 := rs (se 1 (by rfl) ⟨14510, by rfl⟩) R29021
theorem R19361 : Reach 19361 := rs (se 2 (by rfl) ⟨7260, by rfl⟩) R14521
theorem R19363 : Reach 19363 := rs (se 1 (by rfl) ⟨14522, by rfl⟩) R29045
theorem R19377 : Reach 19377 := rs (se 2 (by rfl) ⟨7266, by rfl⟩) R14533
theorem R19379 : Reach 19379 := rs (se 1 (by rfl) ⟨14534, by rfl⟩) R29069
theorem R19393 : Reach 19393 := rs (se 2 (by rfl) ⟨7272, by rfl⟩) R14545
theorem R19395 : Reach 19395 := rs (se 1 (by rfl) ⟨14546, by rfl⟩) R29093
theorem R19409 : Reach 19409 := rs (se 2 (by rfl) ⟨7278, by rfl⟩) R14557
theorem R19411 : Reach 19411 := rs (se 1 (by rfl) ⟨14558, by rfl⟩) R29117
theorem R19425 : Reach 19425 := rs (se 2 (by rfl) ⟨7284, by rfl⟩) R14569
theorem R19427 : Reach 19427 := rs (se 1 (by rfl) ⟨14570, by rfl⟩) R29141
theorem R19441 : Reach 19441 := rs (se 2 (by rfl) ⟨7290, by rfl⟩) R14581
theorem R19443 : Reach 19443 := rs (se 1 (by rfl) ⟨14582, by rfl⟩) R29165
theorem R19457 : Reach 19457 := rs (se 2 (by rfl) ⟨7296, by rfl⟩) R14593
theorem R19459 : Reach 19459 := rs (se 1 (by rfl) ⟨14594, by rfl⟩) R29189
theorem R117773 : Reach 117773 := rs (se 3 (by rfl) ⟨22082, by rfl⟩) R44165
theorem R19473 : Reach 19473 := rs (se 2 (by rfl) ⟨7302, by rfl⟩) R14605
theorem R19475 : Reach 19475 := rs (se 1 (by rfl) ⟨14606, by rfl⟩) R29213
theorem R19489 : Reach 19489 := rs (se 2 (by rfl) ⟨7308, by rfl⟩) R14617
theorem R19491 : Reach 19491 := rs (se 1 (by rfl) ⟨14618, by rfl⟩) R29237
theorem R19505 : Reach 19505 := rs (se 2 (by rfl) ⟨7314, by rfl⟩) R14629
theorem R19507 : Reach 19507 := rs (se 1 (by rfl) ⟨14630, by rfl⟩) R29261
theorem R19521 : Reach 19521 := rs (se 2 (by rfl) ⟨7320, by rfl⟩) R14641
theorem R19523 : Reach 19523 := rs (se 1 (by rfl) ⟨14642, by rfl⟩) R29285
theorem R19537 : Reach 19537 := rs (se 2 (by rfl) ⟨7326, by rfl⟩) R14653
theorem R19539 : Reach 19539 := rs (se 1 (by rfl) ⟨14654, by rfl⟩) R29309
theorem R19553 : Reach 19553 := rs (se 2 (by rfl) ⟨7332, by rfl⟩) R14665
theorem R19555 : Reach 19555 := rs (se 1 (by rfl) ⟨14666, by rfl⟩) R29333
theorem R19569 : Reach 19569 := rs (se 2 (by rfl) ⟨7338, by rfl⟩) R14677
theorem R19571 : Reach 19571 := rs (se 1 (by rfl) ⟨14678, by rfl⟩) R29357
theorem R19585 : Reach 19585 := rs (se 2 (by rfl) ⟨7344, by rfl⟩) R14689
theorem R19587 : Reach 19587 := rs (se 1 (by rfl) ⟨14690, by rfl⟩) R29381
theorem R19601 : Reach 19601 := rs (se 2 (by rfl) ⟨7350, by rfl⟩) R14701
theorem R19603 : Reach 19603 := rs (se 1 (by rfl) ⟨14702, by rfl⟩) R29405
theorem R19617 : Reach 19617 := rs (se 2 (by rfl) ⟨7356, by rfl⟩) R14713
theorem R19619 : Reach 19619 := rs (se 1 (by rfl) ⟨14714, by rfl⟩) R29429
theorem R19633 : Reach 19633 := rs (se 2 (by rfl) ⟨7362, by rfl⟩) R14725
theorem R19635 : Reach 19635 := rs (se 1 (by rfl) ⟨14726, by rfl⟩) R29453
theorem R19649 : Reach 19649 := rs (se 2 (by rfl) ⟨7368, by rfl⟩) R14737
theorem R19651 : Reach 19651 := rs (se 1 (by rfl) ⟨14738, by rfl⟩) R29477
theorem R19665 : Reach 19665 := rs (se 2 (by rfl) ⟨7374, by rfl⟩) R14749
theorem R19667 : Reach 19667 := rs (se 1 (by rfl) ⟨14750, by rfl⟩) R29501
theorem R19681 : Reach 19681 := rs (se 2 (by rfl) ⟨7380, by rfl⟩) R14761
theorem R19683 : Reach 19683 := rs (se 1 (by rfl) ⟨14762, by rfl⟩) R29525
theorem R19697 : Reach 19697 := rs (se 2 (by rfl) ⟨7386, by rfl⟩) R14773
theorem R19699 : Reach 19699 := rs (se 1 (by rfl) ⟨14774, by rfl⟩) R29549
theorem R19713 : Reach 19713 := rs (se 2 (by rfl) ⟨7392, by rfl⟩) R14785
theorem R19715 : Reach 19715 := rs (se 1 (by rfl) ⟨14786, by rfl⟩) R29573
theorem R19729 : Reach 19729 := rs (se 2 (by rfl) ⟨7398, by rfl⟩) R14797
theorem R19731 : Reach 19731 := rs (se 1 (by rfl) ⟨14798, by rfl⟩) R29597
theorem R19745 : Reach 19745 := rs (se 2 (by rfl) ⟨7404, by rfl⟩) R14809
theorem R19747 : Reach 19747 := rs (se 1 (by rfl) ⟨14810, by rfl⟩) R29621
theorem R19761 : Reach 19761 := rs (se 2 (by rfl) ⟨7410, by rfl⟩) R14821
theorem R19763 : Reach 19763 := rs (se 1 (by rfl) ⟨14822, by rfl⟩) R29645
theorem R19777 : Reach 19777 := rs (se 2 (by rfl) ⟨7416, by rfl⟩) R14833
theorem R19779 : Reach 19779 := rs (se 1 (by rfl) ⟨14834, by rfl⟩) R29669
theorem R19793 : Reach 19793 := rs (se 2 (by rfl) ⟨7422, by rfl⟩) R14845
theorem R19795 : Reach 19795 := rs (se 1 (by rfl) ⟨14846, by rfl⟩) R29693
theorem R19809 : Reach 19809 := rs (se 2 (by rfl) ⟨7428, by rfl⟩) R14857
theorem R19811 : Reach 19811 := rs (se 1 (by rfl) ⟨14858, by rfl⟩) R29717
theorem R52579 : Reach 52579 := rs (se 1 (by rfl) ⟨39434, by rfl⟩) R78869
theorem R19825 : Reach 19825 := rs (se 2 (by rfl) ⟨7434, by rfl⟩) R14869
theorem R19827 : Reach 19827 := rs (se 1 (by rfl) ⟨14870, by rfl⟩) R29741
theorem R19841 : Reach 19841 := rs (se 2 (by rfl) ⟨7440, by rfl⟩) R14881
theorem R19843 : Reach 19843 := rs (se 1 (by rfl) ⟨14882, by rfl⟩) R29765
theorem R19857 : Reach 19857 := rs (se 2 (by rfl) ⟨7446, by rfl⟩) R14893
theorem R19859 : Reach 19859 := rs (se 1 (by rfl) ⟨14894, by rfl⟩) R29789
theorem R19873 : Reach 19873 := rs (se 2 (by rfl) ⟨7452, by rfl⟩) R14905
theorem R52643 : Reach 52643 := rs (se 1 (by rfl) ⟨39482, by rfl⟩) R78965
theorem R19875 : Reach 19875 := rs (se 1 (by rfl) ⟨14906, by rfl⟩) R29813
theorem R19889 : Reach 19889 := rs (se 2 (by rfl) ⟨7458, by rfl⟩) R14917
theorem R19891 : Reach 19891 := rs (se 1 (by rfl) ⟨14918, by rfl⟩) R29837
theorem R19905 : Reach 19905 := rs (se 2 (by rfl) ⟨7464, by rfl⟩) R14929
theorem R19907 : Reach 19907 := rs (se 1 (by rfl) ⟨14930, by rfl⟩) R29861
theorem R19921 : Reach 19921 := rs (se 2 (by rfl) ⟨7470, by rfl⟩) R14941
theorem R19923 : Reach 19923 := rs (se 1 (by rfl) ⟨14942, by rfl⟩) R29885
theorem R19937 : Reach 19937 := rs (se 2 (by rfl) ⟨7476, by rfl⟩) R14953
theorem R85475 : Reach 85475 := rs (se 1 (by rfl) ⟨64106, by rfl⟩) R128213
theorem R19939 : Reach 19939 := rs (se 1 (by rfl) ⟨14954, by rfl⟩) R29909
theorem R52721 : Reach 52721 := rs (se 2 (by rfl) ⟨19770, by rfl⟩) R39541
theorem R151025 : Reach 151025 := rs (se 2 (by rfl) ⟨56634, by rfl⟩) R113269
theorem R19955 : Reach 19955 := rs (se 1 (by rfl) ⟨14966, by rfl⟩) R29933
theorem R19953 : Reach 19953 := rs (se 2 (by rfl) ⟨7482, by rfl⟩) R14965
theorem R19969 : Reach 19969 := rs (se 2 (by rfl) ⟨7488, by rfl⟩) R14977
theorem R19971 : Reach 19971 := rs (se 1 (by rfl) ⟨14978, by rfl⟩) R29957
theorem R19985 : Reach 19985 := rs (se 2 (by rfl) ⟨7494, by rfl⟩) R14989
theorem R19987 : Reach 19987 := rs (se 1 (by rfl) ⟨14990, by rfl⟩) R29981
theorem R20003 : Reach 20003 := rs (se 1 (by rfl) ⟨15002, by rfl⟩) R30005
theorem R20017 : Reach 20017 := rs (se 2 (by rfl) ⟨7506, by rfl⟩) R15013
theorem R20033 : Reach 20033 := rs (se 2 (by rfl) ⟨7512, by rfl⟩) R15025
theorem R20051 : Reach 20051 := rs (se 1 (by rfl) ⟨15038, by rfl⟩) R30077
theorem R20065 : Reach 20065 := rs (se 2 (by rfl) ⟨7524, by rfl⟩) R15049
theorem R20081 : Reach 20081 := rs (se 2 (by rfl) ⟨7530, by rfl⟩) R15061
theorem R20083 : Reach 20083 := rs (se 1 (by rfl) ⟨15062, by rfl⟩) R30125
theorem R20099 : Reach 20099 := rs (se 1 (by rfl) ⟨15074, by rfl⟩) R30149
theorem R20129 : Reach 20129 := rs (se 2 (by rfl) ⟨7548, by rfl⟩) R15097
theorem R20131 : Reach 20131 := rs (se 1 (by rfl) ⟨15098, by rfl⟩) R30197
theorem R52913 : Reach 52913 := rs (se 2 (by rfl) ⟨19842, by rfl⟩) R39685
theorem R20147 : Reach 20147 := rs (se 1 (by rfl) ⟨15110, by rfl⟩) R30221
theorem R20177 : Reach 20177 := rs (se 2 (by rfl) ⟨7566, by rfl⟩) R15133
theorem R20179 : Reach 20179 := rs (se 1 (by rfl) ⟨15134, by rfl⟩) R30269
theorem R20195 : Reach 20195 := rs (se 1 (by rfl) ⟨15146, by rfl⟩) R30293
theorem R20209 : Reach 20209 := rs (se 2 (by rfl) ⟨7578, by rfl⟩) R15157
theorem R20225 : Reach 20225 := rs (se 2 (by rfl) ⟨7584, by rfl⟩) R15169
theorem R20227 : Reach 20227 := rs (se 1 (by rfl) ⟨15170, by rfl⟩) R30341
theorem R20243 : Reach 20243 := rs (se 1 (by rfl) ⟨15182, by rfl⟩) R30365
theorem R53027 : Reach 53027 := rs (se 1 (by rfl) ⟨39770, by rfl⟩) R79541
theorem R20273 : Reach 20273 := rs (se 2 (by rfl) ⟨7602, by rfl⟩) R15205
theorem R20291 : Reach 20291 := rs (se 1 (by rfl) ⟨15218, by rfl⟩) R30437
theorem R20321 : Reach 20321 := rs (se 2 (by rfl) ⟨7620, by rfl⟩) R15241
theorem R85859 : Reach 85859 := rs (se 1 (by rfl) ⟨64394, by rfl⟩) R128789
theorem R20339 : Reach 20339 := rs (se 1 (by rfl) ⟨15254, by rfl⟩) R30509
theorem R20353 : Reach 20353 := rs (se 2 (by rfl) ⟨7632, by rfl⟩) R15265
theorem R20369 : Reach 20369 := rs (se 2 (by rfl) ⟨7638, by rfl⟩) R15277
theorem R20371 : Reach 20371 := rs (se 1 (by rfl) ⟨15278, by rfl⟩) R30557
theorem R20387 : Reach 20387 := rs (se 1 (by rfl) ⟨15290, by rfl⟩) R30581
theorem R20417 : Reach 20417 := rs (se 2 (by rfl) ⟨7656, by rfl⟩) R15313
theorem R20435 : Reach 20435 := rs (se 1 (by rfl) ⟨15326, by rfl⟩) R30653
theorem R20465 : Reach 20465 := rs (se 2 (by rfl) ⟨7674, by rfl⟩) R15349
theorem R20483 : Reach 20483 := rs (se 1 (by rfl) ⟨15362, by rfl⟩) R30725
theorem R86021 : Reach 86021 := rs (se 4 (by rfl) ⟨8064, by rfl⟩) R16129
theorem R20497 : Reach 20497 := rs (se 2 (by rfl) ⟨7686, by rfl⟩) R15373
theorem R20513 : Reach 20513 := rs (se 2 (by rfl) ⟨7692, by rfl⟩) R15385
theorem R20515 : Reach 20515 := rs (se 1 (by rfl) ⟨15386, by rfl⟩) R30773
theorem R53297 : Reach 53297 := rs (se 2 (by rfl) ⟨19986, by rfl⟩) R39973
theorem R20531 : Reach 20531 := rs (se 1 (by rfl) ⟨15398, by rfl⟩) R30797
theorem R20561 : Reach 20561 := rs (se 2 (by rfl) ⟨7710, by rfl⟩) R15421
theorem R20579 : Reach 20579 := rs (se 1 (by rfl) ⟨15434, by rfl⟩) R30869
theorem R20609 : Reach 20609 := rs (se 2 (by rfl) ⟨7728, by rfl⟩) R15457
theorem R20627 : Reach 20627 := rs (se 1 (by rfl) ⟨15470, by rfl⟩) R30941
theorem R20641 : Reach 20641 := rs (se 2 (by rfl) ⟨7740, by rfl⟩) R15481
theorem R20657 : Reach 20657 := rs (se 2 (by rfl) ⟨7746, by rfl⟩) R15493
theorem R20659 : Reach 20659 := rs (se 1 (by rfl) ⟨15494, by rfl⟩) R30989
theorem R151733 : Reach 151733 := rs (se 5 (by rfl) ⟨7112, by rfl⟩) R14225
theorem R20675 : Reach 20675 := rs (se 1 (by rfl) ⟨15506, by rfl⟩) R31013
theorem R20705 : Reach 20705 := rs (se 2 (by rfl) ⟨7764, by rfl⟩) R15529
theorem R151793 : Reach 151793 := rs (se 2 (by rfl) ⟨56922, by rfl⟩) R113845
theorem R20723 : Reach 20723 := rs (se 1 (by rfl) ⟨15542, by rfl⟩) R31085
theorem R20753 : Reach 20753 := rs (se 2 (by rfl) ⟨7782, by rfl⟩) R15565
theorem R20771 : Reach 20771 := rs (se 1 (by rfl) ⟨15578, by rfl⟩) R31157
theorem R20785 : Reach 20785 := rs (se 2 (by rfl) ⟨7794, by rfl⟩) R15589
theorem R20801 : Reach 20801 := rs (se 2 (by rfl) ⟨7800, by rfl⟩) R15601
theorem R20803 : Reach 20803 := rs (se 1 (by rfl) ⟨15602, by rfl⟩) R31205
theorem R86341 : Reach 86341 := rs (se 4 (by rfl) ⟨8094, by rfl⟩) R16189
theorem R53581 : Reach 53581 := rs (se 3 (by rfl) ⟨10046, by rfl⟩) R20093
theorem R20819 : Reach 20819 := rs (se 1 (by rfl) ⟨15614, by rfl⟩) R31229
theorem R20849 : Reach 20849 := rs (se 2 (by rfl) ⟨7818, by rfl⟩) R15637
theorem R20867 : Reach 20867 := rs (se 1 (by rfl) ⟨15650, by rfl⟩) R31301
theorem R20897 : Reach 20897 := rs (se 2 (by rfl) ⟨7836, by rfl⟩) R15673
theorem R20915 : Reach 20915 := rs (se 1 (by rfl) ⟨15686, by rfl⟩) R31373
theorem R20929 : Reach 20929 := rs (se 2 (by rfl) ⟨7848, by rfl⟩) R15697
theorem R20945 : Reach 20945 := rs (se 2 (by rfl) ⟨7854, by rfl⟩) R15709
theorem R20947 : Reach 20947 := rs (se 1 (by rfl) ⟨15710, by rfl⟩) R31421
theorem R20963 : Reach 20963 := rs (se 1 (by rfl) ⟨15722, by rfl⟩) R31445
theorem R20993 : Reach 20993 := rs (se 2 (by rfl) ⟨7872, by rfl⟩) R15745
theorem R21011 : Reach 21011 := rs (se 1 (by rfl) ⟨15758, by rfl⟩) R31517
theorem R21041 : Reach 21041 := rs (se 2 (by rfl) ⟨7890, by rfl⟩) R15781
theorem R21059 : Reach 21059 := rs (se 1 (by rfl) ⟨15794, by rfl⟩) R31589
theorem R53837 : Reach 53837 := rs (se 3 (by rfl) ⟨10094, by rfl⟩) R20189
theorem R21073 : Reach 21073 := rs (se 2 (by rfl) ⟨7902, by rfl⟩) R15805
theorem R21089 : Reach 21089 := rs (se 2 (by rfl) ⟨7908, by rfl⟩) R15817
theorem R21091 : Reach 21091 := rs (se 1 (by rfl) ⟨15818, by rfl⟩) R31637
theorem R21107 : Reach 21107 := rs (se 1 (by rfl) ⟨15830, by rfl⟩) R31661
theorem R86669 : Reach 86669 := rs (se 3 (by rfl) ⟨16250, by rfl⟩) R32501
theorem R21137 : Reach 21137 := rs (se 2 (by rfl) ⟨7926, by rfl⟩) R15853
theorem R21155 : Reach 21155 := rs (se 1 (by rfl) ⟨15866, by rfl⟩) R31733
theorem R21185 : Reach 21185 := rs (se 2 (by rfl) ⟨7944, by rfl⟩) R15889
theorem R21203 : Reach 21203 := rs (se 1 (by rfl) ⟨15902, by rfl⟩) R31805
theorem R21217 : Reach 21217 := rs (se 2 (by rfl) ⟨7956, by rfl⟩) R15913
theorem R21233 : Reach 21233 := rs (se 2 (by rfl) ⟨7962, by rfl⟩) R15925
theorem R21235 : Reach 21235 := rs (se 1 (by rfl) ⟨15926, by rfl⟩) R31853
theorem R21251 : Reach 21251 := rs (se 1 (by rfl) ⟨15938, by rfl⟩) R31877
theorem R21281 : Reach 21281 := rs (se 2 (by rfl) ⟨7980, by rfl⟩) R15961
theorem R21299 : Reach 21299 := rs (se 1 (by rfl) ⟨15974, by rfl⟩) R31949
theorem R21313 : Reach 21313 := rs (se 2 (by rfl) ⟨7992, by rfl⟩) R15985
theorem R21329 : Reach 21329 := rs (se 2 (by rfl) ⟨7998, by rfl⟩) R15997
theorem R21347 : Reach 21347 := rs (se 1 (by rfl) ⟨16010, by rfl⟩) R32021
theorem R21361 : Reach 21361 := rs (se 2 (by rfl) ⟨8010, by rfl⟩) R16021
theorem R21377 : Reach 21377 := rs (se 2 (by rfl) ⟨8016, by rfl⟩) R16033
theorem R21379 : Reach 21379 := rs (se 1 (by rfl) ⟨16034, by rfl⟩) R32069
theorem R21395 : Reach 21395 := rs (se 1 (by rfl) ⟨16046, by rfl⟩) R32093
theorem R21425 : Reach 21425 := rs (se 2 (by rfl) ⟨8034, by rfl⟩) R16069
theorem R21443 : Reach 21443 := rs (se 1 (by rfl) ⟨16082, by rfl⟩) R32165
theorem R21473 : Reach 21473 := rs (se 2 (by rfl) ⟨8052, by rfl⟩) R16105
theorem R21475 : Reach 21475 := rs (se 1 (by rfl) ⟨16106, by rfl⟩) R32213
theorem R21491 : Reach 21491 := rs (se 1 (by rfl) ⟨16118, by rfl⟩) R32237
theorem R21505 : Reach 21505 := rs (se 2 (by rfl) ⟨8064, by rfl⟩) R16129
theorem R21521 : Reach 21521 := rs (se 2 (by rfl) ⟨8070, by rfl⟩) R16141
theorem R21523 : Reach 21523 := rs (se 1 (by rfl) ⟨16142, by rfl⟩) R32285
theorem R21539 : Reach 21539 := rs (se 1 (by rfl) ⟨16154, by rfl⟩) R32309
theorem R21569 : Reach 21569 := rs (se 2 (by rfl) ⟨8088, by rfl⟩) R16177
theorem R21587 : Reach 21587 := rs (se 1 (by rfl) ⟨16190, by rfl⟩) R32381
theorem R54371 : Reach 54371 := rs (se 1 (by rfl) ⟨40778, by rfl⟩) R81557
theorem R21617 : Reach 21617 := rs (se 2 (by rfl) ⟨8106, by rfl⟩) R16213
theorem R21635 : Reach 21635 := rs (se 1 (by rfl) ⟨16226, by rfl⟩) R32453
theorem R21649 : Reach 21649 := rs (se 2 (by rfl) ⟨8118, by rfl⟩) R16237
theorem R21665 : Reach 21665 := rs (se 2 (by rfl) ⟨8124, by rfl⟩) R16249
theorem R21667 : Reach 21667 := rs (se 1 (by rfl) ⟨16250, by rfl⟩) R32501
theorem R21683 : Reach 21683 := rs (se 1 (by rfl) ⟨16262, by rfl⟩) R32525
theorem R21713 : Reach 21713 := rs (se 2 (by rfl) ⟨8142, by rfl⟩) R16285
theorem R21731 : Reach 21731 := rs (se 1 (by rfl) ⟨16298, by rfl⟩) R32597
theorem R21745 : Reach 21745 := rs (se 2 (by rfl) ⟨8154, by rfl⟩) R16309
theorem R21761 : Reach 21761 := rs (se 2 (by rfl) ⟨8160, by rfl⟩) R16321
theorem R21779 : Reach 21779 := rs (se 1 (by rfl) ⟨16334, by rfl⟩) R32669
theorem R21793 : Reach 21793 := rs (se 2 (by rfl) ⟨8172, by rfl⟩) R16345
theorem R21809 : Reach 21809 := rs (se 2 (by rfl) ⟨8178, by rfl⟩) R16357
theorem R21811 : Reach 21811 := rs (se 1 (by rfl) ⟨16358, by rfl⟩) R32717
theorem R21827 : Reach 21827 := rs (se 1 (by rfl) ⟨16370, by rfl⟩) R32741
theorem R21857 : Reach 21857 := rs (se 2 (by rfl) ⟨8196, by rfl⟩) R16393
theorem R54641 : Reach 54641 := rs (se 2 (by rfl) ⟨20490, by rfl⟩) R40981
theorem R21875 : Reach 21875 := rs (se 1 (by rfl) ⟨16406, by rfl⟩) R32813
theorem R21905 : Reach 21905 := rs (se 2 (by rfl) ⟨8214, by rfl⟩) R16429
theorem R21923 : Reach 21923 := rs (se 1 (by rfl) ⟨16442, by rfl⟩) R32885
theorem R21937 : Reach 21937 := rs (se 2 (by rfl) ⟨8226, by rfl⟩) R16453
theorem R87473 : Reach 87473 := rs (se 2 (by rfl) ⟨32802, by rfl⟩) R65605
theorem R21953 : Reach 21953 := rs (se 2 (by rfl) ⟨8232, by rfl⟩) R16465
theorem R21955 : Reach 21955 := rs (se 1 (by rfl) ⟨16466, by rfl⟩) R32933
theorem R21971 : Reach 21971 := rs (se 1 (by rfl) ⟨16478, by rfl⟩) R32957
theorem R54755 : Reach 54755 := rs (se 1 (by rfl) ⟨41066, by rfl⟩) R82133
theorem R22001 : Reach 22001 := rs (se 2 (by rfl) ⟨8250, by rfl⟩) R16501
theorem R22019 : Reach 22019 := rs (se 1 (by rfl) ⟨16514, by rfl⟩) R33029
theorem R22049 : Reach 22049 := rs (se 2 (by rfl) ⟨8268, by rfl⟩) R16537
theorem R87601 : Reach 87601 := rs (se 2 (by rfl) ⟨32850, by rfl⟩) R65701
theorem R22067 : Reach 22067 := rs (se 1 (by rfl) ⟨16550, by rfl⟩) R33101
theorem R22081 : Reach 22081 := rs (se 2 (by rfl) ⟨8280, by rfl⟩) R16561
theorem R22097 : Reach 22097 := rs (se 2 (by rfl) ⟨8286, by rfl⟩) R16573
theorem R22099 : Reach 22099 := rs (se 1 (by rfl) ⟨16574, by rfl⟩) R33149
theorem R22115 : Reach 22115 := rs (se 1 (by rfl) ⟨16586, by rfl⟩) R33173
theorem R54883 : Reach 54883 := rs (se 1 (by rfl) ⟨41162, by rfl⟩) R82325
theorem R22145 : Reach 22145 := rs (se 2 (by rfl) ⟨8304, by rfl⟩) R16609
theorem R22163 : Reach 22163 := rs (se 1 (by rfl) ⟨16622, by rfl⟩) R33245
theorem R22193 : Reach 22193 := rs (se 2 (by rfl) ⟨8322, by rfl⟩) R16645
theorem R22195 : Reach 22195 := rs (se 1 (by rfl) ⟨16646, by rfl⟩) R33293
theorem R22211 : Reach 22211 := rs (se 1 (by rfl) ⟨16658, by rfl⟩) R33317
theorem R22225 : Reach 22225 := rs (se 2 (by rfl) ⟨8334, by rfl⟩) R16669
theorem R22241 : Reach 22241 := rs (se 2 (by rfl) ⟨8340, by rfl⟩) R16681
theorem R22243 : Reach 22243 := rs (se 1 (by rfl) ⟨16682, by rfl⟩) R33365
theorem R55025 : Reach 55025 := rs (se 2 (by rfl) ⟨20634, by rfl⟩) R41269
theorem R22259 : Reach 22259 := rs (se 1 (by rfl) ⟨16694, by rfl⟩) R33389
theorem R22289 : Reach 22289 := rs (se 2 (by rfl) ⟨8358, by rfl⟩) R16717
theorem R22307 : Reach 22307 := rs (se 1 (by rfl) ⟨16730, by rfl⟩) R33461
theorem R22337 : Reach 22337 := rs (se 2 (by rfl) ⟨8376, by rfl⟩) R16753
theorem R22355 : Reach 22355 := rs (se 1 (by rfl) ⟨16766, by rfl⟩) R33533
theorem R22369 : Reach 22369 := rs (se 2 (by rfl) ⟨8388, by rfl⟩) R16777
theorem R22385 : Reach 22385 := rs (se 2 (by rfl) ⟨8394, by rfl⟩) R16789
theorem R22387 : Reach 22387 := rs (se 1 (by rfl) ⟨16790, by rfl⟩) R33581
theorem R22403 : Reach 22403 := rs (se 1 (by rfl) ⟨16802, by rfl⟩) R33605
theorem R55181 : Reach 55181 := rs (se 3 (by rfl) ⟨10346, by rfl⟩) R20693
theorem R22433 : Reach 22433 := rs (se 2 (by rfl) ⟨8412, by rfl⟩) R16825
theorem R22451 : Reach 22451 := rs (se 1 (by rfl) ⟨16838, by rfl⟩) R33677
theorem R22481 : Reach 22481 := rs (se 2 (by rfl) ⟨8430, by rfl⟩) R16861
theorem R22499 : Reach 22499 := rs (se 1 (by rfl) ⟨16874, by rfl⟩) R33749
theorem R22513 : Reach 22513 := rs (se 2 (by rfl) ⟨8442, by rfl⟩) R16885
theorem R22529 : Reach 22529 := rs (se 2 (by rfl) ⟨8448, by rfl⟩) R16897
theorem R22531 : Reach 22531 := rs (se 1 (by rfl) ⟨16898, by rfl⟩) R33797
theorem R22547 : Reach 22547 := rs (se 1 (by rfl) ⟨16910, by rfl⟩) R33821
theorem R22577 : Reach 22577 := rs (se 2 (by rfl) ⟨8466, by rfl⟩) R16933
theorem R22595 : Reach 22595 := rs (se 1 (by rfl) ⟨16946, by rfl⟩) R33893
theorem R22609 : Reach 22609 := rs (se 2 (by rfl) ⟨8478, by rfl⟩) R16957
theorem R22625 : Reach 22625 := rs (se 2 (by rfl) ⟨8484, by rfl⟩) R16969
theorem R22643 : Reach 22643 := rs (se 1 (by rfl) ⟨16982, by rfl⟩) R33965
theorem R22673 : Reach 22673 := rs (se 2 (by rfl) ⟨8502, by rfl⟩) R17005
theorem R22675 : Reach 22675 := rs (se 1 (by rfl) ⟨17006, by rfl⟩) R34013
theorem R22691 : Reach 22691 := rs (se 1 (by rfl) ⟨17018, by rfl⟩) R34037
theorem R22721 : Reach 22721 := rs (se 2 (by rfl) ⟨8520, by rfl⟩) R17041
theorem R22739 : Reach 22739 := rs (se 1 (by rfl) ⟨17054, by rfl⟩) R34109
theorem R22753 : Reach 22753 := rs (se 2 (by rfl) ⟨8532, by rfl⟩) R17065
theorem R22769 : Reach 22769 := rs (se 2 (by rfl) ⟨8538, by rfl⟩) R17077
theorem R22771 : Reach 22771 := rs (se 1 (by rfl) ⟨17078, by rfl⟩) R34157
theorem R22787 : Reach 22787 := rs (se 1 (by rfl) ⟨17090, by rfl⟩) R34181
theorem R55565 : Reach 55565 := rs (se 3 (by rfl) ⟨10418, by rfl⟩) R20837
theorem R22801 : Reach 22801 := rs (se 2 (by rfl) ⟨8550, by rfl⟩) R17101
theorem R22865 : Reach 22865 := rs (se 2 (by rfl) ⟨8574, by rfl⟩) R17149
theorem R22883 : Reach 22883 := rs (se 1 (by rfl) ⟨17162, by rfl⟩) R34325
theorem R22961 : Reach 22961 := rs (se 2 (by rfl) ⟨8610, by rfl⟩) R17221
theorem R22979 : Reach 22979 := rs (se 1 (by rfl) ⟨17234, by rfl⟩) R34469
theorem R23057 : Reach 23057 := rs (se 2 (by rfl) ⟨8646, by rfl⟩) R17293
theorem R23075 : Reach 23075 := rs (se 1 (by rfl) ⟨17306, by rfl⟩) R34613
theorem R318005 : Reach 318005 := rs (se 5 (by rfl) ⟨14906, by rfl⟩) R29813
theorem R23153 : Reach 23153 := rs (se 2 (by rfl) ⟨8682, by rfl⟩) R17365
theorem R23171 : Reach 23171 := rs (se 1 (by rfl) ⟨17378, by rfl⟩) R34757
theorem R23203 : Reach 23203 := rs (se 1 (by rfl) ⟨17402, by rfl⟩) R34805
theorem R23249 : Reach 23249 := rs (se 2 (by rfl) ⟨8718, by rfl⟩) R17437
theorem R23267 : Reach 23267 := rs (se 1 (by rfl) ⟨17450, by rfl⟩) R34901
theorem R23345 : Reach 23345 := rs (se 2 (by rfl) ⟨8754, by rfl⟩) R17509
theorem R23363 : Reach 23363 := rs (se 1 (by rfl) ⟨17522, by rfl⟩) R35045
theorem R23395 : Reach 23395 := rs (se 1 (by rfl) ⟨17546, by rfl⟩) R35093
theorem R23441 : Reach 23441 := rs (se 2 (by rfl) ⟨8790, by rfl⟩) R17581
theorem R23459 : Reach 23459 := rs (se 1 (by rfl) ⟨17594, by rfl⟩) R35189
theorem R23537 : Reach 23537 := rs (se 2 (by rfl) ⟨8826, by rfl⟩) R17653
theorem R23555 : Reach 23555 := rs (se 1 (by rfl) ⟨17666, by rfl⟩) R35333
theorem R56369 : Reach 56369 := rs (se 2 (by rfl) ⟨21138, by rfl⟩) R42277
theorem R121925 : Reach 121925 := rs (se 4 (by rfl) ⟨11430, by rfl⟩) R22861
theorem R23633 : Reach 23633 := rs (se 2 (by rfl) ⟨8862, by rfl⟩) R17725
theorem R23651 : Reach 23651 := rs (se 1 (by rfl) ⟨17738, by rfl⟩) R35477
theorem R23665 : Reach 23665 := rs (se 2 (by rfl) ⟨8874, by rfl⟩) R17749
theorem R56483 : Reach 56483 := rs (se 1 (by rfl) ⟨42362, by rfl⟩) R84725
theorem R56497 : Reach 56497 := rs (se 2 (by rfl) ⟨21186, by rfl⟩) R42373
theorem R23729 : Reach 23729 := rs (se 2 (by rfl) ⟨8898, by rfl⟩) R17797
theorem R23747 : Reach 23747 := rs (se 1 (by rfl) ⟨17810, by rfl⟩) R35621
theorem R23761 : Reach 23761 := rs (se 2 (by rfl) ⟨8910, by rfl⟩) R17821
theorem R23825 : Reach 23825 := rs (se 2 (by rfl) ⟨8934, by rfl⟩) R17869
theorem R23843 : Reach 23843 := rs (se 1 (by rfl) ⟨17882, by rfl⟩) R35765
theorem R23921 : Reach 23921 := rs (se 2 (by rfl) ⟨8970, by rfl⟩) R17941
theorem R23939 : Reach 23939 := rs (se 1 (by rfl) ⟨17954, by rfl⟩) R35909
theorem R23971 : Reach 23971 := rs (se 1 (by rfl) ⟨17978, by rfl⟩) R35957
theorem R56753 : Reach 56753 := rs (se 2 (by rfl) ⟨21282, by rfl⟩) R42565
theorem R24017 : Reach 24017 := rs (se 2 (by rfl) ⟨9006, by rfl⟩) R18013
theorem R24035 : Reach 24035 := rs (se 1 (by rfl) ⟨18026, by rfl⟩) R36053
theorem R89585 : Reach 89585 := rs (se 2 (by rfl) ⟨33594, by rfl⟩) R67189
theorem R24067 : Reach 24067 := rs (se 1 (by rfl) ⟨18050, by rfl⟩) R36101
theorem R122381 : Reach 122381 := rs (se 3 (by rfl) ⟨22946, by rfl⟩) R45893
theorem R24113 : Reach 24113 := rs (se 2 (by rfl) ⟨9042, by rfl⟩) R18085
theorem R24131 : Reach 24131 := rs (se 1 (by rfl) ⟨18098, by rfl⟩) R36197
theorem R24209 : Reach 24209 := rs (se 2 (by rfl) ⟨9078, by rfl⟩) R18157
theorem R24227 : Reach 24227 := rs (se 1 (by rfl) ⟨18170, by rfl⟩) R36341
theorem R24259 : Reach 24259 := rs (se 1 (by rfl) ⟨18194, by rfl⟩) R36389
theorem R24305 : Reach 24305 := rs (se 2 (by rfl) ⟨9114, by rfl⟩) R18229
theorem R122609 : Reach 122609 := rs (se 2 (by rfl) ⟨45978, by rfl⟩) R91957
theorem R24323 : Reach 24323 := rs (se 1 (by rfl) ⟨18242, by rfl⟩) R36485
theorem R24401 : Reach 24401 := rs (se 2 (by rfl) ⟨9150, by rfl⟩) R18301
theorem R24419 : Reach 24419 := rs (se 1 (by rfl) ⟨18314, by rfl⟩) R36629
theorem R24497 : Reach 24497 := rs (se 2 (by rfl) ⟨9186, by rfl⟩) R18373
theorem R24515 : Reach 24515 := rs (se 1 (by rfl) ⟨18386, by rfl⟩) R36773
theorem R57293 : Reach 57293 := rs (se 3 (by rfl) ⟨10742, by rfl⟩) R21485
theorem R24529 : Reach 24529 := rs (se 2 (by rfl) ⟨9198, by rfl⟩) R18397
theorem R24593 : Reach 24593 := rs (se 2 (by rfl) ⟨9222, by rfl⟩) R18445
theorem R24611 : Reach 24611 := rs (se 1 (by rfl) ⟨18458, by rfl⟩) R36917
theorem R24689 : Reach 24689 := rs (se 2 (by rfl) ⟨9258, by rfl⟩) R18517
theorem R24707 : Reach 24707 := rs (se 1 (by rfl) ⟨18530, by rfl⟩) R37061
theorem R24785 : Reach 24785 := rs (se 2 (by rfl) ⟨9294, by rfl⟩) R18589
theorem R24803 : Reach 24803 := rs (se 1 (by rfl) ⟨18602, by rfl⟩) R37205
theorem R24881 : Reach 24881 := rs (se 2 (by rfl) ⟨9330, by rfl⟩) R18661
theorem R24899 : Reach 24899 := rs (se 1 (by rfl) ⟨18674, by rfl⟩) R37349
theorem R483725 : Reach 483725 := rs (se 3 (by rfl) ⟨90698, by rfl⟩) R181397
theorem R24977 : Reach 24977 := rs (se 2 (by rfl) ⟨9366, by rfl⟩) R18733
theorem R24995 : Reach 24995 := rs (se 1 (by rfl) ⟨18746, by rfl⟩) R37493
theorem R25073 : Reach 25073 := rs (se 2 (by rfl) ⟨9402, by rfl⟩) R18805
theorem R25091 : Reach 25091 := rs (se 1 (by rfl) ⟨18818, by rfl⟩) R37637
theorem R25105 : Reach 25105 := rs (se 2 (by rfl) ⟨9414, by rfl⟩) R18829
theorem R25123 : Reach 25123 := rs (se 1 (by rfl) ⟨18842, by rfl⟩) R37685
theorem R25169 : Reach 25169 := rs (se 2 (by rfl) ⟨9438, by rfl⟩) R18877
theorem R57955 : Reach 57955 := rs (se 1 (by rfl) ⟨43466, by rfl⟩) R86933
theorem R25187 : Reach 25187 := rs (se 1 (by rfl) ⟨18890, by rfl⟩) R37781
theorem R25201 : Reach 25201 := rs (se 2 (by rfl) ⟨9450, by rfl⟩) R18901
theorem R25219 : Reach 25219 := rs (se 1 (by rfl) ⟨18914, by rfl⟩) R37829
theorem R25265 : Reach 25265 := rs (se 2 (by rfl) ⟨9474, by rfl⟩) R18949
theorem R25283 : Reach 25283 := rs (se 1 (by rfl) ⟨18962, by rfl⟩) R37925
theorem R58097 : Reach 58097 := rs (se 2 (by rfl) ⟨21786, by rfl⟩) R43573
theorem R25361 : Reach 25361 := rs (se 2 (by rfl) ⟨9510, by rfl⟩) R19021
theorem R25379 : Reach 25379 := rs (se 1 (by rfl) ⟨19034, by rfl⟩) R38069
theorem R25393 : Reach 25393 := rs (se 2 (by rfl) ⟨9522, by rfl⟩) R19045
theorem R58211 : Reach 58211 := rs (se 1 (by rfl) ⟨43658, by rfl⟩) R87317
theorem R25457 : Reach 25457 := rs (se 2 (by rfl) ⟨9546, by rfl⟩) R19093
theorem R25475 : Reach 25475 := rs (se 1 (by rfl) ⟨19106, by rfl⟩) R38213
theorem R91043 : Reach 91043 := rs (se 1 (by rfl) ⟨68282, by rfl⟩) R136565
theorem R25553 : Reach 25553 := rs (se 2 (by rfl) ⟨9582, by rfl⟩) R19165
theorem R25571 : Reach 25571 := rs (se 1 (by rfl) ⟨19178, by rfl⟩) R38357
theorem R123875 : Reach 123875 := rs (se 1 (by rfl) ⟨92906, by rfl⟩) R185813
theorem R25649 : Reach 25649 := rs (se 2 (by rfl) ⟨9618, by rfl⟩) R19237
theorem R25667 : Reach 25667 := rs (se 1 (by rfl) ⟨19250, by rfl⟩) R38501
theorem R91205 : Reach 91205 := rs (se 4 (by rfl) ⟨8550, by rfl⟩) R17101
theorem R58481 : Reach 58481 := rs (se 2 (by rfl) ⟨21930, by rfl⟩) R43861
theorem R25745 : Reach 25745 := rs (se 2 (by rfl) ⟨9654, by rfl⟩) R19309
theorem R25763 : Reach 25763 := rs (se 1 (by rfl) ⟨19322, by rfl⟩) R38645
theorem R124145 : Reach 124145 := rs (se 2 (by rfl) ⟨46554, by rfl⟩) R93109
theorem R25841 : Reach 25841 := rs (se 2 (by rfl) ⟨9690, by rfl⟩) R19381
theorem R25859 : Reach 25859 := rs (se 1 (by rfl) ⟨19394, by rfl⟩) R38789
theorem R25937 : Reach 25937 := rs (se 2 (by rfl) ⟨9726, by rfl⟩) R19453
theorem R25955 : Reach 25955 := rs (se 1 (by rfl) ⟨19466, by rfl⟩) R38933
theorem R25987 : Reach 25987 := rs (se 1 (by rfl) ⟨19490, by rfl⟩) R38981
theorem R26033 : Reach 26033 := rs (se 2 (by rfl) ⟨9762, by rfl⟩) R19525
theorem R26051 : Reach 26051 := rs (se 1 (by rfl) ⟨19538, by rfl⟩) R39077
theorem R26065 : Reach 26065 := rs (se 2 (by rfl) ⟨9774, by rfl⟩) R19549
theorem R26129 : Reach 26129 := rs (se 2 (by rfl) ⟨9798, by rfl⟩) R19597
theorem R26147 : Reach 26147 := rs (se 1 (by rfl) ⟨19610, by rfl⟩) R39221
theorem R26225 : Reach 26225 := rs (se 2 (by rfl) ⟨9834, by rfl⟩) R19669
theorem R26243 : Reach 26243 := rs (se 1 (by rfl) ⟨19682, by rfl⟩) R39365
theorem R59021 : Reach 59021 := rs (se 3 (by rfl) ⟨11066, by rfl⟩) R22133
theorem R26257 : Reach 26257 := rs (se 2 (by rfl) ⟨9846, by rfl⟩) R19693
theorem R26321 : Reach 26321 := rs (se 2 (by rfl) ⟨9870, by rfl⟩) R19741
theorem R26339 : Reach 26339 := rs (se 1 (by rfl) ⟨19754, by rfl⟩) R39509
theorem R26417 : Reach 26417 := rs (se 2 (by rfl) ⟨9906, by rfl⟩) R19813
theorem R26435 : Reach 26435 := rs (se 1 (by rfl) ⟨19826, by rfl⟩) R39653
theorem R26449 : Reach 26449 := rs (se 2 (by rfl) ⟨9918, by rfl⟩) R19837
theorem R26513 : Reach 26513 := rs (se 2 (by rfl) ⟨9942, by rfl⟩) R19885
theorem R26531 : Reach 26531 := rs (se 1 (by rfl) ⟨19898, by rfl⟩) R39797
theorem R26563 : Reach 26563 := rs (se 1 (by rfl) ⟨19922, by rfl⟩) R39845
theorem R26609 : Reach 26609 := rs (se 2 (by rfl) ⟨9978, by rfl⟩) R19957
theorem R26627 : Reach 26627 := rs (se 1 (by rfl) ⟨19970, by rfl⟩) R39941
theorem R26705 : Reach 26705 := rs (se 2 (by rfl) ⟨10014, by rfl⟩) R20029
theorem R26723 : Reach 26723 := rs (se 1 (by rfl) ⟨20042, by rfl⟩) R40085
theorem R26801 : Reach 26801 := rs (se 2 (by rfl) ⟨10050, by rfl⟩) R20101
theorem R26819 : Reach 26819 := rs (se 1 (by rfl) ⟨20114, by rfl⟩) R40229
theorem R26851 : Reach 26851 := rs (se 1 (by rfl) ⟨20138, by rfl⟩) R40277
theorem R26897 : Reach 26897 := rs (se 2 (by rfl) ⟨10086, by rfl⟩) R20173
theorem R26915 : Reach 26915 := rs (se 1 (by rfl) ⟨20186, by rfl⟩) R40373
theorem R26993 : Reach 26993 := rs (se 2 (by rfl) ⟨10122, by rfl⟩) R20245
theorem R27011 : Reach 27011 := rs (se 1 (by rfl) ⟨20258, by rfl⟩) R40517
theorem R27089 : Reach 27089 := rs (se 2 (by rfl) ⟨10158, by rfl⟩) R20317
theorem R27107 : Reach 27107 := rs (se 1 (by rfl) ⟨20330, by rfl⟩) R40661
theorem R27121 : Reach 27121 := rs (se 2 (by rfl) ⟨10170, by rfl⟩) R20341
theorem R59939 : Reach 59939 := rs (se 1 (by rfl) ⟨44954, by rfl⟩) R89909
theorem R27185 : Reach 27185 := rs (se 2 (by rfl) ⟨10194, by rfl⟩) R20389
theorem R27203 : Reach 27203 := rs (se 1 (by rfl) ⟨20402, by rfl⟩) R40805
theorem R27281 : Reach 27281 := rs (se 2 (by rfl) ⟨10230, by rfl⟩) R20461
theorem R27299 : Reach 27299 := rs (se 1 (by rfl) ⟨20474, by rfl⟩) R40949
theorem R27377 : Reach 27377 := rs (se 2 (by rfl) ⟨10266, by rfl⟩) R20533
theorem R27395 : Reach 27395 := rs (se 1 (by rfl) ⟨20546, by rfl⟩) R41093
theorem R60173 : Reach 60173 := rs (se 3 (by rfl) ⟨11282, by rfl⟩) R22565
theorem R60209 : Reach 60209 := rs (se 2 (by rfl) ⟨22578, by rfl⟩) R45157
theorem R27473 : Reach 27473 := rs (se 2 (by rfl) ⟨10302, by rfl⟩) R20605
theorem R27491 : Reach 27491 := rs (se 1 (by rfl) ⟨20618, by rfl⟩) R41237
theorem R27569 : Reach 27569 := rs (se 2 (by rfl) ⟨10338, by rfl⟩) R20677
theorem R27587 : Reach 27587 := rs (se 1 (by rfl) ⟨20690, by rfl⟩) R41381
theorem R27665 : Reach 27665 := rs (se 2 (by rfl) ⟨10374, by rfl⟩) R20749
theorem R27683 : Reach 27683 := rs (se 1 (by rfl) ⟨20762, by rfl⟩) R41525
theorem R27697 : Reach 27697 := rs (se 2 (by rfl) ⟨10386, by rfl⟩) R20773
theorem R27715 : Reach 27715 := rs (se 1 (by rfl) ⟨20786, by rfl⟩) R41573
theorem R27761 : Reach 27761 := rs (se 2 (by rfl) ⟨10410, by rfl⟩) R20821
theorem R27779 : Reach 27779 := rs (se 1 (by rfl) ⟨20834, by rfl⟩) R41669
theorem R27793 : Reach 27793 := rs (se 2 (by rfl) ⟨10422, by rfl⟩) R20845
theorem R27857 : Reach 27857 := rs (se 2 (by rfl) ⟨10446, by rfl⟩) R20893
theorem R27875 : Reach 27875 := rs (se 1 (by rfl) ⟨20906, by rfl⟩) R41813
theorem R27953 : Reach 27953 := rs (se 2 (by rfl) ⟨10482, by rfl⟩) R20965
theorem R27971 : Reach 27971 := rs (se 1 (by rfl) ⟨20978, by rfl⟩) R41957
theorem R60749 : Reach 60749 := rs (se 3 (by rfl) ⟨11390, by rfl⟩) R22781
theorem R27985 : Reach 27985 := rs (se 2 (by rfl) ⟨10494, by rfl⟩) R20989
theorem R28049 : Reach 28049 := rs (se 2 (by rfl) ⟨10518, by rfl⟩) R21037
theorem R28067 : Reach 28067 := rs (se 1 (by rfl) ⟨21050, by rfl⟩) R42101
theorem R28081 : Reach 28081 := rs (se 2 (by rfl) ⟨10530, by rfl⟩) R21061
theorem R28145 : Reach 28145 := rs (se 2 (by rfl) ⟨10554, by rfl⟩) R21109
theorem R28163 : Reach 28163 := rs (se 1 (by rfl) ⟨21122, by rfl⟩) R42245
theorem R28241 : Reach 28241 := rs (se 2 (by rfl) ⟨10590, by rfl⟩) R21181
theorem R28259 : Reach 28259 := rs (se 1 (by rfl) ⟨21194, by rfl⟩) R42389
theorem R61069 : Reach 61069 := rs (se 3 (by rfl) ⟨11450, by rfl⟩) R22901
theorem R28337 : Reach 28337 := rs (se 2 (by rfl) ⟨10626, by rfl⟩) R21253
theorem R28355 : Reach 28355 := rs (se 1 (by rfl) ⟨21266, by rfl⟩) R42533
theorem R28433 : Reach 28433 := rs (se 2 (by rfl) ⟨10662, by rfl⟩) R21325
theorem R28451 : Reach 28451 := rs (se 1 (by rfl) ⟨21338, by rfl⟩) R42677
theorem R28529 : Reach 28529 := rs (se 2 (by rfl) ⟨10698, by rfl⟩) R21397
theorem R28547 : Reach 28547 := rs (se 1 (by rfl) ⟨21410, by rfl⟩) R42821
theorem R28579 : Reach 28579 := rs (se 1 (by rfl) ⟨21434, by rfl⟩) R42869
theorem R28625 : Reach 28625 := rs (se 2 (by rfl) ⟨10734, by rfl⟩) R21469
theorem R28643 : Reach 28643 := rs (se 1 (by rfl) ⟨21482, by rfl⟩) R42965
theorem R28721 : Reach 28721 := rs (se 2 (by rfl) ⟨10770, by rfl⟩) R21541
theorem R28739 : Reach 28739 := rs (se 1 (by rfl) ⟨21554, by rfl⟩) R43109
theorem R28817 : Reach 28817 := rs (se 2 (by rfl) ⟨10806, by rfl⟩) R21613
theorem R28835 : Reach 28835 := rs (se 1 (by rfl) ⟨21626, by rfl⟩) R43253
theorem R28849 : Reach 28849 := rs (se 2 (by rfl) ⟨10818, by rfl⟩) R21637
theorem R94405 : Reach 94405 := rs (se 4 (by rfl) ⟨8850, by rfl⟩) R17701
theorem R61667 : Reach 61667 := rs (se 1 (by rfl) ⟨46250, by rfl⟩) R92501
theorem R61681 : Reach 61681 := rs (se 2 (by rfl) ⟨23130, by rfl⟩) R46261
theorem R28913 : Reach 28913 := rs (se 2 (by rfl) ⟨10842, by rfl⟩) R21685
theorem R28931 : Reach 28931 := rs (se 1 (by rfl) ⟨21698, by rfl⟩) R43397
theorem R29009 : Reach 29009 := rs (se 2 (by rfl) ⟨10878, by rfl⟩) R21757
theorem R127331 : Reach 127331 := rs (se 1 (by rfl) ⟨95498, by rfl⟩) R190997
theorem R29027 : Reach 29027 := rs (se 1 (by rfl) ⟨21770, by rfl⟩) R43541
theorem R29105 : Reach 29105 := rs (se 2 (by rfl) ⟨10914, by rfl⟩) R21829
theorem R29123 : Reach 29123 := rs (se 1 (by rfl) ⟨21842, by rfl⟩) R43685
theorem R61937 : Reach 61937 := rs (se 2 (by rfl) ⟨23226, by rfl⟩) R46453
theorem R29201 : Reach 29201 := rs (se 2 (by rfl) ⟨10950, by rfl⟩) R21901
theorem R29219 : Reach 29219 := rs (se 1 (by rfl) ⟨21914, by rfl⟩) R43829
theorem R29251 : Reach 29251 := rs (se 1 (by rfl) ⟨21938, by rfl⟩) R43877
theorem R29297 : Reach 29297 := rs (se 2 (by rfl) ⟨10986, by rfl⟩) R21973
theorem R29315 : Reach 29315 := rs (se 1 (by rfl) ⟨21986, by rfl⟩) R43973
theorem R94861 : Reach 94861 := rs (se 3 (by rfl) ⟨17786, by rfl⟩) R35573
theorem R225989 : Reach 225989 := rs (se 4 (by rfl) ⟨21186, by rfl⟩) R42373
theorem R29393 : Reach 29393 := rs (se 2 (by rfl) ⟨11022, by rfl⟩) R22045
theorem R29411 : Reach 29411 := rs (se 1 (by rfl) ⟨22058, by rfl⟩) R44117
theorem R29443 : Reach 29443 := rs (se 1 (by rfl) ⟨22082, by rfl⟩) R44165
theorem R29489 : Reach 29489 := rs (se 2 (by rfl) ⟨11058, by rfl⟩) R22117
theorem R29507 : Reach 29507 := rs (se 1 (by rfl) ⟨22130, by rfl⟩) R44261
theorem R29585 : Reach 29585 := rs (se 2 (by rfl) ⟨11094, by rfl⟩) R22189
theorem R29603 : Reach 29603 := rs (se 1 (by rfl) ⟨22202, by rfl⟩) R44405
theorem R29681 : Reach 29681 := rs (se 2 (by rfl) ⟨11130, by rfl⟩) R22261
theorem R29699 : Reach 29699 := rs (se 1 (by rfl) ⟨22274, by rfl⟩) R44549
theorem R62477 : Reach 62477 := rs (se 3 (by rfl) ⟨11714, by rfl⟩) R23429
theorem R29713 : Reach 29713 := rs (se 2 (by rfl) ⟨11142, by rfl⟩) R22285
theorem R29777 : Reach 29777 := rs (se 2 (by rfl) ⟨11166, by rfl⟩) R22333
theorem R29795 : Reach 29795 := rs (se 1 (by rfl) ⟨22346, by rfl⟩) R44693
theorem R29873 : Reach 29873 := rs (se 2 (by rfl) ⟨11202, by rfl⟩) R22405
theorem R29891 : Reach 29891 := rs (se 1 (by rfl) ⟨22418, by rfl⟩) R44837
theorem R29969 : Reach 29969 := rs (se 2 (by rfl) ⟨11238, by rfl⟩) R22477
theorem R29987 : Reach 29987 := rs (se 1 (by rfl) ⟨22490, by rfl⟩) R44981
theorem R30161 : Reach 30161 := rs (se 2 (by rfl) ⟨11310, by rfl⟩) R22621
theorem R30179 : Reach 30179 := rs (se 1 (by rfl) ⟨22634, by rfl⟩) R45269
theorem R30257 : Reach 30257 := rs (se 2 (by rfl) ⟨11346, by rfl⟩) R22693
theorem R30275 : Reach 30275 := rs (se 1 (by rfl) ⟨22706, by rfl⟩) R45413
theorem R30307 : Reach 30307 := rs (se 1 (by rfl) ⟨22730, by rfl⟩) R45461
theorem R63089 : Reach 63089 := rs (se 2 (by rfl) ⟨23658, by rfl⟩) R47317
theorem R63139 : Reach 63139 := rs (se 1 (by rfl) ⟨47354, by rfl⟩) R94709
theorem R95941 : Reach 95941 := rs (se 4 (by rfl) ⟨8994, by rfl⟩) R17989
theorem R30449 : Reach 30449 := rs (se 2 (by rfl) ⟨11418, by rfl⟩) R22837
theorem R30545 : Reach 30545 := rs (se 2 (by rfl) ⟨11454, by rfl⟩) R22909
theorem R30563 : Reach 30563 := rs (se 1 (by rfl) ⟨22922, by rfl⟩) R45845
theorem R30577 : Reach 30577 := rs (se 2 (by rfl) ⟨11466, by rfl⟩) R22933
theorem R63395 : Reach 63395 := rs (se 1 (by rfl) ⟨47546, by rfl⟩) R95093
theorem R128965 : Reach 128965 := rs (se 4 (by rfl) ⟨12090, by rfl⟩) R24181
theorem R96227 : Reach 96227 := rs (se 1 (by rfl) ⟨72170, by rfl⟩) R144341
theorem R30755 : Reach 30755 := rs (se 1 (by rfl) ⟨23066, by rfl⟩) R46133
theorem R30833 : Reach 30833 := rs (se 2 (by rfl) ⟨11562, by rfl⟩) R23125
theorem R30851 : Reach 30851 := rs (se 1 (by rfl) ⟨23138, by rfl⟩) R46277
theorem R63629 : Reach 63629 := rs (se 3 (by rfl) ⟨11930, by rfl⟩) R23861
theorem R63665 : Reach 63665 := rs (se 2 (by rfl) ⟨23874, by rfl⟩) R47749
theorem R31025 : Reach 31025 := rs (se 2 (by rfl) ⟨11634, by rfl⟩) R23269
theorem R31043 : Reach 31043 := rs (se 1 (by rfl) ⟨23282, by rfl⟩) R46565
theorem R31121 : Reach 31121 := rs (se 2 (by rfl) ⟨11670, by rfl⟩) R23341
theorem R31139 : Reach 31139 := rs (se 1 (by rfl) ⟨23354, by rfl⟩) R46709
theorem R31171 : Reach 31171 := rs (se 1 (by rfl) ⟨23378, by rfl⟩) R46757
theorem R162317 : Reach 162317 := rs (se 3 (by rfl) ⟨30434, by rfl⟩) R60869
theorem R227893 : Reach 227893 := rs (se 5 (by rfl) ⟨10682, by rfl⟩) R21365
theorem R31313 : Reach 31313 := rs (se 2 (by rfl) ⟨11742, by rfl⟩) R23485
theorem R31409 : Reach 31409 := rs (se 2 (by rfl) ⟨11778, by rfl⟩) R23557
theorem R31427 : Reach 31427 := rs (se 1 (by rfl) ⟨23570, by rfl⟩) R47141
theorem R64205 : Reach 64205 := rs (se 3 (by rfl) ⟨12038, by rfl⟩) R24077
theorem R31441 : Reach 31441 := rs (se 2 (by rfl) ⟨11790, by rfl⟩) R23581
theorem R97037 : Reach 97037 := rs (se 3 (by rfl) ⟨18194, by rfl⟩) R36389
theorem R31537 : Reach 31537 := rs (se 2 (by rfl) ⟨11826, by rfl⟩) R23653
theorem R31601 : Reach 31601 := rs (se 2 (by rfl) ⟨11850, by rfl⟩) R23701
theorem R31697 : Reach 31697 := rs (se 2 (by rfl) ⟨11886, by rfl⟩) R23773
theorem R31715 : Reach 31715 := rs (se 1 (by rfl) ⟨23786, by rfl⟩) R47573
theorem R64547 : Reach 64547 := rs (se 1 (by rfl) ⟨48410, by rfl⟩) R96821
theorem R31811 : Reach 31811 := rs (se 1 (by rfl) ⟨23858, by rfl⟩) R47717
theorem R31907 : Reach 31907 := rs (se 1 (by rfl) ⟨23930, by rfl⟩) R47861
theorem R64739 : Reach 64739 := rs (se 1 (by rfl) ⟨48554, by rfl⟩) R97109
theorem R31985 : Reach 31985 := rs (se 2 (by rfl) ⟨11994, by rfl⟩) R23989
theorem R32003 : Reach 32003 := rs (se 1 (by rfl) ⟨24002, by rfl⟩) R48005
theorem R32035 : Reach 32035 := rs (se 1 (by rfl) ⟨24026, by rfl⟩) R48053
theorem R32113 : Reach 32113 := rs (se 2 (by rfl) ⟨12042, by rfl⟩) R24085
theorem R32177 : Reach 32177 := rs (se 2 (by rfl) ⟨12066, by rfl⟩) R24133
theorem R32273 : Reach 32273 := rs (se 2 (by rfl) ⟨12102, by rfl⟩) R24205
theorem R32291 : Reach 32291 := rs (se 1 (by rfl) ⟨24218, by rfl⟩) R48437
theorem R32305 : Reach 32305 := rs (se 2 (by rfl) ⟨12114, by rfl⟩) R24229
theorem R65123 : Reach 65123 := rs (se 1 (by rfl) ⟨48842, by rfl⟩) R97685
theorem R130673 : Reach 130673 := rs (se 2 (by rfl) ⟨49002, by rfl⟩) R98005
theorem R32561 : Reach 32561 := rs (se 2 (by rfl) ⟨12210, by rfl⟩) R24421
theorem R32579 : Reach 32579 := rs (se 1 (by rfl) ⟨24434, by rfl⟩) R48869
theorem R65393 : Reach 65393 := rs (se 2 (by rfl) ⟨24522, by rfl⟩) R49045
theorem R32791 : Reach 32791 := rs (se 1 (by rfl) ⟨24593, by rfl⟩) R49187
theorem R33047 : Reach 33047 := rs (se 1 (by rfl) ⟨24785, by rfl⟩) R49571
theorem R33203 : Reach 33203 := rs (se 1 (by rfl) ⟨24902, by rfl⟩) R49805
theorem R33227 : Reach 33227 := rs (se 1 (by rfl) ⟨24920, by rfl⟩) R49841
theorem R98765 : Reach 98765 := rs (se 3 (by rfl) ⟨18518, by rfl⟩) R37037
theorem R197081 : Reach 197081 := rs (se 2 (by rfl) ⟨73905, by rfl⟩) R147811
theorem R33331 : Reach 33331 := rs (se 1 (by rfl) ⟨24998, by rfl⟩) R49997
theorem R33473 : Reach 33473 := rs (se 2 (by rfl) ⟨12552, by rfl⟩) R25105
theorem R33497 : Reach 33497 := rs (se 2 (by rfl) ⟨12561, by rfl⟩) R25123
theorem R33587 : Reach 33587 := rs (se 1 (by rfl) ⟨25190, by rfl⟩) R50381
theorem R33601 : Reach 33601 := rs (se 2 (by rfl) ⟨12600, by rfl⟩) R25201
theorem R33625 : Reach 33625 := rs (se 2 (by rfl) ⟨12609, by rfl⟩) R25219
theorem R66521 : Reach 66521 := rs (se 2 (by rfl) ⟨24945, by rfl⟩) R49891
theorem R33857 : Reach 33857 := rs (se 2 (by rfl) ⟨12696, by rfl⟩) R25393
theorem R66635 : Reach 66635 := rs (se 1 (by rfl) ⟨49976, by rfl⟩) R99953
theorem R99629 : Reach 99629 := rs (se 3 (by rfl) ⟨18680, by rfl⟩) R37361
theorem R34199 : Reach 34199 := rs (se 1 (by rfl) ⟨25649, by rfl⟩) R51299
theorem R34379 : Reach 34379 := rs (se 1 (by rfl) ⟨25784, by rfl⟩) R51569
theorem R34397 : Reach 34397 := rs (se 3 (by rfl) ⟨6449, by rfl⟩) R12899
theorem R34649 : Reach 34649 := rs (se 2 (by rfl) ⟨12993, by rfl⟩) R25987
theorem R34739 : Reach 34739 := rs (se 1 (by rfl) ⟨26054, by rfl⟩) R52109
theorem R34753 : Reach 34753 := rs (se 2 (by rfl) ⟨13032, by rfl⟩) R26065
theorem R67715 : Reach 67715 := rs (se 1 (by rfl) ⟨50786, by rfl⟩) R101573
theorem R133271 : Reach 133271 := rs (se 1 (by rfl) ⟨99953, by rfl⟩) R199907
theorem R67763 : Reach 67763 := rs (se 1 (by rfl) ⟨50822, by rfl⟩) R101645
theorem R35009 : Reach 35009 := rs (se 2 (by rfl) ⟨13128, by rfl⟩) R26257
theorem R133325 : Reach 133325 := rs (se 3 (by rfl) ⟨24998, by rfl⟩) R49997
theorem R35095 : Reach 35095 := rs (se 1 (by rfl) ⟨26321, by rfl⟩) R52643
theorem R35147 : Reach 35147 := rs (se 1 (by rfl) ⟨26360, by rfl⟩) R52721
theorem R35275 : Reach 35275 := rs (se 1 (by rfl) ⟨26456, by rfl⟩) R52913
theorem R133649 : Reach 133649 := rs (se 2 (by rfl) ⟨50118, by rfl⟩) R100237
theorem R35351 : Reach 35351 := rs (se 1 (by rfl) ⟨26513, by rfl⟩) R53027
theorem R68161 : Reach 68161 := rs (se 2 (by rfl) ⟨25560, by rfl⟩) R51121
theorem R35417 : Reach 35417 := rs (se 2 (by rfl) ⟨13281, by rfl⟩) R26563
theorem R35531 : Reach 35531 := rs (se 1 (by rfl) ⟨26648, by rfl⟩) R53297
theorem R101081 : Reach 101081 := rs (se 2 (by rfl) ⟨37905, by rfl⟩) R75811
theorem R35549 : Reach 35549 := rs (se 3 (by rfl) ⟨6665, by rfl⟩) R13331
theorem R101155 : Reach 101155 := rs (se 1 (by rfl) ⟨75866, by rfl⟩) R151733
theorem R101195 : Reach 101195 := rs (se 1 (by rfl) ⟨75896, by rfl⟩) R151793
theorem R199523 : Reach 199523 := rs (se 1 (by rfl) ⟨149642, by rfl⟩) R299285
theorem R35801 : Reach 35801 := rs (se 2 (by rfl) ⟨13425, by rfl⟩) R26851
theorem R35891 : Reach 35891 := rs (se 1 (by rfl) ⟨26918, by rfl⟩) R53837
theorem R68825 : Reach 68825 := rs (se 2 (by rfl) ⟨25809, by rfl⟩) R51619
theorem R36161 : Reach 36161 := rs (se 2 (by rfl) ⟨13560, by rfl⟩) R27121
theorem R36247 : Reach 36247 := rs (se 1 (by rfl) ⟨27185, by rfl⟩) R54371
theorem R36445 : Reach 36445 := rs (se 3 (by rfl) ⟨6833, by rfl⟩) R13667
theorem R36503 : Reach 36503 := rs (se 1 (by rfl) ⟨27377, by rfl⟩) R54755
theorem R36683 : Reach 36683 := rs (se 1 (by rfl) ⟨27512, by rfl⟩) R55025
theorem R36701 : Reach 36701 := rs (se 3 (by rfl) ⟨6881, by rfl⟩) R13763
theorem R36787 : Reach 36787 := rs (se 1 (by rfl) ⟨27590, by rfl⟩) R55181
theorem R36929 : Reach 36929 := rs (se 2 (by rfl) ⟨13848, by rfl⟩) R27697
theorem R36953 : Reach 36953 := rs (se 2 (by rfl) ⟨13857, by rfl⟩) R27715
theorem R37043 : Reach 37043 := rs (se 1 (by rfl) ⟨27782, by rfl⟩) R55565
theorem R37057 : Reach 37057 := rs (se 2 (by rfl) ⟨13896, by rfl⟩) R27793
theorem R102721 : Reach 102721 := rs (se 2 (by rfl) ⟨38520, by rfl⟩) R77041
theorem R37313 : Reach 37313 := rs (se 2 (by rfl) ⟨13992, by rfl⟩) R27985
theorem R70105 : Reach 70105 := rs (se 2 (by rfl) ⟨26289, by rfl⟩) R52579
theorem R37441 : Reach 37441 := rs (se 2 (by rfl) ⟨14040, by rfl⟩) R28081
theorem R70237 : Reach 70237 := rs (se 3 (by rfl) ⟨13169, by rfl⟩) R26339
theorem R37579 : Reach 37579 := rs (se 1 (by rfl) ⟨28184, by rfl⟩) R56369
theorem R37597 : Reach 37597 := rs (se 3 (by rfl) ⟨7049, by rfl⟩) R14099
theorem R37655 : Reach 37655 := rs (se 1 (by rfl) ⟨28241, by rfl⟩) R56483
theorem R37835 : Reach 37835 := rs (se 1 (by rfl) ⟨28376, by rfl⟩) R56753
theorem R37853 : Reach 37853 := rs (se 3 (by rfl) ⟨7097, by rfl⟩) R14195
theorem R103517 : Reach 103517 := rs (se 3 (by rfl) ⟨19409, by rfl⟩) R38819
theorem R38105 : Reach 38105 := rs (se 2 (by rfl) ⟨14289, by rfl⟩) R28579
theorem R38195 : Reach 38195 := rs (se 1 (by rfl) ⟨28646, by rfl⟩) R57293
theorem R103781 : Reach 103781 := rs (se 4 (by rfl) ⟨9729, by rfl⟩) R19459
theorem R71063 : Reach 71063 := rs (se 1 (by rfl) ⟨53297, by rfl⟩) R106595
theorem R38465 : Reach 38465 := rs (se 2 (by rfl) ⟨14424, by rfl⟩) R28849
theorem R366277 : Reach 366277 := rs (se 4 (by rfl) ⟨34338, by rfl⟩) R68677
theorem R71441 : Reach 71441 := rs (se 2 (by rfl) ⟨26790, by rfl⟩) R53581
theorem R38731 : Reach 38731 := rs (se 1 (by rfl) ⟨29048, by rfl⟩) R58097
theorem R38807 : Reach 38807 := rs (se 1 (by rfl) ⟨29105, by rfl⟩) R58211
theorem R71603 : Reach 71603 := rs (se 1 (by rfl) ⟨53702, by rfl⟩) R107405
theorem R38987 : Reach 38987 := rs (se 1 (by rfl) ⟨29240, by rfl⟩) R58481
theorem R39001 : Reach 39001 := rs (se 2 (by rfl) ⟨14625, by rfl⟩) R29251
theorem R39005 : Reach 39005 := rs (se 3 (by rfl) ⟨7313, by rfl⟩) R14627
theorem R137537 : Reach 137537 := rs (se 2 (by rfl) ⟨51576, by rfl⟩) R103153
theorem R39257 : Reach 39257 := rs (se 2 (by rfl) ⟨14721, by rfl⟩) R29443
theorem R39347 : Reach 39347 := rs (se 1 (by rfl) ⟨29510, by rfl⟩) R59021
theorem R72323 : Reach 72323 := rs (se 1 (by rfl) ⟨54242, by rfl⟩) R108485
theorem R105137 : Reach 105137 := rs (se 2 (by rfl) ⟨39426, by rfl⟩) R78853
theorem R39617 : Reach 39617 := rs (se 2 (by rfl) ⟨14856, by rfl⟩) R29713
theorem R236465 : Reach 236465 := rs (se 2 (by rfl) ⟨88674, by rfl⟩) R177349
theorem R39959 : Reach 39959 := rs (se 1 (by rfl) ⟨29969, by rfl⟩) R59939
theorem R269347 : Reach 269347 := rs (se 1 (by rfl) ⟨202010, by rfl⟩) R404021
theorem R40115 : Reach 40115 := rs (se 1 (by rfl) ⟨30086, by rfl⟩) R60173
theorem R40139 : Reach 40139 := rs (se 1 (by rfl) ⟨30104, by rfl⟩) R60209
theorem R40157 : Reach 40157 := rs (se 3 (by rfl) ⟨7529, by rfl⟩) R15059
theorem R73061 : Reach 73061 := rs (se 4 (by rfl) ⟨6849, by rfl⟩) R13699
theorem R40409 : Reach 40409 := rs (se 2 (by rfl) ⟨15153, by rfl⟩) R30307
theorem R40499 : Reach 40499 := rs (se 1 (by rfl) ⟨30374, by rfl⟩) R60749
theorem R40769 : Reach 40769 := rs (se 2 (by rfl) ⟨15288, by rfl⟩) R30577
theorem R73547 : Reach 73547 := rs (se 1 (by rfl) ⟨55160, by rfl⟩) R110321
theorem R204643 : Reach 204643 := rs (se 1 (by rfl) ⟨153482, by rfl⟩) R306965
theorem R171953 : Reach 171953 := rs (se 2 (by rfl) ⟨64482, by rfl⟩) R128965
theorem R40925 : Reach 40925 := rs (se 3 (by rfl) ⟨7673, by rfl⟩) R15347
theorem R41053 : Reach 41053 := rs (se 3 (by rfl) ⟨7697, by rfl⟩) R15395
theorem R41111 : Reach 41111 := rs (se 1 (by rfl) ⟨30833, by rfl⟩) R61667
theorem R41291 : Reach 41291 := rs (se 1 (by rfl) ⟨30968, by rfl⟩) R61937
theorem R41309 : Reach 41309 := rs (se 3 (by rfl) ⟨7745, by rfl⟩) R15491
theorem R41561 : Reach 41561 := rs (se 2 (by rfl) ⟨15585, by rfl⟩) R31171
theorem R172637 : Reach 172637 := rs (se 3 (by rfl) ⟨32369, by rfl⟩) R64739
theorem R41651 : Reach 41651 := rs (se 1 (by rfl) ⟨31238, by rfl⟩) R62477
theorem R303857 : Reach 303857 := rs (se 2 (by rfl) ⟨113946, by rfl⟩) R227893
theorem R107365 : Reach 107365 := rs (se 4 (by rfl) ⟨10065, by rfl⟩) R20131
theorem R41921 : Reach 41921 := rs (se 2 (by rfl) ⟨15720, by rfl⟩) R31441
theorem R42049 : Reach 42049 := rs (se 2 (by rfl) ⟨15768, by rfl⟩) R31537
theorem R42059 : Reach 42059 := rs (se 1 (by rfl) ⟨31544, by rfl⟩) R63089
theorem R42077 : Reach 42077 := rs (se 3 (by rfl) ⟨7889, by rfl⟩) R15779
theorem R42263 : Reach 42263 := rs (se 1 (by rfl) ⟨31697, by rfl⟩) R63395
theorem R402733 : Reach 402733 := rs (se 3 (by rfl) ⟨75512, by rfl⟩) R151025
theorem R42419 : Reach 42419 := rs (se 1 (by rfl) ⟨31814, by rfl⟩) R63629
theorem R42443 : Reach 42443 := rs (se 1 (by rfl) ⟨31832, by rfl⟩) R63665
theorem R42461 : Reach 42461 := rs (se 3 (by rfl) ⟨7961, by rfl⟩) R15923
theorem R75329 : Reach 75329 := rs (se 2 (by rfl) ⟨28248, by rfl⟩) R56497
theorem R108125 : Reach 108125 := rs (se 3 (by rfl) ⟨20273, by rfl⟩) R40547
theorem R108211 : Reach 108211 := rs (se 1 (by rfl) ⟨81158, by rfl⟩) R162317
theorem R42713 : Reach 42713 := rs (se 2 (by rfl) ⟨16017, by rfl⟩) R32035
theorem R141061 : Reach 141061 := rs (se 4 (by rfl) ⟨13224, by rfl⟩) R26449
theorem R42803 : Reach 42803 := rs (se 1 (by rfl) ⟨32102, by rfl⟩) R64205
theorem R42817 : Reach 42817 := rs (se 2 (by rfl) ⟨16056, by rfl⟩) R32113
theorem R43031 : Reach 43031 := rs (se 1 (by rfl) ⟨32273, by rfl⟩) R64547
theorem R43073 : Reach 43073 := rs (se 2 (by rfl) ⟨16152, by rfl⟩) R32305
theorem R272645 : Reach 272645 := rs (se 4 (by rfl) ⟨25560, by rfl⟩) R51121
theorem R43415 : Reach 43415 := rs (se 1 (by rfl) ⟨32561, by rfl⟩) R65123
theorem R43595 : Reach 43595 := rs (se 1 (by rfl) ⟨32696, by rfl⟩) R65393
theorem R43613 : Reach 43613 := rs (se 3 (by rfl) ⟨8177, by rfl⟩) R16355
theorem R43699 : Reach 43699 := rs (se 1 (by rfl) ⟨32774, by rfl⟩) R65549
theorem R43841 : Reach 43841 := rs (se 2 (by rfl) ⟨16440, by rfl⟩) R32881
theorem R43865 : Reach 43865 := rs (se 2 (by rfl) ⟨16449, by rfl⟩) R32899
theorem R43955 : Reach 43955 := rs (se 1 (by rfl) ⟨32966, by rfl⟩) R65933
theorem R109745 : Reach 109745 := rs (se 2 (by rfl) ⟨41154, by rfl⟩) R82309
theorem R44225 : Reach 44225 := rs (se 2 (by rfl) ⟨16584, by rfl⟩) R33169
theorem R77273 : Reach 77273 := rs (se 2 (by rfl) ⟨28977, by rfl⟩) R57955
theorem R44509 : Reach 44509 := rs (se 3 (by rfl) ⟨8345, by rfl⟩) R16691
theorem R44567 : Reach 44567 := rs (se 1 (by rfl) ⟨33425, by rfl⟩) R66851
theorem R142883 : Reach 142883 := rs (se 1 (by rfl) ⟨107162, by rfl⟩) R214325
theorem R44747 : Reach 44747 := rs (se 1 (by rfl) ⟨33560, by rfl⟩) R67121
theorem R44765 : Reach 44765 := rs (se 3 (by rfl) ⟨8393, by rfl⟩) R16787
theorem R45107 : Reach 45107 := rs (se 1 (by rfl) ⟨33830, by rfl⟩) R67661
theorem R45335 : Reach 45335 := rs (se 1 (by rfl) ⟨34001, by rfl⟩) R68003
theorem R143795 : Reach 143795 := rs (se 1 (by rfl) ⟨107846, by rfl⟩) R215693
theorem R12843 : Reach 12843 := rs (se 1 (by rfl) ⟨9632, by rfl⟩) R19265
theorem R12855 : Reach 12855 := rs (se 1 (by rfl) ⟨9641, by rfl⟩) R19283
theorem R45643 : Reach 45643 := rs (se 1 (by rfl) ⟨34232, by rfl⟩) R68465
theorem R12875 : Reach 12875 := rs (se 1 (by rfl) ⟨9656, by rfl⟩) R19313
theorem R111179 : Reach 111179 := rs (se 1 (by rfl) ⟨83384, by rfl⟩) R166769
theorem R12887 : Reach 12887 := rs (se 1 (by rfl) ⟨9665, by rfl⟩) R19331
theorem R12907 : Reach 12907 := rs (se 1 (by rfl) ⟨9680, by rfl⟩) R19361
theorem R12919 : Reach 12919 := rs (se 1 (by rfl) ⟨9689, by rfl⟩) R19379
theorem R12939 : Reach 12939 := rs (se 1 (by rfl) ⟨9704, by rfl⟩) R19409
theorem R12951 : Reach 12951 := rs (se 1 (by rfl) ⟨9713, by rfl⟩) R19427
theorem R12971 : Reach 12971 := rs (se 1 (by rfl) ⟨9728, by rfl⟩) R19457
theorem R78515 : Reach 78515 := rs (se 1 (by rfl) ⟨58886, by rfl⟩) R117773
theorem R12983 : Reach 12983 := rs (se 1 (by rfl) ⟨9737, by rfl⟩) R19475
theorem R13003 : Reach 13003 := rs (se 1 (by rfl) ⟨9752, by rfl⟩) R19505
theorem R13015 : Reach 13015 := rs (se 1 (by rfl) ⟨9761, by rfl⟩) R19523
theorem R45785 : Reach 45785 := rs (se 2 (by rfl) ⟨17169, by rfl⟩) R34339
theorem R13035 : Reach 13035 := rs (se 1 (by rfl) ⟨9776, by rfl⟩) R19553
theorem R13047 : Reach 13047 := rs (se 1 (by rfl) ⟨9785, by rfl⟩) R19571
theorem R13067 : Reach 13067 := rs (se 1 (by rfl) ⟨9800, by rfl⟩) R19601
theorem R13079 : Reach 13079 := rs (se 1 (by rfl) ⟨9809, by rfl⟩) R19619
theorem R13099 : Reach 13099 := rs (se 1 (by rfl) ⟨9824, by rfl⟩) R19649
theorem R13111 : Reach 13111 := rs (se 1 (by rfl) ⟨9833, by rfl⟩) R19667
theorem R13131 : Reach 13131 := rs (se 1 (by rfl) ⟨9848, by rfl⟩) R19697
theorem R45899 : Reach 45899 := rs (se 1 (by rfl) ⟨34424, by rfl⟩) R68849
theorem R13143 : Reach 13143 := rs (se 1 (by rfl) ⟨9857, by rfl⟩) R19715
theorem R45917 : Reach 45917 := rs (se 3 (by rfl) ⟨8609, by rfl⟩) R17219
theorem R13163 : Reach 13163 := rs (se 1 (by rfl) ⟨9872, by rfl⟩) R19745
theorem R13175 : Reach 13175 := rs (se 1 (by rfl) ⟨9881, by rfl⟩) R19763
theorem R13195 : Reach 13195 := rs (se 1 (by rfl) ⟨9896, by rfl⟩) R19793
theorem R13207 : Reach 13207 := rs (se 1 (by rfl) ⟨9905, by rfl⟩) R19811
theorem R13227 : Reach 13227 := rs (se 1 (by rfl) ⟨9920, by rfl⟩) R19841
theorem R13239 : Reach 13239 := rs (se 1 (by rfl) ⟨9929, by rfl⟩) R19859
theorem R13259 : Reach 13259 := rs (se 1 (by rfl) ⟨9944, by rfl⟩) R19889
theorem R13271 : Reach 13271 := rs (se 1 (by rfl) ⟨9953, by rfl⟩) R19907
theorem R13291 : Reach 13291 := rs (se 1 (by rfl) ⟨9968, by rfl⟩) R19937
theorem R13303 : Reach 13303 := rs (se 1 (by rfl) ⟨9977, by rfl⟩) R19955
theorem R13323 : Reach 13323 := rs (se 1 (by rfl) ⟨9992, by rfl⟩) R19985
theorem R13335 : Reach 13335 := rs (se 1 (by rfl) ⟨10001, by rfl⟩) R20003
theorem R13355 : Reach 13355 := rs (se 1 (by rfl) ⟨10016, by rfl⟩) R20033
theorem R78893 : Reach 78893 := rs (se 3 (by rfl) ⟨14792, by rfl⟩) R29585
theorem R13367 : Reach 13367 := rs (se 1 (by rfl) ⟨10025, by rfl⟩) R20051
theorem R13387 : Reach 13387 := rs (se 1 (by rfl) ⟨10040, by rfl⟩) R20081
theorem R13399 : Reach 13399 := rs (se 1 (by rfl) ⟨10049, by rfl⟩) R20099
theorem R46169 : Reach 46169 := rs (se 2 (by rfl) ⟨17313, by rfl⟩) R34627
theorem R13419 : Reach 13419 := rs (se 1 (by rfl) ⟨10064, by rfl⟩) R20129
theorem R13431 : Reach 13431 := rs (se 1 (by rfl) ⟨10073, by rfl⟩) R20147
theorem R13451 : Reach 13451 := rs (se 1 (by rfl) ⟨10088, by rfl⟩) R20177
theorem R13463 : Reach 13463 := rs (se 1 (by rfl) ⟨10097, by rfl⟩) R20195
theorem R13483 : Reach 13483 := rs (se 1 (by rfl) ⟨10112, by rfl⟩) R20225
theorem R13495 : Reach 13495 := rs (se 1 (by rfl) ⟨10121, by rfl⟩) R20243
theorem R13515 : Reach 13515 := rs (se 1 (by rfl) ⟨10136, by rfl⟩) R20273
theorem R13527 : Reach 13527 := rs (se 1 (by rfl) ⟨10145, by rfl⟩) R20291
theorem R13547 : Reach 13547 := rs (se 1 (by rfl) ⟨10160, by rfl⟩) R20321
theorem R13559 : Reach 13559 := rs (se 1 (by rfl) ⟨10169, by rfl⟩) R20339
theorem R13579 : Reach 13579 := rs (se 1 (by rfl) ⟨10184, by rfl⟩) R20369
theorem R13591 : Reach 13591 := rs (se 1 (by rfl) ⟨10193, by rfl⟩) R20387
theorem R13611 : Reach 13611 := rs (se 1 (by rfl) ⟨10208, by rfl⟩) R20417
theorem R13623 : Reach 13623 := rs (se 1 (by rfl) ⟨10217, by rfl⟩) R20435
theorem R13643 : Reach 13643 := rs (se 1 (by rfl) ⟨10232, by rfl⟩) R20465
theorem R13655 : Reach 13655 := rs (se 1 (by rfl) ⟨10241, by rfl⟩) R20483
theorem R13675 : Reach 13675 := rs (se 1 (by rfl) ⟨10256, by rfl⟩) R20513
theorem R13687 : Reach 13687 := rs (se 1 (by rfl) ⟨10265, by rfl⟩) R20531
theorem R13707 : Reach 13707 := rs (se 1 (by rfl) ⟨10280, by rfl⟩) R20561
theorem R13719 : Reach 13719 := rs (se 1 (by rfl) ⟨10289, by rfl⟩) R20579
theorem R13739 : Reach 13739 := rs (se 1 (by rfl) ⟨10304, by rfl⟩) R20609
theorem R13751 : Reach 13751 := rs (se 1 (by rfl) ⟨10313, by rfl⟩) R20627
theorem R13771 : Reach 13771 := rs (se 1 (by rfl) ⟨10328, by rfl⟩) R20657
theorem R13783 : Reach 13783 := rs (se 1 (by rfl) ⟨10337, by rfl⟩) R20675
theorem R13803 : Reach 13803 := rs (se 1 (by rfl) ⟨10352, by rfl⟩) R20705
theorem R13815 : Reach 13815 := rs (se 1 (by rfl) ⟨10361, by rfl⟩) R20723
theorem R46595 : Reach 46595 := rs (se 1 (by rfl) ⟨34946, by rfl⟩) R69893
theorem R13835 : Reach 13835 := rs (se 1 (by rfl) ⟨10376, by rfl⟩) R20753
theorem R13847 : Reach 13847 := rs (se 1 (by rfl) ⟨10385, by rfl⟩) R20771
theorem R46615 : Reach 46615 := rs (se 1 (by rfl) ⟨34961, by rfl⟩) R69923
theorem R13867 : Reach 13867 := rs (se 1 (by rfl) ⟨10400, by rfl⟩) R20801
theorem R13879 : Reach 13879 := rs (se 1 (by rfl) ⟨10409, by rfl⟩) R20819
theorem R13899 : Reach 13899 := rs (se 1 (by rfl) ⟨10424, by rfl⟩) R20849
theorem R13911 : Reach 13911 := rs (se 1 (by rfl) ⟨10433, by rfl⟩) R20867
theorem R13931 : Reach 13931 := rs (se 1 (by rfl) ⟨10448, by rfl⟩) R20897
theorem R13943 : Reach 13943 := rs (se 1 (by rfl) ⟨10457, by rfl⟩) R20915
theorem R13963 : Reach 13963 := rs (se 1 (by rfl) ⟨10472, by rfl⟩) R20945
theorem R13975 : Reach 13975 := rs (se 1 (by rfl) ⟨10481, by rfl⟩) R20963
theorem R13995 : Reach 13995 := rs (se 1 (by rfl) ⟨10496, by rfl⟩) R20993
theorem R14007 : Reach 14007 := rs (se 1 (by rfl) ⟨10505, by rfl⟩) R21011
theorem R14027 : Reach 14027 := rs (se 1 (by rfl) ⟨10520, by rfl⟩) R21041
theorem R14039 : Reach 14039 := rs (se 1 (by rfl) ⟨10529, by rfl⟩) R21059
theorem R14059 : Reach 14059 := rs (se 1 (by rfl) ⟨10544, by rfl⟩) R21089
theorem R14071 : Reach 14071 := rs (se 1 (by rfl) ⟨10553, by rfl⟩) R21107
theorem R14091 : Reach 14091 := rs (se 1 (by rfl) ⟨10568, by rfl⟩) R21137
theorem R46871 : Reach 46871 := rs (se 1 (by rfl) ⟨35153, by rfl⟩) R70307
theorem R14103 : Reach 14103 := rs (se 1 (by rfl) ⟨10577, by rfl⟩) R21155
theorem R14123 : Reach 14123 := rs (se 1 (by rfl) ⟨10592, by rfl⟩) R21185
theorem R14135 : Reach 14135 := rs (se 1 (by rfl) ⟨10601, by rfl⟩) R21203
theorem R14155 : Reach 14155 := rs (se 1 (by rfl) ⟨10616, by rfl⟩) R21233
theorem R14167 : Reach 14167 := rs (se 1 (by rfl) ⟨10625, by rfl⟩) R21251
theorem R14187 : Reach 14187 := rs (se 1 (by rfl) ⟨10640, by rfl⟩) R21281
theorem R178037 : Reach 178037 := rs (se 5 (by rfl) ⟨8345, by rfl⟩) R16691
theorem R14199 : Reach 14199 := rs (se 1 (by rfl) ⟨10649, by rfl⟩) R21299
theorem R46979 : Reach 46979 := rs (se 1 (by rfl) ⟨35234, by rfl⟩) R70469
theorem R14219 : Reach 14219 := rs (se 1 (by rfl) ⟨10664, by rfl⟩) R21329
theorem R14231 : Reach 14231 := rs (se 1 (by rfl) ⟨10673, by rfl⟩) R21347
theorem R14251 : Reach 14251 := rs (se 1 (by rfl) ⟨10688, by rfl⟩) R21377
theorem R47027 : Reach 47027 := rs (se 1 (by rfl) ⟨35270, by rfl⟩) R70541
theorem R14263 : Reach 14263 := rs (se 1 (by rfl) ⟨10697, by rfl⟩) R21395
theorem R14283 : Reach 14283 := rs (se 1 (by rfl) ⟨10712, by rfl⟩) R21425
theorem R47051 : Reach 47051 := rs (se 1 (by rfl) ⟨35288, by rfl⟩) R70577
theorem R14295 : Reach 14295 := rs (se 1 (by rfl) ⟨10721, by rfl⟩) R21443
theorem R14315 : Reach 14315 := rs (se 1 (by rfl) ⟨10736, by rfl⟩) R21473
theorem R14327 : Reach 14327 := rs (se 1 (by rfl) ⟨10745, by rfl⟩) R21491
theorem R14347 : Reach 14347 := rs (se 1 (by rfl) ⟨10760, by rfl⟩) R21521
theorem R14359 : Reach 14359 := rs (se 1 (by rfl) ⟨10769, by rfl⟩) R21539
theorem R14379 : Reach 14379 := rs (se 1 (by rfl) ⟨10784, by rfl⟩) R21569
theorem R14391 : Reach 14391 := rs (se 1 (by rfl) ⟨10793, by rfl⟩) R21587
theorem R14411 : Reach 14411 := rs (se 1 (by rfl) ⟨10808, by rfl⟩) R21617
theorem R14423 : Reach 14423 := rs (se 1 (by rfl) ⟨10817, by rfl⟩) R21635
theorem R14443 : Reach 14443 := rs (se 1 (by rfl) ⟨10832, by rfl⟩) R21665
theorem R14455 : Reach 14455 := rs (se 1 (by rfl) ⟨10841, by rfl⟩) R21683
theorem R14475 : Reach 14475 := rs (se 1 (by rfl) ⟨10856, by rfl⟩) R21713
theorem R47249 : Reach 47249 := rs (se 2 (by rfl) ⟨17718, by rfl⟩) R35437
theorem R14487 : Reach 14487 := rs (se 1 (by rfl) ⟨10865, by rfl⟩) R21731
theorem R14507 : Reach 14507 := rs (se 1 (by rfl) ⟨10880, by rfl⟩) R21761
theorem R14519 : Reach 14519 := rs (se 1 (by rfl) ⟨10889, by rfl⟩) R21779
theorem R14539 : Reach 14539 := rs (se 1 (by rfl) ⟨10904, by rfl⟩) R21809
theorem R14551 : Reach 14551 := rs (se 1 (by rfl) ⟨10913, by rfl⟩) R21827
theorem R14571 : Reach 14571 := rs (se 1 (by rfl) ⟨10928, by rfl⟩) R21857
theorem R14583 : Reach 14583 := rs (se 1 (by rfl) ⟨10937, by rfl⟩) R21875
theorem R14603 : Reach 14603 := rs (se 1 (by rfl) ⟨10952, by rfl⟩) R21905
theorem R112913 : Reach 112913 := rs (se 2 (by rfl) ⟨42342, by rfl⟩) R84685
theorem R14615 : Reach 14615 := rs (se 1 (by rfl) ⟨10961, by rfl⟩) R21923
theorem R14635 : Reach 14635 := rs (se 1 (by rfl) ⟨10976, by rfl⟩) R21953
theorem R145709 : Reach 145709 := rs (se 3 (by rfl) ⟨27320, by rfl⟩) R54641
theorem R47405 : Reach 47405 := rs (se 3 (by rfl) ⟨8888, by rfl⟩) R17777
theorem R47411 : Reach 47411 := rs (se 1 (by rfl) ⟨35558, by rfl⟩) R71117
theorem R14647 : Reach 14647 := rs (se 1 (by rfl) ⟨10985, by rfl⟩) R21971
theorem R47425 : Reach 47425 := rs (se 2 (by rfl) ⟨17784, by rfl⟩) R35569
theorem R14667 : Reach 14667 := rs (se 1 (by rfl) ⟨11000, by rfl⟩) R22001
theorem R14679 : Reach 14679 := rs (se 1 (by rfl) ⟨11009, by rfl⟩) R22019
theorem R14699 : Reach 14699 := rs (se 1 (by rfl) ⟨11024, by rfl⟩) R22049
theorem R14711 : Reach 14711 := rs (se 1 (by rfl) ⟨11033, by rfl⟩) R22067
theorem R14731 : Reach 14731 := rs (se 1 (by rfl) ⟨11048, by rfl⟩) R22097
theorem R14743 : Reach 14743 := rs (se 1 (by rfl) ⟨11057, by rfl⟩) R22115
theorem R14763 : Reach 14763 := rs (se 1 (by rfl) ⟨11072, by rfl⟩) R22145
theorem R14775 : Reach 14775 := rs (se 1 (by rfl) ⟨11081, by rfl⟩) R22163
theorem R14795 : Reach 14795 := rs (se 1 (by rfl) ⟨11096, by rfl⟩) R22193
theorem R14807 : Reach 14807 := rs (se 1 (by rfl) ⟨11105, by rfl⟩) R22211
theorem R14827 : Reach 14827 := rs (se 1 (by rfl) ⟨11120, by rfl⟩) R22241
theorem R14839 : Reach 14839 := rs (se 1 (by rfl) ⟨11129, by rfl⟩) R22259
theorem R14859 : Reach 14859 := rs (se 1 (by rfl) ⟨11144, by rfl⟩) R22289
theorem R47639 : Reach 47639 := rs (se 1 (by rfl) ⟨35729, by rfl⟩) R71459
theorem R14871 : Reach 14871 := rs (se 1 (by rfl) ⟨11153, by rfl⟩) R22307
theorem R14891 : Reach 14891 := rs (se 1 (by rfl) ⟨11168, by rfl⟩) R22337
theorem R14903 : Reach 14903 := rs (se 1 (by rfl) ⟨11177, by rfl⟩) R22355
theorem R47681 : Reach 47681 := rs (se 2 (by rfl) ⟨17880, by rfl⟩) R35761
theorem R14923 : Reach 14923 := rs (se 1 (by rfl) ⟨11192, by rfl⟩) R22385
theorem R14935 : Reach 14935 := rs (se 1 (by rfl) ⟨11201, by rfl⟩) R22403
theorem R14955 : Reach 14955 := rs (se 1 (by rfl) ⟨11216, by rfl⟩) R22433
theorem R14967 : Reach 14967 := rs (se 1 (by rfl) ⟨11225, by rfl⟩) R22451
theorem R47747 : Reach 47747 := rs (se 1 (by rfl) ⟨35810, by rfl⟩) R71621
theorem R14987 : Reach 14987 := rs (se 1 (by rfl) ⟨11240, by rfl⟩) R22481
theorem R14999 : Reach 14999 := rs (se 1 (by rfl) ⟨11249, by rfl⟩) R22499
theorem R15019 : Reach 15019 := rs (se 1 (by rfl) ⟨11264, by rfl⟩) R22529
theorem R47789 : Reach 47789 := rs (se 3 (by rfl) ⟨8960, by rfl⟩) R17921
theorem R15031 : Reach 15031 := rs (se 1 (by rfl) ⟨11273, by rfl⟩) R22547
theorem R15051 : Reach 15051 := rs (se 1 (by rfl) ⟨11288, by rfl⟩) R22577
theorem R15063 : Reach 15063 := rs (se 1 (by rfl) ⟨11297, by rfl⟩) R22595
theorem R15083 : Reach 15083 := rs (se 1 (by rfl) ⟨11312, by rfl⟩) R22625
theorem R15095 : Reach 15095 := rs (se 1 (by rfl) ⟨11321, by rfl⟩) R22643
theorem R15115 : Reach 15115 := rs (se 1 (by rfl) ⟨11336, by rfl⟩) R22673
theorem R15127 : Reach 15127 := rs (se 1 (by rfl) ⟨11345, by rfl⟩) R22691
theorem R15147 : Reach 15147 := rs (se 1 (by rfl) ⟨11360, by rfl⟩) R22721
theorem R15159 : Reach 15159 := rs (se 1 (by rfl) ⟨11369, by rfl⟩) R22739
theorem R15179 : Reach 15179 := rs (se 1 (by rfl) ⟨11384, by rfl⟩) R22769
theorem R15191 : Reach 15191 := rs (se 1 (by rfl) ⟨11393, by rfl⟩) R22787
theorem R244579 : Reach 244579 := rs (se 1 (by rfl) ⟨183434, by rfl⟩) R366869
theorem R15243 : Reach 15243 := rs (se 1 (by rfl) ⟨11432, by rfl⟩) R22865
theorem R15255 : Reach 15255 := rs (se 1 (by rfl) ⟨11441, by rfl⟩) R22883
theorem R48023 : Reach 48023 := rs (se 1 (by rfl) ⟨36017, by rfl⟩) R72035
theorem R15307 : Reach 15307 := rs (se 1 (by rfl) ⟨11480, by rfl⟩) R22961
theorem R15319 : Reach 15319 := rs (se 1 (by rfl) ⟨11489, by rfl⟩) R22979
theorem R48089 : Reach 48089 := rs (se 2 (by rfl) ⟨18033, by rfl⟩) R36067
theorem R146393 : Reach 146393 := rs (se 2 (by rfl) ⟨54897, by rfl⟩) R109795
theorem R15371 : Reach 15371 := rs (se 1 (by rfl) ⟨11528, by rfl⟩) R23057
theorem R15383 : Reach 15383 := rs (se 1 (by rfl) ⟨11537, by rfl⟩) R23075
theorem R212003 : Reach 212003 := rs (se 1 (by rfl) ⟨159002, by rfl⟩) R318005
theorem R15435 : Reach 15435 := rs (se 1 (by rfl) ⟨11576, by rfl⟩) R23153
theorem R15447 : Reach 15447 := rs (se 1 (by rfl) ⟨11585, by rfl⟩) R23171
theorem R48221 : Reach 48221 := rs (se 3 (by rfl) ⟨9041, by rfl⟩) R18083
theorem R15499 : Reach 15499 := rs (se 1 (by rfl) ⟨11624, by rfl⟩) R23249
theorem R15511 : Reach 15511 := rs (se 1 (by rfl) ⟨11633, by rfl⟩) R23267
theorem R15563 : Reach 15563 := rs (se 1 (by rfl) ⟨11672, by rfl⟩) R23345
theorem R15575 : Reach 15575 := rs (se 1 (by rfl) ⟨11681, by rfl⟩) R23363
theorem R15627 : Reach 15627 := rs (se 1 (by rfl) ⟨11720, by rfl⟩) R23441
theorem R15639 : Reach 15639 := rs (se 1 (by rfl) ⟨11729, by rfl⟩) R23459
theorem R15691 : Reach 15691 := rs (se 1 (by rfl) ⟨11768, by rfl⟩) R23537
theorem R15703 : Reach 15703 := rs (se 1 (by rfl) ⟨11777, by rfl⟩) R23555
theorem R81283 : Reach 81283 := rs (se 1 (by rfl) ⟨60962, by rfl⟩) R121925
theorem R15755 : Reach 15755 := rs (se 1 (by rfl) ⟨11816, by rfl⟩) R23633
theorem R15767 : Reach 15767 := rs (se 1 (by rfl) ⟨11825, by rfl⟩) R23651
theorem R15819 : Reach 15819 := rs (se 1 (by rfl) ⟨11864, by rfl⟩) R23729
theorem R15831 : Reach 15831 := rs (se 1 (by rfl) ⟨11873, by rfl⟩) R23747
theorem R15883 : Reach 15883 := rs (se 1 (by rfl) ⟨11912, by rfl⟩) R23825
theorem R81425 : Reach 81425 := rs (se 2 (by rfl) ⟨30534, by rfl⟩) R61069
theorem R15895 : Reach 15895 := rs (se 1 (by rfl) ⟨11921, by rfl⟩) R23843
theorem R15947 : Reach 15947 := rs (se 1 (by rfl) ⟨11960, by rfl⟩) R23921
theorem R15959 : Reach 15959 := rs (se 1 (by rfl) ⟨11969, by rfl⟩) R23939
theorem R16011 : Reach 16011 := rs (se 1 (by rfl) ⟨12008, by rfl⟩) R24017
theorem R16023 : Reach 16023 := rs (se 1 (by rfl) ⟨12017, by rfl⟩) R24035
theorem R81587 : Reach 81587 := rs (se 1 (by rfl) ⟨61190, by rfl⟩) R122381
theorem R48833 : Reach 48833 := rs (se 2 (by rfl) ⟨18312, by rfl⟩) R36625
theorem R16075 : Reach 16075 := rs (se 1 (by rfl) ⟨12056, by rfl⟩) R24113
theorem R16087 : Reach 16087 := rs (se 1 (by rfl) ⟨12065, by rfl⟩) R24131
theorem R16139 : Reach 16139 := rs (se 1 (by rfl) ⟨12104, by rfl⟩) R24209
theorem R16151 : Reach 16151 := rs (se 1 (by rfl) ⟨12113, by rfl⟩) R24227
theorem R16203 : Reach 16203 := rs (se 1 (by rfl) ⟨12152, by rfl⟩) R24305
theorem R81739 : Reach 81739 := rs (se 1 (by rfl) ⟨61304, by rfl⟩) R122609
theorem R16215 : Reach 16215 := rs (se 1 (by rfl) ⟨12161, by rfl⟩) R24323
theorem R16267 : Reach 16267 := rs (se 1 (by rfl) ⟨12200, by rfl⟩) R24401
theorem R16279 : Reach 16279 := rs (se 1 (by rfl) ⟨12209, by rfl⟩) R24419
theorem R16331 : Reach 16331 := rs (se 1 (by rfl) ⟨12248, by rfl⟩) R24497
theorem R16343 : Reach 16343 := rs (se 1 (by rfl) ⟨12257, by rfl⟩) R24515
theorem R16395 : Reach 16395 := rs (se 1 (by rfl) ⟨12296, by rfl⟩) R24593
theorem R16407 : Reach 16407 := rs (se 1 (by rfl) ⟨12305, by rfl⟩) R24611
theorem R16459 : Reach 16459 := rs (se 1 (by rfl) ⟨12344, by rfl⟩) R24689
theorem R16471 : Reach 16471 := rs (se 1 (by rfl) ⟨12353, by rfl⟩) R24707
theorem R16523 : Reach 16523 := rs (se 1 (by rfl) ⟨12392, by rfl⟩) R24785
theorem R16535 : Reach 16535 := rs (se 1 (by rfl) ⟨12401, by rfl⟩) R24803
theorem R49355 : Reach 49355 := rs (se 1 (by rfl) ⟨37016, by rfl⟩) R74033
theorem R16587 : Reach 16587 := rs (se 1 (by rfl) ⟨12440, by rfl⟩) R24881
theorem R16599 : Reach 16599 := rs (se 1 (by rfl) ⟨12449, by rfl⟩) R24899
theorem R49369 : Reach 49369 := rs (se 2 (by rfl) ⟨18513, by rfl⟩) R37027
theorem R16651 : Reach 16651 := rs (se 1 (by rfl) ⟨12488, by rfl⟩) R24977
theorem R16663 : Reach 16663 := rs (se 1 (by rfl) ⟨12497, by rfl⟩) R24995
theorem R82241 : Reach 82241 := rs (se 2 (by rfl) ⟨30840, by rfl⟩) R61681
theorem R16715 : Reach 16715 := rs (se 1 (by rfl) ⟨12536, by rfl⟩) R25073
theorem R16727 : Reach 16727 := rs (se 1 (by rfl) ⟨12545, by rfl⟩) R25091
theorem R16779 : Reach 16779 := rs (se 1 (by rfl) ⟨12584, by rfl⟩) R25169
theorem R16791 : Reach 16791 := rs (se 1 (by rfl) ⟨12593, by rfl⟩) R25187
theorem R115121 : Reach 115121 := rs (se 2 (by rfl) ⟨43170, by rfl⟩) R86341
theorem R16843 : Reach 16843 := rs (se 1 (by rfl) ⟨12632, by rfl⟩) R25265
theorem R16855 : Reach 16855 := rs (se 1 (by rfl) ⟨12641, by rfl⟩) R25283
theorem R49625 : Reach 49625 := rs (se 2 (by rfl) ⟨18609, by rfl⟩) R37219
theorem R16907 : Reach 16907 := rs (se 1 (by rfl) ⟨12680, by rfl⟩) R25361
theorem R16919 : Reach 16919 := rs (se 1 (by rfl) ⟨12689, by rfl⟩) R25379
theorem R49709 : Reach 49709 := rs (se 3 (by rfl) ⟨9320, by rfl⟩) R18641
theorem R16971 : Reach 16971 := rs (se 1 (by rfl) ⟨12728, by rfl⟩) R25457
theorem R16983 : Reach 16983 := rs (se 1 (by rfl) ⟨12737, by rfl⟩) R25475
theorem R17035 : Reach 17035 := rs (se 1 (by rfl) ⟨12776, by rfl⟩) R25553
theorem R17047 : Reach 17047 := rs (se 1 (by rfl) ⟨12785, by rfl⟩) R25571
theorem R82583 : Reach 82583 := rs (se 1 (by rfl) ⟨61937, by rfl⟩) R123875
theorem R17099 : Reach 17099 := rs (se 1 (by rfl) ⟨12824, by rfl⟩) R25649
theorem R17111 : Reach 17111 := rs (se 1 (by rfl) ⟨12833, by rfl⟩) R25667
theorem R17113 : Reach 17113 := rs (se 2 (by rfl) ⟨6417, by rfl⟩) R12835
theorem R148229 : Reach 148229 := rs (se 4 (by rfl) ⟨13896, by rfl⟩) R27793
theorem R17163 : Reach 17163 := rs (se 1 (by rfl) ⟨12872, by rfl⟩) R25745
theorem R17175 : Reach 17175 := rs (se 1 (by rfl) ⟨12881, by rfl⟩) R25763
theorem R17177 : Reach 17177 := rs (se 2 (by rfl) ⟨6441, by rfl⟩) R12883
theorem R82763 : Reach 82763 := rs (se 1 (by rfl) ⟨62072, by rfl⟩) R124145
theorem R17227 : Reach 17227 := rs (se 1 (by rfl) ⟨12920, by rfl⟩) R25841
theorem R17239 : Reach 17239 := rs (se 1 (by rfl) ⟨12929, by rfl⟩) R25859
theorem R17241 : Reach 17241 := rs (se 2 (by rfl) ⟨6465, by rfl⟩) R12931
theorem R82781 : Reach 82781 := rs (se 3 (by rfl) ⟨15521, by rfl⟩) R31043
theorem R50051 : Reach 50051 := rs (se 1 (by rfl) ⟨37538, by rfl⟩) R75077
theorem R17291 : Reach 17291 := rs (se 1 (by rfl) ⟨12968, by rfl⟩) R25937
theorem R17303 : Reach 17303 := rs (se 1 (by rfl) ⟨12977, by rfl⟩) R25955
theorem R17305 : Reach 17305 := rs (se 2 (by rfl) ⟨6489, by rfl⟩) R12979
theorem R17355 : Reach 17355 := rs (se 1 (by rfl) ⟨13016, by rfl⟩) R26033
theorem R17367 : Reach 17367 := rs (se 1 (by rfl) ⟨13025, by rfl⟩) R26051
theorem R17369 : Reach 17369 := rs (se 2 (by rfl) ⟨6513, by rfl⟩) R13027
theorem R50179 : Reach 50179 := rs (se 1 (by rfl) ⟨37634, by rfl⟩) R75269
theorem R17419 : Reach 17419 := rs (se 1 (by rfl) ⟨13064, by rfl⟩) R26129
theorem R17431 : Reach 17431 := rs (se 1 (by rfl) ⟨13073, by rfl⟩) R26147
theorem R17433 : Reach 17433 := rs (se 2 (by rfl) ⟨6537, by rfl⟩) R13075
theorem R17483 : Reach 17483 := rs (se 1 (by rfl) ⟨13112, by rfl⟩) R26225
theorem R17495 : Reach 17495 := rs (se 1 (by rfl) ⟨13121, by rfl⟩) R26243
theorem R17497 : Reach 17497 := rs (se 2 (by rfl) ⟨6561, by rfl⟩) R13123
theorem R115843 : Reach 115843 := rs (se 1 (by rfl) ⟨86882, by rfl⟩) R173765
theorem R17547 : Reach 17547 := rs (se 1 (by rfl) ⟨13160, by rfl⟩) R26321
theorem R50327 : Reach 50327 := rs (se 1 (by rfl) ⟨37745, by rfl⟩) R75491
theorem R17559 : Reach 17559 := rs (se 1 (by rfl) ⟨13169, by rfl⟩) R26339
theorem R17561 : Reach 17561 := rs (se 2 (by rfl) ⟨6585, by rfl⟩) R13171
theorem R50321 : Reach 50321 := rs (se 2 (by rfl) ⟨18870, by rfl⟩) R37741
theorem R17611 : Reach 17611 := rs (se 1 (by rfl) ⟨13208, by rfl⟩) R26417
theorem R181453 : Reach 181453 := rs (se 3 (by rfl) ⟨34022, by rfl⟩) R68045
theorem R17623 : Reach 17623 := rs (se 1 (by rfl) ⟨13217, by rfl⟩) R26435
theorem R17625 : Reach 17625 := rs (se 2 (by rfl) ⟨6609, by rfl⟩) R13219
theorem R50435 : Reach 50435 := rs (se 1 (by rfl) ⟨37826, by rfl⟩) R75653
theorem R17675 : Reach 17675 := rs (se 1 (by rfl) ⟨13256, by rfl⟩) R26513
theorem R17687 : Reach 17687 := rs (se 1 (by rfl) ⟨13265, by rfl⟩) R26531
theorem R17689 : Reach 17689 := rs (se 2 (by rfl) ⟨6633, by rfl⟩) R13267
theorem R50483 : Reach 50483 := rs (se 1 (by rfl) ⟨37862, by rfl⟩) R75725
theorem R50507 : Reach 50507 := rs (se 1 (by rfl) ⟨37880, by rfl⟩) R75761
theorem R17739 : Reach 17739 := rs (se 1 (by rfl) ⟨13304, by rfl⟩) R26609
theorem R17751 : Reach 17751 := rs (se 1 (by rfl) ⟨13313, by rfl⟩) R26627
theorem R17753 : Reach 17753 := rs (se 2 (by rfl) ⟨6657, by rfl⟩) R13315
theorem R148853 : Reach 148853 := rs (se 5 (by rfl) ⟨6977, by rfl⟩) R13955
theorem R17803 : Reach 17803 := rs (se 1 (by rfl) ⟨13352, by rfl⟩) R26705
theorem R17815 : Reach 17815 := rs (se 1 (by rfl) ⟨13361, by rfl⟩) R26723
theorem R17817 : Reach 17817 := rs (se 2 (by rfl) ⟨6681, by rfl⟩) R13363
theorem R17867 : Reach 17867 := rs (se 1 (by rfl) ⟨13400, by rfl⟩) R26801
theorem R17879 : Reach 17879 := rs (se 1 (by rfl) ⟨13409, by rfl⟩) R26819
theorem R17881 : Reach 17881 := rs (se 2 (by rfl) ⟨6705, by rfl⟩) R13411
theorem R17931 : Reach 17931 := rs (se 1 (by rfl) ⟨13448, by rfl⟩) R26897
theorem R50705 : Reach 50705 := rs (se 2 (by rfl) ⟨19014, by rfl⟩) R38029
theorem R17943 : Reach 17943 := rs (se 1 (by rfl) ⟨13457, by rfl⟩) R26915
theorem R50711 : Reach 50711 := rs (se 1 (by rfl) ⟨38033, by rfl⟩) R76067
theorem R17945 : Reach 17945 := rs (se 2 (by rfl) ⟨6729, by rfl⟩) R13459
theorem R83501 : Reach 83501 := rs (se 3 (by rfl) ⟨15656, by rfl⟩) R31313
theorem R17995 : Reach 17995 := rs (se 1 (by rfl) ⟨13496, by rfl⟩) R26993
theorem R18007 : Reach 18007 := rs (se 1 (by rfl) ⟨13505, by rfl⟩) R27011
theorem R18009 : Reach 18009 := rs (se 2 (by rfl) ⟨6753, by rfl⟩) R13507
theorem R18059 : Reach 18059 := rs (se 1 (by rfl) ⟨13544, by rfl⟩) R27089
theorem R18071 : Reach 18071 := rs (se 1 (by rfl) ⟨13553, by rfl⟩) R27107
theorem R18073 : Reach 18073 := rs (se 2 (by rfl) ⟨6777, by rfl⟩) R13555
theorem R50867 : Reach 50867 := rs (se 1 (by rfl) ⟨38150, by rfl⟩) R76301
theorem R18123 : Reach 18123 := rs (se 1 (by rfl) ⟨13592, by rfl⟩) R27185
theorem R18135 : Reach 18135 := rs (se 1 (by rfl) ⟨13601, by rfl⟩) R27203
theorem R18137 : Reach 18137 := rs (se 2 (by rfl) ⟨6801, by rfl⟩) R13603
theorem R18187 : Reach 18187 := rs (se 1 (by rfl) ⟨13640, by rfl⟩) R27281
theorem R18199 : Reach 18199 := rs (se 1 (by rfl) ⟨13649, by rfl⟩) R27299
theorem R18201 : Reach 18201 := rs (se 2 (by rfl) ⟨6825, by rfl⟩) R13651
theorem R18251 : Reach 18251 := rs (se 1 (by rfl) ⟨13688, by rfl⟩) R27377
theorem R18263 : Reach 18263 := rs (se 1 (by rfl) ⟨13697, by rfl⟩) R27395
theorem R18265 : Reach 18265 := rs (se 2 (by rfl) ⟨6849, by rfl⟩) R13699
theorem R18315 : Reach 18315 := rs (se 1 (by rfl) ⟨13736, by rfl⟩) R27473
theorem R18327 : Reach 18327 := rs (se 1 (by rfl) ⟨13745, by rfl⟩) R27491
theorem R18329 : Reach 18329 := rs (se 2 (by rfl) ⟨6873, by rfl⟩) R13747
theorem R51137 : Reach 51137 := rs (se 2 (by rfl) ⟨19176, by rfl⟩) R38353
theorem R18379 : Reach 18379 := rs (se 1 (by rfl) ⟨13784, by rfl⟩) R27569
theorem R18391 : Reach 18391 := rs (se 1 (by rfl) ⟨13793, by rfl⟩) R27587
theorem R18393 : Reach 18393 := rs (se 2 (by rfl) ⟨6897, by rfl⟩) R13795
theorem R18443 : Reach 18443 := rs (se 1 (by rfl) ⟨13832, by rfl⟩) R27665
theorem R18455 : Reach 18455 := rs (se 1 (by rfl) ⟨13841, by rfl⟩) R27683
theorem R18457 : Reach 18457 := rs (se 2 (by rfl) ⟨6921, by rfl⟩) R13843
theorem R51245 : Reach 51245 := rs (se 3 (by rfl) ⟨9608, by rfl⟩) R19217
theorem R116801 : Reach 116801 := rs (se 2 (by rfl) ⟨43800, by rfl⟩) R87601
theorem R968773 : Reach 968773 := rs (se 4 (by rfl) ⟨90822, by rfl⟩) R181645
theorem R18507 : Reach 18507 := rs (se 1 (by rfl) ⟨13880, by rfl⟩) R27761
theorem R18519 : Reach 18519 := rs (se 1 (by rfl) ⟨13889, by rfl⟩) R27779
theorem R18521 : Reach 18521 := rs (se 2 (by rfl) ⟨6945, by rfl⟩) R13891
theorem R51293 : Reach 51293 := rs (se 3 (by rfl) ⟨9617, by rfl⟩) R19235
theorem R18571 : Reach 18571 := rs (se 1 (by rfl) ⟨13928, by rfl⟩) R27857
theorem R18583 : Reach 18583 := rs (se 1 (by rfl) ⟨13937, by rfl⟩) R27875
theorem R18585 : Reach 18585 := rs (se 2 (by rfl) ⟨6969, by rfl⟩) R13939
theorem R18635 : Reach 18635 := rs (se 1 (by rfl) ⟨13976, by rfl⟩) R27953
theorem R18647 : Reach 18647 := rs (se 1 (by rfl) ⟨13985, by rfl⟩) R27971
theorem R18649 : Reach 18649 := rs (se 2 (by rfl) ⟨6993, by rfl⟩) R13987
theorem R84185 : Reach 84185 := rs (se 2 (by rfl) ⟨31569, by rfl⟩) R63139
theorem R182513 : Reach 182513 := rs (se 2 (by rfl) ⟨68442, by rfl⟩) R136885
theorem R18699 : Reach 18699 := rs (se 1 (by rfl) ⟨14024, by rfl⟩) R28049
theorem R18711 : Reach 18711 := rs (se 1 (by rfl) ⟨14033, by rfl⟩) R28067
theorem R18713 : Reach 18713 := rs (se 2 (by rfl) ⟨7017, by rfl⟩) R14035
theorem R18763 : Reach 18763 := rs (se 1 (by rfl) ⟨14072, by rfl⟩) R28145
theorem R18775 : Reach 18775 := rs (se 1 (by rfl) ⟨14081, by rfl⟩) R28163
theorem R18777 : Reach 18777 := rs (se 2 (by rfl) ⟨7041, by rfl⟩) R14083
theorem R18827 : Reach 18827 := rs (se 1 (by rfl) ⟨14120, by rfl⟩) R28241
theorem R18839 : Reach 18839 := rs (se 1 (by rfl) ⟨14129, by rfl⟩) R28259
theorem R18841 : Reach 18841 := rs (se 2 (by rfl) ⟨7065, by rfl⟩) R14131
theorem R18891 : Reach 18891 := rs (se 1 (by rfl) ⟨14168, by rfl⟩) R28337
theorem R18903 : Reach 18903 := rs (se 1 (by rfl) ⟨14177, by rfl⟩) R28355
theorem R18905 : Reach 18905 := rs (se 2 (by rfl) ⟨7089, by rfl⟩) R14179
theorem R51677 : Reach 51677 := rs (se 3 (by rfl) ⟨9689, by rfl⟩) R19379
theorem R18955 : Reach 18955 := rs (se 1 (by rfl) ⟨14216, by rfl⟩) R28433
theorem R18967 : Reach 18967 := rs (se 1 (by rfl) ⟨14225, by rfl⟩) R28451
theorem R18969 : Reach 18969 := rs (se 2 (by rfl) ⟨7113, by rfl⟩) R14227
theorem R19019 : Reach 19019 := rs (se 1 (by rfl) ⟨14264, by rfl⟩) R28529
theorem R19031 : Reach 19031 := rs (se 1 (by rfl) ⟨14273, by rfl⟩) R28547
theorem R19033 : Reach 19033 := rs (se 2 (by rfl) ⟨7137, by rfl⟩) R14275
theorem R19083 : Reach 19083 := rs (se 1 (by rfl) ⟨14312, by rfl⟩) R28625
theorem R51857 : Reach 51857 := rs (se 2 (by rfl) ⟨19446, by rfl⟩) R38893
theorem R19095 : Reach 19095 := rs (se 1 (by rfl) ⟨14321, by rfl⟩) R28643
theorem R19097 : Reach 19097 := rs (se 2 (by rfl) ⟨7161, by rfl⟩) R14323
theorem R19147 : Reach 19147 := rs (se 1 (by rfl) ⟨14360, by rfl⟩) R28721
theorem R19159 : Reach 19159 := rs (se 1 (by rfl) ⟨14369, by rfl⟩) R28739
theorem R19161 : Reach 19161 := rs (se 2 (by rfl) ⟨7185, by rfl⟩) R14371
theorem R19211 : Reach 19211 := rs (se 1 (by rfl) ⟨14408, by rfl⟩) R28817
theorem R19223 : Reach 19223 := rs (se 1 (by rfl) ⟨14417, by rfl⟩) R28835
theorem R19225 : Reach 19225 := rs (se 2 (by rfl) ⟨7209, by rfl⟩) R14419
theorem R19275 : Reach 19275 := rs (se 1 (by rfl) ⟨14456, by rfl⟩) R28913
theorem R19287 : Reach 19287 := rs (se 1 (by rfl) ⟨14465, by rfl⟩) R28931
theorem R19289 : Reach 19289 := rs (se 2 (by rfl) ⟨7233, by rfl⟩) R14467
theorem R84829 : Reach 84829 := rs (se 3 (by rfl) ⟨15905, by rfl⟩) R31811
theorem R19339 : Reach 19339 := rs (se 1 (by rfl) ⟨14504, by rfl⟩) R29009
theorem R84887 : Reach 84887 := rs (se 1 (by rfl) ⟨63665, by rfl⟩) R127331
theorem R19351 : Reach 19351 := rs (se 1 (by rfl) ⟨14513, by rfl⟩) R29027
theorem R19353 : Reach 19353 := rs (se 2 (by rfl) ⟨7257, by rfl⟩) R14515
theorem R19403 : Reach 19403 := rs (se 1 (by rfl) ⟨14552, by rfl⟩) R29105
theorem R19415 : Reach 19415 := rs (se 1 (by rfl) ⟨14561, by rfl⟩) R29123
theorem R19417 : Reach 19417 := rs (se 2 (by rfl) ⟨7281, by rfl⟩) R14563
theorem R19467 : Reach 19467 := rs (se 1 (by rfl) ⟨14600, by rfl⟩) R29201
theorem R19479 : Reach 19479 := rs (se 1 (by rfl) ⟨14609, by rfl⟩) R29219
theorem R19481 : Reach 19481 := rs (se 2 (by rfl) ⟨7305, by rfl⟩) R14611
theorem R19531 : Reach 19531 := rs (se 1 (by rfl) ⟨14648, by rfl⟩) R29297
theorem R19543 : Reach 19543 := rs (se 1 (by rfl) ⟨14657, by rfl⟩) R29315
theorem R19545 : Reach 19545 := rs (se 2 (by rfl) ⟨7329, by rfl⟩) R14659
theorem R150659 : Reach 150659 := rs (se 1 (by rfl) ⟨112994, by rfl⟩) R225989
theorem R19595 : Reach 19595 := rs (se 1 (by rfl) ⟨14696, by rfl⟩) R29393
theorem R19607 : Reach 19607 := rs (se 1 (by rfl) ⟨14705, by rfl⟩) R29411
theorem R19609 : Reach 19609 := rs (se 2 (by rfl) ⟨7353, by rfl⟩) R14707
theorem R52397 : Reach 52397 := rs (se 3 (by rfl) ⟨9824, by rfl⟩) R19649
theorem R52427 : Reach 52427 := rs (se 1 (by rfl) ⟨39320, by rfl⟩) R78641
theorem R19659 : Reach 19659 := rs (se 1 (by rfl) ⟨14744, by rfl⟩) R29489
theorem R19671 : Reach 19671 := rs (se 1 (by rfl) ⟨14753, by rfl⟩) R29507
theorem R19673 : Reach 19673 := rs (se 2 (by rfl) ⟨7377, by rfl⟩) R14755
theorem R19723 : Reach 19723 := rs (se 1 (by rfl) ⟨14792, by rfl⟩) R29585
theorem R19735 : Reach 19735 := rs (se 1 (by rfl) ⟨14801, by rfl⟩) R29603
theorem R19737 : Reach 19737 := rs (se 2 (by rfl) ⟨7401, by rfl⟩) R14803
theorem R19787 : Reach 19787 := rs (se 1 (by rfl) ⟨14840, by rfl⟩) R29681
theorem R19799 : Reach 19799 := rs (se 1 (by rfl) ⟨14849, by rfl⟩) R29699
theorem R19801 : Reach 19801 := rs (se 2 (by rfl) ⟨7425, by rfl⟩) R14851
theorem R19851 : Reach 19851 := rs (se 1 (by rfl) ⟨14888, by rfl⟩) R29777
theorem R52625 : Reach 52625 := rs (se 2 (by rfl) ⟨19734, by rfl⟩) R39469
theorem R19863 : Reach 19863 := rs (se 1 (by rfl) ⟨14897, by rfl⟩) R29795
theorem R19865 : Reach 19865 := rs (se 2 (by rfl) ⟨7449, by rfl⟩) R14899
theorem R19915 : Reach 19915 := rs (se 1 (by rfl) ⟨14936, by rfl⟩) R29873
theorem R19927 : Reach 19927 := rs (se 1 (by rfl) ⟨14945, by rfl⟩) R29891
theorem R19929 : Reach 19929 := rs (se 2 (by rfl) ⟨7473, by rfl⟩) R14947
theorem R19979 : Reach 19979 := rs (se 1 (by rfl) ⟨14984, by rfl⟩) R29969
theorem R19991 : Reach 19991 := rs (se 1 (by rfl) ⟨14993, by rfl⟩) R29987
theorem R19993 : Reach 19993 := rs (se 2 (by rfl) ⟨7497, by rfl⟩) R14995
theorem R52811 : Reach 52811 := rs (se 1 (by rfl) ⟨39608, by rfl⟩) R79217
theorem R20057 : Reach 20057 := rs (se 2 (by rfl) ⟨7521, by rfl⟩) R15043
theorem R20107 : Reach 20107 := rs (se 1 (by rfl) ⟨15080, by rfl⟩) R30161
theorem R20119 : Reach 20119 := rs (se 1 (by rfl) ⟨15089, by rfl⟩) R30179
theorem R20171 : Reach 20171 := rs (se 1 (by rfl) ⟨15128, by rfl⟩) R30257
theorem R20183 : Reach 20183 := rs (se 1 (by rfl) ⟨15137, by rfl⟩) R30275
theorem R20249 : Reach 20249 := rs (se 2 (by rfl) ⟨7593, by rfl⟩) R15187
theorem R20299 : Reach 20299 := rs (se 1 (by rfl) ⟨15224, by rfl⟩) R30449
theorem R53081 : Reach 53081 := rs (se 2 (by rfl) ⟨19905, by rfl⟩) R39811
theorem R20363 : Reach 20363 := rs (se 1 (by rfl) ⟨15272, by rfl⟩) R30545
theorem R20375 : Reach 20375 := rs (se 1 (by rfl) ⟨15281, by rfl⟩) R30563
theorem R20441 : Reach 20441 := rs (se 2 (by rfl) ⟨7665, by rfl⟩) R15331
theorem R20503 : Reach 20503 := rs (se 1 (by rfl) ⟨15377, by rfl⟩) R30755
theorem R20555 : Reach 20555 := rs (se 1 (by rfl) ⟨15416, by rfl⟩) R30833
theorem R20567 : Reach 20567 := rs (se 1 (by rfl) ⟨15425, by rfl⟩) R30851
theorem R20569 : Reach 20569 := rs (se 2 (by rfl) ⟨7713, by rfl⟩) R15427
theorem R53399 : Reach 53399 := rs (se 1 (by rfl) ⟨40049, by rfl⟩) R80099
theorem R20633 : Reach 20633 := rs (se 2 (by rfl) ⟨7737, by rfl⟩) R15475
theorem R250037 : Reach 250037 := rs (se 5 (by rfl) ⟨11720, by rfl⟩) R23441
theorem R20683 : Reach 20683 := rs (se 1 (by rfl) ⟨15512, by rfl⟩) R31025
theorem R20695 : Reach 20695 := rs (se 1 (by rfl) ⟨15521, by rfl⟩) R31043
theorem R20747 : Reach 20747 := rs (se 1 (by rfl) ⟨15560, by rfl⟩) R31121
theorem R20759 : Reach 20759 := rs (se 1 (by rfl) ⟨15569, by rfl⟩) R31139
theorem R20825 : Reach 20825 := rs (se 2 (by rfl) ⟨7809, by rfl⟩) R15619
theorem R20875 : Reach 20875 := rs (se 1 (by rfl) ⟨15656, by rfl⟩) R31313
theorem R119191 : Reach 119191 := rs (se 1 (by rfl) ⟨89393, by rfl⟩) R178787
theorem R20939 : Reach 20939 := rs (se 1 (by rfl) ⟨15704, by rfl⟩) R31409
theorem R20951 : Reach 20951 := rs (se 1 (by rfl) ⟨15713, by rfl⟩) R31427
theorem R53783 : Reach 53783 := rs (se 1 (by rfl) ⟨40337, by rfl⟩) R80675
theorem R21017 : Reach 21017 := rs (se 2 (by rfl) ⟨7881, by rfl⟩) R15763
theorem R21067 : Reach 21067 := rs (se 1 (by rfl) ⟨15800, by rfl⟩) R31601
theorem R53891 : Reach 53891 := rs (se 1 (by rfl) ⟨40418, by rfl⟩) R80837
theorem R21131 : Reach 21131 := rs (se 1 (by rfl) ⟨15848, by rfl⟩) R31697
theorem R21143 : Reach 21143 := rs (se 1 (by rfl) ⟨15857, by rfl⟩) R31715
theorem R21145 : Reach 21145 := rs (se 2 (by rfl) ⟨7929, by rfl⟩) R15859
theorem R119501 : Reach 119501 := rs (se 3 (by rfl) ⟨22406, by rfl⟩) R44813
theorem R21209 : Reach 21209 := rs (se 2 (by rfl) ⟨7953, by rfl⟩) R15907
theorem R21271 : Reach 21271 := rs (se 1 (by rfl) ⟨15953, by rfl⟩) R31907
theorem R54067 : Reach 54067 := rs (se 1 (by rfl) ⟨40550, by rfl⟩) R81101
theorem R21323 : Reach 21323 := rs (se 1 (by rfl) ⟨15992, by rfl⟩) R31985
theorem R21335 : Reach 21335 := rs (se 1 (by rfl) ⟨16001, by rfl⟩) R32003
theorem R54161 : Reach 54161 := rs (se 2 (by rfl) ⟨20310, by rfl⟩) R40621
theorem R21401 : Reach 21401 := rs (se 2 (by rfl) ⟨8025, by rfl⟩) R16051
theorem R54209 : Reach 54209 := rs (se 2 (by rfl) ⟨20328, by rfl⟩) R40657
theorem R21451 : Reach 21451 := rs (se 1 (by rfl) ⟨16088, by rfl⟩) R32177
theorem R21515 : Reach 21515 := rs (se 1 (by rfl) ⟨16136, by rfl⟩) R32273
theorem R21527 : Reach 21527 := rs (se 1 (by rfl) ⟨16145, by rfl⟩) R32291
theorem R54323 : Reach 54323 := rs (se 1 (by rfl) ⟨40742, by rfl⟩) R81485
theorem R87115 : Reach 87115 := rs (se 1 (by rfl) ⟨65336, by rfl⟩) R130673
theorem R21593 : Reach 21593 := rs (se 2 (by rfl) ⟨8097, by rfl⟩) R16195
theorem R21707 : Reach 21707 := rs (se 1 (by rfl) ⟨16280, by rfl⟩) R32561
theorem R21719 : Reach 21719 := rs (se 1 (by rfl) ⟨16289, by rfl⟩) R32579
theorem R21721 : Reach 21721 := rs (se 2 (by rfl) ⟨8145, by rfl⟩) R16291
theorem R21785 : Reach 21785 := rs (se 2 (by rfl) ⟨8169, by rfl⟩) R16339
theorem R54593 : Reach 54593 := rs (se 2 (by rfl) ⟨20472, by rfl⟩) R40945
theorem R21847 : Reach 21847 := rs (se 1 (by rfl) ⟨16385, by rfl⟩) R32771
theorem R87389 : Reach 87389 := rs (se 3 (by rfl) ⟨16385, by rfl⟩) R32771
theorem R21899 : Reach 21899 := rs (se 1 (by rfl) ⟨16424, by rfl⟩) R32849
theorem R21911 : Reach 21911 := rs (se 1 (by rfl) ⟨16433, by rfl⟩) R32867
theorem R54701 : Reach 54701 := rs (se 3 (by rfl) ⟨10256, by rfl⟩) R20513
theorem R21977 : Reach 21977 := rs (se 2 (by rfl) ⟨8241, by rfl⟩) R16483
theorem R22027 : Reach 22027 := rs (se 1 (by rfl) ⟨16520, by rfl⟩) R33041
theorem R22091 : Reach 22091 := rs (se 1 (by rfl) ⟨16568, by rfl⟩) R33137
theorem R218699 : Reach 218699 := rs (se 1 (by rfl) ⟨164024, by rfl⟩) R328049
theorem R22103 : Reach 22103 := rs (se 1 (by rfl) ⟨16577, by rfl⟩) R33155
theorem R22169 : Reach 22169 := rs (se 2 (by rfl) ⟨8313, by rfl⟩) R16627
theorem R22231 : Reach 22231 := rs (se 1 (by rfl) ⟨16673, by rfl⟩) R33347
theorem R22283 : Reach 22283 := rs (se 1 (by rfl) ⟨16712, by rfl⟩) R33425
theorem R22295 : Reach 22295 := rs (se 1 (by rfl) ⟨16721, by rfl⟩) R33443
theorem R22297 : Reach 22297 := rs (se 2 (by rfl) ⟨8361, by rfl⟩) R16723
theorem R22361 : Reach 22361 := rs (se 2 (by rfl) ⟨8385, by rfl⟩) R16771
theorem R55133 : Reach 55133 := rs (se 3 (by rfl) ⟨10337, by rfl⟩) R20675
theorem R22423 : Reach 22423 := rs (se 1 (by rfl) ⟨16817, by rfl⟩) R33635
theorem R87959 : Reach 87959 := rs (se 1 (by rfl) ⟨65969, by rfl⟩) R131939
theorem R22475 : Reach 22475 := rs (se 1 (by rfl) ⟨16856, by rfl⟩) R33713
theorem R22487 : Reach 22487 := rs (se 1 (by rfl) ⟨16865, by rfl⟩) R33731
theorem R55313 : Reach 55313 := rs (se 2 (by rfl) ⟨20742, by rfl⟩) R41485
theorem R22553 : Reach 22553 := rs (se 2 (by rfl) ⟨8457, by rfl⟩) R16915
theorem R22667 : Reach 22667 := rs (se 1 (by rfl) ⟨17000, by rfl⟩) R34001
theorem R22679 : Reach 22679 := rs (se 1 (by rfl) ⟨17009, by rfl⟩) R34019
theorem R55475 : Reach 55475 := rs (se 1 (by rfl) ⟨41606, by rfl⟩) R83213
theorem R317621 : Reach 317621 := rs (se 5 (by rfl) ⟨14888, by rfl⟩) R29777
theorem R22745 : Reach 22745 := rs (se 2 (by rfl) ⟨8529, by rfl⟩) R17059
theorem R22835 : Reach 22835 := rs (se 1 (by rfl) ⟨17126, by rfl⟩) R34253
theorem R22859 : Reach 22859 := rs (se 1 (by rfl) ⟨17144, by rfl⟩) R34289
theorem R22871 : Reach 22871 := rs (se 1 (by rfl) ⟨17153, by rfl⟩) R34307
theorem R22913 : Reach 22913 := rs (se 2 (by rfl) ⟨8592, by rfl⟩) R17185
theorem R88451 : Reach 88451 := rs (se 1 (by rfl) ⟨66338, by rfl⟩) R132677
theorem R22937 : Reach 22937 := rs (se 2 (by rfl) ⟨8601, by rfl⟩) R17203
theorem R22963 : Reach 22963 := rs (se 1 (by rfl) ⟨17222, by rfl⟩) R34445
theorem R22987 : Reach 22987 := rs (se 1 (by rfl) ⟨17240, by rfl⟩) R34481
theorem R22999 : Reach 22999 := rs (se 1 (by rfl) ⟨17249, by rfl⟩) R34499
theorem R23027 : Reach 23027 := rs (se 1 (by rfl) ⟨17270, by rfl⟩) R34541
theorem R23041 : Reach 23041 := rs (se 2 (by rfl) ⟨8640, by rfl⟩) R17281
theorem R23051 : Reach 23051 := rs (se 1 (by rfl) ⟨17288, by rfl⟩) R34577
theorem R23063 : Reach 23063 := rs (se 1 (by rfl) ⟨17297, by rfl⟩) R34595
theorem R23105 : Reach 23105 := rs (se 2 (by rfl) ⟨8664, by rfl⟩) R17329
theorem R88651 : Reach 88651 := rs (se 1 (by rfl) ⟨66488, by rfl⟩) R132977
theorem R55883 : Reach 55883 := rs (se 1 (by rfl) ⟨41912, by rfl⟩) R83825
theorem R23129 : Reach 23129 := rs (se 2 (by rfl) ⟨8673, by rfl⟩) R17347
theorem R121445 : Reach 121445 := rs (se 4 (by rfl) ⟨11385, by rfl⟩) R22771
theorem R23179 : Reach 23179 := rs (se 1 (by rfl) ⟨17384, by rfl⟩) R34769
theorem R23219 : Reach 23219 := rs (se 1 (by rfl) ⟨17414, by rfl⟩) R34829
theorem R23233 : Reach 23233 := rs (se 2 (by rfl) ⟨8712, by rfl⟩) R17425
theorem R56011 : Reach 56011 := rs (se 1 (by rfl) ⟨42008, by rfl⟩) R84017
theorem R23243 : Reach 23243 := rs (se 1 (by rfl) ⟨17432, by rfl⟩) R34865
theorem R23255 : Reach 23255 := rs (se 1 (by rfl) ⟨17441, by rfl⟩) R34883
theorem R23257 : Reach 23257 := rs (se 2 (by rfl) ⟨8721, by rfl⟩) R17443
theorem R23297 : Reach 23297 := rs (se 2 (by rfl) ⟨8736, by rfl⟩) R17473
theorem R23321 : Reach 23321 := rs (se 2 (by rfl) ⟨8745, by rfl⟩) R17491
theorem R23411 : Reach 23411 := rs (se 1 (by rfl) ⟨17558, by rfl⟩) R35117
theorem R23435 : Reach 23435 := rs (se 1 (by rfl) ⟨17576, by rfl⟩) R35153
theorem R23447 : Reach 23447 := rs (se 1 (by rfl) ⟨17585, by rfl⟩) R35171
theorem R23449 : Reach 23449 := rs (se 2 (by rfl) ⟨8793, by rfl⟩) R17587
theorem R154547 : Reach 154547 := rs (se 1 (by rfl) ⟨115910, by rfl⟩) R231821
theorem R23489 : Reach 23489 := rs (se 2 (by rfl) ⟨8808, by rfl⟩) R17617
theorem R56267 : Reach 56267 := rs (se 1 (by rfl) ⟨42200, by rfl⟩) R84401
theorem R23513 : Reach 23513 := rs (se 2 (by rfl) ⟨8817, by rfl⟩) R17635
theorem R56285 : Reach 56285 := rs (se 3 (by rfl) ⟨10553, by rfl⟩) R21107
theorem R23603 : Reach 23603 := rs (se 1 (by rfl) ⟨17702, by rfl⟩) R35405
theorem R23627 : Reach 23627 := rs (se 1 (by rfl) ⟨17720, by rfl⟩) R35441
theorem R23639 : Reach 23639 := rs (se 1 (by rfl) ⟨17729, by rfl⟩) R35459
theorem R89189 : Reach 89189 := rs (se 4 (by rfl) ⟨8361, by rfl⟩) R16723
theorem R23681 : Reach 23681 := rs (se 2 (by rfl) ⟨8880, by rfl⟩) R17761
theorem R23705 : Reach 23705 := rs (se 2 (by rfl) ⟨8889, by rfl⟩) R17779
theorem R56513 : Reach 56513 := rs (se 2 (by rfl) ⟨21192, by rfl⟩) R42385
theorem R56537 : Reach 56537 := rs (se 2 (by rfl) ⟨21201, by rfl⟩) R42403
theorem R23795 : Reach 23795 := rs (se 1 (by rfl) ⟨17846, by rfl⟩) R35693
theorem R23809 : Reach 23809 := rs (se 2 (by rfl) ⟨8928, by rfl⟩) R17857
theorem R23819 : Reach 23819 := rs (se 1 (by rfl) ⟨17864, by rfl⟩) R35729
theorem R23831 : Reach 23831 := rs (se 1 (by rfl) ⟨17873, by rfl⟩) R35747
theorem R23873 : Reach 23873 := rs (se 2 (by rfl) ⟨8952, by rfl⟩) R17905
theorem R23897 : Reach 23897 := rs (se 2 (by rfl) ⟨8961, by rfl⟩) R17923
theorem R23987 : Reach 23987 := rs (se 1 (by rfl) ⟨17990, by rfl⟩) R35981
theorem R24011 : Reach 24011 := rs (se 1 (by rfl) ⟨18008, by rfl⟩) R36017
theorem R24023 : Reach 24023 := rs (se 1 (by rfl) ⟨18017, by rfl⟩) R36035
theorem R24065 : Reach 24065 := rs (se 2 (by rfl) ⟨9024, by rfl⟩) R18049
theorem R24089 : Reach 24089 := rs (se 2 (by rfl) ⟨9033, by rfl⟩) R18067
theorem R24151 : Reach 24151 := rs (se 1 (by rfl) ⟨18113, by rfl⟩) R36227
theorem R24179 : Reach 24179 := rs (se 1 (by rfl) ⟨18134, by rfl⟩) R36269
theorem R24203 : Reach 24203 := rs (se 1 (by rfl) ⟨18152, by rfl⟩) R36305
theorem R56983 : Reach 56983 := rs (se 1 (by rfl) ⟨42737, by rfl⟩) R85475
theorem R24215 : Reach 24215 := rs (se 1 (by rfl) ⟨18161, by rfl⟩) R36323
theorem R24257 : Reach 24257 := rs (se 2 (by rfl) ⟨9096, by rfl⟩) R18193
theorem R24281 : Reach 24281 := rs (se 2 (by rfl) ⟨9105, by rfl⟩) R18211
theorem R89873 : Reach 89873 := rs (se 2 (by rfl) ⟨33702, by rfl⟩) R67405
theorem R24371 : Reach 24371 := rs (se 1 (by rfl) ⟨18278, by rfl⟩) R36557
theorem R24395 : Reach 24395 := rs (se 1 (by rfl) ⟨18296, by rfl⟩) R36593
theorem R24407 : Reach 24407 := rs (se 1 (by rfl) ⟨18305, by rfl⟩) R36611
theorem R24449 : Reach 24449 := rs (se 2 (by rfl) ⟨9168, by rfl⟩) R18337
theorem R57239 : Reach 57239 := rs (se 1 (by rfl) ⟨42929, by rfl⟩) R85859
theorem R24473 : Reach 24473 := rs (se 2 (by rfl) ⟨9177, by rfl⟩) R18355
theorem R24499 : Reach 24499 := rs (se 1 (by rfl) ⟨18374, by rfl⟩) R36749
theorem R24563 : Reach 24563 := rs (se 1 (by rfl) ⟨18422, by rfl⟩) R36845
theorem R57347 : Reach 57347 := rs (se 1 (by rfl) ⟨43010, by rfl⟩) R86021
theorem R24587 : Reach 24587 := rs (se 1 (by rfl) ⟨18440, by rfl⟩) R36881
theorem R24599 : Reach 24599 := rs (se 1 (by rfl) ⟨18449, by rfl⟩) R36899
theorem R24641 : Reach 24641 := rs (se 2 (by rfl) ⟨9240, by rfl⟩) R18481
theorem R24665 : Reach 24665 := rs (se 2 (by rfl) ⟨9249, by rfl⟩) R18499
theorem R24691 : Reach 24691 := rs (se 1 (by rfl) ⟨18518, by rfl⟩) R37037
theorem R24715 : Reach 24715 := rs (se 1 (by rfl) ⟨18536, by rfl⟩) R37073
theorem R24755 : Reach 24755 := rs (se 1 (by rfl) ⟨18566, by rfl⟩) R37133
theorem R24779 : Reach 24779 := rs (se 1 (by rfl) ⟨18584, by rfl⟩) R37169
theorem R24791 : Reach 24791 := rs (se 1 (by rfl) ⟨18593, by rfl⟩) R37187
theorem R24833 : Reach 24833 := rs (se 2 (by rfl) ⟨9312, by rfl⟩) R18625
theorem R57617 : Reach 57617 := rs (se 2 (by rfl) ⟨21606, by rfl⟩) R43213
theorem R24857 : Reach 24857 := rs (se 2 (by rfl) ⟨9321, by rfl⟩) R18643
theorem R24907 : Reach 24907 := rs (se 1 (by rfl) ⟨18680, by rfl⟩) R37361
theorem R156005 : Reach 156005 := rs (se 4 (by rfl) ⟨14625, by rfl⟩) R29251
theorem R24947 : Reach 24947 := rs (se 1 (by rfl) ⟨18710, by rfl⟩) R37421
theorem R24961 : Reach 24961 := rs (se 2 (by rfl) ⟨9360, by rfl⟩) R18721
theorem R24971 : Reach 24971 := rs (se 1 (by rfl) ⟨18728, by rfl⟩) R37457
theorem R24983 : Reach 24983 := rs (se 1 (by rfl) ⟨18737, by rfl⟩) R37475
theorem R57773 : Reach 57773 := rs (se 3 (by rfl) ⟨10832, by rfl⟩) R21665
theorem R57779 : Reach 57779 := rs (se 1 (by rfl) ⟨43334, by rfl⟩) R86669
theorem R25025 : Reach 25025 := rs (se 2 (by rfl) ⟨9384, by rfl⟩) R18769
theorem R25049 : Reach 25049 := rs (se 2 (by rfl) ⟨9393, by rfl⟩) R18787
theorem R25139 : Reach 25139 := rs (se 1 (by rfl) ⟨18854, by rfl⟩) R37709
theorem R25163 : Reach 25163 := rs (se 1 (by rfl) ⟨18872, by rfl⟩) R37745
theorem R25175 : Reach 25175 := rs (se 1 (by rfl) ⟨18881, by rfl⟩) R37763
theorem R25177 : Reach 25177 := rs (se 2 (by rfl) ⟨9441, by rfl⟩) R18883
theorem R25217 : Reach 25217 := rs (se 2 (by rfl) ⟨9456, by rfl⟩) R18913
theorem R25241 : Reach 25241 := rs (se 2 (by rfl) ⟨9465, by rfl⟩) R18931
theorem R25267 : Reach 25267 := rs (se 1 (by rfl) ⟨18950, by rfl⟩) R37901
theorem R58049 : Reach 58049 := rs (se 2 (by rfl) ⟨21768, by rfl⟩) R43537
theorem R25331 : Reach 25331 := rs (se 1 (by rfl) ⟨18998, by rfl⟩) R37997
theorem R25355 : Reach 25355 := rs (se 1 (by rfl) ⟨19016, by rfl⟩) R38033
theorem R25367 : Reach 25367 := rs (se 1 (by rfl) ⟨19025, by rfl⟩) R38051
theorem R58157 : Reach 58157 := rs (se 3 (by rfl) ⟨10904, by rfl⟩) R21809
theorem R25409 : Reach 25409 := rs (se 2 (by rfl) ⟨9528, by rfl⟩) R19057
theorem R25433 : Reach 25433 := rs (se 2 (by rfl) ⟨9537, by rfl⟩) R19075
theorem R25523 : Reach 25523 := rs (se 1 (by rfl) ⟨19142, by rfl⟩) R38285
theorem R25547 : Reach 25547 := rs (se 1 (by rfl) ⟨19160, by rfl⟩) R38321
theorem R58315 : Reach 58315 := rs (se 1 (by rfl) ⟨43736, by rfl⟩) R87473
theorem R25559 : Reach 25559 := rs (se 1 (by rfl) ⟨19169, by rfl⟩) R38339
theorem R25601 : Reach 25601 := rs (se 2 (by rfl) ⟨9600, by rfl⟩) R19201
theorem R25625 : Reach 25625 := rs (se 2 (by rfl) ⟨9609, by rfl⟩) R19219
theorem R25687 : Reach 25687 := rs (se 1 (by rfl) ⟨19265, by rfl⟩) R38531
theorem R25715 : Reach 25715 := rs (se 1 (by rfl) ⟨19286, by rfl⟩) R38573
theorem R25739 : Reach 25739 := rs (se 1 (by rfl) ⟨19304, by rfl⟩) R38609
theorem R25751 : Reach 25751 := rs (se 1 (by rfl) ⟨19313, by rfl⟩) R38627
theorem R25793 : Reach 25793 := rs (se 2 (by rfl) ⟨9672, by rfl⟩) R19345
theorem R25817 : Reach 25817 := rs (se 2 (by rfl) ⟨9681, by rfl⟩) R19363
theorem R58589 : Reach 58589 := rs (se 3 (by rfl) ⟨10985, by rfl⟩) R21971
theorem R25879 : Reach 25879 := rs (se 1 (by rfl) ⟨19409, by rfl⟩) R38819
theorem R25907 : Reach 25907 := rs (se 1 (by rfl) ⟨19430, by rfl⟩) R38861
theorem R25931 : Reach 25931 := rs (se 1 (by rfl) ⟨19448, by rfl⟩) R38897
theorem R25943 : Reach 25943 := rs (se 1 (by rfl) ⟨19457, by rfl⟩) R38915
theorem R25985 : Reach 25985 := rs (se 2 (by rfl) ⟨9744, by rfl⟩) R19489
theorem R58769 : Reach 58769 := rs (se 2 (by rfl) ⟨22038, by rfl⟩) R44077
theorem R26009 : Reach 26009 := rs (se 2 (by rfl) ⟨9753, by rfl⟩) R19507
theorem R26099 : Reach 26099 := rs (se 1 (by rfl) ⟨19574, by rfl⟩) R39149
theorem R26123 : Reach 26123 := rs (se 1 (by rfl) ⟨19592, by rfl⟩) R39185
theorem R26135 : Reach 26135 := rs (se 1 (by rfl) ⟨19601, by rfl⟩) R39203
theorem R26177 : Reach 26177 := rs (se 2 (by rfl) ⟨9816, by rfl⟩) R19633
theorem R26201 : Reach 26201 := rs (se 2 (by rfl) ⟨9825, by rfl⟩) R19651
theorem R91799 : Reach 91799 := rs (se 1 (by rfl) ⟨68849, by rfl⟩) R137699
theorem R26291 : Reach 26291 := rs (se 1 (by rfl) ⟨19718, by rfl⟩) R39437
theorem R26315 : Reach 26315 := rs (se 1 (by rfl) ⟨19736, by rfl⟩) R39473
theorem R91853 : Reach 91853 := rs (se 3 (by rfl) ⟨17222, by rfl⟩) R34445
theorem R26327 : Reach 26327 := rs (se 1 (by rfl) ⟨19745, by rfl⟩) R39491
theorem R26369 : Reach 26369 := rs (se 2 (by rfl) ⟨9888, by rfl⟩) R19777
theorem R26393 : Reach 26393 := rs (se 2 (by rfl) ⟨9897, by rfl⟩) R19795
theorem R26419 : Reach 26419 := rs (se 1 (by rfl) ⟨19814, by rfl⟩) R39629
theorem R59201 : Reach 59201 := rs (se 2 (by rfl) ⟨22200, by rfl⟩) R44401
theorem R26483 : Reach 26483 := rs (se 1 (by rfl) ⟨19862, by rfl⟩) R39725
theorem R26507 : Reach 26507 := rs (se 1 (by rfl) ⟨19880, by rfl⟩) R39761
theorem R26519 : Reach 26519 := rs (se 1 (by rfl) ⟨19889, by rfl⟩) R39779
theorem R26561 : Reach 26561 := rs (se 2 (by rfl) ⟨9960, by rfl⟩) R19921
theorem R26585 : Reach 26585 := rs (se 2 (by rfl) ⟨9969, by rfl⟩) R19939
theorem R26635 : Reach 26635 := rs (se 1 (by rfl) ⟨19976, by rfl⟩) R39953
theorem R92177 : Reach 92177 := rs (se 2 (by rfl) ⟨34566, by rfl⟩) R69133
theorem R26675 : Reach 26675 := rs (se 1 (by rfl) ⟨20006, by rfl⟩) R40013
theorem R26689 : Reach 26689 := rs (se 2 (by rfl) ⟨10008, by rfl⟩) R20017
theorem R26699 : Reach 26699 := rs (se 1 (by rfl) ⟨20024, by rfl⟩) R40049
theorem R26711 : Reach 26711 := rs (se 1 (by rfl) ⟨20033, by rfl⟩) R40067
theorem R26753 : Reach 26753 := rs (se 2 (by rfl) ⟨10032, by rfl⟩) R20065
theorem R26777 : Reach 26777 := rs (se 2 (by rfl) ⟨10041, by rfl⟩) R20083
theorem R92339 : Reach 92339 := rs (se 1 (by rfl) ⟨69254, by rfl⟩) R138509
theorem R26867 : Reach 26867 := rs (se 1 (by rfl) ⟨20150, by rfl⟩) R40301
theorem R26891 : Reach 26891 := rs (se 1 (by rfl) ⟨20168, by rfl⟩) R40337
theorem R26903 : Reach 26903 := rs (se 1 (by rfl) ⟨20177, by rfl⟩) R40355
theorem R26905 : Reach 26905 := rs (se 2 (by rfl) ⟨10089, by rfl⟩) R20179
theorem R26945 : Reach 26945 := rs (se 2 (by rfl) ⟨10104, by rfl⟩) R20209
theorem R59723 : Reach 59723 := rs (se 1 (by rfl) ⟨44792, by rfl⟩) R89585
theorem R26969 : Reach 26969 := rs (se 2 (by rfl) ⟨10113, by rfl⟩) R20227
theorem R27059 : Reach 27059 := rs (se 1 (by rfl) ⟨20294, by rfl⟩) R40589
theorem R27083 : Reach 27083 := rs (se 1 (by rfl) ⟨20312, by rfl⟩) R40625
theorem R27095 : Reach 27095 := rs (se 1 (by rfl) ⟨20321, by rfl⟩) R40643
theorem R59869 : Reach 59869 := rs (se 3 (by rfl) ⟨11225, by rfl⟩) R22451
theorem R27137 : Reach 27137 := rs (se 2 (by rfl) ⟨10176, by rfl⟩) R20353
theorem R27161 : Reach 27161 := rs (se 2 (by rfl) ⟨10185, by rfl⟩) R20371
theorem R59993 : Reach 59993 := rs (se 2 (by rfl) ⟨22497, by rfl⟩) R44995
theorem R92765 : Reach 92765 := rs (se 3 (by rfl) ⟨17393, by rfl⟩) R34787
theorem R27251 : Reach 27251 := rs (se 1 (by rfl) ⟨20438, by rfl⟩) R40877
theorem R27275 : Reach 27275 := rs (se 1 (by rfl) ⟨20456, by rfl⟩) R40913
theorem R27287 : Reach 27287 := rs (se 1 (by rfl) ⟨20465, by rfl⟩) R40931
theorem R27329 : Reach 27329 := rs (se 2 (by rfl) ⟨10248, by rfl⟩) R20497
theorem R27353 : Reach 27353 := rs (se 2 (by rfl) ⟨10257, by rfl⟩) R20515
theorem R92933 : Reach 92933 := rs (se 4 (by rfl) ⟨8712, by rfl⟩) R17425
theorem R27443 : Reach 27443 := rs (se 1 (by rfl) ⟨20582, by rfl⟩) R41165
theorem R27467 : Reach 27467 := rs (se 1 (by rfl) ⟨20600, by rfl⟩) R41201
theorem R27479 : Reach 27479 := rs (se 1 (by rfl) ⟨20609, by rfl⟩) R41219
theorem R27521 : Reach 27521 := rs (se 2 (by rfl) ⟨10320, by rfl⟩) R20641
theorem R27545 : Reach 27545 := rs (se 2 (by rfl) ⟨10329, by rfl⟩) R20659
theorem R125873 : Reach 125873 := rs (se 2 (by rfl) ⟨47202, by rfl⟩) R94405
theorem R322483 : Reach 322483 := rs (se 1 (by rfl) ⟨241862, by rfl⟩) R483725
theorem R27607 : Reach 27607 := rs (se 1 (by rfl) ⟨20705, by rfl⟩) R41411
theorem R27635 : Reach 27635 := rs (se 1 (by rfl) ⟨20726, by rfl⟩) R41453
theorem R27659 : Reach 27659 := rs (se 1 (by rfl) ⟨20744, by rfl⟩) R41489
theorem R27671 : Reach 27671 := rs (se 1 (by rfl) ⟨20753, by rfl⟩) R41507
theorem R27713 : Reach 27713 := rs (se 2 (by rfl) ⟨10392, by rfl⟩) R20785
theorem R27737 : Reach 27737 := rs (se 2 (by rfl) ⟨10401, by rfl⟩) R20803
theorem R27827 : Reach 27827 := rs (se 1 (by rfl) ⟨20870, by rfl⟩) R41741
theorem R27851 : Reach 27851 := rs (se 1 (by rfl) ⟨20888, by rfl⟩) R41777
theorem R27863 : Reach 27863 := rs (se 1 (by rfl) ⟨20897, by rfl⟩) R41795
theorem R27905 : Reach 27905 := rs (se 2 (by rfl) ⟨10464, by rfl⟩) R20929
theorem R60689 : Reach 60689 := rs (se 2 (by rfl) ⟨22758, by rfl⟩) R45517
theorem R60695 : Reach 60695 := rs (se 1 (by rfl) ⟨45521, by rfl⟩) R91043
theorem R27929 : Reach 27929 := rs (se 2 (by rfl) ⟨10473, by rfl⟩) R20947
theorem R28019 : Reach 28019 := rs (se 1 (by rfl) ⟨21014, by rfl⟩) R42029
theorem R60803 : Reach 60803 := rs (se 1 (by rfl) ⟨45602, by rfl⟩) R91205
theorem R28043 : Reach 28043 := rs (se 1 (by rfl) ⟨21032, by rfl⟩) R42065
theorem R28055 : Reach 28055 := rs (se 1 (by rfl) ⟨21041, by rfl⟩) R42083
theorem R28097 : Reach 28097 := rs (se 2 (by rfl) ⟨10536, by rfl⟩) R21073
theorem R28121 : Reach 28121 := rs (se 2 (by rfl) ⟨10545, by rfl⟩) R21091
theorem R28147 : Reach 28147 := rs (se 1 (by rfl) ⟨21110, by rfl⟩) R42221
theorem R126481 : Reach 126481 := rs (se 2 (by rfl) ⟨47430, by rfl⟩) R94861
theorem R28211 : Reach 28211 := rs (se 1 (by rfl) ⟨21158, by rfl⟩) R42317
theorem R28235 : Reach 28235 := rs (se 1 (by rfl) ⟨21176, by rfl⟩) R42353
theorem R28247 : Reach 28247 := rs (se 1 (by rfl) ⟨21185, by rfl⟩) R42371
theorem R93797 : Reach 93797 := rs (se 4 (by rfl) ⟨8793, by rfl⟩) R17587
theorem R28289 : Reach 28289 := rs (se 2 (by rfl) ⟨10608, by rfl⟩) R21217
theorem R28313 : Reach 28313 := rs (se 2 (by rfl) ⟨10617, by rfl⟩) R21235
theorem R28363 : Reach 28363 := rs (se 1 (by rfl) ⟨21272, by rfl⟩) R42545
theorem R61145 : Reach 61145 := rs (se 2 (by rfl) ⟨22929, by rfl⟩) R45859
theorem R28403 : Reach 28403 := rs (se 1 (by rfl) ⟨21302, by rfl⟩) R42605
theorem R28417 : Reach 28417 := rs (se 2 (by rfl) ⟨10656, by rfl⟩) R21313
theorem R28427 : Reach 28427 := rs (se 1 (by rfl) ⟨21320, by rfl⟩) R42641
theorem R28439 : Reach 28439 := rs (se 1 (by rfl) ⟨21329, by rfl⟩) R42659
theorem R61229 : Reach 61229 := rs (se 3 (by rfl) ⟨11480, by rfl⟩) R22961
theorem R28481 : Reach 28481 := rs (se 2 (by rfl) ⟨10680, by rfl⟩) R21361
theorem R28505 : Reach 28505 := rs (se 2 (by rfl) ⟨10689, by rfl⟩) R21379
theorem R225125 : Reach 225125 := rs (se 4 (by rfl) ⟨21105, by rfl⟩) R42211
theorem R28595 : Reach 28595 := rs (se 1 (by rfl) ⟨21446, by rfl⟩) R42893
theorem R28619 : Reach 28619 := rs (se 1 (by rfl) ⟨21464, by rfl⟩) R42929
theorem R28631 : Reach 28631 := rs (se 1 (by rfl) ⟨21473, by rfl⟩) R42947
theorem R28633 : Reach 28633 := rs (se 2 (by rfl) ⟨10737, by rfl⟩) R21475
theorem R28673 : Reach 28673 := rs (se 2 (by rfl) ⟨10752, by rfl⟩) R21505
theorem R28697 : Reach 28697 := rs (se 2 (by rfl) ⟨10761, by rfl⟩) R21523
theorem R61505 : Reach 61505 := rs (se 2 (by rfl) ⟨23064, by rfl⟩) R46129
theorem R94283 : Reach 94283 := rs (se 1 (by rfl) ⟨70712, by rfl⟩) R141425
theorem R28787 : Reach 28787 := rs (se 1 (by rfl) ⟨21590, by rfl⟩) R43181
theorem R28811 : Reach 28811 := rs (se 1 (by rfl) ⟨21608, by rfl⟩) R43217
theorem R28823 : Reach 28823 := rs (se 1 (by rfl) ⟨21617, by rfl⟩) R43235
theorem R28865 : Reach 28865 := rs (se 2 (by rfl) ⟨10824, by rfl⟩) R21649
theorem R28889 : Reach 28889 := rs (se 2 (by rfl) ⟨10833, by rfl⟩) R21667
theorem R28979 : Reach 28979 := rs (se 1 (by rfl) ⟨21734, by rfl⟩) R43469
theorem R28993 : Reach 28993 := rs (se 2 (by rfl) ⟨10872, by rfl⟩) R21745
theorem R29003 : Reach 29003 := rs (se 1 (by rfl) ⟨21752, by rfl⟩) R43505
theorem R29015 : Reach 29015 := rs (se 1 (by rfl) ⟨21761, by rfl⟩) R43523
theorem R94565 : Reach 94565 := rs (se 4 (by rfl) ⟨8865, by rfl⟩) R17731
theorem R29057 : Reach 29057 := rs (se 2 (by rfl) ⟨10896, by rfl⟩) R21793
theorem R29081 : Reach 29081 := rs (se 2 (by rfl) ⟨10905, by rfl⟩) R21811
theorem R29171 : Reach 29171 := rs (se 1 (by rfl) ⟨21878, by rfl⟩) R43757
theorem R29195 : Reach 29195 := rs (se 1 (by rfl) ⟨21896, by rfl⟩) R43793
theorem R29207 : Reach 29207 := rs (se 1 (by rfl) ⟨21905, by rfl⟩) R43811
theorem R29249 : Reach 29249 := rs (se 2 (by rfl) ⟨10968, by rfl⟩) R21937
theorem R29273 : Reach 29273 := rs (se 2 (by rfl) ⟨10977, by rfl⟩) R21955
theorem R62045 : Reach 62045 := rs (se 3 (by rfl) ⟨11633, by rfl⟩) R23267
theorem R29335 : Reach 29335 := rs (se 1 (by rfl) ⟨22001, by rfl⟩) R44003
theorem R29363 : Reach 29363 := rs (se 1 (by rfl) ⟨22022, by rfl⟩) R44045
theorem R29387 : Reach 29387 := rs (se 1 (by rfl) ⟨22040, by rfl⟩) R44081
theorem R29399 : Reach 29399 := rs (se 1 (by rfl) ⟨22049, by rfl⟩) R44099
theorem R29441 : Reach 29441 := rs (se 2 (by rfl) ⟨11040, by rfl⟩) R22081
theorem R29465 : Reach 29465 := rs (se 2 (by rfl) ⟨11049, by rfl⟩) R22099
theorem R29555 : Reach 29555 := rs (se 1 (by rfl) ⟨22166, by rfl⟩) R44333
theorem R29579 : Reach 29579 := rs (se 1 (by rfl) ⟨22184, by rfl⟩) R44369
theorem R29591 : Reach 29591 := rs (se 1 (by rfl) ⟨22193, by rfl⟩) R44387
theorem R29593 : Reach 29593 := rs (se 2 (by rfl) ⟨11097, by rfl⟩) R22195
theorem R127921 : Reach 127921 := rs (se 2 (by rfl) ⟨47970, by rfl⟩) R95941
theorem R29633 : Reach 29633 := rs (se 2 (by rfl) ⟨11112, by rfl⟩) R22225
theorem R29657 : Reach 29657 := rs (se 2 (by rfl) ⟨11121, by rfl⟩) R22243
theorem R193549 : Reach 193549 := rs (se 3 (by rfl) ⟨36290, by rfl⟩) R72581
theorem R29747 : Reach 29747 := rs (se 1 (by rfl) ⟨22310, by rfl⟩) R44621
theorem R422981 : Reach 422981 := rs (se 4 (by rfl) ⟨39654, by rfl⟩) R79309
theorem R29771 : Reach 29771 := rs (se 1 (by rfl) ⟨22328, by rfl⟩) R44657
theorem R29783 : Reach 29783 := rs (se 1 (by rfl) ⟨22337, by rfl⟩) R44675
theorem R29825 : Reach 29825 := rs (se 2 (by rfl) ⟨11184, by rfl⟩) R22369
theorem R95363 : Reach 95363 := rs (se 1 (by rfl) ⟨71522, by rfl⟩) R143045
theorem R29849 : Reach 29849 := rs (se 2 (by rfl) ⟨11193, by rfl⟩) R22387
theorem R29875 : Reach 29875 := rs (se 1 (by rfl) ⟨22406, by rfl⟩) R44813
theorem R29939 : Reach 29939 := rs (se 1 (by rfl) ⟨22454, by rfl⟩) R44909
theorem R29963 : Reach 29963 := rs (se 1 (by rfl) ⟨22472, by rfl⟩) R44945
theorem R29975 : Reach 29975 := rs (se 1 (by rfl) ⟨22481, by rfl⟩) R44963
theorem R30017 : Reach 30017 := rs (se 2 (by rfl) ⟨11256, by rfl⟩) R22513
theorem R30041 : Reach 30041 := rs (se 2 (by rfl) ⟨11265, by rfl⟩) R22531
theorem R30091 : Reach 30091 := rs (se 1 (by rfl) ⟨22568, by rfl⟩) R45137
theorem R30131 : Reach 30131 := rs (se 1 (by rfl) ⟨22598, by rfl⟩) R45197
theorem R30145 : Reach 30145 := rs (se 2 (by rfl) ⟨11304, by rfl⟩) R22609
theorem R30167 : Reach 30167 := rs (se 1 (by rfl) ⟨22625, by rfl⟩) R45251
theorem R325133 : Reach 325133 := rs (se 3 (by rfl) ⟨60962, by rfl⟩) R121925
theorem R30233 : Reach 30233 := rs (se 2 (by rfl) ⟨11337, by rfl⟩) R22675
theorem R1799765 : Reach 1799765 := rs (se 8 (by rfl) ⟨10545, by rfl⟩) R21091
theorem R30337 : Reach 30337 := rs (se 2 (by rfl) ⟨11376, by rfl⟩) R22753
theorem R30347 : Reach 30347 := rs (se 1 (by rfl) ⟨22760, by rfl⟩) R45521
theorem R30361 : Reach 30361 := rs (se 2 (by rfl) ⟨11385, by rfl⟩) R22771
theorem R30401 : Reach 30401 := rs (se 2 (by rfl) ⟨11400, by rfl⟩) R22801
theorem R96065 : Reach 96065 := rs (se 2 (by rfl) ⟨36024, by rfl⟩) R72049
theorem R292709 : Reach 292709 := rs (se 4 (by rfl) ⟨27441, by rfl⟩) R54883
theorem R63449 : Reach 63449 := rs (se 2 (by rfl) ⟨23793, by rfl⟩) R47587
theorem R30743 : Reach 30743 := rs (se 1 (by rfl) ⟨23057, by rfl⟩) R46115
theorem R30871 : Reach 30871 := rs (se 1 (by rfl) ⟨23153, by rfl⟩) R46307
theorem R96433 : Reach 96433 := rs (se 2 (by rfl) ⟨36162, by rfl⟩) R72325
theorem R30923 : Reach 30923 := rs (se 1 (by rfl) ⟨23192, by rfl⟩) R46385
theorem R30937 : Reach 30937 := rs (se 2 (by rfl) ⟨11601, by rfl⟩) R23203
theorem R31051 : Reach 31051 := rs (se 1 (by rfl) ⟨23288, by rfl⟩) R46577
theorem R31193 : Reach 31193 := rs (se 2 (by rfl) ⟨11697, by rfl⟩) R23395
theorem R31283 : Reach 31283 := rs (se 1 (by rfl) ⟨23462, by rfl⟩) R46925
theorem R64151 : Reach 64151 := rs (se 1 (by rfl) ⟨48113, by rfl⟩) R96227
theorem R64273 : Reach 64273 := rs (se 2 (by rfl) ⟨24102, by rfl⟩) R48205
theorem R31553 : Reach 31553 := rs (se 2 (by rfl) ⟨11832, by rfl⟩) R23665
theorem R31681 : Reach 31681 := rs (se 2 (by rfl) ⟨11880, by rfl⟩) R23761
theorem R31691 : Reach 31691 := rs (se 1 (by rfl) ⟨23768, by rfl⟩) R47537
theorem R64529 : Reach 64529 := rs (se 2 (by rfl) ⟨24198, by rfl⟩) R48397
theorem R64577 : Reach 64577 := rs (se 2 (by rfl) ⟨24216, by rfl⟩) R48433
theorem R31819 : Reach 31819 := rs (se 1 (by rfl) ⟨23864, by rfl⟩) R47729
theorem R31895 : Reach 31895 := rs (se 1 (by rfl) ⟨23921, by rfl⟩) R47843
theorem R64691 : Reach 64691 := rs (se 1 (by rfl) ⟨48518, by rfl⟩) R97037
theorem R31961 : Reach 31961 := rs (se 2 (by rfl) ⟨11985, by rfl⟩) R23971
theorem R32075 : Reach 32075 := rs (se 1 (by rfl) ⟨24056, by rfl⟩) R48113
theorem R32089 : Reach 32089 := rs (se 2 (by rfl) ⟨12033, by rfl⟩) R24067
theorem R65069 : Reach 65069 := rs (se 3 (by rfl) ⟨12200, by rfl⟩) R24401
theorem R32345 : Reach 32345 := rs (se 2 (by rfl) ⟨12129, by rfl⟩) R24259
theorem R65117 : Reach 65117 := rs (se 3 (by rfl) ⟨12209, by rfl⟩) R24419
theorem R32435 : Reach 32435 := rs (se 1 (by rfl) ⟨24326, by rfl⟩) R48653
theorem R98009 : Reach 98009 := rs (se 2 (by rfl) ⟨36753, by rfl⟩) R73507
theorem R32663 : Reach 32663 := rs (se 1 (by rfl) ⟨24497, by rfl⟩) R48995
theorem R294835 : Reach 294835 := rs (se 1 (by rfl) ⟨221126, by rfl⟩) R442253
theorem R32705 : Reach 32705 := rs (se 2 (by rfl) ⟨12264, by rfl⟩) R24529
theorem R32903 : Reach 32903 := rs (se 1 (by rfl) ⟨24677, by rfl⟩) R49355
theorem R32921 : Reach 32921 := rs (se 2 (by rfl) ⟨12345, by rfl⟩) R24691
theorem R32953 : Reach 32953 := rs (se 2 (by rfl) ⟨12357, by rfl⟩) R24715
theorem R65825 : Reach 65825 := rs (se 2 (by rfl) ⟨24684, by rfl⟩) R49369
theorem R65843 : Reach 65843 := rs (se 1 (by rfl) ⟨49382, by rfl⟩) R98765
theorem R33083 : Reach 33083 := rs (se 1 (by rfl) ⟨24812, by rfl⟩) R49625
theorem R131387 : Reach 131387 := rs (se 1 (by rfl) ⟨98540, by rfl⟩) R197081
theorem R33139 : Reach 33139 := rs (se 1 (by rfl) ⟨24854, by rfl⟩) R49709
theorem R33209 : Reach 33209 := rs (se 2 (by rfl) ⟨12453, by rfl⟩) R24907
theorem R33281 : Reach 33281 := rs (se 2 (by rfl) ⟨12480, by rfl⟩) R24961
theorem R98819 : Reach 98819 := rs (se 1 (by rfl) ⟨74114, by rfl⟩) R148229
theorem R33367 : Reach 33367 := rs (se 1 (by rfl) ⟨25025, by rfl⟩) R50051
theorem R131813 : Reach 131813 := rs (se 4 (by rfl) ⟨12357, by rfl⟩) R24715
theorem R33547 : Reach 33547 := rs (se 1 (by rfl) ⟨25160, by rfl⟩) R50321
theorem R33551 : Reach 33551 := rs (se 1 (by rfl) ⟨25163, by rfl⟩) R50327
theorem R33569 : Reach 33569 := rs (se 2 (by rfl) ⟨12588, by rfl⟩) R25177
theorem R33623 : Reach 33623 := rs (se 1 (by rfl) ⟨25217, by rfl⟩) R50435
theorem R66419 : Reach 66419 := rs (se 1 (by rfl) ⟨49814, by rfl⟩) R99629
theorem R33655 : Reach 33655 := rs (se 1 (by rfl) ⟨25241, by rfl⟩) R50483
theorem R33671 : Reach 33671 := rs (se 1 (by rfl) ⟨25253, by rfl⟩) R50507
theorem R33689 : Reach 33689 := rs (se 2 (by rfl) ⟨12633, by rfl⟩) R25267
theorem R99235 : Reach 99235 := rs (se 1 (by rfl) ⟨74426, by rfl⟩) R148853
theorem R33803 : Reach 33803 := rs (se 1 (by rfl) ⟨25352, by rfl⟩) R50705
theorem R33911 : Reach 33911 := rs (se 1 (by rfl) ⟨25433, by rfl⟩) R50867
theorem R66797 : Reach 66797 := rs (se 3 (by rfl) ⟨12524, by rfl⟩) R25049
theorem R34091 : Reach 34091 := rs (se 1 (by rfl) ⟨25568, by rfl⟩) R51137
theorem R66905 : Reach 66905 := rs (se 2 (by rfl) ⟨25089, by rfl⟩) R50179
theorem R34163 : Reach 34163 := rs (se 1 (by rfl) ⟨25622, by rfl⟩) R51245
theorem R34195 : Reach 34195 := rs (se 1 (by rfl) ⟨25646, by rfl⟩) R51293
theorem R34451 : Reach 34451 := rs (se 1 (by rfl) ⟨25838, by rfl⟩) R51677
theorem R34505 : Reach 34505 := rs (se 2 (by rfl) ⟨12939, by rfl⟩) R25879
theorem R34571 : Reach 34571 := rs (se 1 (by rfl) ⟨25928, by rfl⟩) R51857
theorem R67387 : Reach 67387 := rs (se 1 (by rfl) ⟨50540, by rfl⟩) R101081
theorem R67463 : Reach 67463 := rs (se 1 (by rfl) ⟨50597, by rfl⟩) R101195
theorem R133015 : Reach 133015 := rs (se 1 (by rfl) ⟨99761, by rfl⟩) R199523
theorem R100439 : Reach 100439 := rs (se 1 (by rfl) ⟨75329, by rfl⟩) R150659
theorem R34931 : Reach 34931 := rs (se 1 (by rfl) ⟨26198, by rfl⟩) R52397
theorem R34951 : Reach 34951 := rs (se 1 (by rfl) ⟨26213, by rfl⟩) R52427
theorem R35083 : Reach 35083 := rs (se 1 (by rfl) ⟨26312, by rfl⟩) R52625
theorem R35207 : Reach 35207 := rs (se 1 (by rfl) ⟨26405, by rfl⟩) R52811
theorem R35225 : Reach 35225 := rs (se 2 (by rfl) ⟨13209, by rfl⟩) R26419
theorem R35387 : Reach 35387 := rs (se 1 (by rfl) ⟨26540, by rfl⟩) R53081
theorem R35513 : Reach 35513 := rs (se 2 (by rfl) ⟨13317, by rfl⟩) R26635
theorem R35585 : Reach 35585 := rs (se 2 (by rfl) ⟨13344, by rfl⟩) R26689
theorem R35599 : Reach 35599 := rs (se 1 (by rfl) ⟨26699, by rfl⟩) R53399
theorem R166691 : Reach 166691 := rs (se 1 (by rfl) ⟨125018, by rfl⟩) R250037
theorem R199685 : Reach 199685 := rs (se 4 (by rfl) ⟨18720, by rfl⟩) R37441
theorem R35855 : Reach 35855 := rs (se 1 (by rfl) ⟨26891, by rfl⟩) R53783
theorem R35873 : Reach 35873 := rs (se 2 (by rfl) ⟨13452, by rfl⟩) R26905
theorem R35927 : Reach 35927 := rs (se 1 (by rfl) ⟨26945, by rfl⟩) R53891
theorem R36107 : Reach 36107 := rs (se 1 (by rfl) ⟨27080, by rfl⟩) R54161
theorem R36125 : Reach 36125 := rs (se 3 (by rfl) ⟨6773, by rfl⟩) R13547
theorem R36139 : Reach 36139 := rs (se 1 (by rfl) ⟨27104, by rfl⟩) R54209
theorem R36215 : Reach 36215 := rs (se 1 (by rfl) ⟨27161, by rfl⟩) R54323
theorem R69011 : Reach 69011 := rs (se 1 (by rfl) ⟨51758, by rfl⟩) R103517
theorem R134621 : Reach 134621 := rs (se 3 (by rfl) ⟨25241, by rfl⟩) R50483
theorem R36395 : Reach 36395 := rs (se 1 (by rfl) ⟨27296, by rfl⟩) R54593
theorem R36413 : Reach 36413 := rs (se 3 (by rfl) ⟨6827, by rfl⟩) R13655
theorem R69187 : Reach 69187 := rs (se 1 (by rfl) ⟨51890, by rfl⟩) R103781
theorem R36467 : Reach 36467 := rs (se 1 (by rfl) ⟨27350, by rfl⟩) R54701
theorem R134873 : Reach 134873 := rs (se 2 (by rfl) ⟨50577, by rfl⟩) R101155
theorem R36755 : Reach 36755 := rs (se 1 (by rfl) ⟨27566, by rfl⟩) R55133
theorem R429977 : Reach 429977 := rs (se 2 (by rfl) ⟨161241, by rfl⟩) R322483
theorem R36809 : Reach 36809 := rs (se 2 (by rfl) ⟨13803, by rfl⟩) R27607
theorem R36875 : Reach 36875 := rs (se 1 (by rfl) ⟨27656, by rfl⟩) R55313
theorem R135229 : Reach 135229 := rs (se 3 (by rfl) ⟨25355, by rfl⟩) R50711
theorem R36983 : Reach 36983 := rs (se 1 (by rfl) ⟨27737, by rfl⟩) R55475
theorem R37255 : Reach 37255 := rs (se 1 (by rfl) ⟨27941, by rfl⟩) R55883
theorem R70091 : Reach 70091 := rs (se 1 (by rfl) ⟨52568, by rfl⟩) R105137
theorem R103031 : Reach 103031 := rs (se 1 (by rfl) ⟨77273, by rfl⟩) R154547
theorem R37511 : Reach 37511 := rs (se 1 (by rfl) ⟨28133, by rfl⟩) R56267
theorem R37523 : Reach 37523 := rs (se 1 (by rfl) ⟨28142, by rfl⟩) R56285
theorem R37529 : Reach 37529 := rs (se 2 (by rfl) ⟨14073, by rfl⟩) R28147
theorem R168641 : Reach 168641 := rs (se 2 (by rfl) ⟨63240, by rfl⟩) R126481
theorem R37675 : Reach 37675 := rs (se 1 (by rfl) ⟨28256, by rfl⟩) R56513
theorem R37691 : Reach 37691 := rs (se 1 (by rfl) ⟨28268, by rfl⟩) R56537
theorem R37817 : Reach 37817 := rs (se 2 (by rfl) ⟨14181, by rfl⟩) R28363
theorem R37889 : Reach 37889 := rs (se 2 (by rfl) ⟨14208, by rfl⟩) R28417
theorem R38159 : Reach 38159 := rs (se 1 (by rfl) ⟨28619, by rfl⟩) R57239
theorem R38177 : Reach 38177 := rs (se 2 (by rfl) ⟨14316, by rfl⟩) R28633
theorem R38231 : Reach 38231 := rs (se 1 (by rfl) ⟨28673, by rfl⟩) R57347
theorem R38411 : Reach 38411 := rs (se 1 (by rfl) ⟨28808, by rfl⟩) R57617
theorem R38429 : Reach 38429 := rs (se 3 (by rfl) ⟨7205, by rfl⟩) R14411
theorem R104003 : Reach 104003 := rs (se 1 (by rfl) ⟨78002, by rfl⟩) R156005
theorem R38515 : Reach 38515 := rs (se 1 (by rfl) ⟨28886, by rfl⟩) R57773
theorem R38519 : Reach 38519 := rs (se 1 (by rfl) ⟨28889, by rfl⟩) R57779
theorem R104165 : Reach 104165 := rs (se 4 (by rfl) ⟨9765, by rfl⟩) R19531
theorem R38657 : Reach 38657 := rs (se 2 (by rfl) ⟨14496, by rfl⟩) R28993
theorem R136961 : Reach 136961 := rs (se 2 (by rfl) ⟨51360, by rfl⟩) R102721
theorem R136997 : Reach 136997 := rs (se 4 (by rfl) ⟨12843, by rfl⟩) R25687
theorem R38699 : Reach 38699 := rs (se 1 (by rfl) ⟨29024, by rfl⟩) R58049
theorem R38717 : Reach 38717 := rs (se 3 (by rfl) ⟨7259, by rfl⟩) R14519
theorem R202571 : Reach 202571 := rs (se 1 (by rfl) ⟨151928, by rfl⟩) R303857
theorem R38771 : Reach 38771 := rs (se 1 (by rfl) ⟨29078, by rfl⟩) R58157
theorem R39059 : Reach 39059 := rs (se 1 (by rfl) ⟨29294, by rfl⟩) R58589
theorem R39113 : Reach 39113 := rs (se 2 (by rfl) ⟨14667, by rfl⟩) R29335
theorem R39179 : Reach 39179 := rs (se 1 (by rfl) ⟨29384, by rfl⟩) R58769
theorem R72083 : Reach 72083 := rs (se 1 (by rfl) ⟨54062, by rfl⟩) R108125
theorem R72089 : Reach 72089 := rs (se 2 (by rfl) ⟨27033, by rfl⟩) R54067
theorem R39457 : Reach 39457 := rs (se 2 (by rfl) ⟨14796, by rfl⟩) R29593
theorem R39467 : Reach 39467 := rs (se 1 (by rfl) ⟨29600, by rfl⟩) R59201
theorem R170561 : Reach 170561 := rs (se 2 (by rfl) ⟨63960, by rfl⟩) R127921
theorem R39815 : Reach 39815 := rs (se 1 (by rfl) ⟨29861, by rfl⟩) R59723
theorem R39833 : Reach 39833 := rs (se 2 (by rfl) ⟨14937, by rfl⟩) R29875
theorem R39995 : Reach 39995 := rs (se 1 (by rfl) ⟨29996, by rfl⟩) R59993
theorem R40121 : Reach 40121 := rs (se 2 (by rfl) ⟨15045, by rfl⟩) R30091
theorem R40193 : Reach 40193 := rs (se 2 (by rfl) ⟨15072, by rfl⟩) R30145
theorem R73163 : Reach 73163 := rs (se 1 (by rfl) ⟨54872, by rfl⟩) R109745
theorem R40459 : Reach 40459 := rs (se 1 (by rfl) ⟨30344, by rfl⟩) R60689
theorem R40463 : Reach 40463 := rs (se 1 (by rfl) ⟨30347, by rfl⟩) R60695
theorem R40481 : Reach 40481 := rs (se 2 (by rfl) ⟨15180, by rfl⟩) R30361
theorem R73277 : Reach 73277 := rs (se 3 (by rfl) ⟨13739, by rfl⟩) R27479
theorem R40535 : Reach 40535 := rs (se 1 (by rfl) ⟨30401, by rfl⟩) R60803
theorem R40763 : Reach 40763 := rs (se 1 (by rfl) ⟨30572, by rfl⟩) R61145
theorem R40819 : Reach 40819 := rs (se 1 (by rfl) ⟨30614, by rfl⟩) R61229
theorem R41003 : Reach 41003 := rs (se 1 (by rfl) ⟨30752, by rfl⟩) R61505
theorem R41021 : Reach 41021 := rs (se 3 (by rfl) ⟨7691, by rfl⟩) R15383
theorem R41161 : Reach 41161 := rs (se 2 (by rfl) ⟨15435, by rfl⟩) R30871
theorem R41249 : Reach 41249 := rs (se 2 (by rfl) ⟨15468, by rfl⟩) R30937
theorem R74119 : Reach 74119 := rs (se 1 (by rfl) ⟨55589, by rfl⟩) R111179
theorem R41363 : Reach 41363 := rs (se 1 (by rfl) ⟨31022, by rfl⟩) R62045
theorem R41401 : Reach 41401 := rs (se 2 (by rfl) ⟨15525, by rfl⟩) R31051
theorem R107237 : Reach 107237 := rs (se 4 (by rfl) ⟨10053, by rfl⟩) R20107
theorem R74681 : Reach 74681 := rs (se 2 (by rfl) ⟨28005, by rfl⟩) R56011
theorem R42241 : Reach 42241 := rs (se 2 (by rfl) ⟨15840, by rfl⟩) R31681
theorem R42299 : Reach 42299 := rs (se 1 (by rfl) ⟨31724, by rfl⟩) R63449
theorem R42425 : Reach 42425 := rs (se 2 (by rfl) ⟨15909, by rfl⟩) R31819
theorem R75275 : Reach 75275 := rs (se 1 (by rfl) ⟨56456, by rfl⟩) R112913
theorem R173645 : Reach 173645 := rs (se 3 (by rfl) ⟨32558, by rfl⟩) R65117
theorem R75437 : Reach 75437 := rs (se 3 (by rfl) ⟨14144, by rfl⟩) R28289
theorem R42767 : Reach 42767 := rs (se 1 (by rfl) ⟨32075, by rfl⟩) R64151
theorem R42785 : Reach 42785 := rs (se 2 (by rfl) ⟨16044, by rfl⟩) R32089
theorem R108377 : Reach 108377 := rs (se 2 (by rfl) ⟨40641, by rfl⟩) R81283
theorem R43019 : Reach 43019 := rs (se 1 (by rfl) ⟨32264, by rfl⟩) R64529
theorem R141335 : Reach 141335 := rs (se 1 (by rfl) ⟨106001, by rfl⟩) R212003
theorem R43037 : Reach 43037 := rs (se 3 (by rfl) ⟨8069, by rfl⟩) R16139
theorem R43051 : Reach 43051 := rs (se 1 (by rfl) ⟨32288, by rfl⟩) R64577
theorem R43127 : Reach 43127 := rs (se 1 (by rfl) ⟨32345, by rfl⟩) R64691
theorem R75977 : Reach 75977 := rs (se 2 (by rfl) ⟨28491, by rfl⟩) R56983
theorem R43379 : Reach 43379 := rs (se 1 (by rfl) ⟨32534, by rfl⟩) R65069
theorem R108985 : Reach 108985 := rs (se 2 (by rfl) ⟨40869, by rfl⟩) R81739
theorem R272857 : Reach 272857 := rs (se 2 (by rfl) ⟨102321, by rfl⟩) R204643
theorem R43721 : Reach 43721 := rs (se 2 (by rfl) ⟨16395, by rfl⟩) R32791
theorem R109349 : Reach 109349 := rs (se 4 (by rfl) ⟨10251, by rfl⟩) R20503
theorem R76747 : Reach 76747 := rs (se 1 (by rfl) ⟨57560, by rfl⟩) R115121
theorem R142397 : Reach 142397 := rs (se 3 (by rfl) ⟨26699, by rfl⟩) R53399
theorem R44347 : Reach 44347 := rs (se 1 (by rfl) ⟨33260, by rfl⟩) R66521
theorem R44423 : Reach 44423 := rs (se 1 (by rfl) ⟨33317, by rfl⟩) R66635
theorem R44441 : Reach 44441 := rs (se 2 (by rfl) ⟨16665, by rfl⟩) R33331
theorem R44801 : Reach 44801 := rs (se 2 (by rfl) ⟨16800, by rfl⟩) R33601
theorem R44833 : Reach 44833 := rs (se 2 (by rfl) ⟨16812, by rfl⟩) R33625
theorem R143153 : Reach 143153 := rs (se 2 (by rfl) ⟨53682, by rfl⟩) R107365
theorem R77753 : Reach 77753 := rs (se 2 (by rfl) ⟨29157, by rfl⟩) R58315
theorem R77867 : Reach 77867 := rs (se 1 (by rfl) ⟨58400, by rfl⟩) R116801
theorem R45143 : Reach 45143 := rs (se 1 (by rfl) ⟨33857, by rfl⟩) R67715
theorem R241937 : Reach 241937 := rs (se 2 (by rfl) ⟨90726, by rfl⟩) R181453
theorem R536977 : Reach 536977 := rs (se 2 (by rfl) ⟨201366, by rfl⟩) R402733
theorem R12859 : Reach 12859 := rs (se 1 (by rfl) ⟨9644, by rfl⟩) R19289
theorem R45629 : Reach 45629 := rs (se 3 (by rfl) ⟨8555, by rfl⟩) R17111
theorem R12935 : Reach 12935 := rs (se 1 (by rfl) ⟨9701, by rfl⟩) R19403
theorem R12943 : Reach 12943 := rs (se 1 (by rfl) ⟨9707, by rfl⟩) R19415
theorem R12987 : Reach 12987 := rs (se 1 (by rfl) ⟨9740, by rfl⟩) R19481
theorem R45805 : Reach 45805 := rs (se 3 (by rfl) ⟨8588, by rfl⟩) R17177
theorem R13063 : Reach 13063 := rs (se 1 (by rfl) ⟨9797, by rfl⟩) R19595
theorem R13071 : Reach 13071 := rs (se 1 (by rfl) ⟨9803, by rfl⟩) R19607
theorem R45883 : Reach 45883 := rs (se 1 (by rfl) ⟨34412, by rfl⟩) R68825
theorem R13115 : Reach 13115 := rs (se 1 (by rfl) ⟨9836, by rfl⟩) R19673
theorem R13191 : Reach 13191 := rs (se 1 (by rfl) ⟨9893, by rfl⟩) R19787
theorem R13199 : Reach 13199 := rs (se 1 (by rfl) ⟨9899, by rfl⟩) R19799
theorem R144281 : Reach 144281 := rs (se 2 (by rfl) ⟨54105, by rfl⟩) R108211
theorem R13243 : Reach 13243 := rs (se 1 (by rfl) ⟨9932, by rfl⟩) R19865
theorem R13319 : Reach 13319 := rs (se 1 (by rfl) ⟨9989, by rfl⟩) R19979
theorem R13327 : Reach 13327 := rs (se 1 (by rfl) ⟨9995, by rfl⟩) R19991
theorem R46109 : Reach 46109 := rs (se 3 (by rfl) ⟨8645, by rfl⟩) R17291
theorem R13371 : Reach 13371 := rs (se 1 (by rfl) ⟨10028, by rfl⟩) R20057
theorem R13447 : Reach 13447 := rs (se 1 (by rfl) ⟨10085, by rfl⟩) R20171
theorem R13455 : Reach 13455 := rs (se 1 (by rfl) ⟨10091, by rfl⟩) R20183
theorem R13499 : Reach 13499 := rs (se 1 (by rfl) ⟨10124, by rfl⟩) R20249
theorem R46337 : Reach 46337 := rs (se 2 (by rfl) ⟨17376, by rfl⟩) R34753
theorem R13575 : Reach 13575 := rs (se 1 (by rfl) ⟨10181, by rfl⟩) R20363
theorem R13583 : Reach 13583 := rs (se 1 (by rfl) ⟨10187, by rfl⟩) R20375
theorem R13627 : Reach 13627 := rs (se 1 (by rfl) ⟨10220, by rfl⟩) R20441
theorem R13703 : Reach 13703 := rs (se 1 (by rfl) ⟨10277, by rfl⟩) R20555
theorem R13711 : Reach 13711 := rs (se 1 (by rfl) ⟨10283, by rfl⟩) R20567
theorem R1291697 : Reach 1291697 := rs (se 2 (by rfl) ⟨484386, by rfl⟩) R968773
theorem R13755 : Reach 13755 := rs (se 1 (by rfl) ⟨10316, by rfl⟩) R20633
theorem R79325 : Reach 79325 := rs (se 3 (by rfl) ⟨14873, by rfl⟩) R29747
theorem R13831 : Reach 13831 := rs (se 1 (by rfl) ⟨10373, by rfl⟩) R20747
theorem R13839 : Reach 13839 := rs (se 1 (by rfl) ⟨10379, by rfl⟩) R20759
theorem R13883 : Reach 13883 := rs (se 1 (by rfl) ⟨10412, by rfl⟩) R20825
theorem R112205 : Reach 112205 := rs (se 3 (by rfl) ⟨21038, by rfl⟩) R42077
theorem R13959 : Reach 13959 := rs (se 1 (by rfl) ⟨10469, by rfl⟩) R20939
theorem R13967 : Reach 13967 := rs (se 1 (by rfl) ⟨10475, by rfl⟩) R20951
theorem R14011 : Reach 14011 := rs (se 1 (by rfl) ⟨10508, by rfl⟩) R21017
theorem R46793 : Reach 46793 := rs (se 2 (by rfl) ⟨17547, by rfl⟩) R35095
theorem R112357 : Reach 112357 := rs (se 4 (by rfl) ⟨10533, by rfl⟩) R21067
theorem R14087 : Reach 14087 := rs (se 1 (by rfl) ⟨10565, by rfl⟩) R21131
theorem R14095 : Reach 14095 := rs (se 1 (by rfl) ⟨10571, by rfl⟩) R21143
theorem R79667 : Reach 79667 := rs (se 1 (by rfl) ⟨59750, by rfl⟩) R119501
theorem R14139 : Reach 14139 := rs (se 1 (by rfl) ⟨10604, by rfl⟩) R21209
theorem R14215 : Reach 14215 := rs (se 1 (by rfl) ⟨10661, by rfl⟩) R21323
theorem R14223 : Reach 14223 := rs (se 1 (by rfl) ⟨10667, by rfl⟩) R21335
theorem R47033 : Reach 47033 := rs (se 2 (by rfl) ⟨17637, by rfl⟩) R35275
theorem R14267 : Reach 14267 := rs (se 1 (by rfl) ⟨10700, by rfl⟩) R21401
theorem R79825 : Reach 79825 := rs (se 2 (by rfl) ⟨29934, by rfl⟩) R59869
theorem R14343 : Reach 14343 := rs (se 1 (by rfl) ⟨10757, by rfl⟩) R21515
theorem R14351 : Reach 14351 := rs (se 1 (by rfl) ⟨10763, by rfl⟩) R21527
theorem R14395 : Reach 14395 := rs (se 1 (by rfl) ⟨10796, by rfl⟩) R21593
theorem R14471 : Reach 14471 := rs (se 1 (by rfl) ⟨10853, by rfl⟩) R21707
theorem R14479 : Reach 14479 := rs (se 1 (by rfl) ⟨10859, by rfl⟩) R21719
theorem R14523 : Reach 14523 := rs (se 1 (by rfl) ⟨10892, by rfl⟩) R21785
theorem R14599 : Reach 14599 := rs (se 1 (by rfl) ⟨10949, by rfl⟩) R21899
theorem R14607 : Reach 14607 := rs (se 1 (by rfl) ⟨10955, by rfl⟩) R21911
theorem R47375 : Reach 47375 := rs (se 1 (by rfl) ⟨35531, by rfl⟩) R71063
theorem R14651 : Reach 14651 := rs (se 1 (by rfl) ⟨10988, by rfl⟩) R21977
theorem R14727 : Reach 14727 := rs (se 1 (by rfl) ⟨11045, by rfl⟩) R22091
theorem R145799 : Reach 145799 := rs (se 1 (by rfl) ⟨109349, by rfl⟩) R218699
theorem R14735 : Reach 14735 := rs (se 1 (by rfl) ⟨11051, by rfl⟩) R22103
theorem R14779 : Reach 14779 := rs (se 1 (by rfl) ⟨11084, by rfl⟩) R22169
theorem R113105 : Reach 113105 := rs (se 2 (by rfl) ⟨42414, by rfl⟩) R84829
theorem R14855 : Reach 14855 := rs (se 1 (by rfl) ⟨11141, by rfl⟩) R22283
theorem R47627 : Reach 47627 := rs (se 1 (by rfl) ⟨35720, by rfl⟩) R71441
theorem R14863 : Reach 14863 := rs (se 1 (by rfl) ⟨11147, by rfl⟩) R22295
theorem R14907 : Reach 14907 := rs (se 1 (by rfl) ⟨11180, by rfl⟩) R22361
theorem R47735 : Reach 47735 := rs (se 1 (by rfl) ⟨35801, by rfl⟩) R71603
theorem R14983 : Reach 14983 := rs (se 1 (by rfl) ⟨11237, by rfl⟩) R22475
theorem R14991 : Reach 14991 := rs (se 1 (by rfl) ⟨11243, by rfl⟩) R22487
theorem R15035 : Reach 15035 := rs (se 1 (by rfl) ⟨11276, by rfl⟩) R22553
theorem R15111 : Reach 15111 := rs (se 1 (by rfl) ⟨11333, by rfl⟩) R22667
theorem R15119 : Reach 15119 := rs (se 1 (by rfl) ⟨11339, by rfl⟩) R22679
theorem R211747 : Reach 211747 := rs (se 1 (by rfl) ⟨158810, by rfl⟩) R317621
theorem R15163 : Reach 15163 := rs (se 1 (by rfl) ⟨11372, by rfl⟩) R22745
theorem R15223 : Reach 15223 := rs (se 1 (by rfl) ⟨11417, by rfl⟩) R22835
theorem R15239 : Reach 15239 := rs (se 1 (by rfl) ⟨11429, by rfl⟩) R22859
theorem R15247 : Reach 15247 := rs (se 1 (by rfl) ⟨11435, by rfl⟩) R22871
theorem R15275 : Reach 15275 := rs (se 1 (by rfl) ⟨11456, by rfl⟩) R22913
theorem R15291 : Reach 15291 := rs (se 1 (by rfl) ⟨11468, by rfl⟩) R22937
theorem R15351 : Reach 15351 := rs (se 1 (by rfl) ⟨11513, by rfl⟩) R23027
theorem R15367 : Reach 15367 := rs (se 1 (by rfl) ⟨11525, by rfl⟩) R23051
theorem R15375 : Reach 15375 := rs (se 1 (by rfl) ⟨11531, by rfl⟩) R23063
theorem R15403 : Reach 15403 := rs (se 1 (by rfl) ⟨11552, by rfl⟩) R23105
theorem R15419 : Reach 15419 := rs (se 1 (by rfl) ⟨11564, by rfl⟩) R23129
theorem R80963 : Reach 80963 := rs (se 1 (by rfl) ⟨60722, by rfl⟩) R121445
theorem R48215 : Reach 48215 := rs (se 1 (by rfl) ⟨36161, by rfl⟩) R72323
theorem R15479 : Reach 15479 := rs (se 1 (by rfl) ⟨11609, by rfl⟩) R23219
theorem R179333 : Reach 179333 := rs (se 4 (by rfl) ⟨16812, by rfl⟩) R33625
theorem R15495 : Reach 15495 := rs (se 1 (by rfl) ⟨11621, by rfl⟩) R23243
theorem R15503 : Reach 15503 := rs (se 1 (by rfl) ⟨11627, by rfl⟩) R23255
theorem R15531 : Reach 15531 := rs (se 1 (by rfl) ⟨11648, by rfl⟩) R23297
theorem R15547 : Reach 15547 := rs (se 1 (by rfl) ⟨11660, by rfl⟩) R23321
theorem R48329 : Reach 48329 := rs (se 2 (by rfl) ⟨18123, by rfl⟩) R36247
theorem R48365 : Reach 48365 := rs (se 3 (by rfl) ⟨9068, by rfl⟩) R18137
theorem R15607 : Reach 15607 := rs (se 1 (by rfl) ⟨11705, by rfl⟩) R23411
theorem R15623 : Reach 15623 := rs (se 1 (by rfl) ⟨11717, by rfl⟩) R23435
theorem R15631 : Reach 15631 := rs (se 1 (by rfl) ⟨11723, by rfl⟩) R23447
theorem R15659 : Reach 15659 := rs (se 1 (by rfl) ⟨11744, by rfl⟩) R23489
theorem R15675 : Reach 15675 := rs (se 1 (by rfl) ⟨11756, by rfl⟩) R23513
theorem R15735 : Reach 15735 := rs (se 1 (by rfl) ⟨11801, by rfl⟩) R23603
theorem R15751 : Reach 15751 := rs (se 1 (by rfl) ⟨11813, by rfl⟩) R23627
theorem R15759 : Reach 15759 := rs (se 1 (by rfl) ⟨11819, by rfl⟩) R23639
theorem R15787 : Reach 15787 := rs (se 1 (by rfl) ⟨11840, by rfl⟩) R23681
theorem R15803 : Reach 15803 := rs (se 1 (by rfl) ⟨11852, by rfl⟩) R23705
theorem R48593 : Reach 48593 := rs (se 2 (by rfl) ⟨18222, by rfl⟩) R36445
theorem R15863 : Reach 15863 := rs (se 1 (by rfl) ⟨11897, by rfl⟩) R23795
theorem R15879 : Reach 15879 := rs (se 1 (by rfl) ⟨11909, by rfl⟩) R23819
theorem R15887 : Reach 15887 := rs (se 1 (by rfl) ⟨11915, by rfl⟩) R23831
theorem R15915 : Reach 15915 := rs (se 1 (by rfl) ⟨11936, by rfl⟩) R23873
theorem R15931 : Reach 15931 := rs (se 1 (by rfl) ⟨11948, by rfl⟩) R23897
theorem R48701 : Reach 48701 := rs (se 3 (by rfl) ⟨9131, by rfl⟩) R18263
theorem R48707 : Reach 48707 := rs (se 1 (by rfl) ⟨36530, by rfl⟩) R73061
theorem R15991 : Reach 15991 := rs (se 1 (by rfl) ⟨11993, by rfl⟩) R23987
theorem R16007 : Reach 16007 := rs (se 1 (by rfl) ⟨12005, by rfl⟩) R24011
theorem R16015 : Reach 16015 := rs (se 1 (by rfl) ⟨12011, by rfl⟩) R24023
theorem R16043 : Reach 16043 := rs (se 1 (by rfl) ⟨12032, by rfl⟩) R24065
theorem R16059 : Reach 16059 := rs (se 1 (by rfl) ⟨12044, by rfl⟩) R24089
theorem R16119 : Reach 16119 := rs (se 1 (by rfl) ⟨12089, by rfl⟩) R24179
theorem R16135 : Reach 16135 := rs (se 1 (by rfl) ⟨12101, by rfl⟩) R24203
theorem R16143 : Reach 16143 := rs (se 1 (by rfl) ⟨12107, by rfl⟩) R24215
theorem R16171 : Reach 16171 := rs (se 1 (by rfl) ⟨12128, by rfl⟩) R24257
theorem R16187 : Reach 16187 := rs (se 1 (by rfl) ⟨12140, by rfl⟩) R24281
theorem R16247 : Reach 16247 := rs (se 1 (by rfl) ⟨12185, by rfl⟩) R24371
theorem R49031 : Reach 49031 := rs (se 1 (by rfl) ⟨36773, by rfl⟩) R73547
theorem R16263 : Reach 16263 := rs (se 1 (by rfl) ⟨12197, by rfl⟩) R24395
theorem R16271 : Reach 16271 := rs (se 1 (by rfl) ⟨12203, by rfl⟩) R24407
theorem R49049 : Reach 49049 := rs (se 2 (by rfl) ⟨18393, by rfl⟩) R36787
theorem R16299 : Reach 16299 := rs (se 1 (by rfl) ⟨12224, by rfl⟩) R24449
theorem R16315 : Reach 16315 := rs (se 1 (by rfl) ⟨12236, by rfl⟩) R24473
theorem R114635 : Reach 114635 := rs (se 1 (by rfl) ⟨85976, by rfl⟩) R171953
theorem R16375 : Reach 16375 := rs (se 1 (by rfl) ⟨12281, by rfl⟩) R24563
theorem R16391 : Reach 16391 := rs (se 1 (by rfl) ⟨12293, by rfl⟩) R24587
theorem R16399 : Reach 16399 := rs (se 1 (by rfl) ⟨12299, by rfl⟩) R24599
theorem R16427 : Reach 16427 := rs (se 1 (by rfl) ⟨12320, by rfl⟩) R24641
theorem R16443 : Reach 16443 := rs (se 1 (by rfl) ⟨12332, by rfl⟩) R24665
theorem R16503 : Reach 16503 := rs (se 1 (by rfl) ⟨12377, by rfl⟩) R24755
theorem R16519 : Reach 16519 := rs (se 1 (by rfl) ⟨12389, by rfl⟩) R24779
theorem R16527 : Reach 16527 := rs (se 1 (by rfl) ⟨12395, by rfl⟩) R24791
theorem R16555 : Reach 16555 := rs (se 1 (by rfl) ⟨12416, by rfl⟩) R24833
theorem R16571 : Reach 16571 := rs (se 1 (by rfl) ⟨12428, by rfl⟩) R24857
theorem R16631 : Reach 16631 := rs (se 1 (by rfl) ⟨12473, by rfl⟩) R24947
theorem R49409 : Reach 49409 := rs (se 2 (by rfl) ⟨18528, by rfl⟩) R37057
theorem R16647 : Reach 16647 := rs (se 1 (by rfl) ⟨12485, by rfl⟩) R24971
theorem R16655 : Reach 16655 := rs (se 1 (by rfl) ⟨12491, by rfl⟩) R24983
theorem R16683 : Reach 16683 := rs (se 1 (by rfl) ⟨12512, by rfl⟩) R25025
theorem R16699 : Reach 16699 := rs (se 1 (by rfl) ⟨12524, by rfl⟩) R25049
theorem R16759 : Reach 16759 := rs (se 1 (by rfl) ⟨12569, by rfl⟩) R25139
theorem R16775 : Reach 16775 := rs (se 1 (by rfl) ⟨12581, by rfl⟩) R25163
theorem R16783 : Reach 16783 := rs (se 1 (by rfl) ⟨12587, by rfl⟩) R25175
theorem R115091 : Reach 115091 := rs (se 1 (by rfl) ⟨86318, by rfl⟩) R172637
theorem R16811 : Reach 16811 := rs (se 1 (by rfl) ⟨12608, by rfl⟩) R25217
theorem R16827 : Reach 16827 := rs (se 1 (by rfl) ⟨12620, by rfl⟩) R25241
theorem R180701 : Reach 180701 := rs (se 3 (by rfl) ⟨33881, by rfl⟩) R67763
theorem R16887 : Reach 16887 := rs (se 1 (by rfl) ⟨12665, by rfl⟩) R25331
theorem R16903 : Reach 16903 := rs (se 1 (by rfl) ⟨12677, by rfl⟩) R25355
theorem R16911 : Reach 16911 := rs (se 1 (by rfl) ⟨12683, by rfl⟩) R25367
theorem R49693 : Reach 49693 := rs (se 3 (by rfl) ⟨9317, by rfl⟩) R18635
theorem R16939 : Reach 16939 := rs (se 1 (by rfl) ⟨12704, by rfl⟩) R25409
theorem R16955 : Reach 16955 := rs (se 1 (by rfl) ⟨12716, by rfl⟩) R25433
theorem R17015 : Reach 17015 := rs (se 1 (by rfl) ⟨12761, by rfl⟩) R25523
theorem R17031 : Reach 17031 := rs (se 1 (by rfl) ⟨12773, by rfl⟩) R25547
theorem R17039 : Reach 17039 := rs (se 1 (by rfl) ⟨12779, by rfl⟩) R25559
theorem R17067 : Reach 17067 := rs (se 1 (by rfl) ⟨12800, by rfl⟩) R25601
theorem R17083 : Reach 17083 := rs (se 1 (by rfl) ⟨12812, by rfl⟩) R25625
theorem R17143 : Reach 17143 := rs (se 1 (by rfl) ⟨12857, by rfl⟩) R25715
theorem R17159 : Reach 17159 := rs (se 1 (by rfl) ⟨12869, by rfl⟩) R25739
theorem R17167 : Reach 17167 := rs (se 1 (by rfl) ⟨12875, by rfl⟩) R25751
theorem R17195 : Reach 17195 := rs (se 1 (by rfl) ⟨12896, by rfl⟩) R25793
theorem R17209 : Reach 17209 := rs (se 2 (by rfl) ⟨6453, by rfl⟩) R12907
theorem R17211 : Reach 17211 := rs (se 1 (by rfl) ⟨12908, by rfl⟩) R25817
theorem R17225 : Reach 17225 := rs (se 2 (by rfl) ⟨6459, by rfl⟩) R12919
theorem R17271 : Reach 17271 := rs (se 1 (by rfl) ⟨12953, by rfl⟩) R25907
theorem R17287 : Reach 17287 := rs (se 1 (by rfl) ⟨12965, by rfl⟩) R25931
theorem R17295 : Reach 17295 := rs (se 1 (by rfl) ⟨12971, by rfl⟩) R25943
theorem R17323 : Reach 17323 := rs (se 1 (by rfl) ⟨12992, by rfl⟩) R25985
theorem R50105 : Reach 50105 := rs (se 2 (by rfl) ⟨18789, by rfl⟩) R37579
theorem R17337 : Reach 17337 := rs (se 2 (by rfl) ⟨6501, by rfl⟩) R13003
theorem R17339 : Reach 17339 := rs (se 1 (by rfl) ⟨13004, by rfl⟩) R26009
theorem R17353 : Reach 17353 := rs (se 2 (by rfl) ⟨6507, by rfl⟩) R13015
theorem R50129 : Reach 50129 := rs (se 2 (by rfl) ⟨18798, by rfl⟩) R37597
theorem R17399 : Reach 17399 := rs (se 1 (by rfl) ⟨13049, by rfl⟩) R26099
theorem R17415 : Reach 17415 := rs (se 1 (by rfl) ⟨13061, by rfl⟩) R26123
theorem R17423 : Reach 17423 := rs (se 1 (by rfl) ⟨13067, by rfl⟩) R26135
theorem R50219 : Reach 50219 := rs (se 1 (by rfl) ⟨37664, by rfl⟩) R75329
theorem R17451 : Reach 17451 := rs (se 1 (by rfl) ⟨13088, by rfl⟩) R26177
theorem R17465 : Reach 17465 := rs (se 2 (by rfl) ⟨6549, by rfl⟩) R13099
theorem R17467 : Reach 17467 := rs (se 1 (by rfl) ⟨13100, by rfl⟩) R26201
theorem R17481 : Reach 17481 := rs (se 2 (by rfl) ⟨6555, by rfl⟩) R13111
theorem R17527 : Reach 17527 := rs (se 1 (by rfl) ⟨13145, by rfl⟩) R26291
theorem R17543 : Reach 17543 := rs (se 1 (by rfl) ⟨13157, by rfl⟩) R26315
theorem R17551 : Reach 17551 := rs (se 1 (by rfl) ⟨13163, by rfl⟩) R26327
theorem R17579 : Reach 17579 := rs (se 1 (by rfl) ⟨13184, by rfl⟩) R26369
theorem R17593 : Reach 17593 := rs (se 2 (by rfl) ⟨6597, by rfl⟩) R13195
theorem R17595 : Reach 17595 := rs (se 1 (by rfl) ⟨13196, by rfl⟩) R26393
theorem R17609 : Reach 17609 := rs (se 2 (by rfl) ⟨6603, by rfl⟩) R13207
theorem R17655 : Reach 17655 := rs (se 1 (by rfl) ⟨13241, by rfl⟩) R26483
theorem R17671 : Reach 17671 := rs (se 1 (by rfl) ⟨13253, by rfl⟩) R26507
theorem R17679 : Reach 17679 := rs (se 1 (by rfl) ⟨13259, by rfl⟩) R26519
theorem R17707 : Reach 17707 := rs (se 1 (by rfl) ⟨13280, by rfl⟩) R26561
theorem R17721 : Reach 17721 := rs (se 2 (by rfl) ⟨6645, by rfl⟩) R13291
theorem R17723 : Reach 17723 := rs (se 1 (by rfl) ⟨13292, by rfl⟩) R26585
theorem R17737 : Reach 17737 := rs (se 2 (by rfl) ⟨6651, by rfl⟩) R13303
theorem R17783 : Reach 17783 := rs (se 1 (by rfl) ⟨13337, by rfl⟩) R26675
theorem R17799 : Reach 17799 := rs (se 1 (by rfl) ⟨13349, by rfl⟩) R26699
theorem R17807 : Reach 17807 := rs (se 1 (by rfl) ⟨13355, by rfl⟩) R26711
theorem R17835 : Reach 17835 := rs (se 1 (by rfl) ⟨13376, by rfl⟩) R26753
theorem R116153 : Reach 116153 := rs (se 2 (by rfl) ⟨43557, by rfl⟩) R87115
theorem R17849 : Reach 17849 := rs (se 2 (by rfl) ⟨6693, by rfl⟩) R13387
theorem R17851 : Reach 17851 := rs (se 1 (by rfl) ⟨13388, by rfl⟩) R26777
theorem R17865 : Reach 17865 := rs (se 2 (by rfl) ⟨6699, by rfl⟩) R13399
theorem R17911 : Reach 17911 := rs (se 1 (by rfl) ⟨13433, by rfl⟩) R26867
theorem R181763 : Reach 181763 := rs (se 1 (by rfl) ⟨136322, by rfl⟩) R272645
theorem R17927 : Reach 17927 := rs (se 1 (by rfl) ⟨13445, by rfl⟩) R26891
theorem R17935 : Reach 17935 := rs (se 1 (by rfl) ⟨13451, by rfl⟩) R26903
theorem R17963 : Reach 17963 := rs (se 1 (by rfl) ⟨13472, by rfl⟩) R26945
theorem R17977 : Reach 17977 := rs (se 2 (by rfl) ⟨6741, by rfl⟩) R13483
theorem R17979 : Reach 17979 := rs (se 1 (by rfl) ⟨13484, by rfl⟩) R26969
theorem R17993 : Reach 17993 := rs (se 2 (by rfl) ⟨6747, by rfl⟩) R13495
theorem R247373 : Reach 247373 := rs (se 3 (by rfl) ⟨46382, by rfl⟩) R92765
theorem R18039 : Reach 18039 := rs (se 1 (by rfl) ⟨13529, by rfl⟩) R27059
theorem R18055 : Reach 18055 := rs (se 1 (by rfl) ⟨13541, by rfl⟩) R27083
theorem R18063 : Reach 18063 := rs (se 1 (by rfl) ⟨13547, by rfl⟩) R27095
theorem R18091 : Reach 18091 := rs (se 1 (by rfl) ⟨13568, by rfl⟩) R27137
theorem R18105 : Reach 18105 := rs (se 2 (by rfl) ⟨6789, by rfl⟩) R13579
theorem R18107 : Reach 18107 := rs (se 1 (by rfl) ⟨13580, by rfl⟩) R27161
theorem R18121 : Reach 18121 := rs (se 2 (by rfl) ⟨6795, by rfl⟩) R13591
theorem R18167 : Reach 18167 := rs (se 1 (by rfl) ⟨13625, by rfl⟩) R27251
theorem R18183 : Reach 18183 := rs (se 1 (by rfl) ⟨13637, by rfl⟩) R27275
theorem R18191 : Reach 18191 := rs (se 1 (by rfl) ⟨13643, by rfl⟩) R27287
theorem R18219 : Reach 18219 := rs (se 1 (by rfl) ⟨13664, by rfl⟩) R27329
theorem R18233 : Reach 18233 := rs (se 2 (by rfl) ⟨6837, by rfl⟩) R13675
theorem R18235 : Reach 18235 := rs (se 1 (by rfl) ⟨13676, by rfl⟩) R27353
theorem R18249 : Reach 18249 := rs (se 2 (by rfl) ⟨6843, by rfl⟩) R13687
theorem R18295 : Reach 18295 := rs (se 1 (by rfl) ⟨13721, by rfl⟩) R27443
theorem R18311 : Reach 18311 := rs (se 1 (by rfl) ⟨13733, by rfl⟩) R27467
theorem R18319 : Reach 18319 := rs (se 1 (by rfl) ⟨13739, by rfl⟩) R27479
theorem R18347 : Reach 18347 := rs (se 1 (by rfl) ⟨13760, by rfl⟩) R27521
theorem R18361 : Reach 18361 := rs (se 2 (by rfl) ⟨6885, by rfl⟩) R13771
theorem R18363 : Reach 18363 := rs (se 1 (by rfl) ⟨13772, by rfl⟩) R27545
theorem R18377 : Reach 18377 := rs (se 2 (by rfl) ⟨6891, by rfl⟩) R13783
theorem R83915 : Reach 83915 := rs (se 1 (by rfl) ⟨62936, by rfl⟩) R125873
theorem R18423 : Reach 18423 := rs (se 1 (by rfl) ⟨13817, by rfl⟩) R27635
theorem R18439 : Reach 18439 := rs (se 1 (by rfl) ⟨13829, by rfl⟩) R27659
theorem R18447 : Reach 18447 := rs (se 1 (by rfl) ⟨13835, by rfl⟩) R27671
theorem R18475 : Reach 18475 := rs (se 1 (by rfl) ⟨13856, by rfl⟩) R27713
theorem R18489 : Reach 18489 := rs (se 2 (by rfl) ⟨6933, by rfl⟩) R13867
theorem R18491 : Reach 18491 := rs (se 1 (by rfl) ⟨13868, by rfl⟩) R27737
theorem R18505 : Reach 18505 := rs (se 2 (by rfl) ⟨6939, by rfl⟩) R13879
theorem R18551 : Reach 18551 := rs (se 1 (by rfl) ⟨13913, by rfl⟩) R27827
theorem R18567 : Reach 18567 := rs (se 1 (by rfl) ⟨13925, by rfl⟩) R27851
theorem R18575 : Reach 18575 := rs (se 1 (by rfl) ⟨13931, by rfl⟩) R27863
theorem R18603 : Reach 18603 := rs (se 1 (by rfl) ⟨13952, by rfl⟩) R27905
theorem R18617 : Reach 18617 := rs (se 2 (by rfl) ⟨6981, by rfl⟩) R13963
theorem R18619 : Reach 18619 := rs (se 1 (by rfl) ⟨13964, by rfl⟩) R27929
theorem R18633 : Reach 18633 := rs (se 2 (by rfl) ⟨6987, by rfl⟩) R13975
theorem R18679 : Reach 18679 := rs (se 1 (by rfl) ⟨14009, by rfl⟩) R28019
theorem R18695 : Reach 18695 := rs (se 1 (by rfl) ⟨14021, by rfl⟩) R28043
theorem R18703 : Reach 18703 := rs (se 1 (by rfl) ⟨14027, by rfl⟩) R28055
theorem R18731 : Reach 18731 := rs (se 1 (by rfl) ⟨14048, by rfl⟩) R28097
theorem R18745 : Reach 18745 := rs (se 2 (by rfl) ⟨7029, by rfl⟩) R14059
theorem R51515 : Reach 51515 := rs (se 1 (by rfl) ⟨38636, by rfl⟩) R77273
theorem R18747 : Reach 18747 := rs (se 1 (by rfl) ⟨14060, by rfl⟩) R28121
theorem R18761 : Reach 18761 := rs (se 2 (by rfl) ⟨7035, by rfl⟩) R14071
theorem R18807 : Reach 18807 := rs (se 1 (by rfl) ⟨14105, by rfl⟩) R28211
theorem R18823 : Reach 18823 := rs (se 1 (by rfl) ⟨14117, by rfl⟩) R28235
theorem R18831 : Reach 18831 := rs (se 1 (by rfl) ⟨14123, by rfl⟩) R28247
theorem R18859 : Reach 18859 := rs (se 1 (by rfl) ⟨14144, by rfl⟩) R28289
theorem R51641 : Reach 51641 := rs (se 2 (by rfl) ⟨19365, by rfl⟩) R38731
theorem R18873 : Reach 18873 := rs (se 2 (by rfl) ⟨7077, by rfl⟩) R14155
theorem R18875 : Reach 18875 := rs (se 1 (by rfl) ⟨14156, by rfl⟩) R28313
theorem R18889 : Reach 18889 := rs (se 2 (by rfl) ⟨7083, by rfl⟩) R14167
theorem R18935 : Reach 18935 := rs (se 1 (by rfl) ⟨14201, by rfl⟩) R28403
theorem R18951 : Reach 18951 := rs (se 1 (by rfl) ⟨14213, by rfl⟩) R28427
theorem R18959 : Reach 18959 := rs (se 1 (by rfl) ⟨14219, by rfl⟩) R28439
theorem R84509 : Reach 84509 := rs (se 3 (by rfl) ⟨15845, by rfl⟩) R31691
theorem R18987 : Reach 18987 := rs (se 1 (by rfl) ⟨14240, by rfl⟩) R28481
theorem R19001 : Reach 19001 := rs (se 2 (by rfl) ⟨7125, by rfl⟩) R14251
theorem R19003 : Reach 19003 := rs (se 1 (by rfl) ⟨14252, by rfl⟩) R28505
theorem R150083 : Reach 150083 := rs (se 1 (by rfl) ⟨112562, by rfl⟩) R225125
theorem R19017 : Reach 19017 := rs (se 2 (by rfl) ⟨7131, by rfl⟩) R14263
theorem R19063 : Reach 19063 := rs (se 1 (by rfl) ⟨14297, by rfl⟩) R28595
theorem R19079 : Reach 19079 := rs (se 1 (by rfl) ⟨14309, by rfl⟩) R28619
theorem R19087 : Reach 19087 := rs (se 1 (by rfl) ⟨14315, by rfl⟩) R28631
theorem R19115 : Reach 19115 := rs (se 1 (by rfl) ⟨14336, by rfl⟩) R28673
theorem R19129 : Reach 19129 := rs (se 2 (by rfl) ⟨7173, by rfl⟩) R14347
theorem R19131 : Reach 19131 := rs (se 1 (by rfl) ⟨14348, by rfl⟩) R28697
theorem R19145 : Reach 19145 := rs (se 2 (by rfl) ⟨7179, by rfl⟩) R14359
theorem R19191 : Reach 19191 := rs (se 1 (by rfl) ⟨14393, by rfl⟩) R28787
theorem R19207 : Reach 19207 := rs (se 1 (by rfl) ⟨14405, by rfl⟩) R28811
theorem R19215 : Reach 19215 := rs (se 1 (by rfl) ⟨14411, by rfl⟩) R28823
theorem R52001 : Reach 52001 := rs (se 2 (by rfl) ⟨19500, by rfl⟩) R39001
theorem R19243 : Reach 19243 := rs (se 1 (by rfl) ⟨14432, by rfl⟩) R28865
theorem R19257 : Reach 19257 := rs (se 2 (by rfl) ⟨7221, by rfl⟩) R14443
theorem R19259 : Reach 19259 := rs (se 1 (by rfl) ⟨14444, by rfl⟩) R28889
theorem R19273 : Reach 19273 := rs (se 2 (by rfl) ⟨7227, by rfl⟩) R14455
theorem R19319 : Reach 19319 := rs (se 1 (by rfl) ⟨14489, by rfl⟩) R28979
theorem R19335 : Reach 19335 := rs (se 1 (by rfl) ⟨14501, by rfl⟩) R29003
theorem R19343 : Reach 19343 := rs (se 1 (by rfl) ⟨14507, by rfl⟩) R29015
theorem R19371 : Reach 19371 := rs (se 1 (by rfl) ⟨14528, by rfl⟩) R29057
theorem R19385 : Reach 19385 := rs (se 2 (by rfl) ⟨7269, by rfl⟩) R14539
theorem R19387 : Reach 19387 := rs (se 1 (by rfl) ⟨14540, by rfl⟩) R29081
theorem R19401 : Reach 19401 := rs (se 2 (by rfl) ⟨7275, by rfl⟩) R14551
theorem R19447 : Reach 19447 := rs (se 1 (by rfl) ⟨14585, by rfl⟩) R29171
theorem R19463 : Reach 19463 := rs (se 1 (by rfl) ⟨14597, by rfl⟩) R29195
theorem R19471 : Reach 19471 := rs (se 1 (by rfl) ⟨14603, by rfl⟩) R29207
theorem R19499 : Reach 19499 := rs (se 1 (by rfl) ⟨14624, by rfl⟩) R29249
theorem R19513 : Reach 19513 := rs (se 2 (by rfl) ⟨7317, by rfl⟩) R14635
theorem R19515 : Reach 19515 := rs (se 1 (by rfl) ⟨14636, by rfl⟩) R29273
theorem R19529 : Reach 19529 := rs (se 2 (by rfl) ⟨7323, by rfl⟩) R14647
theorem R52343 : Reach 52343 := rs (se 1 (by rfl) ⟨39257, by rfl⟩) R78515
theorem R19575 : Reach 19575 := rs (se 1 (by rfl) ⟨14681, by rfl⟩) R29363
theorem R19591 : Reach 19591 := rs (se 1 (by rfl) ⟨14693, by rfl⟩) R29387
theorem R19599 : Reach 19599 := rs (se 1 (by rfl) ⟨14699, by rfl⟩) R29399
theorem R19627 : Reach 19627 := rs (se 1 (by rfl) ⟨14720, by rfl⟩) R29441
theorem R19641 : Reach 19641 := rs (se 2 (by rfl) ⟨7365, by rfl⟩) R14731
theorem R19643 : Reach 19643 := rs (se 1 (by rfl) ⟨14732, by rfl⟩) R29465
theorem R19657 : Reach 19657 := rs (se 2 (by rfl) ⟨7371, by rfl⟩) R14743
theorem R19703 : Reach 19703 := rs (se 1 (by rfl) ⟨14777, by rfl⟩) R29555
theorem R19719 : Reach 19719 := rs (se 1 (by rfl) ⟨14789, by rfl⟩) R29579
theorem R19727 : Reach 19727 := rs (se 1 (by rfl) ⟨14795, by rfl⟩) R29591
theorem R19755 : Reach 19755 := rs (se 1 (by rfl) ⟨14816, by rfl⟩) R29633
theorem R19769 : Reach 19769 := rs (se 2 (by rfl) ⟨7413, by rfl⟩) R14827
theorem R19771 : Reach 19771 := rs (se 1 (by rfl) ⟨14828, by rfl⟩) R29657
theorem R19785 : Reach 19785 := rs (se 2 (by rfl) ⟨7419, by rfl⟩) R14839
theorem R52595 : Reach 52595 := rs (se 1 (by rfl) ⟨39446, by rfl⟩) R78893
theorem R19831 : Reach 19831 := rs (se 1 (by rfl) ⟨14873, by rfl⟩) R29747
theorem R281987 : Reach 281987 := rs (se 1 (by rfl) ⟨211490, by rfl⟩) R422981
theorem R19847 : Reach 19847 := rs (se 1 (by rfl) ⟨14885, by rfl⟩) R29771
theorem R19855 : Reach 19855 := rs (se 1 (by rfl) ⟨14891, by rfl⟩) R29783
theorem R19883 : Reach 19883 := rs (se 1 (by rfl) ⟨14912, by rfl⟩) R29825
theorem R118201 : Reach 118201 := rs (se 2 (by rfl) ⟨44325, by rfl⟩) R88651
theorem R19897 : Reach 19897 := rs (se 2 (by rfl) ⟨7461, by rfl⟩) R14923
theorem R19899 : Reach 19899 := rs (se 1 (by rfl) ⟨14924, by rfl⟩) R29849
theorem R19913 : Reach 19913 := rs (se 2 (by rfl) ⟨7467, by rfl⟩) R14935
theorem R19959 : Reach 19959 := rs (se 1 (by rfl) ⟨14969, by rfl⟩) R29939
theorem R19975 : Reach 19975 := rs (se 1 (by rfl) ⟨14981, by rfl⟩) R29963
theorem R19983 : Reach 19983 := rs (se 1 (by rfl) ⟨14987, by rfl⟩) R29975
theorem R20011 : Reach 20011 := rs (se 1 (by rfl) ⟨15008, by rfl⟩) R30017
theorem R20027 : Reach 20027 := rs (se 1 (by rfl) ⟨15020, by rfl⟩) R30041
theorem R20087 : Reach 20087 := rs (se 1 (by rfl) ⟨15065, by rfl⟩) R30131
theorem R20111 : Reach 20111 := rs (se 1 (by rfl) ⟨15083, by rfl⟩) R30167
theorem R216755 : Reach 216755 := rs (se 1 (by rfl) ⟨162566, by rfl⟩) R325133
theorem R20153 : Reach 20153 := rs (se 2 (by rfl) ⟨7557, by rfl⟩) R15115
theorem R20155 : Reach 20155 := rs (se 1 (by rfl) ⟨15116, by rfl⟩) R30233
theorem R85697 : Reach 85697 := rs (se 2 (by rfl) ⟨32136, by rfl⟩) R64273
theorem R1199843 : Reach 1199843 := rs (se 1 (by rfl) ⟨899882, by rfl⟩) R1799765
theorem R52973 : Reach 52973 := rs (se 3 (by rfl) ⟨9932, by rfl⟩) R19865
theorem R20231 : Reach 20231 := rs (se 1 (by rfl) ⟨15173, by rfl⟩) R30347
theorem R20267 : Reach 20267 := rs (se 1 (by rfl) ⟨15200, by rfl⟩) R30401
theorem R118691 : Reach 118691 := rs (se 1 (by rfl) ⟨89018, by rfl⟩) R178037
theorem R20425 : Reach 20425 := rs (se 2 (by rfl) ⟨7659, by rfl⟩) R15319
theorem R20495 : Reach 20495 := rs (se 1 (by rfl) ⟨15371, by rfl⟩) R30743
theorem R20615 : Reach 20615 := rs (se 1 (by rfl) ⟨15461, by rfl⟩) R30923
theorem R20665 : Reach 20665 := rs (se 2 (by rfl) ⟨7749, by rfl⟩) R15499
theorem R20681 : Reach 20681 := rs (se 2 (by rfl) ⟨7755, by rfl⟩) R15511
theorem R20795 : Reach 20795 := rs (se 1 (by rfl) ⟨15596, by rfl⟩) R31193
theorem R20855 : Reach 20855 := rs (se 1 (by rfl) ⟨15641, by rfl⟩) R31283
theorem R20921 : Reach 20921 := rs (se 2 (by rfl) ⟨7845, by rfl⟩) R15691
theorem R21035 : Reach 21035 := rs (se 1 (by rfl) ⟨15776, by rfl⟩) R31553
theorem R53821 : Reach 53821 := rs (se 3 (by rfl) ⟨10091, by rfl⟩) R20183
theorem R21127 : Reach 21127 := rs (se 1 (by rfl) ⟨15845, by rfl⟩) R31691
theorem R21263 : Reach 21263 := rs (se 1 (by rfl) ⟨15947, by rfl⟩) R31895
theorem R21307 : Reach 21307 := rs (se 1 (by rfl) ⟨15980, by rfl⟩) R31961
theorem R21383 : Reach 21383 := rs (se 1 (by rfl) ⟨16037, by rfl⟩) R32075
theorem R21433 : Reach 21433 := rs (se 2 (by rfl) ⟨8037, by rfl⟩) R16075
theorem R21449 : Reach 21449 := rs (se 2 (by rfl) ⟨8043, by rfl⟩) R16087
theorem R54283 : Reach 54283 := rs (se 1 (by rfl) ⟨40712, by rfl⟩) R81425
theorem R21563 : Reach 21563 := rs (se 1 (by rfl) ⟨16172, by rfl⟩) R32345
theorem R21623 : Reach 21623 := rs (se 1 (by rfl) ⟨16217, by rfl⟩) R32435
theorem R54391 : Reach 54391 := rs (se 1 (by rfl) ⟨40793, by rfl⟩) R81587
theorem R21689 : Reach 21689 := rs (se 2 (by rfl) ⟨8133, by rfl⟩) R16267
theorem R21775 : Reach 21775 := rs (se 1 (by rfl) ⟨16331, by rfl⟩) R32663
theorem R21803 : Reach 21803 := rs (se 1 (by rfl) ⟨16352, by rfl⟩) R32705
theorem R21961 : Reach 21961 := rs (se 2 (by rfl) ⟨8235, by rfl⟩) R16471
theorem R54737 : Reach 54737 := rs (se 2 (by rfl) ⟨20526, by rfl⟩) R41053
theorem R22031 : Reach 22031 := rs (se 1 (by rfl) ⟨16523, by rfl⟩) R33047
theorem R54827 : Reach 54827 := rs (se 1 (by rfl) ⟨41120, by rfl⟩) R82241
theorem R22135 : Reach 22135 := rs (se 1 (by rfl) ⟨16601, by rfl⟩) R33203
theorem R22151 : Reach 22151 := rs (se 1 (by rfl) ⟨16613, by rfl⟩) R33227
theorem R22217 : Reach 22217 := rs (se 2 (by rfl) ⟨8331, by rfl⟩) R16663
theorem R55055 : Reach 55055 := rs (se 1 (by rfl) ⟨41291, by rfl⟩) R82583
theorem R22315 : Reach 22315 := rs (se 1 (by rfl) ⟨16736, by rfl⟩) R33473
theorem R22331 : Reach 22331 := rs (se 1 (by rfl) ⟨16748, by rfl⟩) R33497
theorem R22391 : Reach 22391 := rs (se 1 (by rfl) ⟨16793, by rfl⟩) R33587
theorem R55175 : Reach 55175 := rs (se 1 (by rfl) ⟨41381, by rfl⟩) R82763
theorem R55187 : Reach 55187 := rs (se 1 (by rfl) ⟨41390, by rfl⟩) R82781
theorem R22457 : Reach 22457 := rs (se 2 (by rfl) ⟨8421, by rfl⟩) R16843
theorem R22571 : Reach 22571 := rs (se 1 (by rfl) ⟨16928, by rfl⟩) R33857
theorem R252173 : Reach 252173 := rs (se 3 (by rfl) ⟨47282, by rfl⟩) R94565
theorem R22799 : Reach 22799 := rs (se 1 (by rfl) ⟨17099, by rfl⟩) R34199
theorem R22817 : Reach 22817 := rs (se 2 (by rfl) ⟨8556, by rfl⟩) R17113
theorem R55667 : Reach 55667 := rs (se 1 (by rfl) ⟨41750, by rfl⟩) R83501
theorem R22919 : Reach 22919 := rs (se 1 (by rfl) ⟨17189, by rfl⟩) R34379
theorem R22931 : Reach 22931 := rs (se 1 (by rfl) ⟨17198, by rfl⟩) R34397
theorem R22985 : Reach 22985 := rs (se 2 (by rfl) ⟨8619, by rfl⟩) R17239
theorem R154061 : Reach 154061 := rs (se 3 (by rfl) ⟨28886, by rfl⟩) R57773
theorem R383453 : Reach 383453 := rs (se 3 (by rfl) ⟨71897, by rfl⟩) R143795
theorem R23099 : Reach 23099 := rs (se 1 (by rfl) ⟨17324, by rfl⟩) R34649
theorem R23159 : Reach 23159 := rs (se 1 (by rfl) ⟨17369, by rfl⟩) R34739
theorem R23225 : Reach 23225 := rs (se 2 (by rfl) ⟨8709, by rfl⟩) R17419
theorem R56065 : Reach 56065 := rs (se 2 (by rfl) ⟨21024, by rfl⟩) R42049
theorem R88847 : Reach 88847 := rs (se 1 (by rfl) ⟨66635, by rfl⟩) R133271
theorem R23339 : Reach 23339 := rs (se 1 (by rfl) ⟨17504, by rfl⟩) R35009
theorem R88883 : Reach 88883 := rs (se 1 (by rfl) ⟨66662, by rfl⟩) R133325
theorem R56123 : Reach 56123 := rs (se 1 (by rfl) ⟨42092, by rfl⟩) R84185
theorem R121675 : Reach 121675 := rs (se 1 (by rfl) ⟨91256, by rfl⟩) R182513
theorem R154457 : Reach 154457 := rs (se 2 (by rfl) ⟨57921, by rfl⟩) R115843
theorem R23431 : Reach 23431 := rs (se 1 (by rfl) ⟨17573, by rfl⟩) R35147
theorem R89099 : Reach 89099 := rs (se 1 (by rfl) ⟨66824, by rfl⟩) R133649
theorem R23567 : Reach 23567 := rs (se 1 (by rfl) ⟨17675, by rfl⟩) R35351
theorem R23585 : Reach 23585 := rs (se 2 (by rfl) ⟨8844, by rfl⟩) R17689
theorem R23611 : Reach 23611 := rs (se 1 (by rfl) ⟨17708, by rfl⟩) R35417
theorem R23687 : Reach 23687 := rs (se 1 (by rfl) ⟨17765, by rfl⟩) R35531
theorem R23699 : Reach 23699 := rs (se 1 (by rfl) ⟨17774, by rfl⟩) R35549
theorem R89261 : Reach 89261 := rs (se 3 (by rfl) ⟨16736, by rfl⟩) R33473
theorem R23753 : Reach 23753 := rs (se 2 (by rfl) ⟨8907, by rfl⟩) R17815
theorem R56591 : Reach 56591 := rs (se 1 (by rfl) ⟨42443, by rfl⟩) R84887
theorem R23867 : Reach 23867 := rs (se 1 (by rfl) ⟨17900, by rfl⟩) R35801
theorem R23927 : Reach 23927 := rs (se 1 (by rfl) ⟨17945, by rfl⟩) R35891
theorem R23993 : Reach 23993 := rs (se 2 (by rfl) ⟨8997, by rfl⟩) R17995
theorem R56861 : Reach 56861 := rs (se 3 (by rfl) ⟨10661, by rfl⟩) R21323
theorem R24097 : Reach 24097 := rs (se 2 (by rfl) ⟨9036, by rfl⟩) R18073
theorem R24107 : Reach 24107 := rs (se 1 (by rfl) ⟨18080, by rfl⟩) R36161
theorem R188081 : Reach 188081 := rs (se 2 (by rfl) ⟨70530, by rfl⟩) R141061
theorem R57089 : Reach 57089 := rs (se 2 (by rfl) ⟨21408, by rfl⟩) R42817
theorem R24335 : Reach 24335 := rs (se 1 (by rfl) ⟨18251, by rfl⟩) R36503
theorem R24353 : Reach 24353 := rs (se 2 (by rfl) ⟨9132, by rfl⟩) R18265
theorem R319301 : Reach 319301 := rs (se 4 (by rfl) ⟨29934, by rfl⟩) R59869
theorem R24455 : Reach 24455 := rs (se 1 (by rfl) ⟨18341, by rfl⟩) R36683
theorem R24467 : Reach 24467 := rs (se 1 (by rfl) ⟨18350, by rfl⟩) R36701
theorem R24521 : Reach 24521 := rs (se 2 (by rfl) ⟨9195, by rfl⟩) R18391
theorem R24619 : Reach 24619 := rs (se 1 (by rfl) ⟨18464, by rfl⟩) R36929
theorem R24635 : Reach 24635 := rs (se 1 (by rfl) ⟨18476, by rfl⟩) R36953
theorem R24695 : Reach 24695 := rs (se 1 (by rfl) ⟨18521, by rfl⟩) R37043
theorem R24761 : Reach 24761 := rs (se 2 (by rfl) ⟨9285, by rfl⟩) R18571
theorem R57581 : Reach 57581 := rs (se 3 (by rfl) ⟨10796, by rfl⟩) R21593
theorem R24875 : Reach 24875 := rs (se 1 (by rfl) ⟨18656, by rfl⟩) R37313
theorem R25103 : Reach 25103 := rs (se 1 (by rfl) ⟨18827, by rfl⟩) R37655
theorem R25121 : Reach 25121 := rs (se 2 (by rfl) ⟨9420, by rfl⟩) R18841
theorem R25223 : Reach 25223 := rs (se 1 (by rfl) ⟨18917, by rfl⟩) R37835
theorem R25235 : Reach 25235 := rs (se 1 (by rfl) ⟨18926, by rfl⟩) R37853
theorem R25289 : Reach 25289 := rs (se 2 (by rfl) ⟨9483, by rfl⟩) R18967
theorem R90881 : Reach 90881 := rs (se 2 (by rfl) ⟨34080, by rfl⟩) R68161
theorem R25403 : Reach 25403 := rs (se 1 (by rfl) ⟨19052, by rfl⟩) R38105
theorem R25463 : Reach 25463 := rs (se 1 (by rfl) ⟨19097, by rfl⟩) R38195
theorem R58259 : Reach 58259 := rs (se 1 (by rfl) ⟨43694, by rfl⟩) R87389
theorem R58265 : Reach 58265 := rs (se 2 (by rfl) ⟨21849, by rfl⟩) R43699
theorem R25529 : Reach 25529 := rs (se 2 (by rfl) ⟨9573, by rfl⟩) R19147
theorem R2057237 : Reach 2057237 := rs (se 6 (by rfl) ⟨48216, by rfl⟩) R96433
theorem R25643 : Reach 25643 := rs (se 1 (by rfl) ⟨19232, by rfl⟩) R38465
theorem R156917 : Reach 156917 := rs (se 5 (by rfl) ⟨7355, by rfl⟩) R14711
theorem R58639 : Reach 58639 := rs (se 1 (by rfl) ⟨43979, by rfl⟩) R87959
theorem R25871 : Reach 25871 := rs (se 1 (by rfl) ⟨19403, by rfl⟩) R38807
theorem R25889 : Reach 25889 := rs (se 2 (by rfl) ⟨9708, by rfl⟩) R19417
theorem R25991 : Reach 25991 := rs (se 1 (by rfl) ⟨19493, by rfl⟩) R38987
theorem R26003 : Reach 26003 := rs (se 1 (by rfl) ⟨19502, by rfl⟩) R39005
theorem R26041 : Reach 26041 := rs (se 2 (by rfl) ⟨9765, by rfl⟩) R19531
theorem R26057 : Reach 26057 := rs (se 2 (by rfl) ⟨9771, by rfl⟩) R19543
theorem R91691 : Reach 91691 := rs (se 1 (by rfl) ⟨68768, by rfl⟩) R137537
theorem R26171 : Reach 26171 := rs (se 1 (by rfl) ⟨19628, by rfl⟩) R39257
theorem R58967 : Reach 58967 := rs (se 1 (by rfl) ⟨44225, by rfl⟩) R88451
theorem R26231 : Reach 26231 := rs (se 1 (by rfl) ⟨19673, by rfl⟩) R39347
theorem R26297 : Reach 26297 := rs (se 2 (by rfl) ⟨9861, by rfl⟩) R19723
theorem R26411 : Reach 26411 := rs (se 1 (by rfl) ⟨19808, by rfl⟩) R39617
theorem R157643 : Reach 157643 := rs (se 1 (by rfl) ⟨118232, by rfl⟩) R236465
theorem R59345 : Reach 59345 := rs (se 2 (by rfl) ⟨22254, by rfl⟩) R44509
theorem R26639 : Reach 26639 := rs (se 1 (by rfl) ⟨19979, by rfl⟩) R39959
theorem R26657 : Reach 26657 := rs (se 2 (by rfl) ⟨9996, by rfl⟩) R19993
theorem R59453 : Reach 59453 := rs (se 3 (by rfl) ⟨11147, by rfl⟩) R22295
theorem R59459 : Reach 59459 := rs (se 1 (by rfl) ⟨44594, by rfl⟩) R89189
theorem R26743 : Reach 26743 := rs (se 1 (by rfl) ⟨20057, by rfl⟩) R40115
theorem R26759 : Reach 26759 := rs (se 1 (by rfl) ⟨20069, by rfl⟩) R40139
theorem R26771 : Reach 26771 := rs (se 1 (by rfl) ⟨20078, by rfl⟩) R40157
theorem R26825 : Reach 26825 := rs (se 2 (by rfl) ⟨10059, by rfl⟩) R20119
theorem R26939 : Reach 26939 := rs (se 1 (by rfl) ⟨20204, by rfl⟩) R40409
theorem R26999 : Reach 26999 := rs (se 1 (by rfl) ⟨20249, by rfl⟩) R40499
theorem R27065 : Reach 27065 := rs (se 2 (by rfl) ⟨10149, by rfl⟩) R20299
theorem R59915 : Reach 59915 := rs (se 1 (by rfl) ⟨44936, by rfl⟩) R89873
theorem R27179 : Reach 27179 := rs (se 1 (by rfl) ⟨20384, by rfl⟩) R40769
theorem R27283 : Reach 27283 := rs (se 1 (by rfl) ⟨20462, by rfl⟩) R40925
theorem R27337 : Reach 27337 := rs (se 2 (by rfl) ⟨10251, by rfl⟩) R20503
theorem R27407 : Reach 27407 := rs (se 1 (by rfl) ⟨20555, by rfl⟩) R41111
theorem R27425 : Reach 27425 := rs (se 2 (by rfl) ⟨10284, by rfl⟩) R20569
theorem R27527 : Reach 27527 := rs (se 1 (by rfl) ⟨20645, by rfl⟩) R41291
theorem R27539 : Reach 27539 := rs (se 1 (by rfl) ⟨20654, by rfl⟩) R41309
theorem R27577 : Reach 27577 := rs (se 2 (by rfl) ⟨10341, by rfl⟩) R20683
theorem R27593 : Reach 27593 := rs (se 2 (by rfl) ⟨10347, by rfl⟩) R20695
theorem R27707 : Reach 27707 := rs (se 1 (by rfl) ⟨20780, by rfl⟩) R41561
theorem R27767 : Reach 27767 := rs (se 1 (by rfl) ⟨20825, by rfl⟩) R41651
theorem R27833 : Reach 27833 := rs (se 2 (by rfl) ⟨10437, by rfl⟩) R20875
theorem R158921 : Reach 158921 := rs (se 2 (by rfl) ⟨59595, by rfl⟩) R119191
theorem R93473 : Reach 93473 := rs (se 2 (by rfl) ⟨35052, by rfl⟩) R70105
theorem R27947 : Reach 27947 := rs (se 1 (by rfl) ⟨20960, by rfl⟩) R41921
theorem R28039 : Reach 28039 := rs (se 1 (by rfl) ⟨21029, by rfl⟩) R42059
theorem R60857 : Reach 60857 := rs (se 2 (by rfl) ⟨22821, by rfl⟩) R45643
theorem R93649 : Reach 93649 := rs (se 2 (by rfl) ⟨35118, by rfl⟩) R70237
theorem R28175 : Reach 28175 := rs (se 1 (by rfl) ⟨21131, by rfl⟩) R42263
theorem R28193 : Reach 28193 := rs (se 2 (by rfl) ⟨10572, by rfl⟩) R21145
theorem R28279 : Reach 28279 := rs (se 1 (by rfl) ⟨21209, by rfl⟩) R42419
theorem R28295 : Reach 28295 := rs (se 1 (by rfl) ⟨21221, by rfl⟩) R42443
theorem R28307 : Reach 28307 := rs (se 1 (by rfl) ⟨21230, by rfl⟩) R42461
theorem R28361 : Reach 28361 := rs (se 2 (by rfl) ⟨10635, by rfl⟩) R21271
theorem R61199 : Reach 61199 := rs (se 1 (by rfl) ⟨45899, by rfl⟩) R91799
theorem R61235 : Reach 61235 := rs (se 1 (by rfl) ⟨45926, by rfl⟩) R91853
theorem R28475 : Reach 28475 := rs (se 1 (by rfl) ⟨21356, by rfl⟩) R42713
theorem R28535 : Reach 28535 := rs (se 1 (by rfl) ⟨21401, by rfl⟩) R42803
theorem R28601 : Reach 28601 := rs (se 2 (by rfl) ⟨10725, by rfl⟩) R21451
theorem R61451 : Reach 61451 := rs (se 1 (by rfl) ⟨46088, by rfl⟩) R92177
theorem R28687 : Reach 28687 := rs (se 1 (by rfl) ⟨21515, by rfl⟩) R43031
theorem R258065 : Reach 258065 := rs (se 2 (by rfl) ⟨96774, by rfl⟩) R193549
theorem R28715 : Reach 28715 := rs (se 1 (by rfl) ⟨21536, by rfl⟩) R43073
theorem R127037 : Reach 127037 := rs (se 3 (by rfl) ⟨23819, by rfl⟩) R47639
theorem R61559 : Reach 61559 := rs (se 1 (by rfl) ⟨46169, by rfl⟩) R92339
theorem R61613 : Reach 61613 := rs (se 3 (by rfl) ⟨11552, by rfl⟩) R23105
theorem R94445 : Reach 94445 := rs (se 3 (by rfl) ⟨17708, by rfl⟩) R35417
theorem R28943 : Reach 28943 := rs (se 1 (by rfl) ⟨21707, by rfl⟩) R43415
theorem R28961 : Reach 28961 := rs (se 2 (by rfl) ⟨10860, by rfl⟩) R21721
theorem R127325 : Reach 127325 := rs (se 3 (by rfl) ⟨23873, by rfl⟩) R47747
theorem R29063 : Reach 29063 := rs (se 1 (by rfl) ⟨21797, by rfl⟩) R43595
theorem R61843 : Reach 61843 := rs (se 1 (by rfl) ⟨46382, by rfl⟩) R92765
theorem R29075 : Reach 29075 := rs (se 1 (by rfl) ⟨21806, by rfl⟩) R43613
theorem R29129 : Reach 29129 := rs (se 2 (by rfl) ⟨10923, by rfl⟩) R21847
theorem R61955 : Reach 61955 := rs (se 1 (by rfl) ⟨46466, by rfl⟩) R92933
theorem R29227 : Reach 29227 := rs (se 1 (by rfl) ⟨21920, by rfl⟩) R43841
theorem R29243 : Reach 29243 := rs (se 1 (by rfl) ⟨21932, by rfl⟩) R43865
theorem R29303 : Reach 29303 := rs (se 1 (by rfl) ⟨21977, by rfl⟩) R43955
theorem R29369 : Reach 29369 := rs (se 2 (by rfl) ⟨11013, by rfl⟩) R22027
theorem R62153 : Reach 62153 := rs (se 2 (by rfl) ⟨23307, by rfl⟩) R46615
theorem R29483 : Reach 29483 := rs (se 1 (by rfl) ⟨22112, by rfl⟩) R44225
theorem R488369 : Reach 488369 := rs (se 2 (by rfl) ⟨183138, by rfl⟩) R366277
theorem R29641 : Reach 29641 := rs (se 2 (by rfl) ⟨11115, by rfl⟩) R22231
theorem R29711 : Reach 29711 := rs (se 1 (by rfl) ⟨22283, by rfl⟩) R44567
theorem R95255 : Reach 95255 := rs (se 1 (by rfl) ⟨71441, by rfl⟩) R142883
theorem R29729 : Reach 29729 := rs (se 2 (by rfl) ⟨11148, by rfl⟩) R22297
theorem R62531 : Reach 62531 := rs (se 1 (by rfl) ⟨46898, by rfl⟩) R93797
theorem R29831 : Reach 29831 := rs (se 1 (by rfl) ⟨22373, by rfl⟩) R44747
theorem R29843 : Reach 29843 := rs (se 1 (by rfl) ⟨22382, by rfl⟩) R44765
theorem R29897 : Reach 29897 := rs (se 2 (by rfl) ⟨11211, by rfl⟩) R22423
theorem R30071 : Reach 30071 := rs (se 1 (by rfl) ⟨22553, by rfl⟩) R45107
theorem R62855 : Reach 62855 := rs (se 1 (by rfl) ⟨47141, by rfl⟩) R94283
theorem R30223 : Reach 30223 := rs (se 1 (by rfl) ⟨22667, by rfl⟩) R45335
theorem R95863 : Reach 95863 := rs (se 1 (by rfl) ⟨71897, by rfl⟩) R143795
theorem R63233 : Reach 63233 := rs (se 2 (by rfl) ⟨23712, by rfl⟩) R47425
theorem R30523 : Reach 30523 := rs (se 1 (by rfl) ⟨22892, by rfl⟩) R45785
theorem R30599 : Reach 30599 := rs (se 1 (by rfl) ⟨22949, by rfl⟩) R45899
theorem R30611 : Reach 30611 := rs (se 1 (by rfl) ⟨22958, by rfl⟩) R45917
theorem R30617 : Reach 30617 := rs (se 2 (by rfl) ⟨11481, by rfl⟩) R22963
theorem R30649 : Reach 30649 := rs (se 2 (by rfl) ⟨11493, by rfl⟩) R22987
theorem R30665 : Reach 30665 := rs (se 2 (by rfl) ⟨11499, by rfl⟩) R22999
theorem R30721 : Reach 30721 := rs (se 2 (by rfl) ⟨11520, by rfl⟩) R23041
theorem R161797 : Reach 161797 := rs (se 4 (by rfl) ⟨15168, by rfl⟩) R30337
theorem R161837 : Reach 161837 := rs (se 3 (by rfl) ⟨30344, by rfl⟩) R60689
theorem R30779 : Reach 30779 := rs (se 1 (by rfl) ⟨23084, by rfl⟩) R46169
theorem R63575 : Reach 63575 := rs (se 1 (by rfl) ⟨47681, by rfl⟩) R95363
theorem R96389 : Reach 96389 := rs (se 4 (by rfl) ⟨9036, by rfl⟩) R18073
theorem R30905 : Reach 30905 := rs (se 2 (by rfl) ⟨11589, by rfl⟩) R23179
theorem R30977 : Reach 30977 := rs (se 2 (by rfl) ⟨11616, by rfl⟩) R23233
theorem R31009 : Reach 31009 := rs (se 2 (by rfl) ⟨11628, by rfl⟩) R23257
theorem R31063 : Reach 31063 := rs (se 1 (by rfl) ⟨23297, by rfl⟩) R46595
theorem R326105 : Reach 326105 := rs (se 2 (by rfl) ⟨122289, by rfl⟩) R244579
theorem R31247 : Reach 31247 := rs (se 1 (by rfl) ⟨23435, by rfl⟩) R46871
theorem R31265 : Reach 31265 := rs (se 2 (by rfl) ⟨11724, by rfl⟩) R23449
theorem R64043 : Reach 64043 := rs (se 1 (by rfl) ⟨48032, by rfl⟩) R96065
theorem R64061 : Reach 64061 := rs (se 3 (by rfl) ⟨12011, by rfl⟩) R24023
theorem R195139 : Reach 195139 := rs (se 1 (by rfl) ⟨146354, by rfl⟩) R292709
theorem R31319 : Reach 31319 := rs (se 1 (by rfl) ⟨23489, by rfl⟩) R46979
theorem R31351 : Reach 31351 := rs (se 1 (by rfl) ⟨23513, by rfl⟩) R47027
theorem R31367 : Reach 31367 := rs (se 1 (by rfl) ⟨23525, by rfl⟩) R47051
theorem R359129 : Reach 359129 := rs (se 2 (by rfl) ⟨134673, by rfl⟩) R269347
theorem R31499 : Reach 31499 := rs (se 1 (by rfl) ⟨23624, by rfl⟩) R47249
theorem R97139 : Reach 97139 := rs (se 1 (by rfl) ⟨72854, by rfl⟩) R145709
theorem R31603 : Reach 31603 := rs (se 1 (by rfl) ⟨23702, by rfl⟩) R47405
theorem R31607 : Reach 31607 := rs (se 1 (by rfl) ⟨23705, by rfl⟩) R47411
theorem R31745 : Reach 31745 := rs (se 2 (by rfl) ⟨11904, by rfl⟩) R23809
theorem R31787 : Reach 31787 := rs (se 1 (by rfl) ⟨23840, by rfl⟩) R47681
theorem R31859 : Reach 31859 := rs (se 1 (by rfl) ⟨23894, by rfl⟩) R47789
theorem R32015 : Reach 32015 := rs (se 1 (by rfl) ⟨24011, by rfl⟩) R48023
theorem R32059 : Reach 32059 := rs (se 1 (by rfl) ⟨24044, by rfl⟩) R48089
theorem R97595 : Reach 97595 := rs (se 1 (by rfl) ⟨73196, by rfl⟩) R146393
theorem R32147 : Reach 32147 := rs (se 1 (by rfl) ⟨24110, by rfl⟩) R48221
theorem R32201 : Reach 32201 := rs (se 2 (by rfl) ⟨12075, by rfl⟩) R24151
theorem R32555 : Reach 32555 := rs (se 1 (by rfl) ⟨24416, by rfl⟩) R48833
theorem R65339 : Reach 65339 := rs (se 1 (by rfl) ⟨49004, by rfl⟩) R98009
theorem R32665 : Reach 32665 := rs (se 2 (by rfl) ⟨12249, by rfl⟩) R24499
theorem R393113 : Reach 393113 := rs (se 2 (by rfl) ⟨147417, by rfl⟩) R294835
theorem R65501 : Reach 65501 := rs (se 3 (by rfl) ⟨12281, by rfl⟩) R24563
theorem R98333 : Reach 98333 := rs (se 3 (by rfl) ⟨18437, by rfl⟩) R36875
theorem R32825 : Reach 32825 := rs (se 2 (by rfl) ⟨12309, by rfl⟩) R24619
theorem R32939 : Reach 32939 := rs (se 1 (by rfl) ⟨24704, by rfl⟩) R49409
theorem R98621 : Reach 98621 := rs (se 3 (by rfl) ⟨18491, by rfl⟩) R36983
theorem R65879 : Reach 65879 := rs (se 1 (by rfl) ⟨49409, by rfl⟩) R98819
theorem R98825 : Reach 98825 := rs (se 2 (by rfl) ⟨37059, by rfl⟩) R74119
theorem R33419 : Reach 33419 := rs (se 1 (by rfl) ⟨25064, by rfl⟩) R50129
theorem R33479 : Reach 33479 := rs (se 1 (by rfl) ⟨25109, by rfl⟩) R50219
theorem R66257 : Reach 66257 := rs (se 2 (by rfl) ⟨24846, by rfl⟩) R49693
theorem R164915 : Reach 164915 := rs (se 1 (by rfl) ⟨123686, by rfl⟩) R247373
theorem R132313 : Reach 132313 := rs (se 2 (by rfl) ⟨49617, by rfl⟩) R99235
theorem R66959 : Reach 66959 := rs (se 1 (by rfl) ⟨50219, by rfl⟩) R100439
theorem R34343 : Reach 34343 := rs (se 1 (by rfl) ⟨25757, by rfl⟩) R51515
theorem R34427 : Reach 34427 := rs (se 1 (by rfl) ⟨25820, by rfl⟩) R51641
theorem R100055 : Reach 100055 := rs (se 1 (by rfl) ⟨75041, by rfl⟩) R150083
theorem R34667 : Reach 34667 := rs (se 1 (by rfl) ⟨26000, by rfl⟩) R52001
theorem R34721 : Reach 34721 := rs (se 2 (by rfl) ⟨13020, by rfl⟩) R26041
theorem R133123 : Reach 133123 := rs (se 1 (by rfl) ⟨99842, by rfl⟩) R199685
theorem R34895 : Reach 34895 := rs (se 1 (by rfl) ⟨26171, by rfl⟩) R52343
theorem R34973 : Reach 34973 := rs (se 3 (by rfl) ⟨6557, by rfl⟩) R13115
theorem R35063 : Reach 35063 := rs (se 1 (by rfl) ⟨26297, by rfl⟩) R52595
theorem R133613 : Reach 133613 := rs (se 3 (by rfl) ⟨25052, by rfl⟩) R50105
theorem R35315 : Reach 35315 := rs (se 1 (by rfl) ⟨26486, by rfl⟩) R52973
theorem R494261 : Reach 494261 := rs (se 5 (by rfl) ⟨23168, by rfl⟩) R46337
theorem R35657 : Reach 35657 := rs (se 2 (by rfl) ⟨13371, by rfl⟩) R26743
theorem R68687 : Reach 68687 := rs (se 1 (by rfl) ⟨51515, by rfl⟩) R103031
theorem R363809 : Reach 363809 := rs (se 2 (by rfl) ⟨136428, by rfl⟩) R272857
theorem R36377 : Reach 36377 := rs (se 2 (by rfl) ⟨13641, by rfl⟩) R27283
theorem R36449 : Reach 36449 := rs (se 2 (by rfl) ⟨13668, by rfl⟩) R27337
theorem R36541 : Reach 36541 := rs (se 3 (by rfl) ⟨6851, by rfl⟩) R13703
theorem R36551 : Reach 36551 := rs (se 1 (by rfl) ⟨27413, by rfl⟩) R54827
theorem R69335 : Reach 69335 := rs (se 1 (by rfl) ⟨52001, by rfl⟩) R104003
theorem R69443 : Reach 69443 := rs (se 1 (by rfl) ⟨52082, by rfl⟩) R104165
theorem R36703 : Reach 36703 := rs (se 1 (by rfl) ⟨27527, by rfl⟩) R55055
theorem R135047 : Reach 135047 := rs (se 1 (by rfl) ⟨101285, by rfl⟩) R202571
theorem R36769 : Reach 36769 := rs (se 2 (by rfl) ⟨13788, by rfl⟩) R27577
theorem R36791 : Reach 36791 := rs (se 1 (by rfl) ⟨27593, by rfl⟩) R55187
theorem R102329 : Reach 102329 := rs (se 2 (by rfl) ⟨38373, by rfl⟩) R76747
theorem R168115 : Reach 168115 := rs (se 1 (by rfl) ⟨126086, by rfl⟩) R252173
theorem R37111 : Reach 37111 := rs (se 1 (by rfl) ⟨27833, by rfl⟩) R55667
theorem R102707 : Reach 102707 := rs (se 1 (by rfl) ⟨77030, by rfl⟩) R154061
theorem R37385 : Reach 37385 := rs (se 2 (by rfl) ⟨14019, by rfl⟩) R28039
theorem R37415 : Reach 37415 := rs (se 1 (by rfl) ⟨28061, by rfl⟩) R56123
theorem R102971 : Reach 102971 := rs (se 1 (by rfl) ⟨77228, by rfl⟩) R154457
theorem R103085 : Reach 103085 := rs (se 3 (by rfl) ⟨19328, by rfl⟩) R38657
theorem R37565 : Reach 37565 := rs (se 3 (by rfl) ⟨7043, by rfl⟩) R14087
theorem R70429 : Reach 70429 := rs (se 3 (by rfl) ⟨13205, by rfl⟩) R26411
theorem R37705 : Reach 37705 := rs (se 2 (by rfl) ⟨14139, by rfl⟩) R28279
theorem R37727 : Reach 37727 := rs (se 1 (by rfl) ⟨28295, by rfl⟩) R56591
theorem R37907 : Reach 37907 := rs (se 1 (by rfl) ⟨28430, by rfl⟩) R56861
theorem R38045 : Reach 38045 := rs (se 3 (by rfl) ⟨7133, by rfl⟩) R14267
theorem R38059 : Reach 38059 := rs (se 1 (by rfl) ⟨28544, by rfl⟩) R57089
theorem R38249 : Reach 38249 := rs (se 2 (by rfl) ⟨14343, by rfl⟩) R28687
theorem R71077 : Reach 71077 := rs (se 4 (by rfl) ⟨6663, by rfl⟩) R13327
theorem R38387 : Reach 38387 := rs (se 1 (by rfl) ⟨28790, by rfl⟩) R57581
theorem R71491 : Reach 71491 := rs (se 1 (by rfl) ⟨53618, by rfl⟩) R107237
theorem R38839 : Reach 38839 := rs (se 1 (by rfl) ⟨29129, by rfl⟩) R58259
theorem R38843 : Reach 38843 := rs (se 1 (by rfl) ⟨29132, by rfl⟩) R58265
theorem R38969 : Reach 38969 := rs (se 2 (by rfl) ⟨14613, by rfl⟩) R29227
theorem R71761 : Reach 71761 := rs (se 2 (by rfl) ⟨26910, by rfl⟩) R53821
theorem R71837 : Reach 71837 := rs (se 3 (by rfl) ⟨13469, by rfl⟩) R26939
theorem R104611 : Reach 104611 := rs (se 1 (by rfl) ⟨78458, by rfl⟩) R156917
theorem R39293 : Reach 39293 := rs (se 3 (by rfl) ⟨7367, by rfl⟩) R14735
theorem R39311 : Reach 39311 := rs (se 1 (by rfl) ⟨29483, by rfl⟩) R58967
theorem R72251 : Reach 72251 := rs (se 1 (by rfl) ⟨54188, by rfl⟩) R108377
theorem R39521 : Reach 39521 := rs (se 2 (by rfl) ⟨14820, by rfl⟩) R29641
theorem R105095 : Reach 105095 := rs (se 1 (by rfl) ⟨78821, by rfl⟩) R157643
theorem R39563 : Reach 39563 := rs (se 1 (by rfl) ⟨29672, by rfl⟩) R59345
theorem R72377 : Reach 72377 := rs (se 2 (by rfl) ⟨27141, by rfl⟩) R54283
theorem R39635 : Reach 39635 := rs (se 1 (by rfl) ⟨29726, by rfl⟩) R59453
theorem R72521 : Reach 72521 := rs (se 2 (by rfl) ⟨27195, by rfl⟩) R54391
theorem R170981 : Reach 170981 := rs (se 4 (by rfl) ⟨16029, by rfl⟩) R32059
theorem R39943 : Reach 39943 := rs (se 1 (by rfl) ⟨29957, by rfl⟩) R59915
theorem R72899 : Reach 72899 := rs (se 1 (by rfl) ⟨54674, by rfl⟩) R109349
theorem R40297 : Reach 40297 := rs (se 2 (by rfl) ⟨15111, by rfl⟩) R30223
theorem R105947 : Reach 105947 := rs (se 1 (by rfl) ⟨79460, by rfl⟩) R158921
theorem R40571 : Reach 40571 := rs (se 1 (by rfl) ⟨30428, by rfl⟩) R60857
theorem R40697 : Reach 40697 := rs (se 2 (by rfl) ⟨15261, by rfl⟩) R30523
theorem R40733 : Reach 40733 := rs (se 3 (by rfl) ⟨7637, by rfl⟩) R15275
theorem R40799 : Reach 40799 := rs (se 1 (by rfl) ⟨30599, by rfl⟩) R61199
theorem R40823 : Reach 40823 := rs (se 1 (by rfl) ⟨30617, by rfl⟩) R61235
theorem R40865 : Reach 40865 := rs (se 2 (by rfl) ⟨15324, by rfl⟩) R30649
theorem R106433 : Reach 106433 := rs (se 2 (by rfl) ⟨39912, by rfl⟩) R79825
theorem R40961 : Reach 40961 := rs (se 2 (by rfl) ⟨15360, by rfl⟩) R30721
theorem R40967 : Reach 40967 := rs (se 1 (by rfl) ⟨30725, by rfl⟩) R61451
theorem R172043 : Reach 172043 := rs (se 1 (by rfl) ⟨129032, by rfl⟩) R258065
theorem R41039 : Reach 41039 := rs (se 1 (by rfl) ⟨30779, by rfl⟩) R61559
theorem R41075 : Reach 41075 := rs (se 1 (by rfl) ⟨30806, by rfl⟩) R61613
theorem R41303 : Reach 41303 := rs (se 1 (by rfl) ⟨30977, by rfl⟩) R61955
theorem R41345 : Reach 41345 := rs (se 2 (by rfl) ⟨15504, by rfl⟩) R31009
theorem R41417 : Reach 41417 := rs (se 2 (by rfl) ⟨15531, by rfl⟩) R31063
theorem R41435 : Reach 41435 := rs (se 1 (by rfl) ⟨31076, by rfl⟩) R62153
theorem R41687 : Reach 41687 := rs (se 1 (by rfl) ⟨31265, by rfl⟩) R62531
theorem R41801 : Reach 41801 := rs (se 2 (by rfl) ⟨15675, by rfl⟩) R31351
theorem R41903 : Reach 41903 := rs (se 1 (by rfl) ⟨31427, by rfl⟩) R62855
theorem R861131 : Reach 861131 := rs (se 1 (by rfl) ⟨645848, by rfl⟩) R1291697
theorem R74753 : Reach 74753 := rs (se 2 (by rfl) ⟨28032, by rfl⟩) R56065
theorem R74803 : Reach 74803 := rs (se 1 (by rfl) ⟨56102, by rfl⟩) R112205
theorem R42137 : Reach 42137 := rs (se 2 (by rfl) ⟨15801, by rfl⟩) R31603
theorem R42155 : Reach 42155 := rs (se 1 (by rfl) ⟨31616, by rfl⟩) R63233
theorem R107891 : Reach 107891 := rs (se 1 (by rfl) ⟨80918, by rfl⟩) R161837
theorem R42383 : Reach 42383 := rs (se 1 (by rfl) ⟨31787, by rfl⟩) R63575
theorem R75403 : Reach 75403 := rs (se 1 (by rfl) ⟨56552, by rfl⟩) R113105
theorem R42695 : Reach 42695 := rs (se 1 (by rfl) ⟨32021, by rfl⟩) R64043
theorem R42707 : Reach 42707 := rs (se 1 (by rfl) ⟨32030, by rfl⟩) R64061
theorem R75485 : Reach 75485 := rs (se 3 (by rfl) ⟨14153, by rfl⟩) R28307
theorem R239419 : Reach 239419 := rs (se 1 (by rfl) ⟨179564, by rfl⟩) R359129
theorem R43325 : Reach 43325 := rs (se 3 (by rfl) ⟨8123, by rfl⟩) R16247
theorem R43553 : Reach 43553 := rs (se 2 (by rfl) ⟨16332, by rfl⟩) R32665
theorem R43559 : Reach 43559 := rs (se 1 (by rfl) ⟨32669, by rfl⟩) R65339
theorem R76423 : Reach 76423 := rs (se 1 (by rfl) ⟨57317, by rfl⟩) R114635
theorem R43667 : Reach 43667 := rs (se 1 (by rfl) ⟨32750, by rfl⟩) R65501
theorem R43883 : Reach 43883 := rs (se 1 (by rfl) ⟨32912, by rfl⟩) R65825
theorem R43895 : Reach 43895 := rs (se 1 (by rfl) ⟨32921, by rfl⟩) R65843
theorem R43937 : Reach 43937 := rs (se 2 (by rfl) ⟨16476, by rfl⟩) R32953
theorem R76727 : Reach 76727 := rs (se 1 (by rfl) ⟨57545, by rfl⟩) R115091
theorem R44185 : Reach 44185 := rs (se 2 (by rfl) ⟨16569, by rfl⟩) R33139
theorem R44189 : Reach 44189 := rs (se 3 (by rfl) ⟨8285, by rfl⟩) R16571
theorem R44279 : Reach 44279 := rs (se 1 (by rfl) ⟨33209, by rfl⟩) R66419
theorem R44489 : Reach 44489 := rs (se 2 (by rfl) ⟨16683, by rfl⟩) R33367
theorem R44531 : Reach 44531 := rs (se 1 (by rfl) ⟨33398, by rfl⟩) R66797
theorem R44603 : Reach 44603 := rs (se 1 (by rfl) ⟨33452, by rfl⟩) R66905
theorem R77435 : Reach 77435 := rs (se 1 (by rfl) ⟨58076, by rfl⟩) R116153
theorem R44729 : Reach 44729 := rs (se 2 (by rfl) ⟨16773, by rfl⟩) R33547
theorem R44873 : Reach 44873 := rs (se 2 (by rfl) ⟨16827, by rfl⟩) R33655
theorem R44975 : Reach 44975 := rs (se 1 (by rfl) ⟨33731, by rfl⟩) R67463
theorem R78185 : Reach 78185 := rs (se 2 (by rfl) ⟨29319, by rfl⟩) R58639
theorem R111127 : Reach 111127 := rs (se 1 (by rfl) ⟨83345, by rfl⟩) R166691
theorem R45593 : Reach 45593 := rs (se 2 (by rfl) ⟨17097, by rfl⟩) R34195
theorem R12839 : Reach 12839 := rs (se 1 (by rfl) ⟨9629, by rfl⟩) R19259
theorem R12879 : Reach 12879 := rs (se 1 (by rfl) ⟨9659, by rfl⟩) R19319
theorem R12895 : Reach 12895 := rs (se 1 (by rfl) ⟨9671, by rfl⟩) R19343
theorem R12923 : Reach 12923 := rs (se 1 (by rfl) ⟨9692, by rfl⟩) R19385
theorem R12975 : Reach 12975 := rs (se 1 (by rfl) ⟨9731, by rfl⟩) R19463
theorem R12999 : Reach 12999 := rs (se 1 (by rfl) ⟨9749, by rfl⟩) R19499
theorem R13019 : Reach 13019 := rs (se 1 (by rfl) ⟨9764, by rfl⟩) R19529
theorem R13095 : Reach 13095 := rs (se 1 (by rfl) ⟨9821, by rfl⟩) R19643
theorem R13135 : Reach 13135 := rs (se 1 (by rfl) ⟨9851, by rfl⟩) R19703
theorem R13151 : Reach 13151 := rs (se 1 (by rfl) ⟨9863, by rfl⟩) R19727
theorem R13179 : Reach 13179 := rs (se 1 (by rfl) ⟨9884, by rfl⟩) R19769
theorem R13231 : Reach 13231 := rs (se 1 (by rfl) ⟨9923, by rfl⟩) R19847
theorem R46007 : Reach 46007 := rs (se 1 (by rfl) ⟨34505, by rfl⟩) R69011
theorem R13255 : Reach 13255 := rs (se 1 (by rfl) ⟨9941, by rfl⟩) R19883
theorem R13275 : Reach 13275 := rs (se 1 (by rfl) ⟨9956, by rfl⟩) R19913
theorem R13351 : Reach 13351 := rs (se 1 (by rfl) ⟨10013, by rfl⟩) R20027
theorem R13391 : Reach 13391 := rs (se 1 (by rfl) ⟨10043, by rfl⟩) R20087
theorem R13407 : Reach 13407 := rs (se 1 (by rfl) ⟨10055, by rfl⟩) R20111
theorem R144503 : Reach 144503 := rs (se 1 (by rfl) ⟨108377, by rfl⟩) R216755
theorem R13435 : Reach 13435 := rs (se 1 (by rfl) ⟨10076, by rfl⟩) R20153
theorem R799895 : Reach 799895 := rs (se 1 (by rfl) ⟨599921, by rfl⟩) R1199843
theorem R13487 : Reach 13487 := rs (se 1 (by rfl) ⟨10115, by rfl⟩) R20231
theorem R13511 : Reach 13511 := rs (se 1 (by rfl) ⟨10133, by rfl⟩) R20267
theorem R177353 : Reach 177353 := rs (se 2 (by rfl) ⟨66507, by rfl⟩) R133015
theorem R79127 : Reach 79127 := rs (se 1 (by rfl) ⟨59345, by rfl⟩) R118691
theorem R13663 : Reach 13663 := rs (se 1 (by rfl) ⟨10247, by rfl⟩) R20495
theorem R13743 : Reach 13743 := rs (se 1 (by rfl) ⟨10307, by rfl⟩) R20615
theorem R13787 : Reach 13787 := rs (se 1 (by rfl) ⟨10340, by rfl⟩) R20681
theorem R46601 : Reach 46601 := rs (se 2 (by rfl) ⟨17475, by rfl⟩) R34951
theorem R13863 : Reach 13863 := rs (se 1 (by rfl) ⟨10397, by rfl⟩) R20795
theorem R13903 : Reach 13903 := rs (se 1 (by rfl) ⟨10427, by rfl⟩) R20855
theorem R13947 : Reach 13947 := rs (se 1 (by rfl) ⟨10460, by rfl⟩) R20921
theorem R46727 : Reach 46727 := rs (se 1 (by rfl) ⟨35045, by rfl⟩) R70091
theorem R46777 : Reach 46777 := rs (se 2 (by rfl) ⟨17541, by rfl⟩) R35083
theorem R14023 : Reach 14023 := rs (se 1 (by rfl) ⟨10517, by rfl⟩) R21035
theorem R112427 : Reach 112427 := rs (se 1 (by rfl) ⟨84320, by rfl⟩) R168641
theorem R14175 : Reach 14175 := rs (se 1 (by rfl) ⟨10631, by rfl⟩) R21263
theorem R145313 : Reach 145313 := rs (se 2 (by rfl) ⟨54492, by rfl⟩) R108985
theorem R14255 : Reach 14255 := rs (se 1 (by rfl) ⟨10691, by rfl⟩) R21383
theorem R14299 : Reach 14299 := rs (se 1 (by rfl) ⟨10724, by rfl⟩) R21449
theorem R14375 : Reach 14375 := rs (se 1 (by rfl) ⟨10781, by rfl⟩) R21563
theorem R14415 : Reach 14415 := rs (se 1 (by rfl) ⟨10811, by rfl⟩) R21623
theorem R14459 : Reach 14459 := rs (se 1 (by rfl) ⟨10844, by rfl⟩) R21689
theorem R14535 : Reach 14535 := rs (se 1 (by rfl) ⟨10901, by rfl⟩) R21803
theorem R80189 : Reach 80189 := rs (se 3 (by rfl) ⟨15035, by rfl⟩) R30071
theorem R14687 : Reach 14687 := rs (se 1 (by rfl) ⟨11015, by rfl⟩) R22031
theorem R47465 : Reach 47465 := rs (se 2 (by rfl) ⟨17799, by rfl⟩) R35599
theorem R14767 : Reach 14767 := rs (se 1 (by rfl) ⟨11075, by rfl⟩) R22151
theorem R14811 : Reach 14811 := rs (se 1 (by rfl) ⟨11108, by rfl⟩) R22217
theorem R14887 : Reach 14887 := rs (se 1 (by rfl) ⟨11165, by rfl⟩) R22331
theorem R14927 : Reach 14927 := rs (se 1 (by rfl) ⟨11195, by rfl⟩) R22391
theorem R14971 : Reach 14971 := rs (se 1 (by rfl) ⟨11228, by rfl⟩) R22457
theorem R15047 : Reach 15047 := rs (se 1 (by rfl) ⟨11285, by rfl⟩) R22571
theorem R15199 : Reach 15199 := rs (se 1 (by rfl) ⟨11399, by rfl⟩) R22799
theorem R15211 : Reach 15211 := rs (se 1 (by rfl) ⟨11408, by rfl⟩) R22817
theorem R15279 : Reach 15279 := rs (se 1 (by rfl) ⟨11459, by rfl⟩) R22919
theorem R15287 : Reach 15287 := rs (se 1 (by rfl) ⟨11465, by rfl⟩) R22931
theorem R48055 : Reach 48055 := rs (se 1 (by rfl) ⟨36041, by rfl⟩) R72083
theorem R48059 : Reach 48059 := rs (se 1 (by rfl) ⟨36044, by rfl⟩) R72089
theorem R15323 : Reach 15323 := rs (se 1 (by rfl) ⟨11492, by rfl⟩) R22985
theorem R15399 : Reach 15399 := rs (se 1 (by rfl) ⟨11549, by rfl⟩) R23099
theorem R113707 : Reach 113707 := rs (se 1 (by rfl) ⟨85280, by rfl⟩) R170561
theorem R48185 : Reach 48185 := rs (se 2 (by rfl) ⟨18069, by rfl⟩) R36139
theorem R15439 : Reach 15439 := rs (se 1 (by rfl) ⟨11579, by rfl⟩) R23159
theorem R15483 : Reach 15483 := rs (se 1 (by rfl) ⟨11612, by rfl⟩) R23225
theorem R15559 : Reach 15559 := rs (se 1 (by rfl) ⟨11669, by rfl⟩) R23339
theorem R15711 : Reach 15711 := rs (se 1 (by rfl) ⟨11783, by rfl⟩) R23567
theorem R15723 : Reach 15723 := rs (se 1 (by rfl) ⟨11792, by rfl⟩) R23585
theorem R48509 : Reach 48509 := rs (se 3 (by rfl) ⟨9095, by rfl⟩) R18191
theorem R15791 : Reach 15791 := rs (se 1 (by rfl) ⟨11843, by rfl⟩) R23687
theorem R15799 : Reach 15799 := rs (se 1 (by rfl) ⟨11849, by rfl⟩) R23699
theorem R15835 : Reach 15835 := rs (se 1 (by rfl) ⟨11876, by rfl⟩) R23753
theorem R15911 : Reach 15911 := rs (se 1 (by rfl) ⟨11933, by rfl⟩) R23867
theorem R15951 : Reach 15951 := rs (se 1 (by rfl) ⟨11963, by rfl⟩) R23927
theorem R15995 : Reach 15995 := rs (se 1 (by rfl) ⟨11996, by rfl⟩) R23993
theorem R48775 : Reach 48775 := rs (se 1 (by rfl) ⟨36581, by rfl⟩) R73163
theorem R147133 : Reach 147133 := rs (se 3 (by rfl) ⟨27587, by rfl⟩) R55175
theorem R16071 : Reach 16071 := rs (se 1 (by rfl) ⟨12053, by rfl⟩) R24107
theorem R48851 : Reach 48851 := rs (se 1 (by rfl) ⟨36638, by rfl⟩) R73277
theorem R16223 : Reach 16223 := rs (se 1 (by rfl) ⟨12167, by rfl⟩) R24335
theorem R16235 : Reach 16235 := rs (se 1 (by rfl) ⟨12176, by rfl⟩) R24353
theorem R212867 : Reach 212867 := rs (se 1 (by rfl) ⟨159650, by rfl⟩) R319301
theorem R16303 : Reach 16303 := rs (se 1 (by rfl) ⟨12227, by rfl⟩) R24455
theorem R16311 : Reach 16311 := rs (se 1 (by rfl) ⟨12233, by rfl⟩) R24467
theorem R16347 : Reach 16347 := rs (se 1 (by rfl) ⟨12260, by rfl⟩) R24521
theorem R16423 : Reach 16423 := rs (se 1 (by rfl) ⟨12317, by rfl⟩) R24635
theorem R16463 : Reach 16463 := rs (se 1 (by rfl) ⟨12347, by rfl⟩) R24695
theorem R180305 : Reach 180305 := rs (se 2 (by rfl) ⟨67614, by rfl⟩) R135229
theorem R16507 : Reach 16507 := rs (se 1 (by rfl) ⟨12380, by rfl⟩) R24761
theorem R16583 : Reach 16583 := rs (se 1 (by rfl) ⟨12437, by rfl⟩) R24875
theorem R16735 : Reach 16735 := rs (se 1 (by rfl) ⟨12551, by rfl⟩) R25103
theorem R16747 : Reach 16747 := rs (se 1 (by rfl) ⟨12560, by rfl⟩) R25121
theorem R16815 : Reach 16815 := rs (se 1 (by rfl) ⟨12611, by rfl⟩) R25223
theorem R16823 : Reach 16823 := rs (se 1 (by rfl) ⟨12617, by rfl⟩) R25235
theorem R16859 : Reach 16859 := rs (se 1 (by rfl) ⟨12644, by rfl⟩) R25289
theorem R49673 : Reach 49673 := rs (se 2 (by rfl) ⟨18627, by rfl⟩) R37255
theorem R82457 : Reach 82457 := rs (se 2 (by rfl) ⟨30921, by rfl⟩) R61843
theorem R16935 : Reach 16935 := rs (se 1 (by rfl) ⟨12701, by rfl⟩) R25403
theorem R16975 : Reach 16975 := rs (se 1 (by rfl) ⟨12731, by rfl⟩) R25463
theorem R148085 : Reach 148085 := rs (se 5 (by rfl) ⟨6941, by rfl⟩) R13883
theorem R49787 : Reach 49787 := rs (se 1 (by rfl) ⟨37340, by rfl⟩) R74681
theorem R17019 : Reach 17019 := rs (se 1 (by rfl) ⟨12764, by rfl⟩) R25529
theorem R17095 : Reach 17095 := rs (se 1 (by rfl) ⟨12821, by rfl⟩) R25643
theorem R17145 : Reach 17145 := rs (se 2 (by rfl) ⟨6429, by rfl⟩) R12859
theorem R49949 : Reach 49949 := rs (se 3 (by rfl) ⟨9365, by rfl⟩) R18731
theorem R17247 : Reach 17247 := rs (se 1 (by rfl) ⟨12935, by rfl⟩) R25871
theorem R17257 : Reach 17257 := rs (se 2 (by rfl) ⟨6471, by rfl⟩) R12943
theorem R17259 : Reach 17259 := rs (se 1 (by rfl) ⟨12944, by rfl⟩) R25889
theorem R17327 : Reach 17327 := rs (se 1 (by rfl) ⟨12995, by rfl⟩) R25991
theorem R17335 : Reach 17335 := rs (se 1 (by rfl) ⟨13001, by rfl⟩) R26003
theorem R17371 : Reach 17371 := rs (se 1 (by rfl) ⟨13028, by rfl⟩) R26057
theorem R50183 : Reach 50183 := rs (se 1 (by rfl) ⟨37637, by rfl⟩) R75275
theorem R17417 : Reach 17417 := rs (se 2 (by rfl) ⟨6531, by rfl⟩) R13063
theorem R17447 : Reach 17447 := rs (se 1 (by rfl) ⟨13085, by rfl⟩) R26171
theorem R115763 : Reach 115763 := rs (se 1 (by rfl) ⟨86822, by rfl⟩) R173645
theorem R50233 : Reach 50233 := rs (se 2 (by rfl) ⟨18837, by rfl⟩) R37675
theorem R17487 : Reach 17487 := rs (se 1 (by rfl) ⟨13115, by rfl⟩) R26231
theorem R50291 : Reach 50291 := rs (se 1 (by rfl) ⟨37718, by rfl⟩) R75437
theorem R17531 : Reach 17531 := rs (se 1 (by rfl) ⟨13148, by rfl⟩) R26297
theorem R17607 : Reach 17607 := rs (se 1 (by rfl) ⟨13205, by rfl⟩) R26411
theorem R17657 : Reach 17657 := rs (se 2 (by rfl) ⟨6621, by rfl⟩) R13243
theorem R17759 : Reach 17759 := rs (se 1 (by rfl) ⟨13319, by rfl⟩) R26639
theorem R17769 : Reach 17769 := rs (se 2 (by rfl) ⟨6663, by rfl⟩) R13327
theorem R17771 : Reach 17771 := rs (se 1 (by rfl) ⟨13328, by rfl⟩) R26657
theorem R17839 : Reach 17839 := rs (se 1 (by rfl) ⟨13379, by rfl⟩) R26759
theorem R17847 : Reach 17847 := rs (se 1 (by rfl) ⟨13385, by rfl⟩) R26771
theorem R50651 : Reach 50651 := rs (se 1 (by rfl) ⟨37988, by rfl⟩) R75977
theorem R17883 : Reach 17883 := rs (se 1 (by rfl) ⟨13412, by rfl⟩) R26825
theorem R17929 : Reach 17929 := rs (se 2 (by rfl) ⟨6723, by rfl⟩) R13447
theorem R17959 : Reach 17959 := rs (se 1 (by rfl) ⟨13469, by rfl⟩) R26939
theorem R17999 : Reach 17999 := rs (se 1 (by rfl) ⟨13499, by rfl⟩) R26999
theorem R18043 : Reach 18043 := rs (se 1 (by rfl) ⟨13532, by rfl⟩) R27065
theorem R18119 : Reach 18119 := rs (se 1 (by rfl) ⟨13589, by rfl⟩) R27179
theorem R18169 : Reach 18169 := rs (se 2 (by rfl) ⟨6813, by rfl⟩) R13627
theorem R18271 : Reach 18271 := rs (se 1 (by rfl) ⟨13703, by rfl⟩) R27407
theorem R18281 : Reach 18281 := rs (se 2 (by rfl) ⟨6855, by rfl⟩) R13711
theorem R18283 : Reach 18283 := rs (se 1 (by rfl) ⟨13712, by rfl⟩) R27425
theorem R18351 : Reach 18351 := rs (se 1 (by rfl) ⟨13763, by rfl⟩) R27527
theorem R18359 : Reach 18359 := rs (se 1 (by rfl) ⟨13769, by rfl⟩) R27539
theorem R18395 : Reach 18395 := rs (se 1 (by rfl) ⟨13796, by rfl⟩) R27593
theorem R18441 : Reach 18441 := rs (se 2 (by rfl) ⟨6915, by rfl⟩) R13831
theorem R18471 : Reach 18471 := rs (se 1 (by rfl) ⟨13853, by rfl⟩) R27707
theorem R18511 : Reach 18511 := rs (se 1 (by rfl) ⟨13883, by rfl⟩) R27767
theorem R18555 : Reach 18555 := rs (se 1 (by rfl) ⟨13916, by rfl⟩) R27833
theorem R51353 : Reach 51353 := rs (se 2 (by rfl) ⟨19257, by rfl⟩) R38515
theorem R18631 : Reach 18631 := rs (se 1 (by rfl) ⟨13973, by rfl⟩) R27947
theorem R18681 : Reach 18681 := rs (se 2 (by rfl) ⟨7005, by rfl⟩) R14011
theorem R149809 : Reach 149809 := rs (se 2 (by rfl) ⟨56178, by rfl⟩) R112357
theorem R18783 : Reach 18783 := rs (se 1 (by rfl) ⟨14087, by rfl⟩) R28175
theorem R18793 : Reach 18793 := rs (se 2 (by rfl) ⟨7047, by rfl⟩) R14095
theorem R18795 : Reach 18795 := rs (se 1 (by rfl) ⟨14096, by rfl⟩) R28193
theorem R117125 : Reach 117125 := rs (se 4 (by rfl) ⟨10980, by rfl⟩) R21961
theorem R18863 : Reach 18863 := rs (se 1 (by rfl) ⟨14147, by rfl⟩) R28295
theorem R18871 : Reach 18871 := rs (se 1 (by rfl) ⟨14153, by rfl⟩) R28307
theorem R18907 : Reach 18907 := rs (se 1 (by rfl) ⟨14180, by rfl⟩) R28361
theorem R18953 : Reach 18953 := rs (se 2 (by rfl) ⟨7107, by rfl⟩) R14215
theorem R18983 : Reach 18983 := rs (se 1 (by rfl) ⟨14237, by rfl⟩) R28475
theorem R19023 : Reach 19023 := rs (se 1 (by rfl) ⟨14267, by rfl⟩) R28535
theorem R19067 : Reach 19067 := rs (se 1 (by rfl) ⟨14300, by rfl⟩) R28601
theorem R51835 : Reach 51835 := rs (se 1 (by rfl) ⟨38876, by rfl⟩) R77753
theorem R84653 : Reach 84653 := rs (se 3 (by rfl) ⟨15872, by rfl⟩) R31745
theorem R215729 : Reach 215729 := rs (se 2 (by rfl) ⟨80898, by rfl⟩) R161797
theorem R51911 : Reach 51911 := rs (se 1 (by rfl) ⟨38933, by rfl⟩) R77867
theorem R19143 : Reach 19143 := rs (se 1 (by rfl) ⟨14357, by rfl⟩) R28715
theorem R84691 : Reach 84691 := rs (se 1 (by rfl) ⟨63518, by rfl⟩) R127037
theorem R19193 : Reach 19193 := rs (se 2 (by rfl) ⟨7197, by rfl⟩) R14395
theorem R19295 : Reach 19295 := rs (se 1 (by rfl) ⟨14471, by rfl⟩) R28943
theorem R19305 : Reach 19305 := rs (se 2 (by rfl) ⟨7239, by rfl⟩) R14479
theorem R19307 : Reach 19307 := rs (se 1 (by rfl) ⟨14480, by rfl⟩) R28961
theorem R84883 : Reach 84883 := rs (se 1 (by rfl) ⟨63662, by rfl⟩) R127325
theorem R19375 : Reach 19375 := rs (se 1 (by rfl) ⟨14531, by rfl⟩) R29063
theorem R19383 : Reach 19383 := rs (se 1 (by rfl) ⟨14537, by rfl⟩) R29075
theorem R19419 : Reach 19419 := rs (se 1 (by rfl) ⟨14564, by rfl⟩) R29129
theorem R19465 : Reach 19465 := rs (se 2 (by rfl) ⟨7299, by rfl⟩) R14599
theorem R19495 : Reach 19495 := rs (se 1 (by rfl) ⟨14621, by rfl⟩) R29243
theorem R19535 : Reach 19535 := rs (se 1 (by rfl) ⟨14651, by rfl⟩) R29303
theorem R19579 : Reach 19579 := rs (se 1 (by rfl) ⟨14684, by rfl⟩) R29369
theorem R19655 : Reach 19655 := rs (se 1 (by rfl) ⟨14741, by rfl⟩) R29483
theorem R19705 : Reach 19705 := rs (se 2 (by rfl) ⟨7389, by rfl⟩) R14779
theorem R52541 : Reach 52541 := rs (se 3 (by rfl) ⟨9851, by rfl⟩) R19703
theorem R19807 : Reach 19807 := rs (se 1 (by rfl) ⟨14855, by rfl⟩) R29711
theorem R19817 : Reach 19817 := rs (se 2 (by rfl) ⟨7431, by rfl⟩) R14863
theorem R19819 : Reach 19819 := rs (se 1 (by rfl) ⟨14864, by rfl⟩) R29729
theorem R85373 : Reach 85373 := rs (se 3 (by rfl) ⟨16007, by rfl⟩) R32015
theorem R52609 : Reach 52609 := rs (se 2 (by rfl) ⟨19728, by rfl⟩) R39457
theorem R19887 : Reach 19887 := rs (se 1 (by rfl) ⟨14915, by rfl⟩) R29831
theorem R19895 : Reach 19895 := rs (se 1 (by rfl) ⟨14921, by rfl⟩) R29843
theorem R19931 : Reach 19931 := rs (se 1 (by rfl) ⟨14948, by rfl⟩) R29897
theorem R19977 : Reach 19977 := rs (se 2 (by rfl) ⟨7491, by rfl⟩) R14983
theorem R20047 : Reach 20047 := rs (se 1 (by rfl) ⟨15035, by rfl⟩) R30071
theorem R52883 : Reach 52883 := rs (se 1 (by rfl) ⟨39662, by rfl⟩) R79325
theorem R282329 : Reach 282329 := rs (se 2 (by rfl) ⟨105873, by rfl⟩) R211747
theorem R20297 : Reach 20297 := rs (se 2 (by rfl) ⟨7611, by rfl⟩) R15223
theorem R53111 : Reach 53111 := rs (se 1 (by rfl) ⟨39833, by rfl⟩) R79667
theorem R20399 : Reach 20399 := rs (se 1 (by rfl) ⟨15299, by rfl⟩) R30599
theorem R20407 : Reach 20407 := rs (se 1 (by rfl) ⟨15305, by rfl⟩) R30611
theorem R20411 : Reach 20411 := rs (se 1 (by rfl) ⟨15308, by rfl⟩) R30617
theorem R20443 : Reach 20443 := rs (se 1 (by rfl) ⟨15332, by rfl⟩) R30665
theorem R20489 : Reach 20489 := rs (se 2 (by rfl) ⟨7683, by rfl⟩) R15367
theorem R20519 : Reach 20519 := rs (se 1 (by rfl) ⟨15389, by rfl⟩) R30779
theorem R20537 : Reach 20537 := rs (se 2 (by rfl) ⟨7701, by rfl⟩) R15403
theorem R20603 : Reach 20603 := rs (se 1 (by rfl) ⟨15452, by rfl⟩) R30905
theorem R53405 : Reach 53405 := rs (se 3 (by rfl) ⟨10013, by rfl⟩) R20027
theorem R20651 : Reach 20651 := rs (se 1 (by rfl) ⟨15488, by rfl⟩) R30977
theorem R20729 : Reach 20729 := rs (se 2 (by rfl) ⟨7773, by rfl⟩) R15547
theorem R217403 : Reach 217403 := rs (se 1 (by rfl) ⟨163052, by rfl⟩) R326105
theorem R20831 : Reach 20831 := rs (se 1 (by rfl) ⟨15623, by rfl⟩) R31247
theorem R20843 : Reach 20843 := rs (se 1 (by rfl) ⟨15632, by rfl⟩) R31265
theorem R20879 : Reach 20879 := rs (se 1 (by rfl) ⟨15659, by rfl⟩) R31319
theorem R20911 : Reach 20911 := rs (se 1 (by rfl) ⟨15683, by rfl⟩) R31367
theorem R20999 : Reach 20999 := rs (se 1 (by rfl) ⟨15749, by rfl⟩) R31499
theorem R21001 : Reach 21001 := rs (se 2 (by rfl) ⟨7875, by rfl⟩) R15751
theorem R21071 : Reach 21071 := rs (se 1 (by rfl) ⟨15803, by rfl⟩) R31607
theorem R21163 : Reach 21163 := rs (se 1 (by rfl) ⟨15872, by rfl⟩) R31745
theorem R53945 : Reach 53945 := rs (se 2 (by rfl) ⟨20229, by rfl⟩) R40459
theorem R21191 : Reach 21191 := rs (se 1 (by rfl) ⟨15893, by rfl⟩) R31787
theorem R53975 : Reach 53975 := rs (se 1 (by rfl) ⟨40481, by rfl⟩) R80963
theorem R21239 : Reach 21239 := rs (se 1 (by rfl) ⟨15929, by rfl⟩) R31859
theorem R119555 : Reach 119555 := rs (se 1 (by rfl) ⟨89666, by rfl⟩) R179333
theorem R21343 : Reach 21343 := rs (se 1 (by rfl) ⟨16007, by rfl⟩) R32015
theorem R21353 : Reach 21353 := rs (se 2 (by rfl) ⟨8007, by rfl⟩) R16015
theorem R21431 : Reach 21431 := rs (se 1 (by rfl) ⟨16073, by rfl⟩) R32147
theorem R807893 : Reach 807893 := rs (se 7 (by rfl) ⟨9467, by rfl⟩) R18935
theorem R21467 : Reach 21467 := rs (se 1 (by rfl) ⟨16100, by rfl⟩) R32201
theorem R54425 : Reach 54425 := rs (se 2 (by rfl) ⟨20409, by rfl⟩) R40819
theorem R21703 : Reach 21703 := rs (se 1 (by rfl) ⟨16277, by rfl⟩) R32555
theorem R21833 : Reach 21833 := rs (se 2 (by rfl) ⟨8187, by rfl⟩) R16375
theorem R21865 : Reach 21865 := rs (se 2 (by rfl) ⟨8199, by rfl⟩) R16399
theorem R21935 : Reach 21935 := rs (se 1 (by rfl) ⟨16451, by rfl⟩) R32903
theorem R21947 : Reach 21947 := rs (se 1 (by rfl) ⟨16460, by rfl⟩) R32921
theorem R22025 : Reach 22025 := rs (se 2 (by rfl) ⟨8259, by rfl⟩) R16519
theorem R22055 : Reach 22055 := rs (se 1 (by rfl) ⟨16541, by rfl⟩) R33083
theorem R22073 : Reach 22073 := rs (se 2 (by rfl) ⟨8277, by rfl⟩) R16555
theorem R54881 : Reach 54881 := rs (se 2 (by rfl) ⟨20580, by rfl⟩) R41161
theorem R22139 : Reach 22139 := rs (se 1 (by rfl) ⟨16604, by rfl⟩) R33209
theorem R120467 : Reach 120467 := rs (se 1 (by rfl) ⟨90350, by rfl⟩) R180701
theorem R284309 : Reach 284309 := rs (se 6 (by rfl) ⟨6663, by rfl⟩) R13327
theorem R22187 : Reach 22187 := rs (se 1 (by rfl) ⟨16640, by rfl⟩) R33281
theorem R22265 : Reach 22265 := rs (se 2 (by rfl) ⟨8349, by rfl⟩) R16699
theorem R87875 : Reach 87875 := rs (se 1 (by rfl) ⟨65906, by rfl⟩) R131813
theorem R22367 : Reach 22367 := rs (se 1 (by rfl) ⟨16775, by rfl⟩) R33551
theorem R22379 : Reach 22379 := rs (se 1 (by rfl) ⟨16784, by rfl⟩) R33569
theorem R22415 : Reach 22415 := rs (se 1 (by rfl) ⟨16811, by rfl⟩) R33623
theorem R22447 : Reach 22447 := rs (se 1 (by rfl) ⟨16835, by rfl⟩) R33671
theorem R22459 : Reach 22459 := rs (se 1 (by rfl) ⟨16844, by rfl⟩) R33689
theorem R22535 : Reach 22535 := rs (se 1 (by rfl) ⟨16901, by rfl⟩) R33803
theorem R22585 : Reach 22585 := rs (se 2 (by rfl) ⟨8469, by rfl⟩) R16939
theorem R22607 : Reach 22607 := rs (se 1 (by rfl) ⟨16955, by rfl⟩) R33911
theorem R350365 : Reach 350365 := rs (se 3 (by rfl) ⟨65693, by rfl⟩) R131387
theorem R22727 : Reach 22727 := rs (se 1 (by rfl) ⟨17045, by rfl⟩) R34091
theorem R22775 : Reach 22775 := rs (se 1 (by rfl) ⟨17081, by rfl⟩) R34163
theorem R121175 : Reach 121175 := rs (se 1 (by rfl) ⟨90881, by rfl⟩) R181763
theorem R22889 : Reach 22889 := rs (se 2 (by rfl) ⟨8583, by rfl⟩) R17167
theorem R22967 : Reach 22967 := rs (se 1 (by rfl) ⟨17225, by rfl⟩) R34451
theorem R23003 : Reach 23003 := rs (se 1 (by rfl) ⟨17252, by rfl⟩) R34505
theorem R23047 : Reach 23047 := rs (se 1 (by rfl) ⟨17285, by rfl⟩) R34571
theorem R55943 : Reach 55943 := rs (se 1 (by rfl) ⟨41957, by rfl⟩) R83915
theorem R23287 : Reach 23287 := rs (se 1 (by rfl) ⟨17465, by rfl⟩) R34931
theorem R23369 : Reach 23369 := rs (se 2 (by rfl) ⟨8763, by rfl⟩) R17527
theorem R23471 : Reach 23471 := rs (se 1 (by rfl) ⟨17603, by rfl⟩) R35207
theorem R23483 : Reach 23483 := rs (se 1 (by rfl) ⟨17612, by rfl⟩) R35225
theorem R56321 : Reach 56321 := rs (se 2 (by rfl) ⟨21120, by rfl⟩) R42241
theorem R23561 : Reach 23561 := rs (se 2 (by rfl) ⟨8835, by rfl⟩) R17671
theorem R56339 : Reach 56339 := rs (se 1 (by rfl) ⟨42254, by rfl⟩) R84509
theorem R23591 : Reach 23591 := rs (se 1 (by rfl) ⟨17693, by rfl⟩) R35387
theorem R23609 : Reach 23609 := rs (se 2 (by rfl) ⟨8853, by rfl⟩) R17707
theorem R23675 : Reach 23675 := rs (se 1 (by rfl) ⟨17756, by rfl⟩) R35513
theorem R23723 : Reach 23723 := rs (se 1 (by rfl) ⟨17792, by rfl⟩) R35585
theorem R23801 : Reach 23801 := rs (se 2 (by rfl) ⟨8925, by rfl⟩) R17851
theorem R23881 : Reach 23881 := rs (se 2 (by rfl) ⟨8955, by rfl⟩) R17911
theorem R23903 : Reach 23903 := rs (se 1 (by rfl) ⟨17927, by rfl⟩) R35855
theorem R23915 : Reach 23915 := rs (se 1 (by rfl) ⟨17936, by rfl⟩) R35873
theorem R23951 : Reach 23951 := rs (se 1 (by rfl) ⟨17963, by rfl⟩) R35927
theorem R23969 : Reach 23969 := rs (se 2 (by rfl) ⟨8988, by rfl⟩) R17977
theorem R24071 : Reach 24071 := rs (se 1 (by rfl) ⟨18053, by rfl⟩) R36107
theorem R24083 : Reach 24083 := rs (se 1 (by rfl) ⟨18062, by rfl⟩) R36125
theorem R24143 : Reach 24143 := rs (se 1 (by rfl) ⟨18107, by rfl⟩) R36215
theorem R187991 : Reach 187991 := rs (se 1 (by rfl) ⟨140993, by rfl⟩) R281987
theorem R24161 : Reach 24161 := rs (se 2 (by rfl) ⟨9060, by rfl⟩) R18121
theorem R220805 : Reach 220805 := rs (se 4 (by rfl) ⟨20700, by rfl⟩) R41401
theorem R89747 : Reach 89747 := rs (se 1 (by rfl) ⟨67310, by rfl⟩) R134621
theorem R24263 : Reach 24263 := rs (se 1 (by rfl) ⟨18197, by rfl⟩) R36395
theorem R24275 : Reach 24275 := rs (se 1 (by rfl) ⟨18206, by rfl⟩) R36413
theorem R24311 : Reach 24311 := rs (se 1 (by rfl) ⟨18233, by rfl⟩) R36467
theorem R24313 : Reach 24313 := rs (se 2 (by rfl) ⟨9117, by rfl⟩) R18235
theorem R89849 : Reach 89849 := rs (se 2 (by rfl) ⟨33693, by rfl⟩) R67387
theorem R57131 : Reach 57131 := rs (se 1 (by rfl) ⟨42848, by rfl⟩) R85697
theorem R89915 : Reach 89915 := rs (se 1 (by rfl) ⟨67436, by rfl⟩) R134873
theorem R24425 : Reach 24425 := rs (se 2 (by rfl) ⟨9159, by rfl⟩) R18319
theorem R24503 : Reach 24503 := rs (se 1 (by rfl) ⟨18377, by rfl⟩) R36755
theorem R286651 : Reach 286651 := rs (se 1 (by rfl) ⟨214988, by rfl⟩) R429977
theorem R24539 : Reach 24539 := rs (se 1 (by rfl) ⟨18404, by rfl⟩) R36809
theorem R24583 : Reach 24583 := rs (se 1 (by rfl) ⟨18437, by rfl⟩) R36875
theorem R57401 : Reach 57401 := rs (se 2 (by rfl) ⟨21525, by rfl⟩) R43051
theorem R122957 : Reach 122957 := rs (se 3 (by rfl) ⟨23054, by rfl⟩) R46109
theorem R24905 : Reach 24905 := rs (se 2 (by rfl) ⟨9339, by rfl⟩) R18679
theorem R25007 : Reach 25007 := rs (se 1 (by rfl) ⟨18755, by rfl⟩) R37511
theorem R25015 : Reach 25015 := rs (se 1 (by rfl) ⟨18761, by rfl⟩) R37523
theorem R25019 : Reach 25019 := rs (se 1 (by rfl) ⟨18764, by rfl⟩) R37529
theorem R25097 : Reach 25097 := rs (se 2 (by rfl) ⟨9411, by rfl⟩) R18823
theorem R25127 : Reach 25127 := rs (se 1 (by rfl) ⟨18845, by rfl⟩) R37691
theorem R25145 : Reach 25145 := rs (se 2 (by rfl) ⟨9429, by rfl⟩) R18859
theorem R25211 : Reach 25211 := rs (se 1 (by rfl) ⟨18908, by rfl⟩) R37817
theorem R25259 : Reach 25259 := rs (se 1 (by rfl) ⟨18944, by rfl⟩) R37889
theorem R123565 : Reach 123565 := rs (se 3 (by rfl) ⟨23168, by rfl⟩) R46337
theorem R25337 : Reach 25337 := rs (se 2 (by rfl) ⟨9501, by rfl⟩) R19003
theorem R25439 : Reach 25439 := rs (se 1 (by rfl) ⟨19079, by rfl⟩) R38159
theorem R25451 : Reach 25451 := rs (se 1 (by rfl) ⟨19088, by rfl⟩) R38177
theorem R25487 : Reach 25487 := rs (se 1 (by rfl) ⟨19115, by rfl⟩) R38231
theorem R25505 : Reach 25505 := rs (se 2 (by rfl) ⟨9564, by rfl⟩) R19129
theorem R25607 : Reach 25607 := rs (se 1 (by rfl) ⟨19205, by rfl⟩) R38411
theorem R25609 : Reach 25609 := rs (se 2 (by rfl) ⟨9603, by rfl⟩) R19207
theorem R25619 : Reach 25619 := rs (se 1 (by rfl) ⟨19214, by rfl⟩) R38429
theorem R25679 : Reach 25679 := rs (se 1 (by rfl) ⟨19259, by rfl⟩) R38519
theorem R25697 : Reach 25697 := rs (se 2 (by rfl) ⟨9636, by rfl⟩) R19273
theorem R25771 : Reach 25771 := rs (se 1 (by rfl) ⟨19328, by rfl⟩) R38657
theorem R91307 : Reach 91307 := rs (se 1 (by rfl) ⟨68480, by rfl⟩) R136961
theorem R91331 : Reach 91331 := rs (se 1 (by rfl) ⟨68498, by rfl⟩) R136997
theorem R25799 : Reach 25799 := rs (se 1 (by rfl) ⟨19349, by rfl⟩) R38699
theorem R25811 : Reach 25811 := rs (se 1 (by rfl) ⟨19358, by rfl⟩) R38717
theorem R25847 : Reach 25847 := rs (se 1 (by rfl) ⟨19385, by rfl⟩) R38771
theorem R25849 : Reach 25849 := rs (se 2 (by rfl) ⟨9693, by rfl⟩) R19387
theorem R25961 : Reach 25961 := rs (se 2 (by rfl) ⟨9735, by rfl⟩) R19471
theorem R26039 : Reach 26039 := rs (se 1 (by rfl) ⟨19529, by rfl⟩) R39059
theorem R26075 : Reach 26075 := rs (se 1 (by rfl) ⟨19556, by rfl⟩) R39113
theorem R26119 : Reach 26119 := rs (se 1 (by rfl) ⟨19589, by rfl⟩) R39179
theorem R26209 : Reach 26209 := rs (se 2 (by rfl) ⟨9828, by rfl⟩) R19657
theorem R255635 : Reach 255635 := rs (se 1 (by rfl) ⟨191726, by rfl⟩) R383453
theorem R26311 : Reach 26311 := rs (se 1 (by rfl) ⟨19733, by rfl⟩) R39467
theorem R59129 : Reach 59129 := rs (se 2 (by rfl) ⟨22173, by rfl⟩) R44347
theorem R26441 : Reach 26441 := rs (se 2 (by rfl) ⟨9915, by rfl⟩) R19831
theorem R59231 : Reach 59231 := rs (se 1 (by rfl) ⟨44423, by rfl⟩) R88847
theorem R26473 : Reach 26473 := rs (se 2 (by rfl) ⟨9927, by rfl⟩) R19855
theorem R59255 : Reach 59255 := rs (se 1 (by rfl) ⟨44441, by rfl⟩) R88883
theorem R157601 : Reach 157601 := rs (se 2 (by rfl) ⟨59100, by rfl⟩) R118201
theorem R26543 : Reach 26543 := rs (se 1 (by rfl) ⟨19907, by rfl⟩) R39815
theorem R26555 : Reach 26555 := rs (se 1 (by rfl) ⟨19916, by rfl⟩) R39833
theorem R124865 : Reach 124865 := rs (se 2 (by rfl) ⟨46824, by rfl⟩) R93649
theorem R59399 : Reach 59399 := rs (se 1 (by rfl) ⟨44549, by rfl⟩) R89099
theorem R26633 : Reach 26633 := rs (se 2 (by rfl) ⟨9987, by rfl⟩) R19975
theorem R26663 : Reach 26663 := rs (se 1 (by rfl) ⟨19997, by rfl⟩) R39995
theorem R26681 : Reach 26681 := rs (se 2 (by rfl) ⟨10005, by rfl⟩) R20011
theorem R92249 : Reach 92249 := rs (se 2 (by rfl) ⟨34593, by rfl⟩) R69187
theorem R59507 : Reach 59507 := rs (se 1 (by rfl) ⟨44630, by rfl⟩) R89261
theorem R26747 : Reach 26747 := rs (se 1 (by rfl) ⟨20060, by rfl⟩) R40121
theorem R59549 : Reach 59549 := rs (se 3 (by rfl) ⟨11165, by rfl⟩) R22331
theorem R26795 : Reach 26795 := rs (se 1 (by rfl) ⟨20096, by rfl⟩) R40193
theorem R583861 : Reach 583861 := rs (se 5 (by rfl) ⟨27368, by rfl⟩) R54737
theorem R26873 : Reach 26873 := rs (se 2 (by rfl) ⟨10077, by rfl⟩) R20155
theorem R26975 : Reach 26975 := rs (se 1 (by rfl) ⟨20231, by rfl⟩) R40463
theorem R26987 : Reach 26987 := rs (se 1 (by rfl) ⟨20240, by rfl⟩) R40481
theorem R59777 : Reach 59777 := rs (se 2 (by rfl) ⟨22416, by rfl⟩) R44833
theorem R27023 : Reach 27023 := rs (se 1 (by rfl) ⟨20267, by rfl⟩) R40535
theorem R125387 : Reach 125387 := rs (se 1 (by rfl) ⟨94040, by rfl⟩) R188081
theorem R59885 : Reach 59885 := rs (se 3 (by rfl) ⟨11228, by rfl⟩) R22457
theorem R27175 : Reach 27175 := rs (se 1 (by rfl) ⟨20381, by rfl⟩) R40763
theorem R27233 : Reach 27233 := rs (se 2 (by rfl) ⟨10212, by rfl⟩) R20425
theorem R27335 : Reach 27335 := rs (se 1 (by rfl) ⟨20501, by rfl⟩) R41003
theorem R27347 : Reach 27347 := rs (se 1 (by rfl) ⟨20510, by rfl⟩) R41021
theorem R158557 : Reach 158557 := rs (se 3 (by rfl) ⟨29729, by rfl⟩) R59459
theorem R27499 : Reach 27499 := rs (se 1 (by rfl) ⟨20624, by rfl⟩) R41249
theorem R27553 : Reach 27553 := rs (se 2 (by rfl) ⟨10332, by rfl⟩) R20665
theorem R27575 : Reach 27575 := rs (se 1 (by rfl) ⟨20681, by rfl⟩) R41363
theorem R93149 : Reach 93149 := rs (se 3 (by rfl) ⟨17465, by rfl⟩) R34931
theorem R60587 : Reach 60587 := rs (se 1 (by rfl) ⟨45440, by rfl⟩) R90881
theorem R715969 : Reach 715969 := rs (se 2 (by rfl) ⟨268488, by rfl⟩) R536977
theorem R1371491 : Reach 1371491 := rs (se 1 (by rfl) ⟨1028618, by rfl⟩) R2057237
theorem R28169 : Reach 28169 := rs (se 2 (by rfl) ⟨10563, by rfl⟩) R21127
theorem R28199 : Reach 28199 := rs (se 1 (by rfl) ⟨21149, by rfl⟩) R42299
theorem R28283 : Reach 28283 := rs (se 1 (by rfl) ⟨21212, by rfl⟩) R42425
theorem R61073 : Reach 61073 := rs (se 2 (by rfl) ⟨22902, by rfl⟩) R45805
theorem R61127 : Reach 61127 := rs (se 1 (by rfl) ⟨45845, by rfl⟩) R91691
theorem R28409 : Reach 28409 := rs (se 2 (by rfl) ⟨10653, by rfl⟩) R21307
theorem R61177 : Reach 61177 := rs (se 2 (by rfl) ⟨22941, by rfl⟩) R45883
theorem R28511 : Reach 28511 := rs (se 1 (by rfl) ⟨21383, by rfl⟩) R42767
theorem R28523 : Reach 28523 := rs (se 1 (by rfl) ⟨21392, by rfl⟩) R42785
theorem R28577 : Reach 28577 := rs (se 2 (by rfl) ⟨10716, by rfl⟩) R21433
theorem R28679 : Reach 28679 := rs (se 1 (by rfl) ⟨21509, by rfl⟩) R43019
theorem R94223 : Reach 94223 := rs (se 1 (by rfl) ⟨70667, by rfl⟩) R141335
theorem R28691 : Reach 28691 := rs (se 1 (by rfl) ⟨21518, by rfl⟩) R43037
theorem R28751 : Reach 28751 := rs (se 1 (by rfl) ⟨21563, by rfl⟩) R43127
theorem R28919 : Reach 28919 := rs (se 1 (by rfl) ⟨21689, by rfl⟩) R43379
theorem R29033 : Reach 29033 := rs (se 2 (by rfl) ⟨10887, by rfl⟩) R21775
theorem R29147 : Reach 29147 := rs (se 1 (by rfl) ⟨21860, by rfl⟩) R43721
theorem R29281 : Reach 29281 := rs (se 2 (by rfl) ⟨10980, by rfl⟩) R21961
theorem R94931 : Reach 94931 := rs (se 1 (by rfl) ⟨71198, by rfl⟩) R142397
theorem R29513 : Reach 29513 := rs (se 2 (by rfl) ⟨11067, by rfl⟩) R22135
theorem R127817 : Reach 127817 := rs (se 2 (by rfl) ⟨47931, by rfl⟩) R95863
theorem R62315 : Reach 62315 := rs (se 1 (by rfl) ⟨46736, by rfl⟩) R93473
theorem R29615 : Reach 29615 := rs (se 1 (by rfl) ⟨22211, by rfl⟩) R44423
theorem R29627 : Reach 29627 := rs (se 1 (by rfl) ⟨22220, by rfl⟩) R44441
theorem R259037 : Reach 259037 := rs (se 3 (by rfl) ⟨48569, by rfl⟩) R97139
theorem R29753 : Reach 29753 := rs (se 2 (by rfl) ⟨11157, by rfl⟩) R22315
theorem R29867 : Reach 29867 := rs (se 1 (by rfl) ⟨22400, by rfl⟩) R44801
theorem R95435 : Reach 95435 := rs (se 1 (by rfl) ⟨71576, by rfl⟩) R143153
theorem R30095 : Reach 30095 := rs (se 1 (by rfl) ⟨22571, by rfl⟩) R45143
theorem R62963 : Reach 62963 := rs (se 1 (by rfl) ⟨47222, by rfl⟩) R94445
theorem R161291 : Reach 161291 := rs (se 1 (by rfl) ⟨120968, by rfl⟩) R241937
theorem R30419 : Reach 30419 := rs (se 1 (by rfl) ⟨22814, by rfl⟩) R45629
theorem R63341 : Reach 63341 := rs (se 3 (by rfl) ⟨11876, by rfl⟩) R23753
theorem R96187 : Reach 96187 := rs (se 1 (by rfl) ⟨72140, by rfl⟩) R144281
theorem R325579 : Reach 325579 := rs (se 1 (by rfl) ⟨244184, by rfl⟩) R488369
theorem R63503 : Reach 63503 := rs (se 1 (by rfl) ⟨47627, by rfl⟩) R95255
theorem R30739 : Reach 30739 := rs (se 1 (by rfl) ⟨23054, by rfl⟩) R46109
theorem R260185 : Reach 260185 := rs (se 2 (by rfl) ⟨97569, by rfl⟩) R195139
theorem R162233 : Reach 162233 := rs (se 2 (by rfl) ⟨60837, by rfl⟩) R121675
theorem R31195 : Reach 31195 := rs (se 1 (by rfl) ⟨23396, by rfl⟩) R46793
theorem R31241 : Reach 31241 := rs (se 2 (by rfl) ⟨11715, by rfl⟩) R23431
theorem R31355 : Reach 31355 := rs (se 1 (by rfl) ⟨23516, by rfl⟩) R47033
theorem R31481 : Reach 31481 := rs (se 2 (by rfl) ⟨11805, by rfl⟩) R23611
theorem R64259 : Reach 64259 := rs (se 1 (by rfl) ⟨48194, by rfl⟩) R96389
theorem R31583 : Reach 31583 := rs (se 1 (by rfl) ⟨23687, by rfl⟩) R47375
theorem R97199 : Reach 97199 := rs (se 1 (by rfl) ⟨72899, by rfl⟩) R145799
theorem R31751 : Reach 31751 := rs (se 1 (by rfl) ⟨23813, by rfl⟩) R47627
theorem R31823 : Reach 31823 := rs (se 1 (by rfl) ⟨23867, by rfl⟩) R47735
theorem R64759 : Reach 64759 := rs (se 1 (by rfl) ⟨48569, by rfl⟩) R97139
theorem R32129 : Reach 32129 := rs (se 2 (by rfl) ⟨12048, by rfl⟩) R24097
theorem R32143 : Reach 32143 := rs (se 1 (by rfl) ⟨24107, by rfl⟩) R48215
theorem R32219 : Reach 32219 := rs (se 1 (by rfl) ⟨24164, by rfl⟩) R48329
theorem R32243 : Reach 32243 := rs (se 1 (by rfl) ⟨24182, by rfl⟩) R48365
theorem R65063 : Reach 65063 := rs (se 1 (by rfl) ⟨48797, by rfl⟩) R97595
theorem R32395 : Reach 32395 := rs (se 1 (by rfl) ⟨24296, by rfl⟩) R48593
theorem R32467 : Reach 32467 := rs (se 1 (by rfl) ⟨24350, by rfl⟩) R48701
theorem R32471 : Reach 32471 := rs (se 1 (by rfl) ⟨24353, by rfl⟩) R48707
theorem R65245 : Reach 65245 := rs (se 3 (by rfl) ⟨12233, by rfl⟩) R24467
theorem R32687 : Reach 32687 := rs (se 1 (by rfl) ⟨24515, by rfl⟩) R49031
theorem R32699 : Reach 32699 := rs (se 1 (by rfl) ⟨24524, by rfl⟩) R49049
theorem R262075 : Reach 262075 := rs (se 1 (by rfl) ⟨196556, by rfl⟩) R393113
theorem R32777 : Reach 32777 := rs (se 2 (by rfl) ⟨12291, by rfl⟩) R24583
theorem R65555 : Reach 65555 := rs (se 1 (by rfl) ⟨49166, by rfl⟩) R98333
theorem R65747 : Reach 65747 := rs (se 1 (by rfl) ⟨49310, by rfl⟩) R98621
theorem R33115 : Reach 33115 := rs (se 1 (by rfl) ⟨24836, by rfl⟩) R49673
theorem R98723 : Reach 98723 := rs (se 1 (by rfl) ⟨74042, by rfl⟩) R148085
theorem R33191 : Reach 33191 := rs (se 1 (by rfl) ⟨24893, by rfl⟩) R49787
theorem R33299 : Reach 33299 := rs (se 1 (by rfl) ⟨24974, by rfl⟩) R49949
theorem R33353 : Reach 33353 := rs (se 2 (by rfl) ⟨12507, by rfl⟩) R25015
theorem R33455 : Reach 33455 := rs (se 1 (by rfl) ⟨25091, by rfl⟩) R50183
theorem R33527 : Reach 33527 := rs (se 1 (by rfl) ⟨25145, by rfl⟩) R50291
theorem R164753 : Reach 164753 := rs (se 2 (by rfl) ⟨61782, by rfl⟩) R123565
theorem R33767 : Reach 33767 := rs (se 1 (by rfl) ⟨25325, by rfl⟩) R50651
theorem R66703 : Reach 66703 := rs (se 1 (by rfl) ⟨50027, by rfl⟩) R100055
theorem R34145 : Reach 34145 := rs (se 2 (by rfl) ⟨12804, by rfl⟩) R25609
theorem R263533 : Reach 263533 := rs (se 3 (by rfl) ⟨49412, by rfl⟩) R98825
theorem R99737 : Reach 99737 := rs (se 2 (by rfl) ⟨37401, by rfl⟩) R74803
theorem R66977 : Reach 66977 := rs (se 2 (by rfl) ⟨25116, by rfl⟩) R50233
theorem R34235 : Reach 34235 := rs (se 1 (by rfl) ⟨25676, by rfl⟩) R51353
theorem R34361 : Reach 34361 := rs (se 2 (by rfl) ⟨12885, by rfl⟩) R25771
theorem R67229 : Reach 67229 := rs (se 3 (by rfl) ⟨12605, by rfl⟩) R25211
theorem R34465 : Reach 34465 := rs (se 2 (by rfl) ⟨12924, by rfl⟩) R25849
theorem R329507 : Reach 329507 := rs (se 1 (by rfl) ⟨247130, by rfl⟩) R494261
theorem R34607 : Reach 34607 := rs (se 1 (by rfl) ⟨25955, by rfl⟩) R51911
theorem R34825 : Reach 34825 := rs (se 2 (by rfl) ⟨13059, by rfl⟩) R26119
theorem R35027 : Reach 35027 := rs (se 1 (by rfl) ⟨26270, by rfl⟩) R52541
theorem R35081 : Reach 35081 := rs (se 2 (by rfl) ⟨13155, by rfl⟩) R26311
theorem R35255 : Reach 35255 := rs (se 1 (by rfl) ⟨26441, by rfl⟩) R52883
theorem R35297 : Reach 35297 := rs (se 2 (by rfl) ⟨13236, by rfl⟩) R26473
theorem R2296349 : Reach 2296349 := rs (se 3 (by rfl) ⟨430565, by rfl⟩) R861131
theorem R35407 : Reach 35407 := rs (se 1 (by rfl) ⟨26555, by rfl⟩) R53111
theorem R68219 : Reach 68219 := rs (se 1 (by rfl) ⟨51164, by rfl⟩) R102329
theorem R35603 : Reach 35603 := rs (se 1 (by rfl) ⟨26702, by rfl⟩) R53405
theorem R68471 : Reach 68471 := rs (se 1 (by rfl) ⟨51353, by rfl⟩) R102707
theorem R68525 : Reach 68525 := rs (se 3 (by rfl) ⟨12848, by rfl⟩) R25697
theorem R68647 : Reach 68647 := rs (se 1 (by rfl) ⟨51485, by rfl⟩) R102971
theorem R199745 : Reach 199745 := rs (se 2 (by rfl) ⟨74904, by rfl⟩) R149809
theorem R68723 : Reach 68723 := rs (se 1 (by rfl) ⟨51542, by rfl⟩) R103085
theorem R35963 : Reach 35963 := rs (se 1 (by rfl) ⟨26972, by rfl⟩) R53945
theorem R35983 : Reach 35983 := rs (se 1 (by rfl) ⟨26987, by rfl⟩) R53975
theorem R36233 : Reach 36233 := rs (se 2 (by rfl) ⟨13587, by rfl⟩) R27175
theorem R36283 : Reach 36283 := rs (se 1 (by rfl) ⟨27212, by rfl⟩) R54425
theorem R69113 : Reach 69113 := rs (se 2 (by rfl) ⟨25917, by rfl⟩) R51835
theorem R101897 : Reach 101897 := rs (se 2 (by rfl) ⟨38211, by rfl⟩) R76423
theorem R36587 : Reach 36587 := rs (se 1 (by rfl) ⟨27440, by rfl⟩) R54881
theorem R36665 : Reach 36665 := rs (se 2 (by rfl) ⟨13749, by rfl⟩) R27499
theorem R69437 : Reach 69437 := rs (se 3 (by rfl) ⟨13019, by rfl⟩) R26039
theorem R36737 : Reach 36737 := rs (se 2 (by rfl) ⟨13776, by rfl⟩) R27553
theorem R954625 : Reach 954625 := rs (se 2 (by rfl) ⟨357984, by rfl⟩) R715969
theorem R37295 : Reach 37295 := rs (se 1 (by rfl) ⟨27971, by rfl⟩) R55943
theorem R70145 : Reach 70145 := rs (se 2 (by rfl) ⟨26304, by rfl⟩) R52609
theorem R266813 : Reach 266813 := rs (se 3 (by rfl) ⟨50027, by rfl⟩) R100055
theorem R37547 : Reach 37547 := rs (se 1 (by rfl) ⟨28160, by rfl⟩) R56321
theorem R37559 : Reach 37559 := rs (se 1 (by rfl) ⟨28169, by rfl⟩) R56339
theorem R70631 : Reach 70631 := rs (se 1 (by rfl) ⟨52973, by rfl⟩) R105947
theorem R38087 : Reach 38087 := rs (se 1 (by rfl) ⟨28565, by rfl⟩) R57131
theorem R70955 : Reach 70955 := rs (se 1 (by rfl) ⟨53216, by rfl⟩) R106433
theorem R38267 : Reach 38267 := rs (se 1 (by rfl) ⟨28700, by rfl⟩) R57401
theorem R38333 : Reach 38333 := rs (se 3 (by rfl) ⟨7187, by rfl⟩) R14375
theorem R39041 : Reach 39041 := rs (se 2 (by rfl) ⟨14640, by rfl⟩) R29281
theorem R202981 : Reach 202981 := rs (se 4 (by rfl) ⟨19029, by rfl⟩) R38059
theorem R71927 : Reach 71927 := rs (se 1 (by rfl) ⟨53945, by rfl⟩) R107891
theorem R170423 : Reach 170423 := rs (se 1 (by rfl) ⟨127817, by rfl⟩) R255635
theorem R39419 : Reach 39419 := rs (se 1 (by rfl) ⟨29564, by rfl⟩) R59129
theorem R39487 : Reach 39487 := rs (se 1 (by rfl) ⟨29615, by rfl⟩) R59231
theorem R39503 : Reach 39503 := rs (se 1 (by rfl) ⟨29627, by rfl⟩) R59255
theorem R105067 : Reach 105067 := rs (se 1 (by rfl) ⟨78800, by rfl⟩) R157601
theorem R203381 : Reach 203381 := rs (se 5 (by rfl) ⟨9533, by rfl⟩) R19067
theorem R39599 : Reach 39599 := rs (se 1 (by rfl) ⟨29699, by rfl⟩) R59399
theorem R39671 : Reach 39671 := rs (se 1 (by rfl) ⟨29753, by rfl⟩) R59507
theorem R39851 : Reach 39851 := rs (se 1 (by rfl) ⟨29888, by rfl⟩) R59777
theorem R39923 : Reach 39923 := rs (se 1 (by rfl) ⟨29942, by rfl⟩) R59885
theorem R40391 : Reach 40391 := rs (se 1 (by rfl) ⟨30293, by rfl⟩) R60587
theorem R40715 : Reach 40715 := rs (se 1 (by rfl) ⟨30536, by rfl⟩) R61073
theorem R40751 : Reach 40751 := rs (se 1 (by rfl) ⟨30563, by rfl⟩) R61127
theorem R434105 : Reach 434105 := rs (se 2 (by rfl) ⟨162789, by rfl⟩) R325579
theorem R40985 : Reach 40985 := rs (se 2 (by rfl) ⟨15369, by rfl⟩) R30739
theorem R467153 : Reach 467153 := rs (se 2 (by rfl) ⟨175182, by rfl⟩) R350365
theorem R139481 : Reach 139481 := rs (se 2 (by rfl) ⟨52305, by rfl⟩) R104611
theorem R139781 : Reach 139781 := rs (se 4 (by rfl) ⟨13104, by rfl⟩) R26209
theorem R41543 : Reach 41543 := rs (se 1 (by rfl) ⟨31157, by rfl⟩) R62315
theorem R41593 : Reach 41593 := rs (se 2 (by rfl) ⟨15597, by rfl⟩) R31195
theorem R172691 : Reach 172691 := rs (se 1 (by rfl) ⟨129518, by rfl⟩) R259037
theorem R402149 : Reach 402149 := rs (se 4 (by rfl) ⟨37701, by rfl⟩) R75403
theorem R533263 : Reach 533263 := rs (se 1 (by rfl) ⟨399947, by rfl⟩) R799895
theorem R41975 : Reach 41975 := rs (se 1 (by rfl) ⟨31481, by rfl⟩) R62963
theorem R107527 : Reach 107527 := rs (se 1 (by rfl) ⟨80645, by rfl⟩) R161291
theorem R74951 : Reach 74951 := rs (se 1 (by rfl) ⟨56213, by rfl⟩) R112427
theorem R42227 : Reach 42227 := rs (se 1 (by rfl) ⟨31670, by rfl⟩) R63341
theorem R42335 : Reach 42335 := rs (se 1 (by rfl) ⟨31751, by rfl⟩) R63503
theorem R173501 : Reach 173501 := rs (se 3 (by rfl) ⟨32531, by rfl⟩) R65063
theorem R108155 : Reach 108155 := rs (se 1 (by rfl) ⟨81116, by rfl⟩) R162233
theorem R42839 : Reach 42839 := rs (se 1 (by rfl) ⟨32129, by rfl⟩) R64259
theorem R42857 : Reach 42857 := rs (se 2 (by rfl) ⟨16071, by rfl⟩) R32143
theorem R75757 : Reach 75757 := rs (se 3 (by rfl) ⟨14204, by rfl⟩) R28409
theorem R239773 : Reach 239773 := rs (se 3 (by rfl) ⟨44957, by rfl⟩) R89915
theorem R43193 : Reach 43193 := rs (se 2 (by rfl) ⟨16197, by rfl⟩) R32395
theorem R43289 : Reach 43289 := rs (se 2 (by rfl) ⟨16233, by rfl⟩) R32467
theorem R43375 : Reach 43375 := rs (se 1 (by rfl) ⟨32531, by rfl⟩) R65063
theorem R108973 : Reach 108973 := rs (se 3 (by rfl) ⟨20432, by rfl⟩) R40865
theorem R141911 : Reach 141911 := rs (se 1 (by rfl) ⟨106433, by rfl⟩) R212867
theorem R76477 : Reach 76477 := rs (se 3 (by rfl) ⟨14339, by rfl⟩) R28679
theorem R43901 : Reach 43901 := rs (se 3 (by rfl) ⟨8231, by rfl⟩) R16463
theorem R43919 : Reach 43919 := rs (se 1 (by rfl) ⟨32939, by rfl⟩) R65879
theorem R44171 : Reach 44171 := rs (se 1 (by rfl) ⟨33128, by rfl⟩) R66257
theorem R109943 : Reach 109943 := rs (se 1 (by rfl) ⟨82457, by rfl⟩) R164915
theorem R44639 : Reach 44639 := rs (se 1 (by rfl) ⟨33479, by rfl⟩) R66959
theorem R208493 : Reach 208493 := rs (se 3 (by rfl) ⟨39092, by rfl⟩) R78185
theorem R78083 : Reach 78083 := rs (se 1 (by rfl) ⟨58562, by rfl⟩) R117125
theorem R176417 : Reach 176417 := rs (se 2 (by rfl) ⟨66156, by rfl⟩) R132313
theorem R143819 : Reach 143819 := rs (se 1 (by rfl) ⟨107864, by rfl⟩) R215729
theorem R12863 : Reach 12863 := rs (se 1 (by rfl) ⟨9647, by rfl⟩) R19295
theorem R12871 : Reach 12871 := rs (se 1 (by rfl) ⟨9653, by rfl⟩) R19307
theorem R13023 : Reach 13023 := rs (se 1 (by rfl) ⟨9767, by rfl⟩) R19535
theorem R45791 : Reach 45791 := rs (se 1 (by rfl) ⟨34343, by rfl⟩) R68687
theorem R13103 : Reach 13103 := rs (se 1 (by rfl) ⟨9827, by rfl⟩) R19655
theorem R111469 : Reach 111469 := rs (se 3 (by rfl) ⟨20900, by rfl⟩) R41801
theorem R13211 : Reach 13211 := rs (se 1 (by rfl) ⟨9908, by rfl⟩) R19817
theorem R13263 : Reach 13263 := rs (se 1 (by rfl) ⟨9947, by rfl⟩) R19895
theorem R13287 : Reach 13287 := rs (se 1 (by rfl) ⟨9965, by rfl⟩) R19931
theorem R46223 : Reach 46223 := rs (se 1 (by rfl) ⟨34667, by rfl⟩) R69335
theorem R46295 : Reach 46295 := rs (se 1 (by rfl) ⟨34721, by rfl⟩) R69443
theorem R13531 : Reach 13531 := rs (se 1 (by rfl) ⟨10148, by rfl⟩) R20297
theorem R13599 : Reach 13599 := rs (se 1 (by rfl) ⟨10199, by rfl⟩) R20399
theorem R13607 : Reach 13607 := rs (se 1 (by rfl) ⟨10205, by rfl⟩) R20411
theorem R177497 : Reach 177497 := rs (se 2 (by rfl) ⟨66561, by rfl⟩) R133123
theorem R13659 : Reach 13659 := rs (se 1 (by rfl) ⟨10244, by rfl⟩) R20489
theorem R13679 : Reach 13679 := rs (se 1 (by rfl) ⟨10259, by rfl⟩) R20519
theorem R13691 : Reach 13691 := rs (se 1 (by rfl) ⟨10268, by rfl⟩) R20537
theorem R13735 : Reach 13735 := rs (se 1 (by rfl) ⟨10301, by rfl⟩) R20603
theorem R13767 : Reach 13767 := rs (se 1 (by rfl) ⟨10325, by rfl⟩) R20651
theorem R308701 : Reach 308701 := rs (se 3 (by rfl) ⟨57881, by rfl⟩) R115763
theorem R13819 : Reach 13819 := rs (se 1 (by rfl) ⟨10364, by rfl⟩) R20729
theorem R144935 : Reach 144935 := rs (se 1 (by rfl) ⟨108701, by rfl⟩) R217403
theorem R13887 : Reach 13887 := rs (se 1 (by rfl) ⟨10415, by rfl⟩) R20831
theorem R13895 : Reach 13895 := rs (se 1 (by rfl) ⟨10421, by rfl⟩) R20843
theorem R13919 : Reach 13919 := rs (se 1 (by rfl) ⟨10439, by rfl⟩) R20879
theorem R13999 : Reach 13999 := rs (se 1 (by rfl) ⟨10499, by rfl⟩) R20999
theorem R14047 : Reach 14047 := rs (se 1 (by rfl) ⟨10535, by rfl⟩) R21071
theorem R14127 : Reach 14127 := rs (se 1 (by rfl) ⟨10595, by rfl⟩) R21191
theorem R14159 : Reach 14159 := rs (se 1 (by rfl) ⟨10619, by rfl⟩) R21239
theorem R79703 : Reach 79703 := rs (se 1 (by rfl) ⟨59777, by rfl⟩) R119555
theorem R14235 : Reach 14235 := rs (se 1 (by rfl) ⟨10676, by rfl⟩) R21353
theorem R14287 : Reach 14287 := rs (se 1 (by rfl) ⟨10715, by rfl⟩) R21431
theorem R538595 : Reach 538595 := rs (se 1 (by rfl) ⟨403946, by rfl⟩) R807893
theorem R14311 : Reach 14311 := rs (se 1 (by rfl) ⟨10733, by rfl⟩) R21467
theorem R14555 : Reach 14555 := rs (se 1 (by rfl) ⟨10916, by rfl⟩) R21833
theorem R47357 : Reach 47357 := rs (se 3 (by rfl) ⟨8879, by rfl⟩) R17759
theorem R112921 : Reach 112921 := rs (se 2 (by rfl) ⟨42345, by rfl⟩) R84691
theorem R14623 : Reach 14623 := rs (se 1 (by rfl) ⟨10967, by rfl⟩) R21935
theorem R14631 : Reach 14631 := rs (se 1 (by rfl) ⟨10973, by rfl⟩) R21947
theorem R14683 : Reach 14683 := rs (se 1 (by rfl) ⟨11012, by rfl⟩) R22025
theorem R14703 : Reach 14703 := rs (se 1 (by rfl) ⟨11027, by rfl⟩) R22055
theorem R14715 : Reach 14715 := rs (se 1 (by rfl) ⟨11036, by rfl⟩) R22073
theorem R14759 : Reach 14759 := rs (se 1 (by rfl) ⟨11069, by rfl⟩) R22139
theorem R80311 : Reach 80311 := rs (se 1 (by rfl) ⟨60233, by rfl⟩) R120467
theorem R14791 : Reach 14791 := rs (se 1 (by rfl) ⟨11093, by rfl⟩) R22187
theorem R211409 : Reach 211409 := rs (se 2 (by rfl) ⟨79278, by rfl⟩) R158557
theorem R14843 : Reach 14843 := rs (se 1 (by rfl) ⟨11132, by rfl⟩) R22265
theorem R113177 : Reach 113177 := rs (se 2 (by rfl) ⟨42441, by rfl⟩) R84883
theorem R14911 : Reach 14911 := rs (se 1 (by rfl) ⟨11183, by rfl⟩) R22367
theorem R14919 : Reach 14919 := rs (se 1 (by rfl) ⟨11189, by rfl⟩) R22379
theorem R14943 : Reach 14943 := rs (se 1 (by rfl) ⟨11207, by rfl⟩) R22415
theorem R15023 : Reach 15023 := rs (se 1 (by rfl) ⟨11267, by rfl⟩) R22535
theorem R15071 : Reach 15071 := rs (se 1 (by rfl) ⟨11303, by rfl⟩) R22607
theorem R47891 : Reach 47891 := rs (se 1 (by rfl) ⟨35918, by rfl⟩) R71837
theorem R15151 : Reach 15151 := rs (se 1 (by rfl) ⟨11363, by rfl⟩) R22727
theorem R15183 : Reach 15183 := rs (se 1 (by rfl) ⟨11387, by rfl⟩) R22775
theorem R80783 : Reach 80783 := rs (se 1 (by rfl) ⟨60587, by rfl⟩) R121175
theorem R15259 : Reach 15259 := rs (se 1 (by rfl) ⟨11444, by rfl⟩) R22889
theorem R15311 : Reach 15311 := rs (se 1 (by rfl) ⟨11483, by rfl⟩) R22967
theorem R15335 : Reach 15335 := rs (se 1 (by rfl) ⟨11501, by rfl⟩) R23003
theorem R48167 : Reach 48167 := rs (se 1 (by rfl) ⟨36125, by rfl⟩) R72251
theorem R48251 : Reach 48251 := rs (se 1 (by rfl) ⟨36188, by rfl⟩) R72377
theorem R15579 : Reach 15579 := rs (se 1 (by rfl) ⟨11684, by rfl⟩) R23369
theorem R48347 : Reach 48347 := rs (se 1 (by rfl) ⟨36260, by rfl⟩) R72521
theorem R113885 : Reach 113885 := rs (se 3 (by rfl) ⟨21353, by rfl⟩) R42707
theorem R81125 : Reach 81125 := rs (se 4 (by rfl) ⟨7605, by rfl⟩) R15211
theorem R15647 : Reach 15647 := rs (se 1 (by rfl) ⟨11735, by rfl⟩) R23471
theorem R15655 : Reach 15655 := rs (se 1 (by rfl) ⟨11741, by rfl⟩) R23483
theorem R113987 : Reach 113987 := rs (se 1 (by rfl) ⟨85490, by rfl⟩) R170981
theorem R15707 : Reach 15707 := rs (se 1 (by rfl) ⟨11780, by rfl⟩) R23561
theorem R15727 : Reach 15727 := rs (se 1 (by rfl) ⟨11795, by rfl⟩) R23591
theorem R15739 : Reach 15739 := rs (se 1 (by rfl) ⟨11804, by rfl⟩) R23609
theorem R15783 : Reach 15783 := rs (se 1 (by rfl) ⟨11837, by rfl⟩) R23675
theorem R15815 : Reach 15815 := rs (se 1 (by rfl) ⟨11861, by rfl⟩) R23723
theorem R48599 : Reach 48599 := rs (se 1 (by rfl) ⟨36449, by rfl⟩) R72899
theorem R15867 : Reach 15867 := rs (se 1 (by rfl) ⟨11900, by rfl⟩) R23801
theorem R15935 : Reach 15935 := rs (se 1 (by rfl) ⟨11951, by rfl⟩) R23903
theorem R15943 : Reach 15943 := rs (se 1 (by rfl) ⟨11957, by rfl⟩) R23915
theorem R48721 : Reach 48721 := rs (se 2 (by rfl) ⟨18270, by rfl⟩) R36541
theorem R15967 : Reach 15967 := rs (se 1 (by rfl) ⟨11975, by rfl⟩) R23951
theorem R15979 : Reach 15979 := rs (se 1 (by rfl) ⟨11984, by rfl⟩) R23969
theorem R81569 : Reach 81569 := rs (se 2 (by rfl) ⟨30588, by rfl⟩) R61177
theorem R16047 : Reach 16047 := rs (se 1 (by rfl) ⟨12035, by rfl⟩) R24071
theorem R16055 : Reach 16055 := rs (se 1 (by rfl) ⟨12041, by rfl⟩) R24083
theorem R16095 : Reach 16095 := rs (se 1 (by rfl) ⟨12071, by rfl⟩) R24143
theorem R16107 : Reach 16107 := rs (se 1 (by rfl) ⟨12080, by rfl⟩) R24161
theorem R147203 : Reach 147203 := rs (se 1 (by rfl) ⟨110402, by rfl⟩) R220805
theorem R48937 : Reach 48937 := rs (se 2 (by rfl) ⟨18351, by rfl⟩) R36703
theorem R16175 : Reach 16175 := rs (se 1 (by rfl) ⟨12131, by rfl⟩) R24263
theorem R16183 : Reach 16183 := rs (se 1 (by rfl) ⟨12137, by rfl⟩) R24275
theorem R16207 : Reach 16207 := rs (se 1 (by rfl) ⟨12155, by rfl⟩) R24311
theorem R49025 : Reach 49025 := rs (se 2 (by rfl) ⟨18384, by rfl⟩) R36769
theorem R16283 : Reach 16283 := rs (se 1 (by rfl) ⟨12212, by rfl⟩) R24425
theorem R16335 : Reach 16335 := rs (se 1 (by rfl) ⟨12251, by rfl⟩) R24503
theorem R16359 : Reach 16359 := rs (se 1 (by rfl) ⟨12269, by rfl⟩) R24539
theorem R114695 : Reach 114695 := rs (se 1 (by rfl) ⟨86021, by rfl⟩) R172043
theorem R213029 : Reach 213029 := rs (se 4 (by rfl) ⟨19971, by rfl⟩) R39943
theorem R81971 : Reach 81971 := rs (se 1 (by rfl) ⟨61478, by rfl⟩) R122957
theorem R16603 : Reach 16603 := rs (se 1 (by rfl) ⟨12452, by rfl⟩) R24905
theorem R606437 : Reach 606437 := rs (se 4 (by rfl) ⟨56853, by rfl⟩) R113707
theorem R16671 : Reach 16671 := rs (se 1 (by rfl) ⟨12503, by rfl⟩) R25007
theorem R16679 : Reach 16679 := rs (se 1 (by rfl) ⟨12509, by rfl⟩) R25019
theorem R49481 : Reach 49481 := rs (se 2 (by rfl) ⟨18555, by rfl⟩) R37111
theorem R16731 : Reach 16731 := rs (se 1 (by rfl) ⟨12548, by rfl⟩) R25097
theorem R16751 : Reach 16751 := rs (se 1 (by rfl) ⟨12563, by rfl⟩) R25127
theorem R16763 : Reach 16763 := rs (se 1 (by rfl) ⟨12572, by rfl⟩) R25145
theorem R16807 : Reach 16807 := rs (se 1 (by rfl) ⟨12605, by rfl⟩) R25211
theorem R16839 : Reach 16839 := rs (se 1 (by rfl) ⟨12629, by rfl⟩) R25259
theorem R16891 : Reach 16891 := rs (se 1 (by rfl) ⟨12668, by rfl⟩) R25337
theorem R16959 : Reach 16959 := rs (se 1 (by rfl) ⟨12719, by rfl⟩) R25439
theorem R16967 : Reach 16967 := rs (se 1 (by rfl) ⟨12725, by rfl⟩) R25451
theorem R16991 : Reach 16991 := rs (se 1 (by rfl) ⟨12743, by rfl⟩) R25487
theorem R17003 : Reach 17003 := rs (se 1 (by rfl) ⟨12752, by rfl⟩) R25505
theorem R574087 : Reach 574087 := rs (se 1 (by rfl) ⟨430565, by rfl⟩) R861131
theorem R49835 : Reach 49835 := rs (se 1 (by rfl) ⟨37376, by rfl⟩) R74753
theorem R17071 : Reach 17071 := rs (se 1 (by rfl) ⟨12803, by rfl⟩) R25607
theorem R17079 : Reach 17079 := rs (se 1 (by rfl) ⟨12809, by rfl⟩) R25619
theorem R148169 : Reach 148169 := rs (se 2 (by rfl) ⟨55563, by rfl⟩) R111127
theorem R17119 : Reach 17119 := rs (se 1 (by rfl) ⟨12839, by rfl⟩) R25679
theorem R17131 : Reach 17131 := rs (se 1 (by rfl) ⟨12848, by rfl⟩) R25697
theorem R17193 : Reach 17193 := rs (se 2 (by rfl) ⟨6447, by rfl⟩) R12895
theorem R17199 : Reach 17199 := rs (se 1 (by rfl) ⟨12899, by rfl⟩) R25799
theorem R17207 : Reach 17207 := rs (se 1 (by rfl) ⟨12905, by rfl⟩) R25811
theorem R17231 : Reach 17231 := rs (se 1 (by rfl) ⟨12923, by rfl⟩) R25847
theorem R17307 : Reach 17307 := rs (se 1 (by rfl) ⟨12980, by rfl⟩) R25961
theorem R17359 : Reach 17359 := rs (se 1 (by rfl) ⟨13019, by rfl⟩) R26039
theorem R17383 : Reach 17383 := rs (se 1 (by rfl) ⟨13037, by rfl⟩) R26075
theorem R50273 : Reach 50273 := rs (se 2 (by rfl) ⟨18852, by rfl⟩) R37705
theorem R17513 : Reach 17513 := rs (se 2 (by rfl) ⟨6567, by rfl⟩) R13135
theorem R50323 : Reach 50323 := rs (se 1 (by rfl) ⟨37742, by rfl⟩) R75485
theorem R17627 : Reach 17627 := rs (se 1 (by rfl) ⟨13220, by rfl⟩) R26441
theorem R17641 : Reach 17641 := rs (se 2 (by rfl) ⟨6615, by rfl⟩) R13231
theorem R17673 : Reach 17673 := rs (se 2 (by rfl) ⟨6627, by rfl⟩) R13255
theorem R17695 : Reach 17695 := rs (se 1 (by rfl) ⟨13271, by rfl⟩) R26543
theorem R17703 : Reach 17703 := rs (se 1 (by rfl) ⟨13277, by rfl⟩) R26555
theorem R83243 : Reach 83243 := rs (se 1 (by rfl) ⟨62432, by rfl⟩) R124865
theorem R17755 : Reach 17755 := rs (se 1 (by rfl) ⟨13316, by rfl⟩) R26633
theorem R17775 : Reach 17775 := rs (se 1 (by rfl) ⟨13331, by rfl⟩) R26663
theorem R17787 : Reach 17787 := rs (se 1 (by rfl) ⟨13340, by rfl⟩) R26681
theorem R17801 : Reach 17801 := rs (se 2 (by rfl) ⟨6675, by rfl⟩) R13351
theorem R17831 : Reach 17831 := rs (se 1 (by rfl) ⟨13373, by rfl⟩) R26747
theorem R17863 : Reach 17863 := rs (se 1 (by rfl) ⟨13397, by rfl⟩) R26795
theorem R17913 : Reach 17913 := rs (se 2 (by rfl) ⟨6717, by rfl⟩) R13435
theorem R17915 : Reach 17915 := rs (se 1 (by rfl) ⟨13436, by rfl⟩) R26873
theorem R17983 : Reach 17983 := rs (se 1 (by rfl) ⟨13487, by rfl⟩) R26975
theorem R17991 : Reach 17991 := rs (se 1 (by rfl) ⟨13493, by rfl⟩) R26987
theorem R18015 : Reach 18015 := rs (se 1 (by rfl) ⟨13511, by rfl⟩) R27023
theorem R83591 : Reach 83591 := rs (se 1 (by rfl) ⟨62693, by rfl⟩) R125387
theorem R280253 : Reach 280253 := rs (se 3 (by rfl) ⟨52547, by rfl⟩) R105095
theorem R18155 : Reach 18155 := rs (se 1 (by rfl) ⟨13616, by rfl⟩) R27233
theorem R18217 : Reach 18217 := rs (se 2 (by rfl) ⟨6831, by rfl⟩) R13663
theorem R18223 : Reach 18223 := rs (se 1 (by rfl) ⟨13667, by rfl⟩) R27335
theorem R18231 : Reach 18231 := rs (se 1 (by rfl) ⟨13673, by rfl⟩) R27347
theorem R51151 : Reach 51151 := rs (se 1 (by rfl) ⟨38363, by rfl⟩) R76727
theorem R18383 : Reach 18383 := rs (se 1 (by rfl) ⟨13787, by rfl⟩) R27575
theorem R18537 : Reach 18537 := rs (se 2 (by rfl) ⟨6951, by rfl⟩) R13903
theorem R18697 : Reach 18697 := rs (se 2 (by rfl) ⟨7011, by rfl⟩) R14023
theorem R18779 : Reach 18779 := rs (se 1 (by rfl) ⟨14084, by rfl⟩) R28169
theorem R18799 : Reach 18799 := rs (se 1 (by rfl) ⟨14099, by rfl⟩) R28199
theorem R51623 : Reach 51623 := rs (se 1 (by rfl) ⟨38717, by rfl⟩) R77435
theorem R18855 : Reach 18855 := rs (se 1 (by rfl) ⟨14141, by rfl⟩) R28283
theorem R18939 : Reach 18939 := rs (se 1 (by rfl) ⟨14204, by rfl⟩) R28409
theorem R19007 : Reach 19007 := rs (se 1 (by rfl) ⟨14255, by rfl⟩) R28511
theorem R19015 : Reach 19015 := rs (se 1 (by rfl) ⟨14261, by rfl⟩) R28523
theorem R51785 : Reach 51785 := rs (se 2 (by rfl) ⟨19419, by rfl⟩) R38839
theorem R19051 : Reach 19051 := rs (se 1 (by rfl) ⟨14288, by rfl⟩) R28577
theorem R19065 : Reach 19065 := rs (se 2 (by rfl) ⟨7149, by rfl⟩) R14299
theorem R19119 : Reach 19119 := rs (se 1 (by rfl) ⟨14339, by rfl⟩) R28679
theorem R19127 : Reach 19127 := rs (se 1 (by rfl) ⟨14345, by rfl⟩) R28691
theorem R19167 : Reach 19167 := rs (se 1 (by rfl) ⟨14375, by rfl⟩) R28751
theorem R346913 : Reach 346913 := rs (se 2 (by rfl) ⟨130092, by rfl⟩) R260185
theorem R19279 : Reach 19279 := rs (se 1 (by rfl) ⟨14459, by rfl⟩) R28919
theorem R19355 : Reach 19355 := rs (se 1 (by rfl) ⟨14516, by rfl⟩) R29033
theorem R52123 : Reach 52123 := rs (se 1 (by rfl) ⟨39092, by rfl⟩) R78185
theorem R19431 : Reach 19431 := rs (se 1 (by rfl) ⟨14573, by rfl⟩) R29147
theorem R19675 : Reach 19675 := rs (se 1 (by rfl) ⟨14756, by rfl⟩) R29513
theorem R85211 : Reach 85211 := rs (se 1 (by rfl) ⟨63908, by rfl⟩) R127817
theorem R19689 : Reach 19689 := rs (se 2 (by rfl) ⟨7383, by rfl⟩) R14767
theorem R19743 : Reach 19743 := rs (se 1 (by rfl) ⟨14807, by rfl⟩) R29615
theorem R19751 : Reach 19751 := rs (se 1 (by rfl) ⟨14813, by rfl⟩) R29627
theorem R19835 : Reach 19835 := rs (se 1 (by rfl) ⟨14876, by rfl⟩) R29753
theorem R19849 : Reach 19849 := rs (se 2 (by rfl) ⟨7443, by rfl⟩) R14887
theorem R970157 : Reach 970157 := rs (se 3 (by rfl) ⟨181904, by rfl⟩) R363809
theorem R19911 : Reach 19911 := rs (se 1 (by rfl) ⟨14933, by rfl⟩) R29867
theorem R118235 : Reach 118235 := rs (se 1 (by rfl) ⟨88676, by rfl⟩) R177353
theorem R19961 : Reach 19961 := rs (se 2 (by rfl) ⟨7485, by rfl⟩) R14971
theorem R52751 : Reach 52751 := rs (se 1 (by rfl) ⟨39563, by rfl⟩) R79127
theorem R20063 : Reach 20063 := rs (se 1 (by rfl) ⟨15047, by rfl⟩) R30095
theorem R20279 : Reach 20279 := rs (se 1 (by rfl) ⟨15209, by rfl⟩) R30419
theorem R20281 : Reach 20281 := rs (se 2 (by rfl) ⟨7605, by rfl⟩) R15211
theorem R53149 : Reach 53149 := rs (se 3 (by rfl) ⟨9965, by rfl⟩) R19931
theorem R85981 : Reach 85981 := rs (se 3 (by rfl) ⟨16121, by rfl⟩) R32243
theorem R20585 : Reach 20585 := rs (se 2 (by rfl) ⟨7719, by rfl⟩) R15439
theorem R53459 : Reach 53459 := rs (se 1 (by rfl) ⟨40094, by rfl⟩) R80189
theorem R86345 : Reach 86345 := rs (se 2 (by rfl) ⟨32379, by rfl⟩) R64759
theorem R20827 : Reach 20827 := rs (se 1 (by rfl) ⟨15620, by rfl⟩) R31241
theorem R20903 : Reach 20903 := rs (se 1 (by rfl) ⟨15677, by rfl⟩) R31355
theorem R53729 : Reach 53729 := rs (se 2 (by rfl) ⟨20148, by rfl⟩) R40297
theorem R20987 : Reach 20987 := rs (se 1 (by rfl) ⟨15740, by rfl⟩) R31481
theorem R21055 : Reach 21055 := rs (se 1 (by rfl) ⟨15791, by rfl⟩) R31583
theorem R21065 : Reach 21065 := rs (se 2 (by rfl) ⟨7899, by rfl⟩) R15799
theorem R21113 : Reach 21113 := rs (se 2 (by rfl) ⟨7917, by rfl⟩) R15835
theorem R21167 : Reach 21167 := rs (se 1 (by rfl) ⟨15875, by rfl⟩) R31751
theorem R21215 : Reach 21215 := rs (se 1 (by rfl) ⟨15911, by rfl⟩) R31823
theorem R119717 : Reach 119717 := rs (se 4 (by rfl) ⟨11223, by rfl⟩) R22447
theorem R21419 : Reach 21419 := rs (se 1 (by rfl) ⟨16064, by rfl⟩) R32129
theorem R86993 : Reach 86993 := rs (se 2 (by rfl) ⟨32622, by rfl⟩) R65245
theorem R21479 : Reach 21479 := rs (se 1 (by rfl) ⟨16109, by rfl⟩) R32219
theorem R21647 : Reach 21647 := rs (se 1 (by rfl) ⟨16235, by rfl⟩) R32471
theorem R21737 : Reach 21737 := rs (se 2 (by rfl) ⟨8151, by rfl⟩) R16303
theorem R382201 : Reach 382201 := rs (se 2 (by rfl) ⟨143325, by rfl⟩) R286651
theorem R349433 : Reach 349433 := rs (se 2 (by rfl) ⟨131037, by rfl⟩) R262075
theorem R21791 : Reach 21791 := rs (se 1 (by rfl) ⟨16343, by rfl⟩) R32687
theorem R21799 : Reach 21799 := rs (se 1 (by rfl) ⟨16349, by rfl⟩) R32699
theorem R21883 : Reach 21883 := rs (se 1 (by rfl) ⟨16412, by rfl⟩) R32825
theorem R120203 : Reach 120203 := rs (se 1 (by rfl) ⟨90152, by rfl⟩) R180305
theorem R21959 : Reach 21959 := rs (se 1 (by rfl) ⟨16469, by rfl⟩) R32939
theorem R22009 : Reach 22009 := rs (se 2 (by rfl) ⟨8253, by rfl⟩) R16507
theorem R54971 : Reach 54971 := rs (se 1 (by rfl) ⟨41228, by rfl⟩) R82457
theorem R22279 : Reach 22279 := rs (se 1 (by rfl) ⟨16709, by rfl⟩) R33419
theorem R22313 : Reach 22313 := rs (se 2 (by rfl) ⟨8367, by rfl⟩) R16735
theorem R22319 : Reach 22319 := rs (se 1 (by rfl) ⟨16739, by rfl⟩) R33479
theorem R22793 : Reach 22793 := rs (se 2 (by rfl) ⟨8547, by rfl⟩) R17095
theorem R22895 : Reach 22895 := rs (se 1 (by rfl) ⟨17171, by rfl⟩) R34343
theorem R22951 : Reach 22951 := rs (se 1 (by rfl) ⟨17213, by rfl⟩) R34427
theorem R23009 : Reach 23009 := rs (se 2 (by rfl) ⟨8628, by rfl⟩) R17257
theorem R23111 : Reach 23111 := rs (se 1 (by rfl) ⟨17333, by rfl⟩) R34667
theorem R23147 : Reach 23147 := rs (se 1 (by rfl) ⟨17360, by rfl⟩) R34721
theorem R23161 : Reach 23161 := rs (se 2 (by rfl) ⟨8685, by rfl⟩) R17371
theorem R55997 : Reach 55997 := rs (se 3 (by rfl) ⟨10499, by rfl⟩) R20999
theorem R23315 : Reach 23315 := rs (se 1 (by rfl) ⟨17486, by rfl⟩) R34973
theorem R23375 : Reach 23375 := rs (se 1 (by rfl) ⟨17531, by rfl⟩) R35063
theorem R89075 : Reach 89075 := rs (se 1 (by rfl) ⟨66806, by rfl⟩) R133613
theorem R23543 : Reach 23543 := rs (se 1 (by rfl) ⟨17657, by rfl⟩) R35315
theorem R56435 : Reach 56435 := rs (se 1 (by rfl) ⟨42326, by rfl⟩) R84653
theorem R23771 : Reach 23771 := rs (se 1 (by rfl) ⟨17828, by rfl⟩) R35657
theorem R23905 : Reach 23905 := rs (se 2 (by rfl) ⟨8964, by rfl⟩) R17929
theorem R23945 : Reach 23945 := rs (se 2 (by rfl) ⟨8979, by rfl⟩) R17959
theorem R56915 : Reach 56915 := rs (se 1 (by rfl) ⟨42686, by rfl⟩) R85373
theorem R24251 : Reach 24251 := rs (se 1 (by rfl) ⟨18188, by rfl⟩) R36377
theorem R24299 : Reach 24299 := rs (se 1 (by rfl) ⟨18224, by rfl⟩) R36449
theorem R24367 : Reach 24367 := rs (se 1 (by rfl) ⟨18275, by rfl⟩) R36551
theorem R24377 : Reach 24377 := rs (se 2 (by rfl) ⟨9141, by rfl⟩) R18283
theorem R188219 : Reach 188219 := rs (se 1 (by rfl) ⟨141164, by rfl⟩) R282329
theorem R90031 : Reach 90031 := rs (se 1 (by rfl) ⟨67523, by rfl⟩) R135047
theorem R24527 : Reach 24527 := rs (se 1 (by rfl) ⟨18395, by rfl⟩) R36791
theorem R122917 : Reach 122917 := rs (se 4 (by rfl) ⟨11523, by rfl⟩) R23047
theorem R778481 : Reach 778481 := rs (se 2 (by rfl) ⟨291930, by rfl⟩) R583861
theorem R24923 : Reach 24923 := rs (se 1 (by rfl) ⟨18692, by rfl⟩) R37385
theorem R24943 : Reach 24943 := rs (se 1 (by rfl) ⟨18707, by rfl⟩) R37415
theorem R25043 : Reach 25043 := rs (se 1 (by rfl) ⟨18782, by rfl⟩) R37565
theorem R25151 : Reach 25151 := rs (se 1 (by rfl) ⟨18863, by rfl⟩) R37727
theorem R25271 : Reach 25271 := rs (se 1 (by rfl) ⟨18953, by rfl⟩) R37907
theorem R25363 : Reach 25363 := rs (se 1 (by rfl) ⟨19022, by rfl⟩) R38045
theorem R25499 : Reach 25499 := rs (se 1 (by rfl) ⟨19124, by rfl⟩) R38249
theorem R25591 : Reach 25591 := rs (se 1 (by rfl) ⟨19193, by rfl⟩) R38387
theorem R189539 : Reach 189539 := rs (se 1 (by rfl) ⟨142154, by rfl⟩) R284309
theorem R58583 : Reach 58583 := rs (se 1 (by rfl) ⟨43937, by rfl⟩) R87875
theorem R25895 : Reach 25895 := rs (se 1 (by rfl) ⟨19421, by rfl⟩) R38843
theorem R25979 : Reach 25979 := rs (se 1 (by rfl) ⟨19484, by rfl⟩) R38969
theorem R26105 : Reach 26105 := rs (se 2 (by rfl) ⟨9789, by rfl⟩) R19579
theorem R58913 : Reach 58913 := rs (se 2 (by rfl) ⟨22092, by rfl⟩) R44185
theorem R26195 : Reach 26195 := rs (se 1 (by rfl) ⟨19646, by rfl⟩) R39293
theorem R26207 : Reach 26207 := rs (se 1 (by rfl) ⟨19655, by rfl⟩) R39311
theorem R26273 : Reach 26273 := rs (se 2 (by rfl) ⟨9852, by rfl⟩) R19705
theorem R26347 : Reach 26347 := rs (se 1 (by rfl) ⟨19760, by rfl⟩) R39521
theorem R26375 : Reach 26375 := rs (se 1 (by rfl) ⟨19781, by rfl⟩) R39563
theorem R59165 : Reach 59165 := rs (se 3 (by rfl) ⟨11093, by rfl⟩) R22187
theorem R26423 : Reach 26423 := rs (se 1 (by rfl) ⟨19817, by rfl⟩) R39635
theorem R26729 : Reach 26729 := rs (se 2 (by rfl) ⟨10023, by rfl⟩) R20047
theorem R125327 : Reach 125327 := rs (se 1 (by rfl) ⟨93995, by rfl⟩) R187991
theorem R27047 : Reach 27047 := rs (se 1 (by rfl) ⟨20285, by rfl⟩) R40571
theorem R59831 : Reach 59831 := rs (se 1 (by rfl) ⟨44873, by rfl⟩) R89747
theorem R59899 : Reach 59899 := rs (se 1 (by rfl) ⟨44924, by rfl⟩) R89849
theorem R27131 : Reach 27131 := rs (se 1 (by rfl) ⟨20348, by rfl⟩) R40697
theorem R27155 : Reach 27155 := rs (se 1 (by rfl) ⟨20366, by rfl⟩) R40733
theorem R27199 : Reach 27199 := rs (se 1 (by rfl) ⟨20399, by rfl⟩) R40799
theorem R27209 : Reach 27209 := rs (se 2 (by rfl) ⟨10203, by rfl⟩) R20407
theorem R27215 : Reach 27215 := rs (se 1 (by rfl) ⟨20411, by rfl⟩) R40823
theorem R27257 : Reach 27257 := rs (se 2 (by rfl) ⟨10221, by rfl⟩) R20443
theorem R27307 : Reach 27307 := rs (se 1 (by rfl) ⟨20480, by rfl⟩) R40961
theorem R27311 : Reach 27311 := rs (se 1 (by rfl) ⟨20483, by rfl⟩) R40967
theorem R27359 : Reach 27359 := rs (se 1 (by rfl) ⟨20519, by rfl⟩) R41039
theorem R27383 : Reach 27383 := rs (se 1 (by rfl) ⟨20537, by rfl⟩) R41075
theorem R93053 : Reach 93053 := rs (se 3 (by rfl) ⟨17447, by rfl⟩) R34895
theorem R27535 : Reach 27535 := rs (se 1 (by rfl) ⟨20651, by rfl⟩) R41303
theorem R224153 : Reach 224153 := rs (se 2 (by rfl) ⟨84057, by rfl⟩) R168115
theorem R27563 : Reach 27563 := rs (se 1 (by rfl) ⟨20672, by rfl⟩) R41345
theorem R27611 : Reach 27611 := rs (se 1 (by rfl) ⟨20708, by rfl⟩) R41417
theorem R27623 : Reach 27623 := rs (se 1 (by rfl) ⟨20717, by rfl⟩) R41435
theorem R158797 : Reach 158797 := rs (se 3 (by rfl) ⟨29774, by rfl⟩) R59549
theorem R27791 : Reach 27791 := rs (se 1 (by rfl) ⟨20843, by rfl⟩) R41687
theorem R27881 : Reach 27881 := rs (se 2 (by rfl) ⟨10455, by rfl⟩) R20911
theorem R27935 : Reach 27935 := rs (se 1 (by rfl) ⟨20951, by rfl⟩) R41903
theorem R28001 : Reach 28001 := rs (se 2 (by rfl) ⟨10500, by rfl⟩) R21001
theorem R28091 : Reach 28091 := rs (se 1 (by rfl) ⟨21068, by rfl⟩) R42137
theorem R60871 : Reach 60871 := rs (se 1 (by rfl) ⟨45653, by rfl⟩) R91307
theorem R28103 : Reach 28103 := rs (se 1 (by rfl) ⟨21077, by rfl⟩) R42155
theorem R60887 : Reach 60887 := rs (se 1 (by rfl) ⟨45665, by rfl⟩) R91331
theorem R28217 : Reach 28217 := rs (se 2 (by rfl) ⟨10581, by rfl⟩) R21163
theorem R28255 : Reach 28255 := rs (se 1 (by rfl) ⟨21191, by rfl⟩) R42383
theorem R93905 : Reach 93905 := rs (se 2 (by rfl) ⟨35214, by rfl⟩) R70429
theorem R28457 : Reach 28457 := rs (se 2 (by rfl) ⟨10671, by rfl⟩) R21343
theorem R28463 : Reach 28463 := rs (se 1 (by rfl) ⟨21347, by rfl⟩) R42695
theorem R28471 : Reach 28471 := rs (se 1 (by rfl) ⟨21353, by rfl⟩) R42707
theorem R61499 : Reach 61499 := rs (se 1 (by rfl) ⟨46124, by rfl⟩) R92249
theorem R28883 : Reach 28883 := rs (se 1 (by rfl) ⟨21662, by rfl⟩) R43325
theorem R28937 : Reach 28937 := rs (se 2 (by rfl) ⟨10851, by rfl⟩) R21703
theorem R29035 : Reach 29035 := rs (se 1 (by rfl) ⟨21776, by rfl⟩) R43553
theorem R29039 : Reach 29039 := rs (se 1 (by rfl) ⟨21779, by rfl⟩) R43559
theorem R29111 : Reach 29111 := rs (se 1 (by rfl) ⟨21833, by rfl⟩) R43667
theorem R29153 : Reach 29153 := rs (se 2 (by rfl) ⟨10932, by rfl⟩) R21865
theorem R94769 : Reach 94769 := rs (se 2 (by rfl) ⟨35538, by rfl⟩) R71077
theorem R29255 : Reach 29255 := rs (se 1 (by rfl) ⟨21941, by rfl⟩) R43883
theorem R29263 : Reach 29263 := rs (se 1 (by rfl) ⟨21947, by rfl⟩) R43895
theorem R29291 : Reach 29291 := rs (se 1 (by rfl) ⟨21968, by rfl⟩) R43937
theorem R62099 : Reach 62099 := rs (se 1 (by rfl) ⟨46574, by rfl⟩) R93149
theorem R29459 : Reach 29459 := rs (se 1 (by rfl) ⟨22094, by rfl⟩) R44189
theorem R29519 : Reach 29519 := rs (se 1 (by rfl) ⟨22139, by rfl⟩) R44279
theorem R914327 : Reach 914327 := rs (se 1 (by rfl) ⟨685745, by rfl⟩) R1371491
theorem R62369 : Reach 62369 := rs (se 2 (by rfl) ⟨23388, by rfl⟩) R46777
theorem R29659 : Reach 29659 := rs (se 1 (by rfl) ⟨22244, by rfl⟩) R44489
theorem R29687 : Reach 29687 := rs (se 1 (by rfl) ⟨22265, by rfl⟩) R44531
theorem R29735 : Reach 29735 := rs (se 1 (by rfl) ⟨22301, by rfl⟩) R44603
theorem R95321 : Reach 95321 := rs (se 2 (by rfl) ⟨35745, by rfl⟩) R71491
theorem R29819 : Reach 29819 := rs (se 1 (by rfl) ⟨22364, by rfl⟩) R44729
theorem R29915 : Reach 29915 := rs (se 1 (by rfl) ⟨22436, by rfl⟩) R44873
theorem R29929 : Reach 29929 := rs (se 2 (by rfl) ⟨11223, by rfl⟩) R22447
theorem R128249 : Reach 128249 := rs (se 2 (by rfl) ⟨48093, by rfl⟩) R96187
theorem R29945 : Reach 29945 := rs (se 2 (by rfl) ⟨11229, by rfl⟩) R22459
theorem R29983 : Reach 29983 := rs (se 1 (by rfl) ⟨22487, by rfl⟩) R44975
theorem R62815 : Reach 62815 := rs (se 1 (by rfl) ⟨47111, by rfl⟩) R94223
theorem R30113 : Reach 30113 := rs (se 2 (by rfl) ⟨11292, by rfl⟩) R22585
theorem R62909 : Reach 62909 := rs (se 3 (by rfl) ⟨11795, by rfl⟩) R23591
theorem R95681 : Reach 95681 := rs (se 2 (by rfl) ⟨35880, by rfl⟩) R71761
theorem R30395 : Reach 30395 := rs (se 1 (by rfl) ⟨22796, by rfl⟩) R45593
theorem R63287 : Reach 63287 := rs (se 1 (by rfl) ⟨47465, by rfl⟩) R94931
theorem R30671 : Reach 30671 := rs (se 1 (by rfl) ⟨23003, by rfl⟩) R46007
theorem R96335 : Reach 96335 := rs (se 1 (by rfl) ⟨72251, by rfl⟩) R144503
theorem R63623 : Reach 63623 := rs (se 1 (by rfl) ⟨47717, by rfl⟩) R95435
theorem R63773 : Reach 63773 := rs (se 3 (by rfl) ⟨11957, by rfl⟩) R23915
theorem R194885 : Reach 194885 := rs (se 4 (by rfl) ⟨18270, by rfl⟩) R36541
theorem R31049 : Reach 31049 := rs (se 2 (by rfl) ⟨11643, by rfl⟩) R23287
theorem R31067 : Reach 31067 := rs (se 1 (by rfl) ⟨23300, by rfl⟩) R46601
theorem R31151 : Reach 31151 := rs (se 1 (by rfl) ⟨23363, by rfl⟩) R46727
theorem R64073 : Reach 64073 := rs (se 2 (by rfl) ⟨24027, by rfl⟩) R48055
theorem R96875 : Reach 96875 := rs (se 1 (by rfl) ⟨72656, by rfl⟩) R145313
theorem R31643 : Reach 31643 := rs (se 1 (by rfl) ⟨23732, by rfl⟩) R47465
theorem R1276901 : Reach 1276901 := rs (se 4 (by rfl) ⟨119709, by rfl⟩) R239419
theorem R31841 : Reach 31841 := rs (se 2 (by rfl) ⟨11940, by rfl⟩) R23881
theorem R64799 : Reach 64799 := rs (se 1 (by rfl) ⟨48599, by rfl⟩) R97199
theorem R32039 : Reach 32039 := rs (se 1 (by rfl) ⟨24029, by rfl⟩) R48059
theorem R32123 : Reach 32123 := rs (se 1 (by rfl) ⟨24092, by rfl⟩) R48185
theorem R65033 : Reach 65033 := rs (se 2 (by rfl) ⟨24387, by rfl⟩) R48775
theorem R196177 : Reach 196177 := rs (se 2 (by rfl) ⟨73566, by rfl⟩) R147133
theorem R32339 : Reach 32339 := rs (se 1 (by rfl) ⟨24254, by rfl⟩) R48509
theorem R32417 : Reach 32417 := rs (se 2 (by rfl) ⟨12156, by rfl⟩) R24313
theorem R32567 : Reach 32567 := rs (se 1 (by rfl) ⟨24425, by rfl⟩) R48851
theorem R163889 : Reach 163889 := rs (se 2 (by rfl) ⟨61458, by rfl⟩) R122917
theorem R32987 : Reach 32987 := rs (se 1 (by rfl) ⟨24740, by rfl⟩) R49481
theorem R65815 : Reach 65815 := rs (se 1 (by rfl) ⟨49361, by rfl⟩) R98723
theorem R33223 : Reach 33223 := rs (se 1 (by rfl) ⟨24917, by rfl⟩) R49835
theorem R98779 : Reach 98779 := rs (se 1 (by rfl) ⟨74084, by rfl⟩) R148169
theorem R33257 : Reach 33257 := rs (se 2 (by rfl) ⟨12471, by rfl⟩) R24943
theorem R33515 : Reach 33515 := rs (se 1 (by rfl) ⟨25136, by rfl⟩) R50273
theorem R66491 : Reach 66491 := rs (se 1 (by rfl) ⟨49868, by rfl⟩) R99737
theorem R33817 : Reach 33817 := rs (se 2 (by rfl) ⟨12681, by rfl⟩) R25363
theorem R34121 : Reach 34121 := rs (se 2 (by rfl) ⟨12795, by rfl⟩) R25591
theorem R67097 : Reach 67097 := rs (se 2 (by rfl) ⟨25161, by rfl⟩) R50323
theorem R34415 : Reach 34415 := rs (se 1 (by rfl) ⟨25811, by rfl⟩) R51623
theorem R34523 : Reach 34523 := rs (se 1 (by rfl) ⟨25892, by rfl⟩) R51785
theorem R231275 : Reach 231275 := rs (se 1 (by rfl) ⟨173456, by rfl⟩) R346913
theorem R133163 : Reach 133163 := rs (se 1 (by rfl) ⟨99872, by rfl⟩) R199745
theorem R35129 : Reach 35129 := rs (se 2 (by rfl) ⟨13173, by rfl⟩) R26347
theorem R67931 : Reach 67931 := rs (se 1 (by rfl) ⟨50948, by rfl⟩) R101897
theorem R35167 : Reach 35167 := rs (se 1 (by rfl) ⟨26375, by rfl⟩) R52751
theorem R68201 : Reach 68201 := rs (se 2 (by rfl) ⟨25575, by rfl⟩) R51151
theorem R101009 : Reach 101009 := rs (se 2 (by rfl) ⟨37878, by rfl⟩) R75757
theorem R35639 : Reach 35639 := rs (se 1 (by rfl) ⟨26729, by rfl⟩) R53459
theorem R35819 : Reach 35819 := rs (se 1 (by rfl) ⟨26864, by rfl⟩) R53729
theorem R232955 : Reach 232955 := rs (se 1 (by rfl) ⟨174716, by rfl⟩) R349433
theorem R36409 : Reach 36409 := rs (se 2 (by rfl) ⟨13653, by rfl⟩) R27307
theorem R101969 : Reach 101969 := rs (se 2 (by rfl) ⟨38238, by rfl⟩) R76477
theorem R36647 : Reach 36647 := rs (se 1 (by rfl) ⟨27485, by rfl⟩) R54971
theorem R102221 : Reach 102221 := rs (se 3 (by rfl) ⟨19166, by rfl⟩) R38333
theorem R36713 : Reach 36713 := rs (se 2 (by rfl) ⟨13767, by rfl⟩) R27535
theorem R69497 : Reach 69497 := rs (se 2 (by rfl) ⟨26061, by rfl⟩) R52123
theorem R135587 : Reach 135587 := rs (se 1 (by rfl) ⟨101690, by rfl⟩) R203381
theorem R37331 : Reach 37331 := rs (se 1 (by rfl) ⟨27998, by rfl⟩) R55997
theorem R37673 : Reach 37673 := rs (se 2 (by rfl) ⟨14127, by rfl⟩) R28255
theorem R37943 : Reach 37943 := rs (se 1 (by rfl) ⟨28457, by rfl⟩) R56915
theorem R37961 : Reach 37961 := rs (se 2 (by rfl) ⟨14235, by rfl⟩) R28471
theorem R70865 : Reach 70865 := rs (se 2 (by rfl) ⟨26574, by rfl⟩) R53149
theorem R169661 : Reach 169661 := rs (se 3 (by rfl) ⟨31811, by rfl⟩) R63623
theorem R38713 : Reach 38713 := rs (se 2 (by rfl) ⟨14517, by rfl⟩) R29035
theorem R39017 : Reach 39017 := rs (se 2 (by rfl) ⟨14631, by rfl⟩) R29263
theorem R39055 : Reach 39055 := rs (se 1 (by rfl) ⟨29291, by rfl⟩) R58583
theorem R39275 : Reach 39275 := rs (se 1 (by rfl) ⟨29456, by rfl⟩) R58913
theorem R72103 : Reach 72103 := rs (se 1 (by rfl) ⟨54077, by rfl⟩) R108155
theorem R39443 : Reach 39443 := rs (se 1 (by rfl) ⟨29582, by rfl⟩) R59165
theorem R39545 : Reach 39545 := rs (se 2 (by rfl) ⟨14829, by rfl⟩) R29659
theorem R2038405 : Reach 2038405 := rs (se 4 (by rfl) ⟨191100, by rfl⟩) R382201
theorem R39581 : Reach 39581 := rs (se 3 (by rfl) ⟨7421, by rfl⟩) R14843
theorem R72413 : Reach 72413 := rs (se 3 (by rfl) ⟨13577, by rfl⟩) R27155
theorem R301805 : Reach 301805 := rs (se 3 (by rfl) ⟨56588, by rfl⟩) R113177
theorem R39887 : Reach 39887 := rs (se 1 (by rfl) ⟨29915, by rfl⟩) R59831
theorem R39905 : Reach 39905 := rs (se 2 (by rfl) ⟨14964, by rfl⟩) R29929
theorem R39977 : Reach 39977 := rs (se 2 (by rfl) ⟨14991, by rfl⟩) R29983
theorem R40061 : Reach 40061 := rs (se 3 (by rfl) ⟨7511, by rfl⟩) R15023
theorem R73021 : Reach 73021 := rs (se 3 (by rfl) ⟨13691, by rfl⟩) R27383
theorem R73295 : Reach 73295 := rs (se 1 (by rfl) ⟨54971, by rfl⟩) R109943
theorem R40591 : Reach 40591 := rs (se 1 (by rfl) ⟨30443, by rfl⟩) R60887
theorem R138995 : Reach 138995 := rs (se 1 (by rfl) ⟨104246, by rfl⟩) R208493
theorem R40999 : Reach 40999 := rs (se 1 (by rfl) ⟨30749, by rfl⟩) R61499
theorem R270641 : Reach 270641 := rs (se 2 (by rfl) ⟨101490, by rfl⟩) R202981
theorem R41399 : Reach 41399 := rs (se 1 (by rfl) ⟨31049, by rfl⟩) R62099
theorem R107081 : Reach 107081 := rs (se 2 (by rfl) ⟨40155, by rfl⟩) R80311
theorem R41579 : Reach 41579 := rs (se 1 (by rfl) ⟨31184, by rfl⟩) R62369
theorem R140089 : Reach 140089 := rs (se 2 (by rfl) ⟨52533, by rfl⟩) R105067
theorem R41885 : Reach 41885 := rs (se 3 (by rfl) ⟨7853, by rfl⟩) R15707
theorem R41939 : Reach 41939 := rs (se 1 (by rfl) ⟨31454, by rfl⟩) R62909
theorem R42173 : Reach 42173 := rs (se 3 (by rfl) ⟨7907, by rfl⟩) R15815
theorem R42191 : Reach 42191 := rs (se 1 (by rfl) ⟨31643, by rfl⟩) R63287
theorem R42493 : Reach 42493 := rs (se 3 (by rfl) ⟨7967, by rfl⟩) R15935
theorem R42515 : Reach 42515 := rs (se 1 (by rfl) ⟨31886, by rfl⟩) R63773
theorem R140939 : Reach 140939 := rs (se 1 (by rfl) ⟨105704, by rfl⟩) R211409
theorem R75451 : Reach 75451 := rs (se 1 (by rfl) ⟨56588, by rfl⟩) R113177
theorem R42715 : Reach 42715 := rs (se 1 (by rfl) ⟨32036, by rfl⟩) R64073
theorem R75923 : Reach 75923 := rs (se 1 (by rfl) ⟨56942, by rfl⟩) R113885
theorem R43199 : Reach 43199 := rs (se 1 (by rfl) ⟨32399, by rfl⟩) R64799
theorem R75991 : Reach 75991 := rs (se 1 (by rfl) ⟨56993, by rfl⟩) R113987
theorem R43355 : Reach 43355 := rs (se 1 (by rfl) ⟨32516, by rfl⟩) R65033
theorem R76463 : Reach 76463 := rs (se 1 (by rfl) ⟨57347, by rfl⟩) R114695
theorem R43703 : Reach 43703 := rs (se 1 (by rfl) ⟨32777, by rfl⟩) R65555
theorem R142019 : Reach 142019 := rs (se 1 (by rfl) ⟨106514, by rfl⟩) R213029
theorem R43831 : Reach 43831 := rs (se 1 (by rfl) ⟨32873, by rfl⟩) R65747
theorem R404291 : Reach 404291 := rs (se 1 (by rfl) ⟨303218, by rfl⟩) R606437
theorem R44153 : Reach 44153 := rs (se 2 (by rfl) ⟨16557, by rfl⟩) R33115
theorem R109835 : Reach 109835 := rs (se 1 (by rfl) ⟨82376, by rfl⟩) R164753
theorem R44477 : Reach 44477 := rs (se 3 (by rfl) ⟨8339, by rfl⟩) R16679
theorem R765449 : Reach 765449 := rs (se 2 (by rfl) ⟨287043, by rfl⟩) R574087
theorem R44651 : Reach 44651 := rs (se 1 (by rfl) ⟨33488, by rfl⟩) R66977
theorem R44819 : Reach 44819 := rs (se 1 (by rfl) ⟨33614, by rfl⟩) R67229
theorem R143369 : Reach 143369 := rs (se 2 (by rfl) ⟨53763, by rfl⟩) R107527
theorem R602245 : Reach 602245 := rs (se 4 (by rfl) ⟨56460, by rfl⟩) R112921
theorem R45479 : Reach 45479 := rs (se 1 (by rfl) ⟨34109, by rfl⟩) R68219
theorem R45647 : Reach 45647 := rs (se 1 (by rfl) ⟨34235, by rfl⟩) R68471
theorem R12903 : Reach 12903 := rs (se 1 (by rfl) ⟨9677, by rfl⟩) R19355
theorem R45683 : Reach 45683 := rs (se 1 (by rfl) ⟨34262, by rfl⟩) R68525
theorem R45815 : Reach 45815 := rs (se 1 (by rfl) ⟨34361, by rfl⟩) R68723
theorem R13167 : Reach 13167 := rs (se 1 (by rfl) ⟨9875, by rfl⟩) R19751
theorem R45953 : Reach 45953 := rs (se 2 (by rfl) ⟨17232, by rfl⟩) R34465
theorem R13223 : Reach 13223 := rs (se 1 (by rfl) ⟨9917, by rfl⟩) R19835
theorem R78823 : Reach 78823 := rs (se 1 (by rfl) ⟨59117, by rfl⟩) R118235
theorem R13307 : Reach 13307 := rs (se 1 (by rfl) ⟨9980, by rfl⟩) R19961
theorem R13375 : Reach 13375 := rs (se 1 (by rfl) ⟨10031, by rfl⟩) R20063
theorem R13519 : Reach 13519 := rs (se 1 (by rfl) ⟨10139, by rfl⟩) R20279
theorem R46291 : Reach 46291 := rs (se 1 (by rfl) ⟨34718, by rfl⟩) R69437
theorem R46433 : Reach 46433 := rs (se 2 (by rfl) ⟨17412, by rfl⟩) R34825
theorem R13723 : Reach 13723 := rs (se 1 (by rfl) ⟨10292, by rfl⟩) R20585
theorem R13935 : Reach 13935 := rs (se 1 (by rfl) ⟨10451, by rfl⟩) R20903
theorem R145061 : Reach 145061 := rs (se 4 (by rfl) ⟨13599, by rfl⟩) R27199
theorem R13991 : Reach 13991 := rs (se 1 (by rfl) ⟨10493, by rfl⟩) R20987
theorem R46763 : Reach 46763 := rs (se 1 (by rfl) ⟨35072, by rfl⟩) R70145
theorem R177875 : Reach 177875 := rs (se 1 (by rfl) ⟨133406, by rfl⟩) R266813
theorem R14043 : Reach 14043 := rs (se 1 (by rfl) ⟨10532, by rfl⟩) R21065
theorem R14075 : Reach 14075 := rs (se 1 (by rfl) ⟨10556, by rfl⟩) R21113
theorem R14111 : Reach 14111 := rs (se 1 (by rfl) ⟨10583, by rfl⟩) R21167
theorem R14143 : Reach 14143 := rs (se 1 (by rfl) ⟨10607, by rfl⟩) R21215
theorem R145297 : Reach 145297 := rs (se 2 (by rfl) ⟨54486, by rfl⟩) R108973
theorem R79811 : Reach 79811 := rs (se 1 (by rfl) ⟨59858, by rfl⟩) R119717
theorem R14279 : Reach 14279 := rs (se 1 (by rfl) ⟨10709, by rfl⟩) R21419
theorem R47087 : Reach 47087 := rs (se 1 (by rfl) ⟨35315, by rfl⟩) R70631
theorem R14319 : Reach 14319 := rs (se 1 (by rfl) ⟨10739, by rfl⟩) R21479
theorem R79865 : Reach 79865 := rs (se 2 (by rfl) ⟨29949, by rfl⟩) R59899
theorem R14431 : Reach 14431 := rs (se 1 (by rfl) ⟨10823, by rfl⟩) R21647
theorem R47209 : Reach 47209 := rs (se 2 (by rfl) ⟨17703, by rfl⟩) R35407
theorem R14491 : Reach 14491 := rs (se 1 (by rfl) ⟨10868, by rfl⟩) R21737
theorem R14527 : Reach 14527 := rs (se 1 (by rfl) ⟨10895, by rfl⟩) R21791
theorem R47303 : Reach 47303 := rs (se 1 (by rfl) ⟨35477, by rfl⟩) R70955
theorem R80135 : Reach 80135 := rs (se 1 (by rfl) ⟨60101, by rfl⟩) R120203
theorem R14639 : Reach 14639 := rs (se 1 (by rfl) ⟨10979, by rfl⟩) R21959
theorem R14875 : Reach 14875 := rs (se 1 (by rfl) ⟨11156, by rfl⟩) R22313
theorem R14879 : Reach 14879 := rs (se 1 (by rfl) ⟨11159, by rfl⟩) R22319
theorem R211729 : Reach 211729 := rs (se 2 (by rfl) ⟨79398, by rfl⟩) R158797
theorem R47951 : Reach 47951 := rs (se 1 (by rfl) ⟨35963, by rfl⟩) R71927
theorem R15195 : Reach 15195 := rs (se 1 (by rfl) ⟨11396, by rfl⟩) R22793
theorem R15263 : Reach 15263 := rs (se 1 (by rfl) ⟨11447, by rfl⟩) R22895
theorem R113615 : Reach 113615 := rs (se 1 (by rfl) ⟨85211, by rfl⟩) R170423
theorem R15339 : Reach 15339 := rs (se 1 (by rfl) ⟨11504, by rfl⟩) R23009
theorem R15407 : Reach 15407 := rs (se 1 (by rfl) ⟨11555, by rfl⟩) R23111
theorem R15431 : Reach 15431 := rs (se 1 (by rfl) ⟨11573, by rfl⟩) R23147
theorem R15543 : Reach 15543 := rs (se 1 (by rfl) ⟨11657, by rfl⟩) R23315
theorem R15583 : Reach 15583 := rs (se 1 (by rfl) ⟨11687, by rfl⟩) R23375
theorem R48377 : Reach 48377 := rs (se 2 (by rfl) ⟨18141, by rfl⟩) R36283
theorem R81161 : Reach 81161 := rs (se 2 (by rfl) ⟨30435, by rfl⟩) R60871
theorem R15695 : Reach 15695 := rs (se 1 (by rfl) ⟨11771, by rfl⟩) R23543
theorem R15847 : Reach 15847 := rs (se 1 (by rfl) ⟨11885, by rfl⟩) R23771
theorem R15963 : Reach 15963 := rs (se 1 (by rfl) ⟨11972, by rfl⟩) R23945
theorem R16167 : Reach 16167 := rs (se 1 (by rfl) ⟨12125, by rfl⟩) R24251
theorem R16199 : Reach 16199 := rs (se 1 (by rfl) ⟨12149, by rfl⟩) R24299
theorem R16251 : Reach 16251 := rs (se 1 (by rfl) ⟨12188, by rfl⟩) R24377
theorem R114641 : Reach 114641 := rs (se 2 (by rfl) ⟨42990, by rfl⟩) R85981
theorem R16351 : Reach 16351 := rs (se 1 (by rfl) ⟨12263, by rfl⟩) R24527
theorem R311435 : Reach 311435 := rs (se 1 (by rfl) ⟨233576, by rfl⟩) R467153
theorem R16615 : Reach 16615 := rs (se 1 (by rfl) ⟨12461, by rfl⟩) R24923
theorem R16695 : Reach 16695 := rs (se 1 (by rfl) ⟨12521, by rfl⟩) R25043
theorem R16767 : Reach 16767 := rs (se 1 (by rfl) ⟨12575, by rfl⟩) R25151
theorem R115127 : Reach 115127 := rs (se 1 (by rfl) ⟨86345, by rfl⟩) R172691
theorem R16847 : Reach 16847 := rs (se 1 (by rfl) ⟨12635, by rfl⟩) R25271
theorem R115181 : Reach 115181 := rs (se 3 (by rfl) ⟨21596, by rfl⟩) R43193
theorem R16999 : Reach 16999 := rs (se 1 (by rfl) ⟨12749, by rfl⟩) R25499
theorem R17161 : Reach 17161 := rs (se 2 (by rfl) ⟨6435, by rfl⟩) R12871
theorem R49967 : Reach 49967 := rs (se 1 (by rfl) ⟨37475, by rfl⟩) R74951
theorem R17263 : Reach 17263 := rs (se 1 (by rfl) ⟨12947, by rfl⟩) R25895
theorem R17319 : Reach 17319 := rs (se 1 (by rfl) ⟨12989, by rfl⟩) R25979
theorem R115667 : Reach 115667 := rs (se 1 (by rfl) ⟨86750, by rfl⟩) R173501
theorem R17403 : Reach 17403 := rs (se 1 (by rfl) ⟨13052, by rfl⟩) R26105
theorem R17463 : Reach 17463 := rs (se 1 (by rfl) ⟨13097, by rfl⟩) R26195
theorem R17471 : Reach 17471 := rs (se 1 (by rfl) ⟨13103, by rfl⟩) R26207
theorem R17515 : Reach 17515 := rs (se 1 (by rfl) ⟨13136, by rfl⟩) R26273
theorem R148625 : Reach 148625 := rs (se 2 (by rfl) ⟨55734, by rfl⟩) R111469
theorem R17583 : Reach 17583 := rs (se 1 (by rfl) ⟨13187, by rfl⟩) R26375
theorem R17615 : Reach 17615 := rs (se 1 (by rfl) ⟨13211, by rfl⟩) R26423
theorem R17819 : Reach 17819 := rs (se 1 (by rfl) ⟨13364, by rfl⟩) R26729
theorem R83551 : Reach 83551 := rs (se 1 (by rfl) ⟨62663, by rfl⟩) R125327
theorem R18031 : Reach 18031 := rs (se 1 (by rfl) ⟨13523, by rfl⟩) R27047
theorem R18041 : Reach 18041 := rs (se 2 (by rfl) ⟨6765, by rfl⟩) R13531
theorem R18087 : Reach 18087 := rs (se 1 (by rfl) ⟨13565, by rfl⟩) R27131
theorem R18103 : Reach 18103 := rs (se 1 (by rfl) ⟨13577, by rfl⟩) R27155
theorem R18139 : Reach 18139 := rs (se 1 (by rfl) ⟨13604, by rfl⟩) R27209
theorem R18143 : Reach 18143 := rs (se 1 (by rfl) ⟨13607, by rfl⟩) R27215
theorem R18171 : Reach 18171 := rs (se 1 (by rfl) ⟨13628, by rfl⟩) R27257
theorem R18207 : Reach 18207 := rs (se 1 (by rfl) ⟨13655, by rfl⟩) R27311
theorem R83753 : Reach 83753 := rs (se 2 (by rfl) ⟨31407, by rfl⟩) R62815
theorem R18239 : Reach 18239 := rs (se 1 (by rfl) ⟨13679, by rfl⟩) R27359
theorem R18255 : Reach 18255 := rs (se 1 (by rfl) ⟨13691, by rfl⟩) R27383
theorem R18313 : Reach 18313 := rs (se 2 (by rfl) ⟨6867, by rfl⟩) R13735
theorem R149435 : Reach 149435 := rs (se 1 (by rfl) ⟨112076, by rfl⟩) R224153
theorem R18375 : Reach 18375 := rs (se 1 (by rfl) ⟨13781, by rfl⟩) R27563
theorem R411601 : Reach 411601 := rs (se 2 (by rfl) ⟨154350, by rfl⟩) R308701
theorem R18407 : Reach 18407 := rs (se 1 (by rfl) ⟨13805, by rfl⟩) R27611
theorem R18415 : Reach 18415 := rs (se 1 (by rfl) ⟨13811, by rfl⟩) R27623
theorem R18425 : Reach 18425 := rs (se 2 (by rfl) ⟨6909, by rfl⟩) R13819
theorem R18527 : Reach 18527 := rs (se 1 (by rfl) ⟨13895, by rfl⟩) R27791
theorem R18587 : Reach 18587 := rs (se 1 (by rfl) ⟨13940, by rfl⟩) R27881
theorem R18623 : Reach 18623 := rs (se 1 (by rfl) ⟨13967, by rfl⟩) R27935
theorem R18665 : Reach 18665 := rs (se 2 (by rfl) ⟨6999, by rfl⟩) R13999
theorem R18667 : Reach 18667 := rs (se 1 (by rfl) ⟨14000, by rfl⟩) R28001
theorem R18727 : Reach 18727 := rs (se 1 (by rfl) ⟨14045, by rfl⟩) R28091
theorem R18729 : Reach 18729 := rs (se 2 (by rfl) ⟨7023, by rfl⟩) R14047
theorem R18735 : Reach 18735 := rs (se 1 (by rfl) ⟨14051, by rfl⟩) R28103
theorem R248141 : Reach 248141 := rs (se 3 (by rfl) ⟨46526, by rfl⟩) R93053
theorem R18811 : Reach 18811 := rs (se 1 (by rfl) ⟨14108, by rfl⟩) R28217
theorem R18971 : Reach 18971 := rs (se 1 (by rfl) ⟨14228, by rfl⟩) R28457
theorem R18975 : Reach 18975 := rs (se 1 (by rfl) ⟨14231, by rfl⟩) R28463
theorem R19049 : Reach 19049 := rs (se 2 (by rfl) ⟨7143, by rfl⟩) R14287
theorem R19081 : Reach 19081 := rs (se 2 (by rfl) ⟨7155, by rfl⟩) R14311
theorem R19255 : Reach 19255 := rs (se 1 (by rfl) ⟨14441, by rfl⟩) R28883
theorem R52055 : Reach 52055 := rs (se 1 (by rfl) ⟨39041, by rfl⟩) R78083
theorem R19291 : Reach 19291 := rs (se 1 (by rfl) ⟨14468, by rfl⟩) R28937
theorem R117611 : Reach 117611 := rs (se 1 (by rfl) ⟨88208, by rfl⟩) R176417
theorem R19359 : Reach 19359 := rs (se 1 (by rfl) ⟨14519, by rfl⟩) R29039
theorem R19407 : Reach 19407 := rs (se 1 (by rfl) ⟨14555, by rfl⟩) R29111
theorem R150493 : Reach 150493 := rs (se 3 (by rfl) ⟨28217, by rfl⟩) R56435
theorem R19435 : Reach 19435 := rs (se 1 (by rfl) ⟨14576, by rfl⟩) R29153
theorem R19497 : Reach 19497 := rs (se 2 (by rfl) ⟨7311, by rfl⟩) R14623
theorem R19503 : Reach 19503 := rs (se 1 (by rfl) ⟨14627, by rfl⟩) R29255
theorem R19527 : Reach 19527 := rs (se 1 (by rfl) ⟨14645, by rfl⟩) R29291
theorem R19577 : Reach 19577 := rs (se 2 (by rfl) ⟨7341, by rfl⟩) R14683
theorem R85157 : Reach 85157 := rs (se 4 (by rfl) ⟨7983, by rfl⟩) R15967
theorem R19639 : Reach 19639 := rs (se 1 (by rfl) ⟨14729, by rfl⟩) R29459
theorem R19679 : Reach 19679 := rs (se 1 (by rfl) ⟨14759, by rfl⟩) R29519
theorem R19721 : Reach 19721 := rs (se 2 (by rfl) ⟨7395, by rfl⟩) R14791
theorem R609551 : Reach 609551 := rs (se 1 (by rfl) ⟨457163, by rfl⟩) R914327
theorem R19791 : Reach 19791 := rs (se 1 (by rfl) ⟨14843, by rfl⟩) R29687
theorem R19823 : Reach 19823 := rs (se 1 (by rfl) ⟨14867, by rfl⟩) R29735
theorem R19879 : Reach 19879 := rs (se 1 (by rfl) ⟨14909, by rfl⟩) R29819
theorem R52649 : Reach 52649 := rs (se 2 (by rfl) ⟨19743, by rfl⟩) R39487
theorem R19881 : Reach 19881 := rs (se 2 (by rfl) ⟨7455, by rfl⟩) R14911
theorem R19943 : Reach 19943 := rs (se 1 (by rfl) ⟨14957, by rfl⟩) R29915
theorem R85499 : Reach 85499 := rs (se 1 (by rfl) ⟨64124, by rfl⟩) R128249
theorem R19963 : Reach 19963 := rs (se 1 (by rfl) ⟨14972, by rfl⟩) R29945
theorem R118331 : Reach 118331 := rs (se 1 (by rfl) ⟨88748, by rfl⟩) R177497
theorem R20075 : Reach 20075 := rs (se 1 (by rfl) ⟨15056, by rfl⟩) R30113
theorem R20201 : Reach 20201 := rs (se 2 (by rfl) ⟨7575, by rfl⟩) R15151
theorem R20263 : Reach 20263 := rs (se 1 (by rfl) ⟨15197, by rfl⟩) R30395
theorem R20345 : Reach 20345 := rs (se 2 (by rfl) ⟨7629, by rfl⟩) R15259
theorem R53135 : Reach 53135 := rs (se 1 (by rfl) ⟨39851, by rfl⟩) R79703
theorem R20447 : Reach 20447 := rs (se 1 (by rfl) ⟨15335, by rfl⟩) R30671
theorem R184301 : Reach 184301 := rs (se 3 (by rfl) ⟨34556, by rfl⟩) R69113
theorem R20699 : Reach 20699 := rs (se 1 (by rfl) ⟨15524, by rfl⟩) R31049
theorem R20711 : Reach 20711 := rs (se 1 (by rfl) ⟨15533, by rfl⟩) R31067
theorem R20767 : Reach 20767 := rs (se 1 (by rfl) ⟨15575, by rfl⟩) R31151
theorem R20873 : Reach 20873 := rs (se 2 (by rfl) ⟨7827, by rfl⟩) R15655
theorem R20969 : Reach 20969 := rs (se 2 (by rfl) ⟨7863, by rfl⟩) R15727
theorem R53855 : Reach 53855 := rs (se 1 (by rfl) ⟨40391, by rfl⟩) R80783
theorem R21095 : Reach 21095 := rs (se 1 (by rfl) ⟨15821, by rfl⟩) R31643
theorem R21227 : Reach 21227 := rs (se 1 (by rfl) ⟨15920, by rfl⟩) R31841
theorem R21257 : Reach 21257 := rs (se 2 (by rfl) ⟨7971, by rfl⟩) R15943
theorem R21289 : Reach 21289 := rs (se 2 (by rfl) ⟨7983, by rfl⟩) R15967
theorem R21305 : Reach 21305 := rs (se 2 (by rfl) ⟨7989, by rfl⟩) R15979
theorem R86845 : Reach 86845 := rs (se 3 (by rfl) ⟨16283, by rfl⟩) R32567
theorem R54083 : Reach 54083 := rs (se 1 (by rfl) ⟨40562, by rfl⟩) R81125
theorem R185165 : Reach 185165 := rs (se 3 (by rfl) ⟨34718, by rfl⟩) R69437
theorem R21359 : Reach 21359 := rs (se 1 (by rfl) ⟨16019, by rfl⟩) R32039
theorem R21415 : Reach 21415 := rs (se 1 (by rfl) ⟨16061, by rfl⟩) R32123
theorem R21559 : Reach 21559 := rs (se 1 (by rfl) ⟨16169, by rfl⟩) R32339
theorem R21577 : Reach 21577 := rs (se 2 (by rfl) ⟨8091, by rfl⟩) R16183
theorem R21611 : Reach 21611 := rs (se 1 (by rfl) ⟨16208, by rfl⟩) R32417
theorem R54379 : Reach 54379 := rs (se 1 (by rfl) ⟨40784, by rfl⟩) R81569
theorem R120041 : Reach 120041 := rs (se 2 (by rfl) ⟨45015, by rfl⟩) R90031
theorem R21851 : Reach 21851 := rs (se 1 (by rfl) ⟨16388, by rfl⟩) R32777
theorem R54647 : Reach 54647 := rs (se 1 (by rfl) ⟨40985, by rfl⟩) R81971
theorem R22127 : Reach 22127 := rs (se 1 (by rfl) ⟨16595, by rfl⟩) R33191
theorem R22199 : Reach 22199 := rs (se 1 (by rfl) ⟨16649, by rfl⟩) R33299
theorem R22235 : Reach 22235 := rs (se 1 (by rfl) ⟨16676, by rfl⟩) R33353
theorem R22303 : Reach 22303 := rs (se 1 (by rfl) ⟨16727, by rfl⟩) R33455
theorem R22351 : Reach 22351 := rs (se 1 (by rfl) ⟨16763, by rfl⟩) R33527
theorem R22409 : Reach 22409 := rs (se 2 (by rfl) ⟨8403, by rfl⟩) R16807
theorem R22511 : Reach 22511 := rs (se 1 (by rfl) ⟨16883, by rfl⟩) R33767
theorem R55457 : Reach 55457 := rs (se 2 (by rfl) ⟨20796, by rfl⟩) R41593
theorem R55495 : Reach 55495 := rs (se 1 (by rfl) ⟨41621, by rfl⟩) R83243
theorem R22763 : Reach 22763 := rs (se 1 (by rfl) ⟨17072, by rfl⟩) R34145
theorem R22823 : Reach 22823 := rs (se 1 (by rfl) ⟨17117, by rfl⟩) R34235
theorem R22841 : Reach 22841 := rs (se 2 (by rfl) ⟨8565, by rfl⟩) R17131
theorem R711017 : Reach 711017 := rs (se 2 (by rfl) ⟨266631, by rfl⟩) R533263
theorem R22907 : Reach 22907 := rs (se 1 (by rfl) ⟨17180, by rfl⟩) R34361
theorem R55727 : Reach 55727 := rs (se 1 (by rfl) ⟨41795, by rfl⟩) R83591
theorem R186835 : Reach 186835 := rs (se 1 (by rfl) ⟨140126, by rfl⟩) R280253
theorem R219671 : Reach 219671 := rs (se 1 (by rfl) ⟨164753, by rfl⟩) R329507
theorem R23071 : Reach 23071 := rs (se 1 (by rfl) ⟨17303, by rfl⟩) R34607
theorem R23177 : Reach 23177 := rs (se 2 (by rfl) ⟨8691, by rfl⟩) R17383
theorem R23351 : Reach 23351 := rs (se 1 (by rfl) ⟨17513, by rfl⟩) R35027
theorem R23387 : Reach 23387 := rs (se 1 (by rfl) ⟨17540, by rfl⟩) R35081
theorem R88937 : Reach 88937 := rs (se 2 (by rfl) ⟨33351, by rfl⟩) R66703
theorem R23503 : Reach 23503 := rs (se 1 (by rfl) ⟨17627, by rfl⟩) R35255
theorem R23531 : Reach 23531 := rs (se 1 (by rfl) ⟨17648, by rfl⟩) R35297
theorem R1530899 : Reach 1530899 := rs (se 1 (by rfl) ⟨1148174, by rfl⟩) R2296349
theorem R351377 : Reach 351377 := rs (se 2 (by rfl) ⟨131766, by rfl⟩) R263533
theorem R23735 : Reach 23735 := rs (se 1 (by rfl) ⟨17801, by rfl⟩) R35603
theorem R1072397 : Reach 1072397 := rs (se 3 (by rfl) ⟨201074, by rfl⟩) R402149
theorem R23975 : Reach 23975 := rs (se 1 (by rfl) ⟨17981, by rfl⟩) R35963
theorem R56807 : Reach 56807 := rs (se 1 (by rfl) ⟨42605, by rfl⟩) R85211
theorem R24155 : Reach 24155 := rs (se 1 (by rfl) ⟨18116, by rfl⟩) R36233
theorem R24391 : Reach 24391 := rs (se 1 (by rfl) ⟨18293, by rfl⟩) R36587
theorem R24443 : Reach 24443 := rs (se 1 (by rfl) ⟨18332, by rfl⟩) R36665
theorem R24491 : Reach 24491 := rs (se 1 (by rfl) ⟨18368, by rfl⟩) R36737
theorem R319697 : Reach 319697 := rs (se 2 (by rfl) ⟨119886, by rfl⟩) R239773
theorem R57563 : Reach 57563 := rs (se 1 (by rfl) ⟨43172, by rfl⟩) R86345
theorem R24863 : Reach 24863 := rs (se 1 (by rfl) ⟨18647, by rfl⟩) R37295
theorem R24929 : Reach 24929 := rs (se 2 (by rfl) ⟨9348, by rfl⟩) R18697
theorem R57725 : Reach 57725 := rs (se 3 (by rfl) ⟨10823, by rfl⟩) R21647
theorem R25031 : Reach 25031 := rs (se 1 (by rfl) ⟨18773, by rfl⟩) R37547
theorem R25039 : Reach 25039 := rs (se 1 (by rfl) ⟨18779, by rfl⟩) R37559
theorem R57833 : Reach 57833 := rs (se 2 (by rfl) ⟨21687, by rfl⟩) R43375
theorem R57995 : Reach 57995 := rs (se 1 (by rfl) ⟨43496, by rfl⟩) R86993
theorem R25391 : Reach 25391 := rs (se 1 (by rfl) ⟨19043, by rfl⟩) R38087
theorem R25511 : Reach 25511 := rs (se 1 (by rfl) ⟨19133, by rfl⟩) R38267
theorem R25555 : Reach 25555 := rs (se 1 (by rfl) ⟨19166, by rfl⟩) R38333
theorem R91529 : Reach 91529 := rs (se 2 (by rfl) ⟨34323, by rfl⟩) R68647
theorem R26027 : Reach 26027 := rs (se 1 (by rfl) ⟨19520, by rfl⟩) R39041
theorem R26233 : Reach 26233 := rs (se 2 (by rfl) ⟨9837, by rfl⟩) R19675
theorem R26279 : Reach 26279 := rs (se 1 (by rfl) ⟨19709, by rfl⟩) R39419
theorem R26335 : Reach 26335 := rs (se 1 (by rfl) ⟨19751, by rfl⟩) R39503
theorem R26399 : Reach 26399 := rs (se 1 (by rfl) ⟨19799, by rfl⟩) R39599
theorem R26447 : Reach 26447 := rs (se 1 (by rfl) ⟨19835, by rfl⟩) R39671
theorem R26465 : Reach 26465 := rs (se 2 (by rfl) ⟨9924, by rfl⟩) R19849
theorem R26567 : Reach 26567 := rs (se 1 (by rfl) ⟨19925, by rfl⟩) R39851
theorem R26615 : Reach 26615 := rs (se 1 (by rfl) ⟨19961, by rfl⟩) R39923
theorem R59383 : Reach 59383 := rs (se 1 (by rfl) ⟨44537, by rfl⟩) R89075
theorem R26927 : Reach 26927 := rs (se 1 (by rfl) ⟨20195, by rfl⟩) R40391
theorem R27041 : Reach 27041 := rs (se 2 (by rfl) ⟨10140, by rfl⟩) R20281
theorem R27143 : Reach 27143 := rs (se 1 (by rfl) ⟨20357, by rfl⟩) R40715
theorem R27167 : Reach 27167 := rs (se 1 (by rfl) ⟨20375, by rfl⟩) R40751
theorem R125479 : Reach 125479 := rs (se 1 (by rfl) ⟨94109, by rfl⟩) R188219
theorem R289403 : Reach 289403 := rs (se 1 (by rfl) ⟨217052, by rfl⟩) R434105
theorem R27323 : Reach 27323 := rs (se 1 (by rfl) ⟨20492, by rfl⟩) R40985
theorem R92987 : Reach 92987 := rs (se 1 (by rfl) ⟨69740, by rfl⟩) R139481
theorem R518987 : Reach 518987 := rs (se 1 (by rfl) ⟨389240, by rfl⟩) R778481
theorem R1272833 : Reach 1272833 := rs (se 2 (by rfl) ⟨477312, by rfl⟩) R954625
theorem R93187 : Reach 93187 := rs (se 1 (by rfl) ⟨69890, by rfl⟩) R139781
theorem R27695 : Reach 27695 := rs (se 1 (by rfl) ⟨20771, by rfl⟩) R41543
theorem R27769 : Reach 27769 := rs (se 2 (by rfl) ⟨10413, by rfl⟩) R20827
theorem R27983 : Reach 27983 := rs (se 1 (by rfl) ⟨20987, by rfl⟩) R41975
theorem R126359 : Reach 126359 := rs (se 1 (by rfl) ⟨94769, by rfl⟩) R189539
theorem R191909 : Reach 191909 := rs (se 4 (by rfl) ⟨17991, by rfl⟩) R35983
theorem R28073 : Reach 28073 := rs (se 2 (by rfl) ⟨10527, by rfl⟩) R21055
theorem R28151 : Reach 28151 := rs (se 1 (by rfl) ⟨21113, by rfl⟩) R42227
theorem R28223 : Reach 28223 := rs (se 1 (by rfl) ⟨21167, by rfl⟩) R42335
theorem R28559 : Reach 28559 := rs (se 1 (by rfl) ⟨21419, by rfl⟩) R42839
theorem R28571 : Reach 28571 := rs (se 1 (by rfl) ⟨21428, by rfl⟩) R42857
theorem R61357 : Reach 61357 := rs (se 3 (by rfl) ⟨11504, by rfl⟩) R23009
theorem R28795 : Reach 28795 := rs (se 1 (by rfl) ⟨21596, by rfl⟩) R43193
theorem R28859 : Reach 28859 := rs (se 1 (by rfl) ⟨21644, by rfl⟩) R43289
theorem R29065 : Reach 29065 := rs (se 2 (by rfl) ⟨10899, by rfl⟩) R21799
theorem R94607 : Reach 94607 := rs (se 1 (by rfl) ⟨70955, by rfl⟩) R141911
theorem R29177 : Reach 29177 := rs (se 2 (by rfl) ⟨10941, by rfl⟩) R21883
theorem R29267 : Reach 29267 := rs (se 1 (by rfl) ⟨21950, by rfl⟩) R43901
theorem R29279 : Reach 29279 := rs (se 1 (by rfl) ⟨21959, by rfl⟩) R43919
theorem R29345 : Reach 29345 := rs (se 2 (by rfl) ⟨11004, by rfl⟩) R22009
theorem R29447 : Reach 29447 := rs (se 1 (by rfl) ⟨22085, by rfl⟩) R44171
theorem R29705 : Reach 29705 := rs (se 2 (by rfl) ⟨11139, by rfl⟩) R22279
theorem R29759 : Reach 29759 := rs (se 1 (by rfl) ⟨22319, by rfl⟩) R44639
theorem R62603 : Reach 62603 := rs (se 1 (by rfl) ⟨46952, by rfl⟩) R93905
theorem R95879 : Reach 95879 := rs (se 1 (by rfl) ⟨71909, by rfl⟩) R143819
theorem R63179 : Reach 63179 := rs (se 1 (by rfl) ⟨47384, by rfl⟩) R94769
theorem R30527 : Reach 30527 := rs (se 1 (by rfl) ⟨22895, by rfl⟩) R45791
theorem R30601 : Reach 30601 := rs (se 2 (by rfl) ⟨11475, by rfl⟩) R22951
theorem R63547 : Reach 63547 := rs (se 1 (by rfl) ⟨47660, by rfl⟩) R95321
theorem R30815 : Reach 30815 := rs (se 1 (by rfl) ⟨23111, by rfl⟩) R46223
theorem R30863 : Reach 30863 := rs (se 1 (by rfl) ⟨23147, by rfl⟩) R46295
theorem R30881 : Reach 30881 := rs (se 2 (by rfl) ⟨11580, by rfl⟩) R23161
theorem R63787 : Reach 63787 := rs (se 1 (by rfl) ⟨47840, by rfl⟩) R95681
theorem R96623 : Reach 96623 := rs (se 1 (by rfl) ⟨72467, by rfl⟩) R144935
theorem R2587085 : Reach 2587085 := rs (se 3 (by rfl) ⟨485078, by rfl⟩) R970157
theorem R359063 : Reach 359063 := rs (se 1 (by rfl) ⟨269297, by rfl⟩) R538595
theorem R64223 : Reach 64223 := rs (se 1 (by rfl) ⟨48167, by rfl⟩) R96335
theorem R31571 : Reach 31571 := rs (se 1 (by rfl) ⟨23678, by rfl⟩) R47357
theorem R129923 : Reach 129923 := rs (se 1 (by rfl) ⟨97442, by rfl⟩) R194885
theorem R64583 : Reach 64583 := rs (se 1 (by rfl) ⟨48437, by rfl⟩) R96875
theorem R31873 : Reach 31873 := rs (se 2 (by rfl) ⟨11952, by rfl⟩) R23905
theorem R31927 : Reach 31927 := rs (se 1 (by rfl) ⟨23945, by rfl⟩) R47891
theorem R851267 : Reach 851267 := rs (se 1 (by rfl) ⟨638450, by rfl⟩) R1276901
theorem R32111 : Reach 32111 := rs (se 1 (by rfl) ⟨24083, by rfl⟩) R48167
theorem R32167 : Reach 32167 := rs (se 1 (by rfl) ⟨24125, by rfl⟩) R48251
theorem R64961 : Reach 64961 := rs (se 2 (by rfl) ⟨24360, by rfl⟩) R48721
theorem R261569 : Reach 261569 := rs (se 2 (by rfl) ⟨98088, by rfl⟩) R196177
theorem R32231 : Reach 32231 := rs (se 1 (by rfl) ⟨24173, by rfl⟩) R48347
theorem R32399 : Reach 32399 := rs (se 1 (by rfl) ⟨24299, by rfl⟩) R48599
theorem R130733 : Reach 130733 := rs (se 3 (by rfl) ⟨24512, by rfl⟩) R49025
theorem R65249 : Reach 65249 := rs (se 2 (by rfl) ⟨24468, by rfl⟩) R48937
theorem R32489 : Reach 32489 := rs (se 2 (by rfl) ⟨12183, by rfl⟩) R24367
theorem R98135 : Reach 98135 := rs (se 1 (by rfl) ⟨73601, by rfl⟩) R147203
theorem R32683 : Reach 32683 := rs (se 1 (by rfl) ⟨24512, by rfl⟩) R49025
theorem R33311 : Reach 33311 := rs (se 1 (by rfl) ⟨24983, by rfl⟩) R49967
theorem R33385 : Reach 33385 := rs (se 2 (by rfl) ⟨12519, by rfl⟩) R25039
theorem R131705 : Reach 131705 := rs (se 2 (by rfl) ⟨49389, by rfl⟩) R98779
theorem R3211973 : Reach 3211973 := rs (se 4 (by rfl) ⟨301122, by rfl⟩) R602245
theorem R99083 : Reach 99083 := rs (se 1 (by rfl) ⟨74312, by rfl⟩) R148625
theorem R34073 : Reach 34073 := rs (se 2 (by rfl) ⟨12777, by rfl⟩) R25555
theorem R99623 : Reach 99623 := rs (se 1 (by rfl) ⟨74717, by rfl⟩) R149435
theorem R67339 : Reach 67339 := rs (se 1 (by rfl) ⟨50504, by rfl⟩) R101009
theorem R34703 : Reach 34703 := rs (se 1 (by rfl) ⟨26027, by rfl⟩) R52055
theorem R100601 : Reach 100601 := rs (se 2 (by rfl) ⟨37725, by rfl⟩) R75451
theorem R35099 : Reach 35099 := rs (se 1 (by rfl) ⟨26324, by rfl⟩) R52649
theorem R35113 : Reach 35113 := rs (se 2 (by rfl) ⟨13167, by rfl⟩) R26335
theorem R67979 : Reach 67979 := rs (se 1 (by rfl) ⟨50984, by rfl⟩) R101969
theorem R35261 : Reach 35261 := rs (se 3 (by rfl) ⟨6611, by rfl⟩) R13223
theorem R68147 : Reach 68147 := rs (se 1 (by rfl) ⟨51110, by rfl⟩) R102221
theorem R35423 : Reach 35423 := rs (se 1 (by rfl) ⟨26567, by rfl⟩) R53135
theorem R101321 : Reach 101321 := rs (se 2 (by rfl) ⟨37995, by rfl⟩) R75991
theorem R35903 : Reach 35903 := rs (se 1 (by rfl) ⟨26927, by rfl⟩) R53855
theorem R36055 : Reach 36055 := rs (se 1 (by rfl) ⟨27041, by rfl⟩) R54083
theorem R167305 : Reach 167305 := rs (se 2 (by rfl) ⟨62739, by rfl⟩) R125479
theorem R36431 : Reach 36431 := rs (se 1 (by rfl) ⟨27323, by rfl⟩) R54647
theorem R200657 : Reach 200657 := rs (se 2 (by rfl) ⟨75246, by rfl⟩) R150493
theorem R36971 : Reach 36971 := rs (se 1 (by rfl) ⟨27728, by rfl⟩) R55457
theorem R37025 : Reach 37025 := rs (se 2 (by rfl) ⟨13884, by rfl⟩) R27769
theorem R37151 : Reach 37151 := rs (se 1 (by rfl) ⟨27863, by rfl⟩) R55727
theorem R201203 : Reach 201203 := rs (se 1 (by rfl) ⟨150902, by rfl⟩) R301805
theorem R1020599 : Reach 1020599 := rs (se 1 (by rfl) ⟨765449, by rfl⟩) R1530899
theorem R234251 : Reach 234251 := rs (se 1 (by rfl) ⟨175688, by rfl⟩) R351377
theorem R37871 : Reach 37871 := rs (se 1 (by rfl) ⟨28403, by rfl⟩) R56807
theorem R38375 : Reach 38375 := rs (se 1 (by rfl) ⟨28781, by rfl⟩) R57563
theorem R38393 : Reach 38393 := rs (se 2 (by rfl) ⟨14397, by rfl⟩) R28795
theorem R38483 : Reach 38483 := rs (se 1 (by rfl) ⟨28862, by rfl⟩) R57725
theorem R38555 : Reach 38555 := rs (se 1 (by rfl) ⟨28916, by rfl⟩) R57833
theorem R71387 : Reach 71387 := rs (se 1 (by rfl) ⟨53540, by rfl⟩) R107081
theorem R38663 : Reach 38663 := rs (se 1 (by rfl) ⟨28997, by rfl⟩) R57995
theorem R38753 : Reach 38753 := rs (se 2 (by rfl) ⟨14532, by rfl⟩) R29065
theorem R661709 : Reach 661709 := rs (se 3 (by rfl) ⟨124070, by rfl⟩) R248141
theorem R105097 : Reach 105097 := rs (se 2 (by rfl) ⟨39411, by rfl⟩) R78823
theorem R105181 : Reach 105181 := rs (se 3 (by rfl) ⟨19721, by rfl⟩) R39443
theorem R72505 : Reach 72505 := rs (se 2 (by rfl) ⟨27189, by rfl⟩) R54379
theorem R73223 : Reach 73223 := rs (se 1 (by rfl) ⟨54917, by rfl⟩) R109835
theorem R73993 : Reach 73993 := rs (se 2 (by rfl) ⟨27747, by rfl⟩) R55495
theorem R106829 : Reach 106829 := rs (se 3 (by rfl) ⟨20030, by rfl⟩) R40061
theorem R139909 : Reach 139909 := rs (se 4 (by rfl) ⟨13116, by rfl⟩) R26233
theorem R2859725 : Reach 2859725 := rs (se 3 (by rfl) ⟨536198, by rfl⟩) R1072397
theorem R41735 : Reach 41735 := rs (se 1 (by rfl) ⟨31301, by rfl⟩) R62603
theorem R2270045 : Reach 2270045 := rs (se 3 (by rfl) ⟨425633, by rfl⟩) R851267
theorem R74621 : Reach 74621 := rs (se 3 (by rfl) ⟨13991, by rfl⟩) R27983
theorem R42119 : Reach 42119 := rs (se 1 (by rfl) ⟨31589, by rfl⟩) R63179
theorem R140453 : Reach 140453 := rs (se 4 (by rfl) ⟨13167, by rfl⟩) R26335
theorem R697517 : Reach 697517 := rs (se 3 (by rfl) ⟨130784, by rfl⟩) R261569
theorem R42497 : Reach 42497 := rs (se 2 (by rfl) ⟨15936, by rfl⟩) R31873
theorem R42569 : Reach 42569 := rs (se 2 (by rfl) ⟨15963, by rfl⟩) R31927
theorem R239375 : Reach 239375 := rs (se 1 (by rfl) ⟨179531, by rfl⟩) R359063
theorem R42815 : Reach 42815 := rs (se 1 (by rfl) ⟨32111, by rfl⟩) R64223
theorem R42889 : Reach 42889 := rs (se 2 (by rfl) ⟨16083, by rfl⟩) R32167
theorem R75743 : Reach 75743 := rs (se 1 (by rfl) ⟨56807, by rfl⟩) R113615
theorem R43055 : Reach 43055 := rs (se 1 (by rfl) ⟨32291, by rfl⟩) R64583
theorem R43307 : Reach 43307 := rs (se 1 (by rfl) ⟨32480, by rfl⟩) R64961
theorem R43499 : Reach 43499 := rs (se 1 (by rfl) ⟨32624, by rfl⟩) R65249
theorem R43577 : Reach 43577 := rs (se 2 (by rfl) ⟨16341, by rfl⟩) R32683
theorem R76427 : Reach 76427 := rs (se 1 (by rfl) ⟨57320, by rfl⟩) R114641
theorem R109259 : Reach 109259 := rs (se 1 (by rfl) ⟨81944, by rfl⟩) R163889
theorem R207623 : Reach 207623 := rs (se 1 (by rfl) ⟨155717, by rfl⟩) R311435
theorem R76751 : Reach 76751 := rs (se 1 (by rfl) ⟨57563, by rfl⟩) R115127
theorem R338917 : Reach 338917 := rs (se 4 (by rfl) ⟨31773, by rfl⟩) R63547
theorem R76787 : Reach 76787 := rs (se 1 (by rfl) ⟨57590, by rfl⟩) R115181
theorem R44297 : Reach 44297 := rs (se 2 (by rfl) ⟨16611, by rfl⟩) R33223
theorem R44327 : Reach 44327 := rs (se 1 (by rfl) ⟨33245, by rfl⟩) R66491
theorem R77111 : Reach 77111 := rs (se 1 (by rfl) ⟨57833, by rfl⟩) R115667
theorem R44731 : Reach 44731 := rs (se 1 (by rfl) ⟨33548, by rfl⟩) R67097
theorem R45089 : Reach 45089 := rs (se 2 (by rfl) ⟨16908, by rfl⟩) R33817
theorem R45287 : Reach 45287 := rs (se 1 (by rfl) ⟨33965, by rfl⟩) R67931
theorem R45467 : Reach 45467 := rs (se 1 (by rfl) ⟨34100, by rfl⟩) R68201
theorem R78407 : Reach 78407 := rs (se 1 (by rfl) ⟨58805, by rfl⟩) R117611
theorem R13051 : Reach 13051 := rs (se 1 (by rfl) ⟨9788, by rfl⟩) R19577
theorem R111401 : Reach 111401 := rs (se 2 (by rfl) ⟨41775, by rfl⟩) R83551
theorem R13119 : Reach 13119 := rs (se 1 (by rfl) ⟨9839, by rfl⟩) R19679
theorem R13147 : Reach 13147 := rs (se 1 (by rfl) ⟨9860, by rfl⟩) R19721
theorem R406367 : Reach 406367 := rs (se 1 (by rfl) ⟨304775, by rfl⟩) R609551
theorem R13215 : Reach 13215 := rs (se 1 (by rfl) ⟨9911, by rfl⟩) R19823
theorem R13295 : Reach 13295 := rs (se 1 (by rfl) ⟨9971, by rfl⟩) R19943
theorem R78887 : Reach 78887 := rs (se 1 (by rfl) ⟨59165, by rfl⟩) R118331
theorem R13383 : Reach 13383 := rs (se 1 (by rfl) ⟨10037, by rfl⟩) R20075
theorem R13467 : Reach 13467 := rs (se 1 (by rfl) ⟨10100, by rfl⟩) R20201
theorem R13563 : Reach 13563 := rs (se 1 (by rfl) ⟨10172, by rfl⟩) R20345
theorem R46331 : Reach 46331 := rs (se 1 (by rfl) ⟨34748, by rfl⟩) R69497
theorem R13631 : Reach 13631 := rs (se 1 (by rfl) ⟨10223, by rfl⟩) R20447
theorem R79177 : Reach 79177 := rs (se 2 (by rfl) ⟨29691, by rfl⟩) R59383
theorem R13799 : Reach 13799 := rs (se 1 (by rfl) ⟨10349, by rfl⟩) R20699
theorem R13807 : Reach 13807 := rs (se 1 (by rfl) ⟨10355, by rfl⟩) R20711
theorem R669221 : Reach 669221 := rs (se 4 (by rfl) ⟨62739, by rfl⟩) R125479
theorem R13915 : Reach 13915 := rs (se 1 (by rfl) ⟨10436, by rfl⟩) R20873
theorem R13979 : Reach 13979 := rs (se 1 (by rfl) ⟨10484, by rfl⟩) R20969
theorem R14063 : Reach 14063 := rs (se 1 (by rfl) ⟨10547, by rfl⟩) R21095
theorem R46889 : Reach 46889 := rs (se 2 (by rfl) ⟨17583, by rfl⟩) R35167
theorem R14151 : Reach 14151 := rs (se 1 (by rfl) ⟨10613, by rfl⟩) R21227
theorem R14171 : Reach 14171 := rs (se 1 (by rfl) ⟨10628, by rfl⟩) R21257
theorem R14203 : Reach 14203 := rs (se 1 (by rfl) ⟨10652, by rfl⟩) R21305
theorem R14239 : Reach 14239 := rs (se 1 (by rfl) ⟨10679, by rfl⟩) R21359
theorem R14407 : Reach 14407 := rs (se 1 (by rfl) ⟨10805, by rfl⟩) R21611
theorem R47243 : Reach 47243 := rs (se 1 (by rfl) ⟨35432, by rfl⟩) R70865
theorem R80027 : Reach 80027 := rs (se 1 (by rfl) ⟨60020, by rfl⟩) R120041
theorem R14567 : Reach 14567 := rs (se 1 (by rfl) ⟨10925, by rfl⟩) R21851
theorem R14751 : Reach 14751 := rs (se 1 (by rfl) ⟨11063, by rfl⟩) R22127
theorem R14799 : Reach 14799 := rs (se 1 (by rfl) ⟨11099, by rfl⟩) R22199
theorem R14823 : Reach 14823 := rs (se 1 (by rfl) ⟨11117, by rfl⟩) R22235
theorem R14939 : Reach 14939 := rs (se 1 (by rfl) ⟨11204, by rfl⟩) R22409
theorem R15007 : Reach 15007 := rs (se 1 (by rfl) ⟨11255, by rfl⟩) R22511
theorem R15175 : Reach 15175 := rs (se 1 (by rfl) ⟨11381, by rfl⟩) R22763
theorem R15215 : Reach 15215 := rs (se 1 (by rfl) ⟨11411, by rfl⟩) R22823
theorem R15227 : Reach 15227 := rs (se 1 (by rfl) ⟨11420, by rfl⟩) R22841
theorem R474011 : Reach 474011 := rs (se 1 (by rfl) ⟨355508, by rfl⟩) R711017
theorem R15271 : Reach 15271 := rs (se 1 (by rfl) ⟨11453, by rfl⟩) R22907
theorem R146447 : Reach 146447 := rs (se 1 (by rfl) ⟨109835, by rfl⟩) R219671
theorem R15451 : Reach 15451 := rs (se 1 (by rfl) ⟨11588, by rfl⟩) R23177
theorem R48275 : Reach 48275 := rs (se 1 (by rfl) ⟨36206, by rfl⟩) R72413
theorem R15567 : Reach 15567 := rs (se 1 (by rfl) ⟨11675, by rfl⟩) R23351
theorem R15591 : Reach 15591 := rs (se 1 (by rfl) ⟨11693, by rfl⟩) R23387
theorem R15687 : Reach 15687 := rs (se 1 (by rfl) ⟨11765, by rfl⟩) R23531
theorem R48545 : Reach 48545 := rs (se 2 (by rfl) ⟨18204, by rfl⟩) R36409
theorem R15823 : Reach 15823 := rs (se 1 (by rfl) ⟨11867, by rfl⟩) R23735
theorem R15983 : Reach 15983 := rs (se 1 (by rfl) ⟨11987, by rfl⟩) R23975
theorem R48863 : Reach 48863 := rs (se 1 (by rfl) ⟨36647, by rfl⟩) R73295
theorem R16103 : Reach 16103 := rs (se 1 (by rfl) ⟨12077, by rfl⟩) R24155
theorem R81809 : Reach 81809 := rs (se 2 (by rfl) ⟨30678, by rfl⟩) R61357
theorem R16295 : Reach 16295 := rs (se 1 (by rfl) ⟨12221, by rfl⟩) R24443
theorem R49085 : Reach 49085 := rs (se 3 (by rfl) ⟨9203, by rfl⟩) R18407
theorem R16327 : Reach 16327 := rs (se 1 (by rfl) ⟨12245, by rfl⟩) R24491
theorem R213131 : Reach 213131 := rs (se 1 (by rfl) ⟨159848, by rfl⟩) R319697
theorem R16575 : Reach 16575 := rs (se 1 (by rfl) ⟨12431, by rfl⟩) R24863
theorem R180427 : Reach 180427 := rs (se 1 (by rfl) ⟨135320, by rfl⟩) R270641
theorem R16619 : Reach 16619 := rs (se 1 (by rfl) ⟨12464, by rfl⟩) R24929
theorem R16687 : Reach 16687 := rs (se 1 (by rfl) ⟨12515, by rfl⟩) R25031
theorem R82301 : Reach 82301 := rs (se 3 (by rfl) ⟨15431, by rfl⟩) R30863
theorem R49565 : Reach 49565 := rs (se 3 (by rfl) ⟨9293, by rfl⟩) R18587
theorem R16927 : Reach 16927 := rs (se 1 (by rfl) ⟨12695, by rfl⟩) R25391
theorem R17007 : Reach 17007 := rs (se 1 (by rfl) ⟨12755, by rfl⟩) R25511
theorem R17351 : Reach 17351 := rs (se 1 (by rfl) ⟨13013, by rfl⟩) R26027
theorem R115793 : Reach 115793 := rs (se 2 (by rfl) ⟨43422, by rfl⟩) R86845
theorem R17519 : Reach 17519 := rs (se 1 (by rfl) ⟨13139, by rfl⟩) R26279
theorem R17599 : Reach 17599 := rs (se 1 (by rfl) ⟨13199, by rfl⟩) R26399
theorem R17631 : Reach 17631 := rs (se 1 (by rfl) ⟨13223, by rfl⟩) R26447
theorem R17643 : Reach 17643 := rs (se 1 (by rfl) ⟨13232, by rfl⟩) R26465
theorem R17711 : Reach 17711 := rs (se 1 (by rfl) ⟨13283, by rfl⟩) R26567
theorem R17743 : Reach 17743 := rs (se 1 (by rfl) ⟨13307, by rfl⟩) R26615
theorem R17833 : Reach 17833 := rs (se 2 (by rfl) ⟨6687, by rfl⟩) R13375
theorem R50615 : Reach 50615 := rs (se 1 (by rfl) ⟨37961, by rfl⟩) R75923
theorem R17951 : Reach 17951 := rs (se 1 (by rfl) ⟨13463, by rfl⟩) R26927
theorem R18025 : Reach 18025 := rs (se 2 (by rfl) ⟨6759, by rfl⟩) R13519
theorem R18027 : Reach 18027 := rs (se 1 (by rfl) ⟨13520, by rfl⟩) R27041
theorem R50797 : Reach 50797 := rs (se 3 (by rfl) ⟨9524, by rfl⟩) R19049
theorem R18095 : Reach 18095 := rs (se 1 (by rfl) ⟨13571, by rfl⟩) R27143
theorem R18111 : Reach 18111 := rs (se 1 (by rfl) ⟨13583, by rfl⟩) R27167
theorem R50975 : Reach 50975 := rs (se 1 (by rfl) ⟨38231, by rfl⟩) R76463
theorem R18215 : Reach 18215 := rs (se 1 (by rfl) ⟨13661, by rfl⟩) R27323
theorem R18297 : Reach 18297 := rs (se 2 (by rfl) ⟨6861, by rfl⟩) R13723
theorem R345991 : Reach 345991 := rs (se 1 (by rfl) ⟨259493, by rfl⟩) R518987
theorem R18463 : Reach 18463 := rs (se 1 (by rfl) ⟨13847, by rfl⟩) R27695
theorem R18655 : Reach 18655 := rs (se 1 (by rfl) ⟨13991, by rfl⟩) R27983
theorem R84239 : Reach 84239 := rs (se 1 (by rfl) ⟨63179, by rfl⟩) R126359
theorem R18715 : Reach 18715 := rs (se 1 (by rfl) ⟨14036, by rfl⟩) R28073
theorem R18767 : Reach 18767 := rs (se 1 (by rfl) ⟨14075, by rfl⟩) R28151
theorem R510299 : Reach 510299 := rs (se 1 (by rfl) ⟨382724, by rfl⟩) R765449
theorem R18815 : Reach 18815 := rs (se 1 (by rfl) ⟨14111, by rfl⟩) R28223
theorem R51617 : Reach 51617 := rs (se 2 (by rfl) ⟨19356, by rfl⟩) R38713
theorem R18857 : Reach 18857 := rs (se 2 (by rfl) ⟨7071, by rfl⟩) R14143
theorem R19039 : Reach 19039 := rs (se 1 (by rfl) ⟨14279, by rfl⟩) R28559
theorem R19047 : Reach 19047 := rs (se 1 (by rfl) ⟨14285, by rfl⟩) R28571
theorem R19239 : Reach 19239 := rs (se 1 (by rfl) ⟨14429, by rfl⟩) R28859
theorem R19241 : Reach 19241 := rs (se 2 (by rfl) ⟨7215, by rfl⟩) R14431
theorem R52073 : Reach 52073 := rs (se 2 (by rfl) ⟨19527, by rfl⟩) R39055
theorem R19321 : Reach 19321 := rs (se 2 (by rfl) ⟨7245, by rfl⟩) R14491
theorem R19369 : Reach 19369 := rs (se 2 (by rfl) ⟨7263, by rfl⟩) R14527
theorem R19451 : Reach 19451 := rs (se 1 (by rfl) ⟨14588, by rfl⟩) R29177
theorem R19511 : Reach 19511 := rs (se 1 (by rfl) ⟨14633, by rfl⟩) R29267
theorem R85049 : Reach 85049 := rs (se 2 (by rfl) ⟨31893, by rfl⟩) R63787
theorem R19519 : Reach 19519 := rs (se 1 (by rfl) ⟨14639, by rfl⟩) R29279
theorem R19563 : Reach 19563 := rs (se 1 (by rfl) ⟨14672, by rfl⟩) R29345
theorem R19631 : Reach 19631 := rs (se 1 (by rfl) ⟨14723, by rfl⟩) R29447
theorem R249113 : Reach 249113 := rs (se 2 (by rfl) ⟨93417, by rfl⟩) R186835
theorem R19803 : Reach 19803 := rs (se 1 (by rfl) ⟨14852, by rfl⟩) R29705
theorem R19833 : Reach 19833 := rs (se 2 (by rfl) ⟨7437, by rfl⟩) R14875
theorem R19839 : Reach 19839 := rs (se 1 (by rfl) ⟨14879, by rfl⟩) R29759
theorem R282305 : Reach 282305 := rs (se 2 (by rfl) ⟨105864, by rfl⟩) R211729
theorem R511757 : Reach 511757 := rs (se 3 (by rfl) ⟨95954, by rfl⟩) R191909
theorem R118583 : Reach 118583 := rs (se 1 (by rfl) ⟨88937, by rfl⟩) R177875
theorem R20351 : Reach 20351 := rs (se 1 (by rfl) ⟨15263, by rfl⟩) R30527
theorem R53207 : Reach 53207 := rs (se 1 (by rfl) ⟨39905, by rfl⟩) R79811
theorem R53243 : Reach 53243 := rs (se 1 (by rfl) ⟨39932, by rfl⟩) R79865
theorem R20543 : Reach 20543 := rs (se 1 (by rfl) ⟨15407, by rfl⟩) R30815
theorem R20587 : Reach 20587 := rs (se 1 (by rfl) ⟨15440, by rfl⟩) R30881
theorem R53423 : Reach 53423 := rs (se 1 (by rfl) ⟨40067, by rfl⟩) R80135
theorem R119069 : Reach 119069 := rs (se 3 (by rfl) ⟨22325, by rfl⟩) R44651
theorem R20777 : Reach 20777 := rs (se 2 (by rfl) ⟨7791, by rfl⟩) R15583
theorem R1724723 : Reach 1724723 := rs (se 1 (by rfl) ⟨1293542, by rfl⟩) R2587085
theorem R21047 : Reach 21047 := rs (se 1 (by rfl) ⟨15785, by rfl⟩) R31571
theorem R86615 : Reach 86615 := rs (se 1 (by rfl) ⟨64961, by rfl⟩) R129923
theorem R774917 : Reach 774917 := rs (se 4 (by rfl) ⟨72648, by rfl⟩) R145297
theorem R54107 : Reach 54107 := rs (se 1 (by rfl) ⟨40580, by rfl⟩) R81161
theorem R54121 : Reach 54121 := rs (se 2 (by rfl) ⟨20295, by rfl⟩) R40591
theorem R21407 : Reach 21407 := rs (se 1 (by rfl) ⟨16055, by rfl⟩) R32111
theorem R21487 : Reach 21487 := rs (se 1 (by rfl) ⟨16115, by rfl⟩) R32231
theorem R21599 : Reach 21599 := rs (se 1 (by rfl) ⟨16199, by rfl⟩) R32399
theorem R87155 : Reach 87155 := rs (se 1 (by rfl) ⟨65366, by rfl⟩) R130733
theorem R21659 : Reach 21659 := rs (se 1 (by rfl) ⟨16244, by rfl⟩) R32489
theorem R54665 : Reach 54665 := rs (se 2 (by rfl) ⟨20499, by rfl⟩) R40999
theorem R21991 : Reach 21991 := rs (se 1 (by rfl) ⟨16493, by rfl⟩) R32987
theorem R22153 : Reach 22153 := rs (se 2 (by rfl) ⟨8307, by rfl⟩) R16615
theorem R22171 : Reach 22171 := rs (se 1 (by rfl) ⟨16628, by rfl⟩) R33257
theorem R22343 : Reach 22343 := rs (se 1 (by rfl) ⟨16757, by rfl⟩) R33515
theorem R87965 : Reach 87965 := rs (se 3 (by rfl) ⟨16493, by rfl⟩) R32987
theorem R22747 : Reach 22747 := rs (se 1 (by rfl) ⟨17060, by rfl⟩) R34121
theorem R22943 : Reach 22943 := rs (se 1 (by rfl) ⟨17207, by rfl⟩) R34415
theorem R186785 : Reach 186785 := rs (se 2 (by rfl) ⟨70044, by rfl⟩) R140089
theorem R121277 : Reach 121277 := rs (se 3 (by rfl) ⟨22739, by rfl⟩) R45479
theorem R23015 : Reach 23015 := rs (se 1 (by rfl) ⟨17261, by rfl⟩) R34523
theorem R23017 : Reach 23017 := rs (se 2 (by rfl) ⟨8631, by rfl⟩) R17263
theorem R55835 : Reach 55835 := rs (se 1 (by rfl) ⟨41876, by rfl⟩) R83753
theorem R88613 : Reach 88613 := rs (se 4 (by rfl) ⟨8307, by rfl⟩) R16615
theorem R154183 : Reach 154183 := rs (se 1 (by rfl) ⟨115637, by rfl⟩) R231275
theorem R88775 : Reach 88775 := rs (se 1 (by rfl) ⟨66581, by rfl⟩) R133163
theorem R351013 : Reach 351013 := rs (se 4 (by rfl) ⟨32907, by rfl⟩) R65815
theorem R23419 : Reach 23419 := rs (se 1 (by rfl) ⟨17564, by rfl⟩) R35129
theorem R23759 : Reach 23759 := rs (se 1 (by rfl) ⟨17819, by rfl⟩) R35639
theorem R23879 : Reach 23879 := rs (se 1 (by rfl) ⟨17909, by rfl⟩) R35819
theorem R56657 : Reach 56657 := rs (se 2 (by rfl) ⟨21246, by rfl⟩) R42493
theorem R56771 : Reach 56771 := rs (se 1 (by rfl) ⟨42578, by rfl⟩) R85157
theorem R24041 : Reach 24041 := rs (se 2 (by rfl) ⟨9015, by rfl⟩) R18031
theorem R24137 : Reach 24137 := rs (se 2 (by rfl) ⟨9051, by rfl⟩) R18103
theorem R24185 : Reach 24185 := rs (se 2 (by rfl) ⟨9069, by rfl⟩) R18139
theorem R56953 : Reach 56953 := rs (se 2 (by rfl) ⟨21357, by rfl⟩) R42715
theorem R56999 : Reach 56999 := rs (se 1 (by rfl) ⟨42749, by rfl⟩) R85499
theorem R155303 : Reach 155303 := rs (se 1 (by rfl) ⟨116477, by rfl⟩) R232955
theorem R24431 : Reach 24431 := rs (se 1 (by rfl) ⟨18323, by rfl⟩) R36647
theorem R24475 : Reach 24475 := rs (se 1 (by rfl) ⟨18356, by rfl⟩) R36713
theorem R548801 : Reach 548801 := rs (se 2 (by rfl) ⟨205800, by rfl⟩) R411601
theorem R24553 : Reach 24553 := rs (se 2 (by rfl) ⟨9207, by rfl⟩) R18415
theorem R122867 : Reach 122867 := rs (se 1 (by rfl) ⟨92150, by rfl⟩) R184301
theorem R90391 : Reach 90391 := rs (se 1 (by rfl) ⟨67793, by rfl⟩) R135587
theorem R24887 : Reach 24887 := rs (se 1 (by rfl) ⟨18665, by rfl⟩) R37331
theorem R24889 : Reach 24889 := rs (se 2 (by rfl) ⟨9333, by rfl⟩) R18667
theorem R25115 : Reach 25115 := rs (se 1 (by rfl) ⟨18836, by rfl⟩) R37673
theorem R123443 : Reach 123443 := rs (se 1 (by rfl) ⟨92582, by rfl⟩) R185165
theorem R25295 : Reach 25295 := rs (se 1 (by rfl) ⟨18971, by rfl⟩) R37943
theorem R25307 : Reach 25307 := rs (se 1 (by rfl) ⟨18980, by rfl⟩) R37961
theorem R90989 : Reach 90989 := rs (se 3 (by rfl) ⟨17060, by rfl⟩) R34121
theorem R58441 : Reach 58441 := rs (se 2 (by rfl) ⟨21915, by rfl⟩) R43831
theorem R25673 : Reach 25673 := rs (se 2 (by rfl) ⟨9627, by rfl⟩) R19255
theorem R25721 : Reach 25721 := rs (se 2 (by rfl) ⟨9645, by rfl⟩) R19291
theorem R25913 : Reach 25913 := rs (se 2 (by rfl) ⟨9717, by rfl⟩) R19435
theorem R124249 : Reach 124249 := rs (se 2 (by rfl) ⟨46593, by rfl⟩) R93187
theorem R26011 : Reach 26011 := rs (se 1 (by rfl) ⟨19508, by rfl⟩) R39017
theorem R26183 : Reach 26183 := rs (se 1 (by rfl) ⟨19637, by rfl⟩) R39275
theorem R26363 : Reach 26363 := rs (se 1 (by rfl) ⟨19772, by rfl⟩) R39545
theorem R26387 : Reach 26387 := rs (se 1 (by rfl) ⟨19790, by rfl⟩) R39581
theorem R452429 : Reach 452429 := rs (se 3 (by rfl) ⟨84830, by rfl⟩) R169661
theorem R59291 : Reach 59291 := rs (se 1 (by rfl) ⟨44468, by rfl⟩) R88937
theorem R26591 : Reach 26591 := rs (se 1 (by rfl) ⟨19943, by rfl⟩) R39887
theorem R26603 : Reach 26603 := rs (se 1 (by rfl) ⟨19952, by rfl⟩) R39905
theorem R26651 : Reach 26651 := rs (se 1 (by rfl) ⟨19988, by rfl⟩) R39977
theorem R27017 : Reach 27017 := rs (se 2 (by rfl) ⟨10131, by rfl⟩) R20263
theorem R92663 : Reach 92663 := rs (se 1 (by rfl) ⟨69497, by rfl⟩) R138995
theorem R27599 : Reach 27599 := rs (se 1 (by rfl) ⟨20699, by rfl⟩) R41399
theorem R27689 : Reach 27689 := rs (se 2 (by rfl) ⟨10383, by rfl⟩) R20767
theorem R27719 : Reach 27719 := rs (se 1 (by rfl) ⟨20789, by rfl⟩) R41579
theorem R27923 : Reach 27923 := rs (se 1 (by rfl) ⟨20942, by rfl⟩) R41885
theorem R27959 : Reach 27959 := rs (se 1 (by rfl) ⟨20969, by rfl⟩) R41939
theorem R28115 : Reach 28115 := rs (se 1 (by rfl) ⟨21086, by rfl⟩) R42173
theorem R28127 : Reach 28127 := rs (se 1 (by rfl) ⟨21095, by rfl⟩) R42191
theorem R61019 : Reach 61019 := rs (se 1 (by rfl) ⟨45764, by rfl⟩) R91529
theorem R28343 : Reach 28343 := rs (se 1 (by rfl) ⟨21257, by rfl⟩) R42515
theorem R28385 : Reach 28385 := rs (se 2 (by rfl) ⟨10644, by rfl⟩) R21289
theorem R93959 : Reach 93959 := rs (se 1 (by rfl) ⟨70469, by rfl⟩) R140939
theorem R28553 : Reach 28553 := rs (se 2 (by rfl) ⟨10707, by rfl⟩) R21415
theorem R28745 : Reach 28745 := rs (se 2 (by rfl) ⟨10779, by rfl⟩) R21559
theorem R28769 : Reach 28769 := rs (se 2 (by rfl) ⟨10788, by rfl⟩) R21577
theorem R28799 : Reach 28799 := rs (se 1 (by rfl) ⟨21599, by rfl⟩) R43199
theorem R28903 : Reach 28903 := rs (se 1 (by rfl) ⟨21677, by rfl⟩) R43355
theorem R61721 : Reach 61721 := rs (se 2 (by rfl) ⟨23145, by rfl⟩) R46291
theorem R192935 : Reach 192935 := rs (se 1 (by rfl) ⟨144701, by rfl⟩) R289403
theorem R29135 : Reach 29135 := rs (se 1 (by rfl) ⟨21851, by rfl⟩) R43703
theorem R94679 : Reach 94679 := rs (se 1 (by rfl) ⟨71009, by rfl⟩) R142019
theorem R61991 : Reach 61991 := rs (se 1 (by rfl) ⟨46493, by rfl⟩) R92987
theorem R848555 : Reach 848555 := rs (se 1 (by rfl) ⟨636416, by rfl⟩) R1272833
theorem R29435 : Reach 29435 := rs (se 1 (by rfl) ⟨22076, by rfl⟩) R44153
theorem R1078109 : Reach 1078109 := rs (se 3 (by rfl) ⟨202145, by rfl⟩) R404291
theorem R127939 : Reach 127939 := rs (se 1 (by rfl) ⟨95954, by rfl⟩) R191909
theorem R29651 : Reach 29651 := rs (se 1 (by rfl) ⟨22238, by rfl⟩) R44477
theorem R29737 : Reach 29737 := rs (se 2 (by rfl) ⟨11151, by rfl⟩) R22303
theorem R29767 : Reach 29767 := rs (se 1 (by rfl) ⟨22325, by rfl⟩) R44651
theorem R29801 : Reach 29801 := rs (se 2 (by rfl) ⟨11175, by rfl⟩) R22351
theorem R29879 : Reach 29879 := rs (se 1 (by rfl) ⟨22409, by rfl⟩) R44819
theorem R488693 : Reach 488693 := rs (se 5 (by rfl) ⟨22907, by rfl⟩) R45815
theorem R95579 : Reach 95579 := rs (se 1 (by rfl) ⟨71684, by rfl⟩) R143369
theorem R62945 : Reach 62945 := rs (se 2 (by rfl) ⟨23604, by rfl⟩) R47209
theorem R63071 : Reach 63071 := rs (se 1 (by rfl) ⟨47303, by rfl⟩) R94607
theorem R30431 : Reach 30431 := rs (se 1 (by rfl) ⟨22823, by rfl⟩) R45647
theorem R30455 : Reach 30455 := rs (se 1 (by rfl) ⟨22841, by rfl⟩) R45683
theorem R96137 : Reach 96137 := rs (se 2 (by rfl) ⟨36051, by rfl⟩) R72103
theorem R30635 : Reach 30635 := rs (se 1 (by rfl) ⟨22976, by rfl⟩) R45953
theorem R30761 : Reach 30761 := rs (se 2 (by rfl) ⟨11535, by rfl⟩) R23071
theorem R2717873 : Reach 2717873 := rs (se 2 (by rfl) ⟨1019202, by rfl⟩) R2038405
theorem R30955 : Reach 30955 := rs (se 1 (by rfl) ⟨23216, by rfl⟩) R46433
theorem R63919 : Reach 63919 := rs (se 1 (by rfl) ⟨47939, by rfl⟩) R95879
theorem R96707 : Reach 96707 := rs (se 1 (by rfl) ⟨72530, by rfl⟩) R145061
theorem R31175 : Reach 31175 := rs (se 1 (by rfl) ⟨23381, by rfl⟩) R46763
theorem R31337 : Reach 31337 := rs (se 2 (by rfl) ⟨11751, by rfl⟩) R23503
theorem R31391 : Reach 31391 := rs (se 1 (by rfl) ⟨23543, by rfl⟩) R47087
theorem R31535 : Reach 31535 := rs (se 1 (by rfl) ⟨23651, by rfl⟩) R47303
theorem R64415 : Reach 64415 := rs (se 1 (by rfl) ⟨48311, by rfl⟩) R96623
theorem R97361 : Reach 97361 := rs (se 2 (by rfl) ⟨36510, by rfl⟩) R73021
theorem R31967 : Reach 31967 := rs (se 1 (by rfl) ⟨23975, by rfl⟩) R47951
theorem R163205 : Reach 163205 := rs (se 4 (by rfl) ⟨15300, by rfl⟩) R30601
theorem R32251 : Reach 32251 := rs (se 1 (by rfl) ⟨24188, by rfl⟩) R48377
theorem R32521 : Reach 32521 := rs (se 2 (by rfl) ⟨12195, by rfl⟩) R24391
theorem R65423 : Reach 65423 := rs (se 1 (by rfl) ⟨49067, by rfl⟩) R98135
theorem R33043 : Reach 33043 := rs (se 1 (by rfl) ⟨24782, by rfl⟩) R49565
theorem R98657 : Reach 98657 := rs (se 2 (by rfl) ⟨36996, by rfl⟩) R73993
theorem R33185 : Reach 33185 := rs (se 2 (by rfl) ⟨12444, by rfl⟩) R24889
theorem R66055 : Reach 66055 := rs (se 1 (by rfl) ⟨49541, by rfl⟩) R99083
theorem R66365 : Reach 66365 := rs (se 3 (by rfl) ⟨12443, by rfl⟩) R24887
theorem R66415 : Reach 66415 := rs (se 1 (by rfl) ⟨49811, by rfl⟩) R99623
theorem R33743 : Reach 33743 := rs (se 1 (by rfl) ⟨25307, by rfl⟩) R50615
theorem R33983 : Reach 33983 := rs (se 1 (by rfl) ⟨25487, by rfl⟩) R50975
theorem R67067 : Reach 67067 := rs (se 1 (by rfl) ⟨50300, by rfl⟩) R100601
theorem R165665 : Reach 165665 := rs (se 2 (by rfl) ⟨62124, by rfl⟩) R124249
theorem R34681 : Reach 34681 := rs (se 2 (by rfl) ⟨13005, by rfl⟩) R26011
theorem R34715 : Reach 34715 := rs (se 1 (by rfl) ⟨26036, by rfl⟩) R52073
theorem R67547 : Reach 67547 := rs (se 1 (by rfl) ⟨50660, by rfl⟩) R101321
theorem R67729 : Reach 67729 := rs (se 2 (by rfl) ⟨25398, by rfl⟩) R50797
theorem R461321 : Reach 461321 := rs (se 2 (by rfl) ⟨172995, by rfl⟩) R345991
theorem R35471 : Reach 35471 := rs (se 1 (by rfl) ⟨26603, by rfl⟩) R53207
theorem R35495 : Reach 35495 := rs (se 1 (by rfl) ⟨26621, by rfl⟩) R53243
theorem R35615 : Reach 35615 := rs (se 1 (by rfl) ⟨26711, by rfl⟩) R53423
theorem R1149815 : Reach 1149815 := rs (se 1 (by rfl) ⟨862361, by rfl⟩) R1724723
theorem R134135 : Reach 134135 := rs (se 1 (by rfl) ⟨100601, by rfl⟩) R201203
theorem R36071 : Reach 36071 := rs (se 1 (by rfl) ⟨27053, by rfl⟩) R54107
theorem R36443 : Reach 36443 := rs (se 1 (by rfl) ⟨27332, by rfl⟩) R54665
theorem R560965 : Reach 560965 := rs (se 4 (by rfl) ⟨52590, by rfl⟩) R105181
theorem R69605 : Reach 69605 := rs (se 4 (by rfl) ⟨6525, by rfl⟩) R13051
theorem R69821 : Reach 69821 := rs (se 3 (by rfl) ⟨13091, by rfl⟩) R26183
theorem R37223 : Reach 37223 := rs (se 1 (by rfl) ⟨27917, by rfl⟩) R55835
theorem R37277 : Reach 37277 := rs (se 3 (by rfl) ⟨6989, by rfl⟩) R13979
theorem R37847 : Reach 37847 := rs (se 1 (by rfl) ⟨28385, by rfl⟩) R56771
theorem R37999 : Reach 37999 := rs (se 1 (by rfl) ⟨28499, by rfl⟩) R56999
theorem R103535 : Reach 103535 := rs (se 1 (by rfl) ⟨77651, by rfl⟩) R155303
theorem R365867 : Reach 365867 := rs (se 1 (by rfl) ⟨274400, by rfl⟩) R548801
theorem R71219 : Reach 71219 := rs (se 1 (by rfl) ⟨53414, by rfl⟩) R106829
theorem R38537 : Reach 38537 := rs (se 2 (by rfl) ⟨14451, by rfl⟩) R28903
theorem R1513363 : Reach 1513363 := rs (se 1 (by rfl) ⟨1135022, by rfl⟩) R2270045
theorem R465011 : Reach 465011 := rs (se 1 (by rfl) ⟨348758, by rfl⟩) R697517
theorem R137645 : Reach 137645 := rs (se 3 (by rfl) ⟨25808, by rfl⟩) R51617
theorem R72161 : Reach 72161 := rs (se 2 (by rfl) ⟨27060, by rfl⟩) R54121
theorem R301619 : Reach 301619 := rs (se 1 (by rfl) ⟨226214, by rfl⟩) R452429
theorem R170585 : Reach 170585 := rs (se 2 (by rfl) ⟨63969, by rfl⟩) R127939
theorem R39527 : Reach 39527 := rs (se 1 (by rfl) ⟨29645, by rfl⟩) R59291
theorem R39649 : Reach 39649 := rs (se 2 (by rfl) ⟨14868, by rfl⟩) R29737
theorem R39689 : Reach 39689 := rs (se 2 (by rfl) ⟨14883, by rfl⟩) R29767
theorem R105569 : Reach 105569 := rs (se 2 (by rfl) ⟨39588, by rfl⟩) R79177
theorem R72839 : Reach 72839 := rs (se 1 (by rfl) ⟨54629, by rfl⟩) R109259
theorem R40679 : Reach 40679 := rs (se 1 (by rfl) ⟨30509, by rfl⟩) R61019
theorem R41147 : Reach 41147 := rs (se 1 (by rfl) ⟨30860, by rfl⟩) R61721
theorem R41273 : Reach 41273 := rs (se 2 (by rfl) ⟨15477, by rfl⟩) R30955
theorem R41327 : Reach 41327 := rs (se 1 (by rfl) ⟨30995, by rfl⟩) R61991
theorem R565703 : Reach 565703 := rs (se 1 (by rfl) ⟨424277, by rfl⟩) R848555
theorem R74267 : Reach 74267 := rs (se 1 (by rfl) ⟨55700, by rfl⟩) R111401
theorem R270911 : Reach 270911 := rs (se 1 (by rfl) ⟨203183, by rfl⟩) R406367
theorem R664301 : Reach 664301 := rs (se 3 (by rfl) ⟨124556, by rfl⟩) R249113
theorem R205577 : Reach 205577 := rs (se 2 (by rfl) ⟨77091, by rfl⟩) R154183
theorem R140129 : Reach 140129 := rs (se 2 (by rfl) ⟨52548, by rfl⟩) R105097
theorem R238565 : Reach 238565 := rs (se 4 (by rfl) ⟨22365, by rfl⟩) R44731
theorem R41963 : Reach 41963 := rs (se 1 (by rfl) ⟨31472, by rfl⟩) R62945
theorem R468017 : Reach 468017 := rs (se 2 (by rfl) ⟨175506, by rfl⟩) R351013
theorem R42047 : Reach 42047 := rs (se 1 (by rfl) ⟨31535, by rfl⟩) R63071
theorem R75005 : Reach 75005 := rs (se 3 (by rfl) ⟨14063, by rfl⟩) R28127
theorem R1811915 : Reach 1811915 := rs (se 1 (by rfl) ⟨1358936, by rfl⟩) R2717873
theorem R42943 : Reach 42943 := rs (se 1 (by rfl) ⟨32207, by rfl⟩) R64415
theorem R43001 : Reach 43001 := rs (se 2 (by rfl) ⟨16125, by rfl⟩) R32251
theorem R75937 : Reach 75937 := rs (se 2 (by rfl) ⟨28476, by rfl⟩) R56953
theorem R108803 : Reach 108803 := rs (se 1 (by rfl) ⟨81602, by rfl⟩) R163205
theorem R43361 : Reach 43361 := rs (se 2 (by rfl) ⟨16260, by rfl⟩) R32521
theorem R535085 : Reach 535085 := rs (se 3 (by rfl) ⟨100328, by rfl⟩) R200657
theorem R43615 : Reach 43615 := rs (se 1 (by rfl) ⟨32711, by rfl⟩) R65423
theorem R142087 : Reach 142087 := rs (se 1 (by rfl) ⟨106565, by rfl⟩) R213131
theorem R240569 : Reach 240569 := rs (se 2 (by rfl) ⟨90213, by rfl⟩) R180427
theorem R2141315 : Reach 2141315 := rs (se 1 (by rfl) ⟨1605986, by rfl⟩) R3211973
theorem R77195 : Reach 77195 := rs (se 1 (by rfl) ⟨57896, by rfl⟩) R115793
theorem R44513 : Reach 44513 := rs (se 2 (by rfl) ⟨16692, by rfl⟩) R33385
theorem R77921 : Reach 77921 := rs (se 2 (by rfl) ⟨29220, by rfl⟩) R58441
theorem R340199 : Reach 340199 := rs (se 1 (by rfl) ⟨255149, by rfl⟩) R510299
theorem R45319 : Reach 45319 := rs (se 1 (by rfl) ⟨33989, by rfl⟩) R67979
theorem R45431 : Reach 45431 := rs (se 1 (by rfl) ⟨34073, by rfl⟩) R68147
theorem R12827 : Reach 12827 := rs (se 1 (by rfl) ⟨9620, by rfl⟩) R19241
theorem R12967 : Reach 12967 := rs (se 1 (by rfl) ⟨9725, by rfl⟩) R19451
theorem R111293 : Reach 111293 := rs (se 3 (by rfl) ⟨20867, by rfl⟩) R41735
theorem R13007 : Reach 13007 := rs (se 1 (by rfl) ⟨9755, by rfl⟩) R19511
theorem R13087 : Reach 13087 := rs (se 1 (by rfl) ⟨9815, by rfl⟩) R19631
theorem R341171 : Reach 341171 := rs (se 1 (by rfl) ⟨255878, by rfl⟩) R511757
theorem R79055 : Reach 79055 := rs (se 1 (by rfl) ⟨59291, by rfl⟩) R118583
theorem R13567 : Reach 13567 := rs (se 1 (by rfl) ⟨10175, by rfl⟩) R20351
theorem R13695 : Reach 13695 := rs (se 1 (by rfl) ⟨10271, by rfl⟩) R20543
theorem R79379 : Reach 79379 := rs (se 1 (by rfl) ⟨59534, by rfl⟩) R119069
theorem R13851 : Reach 13851 := rs (se 1 (by rfl) ⟨10388, by rfl⟩) R20777
theorem R14031 : Reach 14031 := rs (se 1 (by rfl) ⟨10523, by rfl⟩) R21047
theorem R46817 : Reach 46817 := rs (se 2 (by rfl) ⟨17556, by rfl⟩) R35113
theorem R14271 : Reach 14271 := rs (se 1 (by rfl) ⟨10703, by rfl⟩) R21407
theorem R14399 : Reach 14399 := rs (se 1 (by rfl) ⟨10799, by rfl⟩) R21599
theorem R14439 : Reach 14439 := rs (se 1 (by rfl) ⟨10829, by rfl⟩) R21659
theorem R47591 : Reach 47591 := rs (se 1 (by rfl) ⟨35693, by rfl⟩) R71387
theorem R14895 : Reach 14895 := rs (se 1 (by rfl) ⟨11171, by rfl⟩) R22343
theorem R441139 : Reach 441139 := rs (se 1 (by rfl) ⟨330854, by rfl⟩) R661709
theorem R15295 : Reach 15295 := rs (se 1 (by rfl) ⟨11471, by rfl⟩) R22943
theorem R48073 : Reach 48073 := rs (se 2 (by rfl) ⟨18027, by rfl⟩) R36055
theorem R80851 : Reach 80851 := rs (se 1 (by rfl) ⟨60638, by rfl⟩) R121277
theorem R15343 : Reach 15343 := rs (se 1 (by rfl) ⟨11507, by rfl⟩) R23015
theorem R15839 : Reach 15839 := rs (se 1 (by rfl) ⟨11879, by rfl⟩) R23759
theorem R114173 : Reach 114173 := rs (se 3 (by rfl) ⟨21407, by rfl⟩) R42815
theorem R15919 : Reach 15919 := rs (se 1 (by rfl) ⟨11939, by rfl⟩) R23879
theorem R16027 : Reach 16027 := rs (se 1 (by rfl) ⟨12020, by rfl⟩) R24041
theorem R48815 : Reach 48815 := rs (se 1 (by rfl) ⟨36611, by rfl⟩) R73223
theorem R16091 : Reach 16091 := rs (se 1 (by rfl) ⟨12068, by rfl⟩) R24137
theorem R16123 : Reach 16123 := rs (se 1 (by rfl) ⟨12092, by rfl⟩) R24185
theorem R16287 : Reach 16287 := rs (se 1 (by rfl) ⟨12215, by rfl⟩) R24431
theorem R81911 : Reach 81911 := rs (se 1 (by rfl) ⟨61433, by rfl⟩) R122867
theorem R16591 : Reach 16591 := rs (se 1 (by rfl) ⟨12443, by rfl⟩) R24887
theorem R16743 : Reach 16743 := rs (se 1 (by rfl) ⟨12557, by rfl⟩) R25115
theorem R82295 : Reach 82295 := rs (se 1 (by rfl) ⟨61721, by rfl⟩) R123443
theorem R16863 : Reach 16863 := rs (se 1 (by rfl) ⟨12647, by rfl⟩) R25295
theorem R16871 : Reach 16871 := rs (se 1 (by rfl) ⟨12653, by rfl⟩) R25307
theorem R49747 : Reach 49747 := rs (se 1 (by rfl) ⟨37310, by rfl⟩) R74621
theorem R17115 : Reach 17115 := rs (se 1 (by rfl) ⟨12836, by rfl⟩) R25673
theorem R17147 : Reach 17147 := rs (se 1 (by rfl) ⟨12860, by rfl⟩) R25721
theorem R17275 : Reach 17275 := rs (se 1 (by rfl) ⟨12956, by rfl⟩) R25913
theorem R17401 : Reach 17401 := rs (se 2 (by rfl) ⟨6525, by rfl⟩) R13051
theorem R17455 : Reach 17455 := rs (se 1 (by rfl) ⟨13091, by rfl⟩) R26183
theorem R17529 : Reach 17529 := rs (se 2 (by rfl) ⟨6573, by rfl⟩) R13147
theorem R17575 : Reach 17575 := rs (se 1 (by rfl) ⟨13181, by rfl⟩) R26363
theorem R17591 : Reach 17591 := rs (se 1 (by rfl) ⟨13193, by rfl⟩) R26387
theorem R50495 : Reach 50495 := rs (se 1 (by rfl) ⟨37871, by rfl⟩) R75743
theorem R17727 : Reach 17727 := rs (se 1 (by rfl) ⟨13295, by rfl⟩) R26591
theorem R17735 : Reach 17735 := rs (se 1 (by rfl) ⟨13301, by rfl⟩) R26603
theorem R17767 : Reach 17767 := rs (se 1 (by rfl) ⟨13325, by rfl⟩) R26651
theorem R18011 : Reach 18011 := rs (se 1 (by rfl) ⟨13508, by rfl⟩) R27017
theorem R50951 : Reach 50951 := rs (se 1 (by rfl) ⟨38213, by rfl⟩) R76427
theorem R51167 : Reach 51167 := rs (se 1 (by rfl) ⟨38375, by rfl⟩) R76751
theorem R18399 : Reach 18399 := rs (se 1 (by rfl) ⟨13799, by rfl⟩) R27599
theorem R18409 : Reach 18409 := rs (se 2 (by rfl) ⟨6903, by rfl⟩) R13807
theorem R51191 : Reach 51191 := rs (se 1 (by rfl) ⟨38393, by rfl⟩) R76787
theorem R18459 : Reach 18459 := rs (se 1 (by rfl) ⟨13844, by rfl⟩) R27689
theorem R18479 : Reach 18479 := rs (se 1 (by rfl) ⟨13859, by rfl⟩) R27719
theorem R18553 : Reach 18553 := rs (se 2 (by rfl) ⟨6957, by rfl⟩) R13915
theorem R18615 : Reach 18615 := rs (se 1 (by rfl) ⟨13961, by rfl⟩) R27923
theorem R51407 : Reach 51407 := rs (se 1 (by rfl) ⟨38555, by rfl⟩) R77111
theorem R18639 : Reach 18639 := rs (se 1 (by rfl) ⟨13979, by rfl⟩) R27959
theorem R18743 : Reach 18743 := rs (se 1 (by rfl) ⟨14057, by rfl⟩) R28115
theorem R18751 : Reach 18751 := rs (se 1 (by rfl) ⟨14063, by rfl⟩) R28127
theorem R18895 : Reach 18895 := rs (se 1 (by rfl) ⟨14171, by rfl⟩) R28343
theorem R18923 : Reach 18923 := rs (se 1 (by rfl) ⟨14192, by rfl⟩) R28385
theorem R18937 : Reach 18937 := rs (se 2 (by rfl) ⟨7101, by rfl⟩) R14203
theorem R18985 : Reach 18985 := rs (se 2 (by rfl) ⟨7119, by rfl⟩) R14239
theorem R19035 : Reach 19035 := rs (se 1 (by rfl) ⟨14276, by rfl⟩) R28553
theorem R19163 : Reach 19163 := rs (se 1 (by rfl) ⟨14372, by rfl⟩) R28745
theorem R19179 : Reach 19179 := rs (se 1 (by rfl) ⟨14384, by rfl⟩) R28769
theorem R19199 : Reach 19199 := rs (se 1 (by rfl) ⟨14399, by rfl⟩) R28799
theorem R19209 : Reach 19209 := rs (se 2 (by rfl) ⟨7203, by rfl⟩) R14407
theorem R19423 : Reach 19423 := rs (se 1 (by rfl) ⟨14567, by rfl⟩) R29135
theorem R52271 : Reach 52271 := rs (se 1 (by rfl) ⟨39203, by rfl⟩) R78407
theorem R19623 : Reach 19623 := rs (se 1 (by rfl) ⟨14717, by rfl⟩) R29435
theorem R85225 : Reach 85225 := rs (se 2 (by rfl) ⟨31959, by rfl⟩) R63919
theorem R19767 : Reach 19767 := rs (se 1 (by rfl) ⟨14825, by rfl⟩) R29651
theorem R52591 : Reach 52591 := rs (se 1 (by rfl) ⟨39443, by rfl⟩) R78887
theorem R19867 : Reach 19867 := rs (se 1 (by rfl) ⟨14900, by rfl⟩) R29801
theorem R19919 : Reach 19919 := rs (se 1 (by rfl) ⟨14939, by rfl⟩) R29879
theorem R20009 : Reach 20009 := rs (se 2 (by rfl) ⟨7503, by rfl⟩) R15007
theorem R151085 : Reach 151085 := rs (se 3 (by rfl) ⟨28328, by rfl⟩) R56657
theorem R446147 : Reach 446147 := rs (se 1 (by rfl) ⟨334610, by rfl⟩) R669221
theorem R20287 : Reach 20287 := rs (se 1 (by rfl) ⟨15215, by rfl⟩) R30431
theorem R20303 : Reach 20303 := rs (se 1 (by rfl) ⟨15227, by rfl⟩) R30455
theorem R20423 : Reach 20423 := rs (se 1 (by rfl) ⟨15317, by rfl⟩) R30635
theorem R20507 : Reach 20507 := rs (se 1 (by rfl) ⟨15380, by rfl⟩) R30761
theorem R53351 : Reach 53351 := rs (se 1 (by rfl) ⟨40013, by rfl⟩) R80027
theorem R20783 : Reach 20783 := rs (se 1 (by rfl) ⟨15587, by rfl⟩) R31175
theorem R20891 : Reach 20891 := rs (se 1 (by rfl) ⟨15668, by rfl⟩) R31337
theorem R20927 : Reach 20927 := rs (se 1 (by rfl) ⟨15695, by rfl⟩) R31391
theorem R21023 : Reach 21023 := rs (se 1 (by rfl) ⟨15767, by rfl⟩) R31535
theorem R316007 : Reach 316007 := rs (se 1 (by rfl) ⟨237005, by rfl⟩) R474011
theorem R21311 : Reach 21311 := rs (se 1 (by rfl) ⟨15983, by rfl⟩) R31967
theorem R54269 : Reach 54269 := rs (se 3 (by rfl) ⟨10175, by rfl⟩) R20351
theorem R54539 : Reach 54539 := rs (se 1 (by rfl) ⟨40904, by rfl⟩) R81809
theorem R22207 : Reach 22207 := rs (se 1 (by rfl) ⟨16655, by rfl⟩) R33311
theorem R120521 : Reach 120521 := rs (se 2 (by rfl) ⟨45195, by rfl⟩) R90391
theorem R87803 : Reach 87803 := rs (se 1 (by rfl) ⟨65852, by rfl⟩) R131705
theorem R186545 : Reach 186545 := rs (se 2 (by rfl) ⟨69954, by rfl⟩) R139909
theorem R22715 : Reach 22715 := rs (se 1 (by rfl) ⟨17036, by rfl⟩) R34073
theorem R23135 : Reach 23135 := rs (se 1 (by rfl) ⟨17351, by rfl⟩) R34703
theorem R56159 : Reach 56159 := rs (se 1 (by rfl) ⟨42119, by rfl⟩) R84239
theorem R23399 : Reach 23399 := rs (se 1 (by rfl) ⟨17549, by rfl⟩) R35099
theorem R23465 : Reach 23465 := rs (se 2 (by rfl) ⟨8799, by rfl⟩) R17599
theorem R23507 : Reach 23507 := rs (se 1 (by rfl) ⟨17630, by rfl⟩) R35261
theorem R23615 : Reach 23615 := rs (se 1 (by rfl) ⟨17711, by rfl⟩) R35423
theorem R23657 : Reach 23657 := rs (se 2 (by rfl) ⟨8871, by rfl⟩) R17743
theorem R7625933 : Reach 7625933 := rs (se 3 (by rfl) ⟨1429862, by rfl⟩) R2859725
theorem R23777 : Reach 23777 := rs (se 2 (by rfl) ⟨8916, by rfl⟩) R17833
theorem R56699 : Reach 56699 := rs (se 1 (by rfl) ⟨42524, by rfl⟩) R85049
theorem R23935 : Reach 23935 := rs (se 1 (by rfl) ⟨17951, by rfl⟩) R35903
theorem R89785 : Reach 89785 := rs (se 2 (by rfl) ⟨33669, by rfl⟩) R67339
theorem R24287 : Reach 24287 := rs (se 1 (by rfl) ⟨18215, by rfl⟩) R36431
theorem R188203 : Reach 188203 := rs (se 1 (by rfl) ⟨141152, by rfl⟩) R282305
theorem R57185 : Reach 57185 := rs (se 2 (by rfl) ⟨21444, by rfl⟩) R42889
theorem R24617 : Reach 24617 := rs (se 2 (by rfl) ⟨9231, by rfl⟩) R18463
theorem R24647 : Reach 24647 := rs (se 1 (by rfl) ⟨18485, by rfl⟩) R36971
theorem R24683 : Reach 24683 := rs (se 1 (by rfl) ⟨18512, by rfl⟩) R37025
theorem R24767 : Reach 24767 := rs (se 1 (by rfl) ⟨18575, by rfl⟩) R37151
theorem R24953 : Reach 24953 := rs (se 2 (by rfl) ⟨9357, by rfl⟩) R18715
theorem R57743 : Reach 57743 := rs (se 1 (by rfl) ⟨43307, by rfl⟩) R86615
theorem R680399 : Reach 680399 := rs (se 1 (by rfl) ⟨510299, by rfl⟩) R1020599
theorem R516611 : Reach 516611 := rs (se 1 (by rfl) ⟨387458, by rfl⟩) R774917
theorem R156167 : Reach 156167 := rs (se 1 (by rfl) ⟨117125, by rfl⟩) R234251
theorem R25247 : Reach 25247 := rs (se 1 (by rfl) ⟨18935, by rfl⟩) R37871
theorem R58103 : Reach 58103 := rs (se 1 (by rfl) ⟨43577, by rfl⟩) R87155
theorem R25385 : Reach 25385 := rs (se 2 (by rfl) ⟨9519, by rfl⟩) R19039
theorem R25583 : Reach 25583 := rs (se 1 (by rfl) ⟨19187, by rfl⟩) R38375
theorem R25595 : Reach 25595 := rs (se 1 (by rfl) ⟨19196, by rfl⟩) R38393
theorem R25655 : Reach 25655 := rs (se 1 (by rfl) ⟨19241, by rfl⟩) R38483
theorem R25703 : Reach 25703 := rs (se 1 (by rfl) ⟨19277, by rfl⟩) R38555
theorem R25775 : Reach 25775 := rs (se 1 (by rfl) ⟨19331, by rfl⟩) R38663
theorem R25825 : Reach 25825 := rs (se 2 (by rfl) ⟨9684, by rfl⟩) R19369
theorem R25835 : Reach 25835 := rs (se 1 (by rfl) ⟨19376, by rfl⟩) R38753
theorem R58643 : Reach 58643 := rs (se 1 (by rfl) ⟨43982, by rfl⟩) R87965
theorem R451889 : Reach 451889 := rs (se 2 (by rfl) ⟨169458, by rfl⟩) R338917
theorem R877877 : Reach 877877 := rs (se 5 (by rfl) ⟨41150, by rfl⟩) R82301
theorem R124523 : Reach 124523 := rs (se 1 (by rfl) ⟨93392, by rfl⟩) R186785
theorem R59075 : Reach 59075 := rs (se 1 (by rfl) ⟨44306, by rfl⟩) R88613
theorem R59183 : Reach 59183 := rs (se 1 (by rfl) ⟨44387, by rfl⟩) R88775
theorem R223073 : Reach 223073 := rs (se 2 (by rfl) ⟨83652, by rfl⟩) R167305
theorem R124901 : Reach 124901 := rs (se 4 (by rfl) ⟨11709, by rfl⟩) R23419
theorem R27449 : Reach 27449 := rs (se 2 (by rfl) ⟨10293, by rfl⟩) R20587
theorem R27823 : Reach 27823 := rs (se 1 (by rfl) ⟨20867, by rfl⟩) R41735
theorem R60659 : Reach 60659 := rs (se 1 (by rfl) ⟨45494, by rfl⟩) R90989
theorem R28079 : Reach 28079 := rs (se 1 (by rfl) ⟨21059, by rfl⟩) R42119
theorem R93635 : Reach 93635 := rs (se 1 (by rfl) ⟨70226, by rfl⟩) R140453
theorem R28331 : Reach 28331 := rs (se 1 (by rfl) ⟨21248, by rfl⟩) R42497
theorem R28379 : Reach 28379 := rs (se 1 (by rfl) ⟨21284, by rfl⟩) R42569
theorem R61181 : Reach 61181 := rs (se 3 (by rfl) ⟨11471, by rfl⟩) R22943
theorem R159583 : Reach 159583 := rs (se 1 (by rfl) ⟨119687, by rfl⟩) R239375
theorem R61373 : Reach 61373 := rs (se 3 (by rfl) ⟨11507, by rfl⟩) R23015
theorem R28649 : Reach 28649 := rs (se 2 (by rfl) ⟨10743, by rfl⟩) R21487
theorem R28703 : Reach 28703 := rs (se 1 (by rfl) ⟨21527, by rfl⟩) R43055
theorem R28871 : Reach 28871 := rs (se 1 (by rfl) ⟨21653, by rfl⟩) R43307
theorem R28999 : Reach 28999 := rs (se 1 (by rfl) ⟨21749, by rfl⟩) R43499
theorem R61775 : Reach 61775 := rs (se 1 (by rfl) ⟨46331, by rfl⟩) R92663
theorem R29051 : Reach 29051 := rs (se 1 (by rfl) ⟨21788, by rfl⟩) R43577
theorem R29321 : Reach 29321 := rs (se 2 (by rfl) ⟨10995, by rfl⟩) R21991
theorem R553661 : Reach 553661 := rs (se 3 (by rfl) ⟨103811, by rfl⟩) R207623
theorem R29531 : Reach 29531 := rs (se 1 (by rfl) ⟨22148, by rfl⟩) R44297
theorem R29537 : Reach 29537 := rs (se 2 (by rfl) ⟨11076, by rfl⟩) R22153
theorem R29551 : Reach 29551 := rs (se 1 (by rfl) ⟨22163, by rfl⟩) R44327
theorem R29561 : Reach 29561 := rs (se 2 (by rfl) ⟨11085, by rfl⟩) R22171
theorem R62639 : Reach 62639 := rs (se 1 (by rfl) ⟨46979, by rfl⟩) R93959
theorem R30059 : Reach 30059 := rs (se 1 (by rfl) ⟨22544, by rfl⟩) R45089
theorem R30191 : Reach 30191 := rs (se 1 (by rfl) ⟨22643, by rfl⟩) R45287
theorem R95741 : Reach 95741 := rs (se 3 (by rfl) ⟨17951, by rfl⟩) R35903
theorem R30311 : Reach 30311 := rs (se 1 (by rfl) ⟨22733, by rfl⟩) R45467
theorem R128623 : Reach 128623 := rs (se 1 (by rfl) ⟨96467, by rfl⟩) R192935
theorem R30329 : Reach 30329 := rs (se 2 (by rfl) ⟨11373, by rfl⟩) R22747
theorem R63119 : Reach 63119 := rs (se 1 (by rfl) ⟨47339, by rfl⟩) R94679
theorem R718739 : Reach 718739 := rs (se 1 (by rfl) ⟨539054, by rfl⟩) R1078109
theorem R30689 : Reach 30689 := rs (se 2 (by rfl) ⟨11508, by rfl⟩) R23017
theorem R325795 : Reach 325795 := rs (se 1 (by rfl) ⟨244346, by rfl⟩) R488693
theorem R30887 : Reach 30887 := rs (se 1 (by rfl) ⟨23165, by rfl⟩) R46331
theorem R63719 : Reach 63719 := rs (se 1 (by rfl) ⟨47789, by rfl⟩) R95579
theorem R96673 : Reach 96673 := rs (se 2 (by rfl) ⟨36252, by rfl⟩) R72505
theorem R31225 : Reach 31225 := rs (se 2 (by rfl) ⟨11709, by rfl⟩) R23419
theorem R31259 : Reach 31259 := rs (se 1 (by rfl) ⟨23444, by rfl⟩) R46889
theorem R64091 : Reach 64091 := rs (se 1 (by rfl) ⟨48068, by rfl⟩) R96137
theorem R31495 : Reach 31495 := rs (se 1 (by rfl) ⟨23621, by rfl⟩) R47243
theorem R64471 : Reach 64471 := rs (se 1 (by rfl) ⟨48353, by rfl⟩) R96707
theorem R97631 : Reach 97631 := rs (se 1 (by rfl) ⟨73223, by rfl⟩) R146447
theorem R64907 : Reach 64907 := rs (se 1 (by rfl) ⟨48680, by rfl⟩) R97361
theorem R32183 : Reach 32183 := rs (se 1 (by rfl) ⟨24137, by rfl⟩) R48275
theorem R32363 : Reach 32363 := rs (se 1 (by rfl) ⟨24272, by rfl⟩) R48545
theorem R32575 : Reach 32575 := rs (se 1 (by rfl) ⟨24431, by rfl⟩) R48863
theorem R32633 : Reach 32633 := rs (se 2 (by rfl) ⟨12237, by rfl⟩) R24475
theorem R32723 : Reach 32723 := rs (se 1 (by rfl) ⟨24542, by rfl⟩) R49085
theorem R32737 : Reach 32737 := rs (se 2 (by rfl) ⟨12276, by rfl⟩) R24553
theorem R65771 : Reach 65771 := rs (se 1 (by rfl) ⟨49328, by rfl⟩) R98657
theorem R66329 : Reach 66329 := rs (se 2 (by rfl) ⟨24873, by rfl⟩) R49747
theorem R33967 : Reach 33967 := rs (se 1 (by rfl) ⟨25475, by rfl⟩) R50951
theorem R34111 : Reach 34111 := rs (se 1 (by rfl) ⟨25583, by rfl⟩) R51167
theorem R34127 : Reach 34127 := rs (se 1 (by rfl) ⟨25595, by rfl⟩) R51191
theorem R34271 : Reach 34271 := rs (se 1 (by rfl) ⟨25703, by rfl⟩) R51407
theorem R722429 : Reach 722429 := rs (se 3 (by rfl) ⟨135455, by rfl⟩) R270911
theorem R34433 : Reach 34433 := rs (se 2 (by rfl) ⟨12912, by rfl⟩) R25825
theorem R34685 : Reach 34685 := rs (se 3 (by rfl) ⟨6503, by rfl⟩) R13007
theorem R1771469 : Reach 1771469 := rs (se 3 (by rfl) ⟨332150, by rfl⟩) R664301
theorem R34847 : Reach 34847 := rs (se 1 (by rfl) ⟨26135, by rfl⟩) R52271
theorem R100723 : Reach 100723 := rs (se 1 (by rfl) ⟨75542, by rfl⟩) R151085
theorem R297431 : Reach 297431 := rs (se 1 (by rfl) ⟨223073, by rfl⟩) R446147
theorem R100925 : Reach 100925 := rs (se 3 (by rfl) ⟨18923, by rfl⟩) R37847
theorem R35567 : Reach 35567 := rs (se 1 (by rfl) ⟨26675, by rfl⟩) R53351
theorem R101249 : Reach 101249 := rs (se 2 (by rfl) ⟨37968, by rfl⟩) R75937
theorem R36179 : Reach 36179 := rs (se 1 (by rfl) ⟨27134, by rfl⟩) R54269
theorem R69023 : Reach 69023 := rs (se 1 (by rfl) ⟨51767, by rfl⟩) R103535
theorem R36359 : Reach 36359 := rs (se 1 (by rfl) ⟨27269, by rfl⟩) R54539
theorem R37097 : Reach 37097 := rs (se 2 (by rfl) ⟨13911, by rfl⟩) R27823
theorem R201079 : Reach 201079 := rs (se 1 (by rfl) ⟨150809, by rfl⟩) R301619
theorem R70121 : Reach 70121 := rs (se 2 (by rfl) ⟨26295, by rfl⟩) R52591
theorem R37439 : Reach 37439 := rs (se 1 (by rfl) ⟨28079, by rfl⟩) R56159
theorem R70379 : Reach 70379 := rs (se 1 (by rfl) ⟨52784, by rfl⟩) R105569
theorem R5083955 : Reach 5083955 := rs (se 1 (by rfl) ⟨3812966, by rfl⟩) R7625933
theorem R37799 : Reach 37799 := rs (se 1 (by rfl) ⟨28349, by rfl⟩) R56699
theorem R38123 : Reach 38123 := rs (se 1 (by rfl) ⟨28592, by rfl⟩) R57185
theorem R38495 : Reach 38495 := rs (se 1 (by rfl) ⟨28871, by rfl⟩) R57743
theorem R104111 : Reach 104111 := rs (se 1 (by rfl) ⟨78083, by rfl⟩) R156167
theorem R38665 : Reach 38665 := rs (se 2 (by rfl) ⟨14499, by rfl⟩) R28999
theorem R38735 : Reach 38735 := rs (se 1 (by rfl) ⟨29051, by rfl⟩) R58103
theorem R137051 : Reach 137051 := rs (se 1 (by rfl) ⟨102788, by rfl⟩) R205577
theorem R202661 : Reach 202661 := rs (se 4 (by rfl) ⟨18999, by rfl⟩) R37999
theorem R39095 : Reach 39095 := rs (se 1 (by rfl) ⟨29321, by rfl⟩) R58643
theorem R301259 : Reach 301259 := rs (se 1 (by rfl) ⟨225944, by rfl⟩) R451889
theorem R39383 : Reach 39383 := rs (se 1 (by rfl) ⟨29537, by rfl⟩) R59075
theorem R39401 : Reach 39401 := rs (se 2 (by rfl) ⟨14775, by rfl⟩) R29551
theorem R39455 : Reach 39455 := rs (se 1 (by rfl) ⟨29591, by rfl⟩) R59183
theorem R72535 : Reach 72535 := rs (se 1 (by rfl) ⟨54401, by rfl⟩) R108803
theorem R171497 : Reach 171497 := rs (se 2 (by rfl) ⟨64311, by rfl⟩) R128623
theorem R40439 : Reach 40439 := rs (se 1 (by rfl) ⟨30329, by rfl⟩) R60659
theorem R40787 : Reach 40787 := rs (se 1 (by rfl) ⟨30590, by rfl⟩) R61181
theorem R40915 : Reach 40915 := rs (se 1 (by rfl) ⟨30686, by rfl⟩) R61373
theorem R434393 : Reach 434393 := rs (se 2 (by rfl) ⟨162897, by rfl⟩) R325795
theorem R41183 : Reach 41183 := rs (se 1 (by rfl) ⟨30887, by rfl⟩) R61775
theorem R74195 : Reach 74195 := rs (se 1 (by rfl) ⟨55646, by rfl⟩) R111293
theorem R369107 : Reach 369107 := rs (se 1 (by rfl) ⟨276830, by rfl⟩) R553661
theorem R41633 : Reach 41633 := rs (se 2 (by rfl) ⟨15612, by rfl⟩) R31225
theorem R41759 : Reach 41759 := rs (se 1 (by rfl) ⟨31319, by rfl⟩) R62639
theorem R41993 : Reach 41993 := rs (se 2 (by rfl) ⟨15747, by rfl⟩) R31495
theorem R42079 : Reach 42079 := rs (se 1 (by rfl) ⟨31559, by rfl⟩) R63119
theorem R107801 : Reach 107801 := rs (se 2 (by rfl) ⟨40425, by rfl⟩) R80851
theorem R42479 : Reach 42479 := rs (se 1 (by rfl) ⟨31859, by rfl⟩) R63719
theorem R42727 : Reach 42727 := rs (se 1 (by rfl) ⟨32045, by rfl⟩) R64091
theorem R43271 : Reach 43271 := rs (se 1 (by rfl) ⟨32453, by rfl⟩) R64907
theorem R76115 : Reach 76115 := rs (se 1 (by rfl) ⟨57086, by rfl⟩) R114173
theorem R43433 : Reach 43433 := rs (se 2 (by rfl) ⟨16287, by rfl⟩) R32575
theorem R43649 : Reach 43649 := rs (se 2 (by rfl) ⟨16368, by rfl⟩) R32737
theorem R44057 : Reach 44057 := rs (se 2 (by rfl) ⟨16521, by rfl⟩) R33043
theorem R44243 : Reach 44243 := rs (se 1 (by rfl) ⟨33182, by rfl⟩) R66365
theorem R44711 : Reach 44711 := rs (se 1 (by rfl) ⟨33533, by rfl⟩) R67067
theorem R110443 : Reach 110443 := rs (se 1 (by rfl) ⟨82832, by rfl⟩) R165665
theorem R45031 : Reach 45031 := rs (se 1 (by rfl) ⟨33773, by rfl⟩) R67547
theorem R307547 : Reach 307547 := rs (se 1 (by rfl) ⟨230660, by rfl⟩) R461321
theorem R13279 : Reach 13279 := rs (se 1 (by rfl) ⟨9959, by rfl⟩) R19919
theorem R13339 : Reach 13339 := rs (se 1 (by rfl) ⟨10004, by rfl⟩) R20009
theorem R46241 : Reach 46241 := rs (se 2 (by rfl) ⟨17340, by rfl⟩) R34681
theorem R13535 : Reach 13535 := rs (se 1 (by rfl) ⟨10151, by rfl⟩) R20303
theorem R111901 : Reach 111901 := rs (se 3 (by rfl) ⟨20981, by rfl⟩) R41963
theorem R13615 : Reach 13615 := rs (se 1 (by rfl) ⟨10211, by rfl⟩) R20423
theorem R46403 : Reach 46403 := rs (se 1 (by rfl) ⟨34802, by rfl⟩) R69605
theorem R13671 : Reach 13671 := rs (se 1 (by rfl) ⟨10253, by rfl⟩) R20507
theorem R46547 : Reach 46547 := rs (se 1 (by rfl) ⟨34910, by rfl⟩) R69821
theorem R13855 : Reach 13855 := rs (se 1 (by rfl) ⟨10391, by rfl⟩) R20783
theorem R13927 : Reach 13927 := rs (se 1 (by rfl) ⟨10445, by rfl⟩) R20891
theorem R13951 : Reach 13951 := rs (se 1 (by rfl) ⟨10463, by rfl⟩) R20927
theorem R14015 : Reach 14015 := rs (se 1 (by rfl) ⟨10511, by rfl⟩) R21023
theorem R210671 : Reach 210671 := rs (se 1 (by rfl) ⟨158003, by rfl⟩) R316007
theorem R14207 : Reach 14207 := rs (se 1 (by rfl) ⟨10655, by rfl⟩) R21311
theorem R538613 : Reach 538613 := rs (se 5 (by rfl) ⟨25247, by rfl⟩) R50495
theorem R243911 : Reach 243911 := rs (se 1 (by rfl) ⟨182933, by rfl⟩) R365867
theorem R47479 : Reach 47479 := rs (se 1 (by rfl) ⟨35609, by rfl⟩) R71219
theorem R80347 : Reach 80347 := rs (se 1 (by rfl) ⟨60260, by rfl⟩) R120521
theorem R80509 : Reach 80509 := rs (se 3 (by rfl) ⟨15095, by rfl⟩) R30191
theorem R310007 : Reach 310007 := rs (se 1 (by rfl) ⟨232505, by rfl⟩) R465011
theorem R15143 : Reach 15143 := rs (se 1 (by rfl) ⟨11357, by rfl⟩) R22715
theorem R113633 : Reach 113633 := rs (se 2 (by rfl) ⟨42612, by rfl⟩) R85225
theorem R48107 : Reach 48107 := rs (se 1 (by rfl) ⟨36080, by rfl⟩) R72161
theorem R113723 : Reach 113723 := rs (se 1 (by rfl) ⟨85292, by rfl⟩) R170585
theorem R15423 : Reach 15423 := rs (se 1 (by rfl) ⟨11567, by rfl⟩) R23135
theorem R15599 : Reach 15599 := rs (se 1 (by rfl) ⟨11699, by rfl⟩) R23399
theorem R15643 : Reach 15643 := rs (se 1 (by rfl) ⟨11732, by rfl⟩) R23465
theorem R15671 : Reach 15671 := rs (se 1 (by rfl) ⟨11753, by rfl⟩) R23507
theorem R15743 : Reach 15743 := rs (se 1 (by rfl) ⟨11807, by rfl⟩) R23615
theorem R15771 : Reach 15771 := rs (se 1 (by rfl) ⟨11828, by rfl⟩) R23657
theorem R48559 : Reach 48559 := rs (se 1 (by rfl) ⟨36419, by rfl⟩) R72839
theorem R15851 : Reach 15851 := rs (se 1 (by rfl) ⟨11888, by rfl⟩) R23777
theorem R212777 : Reach 212777 := rs (se 2 (by rfl) ⟨79791, by rfl⟩) R159583
theorem R16191 : Reach 16191 := rs (se 1 (by rfl) ⟨12143, by rfl⟩) R24287
theorem R16411 : Reach 16411 := rs (se 1 (by rfl) ⟨12308, by rfl⟩) R24617
theorem R16431 : Reach 16431 := rs (se 1 (by rfl) ⟨12323, by rfl⟩) R24647
theorem R16455 : Reach 16455 := rs (se 1 (by rfl) ⟨12341, by rfl⟩) R24683
theorem R16511 : Reach 16511 := rs (se 1 (by rfl) ⟨12383, by rfl⟩) R24767
theorem R16635 : Reach 16635 := rs (se 1 (by rfl) ⟨12476, by rfl⟩) R24953
theorem R377135 : Reach 377135 := rs (se 1 (by rfl) ⟨282851, by rfl⟩) R565703
theorem R344407 : Reach 344407 := rs (se 1 (by rfl) ⟨258305, by rfl⟩) R516611
theorem R49511 : Reach 49511 := rs (se 1 (by rfl) ⟨37133, by rfl⟩) R74267
theorem R16831 : Reach 16831 := rs (se 1 (by rfl) ⟨12623, by rfl⟩) R25247
theorem R442867 : Reach 442867 := rs (se 1 (by rfl) ⟨332150, by rfl⟩) R664301
theorem R16923 : Reach 16923 := rs (se 1 (by rfl) ⟨12692, by rfl⟩) R25385
theorem R17055 : Reach 17055 := rs (se 1 (by rfl) ⟨12791, by rfl⟩) R25583
theorem R17063 : Reach 17063 := rs (se 1 (by rfl) ⟨12797, by rfl⟩) R25595
theorem R312011 : Reach 312011 := rs (se 1 (by rfl) ⟨234008, by rfl⟩) R468017
theorem R17103 : Reach 17103 := rs (se 1 (by rfl) ⟨12827, by rfl⟩) R25655
theorem R17135 : Reach 17135 := rs (se 1 (by rfl) ⟨12851, by rfl⟩) R25703
theorem R17183 : Reach 17183 := rs (se 1 (by rfl) ⟨12887, by rfl⟩) R25775
theorem R17223 : Reach 17223 := rs (se 1 (by rfl) ⟨12917, by rfl⟩) R25835
theorem R50003 : Reach 50003 := rs (se 1 (by rfl) ⟨37502, by rfl⟩) R75005
theorem R17289 : Reach 17289 := rs (se 2 (by rfl) ⟨6483, by rfl⟩) R12967
theorem R17449 : Reach 17449 := rs (se 2 (by rfl) ⟨6543, by rfl⟩) R13087
theorem R83015 : Reach 83015 := rs (se 1 (by rfl) ⟨62261, by rfl⟩) R124523
theorem R148715 : Reach 148715 := rs (se 1 (by rfl) ⟨111536, by rfl⟩) R223073
theorem R83267 : Reach 83267 := rs (se 1 (by rfl) ⟨62450, by rfl⟩) R124901
theorem R50665 : Reach 50665 := rs (se 2 (by rfl) ⟨18999, by rfl⟩) R37999
theorem R18089 : Reach 18089 := rs (se 2 (by rfl) ⟨6783, by rfl⟩) R13567
theorem R18299 : Reach 18299 := rs (se 1 (by rfl) ⟨13724, by rfl⟩) R27449
theorem R1427543 : Reach 1427543 := rs (se 1 (by rfl) ⟨1070657, by rfl⟩) R2141315
theorem R51463 : Reach 51463 := rs (se 1 (by rfl) ⟨38597, by rfl⟩) R77195
theorem R18719 : Reach 18719 := rs (se 1 (by rfl) ⟨14039, by rfl⟩) R28079
theorem R3066173 : Reach 3066173 := rs (se 3 (by rfl) ⟨574907, by rfl⟩) R1149815
theorem R18887 : Reach 18887 := rs (se 1 (by rfl) ⟨14165, by rfl⟩) R28331
theorem R18919 : Reach 18919 := rs (se 1 (by rfl) ⟨14189, by rfl⟩) R28379
theorem R2017817 : Reach 2017817 := rs (se 2 (by rfl) ⟨756681, by rfl⟩) R1513363
theorem R19099 : Reach 19099 := rs (se 1 (by rfl) ⟨14324, by rfl⟩) R28649
theorem R19135 : Reach 19135 := rs (se 1 (by rfl) ⟨14351, by rfl⟩) R28703
theorem R51947 : Reach 51947 := rs (se 1 (by rfl) ⟨38960, by rfl⟩) R77921
theorem R19247 : Reach 19247 := rs (se 1 (by rfl) ⟨14435, by rfl⟩) R28871
theorem R19367 : Reach 19367 := rs (se 1 (by rfl) ⟨14525, by rfl⟩) R29051
theorem R19547 : Reach 19547 := rs (se 1 (by rfl) ⟨14660, by rfl⟩) R29321
theorem R19687 : Reach 19687 := rs (se 1 (by rfl) ⟨14765, by rfl⟩) R29531
theorem R19691 : Reach 19691 := rs (se 1 (by rfl) ⟨14768, by rfl⟩) R29537
theorem R19707 : Reach 19707 := rs (se 1 (by rfl) ⟨14780, by rfl⟩) R29561
theorem R52703 : Reach 52703 := rs (se 1 (by rfl) ⟨39527, by rfl⟩) R79055
theorem R20039 : Reach 20039 := rs (se 1 (by rfl) ⟨15029, by rfl⟩) R30059
theorem R52865 : Reach 52865 := rs (se 2 (by rfl) ⟨19824, by rfl⟩) R39649
theorem R52919 : Reach 52919 := rs (se 1 (by rfl) ⟨39689, by rfl⟩) R79379
theorem R20207 : Reach 20207 := rs (se 1 (by rfl) ⟨15155, by rfl⟩) R30311
theorem R20219 : Reach 20219 := rs (se 1 (by rfl) ⟨15164, by rfl⟩) R30329
theorem R20393 : Reach 20393 := rs (se 2 (by rfl) ⟨7647, by rfl⟩) R15295
theorem R479159 : Reach 479159 := rs (se 1 (by rfl) ⟨359369, by rfl⟩) R718739
theorem R85961 : Reach 85961 := rs (se 2 (by rfl) ⟨32235, by rfl⟩) R64471
theorem R20459 : Reach 20459 := rs (se 1 (by rfl) ⟨15344, by rfl⟩) R30689
theorem R20591 : Reach 20591 := rs (se 1 (by rfl) ⟨15443, by rfl⟩) R30887
theorem R20839 : Reach 20839 := rs (se 1 (by rfl) ⟨15629, by rfl⟩) R31259
theorem R119713 : Reach 119713 := rs (se 2 (by rfl) ⟨44892, by rfl⟩) R89785
theorem R21455 : Reach 21455 := rs (se 1 (by rfl) ⟨16091, by rfl⟩) R32183
theorem R21497 : Reach 21497 := rs (se 2 (by rfl) ⟨8061, by rfl⟩) R16123
theorem R250937 : Reach 250937 := rs (se 2 (by rfl) ⟨94101, by rfl⟩) R188203
theorem R21575 : Reach 21575 := rs (se 1 (by rfl) ⟨16181, by rfl⟩) R32363
theorem R21755 : Reach 21755 := rs (se 1 (by rfl) ⟨16316, by rfl⟩) R32633
theorem R21815 : Reach 21815 := rs (se 1 (by rfl) ⟨16361, by rfl⟩) R32723
theorem R54607 : Reach 54607 := rs (se 1 (by rfl) ⟨40955, by rfl⟩) R81911
theorem R54863 : Reach 54863 := rs (se 1 (by rfl) ⟨41147, by rfl⟩) R82295
theorem R22121 : Reach 22121 := rs (se 2 (by rfl) ⟨8295, by rfl⟩) R16591
theorem R22123 : Reach 22123 := rs (se 1 (by rfl) ⟨16592, by rfl⟩) R33185
theorem R22495 : Reach 22495 := rs (se 1 (by rfl) ⟨16871, by rfl⟩) R33743
theorem R88073 : Reach 88073 := rs (se 2 (by rfl) ⟨33027, by rfl⟩) R66055
theorem R22655 : Reach 22655 := rs (se 1 (by rfl) ⟨16991, by rfl⟩) R33983
theorem R88553 : Reach 88553 := rs (se 2 (by rfl) ⟨33207, by rfl⟩) R66415
theorem R23033 : Reach 23033 := rs (se 2 (by rfl) ⟨8637, by rfl⟩) R17275
theorem R23201 : Reach 23201 := rs (se 2 (by rfl) ⟨8700, by rfl⟩) R17401
theorem R23273 : Reach 23273 := rs (se 2 (by rfl) ⟨8727, by rfl⟩) R17455
theorem R23647 : Reach 23647 := rs (se 1 (by rfl) ⟨17735, by rfl⟩) R35471
theorem R23663 : Reach 23663 := rs (se 1 (by rfl) ⟨17747, by rfl⟩) R35495
theorem R23743 : Reach 23743 := rs (se 1 (by rfl) ⟨17807, by rfl⟩) R35615
theorem R89423 : Reach 89423 := rs (se 1 (by rfl) ⟨67067, by rfl⟩) R134135
theorem R24047 : Reach 24047 := rs (se 1 (by rfl) ⟨18035, by rfl⟩) R36071
theorem R24295 : Reach 24295 := rs (se 1 (by rfl) ⟨18221, by rfl⟩) R36443
theorem R57257 : Reach 57257 := rs (se 2 (by rfl) ⟨21471, by rfl⟩) R42943
theorem R24545 : Reach 24545 := rs (se 2 (by rfl) ⟨9204, by rfl⟩) R18409
theorem R24737 : Reach 24737 := rs (se 2 (by rfl) ⟨9276, by rfl⟩) R18553
theorem R90305 : Reach 90305 := rs (se 2 (by rfl) ⟨33864, by rfl⟩) R67729
theorem R24815 : Reach 24815 := rs (se 1 (by rfl) ⟨18611, by rfl⟩) R37223
theorem R24851 : Reach 24851 := rs (se 1 (by rfl) ⟨18638, by rfl⟩) R37277
theorem R25001 : Reach 25001 := rs (se 2 (by rfl) ⟨9375, by rfl⟩) R18751
theorem R25193 : Reach 25193 := rs (se 2 (by rfl) ⟨9447, by rfl⟩) R18895
theorem R25231 : Reach 25231 := rs (se 1 (by rfl) ⟨18923, by rfl⟩) R37847
theorem R25313 : Reach 25313 := rs (se 2 (by rfl) ⟨9492, by rfl⟩) R18985
theorem R58153 : Reach 58153 := rs (se 2 (by rfl) ⟨21807, by rfl⟩) R43615
theorem R189449 : Reach 189449 := rs (se 2 (by rfl) ⟨71043, by rfl⟩) R142087
theorem R25691 : Reach 25691 := rs (se 1 (by rfl) ⟨19268, by rfl⟩) R38537
theorem R58535 : Reach 58535 := rs (se 1 (by rfl) ⟨43901, by rfl⟩) R87803
theorem R124363 : Reach 124363 := rs (se 1 (by rfl) ⟨93272, by rfl⟩) R186545
theorem R91763 : Reach 91763 := rs (se 1 (by rfl) ⟨68822, by rfl⟩) R137645
theorem R26351 : Reach 26351 := rs (se 1 (by rfl) ⟨19763, by rfl⟩) R39527
theorem R26459 : Reach 26459 := rs (se 1 (by rfl) ⟨19844, by rfl⟩) R39689
theorem R26489 : Reach 26489 := rs (se 2 (by rfl) ⟨9933, by rfl⟩) R19867
theorem R92573 : Reach 92573 := rs (se 3 (by rfl) ⟨17357, by rfl⟩) R34715
theorem R27049 : Reach 27049 := rs (se 2 (by rfl) ⟨10143, by rfl⟩) R20287
theorem R747953 : Reach 747953 := rs (se 2 (by rfl) ⟨280482, by rfl⟩) R560965
theorem R27119 : Reach 27119 := rs (se 1 (by rfl) ⟨20339, by rfl⟩) R40679
theorem R27431 : Reach 27431 := rs (se 1 (by rfl) ⟨20573, by rfl⟩) R41147
theorem R27515 : Reach 27515 := rs (se 1 (by rfl) ⟨20636, by rfl⟩) R41273
theorem R27551 : Reach 27551 := rs (se 1 (by rfl) ⟨20663, by rfl⟩) R41327
theorem R453599 : Reach 453599 := rs (se 1 (by rfl) ⟨340199, by rfl⟩) R680399
theorem R60425 : Reach 60425 := rs (se 2 (by rfl) ⟨22659, by rfl⟩) R45319
theorem R93419 : Reach 93419 := rs (se 1 (by rfl) ⟨70064, by rfl⟩) R140129
theorem R159043 : Reach 159043 := rs (se 1 (by rfl) ⟨119282, by rfl⟩) R238565
theorem R290141 : Reach 290141 := rs (se 3 (by rfl) ⟨54401, by rfl⟩) R108803
theorem R28031 : Reach 28031 := rs (se 1 (by rfl) ⟨21023, by rfl⟩) R42047
theorem R585251 : Reach 585251 := rs (se 1 (by rfl) ⟨438938, by rfl⟩) R877877
theorem R1207943 : Reach 1207943 := rs (se 1 (by rfl) ⟨905957, by rfl⟩) R1811915
theorem R28667 : Reach 28667 := rs (se 1 (by rfl) ⟨21500, by rfl⟩) R43001
theorem R28907 : Reach 28907 := rs (se 1 (by rfl) ⟨21680, by rfl⟩) R43361
theorem R356723 : Reach 356723 := rs (se 1 (by rfl) ⟨267542, by rfl⟩) R535085
theorem R160379 : Reach 160379 := rs (se 1 (by rfl) ⟨120284, by rfl⟩) R240569
theorem R29609 : Reach 29609 := rs (se 2 (by rfl) ⟨11103, by rfl⟩) R22207
theorem R62423 : Reach 62423 := rs (se 1 (by rfl) ⟨46817, by rfl⟩) R93635
theorem R29675 : Reach 29675 := rs (se 1 (by rfl) ⟨22256, by rfl⟩) R44513
theorem R226799 : Reach 226799 := rs (se 1 (by rfl) ⟨170099, by rfl⟩) R340199
theorem R30287 : Reach 30287 := rs (se 1 (by rfl) ⟨22715, by rfl⟩) R45431
theorem R128897 : Reach 128897 := rs (se 2 (by rfl) ⟨48336, by rfl⟩) R96673
theorem R227447 : Reach 227447 := rs (se 1 (by rfl) ⟨170585, by rfl⟩) R341171
theorem R63827 : Reach 63827 := rs (se 1 (by rfl) ⟨47870, by rfl⟩) R95741
theorem R588185 : Reach 588185 := rs (se 2 (by rfl) ⟨220569, by rfl⟩) R441139
theorem R31211 : Reach 31211 := rs (se 1 (by rfl) ⟨23408, by rfl⟩) R46817
theorem R64097 : Reach 64097 := rs (se 2 (by rfl) ⟨24036, by rfl⟩) R48073
theorem R31727 : Reach 31727 := rs (se 1 (by rfl) ⟨23795, by rfl⟩) R47591
theorem R31913 : Reach 31913 := rs (se 2 (by rfl) ⟨11967, by rfl⟩) R23935
theorem R65087 : Reach 65087 := rs (se 1 (by rfl) ⟨48815, by rfl⟩) R97631
theorem R32543 : Reach 32543 := rs (se 1 (by rfl) ⟨24407, by rfl⟩) R48815
theorem R33007 : Reach 33007 := rs (se 1 (by rfl) ⟨24755, by rfl⟩) R49511
theorem R459209 : Reach 459209 := rs (se 2 (by rfl) ⟨172203, by rfl⟩) R344407
theorem R33335 : Reach 33335 := rs (se 1 (by rfl) ⟨25001, by rfl⟩) R50003
theorem R590489 : Reach 590489 := rs (se 2 (by rfl) ⟨221433, by rfl⟩) R442867
theorem R99143 : Reach 99143 := rs (se 1 (by rfl) ⟨74357, by rfl⟩) R148715
theorem R33641 : Reach 33641 := rs (se 2 (by rfl) ⟨12615, by rfl⟩) R25231
theorem R1180979 : Reach 1180979 := rs (se 1 (by rfl) ⟨885734, by rfl⟩) R1771469
theorem R951695 : Reach 951695 := rs (se 1 (by rfl) ⟨713771, by rfl⟩) R1427543
theorem R198287 : Reach 198287 := rs (se 1 (by rfl) ⟨148715, by rfl⟩) R297431
theorem R1345211 : Reach 1345211 := rs (se 1 (by rfl) ⟨1008908, by rfl⟩) R2017817
theorem R67283 : Reach 67283 := rs (se 1 (by rfl) ⟨50462, by rfl⟩) R100925
theorem R34631 : Reach 34631 := rs (se 1 (by rfl) ⟨25973, by rfl⟩) R51947
theorem R67499 : Reach 67499 := rs (se 1 (by rfl) ⟨50624, by rfl⟩) R101249
theorem R165817 : Reach 165817 := rs (se 2 (by rfl) ⟨62181, by rfl⟩) R124363
theorem R67553 : Reach 67553 := rs (se 2 (by rfl) ⟨25332, by rfl⟩) R50665
theorem R35135 : Reach 35135 := rs (se 1 (by rfl) ⟨26351, by rfl⟩) R52703
theorem R35243 : Reach 35243 := rs (se 1 (by rfl) ⟨26432, by rfl⟩) R52865
theorem R35279 : Reach 35279 := rs (se 1 (by rfl) ⟨26459, by rfl⟩) R52919
theorem R68617 : Reach 68617 := rs (se 2 (by rfl) ⟨25731, by rfl⟩) R51463
theorem R134297 : Reach 134297 := rs (se 2 (by rfl) ⟨50361, by rfl⟩) R100723
theorem R36065 : Reach 36065 := rs (se 2 (by rfl) ⟨13524, by rfl⟩) R27049
theorem R167291 : Reach 167291 := rs (se 1 (by rfl) ⟨125468, by rfl⟩) R250937
theorem R36575 : Reach 36575 := rs (se 1 (by rfl) ⟨27431, by rfl⟩) R54863
theorem R69407 : Reach 69407 := rs (se 1 (by rfl) ⟨52055, by rfl⟩) R104111
theorem R135107 : Reach 135107 := rs (se 1 (by rfl) ⟨101330, by rfl⟩) R202661
theorem R200839 : Reach 200839 := rs (se 1 (by rfl) ⟨150629, by rfl⟩) R301259
theorem R102653 : Reach 102653 := rs (se 3 (by rfl) ⟨19247, by rfl⟩) R38495
theorem R38171 : Reach 38171 := rs (se 1 (by rfl) ⟨28628, by rfl⟩) R57257
theorem R268105 : Reach 268105 := rs (se 2 (by rfl) ⟨100539, by rfl⟩) R201079
theorem R39023 : Reach 39023 := rs (se 1 (by rfl) ⟨29267, by rfl⟩) R58535
theorem R71867 : Reach 71867 := rs (se 1 (by rfl) ⟨53900, by rfl⟩) R107801
theorem R236141 : Reach 236141 := rs (se 3 (by rfl) ⟨44276, by rfl⟩) R88553
theorem R498635 : Reach 498635 := rs (se 1 (by rfl) ⟨373976, by rfl⟩) R747953
theorem R72809 : Reach 72809 := rs (se 2 (by rfl) ⟨27303, by rfl⟩) R54607
theorem R826685 : Reach 826685 := rs (se 3 (by rfl) ⟨155003, by rfl⟩) R310007
theorem R302399 : Reach 302399 := rs (se 1 (by rfl) ⟨226799, by rfl⟩) R453599
theorem R40283 : Reach 40283 := rs (se 1 (by rfl) ⟨30212, by rfl⟩) R60425
theorem R205031 : Reach 205031 := rs (se 1 (by rfl) ⟨153773, by rfl⟩) R307547
theorem R237815 : Reach 237815 := rs (se 1 (by rfl) ⟨178361, by rfl⟩) R356723
theorem R106919 : Reach 106919 := rs (se 1 (by rfl) ⟨80189, by rfl⟩) R160379
theorem R107129 : Reach 107129 := rs (se 2 (by rfl) ⟨40173, by rfl⟩) R80347
theorem R41597 : Reach 41597 := rs (se 3 (by rfl) ⟨7799, by rfl⟩) R15599
theorem R41615 : Reach 41615 := rs (se 1 (by rfl) ⟨31211, by rfl⟩) R62423
theorem R41789 : Reach 41789 := rs (se 3 (by rfl) ⟨7835, by rfl⟩) R15671
theorem R107345 : Reach 107345 := rs (se 2 (by rfl) ⟨40254, by rfl⟩) R80509
theorem R140447 : Reach 140447 := rs (se 1 (by rfl) ⟨105335, by rfl⟩) R210671
theorem R107837 : Reach 107837 := rs (se 3 (by rfl) ⟨20219, by rfl⟩) R40439
theorem R42551 : Reach 42551 := rs (se 1 (by rfl) ⟨31913, by rfl⟩) R63827
theorem R42731 : Reach 42731 := rs (se 1 (by rfl) ⟨32048, by rfl⟩) R64097
theorem R206671 : Reach 206671 := rs (se 1 (by rfl) ⟨155003, by rfl⟩) R310007
theorem R75755 : Reach 75755 := rs (se 1 (by rfl) ⟨56816, by rfl⟩) R113633
theorem R75815 : Reach 75815 := rs (se 1 (by rfl) ⟨56861, by rfl⟩) R113723
theorem R43391 : Reach 43391 := rs (se 1 (by rfl) ⟨32543, by rfl⟩) R65087
theorem R141851 : Reach 141851 := rs (se 1 (by rfl) ⟨106388, by rfl⟩) R212777
theorem R43847 : Reach 43847 := rs (se 1 (by rfl) ⟨32885, by rfl⟩) R65771
theorem R208007 : Reach 208007 := rs (se 1 (by rfl) ⟨156005, by rfl⟩) R312011
theorem R44219 : Reach 44219 := rs (se 1 (by rfl) ⟨33164, by rfl⟩) R66329
theorem R77537 : Reach 77537 := rs (se 2 (by rfl) ⟨29076, by rfl⟩) R58153
theorem R2044115 : Reach 2044115 := rs (se 1 (by rfl) ⟨1533086, by rfl⟩) R3066173
theorem R45289 : Reach 45289 := rs (se 2 (by rfl) ⟨16983, by rfl⟩) R33967
theorem R45481 : Reach 45481 := rs (se 2 (by rfl) ⟨17055, by rfl⟩) R34111
theorem R12831 : Reach 12831 := rs (se 1 (by rfl) ⟨9623, by rfl⟩) R19247
theorem R12911 : Reach 12911 := rs (se 1 (by rfl) ⟨9683, by rfl⟩) R19367
theorem R13031 : Reach 13031 := rs (se 1 (by rfl) ⟨9773, by rfl⟩) R19547
theorem R13127 : Reach 13127 := rs (se 1 (by rfl) ⟨9845, by rfl⟩) R19691
theorem R46015 : Reach 46015 := rs (se 1 (by rfl) ⟨34511, by rfl⟩) R69023
theorem R13359 : Reach 13359 := rs (se 1 (by rfl) ⟨10019, by rfl⟩) R20039
theorem R13471 : Reach 13471 := rs (se 1 (by rfl) ⟨10103, by rfl⟩) R20207
theorem R13479 : Reach 13479 := rs (se 1 (by rfl) ⟨10109, by rfl⟩) R20219
theorem R13595 : Reach 13595 := rs (se 1 (by rfl) ⟨10196, by rfl⟩) R20393
theorem R13639 : Reach 13639 := rs (se 1 (by rfl) ⟨10229, by rfl⟩) R20459
theorem R13727 : Reach 13727 := rs (se 1 (by rfl) ⟨10295, by rfl⟩) R20591
theorem R46747 : Reach 46747 := rs (se 1 (by rfl) ⟨35060, by rfl⟩) R70121
theorem R46919 : Reach 46919 := rs (se 1 (by rfl) ⟨35189, by rfl⟩) R70379
theorem R3389303 : Reach 3389303 := rs (se 1 (by rfl) ⟨2541977, by rfl⟩) R5083955
theorem R14303 : Reach 14303 := rs (se 1 (by rfl) ⟨10727, by rfl⟩) R21455
theorem R14331 : Reach 14331 := rs (se 1 (by rfl) ⟨10748, by rfl⟩) R21497
theorem R14383 : Reach 14383 := rs (se 1 (by rfl) ⟨10787, by rfl⟩) R21575
theorem R14503 : Reach 14503 := rs (se 1 (by rfl) ⟨10877, by rfl⟩) R21755
theorem R14543 : Reach 14543 := rs (se 1 (by rfl) ⟨10907, by rfl⟩) R21815
theorem R14747 : Reach 14747 := rs (se 1 (by rfl) ⟨11060, by rfl⟩) R22121
theorem R15103 : Reach 15103 := rs (se 1 (by rfl) ⟨11327, by rfl⟩) R22655
theorem R15355 : Reach 15355 := rs (se 1 (by rfl) ⟨11516, by rfl⟩) R23033
theorem R212057 : Reach 212057 := rs (se 2 (by rfl) ⟨79521, by rfl⟩) R159043
theorem R15467 : Reach 15467 := rs (se 1 (by rfl) ⟨11600, by rfl⟩) R23201
theorem R15515 : Reach 15515 := rs (se 1 (by rfl) ⟨11636, by rfl⟩) R23273
theorem R15775 : Reach 15775 := rs (se 1 (by rfl) ⟨11831, by rfl⟩) R23663
theorem R16031 : Reach 16031 := rs (se 1 (by rfl) ⟨12023, by rfl⟩) R24047
theorem R147257 : Reach 147257 := rs (se 2 (by rfl) ⟨55221, by rfl⟩) R110443
theorem R16363 : Reach 16363 := rs (se 1 (by rfl) ⟨12272, by rfl⟩) R24545
theorem R16491 : Reach 16491 := rs (se 1 (by rfl) ⟨12368, by rfl⟩) R24737
theorem R16543 : Reach 16543 := rs (se 1 (by rfl) ⟨12407, by rfl⟩) R24815
theorem R16567 : Reach 16567 := rs (se 1 (by rfl) ⟨12425, by rfl⟩) R24851
theorem R16667 : Reach 16667 := rs (se 1 (by rfl) ⟨12500, by rfl⟩) R25001
theorem R49463 : Reach 49463 := rs (se 1 (by rfl) ⟨37097, by rfl⟩) R74195
theorem R246071 : Reach 246071 := rs (se 1 (by rfl) ⟨184553, by rfl⟩) R369107
theorem R16795 : Reach 16795 := rs (se 1 (by rfl) ⟨12596, by rfl⟩) R25193
theorem R16875 : Reach 16875 := rs (se 1 (by rfl) ⟨12656, by rfl⟩) R25313
theorem R17127 : Reach 17127 := rs (se 1 (by rfl) ⟨12845, by rfl⟩) R25691
theorem R17567 : Reach 17567 := rs (se 1 (by rfl) ⟨13175, by rfl⟩) R26351
theorem R17639 : Reach 17639 := rs (se 1 (by rfl) ⟨13229, by rfl⟩) R26459
theorem R17659 : Reach 17659 := rs (se 1 (by rfl) ⟨13244, by rfl⟩) R26489
theorem R17705 : Reach 17705 := rs (se 2 (by rfl) ⟨6639, by rfl⟩) R13279
theorem R17785 : Reach 17785 := rs (se 2 (by rfl) ⟨6669, by rfl⟩) R13339
theorem R83429 : Reach 83429 := rs (se 4 (by rfl) ⟨7821, by rfl⟩) R15643
theorem R50743 : Reach 50743 := rs (se 1 (by rfl) ⟨38057, by rfl⟩) R76115
theorem R18079 : Reach 18079 := rs (se 1 (by rfl) ⟨13559, by rfl⟩) R27119
theorem R149201 : Reach 149201 := rs (se 2 (by rfl) ⟨55950, by rfl⟩) R111901
theorem R18153 : Reach 18153 := rs (se 2 (by rfl) ⟨6807, by rfl⟩) R13615
theorem R18287 : Reach 18287 := rs (se 1 (by rfl) ⟨13715, by rfl⟩) R27431
theorem R18343 : Reach 18343 := rs (se 1 (by rfl) ⟨13757, by rfl⟩) R27515
theorem R18367 : Reach 18367 := rs (se 1 (by rfl) ⟨13775, by rfl⟩) R27551
theorem R18473 : Reach 18473 := rs (se 2 (by rfl) ⟨6927, by rfl⟩) R13855
theorem R18569 : Reach 18569 := rs (se 2 (by rfl) ⟨6963, by rfl⟩) R13927
theorem R18601 : Reach 18601 := rs (se 2 (by rfl) ⟨6975, by rfl⟩) R13951
theorem R18687 : Reach 18687 := rs (se 1 (by rfl) ⟨14015, by rfl⟩) R28031
theorem R51553 : Reach 51553 := rs (se 2 (by rfl) ⟨19332, by rfl⟩) R38665
theorem R805295 : Reach 805295 := rs (se 1 (by rfl) ⟨603971, by rfl⟩) R1207943
theorem R19111 : Reach 19111 := rs (se 1 (by rfl) ⟨14333, by rfl⟩) R28667
theorem R19271 : Reach 19271 := rs (se 1 (by rfl) ⟨14453, by rfl⟩) R28907
theorem R19739 : Reach 19739 := rs (se 1 (by rfl) ⟨14804, by rfl⟩) R29609
theorem R19783 : Reach 19783 := rs (se 1 (by rfl) ⟨14837, by rfl⟩) R29675
theorem R151199 : Reach 151199 := rs (se 1 (by rfl) ⟨113399, by rfl⟩) R226799
theorem R20191 : Reach 20191 := rs (se 1 (by rfl) ⟨15143, by rfl⟩) R30287
theorem R85931 : Reach 85931 := rs (se 1 (by rfl) ⟨64448, by rfl⟩) R128897
theorem R151631 : Reach 151631 := rs (se 1 (by rfl) ⟨113723, by rfl⟩) R227447
theorem R20807 : Reach 20807 := rs (se 1 (by rfl) ⟨15605, by rfl⟩) R31211
theorem R20857 : Reach 20857 := rs (se 2 (by rfl) ⟨7821, by rfl⟩) R15643
theorem R53885 : Reach 53885 := rs (se 3 (by rfl) ⟨10103, by rfl⟩) R20207
theorem R21151 : Reach 21151 := rs (se 1 (by rfl) ⟨15863, by rfl⟩) R31727
theorem R21275 : Reach 21275 := rs (se 1 (by rfl) ⟨15956, by rfl⟩) R31913
theorem R21695 : Reach 21695 := rs (se 1 (by rfl) ⟨16271, by rfl⟩) R32543
theorem R54553 : Reach 54553 := rs (se 2 (by rfl) ⟨20457, by rfl⟩) R40915
theorem R21881 : Reach 21881 := rs (se 2 (by rfl) ⟨8205, by rfl⟩) R16411
theorem R251423 : Reach 251423 := rs (se 1 (by rfl) ⟨188567, by rfl⟩) R377135
theorem R22441 : Reach 22441 := rs (se 2 (by rfl) ⟨8415, by rfl⟩) R16831
theorem R55343 : Reach 55343 := rs (se 1 (by rfl) ⟨41507, by rfl⟩) R83015
theorem R55511 : Reach 55511 := rs (se 1 (by rfl) ⟨41633, by rfl⟩) R83267
theorem R22751 : Reach 22751 := rs (se 1 (by rfl) ⟨17063, by rfl⟩) R34127
theorem R22847 : Reach 22847 := rs (se 1 (by rfl) ⟨17135, by rfl⟩) R34271
theorem R481619 : Reach 481619 := rs (se 1 (by rfl) ⟨361214, by rfl⟩) R722429
theorem R22955 : Reach 22955 := rs (se 1 (by rfl) ⟨17216, by rfl⟩) R34433
theorem R23123 : Reach 23123 := rs (se 1 (by rfl) ⟨17342, by rfl⟩) R34685
theorem R23231 : Reach 23231 := rs (se 1 (by rfl) ⟨17423, by rfl⟩) R34847
theorem R56105 : Reach 56105 := rs (se 2 (by rfl) ⟨21039, by rfl⟩) R42079
theorem R23711 : Reach 23711 := rs (se 1 (by rfl) ⟨17783, by rfl⟩) R35567
theorem R24119 : Reach 24119 := rs (se 1 (by rfl) ⟨18089, by rfl⟩) R36179
theorem R56969 : Reach 56969 := rs (se 2 (by rfl) ⟨21363, by rfl⟩) R42727
theorem R24239 : Reach 24239 := rs (se 1 (by rfl) ⟨18179, by rfl⟩) R36359
theorem R319439 : Reach 319439 := rs (se 1 (by rfl) ⟨239579, by rfl⟩) R479159
theorem R57307 : Reach 57307 := rs (se 1 (by rfl) ⟨42980, by rfl⟩) R85961
theorem R24731 : Reach 24731 := rs (se 1 (by rfl) ⟨18548, by rfl⟩) R37097
theorem R24959 : Reach 24959 := rs (se 1 (by rfl) ⟨18719, by rfl⟩) R37439
theorem R25199 : Reach 25199 := rs (se 1 (by rfl) ⟨18899, by rfl⟩) R37799
theorem R25415 : Reach 25415 := rs (se 1 (by rfl) ⟨19061, by rfl⟩) R38123
theorem R25663 : Reach 25663 := rs (se 1 (by rfl) ⟨19247, by rfl⟩) R38495
theorem R25823 : Reach 25823 := rs (se 1 (by rfl) ⟨19367, by rfl⟩) R38735
theorem R91367 : Reach 91367 := rs (se 1 (by rfl) ⟨68525, by rfl⟩) R137051
theorem R58715 : Reach 58715 := rs (se 1 (by rfl) ⟨44036, by rfl⟩) R88073
theorem R26063 : Reach 26063 := rs (se 1 (by rfl) ⟨19547, by rfl⟩) R39095
theorem R26249 : Reach 26249 := rs (se 2 (by rfl) ⟨9843, by rfl⟩) R19687
theorem R26255 : Reach 26255 := rs (se 1 (by rfl) ⟨19691, by rfl⟩) R39383
theorem R26267 : Reach 26267 := rs (se 1 (by rfl) ⟨19700, by rfl⟩) R39401
theorem R26303 : Reach 26303 := rs (se 1 (by rfl) ⟨19727, by rfl⟩) R39455
theorem R59615 : Reach 59615 := rs (se 1 (by rfl) ⟨44711, by rfl⟩) R89423
theorem R26959 : Reach 26959 := rs (se 1 (by rfl) ⟨20219, by rfl⟩) R40439
theorem R27191 : Reach 27191 := rs (se 1 (by rfl) ⟨20393, by rfl⟩) R40787
theorem R60041 : Reach 60041 := rs (se 2 (by rfl) ⟨22515, by rfl⟩) R45031
theorem R60203 : Reach 60203 := rs (se 1 (by rfl) ⟨45152, by rfl⟩) R90305
theorem R289595 : Reach 289595 := rs (se 1 (by rfl) ⟨217196, by rfl⟩) R434393
theorem R27455 : Reach 27455 := rs (se 1 (by rfl) ⟨20591, by rfl⟩) R41183
theorem R27755 : Reach 27755 := rs (se 1 (by rfl) ⟨20816, by rfl⟩) R41633
theorem R27785 : Reach 27785 := rs (se 2 (by rfl) ⟨10419, by rfl⟩) R20839
theorem R650429 : Reach 650429 := rs (se 3 (by rfl) ⟨121955, by rfl⟩) R243911
theorem R27839 : Reach 27839 := rs (se 1 (by rfl) ⟨20879, by rfl⟩) R41759
theorem R126299 : Reach 126299 := rs (se 1 (by rfl) ⟨94724, by rfl⟩) R189449
theorem R27995 : Reach 27995 := rs (se 1 (by rfl) ⟨20996, by rfl⟩) R41993
theorem R28319 : Reach 28319 := rs (se 1 (by rfl) ⟨21239, by rfl⟩) R42479
theorem R61175 : Reach 61175 := rs (se 1 (by rfl) ⟨45881, by rfl⟩) R91763
theorem R159617 : Reach 159617 := rs (se 2 (by rfl) ⟨59856, by rfl⟩) R119713
theorem R28847 : Reach 28847 := rs (se 1 (by rfl) ⟨21635, by rfl⟩) R43271
theorem R61715 : Reach 61715 := rs (se 1 (by rfl) ⟨46286, by rfl⟩) R92573
theorem R28955 : Reach 28955 := rs (se 1 (by rfl) ⟨21716, by rfl⟩) R43433
theorem R29099 : Reach 29099 := rs (se 1 (by rfl) ⟨21824, by rfl⟩) R43649
theorem R29371 : Reach 29371 := rs (se 1 (by rfl) ⟨22028, by rfl⟩) R44057
theorem R29495 : Reach 29495 := rs (se 1 (by rfl) ⟨22121, by rfl⟩) R44243
theorem R29497 : Reach 29497 := rs (se 2 (by rfl) ⟨11061, by rfl⟩) R22123
theorem R62279 : Reach 62279 := rs (se 1 (by rfl) ⟨46709, by rfl⟩) R93419
theorem R193427 : Reach 193427 := rs (se 1 (by rfl) ⟨145070, by rfl⟩) R290141
theorem R390167 : Reach 390167 := rs (se 1 (by rfl) ⟨292625, by rfl⟩) R585251
theorem R29807 : Reach 29807 := rs (se 1 (by rfl) ⟨22355, by rfl⟩) R44711
theorem R29993 : Reach 29993 := rs (se 2 (by rfl) ⟨11247, by rfl⟩) R22495
theorem R63305 : Reach 63305 := rs (se 2 (by rfl) ⟨23739, by rfl⟩) R47479
theorem R30827 : Reach 30827 := rs (se 1 (by rfl) ⟨23120, by rfl⟩) R46241
theorem R30935 : Reach 30935 := rs (se 1 (by rfl) ⟨23201, by rfl⟩) R46403
theorem R31031 : Reach 31031 := rs (se 1 (by rfl) ⟨23273, by rfl⟩) R46547
theorem R96713 : Reach 96713 := rs (se 2 (by rfl) ⟨36267, by rfl⟩) R72535
theorem R457325 : Reach 457325 := rs (se 3 (by rfl) ⟨85748, by rfl⟩) R171497
theorem R359075 : Reach 359075 := rs (se 1 (by rfl) ⟨269306, by rfl⟩) R538613
theorem R31529 : Reach 31529 := rs (se 2 (by rfl) ⟨11823, by rfl⟩) R23647
theorem R31657 : Reach 31657 := rs (se 2 (by rfl) ⟨11871, by rfl⟩) R23743
theorem R392123 : Reach 392123 := rs (se 1 (by rfl) ⟨294092, by rfl⟩) R588185
theorem R64745 : Reach 64745 := rs (se 2 (by rfl) ⟨24279, by rfl⟩) R48559
theorem R32071 : Reach 32071 := rs (se 1 (by rfl) ⟨24053, by rfl⟩) R48107
theorem R32393 : Reach 32393 := rs (se 2 (by rfl) ⟨12147, by rfl⟩) R24295
theorem R32975 : Reach 32975 := rs (se 1 (by rfl) ⟨24731, by rfl⟩) R49463
theorem R164047 : Reach 164047 := rs (se 1 (by rfl) ⟨123035, by rfl⟩) R246071
theorem R393659 : Reach 393659 := rs (se 1 (by rfl) ⟨295244, by rfl⟩) R590489
theorem R66095 : Reach 66095 := rs (se 1 (by rfl) ⟨49571, by rfl⟩) R99143
theorem R787319 : Reach 787319 := rs (se 1 (by rfl) ⟨590489, by rfl⟩) R1180979
theorem R132191 : Reach 132191 := rs (se 1 (by rfl) ⟨99143, by rfl⟩) R198287
theorem R99467 : Reach 99467 := rs (se 1 (by rfl) ⟨74600, by rfl⟩) R149201
theorem R34217 : Reach 34217 := rs (se 2 (by rfl) ⟨12831, by rfl⟩) R25663
theorem R67657 : Reach 67657 := rs (se 2 (by rfl) ⟨25371, by rfl⟩) R50743
theorem R100799 : Reach 100799 := rs (se 1 (by rfl) ⟨75599, by rfl⟩) R151199
theorem R101087 : Reach 101087 := rs (se 1 (by rfl) ⟨75815, by rfl⟩) R151631
theorem R68435 : Reach 68435 := rs (se 1 (by rfl) ⟨51326, by rfl⟩) R102653
theorem R35923 : Reach 35923 := rs (se 1 (by rfl) ⟨26942, by rfl⟩) R53885
theorem R35945 : Reach 35945 := rs (se 2 (by rfl) ⟨13479, by rfl⟩) R26959
theorem R68737 : Reach 68737 := rs (se 2 (by rfl) ⟨25776, by rfl⟩) R51553
theorem R167615 : Reach 167615 := rs (se 1 (by rfl) ⟨125711, by rfl⟩) R251423
theorem R36895 : Reach 36895 := rs (se 1 (by rfl) ⟨27671, by rfl⟩) R55343
theorem R37007 : Reach 37007 := rs (se 1 (by rfl) ⟨27755, by rfl⟩) R55511
theorem R37403 : Reach 37403 := rs (se 1 (by rfl) ⟨28052, by rfl⟩) R56105
theorem R332423 : Reach 332423 := rs (se 1 (by rfl) ⟨249317, by rfl⟩) R498635
theorem R201599 : Reach 201599 := rs (se 1 (by rfl) ⟨151199, by rfl⟩) R302399
theorem R37979 : Reach 37979 := rs (se 1 (by rfl) ⟨28484, by rfl⟩) R56969
theorem R38141 : Reach 38141 := rs (se 3 (by rfl) ⟨7151, by rfl⟩) R14303
theorem R136687 : Reach 136687 := rs (se 1 (by rfl) ⟨102515, by rfl⟩) R205031
theorem R267785 : Reach 267785 := rs (se 2 (by rfl) ⟨100419, by rfl⟩) R200839
theorem R71279 : Reach 71279 := rs (se 1 (by rfl) ⟨53459, by rfl⟩) R106919
theorem R71563 : Reach 71563 := rs (se 1 (by rfl) ⟨53672, by rfl⟩) R107345
theorem R71891 : Reach 71891 := rs (se 1 (by rfl) ⟨53918, by rfl⟩) R107837
theorem R39143 : Reach 39143 := rs (se 1 (by rfl) ⟨29357, by rfl⟩) R58715
theorem R39161 : Reach 39161 := rs (se 2 (by rfl) ⟨14685, by rfl⟩) R29371
theorem R39325 : Reach 39325 := rs (se 3 (by rfl) ⟨7373, by rfl⟩) R14747
theorem R39329 : Reach 39329 := rs (se 2 (by rfl) ⟨14748, by rfl⟩) R29497
theorem R39743 : Reach 39743 := rs (se 1 (by rfl) ⟨29807, by rfl⟩) R59615
theorem R72737 : Reach 72737 := rs (se 2 (by rfl) ⟨27276, by rfl⟩) R54553
theorem R40027 : Reach 40027 := rs (se 1 (by rfl) ⟨30020, by rfl⟩) R60041
theorem R40135 : Reach 40135 := rs (se 1 (by rfl) ⟨30101, by rfl⟩) R60203
theorem R138671 : Reach 138671 := rs (se 1 (by rfl) ⟨104003, by rfl⟩) R208007
theorem R433619 : Reach 433619 := rs (se 1 (by rfl) ⟨325214, by rfl⟩) R650429
theorem R40783 : Reach 40783 := rs (se 1 (by rfl) ⟨30587, by rfl⟩) R61175
theorem R41143 : Reach 41143 := rs (se 1 (by rfl) ⟨30857, by rfl⟩) R61715
theorem R41519 : Reach 41519 := rs (se 1 (by rfl) ⟨31139, by rfl⟩) R62279
theorem R336797 : Reach 336797 := rs (se 3 (by rfl) ⟨63149, by rfl⟩) R126299
theorem R42203 : Reach 42203 := rs (se 1 (by rfl) ⟨31652, by rfl⟩) R63305
theorem R42209 : Reach 42209 := rs (se 2 (by rfl) ⟨15828, by rfl⟩) R31657
theorem R304883 : Reach 304883 := rs (se 1 (by rfl) ⟨228662, by rfl⟩) R457325
theorem R42749 : Reach 42749 := rs (se 3 (by rfl) ⟨8015, by rfl⟩) R16031
theorem R42761 : Reach 42761 := rs (se 2 (by rfl) ⟨16035, by rfl⟩) R32071
theorem R239383 : Reach 239383 := rs (se 1 (by rfl) ⟨179537, by rfl⟩) R359075
theorem R141371 : Reach 141371 := rs (se 1 (by rfl) ⟨106028, by rfl⟩) R212057
theorem R43163 : Reach 43163 := rs (se 1 (by rfl) ⟨32372, by rfl⟩) R64745
theorem R76409 : Reach 76409 := rs (se 2 (by rfl) ⟨28653, by rfl⟩) R57307
theorem R306139 : Reach 306139 := rs (se 1 (by rfl) ⟨229604, by rfl⟩) R459209
theorem R44009 : Reach 44009 := rs (se 2 (by rfl) ⟨16503, by rfl⟩) R33007
theorem R77213 : Reach 77213 := rs (se 3 (by rfl) ⟨14477, by rfl⟩) R28955
theorem R634463 : Reach 634463 := rs (se 1 (by rfl) ⟨475847, by rfl⟩) R951695
theorem R77597 : Reach 77597 := rs (se 3 (by rfl) ⟨14549, by rfl⟩) R29099
theorem R896807 : Reach 896807 := rs (se 1 (by rfl) ⟨672605, by rfl⟩) R1345211
theorem R44855 : Reach 44855 := rs (se 1 (by rfl) ⟨33641, by rfl⟩) R67283
theorem R44999 : Reach 44999 := rs (se 1 (by rfl) ⟨33749, by rfl⟩) R67499
theorem R45035 : Reach 45035 := rs (se 1 (by rfl) ⟨33776, by rfl⟩) R67553
theorem R536863 : Reach 536863 := rs (se 1 (by rfl) ⟨402647, by rfl⟩) R805295
theorem R12847 : Reach 12847 := rs (se 1 (by rfl) ⟨9635, by rfl⟩) R19271
theorem R13159 : Reach 13159 := rs (se 1 (by rfl) ⟨9869, by rfl⟩) R19739
theorem R111527 : Reach 111527 := rs (se 1 (by rfl) ⟨83645, by rfl⟩) R167291
theorem R275561 : Reach 275561 := rs (se 2 (by rfl) ⟨103335, by rfl⟩) R206671
theorem R46271 : Reach 46271 := rs (se 1 (by rfl) ⟨34703, by rfl⟩) R69407
theorem R13871 : Reach 13871 := rs (se 1 (by rfl) ⟨10403, by rfl⟩) R20807
theorem R14183 : Reach 14183 := rs (se 1 (by rfl) ⟨10637, by rfl⟩) R21275
theorem R47213 : Reach 47213 := rs (se 3 (by rfl) ⟨8852, by rfl⟩) R17705
theorem R14463 : Reach 14463 := rs (se 1 (by rfl) ⟨10847, by rfl⟩) R21695
theorem R14587 : Reach 14587 := rs (se 1 (by rfl) ⟨10940, by rfl⟩) R21881
theorem R47911 : Reach 47911 := rs (se 1 (by rfl) ⟨35933, by rfl⟩) R71867
theorem R15167 : Reach 15167 := rs (se 1 (by rfl) ⟨11375, by rfl⟩) R22751
theorem R15231 : Reach 15231 := rs (se 1 (by rfl) ⟨11423, by rfl⟩) R22847
theorem R15303 : Reach 15303 := rs (se 1 (by rfl) ⟨11477, by rfl⟩) R22955
theorem R15415 : Reach 15415 := rs (se 1 (by rfl) ⟨11561, by rfl⟩) R23123
theorem R15487 : Reach 15487 := rs (se 1 (by rfl) ⟨11615, by rfl⟩) R23231
theorem R48539 : Reach 48539 := rs (se 1 (by rfl) ⟨36404, by rfl⟩) R72809
theorem R15807 : Reach 15807 := rs (se 1 (by rfl) ⟨11855, by rfl⟩) R23711
theorem R245413 : Reach 245413 := rs (se 4 (by rfl) ⟨23007, by rfl⟩) R46015
theorem R16079 : Reach 16079 := rs (se 1 (by rfl) ⟨12059, by rfl⟩) R24119
theorem R16159 : Reach 16159 := rs (se 1 (by rfl) ⟨12119, by rfl⟩) R24239
theorem R212959 : Reach 212959 := rs (se 1 (by rfl) ⟨159719, by rfl⟩) R319439
theorem R16487 : Reach 16487 := rs (se 1 (by rfl) ⟨12365, by rfl⟩) R24731
theorem R16639 : Reach 16639 := rs (se 1 (by rfl) ⟨12479, by rfl⟩) R24959
theorem R49517 : Reach 49517 := rs (se 3 (by rfl) ⟨9284, by rfl⟩) R18569
theorem R16799 : Reach 16799 := rs (se 1 (by rfl) ⟨12599, by rfl⟩) R25199
theorem R16943 : Reach 16943 := rs (se 1 (by rfl) ⟨12707, by rfl⟩) R25415
theorem R17215 : Reach 17215 := rs (se 1 (by rfl) ⟨12911, by rfl⟩) R25823
theorem R17375 : Reach 17375 := rs (se 1 (by rfl) ⟨13031, by rfl⟩) R26063
theorem R17499 : Reach 17499 := rs (se 1 (by rfl) ⟨13124, by rfl⟩) R26249
theorem R17503 : Reach 17503 := rs (se 1 (by rfl) ⟨13127, by rfl⟩) R26255
theorem R17511 : Reach 17511 := rs (se 1 (by rfl) ⟨13133, by rfl⟩) R26267
theorem R17535 : Reach 17535 := rs (se 1 (by rfl) ⟨13151, by rfl⟩) R26303
theorem R50503 : Reach 50503 := rs (se 1 (by rfl) ⟨37877, by rfl⟩) R75755
theorem R50543 : Reach 50543 := rs (se 1 (by rfl) ⟨37907, by rfl⟩) R75815
theorem R378269 : Reach 378269 := rs (se 3 (by rfl) ⟨70925, by rfl⟩) R141851
theorem R17961 : Reach 17961 := rs (se 2 (by rfl) ⟨6735, by rfl⟩) R13471
theorem R18127 : Reach 18127 := rs (se 1 (by rfl) ⟨13595, by rfl⟩) R27191
theorem R18185 : Reach 18185 := rs (se 2 (by rfl) ⟨6819, by rfl⟩) R13639
theorem R18303 : Reach 18303 := rs (se 1 (by rfl) ⟨13727, by rfl⟩) R27455
theorem R18503 : Reach 18503 := rs (se 1 (by rfl) ⟨13877, by rfl⟩) R27755
theorem R18523 : Reach 18523 := rs (se 1 (by rfl) ⟨13892, by rfl⟩) R27785
theorem R84077 : Reach 84077 := rs (se 3 (by rfl) ⟨15764, by rfl⟩) R31529
theorem R18559 : Reach 18559 := rs (se 1 (by rfl) ⟨13919, by rfl⟩) R27839
theorem R772253 : Reach 772253 := rs (se 3 (by rfl) ⟨144797, by rfl⟩) R289595
theorem R84199 : Reach 84199 := rs (se 1 (by rfl) ⟨63149, by rfl⟩) R126299
theorem R18663 : Reach 18663 := rs (se 1 (by rfl) ⟨13997, by rfl⟩) R27995
theorem R18879 : Reach 18879 := rs (se 1 (by rfl) ⟨14159, by rfl⟩) R28319
theorem R51691 : Reach 51691 := rs (se 1 (by rfl) ⟨38768, by rfl⟩) R77537
theorem R19177 : Reach 19177 := rs (se 2 (by rfl) ⟨7191, by rfl⟩) R14383
theorem R19231 : Reach 19231 := rs (se 1 (by rfl) ⟨14423, by rfl⟩) R28847
theorem R1362743 : Reach 1362743 := rs (se 1 (by rfl) ⟨1022057, by rfl⟩) R2044115
theorem R19303 : Reach 19303 := rs (se 1 (by rfl) ⟨14477, by rfl⟩) R28955
theorem R19337 : Reach 19337 := rs (se 2 (by rfl) ⟨7251, by rfl⟩) R14503
theorem R19399 : Reach 19399 := rs (se 1 (by rfl) ⟨14549, by rfl⟩) R29099
theorem R19663 : Reach 19663 := rs (se 1 (by rfl) ⟨14747, by rfl⟩) R29495
theorem R19871 : Reach 19871 := rs (se 1 (by rfl) ⟨14903, by rfl⟩) R29807
theorem R249317 : Reach 249317 := rs (se 4 (by rfl) ⟨23373, by rfl⟩) R46747
theorem R19995 : Reach 19995 := rs (se 1 (by rfl) ⟨14996, by rfl⟩) R29993
theorem R20137 : Reach 20137 := rs (se 2 (by rfl) ⟨7551, by rfl⟩) R15103
theorem R20551 : Reach 20551 := rs (se 1 (by rfl) ⟨15413, by rfl⟩) R30827
theorem R20623 : Reach 20623 := rs (se 1 (by rfl) ⟨15467, by rfl⟩) R30935
theorem R20687 : Reach 20687 := rs (se 1 (by rfl) ⟨15515, by rfl⟩) R31031
theorem R21019 : Reach 21019 := rs (se 1 (by rfl) ⟨15764, by rfl⟩) R31529
theorem R21595 : Reach 21595 := rs (se 1 (by rfl) ⟨16196, by rfl⟩) R32393
theorem R21817 : Reach 21817 := rs (se 2 (by rfl) ⟨8181, by rfl⟩) R16363
theorem R22223 : Reach 22223 := rs (se 1 (by rfl) ⟨16667, by rfl⟩) R33335
theorem R22427 : Reach 22427 := rs (se 1 (by rfl) ⟨16820, by rfl⟩) R33641
theorem R88229 : Reach 88229 := rs (se 4 (by rfl) ⟨8271, by rfl⟩) R16543
theorem R55619 : Reach 55619 := rs (se 1 (by rfl) ⟨41714, by rfl⟩) R83429
theorem R23087 : Reach 23087 := rs (se 1 (by rfl) ⟨17315, by rfl⟩) R34631
theorem R23423 : Reach 23423 := rs (se 1 (by rfl) ⟨17567, by rfl⟩) R35135
theorem R23495 : Reach 23495 := rs (se 1 (by rfl) ⟨17621, by rfl⟩) R35243
theorem R23519 : Reach 23519 := rs (se 1 (by rfl) ⟨17639, by rfl⟩) R35279
theorem R285677 : Reach 285677 := rs (se 3 (by rfl) ⟨53564, by rfl⟩) R107129
theorem R89531 : Reach 89531 := rs (se 1 (by rfl) ⟨67148, by rfl⟩) R134297
theorem R24043 : Reach 24043 := rs (se 1 (by rfl) ⟨18032, by rfl⟩) R36065
theorem R24383 : Reach 24383 := rs (se 1 (by rfl) ⟨18287, by rfl⟩) R36575
theorem R24457 : Reach 24457 := rs (se 2 (by rfl) ⟨9171, by rfl⟩) R18343
theorem R221089 : Reach 221089 := rs (se 2 (by rfl) ⟨82908, by rfl⟩) R165817
theorem R57287 : Reach 57287 := rs (se 1 (by rfl) ⟨42965, by rfl⟩) R85931
theorem R90071 : Reach 90071 := rs (se 1 (by rfl) ⟨67553, by rfl⟩) R135107
theorem R25447 : Reach 25447 := rs (se 1 (by rfl) ⟨19085, by rfl⟩) R38171
theorem R25481 : Reach 25481 := rs (se 2 (by rfl) ⟨9555, by rfl⟩) R19111
theorem R91489 : Reach 91489 := rs (se 2 (by rfl) ⟨34308, by rfl⟩) R68617
theorem R26015 : Reach 26015 := rs (se 1 (by rfl) ⟨19511, by rfl⟩) R39023
theorem R321079 : Reach 321079 := rs (se 1 (by rfl) ⟨240809, by rfl⟩) R481619
theorem R157427 : Reach 157427 := rs (se 1 (by rfl) ⟨118070, by rfl⟩) R236141
theorem R551123 : Reach 551123 := rs (se 1 (by rfl) ⟨413342, by rfl⟩) R826685
theorem R26855 : Reach 26855 := rs (se 1 (by rfl) ⟨20141, by rfl⟩) R40283
theorem R26921 : Reach 26921 := rs (se 2 (by rfl) ⟨10095, by rfl⟩) R20191
theorem R9038141 : Reach 9038141 := rs (se 3 (by rfl) ⟨1694651, by rfl⟩) R3389303
theorem R158543 : Reach 158543 := rs (se 1 (by rfl) ⟨118907, by rfl⟩) R237815
theorem R60385 : Reach 60385 := rs (se 2 (by rfl) ⟨22644, by rfl⟩) R45289
theorem R27731 : Reach 27731 := rs (se 1 (by rfl) ⟨20798, by rfl⟩) R41597
theorem R27743 : Reach 27743 := rs (se 1 (by rfl) ⟨20807, by rfl⟩) R41615
theorem R27809 : Reach 27809 := rs (se 2 (by rfl) ⟨10428, by rfl⟩) R20857
theorem R27859 : Reach 27859 := rs (se 1 (by rfl) ⟨20894, by rfl⟩) R41789
theorem R60641 : Reach 60641 := rs (se 2 (by rfl) ⟨22740, by rfl⟩) R45481
theorem R93631 : Reach 93631 := rs (se 1 (by rfl) ⟨70223, by rfl⟩) R140447
theorem R60911 : Reach 60911 := rs (se 1 (by rfl) ⟨45683, by rfl⟩) R91367
theorem R28201 : Reach 28201 := rs (se 2 (by rfl) ⟨10575, by rfl⟩) R21151
theorem R28367 : Reach 28367 := rs (se 1 (by rfl) ⟨21275, by rfl⟩) R42551
theorem R28487 : Reach 28487 := rs (se 1 (by rfl) ⟨21365, by rfl⟩) R42731
theorem R61661 : Reach 61661 := rs (se 3 (by rfl) ⟨11561, by rfl⟩) R23123
theorem R28927 : Reach 28927 := rs (se 1 (by rfl) ⟨21695, by rfl⟩) R43391
theorem R29231 : Reach 29231 := rs (se 1 (by rfl) ⟨21923, by rfl⟩) R43847
theorem R160541 : Reach 160541 := rs (se 3 (by rfl) ⟨30101, by rfl⟩) R60203
theorem R29479 : Reach 29479 := rs (se 1 (by rfl) ⟨22109, by rfl⟩) R44219
theorem R62329 : Reach 62329 := rs (se 2 (by rfl) ⟨23373, by rfl⟩) R46747
theorem R357473 : Reach 357473 := rs (se 2 (by rfl) ⟨134052, by rfl⟩) R268105
theorem R29921 : Reach 29921 := rs (se 2 (by rfl) ⟨11220, by rfl⟩) R22441
theorem R128951 : Reach 128951 := rs (se 1 (by rfl) ⟨96713, by rfl⟩) R193427
theorem R260111 : Reach 260111 := rs (se 1 (by rfl) ⟨195083, by rfl⟩) R390167
theorem R31279 : Reach 31279 := rs (se 1 (by rfl) ⟨23459, by rfl⟩) R46919
theorem R64475 : Reach 64475 := rs (se 1 (by rfl) ⟨48356, by rfl⟩) R96713
theorem R64637 : Reach 64637 := rs (se 3 (by rfl) ⟨12119, by rfl⟩) R24239
theorem R261415 : Reach 261415 := rs (se 1 (by rfl) ⟨196061, by rfl⟩) R392123
theorem R425645 : Reach 425645 := rs (se 3 (by rfl) ⟨79808, by rfl⟩) R159617
theorem R98171 : Reach 98171 := rs (se 1 (by rfl) ⟨73628, by rfl⟩) R147257
theorem R33011 : Reach 33011 := rs (se 1 (by rfl) ⟨24758, by rfl⟩) R49517
theorem R262439 : Reach 262439 := rs (se 1 (by rfl) ⟨196829, by rfl⟩) R393659
theorem R524879 : Reach 524879 := rs (se 1 (by rfl) ⟨393659, by rfl⟩) R787319
theorem R98981 : Reach 98981 := rs (se 4 (by rfl) ⟨9279, by rfl⟩) R18559
theorem R66311 : Reach 66311 := rs (se 1 (by rfl) ⟨49733, by rfl⟩) R99467
theorem R33695 : Reach 33695 := rs (se 1 (by rfl) ⟨25271, by rfl⟩) R50543
theorem R33929 : Reach 33929 := rs (se 2 (by rfl) ⟨12723, by rfl⟩) R25447
theorem R67199 : Reach 67199 := rs (se 1 (by rfl) ⟨50399, by rfl⟩) R100799
theorem R67337 : Reach 67337 := rs (se 2 (by rfl) ⟨25251, by rfl⟩) R50503
theorem R67391 : Reach 67391 := rs (se 1 (by rfl) ⟨50543, by rfl⟩) R101087
theorem R428105 : Reach 428105 := rs (se 2 (by rfl) ⟨160539, by rfl⟩) R321079
theorem R166211 : Reach 166211 := rs (se 1 (by rfl) ⟨124658, by rfl⟩) R249317
theorem R67949 : Reach 67949 := rs (se 3 (by rfl) ⟨12740, by rfl⟩) R25481
theorem R134399 : Reach 134399 := rs (se 1 (by rfl) ⟨100799, by rfl⟩) R201599
theorem R68921 : Reach 68921 := rs (se 2 (by rfl) ⟨25845, by rfl⟩) R51691
theorem R36989 : Reach 36989 := rs (se 3 (by rfl) ⟨6935, by rfl⟩) R13871
theorem R37079 : Reach 37079 := rs (se 1 (by rfl) ⟨27809, by rfl⟩) R55619
theorem R37145 : Reach 37145 := rs (se 2 (by rfl) ⟨13929, by rfl⟩) R27859
theorem R37601 : Reach 37601 := rs (se 2 (by rfl) ⟨14100, by rfl⟩) R28201
theorem R38191 : Reach 38191 := rs (se 1 (by rfl) ⟨28643, by rfl⟩) R57287
theorem R693629 : Reach 693629 := rs (se 3 (by rfl) ⟨130055, by rfl⟩) R260111
theorem R38569 : Reach 38569 := rs (se 2 (by rfl) ⟨14463, by rfl⟩) R28927
theorem R104429 : Reach 104429 := rs (se 3 (by rfl) ⟨19580, by rfl⟩) R39161
theorem R39305 : Reach 39305 := rs (se 2 (by rfl) ⟨14739, by rfl⟩) R29479
theorem R104951 : Reach 104951 := rs (se 1 (by rfl) ⟨78713, by rfl⟩) R157427
theorem R203255 : Reach 203255 := rs (se 1 (by rfl) ⟨152441, by rfl⟩) R304883
theorem R367415 : Reach 367415 := rs (se 1 (by rfl) ⟨275561, by rfl⟩) R551123
theorem R105695 : Reach 105695 := rs (se 1 (by rfl) ⟨79271, by rfl⟩) R158543
theorem R40427 : Reach 40427 := rs (se 1 (by rfl) ⟨30320, by rfl⟩) R60641
theorem R40445 : Reach 40445 := rs (se 3 (by rfl) ⟨7583, by rfl⟩) R15167
theorem R40607 : Reach 40607 := rs (se 1 (by rfl) ⟨30455, by rfl⟩) R60911
theorem R597871 : Reach 597871 := rs (se 1 (by rfl) ⟨448403, by rfl⟩) R896807
theorem R41107 : Reach 41107 := rs (se 1 (by rfl) ⟨30830, by rfl⟩) R61661
theorem R107027 : Reach 107027 := rs (se 1 (by rfl) ⟨80270, by rfl⟩) R160541
theorem R74351 : Reach 74351 := rs (se 1 (by rfl) ⟨55763, by rfl⟩) R111527
theorem R41705 : Reach 41705 := rs (se 2 (by rfl) ⟨15639, by rfl⟩) R31279
theorem R238315 : Reach 238315 := rs (se 1 (by rfl) ⟨178736, by rfl⟩) R357473
theorem R42983 : Reach 42983 := rs (se 1 (by rfl) ⟨32237, by rfl⟩) R64475
theorem R43091 : Reach 43091 := rs (se 1 (by rfl) ⟨32318, by rfl⟩) R64637
theorem R44063 : Reach 44063 := rs (se 1 (by rfl) ⟨33047, by rfl⟩) R66095
theorem R110717 : Reach 110717 := rs (se 3 (by rfl) ⟨20759, by rfl⟩) R41519
theorem R45623 : Reach 45623 := rs (se 1 (by rfl) ⟨34217, by rfl⟩) R68435
theorem R12891 : Reach 12891 := rs (se 1 (by rfl) ⟨9668, by rfl⟩) R19337
theorem R13247 : Reach 13247 := rs (se 1 (by rfl) ⟨9935, by rfl⟩) R19871
theorem R111743 : Reach 111743 := rs (se 1 (by rfl) ⟨83807, by rfl⟩) R167615
theorem R13791 : Reach 13791 := rs (se 1 (by rfl) ⟨10343, by rfl⟩) R20687
theorem R112265 : Reach 112265 := rs (se 2 (by rfl) ⟨42099, by rfl⟩) R84199
theorem R178523 : Reach 178523 := rs (se 1 (by rfl) ⟨133892, by rfl⟩) R267785
theorem R47519 : Reach 47519 := rs (se 1 (by rfl) ⟨35639, by rfl⟩) R71279
theorem R14815 : Reach 14815 := rs (se 1 (by rfl) ⟨11111, by rfl⟩) R22223
theorem R14951 : Reach 14951 := rs (se 1 (by rfl) ⟨11213, by rfl⟩) R22427
theorem R408185 : Reach 408185 := rs (se 2 (by rfl) ⟨153069, by rfl⟩) R306139
theorem R80513 : Reach 80513 := rs (se 2 (by rfl) ⟨30192, by rfl⟩) R60385
theorem R47897 : Reach 47897 := rs (se 2 (by rfl) ⟨17961, by rfl⟩) R35923
theorem R47927 : Reach 47927 := rs (se 1 (by rfl) ⟨35945, by rfl⟩) R71891
theorem R15391 : Reach 15391 := rs (se 1 (by rfl) ⟨11543, by rfl⟩) R23087
theorem R15615 : Reach 15615 := rs (se 1 (by rfl) ⟨11711, by rfl⟩) R23423
theorem R15663 : Reach 15663 := rs (se 1 (by rfl) ⟨11747, by rfl⟩) R23495
theorem R15679 : Reach 15679 := rs (se 1 (by rfl) ⟨11759, by rfl⟩) R23519
theorem R48491 : Reach 48491 := rs (se 1 (by rfl) ⟨36368, by rfl⟩) R72737
theorem R16255 : Reach 16255 := rs (se 1 (by rfl) ⟨12191, by rfl⟩) R24383
theorem R49193 : Reach 49193 := rs (se 2 (by rfl) ⟨18447, by rfl⟩) R36895
theorem R16987 : Reach 16987 := rs (se 1 (by rfl) ⟨12740, by rfl⟩) R25481
theorem R17129 : Reach 17129 := rs (se 2 (by rfl) ⟨6423, by rfl⟩) R12847
theorem R17343 : Reach 17343 := rs (se 1 (by rfl) ⟨13007, by rfl⟩) R26015
theorem R17545 : Reach 17545 := rs (se 2 (by rfl) ⟨6579, by rfl⟩) R13159
theorem R83105 : Reach 83105 := rs (se 2 (by rfl) ⟨31164, by rfl⟩) R62329
theorem R17903 : Reach 17903 := rs (se 1 (by rfl) ⟨13427, by rfl⟩) R26855
theorem R17947 : Reach 17947 := rs (se 1 (by rfl) ⟨13460, by rfl⟩) R26921
theorem R50939 : Reach 50939 := rs (se 1 (by rfl) ⟨38204, by rfl⟩) R76409
theorem R182249 : Reach 182249 := rs (se 2 (by rfl) ⟨68343, by rfl⟩) R136687
theorem R18487 : Reach 18487 := rs (se 1 (by rfl) ⟨13865, by rfl⟩) R27731
theorem R18495 : Reach 18495 := rs (se 1 (by rfl) ⟨13871, by rfl⟩) R27743
theorem R18539 : Reach 18539 := rs (se 1 (by rfl) ⟨13904, by rfl⟩) R27809
theorem R51475 : Reach 51475 := rs (se 1 (by rfl) ⟨38606, by rfl⟩) R77213
theorem R18911 : Reach 18911 := rs (se 1 (by rfl) ⟨14183, by rfl⟩) R28367
theorem R51731 : Reach 51731 := rs (se 1 (by rfl) ⟨38798, by rfl⟩) R77597
theorem R18991 : Reach 18991 := rs (se 1 (by rfl) ⟨14243, by rfl⟩) R28487
theorem R19449 : Reach 19449 := rs (se 2 (by rfl) ⟨7293, by rfl⟩) R14587
theorem R19487 : Reach 19487 := rs (se 1 (by rfl) ⟨14615, by rfl⟩) R29231
theorem R52433 : Reach 52433 := rs (se 2 (by rfl) ⟨19662, by rfl⟩) R39325
theorem R183707 : Reach 183707 := rs (se 1 (by rfl) ⟨137780, by rfl⟩) R275561
theorem R19947 : Reach 19947 := rs (se 1 (by rfl) ⟨14960, by rfl⟩) R29921
theorem R85967 : Reach 85967 := rs (se 1 (by rfl) ⟨64475, by rfl⟩) R128951
theorem R53369 : Reach 53369 := rs (se 2 (by rfl) ⟨20013, by rfl⟩) R40027
theorem R53513 : Reach 53513 := rs (se 2 (by rfl) ⟨20067, by rfl⟩) R40135
theorem R348553 : Reach 348553 := rs (se 2 (by rfl) ⟨130707, by rfl⟩) R261415
theorem R21545 : Reach 21545 := rs (se 2 (by rfl) ⟨8079, by rfl⟩) R16159
theorem R54377 : Reach 54377 := rs (se 2 (by rfl) ⟨20391, by rfl⟩) R40783
theorem R283763 : Reach 283763 := rs (se 1 (by rfl) ⟨212822, by rfl⟩) R425645
theorem R283945 : Reach 283945 := rs (se 2 (by rfl) ⟨106479, by rfl⟩) R212959
theorem R21983 : Reach 21983 := rs (se 1 (by rfl) ⟨16487, by rfl⟩) R32975
theorem R54857 : Reach 54857 := rs (se 2 (by rfl) ⟨20571, by rfl⟩) R41143
theorem R218729 : Reach 218729 := rs (se 2 (by rfl) ⟨82023, by rfl⟩) R164047
theorem R88127 : Reach 88127 := rs (se 1 (by rfl) ⟨66095, by rfl⟩) R132191
theorem R252179 : Reach 252179 := rs (se 1 (by rfl) ⟨189134, by rfl⟩) R378269
theorem R22811 : Reach 22811 := rs (se 1 (by rfl) ⟨17108, by rfl⟩) R34217
theorem R56051 : Reach 56051 := rs (se 1 (by rfl) ⟨42038, by rfl⟩) R84077
theorem R514835 : Reach 514835 := rs (se 1 (by rfl) ⟨386126, by rfl⟩) R772253
theorem R121985 : Reach 121985 := rs (se 2 (by rfl) ⟨45744, by rfl⟩) R91489
theorem R908495 : Reach 908495 := rs (se 1 (by rfl) ⟨681371, by rfl⟩) R1362743
theorem R23963 : Reach 23963 := rs (se 1 (by rfl) ⟨17972, by rfl⟩) R35945
theorem R319177 : Reach 319177 := rs (se 2 (by rfl) ⟨119691, by rfl⟩) R239383
theorem R24671 : Reach 24671 := rs (se 1 (by rfl) ⟨18503, by rfl⟩) R37007
theorem R90209 : Reach 90209 := rs (se 2 (by rfl) ⟨33828, by rfl⟩) R67657
theorem R24745 : Reach 24745 := rs (se 2 (by rfl) ⟨9279, by rfl⟩) R18559
theorem R24935 : Reach 24935 := rs (se 1 (by rfl) ⟨18701, by rfl⟩) R37403
theorem R221615 : Reach 221615 := rs (se 1 (by rfl) ⟨166211, by rfl⟩) R332423
theorem R25319 : Reach 25319 := rs (se 1 (by rfl) ⟨18989, by rfl⟩) R37979
theorem R25427 : Reach 25427 := rs (se 1 (by rfl) ⟨19070, by rfl⟩) R38141
theorem R25865 : Reach 25865 := rs (se 2 (by rfl) ⟨9699, by rfl⟩) R19399
theorem R58819 : Reach 58819 := rs (se 1 (by rfl) ⟨44114, by rfl⟩) R88229
theorem R26095 : Reach 26095 := rs (se 1 (by rfl) ⟨19571, by rfl⟩) R39143
theorem R91649 : Reach 91649 := rs (se 2 (by rfl) ⟨34368, by rfl⟩) R68737
theorem R26219 : Reach 26219 := rs (se 1 (by rfl) ⟨19664, by rfl⟩) R39329
theorem R26495 : Reach 26495 := rs (se 1 (by rfl) ⟨19871, by rfl⟩) R39743
theorem R124841 : Reach 124841 := rs (se 2 (by rfl) ⟨46815, by rfl⟩) R93631
theorem R190451 : Reach 190451 := rs (se 1 (by rfl) ⟨142838, by rfl⟩) R285677
theorem R26849 : Reach 26849 := rs (se 2 (by rfl) ⟨10068, by rfl⟩) R20137
theorem R92447 : Reach 92447 := rs (se 1 (by rfl) ⟨69335, by rfl⟩) R138671
theorem R59687 : Reach 59687 := rs (se 1 (by rfl) ⟨44765, by rfl⟩) R89531
theorem R289079 : Reach 289079 := rs (se 1 (by rfl) ⟨216809, by rfl⟩) R433619
theorem R60047 : Reach 60047 := rs (se 1 (by rfl) ⟨45035, by rfl⟩) R90071
theorem R27401 : Reach 27401 := rs (se 2 (by rfl) ⟨10275, by rfl⟩) R20551
theorem R27497 : Reach 27497 := rs (se 2 (by rfl) ⟨10311, by rfl⟩) R20623
theorem R715817 : Reach 715817 := rs (se 2 (by rfl) ⟨268431, by rfl⟩) R536863
theorem R224531 : Reach 224531 := rs (se 1 (by rfl) ⟨168398, by rfl⟩) R336797
theorem R28025 : Reach 28025 := rs (se 2 (by rfl) ⟨10509, by rfl⟩) R21019
theorem R28135 : Reach 28135 := rs (se 1 (by rfl) ⟨21101, by rfl⟩) R42203
theorem R28139 : Reach 28139 := rs (se 1 (by rfl) ⟨21104, by rfl⟩) R42209
theorem R28499 : Reach 28499 := rs (se 1 (by rfl) ⟨21374, by rfl⟩) R42749
theorem R28507 : Reach 28507 := rs (se 1 (by rfl) ⟨21380, by rfl⟩) R42761
theorem R94247 : Reach 94247 := rs (se 1 (by rfl) ⟨70685, by rfl⟩) R141371
theorem R28775 : Reach 28775 := rs (se 1 (by rfl) ⟨21581, by rfl⟩) R43163
theorem R28793 : Reach 28793 := rs (se 2 (by rfl) ⟨10797, by rfl⟩) R21595
theorem R6025427 : Reach 6025427 := rs (se 1 (by rfl) ⟨4519070, by rfl⟩) R9038141
theorem R29089 : Reach 29089 := rs (se 2 (by rfl) ⟨10908, by rfl⟩) R21817
theorem R29339 : Reach 29339 := rs (se 1 (by rfl) ⟨22004, by rfl⟩) R44009
theorem R422975 : Reach 422975 := rs (se 1 (by rfl) ⟨317231, by rfl⟩) R634463
theorem R95417 : Reach 95417 := rs (se 2 (by rfl) ⟨35781, by rfl⟩) R71563
theorem R29903 : Reach 29903 := rs (se 1 (by rfl) ⟨22427, by rfl⟩) R44855
theorem R29999 : Reach 29999 := rs (se 1 (by rfl) ⟨22499, by rfl⟩) R44999
theorem R30023 : Reach 30023 := rs (se 1 (by rfl) ⟨22517, by rfl⟩) R45035
theorem R30847 : Reach 30847 := rs (se 1 (by rfl) ⟨23135, by rfl⟩) R46271
theorem R1308869 : Reach 1308869 := rs (se 4 (by rfl) ⟨122706, by rfl⟩) R245413
theorem R63881 : Reach 63881 := rs (se 2 (by rfl) ⟨23955, by rfl⟩) R47911
theorem R31475 : Reach 31475 := rs (se 1 (by rfl) ⟨23606, by rfl⟩) R47213
theorem R32057 : Reach 32057 := rs (se 2 (by rfl) ⟨12021, by rfl⟩) R24043
theorem R32359 : Reach 32359 := rs (se 1 (by rfl) ⟨24269, by rfl⟩) R48539
theorem R32609 : Reach 32609 := rs (se 2 (by rfl) ⟨12228, by rfl⟩) R24457
theorem R294785 : Reach 294785 := rs (se 2 (by rfl) ⟨110544, by rfl⟩) R221089
theorem R65447 : Reach 65447 := rs (se 1 (by rfl) ⟨49085, by rfl⟩) R98171
theorem R32795 : Reach 32795 := rs (se 1 (by rfl) ⟨24596, by rfl⟩) R49193
theorem R32993 : Reach 32993 := rs (se 2 (by rfl) ⟨12372, by rfl⟩) R24745
theorem R98597 : Reach 98597 := rs (se 4 (by rfl) ⟨9243, by rfl⟩) R18487
theorem R65987 : Reach 65987 := rs (se 1 (by rfl) ⟨49490, by rfl⟩) R98981
theorem R99053 : Reach 99053 := rs (se 3 (by rfl) ⟨18572, by rfl⟩) R37145
theorem R33959 : Reach 33959 := rs (se 1 (by rfl) ⟨25469, by rfl⟩) R50939
theorem R34487 : Reach 34487 := rs (se 1 (by rfl) ⟨25865, by rfl⟩) R51731
theorem R34793 : Reach 34793 := rs (se 2 (by rfl) ⟨13047, by rfl⟩) R26095
theorem R34955 : Reach 34955 := rs (se 1 (by rfl) ⟨26216, by rfl⟩) R52433
theorem R35579 : Reach 35579 := rs (se 1 (by rfl) ⟨26684, by rfl⟩) R53369
theorem R35675 : Reach 35675 := rs (se 1 (by rfl) ⟨26756, by rfl⟩) R53513
theorem R68633 : Reach 68633 := rs (se 2 (by rfl) ⟨25737, by rfl⟩) R51475
theorem R36251 : Reach 36251 := rs (se 1 (by rfl) ⟨27188, by rfl⟩) R54377
theorem R462419 : Reach 462419 := rs (se 1 (by rfl) ⟨346814, by rfl⟩) R693629
theorem R36571 : Reach 36571 := rs (se 1 (by rfl) ⟨27428, by rfl⟩) R54857
theorem R69619 : Reach 69619 := rs (se 1 (by rfl) ⟨52214, by rfl⟩) R104429
theorem R168119 : Reach 168119 := rs (se 1 (by rfl) ⟨126089, by rfl⟩) R252179
theorem R69967 : Reach 69967 := rs (se 1 (by rfl) ⟨52475, by rfl⟩) R104951
theorem R135503 : Reach 135503 := rs (se 1 (by rfl) ⟨101627, by rfl⟩) R203255
theorem R37367 : Reach 37367 := rs (se 1 (by rfl) ⟨28025, by rfl⟩) R56051
theorem R37513 : Reach 37513 := rs (se 2 (by rfl) ⟨14067, by rfl⟩) R28135
theorem R70463 : Reach 70463 := rs (se 1 (by rfl) ⟨52847, by rfl⟩) R105695
theorem R38009 : Reach 38009 := rs (se 2 (by rfl) ⟨14253, by rfl⟩) R28507
theorem R71351 : Reach 71351 := rs (se 1 (by rfl) ⟨53513, by rfl⟩) R107027
theorem R464737 : Reach 464737 := rs (se 2 (by rfl) ⟨174276, by rfl⟩) R348553
theorem R39791 : Reach 39791 := rs (se 1 (by rfl) ⟨29843, by rfl⟩) R59687
theorem R39869 : Reach 39869 := rs (se 3 (by rfl) ⟨7475, by rfl⟩) R14951
theorem R40031 : Reach 40031 := rs (se 1 (by rfl) ⟨30023, by rfl⟩) R60047
theorem R73325 : Reach 73325 := rs (se 3 (by rfl) ⟨13748, by rfl⟩) R27497
theorem R73811 : Reach 73811 := rs (se 1 (by rfl) ⟨55358, by rfl⟩) R110717
theorem R41129 : Reach 41129 := rs (se 2 (by rfl) ⟨15423, by rfl⟩) R30847
theorem R74495 : Reach 74495 := rs (se 1 (by rfl) ⟨55871, by rfl⟩) R111743
theorem R74843 : Reach 74843 := rs (se 1 (by rfl) ⟨56132, by rfl⟩) R112265
theorem R42587 : Reach 42587 := rs (se 1 (by rfl) ⟨31940, by rfl⟩) R63881
theorem R272123 : Reach 272123 := rs (se 1 (by rfl) ⟨204092, by rfl⟩) R408185
theorem R3188645 : Reach 3188645 := rs (se 4 (by rfl) ⟨298935, by rfl⟩) R597871
theorem R43145 : Reach 43145 := rs (se 2 (by rfl) ⟨16179, by rfl⟩) R32359
theorem R797161 : Reach 797161 := rs (se 2 (by rfl) ⟨298935, by rfl⟩) R597871
theorem R43631 : Reach 43631 := rs (se 1 (by rfl) ⟨32723, by rfl⟩) R65447
theorem R174959 : Reach 174959 := rs (se 1 (by rfl) ⟨131219, by rfl⟩) R262439
theorem R44207 : Reach 44207 := rs (se 1 (by rfl) ⟨33155, by rfl⟩) R66311
theorem R44891 : Reach 44891 := rs (se 1 (by rfl) ⟨33668, by rfl⟩) R67337
theorem R44927 : Reach 44927 := rs (se 1 (by rfl) ⟨33695, by rfl⟩) R67391
theorem R110807 : Reach 110807 := rs (se 1 (by rfl) ⟨83105, by rfl⟩) R166211
theorem R45299 : Reach 45299 := rs (se 1 (by rfl) ⟨33974, by rfl⟩) R67949
theorem R78425 : Reach 78425 := rs (se 2 (by rfl) ⟨29409, by rfl⟩) R58819
theorem R45677 : Reach 45677 := rs (se 3 (by rfl) ⟨8564, by rfl⟩) R17129
theorem R12991 : Reach 12991 := rs (se 1 (by rfl) ⟨9743, by rfl⟩) R19487
theorem R45947 : Reach 45947 := rs (se 1 (by rfl) ⟨34460, by rfl⟩) R68921
theorem R14363 : Reach 14363 := rs (se 1 (by rfl) ⟨10772, by rfl⟩) R21545
theorem R14655 : Reach 14655 := rs (se 1 (by rfl) ⟨10991, by rfl⟩) R21983
theorem R145819 : Reach 145819 := rs (se 1 (by rfl) ⟨109364, by rfl⟩) R218729
theorem R244397 : Reach 244397 := rs (se 3 (by rfl) ⟨45824, by rfl⟩) R91649
theorem R15207 : Reach 15207 := rs (se 1 (by rfl) ⟨11405, by rfl⟩) R22811
theorem R146285 : Reach 146285 := rs (se 3 (by rfl) ⟨27428, by rfl⟩) R54857
theorem R343223 : Reach 343223 := rs (se 1 (by rfl) ⟨257417, by rfl⟩) R514835
theorem R244943 : Reach 244943 := rs (se 1 (by rfl) ⟨183707, by rfl⟩) R367415
theorem R81323 : Reach 81323 := rs (se 1 (by rfl) ⟨60992, by rfl⟩) R121985
theorem R605663 : Reach 605663 := rs (se 1 (by rfl) ⟨454247, by rfl⟩) R908495
theorem R15975 : Reach 15975 := rs (se 1 (by rfl) ⟨11981, by rfl⟩) R23963
theorem R16447 : Reach 16447 := rs (se 1 (by rfl) ⟨12335, by rfl⟩) R24671
theorem R16623 : Reach 16623 := rs (se 1 (by rfl) ⟨12467, by rfl⟩) R24935
theorem R147743 : Reach 147743 := rs (se 1 (by rfl) ⟨110807, by rfl⟩) R221615
theorem R49567 : Reach 49567 := rs (se 1 (by rfl) ⟨37175, by rfl⟩) R74351
theorem R16879 : Reach 16879 := rs (se 1 (by rfl) ⟨12659, by rfl⟩) R25319
theorem R16951 : Reach 16951 := rs (se 1 (by rfl) ⟨12713, by rfl⟩) R25427
theorem R17243 : Reach 17243 := rs (se 1 (by rfl) ⟨12932, by rfl⟩) R25865
theorem R17479 : Reach 17479 := rs (se 1 (by rfl) ⟨13109, by rfl⟩) R26219
theorem R17663 : Reach 17663 := rs (se 1 (by rfl) ⟨13247, by rfl⟩) R26495
theorem R83227 : Reach 83227 := rs (se 1 (by rfl) ⟨62420, by rfl⟩) R124841
theorem R17899 : Reach 17899 := rs (se 1 (by rfl) ⟨13424, by rfl⟩) R26849
theorem R378593 : Reach 378593 := rs (se 2 (by rfl) ⟨141972, by rfl⟩) R283945
theorem R50921 : Reach 50921 := rs (se 2 (by rfl) ⟨19095, by rfl⟩) R38191
theorem R18267 : Reach 18267 := rs (se 1 (by rfl) ⟨13700, by rfl⟩) R27401
theorem R18331 : Reach 18331 := rs (se 1 (by rfl) ⟨13748, by rfl⟩) R27497
theorem R477211 : Reach 477211 := rs (se 1 (by rfl) ⟨357908, by rfl⟩) R715817
theorem R149687 : Reach 149687 := rs (se 1 (by rfl) ⟨112265, by rfl⟩) R224531
theorem R51425 : Reach 51425 := rs (se 2 (by rfl) ⟨19284, by rfl⟩) R38569
theorem R18683 : Reach 18683 := rs (se 1 (by rfl) ⟨14012, by rfl⟩) R28025
theorem R18759 : Reach 18759 := rs (se 1 (by rfl) ⟨14069, by rfl⟩) R28139
theorem R18999 : Reach 18999 := rs (se 1 (by rfl) ⟨14249, by rfl⟩) R28499
theorem R19183 : Reach 19183 := rs (se 1 (by rfl) ⟨14387, by rfl⟩) R28775
theorem R19195 : Reach 19195 := rs (se 1 (by rfl) ⟨14396, by rfl⟩) R28793
theorem R51965 : Reach 51965 := rs (se 3 (by rfl) ⟨9743, by rfl⟩) R19487
theorem R4016951 : Reach 4016951 := rs (se 1 (by rfl) ⟨3012713, by rfl⟩) R6025427
theorem R19559 : Reach 19559 := rs (se 1 (by rfl) ⟨14669, by rfl⟩) R29339
theorem R19753 : Reach 19753 := rs (se 2 (by rfl) ⟨7407, by rfl⟩) R14815
theorem R281983 : Reach 281983 := rs (se 1 (by rfl) ⟨211487, by rfl⟩) R422975
theorem R19935 : Reach 19935 := rs (se 1 (by rfl) ⟨14951, by rfl⟩) R29903
theorem R19999 : Reach 19999 := rs (se 1 (by rfl) ⟨14999, by rfl⟩) R29999
theorem R20015 : Reach 20015 := rs (se 1 (by rfl) ⟨15011, by rfl⟩) R30023
theorem R872579 : Reach 872579 := rs (se 1 (by rfl) ⟨654434, by rfl⟩) R1308869
theorem R119015 : Reach 119015 := rs (se 1 (by rfl) ⟨89261, by rfl⟩) R178523
theorem R53675 : Reach 53675 := rs (se 1 (by rfl) ⟨40256, by rfl⟩) R80513
theorem R20983 : Reach 20983 := rs (se 1 (by rfl) ⟨15737, by rfl⟩) R31475
theorem R21371 : Reach 21371 := rs (se 1 (by rfl) ⟨16028, by rfl⟩) R32057
theorem R21739 : Reach 21739 := rs (se 1 (by rfl) ⟨16304, by rfl⟩) R32609
theorem R22007 : Reach 22007 := rs (se 1 (by rfl) ⟨16505, by rfl⟩) R33011
theorem R54809 : Reach 54809 := rs (se 2 (by rfl) ⟨20553, by rfl⟩) R41107
theorem R349919 : Reach 349919 := rs (se 1 (by rfl) ⟨262439, by rfl⟩) R524879
theorem R22463 : Reach 22463 := rs (se 1 (by rfl) ⟨16847, by rfl⟩) R33695
theorem R22619 : Reach 22619 := rs (se 1 (by rfl) ⟨16964, by rfl⟩) R33929
theorem R55403 : Reach 55403 := rs (se 1 (by rfl) ⟨41552, by rfl⟩) R83105
theorem R22649 : Reach 22649 := rs (se 2 (by rfl) ⟨8493, by rfl⟩) R16987
theorem R317753 : Reach 317753 := rs (se 2 (by rfl) ⟨119157, by rfl⟩) R238315
theorem R121499 : Reach 121499 := rs (se 1 (by rfl) ⟨91124, by rfl⟩) R182249
theorem R285403 : Reach 285403 := rs (se 1 (by rfl) ⟨214052, by rfl⟩) R428105
theorem R23393 : Reach 23393 := rs (se 2 (by rfl) ⟨8772, by rfl⟩) R17545
theorem R89599 : Reach 89599 := rs (se 1 (by rfl) ⟨67199, by rfl⟩) R134399
theorem R155141 : Reach 155141 := rs (se 4 (by rfl) ⟨14544, by rfl⟩) R29089
theorem R122471 : Reach 122471 := rs (se 1 (by rfl) ⟨91853, by rfl⟩) R183707
theorem R57311 : Reach 57311 := rs (se 1 (by rfl) ⟨42983, by rfl⟩) R85967
theorem R24659 : Reach 24659 := rs (se 1 (by rfl) ⟨18494, by rfl⟩) R36989
theorem R24719 : Reach 24719 := rs (se 1 (by rfl) ⟨18539, by rfl⟩) R37079
theorem R25067 : Reach 25067 := rs (se 1 (by rfl) ⟨18800, by rfl⟩) R37601
theorem R189175 : Reach 189175 := rs (se 1 (by rfl) ⟨141881, by rfl⟩) R283763
theorem R58751 : Reach 58751 := rs (se 1 (by rfl) ⟨44063, by rfl⟩) R88127
theorem R26203 : Reach 26203 := rs (se 1 (by rfl) ⟨19652, by rfl⟩) R39305
theorem R26951 : Reach 26951 := rs (se 1 (by rfl) ⟨20213, by rfl⟩) R40427
theorem R26963 : Reach 26963 := rs (se 1 (by rfl) ⟨20222, by rfl⟩) R40445
theorem R27071 : Reach 27071 := rs (se 1 (by rfl) ⟨20303, by rfl⟩) R40607
theorem R60139 : Reach 60139 := rs (se 1 (by rfl) ⟨45104, by rfl⟩) R90209
theorem R27803 : Reach 27803 := rs (se 1 (by rfl) ⟨20852, by rfl⟩) R41705
theorem R28655 : Reach 28655 := rs (se 1 (by rfl) ⟨21491, by rfl⟩) R42983
theorem R716789 : Reach 716789 := rs (se 5 (by rfl) ⟨33599, by rfl⟩) R67199
theorem R126967 : Reach 126967 := rs (se 1 (by rfl) ⟨95225, by rfl⟩) R190451
theorem R28727 : Reach 28727 := rs (se 1 (by rfl) ⟨21545, by rfl⟩) R43091
theorem R61631 : Reach 61631 := rs (se 1 (by rfl) ⟨46223, by rfl⟩) R92447
theorem R192719 : Reach 192719 := rs (se 1 (by rfl) ⟨144539, by rfl⟩) R289079
theorem R29375 : Reach 29375 := rs (se 1 (by rfl) ⟨22031, by rfl⟩) R44063
theorem R62831 : Reach 62831 := rs (se 1 (by rfl) ⟨47123, by rfl⟩) R94247
theorem R30415 : Reach 30415 := rs (se 1 (by rfl) ⟨22811, by rfl⟩) R45623
theorem R63611 : Reach 63611 := rs (se 1 (by rfl) ⟨47708, by rfl⟩) R95417
theorem R31679 : Reach 31679 := rs (se 1 (by rfl) ⟨23759, by rfl⟩) R47519
theorem R31931 : Reach 31931 := rs (se 1 (by rfl) ⟨23948, by rfl⟩) R47897
theorem R31951 : Reach 31951 := rs (se 1 (by rfl) ⟨23963, by rfl⟩) R47927
theorem R32327 : Reach 32327 := rs (se 1 (by rfl) ⟨24245, by rfl⟩) R48491
theorem R425569 : Reach 425569 := rs (se 2 (by rfl) ⟨159588, by rfl⟩) R319177
theorem R196523 : Reach 196523 := rs (se 1 (by rfl) ⟨147392, by rfl⟩) R294785
theorem R98495 : Reach 98495 := rs (se 1 (by rfl) ⟨73871, by rfl⟩) R147743
theorem R65731 : Reach 65731 := rs (se 1 (by rfl) ⟨49298, by rfl⟩) R98597
theorem R196829 : Reach 196829 := rs (se 3 (by rfl) ⟨36905, by rfl⟩) R73811
theorem R2326877 : Reach 2326877 := rs (se 3 (by rfl) ⟨436289, by rfl⟩) R872579
theorem R66035 : Reach 66035 := rs (se 1 (by rfl) ⟨49526, by rfl⟩) R99053
theorem R66089 : Reach 66089 := rs (se 2 (by rfl) ⟨24783, by rfl⟩) R49567
theorem R33947 : Reach 33947 := rs (se 1 (by rfl) ⟨25460, by rfl⟩) R50921
theorem R99791 : Reach 99791 := rs (se 1 (by rfl) ⟨74843, by rfl⟩) R149687
theorem R34283 : Reach 34283 := rs (se 1 (by rfl) ⟨25712, by rfl⟩) R51425
theorem R34643 : Reach 34643 := rs (se 1 (by rfl) ⟨25982, by rfl⟩) R51965
theorem R34937 : Reach 34937 := rs (se 2 (by rfl) ⟨13101, by rfl⟩) R26203
theorem R35783 : Reach 35783 := rs (se 1 (by rfl) ⟨26837, by rfl⟩) R53675
theorem R36539 : Reach 36539 := rs (se 1 (by rfl) ⟨27404, by rfl⟩) R54809
theorem R233279 : Reach 233279 := rs (se 1 (by rfl) ⟨174959, by rfl⟩) R349919
theorem R36935 : Reach 36935 := rs (se 1 (by rfl) ⟨27701, by rfl⟩) R55403
theorem R103427 : Reach 103427 := rs (se 1 (by rfl) ⟨77570, by rfl⟩) R155141
theorem R38207 : Reach 38207 := rs (se 1 (by rfl) ⟨28655, by rfl⟩) R57311
theorem R169289 : Reach 169289 := rs (se 2 (by rfl) ⟨63483, by rfl⟩) R126967
theorem R39167 : Reach 39167 := rs (se 1 (by rfl) ⟨29375, by rfl⟩) R58751
theorem R40553 : Reach 40553 := rs (se 2 (by rfl) ⟨15207, by rfl⟩) R30415
theorem R41087 : Reach 41087 := rs (se 1 (by rfl) ⟨30815, by rfl⟩) R61631
theorem R73871 : Reach 73871 := rs (se 1 (by rfl) ⟨55403, by rfl⟩) R110807
theorem R41887 : Reach 41887 := rs (se 1 (by rfl) ⟨31415, by rfl⟩) R62831
theorem R42407 : Reach 42407 := rs (se 1 (by rfl) ⟨31805, by rfl⟩) R63611
theorem R42601 : Reach 42601 := rs (se 2 (by rfl) ⟨15975, by rfl⟩) R31951
theorem R567425 : Reach 567425 := rs (se 2 (by rfl) ⟨212784, by rfl⟩) R425569
theorem R403775 : Reach 403775 := rs (se 1 (by rfl) ⟨302831, by rfl⟩) R605663
theorem R1911437 : Reach 1911437 := rs (se 3 (by rfl) ⟨358394, by rfl⟩) R716789
theorem R43991 : Reach 43991 := rs (se 1 (by rfl) ⟨32993, by rfl⟩) R65987
theorem R110969 : Reach 110969 := rs (se 2 (by rfl) ⟨41613, by rfl⟩) R83227
theorem R373157 : Reach 373157 := rs (se 4 (by rfl) ⟨34983, by rfl⟩) R69967
theorem R45755 : Reach 45755 := rs (se 1 (by rfl) ⟨34316, by rfl⟩) R68633
theorem R13039 : Reach 13039 := rs (se 1 (by rfl) ⟨9779, by rfl⟩) R19559
theorem R13343 : Reach 13343 := rs (se 1 (by rfl) ⟨10007, by rfl⟩) R20015
theorem R308279 : Reach 308279 := rs (se 1 (by rfl) ⟨231209, by rfl⟩) R462419
theorem R636281 : Reach 636281 := rs (se 2 (by rfl) ⟨238605, by rfl⟩) R477211
theorem R112079 : Reach 112079 := rs (se 1 (by rfl) ⟨84059, by rfl⟩) R168119
theorem R79343 : Reach 79343 := rs (se 1 (by rfl) ⟨59507, by rfl⟩) R119015
theorem R46975 : Reach 46975 := rs (se 1 (by rfl) ⟨35231, by rfl⟩) R70463
theorem R14247 : Reach 14247 := rs (se 1 (by rfl) ⟨10685, by rfl⟩) R21371
theorem R1062881 : Reach 1062881 := rs (se 2 (by rfl) ⟨398580, by rfl⟩) R797161
theorem R47101 : Reach 47101 := rs (se 3 (by rfl) ⟨8831, by rfl⟩) R17663
theorem R80185 : Reach 80185 := rs (se 2 (by rfl) ⟨30069, by rfl⟩) R60139
theorem R14671 : Reach 14671 := rs (se 1 (by rfl) ⟨11003, by rfl⟩) R22007
theorem R47567 : Reach 47567 := rs (se 1 (by rfl) ⟨35675, by rfl⟩) R71351
theorem R14975 : Reach 14975 := rs (se 1 (by rfl) ⟨11231, by rfl⟩) R22463
theorem R277141 : Reach 277141 := rs (se 6 (by rfl) ⟨6495, by rfl⟩) R12991
theorem R15079 : Reach 15079 := rs (se 1 (by rfl) ⟨11309, by rfl⟩) R22619
theorem R15099 : Reach 15099 := rs (se 1 (by rfl) ⟨11324, by rfl⟩) R22649
theorem R211835 : Reach 211835 := rs (se 1 (by rfl) ⟨158876, by rfl⟩) R317753
theorem R80999 : Reach 80999 := rs (se 1 (by rfl) ⟨60749, by rfl⟩) R121499
theorem R375977 : Reach 375977 := rs (se 2 (by rfl) ⟨140991, by rfl⟩) R281983
theorem R15595 : Reach 15595 := rs (se 1 (by rfl) ⟨11696, by rfl⟩) R23393
theorem R48761 : Reach 48761 := rs (se 2 (by rfl) ⟨18285, by rfl⟩) R36571
theorem R81647 : Reach 81647 := rs (se 1 (by rfl) ⟨61235, by rfl⟩) R122471
theorem R48883 : Reach 48883 := rs (se 1 (by rfl) ⟨36662, by rfl⟩) R73325
theorem R49207 : Reach 49207 := rs (se 1 (by rfl) ⟨36905, by rfl⟩) R73811
theorem R16439 : Reach 16439 := rs (se 1 (by rfl) ⟨12329, by rfl⟩) R24659
theorem R16479 : Reach 16479 := rs (se 1 (by rfl) ⟨12359, by rfl⟩) R24719
theorem R16711 : Reach 16711 := rs (se 1 (by rfl) ⟨12533, by rfl⟩) R25067
theorem R49663 : Reach 49663 := rs (se 1 (by rfl) ⟨37247, by rfl⟩) R74495
theorem R49895 : Reach 49895 := rs (se 1 (by rfl) ⟨37421, by rfl⟩) R74843
theorem R50017 : Reach 50017 := rs (se 2 (by rfl) ⟨18756, by rfl⟩) R37513
theorem R17321 : Reach 17321 := rs (se 2 (by rfl) ⟨6495, by rfl⟩) R12991
theorem R181415 : Reach 181415 := rs (se 1 (by rfl) ⟨136061, by rfl⟩) R272123
theorem R17967 : Reach 17967 := rs (se 1 (by rfl) ⟨13475, by rfl⟩) R26951
theorem R17975 : Reach 17975 := rs (se 1 (by rfl) ⟨13481, by rfl⟩) R26963
theorem R18047 : Reach 18047 := rs (se 1 (by rfl) ⟨13535, by rfl⟩) R27071
theorem R116639 : Reach 116639 := rs (se 1 (by rfl) ⟨87479, by rfl⟩) R174959
theorem R18535 : Reach 18535 := rs (se 1 (by rfl) ⟨13901, by rfl⟩) R27803
theorem R19103 : Reach 19103 := rs (se 1 (by rfl) ⟨14327, by rfl⟩) R28655
theorem R19151 : Reach 19151 := rs (se 1 (by rfl) ⟨14363, by rfl⟩) R28727
theorem R52283 : Reach 52283 := rs (se 1 (by rfl) ⟨39212, by rfl⟩) R78425
theorem R19583 : Reach 19583 := rs (se 1 (by rfl) ⟨14687, by rfl⟩) R29375
theorem R380537 : Reach 380537 := rs (se 2 (by rfl) ⟨142701, by rfl⟩) R285403
theorem R21119 : Reach 21119 := rs (se 1 (by rfl) ⟨15839, by rfl⟩) R31679
theorem R119465 : Reach 119465 := rs (se 2 (by rfl) ⟨44799, by rfl⟩) R89599
theorem R21287 : Reach 21287 := rs (se 1 (by rfl) ⟨15965, by rfl⟩) R31931
theorem R54215 : Reach 54215 := rs (se 1 (by rfl) ⟨40661, by rfl⟩) R81323
theorem R21551 : Reach 21551 := rs (se 1 (by rfl) ⟨16163, by rfl⟩) R32327
theorem R21863 : Reach 21863 := rs (se 1 (by rfl) ⟨16397, by rfl⟩) R32795
theorem R21929 : Reach 21929 := rs (se 2 (by rfl) ⟨8223, by rfl⟩) R16447
theorem R21995 : Reach 21995 := rs (se 1 (by rfl) ⟨16496, by rfl⟩) R32993
theorem R22505 : Reach 22505 := rs (se 2 (by rfl) ⟨8439, by rfl⟩) R16879
theorem R22601 : Reach 22601 := rs (se 2 (by rfl) ⟨8475, by rfl⟩) R16951
theorem R22639 : Reach 22639 := rs (se 1 (by rfl) ⟨16979, by rfl⟩) R33959
theorem R252233 : Reach 252233 := rs (se 2 (by rfl) ⟨94587, by rfl⟩) R189175
theorem R22991 : Reach 22991 := rs (se 1 (by rfl) ⟨17243, by rfl⟩) R34487
theorem R252395 : Reach 252395 := rs (se 1 (by rfl) ⟨189296, by rfl⟩) R378593
theorem R23195 : Reach 23195 := rs (se 1 (by rfl) ⟨17396, by rfl⟩) R34793
theorem R23303 : Reach 23303 := rs (se 1 (by rfl) ⟨17477, by rfl⟩) R34955
theorem R23719 : Reach 23719 := rs (se 1 (by rfl) ⟨17789, by rfl⟩) R35579
theorem R2677967 : Reach 2677967 := rs (se 1 (by rfl) ⟨2008475, by rfl⟩) R4016951
theorem R23783 : Reach 23783 := rs (se 1 (by rfl) ⟨17837, by rfl⟩) R35675
theorem R777701 : Reach 777701 := rs (se 4 (by rfl) ⟨72909, by rfl⟩) R145819
theorem R24167 : Reach 24167 := rs (se 1 (by rfl) ⟨18125, by rfl⟩) R36251
theorem R90335 : Reach 90335 := rs (se 1 (by rfl) ⟨67751, by rfl⟩) R135503
theorem R24911 : Reach 24911 := rs (se 1 (by rfl) ⟨18683, by rfl⟩) R37367
theorem R90557 : Reach 90557 := rs (se 3 (by rfl) ⟨16979, by rfl⟩) R33959
theorem R25339 : Reach 25339 := rs (se 1 (by rfl) ⟨19004, by rfl⟩) R38009
theorem R25577 : Reach 25577 := rs (se 2 (by rfl) ⟨9591, by rfl⟩) R19183
theorem R26527 : Reach 26527 := rs (se 1 (by rfl) ⟨19895, by rfl⟩) R39791
theorem R26579 : Reach 26579 := rs (se 1 (by rfl) ⟨19934, by rfl⟩) R39869
theorem R26687 : Reach 26687 := rs (se 1 (by rfl) ⟨20015, by rfl⟩) R40031
theorem R92825 : Reach 92825 := rs (se 2 (by rfl) ⟨34809, by rfl⟩) R69619
theorem R27419 : Reach 27419 := rs (se 1 (by rfl) ⟨20564, by rfl⟩) R41129
theorem R60317 : Reach 60317 := rs (se 3 (by rfl) ⟨11309, by rfl⟩) R22619
theorem R93221 : Reach 93221 := rs (se 4 (by rfl) ⟨8739, by rfl⟩) R17479
theorem R27977 : Reach 27977 := rs (se 2 (by rfl) ⟨10491, by rfl⟩) R20983
theorem R28391 : Reach 28391 := rs (se 1 (by rfl) ⟨21293, by rfl⟩) R42587
theorem R2125763 : Reach 2125763 := rs (se 1 (by rfl) ⟨1594322, by rfl⟩) R3188645
theorem R28763 : Reach 28763 := rs (se 1 (by rfl) ⟨21572, by rfl⟩) R43145
theorem R28985 : Reach 28985 := rs (se 2 (by rfl) ⟨10869, by rfl⟩) R21739
theorem R29087 : Reach 29087 := rs (se 1 (by rfl) ⟨21815, by rfl⟩) R43631
theorem R29471 : Reach 29471 := rs (se 1 (by rfl) ⟨22103, by rfl⟩) R44207
theorem R619649 : Reach 619649 := rs (se 2 (by rfl) ⟨232368, by rfl⟩) R464737
theorem R29927 : Reach 29927 := rs (se 1 (by rfl) ⟨22445, by rfl⟩) R44891
theorem R29951 : Reach 29951 := rs (se 1 (by rfl) ⟨22463, by rfl⟩) R44927
theorem R128479 : Reach 128479 := rs (se 1 (by rfl) ⟨96359, by rfl⟩) R192719
theorem R30199 : Reach 30199 := rs (se 1 (by rfl) ⟨22649, by rfl⟩) R45299
theorem R30451 : Reach 30451 := rs (se 1 (by rfl) ⟨22838, by rfl⟩) R45677
theorem R30631 : Reach 30631 := rs (se 1 (by rfl) ⟨22973, by rfl⟩) R45947
theorem R162931 : Reach 162931 := rs (se 1 (by rfl) ⟨122198, by rfl⟩) R244397
theorem R97523 : Reach 97523 := rs (se 1 (by rfl) ⟨73142, by rfl⟩) R146285
theorem R228815 : Reach 228815 := rs (se 1 (by rfl) ⟨171611, by rfl⟩) R343223
theorem R163295 : Reach 163295 := rs (se 1 (by rfl) ⟨122471, by rfl⟩) R244943
theorem R131015 : Reach 131015 := rs (se 1 (by rfl) ⟨98261, by rfl⟩) R196523
theorem R65609 : Reach 65609 := rs (se 2 (by rfl) ⟨24603, by rfl⟩) R49207
theorem R65663 : Reach 65663 := rs (se 1 (by rfl) ⟨49247, by rfl⟩) R98495
theorem R131219 : Reach 131219 := rs (se 1 (by rfl) ⟨98414, by rfl⟩) R196829
theorem R33263 : Reach 33263 := rs (se 1 (by rfl) ⟨24947, by rfl⟩) R49895
theorem R66217 : Reach 66217 := rs (se 2 (by rfl) ⟨24831, by rfl⟩) R49663
theorem R66527 : Reach 66527 := rs (se 1 (by rfl) ⟨49895, by rfl⟩) R99791
theorem R33785 : Reach 33785 := rs (se 2 (by rfl) ⟨12669, by rfl⟩) R25339
theorem R66689 : Reach 66689 := rs (se 2 (by rfl) ⟨25008, by rfl⟩) R50017
theorem R35369 : Reach 35369 := rs (se 2 (by rfl) ⟨13263, by rfl⟩) R26527
theorem R36143 : Reach 36143 := rs (se 1 (by rfl) ⟨27107, by rfl⟩) R54215
theorem R68951 : Reach 68951 := rs (se 1 (by rfl) ⟨51713, by rfl⟩) R103427
theorem R168155 : Reach 168155 := rs (se 1 (by rfl) ⟨126116, by rfl⟩) R252233
theorem R168263 : Reach 168263 := rs (se 1 (by rfl) ⟨126197, by rfl⟩) R252395
theorem R269183 : Reach 269183 := rs (se 1 (by rfl) ⟨201887, by rfl⟩) R403775
theorem R40211 : Reach 40211 := rs (se 1 (by rfl) ⟨30158, by rfl⟩) R60317
theorem R171305 : Reach 171305 := rs (se 2 (by rfl) ⟨64239, by rfl⟩) R128479
theorem R40265 : Reach 40265 := rs (se 2 (by rfl) ⟨15099, by rfl⟩) R30199
theorem R40601 : Reach 40601 := rs (se 2 (by rfl) ⟨15225, by rfl⟩) R30451
theorem R40841 : Reach 40841 := rs (se 2 (by rfl) ⟨15315, by rfl⟩) R30631
theorem R1417175 : Reach 1417175 := rs (se 1 (by rfl) ⟨1062881, by rfl⟩) R2125763
theorem R139421 : Reach 139421 := rs (se 3 (by rfl) ⟨26141, by rfl⟩) R52283
theorem R73979 : Reach 73979 := rs (se 1 (by rfl) ⟨55484, by rfl⟩) R110969
theorem R106913 : Reach 106913 := rs (se 2 (by rfl) ⟨40092, by rfl⟩) R80185
theorem R205519 : Reach 205519 := rs (se 1 (by rfl) ⟨154139, by rfl⟩) R308279
theorem R369521 : Reach 369521 := rs (se 2 (by rfl) ⟨138570, by rfl⟩) R277141
theorem R74719 : Reach 74719 := rs (se 1 (by rfl) ⟨56039, by rfl⟩) R112079
theorem R2073869 : Reach 2073869 := rs (se 3 (by rfl) ⟨388850, by rfl⟩) R777701
theorem R141223 : Reach 141223 := rs (se 1 (by rfl) ⟨105917, by rfl⟩) R211835
theorem R108863 : Reach 108863 := rs (se 1 (by rfl) ⟨81647, by rfl⟩) R163295
theorem R1551251 : Reach 1551251 := rs (se 1 (by rfl) ⟨1163438, by rfl⟩) R2326877
theorem R44023 : Reach 44023 := rs (se 1 (by rfl) ⟨33017, by rfl⟩) R66035
theorem R44059 : Reach 44059 := rs (se 1 (by rfl) ⟨33044, by rfl⟩) R66089
theorem R77759 : Reach 77759 := rs (se 1 (by rfl) ⟨58319, by rfl⟩) R116639
theorem R78245 : Reach 78245 := rs (se 4 (by rfl) ⟨7335, by rfl⟩) R14671
theorem R13055 : Reach 13055 := rs (se 1 (by rfl) ⟨9791, by rfl⟩) R19583
theorem R14079 : Reach 14079 := rs (se 1 (by rfl) ⟨10559, by rfl⟩) R21119
theorem R79643 : Reach 79643 := rs (se 1 (by rfl) ⟨59732, by rfl⟩) R119465
theorem R14191 : Reach 14191 := rs (se 1 (by rfl) ⟨10643, by rfl⟩) R21287
theorem R14367 : Reach 14367 := rs (se 1 (by rfl) ⟨10775, by rfl⟩) R21551
theorem R112859 : Reach 112859 := rs (se 1 (by rfl) ⟨84644, by rfl⟩) R169289
theorem R14575 : Reach 14575 := rs (se 1 (by rfl) ⟨10931, by rfl⟩) R21863
theorem R14619 : Reach 14619 := rs (se 1 (by rfl) ⟨10964, by rfl⟩) R21929
theorem R14663 : Reach 14663 := rs (se 1 (by rfl) ⟨10997, by rfl⟩) R21995
theorem R15003 : Reach 15003 := rs (se 1 (by rfl) ⟨11252, by rfl⟩) R22505
theorem R15067 : Reach 15067 := rs (se 1 (by rfl) ⟨11300, by rfl⟩) R22601
theorem R15327 : Reach 15327 := rs (se 1 (by rfl) ⟨11495, by rfl⟩) R22991
theorem R15463 : Reach 15463 := rs (se 1 (by rfl) ⟨11597, by rfl⟩) R23195
theorem R15535 : Reach 15535 := rs (se 1 (by rfl) ⟨11651, by rfl⟩) R23303
theorem R1785311 : Reach 1785311 := rs (se 1 (by rfl) ⟨1338983, by rfl⟩) R2677967
theorem R15855 : Reach 15855 := rs (se 1 (by rfl) ⟨11891, by rfl⟩) R23783
theorem R16111 : Reach 16111 := rs (se 1 (by rfl) ⟨12083, by rfl⟩) R24167
theorem R49247 : Reach 49247 := rs (se 1 (by rfl) ⟨36935, by rfl⟩) R73871
theorem R16607 : Reach 16607 := rs (se 1 (by rfl) ⟨12455, by rfl⟩) R24911
theorem R17051 : Reach 17051 := rs (se 1 (by rfl) ⟨12788, by rfl⟩) R25577
theorem R17385 : Reach 17385 := rs (se 2 (by rfl) ⟨6519, by rfl⟩) R13039
theorem R17719 : Reach 17719 := rs (se 1 (by rfl) ⟨13289, by rfl⟩) R26579
theorem R17791 : Reach 17791 := rs (se 1 (by rfl) ⟨13343, by rfl⟩) R26687
theorem R378283 : Reach 378283 := rs (se 1 (by rfl) ⟨283712, by rfl⟩) R567425
theorem R18279 : Reach 18279 := rs (se 1 (by rfl) ⟨13709, by rfl⟩) R27419
theorem R18651 : Reach 18651 := rs (se 1 (by rfl) ⟨13988, by rfl⟩) R27977
theorem R18927 : Reach 18927 := rs (se 1 (by rfl) ⟨14195, by rfl⟩) R28391
theorem R19175 : Reach 19175 := rs (se 1 (by rfl) ⟨14381, by rfl⟩) R28763
theorem R19323 : Reach 19323 := rs (se 1 (by rfl) ⟨14492, by rfl⟩) R28985
theorem R19391 : Reach 19391 := rs (se 1 (by rfl) ⟨14543, by rfl⟩) R29087
theorem R248771 : Reach 248771 := rs (se 1 (by rfl) ⟨186578, by rfl⟩) R373157
theorem R19561 : Reach 19561 := rs (se 2 (by rfl) ⟨7335, by rfl⟩) R14671
theorem R19647 : Reach 19647 := rs (se 1 (by rfl) ⟨14735, by rfl⟩) R29471
theorem R413099 : Reach 413099 := rs (se 1 (by rfl) ⟨309824, by rfl⟩) R619649
theorem R19951 : Reach 19951 := rs (se 1 (by rfl) ⟨14963, by rfl⟩) R29927
theorem R19967 : Reach 19967 := rs (se 1 (by rfl) ⟨14975, by rfl⟩) R29951
theorem R20105 : Reach 20105 := rs (se 2 (by rfl) ⟨7539, by rfl⟩) R15079
theorem R52895 : Reach 52895 := rs (se 1 (by rfl) ⟨39671, by rfl⟩) R79343
theorem R708587 : Reach 708587 := rs (se 1 (by rfl) ⟨531440, by rfl⟩) R1062881
theorem R217241 : Reach 217241 := rs (se 2 (by rfl) ⟨81465, by rfl⟩) R162931
theorem R53999 : Reach 53999 := rs (se 1 (by rfl) ⟨40499, by rfl⟩) R80999
theorem R250651 : Reach 250651 := rs (se 1 (by rfl) ⟨187988, by rfl⟩) R375977
theorem R152543 : Reach 152543 := rs (se 1 (by rfl) ⟨114407, by rfl⟩) R228815
theorem R54431 : Reach 54431 := rs (se 1 (by rfl) ⟨40823, by rfl⟩) R81647
theorem R349373 : Reach 349373 := rs (se 3 (by rfl) ⟨65507, by rfl⟩) R131015
theorem R87641 : Reach 87641 := rs (se 2 (by rfl) ⟨32865, by rfl⟩) R65731
theorem R22631 : Reach 22631 := rs (se 1 (by rfl) ⟨16973, by rfl⟩) R33947
theorem R120943 : Reach 120943 := rs (se 1 (by rfl) ⟨90707, by rfl⟩) R181415
theorem R22855 : Reach 22855 := rs (se 1 (by rfl) ⟨17141, by rfl⟩) R34283
theorem R55849 : Reach 55849 := rs (se 2 (by rfl) ⟨20943, by rfl⟩) R41887
theorem R23095 : Reach 23095 := rs (se 1 (by rfl) ⟨17321, by rfl⟩) R34643
theorem R23291 : Reach 23291 := rs (se 1 (by rfl) ⟨17468, by rfl⟩) R34937
theorem R23855 : Reach 23855 := rs (se 1 (by rfl) ⟨17891, by rfl⟩) R35783
theorem R56801 : Reach 56801 := rs (se 2 (by rfl) ⟨21300, by rfl⟩) R42601
theorem R253691 : Reach 253691 := rs (se 1 (by rfl) ⟨190268, by rfl⟩) R380537
theorem R24359 : Reach 24359 := rs (se 1 (by rfl) ⟨18269, by rfl⟩) R36539
theorem R155519 : Reach 155519 := rs (se 1 (by rfl) ⟨116639, by rfl⟩) R233279
theorem R24623 : Reach 24623 := rs (se 1 (by rfl) ⟨18467, by rfl⟩) R36935
theorem R57469 : Reach 57469 := rs (se 3 (by rfl) ⟨10775, by rfl⟩) R21551
theorem R24713 : Reach 24713 := rs (se 2 (by rfl) ⟨9267, by rfl⟩) R18535
theorem R25471 : Reach 25471 := rs (se 1 (by rfl) ⟨19103, by rfl⟩) R38207
theorem R26111 : Reach 26111 := rs (se 1 (by rfl) ⟨19583, by rfl⟩) R39167
theorem R27035 : Reach 27035 := rs (se 1 (by rfl) ⟨20276, by rfl⟩) R40553
theorem R27391 : Reach 27391 := rs (se 1 (by rfl) ⟨20543, by rfl⟩) R41087
theorem R60223 : Reach 60223 := rs (se 1 (by rfl) ⟨45167, by rfl⟩) R90335
theorem R60371 : Reach 60371 := rs (se 1 (by rfl) ⟨45278, by rfl⟩) R90557
theorem R28271 : Reach 28271 := rs (se 1 (by rfl) ⟨21203, by rfl⟩) R42407
theorem R126845 : Reach 126845 := rs (se 3 (by rfl) ⟨23783, by rfl⟩) R47567
theorem R1274291 : Reach 1274291 := rs (se 1 (by rfl) ⟨955718, by rfl⟩) R1911437
theorem R61883 : Reach 61883 := rs (se 1 (by rfl) ⟨46412, by rfl⟩) R92825
theorem R29327 : Reach 29327 := rs (se 1 (by rfl) ⟨21995, by rfl⟩) R43991
theorem R62147 : Reach 62147 := rs (se 1 (by rfl) ⟨46610, by rfl⟩) R93221
theorem R62633 : Reach 62633 := rs (se 2 (by rfl) ⟨23487, by rfl⟩) R46975
theorem R62801 : Reach 62801 := rs (se 2 (by rfl) ⟨23550, by rfl⟩) R47101
theorem R30185 : Reach 30185 := rs (se 2 (by rfl) ⟨11319, by rfl⟩) R22639
theorem R30503 : Reach 30503 := rs (se 1 (by rfl) ⟨22877, by rfl⟩) R45755
theorem R424187 : Reach 424187 := rs (se 1 (by rfl) ⟨318140, by rfl⟩) R636281
theorem R31625 : Reach 31625 := rs (se 2 (by rfl) ⟨11859, by rfl⟩) R23719
theorem R31711 : Reach 31711 := rs (se 1 (by rfl) ⟨23783, by rfl⟩) R47567
theorem R65015 : Reach 65015 := rs (se 1 (by rfl) ⟨48761, by rfl⟩) R97523
theorem R65177 : Reach 65177 := rs (se 2 (by rfl) ⟨24441, by rfl⟩) R48883
theorem R32507 : Reach 32507 := rs (se 1 (by rfl) ⟨24380, by rfl⟩) R48761
theorem R32831 : Reach 32831 := rs (se 1 (by rfl) ⟨24623, by rfl⟩) R49247
theorem R99625 : Reach 99625 := rs (se 2 (by rfl) ⟨37359, by rfl⟩) R74719
theorem R165725 : Reach 165725 := rs (se 3 (by rfl) ⟨31073, by rfl⟩) R62147
theorem R165847 : Reach 165847 := rs (se 1 (by rfl) ⟨124385, by rfl⟩) R248771
theorem R35263 : Reach 35263 := rs (se 1 (by rfl) ⟨26447, by rfl⟩) R52895
theorem R35999 : Reach 35999 := rs (se 1 (by rfl) ⟨26999, by rfl⟩) R53999
theorem R101695 : Reach 101695 := rs (se 1 (by rfl) ⟨76271, by rfl⟩) R152543
theorem R36287 : Reach 36287 := rs (se 1 (by rfl) ⟨27215, by rfl⟩) R54431
theorem R232915 : Reach 232915 := rs (se 1 (by rfl) ⟨174686, by rfl⟩) R349373
theorem R36521 : Reach 36521 := rs (se 2 (by rfl) ⟨13695, by rfl⟩) R27391
theorem R135845 : Reach 135845 := rs (se 4 (by rfl) ⟨12735, by rfl⟩) R25471
theorem R37867 : Reach 37867 := rs (se 1 (by rfl) ⟨28400, by rfl⟩) R56801
theorem R169127 : Reach 169127 := rs (se 1 (by rfl) ⟨126845, by rfl⟩) R253691
theorem R103679 : Reach 103679 := rs (se 1 (by rfl) ⟨77759, by rfl⟩) R155519
theorem R71275 : Reach 71275 := rs (se 1 (by rfl) ⟨53456, by rfl⟩) R106913
theorem R1382579 : Reach 1382579 := rs (se 1 (by rfl) ⟨1036934, by rfl⟩) R2073869
theorem R334201 : Reach 334201 := rs (se 2 (by rfl) ⟨125325, by rfl⟩) R250651
theorem R72575 : Reach 72575 := rs (se 1 (by rfl) ⟨54431, by rfl⟩) R108863
theorem R40247 : Reach 40247 := rs (se 1 (by rfl) ⟨30185, by rfl⟩) R60371
theorem R41255 : Reach 41255 := rs (se 1 (by rfl) ⟨30941, by rfl⟩) R61883
theorem R41431 : Reach 41431 := rs (se 1 (by rfl) ⟨31073, by rfl⟩) R62147
theorem R74465 : Reach 74465 := rs (se 2 (by rfl) ⟨27924, by rfl⟩) R55849
theorem R41755 : Reach 41755 := rs (se 1 (by rfl) ⟨31316, by rfl⟩) R62633
theorem R41867 : Reach 41867 := rs (se 1 (by rfl) ⟨31400, by rfl⟩) R62801
theorem R42281 : Reach 42281 := rs (se 2 (by rfl) ⟨15855, by rfl⟩) R31711
theorem R75239 : Reach 75239 := rs (se 1 (by rfl) ⟨56429, by rfl⟩) R112859
theorem R1190207 : Reach 1190207 := rs (se 1 (by rfl) ⟨892655, by rfl⟩) R1785311
theorem R43343 : Reach 43343 := rs (se 1 (by rfl) ⟨32507, by rfl⟩) R65015
theorem R43451 : Reach 43451 := rs (se 1 (by rfl) ⟨32588, by rfl⟩) R65177
theorem R43739 : Reach 43739 := rs (se 1 (by rfl) ⟨32804, by rfl⟩) R65609
theorem R43775 : Reach 43775 := rs (se 1 (by rfl) ⟨32831, by rfl⟩) R65663
theorem R76625 : Reach 76625 := rs (se 2 (by rfl) ⟨28734, by rfl⟩) R57469
theorem R44351 : Reach 44351 := rs (se 1 (by rfl) ⟨33263, by rfl⟩) R66527
theorem R44459 : Reach 44459 := rs (se 1 (by rfl) ⟨33344, by rfl⟩) R66689
theorem R274025 : Reach 274025 := rs (se 2 (by rfl) ⟨102759, by rfl⟩) R205519
theorem R504377 : Reach 504377 := rs (se 2 (by rfl) ⟨189141, by rfl⟩) R378283
theorem R12927 : Reach 12927 := rs (se 1 (by rfl) ⟨9695, by rfl⟩) R19391
theorem R45967 : Reach 45967 := rs (se 1 (by rfl) ⟨34475, by rfl⟩) R68951
theorem R275399 : Reach 275399 := rs (se 1 (by rfl) ⟨206549, by rfl⟩) R413099
theorem R13311 : Reach 13311 := rs (se 1 (by rfl) ⟨9983, by rfl⟩) R19967
theorem R13403 : Reach 13403 := rs (se 1 (by rfl) ⟨10052, by rfl⟩) R20105
theorem R406781 : Reach 406781 := rs (se 3 (by rfl) ⟨76271, by rfl⟩) R152543
theorem R472391 : Reach 472391 := rs (se 1 (by rfl) ⟨354293, by rfl⟩) R708587
theorem R144827 : Reach 144827 := rs (se 1 (by rfl) ⟨108620, by rfl⟩) R217241
theorem R112103 : Reach 112103 := rs (se 1 (by rfl) ⟨84077, by rfl⟩) R168155
theorem R112175 : Reach 112175 := rs (se 1 (by rfl) ⟨84131, by rfl⟩) R168263
theorem R80297 : Reach 80297 := rs (se 2 (by rfl) ⟨30111, by rfl⟩) R60223
theorem R15087 : Reach 15087 := rs (se 1 (by rfl) ⟨11315, by rfl⟩) R22631
theorem R15527 : Reach 15527 := rs (se 1 (by rfl) ⟨11645, by rfl⟩) R23291
theorem R179455 : Reach 179455 := rs (se 1 (by rfl) ⟨134591, by rfl⟩) R269183
theorem R114203 : Reach 114203 := rs (se 1 (by rfl) ⟨85652, by rfl⟩) R171305
theorem R15903 : Reach 15903 := rs (se 1 (by rfl) ⟨11927, by rfl⟩) R23855
theorem R16239 : Reach 16239 := rs (se 1 (by rfl) ⟨12179, by rfl⟩) R24359
theorem R16415 : Reach 16415 := rs (se 1 (by rfl) ⟨12311, by rfl⟩) R24623
theorem R16475 : Reach 16475 := rs (se 1 (by rfl) ⟨12356, by rfl⟩) R24713
theorem R49319 : Reach 49319 := rs (se 1 (by rfl) ⟨36989, by rfl⟩) R73979
theorem R246347 : Reach 246347 := rs (se 1 (by rfl) ⟨184760, by rfl⟩) R369521
theorem R17407 : Reach 17407 := rs (se 1 (by rfl) ⟨13055, by rfl⟩) R26111
theorem R18023 : Reach 18023 := rs (se 1 (by rfl) ⟨13517, by rfl⟩) R27035
theorem R1034167 : Reach 1034167 := rs (se 1 (by rfl) ⟨775625, by rfl⟩) R1551251
theorem R18847 : Reach 18847 := rs (se 1 (by rfl) ⟨14135, by rfl⟩) R28271
theorem R18921 : Reach 18921 := rs (se 2 (by rfl) ⟨7095, by rfl⟩) R14191
theorem R84563 : Reach 84563 := rs (se 1 (by rfl) ⟨63422, by rfl⟩) R126845
theorem R51839 : Reach 51839 := rs (se 1 (by rfl) ⟨38879, by rfl⟩) R77759
theorem R52163 : Reach 52163 := rs (se 1 (by rfl) ⟨39122, by rfl⟩) R78245
theorem R19433 : Reach 19433 := rs (se 2 (by rfl) ⟨7287, by rfl⟩) R14575
theorem R19551 : Reach 19551 := rs (se 1 (by rfl) ⟨14663, by rfl⟩) R29327
theorem R20123 : Reach 20123 := rs (se 1 (by rfl) ⟨15092, by rfl⟩) R30185
theorem R53095 : Reach 53095 := rs (se 1 (by rfl) ⟨39821, by rfl⟩) R79643
theorem R20335 : Reach 20335 := rs (se 1 (by rfl) ⟨15251, by rfl⟩) R30503
theorem R282791 : Reach 282791 := rs (se 1 (by rfl) ⟨212093, by rfl⟩) R424187
theorem R20713 : Reach 20713 := rs (se 2 (by rfl) ⟨7767, by rfl⟩) R15535
theorem R21083 : Reach 21083 := rs (se 1 (by rfl) ⟨15812, by rfl⟩) R31625
theorem R21671 : Reach 21671 := rs (se 1 (by rfl) ⟨16253, by rfl⟩) R32507
theorem R87479 : Reach 87479 := rs (se 1 (by rfl) ⟨65609, by rfl⟩) R131219
theorem R22175 : Reach 22175 := rs (se 1 (by rfl) ⟨16631, by rfl⟩) R33263
theorem R645029 : Reach 645029 := rs (se 4 (by rfl) ⟨60471, by rfl⟩) R120943
theorem R22523 : Reach 22523 := rs (se 1 (by rfl) ⟨16892, by rfl⟩) R33785
theorem R88289 : Reach 88289 := rs (se 2 (by rfl) ⟨33108, by rfl⟩) R66217
theorem R23579 : Reach 23579 := rs (se 1 (by rfl) ⟨17684, by rfl⟩) R35369
theorem R24095 : Reach 24095 := rs (se 1 (by rfl) ⟨18071, by rfl⟩) R36143
theorem R188297 : Reach 188297 := rs (se 2 (by rfl) ⟨70611, by rfl⟩) R141223
theorem R58427 : Reach 58427 := rs (se 1 (by rfl) ⟨43820, by rfl⟩) R87641
theorem R58697 : Reach 58697 := rs (se 2 (by rfl) ⟨22011, by rfl⟩) R44023
theorem R58745 : Reach 58745 := rs (se 2 (by rfl) ⟨22029, by rfl⟩) R44059
theorem R26081 : Reach 26081 := rs (se 2 (by rfl) ⟨9780, by rfl⟩) R19561
theorem R26807 : Reach 26807 := rs (se 1 (by rfl) ⟨20105, by rfl⟩) R40211
theorem R26843 : Reach 26843 := rs (se 1 (by rfl) ⟨20132, by rfl⟩) R40265
theorem R27067 : Reach 27067 := rs (se 1 (by rfl) ⟨20300, by rfl⟩) R40601
theorem R27227 : Reach 27227 := rs (se 1 (by rfl) ⟨20420, by rfl⟩) R40841
theorem R944783 : Reach 944783 := rs (se 1 (by rfl) ⟨708587, by rfl⟩) R1417175
theorem R92947 : Reach 92947 := rs (se 1 (by rfl) ⟨69710, by rfl⟩) R139421
theorem R849527 : Reach 849527 := rs (se 1 (by rfl) ⟨637145, by rfl⟩) R1274291
theorem R30473 : Reach 30473 := rs (se 2 (by rfl) ⟨11427, by rfl⟩) R22855
theorem R30793 : Reach 30793 := rs (se 2 (by rfl) ⟨11547, by rfl⟩) R23095
theorem R32879 : Reach 32879 := rs (se 1 (by rfl) ⟨24659, by rfl⟩) R49319
theorem R164231 : Reach 164231 := rs (se 1 (by rfl) ⟨123173, by rfl⟩) R246347
theorem R132833 : Reach 132833 := rs (se 2 (by rfl) ⟨49812, by rfl⟩) R99625
theorem R34559 : Reach 34559 := rs (se 1 (by rfl) ⟨25919, by rfl⟩) R51839
theorem R34775 : Reach 34775 := rs (se 1 (by rfl) ⟨26081, by rfl⟩) R52163
theorem R1378889 : Reach 1378889 := rs (se 2 (by rfl) ⟨517083, by rfl⟩) R1034167
theorem R35741 : Reach 35741 := rs (se 3 (by rfl) ⟨6701, by rfl⟩) R13403
theorem R36089 : Reach 36089 := rs (se 2 (by rfl) ⟨13533, by rfl⟩) R27067
theorem R69119 : Reach 69119 := rs (se 1 (by rfl) ⟨51839, by rfl⟩) R103679
theorem R430019 : Reach 430019 := rs (se 1 (by rfl) ⟨322514, by rfl⟩) R645029
theorem R921719 : Reach 921719 := rs (se 1 (by rfl) ⟨691289, by rfl⟩) R1382579
theorem R135593 : Reach 135593 := rs (se 2 (by rfl) ⟨50847, by rfl⟩) R101695
theorem R70793 : Reach 70793 := rs (se 2 (by rfl) ⟨26547, by rfl⟩) R53095
theorem R38951 : Reach 38951 := rs (se 1 (by rfl) ⟨29213, by rfl⟩) R58427
theorem R39131 : Reach 39131 := rs (se 1 (by rfl) ⟨29348, by rfl⟩) R58697
theorem R39163 : Reach 39163 := rs (se 1 (by rfl) ⟨29372, by rfl⟩) R58745
theorem R793471 : Reach 793471 := rs (se 1 (by rfl) ⟨595103, by rfl⟩) R1190207
theorem R629855 : Reach 629855 := rs (se 1 (by rfl) ⟨472391, by rfl⟩) R944783
theorem R41057 : Reach 41057 := rs (se 2 (by rfl) ⟨15396, by rfl⟩) R30793
theorem R336251 : Reach 336251 := rs (se 1 (by rfl) ⟨252188, by rfl⟩) R504377
theorem R271187 : Reach 271187 := rs (se 1 (by rfl) ⟨203390, by rfl⟩) R406781
theorem R74735 : Reach 74735 := rs (se 1 (by rfl) ⟨56051, by rfl⟩) R112103
theorem R74783 : Reach 74783 := rs (se 1 (by rfl) ⟨56087, by rfl⟩) R112175
theorem R566351 : Reach 566351 := rs (se 1 (by rfl) ⟨424763, by rfl⟩) R849527
theorem R239273 : Reach 239273 := rs (se 2 (by rfl) ⟨89727, by rfl⟩) R179455
theorem R76135 : Reach 76135 := rs (se 1 (by rfl) ⟨57101, by rfl⟩) R114203
theorem R110483 : Reach 110483 := rs (se 1 (by rfl) ⟨82862, by rfl⟩) R165725
theorem R12955 : Reach 12955 := rs (se 1 (by rfl) ⟨9716, by rfl⟩) R19433
theorem R13415 : Reach 13415 := rs (se 1 (by rfl) ⟨10061, by rfl⟩) R20123
theorem R14055 : Reach 14055 := rs (se 1 (by rfl) ⟨10541, by rfl⟩) R21083
theorem R47017 : Reach 47017 := rs (se 2 (by rfl) ⟨17631, by rfl⟩) R35263
theorem R14447 : Reach 14447 := rs (se 1 (by rfl) ⟨10835, by rfl⟩) R21671
theorem R112751 : Reach 112751 := rs (se 1 (by rfl) ⟨84563, by rfl⟩) R169127
theorem R14783 : Reach 14783 := rs (se 1 (by rfl) ⟨11087, by rfl⟩) R22175
theorem R15015 : Reach 15015 := rs (se 1 (by rfl) ⟨11261, by rfl⟩) R22523
theorem R48383 : Reach 48383 := rs (se 1 (by rfl) ⟨36287, by rfl⟩) R72575
theorem R310553 : Reach 310553 := rs (se 2 (by rfl) ⟨116457, by rfl⟩) R232915
theorem R15719 : Reach 15719 := rs (se 1 (by rfl) ⟨11789, by rfl⟩) R23579
theorem R16063 : Reach 16063 := rs (se 1 (by rfl) ⟨12047, by rfl⟩) R24095
theorem R49643 : Reach 49643 := rs (se 1 (by rfl) ⟨37232, by rfl⟩) R74465
theorem R17387 : Reach 17387 := rs (se 1 (by rfl) ⟨13040, by rfl⟩) R26081
theorem R50159 : Reach 50159 := rs (se 1 (by rfl) ⟨37619, by rfl⟩) R75239
theorem R50489 : Reach 50489 := rs (se 2 (by rfl) ⟨18933, by rfl⟩) R37867
theorem R17871 : Reach 17871 := rs (se 1 (by rfl) ⟨13403, by rfl⟩) R26807
theorem R17895 : Reach 17895 := rs (se 1 (by rfl) ⟨13421, by rfl⟩) R26843
theorem R18151 : Reach 18151 := rs (se 1 (by rfl) ⟨13613, by rfl⟩) R27227
theorem R51083 : Reach 51083 := rs (se 1 (by rfl) ⟨38312, by rfl⟩) R76625
theorem R182683 : Reach 182683 := rs (se 1 (by rfl) ⟨137012, by rfl⟩) R274025
theorem R445601 : Reach 445601 := rs (se 2 (by rfl) ⟨167100, by rfl⟩) R334201
theorem R183599 : Reach 183599 := rs (se 1 (by rfl) ⟨137699, by rfl⟩) R275399
theorem R314927 : Reach 314927 := rs (se 1 (by rfl) ⟨236195, by rfl⟩) R472391
theorem R20315 : Reach 20315 := rs (se 1 (by rfl) ⟨15236, by rfl⟩) R30473
theorem R53531 : Reach 53531 := rs (se 1 (by rfl) ⟨40148, by rfl⟩) R80297
theorem R21887 : Reach 21887 := rs (se 1 (by rfl) ⟨16415, by rfl⟩) R32831
theorem R55241 : Reach 55241 := rs (se 2 (by rfl) ⟨20715, by rfl⟩) R41431
theorem R55673 : Reach 55673 := rs (se 2 (by rfl) ⟨20877, by rfl⟩) R41755
theorem R56375 : Reach 56375 := rs (se 1 (by rfl) ⟨42281, by rfl⟩) R84563
theorem R23999 : Reach 23999 := rs (se 1 (by rfl) ⟨17999, by rfl⟩) R35999
theorem R24191 : Reach 24191 := rs (se 1 (by rfl) ⟨18143, by rfl⟩) R36287
theorem R24347 : Reach 24347 := rs (se 1 (by rfl) ⟨18260, by rfl⟩) R36521
theorem R221129 : Reach 221129 := rs (se 2 (by rfl) ⟨82923, by rfl⟩) R165847
theorem R188527 : Reach 188527 := rs (se 1 (by rfl) ⟨141395, by rfl⟩) R282791
theorem R90563 : Reach 90563 := rs (se 1 (by rfl) ⟨67922, by rfl⟩) R135845
theorem R58319 : Reach 58319 := rs (se 1 (by rfl) ⟨43739, by rfl⟩) R87479
theorem R156653 : Reach 156653 := rs (se 3 (by rfl) ⟨29372, by rfl⟩) R58745
theorem R123929 : Reach 123929 := rs (se 2 (by rfl) ⟨46473, by rfl⟩) R92947
theorem R58859 : Reach 58859 := rs (se 1 (by rfl) ⟨44144, by rfl⟩) R88289
theorem R26831 : Reach 26831 := rs (se 1 (by rfl) ⟨20123, by rfl⟩) R40247
theorem R27113 : Reach 27113 := rs (se 2 (by rfl) ⟨10167, by rfl⟩) R20335
theorem R125531 : Reach 125531 := rs (se 1 (by rfl) ⟨94148, by rfl⟩) R188297
theorem R27503 : Reach 27503 := rs (se 1 (by rfl) ⟨20627, by rfl⟩) R41255
theorem R27617 : Reach 27617 := rs (se 2 (by rfl) ⟨10356, by rfl⟩) R20713
theorem R27911 : Reach 27911 := rs (se 1 (by rfl) ⟨20933, by rfl⟩) R41867
theorem R28187 : Reach 28187 := rs (se 1 (by rfl) ⟨21140, by rfl⟩) R42281
theorem R61289 : Reach 61289 := rs (se 2 (by rfl) ⟨22983, by rfl⟩) R45967
theorem R28895 : Reach 28895 := rs (se 1 (by rfl) ⟨21671, by rfl⟩) R43343
theorem R28967 : Reach 28967 := rs (se 1 (by rfl) ⟨21725, by rfl⟩) R43451
theorem R29159 : Reach 29159 := rs (se 1 (by rfl) ⟨21869, by rfl⟩) R43739
theorem R29183 : Reach 29183 := rs (se 1 (by rfl) ⟨21887, by rfl⟩) R43775
theorem R95033 : Reach 95033 := rs (se 2 (by rfl) ⟨35637, by rfl⟩) R71275
theorem R29567 : Reach 29567 := rs (se 1 (by rfl) ⟨22175, by rfl⟩) R44351
theorem R29639 : Reach 29639 := rs (se 1 (by rfl) ⟨22229, by rfl⟩) R44459
theorem R96551 : Reach 96551 := rs (se 1 (by rfl) ⟨72413, by rfl⟩) R144827
theorem R33095 : Reach 33095 := rs (se 1 (by rfl) ⟨24821, by rfl⟩) R49643
theorem R33439 : Reach 33439 := rs (se 1 (by rfl) ⟨25079, by rfl⟩) R50159
theorem R33659 : Reach 33659 := rs (se 1 (by rfl) ⟨25244, by rfl⟩) R50489
theorem R34055 : Reach 34055 := rs (se 1 (by rfl) ⟨25541, by rfl⟩) R51083
theorem R919259 : Reach 919259 := rs (se 1 (by rfl) ⟨689444, by rfl⟩) R1378889
theorem R297067 : Reach 297067 := rs (se 1 (by rfl) ⟨222800, by rfl⟩) R445601
theorem R35687 : Reach 35687 := rs (se 1 (by rfl) ⟨26765, by rfl⟩) R53531
theorem R101513 : Reach 101513 := rs (se 2 (by rfl) ⟨38067, by rfl⟩) R76135
theorem R167669 : Reach 167669 := rs (se 5 (by rfl) ⟨7859, by rfl⟩) R15719
theorem R36827 : Reach 36827 := rs (se 1 (by rfl) ⟨27620, by rfl⟩) R55241
theorem R37115 : Reach 37115 := rs (se 1 (by rfl) ⟨27836, by rfl⟩) R55673
theorem R37583 : Reach 37583 := rs (se 1 (by rfl) ⟨28187, by rfl⟩) R56375
theorem R71549 : Reach 71549 := rs (se 3 (by rfl) ⟨13415, by rfl⟩) R26831
theorem R38879 : Reach 38879 := rs (se 1 (by rfl) ⟨29159, by rfl⟩) R58319
theorem R104435 : Reach 104435 := rs (se 1 (by rfl) ⟨78326, by rfl⟩) R156653
theorem R39239 : Reach 39239 := rs (se 1 (by rfl) ⟨29429, by rfl⟩) R58859
theorem R40859 : Reach 40859 := rs (se 1 (by rfl) ⟨30644, by rfl⟩) R61289
theorem R73655 : Reach 73655 := rs (se 1 (by rfl) ⟨55241, by rfl⟩) R110483
theorem R41917 : Reach 41917 := rs (se 3 (by rfl) ⟨7859, by rfl⟩) R15719
theorem R1057961 : Reach 1057961 := rs (se 2 (by rfl) ⟨396735, by rfl⟩) R793471
theorem R75167 : Reach 75167 := rs (se 1 (by rfl) ⟨56375, by rfl⟩) R112751
theorem R207035 : Reach 207035 := rs (se 1 (by rfl) ⟨155276, by rfl⟩) R310553
theorem R109487 : Reach 109487 := rs (se 1 (by rfl) ⟨82115, by rfl⟩) R164231
theorem R241501 : Reach 241501 := rs (se 3 (by rfl) ⟨45281, by rfl⟩) R90563
theorem R46079 : Reach 46079 := rs (se 1 (by rfl) ⟨34559, by rfl⟩) R69119
theorem R209951 : Reach 209951 := rs (se 1 (by rfl) ⟨157463, by rfl⟩) R314927
theorem R13543 : Reach 13543 := rs (se 1 (by rfl) ⟨10157, by rfl⟩) R20315
theorem R243577 : Reach 243577 := rs (se 2 (by rfl) ⟨91341, by rfl⟩) R182683
theorem R47195 : Reach 47195 := rs (se 1 (by rfl) ⟨35396, by rfl⟩) R70793
theorem R14591 : Reach 14591 := rs (se 1 (by rfl) ⟨10943, by rfl⟩) R21887
theorem R15999 : Reach 15999 := rs (se 1 (by rfl) ⟨11999, by rfl⟩) R23999
theorem R16127 : Reach 16127 := rs (se 1 (by rfl) ⟨12095, by rfl⟩) R24191
theorem R16231 : Reach 16231 := rs (se 1 (by rfl) ⟨12173, by rfl⟩) R24347
theorem R147419 : Reach 147419 := rs (se 1 (by rfl) ⟨110564, by rfl⟩) R221129
theorem R180791 : Reach 180791 := rs (se 1 (by rfl) ⟨135593, by rfl⟩) R271187
theorem R49823 : Reach 49823 := rs (se 1 (by rfl) ⟨37367, by rfl⟩) R74735
theorem R82619 : Reach 82619 := rs (se 1 (by rfl) ⟨61964, by rfl⟩) R123929
theorem R49855 : Reach 49855 := rs (se 1 (by rfl) ⟨37391, by rfl⟩) R74783
theorem R377567 : Reach 377567 := rs (se 1 (by rfl) ⟨283175, by rfl⟩) R566351
theorem R17273 : Reach 17273 := rs (se 2 (by rfl) ⟨6477, by rfl⟩) R12955
theorem R17887 : Reach 17887 := rs (se 1 (by rfl) ⟨13415, by rfl⟩) R26831
theorem R18075 : Reach 18075 := rs (se 1 (by rfl) ⟨13556, by rfl⟩) R27113
theorem R83687 : Reach 83687 := rs (se 1 (by rfl) ⟨62765, by rfl⟩) R125531
theorem R18335 : Reach 18335 := rs (se 1 (by rfl) ⟨13751, by rfl⟩) R27503
theorem R18411 : Reach 18411 := rs (se 1 (by rfl) ⟨13808, by rfl⟩) R27617
theorem R18607 : Reach 18607 := rs (se 1 (by rfl) ⟨13955, by rfl⟩) R27911
theorem R18791 : Reach 18791 := rs (se 1 (by rfl) ⟨14093, by rfl⟩) R28187
theorem R19263 : Reach 19263 := rs (se 1 (by rfl) ⟨14447, by rfl⟩) R28895
theorem R19311 : Reach 19311 := rs (se 1 (by rfl) ⟨14483, by rfl⟩) R28967
theorem R19439 : Reach 19439 := rs (se 1 (by rfl) ⟨14579, by rfl⟩) R29159
theorem R52217 : Reach 52217 := rs (se 2 (by rfl) ⟨19581, by rfl⟩) R39163
theorem R19455 : Reach 19455 := rs (se 1 (by rfl) ⟨14591, by rfl⟩) R29183
theorem R19711 : Reach 19711 := rs (se 1 (by rfl) ⟨14783, by rfl⟩) R29567
theorem R19759 : Reach 19759 := rs (se 1 (by rfl) ⟨14819, by rfl⟩) R29639
theorem R21919 : Reach 21919 := rs (se 1 (by rfl) ⟨16439, by rfl⟩) R32879
theorem R251369 : Reach 251369 := rs (se 2 (by rfl) ⟨94263, by rfl⟩) R188527
theorem R88555 : Reach 88555 := rs (se 1 (by rfl) ⟨66416, by rfl⟩) R132833
theorem R23039 : Reach 23039 := rs (se 1 (by rfl) ⟨17279, by rfl⟩) R34559
theorem R23183 : Reach 23183 := rs (se 1 (by rfl) ⟨17387, by rfl⟩) R34775
theorem R23827 : Reach 23827 := rs (se 1 (by rfl) ⟨17870, by rfl⟩) R35741
theorem R24059 : Reach 24059 := rs (se 1 (by rfl) ⟨18044, by rfl⟩) R36089
theorem R122399 : Reach 122399 := rs (se 1 (by rfl) ⟨91799, by rfl⟩) R183599
theorem R286679 : Reach 286679 := rs (se 1 (by rfl) ⟨215009, by rfl⟩) R430019
theorem R614479 : Reach 614479 := rs (se 1 (by rfl) ⟨460859, by rfl⟩) R921719
theorem R90395 : Reach 90395 := rs (se 1 (by rfl) ⟨67796, by rfl⟩) R135593
theorem R25967 : Reach 25967 := rs (se 1 (by rfl) ⟨19475, by rfl⟩) R38951
theorem R26087 : Reach 26087 := rs (se 1 (by rfl) ⟨19565, by rfl⟩) R39131
theorem R419903 : Reach 419903 := rs (se 1 (by rfl) ⟨314927, by rfl⟩) R629855
theorem R27371 : Reach 27371 := rs (se 1 (by rfl) ⟨20528, by rfl⟩) R41057
theorem R224167 : Reach 224167 := rs (se 1 (by rfl) ⟨168125, by rfl⟩) R336251
theorem R159515 : Reach 159515 := rs (se 1 (by rfl) ⟨119636, by rfl⟩) R239273
theorem R62689 : Reach 62689 := rs (se 2 (by rfl) ⟨23508, by rfl⟩) R47017
theorem R63355 : Reach 63355 := rs (se 1 (by rfl) ⟨47516, by rfl⟩) R95033
theorem R64367 : Reach 64367 := rs (se 1 (by rfl) ⟨48275, by rfl⟩) R96551
theorem R32255 : Reach 32255 := rs (se 1 (by rfl) ⟨24191, by rfl⟩) R48383
theorem R819305 : Reach 819305 := rs (se 2 (by rfl) ⟨307239, by rfl⟩) R614479
theorem R33215 : Reach 33215 := rs (se 1 (by rfl) ⟨24911, by rfl⟩) R49823
theorem R66473 : Reach 66473 := rs (se 2 (by rfl) ⟨24927, by rfl⟩) R49855
theorem R34811 : Reach 34811 := rs (se 1 (by rfl) ⟨26108, by rfl⟩) R52217
theorem R67675 : Reach 67675 := rs (se 1 (by rfl) ⟨50756, by rfl⟩) R101513
theorem R396089 : Reach 396089 := rs (se 2 (by rfl) ⟨148533, by rfl⟩) R297067
theorem R167579 : Reach 167579 := rs (se 1 (by rfl) ⟨125684, by rfl⟩) R251369
theorem R298889 : Reach 298889 := rs (se 2 (by rfl) ⟨112083, by rfl⟩) R224167
theorem R69623 : Reach 69623 := rs (se 1 (by rfl) ⟨52217, by rfl⟩) R104435
theorem R138023 : Reach 138023 := rs (se 1 (by rfl) ⟨103517, by rfl⟩) R207035
theorem R72991 : Reach 72991 := rs (se 1 (by rfl) ⟨54743, by rfl⟩) R109487
theorem R106343 : Reach 106343 := rs (se 1 (by rfl) ⟨79757, by rfl⟩) R159515
theorem R139967 : Reach 139967 := rs (se 1 (by rfl) ⟨104975, by rfl⟩) R209951
theorem R42911 : Reach 42911 := rs (se 1 (by rfl) ⟨32183, by rfl⟩) R64367
theorem R44585 : Reach 44585 := rs (se 2 (by rfl) ⟨16719, by rfl⟩) R33439
theorem R12959 : Reach 12959 := rs (se 1 (by rfl) ⟨9719, by rfl⟩) R19439
theorem R46061 : Reach 46061 := rs (se 3 (by rfl) ⟨8636, by rfl⟩) R17273
theorem R111779 : Reach 111779 := rs (se 1 (by rfl) ⟨83834, by rfl⟩) R167669
theorem R47699 : Reach 47699 := rs (se 1 (by rfl) ⟨35774, by rfl⟩) R71549
theorem R15359 : Reach 15359 := rs (se 1 (by rfl) ⟨11519, by rfl⟩) R23039
theorem R15455 : Reach 15455 := rs (se 1 (by rfl) ⟨11591, by rfl⟩) R23183
theorem R16039 : Reach 16039 := rs (se 1 (by rfl) ⟨12029, by rfl⟩) R24059
theorem R81599 : Reach 81599 := rs (se 1 (by rfl) ⟨61199, by rfl⟩) R122399
theorem R49103 : Reach 49103 := rs (se 1 (by rfl) ⟨36827, by rfl⟩) R73655
theorem R705307 : Reach 705307 := rs (se 1 (by rfl) ⟨528980, by rfl⟩) R1057961
theorem R17311 : Reach 17311 := rs (se 1 (by rfl) ⟨12983, by rfl⟩) R25967
theorem R50111 : Reach 50111 := rs (se 1 (by rfl) ⟨37583, by rfl⟩) R75167
theorem R17391 : Reach 17391 := rs (se 1 (by rfl) ⟨13043, by rfl⟩) R26087
theorem R279935 : Reach 279935 := rs (se 1 (by rfl) ⟨209951, by rfl⟩) R419903
theorem R83585 : Reach 83585 := rs (se 2 (by rfl) ⟨31344, by rfl⟩) R62689
theorem R18057 : Reach 18057 := rs (se 2 (by rfl) ⟨6771, by rfl⟩) R13543
theorem R18247 : Reach 18247 := rs (se 1 (by rfl) ⟨13685, by rfl⟩) R27371
theorem R84473 : Reach 84473 := rs (se 2 (by rfl) ⟨31677, by rfl⟩) R63355
theorem R118073 : Reach 118073 := rs (se 2 (by rfl) ⟨44277, by rfl⟩) R88555
theorem R21503 : Reach 21503 := rs (se 1 (by rfl) ⟨16127, by rfl⟩) R32255
theorem R21641 : Reach 21641 := rs (se 2 (by rfl) ⟨8115, by rfl⟩) R16231
theorem R22063 : Reach 22063 := rs (se 1 (by rfl) ⟨16547, by rfl⟩) R33095
theorem R120527 : Reach 120527 := rs (se 1 (by rfl) ⟨90395, by rfl⟩) R180791
theorem R55079 : Reach 55079 := rs (se 1 (by rfl) ⟨41309, by rfl⟩) R82619
theorem R251711 : Reach 251711 := rs (se 1 (by rfl) ⟨188783, by rfl⟩) R377567
theorem R22439 : Reach 22439 := rs (se 1 (by rfl) ⟨16829, by rfl⟩) R33659
theorem R22703 : Reach 22703 := rs (se 1 (by rfl) ⟨17027, by rfl⟩) R34055
theorem R612839 : Reach 612839 := rs (se 1 (by rfl) ⟨459629, by rfl⟩) R919259
theorem R55889 : Reach 55889 := rs (se 2 (by rfl) ⟨20958, by rfl⟩) R41917
theorem R23849 : Reach 23849 := rs (se 2 (by rfl) ⟨8943, by rfl⟩) R17887
theorem R24551 : Reach 24551 := rs (se 1 (by rfl) ⟨18413, by rfl⟩) R36827
theorem R24743 : Reach 24743 := rs (se 1 (by rfl) ⟨18557, by rfl⟩) R37115
theorem R24809 : Reach 24809 := rs (se 2 (by rfl) ⟨9303, by rfl⟩) R18607
theorem R25055 : Reach 25055 := rs (se 1 (by rfl) ⟨18791, by rfl⟩) R37583
theorem R25919 : Reach 25919 := rs (se 1 (by rfl) ⟨19439, by rfl⟩) R38879
theorem R26159 : Reach 26159 := rs (se 1 (by rfl) ⟨19619, by rfl⟩) R39239
theorem R26345 : Reach 26345 := rs (se 2 (by rfl) ⟨9879, by rfl⟩) R19759
theorem R223165 : Reach 223165 := rs (se 3 (by rfl) ⟨41843, by rfl⟩) R83687
theorem R322001 : Reach 322001 := rs (se 2 (by rfl) ⟨120750, by rfl⟩) R241501
theorem R27239 : Reach 27239 := rs (se 1 (by rfl) ⟨20429, by rfl⟩) R40859
theorem R191119 : Reach 191119 := rs (se 1 (by rfl) ⟨143339, by rfl⟩) R286679
theorem R60263 : Reach 60263 := rs (se 1 (by rfl) ⟨45197, by rfl⟩) R90395
theorem R29225 : Reach 29225 := rs (se 2 (by rfl) ⟨10959, by rfl⟩) R21919
theorem R95165 : Reach 95165 := rs (se 3 (by rfl) ⟨17843, by rfl⟩) R35687
theorem R324769 : Reach 324769 := rs (se 2 (by rfl) ⟨121788, by rfl⟩) R243577
theorem R30719 : Reach 30719 := rs (se 1 (by rfl) ⟨23039, by rfl⟩) R46079
theorem R31463 : Reach 31463 := rs (se 1 (by rfl) ⟨23597, by rfl⟩) R47195
theorem R31769 : Reach 31769 := rs (se 2 (by rfl) ⟨11913, by rfl⟩) R23827
theorem R98279 : Reach 98279 := rs (se 1 (by rfl) ⟨73709, by rfl⟩) R147419
theorem R33407 : Reach 33407 := rs (se 1 (by rfl) ⟨25055, by rfl⟩) R50111
theorem R264059 : Reach 264059 := rs (se 1 (by rfl) ⟨198044, by rfl⟩) R396089
theorem R297553 : Reach 297553 := rs (se 2 (by rfl) ⟨111582, by rfl⟩) R223165
theorem R199259 : Reach 199259 := rs (se 1 (by rfl) ⟨149444, by rfl⟩) R298889
theorem R36719 : Reach 36719 := rs (se 1 (by rfl) ⟨27539, by rfl⟩) R55079
theorem R167807 : Reach 167807 := rs (se 1 (by rfl) ⟨125855, by rfl⟩) R251711
theorem R37259 : Reach 37259 := rs (se 1 (by rfl) ⟨27944, by rfl⟩) R55889
theorem R70895 : Reach 70895 := rs (se 1 (by rfl) ⟨53171, by rfl⟩) R106343
theorem R433025 : Reach 433025 := rs (se 2 (by rfl) ⟨162384, by rfl⟩) R324769
theorem R40175 : Reach 40175 := rs (se 1 (by rfl) ⟨30131, by rfl⟩) R60263
theorem R74519 : Reach 74519 := rs (se 1 (by rfl) ⟨55889, by rfl⟩) R111779
theorem R44315 : Reach 44315 := rs (se 1 (by rfl) ⟨33236, by rfl⟩) R66473
theorem R78715 : Reach 78715 := rs (se 1 (by rfl) ⟨59036, by rfl⟩) R118073
theorem R111719 : Reach 111719 := rs (se 1 (by rfl) ⟨83789, by rfl⟩) R167579
theorem R46415 : Reach 46415 := rs (se 1 (by rfl) ⟨34811, by rfl⟩) R69623
theorem R14335 : Reach 14335 := rs (se 1 (by rfl) ⟨10751, by rfl⟩) R21503
theorem R14427 : Reach 14427 := rs (se 1 (by rfl) ⟨10820, by rfl⟩) R21641
theorem R80351 : Reach 80351 := rs (se 1 (by rfl) ⟨60263, by rfl⟩) R120527
theorem R14959 : Reach 14959 := rs (se 1 (by rfl) ⟨11219, by rfl⟩) R22439
theorem R15135 : Reach 15135 := rs (se 1 (by rfl) ⟨11351, by rfl⟩) R22703
theorem R408559 : Reach 408559 := rs (se 1 (by rfl) ⟨306419, by rfl⟩) R612839
theorem R15899 : Reach 15899 := rs (se 1 (by rfl) ⟨11924, by rfl⟩) R23849
theorem R16367 : Reach 16367 := rs (se 1 (by rfl) ⟨12275, by rfl⟩) R24551
theorem R16495 : Reach 16495 := rs (se 1 (by rfl) ⟨12371, by rfl⟩) R24743
theorem R16539 : Reach 16539 := rs (se 1 (by rfl) ⟨12404, by rfl⟩) R24809
theorem R16703 : Reach 16703 := rs (se 1 (by rfl) ⟨12527, by rfl⟩) R25055
theorem R17279 : Reach 17279 := rs (se 1 (by rfl) ⟨12959, by rfl⟩) R25919
theorem R17439 : Reach 17439 := rs (se 1 (by rfl) ⟨13079, by rfl⟩) R26159
theorem R17563 : Reach 17563 := rs (se 1 (by rfl) ⟨13172, by rfl⟩) R26345
theorem R214667 : Reach 214667 := rs (se 1 (by rfl) ⟨161000, by rfl⟩) R322001
theorem R18159 : Reach 18159 := rs (se 1 (by rfl) ⟨13619, by rfl⟩) R27239
theorem R870389 : Reach 870389 := rs (se 5 (by rfl) ⟨40799, by rfl⟩) R81599
theorem R19483 : Reach 19483 := rs (se 1 (by rfl) ⟨14612, by rfl⟩) R29225
theorem R20479 : Reach 20479 := rs (se 1 (by rfl) ⟨15359, by rfl⟩) R30719
theorem R20975 : Reach 20975 := rs (se 1 (by rfl) ⟨15731, by rfl⟩) R31463
theorem R21179 : Reach 21179 := rs (se 1 (by rfl) ⟨15884, by rfl⟩) R31769
theorem R546203 : Reach 546203 := rs (se 1 (by rfl) ⟨409652, by rfl⟩) R819305
theorem R186623 : Reach 186623 := rs (se 1 (by rfl) ⟨139967, by rfl⟩) R279935
theorem R940409 : Reach 940409 := rs (se 2 (by rfl) ⟨352653, by rfl⟩) R705307
theorem R55723 : Reach 55723 := rs (se 1 (by rfl) ⟨41792, by rfl⟩) R83585
theorem R88573 : Reach 88573 := rs (se 3 (by rfl) ⟨16607, by rfl⟩) R33215
theorem R23081 : Reach 23081 := rs (se 2 (by rfl) ⟨8655, by rfl⟩) R17311
theorem R23207 : Reach 23207 := rs (se 1 (by rfl) ⟨17405, by rfl⟩) R34811
theorem R56315 : Reach 56315 := rs (se 1 (by rfl) ⟨42236, by rfl⟩) R84473
theorem R24329 : Reach 24329 := rs (se 2 (by rfl) ⟨9123, by rfl⟩) R18247
theorem R57341 : Reach 57341 := rs (se 3 (by rfl) ⟨10751, by rfl⟩) R21503
theorem R90233 : Reach 90233 := rs (se 2 (by rfl) ⟨33837, by rfl⟩) R67675
theorem R254825 : Reach 254825 := rs (se 2 (by rfl) ⟨95559, by rfl⟩) R191119
theorem R92015 : Reach 92015 := rs (se 1 (by rfl) ⟨69011, by rfl⟩) R138023
theorem R354293 : Reach 354293 := rs (se 5 (by rfl) ⟨16607, by rfl⟩) R33215
theorem R93311 : Reach 93311 := rs (se 1 (by rfl) ⟨69983, by rfl⟩) R139967
theorem R28607 : Reach 28607 := rs (se 1 (by rfl) ⟨21455, by rfl⟩) R42911
theorem R29417 : Reach 29417 := rs (se 2 (by rfl) ⟨11031, by rfl⟩) R22063
theorem R29723 : Reach 29723 := rs (se 1 (by rfl) ⟨22292, by rfl⟩) R44585
theorem R63443 : Reach 63443 := rs (se 1 (by rfl) ⟨47582, by rfl⟩) R95165
theorem R30707 : Reach 30707 := rs (se 1 (by rfl) ⟨23030, by rfl⟩) R46061
theorem R97321 : Reach 97321 := rs (se 2 (by rfl) ⟨36495, by rfl⟩) R72991
theorem R31799 : Reach 31799 := rs (se 1 (by rfl) ⟨23849, by rfl⟩) R47699
theorem R32735 : Reach 32735 := rs (se 1 (by rfl) ⟨24551, by rfl⟩) R49103
theorem R65519 : Reach 65519 := rs (se 1 (by rfl) ⟨49139, by rfl⟩) R98279
theorem R132839 : Reach 132839 := rs (se 1 (by rfl) ⟨99629, by rfl⟩) R199259
theorem R396737 : Reach 396737 := rs (se 2 (by rfl) ⟨148776, by rfl⟩) R297553
theorem R364135 : Reach 364135 := rs (se 1 (by rfl) ⟨273101, by rfl⟩) R546203
theorem R626939 : Reach 626939 := rs (se 1 (by rfl) ⟨470204, by rfl⟩) R940409
theorem R37543 : Reach 37543 := rs (se 1 (by rfl) ⟨28157, by rfl⟩) R56315
theorem R38227 : Reach 38227 := rs (se 1 (by rfl) ⟨28670, by rfl⟩) R57341
theorem R169883 : Reach 169883 := rs (se 1 (by rfl) ⟨127412, by rfl⟩) R254825
theorem R236195 : Reach 236195 := rs (se 1 (by rfl) ⟨177146, by rfl⟩) R354293
theorem R74297 : Reach 74297 := rs (se 2 (by rfl) ⟨27861, by rfl⟩) R55723
theorem R74479 : Reach 74479 := rs (se 1 (by rfl) ⟨55859, by rfl⟩) R111719
theorem R42295 : Reach 42295 := rs (se 1 (by rfl) ⟨31721, by rfl⟩) R63443
theorem R43679 : Reach 43679 := rs (se 1 (by rfl) ⟨32759, by rfl⟩) R65519
theorem R143111 : Reach 143111 := rs (se 1 (by rfl) ⟨107333, by rfl⟩) R214667
theorem R176039 : Reach 176039 := rs (se 1 (by rfl) ⟨132029, by rfl⟩) R264059
theorem R111871 : Reach 111871 := rs (se 1 (by rfl) ⟨83903, by rfl⟩) R167807
theorem R13983 : Reach 13983 := rs (se 1 (by rfl) ⟨10487, by rfl⟩) R20975
theorem R14119 : Reach 14119 := rs (se 1 (by rfl) ⟨10589, by rfl⟩) R21179
theorem R47263 : Reach 47263 := rs (se 1 (by rfl) ⟨35447, by rfl⟩) R70895
theorem R15387 : Reach 15387 := rs (se 1 (by rfl) ⟨11540, by rfl⟩) R23081
theorem R15471 : Reach 15471 := rs (se 1 (by rfl) ⟨11603, by rfl⟩) R23207
theorem R16219 : Reach 16219 := rs (se 1 (by rfl) ⟨12164, by rfl⟩) R24329
theorem R49679 : Reach 49679 := rs (se 1 (by rfl) ⟨37259, by rfl⟩) R74519
theorem R19071 : Reach 19071 := rs (se 1 (by rfl) ⟨14303, by rfl⟩) R28607
theorem R150173 : Reach 150173 := rs (se 3 (by rfl) ⟨28157, by rfl⟩) R56315
theorem R19113 : Reach 19113 := rs (se 2 (by rfl) ⟨7167, by rfl⟩) R14335
theorem R19611 : Reach 19611 := rs (se 1 (by rfl) ⟨14708, by rfl⟩) R29417
theorem R118097 : Reach 118097 := rs (se 2 (by rfl) ⟨44286, by rfl⟩) R88573
theorem R19815 : Reach 19815 := rs (se 1 (by rfl) ⟨14861, by rfl⟩) R29723
theorem R19945 : Reach 19945 := rs (se 2 (by rfl) ⟨7479, by rfl⟩) R14959
theorem R544745 : Reach 544745 := rs (se 2 (by rfl) ⟨204279, by rfl⟩) R408559
theorem R20471 : Reach 20471 := rs (se 1 (by rfl) ⟨15353, by rfl⟩) R30707
theorem R53567 : Reach 53567 := rs (se 1 (by rfl) ⟨40175, by rfl⟩) R80351
theorem R21199 : Reach 21199 := rs (se 1 (by rfl) ⟨15899, by rfl⟩) R31799
theorem R87293 : Reach 87293 := rs (se 3 (by rfl) ⟨16367, by rfl⟩) R32735
theorem R22271 : Reach 22271 := rs (se 1 (by rfl) ⟨16703, by rfl⟩) R33407
theorem R580259 : Reach 580259 := rs (se 1 (by rfl) ⟨435194, by rfl⟩) R870389
theorem R23417 : Reach 23417 := rs (se 2 (by rfl) ⟨8781, by rfl⟩) R17563
theorem R24479 : Reach 24479 := rs (se 1 (by rfl) ⟨18359, by rfl⟩) R36719
theorem R24839 : Reach 24839 := rs (se 1 (by rfl) ⟨18629, by rfl⟩) R37259
theorem R124415 : Reach 124415 := rs (se 1 (by rfl) ⟨93311, by rfl⟩) R186623
theorem R288683 : Reach 288683 := rs (se 1 (by rfl) ⟨216512, by rfl⟩) R433025
theorem R419813 : Reach 419813 := rs (se 4 (by rfl) ⟨39357, by rfl⟩) R78715
theorem R26783 : Reach 26783 := rs (se 1 (by rfl) ⟨20087, by rfl⟩) R40175
theorem R27305 : Reach 27305 := rs (se 2 (by rfl) ⟨10239, by rfl⟩) R20479
theorem R60155 : Reach 60155 := rs (se 1 (by rfl) ⟨45116, by rfl⟩) R90233
theorem R61343 : Reach 61343 := rs (se 1 (by rfl) ⟨46007, by rfl⟩) R92015
theorem R62207 : Reach 62207 := rs (se 1 (by rfl) ⟨46655, by rfl⟩) R93311
theorem R29543 : Reach 29543 := rs (se 1 (by rfl) ⟨22157, by rfl⟩) R44315
theorem R30943 : Reach 30943 := rs (se 1 (by rfl) ⟨23207, by rfl⟩) R46415
theorem R129761 : Reach 129761 := rs (se 2 (by rfl) ⟨48660, by rfl⟩) R97321
theorem R33119 : Reach 33119 := rs (se 1 (by rfl) ⟨24839, by rfl⟩) R49679
theorem R99305 : Reach 99305 := rs (se 2 (by rfl) ⟨37239, by rfl⟩) R74479
theorem R100115 : Reach 100115 := rs (se 1 (by rfl) ⟨75086, by rfl⟩) R150173
theorem R264491 : Reach 264491 := rs (se 1 (by rfl) ⟨198368, by rfl⟩) R396737
theorem R363163 : Reach 363163 := rs (se 1 (by rfl) ⟨272372, by rfl⟩) R544745
theorem R35711 : Reach 35711 := rs (se 1 (by rfl) ⟨26783, by rfl⟩) R53567
theorem R40103 : Reach 40103 := rs (se 1 (by rfl) ⟨30077, by rfl⟩) R60155
theorem R40895 : Reach 40895 := rs (se 1 (by rfl) ⟨30671, by rfl⟩) R61343
theorem R41257 : Reach 41257 := rs (se 2 (by rfl) ⟨15471, by rfl⟩) R30943
theorem R41471 : Reach 41471 := rs (se 1 (by rfl) ⟨31103, by rfl⟩) R62207
theorem R78731 : Reach 78731 := rs (se 1 (by rfl) ⟨59048, by rfl⟩) R118097
theorem R13647 : Reach 13647 := rs (se 1 (by rfl) ⟨10235, by rfl⟩) R20471
theorem R14847 : Reach 14847 := rs (se 1 (by rfl) ⟨11135, by rfl⟩) R22271
theorem R113255 : Reach 113255 := rs (se 1 (by rfl) ⟨84941, by rfl⟩) R169883
theorem R15611 : Reach 15611 := rs (se 1 (by rfl) ⟨11708, by rfl⟩) R23417
theorem R16319 : Reach 16319 := rs (se 1 (by rfl) ⟨12239, by rfl⟩) R24479
theorem R16559 : Reach 16559 := rs (se 1 (by rfl) ⟨12419, by rfl⟩) R24839
theorem R49531 : Reach 49531 := rs (se 1 (by rfl) ⟨37148, by rfl⟩) R74297
theorem R50057 : Reach 50057 := rs (se 2 (by rfl) ⟨18771, by rfl⟩) R37543
theorem R82943 : Reach 82943 := rs (se 1 (by rfl) ⟨62207, by rfl⟩) R124415
theorem R279875 : Reach 279875 := rs (se 1 (by rfl) ⟨209906, by rfl⟩) R419813
theorem R17855 : Reach 17855 := rs (se 1 (by rfl) ⟨13391, by rfl⟩) R26783
theorem R149161 : Reach 149161 := rs (se 2 (by rfl) ⟨55935, by rfl⟩) R111871
theorem R50969 : Reach 50969 := rs (se 2 (by rfl) ⟨19113, by rfl⟩) R38227
theorem R18203 : Reach 18203 := rs (se 1 (by rfl) ⟨13652, by rfl⟩) R27305
theorem R18825 : Reach 18825 := rs (se 2 (by rfl) ⟨7059, by rfl⟩) R14119
theorem R117359 : Reach 117359 := rs (se 1 (by rfl) ⟨88019, by rfl⟩) R176039
theorem R19695 : Reach 19695 := rs (se 1 (by rfl) ⟨14771, by rfl⟩) R29543
theorem R86507 : Reach 86507 := rs (se 1 (by rfl) ⟨64880, by rfl⟩) R129761
theorem R88559 : Reach 88559 := rs (se 1 (by rfl) ⟨66419, by rfl⟩) R132839
theorem R56393 : Reach 56393 := rs (se 2 (by rfl) ⟨21147, by rfl⟩) R42295
theorem R417959 : Reach 417959 := rs (se 1 (by rfl) ⟨313469, by rfl⟩) R626939
theorem R58195 : Reach 58195 := rs (se 1 (by rfl) ⟨43646, by rfl⟩) R87293
theorem R157463 : Reach 157463 := rs (se 1 (by rfl) ⟨118097, by rfl⟩) R236195
theorem R386839 : Reach 386839 := rs (se 1 (by rfl) ⟨290129, by rfl⟩) R580259
theorem R485513 : Reach 485513 := rs (se 2 (by rfl) ⟨182067, by rfl⟩) R364135
theorem R28265 : Reach 28265 := rs (se 2 (by rfl) ⟨10599, by rfl⟩) R21199
theorem R192455 : Reach 192455 := rs (se 1 (by rfl) ⟨144341, by rfl⟩) R288683
theorem R29119 : Reach 29119 := rs (se 1 (by rfl) ⟨21839, by rfl⟩) R43679
theorem R95407 : Reach 95407 := rs (se 1 (by rfl) ⟨71555, by rfl⟩) R143111
theorem R63017 : Reach 63017 := rs (se 2 (by rfl) ⟨23631, by rfl⟩) R47263
theorem R66041 : Reach 66041 := rs (se 2 (by rfl) ⟨24765, by rfl⟩) R49531
theorem R33371 : Reach 33371 := rs (se 1 (by rfl) ⟨25028, by rfl⟩) R50057
theorem R66203 : Reach 66203 := rs (se 1 (by rfl) ⟨49652, by rfl⟩) R99305
theorem R66743 : Reach 66743 := rs (se 1 (by rfl) ⟨50057, by rfl⟩) R100115
theorem R33979 : Reach 33979 := rs (se 1 (by rfl) ⟨25484, by rfl⟩) R50969
theorem R198881 : Reach 198881 := rs (se 2 (by rfl) ⟨74580, by rfl⟩) R149161
theorem R37595 : Reach 37595 := rs (se 1 (by rfl) ⟨28196, by rfl⟩) R56393
theorem R38825 : Reach 38825 := rs (se 2 (by rfl) ⟨14559, by rfl⟩) R29119
theorem R104975 : Reach 104975 := rs (se 1 (by rfl) ⟨78731, by rfl⟩) R157463
theorem R41629 : Reach 41629 := rs (se 3 (by rfl) ⟨7805, by rfl⟩) R15611
theorem R42011 : Reach 42011 := rs (se 1 (by rfl) ⟨31508, by rfl⟩) R63017
theorem R75503 : Reach 75503 := rs (se 1 (by rfl) ⟨56627, by rfl⟩) R113255
theorem R43517 : Reach 43517 := rs (se 3 (by rfl) ⟨8159, by rfl⟩) R16319
theorem R77593 : Reach 77593 := rs (se 2 (by rfl) ⟨29097, by rfl⟩) R58195
theorem R176327 : Reach 176327 := rs (se 1 (by rfl) ⟨132245, by rfl⟩) R264491
theorem R78239 : Reach 78239 := rs (se 1 (by rfl) ⟨58679, by rfl⟩) R117359
theorem R278639 : Reach 278639 := rs (se 1 (by rfl) ⟨208979, by rfl⟩) R417959
theorem R508837 : Reach 508837 := rs (se 4 (by rfl) ⟨47703, by rfl⟩) R95407
theorem R18843 : Reach 18843 := rs (se 1 (by rfl) ⟨14132, by rfl⟩) R28265
theorem R52487 : Reach 52487 := rs (se 1 (by rfl) ⟨39365, by rfl⟩) R78731
theorem R22079 : Reach 22079 := rs (se 1 (by rfl) ⟨16559, by rfl⟩) R33119
theorem R55009 : Reach 55009 := rs (se 2 (by rfl) ⟨20628, by rfl⟩) R41257
theorem R55295 : Reach 55295 := rs (se 1 (by rfl) ⟨41471, by rfl⟩) R82943
theorem R186583 : Reach 186583 := rs (se 1 (by rfl) ⟨139937, by rfl⟩) R279875
theorem R23807 : Reach 23807 := rs (se 1 (by rfl) ⟨17855, by rfl⟩) R35711
theorem R57671 : Reach 57671 := rs (se 1 (by rfl) ⟨43253, by rfl⟩) R86507
theorem R484217 : Reach 484217 := rs (se 2 (by rfl) ⟨181581, by rfl⟩) R363163
theorem R59039 : Reach 59039 := rs (se 1 (by rfl) ⟨44279, by rfl⟩) R88559
theorem R26735 : Reach 26735 := rs (se 1 (by rfl) ⟨20051, by rfl⟩) R40103
theorem R27263 : Reach 27263 := rs (se 1 (by rfl) ⟨20447, by rfl⟩) R40895
theorem R27647 : Reach 27647 := rs (se 1 (by rfl) ⟨20735, by rfl⟩) R41471
theorem R323675 : Reach 323675 := rs (se 1 (by rfl) ⟨242756, by rfl⟩) R485513
theorem R128303 : Reach 128303 := rs (se 1 (by rfl) ⟨96227, by rfl⟩) R192455
theorem R2063141 : Reach 2063141 := rs (se 4 (by rfl) ⟨193419, by rfl⟩) R386839
theorem R132587 : Reach 132587 := rs (se 1 (by rfl) ⟨99440, by rfl⟩) R198881
theorem R100253 : Reach 100253 := rs (se 3 (by rfl) ⟨18797, by rfl⟩) R37595
theorem R34991 : Reach 34991 := rs (se 1 (by rfl) ⟨26243, by rfl⟩) R52487
theorem R36863 : Reach 36863 := rs (se 1 (by rfl) ⟨27647, by rfl⟩) R55295
theorem R69983 : Reach 69983 := rs (se 1 (by rfl) ⟨52487, by rfl⟩) R104975
theorem R201341 : Reach 201341 := rs (se 3 (by rfl) ⟨37751, by rfl⟩) R75503
theorem R103457 : Reach 103457 := rs (se 2 (by rfl) ⟨38796, by rfl⟩) R77593
theorem R38447 : Reach 38447 := rs (se 1 (by rfl) ⟨28835, by rfl⟩) R57671
theorem R39359 : Reach 39359 := rs (se 1 (by rfl) ⟨29519, by rfl⟩) R59039
theorem R73345 : Reach 73345 := rs (se 2 (by rfl) ⟨27504, by rfl⟩) R55009
theorem R44027 : Reach 44027 := rs (se 1 (by rfl) ⟨33020, by rfl⟩) R66041
theorem R44135 : Reach 44135 := rs (se 1 (by rfl) ⟨33101, by rfl⟩) R66203
theorem R44495 : Reach 44495 := rs (se 1 (by rfl) ⟨33371, by rfl⟩) R66743
theorem R45305 : Reach 45305 := rs (se 2 (by rfl) ⟨16989, by rfl⟩) R33979
theorem R14719 : Reach 14719 := rs (se 1 (by rfl) ⟨11039, by rfl⟩) R22079
theorem R15871 : Reach 15871 := rs (se 1 (by rfl) ⟨11903, by rfl⟩) R23807
theorem R17823 : Reach 17823 := rs (se 1 (by rfl) ⟨13367, by rfl⟩) R26735
theorem R18175 : Reach 18175 := rs (se 1 (by rfl) ⟨13631, by rfl⟩) R27263
theorem R18431 : Reach 18431 := rs (se 1 (by rfl) ⟨13823, by rfl⟩) R27647
theorem R215783 : Reach 215783 := rs (se 1 (by rfl) ⟨161837, by rfl⟩) R323675
theorem R117551 : Reach 117551 := rs (se 1 (by rfl) ⟨88163, by rfl⟩) R176327
theorem R52159 : Reach 52159 := rs (se 1 (by rfl) ⟨39119, by rfl⟩) R78239
theorem R248777 : Reach 248777 := rs (se 2 (by rfl) ⟨93291, by rfl⟩) R186583
theorem R85535 : Reach 85535 := rs (se 1 (by rfl) ⟨64151, by rfl⟩) R128303
theorem R185759 : Reach 185759 := rs (se 1 (by rfl) ⟨139319, by rfl⟩) R278639
theorem R22247 : Reach 22247 := rs (se 1 (by rfl) ⟨16685, by rfl⟩) R33371
theorem R55505 : Reach 55505 := rs (se 2 (by rfl) ⟨20814, by rfl⟩) R41629
theorem R678449 : Reach 678449 := rs (se 2 (by rfl) ⟨254418, by rfl⟩) R508837
theorem R25883 : Reach 25883 := rs (se 1 (by rfl) ⟨19412, by rfl⟩) R38825
theorem R322811 : Reach 322811 := rs (se 1 (by rfl) ⟨242108, by rfl⟩) R484217
theorem R28007 : Reach 28007 := rs (se 1 (by rfl) ⟨21005, by rfl⟩) R42011
theorem R29011 : Reach 29011 := rs (se 1 (by rfl) ⟨21758, by rfl⟩) R43517
theorem R1375427 : Reach 1375427 := rs (se 1 (by rfl) ⟨1031570, by rfl⟩) R2063141
theorem R66835 : Reach 66835 := rs (se 1 (by rfl) ⟨50126, by rfl⟩) R100253
theorem R165851 : Reach 165851 := rs (se 1 (by rfl) ⟨124388, by rfl⟩) R248777
theorem R134227 : Reach 134227 := rs (se 1 (by rfl) ⟨100670, by rfl⟩) R201341
theorem R68971 : Reach 68971 := rs (se 1 (by rfl) ⟨51728, by rfl⟩) R103457
theorem R69545 : Reach 69545 := rs (se 2 (by rfl) ⟨26079, by rfl⟩) R52159
theorem R37003 : Reach 37003 := rs (se 1 (by rfl) ⟨27752, by rfl⟩) R55505
theorem R38681 : Reach 38681 := rs (se 2 (by rfl) ⟨14505, by rfl⟩) R29011
theorem R143855 : Reach 143855 := rs (se 1 (by rfl) ⟨107891, by rfl⟩) R215783
theorem R78367 : Reach 78367 := rs (se 1 (by rfl) ⟨58775, by rfl⟩) R117551
theorem R46655 : Reach 46655 := rs (se 1 (by rfl) ⟨34991, by rfl⟩) R69983
theorem R14831 : Reach 14831 := rs (se 1 (by rfl) ⟨11123, by rfl⟩) R22247
theorem R17255 : Reach 17255 := rs (se 1 (by rfl) ⟨12941, by rfl⟩) R25883
theorem R215207 : Reach 215207 := rs (se 1 (by rfl) ⟨161405, by rfl⟩) R322811
theorem R18671 : Reach 18671 := rs (se 1 (by rfl) ⟨14003, by rfl⟩) R28007
theorem R19625 : Reach 19625 := rs (se 2 (by rfl) ⟨7359, by rfl⟩) R14719
theorem R21161 : Reach 21161 := rs (se 2 (by rfl) ⟨7935, by rfl⟩) R15871
theorem R88391 : Reach 88391 := rs (se 1 (by rfl) ⟨66293, by rfl⟩) R132587
theorem R23327 : Reach 23327 := rs (se 1 (by rfl) ⟨17495, by rfl⟩) R34991
theorem R24233 : Reach 24233 := rs (se 2 (by rfl) ⟨9087, by rfl⟩) R18175
theorem R57023 : Reach 57023 := rs (se 1 (by rfl) ⟨42767, by rfl⟩) R85535
theorem R24575 : Reach 24575 := rs (se 1 (by rfl) ⟨18431, by rfl⟩) R36863
theorem R123839 : Reach 123839 := rs (se 1 (by rfl) ⟨92879, by rfl⟩) R185759
theorem R25631 : Reach 25631 := rs (se 1 (by rfl) ⟨19223, by rfl⟩) R38447
theorem R26239 : Reach 26239 := rs (se 1 (by rfl) ⟨19679, by rfl⟩) R39359
theorem R452299 : Reach 452299 := rs (se 1 (by rfl) ⟨339224, by rfl⟩) R678449
theorem R29351 : Reach 29351 := rs (se 1 (by rfl) ⟨22013, by rfl⟩) R44027
theorem R29423 : Reach 29423 := rs (se 1 (by rfl) ⟨22067, by rfl⟩) R44135
theorem R29663 : Reach 29663 := rs (se 1 (by rfl) ⟨22247, by rfl⟩) R44495
theorem R30203 : Reach 30203 := rs (se 1 (by rfl) ⟨22652, by rfl⟩) R45305
theorem R3667805 : Reach 3667805 := rs (se 3 (by rfl) ⟨687713, by rfl⟩) R1375427
theorem R97793 : Reach 97793 := rs (se 2 (by rfl) ⟨36672, by rfl⟩) R73345
theorem R34985 : Reach 34985 := rs (se 2 (by rfl) ⟨13119, by rfl⟩) R26239
theorem R38015 : Reach 38015 := rs (se 1 (by rfl) ⟨28511, by rfl⟩) R57023
theorem R104489 : Reach 104489 := rs (se 2 (by rfl) ⟨39183, by rfl⟩) R78367
theorem R110567 : Reach 110567 := rs (se 1 (by rfl) ⟨82925, by rfl⟩) R165851
theorem R143471 : Reach 143471 := rs (se 1 (by rfl) ⟨107603, by rfl⟩) R215207
theorem R13083 : Reach 13083 := rs (se 1 (by rfl) ⟨9812, by rfl⟩) R19625
theorem R603065 : Reach 603065 := rs (se 2 (by rfl) ⟨226149, by rfl⟩) R452299
theorem R46363 : Reach 46363 := rs (se 1 (by rfl) ⟨34772, by rfl⟩) R69545
theorem R14107 : Reach 14107 := rs (se 1 (by rfl) ⟨10580, by rfl⟩) R21161
theorem R178969 : Reach 178969 := rs (se 2 (by rfl) ⟨67113, by rfl⟩) R134227
theorem R15551 : Reach 15551 := rs (se 1 (by rfl) ⟨11663, by rfl⟩) R23327
theorem R16155 : Reach 16155 := rs (se 1 (by rfl) ⟨12116, by rfl⟩) R24233
theorem R16383 : Reach 16383 := rs (se 1 (by rfl) ⟨12287, by rfl⟩) R24575
theorem R49337 : Reach 49337 := rs (se 2 (by rfl) ⟨18501, by rfl⟩) R37003
theorem R82559 : Reach 82559 := rs (se 1 (by rfl) ⟨61919, by rfl⟩) R123839
theorem R17087 : Reach 17087 := rs (se 1 (by rfl) ⟨12815, by rfl⟩) R25631
theorem R19567 : Reach 19567 := rs (se 1 (by rfl) ⟨14675, by rfl⟩) R29351
theorem R19615 : Reach 19615 := rs (se 1 (by rfl) ⟨14711, by rfl⟩) R29423
theorem R19775 : Reach 19775 := rs (se 1 (by rfl) ⟨14831, by rfl⟩) R29663
theorem R20135 : Reach 20135 := rs (se 1 (by rfl) ⟨15101, by rfl⟩) R30203
theorem R2445203 : Reach 2445203 := rs (se 1 (by rfl) ⟨1833902, by rfl⟩) R3667805
theorem R89113 : Reach 89113 := rs (se 2 (by rfl) ⟨33417, by rfl⟩) R66835
theorem R56429 : Reach 56429 := rs (se 3 (by rfl) ⟨10580, by rfl⟩) R21161
theorem R25787 : Reach 25787 := rs (se 1 (by rfl) ⟨19340, by rfl⟩) R38681
theorem R58927 : Reach 58927 := rs (se 1 (by rfl) ⟨44195, by rfl⟩) R88391
theorem R91961 : Reach 91961 := rs (se 2 (by rfl) ⟨34485, by rfl⟩) R68971
theorem R95903 : Reach 95903 := rs (se 1 (by rfl) ⟨71927, by rfl⟩) R143855
theorem R31103 : Reach 31103 := rs (se 1 (by rfl) ⟨23327, by rfl⟩) R46655
theorem R65195 : Reach 65195 := rs (se 1 (by rfl) ⟨48896, by rfl⟩) R97793
theorem R32891 : Reach 32891 := rs (se 1 (by rfl) ⟨24668, by rfl⟩) R49337
theorem R69659 : Reach 69659 := rs (se 1 (by rfl) ⟨52244, by rfl⟩) R104489
theorem R37619 : Reach 37619 := rs (se 1 (by rfl) ⟨28214, by rfl⟩) R56429
theorem R73711 : Reach 73711 := rs (se 1 (by rfl) ⟨55283, by rfl⟩) R110567
theorem R402043 : Reach 402043 := rs (se 1 (by rfl) ⟨301532, by rfl⟩) R603065
theorem R238625 : Reach 238625 := rs (se 2 (by rfl) ⟨89484, by rfl⟩) R178969
theorem R43463 : Reach 43463 := rs (se 1 (by rfl) ⟨32597, by rfl⟩) R65195
theorem R78569 : Reach 78569 := rs (se 2 (by rfl) ⟨29463, by rfl⟩) R58927
theorem R13183 : Reach 13183 := rs (se 1 (by rfl) ⟨9887, by rfl⟩) R19775
theorem R13423 : Reach 13423 := rs (se 1 (by rfl) ⟨10067, by rfl⟩) R20135
theorem R17191 : Reach 17191 := rs (se 1 (by rfl) ⟨12893, by rfl⟩) R25787
theorem R18809 : Reach 18809 := rs (se 2 (by rfl) ⟨7053, by rfl⟩) R14107
theorem R118817 : Reach 118817 := rs (se 2 (by rfl) ⟨44556, by rfl⟩) R89113
theorem R20735 : Reach 20735 := rs (se 1 (by rfl) ⟨15551, by rfl⟩) R31103
theorem R53693 : Reach 53693 := rs (se 3 (by rfl) ⟨10067, by rfl⟩) R20135
theorem R382589 : Reach 382589 := rs (se 3 (by rfl) ⟨71735, by rfl⟩) R143471
theorem R55039 : Reach 55039 := rs (se 1 (by rfl) ⟨41279, by rfl⟩) R82559
theorem R23323 : Reach 23323 := rs (se 1 (by rfl) ⟨17492, by rfl⟩) R34985
theorem R220157 : Reach 220157 := rs (se 3 (by rfl) ⟨41279, by rfl⟩) R82559
theorem R1630135 : Reach 1630135 := rs (se 1 (by rfl) ⟨1222601, by rfl⟩) R2445203
theorem R25343 : Reach 25343 := rs (se 1 (by rfl) ⟨19007, by rfl⟩) R38015
theorem R26153 : Reach 26153 := rs (se 2 (by rfl) ⟨9807, by rfl⟩) R19615
theorem R61307 : Reach 61307 := rs (se 1 (by rfl) ⟨45980, by rfl⟩) R91961
theorem R61817 : Reach 61817 := rs (se 2 (by rfl) ⟨23181, by rfl⟩) R46363
theorem R63935 : Reach 63935 := rs (se 1 (by rfl) ⟨47951, by rfl⟩) R95903
theorem R164845 : Reach 164845 := rs (se 3 (by rfl) ⟨30908, by rfl⟩) R61817
theorem R35795 : Reach 35795 := rs (se 1 (by rfl) ⟨26846, by rfl⟩) R53693
theorem R73385 : Reach 73385 := rs (se 2 (by rfl) ⟨27519, by rfl⟩) R55039
theorem R40871 : Reach 40871 := rs (se 1 (by rfl) ⟨30653, by rfl⟩) R61307
theorem R42623 : Reach 42623 := rs (se 1 (by rfl) ⟨31967, by rfl⟩) R63935
theorem R2173513 : Reach 2173513 := rs (se 2 (by rfl) ⟨815067, by rfl⟩) R1630135
theorem R536057 : Reach 536057 := rs (se 2 (by rfl) ⟨201021, by rfl⟩) R402043
theorem R46439 : Reach 46439 := rs (se 1 (by rfl) ⟨34829, by rfl⟩) R69659
theorem R79211 : Reach 79211 := rs (se 1 (by rfl) ⟨59408, by rfl⟩) R118817
theorem R13823 : Reach 13823 := rs (se 1 (by rfl) ⟨10367, by rfl⟩) R20735
theorem R146771 : Reach 146771 := rs (se 1 (by rfl) ⟨110078, by rfl⟩) R220157
theorem R16895 : Reach 16895 := rs (se 1 (by rfl) ⟨12671, by rfl⟩) R25343
theorem R17435 : Reach 17435 := rs (se 1 (by rfl) ⟨13076, by rfl⟩) R26153
theorem R17577 : Reach 17577 := rs (se 2 (by rfl) ⟨6591, by rfl⟩) R13183
theorem R115901 : Reach 115901 := rs (se 3 (by rfl) ⟨21731, by rfl⟩) R43463
theorem R17897 : Reach 17897 := rs (se 2 (by rfl) ⟨6711, by rfl⟩) R13423
theorem R52379 : Reach 52379 := rs (se 1 (by rfl) ⟨39284, by rfl⟩) R78569
theorem R350837 : Reach 350837 := rs (se 5 (by rfl) ⟨16445, by rfl⟩) R32891
theorem R25079 : Reach 25079 := rs (se 1 (by rfl) ⟨18809, by rfl⟩) R37619
theorem R255059 : Reach 255059 := rs (se 1 (by rfl) ⟨191294, by rfl⟩) R382589
theorem R159083 : Reach 159083 := rs (se 1 (by rfl) ⟨119312, by rfl⟩) R238625
theorem R31097 : Reach 31097 := rs (se 2 (by rfl) ⟨11661, by rfl⟩) R23323
theorem R98281 : Reach 98281 := rs (se 2 (by rfl) ⟨36855, by rfl⟩) R73711
theorem R34919 : Reach 34919 := rs (se 1 (by rfl) ⟨26189, by rfl⟩) R52379
theorem R233891 : Reach 233891 := rs (se 1 (by rfl) ⟨175418, by rfl⟩) R350837
theorem R170039 : Reach 170039 := rs (se 1 (by rfl) ⟨127529, by rfl⟩) R255059
theorem R106055 : Reach 106055 := rs (se 1 (by rfl) ⟨79541, by rfl⟩) R159083
theorem R108989 : Reach 108989 := rs (se 3 (by rfl) ⟨20435, by rfl⟩) R40871
theorem R77267 : Reach 77267 := rs (se 1 (by rfl) ⟨57950, by rfl⟩) R115901
theorem R46493 : Reach 46493 := rs (se 3 (by rfl) ⟨8717, by rfl⟩) R17435
theorem R2898017 : Reach 2898017 := rs (se 2 (by rfl) ⟨1086756, by rfl⟩) R2173513
theorem R48923 : Reach 48923 := rs (se 1 (by rfl) ⟨36692, by rfl⟩) R73385
theorem R16719 : Reach 16719 := rs (se 1 (by rfl) ⟨12539, by rfl⟩) R25079
theorem R52807 : Reach 52807 := rs (se 1 (by rfl) ⟨39605, by rfl⟩) R79211
theorem R20731 : Reach 20731 := rs (se 1 (by rfl) ⟨15548, by rfl⟩) R31097
theorem R219793 : Reach 219793 := rs (se 2 (by rfl) ⟨82422, by rfl⟩) R164845
theorem R23863 : Reach 23863 := rs (se 1 (by rfl) ⟨17897, by rfl⟩) R35795
theorem R879173 : Reach 879173 := rs (se 4 (by rfl) ⟨82422, by rfl⟩) R164845
theorem R28415 : Reach 28415 := rs (se 1 (by rfl) ⟨21311, by rfl⟩) R42623
theorem R357371 : Reach 357371 := rs (se 1 (by rfl) ⟨268028, by rfl⟩) R536057
theorem R30959 : Reach 30959 := rs (se 1 (by rfl) ⟨23219, by rfl⟩) R46439
theorem R97847 : Reach 97847 := rs (se 1 (by rfl) ⟨73385, by rfl⟩) R146771
theorem R131041 : Reach 131041 := rs (se 2 (by rfl) ⟨49140, by rfl⟩) R98281
theorem R70409 : Reach 70409 := rs (se 2 (by rfl) ⟨26403, by rfl⟩) R52807
theorem R70703 : Reach 70703 := rs (se 1 (by rfl) ⟨53027, by rfl⟩) R106055
theorem R72659 : Reach 72659 := rs (se 1 (by rfl) ⟨54494, by rfl⟩) R108989
theorem R238247 : Reach 238247 := rs (se 1 (by rfl) ⟨178685, by rfl⟩) R357371
theorem R174721 : Reach 174721 := rs (se 2 (by rfl) ⟨65520, by rfl⟩) R131041
theorem R113359 : Reach 113359 := rs (se 1 (by rfl) ⟨85019, by rfl⟩) R170039
theorem R51511 : Reach 51511 := rs (se 1 (by rfl) ⟨38633, by rfl⟩) R77267
theorem R18943 : Reach 18943 := rs (se 1 (by rfl) ⟨14207, by rfl⟩) R28415
theorem R20639 : Reach 20639 := rs (se 1 (by rfl) ⟨15479, by rfl⟩) R30959
theorem R23279 : Reach 23279 := rs (se 1 (by rfl) ⟨17459, by rfl⟩) R34919
theorem R155927 : Reach 155927 := rs (se 1 (by rfl) ⟨116945, by rfl⟩) R233891
theorem R27641 : Reach 27641 := rs (se 2 (by rfl) ⟨10365, by rfl⟩) R20731
theorem R586115 : Reach 586115 := rs (se 1 (by rfl) ⟨439586, by rfl⟩) R879173
theorem R293057 : Reach 293057 := rs (se 2 (by rfl) ⟨109896, by rfl⟩) R219793
theorem R30995 : Reach 30995 := rs (se 1 (by rfl) ⟨23246, by rfl⟩) R46493
theorem R1932011 : Reach 1932011 := rs (se 1 (by rfl) ⟨1449008, by rfl⟩) R2898017
theorem R31817 : Reach 31817 := rs (se 2 (by rfl) ⟨11931, by rfl⟩) R23863
theorem R65231 : Reach 65231 := rs (se 1 (by rfl) ⟨48923, by rfl⟩) R97847
theorem R32615 : Reach 32615 := rs (se 1 (by rfl) ⟨24461, by rfl⟩) R48923
theorem R68681 : Reach 68681 := rs (se 2 (by rfl) ⟨25755, by rfl⟩) R51511
theorem R232961 : Reach 232961 := rs (se 2 (by rfl) ⟨87360, by rfl⟩) R174721
theorem R103951 : Reach 103951 := rs (se 1 (by rfl) ⟨77963, by rfl⟩) R155927
theorem R73709 : Reach 73709 := rs (se 3 (by rfl) ⟨13820, by rfl⟩) R27641
theorem R1288007 : Reach 1288007 := rs (se 1 (by rfl) ⟨966005, by rfl⟩) R1932011
theorem R43487 : Reach 43487 := rs (se 1 (by rfl) ⟨32615, by rfl⟩) R65231
theorem R13759 : Reach 13759 := rs (se 1 (by rfl) ⟨10319, by rfl⟩) R20639
theorem R46939 : Reach 46939 := rs (se 1 (by rfl) ⟨35204, by rfl⟩) R70409
theorem R47135 : Reach 47135 := rs (se 1 (by rfl) ⟨35351, by rfl⟩) R70703
theorem R15519 : Reach 15519 := rs (se 1 (by rfl) ⟨11639, by rfl⟩) R23279
theorem R48439 : Reach 48439 := rs (se 1 (by rfl) ⟨36329, by rfl⟩) R72659
theorem R18427 : Reach 18427 := rs (se 1 (by rfl) ⟨13820, by rfl⟩) R27641
theorem R84845 : Reach 84845 := rs (se 3 (by rfl) ⟨15908, by rfl⟩) R31817
theorem R151145 : Reach 151145 := rs (se 2 (by rfl) ⟨56679, by rfl⟩) R113359
theorem R20663 : Reach 20663 := rs (se 1 (by rfl) ⟨15497, by rfl⟩) R30995
theorem R21743 : Reach 21743 := rs (se 1 (by rfl) ⟨16307, by rfl⟩) R32615
theorem R158831 : Reach 158831 := rs (se 1 (by rfl) ⟨119123, by rfl⟩) R238247
theorem R390743 : Reach 390743 := rs (se 1 (by rfl) ⟨293057, by rfl⟩) R586115
theorem R195371 : Reach 195371 := rs (se 1 (by rfl) ⟨146528, by rfl⟩) R293057
theorem R100763 : Reach 100763 := rs (se 1 (by rfl) ⟨75572, by rfl⟩) R151145
theorem R858671 : Reach 858671 := rs (se 1 (by rfl) ⟨644003, by rfl⟩) R1288007
theorem R138601 : Reach 138601 := rs (se 2 (by rfl) ⟨51975, by rfl⟩) R103951
theorem R105887 : Reach 105887 := rs (se 1 (by rfl) ⟨79415, by rfl⟩) R158831
theorem R45787 : Reach 45787 := rs (se 1 (by rfl) ⟨34340, by rfl⟩) R68681
theorem R13775 : Reach 13775 := rs (se 1 (by rfl) ⟨10331, by rfl⟩) R20663
theorem R14495 : Reach 14495 := rs (se 1 (by rfl) ⟨10871, by rfl⟩) R21743
theorem R49139 : Reach 49139 := rs (se 1 (by rfl) ⟨36854, by rfl⟩) R73709
theorem R18345 : Reach 18345 := rs (se 2 (by rfl) ⟨6879, by rfl⟩) R13759
theorem R24569 : Reach 24569 := rs (se 2 (by rfl) ⟨9213, by rfl⟩) R18427
theorem R28991 : Reach 28991 := rs (se 1 (by rfl) ⟨21743, by rfl⟩) R43487
theorem R226253 : Reach 226253 := rs (se 3 (by rfl) ⟨42422, by rfl⟩) R84845
theorem R62585 : Reach 62585 := rs (se 2 (by rfl) ⟨23469, by rfl⟩) R46939
theorem R260495 : Reach 260495 := rs (se 1 (by rfl) ⟨195371, by rfl⟩) R390743
theorem R621229 : Reach 621229 := rs (se 3 (by rfl) ⟨116480, by rfl⟩) R232961
theorem R31423 : Reach 31423 := rs (se 1 (by rfl) ⟨23567, by rfl⟩) R47135
theorem R64585 : Reach 64585 := rs (se 2 (by rfl) ⟨24219, by rfl⟩) R48439
theorem R130247 : Reach 130247 := rs (se 1 (by rfl) ⟨97685, by rfl⟩) R195371
theorem R67175 : Reach 67175 := rs (se 1 (by rfl) ⟨50381, by rfl⟩) R100763
theorem R36733 : Reach 36733 := rs (se 3 (by rfl) ⟨6887, by rfl⟩) R13775
theorem R70591 : Reach 70591 := rs (se 1 (by rfl) ⟨52943, by rfl⟩) R105887
theorem R41723 : Reach 41723 := rs (se 1 (by rfl) ⟨31292, by rfl⟩) R62585
theorem R828305 : Reach 828305 := rs (se 2 (by rfl) ⟨310614, by rfl⟩) R621229
theorem R41897 : Reach 41897 := rs (se 2 (by rfl) ⟨15711, by rfl⟩) R31423
theorem R173663 : Reach 173663 := rs (se 1 (by rfl) ⟨130247, by rfl⟩) R260495
theorem R572447 : Reach 572447 := rs (se 1 (by rfl) ⟨429335, by rfl⟩) R858671
theorem R16379 : Reach 16379 := rs (se 1 (by rfl) ⟨12284, by rfl⟩) R24569
theorem R19327 : Reach 19327 := rs (se 1 (by rfl) ⟨14495, by rfl⟩) R28991
theorem R150835 : Reach 150835 := rs (se 1 (by rfl) ⟨113126, by rfl⟩) R226253
theorem R86113 : Reach 86113 := rs (se 2 (by rfl) ⟨32292, by rfl⟩) R64585
theorem R184801 : Reach 184801 := rs (se 2 (by rfl) ⟨69300, by rfl⟩) R138601
theorem R86831 : Reach 86831 := rs (se 1 (by rfl) ⟨65123, by rfl⟩) R130247
theorem R61049 : Reach 61049 := rs (se 2 (by rfl) ⟨22893, by rfl⟩) R45787
theorem R32759 : Reach 32759 := rs (se 1 (by rfl) ⟨24569, by rfl⟩) R49139
theorem R459269 : Reach 459269 := rs (se 4 (by rfl) ⟨43056, by rfl⟩) R86113
theorem R201113 : Reach 201113 := rs (se 2 (by rfl) ⟨75417, by rfl⟩) R150835
theorem R40699 : Reach 40699 := rs (se 1 (by rfl) ⟨30524, by rfl⟩) R61049
theorem R44783 : Reach 44783 := rs (se 1 (by rfl) ⟨33587, by rfl⟩) R67175
theorem R48977 : Reach 48977 := rs (se 2 (by rfl) ⟨18366, by rfl⟩) R36733
theorem R114817 : Reach 114817 := rs (se 2 (by rfl) ⟨43056, by rfl⟩) R86113
theorem R246401 : Reach 246401 := rs (se 2 (by rfl) ⟨92400, by rfl⟩) R184801
theorem R115775 : Reach 115775 := rs (se 1 (by rfl) ⟨86831, by rfl⟩) R173663
theorem R381631 : Reach 381631 := rs (se 1 (by rfl) ⟨286223, by rfl⟩) R572447
theorem R21839 : Reach 21839 := rs (se 1 (by rfl) ⟨16379, by rfl⟩) R32759
theorem R57887 : Reach 57887 := rs (se 1 (by rfl) ⟨43415, by rfl⟩) R86831
theorem R25769 : Reach 25769 := rs (se 2 (by rfl) ⟨9663, by rfl⟩) R19327
theorem R27815 : Reach 27815 := rs (se 1 (by rfl) ⟨20861, by rfl⟩) R41723
theorem R552203 : Reach 552203 := rs (se 1 (by rfl) ⟨414152, by rfl⟩) R828305
theorem R27931 : Reach 27931 := rs (se 1 (by rfl) ⟨20948, by rfl⟩) R41897
theorem R94121 : Reach 94121 := rs (se 2 (by rfl) ⟨35295, by rfl⟩) R70591
theorem R164267 : Reach 164267 := rs (se 1 (by rfl) ⟨123200, by rfl⟩) R246401
theorem R134075 : Reach 134075 := rs (se 1 (by rfl) ⟨100556, by rfl⟩) R201113
theorem R37241 : Reach 37241 := rs (se 2 (by rfl) ⟨13965, by rfl⟩) R27931
theorem R38591 : Reach 38591 := rs (se 1 (by rfl) ⟨28943, by rfl⟩) R57887
theorem R368135 : Reach 368135 := rs (se 1 (by rfl) ⟨276101, by rfl⟩) R552203
theorem R306179 : Reach 306179 := rs (se 1 (by rfl) ⟨229634, by rfl⟩) R459269
theorem R77183 : Reach 77183 := rs (se 1 (by rfl) ⟨57887, by rfl⟩) R115775
theorem R14559 : Reach 14559 := rs (se 1 (by rfl) ⟨10919, by rfl⟩) R21839
theorem R17179 : Reach 17179 := rs (se 1 (by rfl) ⟨12884, by rfl⟩) R25769
theorem R508841 : Reach 508841 := rs (se 2 (by rfl) ⟨190815, by rfl⟩) R381631
theorem R18543 : Reach 18543 := rs (se 1 (by rfl) ⟨13907, by rfl⟩) R27815
theorem R54265 : Reach 54265 := rs (se 2 (by rfl) ⟨20349, by rfl⟩) R40699
theorem R153089 : Reach 153089 := rs (se 2 (by rfl) ⟨57408, by rfl⟩) R114817
theorem R29855 : Reach 29855 := rs (se 1 (by rfl) ⟨22391, by rfl⟩) R44783
theorem R62747 : Reach 62747 := rs (se 1 (by rfl) ⟨47060, by rfl⟩) R94121
theorem R32651 : Reach 32651 := rs (se 1 (by rfl) ⟨24488, by rfl⟩) R48977
theorem R102059 : Reach 102059 := rs (se 1 (by rfl) ⟨76544, by rfl⟩) R153089
theorem R72353 : Reach 72353 := rs (se 2 (by rfl) ⟨27132, by rfl⟩) R54265
theorem R204119 : Reach 204119 := rs (se 1 (by rfl) ⟨153089, by rfl⟩) R306179
theorem R41831 : Reach 41831 := rs (se 1 (by rfl) ⟨31373, by rfl⟩) R62747
theorem R109511 : Reach 109511 := rs (se 1 (by rfl) ⟨82133, by rfl⟩) R164267
theorem R339227 : Reach 339227 := rs (se 1 (by rfl) ⟨254420, by rfl⟩) R508841
theorem R245423 : Reach 245423 := rs (se 1 (by rfl) ⟨184067, by rfl⟩) R368135
theorem R51455 : Reach 51455 := rs (se 1 (by rfl) ⟨38591, by rfl⟩) R77183
theorem R19903 : Reach 19903 := rs (se 1 (by rfl) ⟨14927, by rfl⟩) R29855
theorem R21767 : Reach 21767 := rs (se 1 (by rfl) ⟨16325, by rfl⟩) R32651
theorem R89383 : Reach 89383 := rs (se 1 (by rfl) ⟨67037, by rfl⟩) R134075
theorem R24827 : Reach 24827 := rs (se 1 (by rfl) ⟨18620, by rfl⟩) R37241
theorem R25727 : Reach 25727 := rs (se 1 (by rfl) ⟨19295, by rfl⟩) R38591
theorem R34303 : Reach 34303 := rs (se 1 (by rfl) ⟨25727, by rfl⟩) R51455
theorem R68039 : Reach 68039 := rs (se 1 (by rfl) ⟨51029, by rfl⟩) R102059
theorem R136079 : Reach 136079 := rs (se 1 (by rfl) ⟨102059, by rfl⟩) R204119
theorem R137213 : Reach 137213 := rs (se 3 (by rfl) ⟨25727, by rfl⟩) R51455
theorem R73007 : Reach 73007 := rs (se 1 (by rfl) ⟨54755, by rfl⟩) R109511
theorem R14511 : Reach 14511 := rs (se 1 (by rfl) ⟨10883, by rfl⟩) R21767
theorem R48235 : Reach 48235 := rs (se 1 (by rfl) ⟨36176, by rfl⟩) R72353
theorem R16551 : Reach 16551 := rs (se 1 (by rfl) ⟨12413, by rfl⟩) R24827
theorem R17151 : Reach 17151 := rs (se 1 (by rfl) ⟨12863, by rfl⟩) R25727
theorem R119177 : Reach 119177 := rs (se 2 (by rfl) ⟨44691, by rfl⟩) R89383
theorem R26537 : Reach 26537 := rs (se 2 (by rfl) ⟨9951, by rfl⟩) R19903
theorem R27887 : Reach 27887 := rs (se 1 (by rfl) ⟨20915, by rfl⟩) R41831
theorem R226151 : Reach 226151 := rs (se 1 (by rfl) ⟨169613, by rfl⟩) R339227
theorem R163615 : Reach 163615 := rs (se 1 (by rfl) ⟨122711, by rfl⟩) R245423
theorem R45359 : Reach 45359 := rs (se 1 (by rfl) ⟨34019, by rfl⟩) R68039
theorem R45737 : Reach 45737 := rs (se 2 (by rfl) ⟨17151, by rfl⟩) R34303
theorem R79451 : Reach 79451 := rs (se 1 (by rfl) ⟨59588, by rfl⟩) R119177
theorem R48671 : Reach 48671 := rs (se 1 (by rfl) ⟨36503, by rfl⟩) R73007
theorem R17691 : Reach 17691 := rs (se 1 (by rfl) ⟨13268, by rfl⟩) R26537
theorem R18591 : Reach 18591 := rs (se 1 (by rfl) ⟨13943, by rfl⟩) R27887
theorem R150767 : Reach 150767 := rs (se 1 (by rfl) ⟨113075, by rfl⟩) R226151
theorem R218153 : Reach 218153 := rs (se 2 (by rfl) ⟨81807, by rfl⟩) R163615
theorem R90719 : Reach 90719 := rs (se 1 (by rfl) ⟨68039, by rfl⟩) R136079
theorem R91475 : Reach 91475 := rs (se 1 (by rfl) ⟨68606, by rfl⟩) R137213
theorem R64313 : Reach 64313 := rs (se 2 (by rfl) ⟨24117, by rfl⟩) R48235
theorem R100511 : Reach 100511 := rs (se 1 (by rfl) ⟨75383, by rfl⟩) R150767
theorem R42875 : Reach 42875 := rs (se 1 (by rfl) ⟨32156, by rfl⟩) R64313
theorem R145435 : Reach 145435 := rs (se 1 (by rfl) ⟨109076, by rfl⟩) R218153
theorem R52967 : Reach 52967 := rs (se 1 (by rfl) ⟨39725, by rfl⟩) R79451
theorem R60479 : Reach 60479 := rs (se 1 (by rfl) ⟨45359, by rfl⟩) R90719
theorem R60983 : Reach 60983 := rs (se 1 (by rfl) ⟨45737, by rfl⟩) R91475
theorem R30239 : Reach 30239 := rs (se 1 (by rfl) ⟨22679, by rfl⟩) R45359
theorem R30491 : Reach 30491 := rs (se 1 (by rfl) ⟨22868, by rfl⟩) R45737
theorem R32447 : Reach 32447 := rs (se 1 (by rfl) ⟨24335, by rfl⟩) R48671
theorem R67007 : Reach 67007 := rs (se 1 (by rfl) ⟨50255, by rfl⟩) R100511
theorem R35311 : Reach 35311 := rs (se 1 (by rfl) ⟨26483, by rfl⟩) R52967
theorem R40319 : Reach 40319 := rs (se 1 (by rfl) ⟨30239, by rfl⟩) R60479
theorem R40655 : Reach 40655 := rs (se 1 (by rfl) ⟨30491, by rfl⟩) R60983
theorem R20159 : Reach 20159 := rs (se 1 (by rfl) ⟨15119, by rfl⟩) R30239
theorem R20327 : Reach 20327 := rs (se 1 (by rfl) ⟨15245, by rfl⟩) R30491
theorem R21631 : Reach 21631 := rs (se 1 (by rfl) ⟨16223, by rfl⟩) R32447
theorem R28583 : Reach 28583 := rs (se 1 (by rfl) ⟨21437, by rfl⟩) R42875
theorem R193913 : Reach 193913 := rs (se 2 (by rfl) ⟨72717, by rfl⟩) R145435
theorem R44671 : Reach 44671 := rs (se 1 (by rfl) ⟨33503, by rfl⟩) R67007
theorem R13439 : Reach 13439 := rs (se 1 (by rfl) ⟨10079, by rfl⟩) R20159
theorem R13551 : Reach 13551 := rs (se 1 (by rfl) ⟨10163, by rfl⟩) R20327
theorem R47081 : Reach 47081 := rs (se 2 (by rfl) ⟨17655, by rfl⟩) R35311
theorem R19055 : Reach 19055 := rs (se 1 (by rfl) ⟨14291, by rfl⟩) R28583
theorem R26879 : Reach 26879 := rs (se 1 (by rfl) ⟨20159, by rfl⟩) R40319
theorem R27103 : Reach 27103 := rs (se 1 (by rfl) ⟨20327, by rfl⟩) R40655
theorem R28841 : Reach 28841 := rs (se 2 (by rfl) ⟨10815, by rfl⟩) R21631
theorem R129275 : Reach 129275 := rs (se 1 (by rfl) ⟨96956, by rfl⟩) R193913
theorem R35837 : Reach 35837 := rs (se 3 (by rfl) ⟨6719, by rfl⟩) R13439
theorem R36137 : Reach 36137 := rs (se 2 (by rfl) ⟨13551, by rfl⟩) R27103
theorem R76909 : Reach 76909 := rs (se 3 (by rfl) ⟨14420, by rfl⟩) R28841
theorem R17919 : Reach 17919 := rs (se 1 (by rfl) ⟨13439, by rfl⟩) R26879
theorem R50813 : Reach 50813 := rs (se 3 (by rfl) ⟨9527, by rfl⟩) R19055
theorem R19227 : Reach 19227 := rs (se 1 (by rfl) ⟨14420, by rfl⟩) R28841
theorem R86183 : Reach 86183 := rs (se 1 (by rfl) ⟨64637, by rfl⟩) R129275
theorem R59561 : Reach 59561 := rs (se 2 (by rfl) ⟨22335, by rfl⟩) R44671
theorem R125549 : Reach 125549 := rs (se 3 (by rfl) ⟨23540, by rfl⟩) R47081
theorem R31387 : Reach 31387 := rs (se 1 (by rfl) ⟨23540, by rfl⟩) R47081
theorem R33875 : Reach 33875 := rs (se 1 (by rfl) ⟨25406, by rfl⟩) R50813
theorem R102545 : Reach 102545 := rs (se 2 (by rfl) ⟨38454, by rfl⟩) R76909
theorem R39707 : Reach 39707 := rs (se 1 (by rfl) ⟨29780, by rfl⟩) R59561
theorem R41849 : Reach 41849 := rs (se 2 (by rfl) ⟨15693, by rfl⟩) R31387
theorem R83699 : Reach 83699 := rs (se 1 (by rfl) ⟨62774, by rfl⟩) R125549
theorem R23891 : Reach 23891 := rs (se 1 (by rfl) ⟨17918, by rfl⟩) R35837
theorem R57455 : Reach 57455 := rs (se 1 (by rfl) ⟨43091, by rfl⟩) R86183
theorem R96365 : Reach 96365 := rs (se 3 (by rfl) ⟨18068, by rfl⟩) R36137
theorem R68363 : Reach 68363 := rs (se 1 (by rfl) ⟨51272, by rfl⟩) R102545
theorem R38303 : Reach 38303 := rs (se 1 (by rfl) ⟨28727, by rfl⟩) R57455
theorem R15927 : Reach 15927 := rs (se 1 (by rfl) ⟨11945, by rfl⟩) R23891
theorem R22583 : Reach 22583 := rs (se 1 (by rfl) ⟨16937, by rfl⟩) R33875
theorem R55799 : Reach 55799 := rs (se 1 (by rfl) ⟨41849, by rfl⟩) R83699
theorem R26471 : Reach 26471 := rs (se 1 (by rfl) ⟨19853, by rfl⟩) R39707
theorem R27899 : Reach 27899 := rs (se 1 (by rfl) ⟨20924, by rfl⟩) R41849
theorem R64243 : Reach 64243 := rs (se 1 (by rfl) ⟨48182, by rfl⟩) R96365
theorem R37199 : Reach 37199 := rs (se 1 (by rfl) ⟨27899, by rfl⟩) R55799
theorem R45575 : Reach 45575 := rs (se 1 (by rfl) ⟨34181, by rfl⟩) R68363
theorem R15055 : Reach 15055 := rs (se 1 (by rfl) ⟨11291, by rfl⟩) R22583
theorem R17647 : Reach 17647 := rs (se 1 (by rfl) ⟨13235, by rfl⟩) R26471
theorem R18599 : Reach 18599 := rs (se 1 (by rfl) ⟨13949, by rfl⟩) R27899
theorem R85657 : Reach 85657 := rs (se 2 (by rfl) ⟨32121, by rfl⟩) R64243
theorem R25535 : Reach 25535 := rs (se 1 (by rfl) ⟨19151, by rfl⟩) R38303
theorem R114209 : Reach 114209 := rs (se 2 (by rfl) ⟨42828, by rfl⟩) R85657
theorem R17023 : Reach 17023 := rs (se 1 (by rfl) ⟨12767, by rfl⟩) R25535
theorem R24799 : Reach 24799 := rs (se 1 (by rfl) ⟨18599, by rfl⟩) R37199
theorem R30383 : Reach 30383 := rs (se 1 (by rfl) ⟨22787, by rfl⟩) R45575
theorem R33065 : Reach 33065 := rs (se 2 (by rfl) ⟨12399, by rfl⟩) R24799
theorem R76139 : Reach 76139 := rs (se 1 (by rfl) ⟨57104, by rfl⟩) R114209
theorem R20255 : Reach 20255 := rs (se 1 (by rfl) ⟨15191, by rfl⟩) R30383
theorem R22697 : Reach 22697 := rs (se 2 (by rfl) ⟨8511, by rfl⟩) R17023
theorem R13503 : Reach 13503 := rs (se 1 (by rfl) ⟨10127, by rfl⟩) R20255
theorem R15131 : Reach 15131 := rs (se 1 (by rfl) ⟨11348, by rfl⟩) R22697
theorem R50759 : Reach 50759 := rs (se 1 (by rfl) ⟨38069, by rfl⟩) R76139
theorem R22043 : Reach 22043 := rs (se 1 (by rfl) ⟨16532, by rfl⟩) R33065
theorem R33839 : Reach 33839 := rs (se 1 (by rfl) ⟨25379, by rfl⟩) R50759
theorem R14695 : Reach 14695 := rs (se 1 (by rfl) ⟨11021, by rfl⟩) R22043
theorem R19593 : Reach 19593 := rs (se 2 (by rfl) ⟨7347, by rfl⟩) R14695
theorem R22559 : Reach 22559 := rs (se 1 (by rfl) ⟨16919, by rfl⟩) R33839
theorem R15039 : Reach 15039 := rs (se 1 (by rfl) ⟨11279, by rfl⟩) R22559

theorem C0 (j : ℕ) (h1 : 6412 ≤ j) (h2 : j ≤ 7111) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R12825
  · exact R12827
  · exact R12829
  · exact R12831
  · exact R12833
  · exact R12835
  · exact R12837
  · exact R12839
  · exact R12841
  · exact R12843
  · exact R12845
  · exact R12847
  · exact R12849
  · exact R12851
  · exact R12853
  · exact R12855
  · exact R12857
  · exact R12859
  · exact R12861
  · exact R12863
  · exact R12865
  · exact R12867
  · exact R12869
  · exact R12871
  · exact R12873
  · exact R12875
  · exact R12877
  · exact R12879
  · exact R12881
  · exact R12883
  · exact R12885
  · exact R12887
  · exact R12889
  · exact R12891
  · exact R12893
  · exact R12895
  · exact R12897
  · exact R12899
  · exact R12901
  · exact R12903
  · exact R12905
  · exact R12907
  · exact R12909
  · exact R12911
  · exact R12913
  · exact R12915
  · exact R12917
  · exact R12919
  · exact R12921
  · exact R12923
  · exact R12925
  · exact R12927
  · exact R12929
  · exact R12931
  · exact R12933
  · exact R12935
  · exact R12937
  · exact R12939
  · exact R12941
  · exact R12943
  · exact R12945
  · exact R12947
  · exact R12949
  · exact R12951
  · exact R12953
  · exact R12955
  · exact R12957
  · exact R12959
  · exact R12961
  · exact R12963
  · exact R12965
  · exact R12967
  · exact R12969
  · exact R12971
  · exact R12973
  · exact R12975
  · exact R12977
  · exact R12979
  · exact R12981
  · exact R12983
  · exact R12985
  · exact R12987
  · exact R12989
  · exact R12991
  · exact R12993
  · exact R12995
  · exact R12997
  · exact R12999
  · exact R13001
  · exact R13003
  · exact R13005
  · exact R13007
  · exact R13009
  · exact R13011
  · exact R13013
  · exact R13015
  · exact R13017
  · exact R13019
  · exact R13021
  · exact R13023
  · exact R13025
  · exact R13027
  · exact R13029
  · exact R13031
  · exact R13033
  · exact R13035
  · exact R13037
  · exact R13039
  · exact R13041
  · exact R13043
  · exact R13045
  · exact R13047
  · exact R13049
  · exact R13051
  · exact R13053
  · exact R13055
  · exact R13057
  · exact R13059
  · exact R13061
  · exact R13063
  · exact R13065
  · exact R13067
  · exact R13069
  · exact R13071
  · exact R13073
  · exact R13075
  · exact R13077
  · exact R13079
  · exact R13081
  · exact R13083
  · exact R13085
  · exact R13087
  · exact R13089
  · exact R13091
  · exact R13093
  · exact R13095
  · exact R13097
  · exact R13099
  · exact R13101
  · exact R13103
  · exact R13105
  · exact R13107
  · exact R13109
  · exact R13111
  · exact R13113
  · exact R13115
  · exact R13117
  · exact R13119
  · exact R13121
  · exact R13123
  · exact R13125
  · exact R13127
  · exact R13129
  · exact R13131
  · exact R13133
  · exact R13135
  · exact R13137
  · exact R13139
  · exact R13141
  · exact R13143
  · exact R13145
  · exact R13147
  · exact R13149
  · exact R13151
  · exact R13153
  · exact R13155
  · exact R13157
  · exact R13159
  · exact R13161
  · exact R13163
  · exact R13165
  · exact R13167
  · exact R13169
  · exact R13171
  · exact R13173
  · exact R13175
  · exact R13177
  · exact R13179
  · exact R13181
  · exact R13183
  · exact R13185
  · exact R13187
  · exact R13189
  · exact R13191
  · exact R13193
  · exact R13195
  · exact R13197
  · exact R13199
  · exact R13201
  · exact R13203
  · exact R13205
  · exact R13207
  · exact R13209
  · exact R13211
  · exact R13213
  · exact R13215
  · exact R13217
  · exact R13219
  · exact R13221
  · exact R13223
  · exact R13225
  · exact R13227
  · exact R13229
  · exact R13231
  · exact R13233
  · exact R13235
  · exact R13237
  · exact R13239
  · exact R13241
  · exact R13243
  · exact R13245
  · exact R13247
  · exact R13249
  · exact R13251
  · exact R13253
  · exact R13255
  · exact R13257
  · exact R13259
  · exact R13261
  · exact R13263
  · exact R13265
  · exact R13267
  · exact R13269
  · exact R13271
  · exact R13273
  · exact R13275
  · exact R13277
  · exact R13279
  · exact R13281
  · exact R13283
  · exact R13285
  · exact R13287
  · exact R13289
  · exact R13291
  · exact R13293
  · exact R13295
  · exact R13297
  · exact R13299
  · exact R13301
  · exact R13303
  · exact R13305
  · exact R13307
  · exact R13309
  · exact R13311
  · exact R13313
  · exact R13315
  · exact R13317
  · exact R13319
  · exact R13321
  · exact R13323
  · exact R13325
  · exact R13327
  · exact R13329
  · exact R13331
  · exact R13333
  · exact R13335
  · exact R13337
  · exact R13339
  · exact R13341
  · exact R13343
  · exact R13345
  · exact R13347
  · exact R13349
  · exact R13351
  · exact R13353
  · exact R13355
  · exact R13357
  · exact R13359
  · exact R13361
  · exact R13363
  · exact R13365
  · exact R13367
  · exact R13369
  · exact R13371
  · exact R13373
  · exact R13375
  · exact R13377
  · exact R13379
  · exact R13381
  · exact R13383
  · exact R13385
  · exact R13387
  · exact R13389
  · exact R13391
  · exact R13393
  · exact R13395
  · exact R13397
  · exact R13399
  · exact R13401
  · exact R13403
  · exact R13405
  · exact R13407
  · exact R13409
  · exact R13411
  · exact R13413
  · exact R13415
  · exact R13417
  · exact R13419
  · exact R13421
  · exact R13423
  · exact R13425
  · exact R13427
  · exact R13429
  · exact R13431
  · exact R13433
  · exact R13435
  · exact R13437
  · exact R13439
  · exact R13441
  · exact R13443
  · exact R13445
  · exact R13447
  · exact R13449
  · exact R13451
  · exact R13453
  · exact R13455
  · exact R13457
  · exact R13459
  · exact R13461
  · exact R13463
  · exact R13465
  · exact R13467
  · exact R13469
  · exact R13471
  · exact R13473
  · exact R13475
  · exact R13477
  · exact R13479
  · exact R13481
  · exact R13483
  · exact R13485
  · exact R13487
  · exact R13489
  · exact R13491
  · exact R13493
  · exact R13495
  · exact R13497
  · exact R13499
  · exact R13501
  · exact R13503
  · exact R13505
  · exact R13507
  · exact R13509
  · exact R13511
  · exact R13513
  · exact R13515
  · exact R13517
  · exact R13519
  · exact R13521
  · exact R13523
  · exact R13525
  · exact R13527
  · exact R13529
  · exact R13531
  · exact R13533
  · exact R13535
  · exact R13537
  · exact R13539
  · exact R13541
  · exact R13543
  · exact R13545
  · exact R13547
  · exact R13549
  · exact R13551
  · exact R13553
  · exact R13555
  · exact R13557
  · exact R13559
  · exact R13561
  · exact R13563
  · exact R13565
  · exact R13567
  · exact R13569
  · exact R13571
  · exact R13573
  · exact R13575
  · exact R13577
  · exact R13579
  · exact R13581
  · exact R13583
  · exact R13585
  · exact R13587
  · exact R13589
  · exact R13591
  · exact R13593
  · exact R13595
  · exact R13597
  · exact R13599
  · exact R13601
  · exact R13603
  · exact R13605
  · exact R13607
  · exact R13609
  · exact R13611
  · exact R13613
  · exact R13615
  · exact R13617
  · exact R13619
  · exact R13621
  · exact R13623
  · exact R13625
  · exact R13627
  · exact R13629
  · exact R13631
  · exact R13633
  · exact R13635
  · exact R13637
  · exact R13639
  · exact R13641
  · exact R13643
  · exact R13645
  · exact R13647
  · exact R13649
  · exact R13651
  · exact R13653
  · exact R13655
  · exact R13657
  · exact R13659
  · exact R13661
  · exact R13663
  · exact R13665
  · exact R13667
  · exact R13669
  · exact R13671
  · exact R13673
  · exact R13675
  · exact R13677
  · exact R13679
  · exact R13681
  · exact R13683
  · exact R13685
  · exact R13687
  · exact R13689
  · exact R13691
  · exact R13693
  · exact R13695
  · exact R13697
  · exact R13699
  · exact R13701
  · exact R13703
  · exact R13705
  · exact R13707
  · exact R13709
  · exact R13711
  · exact R13713
  · exact R13715
  · exact R13717
  · exact R13719
  · exact R13721
  · exact R13723
  · exact R13725
  · exact R13727
  · exact R13729
  · exact R13731
  · exact R13733
  · exact R13735
  · exact R13737
  · exact R13739
  · exact R13741
  · exact R13743
  · exact R13745
  · exact R13747
  · exact R13749
  · exact R13751
  · exact R13753
  · exact R13755
  · exact R13757
  · exact R13759
  · exact R13761
  · exact R13763
  · exact R13765
  · exact R13767
  · exact R13769
  · exact R13771
  · exact R13773
  · exact R13775
  · exact R13777
  · exact R13779
  · exact R13781
  · exact R13783
  · exact R13785
  · exact R13787
  · exact R13789
  · exact R13791
  · exact R13793
  · exact R13795
  · exact R13797
  · exact R13799
  · exact R13801
  · exact R13803
  · exact R13805
  · exact R13807
  · exact R13809
  · exact R13811
  · exact R13813
  · exact R13815
  · exact R13817
  · exact R13819
  · exact R13821
  · exact R13823
  · exact R13825
  · exact R13827
  · exact R13829
  · exact R13831
  · exact R13833
  · exact R13835
  · exact R13837
  · exact R13839
  · exact R13841
  · exact R13843
  · exact R13845
  · exact R13847
  · exact R13849
  · exact R13851
  · exact R13853
  · exact R13855
  · exact R13857
  · exact R13859
  · exact R13861
  · exact R13863
  · exact R13865
  · exact R13867
  · exact R13869
  · exact R13871
  · exact R13873
  · exact R13875
  · exact R13877
  · exact R13879
  · exact R13881
  · exact R13883
  · exact R13885
  · exact R13887
  · exact R13889
  · exact R13891
  · exact R13893
  · exact R13895
  · exact R13897
  · exact R13899
  · exact R13901
  · exact R13903
  · exact R13905
  · exact R13907
  · exact R13909
  · exact R13911
  · exact R13913
  · exact R13915
  · exact R13917
  · exact R13919
  · exact R13921
  · exact R13923
  · exact R13925
  · exact R13927
  · exact R13929
  · exact R13931
  · exact R13933
  · exact R13935
  · exact R13937
  · exact R13939
  · exact R13941
  · exact R13943
  · exact R13945
  · exact R13947
  · exact R13949
  · exact R13951
  · exact R13953
  · exact R13955
  · exact R13957
  · exact R13959
  · exact R13961
  · exact R13963
  · exact R13965
  · exact R13967
  · exact R13969
  · exact R13971
  · exact R13973
  · exact R13975
  · exact R13977
  · exact R13979
  · exact R13981
  · exact R13983
  · exact R13985
  · exact R13987
  · exact R13989
  · exact R13991
  · exact R13993
  · exact R13995
  · exact R13997
  · exact R13999
  · exact R14001
  · exact R14003
  · exact R14005
  · exact R14007
  · exact R14009
  · exact R14011
  · exact R14013
  · exact R14015
  · exact R14017
  · exact R14019
  · exact R14021
  · exact R14023
  · exact R14025
  · exact R14027
  · exact R14029
  · exact R14031
  · exact R14033
  · exact R14035
  · exact R14037
  · exact R14039
  · exact R14041
  · exact R14043
  · exact R14045
  · exact R14047
  · exact R14049
  · exact R14051
  · exact R14053
  · exact R14055
  · exact R14057
  · exact R14059
  · exact R14061
  · exact R14063
  · exact R14065
  · exact R14067
  · exact R14069
  · exact R14071
  · exact R14073
  · exact R14075
  · exact R14077
  · exact R14079
  · exact R14081
  · exact R14083
  · exact R14085
  · exact R14087
  · exact R14089
  · exact R14091
  · exact R14093
  · exact R14095
  · exact R14097
  · exact R14099
  · exact R14101
  · exact R14103
  · exact R14105
  · exact R14107
  · exact R14109
  · exact R14111
  · exact R14113
  · exact R14115
  · exact R14117
  · exact R14119
  · exact R14121
  · exact R14123
  · exact R14125
  · exact R14127
  · exact R14129
  · exact R14131
  · exact R14133
  · exact R14135
  · exact R14137
  · exact R14139
  · exact R14141
  · exact R14143
  · exact R14145
  · exact R14147
  · exact R14149
  · exact R14151
  · exact R14153
  · exact R14155
  · exact R14157
  · exact R14159
  · exact R14161
  · exact R14163
  · exact R14165
  · exact R14167
  · exact R14169
  · exact R14171
  · exact R14173
  · exact R14175
  · exact R14177
  · exact R14179
  · exact R14181
  · exact R14183
  · exact R14185
  · exact R14187
  · exact R14189
  · exact R14191
  · exact R14193
  · exact R14195
  · exact R14197
  · exact R14199
  · exact R14201
  · exact R14203
  · exact R14205
  · exact R14207
  · exact R14209
  · exact R14211
  · exact R14213
  · exact R14215
  · exact R14217
  · exact R14219
  · exact R14221
  · exact R14223

theorem C1 (j : ℕ) (h1 : 7112 ≤ j) (h2 : j ≤ 7811) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R14225
  · exact R14227
  · exact R14229
  · exact R14231
  · exact R14233
  · exact R14235
  · exact R14237
  · exact R14239
  · exact R14241
  · exact R14243
  · exact R14245
  · exact R14247
  · exact R14249
  · exact R14251
  · exact R14253
  · exact R14255
  · exact R14257
  · exact R14259
  · exact R14261
  · exact R14263
  · exact R14265
  · exact R14267
  · exact R14269
  · exact R14271
  · exact R14273
  · exact R14275
  · exact R14277
  · exact R14279
  · exact R14281
  · exact R14283
  · exact R14285
  · exact R14287
  · exact R14289
  · exact R14291
  · exact R14293
  · exact R14295
  · exact R14297
  · exact R14299
  · exact R14301
  · exact R14303
  · exact R14305
  · exact R14307
  · exact R14309
  · exact R14311
  · exact R14313
  · exact R14315
  · exact R14317
  · exact R14319
  · exact R14321
  · exact R14323
  · exact R14325
  · exact R14327
  · exact R14329
  · exact R14331
  · exact R14333
  · exact R14335
  · exact R14337
  · exact R14339
  · exact R14341
  · exact R14343
  · exact R14345
  · exact R14347
  · exact R14349
  · exact R14351
  · exact R14353
  · exact R14355
  · exact R14357
  · exact R14359
  · exact R14361
  · exact R14363
  · exact R14365
  · exact R14367
  · exact R14369
  · exact R14371
  · exact R14373
  · exact R14375
  · exact R14377
  · exact R14379
  · exact R14381
  · exact R14383
  · exact R14385
  · exact R14387
  · exact R14389
  · exact R14391
  · exact R14393
  · exact R14395
  · exact R14397
  · exact R14399
  · exact R14401
  · exact R14403
  · exact R14405
  · exact R14407
  · exact R14409
  · exact R14411
  · exact R14413
  · exact R14415
  · exact R14417
  · exact R14419
  · exact R14421
  · exact R14423
  · exact R14425
  · exact R14427
  · exact R14429
  · exact R14431
  · exact R14433
  · exact R14435
  · exact R14437
  · exact R14439
  · exact R14441
  · exact R14443
  · exact R14445
  · exact R14447
  · exact R14449
  · exact R14451
  · exact R14453
  · exact R14455
  · exact R14457
  · exact R14459
  · exact R14461
  · exact R14463
  · exact R14465
  · exact R14467
  · exact R14469
  · exact R14471
  · exact R14473
  · exact R14475
  · exact R14477
  · exact R14479
  · exact R14481
  · exact R14483
  · exact R14485
  · exact R14487
  · exact R14489
  · exact R14491
  · exact R14493
  · exact R14495
  · exact R14497
  · exact R14499
  · exact R14501
  · exact R14503
  · exact R14505
  · exact R14507
  · exact R14509
  · exact R14511
  · exact R14513
  · exact R14515
  · exact R14517
  · exact R14519
  · exact R14521
  · exact R14523
  · exact R14525
  · exact R14527
  · exact R14529
  · exact R14531
  · exact R14533
  · exact R14535
  · exact R14537
  · exact R14539
  · exact R14541
  · exact R14543
  · exact R14545
  · exact R14547
  · exact R14549
  · exact R14551
  · exact R14553
  · exact R14555
  · exact R14557
  · exact R14559
  · exact R14561
  · exact R14563
  · exact R14565
  · exact R14567
  · exact R14569
  · exact R14571
  · exact R14573
  · exact R14575
  · exact R14577
  · exact R14579
  · exact R14581
  · exact R14583
  · exact R14585
  · exact R14587
  · exact R14589
  · exact R14591
  · exact R14593
  · exact R14595
  · exact R14597
  · exact R14599
  · exact R14601
  · exact R14603
  · exact R14605
  · exact R14607
  · exact R14609
  · exact R14611
  · exact R14613
  · exact R14615
  · exact R14617
  · exact R14619
  · exact R14621
  · exact R14623
  · exact R14625
  · exact R14627
  · exact R14629
  · exact R14631
  · exact R14633
  · exact R14635
  · exact R14637
  · exact R14639
  · exact R14641
  · exact R14643
  · exact R14645
  · exact R14647
  · exact R14649
  · exact R14651
  · exact R14653
  · exact R14655
  · exact R14657
  · exact R14659
  · exact R14661
  · exact R14663
  · exact R14665
  · exact R14667
  · exact R14669
  · exact R14671
  · exact R14673
  · exact R14675
  · exact R14677
  · exact R14679
  · exact R14681
  · exact R14683
  · exact R14685
  · exact R14687
  · exact R14689
  · exact R14691
  · exact R14693
  · exact R14695
  · exact R14697
  · exact R14699
  · exact R14701
  · exact R14703
  · exact R14705
  · exact R14707
  · exact R14709
  · exact R14711
  · exact R14713
  · exact R14715
  · exact R14717
  · exact R14719
  · exact R14721
  · exact R14723
  · exact R14725
  · exact R14727
  · exact R14729
  · exact R14731
  · exact R14733
  · exact R14735
  · exact R14737
  · exact R14739
  · exact R14741
  · exact R14743
  · exact R14745
  · exact R14747
  · exact R14749
  · exact R14751
  · exact R14753
  · exact R14755
  · exact R14757
  · exact R14759
  · exact R14761
  · exact R14763
  · exact R14765
  · exact R14767
  · exact R14769
  · exact R14771
  · exact R14773
  · exact R14775
  · exact R14777
  · exact R14779
  · exact R14781
  · exact R14783
  · exact R14785
  · exact R14787
  · exact R14789
  · exact R14791
  · exact R14793
  · exact R14795
  · exact R14797
  · exact R14799
  · exact R14801
  · exact R14803
  · exact R14805
  · exact R14807
  · exact R14809
  · exact R14811
  · exact R14813
  · exact R14815
  · exact R14817
  · exact R14819
  · exact R14821
  · exact R14823
  · exact R14825
  · exact R14827
  · exact R14829
  · exact R14831
  · exact R14833
  · exact R14835
  · exact R14837
  · exact R14839
  · exact R14841
  · exact R14843
  · exact R14845
  · exact R14847
  · exact R14849
  · exact R14851
  · exact R14853
  · exact R14855
  · exact R14857
  · exact R14859
  · exact R14861
  · exact R14863
  · exact R14865
  · exact R14867
  · exact R14869
  · exact R14871
  · exact R14873
  · exact R14875
  · exact R14877
  · exact R14879
  · exact R14881
  · exact R14883
  · exact R14885
  · exact R14887
  · exact R14889
  · exact R14891
  · exact R14893
  · exact R14895
  · exact R14897
  · exact R14899
  · exact R14901
  · exact R14903
  · exact R14905
  · exact R14907
  · exact R14909
  · exact R14911
  · exact R14913
  · exact R14915
  · exact R14917
  · exact R14919
  · exact R14921
  · exact R14923
  · exact R14925
  · exact R14927
  · exact R14929
  · exact R14931
  · exact R14933
  · exact R14935
  · exact R14937
  · exact R14939
  · exact R14941
  · exact R14943
  · exact R14945
  · exact R14947
  · exact R14949
  · exact R14951
  · exact R14953
  · exact R14955
  · exact R14957
  · exact R14959
  · exact R14961
  · exact R14963
  · exact R14965
  · exact R14967
  · exact R14969
  · exact R14971
  · exact R14973
  · exact R14975
  · exact R14977
  · exact R14979
  · exact R14981
  · exact R14983
  · exact R14985
  · exact R14987
  · exact R14989
  · exact R14991
  · exact R14993
  · exact R14995
  · exact R14997
  · exact R14999
  · exact R15001
  · exact R15003
  · exact R15005
  · exact R15007
  · exact R15009
  · exact R15011
  · exact R15013
  · exact R15015
  · exact R15017
  · exact R15019
  · exact R15021
  · exact R15023
  · exact R15025
  · exact R15027
  · exact R15029
  · exact R15031
  · exact R15033
  · exact R15035
  · exact R15037
  · exact R15039
  · exact R15041
  · exact R15043
  · exact R15045
  · exact R15047
  · exact R15049
  · exact R15051
  · exact R15053
  · exact R15055
  · exact R15057
  · exact R15059
  · exact R15061
  · exact R15063
  · exact R15065
  · exact R15067
  · exact R15069
  · exact R15071
  · exact R15073
  · exact R15075
  · exact R15077
  · exact R15079
  · exact R15081
  · exact R15083
  · exact R15085
  · exact R15087
  · exact R15089
  · exact R15091
  · exact R15093
  · exact R15095
  · exact R15097
  · exact R15099
  · exact R15101
  · exact R15103
  · exact R15105
  · exact R15107
  · exact R15109
  · exact R15111
  · exact R15113
  · exact R15115
  · exact R15117
  · exact R15119
  · exact R15121
  · exact R15123
  · exact R15125
  · exact R15127
  · exact R15129
  · exact R15131
  · exact R15133
  · exact R15135
  · exact R15137
  · exact R15139
  · exact R15141
  · exact R15143
  · exact R15145
  · exact R15147
  · exact R15149
  · exact R15151
  · exact R15153
  · exact R15155
  · exact R15157
  · exact R15159
  · exact R15161
  · exact R15163
  · exact R15165
  · exact R15167
  · exact R15169
  · exact R15171
  · exact R15173
  · exact R15175
  · exact R15177
  · exact R15179
  · exact R15181
  · exact R15183
  · exact R15185
  · exact R15187
  · exact R15189
  · exact R15191
  · exact R15193
  · exact R15195
  · exact R15197
  · exact R15199
  · exact R15201
  · exact R15203
  · exact R15205
  · exact R15207
  · exact R15209
  · exact R15211
  · exact R15213
  · exact R15215
  · exact R15217
  · exact R15219
  · exact R15221
  · exact R15223
  · exact R15225
  · exact R15227
  · exact R15229
  · exact R15231
  · exact R15233
  · exact R15235
  · exact R15237
  · exact R15239
  · exact R15241
  · exact R15243
  · exact R15245
  · exact R15247
  · exact R15249
  · exact R15251
  · exact R15253
  · exact R15255
  · exact R15257
  · exact R15259
  · exact R15261
  · exact R15263
  · exact R15265
  · exact R15267
  · exact R15269
  · exact R15271
  · exact R15273
  · exact R15275
  · exact R15277
  · exact R15279
  · exact R15281
  · exact R15283
  · exact R15285
  · exact R15287
  · exact R15289
  · exact R15291
  · exact R15293
  · exact R15295
  · exact R15297
  · exact R15299
  · exact R15301
  · exact R15303
  · exact R15305
  · exact R15307
  · exact R15309
  · exact R15311
  · exact R15313
  · exact R15315
  · exact R15317
  · exact R15319
  · exact R15321
  · exact R15323
  · exact R15325
  · exact R15327
  · exact R15329
  · exact R15331
  · exact R15333
  · exact R15335
  · exact R15337
  · exact R15339
  · exact R15341
  · exact R15343
  · exact R15345
  · exact R15347
  · exact R15349
  · exact R15351
  · exact R15353
  · exact R15355
  · exact R15357
  · exact R15359
  · exact R15361
  · exact R15363
  · exact R15365
  · exact R15367
  · exact R15369
  · exact R15371
  · exact R15373
  · exact R15375
  · exact R15377
  · exact R15379
  · exact R15381
  · exact R15383
  · exact R15385
  · exact R15387
  · exact R15389
  · exact R15391
  · exact R15393
  · exact R15395
  · exact R15397
  · exact R15399
  · exact R15401
  · exact R15403
  · exact R15405
  · exact R15407
  · exact R15409
  · exact R15411
  · exact R15413
  · exact R15415
  · exact R15417
  · exact R15419
  · exact R15421
  · exact R15423
  · exact R15425
  · exact R15427
  · exact R15429
  · exact R15431
  · exact R15433
  · exact R15435
  · exact R15437
  · exact R15439
  · exact R15441
  · exact R15443
  · exact R15445
  · exact R15447
  · exact R15449
  · exact R15451
  · exact R15453
  · exact R15455
  · exact R15457
  · exact R15459
  · exact R15461
  · exact R15463
  · exact R15465
  · exact R15467
  · exact R15469
  · exact R15471
  · exact R15473
  · exact R15475
  · exact R15477
  · exact R15479
  · exact R15481
  · exact R15483
  · exact R15485
  · exact R15487
  · exact R15489
  · exact R15491
  · exact R15493
  · exact R15495
  · exact R15497
  · exact R15499
  · exact R15501
  · exact R15503
  · exact R15505
  · exact R15507
  · exact R15509
  · exact R15511
  · exact R15513
  · exact R15515
  · exact R15517
  · exact R15519
  · exact R15521
  · exact R15523
  · exact R15525
  · exact R15527
  · exact R15529
  · exact R15531
  · exact R15533
  · exact R15535
  · exact R15537
  · exact R15539
  · exact R15541
  · exact R15543
  · exact R15545
  · exact R15547
  · exact R15549
  · exact R15551
  · exact R15553
  · exact R15555
  · exact R15557
  · exact R15559
  · exact R15561
  · exact R15563
  · exact R15565
  · exact R15567
  · exact R15569
  · exact R15571
  · exact R15573
  · exact R15575
  · exact R15577
  · exact R15579
  · exact R15581
  · exact R15583
  · exact R15585
  · exact R15587
  · exact R15589
  · exact R15591
  · exact R15593
  · exact R15595
  · exact R15597
  · exact R15599
  · exact R15601
  · exact R15603
  · exact R15605
  · exact R15607
  · exact R15609
  · exact R15611
  · exact R15613
  · exact R15615
  · exact R15617
  · exact R15619
  · exact R15621
  · exact R15623

theorem C2 (j : ℕ) (h1 : 7812 ≤ j) (h2 : j ≤ 8511) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R15625
  · exact R15627
  · exact R15629
  · exact R15631
  · exact R15633
  · exact R15635
  · exact R15637
  · exact R15639
  · exact R15641
  · exact R15643
  · exact R15645
  · exact R15647
  · exact R15649
  · exact R15651
  · exact R15653
  · exact R15655
  · exact R15657
  · exact R15659
  · exact R15661
  · exact R15663
  · exact R15665
  · exact R15667
  · exact R15669
  · exact R15671
  · exact R15673
  · exact R15675
  · exact R15677
  · exact R15679
  · exact R15681
  · exact R15683
  · exact R15685
  · exact R15687
  · exact R15689
  · exact R15691
  · exact R15693
  · exact R15695
  · exact R15697
  · exact R15699
  · exact R15701
  · exact R15703
  · exact R15705
  · exact R15707
  · exact R15709
  · exact R15711
  · exact R15713
  · exact R15715
  · exact R15717
  · exact R15719
  · exact R15721
  · exact R15723
  · exact R15725
  · exact R15727
  · exact R15729
  · exact R15731
  · exact R15733
  · exact R15735
  · exact R15737
  · exact R15739
  · exact R15741
  · exact R15743
  · exact R15745
  · exact R15747
  · exact R15749
  · exact R15751
  · exact R15753
  · exact R15755
  · exact R15757
  · exact R15759
  · exact R15761
  · exact R15763
  · exact R15765
  · exact R15767
  · exact R15769
  · exact R15771
  · exact R15773
  · exact R15775
  · exact R15777
  · exact R15779
  · exact R15781
  · exact R15783
  · exact R15785
  · exact R15787
  · exact R15789
  · exact R15791
  · exact R15793
  · exact R15795
  · exact R15797
  · exact R15799
  · exact R15801
  · exact R15803
  · exact R15805
  · exact R15807
  · exact R15809
  · exact R15811
  · exact R15813
  · exact R15815
  · exact R15817
  · exact R15819
  · exact R15821
  · exact R15823
  · exact R15825
  · exact R15827
  · exact R15829
  · exact R15831
  · exact R15833
  · exact R15835
  · exact R15837
  · exact R15839
  · exact R15841
  · exact R15843
  · exact R15845
  · exact R15847
  · exact R15849
  · exact R15851
  · exact R15853
  · exact R15855
  · exact R15857
  · exact R15859
  · exact R15861
  · exact R15863
  · exact R15865
  · exact R15867
  · exact R15869
  · exact R15871
  · exact R15873
  · exact R15875
  · exact R15877
  · exact R15879
  · exact R15881
  · exact R15883
  · exact R15885
  · exact R15887
  · exact R15889
  · exact R15891
  · exact R15893
  · exact R15895
  · exact R15897
  · exact R15899
  · exact R15901
  · exact R15903
  · exact R15905
  · exact R15907
  · exact R15909
  · exact R15911
  · exact R15913
  · exact R15915
  · exact R15917
  · exact R15919
  · exact R15921
  · exact R15923
  · exact R15925
  · exact R15927
  · exact R15929
  · exact R15931
  · exact R15933
  · exact R15935
  · exact R15937
  · exact R15939
  · exact R15941
  · exact R15943
  · exact R15945
  · exact R15947
  · exact R15949
  · exact R15951
  · exact R15953
  · exact R15955
  · exact R15957
  · exact R15959
  · exact R15961
  · exact R15963
  · exact R15965
  · exact R15967
  · exact R15969
  · exact R15971
  · exact R15973
  · exact R15975
  · exact R15977
  · exact R15979
  · exact R15981
  · exact R15983
  · exact R15985
  · exact R15987
  · exact R15989
  · exact R15991
  · exact R15993
  · exact R15995
  · exact R15997
  · exact R15999
  · exact R16001
  · exact R16003
  · exact R16005
  · exact R16007
  · exact R16009
  · exact R16011
  · exact R16013
  · exact R16015
  · exact R16017
  · exact R16019
  · exact R16021
  · exact R16023
  · exact R16025
  · exact R16027
  · exact R16029
  · exact R16031
  · exact R16033
  · exact R16035
  · exact R16037
  · exact R16039
  · exact R16041
  · exact R16043
  · exact R16045
  · exact R16047
  · exact R16049
  · exact R16051
  · exact R16053
  · exact R16055
  · exact R16057
  · exact R16059
  · exact R16061
  · exact R16063
  · exact R16065
  · exact R16067
  · exact R16069
  · exact R16071
  · exact R16073
  · exact R16075
  · exact R16077
  · exact R16079
  · exact R16081
  · exact R16083
  · exact R16085
  · exact R16087
  · exact R16089
  · exact R16091
  · exact R16093
  · exact R16095
  · exact R16097
  · exact R16099
  · exact R16101
  · exact R16103
  · exact R16105
  · exact R16107
  · exact R16109
  · exact R16111
  · exact R16113
  · exact R16115
  · exact R16117
  · exact R16119
  · exact R16121
  · exact R16123
  · exact R16125
  · exact R16127
  · exact R16129
  · exact R16131
  · exact R16133
  · exact R16135
  · exact R16137
  · exact R16139
  · exact R16141
  · exact R16143
  · exact R16145
  · exact R16147
  · exact R16149
  · exact R16151
  · exact R16153
  · exact R16155
  · exact R16157
  · exact R16159
  · exact R16161
  · exact R16163
  · exact R16165
  · exact R16167
  · exact R16169
  · exact R16171
  · exact R16173
  · exact R16175
  · exact R16177
  · exact R16179
  · exact R16181
  · exact R16183
  · exact R16185
  · exact R16187
  · exact R16189
  · exact R16191
  · exact R16193
  · exact R16195
  · exact R16197
  · exact R16199
  · exact R16201
  · exact R16203
  · exact R16205
  · exact R16207
  · exact R16209
  · exact R16211
  · exact R16213
  · exact R16215
  · exact R16217
  · exact R16219
  · exact R16221
  · exact R16223
  · exact R16225
  · exact R16227
  · exact R16229
  · exact R16231
  · exact R16233
  · exact R16235
  · exact R16237
  · exact R16239
  · exact R16241
  · exact R16243
  · exact R16245
  · exact R16247
  · exact R16249
  · exact R16251
  · exact R16253
  · exact R16255
  · exact R16257
  · exact R16259
  · exact R16261
  · exact R16263
  · exact R16265
  · exact R16267
  · exact R16269
  · exact R16271
  · exact R16273
  · exact R16275
  · exact R16277
  · exact R16279
  · exact R16281
  · exact R16283
  · exact R16285
  · exact R16287
  · exact R16289
  · exact R16291
  · exact R16293
  · exact R16295
  · exact R16297
  · exact R16299
  · exact R16301
  · exact R16303
  · exact R16305
  · exact R16307
  · exact R16309
  · exact R16311
  · exact R16313
  · exact R16315
  · exact R16317
  · exact R16319
  · exact R16321
  · exact R16323
  · exact R16325
  · exact R16327
  · exact R16329
  · exact R16331
  · exact R16333
  · exact R16335
  · exact R16337
  · exact R16339
  · exact R16341
  · exact R16343
  · exact R16345
  · exact R16347
  · exact R16349
  · exact R16351
  · exact R16353
  · exact R16355
  · exact R16357
  · exact R16359
  · exact R16361
  · exact R16363
  · exact R16365
  · exact R16367
  · exact R16369
  · exact R16371
  · exact R16373
  · exact R16375
  · exact R16377
  · exact R16379
  · exact R16381
  · exact R16383
  · exact R16385
  · exact R16387
  · exact R16389
  · exact R16391
  · exact R16393
  · exact R16395
  · exact R16397
  · exact R16399
  · exact R16401
  · exact R16403
  · exact R16405
  · exact R16407
  · exact R16409
  · exact R16411
  · exact R16413
  · exact R16415
  · exact R16417
  · exact R16419
  · exact R16421
  · exact R16423
  · exact R16425
  · exact R16427
  · exact R16429
  · exact R16431
  · exact R16433
  · exact R16435
  · exact R16437
  · exact R16439
  · exact R16441
  · exact R16443
  · exact R16445
  · exact R16447
  · exact R16449
  · exact R16451
  · exact R16453
  · exact R16455
  · exact R16457
  · exact R16459
  · exact R16461
  · exact R16463
  · exact R16465
  · exact R16467
  · exact R16469
  · exact R16471
  · exact R16473
  · exact R16475
  · exact R16477
  · exact R16479
  · exact R16481
  · exact R16483
  · exact R16485
  · exact R16487
  · exact R16489
  · exact R16491
  · exact R16493
  · exact R16495
  · exact R16497
  · exact R16499
  · exact R16501
  · exact R16503
  · exact R16505
  · exact R16507
  · exact R16509
  · exact R16511
  · exact R16513
  · exact R16515
  · exact R16517
  · exact R16519
  · exact R16521
  · exact R16523
  · exact R16525
  · exact R16527
  · exact R16529
  · exact R16531
  · exact R16533
  · exact R16535
  · exact R16537
  · exact R16539
  · exact R16541
  · exact R16543
  · exact R16545
  · exact R16547
  · exact R16549
  · exact R16551
  · exact R16553
  · exact R16555
  · exact R16557
  · exact R16559
  · exact R16561
  · exact R16563
  · exact R16565
  · exact R16567
  · exact R16569
  · exact R16571
  · exact R16573
  · exact R16575
  · exact R16577
  · exact R16579
  · exact R16581
  · exact R16583
  · exact R16585
  · exact R16587
  · exact R16589
  · exact R16591
  · exact R16593
  · exact R16595
  · exact R16597
  · exact R16599
  · exact R16601
  · exact R16603
  · exact R16605
  · exact R16607
  · exact R16609
  · exact R16611
  · exact R16613
  · exact R16615
  · exact R16617
  · exact R16619
  · exact R16621
  · exact R16623
  · exact R16625
  · exact R16627
  · exact R16629
  · exact R16631
  · exact R16633
  · exact R16635
  · exact R16637
  · exact R16639
  · exact R16641
  · exact R16643
  · exact R16645
  · exact R16647
  · exact R16649
  · exact R16651
  · exact R16653
  · exact R16655
  · exact R16657
  · exact R16659
  · exact R16661
  · exact R16663
  · exact R16665
  · exact R16667
  · exact R16669
  · exact R16671
  · exact R16673
  · exact R16675
  · exact R16677
  · exact R16679
  · exact R16681
  · exact R16683
  · exact R16685
  · exact R16687
  · exact R16689
  · exact R16691
  · exact R16693
  · exact R16695
  · exact R16697
  · exact R16699
  · exact R16701
  · exact R16703
  · exact R16705
  · exact R16707
  · exact R16709
  · exact R16711
  · exact R16713
  · exact R16715
  · exact R16717
  · exact R16719
  · exact R16721
  · exact R16723
  · exact R16725
  · exact R16727
  · exact R16729
  · exact R16731
  · exact R16733
  · exact R16735
  · exact R16737
  · exact R16739
  · exact R16741
  · exact R16743
  · exact R16745
  · exact R16747
  · exact R16749
  · exact R16751
  · exact R16753
  · exact R16755
  · exact R16757
  · exact R16759
  · exact R16761
  · exact R16763
  · exact R16765
  · exact R16767
  · exact R16769
  · exact R16771
  · exact R16773
  · exact R16775
  · exact R16777
  · exact R16779
  · exact R16781
  · exact R16783
  · exact R16785
  · exact R16787
  · exact R16789
  · exact R16791
  · exact R16793
  · exact R16795
  · exact R16797
  · exact R16799
  · exact R16801
  · exact R16803
  · exact R16805
  · exact R16807
  · exact R16809
  · exact R16811
  · exact R16813
  · exact R16815
  · exact R16817
  · exact R16819
  · exact R16821
  · exact R16823
  · exact R16825
  · exact R16827
  · exact R16829
  · exact R16831
  · exact R16833
  · exact R16835
  · exact R16837
  · exact R16839
  · exact R16841
  · exact R16843
  · exact R16845
  · exact R16847
  · exact R16849
  · exact R16851
  · exact R16853
  · exact R16855
  · exact R16857
  · exact R16859
  · exact R16861
  · exact R16863
  · exact R16865
  · exact R16867
  · exact R16869
  · exact R16871
  · exact R16873
  · exact R16875
  · exact R16877
  · exact R16879
  · exact R16881
  · exact R16883
  · exact R16885
  · exact R16887
  · exact R16889
  · exact R16891
  · exact R16893
  · exact R16895
  · exact R16897
  · exact R16899
  · exact R16901
  · exact R16903
  · exact R16905
  · exact R16907
  · exact R16909
  · exact R16911
  · exact R16913
  · exact R16915
  · exact R16917
  · exact R16919
  · exact R16921
  · exact R16923
  · exact R16925
  · exact R16927
  · exact R16929
  · exact R16931
  · exact R16933
  · exact R16935
  · exact R16937
  · exact R16939
  · exact R16941
  · exact R16943
  · exact R16945
  · exact R16947
  · exact R16949
  · exact R16951
  · exact R16953
  · exact R16955
  · exact R16957
  · exact R16959
  · exact R16961
  · exact R16963
  · exact R16965
  · exact R16967
  · exact R16969
  · exact R16971
  · exact R16973
  · exact R16975
  · exact R16977
  · exact R16979
  · exact R16981
  · exact R16983
  · exact R16985
  · exact R16987
  · exact R16989
  · exact R16991
  · exact R16993
  · exact R16995
  · exact R16997
  · exact R16999
  · exact R17001
  · exact R17003
  · exact R17005
  · exact R17007
  · exact R17009
  · exact R17011
  · exact R17013
  · exact R17015
  · exact R17017
  · exact R17019
  · exact R17021
  · exact R17023

theorem C3 (j : ℕ) (h1 : 8512 ≤ j) (h2 : j ≤ 9211) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R17025
  · exact R17027
  · exact R17029
  · exact R17031
  · exact R17033
  · exact R17035
  · exact R17037
  · exact R17039
  · exact R17041
  · exact R17043
  · exact R17045
  · exact R17047
  · exact R17049
  · exact R17051
  · exact R17053
  · exact R17055
  · exact R17057
  · exact R17059
  · exact R17061
  · exact R17063
  · exact R17065
  · exact R17067
  · exact R17069
  · exact R17071
  · exact R17073
  · exact R17075
  · exact R17077
  · exact R17079
  · exact R17081
  · exact R17083
  · exact R17085
  · exact R17087
  · exact R17089
  · exact R17091
  · exact R17093
  · exact R17095
  · exact R17097
  · exact R17099
  · exact R17101
  · exact R17103
  · exact R17105
  · exact R17107
  · exact R17109
  · exact R17111
  · exact R17113
  · exact R17115
  · exact R17117
  · exact R17119
  · exact R17121
  · exact R17123
  · exact R17125
  · exact R17127
  · exact R17129
  · exact R17131
  · exact R17133
  · exact R17135
  · exact R17137
  · exact R17139
  · exact R17141
  · exact R17143
  · exact R17145
  · exact R17147
  · exact R17149
  · exact R17151
  · exact R17153
  · exact R17155
  · exact R17157
  · exact R17159
  · exact R17161
  · exact R17163
  · exact R17165
  · exact R17167
  · exact R17169
  · exact R17171
  · exact R17173
  · exact R17175
  · exact R17177
  · exact R17179
  · exact R17181
  · exact R17183
  · exact R17185
  · exact R17187
  · exact R17189
  · exact R17191
  · exact R17193
  · exact R17195
  · exact R17197
  · exact R17199
  · exact R17201
  · exact R17203
  · exact R17205
  · exact R17207
  · exact R17209
  · exact R17211
  · exact R17213
  · exact R17215
  · exact R17217
  · exact R17219
  · exact R17221
  · exact R17223
  · exact R17225
  · exact R17227
  · exact R17229
  · exact R17231
  · exact R17233
  · exact R17235
  · exact R17237
  · exact R17239
  · exact R17241
  · exact R17243
  · exact R17245
  · exact R17247
  · exact R17249
  · exact R17251
  · exact R17253
  · exact R17255
  · exact R17257
  · exact R17259
  · exact R17261
  · exact R17263
  · exact R17265
  · exact R17267
  · exact R17269
  · exact R17271
  · exact R17273
  · exact R17275
  · exact R17277
  · exact R17279
  · exact R17281
  · exact R17283
  · exact R17285
  · exact R17287
  · exact R17289
  · exact R17291
  · exact R17293
  · exact R17295
  · exact R17297
  · exact R17299
  · exact R17301
  · exact R17303
  · exact R17305
  · exact R17307
  · exact R17309
  · exact R17311
  · exact R17313
  · exact R17315
  · exact R17317
  · exact R17319
  · exact R17321
  · exact R17323
  · exact R17325
  · exact R17327
  · exact R17329
  · exact R17331
  · exact R17333
  · exact R17335
  · exact R17337
  · exact R17339
  · exact R17341
  · exact R17343
  · exact R17345
  · exact R17347
  · exact R17349
  · exact R17351
  · exact R17353
  · exact R17355
  · exact R17357
  · exact R17359
  · exact R17361
  · exact R17363
  · exact R17365
  · exact R17367
  · exact R17369
  · exact R17371
  · exact R17373
  · exact R17375
  · exact R17377
  · exact R17379
  · exact R17381
  · exact R17383
  · exact R17385
  · exact R17387
  · exact R17389
  · exact R17391
  · exact R17393
  · exact R17395
  · exact R17397
  · exact R17399
  · exact R17401
  · exact R17403
  · exact R17405
  · exact R17407
  · exact R17409
  · exact R17411
  · exact R17413
  · exact R17415
  · exact R17417
  · exact R17419
  · exact R17421
  · exact R17423
  · exact R17425
  · exact R17427
  · exact R17429
  · exact R17431
  · exact R17433
  · exact R17435
  · exact R17437
  · exact R17439
  · exact R17441
  · exact R17443
  · exact R17445
  · exact R17447
  · exact R17449
  · exact R17451
  · exact R17453
  · exact R17455
  · exact R17457
  · exact R17459
  · exact R17461
  · exact R17463
  · exact R17465
  · exact R17467
  · exact R17469
  · exact R17471
  · exact R17473
  · exact R17475
  · exact R17477
  · exact R17479
  · exact R17481
  · exact R17483
  · exact R17485
  · exact R17487
  · exact R17489
  · exact R17491
  · exact R17493
  · exact R17495
  · exact R17497
  · exact R17499
  · exact R17501
  · exact R17503
  · exact R17505
  · exact R17507
  · exact R17509
  · exact R17511
  · exact R17513
  · exact R17515
  · exact R17517
  · exact R17519
  · exact R17521
  · exact R17523
  · exact R17525
  · exact R17527
  · exact R17529
  · exact R17531
  · exact R17533
  · exact R17535
  · exact R17537
  · exact R17539
  · exact R17541
  · exact R17543
  · exact R17545
  · exact R17547
  · exact R17549
  · exact R17551
  · exact R17553
  · exact R17555
  · exact R17557
  · exact R17559
  · exact R17561
  · exact R17563
  · exact R17565
  · exact R17567
  · exact R17569
  · exact R17571
  · exact R17573
  · exact R17575
  · exact R17577
  · exact R17579
  · exact R17581
  · exact R17583
  · exact R17585
  · exact R17587
  · exact R17589
  · exact R17591
  · exact R17593
  · exact R17595
  · exact R17597
  · exact R17599
  · exact R17601
  · exact R17603
  · exact R17605
  · exact R17607
  · exact R17609
  · exact R17611
  · exact R17613
  · exact R17615
  · exact R17617
  · exact R17619
  · exact R17621
  · exact R17623
  · exact R17625
  · exact R17627
  · exact R17629
  · exact R17631
  · exact R17633
  · exact R17635
  · exact R17637
  · exact R17639
  · exact R17641
  · exact R17643
  · exact R17645
  · exact R17647
  · exact R17649
  · exact R17651
  · exact R17653
  · exact R17655
  · exact R17657
  · exact R17659
  · exact R17661
  · exact R17663
  · exact R17665
  · exact R17667
  · exact R17669
  · exact R17671
  · exact R17673
  · exact R17675
  · exact R17677
  · exact R17679
  · exact R17681
  · exact R17683
  · exact R17685
  · exact R17687
  · exact R17689
  · exact R17691
  · exact R17693
  · exact R17695
  · exact R17697
  · exact R17699
  · exact R17701
  · exact R17703
  · exact R17705
  · exact R17707
  · exact R17709
  · exact R17711
  · exact R17713
  · exact R17715
  · exact R17717
  · exact R17719
  · exact R17721
  · exact R17723
  · exact R17725
  · exact R17727
  · exact R17729
  · exact R17731
  · exact R17733
  · exact R17735
  · exact R17737
  · exact R17739
  · exact R17741
  · exact R17743
  · exact R17745
  · exact R17747
  · exact R17749
  · exact R17751
  · exact R17753
  · exact R17755
  · exact R17757
  · exact R17759
  · exact R17761
  · exact R17763
  · exact R17765
  · exact R17767
  · exact R17769
  · exact R17771
  · exact R17773
  · exact R17775
  · exact R17777
  · exact R17779
  · exact R17781
  · exact R17783
  · exact R17785
  · exact R17787
  · exact R17789
  · exact R17791
  · exact R17793
  · exact R17795
  · exact R17797
  · exact R17799
  · exact R17801
  · exact R17803
  · exact R17805
  · exact R17807
  · exact R17809
  · exact R17811
  · exact R17813
  · exact R17815
  · exact R17817
  · exact R17819
  · exact R17821
  · exact R17823
  · exact R17825
  · exact R17827
  · exact R17829
  · exact R17831
  · exact R17833
  · exact R17835
  · exact R17837
  · exact R17839
  · exact R17841
  · exact R17843
  · exact R17845
  · exact R17847
  · exact R17849
  · exact R17851
  · exact R17853
  · exact R17855
  · exact R17857
  · exact R17859
  · exact R17861
  · exact R17863
  · exact R17865
  · exact R17867
  · exact R17869
  · exact R17871
  · exact R17873
  · exact R17875
  · exact R17877
  · exact R17879
  · exact R17881
  · exact R17883
  · exact R17885
  · exact R17887
  · exact R17889
  · exact R17891
  · exact R17893
  · exact R17895
  · exact R17897
  · exact R17899
  · exact R17901
  · exact R17903
  · exact R17905
  · exact R17907
  · exact R17909
  · exact R17911
  · exact R17913
  · exact R17915
  · exact R17917
  · exact R17919
  · exact R17921
  · exact R17923
  · exact R17925
  · exact R17927
  · exact R17929
  · exact R17931
  · exact R17933
  · exact R17935
  · exact R17937
  · exact R17939
  · exact R17941
  · exact R17943
  · exact R17945
  · exact R17947
  · exact R17949
  · exact R17951
  · exact R17953
  · exact R17955
  · exact R17957
  · exact R17959
  · exact R17961
  · exact R17963
  · exact R17965
  · exact R17967
  · exact R17969
  · exact R17971
  · exact R17973
  · exact R17975
  · exact R17977
  · exact R17979
  · exact R17981
  · exact R17983
  · exact R17985
  · exact R17987
  · exact R17989
  · exact R17991
  · exact R17993
  · exact R17995
  · exact R17997
  · exact R17999
  · exact R18001
  · exact R18003
  · exact R18005
  · exact R18007
  · exact R18009
  · exact R18011
  · exact R18013
  · exact R18015
  · exact R18017
  · exact R18019
  · exact R18021
  · exact R18023
  · exact R18025
  · exact R18027
  · exact R18029
  · exact R18031
  · exact R18033
  · exact R18035
  · exact R18037
  · exact R18039
  · exact R18041
  · exact R18043
  · exact R18045
  · exact R18047
  · exact R18049
  · exact R18051
  · exact R18053
  · exact R18055
  · exact R18057
  · exact R18059
  · exact R18061
  · exact R18063
  · exact R18065
  · exact R18067
  · exact R18069
  · exact R18071
  · exact R18073
  · exact R18075
  · exact R18077
  · exact R18079
  · exact R18081
  · exact R18083
  · exact R18085
  · exact R18087
  · exact R18089
  · exact R18091
  · exact R18093
  · exact R18095
  · exact R18097
  · exact R18099
  · exact R18101
  · exact R18103
  · exact R18105
  · exact R18107
  · exact R18109
  · exact R18111
  · exact R18113
  · exact R18115
  · exact R18117
  · exact R18119
  · exact R18121
  · exact R18123
  · exact R18125
  · exact R18127
  · exact R18129
  · exact R18131
  · exact R18133
  · exact R18135
  · exact R18137
  · exact R18139
  · exact R18141
  · exact R18143
  · exact R18145
  · exact R18147
  · exact R18149
  · exact R18151
  · exact R18153
  · exact R18155
  · exact R18157
  · exact R18159
  · exact R18161
  · exact R18163
  · exact R18165
  · exact R18167
  · exact R18169
  · exact R18171
  · exact R18173
  · exact R18175
  · exact R18177
  · exact R18179
  · exact R18181
  · exact R18183
  · exact R18185
  · exact R18187
  · exact R18189
  · exact R18191
  · exact R18193
  · exact R18195
  · exact R18197
  · exact R18199
  · exact R18201
  · exact R18203
  · exact R18205
  · exact R18207
  · exact R18209
  · exact R18211
  · exact R18213
  · exact R18215
  · exact R18217
  · exact R18219
  · exact R18221
  · exact R18223
  · exact R18225
  · exact R18227
  · exact R18229
  · exact R18231
  · exact R18233
  · exact R18235
  · exact R18237
  · exact R18239
  · exact R18241
  · exact R18243
  · exact R18245
  · exact R18247
  · exact R18249
  · exact R18251
  · exact R18253
  · exact R18255
  · exact R18257
  · exact R18259
  · exact R18261
  · exact R18263
  · exact R18265
  · exact R18267
  · exact R18269
  · exact R18271
  · exact R18273
  · exact R18275
  · exact R18277
  · exact R18279
  · exact R18281
  · exact R18283
  · exact R18285
  · exact R18287
  · exact R18289
  · exact R18291
  · exact R18293
  · exact R18295
  · exact R18297
  · exact R18299
  · exact R18301
  · exact R18303
  · exact R18305
  · exact R18307
  · exact R18309
  · exact R18311
  · exact R18313
  · exact R18315
  · exact R18317
  · exact R18319
  · exact R18321
  · exact R18323
  · exact R18325
  · exact R18327
  · exact R18329
  · exact R18331
  · exact R18333
  · exact R18335
  · exact R18337
  · exact R18339
  · exact R18341
  · exact R18343
  · exact R18345
  · exact R18347
  · exact R18349
  · exact R18351
  · exact R18353
  · exact R18355
  · exact R18357
  · exact R18359
  · exact R18361
  · exact R18363
  · exact R18365
  · exact R18367
  · exact R18369
  · exact R18371
  · exact R18373
  · exact R18375
  · exact R18377
  · exact R18379
  · exact R18381
  · exact R18383
  · exact R18385
  · exact R18387
  · exact R18389
  · exact R18391
  · exact R18393
  · exact R18395
  · exact R18397
  · exact R18399
  · exact R18401
  · exact R18403
  · exact R18405
  · exact R18407
  · exact R18409
  · exact R18411
  · exact R18413
  · exact R18415
  · exact R18417
  · exact R18419
  · exact R18421
  · exact R18423

theorem C4 (j : ℕ) (h1 : 9212 ≤ j) (h2 : j ≤ 9911) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R18425
  · exact R18427
  · exact R18429
  · exact R18431
  · exact R18433
  · exact R18435
  · exact R18437
  · exact R18439
  · exact R18441
  · exact R18443
  · exact R18445
  · exact R18447
  · exact R18449
  · exact R18451
  · exact R18453
  · exact R18455
  · exact R18457
  · exact R18459
  · exact R18461
  · exact R18463
  · exact R18465
  · exact R18467
  · exact R18469
  · exact R18471
  · exact R18473
  · exact R18475
  · exact R18477
  · exact R18479
  · exact R18481
  · exact R18483
  · exact R18485
  · exact R18487
  · exact R18489
  · exact R18491
  · exact R18493
  · exact R18495
  · exact R18497
  · exact R18499
  · exact R18501
  · exact R18503
  · exact R18505
  · exact R18507
  · exact R18509
  · exact R18511
  · exact R18513
  · exact R18515
  · exact R18517
  · exact R18519
  · exact R18521
  · exact R18523
  · exact R18525
  · exact R18527
  · exact R18529
  · exact R18531
  · exact R18533
  · exact R18535
  · exact R18537
  · exact R18539
  · exact R18541
  · exact R18543
  · exact R18545
  · exact R18547
  · exact R18549
  · exact R18551
  · exact R18553
  · exact R18555
  · exact R18557
  · exact R18559
  · exact R18561
  · exact R18563
  · exact R18565
  · exact R18567
  · exact R18569
  · exact R18571
  · exact R18573
  · exact R18575
  · exact R18577
  · exact R18579
  · exact R18581
  · exact R18583
  · exact R18585
  · exact R18587
  · exact R18589
  · exact R18591
  · exact R18593
  · exact R18595
  · exact R18597
  · exact R18599
  · exact R18601
  · exact R18603
  · exact R18605
  · exact R18607
  · exact R18609
  · exact R18611
  · exact R18613
  · exact R18615
  · exact R18617
  · exact R18619
  · exact R18621
  · exact R18623
  · exact R18625
  · exact R18627
  · exact R18629
  · exact R18631
  · exact R18633
  · exact R18635
  · exact R18637
  · exact R18639
  · exact R18641
  · exact R18643
  · exact R18645
  · exact R18647
  · exact R18649
  · exact R18651
  · exact R18653
  · exact R18655
  · exact R18657
  · exact R18659
  · exact R18661
  · exact R18663
  · exact R18665
  · exact R18667
  · exact R18669
  · exact R18671
  · exact R18673
  · exact R18675
  · exact R18677
  · exact R18679
  · exact R18681
  · exact R18683
  · exact R18685
  · exact R18687
  · exact R18689
  · exact R18691
  · exact R18693
  · exact R18695
  · exact R18697
  · exact R18699
  · exact R18701
  · exact R18703
  · exact R18705
  · exact R18707
  · exact R18709
  · exact R18711
  · exact R18713
  · exact R18715
  · exact R18717
  · exact R18719
  · exact R18721
  · exact R18723
  · exact R18725
  · exact R18727
  · exact R18729
  · exact R18731
  · exact R18733
  · exact R18735
  · exact R18737
  · exact R18739
  · exact R18741
  · exact R18743
  · exact R18745
  · exact R18747
  · exact R18749
  · exact R18751
  · exact R18753
  · exact R18755
  · exact R18757
  · exact R18759
  · exact R18761
  · exact R18763
  · exact R18765
  · exact R18767
  · exact R18769
  · exact R18771
  · exact R18773
  · exact R18775
  · exact R18777
  · exact R18779
  · exact R18781
  · exact R18783
  · exact R18785
  · exact R18787
  · exact R18789
  · exact R18791
  · exact R18793
  · exact R18795
  · exact R18797
  · exact R18799
  · exact R18801
  · exact R18803
  · exact R18805
  · exact R18807
  · exact R18809
  · exact R18811
  · exact R18813
  · exact R18815
  · exact R18817
  · exact R18819
  · exact R18821
  · exact R18823
  · exact R18825
  · exact R18827
  · exact R18829
  · exact R18831
  · exact R18833
  · exact R18835
  · exact R18837
  · exact R18839
  · exact R18841
  · exact R18843
  · exact R18845
  · exact R18847
  · exact R18849
  · exact R18851
  · exact R18853
  · exact R18855
  · exact R18857
  · exact R18859
  · exact R18861
  · exact R18863
  · exact R18865
  · exact R18867
  · exact R18869
  · exact R18871
  · exact R18873
  · exact R18875
  · exact R18877
  · exact R18879
  · exact R18881
  · exact R18883
  · exact R18885
  · exact R18887
  · exact R18889
  · exact R18891
  · exact R18893
  · exact R18895
  · exact R18897
  · exact R18899
  · exact R18901
  · exact R18903
  · exact R18905
  · exact R18907
  · exact R18909
  · exact R18911
  · exact R18913
  · exact R18915
  · exact R18917
  · exact R18919
  · exact R18921
  · exact R18923
  · exact R18925
  · exact R18927
  · exact R18929
  · exact R18931
  · exact R18933
  · exact R18935
  · exact R18937
  · exact R18939
  · exact R18941
  · exact R18943
  · exact R18945
  · exact R18947
  · exact R18949
  · exact R18951
  · exact R18953
  · exact R18955
  · exact R18957
  · exact R18959
  · exact R18961
  · exact R18963
  · exact R18965
  · exact R18967
  · exact R18969
  · exact R18971
  · exact R18973
  · exact R18975
  · exact R18977
  · exact R18979
  · exact R18981
  · exact R18983
  · exact R18985
  · exact R18987
  · exact R18989
  · exact R18991
  · exact R18993
  · exact R18995
  · exact R18997
  · exact R18999
  · exact R19001
  · exact R19003
  · exact R19005
  · exact R19007
  · exact R19009
  · exact R19011
  · exact R19013
  · exact R19015
  · exact R19017
  · exact R19019
  · exact R19021
  · exact R19023
  · exact R19025
  · exact R19027
  · exact R19029
  · exact R19031
  · exact R19033
  · exact R19035
  · exact R19037
  · exact R19039
  · exact R19041
  · exact R19043
  · exact R19045
  · exact R19047
  · exact R19049
  · exact R19051
  · exact R19053
  · exact R19055
  · exact R19057
  · exact R19059
  · exact R19061
  · exact R19063
  · exact R19065
  · exact R19067
  · exact R19069
  · exact R19071
  · exact R19073
  · exact R19075
  · exact R19077
  · exact R19079
  · exact R19081
  · exact R19083
  · exact R19085
  · exact R19087
  · exact R19089
  · exact R19091
  · exact R19093
  · exact R19095
  · exact R19097
  · exact R19099
  · exact R19101
  · exact R19103
  · exact R19105
  · exact R19107
  · exact R19109
  · exact R19111
  · exact R19113
  · exact R19115
  · exact R19117
  · exact R19119
  · exact R19121
  · exact R19123
  · exact R19125
  · exact R19127
  · exact R19129
  · exact R19131
  · exact R19133
  · exact R19135
  · exact R19137
  · exact R19139
  · exact R19141
  · exact R19143
  · exact R19145
  · exact R19147
  · exact R19149
  · exact R19151
  · exact R19153
  · exact R19155
  · exact R19157
  · exact R19159
  · exact R19161
  · exact R19163
  · exact R19165
  · exact R19167
  · exact R19169
  · exact R19171
  · exact R19173
  · exact R19175
  · exact R19177
  · exact R19179
  · exact R19181
  · exact R19183
  · exact R19185
  · exact R19187
  · exact R19189
  · exact R19191
  · exact R19193
  · exact R19195
  · exact R19197
  · exact R19199
  · exact R19201
  · exact R19203
  · exact R19205
  · exact R19207
  · exact R19209
  · exact R19211
  · exact R19213
  · exact R19215
  · exact R19217
  · exact R19219
  · exact R19221
  · exact R19223
  · exact R19225
  · exact R19227
  · exact R19229
  · exact R19231
  · exact R19233
  · exact R19235
  · exact R19237
  · exact R19239
  · exact R19241
  · exact R19243
  · exact R19245
  · exact R19247
  · exact R19249
  · exact R19251
  · exact R19253
  · exact R19255
  · exact R19257
  · exact R19259
  · exact R19261
  · exact R19263
  · exact R19265
  · exact R19267
  · exact R19269
  · exact R19271
  · exact R19273
  · exact R19275
  · exact R19277
  · exact R19279
  · exact R19281
  · exact R19283
  · exact R19285
  · exact R19287
  · exact R19289
  · exact R19291
  · exact R19293
  · exact R19295
  · exact R19297
  · exact R19299
  · exact R19301
  · exact R19303
  · exact R19305
  · exact R19307
  · exact R19309
  · exact R19311
  · exact R19313
  · exact R19315
  · exact R19317
  · exact R19319
  · exact R19321
  · exact R19323
  · exact R19325
  · exact R19327
  · exact R19329
  · exact R19331
  · exact R19333
  · exact R19335
  · exact R19337
  · exact R19339
  · exact R19341
  · exact R19343
  · exact R19345
  · exact R19347
  · exact R19349
  · exact R19351
  · exact R19353
  · exact R19355
  · exact R19357
  · exact R19359
  · exact R19361
  · exact R19363
  · exact R19365
  · exact R19367
  · exact R19369
  · exact R19371
  · exact R19373
  · exact R19375
  · exact R19377
  · exact R19379
  · exact R19381
  · exact R19383
  · exact R19385
  · exact R19387
  · exact R19389
  · exact R19391
  · exact R19393
  · exact R19395
  · exact R19397
  · exact R19399
  · exact R19401
  · exact R19403
  · exact R19405
  · exact R19407
  · exact R19409
  · exact R19411
  · exact R19413
  · exact R19415
  · exact R19417
  · exact R19419
  · exact R19421
  · exact R19423
  · exact R19425
  · exact R19427
  · exact R19429
  · exact R19431
  · exact R19433
  · exact R19435
  · exact R19437
  · exact R19439
  · exact R19441
  · exact R19443
  · exact R19445
  · exact R19447
  · exact R19449
  · exact R19451
  · exact R19453
  · exact R19455
  · exact R19457
  · exact R19459
  · exact R19461
  · exact R19463
  · exact R19465
  · exact R19467
  · exact R19469
  · exact R19471
  · exact R19473
  · exact R19475
  · exact R19477
  · exact R19479
  · exact R19481
  · exact R19483
  · exact R19485
  · exact R19487
  · exact R19489
  · exact R19491
  · exact R19493
  · exact R19495
  · exact R19497
  · exact R19499
  · exact R19501
  · exact R19503
  · exact R19505
  · exact R19507
  · exact R19509
  · exact R19511
  · exact R19513
  · exact R19515
  · exact R19517
  · exact R19519
  · exact R19521
  · exact R19523
  · exact R19525
  · exact R19527
  · exact R19529
  · exact R19531
  · exact R19533
  · exact R19535
  · exact R19537
  · exact R19539
  · exact R19541
  · exact R19543
  · exact R19545
  · exact R19547
  · exact R19549
  · exact R19551
  · exact R19553
  · exact R19555
  · exact R19557
  · exact R19559
  · exact R19561
  · exact R19563
  · exact R19565
  · exact R19567
  · exact R19569
  · exact R19571
  · exact R19573
  · exact R19575
  · exact R19577
  · exact R19579
  · exact R19581
  · exact R19583
  · exact R19585
  · exact R19587
  · exact R19589
  · exact R19591
  · exact R19593
  · exact R19595
  · exact R19597
  · exact R19599
  · exact R19601
  · exact R19603
  · exact R19605
  · exact R19607
  · exact R19609
  · exact R19611
  · exact R19613
  · exact R19615
  · exact R19617
  · exact R19619
  · exact R19621
  · exact R19623
  · exact R19625
  · exact R19627
  · exact R19629
  · exact R19631
  · exact R19633
  · exact R19635
  · exact R19637
  · exact R19639
  · exact R19641
  · exact R19643
  · exact R19645
  · exact R19647
  · exact R19649
  · exact R19651
  · exact R19653
  · exact R19655
  · exact R19657
  · exact R19659
  · exact R19661
  · exact R19663
  · exact R19665
  · exact R19667
  · exact R19669
  · exact R19671
  · exact R19673
  · exact R19675
  · exact R19677
  · exact R19679
  · exact R19681
  · exact R19683
  · exact R19685
  · exact R19687
  · exact R19689
  · exact R19691
  · exact R19693
  · exact R19695
  · exact R19697
  · exact R19699
  · exact R19701
  · exact R19703
  · exact R19705
  · exact R19707
  · exact R19709
  · exact R19711
  · exact R19713
  · exact R19715
  · exact R19717
  · exact R19719
  · exact R19721
  · exact R19723
  · exact R19725
  · exact R19727
  · exact R19729
  · exact R19731
  · exact R19733
  · exact R19735
  · exact R19737
  · exact R19739
  · exact R19741
  · exact R19743
  · exact R19745
  · exact R19747
  · exact R19749
  · exact R19751
  · exact R19753
  · exact R19755
  · exact R19757
  · exact R19759
  · exact R19761
  · exact R19763
  · exact R19765
  · exact R19767
  · exact R19769
  · exact R19771
  · exact R19773
  · exact R19775
  · exact R19777
  · exact R19779
  · exact R19781
  · exact R19783
  · exact R19785
  · exact R19787
  · exact R19789
  · exact R19791
  · exact R19793
  · exact R19795
  · exact R19797
  · exact R19799
  · exact R19801
  · exact R19803
  · exact R19805
  · exact R19807
  · exact R19809
  · exact R19811
  · exact R19813
  · exact R19815
  · exact R19817
  · exact R19819
  · exact R19821
  · exact R19823

theorem C5 (j : ℕ) (h1 : 9912 ≤ j) (h2 : j ≤ 9999) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R19825
  · exact R19827
  · exact R19829
  · exact R19831
  · exact R19833
  · exact R19835
  · exact R19837
  · exact R19839
  · exact R19841
  · exact R19843
  · exact R19845
  · exact R19847
  · exact R19849
  · exact R19851
  · exact R19853
  · exact R19855
  · exact R19857
  · exact R19859
  · exact R19861
  · exact R19863
  · exact R19865
  · exact R19867
  · exact R19869
  · exact R19871
  · exact R19873
  · exact R19875
  · exact R19877
  · exact R19879
  · exact R19881
  · exact R19883
  · exact R19885
  · exact R19887
  · exact R19889
  · exact R19891
  · exact R19893
  · exact R19895
  · exact R19897
  · exact R19899
  · exact R19901
  · exact R19903
  · exact R19905
  · exact R19907
  · exact R19909
  · exact R19911
  · exact R19913
  · exact R19915
  · exact R19917
  · exact R19919
  · exact R19921
  · exact R19923
  · exact R19925
  · exact R19927
  · exact R19929
  · exact R19931
  · exact R19933
  · exact R19935
  · exact R19937
  · exact R19939
  · exact R19941
  · exact R19943
  · exact R19945
  · exact R19947
  · exact R19949
  · exact R19951
  · exact R19953
  · exact R19955
  · exact R19957
  · exact R19959
  · exact R19961
  · exact R19963
  · exact R19965
  · exact R19967
  · exact R19969
  · exact R19971
  · exact R19973
  · exact R19975
  · exact R19977
  · exact R19979
  · exact R19981
  · exact R19983
  · exact R19985
  · exact R19987
  · exact R19989
  · exact R19991
  · exact R19993
  · exact R19995
  · exact R19997
  · exact R19999

theorem solution (m : ℕ) (hm : 0 < m) (hodd : Odd m) (hle : m ≤ 20000) :
    ∃ k : ℕ, syracuseStep^[k] m = 1 := by
  rcases Nat.lt_or_ge m 12825 with hlo | hlo
  · exact syracuse_reaches_one_below_12825 m hm hodd (by omega)
  obtain ⟨j, rfl⟩ : ∃ j, m = 2 * j + 1 := by obtain ⟨t, ht⟩ := hodd; exact ⟨t, by omega⟩
  rcases Nat.lt_or_ge j 7112 with h0 | h0
  · exact C0 j (by omega) (by omega)
  rcases Nat.lt_or_ge j 7812 with h1 | h1
  · exact C1 j (by omega) (by omega)
  rcases Nat.lt_or_ge j 8512 with h2 | h2
  · exact C2 j (by omega) (by omega)
  rcases Nat.lt_or_ge j 9212 with h3 | h3
  · exact C3 j (by omega) (by omega)
  rcases Nat.lt_or_ge j 9912 with h4 | h4
  · exact C4 j (by omega) (by omega)
  exact C5 j (by omega) (by omega)
