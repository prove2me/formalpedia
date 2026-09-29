-- Prove2me | solution 1 for syracuse_reaches_one_below_51120
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T05:51:01.713831+00:00
-- url     : https://prove2.me/submissions/2f46278f-163d-493c-93aa-1963c7df821c

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_reaches_one_below_47119

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
theorem B (n : ℕ) (h1 : 0 < n) (h2 : Odd n) (h3 : n ≤ 47118) : Reach n :=
  syracuse_reaches_one_below_47119 n h1 h2 h3
theorem R65605 : Reach 65605 := rs (se 4 (by rfl) ⟨6150, by rfl⟩) (B 12301 (by norm_num) ⟨6150, by rfl⟩ (by norm_num))
theorem R327989 : Reach 327989 := rs (se 5 (by rfl) ⟨15374, by rfl⟩) (B 30749 (by norm_num) ⟨15374, by rfl⟩ (by norm_num))
theorem R164213 : Reach 164213 := rs (se 5 (by rfl) ⟨7697, by rfl⟩) (B 15395 (by norm_num) ⟨7697, by rfl⟩ (by norm_num))
theorem R393653 : Reach 393653 := rs (se 5 (by rfl) ⟨18452, by rfl⟩) (B 36905 (by norm_num) ⟨18452, by rfl⟩ (by norm_num))
theorem R164501 : Reach 164501 := rs (se 6 (by rfl) ⟨3855, by rfl⟩) (B 7711 (by norm_num) ⟨3855, by rfl⟩ (by norm_num))
theorem R164645 : Reach 164645 := rs (se 4 (by rfl) ⟨15435, by rfl⟩) (B 30871 (by norm_num) ⟨15435, by rfl⟩ (by norm_num))
theorem R66469 : Reach 66469 := rs (se 4 (by rfl) ⟨6231, by rfl⟩) (B 12463 (by norm_num) ⟨6231, by rfl⟩ (by norm_num))
theorem R459989 : Reach 459989 := rs (se 7 (by rfl) ⟨5390, by rfl⟩) (B 10781 (by norm_num) ⟨5390, by rfl⟩ (by norm_num))
theorem R165077 : Reach 165077 := rs (se 7 (by rfl) ⟨1934, by rfl⟩) (B 3869 (by norm_num) ⟨1934, by rfl⟩ (by norm_num))
theorem R165125 : Reach 165125 := rs (se 4 (by rfl) ⟨15480, by rfl⟩) (B 30961 (by norm_num) ⟨15480, by rfl⟩ (by norm_num))
theorem R230917 : Reach 230917 := rs (se 4 (by rfl) ⟨21648, by rfl⟩) (B 43297 (by norm_num) ⟨21648, by rfl⟩ (by norm_num))
theorem R362069 : Reach 362069 := rs (se 8 (by rfl) ⟨2121, by rfl⟩) (B 4243 (by norm_num) ⟨2121, by rfl⟩ (by norm_num))
theorem R165509 : Reach 165509 := rs (se 4 (by rfl) ⟨15516, by rfl⟩) (B 31033 (by norm_num) ⟨15516, by rfl⟩ (by norm_num))
theorem R132853 : Reach 132853 := rs (se 5 (by rfl) ⟨6227, by rfl⟩) (B 12455 (by norm_num) ⟨6227, by rfl⟩ (by norm_num))
theorem R100133 : Reach 100133 := rs (se 4 (by rfl) ⟨9387, by rfl⟩) (B 18775 (by norm_num) ⟨9387, by rfl⟩ (by norm_num))
theorem R132949 : Reach 132949 := rs (se 9 (by rfl) ⟨389, by rfl⟩) (B 779 (by norm_num) ⟨389, by rfl⟩ (by norm_num))
theorem R67501 : Reach 67501 := rs (se 3 (by rfl) ⟨12656, by rfl⟩) (B 25313 (by norm_num) ⟨12656, by rfl⟩ (by norm_num))
theorem R755669 : Reach 755669 := rs (se 7 (by rfl) ⟨8855, by rfl⟩) (B 17711 (by norm_num) ⟨8855, by rfl⟩ (by norm_num))
theorem R165941 : Reach 165941 := rs (se 5 (by rfl) ⟨7778, by rfl⟩) (B 15557 (by norm_num) ⟨7778, by rfl⟩ (by norm_num))
theorem R133285 : Reach 133285 := rs (se 4 (by rfl) ⟨12495, by rfl⟩) (B 24991 (by norm_num) ⟨12495, by rfl⟩ (by norm_num))
theorem R100757 : Reach 100757 := rs (se 6 (by rfl) ⟨2361, by rfl⟩) (B 4723 (by norm_num) ⟨2361, by rfl⟩ (by norm_num))
theorem R166373 : Reach 166373 := rs (se 4 (by rfl) ⟨15597, by rfl⟩) (B 31195 (by norm_num) ⟨15597, by rfl⟩ (by norm_num))
theorem R68117 : Reach 68117 := rs (se 6 (by rfl) ⟨1596, by rfl⟩) (B 3193 (by norm_num) ⟨1596, by rfl⟩ (by norm_num))
theorem R232085 : Reach 232085 := rs (se 6 (by rfl) ⟨5439, by rfl⟩) (B 10879 (by norm_num) ⟨5439, by rfl⟩ (by norm_num))
theorem R68293 : Reach 68293 := rs (se 4 (by rfl) ⟨6402, by rfl⟩) (B 12805 (by norm_num) ⟨6402, by rfl⟩ (by norm_num))
theorem R166805 : Reach 166805 := rs (se 6 (by rfl) ⟨3909, by rfl⟩) (B 7819 (by norm_num) ⟨3909, by rfl⟩ (by norm_num))
theorem R68629 : Reach 68629 := rs (se 6 (by rfl) ⟨1608, by rfl⟩) (B 3217 (by norm_num) ⟨1608, by rfl⟩ (by norm_num))
theorem R166949 : Reach 166949 := rs (se 4 (by rfl) ⟨15651, by rfl⟩) (B 31303 (by norm_num) ⟨15651, by rfl⟩ (by norm_num))
theorem R68677 : Reach 68677 := rs (se 4 (by rfl) ⟨6438, by rfl⟩) (B 12877 (by norm_num) ⟨6438, by rfl⟩ (by norm_num))
theorem R68845 : Reach 68845 := rs (se 3 (by rfl) ⟨12908, by rfl⟩) (B 25817 (by norm_num) ⟨12908, by rfl⟩ (by norm_num))
theorem R101645 : Reach 101645 := rs (se 3 (by rfl) ⟨19058, by rfl⟩) (B 38117 (by norm_num) ⟨19058, by rfl⟩ (by norm_num))
theorem R167237 : Reach 167237 := rs (se 4 (by rfl) ⟨15678, by rfl⟩) (B 31357 (by norm_num) ⟨15678, by rfl⟩ (by norm_num))
theorem R134581 : Reach 134581 := rs (se 5 (by rfl) ⟨6308, by rfl⟩) (B 12617 (by norm_num) ⟨6308, by rfl⟩ (by norm_num))
theorem R101893 : Reach 101893 := rs (se 4 (by rfl) ⟨9552, by rfl⟩) (B 19105 (by norm_num) ⟨9552, by rfl⟩ (by norm_num))
theorem R69221 : Reach 69221 := rs (se 4 (by rfl) ⟨6489, by rfl⟩) (B 12979 (by norm_num) ⟨6489, by rfl⟩ (by norm_num))
theorem R167669 : Reach 167669 := rs (se 5 (by rfl) ⟨7859, by rfl⟩) (B 15719 (by norm_num) ⟨7859, by rfl⟩ (by norm_num))
theorem R102397 : Reach 102397 := rs (se 3 (by rfl) ⟨19199, by rfl⟩) (B 38399 (by norm_num) ⟨19199, by rfl⟩ (by norm_num))
theorem R168101 : Reach 168101 := rs (se 4 (by rfl) ⟨15759, by rfl⟩) (B 31519 (by norm_num) ⟨15759, by rfl⟩ (by norm_num))
theorem R102565 : Reach 102565 := rs (se 4 (by rfl) ⟨9615, by rfl⟩) (B 19231 (by norm_num) ⟨9615, by rfl⟩ (by norm_num))
theorem R69925 : Reach 69925 := rs (se 4 (by rfl) ⟨6555, by rfl⟩) (B 13111 (by norm_num) ⟨6555, by rfl⟩ (by norm_num))
theorem R135685 : Reach 135685 := rs (se 4 (by rfl) ⟨12720, by rfl⟩) (B 25441 (by norm_num) ⟨12720, by rfl⟩ (by norm_num))
theorem R168533 : Reach 168533 := rs (se 8 (by rfl) ⟨987, by rfl⟩) (B 1975 (by norm_num) ⟨987, by rfl⟩ (by norm_num))
theorem R103285 : Reach 103285 := rs (se 5 (by rfl) ⟨4841, by rfl⟩) (B 9683 (by norm_num) ⟨4841, by rfl⟩ (by norm_num))
theorem R70645 : Reach 70645 := rs (se 5 (by rfl) ⟨3311, by rfl⟩) (B 6623 (by norm_num) ⟨3311, by rfl⟩ (by norm_num))
theorem R168965 : Reach 168965 := rs (se 4 (by rfl) ⟨15840, by rfl⟩) (B 31681 (by norm_num) ⟨15840, by rfl⟩ (by norm_num))
theorem R70685 : Reach 70685 := rs (se 3 (by rfl) ⟨13253, by rfl⟩) (B 26507 (by norm_num) ⟨13253, by rfl⟩ (by norm_num))
theorem R70709 : Reach 70709 := rs (se 5 (by rfl) ⟨3314, by rfl⟩) (B 6629 (by norm_num) ⟨3314, by rfl⟩ (by norm_num))
theorem R70733 : Reach 70733 := rs (se 3 (by rfl) ⟨13262, by rfl⟩) (B 26525 (by norm_num) ⟨13262, by rfl⟩ (by norm_num))
theorem R70757 : Reach 70757 := rs (se 4 (by rfl) ⟨6633, by rfl⟩) (B 13267 (by norm_num) ⟨6633, by rfl⟩ (by norm_num))
theorem R70781 : Reach 70781 := rs (se 3 (by rfl) ⟨13271, by rfl⟩) (B 26543 (by norm_num) ⟨13271, by rfl⟩ (by norm_num))
theorem R70805 : Reach 70805 := rs (se 6 (by rfl) ⟨1659, by rfl⟩) (B 3319 (by norm_num) ⟨1659, by rfl⟩ (by norm_num))
theorem R70829 : Reach 70829 := rs (se 3 (by rfl) ⟨13280, by rfl⟩) (B 26561 (by norm_num) ⟨13280, by rfl⟩ (by norm_num))
theorem R70853 : Reach 70853 := rs (se 4 (by rfl) ⟨6642, by rfl⟩) (B 13285 (by norm_num) ⟨6642, by rfl⟩ (by norm_num))
theorem R103621 : Reach 103621 := rs (se 4 (by rfl) ⟨9714, by rfl⟩) (B 19429 (by norm_num) ⟨9714, by rfl⟩ (by norm_num))
theorem R70877 : Reach 70877 := rs (se 3 (by rfl) ⟨13289, by rfl⟩) (B 26579 (by norm_num) ⟨13289, by rfl⟩ (by norm_num))
theorem R70901 : Reach 70901 := rs (se 5 (by rfl) ⟨3323, by rfl⟩) (B 6647 (by norm_num) ⟨3323, by rfl⟩ (by norm_num))
theorem R70925 : Reach 70925 := rs (se 3 (by rfl) ⟨13298, by rfl⟩) (B 26597 (by norm_num) ⟨13298, by rfl⟩ (by norm_num))
theorem R70949 : Reach 70949 := rs (se 4 (by rfl) ⟨6651, by rfl⟩) (B 13303 (by norm_num) ⟨6651, by rfl⟩ (by norm_num))
theorem R70973 : Reach 70973 := rs (se 3 (by rfl) ⟨13307, by rfl⟩) (B 26615 (by norm_num) ⟨13307, by rfl⟩ (by norm_num))
theorem R70997 : Reach 70997 := rs (se 14 (by rfl) ⟨6, by rfl⟩) (B 13 (by norm_num) ⟨6, by rfl⟩ (by norm_num))
theorem R103781 : Reach 103781 := rs (se 4 (by rfl) ⟨9729, by rfl⟩) (B 19459 (by norm_num) ⟨9729, by rfl⟩ (by norm_num))
theorem R71021 : Reach 71021 := rs (se 3 (by rfl) ⟨13316, by rfl⟩) (B 26633 (by norm_num) ⟨13316, by rfl⟩ (by norm_num))
theorem R71045 : Reach 71045 := rs (se 4 (by rfl) ⟨6660, by rfl⟩) (B 13321 (by norm_num) ⟨6660, by rfl⟩ (by norm_num))
theorem R71069 : Reach 71069 := rs (se 3 (by rfl) ⟨13325, by rfl⟩) (B 26651 (by norm_num) ⟨13325, by rfl⟩ (by norm_num))
theorem R71093 : Reach 71093 := rs (se 5 (by rfl) ⟨3332, by rfl⟩) (B 6665 (by norm_num) ⟨3332, by rfl⟩ (by norm_num))
theorem R169397 : Reach 169397 := rs (se 5 (by rfl) ⟨7940, by rfl⟩) (B 15881 (by norm_num) ⟨7940, by rfl⟩ (by norm_num))
theorem R71117 : Reach 71117 := rs (se 3 (by rfl) ⟨13334, by rfl⟩) (B 26669 (by norm_num) ⟨13334, by rfl⟩ (by norm_num))
theorem R71141 : Reach 71141 := rs (se 4 (by rfl) ⟨6669, by rfl⟩) (B 13339 (by norm_num) ⟨6669, by rfl⟩ (by norm_num))
theorem R71165 : Reach 71165 := rs (se 3 (by rfl) ⟨13343, by rfl⟩) (B 26687 (by norm_num) ⟨13343, by rfl⟩ (by norm_num))
theorem R71189 : Reach 71189 := rs (se 6 (by rfl) ⟨1668, by rfl⟩) (B 3337 (by norm_num) ⟨1668, by rfl⟩ (by norm_num))
theorem R71213 : Reach 71213 := rs (se 3 (by rfl) ⟨13352, by rfl⟩) (B 26705 (by norm_num) ⟨13352, by rfl⟩ (by norm_num))
theorem R71237 : Reach 71237 := rs (se 4 (by rfl) ⟨6678, by rfl⟩) (B 13357 (by norm_num) ⟨6678, by rfl⟩ (by norm_num))
theorem R71261 : Reach 71261 := rs (se 3 (by rfl) ⟨13361, by rfl⟩) (B 26723 (by norm_num) ⟨13361, by rfl⟩ (by norm_num))
theorem R71285 : Reach 71285 := rs (se 5 (by rfl) ⟨3341, by rfl⟩) (B 6683 (by norm_num) ⟨3341, by rfl⟩ (by norm_num))
theorem R71309 : Reach 71309 := rs (se 3 (by rfl) ⟨13370, by rfl⟩) (B 26741 (by norm_num) ⟨13370, by rfl⟩ (by norm_num))
theorem R71317 : Reach 71317 := rs (se 6 (by rfl) ⟨1671, by rfl⟩) (B 3343 (by norm_num) ⟨1671, by rfl⟩ (by norm_num))
theorem R71333 : Reach 71333 := rs (se 4 (by rfl) ⟨6687, by rfl⟩) (B 13375 (by norm_num) ⟨6687, by rfl⟩ (by norm_num))
theorem R202405 : Reach 202405 := rs (se 4 (by rfl) ⟨18975, by rfl⟩) (B 37951 (by norm_num) ⟨18975, by rfl⟩ (by norm_num))
theorem R136885 : Reach 136885 := rs (se 5 (by rfl) ⟨6416, by rfl⟩) (B 12833 (by norm_num) ⟨6416, by rfl⟩ (by norm_num))
theorem R71357 : Reach 71357 := rs (se 3 (by rfl) ⟨13379, by rfl⟩) (B 26759 (by norm_num) ⟨13379, by rfl⟩ (by norm_num))
theorem R71381 : Reach 71381 := rs (se 7 (by rfl) ⟨836, by rfl⟩) (B 1673 (by norm_num) ⟨836, by rfl⟩ (by norm_num))
theorem R71405 : Reach 71405 := rs (se 3 (by rfl) ⟨13388, by rfl⟩) (B 26777 (by norm_num) ⟨13388, by rfl⟩ (by norm_num))
theorem R71429 : Reach 71429 := rs (se 4 (by rfl) ⟨6696, by rfl⟩) (B 13393 (by norm_num) ⟨6696, by rfl⟩ (by norm_num))
theorem R71437 : Reach 71437 := rs (se 3 (by rfl) ⟨13394, by rfl⟩) (B 26789 (by norm_num) ⟨13394, by rfl⟩ (by norm_num))
theorem R71453 : Reach 71453 := rs (se 3 (by rfl) ⟨13397, by rfl⟩) (B 26795 (by norm_num) ⟨13397, by rfl⟩ (by norm_num))
theorem R71477 : Reach 71477 := rs (se 5 (by rfl) ⟨3350, by rfl⟩) (B 6701 (by norm_num) ⟨3350, by rfl⟩ (by norm_num))
theorem R71501 : Reach 71501 := rs (se 3 (by rfl) ⟨13406, by rfl⟩) (B 26813 (by norm_num) ⟨13406, by rfl⟩ (by norm_num))
theorem R71525 : Reach 71525 := rs (se 4 (by rfl) ⟨6705, by rfl⟩) (B 13411 (by norm_num) ⟨6705, by rfl⟩ (by norm_num))
theorem R169829 : Reach 169829 := rs (se 4 (by rfl) ⟨15921, by rfl⟩) (B 31843 (by norm_num) ⟨15921, by rfl⟩ (by norm_num))
theorem R71533 : Reach 71533 := rs (se 3 (by rfl) ⟨13412, by rfl⟩) (B 26825 (by norm_num) ⟨13412, by rfl⟩ (by norm_num))
theorem R71549 : Reach 71549 := rs (se 3 (by rfl) ⟨13415, by rfl⟩) (B 26831 (by norm_num) ⟨13415, by rfl⟩ (by norm_num))
theorem R71573 : Reach 71573 := rs (se 6 (by rfl) ⟨1677, by rfl⟩) (B 3355 (by norm_num) ⟨1677, by rfl⟩ (by norm_num))
theorem R71597 : Reach 71597 := rs (se 3 (by rfl) ⟨13424, by rfl⟩) (B 26849 (by norm_num) ⟨13424, by rfl⟩ (by norm_num))
theorem R71621 : Reach 71621 := rs (se 4 (by rfl) ⟨6714, by rfl⟩) (B 13429 (by norm_num) ⟨6714, by rfl⟩ (by norm_num))
theorem R71645 : Reach 71645 := rs (se 3 (by rfl) ⟨13433, by rfl⟩) (B 26867 (by norm_num) ⟨13433, by rfl⟩ (by norm_num))
theorem R137189 : Reach 137189 := rs (se 4 (by rfl) ⟨12861, by rfl⟩) (B 25723 (by norm_num) ⟨12861, by rfl⟩ (by norm_num))
theorem R71669 : Reach 71669 := rs (se 5 (by rfl) ⟨3359, by rfl⟩) (B 6719 (by norm_num) ⟨3359, by rfl⟩ (by norm_num))
theorem R71693 : Reach 71693 := rs (se 3 (by rfl) ⟨13442, by rfl⟩) (B 26885 (by norm_num) ⟨13442, by rfl⟩ (by norm_num))
theorem R71717 : Reach 71717 := rs (se 4 (by rfl) ⟨6723, by rfl⟩) (B 13447 (by norm_num) ⟨6723, by rfl⟩ (by norm_num))
theorem R71741 : Reach 71741 := rs (se 3 (by rfl) ⟨13451, by rfl⟩) (B 26903 (by norm_num) ⟨13451, by rfl⟩ (by norm_num))
theorem R71765 : Reach 71765 := rs (se 8 (by rfl) ⟨420, by rfl⟩) (B 841 (by norm_num) ⟨420, by rfl⟩ (by norm_num))
theorem R71789 : Reach 71789 := rs (se 3 (by rfl) ⟨13460, by rfl⟩) (B 26921 (by norm_num) ⟨13460, by rfl⟩ (by norm_num))
theorem R71813 : Reach 71813 := rs (se 4 (by rfl) ⟨6732, by rfl⟩) (B 13465 (by norm_num) ⟨6732, by rfl⟩ (by norm_num))
theorem R71837 : Reach 71837 := rs (se 3 (by rfl) ⟨13469, by rfl⟩) (B 26939 (by norm_num) ⟨13469, by rfl⟩ (by norm_num))
theorem R71861 : Reach 71861 := rs (se 5 (by rfl) ⟨3368, by rfl⟩) (B 6737 (by norm_num) ⟨3368, by rfl⟩ (by norm_num))
theorem R71885 : Reach 71885 := rs (se 3 (by rfl) ⟨13478, by rfl⟩) (B 26957 (by norm_num) ⟨13478, by rfl⟩ (by norm_num))
theorem R104669 : Reach 104669 := rs (se 3 (by rfl) ⟨19625, by rfl⟩) (B 39251 (by norm_num) ⟨19625, by rfl⟩ (by norm_num))
theorem R202981 : Reach 202981 := rs (se 4 (by rfl) ⟨19029, by rfl⟩) (B 38059 (by norm_num) ⟨19029, by rfl⟩ (by norm_num))
theorem R71909 : Reach 71909 := rs (se 4 (by rfl) ⟨6741, by rfl⟩) (B 13483 (by norm_num) ⟨6741, by rfl⟩ (by norm_num))
theorem R71933 : Reach 71933 := rs (se 3 (by rfl) ⟨13487, by rfl⟩) (B 26975 (by norm_num) ⟨13487, by rfl⟩ (by norm_num))
theorem R71957 : Reach 71957 := rs (se 6 (by rfl) ⟨1686, by rfl⟩) (B 3373 (by norm_num) ⟨1686, by rfl⟩ (by norm_num))
theorem R170261 : Reach 170261 := rs (se 6 (by rfl) ⟨3990, by rfl⟩) (B 7981 (by norm_num) ⟨3990, by rfl⟩ (by norm_num))
theorem R366869 : Reach 366869 := rs (se 6 (by rfl) ⟨8598, by rfl⟩) (B 17197 (by norm_num) ⟨8598, by rfl⟩ (by norm_num))
theorem R71981 : Reach 71981 := rs (se 3 (by rfl) ⟨13496, by rfl⟩) (B 26993 (by norm_num) ⟨13496, by rfl⟩ (by norm_num))
theorem R72005 : Reach 72005 := rs (se 4 (by rfl) ⟨6750, by rfl⟩) (B 13501 (by norm_num) ⟨6750, by rfl⟩ (by norm_num))
theorem R104789 : Reach 104789 := rs (se 10 (by rfl) ⟨153, by rfl⟩) (B 307 (by norm_num) ⟨153, by rfl⟩ (by norm_num))
theorem R72029 : Reach 72029 := rs (se 3 (by rfl) ⟨13505, by rfl⟩) (B 27011 (by norm_num) ⟨13505, by rfl⟩ (by norm_num))
theorem R72053 : Reach 72053 := rs (se 5 (by rfl) ⟨3377, by rfl⟩) (B 6755 (by norm_num) ⟨3377, by rfl⟩ (by norm_num))
theorem R72077 : Reach 72077 := rs (se 3 (by rfl) ⟨13514, by rfl⟩) (B 27029 (by norm_num) ⟨13514, by rfl⟩ (by norm_num))
theorem R72101 : Reach 72101 := rs (se 4 (by rfl) ⟨6759, by rfl⟩) (B 13519 (by norm_num) ⟨6759, by rfl⟩ (by norm_num))
theorem R72125 : Reach 72125 := rs (se 3 (by rfl) ⟨13523, by rfl⟩) (B 27047 (by norm_num) ⟨13523, by rfl⟩ (by norm_num))
theorem R72149 : Reach 72149 := rs (se 7 (by rfl) ⟨845, by rfl⟩) (B 1691 (by norm_num) ⟨845, by rfl⟩ (by norm_num))
theorem R72173 : Reach 72173 := rs (se 3 (by rfl) ⟨13532, by rfl⟩) (B 27065 (by norm_num) ⟨13532, by rfl⟩ (by norm_num))
theorem R72197 : Reach 72197 := rs (se 4 (by rfl) ⟨6768, by rfl⟩) (B 13537 (by norm_num) ⟨6768, by rfl⟩ (by norm_num))
theorem R72221 : Reach 72221 := rs (se 3 (by rfl) ⟨13541, by rfl⟩) (B 27083 (by norm_num) ⟨13541, by rfl⟩ (by norm_num))
theorem R72245 : Reach 72245 := rs (se 5 (by rfl) ⟨3386, by rfl⟩) (B 6773 (by norm_num) ⟨3386, by rfl⟩ (by norm_num))
theorem R72269 : Reach 72269 := rs (se 3 (by rfl) ⟨13550, by rfl⟩) (B 27101 (by norm_num) ⟨13550, by rfl⟩ (by norm_num))
theorem R72293 : Reach 72293 := rs (se 4 (by rfl) ⟨6777, by rfl⟩) (B 13555 (by norm_num) ⟨6777, by rfl⟩ (by norm_num))
theorem R203381 : Reach 203381 := rs (se 5 (by rfl) ⟨9533, by rfl⟩) (B 19067 (by norm_num) ⟨9533, by rfl⟩ (by norm_num))
theorem R72317 : Reach 72317 := rs (se 3 (by rfl) ⟨13559, by rfl⟩) (B 27119 (by norm_num) ⟨13559, by rfl⟩ (by norm_num))
theorem R72325 : Reach 72325 := rs (se 4 (by rfl) ⟨6780, by rfl⟩) (B 13561 (by norm_num) ⟨6780, by rfl⟩ (by norm_num))
theorem R72341 : Reach 72341 := rs (se 6 (by rfl) ⟨1695, by rfl⟩) (B 3391 (by norm_num) ⟨1695, by rfl⟩ (by norm_num))
theorem R72365 : Reach 72365 := rs (se 3 (by rfl) ⟨13568, by rfl⟩) (B 27137 (by norm_num) ⟨13568, by rfl⟩ (by norm_num))
theorem R170677 : Reach 170677 := rs (se 5 (by rfl) ⟨8000, by rfl⟩) (B 16001 (by norm_num) ⟨8000, by rfl⟩ (by norm_num))
theorem R72389 : Reach 72389 := rs (se 4 (by rfl) ⟨6786, by rfl⟩) (B 13573 (by norm_num) ⟨6786, by rfl⟩ (by norm_num))
theorem R170693 : Reach 170693 := rs (se 4 (by rfl) ⟨16002, by rfl⟩) (B 32005 (by norm_num) ⟨16002, by rfl⟩ (by norm_num))
theorem R72413 : Reach 72413 := rs (se 3 (by rfl) ⟨13577, by rfl⟩) (B 27155 (by norm_num) ⟨13577, by rfl⟩ (by norm_num))
theorem R72437 : Reach 72437 := rs (se 5 (by rfl) ⟨3395, by rfl⟩) (B 6791 (by norm_num) ⟨3395, by rfl⟩ (by norm_num))
theorem R72461 : Reach 72461 := rs (se 3 (by rfl) ⟨13586, by rfl⟩) (B 27173 (by norm_num) ⟨13586, by rfl⟩ (by norm_num))
theorem R72485 : Reach 72485 := rs (se 4 (by rfl) ⟨6795, by rfl⟩) (B 13591 (by norm_num) ⟨6795, by rfl⟩ (by norm_num))
theorem R72509 : Reach 72509 := rs (se 3 (by rfl) ⟨13595, by rfl⟩) (B 27191 (by norm_num) ⟨13595, by rfl⟩ (by norm_num))
theorem R170837 : Reach 170837 := rs (se 9 (by rfl) ⟨500, by rfl⟩) (B 1001 (by norm_num) ⟨500, by rfl⟩ (by norm_num))
theorem R105301 : Reach 105301 := rs (se 9 (by rfl) ⟨308, by rfl⟩) (B 617 (by norm_num) ⟨308, by rfl⟩ (by norm_num))
theorem R72533 : Reach 72533 := rs (se 9 (by rfl) ⟨212, by rfl⟩) (B 425 (by norm_num) ⟨212, by rfl⟩ (by norm_num))
theorem R72557 : Reach 72557 := rs (se 3 (by rfl) ⟨13604, by rfl⟩) (B 27209 (by norm_num) ⟨13604, by rfl⟩ (by norm_num))
theorem R72581 : Reach 72581 := rs (se 4 (by rfl) ⟨6804, by rfl⟩) (B 13609 (by norm_num) ⟨6804, by rfl⟩ (by norm_num))
theorem R72605 : Reach 72605 := rs (se 3 (by rfl) ⟨13613, by rfl⟩) (B 27227 (by norm_num) ⟨13613, by rfl⟩ (by norm_num))
theorem R72629 : Reach 72629 := rs (se 5 (by rfl) ⟨3404, by rfl⟩) (B 6809 (by norm_num) ⟨3404, by rfl⟩ (by norm_num))
theorem R72653 : Reach 72653 := rs (se 3 (by rfl) ⟨13622, by rfl⟩) (B 27245 (by norm_num) ⟨13622, by rfl⟩ (by norm_num))
theorem R105421 : Reach 105421 := rs (se 3 (by rfl) ⟨19766, by rfl⟩) (B 39533 (by norm_num) ⟨19766, by rfl⟩ (by norm_num))
theorem R72677 : Reach 72677 := rs (se 4 (by rfl) ⟨6813, by rfl⟩) (B 13627 (by norm_num) ⟨6813, by rfl⟩ (by norm_num))
theorem R72701 : Reach 72701 := rs (se 3 (by rfl) ⟨13631, by rfl⟩) (B 27263 (by norm_num) ⟨13631, by rfl⟩ (by norm_num))
theorem R72725 : Reach 72725 := rs (se 6 (by rfl) ⟨1704, by rfl⟩) (B 3409 (by norm_num) ⟨1704, by rfl⟩ (by norm_num))
theorem R564245 : Reach 564245 := rs (se 6 (by rfl) ⟨13224, by rfl⟩) (B 26449 (by norm_num) ⟨13224, by rfl⟩ (by norm_num))
theorem R72749 : Reach 72749 := rs (se 3 (by rfl) ⟨13640, by rfl⟩) (B 27281 (by norm_num) ⟨13640, by rfl⟩ (by norm_num))
theorem R269365 : Reach 269365 := rs (se 5 (by rfl) ⟨12626, by rfl⟩) (B 25253 (by norm_num) ⟨12626, by rfl⟩ (by norm_num))
theorem R72773 : Reach 72773 := rs (se 4 (by rfl) ⟨6822, by rfl⟩) (B 13645 (by norm_num) ⟨6822, by rfl⟩ (by norm_num))
theorem R72797 : Reach 72797 := rs (se 3 (by rfl) ⟨13649, by rfl⟩) (B 27299 (by norm_num) ⟨13649, by rfl⟩ (by norm_num))
theorem R72821 : Reach 72821 := rs (se 5 (by rfl) ⟨3413, by rfl⟩) (B 6827 (by norm_num) ⟨3413, by rfl⟩ (by norm_num))
theorem R171125 : Reach 171125 := rs (se 5 (by rfl) ⟨8021, by rfl⟩) (B 16043 (by norm_num) ⟨8021, by rfl⟩ (by norm_num))
theorem R72845 : Reach 72845 := rs (se 3 (by rfl) ⟨13658, by rfl⟩) (B 27317 (by norm_num) ⟨13658, by rfl⟩ (by norm_num))
theorem R72869 : Reach 72869 := rs (se 4 (by rfl) ⟨6831, by rfl⟩) (B 13663 (by norm_num) ⟨6831, by rfl⟩ (by norm_num))
theorem R72893 : Reach 72893 := rs (se 3 (by rfl) ⟨13667, by rfl⟩) (B 27335 (by norm_num) ⟨13667, by rfl⟩ (by norm_num))
theorem R72917 : Reach 72917 := rs (se 7 (by rfl) ⟨854, by rfl⟩) (B 1709 (by norm_num) ⟨854, by rfl⟩ (by norm_num))
theorem R269525 : Reach 269525 := rs (se 7 (by rfl) ⟨3158, by rfl⟩) (B 6317 (by norm_num) ⟨3158, by rfl⟩ (by norm_num))
theorem R72941 : Reach 72941 := rs (se 3 (by rfl) ⟨13676, by rfl⟩) (B 27353 (by norm_num) ⟨13676, by rfl⟩ (by norm_num))
theorem R72965 : Reach 72965 := rs (se 4 (by rfl) ⟨6840, by rfl⟩) (B 13681 (by norm_num) ⟨6840, by rfl⟩ (by norm_num))
theorem R72989 : Reach 72989 := rs (se 3 (by rfl) ⟨13685, by rfl⟩) (B 27371 (by norm_num) ⟨13685, by rfl⟩ (by norm_num))
theorem R73013 : Reach 73013 := rs (se 5 (by rfl) ⟨3422, by rfl⟩) (B 6845 (by norm_num) ⟨3422, by rfl⟩ (by norm_num))
theorem R73037 : Reach 73037 := rs (se 3 (by rfl) ⟨13694, by rfl⟩) (B 27389 (by norm_num) ⟨13694, by rfl⟩ (by norm_num))
theorem R73061 : Reach 73061 := rs (se 4 (by rfl) ⟨6849, by rfl⟩) (B 13699 (by norm_num) ⟨6849, by rfl⟩ (by norm_num))
theorem R73085 : Reach 73085 := rs (se 3 (by rfl) ⟨13703, by rfl⟩) (B 27407 (by norm_num) ⟨13703, by rfl⟩ (by norm_num))
theorem R73109 : Reach 73109 := rs (se 6 (by rfl) ⟨1713, by rfl⟩) (B 3427 (by norm_num) ⟨1713, by rfl⟩ (by norm_num))
theorem R73133 : Reach 73133 := rs (se 3 (by rfl) ⟨13712, by rfl⟩) (B 27425 (by norm_num) ⟨13712, by rfl⟩ (by norm_num))
theorem R335285 : Reach 335285 := rs (se 5 (by rfl) ⟨15716, by rfl⟩) (B 31433 (by norm_num) ⟨15716, by rfl⟩ (by norm_num))
theorem R73157 : Reach 73157 := rs (se 4 (by rfl) ⟨6858, by rfl⟩) (B 13717 (by norm_num) ⟨6858, by rfl⟩ (by norm_num))
theorem R73181 : Reach 73181 := rs (se 3 (by rfl) ⟨13721, by rfl⟩) (B 27443 (by norm_num) ⟨13721, by rfl⟩ (by norm_num))
theorem R73205 : Reach 73205 := rs (se 5 (by rfl) ⟨3431, by rfl⟩) (B 6863 (by norm_num) ⟨3431, by rfl⟩ (by norm_num))
theorem R73229 : Reach 73229 := rs (se 3 (by rfl) ⟨13730, by rfl⟩) (B 27461 (by norm_num) ⟨13730, by rfl⟩ (by norm_num))
theorem R138773 : Reach 138773 := rs (se 6 (by rfl) ⟨3252, by rfl⟩) (B 6505 (by norm_num) ⟨3252, by rfl⟩ (by norm_num))
theorem R73253 : Reach 73253 := rs (se 4 (by rfl) ⟨6867, by rfl⟩) (B 13735 (by norm_num) ⟨6867, by rfl⟩ (by norm_num))
theorem R171557 : Reach 171557 := rs (se 4 (by rfl) ⟨16083, by rfl⟩) (B 32167 (by norm_num) ⟨16083, by rfl⟩ (by norm_num))
theorem R106037 : Reach 106037 := rs (se 5 (by rfl) ⟨4970, by rfl⟩) (B 9941 (by norm_num) ⟨4970, by rfl⟩ (by norm_num))
theorem R73277 : Reach 73277 := rs (se 3 (by rfl) ⟨13739, by rfl⟩) (B 27479 (by norm_num) ⟨13739, by rfl⟩ (by norm_num))
theorem R73301 : Reach 73301 := rs (se 8 (by rfl) ⟨429, by rfl⟩) (B 859 (by norm_num) ⟨429, by rfl⟩ (by norm_num))
theorem R73325 : Reach 73325 := rs (se 3 (by rfl) ⟨13748, by rfl⟩) (B 27497 (by norm_num) ⟨13748, by rfl⟩ (by norm_num))
theorem R106109 : Reach 106109 := rs (se 3 (by rfl) ⟨19895, by rfl⟩) (B 39791 (by norm_num) ⟨19895, by rfl⟩ (by norm_num))
theorem R73349 : Reach 73349 := rs (se 4 (by rfl) ⟨6876, by rfl⟩) (B 13753 (by norm_num) ⟨6876, by rfl⟩ (by norm_num))
theorem R73373 : Reach 73373 := rs (se 3 (by rfl) ⟨13757, by rfl⟩) (B 27515 (by norm_num) ⟨13757, by rfl⟩ (by norm_num))
theorem R73397 : Reach 73397 := rs (se 5 (by rfl) ⟨3440, by rfl⟩) (B 6881 (by norm_num) ⟨3440, by rfl⟩ (by norm_num))
theorem R106181 : Reach 106181 := rs (se 4 (by rfl) ⟨9954, by rfl⟩) (B 19909 (by norm_num) ⟨9954, by rfl⟩ (by norm_num))
theorem R73421 : Reach 73421 := rs (se 3 (by rfl) ⟨13766, by rfl⟩) (B 27533 (by norm_num) ⟨13766, by rfl⟩ (by norm_num))
theorem R73445 : Reach 73445 := rs (se 4 (by rfl) ⟨6885, by rfl⟩) (B 13771 (by norm_num) ⟨6885, by rfl⟩ (by norm_num))
theorem R73469 : Reach 73469 := rs (se 3 (by rfl) ⟨13775, by rfl⟩) (B 27551 (by norm_num) ⟨13775, by rfl⟩ (by norm_num))
theorem R106253 : Reach 106253 := rs (se 3 (by rfl) ⟨19922, by rfl⟩) (B 39845 (by norm_num) ⟨19922, by rfl⟩ (by norm_num))
theorem R73493 : Reach 73493 := rs (se 6 (by rfl) ⟨1722, by rfl⟩) (B 3445 (by norm_num) ⟨1722, by rfl⟩ (by norm_num))
theorem R73517 : Reach 73517 := rs (se 3 (by rfl) ⟨13784, by rfl⟩) (B 27569 (by norm_num) ⟨13784, by rfl⟩ (by norm_num))
theorem R73541 : Reach 73541 := rs (se 4 (by rfl) ⟨6894, by rfl⟩) (B 13789 (by norm_num) ⟨6894, by rfl⟩ (by norm_num))
theorem R106309 : Reach 106309 := rs (se 4 (by rfl) ⟨9966, by rfl⟩) (B 19933 (by norm_num) ⟨9966, by rfl⟩ (by norm_num))
theorem R106325 : Reach 106325 := rs (se 9 (by rfl) ⟨311, by rfl⟩) (B 623 (by norm_num) ⟨311, by rfl⟩ (by norm_num))
theorem R73565 : Reach 73565 := rs (se 3 (by rfl) ⟨13793, by rfl⟩) (B 27587 (by norm_num) ⟨13793, by rfl⟩ (by norm_num))
theorem R73589 : Reach 73589 := rs (se 5 (by rfl) ⟨3449, by rfl⟩) (B 6899 (by norm_num) ⟨3449, by rfl⟩ (by norm_num))
theorem R73613 : Reach 73613 := rs (se 3 (by rfl) ⟨13802, by rfl⟩) (B 27605 (by norm_num) ⟨13802, by rfl⟩ (by norm_num))
theorem R106397 : Reach 106397 := rs (se 3 (by rfl) ⟨19949, by rfl⟩) (B 39899 (by norm_num) ⟨19949, by rfl⟩ (by norm_num))
theorem R73637 : Reach 73637 := rs (se 4 (by rfl) ⟨6903, by rfl⟩) (B 13807 (by norm_num) ⟨6903, by rfl⟩ (by norm_num))
theorem R106429 : Reach 106429 := rs (se 3 (by rfl) ⟨19955, by rfl⟩) (B 39911 (by norm_num) ⟨19955, by rfl⟩ (by norm_num))
theorem R73661 : Reach 73661 := rs (se 3 (by rfl) ⟨13811, by rfl⟩) (B 27623 (by norm_num) ⟨13811, by rfl⟩ (by norm_num))
theorem R171989 : Reach 171989 := rs (se 7 (by rfl) ⟨2015, by rfl⟩) (B 4031 (by norm_num) ⟨2015, by rfl⟩ (by norm_num))
theorem R73685 : Reach 73685 := rs (se 7 (by rfl) ⟨863, by rfl⟩) (B 1727 (by norm_num) ⟨863, by rfl⟩ (by norm_num))
theorem R106469 : Reach 106469 := rs (se 4 (by rfl) ⟨9981, by rfl⟩) (B 19963 (by norm_num) ⟨9981, by rfl⟩ (by norm_num))
theorem R73709 : Reach 73709 := rs (se 3 (by rfl) ⟨13820, by rfl⟩) (B 27641 (by norm_num) ⟨13820, by rfl⟩ (by norm_num))
theorem R73733 : Reach 73733 := rs (se 4 (by rfl) ⟨6912, by rfl⟩) (B 13825 (by norm_num) ⟨6912, by rfl⟩ (by norm_num))
theorem R73757 : Reach 73757 := rs (se 3 (by rfl) ⟨13829, by rfl⟩) (B 27659 (by norm_num) ⟨13829, by rfl⟩ (by norm_num))
theorem R106541 : Reach 106541 := rs (se 3 (by rfl) ⟨19976, by rfl⟩) (B 39953 (by norm_num) ⟨19976, by rfl⟩ (by norm_num))
theorem R73781 : Reach 73781 := rs (se 5 (by rfl) ⟨3458, by rfl⟩) (B 6917 (by norm_num) ⟨3458, by rfl⟩ (by norm_num))
theorem R73805 : Reach 73805 := rs (se 3 (by rfl) ⟨13838, by rfl⟩) (B 27677 (by norm_num) ⟨13838, by rfl⟩ (by norm_num))
theorem R73829 : Reach 73829 := rs (se 4 (by rfl) ⟨6921, by rfl⟩) (B 13843 (by norm_num) ⟨6921, by rfl⟩ (by norm_num))
theorem R106613 : Reach 106613 := rs (se 5 (by rfl) ⟨4997, by rfl⟩) (B 9995 (by norm_num) ⟨4997, by rfl⟩ (by norm_num))
theorem R73853 : Reach 73853 := rs (se 3 (by rfl) ⟨13847, by rfl⟩) (B 27695 (by norm_num) ⟨13847, by rfl⟩ (by norm_num))
theorem R73877 : Reach 73877 := rs (se 6 (by rfl) ⟨1731, by rfl⟩) (B 3463 (by norm_num) ⟨1731, by rfl⟩ (by norm_num))
theorem R73901 : Reach 73901 := rs (se 3 (by rfl) ⟨13856, by rfl⟩) (B 27713 (by norm_num) ⟨13856, by rfl⟩ (by norm_num))
theorem R139445 : Reach 139445 := rs (se 5 (by rfl) ⟨6536, by rfl⟩) (B 13073 (by norm_num) ⟨6536, by rfl⟩ (by norm_num))
theorem R106685 : Reach 106685 := rs (se 3 (by rfl) ⟨20003, by rfl⟩) (B 40007 (by norm_num) ⟨20003, by rfl⟩ (by norm_num))
theorem R73925 : Reach 73925 := rs (se 4 (by rfl) ⟨6930, by rfl⟩) (B 13861 (by norm_num) ⟨6930, by rfl⟩ (by norm_num))
theorem R73949 : Reach 73949 := rs (se 3 (by rfl) ⟨13865, by rfl⟩) (B 27731 (by norm_num) ⟨13865, by rfl⟩ (by norm_num))
theorem R73973 : Reach 73973 := rs (se 5 (by rfl) ⟨3467, by rfl⟩) (B 6935 (by norm_num) ⟨3467, by rfl⟩ (by norm_num))
theorem R106757 : Reach 106757 := rs (se 4 (by rfl) ⟨10008, by rfl⟩) (B 20017 (by norm_num) ⟨10008, by rfl⟩ (by norm_num))
theorem R73997 : Reach 73997 := rs (se 3 (by rfl) ⟨13874, by rfl⟩) (B 27749 (by norm_num) ⟨13874, by rfl⟩ (by norm_num))
theorem R74021 : Reach 74021 := rs (se 4 (by rfl) ⟨6939, by rfl⟩) (B 13879 (by norm_num) ⟨6939, by rfl⟩ (by norm_num))
theorem R74045 : Reach 74045 := rs (se 3 (by rfl) ⟨13883, by rfl⟩) (B 27767 (by norm_num) ⟨13883, by rfl⟩ (by norm_num))
theorem R106829 : Reach 106829 := rs (se 3 (by rfl) ⟨20030, by rfl⟩) (B 40061 (by norm_num) ⟨20030, by rfl⟩ (by norm_num))
theorem R74069 : Reach 74069 := rs (se 10 (by rfl) ⟨108, by rfl⟩) (B 217 (by norm_num) ⟨108, by rfl⟩ (by norm_num))
theorem R74093 : Reach 74093 := rs (se 3 (by rfl) ⟨13892, by rfl⟩) (B 27785 (by norm_num) ⟨13892, by rfl⟩ (by norm_num))
theorem R74117 : Reach 74117 := rs (se 4 (by rfl) ⟨6948, by rfl⟩) (B 13897 (by norm_num) ⟨6948, by rfl⟩ (by norm_num))
theorem R172421 : Reach 172421 := rs (se 4 (by rfl) ⟨16164, by rfl⟩) (B 32329 (by norm_num) ⟨16164, by rfl⟩ (by norm_num))
theorem R106901 : Reach 106901 := rs (se 6 (by rfl) ⟨2505, by rfl⟩) (B 5011 (by norm_num) ⟨2505, by rfl⟩ (by norm_num))
theorem R74141 : Reach 74141 := rs (se 3 (by rfl) ⟨13901, by rfl⟩) (B 27803 (by norm_num) ⟨13901, by rfl⟩ (by norm_num))
theorem R74165 : Reach 74165 := rs (se 5 (by rfl) ⟨3476, by rfl⟩) (B 6953 (by norm_num) ⟨3476, by rfl⟩ (by norm_num))
theorem R74189 : Reach 74189 := rs (se 3 (by rfl) ⟨13910, by rfl⟩) (B 27821 (by norm_num) ⟨13910, by rfl⟩ (by norm_num))
theorem R106973 : Reach 106973 := rs (se 3 (by rfl) ⟨20057, by rfl⟩) (B 40115 (by norm_num) ⟨20057, by rfl⟩ (by norm_num))
theorem R74213 : Reach 74213 := rs (se 4 (by rfl) ⟨6957, by rfl⟩) (B 13915 (by norm_num) ⟨6957, by rfl⟩ (by norm_num))
theorem R74237 : Reach 74237 := rs (se 3 (by rfl) ⟨13919, by rfl⟩) (B 27839 (by norm_num) ⟨13919, by rfl⟩ (by norm_num))
theorem R74261 : Reach 74261 := rs (se 6 (by rfl) ⟨1740, by rfl⟩) (B 3481 (by norm_num) ⟨1740, by rfl⟩ (by norm_num))
theorem R107045 : Reach 107045 := rs (se 4 (by rfl) ⟨10035, by rfl⟩) (B 20071 (by norm_num) ⟨10035, by rfl⟩ (by norm_num))
theorem R74285 : Reach 74285 := rs (se 3 (by rfl) ⟨13928, by rfl⟩) (B 27857 (by norm_num) ⟨13928, by rfl⟩ (by norm_num))
theorem R74309 : Reach 74309 := rs (se 4 (by rfl) ⟨6966, by rfl⟩) (B 13933 (by norm_num) ⟨6966, by rfl⟩ (by norm_num))
theorem R74333 : Reach 74333 := rs (se 3 (by rfl) ⟨13937, by rfl⟩) (B 27875 (by norm_num) ⟨13937, by rfl⟩ (by norm_num))
theorem R139877 : Reach 139877 := rs (se 4 (by rfl) ⟨13113, by rfl⟩) (B 26227 (by norm_num) ⟨13113, by rfl⟩ (by norm_num))
theorem R107117 : Reach 107117 := rs (se 3 (by rfl) ⟨20084, by rfl⟩) (B 40169 (by norm_num) ⟨20084, by rfl⟩ (by norm_num))
theorem R74357 : Reach 74357 := rs (se 5 (by rfl) ⟨3485, by rfl⟩) (B 6971 (by norm_num) ⟨3485, by rfl⟩ (by norm_num))
theorem R74381 : Reach 74381 := rs (se 3 (by rfl) ⟨13946, by rfl⟩) (B 27893 (by norm_num) ⟨13946, by rfl⟩ (by norm_num))
theorem R74405 : Reach 74405 := rs (se 4 (by rfl) ⟨6975, by rfl⟩) (B 13951 (by norm_num) ⟨6975, by rfl⟩ (by norm_num))
theorem R107189 : Reach 107189 := rs (se 5 (by rfl) ⟨5024, by rfl⟩) (B 10049 (by norm_num) ⟨5024, by rfl⟩ (by norm_num))
theorem R74429 : Reach 74429 := rs (se 3 (by rfl) ⟨13955, by rfl⟩) (B 27911 (by norm_num) ⟨13955, by rfl⟩ (by norm_num))
theorem R74453 : Reach 74453 := rs (se 7 (by rfl) ⟨872, by rfl⟩) (B 1745 (by norm_num) ⟨872, by rfl⟩ (by norm_num))
theorem R74477 : Reach 74477 := rs (se 3 (by rfl) ⟨13964, by rfl⟩) (B 27929 (by norm_num) ⟨13964, by rfl⟩ (by norm_num))
theorem R107261 : Reach 107261 := rs (se 3 (by rfl) ⟨20111, by rfl⟩) (B 40223 (by norm_num) ⟨20111, by rfl⟩ (by norm_num))
theorem R74501 : Reach 74501 := rs (se 4 (by rfl) ⟨6984, by rfl⟩) (B 13969 (by norm_num) ⟨6984, by rfl⟩ (by norm_num))
theorem R74525 : Reach 74525 := rs (se 3 (by rfl) ⟨13973, by rfl⟩) (B 27947 (by norm_num) ⟨13973, by rfl⟩ (by norm_num))
theorem R74549 : Reach 74549 := rs (se 5 (by rfl) ⟨3494, by rfl⟩) (B 6989 (by norm_num) ⟨3494, by rfl⟩ (by norm_num))
theorem R107333 : Reach 107333 := rs (se 4 (by rfl) ⟨10062, by rfl⟩) (B 20125 (by norm_num) ⟨10062, by rfl⟩ (by norm_num))
theorem R74573 : Reach 74573 := rs (se 3 (by rfl) ⟨13982, by rfl⟩) (B 27965 (by norm_num) ⟨13982, by rfl⟩ (by norm_num))
theorem R74597 : Reach 74597 := rs (se 4 (by rfl) ⟨6993, by rfl⟩) (B 13987 (by norm_num) ⟨6993, by rfl⟩ (by norm_num))
theorem R74621 : Reach 74621 := rs (se 3 (by rfl) ⟨13991, by rfl⟩) (B 27983 (by norm_num) ⟨13991, by rfl⟩ (by norm_num))
theorem R107405 : Reach 107405 := rs (se 3 (by rfl) ⟨20138, by rfl⟩) (B 40277 (by norm_num) ⟨20138, by rfl⟩ (by norm_num))
theorem R74645 : Reach 74645 := rs (se 6 (by rfl) ⟨1749, by rfl⟩) (B 3499 (by norm_num) ⟨1749, by rfl⟩ (by norm_num))
theorem R74669 : Reach 74669 := rs (se 3 (by rfl) ⟨14000, by rfl⟩) (B 28001 (by norm_num) ⟨14000, by rfl⟩ (by norm_num))
theorem R74693 : Reach 74693 := rs (se 4 (by rfl) ⟨7002, by rfl⟩) (B 14005 (by norm_num) ⟨7002, by rfl⟩ (by norm_num))
theorem R107477 : Reach 107477 := rs (se 7 (by rfl) ⟨1259, by rfl⟩) (B 2519 (by norm_num) ⟨1259, by rfl⟩ (by norm_num))
theorem R74717 : Reach 74717 := rs (se 3 (by rfl) ⟨14009, by rfl⟩) (B 28019 (by norm_num) ⟨14009, by rfl⟩ (by norm_num))
theorem R271349 : Reach 271349 := rs (se 5 (by rfl) ⟨12719, by rfl⟩) (B 25439 (by norm_num) ⟨12719, by rfl⟩ (by norm_num))
theorem R74741 : Reach 74741 := rs (se 5 (by rfl) ⟨3503, by rfl⟩) (B 7007 (by norm_num) ⟨3503, by rfl⟩ (by norm_num))
theorem R74765 : Reach 74765 := rs (se 3 (by rfl) ⟨14018, by rfl⟩) (B 28037 (by norm_num) ⟨14018, by rfl⟩ (by norm_num))
theorem R926741 : Reach 926741 := rs (se 6 (by rfl) ⟨21720, by rfl⟩) (B 43441 (by norm_num) ⟨21720, by rfl⟩ (by norm_num))
theorem R107549 : Reach 107549 := rs (se 3 (by rfl) ⟨20165, by rfl⟩) (B 40331 (by norm_num) ⟨20165, by rfl⟩ (by norm_num))
theorem R74789 : Reach 74789 := rs (se 4 (by rfl) ⟨7011, by rfl⟩) (B 14023 (by norm_num) ⟨7011, by rfl⟩ (by norm_num))
theorem R107573 : Reach 107573 := rs (se 5 (by rfl) ⟨5042, by rfl⟩) (B 10085 (by norm_num) ⟨5042, by rfl⟩ (by norm_num))
theorem R74813 : Reach 74813 := rs (se 3 (by rfl) ⟨14027, by rfl⟩) (B 28055 (by norm_num) ⟨14027, by rfl⟩ (by norm_num))
theorem R74837 : Reach 74837 := rs (se 8 (by rfl) ⟨438, by rfl⟩) (B 877 (by norm_num) ⟨438, by rfl⟩ (by norm_num))
theorem R107621 : Reach 107621 := rs (se 4 (by rfl) ⟨10089, by rfl⟩) (B 20179 (by norm_num) ⟨10089, by rfl⟩ (by norm_num))
theorem R74861 : Reach 74861 := rs (se 3 (by rfl) ⟨14036, by rfl⟩) (B 28073 (by norm_num) ⟨14036, by rfl⟩ (by norm_num))
theorem R74885 : Reach 74885 := rs (se 4 (by rfl) ⟨7020, by rfl⟩) (B 14041 (by norm_num) ⟨7020, by rfl⟩ (by norm_num))
theorem R205973 : Reach 205973 := rs (se 6 (by rfl) ⟨4827, by rfl⟩) (B 9655 (by norm_num) ⟨4827, by rfl⟩ (by norm_num))
theorem R74909 : Reach 74909 := rs (se 3 (by rfl) ⟨14045, by rfl⟩) (B 28091 (by norm_num) ⟨14045, by rfl⟩ (by norm_num))
theorem R107693 : Reach 107693 := rs (se 3 (by rfl) ⟨20192, by rfl⟩) (B 40385 (by norm_num) ⟨20192, by rfl⟩ (by norm_num))
theorem R369845 : Reach 369845 := rs (se 5 (by rfl) ⟨17336, by rfl⟩) (B 34673 (by norm_num) ⟨17336, by rfl⟩ (by norm_num))
theorem R74933 : Reach 74933 := rs (se 5 (by rfl) ⟨3512, by rfl⟩) (B 7025 (by norm_num) ⟨3512, by rfl⟩ (by norm_num))
theorem R74957 : Reach 74957 := rs (se 3 (by rfl) ⟨14054, by rfl⟩) (B 28109 (by norm_num) ⟨14054, by rfl⟩ (by norm_num))
theorem R173285 : Reach 173285 := rs (se 4 (by rfl) ⟨16245, by rfl⟩) (B 32491 (by norm_num) ⟨16245, by rfl⟩ (by norm_num))
theorem R74981 : Reach 74981 := rs (se 4 (by rfl) ⟨7029, by rfl⟩) (B 14059 (by norm_num) ⟨7029, by rfl⟩ (by norm_num))
theorem R107765 : Reach 107765 := rs (se 5 (by rfl) ⟨5051, by rfl⟩) (B 10103 (by norm_num) ⟨5051, by rfl⟩ (by norm_num))
theorem R75005 : Reach 75005 := rs (se 3 (by rfl) ⟨14063, by rfl⟩) (B 28127 (by norm_num) ⟨14063, by rfl⟩ (by norm_num))
theorem R75029 : Reach 75029 := rs (se 6 (by rfl) ⟨1758, by rfl⟩) (B 3517 (by norm_num) ⟨1758, by rfl⟩ (by norm_num))
theorem R107813 : Reach 107813 := rs (se 4 (by rfl) ⟨10107, by rfl⟩) (B 20215 (by norm_num) ⟨10107, by rfl⟩ (by norm_num))
theorem R75053 : Reach 75053 := rs (se 3 (by rfl) ⟨14072, by rfl⟩) (B 28145 (by norm_num) ⟨14072, by rfl⟩ (by norm_num))
theorem R107837 : Reach 107837 := rs (se 3 (by rfl) ⟨20219, by rfl⟩) (B 40439 (by norm_num) ⟨20219, by rfl⟩ (by norm_num))
theorem R75077 : Reach 75077 := rs (se 4 (by rfl) ⟨7038, by rfl⟩) (B 14077 (by norm_num) ⟨7038, by rfl⟩ (by norm_num))
theorem R140629 : Reach 140629 := rs (se 12 (by rfl) ⟨51, by rfl⟩) (B 103 (by norm_num) ⟨51, by rfl⟩ (by norm_num))
theorem R75101 : Reach 75101 := rs (se 3 (by rfl) ⟨14081, by rfl⟩) (B 28163 (by norm_num) ⟨14081, by rfl⟩ (by norm_num))
theorem R238949 : Reach 238949 := rs (se 4 (by rfl) ⟨22401, by rfl⟩) (B 44803 (by norm_num) ⟨22401, by rfl⟩ (by norm_num))
theorem R75125 : Reach 75125 := rs (se 5 (by rfl) ⟨3521, by rfl⟩) (B 7043 (by norm_num) ⟨3521, by rfl⟩ (by norm_num))
theorem R107909 : Reach 107909 := rs (se 4 (by rfl) ⟨10116, by rfl⟩) (B 20233 (by norm_num) ⟨10116, by rfl⟩ (by norm_num))
theorem R75149 : Reach 75149 := rs (se 3 (by rfl) ⟨14090, by rfl⟩) (B 28181 (by norm_num) ⟨14090, by rfl⟩ (by norm_num))
theorem R75173 : Reach 75173 := rs (se 4 (by rfl) ⟨7047, by rfl⟩) (B 14095 (by norm_num) ⟨7047, by rfl⟩ (by norm_num))
theorem R75197 : Reach 75197 := rs (se 3 (by rfl) ⟨14099, by rfl⟩) (B 28199 (by norm_num) ⟨14099, by rfl⟩ (by norm_num))
theorem R107981 : Reach 107981 := rs (se 3 (by rfl) ⟨20246, by rfl⟩) (B 40493 (by norm_num) ⟨20246, by rfl⟩ (by norm_num))
theorem R75221 : Reach 75221 := rs (se 7 (by rfl) ⟨881, by rfl⟩) (B 1763 (by norm_num) ⟨881, by rfl⟩ (by norm_num))
theorem R75245 : Reach 75245 := rs (se 3 (by rfl) ⟨14108, by rfl⟩) (B 28217 (by norm_num) ⟨14108, by rfl⟩ (by norm_num))
theorem R173573 : Reach 173573 := rs (se 4 (by rfl) ⟨16272, by rfl⟩) (B 32545 (by norm_num) ⟨16272, by rfl⟩ (by norm_num))
theorem R75269 : Reach 75269 := rs (se 4 (by rfl) ⟨7056, by rfl⟩) (B 14113 (by norm_num) ⟨7056, by rfl⟩ (by norm_num))
theorem R108053 : Reach 108053 := rs (se 6 (by rfl) ⟨2532, by rfl⟩) (B 5065 (by norm_num) ⟨2532, by rfl⟩ (by norm_num))
theorem R75293 : Reach 75293 := rs (se 3 (by rfl) ⟨14117, by rfl⟩) (B 28235 (by norm_num) ⟨14117, by rfl⟩ (by norm_num))
theorem R75317 : Reach 75317 := rs (se 5 (by rfl) ⟨3530, by rfl⟩) (B 7061 (by norm_num) ⟨3530, by rfl⟩ (by norm_num))
theorem R75341 : Reach 75341 := rs (se 3 (by rfl) ⟨14126, by rfl⟩) (B 28253 (by norm_num) ⟨14126, by rfl⟩ (by norm_num))
theorem R108125 : Reach 108125 := rs (se 3 (by rfl) ⟨20273, by rfl⟩) (B 40547 (by norm_num) ⟨20273, by rfl⟩ (by norm_num))
theorem R75365 : Reach 75365 := rs (se 4 (by rfl) ⟨7065, by rfl⟩) (B 14131 (by norm_num) ⟨7065, by rfl⟩ (by norm_num))
theorem R75389 : Reach 75389 := rs (se 3 (by rfl) ⟨14135, by rfl⟩) (B 28271 (by norm_num) ⟨14135, by rfl⟩ (by norm_num))
theorem R75413 : Reach 75413 := rs (se 6 (by rfl) ⟨1767, by rfl⟩) (B 3535 (by norm_num) ⟨1767, by rfl⟩ (by norm_num))
theorem R108197 : Reach 108197 := rs (se 4 (by rfl) ⟨10143, by rfl⟩) (B 20287 (by norm_num) ⟨10143, by rfl⟩ (by norm_num))
theorem R75437 : Reach 75437 := rs (se 3 (by rfl) ⟨14144, by rfl⟩) (B 28289 (by norm_num) ⟨14144, by rfl⟩ (by norm_num))
theorem R75461 : Reach 75461 := rs (se 4 (by rfl) ⟨7074, by rfl⟩) (B 14149 (by norm_num) ⟨7074, by rfl⟩ (by norm_num))
theorem R108253 : Reach 108253 := rs (se 3 (by rfl) ⟨20297, by rfl⟩) (B 40595 (by norm_num) ⟨20297, by rfl⟩ (by norm_num))
theorem R75485 : Reach 75485 := rs (se 3 (by rfl) ⟨14153, by rfl⟩) (B 28307 (by norm_num) ⟨14153, by rfl⟩ (by norm_num))
theorem R108269 : Reach 108269 := rs (se 3 (by rfl) ⟨20300, by rfl⟩) (B 40601 (by norm_num) ⟨20300, by rfl⟩ (by norm_num))
theorem R75509 : Reach 75509 := rs (se 5 (by rfl) ⟨3539, by rfl⟩) (B 7079 (by norm_num) ⟨3539, by rfl⟩ (by norm_num))
theorem R75533 : Reach 75533 := rs (se 3 (by rfl) ⟨14162, by rfl⟩) (B 28325 (by norm_num) ⟨14162, by rfl⟩ (by norm_num))
theorem R108317 : Reach 108317 := rs (se 3 (by rfl) ⟨20309, by rfl⟩) (B 40619 (by norm_num) ⟨20309, by rfl⟩ (by norm_num))
theorem R75557 : Reach 75557 := rs (se 4 (by rfl) ⟨7083, by rfl⟩) (B 14167 (by norm_num) ⟨7083, by rfl⟩ (by norm_num))
theorem R108325 : Reach 108325 := rs (se 4 (by rfl) ⟨10155, by rfl⟩) (B 20311 (by norm_num) ⟨10155, by rfl⟩ (by norm_num))
theorem R108341 : Reach 108341 := rs (se 5 (by rfl) ⟨5078, by rfl⟩) (B 10157 (by norm_num) ⟨5078, by rfl⟩ (by norm_num))
theorem R75581 : Reach 75581 := rs (se 3 (by rfl) ⟨14171, by rfl⟩) (B 28343 (by norm_num) ⟨14171, by rfl⟩ (by norm_num))
theorem R108373 : Reach 108373 := rs (se 9 (by rfl) ⟨317, by rfl⟩) (B 635 (by norm_num) ⟨317, by rfl⟩ (by norm_num))
theorem R75605 : Reach 75605 := rs (se 9 (by rfl) ⟨221, by rfl⟩) (B 443 (by norm_num) ⟨221, by rfl⟩ (by norm_num))
theorem R75629 : Reach 75629 := rs (se 3 (by rfl) ⟨14180, by rfl⟩) (B 28361 (by norm_num) ⟨14180, by rfl⟩ (by norm_num))
theorem R108413 : Reach 108413 := rs (se 3 (by rfl) ⟨20327, by rfl⟩) (B 40655 (by norm_num) ⟨20327, by rfl⟩ (by norm_num))
theorem R75653 : Reach 75653 := rs (se 4 (by rfl) ⟨7092, by rfl⟩) (B 14185 (by norm_num) ⟨7092, by rfl⟩ (by norm_num))
theorem R75677 : Reach 75677 := rs (se 3 (by rfl) ⟨14189, by rfl⟩) (B 28379 (by norm_num) ⟨14189, by rfl⟩ (by norm_num))
theorem R75701 : Reach 75701 := rs (se 5 (by rfl) ⟨3548, by rfl⟩) (B 7097 (by norm_num) ⟨3548, by rfl⟩ (by norm_num))
theorem R108485 : Reach 108485 := rs (se 4 (by rfl) ⟨10170, by rfl⟩) (B 20341 (by norm_num) ⟨10170, by rfl⟩ (by norm_num))
theorem R75725 : Reach 75725 := rs (se 3 (by rfl) ⟨14198, by rfl⟩) (B 28397 (by norm_num) ⟨14198, by rfl⟩ (by norm_num))
theorem R75749 : Reach 75749 := rs (se 4 (by rfl) ⟨7101, by rfl⟩) (B 14203 (by norm_num) ⟨7101, by rfl⟩ (by norm_num))
theorem R75757 : Reach 75757 := rs (se 3 (by rfl) ⟨14204, by rfl⟩) (B 28409 (by norm_num) ⟨14204, by rfl⟩ (by norm_num))
theorem R75773 : Reach 75773 := rs (se 3 (by rfl) ⟨14207, by rfl⟩) (B 28415 (by norm_num) ⟨14207, by rfl⟩ (by norm_num))
theorem R108557 : Reach 108557 := rs (se 3 (by rfl) ⟨20354, by rfl⟩) (B 40709 (by norm_num) ⟨20354, by rfl⟩ (by norm_num))
theorem R75797 : Reach 75797 := rs (se 6 (by rfl) ⟨1776, by rfl⟩) (B 3553 (by norm_num) ⟨1776, by rfl⟩ (by norm_num))
theorem R75821 : Reach 75821 := rs (se 3 (by rfl) ⟨14216, by rfl⟩) (B 28433 (by norm_num) ⟨14216, by rfl⟩ (by norm_num))
theorem R75845 : Reach 75845 := rs (se 4 (by rfl) ⟨7110, by rfl⟩) (B 14221 (by norm_num) ⟨7110, by rfl⟩ (by norm_num))
theorem R108629 : Reach 108629 := rs (se 8 (by rfl) ⟨636, by rfl⟩) (B 1273 (by norm_num) ⟨636, by rfl⟩ (by norm_num))
theorem R75869 : Reach 75869 := rs (se 3 (by rfl) ⟨14225, by rfl⟩) (B 28451 (by norm_num) ⟨14225, by rfl⟩ (by norm_num))
theorem R75893 : Reach 75893 := rs (se 5 (by rfl) ⟨3557, by rfl⟩) (B 7115 (by norm_num) ⟨3557, by rfl⟩ (by norm_num))
theorem R206981 : Reach 206981 := rs (se 4 (by rfl) ⟨19404, by rfl⟩) (B 38809 (by norm_num) ⟨19404, by rfl⟩ (by norm_num))
theorem R75917 : Reach 75917 := rs (se 3 (by rfl) ⟨14234, by rfl⟩) (B 28469 (by norm_num) ⟨14234, by rfl⟩ (by norm_num))
theorem R108701 : Reach 108701 := rs (se 3 (by rfl) ⟨20381, by rfl⟩) (B 40763 (by norm_num) ⟨20381, by rfl⟩ (by norm_num))
theorem R75941 : Reach 75941 := rs (se 4 (by rfl) ⟨7119, by rfl⟩) (B 14239 (by norm_num) ⟨7119, by rfl⟩ (by norm_num))
theorem R75965 : Reach 75965 := rs (se 3 (by rfl) ⟨14243, by rfl⟩) (B 28487 (by norm_num) ⟨14243, by rfl⟩ (by norm_num))
theorem R75989 : Reach 75989 := rs (se 7 (by rfl) ⟨890, by rfl⟩) (B 1781 (by norm_num) ⟨890, by rfl⟩ (by norm_num))
theorem R108773 : Reach 108773 := rs (se 4 (by rfl) ⟨10197, by rfl⟩) (B 20395 (by norm_num) ⟨10197, by rfl⟩ (by norm_num))
theorem R76013 : Reach 76013 := rs (se 3 (by rfl) ⟨14252, by rfl⟩) (B 28505 (by norm_num) ⟨14252, by rfl⟩ (by norm_num))
theorem R76037 : Reach 76037 := rs (se 4 (by rfl) ⟨7128, by rfl⟩) (B 14257 (by norm_num) ⟨7128, by rfl⟩ (by norm_num))
theorem R76061 : Reach 76061 := rs (se 3 (by rfl) ⟨14261, by rfl⟩) (B 28523 (by norm_num) ⟨14261, by rfl⟩ (by norm_num))
theorem R108845 : Reach 108845 := rs (se 3 (by rfl) ⟨20408, by rfl⟩) (B 40817 (by norm_num) ⟨20408, by rfl⟩ (by norm_num))
theorem R76085 : Reach 76085 := rs (se 5 (by rfl) ⟨3566, by rfl⟩) (B 7133 (by norm_num) ⟨3566, by rfl⟩ (by norm_num))
theorem R76109 : Reach 76109 := rs (se 3 (by rfl) ⟨14270, by rfl⟩) (B 28541 (by norm_num) ⟨14270, by rfl⟩ (by norm_num))
theorem R76133 : Reach 76133 := rs (se 4 (by rfl) ⟨7137, by rfl⟩) (B 14275 (by norm_num) ⟨7137, by rfl⟩ (by norm_num))
theorem R108917 : Reach 108917 := rs (se 5 (by rfl) ⟨5105, by rfl⟩) (B 10211 (by norm_num) ⟨5105, by rfl⟩ (by norm_num))
theorem R76157 : Reach 76157 := rs (se 3 (by rfl) ⟨14279, by rfl⟩) (B 28559 (by norm_num) ⟨14279, by rfl⟩ (by norm_num))
theorem R76181 : Reach 76181 := rs (se 6 (by rfl) ⟨1785, by rfl⟩) (B 3571 (by norm_num) ⟨1785, by rfl⟩ (by norm_num))
theorem R108973 : Reach 108973 := rs (se 3 (by rfl) ⟨20432, by rfl⟩) (B 40865 (by norm_num) ⟨20432, by rfl⟩ (by norm_num))
theorem R76205 : Reach 76205 := rs (se 3 (by rfl) ⟨14288, by rfl⟩) (B 28577 (by norm_num) ⟨14288, by rfl⟩ (by norm_num))
theorem R108989 : Reach 108989 := rs (se 3 (by rfl) ⟨20435, by rfl⟩) (B 40871 (by norm_num) ⟨20435, by rfl⟩ (by norm_num))
theorem R76229 : Reach 76229 := rs (se 4 (by rfl) ⟨7146, by rfl⟩) (B 14293 (by norm_num) ⟨7146, by rfl⟩ (by norm_num))
theorem R76253 : Reach 76253 := rs (se 3 (by rfl) ⟨14297, by rfl⟩) (B 28595 (by norm_num) ⟨14297, by rfl⟩ (by norm_num))
theorem R76277 : Reach 76277 := rs (se 5 (by rfl) ⟨3575, by rfl⟩) (B 7151 (by norm_num) ⟨3575, by rfl⟩ (by norm_num))
theorem R109061 : Reach 109061 := rs (se 4 (by rfl) ⟨10224, by rfl⟩) (B 20449 (by norm_num) ⟨10224, by rfl⟩ (by norm_num))
theorem R76301 : Reach 76301 := rs (se 3 (by rfl) ⟨14306, by rfl⟩) (B 28613 (by norm_num) ⟨14306, by rfl⟩ (by norm_num))
theorem R76325 : Reach 76325 := rs (se 4 (by rfl) ⟨7155, by rfl⟩) (B 14311 (by norm_num) ⟨7155, by rfl⟩ (by norm_num))
theorem R76349 : Reach 76349 := rs (se 3 (by rfl) ⟨14315, by rfl⟩) (B 28631 (by norm_num) ⟨14315, by rfl⟩ (by norm_num))
theorem R109133 : Reach 109133 := rs (se 3 (by rfl) ⟨20462, by rfl⟩) (B 40925 (by norm_num) ⟨20462, by rfl⟩ (by norm_num))
theorem R76373 : Reach 76373 := rs (se 8 (by rfl) ⟨447, by rfl⟩) (B 895 (by norm_num) ⟨447, by rfl⟩ (by norm_num))
theorem R76397 : Reach 76397 := rs (se 3 (by rfl) ⟨14324, by rfl⟩) (B 28649 (by norm_num) ⟨14324, by rfl⟩ (by norm_num))
theorem R240245 : Reach 240245 := rs (se 5 (by rfl) ⟨11261, by rfl⟩) (B 22523 (by norm_num) ⟨11261, by rfl⟩ (by norm_num))
theorem R76421 : Reach 76421 := rs (se 4 (by rfl) ⟨7164, by rfl⟩) (B 14329 (by norm_num) ⟨7164, by rfl⟩ (by norm_num))
theorem R109205 : Reach 109205 := rs (se 6 (by rfl) ⟨2559, by rfl⟩) (B 5119 (by norm_num) ⟨2559, by rfl⟩ (by norm_num))
theorem R76445 : Reach 76445 := rs (se 3 (by rfl) ⟨14333, by rfl⟩) (B 28667 (by norm_num) ⟨14333, by rfl⟩ (by norm_num))
theorem R76469 : Reach 76469 := rs (se 5 (by rfl) ⟨3584, by rfl⟩) (B 7169 (by norm_num) ⟨3584, by rfl⟩ (by norm_num))
theorem R76493 : Reach 76493 := rs (se 3 (by rfl) ⟨14342, by rfl⟩) (B 28685 (by norm_num) ⟨14342, by rfl⟩ (by norm_num))
theorem R109277 : Reach 109277 := rs (se 3 (by rfl) ⟨20489, by rfl⟩) (B 40979 (by norm_num) ⟨20489, by rfl⟩ (by norm_num))
theorem R76517 : Reach 76517 := rs (se 4 (by rfl) ⟨7173, by rfl⟩) (B 14347 (by norm_num) ⟨7173, by rfl⟩ (by norm_num))
theorem R76541 : Reach 76541 := rs (se 3 (by rfl) ⟨14351, by rfl⟩) (B 28703 (by norm_num) ⟨14351, by rfl⟩ (by norm_num))
theorem R76565 : Reach 76565 := rs (se 6 (by rfl) ⟨1794, by rfl⟩) (B 3589 (by norm_num) ⟨1794, by rfl⟩ (by norm_num))
theorem R109349 : Reach 109349 := rs (se 4 (by rfl) ⟨10251, by rfl⟩) (B 20503 (by norm_num) ⟨10251, by rfl⟩ (by norm_num))
theorem R76589 : Reach 76589 := rs (se 3 (by rfl) ⟨14360, by rfl⟩) (B 28721 (by norm_num) ⟨14360, by rfl⟩ (by norm_num))
theorem R76613 : Reach 76613 := rs (se 4 (by rfl) ⟨7182, by rfl⟩) (B 14365 (by norm_num) ⟨7182, by rfl⟩ (by norm_num))
theorem R76637 : Reach 76637 := rs (se 3 (by rfl) ⟨14369, by rfl⟩) (B 28739 (by norm_num) ⟨14369, by rfl⟩ (by norm_num))
theorem R109421 : Reach 109421 := rs (se 3 (by rfl) ⟨20516, by rfl⟩) (B 41033 (by norm_num) ⟨20516, by rfl⟩ (by norm_num))
theorem R76661 : Reach 76661 := rs (se 5 (by rfl) ⟨3593, by rfl⟩) (B 7187 (by norm_num) ⟨3593, by rfl⟩ (by norm_num))
theorem R732053 : Reach 732053 := rs (se 6 (by rfl) ⟨17157, by rfl⟩) (B 34315 (by norm_num) ⟨17157, by rfl⟩ (by norm_num))
theorem R109493 : Reach 109493 := rs (se 5 (by rfl) ⟨5132, by rfl⟩) (B 10265 (by norm_num) ⟨5132, by rfl⟩ (by norm_num))
theorem R109565 : Reach 109565 := rs (se 3 (by rfl) ⟨20543, by rfl⟩) (B 41087 (by norm_num) ⟨20543, by rfl⟩ (by norm_num))
theorem R109637 : Reach 109637 := rs (se 4 (by rfl) ⟨10278, by rfl⟩) (B 20557 (by norm_num) ⟨10278, by rfl⟩ (by norm_num))
theorem R109709 : Reach 109709 := rs (se 3 (by rfl) ⟨20570, by rfl⟩) (B 41141 (by norm_num) ⟨20570, by rfl⟩ (by norm_num))
theorem R273557 : Reach 273557 := rs (se 6 (by rfl) ⟨6411, by rfl⟩) (B 12823 (by norm_num) ⟨6411, by rfl⟩ (by norm_num))
theorem R109781 : Reach 109781 := rs (se 7 (by rfl) ⟨1286, by rfl⟩) (B 2573 (by norm_num) ⟨1286, by rfl⟩ (by norm_num))
theorem R109853 : Reach 109853 := rs (se 3 (by rfl) ⟨20597, by rfl⟩) (B 41195 (by norm_num) ⟨20597, by rfl⟩ (by norm_num))
theorem R240965 : Reach 240965 := rs (se 4 (by rfl) ⟨22590, by rfl⟩) (B 45181 (by norm_num) ⟨22590, by rfl⟩ (by norm_num))
theorem R109925 : Reach 109925 := rs (se 4 (by rfl) ⟨10305, by rfl⟩) (B 20611 (by norm_num) ⟨10305, by rfl⟩ (by norm_num))
theorem R109997 : Reach 109997 := rs (se 3 (by rfl) ⟨20624, by rfl⟩) (B 41249 (by norm_num) ⟨20624, by rfl⟩ (by norm_num))
theorem R142805 : Reach 142805 := rs (se 7 (by rfl) ⟨1673, by rfl⟩) (B 3347 (by norm_num) ⟨1673, by rfl⟩ (by norm_num))
theorem R110069 : Reach 110069 := rs (se 5 (by rfl) ⟨5159, by rfl⟩) (B 10319 (by norm_num) ⟨5159, by rfl⟩ (by norm_num))
theorem R273941 : Reach 273941 := rs (se 6 (by rfl) ⟨6420, by rfl⟩) (B 12841 (by norm_num) ⟨6420, by rfl⟩ (by norm_num))
theorem R110141 : Reach 110141 := rs (se 3 (by rfl) ⟨20651, by rfl⟩) (B 41303 (by norm_num) ⟨20651, by rfl⟩ (by norm_num))
theorem R110213 : Reach 110213 := rs (se 4 (by rfl) ⟨10332, by rfl⟩) (B 20665 (by norm_num) ⟨10332, by rfl⟩ (by norm_num))
theorem R110285 : Reach 110285 := rs (se 3 (by rfl) ⟨20678, by rfl⟩) (B 41357 (by norm_num) ⟨20678, by rfl⟩ (by norm_num))
theorem R110341 : Reach 110341 := rs (se 4 (by rfl) ⟨10344, by rfl⟩) (B 20689 (by norm_num) ⟨10344, by rfl⟩ (by norm_num))
theorem R306965 : Reach 306965 := rs (se 6 (by rfl) ⟨7194, by rfl⟩) (B 14389 (by norm_num) ⟨7194, by rfl⟩ (by norm_num))
theorem R110357 : Reach 110357 := rs (se 6 (by rfl) ⟨2586, by rfl⟩) (B 5173 (by norm_num) ⟨2586, by rfl⟩ (by norm_num))
theorem R110429 : Reach 110429 := rs (se 3 (by rfl) ⟨20705, by rfl⟩) (B 41411 (by norm_num) ⟨20705, by rfl⟩ (by norm_num))
theorem R208757 : Reach 208757 := rs (se 5 (by rfl) ⟨9785, by rfl⟩) (B 19571 (by norm_num) ⟨9785, by rfl⟩ (by norm_num))
theorem R241541 : Reach 241541 := rs (se 4 (by rfl) ⟨22644, by rfl⟩) (B 45289 (by norm_num) ⟨22644, by rfl⟩ (by norm_num))
theorem R110501 : Reach 110501 := rs (se 4 (by rfl) ⟨10359, by rfl⟩) (B 20719 (by norm_num) ⟨10359, by rfl⟩ (by norm_num))
theorem R110573 : Reach 110573 := rs (se 3 (by rfl) ⟨20732, by rfl⟩) (B 41465 (by norm_num) ⟨20732, by rfl⟩ (by norm_num))
theorem R77861 : Reach 77861 := rs (se 4 (by rfl) ⟨7299, by rfl⟩) (B 14599 (by norm_num) ⟨7299, by rfl⟩ (by norm_num))
theorem R110645 : Reach 110645 := rs (se 5 (by rfl) ⟨5186, by rfl⟩) (B 10373 (by norm_num) ⟨5186, by rfl⟩ (by norm_num))
theorem R143477 : Reach 143477 := rs (se 5 (by rfl) ⟨6725, by rfl⟩) (B 13451 (by norm_num) ⟨6725, by rfl⟩ (by norm_num))
theorem R110717 : Reach 110717 := rs (se 3 (by rfl) ⟨20759, by rfl⟩) (B 41519 (by norm_num) ⟨20759, by rfl⟩ (by norm_num))
theorem R110789 : Reach 110789 := rs (se 4 (by rfl) ⟨10386, by rfl⟩) (B 20773 (by norm_num) ⟨10386, by rfl⟩ (by norm_num))
theorem R110861 : Reach 110861 := rs (se 3 (by rfl) ⟨20786, by rfl⟩) (B 41573 (by norm_num) ⟨20786, by rfl⟩ (by norm_num))
theorem R241973 : Reach 241973 := rs (se 5 (by rfl) ⟨11342, by rfl⟩) (B 22685 (by norm_num) ⟨11342, by rfl⟩ (by norm_num))
theorem R110933 : Reach 110933 := rs (se 10 (by rfl) ⟨162, by rfl⟩) (B 325 (by norm_num) ⟨162, by rfl⟩ (by norm_num))
theorem R111005 : Reach 111005 := rs (se 3 (by rfl) ⟨20813, by rfl⟩) (B 41627 (by norm_num) ⟨20813, by rfl⟩ (by norm_num))
theorem R111077 : Reach 111077 := rs (se 4 (by rfl) ⟨10413, by rfl⟩) (B 20827 (by norm_num) ⟨10413, by rfl⟩ (by norm_num))
theorem R78317 : Reach 78317 := rs (se 3 (by rfl) ⟨14684, by rfl⟩) (B 29369 (by norm_num) ⟨14684, by rfl⟩ (by norm_num))
theorem R209429 : Reach 209429 := rs (se 6 (by rfl) ⟨4908, by rfl⟩) (B 9817 (by norm_num) ⟨4908, by rfl⟩ (by norm_num))
theorem R111149 : Reach 111149 := rs (se 3 (by rfl) ⟨20840, by rfl⟩) (B 41681 (by norm_num) ⟨20840, by rfl⟩ (by norm_num))
theorem R111221 : Reach 111221 := rs (se 5 (by rfl) ⟨5213, by rfl⟩) (B 10427 (by norm_num) ⟨5213, by rfl⟩ (by norm_num))
theorem R111293 : Reach 111293 := rs (se 3 (by rfl) ⟨20867, by rfl⟩) (B 41735 (by norm_num) ⟨20867, by rfl⟩ (by norm_num))
theorem R307957 : Reach 307957 := rs (se 5 (by rfl) ⟨14435, by rfl⟩) (B 28871 (by norm_num) ⟨14435, by rfl⟩ (by norm_num))
theorem R111365 : Reach 111365 := rs (se 4 (by rfl) ⟨10440, by rfl⟩) (B 20881 (by norm_num) ⟨10440, by rfl⟩ (by norm_num))
theorem R176917 : Reach 176917 := rs (se 6 (by rfl) ⟨4146, by rfl⟩) (B 8293 (by norm_num) ⟨4146, by rfl⟩ (by norm_num))
theorem R111437 : Reach 111437 := rs (se 3 (by rfl) ⟨20894, by rfl⟩) (B 41789 (by norm_num) ⟨20894, by rfl⟩ (by norm_num))
theorem R111509 : Reach 111509 := rs (se 6 (by rfl) ⟨2613, by rfl⟩) (B 5227 (by norm_num) ⟨2613, by rfl⟩ (by norm_num))
theorem R111581 : Reach 111581 := rs (se 3 (by rfl) ⟨20921, by rfl⟩) (B 41843 (by norm_num) ⟨20921, by rfl⟩ (by norm_num))
theorem R111653 : Reach 111653 := rs (se 4 (by rfl) ⟨10467, by rfl⟩) (B 20935 (by norm_num) ⟨10467, by rfl⟩ (by norm_num))
theorem R111725 : Reach 111725 := rs (se 3 (by rfl) ⟨20948, by rfl⟩) (B 41897 (by norm_num) ⟨20948, by rfl⟩ (by norm_num))
theorem R242837 : Reach 242837 := rs (se 6 (by rfl) ⟨5691, by rfl⟩) (B 11383 (by norm_num) ⟨5691, by rfl⟩ (by norm_num))
theorem R373909 : Reach 373909 := rs (se 6 (by rfl) ⟨8763, by rfl⟩) (B 17527 (by norm_num) ⟨8763, by rfl⟩ (by norm_num))
theorem R111797 : Reach 111797 := rs (se 5 (by rfl) ⟨5240, by rfl⟩) (B 10481 (by norm_num) ⟨5240, by rfl⟩ (by norm_num))
theorem R111869 : Reach 111869 := rs (se 3 (by rfl) ⟨20975, by rfl⟩) (B 41951 (by norm_num) ⟨20975, by rfl⟩ (by norm_num))
theorem R144661 : Reach 144661 := rs (se 6 (by rfl) ⟨3390, by rfl⟩) (B 6781 (by norm_num) ⟨3390, by rfl⟩ (by norm_num))
theorem R111941 : Reach 111941 := rs (se 4 (by rfl) ⟨10494, by rfl⟩) (B 20989 (by norm_num) ⟨10494, by rfl⟩ (by norm_num))
theorem R112013 : Reach 112013 := rs (se 3 (by rfl) ⟨21002, by rfl⟩) (B 42005 (by norm_num) ⟨21002, by rfl⟩ (by norm_num))
theorem R144821 : Reach 144821 := rs (se 5 (by rfl) ⟨6788, by rfl⟩) (B 13577 (by norm_num) ⟨6788, by rfl⟩ (by norm_num))
theorem R79309 : Reach 79309 := rs (se 3 (by rfl) ⟨14870, by rfl⟩) (B 29741 (by norm_num) ⟨14870, by rfl⟩ (by norm_num))
theorem R112085 : Reach 112085 := rs (se 7 (by rfl) ⟨1313, by rfl⟩) (B 2627 (by norm_num) ⟨1313, by rfl⟩ (by norm_num))
theorem R112157 : Reach 112157 := rs (se 3 (by rfl) ⟨21029, by rfl⟩) (B 42059 (by norm_num) ⟨21029, by rfl⟩ (by norm_num))
theorem R112229 : Reach 112229 := rs (se 4 (by rfl) ⟨10521, by rfl⟩) (B 21043 (by norm_num) ⟨10521, by rfl⟩ (by norm_num))
theorem R145061 : Reach 145061 := rs (se 4 (by rfl) ⟨13599, by rfl⟩) (B 27199 (by norm_num) ⟨13599, by rfl⟩ (by norm_num))
theorem R112301 : Reach 112301 := rs (se 3 (by rfl) ⟨21056, by rfl⟩) (B 42113 (by norm_num) ⟨21056, by rfl⟩ (by norm_num))
theorem R79589 : Reach 79589 := rs (se 4 (by rfl) ⟨7461, by rfl⟩) (B 14923 (by norm_num) ⟨7461, by rfl⟩ (by norm_num))
theorem R112373 : Reach 112373 := rs (se 5 (by rfl) ⟨5267, by rfl⟩) (B 10535 (by norm_num) ⟨5267, by rfl⟩ (by norm_num))
theorem R112445 : Reach 112445 := rs (se 3 (by rfl) ⟨21083, by rfl⟩) (B 42167 (by norm_num) ⟨21083, by rfl⟩ (by norm_num))
theorem R79717 : Reach 79717 := rs (se 4 (by rfl) ⟨7473, by rfl⟩) (B 14947 (by norm_num) ⟨7473, by rfl⟩ (by norm_num))
theorem R145253 : Reach 145253 := rs (se 4 (by rfl) ⟨13617, by rfl⟩) (B 27235 (by norm_num) ⟨13617, by rfl⟩ (by norm_num))
theorem R112517 : Reach 112517 := rs (se 4 (by rfl) ⟨10548, by rfl⟩) (B 21097 (by norm_num) ⟨10548, by rfl⟩ (by norm_num))
theorem R79805 : Reach 79805 := rs (se 3 (by rfl) ⟨14963, by rfl⟩) (B 29927 (by norm_num) ⟨14963, by rfl⟩ (by norm_num))
theorem R112589 : Reach 112589 := rs (se 3 (by rfl) ⟨21110, by rfl⟩) (B 42221 (by norm_num) ⟨21110, by rfl⟩ (by norm_num))
theorem R47121 : Reach 47121 := rs (se 2 (by rfl) ⟨17670, by rfl⟩) (B 35341 (by norm_num) ⟨17670, by rfl⟩ (by norm_num))
theorem R47125 : Reach 47125 := rs (se 6 (by rfl) ⟨1104, by rfl⟩) (B 2209 (by norm_num) ⟨1104, by rfl⟩ (by norm_num))
theorem R112661 : Reach 112661 := rs (se 6 (by rfl) ⟨2640, by rfl⟩) (B 5281 (by norm_num) ⟨2640, by rfl⟩ (by norm_num))
theorem R47129 : Reach 47129 := rs (se 2 (by rfl) ⟨17673, by rfl⟩) (B 35347 (by norm_num) ⟨17673, by rfl⟩ (by norm_num))
theorem R47133 : Reach 47133 := rs (se 3 (by rfl) ⟨8837, by rfl⟩) (B 17675 (by norm_num) ⟨8837, by rfl⟩ (by norm_num))
theorem R47137 : Reach 47137 := rs (se 2 (by rfl) ⟨17676, by rfl⟩) (B 35353 (by norm_num) ⟨17676, by rfl⟩ (by norm_num))
theorem R47141 : Reach 47141 := rs (se 4 (by rfl) ⟨4419, by rfl⟩) (B 8839 (by norm_num) ⟨4419, by rfl⟩ (by norm_num))
theorem R47145 : Reach 47145 := rs (se 2 (by rfl) ⟨17679, by rfl⟩) (B 35359 (by norm_num) ⟨17679, by rfl⟩ (by norm_num))
theorem R47149 : Reach 47149 := rs (se 3 (by rfl) ⟨8840, by rfl⟩) (B 17681 (by norm_num) ⟨8840, by rfl⟩ (by norm_num))
theorem R47153 : Reach 47153 := rs (se 2 (by rfl) ⟨17682, by rfl⟩) (B 35365 (by norm_num) ⟨17682, by rfl⟩ (by norm_num))
theorem R47157 : Reach 47157 := rs (se 5 (by rfl) ⟨2210, by rfl⟩) (B 4421 (by norm_num) ⟨2210, by rfl⟩ (by norm_num))
theorem R47161 : Reach 47161 := rs (se 2 (by rfl) ⟨17685, by rfl⟩) (B 35371 (by norm_num) ⟨17685, by rfl⟩ (by norm_num))
theorem R47165 : Reach 47165 := rs (se 3 (by rfl) ⟨8843, by rfl⟩) (B 17687 (by norm_num) ⟨8843, by rfl⟩ (by norm_num))
theorem R79933 : Reach 79933 := rs (se 3 (by rfl) ⟨14987, by rfl⟩) (B 29975 (by norm_num) ⟨14987, by rfl⟩ (by norm_num))
theorem R47169 : Reach 47169 := rs (se 2 (by rfl) ⟨17688, by rfl⟩) (B 35377 (by norm_num) ⟨17688, by rfl⟩ (by norm_num))
theorem R47173 : Reach 47173 := rs (se 4 (by rfl) ⟨4422, by rfl⟩) (B 8845 (by norm_num) ⟨4422, by rfl⟩ (by norm_num))
theorem R47177 : Reach 47177 := rs (se 2 (by rfl) ⟨17691, by rfl⟩) (B 35383 (by norm_num) ⟨17691, by rfl⟩ (by norm_num))
theorem R47181 : Reach 47181 := rs (se 3 (by rfl) ⟨8846, by rfl⟩) (B 17693 (by norm_num) ⟨8846, by rfl⟩ (by norm_num))
theorem R47185 : Reach 47185 := rs (se 2 (by rfl) ⟨17694, by rfl⟩) (B 35389 (by norm_num) ⟨17694, by rfl⟩ (by norm_num))
theorem R79957 : Reach 79957 := rs (se 8 (by rfl) ⟨468, by rfl⟩) (B 937 (by norm_num) ⟨468, by rfl⟩ (by norm_num))
theorem R47189 : Reach 47189 := rs (se 8 (by rfl) ⟨276, by rfl⟩) (B 553 (by norm_num) ⟨276, by rfl⟩ (by norm_num))
theorem R47193 : Reach 47193 := rs (se 2 (by rfl) ⟨17697, by rfl⟩) (B 35395 (by norm_num) ⟨17697, by rfl⟩ (by norm_num))
theorem R47197 : Reach 47197 := rs (se 3 (by rfl) ⟨8849, by rfl⟩) (B 17699 (by norm_num) ⟨8849, by rfl⟩ (by norm_num))
theorem R112733 : Reach 112733 := rs (se 3 (by rfl) ⟨21137, by rfl⟩) (B 42275 (by norm_num) ⟨21137, by rfl⟩ (by norm_num))
theorem R47201 : Reach 47201 := rs (se 2 (by rfl) ⟨17700, by rfl⟩) (B 35401 (by norm_num) ⟨17700, by rfl⟩ (by norm_num))
theorem R47205 : Reach 47205 := rs (se 4 (by rfl) ⟨4425, by rfl⟩) (B 8851 (by norm_num) ⟨4425, by rfl⟩ (by norm_num))
theorem R47209 : Reach 47209 := rs (se 2 (by rfl) ⟨17703, by rfl⟩) (B 35407 (by norm_num) ⟨17703, by rfl⟩ (by norm_num))
theorem R47213 : Reach 47213 := rs (se 3 (by rfl) ⟨8852, by rfl⟩) (B 17705 (by norm_num) ⟨8852, by rfl⟩ (by norm_num))
theorem R47217 : Reach 47217 := rs (se 2 (by rfl) ⟨17706, by rfl⟩) (B 35413 (by norm_num) ⟨17706, by rfl⟩ (by norm_num))
theorem R47221 : Reach 47221 := rs (se 5 (by rfl) ⟨2213, by rfl⟩) (B 4427 (by norm_num) ⟨2213, by rfl⟩ (by norm_num))
theorem R47225 : Reach 47225 := rs (se 2 (by rfl) ⟨17709, by rfl⟩) (B 35419 (by norm_num) ⟨17709, by rfl⟩ (by norm_num))
theorem R47229 : Reach 47229 := rs (se 3 (by rfl) ⟨8855, by rfl⟩) (B 17711 (by norm_num) ⟨8855, by rfl⟩ (by norm_num))
theorem R47233 : Reach 47233 := rs (se 2 (by rfl) ⟨17712, by rfl⟩) (B 35425 (by norm_num) ⟨17712, by rfl⟩ (by norm_num))
theorem R47237 : Reach 47237 := rs (se 4 (by rfl) ⟨4428, by rfl⟩) (B 8857 (by norm_num) ⟨4428, by rfl⟩ (by norm_num))
theorem R47241 : Reach 47241 := rs (se 2 (by rfl) ⟨17715, by rfl⟩) (B 35431 (by norm_num) ⟨17715, by rfl⟩ (by norm_num))
theorem R47245 : Reach 47245 := rs (se 3 (by rfl) ⟨8858, by rfl⟩) (B 17717 (by norm_num) ⟨8858, by rfl⟩ (by norm_num))
theorem R47249 : Reach 47249 := rs (se 2 (by rfl) ⟨17718, by rfl⟩) (B 35437 (by norm_num) ⟨17718, by rfl⟩ (by norm_num))
theorem R47253 : Reach 47253 := rs (se 6 (by rfl) ⟨1107, by rfl⟩) (B 2215 (by norm_num) ⟨1107, by rfl⟩ (by norm_num))
theorem R80021 : Reach 80021 := rs (se 6 (by rfl) ⟨1875, by rfl⟩) (B 3751 (by norm_num) ⟨1875, by rfl⟩ (by norm_num))
theorem R47257 : Reach 47257 := rs (se 2 (by rfl) ⟨17721, by rfl⟩) (B 35443 (by norm_num) ⟨17721, by rfl⟩ (by norm_num))
theorem R47261 : Reach 47261 := rs (se 3 (by rfl) ⟨8861, by rfl⟩) (B 17723 (by norm_num) ⟨8861, by rfl⟩ (by norm_num))
theorem R47265 : Reach 47265 := rs (se 2 (by rfl) ⟨17724, by rfl⟩) (B 35449 (by norm_num) ⟨17724, by rfl⟩ (by norm_num))
theorem R47269 : Reach 47269 := rs (se 4 (by rfl) ⟨4431, by rfl⟩) (B 8863 (by norm_num) ⟨4431, by rfl⟩ (by norm_num))
theorem R112805 : Reach 112805 := rs (se 4 (by rfl) ⟨10575, by rfl⟩) (B 21151 (by norm_num) ⟨10575, by rfl⟩ (by norm_num))
theorem R47273 : Reach 47273 := rs (se 2 (by rfl) ⟨17727, by rfl⟩) (B 35455 (by norm_num) ⟨17727, by rfl⟩ (by norm_num))
theorem R47277 : Reach 47277 := rs (se 3 (by rfl) ⟨8864, by rfl⟩) (B 17729 (by norm_num) ⟨8864, by rfl⟩ (by norm_num))
theorem R47281 : Reach 47281 := rs (se 2 (by rfl) ⟨17730, by rfl⟩) (B 35461 (by norm_num) ⟨17730, by rfl⟩ (by norm_num))
theorem R47285 : Reach 47285 := rs (se 5 (by rfl) ⟨2216, by rfl⟩) (B 4433 (by norm_num) ⟨2216, by rfl⟩ (by norm_num))
theorem R47289 : Reach 47289 := rs (se 2 (by rfl) ⟨17733, by rfl⟩) (B 35467 (by norm_num) ⟨17733, by rfl⟩ (by norm_num))
theorem R47293 : Reach 47293 := rs (se 3 (by rfl) ⟨8867, by rfl⟩) (B 17735 (by norm_num) ⟨8867, by rfl⟩ (by norm_num))
theorem R47297 : Reach 47297 := rs (se 2 (by rfl) ⟨17736, by rfl⟩) (B 35473 (by norm_num) ⟨17736, by rfl⟩ (by norm_num))
theorem R47301 : Reach 47301 := rs (se 4 (by rfl) ⟨4434, by rfl⟩) (B 8869 (by norm_num) ⟨4434, by rfl⟩ (by norm_num))
theorem R47305 : Reach 47305 := rs (se 2 (by rfl) ⟨17739, by rfl⟩) (B 35479 (by norm_num) ⟨17739, by rfl⟩ (by norm_num))
theorem R47309 : Reach 47309 := rs (se 3 (by rfl) ⟨8870, by rfl⟩) (B 17741 (by norm_num) ⟨8870, by rfl⟩ (by norm_num))
theorem R47313 : Reach 47313 := rs (se 2 (by rfl) ⟨17742, by rfl⟩) (B 35485 (by norm_num) ⟨17742, by rfl⟩ (by norm_num))
theorem R47317 : Reach 47317 := rs (se 7 (by rfl) ⟨554, by rfl⟩) (B 1109 (by norm_num) ⟨554, by rfl⟩ (by norm_num))
theorem R211157 : Reach 211157 := rs (se 7 (by rfl) ⟨2474, by rfl⟩) (B 4949 (by norm_num) ⟨2474, by rfl⟩ (by norm_num))
theorem R47321 : Reach 47321 := rs (se 2 (by rfl) ⟨17745, by rfl⟩) (B 35491 (by norm_num) ⟨17745, by rfl⟩ (by norm_num))
theorem R47325 : Reach 47325 := rs (se 3 (by rfl) ⟨8873, by rfl⟩) (B 17747 (by norm_num) ⟨8873, by rfl⟩ (by norm_num))
theorem R47329 : Reach 47329 := rs (se 2 (by rfl) ⟨17748, by rfl⟩) (B 35497 (by norm_num) ⟨17748, by rfl⟩ (by norm_num))
theorem R47333 : Reach 47333 := rs (se 4 (by rfl) ⟨4437, by rfl⟩) (B 8875 (by norm_num) ⟨4437, by rfl⟩ (by norm_num))
theorem R47337 : Reach 47337 := rs (se 2 (by rfl) ⟨17751, by rfl⟩) (B 35503 (by norm_num) ⟨17751, by rfl⟩ (by norm_num))
theorem R47341 : Reach 47341 := rs (se 3 (by rfl) ⟨8876, by rfl⟩) (B 17753 (by norm_num) ⟨8876, by rfl⟩ (by norm_num))
theorem R112877 : Reach 112877 := rs (se 3 (by rfl) ⟨21164, by rfl⟩) (B 42329 (by norm_num) ⟨21164, by rfl⟩ (by norm_num))
theorem R47345 : Reach 47345 := rs (se 2 (by rfl) ⟨17754, by rfl⟩) (B 35509 (by norm_num) ⟨17754, by rfl⟩ (by norm_num))
theorem R47349 : Reach 47349 := rs (se 5 (by rfl) ⟨2219, by rfl⟩) (B 4439 (by norm_num) ⟨2219, by rfl⟩ (by norm_num))
theorem R47353 : Reach 47353 := rs (se 2 (by rfl) ⟨17757, by rfl⟩) (B 35515 (by norm_num) ⟨17757, by rfl⟩ (by norm_num))
theorem R47357 : Reach 47357 := rs (se 3 (by rfl) ⟨8879, by rfl⟩) (B 17759 (by norm_num) ⟨8879, by rfl⟩ (by norm_num))
theorem R47361 : Reach 47361 := rs (se 2 (by rfl) ⟨17760, by rfl⟩) (B 35521 (by norm_num) ⟨17760, by rfl⟩ (by norm_num))
theorem R47365 : Reach 47365 := rs (se 4 (by rfl) ⟨4440, by rfl⟩) (B 8881 (by norm_num) ⟨4440, by rfl⟩ (by norm_num))
theorem R47369 : Reach 47369 := rs (se 2 (by rfl) ⟨17763, by rfl⟩) (B 35527 (by norm_num) ⟨17763, by rfl⟩ (by norm_num))
theorem R47373 : Reach 47373 := rs (se 3 (by rfl) ⟨8882, by rfl⟩) (B 17765 (by norm_num) ⟨8882, by rfl⟩ (by norm_num))
theorem R47377 : Reach 47377 := rs (se 2 (by rfl) ⟨17766, by rfl⟩) (B 35533 (by norm_num) ⟨17766, by rfl⟩ (by norm_num))
theorem R47381 : Reach 47381 := rs (se 6 (by rfl) ⟨1110, by rfl⟩) (B 2221 (by norm_num) ⟨1110, by rfl⟩ (by norm_num))
theorem R80149 : Reach 80149 := rs (se 6 (by rfl) ⟨1878, by rfl⟩) (B 3757 (by norm_num) ⟨1878, by rfl⟩ (by norm_num))
theorem R47385 : Reach 47385 := rs (se 2 (by rfl) ⟨17769, by rfl⟩) (B 35539 (by norm_num) ⟨17769, by rfl⟩ (by norm_num))
theorem R47389 : Reach 47389 := rs (se 3 (by rfl) ⟨8885, by rfl⟩) (B 17771 (by norm_num) ⟨8885, by rfl⟩ (by norm_num))
theorem R47393 : Reach 47393 := rs (se 2 (by rfl) ⟨17772, by rfl⟩) (B 35545 (by norm_num) ⟨17772, by rfl⟩ (by norm_num))
theorem R47397 : Reach 47397 := rs (se 4 (by rfl) ⟨4443, by rfl⟩) (B 8887 (by norm_num) ⟨4443, by rfl⟩ (by norm_num))
theorem R47401 : Reach 47401 := rs (se 2 (by rfl) ⟨17775, by rfl⟩) (B 35551 (by norm_num) ⟨17775, by rfl⟩ (by norm_num))
theorem R47405 : Reach 47405 := rs (se 3 (by rfl) ⟨8888, by rfl⟩) (B 17777 (by norm_num) ⟨8888, by rfl⟩ (by norm_num))
theorem R47409 : Reach 47409 := rs (se 2 (by rfl) ⟨17778, by rfl⟩) (B 35557 (by norm_num) ⟨17778, by rfl⟩ (by norm_num))
theorem R47413 : Reach 47413 := rs (se 5 (by rfl) ⟨2222, by rfl⟩) (B 4445 (by norm_num) ⟨2222, by rfl⟩ (by norm_num))
theorem R112949 : Reach 112949 := rs (se 5 (by rfl) ⟨5294, by rfl⟩) (B 10589 (by norm_num) ⟨5294, by rfl⟩ (by norm_num))
theorem R47417 : Reach 47417 := rs (se 2 (by rfl) ⟨17781, by rfl⟩) (B 35563 (by norm_num) ⟨17781, by rfl⟩ (by norm_num))
theorem R47421 : Reach 47421 := rs (se 3 (by rfl) ⟨8891, by rfl⟩) (B 17783 (by norm_num) ⟨8891, by rfl⟩ (by norm_num))
theorem R47425 : Reach 47425 := rs (se 2 (by rfl) ⟨17784, by rfl⟩) (B 35569 (by norm_num) ⟨17784, by rfl⟩ (by norm_num))
theorem R47429 : Reach 47429 := rs (se 4 (by rfl) ⟨4446, by rfl⟩) (B 8893 (by norm_num) ⟨4446, by rfl⟩ (by norm_num))
theorem R47433 : Reach 47433 := rs (se 2 (by rfl) ⟨17787, by rfl⟩) (B 35575 (by norm_num) ⟨17787, by rfl⟩ (by norm_num))
theorem R47437 : Reach 47437 := rs (se 3 (by rfl) ⟨8894, by rfl⟩) (B 17789 (by norm_num) ⟨8894, by rfl⟩ (by norm_num))
theorem R47441 : Reach 47441 := rs (se 2 (by rfl) ⟨17790, by rfl⟩) (B 35581 (by norm_num) ⟨17790, by rfl⟩ (by norm_num))
theorem R47445 : Reach 47445 := rs (se 10 (by rfl) ⟨69, by rfl⟩) (B 139 (by norm_num) ⟨69, by rfl⟩ (by norm_num))
theorem R47449 : Reach 47449 := rs (se 2 (by rfl) ⟨17793, by rfl⟩) (B 35587 (by norm_num) ⟨17793, by rfl⟩ (by norm_num))
theorem R47453 : Reach 47453 := rs (se 3 (by rfl) ⟨8897, by rfl⟩) (B 17795 (by norm_num) ⟨8897, by rfl⟩ (by norm_num))
theorem R47457 : Reach 47457 := rs (se 2 (by rfl) ⟨17796, by rfl⟩) (B 35593 (by norm_num) ⟨17796, by rfl⟩ (by norm_num))
theorem R47461 : Reach 47461 := rs (se 4 (by rfl) ⟨4449, by rfl⟩) (B 8899 (by norm_num) ⟨4449, by rfl⟩ (by norm_num))
theorem R47465 : Reach 47465 := rs (se 2 (by rfl) ⟨17799, by rfl⟩) (B 35599 (by norm_num) ⟨17799, by rfl⟩ (by norm_num))
theorem R47469 : Reach 47469 := rs (se 3 (by rfl) ⟨8900, by rfl⟩) (B 17801 (by norm_num) ⟨8900, by rfl⟩ (by norm_num))
theorem R80237 : Reach 80237 := rs (se 3 (by rfl) ⟨15044, by rfl⟩) (B 30089 (by norm_num) ⟨15044, by rfl⟩ (by norm_num))
theorem R47473 : Reach 47473 := rs (se 2 (by rfl) ⟨17802, by rfl⟩) (B 35605 (by norm_num) ⟨17802, by rfl⟩ (by norm_num))
theorem R47477 : Reach 47477 := rs (se 5 (by rfl) ⟨2225, by rfl⟩) (B 4451 (by norm_num) ⟨2225, by rfl⟩ (by norm_num))
theorem R47481 : Reach 47481 := rs (se 2 (by rfl) ⟨17805, by rfl⟩) (B 35611 (by norm_num) ⟨17805, by rfl⟩ (by norm_num))
theorem R47485 : Reach 47485 := rs (se 3 (by rfl) ⟨8903, by rfl⟩) (B 17807 (by norm_num) ⟨8903, by rfl⟩ (by norm_num))
theorem R113021 : Reach 113021 := rs (se 3 (by rfl) ⟨21191, by rfl⟩) (B 42383 (by norm_num) ⟨21191, by rfl⟩ (by norm_num))
theorem R47489 : Reach 47489 := rs (se 2 (by rfl) ⟨17808, by rfl⟩) (B 35617 (by norm_num) ⟨17808, by rfl⟩ (by norm_num))
theorem R47493 : Reach 47493 := rs (se 4 (by rfl) ⟨4452, by rfl⟩) (B 8905 (by norm_num) ⟨4452, by rfl⟩ (by norm_num))
theorem R47497 : Reach 47497 := rs (se 2 (by rfl) ⟨17811, by rfl⟩) (B 35623 (by norm_num) ⟨17811, by rfl⟩ (by norm_num))
theorem R47501 : Reach 47501 := rs (se 3 (by rfl) ⟨8906, by rfl⟩) (B 17813 (by norm_num) ⟨8906, by rfl⟩ (by norm_num))
theorem R47505 : Reach 47505 := rs (se 2 (by rfl) ⟨17814, by rfl⟩) (B 35629 (by norm_num) ⟨17814, by rfl⟩ (by norm_num))
theorem R47509 : Reach 47509 := rs (se 6 (by rfl) ⟨1113, by rfl⟩) (B 2227 (by norm_num) ⟨1113, by rfl⟩ (by norm_num))
theorem R47513 : Reach 47513 := rs (se 2 (by rfl) ⟨17817, by rfl⟩) (B 35635 (by norm_num) ⟨17817, by rfl⟩ (by norm_num))
theorem R47517 : Reach 47517 := rs (se 3 (by rfl) ⟨8909, by rfl⟩) (B 17819 (by norm_num) ⟨8909, by rfl⟩ (by norm_num))
theorem R47521 : Reach 47521 := rs (se 2 (by rfl) ⟨17820, by rfl⟩) (B 35641 (by norm_num) ⟨17820, by rfl⟩ (by norm_num))
theorem R47525 : Reach 47525 := rs (se 4 (by rfl) ⟨4455, by rfl⟩) (B 8911 (by norm_num) ⟨4455, by rfl⟩ (by norm_num))
theorem R244133 : Reach 244133 := rs (se 4 (by rfl) ⟨22887, by rfl⟩) (B 45775 (by norm_num) ⟨22887, by rfl⟩ (by norm_num))
theorem R47529 : Reach 47529 := rs (se 2 (by rfl) ⟨17823, by rfl⟩) (B 35647 (by norm_num) ⟨17823, by rfl⟩ (by norm_num))
theorem R47533 : Reach 47533 := rs (se 3 (by rfl) ⟨8912, by rfl⟩) (B 17825 (by norm_num) ⟨8912, by rfl⟩ (by norm_num))
theorem R47537 : Reach 47537 := rs (se 2 (by rfl) ⟨17826, by rfl⟩) (B 35653 (by norm_num) ⟨17826, by rfl⟩ (by norm_num))
theorem R47541 : Reach 47541 := rs (se 5 (by rfl) ⟨2228, by rfl⟩) (B 4457 (by norm_num) ⟨2228, by rfl⟩ (by norm_num))
theorem R47545 : Reach 47545 := rs (se 2 (by rfl) ⟨17829, by rfl⟩) (B 35659 (by norm_num) ⟨17829, by rfl⟩ (by norm_num))
theorem R47549 : Reach 47549 := rs (se 3 (by rfl) ⟨8915, by rfl⟩) (B 17831 (by norm_num) ⟨8915, by rfl⟩ (by norm_num))
theorem R47553 : Reach 47553 := rs (se 2 (by rfl) ⟨17832, by rfl⟩) (B 35665 (by norm_num) ⟨17832, by rfl⟩ (by norm_num))
theorem R47557 : Reach 47557 := rs (se 4 (by rfl) ⟨4458, by rfl⟩) (B 8917 (by norm_num) ⟨4458, by rfl⟩ (by norm_num))
theorem R113093 : Reach 113093 := rs (se 4 (by rfl) ⟨10602, by rfl⟩) (B 21205 (by norm_num) ⟨10602, by rfl⟩ (by norm_num))
theorem R47561 : Reach 47561 := rs (se 2 (by rfl) ⟨17835, by rfl⟩) (B 35671 (by norm_num) ⟨17835, by rfl⟩ (by norm_num))
theorem R47565 : Reach 47565 := rs (se 3 (by rfl) ⟨8918, by rfl⟩) (B 17837 (by norm_num) ⟨8918, by rfl⟩ (by norm_num))
theorem R47569 : Reach 47569 := rs (se 2 (by rfl) ⟨17838, by rfl⟩) (B 35677 (by norm_num) ⟨17838, by rfl⟩ (by norm_num))
theorem R47573 : Reach 47573 := rs (se 7 (by rfl) ⟨557, by rfl⟩) (B 1115 (by norm_num) ⟨557, by rfl⟩ (by norm_num))
theorem R47577 : Reach 47577 := rs (se 2 (by rfl) ⟨17841, by rfl⟩) (B 35683 (by norm_num) ⟨17841, by rfl⟩ (by norm_num))
theorem R47581 : Reach 47581 := rs (se 3 (by rfl) ⟨8921, by rfl⟩) (B 17843 (by norm_num) ⟨8921, by rfl⟩ (by norm_num))
theorem R47585 : Reach 47585 := rs (se 2 (by rfl) ⟨17844, by rfl⟩) (B 35689 (by norm_num) ⟨17844, by rfl⟩ (by norm_num))
theorem R47589 : Reach 47589 := rs (se 4 (by rfl) ⟨4461, by rfl⟩) (B 8923 (by norm_num) ⟨4461, by rfl⟩ (by norm_num))
theorem R47593 : Reach 47593 := rs (se 2 (by rfl) ⟨17847, by rfl⟩) (B 35695 (by norm_num) ⟨17847, by rfl⟩ (by norm_num))
theorem R47597 : Reach 47597 := rs (se 3 (by rfl) ⟨8924, by rfl⟩) (B 17849 (by norm_num) ⟨8924, by rfl⟩ (by norm_num))
theorem R80365 : Reach 80365 := rs (se 3 (by rfl) ⟨15068, by rfl⟩) (B 30137 (by norm_num) ⟨15068, by rfl⟩ (by norm_num))
theorem R47601 : Reach 47601 := rs (se 2 (by rfl) ⟨17850, by rfl⟩) (B 35701 (by norm_num) ⟨17850, by rfl⟩ (by norm_num))
theorem R47605 : Reach 47605 := rs (se 5 (by rfl) ⟨2231, by rfl⟩) (B 4463 (by norm_num) ⟨2231, by rfl⟩ (by norm_num))
theorem R47609 : Reach 47609 := rs (se 2 (by rfl) ⟨17853, by rfl⟩) (B 35707 (by norm_num) ⟨17853, by rfl⟩ (by norm_num))
theorem R47613 : Reach 47613 := rs (se 3 (by rfl) ⟨8927, by rfl⟩) (B 17855 (by norm_num) ⟨8927, by rfl⟩ (by norm_num))
theorem R47617 : Reach 47617 := rs (se 2 (by rfl) ⟨17856, by rfl⟩) (B 35713 (by norm_num) ⟨17856, by rfl⟩ (by norm_num))
theorem R47621 : Reach 47621 := rs (se 4 (by rfl) ⟨4464, by rfl⟩) (B 8929 (by norm_num) ⟨4464, by rfl⟩ (by norm_num))
theorem R47625 : Reach 47625 := rs (se 2 (by rfl) ⟨17859, by rfl⟩) (B 35719 (by norm_num) ⟨17859, by rfl⟩ (by norm_num))
theorem R47629 : Reach 47629 := rs (se 3 (by rfl) ⟨8930, by rfl⟩) (B 17861 (by norm_num) ⟨8930, by rfl⟩ (by norm_num))
theorem R113165 : Reach 113165 := rs (se 3 (by rfl) ⟨21218, by rfl⟩) (B 42437 (by norm_num) ⟨21218, by rfl⟩ (by norm_num))
theorem R47633 : Reach 47633 := rs (se 2 (by rfl) ⟨17862, by rfl⟩) (B 35725 (by norm_num) ⟨17862, by rfl⟩ (by norm_num))
theorem R47637 : Reach 47637 := rs (se 6 (by rfl) ⟨1116, by rfl⟩) (B 2233 (by norm_num) ⟨1116, by rfl⟩ (by norm_num))
theorem R47641 : Reach 47641 := rs (se 2 (by rfl) ⟨17865, by rfl⟩) (B 35731 (by norm_num) ⟨17865, by rfl⟩ (by norm_num))
theorem R47645 : Reach 47645 := rs (se 3 (by rfl) ⟨8933, by rfl⟩) (B 17867 (by norm_num) ⟨8933, by rfl⟩ (by norm_num))
theorem R47649 : Reach 47649 := rs (se 2 (by rfl) ⟨17868, by rfl⟩) (B 35737 (by norm_num) ⟨17868, by rfl⟩ (by norm_num))
theorem R47653 : Reach 47653 := rs (se 4 (by rfl) ⟨4467, by rfl⟩) (B 8935 (by norm_num) ⟨4467, by rfl⟩ (by norm_num))
theorem R47657 : Reach 47657 := rs (se 2 (by rfl) ⟨17871, by rfl⟩) (B 35743 (by norm_num) ⟨17871, by rfl⟩ (by norm_num))
theorem R47661 : Reach 47661 := rs (se 3 (by rfl) ⟨8936, by rfl⟩) (B 17873 (by norm_num) ⟨8936, by rfl⟩ (by norm_num))
theorem R47665 : Reach 47665 := rs (se 2 (by rfl) ⟨17874, by rfl⟩) (B 35749 (by norm_num) ⟨17874, by rfl⟩ (by norm_num))
theorem R47669 : Reach 47669 := rs (se 5 (by rfl) ⟨2234, by rfl⟩) (B 4469 (by norm_num) ⟨2234, by rfl⟩ (by norm_num))
theorem R47673 : Reach 47673 := rs (se 2 (by rfl) ⟨17877, by rfl⟩) (B 35755 (by norm_num) ⟨17877, by rfl⟩ (by norm_num))
theorem R47677 : Reach 47677 := rs (se 3 (by rfl) ⟨8939, by rfl⟩) (B 17879 (by norm_num) ⟨8939, by rfl⟩ (by norm_num))
theorem R47681 : Reach 47681 := rs (se 2 (by rfl) ⟨17880, by rfl⟩) (B 35761 (by norm_num) ⟨17880, by rfl⟩ (by norm_num))
theorem R80453 : Reach 80453 := rs (se 4 (by rfl) ⟨7542, by rfl⟩) (B 15085 (by norm_num) ⟨7542, by rfl⟩ (by norm_num))
theorem R47685 : Reach 47685 := rs (se 4 (by rfl) ⟨4470, by rfl⟩) (B 8941 (by norm_num) ⟨4470, by rfl⟩ (by norm_num))
theorem R47689 : Reach 47689 := rs (se 2 (by rfl) ⟨17883, by rfl⟩) (B 35767 (by norm_num) ⟨17883, by rfl⟩ (by norm_num))
theorem R47693 : Reach 47693 := rs (se 3 (by rfl) ⟨8942, by rfl⟩) (B 17885 (by norm_num) ⟨8942, by rfl⟩ (by norm_num))
theorem R47697 : Reach 47697 := rs (se 2 (by rfl) ⟨17886, by rfl⟩) (B 35773 (by norm_num) ⟨17886, by rfl⟩ (by norm_num))
theorem R47701 : Reach 47701 := rs (se 8 (by rfl) ⟨279, by rfl⟩) (B 559 (by norm_num) ⟨279, by rfl⟩ (by norm_num))
theorem R408149 : Reach 408149 := rs (se 8 (by rfl) ⟨2391, by rfl⟩) (B 4783 (by norm_num) ⟨2391, by rfl⟩ (by norm_num))
theorem R113237 : Reach 113237 := rs (se 8 (by rfl) ⟨663, by rfl⟩) (B 1327 (by norm_num) ⟨663, by rfl⟩ (by norm_num))
theorem R47705 : Reach 47705 := rs (se 2 (by rfl) ⟨17889, by rfl⟩) (B 35779 (by norm_num) ⟨17889, by rfl⟩ (by norm_num))
theorem R47709 : Reach 47709 := rs (se 3 (by rfl) ⟨8945, by rfl⟩) (B 17891 (by norm_num) ⟨8945, by rfl⟩ (by norm_num))
theorem R47713 : Reach 47713 := rs (se 2 (by rfl) ⟨17892, by rfl⟩) (B 35785 (by norm_num) ⟨17892, by rfl⟩ (by norm_num))
theorem R47717 : Reach 47717 := rs (se 4 (by rfl) ⟨4473, by rfl⟩) (B 8947 (by norm_num) ⟨4473, by rfl⟩ (by norm_num))
theorem R47721 : Reach 47721 := rs (se 2 (by rfl) ⟨17895, by rfl⟩) (B 35791 (by norm_num) ⟨17895, by rfl⟩ (by norm_num))
theorem R47725 : Reach 47725 := rs (se 3 (by rfl) ⟨8948, by rfl⟩) (B 17897 (by norm_num) ⟨8948, by rfl⟩ (by norm_num))
theorem R47729 : Reach 47729 := rs (se 2 (by rfl) ⟨17898, by rfl⟩) (B 35797 (by norm_num) ⟨17898, by rfl⟩ (by norm_num))
theorem R113269 : Reach 113269 := rs (se 5 (by rfl) ⟨5309, by rfl⟩) (B 10619 (by norm_num) ⟨5309, by rfl⟩ (by norm_num))
theorem R47733 : Reach 47733 := rs (se 5 (by rfl) ⟨2237, by rfl⟩) (B 4475 (by norm_num) ⟨2237, by rfl⟩ (by norm_num))
theorem R47737 : Reach 47737 := rs (se 2 (by rfl) ⟨17901, by rfl⟩) (B 35803 (by norm_num) ⟨17901, by rfl⟩ (by norm_num))
theorem R47741 : Reach 47741 := rs (se 3 (by rfl) ⟨8951, by rfl⟩) (B 17903 (by norm_num) ⟨8951, by rfl⟩ (by norm_num))
theorem R47745 : Reach 47745 := rs (se 2 (by rfl) ⟨17904, by rfl⟩) (B 35809 (by norm_num) ⟨17904, by rfl⟩ (by norm_num))
theorem R47749 : Reach 47749 := rs (se 4 (by rfl) ⟨4476, by rfl⟩) (B 8953 (by norm_num) ⟨4476, by rfl⟩ (by norm_num))
theorem R47753 : Reach 47753 := rs (se 2 (by rfl) ⟨17907, by rfl⟩) (B 35815 (by norm_num) ⟨17907, by rfl⟩ (by norm_num))
theorem R47757 : Reach 47757 := rs (se 3 (by rfl) ⟨8954, by rfl⟩) (B 17909 (by norm_num) ⟨8954, by rfl⟩ (by norm_num))
theorem R47761 : Reach 47761 := rs (se 2 (by rfl) ⟨17910, by rfl⟩) (B 35821 (by norm_num) ⟨17910, by rfl⟩ (by norm_num))
theorem R47765 : Reach 47765 := rs (se 6 (by rfl) ⟨1119, by rfl⟩) (B 2239 (by norm_num) ⟨1119, by rfl⟩ (by norm_num))
theorem R47769 : Reach 47769 := rs (se 2 (by rfl) ⟨17913, by rfl⟩) (B 35827 (by norm_num) ⟨17913, by rfl⟩ (by norm_num))
theorem R47773 : Reach 47773 := rs (se 3 (by rfl) ⟨8957, by rfl⟩) (B 17915 (by norm_num) ⟨8957, by rfl⟩ (by norm_num))
theorem R113309 : Reach 113309 := rs (se 3 (by rfl) ⟨21245, by rfl⟩) (B 42491 (by norm_num) ⟨21245, by rfl⟩ (by norm_num))
theorem R47777 : Reach 47777 := rs (se 2 (by rfl) ⟨17916, by rfl⟩) (B 35833 (by norm_num) ⟨17916, by rfl⟩ (by norm_num))
theorem R47781 : Reach 47781 := rs (se 4 (by rfl) ⟨4479, by rfl⟩) (B 8959 (by norm_num) ⟨4479, by rfl⟩ (by norm_num))
theorem R47785 : Reach 47785 := rs (se 2 (by rfl) ⟨17919, by rfl⟩) (B 35839 (by norm_num) ⟨17919, by rfl⟩ (by norm_num))
theorem R47789 : Reach 47789 := rs (se 3 (by rfl) ⟨8960, by rfl⟩) (B 17921 (by norm_num) ⟨8960, by rfl⟩ (by norm_num))
theorem R47793 : Reach 47793 := rs (se 2 (by rfl) ⟨17922, by rfl⟩) (B 35845 (by norm_num) ⟨17922, by rfl⟩ (by norm_num))
theorem R47797 : Reach 47797 := rs (se 5 (by rfl) ⟨2240, by rfl⟩) (B 4481 (by norm_num) ⟨2240, by rfl⟩ (by norm_num))
theorem R47801 : Reach 47801 := rs (se 2 (by rfl) ⟨17925, by rfl⟩) (B 35851 (by norm_num) ⟨17925, by rfl⟩ (by norm_num))
theorem R47805 : Reach 47805 := rs (se 3 (by rfl) ⟨8963, by rfl⟩) (B 17927 (by norm_num) ⟨8963, by rfl⟩ (by norm_num))
theorem R47809 : Reach 47809 := rs (se 2 (by rfl) ⟨17928, by rfl⟩) (B 35857 (by norm_num) ⟨17928, by rfl⟩ (by norm_num))
theorem R80581 : Reach 80581 := rs (se 4 (by rfl) ⟨7554, by rfl⟩) (B 15109 (by norm_num) ⟨7554, by rfl⟩ (by norm_num))
theorem R47813 : Reach 47813 := rs (se 4 (by rfl) ⟨4482, by rfl⟩) (B 8965 (by norm_num) ⟨4482, by rfl⟩ (by norm_num))
theorem R47817 : Reach 47817 := rs (se 2 (by rfl) ⟨17931, by rfl⟩) (B 35863 (by norm_num) ⟨17931, by rfl⟩ (by norm_num))
theorem R47821 : Reach 47821 := rs (se 3 (by rfl) ⟨8966, by rfl⟩) (B 17933 (by norm_num) ⟨8966, by rfl⟩ (by norm_num))
theorem R47825 : Reach 47825 := rs (se 2 (by rfl) ⟨17934, by rfl⟩) (B 35869 (by norm_num) ⟨17934, by rfl⟩ (by norm_num))
theorem R47829 : Reach 47829 := rs (se 7 (by rfl) ⟨560, by rfl⟩) (B 1121 (by norm_num) ⟨560, by rfl⟩ (by norm_num))
theorem R47833 : Reach 47833 := rs (se 2 (by rfl) ⟨17937, by rfl⟩) (B 35875 (by norm_num) ⟨17937, by rfl⟩ (by norm_num))
theorem R47837 : Reach 47837 := rs (se 3 (by rfl) ⟨8969, by rfl⟩) (B 17939 (by norm_num) ⟨8969, by rfl⟩ (by norm_num))
theorem R47841 : Reach 47841 := rs (se 2 (by rfl) ⟨17940, by rfl⟩) (B 35881 (by norm_num) ⟨17940, by rfl⟩ (by norm_num))
theorem R47845 : Reach 47845 := rs (se 4 (by rfl) ⟨4485, by rfl⟩) (B 8971 (by norm_num) ⟨4485, by rfl⟩ (by norm_num))
theorem R113381 : Reach 113381 := rs (se 4 (by rfl) ⟨10629, by rfl⟩) (B 21259 (by norm_num) ⟨10629, by rfl⟩ (by norm_num))
theorem R47849 : Reach 47849 := rs (se 2 (by rfl) ⟨17943, by rfl⟩) (B 35887 (by norm_num) ⟨17943, by rfl⟩ (by norm_num))
theorem R47853 : Reach 47853 := rs (se 3 (by rfl) ⟨8972, by rfl⟩) (B 17945 (by norm_num) ⟨8972, by rfl⟩ (by norm_num))
theorem R47857 : Reach 47857 := rs (se 2 (by rfl) ⟨17946, by rfl⟩) (B 35893 (by norm_num) ⟨17946, by rfl⟩ (by norm_num))
theorem R47861 : Reach 47861 := rs (se 5 (by rfl) ⟨2243, by rfl⟩) (B 4487 (by norm_num) ⟨2243, by rfl⟩ (by norm_num))
theorem R47865 : Reach 47865 := rs (se 2 (by rfl) ⟨17949, by rfl⟩) (B 35899 (by norm_num) ⟨17949, by rfl⟩ (by norm_num))
theorem R47869 : Reach 47869 := rs (se 3 (by rfl) ⟨8975, by rfl⟩) (B 17951 (by norm_num) ⟨8975, by rfl⟩ (by norm_num))
theorem R47873 : Reach 47873 := rs (se 2 (by rfl) ⟨17952, by rfl⟩) (B 35905 (by norm_num) ⟨17952, by rfl⟩ (by norm_num))
theorem R47877 : Reach 47877 := rs (se 4 (by rfl) ⟨4488, by rfl⟩) (B 8977 (by norm_num) ⟨4488, by rfl⟩ (by norm_num))
theorem R47881 : Reach 47881 := rs (se 2 (by rfl) ⟨17955, by rfl⟩) (B 35911 (by norm_num) ⟨17955, by rfl⟩ (by norm_num))
theorem R47885 : Reach 47885 := rs (se 3 (by rfl) ⟨8978, by rfl⟩) (B 17957 (by norm_num) ⟨8978, by rfl⟩ (by norm_num))
theorem R47889 : Reach 47889 := rs (se 2 (by rfl) ⟨17958, by rfl⟩) (B 35917 (by norm_num) ⟨17958, by rfl⟩ (by norm_num))
theorem R47893 : Reach 47893 := rs (se 6 (by rfl) ⟨1122, by rfl⟩) (B 2245 (by norm_num) ⟨1122, by rfl⟩ (by norm_num))
theorem R47897 : Reach 47897 := rs (se 2 (by rfl) ⟨17961, by rfl⟩) (B 35923 (by norm_num) ⟨17961, by rfl⟩ (by norm_num))
theorem R80669 : Reach 80669 := rs (se 3 (by rfl) ⟨15125, by rfl⟩) (B 30251 (by norm_num) ⟨15125, by rfl⟩ (by norm_num))
theorem R47901 : Reach 47901 := rs (se 3 (by rfl) ⟨8981, by rfl⟩) (B 17963 (by norm_num) ⟨8981, by rfl⟩ (by norm_num))
theorem R47905 : Reach 47905 := rs (se 2 (by rfl) ⟨17964, by rfl⟩) (B 35929 (by norm_num) ⟨17964, by rfl⟩ (by norm_num))
theorem R47909 : Reach 47909 := rs (se 4 (by rfl) ⟨4491, by rfl⟩) (B 8983 (by norm_num) ⟨4491, by rfl⟩ (by norm_num))
theorem R47913 : Reach 47913 := rs (se 2 (by rfl) ⟨17967, by rfl⟩) (B 35935 (by norm_num) ⟨17967, by rfl⟩ (by norm_num))
theorem R47917 : Reach 47917 := rs (se 3 (by rfl) ⟨8984, by rfl⟩) (B 17969 (by norm_num) ⟨8984, by rfl⟩ (by norm_num))
theorem R113453 : Reach 113453 := rs (se 3 (by rfl) ⟨21272, by rfl⟩) (B 42545 (by norm_num) ⟨21272, by rfl⟩ (by norm_num))
theorem R47921 : Reach 47921 := rs (se 2 (by rfl) ⟨17970, by rfl⟩) (B 35941 (by norm_num) ⟨17970, by rfl⟩ (by norm_num))
theorem R47925 : Reach 47925 := rs (se 5 (by rfl) ⟨2246, by rfl⟩) (B 4493 (by norm_num) ⟨2246, by rfl⟩ (by norm_num))
theorem R47929 : Reach 47929 := rs (se 2 (by rfl) ⟨17973, by rfl⟩) (B 35947 (by norm_num) ⟨17973, by rfl⟩ (by norm_num))
theorem R47933 : Reach 47933 := rs (se 3 (by rfl) ⟨8987, by rfl⟩) (B 17975 (by norm_num) ⟨8987, by rfl⟩ (by norm_num))
theorem R47937 : Reach 47937 := rs (se 2 (by rfl) ⟨17976, by rfl⟩) (B 35953 (by norm_num) ⟨17976, by rfl⟩ (by norm_num))
theorem R47941 : Reach 47941 := rs (se 4 (by rfl) ⟨4494, by rfl⟩) (B 8989 (by norm_num) ⟨4494, by rfl⟩ (by norm_num))
theorem R47945 : Reach 47945 := rs (se 2 (by rfl) ⟨17979, by rfl⟩) (B 35959 (by norm_num) ⟨17979, by rfl⟩ (by norm_num))
theorem R80717 : Reach 80717 := rs (se 3 (by rfl) ⟨15134, by rfl⟩) (B 30269 (by norm_num) ⟨15134, by rfl⟩ (by norm_num))
theorem R113485 : Reach 113485 := rs (se 3 (by rfl) ⟨21278, by rfl⟩) (B 42557 (by norm_num) ⟨21278, by rfl⟩ (by norm_num))
theorem R47949 : Reach 47949 := rs (se 3 (by rfl) ⟨8990, by rfl⟩) (B 17981 (by norm_num) ⟨8990, by rfl⟩ (by norm_num))
theorem R47953 : Reach 47953 := rs (se 2 (by rfl) ⟨17982, by rfl⟩) (B 35965 (by norm_num) ⟨17982, by rfl⟩ (by norm_num))
theorem R47957 : Reach 47957 := rs (se 9 (by rfl) ⟨140, by rfl⟩) (B 281 (by norm_num) ⟨140, by rfl⟩ (by norm_num))
theorem R47961 : Reach 47961 := rs (se 2 (by rfl) ⟨17985, by rfl⟩) (B 35971 (by norm_num) ⟨17985, by rfl⟩ (by norm_num))
theorem R47965 : Reach 47965 := rs (se 3 (by rfl) ⟨8993, by rfl⟩) (B 17987 (by norm_num) ⟨8993, by rfl⟩ (by norm_num))
theorem R47969 : Reach 47969 := rs (se 2 (by rfl) ⟨17988, by rfl⟩) (B 35977 (by norm_num) ⟨17988, by rfl⟩ (by norm_num))
theorem R47973 : Reach 47973 := rs (se 4 (by rfl) ⟨4497, by rfl⟩) (B 8995 (by norm_num) ⟨4497, by rfl⟩ (by norm_num))
theorem R47977 : Reach 47977 := rs (se 2 (by rfl) ⟨17991, by rfl⟩) (B 35983 (by norm_num) ⟨17991, by rfl⟩ (by norm_num))
theorem R47981 : Reach 47981 := rs (se 3 (by rfl) ⟨8996, by rfl⟩) (B 17993 (by norm_num) ⟨8996, by rfl⟩ (by norm_num))
theorem R47985 : Reach 47985 := rs (se 2 (by rfl) ⟨17994, by rfl⟩) (B 35989 (by norm_num) ⟨17994, by rfl⟩ (by norm_num))
theorem R47989 : Reach 47989 := rs (se 5 (by rfl) ⟨2249, by rfl⟩) (B 4499 (by norm_num) ⟨2249, by rfl⟩ (by norm_num))
theorem R113525 : Reach 113525 := rs (se 5 (by rfl) ⟨5321, by rfl⟩) (B 10643 (by norm_num) ⟨5321, by rfl⟩ (by norm_num))
theorem R47993 : Reach 47993 := rs (se 2 (by rfl) ⟨17997, by rfl⟩) (B 35995 (by norm_num) ⟨17997, by rfl⟩ (by norm_num))
theorem R47997 : Reach 47997 := rs (se 3 (by rfl) ⟨8999, by rfl⟩) (B 17999 (by norm_num) ⟨8999, by rfl⟩ (by norm_num))
theorem R48001 : Reach 48001 := rs (se 2 (by rfl) ⟨18000, by rfl⟩) (B 36001 (by norm_num) ⟨18000, by rfl⟩ (by norm_num))
theorem R48005 : Reach 48005 := rs (se 4 (by rfl) ⟨4500, by rfl⟩) (B 9001 (by norm_num) ⟨4500, by rfl⟩ (by norm_num))
theorem R48009 : Reach 48009 := rs (se 2 (by rfl) ⟨18003, by rfl⟩) (B 36007 (by norm_num) ⟨18003, by rfl⟩ (by norm_num))
theorem R48013 : Reach 48013 := rs (se 3 (by rfl) ⟨9002, by rfl⟩) (B 18005 (by norm_num) ⟨9002, by rfl⟩ (by norm_num))
theorem R48017 : Reach 48017 := rs (se 2 (by rfl) ⟨18006, by rfl⟩) (B 36013 (by norm_num) ⟨18006, by rfl⟩ (by norm_num))
theorem R48021 : Reach 48021 := rs (se 6 (by rfl) ⟨1125, by rfl⟩) (B 2251 (by norm_num) ⟨1125, by rfl⟩ (by norm_num))
theorem R48025 : Reach 48025 := rs (se 2 (by rfl) ⟨18009, by rfl⟩) (B 36019 (by norm_num) ⟨18009, by rfl⟩ (by norm_num))
theorem R80797 : Reach 80797 := rs (se 3 (by rfl) ⟨15149, by rfl⟩) (B 30299 (by norm_num) ⟨15149, by rfl⟩ (by norm_num))
theorem R48029 : Reach 48029 := rs (se 3 (by rfl) ⟨9005, by rfl⟩) (B 18011 (by norm_num) ⟨9005, by rfl⟩ (by norm_num))
theorem R48033 : Reach 48033 := rs (se 2 (by rfl) ⟨18012, by rfl⟩) (B 36025 (by norm_num) ⟨18012, by rfl⟩ (by norm_num))
theorem R48037 : Reach 48037 := rs (se 4 (by rfl) ⟨4503, by rfl⟩) (B 9007 (by norm_num) ⟨4503, by rfl⟩ (by norm_num))
theorem R48041 : Reach 48041 := rs (se 2 (by rfl) ⟨18015, by rfl⟩) (B 36031 (by norm_num) ⟨18015, by rfl⟩ (by norm_num))
theorem R48045 : Reach 48045 := rs (se 3 (by rfl) ⟨9008, by rfl⟩) (B 18017 (by norm_num) ⟨9008, by rfl⟩ (by norm_num))
theorem R48049 : Reach 48049 := rs (se 2 (by rfl) ⟨18018, by rfl⟩) (B 36037 (by norm_num) ⟨18018, by rfl⟩ (by norm_num))
theorem R48053 : Reach 48053 := rs (se 5 (by rfl) ⟨2252, by rfl⟩) (B 4505 (by norm_num) ⟨2252, by rfl⟩ (by norm_num))
theorem R48057 : Reach 48057 := rs (se 2 (by rfl) ⟨18021, by rfl⟩) (B 36043 (by norm_num) ⟨18021, by rfl⟩ (by norm_num))
theorem R48061 : Reach 48061 := rs (se 3 (by rfl) ⟨9011, by rfl⟩) (B 18023 (by norm_num) ⟨9011, by rfl⟩ (by norm_num))
theorem R113597 : Reach 113597 := rs (se 3 (by rfl) ⟨21299, by rfl⟩) (B 42599 (by norm_num) ⟨21299, by rfl⟩ (by norm_num))
theorem R48065 : Reach 48065 := rs (se 2 (by rfl) ⟨18024, by rfl⟩) (B 36049 (by norm_num) ⟨18024, by rfl⟩ (by norm_num))
theorem R48069 : Reach 48069 := rs (se 4 (by rfl) ⟨4506, by rfl⟩) (B 9013 (by norm_num) ⟨4506, by rfl⟩ (by norm_num))
theorem R48073 : Reach 48073 := rs (se 2 (by rfl) ⟨18027, by rfl⟩) (B 36055 (by norm_num) ⟨18027, by rfl⟩ (by norm_num))
theorem R48077 : Reach 48077 := rs (se 3 (by rfl) ⟨9014, by rfl⟩) (B 18029 (by norm_num) ⟨9014, by rfl⟩ (by norm_num))
theorem R48081 : Reach 48081 := rs (se 2 (by rfl) ⟨18030, by rfl⟩) (B 36061 (by norm_num) ⟨18030, by rfl⟩ (by norm_num))
theorem R48085 : Reach 48085 := rs (se 7 (by rfl) ⟨563, by rfl⟩) (B 1127 (by norm_num) ⟨563, by rfl⟩ (by norm_num))
theorem R48089 : Reach 48089 := rs (se 2 (by rfl) ⟨18033, by rfl⟩) (B 36067 (by norm_num) ⟨18033, by rfl⟩ (by norm_num))
theorem R48093 : Reach 48093 := rs (se 3 (by rfl) ⟨9017, by rfl⟩) (B 18035 (by norm_num) ⟨9017, by rfl⟩ (by norm_num))
theorem R48097 : Reach 48097 := rs (se 2 (by rfl) ⟨18036, by rfl⟩) (B 36073 (by norm_num) ⟨18036, by rfl⟩ (by norm_num))
theorem R48101 : Reach 48101 := rs (se 4 (by rfl) ⟨4509, by rfl⟩) (B 9019 (by norm_num) ⟨4509, by rfl⟩ (by norm_num))
theorem R48105 : Reach 48105 := rs (se 2 (by rfl) ⟨18039, by rfl⟩) (B 36079 (by norm_num) ⟨18039, by rfl⟩ (by norm_num))
theorem R48109 : Reach 48109 := rs (se 3 (by rfl) ⟨9020, by rfl⟩) (B 18041 (by norm_num) ⟨9020, by rfl⟩ (by norm_num))
theorem R48113 : Reach 48113 := rs (se 2 (by rfl) ⟨18042, by rfl⟩) (B 36085 (by norm_num) ⟨18042, by rfl⟩ (by norm_num))
theorem R80885 : Reach 80885 := rs (se 5 (by rfl) ⟨3791, by rfl⟩) (B 7583 (by norm_num) ⟨3791, by rfl⟩ (by norm_num))
theorem R48117 : Reach 48117 := rs (se 5 (by rfl) ⟨2255, by rfl⟩) (B 4511 (by norm_num) ⟨2255, by rfl⟩ (by norm_num))
theorem R48121 : Reach 48121 := rs (se 2 (by rfl) ⟨18045, by rfl⟩) (B 36091 (by norm_num) ⟨18045, by rfl⟩ (by norm_num))
theorem R48125 : Reach 48125 := rs (se 3 (by rfl) ⟨9023, by rfl⟩) (B 18047 (by norm_num) ⟨9023, by rfl⟩ (by norm_num))
theorem R48129 : Reach 48129 := rs (se 2 (by rfl) ⟨18048, by rfl⟩) (B 36097 (by norm_num) ⟨18048, by rfl⟩ (by norm_num))
theorem R48133 : Reach 48133 := rs (se 4 (by rfl) ⟨4512, by rfl⟩) (B 9025 (by norm_num) ⟨4512, by rfl⟩ (by norm_num))
theorem R113669 : Reach 113669 := rs (se 4 (by rfl) ⟨10656, by rfl⟩) (B 21313 (by norm_num) ⟨10656, by rfl⟩ (by norm_num))
theorem R48137 : Reach 48137 := rs (se 2 (by rfl) ⟨18051, by rfl⟩) (B 36103 (by norm_num) ⟨18051, by rfl⟩ (by norm_num))
theorem R48141 : Reach 48141 := rs (se 3 (by rfl) ⟨9026, by rfl⟩) (B 18053 (by norm_num) ⟨9026, by rfl⟩ (by norm_num))
theorem R48145 : Reach 48145 := rs (se 2 (by rfl) ⟨18054, by rfl⟩) (B 36109 (by norm_num) ⟨18054, by rfl⟩ (by norm_num))
theorem R48149 : Reach 48149 := rs (se 6 (by rfl) ⟨1128, by rfl⟩) (B 2257 (by norm_num) ⟨1128, by rfl⟩ (by norm_num))
theorem R48153 : Reach 48153 := rs (se 2 (by rfl) ⟨18057, by rfl⟩) (B 36115 (by norm_num) ⟨18057, by rfl⟩ (by norm_num))
theorem R48157 : Reach 48157 := rs (se 3 (by rfl) ⟨9029, by rfl⟩) (B 18059 (by norm_num) ⟨9029, by rfl⟩ (by norm_num))
theorem R48161 : Reach 48161 := rs (se 2 (by rfl) ⟨18060, by rfl⟩) (B 36121 (by norm_num) ⟨18060, by rfl⟩ (by norm_num))
theorem R48165 : Reach 48165 := rs (se 4 (by rfl) ⟨4515, by rfl⟩) (B 9031 (by norm_num) ⟨4515, by rfl⟩ (by norm_num))
theorem R48169 : Reach 48169 := rs (se 2 (by rfl) ⟨18063, by rfl⟩) (B 36127 (by norm_num) ⟨18063, by rfl⟩ (by norm_num))
theorem R48173 : Reach 48173 := rs (se 3 (by rfl) ⟨9032, by rfl⟩) (B 18065 (by norm_num) ⟨9032, by rfl⟩ (by norm_num))
theorem R48177 : Reach 48177 := rs (se 2 (by rfl) ⟨18066, by rfl⟩) (B 36133 (by norm_num) ⟨18066, by rfl⟩ (by norm_num))
theorem R113717 : Reach 113717 := rs (se 5 (by rfl) ⟨5330, by rfl⟩) (B 10661 (by norm_num) ⟨5330, by rfl⟩ (by norm_num))
theorem R48181 : Reach 48181 := rs (se 5 (by rfl) ⟨2258, by rfl⟩) (B 4517 (by norm_num) ⟨2258, by rfl⟩ (by norm_num))
theorem R48185 : Reach 48185 := rs (se 2 (by rfl) ⟨18069, by rfl⟩) (B 36139 (by norm_num) ⟨18069, by rfl⟩ (by norm_num))
theorem R48189 : Reach 48189 := rs (se 3 (by rfl) ⟨9035, by rfl⟩) (B 18071 (by norm_num) ⟨9035, by rfl⟩ (by norm_num))
theorem R48193 : Reach 48193 := rs (se 2 (by rfl) ⟨18072, by rfl⟩) (B 36145 (by norm_num) ⟨18072, by rfl⟩ (by norm_num))
theorem R48197 : Reach 48197 := rs (se 4 (by rfl) ⟨4518, by rfl⟩) (B 9037 (by norm_num) ⟨4518, by rfl⟩ (by norm_num))
theorem R48201 : Reach 48201 := rs (se 2 (by rfl) ⟨18075, by rfl⟩) (B 36151 (by norm_num) ⟨18075, by rfl⟩ (by norm_num))
theorem R48205 : Reach 48205 := rs (se 3 (by rfl) ⟨9038, by rfl⟩) (B 18077 (by norm_num) ⟨9038, by rfl⟩ (by norm_num))
theorem R113741 : Reach 113741 := rs (se 3 (by rfl) ⟨21326, by rfl⟩) (B 42653 (by norm_num) ⟨21326, by rfl⟩ (by norm_num))
theorem R48209 : Reach 48209 := rs (se 2 (by rfl) ⟨18078, by rfl⟩) (B 36157 (by norm_num) ⟨18078, by rfl⟩ (by norm_num))
theorem R48213 : Reach 48213 := rs (se 8 (by rfl) ⟨282, by rfl⟩) (B 565 (by norm_num) ⟨282, by rfl⟩ (by norm_num))
theorem R48217 : Reach 48217 := rs (se 2 (by rfl) ⟨18081, by rfl⟩) (B 36163 (by norm_num) ⟨18081, by rfl⟩ (by norm_num))
theorem R48221 : Reach 48221 := rs (se 3 (by rfl) ⟨9041, by rfl⟩) (B 18083 (by norm_num) ⟨9041, by rfl⟩ (by norm_num))
theorem R48225 : Reach 48225 := rs (se 2 (by rfl) ⟨18084, by rfl⟩) (B 36169 (by norm_num) ⟨18084, by rfl⟩ (by norm_num))
theorem R48229 : Reach 48229 := rs (se 4 (by rfl) ⟨4521, by rfl⟩) (B 9043 (by norm_num) ⟨4521, by rfl⟩ (by norm_num))
theorem R48233 : Reach 48233 := rs (se 2 (by rfl) ⟨18087, by rfl⟩) (B 36175 (by norm_num) ⟨18087, by rfl⟩ (by norm_num))
theorem R48237 : Reach 48237 := rs (se 3 (by rfl) ⟨9044, by rfl⟩) (B 18089 (by norm_num) ⟨9044, by rfl⟩ (by norm_num))
theorem R48241 : Reach 48241 := rs (se 2 (by rfl) ⟨18090, by rfl⟩) (B 36181 (by norm_num) ⟨18090, by rfl⟩ (by norm_num))
theorem R81013 : Reach 81013 := rs (se 5 (by rfl) ⟨3797, by rfl⟩) (B 7595 (by norm_num) ⟨3797, by rfl⟩ (by norm_num))
theorem R48245 : Reach 48245 := rs (se 5 (by rfl) ⟨2261, by rfl⟩) (B 4523 (by norm_num) ⟨2261, by rfl⟩ (by norm_num))
theorem R48249 : Reach 48249 := rs (se 2 (by rfl) ⟨18093, by rfl⟩) (B 36187 (by norm_num) ⟨18093, by rfl⟩ (by norm_num))
theorem R48253 : Reach 48253 := rs (se 3 (by rfl) ⟨9047, by rfl⟩) (B 18095 (by norm_num) ⟨9047, by rfl⟩ (by norm_num))
theorem R48257 : Reach 48257 := rs (se 2 (by rfl) ⟨18096, by rfl⟩) (B 36193 (by norm_num) ⟨18096, by rfl⟩ (by norm_num))
theorem R48261 : Reach 48261 := rs (se 4 (by rfl) ⟨4524, by rfl⟩) (B 9049 (by norm_num) ⟨4524, by rfl⟩ (by norm_num))
theorem R48265 : Reach 48265 := rs (se 2 (by rfl) ⟨18099, by rfl⟩) (B 36199 (by norm_num) ⟨18099, by rfl⟩ (by norm_num))
theorem R48269 : Reach 48269 := rs (se 3 (by rfl) ⟨9050, by rfl⟩) (B 18101 (by norm_num) ⟨9050, by rfl⟩ (by norm_num))
theorem R48273 : Reach 48273 := rs (se 2 (by rfl) ⟨18102, by rfl⟩) (B 36205 (by norm_num) ⟨18102, by rfl⟩ (by norm_num))
theorem R48277 : Reach 48277 := rs (se 6 (by rfl) ⟨1131, by rfl⟩) (B 2263 (by norm_num) ⟨1131, by rfl⟩ (by norm_num))
theorem R113813 : Reach 113813 := rs (se 6 (by rfl) ⟨2667, by rfl⟩) (B 5335 (by norm_num) ⟨2667, by rfl⟩ (by norm_num))
theorem R48281 : Reach 48281 := rs (se 2 (by rfl) ⟨18105, by rfl⟩) (B 36211 (by norm_num) ⟨18105, by rfl⟩ (by norm_num))
theorem R48285 : Reach 48285 := rs (se 3 (by rfl) ⟨9053, by rfl⟩) (B 18107 (by norm_num) ⟨9053, by rfl⟩ (by norm_num))
theorem R48289 : Reach 48289 := rs (se 2 (by rfl) ⟨18108, by rfl⟩) (B 36217 (by norm_num) ⟨18108, by rfl⟩ (by norm_num))
theorem R48293 : Reach 48293 := rs (se 4 (by rfl) ⟨4527, by rfl⟩) (B 9055 (by norm_num) ⟨4527, by rfl⟩ (by norm_num))
theorem R48297 : Reach 48297 := rs (se 2 (by rfl) ⟨18111, by rfl⟩) (B 36223 (by norm_num) ⟨18111, by rfl⟩ (by norm_num))
theorem R48301 : Reach 48301 := rs (se 3 (by rfl) ⟨9056, by rfl⟩) (B 18113 (by norm_num) ⟨9056, by rfl⟩ (by norm_num))
theorem R48305 : Reach 48305 := rs (se 2 (by rfl) ⟨18114, by rfl⟩) (B 36229 (by norm_num) ⟨18114, by rfl⟩ (by norm_num))
theorem R48309 : Reach 48309 := rs (se 5 (by rfl) ⟨2264, by rfl⟩) (B 4529 (by norm_num) ⟨2264, by rfl⟩ (by norm_num))
theorem R48313 : Reach 48313 := rs (se 2 (by rfl) ⟨18117, by rfl⟩) (B 36235 (by norm_num) ⟨18117, by rfl⟩ (by norm_num))
theorem R48317 : Reach 48317 := rs (se 3 (by rfl) ⟨9059, by rfl⟩) (B 18119 (by norm_num) ⟨9059, by rfl⟩ (by norm_num))
theorem R48321 : Reach 48321 := rs (se 2 (by rfl) ⟨18120, by rfl⟩) (B 36241 (by norm_num) ⟨18120, by rfl⟩ (by norm_num))
theorem R113861 : Reach 113861 := rs (se 4 (by rfl) ⟨10674, by rfl⟩) (B 21349 (by norm_num) ⟨10674, by rfl⟩ (by norm_num))
theorem R48325 : Reach 48325 := rs (se 4 (by rfl) ⟨4530, by rfl⟩) (B 9061 (by norm_num) ⟨4530, by rfl⟩ (by norm_num))
theorem R48329 : Reach 48329 := rs (se 2 (by rfl) ⟨18123, by rfl⟩) (B 36247 (by norm_num) ⟨18123, by rfl⟩ (by norm_num))
theorem R81101 : Reach 81101 := rs (se 3 (by rfl) ⟨15206, by rfl⟩) (B 30413 (by norm_num) ⟨15206, by rfl⟩ (by norm_num))
theorem R48333 : Reach 48333 := rs (se 3 (by rfl) ⟨9062, by rfl⟩) (B 18125 (by norm_num) ⟨9062, by rfl⟩ (by norm_num))
theorem R48337 : Reach 48337 := rs (se 2 (by rfl) ⟨18126, by rfl⟩) (B 36253 (by norm_num) ⟨18126, by rfl⟩ (by norm_num))
theorem R48341 : Reach 48341 := rs (se 7 (by rfl) ⟨566, by rfl⟩) (B 1133 (by norm_num) ⟨566, by rfl⟩ (by norm_num))
theorem R48345 : Reach 48345 := rs (se 2 (by rfl) ⟨18129, by rfl⟩) (B 36259 (by norm_num) ⟨18129, by rfl⟩ (by norm_num))
theorem R48349 : Reach 48349 := rs (se 3 (by rfl) ⟨9065, by rfl⟩) (B 18131 (by norm_num) ⟨9065, by rfl⟩ (by norm_num))
theorem R113885 : Reach 113885 := rs (se 3 (by rfl) ⟨21353, by rfl⟩) (B 42707 (by norm_num) ⟨21353, by rfl⟩ (by norm_num))
theorem R48353 : Reach 48353 := rs (se 2 (by rfl) ⟨18132, by rfl⟩) (B 36265 (by norm_num) ⟨18132, by rfl⟩ (by norm_num))
theorem R48357 : Reach 48357 := rs (se 4 (by rfl) ⟨4533, by rfl⟩) (B 9067 (by norm_num) ⟨4533, by rfl⟩ (by norm_num))
theorem R48361 : Reach 48361 := rs (se 2 (by rfl) ⟨18135, by rfl⟩) (B 36271 (by norm_num) ⟨18135, by rfl⟩ (by norm_num))
theorem R48365 : Reach 48365 := rs (se 3 (by rfl) ⟨9068, by rfl⟩) (B 18137 (by norm_num) ⟨9068, by rfl⟩ (by norm_num))
theorem R48369 : Reach 48369 := rs (se 2 (by rfl) ⟨18138, by rfl⟩) (B 36277 (by norm_num) ⟨18138, by rfl⟩ (by norm_num))
theorem R48373 : Reach 48373 := rs (se 5 (by rfl) ⟨2267, by rfl⟩) (B 4535 (by norm_num) ⟨2267, by rfl⟩ (by norm_num))
theorem R48377 : Reach 48377 := rs (se 2 (by rfl) ⟨18141, by rfl⟩) (B 36283 (by norm_num) ⟨18141, by rfl⟩ (by norm_num))
theorem R48381 : Reach 48381 := rs (se 3 (by rfl) ⟨9071, by rfl⟩) (B 18143 (by norm_num) ⟨9071, by rfl⟩ (by norm_num))
theorem R48385 : Reach 48385 := rs (se 2 (by rfl) ⟨18144, by rfl⟩) (B 36289 (by norm_num) ⟨18144, by rfl⟩ (by norm_num))
theorem R48389 : Reach 48389 := rs (se 4 (by rfl) ⟨4536, by rfl⟩) (B 9073 (by norm_num) ⟨4536, by rfl⟩ (by norm_num))
theorem R48393 : Reach 48393 := rs (se 2 (by rfl) ⟨18147, by rfl⟩) (B 36295 (by norm_num) ⟨18147, by rfl⟩ (by norm_num))
theorem R48397 : Reach 48397 := rs (se 3 (by rfl) ⟨9074, by rfl⟩) (B 18149 (by norm_num) ⟨9074, by rfl⟩ (by norm_num))
theorem R48401 : Reach 48401 := rs (se 2 (by rfl) ⟨18150, by rfl⟩) (B 36301 (by norm_num) ⟨18150, by rfl⟩ (by norm_num))
theorem R48405 : Reach 48405 := rs (se 6 (by rfl) ⟨1134, by rfl⟩) (B 2269 (by norm_num) ⟨1134, by rfl⟩ (by norm_num))
theorem R48409 : Reach 48409 := rs (se 2 (by rfl) ⟨18153, by rfl⟩) (B 36307 (by norm_num) ⟨18153, by rfl⟩ (by norm_num))
theorem R48413 : Reach 48413 := rs (se 3 (by rfl) ⟨9077, by rfl⟩) (B 18155 (by norm_num) ⟨9077, by rfl⟩ (by norm_num))
theorem R48417 : Reach 48417 := rs (se 2 (by rfl) ⟨18156, by rfl⟩) (B 36313 (by norm_num) ⟨18156, by rfl⟩ (by norm_num))
theorem R48421 : Reach 48421 := rs (se 4 (by rfl) ⟨4539, by rfl⟩) (B 9079 (by norm_num) ⟨4539, by rfl⟩ (by norm_num))
theorem R113957 : Reach 113957 := rs (se 4 (by rfl) ⟨10683, by rfl⟩) (B 21367 (by norm_num) ⟨10683, by rfl⟩ (by norm_num))
theorem R48425 : Reach 48425 := rs (se 2 (by rfl) ⟨18159, by rfl⟩) (B 36319 (by norm_num) ⟨18159, by rfl⟩ (by norm_num))
theorem R48429 : Reach 48429 := rs (se 3 (by rfl) ⟨9080, by rfl⟩) (B 18161 (by norm_num) ⟨9080, by rfl⟩ (by norm_num))
theorem R48433 : Reach 48433 := rs (se 2 (by rfl) ⟨18162, by rfl⟩) (B 36325 (by norm_num) ⟨18162, by rfl⟩ (by norm_num))
theorem R48437 : Reach 48437 := rs (se 5 (by rfl) ⟨2270, by rfl⟩) (B 4541 (by norm_num) ⟨2270, by rfl⟩ (by norm_num))
theorem R48441 : Reach 48441 := rs (se 2 (by rfl) ⟨18165, by rfl⟩) (B 36331 (by norm_num) ⟨18165, by rfl⟩ (by norm_num))
theorem R48445 : Reach 48445 := rs (se 3 (by rfl) ⟨9083, by rfl⟩) (B 18167 (by norm_num) ⟨9083, by rfl⟩ (by norm_num))
theorem R48449 : Reach 48449 := rs (se 2 (by rfl) ⟨18168, by rfl⟩) (B 36337 (by norm_num) ⟨18168, by rfl⟩ (by norm_num))
theorem R48453 : Reach 48453 := rs (se 4 (by rfl) ⟨4542, by rfl⟩) (B 9085 (by norm_num) ⟨4542, by rfl⟩ (by norm_num))
theorem R48457 : Reach 48457 := rs (se 2 (by rfl) ⟨18171, by rfl⟩) (B 36343 (by norm_num) ⟨18171, by rfl⟩ (by norm_num))
theorem R81229 : Reach 81229 := rs (se 3 (by rfl) ⟨15230, by rfl⟩) (B 30461 (by norm_num) ⟨15230, by rfl⟩ (by norm_num))
theorem R48461 : Reach 48461 := rs (se 3 (by rfl) ⟨9086, by rfl⟩) (B 18173 (by norm_num) ⟨9086, by rfl⟩ (by norm_num))
theorem R48465 : Reach 48465 := rs (se 2 (by rfl) ⟨18174, by rfl⟩) (B 36349 (by norm_num) ⟨18174, by rfl⟩ (by norm_num))
theorem R48469 : Reach 48469 := rs (se 11 (by rfl) ⟨35, by rfl⟩) (B 71 (by norm_num) ⟨35, by rfl⟩ (by norm_num))
theorem R48473 : Reach 48473 := rs (se 2 (by rfl) ⟨18177, by rfl⟩) (B 36355 (by norm_num) ⟨18177, by rfl⟩ (by norm_num))
theorem R48477 : Reach 48477 := rs (se 3 (by rfl) ⟨9089, by rfl⟩) (B 18179 (by norm_num) ⟨9089, by rfl⟩ (by norm_num))
theorem R48481 : Reach 48481 := rs (se 2 (by rfl) ⟨18180, by rfl⟩) (B 36361 (by norm_num) ⟨18180, by rfl⟩ (by norm_num))
theorem R48485 : Reach 48485 := rs (se 4 (by rfl) ⟨4545, by rfl⟩) (B 9091 (by norm_num) ⟨4545, by rfl⟩ (by norm_num))
theorem R48489 : Reach 48489 := rs (se 2 (by rfl) ⟨18183, by rfl⟩) (B 36367 (by norm_num) ⟨18183, by rfl⟩ (by norm_num))
theorem R48493 : Reach 48493 := rs (se 3 (by rfl) ⟨9092, by rfl⟩) (B 18185 (by norm_num) ⟨9092, by rfl⟩ (by norm_num))
theorem R114029 : Reach 114029 := rs (se 3 (by rfl) ⟨21380, by rfl⟩) (B 42761 (by norm_num) ⟨21380, by rfl⟩ (by norm_num))
theorem R48497 : Reach 48497 := rs (se 2 (by rfl) ⟨18186, by rfl⟩) (B 36373 (by norm_num) ⟨18186, by rfl⟩ (by norm_num))
theorem R48501 : Reach 48501 := rs (se 5 (by rfl) ⟨2273, by rfl⟩) (B 4547 (by norm_num) ⟨2273, by rfl⟩ (by norm_num))
theorem R48505 : Reach 48505 := rs (se 2 (by rfl) ⟨18189, by rfl⟩) (B 36379 (by norm_num) ⟨18189, by rfl⟩ (by norm_num))
theorem R48509 : Reach 48509 := rs (se 3 (by rfl) ⟨9095, by rfl⟩) (B 18191 (by norm_num) ⟨9095, by rfl⟩ (by norm_num))
theorem R48513 : Reach 48513 := rs (se 2 (by rfl) ⟨18192, by rfl⟩) (B 36385 (by norm_num) ⟨18192, by rfl⟩ (by norm_num))
theorem R48517 : Reach 48517 := rs (se 4 (by rfl) ⟨4548, by rfl⟩) (B 9097 (by norm_num) ⟨4548, by rfl⟩ (by norm_num))
theorem R48521 : Reach 48521 := rs (se 2 (by rfl) ⟨18195, by rfl⟩) (B 36391 (by norm_num) ⟨18195, by rfl⟩ (by norm_num))
theorem R48525 : Reach 48525 := rs (se 3 (by rfl) ⟨9098, by rfl⟩) (B 18197 (by norm_num) ⟨9098, by rfl⟩ (by norm_num))
theorem R48529 : Reach 48529 := rs (se 2 (by rfl) ⟨18198, by rfl⟩) (B 36397 (by norm_num) ⟨18198, by rfl⟩ (by norm_num))
theorem R48533 : Reach 48533 := rs (se 6 (by rfl) ⟨1137, by rfl⟩) (B 2275 (by norm_num) ⟨1137, by rfl⟩ (by norm_num))
theorem R540053 : Reach 540053 := rs (se 6 (by rfl) ⟨12657, by rfl⟩) (B 25315 (by norm_num) ⟨12657, by rfl⟩ (by norm_num))
theorem R48537 : Reach 48537 := rs (se 2 (by rfl) ⟨18201, by rfl⟩) (B 36403 (by norm_num) ⟨18201, by rfl⟩ (by norm_num))
theorem R48541 : Reach 48541 := rs (se 3 (by rfl) ⟨9101, by rfl⟩) (B 18203 (by norm_num) ⟨9101, by rfl⟩ (by norm_num))
theorem R48545 : Reach 48545 := rs (se 2 (by rfl) ⟨18204, by rfl⟩) (B 36409 (by norm_num) ⟨18204, by rfl⟩ (by norm_num))
theorem R81317 : Reach 81317 := rs (se 4 (by rfl) ⟨7623, by rfl⟩) (B 15247 (by norm_num) ⟨7623, by rfl⟩ (by norm_num))
theorem R48549 : Reach 48549 := rs (se 4 (by rfl) ⟨4551, by rfl⟩) (B 9103 (by norm_num) ⟨4551, by rfl⟩ (by norm_num))
theorem R48553 : Reach 48553 := rs (se 2 (by rfl) ⟨18207, by rfl⟩) (B 36415 (by norm_num) ⟨18207, by rfl⟩ (by norm_num))
theorem R48557 : Reach 48557 := rs (se 3 (by rfl) ⟨9104, by rfl⟩) (B 18209 (by norm_num) ⟨9104, by rfl⟩ (by norm_num))
theorem R48561 : Reach 48561 := rs (se 2 (by rfl) ⟨18210, by rfl⟩) (B 36421 (by norm_num) ⟨18210, by rfl⟩ (by norm_num))
theorem R114101 : Reach 114101 := rs (se 5 (by rfl) ⟨5348, by rfl⟩) (B 10697 (by norm_num) ⟨5348, by rfl⟩ (by norm_num))
theorem R48565 : Reach 48565 := rs (se 5 (by rfl) ⟨2276, by rfl⟩) (B 4553 (by norm_num) ⟨2276, by rfl⟩ (by norm_num))
theorem R48569 : Reach 48569 := rs (se 2 (by rfl) ⟨18213, by rfl⟩) (B 36427 (by norm_num) ⟨18213, by rfl⟩ (by norm_num))
theorem R48573 : Reach 48573 := rs (se 3 (by rfl) ⟨9107, by rfl⟩) (B 18215 (by norm_num) ⟨9107, by rfl⟩ (by norm_num))
theorem R81341 : Reach 81341 := rs (se 3 (by rfl) ⟨15251, by rfl⟩) (B 30503 (by norm_num) ⟨15251, by rfl⟩ (by norm_num))
theorem R48577 : Reach 48577 := rs (se 2 (by rfl) ⟨18216, by rfl⟩) (B 36433 (by norm_num) ⟨18216, by rfl⟩ (by norm_num))
theorem R48581 : Reach 48581 := rs (se 4 (by rfl) ⟨4554, by rfl⟩) (B 9109 (by norm_num) ⟨4554, by rfl⟩ (by norm_num))
theorem R48585 : Reach 48585 := rs (se 2 (by rfl) ⟨18219, by rfl⟩) (B 36439 (by norm_num) ⟨18219, by rfl⟩ (by norm_num))
theorem R48589 : Reach 48589 := rs (se 3 (by rfl) ⟨9110, by rfl⟩) (B 18221 (by norm_num) ⟨9110, by rfl⟩ (by norm_num))
theorem R48593 : Reach 48593 := rs (se 2 (by rfl) ⟨18222, by rfl⟩) (B 36445 (by norm_num) ⟨18222, by rfl⟩ (by norm_num))
theorem R48597 : Reach 48597 := rs (se 7 (by rfl) ⟨569, by rfl⟩) (B 1139 (by norm_num) ⟨569, by rfl⟩ (by norm_num))
theorem R48601 : Reach 48601 := rs (se 2 (by rfl) ⟨18225, by rfl⟩) (B 36451 (by norm_num) ⟨18225, by rfl⟩ (by norm_num))
theorem R48605 : Reach 48605 := rs (se 3 (by rfl) ⟨9113, by rfl⟩) (B 18227 (by norm_num) ⟨9113, by rfl⟩ (by norm_num))
theorem R48609 : Reach 48609 := rs (se 2 (by rfl) ⟨18228, by rfl⟩) (B 36457 (by norm_num) ⟨18228, by rfl⟩ (by norm_num))
theorem R48613 : Reach 48613 := rs (se 4 (by rfl) ⟨4557, by rfl⟩) (B 9115 (by norm_num) ⟨4557, by rfl⟩ (by norm_num))
theorem R48617 : Reach 48617 := rs (se 2 (by rfl) ⟨18231, by rfl⟩) (B 36463 (by norm_num) ⟨18231, by rfl⟩ (by norm_num))
theorem R48621 : Reach 48621 := rs (se 3 (by rfl) ⟨9116, by rfl⟩) (B 18233 (by norm_num) ⟨9116, by rfl⟩ (by norm_num))
theorem R48625 : Reach 48625 := rs (se 2 (by rfl) ⟨18234, by rfl⟩) (B 36469 (by norm_num) ⟨18234, by rfl⟩ (by norm_num))
theorem R48629 : Reach 48629 := rs (se 5 (by rfl) ⟨2279, by rfl⟩) (B 4559 (by norm_num) ⟨2279, by rfl⟩ (by norm_num))
theorem R48633 : Reach 48633 := rs (se 2 (by rfl) ⟨18237, by rfl⟩) (B 36475 (by norm_num) ⟨18237, by rfl⟩ (by norm_num))
theorem R48637 : Reach 48637 := rs (se 3 (by rfl) ⟨9119, by rfl⟩) (B 18239 (by norm_num) ⟨9119, by rfl⟩ (by norm_num))
theorem R114173 : Reach 114173 := rs (se 3 (by rfl) ⟨21407, by rfl⟩) (B 42815 (by norm_num) ⟨21407, by rfl⟩ (by norm_num))
theorem R48641 : Reach 48641 := rs (se 2 (by rfl) ⟨18240, by rfl⟩) (B 36481 (by norm_num) ⟨18240, by rfl⟩ (by norm_num))
theorem R48645 : Reach 48645 := rs (se 4 (by rfl) ⟨4560, by rfl⟩) (B 9121 (by norm_num) ⟨4560, by rfl⟩ (by norm_num))
theorem R48649 : Reach 48649 := rs (se 2 (by rfl) ⟨18243, by rfl⟩) (B 36487 (by norm_num) ⟨18243, by rfl⟩ (by norm_num))
theorem R48653 : Reach 48653 := rs (se 3 (by rfl) ⟨9122, by rfl⟩) (B 18245 (by norm_num) ⟨9122, by rfl⟩ (by norm_num))
theorem R48657 : Reach 48657 := rs (se 2 (by rfl) ⟨18246, by rfl⟩) (B 36493 (by norm_num) ⟨18246, by rfl⟩ (by norm_num))
theorem R48661 : Reach 48661 := rs (se 6 (by rfl) ⟨1140, by rfl⟩) (B 2281 (by norm_num) ⟨1140, by rfl⟩ (by norm_num))
theorem R48665 : Reach 48665 := rs (se 2 (by rfl) ⟨18249, by rfl⟩) (B 36499 (by norm_num) ⟨18249, by rfl⟩ (by norm_num))
theorem R48669 : Reach 48669 := rs (se 3 (by rfl) ⟨9125, by rfl⟩) (B 18251 (by norm_num) ⟨9125, by rfl⟩ (by norm_num))
theorem R48673 : Reach 48673 := rs (se 2 (by rfl) ⟨18252, by rfl⟩) (B 36505 (by norm_num) ⟨18252, by rfl⟩ (by norm_num))
theorem R81445 : Reach 81445 := rs (se 4 (by rfl) ⟨7635, by rfl⟩) (B 15271 (by norm_num) ⟨7635, by rfl⟩ (by norm_num))
theorem R48677 : Reach 48677 := rs (se 4 (by rfl) ⟨4563, by rfl⟩) (B 9127 (by norm_num) ⟨4563, by rfl⟩ (by norm_num))
theorem R48681 : Reach 48681 := rs (se 2 (by rfl) ⟨18255, by rfl⟩) (B 36511 (by norm_num) ⟨18255, by rfl⟩ (by norm_num))
theorem R48685 : Reach 48685 := rs (se 3 (by rfl) ⟨9128, by rfl⟩) (B 18257 (by norm_num) ⟨9128, by rfl⟩ (by norm_num))
theorem R48689 : Reach 48689 := rs (se 2 (by rfl) ⟨18258, by rfl⟩) (B 36517 (by norm_num) ⟨18258, by rfl⟩ (by norm_num))
theorem R48693 : Reach 48693 := rs (se 5 (by rfl) ⟨2282, by rfl⟩) (B 4565 (by norm_num) ⟨2282, by rfl⟩ (by norm_num))
theorem R48697 : Reach 48697 := rs (se 2 (by rfl) ⟨18261, by rfl⟩) (B 36523 (by norm_num) ⟨18261, by rfl⟩ (by norm_num))
theorem R48701 : Reach 48701 := rs (se 3 (by rfl) ⟨9131, by rfl⟩) (B 18263 (by norm_num) ⟨9131, by rfl⟩ (by norm_num))
theorem R48705 : Reach 48705 := rs (se 2 (by rfl) ⟨18264, by rfl⟩) (B 36529 (by norm_num) ⟨18264, by rfl⟩ (by norm_num))
theorem R48709 : Reach 48709 := rs (se 4 (by rfl) ⟨4566, by rfl⟩) (B 9133 (by norm_num) ⟨4566, by rfl⟩ (by norm_num))
theorem R114245 : Reach 114245 := rs (se 4 (by rfl) ⟨10710, by rfl⟩) (B 21421 (by norm_num) ⟨10710, by rfl⟩ (by norm_num))
theorem R48713 : Reach 48713 := rs (se 2 (by rfl) ⟨18267, by rfl⟩) (B 36535 (by norm_num) ⟨18267, by rfl⟩ (by norm_num))
theorem R48717 : Reach 48717 := rs (se 3 (by rfl) ⟨9134, by rfl⟩) (B 18269 (by norm_num) ⟨9134, by rfl⟩ (by norm_num))
theorem R48721 : Reach 48721 := rs (se 2 (by rfl) ⟨18270, by rfl⟩) (B 36541 (by norm_num) ⟨18270, by rfl⟩ (by norm_num))
theorem R48725 : Reach 48725 := rs (se 8 (by rfl) ⟨285, by rfl⟩) (B 571 (by norm_num) ⟨285, by rfl⟩ (by norm_num))
theorem R48729 : Reach 48729 := rs (se 2 (by rfl) ⟨18273, by rfl⟩) (B 36547 (by norm_num) ⟨18273, by rfl⟩ (by norm_num))
theorem R48733 : Reach 48733 := rs (se 3 (by rfl) ⟨9137, by rfl⟩) (B 18275 (by norm_num) ⟨9137, by rfl⟩ (by norm_num))
theorem R48737 : Reach 48737 := rs (se 2 (by rfl) ⟨18276, by rfl⟩) (B 36553 (by norm_num) ⟨18276, by rfl⟩ (by norm_num))
theorem R48741 : Reach 48741 := rs (se 4 (by rfl) ⟨4569, by rfl⟩) (B 9139 (by norm_num) ⟨4569, by rfl⟩ (by norm_num))
theorem R48745 : Reach 48745 := rs (se 2 (by rfl) ⟨18279, by rfl⟩) (B 36559 (by norm_num) ⟨18279, by rfl⟩ (by norm_num))
theorem R48749 : Reach 48749 := rs (se 3 (by rfl) ⟨9140, by rfl⟩) (B 18281 (by norm_num) ⟨9140, by rfl⟩ (by norm_num))
theorem R48753 : Reach 48753 := rs (se 2 (by rfl) ⟨18282, by rfl⟩) (B 36565 (by norm_num) ⟨18282, by rfl⟩ (by norm_num))
theorem R48757 : Reach 48757 := rs (se 5 (by rfl) ⟨2285, by rfl⟩) (B 4571 (by norm_num) ⟨2285, by rfl⟩ (by norm_num))
theorem R48761 : Reach 48761 := rs (se 2 (by rfl) ⟨18285, by rfl⟩) (B 36571 (by norm_num) ⟨18285, by rfl⟩ (by norm_num))
theorem R81533 : Reach 81533 := rs (se 3 (by rfl) ⟨15287, by rfl⟩) (B 30575 (by norm_num) ⟨15287, by rfl⟩ (by norm_num))
theorem R48765 : Reach 48765 := rs (se 3 (by rfl) ⟨9143, by rfl⟩) (B 18287 (by norm_num) ⟨9143, by rfl⟩ (by norm_num))
theorem R48769 : Reach 48769 := rs (se 2 (by rfl) ⟨18288, by rfl⟩) (B 36577 (by norm_num) ⟨18288, by rfl⟩ (by norm_num))
theorem R48773 : Reach 48773 := rs (se 4 (by rfl) ⟨4572, by rfl⟩) (B 9145 (by norm_num) ⟨4572, by rfl⟩ (by norm_num))
theorem R48777 : Reach 48777 := rs (se 2 (by rfl) ⟨18291, by rfl⟩) (B 36583 (by norm_num) ⟨18291, by rfl⟩ (by norm_num))
theorem R48781 : Reach 48781 := rs (se 3 (by rfl) ⟨9146, by rfl⟩) (B 18293 (by norm_num) ⟨9146, by rfl⟩ (by norm_num))
theorem R114317 : Reach 114317 := rs (se 3 (by rfl) ⟨21434, by rfl⟩) (B 42869 (by norm_num) ⟨21434, by rfl⟩ (by norm_num))
theorem R48785 : Reach 48785 := rs (se 2 (by rfl) ⟨18294, by rfl⟩) (B 36589 (by norm_num) ⟨18294, by rfl⟩ (by norm_num))
theorem R48789 : Reach 48789 := rs (se 6 (by rfl) ⟨1143, by rfl⟩) (B 2287 (by norm_num) ⟨1143, by rfl⟩ (by norm_num))
theorem R48793 : Reach 48793 := rs (se 2 (by rfl) ⟨18297, by rfl⟩) (B 36595 (by norm_num) ⟨18297, by rfl⟩ (by norm_num))
theorem R48797 : Reach 48797 := rs (se 3 (by rfl) ⟨9149, by rfl⟩) (B 18299 (by norm_num) ⟨9149, by rfl⟩ (by norm_num))
theorem R48801 : Reach 48801 := rs (se 2 (by rfl) ⟨18300, by rfl⟩) (B 36601 (by norm_num) ⟨18300, by rfl⟩ (by norm_num))
theorem R48805 : Reach 48805 := rs (se 4 (by rfl) ⟨4575, by rfl⟩) (B 9151 (by norm_num) ⟨4575, by rfl⟩ (by norm_num))
theorem R48809 : Reach 48809 := rs (se 2 (by rfl) ⟨18303, by rfl⟩) (B 36607 (by norm_num) ⟨18303, by rfl⟩ (by norm_num))
theorem R48813 : Reach 48813 := rs (se 3 (by rfl) ⟨9152, by rfl⟩) (B 18305 (by norm_num) ⟨9152, by rfl⟩ (by norm_num))
theorem R48817 : Reach 48817 := rs (se 2 (by rfl) ⟨18306, by rfl⟩) (B 36613 (by norm_num) ⟨18306, by rfl⟩ (by norm_num))
theorem R245429 : Reach 245429 := rs (se 5 (by rfl) ⟨11504, by rfl⟩) (B 23009 (by norm_num) ⟨11504, by rfl⟩ (by norm_num))
theorem R48821 : Reach 48821 := rs (se 5 (by rfl) ⟨2288, by rfl⟩) (B 4577 (by norm_num) ⟨2288, by rfl⟩ (by norm_num))
theorem R48825 : Reach 48825 := rs (se 2 (by rfl) ⟨18309, by rfl⟩) (B 36619 (by norm_num) ⟨18309, by rfl⟩ (by norm_num))
theorem R48829 : Reach 48829 := rs (se 3 (by rfl) ⟨9155, by rfl⟩) (B 18311 (by norm_num) ⟨9155, by rfl⟩ (by norm_num))
theorem R48833 : Reach 48833 := rs (se 2 (by rfl) ⟨18312, by rfl⟩) (B 36625 (by norm_num) ⟨18312, by rfl⟩ (by norm_num))
theorem R48837 : Reach 48837 := rs (se 4 (by rfl) ⟨4578, by rfl⟩) (B 9157 (by norm_num) ⟨4578, by rfl⟩ (by norm_num))
theorem R48841 : Reach 48841 := rs (se 2 (by rfl) ⟨18315, by rfl⟩) (B 36631 (by norm_num) ⟨18315, by rfl⟩ (by norm_num))
theorem R48845 : Reach 48845 := rs (se 3 (by rfl) ⟨9158, by rfl⟩) (B 18317 (by norm_num) ⟨9158, by rfl⟩ (by norm_num))
theorem R48849 : Reach 48849 := rs (se 2 (by rfl) ⟨18318, by rfl⟩) (B 36637 (by norm_num) ⟨18318, by rfl⟩ (by norm_num))
theorem R704213 : Reach 704213 := rs (se 7 (by rfl) ⟨8252, by rfl⟩) (B 16505 (by norm_num) ⟨8252, by rfl⟩ (by norm_num))
theorem R48853 : Reach 48853 := rs (se 7 (by rfl) ⟨572, by rfl⟩) (B 1145 (by norm_num) ⟨572, by rfl⟩ (by norm_num))
theorem R48857 : Reach 48857 := rs (se 2 (by rfl) ⟨18321, by rfl⟩) (B 36643 (by norm_num) ⟨18321, by rfl⟩ (by norm_num))
theorem R114389 : Reach 114389 := rs (se 7 (by rfl) ⟨1340, by rfl⟩) (B 2681 (by norm_num) ⟨1340, by rfl⟩ (by norm_num))
theorem R48861 : Reach 48861 := rs (se 3 (by rfl) ⟨9161, by rfl⟩) (B 18323 (by norm_num) ⟨9161, by rfl⟩ (by norm_num))
theorem R48865 : Reach 48865 := rs (se 2 (by rfl) ⟨18324, by rfl⟩) (B 36649 (by norm_num) ⟨18324, by rfl⟩ (by norm_num))
theorem R179941 : Reach 179941 := rs (se 4 (by rfl) ⟨16869, by rfl⟩) (B 33739 (by norm_num) ⟨16869, by rfl⟩ (by norm_num))
theorem R48869 : Reach 48869 := rs (se 4 (by rfl) ⟨4581, by rfl⟩) (B 9163 (by norm_num) ⟨4581, by rfl⟩ (by norm_num))
theorem R48873 : Reach 48873 := rs (se 2 (by rfl) ⟨18327, by rfl⟩) (B 36655 (by norm_num) ⟨18327, by rfl⟩ (by norm_num))
theorem R48877 : Reach 48877 := rs (se 3 (by rfl) ⟨9164, by rfl⟩) (B 18329 (by norm_num) ⟨9164, by rfl⟩ (by norm_num))
theorem R48881 : Reach 48881 := rs (se 2 (by rfl) ⟨18330, by rfl⟩) (B 36661 (by norm_num) ⟨18330, by rfl⟩ (by norm_num))
theorem R48885 : Reach 48885 := rs (se 5 (by rfl) ⟨2291, by rfl⟩) (B 4583 (by norm_num) ⟨2291, by rfl⟩ (by norm_num))
theorem R48889 : Reach 48889 := rs (se 2 (by rfl) ⟨18333, by rfl⟩) (B 36667 (by norm_num) ⟨18333, by rfl⟩ (by norm_num))
theorem R81661 : Reach 81661 := rs (se 3 (by rfl) ⟨15311, by rfl⟩) (B 30623 (by norm_num) ⟨15311, by rfl⟩ (by norm_num))
theorem R48893 : Reach 48893 := rs (se 3 (by rfl) ⟨9167, by rfl⟩) (B 18335 (by norm_num) ⟨9167, by rfl⟩ (by norm_num))
theorem R48897 : Reach 48897 := rs (se 2 (by rfl) ⟨18336, by rfl⟩) (B 36673 (by norm_num) ⟨18336, by rfl⟩ (by norm_num))
theorem R48901 : Reach 48901 := rs (se 4 (by rfl) ⟨4584, by rfl⟩) (B 9169 (by norm_num) ⟨4584, by rfl⟩ (by norm_num))
theorem R114437 : Reach 114437 := rs (se 4 (by rfl) ⟨10728, by rfl⟩) (B 21457 (by norm_num) ⟨10728, by rfl⟩ (by norm_num))
theorem R48905 : Reach 48905 := rs (se 2 (by rfl) ⟨18339, by rfl⟩) (B 36679 (by norm_num) ⟨18339, by rfl⟩ (by norm_num))
theorem R48909 : Reach 48909 := rs (se 3 (by rfl) ⟨9170, by rfl⟩) (B 18341 (by norm_num) ⟨9170, by rfl⟩ (by norm_num))
theorem R48913 : Reach 48913 := rs (se 2 (by rfl) ⟨18342, by rfl⟩) (B 36685 (by norm_num) ⟨18342, by rfl⟩ (by norm_num))
theorem R147221 : Reach 147221 := rs (se 6 (by rfl) ⟨3450, by rfl⟩) (B 6901 (by norm_num) ⟨3450, by rfl⟩ (by norm_num))
theorem R48917 : Reach 48917 := rs (se 6 (by rfl) ⟨1146, by rfl⟩) (B 2293 (by norm_num) ⟨1146, by rfl⟩ (by norm_num))
theorem R48921 : Reach 48921 := rs (se 2 (by rfl) ⟨18345, by rfl⟩) (B 36691 (by norm_num) ⟨18345, by rfl⟩ (by norm_num))
theorem R48925 : Reach 48925 := rs (se 3 (by rfl) ⟨9173, by rfl⟩) (B 18347 (by norm_num) ⟨9173, by rfl⟩ (by norm_num))
theorem R114461 : Reach 114461 := rs (se 3 (by rfl) ⟨21461, by rfl⟩) (B 42923 (by norm_num) ⟨21461, by rfl⟩ (by norm_num))
theorem R48929 : Reach 48929 := rs (se 2 (by rfl) ⟨18348, by rfl⟩) (B 36697 (by norm_num) ⟨18348, by rfl⟩ (by norm_num))
theorem R48933 : Reach 48933 := rs (se 4 (by rfl) ⟨4587, by rfl⟩) (B 9175 (by norm_num) ⟨4587, by rfl⟩ (by norm_num))
theorem R48937 : Reach 48937 := rs (se 2 (by rfl) ⟨18351, by rfl⟩) (B 36703 (by norm_num) ⟨18351, by rfl⟩ (by norm_num))
theorem R48941 : Reach 48941 := rs (se 3 (by rfl) ⟨9176, by rfl⟩) (B 18353 (by norm_num) ⟨9176, by rfl⟩ (by norm_num))
theorem R48945 : Reach 48945 := rs (se 2 (by rfl) ⟨18354, by rfl⟩) (B 36709 (by norm_num) ⟨18354, by rfl⟩ (by norm_num))
theorem R48949 : Reach 48949 := rs (se 5 (by rfl) ⟨2294, by rfl⟩) (B 4589 (by norm_num) ⟨2294, by rfl⟩ (by norm_num))
theorem R48953 : Reach 48953 := rs (se 2 (by rfl) ⟨18357, by rfl⟩) (B 36715 (by norm_num) ⟨18357, by rfl⟩ (by norm_num))
theorem R48957 : Reach 48957 := rs (se 3 (by rfl) ⟨9179, by rfl⟩) (B 18359 (by norm_num) ⟨9179, by rfl⟩ (by norm_num))
theorem R48961 : Reach 48961 := rs (se 2 (by rfl) ⟨18360, by rfl⟩) (B 36721 (by norm_num) ⟨18360, by rfl⟩ (by norm_num))
theorem R48965 : Reach 48965 := rs (se 4 (by rfl) ⟨4590, by rfl⟩) (B 9181 (by norm_num) ⟨4590, by rfl⟩ (by norm_num))
theorem R48969 : Reach 48969 := rs (se 2 (by rfl) ⟨18363, by rfl⟩) (B 36727 (by norm_num) ⟨18363, by rfl⟩ (by norm_num))
theorem R48973 : Reach 48973 := rs (se 3 (by rfl) ⟨9182, by rfl⟩) (B 18365 (by norm_num) ⟨9182, by rfl⟩ (by norm_num))
theorem R48977 : Reach 48977 := rs (se 2 (by rfl) ⟨18366, by rfl⟩) (B 36733 (by norm_num) ⟨18366, by rfl⟩ (by norm_num))
theorem R81749 : Reach 81749 := rs (se 9 (by rfl) ⟨239, by rfl⟩) (B 479 (by norm_num) ⟨239, by rfl⟩ (by norm_num))
theorem R48981 : Reach 48981 := rs (se 9 (by rfl) ⟨143, by rfl⟩) (B 287 (by norm_num) ⟨143, by rfl⟩ (by norm_num))
theorem R48985 : Reach 48985 := rs (se 2 (by rfl) ⟨18369, by rfl⟩) (B 36739 (by norm_num) ⟨18369, by rfl⟩ (by norm_num))
theorem R48989 : Reach 48989 := rs (se 3 (by rfl) ⟨9185, by rfl⟩) (B 18371 (by norm_num) ⟨9185, by rfl⟩ (by norm_num))
theorem R48993 : Reach 48993 := rs (se 2 (by rfl) ⟨18372, by rfl⟩) (B 36745 (by norm_num) ⟨18372, by rfl⟩ (by norm_num))
theorem R48997 : Reach 48997 := rs (se 4 (by rfl) ⟨4593, by rfl⟩) (B 9187 (by norm_num) ⟨4593, by rfl⟩ (by norm_num))
theorem R114533 : Reach 114533 := rs (se 4 (by rfl) ⟨10737, by rfl⟩) (B 21475 (by norm_num) ⟨10737, by rfl⟩ (by norm_num))
theorem R49001 : Reach 49001 := rs (se 2 (by rfl) ⟨18375, by rfl⟩) (B 36751 (by norm_num) ⟨18375, by rfl⟩ (by norm_num))
theorem R49005 : Reach 49005 := rs (se 3 (by rfl) ⟨9188, by rfl⟩) (B 18377 (by norm_num) ⟨9188, by rfl⟩ (by norm_num))
theorem R49009 : Reach 49009 := rs (se 2 (by rfl) ⟨18378, by rfl⟩) (B 36757 (by norm_num) ⟨18378, by rfl⟩ (by norm_num))
theorem R49013 : Reach 49013 := rs (se 5 (by rfl) ⟨2297, by rfl⟩) (B 4595 (by norm_num) ⟨2297, by rfl⟩ (by norm_num))
theorem R49017 : Reach 49017 := rs (se 2 (by rfl) ⟨18381, by rfl⟩) (B 36763 (by norm_num) ⟨18381, by rfl⟩ (by norm_num))
theorem R49021 : Reach 49021 := rs (se 3 (by rfl) ⟨9191, by rfl⟩) (B 18383 (by norm_num) ⟨9191, by rfl⟩ (by norm_num))
theorem R49025 : Reach 49025 := rs (se 2 (by rfl) ⟨18384, by rfl⟩) (B 36769 (by norm_num) ⟨18384, by rfl⟩ (by norm_num))
theorem R49029 : Reach 49029 := rs (se 4 (by rfl) ⟨4596, by rfl⟩) (B 9193 (by norm_num) ⟨4596, by rfl⟩ (by norm_num))
theorem R49033 : Reach 49033 := rs (se 2 (by rfl) ⟨18387, by rfl⟩) (B 36775 (by norm_num) ⟨18387, by rfl⟩ (by norm_num))
theorem R49037 : Reach 49037 := rs (se 3 (by rfl) ⟨9194, by rfl⟩) (B 18389 (by norm_num) ⟨9194, by rfl⟩ (by norm_num))
theorem R49041 : Reach 49041 := rs (se 2 (by rfl) ⟨18390, by rfl⟩) (B 36781 (by norm_num) ⟨18390, by rfl⟩ (by norm_num))
theorem R49045 : Reach 49045 := rs (se 6 (by rfl) ⟨1149, by rfl⟩) (B 2299 (by norm_num) ⟨1149, by rfl⟩ (by norm_num))
theorem R49049 : Reach 49049 := rs (se 2 (by rfl) ⟨18393, by rfl⟩) (B 36787 (by norm_num) ⟨18393, by rfl⟩ (by norm_num))
theorem R49053 : Reach 49053 := rs (se 3 (by rfl) ⟨9197, by rfl⟩) (B 18395 (by norm_num) ⟨9197, by rfl⟩ (by norm_num))
theorem R49057 : Reach 49057 := rs (se 2 (by rfl) ⟨18396, by rfl⟩) (B 36793 (by norm_num) ⟨18396, by rfl⟩ (by norm_num))
theorem R49061 : Reach 49061 := rs (se 4 (by rfl) ⟨4599, by rfl⟩) (B 9199 (by norm_num) ⟨4599, by rfl⟩ (by norm_num))
theorem R49065 : Reach 49065 := rs (se 2 (by rfl) ⟨18399, by rfl⟩) (B 36799 (by norm_num) ⟨18399, by rfl⟩ (by norm_num))
theorem R49069 : Reach 49069 := rs (se 3 (by rfl) ⟨9200, by rfl⟩) (B 18401 (by norm_num) ⟨9200, by rfl⟩ (by norm_num))
theorem R114605 : Reach 114605 := rs (se 3 (by rfl) ⟨21488, by rfl⟩) (B 42977 (by norm_num) ⟨21488, by rfl⟩ (by norm_num))
theorem R49073 : Reach 49073 := rs (se 2 (by rfl) ⟨18402, by rfl⟩) (B 36805 (by norm_num) ⟨18402, by rfl⟩ (by norm_num))
theorem R49077 : Reach 49077 := rs (se 5 (by rfl) ⟨2300, by rfl⟩) (B 4601 (by norm_num) ⟨2300, by rfl⟩ (by norm_num))
theorem R49081 : Reach 49081 := rs (se 2 (by rfl) ⟨18405, by rfl⟩) (B 36811 (by norm_num) ⟨18405, by rfl⟩ (by norm_num))
theorem R49085 : Reach 49085 := rs (se 3 (by rfl) ⟨9203, by rfl⟩) (B 18407 (by norm_num) ⟨9203, by rfl⟩ (by norm_num))
theorem R49089 : Reach 49089 := rs (se 2 (by rfl) ⟨18408, by rfl⟩) (B 36817 (by norm_num) ⟨18408, by rfl⟩ (by norm_num))
theorem R49093 : Reach 49093 := rs (se 4 (by rfl) ⟨4602, by rfl⟩) (B 9205 (by norm_num) ⟨4602, by rfl⟩ (by norm_num))
theorem R49097 : Reach 49097 := rs (se 2 (by rfl) ⟨18411, by rfl⟩) (B 36823 (by norm_num) ⟨18411, by rfl⟩ (by norm_num))
theorem R49101 : Reach 49101 := rs (se 3 (by rfl) ⟨9206, by rfl⟩) (B 18413 (by norm_num) ⟨9206, by rfl⟩ (by norm_num))
theorem R49105 : Reach 49105 := rs (se 2 (by rfl) ⟨18414, by rfl⟩) (B 36829 (by norm_num) ⟨18414, by rfl⟩ (by norm_num))
theorem R81877 : Reach 81877 := rs (se 7 (by rfl) ⟨959, by rfl⟩) (B 1919 (by norm_num) ⟨959, by rfl⟩ (by norm_num))
theorem R49109 : Reach 49109 := rs (se 7 (by rfl) ⟨575, by rfl⟩) (B 1151 (by norm_num) ⟨575, by rfl⟩ (by norm_num))
theorem R49113 : Reach 49113 := rs (se 2 (by rfl) ⟨18417, by rfl⟩) (B 36835 (by norm_num) ⟨18417, by rfl⟩ (by norm_num))
theorem R49117 : Reach 49117 := rs (se 3 (by rfl) ⟨9209, by rfl⟩) (B 18419 (by norm_num) ⟨9209, by rfl⟩ (by norm_num))
theorem R49121 : Reach 49121 := rs (se 2 (by rfl) ⟨18420, by rfl⟩) (B 36841 (by norm_num) ⟨18420, by rfl⟩ (by norm_num))
theorem R49125 : Reach 49125 := rs (se 4 (by rfl) ⟨4605, by rfl⟩) (B 9211 (by norm_num) ⟨4605, by rfl⟩ (by norm_num))
theorem R49129 : Reach 49129 := rs (se 2 (by rfl) ⟨18423, by rfl⟩) (B 36847 (by norm_num) ⟨18423, by rfl⟩ (by norm_num))
theorem R49133 : Reach 49133 := rs (se 3 (by rfl) ⟨9212, by rfl⟩) (B 18425 (by norm_num) ⟨9212, by rfl⟩ (by norm_num))
theorem R49137 : Reach 49137 := rs (se 2 (by rfl) ⟨18426, by rfl⟩) (B 36853 (by norm_num) ⟨18426, by rfl⟩ (by norm_num))
theorem R49141 : Reach 49141 := rs (se 5 (by rfl) ⟨2303, by rfl⟩) (B 4607 (by norm_num) ⟨2303, by rfl⟩ (by norm_num))
theorem R114677 : Reach 114677 := rs (se 5 (by rfl) ⟨5375, by rfl⟩) (B 10751 (by norm_num) ⟨5375, by rfl⟩ (by norm_num))
theorem R49145 : Reach 49145 := rs (se 2 (by rfl) ⟨18429, by rfl⟩) (B 36859 (by norm_num) ⟨18429, by rfl⟩ (by norm_num))
theorem R49149 : Reach 49149 := rs (se 3 (by rfl) ⟨9215, by rfl⟩) (B 18431 (by norm_num) ⟨9215, by rfl⟩ (by norm_num))
theorem R49153 : Reach 49153 := rs (se 2 (by rfl) ⟨18432, by rfl⟩) (B 36865 (by norm_num) ⟨18432, by rfl⟩ (by norm_num))
theorem R49157 : Reach 49157 := rs (se 4 (by rfl) ⟨4608, by rfl⟩) (B 9217 (by norm_num) ⟨4608, by rfl⟩ (by norm_num))
theorem R49161 : Reach 49161 := rs (se 2 (by rfl) ⟨18435, by rfl⟩) (B 36871 (by norm_num) ⟨18435, by rfl⟩ (by norm_num))
theorem R49165 : Reach 49165 := rs (se 3 (by rfl) ⟨9218, by rfl⟩) (B 18437 (by norm_num) ⟨9218, by rfl⟩ (by norm_num))
theorem R49169 : Reach 49169 := rs (se 2 (by rfl) ⟨18438, by rfl⟩) (B 36877 (by norm_num) ⟨18438, by rfl⟩ (by norm_num))
theorem R180245 : Reach 180245 := rs (se 6 (by rfl) ⟨4224, by rfl⟩) (B 8449 (by norm_num) ⟨4224, by rfl⟩ (by norm_num))
theorem R49173 : Reach 49173 := rs (se 6 (by rfl) ⟨1152, by rfl⟩) (B 2305 (by norm_num) ⟨1152, by rfl⟩ (by norm_num))
theorem R49177 : Reach 49177 := rs (se 2 (by rfl) ⟨18441, by rfl⟩) (B 36883 (by norm_num) ⟨18441, by rfl⟩ (by norm_num))
theorem R49181 : Reach 49181 := rs (se 3 (by rfl) ⟨9221, by rfl⟩) (B 18443 (by norm_num) ⟨9221, by rfl⟩ (by norm_num))
theorem R49185 : Reach 49185 := rs (se 2 (by rfl) ⟨18444, by rfl⟩) (B 36889 (by norm_num) ⟨18444, by rfl⟩ (by norm_num))
theorem R49189 : Reach 49189 := rs (se 4 (by rfl) ⟨4611, by rfl⟩) (B 9223 (by norm_num) ⟨4611, by rfl⟩ (by norm_num))
theorem R213029 : Reach 213029 := rs (se 4 (by rfl) ⟨19971, by rfl⟩) (B 39943 (by norm_num) ⟨19971, by rfl⟩ (by norm_num))
theorem R49193 : Reach 49193 := rs (se 2 (by rfl) ⟨18447, by rfl⟩) (B 36895 (by norm_num) ⟨18447, by rfl⟩ (by norm_num))
theorem R81965 : Reach 81965 := rs (se 3 (by rfl) ⟨15368, by rfl⟩) (B 30737 (by norm_num) ⟨15368, by rfl⟩ (by norm_num))
theorem R49197 : Reach 49197 := rs (se 3 (by rfl) ⟨9224, by rfl⟩) (B 18449 (by norm_num) ⟨9224, by rfl⟩ (by norm_num))
theorem R49201 : Reach 49201 := rs (se 2 (by rfl) ⟨18450, by rfl⟩) (B 36901 (by norm_num) ⟨18450, by rfl⟩ (by norm_num))
theorem R49205 : Reach 49205 := rs (se 5 (by rfl) ⟨2306, by rfl⟩) (B 4613 (by norm_num) ⟨2306, by rfl⟩ (by norm_num))
theorem R49209 : Reach 49209 := rs (se 2 (by rfl) ⟨18453, by rfl⟩) (B 36907 (by norm_num) ⟨18453, by rfl⟩ (by norm_num))
theorem R49213 : Reach 49213 := rs (se 3 (by rfl) ⟨9227, by rfl⟩) (B 18455 (by norm_num) ⟨9227, by rfl⟩ (by norm_num))
theorem R114749 : Reach 114749 := rs (se 3 (by rfl) ⟨21515, by rfl⟩) (B 43031 (by norm_num) ⟨21515, by rfl⟩ (by norm_num))
theorem R49217 : Reach 49217 := rs (se 2 (by rfl) ⟨18456, by rfl⟩) (B 36913 (by norm_num) ⟨18456, by rfl⟩ (by norm_num))
theorem R49221 : Reach 49221 := rs (se 4 (by rfl) ⟨4614, by rfl⟩) (B 9229 (by norm_num) ⟨4614, by rfl⟩ (by norm_num))
theorem R49225 : Reach 49225 := rs (se 2 (by rfl) ⟨18459, by rfl⟩) (B 36919 (by norm_num) ⟨18459, by rfl⟩ (by norm_num))
theorem R49229 : Reach 49229 := rs (se 3 (by rfl) ⟨9230, by rfl⟩) (B 18461 (by norm_num) ⟨9230, by rfl⟩ (by norm_num))
theorem R49233 : Reach 49233 := rs (se 2 (by rfl) ⟨18462, by rfl⟩) (B 36925 (by norm_num) ⟨18462, by rfl⟩ (by norm_num))
theorem R49237 : Reach 49237 := rs (se 8 (by rfl) ⟨288, by rfl⟩) (B 577 (by norm_num) ⟨288, by rfl⟩ (by norm_num))
theorem R49241 : Reach 49241 := rs (se 2 (by rfl) ⟨18465, by rfl⟩) (B 36931 (by norm_num) ⟨18465, by rfl⟩ (by norm_num))
theorem R49245 : Reach 49245 := rs (se 3 (by rfl) ⟨9233, by rfl⟩) (B 18467 (by norm_num) ⟨9233, by rfl⟩ (by norm_num))
theorem R49249 : Reach 49249 := rs (se 2 (by rfl) ⟨18468, by rfl⟩) (B 36937 (by norm_num) ⟨18468, by rfl⟩ (by norm_num))
theorem R49253 : Reach 49253 := rs (se 4 (by rfl) ⟨4617, by rfl⟩) (B 9235 (by norm_num) ⟨4617, by rfl⟩ (by norm_num))
theorem R49257 : Reach 49257 := rs (se 2 (by rfl) ⟨18471, by rfl⟩) (B 36943 (by norm_num) ⟨18471, by rfl⟩ (by norm_num))
theorem R49261 : Reach 49261 := rs (se 3 (by rfl) ⟨9236, by rfl⟩) (B 18473 (by norm_num) ⟨9236, by rfl⟩ (by norm_num))
theorem R49265 : Reach 49265 := rs (se 2 (by rfl) ⟨18474, by rfl⟩) (B 36949 (by norm_num) ⟨18474, by rfl⟩ (by norm_num))
theorem R49269 : Reach 49269 := rs (se 5 (by rfl) ⟨2309, by rfl⟩) (B 4619 (by norm_num) ⟨2309, by rfl⟩ (by norm_num))
theorem R49273 : Reach 49273 := rs (se 2 (by rfl) ⟨18477, by rfl⟩) (B 36955 (by norm_num) ⟨18477, by rfl⟩ (by norm_num))
theorem R49277 : Reach 49277 := rs (se 3 (by rfl) ⟨9239, by rfl⟩) (B 18479 (by norm_num) ⟨9239, by rfl⟩ (by norm_num))
theorem R49281 : Reach 49281 := rs (se 2 (by rfl) ⟨18480, by rfl⟩) (B 36961 (by norm_num) ⟨18480, by rfl⟩ (by norm_num))
theorem R49285 : Reach 49285 := rs (se 4 (by rfl) ⟨4620, by rfl⟩) (B 9241 (by norm_num) ⟨4620, by rfl⟩ (by norm_num))
theorem R114821 : Reach 114821 := rs (se 4 (by rfl) ⟨10764, by rfl⟩) (B 21529 (by norm_num) ⟨10764, by rfl⟩ (by norm_num))
theorem R49289 : Reach 49289 := rs (se 2 (by rfl) ⟨18483, by rfl⟩) (B 36967 (by norm_num) ⟨18483, by rfl⟩ (by norm_num))
theorem R49293 : Reach 49293 := rs (se 3 (by rfl) ⟨9242, by rfl⟩) (B 18485 (by norm_num) ⟨9242, by rfl⟩ (by norm_num))
theorem R49297 : Reach 49297 := rs (se 2 (by rfl) ⟨18486, by rfl⟩) (B 36973 (by norm_num) ⟨18486, by rfl⟩ (by norm_num))
theorem R49301 : Reach 49301 := rs (se 6 (by rfl) ⟨1155, by rfl⟩) (B 2311 (by norm_num) ⟨1155, by rfl⟩ (by norm_num))
theorem R49305 : Reach 49305 := rs (se 2 (by rfl) ⟨18489, by rfl⟩) (B 36979 (by norm_num) ⟨18489, by rfl⟩ (by norm_num))
theorem R49309 : Reach 49309 := rs (se 3 (by rfl) ⟨9245, by rfl⟩) (B 18491 (by norm_num) ⟨9245, by rfl⟩ (by norm_num))
theorem R49313 : Reach 49313 := rs (se 2 (by rfl) ⟨18492, by rfl⟩) (B 36985 (by norm_num) ⟨18492, by rfl⟩ (by norm_num))
theorem R49317 : Reach 49317 := rs (se 4 (by rfl) ⟨4623, by rfl⟩) (B 9247 (by norm_num) ⟨4623, by rfl⟩ (by norm_num))
theorem R49321 : Reach 49321 := rs (se 2 (by rfl) ⟨18495, by rfl⟩) (B 36991 (by norm_num) ⟨18495, by rfl⟩ (by norm_num))
theorem R82093 : Reach 82093 := rs (se 3 (by rfl) ⟨15392, by rfl⟩) (B 30785 (by norm_num) ⟨15392, by rfl⟩ (by norm_num))
theorem R49325 : Reach 49325 := rs (se 3 (by rfl) ⟨9248, by rfl⟩) (B 18497 (by norm_num) ⟨9248, by rfl⟩ (by norm_num))
theorem R49329 : Reach 49329 := rs (se 2 (by rfl) ⟨18498, by rfl⟩) (B 36997 (by norm_num) ⟨18498, by rfl⟩ (by norm_num))
theorem R114869 : Reach 114869 := rs (se 5 (by rfl) ⟨5384, by rfl⟩) (B 10769 (by norm_num) ⟨5384, by rfl⟩ (by norm_num))
theorem R49333 : Reach 49333 := rs (se 5 (by rfl) ⟨2312, by rfl⟩) (B 4625 (by norm_num) ⟨2312, by rfl⟩ (by norm_num))
theorem R49337 : Reach 49337 := rs (se 2 (by rfl) ⟨18501, by rfl⟩) (B 37003 (by norm_num) ⟨18501, by rfl⟩ (by norm_num))
theorem R49341 : Reach 49341 := rs (se 3 (by rfl) ⟨9251, by rfl⟩) (B 18503 (by norm_num) ⟨9251, by rfl⟩ (by norm_num))
theorem R49345 : Reach 49345 := rs (se 2 (by rfl) ⟨18504, by rfl⟩) (B 37009 (by norm_num) ⟨18504, by rfl⟩ (by norm_num))
theorem R49349 : Reach 49349 := rs (se 4 (by rfl) ⟨4626, by rfl⟩) (B 9253 (by norm_num) ⟨4626, by rfl⟩ (by norm_num))
theorem R49353 : Reach 49353 := rs (se 2 (by rfl) ⟨18507, by rfl⟩) (B 37015 (by norm_num) ⟨18507, by rfl⟩ (by norm_num))
theorem R49357 : Reach 49357 := rs (se 3 (by rfl) ⟨9254, by rfl⟩) (B 18509 (by norm_num) ⟨9254, by rfl⟩ (by norm_num))
theorem R114893 : Reach 114893 := rs (se 3 (by rfl) ⟨21542, by rfl⟩) (B 43085 (by norm_num) ⟨21542, by rfl⟩ (by norm_num))
theorem R49361 : Reach 49361 := rs (se 2 (by rfl) ⟨18510, by rfl⟩) (B 37021 (by norm_num) ⟨18510, by rfl⟩ (by norm_num))
theorem R49365 : Reach 49365 := rs (se 7 (by rfl) ⟨578, by rfl⟩) (B 1157 (by norm_num) ⟨578, by rfl⟩ (by norm_num))
theorem R49369 : Reach 49369 := rs (se 2 (by rfl) ⟨18513, by rfl⟩) (B 37027 (by norm_num) ⟨18513, by rfl⟩ (by norm_num))
theorem R49373 : Reach 49373 := rs (se 3 (by rfl) ⟨9257, by rfl⟩) (B 18515 (by norm_num) ⟨9257, by rfl⟩ (by norm_num))
theorem R49377 : Reach 49377 := rs (se 2 (by rfl) ⟨18516, by rfl⟩) (B 37033 (by norm_num) ⟨18516, by rfl⟩ (by norm_num))
theorem R49381 : Reach 49381 := rs (se 4 (by rfl) ⟨4629, by rfl⟩) (B 9259 (by norm_num) ⟨4629, by rfl⟩ (by norm_num))
theorem R49385 : Reach 49385 := rs (se 2 (by rfl) ⟨18519, by rfl⟩) (B 37039 (by norm_num) ⟨18519, by rfl⟩ (by norm_num))
theorem R49389 : Reach 49389 := rs (se 3 (by rfl) ⟨9260, by rfl⟩) (B 18521 (by norm_num) ⟨9260, by rfl⟩ (by norm_num))
theorem R49393 : Reach 49393 := rs (se 2 (by rfl) ⟨18522, by rfl⟩) (B 37045 (by norm_num) ⟨18522, by rfl⟩ (by norm_num))
theorem R49397 : Reach 49397 := rs (se 5 (by rfl) ⟨2315, by rfl⟩) (B 4631 (by norm_num) ⟨2315, by rfl⟩ (by norm_num))
theorem R49401 : Reach 49401 := rs (se 2 (by rfl) ⟨18525, by rfl⟩) (B 37051 (by norm_num) ⟨18525, by rfl⟩ (by norm_num))
theorem R49405 : Reach 49405 := rs (se 3 (by rfl) ⟨9263, by rfl⟩) (B 18527 (by norm_num) ⟨9263, by rfl⟩ (by norm_num))
theorem R49409 : Reach 49409 := rs (se 2 (by rfl) ⟨18528, by rfl⟩) (B 37057 (by norm_num) ⟨18528, by rfl⟩ (by norm_num))
theorem R82181 : Reach 82181 := rs (se 4 (by rfl) ⟨7704, by rfl⟩) (B 15409 (by norm_num) ⟨7704, by rfl⟩ (by norm_num))
theorem R49413 : Reach 49413 := rs (se 4 (by rfl) ⟨4632, by rfl⟩) (B 9265 (by norm_num) ⟨4632, by rfl⟩ (by norm_num))
theorem R49417 : Reach 49417 := rs (se 2 (by rfl) ⟨18531, by rfl⟩) (B 37063 (by norm_num) ⟨18531, by rfl⟩ (by norm_num))
theorem R49421 : Reach 49421 := rs (se 3 (by rfl) ⟨9266, by rfl⟩) (B 18533 (by norm_num) ⟨9266, by rfl⟩ (by norm_num))
theorem R49425 : Reach 49425 := rs (se 2 (by rfl) ⟨18534, by rfl⟩) (B 37069 (by norm_num) ⟨18534, by rfl⟩ (by norm_num))
theorem R49429 : Reach 49429 := rs (se 6 (by rfl) ⟨1158, by rfl⟩) (B 2317 (by norm_num) ⟨1158, by rfl⟩ (by norm_num))
theorem R114965 : Reach 114965 := rs (se 6 (by rfl) ⟨2694, by rfl⟩) (B 5389 (by norm_num) ⟨2694, by rfl⟩ (by norm_num))
theorem R49433 : Reach 49433 := rs (se 2 (by rfl) ⟨18537, by rfl⟩) (B 37075 (by norm_num) ⟨18537, by rfl⟩ (by norm_num))
theorem R49437 : Reach 49437 := rs (se 3 (by rfl) ⟨9269, by rfl⟩) (B 18539 (by norm_num) ⟨9269, by rfl⟩ (by norm_num))
theorem R49441 : Reach 49441 := rs (se 2 (by rfl) ⟨18540, by rfl⟩) (B 37081 (by norm_num) ⟨18540, by rfl⟩ (by norm_num))
theorem R49445 : Reach 49445 := rs (se 4 (by rfl) ⟨4635, by rfl⟩) (B 9271 (by norm_num) ⟨4635, by rfl⟩ (by norm_num))
theorem R49449 : Reach 49449 := rs (se 2 (by rfl) ⟨18543, by rfl⟩) (B 37087 (by norm_num) ⟨18543, by rfl⟩ (by norm_num))
theorem R49453 : Reach 49453 := rs (se 3 (by rfl) ⟨9272, by rfl⟩) (B 18545 (by norm_num) ⟨9272, by rfl⟩ (by norm_num))
theorem R49457 : Reach 49457 := rs (se 2 (by rfl) ⟨18546, by rfl⟩) (B 37093 (by norm_num) ⟨18546, by rfl⟩ (by norm_num))
theorem R49461 : Reach 49461 := rs (se 5 (by rfl) ⟨2318, by rfl⟩) (B 4637 (by norm_num) ⟨2318, by rfl⟩ (by norm_num))
theorem R49465 : Reach 49465 := rs (se 2 (by rfl) ⟨18549, by rfl⟩) (B 37099 (by norm_num) ⟨18549, by rfl⟩ (by norm_num))
theorem R49469 : Reach 49469 := rs (se 3 (by rfl) ⟨9275, by rfl⟩) (B 18551 (by norm_num) ⟨9275, by rfl⟩ (by norm_num))
theorem R49473 : Reach 49473 := rs (se 2 (by rfl) ⟨18552, by rfl⟩) (B 37105 (by norm_num) ⟨18552, by rfl⟩ (by norm_num))
theorem R49477 : Reach 49477 := rs (se 4 (by rfl) ⟨4638, by rfl⟩) (B 9277 (by norm_num) ⟨4638, by rfl⟩ (by norm_num))
theorem R49481 : Reach 49481 := rs (se 2 (by rfl) ⟨18555, by rfl⟩) (B 37111 (by norm_num) ⟨18555, by rfl⟩ (by norm_num))
theorem R49485 : Reach 49485 := rs (se 3 (by rfl) ⟨9278, by rfl⟩) (B 18557 (by norm_num) ⟨9278, by rfl⟩ (by norm_num))
theorem R49489 : Reach 49489 := rs (se 2 (by rfl) ⟨18558, by rfl⟩) (B 37117 (by norm_num) ⟨18558, by rfl⟩ (by norm_num))
theorem R115021 : Reach 115021 := rs (se 3 (by rfl) ⟨21566, by rfl⟩) (B 43133 (by norm_num) ⟨21566, by rfl⟩ (by norm_num))
theorem R49493 : Reach 49493 := rs (se 10 (by rfl) ⟨72, by rfl⟩) (B 145 (by norm_num) ⟨72, by rfl⟩ (by norm_num))
theorem R49497 : Reach 49497 := rs (se 2 (by rfl) ⟨18561, by rfl⟩) (B 37123 (by norm_num) ⟨18561, by rfl⟩ (by norm_num))
theorem R49501 : Reach 49501 := rs (se 3 (by rfl) ⟨9281, by rfl⟩) (B 18563 (by norm_num) ⟨9281, by rfl⟩ (by norm_num))
theorem R49505 : Reach 49505 := rs (se 2 (by rfl) ⟨18564, by rfl⟩) (B 37129 (by norm_num) ⟨18564, by rfl⟩ (by norm_num))
theorem R49509 : Reach 49509 := rs (se 4 (by rfl) ⟨4641, by rfl⟩) (B 9283 (by norm_num) ⟨4641, by rfl⟩ (by norm_num))
theorem R49513 : Reach 49513 := rs (se 2 (by rfl) ⟨18567, by rfl⟩) (B 37135 (by norm_num) ⟨18567, by rfl⟩ (by norm_num))
theorem R49517 : Reach 49517 := rs (se 3 (by rfl) ⟨9284, by rfl⟩) (B 18569 (by norm_num) ⟨9284, by rfl⟩ (by norm_num))
theorem R49521 : Reach 49521 := rs (se 2 (by rfl) ⟨18570, by rfl⟩) (B 37141 (by norm_num) ⟨18570, by rfl⟩ (by norm_num))
theorem R49525 : Reach 49525 := rs (se 5 (by rfl) ⟨2321, by rfl⟩) (B 4643 (by norm_num) ⟨2321, by rfl⟩ (by norm_num))
theorem R49529 : Reach 49529 := rs (se 2 (by rfl) ⟨18573, by rfl⟩) (B 37147 (by norm_num) ⟨18573, by rfl⟩ (by norm_num))
theorem R49533 : Reach 49533 := rs (se 3 (by rfl) ⟨9287, by rfl⟩) (B 18575 (by norm_num) ⟨9287, by rfl⟩ (by norm_num))
theorem R82301 : Reach 82301 := rs (se 3 (by rfl) ⟨15431, by rfl⟩) (B 30863 (by norm_num) ⟨15431, by rfl⟩ (by norm_num))
theorem R49537 : Reach 49537 := rs (se 2 (by rfl) ⟨18576, by rfl⟩) (B 37153 (by norm_num) ⟨18576, by rfl⟩ (by norm_num))
theorem R82309 : Reach 82309 := rs (se 4 (by rfl) ⟨7716, by rfl⟩) (B 15433 (by norm_num) ⟨7716, by rfl⟩ (by norm_num))
theorem R49541 : Reach 49541 := rs (se 4 (by rfl) ⟨4644, by rfl⟩) (B 9289 (by norm_num) ⟨4644, by rfl⟩ (by norm_num))
theorem R49545 : Reach 49545 := rs (se 2 (by rfl) ⟨18579, by rfl⟩) (B 37159 (by norm_num) ⟨18579, by rfl⟩ (by norm_num))
theorem R49549 : Reach 49549 := rs (se 3 (by rfl) ⟨9290, by rfl⟩) (B 18581 (by norm_num) ⟨9290, by rfl⟩ (by norm_num))
theorem R49553 : Reach 49553 := rs (se 2 (by rfl) ⟨18582, by rfl⟩) (B 37165 (by norm_num) ⟨18582, by rfl⟩ (by norm_num))
theorem R82325 : Reach 82325 := rs (se 6 (by rfl) ⟨1929, by rfl⟩) (B 3859 (by norm_num) ⟨1929, by rfl⟩ (by norm_num))
theorem R49557 : Reach 49557 := rs (se 6 (by rfl) ⟨1161, by rfl⟩) (B 2323 (by norm_num) ⟨1161, by rfl⟩ (by norm_num))
theorem R49561 : Reach 49561 := rs (se 2 (by rfl) ⟨18585, by rfl⟩) (B 37171 (by norm_num) ⟨18585, by rfl⟩ (by norm_num))
theorem R49565 : Reach 49565 := rs (se 3 (by rfl) ⟨9293, by rfl⟩) (B 18587 (by norm_num) ⟨9293, by rfl⟩ (by norm_num))
theorem R49569 : Reach 49569 := rs (se 2 (by rfl) ⟨18588, by rfl⟩) (B 37177 (by norm_num) ⟨18588, by rfl⟩ (by norm_num))
theorem R49573 : Reach 49573 := rs (se 4 (by rfl) ⟨4647, by rfl⟩) (B 9295 (by norm_num) ⟨4647, by rfl⟩ (by norm_num))
theorem R49577 : Reach 49577 := rs (se 2 (by rfl) ⟨18591, by rfl⟩) (B 37183 (by norm_num) ⟨18591, by rfl⟩ (by norm_num))
theorem R49581 : Reach 49581 := rs (se 3 (by rfl) ⟨9296, by rfl⟩) (B 18593 (by norm_num) ⟨9296, by rfl⟩ (by norm_num))
theorem R49585 : Reach 49585 := rs (se 2 (by rfl) ⟨18594, by rfl⟩) (B 37189 (by norm_num) ⟨18594, by rfl⟩ (by norm_num))
theorem R49589 : Reach 49589 := rs (se 5 (by rfl) ⟨2324, by rfl⟩) (B 4649 (by norm_num) ⟨2324, by rfl⟩ (by norm_num))
theorem R49593 : Reach 49593 := rs (se 2 (by rfl) ⟨18597, by rfl⟩) (B 37195 (by norm_num) ⟨18597, by rfl⟩ (by norm_num))
theorem R49597 : Reach 49597 := rs (se 3 (by rfl) ⟨9299, by rfl⟩) (B 18599 (by norm_num) ⟨9299, by rfl⟩ (by norm_num))
theorem R49601 : Reach 49601 := rs (se 2 (by rfl) ⟨18600, by rfl⟩) (B 37201 (by norm_num) ⟨18600, by rfl⟩ (by norm_num))
theorem R49605 : Reach 49605 := rs (se 4 (by rfl) ⟨4650, by rfl⟩) (B 9301 (by norm_num) ⟨4650, by rfl⟩ (by norm_num))
theorem R49609 : Reach 49609 := rs (se 2 (by rfl) ⟨18603, by rfl⟩) (B 37207 (by norm_num) ⟨18603, by rfl⟩ (by norm_num))
theorem R49613 : Reach 49613 := rs (se 3 (by rfl) ⟨9302, by rfl⟩) (B 18605 (by norm_num) ⟨9302, by rfl⟩ (by norm_num))
theorem R49617 : Reach 49617 := rs (se 2 (by rfl) ⟨18606, by rfl⟩) (B 37213 (by norm_num) ⟨18606, by rfl⟩ (by norm_num))
theorem R49621 : Reach 49621 := rs (se 7 (by rfl) ⟨581, by rfl⟩) (B 1163 (by norm_num) ⟨581, by rfl⟩ (by norm_num))
theorem R49625 : Reach 49625 := rs (se 2 (by rfl) ⟨18609, by rfl⟩) (B 37219 (by norm_num) ⟨18609, by rfl⟩ (by norm_num))
theorem R82397 : Reach 82397 := rs (se 3 (by rfl) ⟨15449, by rfl⟩) (B 30899 (by norm_num) ⟨15449, by rfl⟩ (by norm_num))
theorem R49629 : Reach 49629 := rs (se 3 (by rfl) ⟨9305, by rfl⟩) (B 18611 (by norm_num) ⟨9305, by rfl⟩ (by norm_num))
theorem R49633 : Reach 49633 := rs (se 2 (by rfl) ⟨18612, by rfl⟩) (B 37225 (by norm_num) ⟨18612, by rfl⟩ (by norm_num))
theorem R49637 : Reach 49637 := rs (se 4 (by rfl) ⟨4653, by rfl⟩) (B 9307 (by norm_num) ⟨4653, by rfl⟩ (by norm_num))
theorem R49641 : Reach 49641 := rs (se 2 (by rfl) ⟨18615, by rfl⟩) (B 37231 (by norm_num) ⟨18615, by rfl⟩ (by norm_num))
theorem R49645 : Reach 49645 := rs (se 3 (by rfl) ⟨9308, by rfl⟩) (B 18617 (by norm_num) ⟨9308, by rfl⟩ (by norm_num))
theorem R49649 : Reach 49649 := rs (se 2 (by rfl) ⟨18618, by rfl⟩) (B 37237 (by norm_num) ⟨18618, by rfl⟩ (by norm_num))
theorem R49653 : Reach 49653 := rs (se 5 (by rfl) ⟨2327, by rfl⟩) (B 4655 (by norm_num) ⟨2327, by rfl⟩ (by norm_num))
theorem R49657 : Reach 49657 := rs (se 2 (by rfl) ⟨18621, by rfl⟩) (B 37243 (by norm_num) ⟨18621, by rfl⟩ (by norm_num))
theorem R49661 : Reach 49661 := rs (se 3 (by rfl) ⟨9311, by rfl⟩) (B 18623 (by norm_num) ⟨9311, by rfl⟩ (by norm_num))
theorem R49665 : Reach 49665 := rs (se 2 (by rfl) ⟨18624, by rfl⟩) (B 37249 (by norm_num) ⟨18624, by rfl⟩ (by norm_num))
theorem R49669 : Reach 49669 := rs (se 4 (by rfl) ⟨4656, by rfl⟩) (B 9313 (by norm_num) ⟨4656, by rfl⟩ (by norm_num))
theorem R49673 : Reach 49673 := rs (se 2 (by rfl) ⟨18627, by rfl⟩) (B 37255 (by norm_num) ⟨18627, by rfl⟩ (by norm_num))
theorem R49677 : Reach 49677 := rs (se 3 (by rfl) ⟨9314, by rfl⟩) (B 18629 (by norm_num) ⟨9314, by rfl⟩ (by norm_num))
theorem R49681 : Reach 49681 := rs (se 2 (by rfl) ⟨18630, by rfl⟩) (B 37261 (by norm_num) ⟨18630, by rfl⟩ (by norm_num))
theorem R49685 : Reach 49685 := rs (se 6 (by rfl) ⟨1164, by rfl⟩) (B 2329 (by norm_num) ⟨1164, by rfl⟩ (by norm_num))
theorem R49689 : Reach 49689 := rs (se 2 (by rfl) ⟨18633, by rfl⟩) (B 37267 (by norm_num) ⟨18633, by rfl⟩ (by norm_num))
theorem R49693 : Reach 49693 := rs (se 3 (by rfl) ⟨9317, by rfl⟩) (B 18635 (by norm_num) ⟨9317, by rfl⟩ (by norm_num))
theorem R49697 : Reach 49697 := rs (se 2 (by rfl) ⟨18636, by rfl⟩) (B 37273 (by norm_num) ⟨18636, by rfl⟩ (by norm_num))
theorem R49701 : Reach 49701 := rs (se 4 (by rfl) ⟨4659, by rfl⟩) (B 9319 (by norm_num) ⟨4659, by rfl⟩ (by norm_num))
theorem R49705 : Reach 49705 := rs (se 2 (by rfl) ⟨18639, by rfl⟩) (B 37279 (by norm_num) ⟨18639, by rfl⟩ (by norm_num))
theorem R49709 : Reach 49709 := rs (se 3 (by rfl) ⟨9320, by rfl⟩) (B 18641 (by norm_num) ⟨9320, by rfl⟩ (by norm_num))
theorem R49713 : Reach 49713 := rs (se 2 (by rfl) ⟨18642, by rfl⟩) (B 37285 (by norm_num) ⟨18642, by rfl⟩ (by norm_num))
theorem R49717 : Reach 49717 := rs (se 5 (by rfl) ⟨2330, by rfl⟩) (B 4661 (by norm_num) ⟨2330, by rfl⟩ (by norm_num))
theorem R49721 : Reach 49721 := rs (se 2 (by rfl) ⟨18645, by rfl⟩) (B 37291 (by norm_num) ⟨18645, by rfl⟩ (by norm_num))
theorem R49725 : Reach 49725 := rs (se 3 (by rfl) ⟨9323, by rfl⟩) (B 18647 (by norm_num) ⟨9323, by rfl⟩ (by norm_num))
theorem R49729 : Reach 49729 := rs (se 2 (by rfl) ⟨18648, by rfl⟩) (B 37297 (by norm_num) ⟨18648, by rfl⟩ (by norm_num))
theorem R49733 : Reach 49733 := rs (se 4 (by rfl) ⟨4662, by rfl⟩) (B 9325 (by norm_num) ⟨4662, by rfl⟩ (by norm_num))
theorem R49737 : Reach 49737 := rs (se 2 (by rfl) ⟨18651, by rfl⟩) (B 37303 (by norm_num) ⟨18651, by rfl⟩ (by norm_num))
theorem R49741 : Reach 49741 := rs (se 3 (by rfl) ⟨9326, by rfl⟩) (B 18653 (by norm_num) ⟨9326, by rfl⟩ (by norm_num))
theorem R49745 : Reach 49745 := rs (se 2 (by rfl) ⟨18654, by rfl⟩) (B 37309 (by norm_num) ⟨18654, by rfl⟩ (by norm_num))
theorem R49749 : Reach 49749 := rs (se 8 (by rfl) ⟨291, by rfl⟩) (B 583 (by norm_num) ⟨291, by rfl⟩ (by norm_num))
theorem R49753 : Reach 49753 := rs (se 2 (by rfl) ⟨18657, by rfl⟩) (B 37315 (by norm_num) ⟨18657, by rfl⟩ (by norm_num))
theorem R82525 : Reach 82525 := rs (se 3 (by rfl) ⟨15473, by rfl⟩) (B 30947 (by norm_num) ⟨15473, by rfl⟩ (by norm_num))
theorem R49757 : Reach 49757 := rs (se 3 (by rfl) ⟨9329, by rfl⟩) (B 18659 (by norm_num) ⟨9329, by rfl⟩ (by norm_num))
theorem R49761 : Reach 49761 := rs (se 2 (by rfl) ⟨18660, by rfl⟩) (B 37321 (by norm_num) ⟨18660, by rfl⟩ (by norm_num))
theorem R49765 : Reach 49765 := rs (se 4 (by rfl) ⟨4665, by rfl⟩) (B 9331 (by norm_num) ⟨4665, by rfl⟩ (by norm_num))
theorem R49769 : Reach 49769 := rs (se 2 (by rfl) ⟨18663, by rfl⟩) (B 37327 (by norm_num) ⟨18663, by rfl⟩ (by norm_num))
theorem R49773 : Reach 49773 := rs (se 3 (by rfl) ⟨9332, by rfl⟩) (B 18665 (by norm_num) ⟨9332, by rfl⟩ (by norm_num))
theorem R49777 : Reach 49777 := rs (se 2 (by rfl) ⟨18666, by rfl⟩) (B 37333 (by norm_num) ⟨18666, by rfl⟩ (by norm_num))
theorem R49781 : Reach 49781 := rs (se 5 (by rfl) ⟨2333, by rfl⟩) (B 4667 (by norm_num) ⟨2333, by rfl⟩ (by norm_num))
theorem R49785 : Reach 49785 := rs (se 2 (by rfl) ⟨18669, by rfl⟩) (B 37339 (by norm_num) ⟨18669, by rfl⟩ (by norm_num))
theorem R49789 : Reach 49789 := rs (se 3 (by rfl) ⟨9335, by rfl⟩) (B 18671 (by norm_num) ⟨9335, by rfl⟩ (by norm_num))
theorem R49793 : Reach 49793 := rs (se 2 (by rfl) ⟨18672, by rfl⟩) (B 37345 (by norm_num) ⟨18672, by rfl⟩ (by norm_num))
theorem R49797 : Reach 49797 := rs (se 4 (by rfl) ⟨4668, by rfl⟩) (B 9337 (by norm_num) ⟨4668, by rfl⟩ (by norm_num))
theorem R49801 : Reach 49801 := rs (se 2 (by rfl) ⟨18675, by rfl⟩) (B 37351 (by norm_num) ⟨18675, by rfl⟩ (by norm_num))
theorem R49805 : Reach 49805 := rs (se 3 (by rfl) ⟨9338, by rfl⟩) (B 18677 (by norm_num) ⟨9338, by rfl⟩ (by norm_num))
theorem R49809 : Reach 49809 := rs (se 2 (by rfl) ⟨18678, by rfl⟩) (B 37357 (by norm_num) ⟨18678, by rfl⟩ (by norm_num))
theorem R311957 : Reach 311957 := rs (se 6 (by rfl) ⟨7311, by rfl⟩) (B 14623 (by norm_num) ⟨7311, by rfl⟩ (by norm_num))
theorem R49813 : Reach 49813 := rs (se 6 (by rfl) ⟨1167, by rfl⟩) (B 2335 (by norm_num) ⟨1167, by rfl⟩ (by norm_num))
theorem R49817 : Reach 49817 := rs (se 2 (by rfl) ⟨18681, by rfl⟩) (B 37363 (by norm_num) ⟨18681, by rfl⟩ (by norm_num))
theorem R49821 : Reach 49821 := rs (se 3 (by rfl) ⟨9341, by rfl⟩) (B 18683 (by norm_num) ⟨9341, by rfl⟩ (by norm_num))
theorem R49825 : Reach 49825 := rs (se 2 (by rfl) ⟨18684, by rfl⟩) (B 37369 (by norm_num) ⟨18684, by rfl⟩ (by norm_num))
theorem R49829 : Reach 49829 := rs (se 4 (by rfl) ⟨4671, by rfl⟩) (B 9343 (by norm_num) ⟨4671, by rfl⟩ (by norm_num))
theorem R49833 : Reach 49833 := rs (se 2 (by rfl) ⟨18687, by rfl⟩) (B 37375 (by norm_num) ⟨18687, by rfl⟩ (by norm_num))
theorem R49837 : Reach 49837 := rs (se 3 (by rfl) ⟨9344, by rfl⟩) (B 18689 (by norm_num) ⟨9344, by rfl⟩ (by norm_num))
theorem R49841 : Reach 49841 := rs (se 2 (by rfl) ⟨18690, by rfl⟩) (B 37381 (by norm_num) ⟨18690, by rfl⟩ (by norm_num))
theorem R82613 : Reach 82613 := rs (se 5 (by rfl) ⟨3872, by rfl⟩) (B 7745 (by norm_num) ⟨3872, by rfl⟩ (by norm_num))
theorem R49845 : Reach 49845 := rs (se 5 (by rfl) ⟨2336, by rfl⟩) (B 4673 (by norm_num) ⟨2336, by rfl⟩ (by norm_num))
theorem R49849 : Reach 49849 := rs (se 2 (by rfl) ⟨18693, by rfl⟩) (B 37387 (by norm_num) ⟨18693, by rfl⟩ (by norm_num))
theorem R49853 : Reach 49853 := rs (se 3 (by rfl) ⟨9347, by rfl⟩) (B 18695 (by norm_num) ⟨9347, by rfl⟩ (by norm_num))
theorem R49857 : Reach 49857 := rs (se 2 (by rfl) ⟨18696, by rfl⟩) (B 37393 (by norm_num) ⟨18696, by rfl⟩ (by norm_num))
theorem R49861 : Reach 49861 := rs (se 4 (by rfl) ⟨4674, by rfl⟩) (B 9349 (by norm_num) ⟨4674, by rfl⟩ (by norm_num))
theorem R49865 : Reach 49865 := rs (se 2 (by rfl) ⟨18699, by rfl⟩) (B 37399 (by norm_num) ⟨18699, by rfl⟩ (by norm_num))
theorem R49869 : Reach 49869 := rs (se 3 (by rfl) ⟨9350, by rfl⟩) (B 18701 (by norm_num) ⟨9350, by rfl⟩ (by norm_num))
theorem R49873 : Reach 49873 := rs (se 2 (by rfl) ⟨18702, by rfl⟩) (B 37405 (by norm_num) ⟨18702, by rfl⟩ (by norm_num))
theorem R49877 : Reach 49877 := rs (se 7 (by rfl) ⟨584, by rfl⟩) (B 1169 (by norm_num) ⟨584, by rfl⟩ (by norm_num))
theorem R49881 : Reach 49881 := rs (se 2 (by rfl) ⟨18705, by rfl⟩) (B 37411 (by norm_num) ⟨18705, by rfl⟩ (by norm_num))
theorem R49885 : Reach 49885 := rs (se 3 (by rfl) ⟨9353, by rfl⟩) (B 18707 (by norm_num) ⟨9353, by rfl⟩ (by norm_num))
theorem R49889 : Reach 49889 := rs (se 2 (by rfl) ⟨18708, by rfl⟩) (B 37417 (by norm_num) ⟨18708, by rfl⟩ (by norm_num))
theorem R49893 : Reach 49893 := rs (se 4 (by rfl) ⟨4677, by rfl⟩) (B 9355 (by norm_num) ⟨4677, by rfl⟩ (by norm_num))
theorem R49897 : Reach 49897 := rs (se 2 (by rfl) ⟨18711, by rfl⟩) (B 37423 (by norm_num) ⟨18711, by rfl⟩ (by norm_num))
theorem R49901 : Reach 49901 := rs (se 3 (by rfl) ⟨9356, by rfl⟩) (B 18713 (by norm_num) ⟨9356, by rfl⟩ (by norm_num))
theorem R49905 : Reach 49905 := rs (se 2 (by rfl) ⟨18714, by rfl⟩) (B 37429 (by norm_num) ⟨18714, by rfl⟩ (by norm_num))
theorem R49909 : Reach 49909 := rs (se 5 (by rfl) ⟨2339, by rfl⟩) (B 4679 (by norm_num) ⟨2339, by rfl⟩ (by norm_num))
theorem R49913 : Reach 49913 := rs (se 2 (by rfl) ⟨18717, by rfl⟩) (B 37435 (by norm_num) ⟨18717, by rfl⟩ (by norm_num))
theorem R49917 : Reach 49917 := rs (se 3 (by rfl) ⟨9359, by rfl⟩) (B 18719 (by norm_num) ⟨9359, by rfl⟩ (by norm_num))
theorem R49921 : Reach 49921 := rs (se 2 (by rfl) ⟨18720, by rfl⟩) (B 37441 (by norm_num) ⟨18720, by rfl⟩ (by norm_num))
theorem R49925 : Reach 49925 := rs (se 4 (by rfl) ⟨4680, by rfl⟩) (B 9361 (by norm_num) ⟨4680, by rfl⟩ (by norm_num))
theorem R49929 : Reach 49929 := rs (se 2 (by rfl) ⟨18723, by rfl⟩) (B 37447 (by norm_num) ⟨18723, by rfl⟩ (by norm_num))
theorem R49933 : Reach 49933 := rs (se 3 (by rfl) ⟨9362, by rfl⟩) (B 18725 (by norm_num) ⟨9362, by rfl⟩ (by norm_num))
theorem R49937 : Reach 49937 := rs (se 2 (by rfl) ⟨18726, by rfl⟩) (B 37453 (by norm_num) ⟨18726, by rfl⟩ (by norm_num))
theorem R377621 : Reach 377621 := rs (se 6 (by rfl) ⟨8850, by rfl⟩) (B 17701 (by norm_num) ⟨8850, by rfl⟩ (by norm_num))
theorem R49941 : Reach 49941 := rs (se 6 (by rfl) ⟨1170, by rfl⟩) (B 2341 (by norm_num) ⟨1170, by rfl⟩ (by norm_num))
theorem R49945 : Reach 49945 := rs (se 2 (by rfl) ⟨18729, by rfl⟩) (B 37459 (by norm_num) ⟨18729, by rfl⟩ (by norm_num))
theorem R49949 : Reach 49949 := rs (se 3 (by rfl) ⟨9365, by rfl⟩) (B 18731 (by norm_num) ⟨9365, by rfl⟩ (by norm_num))
theorem R49953 : Reach 49953 := rs (se 2 (by rfl) ⟨18732, by rfl⟩) (B 37465 (by norm_num) ⟨18732, by rfl⟩ (by norm_num))
theorem R49957 : Reach 49957 := rs (se 4 (by rfl) ⟨4683, by rfl⟩) (B 9367 (by norm_num) ⟨4683, by rfl⟩ (by norm_num))
theorem R49961 : Reach 49961 := rs (se 2 (by rfl) ⟨18735, by rfl⟩) (B 37471 (by norm_num) ⟨18735, by rfl⟩ (by norm_num))
theorem R49965 : Reach 49965 := rs (se 3 (by rfl) ⟨9368, by rfl⟩) (B 18737 (by norm_num) ⟨9368, by rfl⟩ (by norm_num))
theorem R49969 : Reach 49969 := rs (se 2 (by rfl) ⟨18738, by rfl⟩) (B 37477 (by norm_num) ⟨18738, by rfl⟩ (by norm_num))
theorem R82741 : Reach 82741 := rs (se 5 (by rfl) ⟨3878, by rfl⟩) (B 7757 (by norm_num) ⟨3878, by rfl⟩ (by norm_num))
theorem R49973 : Reach 49973 := rs (se 5 (by rfl) ⟨2342, by rfl⟩) (B 4685 (by norm_num) ⟨2342, by rfl⟩ (by norm_num))
theorem R49977 : Reach 49977 := rs (se 2 (by rfl) ⟨18741, by rfl⟩) (B 37483 (by norm_num) ⟨18741, by rfl⟩ (by norm_num))
theorem R49981 : Reach 49981 := rs (se 3 (by rfl) ⟨9371, by rfl⟩) (B 18743 (by norm_num) ⟨9371, by rfl⟩ (by norm_num))
theorem R49985 : Reach 49985 := rs (se 2 (by rfl) ⟨18744, by rfl⟩) (B 37489 (by norm_num) ⟨18744, by rfl⟩ (by norm_num))
theorem R49989 : Reach 49989 := rs (se 4 (by rfl) ⟨4686, by rfl⟩) (B 9373 (by norm_num) ⟨4686, by rfl⟩ (by norm_num))
theorem R49993 : Reach 49993 := rs (se 2 (by rfl) ⟨18747, by rfl⟩) (B 37495 (by norm_num) ⟨18747, by rfl⟩ (by norm_num))
theorem R49997 : Reach 49997 := rs (se 3 (by rfl) ⟨9374, by rfl⟩) (B 18749 (by norm_num) ⟨9374, by rfl⟩ (by norm_num))
theorem R50001 : Reach 50001 := rs (se 2 (by rfl) ⟨18750, by rfl⟩) (B 37501 (by norm_num) ⟨18750, by rfl⟩ (by norm_num))
theorem R50005 : Reach 50005 := rs (se 9 (by rfl) ⟨146, by rfl⟩) (B 293 (by norm_num) ⟨146, by rfl⟩ (by norm_num))
theorem R50009 : Reach 50009 := rs (se 2 (by rfl) ⟨18753, by rfl⟩) (B 37507 (by norm_num) ⟨18753, by rfl⟩ (by norm_num))
theorem R50013 : Reach 50013 := rs (se 3 (by rfl) ⟨9377, by rfl⟩) (B 18755 (by norm_num) ⟨9377, by rfl⟩ (by norm_num))
theorem R50017 : Reach 50017 := rs (se 2 (by rfl) ⟨18756, by rfl⟩) (B 37513 (by norm_num) ⟨18756, by rfl⟩ (by norm_num))
theorem R50021 : Reach 50021 := rs (se 4 (by rfl) ⟨4689, by rfl⟩) (B 9379 (by norm_num) ⟨4689, by rfl⟩ (by norm_num))
theorem R50025 : Reach 50025 := rs (se 2 (by rfl) ⟨18759, by rfl⟩) (B 37519 (by norm_num) ⟨18759, by rfl⟩ (by norm_num))
theorem R50029 : Reach 50029 := rs (se 3 (by rfl) ⟨9380, by rfl⟩) (B 18761 (by norm_num) ⟨9380, by rfl⟩ (by norm_num))
theorem R50033 : Reach 50033 := rs (se 2 (by rfl) ⟨18762, by rfl⟩) (B 37525 (by norm_num) ⟨18762, by rfl⟩ (by norm_num))
theorem R50037 : Reach 50037 := rs (se 5 (by rfl) ⟨2345, by rfl⟩) (B 4691 (by norm_num) ⟨2345, by rfl⟩ (by norm_num))
theorem R50041 : Reach 50041 := rs (se 2 (by rfl) ⟨18765, by rfl⟩) (B 37531 (by norm_num) ⟨18765, by rfl⟩ (by norm_num))
theorem R50045 : Reach 50045 := rs (se 3 (by rfl) ⟨9383, by rfl⟩) (B 18767 (by norm_num) ⟨9383, by rfl⟩ (by norm_num))
theorem R50049 : Reach 50049 := rs (se 2 (by rfl) ⟨18768, by rfl⟩) (B 37537 (by norm_num) ⟨18768, by rfl⟩ (by norm_num))
theorem R50053 : Reach 50053 := rs (se 4 (by rfl) ⟨4692, by rfl⟩) (B 9385 (by norm_num) ⟨4692, by rfl⟩ (by norm_num))
theorem R50057 : Reach 50057 := rs (se 2 (by rfl) ⟨18771, by rfl⟩) (B 37543 (by norm_num) ⟨18771, by rfl⟩ (by norm_num))
theorem R82829 : Reach 82829 := rs (se 3 (by rfl) ⟨15530, by rfl⟩) (B 31061 (by norm_num) ⟨15530, by rfl⟩ (by norm_num))
theorem R50061 : Reach 50061 := rs (se 3 (by rfl) ⟨9386, by rfl⟩) (B 18773 (by norm_num) ⟨9386, by rfl⟩ (by norm_num))
theorem R50065 : Reach 50065 := rs (se 2 (by rfl) ⟨18774, by rfl⟩) (B 37549 (by norm_num) ⟨18774, by rfl⟩ (by norm_num))
theorem R50069 : Reach 50069 := rs (se 6 (by rfl) ⟨1173, by rfl⟩) (B 2347 (by norm_num) ⟨1173, by rfl⟩ (by norm_num))
theorem R50073 : Reach 50073 := rs (se 2 (by rfl) ⟨18777, by rfl⟩) (B 37555 (by norm_num) ⟨18777, by rfl⟩ (by norm_num))
theorem R50077 : Reach 50077 := rs (se 3 (by rfl) ⟨9389, by rfl⟩) (B 18779 (by norm_num) ⟨9389, by rfl⟩ (by norm_num))
theorem R50081 : Reach 50081 := rs (se 2 (by rfl) ⟨18780, by rfl⟩) (B 37561 (by norm_num) ⟨18780, by rfl⟩ (by norm_num))
theorem R50085 : Reach 50085 := rs (se 4 (by rfl) ⟨4695, by rfl⟩) (B 9391 (by norm_num) ⟨4695, by rfl⟩ (by norm_num))
theorem R50089 : Reach 50089 := rs (se 2 (by rfl) ⟨18783, by rfl⟩) (B 37567 (by norm_num) ⟨18783, by rfl⟩ (by norm_num))
theorem R50093 : Reach 50093 := rs (se 3 (by rfl) ⟨9392, by rfl⟩) (B 18785 (by norm_num) ⟨9392, by rfl⟩ (by norm_num))
theorem R50097 : Reach 50097 := rs (se 2 (by rfl) ⟨18786, by rfl⟩) (B 37573 (by norm_num) ⟨18786, by rfl⟩ (by norm_num))
theorem R50101 : Reach 50101 := rs (se 5 (by rfl) ⟨2348, by rfl⟩) (B 4697 (by norm_num) ⟨2348, by rfl⟩ (by norm_num))
theorem R50105 : Reach 50105 := rs (se 2 (by rfl) ⟨18789, by rfl⟩) (B 37579 (by norm_num) ⟨18789, by rfl⟩ (by norm_num))
theorem R50109 : Reach 50109 := rs (se 3 (by rfl) ⟨9395, by rfl⟩) (B 18791 (by norm_num) ⟨9395, by rfl⟩ (by norm_num))
theorem R50113 : Reach 50113 := rs (se 2 (by rfl) ⟨18792, by rfl⟩) (B 37585 (by norm_num) ⟨18792, by rfl⟩ (by norm_num))
theorem R246725 : Reach 246725 := rs (se 4 (by rfl) ⟨23130, by rfl⟩) (B 46261 (by norm_num) ⟨23130, by rfl⟩ (by norm_num))
theorem R50117 : Reach 50117 := rs (se 4 (by rfl) ⟨4698, by rfl⟩) (B 9397 (by norm_num) ⟨4698, by rfl⟩ (by norm_num))
theorem R50121 : Reach 50121 := rs (se 2 (by rfl) ⟨18795, by rfl⟩) (B 37591 (by norm_num) ⟨18795, by rfl⟩ (by norm_num))
theorem R50125 : Reach 50125 := rs (se 3 (by rfl) ⟨9398, by rfl⟩) (B 18797 (by norm_num) ⟨9398, by rfl⟩ (by norm_num))
theorem R50129 : Reach 50129 := rs (se 2 (by rfl) ⟨18798, by rfl⟩) (B 37597 (by norm_num) ⟨18798, by rfl⟩ (by norm_num))
theorem R50133 : Reach 50133 := rs (se 7 (by rfl) ⟨587, by rfl⟩) (B 1175 (by norm_num) ⟨587, by rfl⟩ (by norm_num))
theorem R50137 : Reach 50137 := rs (se 2 (by rfl) ⟨18801, by rfl⟩) (B 37603 (by norm_num) ⟨18801, by rfl⟩ (by norm_num))
theorem R50141 : Reach 50141 := rs (se 3 (by rfl) ⟨9401, by rfl⟩) (B 18803 (by norm_num) ⟨9401, by rfl⟩ (by norm_num))
theorem R50145 : Reach 50145 := rs (se 2 (by rfl) ⟨18804, by rfl⟩) (B 37609 (by norm_num) ⟨18804, by rfl⟩ (by norm_num))
theorem R50149 : Reach 50149 := rs (se 4 (by rfl) ⟨4701, by rfl⟩) (B 9403 (by norm_num) ⟨4701, by rfl⟩ (by norm_num))
theorem R50153 : Reach 50153 := rs (se 2 (by rfl) ⟨18807, by rfl⟩) (B 37615 (by norm_num) ⟨18807, by rfl⟩ (by norm_num))
theorem R50157 : Reach 50157 := rs (se 3 (by rfl) ⟨9404, by rfl⟩) (B 18809 (by norm_num) ⟨9404, by rfl⟩ (by norm_num))
theorem R50161 : Reach 50161 := rs (se 2 (by rfl) ⟨18810, by rfl⟩) (B 37621 (by norm_num) ⟨18810, by rfl⟩ (by norm_num))
theorem R50165 : Reach 50165 := rs (se 5 (by rfl) ⟨2351, by rfl⟩) (B 4703 (by norm_num) ⟨2351, by rfl⟩ (by norm_num))
theorem R50169 : Reach 50169 := rs (se 2 (by rfl) ⟨18813, by rfl⟩) (B 37627 (by norm_num) ⟨18813, by rfl⟩ (by norm_num))
theorem R50173 : Reach 50173 := rs (se 3 (by rfl) ⟨9407, by rfl⟩) (B 18815 (by norm_num) ⟨9407, by rfl⟩ (by norm_num))
theorem R50177 : Reach 50177 := rs (se 2 (by rfl) ⟨18816, by rfl⟩) (B 37633 (by norm_num) ⟨18816, by rfl⟩ (by norm_num))
theorem R50181 : Reach 50181 := rs (se 4 (by rfl) ⟨4704, by rfl⟩) (B 9409 (by norm_num) ⟨4704, by rfl⟩ (by norm_num))
theorem R50185 : Reach 50185 := rs (se 2 (by rfl) ⟨18819, by rfl⟩) (B 37639 (by norm_num) ⟨18819, by rfl⟩ (by norm_num))
theorem R82957 : Reach 82957 := rs (se 3 (by rfl) ⟨15554, by rfl⟩) (B 31109 (by norm_num) ⟨15554, by rfl⟩ (by norm_num))
theorem R50189 : Reach 50189 := rs (se 3 (by rfl) ⟨9410, by rfl⟩) (B 18821 (by norm_num) ⟨9410, by rfl⟩ (by norm_num))
theorem R50193 : Reach 50193 := rs (se 2 (by rfl) ⟨18822, by rfl⟩) (B 37645 (by norm_num) ⟨18822, by rfl⟩ (by norm_num))
theorem R50197 : Reach 50197 := rs (se 6 (by rfl) ⟨1176, by rfl⟩) (B 2353 (by norm_num) ⟨1176, by rfl⟩ (by norm_num))
theorem R50201 : Reach 50201 := rs (se 2 (by rfl) ⟨18825, by rfl⟩) (B 37651 (by norm_num) ⟨18825, by rfl⟩ (by norm_num))
theorem R50205 : Reach 50205 := rs (se 3 (by rfl) ⟨9413, by rfl⟩) (B 18827 (by norm_num) ⟨9413, by rfl⟩ (by norm_num))
theorem R50209 : Reach 50209 := rs (se 2 (by rfl) ⟨18828, by rfl⟩) (B 37657 (by norm_num) ⟨18828, by rfl⟩ (by norm_num))
theorem R50213 : Reach 50213 := rs (se 4 (by rfl) ⟨4707, by rfl⟩) (B 9415 (by norm_num) ⟨4707, by rfl⟩ (by norm_num))
theorem R50217 : Reach 50217 := rs (se 2 (by rfl) ⟨18831, by rfl⟩) (B 37663 (by norm_num) ⟨18831, by rfl⟩ (by norm_num))
theorem R50221 : Reach 50221 := rs (se 3 (by rfl) ⟨9416, by rfl⟩) (B 18833 (by norm_num) ⟨9416, by rfl⟩ (by norm_num))
theorem R50225 : Reach 50225 := rs (se 2 (by rfl) ⟨18834, by rfl⟩) (B 37669 (by norm_num) ⟨18834, by rfl⟩ (by norm_num))
theorem R50229 : Reach 50229 := rs (se 5 (by rfl) ⟨2354, by rfl⟩) (B 4709 (by norm_num) ⟨2354, by rfl⟩ (by norm_num))
theorem R50233 : Reach 50233 := rs (se 2 (by rfl) ⟨18837, by rfl⟩) (B 37675 (by norm_num) ⟨18837, by rfl⟩ (by norm_num))
theorem R50237 : Reach 50237 := rs (se 3 (by rfl) ⟨9419, by rfl⟩) (B 18839 (by norm_num) ⟨9419, by rfl⟩ (by norm_num))
theorem R50241 : Reach 50241 := rs (se 2 (by rfl) ⟨18840, by rfl⟩) (B 37681 (by norm_num) ⟨18840, by rfl⟩ (by norm_num))
theorem R50245 : Reach 50245 := rs (se 4 (by rfl) ⟨4710, by rfl⟩) (B 9421 (by norm_num) ⟨4710, by rfl⟩ (by norm_num))
theorem R50249 : Reach 50249 := rs (se 2 (by rfl) ⟨18843, by rfl⟩) (B 37687 (by norm_num) ⟨18843, by rfl⟩ (by norm_num))
theorem R50253 : Reach 50253 := rs (se 3 (by rfl) ⟨9422, by rfl⟩) (B 18845 (by norm_num) ⟨9422, by rfl⟩ (by norm_num))
theorem R50257 : Reach 50257 := rs (se 2 (by rfl) ⟨18846, by rfl⟩) (B 37693 (by norm_num) ⟨18846, by rfl⟩ (by norm_num))
theorem R50261 : Reach 50261 := rs (se 8 (by rfl) ⟨294, by rfl⟩) (B 589 (by norm_num) ⟨294, by rfl⟩ (by norm_num))
theorem R50265 : Reach 50265 := rs (se 2 (by rfl) ⟨18849, by rfl⟩) (B 37699 (by norm_num) ⟨18849, by rfl⟩ (by norm_num))
theorem R50269 : Reach 50269 := rs (se 3 (by rfl) ⟨9425, by rfl⟩) (B 18851 (by norm_num) ⟨9425, by rfl⟩ (by norm_num))
theorem R50273 : Reach 50273 := rs (se 2 (by rfl) ⟨18852, by rfl⟩) (B 37705 (by norm_num) ⟨18852, by rfl⟩ (by norm_num))
theorem R83045 : Reach 83045 := rs (se 4 (by rfl) ⟨7785, by rfl⟩) (B 15571 (by norm_num) ⟨7785, by rfl⟩ (by norm_num))
theorem R50277 : Reach 50277 := rs (se 4 (by rfl) ⟨4713, by rfl⟩) (B 9427 (by norm_num) ⟨4713, by rfl⟩ (by norm_num))
theorem R50281 : Reach 50281 := rs (se 2 (by rfl) ⟨18855, by rfl⟩) (B 37711 (by norm_num) ⟨18855, by rfl⟩ (by norm_num))
theorem R50285 : Reach 50285 := rs (se 3 (by rfl) ⟨9428, by rfl⟩) (B 18857 (by norm_num) ⟨9428, by rfl⟩ (by norm_num))
theorem R50289 : Reach 50289 := rs (se 2 (by rfl) ⟨18858, by rfl⟩) (B 37717 (by norm_num) ⟨18858, by rfl⟩ (by norm_num))
theorem R50293 : Reach 50293 := rs (se 5 (by rfl) ⟨2357, by rfl⟩) (B 4715 (by norm_num) ⟨2357, by rfl⟩ (by norm_num))
theorem R50297 : Reach 50297 := rs (se 2 (by rfl) ⟨18861, by rfl⟩) (B 37723 (by norm_num) ⟨18861, by rfl⟩ (by norm_num))
theorem R50301 : Reach 50301 := rs (se 3 (by rfl) ⟨9431, by rfl⟩) (B 18863 (by norm_num) ⟨9431, by rfl⟩ (by norm_num))
theorem R50305 : Reach 50305 := rs (se 2 (by rfl) ⟨18864, by rfl⟩) (B 37729 (by norm_num) ⟨18864, by rfl⟩ (by norm_num))
theorem R50309 : Reach 50309 := rs (se 4 (by rfl) ⟨4716, by rfl⟩) (B 9433 (by norm_num) ⟨4716, by rfl⟩ (by norm_num))
theorem R50313 : Reach 50313 := rs (se 2 (by rfl) ⟨18867, by rfl⟩) (B 37735 (by norm_num) ⟨18867, by rfl⟩ (by norm_num))
theorem R50317 : Reach 50317 := rs (se 3 (by rfl) ⟨9434, by rfl⟩) (B 18869 (by norm_num) ⟨9434, by rfl⟩ (by norm_num))
theorem R50321 : Reach 50321 := rs (se 2 (by rfl) ⟨18870, by rfl⟩) (B 37741 (by norm_num) ⟨18870, by rfl⟩ (by norm_num))
theorem R50325 : Reach 50325 := rs (se 6 (by rfl) ⟨1179, by rfl⟩) (B 2359 (by norm_num) ⟨1179, by rfl⟩ (by norm_num))
theorem R50329 : Reach 50329 := rs (se 2 (by rfl) ⟨18873, by rfl⟩) (B 37747 (by norm_num) ⟨18873, by rfl⟩ (by norm_num))
theorem R50333 : Reach 50333 := rs (se 3 (by rfl) ⟨9437, by rfl⟩) (B 18875 (by norm_num) ⟨9437, by rfl⟩ (by norm_num))
theorem R50337 : Reach 50337 := rs (se 2 (by rfl) ⟨18876, by rfl⟩) (B 37753 (by norm_num) ⟨18876, by rfl⟩ (by norm_num))
theorem R50341 : Reach 50341 := rs (se 4 (by rfl) ⟨4719, by rfl⟩) (B 9439 (by norm_num) ⟨4719, by rfl⟩ (by norm_num))
theorem R50345 : Reach 50345 := rs (se 2 (by rfl) ⟨18879, by rfl⟩) (B 37759 (by norm_num) ⟨18879, by rfl⟩ (by norm_num))
theorem R50349 : Reach 50349 := rs (se 3 (by rfl) ⟨9440, by rfl⟩) (B 18881 (by norm_num) ⟨9440, by rfl⟩ (by norm_num))
theorem R50353 : Reach 50353 := rs (se 2 (by rfl) ⟨18882, by rfl⟩) (B 37765 (by norm_num) ⟨18882, by rfl⟩ (by norm_num))
theorem R50357 : Reach 50357 := rs (se 5 (by rfl) ⟨2360, by rfl⟩) (B 4721 (by norm_num) ⟨2360, by rfl⟩ (by norm_num))
theorem R50361 : Reach 50361 := rs (se 2 (by rfl) ⟨18885, by rfl⟩) (B 37771 (by norm_num) ⟨18885, by rfl⟩ (by norm_num))
theorem R50365 : Reach 50365 := rs (se 3 (by rfl) ⟨9443, by rfl⟩) (B 18887 (by norm_num) ⟨9443, by rfl⟩ (by norm_num))
theorem R50369 : Reach 50369 := rs (se 2 (by rfl) ⟨18888, by rfl⟩) (B 37777 (by norm_num) ⟨18888, by rfl⟩ (by norm_num))
theorem R50373 : Reach 50373 := rs (se 4 (by rfl) ⟨4722, by rfl⟩) (B 9445 (by norm_num) ⟨4722, by rfl⟩ (by norm_num))
theorem R50377 : Reach 50377 := rs (se 2 (by rfl) ⟨18891, by rfl⟩) (B 37783 (by norm_num) ⟨18891, by rfl⟩ (by norm_num))
theorem R50381 : Reach 50381 := rs (se 3 (by rfl) ⟨9446, by rfl⟩) (B 18893 (by norm_num) ⟨9446, by rfl⟩ (by norm_num))
theorem R50385 : Reach 50385 := rs (se 2 (by rfl) ⟨18894, by rfl⟩) (B 37789 (by norm_num) ⟨18894, by rfl⟩ (by norm_num))
theorem R50389 : Reach 50389 := rs (se 7 (by rfl) ⟨590, by rfl⟩) (B 1181 (by norm_num) ⟨590, by rfl⟩ (by norm_num))
theorem R50393 : Reach 50393 := rs (se 2 (by rfl) ⟨18897, by rfl⟩) (B 37795 (by norm_num) ⟨18897, by rfl⟩ (by norm_num))
theorem R50397 : Reach 50397 := rs (se 3 (by rfl) ⟨9449, by rfl⟩) (B 18899 (by norm_num) ⟨9449, by rfl⟩ (by norm_num))
theorem R50401 : Reach 50401 := rs (se 2 (by rfl) ⟨18900, by rfl⟩) (B 37801 (by norm_num) ⟨18900, by rfl⟩ (by norm_num))
theorem R83173 : Reach 83173 := rs (se 4 (by rfl) ⟨7797, by rfl⟩) (B 15595 (by norm_num) ⟨7797, by rfl⟩ (by norm_num))
theorem R50405 : Reach 50405 := rs (se 4 (by rfl) ⟨4725, by rfl⟩) (B 9451 (by norm_num) ⟨4725, by rfl⟩ (by norm_num))
theorem R50409 : Reach 50409 := rs (se 2 (by rfl) ⟨18903, by rfl⟩) (B 37807 (by norm_num) ⟨18903, by rfl⟩ (by norm_num))
theorem R50413 : Reach 50413 := rs (se 3 (by rfl) ⟨9452, by rfl⟩) (B 18905 (by norm_num) ⟨9452, by rfl⟩ (by norm_num))
theorem R50417 : Reach 50417 := rs (se 2 (by rfl) ⟨18906, by rfl⟩) (B 37813 (by norm_num) ⟨18906, by rfl⟩ (by norm_num))
theorem R50421 : Reach 50421 := rs (se 5 (by rfl) ⟨2363, by rfl⟩) (B 4727 (by norm_num) ⟨2363, by rfl⟩ (by norm_num))
theorem R50425 : Reach 50425 := rs (se 2 (by rfl) ⟨18909, by rfl⟩) (B 37819 (by norm_num) ⟨18909, by rfl⟩ (by norm_num))
theorem R50429 : Reach 50429 := rs (se 3 (by rfl) ⟨9455, by rfl⟩) (B 18911 (by norm_num) ⟨9455, by rfl⟩ (by norm_num))
theorem R50433 : Reach 50433 := rs (se 2 (by rfl) ⟨18912, by rfl⟩) (B 37825 (by norm_num) ⟨18912, by rfl⟩ (by norm_num))
theorem R50437 : Reach 50437 := rs (se 4 (by rfl) ⟨4728, by rfl⟩) (B 9457 (by norm_num) ⟨4728, by rfl⟩ (by norm_num))
theorem R50441 : Reach 50441 := rs (se 2 (by rfl) ⟨18915, by rfl⟩) (B 37831 (by norm_num) ⟨18915, by rfl⟩ (by norm_num))
theorem R50445 : Reach 50445 := rs (se 3 (by rfl) ⟨9458, by rfl⟩) (B 18917 (by norm_num) ⟨9458, by rfl⟩ (by norm_num))
theorem R50449 : Reach 50449 := rs (se 2 (by rfl) ⟨18918, by rfl⟩) (B 37837 (by norm_num) ⟨18918, by rfl⟩ (by norm_num))
theorem R50453 : Reach 50453 := rs (se 6 (by rfl) ⟨1182, by rfl⟩) (B 2365 (by norm_num) ⟨1182, by rfl⟩ (by norm_num))
theorem R50457 : Reach 50457 := rs (se 2 (by rfl) ⟨18921, by rfl⟩) (B 37843 (by norm_num) ⟨18921, by rfl⟩ (by norm_num))
theorem R50461 : Reach 50461 := rs (se 3 (by rfl) ⟨9461, by rfl⟩) (B 18923 (by norm_num) ⟨9461, by rfl⟩ (by norm_num))
theorem R50465 : Reach 50465 := rs (se 2 (by rfl) ⟨18924, by rfl⟩) (B 37849 (by norm_num) ⟨18924, by rfl⟩ (by norm_num))
theorem R50469 : Reach 50469 := rs (se 4 (by rfl) ⟨4731, by rfl⟩) (B 9463 (by norm_num) ⟨4731, by rfl⟩ (by norm_num))
theorem R50473 : Reach 50473 := rs (se 2 (by rfl) ⟨18927, by rfl⟩) (B 37855 (by norm_num) ⟨18927, by rfl⟩ (by norm_num))
theorem R50477 : Reach 50477 := rs (se 3 (by rfl) ⟨9464, by rfl⟩) (B 18929 (by norm_num) ⟨9464, by rfl⟩ (by norm_num))
theorem R50481 : Reach 50481 := rs (se 2 (by rfl) ⟨18930, by rfl⟩) (B 37861 (by norm_num) ⟨18930, by rfl⟩ (by norm_num))
theorem R50485 : Reach 50485 := rs (se 5 (by rfl) ⟨2366, by rfl⟩) (B 4733 (by norm_num) ⟨2366, by rfl⟩ (by norm_num))
theorem R50489 : Reach 50489 := rs (se 2 (by rfl) ⟨18933, by rfl⟩) (B 37867 (by norm_num) ⟨18933, by rfl⟩ (by norm_num))
theorem R83261 : Reach 83261 := rs (se 3 (by rfl) ⟨15611, by rfl⟩) (B 31223 (by norm_num) ⟨15611, by rfl⟩ (by norm_num))
theorem R50493 : Reach 50493 := rs (se 3 (by rfl) ⟨9467, by rfl⟩) (B 18935 (by norm_num) ⟨9467, by rfl⟩ (by norm_num))
theorem R50497 : Reach 50497 := rs (se 2 (by rfl) ⟨18936, by rfl⟩) (B 37873 (by norm_num) ⟨18936, by rfl⟩ (by norm_num))
theorem R50501 : Reach 50501 := rs (se 4 (by rfl) ⟨4734, by rfl⟩) (B 9469 (by norm_num) ⟨4734, by rfl⟩ (by norm_num))
theorem R50505 : Reach 50505 := rs (se 2 (by rfl) ⟨18939, by rfl⟩) (B 37879 (by norm_num) ⟨18939, by rfl⟩ (by norm_num))
theorem R50509 : Reach 50509 := rs (se 3 (by rfl) ⟨9470, by rfl⟩) (B 18941 (by norm_num) ⟨9470, by rfl⟩ (by norm_num))
theorem R50513 : Reach 50513 := rs (se 2 (by rfl) ⟨18942, by rfl⟩) (B 37885 (by norm_num) ⟨18942, by rfl⟩ (by norm_num))
theorem R50517 : Reach 50517 := rs (se 12 (by rfl) ⟨18, by rfl⟩) (B 37 (by norm_num) ⟨18, by rfl⟩ (by norm_num))
theorem R50521 : Reach 50521 := rs (se 2 (by rfl) ⟨18945, by rfl⟩) (B 37891 (by norm_num) ⟨18945, by rfl⟩ (by norm_num))
theorem R50525 : Reach 50525 := rs (se 3 (by rfl) ⟨9473, by rfl⟩) (B 18947 (by norm_num) ⟨9473, by rfl⟩ (by norm_num))
theorem R50529 : Reach 50529 := rs (se 2 (by rfl) ⟨18948, by rfl⟩) (B 37897 (by norm_num) ⟨18948, by rfl⟩ (by norm_num))
theorem R50533 : Reach 50533 := rs (se 4 (by rfl) ⟨4737, by rfl⟩) (B 9475 (by norm_num) ⟨4737, by rfl⟩ (by norm_num))
theorem R50537 : Reach 50537 := rs (se 2 (by rfl) ⟨18951, by rfl⟩) (B 37903 (by norm_num) ⟨18951, by rfl⟩ (by norm_num))
theorem R50541 : Reach 50541 := rs (se 3 (by rfl) ⟨9476, by rfl⟩) (B 18953 (by norm_num) ⟨9476, by rfl⟩ (by norm_num))
theorem R50545 : Reach 50545 := rs (se 2 (by rfl) ⟨18954, by rfl⟩) (B 37909 (by norm_num) ⟨18954, by rfl⟩ (by norm_num))
theorem R50549 : Reach 50549 := rs (se 5 (by rfl) ⟨2369, by rfl⟩) (B 4739 (by norm_num) ⟨2369, by rfl⟩ (by norm_num))
theorem R50553 : Reach 50553 := rs (se 2 (by rfl) ⟨18957, by rfl⟩) (B 37915 (by norm_num) ⟨18957, by rfl⟩ (by norm_num))
theorem R50557 : Reach 50557 := rs (se 3 (by rfl) ⟨9479, by rfl⟩) (B 18959 (by norm_num) ⟨9479, by rfl⟩ (by norm_num))
theorem R50561 : Reach 50561 := rs (se 2 (by rfl) ⟨18960, by rfl⟩) (B 37921 (by norm_num) ⟨18960, by rfl⟩ (by norm_num))
theorem R50565 : Reach 50565 := rs (se 4 (by rfl) ⟨4740, by rfl⟩) (B 9481 (by norm_num) ⟨4740, by rfl⟩ (by norm_num))
theorem R50569 : Reach 50569 := rs (se 2 (by rfl) ⟨18963, by rfl⟩) (B 37927 (by norm_num) ⟨18963, by rfl⟩ (by norm_num))
theorem R50573 : Reach 50573 := rs (se 3 (by rfl) ⟨9482, by rfl⟩) (B 18965 (by norm_num) ⟨9482, by rfl⟩ (by norm_num))
theorem R50577 : Reach 50577 := rs (se 2 (by rfl) ⟨18966, by rfl⟩) (B 37933 (by norm_num) ⟨18966, by rfl⟩ (by norm_num))
theorem R50581 : Reach 50581 := rs (se 6 (by rfl) ⟨1185, by rfl⟩) (B 2371 (by norm_num) ⟨1185, by rfl⟩ (by norm_num))
theorem R50585 : Reach 50585 := rs (se 2 (by rfl) ⟨18969, by rfl⟩) (B 37939 (by norm_num) ⟨18969, by rfl⟩ (by norm_num))
theorem R50589 : Reach 50589 := rs (se 3 (by rfl) ⟨9485, by rfl⟩) (B 18971 (by norm_num) ⟨9485, by rfl⟩ (by norm_num))
theorem R50593 : Reach 50593 := rs (se 2 (by rfl) ⟨18972, by rfl⟩) (B 37945 (by norm_num) ⟨18972, by rfl⟩ (by norm_num))
theorem R50597 : Reach 50597 := rs (se 4 (by rfl) ⟨4743, by rfl⟩) (B 9487 (by norm_num) ⟨4743, by rfl⟩ (by norm_num))
theorem R50601 : Reach 50601 := rs (se 2 (by rfl) ⟨18975, by rfl⟩) (B 37951 (by norm_num) ⟨18975, by rfl⟩ (by norm_num))
theorem R50605 : Reach 50605 := rs (se 3 (by rfl) ⟨9488, by rfl⟩) (B 18977 (by norm_num) ⟨9488, by rfl⟩ (by norm_num))
theorem R50609 : Reach 50609 := rs (se 2 (by rfl) ⟨18978, by rfl⟩) (B 37957 (by norm_num) ⟨18978, by rfl⟩ (by norm_num))
theorem R50613 : Reach 50613 := rs (se 5 (by rfl) ⟨2372, by rfl⟩) (B 4745 (by norm_num) ⟨2372, by rfl⟩ (by norm_num))
theorem R50617 : Reach 50617 := rs (se 2 (by rfl) ⟨18981, by rfl⟩) (B 37963 (by norm_num) ⟨18981, by rfl⟩ (by norm_num))
theorem R83389 : Reach 83389 := rs (se 3 (by rfl) ⟨15635, by rfl⟩) (B 31271 (by norm_num) ⟨15635, by rfl⟩ (by norm_num))
theorem R50621 : Reach 50621 := rs (se 3 (by rfl) ⟨9491, by rfl⟩) (B 18983 (by norm_num) ⟨9491, by rfl⟩ (by norm_num))
theorem R50625 : Reach 50625 := rs (se 2 (by rfl) ⟨18984, by rfl⟩) (B 37969 (by norm_num) ⟨18984, by rfl⟩ (by norm_num))
theorem R50629 : Reach 50629 := rs (se 4 (by rfl) ⟨4746, by rfl⟩) (B 9493 (by norm_num) ⟨4746, by rfl⟩ (by norm_num))
theorem R50633 : Reach 50633 := rs (se 2 (by rfl) ⟨18987, by rfl⟩) (B 37975 (by norm_num) ⟨18987, by rfl⟩ (by norm_num))
theorem R50637 : Reach 50637 := rs (se 3 (by rfl) ⟨9494, by rfl⟩) (B 18989 (by norm_num) ⟨9494, by rfl⟩ (by norm_num))
theorem R50641 : Reach 50641 := rs (se 2 (by rfl) ⟨18990, by rfl⟩) (B 37981 (by norm_num) ⟨18990, by rfl⟩ (by norm_num))
theorem R148949 : Reach 148949 := rs (se 7 (by rfl) ⟨1745, by rfl⟩) (B 3491 (by norm_num) ⟨1745, by rfl⟩ (by norm_num))
theorem R50645 : Reach 50645 := rs (se 7 (by rfl) ⟨593, by rfl⟩) (B 1187 (by norm_num) ⟨593, by rfl⟩ (by norm_num))
theorem R50649 : Reach 50649 := rs (se 2 (by rfl) ⟨18993, by rfl⟩) (B 37987 (by norm_num) ⟨18993, by rfl⟩ (by norm_num))
theorem R50653 : Reach 50653 := rs (se 3 (by rfl) ⟨9497, by rfl⟩) (B 18995 (by norm_num) ⟨9497, by rfl⟩ (by norm_num))
theorem R50657 : Reach 50657 := rs (se 2 (by rfl) ⟨18996, by rfl⟩) (B 37993 (by norm_num) ⟨18996, by rfl⟩ (by norm_num))
theorem R50661 : Reach 50661 := rs (se 4 (by rfl) ⟨4749, by rfl⟩) (B 9499 (by norm_num) ⟨4749, by rfl⟩ (by norm_num))
theorem R50665 : Reach 50665 := rs (se 2 (by rfl) ⟨18999, by rfl⟩) (B 37999 (by norm_num) ⟨18999, by rfl⟩ (by norm_num))
theorem R50669 : Reach 50669 := rs (se 3 (by rfl) ⟨9500, by rfl⟩) (B 19001 (by norm_num) ⟨9500, by rfl⟩ (by norm_num))
theorem R50673 : Reach 50673 := rs (se 2 (by rfl) ⟨19002, by rfl⟩) (B 38005 (by norm_num) ⟨19002, by rfl⟩ (by norm_num))
theorem R50677 : Reach 50677 := rs (se 5 (by rfl) ⟨2375, by rfl⟩) (B 4751 (by norm_num) ⟨2375, by rfl⟩ (by norm_num))
theorem R50681 : Reach 50681 := rs (se 2 (by rfl) ⟨19005, by rfl⟩) (B 38011 (by norm_num) ⟨19005, by rfl⟩ (by norm_num))
theorem R50685 : Reach 50685 := rs (se 3 (by rfl) ⟨9503, by rfl⟩) (B 19007 (by norm_num) ⟨9503, by rfl⟩ (by norm_num))
theorem R50689 : Reach 50689 := rs (se 2 (by rfl) ⟨19008, by rfl⟩) (B 38017 (by norm_num) ⟨19008, by rfl⟩ (by norm_num))
theorem R50693 : Reach 50693 := rs (se 4 (by rfl) ⟨4752, by rfl⟩) (B 9505 (by norm_num) ⟨4752, by rfl⟩ (by norm_num))
theorem R50697 : Reach 50697 := rs (se 2 (by rfl) ⟨19011, by rfl⟩) (B 38023 (by norm_num) ⟨19011, by rfl⟩ (by norm_num))
theorem R50701 : Reach 50701 := rs (se 3 (by rfl) ⟨9506, by rfl⟩) (B 19013 (by norm_num) ⟨9506, by rfl⟩ (by norm_num))
theorem R50705 : Reach 50705 := rs (se 2 (by rfl) ⟨19014, by rfl⟩) (B 38029 (by norm_num) ⟨19014, by rfl⟩ (by norm_num))
theorem R116245 : Reach 116245 := rs (se 6 (by rfl) ⟨2724, by rfl⟩) (B 5449 (by norm_num) ⟨2724, by rfl⟩ (by norm_num))
theorem R83477 : Reach 83477 := rs (se 6 (by rfl) ⟨1956, by rfl⟩) (B 3913 (by norm_num) ⟨1956, by rfl⟩ (by norm_num))
theorem R50709 : Reach 50709 := rs (se 6 (by rfl) ⟨1188, by rfl⟩) (B 2377 (by norm_num) ⟨1188, by rfl⟩ (by norm_num))
theorem R50713 : Reach 50713 := rs (se 2 (by rfl) ⟨19017, by rfl⟩) (B 38035 (by norm_num) ⟨19017, by rfl⟩ (by norm_num))
theorem R50717 : Reach 50717 := rs (se 3 (by rfl) ⟨9509, by rfl⟩) (B 19019 (by norm_num) ⟨9509, by rfl⟩ (by norm_num))
theorem R50721 : Reach 50721 := rs (se 2 (by rfl) ⟨19020, by rfl⟩) (B 38041 (by norm_num) ⟨19020, by rfl⟩ (by norm_num))
theorem R50725 : Reach 50725 := rs (se 4 (by rfl) ⟨4755, by rfl⟩) (B 9511 (by norm_num) ⟨4755, by rfl⟩ (by norm_num))
theorem R50729 : Reach 50729 := rs (se 2 (by rfl) ⟨19023, by rfl⟩) (B 38047 (by norm_num) ⟨19023, by rfl⟩ (by norm_num))
theorem R50733 : Reach 50733 := rs (se 3 (by rfl) ⟨9512, by rfl⟩) (B 19025 (by norm_num) ⟨9512, by rfl⟩ (by norm_num))
theorem R50737 : Reach 50737 := rs (se 2 (by rfl) ⟨19026, by rfl⟩) (B 38053 (by norm_num) ⟨19026, by rfl⟩ (by norm_num))
theorem R50741 : Reach 50741 := rs (se 5 (by rfl) ⟨2378, by rfl⟩) (B 4757 (by norm_num) ⟨2378, by rfl⟩ (by norm_num))
theorem R50745 : Reach 50745 := rs (se 2 (by rfl) ⟨19029, by rfl⟩) (B 38059 (by norm_num) ⟨19029, by rfl⟩ (by norm_num))
theorem R50749 : Reach 50749 := rs (se 3 (by rfl) ⟨9515, by rfl⟩) (B 19031 (by norm_num) ⟨9515, by rfl⟩ (by norm_num))
theorem R50753 : Reach 50753 := rs (se 2 (by rfl) ⟨19032, by rfl⟩) (B 38065 (by norm_num) ⟨19032, by rfl⟩ (by norm_num))
theorem R50757 : Reach 50757 := rs (se 4 (by rfl) ⟨4758, by rfl⟩) (B 9517 (by norm_num) ⟨4758, by rfl⟩ (by norm_num))
theorem R50761 : Reach 50761 := rs (se 2 (by rfl) ⟨19035, by rfl⟩) (B 38071 (by norm_num) ⟨19035, by rfl⟩ (by norm_num))
theorem R50765 : Reach 50765 := rs (se 3 (by rfl) ⟨9518, by rfl⟩) (B 19037 (by norm_num) ⟨9518, by rfl⟩ (by norm_num))
theorem R50769 : Reach 50769 := rs (se 2 (by rfl) ⟨19038, by rfl⟩) (B 38077 (by norm_num) ⟨19038, by rfl⟩ (by norm_num))
theorem R50773 : Reach 50773 := rs (se 8 (by rfl) ⟨297, by rfl⟩) (B 595 (by norm_num) ⟨297, by rfl⟩ (by norm_num))
theorem R50777 : Reach 50777 := rs (se 2 (by rfl) ⟨19041, by rfl⟩) (B 38083 (by norm_num) ⟨19041, by rfl⟩ (by norm_num))
theorem R50781 : Reach 50781 := rs (se 3 (by rfl) ⟨9521, by rfl⟩) (B 19043 (by norm_num) ⟨9521, by rfl⟩ (by norm_num))
theorem R50785 : Reach 50785 := rs (se 2 (by rfl) ⟨19044, by rfl⟩) (B 38089 (by norm_num) ⟨19044, by rfl⟩ (by norm_num))
theorem R50789 : Reach 50789 := rs (se 4 (by rfl) ⟨4761, by rfl⟩) (B 9523 (by norm_num) ⟨4761, by rfl⟩ (by norm_num))
theorem R50793 : Reach 50793 := rs (se 2 (by rfl) ⟨19047, by rfl⟩) (B 38095 (by norm_num) ⟨19047, by rfl⟩ (by norm_num))
theorem R50797 : Reach 50797 := rs (se 3 (by rfl) ⟨9524, by rfl⟩) (B 19049 (by norm_num) ⟨9524, by rfl⟩ (by norm_num))
theorem R50801 : Reach 50801 := rs (se 2 (by rfl) ⟨19050, by rfl⟩) (B 38101 (by norm_num) ⟨19050, by rfl⟩ (by norm_num))
theorem R50805 : Reach 50805 := rs (se 5 (by rfl) ⟨2381, by rfl⟩) (B 4763 (by norm_num) ⟨2381, by rfl⟩ (by norm_num))
theorem R50809 : Reach 50809 := rs (se 2 (by rfl) ⟨19053, by rfl⟩) (B 38107 (by norm_num) ⟨19053, by rfl⟩ (by norm_num))
theorem R50813 : Reach 50813 := rs (se 3 (by rfl) ⟨9527, by rfl⟩) (B 19055 (by norm_num) ⟨9527, by rfl⟩ (by norm_num))
theorem R50817 : Reach 50817 := rs (se 2 (by rfl) ⟨19056, by rfl⟩) (B 38113 (by norm_num) ⟨19056, by rfl⟩ (by norm_num))
theorem R50821 : Reach 50821 := rs (se 4 (by rfl) ⟨4764, by rfl⟩) (B 9529 (by norm_num) ⟨4764, by rfl⟩ (by norm_num))
theorem R50825 : Reach 50825 := rs (se 2 (by rfl) ⟨19059, by rfl⟩) (B 38119 (by norm_num) ⟨19059, by rfl⟩ (by norm_num))
theorem R50829 : Reach 50829 := rs (se 3 (by rfl) ⟨9530, by rfl⟩) (B 19061 (by norm_num) ⟨9530, by rfl⟩ (by norm_num))
theorem R50833 : Reach 50833 := rs (se 2 (by rfl) ⟨19062, by rfl⟩) (B 38125 (by norm_num) ⟨19062, by rfl⟩ (by norm_num))
theorem R83605 : Reach 83605 := rs (se 6 (by rfl) ⟨1959, by rfl⟩) (B 3919 (by norm_num) ⟨1959, by rfl⟩ (by norm_num))
theorem R50837 : Reach 50837 := rs (se 6 (by rfl) ⟨1191, by rfl⟩) (B 2383 (by norm_num) ⟨1191, by rfl⟩ (by norm_num))
theorem R50841 : Reach 50841 := rs (se 2 (by rfl) ⟨19065, by rfl⟩) (B 38131 (by norm_num) ⟨19065, by rfl⟩ (by norm_num))
theorem R50845 : Reach 50845 := rs (se 3 (by rfl) ⟨9533, by rfl⟩) (B 19067 (by norm_num) ⟨9533, by rfl⟩ (by norm_num))
theorem R50849 : Reach 50849 := rs (se 2 (by rfl) ⟨19068, by rfl⟩) (B 38137 (by norm_num) ⟨19068, by rfl⟩ (by norm_num))
theorem R50853 : Reach 50853 := rs (se 4 (by rfl) ⟨4767, by rfl⟩) (B 9535 (by norm_num) ⟨4767, by rfl⟩ (by norm_num))
theorem R50857 : Reach 50857 := rs (se 2 (by rfl) ⟨19071, by rfl⟩) (B 38143 (by norm_num) ⟨19071, by rfl⟩ (by norm_num))
theorem R50861 : Reach 50861 := rs (se 3 (by rfl) ⟨9536, by rfl⟩) (B 19073 (by norm_num) ⟨9536, by rfl⟩ (by norm_num))
theorem R50865 : Reach 50865 := rs (se 2 (by rfl) ⟨19074, by rfl⟩) (B 38149 (by norm_num) ⟨19074, by rfl⟩ (by norm_num))
theorem R50869 : Reach 50869 := rs (se 5 (by rfl) ⟨2384, by rfl⟩) (B 4769 (by norm_num) ⟨2384, by rfl⟩ (by norm_num))
theorem R50873 : Reach 50873 := rs (se 2 (by rfl) ⟨19077, by rfl⟩) (B 38155 (by norm_num) ⟨19077, by rfl⟩ (by norm_num))
theorem R50877 : Reach 50877 := rs (se 3 (by rfl) ⟨9539, by rfl⟩) (B 19079 (by norm_num) ⟨9539, by rfl⟩ (by norm_num))
theorem R50881 : Reach 50881 := rs (se 2 (by rfl) ⟨19080, by rfl⟩) (B 38161 (by norm_num) ⟨19080, by rfl⟩ (by norm_num))
theorem R50885 : Reach 50885 := rs (se 4 (by rfl) ⟨4770, by rfl⟩) (B 9541 (by norm_num) ⟨4770, by rfl⟩ (by norm_num))
theorem R50889 : Reach 50889 := rs (se 2 (by rfl) ⟨19083, by rfl⟩) (B 38167 (by norm_num) ⟨19083, by rfl⟩ (by norm_num))
theorem R50893 : Reach 50893 := rs (se 3 (by rfl) ⟨9542, by rfl⟩) (B 19085 (by norm_num) ⟨9542, by rfl⟩ (by norm_num))
theorem R50897 : Reach 50897 := rs (se 2 (by rfl) ⟨19086, by rfl⟩) (B 38173 (by norm_num) ⟨19086, by rfl⟩ (by norm_num))
theorem R50901 : Reach 50901 := rs (se 7 (by rfl) ⟨596, by rfl⟩) (B 1193 (by norm_num) ⟨596, by rfl⟩ (by norm_num))
theorem R50905 : Reach 50905 := rs (se 2 (by rfl) ⟨19089, by rfl⟩) (B 38179 (by norm_num) ⟨19089, by rfl⟩ (by norm_num))
theorem R50909 : Reach 50909 := rs (se 3 (by rfl) ⟨9545, by rfl⟩) (B 19091 (by norm_num) ⟨9545, by rfl⟩ (by norm_num))
theorem R50913 : Reach 50913 := rs (se 2 (by rfl) ⟨19092, by rfl⟩) (B 38185 (by norm_num) ⟨19092, by rfl⟩ (by norm_num))
theorem R50917 : Reach 50917 := rs (se 4 (by rfl) ⟨4773, by rfl⟩) (B 9547 (by norm_num) ⟨4773, by rfl⟩ (by norm_num))
theorem R50921 : Reach 50921 := rs (se 2 (by rfl) ⟨19095, by rfl⟩) (B 38191 (by norm_num) ⟨19095, by rfl⟩ (by norm_num))
theorem R83693 : Reach 83693 := rs (se 3 (by rfl) ⟨15692, by rfl⟩) (B 31385 (by norm_num) ⟨15692, by rfl⟩ (by norm_num))
theorem R50925 : Reach 50925 := rs (se 3 (by rfl) ⟨9548, by rfl⟩) (B 19097 (by norm_num) ⟨9548, by rfl⟩ (by norm_num))
theorem R50929 : Reach 50929 := rs (se 2 (by rfl) ⟨19098, by rfl⟩) (B 38197 (by norm_num) ⟨19098, by rfl⟩ (by norm_num))
theorem R50933 : Reach 50933 := rs (se 5 (by rfl) ⟨2387, by rfl⟩) (B 4775 (by norm_num) ⟨2387, by rfl⟩ (by norm_num))
theorem R50937 : Reach 50937 := rs (se 2 (by rfl) ⟨19101, by rfl⟩) (B 38203 (by norm_num) ⟨19101, by rfl⟩ (by norm_num))
theorem R50941 : Reach 50941 := rs (se 3 (by rfl) ⟨9551, by rfl⟩) (B 19103 (by norm_num) ⟨9551, by rfl⟩ (by norm_num))
theorem R50945 : Reach 50945 := rs (se 2 (by rfl) ⟨19104, by rfl⟩) (B 38209 (by norm_num) ⟨19104, by rfl⟩ (by norm_num))
theorem R50949 : Reach 50949 := rs (se 4 (by rfl) ⟨4776, by rfl⟩) (B 9553 (by norm_num) ⟨4776, by rfl⟩ (by norm_num))
theorem R50953 : Reach 50953 := rs (se 2 (by rfl) ⟨19107, by rfl⟩) (B 38215 (by norm_num) ⟨19107, by rfl⟩ (by norm_num))
theorem R50957 : Reach 50957 := rs (se 3 (by rfl) ⟨9554, by rfl⟩) (B 19109 (by norm_num) ⟨9554, by rfl⟩ (by norm_num))
theorem R50961 : Reach 50961 := rs (se 2 (by rfl) ⟨19110, by rfl⟩) (B 38221 (by norm_num) ⟨19110, by rfl⟩ (by norm_num))
theorem R214805 : Reach 214805 := rs (se 6 (by rfl) ⟨5034, by rfl⟩) (B 10069 (by norm_num) ⟨5034, by rfl⟩ (by norm_num))
theorem R50965 : Reach 50965 := rs (se 6 (by rfl) ⟨1194, by rfl⟩) (B 2389 (by norm_num) ⟨1194, by rfl⟩ (by norm_num))
theorem R50969 : Reach 50969 := rs (se 2 (by rfl) ⟨19113, by rfl⟩) (B 38227 (by norm_num) ⟨19113, by rfl⟩ (by norm_num))
theorem R50973 : Reach 50973 := rs (se 3 (by rfl) ⟨9557, by rfl⟩) (B 19115 (by norm_num) ⟨9557, by rfl⟩ (by norm_num))
theorem R50977 : Reach 50977 := rs (se 2 (by rfl) ⟨19116, by rfl⟩) (B 38233 (by norm_num) ⟨19116, by rfl⟩ (by norm_num))
theorem R50981 : Reach 50981 := rs (se 4 (by rfl) ⟨4779, by rfl⟩) (B 9559 (by norm_num) ⟨4779, by rfl⟩ (by norm_num))
theorem R50985 : Reach 50985 := rs (se 2 (by rfl) ⟨19119, by rfl⟩) (B 38239 (by norm_num) ⟨19119, by rfl⟩ (by norm_num))
theorem R50989 : Reach 50989 := rs (se 3 (by rfl) ⟨9560, by rfl⟩) (B 19121 (by norm_num) ⟨9560, by rfl⟩ (by norm_num))
theorem R50993 : Reach 50993 := rs (se 2 (by rfl) ⟨19122, by rfl⟩) (B 38245 (by norm_num) ⟨19122, by rfl⟩ (by norm_num))
theorem R50997 : Reach 50997 := rs (se 5 (by rfl) ⟨2390, by rfl⟩) (B 4781 (by norm_num) ⟨2390, by rfl⟩ (by norm_num))
theorem R51001 : Reach 51001 := rs (se 2 (by rfl) ⟨19125, by rfl⟩) (B 38251 (by norm_num) ⟨19125, by rfl⟩ (by norm_num))
theorem R51005 : Reach 51005 := rs (se 3 (by rfl) ⟨9563, by rfl⟩) (B 19127 (by norm_num) ⟨9563, by rfl⟩ (by norm_num))
theorem R51009 : Reach 51009 := rs (se 2 (by rfl) ⟨19128, by rfl⟩) (B 38257 (by norm_num) ⟨19128, by rfl⟩ (by norm_num))
theorem R51013 : Reach 51013 := rs (se 4 (by rfl) ⟨4782, by rfl⟩) (B 9565 (by norm_num) ⟨4782, by rfl⟩ (by norm_num))
theorem R51017 : Reach 51017 := rs (se 2 (by rfl) ⟨19131, by rfl⟩) (B 38263 (by norm_num) ⟨19131, by rfl⟩ (by norm_num))
theorem R51021 : Reach 51021 := rs (se 3 (by rfl) ⟨9566, by rfl⟩) (B 19133 (by norm_num) ⟨9566, by rfl⟩ (by norm_num))
theorem R51025 : Reach 51025 := rs (se 2 (by rfl) ⟨19134, by rfl⟩) (B 38269 (by norm_num) ⟨19134, by rfl⟩ (by norm_num))
theorem R345941 : Reach 345941 := rs (se 9 (by rfl) ⟨1013, by rfl⟩) (B 2027 (by norm_num) ⟨1013, by rfl⟩ (by norm_num))
theorem R51029 : Reach 51029 := rs (se 9 (by rfl) ⟨149, by rfl⟩) (B 299 (by norm_num) ⟨149, by rfl⟩ (by norm_num))
theorem R51033 : Reach 51033 := rs (se 2 (by rfl) ⟨19137, by rfl⟩) (B 38275 (by norm_num) ⟨19137, by rfl⟩ (by norm_num))
theorem R51037 : Reach 51037 := rs (se 3 (by rfl) ⟨9569, by rfl⟩) (B 19139 (by norm_num) ⟨9569, by rfl⟩ (by norm_num))
theorem R51041 : Reach 51041 := rs (se 2 (by rfl) ⟨19140, by rfl⟩) (B 38281 (by norm_num) ⟨19140, by rfl⟩ (by norm_num))
theorem R51045 : Reach 51045 := rs (se 4 (by rfl) ⟨4785, by rfl⟩) (B 9571 (by norm_num) ⟨4785, by rfl⟩ (by norm_num))
theorem R51049 : Reach 51049 := rs (se 2 (by rfl) ⟨19143, by rfl⟩) (B 38287 (by norm_num) ⟨19143, by rfl⟩ (by norm_num))
theorem R83821 : Reach 83821 := rs (se 3 (by rfl) ⟨15716, by rfl⟩) (B 31433 (by norm_num) ⟨15716, by rfl⟩ (by norm_num))
theorem R51053 : Reach 51053 := rs (se 3 (by rfl) ⟨9572, by rfl⟩) (B 19145 (by norm_num) ⟨9572, by rfl⟩ (by norm_num))
theorem R51057 : Reach 51057 := rs (se 2 (by rfl) ⟨19146, by rfl⟩) (B 38293 (by norm_num) ⟨19146, by rfl⟩ (by norm_num))
theorem R51061 : Reach 51061 := rs (se 5 (by rfl) ⟨2393, by rfl⟩) (B 4787 (by norm_num) ⟨2393, by rfl⟩ (by norm_num))
theorem R51065 : Reach 51065 := rs (se 2 (by rfl) ⟨19149, by rfl⟩) (B 38299 (by norm_num) ⟨19149, by rfl⟩ (by norm_num))
theorem R51069 : Reach 51069 := rs (se 3 (by rfl) ⟨9575, by rfl⟩) (B 19151 (by norm_num) ⟨9575, by rfl⟩ (by norm_num))
theorem R51073 : Reach 51073 := rs (se 2 (by rfl) ⟨19152, by rfl⟩) (B 38305 (by norm_num) ⟨19152, by rfl⟩ (by norm_num))
theorem R51077 : Reach 51077 := rs (se 4 (by rfl) ⟨4788, by rfl⟩) (B 9577 (by norm_num) ⟨4788, by rfl⟩ (by norm_num))
theorem R51081 : Reach 51081 := rs (se 2 (by rfl) ⟨19155, by rfl⟩) (B 38311 (by norm_num) ⟨19155, by rfl⟩ (by norm_num))
theorem R51085 : Reach 51085 := rs (se 3 (by rfl) ⟨9578, by rfl⟩) (B 19157 (by norm_num) ⟨9578, by rfl⟩ (by norm_num))
theorem R51089 : Reach 51089 := rs (se 2 (by rfl) ⟨19158, by rfl⟩) (B 38317 (by norm_num) ⟨19158, by rfl⟩ (by norm_num))
theorem R51093 : Reach 51093 := rs (se 6 (by rfl) ⟨1197, by rfl⟩) (B 2395 (by norm_num) ⟨1197, by rfl⟩ (by norm_num))
theorem R51097 : Reach 51097 := rs (se 2 (by rfl) ⟨19161, by rfl⟩) (B 38323 (by norm_num) ⟨19161, by rfl⟩ (by norm_num))
theorem R51101 : Reach 51101 := rs (se 3 (by rfl) ⟨9581, by rfl⟩) (B 19163 (by norm_num) ⟨9581, by rfl⟩ (by norm_num))
theorem R51105 : Reach 51105 := rs (se 2 (by rfl) ⟨19164, by rfl⟩) (B 38329 (by norm_num) ⟨19164, by rfl⟩ (by norm_num))
theorem R51109 : Reach 51109 := rs (se 4 (by rfl) ⟨4791, by rfl⟩) (B 9583 (by norm_num) ⟨4791, by rfl⟩ (by norm_num))
theorem R51113 : Reach 51113 := rs (se 2 (by rfl) ⟨19167, by rfl⟩) (B 38335 (by norm_num) ⟨19167, by rfl⟩ (by norm_num))
theorem R51117 : Reach 51117 := rs (se 3 (by rfl) ⟨9584, by rfl⟩) (B 19169 (by norm_num) ⟨9584, by rfl⟩ (by norm_num))
theorem R83909 : Reach 83909 := rs (se 4 (by rfl) ⟨7866, by rfl⟩) (B 15733 (by norm_num) ⟨7866, by rfl⟩ (by norm_num))
theorem R215045 : Reach 215045 := rs (se 4 (by rfl) ⟨20160, by rfl⟩) (B 40321 (by norm_num) ⟨20160, by rfl⟩ (by norm_num))
theorem R51241 : Reach 51241 := rs (se 2 (by rfl) ⟨19215, by rfl⟩) (B 38431 (by norm_num) ⟨19215, by rfl⟩ (by norm_num))
theorem R84037 : Reach 84037 := rs (se 4 (by rfl) ⟨7878, by rfl⟩) (B 15757 (by norm_num) ⟨7878, by rfl⟩ (by norm_num))
theorem R182357 : Reach 182357 := rs (se 8 (by rfl) ⟨1068, by rfl⟩) (B 2137 (by norm_num) ⟨1068, by rfl⟩ (by norm_num))
theorem R51301 : Reach 51301 := rs (se 4 (by rfl) ⟨4809, by rfl⟩) (B 9619 (by norm_num) ⟨4809, by rfl⟩ (by norm_num))
theorem R84125 : Reach 84125 := rs (se 3 (by rfl) ⟨15773, by rfl⟩) (B 31547 (by norm_num) ⟨15773, by rfl⟩ (by norm_num))
theorem R248021 : Reach 248021 := rs (se 7 (by rfl) ⟨2906, by rfl⟩) (B 5813 (by norm_num) ⟨2906, by rfl⟩ (by norm_num))
theorem R84253 : Reach 84253 := rs (se 3 (by rfl) ⟨15797, by rfl⟩) (B 31595 (by norm_num) ⟨15797, by rfl⟩ (by norm_num))
theorem R182645 : Reach 182645 := rs (se 5 (by rfl) ⟨8561, by rfl⟩) (B 17123 (by norm_num) ⟨8561, by rfl⟩ (by norm_num))
theorem R84341 : Reach 84341 := rs (se 5 (by rfl) ⟨3953, by rfl⟩) (B 7907 (by norm_num) ⟨3953, by rfl⟩ (by norm_num))
theorem R51617 : Reach 51617 := rs (se 2 (by rfl) ⟨19356, by rfl⟩) (B 38713 (by norm_num) ⟨19356, by rfl⟩ (by norm_num))
theorem R84469 : Reach 84469 := rs (se 5 (by rfl) ⟨3959, by rfl⟩) (B 7919 (by norm_num) ⟨3959, by rfl⟩ (by norm_num))
theorem R51725 : Reach 51725 := rs (se 3 (by rfl) ⟨9698, by rfl⟩) (B 19397 (by norm_num) ⟨9698, by rfl⟩ (by norm_num))
theorem R51745 : Reach 51745 := rs (se 2 (by rfl) ⟨19404, by rfl⟩) (B 38809 (by norm_num) ⟨19404, by rfl⟩ (by norm_num))
theorem R84557 : Reach 84557 := rs (se 3 (by rfl) ⟨15854, by rfl⟩) (B 31709 (by norm_num) ⟨15854, by rfl⟩ (by norm_num))
theorem R117445 : Reach 117445 := rs (se 4 (by rfl) ⟨11010, by rfl⟩) (B 22021 (by norm_num) ⟨11010, by rfl⟩ (by norm_num))
theorem R84685 : Reach 84685 := rs (se 3 (by rfl) ⟨15878, by rfl⟩) (B 31757 (by norm_num) ⟨15878, by rfl⟩ (by norm_num))
theorem R84773 : Reach 84773 := rs (se 4 (by rfl) ⟨7947, by rfl⟩) (B 15895 (by norm_num) ⟨7947, by rfl⟩ (by norm_num))
theorem R52061 : Reach 52061 := rs (se 3 (by rfl) ⟨9761, by rfl⟩) (B 19523 (by norm_num) ⟨9761, by rfl⟩ (by norm_num))
theorem R84829 : Reach 84829 := rs (se 3 (by rfl) ⟨15905, by rfl⟩) (B 31811 (by norm_num) ⟨15905, by rfl⟩ (by norm_num))
theorem R52121 : Reach 52121 := rs (se 2 (by rfl) ⟨19545, by rfl⟩) (B 39091 (by norm_num) ⟨19545, by rfl⟩ (by norm_num))
theorem R84901 : Reach 84901 := rs (se 4 (by rfl) ⟨7959, by rfl⟩) (B 15919 (by norm_num) ⟨7959, by rfl⟩ (by norm_num))
theorem R84989 : Reach 84989 := rs (se 3 (by rfl) ⟨15935, by rfl⟩) (B 31871 (by norm_num) ⟨15935, by rfl⟩ (by norm_num))
theorem R52249 : Reach 52249 := rs (se 2 (by rfl) ⟨19593, by rfl⟩) (B 39187 (by norm_num) ⟨19593, by rfl⟩ (by norm_num))
theorem R52321 : Reach 52321 := rs (se 2 (by rfl) ⟨19620, by rfl⟩) (B 39241 (by norm_num) ⟨19620, by rfl⟩ (by norm_num))
theorem R85117 : Reach 85117 := rs (se 3 (by rfl) ⟨15959, by rfl⟩) (B 31919 (by norm_num) ⟨15959, by rfl⟩ (by norm_num))
theorem R85205 : Reach 85205 := rs (se 7 (by rfl) ⟨998, by rfl⟩) (B 1997 (by norm_num) ⟨998, by rfl⟩ (by norm_num))
theorem R118061 : Reach 118061 := rs (se 3 (by rfl) ⟨22136, by rfl⟩) (B 44273 (by norm_num) ⟨22136, by rfl⟩ (by norm_num))
theorem R85333 : Reach 85333 := rs (se 11 (by rfl) ⟨62, by rfl⟩) (B 125 (by norm_num) ⟨62, by rfl⟩ (by norm_num))
theorem R85421 : Reach 85421 := rs (se 3 (by rfl) ⟨16016, by rfl⟩) (B 32033 (by norm_num) ⟨16016, by rfl⟩ (by norm_num))
theorem R52693 : Reach 52693 := rs (se 7 (by rfl) ⟨617, by rfl⟩) (B 1235 (by norm_num) ⟨617, by rfl⟩ (by norm_num))
theorem R249317 : Reach 249317 := rs (se 4 (by rfl) ⟨23373, by rfl⟩) (B 46747 (by norm_num) ⟨23373, by rfl⟩ (by norm_num))
theorem R118253 : Reach 118253 := rs (se 3 (by rfl) ⟨22172, by rfl⟩) (B 44345 (by norm_num) ⟨22172, by rfl⟩ (by norm_num))
theorem R183829 : Reach 183829 := rs (se 6 (by rfl) ⟨4308, by rfl⟩) (B 8617 (by norm_num) ⟨4308, by rfl⟩ (by norm_num))
theorem R85549 : Reach 85549 := rs (se 3 (by rfl) ⟨16040, by rfl⟩) (B 32081 (by norm_num) ⟨16040, by rfl⟩ (by norm_num))
theorem R151109 : Reach 151109 := rs (se 4 (by rfl) ⟨14166, by rfl⟩) (B 28333 (by norm_num) ⟨14166, by rfl⟩ (by norm_num))
theorem R118349 : Reach 118349 := rs (se 3 (by rfl) ⟨22190, by rfl⟩) (B 44381 (by norm_num) ⟨22190, by rfl⟩ (by norm_num))
theorem R52813 : Reach 52813 := rs (se 3 (by rfl) ⟨9902, by rfl⟩) (B 19805 (by norm_num) ⟨9902, by rfl⟩ (by norm_num))
theorem R446069 : Reach 446069 := rs (se 5 (by rfl) ⟨20909, by rfl⟩) (B 41819 (by norm_num) ⟨20909, by rfl⟩ (by norm_num))
theorem R380533 : Reach 380533 := rs (se 5 (by rfl) ⟨17837, by rfl⟩) (B 35675 (by norm_num) ⟨17837, by rfl⟩ (by norm_num))
theorem R85637 : Reach 85637 := rs (se 4 (by rfl) ⟨8028, by rfl⟩) (B 16057 (by norm_num) ⟨8028, by rfl⟩ (by norm_num))
theorem R183941 : Reach 183941 := rs (se 4 (by rfl) ⟨17244, by rfl⟩) (B 34489 (by norm_num) ⟨17244, by rfl⟩ (by norm_num))
theorem R151237 : Reach 151237 := rs (se 4 (by rfl) ⟨14178, by rfl⟩) (B 28357 (by norm_num) ⟨14178, by rfl⟩ (by norm_num))
theorem R85765 : Reach 85765 := rs (se 4 (by rfl) ⟨8040, by rfl⟩) (B 16081 (by norm_num) ⟨8040, by rfl⟩ (by norm_num))
theorem R53041 : Reach 53041 := rs (se 2 (by rfl) ⟨19890, by rfl⟩) (B 39781 (by norm_num) ⟨19890, by rfl⟩ (by norm_num))
theorem R184133 : Reach 184133 := rs (se 4 (by rfl) ⟨17262, by rfl⟩) (B 34525 (by norm_num) ⟨17262, by rfl⟩ (by norm_num))
theorem R53065 : Reach 53065 := rs (se 2 (by rfl) ⟨19899, by rfl⟩) (B 39799 (by norm_num) ⟨19899, by rfl⟩ (by norm_num))
theorem R53069 : Reach 53069 := rs (se 3 (by rfl) ⟨9950, by rfl⟩) (B 19901 (by norm_num) ⟨9950, by rfl⟩ (by norm_num))
theorem R53077 : Reach 53077 := rs (se 9 (by rfl) ⟨155, by rfl⟩) (B 311 (by norm_num) ⟨155, by rfl⟩ (by norm_num))
theorem R85853 : Reach 85853 := rs (se 3 (by rfl) ⟨16097, by rfl⟩) (B 32195 (by norm_num) ⟨16097, by rfl⟩ (by norm_num))
theorem R85877 : Reach 85877 := rs (se 5 (by rfl) ⟨4025, by rfl⟩) (B 8051 (by norm_num) ⟨4025, by rfl⟩ (by norm_num))
theorem R53113 : Reach 53113 := rs (se 2 (by rfl) ⟨19917, by rfl⟩) (B 39835 (by norm_num) ⟨19917, by rfl⟩ (by norm_num))
theorem R53149 : Reach 53149 := rs (se 3 (by rfl) ⟨9965, by rfl⟩) (B 19931 (by norm_num) ⟨9965, by rfl⟩ (by norm_num))
theorem R53185 : Reach 53185 := rs (se 2 (by rfl) ⟨19944, by rfl⟩) (B 39889 (by norm_num) ⟨19944, by rfl⟩ (by norm_num))
theorem R85981 : Reach 85981 := rs (se 3 (by rfl) ⟨16121, by rfl⟩) (B 32243 (by norm_num) ⟨16121, by rfl⟩ (by norm_num))
theorem R53221 : Reach 53221 := rs (se 4 (by rfl) ⟨4989, by rfl⟩) (B 9979 (by norm_num) ⟨4989, by rfl⟩ (by norm_num))
theorem R53257 : Reach 53257 := rs (se 2 (by rfl) ⟨19971, by rfl⟩) (B 39943 (by norm_num) ⟨19971, by rfl⟩ (by norm_num))
theorem R53293 : Reach 53293 := rs (se 3 (by rfl) ⟨9992, by rfl⟩) (B 19985 (by norm_num) ⟨9992, by rfl⟩ (by norm_num))
theorem R86069 : Reach 86069 := rs (se 5 (by rfl) ⟨4034, by rfl⟩) (B 8069 (by norm_num) ⟨4034, by rfl⟩ (by norm_num))
theorem R53329 : Reach 53329 := rs (se 2 (by rfl) ⟨19998, by rfl⟩) (B 39997 (by norm_num) ⟨19998, by rfl⟩ (by norm_num))
theorem R53365 : Reach 53365 := rs (se 5 (by rfl) ⟨2501, by rfl⟩) (B 5003 (by norm_num) ⟨2501, by rfl⟩ (by norm_num))
theorem R53401 : Reach 53401 := rs (se 2 (by rfl) ⟨20025, by rfl⟩) (B 40051 (by norm_num) ⟨20025, by rfl⟩ (by norm_num))
theorem R151733 : Reach 151733 := rs (se 5 (by rfl) ⟨7112, by rfl⟩) (B 14225 (by norm_num) ⟨7112, by rfl⟩ (by norm_num))
theorem R86197 : Reach 86197 := rs (se 5 (by rfl) ⟨4040, by rfl⟩) (B 8081 (by norm_num) ⟨4040, by rfl⟩ (by norm_num))
theorem R53437 : Reach 53437 := rs (se 3 (by rfl) ⟨10019, by rfl⟩) (B 20039 (by norm_num) ⟨10019, by rfl⟩ (by norm_num))
theorem R53473 : Reach 53473 := rs (se 2 (by rfl) ⟨20052, by rfl⟩) (B 40105 (by norm_num) ⟨20052, by rfl⟩ (by norm_num))
theorem R217333 : Reach 217333 := rs (se 5 (by rfl) ⟨10187, by rfl⟩) (B 20375 (by norm_num) ⟨10187, by rfl⟩ (by norm_num))
theorem R53509 : Reach 53509 := rs (se 4 (by rfl) ⟨5016, by rfl⟩) (B 10033 (by norm_num) ⟨5016, by rfl⟩ (by norm_num))
theorem R53545 : Reach 53545 := rs (se 2 (by rfl) ⟨20079, by rfl⟩) (B 40159 (by norm_num) ⟨20079, by rfl⟩ (by norm_num))
theorem R53581 : Reach 53581 := rs (se 3 (by rfl) ⟨10046, by rfl⟩) (B 20093 (by norm_num) ⟨10046, by rfl⟩ (by norm_num))
theorem R53617 : Reach 53617 := rs (se 2 (by rfl) ⟨20106, by rfl⟩) (B 40213 (by norm_num) ⟨20106, by rfl⟩ (by norm_num))
theorem R53633 : Reach 53633 := rs (se 2 (by rfl) ⟨20112, by rfl⟩) (B 40225 (by norm_num) ⟨20112, by rfl⟩ (by norm_num))
theorem R53653 : Reach 53653 := rs (se 6 (by rfl) ⟨1257, by rfl⟩) (B 2515 (by norm_num) ⟨1257, by rfl⟩ (by norm_num))
theorem R348565 : Reach 348565 := rs (se 6 (by rfl) ⟨8169, by rfl⟩) (B 16339 (by norm_num) ⟨8169, by rfl⟩ (by norm_num))
theorem R53689 : Reach 53689 := rs (se 2 (by rfl) ⟨20133, by rfl⟩) (B 40267 (by norm_num) ⟨20133, by rfl⟩ (by norm_num))
theorem R53725 : Reach 53725 := rs (se 3 (by rfl) ⟨10073, by rfl⟩) (B 20147 (by norm_num) ⟨10073, by rfl⟩ (by norm_num))
theorem R53761 : Reach 53761 := rs (se 2 (by rfl) ⟨20160, by rfl⟩) (B 40321 (by norm_num) ⟨20160, by rfl⟩ (by norm_num))
theorem R119333 : Reach 119333 := rs (se 4 (by rfl) ⟨11187, by rfl⟩) (B 22375 (by norm_num) ⟨11187, by rfl⟩ (by norm_num))
theorem R53797 : Reach 53797 := rs (se 4 (by rfl) ⟨5043, by rfl⟩) (B 10087 (by norm_num) ⟨5043, by rfl⟩ (by norm_num))
theorem R348725 : Reach 348725 := rs (se 5 (by rfl) ⟨16346, by rfl⟩) (B 32693 (by norm_num) ⟨16346, by rfl⟩ (by norm_num))
theorem R53821 : Reach 53821 := rs (se 3 (by rfl) ⟨10091, by rfl⟩) (B 20183 (by norm_num) ⟨10091, by rfl⟩ (by norm_num))
theorem R53833 : Reach 53833 := rs (se 2 (by rfl) ⟨20187, by rfl⟩) (B 40375 (by norm_num) ⟨20187, by rfl⟩ (by norm_num))
theorem R53869 : Reach 53869 := rs (se 3 (by rfl) ⟨10100, by rfl⟩) (B 20201 (by norm_num) ⟨10100, by rfl⟩ (by norm_num))
theorem R53905 : Reach 53905 := rs (se 2 (by rfl) ⟨20214, by rfl⟩) (B 40429 (by norm_num) ⟨20214, by rfl⟩ (by norm_num))
theorem R53941 : Reach 53941 := rs (se 5 (by rfl) ⟨2528, by rfl⟩) (B 5057 (by norm_num) ⟨2528, by rfl⟩ (by norm_num))
theorem R53977 : Reach 53977 := rs (se 2 (by rfl) ⟨20241, by rfl⟩) (B 40483 (by norm_num) ⟨20241, by rfl⟩ (by norm_num))
theorem R53989 : Reach 53989 := rs (se 4 (by rfl) ⟨5061, by rfl⟩) (B 10123 (by norm_num) ⟨5061, by rfl⟩ (by norm_num))
theorem R152293 : Reach 152293 := rs (se 4 (by rfl) ⟨14277, by rfl⟩) (B 28555 (by norm_num) ⟨14277, by rfl⟩ (by norm_num))
theorem R250613 : Reach 250613 := rs (se 5 (by rfl) ⟨11747, by rfl⟩) (B 23495 (by norm_num) ⟨11747, by rfl⟩ (by norm_num))
theorem R54013 : Reach 54013 := rs (se 3 (by rfl) ⟨10127, by rfl⟩) (B 20255 (by norm_num) ⟨10127, by rfl⟩ (by norm_num))
theorem R54049 : Reach 54049 := rs (se 2 (by rfl) ⟨20268, by rfl⟩) (B 40537 (by norm_num) ⟨20268, by rfl⟩ (by norm_num))
theorem R283445 : Reach 283445 := rs (se 5 (by rfl) ⟨13286, by rfl⟩) (B 26573 (by norm_num) ⟨13286, by rfl⟩ (by norm_num))
theorem R86845 : Reach 86845 := rs (se 3 (by rfl) ⟨16283, by rfl⟩) (B 32567 (by norm_num) ⟨16283, by rfl⟩ (by norm_num))
theorem R54085 : Reach 54085 := rs (se 4 (by rfl) ⟨5070, by rfl⟩) (B 10141 (by norm_num) ⟨5070, by rfl⟩ (by norm_num))
theorem R54121 : Reach 54121 := rs (se 2 (by rfl) ⟨20295, by rfl⟩) (B 40591 (by norm_num) ⟨20295, by rfl⟩ (by norm_num))
theorem R119677 : Reach 119677 := rs (se 3 (by rfl) ⟨22439, by rfl⟩) (B 44879 (by norm_num) ⟨22439, by rfl⟩ (by norm_num))
theorem R54157 : Reach 54157 := rs (se 3 (by rfl) ⟨10154, by rfl⟩) (B 20309 (by norm_num) ⟨10154, by rfl⟩ (by norm_num))
theorem R54193 : Reach 54193 := rs (se 2 (by rfl) ⟨20322, by rfl⟩) (B 40645 (by norm_num) ⟨20322, by rfl⟩ (by norm_num))
theorem R349109 : Reach 349109 := rs (se 5 (by rfl) ⟨16364, by rfl⟩) (B 32729 (by norm_num) ⟨16364, by rfl⟩ (by norm_num))
theorem R54229 : Reach 54229 := rs (se 7 (by rfl) ⟨635, by rfl⟩) (B 1271 (by norm_num) ⟨635, by rfl⟩ (by norm_num))
theorem R807893 : Reach 807893 := rs (se 7 (by rfl) ⟨9467, by rfl⟩) (B 18935 (by norm_num) ⟨9467, by rfl⟩ (by norm_num))
theorem R119789 : Reach 119789 := rs (se 3 (by rfl) ⟨22460, by rfl⟩) (B 44921 (by norm_num) ⟨22460, by rfl⟩ (by norm_num))
theorem R54265 : Reach 54265 := rs (se 2 (by rfl) ⟨20349, by rfl⟩) (B 40699 (by norm_num) ⟨20349, by rfl⟩ (by norm_num))
theorem R54301 : Reach 54301 := rs (se 3 (by rfl) ⟨10181, by rfl⟩) (B 20363 (by norm_num) ⟨10181, by rfl⟩ (by norm_num))
theorem R54337 : Reach 54337 := rs (se 2 (by rfl) ⟨20376, by rfl⟩) (B 40753 (by norm_num) ⟨20376, by rfl⟩ (by norm_num))
theorem R54373 : Reach 54373 := rs (se 4 (by rfl) ⟨5097, by rfl⟩) (B 10195 (by norm_num) ⟨5097, by rfl⟩ (by norm_num))
theorem R54409 : Reach 54409 := rs (se 2 (by rfl) ⟨20403, by rfl⟩) (B 40807 (by norm_num) ⟨20403, by rfl⟩ (by norm_num))
theorem R119981 : Reach 119981 := rs (se 3 (by rfl) ⟨22496, by rfl⟩) (B 44993 (by norm_num) ⟨22496, by rfl⟩ (by norm_num))
theorem R54445 : Reach 54445 := rs (se 3 (by rfl) ⟨10208, by rfl⟩) (B 20417 (by norm_num) ⟨10208, by rfl⟩ (by norm_num))
theorem R54481 : Reach 54481 := rs (se 2 (by rfl) ⟨20430, by rfl⟩) (B 40861 (by norm_num) ⟨20430, by rfl⟩ (by norm_num))
theorem R54517 : Reach 54517 := rs (se 5 (by rfl) ⟨2555, by rfl⟩) (B 5111 (by norm_num) ⟨2555, by rfl⟩ (by norm_num))
theorem R54553 : Reach 54553 := rs (se 2 (by rfl) ⟨20457, by rfl⟩) (B 40915 (by norm_num) ⟨20457, by rfl⟩ (by norm_num))
theorem R54589 : Reach 54589 := rs (se 3 (by rfl) ⟨10235, by rfl⟩) (B 20471 (by norm_num) ⟨10235, by rfl⟩ (by norm_num))
theorem R54625 : Reach 54625 := rs (se 2 (by rfl) ⟨20484, by rfl⟩) (B 40969 (by norm_num) ⟨20484, by rfl⟩ (by norm_num))
theorem R87421 : Reach 87421 := rs (se 3 (by rfl) ⟨16391, by rfl⟩) (B 32783 (by norm_num) ⟨16391, by rfl⟩ (by norm_num))
theorem R54661 : Reach 54661 := rs (se 4 (by rfl) ⟨5124, by rfl⟩) (B 10249 (by norm_num) ⟨5124, by rfl⟩ (by norm_num))
theorem R54697 : Reach 54697 := rs (se 2 (by rfl) ⟨20511, by rfl⟩) (B 41023 (by norm_num) ⟨20511, by rfl⟩ (by norm_num))
theorem R87493 : Reach 87493 := rs (se 4 (by rfl) ⟨8202, by rfl⟩) (B 16405 (by norm_num) ⟨8202, by rfl⟩ (by norm_num))
theorem R54733 : Reach 54733 := rs (se 3 (by rfl) ⟨10262, by rfl⟩) (B 20525 (by norm_num) ⟨10262, by rfl⟩ (by norm_num))
theorem R54737 : Reach 54737 := rs (se 2 (by rfl) ⟨20526, by rfl⟩) (B 41053 (by norm_num) ⟨20526, by rfl⟩ (by norm_num))
theorem R54769 : Reach 54769 := rs (se 2 (by rfl) ⟨20538, by rfl⟩) (B 41077 (by norm_num) ⟨20538, by rfl⟩ (by norm_num))
theorem R120325 : Reach 120325 := rs (se 4 (by rfl) ⟨11280, by rfl⟩) (B 22561 (by norm_num) ⟨11280, by rfl⟩ (by norm_num))
theorem R54805 : Reach 54805 := rs (se 6 (by rfl) ⟨1284, by rfl⟩) (B 2569 (by norm_num) ⟨1284, by rfl⟩ (by norm_num))
theorem R54841 : Reach 54841 := rs (se 2 (by rfl) ⟨20565, by rfl⟩) (B 41131 (by norm_num) ⟨20565, by rfl⟩ (by norm_num))
theorem R54877 : Reach 54877 := rs (se 3 (by rfl) ⟨10289, by rfl⟩) (B 20579 (by norm_num) ⟨10289, by rfl⟩ (by norm_num))
theorem R120437 : Reach 120437 := rs (se 5 (by rfl) ⟨5645, by rfl⟩) (B 11291 (by norm_num) ⟨5645, by rfl⟩ (by norm_num))
theorem R54913 : Reach 54913 := rs (se 2 (by rfl) ⟨20592, by rfl⟩) (B 41185 (by norm_num) ⟨20592, by rfl⟩ (by norm_num))
theorem R54949 : Reach 54949 := rs (se 4 (by rfl) ⟨5151, by rfl⟩) (B 10303 (by norm_num) ⟨5151, by rfl⟩ (by norm_num))
theorem R54985 : Reach 54985 := rs (se 2 (by rfl) ⟨20619, by rfl⟩) (B 41239 (by norm_num) ⟨20619, by rfl⟩ (by norm_num))
theorem R55021 : Reach 55021 := rs (se 3 (by rfl) ⟨10316, by rfl⟩) (B 20633 (by norm_num) ⟨10316, by rfl⟩ (by norm_num))
theorem R55057 : Reach 55057 := rs (se 2 (by rfl) ⟨20646, by rfl⟩) (B 41293 (by norm_num) ⟨20646, by rfl⟩ (by norm_num))
theorem R120629 : Reach 120629 := rs (se 5 (by rfl) ⟨5654, by rfl⟩) (B 11309 (by norm_num) ⟨5654, by rfl⟩ (by norm_num))
theorem R55093 : Reach 55093 := rs (se 5 (by rfl) ⟨2582, by rfl⟩) (B 5165 (by norm_num) ⟨2582, by rfl⟩ (by norm_num))
theorem R55129 : Reach 55129 := rs (se 2 (by rfl) ⟨20673, by rfl⟩) (B 41347 (by norm_num) ⟨20673, by rfl⟩ (by norm_num))
theorem R55165 : Reach 55165 := rs (se 3 (by rfl) ⟨10343, by rfl⟩) (B 20687 (by norm_num) ⟨10343, by rfl⟩ (by norm_num))
theorem R186245 : Reach 186245 := rs (se 4 (by rfl) ⟨17460, by rfl⟩) (B 34921 (by norm_num) ⟨17460, by rfl⟩ (by norm_num))
theorem R55201 : Reach 55201 := rs (se 2 (by rfl) ⟨20700, by rfl⟩) (B 41401 (by norm_num) ⟨20700, by rfl⟩ (by norm_num))
theorem R55237 : Reach 55237 := rs (se 4 (by rfl) ⟨5178, by rfl⟩) (B 10357 (by norm_num) ⟨5178, by rfl⟩ (by norm_num))
theorem R120781 : Reach 120781 := rs (se 3 (by rfl) ⟨22646, by rfl⟩) (B 45293 (by norm_num) ⟨22646, by rfl⟩ (by norm_num))
theorem R55273 : Reach 55273 := rs (se 2 (by rfl) ⟨20727, by rfl⟩) (B 41455 (by norm_num) ⟨20727, by rfl⟩ (by norm_num))
theorem R55309 : Reach 55309 := rs (se 3 (by rfl) ⟨10370, by rfl⟩) (B 20741 (by norm_num) ⟨10370, by rfl⟩ (by norm_num))
theorem R55337 : Reach 55337 := rs (se 2 (by rfl) ⟨20751, by rfl⟩) (B 41503 (by norm_num) ⟨20751, by rfl⟩ (by norm_num))
theorem R55345 : Reach 55345 := rs (se 2 (by rfl) ⟨20754, by rfl⟩) (B 41509 (by norm_num) ⟨20754, by rfl⟩ (by norm_num))
theorem R55381 : Reach 55381 := rs (se 8 (by rfl) ⟨324, by rfl⟩) (B 649 (by norm_num) ⟨324, by rfl⟩ (by norm_num))
theorem R55417 : Reach 55417 := rs (se 2 (by rfl) ⟨20781, by rfl⟩) (B 41563 (by norm_num) ⟨20781, by rfl⟩ (by norm_num))
theorem R120973 : Reach 120973 := rs (se 3 (by rfl) ⟨22682, by rfl⟩) (B 45365 (by norm_num) ⟨22682, by rfl⟩ (by norm_num))
theorem R55453 : Reach 55453 := rs (se 3 (by rfl) ⟨10397, by rfl⟩) (B 20795 (by norm_num) ⟨10397, by rfl⟩ (by norm_num))
theorem R88229 : Reach 88229 := rs (se 4 (by rfl) ⟨8271, by rfl⟩) (B 16543 (by norm_num) ⟨8271, by rfl⟩ (by norm_num))
theorem R186533 : Reach 186533 := rs (se 4 (by rfl) ⟨17487, by rfl⟩) (B 34975 (by norm_num) ⟨17487, by rfl⟩ (by norm_num))
theorem R55489 : Reach 55489 := rs (se 2 (by rfl) ⟨20808, by rfl⟩) (B 41617 (by norm_num) ⟨20808, by rfl⟩ (by norm_num))
theorem R55525 : Reach 55525 := rs (se 4 (by rfl) ⟨5205, by rfl⟩) (B 10411 (by norm_num) ⟨5205, by rfl⟩ (by norm_num))
theorem R121085 : Reach 121085 := rs (se 3 (by rfl) ⟨22703, by rfl⟩) (B 45407 (by norm_num) ⟨22703, by rfl⟩ (by norm_num))
theorem R55561 : Reach 55561 := rs (se 2 (by rfl) ⟨20835, by rfl⟩) (B 41671 (by norm_num) ⟨20835, by rfl⟩ (by norm_num))
theorem R121117 : Reach 121117 := rs (se 3 (by rfl) ⟨22709, by rfl⟩) (B 45419 (by norm_num) ⟨22709, by rfl⟩ (by norm_num))
theorem R55597 : Reach 55597 := rs (se 3 (by rfl) ⟨10424, by rfl⟩) (B 20849 (by norm_num) ⟨10424, by rfl⟩ (by norm_num))
theorem R55633 : Reach 55633 := rs (se 2 (by rfl) ⟨20862, by rfl⟩) (B 41725 (by norm_num) ⟨20862, by rfl⟩ (by norm_num))
theorem R55669 : Reach 55669 := rs (se 5 (by rfl) ⟨2609, by rfl⟩) (B 5219 (by norm_num) ⟨2609, by rfl⟩ (by norm_num))
theorem R55705 : Reach 55705 := rs (se 2 (by rfl) ⟨20889, by rfl⟩) (B 41779 (by norm_num) ⟨20889, by rfl⟩ (by norm_num))
theorem R252341 : Reach 252341 := rs (se 5 (by rfl) ⟨11828, by rfl⟩) (B 23657 (by norm_num) ⟨11828, by rfl⟩ (by norm_num))
theorem R55741 : Reach 55741 := rs (se 3 (by rfl) ⟨10451, by rfl⟩) (B 20903 (by norm_num) ⟨10451, by rfl⟩ (by norm_num))
theorem R121277 : Reach 121277 := rs (se 3 (by rfl) ⟨22739, by rfl⟩) (B 45479 (by norm_num) ⟨22739, by rfl⟩ (by norm_num))
theorem R55777 : Reach 55777 := rs (se 2 (by rfl) ⟨20916, by rfl⟩) (B 41833 (by norm_num) ⟨20916, by rfl⟩ (by norm_num))
theorem R55813 : Reach 55813 := rs (se 4 (by rfl) ⟨5232, by rfl⟩) (B 10465 (by norm_num) ⟨5232, by rfl⟩ (by norm_num))
theorem R154133 : Reach 154133 := rs (se 6 (by rfl) ⟨3612, by rfl⟩) (B 7225 (by norm_num) ⟨3612, by rfl⟩ (by norm_num))
theorem R55849 : Reach 55849 := rs (se 2 (by rfl) ⟨20943, by rfl⟩) (B 41887 (by norm_num) ⟨20943, by rfl⟩ (by norm_num))
theorem R318005 : Reach 318005 := rs (se 5 (by rfl) ⟨14906, by rfl⟩) (B 29813 (by norm_num) ⟨14906, by rfl⟩ (by norm_num))
theorem R55885 : Reach 55885 := rs (se 3 (by rfl) ⟨10478, by rfl⟩) (B 20957 (by norm_num) ⟨10478, by rfl⟩ (by norm_num))
theorem R88661 : Reach 88661 := rs (se 8 (by rfl) ⟨519, by rfl⟩) (B 1039 (by norm_num) ⟨519, by rfl⟩ (by norm_num))
theorem R55921 : Reach 55921 := rs (se 2 (by rfl) ⟨20970, by rfl⟩) (B 41941 (by norm_num) ⟨20970, by rfl⟩ (by norm_num))
theorem R350837 : Reach 350837 := rs (se 5 (by rfl) ⟨16445, by rfl⟩) (B 32891 (by norm_num) ⟨16445, by rfl⟩ (by norm_num))
theorem R55957 : Reach 55957 := rs (se 6 (by rfl) ⟨1311, by rfl⟩) (B 2623 (by norm_num) ⟨1311, by rfl⟩ (by norm_num))
theorem R55993 : Reach 55993 := rs (se 2 (by rfl) ⟨20997, by rfl⟩) (B 41995 (by norm_num) ⟨20997, by rfl⟩ (by norm_num))
theorem R56029 : Reach 56029 := rs (se 3 (by rfl) ⟨10505, by rfl⟩) (B 21011 (by norm_num) ⟨10505, by rfl⟩ (by norm_num))
theorem R88805 : Reach 88805 := rs (se 4 (by rfl) ⟨8325, by rfl⟩) (B 16651 (by norm_num) ⟨8325, by rfl⟩ (by norm_num))
theorem R56065 : Reach 56065 := rs (se 2 (by rfl) ⟨21024, by rfl⟩) (B 42049 (by norm_num) ⟨21024, by rfl⟩ (by norm_num))
theorem R121621 : Reach 121621 := rs (se 6 (by rfl) ⟨2850, by rfl⟩) (B 5701 (by norm_num) ⟨2850, by rfl⟩ (by norm_num))
theorem R56101 : Reach 56101 := rs (se 4 (by rfl) ⟨5259, by rfl⟩) (B 10519 (by norm_num) ⟨5259, by rfl⟩ (by norm_num))
theorem R56137 : Reach 56137 := rs (se 2 (by rfl) ⟨21051, by rfl⟩) (B 42103 (by norm_num) ⟨21051, by rfl⟩ (by norm_num))
theorem R56173 : Reach 56173 := rs (se 3 (by rfl) ⟨10532, by rfl⟩) (B 21065 (by norm_num) ⟨10532, by rfl⟩ (by norm_num))
theorem R121733 : Reach 121733 := rs (se 4 (by rfl) ⟨11412, by rfl⟩) (B 22825 (by norm_num) ⟨11412, by rfl⟩ (by norm_num))
theorem R56209 : Reach 56209 := rs (se 2 (by rfl) ⟨21078, by rfl⟩) (B 42157 (by norm_num) ⟨21078, by rfl⟩ (by norm_num))
theorem R56245 : Reach 56245 := rs (se 5 (by rfl) ⟨2636, by rfl⟩) (B 5273 (by norm_num) ⟨2636, by rfl⟩ (by norm_num))
theorem R89029 : Reach 89029 := rs (se 4 (by rfl) ⟨8346, by rfl⟩) (B 16693 (by norm_num) ⟨8346, by rfl⟩ (by norm_num))
theorem R220117 : Reach 220117 := rs (se 7 (by rfl) ⟨2579, by rfl⟩) (B 5159 (by norm_num) ⟨2579, by rfl⟩ (by norm_num))
theorem R56281 : Reach 56281 := rs (se 2 (by rfl) ⟨21105, by rfl⟩) (B 42211 (by norm_num) ⟨21105, by rfl⟩ (by norm_num))
theorem R56317 : Reach 56317 := rs (se 3 (by rfl) ⟨10559, by rfl⟩) (B 21119 (by norm_num) ⟨10559, by rfl⟩ (by norm_num))
theorem R56353 : Reach 56353 := rs (se 2 (by rfl) ⟨21132, by rfl⟩) (B 42265 (by norm_num) ⟨21132, by rfl⟩ (by norm_num))
theorem R121925 : Reach 121925 := rs (se 4 (by rfl) ⟨11430, by rfl⟩) (B 22861 (by norm_num) ⟨11430, by rfl⟩ (by norm_num))
theorem R56389 : Reach 56389 := rs (se 4 (by rfl) ⟨5286, by rfl⟩) (B 10573 (by norm_num) ⟨5286, by rfl⟩ (by norm_num))
theorem R56425 : Reach 56425 := rs (se 2 (by rfl) ⟨21159, by rfl⟩) (B 42319 (by norm_num) ⟨21159, by rfl⟩ (by norm_num))
theorem R56461 : Reach 56461 := rs (se 3 (by rfl) ⟨10586, by rfl⟩) (B 21173 (by norm_num) ⟨10586, by rfl⟩ (by norm_num))
theorem R56497 : Reach 56497 := rs (se 2 (by rfl) ⟨21186, by rfl⟩) (B 42373 (by norm_num) ⟨21186, by rfl⟩ (by norm_num))
theorem R56533 : Reach 56533 := rs (se 7 (by rfl) ⟨662, by rfl⟩) (B 1325 (by norm_num) ⟨662, by rfl⟩ (by norm_num))
theorem R56569 : Reach 56569 := rs (se 2 (by rfl) ⟨21213, by rfl⟩) (B 42427 (by norm_num) ⟨21213, by rfl⟩ (by norm_num))
theorem R253205 : Reach 253205 := rs (se 6 (by rfl) ⟨5934, by rfl⟩) (B 11869 (by norm_num) ⟨5934, by rfl⟩ (by norm_num))
theorem R56605 : Reach 56605 := rs (se 3 (by rfl) ⟨10613, by rfl⟩) (B 21227 (by norm_num) ⟨10613, by rfl⟩ (by norm_num))
theorem R89381 : Reach 89381 := rs (se 4 (by rfl) ⟨8379, by rfl⟩) (B 16759 (by norm_num) ⟨8379, by rfl⟩ (by norm_num))
theorem R122165 : Reach 122165 := rs (se 5 (by rfl) ⟨5726, by rfl⟩) (B 11453 (by norm_num) ⟨5726, by rfl⟩ (by norm_num))
theorem R56641 : Reach 56641 := rs (se 2 (by rfl) ⟨21240, by rfl⟩) (B 42481 (by norm_num) ⟨21240, by rfl⟩ (by norm_num))
theorem R187717 : Reach 187717 := rs (se 4 (by rfl) ⟨17598, by rfl⟩) (B 35197 (by norm_num) ⟨17598, by rfl⟩ (by norm_num))
theorem R56677 : Reach 56677 := rs (se 4 (by rfl) ⟨5313, by rfl⟩) (B 10627 (by norm_num) ⟨5313, by rfl⟩ (by norm_num))
theorem R56713 : Reach 56713 := rs (se 2 (by rfl) ⟨21267, by rfl⟩) (B 42535 (by norm_num) ⟨21267, by rfl⟩ (by norm_num))
theorem R122269 : Reach 122269 := rs (se 3 (by rfl) ⟨22925, by rfl⟩) (B 45851 (by norm_num) ⟨22925, by rfl⟩ (by norm_num))
theorem R56749 : Reach 56749 := rs (se 3 (by rfl) ⟨10640, by rfl⟩) (B 21281 (by norm_num) ⟨10640, by rfl⟩ (by norm_num))
theorem R56785 : Reach 56785 := rs (se 2 (by rfl) ⟨21294, by rfl⟩) (B 42589 (by norm_num) ⟨21294, by rfl⟩ (by norm_num))
theorem R56813 : Reach 56813 := rs (se 3 (by rfl) ⟨10652, by rfl⟩) (B 21305 (by norm_num) ⟨10652, by rfl⟩ (by norm_num))
theorem R56821 : Reach 56821 := rs (se 5 (by rfl) ⟨2663, by rfl⟩) (B 5327 (by norm_num) ⟨2663, by rfl⟩ (by norm_num))
theorem R155141 : Reach 155141 := rs (se 4 (by rfl) ⟨14544, by rfl⟩) (B 29089 (by norm_num) ⟨14544, by rfl⟩ (by norm_num))
theorem R122381 : Reach 122381 := rs (se 3 (by rfl) ⟨22946, by rfl⟩) (B 45893 (by norm_num) ⟨22946, by rfl⟩ (by norm_num))
theorem R56857 : Reach 56857 := rs (se 2 (by rfl) ⟨21321, by rfl⟩) (B 42643 (by norm_num) ⟨21321, by rfl⟩ (by norm_num))
theorem R56893 : Reach 56893 := rs (se 3 (by rfl) ⟨10667, by rfl⟩) (B 21335 (by norm_num) ⟨10667, by rfl⟩ (by norm_num))
theorem R56909 : Reach 56909 := rs (se 3 (by rfl) ⟨10670, by rfl⟩) (B 21341 (by norm_num) ⟨10670, by rfl⟩ (by norm_num))
theorem R56929 : Reach 56929 := rs (se 2 (by rfl) ⟨21348, by rfl⟩) (B 42697 (by norm_num) ⟨21348, by rfl⟩ (by norm_num))
theorem R188021 : Reach 188021 := rs (se 5 (by rfl) ⟨8813, by rfl⟩) (B 17627 (by norm_num) ⟨8813, by rfl⟩ (by norm_num))
theorem R56965 : Reach 56965 := rs (se 4 (by rfl) ⟨5340, by rfl⟩) (B 10681 (by norm_num) ⟨5340, by rfl⟩ (by norm_num))
theorem R57001 : Reach 57001 := rs (se 2 (by rfl) ⟨21375, by rfl⟩) (B 42751 (by norm_num) ⟨21375, by rfl⟩ (by norm_num))
theorem R122573 : Reach 122573 := rs (se 3 (by rfl) ⟨22982, by rfl⟩) (B 45965 (by norm_num) ⟨22982, by rfl⟩ (by norm_num))
theorem R57037 : Reach 57037 := rs (se 3 (by rfl) ⟨10694, by rfl⟩) (B 21389 (by norm_num) ⟨10694, by rfl⟩ (by norm_num))
theorem R57073 : Reach 57073 := rs (se 2 (by rfl) ⟨21402, by rfl⟩) (B 42805 (by norm_num) ⟨21402, by rfl⟩ (by norm_num))
theorem R351989 : Reach 351989 := rs (se 5 (by rfl) ⟨16499, by rfl⟩) (B 32999 (by norm_num) ⟨16499, by rfl⟩ (by norm_num))
theorem R57109 : Reach 57109 := rs (se 6 (by rfl) ⟨1338, by rfl⟩) (B 2677 (by norm_num) ⟨1338, by rfl⟩ (by norm_num))
theorem R384821 : Reach 384821 := rs (se 5 (by rfl) ⟨18038, by rfl⟩) (B 36077 (by norm_num) ⟨18038, by rfl⟩ (by norm_num))
theorem R57145 : Reach 57145 := rs (se 2 (by rfl) ⟨21429, by rfl⟩) (B 42859 (by norm_num) ⟨21429, by rfl⟩ (by norm_num))
theorem R57181 : Reach 57181 := rs (se 3 (by rfl) ⟨10721, by rfl⟩) (B 21443 (by norm_num) ⟨10721, by rfl⟩ (by norm_num))
theorem R57217 : Reach 57217 := rs (se 2 (by rfl) ⟨21456, by rfl⟩) (B 42913 (by norm_num) ⟨21456, by rfl⟩ (by norm_num))
theorem R57253 : Reach 57253 := rs (se 4 (by rfl) ⟨5367, by rfl⟩) (B 10735 (by norm_num) ⟨5367, by rfl⟩ (by norm_num))
theorem R122789 : Reach 122789 := rs (se 4 (by rfl) ⟨11511, by rfl⟩) (B 23023 (by norm_num) ⟨11511, by rfl⟩ (by norm_num))
theorem R57289 : Reach 57289 := rs (se 2 (by rfl) ⟨21483, by rfl⟩) (B 42967 (by norm_num) ⟨21483, by rfl⟩ (by norm_num))
theorem R90085 : Reach 90085 := rs (se 4 (by rfl) ⟨8445, by rfl⟩) (B 16891 (by norm_num) ⟨8445, by rfl⟩ (by norm_num))
theorem R57325 : Reach 57325 := rs (se 3 (by rfl) ⟨10748, by rfl⟩) (B 21497 (by norm_num) ⟨10748, by rfl⟩ (by norm_num))
theorem R57361 : Reach 57361 := rs (se 2 (by rfl) ⟨21510, by rfl⟩) (B 43021 (by norm_num) ⟨21510, by rfl⟩ (by norm_num))
theorem R122917 : Reach 122917 := rs (se 4 (by rfl) ⟨11523, by rfl⟩) (B 23047 (by norm_num) ⟨11523, by rfl⟩ (by norm_num))
theorem R57397 : Reach 57397 := rs (se 5 (by rfl) ⟨2690, by rfl⟩) (B 5381 (by norm_num) ⟨2690, by rfl⟩ (by norm_num))
theorem R680021 : Reach 680021 := rs (se 8 (by rfl) ⟨3984, by rfl⟩) (B 7969 (by norm_num) ⟨3984, by rfl⟩ (by norm_num))
theorem R57433 : Reach 57433 := rs (se 2 (by rfl) ⟨21537, by rfl⟩) (B 43075 (by norm_num) ⟨21537, by rfl⟩ (by norm_num))
theorem R90229 : Reach 90229 := rs (se 5 (by rfl) ⟨4229, by rfl⟩) (B 8459 (by norm_num) ⟨4229, by rfl⟩ (by norm_num))
theorem R57469 : Reach 57469 := rs (se 3 (by rfl) ⟨10775, by rfl⟩) (B 21551 (by norm_num) ⟨10775, by rfl⟩ (by norm_num))
theorem R123029 : Reach 123029 := rs (se 6 (by rfl) ⟨2883, by rfl⟩) (B 5767 (by norm_num) ⟨2883, by rfl⟩ (by norm_num))
theorem R57505 : Reach 57505 := rs (se 2 (by rfl) ⟨21564, by rfl⟩) (B 43129 (by norm_num) ⟨21564, by rfl⟩ (by norm_num))
theorem R90389 : Reach 90389 := rs (se 6 (by rfl) ⟨2118, by rfl⟩) (B 4237 (by norm_num) ⟨2118, by rfl⟩ (by norm_num))
theorem R123221 : Reach 123221 := rs (se 10 (by rfl) ⟨180, by rfl⟩) (B 361 (by norm_num) ⟨180, by rfl⟩ (by norm_num))
theorem R385397 : Reach 385397 := rs (se 5 (by rfl) ⟨18065, by rfl⟩) (B 36131 (by norm_num) ⟨18065, by rfl⟩ (by norm_num))
theorem R844181 : Reach 844181 := rs (se 6 (by rfl) ⟨19785, by rfl⟩) (B 39571 (by norm_num) ⟨19785, by rfl⟩ (by norm_num))
theorem R90533 : Reach 90533 := rs (se 4 (by rfl) ⟨8487, by rfl⟩) (B 16975 (by norm_num) ⟨8487, by rfl⟩ (by norm_num))
theorem R57781 : Reach 57781 := rs (se 5 (by rfl) ⟨2708, by rfl⟩) (B 5417 (by norm_num) ⟨2708, by rfl⟩ (by norm_num))
theorem R57853 : Reach 57853 := rs (se 3 (by rfl) ⟨10847, by rfl⟩) (B 21695 (by norm_num) ⟨10847, by rfl⟩ (by norm_num))
theorem R156325 : Reach 156325 := rs (se 4 (by rfl) ⟨14655, by rfl⟩) (B 29311 (by norm_num) ⟨14655, by rfl⟩ (by norm_num))
theorem R123565 : Reach 123565 := rs (se 3 (by rfl) ⟨23168, by rfl⟩) (B 46337 (by norm_num) ⟨23168, by rfl⟩ (by norm_num))
theorem R90821 : Reach 90821 := rs (se 4 (by rfl) ⟨8514, by rfl⟩) (B 17029 (by norm_num) ⟨8514, by rfl⟩ (by norm_num))
theorem R58141 : Reach 58141 := rs (se 3 (by rfl) ⟨10901, by rfl⟩) (B 21803 (by norm_num) ⟨10901, by rfl⟩ (by norm_num))
theorem R123677 : Reach 123677 := rs (se 3 (by rfl) ⟨23189, by rfl⟩) (B 46379 (by norm_num) ⟨23189, by rfl⟩ (by norm_num))
theorem R90973 : Reach 90973 := rs (se 3 (by rfl) ⟨17057, by rfl⟩) (B 34115 (by norm_num) ⟨17057, by rfl⟩ (by norm_num))
theorem R123869 : Reach 123869 := rs (se 3 (by rfl) ⟨23225, by rfl⟩) (B 46451 (by norm_num) ⟨23225, by rfl⟩ (by norm_num))
theorem R91277 : Reach 91277 := rs (se 3 (by rfl) ⟨17114, by rfl⟩) (B 34229 (by norm_num) ⟨17114, by rfl⟩ (by norm_num))
theorem R124213 : Reach 124213 := rs (se 5 (by rfl) ⟨5822, by rfl⟩) (B 11645 (by norm_num) ⟨5822, by rfl⟩ (by norm_num))
theorem R681365 : Reach 681365 := rs (se 6 (by rfl) ⟨15969, by rfl⟩) (B 31939 (by norm_num) ⟨15969, by rfl⟩ (by norm_num))
theorem R124325 : Reach 124325 := rs (se 4 (by rfl) ⟨11655, by rfl⟩) (B 23311 (by norm_num) ⟨11655, by rfl⟩ (by norm_num))
theorem R58853 : Reach 58853 := rs (se 4 (by rfl) ⟨5517, by rfl⟩) (B 11035 (by norm_num) ⟨5517, by rfl⟩ (by norm_num))
theorem R157157 : Reach 157157 := rs (se 4 (by rfl) ⟨14733, by rfl⟩) (B 29467 (by norm_num) ⟨14733, by rfl⟩ (by norm_num))
theorem R124517 : Reach 124517 := rs (se 4 (by rfl) ⟨11673, by rfl⟩) (B 23347 (by norm_num) ⟨11673, by rfl⟩ (by norm_num))
theorem R190133 : Reach 190133 := rs (se 5 (by rfl) ⟨8912, by rfl⟩) (B 17825 (by norm_num) ⟨8912, by rfl⟩ (by norm_num))
theorem R517909 : Reach 517909 := rs (se 6 (by rfl) ⟨12138, by rfl⟩) (B 24277 (by norm_num) ⟨12138, by rfl⟩ (by norm_num))
theorem R255797 : Reach 255797 := rs (se 5 (by rfl) ⟨11990, by rfl⟩) (B 23981 (by norm_num) ⟨11990, by rfl⟩ (by norm_num))
theorem R92029 : Reach 92029 := rs (se 3 (by rfl) ⟨17255, by rfl⟩) (B 34511 (by norm_num) ⟨17255, by rfl⟩ (by norm_num))
theorem R124861 : Reach 124861 := rs (se 3 (by rfl) ⟨23411, by rfl⟩) (B 46823 (by norm_num) ⟨23411, by rfl⟩ (by norm_num))
theorem R190421 : Reach 190421 := rs (se 7 (by rfl) ⟨2231, by rfl⟩) (B 4463 (by norm_num) ⟨2231, by rfl⟩ (by norm_num))
theorem R92173 : Reach 92173 := rs (se 3 (by rfl) ⟨17282, by rfl⟩) (B 34565 (by norm_num) ⟨17282, by rfl⟩ (by norm_num))
theorem R124973 : Reach 124973 := rs (se 3 (by rfl) ⟨23432, by rfl⟩) (B 46865 (by norm_num) ⟨23432, by rfl⟩ (by norm_num))
theorem R125069 : Reach 125069 := rs (se 3 (by rfl) ⟨23450, by rfl⟩) (B 46901 (by norm_num) ⟨23450, by rfl⟩ (by norm_num))
theorem R59545 : Reach 59545 := rs (se 2 (by rfl) ⟨22329, by rfl⟩) (B 44659 (by norm_num) ⟨22329, by rfl⟩ (by norm_num))
theorem R59549 : Reach 59549 := rs (se 3 (by rfl) ⟨11165, by rfl⟩) (B 22331 (by norm_num) ⟨11165, by rfl⟩ (by norm_num))
theorem R92333 : Reach 92333 := rs (se 3 (by rfl) ⟨17312, by rfl⟩) (B 34625 (by norm_num) ⟨17312, by rfl⟩ (by norm_num))
theorem R125165 : Reach 125165 := rs (se 3 (by rfl) ⟨23468, by rfl⟩) (B 46937 (by norm_num) ⟨23468, by rfl⟩ (by norm_num))
theorem R92477 : Reach 92477 := rs (se 3 (by rfl) ⟨17339, by rfl⟩) (B 34679 (by norm_num) ⟨17339, by rfl⟩ (by norm_num))
theorem R59717 : Reach 59717 := rs (se 4 (by rfl) ⟨5598, by rfl⟩) (B 11197 (by norm_num) ⟨5598, by rfl⟩ (by norm_num))
theorem R59773 : Reach 59773 := rs (se 3 (by rfl) ⟨11207, by rfl⟩) (B 22415 (by norm_num) ⟨11207, by rfl⟩ (by norm_num))
theorem R59869 : Reach 59869 := rs (se 3 (by rfl) ⟨11225, by rfl⟩) (B 22451 (by norm_num) ⟨11225, by rfl⟩ (by norm_num))
theorem R125509 : Reach 125509 := rs (se 4 (by rfl) ⟨11766, by rfl⟩) (B 23533 (by norm_num) ⟨11766, by rfl⟩ (by norm_num))
theorem R92765 : Reach 92765 := rs (se 3 (by rfl) ⟨17393, by rfl⟩) (B 34787 (by norm_num) ⟨17393, by rfl⟩ (by norm_num))
theorem R60041 : Reach 60041 := rs (se 2 (by rfl) ⟨22515, by rfl⟩) (B 45031 (by norm_num) ⟨22515, by rfl⟩ (by norm_num))
theorem R60049 : Reach 60049 := rs (se 2 (by rfl) ⟨22518, by rfl⟩) (B 45037 (by norm_num) ⟨22518, by rfl⟩ (by norm_num))
theorem R125621 : Reach 125621 := rs (se 5 (by rfl) ⟨5888, by rfl⟩) (B 11777 (by norm_num) ⟨5888, by rfl⟩ (by norm_num))
theorem R60097 : Reach 60097 := rs (se 2 (by rfl) ⟨22536, by rfl⟩) (B 45073 (by norm_num) ⟨22536, by rfl⟩ (by norm_num))
theorem R92917 : Reach 92917 := rs (se 5 (by rfl) ⟨4355, by rfl⟩) (B 8711 (by norm_num) ⟨4355, by rfl⟩ (by norm_num))
theorem R60193 : Reach 60193 := rs (se 2 (by rfl) ⟨22572, by rfl⟩) (B 45145 (by norm_num) ⟨22572, by rfl⟩ (by norm_num))
theorem R191333 : Reach 191333 := rs (se 4 (by rfl) ⟨17937, by rfl⟩) (B 35875 (by norm_num) ⟨17937, by rfl⟩ (by norm_num))
theorem R125813 : Reach 125813 := rs (se 5 (by rfl) ⟨5897, by rfl⟩) (B 11795 (by norm_num) ⟨5897, by rfl⟩ (by norm_num))
theorem R93109 : Reach 93109 := rs (se 5 (by rfl) ⟨4364, by rfl⟩) (B 8729 (by norm_num) ⟨4364, by rfl⟩ (by norm_num))
theorem R60365 : Reach 60365 := rs (se 3 (by rfl) ⟨11318, by rfl⟩) (B 22637 (by norm_num) ⟨11318, by rfl⟩ (by norm_num))
theorem R60421 : Reach 60421 := rs (se 4 (by rfl) ⟨5664, by rfl⟩) (B 11329 (by norm_num) ⟨5664, by rfl⟩ (by norm_num))
theorem R60433 : Reach 60433 := rs (se 2 (by rfl) ⟨22662, by rfl⟩) (B 45325 (by norm_num) ⟨22662, by rfl⟩ (by norm_num))
theorem R93221 : Reach 93221 := rs (se 4 (by rfl) ⟨8739, by rfl⟩) (B 17479 (by norm_num) ⟨8739, by rfl⟩ (by norm_num))
theorem R60517 : Reach 60517 := rs (se 4 (by rfl) ⟨5673, by rfl⟩) (B 11347 (by norm_num) ⟨5673, by rfl⟩ (by norm_num))
theorem R191605 : Reach 191605 := rs (se 5 (by rfl) ⟨8981, by rfl⟩) (B 17963 (by norm_num) ⟨8981, by rfl⟩ (by norm_num))
theorem R60689 : Reach 60689 := rs (se 2 (by rfl) ⟨22758, by rfl⟩) (B 45517 (by norm_num) ⟨22758, by rfl⟩ (by norm_num))
theorem R159029 : Reach 159029 := rs (se 5 (by rfl) ⟨7454, by rfl⟩) (B 14909 (by norm_num) ⟨7454, by rfl⟩ (by norm_num))
theorem R60745 : Reach 60745 := rs (se 2 (by rfl) ⟨22779, by rfl⟩) (B 45559 (by norm_num) ⟨22779, by rfl⟩ (by norm_num))
theorem R191909 : Reach 191909 := rs (se 4 (by rfl) ⟨17991, by rfl⟩) (B 35983 (by norm_num) ⟨17991, by rfl⟩ (by norm_num))
theorem R60841 : Reach 60841 := rs (se 2 (by rfl) ⟨22815, by rfl⟩) (B 45631 (by norm_num) ⟨22815, by rfl⟩ (by norm_num))
theorem R61013 : Reach 61013 := rs (se 8 (by rfl) ⟨357, by rfl⟩) (B 715 (by norm_num) ⟨357, by rfl⟩ (by norm_num))
theorem R61069 : Reach 61069 := rs (se 3 (by rfl) ⟨11450, by rfl⟩) (B 22901 (by norm_num) ⟨11450, by rfl⟩ (by norm_num))
theorem R159461 : Reach 159461 := rs (se 4 (by rfl) ⟨14949, by rfl⟩) (B 29899 (by norm_num) ⟨14949, by rfl⟩ (by norm_num))
theorem R61165 : Reach 61165 := rs (se 3 (by rfl) ⟨11468, by rfl⟩) (B 22937 (by norm_num) ⟨11468, by rfl⟩ (by norm_num))
theorem R93973 : Reach 93973 := rs (se 6 (by rfl) ⟨2202, by rfl⟩) (B 4405 (by norm_num) ⟨2202, by rfl⟩ (by norm_num))
theorem R126805 : Reach 126805 := rs (se 9 (by rfl) ⟨371, by rfl⟩) (B 743 (by norm_num) ⟨371, by rfl⟩ (by norm_num))
theorem R61337 : Reach 61337 := rs (se 2 (by rfl) ⟨23001, by rfl⟩) (B 46003 (by norm_num) ⟨23001, by rfl⟩ (by norm_num))
theorem R94117 : Reach 94117 := rs (se 4 (by rfl) ⟨8823, by rfl⟩) (B 17647 (by norm_num) ⟨8823, by rfl⟩ (by norm_num))
theorem R126917 : Reach 126917 := rs (se 4 (by rfl) ⟨11898, by rfl⟩) (B 23797 (by norm_num) ⟨11898, by rfl⟩ (by norm_num))
theorem R61393 : Reach 61393 := rs (se 2 (by rfl) ⟨23022, by rfl⟩) (B 46045 (by norm_num) ⟨23022, by rfl⟩ (by norm_num))
theorem R61457 : Reach 61457 := rs (se 2 (by rfl) ⟨23046, by rfl⟩) (B 46093 (by norm_num) ⟨23046, by rfl⟩ (by norm_num))
theorem R61489 : Reach 61489 := rs (se 2 (by rfl) ⟨23058, by rfl⟩) (B 46117 (by norm_num) ⟨23058, by rfl⟩ (by norm_num))
theorem R94277 : Reach 94277 := rs (se 4 (by rfl) ⟨8838, by rfl⟩) (B 17677 (by norm_num) ⟨8838, by rfl⟩ (by norm_num))
theorem R127109 : Reach 127109 := rs (se 4 (by rfl) ⟨11916, by rfl⟩) (B 23833 (by norm_num) ⟨11916, by rfl⟩ (by norm_num))
theorem R159893 : Reach 159893 := rs (se 6 (by rfl) ⟨3747, by rfl⟩) (B 7495 (by norm_num) ⟨3747, by rfl⟩ (by norm_num))
theorem R94421 : Reach 94421 := rs (se 7 (by rfl) ⟨1106, by rfl⟩) (B 2213 (by norm_num) ⟨1106, by rfl⟩ (by norm_num))
theorem R323797 : Reach 323797 := rs (se 7 (by rfl) ⟨3794, by rfl⟩) (B 7589 (by norm_num) ⟨3794, by rfl⟩ (by norm_num))
theorem R61661 : Reach 61661 := rs (se 3 (by rfl) ⟨11561, by rfl⟩) (B 23123 (by norm_num) ⟨11561, by rfl⟩ (by norm_num))
theorem R61717 : Reach 61717 := rs (se 6 (by rfl) ⟨1446, by rfl⟩) (B 2893 (by norm_num) ⟨1446, by rfl⟩ (by norm_num))
theorem R258389 : Reach 258389 := rs (se 10 (by rfl) ⟨378, by rfl⟩) (B 757 (by norm_num) ⟨378, by rfl⟩ (by norm_num))
theorem R61813 : Reach 61813 := rs (se 5 (by rfl) ⟨2897, by rfl⟩) (B 5795 (by norm_num) ⟨2897, by rfl⟩ (by norm_num))
theorem R94709 : Reach 94709 := rs (se 5 (by rfl) ⟨4439, by rfl⟩) (B 8879 (by norm_num) ⟨4439, by rfl⟩ (by norm_num))
theorem R61985 : Reach 61985 := rs (se 2 (by rfl) ⟨23244, by rfl⟩) (B 46489 (by norm_num) ⟨23244, by rfl⟩ (by norm_num))
theorem R94765 : Reach 94765 := rs (se 3 (by rfl) ⟨17768, by rfl⟩) (B 35537 (by norm_num) ⟨17768, by rfl⟩ (by norm_num))
theorem R160325 : Reach 160325 := rs (se 4 (by rfl) ⟨15030, by rfl⟩) (B 30061 (by norm_num) ⟨15030, by rfl⟩ (by norm_num))
theorem R62041 : Reach 62041 := rs (se 2 (by rfl) ⟨23265, by rfl⟩) (B 46531 (by norm_num) ⟨23265, by rfl⟩ (by norm_num))
theorem R94861 : Reach 94861 := rs (se 3 (by rfl) ⟨17786, by rfl⟩) (B 35573 (by norm_num) ⟨17786, by rfl⟩ (by norm_num))
theorem R62137 : Reach 62137 := rs (se 2 (by rfl) ⟨23301, by rfl⟩) (B 46603 (by norm_num) ⟨23301, by rfl⟩ (by norm_num))
theorem R127781 : Reach 127781 := rs (se 4 (by rfl) ⟨11979, by rfl⟩) (B 23959 (by norm_num) ⟨11979, by rfl⟩ (by norm_num))
theorem R62309 : Reach 62309 := rs (se 4 (by rfl) ⟨5841, by rfl⟩) (B 11683 (by norm_num) ⟨5841, by rfl⟩ (by norm_num))
theorem R62365 : Reach 62365 := rs (se 3 (by rfl) ⟨11693, by rfl⟩) (B 23387 (by norm_num) ⟨11693, by rfl⟩ (by norm_num))
theorem R62381 : Reach 62381 := rs (se 3 (by rfl) ⟨11696, by rfl⟩) (B 23393 (by norm_num) ⟨11696, by rfl⟩ (by norm_num))
theorem R95165 : Reach 95165 := rs (se 3 (by rfl) ⟨17843, by rfl⟩) (B 35687 (by norm_num) ⟨17843, by rfl⟩ (by norm_num))
theorem R160757 : Reach 160757 := rs (se 5 (by rfl) ⟨7535, by rfl⟩) (B 15071 (by norm_num) ⟨7535, by rfl⟩ (by norm_num))
theorem R62461 : Reach 62461 := rs (se 3 (by rfl) ⟨11711, by rfl⟩) (B 23423 (by norm_num) ⟨11711, by rfl⟩ (by norm_num))
theorem R128101 : Reach 128101 := rs (se 4 (by rfl) ⟨12009, by rfl⟩) (B 24019 (by norm_num) ⟨12009, by rfl⟩ (by norm_num))
theorem R62633 : Reach 62633 := rs (se 2 (by rfl) ⟨23487, by rfl⟩) (B 46975 (by norm_num) ⟨23487, by rfl⟩ (by norm_num))
theorem R324821 : Reach 324821 := rs (se 7 (by rfl) ⟨3806, by rfl⟩) (B 7613 (by norm_num) ⟨3806, by rfl⟩ (by norm_num))
theorem R128213 : Reach 128213 := rs (se 7 (by rfl) ⟨1502, by rfl⟩) (B 3005 (by norm_num) ⟨1502, by rfl⟩ (by norm_num))
theorem R62689 : Reach 62689 := rs (se 2 (by rfl) ⟨23508, by rfl⟩) (B 47017 (by norm_num) ⟨23508, by rfl⟩ (by norm_num))
theorem R488693 : Reach 488693 := rs (se 5 (by rfl) ⟨22907, by rfl⟩) (B 45815 (by norm_num) ⟨22907, by rfl⟩ (by norm_num))
theorem R62785 : Reach 62785 := rs (se 2 (by rfl) ⟨23544, by rfl⟩) (B 47089 (by norm_num) ⟨23544, by rfl⟩ (by norm_num))
theorem R193909 : Reach 193909 := rs (se 5 (by rfl) ⟨9089, by rfl⟩) (B 18179 (by norm_num) ⟨9089, by rfl⟩ (by norm_num))
theorem R128405 : Reach 128405 := rs (se 6 (by rfl) ⟨3009, by rfl⟩) (B 6019 (by norm_num) ⟨3009, by rfl⟩ (by norm_num))
theorem R161189 : Reach 161189 := rs (se 4 (by rfl) ⟨15111, by rfl⟩) (B 30223 (by norm_num) ⟨15111, by rfl⟩ (by norm_num))
theorem R194005 : Reach 194005 := rs (se 7 (by rfl) ⟨2273, by rfl⟩) (B 4547 (by norm_num) ⟨2273, by rfl⟩ (by norm_num))
theorem R194021 : Reach 194021 := rs (se 4 (by rfl) ⟨18189, by rfl⟩) (B 36379 (by norm_num) ⟨18189, by rfl⟩ (by norm_num))
theorem R62957 : Reach 62957 := rs (se 3 (by rfl) ⟨11804, by rfl⟩) (B 23609 (by norm_num) ⟨11804, by rfl⟩ (by norm_num))
theorem R63013 : Reach 63013 := rs (se 4 (by rfl) ⟨5907, by rfl⟩) (B 11815 (by norm_num) ⟨5907, by rfl⟩ (by norm_num))
theorem R1799765 : Reach 1799765 := rs (se 8 (by rfl) ⟨10545, by rfl⟩) (B 21091 (by norm_num) ⟨10545, by rfl⟩ (by norm_num))
theorem R63109 : Reach 63109 := rs (se 4 (by rfl) ⟨5916, by rfl⟩) (B 11833 (by norm_num) ⟨5916, by rfl⟩ (by norm_num))
theorem R947861 : Reach 947861 := rs (se 6 (by rfl) ⟨22215, by rfl⟩) (B 44431 (by norm_num) ⟨22215, by rfl⟩ (by norm_num))
theorem R95917 : Reach 95917 := rs (se 3 (by rfl) ⟨17984, by rfl⟩) (B 35969 (by norm_num) ⟨17984, by rfl⟩ (by norm_num))
theorem R95941 : Reach 95941 := rs (se 4 (by rfl) ⟨8994, by rfl⟩) (B 17989 (by norm_num) ⟨8994, by rfl⟩ (by norm_num))
theorem R980693 : Reach 980693 := rs (se 7 (by rfl) ⟨11492, by rfl⟩) (B 22985 (by norm_num) ⟨11492, by rfl⟩ (by norm_num))
theorem R96013 : Reach 96013 := rs (se 3 (by rfl) ⟨18002, by rfl⟩) (B 36005 (by norm_num) ⟨18002, by rfl⟩ (by norm_num))
theorem R96061 : Reach 96061 := rs (se 3 (by rfl) ⟨18011, by rfl⟩) (B 36023 (by norm_num) ⟨18011, by rfl⟩ (by norm_num))
theorem R161621 : Reach 161621 := rs (se 9 (by rfl) ⟨473, by rfl⟩) (B 947 (by norm_num) ⟨473, by rfl⟩ (by norm_num))
theorem R292693 : Reach 292693 := rs (se 9 (by rfl) ⟨857, by rfl⟩) (B 1715 (by norm_num) ⟨857, by rfl⟩ (by norm_num))
theorem R96221 : Reach 96221 := rs (se 3 (by rfl) ⟨18041, by rfl⟩) (B 36083 (by norm_num) ⟨18041, by rfl⟩ (by norm_num))
theorem R161797 : Reach 161797 := rs (se 4 (by rfl) ⟨15168, by rfl⟩) (B 30337 (by norm_num) ⟨15168, by rfl⟩ (by norm_num))
theorem R391189 : Reach 391189 := rs (se 6 (by rfl) ⟨9168, by rfl⟩) (B 18337 (by norm_num) ⟨9168, by rfl⟩ (by norm_num))
theorem R96365 : Reach 96365 := rs (se 3 (by rfl) ⟨18068, by rfl⟩) (B 36137 (by norm_num) ⟨18068, by rfl⟩ (by norm_num))
theorem R63605 : Reach 63605 := rs (se 5 (by rfl) ⟨2981, by rfl⟩) (B 5963 (by norm_num) ⟨2981, by rfl⟩ (by norm_num))
theorem R63661 : Reach 63661 := rs (se 3 (by rfl) ⟨11936, by rfl⟩) (B 23873 (by norm_num) ⟨11936, by rfl⟩ (by norm_num))
theorem R162053 : Reach 162053 := rs (se 4 (by rfl) ⟨15192, by rfl⟩) (B 30385 (by norm_num) ⟨15192, by rfl⟩ (by norm_num))
theorem R63757 : Reach 63757 := rs (se 3 (by rfl) ⟨11954, by rfl⟩) (B 23909 (by norm_num) ⟨11954, by rfl⟩ (by norm_num))
theorem R129397 : Reach 129397 := rs (se 5 (by rfl) ⟨6065, by rfl⟩) (B 12131 (by norm_num) ⟨6065, by rfl⟩ (by norm_num))
theorem R96653 : Reach 96653 := rs (se 3 (by rfl) ⟨18122, by rfl⟩) (B 36245 (by norm_num) ⟨18122, by rfl⟩ (by norm_num))
theorem R96805 : Reach 96805 := rs (se 4 (by rfl) ⟨9075, by rfl⟩) (B 18151 (by norm_num) ⟨9075, by rfl⟩ (by norm_num))
theorem R227893 : Reach 227893 := rs (se 5 (by rfl) ⟨10682, by rfl⟩) (B 21365 (by norm_num) ⟨10682, by rfl⟩ (by norm_num))
theorem R162485 : Reach 162485 := rs (se 5 (by rfl) ⟨7616, by rfl⟩) (B 15233 (by norm_num) ⟨7616, by rfl⟩ (by norm_num))
theorem R64253 : Reach 64253 := rs (se 3 (by rfl) ⟨12047, by rfl⟩) (B 24095 (by norm_num) ⟨12047, by rfl⟩ (by norm_num))
theorem R64309 : Reach 64309 := rs (se 5 (by rfl) ⟨3014, by rfl⟩) (B 6029 (by norm_num) ⟨3014, by rfl⟩ (by norm_num))
theorem R64333 : Reach 64333 := rs (se 3 (by rfl) ⟨12062, by rfl⟩) (B 24125 (by norm_num) ⟨12062, by rfl⟩ (by norm_num))
theorem R228181 : Reach 228181 := rs (se 9 (by rfl) ⟨668, by rfl⟩) (B 1337 (by norm_num) ⟨668, by rfl⟩ (by norm_num))
theorem R64405 : Reach 64405 := rs (se 6 (by rfl) ⟨1509, by rfl⟩) (B 3019 (by norm_num) ⟨1509, by rfl⟩ (by norm_num))
theorem R162917 : Reach 162917 := rs (se 4 (by rfl) ⟨15273, by rfl⟩) (B 30547 (by norm_num) ⟨15273, by rfl⟩ (by norm_num))
theorem R130517 : Reach 130517 := rs (se 7 (by rfl) ⟨1529, by rfl⟩) (B 3059 (by norm_num) ⟨1529, by rfl⟩ (by norm_num))
theorem R97781 : Reach 97781 := rs (se 5 (by rfl) ⟨4583, by rfl⟩) (B 9167 (by norm_num) ⟨4583, by rfl⟩ (by norm_num))
theorem R163349 : Reach 163349 := rs (se 6 (by rfl) ⟨3828, by rfl⟩) (B 7657 (by norm_num) ⟨3828, by rfl⟩ (by norm_num))
theorem R163781 : Reach 163781 := rs (se 4 (by rfl) ⟨15354, by rfl⟩) (B 30709 (by norm_num) ⟨15354, by rfl⟩ (by norm_num))
theorem R262133 : Reach 262133 := rs (se 5 (by rfl) ⟨12287, by rfl⟩) (B 24575 (by norm_num) ⟨12287, by rfl⟩ (by norm_num))
theorem R163885 : Reach 163885 := rs (se 3 (by rfl) ⟨30728, by rfl⟩) R61457
theorem R163889 : Reach 163889 := rs (se 2 (by rfl) ⟨61458, by rfl⟩) R122917
theorem R65777 : Reach 65777 := rs (se 2 (by rfl) ⟨24666, by rfl⟩) R49333
theorem R262435 : Reach 262435 := rs (se 1 (by rfl) ⟨196826, by rfl⟩) R393653
theorem R164429 : Reach 164429 := rs (se 3 (by rfl) ⟨30830, by rfl⟩) R61661
theorem R164483 : Reach 164483 := rs (se 1 (by rfl) ⟨123362, by rfl⟩) R246725
theorem R164753 : Reach 164753 := rs (se 2 (by rfl) ⟨61782, by rfl⟩) R123565
theorem R66529 : Reach 66529 := rs (se 2 (by rfl) ⟨24948, by rfl⟩) R49897
theorem R99299 : Reach 99299 := rs (se 1 (by rfl) ⟨74474, by rfl⟩) R148949
theorem R66755 : Reach 66755 := rs (se 1 (by rfl) ⟨50066, by rfl⟩) R100133
theorem R230627 : Reach 230627 := rs (se 1 (by rfl) ⟨172970, by rfl⟩) R345941
theorem R165293 : Reach 165293 := rs (se 3 (by rfl) ⟨30992, by rfl⟩) R61985
theorem R165347 : Reach 165347 := rs (se 1 (by rfl) ⟨124010, by rfl⟩) R248021
theorem R67171 : Reach 67171 := rs (se 1 (by rfl) ⟨50378, by rfl⟩) R100757
theorem R165617 : Reach 165617 := rs (se 2 (by rfl) ⟨62106, by rfl⟩) R124213
theorem R67729 : Reach 67729 := rs (se 2 (by rfl) ⟨25398, by rfl⟩) R50797
theorem R67763 : Reach 67763 := rs (se 1 (by rfl) ⟨50822, by rfl⟩) R101645
theorem R166157 : Reach 166157 := rs (se 3 (by rfl) ⟨31154, by rfl⟩) R62309
theorem R166211 : Reach 166211 := rs (se 1 (by rfl) ⟨124658, by rfl⟩) R249317
theorem R690545 : Reach 690545 := rs (se 2 (by rfl) ⟨258954, by rfl⟩) R517909
theorem R100739 : Reach 100739 := rs (se 1 (by rfl) ⟨75554, by rfl⟩) R151109
theorem R297379 : Reach 297379 := rs (se 1 (by rfl) ⟨223034, by rfl⟩) R446069
theorem R166349 : Reach 166349 := rs (se 3 (by rfl) ⟨31190, by rfl⟩) R62381
theorem R166481 : Reach 166481 := rs (se 2 (by rfl) ⟨62430, by rfl⟩) R124861
theorem R101009 : Reach 101009 := rs (se 2 (by rfl) ⟨37878, by rfl⟩) R75757
theorem R68321 : Reach 68321 := rs (se 2 (by rfl) ⟨25620, by rfl⟩) R51241
theorem R101155 : Reach 101155 := rs (se 1 (by rfl) ⟨75866, by rfl⟩) R151733
theorem R68401 : Reach 68401 := rs (se 2 (by rfl) ⟨25650, by rfl⟩) R51301
theorem R232483 : Reach 232483 := rs (se 1 (by rfl) ⟨174362, by rfl⟩) R348725
theorem R167021 : Reach 167021 := rs (se 3 (by rfl) ⟨31316, by rfl⟩) R62633
theorem R167075 : Reach 167075 := rs (se 1 (by rfl) ⟨125306, by rfl⟩) R250613
theorem R232739 : Reach 232739 := rs (se 1 (by rfl) ⟨174554, by rfl⟩) R349109
theorem R68993 : Reach 68993 := rs (se 2 (by rfl) ⟨25872, by rfl⟩) R51745
theorem R167345 : Reach 167345 := rs (se 2 (by rfl) ⟨62754, by rfl⟩) R125509
theorem R69187 : Reach 69187 := rs (se 1 (by rfl) ⟨51890, by rfl⟩) R103781
theorem R134797 : Reach 134797 := rs (se 3 (by rfl) ⟨25274, by rfl⟩) R50549
theorem R167885 : Reach 167885 := rs (se 3 (by rfl) ⟨31478, by rfl⟩) R62957
theorem R69665 : Reach 69665 := rs (se 2 (by rfl) ⟨26124, by rfl⟩) R52249
theorem R69761 : Reach 69761 := rs (se 2 (by rfl) ⟨26160, by rfl⟩) R52321
theorem R69779 : Reach 69779 := rs (se 1 (by rfl) ⟨52334, by rfl⟩) R104669
theorem R69859 : Reach 69859 := rs (se 1 (by rfl) ⟨52394, by rfl⟩) R104789
theorem R168227 : Reach 168227 := rs (se 1 (by rfl) ⟨126170, by rfl⟩) R252341
theorem R102755 : Reach 102755 := rs (se 1 (by rfl) ⟨77066, by rfl⟩) R154133
theorem R233891 : Reach 233891 := rs (se 1 (by rfl) ⟨175418, by rfl⟩) R350837
theorem R135587 : Reach 135587 := rs (se 1 (by rfl) ⟨101690, by rfl⟩) R203381
theorem R135857 : Reach 135857 := rs (se 2 (by rfl) ⟨50946, by rfl⟩) R101893
theorem R70417 : Reach 70417 := rs (se 2 (by rfl) ⟨26406, by rfl⟩) R52813
theorem R1151765 : Reach 1151765 := rs (se 6 (by rfl) ⟨26994, by rfl⟩) R53989
theorem R168803 : Reach 168803 := rs (se 1 (by rfl) ⟨126602, by rfl⟩) R253205
theorem R201649 : Reach 201649 := rs (se 2 (by rfl) ⟨75618, by rfl⟩) R151237
theorem R103427 : Reach 103427 := rs (se 1 (by rfl) ⟨77570, by rfl⟩) R155141
theorem R70691 : Reach 70691 := rs (se 1 (by rfl) ⟨53018, by rfl⟩) R106037
theorem R70721 : Reach 70721 := rs (se 2 (by rfl) ⟨26520, by rfl⟩) R53041
theorem R70739 : Reach 70739 := rs (se 1 (by rfl) ⟨53054, by rfl⟩) R106109
theorem R70769 : Reach 70769 := rs (se 2 (by rfl) ⟨26538, by rfl⟩) R53077
theorem R169073 : Reach 169073 := rs (se 2 (by rfl) ⟨63402, by rfl⟩) R126805
theorem R70787 : Reach 70787 := rs (se 1 (by rfl) ⟨53090, by rfl⟩) R106181
theorem R70817 : Reach 70817 := rs (se 2 (by rfl) ⟨26556, by rfl⟩) R53113
theorem R234659 : Reach 234659 := rs (se 1 (by rfl) ⟨175994, by rfl⟩) R351989
theorem R70835 : Reach 70835 := rs (se 1 (by rfl) ⟨53126, by rfl⟩) R106253
theorem R70865 : Reach 70865 := rs (se 2 (by rfl) ⟨26574, by rfl⟩) R53149
theorem R70883 : Reach 70883 := rs (se 1 (by rfl) ⟨53162, by rfl⟩) R106325
theorem R70913 : Reach 70913 := rs (se 2 (by rfl) ⟨26592, by rfl⟩) R53185
theorem R70931 : Reach 70931 := rs (se 1 (by rfl) ⟨53198, by rfl⟩) R106397
theorem R70961 : Reach 70961 := rs (se 2 (by rfl) ⟨26610, by rfl⟩) R53221
theorem R70979 : Reach 70979 := rs (se 1 (by rfl) ⟨53234, by rfl⟩) R106469
theorem R136529 : Reach 136529 := rs (se 2 (by rfl) ⟨51198, by rfl⟩) R102397
theorem R71009 : Reach 71009 := rs (se 2 (by rfl) ⟨26628, by rfl⟩) R53257
theorem R71027 : Reach 71027 := rs (se 1 (by rfl) ⟨53270, by rfl⟩) R106541
theorem R71057 : Reach 71057 := rs (se 2 (by rfl) ⟨26646, by rfl⟩) R53293
theorem R71075 : Reach 71075 := rs (se 1 (by rfl) ⟨53306, by rfl⟩) R106613
theorem R71105 : Reach 71105 := rs (se 2 (by rfl) ⟨26664, by rfl⟩) R53329
theorem R71123 : Reach 71123 := rs (se 1 (by rfl) ⟨53342, by rfl⟩) R106685
theorem R71153 : Reach 71153 := rs (se 2 (by rfl) ⟨26682, by rfl⟩) R53365
theorem R71171 : Reach 71171 := rs (se 1 (by rfl) ⟨53378, by rfl⟩) R106757
theorem R71201 : Reach 71201 := rs (se 2 (by rfl) ⟨26700, by rfl⟩) R53401
theorem R71219 : Reach 71219 := rs (se 1 (by rfl) ⟨53414, by rfl⟩) R106829
theorem R71249 : Reach 71249 := rs (se 2 (by rfl) ⟨26718, by rfl⟩) R53437
theorem R71267 : Reach 71267 := rs (se 1 (by rfl) ⟨53450, by rfl⟩) R106901
theorem R562787 : Reach 562787 := rs (se 1 (by rfl) ⟨422090, by rfl⟩) R844181
theorem R431729 : Reach 431729 := rs (se 2 (by rfl) ⟨161898, by rfl⟩) R323797
theorem R71297 : Reach 71297 := rs (se 2 (by rfl) ⟨26736, by rfl⟩) R53473
theorem R169613 : Reach 169613 := rs (se 3 (by rfl) ⟨31802, by rfl⟩) R63605
theorem R71315 : Reach 71315 := rs (se 1 (by rfl) ⟨53486, by rfl⟩) R106973
theorem R71345 : Reach 71345 := rs (se 2 (by rfl) ⟨26754, by rfl⟩) R53509
theorem R71363 : Reach 71363 := rs (se 1 (by rfl) ⟨53522, by rfl⟩) R107045
theorem R366277 : Reach 366277 := rs (se 4 (by rfl) ⟨34338, by rfl⟩) R68677
theorem R71393 : Reach 71393 := rs (se 2 (by rfl) ⟨26772, by rfl⟩) R53545
theorem R71411 : Reach 71411 := rs (se 1 (by rfl) ⟨53558, by rfl⟩) R107117
theorem R71441 : Reach 71441 := rs (se 2 (by rfl) ⟨26790, by rfl⟩) R53581
theorem R71459 : Reach 71459 := rs (se 1 (by rfl) ⟨53594, by rfl⟩) R107189
theorem R71489 : Reach 71489 := rs (se 2 (by rfl) ⟨26808, by rfl⟩) R53617
theorem R71507 : Reach 71507 := rs (se 1 (by rfl) ⟨53630, by rfl⟩) R107261
theorem R71537 : Reach 71537 := rs (se 2 (by rfl) ⟨26826, by rfl⟩) R53653
theorem R464753 : Reach 464753 := rs (se 2 (by rfl) ⟨174282, by rfl⟩) R348565
theorem R71555 : Reach 71555 := rs (se 1 (by rfl) ⟨53666, by rfl⟩) R107333
theorem R71585 : Reach 71585 := rs (se 2 (by rfl) ⟨26844, by rfl⟩) R53689
theorem R71603 : Reach 71603 := rs (se 1 (by rfl) ⟨53702, by rfl⟩) R107405
theorem R71633 : Reach 71633 := rs (se 2 (by rfl) ⟨26862, by rfl⟩) R53725
theorem R71651 : Reach 71651 := rs (se 1 (by rfl) ⟨53738, by rfl⟩) R107477
theorem R71681 : Reach 71681 := rs (se 2 (by rfl) ⟨26880, by rfl⟩) R53761
theorem R71699 : Reach 71699 := rs (se 1 (by rfl) ⟨53774, by rfl⟩) R107549
theorem R71729 : Reach 71729 := rs (se 2 (by rfl) ⟨26898, by rfl⟩) R53797
theorem R71747 : Reach 71747 := rs (se 1 (by rfl) ⟨53810, by rfl⟩) R107621
theorem R71761 : Reach 71761 := rs (se 2 (by rfl) ⟨26910, by rfl⟩) R53821
theorem R71777 : Reach 71777 := rs (se 2 (by rfl) ⟨26916, by rfl⟩) R53833
theorem R137315 : Reach 137315 := rs (se 1 (by rfl) ⟨102986, by rfl⟩) R205973
theorem R71795 : Reach 71795 := rs (se 1 (by rfl) ⟨53846, by rfl⟩) R107693
theorem R71825 : Reach 71825 := rs (se 2 (by rfl) ⟨26934, by rfl⟩) R53869
theorem R71843 : Reach 71843 := rs (se 1 (by rfl) ⟨53882, by rfl⟩) R107765
theorem R71873 : Reach 71873 := rs (se 2 (by rfl) ⟨26952, by rfl⟩) R53905
theorem R71875 : Reach 71875 := rs (se 1 (by rfl) ⟨53906, by rfl⟩) R107813
theorem R71891 : Reach 71891 := rs (se 1 (by rfl) ⟨53918, by rfl⟩) R107837
theorem R71921 : Reach 71921 := rs (se 2 (by rfl) ⟨26970, by rfl⟩) R53941
theorem R71939 : Reach 71939 := rs (se 1 (by rfl) ⟨53954, by rfl⟩) R107909
theorem R71969 : Reach 71969 := rs (se 2 (by rfl) ⟨26988, by rfl⟩) R53977
theorem R203057 : Reach 203057 := rs (se 2 (by rfl) ⟨76146, by rfl⟩) R152293
theorem R71987 : Reach 71987 := rs (se 1 (by rfl) ⟨53990, by rfl⟩) R107981
theorem R104771 : Reach 104771 := rs (se 1 (by rfl) ⟨78578, by rfl⟩) R157157
theorem R72017 : Reach 72017 := rs (se 2 (by rfl) ⟨27006, by rfl⟩) R54013
theorem R72035 : Reach 72035 := rs (se 1 (by rfl) ⟨54026, by rfl⟩) R108053
theorem R235889 : Reach 235889 := rs (se 2 (by rfl) ⟨88458, by rfl⟩) R176917
theorem R72065 : Reach 72065 := rs (se 2 (by rfl) ⟨27024, by rfl⟩) R54049
theorem R72083 : Reach 72083 := rs (se 1 (by rfl) ⟨54062, by rfl⟩) R108125
theorem R137645 : Reach 137645 := rs (se 3 (by rfl) ⟨25808, by rfl⟩) R51617
theorem R72113 : Reach 72113 := rs (se 2 (by rfl) ⟨27042, by rfl⟩) R54085
theorem R72131 : Reach 72131 := rs (se 1 (by rfl) ⟨54098, by rfl⟩) R108197
theorem R72161 : Reach 72161 := rs (se 2 (by rfl) ⟨27060, by rfl⟩) R54121
theorem R137713 : Reach 137713 := rs (se 2 (by rfl) ⟨51642, by rfl⟩) R103285
theorem R72179 : Reach 72179 := rs (se 1 (by rfl) ⟨54134, by rfl⟩) R108269
theorem R72209 : Reach 72209 := rs (se 2 (by rfl) ⟨27078, by rfl⟩) R54157
theorem R72227 : Reach 72227 := rs (se 1 (by rfl) ⟨54170, by rfl⟩) R108341
theorem R170531 : Reach 170531 := rs (se 1 (by rfl) ⟨127898, by rfl⟩) R255797
theorem R72257 : Reach 72257 := rs (se 2 (by rfl) ⟨27096, by rfl⟩) R54193
theorem R72275 : Reach 72275 := rs (se 1 (by rfl) ⟨54206, by rfl⟩) R108413
theorem R72305 : Reach 72305 := rs (se 2 (by rfl) ⟨27114, by rfl⟩) R54229
theorem R72323 : Reach 72323 := rs (se 1 (by rfl) ⟨54242, by rfl⟩) R108485
theorem R72353 : Reach 72353 := rs (se 2 (by rfl) ⟨27132, by rfl⟩) R54265
theorem R72371 : Reach 72371 := rs (se 1 (by rfl) ⟨54278, by rfl⟩) R108557
theorem R137933 : Reach 137933 := rs (se 3 (by rfl) ⟨25862, by rfl⟩) R51725
theorem R72401 : Reach 72401 := rs (se 2 (by rfl) ⟨27150, by rfl⟩) R54301
theorem R72419 : Reach 72419 := rs (se 1 (by rfl) ⟨54314, by rfl⟩) R108629
theorem R72449 : Reach 72449 := rs (se 2 (by rfl) ⟨27168, by rfl⟩) R54337
theorem R137987 : Reach 137987 := rs (se 1 (by rfl) ⟨103490, by rfl⟩) R206981
theorem R72467 : Reach 72467 := rs (se 1 (by rfl) ⟨54350, by rfl⟩) R108701
theorem R72497 : Reach 72497 := rs (se 2 (by rfl) ⟨27186, by rfl⟩) R54373
theorem R170801 : Reach 170801 := rs (se 2 (by rfl) ⟨64050, by rfl⟩) R128101
theorem R72515 : Reach 72515 := rs (se 1 (by rfl) ⟨54386, by rfl⟩) R108773
theorem R203597 : Reach 203597 := rs (se 3 (by rfl) ⟨38174, by rfl⟩) R76349
theorem R72545 : Reach 72545 := rs (se 2 (by rfl) ⟨27204, by rfl⟩) R54409
theorem R498545 : Reach 498545 := rs (se 2 (by rfl) ⟨186954, by rfl⟩) R373909
theorem R72563 : Reach 72563 := rs (se 1 (by rfl) ⟨54422, by rfl⟩) R108845
theorem R236429 : Reach 236429 := rs (se 3 (by rfl) ⟨44330, by rfl⟩) R88661
theorem R72593 : Reach 72593 := rs (se 2 (by rfl) ⟨27222, by rfl⟩) R54445
theorem R72611 : Reach 72611 := rs (se 1 (by rfl) ⟨54458, by rfl⟩) R108917
theorem R138161 : Reach 138161 := rs (se 2 (by rfl) ⟨51810, by rfl⟩) R103621
theorem R72641 : Reach 72641 := rs (se 2 (by rfl) ⟨27240, by rfl⟩) R54481
theorem R72659 : Reach 72659 := rs (se 1 (by rfl) ⟨54494, by rfl⟩) R108989
theorem R72689 : Reach 72689 := rs (se 2 (by rfl) ⟨27258, by rfl⟩) R54517
theorem R72707 : Reach 72707 := rs (se 1 (by rfl) ⟨54530, by rfl⟩) R109061
theorem R72737 : Reach 72737 := rs (se 2 (by rfl) ⟨27276, by rfl⟩) R54553
theorem R72755 : Reach 72755 := rs (se 1 (by rfl) ⟨54566, by rfl⟩) R109133
theorem R72785 : Reach 72785 := rs (se 2 (by rfl) ⟨27294, by rfl⟩) R54589
theorem R72803 : Reach 72803 := rs (se 1 (by rfl) ⟨54602, by rfl⟩) R109205
theorem R72833 : Reach 72833 := rs (se 2 (by rfl) ⟨27312, by rfl⟩) R54625
theorem R72851 : Reach 72851 := rs (se 1 (by rfl) ⟨54638, by rfl⟩) R109277
theorem R72881 : Reach 72881 := rs (se 2 (by rfl) ⟨27330, by rfl⟩) R54661
theorem R72899 : Reach 72899 := rs (se 1 (by rfl) ⟨54674, by rfl⟩) R109349
theorem R72929 : Reach 72929 := rs (se 2 (by rfl) ⟨27348, by rfl⟩) R54697
theorem R72947 : Reach 72947 := rs (se 1 (by rfl) ⟨54710, by rfl⟩) R109421
theorem R72977 : Reach 72977 := rs (se 2 (by rfl) ⟨27366, by rfl⟩) R54733
theorem R72995 : Reach 72995 := rs (se 1 (by rfl) ⟨54746, by rfl⟩) R109493
theorem R73025 : Reach 73025 := rs (se 2 (by rfl) ⟨27384, by rfl⟩) R54769
theorem R171341 : Reach 171341 := rs (se 3 (by rfl) ⟨32126, by rfl⟩) R64253
theorem R73043 : Reach 73043 := rs (se 1 (by rfl) ⟨54782, by rfl⟩) R109565
theorem R73073 : Reach 73073 := rs (se 2 (by rfl) ⟨27402, by rfl⟩) R54805
theorem R73091 : Reach 73091 := rs (se 1 (by rfl) ⟨54818, by rfl⟩) R109637
theorem R73121 : Reach 73121 := rs (se 2 (by rfl) ⟨27420, by rfl⟩) R54841
theorem R73139 : Reach 73139 := rs (se 1 (by rfl) ⟨54854, by rfl⟩) R109709
theorem R73169 : Reach 73169 := rs (se 2 (by rfl) ⟨27438, by rfl⟩) R54877
theorem R73187 : Reach 73187 := rs (se 1 (by rfl) ⟨54890, by rfl⟩) R109781
theorem R73217 : Reach 73217 := rs (se 2 (by rfl) ⟨27456, by rfl⟩) R54913
theorem R73235 : Reach 73235 := rs (se 1 (by rfl) ⟨54926, by rfl⟩) R109853
theorem R106019 : Reach 106019 := rs (se 1 (by rfl) ⟨79514, by rfl⟩) R159029
theorem R73265 : Reach 73265 := rs (se 2 (by rfl) ⟨27474, by rfl⟩) R54949
theorem R269873 : Reach 269873 := rs (se 2 (by rfl) ⟨101202, by rfl⟩) R202405
theorem R73283 : Reach 73283 := rs (se 1 (by rfl) ⟨54962, by rfl⟩) R109925
theorem R138829 : Reach 138829 := rs (se 3 (by rfl) ⟨26030, by rfl⟩) R52061
theorem R73313 : Reach 73313 := rs (se 2 (by rfl) ⟨27492, by rfl⟩) R54985
theorem R73331 : Reach 73331 := rs (se 1 (by rfl) ⟨54998, by rfl⟩) R109997
theorem R73361 : Reach 73361 := rs (se 2 (by rfl) ⟨27510, by rfl⟩) R55021
theorem R73379 : Reach 73379 := rs (se 1 (by rfl) ⟨55034, by rfl⟩) R110069
theorem R73409 : Reach 73409 := rs (se 2 (by rfl) ⟨27528, by rfl⟩) R55057
theorem R73427 : Reach 73427 := rs (se 1 (by rfl) ⟨55070, by rfl⟩) R110141
theorem R138989 : Reach 138989 := rs (se 3 (by rfl) ⟨26060, by rfl⟩) R52121
theorem R73457 : Reach 73457 := rs (se 2 (by rfl) ⟨27546, by rfl⟩) R55093
theorem R73475 : Reach 73475 := rs (se 1 (by rfl) ⟨55106, by rfl⟩) R110213
theorem R73505 : Reach 73505 := rs (se 2 (by rfl) ⟨27564, by rfl⟩) R55129
theorem R106289 : Reach 106289 := rs (se 2 (by rfl) ⟨39858, by rfl⟩) R79717
theorem R73523 : Reach 73523 := rs (se 1 (by rfl) ⟨55142, by rfl⟩) R110285
theorem R106307 : Reach 106307 := rs (se 1 (by rfl) ⟨79730, by rfl⟩) R159461
theorem R73553 : Reach 73553 := rs (se 2 (by rfl) ⟨27582, by rfl⟩) R55165
theorem R73571 : Reach 73571 := rs (se 1 (by rfl) ⟨55178, by rfl⟩) R110357
theorem R204643 : Reach 204643 := rs (se 1 (by rfl) ⟨153482, by rfl⟩) R306965
theorem R73601 : Reach 73601 := rs (se 2 (by rfl) ⟨27600, by rfl⟩) R55201
theorem R73619 : Reach 73619 := rs (se 1 (by rfl) ⟨55214, by rfl⟩) R110429
theorem R139171 : Reach 139171 := rs (se 1 (by rfl) ⟨104378, by rfl⟩) R208757
theorem R73649 : Reach 73649 := rs (se 2 (by rfl) ⟨27618, by rfl⟩) R55237
theorem R73667 : Reach 73667 := rs (se 1 (by rfl) ⟨55250, by rfl⟩) R110501
theorem R73697 : Reach 73697 := rs (se 2 (by rfl) ⟨27636, by rfl⟩) R55273
theorem R73715 : Reach 73715 := rs (se 1 (by rfl) ⟨55286, by rfl⟩) R110573
theorem R73745 : Reach 73745 := rs (se 2 (by rfl) ⟨27654, by rfl⟩) R55309
theorem R73763 : Reach 73763 := rs (se 1 (by rfl) ⟨55322, by rfl⟩) R110645
theorem R73793 : Reach 73793 := rs (se 2 (by rfl) ⟨27672, by rfl⟩) R55345
theorem R106577 : Reach 106577 := rs (se 2 (by rfl) ⟨39966, by rfl⟩) R79933
theorem R73811 : Reach 73811 := rs (se 1 (by rfl) ⟨55358, by rfl⟩) R110717
theorem R106595 : Reach 106595 := rs (se 1 (by rfl) ⟨79946, by rfl⟩) R159893
theorem R73841 : Reach 73841 := rs (se 2 (by rfl) ⟨27690, by rfl⟩) R55381
theorem R106609 : Reach 106609 := rs (se 2 (by rfl) ⟨39978, by rfl⟩) R79957
theorem R73859 : Reach 73859 := rs (se 1 (by rfl) ⟨55394, by rfl⟩) R110789
theorem R73889 : Reach 73889 := rs (se 2 (by rfl) ⟨27708, by rfl⟩) R55417
theorem R73907 : Reach 73907 := rs (se 1 (by rfl) ⟨55430, by rfl⟩) R110861
theorem R73937 : Reach 73937 := rs (se 2 (by rfl) ⟨27726, by rfl⟩) R55453
theorem R73955 : Reach 73955 := rs (se 1 (by rfl) ⟨55466, by rfl⟩) R110933
theorem R172259 : Reach 172259 := rs (se 1 (by rfl) ⟨129194, by rfl⟩) R258389
theorem R73985 : Reach 73985 := rs (se 2 (by rfl) ⟨27744, by rfl⟩) R55489
theorem R74003 : Reach 74003 := rs (se 1 (by rfl) ⟨55502, by rfl⟩) R111005
theorem R270641 : Reach 270641 := rs (se 2 (by rfl) ⟨101490, by rfl⟩) R202981
theorem R74033 : Reach 74033 := rs (se 2 (by rfl) ⟨27762, by rfl⟩) R55525
theorem R74051 : Reach 74051 := rs (se 1 (by rfl) ⟨55538, by rfl⟩) R111077
theorem R74081 : Reach 74081 := rs (se 2 (by rfl) ⟨27780, by rfl⟩) R55561
theorem R139619 : Reach 139619 := rs (se 1 (by rfl) ⟨104714, by rfl⟩) R209429
theorem R106865 : Reach 106865 := rs (se 2 (by rfl) ⟨40074, by rfl⟩) R80149
theorem R74099 : Reach 74099 := rs (se 1 (by rfl) ⟨55574, by rfl⟩) R111149
theorem R106883 : Reach 106883 := rs (se 1 (by rfl) ⟨80162, by rfl⟩) R160325
theorem R74129 : Reach 74129 := rs (se 2 (by rfl) ⟨27798, by rfl⟩) R55597
theorem R74147 : Reach 74147 := rs (se 1 (by rfl) ⟨55610, by rfl⟩) R111221
theorem R74177 : Reach 74177 := rs (se 2 (by rfl) ⟨27816, by rfl⟩) R55633
theorem R74195 : Reach 74195 := rs (se 1 (by rfl) ⟨55646, by rfl⟩) R111293
theorem R74225 : Reach 74225 := rs (se 2 (by rfl) ⟨27834, by rfl⟩) R55669
theorem R172529 : Reach 172529 := rs (se 2 (by rfl) ⟨64698, by rfl⟩) R129397
theorem R74243 : Reach 74243 := rs (se 1 (by rfl) ⟨55682, by rfl⟩) R111365
theorem R74273 : Reach 74273 := rs (se 2 (by rfl) ⟨27852, by rfl⟩) R55705
theorem R74291 : Reach 74291 := rs (se 1 (by rfl) ⟨55718, by rfl⟩) R111437
theorem R74321 : Reach 74321 := rs (se 2 (by rfl) ⟨27870, by rfl⟩) R55741
theorem R74339 : Reach 74339 := rs (se 1 (by rfl) ⟨55754, by rfl⟩) R111509
theorem R74369 : Reach 74369 := rs (se 2 (by rfl) ⟨27888, by rfl⟩) R55777
theorem R107153 : Reach 107153 := rs (se 2 (by rfl) ⟨40182, by rfl⟩) R80365
theorem R74387 : Reach 74387 := rs (se 1 (by rfl) ⟨55790, by rfl⟩) R111581
theorem R107171 : Reach 107171 := rs (se 1 (by rfl) ⟨80378, by rfl⟩) R160757
theorem R74417 : Reach 74417 := rs (se 2 (by rfl) ⟨27906, by rfl⟩) R55813
theorem R74435 : Reach 74435 := rs (se 1 (by rfl) ⟨55826, by rfl⟩) R111653
theorem R74465 : Reach 74465 := rs (se 2 (by rfl) ⟨27924, by rfl⟩) R55849
theorem R303857 : Reach 303857 := rs (se 2 (by rfl) ⟨113946, by rfl⟩) R227893
theorem R74483 : Reach 74483 := rs (se 1 (by rfl) ⟨55862, by rfl⟩) R111725
theorem R238349 : Reach 238349 := rs (se 3 (by rfl) ⟨44690, by rfl⟩) R89381
theorem R74513 : Reach 74513 := rs (se 2 (by rfl) ⟨27942, by rfl⟩) R55885
theorem R74531 : Reach 74531 := rs (se 1 (by rfl) ⟨55898, by rfl⟩) R111797
theorem R74561 : Reach 74561 := rs (se 2 (by rfl) ⟨27960, by rfl⟩) R55921
theorem R74579 : Reach 74579 := rs (se 1 (by rfl) ⟨55934, by rfl⟩) R111869
theorem R74609 : Reach 74609 := rs (se 2 (by rfl) ⟨27978, by rfl⟩) R55957
theorem R74627 : Reach 74627 := rs (se 1 (by rfl) ⟨55970, by rfl⟩) R111941
theorem R74657 : Reach 74657 := rs (se 2 (by rfl) ⟨27996, by rfl⟩) R55993
theorem R107441 : Reach 107441 := rs (se 2 (by rfl) ⟨40290, by rfl⟩) R80581
theorem R74675 : Reach 74675 := rs (se 1 (by rfl) ⟨56006, by rfl⟩) R112013
theorem R107459 : Reach 107459 := rs (se 1 (by rfl) ⟨80594, by rfl⟩) R161189
theorem R74705 : Reach 74705 := rs (se 2 (by rfl) ⟨28014, by rfl⟩) R56029
theorem R74723 : Reach 74723 := rs (se 1 (by rfl) ⟨56042, by rfl⟩) R112085
theorem R74753 : Reach 74753 := rs (se 2 (by rfl) ⟨28032, by rfl⟩) R56065
theorem R74771 : Reach 74771 := rs (se 1 (by rfl) ⟨56078, by rfl⟩) R112157
theorem R74801 : Reach 74801 := rs (se 2 (by rfl) ⟨28050, by rfl⟩) R56101
theorem R74819 : Reach 74819 := rs (se 1 (by rfl) ⟨56114, by rfl⟩) R112229
theorem R74849 : Reach 74849 := rs (se 2 (by rfl) ⟨28068, by rfl⟩) R56137
theorem R631907 : Reach 631907 := rs (se 1 (by rfl) ⟨473930, by rfl⟩) R947861
theorem R140401 : Reach 140401 := rs (se 2 (by rfl) ⟨52650, by rfl⟩) R105301
theorem R304241 : Reach 304241 := rs (se 2 (by rfl) ⟨114090, by rfl⟩) R228181
theorem R74867 : Reach 74867 := rs (se 1 (by rfl) ⟨56150, by rfl⟩) R112301
theorem R74897 : Reach 74897 := rs (se 2 (by rfl) ⟨28086, by rfl⟩) R56173
theorem R74915 : Reach 74915 := rs (se 1 (by rfl) ⟨56186, by rfl⟩) R112373
theorem R74945 : Reach 74945 := rs (se 2 (by rfl) ⟨28104, by rfl⟩) R56209
theorem R107729 : Reach 107729 := rs (se 2 (by rfl) ⟨40398, by rfl⟩) R80797
theorem R74963 : Reach 74963 := rs (se 1 (by rfl) ⟨56222, by rfl⟩) R112445
theorem R107747 : Reach 107747 := rs (se 1 (by rfl) ⟨80810, by rfl⟩) R161621
theorem R74993 : Reach 74993 := rs (se 2 (by rfl) ⟨28122, by rfl⟩) R56245
theorem R75011 : Reach 75011 := rs (se 1 (by rfl) ⟨56258, by rfl⟩) R112517
theorem R140561 : Reach 140561 := rs (se 2 (by rfl) ⟨52710, by rfl⟩) R105421
theorem R75041 : Reach 75041 := rs (se 2 (by rfl) ⟨28140, by rfl⟩) R56281
theorem R75059 : Reach 75059 := rs (se 1 (by rfl) ⟨56294, by rfl⟩) R112589
theorem R75089 : Reach 75089 := rs (se 2 (by rfl) ⟨28158, by rfl⟩) R56317
theorem R75107 : Reach 75107 := rs (se 1 (by rfl) ⟨56330, by rfl⟩) R112661
theorem R75137 : Reach 75137 := rs (se 2 (by rfl) ⟨28176, by rfl⟩) R56353
theorem R75155 : Reach 75155 := rs (se 1 (by rfl) ⟨56366, by rfl⟩) R112733
theorem R75185 : Reach 75185 := rs (se 2 (by rfl) ⟨28194, by rfl⟩) R56389
theorem R75203 : Reach 75203 := rs (se 1 (by rfl) ⟨56402, by rfl⟩) R112805
theorem R75233 : Reach 75233 := rs (se 2 (by rfl) ⟨28212, by rfl⟩) R56425
theorem R140771 : Reach 140771 := rs (se 1 (by rfl) ⟨105578, by rfl⟩) R211157
theorem R108017 : Reach 108017 := rs (se 2 (by rfl) ⟨40506, by rfl⟩) R81013
theorem R75251 : Reach 75251 := rs (se 1 (by rfl) ⟨56438, by rfl⟩) R112877
theorem R108035 : Reach 108035 := rs (se 1 (by rfl) ⟨81026, by rfl⟩) R162053
theorem R75281 : Reach 75281 := rs (se 2 (by rfl) ⟨28230, by rfl⟩) R56461
theorem R75299 : Reach 75299 := rs (se 1 (by rfl) ⟨56474, by rfl⟩) R112949
theorem R75329 : Reach 75329 := rs (se 2 (by rfl) ⟨28248, by rfl⟩) R56497
theorem R75347 : Reach 75347 := rs (se 1 (by rfl) ⟨56510, by rfl⟩) R113021
theorem R75377 : Reach 75377 := rs (se 2 (by rfl) ⟨28266, by rfl⟩) R56533
theorem R75395 : Reach 75395 := rs (se 1 (by rfl) ⟨56546, by rfl⟩) R113093
theorem R75425 : Reach 75425 := rs (se 2 (by rfl) ⟨28284, by rfl⟩) R56569
theorem R75443 : Reach 75443 := rs (se 1 (by rfl) ⟨56582, by rfl⟩) R113165
theorem R272069 : Reach 272069 := rs (se 4 (by rfl) ⟨25506, by rfl⟩) R51013
theorem R75473 : Reach 75473 := rs (se 2 (by rfl) ⟨28302, by rfl⟩) R56605
theorem R272099 : Reach 272099 := rs (se 1 (by rfl) ⟨204074, by rfl⟩) R408149
theorem R75491 : Reach 75491 := rs (se 1 (by rfl) ⟨56618, by rfl⟩) R113237
theorem R75521 : Reach 75521 := rs (se 2 (by rfl) ⟨28320, by rfl⟩) R56641
theorem R108305 : Reach 108305 := rs (se 2 (by rfl) ⟨40614, by rfl⟩) R81229
theorem R75539 : Reach 75539 := rs (se 1 (by rfl) ⟨56654, by rfl⟩) R113309
theorem R108323 : Reach 108323 := rs (se 1 (by rfl) ⟨81242, by rfl⟩) R162485
theorem R75569 : Reach 75569 := rs (se 2 (by rfl) ⟨28338, by rfl⟩) R56677
theorem R75587 : Reach 75587 := rs (se 1 (by rfl) ⟨56690, by rfl⟩) R113381
theorem R75617 : Reach 75617 := rs (se 2 (by rfl) ⟨28356, by rfl⟩) R56713
theorem R75635 : Reach 75635 := rs (se 1 (by rfl) ⟨56726, by rfl⟩) R113453
theorem R75665 : Reach 75665 := rs (se 2 (by rfl) ⟨28374, by rfl⟩) R56749
theorem R75683 : Reach 75683 := rs (se 1 (by rfl) ⟨56762, by rfl⟩) R113525
theorem R75713 : Reach 75713 := rs (se 2 (by rfl) ⟨28392, by rfl⟩) R56785
theorem R75731 : Reach 75731 := rs (se 1 (by rfl) ⟨56798, by rfl⟩) R113597
theorem R75761 : Reach 75761 := rs (se 2 (by rfl) ⟨28410, by rfl⟩) R56821
theorem R75779 : Reach 75779 := rs (se 1 (by rfl) ⟨56834, by rfl⟩) R113669
theorem R75809 : Reach 75809 := rs (se 2 (by rfl) ⟨28428, by rfl⟩) R56857
theorem R75811 : Reach 75811 := rs (se 1 (by rfl) ⟨56858, by rfl⟩) R113717
theorem R108593 : Reach 108593 := rs (se 2 (by rfl) ⟨40722, by rfl⟩) R81445
theorem R75827 : Reach 75827 := rs (se 1 (by rfl) ⟨56870, by rfl⟩) R113741
theorem R108611 : Reach 108611 := rs (se 1 (by rfl) ⟨81458, by rfl⟩) R162917
theorem R75857 : Reach 75857 := rs (se 2 (by rfl) ⟨28446, by rfl⟩) R56893
theorem R75875 : Reach 75875 := rs (se 1 (by rfl) ⟨56906, by rfl⟩) R113813
theorem R75905 : Reach 75905 := rs (se 2 (by rfl) ⟨28464, by rfl⟩) R56929
theorem R75907 : Reach 75907 := rs (se 1 (by rfl) ⟨56930, by rfl⟩) R113861
theorem R75923 : Reach 75923 := rs (se 1 (by rfl) ⟨56942, by rfl⟩) R113885
theorem R75953 : Reach 75953 := rs (se 2 (by rfl) ⟨28482, by rfl⟩) R56965
theorem R75971 : Reach 75971 := rs (se 1 (by rfl) ⟨56978, by rfl⟩) R113957
theorem R141517 : Reach 141517 := rs (se 3 (by rfl) ⟨26534, by rfl⟩) R53069
theorem R76001 : Reach 76001 := rs (se 2 (by rfl) ⟨28500, by rfl⟩) R57001
theorem R76019 : Reach 76019 := rs (se 1 (by rfl) ⟨57014, by rfl⟩) R114029
theorem R76049 : Reach 76049 := rs (se 2 (by rfl) ⟨28518, by rfl⟩) R57037
theorem R76067 : Reach 76067 := rs (se 1 (by rfl) ⟨57050, by rfl⟩) R114101
theorem R239921 : Reach 239921 := rs (se 2 (by rfl) ⟨89970, by rfl⟩) R179941
theorem R76097 : Reach 76097 := rs (se 2 (by rfl) ⟨28536, by rfl⟩) R57073
theorem R108881 : Reach 108881 := rs (se 2 (by rfl) ⟨40830, by rfl⟩) R81661
theorem R76115 : Reach 76115 := rs (se 1 (by rfl) ⟨57086, by rfl⟩) R114173
theorem R108899 : Reach 108899 := rs (se 1 (by rfl) ⟨81674, by rfl⟩) R163349
theorem R76145 : Reach 76145 := rs (se 2 (by rfl) ⟨28554, by rfl⟩) R57109
theorem R76163 : Reach 76163 := rs (se 1 (by rfl) ⟨57122, by rfl⟩) R114245
theorem R76193 : Reach 76193 := rs (se 2 (by rfl) ⟨28572, by rfl⟩) R57145
theorem R141745 : Reach 141745 := rs (se 2 (by rfl) ⟨53154, by rfl⟩) R106309
theorem R76211 : Reach 76211 := rs (se 1 (by rfl) ⟨57158, by rfl⟩) R114317
theorem R76241 : Reach 76241 := rs (se 2 (by rfl) ⟨28590, by rfl⟩) R57181
theorem R469475 : Reach 469475 := rs (se 1 (by rfl) ⟨352106, by rfl⟩) R704213
theorem R76259 : Reach 76259 := rs (se 1 (by rfl) ⟨57194, by rfl⟩) R114389
theorem R76289 : Reach 76289 := rs (se 2 (by rfl) ⟨28608, by rfl⟩) R57217
theorem R76291 : Reach 76291 := rs (se 1 (by rfl) ⟨57218, by rfl⟩) R114437
theorem R76307 : Reach 76307 := rs (se 1 (by rfl) ⟨57230, by rfl⟩) R114461
theorem R76337 : Reach 76337 := rs (se 2 (by rfl) ⟨28626, by rfl⟩) R57253
theorem R76355 : Reach 76355 := rs (se 1 (by rfl) ⟨57266, by rfl⟩) R114533
theorem R141905 : Reach 141905 := rs (se 2 (by rfl) ⟨53214, by rfl⟩) R106429
theorem R76385 : Reach 76385 := rs (se 2 (by rfl) ⟨28644, by rfl⟩) R57289
theorem R109169 : Reach 109169 := rs (se 2 (by rfl) ⟨40938, by rfl⟩) R81877
theorem R76403 : Reach 76403 := rs (se 1 (by rfl) ⟨57302, by rfl⟩) R114605
theorem R109187 : Reach 109187 := rs (se 1 (by rfl) ⟨81890, by rfl⟩) R163781
theorem R76433 : Reach 76433 := rs (se 2 (by rfl) ⟨28662, by rfl⟩) R57325
theorem R174755 : Reach 174755 := rs (se 1 (by rfl) ⟨131066, by rfl⟩) R262133
theorem R76451 : Reach 76451 := rs (se 1 (by rfl) ⟨57338, by rfl⟩) R114677
theorem R76481 : Reach 76481 := rs (se 2 (by rfl) ⟨28680, by rfl⟩) R57361
theorem R142019 : Reach 142019 := rs (se 1 (by rfl) ⟨106514, by rfl⟩) R213029
theorem R76499 : Reach 76499 := rs (se 1 (by rfl) ⟨57374, by rfl⟩) R114749
theorem R76529 : Reach 76529 := rs (se 2 (by rfl) ⟨28698, by rfl⟩) R57397
theorem R76547 : Reach 76547 := rs (se 1 (by rfl) ⟨57410, by rfl⟩) R114821
theorem R207629 : Reach 207629 := rs (se 3 (by rfl) ⟨38930, by rfl⟩) R77861
theorem R76577 : Reach 76577 := rs (se 2 (by rfl) ⟨28716, by rfl⟩) R57433
theorem R76595 : Reach 76595 := rs (se 1 (by rfl) ⟨57446, by rfl⟩) R114893
theorem R76625 : Reach 76625 := rs (se 2 (by rfl) ⟨28734, by rfl⟩) R57469
theorem R76643 : Reach 76643 := rs (se 1 (by rfl) ⟨57482, by rfl⟩) R114965
theorem R76673 : Reach 76673 := rs (se 2 (by rfl) ⟨28752, by rfl⟩) R57505
theorem R109457 : Reach 109457 := rs (se 2 (by rfl) ⟨41046, by rfl⟩) R82093
theorem R109475 : Reach 109475 := rs (se 1 (by rfl) ⟨82106, by rfl⟩) R164213
theorem R207971 : Reach 207971 := rs (se 1 (by rfl) ⟨155978, by rfl⟩) R311957
theorem R109667 : Reach 109667 := rs (se 1 (by rfl) ⟨82250, by rfl⟩) R164501
theorem R306317 : Reach 306317 := rs (se 3 (by rfl) ⟨57434, by rfl⟩) R114869
theorem R109745 : Reach 109745 := rs (se 2 (by rfl) ⟨41154, by rfl⟩) R82309
theorem R109763 : Reach 109763 := rs (se 1 (by rfl) ⟨82322, by rfl⟩) R164645
theorem R77041 : Reach 77041 := rs (se 2 (by rfl) ⟨28890, by rfl⟩) R57781
theorem R110033 : Reach 110033 := rs (se 2 (by rfl) ⟨41262, by rfl⟩) R82525
theorem R306659 : Reach 306659 := rs (se 1 (by rfl) ⟨229994, by rfl⟩) R459989
theorem R110051 : Reach 110051 := rs (se 1 (by rfl) ⟨82538, by rfl⟩) R165077
theorem R110083 : Reach 110083 := rs (se 1 (by rfl) ⟨82562, by rfl⟩) R165125
theorem R208433 : Reach 208433 := rs (se 2 (by rfl) ⟨78162, by rfl⟩) R156325
theorem R143021 : Reach 143021 := rs (se 3 (by rfl) ⟨26816, by rfl⟩) R53633
theorem R241379 : Reach 241379 := rs (se 1 (by rfl) ⟨181034, by rfl⟩) R362069
theorem R110321 : Reach 110321 := rs (se 2 (by rfl) ⟨41370, by rfl⟩) R82741
theorem R110339 : Reach 110339 := rs (se 1 (by rfl) ⟨82754, by rfl⟩) R165509
theorem R143203 : Reach 143203 := rs (se 1 (by rfl) ⟨107402, by rfl⟩) R214805
theorem R143363 : Reach 143363 := rs (se 1 (by rfl) ⟨107522, by rfl⟩) R215045
theorem R110609 : Reach 110609 := rs (se 2 (by rfl) ⟨41478, by rfl⟩) R82957
theorem R110627 : Reach 110627 := rs (se 1 (by rfl) ⟨82970, by rfl⟩) R165941
theorem R110897 : Reach 110897 := rs (se 2 (by rfl) ⟨41586, by rfl⟩) R83173
theorem R110915 : Reach 110915 := rs (se 1 (by rfl) ⟨83186, by rfl⟩) R166373
theorem R242189 : Reach 242189 := rs (se 3 (by rfl) ⟨45410, by rfl⟩) R90821
theorem R111185 : Reach 111185 := rs (se 2 (by rfl) ⟨41694, by rfl⟩) R83389
theorem R111203 : Reach 111203 := rs (se 1 (by rfl) ⟨83402, by rfl⟩) R166805
theorem R307889 : Reach 307889 := rs (se 2 (by rfl) ⟨115458, by rfl⟩) R230917
theorem R111299 : Reach 111299 := rs (se 1 (by rfl) ⟨83474, by rfl⟩) R166949
theorem R111473 : Reach 111473 := rs (se 2 (by rfl) ⟨41802, by rfl⟩) R83605
theorem R78707 : Reach 78707 := rs (se 1 (by rfl) ⟨59030, by rfl⟩) R118061
theorem R111491 : Reach 111491 := rs (se 1 (by rfl) ⟨83618, by rfl⟩) R167237
theorem R144337 : Reach 144337 := rs (se 2 (by rfl) ⟨54126, by rfl⟩) R108253
theorem R177137 : Reach 177137 := rs (se 2 (by rfl) ⟨66426, by rfl⟩) R132853
theorem R78835 : Reach 78835 := rs (se 1 (by rfl) ⟨59126, by rfl⟩) R118253
theorem R144433 : Reach 144433 := rs (se 2 (by rfl) ⟨54162, by rfl⟩) R108325
theorem R78899 : Reach 78899 := rs (se 1 (by rfl) ⟨59174, by rfl⟩) R118349
theorem R144497 : Reach 144497 := rs (se 2 (by rfl) ⟨54186, by rfl⟩) R108373
theorem R177265 : Reach 177265 := rs (se 2 (by rfl) ⟨66474, by rfl⟩) R132949
theorem R111761 : Reach 111761 := rs (se 2 (by rfl) ⟨41910, by rfl⟩) R83821
theorem R111779 : Reach 111779 := rs (se 1 (by rfl) ⟨83834, by rfl⟩) R167669
theorem R308549 : Reach 308549 := rs (se 4 (by rfl) ⟨28926, by rfl⟩) R57853
theorem R112049 : Reach 112049 := rs (se 2 (by rfl) ⟨42018, by rfl⟩) R84037
theorem R112067 : Reach 112067 := rs (se 1 (by rfl) ⟨84050, by rfl⟩) R168101
theorem R79393 : Reach 79393 := rs (se 2 (by rfl) ⟨29772, by rfl⟩) R59545
theorem R177713 : Reach 177713 := rs (se 2 (by rfl) ⟨66642, by rfl⟩) R133285
theorem R79555 : Reach 79555 := rs (se 1 (by rfl) ⟨59666, by rfl⟩) R119333
theorem R112337 : Reach 112337 := rs (se 2 (by rfl) ⟨42126, by rfl⟩) R84253
theorem R112355 : Reach 112355 := rs (se 1 (by rfl) ⟨84266, by rfl⟩) R168533
theorem R79697 : Reach 79697 := rs (se 2 (by rfl) ⟨29886, by rfl⟩) R59773
theorem R866189 : Reach 866189 := rs (se 3 (by rfl) ⟨162410, by rfl⟩) R324821
theorem R145297 : Reach 145297 := rs (se 2 (by rfl) ⟨54486, by rfl⟩) R108973
theorem R79825 : Reach 79825 := rs (se 2 (by rfl) ⟨29934, by rfl⟩) R59869
theorem R538595 : Reach 538595 := rs (se 1 (by rfl) ⟨403946, by rfl⟩) R807893
theorem R112625 : Reach 112625 := rs (se 2 (by rfl) ⟨42234, by rfl⟩) R84469
theorem R79859 : Reach 79859 := rs (se 1 (by rfl) ⟨59894, by rfl⟩) R119789
theorem R112643 : Reach 112643 := rs (se 1 (by rfl) ⟨84482, by rfl⟩) R168965
theorem R47123 : Reach 47123 := rs (se 1 (by rfl) ⟨35342, by rfl⟩) R70685
theorem R47139 : Reach 47139 := rs (se 1 (by rfl) ⟨35354, by rfl⟩) R70709
theorem R47155 : Reach 47155 := rs (se 1 (by rfl) ⟨35366, by rfl⟩) R70733
theorem R47171 : Reach 47171 := rs (se 1 (by rfl) ⟨35378, by rfl⟩) R70757
theorem R47187 : Reach 47187 := rs (se 1 (by rfl) ⟨35390, by rfl⟩) R70781
theorem R47203 : Reach 47203 := rs (se 1 (by rfl) ⟨35402, by rfl⟩) R70805
theorem R47219 : Reach 47219 := rs (se 1 (by rfl) ⟨35414, by rfl⟩) R70829
theorem R79987 : Reach 79987 := rs (se 1 (by rfl) ⟨59990, by rfl⟩) R119981
theorem R47235 : Reach 47235 := rs (se 1 (by rfl) ⟨35426, by rfl⟩) R70853
theorem R47251 : Reach 47251 := rs (se 1 (by rfl) ⟨35438, by rfl⟩) R70877
theorem R47267 : Reach 47267 := rs (se 1 (by rfl) ⟨35450, by rfl⟩) R70901
theorem R47283 : Reach 47283 := rs (se 1 (by rfl) ⟨35462, by rfl⟩) R70925
theorem R80065 : Reach 80065 := rs (se 2 (by rfl) ⟨30024, by rfl⟩) R60049
theorem R47299 : Reach 47299 := rs (se 1 (by rfl) ⟨35474, by rfl⟩) R70949
theorem R47315 : Reach 47315 := rs (se 1 (by rfl) ⟨35486, by rfl⟩) R70973
theorem R47331 : Reach 47331 := rs (se 1 (by rfl) ⟨35498, by rfl⟩) R70997
theorem R47347 : Reach 47347 := rs (se 1 (by rfl) ⟨35510, by rfl⟩) R71021
theorem R80129 : Reach 80129 := rs (se 2 (by rfl) ⟨30048, by rfl⟩) R60097
theorem R47363 : Reach 47363 := rs (se 1 (by rfl) ⟨35522, by rfl⟩) R71045
theorem R112913 : Reach 112913 := rs (se 2 (by rfl) ⟨42342, by rfl⟩) R84685
theorem R47379 : Reach 47379 := rs (se 1 (by rfl) ⟨35534, by rfl⟩) R71069
theorem R47395 : Reach 47395 := rs (se 1 (by rfl) ⟨35546, by rfl⟩) R71093
theorem R112931 : Reach 112931 := rs (se 1 (by rfl) ⟨84698, by rfl⟩) R169397
theorem R47411 : Reach 47411 := rs (se 1 (by rfl) ⟨35558, by rfl⟩) R71117
theorem R47427 : Reach 47427 := rs (se 1 (by rfl) ⟨35570, by rfl⟩) R71141
theorem R47443 : Reach 47443 := rs (se 1 (by rfl) ⟨35582, by rfl⟩) R71165
theorem R47459 : Reach 47459 := rs (se 1 (by rfl) ⟨35594, by rfl⟩) R71189
theorem R47475 : Reach 47475 := rs (se 1 (by rfl) ⟨35606, by rfl⟩) R71213
theorem R80257 : Reach 80257 := rs (se 2 (by rfl) ⟨30096, by rfl⟩) R60193
theorem R47491 : Reach 47491 := rs (se 1 (by rfl) ⟨35618, by rfl⟩) R71237
theorem R47507 : Reach 47507 := rs (se 1 (by rfl) ⟨35630, by rfl⟩) R71261
theorem R47523 : Reach 47523 := rs (se 1 (by rfl) ⟨35642, by rfl⟩) R71285
theorem R80291 : Reach 80291 := rs (se 1 (by rfl) ⟨60218, by rfl⟩) R120437
theorem R47539 : Reach 47539 := rs (se 1 (by rfl) ⟨35654, by rfl⟩) R71309
theorem R47555 : Reach 47555 := rs (se 1 (by rfl) ⟨35666, by rfl⟩) R71333
theorem R113105 : Reach 113105 := rs (se 2 (by rfl) ⟨42414, by rfl⟩) R84829
theorem R47571 : Reach 47571 := rs (se 1 (by rfl) ⟨35678, by rfl⟩) R71357
theorem R47587 : Reach 47587 := rs (se 1 (by rfl) ⟨35690, by rfl⟩) R71381
theorem R47603 : Reach 47603 := rs (se 1 (by rfl) ⟨35702, by rfl⟩) R71405
theorem R47619 : Reach 47619 := rs (se 1 (by rfl) ⟨35714, by rfl⟩) R71429
theorem R47635 : Reach 47635 := rs (se 1 (by rfl) ⟨35726, by rfl⟩) R71453
theorem R47651 : Reach 47651 := rs (se 1 (by rfl) ⟨35738, by rfl⟩) R71477
theorem R80419 : Reach 80419 := rs (se 1 (by rfl) ⟨60314, by rfl⟩) R120629
theorem R113201 : Reach 113201 := rs (se 2 (by rfl) ⟨42450, by rfl⟩) R84901
theorem R47667 : Reach 47667 := rs (se 1 (by rfl) ⟨35750, by rfl⟩) R71501
theorem R47683 : Reach 47683 := rs (se 1 (by rfl) ⟨35762, by rfl⟩) R71525
theorem R113219 : Reach 113219 := rs (se 1 (by rfl) ⟨84914, by rfl⟩) R169829
theorem R47699 : Reach 47699 := rs (se 1 (by rfl) ⟨35774, by rfl⟩) R71549
theorem R47715 : Reach 47715 := rs (se 1 (by rfl) ⟨35786, by rfl⟩) R71573
theorem R47731 : Reach 47731 := rs (se 1 (by rfl) ⟨35798, by rfl⟩) R71597
theorem R47747 : Reach 47747 := rs (se 1 (by rfl) ⟨35810, by rfl⟩) R71621
theorem R47763 : Reach 47763 := rs (se 1 (by rfl) ⟨35822, by rfl⟩) R71645
theorem R47779 : Reach 47779 := rs (se 1 (by rfl) ⟨35834, by rfl⟩) R71669
theorem R80561 : Reach 80561 := rs (se 2 (by rfl) ⟨30210, by rfl⟩) R60421
theorem R47795 : Reach 47795 := rs (se 1 (by rfl) ⟨35846, by rfl⟩) R71693
theorem R47811 : Reach 47811 := rs (se 1 (by rfl) ⟨35858, by rfl⟩) R71717
theorem R47827 : Reach 47827 := rs (se 1 (by rfl) ⟨35870, by rfl⟩) R71741
theorem R47843 : Reach 47843 := rs (se 1 (by rfl) ⟨35882, by rfl⟩) R71765
theorem R47859 : Reach 47859 := rs (se 1 (by rfl) ⟨35894, by rfl⟩) R71789
theorem R47875 : Reach 47875 := rs (se 1 (by rfl) ⟨35906, by rfl⟩) R71813
theorem R47891 : Reach 47891 := rs (se 1 (by rfl) ⟨35918, by rfl⟩) R71837
theorem R47907 : Reach 47907 := rs (se 1 (by rfl) ⟨35930, by rfl⟩) R71861
theorem R80689 : Reach 80689 := rs (se 2 (by rfl) ⟨30258, by rfl⟩) R60517
theorem R47923 : Reach 47923 := rs (se 1 (by rfl) ⟨35942, by rfl⟩) R71885
theorem R47939 : Reach 47939 := rs (se 1 (by rfl) ⟨35954, by rfl⟩) R71909
theorem R310085 : Reach 310085 := rs (se 4 (by rfl) ⟨29070, by rfl⟩) R58141
theorem R113489 : Reach 113489 := rs (se 2 (by rfl) ⟨42558, by rfl⟩) R85117
theorem R80723 : Reach 80723 := rs (se 1 (by rfl) ⟨60542, by rfl⟩) R121085
theorem R47955 : Reach 47955 := rs (se 1 (by rfl) ⟨35966, by rfl⟩) R71933
theorem R47971 : Reach 47971 := rs (se 1 (by rfl) ⟨35978, by rfl⟩) R71957
theorem R113507 : Reach 113507 := rs (se 1 (by rfl) ⟨85130, by rfl⟩) R170261
theorem R244579 : Reach 244579 := rs (se 1 (by rfl) ⟨183434, by rfl⟩) R366869
theorem R47987 : Reach 47987 := rs (se 1 (by rfl) ⟨35990, by rfl⟩) R71981
theorem R48003 : Reach 48003 := rs (se 1 (by rfl) ⟨36002, by rfl⟩) R72005
theorem R48019 : Reach 48019 := rs (se 1 (by rfl) ⟨36014, by rfl⟩) R72029
theorem R48035 : Reach 48035 := rs (se 1 (by rfl) ⟨36026, by rfl⟩) R72053
theorem R48051 : Reach 48051 := rs (se 1 (by rfl) ⟨36038, by rfl⟩) R72077
theorem R48067 : Reach 48067 := rs (se 1 (by rfl) ⟨36050, by rfl⟩) R72101
theorem R80851 : Reach 80851 := rs (se 1 (by rfl) ⟨60638, by rfl⟩) R121277
theorem R48083 : Reach 48083 := rs (se 1 (by rfl) ⟨36062, by rfl⟩) R72125
theorem R48099 : Reach 48099 := rs (se 1 (by rfl) ⟨36074, by rfl⟩) R72149
theorem R48115 : Reach 48115 := rs (se 1 (by rfl) ⟨36086, by rfl⟩) R72173
theorem R48131 : Reach 48131 := rs (se 1 (by rfl) ⟨36098, by rfl⟩) R72197
theorem R48147 : Reach 48147 := rs (se 1 (by rfl) ⟨36110, by rfl⟩) R72221
theorem R48163 : Reach 48163 := rs (se 1 (by rfl) ⟨36122, by rfl⟩) R72245
theorem R212003 : Reach 212003 := rs (se 1 (by rfl) ⟨159002, by rfl⟩) R318005
theorem R48179 : Reach 48179 := rs (se 1 (by rfl) ⟨36134, by rfl⟩) R72269
theorem R48195 : Reach 48195 := rs (se 1 (by rfl) ⟨36146, by rfl⟩) R72293
theorem R343109 : Reach 343109 := rs (se 4 (by rfl) ⟨32166, by rfl⟩) R64333
theorem R48211 : Reach 48211 := rs (se 1 (by rfl) ⟨36158, by rfl⟩) R72317
theorem R80993 : Reach 80993 := rs (se 2 (by rfl) ⟨30372, by rfl⟩) R60745
theorem R48227 : Reach 48227 := rs (se 1 (by rfl) ⟨36170, by rfl⟩) R72341
theorem R113777 : Reach 113777 := rs (se 2 (by rfl) ⟨42666, by rfl⟩) R85333
theorem R48243 : Reach 48243 := rs (se 1 (by rfl) ⟨36182, by rfl⟩) R72365
theorem R48259 : Reach 48259 := rs (se 1 (by rfl) ⟨36194, by rfl⟩) R72389
theorem R113795 : Reach 113795 := rs (se 1 (by rfl) ⟨85346, by rfl⟩) R170693
theorem R48275 : Reach 48275 := rs (se 1 (by rfl) ⟨36206, by rfl⟩) R72413
theorem R48291 : Reach 48291 := rs (se 1 (by rfl) ⟨36218, by rfl⟩) R72437
theorem R48307 : Reach 48307 := rs (se 1 (by rfl) ⟨36230, by rfl⟩) R72461
theorem R48323 : Reach 48323 := rs (se 1 (by rfl) ⟨36242, by rfl⟩) R72485
theorem R48339 : Reach 48339 := rs (se 1 (by rfl) ⟨36254, by rfl⟩) R72509
theorem R81121 : Reach 81121 := rs (se 2 (by rfl) ⟨30420, by rfl⟩) R60841
theorem R48355 : Reach 48355 := rs (se 1 (by rfl) ⟨36266, by rfl⟩) R72533
theorem R113891 : Reach 113891 := rs (se 1 (by rfl) ⟨85418, by rfl⟩) R170837
theorem R179441 : Reach 179441 := rs (se 2 (by rfl) ⟨67290, by rfl⟩) R134581
theorem R48371 : Reach 48371 := rs (se 1 (by rfl) ⟨36278, by rfl⟩) R72557
theorem R81155 : Reach 81155 := rs (se 1 (by rfl) ⟨60866, by rfl⟩) R121733
theorem R48387 : Reach 48387 := rs (se 1 (by rfl) ⟨36290, by rfl⟩) R72581
theorem R48403 : Reach 48403 := rs (se 1 (by rfl) ⟨36302, by rfl⟩) R72605
theorem R48419 : Reach 48419 := rs (se 1 (by rfl) ⟨36314, by rfl⟩) R72629
theorem R48435 : Reach 48435 := rs (se 1 (by rfl) ⟨36326, by rfl⟩) R72653
theorem R48451 : Reach 48451 := rs (se 1 (by rfl) ⟨36338, by rfl⟩) R72677
theorem R48467 : Reach 48467 := rs (se 1 (by rfl) ⟨36350, by rfl⟩) R72701
theorem R48483 : Reach 48483 := rs (se 1 (by rfl) ⟨36362, by rfl⟩) R72725
theorem R376163 : Reach 376163 := rs (se 1 (by rfl) ⟨282122, by rfl⟩) R564245
theorem R245105 : Reach 245105 := rs (se 2 (by rfl) ⟨91914, by rfl⟩) R183829
theorem R48499 : Reach 48499 := rs (se 1 (by rfl) ⟨36374, by rfl⟩) R72749
theorem R81283 : Reach 81283 := rs (se 1 (by rfl) ⟨60962, by rfl⟩) R121925
theorem R48515 : Reach 48515 := rs (se 1 (by rfl) ⟨36386, by rfl⟩) R72773
theorem R114065 : Reach 114065 := rs (se 2 (by rfl) ⟨42774, by rfl⟩) R85549
theorem R48531 : Reach 48531 := rs (se 1 (by rfl) ⟨36398, by rfl⟩) R72797
theorem R48547 : Reach 48547 := rs (se 1 (by rfl) ⟨36410, by rfl⟩) R72821
theorem R114083 : Reach 114083 := rs (se 1 (by rfl) ⟨85562, by rfl⟩) R171125
theorem R48563 : Reach 48563 := rs (se 1 (by rfl) ⟨36422, by rfl⟩) R72845
theorem R48579 : Reach 48579 := rs (se 1 (by rfl) ⟨36434, by rfl⟩) R72869
theorem R48595 : Reach 48595 := rs (se 1 (by rfl) ⟨36446, by rfl⟩) R72893
theorem R48611 : Reach 48611 := rs (se 1 (by rfl) ⟨36458, by rfl⟩) R72917
theorem R507377 : Reach 507377 := rs (se 2 (by rfl) ⟨190266, by rfl⟩) R380533
theorem R48627 : Reach 48627 := rs (se 1 (by rfl) ⟨36470, by rfl⟩) R72941
theorem R48643 : Reach 48643 := rs (se 1 (by rfl) ⟨36482, by rfl⟩) R72965
theorem R81425 : Reach 81425 := rs (se 2 (by rfl) ⟨30534, by rfl⟩) R61069
theorem R48659 : Reach 48659 := rs (se 1 (by rfl) ⟨36494, by rfl⟩) R72989
theorem R48675 : Reach 48675 := rs (se 1 (by rfl) ⟨36506, by rfl⟩) R73013
theorem R81443 : Reach 81443 := rs (se 1 (by rfl) ⟨61082, by rfl⟩) R122165
theorem R48691 : Reach 48691 := rs (se 1 (by rfl) ⟨36518, by rfl⟩) R73037
theorem R48707 : Reach 48707 := rs (se 1 (by rfl) ⟨36530, by rfl⟩) R73061
theorem R48723 : Reach 48723 := rs (se 1 (by rfl) ⟨36542, by rfl⟩) R73085
theorem R48739 : Reach 48739 := rs (se 1 (by rfl) ⟨36554, by rfl⟩) R73109
theorem R48755 : Reach 48755 := rs (se 1 (by rfl) ⟨36566, by rfl⟩) R73133
theorem R48771 : Reach 48771 := rs (se 1 (by rfl) ⟨36578, by rfl⟩) R73157
theorem R81553 : Reach 81553 := rs (se 2 (by rfl) ⟨30582, by rfl⟩) R61165
theorem R48787 : Reach 48787 := rs (se 1 (by rfl) ⟨36590, by rfl⟩) R73181
theorem R48803 : Reach 48803 := rs (se 1 (by rfl) ⟨36602, by rfl⟩) R73205
theorem R114353 : Reach 114353 := rs (se 2 (by rfl) ⟨42882, by rfl⟩) R85765
theorem R81587 : Reach 81587 := rs (se 1 (by rfl) ⟨61190, by rfl⟩) R122381
theorem R48819 : Reach 48819 := rs (se 1 (by rfl) ⟨36614, by rfl⟩) R73229
theorem R48835 : Reach 48835 := rs (se 1 (by rfl) ⟨36626, by rfl⟩) R73253
theorem R114371 : Reach 114371 := rs (se 1 (by rfl) ⟨85778, by rfl⟩) R171557
theorem R474821 : Reach 474821 := rs (se 4 (by rfl) ⟨44514, by rfl⟩) R89029
theorem R48851 : Reach 48851 := rs (se 1 (by rfl) ⟨36638, by rfl⟩) R73277
theorem R48867 : Reach 48867 := rs (se 1 (by rfl) ⟨36650, by rfl⟩) R73301
theorem R48883 : Reach 48883 := rs (se 1 (by rfl) ⟨36662, by rfl⟩) R73325
theorem R48899 : Reach 48899 := rs (se 1 (by rfl) ⟨36674, by rfl⟩) R73349
theorem R48915 : Reach 48915 := rs (se 1 (by rfl) ⟨36686, by rfl⟩) R73373
theorem R48931 : Reach 48931 := rs (se 1 (by rfl) ⟨36698, by rfl⟩) R73397
theorem R48947 : Reach 48947 := rs (se 1 (by rfl) ⟨36710, by rfl⟩) R73421
theorem R81715 : Reach 81715 := rs (se 1 (by rfl) ⟨61286, by rfl⟩) R122573
theorem R606005 : Reach 606005 := rs (se 5 (by rfl) ⟨28406, by rfl⟩) R56813
theorem R48963 : Reach 48963 := rs (se 1 (by rfl) ⟨36722, by rfl⟩) R73445
theorem R48979 : Reach 48979 := rs (se 1 (by rfl) ⟨36734, by rfl⟩) R73469
theorem R48995 : Reach 48995 := rs (se 1 (by rfl) ⟨36746, by rfl⟩) R73493
theorem R49011 : Reach 49011 := rs (se 1 (by rfl) ⟨36758, by rfl⟩) R73517
theorem R49027 : Reach 49027 := rs (se 1 (by rfl) ⟨36770, by rfl⟩) R73541
theorem R2015117 : Reach 2015117 := rs (se 3 (by rfl) ⟨377834, by rfl⟩) R755669
theorem R49043 : Reach 49043 := rs (se 1 (by rfl) ⟨36782, by rfl⟩) R73565
theorem R49059 : Reach 49059 := rs (se 1 (by rfl) ⟨36794, by rfl⟩) R73589
theorem R49075 : Reach 49075 := rs (se 1 (by rfl) ⟨36806, by rfl⟩) R73613
theorem R507829 : Reach 507829 := rs (se 5 (by rfl) ⟨23804, by rfl⟩) R47609
theorem R81857 : Reach 81857 := rs (se 2 (by rfl) ⟨30696, by rfl⟩) R61393
theorem R49091 : Reach 49091 := rs (se 1 (by rfl) ⟨36818, by rfl⟩) R73637
theorem R81859 : Reach 81859 := rs (se 1 (by rfl) ⟨61394, by rfl⟩) R122789
theorem R114641 : Reach 114641 := rs (se 2 (by rfl) ⟨42990, by rfl⟩) R85981
theorem R49107 : Reach 49107 := rs (se 1 (by rfl) ⟨36830, by rfl⟩) R73661
theorem R114659 : Reach 114659 := rs (se 1 (by rfl) ⟨85994, by rfl⟩) R171989
theorem R49123 : Reach 49123 := rs (se 1 (by rfl) ⟨36842, by rfl⟩) R73685
theorem R49139 : Reach 49139 := rs (se 1 (by rfl) ⟨36854, by rfl⟩) R73709
theorem R49155 : Reach 49155 := rs (se 1 (by rfl) ⟨36866, by rfl⟩) R73733
theorem R49171 : Reach 49171 := rs (se 1 (by rfl) ⟨36878, by rfl⟩) R73757
theorem R49187 : Reach 49187 := rs (se 1 (by rfl) ⟨36890, by rfl⟩) R73781
theorem R49203 : Reach 49203 := rs (se 1 (by rfl) ⟨36902, by rfl⟩) R73805
theorem R81985 : Reach 81985 := rs (se 2 (by rfl) ⟨30744, by rfl⟩) R61489
theorem R49219 : Reach 49219 := rs (se 1 (by rfl) ⟨36914, by rfl⟩) R73829
theorem R49235 : Reach 49235 := rs (se 1 (by rfl) ⟨36926, by rfl⟩) R73853
theorem R82019 : Reach 82019 := rs (se 1 (by rfl) ⟨61514, by rfl⟩) R123029
theorem R49251 : Reach 49251 := rs (se 1 (by rfl) ⟨36938, by rfl⟩) R73877
theorem R147565 : Reach 147565 := rs (se 3 (by rfl) ⟨27668, by rfl⟩) R55337
theorem R49267 : Reach 49267 := rs (se 1 (by rfl) ⟨36950, by rfl⟩) R73901
theorem R49283 : Reach 49283 := rs (se 1 (by rfl) ⟨36962, by rfl⟩) R73925
theorem R49299 : Reach 49299 := rs (se 1 (by rfl) ⟨36974, by rfl⟩) R73949
theorem R49315 : Reach 49315 := rs (se 1 (by rfl) ⟨36986, by rfl⟩) R73973
theorem R49331 : Reach 49331 := rs (se 1 (by rfl) ⟨36998, by rfl⟩) R73997
theorem R49347 : Reach 49347 := rs (se 1 (by rfl) ⟨37010, by rfl⟩) R74021
theorem R49363 : Reach 49363 := rs (se 1 (by rfl) ⟨37022, by rfl⟩) R74045
theorem R82147 : Reach 82147 := rs (se 1 (by rfl) ⟨61610, by rfl⟩) R123221
theorem R49379 : Reach 49379 := rs (se 1 (by rfl) ⟨37034, by rfl⟩) R74069
theorem R114929 : Reach 114929 := rs (se 2 (by rfl) ⟨43098, by rfl⟩) R86197
theorem R49395 : Reach 49395 := rs (se 1 (by rfl) ⟨37046, by rfl⟩) R74093
theorem R49411 : Reach 49411 := rs (se 1 (by rfl) ⟨37058, by rfl⟩) R74117
theorem R114947 : Reach 114947 := rs (se 1 (by rfl) ⟨86210, by rfl⟩) R172421
theorem R49427 : Reach 49427 := rs (se 1 (by rfl) ⟨37070, by rfl⟩) R74141
theorem R49443 : Reach 49443 := rs (se 1 (by rfl) ⟨37082, by rfl⟩) R74165
theorem R49459 : Reach 49459 := rs (se 1 (by rfl) ⟨37094, by rfl⟩) R74189
theorem R49475 : Reach 49475 := rs (se 1 (by rfl) ⟨37106, by rfl⟩) R74213
theorem R49491 : Reach 49491 := rs (se 1 (by rfl) ⟨37118, by rfl⟩) R74237
theorem R49507 : Reach 49507 := rs (se 1 (by rfl) ⟨37130, by rfl⟩) R74261
theorem R82289 : Reach 82289 := rs (se 2 (by rfl) ⟨30858, by rfl⟩) R61717
theorem R49523 : Reach 49523 := rs (se 1 (by rfl) ⟨37142, by rfl⟩) R74285
theorem R49539 : Reach 49539 := rs (se 1 (by rfl) ⟨37154, by rfl⟩) R74309
theorem R49555 : Reach 49555 := rs (se 1 (by rfl) ⟨37166, by rfl⟩) R74333
theorem R49571 : Reach 49571 := rs (se 1 (by rfl) ⟨37178, by rfl⟩) R74357
theorem R49587 : Reach 49587 := rs (se 1 (by rfl) ⟨37190, by rfl⟩) R74381
theorem R49603 : Reach 49603 := rs (se 1 (by rfl) ⟨37202, by rfl⟩) R74405
theorem R49619 : Reach 49619 := rs (se 1 (by rfl) ⟨37214, by rfl⟩) R74429
theorem R49635 : Reach 49635 := rs (se 1 (by rfl) ⟨37226, by rfl⟩) R74453
theorem R82417 : Reach 82417 := rs (se 2 (by rfl) ⟨30906, by rfl⟩) R61813
theorem R49651 : Reach 49651 := rs (se 1 (by rfl) ⟨37238, by rfl⟩) R74477
theorem R49667 : Reach 49667 := rs (se 1 (by rfl) ⟨37250, by rfl⟩) R74501
theorem R82451 : Reach 82451 := rs (se 1 (by rfl) ⟨61838, by rfl⟩) R123677
theorem R49683 : Reach 49683 := rs (se 1 (by rfl) ⟨37262, by rfl⟩) R74525
theorem R49699 : Reach 49699 := rs (se 1 (by rfl) ⟨37274, by rfl⟩) R74549
theorem R49715 : Reach 49715 := rs (se 1 (by rfl) ⟨37286, by rfl⟩) R74573
theorem R49731 : Reach 49731 := rs (se 1 (by rfl) ⟨37298, by rfl⟩) R74597
theorem R49747 : Reach 49747 := rs (se 1 (by rfl) ⟨37310, by rfl⟩) R74621
theorem R49763 : Reach 49763 := rs (se 1 (by rfl) ⟨37322, by rfl⟩) R74645
theorem R49779 : Reach 49779 := rs (se 1 (by rfl) ⟨37334, by rfl⟩) R74669
theorem R49795 : Reach 49795 := rs (se 1 (by rfl) ⟨37346, by rfl⟩) R74693
theorem R82579 : Reach 82579 := rs (se 1 (by rfl) ⟨61934, by rfl⟩) R123869
theorem R49811 : Reach 49811 := rs (se 1 (by rfl) ⟨37358, by rfl⟩) R74717
theorem R180899 : Reach 180899 := rs (se 1 (by rfl) ⟨135674, by rfl⟩) R271349
theorem R49827 : Reach 49827 := rs (se 1 (by rfl) ⟨37370, by rfl⟩) R74741
theorem R180913 : Reach 180913 := rs (se 2 (by rfl) ⟨67842, by rfl⟩) R135685
theorem R49843 : Reach 49843 := rs (se 1 (by rfl) ⟨37382, by rfl⟩) R74765
theorem R49859 : Reach 49859 := rs (se 1 (by rfl) ⟨37394, by rfl⟩) R74789
theorem R49875 : Reach 49875 := rs (se 1 (by rfl) ⟨37406, by rfl⟩) R74813
theorem R49891 : Reach 49891 := rs (se 1 (by rfl) ⟨37418, by rfl⟩) R74837
theorem R49907 : Reach 49907 := rs (se 1 (by rfl) ⟨37430, by rfl⟩) R74861
theorem R49923 : Reach 49923 := rs (se 1 (by rfl) ⟨37442, by rfl⟩) R74885
theorem R49939 : Reach 49939 := rs (se 1 (by rfl) ⟨37454, by rfl⟩) R74909
theorem R82721 : Reach 82721 := rs (se 2 (by rfl) ⟨31020, by rfl⟩) R62041
theorem R246563 : Reach 246563 := rs (se 1 (by rfl) ⟨184922, by rfl⟩) R369845
theorem R49955 : Reach 49955 := rs (se 1 (by rfl) ⟨37466, by rfl⟩) R74933
theorem R49971 : Reach 49971 := rs (se 1 (by rfl) ⟨37478, by rfl⟩) R74957
theorem R115523 : Reach 115523 := rs (se 1 (by rfl) ⟨86642, by rfl⟩) R173285
theorem R49987 : Reach 49987 := rs (se 1 (by rfl) ⟨37490, by rfl⟩) R74981
theorem R50003 : Reach 50003 := rs (se 1 (by rfl) ⟨37502, by rfl⟩) R75005
theorem R50019 : Reach 50019 := rs (se 1 (by rfl) ⟨37514, by rfl⟩) R75029
theorem R50035 : Reach 50035 := rs (se 1 (by rfl) ⟨37526, by rfl⟩) R75053
theorem R50051 : Reach 50051 := rs (se 1 (by rfl) ⟨37538, by rfl⟩) R75077
theorem R50067 : Reach 50067 := rs (se 1 (by rfl) ⟨37550, by rfl⟩) R75101
theorem R82849 : Reach 82849 := rs (se 2 (by rfl) ⟨31068, by rfl⟩) R62137
theorem R50083 : Reach 50083 := rs (se 1 (by rfl) ⟨37562, by rfl⟩) R75125
theorem R50099 : Reach 50099 := rs (se 1 (by rfl) ⟨37574, by rfl⟩) R75149
theorem R82883 : Reach 82883 := rs (se 1 (by rfl) ⟨62162, by rfl⟩) R124325
theorem R50115 : Reach 50115 := rs (se 1 (by rfl) ⟨37586, by rfl⟩) R75173
theorem R50131 : Reach 50131 := rs (se 1 (by rfl) ⟨37598, by rfl⟩) R75197
theorem R50147 : Reach 50147 := rs (se 1 (by rfl) ⟨37610, by rfl⟩) R75221
theorem R410609 : Reach 410609 := rs (se 2 (by rfl) ⟨153978, by rfl⟩) R307957
theorem R50163 : Reach 50163 := rs (se 1 (by rfl) ⟨37622, by rfl⟩) R75245
theorem R115715 : Reach 115715 := rs (se 1 (by rfl) ⟨86786, by rfl⟩) R173573
theorem R50179 : Reach 50179 := rs (se 1 (by rfl) ⟨37634, by rfl⟩) R75269
theorem R50195 : Reach 50195 := rs (se 1 (by rfl) ⟨37646, by rfl⟩) R75293
theorem R50211 : Reach 50211 := rs (se 1 (by rfl) ⟨37658, by rfl⟩) R75317
theorem R50227 : Reach 50227 := rs (se 1 (by rfl) ⟨37670, by rfl⟩) R75341
theorem R83011 : Reach 83011 := rs (se 1 (by rfl) ⟨62258, by rfl⟩) R124517
theorem R50243 : Reach 50243 := rs (se 1 (by rfl) ⟨37682, by rfl⟩) R75365
theorem R115793 : Reach 115793 := rs (se 2 (by rfl) ⟨43422, by rfl⟩) R86845
theorem R50259 : Reach 50259 := rs (se 1 (by rfl) ⟨37694, by rfl⟩) R75389
theorem R50275 : Reach 50275 := rs (se 1 (by rfl) ⟨37706, by rfl⟩) R75413
theorem R50291 : Reach 50291 := rs (se 1 (by rfl) ⟨37718, by rfl⟩) R75437
theorem R50307 : Reach 50307 := rs (se 1 (by rfl) ⟨37730, by rfl⟩) R75461
theorem R50323 : Reach 50323 := rs (se 1 (by rfl) ⟨37742, by rfl⟩) R75485
theorem R50339 : Reach 50339 := rs (se 1 (by rfl) ⟨37754, by rfl⟩) R75509
theorem R50355 : Reach 50355 := rs (se 1 (by rfl) ⟨37766, by rfl⟩) R75533
theorem R50371 : Reach 50371 := rs (se 1 (by rfl) ⟨37778, by rfl⟩) R75557
theorem R83153 : Reach 83153 := rs (se 2 (by rfl) ⟨31182, by rfl⟩) R62365
theorem R50387 : Reach 50387 := rs (se 1 (by rfl) ⟨37790, by rfl⟩) R75581
theorem R50403 : Reach 50403 := rs (se 1 (by rfl) ⟨37802, by rfl⟩) R75605
theorem R50419 : Reach 50419 := rs (se 1 (by rfl) ⟨37814, by rfl⟩) R75629
theorem R50435 : Reach 50435 := rs (se 1 (by rfl) ⟨37826, by rfl⟩) R75653
theorem R50451 : Reach 50451 := rs (se 1 (by rfl) ⟨37838, by rfl⟩) R75677
theorem R50467 : Reach 50467 := rs (se 1 (by rfl) ⟨37850, by rfl⟩) R75701
theorem R50483 : Reach 50483 := rs (se 1 (by rfl) ⟨37862, by rfl⟩) R75725
theorem R50499 : Reach 50499 := rs (se 1 (by rfl) ⟨37874, by rfl⟩) R75749
theorem R83281 : Reach 83281 := rs (se 2 (by rfl) ⟨31230, by rfl⟩) R62461
theorem R50515 : Reach 50515 := rs (se 1 (by rfl) ⟨37886, by rfl⟩) R75773
theorem R50531 : Reach 50531 := rs (se 1 (by rfl) ⟨37898, by rfl⟩) R75797
theorem R83315 : Reach 83315 := rs (se 1 (by rfl) ⟨62486, by rfl⟩) R124973
theorem R50547 : Reach 50547 := rs (se 1 (by rfl) ⟨37910, by rfl⟩) R75821
theorem R50563 : Reach 50563 := rs (se 1 (by rfl) ⟨37922, by rfl⟩) R75845
theorem R181645 : Reach 181645 := rs (se 3 (by rfl) ⟨34058, by rfl⟩) R68117
theorem R50579 : Reach 50579 := rs (se 1 (by rfl) ⟨37934, by rfl⟩) R75869
theorem R50595 : Reach 50595 := rs (se 1 (by rfl) ⟨37946, by rfl⟩) R75893
theorem R50611 : Reach 50611 := rs (se 1 (by rfl) ⟨37958, by rfl⟩) R75917
theorem R50627 : Reach 50627 := rs (se 1 (by rfl) ⟨37970, by rfl⟩) R75941
theorem R50643 : Reach 50643 := rs (se 1 (by rfl) ⟨37982, by rfl⟩) R75965
theorem R50659 : Reach 50659 := rs (se 1 (by rfl) ⟨37994, by rfl⟩) R75989
theorem R83443 : Reach 83443 := rs (se 1 (by rfl) ⟨62582, by rfl⟩) R125165
theorem R50675 : Reach 50675 := rs (se 1 (by rfl) ⟨38006, by rfl⟩) R76013
theorem R50691 : Reach 50691 := rs (se 1 (by rfl) ⟨38018, by rfl⟩) R76037
theorem R50707 : Reach 50707 := rs (se 1 (by rfl) ⟨38030, by rfl⟩) R76061
theorem R50723 : Reach 50723 := rs (se 1 (by rfl) ⟨38042, by rfl⟩) R76085
theorem R50739 : Reach 50739 := rs (se 1 (by rfl) ⟨38054, by rfl⟩) R76109
theorem R50755 : Reach 50755 := rs (se 1 (by rfl) ⟨38066, by rfl⟩) R76133
theorem R247373 : Reach 247373 := rs (se 3 (by rfl) ⟨46382, by rfl⟩) R92765
theorem R50771 : Reach 50771 := rs (se 1 (by rfl) ⟨38078, by rfl⟩) R76157
theorem R50787 : Reach 50787 := rs (se 1 (by rfl) ⟨38090, by rfl⟩) R76181
theorem R50803 : Reach 50803 := rs (se 1 (by rfl) ⟨38102, by rfl⟩) R76205
theorem R83585 : Reach 83585 := rs (se 2 (by rfl) ⟨31344, by rfl⟩) R62689
theorem R50819 : Reach 50819 := rs (se 1 (by rfl) ⟨38114, by rfl⟩) R76229
theorem R50835 : Reach 50835 := rs (se 1 (by rfl) ⟨38126, by rfl⟩) R76253
theorem R50851 : Reach 50851 := rs (se 1 (by rfl) ⟨38138, by rfl⟩) R76277
theorem R50867 : Reach 50867 := rs (se 1 (by rfl) ⟨38150, by rfl⟩) R76301
theorem R50883 : Reach 50883 := rs (se 1 (by rfl) ⟨38162, by rfl⟩) R76325
theorem R50899 : Reach 50899 := rs (se 1 (by rfl) ⟨38174, by rfl⟩) R76349
theorem R50915 : Reach 50915 := rs (se 1 (by rfl) ⟨38186, by rfl⟩) R76373
theorem R50931 : Reach 50931 := rs (se 1 (by rfl) ⟨38198, by rfl⟩) R76397
theorem R83713 : Reach 83713 := rs (se 2 (by rfl) ⟨31392, by rfl⟩) R62785
theorem R50947 : Reach 50947 := rs (se 1 (by rfl) ⟨38210, by rfl⟩) R76421
theorem R50963 : Reach 50963 := rs (se 1 (by rfl) ⟨38222, by rfl⟩) R76445
theorem R83747 : Reach 83747 := rs (se 1 (by rfl) ⟨62810, by rfl⟩) R125621
theorem R50979 : Reach 50979 := rs (se 1 (by rfl) ⟨38234, by rfl⟩) R76469
theorem R50995 : Reach 50995 := rs (se 1 (by rfl) ⟨38246, by rfl⟩) R76493
theorem R51011 : Reach 51011 := rs (se 1 (by rfl) ⟨38258, by rfl⟩) R76517
theorem R116561 : Reach 116561 := rs (se 2 (by rfl) ⟨43710, by rfl⟩) R87421
theorem R51027 : Reach 51027 := rs (se 1 (by rfl) ⟨38270, by rfl⟩) R76541
theorem R51043 : Reach 51043 := rs (se 1 (by rfl) ⟨38282, by rfl⟩) R76565
theorem R51059 : Reach 51059 := rs (se 1 (by rfl) ⟨38294, by rfl⟩) R76589
theorem R51075 : Reach 51075 := rs (se 1 (by rfl) ⟨38306, by rfl⟩) R76613
theorem R51091 : Reach 51091 := rs (se 1 (by rfl) ⟨38318, by rfl⟩) R76637
theorem R83875 : Reach 83875 := rs (se 1 (by rfl) ⟨62906, by rfl⟩) R125813
theorem R51107 : Reach 51107 := rs (se 1 (by rfl) ⟨38330, by rfl⟩) R76661
theorem R116657 : Reach 116657 := rs (se 2 (by rfl) ⟨43746, by rfl⟩) R87493
theorem R84017 : Reach 84017 := rs (se 2 (by rfl) ⟨31506, by rfl⟩) R63013
theorem R182371 : Reach 182371 := rs (se 1 (by rfl) ⟨136778, by rfl⟩) R273557
theorem R84145 : Reach 84145 := rs (se 2 (by rfl) ⟨31554, by rfl⟩) R63109
theorem R215245 : Reach 215245 := rs (se 3 (by rfl) ⟨40358, by rfl⟩) R80717
theorem R182513 : Reach 182513 := rs (se 2 (by rfl) ⟨68442, by rfl⟩) R136885
theorem R182627 : Reach 182627 := rs (se 1 (by rfl) ⟨136970, by rfl⟩) R273941
theorem R1034693 : Reach 1034693 := rs (se 4 (by rfl) ⟨97002, by rfl⟩) R194005
theorem R281029 : Reach 281029 := rs (se 4 (by rfl) ⟨26346, by rfl⟩) R52693
theorem R84611 : Reach 84611 := rs (se 1 (by rfl) ⟨63458, by rfl⟩) R126917
theorem R215693 : Reach 215693 := rs (se 3 (by rfl) ⟨40442, by rfl⟩) R80885
theorem R215729 : Reach 215729 := rs (se 2 (by rfl) ⟨80898, by rfl⟩) R161797
theorem R84739 : Reach 84739 := rs (se 1 (by rfl) ⟨63554, by rfl⟩) R127109
theorem R84881 : Reach 84881 := rs (se 2 (by rfl) ⟨31830, by rfl⟩) R63661
theorem R52211 : Reach 52211 := rs (se 1 (by rfl) ⟨39158, by rfl⟩) R78317
theorem R85009 : Reach 85009 := rs (se 2 (by rfl) ⟨31878, by rfl⟩) R63757
theorem R85187 : Reach 85187 := rs (se 1 (by rfl) ⟨63890, by rfl⟩) R127781
theorem R85475 : Reach 85475 := rs (se 1 (by rfl) ⟨64106, by rfl⟩) R128213
theorem R151025 : Reach 151025 := rs (se 2 (by rfl) ⟨56634, by rfl⟩) R113269
theorem R85603 : Reach 85603 := rs (se 1 (by rfl) ⟨64202, by rfl⟩) R128405
theorem R1199843 : Reach 1199843 := rs (se 1 (by rfl) ⟨899882, by rfl⟩) R1799765
theorem R85745 : Reach 85745 := rs (se 2 (by rfl) ⟨32154, by rfl⟩) R64309
theorem R151313 : Reach 151313 := rs (se 2 (by rfl) ⟨56742, by rfl⟩) R113485
theorem R53059 : Reach 53059 := rs (se 1 (by rfl) ⟨39794, by rfl⟩) R79589
theorem R85873 : Reach 85873 := rs (se 2 (by rfl) ⟨32202, by rfl⟩) R64405
theorem R53203 : Reach 53203 := rs (se 1 (by rfl) ⟨39902, by rfl⟩) R79805
theorem R53347 : Reach 53347 := rs (se 1 (by rfl) ⟨40010, by rfl⟩) R80021
theorem R151757 : Reach 151757 := rs (se 3 (by rfl) ⟨28454, by rfl⟩) R56909
theorem R53491 : Reach 53491 := rs (se 1 (by rfl) ⟨40118, by rfl⟩) R80237
theorem R184589 : Reach 184589 := rs (se 3 (by rfl) ⟨34610, by rfl⟩) R69221
theorem R53635 : Reach 53635 := rs (se 1 (by rfl) ⟨40226, by rfl⟩) R80453
theorem R283013 : Reach 283013 := rs (se 4 (by rfl) ⟨26532, by rfl⟩) R53065
theorem R250289 : Reach 250289 := rs (se 2 (by rfl) ⟨93858, by rfl⟩) R187717
theorem R53779 : Reach 53779 := rs (se 1 (by rfl) ⟨40334, by rfl⟩) R80669
theorem R381509 : Reach 381509 := rs (se 4 (by rfl) ⟨35766, by rfl⟩) R71533
theorem R53923 : Reach 53923 := rs (se 1 (by rfl) ⟨40442, by rfl⟩) R80885
theorem R54067 : Reach 54067 := rs (se 1 (by rfl) ⟨40550, by rfl⟩) R81101
theorem R54211 : Reach 54211 := rs (se 1 (by rfl) ⟨40658, by rfl⟩) R81317
theorem R54227 : Reach 54227 := rs (se 1 (by rfl) ⟨40670, by rfl⟩) R81341
theorem R87011 : Reach 87011 := rs (se 1 (by rfl) ⟨65258, by rfl⟩) R130517
theorem R54355 : Reach 54355 := rs (se 1 (by rfl) ⟨40766, by rfl⟩) R81533
theorem R54499 : Reach 54499 := rs (se 1 (by rfl) ⟨40874, by rfl⟩) R81749
theorem R120113 : Reach 120113 := rs (se 2 (by rfl) ⟨45042, by rfl⟩) R90085
theorem R120163 : Reach 120163 := rs (se 1 (by rfl) ⟨90122, by rfl⟩) R180245
theorem R54643 : Reach 54643 := rs (se 1 (by rfl) ⟨40982, by rfl⟩) R81965
theorem R87473 : Reach 87473 := rs (se 2 (by rfl) ⟨32802, by rfl⟩) R65605
theorem R120305 : Reach 120305 := rs (se 2 (by rfl) ⟨45114, by rfl⟩) R90229
theorem R54787 : Reach 54787 := rs (se 1 (by rfl) ⟨41090, by rfl⟩) R82181
theorem R218659 : Reach 218659 := rs (se 1 (by rfl) ⟨163994, by rfl⟩) R327989
theorem R54883 : Reach 54883 := rs (se 1 (by rfl) ⟨41162, by rfl⟩) R82325
theorem R54931 : Reach 54931 := rs (se 1 (by rfl) ⟨41198, by rfl⟩) R82397
theorem R153361 : Reach 153361 := rs (se 2 (by rfl) ⟨57510, by rfl⟩) R115021
theorem R55075 : Reach 55075 := rs (se 1 (by rfl) ⟨41306, by rfl⟩) R82613
theorem R251747 : Reach 251747 := rs (se 1 (by rfl) ⟨188810, by rfl⟩) R377621
theorem R55219 : Reach 55219 := rs (se 1 (by rfl) ⟨41414, by rfl⟩) R82829
theorem R251909 : Reach 251909 := rs (se 4 (by rfl) ⟨23616, by rfl⟩) R47233
theorem R55363 : Reach 55363 := rs (se 1 (by rfl) ⟨41522, by rfl⟩) R83045
theorem R547013 : Reach 547013 := rs (se 4 (by rfl) ⟨51282, by rfl⟩) R102565
theorem R55507 : Reach 55507 := rs (se 1 (by rfl) ⟨41630, by rfl⟩) R83261
theorem R55651 : Reach 55651 := rs (se 1 (by rfl) ⟨41738, by rfl⟩) R83477
theorem R121297 : Reach 121297 := rs (se 2 (by rfl) ⟨45486, by rfl⟩) R90973
theorem R55795 : Reach 55795 := rs (se 1 (by rfl) ⟨41846, by rfl⟩) R83693
theorem R88625 : Reach 88625 := rs (se 2 (by rfl) ⟨33234, by rfl⟩) R66469
theorem R55939 : Reach 55939 := rs (se 1 (by rfl) ⟨41954, by rfl⟩) R83909
theorem R252557 : Reach 252557 := rs (se 3 (by rfl) ⟨47354, by rfl⟩) R94709
theorem R121571 : Reach 121571 := rs (se 1 (by rfl) ⟨91178, by rfl⟩) R182357
theorem R56083 : Reach 56083 := rs (se 1 (by rfl) ⟨42062, by rfl⟩) R84125
theorem R1334069 : Reach 1334069 := rs (se 5 (by rfl) ⟨62534, by rfl⟩) R125069
theorem R121763 : Reach 121763 := rs (se 1 (by rfl) ⟨91322, by rfl⟩) R182645
theorem R56227 : Reach 56227 := rs (se 1 (by rfl) ⟨42170, by rfl⟩) R84341
theorem R56371 : Reach 56371 := rs (se 1 (by rfl) ⟨42278, by rfl⟩) R84557
theorem R154723 : Reach 154723 := rs (se 1 (by rfl) ⟨116042, by rfl⟩) R232085
theorem R187505 : Reach 187505 := rs (se 2 (by rfl) ⟨70314, by rfl⟩) R140629
theorem R56515 : Reach 56515 := rs (se 1 (by rfl) ⟨42386, by rfl⟩) R84773
theorem R56659 : Reach 56659 := rs (se 1 (by rfl) ⟨42494, by rfl⟩) R84989
theorem R154993 : Reach 154993 := rs (se 2 (by rfl) ⟨58122, by rfl⟩) R116245
theorem R253381 : Reach 253381 := rs (se 4 (by rfl) ⟨23754, by rfl⟩) R47509
theorem R56803 : Reach 56803 := rs (se 1 (by rfl) ⟨42602, by rfl⟩) R85205
theorem R56947 : Reach 56947 := rs (se 1 (by rfl) ⟨42710, by rfl⟩) R85421
theorem R57091 : Reach 57091 := rs (se 1 (by rfl) ⟨42818, by rfl⟩) R85637
theorem R122627 : Reach 122627 := rs (se 1 (by rfl) ⟨91970, by rfl⟩) R183941
theorem R122705 : Reach 122705 := rs (se 2 (by rfl) ⟨46014, by rfl⟩) R92029
theorem R122755 : Reach 122755 := rs (se 1 (by rfl) ⟨92066, by rfl⟩) R184133
theorem R90001 : Reach 90001 := rs (se 2 (by rfl) ⟨33750, by rfl⟩) R67501
theorem R57235 : Reach 57235 := rs (se 1 (by rfl) ⟨42926, by rfl⟩) R85853
theorem R57251 : Reach 57251 := rs (se 1 (by rfl) ⟨42938, by rfl⟩) R85877
theorem R122897 : Reach 122897 := rs (se 2 (by rfl) ⟨46086, by rfl⟩) R92173
theorem R57379 : Reach 57379 := rs (se 1 (by rfl) ⟨43034, by rfl⟩) R86069
theorem R286861 : Reach 286861 := rs (se 3 (by rfl) ⟨53786, by rfl⟩) R107573
theorem R188963 : Reach 188963 := rs (se 1 (by rfl) ⟨141722, by rfl⟩) R283445
theorem R91057 : Reach 91057 := rs (se 2 (by rfl) ⟨34146, by rfl⟩) R68293
theorem R156593 : Reach 156593 := rs (se 2 (by rfl) ⟨58722, by rfl⟩) R117445
theorem R123889 : Reach 123889 := rs (se 2 (by rfl) ⟨46458, by rfl⟩) R92917
theorem R124145 : Reach 124145 := rs (se 2 (by rfl) ⟨46554, by rfl⟩) R93109
theorem R124163 : Reach 124163 := rs (se 1 (by rfl) ⟨93122, by rfl⟩) R186245
theorem R156941 : Reach 156941 := rs (se 3 (by rfl) ⟨29426, by rfl⟩) R58853
theorem R517429 : Reach 517429 := rs (se 5 (by rfl) ⟨24254, by rfl⟩) R48509
theorem R877877 : Reach 877877 := rs (se 5 (by rfl) ⟨41150, by rfl⟩) R82301
theorem R91459 : Reach 91459 := rs (se 1 (by rfl) ⟨68594, by rfl⟩) R137189
theorem R91505 : Reach 91505 := rs (se 2 (by rfl) ⟨34314, by rfl⟩) R68629
theorem R58819 : Reach 58819 := rs (se 1 (by rfl) ⟨44114, by rfl⟩) R88229
theorem R124355 : Reach 124355 := rs (se 1 (by rfl) ⟨93266, by rfl⟩) R186533
theorem R255473 : Reach 255473 := rs (se 2 (by rfl) ⟨95802, by rfl⟩) R191605
theorem R189965 : Reach 189965 := rs (se 3 (by rfl) ⟨35618, by rfl⟩) R71237
theorem R91793 : Reach 91793 := rs (se 2 (by rfl) ⟨34422, by rfl⟩) R68845
theorem R59203 : Reach 59203 := rs (se 1 (by rfl) ⟨44402, by rfl⟩) R88805
theorem R288845 : Reach 288845 := rs (se 3 (by rfl) ⟨54158, by rfl⟩) R108317
theorem R583861 : Reach 583861 := rs (se 5 (by rfl) ⟨27368, by rfl⟩) R54737
theorem R387341 : Reach 387341 := rs (se 3 (by rfl) ⟨72626, by rfl⟩) R145253
theorem R223523 : Reach 223523 := rs (se 1 (by rfl) ⟨167642, by rfl⟩) R335285
theorem R92515 : Reach 92515 := rs (se 1 (by rfl) ⟨69386, by rfl⟩) R138773
theorem R125297 : Reach 125297 := rs (se 2 (by rfl) ⟨46986, by rfl⟩) R93973
theorem R125347 : Reach 125347 := rs (se 1 (by rfl) ⟨94010, by rfl⟩) R188021
theorem R256547 : Reach 256547 := rs (se 1 (by rfl) ⟨192410, by rfl⟩) R384821
theorem R125489 : Reach 125489 := rs (se 2 (by rfl) ⟨47058, by rfl⟩) R94117
theorem R453347 : Reach 453347 := rs (se 1 (by rfl) ⟨340010, by rfl⟩) R680021
theorem R322309 : Reach 322309 := rs (se 4 (by rfl) ⟨30216, by rfl⟩) R60433
theorem R92963 : Reach 92963 := rs (se 1 (by rfl) ⟨69722, by rfl⟩) R139445
theorem R60259 : Reach 60259 := rs (se 1 (by rfl) ⟨45194, by rfl⟩) R90389
theorem R256931 : Reach 256931 := rs (se 1 (by rfl) ⟨192698, by rfl⟩) R385397
theorem R60355 : Reach 60355 := rs (se 1 (by rfl) ⟨45266, by rfl⟩) R90533
theorem R289777 : Reach 289777 := rs (se 2 (by rfl) ⟨108666, by rfl⟩) R217333
theorem R93233 : Reach 93233 := rs (se 2 (by rfl) ⟨34962, by rfl⟩) R69925
theorem R93251 : Reach 93251 := rs (se 1 (by rfl) ⟨69938, by rfl⟩) R139877
theorem R257093 : Reach 257093 := rs (se 4 (by rfl) ⟨24102, by rfl⟩) R48205
theorem R158797 : Reach 158797 := rs (se 3 (by rfl) ⟨29774, by rfl⟩) R59549
theorem R126157 : Reach 126157 := rs (se 3 (by rfl) ⟨23654, by rfl⟩) R47309
theorem R617827 : Reach 617827 := rs (se 1 (by rfl) ⟨463370, by rfl⟩) R926741
theorem R126353 : Reach 126353 := rs (se 2 (by rfl) ⟨47382, by rfl⟩) R94765
theorem R60851 : Reach 60851 := rs (se 1 (by rfl) ⟨45638, by rfl⟩) R91277
theorem R159245 : Reach 159245 := rs (se 3 (by rfl) ⟨29858, by rfl⟩) R59717
theorem R126481 : Reach 126481 := rs (se 2 (by rfl) ⟨47430, by rfl⟩) R94861
theorem R159299 : Reach 159299 := rs (se 1 (by rfl) ⟨119474, by rfl⟩) R238949
theorem R192077 : Reach 192077 := rs (se 3 (by rfl) ⟨36014, by rfl⟩) R72029
theorem R454243 : Reach 454243 := rs (se 1 (by rfl) ⟨340682, by rfl⟩) R681365
theorem R257741 : Reach 257741 := rs (se 3 (by rfl) ⟨48326, by rfl⟩) R96653
theorem R126755 : Reach 126755 := rs (se 1 (by rfl) ⟨95066, by rfl⟩) R190133
theorem R159569 : Reach 159569 := rs (se 2 (by rfl) ⟨59838, by rfl⟩) R119677
theorem R126947 : Reach 126947 := rs (se 1 (by rfl) ⟨95210, by rfl⟩) R190421
theorem R94193 : Reach 94193 := rs (se 2 (by rfl) ⟨35322, by rfl⟩) R70645
theorem R61555 : Reach 61555 := rs (se 1 (by rfl) ⟨46166, by rfl⟩) R92333
theorem R61651 : Reach 61651 := rs (se 1 (by rfl) ⟨46238, by rfl⟩) R92477
theorem R160109 : Reach 160109 := rs (se 3 (by rfl) ⟨30020, by rfl⟩) R60041
theorem R192881 : Reach 192881 := rs (se 2 (by rfl) ⟨72330, by rfl⟩) R144661
theorem R160163 : Reach 160163 := rs (se 1 (by rfl) ⟨120122, by rfl⟩) R240245
theorem R258545 : Reach 258545 := rs (se 2 (by rfl) ⟨96954, by rfl⟩) R193909
theorem R127555 : Reach 127555 := rs (se 1 (by rfl) ⟨95666, by rfl⟩) R191333
theorem R127565 : Reach 127565 := rs (se 3 (by rfl) ⟨23918, by rfl⟩) R47837
theorem R488035 : Reach 488035 := rs (se 1 (by rfl) ⟨366026, by rfl⟩) R732053
theorem R160433 : Reach 160433 := rs (se 2 (by rfl) ⟨60162, by rfl⟩) R120325
theorem R62147 : Reach 62147 := rs (se 1 (by rfl) ⟨46610, by rfl⟩) R93221
theorem R127757 : Reach 127757 := rs (se 3 (by rfl) ⟨23954, by rfl⟩) R47909
theorem R95089 : Reach 95089 := rs (se 2 (by rfl) ⟨35658, by rfl⟩) R71317
theorem R160643 : Reach 160643 := rs (se 1 (by rfl) ⟨120482, by rfl⟩) R240965
theorem R127889 : Reach 127889 := rs (se 2 (by rfl) ⟨47958, by rfl⟩) R95917
theorem R127921 : Reach 127921 := rs (se 2 (by rfl) ⟨47970, by rfl⟩) R95941
theorem R127939 : Reach 127939 := rs (se 1 (by rfl) ⟨95954, by rfl⟩) R191909
theorem R95203 : Reach 95203 := rs (se 1 (by rfl) ⟨71402, by rfl⟩) R142805
theorem R193549 : Reach 193549 := rs (se 3 (by rfl) ⟨36290, by rfl⟩) R72581
theorem R128017 : Reach 128017 := rs (se 2 (by rfl) ⟨48006, by rfl⟩) R96013
theorem R95249 : Reach 95249 := rs (se 2 (by rfl) ⟨35718, by rfl⟩) R71437
theorem R422981 : Reach 422981 := rs (se 4 (by rfl) ⟨39654, by rfl⟩) R79309
theorem R128081 : Reach 128081 := rs (se 2 (by rfl) ⟨48030, by rfl⟩) R96061
theorem R390257 : Reach 390257 := rs (se 2 (by rfl) ⟨146346, by rfl⟩) R292693
theorem R160973 : Reach 160973 := rs (se 3 (by rfl) ⟨30182, by rfl⟩) R60365
theorem R161027 : Reach 161027 := rs (se 1 (by rfl) ⟨120770, by rfl⟩) R241541
theorem R161041 : Reach 161041 := rs (se 2 (by rfl) ⟨60390, by rfl⟩) R120781
theorem R521585 : Reach 521585 := rs (se 2 (by rfl) ⟨195594, by rfl⟩) R391189
theorem R62851 : Reach 62851 := rs (se 1 (by rfl) ⟨47138, by rfl⟩) R94277
theorem R95651 : Reach 95651 := rs (se 1 (by rfl) ⟨71738, by rfl⟩) R143477
theorem R62947 : Reach 62947 := rs (se 1 (by rfl) ⟨47210, by rfl⟩) R94421
theorem R161297 : Reach 161297 := rs (se 2 (by rfl) ⟨60486, by rfl⟩) R120973
theorem R161315 : Reach 161315 := rs (se 1 (by rfl) ⟨120986, by rfl⟩) R241973
theorem R161489 : Reach 161489 := rs (se 2 (by rfl) ⟨60558, by rfl⟩) R121117
theorem R128749 : Reach 128749 := rs (se 3 (by rfl) ⟨24140, by rfl⟩) R48281
theorem R63281 : Reach 63281 := rs (se 2 (by rfl) ⟨23730, by rfl⟩) R47461
theorem R718733 : Reach 718733 := rs (se 3 (by rfl) ⟨134762, by rfl⟩) R269525
theorem R63443 : Reach 63443 := rs (se 1 (by rfl) ⟨47582, by rfl⟩) R95165
theorem R161837 : Reach 161837 := rs (se 3 (by rfl) ⟨30344, by rfl⟩) R60689
theorem R129073 : Reach 129073 := rs (se 2 (by rfl) ⟨48402, by rfl⟩) R96805
theorem R161891 : Reach 161891 := rs (se 1 (by rfl) ⟨121418, by rfl⟩) R242837
theorem R325795 : Reach 325795 := rs (se 1 (by rfl) ⟨244346, by rfl⟩) R488693
theorem R96433 : Reach 96433 := rs (se 2 (by rfl) ⟨36162, by rfl⟩) R72325
theorem R227569 : Reach 227569 := rs (se 2 (by rfl) ⟨85338, by rfl⟩) R170677
theorem R96547 : Reach 96547 := rs (se 1 (by rfl) ⟨72410, by rfl⟩) R144821
theorem R129347 : Reach 129347 := rs (se 1 (by rfl) ⟨97010, by rfl⟩) R194021
theorem R162161 : Reach 162161 := rs (se 2 (by rfl) ⟨60810, by rfl⟩) R121621
theorem R96707 : Reach 96707 := rs (se 1 (by rfl) ⟨72530, by rfl⟩) R145061
theorem R653795 : Reach 653795 := rs (se 1 (by rfl) ⟨490346, by rfl⟩) R980693
theorem R63985 : Reach 63985 := rs (se 2 (by rfl) ⟨23994, by rfl⟩) R47989
theorem R64081 : Reach 64081 := rs (se 2 (by rfl) ⟨24030, by rfl⟩) R48061
theorem R293489 : Reach 293489 := rs (se 2 (by rfl) ⟨110058, by rfl⟩) R220117
theorem R260749 : Reach 260749 := rs (se 3 (by rfl) ⟨48890, by rfl⟩) R97781
theorem R64147 : Reach 64147 := rs (se 1 (by rfl) ⟨48110, by rfl⟩) R96221
theorem R588485 : Reach 588485 := rs (se 4 (by rfl) ⟨55170, by rfl⟩) R110341
theorem R359153 : Reach 359153 := rs (se 2 (by rfl) ⟨134682, by rfl⟩) R269365
theorem R64243 : Reach 64243 := rs (se 1 (by rfl) ⟨48182, by rfl⟩) R96365
theorem R162701 : Reach 162701 := rs (se 3 (by rfl) ⟨30506, by rfl⟩) R61013
theorem R162755 : Reach 162755 := rs (se 1 (by rfl) ⟨122066, by rfl⟩) R244133
theorem R64577 : Reach 64577 := rs (se 2 (by rfl) ⟨24216, by rfl⟩) R48433
theorem R64705 : Reach 64705 := rs (se 2 (by rfl) ⟨24264, by rfl⟩) R48529
theorem R163025 : Reach 163025 := rs (se 2 (by rfl) ⟨61134, by rfl⟩) R122269
theorem R360035 : Reach 360035 := rs (se 1 (by rfl) ⟨270026, by rfl⟩) R540053
theorem R163565 : Reach 163565 := rs (se 3 (by rfl) ⟨30668, by rfl⟩) R61337
theorem R163619 : Reach 163619 := rs (se 1 (by rfl) ⟨122714, by rfl⟩) R245429
theorem R98147 : Reach 98147 := rs (se 1 (by rfl) ⟨73610, by rfl⟩) R147221
theorem R164375 : Reach 164375 := rs (se 1 (by rfl) ⟨123281, by rfl⟩) R246563
theorem R787013 : Reach 787013 := rs (se 4 (by rfl) ⟨73782, by rfl⟩) R147565
theorem R66199 : Reach 66199 := rs (se 1 (by rfl) ⟨49649, by rfl⟩) R99299
theorem R164915 : Reach 164915 := rs (se 1 (by rfl) ⟨123686, by rfl⟩) R247373
theorem R165185 : Reach 165185 := rs (se 2 (by rfl) ⟨61944, by rfl⟩) R123889
theorem R460363 : Reach 460363 := rs (se 1 (by rfl) ⟨345272, by rfl⟩) R690545
theorem R67159 : Reach 67159 := rs (se 1 (by rfl) ⟨50369, by rfl⟩) R100739
theorem R689795 : Reach 689795 := rs (se 1 (by rfl) ⟨517346, by rfl⟩) R1034693
theorem R689905 : Reach 689905 := rs (se 2 (by rfl) ⟨258714, by rfl⟩) R517429
theorem R67339 : Reach 67339 := rs (se 1 (by rfl) ⟨50504, by rfl⟩) R101009
theorem R296797 : Reach 296797 := rs (se 3 (by rfl) ⟨55649, by rfl⟩) R111299
theorem R165725 : Reach 165725 := rs (se 3 (by rfl) ⟨31073, by rfl⟩) R62147
theorem R101081 : Reach 101081 := rs (se 2 (by rfl) ⟨37905, by rfl⟩) R75811
theorem R101171 : Reach 101171 := rs (se 1 (by rfl) ⟨75878, by rfl⟩) R151757
theorem R166859 : Reach 166859 := rs (se 1 (by rfl) ⟨125144, by rfl⟩) R250289
theorem R396505 : Reach 396505 := rs (se 2 (by rfl) ⟨148689, by rfl⟩) R297379
theorem R167129 : Reach 167129 := rs (se 2 (by rfl) ⟨62673, by rfl⟩) R125347
theorem R68951 : Reach 68951 := rs (se 1 (by rfl) ⟨51713, by rfl⟩) R103427
theorem R429745 : Reach 429745 := rs (se 2 (by rfl) ⟨161154, by rfl⟩) R322309
theorem R134873 : Reach 134873 := rs (se 2 (by rfl) ⟨50577, by rfl⟩) R101155
theorem R167831 : Reach 167831 := rs (se 1 (by rfl) ⟨125873, by rfl⟩) R251747
theorem R167939 : Reach 167939 := rs (se 1 (by rfl) ⟨125954, by rfl⟩) R251909
theorem R364675 : Reach 364675 := rs (se 1 (by rfl) ⟨273506, by rfl⟩) R547013
theorem R135371 : Reach 135371 := rs (se 1 (by rfl) ⟨101528, by rfl⟩) R203057
theorem R168209 : Reach 168209 := rs (se 2 (by rfl) ⟨63078, by rfl⟩) R126157
theorem R102721 : Reach 102721 := rs (se 2 (by rfl) ⟨38520, by rfl⟩) R77041
theorem R168371 : Reach 168371 := rs (se 1 (by rfl) ⟨126278, by rfl⟩) R252557
theorem R823769 : Reach 823769 := rs (se 2 (by rfl) ⟨308913, by rfl⟩) R617827
theorem R889379 : Reach 889379 := rs (se 1 (by rfl) ⟨667034, by rfl⟩) R1334069
theorem R135731 : Reach 135731 := rs (se 1 (by rfl) ⟨101798, by rfl⟩) R203597
theorem R332363 : Reach 332363 := rs (se 1 (by rfl) ⟨249272, by rfl⟩) R498545
theorem R168641 : Reach 168641 := rs (se 2 (by rfl) ⟨63240, by rfl⟩) R126481
theorem R168749 : Reach 168749 := rs (se 3 (by rfl) ⟨31640, by rfl⟩) R63281
theorem R70679 : Reach 70679 := rs (se 1 (by rfl) ⟨53009, by rfl⟩) R106019
theorem R70745 : Reach 70745 := rs (se 2 (by rfl) ⟨26529, by rfl⟩) R53059
theorem R70859 : Reach 70859 := rs (se 1 (by rfl) ⟨53144, by rfl⟩) R106289
theorem R70871 : Reach 70871 := rs (se 1 (by rfl) ⟨53153, by rfl⟩) R106307
theorem R169181 : Reach 169181 := rs (se 3 (by rfl) ⟨31721, by rfl⟩) R63443
theorem R70937 : Reach 70937 := rs (se 2 (by rfl) ⟨26601, by rfl⟩) R53203
theorem R71051 : Reach 71051 := rs (se 1 (by rfl) ⟨53288, by rfl⟩) R106577
theorem R71063 : Reach 71063 := rs (se 1 (by rfl) ⟨53297, by rfl⟩) R106595
theorem R71129 : Reach 71129 := rs (se 2 (by rfl) ⟨26673, by rfl⟩) R53347
theorem R71243 : Reach 71243 := rs (se 1 (by rfl) ⟨53432, by rfl⟩) R106865
theorem R71255 : Reach 71255 := rs (se 1 (by rfl) ⟨53441, by rfl⟩) R106883
theorem R71321 : Reach 71321 := rs (se 2 (by rfl) ⟨26745, by rfl⟩) R53491
theorem R71435 : Reach 71435 := rs (se 1 (by rfl) ⟨53576, by rfl⟩) R107153
theorem R71447 : Reach 71447 := rs (se 1 (by rfl) ⟨53585, by rfl⟩) R107171
theorem R202571 : Reach 202571 := rs (se 1 (by rfl) ⟨151928, by rfl⟩) R303857
theorem R71513 : Reach 71513 := rs (se 2 (by rfl) ⟨26817, by rfl⟩) R53635
theorem R71627 : Reach 71627 := rs (se 1 (by rfl) ⟨53720, by rfl⟩) R107441
theorem R71639 : Reach 71639 := rs (se 1 (by rfl) ⟨53729, by rfl⟩) R107459
theorem R71705 : Reach 71705 := rs (se 2 (by rfl) ⟨26889, by rfl⟩) R53779
theorem R71819 : Reach 71819 := rs (se 1 (by rfl) ⟨53864, by rfl⟩) R107729
theorem R71831 : Reach 71831 := rs (se 1 (by rfl) ⟨53873, by rfl⟩) R107747
theorem R202925 : Reach 202925 := rs (se 3 (by rfl) ⟨38048, by rfl⟩) R76097
theorem R104627 : Reach 104627 := rs (se 1 (by rfl) ⟨78470, by rfl⟩) R156941
theorem R71897 : Reach 71897 := rs (se 2 (by rfl) ⟨26961, by rfl⟩) R53923
theorem R72011 : Reach 72011 := rs (se 1 (by rfl) ⟨54008, by rfl⟩) R108017
theorem R170315 : Reach 170315 := rs (se 1 (by rfl) ⟨127736, by rfl⟩) R255473
theorem R72023 : Reach 72023 := rs (se 1 (by rfl) ⟨54017, by rfl⟩) R108035
theorem R72089 : Reach 72089 := rs (se 2 (by rfl) ⟨27033, by rfl⟩) R54067
theorem R72203 : Reach 72203 := rs (se 1 (by rfl) ⟨54152, by rfl⟩) R108305
theorem R72215 : Reach 72215 := rs (se 1 (by rfl) ⟨54161, by rfl⟩) R108323
theorem R170561 : Reach 170561 := rs (se 2 (by rfl) ⟨63960, by rfl⟩) R127921
theorem R268865 : Reach 268865 := rs (se 2 (by rfl) ⟨100824, by rfl⟩) R201649
theorem R72281 : Reach 72281 := rs (se 2 (by rfl) ⟨27105, by rfl⟩) R54211
theorem R170585 : Reach 170585 := rs (se 2 (by rfl) ⟨63969, by rfl⟩) R127939
theorem R105113 : Reach 105113 := rs (se 2 (by rfl) ⟨39417, by rfl⟩) R78835
theorem R170689 : Reach 170689 := rs (se 2 (by rfl) ⟨64008, by rfl⟩) R128017
theorem R72395 : Reach 72395 := rs (se 1 (by rfl) ⟨54296, by rfl⟩) R108593
theorem R72407 : Reach 72407 := rs (se 1 (by rfl) ⟨54305, by rfl⟩) R108611
theorem R72473 : Reach 72473 := rs (se 2 (by rfl) ⟨27177, by rfl⟩) R54355
theorem R236333 : Reach 236333 := rs (se 3 (by rfl) ⟨44312, by rfl⟩) R88625
theorem R72587 : Reach 72587 := rs (se 1 (by rfl) ⟨54440, by rfl⟩) R108881
theorem R72599 : Reach 72599 := rs (se 1 (by rfl) ⟨54449, by rfl⟩) R108899
theorem R72665 : Reach 72665 := rs (se 2 (by rfl) ⟨27249, by rfl⟩) R54499
theorem R203741 : Reach 203741 := rs (se 3 (by rfl) ⟨38201, by rfl⟩) R76403
theorem R171031 : Reach 171031 := rs (se 1 (by rfl) ⟨128273, by rfl⟩) R256547
theorem R72779 : Reach 72779 := rs (se 1 (by rfl) ⟨54584, by rfl⟩) R109169
theorem R72791 : Reach 72791 := rs (se 1 (by rfl) ⟨54593, by rfl⟩) R109187
theorem R466013 : Reach 466013 := rs (se 3 (by rfl) ⟨87377, by rfl⟩) R174755
theorem R302231 : Reach 302231 := rs (se 1 (by rfl) ⟨226673, by rfl⟩) R453347
theorem R72857 : Reach 72857 := rs (se 2 (by rfl) ⟨27321, by rfl⟩) R54643
theorem R138419 : Reach 138419 := rs (se 1 (by rfl) ⟨103814, by rfl⟩) R207629
theorem R72971 : Reach 72971 := rs (se 1 (by rfl) ⟨54728, by rfl⟩) R109457
theorem R72983 : Reach 72983 := rs (se 1 (by rfl) ⟨54737, by rfl⟩) R109475
theorem R171287 : Reach 171287 := rs (se 1 (by rfl) ⟨128465, by rfl⟩) R256931
theorem R73049 : Reach 73049 := rs (se 2 (by rfl) ⟨27393, by rfl⟩) R54787
theorem R105857 : Reach 105857 := rs (se 2 (by rfl) ⟨39696, by rfl⟩) R79393
theorem R171395 : Reach 171395 := rs (se 1 (by rfl) ⟨128546, by rfl⟩) R257093
theorem R138647 : Reach 138647 := rs (se 1 (by rfl) ⟨103985, by rfl⟩) R207971
theorem R73111 : Reach 73111 := rs (se 1 (by rfl) ⟨54833, by rfl⟩) R109667
theorem R204211 : Reach 204211 := rs (se 1 (by rfl) ⟨153158, by rfl⟩) R306317
theorem R73163 : Reach 73163 := rs (se 1 (by rfl) ⟨54872, by rfl⟩) R109745
theorem R73175 : Reach 73175 := rs (se 1 (by rfl) ⟨54881, by rfl⟩) R109763
theorem R73177 : Reach 73177 := rs (se 2 (by rfl) ⟨27441, by rfl⟩) R54883
theorem R73241 : Reach 73241 := rs (se 2 (by rfl) ⟨27465, by rfl⟩) R54931
theorem R106073 : Reach 106073 := rs (se 2 (by rfl) ⟨39777, by rfl⟩) R79555
theorem R73355 : Reach 73355 := rs (se 1 (by rfl) ⟨55016, by rfl⟩) R110033
theorem R171665 : Reach 171665 := rs (se 2 (by rfl) ⟨64374, by rfl⟩) R128749
theorem R204439 : Reach 204439 := rs (se 1 (by rfl) ⟨153329, by rfl⟩) R306659
theorem R73367 : Reach 73367 := rs (se 1 (by rfl) ⟨55025, by rfl⟩) R110051
theorem R106163 : Reach 106163 := rs (se 1 (by rfl) ⟨79622, by rfl⟩) R159245
theorem R204481 : Reach 204481 := rs (se 2 (by rfl) ⟨76680, by rfl⟩) R153361
theorem R138955 : Reach 138955 := rs (se 1 (by rfl) ⟨104216, by rfl⟩) R208433
theorem R106199 : Reach 106199 := rs (se 1 (by rfl) ⟨79649, by rfl⟩) R159299
theorem R73433 : Reach 73433 := rs (se 2 (by rfl) ⟨27537, by rfl⟩) R55075
theorem R171827 : Reach 171827 := rs (se 1 (by rfl) ⟨128870, by rfl⟩) R257741
theorem R73547 : Reach 73547 := rs (se 1 (by rfl) ⟨55160, by rfl⟩) R110321
theorem R73559 : Reach 73559 := rs (se 1 (by rfl) ⟨55169, by rfl⟩) R110339
theorem R106379 : Reach 106379 := rs (se 1 (by rfl) ⟨79784, by rfl⟩) R159569
theorem R73625 : Reach 73625 := rs (se 2 (by rfl) ⟨27609, by rfl⟩) R55219
theorem R106433 : Reach 106433 := rs (se 2 (by rfl) ⟨39912, by rfl⟩) R79825
theorem R139229 : Reach 139229 := rs (se 3 (by rfl) ⟨26105, by rfl⟩) R52211
theorem R73739 : Reach 73739 := rs (se 1 (by rfl) ⟨55304, by rfl⟩) R110609
theorem R73751 : Reach 73751 := rs (se 1 (by rfl) ⟨55313, by rfl⟩) R110627
theorem R172097 : Reach 172097 := rs (se 2 (by rfl) ⟨64536, by rfl⟩) R129073
theorem R73817 : Reach 73817 := rs (se 2 (by rfl) ⟨27681, by rfl⟩) R55363
theorem R106649 : Reach 106649 := rs (se 2 (by rfl) ⟨39993, by rfl⟩) R79987
theorem R172205 : Reach 172205 := rs (se 3 (by rfl) ⟨32288, by rfl⟩) R64577
theorem R73931 : Reach 73931 := rs (se 1 (by rfl) ⟨55448, by rfl⟩) R110897
theorem R73943 : Reach 73943 := rs (se 1 (by rfl) ⟨55457, by rfl⟩) R110915
theorem R434393 : Reach 434393 := rs (se 2 (by rfl) ⟨162897, by rfl⟩) R325795
theorem R106739 : Reach 106739 := rs (se 1 (by rfl) ⟨80054, by rfl⟩) R160109
theorem R106753 : Reach 106753 := rs (se 2 (by rfl) ⟨40032, by rfl⟩) R80065
theorem R106775 : Reach 106775 := rs (se 1 (by rfl) ⟨80081, by rfl⟩) R160163
theorem R74009 : Reach 74009 := rs (se 2 (by rfl) ⟨27753, by rfl⟩) R55507
theorem R303425 : Reach 303425 := rs (se 2 (by rfl) ⟨113784, by rfl⟩) R227569
theorem R172363 : Reach 172363 := rs (se 1 (by rfl) ⟨129272, by rfl⟩) R258545
theorem R74123 : Reach 74123 := rs (se 1 (by rfl) ⟨55592, by rfl⟩) R111185
theorem R74135 : Reach 74135 := rs (se 1 (by rfl) ⟨55601, by rfl⟩) R111203
theorem R106955 : Reach 106955 := rs (se 1 (by rfl) ⟨80216, by rfl⟩) R160433
theorem R205259 : Reach 205259 := rs (se 1 (by rfl) ⟨153944, by rfl⟩) R307889
theorem R74201 : Reach 74201 := rs (se 2 (by rfl) ⟨27825, by rfl⟩) R55651
theorem R107009 : Reach 107009 := rs (se 2 (by rfl) ⟨40128, by rfl⟩) R80257
theorem R74315 : Reach 74315 := rs (se 1 (by rfl) ⟨55736, by rfl⟩) R111473
theorem R74327 : Reach 74327 := rs (se 1 (by rfl) ⟨55745, by rfl⟩) R111491
theorem R107095 : Reach 107095 := rs (se 1 (by rfl) ⟨80321, by rfl⟩) R160643
theorem R303709 : Reach 303709 := rs (se 3 (by rfl) ⟨56945, by rfl⟩) R113891
theorem R74393 : Reach 74393 := rs (se 2 (by rfl) ⟨27897, by rfl⟩) R55795
theorem R107225 : Reach 107225 := rs (se 2 (by rfl) ⟨40209, by rfl⟩) R80419
theorem R74507 : Reach 74507 := rs (se 1 (by rfl) ⟨55880, by rfl⟩) R111761
theorem R74519 : Reach 74519 := rs (se 1 (by rfl) ⟨55889, by rfl⟩) R111779
theorem R107315 : Reach 107315 := rs (se 1 (by rfl) ⟨80486, by rfl⟩) R160973
theorem R107351 : Reach 107351 := rs (se 1 (by rfl) ⟨80513, by rfl⟩) R161027
theorem R74585 : Reach 74585 := rs (se 2 (by rfl) ⟨27969, by rfl⟩) R55939
theorem R205699 : Reach 205699 := rs (se 1 (by rfl) ⟨154274, by rfl⟩) R308549
theorem R74699 : Reach 74699 := rs (se 1 (by rfl) ⟨56024, by rfl⟩) R112049
theorem R74711 : Reach 74711 := rs (se 1 (by rfl) ⟨56033, by rfl⟩) R112067
theorem R107531 : Reach 107531 := rs (se 1 (by rfl) ⟨80648, by rfl⟩) R161297
theorem R107543 : Reach 107543 := rs (se 1 (by rfl) ⟨80657, by rfl⟩) R161315
theorem R74777 : Reach 74777 := rs (se 2 (by rfl) ⟨28041, by rfl⟩) R56083
theorem R107585 : Reach 107585 := rs (se 2 (by rfl) ⟨40344, by rfl⟩) R80689
theorem R74891 : Reach 74891 := rs (se 1 (by rfl) ⟨56168, by rfl⟩) R112337
theorem R107659 : Reach 107659 := rs (se 1 (by rfl) ⟨80744, by rfl⟩) R161489
theorem R74903 : Reach 74903 := rs (se 1 (by rfl) ⟨56177, by rfl⟩) R112355
theorem R74969 : Reach 74969 := rs (se 2 (by rfl) ⟨28113, by rfl⟩) R56227
theorem R107801 : Reach 107801 := rs (se 2 (by rfl) ⟨40425, by rfl⟩) R80851
theorem R402733 : Reach 402733 := rs (se 3 (by rfl) ⟨75512, by rfl⟩) R151025
theorem R75083 : Reach 75083 := rs (se 1 (by rfl) ⟨56312, by rfl⟩) R112625
theorem R75095 : Reach 75095 := rs (se 1 (by rfl) ⟨56321, by rfl⟩) R112643
theorem R107891 : Reach 107891 := rs (se 1 (by rfl) ⟨80918, by rfl⟩) R161837
theorem R107927 : Reach 107927 := rs (se 1 (by rfl) ⟨80945, by rfl⟩) R161891
theorem R75161 : Reach 75161 := rs (se 2 (by rfl) ⟨28185, by rfl⟩) R56371
theorem R206297 : Reach 206297 := rs (se 2 (by rfl) ⟨77361, by rfl⟩) R154723
theorem R75275 : Reach 75275 := rs (se 1 (by rfl) ⟨56456, by rfl⟩) R112913
theorem R75287 : Reach 75287 := rs (se 1 (by rfl) ⟨56465, by rfl⟩) R112931
theorem R108107 : Reach 108107 := rs (se 1 (by rfl) ⟨81080, by rfl⟩) R162161
theorem R75353 : Reach 75353 := rs (se 2 (by rfl) ⟨28257, by rfl⟩) R56515
theorem R108161 : Reach 108161 := rs (se 2 (by rfl) ⟨40560, by rfl⟩) R81121
theorem R75403 : Reach 75403 := rs (se 1 (by rfl) ⟨56552, by rfl⟩) R113105
theorem R435863 : Reach 435863 := rs (se 1 (by rfl) ⟨326897, by rfl⟩) R653795
theorem R75467 : Reach 75467 := rs (se 1 (by rfl) ⟨56600, by rfl⟩) R113201
theorem R75479 : Reach 75479 := rs (se 1 (by rfl) ⟨56609, by rfl⟩) R113219
theorem R75545 : Reach 75545 := rs (se 2 (by rfl) ⟨28329, by rfl⟩) R56659
theorem R206657 : Reach 206657 := rs (se 2 (by rfl) ⟨77496, by rfl⟩) R154993
theorem R239435 : Reach 239435 := rs (se 1 (by rfl) ⟨179576, by rfl⟩) R359153
theorem R108377 : Reach 108377 := rs (se 2 (by rfl) ⟨40641, by rfl⟩) R81283
theorem R206723 : Reach 206723 := rs (se 1 (by rfl) ⟨155042, by rfl⟩) R310085
theorem R75659 : Reach 75659 := rs (se 1 (by rfl) ⟨56744, by rfl⟩) R113489
theorem R75671 : Reach 75671 := rs (se 1 (by rfl) ⟨56753, by rfl⟩) R113507
theorem R337841 : Reach 337841 := rs (se 2 (by rfl) ⟨126690, by rfl⟩) R253381
theorem R108467 : Reach 108467 := rs (se 1 (by rfl) ⟨81350, by rfl⟩) R162701
theorem R108503 : Reach 108503 := rs (se 1 (by rfl) ⟨81377, by rfl⟩) R162755
theorem R75737 : Reach 75737 := rs (se 2 (by rfl) ⟨28401, by rfl⟩) R56803
theorem R141335 : Reach 141335 := rs (se 1 (by rfl) ⟨106001, by rfl⟩) R212003
theorem R403501 : Reach 403501 := rs (se 3 (by rfl) ⟨75656, by rfl⟩) R151313
theorem R75851 : Reach 75851 := rs (se 1 (by rfl) ⟨56888, by rfl⟩) R113777
theorem R75863 : Reach 75863 := rs (se 1 (by rfl) ⟨56897, by rfl⟩) R113795
theorem R108683 : Reach 108683 := rs (se 1 (by rfl) ⟨81512, by rfl⟩) R163025
theorem R75929 : Reach 75929 := rs (se 2 (by rfl) ⟨28473, by rfl⟩) R56947
theorem R108737 : Reach 108737 := rs (se 2 (by rfl) ⟨40776, by rfl⟩) R81553
theorem R76043 : Reach 76043 := rs (se 1 (by rfl) ⟨57032, by rfl⟩) R114065
theorem R76055 : Reach 76055 := rs (se 1 (by rfl) ⟨57041, by rfl⟩) R114083
theorem R338251 : Reach 338251 := rs (se 1 (by rfl) ⟨253688, by rfl⟩) R507377
theorem R76121 : Reach 76121 := rs (se 2 (by rfl) ⟨28545, by rfl⟩) R57091
theorem R240023 : Reach 240023 := rs (se 1 (by rfl) ⟨180017, by rfl⟩) R360035
theorem R108953 : Reach 108953 := rs (se 2 (by rfl) ⟨40857, by rfl⟩) R81715
theorem R76235 : Reach 76235 := rs (se 1 (by rfl) ⟨57176, by rfl⟩) R114353
theorem R76247 : Reach 76247 := rs (se 1 (by rfl) ⟨57185, by rfl⟩) R114371
theorem R272857 : Reach 272857 := rs (se 2 (by rfl) ⟨102321, by rfl⟩) R204643
theorem R109043 : Reach 109043 := rs (se 1 (by rfl) ⟨81782, by rfl⟩) R163565
theorem R109079 : Reach 109079 := rs (se 1 (by rfl) ⟨81809, by rfl⟩) R163619
theorem R76313 : Reach 76313 := rs (se 2 (by rfl) ⟨28617, by rfl⟩) R57235
theorem R404003 : Reach 404003 := rs (se 1 (by rfl) ⟨303002, by rfl⟩) R606005
theorem R109145 : Reach 109145 := rs (se 2 (by rfl) ⟨40929, by rfl⟩) R81859
theorem R76427 : Reach 76427 := rs (se 1 (by rfl) ⟨57320, by rfl⟩) R114641
theorem R76439 : Reach 76439 := rs (se 1 (by rfl) ⟨57329, by rfl⟩) R114659
theorem R109259 : Reach 109259 := rs (se 1 (by rfl) ⟨81944, by rfl⟩) R163889
theorem R76505 : Reach 76505 := rs (se 2 (by rfl) ⟨28689, by rfl⟩) R57379
theorem R109313 : Reach 109313 := rs (se 2 (by rfl) ⟨40992, by rfl⟩) R81985
theorem R142145 : Reach 142145 := rs (se 2 (by rfl) ⟨53304, by rfl⟩) R106609
theorem R76619 : Reach 76619 := rs (se 1 (by rfl) ⟨57464, by rfl⟩) R114929
theorem R76631 : Reach 76631 := rs (se 1 (by rfl) ⟨57473, by rfl⟩) R114947
theorem R109529 : Reach 109529 := rs (se 2 (by rfl) ⟨41073, by rfl⟩) R82147
theorem R109619 : Reach 109619 := rs (se 1 (by rfl) ⟨82214, by rfl⟩) R164429
theorem R109655 : Reach 109655 := rs (se 1 (by rfl) ⟨82241, by rfl⟩) R164483
theorem R77015 : Reach 77015 := rs (se 1 (by rfl) ⟨57761, by rfl⟩) R115523
theorem R109835 : Reach 109835 := rs (se 1 (by rfl) ⟨82376, by rfl⟩) R164753
theorem R175405 : Reach 175405 := rs (se 3 (by rfl) ⟨32888, by rfl⟩) R65777
theorem R109889 : Reach 109889 := rs (se 2 (by rfl) ⟨41208, by rfl⟩) R82417
theorem R273739 : Reach 273739 := rs (se 1 (by rfl) ⟨205304, by rfl⟩) R410609
theorem R404837 : Reach 404837 := rs (se 4 (by rfl) ⟨37953, by rfl⟩) R75907
theorem R77195 : Reach 77195 := rs (se 1 (by rfl) ⟨57896, by rfl⟩) R115793
theorem R110105 : Reach 110105 := rs (se 2 (by rfl) ⟨41289, by rfl⟩) R82579
theorem R241217 : Reach 241217 := rs (se 2 (by rfl) ⟨90456, by rfl⟩) R180913
theorem R274013 : Reach 274013 := rs (se 3 (by rfl) ⟨51377, by rfl⟩) R102755
theorem R110195 : Reach 110195 := rs (se 1 (by rfl) ⟨82646, by rfl⟩) R165293
theorem R110231 : Reach 110231 := rs (se 1 (by rfl) ⟨82673, by rfl⟩) R165347
theorem R110411 : Reach 110411 := rs (se 1 (by rfl) ⟨82808, by rfl⟩) R165617
theorem R110465 : Reach 110465 := rs (se 2 (by rfl) ⟨41424, by rfl⟩) R82849
theorem R77707 : Reach 77707 := rs (se 1 (by rfl) ⟨58280, by rfl⟩) R116561
theorem R77771 : Reach 77771 := rs (se 1 (by rfl) ⟨58328, by rfl⟩) R116657
theorem R110681 : Reach 110681 := rs (se 2 (by rfl) ⟨41505, by rfl⟩) R83011
theorem R110771 : Reach 110771 := rs (se 1 (by rfl) ⟨83078, by rfl⟩) R166157
theorem R110807 : Reach 110807 := rs (se 1 (by rfl) ⟨83105, by rfl⟩) R166211
theorem R110899 : Reach 110899 := rs (se 1 (by rfl) ⟨83174, by rfl⟩) R166349
theorem R110987 : Reach 110987 := rs (se 1 (by rfl) ⟨83240, by rfl⟩) R166481
theorem R143795 : Reach 143795 := rs (se 1 (by rfl) ⟨107846, by rfl⟩) R215693
theorem R111041 : Reach 111041 := rs (se 2 (by rfl) ⟨41640, by rfl⟩) R83281
theorem R143819 : Reach 143819 := rs (se 1 (by rfl) ⟨107864, by rfl⟩) R215729
theorem R78425 : Reach 78425 := rs (se 2 (by rfl) ⟨29409, by rfl⟩) R58819
theorem R111257 : Reach 111257 := rs (se 2 (by rfl) ⟨41721, by rfl⟩) R83443
theorem R635597 : Reach 635597 := rs (se 3 (by rfl) ⟨119174, by rfl⟩) R238349
theorem R111347 : Reach 111347 := rs (se 1 (by rfl) ⟨83510, by rfl⟩) R167021
theorem R111383 : Reach 111383 := rs (se 1 (by rfl) ⟨83537, by rfl⟩) R167075
theorem R111563 : Reach 111563 := rs (se 1 (by rfl) ⟨83672, by rfl⟩) R167345
theorem R111617 : Reach 111617 := rs (se 2 (by rfl) ⟨41856, by rfl⟩) R83713
theorem R78937 : Reach 78937 := rs (se 2 (by rfl) ⟨29601, by rfl⟩) R59203
theorem R799895 : Reach 799895 := rs (se 1 (by rfl) ⟨599921, by rfl⟩) R1199843
theorem R111833 : Reach 111833 := rs (se 2 (by rfl) ⟨41937, by rfl⟩) R83875
theorem R144605 : Reach 144605 := rs (se 3 (by rfl) ⟨27113, by rfl⟩) R54227
theorem R111923 : Reach 111923 := rs (se 1 (by rfl) ⟨83942, by rfl⟩) R167885
theorem R308573 : Reach 308573 := rs (se 3 (by rfl) ⟨57857, by rfl⟩) R115715
theorem R406885 : Reach 406885 := rs (se 4 (by rfl) ⟨38145, by rfl⟩) R76291
theorem R243161 : Reach 243161 := rs (se 2 (by rfl) ⟨91185, by rfl⟩) R182371
theorem R210397 : Reach 210397 := rs (se 3 (by rfl) ⟨39449, by rfl⟩) R78899
theorem R112151 : Reach 112151 := rs (se 1 (by rfl) ⟨84113, by rfl⟩) R168227
theorem R112193 : Reach 112193 := rs (se 2 (by rfl) ⟨42072, by rfl⟩) R84145
theorem R178013 : Reach 178013 := rs (se 3 (by rfl) ⟨33377, by rfl⟩) R66755
theorem R767843 : Reach 767843 := rs (se 1 (by rfl) ⟨575882, by rfl⟩) R1151765
theorem R112535 : Reach 112535 := rs (se 1 (by rfl) ⟨84401, by rfl⟩) R168803
theorem R374705 : Reach 374705 := rs (se 2 (by rfl) ⟨140514, by rfl⟩) R281029
theorem R47127 : Reach 47127 := rs (se 1 (by rfl) ⟨35345, by rfl⟩) R70691
theorem R47147 : Reach 47147 := rs (se 1 (by rfl) ⟨35360, by rfl⟩) R70721
theorem R47159 : Reach 47159 := rs (se 1 (by rfl) ⟨35369, by rfl⟩) R70739
theorem R47179 : Reach 47179 := rs (se 1 (by rfl) ⟨35384, by rfl⟩) R70769
theorem R112715 : Reach 112715 := rs (se 1 (by rfl) ⟨84536, by rfl⟩) R169073
theorem R47191 : Reach 47191 := rs (se 1 (by rfl) ⟨35393, by rfl⟩) R70787
theorem R47211 : Reach 47211 := rs (se 1 (by rfl) ⟨35408, by rfl⟩) R70817
theorem R47223 : Reach 47223 := rs (se 1 (by rfl) ⟨35417, by rfl⟩) R70835
theorem R47243 : Reach 47243 := rs (se 1 (by rfl) ⟨35432, by rfl⟩) R70865
theorem R47255 : Reach 47255 := rs (se 1 (by rfl) ⟨35441, by rfl⟩) R70883
theorem R47275 : Reach 47275 := rs (se 1 (by rfl) ⟨35456, by rfl⟩) R70913
theorem R47287 : Reach 47287 := rs (se 1 (by rfl) ⟨35465, by rfl⟩) R70931
theorem R47307 : Reach 47307 := rs (se 1 (by rfl) ⟨35480, by rfl⟩) R70961
theorem R80075 : Reach 80075 := rs (se 1 (by rfl) ⟨60056, by rfl⟩) R120113
theorem R47319 : Reach 47319 := rs (se 1 (by rfl) ⟨35489, by rfl⟩) R70979
theorem R47339 : Reach 47339 := rs (se 1 (by rfl) ⟨35504, by rfl⟩) R71009
theorem R47351 : Reach 47351 := rs (se 1 (by rfl) ⟨35513, by rfl⟩) R71027
theorem R47371 : Reach 47371 := rs (se 1 (by rfl) ⟨35528, by rfl⟩) R71057
theorem R47383 : Reach 47383 := rs (se 1 (by rfl) ⟨35537, by rfl⟩) R71075
theorem R47403 : Reach 47403 := rs (se 1 (by rfl) ⟨35552, by rfl⟩) R71105
theorem R47415 : Reach 47415 := rs (se 1 (by rfl) ⟨35561, by rfl⟩) R71123
theorem R47435 : Reach 47435 := rs (se 1 (by rfl) ⟨35576, by rfl⟩) R71153
theorem R80203 : Reach 80203 := rs (se 1 (by rfl) ⟨60152, by rfl⟩) R120305
theorem R47447 : Reach 47447 := rs (se 1 (by rfl) ⟨35585, by rfl⟩) R71171
theorem R112985 : Reach 112985 := rs (se 2 (by rfl) ⟨42369, by rfl⟩) R84739
theorem R47467 : Reach 47467 := rs (se 1 (by rfl) ⟨35600, by rfl⟩) R71201
theorem R47479 : Reach 47479 := rs (se 1 (by rfl) ⟨35609, by rfl⟩) R71219
theorem R47499 : Reach 47499 := rs (se 1 (by rfl) ⟨35624, by rfl⟩) R71249
theorem R47511 : Reach 47511 := rs (se 1 (by rfl) ⟨35633, by rfl⟩) R71267
theorem R375191 : Reach 375191 := rs (se 1 (by rfl) ⟨281393, by rfl⟩) R562787
theorem R47531 : Reach 47531 := rs (se 1 (by rfl) ⟨35648, by rfl⟩) R71297
theorem R113075 : Reach 113075 := rs (se 1 (by rfl) ⟨84806, by rfl⟩) R169613
theorem R47543 : Reach 47543 := rs (se 1 (by rfl) ⟨35657, by rfl⟩) R71315
theorem R47563 : Reach 47563 := rs (se 1 (by rfl) ⟨35672, by rfl⟩) R71345
theorem R47575 : Reach 47575 := rs (se 1 (by rfl) ⟨35681, by rfl⟩) R71363
theorem R80345 : Reach 80345 := rs (se 2 (by rfl) ⟨30129, by rfl⟩) R60259
theorem R47595 : Reach 47595 := rs (se 1 (by rfl) ⟨35696, by rfl⟩) R71393
theorem R47607 : Reach 47607 := rs (se 1 (by rfl) ⟨35705, by rfl⟩) R71411
theorem R47627 : Reach 47627 := rs (se 1 (by rfl) ⟨35720, by rfl⟩) R71441
theorem R47639 : Reach 47639 := rs (se 1 (by rfl) ⟨35729, by rfl⟩) R71459
theorem R47659 : Reach 47659 := rs (se 1 (by rfl) ⟨35744, by rfl⟩) R71489
theorem R47671 : Reach 47671 := rs (se 1 (by rfl) ⟨35753, by rfl⟩) R71507
theorem R47691 : Reach 47691 := rs (se 1 (by rfl) ⟨35768, by rfl⟩) R71537
theorem R309835 : Reach 309835 := rs (se 1 (by rfl) ⟨232376, by rfl⟩) R464753
theorem R47703 : Reach 47703 := rs (se 1 (by rfl) ⟨35777, by rfl⟩) R71555
theorem R80473 : Reach 80473 := rs (se 2 (by rfl) ⟨30177, by rfl⟩) R60355
theorem R47723 : Reach 47723 := rs (se 1 (by rfl) ⟨35792, by rfl⟩) R71585
theorem R47735 : Reach 47735 := rs (se 1 (by rfl) ⟨35801, by rfl⟩) R71603
theorem R47755 : Reach 47755 := rs (se 1 (by rfl) ⟨35816, by rfl⟩) R71633
theorem R47767 : Reach 47767 := rs (se 1 (by rfl) ⟨35825, by rfl⟩) R71651
theorem R47787 : Reach 47787 := rs (se 1 (by rfl) ⟨35840, by rfl⟩) R71681
theorem R735925 : Reach 735925 := rs (se 5 (by rfl) ⟨34496, by rfl⟩) R68993
theorem R47799 : Reach 47799 := rs (se 1 (by rfl) ⟨35849, by rfl⟩) R71699
theorem R113345 : Reach 113345 := rs (se 2 (by rfl) ⟨42504, by rfl⟩) R85009
theorem R47819 : Reach 47819 := rs (se 1 (by rfl) ⟨35864, by rfl⟩) R71729
theorem R47831 : Reach 47831 := rs (se 1 (by rfl) ⟨35873, by rfl⟩) R71747
theorem R309977 : Reach 309977 := rs (se 2 (by rfl) ⟨116241, by rfl⟩) R232483
theorem R47851 : Reach 47851 := rs (se 1 (by rfl) ⟨35888, by rfl⟩) R71777
theorem R47863 : Reach 47863 := rs (se 1 (by rfl) ⟨35897, by rfl⟩) R71795
theorem R47883 : Reach 47883 := rs (se 1 (by rfl) ⟨35912, by rfl⟩) R71825
theorem R211729 : Reach 211729 := rs (se 2 (by rfl) ⟨79398, by rfl⟩) R158797
theorem R47895 : Reach 47895 := rs (se 1 (by rfl) ⟨35921, by rfl⟩) R71843
theorem R47915 : Reach 47915 := rs (se 1 (by rfl) ⟨35936, by rfl⟩) R71873
theorem R47927 : Reach 47927 := rs (se 1 (by rfl) ⟨35945, by rfl⟩) R71891
theorem R47947 : Reach 47947 := rs (se 1 (by rfl) ⟨35960, by rfl⟩) R71921
theorem R47959 : Reach 47959 := rs (se 1 (by rfl) ⟨35969, by rfl⟩) R71939
theorem R47979 : Reach 47979 := rs (se 1 (by rfl) ⟨35984, by rfl⟩) R71969
theorem R47991 : Reach 47991 := rs (se 1 (by rfl) ⟨35993, by rfl⟩) R71987
theorem R48011 : Reach 48011 := rs (se 1 (by rfl) ⟨36008, by rfl⟩) R72017
theorem R48023 : Reach 48023 := rs (se 1 (by rfl) ⟨36017, by rfl⟩) R72035
theorem R48043 : Reach 48043 := rs (se 1 (by rfl) ⟨36032, by rfl⟩) R72065
theorem R48055 : Reach 48055 := rs (se 1 (by rfl) ⟨36041, by rfl⟩) R72083
theorem R48075 : Reach 48075 := rs (se 1 (by rfl) ⟨36056, by rfl⟩) R72113
theorem R48087 : Reach 48087 := rs (se 1 (by rfl) ⟨36065, by rfl⟩) R72131
theorem R48107 : Reach 48107 := rs (se 1 (by rfl) ⟨36080, by rfl⟩) R72161
theorem R48119 : Reach 48119 := rs (se 1 (by rfl) ⟨36089, by rfl⟩) R72179
theorem R48139 : Reach 48139 := rs (se 1 (by rfl) ⟨36104, by rfl⟩) R72209
theorem R48151 : Reach 48151 := rs (se 1 (by rfl) ⟨36113, by rfl⟩) R72227
theorem R113687 : Reach 113687 := rs (se 1 (by rfl) ⟨85265, by rfl⟩) R170531
theorem R48171 : Reach 48171 := rs (se 1 (by rfl) ⟨36128, by rfl⟩) R72257
theorem R244781 : Reach 244781 := rs (se 3 (by rfl) ⟨45896, by rfl⟩) R91793
theorem R48183 : Reach 48183 := rs (se 1 (by rfl) ⟨36137, by rfl⟩) R72275
theorem R48203 : Reach 48203 := rs (se 1 (by rfl) ⟨36152, by rfl⟩) R72305
theorem R48215 : Reach 48215 := rs (se 1 (by rfl) ⟨36161, by rfl⟩) R72323
theorem R48235 : Reach 48235 := rs (se 1 (by rfl) ⟨36176, by rfl⟩) R72353
theorem R48247 : Reach 48247 := rs (se 1 (by rfl) ⟨36185, by rfl⟩) R72371
theorem R48267 : Reach 48267 := rs (se 1 (by rfl) ⟨36200, by rfl⟩) R72401
theorem R81047 : Reach 81047 := rs (se 1 (by rfl) ⟨60785, by rfl⟩) R121571
theorem R48279 : Reach 48279 := rs (se 1 (by rfl) ⟨36209, by rfl⟩) R72419
theorem R48299 : Reach 48299 := rs (se 1 (by rfl) ⟨36224, by rfl⟩) R72449
theorem R48311 : Reach 48311 := rs (se 1 (by rfl) ⟨36233, by rfl⟩) R72467
theorem R48331 : Reach 48331 := rs (se 1 (by rfl) ⟨36248, by rfl⟩) R72497
theorem R113867 : Reach 113867 := rs (se 1 (by rfl) ⟨85400, by rfl⟩) R170801
theorem R48343 : Reach 48343 := rs (se 1 (by rfl) ⟨36257, by rfl⟩) R72515
theorem R48363 : Reach 48363 := rs (se 1 (by rfl) ⟨36272, by rfl⟩) R72545
theorem R48375 : Reach 48375 := rs (se 1 (by rfl) ⟨36281, by rfl⟩) R72563
theorem R48395 : Reach 48395 := rs (se 1 (by rfl) ⟨36296, by rfl⟩) R72593
theorem R81175 : Reach 81175 := rs (se 1 (by rfl) ⟨60881, by rfl⟩) R121763
theorem R48407 : Reach 48407 := rs (se 1 (by rfl) ⟨36305, by rfl⟩) R72611
theorem R48427 : Reach 48427 := rs (se 1 (by rfl) ⟨36320, by rfl⟩) R72641
theorem R48439 : Reach 48439 := rs (se 1 (by rfl) ⟨36329, by rfl⟩) R72659
theorem R48459 : Reach 48459 := rs (se 1 (by rfl) ⟨36344, by rfl⟩) R72689
theorem R48471 : Reach 48471 := rs (se 1 (by rfl) ⟨36353, by rfl⟩) R72707
theorem R146777 : Reach 146777 := rs (se 2 (by rfl) ⟨55041, by rfl⟩) R110083
theorem R48491 : Reach 48491 := rs (se 1 (by rfl) ⟨36368, by rfl⟩) R72737
theorem R48503 : Reach 48503 := rs (se 1 (by rfl) ⟨36377, by rfl⟩) R72755
theorem R48523 : Reach 48523 := rs (se 1 (by rfl) ⟨36392, by rfl⟩) R72785
theorem R48535 : Reach 48535 := rs (se 1 (by rfl) ⟨36401, by rfl⟩) R72803
theorem R48555 : Reach 48555 := rs (se 1 (by rfl) ⟨36416, by rfl⟩) R72833
theorem R48567 : Reach 48567 := rs (se 1 (by rfl) ⟨36425, by rfl⟩) R72851
theorem R48587 : Reach 48587 := rs (se 1 (by rfl) ⟨36440, by rfl⟩) R72881
theorem R48599 : Reach 48599 := rs (se 1 (by rfl) ⟨36449, by rfl⟩) R72899
theorem R605657 : Reach 605657 := rs (se 2 (by rfl) ⟨227121, by rfl⟩) R454243
theorem R48619 : Reach 48619 := rs (se 1 (by rfl) ⟨36464, by rfl⟩) R72929
theorem R48631 : Reach 48631 := rs (se 1 (by rfl) ⟨36473, by rfl⟩) R72947
theorem R48651 : Reach 48651 := rs (se 1 (by rfl) ⟨36488, by rfl⟩) R72977
theorem R179729 : Reach 179729 := rs (se 2 (by rfl) ⟨67398, by rfl⟩) R134797
theorem R48663 : Reach 48663 := rs (se 1 (by rfl) ⟨36497, by rfl⟩) R72995
theorem R48683 : Reach 48683 := rs (se 1 (by rfl) ⟨36512, by rfl⟩) R73025
theorem R114227 : Reach 114227 := rs (se 1 (by rfl) ⟨85670, by rfl⟩) R171341
theorem R48695 : Reach 48695 := rs (se 1 (by rfl) ⟨36521, by rfl⟩) R73043
theorem R48715 : Reach 48715 := rs (se 1 (by rfl) ⟨36536, by rfl⟩) R73073
theorem R48727 : Reach 48727 := rs (se 1 (by rfl) ⟨36545, by rfl⟩) R73091
theorem R48747 : Reach 48747 := rs (se 1 (by rfl) ⟨36560, by rfl⟩) R73121
theorem R48759 : Reach 48759 := rs (se 1 (by rfl) ⟨36569, by rfl⟩) R73139
theorem R48779 : Reach 48779 := rs (se 1 (by rfl) ⟨36584, by rfl⟩) R73169
theorem R48791 : Reach 48791 := rs (se 1 (by rfl) ⟨36593, by rfl⟩) R73187
theorem R48811 : Reach 48811 := rs (se 1 (by rfl) ⟨36608, by rfl⟩) R73217
theorem R48823 : Reach 48823 := rs (se 1 (by rfl) ⟨36617, by rfl⟩) R73235
theorem R48843 : Reach 48843 := rs (se 1 (by rfl) ⟨36632, by rfl⟩) R73265
theorem R179915 : Reach 179915 := rs (se 1 (by rfl) ⟨134936, by rfl⟩) R269873
theorem R48855 : Reach 48855 := rs (se 1 (by rfl) ⟨36641, by rfl⟩) R73283
theorem R48875 : Reach 48875 := rs (se 1 (by rfl) ⟨36656, by rfl⟩) R73313
theorem R48887 : Reach 48887 := rs (se 1 (by rfl) ⟨36665, by rfl⟩) R73331
theorem R48907 : Reach 48907 := rs (se 1 (by rfl) ⟨36680, by rfl⟩) R73361
theorem R48919 : Reach 48919 := rs (se 1 (by rfl) ⟨36689, by rfl⟩) R73379
theorem R48939 : Reach 48939 := rs (se 1 (by rfl) ⟨36704, by rfl⟩) R73409
theorem R48951 : Reach 48951 := rs (se 1 (by rfl) ⟨36713, by rfl⟩) R73427
theorem R114497 : Reach 114497 := rs (se 2 (by rfl) ⟨42936, by rfl⟩) R85873
theorem R48971 : Reach 48971 := rs (se 1 (by rfl) ⟨36728, by rfl⟩) R73457
theorem R48983 : Reach 48983 := rs (se 1 (by rfl) ⟨36737, by rfl⟩) R73475
theorem R81751 : Reach 81751 := rs (se 1 (by rfl) ⟨61313, by rfl⟩) R122627
theorem R49003 : Reach 49003 := rs (se 1 (by rfl) ⟨36752, by rfl⟩) R73505
theorem R49015 : Reach 49015 := rs (se 1 (by rfl) ⟨36761, by rfl⟩) R73523
theorem R81803 : Reach 81803 := rs (se 1 (by rfl) ⟨61352, by rfl⟩) R122705
theorem R49035 : Reach 49035 := rs (se 1 (by rfl) ⟨36776, by rfl⟩) R73553
theorem R49047 : Reach 49047 := rs (se 1 (by rfl) ⟨36785, by rfl⟩) R73571
theorem R49067 : Reach 49067 := rs (se 1 (by rfl) ⟨36800, by rfl⟩) R73601
theorem R49079 : Reach 49079 := rs (se 1 (by rfl) ⟨36809, by rfl⟩) R73619
theorem R49099 : Reach 49099 := rs (se 1 (by rfl) ⟨36824, by rfl⟩) R73649
theorem R49111 : Reach 49111 := rs (se 1 (by rfl) ⟨36833, by rfl⟩) R73667
theorem R49131 : Reach 49131 := rs (se 1 (by rfl) ⟨36848, by rfl⟩) R73697
theorem R49143 : Reach 49143 := rs (se 1 (by rfl) ⟨36857, by rfl⟩) R73715
theorem R81931 : Reach 81931 := rs (se 1 (by rfl) ⟨61448, by rfl⟩) R122897
theorem R49163 : Reach 49163 := rs (se 1 (by rfl) ⟨36872, by rfl⟩) R73745
theorem R49175 : Reach 49175 := rs (se 1 (by rfl) ⟨36881, by rfl⟩) R73763
theorem R49195 : Reach 49195 := rs (se 1 (by rfl) ⟨36896, by rfl⟩) R73793
theorem R49207 : Reach 49207 := rs (se 1 (by rfl) ⟨36905, by rfl⟩) R73811
theorem R49227 : Reach 49227 := rs (se 1 (by rfl) ⟨36920, by rfl⟩) R73841
theorem R49239 : Reach 49239 := rs (se 1 (by rfl) ⟨36929, by rfl⟩) R73859
theorem R49259 : Reach 49259 := rs (se 1 (by rfl) ⟨36944, by rfl⟩) R73889
theorem R49271 : Reach 49271 := rs (se 1 (by rfl) ⟨36953, by rfl⟩) R73907
theorem R49291 : Reach 49291 := rs (se 1 (by rfl) ⟨36968, by rfl⟩) R73937
theorem R49303 : Reach 49303 := rs (se 1 (by rfl) ⟨36977, by rfl⟩) R73955
theorem R114839 : Reach 114839 := rs (se 1 (by rfl) ⟨86129, by rfl⟩) R172259
theorem R82073 : Reach 82073 := rs (se 2 (by rfl) ⟨30777, by rfl⟩) R61555
theorem R49323 : Reach 49323 := rs (se 1 (by rfl) ⟨36992, by rfl⟩) R73985
theorem R49335 : Reach 49335 := rs (se 1 (by rfl) ⟨37001, by rfl⟩) R74003
theorem R180427 : Reach 180427 := rs (se 1 (by rfl) ⟨135320, by rfl⟩) R270641
theorem R49355 : Reach 49355 := rs (se 1 (by rfl) ⟨37016, by rfl⟩) R74033
theorem R49367 : Reach 49367 := rs (se 1 (by rfl) ⟨37025, by rfl⟩) R74051
theorem R49387 : Reach 49387 := rs (se 1 (by rfl) ⟨37040, by rfl⟩) R74081
theorem R49399 : Reach 49399 := rs (se 1 (by rfl) ⟨37049, by rfl⟩) R74099
theorem R49419 : Reach 49419 := rs (se 1 (by rfl) ⟨37064, by rfl⟩) R74129
theorem R49431 : Reach 49431 := rs (se 1 (by rfl) ⟨37073, by rfl⟩) R74147
theorem R82201 : Reach 82201 := rs (se 2 (by rfl) ⟨30825, by rfl⟩) R61651
theorem R49451 : Reach 49451 := rs (se 1 (by rfl) ⟨37088, by rfl⟩) R74177
theorem R49463 : Reach 49463 := rs (se 1 (by rfl) ⟨37097, by rfl⟩) R74195
theorem R49483 : Reach 49483 := rs (se 1 (by rfl) ⟨37112, by rfl⟩) R74225
theorem R115019 : Reach 115019 := rs (se 1 (by rfl) ⟨86264, by rfl⟩) R172529
theorem R49495 : Reach 49495 := rs (se 1 (by rfl) ⟨37121, by rfl⟩) R74243
theorem R49515 : Reach 49515 := rs (se 1 (by rfl) ⟨37136, by rfl⟩) R74273
theorem R49527 : Reach 49527 := rs (se 1 (by rfl) ⟨37145, by rfl⟩) R74291
theorem R49547 : Reach 49547 := rs (se 1 (by rfl) ⟨37160, by rfl⟩) R74321
theorem R49559 : Reach 49559 := rs (se 1 (by rfl) ⟨37169, by rfl⟩) R74339
theorem R49579 : Reach 49579 := rs (se 1 (by rfl) ⟨37184, by rfl⟩) R74369
theorem R49591 : Reach 49591 := rs (se 1 (by rfl) ⟨37193, by rfl⟩) R74387
theorem R49611 : Reach 49611 := rs (se 1 (by rfl) ⟨37208, by rfl⟩) R74417
theorem R49623 : Reach 49623 := rs (se 1 (by rfl) ⟨37217, by rfl⟩) R74435
theorem R180701 : Reach 180701 := rs (se 3 (by rfl) ⟨33881, by rfl⟩) R67763
theorem R49643 : Reach 49643 := rs (se 1 (by rfl) ⟨37232, by rfl⟩) R74465
theorem R49655 : Reach 49655 := rs (se 1 (by rfl) ⟨37241, by rfl⟩) R74483
theorem R49675 : Reach 49675 := rs (se 1 (by rfl) ⟨37256, by rfl⟩) R74513
theorem R49687 : Reach 49687 := rs (se 1 (by rfl) ⟨37265, by rfl⟩) R74531
theorem R49707 : Reach 49707 := rs (se 1 (by rfl) ⟨37280, by rfl⟩) R74561
theorem R49719 : Reach 49719 := rs (se 1 (by rfl) ⟨37289, by rfl⟩) R74579
theorem R49739 : Reach 49739 := rs (se 1 (by rfl) ⟨37304, by rfl⟩) R74609
theorem R49751 : Reach 49751 := rs (se 1 (by rfl) ⟨37313, by rfl⟩) R74627
theorem R49771 : Reach 49771 := rs (se 1 (by rfl) ⟨37328, by rfl⟩) R74657
theorem R49783 : Reach 49783 := rs (se 1 (by rfl) ⟨37337, by rfl⟩) R74675
theorem R49803 : Reach 49803 := rs (se 1 (by rfl) ⟨37352, by rfl⟩) R74705
theorem R49815 : Reach 49815 := rs (se 1 (by rfl) ⟨37361, by rfl⟩) R74723
theorem R49835 : Reach 49835 := rs (se 1 (by rfl) ⟨37376, by rfl⟩) R74753
theorem R49847 : Reach 49847 := rs (se 1 (by rfl) ⟨37385, by rfl⟩) R74771
theorem R49867 : Reach 49867 := rs (se 1 (by rfl) ⟨37400, by rfl⟩) R74801
theorem R49879 : Reach 49879 := rs (se 1 (by rfl) ⟨37409, by rfl⟩) R74819
theorem R49899 : Reach 49899 := rs (se 1 (by rfl) ⟨37424, by rfl⟩) R74849
theorem R49911 : Reach 49911 := rs (se 1 (by rfl) ⟨37433, by rfl⟩) R74867
theorem R49931 : Reach 49931 := rs (se 1 (by rfl) ⟨37448, by rfl⟩) R74897
theorem R49943 : Reach 49943 := rs (se 1 (by rfl) ⟨37457, by rfl⟩) R74915
theorem R49963 : Reach 49963 := rs (se 1 (by rfl) ⟨37472, by rfl⟩) R74945
theorem R114137 : Reach 114137 := rs (se 2 (by rfl) ⟨42801, by rfl⟩) R85603
theorem R49975 : Reach 49975 := rs (se 1 (by rfl) ⟨37481, by rfl⟩) R74963
theorem R82763 : Reach 82763 := rs (se 1 (by rfl) ⟨62072, by rfl⟩) R124145
theorem R49995 : Reach 49995 := rs (se 1 (by rfl) ⟨37496, by rfl⟩) R74993
theorem R82775 : Reach 82775 := rs (se 1 (by rfl) ⟨62081, by rfl⟩) R124163
theorem R50007 : Reach 50007 := rs (se 1 (by rfl) ⟨37505, by rfl⟩) R75011
theorem R279389 : Reach 279389 := rs (se 3 (by rfl) ⟨52385, by rfl⟩) R104771
theorem R50027 : Reach 50027 := rs (se 1 (by rfl) ⟨37520, by rfl⟩) R75041
theorem R50039 : Reach 50039 := rs (se 1 (by rfl) ⟨37529, by rfl⟩) R75059
theorem R50059 : Reach 50059 := rs (se 1 (by rfl) ⟨37544, by rfl⟩) R75089
theorem R50071 : Reach 50071 := rs (se 1 (by rfl) ⟨37553, by rfl⟩) R75107
theorem R50091 : Reach 50091 := rs (se 1 (by rfl) ⟨37568, by rfl⟩) R75137
theorem R50103 : Reach 50103 := rs (se 1 (by rfl) ⟨37577, by rfl⟩) R75155
theorem R50123 : Reach 50123 := rs (se 1 (by rfl) ⟨37592, by rfl⟩) R75185
theorem R82903 : Reach 82903 := rs (se 1 (by rfl) ⟨62177, by rfl⟩) R124355
theorem R50135 : Reach 50135 := rs (se 1 (by rfl) ⟨37601, by rfl⟩) R75203
theorem R50155 : Reach 50155 := rs (se 1 (by rfl) ⟨37616, by rfl⟩) R75233
theorem R50167 : Reach 50167 := rs (se 1 (by rfl) ⟨37625, by rfl⟩) R75251
theorem R50187 : Reach 50187 := rs (se 1 (by rfl) ⟨37640, by rfl⟩) R75281
theorem R50199 : Reach 50199 := rs (se 1 (by rfl) ⟨37649, by rfl⟩) R75299
theorem R50219 : Reach 50219 := rs (se 1 (by rfl) ⟨37664, by rfl⟩) R75329
theorem R50231 : Reach 50231 := rs (se 1 (by rfl) ⟨37673, by rfl⟩) R75347
theorem R50251 : Reach 50251 := rs (se 1 (by rfl) ⟨37688, by rfl⟩) R75377
theorem R50263 : Reach 50263 := rs (se 1 (by rfl) ⟨37697, by rfl⟩) R75395
theorem R50283 : Reach 50283 := rs (se 1 (by rfl) ⟨37712, by rfl⟩) R75425
theorem R50295 : Reach 50295 := rs (se 1 (by rfl) ⟨37721, by rfl⟩) R75443
theorem R181379 : Reach 181379 := rs (se 1 (by rfl) ⟨136034, by rfl⟩) R272069
theorem R50315 : Reach 50315 := rs (se 1 (by rfl) ⟨37736, by rfl⟩) R75473
theorem R181399 : Reach 181399 := rs (se 1 (by rfl) ⟨136049, by rfl⟩) R272099
theorem R50327 : Reach 50327 := rs (se 1 (by rfl) ⟨37745, by rfl⟩) R75491
theorem R50347 : Reach 50347 := rs (se 1 (by rfl) ⟨37760, by rfl⟩) R75521
theorem R50359 : Reach 50359 := rs (se 1 (by rfl) ⟨37769, by rfl⟩) R75539
theorem R50379 : Reach 50379 := rs (se 1 (by rfl) ⟨37784, by rfl⟩) R75569
theorem R50391 : Reach 50391 := rs (se 1 (by rfl) ⟨37793, by rfl⟩) R75587
theorem R50411 : Reach 50411 := rs (se 1 (by rfl) ⟨37808, by rfl⟩) R75617
theorem R50423 : Reach 50423 := rs (se 1 (by rfl) ⟨37817, by rfl⟩) R75635
theorem R50443 : Reach 50443 := rs (se 1 (by rfl) ⟨37832, by rfl⟩) R75665
theorem R50455 : Reach 50455 := rs (se 1 (by rfl) ⟨37841, by rfl⟩) R75683
theorem R50475 : Reach 50475 := rs (se 1 (by rfl) ⟨37856, by rfl⟩) R75713
theorem R50487 : Reach 50487 := rs (se 1 (by rfl) ⟨37865, by rfl⟩) R75731
theorem R50507 : Reach 50507 := rs (se 1 (by rfl) ⟨37880, by rfl⟩) R75761
theorem R50519 : Reach 50519 := rs (se 1 (by rfl) ⟨37889, by rfl⟩) R75779
theorem R50539 : Reach 50539 := rs (se 1 (by rfl) ⟨37904, by rfl⟩) R75809
theorem R50551 : Reach 50551 := rs (se 1 (by rfl) ⟨37913, by rfl⟩) R75827
theorem R50571 : Reach 50571 := rs (se 1 (by rfl) ⟨37928, by rfl⟩) R75857
theorem R50583 : Reach 50583 := rs (se 1 (by rfl) ⟨37937, by rfl⟩) R75875
theorem R50603 : Reach 50603 := rs (se 1 (by rfl) ⟨37952, by rfl⟩) R75905
theorem R50615 : Reach 50615 := rs (se 1 (by rfl) ⟨37961, by rfl⟩) R75923
theorem R50635 : Reach 50635 := rs (se 1 (by rfl) ⟨37976, by rfl⟩) R75953
theorem R50647 : Reach 50647 := rs (se 1 (by rfl) ⟨37985, by rfl⟩) R75971
theorem R50667 : Reach 50667 := rs (se 1 (by rfl) ⟨38000, by rfl⟩) R76001
theorem R50679 : Reach 50679 := rs (se 1 (by rfl) ⟨38009, by rfl⟩) R76019
theorem R50699 : Reach 50699 := rs (se 1 (by rfl) ⟨38024, by rfl⟩) R76049
theorem R50711 : Reach 50711 := rs (se 1 (by rfl) ⟨38033, by rfl⟩) R76067
theorem R149015 : Reach 149015 := rs (se 1 (by rfl) ⟨111761, by rfl⟩) R223523
theorem R50731 : Reach 50731 := rs (se 1 (by rfl) ⟨38048, by rfl⟩) R76097
theorem R50743 : Reach 50743 := rs (se 1 (by rfl) ⟨38057, by rfl⟩) R76115
theorem R83531 : Reach 83531 := rs (se 1 (by rfl) ⟨62648, by rfl⟩) R125297
theorem R50763 : Reach 50763 := rs (se 1 (by rfl) ⟨38072, by rfl⟩) R76145
theorem R50775 : Reach 50775 := rs (se 1 (by rfl) ⟨38081, by rfl⟩) R76163
theorem R50795 : Reach 50795 := rs (se 1 (by rfl) ⟨38096, by rfl⟩) R76193
theorem R50807 : Reach 50807 := rs (se 1 (by rfl) ⟨38105, by rfl⟩) R76211
theorem R50827 : Reach 50827 := rs (se 1 (by rfl) ⟨38120, by rfl⟩) R76241
theorem R312983 : Reach 312983 := rs (se 1 (by rfl) ⟨234737, by rfl⟩) R469475
theorem R50839 : Reach 50839 := rs (se 1 (by rfl) ⟨38129, by rfl⟩) R76259
theorem R50859 : Reach 50859 := rs (se 1 (by rfl) ⟨38144, by rfl⟩) R76289
theorem R50871 : Reach 50871 := rs (se 1 (by rfl) ⟨38153, by rfl⟩) R76307
theorem R214721 : Reach 214721 := rs (se 2 (by rfl) ⟨80520, by rfl⟩) R161041
theorem R83659 : Reach 83659 := rs (se 1 (by rfl) ⟨62744, by rfl⟩) R125489
theorem R50891 : Reach 50891 := rs (se 1 (by rfl) ⟨38168, by rfl⟩) R76337
theorem R50903 : Reach 50903 := rs (se 1 (by rfl) ⟨38177, by rfl⟩) R76355
theorem R50923 : Reach 50923 := rs (se 1 (by rfl) ⟨38192, by rfl⟩) R76385
theorem R50935 : Reach 50935 := rs (se 1 (by rfl) ⟨38201, by rfl⟩) R76403
theorem R50955 : Reach 50955 := rs (se 1 (by rfl) ⟨38216, by rfl⟩) R76433
theorem R50967 : Reach 50967 := rs (se 1 (by rfl) ⟨38225, by rfl⟩) R76451
theorem R50987 : Reach 50987 := rs (se 1 (by rfl) ⟨38240, by rfl⟩) R76481
theorem R50999 : Reach 50999 := rs (se 1 (by rfl) ⟨38249, by rfl⟩) R76499
theorem R51019 : Reach 51019 := rs (se 1 (by rfl) ⟨38264, by rfl⟩) R76529
theorem R51031 : Reach 51031 := rs (se 1 (by rfl) ⟨38273, by rfl⟩) R76547
theorem R83801 : Reach 83801 := rs (se 2 (by rfl) ⟨31425, by rfl⟩) R62851
theorem R51051 : Reach 51051 := rs (se 1 (by rfl) ⟨38288, by rfl⟩) R76577
theorem R51063 : Reach 51063 := rs (se 1 (by rfl) ⟨38297, by rfl⟩) R76595
theorem R51083 : Reach 51083 := rs (se 1 (by rfl) ⟨38312, by rfl⟩) R76625
theorem R51095 : Reach 51095 := rs (se 1 (by rfl) ⟨38321, by rfl⟩) R76643
theorem R51115 : Reach 51115 := rs (se 1 (by rfl) ⟨38336, by rfl⟩) R76673
theorem R182189 : Reach 182189 := rs (se 3 (by rfl) ⟨34160, by rfl⟩) R68321
theorem R83929 : Reach 83929 := rs (se 2 (by rfl) ⟨31473, by rfl⟩) R62947
theorem R968773 : Reach 968773 := rs (se 4 (by rfl) ⟨90822, by rfl⟩) R181645
theorem R247901 : Reach 247901 := rs (se 3 (by rfl) ⟨46481, by rfl⟩) R92963
theorem R84235 : Reach 84235 := rs (se 1 (by rfl) ⟨63176, by rfl⟩) R126353
theorem R84503 : Reach 84503 := rs (se 1 (by rfl) ⟨63377, by rfl⟩) R126755
theorem R84631 : Reach 84631 := rs (se 1 (by rfl) ⟨63473, by rfl⟩) R126947
theorem R248669 : Reach 248669 := rs (se 3 (by rfl) ⟨46625, by rfl⟩) R93251
theorem R85043 : Reach 85043 := rs (se 1 (by rfl) ⟨63782, by rfl⟩) R127565
theorem R85171 : Reach 85171 := rs (se 1 (by rfl) ⟨63878, by rfl⟩) R127757
theorem R52471 : Reach 52471 := rs (se 1 (by rfl) ⟨39353, by rfl⟩) R78707
theorem R85259 : Reach 85259 := rs (se 1 (by rfl) ⟨63944, by rfl⟩) R127889
theorem R183617 : Reach 183617 := rs (se 2 (by rfl) ⟨68856, by rfl⟩) R137713
theorem R85313 : Reach 85313 := rs (se 2 (by rfl) ⟨31992, by rfl⟩) R63985
theorem R118091 : Reach 118091 := rs (se 1 (by rfl) ⟨88568, by rfl⟩) R177137
theorem R281987 : Reach 281987 := rs (se 1 (by rfl) ⟨211490, by rfl⟩) R422981
theorem R85387 : Reach 85387 := rs (se 1 (by rfl) ⟨64040, by rfl⟩) R128081
theorem R85441 : Reach 85441 := rs (se 2 (by rfl) ⟨32040, by rfl⟩) R64081
theorem R347665 : Reach 347665 := rs (se 2 (by rfl) ⟨130374, by rfl⟩) R260749
theorem R85529 : Reach 85529 := rs (se 2 (by rfl) ⟨32073, by rfl⟩) R64147
theorem R347723 : Reach 347723 := rs (se 1 (by rfl) ⟨260792, by rfl⟩) R521585
theorem R85657 : Reach 85657 := rs (se 2 (by rfl) ⟨32121, by rfl⟩) R64243
theorem R118475 : Reach 118475 := rs (se 1 (by rfl) ⟨88856, by rfl⟩) R177713
theorem R53131 : Reach 53131 := rs (se 1 (by rfl) ⟨39848, by rfl⟩) R79697
theorem R479155 : Reach 479155 := rs (se 1 (by rfl) ⟨359366, by rfl⟩) R718733
theorem R577459 : Reach 577459 := rs (se 1 (by rfl) ⟨433094, by rfl⟩) R866189
theorem R53239 : Reach 53239 := rs (se 1 (by rfl) ⟨39929, by rfl⟩) R79859
theorem R217181 : Reach 217181 := rs (se 3 (by rfl) ⟨40721, by rfl⟩) R81443
theorem R53419 : Reach 53419 := rs (se 1 (by rfl) ⟨40064, by rfl⟩) R80129
theorem R86231 : Reach 86231 := rs (se 1 (by rfl) ⟨64673, by rfl⟩) R129347
theorem R86273 : Reach 86273 := rs (se 2 (by rfl) ⟨32352, by rfl⟩) R64705
theorem R53527 : Reach 53527 := rs (se 1 (by rfl) ⟨40145, by rfl⟩) R80291
theorem R53707 : Reach 53707 := rs (se 1 (by rfl) ⟨40280, by rfl⟩) R80561
theorem R53815 : Reach 53815 := rs (se 1 (by rfl) ⟨40361, by rfl⟩) R80723
theorem R53995 : Reach 53995 := rs (se 1 (by rfl) ⟨40496, by rfl⟩) R80993
theorem R774917 : Reach 774917 := rs (se 4 (by rfl) ⟨72648, by rfl⟩) R145297
theorem R185105 : Reach 185105 := rs (se 2 (by rfl) ⟨69414, by rfl⟩) R138829
theorem R119627 : Reach 119627 := rs (se 1 (by rfl) ⟨89720, by rfl⟩) R179441
theorem R54103 : Reach 54103 := rs (se 1 (by rfl) ⟨40577, by rfl⟩) R81155
theorem R250775 : Reach 250775 := rs (se 1 (by rfl) ⟨188081, by rfl⟩) R376163
theorem R54283 : Reach 54283 := rs (se 1 (by rfl) ⟨40712, by rfl⟩) R81425
theorem R152669 : Reach 152669 := rs (se 3 (by rfl) ⟨28625, by rfl⟩) R57251
theorem R54391 : Reach 54391 := rs (se 1 (by rfl) ⟨40793, by rfl⟩) R81587
theorem R316547 : Reach 316547 := rs (se 1 (by rfl) ⟨237410, by rfl⟩) R474821
theorem R120001 : Reach 120001 := rs (se 2 (by rfl) ⟨45000, by rfl⟩) R90001
theorem R185561 : Reach 185561 := rs (se 2 (by rfl) ⟨69585, by rfl⟩) R139171
theorem R677105 : Reach 677105 := rs (se 2 (by rfl) ⟨253914, by rfl⟩) R507829
theorem R54571 : Reach 54571 := rs (se 1 (by rfl) ⟨40928, by rfl⟩) R81857
theorem R218513 : Reach 218513 := rs (se 2 (by rfl) ⟨81942, by rfl⟩) R163885
theorem R54679 : Reach 54679 := rs (se 1 (by rfl) ⟨41009, by rfl⟩) R82019
theorem R185773 : Reach 185773 := rs (se 3 (by rfl) ⟨34832, by rfl⟩) R69665
theorem R382481 : Reach 382481 := rs (se 2 (by rfl) ⟨143430, by rfl⟩) R286861
theorem R54859 : Reach 54859 := rs (se 1 (by rfl) ⟨41144, by rfl⟩) R82289
theorem R186029 : Reach 186029 := rs (se 3 (by rfl) ⟨34880, by rfl⟩) R69761
theorem R54967 : Reach 54967 := rs (se 1 (by rfl) ⟨41225, by rfl⟩) R82451
theorem R349913 : Reach 349913 := rs (se 2 (by rfl) ⟨131217, by rfl⟩) R262435
theorem R186077 : Reach 186077 := rs (se 3 (by rfl) ⟨34889, by rfl⟩) R69779
theorem R120599 : Reach 120599 := rs (se 1 (by rfl) ⟨90449, by rfl⟩) R180899
theorem R55147 : Reach 55147 := rs (se 1 (by rfl) ⟨41360, by rfl⟩) R82721
theorem R55255 : Reach 55255 := rs (se 1 (by rfl) ⟨41441, by rfl⟩) R82883
theorem R55435 : Reach 55435 := rs (se 1 (by rfl) ⟨41576, by rfl⟩) R83153
theorem R153751 : Reach 153751 := rs (se 1 (by rfl) ⟨115313, by rfl⟩) R230627
theorem R55543 : Reach 55543 := rs (se 1 (by rfl) ⟨41657, by rfl⟩) R83315
theorem R55723 : Reach 55723 := rs (se 1 (by rfl) ⟨41792, by rfl⟩) R83585
theorem R55831 : Reach 55831 := rs (se 1 (by rfl) ⟨41873, by rfl⟩) R83747
theorem R121409 : Reach 121409 := rs (se 2 (by rfl) ⟨45528, by rfl⟩) R91057
theorem R88705 : Reach 88705 := rs (se 2 (by rfl) ⟨33264, by rfl⟩) R66529
theorem R56011 : Reach 56011 := rs (se 1 (by rfl) ⟨42008, by rfl⟩) R84017
theorem R187201 : Reach 187201 := rs (se 2 (by rfl) ⟨70200, by rfl⟩) R140401
theorem R121675 : Reach 121675 := rs (se 1 (by rfl) ⟨91256, by rfl⟩) R182513
theorem R121751 : Reach 121751 := rs (se 1 (by rfl) ⟨91313, by rfl⟩) R182627
theorem R56407 : Reach 56407 := rs (se 1 (by rfl) ⟨42305, by rfl⟩) R84611
theorem R121945 : Reach 121945 := rs (se 2 (by rfl) ⟨45729, by rfl⟩) R91459
theorem R56587 : Reach 56587 := rs (se 1 (by rfl) ⟨42440, by rfl⟩) R84881
theorem R56791 : Reach 56791 := rs (se 1 (by rfl) ⟨42593, by rfl⟩) R85187
theorem R89561 : Reach 89561 := rs (se 2 (by rfl) ⟨33585, by rfl⟩) R67171
theorem R155159 : Reach 155159 := rs (se 1 (by rfl) ⟨116369, by rfl⟩) R232739
theorem R56983 : Reach 56983 := rs (se 1 (by rfl) ⟨42737, by rfl⟩) R85475
theorem R417581 : Reach 417581 := rs (se 3 (by rfl) ⟨78296, by rfl⟩) R156593
theorem R57163 : Reach 57163 := rs (se 1 (by rfl) ⟨42872, by rfl⟩) R85745
theorem R123059 : Reach 123059 := rs (se 1 (by rfl) ⟨92294, by rfl⟩) R184589
theorem R90305 : Reach 90305 := rs (se 2 (by rfl) ⟨33864, by rfl⟩) R67729
theorem R778481 : Reach 778481 := rs (se 2 (by rfl) ⟨291930, by rfl⟩) R583861
theorem R188675 : Reach 188675 := rs (se 1 (by rfl) ⟨141506, by rfl⟩) R283013
theorem R286993 : Reach 286993 := rs (se 2 (by rfl) ⟨107622, by rfl⟩) R215245
theorem R188689 : Reach 188689 := rs (se 2 (by rfl) ⟨70758, by rfl⟩) R141517
theorem R155927 : Reach 155927 := rs (se 1 (by rfl) ⟨116945, by rfl⟩) R233891
theorem R90391 : Reach 90391 := rs (se 1 (by rfl) ⟨67793, by rfl⟩) R135587
theorem R811309 : Reach 811309 := rs (se 3 (by rfl) ⟨152120, by rfl⟩) R304241
theorem R680293 : Reach 680293 := rs (se 4 (by rfl) ⟨63777, by rfl⟩) R127555
theorem R254339 : Reach 254339 := rs (se 1 (by rfl) ⟨190754, by rfl⟩) R381509
theorem R90571 : Reach 90571 := rs (se 1 (by rfl) ⟨67928, by rfl⟩) R135857
theorem R123353 : Reach 123353 := rs (se 2 (by rfl) ⟨46257, by rfl⟩) R92515
theorem R188993 : Reach 188993 := rs (se 2 (by rfl) ⟨70872, by rfl⟩) R141745
theorem R58007 : Reach 58007 := rs (se 1 (by rfl) ⟨43505, by rfl⟩) R87011
theorem R156439 : Reach 156439 := rs (se 1 (by rfl) ⟨117329, by rfl⟩) R234659
theorem R91019 : Reach 91019 := rs (se 1 (by rfl) ⟨68264, by rfl⟩) R136529
theorem R58315 : Reach 58315 := rs (se 1 (by rfl) ⟨43736, by rfl⟩) R87473
theorem R2057237 : Reach 2057237 := rs (se 6 (by rfl) ⟨48216, by rfl⟩) R96433
theorem R91201 : Reach 91201 := rs (se 2 (by rfl) ⟨34200, by rfl⟩) R68401
theorem R287819 : Reach 287819 := rs (se 1 (by rfl) ⟨215864, by rfl⟩) R431729
theorem R189661 : Reach 189661 := rs (se 3 (by rfl) ⟨35561, by rfl⟩) R71123
theorem R386369 : Reach 386369 := rs (se 2 (by rfl) ⟨144888, by rfl⟩) R289777
theorem R91543 : Reach 91543 := rs (se 1 (by rfl) ⟨68657, by rfl⟩) R137315
theorem R157259 : Reach 157259 := rs (se 1 (by rfl) ⟨117944, by rfl⟩) R235889
theorem R91763 : Reach 91763 := rs (se 1 (by rfl) ⟨68822, by rfl⟩) R137645
theorem R91955 : Reach 91955 := rs (se 1 (by rfl) ⟨68966, by rfl⟩) R137933
theorem R91991 : Reach 91991 := rs (se 1 (by rfl) ⟨68993, by rfl⟩) R137987
theorem R157619 : Reach 157619 := rs (se 1 (by rfl) ⟨118214, by rfl⟩) R236429
theorem R92107 : Reach 92107 := rs (se 1 (by rfl) ⟨69080, by rfl⟩) R138161
theorem R125003 : Reach 125003 := rs (se 1 (by rfl) ⟨93752, by rfl⟩) R187505
theorem R92249 : Reach 92249 := rs (se 2 (by rfl) ⟨34593, by rfl⟩) R69187
theorem R321893 : Reach 321893 := rs (se 4 (by rfl) ⟨30177, by rfl⟩) R60355
theorem R190937 : Reach 190937 := rs (se 2 (by rfl) ⟨71601, by rfl⟩) R143203
theorem R92659 : Reach 92659 := rs (se 1 (by rfl) ⟨69494, by rfl⟩) R138989
theorem R93079 : Reach 93079 := rs (se 1 (by rfl) ⟨69809, by rfl⟩) R139619
theorem R93145 : Reach 93145 := rs (se 2 (by rfl) ⟨34929, by rfl⟩) R69859
theorem R125975 : Reach 125975 := rs (se 1 (by rfl) ⟨94481, by rfl⟩) R188963
theorem R945413 : Reach 945413 := rs (se 4 (by rfl) ⟨88632, by rfl⟩) R177265
theorem R421271 : Reach 421271 := rs (se 1 (by rfl) ⟨315953, by rfl⟩) R631907
theorem R650713 : Reach 650713 := rs (se 2 (by rfl) ⟨244017, by rfl⟩) R488035
theorem R93707 : Reach 93707 := rs (se 1 (by rfl) ⟨70280, by rfl⟩) R140561
theorem R585251 : Reach 585251 := rs (se 1 (by rfl) ⟨438938, by rfl⟩) R877877
theorem R61003 : Reach 61003 := rs (se 1 (by rfl) ⟨45752, by rfl⟩) R91505
theorem R93847 : Reach 93847 := rs (se 1 (by rfl) ⟨70385, by rfl⟩) R140771
theorem R126643 : Reach 126643 := rs (se 1 (by rfl) ⟨94982, by rfl⟩) R189965
theorem R93889 : Reach 93889 := rs (se 2 (by rfl) ⟨35208, by rfl⟩) R70417
theorem R126785 : Reach 126785 := rs (se 2 (by rfl) ⟨47544, by rfl⟩) R95089
theorem R192449 : Reach 192449 := rs (se 2 (by rfl) ⟨72168, by rfl⟩) R144337
theorem R126937 : Reach 126937 := rs (se 2 (by rfl) ⟨47601, by rfl⟩) R95203
theorem R258065 : Reach 258065 := rs (se 2 (by rfl) ⟨96774, by rfl⟩) R193549
theorem R192563 : Reach 192563 := rs (se 1 (by rfl) ⟨144422, by rfl⟩) R288845
theorem R192577 : Reach 192577 := rs (se 2 (by rfl) ⟨72216, by rfl⟩) R144433
theorem R258227 : Reach 258227 := rs (se 1 (by rfl) ⟨193670, by rfl⟩) R387341
theorem R159947 : Reach 159947 := rs (se 1 (by rfl) ⟨119960, by rfl⟩) R239921
theorem R94603 : Reach 94603 := rs (se 1 (by rfl) ⟨70952, by rfl⟩) R141905
theorem R94679 : Reach 94679 := rs (se 1 (by rfl) ⟨71009, by rfl⟩) R142019
theorem R160217 : Reach 160217 := rs (se 2 (by rfl) ⟨60081, by rfl⟩) R120163
theorem R127453 : Reach 127453 := rs (se 3 (by rfl) ⟨23897, by rfl⟩) R47795
theorem R61975 : Reach 61975 := rs (se 1 (by rfl) ⟨46481, by rfl⟩) R92963
theorem R62155 : Reach 62155 := rs (se 1 (by rfl) ⟨46616, by rfl⟩) R93233
theorem R291545 : Reach 291545 := rs (se 2 (by rfl) ⟨109329, by rfl⟩) R218659
theorem R127837 : Reach 127837 := rs (se 3 (by rfl) ⟨23969, by rfl⟩) R47939
theorem R488369 : Reach 488369 := rs (se 2 (by rfl) ⟨183138, by rfl⟩) R366277
theorem R128051 : Reach 128051 := rs (se 1 (by rfl) ⟨96038, by rfl⟩) R192077
theorem R95347 : Reach 95347 := rs (se 1 (by rfl) ⟨71510, by rfl⟩) R143021
theorem R160919 : Reach 160919 := rs (se 1 (by rfl) ⟨120689, by rfl⟩) R241379
theorem R62795 : Reach 62795 := rs (se 1 (by rfl) ⟨47096, by rfl⟩) R94193
theorem R95575 : Reach 95575 := rs (se 1 (by rfl) ⟨71681, by rfl⟩) R143363
theorem R95681 : Reach 95681 := rs (se 2 (by rfl) ⟨35880, by rfl⟩) R71761
theorem R128587 : Reach 128587 := rs (se 1 (by rfl) ⟨96440, by rfl⟩) R192881
theorem R95833 : Reach 95833 := rs (se 2 (by rfl) ⟨35937, by rfl⟩) R71875
theorem R161459 : Reach 161459 := rs (se 1 (by rfl) ⟨121094, by rfl⟩) R242189
theorem R128729 : Reach 128729 := rs (se 2 (by rfl) ⟨48273, by rfl⟩) R96547
theorem R128861 : Reach 128861 := rs (se 3 (by rfl) ⟨24161, by rfl⟩) R48323
theorem R522101 : Reach 522101 := rs (se 5 (by rfl) ⟨24473, by rfl⟩) R48947
theorem R161729 : Reach 161729 := rs (se 2 (by rfl) ⟨60648, by rfl⟩) R121297
theorem R194525 : Reach 194525 := rs (se 3 (by rfl) ⟨36473, by rfl⟩) R72947
theorem R63499 : Reach 63499 := rs (se 1 (by rfl) ⟨47624, by rfl⟩) R95249
theorem R96331 : Reach 96331 := rs (se 1 (by rfl) ⟨72248, by rfl⟩) R144497
theorem R260171 : Reach 260171 := rs (se 1 (by rfl) ⟨195128, by rfl⟩) R390257
theorem R63767 : Reach 63767 := rs (se 1 (by rfl) ⟨47825, by rfl⟩) R95651
theorem R326105 : Reach 326105 := rs (se 2 (by rfl) ⟨122289, by rfl⟩) R244579
theorem R162269 : Reach 162269 := rs (se 3 (by rfl) ⟨30425, by rfl⟩) R60851
theorem R359063 : Reach 359063 := rs (se 1 (by rfl) ⟨269297, by rfl⟩) R538595
theorem R64471 : Reach 64471 := rs (se 1 (by rfl) ⟨48353, by rfl⟩) R96707
theorem R195659 : Reach 195659 := rs (se 1 (by rfl) ⟨146744, by rfl⟩) R293489
theorem R392323 : Reach 392323 := rs (se 1 (by rfl) ⟨294242, by rfl⟩) R588485
theorem R228739 : Reach 228739 := rs (se 1 (by rfl) ⟨171554, by rfl⟩) R343109
theorem R163403 : Reach 163403 := rs (se 1 (by rfl) ⟨122552, by rfl⟩) R245105
theorem R163673 : Reach 163673 := rs (se 2 (by rfl) ⟨61377, by rfl⟩) R122755
theorem R65431 : Reach 65431 := rs (se 1 (by rfl) ⟨49073, by rfl⟩) R98147
theorem R1343411 : Reach 1343411 := rs (se 1 (by rfl) ⟨1007558, by rfl⟩) R2015117
theorem R40337621 : Reach 40337621 := rs (se 7 (by rfl) ⟨472706, by rfl⟩) R945413
theorem R524675 : Reach 524675 := rs (se 1 (by rfl) ⟨393506, by rfl⟩) R787013
theorem R1081745 : Reach 1081745 := rs (se 2 (by rfl) ⟨405654, by rfl⟩) R811309
theorem R229817 : Reach 229817 := rs (se 2 (by rfl) ⟨86181, by rfl⟩) R172363
theorem R99343 : Reach 99343 := rs (se 1 (by rfl) ⟨74507, by rfl⟩) R149015
theorem R459863 : Reach 459863 := rs (se 1 (by rfl) ⟨344897, by rfl⟩) R689795
theorem R886301 : Reach 886301 := rs (se 3 (by rfl) ⟨166181, by rfl⟩) R332363
theorem R67387 : Reach 67387 := rs (se 1 (by rfl) ⟨50540, by rfl⟩) R101081
theorem R67447 : Reach 67447 := rs (se 1 (by rfl) ⟨50585, by rfl⟩) R101171
theorem R165779 : Reach 165779 := rs (se 1 (by rfl) ⟨124334, by rfl⟩) R248669
theorem R919873 : Reach 919873 := rs (se 2 (by rfl) ⟨344952, by rfl⟩) R689905
theorem R231815 : Reach 231815 := rs (se 1 (by rfl) ⟨173861, by rfl⟩) R347723
theorem R395729 : Reach 395729 := rs (se 2 (by rfl) ⟨148398, by rfl⟩) R296797
theorem R592919 : Reach 592919 := rs (se 1 (by rfl) ⟨444689, by rfl⟩) R889379
theorem R167183 : Reach 167183 := rs (se 1 (by rfl) ⟨125387, by rfl⟩) R250775
theorem R363809 : Reach 363809 := rs (se 2 (by rfl) ⟨136428, by rfl⟩) R272857
theorem R101779 : Reach 101779 := rs (se 1 (by rfl) ⟨76334, by rfl⟩) R152669
theorem R167453 : Reach 167453 := rs (se 3 (by rfl) ⟨31397, by rfl⟩) R62795
theorem R233275 : Reach 233275 := rs (se 1 (by rfl) ⟨174956, by rfl⟩) R349913
theorem R135047 : Reach 135047 := rs (se 1 (by rfl) ⟨101285, by rfl⟩) R202571
theorem R135283 : Reach 135283 := rs (se 1 (by rfl) ⟨101462, by rfl⟩) R202925
theorem R69751 : Reach 69751 := rs (se 1 (by rfl) ⟨52313, by rfl⟩) R104627
theorem R233873 : Reach 233873 := rs (se 2 (by rfl) ⟨87702, by rfl⟩) R175405
theorem R364985 : Reach 364985 := rs (se 2 (by rfl) ⟨136869, by rfl⟩) R273739
theorem R70075 : Reach 70075 := rs (se 1 (by rfl) ⟨52556, by rfl⟩) R105113
theorem R135827 : Reach 135827 := rs (se 1 (by rfl) ⟨101870, by rfl⟩) R203741
theorem R463553 : Reach 463553 := rs (se 2 (by rfl) ⟨173832, by rfl⟩) R347665
theorem R168857 : Reach 168857 := rs (se 2 (by rfl) ⟨63321, by rfl⟩) R126643
theorem R70571 : Reach 70571 := rs (se 1 (by rfl) ⟨52928, by rfl⟩) R105857
theorem R103439 : Reach 103439 := rs (se 1 (by rfl) ⟨77579, by rfl⟩) R155159
theorem R70715 : Reach 70715 := rs (se 1 (by rfl) ⟨53036, by rfl⟩) R106073
theorem R70775 : Reach 70775 := rs (se 1 (by rfl) ⟨53081, by rfl⟩) R106163
theorem R70799 : Reach 70799 := rs (se 1 (by rfl) ⟨53099, by rfl⟩) R106199
theorem R70841 : Reach 70841 := rs (se 2 (by rfl) ⟨26565, by rfl⟩) R53131
theorem R103609 : Reach 103609 := rs (se 2 (by rfl) ⟨38853, by rfl⟩) R77707
theorem R70919 : Reach 70919 := rs (se 1 (by rfl) ⟨53189, by rfl⟩) R106379
theorem R169249 : Reach 169249 := rs (se 2 (by rfl) ⟨63468, by rfl⟩) R126937
theorem R70955 : Reach 70955 := rs (se 1 (by rfl) ⟨53216, by rfl⟩) R106433
theorem R70985 : Reach 70985 := rs (se 2 (by rfl) ⟨26619, by rfl⟩) R53239
theorem R71099 : Reach 71099 := rs (se 1 (by rfl) ⟨53324, by rfl⟩) R106649
theorem R71159 : Reach 71159 := rs (se 1 (by rfl) ⟨53369, by rfl⟩) R106739
theorem R71183 : Reach 71183 := rs (se 1 (by rfl) ⟨53387, by rfl⟩) R106775
theorem R103951 : Reach 103951 := rs (se 1 (by rfl) ⟨77963, by rfl⟩) R155927
theorem R202283 : Reach 202283 := rs (se 1 (by rfl) ⟨151712, by rfl⟩) R303425
theorem R71225 : Reach 71225 := rs (se 2 (by rfl) ⟨26709, by rfl⟩) R53419
theorem R661069 : Reach 661069 := rs (se 3 (by rfl) ⟨123950, by rfl⟩) R247901
theorem R169559 : Reach 169559 := rs (se 1 (by rfl) ⟨127169, by rfl⟩) R254339
theorem R71303 : Reach 71303 := rs (se 1 (by rfl) ⟨53477, by rfl⟩) R106955
theorem R71339 : Reach 71339 := rs (se 1 (by rfl) ⟨53504, by rfl⟩) R107009
theorem R71369 : Reach 71369 := rs (se 2 (by rfl) ⟨26763, by rfl⟩) R53527
theorem R136961 : Reach 136961 := rs (se 2 (by rfl) ⟨51360, by rfl⟩) R102721
theorem R71483 : Reach 71483 := rs (se 1 (by rfl) ⟨53612, by rfl⟩) R107225
theorem R71543 : Reach 71543 := rs (se 1 (by rfl) ⟨53657, by rfl⟩) R107315
theorem R71567 : Reach 71567 := rs (se 1 (by rfl) ⟨53675, by rfl⟩) R107351
theorem R71609 : Reach 71609 := rs (se 2 (by rfl) ⟨26853, by rfl⟩) R53707
theorem R169937 : Reach 169937 := rs (se 2 (by rfl) ⟨63726, by rfl⟩) R127453
theorem R71687 : Reach 71687 := rs (se 1 (by rfl) ⟨53765, by rfl⟩) R107531
theorem R71695 : Reach 71695 := rs (se 1 (by rfl) ⟨53771, by rfl⟩) R107543
theorem R71723 : Reach 71723 := rs (se 1 (by rfl) ⟨53792, by rfl⟩) R107585
theorem R170045 : Reach 170045 := rs (se 3 (by rfl) ⟨31883, by rfl⟩) R63767
theorem R71753 : Reach 71753 := rs (se 2 (by rfl) ⟨26907, by rfl⟩) R53815
theorem R71867 : Reach 71867 := rs (se 1 (by rfl) ⟨53900, by rfl⟩) R107801
theorem R71927 : Reach 71927 := rs (se 1 (by rfl) ⟨53945, by rfl⟩) R107891
theorem R71951 : Reach 71951 := rs (se 1 (by rfl) ⟨53963, by rfl⟩) R107927
theorem R71993 : Reach 71993 := rs (se 2 (by rfl) ⟨26997, by rfl⟩) R53995
theorem R137531 : Reach 137531 := rs (se 1 (by rfl) ⟨103148, by rfl⟩) R206297
theorem R72071 : Reach 72071 := rs (se 1 (by rfl) ⟨54053, by rfl⟩) R108107
theorem R72107 : Reach 72107 := rs (se 1 (by rfl) ⟨54080, by rfl⟩) R108161
theorem R72137 : Reach 72137 := rs (se 2 (by rfl) ⟨27051, by rfl⟩) R54103
theorem R137771 : Reach 137771 := rs (se 1 (by rfl) ⟨103328, by rfl⟩) R206657
theorem R72251 : Reach 72251 := rs (se 1 (by rfl) ⟨54188, by rfl⟩) R108377
theorem R105079 : Reach 105079 := rs (se 1 (by rfl) ⟨78809, by rfl⟩) R157619
theorem R72311 : Reach 72311 := rs (se 1 (by rfl) ⟨54233, by rfl⟩) R108467
theorem R72335 : Reach 72335 := rs (se 1 (by rfl) ⟨54251, by rfl⟩) R108503
theorem R72377 : Reach 72377 := rs (se 2 (by rfl) ⟨27141, by rfl⟩) R54283
theorem R72455 : Reach 72455 := rs (se 1 (by rfl) ⟨54341, by rfl⟩) R108683
theorem R72491 : Reach 72491 := rs (se 1 (by rfl) ⟨54368, by rfl⟩) R108737
theorem R72521 : Reach 72521 := rs (se 2 (by rfl) ⟨27195, by rfl⟩) R54391
theorem R72635 : Reach 72635 := rs (se 1 (by rfl) ⟨54476, by rfl⟩) R108953
theorem R72695 : Reach 72695 := rs (se 1 (by rfl) ⟨54521, by rfl⟩) R109043
theorem R72719 : Reach 72719 := rs (se 1 (by rfl) ⟨54539, by rfl⟩) R109079
theorem R269335 : Reach 269335 := rs (se 1 (by rfl) ⟨202001, by rfl⟩) R404003
theorem R72761 : Reach 72761 := rs (se 2 (by rfl) ⟨27285, by rfl⟩) R54571
theorem R72839 : Reach 72839 := rs (se 1 (by rfl) ⟨54629, by rfl⟩) R109259
theorem R72875 : Reach 72875 := rs (se 1 (by rfl) ⟨54656, by rfl⟩) R109313
theorem R72905 : Reach 72905 := rs (se 2 (by rfl) ⟨27339, by rfl⟩) R54679
theorem R73019 : Reach 73019 := rs (se 1 (by rfl) ⟨54764, by rfl⟩) R109529
theorem R73079 : Reach 73079 := rs (se 1 (by rfl) ⟨54809, by rfl⟩) R109619
theorem R73103 : Reach 73103 := rs (se 1 (by rfl) ⟨54827, by rfl⟩) R109655
theorem R73145 : Reach 73145 := rs (se 2 (by rfl) ⟨27429, by rfl⟩) R54859
theorem R171449 : Reach 171449 := rs (se 2 (by rfl) ⟨64293, by rfl⟩) R128587
theorem R73223 : Reach 73223 := rs (se 1 (by rfl) ⟨54917, by rfl⟩) R109835
theorem R73259 : Reach 73259 := rs (se 1 (by rfl) ⟨54944, by rfl⟩) R109889
theorem R269891 : Reach 269891 := rs (se 1 (by rfl) ⟨202418, by rfl⟩) R404837
theorem R73289 : Reach 73289 := rs (se 2 (by rfl) ⟨27483, by rfl⟩) R54967
theorem R73403 : Reach 73403 := rs (se 1 (by rfl) ⟨55052, by rfl⟩) R110105
theorem R73463 : Reach 73463 := rs (se 1 (by rfl) ⟨55097, by rfl⟩) R110195
theorem R73487 : Reach 73487 := rs (se 1 (by rfl) ⟨55115, by rfl⟩) R110231
theorem R302885 : Reach 302885 := rs (se 4 (by rfl) ⟨28395, by rfl⟩) R56791
theorem R73529 : Reach 73529 := rs (se 2 (by rfl) ⟨27573, by rfl⟩) R55147
theorem R73607 : Reach 73607 := rs (se 1 (by rfl) ⟨55205, by rfl⟩) R110411
theorem R73643 : Reach 73643 := rs (se 1 (by rfl) ⟨55232, by rfl⟩) R110465
theorem R73673 : Reach 73673 := rs (se 2 (by rfl) ⟨27627, by rfl⟩) R55255
theorem R172043 : Reach 172043 := rs (se 1 (by rfl) ⟨129032, by rfl⟩) R258065
theorem R73787 : Reach 73787 := rs (se 1 (by rfl) ⟨55340, by rfl⟩) R110681
theorem R73847 : Reach 73847 := rs (se 1 (by rfl) ⟨55385, by rfl⟩) R110771
theorem R172151 : Reach 172151 := rs (se 1 (by rfl) ⟨129113, by rfl⟩) R258227
theorem R106631 : Reach 106631 := rs (se 1 (by rfl) ⟨79973, by rfl⟩) R159947
theorem R73871 : Reach 73871 := rs (se 1 (by rfl) ⟨55403, by rfl⟩) R110807
theorem R73913 : Reach 73913 := rs (se 2 (by rfl) ⟨27717, by rfl⟩) R55435
theorem R205001 : Reach 205001 := rs (se 2 (by rfl) ⟨76875, by rfl⟩) R153751
theorem R73991 : Reach 73991 := rs (se 1 (by rfl) ⟨55493, by rfl⟩) R110987
theorem R74027 : Reach 74027 := rs (se 1 (by rfl) ⟨55520, by rfl⟩) R111041
theorem R106811 : Reach 106811 := rs (se 1 (by rfl) ⟨80108, by rfl⟩) R160217
theorem R74057 : Reach 74057 := rs (se 2 (by rfl) ⟨27771, by rfl⟩) R55543
theorem R106937 : Reach 106937 := rs (se 2 (by rfl) ⟨40101, by rfl⟩) R80203
theorem R74171 : Reach 74171 := rs (se 1 (by rfl) ⟨55628, by rfl⟩) R111257
theorem R74231 : Reach 74231 := rs (se 1 (by rfl) ⟨55673, by rfl⟩) R111347
theorem R74255 : Reach 74255 := rs (se 1 (by rfl) ⟨55691, by rfl⟩) R111383
theorem R74297 : Reach 74297 := rs (se 2 (by rfl) ⟨27861, by rfl⟩) R55723
theorem R205373 : Reach 205373 := rs (se 3 (by rfl) ⟨38507, by rfl⟩) R77015
theorem R74375 : Reach 74375 := rs (se 1 (by rfl) ⟨55781, by rfl⟩) R111563
theorem R74411 : Reach 74411 := rs (se 1 (by rfl) ⟨55808, by rfl⟩) R111617
theorem R74441 : Reach 74441 := rs (se 2 (by rfl) ⟨27915, by rfl⟩) R55831
theorem R402149 : Reach 402149 := rs (se 4 (by rfl) ⟨37701, by rfl⟩) R75403
theorem R107279 : Reach 107279 := rs (se 1 (by rfl) ⟨80459, by rfl⟩) R160919
theorem R533263 : Reach 533263 := rs (se 1 (by rfl) ⟨399947, by rfl⟩) R799895
theorem R107297 : Reach 107297 := rs (se 2 (by rfl) ⟨40236, by rfl⟩) R80473
theorem R74555 : Reach 74555 := rs (se 1 (by rfl) ⟨55916, by rfl⟩) R111833
theorem R74615 : Reach 74615 := rs (se 1 (by rfl) ⟨55961, by rfl⟩) R111923
theorem R205715 : Reach 205715 := rs (se 1 (by rfl) ⟨154286, by rfl⟩) R308573
theorem R74681 : Reach 74681 := rs (se 2 (by rfl) ⟨28005, by rfl⟩) R56011
theorem R74767 : Reach 74767 := rs (se 1 (by rfl) ⟨56075, by rfl⟩) R112151
theorem R74795 : Reach 74795 := rs (se 1 (by rfl) ⟨56096, by rfl⟩) R112193
theorem R107639 : Reach 107639 := rs (se 1 (by rfl) ⟨80729, by rfl⟩) R161459
theorem R1615085 : Reach 1615085 := rs (se 3 (by rfl) ⟨302828, by rfl⟩) R605657
theorem R75023 : Reach 75023 := rs (se 1 (by rfl) ⟨56267, by rfl⟩) R112535
theorem R107819 : Reach 107819 := rs (se 1 (by rfl) ⟨80864, by rfl⟩) R161729
theorem R173447 : Reach 173447 := rs (se 1 (by rfl) ⟨130085, by rfl⟩) R260171
theorem R75143 : Reach 75143 := rs (se 1 (by rfl) ⟨56357, by rfl⟩) R112715
theorem R75209 : Reach 75209 := rs (se 2 (by rfl) ⟨28203, by rfl⟩) R56407
theorem R75323 : Reach 75323 := rs (se 1 (by rfl) ⟨56492, by rfl⟩) R112985
theorem R75383 : Reach 75383 := rs (se 1 (by rfl) ⟨56537, by rfl⟩) R113075
theorem R108179 : Reach 108179 := rs (se 1 (by rfl) ⟨81134, by rfl⟩) R162269
theorem R75449 : Reach 75449 := rs (se 2 (by rfl) ⟨28293, by rfl⟩) R56587
theorem R108233 : Reach 108233 := rs (se 2 (by rfl) ⟨40587, by rfl⟩) R81175
theorem R239375 : Reach 239375 := rs (se 1 (by rfl) ⟨179531, by rfl⟩) R359063
theorem R75563 : Reach 75563 := rs (se 1 (by rfl) ⟨56672, by rfl⟩) R113345
theorem R206651 : Reach 206651 := rs (se 1 (by rfl) ⟨154988, by rfl⟩) R309977
theorem R304985 : Reach 304985 := rs (se 2 (by rfl) ⟨114369, by rfl⟩) R228739
theorem R272281 : Reach 272281 := rs (se 2 (by rfl) ⟨102105, by rfl⟩) R204211
theorem R75791 : Reach 75791 := rs (se 1 (by rfl) ⟨56843, by rfl⟩) R113687
theorem R75911 : Reach 75911 := rs (se 1 (by rfl) ⟨56933, by rfl⟩) R113867
theorem R272585 : Reach 272585 := rs (se 2 (by rfl) ⟨102219, by rfl⟩) R204439
theorem R75977 : Reach 75977 := rs (se 2 (by rfl) ⟨28491, by rfl⟩) R56983
theorem R272641 : Reach 272641 := rs (se 2 (by rfl) ⟨102240, by rfl⟩) R204481
theorem R76091 : Reach 76091 := rs (se 1 (by rfl) ⟨57068, by rfl⟩) R114137
theorem R76151 : Reach 76151 := rs (se 1 (by rfl) ⟨57113, by rfl⟩) R114227
theorem R108935 : Reach 108935 := rs (se 1 (by rfl) ⟨81701, by rfl⟩) R163403
theorem R76217 : Reach 76217 := rs (se 2 (by rfl) ⟨28581, by rfl⟩) R57163
theorem R109001 : Reach 109001 := rs (se 2 (by rfl) ⟨40875, by rfl⟩) R81751
theorem R76331 : Reach 76331 := rs (se 1 (by rfl) ⟨57248, by rfl⟩) R114497
theorem R109115 : Reach 109115 := rs (se 1 (by rfl) ⟨81836, by rfl⟩) R163673
theorem R895607 : Reach 895607 := rs (se 1 (by rfl) ⟨671705, by rfl⟩) R1343411
theorem R109241 : Reach 109241 := rs (se 2 (by rfl) ⟨40965, by rfl⟩) R81931
theorem R76559 : Reach 76559 := rs (se 1 (by rfl) ⟨57419, by rfl⟩) R114839
theorem R76679 : Reach 76679 := rs (se 1 (by rfl) ⟨57509, by rfl⟩) R115019
theorem R240569 : Reach 240569 := rs (se 2 (by rfl) ⟨90213, by rfl⟩) R180427
theorem R142337 : Reach 142337 := rs (se 2 (by rfl) ⟨53376, by rfl⟩) R106753
theorem R109583 : Reach 109583 := rs (se 1 (by rfl) ⟨82187, by rfl⟩) R164375
theorem R109601 : Reach 109601 := rs (se 2 (by rfl) ⟨41100, by rfl⟩) R82201
theorem R109943 : Reach 109943 := rs (se 1 (by rfl) ⟨82457, by rfl⟩) R164915
theorem R142793 : Reach 142793 := rs (se 2 (by rfl) ⟨53547, by rfl⟩) R107095
theorem R404945 : Reach 404945 := rs (se 2 (by rfl) ⟨151854, by rfl⟩) R303709
theorem R110123 : Reach 110123 := rs (se 1 (by rfl) ⟨82592, by rfl⟩) R165185
theorem R208585 : Reach 208585 := rs (se 2 (by rfl) ⟨78219, by rfl⟩) R156439
theorem R208655 : Reach 208655 := rs (se 1 (by rfl) ⟨156491, by rfl⟩) R312983
theorem R143147 : Reach 143147 := rs (se 1 (by rfl) ⟨107360, by rfl⟩) R214721
theorem R274265 : Reach 274265 := rs (se 2 (by rfl) ⟨102849, by rfl⟩) R205699
theorem R110483 : Reach 110483 := rs (se 1 (by rfl) ⟨82862, by rfl⟩) R165725
theorem R77753 : Reach 77753 := rs (se 2 (by rfl) ⟨29157, by rfl⟩) R58315
theorem R110537 : Reach 110537 := rs (se 2 (by rfl) ⟨41451, by rfl⟩) R82903
theorem R143545 : Reach 143545 := rs (se 2 (by rfl) ⟨53829, by rfl⟩) R107659
theorem R241865 : Reach 241865 := rs (se 2 (by rfl) ⟨90699, by rfl⟩) R181399
theorem R536977 : Reach 536977 := rs (se 2 (by rfl) ⟨201366, by rfl⟩) R402733
theorem R111239 : Reach 111239 := rs (se 1 (by rfl) ⟨83429, by rfl⟩) R166859
theorem R111419 : Reach 111419 := rs (se 1 (by rfl) ⟨83564, by rfl⟩) R167129
theorem R78727 : Reach 78727 := rs (se 1 (by rfl) ⟨59045, by rfl⟩) R118091
theorem R111545 : Reach 111545 := rs (se 2 (by rfl) ⟨41829, by rfl⟩) R83659
theorem R78983 : Reach 78983 := rs (se 1 (by rfl) ⟨59237, by rfl⟩) R118475
theorem R111887 : Reach 111887 := rs (se 1 (by rfl) ⟨83915, by rfl⟩) R167831
theorem R111905 : Reach 111905 := rs (se 2 (by rfl) ⟨41964, by rfl⟩) R83929
theorem R111959 : Reach 111959 := rs (se 1 (by rfl) ⟨83969, by rfl⟩) R167939
theorem R538001 : Reach 538001 := rs (se 2 (by rfl) ⟨201750, by rfl⟩) R403501
theorem R144787 : Reach 144787 := rs (se 1 (by rfl) ⟨108590, by rfl⟩) R217181
theorem R1291697 : Reach 1291697 := rs (se 2 (by rfl) ⟨484386, by rfl⟩) R968773
theorem R112139 : Reach 112139 := rs (se 1 (by rfl) ⟨84104, by rfl⟩) R168209
theorem R112247 : Reach 112247 := rs (se 1 (by rfl) ⟨84185, by rfl⟩) R168371
theorem R112313 : Reach 112313 := rs (se 2 (by rfl) ⟨42117, by rfl⟩) R84235
theorem R112427 : Reach 112427 := rs (se 1 (by rfl) ⟨84320, by rfl⟩) R168641
theorem R112499 : Reach 112499 := rs (se 1 (by rfl) ⟨84374, by rfl⟩) R168749
theorem R79751 : Reach 79751 := rs (se 1 (by rfl) ⟨59813, by rfl⟩) R119627
theorem R47119 : Reach 47119 := rs (se 1 (by rfl) ⟨35339, by rfl⟩) R70679
theorem R47163 : Reach 47163 := rs (se 1 (by rfl) ⟨35372, by rfl⟩) R70745
theorem R211031 : Reach 211031 := rs (se 1 (by rfl) ⟨158273, by rfl⟩) R316547
theorem R47239 : Reach 47239 := rs (se 1 (by rfl) ⟨35429, by rfl⟩) R70859
theorem R47247 : Reach 47247 := rs (se 1 (by rfl) ⟨35435, by rfl⟩) R70871
theorem R112787 : Reach 112787 := rs (se 1 (by rfl) ⟨84590, by rfl⟩) R169181
theorem R47291 : Reach 47291 := rs (se 1 (by rfl) ⟨35468, by rfl⟩) R70937
theorem R112841 : Reach 112841 := rs (se 2 (by rfl) ⟨42315, by rfl⟩) R84631
theorem R47367 : Reach 47367 := rs (se 1 (by rfl) ⟨35525, by rfl⟩) R71051
theorem R145675 : Reach 145675 := rs (se 1 (by rfl) ⟨109256, by rfl⟩) R218513
theorem R47375 : Reach 47375 := rs (se 1 (by rfl) ⟨35531, by rfl⟩) R71063
theorem R47419 : Reach 47419 := rs (se 1 (by rfl) ⟨35564, by rfl⟩) R71129
theorem R47495 : Reach 47495 := rs (se 1 (by rfl) ⟨35621, by rfl⟩) R71243
theorem R47503 : Reach 47503 := rs (se 1 (by rfl) ⟨35627, by rfl⟩) R71255
theorem R47547 : Reach 47547 := rs (se 1 (by rfl) ⟨35660, by rfl⟩) R71321
theorem R47623 : Reach 47623 := rs (se 1 (by rfl) ⟨35717, by rfl⟩) R71435
theorem R47631 : Reach 47631 := rs (se 1 (by rfl) ⟨35723, by rfl⟩) R71447
theorem R80399 : Reach 80399 := rs (se 1 (by rfl) ⟨60299, by rfl⟩) R120599
theorem R47675 : Reach 47675 := rs (se 1 (by rfl) ⟨35756, by rfl⟩) R71513
theorem R47751 : Reach 47751 := rs (se 1 (by rfl) ⟨35813, by rfl⟩) R71627
theorem R47759 : Reach 47759 := rs (se 1 (by rfl) ⟨35819, by rfl⟩) R71639
theorem R47803 : Reach 47803 := rs (se 1 (by rfl) ⟨35852, by rfl⟩) R71705
theorem R47879 : Reach 47879 := rs (se 1 (by rfl) ⟨35909, by rfl⟩) R71819
theorem R47887 : Reach 47887 := rs (se 1 (by rfl) ⟨35915, by rfl⟩) R71831
theorem R47931 : Reach 47931 := rs (se 1 (by rfl) ⟨35948, by rfl⟩) R71897
theorem R48007 : Reach 48007 := rs (se 1 (by rfl) ⟨36005, by rfl⟩) R72011
theorem R113543 : Reach 113543 := rs (se 1 (by rfl) ⟨85157, by rfl⟩) R170315
theorem R48015 : Reach 48015 := rs (se 1 (by rfl) ⟨36011, by rfl⟩) R72023
theorem R113561 : Reach 113561 := rs (se 2 (by rfl) ⟨42585, by rfl⟩) R85171
theorem R48059 : Reach 48059 := rs (se 1 (by rfl) ⟨36044, by rfl⟩) R72089
theorem R48135 : Reach 48135 := rs (se 1 (by rfl) ⟨36101, by rfl⟩) R72203
theorem R48143 : Reach 48143 := rs (se 1 (by rfl) ⟨36107, by rfl⟩) R72215
theorem R113707 : Reach 113707 := rs (se 1 (by rfl) ⟨85280, by rfl⟩) R170561
theorem R179243 : Reach 179243 := rs (se 1 (by rfl) ⟨134432, by rfl⟩) R268865
theorem R80939 : Reach 80939 := rs (se 1 (by rfl) ⟨60704, by rfl⟩) R121409
theorem R48187 : Reach 48187 := rs (se 1 (by rfl) ⟨36140, by rfl⟩) R72281
theorem R113723 : Reach 113723 := rs (se 1 (by rfl) ⟨85292, by rfl⟩) R170585
theorem R48263 : Reach 48263 := rs (se 1 (by rfl) ⟨36197, by rfl⟩) R72395
theorem R48271 : Reach 48271 := rs (se 1 (by rfl) ⟨36203, by rfl⟩) R72407
theorem R113849 : Reach 113849 := rs (se 2 (by rfl) ⟨42693, by rfl⟩) R85387
theorem R48315 : Reach 48315 := rs (se 1 (by rfl) ⟨36236, by rfl⟩) R72473
theorem R113921 : Reach 113921 := rs (se 2 (by rfl) ⟨42720, by rfl⟩) R85441
theorem R48391 : Reach 48391 := rs (se 1 (by rfl) ⟨36293, by rfl⟩) R72587
theorem R48399 : Reach 48399 := rs (se 1 (by rfl) ⟨36299, by rfl⟩) R72599
theorem R81167 : Reach 81167 := rs (se 1 (by rfl) ⟨60875, by rfl⟩) R121751
theorem R867617 : Reach 867617 := rs (se 2 (by rfl) ⟨325356, by rfl⟩) R650713
theorem R48443 : Reach 48443 := rs (se 1 (by rfl) ⟨36332, by rfl⟩) R72665
theorem R48519 : Reach 48519 := rs (se 1 (by rfl) ⟨36389, by rfl⟩) R72779
theorem R48527 : Reach 48527 := rs (se 1 (by rfl) ⟨36395, by rfl⟩) R72791
theorem R310675 : Reach 310675 := rs (se 1 (by rfl) ⟨233006, by rfl⟩) R466013
theorem R81337 : Reach 81337 := rs (se 2 (by rfl) ⟨30501, by rfl⟩) R61003
theorem R48571 : Reach 48571 := rs (se 1 (by rfl) ⟨36428, by rfl⟩) R72857
theorem R245213 : Reach 245213 := rs (se 3 (by rfl) ⟨45977, by rfl⟩) R91955
theorem R48647 : Reach 48647 := rs (se 1 (by rfl) ⟨36485, by rfl⟩) R72971
theorem R48655 : Reach 48655 := rs (se 1 (by rfl) ⟨36491, by rfl⟩) R72983
theorem R114191 : Reach 114191 := rs (se 1 (by rfl) ⟨85643, by rfl⟩) R171287
theorem R114209 : Reach 114209 := rs (se 2 (by rfl) ⟨42828, by rfl⟩) R85657
theorem R48699 : Reach 48699 := rs (se 1 (by rfl) ⟨36524, by rfl⟩) R73049
theorem R572993 : Reach 572993 := rs (se 2 (by rfl) ⟨214872, by rfl⟩) R429745
theorem R114263 : Reach 114263 := rs (se 1 (by rfl) ⟨85697, by rfl⟩) R171395
theorem R48775 : Reach 48775 := rs (se 1 (by rfl) ⟨36581, by rfl⟩) R73163
theorem R48783 : Reach 48783 := rs (se 1 (by rfl) ⟨36587, by rfl⟩) R73175
theorem R48827 : Reach 48827 := rs (se 1 (by rfl) ⟨36620, by rfl⟩) R73241
theorem R48903 : Reach 48903 := rs (se 1 (by rfl) ⟨36677, by rfl⟩) R73355
theorem R114443 : Reach 114443 := rs (se 1 (by rfl) ⟨85832, by rfl⟩) R171665
theorem R48911 : Reach 48911 := rs (se 1 (by rfl) ⟨36683, by rfl⟩) R73367
theorem R48955 : Reach 48955 := rs (se 1 (by rfl) ⟨36716, by rfl⟩) R73433
theorem R278387 : Reach 278387 := rs (se 1 (by rfl) ⟨208790, by rfl⟩) R417581
theorem R114551 : Reach 114551 := rs (se 1 (by rfl) ⟨85913, by rfl⟩) R171827
theorem R49031 : Reach 49031 := rs (se 1 (by rfl) ⟨36773, by rfl⟩) R73547
theorem R49039 : Reach 49039 := rs (se 1 (by rfl) ⟨36779, by rfl⟩) R73559
theorem R638873 : Reach 638873 := rs (se 2 (by rfl) ⟨239577, by rfl⟩) R479155
theorem R769945 : Reach 769945 := rs (se 2 (by rfl) ⟨288729, by rfl⟩) R577459
theorem R49083 : Reach 49083 := rs (se 1 (by rfl) ⟨36812, by rfl⟩) R73625
theorem R49159 : Reach 49159 := rs (se 1 (by rfl) ⟨36869, by rfl⟩) R73739
theorem R49167 : Reach 49167 := rs (se 1 (by rfl) ⟨36875, by rfl⟩) R73751
theorem R114731 : Reach 114731 := rs (se 1 (by rfl) ⟨86048, by rfl⟩) R172097
theorem R49211 : Reach 49211 := rs (se 1 (by rfl) ⟨36908, by rfl⟩) R73817
theorem R114803 : Reach 114803 := rs (se 1 (by rfl) ⟨86102, by rfl⟩) R172205
theorem R82039 : Reach 82039 := rs (se 1 (by rfl) ⟨61529, by rfl⟩) R123059
theorem R49287 : Reach 49287 := rs (se 1 (by rfl) ⟨36965, by rfl⟩) R73931
theorem R49295 : Reach 49295 := rs (se 1 (by rfl) ⟨36971, by rfl⟩) R73943
theorem R49339 : Reach 49339 := rs (se 1 (by rfl) ⟨37004, by rfl⟩) R74009
theorem R540917 : Reach 540917 := rs (se 5 (by rfl) ⟨25355, by rfl⟩) R50711
theorem R49415 : Reach 49415 := rs (se 1 (by rfl) ⟨37061, by rfl⟩) R74123
theorem R49423 : Reach 49423 := rs (se 1 (by rfl) ⟨37067, by rfl⟩) R74135
theorem R82235 : Reach 82235 := rs (se 1 (by rfl) ⟨61676, by rfl⟩) R123353
theorem R49467 : Reach 49467 := rs (se 1 (by rfl) ⟨37100, by rfl⟩) R74201
theorem R49543 : Reach 49543 := rs (se 1 (by rfl) ⟨37157, by rfl⟩) R74315
theorem R49551 : Reach 49551 := rs (se 1 (by rfl) ⟨37163, by rfl⟩) R74327
theorem R147865 : Reach 147865 := rs (se 2 (by rfl) ⟨55449, by rfl⟩) R110899
theorem R49595 : Reach 49595 := rs (se 1 (by rfl) ⟨37196, by rfl⟩) R74393
theorem R49671 : Reach 49671 := rs (se 1 (by rfl) ⟨37253, by rfl⟩) R74507
theorem R49679 : Reach 49679 := rs (se 1 (by rfl) ⟨37259, by rfl⟩) R74519
theorem R49723 : Reach 49723 := rs (se 1 (by rfl) ⟨37292, by rfl⟩) R74585
theorem R49799 : Reach 49799 := rs (se 1 (by rfl) ⟨37349, by rfl⟩) R74699
theorem R49807 : Reach 49807 := rs (se 1 (by rfl) ⟨37355, by rfl⟩) R74711
theorem R49851 : Reach 49851 := rs (se 1 (by rfl) ⟨37388, by rfl⟩) R74777
theorem R82633 : Reach 82633 := rs (se 2 (by rfl) ⟨30987, by rfl⟩) R61975
theorem R49927 : Reach 49927 := rs (se 1 (by rfl) ⟨37445, by rfl⟩) R74891
theorem R49935 : Reach 49935 := rs (se 1 (by rfl) ⟨37451, by rfl⟩) R74903
theorem R49979 : Reach 49979 := rs (se 1 (by rfl) ⟨37484, by rfl⟩) R74969
theorem R50055 : Reach 50055 := rs (se 1 (by rfl) ⟨37541, by rfl⟩) R75083
theorem R50063 : Reach 50063 := rs (se 1 (by rfl) ⟨37547, by rfl⟩) R75095
theorem R82873 : Reach 82873 := rs (se 2 (by rfl) ⟨31077, by rfl⟩) R62155
theorem R50107 : Reach 50107 := rs (se 1 (by rfl) ⟨37580, by rfl⟩) R75161
theorem R50183 : Reach 50183 := rs (se 1 (by rfl) ⟨37637, by rfl⟩) R75275
theorem R50191 : Reach 50191 := rs (se 1 (by rfl) ⟨37643, by rfl⟩) R75287
theorem R50235 : Reach 50235 := rs (se 1 (by rfl) ⟨37676, by rfl⟩) R75353
theorem R640061 : Reach 640061 := rs (se 3 (by rfl) ⟨120011, by rfl⟩) R240023
theorem R2114693 : Reach 2114693 := rs (se 4 (by rfl) ⟨198252, by rfl⟩) R396505
theorem R50311 : Reach 50311 := rs (se 1 (by rfl) ⟨37733, by rfl⟩) R75467
theorem R50319 : Reach 50319 := rs (se 1 (by rfl) ⟨37739, by rfl⟩) R75479
theorem R50363 : Reach 50363 := rs (se 1 (by rfl) ⟨37772, by rfl⟩) R75545
theorem R50439 : Reach 50439 := rs (se 1 (by rfl) ⟨37829, by rfl⟩) R75659
theorem R50447 : Reach 50447 := rs (se 1 (by rfl) ⟨37835, by rfl⟩) R75671
theorem R279845 : Reach 279845 := rs (se 4 (by rfl) ⟨26235, by rfl⟩) R52471
theorem R50491 : Reach 50491 := rs (se 1 (by rfl) ⟨37868, by rfl⟩) R75737
theorem R83335 : Reach 83335 := rs (se 1 (by rfl) ⟨62501, by rfl⟩) R125003
theorem R50567 : Reach 50567 := rs (se 1 (by rfl) ⟨37925, by rfl⟩) R75851
theorem R50575 : Reach 50575 := rs (se 1 (by rfl) ⟨37931, by rfl⟩) R75863
theorem R50619 : Reach 50619 := rs (se 1 (by rfl) ⟨37964, by rfl⟩) R75929
theorem R50695 : Reach 50695 := rs (se 1 (by rfl) ⟨38021, by rfl⟩) R76043
theorem R50703 : Reach 50703 := rs (se 1 (by rfl) ⟨38027, by rfl⟩) R76055
theorem R50747 : Reach 50747 := rs (se 1 (by rfl) ⟨38060, by rfl⟩) R76121
theorem R214595 : Reach 214595 := rs (se 1 (by rfl) ⟨160946, by rfl⟩) R321893
theorem R50823 : Reach 50823 := rs (se 1 (by rfl) ⟨38117, by rfl⟩) R76235
theorem R50831 : Reach 50831 := rs (se 1 (by rfl) ⟨38123, by rfl⟩) R76247
theorem R50875 : Reach 50875 := rs (se 1 (by rfl) ⟨38156, by rfl⟩) R76313
theorem R50951 : Reach 50951 := rs (se 1 (by rfl) ⟨38213, by rfl⟩) R76427
theorem R50959 : Reach 50959 := rs (se 1 (by rfl) ⟨38219, by rfl⟩) R76439
theorem R542513 : Reach 542513 := rs (se 2 (by rfl) ⟨203442, by rfl⟩) R406885
theorem R51003 : Reach 51003 := rs (se 1 (by rfl) ⟨38252, by rfl⟩) R76505
theorem R51079 : Reach 51079 := rs (se 1 (by rfl) ⟨38309, by rfl⟩) R76619
theorem R247697 : Reach 247697 := rs (se 2 (by rfl) ⟨92886, by rfl⟩) R185773
theorem R51087 : Reach 51087 := rs (se 1 (by rfl) ⟨38315, by rfl⟩) R76631
theorem R280529 : Reach 280529 := rs (se 2 (by rfl) ⟨105198, by rfl⟩) R210397
theorem R83983 : Reach 83983 := rs (se 1 (by rfl) ⟨62987, by rfl⟩) R125975
theorem R51463 : Reach 51463 := rs (se 1 (by rfl) ⟨38597, by rfl⟩) R77195
theorem R280847 : Reach 280847 := rs (se 1 (by rfl) ⟨210635, by rfl⟩) R421271
theorem R182675 : Reach 182675 := rs (se 1 (by rfl) ⟨137006, by rfl⟩) R274013
theorem R84523 : Reach 84523 := rs (se 1 (by rfl) ⟨63392, by rfl⟩) R126785
theorem R51847 : Reach 51847 := rs (se 1 (by rfl) ⟨38885, by rfl⟩) R77771
theorem R84665 : Reach 84665 := rs (se 2 (by rfl) ⟨31749, by rfl⟩) R63499
theorem R52283 : Reach 52283 := rs (se 1 (by rfl) ⟨39212, by rfl⟩) R78425
theorem R805949 : Reach 805949 := rs (se 3 (by rfl) ⟨151115, by rfl⟩) R302231
theorem R85367 : Reach 85367 := rs (se 1 (by rfl) ⟨64025, by rfl⟩) R128051
theorem R413113 : Reach 413113 := rs (se 2 (by rfl) ⟨154917, by rfl⟩) R309835
theorem R118273 : Reach 118273 := rs (se 2 (by rfl) ⟨44352, by rfl⟩) R88705
theorem R183869 : Reach 183869 := rs (se 3 (by rfl) ⟨34475, by rfl⟩) R68951
theorem R282305 : Reach 282305 := rs (se 2 (by rfl) ⟨105864, by rfl⟩) R211729
theorem R249601 : Reach 249601 := rs (se 2 (by rfl) ⟨93600, by rfl⟩) R187201
theorem R85819 : Reach 85819 := rs (se 1 (by rfl) ⟨64364, by rfl⟩) R128729
theorem R118675 : Reach 118675 := rs (se 1 (by rfl) ⟨89006, by rfl⟩) R178013
theorem R85907 : Reach 85907 := rs (se 1 (by rfl) ⟨64430, by rfl⟩) R128861
theorem R511895 : Reach 511895 := rs (se 1 (by rfl) ⟨383921, by rfl⟩) R767843
theorem R348067 : Reach 348067 := rs (se 1 (by rfl) ⟨261050, by rfl⟩) R522101
theorem R85961 : Reach 85961 := rs (se 2 (by rfl) ⟨32235, by rfl⟩) R64471
theorem R249803 : Reach 249803 := rs (se 1 (by rfl) ⟨187352, by rfl⟩) R374705
theorem R53383 : Reach 53383 := rs (se 1 (by rfl) ⟨40037, by rfl⟩) R80075
theorem R250127 : Reach 250127 := rs (se 1 (by rfl) ⟨187595, by rfl⟩) R375191
theorem R53563 : Reach 53563 := rs (se 1 (by rfl) ⟨40172, by rfl⟩) R80345
theorem R217403 : Reach 217403 := rs (se 1 (by rfl) ⟨163052, by rfl⟩) R326105
theorem R479773 : Reach 479773 := rs (se 3 (by rfl) ⟨89957, by rfl⟩) R179915
theorem R54031 : Reach 54031 := rs (se 1 (by rfl) ⟨40523, by rfl⟩) R81047
theorem R185273 : Reach 185273 := rs (se 2 (by rfl) ⟨69477, by rfl⟩) R138955
theorem R119819 : Reach 119819 := rs (se 1 (by rfl) ⟨89864, by rfl⟩) R179729
theorem R87241 : Reach 87241 := rs (se 2 (by rfl) ⟨32715, by rfl⟩) R65431
theorem R54535 : Reach 54535 := rs (se 1 (by rfl) ⟨40901, by rfl⟩) R81803
theorem R54715 : Reach 54715 := rs (se 1 (by rfl) ⟨41036, by rfl⟩) R82073
theorem R120467 : Reach 120467 := rs (se 1 (by rfl) ⟨90350, by rfl⟩) R180701
theorem R251585 : Reach 251585 := rs (se 2 (by rfl) ⟨94344, by rfl⟩) R188689
theorem R382657 : Reach 382657 := rs (se 2 (by rfl) ⟨143496, by rfl⟩) R286993
theorem R120521 : Reach 120521 := rs (se 2 (by rfl) ⟨45195, by rfl⟩) R90391
theorem R907057 : Reach 907057 := rs (se 2 (by rfl) ⟨340146, by rfl⟩) R680293
theorem R55175 : Reach 55175 := rs (se 1 (by rfl) ⟨41381, by rfl⟩) R82763
theorem R55183 : Reach 55183 := rs (se 1 (by rfl) ⟨41387, by rfl⟩) R82775
theorem R186259 : Reach 186259 := rs (se 1 (by rfl) ⟨139694, by rfl⟩) R279389
theorem R120761 : Reach 120761 := rs (se 2 (by rfl) ⟨45285, by rfl⟩) R90571
theorem R120919 : Reach 120919 := rs (se 1 (by rfl) ⟨90689, by rfl⟩) R181379
theorem R88265 : Reach 88265 := rs (se 2 (by rfl) ⟨33099, by rfl⟩) R66199
theorem R55687 : Reach 55687 := rs (se 1 (by rfl) ⟨41765, by rfl⟩) R83531
theorem R383453 : Reach 383453 := rs (se 3 (by rfl) ⟨71897, by rfl⟩) R143795
theorem R55867 : Reach 55867 := rs (se 1 (by rfl) ⟨41900, by rfl⟩) R83801
theorem R121459 : Reach 121459 := rs (se 1 (by rfl) ⟨91094, by rfl⟩) R182189
theorem R121601 : Reach 121601 := rs (se 2 (by rfl) ⟨45600, by rfl⟩) R91201
theorem R252881 : Reach 252881 := rs (se 2 (by rfl) ⟨94830, by rfl⟩) R189661
theorem R56335 : Reach 56335 := rs (se 1 (by rfl) ⟨42251, by rfl⟩) R84503
theorem R154685 : Reach 154685 := rs (se 3 (by rfl) ⟨29003, by rfl⟩) R58007
theorem R122057 : Reach 122057 := rs (se 2 (by rfl) ⟨45771, by rfl⟩) R91543
theorem R56695 : Reach 56695 := rs (se 1 (by rfl) ⟨42521, by rfl⟩) R85043
theorem R613817 : Reach 613817 := rs (se 2 (by rfl) ⟨230181, by rfl⟩) R460363
theorem R56839 : Reach 56839 := rs (se 1 (by rfl) ⟨42629, by rfl⟩) R85259
theorem R122411 : Reach 122411 := rs (se 1 (by rfl) ⟨91808, by rfl⟩) R183617
theorem R56875 : Reach 56875 := rs (se 1 (by rfl) ⟨42656, by rfl⟩) R85313
theorem R187991 : Reach 187991 := rs (se 1 (by rfl) ⟨140993, by rfl⟩) R281987
theorem R89785 : Reach 89785 := rs (se 2 (by rfl) ⟨33669, by rfl⟩) R67339
theorem R57019 : Reach 57019 := rs (se 1 (by rfl) ⟨42764, by rfl⟩) R85529
theorem R89915 : Reach 89915 := rs (se 1 (by rfl) ⟨67436, by rfl⟩) R134873
theorem R122809 : Reach 122809 := rs (se 2 (by rfl) ⟨46053, by rfl⟩) R92107
theorem R188477 : Reach 188477 := rs (se 3 (by rfl) ⟨35339, by rfl⟩) R70679
theorem R90247 : Reach 90247 := rs (se 1 (by rfl) ⟨67685, by rfl⟩) R135371
theorem R57487 : Reach 57487 := rs (se 1 (by rfl) ⟨43115, by rfl⟩) R86231
theorem R57515 : Reach 57515 := rs (se 1 (by rfl) ⟨43136, by rfl⟩) R86273
theorem R549179 : Reach 549179 := rs (se 1 (by rfl) ⟨411884, by rfl⟩) R823769
theorem R90487 : Reach 90487 := rs (se 1 (by rfl) ⟨67865, by rfl⟩) R135731
theorem R451001 : Reach 451001 := rs (se 2 (by rfl) ⟨169125, by rfl⟩) R338251
theorem R516611 : Reach 516611 := rs (se 1 (by rfl) ⟨387458, by rfl⟩) R774917
theorem R123403 : Reach 123403 := rs (se 1 (by rfl) ⟨92552, by rfl⟩) R185105
theorem R123545 : Reach 123545 := rs (se 2 (by rfl) ⟨46329, by rfl⟩) R92659
theorem R123707 : Reach 123707 := rs (se 1 (by rfl) ⟨92780, by rfl⟩) R185561
theorem R451403 : Reach 451403 := rs (se 1 (by rfl) ⟨338552, by rfl⟩) R677105
theorem R254987 : Reach 254987 := rs (se 1 (by rfl) ⟨191240, by rfl⟩) R382481
theorem R124019 : Reach 124019 := rs (se 1 (by rfl) ⟨93014, by rfl⟩) R186029
theorem R124051 : Reach 124051 := rs (se 1 (by rfl) ⟨93038, by rfl⟩) R186077
theorem R255149 : Reach 255149 := rs (se 3 (by rfl) ⟨47840, by rfl⟩) R95681
theorem R124105 : Reach 124105 := rs (se 2 (by rfl) ⟨46539, by rfl⟩) R93079
theorem R124193 : Reach 124193 := rs (se 2 (by rfl) ⟨46572, by rfl⟩) R93145
theorem R419357 : Reach 419357 := rs (se 3 (by rfl) ⟨78629, by rfl⟩) R157259
theorem R681797 : Reach 681797 := rs (se 4 (by rfl) ⟨63918, by rfl⟩) R127837
theorem R157555 : Reach 157555 := rs (se 1 (by rfl) ⟨118166, by rfl⟩) R236333
theorem R2189429 : Reach 2189429 := rs (se 5 (by rfl) ⟨102629, by rfl⟩) R205259
theorem R92279 : Reach 92279 := rs (se 1 (by rfl) ⟨69209, by rfl⟩) R138419
theorem R125129 : Reach 125129 := rs (se 2 (by rfl) ⟨46923, by rfl⟩) R93847
theorem R125185 : Reach 125185 := rs (se 2 (by rfl) ⟨46944, by rfl⟩) R93889
theorem R92431 : Reach 92431 := rs (se 1 (by rfl) ⟨69323, by rfl⟩) R138647
theorem R59707 : Reach 59707 := rs (se 1 (by rfl) ⟨44780, by rfl⟩) R89561
theorem R551261 : Reach 551261 := rs (se 3 (by rfl) ⟨103361, by rfl⟩) R206723
theorem R92819 : Reach 92819 := rs (se 1 (by rfl) ⟨69614, by rfl⟩) R139229
theorem R256769 : Reach 256769 := rs (se 2 (by rfl) ⟨96288, by rfl⟩) R192577
theorem R125725 : Reach 125725 := rs (se 3 (by rfl) ⟨23573, by rfl⟩) R47147
theorem R60203 : Reach 60203 := rs (se 1 (by rfl) ⟨45152, by rfl⟩) R90305
theorem R289595 : Reach 289595 := rs (se 1 (by rfl) ⟨217196, by rfl⟩) R434393
theorem R518987 : Reach 518987 := rs (se 1 (by rfl) ⟨389240, by rfl⟩) R778481
theorem R125783 : Reach 125783 := rs (se 1 (by rfl) ⟨94337, by rfl⟩) R188675
theorem R486233 : Reach 486233 := rs (se 2 (by rfl) ⟨182337, by rfl⟩) R364675
theorem R125995 : Reach 125995 := rs (se 1 (by rfl) ⟨94496, by rfl⟩) R188993
theorem R420997 : Reach 420997 := rs (se 4 (by rfl) ⟨39468, by rfl⟩) R78937
theorem R126137 : Reach 126137 := rs (se 2 (by rfl) ⟨47301, by rfl⟩) R94603
theorem R60679 : Reach 60679 := rs (se 1 (by rfl) ⟨45509, by rfl⟩) R91019
theorem R126269 : Reach 126269 := rs (se 3 (by rfl) ⟨23675, by rfl⟩) R47351
theorem R1371491 : Reach 1371491 := rs (se 1 (by rfl) ⟨1028618, by rfl⟩) R2057237
theorem R191879 : Reach 191879 := rs (se 1 (by rfl) ⟨143909, by rfl⟩) R287819
theorem R257579 : Reach 257579 := rs (se 1 (by rfl) ⟨193184, by rfl⟩) R386369
theorem R61175 : Reach 61175 := rs (se 1 (by rfl) ⟨45881, by rfl⟩) R91763
theorem R290575 : Reach 290575 := rs (se 1 (by rfl) ⟨217931, by rfl⟩) R435863
theorem R159623 : Reach 159623 := rs (se 1 (by rfl) ⟨119717, by rfl⟩) R239435
theorem R61327 : Reach 61327 := rs (se 1 (by rfl) ⟨45995, by rfl⟩) R91991
theorem R225227 : Reach 225227 := rs (se 1 (by rfl) ⟨168920, by rfl⟩) R337841
theorem R94223 : Reach 94223 := rs (se 1 (by rfl) ⟨70667, by rfl⟩) R141335
theorem R61499 : Reach 61499 := rs (se 1 (by rfl) ⟨46124, by rfl⟩) R92249
theorem R127129 : Reach 127129 := rs (se 2 (by rfl) ⟨47673, by rfl⟩) R95347
theorem R291053 : Reach 291053 := rs (se 3 (by rfl) ⟨54572, by rfl⟩) R109145
theorem R160001 : Reach 160001 := rs (se 2 (by rfl) ⟨60000, by rfl⟩) R120001
theorem R127291 : Reach 127291 := rs (se 1 (by rfl) ⟨95468, by rfl⟩) R190937
theorem R127433 : Reach 127433 := rs (se 2 (by rfl) ⟨47787, by rfl⟩) R95575
theorem R94763 : Reach 94763 := rs (se 1 (by rfl) ⟨71072, by rfl⟩) R142145
theorem R127777 : Reach 127777 := rs (se 2 (by rfl) ⟨47916, by rfl⟩) R95833
theorem R62471 : Reach 62471 := rs (se 1 (by rfl) ⟨46853, by rfl⟩) R93707
theorem R390167 : Reach 390167 := rs (se 1 (by rfl) ⟨292625, by rfl⟩) R585251
theorem R160811 : Reach 160811 := rs (se 1 (by rfl) ⟨120608, by rfl⟩) R241217
theorem R390277 : Reach 390277 := rs (se 4 (by rfl) ⟨36588, by rfl⟩) R73177
theorem R128299 : Reach 128299 := rs (se 1 (by rfl) ⟨96224, by rfl⟩) R192449
theorem R128375 : Reach 128375 := rs (se 1 (by rfl) ⟨96281, by rfl⟩) R192563
theorem R128441 : Reach 128441 := rs (se 2 (by rfl) ⟨48165, by rfl⟩) R96331
theorem R95879 : Reach 95879 := rs (se 1 (by rfl) ⟨71909, by rfl⟩) R143819
theorem R63119 : Reach 63119 := rs (se 1 (by rfl) ⟨47339, by rfl⟩) R94679
theorem R358181 : Reach 358181 := rs (se 4 (by rfl) ⟨33579, by rfl⟩) R67159
theorem R423731 : Reach 423731 := rs (se 1 (by rfl) ⟨317798, by rfl⟩) R635597
theorem R194363 : Reach 194363 := rs (se 1 (by rfl) ⟨145772, by rfl⟩) R291545
theorem R63433 : Reach 63433 := rs (se 2 (by rfl) ⟨23787, by rfl⟩) R47575
theorem R325579 : Reach 325579 := rs (se 1 (by rfl) ⟨244184, by rfl⟩) R488369
theorem R227357 : Reach 227357 := rs (se 3 (by rfl) ⟨42629, by rfl⟩) R85259
theorem R129053 : Reach 129053 := rs (se 3 (by rfl) ⟨24197, by rfl⟩) R48395
theorem R96403 : Reach 96403 := rs (se 1 (by rfl) ⟨72302, by rfl⟩) R144605
theorem R391405 : Reach 391405 := rs (se 3 (by rfl) ⟨73388, by rfl⟩) R146777
theorem R981233 : Reach 981233 := rs (se 2 (by rfl) ⟨367962, by rfl⟩) R735925
theorem R227585 : Reach 227585 := rs (se 2 (by rfl) ⟨85344, by rfl⟩) R170689
theorem R162107 : Reach 162107 := rs (se 1 (by rfl) ⟨121580, by rfl⟩) R243161
theorem R63929 : Reach 63929 := rs (se 2 (by rfl) ⟨23973, by rfl⟩) R47947
theorem R162233 : Reach 162233 := rs (se 2 (by rfl) ⟨60837, by rfl⟩) R121675
theorem R129683 : Reach 129683 := rs (se 1 (by rfl) ⟨97262, by rfl⟩) R194525
theorem R228041 : Reach 228041 := rs (se 2 (by rfl) ⟨85515, by rfl⟩) R171031
theorem R162593 : Reach 162593 := rs (se 2 (by rfl) ⟨60972, by rfl⟩) R121945
theorem R523097 : Reach 523097 := rs (se 2 (by rfl) ⟨196161, by rfl⟩) R392323
theorem R97481 : Reach 97481 := rs (se 2 (by rfl) ⟨36555, by rfl⟩) R73111
theorem R163187 : Reach 163187 := rs (se 1 (by rfl) ⟨122390, by rfl⟩) R244781
theorem R130439 : Reach 130439 := rs (se 1 (by rfl) ⟨97829, by rfl⟩) R195659
theorem R163997 : Reach 163997 := rs (se 3 (by rfl) ⟨30749, by rfl⟩) R61499
theorem R360611 : Reach 360611 := rs (se 1 (by rfl) ⟨270458, by rfl⟩) R540917
theorem R721163 : Reach 721163 := rs (se 1 (by rfl) ⟨540872, by rfl⟩) R1081745
theorem R197153 : Reach 197153 := rs (se 2 (by rfl) ⟨73932, by rfl⟩) R147865
theorem R164537 : Reach 164537 := rs (se 2 (by rfl) ⟨61701, by rfl⟩) R123403
theorem R426707 : Reach 426707 := rs (se 1 (by rfl) ⟨320030, by rfl⟩) R640061
theorem R1409795 : Reach 1409795 := rs (se 1 (by rfl) ⟨1057346, by rfl⟩) R2114693
theorem R590867 : Reach 590867 := rs (se 1 (by rfl) ⟨443150, by rfl⟩) R886301
theorem R361675 : Reach 361675 := rs (se 1 (by rfl) ⟨271256, by rfl⟩) R542513
theorem R165131 : Reach 165131 := rs (se 1 (by rfl) ⟨123848, by rfl⟩) R247697
theorem R99689 : Reach 99689 := rs (se 2 (by rfl) ⟨37383, by rfl⟩) R74767
theorem R132457 : Reach 132457 := rs (se 2 (by rfl) ⟨49671, by rfl⟩) R99343
theorem R165401 : Reach 165401 := rs (se 2 (by rfl) ⟨62025, by rfl⟩) R124051
theorem R165473 : Reach 165473 := rs (se 2 (by rfl) ⟨62052, by rfl⟩) R124105
theorem R263819 : Reach 263819 := rs (se 1 (by rfl) ⟨197864, by rfl⟩) R395729
theorem R395279 : Reach 395279 := rs (se 1 (by rfl) ⟨296459, by rfl⟩) R592919
theorem R363041 : Reach 363041 := rs (se 2 (by rfl) ⟨136140, by rfl⟩) R272281
theorem R166535 : Reach 166535 := rs (se 1 (by rfl) ⟨124901, by rfl⟩) R249803
theorem R166589 : Reach 166589 := rs (se 3 (by rfl) ⟨31235, by rfl⟩) R62471
theorem R166751 : Reach 166751 := rs (se 1 (by rfl) ⟨125063, by rfl⟩) R250127
theorem R166913 : Reach 166913 := rs (se 2 (by rfl) ⟨62592, by rfl⟩) R125185
theorem R363521 : Reach 363521 := rs (se 2 (by rfl) ⟨136320, by rfl⟩) R272641
theorem R68617 : Reach 68617 := rs (se 2 (by rfl) ⟨25731, by rfl⟩) R51463
theorem R68959 : Reach 68959 := rs (se 1 (by rfl) ⟨51719, by rfl⟩) R103439
theorem R134855 : Reach 134855 := rs (se 1 (by rfl) ⟨101141, by rfl⟩) R202283
theorem R167633 : Reach 167633 := rs (se 2 (by rfl) ⟨62862, by rfl⟩) R125725
theorem R167723 : Reach 167723 := rs (se 1 (by rfl) ⟨125792, by rfl⟩) R251585
theorem R167993 : Reach 167993 := rs (se 2 (by rfl) ⟨62997, by rfl⟩) R125995
theorem R561329 : Reach 561329 := rs (se 2 (by rfl) ⟨210498, by rfl⟩) R420997
theorem R168317 : Reach 168317 := rs (se 3 (by rfl) ⟨31559, by rfl⟩) R63119
theorem R299501 : Reach 299501 := rs (se 3 (by rfl) ⟨56156, by rfl⟩) R112313
theorem R168587 : Reach 168587 := rs (se 1 (by rfl) ⟨126440, by rfl⟩) R252881
theorem R103123 : Reach 103123 := rs (se 1 (by rfl) ⟨77342, by rfl⟩) R154685
theorem R332801 : Reach 332801 := rs (se 2 (by rfl) ⟨124800, by rfl⟩) R249601
theorem R201923 : Reach 201923 := rs (se 1 (by rfl) ⟨151442, by rfl⟩) R302885
theorem R464089 : Reach 464089 := rs (se 2 (by rfl) ⟨174033, by rfl⟩) R348067
theorem R71087 : Reach 71087 := rs (se 1 (by rfl) ⟨53315, by rfl⟩) R106631
theorem R136667 : Reach 136667 := rs (se 1 (by rfl) ⟨102500, by rfl⟩) R205001
theorem R71177 : Reach 71177 := rs (se 2 (by rfl) ⟨26691, by rfl⟩) R53383
theorem R169505 : Reach 169505 := rs (se 2 (by rfl) ⟨63564, by rfl⟩) R127129
theorem R71207 : Reach 71207 := rs (se 1 (by rfl) ⟨53405, by rfl⟩) R106811
theorem R366119 : Reach 366119 := rs (se 1 (by rfl) ⟨274589, by rfl⟩) R549179
theorem R71291 : Reach 71291 := rs (se 1 (by rfl) ⟨53468, by rfl⟩) R106937
theorem R300667 : Reach 300667 := rs (se 1 (by rfl) ⟨225500, by rfl⟩) R451001
theorem R71417 : Reach 71417 := rs (se 2 (by rfl) ⟨26781, by rfl⟩) R53563
theorem R169721 : Reach 169721 := rs (se 2 (by rfl) ⟨63645, by rfl⟩) R127291
theorem R71519 : Reach 71519 := rs (se 1 (by rfl) ⟨53639, by rfl⟩) R107279
theorem R71531 : Reach 71531 := rs (se 1 (by rfl) ⟨53648, by rfl⟩) R107297
theorem R300935 : Reach 300935 := rs (se 1 (by rfl) ⟨225701, by rfl⟩) R451403
theorem R137143 : Reach 137143 := rs (se 1 (by rfl) ⟨102857, by rfl⟩) R205715
theorem R169991 : Reach 169991 := rs (se 1 (by rfl) ⟨127493, by rfl⟩) R254987
theorem R71759 : Reach 71759 := rs (se 1 (by rfl) ⟨53819, by rfl⟩) R107639
theorem R170099 : Reach 170099 := rs (se 1 (by rfl) ⟨127574, by rfl⟩) R255149
theorem R71879 : Reach 71879 := rs (se 1 (by rfl) ⟨53909, by rfl⟩) R107819
theorem R72041 : Reach 72041 := rs (se 2 (by rfl) ⟨27015, by rfl⟩) R54031
theorem R170369 : Reach 170369 := rs (se 2 (by rfl) ⟨63888, by rfl⟩) R127777
theorem R72119 : Reach 72119 := rs (se 1 (by rfl) ⟨54089, by rfl⟩) R108179
theorem R72155 : Reach 72155 := rs (se 1 (by rfl) ⟨54116, by rfl⟩) R108233
theorem R170477 : Reach 170477 := rs (se 3 (by rfl) ⟨31964, by rfl⟩) R63929
theorem R104969 : Reach 104969 := rs (se 2 (by rfl) ⟨39363, by rfl⟩) R78727
theorem R203323 : Reach 203323 := rs (se 1 (by rfl) ⟨152492, by rfl⟩) R304985
theorem R367507 : Reach 367507 := rs (se 1 (by rfl) ⟨275630, by rfl⟩) R551261
theorem R72623 : Reach 72623 := rs (se 1 (by rfl) ⟨54467, by rfl⟩) R108935
theorem R72667 : Reach 72667 := rs (se 1 (by rfl) ⟨54500, by rfl⟩) R109001
theorem R72713 : Reach 72713 := rs (se 2 (by rfl) ⟨27267, by rfl⟩) R54535
theorem R72743 : Reach 72743 := rs (se 1 (by rfl) ⟨54557, by rfl⟩) R109115
theorem R171065 : Reach 171065 := rs (se 2 (by rfl) ⟨64149, by rfl⟩) R128299
theorem R597071 : Reach 597071 := rs (se 1 (by rfl) ⟨447803, by rfl⟩) R895607
theorem R72827 : Reach 72827 := rs (se 1 (by rfl) ⟨54620, by rfl⟩) R109241
theorem R171179 : Reach 171179 := rs (se 1 (by rfl) ⟨128384, by rfl⟩) R256769
theorem R72953 : Reach 72953 := rs (se 2 (by rfl) ⟨27357, by rfl⟩) R54715
theorem R73055 : Reach 73055 := rs (se 1 (by rfl) ⟨54791, by rfl⟩) R109583
theorem R138601 : Reach 138601 := rs (se 2 (by rfl) ⟨51975, by rfl⟩) R103951
theorem R73067 : Reach 73067 := rs (se 1 (by rfl) ⟨54800, by rfl⟩) R109601
theorem R73295 : Reach 73295 := rs (se 1 (by rfl) ⟨54971, by rfl⟩) R109943
theorem R269963 : Reach 269963 := rs (se 1 (by rfl) ⟨202472, by rfl⟩) R404945
theorem R73415 : Reach 73415 := rs (se 1 (by rfl) ⟨55061, by rfl⟩) R110123
theorem R171719 : Reach 171719 := rs (se 1 (by rfl) ⟨128789, by rfl⟩) R257579
theorem R139103 : Reach 139103 := rs (se 1 (by rfl) ⟨104327, by rfl⟩) R208655
theorem R73577 : Reach 73577 := rs (se 2 (by rfl) ⟨27591, by rfl⟩) R55183
theorem R106415 : Reach 106415 := rs (se 1 (by rfl) ⟨79811, by rfl⟩) R159623
theorem R73655 : Reach 73655 := rs (se 1 (by rfl) ⟨55241, by rfl⟩) R110483
theorem R434105 : Reach 434105 := rs (se 2 (by rfl) ⟨162789, by rfl⟩) R325579
theorem R73691 : Reach 73691 := rs (se 1 (by rfl) ⟨55268, by rfl⟩) R110537
theorem R139421 : Reach 139421 := rs (se 3 (by rfl) ⟨26141, by rfl⟩) R52283
theorem R106667 : Reach 106667 := rs (se 1 (by rfl) ⟨80000, by rfl⟩) R160001
theorem R74159 : Reach 74159 := rs (se 1 (by rfl) ⟨55619, by rfl⟩) R111239
theorem R74249 : Reach 74249 := rs (se 2 (by rfl) ⟨27843, by rfl⟩) R55687
theorem R74279 : Reach 74279 := rs (se 1 (by rfl) ⟨55709, by rfl⟩) R111419
theorem R74363 : Reach 74363 := rs (se 1 (by rfl) ⟨55772, by rfl⟩) R111545
theorem R107207 : Reach 107207 := rs (se 1 (by rfl) ⟨80405, by rfl⟩) R160811
theorem R74489 : Reach 74489 := rs (se 2 (by rfl) ⟨27933, by rfl⟩) R55867
theorem R140105 : Reach 140105 := rs (se 2 (by rfl) ⟨52539, by rfl⟩) R105079
theorem R74591 : Reach 74591 := rs (se 1 (by rfl) ⟨55943, by rfl⟩) R111887
theorem R74603 : Reach 74603 := rs (se 1 (by rfl) ⟨55952, by rfl⟩) R111905
theorem R74639 : Reach 74639 := rs (se 1 (by rfl) ⟨55979, by rfl⟩) R111959
theorem R861131 : Reach 861131 := rs (se 1 (by rfl) ⟨645848, by rfl⟩) R1291697
theorem R74759 : Reach 74759 := rs (se 1 (by rfl) ⟨56069, by rfl⟩) R112139
theorem R74831 : Reach 74831 := rs (se 1 (by rfl) ⟨56123, by rfl⟩) R112247
theorem R238787 : Reach 238787 := rs (se 1 (by rfl) ⟨179090, by rfl⟩) R358181
theorem R74951 : Reach 74951 := rs (se 1 (by rfl) ⟨56213, by rfl⟩) R112427
theorem R74999 : Reach 74999 := rs (se 1 (by rfl) ⟨56249, by rfl⟩) R112499
theorem R75113 : Reach 75113 := rs (se 2 (by rfl) ⟨28167, by rfl⟩) R56335
theorem R140687 : Reach 140687 := rs (se 1 (by rfl) ⟨105515, by rfl⟩) R211031
theorem R271781 : Reach 271781 := rs (se 4 (by rfl) ⟨25479, by rfl⟩) R50959
theorem R75191 : Reach 75191 := rs (se 1 (by rfl) ⟨56393, by rfl⟩) R112787
theorem R75227 : Reach 75227 := rs (se 1 (by rfl) ⟨56420, by rfl⟩) R112841
theorem R108071 : Reach 108071 := rs (se 1 (by rfl) ⟨81053, by rfl⟩) R162107
theorem R108155 : Reach 108155 := rs (se 1 (by rfl) ⟨81116, by rfl⟩) R162233
theorem R75593 : Reach 75593 := rs (se 2 (by rfl) ⟨28347, by rfl⟩) R56695
theorem R108395 : Reach 108395 := rs (se 1 (by rfl) ⟨81296, by rfl⟩) R162593
theorem R108449 : Reach 108449 := rs (se 2 (by rfl) ⟨40668, by rfl⟩) R81337
theorem R75695 : Reach 75695 := rs (se 1 (by rfl) ⟨56771, by rfl⟩) R113543
theorem R75707 : Reach 75707 := rs (se 1 (by rfl) ⟨56780, by rfl⟩) R113561
theorem R75785 : Reach 75785 := rs (se 2 (by rfl) ⟨28419, by rfl⟩) R56839
theorem R75815 : Reach 75815 := rs (se 1 (by rfl) ⟨56861, by rfl⟩) R113723
theorem R75833 : Reach 75833 := rs (se 2 (by rfl) ⟨28437, by rfl⟩) R56875
theorem R632933 : Reach 632933 := rs (se 4 (by rfl) ⟨59337, by rfl⟩) R118675
theorem R75899 : Reach 75899 := rs (se 1 (by rfl) ⟨56924, by rfl⟩) R113849
theorem R239773 : Reach 239773 := rs (se 3 (by rfl) ⟨44957, by rfl⟩) R89915
theorem R75947 : Reach 75947 := rs (se 1 (by rfl) ⟨56960, by rfl⟩) R113921
theorem R108791 : Reach 108791 := rs (se 1 (by rfl) ⟨81593, by rfl⟩) R163187
theorem R76025 : Reach 76025 := rs (se 2 (by rfl) ⟨28509, by rfl⟩) R57019
theorem R76127 : Reach 76127 := rs (se 1 (by rfl) ⟨57095, by rfl⟩) R114191
theorem R76139 : Reach 76139 := rs (se 1 (by rfl) ⟨57104, by rfl⟩) R114209
theorem R76175 : Reach 76175 := rs (se 1 (by rfl) ⟨57131, by rfl⟩) R114263
theorem R76295 : Reach 76295 := rs (se 1 (by rfl) ⟨57221, by rfl⟩) R114443
theorem R600605 : Reach 600605 := rs (se 3 (by rfl) ⟨112613, by rfl⟩) R225227
theorem R1026593 : Reach 1026593 := rs (se 2 (by rfl) ⟨384972, by rfl⟩) R769945
theorem R76367 : Reach 76367 := rs (se 1 (by rfl) ⟨57275, by rfl⟩) R114551
theorem R76487 : Reach 76487 := rs (se 1 (by rfl) ⟨57365, by rfl⟩) R114731
theorem R76535 : Reach 76535 := rs (se 1 (by rfl) ⟨57401, by rfl⟩) R114803
theorem R109385 : Reach 109385 := rs (se 2 (by rfl) ⟨41019, by rfl⟩) R82039
theorem R76649 : Reach 76649 := rs (se 2 (by rfl) ⟨28743, by rfl⟩) R57487
theorem R306575 : Reach 306575 := rs (se 1 (by rfl) ⟨229931, by rfl⟩) R459863
theorem R110177 : Reach 110177 := rs (se 2 (by rfl) ⟨41316, by rfl⟩) R82633
theorem R143063 : Reach 143063 := rs (se 1 (by rfl) ⟨107297, by rfl⟩) R214595
theorem R110497 : Reach 110497 := rs (se 2 (by rfl) ⟨41436, by rfl⟩) R82873
theorem R110519 : Reach 110519 := rs (se 1 (by rfl) ⟨82889, by rfl⟩) R165779
theorem R111113 : Reach 111113 := rs (se 2 (by rfl) ⟨41667, by rfl⟩) R83335
theorem R537299 : Reach 537299 := rs (se 1 (by rfl) ⟨402974, by rfl⟩) R805949
theorem R111455 : Reach 111455 := rs (se 1 (by rfl) ⟨83591, by rfl⟩) R167183
theorem R373733 : Reach 373733 := rs (se 4 (by rfl) ⟨35037, by rfl⟩) R70075
theorem R111635 : Reach 111635 := rs (se 1 (by rfl) ⟨83726, by rfl⟩) R167453
theorem R210073 : Reach 210073 := rs (se 2 (by rfl) ⟨78777, by rfl⟩) R157555
theorem R341263 : Reach 341263 := rs (se 1 (by rfl) ⟨255947, by rfl⟩) R511895
theorem R111977 : Reach 111977 := rs (se 2 (by rfl) ⟨41991, by rfl⟩) R83983
theorem R144935 : Reach 144935 := rs (se 1 (by rfl) ⟨108701, by rfl⟩) R217403
theorem R243323 : Reach 243323 := rs (se 1 (by rfl) ⟨182492, by rfl⟩) R364985
theorem R79609 : Reach 79609 := rs (se 2 (by rfl) ⟨29853, by rfl⟩) R59707
theorem R1226497 : Reach 1226497 := rs (se 2 (by rfl) ⟨459936, by rfl⟩) R919873
theorem R309035 : Reach 309035 := rs (se 1 (by rfl) ⟨231776, by rfl⟩) R463553
theorem R112571 : Reach 112571 := rs (se 1 (by rfl) ⟨84428, by rfl⟩) R168857
theorem R79879 : Reach 79879 := rs (se 1 (by rfl) ⟨59909, by rfl⟩) R119819
theorem R276517 : Reach 276517 := rs (se 4 (by rfl) ⟨25923, by rfl⟩) R51847
theorem R47143 : Reach 47143 := rs (se 1 (by rfl) ⟨35357, by rfl⟩) R70715
theorem R112697 : Reach 112697 := rs (se 2 (by rfl) ⟨42261, by rfl⟩) R84523
theorem R47183 : Reach 47183 := rs (se 1 (by rfl) ⟨35387, by rfl⟩) R70775
theorem R47199 : Reach 47199 := rs (se 1 (by rfl) ⟨35399, by rfl⟩) R70799
theorem R47227 : Reach 47227 := rs (se 1 (by rfl) ⟨35420, by rfl⟩) R70841
theorem R47279 : Reach 47279 := rs (se 1 (by rfl) ⟨35459, by rfl⟩) R70919
theorem R47303 : Reach 47303 := rs (se 1 (by rfl) ⟨35477, by rfl⟩) R70955
theorem R47323 : Reach 47323 := rs (se 1 (by rfl) ⟨35492, by rfl⟩) R70985
theorem R47399 : Reach 47399 := rs (se 1 (by rfl) ⟨35549, by rfl⟩) R71099
theorem R47439 : Reach 47439 := rs (se 1 (by rfl) ⟨35579, by rfl⟩) R71159
theorem R47455 : Reach 47455 := rs (se 1 (by rfl) ⟨35591, by rfl⟩) R71183
theorem R47483 : Reach 47483 := rs (se 1 (by rfl) ⟨35612, by rfl⟩) R71225
theorem R113039 : Reach 113039 := rs (se 1 (by rfl) ⟨84779, by rfl⟩) R169559
theorem R47535 : Reach 47535 := rs (se 1 (by rfl) ⟨35651, by rfl⟩) R71303
theorem R80311 : Reach 80311 := rs (se 1 (by rfl) ⟨60233, by rfl⟩) R120467
theorem R47559 : Reach 47559 := rs (se 1 (by rfl) ⟨35669, by rfl⟩) R71339
theorem R47579 : Reach 47579 := rs (se 1 (by rfl) ⟨35684, by rfl⟩) R71369
theorem R80347 : Reach 80347 := rs (se 1 (by rfl) ⟨60260, by rfl⟩) R120521
theorem R47655 : Reach 47655 := rs (se 1 (by rfl) ⟨35741, by rfl⟩) R71483
theorem R47695 : Reach 47695 := rs (se 1 (by rfl) ⟨35771, by rfl⟩) R71543
theorem R47711 : Reach 47711 := rs (se 1 (by rfl) ⟨35783, by rfl⟩) R71567
theorem R80507 : Reach 80507 := rs (se 1 (by rfl) ⟨60380, by rfl⟩) R120761
theorem R47739 : Reach 47739 := rs (se 1 (by rfl) ⟨35804, by rfl⟩) R71609
theorem R113291 : Reach 113291 := rs (se 1 (by rfl) ⟨84968, by rfl⟩) R169937
theorem R47791 : Reach 47791 := rs (se 1 (by rfl) ⟨35843, by rfl⟩) R71687
theorem R47815 : Reach 47815 := rs (se 1 (by rfl) ⟨35861, by rfl⟩) R71723
theorem R113363 : Reach 113363 := rs (se 1 (by rfl) ⟨85022, by rfl⟩) R170045
theorem R47835 : Reach 47835 := rs (se 1 (by rfl) ⟨35876, by rfl⟩) R71753
theorem R47911 : Reach 47911 := rs (se 1 (by rfl) ⟨35933, by rfl⟩) R71867
theorem R47951 : Reach 47951 := rs (se 1 (by rfl) ⟨35963, by rfl⟩) R71927
theorem R47967 : Reach 47967 := rs (se 1 (by rfl) ⟨35975, by rfl⟩) R71951
theorem R47995 : Reach 47995 := rs (se 1 (by rfl) ⟨35996, by rfl⟩) R71993
theorem R48047 : Reach 48047 := rs (se 1 (by rfl) ⟨36035, by rfl⟩) R72071
theorem R48071 : Reach 48071 := rs (se 1 (by rfl) ⟨36053, by rfl⟩) R72107
theorem R48091 : Reach 48091 := rs (se 1 (by rfl) ⟨36068, by rfl⟩) R72137
theorem R80905 : Reach 80905 := rs (se 2 (by rfl) ⟨30339, by rfl⟩) R60679
theorem R48167 : Reach 48167 := rs (se 1 (by rfl) ⟨36125, by rfl⟩) R72251
theorem R48207 : Reach 48207 := rs (se 1 (by rfl) ⟨36155, by rfl⟩) R72311
theorem R48223 : Reach 48223 := rs (se 1 (by rfl) ⟨36167, by rfl⟩) R72335
theorem R48251 : Reach 48251 := rs (se 1 (by rfl) ⟨36188, by rfl⟩) R72377
theorem R81067 : Reach 81067 := rs (se 1 (by rfl) ⟨60800, by rfl⟩) R121601
theorem R48303 : Reach 48303 := rs (se 1 (by rfl) ⟨36227, by rfl⟩) R72455
theorem R48327 : Reach 48327 := rs (se 1 (by rfl) ⟨36245, by rfl⟩) R72491
theorem R48347 : Reach 48347 := rs (se 1 (by rfl) ⟨36260, by rfl⟩) R72521
theorem R48423 : Reach 48423 := rs (se 1 (by rfl) ⟨36317, by rfl⟩) R72635
theorem R48463 : Reach 48463 := rs (se 1 (by rfl) ⟨36347, by rfl⟩) R72695
theorem R48479 : Reach 48479 := rs (se 1 (by rfl) ⟨36359, by rfl⟩) R72719
theorem R48507 : Reach 48507 := rs (se 1 (by rfl) ⟨36380, by rfl⟩) R72761
theorem R48559 : Reach 48559 := rs (se 1 (by rfl) ⟨36419, by rfl⟩) R72839
theorem R48583 : Reach 48583 := rs (se 1 (by rfl) ⟨36437, by rfl⟩) R72875
theorem R81371 : Reach 81371 := rs (se 1 (by rfl) ⟨61028, by rfl⟩) R122057
theorem R48603 : Reach 48603 := rs (se 1 (by rfl) ⟨36452, by rfl⟩) R72905
theorem R48679 : Reach 48679 := rs (se 1 (by rfl) ⟨36509, by rfl⟩) R73019
theorem R48719 : Reach 48719 := rs (se 1 (by rfl) ⟨36539, by rfl⟩) R73079
theorem R48735 : Reach 48735 := rs (se 1 (by rfl) ⟨36551, by rfl⟩) R73103
theorem R278113 : Reach 278113 := rs (se 2 (by rfl) ⟨104292, by rfl⟩) R208585
theorem R409211 : Reach 409211 := rs (se 1 (by rfl) ⟨306908, by rfl⟩) R613817
theorem R48763 : Reach 48763 := rs (se 1 (by rfl) ⟨36572, by rfl⟩) R73145
theorem R114299 : Reach 114299 := rs (se 1 (by rfl) ⟨85724, by rfl⟩) R171449
theorem R48815 : Reach 48815 := rs (se 1 (by rfl) ⟨36611, by rfl⟩) R73223
theorem R147133 : Reach 147133 := rs (se 3 (by rfl) ⟨27587, by rfl⟩) R55175
theorem R81607 : Reach 81607 := rs (se 1 (by rfl) ⟨61205, by rfl⟩) R122411
theorem R48839 : Reach 48839 := rs (se 1 (by rfl) ⟨36629, by rfl⟩) R73259
theorem R179927 : Reach 179927 := rs (se 1 (by rfl) ⟨134945, by rfl⟩) R269891
theorem R48859 : Reach 48859 := rs (se 1 (by rfl) ⟨36644, by rfl⟩) R73289
theorem R311033 : Reach 311033 := rs (se 2 (by rfl) ⟨116637, by rfl⟩) R233275
theorem R114425 : Reach 114425 := rs (se 2 (by rfl) ⟨42909, by rfl⟩) R85819
theorem R48935 : Reach 48935 := rs (se 1 (by rfl) ⟨36701, by rfl⟩) R73403
theorem R48975 : Reach 48975 := rs (se 1 (by rfl) ⟨36731, by rfl⟩) R73463
theorem R48991 : Reach 48991 := rs (se 1 (by rfl) ⟨36743, by rfl⟩) R73487
theorem R81769 : Reach 81769 := rs (se 2 (by rfl) ⟨30663, by rfl⟩) R61327
theorem R49019 : Reach 49019 := rs (se 1 (by rfl) ⟨36764, by rfl⟩) R73529
theorem R49071 : Reach 49071 := rs (se 1 (by rfl) ⟨36803, by rfl⟩) R73607
theorem R49095 : Reach 49095 := rs (se 1 (by rfl) ⟨36821, by rfl⟩) R73643
theorem R49115 : Reach 49115 := rs (se 1 (by rfl) ⟨36836, by rfl⟩) R73673
theorem R114695 : Reach 114695 := rs (se 1 (by rfl) ⟨86021, by rfl⟩) R172043
theorem R49191 : Reach 49191 := rs (se 1 (by rfl) ⟨36893, by rfl⟩) R73787
theorem R49231 : Reach 49231 := rs (se 1 (by rfl) ⟨36923, by rfl⟩) R73847
theorem R114767 : Reach 114767 := rs (se 1 (by rfl) ⟨86075, by rfl⟩) R172151
theorem R49247 : Reach 49247 := rs (se 1 (by rfl) ⟨36935, by rfl⟩) R73871
theorem R49275 : Reach 49275 := rs (se 1 (by rfl) ⟨36956, by rfl⟩) R73913
theorem R180377 : Reach 180377 := rs (se 2 (by rfl) ⟨67641, by rfl⟩) R135283
theorem R49327 : Reach 49327 := rs (se 1 (by rfl) ⟨36995, by rfl⟩) R73991
theorem R49351 : Reach 49351 := rs (se 1 (by rfl) ⟨37013, by rfl⟩) R74027
theorem R49371 : Reach 49371 := rs (se 1 (by rfl) ⟨37028, by rfl⟩) R74057
theorem R606437 : Reach 606437 := rs (se 4 (by rfl) ⟨56853, by rfl⟩) R113707
theorem R49447 : Reach 49447 := rs (se 1 (by rfl) ⟨37085, by rfl⟩) R74171
theorem R246077 : Reach 246077 := rs (se 3 (by rfl) ⟨46139, by rfl⟩) R92279
theorem R49487 : Reach 49487 := rs (se 1 (by rfl) ⟨37115, by rfl⟩) R74231
theorem R344407 : Reach 344407 := rs (se 1 (by rfl) ⟨258305, by rfl⟩) R516611
theorem R49503 : Reach 49503 := rs (se 1 (by rfl) ⟨37127, by rfl⟩) R74255
theorem R49531 : Reach 49531 := rs (se 1 (by rfl) ⟨37148, by rfl⟩) R74297
theorem R49583 : Reach 49583 := rs (se 1 (by rfl) ⟨37187, by rfl⟩) R74375
theorem R82363 : Reach 82363 := rs (se 1 (by rfl) ⟨61772, by rfl⟩) R123545
theorem R49607 : Reach 49607 := rs (se 1 (by rfl) ⟨37205, by rfl⟩) R74411
theorem R49627 : Reach 49627 := rs (se 1 (by rfl) ⟨37220, by rfl⟩) R74441
theorem R82471 : Reach 82471 := rs (se 1 (by rfl) ⟨61853, by rfl⟩) R123707
theorem R49703 : Reach 49703 := rs (se 1 (by rfl) ⟨37277, by rfl⟩) R74555
theorem R49743 : Reach 49743 := rs (se 1 (by rfl) ⟨37307, by rfl⟩) R74615
theorem R49787 : Reach 49787 := rs (se 1 (by rfl) ⟨37340, by rfl⟩) R74681
theorem R2081477 : Reach 2081477 := rs (se 4 (by rfl) ⟨195138, by rfl⟩) R390277
theorem R49863 : Reach 49863 := rs (se 1 (by rfl) ⟨37397, by rfl⟩) R74795
theorem R639697 : Reach 639697 := rs (se 2 (by rfl) ⟨239886, by rfl⟩) R479773
theorem R82679 : Reach 82679 := rs (se 1 (by rfl) ⟨62009, by rfl⟩) R124019
theorem R50015 : Reach 50015 := rs (se 1 (by rfl) ⟨37511, by rfl⟩) R75023
theorem R82795 : Reach 82795 := rs (se 1 (by rfl) ⟨62096, by rfl⟩) R124193
theorem R115631 : Reach 115631 := rs (se 1 (by rfl) ⟨86723, by rfl⟩) R173447
theorem R50095 : Reach 50095 := rs (se 1 (by rfl) ⟨37571, by rfl⟩) R75143
theorem R50139 : Reach 50139 := rs (se 1 (by rfl) ⟨37604, by rfl⟩) R75209
theorem R279571 : Reach 279571 := rs (se 1 (by rfl) ⟨209678, by rfl⟩) R419357
theorem R50215 : Reach 50215 := rs (se 1 (by rfl) ⟨37661, by rfl⟩) R75323
theorem R50255 : Reach 50255 := rs (se 1 (by rfl) ⟨37691, by rfl⟩) R75383
theorem R50299 : Reach 50299 := rs (se 1 (by rfl) ⟨37724, by rfl⟩) R75449
theorem R50375 : Reach 50375 := rs (se 1 (by rfl) ⟨37781, by rfl⟩) R75563
theorem R50527 : Reach 50527 := rs (se 1 (by rfl) ⟨37895, by rfl⟩) R75791
theorem R1459619 : Reach 1459619 := rs (se 1 (by rfl) ⟨1094714, by rfl⟩) R2189429
theorem R50607 : Reach 50607 := rs (se 1 (by rfl) ⟨37955, by rfl⟩) R75911
theorem R181723 : Reach 181723 := rs (se 1 (by rfl) ⟨136292, by rfl⟩) R272585
theorem R83419 : Reach 83419 := rs (se 1 (by rfl) ⟨62564, by rfl⟩) R125129
theorem R50651 : Reach 50651 := rs (se 1 (by rfl) ⟨37988, by rfl⟩) R75977
theorem R50727 : Reach 50727 := rs (se 1 (by rfl) ⟨38045, by rfl⟩) R76091
theorem R50767 : Reach 50767 := rs (se 1 (by rfl) ⟨38075, by rfl⟩) R76151
theorem R116321 : Reach 116321 := rs (se 2 (by rfl) ⟨43620, by rfl⟩) R87241
theorem R50811 : Reach 50811 := rs (se 1 (by rfl) ⟨38108, by rfl⟩) R76217
theorem R50887 : Reach 50887 := rs (se 1 (by rfl) ⟨38165, by rfl⟩) R76331
theorem R51039 : Reach 51039 := rs (se 1 (by rfl) ⟨38279, by rfl⟩) R76559
theorem R345991 : Reach 345991 := rs (se 1 (by rfl) ⟨259493, by rfl⟩) R518987
theorem R83855 : Reach 83855 := rs (se 1 (by rfl) ⟨62891, by rfl⟩) R125783
theorem R51119 : Reach 51119 := rs (se 1 (by rfl) ⟨38339, by rfl⟩) R76679
theorem R542821 : Reach 542821 := rs (se 4 (by rfl) ⟨50889, by rfl⟩) R101779
theorem R84091 : Reach 84091 := rs (se 1 (by rfl) ⟨63068, by rfl⟩) R126137
theorem R84179 : Reach 84179 := rs (se 1 (by rfl) ⟨63134, by rfl⟩) R126269
theorem R510209 : Reach 510209 := rs (se 2 (by rfl) ⟨191328, by rfl⟩) R382657
theorem R248345 : Reach 248345 := rs (se 2 (by rfl) ⟨93129, by rfl⟩) R186259
theorem R182843 : Reach 182843 := rs (se 1 (by rfl) ⟨137132, by rfl⟩) R274265
theorem R84577 : Reach 84577 := rs (se 2 (by rfl) ⟨31716, by rfl⟩) R63433
theorem R51835 : Reach 51835 := rs (se 1 (by rfl) ⟨38876, by rfl⟩) R77753
theorem R379565 : Reach 379565 := rs (se 3 (by rfl) ⟨71168, by rfl⟩) R142337
theorem R84955 : Reach 84955 := rs (se 1 (by rfl) ⟨63716, by rfl⟩) R127433
theorem R216445 : Reach 216445 := rs (se 3 (by rfl) ⟨40583, by rfl⟩) R81167
theorem R970157 : Reach 970157 := rs (se 3 (by rfl) ⟨181904, by rfl⟩) R363809
theorem R52655 : Reach 52655 := rs (se 1 (by rfl) ⟨39491, by rfl⟩) R78983
theorem R85583 : Reach 85583 := rs (se 1 (by rfl) ⟨64187, by rfl⟩) R128375
theorem R85627 : Reach 85627 := rs (se 1 (by rfl) ⟨64220, by rfl⟩) R128441
theorem R282487 : Reach 282487 := rs (se 1 (by rfl) ⟨211865, by rfl⟩) R423731
theorem R53167 : Reach 53167 := rs (se 1 (by rfl) ⟨39875, by rfl⟩) R79751
theorem R151571 : Reach 151571 := rs (se 1 (by rfl) ⟨113678, by rfl⟩) R227357
theorem R86035 : Reach 86035 := rs (se 1 (by rfl) ⟨64526, by rfl⟩) R129053
theorem R151723 : Reach 151723 := rs (se 1 (by rfl) ⟨113792, by rfl⟩) R227585
theorem R4837637 : Reach 4837637 := rs (se 4 (by rfl) ⟨453528, by rfl⟩) R907057
theorem R53599 : Reach 53599 := rs (se 1 (by rfl) ⟨40199, by rfl⟩) R80399
theorem R86455 : Reach 86455 := rs (se 1 (by rfl) ⟨64841, by rfl⟩) R129683
theorem R152027 : Reach 152027 := rs (se 1 (by rfl) ⟨114020, by rfl⟩) R228041
theorem R414233 : Reach 414233 := rs (se 2 (by rfl) ⟨155337, by rfl⟩) R310675
theorem R348731 : Reach 348731 := rs (se 1 (by rfl) ⟨261548, by rfl⟩) R523097
theorem R119495 : Reach 119495 := rs (se 1 (by rfl) ⟨89621, by rfl⟩) R179243
theorem R53959 : Reach 53959 := rs (se 1 (by rfl) ⟨40469, by rfl⟩) R80939
theorem R578411 : Reach 578411 := rs (se 1 (by rfl) ⟨433808, by rfl⟩) R867617
theorem R119713 : Reach 119713 := rs (se 2 (by rfl) ⟨44892, by rfl⟩) R89785
theorem R86959 : Reach 86959 := rs (se 1 (by rfl) ⟨65219, by rfl⟩) R130439
theorem R381995 : Reach 381995 := rs (se 1 (by rfl) ⟨286496, by rfl⟩) R572993
theorem R185591 : Reach 185591 := rs (se 1 (by rfl) ⟨139193, by rfl⟩) R278387
theorem R251261 : Reach 251261 := rs (se 3 (by rfl) ⟨47111, by rfl⟩) R94223
theorem R26891747 : Reach 26891747 := rs (se 1 (by rfl) ⟨20168810, by rfl⟩) R40337621
theorem R120329 : Reach 120329 := rs (se 2 (by rfl) ⟨45123, by rfl⟩) R90247
theorem R54823 : Reach 54823 := rs (se 1 (by rfl) ⟨41117, by rfl⟩) R82235
theorem R153211 : Reach 153211 := rs (se 1 (by rfl) ⟨114908, by rfl⟩) R229817
theorem R120649 : Reach 120649 := rs (se 2 (by rfl) ⟨45243, by rfl⟩) R90487
theorem R186563 : Reach 186563 := rs (se 1 (by rfl) ⟨139922, by rfl⟩) R279845
theorem R1399133 : Reach 1399133 := rs (se 3 (by rfl) ⟨262337, by rfl⟩) R524675
theorem R711017 : Reach 711017 := rs (se 2 (by rfl) ⟨266631, by rfl⟩) R533263
theorem R187019 : Reach 187019 := rs (se 1 (by rfl) ⟨140264, by rfl⟩) R280529
theorem R547661 : Reach 547661 := rs (se 3 (by rfl) ⟨102686, by rfl⟩) R205373
theorem R187231 : Reach 187231 := rs (se 1 (by rfl) ⟨140423, by rfl⟩) R280847
theorem R154543 : Reach 154543 := rs (se 1 (by rfl) ⟨115907, by rfl⟩) R231815
theorem R121783 : Reach 121783 := rs (se 1 (by rfl) ⟨91337, by rfl⟩) R182675
theorem R613493 : Reach 613493 := rs (se 5 (by rfl) ⟨28757, by rfl⟩) R57515
theorem R56443 : Reach 56443 := rs (se 1 (by rfl) ⟨42332, by rfl⟩) R84665
theorem R1072397 : Reach 1072397 := rs (se 3 (by rfl) ⟨201074, by rfl⟩) R402149
theorem R56911 : Reach 56911 := rs (se 1 (by rfl) ⟨42683, by rfl⟩) R85367
theorem R122579 : Reach 122579 := rs (se 1 (by rfl) ⟨91934, by rfl⟩) R183869
theorem R89849 : Reach 89849 := rs (se 2 (by rfl) ⟨33693, by rfl⟩) R67387
theorem R188189 : Reach 188189 := rs (se 3 (by rfl) ⟨35285, by rfl⟩) R70571
theorem R188203 : Reach 188203 := rs (se 1 (by rfl) ⟨141152, by rfl⟩) R282305
theorem R89929 : Reach 89929 := rs (se 2 (by rfl) ⟨33723, by rfl⟩) R67447
theorem R57271 : Reach 57271 := rs (se 1 (by rfl) ⟨42953, by rfl⟩) R85907
theorem R57307 : Reach 57307 := rs (se 1 (by rfl) ⟨42980, by rfl⟩) R85961
theorem R155915 : Reach 155915 := rs (se 1 (by rfl) ⟨116936, by rfl⟩) R233873
theorem R123241 : Reach 123241 := rs (se 2 (by rfl) ⟨46215, by rfl⟩) R92431
theorem R90551 : Reach 90551 := rs (se 1 (by rfl) ⟨67913, by rfl⟩) R135827
theorem R123515 : Reach 123515 := rs (se 1 (by rfl) ⟨92636, by rfl⟩) R185273
theorem R91307 : Reach 91307 := rs (se 1 (by rfl) ⟨68480, by rfl⟩) R136961
theorem R58843 : Reach 58843 := rs (se 1 (by rfl) ⟨44132, by rfl⟩) R88265
theorem R91687 : Reach 91687 := rs (se 1 (by rfl) ⟨68765, by rfl⟩) R137531
theorem R255635 : Reach 255635 := rs (se 1 (by rfl) ⟨191726, by rfl⟩) R383453
theorem R91847 : Reach 91847 := rs (se 1 (by rfl) ⟨68885, by rfl⟩) R137771
theorem R550817 : Reach 550817 := rs (se 2 (by rfl) ⟨206556, by rfl⟩) R413113
theorem R157697 : Reach 157697 := rs (se 2 (by rfl) ⟨59136, by rfl⟩) R118273
theorem R551069 : Reach 551069 := rs (se 3 (by rfl) ⟨103325, by rfl⟩) R206651
theorem R387433 : Reach 387433 := rs (se 2 (by rfl) ⟨145287, by rfl⟩) R290575
theorem R125327 : Reach 125327 := rs (se 1 (by rfl) ⟨93995, by rfl⟩) R187991
theorem R125651 : Reach 125651 := rs (se 1 (by rfl) ⟨94238, by rfl⟩) R188477
theorem R93001 : Reach 93001 := rs (se 2 (by rfl) ⟨34875, by rfl⟩) R69751
theorem R191393 : Reach 191393 := rs (se 2 (by rfl) ⟨71772, by rfl⟩) R143545
theorem R715969 : Reach 715969 := rs (se 2 (by rfl) ⟨268488, by rfl⟩) R536977
theorem R1076723 : Reach 1076723 := rs (se 1 (by rfl) ⟨807542, by rfl⟩) R1615085
theorem R552581 : Reach 552581 := rs (se 4 (by rfl) ⟨51804, by rfl⟩) R103609
theorem R159583 : Reach 159583 := rs (se 1 (by rfl) ⟨119687, by rfl⟩) R239375
theorem R192365 : Reach 192365 := rs (se 3 (by rfl) ⟨36068, by rfl⟩) R72137
theorem R454531 : Reach 454531 := rs (se 1 (by rfl) ⟨340898, by rfl⟩) R681797
theorem R225665 : Reach 225665 := rs (se 2 (by rfl) ⟨84624, by rfl⟩) R169249
theorem R61879 : Reach 61879 := rs (se 1 (by rfl) ⟨46409, by rfl⟩) R92819
theorem R193049 : Reach 193049 := rs (se 2 (by rfl) ⟨72393, by rfl⟩) R144787
theorem R193063 : Reach 193063 := rs (se 1 (by rfl) ⟨144797, by rfl⟩) R289595
theorem R324155 : Reach 324155 := rs (se 1 (by rfl) ⟨243116, by rfl⟩) R486233
theorem R160379 : Reach 160379 := rs (se 1 (by rfl) ⟨120284, by rfl⟩) R240569
theorem R881425 : Reach 881425 := rs (se 2 (by rfl) ⟨330534, by rfl⟩) R661069
theorem R160541 : Reach 160541 := rs (se 3 (by rfl) ⟨30101, by rfl⟩) R60203
theorem R914327 : Reach 914327 := rs (se 1 (by rfl) ⟨685745, by rfl⟩) R1371491
theorem R127919 : Reach 127919 := rs (se 1 (by rfl) ⟨95939, by rfl⟩) R191879
theorem R95195 : Reach 95195 := rs (se 1 (by rfl) ⟨71396, by rfl⟩) R142793
theorem R95431 : Reach 95431 := rs (se 1 (by rfl) ⟨71573, by rfl⟩) R143147
theorem R193853 : Reach 193853 := rs (se 3 (by rfl) ⟨36347, by rfl⟩) R72695
theorem R95593 : Reach 95593 := rs (se 2 (by rfl) ⟨35847, by rfl⟩) R71695
theorem R161225 : Reach 161225 := rs (se 2 (by rfl) ⟨60459, by rfl⟩) R120919
theorem R161243 : Reach 161243 := rs (se 1 (by rfl) ⟨120932, by rfl⟩) R241865
theorem R194035 : Reach 194035 := rs (se 1 (by rfl) ⟨145526, by rfl⟩) R291053
theorem R128537 : Reach 128537 := rs (se 2 (by rfl) ⟨48201, by rfl⟩) R96403
theorem R521873 : Reach 521873 := rs (se 2 (by rfl) ⟨195702, by rfl⟩) R391405
theorem R194233 : Reach 194233 := rs (se 2 (by rfl) ⟨72837, by rfl⟩) R145675
theorem R63175 : Reach 63175 := rs (se 1 (by rfl) ⟨47381, by rfl⟩) R94763
theorem R63337 : Reach 63337 := rs (se 2 (by rfl) ⟨23751, by rfl⟩) R47503
theorem R259949 : Reach 259949 := rs (se 3 (by rfl) ⟨48740, by rfl⟩) R97481
theorem R260111 : Reach 260111 := rs (se 1 (by rfl) ⟨195083, by rfl⟩) R390167
theorem R161945 : Reach 161945 := rs (se 2 (by rfl) ⟨60729, by rfl⟩) R121459
theorem R358667 : Reach 358667 := rs (se 1 (by rfl) ⟨269000, by rfl⟩) R538001
theorem R63919 : Reach 63919 := rs (se 1 (by rfl) ⟨47939, by rfl⟩) R95879
theorem R129575 : Reach 129575 := rs (se 1 (by rfl) ⟨97181, by rfl⟩) R194363
theorem R359113 : Reach 359113 := rs (se 2 (by rfl) ⟨134667, by rfl⟩) R269335
theorem R654155 : Reach 654155 := rs (se 1 (by rfl) ⟨490616, by rfl⟩) R981233
theorem R163133 : Reach 163133 := rs (se 3 (by rfl) ⟨30587, by rfl⟩) R61175
theorem R163475 : Reach 163475 := rs (se 1 (by rfl) ⟨122606, by rfl⟩) R245213
theorem R360125 : Reach 360125 := rs (se 3 (by rfl) ⟨67523, by rfl⟩) R135047
theorem R163745 : Reach 163745 := rs (se 2 (by rfl) ⟨61404, by rfl⟩) R122809
theorem R425915 : Reach 425915 := rs (se 1 (by rfl) ⟨319436, by rfl⟩) R638873
theorem R1474757 : Reach 1474757 := rs (se 4 (by rfl) ⟨138258, by rfl⟩) R276517
theorem R164051 : Reach 164051 := rs (se 1 (by rfl) ⟨123038, by rfl⟩) R246077
theorem R131435 : Reach 131435 := rs (se 1 (by rfl) ⟨98576, by rfl⟩) R197153
theorem R459209 : Reach 459209 := rs (se 2 (by rfl) ⟨172203, by rfl⟩) R344407
theorem R164321 : Reach 164321 := rs (se 2 (by rfl) ⟨61620, by rfl⟩) R123241
theorem R393911 : Reach 393911 := rs (se 1 (by rfl) ⟨295433, by rfl⟩) R590867
theorem R852929 : Reach 852929 := rs (se 2 (by rfl) ⟨319848, by rfl⟩) R639697
theorem R263519 : Reach 263519 := rs (se 1 (by rfl) ⟨197639, by rfl⟩) R395279
theorem R165563 : Reach 165563 := rs (se 1 (by rfl) ⟨124172, by rfl⟩) R248345
theorem R461321 : Reach 461321 := rs (se 2 (by rfl) ⟨172995, by rfl⟩) R345991
theorem R2296349 : Reach 2296349 := rs (se 3 (by rfl) ⟨430565, by rfl⟩) R861131
theorem R101047 : Reach 101047 := rs (se 1 (by rfl) ⟨75785, by rfl⟩) R151571
theorem R723761 : Reach 723761 := rs (se 2 (by rfl) ⟨271410, by rfl⟩) R542821
theorem R101351 : Reach 101351 := rs (se 1 (by rfl) ⟨76013, by rfl⟩) R152027
theorem R199667 : Reach 199667 := rs (se 1 (by rfl) ⟨149750, by rfl⟩) R299501
theorem R232487 : Reach 232487 := rs (se 1 (by rfl) ⟨174365, by rfl⟩) R348731
theorem R134615 : Reach 134615 := rs (se 1 (by rfl) ⟨100961, by rfl⟩) R201923
theorem R69113 : Reach 69113 := rs (se 2 (by rfl) ⟨25917, by rfl⟩) R51835
theorem R167507 : Reach 167507 := rs (se 1 (by rfl) ⟨125630, by rfl⟩) R251261
theorem R265837 : Reach 265837 := rs (se 3 (by rfl) ⟨49844, by rfl⟩) R99689
theorem R17927831 : Reach 17927831 := rs (se 1 (by rfl) ⟨13445873, by rfl⟩) R26891747
theorem R364445 : Reach 364445 := rs (se 3 (by rfl) ⟨68333, by rfl⟩) R136667
theorem R954625 : Reach 954625 := rs (se 2 (by rfl) ⟨357984, by rfl⟩) R715969
theorem R69979 : Reach 69979 := rs (se 1 (by rfl) ⟨52484, by rfl⟩) R104969
theorem R398047 : Reach 398047 := rs (se 1 (by rfl) ⟨298535, by rfl⟩) R597071
theorem R463781 : Reach 463781 := rs (se 4 (by rfl) ⟨43479, by rfl⟩) R86959
theorem R693197 : Reach 693197 := rs (se 3 (by rfl) ⟨129974, by rfl⟩) R259949
theorem R70889 : Reach 70889 := rs (se 2 (by rfl) ⟨26583, by rfl⟩) R53167
theorem R70943 : Reach 70943 := rs (se 1 (by rfl) ⟨53207, by rfl⟩) R106415
theorem R693629 : Reach 693629 := rs (se 3 (by rfl) ⟨130055, by rfl⟩) R260111
theorem R365957 : Reach 365957 := rs (se 4 (by rfl) ⟨34308, by rfl⟩) R68617
theorem R71111 : Reach 71111 := rs (se 1 (by rfl) ⟨53333, by rfl⟩) R106667
theorem R103943 : Reach 103943 := rs (se 1 (by rfl) ⟨77957, by rfl⟩) R155915
theorem R71465 : Reach 71465 := rs (se 2 (by rfl) ⟨26799, by rfl⟩) R53599
theorem R71471 : Reach 71471 := rs (se 1 (by rfl) ⟨53603, by rfl⟩) R107207
theorem R71945 : Reach 71945 := rs (se 2 (by rfl) ⟨26979, by rfl⟩) R53959
theorem R137497 : Reach 137497 := rs (se 2 (by rfl) ⟨51561, by rfl⟩) R103123
theorem R72047 : Reach 72047 := rs (se 1 (by rfl) ⟨54035, by rfl⟩) R108071
theorem R72103 : Reach 72103 := rs (se 1 (by rfl) ⟨54077, by rfl⟩) R108155
theorem R170423 : Reach 170423 := rs (se 1 (by rfl) ⟨127817, by rfl⟩) R255635
theorem R72263 : Reach 72263 := rs (se 1 (by rfl) ⟨54197, by rfl⟩) R108395
theorem R72299 : Reach 72299 := rs (se 1 (by rfl) ⟨54224, by rfl⟩) R108449
theorem R367211 : Reach 367211 := rs (se 1 (by rfl) ⟨275408, by rfl⟩) R550817
theorem R105131 : Reach 105131 := rs (se 1 (by rfl) ⟨78848, by rfl⟩) R157697
theorem R367379 : Reach 367379 := rs (se 1 (by rfl) ⟨275534, by rfl⟩) R551069
theorem R72527 : Reach 72527 := rs (se 1 (by rfl) ⟨54395, by rfl⟩) R108791
theorem R400403 : Reach 400403 := rs (se 1 (by rfl) ⟨300302, by rfl⟩) R600605
theorem R72923 : Reach 72923 := rs (se 1 (by rfl) ⟨54692, by rfl⟩) R109385
theorem R73097 : Reach 73097 := rs (se 2 (by rfl) ⟨27411, by rfl⟩) R54823
theorem R400889 : Reach 400889 := rs (se 2 (by rfl) ⟨150333, by rfl⟩) R300667
theorem R204281 : Reach 204281 := rs (se 2 (by rfl) ⟨76605, by rfl⟩) R153211
theorem R204383 : Reach 204383 := rs (se 1 (by rfl) ⟨153287, by rfl⟩) R306575
theorem R106145 : Reach 106145 := rs (se 2 (by rfl) ⟨39804, by rfl⟩) R79609
theorem R73451 : Reach 73451 := rs (se 1 (by rfl) ⟨55088, by rfl⟩) R110177
theorem R368387 : Reach 368387 := rs (se 1 (by rfl) ⟨276290, by rfl⟩) R552581
theorem R73679 : Reach 73679 := rs (se 1 (by rfl) ⟨55259, by rfl⟩) R110519
theorem R106505 : Reach 106505 := rs (se 2 (by rfl) ⟨39939, by rfl⟩) R79879
theorem R74075 : Reach 74075 := rs (se 1 (by rfl) ⟨55556, by rfl⟩) R111113
theorem R106919 : Reach 106919 := rs (se 1 (by rfl) ⟨80189, by rfl⟩) R160379
theorem R107027 : Reach 107027 := rs (se 1 (by rfl) ⟨80270, by rfl⟩) R160541
theorem R74303 : Reach 74303 := rs (se 1 (by rfl) ⟨55727, by rfl⟩) R111455
theorem R107081 : Reach 107081 := rs (se 2 (by rfl) ⟨40155, by rfl⟩) R80311
theorem R107129 : Reach 107129 := rs (se 2 (by rfl) ⟨40173, by rfl⟩) R80347
theorem R74423 : Reach 74423 := rs (se 1 (by rfl) ⟨55817, by rfl⟩) R111635
theorem R2859725 : Reach 2859725 := rs (se 3 (by rfl) ⟨536198, by rfl⟩) R1072397
theorem R271097 : Reach 271097 := rs (se 2 (by rfl) ⟨101661, by rfl⟩) R203323
theorem R74651 : Reach 74651 := rs (se 1 (by rfl) ⟨55988, by rfl⟩) R111977
theorem R107483 : Reach 107483 := rs (se 1 (by rfl) ⟨80612, by rfl⟩) R161225
theorem R107495 : Reach 107495 := rs (se 1 (by rfl) ⟨80621, by rfl⟩) R161243
theorem R140413 : Reach 140413 := rs (se 3 (by rfl) ⟨26327, by rfl⟩) R52655
theorem R206023 : Reach 206023 := rs (se 1 (by rfl) ⟨154517, by rfl⟩) R309035
theorem R206057 : Reach 206057 := rs (se 2 (by rfl) ⟨77271, by rfl⟩) R154543
theorem R75047 : Reach 75047 := rs (se 1 (by rfl) ⟨56285, by rfl⟩) R112571
theorem R107873 : Reach 107873 := rs (se 2 (by rfl) ⟨40452, by rfl⟩) R80905
theorem R75131 : Reach 75131 := rs (se 1 (by rfl) ⟨56348, by rfl⟩) R112697
theorem R107963 : Reach 107963 := rs (se 1 (by rfl) ⟨80972, by rfl⟩) R161945
theorem R75257 : Reach 75257 := rs (se 2 (by rfl) ⟨28221, by rfl⟩) R56443
theorem R239111 : Reach 239111 := rs (se 1 (by rfl) ⟨179333, by rfl⟩) R358667
theorem R108089 : Reach 108089 := rs (se 2 (by rfl) ⟨40533, by rfl⟩) R81067
theorem R75359 : Reach 75359 := rs (se 1 (by rfl) ⟨56519, by rfl⟩) R113039
theorem R75527 : Reach 75527 := rs (se 1 (by rfl) ⟨56645, by rfl⟩) R113291
theorem R75575 : Reach 75575 := rs (se 1 (by rfl) ⟨56681, by rfl⟩) R113363
theorem R436103 : Reach 436103 := rs (se 1 (by rfl) ⟨327077, by rfl⟩) R654155
theorem R239597 : Reach 239597 := rs (se 3 (by rfl) ⟨44924, by rfl⟩) R89849
theorem R75881 : Reach 75881 := rs (se 2 (by rfl) ⟨28455, by rfl⟩) R56911
theorem R370817 : Reach 370817 := rs (se 2 (by rfl) ⟨139056, by rfl⟩) R278113
theorem R108755 : Reach 108755 := rs (se 1 (by rfl) ⟨81566, by rfl⟩) R163133
theorem R108809 : Reach 108809 := rs (se 2 (by rfl) ⟨40803, by rfl⟩) R81607
theorem R731429 : Reach 731429 := rs (se 4 (by rfl) ⟨68571, by rfl⟩) R137143
theorem R272807 : Reach 272807 := rs (se 1 (by rfl) ⟨204605, by rfl⟩) R409211
theorem R76199 : Reach 76199 := rs (se 1 (by rfl) ⟨57149, by rfl⟩) R114299
theorem R108983 : Reach 108983 := rs (se 1 (by rfl) ⟨81737, by rfl⟩) R163475
theorem R240083 : Reach 240083 := rs (se 1 (by rfl) ⟨180062, by rfl⟩) R360125
theorem R109025 : Reach 109025 := rs (se 2 (by rfl) ⟨40884, by rfl⟩) R81769
theorem R207355 : Reach 207355 := rs (se 1 (by rfl) ⟨155516, by rfl⟩) R311033
theorem R76283 : Reach 76283 := rs (se 1 (by rfl) ⟨57212, by rfl⟩) R114425
theorem R76361 : Reach 76361 := rs (se 2 (by rfl) ⟨28635, by rfl⟩) R57271
theorem R109163 : Reach 109163 := rs (se 1 (by rfl) ⟨81872, by rfl⟩) R163745
theorem R76409 : Reach 76409 := rs (se 2 (by rfl) ⟨28653, by rfl⟩) R57307
theorem R76463 : Reach 76463 := rs (se 1 (by rfl) ⟨57347, by rfl⟩) R114695
theorem R76511 : Reach 76511 := rs (se 1 (by rfl) ⟨57383, by rfl⟩) R114767
theorem R109331 : Reach 109331 := rs (se 1 (by rfl) ⟨81998, by rfl⟩) R163997
theorem R240407 : Reach 240407 := rs (se 1 (by rfl) ⟨180305, by rfl⟩) R360611
theorem R404291 : Reach 404291 := rs (se 1 (by rfl) ⟨303218, by rfl⟩) R606437
theorem R371789 : Reach 371789 := rs (se 3 (by rfl) ⟨69710, by rfl⟩) R139421
theorem R109691 : Reach 109691 := rs (se 1 (by rfl) ⟨82268, by rfl⟩) R164537
theorem R1387651 : Reach 1387651 := rs (se 1 (by rfl) ⟨1040738, by rfl⟩) R2081477
theorem R109817 : Reach 109817 := rs (se 2 (by rfl) ⟨41181, by rfl⟩) R82363
theorem R77087 : Reach 77087 := rs (se 1 (by rfl) ⟨57815, by rfl⟩) R115631
theorem R109961 : Reach 109961 := rs (se 2 (by rfl) ⟨41235, by rfl⟩) R82471
theorem R110087 : Reach 110087 := rs (se 1 (by rfl) ⟨82565, by rfl⟩) R165131
theorem R110267 : Reach 110267 := rs (se 1 (by rfl) ⟨82700, by rfl⟩) R165401
theorem R110315 : Reach 110315 := rs (se 1 (by rfl) ⟨82736, by rfl⟩) R165473
theorem R175879 : Reach 175879 := rs (se 1 (by rfl) ⟨131909, by rfl⟩) R263819
theorem R110393 : Reach 110393 := rs (se 2 (by rfl) ⟨41397, by rfl⟩) R82795
theorem R372761 : Reach 372761 := rs (se 2 (by rfl) ⟨139785, by rfl⟩) R279571
theorem R340139 : Reach 340139 := rs (se 1 (by rfl) ⟨255104, by rfl⟩) R510209
theorem R242027 : Reach 242027 := rs (se 1 (by rfl) ⟨181520, by rfl⟩) R363041
theorem R111023 : Reach 111023 := rs (se 1 (by rfl) ⟨83267, by rfl⟩) R166535
theorem R111059 : Reach 111059 := rs (se 1 (by rfl) ⟨83294, by rfl⟩) R166589
theorem R176609 : Reach 176609 := rs (se 2 (by rfl) ⟨66228, by rfl⟩) R132457
theorem R111167 : Reach 111167 := rs (se 1 (by rfl) ⟨83375, by rfl⟩) R166751
theorem R242297 : Reach 242297 := rs (se 2 (by rfl) ⟨90861, by rfl⟩) R181723
theorem R78457 : Reach 78457 := rs (se 2 (by rfl) ⟨29421, by rfl⟩) R58843
theorem R111275 : Reach 111275 := rs (se 1 (by rfl) ⟨83456, by rfl⟩) R166913
theorem R242347 : Reach 242347 := rs (se 1 (by rfl) ⟨181760, by rfl⟩) R363521
theorem R111755 : Reach 111755 := rs (se 1 (by rfl) ⟨83816, by rfl⟩) R167633
theorem R111815 : Reach 111815 := rs (se 1 (by rfl) ⟨83861, by rfl⟩) R167723
theorem R111995 : Reach 111995 := rs (se 1 (by rfl) ⟨83996, by rfl⟩) R167993
theorem R374219 : Reach 374219 := rs (se 1 (by rfl) ⟨280664, by rfl⟩) R561329
theorem R112121 : Reach 112121 := rs (se 2 (by rfl) ⟨42045, by rfl⟩) R84091
theorem R3225091 : Reach 3225091 := rs (se 1 (by rfl) ⟨2418818, by rfl⟩) R4837637
theorem R112211 : Reach 112211 := rs (se 1 (by rfl) ⟨84158, by rfl⟩) R168317
theorem R276155 : Reach 276155 := rs (se 1 (by rfl) ⟨207116, by rfl⟩) R414233
theorem R112391 : Reach 112391 := rs (se 1 (by rfl) ⟨84293, by rfl⟩) R168587
theorem R243485 : Reach 243485 := rs (se 3 (by rfl) ⟨45653, by rfl⟩) R91307
theorem R79663 : Reach 79663 := rs (se 1 (by rfl) ⟨59747, by rfl⟩) R119495
theorem R112769 : Reach 112769 := rs (se 2 (by rfl) ⟨42288, by rfl⟩) R84577
theorem R47391 : Reach 47391 := rs (se 1 (by rfl) ⟨35543, by rfl⟩) R71087
theorem R47451 : Reach 47451 := rs (se 1 (by rfl) ⟨35588, by rfl⟩) R71177
theorem R80219 : Reach 80219 := rs (se 1 (by rfl) ⟨60164, by rfl⟩) R120329
theorem R113003 : Reach 113003 := rs (se 1 (by rfl) ⟨84752, by rfl⟩) R169505
theorem R47471 : Reach 47471 := rs (se 1 (by rfl) ⟨35603, by rfl⟩) R71207
theorem R244079 : Reach 244079 := rs (se 1 (by rfl) ⟨183059, by rfl⟩) R366119
theorem R47527 : Reach 47527 := rs (se 1 (by rfl) ⟨35645, by rfl⟩) R71291
theorem R47611 : Reach 47611 := rs (se 1 (by rfl) ⟨35708, by rfl⟩) R71417
theorem R113147 : Reach 113147 := rs (se 1 (by rfl) ⟨84860, by rfl⟩) R169721
theorem R47679 : Reach 47679 := rs (se 1 (by rfl) ⟨35759, by rfl⟩) R71519
theorem R47687 : Reach 47687 := rs (se 1 (by rfl) ⟨35765, by rfl⟩) R71531
theorem R113273 : Reach 113273 := rs (se 2 (by rfl) ⟨42477, by rfl⟩) R84955
theorem R113327 : Reach 113327 := rs (se 1 (by rfl) ⟨84995, by rfl⟩) R169991
theorem R47839 : Reach 47839 := rs (se 1 (by rfl) ⟨35879, by rfl⟩) R71759
theorem R113399 : Reach 113399 := rs (se 1 (by rfl) ⟨85049, by rfl⟩) R170099
theorem R47919 : Reach 47919 := rs (se 1 (by rfl) ⟨35939, by rfl⟩) R71879
theorem R932755 : Reach 932755 := rs (se 1 (by rfl) ⟨699566, by rfl⟩) R1399133
theorem R48027 : Reach 48027 := rs (se 1 (by rfl) ⟨36020, by rfl⟩) R72041
theorem R474011 : Reach 474011 := rs (se 1 (by rfl) ⟨355508, by rfl⟩) R711017
theorem R113579 : Reach 113579 := rs (se 1 (by rfl) ⟨85184, by rfl⟩) R170369
theorem R310189 : Reach 310189 := rs (se 3 (by rfl) ⟨58160, by rfl⟩) R116321
theorem R48079 : Reach 48079 := rs (se 1 (by rfl) ⟨36059, by rfl⟩) R72119
theorem R48103 : Reach 48103 := rs (se 1 (by rfl) ⟨36077, by rfl⟩) R72155
theorem R113651 : Reach 113651 := rs (se 1 (by rfl) ⟨85238, by rfl⟩) R170477
theorem R48415 : Reach 48415 := rs (se 1 (by rfl) ⟨36311, by rfl⟩) R72623
theorem R48475 : Reach 48475 := rs (se 1 (by rfl) ⟨36356, by rfl⟩) R72713
theorem R48495 : Reach 48495 := rs (se 1 (by rfl) ⟨36371, by rfl⟩) R72743
theorem R114043 : Reach 114043 := rs (se 1 (by rfl) ⟨85532, by rfl⟩) R171065
theorem R408995 : Reach 408995 := rs (se 1 (by rfl) ⟨306746, by rfl⟩) R613493
theorem R48551 : Reach 48551 := rs (se 1 (by rfl) ⟨36413, by rfl⟩) R72827
theorem R114119 : Reach 114119 := rs (se 1 (by rfl) ⟨85589, by rfl⟩) R171179
theorem R114169 : Reach 114169 := rs (se 2 (by rfl) ⟨42813, by rfl⟩) R85627
theorem R48635 : Reach 48635 := rs (se 1 (by rfl) ⟨36476, by rfl⟩) R72953
theorem R48703 : Reach 48703 := rs (se 1 (by rfl) ⟨36527, by rfl⟩) R73055
theorem R48711 : Reach 48711 := rs (se 1 (by rfl) ⟨36533, by rfl⟩) R73067
theorem R802493 : Reach 802493 := rs (se 3 (by rfl) ⟨150467, by rfl⟩) R300935
theorem R48863 : Reach 48863 := rs (se 1 (by rfl) ⟨36647, by rfl⟩) R73295
theorem R179975 : Reach 179975 := rs (se 1 (by rfl) ⟨134981, by rfl⟩) R269963
theorem R212777 : Reach 212777 := rs (se 2 (by rfl) ⟨79791, by rfl⟩) R159583
theorem R48943 : Reach 48943 := rs (se 1 (by rfl) ⟨36707, by rfl⟩) R73415
theorem R114479 : Reach 114479 := rs (se 1 (by rfl) ⟨85859, by rfl⟩) R171719
theorem R81719 : Reach 81719 := rs (se 1 (by rfl) ⟨61289, by rfl⟩) R122579
theorem R376649 : Reach 376649 := rs (se 2 (by rfl) ⟨141243, by rfl⟩) R282487
theorem R606041 : Reach 606041 := rs (se 2 (by rfl) ⟨227265, by rfl⟩) R454531
theorem R147329 : Reach 147329 := rs (se 2 (by rfl) ⟨55248, by rfl⟩) R110497
theorem R49051 : Reach 49051 := rs (se 1 (by rfl) ⟨36788, by rfl⟩) R73577
theorem R49103 : Reach 49103 := rs (se 1 (by rfl) ⟨36827, by rfl⟩) R73655
theorem R49127 : Reach 49127 := rs (se 1 (by rfl) ⟨36845, by rfl⟩) R73691
theorem R114713 : Reach 114713 := rs (se 2 (by rfl) ⟨43017, by rfl⟩) R86035
theorem R49439 : Reach 49439 := rs (se 1 (by rfl) ⟨37079, by rfl⟩) R74159
theorem R49499 : Reach 49499 := rs (se 1 (by rfl) ⟨37124, by rfl⟩) R74249
theorem R49519 : Reach 49519 := rs (se 1 (by rfl) ⟨37139, by rfl⟩) R74279
theorem R82343 : Reach 82343 := rs (se 1 (by rfl) ⟨61757, by rfl⟩) R123515
theorem R49575 : Reach 49575 := rs (se 1 (by rfl) ⟨37181, by rfl⟩) R74363
theorem R49659 : Reach 49659 := rs (se 1 (by rfl) ⟨37244, by rfl⟩) R74489
theorem R49727 : Reach 49727 := rs (se 1 (by rfl) ⟨37295, by rfl⟩) R74591
theorem R49735 : Reach 49735 := rs (se 1 (by rfl) ⟨37301, by rfl⟩) R74603
theorem R115273 : Reach 115273 := rs (se 2 (by rfl) ⟨43227, by rfl⟩) R86455
theorem R82505 : Reach 82505 := rs (se 2 (by rfl) ⟨30939, by rfl⟩) R61879
theorem R49759 : Reach 49759 := rs (se 1 (by rfl) ⟨37319, by rfl⟩) R74639
theorem R49839 : Reach 49839 := rs (se 1 (by rfl) ⟨37379, by rfl⟩) R74759
theorem R49887 : Reach 49887 := rs (se 1 (by rfl) ⟨37415, by rfl⟩) R74831
theorem R49967 : Reach 49967 := rs (se 1 (by rfl) ⟨37475, by rfl⟩) R74951
theorem R49999 : Reach 49999 := rs (se 1 (by rfl) ⟨37499, by rfl⟩) R74999
theorem R50075 : Reach 50075 := rs (se 1 (by rfl) ⟨37556, by rfl⟩) R75113
theorem R181187 : Reach 181187 := rs (se 1 (by rfl) ⟨135890, by rfl⟩) R271781
theorem R50127 : Reach 50127 := rs (se 1 (by rfl) ⟨37595, by rfl⟩) R75191
theorem R50151 : Reach 50151 := rs (se 1 (by rfl) ⟨37613, by rfl⟩) R75227
theorem R50395 : Reach 50395 := rs (se 1 (by rfl) ⟨37796, by rfl⟩) R75593
theorem R50463 : Reach 50463 := rs (se 1 (by rfl) ⟨37847, by rfl⟩) R75695
theorem R50471 : Reach 50471 := rs (se 1 (by rfl) ⟨37853, by rfl⟩) R75707
theorem R50523 : Reach 50523 := rs (se 1 (by rfl) ⟨37892, by rfl⟩) R75785
theorem R50543 : Reach 50543 := rs (se 1 (by rfl) ⟨37907, by rfl⟩) R75815
theorem R50555 : Reach 50555 := rs (se 1 (by rfl) ⟨37916, by rfl⟩) R75833
theorem R50599 : Reach 50599 := rs (se 1 (by rfl) ⟨37949, by rfl⟩) R75899
theorem R50631 : Reach 50631 := rs (se 1 (by rfl) ⟨37973, by rfl⟩) R75947
theorem R50683 : Reach 50683 := rs (se 1 (by rfl) ⟨38012, by rfl⟩) R76025
theorem R280097 : Reach 280097 := rs (se 2 (by rfl) ⟨105036, by rfl⟩) R210073
theorem R50751 : Reach 50751 := rs (se 1 (by rfl) ⟨38063, by rfl⟩) R76127
theorem R50759 : Reach 50759 := rs (se 1 (by rfl) ⟨38069, by rfl⟩) R76139
theorem R83551 : Reach 83551 := rs (se 1 (by rfl) ⟨62663, by rfl⟩) R125327
theorem R50783 : Reach 50783 := rs (se 1 (by rfl) ⟨38087, by rfl⟩) R76175
theorem R50863 : Reach 50863 := rs (se 1 (by rfl) ⟨38147, by rfl⟩) R76295
theorem R50911 : Reach 50911 := rs (se 1 (by rfl) ⟨38183, by rfl⟩) R76367
theorem R50991 : Reach 50991 := rs (se 1 (by rfl) ⟨38243, by rfl⟩) R76487
theorem R83767 : Reach 83767 := rs (se 1 (by rfl) ⟨62825, by rfl⟩) R125651
theorem R51023 : Reach 51023 := rs (se 1 (by rfl) ⟨38267, by rfl⟩) R76535
theorem R51099 : Reach 51099 := rs (se 1 (by rfl) ⟨38324, by rfl⟩) R76649
theorem R1460429 : Reach 1460429 := rs (se 3 (by rfl) ⟨273830, by rfl⟩) R547661
theorem R84233 : Reach 84233 := rs (se 2 (by rfl) ⟨31587, by rfl⟩) R63175
theorem R84449 : Reach 84449 := rs (se 2 (by rfl) ⟨31668, by rfl⟩) R63337
theorem R444901 : Reach 444901 := rs (se 4 (by rfl) ⟨41709, by rfl⟩) R83419
theorem R182857 : Reach 182857 := rs (se 2 (by rfl) ⟨68571, by rfl⟩) R137143
theorem R150443 : Reach 150443 := rs (se 1 (by rfl) ⟨112832, by rfl⟩) R225665
theorem R216103 : Reach 216103 := rs (se 1 (by rfl) ⟨162077, by rfl⟩) R324155
theorem R85225 : Reach 85225 := rs (se 2 (by rfl) ⟨31959, by rfl⟩) R63919
theorem R609551 : Reach 609551 := rs (se 1 (by rfl) ⟨457163, by rfl⟩) R914327
theorem R85279 : Reach 85279 := rs (se 1 (by rfl) ⟨63959, by rfl⟩) R127919
theorem R249155 : Reach 249155 := rs (se 1 (by rfl) ⟨186866, by rfl⟩) R373733
theorem R478817 : Reach 478817 := rs (se 2 (by rfl) ⟨179556, by rfl⟩) R359113
theorem R85691 : Reach 85691 := rs (se 1 (by rfl) ⟨64268, by rfl⟩) R128537
theorem R347915 : Reach 347915 := rs (se 1 (by rfl) ⟨260936, by rfl⟩) R521873
theorem R249641 : Reach 249641 := rs (se 2 (by rfl) ⟨93615, by rfl⟩) R187231
theorem R86383 : Reach 86383 := rs (se 1 (by rfl) ⟨64787, by rfl⟩) R129575
theorem R479621 : Reach 479621 := rs (se 4 (by rfl) ⟨44964, by rfl⟩) R89929
theorem R53671 : Reach 53671 := rs (se 1 (by rfl) ⟨40253, by rfl⟩) R80507
theorem R184801 : Reach 184801 := rs (se 2 (by rfl) ⟨69300, by rfl⟩) R138601
theorem R54247 : Reach 54247 := rs (se 1 (by rfl) ⟨40685, by rfl⟩) R81371
theorem R250937 : Reach 250937 := rs (se 2 (by rfl) ⟨94101, by rfl⟩) R188203
theorem R119951 : Reach 119951 := rs (se 1 (by rfl) ⟨89963, by rfl⟩) R179927
theorem R283943 : Reach 283943 := rs (se 1 (by rfl) ⟨212957, by rfl⟩) R425915
theorem R120251 : Reach 120251 := rs (se 1 (by rfl) ⟨90188, by rfl⟩) R180377
theorem R480775 : Reach 480775 := rs (se 1 (by rfl) ⟨360581, by rfl⟩) R721163
theorem R284471 : Reach 284471 := rs (se 1 (by rfl) ⟨213353, by rfl⟩) R426707
theorem R939863 : Reach 939863 := rs (se 1 (by rfl) ⟨704897, by rfl⟩) R1409795
theorem R809189 : Reach 809189 := rs (se 4 (by rfl) ⟨75861, by rfl⟩) R151723
theorem R973079 : Reach 973079 := rs (se 1 (by rfl) ⟨729809, by rfl⟩) R1459619
theorem R55903 : Reach 55903 := rs (se 1 (by rfl) ⟨41927, by rfl⟩) R83855
theorem R56119 : Reach 56119 := rs (se 1 (by rfl) ⟨42089, by rfl⟩) R84179
theorem R121895 : Reach 121895 := rs (se 1 (by rfl) ⟨91421, by rfl⟩) R182843
theorem R253043 : Reach 253043 := rs (se 1 (by rfl) ⟨189782, by rfl⟩) R379565
theorem R220477 : Reach 220477 := rs (se 3 (by rfl) ⟨41339, by rfl⟩) R82679
theorem R122249 : Reach 122249 := rs (se 2 (by rfl) ⟨45843, by rfl⟩) R91687
theorem R57055 : Reach 57055 := rs (se 1 (by rfl) ⟨42791, by rfl⟩) R85583
theorem R89903 : Reach 89903 := rs (se 1 (by rfl) ⟨67427, by rfl⟩) R134855
theorem R253853 : Reach 253853 := rs (se 3 (by rfl) ⟨47597, by rfl⟩) R95195
theorem R319697 : Reach 319697 := rs (se 2 (by rfl) ⟨119886, by rfl⟩) R239773
theorem R516577 : Reach 516577 := rs (se 2 (by rfl) ⟨193716, by rfl⟩) R387433
theorem R385607 : Reach 385607 := rs (se 1 (by rfl) ⟨289205, by rfl⟩) R578411
theorem R221867 : Reach 221867 := rs (se 1 (by rfl) ⟨166400, by rfl⟩) R332801
theorem R254663 : Reach 254663 := rs (se 1 (by rfl) ⟨190997, by rfl⟩) R381995
theorem R123727 : Reach 123727 := rs (se 1 (by rfl) ⟨92795, by rfl⟩) R185591
theorem R124001 : Reach 124001 := rs (se 2 (by rfl) ⟨46500, by rfl⟩) R93001
theorem R124375 : Reach 124375 := rs (se 1 (by rfl) ⟨93281, by rfl⟩) R186563
theorem R124679 : Reach 124679 := rs (se 1 (by rfl) ⟨93509, by rfl⟩) R187019
theorem R91945 : Reach 91945 := rs (se 2 (by rfl) ⟨34479, by rfl⟩) R68959
theorem R288593 : Reach 288593 := rs (se 2 (by rfl) ⟨108222, by rfl⟩) R216445
theorem R125459 : Reach 125459 := rs (se 1 (by rfl) ⟨94094, by rfl⟩) R188189
theorem R92735 : Reach 92735 := rs (se 1 (by rfl) ⟨69551, by rfl⟩) R139103
theorem R289403 : Reach 289403 := rs (se 1 (by rfl) ⟨217052, by rfl⟩) R434105
theorem R60367 : Reach 60367 := rs (se 1 (by rfl) ⟨45275, by rfl⟩) R90551
theorem R93403 : Reach 93403 := rs (se 1 (by rfl) ⟨70052, by rfl⟩) R140105
theorem R257417 : Reach 257417 := rs (se 2 (by rfl) ⟨96531, by rfl⟩) R193063
theorem R159191 : Reach 159191 := rs (se 1 (by rfl) ⟨119393, by rfl⟩) R238787
theorem R93791 : Reach 93791 := rs (se 1 (by rfl) ⟨70343, by rfl⟩) R140687
theorem R1175233 : Reach 1175233 := rs (se 2 (by rfl) ⟨440712, by rfl⟩) R881425
theorem R1928933 : Reach 1928933 := rs (se 4 (by rfl) ⟨180837, by rfl⟩) R361675
theorem R61231 : Reach 61231 := rs (se 1 (by rfl) ⟨45923, by rfl⟩) R91847
theorem R159617 : Reach 159617 := rs (se 2 (by rfl) ⟨59856, by rfl⟩) R119713
theorem R421955 : Reach 421955 := rs (se 1 (by rfl) ⟨316466, by rfl⟩) R632933
theorem R127241 : Reach 127241 := rs (se 2 (by rfl) ⟨47715, by rfl⟩) R95431
theorem R618785 : Reach 618785 := rs (se 2 (by rfl) ⟨232044, by rfl⟩) R464089
theorem R455017 : Reach 455017 := rs (se 2 (by rfl) ⟨170631, by rfl⟩) R341263
theorem R684395 : Reach 684395 := rs (se 1 (by rfl) ⟨513296, by rfl⟩) R1026593
theorem R127457 : Reach 127457 := rs (se 2 (by rfl) ⟨47796, by rfl⟩) R95593
theorem R127595 : Reach 127595 := rs (se 1 (by rfl) ⟨95696, by rfl⟩) R191393
theorem R258713 : Reach 258713 := rs (se 2 (by rfl) ⟨97017, by rfl⟩) R194035
theorem R258977 : Reach 258977 := rs (se 2 (by rfl) ⟨97116, by rfl⟩) R194233
theorem R717815 : Reach 717815 := rs (se 1 (by rfl) ⟨538361, by rfl⟩) R1076723
theorem R1635329 : Reach 1635329 := rs (se 2 (by rfl) ⟨613248, by rfl⟩) R1226497
theorem R160865 : Reach 160865 := rs (se 2 (by rfl) ⟨60324, by rfl⟩) R120649
theorem R95375 : Reach 95375 := rs (se 1 (by rfl) ⟨71531, by rfl⟩) R143063
theorem R128243 : Reach 128243 := rs (se 1 (by rfl) ⟨96182, by rfl⟩) R192365
theorem R128699 : Reach 128699 := rs (se 1 (by rfl) ⟨96524, by rfl⟩) R193049
theorem R358199 : Reach 358199 := rs (se 1 (by rfl) ⟨268649, by rfl⟩) R537299
theorem R129235 : Reach 129235 := rs (se 1 (by rfl) ⟨96926, by rfl⟩) R193853
theorem R96623 : Reach 96623 := rs (se 1 (by rfl) ⟨72467, by rfl⟩) R144935
theorem R162215 : Reach 162215 := rs (se 1 (by rfl) ⟨121661, by rfl⟩) R243323
theorem R2587085 : Reach 2587085 := rs (se 3 (by rfl) ⟨485078, by rfl⟩) R970157
theorem R490009 : Reach 490009 := rs (se 2 (by rfl) ⟨183753, by rfl⟩) R367507
theorem R162377 : Reach 162377 := rs (se 2 (by rfl) ⟨60891, by rfl⟩) R121783
theorem R96889 : Reach 96889 := rs (se 2 (by rfl) ⟨36333, by rfl⟩) R72667
theorem R196177 : Reach 196177 := rs (se 2 (by rfl) ⟨73566, by rfl⟩) R147133
theorem R983171 : Reach 983171 := rs (se 1 (by rfl) ⟨737378, by rfl⟩) R1474757
theorem R262607 : Reach 262607 := rs (se 1 (by rfl) ⟨196955, by rfl⟩) R393911
theorem R688769 : Reach 688769 := rs (se 2 (by rfl) ⟨258288, by rfl⟩) R516577
theorem R164969 : Reach 164969 := rs (se 2 (by rfl) ⟨61863, by rfl⟩) R123727
theorem R100295 : Reach 100295 := rs (se 1 (by rfl) ⟨75221, by rfl⟩) R150443
theorem R165833 : Reach 165833 := rs (se 2 (by rfl) ⟨62187, by rfl⟩) R124375
theorem R67567 : Reach 67567 := rs (se 1 (by rfl) ⟨50675, by rfl⟩) R101351
theorem R133111 : Reach 133111 := rs (se 1 (by rfl) ⟨99833, by rfl⟩) R199667
theorem R166103 : Reach 166103 := rs (se 1 (by rfl) ⟨124577, by rfl⟩) R249155
theorem R231943 : Reach 231943 := rs (se 1 (by rfl) ⟨173957, by rfl⟩) R347915
theorem R166427 : Reach 166427 := rs (se 1 (by rfl) ⟨124820, by rfl⟩) R249641
theorem R298013 : Reach 298013 := rs (se 3 (by rfl) ⟨55877, by rfl⟩) R111755
theorem R593201 : Reach 593201 := rs (se 2 (by rfl) ⟨222450, by rfl⟩) R444901
theorem R462131 : Reach 462131 := rs (se 1 (by rfl) ⟨346598, by rfl⟩) R693197
theorem R167291 : Reach 167291 := rs (se 1 (by rfl) ⟨125468, by rfl⟩) R250937
theorem R757181 : Reach 757181 := rs (se 3 (by rfl) ⟨141971, by rfl⟩) R283943
theorem R134729 : Reach 134729 := rs (se 2 (by rfl) ⟨50523, by rfl⟩) R101047
theorem R462419 : Reach 462419 := rs (se 1 (by rfl) ⟨346814, by rfl⟩) R693629
theorem R626575 : Reach 626575 := rs (se 1 (by rfl) ⟨469931, by rfl⟩) R939863
theorem R70087 : Reach 70087 := rs (se 1 (by rfl) ⟨52565, by rfl⟩) R105131
theorem R266935 : Reach 266935 := rs (se 1 (by rfl) ⟨200201, by rfl⟩) R400403
theorem R168695 : Reach 168695 := rs (se 1 (by rfl) ⟨126521, by rfl⟩) R253043
theorem R136187 : Reach 136187 := rs (se 1 (by rfl) ⟨102140, by rfl⟩) R204281
theorem R267259 : Reach 267259 := rs (se 1 (by rfl) ⟨200444, by rfl⟩) R400889
theorem R234505 : Reach 234505 := rs (se 2 (by rfl) ⟨87939, by rfl⟩) R175879
theorem R136255 : Reach 136255 := rs (se 1 (by rfl) ⟨102191, by rfl⟩) R204383
theorem R70763 : Reach 70763 := rs (se 1 (by rfl) ⟨53072, by rfl⟩) R106145
theorem R169235 : Reach 169235 := rs (se 1 (by rfl) ⟨126926, by rfl⟩) R253853
theorem R71003 : Reach 71003 := rs (se 1 (by rfl) ⟨53252, by rfl⟩) R106505
theorem R71279 : Reach 71279 := rs (se 1 (by rfl) ⟨53459, by rfl⟩) R106919
theorem R71351 : Reach 71351 := rs (se 1 (by rfl) ⟨53513, by rfl⟩) R107027
theorem R71387 : Reach 71387 := rs (se 1 (by rfl) ⟨53540, by rfl⟩) R107081
theorem R169775 : Reach 169775 := rs (se 1 (by rfl) ⟨127331, by rfl⟩) R254663
theorem R71561 : Reach 71561 := rs (se 2 (by rfl) ⟨26835, by rfl⟩) R53671
theorem R71663 : Reach 71663 := rs (se 1 (by rfl) ⟨53747, by rfl⟩) R107495
theorem R137371 : Reach 137371 := rs (se 1 (by rfl) ⟨103028, by rfl⟩) R206057
theorem R104609 : Reach 104609 := rs (se 2 (by rfl) ⟨39228, by rfl⟩) R78457
theorem R71915 : Reach 71915 := rs (se 1 (by rfl) ⟨53936, by rfl⟩) R107873
theorem R71975 : Reach 71975 := rs (se 1 (by rfl) ⟨53981, by rfl⟩) R107963
theorem R530729 : Reach 530729 := rs (se 2 (by rfl) ⟨199023, by rfl⟩) R398047
theorem R72059 : Reach 72059 := rs (se 1 (by rfl) ⟨54044, by rfl⟩) R108089
theorem R72329 : Reach 72329 := rs (se 2 (by rfl) ⟨27123, by rfl⟩) R54247
theorem R72503 : Reach 72503 := rs (se 1 (by rfl) ⟨54377, by rfl⟩) R108755
theorem R72539 : Reach 72539 := rs (se 1 (by rfl) ⟨54404, by rfl⟩) R108809
theorem R72683 : Reach 72683 := rs (se 1 (by rfl) ⟨54512, by rfl⟩) R109025
theorem R72775 : Reach 72775 := rs (se 1 (by rfl) ⟨54581, by rfl⟩) R109163
theorem R72887 : Reach 72887 := rs (se 1 (by rfl) ⟨54665, by rfl⟩) R109331
theorem R4300121 : Reach 4300121 := rs (se 2 (by rfl) ⟨1612545, by rfl⟩) R3225091
theorem R73127 : Reach 73127 := rs (se 1 (by rfl) ⟨54845, by rfl⟩) R109691
theorem R73211 : Reach 73211 := rs (se 1 (by rfl) ⟨54908, by rfl⟩) R109817
theorem R73307 : Reach 73307 := rs (se 1 (by rfl) ⟨54980, by rfl⟩) R109961
theorem R171611 : Reach 171611 := rs (se 1 (by rfl) ⟨128708, by rfl⟩) R257417
theorem R106127 : Reach 106127 := rs (se 1 (by rfl) ⟨79595, by rfl⟩) R159191
theorem R73391 : Reach 73391 := rs (se 1 (by rfl) ⟨55043, by rfl⟩) R110087
theorem R106217 : Reach 106217 := rs (se 2 (by rfl) ⟨39831, by rfl⟩) R79663
theorem R73511 : Reach 73511 := rs (se 1 (by rfl) ⟨55133, by rfl⟩) R110267
theorem R1285955 : Reach 1285955 := rs (se 1 (by rfl) ⟨964466, by rfl⟩) R1928933
theorem R73543 : Reach 73543 := rs (se 1 (by rfl) ⟨55157, by rfl⟩) R110315
theorem R73595 : Reach 73595 := rs (se 1 (by rfl) ⟨55196, by rfl⟩) R110393
theorem R172313 : Reach 172313 := rs (se 2 (by rfl) ⟨64617, by rfl⟩) R129235
theorem R74015 : Reach 74015 := rs (se 1 (by rfl) ⟨55511, by rfl⟩) R111023
theorem R74039 : Reach 74039 := rs (se 1 (by rfl) ⟨55529, by rfl⟩) R111059
theorem R74111 : Reach 74111 := rs (se 1 (by rfl) ⟨55583, by rfl⟩) R111167
theorem R172475 : Reach 172475 := rs (se 1 (by rfl) ⟨129356, by rfl⟩) R258713
theorem R74183 : Reach 74183 := rs (se 1 (by rfl) ⟨55637, by rfl⟩) R111275
theorem R172651 : Reach 172651 := rs (se 1 (by rfl) ⟨129488, by rfl⟩) R258977
theorem R1090219 : Reach 1090219 := rs (se 1 (by rfl) ⟨817664, by rfl⟩) R1635329
theorem R107243 : Reach 107243 := rs (se 1 (by rfl) ⟨80432, by rfl⟩) R160865
theorem R74537 : Reach 74537 := rs (se 2 (by rfl) ⟨27951, by rfl⟩) R55903
theorem R74543 : Reach 74543 := rs (se 1 (by rfl) ⟨55907, by rfl⟩) R111815
theorem R74663 : Reach 74663 := rs (se 1 (by rfl) ⟨55997, by rfl⟩) R111995
theorem R74747 : Reach 74747 := rs (se 1 (by rfl) ⟨56060, by rfl⟩) R112121
theorem R74807 : Reach 74807 := rs (se 1 (by rfl) ⟨56105, by rfl⟩) R112211
theorem R74825 : Reach 74825 := rs (se 2 (by rfl) ⟨28059, by rfl⟩) R56119
theorem R74927 : Reach 74927 := rs (se 1 (by rfl) ⟨56195, by rfl⟩) R112391
theorem R238799 : Reach 238799 := rs (se 1 (by rfl) ⟨179099, by rfl⟩) R358199
theorem R75179 : Reach 75179 := rs (se 1 (by rfl) ⟨56384, by rfl⟩) R112769
theorem R75335 : Reach 75335 := rs (se 1 (by rfl) ⟨56501, by rfl⟩) R113003
theorem R108143 : Reach 108143 := rs (se 1 (by rfl) ⟨81107, by rfl⟩) R162215
theorem R75431 : Reach 75431 := rs (se 1 (by rfl) ⟨56573, by rfl⟩) R113147
theorem R108251 : Reach 108251 := rs (se 1 (by rfl) ⟨81188, by rfl⟩) R162377
theorem R75515 : Reach 75515 := rs (se 1 (by rfl) ⟨56636, by rfl⟩) R113273
theorem R75551 : Reach 75551 := rs (se 1 (by rfl) ⟨56663, by rfl⟩) R113327
theorem R75599 : Reach 75599 := rs (se 1 (by rfl) ⟨56699, by rfl⟩) R113399
theorem R75719 : Reach 75719 := rs (se 1 (by rfl) ⟨56789, by rfl⟩) R113579
theorem R75767 : Reach 75767 := rs (se 1 (by rfl) ⟨56825, by rfl⟩) R113651
theorem R272663 : Reach 272663 := rs (se 1 (by rfl) ⟨204497, by rfl⟩) R408995
theorem R76073 : Reach 76073 := rs (se 2 (by rfl) ⟨28527, by rfl⟩) R57055
theorem R76079 : Reach 76079 := rs (se 1 (by rfl) ⟨57059, by rfl⟩) R114119
theorem R534995 : Reach 534995 := rs (se 1 (by rfl) ⟨401246, by rfl⟩) R802493
theorem R141851 : Reach 141851 := rs (se 1 (by rfl) ⟨106388, by rfl⟩) R212777
theorem R76319 : Reach 76319 := rs (se 1 (by rfl) ⟨57239, by rfl⟩) R114479
theorem R404027 : Reach 404027 := rs (se 1 (by rfl) ⟨303020, by rfl⟩) R606041
theorem R76475 : Reach 76475 := rs (se 1 (by rfl) ⟨57356, by rfl⟩) R114713
theorem R109367 : Reach 109367 := rs (se 1 (by rfl) ⟨82025, by rfl⟩) R164051
theorem R306139 : Reach 306139 := rs (se 1 (by rfl) ⟨229604, by rfl⟩) R459209
theorem R109547 : Reach 109547 := rs (se 1 (by rfl) ⟨82160, by rfl⟩) R164321
theorem R568619 : Reach 568619 := rs (se 1 (by rfl) ⟨426464, by rfl⟩) R852929
theorem R175679 : Reach 175679 := rs (se 1 (by rfl) ⟨131759, by rfl⟩) R263519
theorem R110375 : Reach 110375 := rs (se 1 (by rfl) ⟨82781, by rfl⟩) R165563
theorem R1028285 : Reach 1028285 := rs (se 3 (by rfl) ⟨192803, by rfl⟩) R385607
theorem R274697 : Reach 274697 := rs (se 2 (by rfl) ⟨103011, by rfl⟩) R206023
theorem R307547 : Reach 307547 := rs (se 1 (by rfl) ⟨230660, by rfl⟩) R461321
theorem R111401 : Reach 111401 := rs (se 2 (by rfl) ⟨41775, by rfl⟩) R83551
theorem R406367 : Reach 406367 := rs (se 1 (by rfl) ⟨304775, by rfl⟩) R609551
theorem R111671 : Reach 111671 := rs (se 1 (by rfl) ⟨83753, by rfl⟩) R167507
theorem R111689 : Reach 111689 := rs (se 2 (by rfl) ⟨41883, by rfl⟩) R83767
theorem R242963 : Reach 242963 := rs (se 1 (by rfl) ⟨182222, by rfl⟩) R364445
theorem R309187 : Reach 309187 := rs (se 1 (by rfl) ⟨231890, by rfl⟩) R463781
theorem R276473 : Reach 276473 := rs (se 2 (by rfl) ⟨103677, by rfl⟩) R207355
theorem R79967 : Reach 79967 := rs (se 1 (by rfl) ⟨59975, by rfl⟩) R119951
theorem R243809 : Reach 243809 := rs (se 2 (by rfl) ⟨91428, by rfl⟩) R182857
theorem R47259 : Reach 47259 := rs (se 1 (by rfl) ⟨35444, by rfl⟩) R70889
theorem R47295 : Reach 47295 := rs (se 1 (by rfl) ⟨35471, by rfl⟩) R70943
theorem R243971 : Reach 243971 := rs (se 1 (by rfl) ⟨182978, by rfl⟩) R365957
theorem R47407 : Reach 47407 := rs (se 1 (by rfl) ⟨35555, by rfl⟩) R71111
theorem R47643 : Reach 47643 := rs (se 1 (by rfl) ⟨35732, by rfl⟩) R71465
theorem R47647 : Reach 47647 := rs (se 1 (by rfl) ⟨35735, by rfl⟩) R71471
theorem R80489 : Reach 80489 := rs (se 2 (by rfl) ⟨30183, by rfl⟩) R60367
theorem R277181 : Reach 277181 := rs (se 3 (by rfl) ⟨51971, by rfl⟩) R103943
theorem R539459 : Reach 539459 := rs (se 1 (by rfl) ⟨404594, by rfl⟩) R809189
theorem R1850201 : Reach 1850201 := rs (se 2 (by rfl) ⟨693825, by rfl⟩) R1387651
theorem R47963 : Reach 47963 := rs (se 1 (by rfl) ⟨35972, by rfl⟩) R71945
theorem R48031 : Reach 48031 := rs (se 1 (by rfl) ⟨36023, by rfl⟩) R72047
theorem R113615 : Reach 113615 := rs (se 1 (by rfl) ⟨85211, by rfl⟩) R170423
theorem R113633 : Reach 113633 := rs (se 2 (by rfl) ⟨42612, by rfl⟩) R85225
theorem R113705 : Reach 113705 := rs (se 2 (by rfl) ⟨42639, by rfl⟩) R85279
theorem R48175 : Reach 48175 := rs (se 1 (by rfl) ⟨36131, by rfl⟩) R72263
theorem R48199 : Reach 48199 := rs (se 1 (by rfl) ⟨36149, by rfl⟩) R72299
theorem R244919 : Reach 244919 := rs (se 1 (by rfl) ⟨183689, by rfl⟩) R367379
theorem R48351 : Reach 48351 := rs (se 1 (by rfl) ⟨36263, by rfl⟩) R72527
theorem R81263 : Reach 81263 := rs (se 1 (by rfl) ⟨60947, by rfl⟩) R121895
theorem R48615 : Reach 48615 := rs (se 1 (by rfl) ⟨36461, by rfl⟩) R72923
theorem R81499 : Reach 81499 := rs (se 1 (by rfl) ⟨61124, by rfl⟩) R122249
theorem R48731 : Reach 48731 := rs (se 1 (by rfl) ⟨36548, by rfl⟩) R73097
theorem R81641 : Reach 81641 := rs (se 2 (by rfl) ⟨30615, by rfl⟩) R61231
theorem R48967 : Reach 48967 := rs (se 1 (by rfl) ⟨36725, by rfl⟩) R73451
theorem R245591 : Reach 245591 := rs (se 1 (by rfl) ⟨184193, by rfl⟩) R368387
theorem R49119 : Reach 49119 := rs (se 1 (by rfl) ⟨36839, by rfl⟩) R73679
theorem R213131 : Reach 213131 := rs (se 1 (by rfl) ⟨159848, by rfl⟩) R319697
theorem R49383 : Reach 49383 := rs (se 1 (by rfl) ⟨37037, by rfl⟩) R74075
theorem R49535 : Reach 49535 := rs (se 1 (by rfl) ⟨37151, by rfl⟩) R74303
theorem R147911 : Reach 147911 := rs (se 1 (by rfl) ⟨110933, by rfl⟩) R221867
theorem R49615 : Reach 49615 := rs (se 1 (by rfl) ⟨37211, by rfl⟩) R74423
theorem R606689 : Reach 606689 := rs (se 2 (by rfl) ⟨227508, by rfl⟩) R455017
theorem R115177 : Reach 115177 := rs (se 2 (by rfl) ⟨43191, by rfl⟩) R86383
theorem R180731 : Reach 180731 := rs (se 1 (by rfl) ⟨135548, by rfl⟩) R271097
theorem R49767 : Reach 49767 := rs (se 1 (by rfl) ⟨37325, by rfl⟩) R74651
theorem R246401 : Reach 246401 := rs (se 2 (by rfl) ⟨92400, by rfl⟩) R184801
theorem R82667 : Reach 82667 := rs (se 1 (by rfl) ⟨62000, by rfl⟩) R124001
theorem R50031 : Reach 50031 := rs (se 1 (by rfl) ⟨37523, by rfl⟩) R75047
theorem R50087 : Reach 50087 := rs (se 1 (by rfl) ⟨37565, by rfl⟩) R75131
theorem R50171 : Reach 50171 := rs (se 1 (by rfl) ⟨37628, by rfl⟩) R75257
theorem R50239 : Reach 50239 := rs (se 1 (by rfl) ⟨37679, by rfl⟩) R75359
theorem R83119 : Reach 83119 := rs (se 1 (by rfl) ⟨62339, by rfl⟩) R124679
theorem R50351 : Reach 50351 := rs (se 1 (by rfl) ⟨37763, by rfl⟩) R75527
theorem R50383 : Reach 50383 := rs (se 1 (by rfl) ⟨37787, by rfl⟩) R75575
theorem R50587 : Reach 50587 := rs (se 1 (by rfl) ⟨37940, by rfl⟩) R75881
theorem R247211 : Reach 247211 := rs (se 1 (by rfl) ⟨185408, by rfl⟩) R370817
theorem R181871 : Reach 181871 := rs (se 1 (by rfl) ⟨136403, by rfl⟩) R272807
theorem R50799 : Reach 50799 := rs (se 1 (by rfl) ⟨38099, by rfl⟩) R76199
theorem R50855 : Reach 50855 := rs (se 1 (by rfl) ⟨38141, by rfl⟩) R76283
theorem R83639 : Reach 83639 := rs (se 1 (by rfl) ⟨62729, by rfl⟩) R125459
theorem R50907 : Reach 50907 := rs (se 1 (by rfl) ⟨38180, by rfl⟩) R76361
theorem R50939 : Reach 50939 := rs (se 1 (by rfl) ⟨38204, by rfl⟩) R76409
theorem R50975 : Reach 50975 := rs (se 1 (by rfl) ⟨38231, by rfl⟩) R76463
theorem R51007 : Reach 51007 := rs (se 1 (by rfl) ⟨38255, by rfl⟩) R76511
theorem R641033 : Reach 641033 := rs (se 2 (by rfl) ⟨240387, by rfl⟩) R480775
theorem R247859 : Reach 247859 := rs (se 1 (by rfl) ⟨185894, by rfl⟩) R371789
theorem R51391 : Reach 51391 := rs (se 1 (by rfl) ⟨38543, by rfl⟩) R77087
theorem R248507 : Reach 248507 := rs (se 1 (by rfl) ⟨186380, by rfl⟩) R372761
theorem R281303 : Reach 281303 := rs (se 1 (by rfl) ⟨210977, by rfl⟩) R421955
theorem R84827 : Reach 84827 := rs (se 1 (by rfl) ⟨63620, by rfl⟩) R127241
theorem R412523 : Reach 412523 := rs (se 1 (by rfl) ⟨309392, by rfl⟩) R618785
theorem R84971 : Reach 84971 := rs (se 1 (by rfl) ⟨63728, by rfl⟩) R127457
theorem R117739 : Reach 117739 := rs (se 1 (by rfl) ⟨88304, by rfl⟩) R176609
theorem R183329 : Reach 183329 := rs (se 2 (by rfl) ⟨68748, by rfl⟩) R137497
theorem R85063 : Reach 85063 := rs (se 1 (by rfl) ⟨63797, by rfl⟩) R127595
theorem R478543 : Reach 478543 := rs (se 1 (by rfl) ⟨358907, by rfl⟩) R717815
theorem R85495 : Reach 85495 := rs (se 1 (by rfl) ⟨64121, by rfl⟩) R128243
theorem R249479 : Reach 249479 := rs (se 1 (by rfl) ⟨187109, by rfl⟩) R374219
theorem R184103 : Reach 184103 := rs (se 1 (by rfl) ⟨138077, by rfl⟩) R276155
theorem R85799 : Reach 85799 := rs (se 1 (by rfl) ⟨64349, by rfl⟩) R128699
theorem R413585 : Reach 413585 := rs (se 2 (by rfl) ⟨155094, by rfl⟩) R310189
theorem R184301 : Reach 184301 := rs (se 3 (by rfl) ⟨34556, by rfl⟩) R69113
theorem R53479 : Reach 53479 := rs (se 1 (by rfl) ⟨40109, by rfl⟩) R80219
theorem R1724723 : Reach 1724723 := rs (se 1 (by rfl) ⟨1293542, by rfl⟩) R2587085
theorem R152057 : Reach 152057 := rs (se 2 (by rfl) ⟨57021, by rfl⟩) R114043
theorem R316007 : Reach 316007 := rs (se 1 (by rfl) ⟨237005, by rfl⟩) R474011
theorem R152225 : Reach 152225 := rs (se 2 (by rfl) ⟨57084, by rfl⟩) R114169
theorem R479933 : Reach 479933 := rs (se 3 (by rfl) ⟨89987, by rfl⟩) R179975
theorem R54479 : Reach 54479 := rs (se 1 (by rfl) ⟨40859, by rfl⟩) R81719
theorem R251099 : Reach 251099 := rs (se 1 (by rfl) ⟨188324, by rfl⟩) R376649
theorem R87623 : Reach 87623 := rs (se 1 (by rfl) ⟨65717, by rfl⟩) R131435
theorem R54895 : Reach 54895 := rs (se 1 (by rfl) ⟨41171, by rfl⟩) R82343
theorem R55003 : Reach 55003 := rs (se 1 (by rfl) ⟨41252, by rfl⟩) R82505
theorem R907037 : Reach 907037 := rs (se 3 (by rfl) ⟨170069, by rfl⟩) R340139
theorem R120791 : Reach 120791 := rs (se 1 (by rfl) ⟨90593, by rfl⟩) R181187
theorem R186731 : Reach 186731 := rs (se 1 (by rfl) ⟨140048, by rfl⟩) R280097
theorem R973619 : Reach 973619 := rs (se 1 (by rfl) ⟨730214, by rfl⟩) R1460429
theorem R187217 : Reach 187217 := rs (se 2 (by rfl) ⟨70206, by rfl⟩) R140413
theorem R56155 : Reach 56155 := rs (se 1 (by rfl) ⟨42116, by rfl⟩) R84233
theorem R56299 : Reach 56299 := rs (se 1 (by rfl) ⟨42224, by rfl⟩) R84449
theorem R285677 : Reach 285677 := rs (se 3 (by rfl) ⟨53564, by rfl⟩) R107129
theorem R1530899 : Reach 1530899 := rs (se 1 (by rfl) ⟨1148174, by rfl⟩) R2296349
theorem R482507 : Reach 482507 := rs (se 1 (by rfl) ⟨361880, by rfl⟩) R723761
theorem R7625933 : Reach 7625933 := rs (se 3 (by rfl) ⟨1429862, by rfl⟩) R2859725
theorem R154991 : Reach 154991 := rs (se 1 (by rfl) ⟨116243, by rfl⟩) R232487
theorem R89743 : Reach 89743 := rs (se 1 (by rfl) ⟨67307, by rfl⟩) R134615
theorem R122593 : Reach 122593 := rs (se 2 (by rfl) ⟨45972, by rfl⟩) R91945
theorem R319211 : Reach 319211 := rs (se 1 (by rfl) ⟨239408, by rfl⟩) R478817
theorem R11951887 : Reach 11951887 := rs (se 1 (by rfl) ⟨8963915, by rfl⟩) R17927831
theorem R57127 : Reach 57127 := rs (se 1 (by rfl) ⟨42845, by rfl⟩) R85691
theorem R286621 : Reach 286621 := rs (se 3 (by rfl) ⟨53741, by rfl⟩) R107483
theorem R319747 : Reach 319747 := rs (se 1 (by rfl) ⟨239810, by rfl⟩) R479621
theorem R614789 : Reach 614789 := rs (se 4 (by rfl) ⟨57636, by rfl⟩) R115273
theorem R320669 : Reach 320669 := rs (se 3 (by rfl) ⟨60125, by rfl⟩) R120251
theorem R189647 : Reach 189647 := rs (se 1 (by rfl) ⟨142235, by rfl⟩) R284471
theorem R288137 : Reach 288137 := rs (se 2 (by rfl) ⟨108051, by rfl⟩) R216103
theorem R648719 : Reach 648719 := rs (se 1 (by rfl) ⟨486539, by rfl⟩) R973079
theorem R124537 : Reach 124537 := rs (se 2 (by rfl) ⟨46701, by rfl⟩) R93403
theorem R354449 : Reach 354449 := rs (se 2 (by rfl) ⟨132918, by rfl⟩) R265837
theorem R1566977 : Reach 1566977 := rs (se 2 (by rfl) ⟨587616, by rfl⟩) R1175233
theorem R59935 : Reach 59935 := rs (se 1 (by rfl) ⟨44951, by rfl⟩) R89903
theorem R1272833 : Reach 1272833 := rs (se 2 (by rfl) ⟨477312, by rfl⟩) R954625
theorem R93305 : Reach 93305 := rs (se 2 (by rfl) ⟨34989, by rfl⟩) R69979
theorem R323129 : Reach 323129 := rs (se 2 (by rfl) ⟨121173, by rfl⟩) R242347
theorem R159407 : Reach 159407 := rs (se 1 (by rfl) ⟨119555, by rfl⟩) R239111
theorem R290621 : Reach 290621 := rs (se 3 (by rfl) ⟨54491, by rfl⟩) R108983
theorem R192395 : Reach 192395 := rs (se 1 (by rfl) ⟨144296, by rfl⟩) R288593
theorem R290735 : Reach 290735 := rs (se 1 (by rfl) ⟨218051, by rfl⟩) R436103
theorem R159731 : Reach 159731 := rs (se 1 (by rfl) ⟨119798, by rfl⟩) R239597
theorem R487619 : Reach 487619 := rs (se 1 (by rfl) ⟨365714, by rfl⟩) R731429
theorem R979229 : Reach 979229 := rs (se 3 (by rfl) ⟨183605, by rfl⟩) R367211
theorem R160055 : Reach 160055 := rs (se 1 (by rfl) ⟨120041, by rfl⟩) R240083
theorem R61823 : Reach 61823 := rs (se 1 (by rfl) ⟨46367, by rfl⟩) R92735
theorem R192935 : Reach 192935 := rs (se 1 (by rfl) ⟨144701, by rfl⟩) R289403
theorem R160271 : Reach 160271 := rs (se 1 (by rfl) ⟨120203, by rfl⟩) R240407
theorem R1078109 : Reach 1078109 := rs (se 3 (by rfl) ⟨202145, by rfl⟩) R404291
theorem R62527 : Reach 62527 := rs (se 1 (by rfl) ⟨46895, by rfl⟩) R93791
theorem R161351 : Reach 161351 := rs (se 1 (by rfl) ⟨121013, by rfl⟩) R242027
theorem R456263 : Reach 456263 := rs (se 1 (by rfl) ⟨342197, by rfl⟩) R684395
theorem R161531 : Reach 161531 := rs (se 1 (by rfl) ⟨121148, by rfl⟩) R242297
theorem R96137 : Reach 96137 := rs (se 2 (by rfl) ⟨36051, by rfl⟩) R72103
theorem R653345 : Reach 653345 := rs (se 2 (by rfl) ⟨245004, by rfl⟩) R490009
theorem R63583 : Reach 63583 := rs (se 1 (by rfl) ⟨47687, by rfl⟩) R95375
theorem R129185 : Reach 129185 := rs (se 2 (by rfl) ⟨48444, by rfl⟩) R96889
theorem R162323 : Reach 162323 := rs (se 1 (by rfl) ⟨121742, by rfl⟩) R243485
theorem R1243673 : Reach 1243673 := rs (se 2 (by rfl) ⟨466377, by rfl⟩) R932755
theorem R162719 : Reach 162719 := rs (se 1 (by rfl) ⟨122039, by rfl⟩) R244079
theorem R64415 : Reach 64415 := rs (se 1 (by rfl) ⟨48311, by rfl⟩) R96623
theorem R293969 : Reach 293969 := rs (se 2 (by rfl) ⟨110238, by rfl⟩) R220477
theorem R64633 : Reach 64633 := rs (se 2 (by rfl) ⟨24237, by rfl⟩) R48475
theorem R261569 : Reach 261569 := rs (se 2 (by rfl) ⟨98088, by rfl⟩) R196177
theorem R425645 : Reach 425645 := rs (se 3 (by rfl) ⟨79808, by rfl⟩) R159617
theorem R98219 : Reach 98219 := rs (se 1 (by rfl) ⟨73664, by rfl⟩) R147329
theorem R655447 : Reach 655447 := rs (se 1 (by rfl) ⟨491585, by rfl⟩) R983171
theorem R426329 : Reach 426329 := rs (se 2 (by rfl) ⟨159873, by rfl⟩) R319747
theorem R459179 : Reach 459179 := rs (se 1 (by rfl) ⟨344384, by rfl⟩) R688769
theorem R164267 : Reach 164267 := rs (se 1 (by rfl) ⟨123200, by rfl⟩) R246401
theorem R230201 : Reach 230201 := rs (se 2 (by rfl) ⟨86325, by rfl⟩) R172651
theorem R164807 : Reach 164807 := rs (se 1 (by rfl) ⟨123605, by rfl⟩) R247211
theorem R164861 : Reach 164861 := rs (se 3 (by rfl) ⟨30911, by rfl⟩) R61823
theorem R66863 : Reach 66863 := rs (se 1 (by rfl) ⟨50147, by rfl⟩) R100295
theorem R427355 : Reach 427355 := rs (se 1 (by rfl) ⟨320516, by rfl⟩) R641033
theorem R165239 : Reach 165239 := rs (se 1 (by rfl) ⟨123929, by rfl⟩) R247859
theorem R165671 : Reach 165671 := rs (se 1 (by rfl) ⟨124253, by rfl⟩) R248507
theorem R166049 : Reach 166049 := rs (se 2 (by rfl) ⟨62268, by rfl⟩) R124537
theorem R166319 : Reach 166319 := rs (se 1 (by rfl) ⟨124739, by rfl⟩) R249479
theorem R16714421 : Reach 16714421 := rs (se 5 (by rfl) ⟨783488, by rfl⟩) R1566977
theorem R1149815 : Reach 1149815 := rs (se 1 (by rfl) ⟨862361, by rfl⟩) R1724723
theorem R68521 : Reach 68521 := rs (se 2 (by rfl) ⟨25695, by rfl⟩) R51391
theorem R101483 : Reach 101483 := rs (se 1 (by rfl) ⟨76112, by rfl⟩) R152225
theorem R167399 : Reach 167399 := rs (se 1 (by rfl) ⟨125549, by rfl⟩) R251099
theorem R1020599 : Reach 1020599 := rs (se 1 (by rfl) ⟨765449, by rfl⟩) R1530899
theorem R1577717 : Reach 1577717 := rs (se 5 (by rfl) ⟨73955, by rfl⟩) R147911
theorem R5083955 : Reach 5083955 := rs (se 1 (by rfl) ⟨3812966, by rfl⟩) R7625933
theorem R70751 : Reach 70751 := rs (se 1 (by rfl) ⟨53063, by rfl⟩) R106127
theorem R70811 : Reach 70811 := rs (se 1 (by rfl) ⟨53108, by rfl⟩) R106217
theorem R857303 : Reach 857303 := rs (se 1 (by rfl) ⟨642977, by rfl⟩) R1285955
theorem R627941 : Reach 627941 := rs (se 4 (by rfl) ⟨58869, by rfl⟩) R117739
theorem R71495 : Reach 71495 := rs (se 1 (by rfl) ⟨53621, by rfl⟩) R107243
theorem R432479 : Reach 432479 := rs (se 1 (by rfl) ⟨324359, by rfl⟩) R648719
theorem R72095 : Reach 72095 := rs (se 1 (by rfl) ⟨54071, by rfl⟩) R108143
theorem R72167 : Reach 72167 := rs (se 1 (by rfl) ⟨54125, by rfl⟩) R108251
theorem R236299 : Reach 236299 := rs (se 1 (by rfl) ⟨177224, by rfl⟩) R354449
theorem R269351 : Reach 269351 := rs (se 1 (by rfl) ⟨202013, by rfl⟩) R404027
theorem R72911 : Reach 72911 := rs (se 1 (by rfl) ⟨54683, by rfl⟩) R109367
theorem R73031 : Reach 73031 := rs (se 1 (by rfl) ⟨54773, by rfl⟩) R109547
theorem R73193 : Reach 73193 := rs (se 2 (by rfl) ⟨27447, by rfl⟩) R54895
theorem R73337 : Reach 73337 := rs (se 2 (by rfl) ⟨27501, by rfl⟩) R55003
theorem R171773 : Reach 171773 := rs (se 3 (by rfl) ⟨32207, by rfl⟩) R64415
theorem R106271 : Reach 106271 := rs (se 1 (by rfl) ⟨79703, by rfl⟩) R159407
theorem R73583 : Reach 73583 := rs (se 1 (by rfl) ⟨55187, by rfl⟩) R110375
theorem R106487 : Reach 106487 := rs (se 1 (by rfl) ⟨79865, by rfl⟩) R159731
theorem R794701 : Reach 794701 := rs (se 3 (by rfl) ⟨149006, by rfl⟩) R298013
theorem R106703 : Reach 106703 := rs (se 1 (by rfl) ⟨80027, by rfl⟩) R160055
theorem R205031 : Reach 205031 := rs (se 1 (by rfl) ⟨153773, by rfl⟩) R307547
theorem R106847 : Reach 106847 := rs (se 1 (by rfl) ⟨80135, by rfl⟩) R160271
theorem R74267 : Reach 74267 := rs (se 1 (by rfl) ⟨55700, by rfl⟩) R111401
theorem R270911 : Reach 270911 := rs (se 1 (by rfl) ⟨203183, by rfl⟩) R406367
theorem R74447 : Reach 74447 := rs (se 1 (by rfl) ⟨55835, by rfl⟩) R111671
theorem R74459 : Reach 74459 := rs (se 1 (by rfl) ⟨55844, by rfl⟩) R111689
theorem R1581869 : Reach 1581869 := rs (se 3 (by rfl) ⟨296600, by rfl⟩) R593201
theorem R107567 : Reach 107567 := rs (se 1 (by rfl) ⟨80675, by rfl⟩) R161351
theorem R304175 : Reach 304175 := rs (se 1 (by rfl) ⟨228131, by rfl⟩) R456263
theorem R74873 : Reach 74873 := rs (se 2 (by rfl) ⟨28077, by rfl⟩) R56155
theorem R107687 : Reach 107687 := rs (se 1 (by rfl) ⟨80765, by rfl⟩) R161531
theorem R697517 : Reach 697517 := rs (se 3 (by rfl) ⟨130784, by rfl⟩) R261569
theorem R75065 : Reach 75065 := rs (se 2 (by rfl) ⟨28149, by rfl⟩) R56299
theorem R435563 : Reach 435563 := rs (se 1 (by rfl) ⟨326672, by rfl⟩) R653345
theorem R861677 : Reach 861677 := rs (se 3 (by rfl) ⟨161564, by rfl⟩) R323129
theorem R108215 : Reach 108215 := rs (se 1 (by rfl) ⟨81161, by rfl⟩) R162323
theorem R829115 : Reach 829115 := rs (se 1 (by rfl) ⟨621836, by rfl⟩) R1243673
theorem R108479 : Reach 108479 := rs (se 1 (by rfl) ⟨81359, by rfl⟩) R162719
theorem R75743 : Reach 75743 := rs (se 1 (by rfl) ⟨56807, by rfl⟩) R113615
theorem R75755 : Reach 75755 := rs (se 1 (by rfl) ⟨56816, by rfl⟩) R113633
theorem R75803 : Reach 75803 := rs (se 1 (by rfl) ⟨56852, by rfl⟩) R113705
theorem R108665 : Reach 108665 := rs (se 2 (by rfl) ⟨40749, by rfl⟩) R81499
theorem R15935849 : Reach 15935849 := rs (se 2 (by rfl) ⟨5975943, by rfl⟩) R11951887
theorem R76169 : Reach 76169 := rs (se 2 (by rfl) ⟨28563, by rfl⟩) R57127
theorem R142087 : Reach 142087 := rs (se 1 (by rfl) ⟨106565, by rfl⟩) R213131
theorem R404459 : Reach 404459 := rs (se 1 (by rfl) ⟨303344, by rfl⟩) R606689
theorem R339109 : Reach 339109 := rs (se 4 (by rfl) ⟨31791, by rfl⟩) R63583
theorem R109979 : Reach 109979 := rs (se 1 (by rfl) ⟨82484, by rfl⟩) R164969
theorem R1453625 : Reach 1453625 := rs (se 2 (by rfl) ⟨545109, by rfl⟩) R1090219
theorem R700285 : Reach 700285 := rs (se 3 (by rfl) ⟨131303, by rfl⟩) R262607
theorem R110555 : Reach 110555 := rs (se 1 (by rfl) ⟨82916, by rfl⟩) R165833
theorem R405485 : Reach 405485 := rs (se 3 (by rfl) ⟨76028, by rfl⟩) R152057
theorem R110735 : Reach 110735 := rs (se 1 (by rfl) ⟨83051, by rfl⟩) R166103
theorem R110825 : Reach 110825 := rs (se 2 (by rfl) ⟨41559, by rfl⟩) R83119
theorem R110951 : Reach 110951 := rs (se 1 (by rfl) ⟨83213, by rfl⟩) R166427
theorem R275015 : Reach 275015 := rs (se 1 (by rfl) ⟨206261, by rfl⟩) R412523
theorem R308087 : Reach 308087 := rs (se 1 (by rfl) ⟨231065, by rfl⟩) R462131
theorem R111527 : Reach 111527 := rs (se 1 (by rfl) ⟨83645, by rfl⟩) R167291
theorem R504787 : Reach 504787 := rs (se 1 (by rfl) ⟨378590, by rfl⟩) R757181
theorem R308279 : Reach 308279 := rs (se 1 (by rfl) ⟨231209, by rfl⟩) R462419
theorem R275723 : Reach 275723 := rs (se 1 (by rfl) ⟨206792, by rfl⟩) R413585
theorem R177481 : Reach 177481 := rs (se 2 (by rfl) ⟨66555, by rfl⟩) R133111
theorem R210671 : Reach 210671 := rs (se 1 (by rfl) ⟨158003, by rfl⟩) R316007
theorem R112463 : Reach 112463 := rs (se 1 (by rfl) ⟨84347, by rfl⟩) R168695
theorem R636797 : Reach 636797 := rs (se 3 (by rfl) ⟨119399, by rfl⟩) R238799
theorem R145277 : Reach 145277 := rs (se 3 (by rfl) ⟨27239, by rfl⟩) R54479
theorem R309257 : Reach 309257 := rs (se 2 (by rfl) ⟨115971, by rfl⟩) R231943
theorem R79913 : Reach 79913 := rs (se 2 (by rfl) ⟨29967, by rfl⟩) R59935
theorem R47175 : Reach 47175 := rs (se 1 (by rfl) ⟨35381, by rfl⟩) R70763
theorem R112823 : Reach 112823 := rs (se 1 (by rfl) ⟨84617, by rfl⟩) R169235
theorem R47335 : Reach 47335 := rs (se 1 (by rfl) ⟨35501, by rfl⟩) R71003
theorem R47519 : Reach 47519 := rs (se 1 (by rfl) ⟨35639, by rfl⟩) R71279
theorem R47567 : Reach 47567 := rs (se 1 (by rfl) ⟨35675, by rfl⟩) R71351
theorem R47591 : Reach 47591 := rs (se 1 (by rfl) ⟨35693, by rfl⟩) R71387
theorem R604691 : Reach 604691 := rs (se 1 (by rfl) ⟨453518, by rfl⟩) R907037
theorem R113183 : Reach 113183 := rs (se 1 (by rfl) ⟨84887, by rfl⟩) R169775
theorem R47707 : Reach 47707 := rs (se 1 (by rfl) ⟨35780, by rfl⟩) R71561
theorem R408185 : Reach 408185 := rs (se 2 (by rfl) ⟨153069, by rfl⟩) R306139
theorem R80527 : Reach 80527 := rs (se 1 (by rfl) ⟨60395, by rfl⟩) R120791
theorem R47775 : Reach 47775 := rs (se 1 (by rfl) ⟨35831, by rfl⟩) R71663
theorem R113417 : Reach 113417 := rs (se 2 (by rfl) ⟨42531, by rfl⟩) R85063
theorem R47943 : Reach 47943 := rs (se 1 (by rfl) ⟨35957, by rfl⟩) R71915
theorem R47983 : Reach 47983 := rs (se 1 (by rfl) ⟨35987, by rfl⟩) R71975
theorem R48039 : Reach 48039 := rs (se 1 (by rfl) ⟨36029, by rfl⟩) R72059
theorem R48219 : Reach 48219 := rs (se 1 (by rfl) ⟨36164, by rfl⟩) R72329
theorem R638057 : Reach 638057 := rs (se 2 (by rfl) ⟨239271, by rfl⟩) R478543
theorem R48335 : Reach 48335 := rs (se 1 (by rfl) ⟨36251, by rfl⟩) R72503
theorem R48359 : Reach 48359 := rs (se 1 (by rfl) ⟨36269, by rfl⟩) R72539
theorem R48455 : Reach 48455 := rs (se 1 (by rfl) ⟨36341, by rfl⟩) R72683
theorem R113993 : Reach 113993 := rs (se 2 (by rfl) ⟨42747, by rfl⟩) R85495
theorem R48591 : Reach 48591 := rs (se 1 (by rfl) ⟨36443, by rfl⟩) R72887
theorem R2866747 : Reach 2866747 := rs (se 1 (by rfl) ⟨2150060, by rfl⟩) R4300121
theorem R48751 : Reach 48751 := rs (se 1 (by rfl) ⟨36563, by rfl⟩) R73127
theorem R48807 : Reach 48807 := rs (se 1 (by rfl) ⟨36605, by rfl⟩) R73211
theorem R48871 : Reach 48871 := rs (se 1 (by rfl) ⟨36653, by rfl⟩) R73307
theorem R114407 : Reach 114407 := rs (se 1 (by rfl) ⟨85805, by rfl⟩) R171611
theorem R48927 : Reach 48927 := rs (se 1 (by rfl) ⟨36695, by rfl⟩) R73391
theorem R212807 : Reach 212807 := rs (se 1 (by rfl) ⟨159605, by rfl⟩) R319211
theorem R835433 : Reach 835433 := rs (se 2 (by rfl) ⟨313287, by rfl⟩) R626575
theorem R49007 : Reach 49007 := rs (se 1 (by rfl) ⟨36755, by rfl⟩) R73511
theorem R49063 : Reach 49063 := rs (se 1 (by rfl) ⟨36797, by rfl⟩) R73595
theorem R114875 : Reach 114875 := rs (se 1 (by rfl) ⟨86156, by rfl⟩) R172313
theorem R49343 : Reach 49343 := rs (se 1 (by rfl) ⟨37007, by rfl⟩) R74015
theorem R49359 : Reach 49359 := rs (se 1 (by rfl) ⟨37019, by rfl⟩) R74039
theorem R49407 : Reach 49407 := rs (se 1 (by rfl) ⟨37055, by rfl⟩) R74111
theorem R409859 : Reach 409859 := rs (se 1 (by rfl) ⟨307394, by rfl⟩) R614789
theorem R114983 : Reach 114983 := rs (se 1 (by rfl) ⟨86237, by rfl⟩) R172475
theorem R49455 : Reach 49455 := rs (se 1 (by rfl) ⟨37091, by rfl⟩) R74183
theorem R278957 : Reach 278957 := rs (se 3 (by rfl) ⟨52304, by rfl⟩) R104609
theorem R49691 : Reach 49691 := rs (se 1 (by rfl) ⟨37268, by rfl⟩) R74537
theorem R49695 : Reach 49695 := rs (se 1 (by rfl) ⟨37271, by rfl⟩) R74543
theorem R49775 : Reach 49775 := rs (se 1 (by rfl) ⟨37331, by rfl⟩) R74663
theorem R49831 : Reach 49831 := rs (se 1 (by rfl) ⟨37373, by rfl⟩) R74747
theorem R49871 : Reach 49871 := rs (se 1 (by rfl) ⟨37403, by rfl⟩) R74807
theorem R49883 : Reach 49883 := rs (se 1 (by rfl) ⟨37412, by rfl⟩) R74825
theorem R213779 : Reach 213779 := rs (se 1 (by rfl) ⟨160334, by rfl⟩) R320669
theorem R49951 : Reach 49951 := rs (se 1 (by rfl) ⟨37463, by rfl⟩) R74927
theorem R50119 : Reach 50119 := rs (se 1 (by rfl) ⟨37589, by rfl⟩) R75179
theorem R50223 : Reach 50223 := rs (se 1 (by rfl) ⟨37667, by rfl⟩) R75335
theorem R50287 : Reach 50287 := rs (se 1 (by rfl) ⟨37715, by rfl⟩) R75431
theorem R50343 : Reach 50343 := rs (se 1 (by rfl) ⟨37757, by rfl⟩) R75515
theorem R50367 : Reach 50367 := rs (se 1 (by rfl) ⟨37775, by rfl⟩) R75551
theorem R50399 : Reach 50399 := rs (se 1 (by rfl) ⟨37799, by rfl⟩) R75599
theorem R50479 : Reach 50479 := rs (se 1 (by rfl) ⟨37859, by rfl⟩) R75719
theorem R50511 : Reach 50511 := rs (se 1 (by rfl) ⟨37883, by rfl⟩) R75767
theorem R312673 : Reach 312673 := rs (se 2 (by rfl) ⟨117252, by rfl⟩) R234505
theorem R378269 : Reach 378269 := rs (se 3 (by rfl) ⟨70925, by rfl⟩) R141851
theorem R181673 : Reach 181673 := rs (se 2 (by rfl) ⟨68127, by rfl⟩) R136255
theorem R83369 : Reach 83369 := rs (se 2 (by rfl) ⟨31263, by rfl⟩) R62527
theorem R181775 : Reach 181775 := rs (se 1 (by rfl) ⟨136331, by rfl⟩) R272663
theorem R50715 : Reach 50715 := rs (se 1 (by rfl) ⟨38036, by rfl⟩) R76073
theorem R50719 : Reach 50719 := rs (se 1 (by rfl) ⟨38039, by rfl⟩) R76079
theorem R50879 : Reach 50879 := rs (se 1 (by rfl) ⟨38159, by rfl⟩) R76319
theorem R50983 : Reach 50983 := rs (se 1 (by rfl) ⟨38237, by rfl⟩) R76475
theorem R379079 : Reach 379079 := rs (se 1 (by rfl) ⟨284309, by rfl⟩) R568619
theorem R117119 : Reach 117119 := rs (se 1 (by rfl) ⟨87839, by rfl⟩) R175679
theorem R412249 : Reach 412249 := rs (se 2 (by rfl) ⟨154593, by rfl⟩) R309187
theorem R183131 : Reach 183131 := rs (se 1 (by rfl) ⟨137348, by rfl⟩) R274697
theorem R183161 : Reach 183161 := rs (se 2 (by rfl) ⟨68685, by rfl⟩) R137371
theorem R413309 : Reach 413309 := rs (se 3 (by rfl) ⟨77495, by rfl⟩) R154991
theorem R184315 : Reach 184315 := rs (se 1 (by rfl) ⟨138236, by rfl⟩) R276473
theorem R53311 : Reach 53311 := rs (se 1 (by rfl) ⟨39983, by rfl⟩) R79967
theorem R86123 : Reach 86123 := rs (se 1 (by rfl) ⟨64592, by rfl⟩) R129185
theorem R86177 : Reach 86177 := rs (se 2 (by rfl) ⟨32316, by rfl⟩) R64633
theorem R53659 : Reach 53659 := rs (se 1 (by rfl) ⟨40244, by rfl⟩) R80489
theorem R184787 : Reach 184787 := rs (se 1 (by rfl) ⟨138590, by rfl⟩) R277181
theorem R1233467 : Reach 1233467 := rs (se 1 (by rfl) ⟨925100, by rfl⟩) R1850201
theorem R1528645 : Reach 1528645 := rs (se 4 (by rfl) ⟨143310, by rfl⟩) R286621
theorem R119657 : Reach 119657 := rs (se 2 (by rfl) ⟨44871, by rfl⟩) R89743
theorem R54175 : Reach 54175 := rs (se 1 (by rfl) ⟨40631, by rfl⟩) R81263
theorem R283763 : Reach 283763 := rs (se 1 (by rfl) ⟨212822, by rfl⟩) R425645
theorem R54427 : Reach 54427 := rs (se 1 (by rfl) ⟨40820, by rfl⟩) R81641
theorem R120487 : Reach 120487 := rs (se 1 (by rfl) ⟨90365, by rfl⟩) R180731
theorem R55111 : Reach 55111 := rs (se 1 (by rfl) ⟨41333, by rfl⟩) R82667
theorem R153569 : Reach 153569 := rs (se 2 (by rfl) ⟨57588, by rfl⟩) R115177
theorem R121247 : Reach 121247 := rs (se 1 (by rfl) ⟨90935, by rfl⟩) R181871
theorem R55759 : Reach 55759 := rs (se 1 (by rfl) ⟨41819, by rfl⟩) R83639
theorem R285221 : Reach 285221 := rs (se 4 (by rfl) ⟨26739, by rfl⟩) R53479
theorem R187535 : Reach 187535 := rs (se 1 (by rfl) ⟨140651, by rfl⟩) R281303
theorem R56551 : Reach 56551 := rs (se 1 (by rfl) ⟨42413, by rfl⟩) R84827
theorem R56647 : Reach 56647 := rs (se 1 (by rfl) ⟨42485, by rfl⟩) R84971
theorem R122219 : Reach 122219 := rs (se 1 (by rfl) ⟨91664, by rfl⟩) R183329
theorem R89819 : Reach 89819 := rs (se 1 (by rfl) ⟨67364, by rfl⟩) R134729
theorem R122735 : Reach 122735 := rs (se 1 (by rfl) ⟨92051, by rfl⟩) R184103
theorem R57199 : Reach 57199 := rs (se 1 (by rfl) ⟨42899, by rfl⟩) R85799
theorem R90089 : Reach 90089 := rs (se 2 (by rfl) ⟨33783, by rfl⟩) R67567
theorem R122867 : Reach 122867 := rs (se 1 (by rfl) ⟨92150, by rfl⟩) R184301
theorem R319955 : Reach 319955 := rs (se 1 (by rfl) ⟨239966, by rfl⟩) R479933
theorem R90791 : Reach 90791 := rs (se 1 (by rfl) ⟨68093, by rfl⟩) R136187
theorem R58415 : Reach 58415 := rs (se 1 (by rfl) ⟨43811, by rfl⟩) R87623
theorem R353819 : Reach 353819 := rs (se 1 (by rfl) ⟨265364, by rfl⟩) R530729
theorem R124487 : Reach 124487 := rs (se 1 (by rfl) ⟨93365, by rfl⟩) R186731
theorem R649079 : Reach 649079 := rs (se 1 (by rfl) ⟨486809, by rfl⟩) R973619
theorem R124811 : Reach 124811 := rs (se 1 (by rfl) ⟨93608, by rfl⟩) R187217
theorem R190451 : Reach 190451 := rs (se 1 (by rfl) ⟨142838, by rfl⟩) R285677
theorem R321671 : Reach 321671 := rs (se 1 (by rfl) ⟨241253, by rfl⟩) R482507
theorem R93449 : Reach 93449 := rs (se 2 (by rfl) ⟨35043, by rfl⟩) R70087
theorem R126431 : Reach 126431 := rs (se 1 (by rfl) ⟨94823, by rfl⟩) R189647
theorem R355913 : Reach 355913 := rs (se 2 (by rfl) ⟨133467, by rfl⟩) R266935
theorem R192091 : Reach 192091 := rs (se 1 (by rfl) ⟨144068, by rfl⟩) R288137
theorem R356345 : Reach 356345 := rs (se 2 (by rfl) ⟨133629, by rfl⟩) R267259
theorem R356663 : Reach 356663 := rs (se 1 (by rfl) ⟨267497, by rfl⟩) R534995
theorem R848555 : Reach 848555 := rs (se 1 (by rfl) ⟨636416, by rfl⟩) R1272833
theorem R62203 : Reach 62203 := rs (se 1 (by rfl) ⟨46652, by rfl⟩) R93305
theorem R193747 : Reach 193747 := rs (se 1 (by rfl) ⟨145310, by rfl⟩) R290621
theorem R128263 : Reach 128263 := rs (se 1 (by rfl) ⟨96197, by rfl⟩) R192395
theorem R193823 : Reach 193823 := rs (se 1 (by rfl) ⟨145367, by rfl⟩) R290735
theorem R685523 : Reach 685523 := rs (se 1 (by rfl) ⟨514142, by rfl⟩) R1028285
theorem R325079 : Reach 325079 := rs (se 1 (by rfl) ⟨243809, by rfl⟩) R487619
theorem R652819 : Reach 652819 := rs (se 1 (by rfl) ⟨489614, by rfl⟩) R979229
theorem R783917 : Reach 783917 := rs (se 3 (by rfl) ⟨146984, by rfl⟩) R293969
theorem R128623 : Reach 128623 := rs (se 1 (by rfl) ⟨96467, by rfl⟩) R192935
theorem R718739 : Reach 718739 := rs (se 1 (by rfl) ⟨539054, by rfl⟩) R1078109
theorem R161975 : Reach 161975 := rs (se 1 (by rfl) ⟨121481, by rfl⟩) R242963
theorem R64091 : Reach 64091 := rs (se 1 (by rfl) ⟨48068, by rfl⟩) R96137
theorem R162539 : Reach 162539 := rs (se 1 (by rfl) ⟨121904, by rfl⟩) R243809
theorem R97033 : Reach 97033 := rs (se 2 (by rfl) ⟨36387, by rfl⟩) R72775
theorem R162647 : Reach 162647 := rs (se 1 (by rfl) ⟨121985, by rfl⟩) R243971
theorem R359639 : Reach 359639 := rs (se 1 (by rfl) ⟨269729, by rfl⟩) R539459
theorem R163279 : Reach 163279 := rs (se 1 (by rfl) ⟨122459, by rfl⟩) R244919
theorem R163457 : Reach 163457 := rs (se 2 (by rfl) ⟨61296, by rfl⟩) R122593
theorem R98057 : Reach 98057 := rs (se 2 (by rfl) ⟨36771, by rfl⟩) R73543
theorem R261917 : Reach 261917 := rs (se 3 (by rfl) ⟨49109, by rfl⟩) R98219
theorem R163727 : Reach 163727 := rs (se 1 (by rfl) ⟨122795, by rfl⟩) R245591
theorem R853213 : Reach 853213 := rs (se 3 (by rfl) ⟨159977, by rfl⟩) R319955
theorem R722429 : Reach 722429 := rs (se 3 (by rfl) ⟨135455, by rfl⟩) R270911
theorem R11142947 : Reach 11142947 := rs (se 1 (by rfl) ⟨8357210, by rfl⟩) R16714421
theorem R67655 : Reach 67655 := rs (se 1 (by rfl) ⟨50741, by rfl⟩) R101483
theorem R822311 : Reach 822311 := rs (se 1 (by rfl) ⟨616733, by rfl⟩) R1233467
theorem R1051811 : Reach 1051811 := rs (se 1 (by rfl) ⟨788858, by rfl⟩) R1577717
theorem R102379 : Reach 102379 := rs (se 1 (by rfl) ⟨76784, by rfl⟩) R153569
theorem R70847 : Reach 70847 := rs (se 1 (by rfl) ⟨53135, by rfl⟩) R106271
theorem R70991 : Reach 70991 := rs (se 1 (by rfl) ⟨53243, by rfl⟩) R106487
theorem R71081 : Reach 71081 := rs (se 2 (by rfl) ⟨26655, by rfl⟩) R53311
theorem R71135 : Reach 71135 := rs (se 1 (by rfl) ⟨53351, by rfl⟩) R106703
theorem R71231 : Reach 71231 := rs (se 1 (by rfl) ⟨53423, by rfl⟩) R106847
theorem R1054579 : Reach 1054579 := rs (se 1 (by rfl) ⟨790934, by rfl⟩) R1581869
theorem R71545 : Reach 71545 := rs (se 2 (by rfl) ⟨26829, by rfl⟩) R53659
theorem R202783 : Reach 202783 := rs (se 1 (by rfl) ⟨152087, by rfl⟩) R304175
theorem R71711 : Reach 71711 := rs (se 1 (by rfl) ⟨53783, by rfl⟩) R107567
theorem R465011 : Reach 465011 := rs (se 1 (by rfl) ⟨348758, by rfl⟩) R697517
theorem R1808581 : Reach 1808581 := rs (se 4 (by rfl) ⟨169554, by rfl⟩) R339109
theorem R235879 : Reach 235879 := rs (se 1 (by rfl) ⟨176909, by rfl⟩) R353819
theorem R2038193 : Reach 2038193 := rs (se 2 (by rfl) ⟨764322, by rfl⟩) R1528645
theorem R72143 : Reach 72143 := rs (se 1 (by rfl) ⟨54107, by rfl⟩) R108215
theorem R72233 : Reach 72233 := rs (se 2 (by rfl) ⟨27087, by rfl⟩) R54175
theorem R432719 : Reach 432719 := rs (se 1 (by rfl) ⟨324539, by rfl⟩) R649079
theorem R72443 : Reach 72443 := rs (se 1 (by rfl) ⟨54332, by rfl⟩) R108665
theorem R72569 : Reach 72569 := rs (se 2 (by rfl) ⟨27213, by rfl⟩) R54427
theorem R10623899 : Reach 10623899 := rs (se 1 (by rfl) ⟨7967924, by rfl⟩) R15935849
theorem R170909 : Reach 170909 := rs (se 3 (by rfl) ⟨32045, by rfl⟩) R64091
theorem R171017 : Reach 171017 := rs (se 2 (by rfl) ⟨64131, by rfl⟩) R128263
theorem R236641 : Reach 236641 := rs (se 2 (by rfl) ⟨88740, by rfl⟩) R177481
theorem R269639 : Reach 269639 := rs (se 1 (by rfl) ⟨202229, by rfl⟩) R404459
theorem R171497 : Reach 171497 := rs (se 2 (by rfl) ⟨64311, by rfl⟩) R128623
theorem R73319 : Reach 73319 := rs (se 1 (by rfl) ⟨54989, by rfl⟩) R109979
theorem R237275 : Reach 237275 := rs (se 1 (by rfl) ⟨177956, by rfl⟩) R355913
theorem R73481 : Reach 73481 := rs (se 2 (by rfl) ⟨27555, by rfl⟩) R55111
theorem R73703 : Reach 73703 := rs (se 1 (by rfl) ⟨55277, by rfl⟩) R110555
theorem R270323 : Reach 270323 := rs (se 1 (by rfl) ⟨202742, by rfl⟩) R405485
theorem R237563 : Reach 237563 := rs (se 1 (by rfl) ⟨178172, by rfl⟩) R356345
theorem R73823 : Reach 73823 := rs (se 1 (by rfl) ⟨55367, by rfl⟩) R110735
theorem R73883 : Reach 73883 := rs (se 1 (by rfl) ⟨55412, by rfl⟩) R110825
theorem R237775 : Reach 237775 := rs (se 1 (by rfl) ⟨178331, by rfl⟩) R356663
theorem R73967 : Reach 73967 := rs (se 1 (by rfl) ⟨55475, by rfl⟩) R110951
theorem R565703 : Reach 565703 := rs (se 1 (by rfl) ⟨424277, by rfl⟩) R848555
theorem R205391 : Reach 205391 := rs (se 1 (by rfl) ⟨154043, by rfl⟩) R308087
theorem R74345 : Reach 74345 := rs (se 2 (by rfl) ⟨27879, by rfl⟩) R55759
theorem R74351 : Reach 74351 := rs (se 1 (by rfl) ⟨55763, by rfl⟩) R111527
theorem R205519 : Reach 205519 := rs (se 1 (by rfl) ⟨154139, by rfl⟩) R308279
theorem R107369 : Reach 107369 := rs (se 2 (by rfl) ⟨40263, by rfl⟩) R80527
theorem R140447 : Reach 140447 := rs (se 1 (by rfl) ⟨105335, by rfl⟩) R210671
theorem R74975 : Reach 74975 := rs (se 1 (by rfl) ⟨56231, by rfl⟩) R112463
theorem R206171 : Reach 206171 := rs (se 1 (by rfl) ⟨154628, by rfl⟩) R309257
theorem R75215 : Reach 75215 := rs (se 1 (by rfl) ⟨56411, by rfl⟩) R112823
theorem R107983 : Reach 107983 := rs (se 1 (by rfl) ⟨80987, by rfl⟩) R161975
theorem R75401 : Reach 75401 := rs (se 2 (by rfl) ⟨28275, by rfl⟩) R56551
theorem R403127 : Reach 403127 := rs (se 1 (by rfl) ⟨302345, by rfl⟩) R604691
theorem R75455 : Reach 75455 := rs (se 1 (by rfl) ⟨56591, by rfl⟩) R113183
theorem R272123 : Reach 272123 := rs (se 1 (by rfl) ⟨204092, by rfl⟩) R408185
theorem R75529 : Reach 75529 := rs (se 2 (by rfl) ⟨28323, by rfl⟩) R56647
theorem R108359 : Reach 108359 := rs (se 1 (by rfl) ⟨81269, by rfl⟩) R162539
theorem R75611 : Reach 75611 := rs (se 1 (by rfl) ⟨56708, by rfl⟩) R113417
theorem R108431 : Reach 108431 := rs (se 1 (by rfl) ⟨81323, by rfl⟩) R162647
theorem R239759 : Reach 239759 := rs (se 1 (by rfl) ⟨179819, by rfl⟩) R359639
theorem R75995 : Reach 75995 := rs (se 1 (by rfl) ⟨56996, by rfl⟩) R113993
theorem R108971 : Reach 108971 := rs (se 1 (by rfl) ⟨81728, by rfl⟩) R163457
theorem R76265 : Reach 76265 := rs (se 2 (by rfl) ⟨28599, by rfl⟩) R57199
theorem R76271 : Reach 76271 := rs (se 1 (by rfl) ⟨57203, by rfl⟩) R114407
theorem R174611 : Reach 174611 := rs (se 1 (by rfl) ⟨130958, by rfl⟩) R261917
theorem R141871 : Reach 141871 := rs (se 1 (by rfl) ⟨106403, by rfl⟩) R212807
theorem R109151 : Reach 109151 := rs (se 1 (by rfl) ⟨81863, by rfl⟩) R163727
theorem R1059601 : Reach 1059601 := rs (se 2 (by rfl) ⟨397350, by rfl⟩) R794701
theorem R76583 : Reach 76583 := rs (se 1 (by rfl) ⟨57437, by rfl⟩) R114875
theorem R273239 : Reach 273239 := rs (se 1 (by rfl) ⟨204929, by rfl⟩) R409859
theorem R76655 : Reach 76655 := rs (se 1 (by rfl) ⟨57491, by rfl⟩) R114983
theorem R306119 : Reach 306119 := rs (se 1 (by rfl) ⟨229589, by rfl⟩) R459179
theorem R109511 : Reach 109511 := rs (se 1 (by rfl) ⟨82133, by rfl⟩) R164267
theorem R109871 : Reach 109871 := rs (se 1 (by rfl) ⟨82403, by rfl⟩) R164807
theorem R109907 : Reach 109907 := rs (se 1 (by rfl) ⟨82430, by rfl⟩) R164861
theorem R110159 : Reach 110159 := rs (se 1 (by rfl) ⟨82619, by rfl⟩) R165239
theorem R110447 : Reach 110447 := rs (se 1 (by rfl) ⟨82835, by rfl⟩) R165671
theorem R110699 : Reach 110699 := rs (se 1 (by rfl) ⟨83024, by rfl⟩) R166049
theorem R78079 : Reach 78079 := rs (se 1 (by rfl) ⟨58559, by rfl⟩) R117119
theorem R110879 : Reach 110879 := rs (se 1 (by rfl) ⟨83159, by rfl⟩) R166319
theorem R570077 : Reach 570077 := rs (se 3 (by rfl) ⟨106889, by rfl⟩) R213779
theorem R111599 : Reach 111599 := rs (se 1 (by rfl) ⟨83699, by rfl⟩) R167399
theorem R3389303 : Reach 3389303 := rs (se 1 (by rfl) ⟨2541977, by rfl⟩) R5083955
theorem R79771 : Reach 79771 := rs (se 1 (by rfl) ⟨59828, by rfl⟩) R119657
theorem R47167 : Reach 47167 := rs (se 1 (by rfl) ⟨35375, by rfl⟩) R70751
theorem R47207 : Reach 47207 := rs (se 1 (by rfl) ⟨35405, by rfl⟩) R70811
theorem R178301 : Reach 178301 := rs (se 3 (by rfl) ⟨33431, by rfl⟩) R66863
theorem R571535 : Reach 571535 := rs (se 1 (by rfl) ⟨428651, by rfl⟩) R857303
theorem R47663 : Reach 47663 := rs (se 1 (by rfl) ⟨35747, by rfl⟩) R71495
theorem R80831 : Reach 80831 := rs (se 1 (by rfl) ⟨60623, by rfl⟩) R121247
theorem R48063 : Reach 48063 := rs (se 1 (by rfl) ⟨36047, by rfl⟩) R72095
theorem R48111 : Reach 48111 := rs (se 1 (by rfl) ⟨36083, by rfl⟩) R72167
theorem R179567 : Reach 179567 := rs (se 1 (by rfl) ⟨134675, by rfl⟩) R269351
theorem R48607 : Reach 48607 := rs (se 1 (by rfl) ⟨36455, by rfl⟩) R72911
theorem R48687 : Reach 48687 := rs (se 1 (by rfl) ⟨36515, by rfl⟩) R73031
theorem R81479 : Reach 81479 := rs (se 1 (by rfl) ⟨61109, by rfl⟩) R122219
theorem R48795 : Reach 48795 := rs (se 1 (by rfl) ⟨36596, by rfl⟩) R73193
theorem R48891 : Reach 48891 := rs (se 1 (by rfl) ⟨36668, by rfl⟩) R73337
theorem R933713 : Reach 933713 := rs (se 2 (by rfl) ⟨350142, by rfl⟩) R700285
theorem R114515 : Reach 114515 := rs (se 1 (by rfl) ⟨85886, by rfl⟩) R171773
theorem R81823 : Reach 81823 := rs (se 1 (by rfl) ⟨61367, by rfl⟩) R122735
theorem R49055 : Reach 49055 := rs (se 1 (by rfl) ⟨36791, by rfl⟩) R73583
theorem R81911 : Reach 81911 := rs (se 1 (by rfl) ⟨61433, by rfl⟩) R122867
theorem R245753 : Reach 245753 := rs (se 2 (by rfl) ⟨92157, by rfl⟩) R184315
theorem R49511 : Reach 49511 := rs (se 1 (by rfl) ⟨37133, by rfl⟩) R74267
theorem R49631 : Reach 49631 := rs (se 1 (by rfl) ⟨37223, by rfl⟩) R74447
theorem R49639 : Reach 49639 := rs (se 1 (by rfl) ⟨37229, by rfl⟩) R74459
theorem R49915 : Reach 49915 := rs (se 1 (by rfl) ⟨37436, by rfl⟩) R74873
theorem R50043 : Reach 50043 := rs (se 1 (by rfl) ⟨37532, by rfl⟩) R75065
theorem R574451 : Reach 574451 := rs (se 1 (by rfl) ⟨430838, by rfl⟩) R861677
theorem R82937 : Reach 82937 := rs (se 2 (by rfl) ⟨31101, by rfl⟩) R62203
theorem R82991 : Reach 82991 := rs (se 1 (by rfl) ⟨62243, by rfl⟩) R124487
theorem R83207 : Reach 83207 := rs (se 1 (by rfl) ⟨62405, by rfl⟩) R124811
theorem R673049 : Reach 673049 := rs (se 2 (by rfl) ⟨252393, by rfl⟩) R504787
theorem R50495 : Reach 50495 := rs (se 1 (by rfl) ⟨37871, by rfl⟩) R75743
theorem R50503 : Reach 50503 := rs (se 1 (by rfl) ⟨37877, by rfl⟩) R75755
theorem R50535 : Reach 50535 := rs (se 1 (by rfl) ⟨37901, by rfl⟩) R75803
theorem R214447 : Reach 214447 := rs (se 1 (by rfl) ⟨160835, by rfl⟩) R321671
theorem R50779 : Reach 50779 := rs (se 1 (by rfl) ⟨38084, by rfl⟩) R76169
theorem R870425 : Reach 870425 := rs (se 2 (by rfl) ⟨326409, by rfl⟩) R652819
theorem R3066173 : Reach 3066173 := rs (se 3 (by rfl) ⟨574907, by rfl⟩) R1149815
theorem R84287 : Reach 84287 := rs (se 1 (by rfl) ⟨63215, by rfl⟩) R126431
theorem R969083 : Reach 969083 := rs (se 1 (by rfl) ⟨726812, by rfl⟩) R1453625
theorem R870821 : Reach 870821 := rs (se 4 (by rfl) ⟨81639, by rfl⟩) R163279
theorem R183343 : Reach 183343 := rs (se 1 (by rfl) ⟨137507, by rfl⟩) R275015
theorem R183815 : Reach 183815 := rs (se 1 (by rfl) ⟨137861, by rfl⟩) R275723
theorem R216719 : Reach 216719 := rs (se 1 (by rfl) ⟨162539, by rfl⟩) R325079
theorem R315065 : Reach 315065 := rs (se 2 (by rfl) ⟨118149, by rfl⟩) R236299
theorem R479159 : Reach 479159 := rs (se 1 (by rfl) ⟨359369, by rfl⟩) R718739
theorem R53275 : Reach 53275 := rs (se 1 (by rfl) ⟨39956, by rfl⟩) R79913
theorem R1102157 : Reach 1102157 := rs (se 3 (by rfl) ⟨206654, by rfl⟩) R413309
theorem R3822329 : Reach 3822329 := rs (se 2 (by rfl) ⟨1433373, by rfl⟩) R2866747
theorem R873929 : Reach 873929 := rs (se 2 (by rfl) ⟨327723, by rfl⟩) R655447
theorem R284219 : Reach 284219 := rs (se 1 (by rfl) ⟨213164, by rfl⟩) R426329
theorem R185971 : Reach 185971 := rs (se 1 (by rfl) ⟨139478, by rfl⟩) R278957
theorem R153467 : Reach 153467 := rs (se 1 (by rfl) ⟨115100, by rfl⟩) R230201
theorem R546749 : Reach 546749 := rs (se 3 (by rfl) ⟨102515, by rfl⟩) R205031
theorem R284903 : Reach 284903 := rs (se 1 (by rfl) ⟨213677, by rfl⟩) R427355
theorem R252179 : Reach 252179 := rs (se 1 (by rfl) ⟨189134, by rfl⟩) R378269
theorem R121115 : Reach 121115 := rs (se 1 (by rfl) ⟨90836, by rfl⟩) R181673
theorem R55579 : Reach 55579 := rs (se 1 (by rfl) ⟨41684, by rfl⟩) R83369
theorem R252719 : Reach 252719 := rs (se 1 (by rfl) ⟨189539, by rfl⟩) R379079
theorem R416897 : Reach 416897 := rs (se 2 (by rfl) ⟨156336, by rfl⟩) R312673
theorem R122087 : Reach 122087 := rs (se 1 (by rfl) ⟨91565, by rfl⟩) R183131
theorem R122107 : Reach 122107 := rs (se 1 (by rfl) ⟨91580, by rfl⟩) R183161
theorem R57415 : Reach 57415 := rs (se 1 (by rfl) ⟨43061, by rfl⟩) R86123
theorem R57451 : Reach 57451 := rs (se 1 (by rfl) ⟨43088, by rfl⟩) R86177
theorem R155773 : Reach 155773 := rs (se 3 (by rfl) ⟨29207, by rfl⟩) R58415
theorem R123191 : Reach 123191 := rs (se 1 (by rfl) ⟨92393, by rfl⟩) R184787
theorem R287165 : Reach 287165 := rs (se 3 (by rfl) ⟨53843, by rfl⟩) R107687
theorem R680399 : Reach 680399 := rs (se 1 (by rfl) ⟨510299, by rfl⟩) R1020599
theorem R189175 : Reach 189175 := rs (se 1 (by rfl) ⟨141881, by rfl⟩) R283763
theorem R549665 : Reach 549665 := rs (se 2 (by rfl) ⟨206124, by rfl⟩) R412249
theorem R418627 : Reach 418627 := rs (se 1 (by rfl) ⟨313970, by rfl⟩) R627941
theorem R189449 : Reach 189449 := rs (se 2 (by rfl) ⟨71043, by rfl⟩) R142087
theorem R91361 : Reach 91361 := rs (se 2 (by rfl) ⟨34260, by rfl⟩) R68521
theorem R484733 : Reach 484733 := rs (se 3 (by rfl) ⟨90887, by rfl⟩) R181775
theorem R288319 : Reach 288319 := rs (se 1 (by rfl) ⟨216239, by rfl⟩) R432479
theorem R190147 : Reach 190147 := rs (se 1 (by rfl) ⟨142610, by rfl⟩) R285221
theorem R125023 : Reach 125023 := rs (se 1 (by rfl) ⟨93767, by rfl⟩) R187535
theorem R256121 : Reach 256121 := rs (se 2 (by rfl) ⟨96045, by rfl⟩) R192091
theorem R59879 : Reach 59879 := rs (se 1 (by rfl) ⟨44909, by rfl⟩) R89819
theorem R289277 : Reach 289277 := rs (se 3 (by rfl) ⟨54239, by rfl⟩) R108479
theorem R60059 : Reach 60059 := rs (se 1 (by rfl) ⟨45044, by rfl⟩) R90089
theorem R60527 : Reach 60527 := rs (se 1 (by rfl) ⟨45395, by rfl⟩) R90791
theorem R290375 : Reach 290375 := rs (se 1 (by rfl) ⟨217781, by rfl⟩) R435563
theorem R552743 : Reach 552743 := rs (se 1 (by rfl) ⟨414557, by rfl⟩) R829115
theorem R126967 : Reach 126967 := rs (se 1 (by rfl) ⟨95225, by rfl⟩) R190451
theorem R258329 : Reach 258329 := rs (se 2 (by rfl) ⟨96873, by rfl⟩) R193747
theorem R62299 : Reach 62299 := rs (se 1 (by rfl) ⟨46724, by rfl⟩) R93449
theorem R160649 : Reach 160649 := rs (se 2 (by rfl) ⟨60243, by rfl⟩) R120487
theorem R129215 : Reach 129215 := rs (se 1 (by rfl) ⟨96911, by rfl⟩) R193823
theorem R457015 : Reach 457015 := rs (se 1 (by rfl) ⟨342761, by rfl⟩) R685523
theorem R129377 : Reach 129377 := rs (se 2 (by rfl) ⟨48516, by rfl⟩) R97033
theorem R522611 : Reach 522611 := rs (se 1 (by rfl) ⟨391958, by rfl⟩) R783917
theorem R424531 : Reach 424531 := rs (se 1 (by rfl) ⟨318398, by rfl⟩) R636797
theorem R96851 : Reach 96851 := rs (se 1 (by rfl) ⟨72638, by rfl⟩) R145277
theorem R425371 : Reach 425371 := rs (se 1 (by rfl) ⟨319028, by rfl⟩) R638057
theorem R65371 : Reach 65371 := rs (se 1 (by rfl) ⟨49028, by rfl⟩) R98057
theorem R556955 : Reach 556955 := rs (se 1 (by rfl) ⟨417716, by rfl⟩) R835433
theorem R10192877 : Reach 10192877 := rs (se 3 (by rfl) ⟨1911164, by rfl⟩) R3822329
theorem R100705 : Reach 100705 := rs (se 2 (by rfl) ⟨37764, by rfl⟩) R75529
theorem R166697 : Reach 166697 := rs (se 2 (by rfl) ⟨62511, by rfl⟩) R125023
theorem R1412801 : Reach 1412801 := rs (se 2 (by rfl) ⟨529800, by rfl⟩) R1059601
theorem R2330477 : Reach 2330477 := rs (se 3 (by rfl) ⟨436964, by rfl⟩) R873929
theorem R102311 : Reach 102311 := rs (se 1 (by rfl) ⟨76733, by rfl⟩) R153467
theorem R364499 : Reach 364499 := rs (se 1 (by rfl) ⟨273374, by rfl⟩) R546749
theorem R168119 : Reach 168119 := rs (se 1 (by rfl) ⟨126089, by rfl⟩) R252179
theorem R2232677 : Reach 2232677 := rs (se 4 (by rfl) ⟨209313, by rfl⟩) R418627
theorem R168479 : Reach 168479 := rs (se 1 (by rfl) ⟨126359, by rfl⟩) R252719
theorem R7082599 : Reach 7082599 := rs (se 1 (by rfl) ⟨5311949, by rfl⟩) R10623899
theorem R136505 : Reach 136505 := rs (se 2 (by rfl) ⟨51189, by rfl⟩) R102379
theorem R169289 : Reach 169289 := rs (se 2 (by rfl) ⟨63483, by rfl⟩) R126967
theorem R71033 : Reach 71033 := rs (se 2 (by rfl) ⟨26637, by rfl⟩) R53275
theorem R104105 : Reach 104105 := rs (se 2 (by rfl) ⟨39039, by rfl⟩) R78079
theorem R136927 : Reach 136927 := rs (se 1 (by rfl) ⟨102695, by rfl⟩) R205391
theorem R366443 : Reach 366443 := rs (se 1 (by rfl) ⟨274832, by rfl⟩) R549665
theorem R71579 : Reach 71579 := rs (se 1 (by rfl) ⟨53684, by rfl⟩) R107369
theorem R137447 : Reach 137447 := rs (se 1 (by rfl) ⟨103085, by rfl⟩) R206171
theorem R268751 : Reach 268751 := rs (se 1 (by rfl) ⟨201563, by rfl⟩) R403127
theorem R72239 : Reach 72239 := rs (se 1 (by rfl) ⟨54179, by rfl⟩) R108359
theorem R72287 : Reach 72287 := rs (se 1 (by rfl) ⟨54215, by rfl⟩) R108431
theorem R170747 : Reach 170747 := rs (se 1 (by rfl) ⟨128060, by rfl⟩) R256121
theorem R72647 : Reach 72647 := rs (se 1 (by rfl) ⟨54485, by rfl⟩) R108971
theorem R72767 : Reach 72767 := rs (se 1 (by rfl) ⟨54575, by rfl⟩) R109151
theorem R204079 : Reach 204079 := rs (se 1 (by rfl) ⟨153059, by rfl⟩) R306119
theorem R73007 : Reach 73007 := rs (se 1 (by rfl) ⟨54755, by rfl⟩) R109511
theorem R73247 : Reach 73247 := rs (se 1 (by rfl) ⟨54935, by rfl⟩) R109871
theorem R73271 : Reach 73271 := rs (se 1 (by rfl) ⟨54953, by rfl⟩) R109907
theorem R73439 : Reach 73439 := rs (se 1 (by rfl) ⟨55079, by rfl⟩) R110159
theorem R368495 : Reach 368495 := rs (se 1 (by rfl) ⟨276371, by rfl⟩) R552743
theorem R106361 : Reach 106361 := rs (se 2 (by rfl) ⟨39885, by rfl⟩) R79771
theorem R73631 : Reach 73631 := rs (se 1 (by rfl) ⟨55223, by rfl⟩) R110447
theorem R270377 : Reach 270377 := rs (se 2 (by rfl) ⟨101391, by rfl⟩) R202783
theorem R73799 : Reach 73799 := rs (se 1 (by rfl) ⟨55349, by rfl⟩) R110699
theorem R172219 : Reach 172219 := rs (se 1 (by rfl) ⟨129164, by rfl⟩) R258329
theorem R73919 : Reach 73919 := rs (se 1 (by rfl) ⟨55439, by rfl⟩) R110879
theorem R74105 : Reach 74105 := rs (se 2 (by rfl) ⟨27789, by rfl⟩) R55579
theorem R107099 : Reach 107099 := rs (se 1 (by rfl) ⟨80324, by rfl⟩) R160649
theorem R74399 : Reach 74399 := rs (se 1 (by rfl) ⟨55799, by rfl⟩) R111599
theorem R566041 : Reach 566041 := rs (se 2 (by rfl) ⟨212265, by rfl⟩) R424531
theorem R567161 : Reach 567161 := rs (se 2 (by rfl) ⟨212685, by rfl⟩) R425371
theorem R109097 : Reach 109097 := rs (se 2 (by rfl) ⟨40911, by rfl⟩) R81823
theorem R76343 : Reach 76343 := rs (se 1 (by rfl) ⟨57257, by rfl⟩) R114515
theorem R371303 : Reach 371303 := rs (se 1 (by rfl) ⟨278477, by rfl⟩) R556955
theorem R76553 : Reach 76553 := rs (se 2 (by rfl) ⟨28707, by rfl⟩) R57415
theorem R76601 : Reach 76601 := rs (se 2 (by rfl) ⟨28725, by rfl⟩) R57451
theorem R207697 : Reach 207697 := rs (se 2 (by rfl) ⟨77886, by rfl⟩) R155773
theorem R274025 : Reach 274025 := rs (se 2 (by rfl) ⟨102759, by rfl⟩) R205519
theorem R2044115 : Reach 2044115 := rs (se 1 (by rfl) ⟨1533086, by rfl⟩) R3066173
theorem R1258021 : Reach 1258021 := rs (se 4 (by rfl) ⟨117939, by rfl⟩) R235879
theorem R701207 : Reach 701207 := rs (se 1 (by rfl) ⟨525905, by rfl⟩) R1051811
theorem R144479 : Reach 144479 := rs (se 1 (by rfl) ⟨108359, by rfl⟩) R216719
theorem R210043 : Reach 210043 := rs (se 1 (by rfl) ⟨157532, by rfl⟩) R315065
theorem R734771 : Reach 734771 := rs (se 1 (by rfl) ⟨551078, by rfl⟩) R1102157
theorem R47231 : Reach 47231 := rs (se 1 (by rfl) ⟨35423, by rfl⟩) R70847
theorem R47327 : Reach 47327 := rs (se 1 (by rfl) ⟨35495, by rfl⟩) R70991
theorem R47387 : Reach 47387 := rs (se 1 (by rfl) ⟨35540, by rfl⟩) R71081
theorem R47423 : Reach 47423 := rs (se 1 (by rfl) ⟨35567, by rfl⟩) R71135
theorem R47487 : Reach 47487 := rs (se 1 (by rfl) ⟨35615, by rfl⟩) R71231
theorem R47807 : Reach 47807 := rs (se 1 (by rfl) ⟨35855, by rfl⟩) R71711
theorem R244457 : Reach 244457 := rs (se 2 (by rfl) ⟨91671, by rfl⟩) R183343
theorem R310007 : Reach 310007 := rs (se 1 (by rfl) ⟨232505, by rfl⟩) R465011
theorem R80743 : Reach 80743 := rs (se 1 (by rfl) ⟨60557, by rfl⟩) R121115
theorem R1358795 : Reach 1358795 := rs (se 1 (by rfl) ⟨1019096, by rfl⟩) R2038193
theorem R48095 : Reach 48095 := rs (se 1 (by rfl) ⟨36071, by rfl⟩) R72143
theorem R48155 : Reach 48155 := rs (se 1 (by rfl) ⟨36116, by rfl⟩) R72233
theorem R48295 : Reach 48295 := rs (se 1 (by rfl) ⟨36221, by rfl⟩) R72443
theorem R48379 : Reach 48379 := rs (se 1 (by rfl) ⟨36284, by rfl⟩) R72569
theorem R113939 : Reach 113939 := rs (se 1 (by rfl) ⟨85454, by rfl⟩) R170909
theorem R114011 : Reach 114011 := rs (se 1 (by rfl) ⟨85508, by rfl⟩) R171017
theorem R277931 : Reach 277931 := rs (se 1 (by rfl) ⟨208448, by rfl⟩) R416897
theorem R81391 : Reach 81391 := rs (se 1 (by rfl) ⟨61043, by rfl⟩) R122087
theorem R179759 : Reach 179759 := rs (se 1 (by rfl) ⟨134819, by rfl⟩) R269639
theorem R48879 : Reach 48879 := rs (se 1 (by rfl) ⟨36659, by rfl⟩) R73319
theorem R48987 : Reach 48987 := rs (se 1 (by rfl) ⟨36740, by rfl⟩) R73481
theorem R49135 : Reach 49135 := rs (se 1 (by rfl) ⟨36851, by rfl⟩) R73703
theorem R180215 : Reach 180215 := rs (se 1 (by rfl) ⟨135161, by rfl⟩) R270323
theorem R49215 : Reach 49215 := rs (se 1 (by rfl) ⟨36911, by rfl⟩) R73823
theorem R49255 : Reach 49255 := rs (se 1 (by rfl) ⟨36941, by rfl⟩) R73883
theorem R49311 : Reach 49311 := rs (se 1 (by rfl) ⟨36983, by rfl⟩) R73967
theorem R180413 : Reach 180413 := rs (se 3 (by rfl) ⟨33827, by rfl⟩) R67655
theorem R82127 : Reach 82127 := rs (se 1 (by rfl) ⟨61595, by rfl⟩) R123191
theorem R377135 : Reach 377135 := rs (se 1 (by rfl) ⟨282851, by rfl⟩) R565703
theorem R475469 : Reach 475469 := rs (se 3 (by rfl) ⟨89150, by rfl⟩) R178301
theorem R49563 : Reach 49563 := rs (se 1 (by rfl) ⟨37172, by rfl⟩) R74345
theorem R49567 : Reach 49567 := rs (se 1 (by rfl) ⟨37175, by rfl⟩) R74351
theorem R49983 : Reach 49983 := rs (se 1 (by rfl) ⟨37487, by rfl⟩) R74975
theorem R50143 : Reach 50143 := rs (se 1 (by rfl) ⟨37607, by rfl⟩) R75215
theorem R50267 : Reach 50267 := rs (se 1 (by rfl) ⟨37700, by rfl⟩) R75401
theorem R83065 : Reach 83065 := rs (se 2 (by rfl) ⟨31149, by rfl⟩) R62299
theorem R50303 : Reach 50303 := rs (se 1 (by rfl) ⟨37727, by rfl⟩) R75455
theorem R181415 : Reach 181415 := rs (se 1 (by rfl) ⟨136061, by rfl⟩) R272123
theorem R50407 : Reach 50407 := rs (se 1 (by rfl) ⟨37805, by rfl⟩) R75611
theorem R50663 : Reach 50663 := rs (se 1 (by rfl) ⟨37997, by rfl⟩) R75995
theorem R50843 : Reach 50843 := rs (se 1 (by rfl) ⟨38132, by rfl⟩) R76265
theorem R50847 : Reach 50847 := rs (se 1 (by rfl) ⟨38135, by rfl⟩) R76271
theorem R116407 : Reach 116407 := rs (se 1 (by rfl) ⟨87305, by rfl⟩) R174611
theorem R51055 : Reach 51055 := rs (se 1 (by rfl) ⟨38291, by rfl⟩) R76583
theorem R182159 : Reach 182159 := rs (se 1 (by rfl) ⟨136619, by rfl⟩) R273239
theorem R51103 : Reach 51103 := rs (se 1 (by rfl) ⟨38327, by rfl⟩) R76655
theorem R247961 : Reach 247961 := rs (se 2 (by rfl) ⟨92985, by rfl⟩) R185971
theorem R575909 : Reach 575909 := rs (se 4 (by rfl) ⟨53991, by rfl⟩) R107983
theorem R2411441 : Reach 2411441 := rs (se 2 (by rfl) ⟨904290, by rfl⟩) R1808581
theorem R609353 : Reach 609353 := rs (se 2 (by rfl) ⟨228507, by rfl⟩) R457015
theorem R380051 : Reach 380051 := rs (se 1 (by rfl) ⟨285038, by rfl⟩) R570077
theorem R381023 : Reach 381023 := rs (se 1 (by rfl) ⟨285767, by rfl⟩) R571535
theorem R86143 : Reach 86143 := rs (se 1 (by rfl) ⟨64607, by rfl⟩) R129215
theorem R315521 : Reach 315521 := rs (se 2 (by rfl) ⟨118320, by rfl⟩) R236641
theorem R86251 : Reach 86251 := rs (se 1 (by rfl) ⟨64688, by rfl⟩) R129377
theorem R348407 : Reach 348407 := rs (se 1 (by rfl) ⟨261305, by rfl⟩) R522611
theorem R53887 : Reach 53887 := rs (se 1 (by rfl) ⟨40415, by rfl⟩) R80831
theorem R119711 : Reach 119711 := rs (se 1 (by rfl) ⟨89783, by rfl⟩) R179567
theorem R54319 : Reach 54319 := rs (se 1 (by rfl) ⟨40739, by rfl⟩) R81479
theorem R87161 : Reach 87161 := rs (se 2 (by rfl) ⟨32685, by rfl⟩) R65371
theorem R54607 : Reach 54607 := rs (se 1 (by rfl) ⟨40955, by rfl⟩) R81911
theorem R317033 : Reach 317033 := rs (se 2 (by rfl) ⟨118887, by rfl⟩) R237775
theorem R382967 : Reach 382967 := rs (se 1 (by rfl) ⟨287225, by rfl⟩) R574451
theorem R55291 : Reach 55291 := rs (se 1 (by rfl) ⟨41468, by rfl⟩) R82937
theorem R55327 : Reach 55327 := rs (se 1 (by rfl) ⟨41495, by rfl⟩) R82991
theorem R55471 : Reach 55471 := rs (se 1 (by rfl) ⟨41603, by rfl⟩) R83207
theorem R252233 : Reach 252233 := rs (se 2 (by rfl) ⟨94587, by rfl⟩) R189175
theorem R481619 : Reach 481619 := rs (se 1 (by rfl) ⟨361214, by rfl⟩) R722429
theorem R7428631 : Reach 7428631 := rs (se 1 (by rfl) ⟨5571473, by rfl⟩) R11142947
theorem R580283 : Reach 580283 := rs (se 1 (by rfl) ⟨435212, by rfl⟩) R870425
theorem R56191 : Reach 56191 := rs (se 1 (by rfl) ⟨42143, by rfl⟩) R84287
theorem R646055 : Reach 646055 := rs (se 1 (by rfl) ⟨484541, by rfl⟩) R969083
theorem R580547 : Reach 580547 := rs (se 1 (by rfl) ⟨435410, by rfl⟩) R870821
theorem R1137617 : Reach 1137617 := rs (se 2 (by rfl) ⟨426606, by rfl⟩) R853213
theorem R285929 : Reach 285929 := rs (se 2 (by rfl) ⟨107223, by rfl⟩) R214447
theorem R548207 : Reach 548207 := rs (se 1 (by rfl) ⟨411155, by rfl⟩) R822311
theorem R384425 : Reach 384425 := rs (se 2 (by rfl) ⟨144159, by rfl⟩) R288319
theorem R253529 : Reach 253529 := rs (se 2 (by rfl) ⟨95073, by rfl⟩) R190147
theorem R122543 : Reach 122543 := rs (se 1 (by rfl) ⟨91907, by rfl⟩) R183815
theorem R319439 : Reach 319439 := rs (se 1 (by rfl) ⟨239579, by rfl⟩) R479159
theorem R189161 : Reach 189161 := rs (se 2 (by rfl) ⟨70935, by rfl⟩) R141871
theorem R1794797 : Reach 1794797 := rs (se 3 (by rfl) ⟨336524, by rfl⟩) R673049
theorem R189479 : Reach 189479 := rs (se 1 (by rfl) ⟨142109, by rfl⟩) R284219
theorem R189935 : Reach 189935 := rs (se 1 (by rfl) ⟨142451, by rfl⟩) R284903
theorem R288479 : Reach 288479 := rs (se 1 (by rfl) ⟨216359, by rfl⟩) R432719
theorem R9038141 : Reach 9038141 := rs (se 3 (by rfl) ⟨1694651, by rfl⟩) R3389303
theorem R158183 : Reach 158183 := rs (se 1 (by rfl) ⟨118637, by rfl⟩) R237275
theorem R158375 : Reach 158375 := rs (se 1 (by rfl) ⟨118781, by rfl⟩) R237563
theorem R191443 : Reach 191443 := rs (se 1 (by rfl) ⟨143582, by rfl⟩) R287165
theorem R453599 : Reach 453599 := rs (se 1 (by rfl) ⟨340199, by rfl⟩) R680399
theorem R126299 : Reach 126299 := rs (se 1 (by rfl) ⟨94724, by rfl⟩) R189449
theorem R93631 : Reach 93631 := rs (se 1 (by rfl) ⟨70223, by rfl⟩) R140447
theorem R60907 : Reach 60907 := rs (se 1 (by rfl) ⟨45680, by rfl⟩) R91361
theorem R323155 : Reach 323155 := rs (se 1 (by rfl) ⟨242366, by rfl⟩) R484733
theorem R159677 : Reach 159677 := rs (se 3 (by rfl) ⟨29939, by rfl⟩) R59879
theorem R159839 : Reach 159839 := rs (se 1 (by rfl) ⟨119879, by rfl⟩) R239759
theorem R192851 : Reach 192851 := rs (se 1 (by rfl) ⟨144638, by rfl⟩) R289277
theorem R160157 : Reach 160157 := rs (se 3 (by rfl) ⟨30029, by rfl⟩) R60059
theorem R193583 : Reach 193583 := rs (se 1 (by rfl) ⟨145187, by rfl⟩) R290375
theorem R1406105 : Reach 1406105 := rs (se 2 (by rfl) ⟨527289, by rfl⟩) R1054579
theorem R95393 : Reach 95393 := rs (se 2 (by rfl) ⟨35772, by rfl⟩) R71545
theorem R161405 : Reach 161405 := rs (se 3 (by rfl) ⟨30263, by rfl⟩) R60527
theorem R457325 : Reach 457325 := rs (se 3 (by rfl) ⟨85748, by rfl⟩) R171497
theorem R162809 : Reach 162809 := rs (se 2 (by rfl) ⟨61053, by rfl⟩) R122107
theorem R64567 : Reach 64567 := rs (se 1 (by rfl) ⟨48425, by rfl⟩) R96851
theorem R622475 : Reach 622475 := rs (se 1 (by rfl) ⟨466856, by rfl⟩) R933713
theorem R163835 : Reach 163835 := rs (se 1 (by rfl) ⟨122876, by rfl⟩) R245753
theorem R229625 : Reach 229625 := rs (se 2 (by rfl) ⟨86109, by rfl⟩) R172219
theorem R754721 : Reach 754721 := rs (se 2 (by rfl) ⟨283020, by rfl⟩) R566041
theorem R165307 : Reach 165307 := rs (se 1 (by rfl) ⟨123980, by rfl⟩) R247961
theorem R1607627 : Reach 1607627 := rs (se 1 (by rfl) ⟨1205720, by rfl⟩) R2411441
theorem R68207 : Reach 68207 := rs (se 1 (by rfl) ⟨51155, by rfl⟩) R102311
theorem R232271 : Reach 232271 := rs (se 1 (by rfl) ⟨174203, by rfl⟩) R348407
theorem R134273 : Reach 134273 := rs (se 2 (by rfl) ⟨50352, by rfl⟩) R100705
theorem R364013 : Reach 364013 := rs (se 3 (by rfl) ⟨68252, by rfl⟩) R136505
theorem R168155 : Reach 168155 := rs (se 1 (by rfl) ⟨126116, by rfl⟩) R252233
theorem R430703 : Reach 430703 := rs (se 1 (by rfl) ⟨323027, by rfl⟩) R646055
theorem R758411 : Reach 758411 := rs (se 1 (by rfl) ⟨568808, by rfl⟩) R1137617
theorem R365471 : Reach 365471 := rs (se 1 (by rfl) ⟨274103, by rfl⟩) R548207
theorem R169019 : Reach 169019 := rs (se 1 (by rfl) ⟨126764, by rfl⟩) R253529
theorem R70907 : Reach 70907 := rs (se 1 (by rfl) ⟨53180, by rfl⟩) R106361
theorem R71399 : Reach 71399 := rs (se 1 (by rfl) ⟨53549, by rfl⟩) R107099
theorem R1677361 : Reach 1677361 := rs (se 2 (by rfl) ⟨629010, by rfl⟩) R1258021
theorem R9443465 : Reach 9443465 := rs (se 2 (by rfl) ⟨3541299, by rfl⟩) R7082599
theorem R71849 : Reach 71849 := rs (se 2 (by rfl) ⟨26943, by rfl⟩) R53887
theorem R72425 : Reach 72425 := rs (se 2 (by rfl) ⟨27159, by rfl⟩) R54319
theorem R105455 : Reach 105455 := rs (se 1 (by rfl) ⟨79091, by rfl⟩) R158183
theorem R72731 : Reach 72731 := rs (se 1 (by rfl) ⟨54548, by rfl⟩) R109097
theorem R72809 : Reach 72809 := rs (se 2 (by rfl) ⟨27303, by rfl⟩) R54607
theorem R826685 : Reach 826685 := rs (se 3 (by rfl) ⟨155003, by rfl⟩) R310007
theorem R302399 : Reach 302399 := rs (se 1 (by rfl) ⟨226799, by rfl⟩) R453599
theorem R106451 : Reach 106451 := rs (se 1 (by rfl) ⟨79838, by rfl⟩) R159677
theorem R73721 : Reach 73721 := rs (se 2 (by rfl) ⟨27645, by rfl⟩) R55291
theorem R73769 : Reach 73769 := rs (se 2 (by rfl) ⟨27663, by rfl⟩) R55327
theorem R106559 : Reach 106559 := rs (se 1 (by rfl) ⟨79919, by rfl⟩) R159839
theorem R73961 : Reach 73961 := rs (se 2 (by rfl) ⟨27735, by rfl⟩) R55471
theorem R106771 : Reach 106771 := rs (se 1 (by rfl) ⟨80078, by rfl⟩) R160157
theorem R467471 : Reach 467471 := rs (se 1 (by rfl) ⟨350603, by rfl⟩) R701207
theorem R9904841 : Reach 9904841 := rs (se 2 (by rfl) ⟨3714315, by rfl⟩) R7428631
theorem R107603 : Reach 107603 := rs (se 1 (by rfl) ⟨80702, by rfl⟩) R161405
theorem R107657 : Reach 107657 := rs (se 2 (by rfl) ⟨40371, by rfl⟩) R80743
theorem R74921 : Reach 74921 := rs (se 2 (by rfl) ⟨28095, by rfl⟩) R56191
theorem R272105 : Reach 272105 := rs (se 2 (by rfl) ⟨102039, by rfl⟩) R204079
theorem R304883 : Reach 304883 := rs (se 1 (by rfl) ⟨228662, by rfl⟩) R457325
theorem R108521 : Reach 108521 := rs (se 2 (by rfl) ⟨40695, by rfl⟩) R81391
theorem R108539 : Reach 108539 := rs (se 1 (by rfl) ⟨81404, by rfl⟩) R162809
theorem R75959 : Reach 75959 := rs (se 1 (by rfl) ⟨56969, by rfl⟩) R113939
theorem R76007 : Reach 76007 := rs (se 1 (by rfl) ⟨57005, by rfl⟩) R114011
theorem R109223 : Reach 109223 := rs (se 1 (by rfl) ⟨81917, by rfl⟩) R163835
theorem R929717 : Reach 929717 := rs (se 5 (by rfl) ⟨43580, by rfl⟩) R87161
theorem R6795251 : Reach 6795251 := rs (se 1 (by rfl) ⟨5096438, by rfl⟩) R10192877
theorem R110753 : Reach 110753 := rs (se 2 (by rfl) ⟨41532, by rfl⟩) R83065
theorem R111131 : Reach 111131 := rs (se 1 (by rfl) ⟨83348, by rfl⟩) R166697
theorem R406235 : Reach 406235 := rs (se 1 (by rfl) ⟨304676, by rfl⟩) R609353
theorem R1553651 : Reach 1553651 := rs (se 1 (by rfl) ⟨1165238, by rfl⟩) R2330477
theorem R242999 : Reach 242999 := rs (se 1 (by rfl) ⟨182249, by rfl⟩) R364499
theorem R210347 : Reach 210347 := rs (se 1 (by rfl) ⟨157760, by rfl⟩) R315521
theorem R112079 : Reach 112079 := rs (se 1 (by rfl) ⟨84059, by rfl⟩) R168119
theorem R1488451 : Reach 1488451 := rs (se 1 (by rfl) ⟨1116338, by rfl⟩) R2232677
theorem R112319 : Reach 112319 := rs (se 1 (by rfl) ⟨84239, by rfl⟩) R168479
theorem R79807 : Reach 79807 := rs (se 1 (by rfl) ⟨59855, by rfl⟩) R119711
theorem R112859 : Reach 112859 := rs (se 1 (by rfl) ⟨84644, by rfl⟩) R169289
theorem R47355 : Reach 47355 := rs (se 1 (by rfl) ⟨35516, by rfl⟩) R71033
theorem R211355 : Reach 211355 := rs (se 1 (by rfl) ⟨158516, by rfl⟩) R317033
theorem R276929 : Reach 276929 := rs (se 2 (by rfl) ⟨103848, by rfl⟩) R207697
theorem R244295 : Reach 244295 := rs (se 1 (by rfl) ⟨183221, by rfl⟩) R366443
theorem R47719 : Reach 47719 := rs (se 1 (by rfl) ⟨35789, by rfl⟩) R71579
theorem R179167 : Reach 179167 := rs (se 1 (by rfl) ⟨134375, by rfl⟩) R268751
theorem R48159 : Reach 48159 := rs (se 1 (by rfl) ⟨36119, by rfl⟩) R72239
theorem R48191 : Reach 48191 := rs (se 1 (by rfl) ⟨36143, by rfl⟩) R72287
theorem R277613 : Reach 277613 := rs (se 3 (by rfl) ⟨52052, by rfl⟩) R104105
theorem R113831 : Reach 113831 := rs (se 1 (by rfl) ⟨85373, by rfl⟩) R170747
theorem R769277 : Reach 769277 := rs (se 3 (by rfl) ⟨144239, by rfl⟩) R288479
theorem R48431 : Reach 48431 := rs (se 1 (by rfl) ⟨36323, by rfl⟩) R72647
theorem R81209 : Reach 81209 := rs (se 2 (by rfl) ⟨30453, by rfl⟩) R60907
theorem R48511 : Reach 48511 := rs (se 1 (by rfl) ⟨36383, by rfl⟩) R72767
theorem R48671 : Reach 48671 := rs (se 1 (by rfl) ⟨36503, by rfl⟩) R73007
theorem R48831 : Reach 48831 := rs (se 1 (by rfl) ⟨36623, by rfl⟩) R73247
theorem R48847 : Reach 48847 := rs (se 1 (by rfl) ⟨36635, by rfl⟩) R73271
theorem R81695 : Reach 81695 := rs (se 1 (by rfl) ⟨61271, by rfl⟩) R122543
theorem R48959 : Reach 48959 := rs (se 1 (by rfl) ⟨36719, by rfl⟩) R73439
theorem R245663 : Reach 245663 := rs (se 1 (by rfl) ⟨184247, by rfl⟩) R368495
theorem R49087 : Reach 49087 := rs (se 1 (by rfl) ⟨36815, by rfl⟩) R73631
theorem R212959 : Reach 212959 := rs (se 1 (by rfl) ⟨159719, by rfl⟩) R319439
theorem R180251 : Reach 180251 := rs (se 1 (by rfl) ⟨135188, by rfl⟩) R270377
theorem R49199 : Reach 49199 := rs (se 1 (by rfl) ⟨36899, by rfl⟩) R73799
theorem R49279 : Reach 49279 := rs (se 1 (by rfl) ⟨36959, by rfl⟩) R73919
theorem R114857 : Reach 114857 := rs (se 2 (by rfl) ⟨43071, by rfl⟩) R86143
theorem R49403 : Reach 49403 := rs (se 1 (by rfl) ⟨37052, by rfl⟩) R74105
theorem R115001 : Reach 115001 := rs (se 2 (by rfl) ⟨43125, by rfl⟩) R86251
theorem R49599 : Reach 49599 := rs (se 1 (by rfl) ⟨37199, by rfl⟩) R74399
theorem R1196531 : Reach 1196531 := rs (se 1 (by rfl) ⟨897398, by rfl⟩) R1794797
theorem R378107 : Reach 378107 := rs (se 1 (by rfl) ⟨283580, by rfl⟩) R567161
theorem R280057 : Reach 280057 := rs (se 2 (by rfl) ⟨105021, by rfl⟩) R210043
theorem R50895 : Reach 50895 := rs (se 1 (by rfl) ⟨38171, by rfl⟩) R76343
theorem R247535 : Reach 247535 := rs (se 1 (by rfl) ⟨185651, by rfl⟩) R371303
theorem R51035 : Reach 51035 := rs (se 1 (by rfl) ⟨38276, by rfl⟩) R76553
theorem R51067 : Reach 51067 := rs (se 1 (by rfl) ⟨38300, by rfl⟩) R76601
theorem R84199 : Reach 84199 := rs (se 1 (by rfl) ⟨63149, by rfl⟩) R126299
theorem R182569 : Reach 182569 := rs (se 2 (by rfl) ⟨68463, by rfl⟩) R136927
theorem R182683 : Reach 182683 := rs (se 1 (by rfl) ⟨137012, by rfl⟩) R274025
theorem R1362743 : Reach 1362743 := rs (se 1 (by rfl) ⟨1022057, by rfl⟩) R2044115
theorem R1723493 : Reach 1723493 := rs (se 4 (by rfl) ⟨161577, by rfl⟩) R323155
theorem R937403 : Reach 937403 := rs (se 1 (by rfl) ⟨703052, by rfl⟩) R1406105
theorem R86089 : Reach 86089 := rs (se 2 (by rfl) ⟨32283, by rfl⟩) R64567
theorem R905863 : Reach 905863 := rs (se 1 (by rfl) ⟨679397, by rfl⟩) R1358795
theorem R185287 : Reach 185287 := rs (se 1 (by rfl) ⟨138965, by rfl⟩) R277931
theorem R119839 : Reach 119839 := rs (se 1 (by rfl) ⟨89879, by rfl⟩) R179759
theorem R414983 : Reach 414983 := rs (se 1 (by rfl) ⟨311237, by rfl⟩) R622475
theorem R120143 : Reach 120143 := rs (se 1 (by rfl) ⟨90107, by rfl⟩) R180215
theorem R120275 : Reach 120275 := rs (se 1 (by rfl) ⟨90206, by rfl⟩) R180413
theorem R54751 : Reach 54751 := rs (se 1 (by rfl) ⟨41063, by rfl⟩) R82127
theorem R251423 : Reach 251423 := rs (se 1 (by rfl) ⟨188567, by rfl⟩) R377135
theorem R316979 : Reach 316979 := rs (se 1 (by rfl) ⟨237734, by rfl⟩) R475469
theorem R120943 : Reach 120943 := rs (se 1 (by rfl) ⟨90707, by rfl⟩) R181415
theorem R121439 : Reach 121439 := rs (se 1 (by rfl) ⟨91079, by rfl⟩) R182159
theorem R383939 : Reach 383939 := rs (se 1 (by rfl) ⟨287954, by rfl⟩) R575909
theorem R253367 : Reach 253367 := rs (se 1 (by rfl) ⟨190025, by rfl⟩) R380051
theorem R155209 : Reach 155209 := rs (se 2 (by rfl) ⟨58203, by rfl⟩) R116407
theorem R941867 : Reach 941867 := rs (se 1 (by rfl) ⟨706400, by rfl⟩) R1412801
theorem R254015 : Reach 254015 := rs (se 1 (by rfl) ⟨190511, by rfl⟩) R381023
theorem R255257 : Reach 255257 := rs (se 2 (by rfl) ⟨95721, by rfl⟩) R191443
theorem R255311 : Reach 255311 := rs (se 1 (by rfl) ⟨191483, by rfl⟩) R382967
theorem R91631 : Reach 91631 := rs (se 1 (by rfl) ⟨68723, by rfl⟩) R137447
theorem R321079 : Reach 321079 := rs (se 1 (by rfl) ⟨240809, by rfl⟩) R481619
theorem R386855 : Reach 386855 := rs (se 1 (by rfl) ⟨290141, by rfl⟩) R580283
theorem R124841 : Reach 124841 := rs (se 2 (by rfl) ⟨46815, by rfl⟩) R93631
theorem R387031 : Reach 387031 := rs (se 1 (by rfl) ⟨290273, by rfl⟩) R580547
theorem R190619 : Reach 190619 := rs (se 1 (by rfl) ⟨142964, by rfl⟩) R285929
theorem R256283 : Reach 256283 := rs (se 1 (by rfl) ⟨192212, by rfl⟩) R384425
theorem R126107 : Reach 126107 := rs (se 1 (by rfl) ⟨94580, by rfl⟩) R189161
theorem R126319 : Reach 126319 := rs (se 1 (by rfl) ⟨94739, by rfl⟩) R189479
theorem R126461 : Reach 126461 := rs (se 3 (by rfl) ⟨23711, by rfl⟩) R47423
theorem R126623 : Reach 126623 := rs (se 1 (by rfl) ⟨94967, by rfl⟩) R189935
theorem R6025427 : Reach 6025427 := rs (se 1 (by rfl) ⟨4519070, by rfl⟩) R9038141
theorem R422333 : Reach 422333 := rs (se 3 (by rfl) ⟨79187, by rfl⟩) R158375
theorem R128567 : Reach 128567 := rs (se 1 (by rfl) ⟨96425, by rfl⟩) R192851
theorem R129055 : Reach 129055 := rs (se 1 (by rfl) ⟨96791, by rfl⟩) R193583
theorem R96319 : Reach 96319 := rs (se 1 (by rfl) ⟨72239, by rfl⟩) R144479
theorem R63595 : Reach 63595 := rs (se 1 (by rfl) ⟨47696, by rfl⟩) R95393
theorem R489847 : Reach 489847 := rs (se 1 (by rfl) ⟨367385, by rfl⟩) R734771
theorem R162971 : Reach 162971 := rs (se 1 (by rfl) ⟨122228, by rfl⟩) R244457
theorem R165023 : Reach 165023 := rs (se 1 (by rfl) ⟨123767, by rfl⟩) R247535
theorem R1246589 : Reach 1246589 := rs (se 3 (by rfl) ⟨233735, by rfl⟩) R467471
theorem R1148995 : Reach 1148995 := rs (se 1 (by rfl) ⟨861746, by rfl⟩) R1723493
theorem R428105 : Reach 428105 := rs (se 2 (by rfl) ⟨160539, by rfl⟩) R321079
theorem R624935 : Reach 624935 := rs (se 1 (by rfl) ⟨468701, by rfl⟩) R937403
theorem R167615 : Reach 167615 := rs (se 1 (by rfl) ⟨125711, by rfl⟩) R251423
theorem R6295643 : Reach 6295643 := rs (se 1 (by rfl) ⟨4721732, by rfl⟩) R9443465
theorem R168425 : Reach 168425 := rs (se 2 (by rfl) ⟨63159, by rfl⟩) R126319
theorem R70303 : Reach 70303 := rs (se 1 (by rfl) ⟨52727, by rfl⟩) R105455
theorem R201599 : Reach 201599 := rs (se 1 (by rfl) ⟨151199, by rfl⟩) R302399
theorem R168911 : Reach 168911 := rs (se 1 (by rfl) ⟨126683, by rfl⟩) R253367
theorem R627911 : Reach 627911 := rs (se 1 (by rfl) ⟨470933, by rfl⟩) R941867
theorem R70967 : Reach 70967 := rs (se 1 (by rfl) ⟨53225, by rfl⟩) R106451
theorem R71039 : Reach 71039 := rs (se 1 (by rfl) ⟨53279, by rfl⟩) R106559
theorem R169343 : Reach 169343 := rs (se 1 (by rfl) ⟨127007, by rfl⟩) R254015
theorem R71735 : Reach 71735 := rs (se 1 (by rfl) ⟨53801, by rfl⟩) R107603
theorem R71771 : Reach 71771 := rs (se 1 (by rfl) ⟨53828, by rfl⟩) R107657
theorem R170171 : Reach 170171 := rs (se 1 (by rfl) ⟨127628, by rfl⟩) R255257
theorem R170207 : Reach 170207 := rs (se 1 (by rfl) ⟨127655, by rfl⟩) R255311
theorem R203255 : Reach 203255 := rs (se 1 (by rfl) ⟨152441, by rfl⟩) R304883
theorem R72347 : Reach 72347 := rs (se 1 (by rfl) ⟨54260, by rfl⟩) R108521
theorem R72359 : Reach 72359 := rs (se 1 (by rfl) ⟨54269, by rfl⟩) R108539
theorem R170855 : Reach 170855 := rs (se 1 (by rfl) ⟨128141, by rfl⟩) R256283
theorem R72815 : Reach 72815 := rs (se 1 (by rfl) ⟨54611, by rfl⟩) R109223
theorem R73001 : Reach 73001 := rs (se 2 (by rfl) ⟨27375, by rfl⟩) R54751
theorem R106409 : Reach 106409 := rs (se 2 (by rfl) ⟨39903, by rfl⟩) R79807
theorem R4530167 : Reach 4530167 := rs (se 1 (by rfl) ⟨3397625, by rfl⟩) R6795251
theorem R172073 : Reach 172073 := rs (se 2 (by rfl) ⟨64527, by rfl⟩) R129055
theorem R2236481 : Reach 2236481 := rs (se 2 (by rfl) ⟨838680, by rfl⟩) R1677361
theorem R73835 : Reach 73835 := rs (se 1 (by rfl) ⟨55376, by rfl⟩) R110753
theorem R74087 : Reach 74087 := rs (se 1 (by rfl) ⟨55565, by rfl⟩) R111131
theorem R270823 : Reach 270823 := rs (se 1 (by rfl) ⟨203117, by rfl⟩) R406235
theorem R140231 : Reach 140231 := rs (se 1 (by rfl) ⟨105173, by rfl⟩) R210347
theorem R74719 : Reach 74719 := rs (se 1 (by rfl) ⟨56039, by rfl⟩) R112079
theorem R74879 : Reach 74879 := rs (se 1 (by rfl) ⟨56159, by rfl⟩) R112319
theorem R238889 : Reach 238889 := rs (se 2 (by rfl) ⟨89583, by rfl⟩) R179167
theorem R75239 : Reach 75239 := rs (se 1 (by rfl) ⟨56429, by rfl⟩) R112859
theorem R140903 : Reach 140903 := rs (se 1 (by rfl) ⟨105677, by rfl⟩) R211355
theorem R206945 : Reach 206945 := rs (se 2 (by rfl) ⟨77604, by rfl⟩) R155209
theorem R108647 : Reach 108647 := rs (se 1 (by rfl) ⟨81485, by rfl⟩) R162971
theorem R75887 : Reach 75887 := rs (se 1 (by rfl) ⟨56915, by rfl⟩) R113831
theorem R76571 : Reach 76571 := rs (se 1 (by rfl) ⟨57428, by rfl⟩) R114857
theorem R76667 : Reach 76667 := rs (se 1 (by rfl) ⟨57500, by rfl⟩) R115001
theorem R797687 : Reach 797687 := rs (se 1 (by rfl) ⟨598265, by rfl⟩) R1196531
theorem R142361 : Reach 142361 := rs (se 2 (by rfl) ⟨53385, by rfl⟩) R106771
theorem R503147 : Reach 503147 := rs (se 1 (by rfl) ⟨377360, by rfl⟩) R754721
theorem R373409 : Reach 373409 := rs (se 2 (by rfl) ⟨140028, by rfl⟩) R280057
theorem R242675 : Reach 242675 := rs (se 1 (by rfl) ⟨182006, by rfl⟩) R364013
theorem R112103 : Reach 112103 := rs (se 1 (by rfl) ⟨84077, by rfl⟩) R168155
theorem R112265 : Reach 112265 := rs (se 2 (by rfl) ⟨42099, by rfl⟩) R84199
theorem R243425 : Reach 243425 := rs (se 2 (by rfl) ⟨91284, by rfl⟩) R182569
theorem R505607 : Reach 505607 := rs (se 1 (by rfl) ⟨379205, by rfl⟩) R758411
theorem R243577 : Reach 243577 := rs (se 2 (by rfl) ⟨91341, by rfl⟩) R182683
theorem R243647 : Reach 243647 := rs (se 1 (by rfl) ⟨182735, by rfl⟩) R365471
theorem R112679 : Reach 112679 := rs (se 1 (by rfl) ⟨84509, by rfl⟩) R169019
theorem R47271 : Reach 47271 := rs (se 1 (by rfl) ⟨35453, by rfl⟩) R70907
theorem R276655 : Reach 276655 := rs (se 1 (by rfl) ⟨207491, by rfl⟩) R414983
theorem R80095 : Reach 80095 := rs (se 1 (by rfl) ⟨60071, by rfl⟩) R120143
theorem R80183 : Reach 80183 := rs (se 1 (by rfl) ⟨60137, by rfl⟩) R120275
theorem R211319 : Reach 211319 := rs (se 1 (by rfl) ⟨158489, by rfl⟩) R316979
theorem R47599 : Reach 47599 := rs (se 1 (by rfl) ⟨35699, by rfl⟩) R71399
theorem R47899 : Reach 47899 := rs (se 1 (by rfl) ⟨35924, by rfl⟩) R71849
theorem R80959 : Reach 80959 := rs (se 1 (by rfl) ⟨60719, by rfl⟩) R121439
theorem R48283 : Reach 48283 := rs (se 1 (by rfl) ⟨36212, by rfl⟩) R72425
theorem R48487 : Reach 48487 := rs (se 1 (by rfl) ⟨36365, by rfl⟩) R72731
theorem R48539 : Reach 48539 := rs (se 1 (by rfl) ⟨36404, by rfl⟩) R72809
theorem R49147 : Reach 49147 := rs (se 1 (by rfl) ⟨36860, by rfl⟩) R73721
theorem R49179 : Reach 49179 := rs (se 1 (by rfl) ⟨36884, by rfl⟩) R73769
theorem R114785 : Reach 114785 := rs (se 2 (by rfl) ⟨43044, by rfl⟩) R86089
theorem R49307 : Reach 49307 := rs (se 1 (by rfl) ⟨36980, by rfl⟩) R73961
theorem R6603227 : Reach 6603227 := rs (se 1 (by rfl) ⟨4952420, by rfl⟩) R9904841
theorem R49947 : Reach 49947 := rs (se 1 (by rfl) ⟨37460, by rfl⟩) R74921
theorem R181403 : Reach 181403 := rs (se 1 (by rfl) ⟨136052, by rfl⟩) R272105
theorem R247049 : Reach 247049 := rs (se 2 (by rfl) ⟨92643, by rfl⟩) R185287
theorem R83227 : Reach 83227 := rs (se 1 (by rfl) ⟨62420, by rfl⟩) R124841
theorem R50639 : Reach 50639 := rs (se 1 (by rfl) ⟨37979, by rfl⟩) R75959
theorem R50671 : Reach 50671 := rs (se 1 (by rfl) ⟨38003, by rfl⟩) R76007
theorem R181885 : Reach 181885 := rs (se 3 (by rfl) ⟨34103, by rfl⟩) R68207
theorem R1984601 : Reach 1984601 := rs (se 2 (by rfl) ⟨744225, by rfl⟩) R1488451
theorem R84071 : Reach 84071 := rs (se 1 (by rfl) ⟨63053, by rfl⟩) R126107
theorem R84307 : Reach 84307 := rs (se 1 (by rfl) ⟨63230, by rfl⟩) R126461
theorem R84415 : Reach 84415 := rs (se 1 (by rfl) ⟨63311, by rfl⟩) R126623
theorem R4016951 : Reach 4016951 := rs (se 1 (by rfl) ⟨3012713, by rfl⟩) R6025427
theorem R84793 : Reach 84793 := rs (se 2 (by rfl) ⟨31797, by rfl⟩) R63595
theorem R281555 : Reach 281555 := rs (se 1 (by rfl) ⟨211166, by rfl⟩) R422333
theorem R1035767 : Reach 1035767 := rs (se 1 (by rfl) ⟨776825, by rfl⟩) R1553651
theorem R85711 : Reach 85711 := rs (se 1 (by rfl) ⟨64283, by rfl⟩) R128567
theorem R184619 : Reach 184619 := rs (se 1 (by rfl) ⟨138464, by rfl⟩) R276929
theorem R185075 : Reach 185075 := rs (se 1 (by rfl) ⟨138806, by rfl⟩) R277613
theorem R512851 : Reach 512851 := rs (se 1 (by rfl) ⟨384638, by rfl⟩) R769277
theorem R54139 : Reach 54139 := rs (se 1 (by rfl) ⟨40604, by rfl⟩) R81209
theorem R54463 : Reach 54463 := rs (se 1 (by rfl) ⟨40847, by rfl⟩) R81695
theorem R283945 : Reach 283945 := rs (se 2 (by rfl) ⟨106479, by rfl⟩) R212959
theorem R120167 : Reach 120167 := rs (se 1 (by rfl) ⟨90125, by rfl⟩) R180251
theorem R153083 : Reach 153083 := rs (se 1 (by rfl) ⟨114812, by rfl⟩) R229625
theorem R645029 : Reach 645029 := rs (se 4 (by rfl) ⟨60471, by rfl⟩) R120943
theorem R252071 : Reach 252071 := rs (se 1 (by rfl) ⟨189053, by rfl⟩) R378107
theorem R1071751 : Reach 1071751 := rs (se 1 (by rfl) ⟨803813, by rfl⟩) R1607627
theorem R908495 : Reach 908495 := rs (se 1 (by rfl) ⟨681371, by rfl⟩) R1362743
theorem R154847 : Reach 154847 := rs (se 1 (by rfl) ⟨116135, by rfl⟩) R232271
theorem R220409 : Reach 220409 := rs (se 2 (by rfl) ⟨82653, by rfl⟩) R165307
theorem R89515 : Reach 89515 := rs (se 1 (by rfl) ⟨67136, by rfl⟩) R134273
theorem R516041 : Reach 516041 := rs (se 2 (by rfl) ⟨193515, by rfl⟩) R387031
theorem R287135 : Reach 287135 := rs (se 1 (by rfl) ⟨215351, by rfl⟩) R430703
theorem R254501 : Reach 254501 := rs (se 4 (by rfl) ⟨23859, by rfl⟩) R47719
theorem R255959 : Reach 255959 := rs (se 1 (by rfl) ⟨191969, by rfl⟩) R383939
theorem R551123 : Reach 551123 := rs (se 1 (by rfl) ⟨413342, by rfl⟩) R826685
theorem R1207817 : Reach 1207817 := rs (se 2 (by rfl) ⟨452931, by rfl⟩) R905863
theorem R61087 : Reach 61087 := rs (se 1 (by rfl) ⟨45815, by rfl⟩) R91631
theorem R257903 : Reach 257903 := rs (se 1 (by rfl) ⟨193427, by rfl⟩) R386855
theorem R159785 : Reach 159785 := rs (se 2 (by rfl) ⟨59919, by rfl⟩) R119839
theorem R127079 : Reach 127079 := rs (se 1 (by rfl) ⟨95309, by rfl⟩) R190619
theorem R619811 : Reach 619811 := rs (se 1 (by rfl) ⟨464858, by rfl⟩) R929717
theorem R128425 : Reach 128425 := rs (se 2 (by rfl) ⟨48159, by rfl⟩) R96319
theorem R653129 : Reach 653129 := rs (se 2 (by rfl) ⟨244923, by rfl⟩) R489847
theorem R161999 : Reach 161999 := rs (se 1 (by rfl) ⟨121499, by rfl⟩) R242999
theorem R162863 : Reach 162863 := rs (se 1 (by rfl) ⟨122147, by rfl⟩) R244295
theorem R163775 : Reach 163775 := rs (se 1 (by rfl) ⟨122831, by rfl⟩) R245663
theorem R361097 : Reach 361097 := rs (se 2 (by rfl) ⟨135411, by rfl⟩) R270823
theorem R164699 : Reach 164699 := rs (se 1 (by rfl) ⟨123524, by rfl⟩) R247049
theorem R99625 : Reach 99625 := rs (se 2 (by rfl) ⟨37359, by rfl⟩) R74719
theorem R4197095 : Reach 4197095 := rs (se 1 (by rfl) ⟨3147821, by rfl⟩) R6295643
theorem R134399 : Reach 134399 := rs (se 1 (by rfl) ⟨100799, by rfl⟩) R201599
theorem R102055 : Reach 102055 := rs (se 1 (by rfl) ⟨76541, by rfl⟩) R153083
theorem R430019 : Reach 430019 := rs (se 1 (by rfl) ⟨322514, by rfl⟩) R645029
theorem R168047 : Reach 168047 := rs (se 1 (by rfl) ⟨126035, by rfl⟩) R252071
theorem R135503 : Reach 135503 := rs (se 1 (by rfl) ⟨101627, by rfl⟩) R203255
theorem R103231 : Reach 103231 := rs (se 1 (by rfl) ⟨77423, by rfl⟩) R154847
theorem R70939 : Reach 70939 := rs (se 1 (by rfl) ⟨53204, by rfl⟩) R106409
theorem R3020111 : Reach 3020111 := rs (se 1 (by rfl) ⟨2265083, by rfl⟩) R4530167
theorem R169667 : Reach 169667 := rs (se 1 (by rfl) ⟨127250, by rfl⟩) R254501
theorem R72185 : Reach 72185 := rs (se 2 (by rfl) ⟨27069, by rfl⟩) R54139
theorem R170639 : Reach 170639 := rs (se 1 (by rfl) ⟨127979, by rfl⟩) R255959
theorem R137963 : Reach 137963 := rs (se 1 (by rfl) ⟨103472, by rfl⟩) R206945
theorem R72431 : Reach 72431 := rs (se 1 (by rfl) ⟨54323, by rfl⟩) R108647
theorem R367415 : Reach 367415 := rs (se 1 (by rfl) ⟨275561, by rfl⟩) R551123
theorem R72617 : Reach 72617 := rs (se 2 (by rfl) ⟨27231, by rfl⟩) R54463
theorem R171233 : Reach 171233 := rs (se 2 (by rfl) ⟨64212, by rfl⟩) R128425
theorem R531791 : Reach 531791 := rs (se 1 (by rfl) ⟨398843, by rfl⟩) R797687
theorem R335431 : Reach 335431 := rs (se 1 (by rfl) ⟨251573, by rfl⟩) R503147
theorem R171935 : Reach 171935 := rs (se 1 (by rfl) ⟨128951, by rfl⟩) R257903
theorem R106523 : Reach 106523 := rs (se 1 (by rfl) ⟨79892, by rfl⟩) R159785
theorem R368873 : Reach 368873 := rs (se 2 (by rfl) ⟨138327, by rfl⟩) R276655
theorem R106793 : Reach 106793 := rs (se 2 (by rfl) ⟨40047, by rfl⟩) R80095
theorem R74735 : Reach 74735 := rs (se 1 (by rfl) ⟨56051, by rfl⟩) R112103
theorem R74843 : Reach 74843 := rs (se 1 (by rfl) ⟨56132, by rfl⟩) R112265
theorem R435419 : Reach 435419 := rs (se 1 (by rfl) ⟨326564, by rfl⟩) R653129
theorem R2762045 : Reach 2762045 := rs (se 3 (by rfl) ⟨517883, by rfl⟩) R1035767
theorem R75119 : Reach 75119 := rs (se 1 (by rfl) ⟨56339, by rfl⟩) R112679
theorem R107945 : Reach 107945 := rs (se 2 (by rfl) ⟨40479, by rfl⟩) R80959
theorem R107999 : Reach 107999 := rs (se 1 (by rfl) ⟨80999, by rfl⟩) R161999
theorem R140879 : Reach 140879 := rs (se 1 (by rfl) ⟨105659, by rfl⟩) R211319
theorem R108575 : Reach 108575 := rs (se 1 (by rfl) ⟨81431, by rfl⟩) R162863
theorem R109183 : Reach 109183 := rs (se 1 (by rfl) ⟨81887, by rfl⟩) R163775
theorem R76523 : Reach 76523 := rs (se 1 (by rfl) ⟨57392, by rfl⟩) R114785
theorem R4402151 : Reach 4402151 := rs (se 1 (by rfl) ⟨3301613, by rfl⟩) R6603227
theorem R110015 : Reach 110015 := rs (se 1 (by rfl) ⟨82511, by rfl⟩) R165023
theorem R831059 : Reach 831059 := rs (se 1 (by rfl) ⟨623294, by rfl⟩) R1246589
theorem R1323067 : Reach 1323067 := rs (se 1 (by rfl) ⟨992300, by rfl⟩) R1984601
theorem R110969 : Reach 110969 := rs (se 2 (by rfl) ⟨41613, by rfl⟩) R83227
theorem R242513 : Reach 242513 := rs (se 2 (by rfl) ⟨90942, by rfl⟩) R181885
theorem R111743 : Reach 111743 := rs (se 1 (by rfl) ⟨83807, by rfl⟩) R167615
theorem R112283 : Reach 112283 := rs (se 1 (by rfl) ⟨84212, by rfl⟩) R168425
theorem R112409 : Reach 112409 := rs (se 2 (by rfl) ⟨42153, by rfl⟩) R84307
theorem R112553 : Reach 112553 := rs (se 2 (by rfl) ⟨42207, by rfl⟩) R84415
theorem R112607 : Reach 112607 := rs (se 1 (by rfl) ⟨84455, by rfl⟩) R168911
theorem R47311 : Reach 47311 := rs (se 1 (by rfl) ⟨35483, by rfl⟩) R70967
theorem R80111 : Reach 80111 := rs (se 1 (by rfl) ⟨60083, by rfl⟩) R120167
theorem R47359 : Reach 47359 := rs (se 1 (by rfl) ⟨35519, by rfl⟩) R71039
theorem R112895 : Reach 112895 := rs (se 1 (by rfl) ⟨84671, by rfl⟩) R169343
theorem R113057 : Reach 113057 := rs (se 2 (by rfl) ⟨42396, by rfl⟩) R84793
theorem R47823 : Reach 47823 := rs (se 1 (by rfl) ⟨35867, by rfl⟩) R71735
theorem R47847 : Reach 47847 := rs (se 1 (by rfl) ⟨35885, by rfl⟩) R71771
theorem R113447 : Reach 113447 := rs (se 1 (by rfl) ⟨85085, by rfl⟩) R170171
theorem R113471 : Reach 113471 := rs (se 1 (by rfl) ⟨85103, by rfl⟩) R170207
theorem R48231 : Reach 48231 := rs (se 1 (by rfl) ⟨36173, by rfl⟩) R72347
theorem R48239 : Reach 48239 := rs (se 1 (by rfl) ⟨36179, by rfl⟩) R72359
theorem R113903 : Reach 113903 := rs (se 1 (by rfl) ⟨85427, by rfl⟩) R170855
theorem R48543 : Reach 48543 := rs (se 1 (by rfl) ⟨36407, by rfl⟩) R72815
theorem R605663 : Reach 605663 := rs (se 1 (by rfl) ⟨454247, by rfl⟩) R908495
theorem R146939 : Reach 146939 := rs (se 1 (by rfl) ⟨110204, by rfl⟩) R220409
theorem R48667 : Reach 48667 := rs (se 1 (by rfl) ⟨36500, by rfl⟩) R73001
theorem R81449 : Reach 81449 := rs (se 2 (by rfl) ⟨30543, by rfl⟩) R61087
theorem R114281 : Reach 114281 := rs (se 2 (by rfl) ⟨42855, by rfl⟩) R85711
theorem R344027 : Reach 344027 := rs (se 1 (by rfl) ⟨258020, by rfl⟩) R516041
theorem R114715 : Reach 114715 := rs (se 1 (by rfl) ⟨86036, by rfl⟩) R172073
theorem R1490987 : Reach 1490987 := rs (se 1 (by rfl) ⟨1118240, by rfl⟩) R2236481
theorem R49223 : Reach 49223 := rs (se 1 (by rfl) ⟨36917, by rfl⟩) R73835
theorem R49391 : Reach 49391 := rs (se 1 (by rfl) ⟨37043, by rfl⟩) R74087
theorem R49919 : Reach 49919 := rs (se 1 (by rfl) ⟨37439, by rfl⟩) R74879
theorem R50159 : Reach 50159 := rs (se 1 (by rfl) ⟨37619, by rfl⟩) R75239
theorem R50591 : Reach 50591 := rs (se 1 (by rfl) ⟨37943, by rfl⟩) R75887
theorem R378593 : Reach 378593 := rs (se 2 (by rfl) ⟨141972, by rfl⟩) R283945
theorem R51047 : Reach 51047 := rs (se 1 (by rfl) ⟨38285, by rfl⟩) R76571
theorem R51111 : Reach 51111 := rs (se 1 (by rfl) ⟨38333, by rfl⟩) R76667
theorem R805211 : Reach 805211 := rs (se 1 (by rfl) ⟨603908, by rfl⟩) R1207817
theorem R84719 : Reach 84719 := rs (se 1 (by rfl) ⟨63539, by rfl⟩) R127079
theorem R5393141 : Reach 5393141 := rs (se 5 (by rfl) ⟨252803, by rfl⟩) R505607
theorem R248939 : Reach 248939 := rs (se 1 (by rfl) ⟨186704, by rfl⟩) R373409
theorem R1429001 : Reach 1429001 := rs (se 2 (by rfl) ⟨535875, by rfl⟩) R1071751
theorem R413207 : Reach 413207 := rs (se 1 (by rfl) ⟨309905, by rfl⟩) R619811
theorem R53455 : Reach 53455 := rs (se 1 (by rfl) ⟨40091, by rfl⟩) R80183
theorem R119353 : Reach 119353 := rs (se 2 (by rfl) ⟨44757, by rfl⟩) R89515
theorem R1299077 : Reach 1299077 := rs (se 4 (by rfl) ⟨121788, by rfl⟩) R243577
theorem R120935 : Reach 120935 := rs (se 1 (by rfl) ⟨90701, by rfl⟩) R181403
theorem R285403 : Reach 285403 := rs (se 1 (by rfl) ⟨214052, by rfl⟩) R428105
theorem R56047 : Reach 56047 := rs (se 1 (by rfl) ⟨42035, by rfl⟩) R84071
theorem R416623 : Reach 416623 := rs (se 1 (by rfl) ⟨312467, by rfl⟩) R624935
theorem R2677967 : Reach 2677967 := rs (se 1 (by rfl) ⟨2008475, by rfl⟩) R4016951
theorem R187703 : Reach 187703 := rs (se 1 (by rfl) ⟨140777, by rfl⟩) R281555
theorem R1531993 : Reach 1531993 := rs (se 2 (by rfl) ⟨574497, by rfl⟩) R1148995
theorem R123079 : Reach 123079 := rs (se 1 (by rfl) ⟨92309, by rfl⟩) R184619
theorem R123383 : Reach 123383 := rs (se 1 (by rfl) ⟨92537, by rfl⟩) R185075
theorem R418607 : Reach 418607 := rs (se 1 (by rfl) ⟨313955, by rfl⟩) R627911
theorem R191423 : Reach 191423 := rs (se 1 (by rfl) ⟨143567, by rfl⟩) R287135
theorem R93487 : Reach 93487 := rs (se 1 (by rfl) ⟨70115, by rfl⟩) R140231
theorem R159259 : Reach 159259 := rs (se 1 (by rfl) ⟨119444, by rfl⟩) R238889
theorem R93737 : Reach 93737 := rs (se 2 (by rfl) ⟨35151, by rfl⟩) R70303
theorem R93935 : Reach 93935 := rs (se 1 (by rfl) ⟨70451, by rfl⟩) R140903
theorem R683801 : Reach 683801 := rs (se 2 (by rfl) ⟨256425, by rfl⟩) R512851
theorem R94907 : Reach 94907 := rs (se 1 (by rfl) ⟨71180, by rfl⟩) R142361
theorem R161783 : Reach 161783 := rs (se 1 (by rfl) ⟨121337, by rfl⟩) R242675
theorem R162283 : Reach 162283 := rs (se 1 (by rfl) ⟨121712, by rfl⟩) R243425
theorem R162431 : Reach 162431 := rs (se 1 (by rfl) ⟨121823, by rfl⟩) R243647
theorem R164105 : Reach 164105 := rs (se 2 (by rfl) ⟨61539, by rfl⟩) R123079
theorem R132833 : Reach 132833 := rs (se 2 (by rfl) ⟨49812, by rfl⟩) R99625
theorem R165959 : Reach 165959 := rs (se 1 (by rfl) ⟨124469, by rfl⟩) R248939
theorem R952667 : Reach 952667 := rs (se 1 (by rfl) ⟨714500, by rfl⟩) R1429001
theorem R136073 : Reach 136073 := rs (se 2 (by rfl) ⟨51027, by rfl⟩) R102055
theorem R71015 : Reach 71015 := rs (se 1 (by rfl) ⟨53261, by rfl⟩) R106523
theorem R71195 : Reach 71195 := rs (se 1 (by rfl) ⟨53396, by rfl⟩) R106793
theorem R71273 : Reach 71273 := rs (se 2 (by rfl) ⟨26727, by rfl⟩) R53455
theorem R1841363 : Reach 1841363 := rs (se 1 (by rfl) ⟨1381022, by rfl⟩) R2762045
theorem R71963 : Reach 71963 := rs (se 1 (by rfl) ⟨53972, by rfl⟩) R107945
theorem R71999 : Reach 71999 := rs (se 1 (by rfl) ⟨53999, by rfl⟩) R107999
theorem R137641 : Reach 137641 := rs (se 2 (by rfl) ⟨51615, by rfl⟩) R103231
theorem R72383 : Reach 72383 := rs (se 1 (by rfl) ⟨54287, by rfl⟩) R108575
theorem R367901 : Reach 367901 := rs (se 3 (by rfl) ⟨68981, by rfl⟩) R137963
theorem R302525 : Reach 302525 := rs (se 3 (by rfl) ⟨56723, by rfl⟩) R113447
theorem R73343 : Reach 73343 := rs (se 1 (by rfl) ⟨55007, by rfl⟩) R110015
theorem R73979 : Reach 73979 := rs (se 1 (by rfl) ⟨55484, by rfl⟩) R110969
theorem R74495 : Reach 74495 := rs (se 1 (by rfl) ⟨55871, by rfl⟩) R111743
theorem R74729 : Reach 74729 := rs (se 2 (by rfl) ⟨28023, by rfl⟩) R56047
theorem R74855 : Reach 74855 := rs (se 1 (by rfl) ⟨56141, by rfl⟩) R112283
theorem R74939 : Reach 74939 := rs (se 1 (by rfl) ⟨56204, by rfl⟩) R112409
theorem R75035 : Reach 75035 := rs (se 1 (by rfl) ⟨56276, by rfl⟩) R112553
theorem R75071 : Reach 75071 := rs (se 1 (by rfl) ⟨56303, by rfl⟩) R112607
theorem R107855 : Reach 107855 := rs (se 1 (by rfl) ⟨80891, by rfl⟩) R161783
theorem R75263 : Reach 75263 := rs (se 1 (by rfl) ⟨56447, by rfl⟩) R112895
theorem R75371 : Reach 75371 := rs (se 1 (by rfl) ⟨56528, by rfl⟩) R113057
theorem R108287 : Reach 108287 := rs (se 1 (by rfl) ⟨81215, by rfl⟩) R162431
theorem R75647 : Reach 75647 := rs (se 1 (by rfl) ⟨56735, by rfl⟩) R113471
theorem R75935 : Reach 75935 := rs (se 1 (by rfl) ⟨56951, by rfl⟩) R113903
theorem R403775 : Reach 403775 := rs (se 1 (by rfl) ⟨302831, by rfl⟩) R605663
theorem R76187 : Reach 76187 := rs (se 1 (by rfl) ⟨57140, by rfl⟩) R114281
theorem R3975965 : Reach 3975965 := rs (se 3 (by rfl) ⟨745493, by rfl⟩) R1490987
theorem R2042657 : Reach 2042657 := rs (se 2 (by rfl) ⟨765996, by rfl⟩) R1531993
theorem R240731 : Reach 240731 := rs (se 1 (by rfl) ⟨180548, by rfl⟩) R361097
theorem R109799 : Reach 109799 := rs (se 1 (by rfl) ⟨82349, by rfl⟩) R164699
theorem R536807 : Reach 536807 := rs (se 1 (by rfl) ⟨402605, by rfl⟩) R805211
theorem R2798063 : Reach 2798063 := rs (se 1 (by rfl) ⟨2098547, by rfl⟩) R4197095
theorem R275471 : Reach 275471 := rs (se 1 (by rfl) ⟨206603, by rfl⟩) R413207
theorem R112031 : Reach 112031 := rs (se 1 (by rfl) ⟨84023, by rfl⟩) R168047
theorem R866051 : Reach 866051 := rs (se 1 (by rfl) ⟨649538, by rfl⟩) R1299077
theorem R145577 : Reach 145577 := rs (se 2 (by rfl) ⟨54591, by rfl⟩) R109183
theorem R2013407 : Reach 2013407 := rs (se 1 (by rfl) ⟨1510055, by rfl⟩) R3020111
theorem R113111 : Reach 113111 := rs (se 1 (by rfl) ⟨84833, by rfl⟩) R169667
theorem R80623 : Reach 80623 := rs (se 1 (by rfl) ⟨60467, by rfl⟩) R120935
theorem R375677 : Reach 375677 := rs (se 3 (by rfl) ⟨70439, by rfl⟩) R140879
theorem R48123 : Reach 48123 := rs (se 1 (by rfl) ⟨36092, by rfl⟩) R72185
theorem R113759 : Reach 113759 := rs (se 1 (by rfl) ⟨85319, by rfl⟩) R170639
theorem R48287 : Reach 48287 := rs (se 1 (by rfl) ⟨36215, by rfl⟩) R72431
theorem R244943 : Reach 244943 := rs (se 1 (by rfl) ⟨183707, by rfl⟩) R367415
theorem R48411 : Reach 48411 := rs (se 1 (by rfl) ⟨36308, by rfl⟩) R72617
theorem R212345 : Reach 212345 := rs (se 2 (by rfl) ⟨79629, by rfl⟩) R159259
theorem R1785311 : Reach 1785311 := rs (se 1 (by rfl) ⟨1338983, by rfl⟩) R2677967
theorem R114155 : Reach 114155 := rs (se 1 (by rfl) ⟨85616, by rfl⟩) R171233
theorem R114623 : Reach 114623 := rs (se 1 (by rfl) ⟨85967, by rfl⟩) R171935
theorem R245915 : Reach 245915 := rs (se 1 (by rfl) ⟨184436, by rfl⟩) R368873
theorem R82255 : Reach 82255 := rs (se 1 (by rfl) ⟨61691, by rfl⟩) R123383
theorem R279071 : Reach 279071 := rs (se 1 (by rfl) ⟨209303, by rfl⟩) R418607
theorem R49823 : Reach 49823 := rs (se 1 (by rfl) ⟨37367, by rfl⟩) R74735
theorem R49895 : Reach 49895 := rs (se 1 (by rfl) ⟨37421, by rfl⟩) R74843
theorem R50079 : Reach 50079 := rs (se 1 (by rfl) ⟨37559, by rfl⟩) R75119
theorem R378341 : Reach 378341 := rs (se 4 (by rfl) ⟨35469, by rfl⟩) R70939
theorem R51015 : Reach 51015 := rs (se 1 (by rfl) ⟨38261, by rfl⟩) R76523
theorem R2934767 : Reach 2934767 := rs (se 1 (by rfl) ⟨2201075, by rfl⟩) R4402151
theorem R216377 : Reach 216377 := rs (se 2 (by rfl) ⟨81141, by rfl⟩) R162283
theorem R380537 : Reach 380537 := rs (se 2 (by rfl) ⟨142701, by rfl⟩) R285403
theorem R249965 : Reach 249965 := rs (se 3 (by rfl) ⟨46868, by rfl⟩) R93737
theorem R53407 : Reach 53407 := rs (se 1 (by rfl) ⟨40055, by rfl⟩) R80111
theorem R447241 : Reach 447241 := rs (se 2 (by rfl) ⟨167715, by rfl⟩) R335431
theorem R54299 : Reach 54299 := rs (se 1 (by rfl) ⟨40724, by rfl⟩) R81449
theorem R611813 : Reach 611813 := rs (se 4 (by rfl) ⟨57357, by rfl⟩) R114715
theorem R252395 : Reach 252395 := rs (se 1 (by rfl) ⟨189296, by rfl⟩) R378593
theorem R56479 : Reach 56479 := rs (se 1 (by rfl) ⟨42359, by rfl⟩) R84719
theorem R3595427 : Reach 3595427 := rs (se 1 (by rfl) ⟨2696570, by rfl⟩) R5393141
theorem R89599 : Reach 89599 := rs (se 1 (by rfl) ⟨67199, by rfl⟩) R134399
theorem R286679 : Reach 286679 := rs (se 1 (by rfl) ⟨215009, by rfl⟩) R430019
theorem R90335 : Reach 90335 := rs (se 1 (by rfl) ⟨67751, by rfl⟩) R135503
theorem R124649 : Reach 124649 := rs (se 2 (by rfl) ⟨46743, by rfl⟩) R93487
theorem R125135 : Reach 125135 := rs (se 1 (by rfl) ⟨93851, by rfl⟩) R187703
theorem R354527 : Reach 354527 := rs (se 1 (by rfl) ⟨265895, by rfl⟩) R531791
theorem R1764089 : Reach 1764089 := rs (se 2 (by rfl) ⟨661533, by rfl⟩) R1323067
theorem R159137 : Reach 159137 := rs (se 2 (by rfl) ⟨59676, by rfl⟩) R119353
theorem R290279 : Reach 290279 := rs (se 1 (by rfl) ⟨217709, by rfl⟩) R435419
theorem R127615 : Reach 127615 := rs (se 1 (by rfl) ⟨95711, by rfl⟩) R191423
theorem R554039 : Reach 554039 := rs (se 1 (by rfl) ⟨415529, by rfl⟩) R831059
theorem R62623 : Reach 62623 := rs (se 1 (by rfl) ⟨46967, by rfl⟩) R93935
theorem R455867 : Reach 455867 := rs (se 1 (by rfl) ⟨341900, by rfl⟩) R683801
theorem R63271 : Reach 63271 := rs (se 1 (by rfl) ⟨47453, by rfl⟩) R94907
theorem R161675 : Reach 161675 := rs (se 1 (by rfl) ⟨121256, by rfl⟩) R242513
theorem R555497 : Reach 555497 := rs (se 2 (by rfl) ⟨208311, by rfl⟩) R416623
theorem R391837 : Reach 391837 := rs (se 3 (by rfl) ⟨73469, by rfl⟩) R146939
theorem R229351 : Reach 229351 := rs (se 1 (by rfl) ⟨172013, by rfl⟩) R344027
theorem R163943 : Reach 163943 := rs (se 1 (by rfl) ⟨122957, by rfl⟩) R245915
theorem R166643 : Reach 166643 := rs (se 1 (by rfl) ⟨124982, by rfl⟩) R249965
theorem R168263 : Reach 168263 := rs (se 1 (by rfl) ⟨126197, by rfl⟩) R252395
theorem R2396951 : Reach 2396951 := rs (se 1 (by rfl) ⟨1797713, by rfl⟩) R3595427
theorem R201683 : Reach 201683 := rs (se 1 (by rfl) ⟨151262, by rfl⟩) R302525
theorem R71209 : Reach 71209 := rs (se 2 (by rfl) ⟨26703, by rfl⟩) R53407
theorem R170153 : Reach 170153 := rs (se 2 (by rfl) ⟨63807, by rfl⟩) R127615
theorem R71903 : Reach 71903 := rs (se 1 (by rfl) ⟨53927, by rfl⟩) R107855
theorem R596321 : Reach 596321 := rs (se 2 (by rfl) ⟨223620, by rfl⟩) R447241
theorem R72191 : Reach 72191 := rs (se 1 (by rfl) ⟨54143, by rfl⟩) R108287
theorem R236351 : Reach 236351 := rs (se 1 (by rfl) ⟨177263, by rfl⟩) R354527
theorem R269183 : Reach 269183 := rs (se 1 (by rfl) ⟨201887, by rfl⟩) R403775
theorem R73199 : Reach 73199 := rs (se 1 (by rfl) ⟨54899, by rfl⟩) R109799
theorem R106091 : Reach 106091 := rs (se 1 (by rfl) ⟨79568, by rfl⟩) R159137
theorem R369359 : Reach 369359 := rs (se 1 (by rfl) ⟨277019, by rfl⟩) R554039
theorem R303911 : Reach 303911 := rs (se 1 (by rfl) ⟨227933, by rfl⟩) R455867
theorem R74687 : Reach 74687 := rs (se 1 (by rfl) ⟨56015, by rfl⟩) R112031
theorem R107497 : Reach 107497 := rs (se 2 (by rfl) ⟨40311, by rfl⟩) R80623
theorem R107783 : Reach 107783 := rs (se 1 (by rfl) ⟨80837, by rfl⟩) R161675
theorem R75305 : Reach 75305 := rs (se 2 (by rfl) ⟨28239, by rfl⟩) R56479
theorem R75407 : Reach 75407 := rs (se 1 (by rfl) ⟨56555, by rfl⟩) R113111
theorem R370331 : Reach 370331 := rs (se 1 (by rfl) ⟨277748, by rfl⟩) R555497
theorem R75839 : Reach 75839 := rs (se 1 (by rfl) ⟨56879, by rfl⟩) R113759
theorem R141563 : Reach 141563 := rs (se 1 (by rfl) ⟨106172, by rfl⟩) R212345
theorem R1190207 : Reach 1190207 := rs (se 1 (by rfl) ⟨892655, by rfl⟩) R1785311
theorem R76103 : Reach 76103 := rs (se 1 (by rfl) ⟨57077, by rfl⟩) R114155
theorem R76415 : Reach 76415 := rs (se 1 (by rfl) ⟨57311, by rfl⟩) R114623
theorem R305801 : Reach 305801 := rs (se 2 (by rfl) ⟨114675, by rfl⟩) R229351
theorem R109403 : Reach 109403 := rs (se 1 (by rfl) ⟨82052, by rfl⟩) R164105
theorem R109673 : Reach 109673 := rs (se 2 (by rfl) ⟨41127, by rfl⟩) R82255
theorem R240893 : Reach 240893 := rs (se 3 (by rfl) ⟨45167, by rfl⟩) R90335
theorem R110639 : Reach 110639 := rs (se 1 (by rfl) ⟨82979, by rfl⟩) R165959
theorem R635111 : Reach 635111 := rs (se 1 (by rfl) ⟨476333, by rfl⟩) R952667
theorem R144251 : Reach 144251 := rs (se 1 (by rfl) ⟨108188, by rfl⟩) R216377
theorem R144797 : Reach 144797 := rs (se 3 (by rfl) ⟨27149, by rfl⟩) R54299
theorem R47343 : Reach 47343 := rs (se 1 (by rfl) ⟨35507, by rfl⟩) R71015
theorem R407875 : Reach 407875 := rs (se 1 (by rfl) ⟨305906, by rfl⟩) R611813
theorem R47463 : Reach 47463 := rs (se 1 (by rfl) ⟨35597, by rfl⟩) R71195
theorem R47515 : Reach 47515 := rs (se 1 (by rfl) ⟨35636, by rfl⟩) R71273
theorem R1227575 : Reach 1227575 := rs (se 1 (by rfl) ⟨920681, by rfl⟩) R1841363
theorem R47975 : Reach 47975 := rs (se 1 (by rfl) ⟨35981, by rfl⟩) R71963
theorem R47999 : Reach 47999 := rs (se 1 (by rfl) ⟨35999, by rfl⟩) R71999
theorem R48255 : Reach 48255 := rs (se 1 (by rfl) ⟨36191, by rfl⟩) R72383
theorem R245267 : Reach 245267 := rs (se 1 (by rfl) ⟨183950, by rfl⟩) R367901
theorem R48895 : Reach 48895 := rs (se 1 (by rfl) ⟨36671, by rfl⟩) R73343
theorem R49319 : Reach 49319 := rs (se 1 (by rfl) ⟨36989, by rfl⟩) R73979
theorem R49663 : Reach 49663 := rs (se 1 (by rfl) ⟨37247, by rfl⟩) R74495
theorem R49819 : Reach 49819 := rs (se 1 (by rfl) ⟨37364, by rfl⟩) R74729
theorem R49903 : Reach 49903 := rs (se 1 (by rfl) ⟨37427, by rfl⟩) R74855
theorem R49959 : Reach 49959 := rs (se 1 (by rfl) ⟨37469, by rfl⟩) R74939
theorem R50023 : Reach 50023 := rs (se 1 (by rfl) ⟨37517, by rfl⟩) R75035
theorem R50047 : Reach 50047 := rs (se 1 (by rfl) ⟨37535, by rfl⟩) R75071
theorem R50175 : Reach 50175 := rs (se 1 (by rfl) ⟨37631, by rfl⟩) R75263
theorem R50247 : Reach 50247 := rs (se 1 (by rfl) ⟨37685, by rfl⟩) R75371
theorem R83099 : Reach 83099 := rs (se 1 (by rfl) ⟨62324, by rfl⟩) R124649
theorem R50431 : Reach 50431 := rs (se 1 (by rfl) ⟨37823, by rfl⟩) R75647
theorem R50623 : Reach 50623 := rs (se 1 (by rfl) ⟨37967, by rfl⟩) R75935
theorem R83423 : Reach 83423 := rs (se 1 (by rfl) ⟨62567, by rfl⟩) R125135
theorem R83497 : Reach 83497 := rs (se 2 (by rfl) ⟨31311, by rfl⟩) R62623
theorem R50791 : Reach 50791 := rs (se 1 (by rfl) ⟨38093, by rfl⟩) R76187
theorem R1361771 : Reach 1361771 := rs (se 1 (by rfl) ⟨1021328, by rfl⟩) R2042657
theorem R84361 : Reach 84361 := rs (se 2 (by rfl) ⟨31635, by rfl⟩) R63271
theorem R183521 : Reach 183521 := rs (se 2 (by rfl) ⟨68820, by rfl⟩) R137641
theorem R183647 : Reach 183647 := rs (se 1 (by rfl) ⟨137735, by rfl⟩) R275471
theorem R577367 : Reach 577367 := rs (se 1 (by rfl) ⟨433025, by rfl⟩) R866051
theorem R250451 : Reach 250451 := rs (se 1 (by rfl) ⟨187838, by rfl⟩) R375677
theorem R119465 : Reach 119465 := rs (se 2 (by rfl) ⟨44799, by rfl⟩) R89599
theorem R186047 : Reach 186047 := rs (se 1 (by rfl) ⟨139535, by rfl⟩) R279071
theorem R252227 : Reach 252227 := rs (se 1 (by rfl) ⟨189170, by rfl⟩) R378341
theorem R88555 : Reach 88555 := rs (se 1 (by rfl) ⟨66416, by rfl⟩) R132833
theorem R1956511 : Reach 1956511 := rs (se 1 (by rfl) ⟨1467383, by rfl⟩) R2934767
theorem R253691 : Reach 253691 := rs (se 1 (by rfl) ⟨190268, by rfl⟩) R380537
theorem R90715 : Reach 90715 := rs (se 1 (by rfl) ⟨68036, by rfl⟩) R136073
theorem R191119 : Reach 191119 := rs (se 1 (by rfl) ⟨143339, by rfl⟩) R286679
theorem R1176059 : Reach 1176059 := rs (se 1 (by rfl) ⟨882044, by rfl⟩) R1764089
theorem R2650643 : Reach 2650643 := rs (se 1 (by rfl) ⟨1987982, by rfl⟩) R3975965
theorem R160487 : Reach 160487 := rs (se 1 (by rfl) ⟨120365, by rfl⟩) R240731
theorem R193519 : Reach 193519 := rs (se 1 (by rfl) ⟨145139, by rfl⟩) R290279
theorem R357871 : Reach 357871 := rs (se 1 (by rfl) ⟨268403, by rfl⟩) R536807
theorem R1865375 : Reach 1865375 := rs (se 1 (by rfl) ⟨1399031, by rfl⟩) R2798063
theorem R522449 : Reach 522449 := rs (se 2 (by rfl) ⟨195918, by rfl⟩) R391837
theorem R97051 : Reach 97051 := rs (se 1 (by rfl) ⟨72788, by rfl⟩) R145577
theorem R1342271 : Reach 1342271 := rs (se 1 (by rfl) ⟨1006703, by rfl⟩) R2013407
theorem R163295 : Reach 163295 := rs (se 1 (by rfl) ⟨122471, by rfl⟩) R244943
theorem R166967 : Reach 166967 := rs (se 1 (by rfl) ⟨125225, by rfl⟩) R250451
theorem R134455 : Reach 134455 := rs (se 1 (by rfl) ⟨100841, by rfl⟩) R201683
theorem R397547 : Reach 397547 := rs (se 1 (by rfl) ⟨298160, by rfl⟩) R596321
theorem R1544501 : Reach 1544501 := rs (se 5 (by rfl) ⟨72398, by rfl⟩) R144797
theorem R70727 : Reach 70727 := rs (se 1 (by rfl) ⟨53045, by rfl⟩) R106091
theorem R169127 : Reach 169127 := rs (se 1 (by rfl) ⟨126845, by rfl⟩) R253691
theorem R202607 : Reach 202607 := rs (se 1 (by rfl) ⟨151955, by rfl⟩) R303911
theorem R71855 : Reach 71855 := rs (se 1 (by rfl) ⟨53891, by rfl⟩) R107783
theorem R793471 : Reach 793471 := rs (se 1 (by rfl) ⟨595103, by rfl⟩) R1190207
theorem R203867 : Reach 203867 := rs (se 1 (by rfl) ⟨152900, by rfl⟩) R305801
theorem R72935 : Reach 72935 := rs (se 1 (by rfl) ⟨54701, by rfl⟩) R109403
theorem R73115 : Reach 73115 := rs (se 1 (by rfl) ⟨54836, by rfl⟩) R109673
theorem R3579389 : Reach 3579389 := rs (se 3 (by rfl) ⟨671135, by rfl⟩) R1342271
theorem R73759 : Reach 73759 := rs (se 1 (by rfl) ⟨55319, by rfl⟩) R110639
theorem R106991 : Reach 106991 := rs (se 1 (by rfl) ⟨80243, by rfl⟩) R160487
theorem R108863 : Reach 108863 := rs (se 1 (by rfl) ⟨81647, by rfl⟩) R163295
theorem R109295 : Reach 109295 := rs (se 1 (by rfl) ⟨81971, by rfl⟩) R163943
theorem R143329 : Reach 143329 := rs (se 2 (by rfl) ⟨53748, by rfl⟩) R107497
theorem R111095 : Reach 111095 := rs (se 1 (by rfl) ⟨83321, by rfl⟩) R166643
theorem R111329 : Reach 111329 := rs (se 2 (by rfl) ⟨41748, by rfl⟩) R83497
theorem R112175 : Reach 112175 := rs (se 1 (by rfl) ⟨84131, by rfl⟩) R168263
theorem R79643 : Reach 79643 := rs (se 1 (by rfl) ⟨59732, by rfl⟩) R119465
theorem R112481 : Reach 112481 := rs (se 2 (by rfl) ⟨42180, by rfl⟩) R84361
theorem R113435 : Reach 113435 := rs (se 1 (by rfl) ⟨85076, by rfl⟩) R170153
theorem R47935 : Reach 47935 := rs (se 1 (by rfl) ⟨35951, by rfl⟩) R71903
theorem R48127 : Reach 48127 := rs (se 1 (by rfl) ⟨36095, by rfl⟩) R72191
theorem R179455 : Reach 179455 := rs (se 1 (by rfl) ⟨134591, by rfl⟩) R269183
theorem R48799 : Reach 48799 := rs (se 1 (by rfl) ⟨36599, by rfl⟩) R73199
theorem R246239 : Reach 246239 := rs (se 1 (by rfl) ⟨184679, by rfl⟩) R369359
theorem R49791 : Reach 49791 := rs (se 1 (by rfl) ⟨37343, by rfl⟩) R74687
theorem R672605 : Reach 672605 := rs (se 3 (by rfl) ⟨126113, by rfl⟩) R252227
theorem R50203 : Reach 50203 := rs (se 1 (by rfl) ⟨37652, by rfl⟩) R75305
theorem R50271 : Reach 50271 := rs (se 1 (by rfl) ⟨37703, by rfl⟩) R75407
theorem R246887 : Reach 246887 := rs (se 1 (by rfl) ⟨185165, by rfl⟩) R370331
theorem R50559 : Reach 50559 := rs (se 1 (by rfl) ⟨37919, by rfl⟩) R75839
theorem R50735 : Reach 50735 := rs (se 1 (by rfl) ⟨38051, by rfl⟩) R76103
theorem R50943 : Reach 50943 := rs (se 1 (by rfl) ⟨38207, by rfl⟩) R76415
theorem R477161 : Reach 477161 := rs (se 2 (by rfl) ⟨178935, by rfl⟩) R357871
theorem R543833 : Reach 543833 := rs (se 2 (by rfl) ⟨203937, by rfl⟩) R407875
theorem R118073 : Reach 118073 := rs (se 2 (by rfl) ⟨44277, by rfl⟩) R88555
theorem R2608681 : Reach 2608681 := rs (se 2 (by rfl) ⟨978255, by rfl⟩) R1956511
theorem R348299 : Reach 348299 := rs (se 1 (by rfl) ⟨261224, by rfl⟩) R522449
theorem R55399 : Reach 55399 := rs (se 1 (by rfl) ⟨41549, by rfl⟩) R83099
theorem R120953 : Reach 120953 := rs (se 2 (by rfl) ⟨45357, by rfl⟩) R90715
theorem R55615 : Reach 55615 := rs (se 1 (by rfl) ⟨41711, by rfl⟩) R83423
theorem R907847 : Reach 907847 := rs (se 1 (by rfl) ⟨680885, by rfl⟩) R1361771
theorem R122347 : Reach 122347 := rs (se 1 (by rfl) ⟨91760, by rfl⟩) R183521
theorem R122431 : Reach 122431 := rs (se 1 (by rfl) ⟨91823, by rfl⟩) R183647
theorem R384911 : Reach 384911 := rs (se 1 (by rfl) ⟨288683, by rfl⟩) R577367
theorem R1597967 : Reach 1597967 := rs (se 1 (by rfl) ⟨1198475, by rfl⟩) R2396951
theorem R254825 : Reach 254825 := rs (se 2 (by rfl) ⟨95559, by rfl⟩) R191119
theorem R124031 : Reach 124031 := rs (se 1 (by rfl) ⟨93023, by rfl⟩) R186047
theorem R157567 : Reach 157567 := rs (se 1 (by rfl) ⟨118175, by rfl⟩) R236351
theorem R258025 : Reach 258025 := rs (se 2 (by rfl) ⟨96759, by rfl⟩) R193519
theorem R94375 : Reach 94375 := rs (se 1 (by rfl) ⟨70781, by rfl⟩) R141563
theorem R94945 : Reach 94945 := rs (se 2 (by rfl) ⟨35604, by rfl⟩) R71209
theorem R160595 : Reach 160595 := rs (se 1 (by rfl) ⟨120446, by rfl⟩) R240893
theorem R423407 : Reach 423407 := rs (se 1 (by rfl) ⟨317555, by rfl⟩) R635111
theorem R784039 : Reach 784039 := rs (se 1 (by rfl) ⟨588029, by rfl⟩) R1176059
theorem R1767095 : Reach 1767095 := rs (se 1 (by rfl) ⟨1325321, by rfl⟩) R2650643
theorem R96167 : Reach 96167 := rs (se 1 (by rfl) ⟨72125, by rfl⟩) R144251
theorem R129401 : Reach 129401 := rs (se 2 (by rfl) ⟨48525, by rfl⟩) R97051
theorem R1243583 : Reach 1243583 := rs (se 1 (by rfl) ⟨932687, by rfl⟩) R1865375
theorem R818383 : Reach 818383 := rs (se 1 (by rfl) ⟨613787, by rfl⟩) R1227575
theorem R163511 : Reach 163511 := rs (se 1 (by rfl) ⟨122633, by rfl⟩) R245267
theorem R98345 : Reach 98345 := rs (se 2 (by rfl) ⟨36879, by rfl⟩) R73759
theorem R164159 : Reach 164159 := rs (se 1 (by rfl) ⟨123119, by rfl⟩) R246239
theorem R164591 : Reach 164591 := rs (se 1 (by rfl) ⟨123443, by rfl⟩) R246887
theorem R362555 : Reach 362555 := rs (se 1 (by rfl) ⟨271916, by rfl⟩) R543833
theorem R232199 : Reach 232199 := rs (se 1 (by rfl) ⟨174149, by rfl⟩) R348299
theorem R265031 : Reach 265031 := rs (se 1 (by rfl) ⟨198773, by rfl⟩) R397547
theorem R135071 : Reach 135071 := rs (se 1 (by rfl) ⟨101303, by rfl⟩) R202607
theorem R3478241 : Reach 3478241 := rs (se 2 (by rfl) ⟨1304340, by rfl⟩) R2608681
theorem R135911 : Reach 135911 := rs (se 1 (by rfl) ⟨101933, by rfl⟩) R203867
theorem R71327 : Reach 71327 := rs (se 1 (by rfl) ⟨53495, by rfl⟩) R106991
theorem R169883 : Reach 169883 := rs (se 1 (by rfl) ⟨127412, by rfl⟩) R254825
theorem R72575 : Reach 72575 := rs (se 1 (by rfl) ⟨54431, by rfl⟩) R108863
theorem R72863 : Reach 72863 := rs (se 1 (by rfl) ⟨54647, by rfl⟩) R109295
theorem R73865 : Reach 73865 := rs (se 2 (by rfl) ⟨27699, by rfl⟩) R55399
theorem R74063 : Reach 74063 := rs (se 1 (by rfl) ⟨55547, by rfl⟩) R111095
theorem R74153 : Reach 74153 := rs (se 2 (by rfl) ⟨27807, by rfl⟩) R55615
theorem R74219 : Reach 74219 := rs (se 1 (by rfl) ⟨55664, by rfl⟩) R111329
theorem R107063 : Reach 107063 := rs (se 1 (by rfl) ⟨80297, by rfl⟩) R160595
theorem R74783 : Reach 74783 := rs (se 1 (by rfl) ⟨56087, by rfl⟩) R112175
theorem R1057961 : Reach 1057961 := rs (se 2 (by rfl) ⟨396735, by rfl⟩) R793471
theorem R74987 : Reach 74987 := rs (se 1 (by rfl) ⟨56240, by rfl⟩) R112481
theorem R1091177 : Reach 1091177 := rs (se 2 (by rfl) ⟨409191, by rfl⟩) R818383
theorem R829055 : Reach 829055 := rs (se 1 (by rfl) ⟨621791, by rfl⟩) R1243583
theorem R239273 : Reach 239273 := rs (se 2 (by rfl) ⟨89727, by rfl⟩) R179455
theorem R75623 : Reach 75623 := rs (se 1 (by rfl) ⟨56717, by rfl⟩) R113435
theorem R109007 : Reach 109007 := rs (se 1 (by rfl) ⟨81755, by rfl⟩) R163511
theorem R111311 : Reach 111311 := rs (se 1 (by rfl) ⟨83483, by rfl⟩) R166967
theorem R78715 : Reach 78715 := rs (se 1 (by rfl) ⟨59036, by rfl⟩) R118073
theorem R210089 : Reach 210089 := rs (se 2 (by rfl) ⟨78783, by rfl⟩) R157567
theorem R1029667 : Reach 1029667 := rs (se 1 (by rfl) ⟨772250, by rfl⟩) R1544501
theorem R47151 : Reach 47151 := rs (se 1 (by rfl) ⟨35363, by rfl⟩) R70727
theorem R112751 : Reach 112751 := rs (se 1 (by rfl) ⟨84563, by rfl⟩) R169127
theorem R1129085 : Reach 1129085 := rs (se 3 (by rfl) ⟨211703, by rfl⟩) R423407
theorem R80635 : Reach 80635 := rs (se 1 (by rfl) ⟨60476, by rfl⟩) R120953
theorem R47903 : Reach 47903 := rs (se 1 (by rfl) ⟨35927, by rfl⟩) R71855
theorem R605231 : Reach 605231 := rs (se 1 (by rfl) ⟨453923, by rfl⟩) R907847
theorem R179273 : Reach 179273 := rs (se 2 (by rfl) ⟨67227, by rfl⟩) R134455
theorem R48623 : Reach 48623 := rs (se 1 (by rfl) ⟨36467, by rfl⟩) R72935
theorem R48743 : Reach 48743 := rs (se 1 (by rfl) ⟨36557, by rfl⟩) R73115
theorem R344033 : Reach 344033 := rs (se 2 (by rfl) ⟨129012, by rfl⟩) R258025
theorem R1065311 : Reach 1065311 := rs (se 1 (by rfl) ⟨798983, by rfl⟩) R1597967
theorem R82687 : Reach 82687 := rs (se 1 (by rfl) ⟨62015, by rfl⟩) R124031
theorem R53095 : Reach 53095 := rs (se 1 (by rfl) ⟨39821, by rfl⟩) R79643
theorem R86267 : Reach 86267 := rs (se 1 (by rfl) ⟨64700, by rfl⟩) R129401
theorem R318107 : Reach 318107 := rs (se 1 (by rfl) ⟨238580, by rfl⟩) R477161
theorem R2386259 : Reach 2386259 := rs (se 1 (by rfl) ⟨1789694, by rfl⟩) R3579389
theorem R256445 : Reach 256445 := rs (se 3 (by rfl) ⟨48083, by rfl⟩) R96167
theorem R256607 : Reach 256607 := rs (se 1 (by rfl) ⟨192455, by rfl⟩) R384911
theorem R191105 : Reach 191105 := rs (se 2 (by rfl) ⟨71664, by rfl⟩) R143329
theorem R125833 : Reach 125833 := rs (se 2 (by rfl) ⟨47187, by rfl⟩) R94375
theorem R126593 : Reach 126593 := rs (se 2 (by rfl) ⟨47472, by rfl⟩) R94945
theorem R1045385 : Reach 1045385 := rs (se 2 (by rfl) ⟨392019, by rfl⟩) R784039
theorem R7174453 : Reach 7174453 := rs (se 5 (by rfl) ⟨336302, by rfl⟩) R672605
theorem R1178063 : Reach 1178063 := rs (se 1 (by rfl) ⟨883547, by rfl⟩) R1767095
theorem R163129 : Reach 163129 := rs (se 2 (by rfl) ⟨61173, by rfl⟩) R122347
theorem R163241 : Reach 163241 := rs (se 2 (by rfl) ⟨61215, by rfl⟩) R122431
theorem R262253 : Reach 262253 := rs (se 3 (by rfl) ⟨49172, by rfl⟩) R98345
theorem R230045 : Reach 230045 := rs (se 3 (by rfl) ⟨43133, by rfl⟩) R86267
theorem R9275309 : Reach 9275309 := rs (se 3 (by rfl) ⟨1739120, by rfl⟩) R3478241
theorem R167777 : Reach 167777 := rs (se 2 (by rfl) ⟨62916, by rfl⟩) R125833
theorem R70793 : Reach 70793 := rs (se 2 (by rfl) ⟨26547, by rfl⟩) R53095
theorem R71375 : Reach 71375 := rs (se 1 (by rfl) ⟨53531, by rfl⟩) R107063
theorem R727451 : Reach 727451 := rs (se 1 (by rfl) ⟨545588, by rfl⟩) R1091177
theorem R170963 : Reach 170963 := rs (se 1 (by rfl) ⟨128222, by rfl⟩) R256445
theorem R72671 : Reach 72671 := rs (se 1 (by rfl) ⟨54503, by rfl⟩) R109007
theorem R171071 : Reach 171071 := rs (se 1 (by rfl) ⟨128303, by rfl⟩) R256607
theorem R74207 : Reach 74207 := rs (se 1 (by rfl) ⟨55655, by rfl⟩) R111311
theorem R696923 : Reach 696923 := rs (se 1 (by rfl) ⟨522692, by rfl⟩) R1045385
theorem R140059 : Reach 140059 := rs (se 1 (by rfl) ⟨105044, by rfl⟩) R210089
theorem R107513 : Reach 107513 := rs (se 2 (by rfl) ⟨40317, by rfl⟩) R80635
theorem R75167 : Reach 75167 := rs (se 1 (by rfl) ⟨56375, by rfl⟩) R112751
theorem R403487 : Reach 403487 := rs (se 1 (by rfl) ⟨302615, by rfl⟩) R605231
theorem R108827 : Reach 108827 := rs (se 1 (by rfl) ⟨81620, by rfl⟩) R163241
theorem R109439 : Reach 109439 := rs (se 1 (by rfl) ⟨82079, by rfl⟩) R164159
theorem R109727 : Reach 109727 := rs (se 1 (by rfl) ⟨82295, by rfl⟩) R164591
theorem R110249 : Reach 110249 := rs (se 2 (by rfl) ⟨41343, by rfl⟩) R82687
theorem R241703 : Reach 241703 := rs (se 1 (by rfl) ⟨181277, by rfl⟩) R362555
theorem R176687 : Reach 176687 := rs (se 1 (by rfl) ⟨132515, by rfl⟩) R265031
theorem R47551 : Reach 47551 := rs (se 1 (by rfl) ⟨35663, by rfl⟩) R71327
theorem R113255 : Reach 113255 := rs (se 1 (by rfl) ⟨84941, by rfl⟩) R169883
theorem R212071 : Reach 212071 := rs (se 1 (by rfl) ⟨159053, by rfl⟩) R318107
theorem R48383 : Reach 48383 := rs (se 1 (by rfl) ⟨36287, by rfl⟩) R72575
theorem R48575 : Reach 48575 := rs (se 1 (by rfl) ⟨36431, by rfl⟩) R72863
theorem R49243 : Reach 49243 := rs (se 1 (by rfl) ⟨36932, by rfl⟩) R73865
theorem R49375 : Reach 49375 := rs (se 1 (by rfl) ⟨37031, by rfl⟩) R74063
theorem R49435 : Reach 49435 := rs (se 1 (by rfl) ⟨37076, by rfl⟩) R74153
theorem R49479 : Reach 49479 := rs (se 1 (by rfl) ⟨37109, by rfl⟩) R74219
theorem R49855 : Reach 49855 := rs (se 1 (by rfl) ⟨37391, by rfl⟩) R74783
theorem R705307 : Reach 705307 := rs (se 1 (by rfl) ⟨528980, by rfl⟩) R1057961
theorem R49991 : Reach 49991 := rs (se 1 (by rfl) ⟨37493, by rfl⟩) R74987
theorem R50415 : Reach 50415 := rs (se 1 (by rfl) ⟨37811, by rfl⟩) R75623
theorem R1590839 : Reach 1590839 := rs (se 1 (by rfl) ⟨1193129, by rfl⟩) R2386259
theorem R84395 : Reach 84395 := rs (se 1 (by rfl) ⟨63296, by rfl⟩) R126593
theorem R217505 : Reach 217505 := rs (se 2 (by rfl) ⟨81564, by rfl⟩) R163129
theorem R119515 : Reach 119515 := rs (se 1 (by rfl) ⟨89636, by rfl⟩) R179273
theorem R710207 : Reach 710207 := rs (se 1 (by rfl) ⟨532655, by rfl⟩) R1065311
theorem R154799 : Reach 154799 := rs (se 1 (by rfl) ⟨116099, by rfl⟩) R232199
theorem R90047 : Reach 90047 := rs (se 1 (by rfl) ⟨67535, by rfl⟩) R135071
theorem R90607 : Reach 90607 := rs (se 1 (by rfl) ⟨67955, by rfl⟩) R135911
theorem R419813 : Reach 419813 := rs (se 4 (by rfl) ⟨39357, by rfl⟩) R78715
theorem R552703 : Reach 552703 := rs (se 1 (by rfl) ⟨414527, by rfl⟩) R829055
theorem R159515 : Reach 159515 := rs (se 1 (by rfl) ⟨119636, by rfl⟩) R239273
theorem R127403 : Reach 127403 := rs (se 1 (by rfl) ⟨95552, by rfl⟩) R191105
theorem R1372889 : Reach 1372889 := rs (se 2 (by rfl) ⟨514833, by rfl⟩) R1029667
theorem R9565937 : Reach 9565937 := rs (se 2 (by rfl) ⟨3587226, by rfl⟩) R7174453
theorem R785375 : Reach 785375 := rs (se 1 (by rfl) ⟨589031, by rfl⟩) R1178063
theorem R752723 : Reach 752723 := rs (se 1 (by rfl) ⟨564542, by rfl⟩) R1129085
theorem R229355 : Reach 229355 := rs (se 1 (by rfl) ⟨172016, by rfl⟩) R344033
theorem R103199 : Reach 103199 := rs (se 1 (by rfl) ⟨77399, by rfl⟩) R154799
theorem R464615 : Reach 464615 := rs (se 1 (by rfl) ⟨348461, by rfl⟩) R696923
theorem R71675 : Reach 71675 := rs (se 1 (by rfl) ⟨53756, by rfl⟩) R107513
theorem R268991 : Reach 268991 := rs (se 1 (by rfl) ⟨201743, by rfl⟩) R403487
theorem R72551 : Reach 72551 := rs (se 1 (by rfl) ⟨54413, by rfl⟩) R108827
theorem R72959 : Reach 72959 := rs (se 1 (by rfl) ⟨54719, by rfl⟩) R109439
theorem R73151 : Reach 73151 := rs (se 1 (by rfl) ⟨54863, by rfl⟩) R109727
theorem R73499 : Reach 73499 := rs (se 1 (by rfl) ⟨55124, by rfl⟩) R110249
theorem R106343 : Reach 106343 := rs (se 1 (by rfl) ⟨79757, by rfl⟩) R159515
theorem R75503 : Reach 75503 := rs (se 1 (by rfl) ⟨56627, by rfl⟩) R113255
theorem R501815 : Reach 501815 := rs (se 1 (by rfl) ⟨376361, by rfl⟩) R752723
theorem R174835 : Reach 174835 := rs (se 1 (by rfl) ⟨131126, by rfl⟩) R262253
theorem R1060559 : Reach 1060559 := rs (se 1 (by rfl) ⟨795419, by rfl⟩) R1590839
theorem R111851 : Reach 111851 := rs (se 1 (by rfl) ⟨83888, by rfl⟩) R167777
theorem R145003 : Reach 145003 := rs (se 1 (by rfl) ⟨108752, by rfl⟩) R217505
theorem R47195 : Reach 47195 := rs (se 1 (by rfl) ⟨35396, by rfl⟩) R70793
theorem R473471 : Reach 473471 := rs (se 1 (by rfl) ⟨355103, by rfl⟩) R710207
theorem R47583 : Reach 47583 := rs (se 1 (by rfl) ⟨35687, by rfl⟩) R71375
theorem R113975 : Reach 113975 := rs (se 1 (by rfl) ⟨85481, by rfl⟩) R170963
theorem R48447 : Reach 48447 := rs (se 1 (by rfl) ⟨36335, by rfl⟩) R72671
theorem R114047 : Reach 114047 := rs (se 1 (by rfl) ⟨85535, by rfl⟩) R171071
theorem R736937 : Reach 736937 := rs (se 2 (by rfl) ⟨276351, by rfl⟩) R552703
theorem R49471 : Reach 49471 := rs (se 1 (by rfl) ⟨37103, by rfl⟩) R74207
theorem R50111 : Reach 50111 := rs (se 1 (by rfl) ⟨37583, by rfl⟩) R75167
theorem R279875 : Reach 279875 := rs (se 1 (by rfl) ⟨209906, by rfl⟩) R419813
theorem R84935 : Reach 84935 := rs (se 1 (by rfl) ⟨63701, by rfl⟩) R127403
theorem R117791 : Reach 117791 := rs (se 1 (by rfl) ⟨88343, by rfl⟩) R176687
theorem R6377291 : Reach 6377291 := rs (se 1 (by rfl) ⟨4782968, by rfl⟩) R9565937
theorem R282761 : Reach 282761 := rs (se 2 (by rfl) ⟨106035, by rfl⟩) R212071
theorem R152903 : Reach 152903 := rs (se 1 (by rfl) ⟨114677, by rfl⟩) R229355
theorem R120809 : Reach 120809 := rs (se 2 (by rfl) ⟨45303, by rfl⟩) R90607
theorem R940409 : Reach 940409 := rs (se 2 (by rfl) ⟨352653, by rfl⟩) R705307
theorem R186745 : Reach 186745 := rs (se 2 (by rfl) ⟨70029, by rfl⟩) R140059
theorem R6183539 : Reach 6183539 := rs (se 1 (by rfl) ⟨4637654, by rfl⟩) R9275309
theorem R56263 : Reach 56263 := rs (se 1 (by rfl) ⟨42197, by rfl⟩) R84395
theorem R613453 : Reach 613453 := rs (se 3 (by rfl) ⟨115022, by rfl⟩) R230045
theorem R484967 : Reach 484967 := rs (se 1 (by rfl) ⟨363725, by rfl⟩) R727451
theorem R60031 : Reach 60031 := rs (se 1 (by rfl) ⟨45023, by rfl⟩) R90047
theorem R159353 : Reach 159353 := rs (se 2 (by rfl) ⟨59757, by rfl⟩) R119515
theorem R161135 : Reach 161135 := rs (se 1 (by rfl) ⟨120851, by rfl⟩) R241703
theorem R915259 : Reach 915259 := rs (se 1 (by rfl) ⟨686444, by rfl⟩) R1372889
theorem R523583 : Reach 523583 := rs (se 1 (by rfl) ⟨392687, by rfl⟩) R785375
theorem R101935 : Reach 101935 := rs (se 1 (by rfl) ⟨76451, by rfl⟩) R152903
theorem R233113 : Reach 233113 := rs (se 2 (by rfl) ⟨87417, by rfl⟩) R174835
theorem R626939 : Reach 626939 := rs (se 1 (by rfl) ⟨470204, by rfl⟩) R940409
theorem R201341 : Reach 201341 := rs (se 3 (by rfl) ⟨37751, by rfl⟩) R75503
theorem R70895 : Reach 70895 := rs (se 1 (by rfl) ⟨53171, by rfl⟩) R106343
theorem R334543 : Reach 334543 := rs (se 1 (by rfl) ⟨250907, by rfl⟩) R501815
theorem R1220345 : Reach 1220345 := rs (se 2 (by rfl) ⟨457629, by rfl⟩) R915259
theorem R106235 : Reach 106235 := rs (se 1 (by rfl) ⟨79676, by rfl⟩) R159353
theorem R74567 : Reach 74567 := rs (se 1 (by rfl) ⟨55925, by rfl⟩) R111851
theorem R107423 : Reach 107423 := rs (se 1 (by rfl) ⟨80567, by rfl⟩) R161135
theorem R75017 : Reach 75017 := rs (se 2 (by rfl) ⟨28131, by rfl⟩) R56263
theorem R75983 : Reach 75983 := rs (se 1 (by rfl) ⟨56987, by rfl⟩) R113975
theorem R76031 : Reach 76031 := rs (se 1 (by rfl) ⟨57023, by rfl⟩) R114047
theorem R78527 : Reach 78527 := rs (se 1 (by rfl) ⟨58895, by rfl⟩) R117791
theorem R275197 : Reach 275197 := rs (se 3 (by rfl) ⟨51599, by rfl⟩) R103199
theorem R80041 : Reach 80041 := rs (se 2 (by rfl) ⟨30015, by rfl⟩) R60031
theorem R309743 : Reach 309743 := rs (se 1 (by rfl) ⟨232307, by rfl⟩) R464615
theorem R47783 : Reach 47783 := rs (se 1 (by rfl) ⟨35837, by rfl⟩) R71675
theorem R179327 : Reach 179327 := rs (se 1 (by rfl) ⟨134495, by rfl⟩) R268991
theorem R48367 : Reach 48367 := rs (se 1 (by rfl) ⟨36275, by rfl⟩) R72551
theorem R48639 : Reach 48639 := rs (se 1 (by rfl) ⟨36479, by rfl⟩) R72959
theorem R48767 : Reach 48767 := rs (se 1 (by rfl) ⟨36575, by rfl⟩) R73151
theorem R48999 : Reach 48999 := rs (se 1 (by rfl) ⟨36749, by rfl⟩) R73499
theorem R50335 : Reach 50335 := rs (se 1 (by rfl) ⟨37751, by rfl⟩) R75503
theorem R707039 : Reach 707039 := rs (se 1 (by rfl) ⟨530279, by rfl⟩) R1060559
theorem R248993 : Reach 248993 := rs (se 2 (by rfl) ⟨93372, by rfl⟩) R186745
theorem R315647 : Reach 315647 := rs (se 1 (by rfl) ⟨236735, by rfl⟩) R473471
theorem R349055 : Reach 349055 := rs (se 1 (by rfl) ⟨261791, by rfl⟩) R523583
theorem R186583 : Reach 186583 := rs (se 1 (by rfl) ⟨139937, by rfl⟩) R279875
theorem R56623 : Reach 56623 := rs (se 1 (by rfl) ⟨42467, by rfl⟩) R84935
theorem R4251527 : Reach 4251527 := rs (se 1 (by rfl) ⟨3188645, by rfl⟩) R6377291
theorem R188507 : Reach 188507 := rs (se 1 (by rfl) ⟨141380, by rfl⟩) R282761
theorem R4122359 : Reach 4122359 := rs (se 1 (by rfl) ⟨3091769, by rfl⟩) R6183539
theorem R322157 : Reach 322157 := rs (se 3 (by rfl) ⟨60404, by rfl⟩) R120809
theorem R323311 : Reach 323311 := rs (se 1 (by rfl) ⟨242483, by rfl⟩) R484967
theorem R193337 : Reach 193337 := rs (se 2 (by rfl) ⟨72501, by rfl⟩) R145003
theorem R817937 : Reach 817937 := rs (se 2 (by rfl) ⟨306726, by rfl⟩) R613453
theorem R491291 : Reach 491291 := rs (se 1 (by rfl) ⟨368468, by rfl⟩) R736937
theorem R165995 : Reach 165995 := rs (se 1 (by rfl) ⟨124496, by rfl⟩) R248993
theorem R134227 : Reach 134227 := rs (se 1 (by rfl) ⟨100670, by rfl⟩) R201341
theorem R232703 : Reach 232703 := rs (se 1 (by rfl) ⟨174527, by rfl⟩) R349055
theorem R135913 : Reach 135913 := rs (se 2 (by rfl) ⟨50967, by rfl⟩) R101935
theorem R431081 : Reach 431081 := rs (se 2 (by rfl) ⟨161655, by rfl⟩) R323311
theorem R70823 : Reach 70823 := rs (se 1 (by rfl) ⟨53117, by rfl⟩) R106235
theorem R71615 : Reach 71615 := rs (se 1 (by rfl) ⟨53711, by rfl⟩) R107423
theorem R366929 : Reach 366929 := rs (se 2 (by rfl) ⟨137598, by rfl⟩) R275197
theorem R106721 : Reach 106721 := rs (se 2 (by rfl) ⟨40020, by rfl⟩) R80041
theorem R206495 : Reach 206495 := rs (se 1 (by rfl) ⟨154871, by rfl⟩) R309743
theorem R75497 : Reach 75497 := rs (se 2 (by rfl) ⟨28311, by rfl⟩) R56623
theorem R471359 : Reach 471359 := rs (se 1 (by rfl) ⟨353519, by rfl⟩) R707039
theorem R209405 : Reach 209405 := rs (se 3 (by rfl) ⟨39263, by rfl⟩) R78527
theorem R210431 : Reach 210431 := rs (se 1 (by rfl) ⟨157823, by rfl⟩) R315647
theorem R47263 : Reach 47263 := rs (se 1 (by rfl) ⟨35447, by rfl⟩) R70895
theorem R310817 : Reach 310817 := rs (se 2 (by rfl) ⟨116556, by rfl⟩) R233113
theorem R2834351 : Reach 2834351 := rs (se 1 (by rfl) ⟨2125763, by rfl⟩) R4251527
theorem R49711 : Reach 49711 := rs (se 1 (by rfl) ⟨37283, by rfl⟩) R74567
theorem R50011 : Reach 50011 := rs (se 1 (by rfl) ⟨37508, by rfl⟩) R75017
theorem R50655 : Reach 50655 := rs (se 1 (by rfl) ⟨37991, by rfl⟩) R75983
theorem R50687 : Reach 50687 := rs (se 1 (by rfl) ⟨38015, by rfl⟩) R76031
theorem R214771 : Reach 214771 := rs (se 1 (by rfl) ⟨161078, by rfl⟩) R322157
theorem R248777 : Reach 248777 := rs (se 2 (by rfl) ⟨93291, by rfl⟩) R186583
theorem R446057 : Reach 446057 := rs (se 2 (by rfl) ⟨167271, by rfl⟩) R334543
theorem R545291 : Reach 545291 := rs (se 1 (by rfl) ⟨408968, by rfl⟩) R817937
theorem R119551 : Reach 119551 := rs (se 1 (by rfl) ⟨89663, by rfl⟩) R179327
theorem R417959 : Reach 417959 := rs (se 1 (by rfl) ⟨313469, by rfl⟩) R626939
theorem R813563 : Reach 813563 := rs (se 1 (by rfl) ⟨610172, by rfl⟩) R1220345
theorem R125671 : Reach 125671 := rs (se 1 (by rfl) ⟨94253, by rfl⟩) R188507
theorem R2748239 : Reach 2748239 := rs (se 1 (by rfl) ⟨2061179, by rfl⟩) R4122359
theorem R128891 : Reach 128891 := rs (se 1 (by rfl) ⟨96668, by rfl⟩) R193337
theorem R327527 : Reach 327527 := rs (se 1 (by rfl) ⟨245645, by rfl⟩) R491291
theorem R558413 : Reach 558413 := rs (se 3 (by rfl) ⟨104702, by rfl⟩) R209405
theorem R165851 : Reach 165851 := rs (se 1 (by rfl) ⟨124388, by rfl⟩) R248777
theorem R297371 : Reach 297371 := rs (se 1 (by rfl) ⟨223028, by rfl⟩) R446057
theorem R363527 : Reach 363527 := rs (se 1 (by rfl) ⟨272645, by rfl⟩) R545291
theorem R167561 : Reach 167561 := rs (se 2 (by rfl) ⟨62835, by rfl⟩) R125671
theorem R201325 : Reach 201325 := rs (se 3 (by rfl) ⟨37748, by rfl⟩) R75497
theorem R71147 : Reach 71147 := rs (se 1 (by rfl) ⟨53360, by rfl⟩) R106721
theorem R137663 : Reach 137663 := rs (se 1 (by rfl) ⟨103247, by rfl⟩) R206495
theorem R140287 : Reach 140287 := rs (se 1 (by rfl) ⟨105215, by rfl⟩) R210431
theorem R207211 : Reach 207211 := rs (se 1 (by rfl) ⟨155408, by rfl⟩) R310817
theorem R1256957 : Reach 1256957 := rs (se 3 (by rfl) ⟨235679, by rfl⟩) R471359
theorem R110663 : Reach 110663 := rs (se 1 (by rfl) ⟨82997, by rfl⟩) R165995
theorem R47215 : Reach 47215 := rs (se 1 (by rfl) ⟨35411, by rfl⟩) R70823
theorem R47743 : Reach 47743 := rs (se 1 (by rfl) ⟨35807, by rfl⟩) R71615
theorem R178969 : Reach 178969 := rs (se 2 (by rfl) ⟨67113, by rfl⟩) R134227
theorem R244619 : Reach 244619 := rs (se 1 (by rfl) ⟨183464, by rfl⟩) R366929
theorem R278639 : Reach 278639 := rs (se 1 (by rfl) ⟨208979, by rfl⟩) R417959
theorem R181217 : Reach 181217 := rs (se 2 (by rfl) ⟨67956, by rfl⟩) R135913
theorem R50331 : Reach 50331 := rs (se 1 (by rfl) ⟨37748, by rfl⟩) R75497
theorem R542375 : Reach 542375 := rs (se 1 (by rfl) ⟨406781, by rfl⟩) R813563
theorem R85927 : Reach 85927 := rs (se 1 (by rfl) ⟨64445, by rfl⟩) R128891
theorem R218351 : Reach 218351 := rs (se 1 (by rfl) ⟨163763, by rfl⟩) R327527
theorem R1889567 : Reach 1889567 := rs (se 1 (by rfl) ⟨1417175, by rfl⟩) R2834351
theorem R155135 : Reach 155135 := rs (se 1 (by rfl) ⟨116351, by rfl⟩) R232703
theorem R286361 : Reach 286361 := rs (se 2 (by rfl) ⟨107385, by rfl⟩) R214771
theorem R287387 : Reach 287387 := rs (se 1 (by rfl) ⟨215540, by rfl⟩) R431081
theorem R159401 : Reach 159401 := rs (se 2 (by rfl) ⟨59775, by rfl⟩) R119551
theorem R1832159 : Reach 1832159 := rs (se 1 (by rfl) ⟨1374119, by rfl⟩) R2748239
theorem R361583 : Reach 361583 := rs (se 1 (by rfl) ⟨271187, by rfl⟩) R542375
theorem R198247 : Reach 198247 := rs (se 1 (by rfl) ⟨148685, by rfl⟩) R297371
theorem R103423 : Reach 103423 := rs (se 1 (by rfl) ⟨77567, by rfl⟩) R155135
theorem R268433 : Reach 268433 := rs (se 2 (by rfl) ⟨100662, by rfl⟩) R201325
theorem R106267 : Reach 106267 := rs (se 1 (by rfl) ⟨79700, by rfl⟩) R159401
theorem R73775 : Reach 73775 := rs (se 1 (by rfl) ⟨55331, by rfl⟩) R110663
theorem R1221439 : Reach 1221439 := rs (se 1 (by rfl) ⟨916079, by rfl⟩) R1832159
theorem R238625 : Reach 238625 := rs (se 2 (by rfl) ⟨89484, by rfl⟩) R178969
theorem R372275 : Reach 372275 := rs (se 1 (by rfl) ⟨279206, by rfl⟩) R558413
theorem R110567 : Reach 110567 := rs (se 1 (by rfl) ⟨82925, by rfl⟩) R165851
theorem R242351 : Reach 242351 := rs (se 1 (by rfl) ⟨181763, by rfl⟩) R363527
theorem R111707 : Reach 111707 := rs (se 1 (by rfl) ⟨83780, by rfl⟩) R167561
theorem R276281 : Reach 276281 := rs (se 2 (by rfl) ⟨103605, by rfl⟩) R207211
theorem R145567 : Reach 145567 := rs (se 1 (by rfl) ⟨109175, by rfl⟩) R218351
theorem R1259711 : Reach 1259711 := rs (se 1 (by rfl) ⟨944783, by rfl⟩) R1889567
theorem R47431 : Reach 47431 := rs (se 1 (by rfl) ⟨35573, by rfl⟩) R71147
theorem R114569 : Reach 114569 := rs (se 2 (by rfl) ⟨42963, by rfl⟩) R85927
theorem R837971 : Reach 837971 := rs (se 1 (by rfl) ⟨628478, by rfl⟩) R1256957
theorem R185759 : Reach 185759 := rs (se 1 (by rfl) ⟨139319, by rfl⟩) R278639
theorem R120811 : Reach 120811 := rs (se 1 (by rfl) ⟨90608, by rfl⟩) R181217
theorem R187049 : Reach 187049 := rs (se 2 (by rfl) ⟨70143, by rfl⟩) R140287
theorem R91775 : Reach 91775 := rs (se 1 (by rfl) ⟨68831, by rfl⟩) R137663
theorem R190907 : Reach 190907 := rs (se 1 (by rfl) ⟨143180, by rfl⟩) R286361
theorem R191591 : Reach 191591 := rs (se 1 (by rfl) ⟨143693, by rfl⟩) R287387
theorem R163079 : Reach 163079 := rs (se 1 (by rfl) ⟨122309, by rfl⟩) R244619
theorem R558647 : Reach 558647 := rs (se 1 (by rfl) ⟨418985, by rfl⟩) R837971
theorem R264329 : Reach 264329 := rs (se 2 (by rfl) ⟨99123, by rfl⟩) R198247
theorem R137897 : Reach 137897 := rs (se 2 (by rfl) ⟨51711, by rfl⟩) R103423
theorem R73711 : Reach 73711 := rs (se 1 (by rfl) ⟨55283, by rfl⟩) R110567
theorem R74471 : Reach 74471 := rs (se 1 (by rfl) ⟨55853, by rfl⟩) R111707
theorem R108719 : Reach 108719 := rs (se 1 (by rfl) ⟨81539, by rfl⟩) R163079
theorem R141689 : Reach 141689 := rs (se 2 (by rfl) ⟨53133, by rfl⟩) R106267
theorem R76379 : Reach 76379 := rs (se 1 (by rfl) ⟨57284, by rfl⟩) R114569
theorem R241055 : Reach 241055 := rs (se 1 (by rfl) ⟨180791, by rfl⟩) R361583
theorem R178955 : Reach 178955 := rs (se 1 (by rfl) ⟨134216, by rfl⟩) R268433
theorem R49183 : Reach 49183 := rs (se 1 (by rfl) ⟨36887, by rfl⟩) R73775
theorem R248183 : Reach 248183 := rs (se 1 (by rfl) ⟨186137, by rfl⟩) R372275
theorem R184187 : Reach 184187 := rs (se 1 (by rfl) ⟨138140, by rfl⟩) R276281
theorem R839807 : Reach 839807 := rs (se 1 (by rfl) ⟨629855, by rfl⟩) R1259711
theorem R1628585 : Reach 1628585 := rs (se 2 (by rfl) ⟨610719, by rfl⟩) R1221439
theorem R123839 : Reach 123839 := rs (se 1 (by rfl) ⟨92879, by rfl⟩) R185759
theorem R124699 : Reach 124699 := rs (se 1 (by rfl) ⟨93524, by rfl⟩) R187049
theorem R159083 : Reach 159083 := rs (se 1 (by rfl) ⟨119312, by rfl⟩) R238625
theorem R61183 : Reach 61183 := rs (se 1 (by rfl) ⟨45887, by rfl⟩) R91775
theorem R127271 : Reach 127271 := rs (se 1 (by rfl) ⟨95453, by rfl⟩) R190907
theorem R127727 : Reach 127727 := rs (se 1 (by rfl) ⟨95795, by rfl⟩) R191591
theorem R161081 : Reach 161081 := rs (se 2 (by rfl) ⟨60405, by rfl⟩) R120811
theorem R194089 : Reach 194089 := rs (se 2 (by rfl) ⟨72783, by rfl⟩) R145567
theorem R161567 : Reach 161567 := rs (se 1 (by rfl) ⟨121175, by rfl⟩) R242351
theorem R165455 : Reach 165455 := rs (se 1 (by rfl) ⟨124091, by rfl⟩) R248183
theorem R166265 : Reach 166265 := rs (se 2 (by rfl) ⟨62349, by rfl⟩) R124699
theorem R559871 : Reach 559871 := rs (se 1 (by rfl) ⟨419903, by rfl⟩) R839807
theorem R1085723 : Reach 1085723 := rs (se 1 (by rfl) ⟨814292, by rfl⟩) R1628585
theorem R72479 : Reach 72479 := rs (se 1 (by rfl) ⟨54359, by rfl⟩) R108719
theorem R106055 : Reach 106055 := rs (se 1 (by rfl) ⟨79541, by rfl⟩) R159083
theorem R107387 : Reach 107387 := rs (se 1 (by rfl) ⟨80540, by rfl⟩) R161081
theorem R107711 : Reach 107711 := rs (se 1 (by rfl) ⟨80783, by rfl⟩) R161567
theorem R372431 : Reach 372431 := rs (se 1 (by rfl) ⟨279323, by rfl⟩) R558647
theorem R176219 : Reach 176219 := rs (se 1 (by rfl) ⟨132164, by rfl⟩) R264329
theorem R81577 : Reach 81577 := rs (se 2 (by rfl) ⟨30591, by rfl⟩) R61183
theorem R49647 : Reach 49647 := rs (se 1 (by rfl) ⟨37235, by rfl⟩) R74471
theorem R82559 : Reach 82559 := rs (se 1 (by rfl) ⟨61919, by rfl⟩) R123839
theorem R50919 : Reach 50919 := rs (se 1 (by rfl) ⟨38189, by rfl⟩) R76379
theorem R84847 : Reach 84847 := rs (se 1 (by rfl) ⟨63635, by rfl⟩) R127271
theorem R85151 : Reach 85151 := rs (se 1 (by rfl) ⟨63863, by rfl⟩) R127727
theorem R119303 : Reach 119303 := rs (se 1 (by rfl) ⟨89477, by rfl⟩) R178955
theorem R122791 : Reach 122791 := rs (se 1 (by rfl) ⟨92093, by rfl⟩) R184187
theorem R91931 : Reach 91931 := rs (se 1 (by rfl) ⟨68948, by rfl⟩) R137897
theorem R94459 : Reach 94459 := rs (se 1 (by rfl) ⟨70844, by rfl⟩) R141689
theorem R258785 : Reach 258785 := rs (se 2 (by rfl) ⟨97044, by rfl⟩) R194089
theorem R160703 : Reach 160703 := rs (se 1 (by rfl) ⟨120527, by rfl⟩) R241055
theorem R98281 : Reach 98281 := rs (se 2 (by rfl) ⟨36855, by rfl⟩) R73711
theorem R723815 : Reach 723815 := rs (se 1 (by rfl) ⟨542861, by rfl⟩) R1085723
theorem R70703 : Reach 70703 := rs (se 1 (by rfl) ⟨53027, by rfl⟩) R106055
theorem R71591 : Reach 71591 := rs (se 1 (by rfl) ⟨53693, by rfl⟩) R107387
theorem R71807 : Reach 71807 := rs (se 1 (by rfl) ⟨53855, by rfl⟩) R107711
theorem R172523 : Reach 172523 := rs (se 1 (by rfl) ⟨129392, by rfl⟩) R258785
theorem R107135 : Reach 107135 := rs (se 1 (by rfl) ⟨80351, by rfl⟩) R160703
theorem R435077 : Reach 435077 := rs (se 4 (by rfl) ⟨40788, by rfl⟩) R81577
theorem R110303 : Reach 110303 := rs (se 1 (by rfl) ⟨82727, by rfl⟩) R165455
theorem R110843 : Reach 110843 := rs (se 1 (by rfl) ⟨83132, by rfl⟩) R166265
theorem R373247 : Reach 373247 := rs (se 1 (by rfl) ⟨279935, by rfl⟩) R559871
theorem R79535 : Reach 79535 := rs (se 1 (by rfl) ⟨59651, by rfl⟩) R119303
theorem R113129 : Reach 113129 := rs (se 2 (by rfl) ⟨42423, by rfl⟩) R84847
theorem R48319 : Reach 48319 := rs (se 1 (by rfl) ⟨36239, by rfl⟩) R72479
theorem R245149 : Reach 245149 := rs (se 3 (by rfl) ⟨45965, by rfl⟩) R91931
theorem R248287 : Reach 248287 := rs (se 1 (by rfl) ⟨186215, by rfl⟩) R372431
theorem R117479 : Reach 117479 := rs (se 1 (by rfl) ⟨88109, by rfl⟩) R176219
theorem R55039 : Reach 55039 := rs (se 1 (by rfl) ⟨41279, by rfl⟩) R82559
theorem R56767 : Reach 56767 := rs (se 1 (by rfl) ⟨42575, by rfl⟩) R85151
theorem R125945 : Reach 125945 := rs (se 2 (by rfl) ⟨47229, by rfl⟩) R94459
theorem R163721 : Reach 163721 := rs (se 2 (by rfl) ⟨61395, by rfl⟩) R122791
theorem R131041 : Reach 131041 := rs (se 2 (by rfl) ⟨49140, by rfl⟩) R98281
theorem R331049 : Reach 331049 := rs (se 2 (by rfl) ⟨124143, by rfl⟩) R248287
theorem R71423 : Reach 71423 := rs (se 1 (by rfl) ⟨53567, by rfl⟩) R107135
theorem R73385 : Reach 73385 := rs (se 2 (by rfl) ⟨27519, by rfl⟩) R55039
theorem R73535 : Reach 73535 := rs (se 1 (by rfl) ⟨55151, by rfl⟩) R110303
theorem R73895 : Reach 73895 := rs (se 1 (by rfl) ⟨55421, by rfl⟩) R110843
theorem R75419 : Reach 75419 := rs (se 1 (by rfl) ⟨56564, by rfl⟩) R113129
theorem R75689 : Reach 75689 := rs (se 2 (by rfl) ⟨28383, by rfl⟩) R56767
theorem R109147 : Reach 109147 := rs (se 1 (by rfl) ⟨81860, by rfl⟩) R163721
theorem R174721 : Reach 174721 := rs (se 2 (by rfl) ⟨65520, by rfl⟩) R131041
theorem R78319 : Reach 78319 := rs (se 1 (by rfl) ⟨58739, by rfl⟩) R117479
theorem R47135 : Reach 47135 := rs (se 1 (by rfl) ⟨35351, by rfl⟩) R70703
theorem R47727 : Reach 47727 := rs (se 1 (by rfl) ⟨35795, by rfl⟩) R71591
theorem R47871 : Reach 47871 := rs (se 1 (by rfl) ⟨35903, by rfl⟩) R71807
theorem R115015 : Reach 115015 := rs (se 1 (by rfl) ⟨86261, by rfl⟩) R172523
theorem R83963 : Reach 83963 := rs (se 1 (by rfl) ⟨62972, by rfl⟩) R125945
theorem R248831 : Reach 248831 := rs (se 1 (by rfl) ⟨186623, by rfl⟩) R373247
theorem R53023 : Reach 53023 := rs (se 1 (by rfl) ⟨39767, by rfl⟩) R79535
theorem R482543 : Reach 482543 := rs (se 1 (by rfl) ⟨361907, by rfl⟩) R723815
theorem R290051 : Reach 290051 := rs (se 1 (by rfl) ⟨217538, by rfl⟩) R435077
theorem R1307461 : Reach 1307461 := rs (se 4 (by rfl) ⟨122574, by rfl⟩) R245149
theorem R165887 : Reach 165887 := rs (se 1 (by rfl) ⟨124415, by rfl⟩) R248831
theorem R232961 : Reach 232961 := rs (se 2 (by rfl) ⟨87360, by rfl⟩) R174721
theorem R70697 : Reach 70697 := rs (se 2 (by rfl) ⟨26511, by rfl⟩) R53023
theorem R104425 : Reach 104425 := rs (se 2 (by rfl) ⟨39159, by rfl⟩) R78319
theorem R1743281 : Reach 1743281 := rs (se 2 (by rfl) ⟨653730, by rfl⟩) R1307461
theorem R145529 : Reach 145529 := rs (se 2 (by rfl) ⟨54573, by rfl⟩) R109147
theorem R47615 : Reach 47615 := rs (se 1 (by rfl) ⟨35711, by rfl⟩) R71423
theorem R48923 : Reach 48923 := rs (se 1 (by rfl) ⟨36692, by rfl⟩) R73385
theorem R49023 : Reach 49023 := rs (se 1 (by rfl) ⟨36767, by rfl⟩) R73535
theorem R49263 : Reach 49263 := rs (se 1 (by rfl) ⟨36947, by rfl⟩) R73895
theorem R50279 : Reach 50279 := rs (se 1 (by rfl) ⟨37709, by rfl⟩) R75419
theorem R50459 : Reach 50459 := rs (se 1 (by rfl) ⟨37844, by rfl⟩) R75689
theorem R153353 : Reach 153353 := rs (se 2 (by rfl) ⟨57507, by rfl⟩) R115015
theorem R55975 : Reach 55975 := rs (se 1 (by rfl) ⟨41981, by rfl⟩) R83963
theorem R220699 : Reach 220699 := rs (se 1 (by rfl) ⟨165524, by rfl⟩) R331049
theorem R321695 : Reach 321695 := rs (se 1 (by rfl) ⟨241271, by rfl⟩) R482543
theorem R193367 : Reach 193367 := rs (se 1 (by rfl) ⟨145025, by rfl⟩) R290051
theorem R102235 : Reach 102235 := rs (se 1 (by rfl) ⟨76676, by rfl⟩) R153353
theorem R74633 : Reach 74633 := rs (se 2 (by rfl) ⟨27987, by rfl⟩) R55975
theorem R110591 : Reach 110591 := rs (se 1 (by rfl) ⟨82943, by rfl⟩) R165887
theorem R47131 : Reach 47131 := rs (se 1 (by rfl) ⟨35348, by rfl⟩) R70697
theorem R1162187 : Reach 1162187 := rs (se 1 (by rfl) ⟨871640, by rfl⟩) R1743281
theorem R214463 : Reach 214463 := rs (se 1 (by rfl) ⟨160847, by rfl⟩) R321695
theorem R128911 : Reach 128911 := rs (se 1 (by rfl) ⟨96683, by rfl⟩) R193367
theorem R621229 : Reach 621229 := rs (se 3 (by rfl) ⟨116480, by rfl⟩) R232961
theorem R97019 : Reach 97019 := rs (se 1 (by rfl) ⟨72764, by rfl⟩) R145529
theorem R294265 : Reach 294265 := rs (se 2 (by rfl) ⟨110349, by rfl⟩) R220699
theorem R2227733 : Reach 2227733 := rs (se 6 (by rfl) ⟨52212, by rfl⟩) R104425
theorem R136313 : Reach 136313 := rs (se 2 (by rfl) ⟨51117, by rfl⟩) R102235
theorem R171881 : Reach 171881 := rs (se 2 (by rfl) ⟨64455, by rfl⟩) R128911
theorem R73727 : Reach 73727 := rs (se 1 (by rfl) ⟨55295, by rfl⟩) R110591
theorem R828305 : Reach 828305 := rs (se 2 (by rfl) ⟨310614, by rfl⟩) R621229
theorem R1485155 : Reach 1485155 := rs (se 1 (by rfl) ⟨1113866, by rfl⟩) R2227733
theorem R142975 : Reach 142975 := rs (se 1 (by rfl) ⟨107231, by rfl⟩) R214463
theorem R49755 : Reach 49755 := rs (se 1 (by rfl) ⟨37316, by rfl⟩) R74633
theorem R774791 : Reach 774791 := rs (se 1 (by rfl) ⟨581093, by rfl⟩) R1162187
theorem R392353 : Reach 392353 := rs (se 2 (by rfl) ⟨147132, by rfl⟩) R294265
theorem R64679 : Reach 64679 := rs (se 1 (by rfl) ⟨48509, by rfl⟩) R97019
theorem R990103 : Reach 990103 := rs (se 1 (by rfl) ⟨742577, by rfl⟩) R1485155
theorem R172477 : Reach 172477 := rs (se 3 (by rfl) ⟨32339, by rfl⟩) R64679
theorem R114587 : Reach 114587 := rs (se 1 (by rfl) ⟨85940, by rfl⟩) R171881
theorem R49151 : Reach 49151 := rs (se 1 (by rfl) ⟨36863, by rfl⟩) R73727
theorem R516527 : Reach 516527 := rs (se 1 (by rfl) ⟨387395, by rfl⟩) R774791
theorem R90875 : Reach 90875 := rs (se 1 (by rfl) ⟨68156, by rfl⟩) R136313
theorem R190633 : Reach 190633 := rs (se 2 (by rfl) ⟨71487, by rfl⟩) R142975
theorem R552203 : Reach 552203 := rs (se 1 (by rfl) ⟨414152, by rfl⟩) R828305
theorem R2092549 : Reach 2092549 := rs (se 4 (by rfl) ⟨196176, by rfl⟩) R392353
theorem R229969 : Reach 229969 := rs (se 2 (by rfl) ⟨86238, by rfl⟩) R172477
theorem R2790065 : Reach 2790065 := rs (se 2 (by rfl) ⟨1046274, by rfl⟩) R2092549
theorem R368135 : Reach 368135 := rs (se 1 (by rfl) ⟨276101, by rfl⟩) R552203
theorem R1320137 : Reach 1320137 := rs (se 2 (by rfl) ⟨495051, by rfl⟩) R990103
theorem R76391 : Reach 76391 := rs (se 1 (by rfl) ⟨57293, by rfl⟩) R114587
theorem R344351 : Reach 344351 := rs (se 1 (by rfl) ⟨258263, by rfl⟩) R516527
theorem R254177 : Reach 254177 := rs (se 2 (by rfl) ⟨95316, by rfl⟩) R190633
theorem R60583 : Reach 60583 := rs (se 1 (by rfl) ⟨45437, by rfl⟩) R90875
theorem R229567 : Reach 229567 := rs (se 1 (by rfl) ⟨172175, by rfl⟩) R344351
theorem R7440173 : Reach 7440173 := rs (se 3 (by rfl) ⟨1395032, by rfl⟩) R2790065
theorem R169451 : Reach 169451 := rs (se 1 (by rfl) ⟨127088, by rfl⟩) R254177
theorem R306625 : Reach 306625 := rs (se 2 (by rfl) ⟨114984, by rfl⟩) R229969
theorem R80777 : Reach 80777 := rs (se 2 (by rfl) ⟨30291, by rfl⟩) R60583
theorem R245423 : Reach 245423 := rs (se 1 (by rfl) ⟨184067, by rfl⟩) R368135
theorem R50927 : Reach 50927 := rs (se 1 (by rfl) ⟨38195, by rfl⟩) R76391
theorem R880091 : Reach 880091 := rs (se 1 (by rfl) ⟨660068, by rfl⟩) R1320137
theorem R306089 : Reach 306089 := rs (se 2 (by rfl) ⟨114783, by rfl⟩) R229567
theorem R4960115 : Reach 4960115 := rs (se 1 (by rfl) ⟨3720086, by rfl⟩) R7440173
theorem R112967 : Reach 112967 := rs (se 1 (by rfl) ⟨84725, by rfl⟩) R169451
theorem R408833 : Reach 408833 := rs (se 2 (by rfl) ⟨153312, by rfl⟩) R306625
theorem R215405 : Reach 215405 := rs (se 3 (by rfl) ⟨40388, by rfl⟩) R80777
theorem R53851 : Reach 53851 := rs (se 1 (by rfl) ⟨40388, by rfl⟩) R80777
theorem R586727 : Reach 586727 := rs (se 1 (by rfl) ⟨440045, by rfl⟩) R880091
theorem R163615 : Reach 163615 := rs (se 1 (by rfl) ⟨122711, by rfl⟩) R245423
theorem R71801 : Reach 71801 := rs (se 2 (by rfl) ⟨26925, by rfl⟩) R53851
theorem R204059 : Reach 204059 := rs (se 1 (by rfl) ⟨153044, by rfl⟩) R306089
theorem R75311 : Reach 75311 := rs (se 1 (by rfl) ⟨56483, by rfl⟩) R112967
theorem R272555 : Reach 272555 := rs (se 1 (by rfl) ⟨204416, by rfl⟩) R408833
theorem R143603 : Reach 143603 := rs (se 1 (by rfl) ⟨107702, by rfl⟩) R215405
theorem R218153 : Reach 218153 := rs (se 2 (by rfl) ⟨81807, by rfl⟩) R163615
theorem R3306743 : Reach 3306743 := rs (se 1 (by rfl) ⟨2480057, by rfl⟩) R4960115
theorem R391151 : Reach 391151 := rs (se 1 (by rfl) ⟨293363, by rfl⟩) R586727
theorem R136039 : Reach 136039 := rs (se 1 (by rfl) ⟨102029, by rfl⟩) R204059
theorem R2204495 : Reach 2204495 := rs (se 1 (by rfl) ⟨1653371, by rfl⟩) R3306743
theorem R47867 : Reach 47867 := rs (se 1 (by rfl) ⟨35900, by rfl⟩) R71801
theorem R50207 : Reach 50207 := rs (se 1 (by rfl) ⟨37655, by rfl⟩) R75311
theorem R181703 : Reach 181703 := rs (se 1 (by rfl) ⟨136277, by rfl⟩) R272555
theorem R581741 : Reach 581741 := rs (se 3 (by rfl) ⟨109076, by rfl⟩) R218153
theorem R95735 : Reach 95735 := rs (se 1 (by rfl) ⟨71801, by rfl⟩) R143603
theorem R260767 : Reach 260767 := rs (se 1 (by rfl) ⟨195575, by rfl⟩) R391151
theorem R181385 : Reach 181385 := rs (se 2 (by rfl) ⟨68019, by rfl⟩) R136039
theorem R347689 : Reach 347689 := rs (se 2 (by rfl) ⟨130383, by rfl⟩) R260767
theorem R121135 : Reach 121135 := rs (se 1 (by rfl) ⟨90851, by rfl⟩) R181703
theorem R387827 : Reach 387827 := rs (se 1 (by rfl) ⟨290870, by rfl⟩) R581741
theorem R1469663 : Reach 1469663 := rs (se 1 (by rfl) ⟨1102247, by rfl⟩) R2204495
theorem R63823 : Reach 63823 := rs (se 1 (by rfl) ⟨47867, by rfl⟩) R95735
theorem R463585 : Reach 463585 := rs (se 2 (by rfl) ⟨173844, by rfl⟩) R347689
theorem R85097 : Reach 85097 := rs (se 2 (by rfl) ⟨31911, by rfl⟩) R63823
theorem R120923 : Reach 120923 := rs (se 1 (by rfl) ⟨90692, by rfl⟩) R181385
theorem R258551 : Reach 258551 := rs (se 1 (by rfl) ⟨193913, by rfl⟩) R387827
theorem R979775 : Reach 979775 := rs (se 1 (by rfl) ⟨734831, by rfl⟩) R1469663
theorem R161513 : Reach 161513 := rs (se 2 (by rfl) ⟨60567, by rfl⟩) R121135
theorem R172367 : Reach 172367 := rs (se 1 (by rfl) ⟨129275, by rfl⟩) R258551
theorem R107675 : Reach 107675 := rs (se 1 (by rfl) ⟨80756, by rfl⟩) R161513
theorem R80615 : Reach 80615 := rs (se 1 (by rfl) ⟨60461, by rfl⟩) R120923
theorem R56731 : Reach 56731 := rs (se 1 (by rfl) ⟨42548, by rfl⟩) R85097
theorem R618113 : Reach 618113 := rs (se 2 (by rfl) ⟨231792, by rfl⟩) R463585
theorem R653183 : Reach 653183 := rs (se 1 (by rfl) ⟨489887, by rfl⟩) R979775
theorem R71783 : Reach 71783 := rs (se 1 (by rfl) ⟨53837, by rfl⟩) R107675
theorem R435455 : Reach 435455 := rs (se 1 (by rfl) ⟨326591, by rfl⟩) R653183
theorem R75641 : Reach 75641 := rs (se 2 (by rfl) ⟨28365, by rfl⟩) R56731
theorem R114911 : Reach 114911 := rs (se 1 (by rfl) ⟨86183, by rfl⟩) R172367
theorem R412075 : Reach 412075 := rs (se 1 (by rfl) ⟨309056, by rfl⟩) R618113
theorem R53743 : Reach 53743 := rs (se 1 (by rfl) ⟨40307, by rfl⟩) R80615
theorem R71657 : Reach 71657 := rs (se 2 (by rfl) ⟨26871, by rfl⟩) R53743
theorem R76607 : Reach 76607 := rs (se 1 (by rfl) ⟨57455, by rfl⟩) R114911
theorem R47855 : Reach 47855 := rs (se 1 (by rfl) ⟨35891, by rfl⟩) R71783
theorem R50427 : Reach 50427 := rs (se 1 (by rfl) ⟨37820, by rfl⟩) R75641
theorem R549433 : Reach 549433 := rs (se 2 (by rfl) ⟨206037, by rfl⟩) R412075
theorem R290303 : Reach 290303 := rs (se 1 (by rfl) ⟨217727, by rfl⟩) R435455
theorem R732577 : Reach 732577 := rs (se 2 (by rfl) ⟨274716, by rfl⟩) R549433
theorem R47771 : Reach 47771 := rs (se 1 (by rfl) ⟨35828, by rfl⟩) R71657
theorem R51071 : Reach 51071 := rs (se 1 (by rfl) ⟨38303, by rfl⟩) R76607
theorem R193535 : Reach 193535 := rs (se 1 (by rfl) ⟨145151, by rfl⟩) R290303
theorem R976769 : Reach 976769 := rs (se 2 (by rfl) ⟨366288, by rfl⟩) R732577
theorem R129023 : Reach 129023 := rs (se 1 (by rfl) ⟨96767, by rfl⟩) R193535
theorem R86015 : Reach 86015 := rs (se 1 (by rfl) ⟨64511, by rfl⟩) R129023
theorem R651179 : Reach 651179 := rs (se 1 (by rfl) ⟨488384, by rfl⟩) R976769
theorem R434119 : Reach 434119 := rs (se 1 (by rfl) ⟨325589, by rfl⟩) R651179
theorem R57343 : Reach 57343 := rs (se 1 (by rfl) ⟨43007, by rfl⟩) R86015
theorem R76457 : Reach 76457 := rs (se 2 (by rfl) ⟨28671, by rfl⟩) R57343
theorem R578825 : Reach 578825 := rs (se 2 (by rfl) ⟨217059, by rfl⟩) R434119
theorem R50971 : Reach 50971 := rs (se 1 (by rfl) ⟨38228, by rfl⟩) R76457
theorem R385883 : Reach 385883 := rs (se 1 (by rfl) ⟨289412, by rfl⟩) R578825
theorem R257255 : Reach 257255 := rs (se 1 (by rfl) ⟨192941, by rfl⟩) R385883
theorem R171503 : Reach 171503 := rs (se 1 (by rfl) ⟨128627, by rfl⟩) R257255
theorem R114335 : Reach 114335 := rs (se 1 (by rfl) ⟨85751, by rfl⟩) R171503
theorem R76223 : Reach 76223 := rs (se 1 (by rfl) ⟨57167, by rfl⟩) R114335
theorem R50815 : Reach 50815 := rs (se 1 (by rfl) ⟨38111, by rfl⟩) R76223

theorem C0 (j : ℕ) (h1 : 23559 ≤ j) (h2 : j ≤ 24258) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R47119
  · exact R47121
  · exact R47123
  · exact R47125
  · exact R47127
  · exact R47129
  · exact R47131
  · exact R47133
  · exact R47135
  · exact R47137
  · exact R47139
  · exact R47141
  · exact R47143
  · exact R47145
  · exact R47147
  · exact R47149
  · exact R47151
  · exact R47153
  · exact R47155
  · exact R47157
  · exact R47159
  · exact R47161
  · exact R47163
  · exact R47165
  · exact R47167
  · exact R47169
  · exact R47171
  · exact R47173
  · exact R47175
  · exact R47177
  · exact R47179
  · exact R47181
  · exact R47183
  · exact R47185
  · exact R47187
  · exact R47189
  · exact R47191
  · exact R47193
  · exact R47195
  · exact R47197
  · exact R47199
  · exact R47201
  · exact R47203
  · exact R47205
  · exact R47207
  · exact R47209
  · exact R47211
  · exact R47213
  · exact R47215
  · exact R47217
  · exact R47219
  · exact R47221
  · exact R47223
  · exact R47225
  · exact R47227
  · exact R47229
  · exact R47231
  · exact R47233
  · exact R47235
  · exact R47237
  · exact R47239
  · exact R47241
  · exact R47243
  · exact R47245
  · exact R47247
  · exact R47249
  · exact R47251
  · exact R47253
  · exact R47255
  · exact R47257
  · exact R47259
  · exact R47261
  · exact R47263
  · exact R47265
  · exact R47267
  · exact R47269
  · exact R47271
  · exact R47273
  · exact R47275
  · exact R47277
  · exact R47279
  · exact R47281
  · exact R47283
  · exact R47285
  · exact R47287
  · exact R47289
  · exact R47291
  · exact R47293
  · exact R47295
  · exact R47297
  · exact R47299
  · exact R47301
  · exact R47303
  · exact R47305
  · exact R47307
  · exact R47309
  · exact R47311
  · exact R47313
  · exact R47315
  · exact R47317
  · exact R47319
  · exact R47321
  · exact R47323
  · exact R47325
  · exact R47327
  · exact R47329
  · exact R47331
  · exact R47333
  · exact R47335
  · exact R47337
  · exact R47339
  · exact R47341
  · exact R47343
  · exact R47345
  · exact R47347
  · exact R47349
  · exact R47351
  · exact R47353
  · exact R47355
  · exact R47357
  · exact R47359
  · exact R47361
  · exact R47363
  · exact R47365
  · exact R47367
  · exact R47369
  · exact R47371
  · exact R47373
  · exact R47375
  · exact R47377
  · exact R47379
  · exact R47381
  · exact R47383
  · exact R47385
  · exact R47387
  · exact R47389
  · exact R47391
  · exact R47393
  · exact R47395
  · exact R47397
  · exact R47399
  · exact R47401
  · exact R47403
  · exact R47405
  · exact R47407
  · exact R47409
  · exact R47411
  · exact R47413
  · exact R47415
  · exact R47417
  · exact R47419
  · exact R47421
  · exact R47423
  · exact R47425
  · exact R47427
  · exact R47429
  · exact R47431
  · exact R47433
  · exact R47435
  · exact R47437
  · exact R47439
  · exact R47441
  · exact R47443
  · exact R47445
  · exact R47447
  · exact R47449
  · exact R47451
  · exact R47453
  · exact R47455
  · exact R47457
  · exact R47459
  · exact R47461
  · exact R47463
  · exact R47465
  · exact R47467
  · exact R47469
  · exact R47471
  · exact R47473
  · exact R47475
  · exact R47477
  · exact R47479
  · exact R47481
  · exact R47483
  · exact R47485
  · exact R47487
  · exact R47489
  · exact R47491
  · exact R47493
  · exact R47495
  · exact R47497
  · exact R47499
  · exact R47501
  · exact R47503
  · exact R47505
  · exact R47507
  · exact R47509
  · exact R47511
  · exact R47513
  · exact R47515
  · exact R47517
  · exact R47519
  · exact R47521
  · exact R47523
  · exact R47525
  · exact R47527
  · exact R47529
  · exact R47531
  · exact R47533
  · exact R47535
  · exact R47537
  · exact R47539
  · exact R47541
  · exact R47543
  · exact R47545
  · exact R47547
  · exact R47549
  · exact R47551
  · exact R47553
  · exact R47555
  · exact R47557
  · exact R47559
  · exact R47561
  · exact R47563
  · exact R47565
  · exact R47567
  · exact R47569
  · exact R47571
  · exact R47573
  · exact R47575
  · exact R47577
  · exact R47579
  · exact R47581
  · exact R47583
  · exact R47585
  · exact R47587
  · exact R47589
  · exact R47591
  · exact R47593
  · exact R47595
  · exact R47597
  · exact R47599
  · exact R47601
  · exact R47603
  · exact R47605
  · exact R47607
  · exact R47609
  · exact R47611
  · exact R47613
  · exact R47615
  · exact R47617
  · exact R47619
  · exact R47621
  · exact R47623
  · exact R47625
  · exact R47627
  · exact R47629
  · exact R47631
  · exact R47633
  · exact R47635
  · exact R47637
  · exact R47639
  · exact R47641
  · exact R47643
  · exact R47645
  · exact R47647
  · exact R47649
  · exact R47651
  · exact R47653
  · exact R47655
  · exact R47657
  · exact R47659
  · exact R47661
  · exact R47663
  · exact R47665
  · exact R47667
  · exact R47669
  · exact R47671
  · exact R47673
  · exact R47675
  · exact R47677
  · exact R47679
  · exact R47681
  · exact R47683
  · exact R47685
  · exact R47687
  · exact R47689
  · exact R47691
  · exact R47693
  · exact R47695
  · exact R47697
  · exact R47699
  · exact R47701
  · exact R47703
  · exact R47705
  · exact R47707
  · exact R47709
  · exact R47711
  · exact R47713
  · exact R47715
  · exact R47717
  · exact R47719
  · exact R47721
  · exact R47723
  · exact R47725
  · exact R47727
  · exact R47729
  · exact R47731
  · exact R47733
  · exact R47735
  · exact R47737
  · exact R47739
  · exact R47741
  · exact R47743
  · exact R47745
  · exact R47747
  · exact R47749
  · exact R47751
  · exact R47753
  · exact R47755
  · exact R47757
  · exact R47759
  · exact R47761
  · exact R47763
  · exact R47765
  · exact R47767
  · exact R47769
  · exact R47771
  · exact R47773
  · exact R47775
  · exact R47777
  · exact R47779
  · exact R47781
  · exact R47783
  · exact R47785
  · exact R47787
  · exact R47789
  · exact R47791
  · exact R47793
  · exact R47795
  · exact R47797
  · exact R47799
  · exact R47801
  · exact R47803
  · exact R47805
  · exact R47807
  · exact R47809
  · exact R47811
  · exact R47813
  · exact R47815
  · exact R47817
  · exact R47819
  · exact R47821
  · exact R47823
  · exact R47825
  · exact R47827
  · exact R47829
  · exact R47831
  · exact R47833
  · exact R47835
  · exact R47837
  · exact R47839
  · exact R47841
  · exact R47843
  · exact R47845
  · exact R47847
  · exact R47849
  · exact R47851
  · exact R47853
  · exact R47855
  · exact R47857
  · exact R47859
  · exact R47861
  · exact R47863
  · exact R47865
  · exact R47867
  · exact R47869
  · exact R47871
  · exact R47873
  · exact R47875
  · exact R47877
  · exact R47879
  · exact R47881
  · exact R47883
  · exact R47885
  · exact R47887
  · exact R47889
  · exact R47891
  · exact R47893
  · exact R47895
  · exact R47897
  · exact R47899
  · exact R47901
  · exact R47903
  · exact R47905
  · exact R47907
  · exact R47909
  · exact R47911
  · exact R47913
  · exact R47915
  · exact R47917
  · exact R47919
  · exact R47921
  · exact R47923
  · exact R47925
  · exact R47927
  · exact R47929
  · exact R47931
  · exact R47933
  · exact R47935
  · exact R47937
  · exact R47939
  · exact R47941
  · exact R47943
  · exact R47945
  · exact R47947
  · exact R47949
  · exact R47951
  · exact R47953
  · exact R47955
  · exact R47957
  · exact R47959
  · exact R47961
  · exact R47963
  · exact R47965
  · exact R47967
  · exact R47969
  · exact R47971
  · exact R47973
  · exact R47975
  · exact R47977
  · exact R47979
  · exact R47981
  · exact R47983
  · exact R47985
  · exact R47987
  · exact R47989
  · exact R47991
  · exact R47993
  · exact R47995
  · exact R47997
  · exact R47999
  · exact R48001
  · exact R48003
  · exact R48005
  · exact R48007
  · exact R48009
  · exact R48011
  · exact R48013
  · exact R48015
  · exact R48017
  · exact R48019
  · exact R48021
  · exact R48023
  · exact R48025
  · exact R48027
  · exact R48029
  · exact R48031
  · exact R48033
  · exact R48035
  · exact R48037
  · exact R48039
  · exact R48041
  · exact R48043
  · exact R48045
  · exact R48047
  · exact R48049
  · exact R48051
  · exact R48053
  · exact R48055
  · exact R48057
  · exact R48059
  · exact R48061
  · exact R48063
  · exact R48065
  · exact R48067
  · exact R48069
  · exact R48071
  · exact R48073
  · exact R48075
  · exact R48077
  · exact R48079
  · exact R48081
  · exact R48083
  · exact R48085
  · exact R48087
  · exact R48089
  · exact R48091
  · exact R48093
  · exact R48095
  · exact R48097
  · exact R48099
  · exact R48101
  · exact R48103
  · exact R48105
  · exact R48107
  · exact R48109
  · exact R48111
  · exact R48113
  · exact R48115
  · exact R48117
  · exact R48119
  · exact R48121
  · exact R48123
  · exact R48125
  · exact R48127
  · exact R48129
  · exact R48131
  · exact R48133
  · exact R48135
  · exact R48137
  · exact R48139
  · exact R48141
  · exact R48143
  · exact R48145
  · exact R48147
  · exact R48149
  · exact R48151
  · exact R48153
  · exact R48155
  · exact R48157
  · exact R48159
  · exact R48161
  · exact R48163
  · exact R48165
  · exact R48167
  · exact R48169
  · exact R48171
  · exact R48173
  · exact R48175
  · exact R48177
  · exact R48179
  · exact R48181
  · exact R48183
  · exact R48185
  · exact R48187
  · exact R48189
  · exact R48191
  · exact R48193
  · exact R48195
  · exact R48197
  · exact R48199
  · exact R48201
  · exact R48203
  · exact R48205
  · exact R48207
  · exact R48209
  · exact R48211
  · exact R48213
  · exact R48215
  · exact R48217
  · exact R48219
  · exact R48221
  · exact R48223
  · exact R48225
  · exact R48227
  · exact R48229
  · exact R48231
  · exact R48233
  · exact R48235
  · exact R48237
  · exact R48239
  · exact R48241
  · exact R48243
  · exact R48245
  · exact R48247
  · exact R48249
  · exact R48251
  · exact R48253
  · exact R48255
  · exact R48257
  · exact R48259
  · exact R48261
  · exact R48263
  · exact R48265
  · exact R48267
  · exact R48269
  · exact R48271
  · exact R48273
  · exact R48275
  · exact R48277
  · exact R48279
  · exact R48281
  · exact R48283
  · exact R48285
  · exact R48287
  · exact R48289
  · exact R48291
  · exact R48293
  · exact R48295
  · exact R48297
  · exact R48299
  · exact R48301
  · exact R48303
  · exact R48305
  · exact R48307
  · exact R48309
  · exact R48311
  · exact R48313
  · exact R48315
  · exact R48317
  · exact R48319
  · exact R48321
  · exact R48323
  · exact R48325
  · exact R48327
  · exact R48329
  · exact R48331
  · exact R48333
  · exact R48335
  · exact R48337
  · exact R48339
  · exact R48341
  · exact R48343
  · exact R48345
  · exact R48347
  · exact R48349
  · exact R48351
  · exact R48353
  · exact R48355
  · exact R48357
  · exact R48359
  · exact R48361
  · exact R48363
  · exact R48365
  · exact R48367
  · exact R48369
  · exact R48371
  · exact R48373
  · exact R48375
  · exact R48377
  · exact R48379
  · exact R48381
  · exact R48383
  · exact R48385
  · exact R48387
  · exact R48389
  · exact R48391
  · exact R48393
  · exact R48395
  · exact R48397
  · exact R48399
  · exact R48401
  · exact R48403
  · exact R48405
  · exact R48407
  · exact R48409
  · exact R48411
  · exact R48413
  · exact R48415
  · exact R48417
  · exact R48419
  · exact R48421
  · exact R48423
  · exact R48425
  · exact R48427
  · exact R48429
  · exact R48431
  · exact R48433
  · exact R48435
  · exact R48437
  · exact R48439
  · exact R48441
  · exact R48443
  · exact R48445
  · exact R48447
  · exact R48449
  · exact R48451
  · exact R48453
  · exact R48455
  · exact R48457
  · exact R48459
  · exact R48461
  · exact R48463
  · exact R48465
  · exact R48467
  · exact R48469
  · exact R48471
  · exact R48473
  · exact R48475
  · exact R48477
  · exact R48479
  · exact R48481
  · exact R48483
  · exact R48485
  · exact R48487
  · exact R48489
  · exact R48491
  · exact R48493
  · exact R48495
  · exact R48497
  · exact R48499
  · exact R48501
  · exact R48503
  · exact R48505
  · exact R48507
  · exact R48509
  · exact R48511
  · exact R48513
  · exact R48515
  · exact R48517

theorem C1 (j : ℕ) (h1 : 24259 ≤ j) (h2 : j ≤ 24958) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R48519
  · exact R48521
  · exact R48523
  · exact R48525
  · exact R48527
  · exact R48529
  · exact R48531
  · exact R48533
  · exact R48535
  · exact R48537
  · exact R48539
  · exact R48541
  · exact R48543
  · exact R48545
  · exact R48547
  · exact R48549
  · exact R48551
  · exact R48553
  · exact R48555
  · exact R48557
  · exact R48559
  · exact R48561
  · exact R48563
  · exact R48565
  · exact R48567
  · exact R48569
  · exact R48571
  · exact R48573
  · exact R48575
  · exact R48577
  · exact R48579
  · exact R48581
  · exact R48583
  · exact R48585
  · exact R48587
  · exact R48589
  · exact R48591
  · exact R48593
  · exact R48595
  · exact R48597
  · exact R48599
  · exact R48601
  · exact R48603
  · exact R48605
  · exact R48607
  · exact R48609
  · exact R48611
  · exact R48613
  · exact R48615
  · exact R48617
  · exact R48619
  · exact R48621
  · exact R48623
  · exact R48625
  · exact R48627
  · exact R48629
  · exact R48631
  · exact R48633
  · exact R48635
  · exact R48637
  · exact R48639
  · exact R48641
  · exact R48643
  · exact R48645
  · exact R48647
  · exact R48649
  · exact R48651
  · exact R48653
  · exact R48655
  · exact R48657
  · exact R48659
  · exact R48661
  · exact R48663
  · exact R48665
  · exact R48667
  · exact R48669
  · exact R48671
  · exact R48673
  · exact R48675
  · exact R48677
  · exact R48679
  · exact R48681
  · exact R48683
  · exact R48685
  · exact R48687
  · exact R48689
  · exact R48691
  · exact R48693
  · exact R48695
  · exact R48697
  · exact R48699
  · exact R48701
  · exact R48703
  · exact R48705
  · exact R48707
  · exact R48709
  · exact R48711
  · exact R48713
  · exact R48715
  · exact R48717
  · exact R48719
  · exact R48721
  · exact R48723
  · exact R48725
  · exact R48727
  · exact R48729
  · exact R48731
  · exact R48733
  · exact R48735
  · exact R48737
  · exact R48739
  · exact R48741
  · exact R48743
  · exact R48745
  · exact R48747
  · exact R48749
  · exact R48751
  · exact R48753
  · exact R48755
  · exact R48757
  · exact R48759
  · exact R48761
  · exact R48763
  · exact R48765
  · exact R48767
  · exact R48769
  · exact R48771
  · exact R48773
  · exact R48775
  · exact R48777
  · exact R48779
  · exact R48781
  · exact R48783
  · exact R48785
  · exact R48787
  · exact R48789
  · exact R48791
  · exact R48793
  · exact R48795
  · exact R48797
  · exact R48799
  · exact R48801
  · exact R48803
  · exact R48805
  · exact R48807
  · exact R48809
  · exact R48811
  · exact R48813
  · exact R48815
  · exact R48817
  · exact R48819
  · exact R48821
  · exact R48823
  · exact R48825
  · exact R48827
  · exact R48829
  · exact R48831
  · exact R48833
  · exact R48835
  · exact R48837
  · exact R48839
  · exact R48841
  · exact R48843
  · exact R48845
  · exact R48847
  · exact R48849
  · exact R48851
  · exact R48853
  · exact R48855
  · exact R48857
  · exact R48859
  · exact R48861
  · exact R48863
  · exact R48865
  · exact R48867
  · exact R48869
  · exact R48871
  · exact R48873
  · exact R48875
  · exact R48877
  · exact R48879
  · exact R48881
  · exact R48883
  · exact R48885
  · exact R48887
  · exact R48889
  · exact R48891
  · exact R48893
  · exact R48895
  · exact R48897
  · exact R48899
  · exact R48901
  · exact R48903
  · exact R48905
  · exact R48907
  · exact R48909
  · exact R48911
  · exact R48913
  · exact R48915
  · exact R48917
  · exact R48919
  · exact R48921
  · exact R48923
  · exact R48925
  · exact R48927
  · exact R48929
  · exact R48931
  · exact R48933
  · exact R48935
  · exact R48937
  · exact R48939
  · exact R48941
  · exact R48943
  · exact R48945
  · exact R48947
  · exact R48949
  · exact R48951
  · exact R48953
  · exact R48955
  · exact R48957
  · exact R48959
  · exact R48961
  · exact R48963
  · exact R48965
  · exact R48967
  · exact R48969
  · exact R48971
  · exact R48973
  · exact R48975
  · exact R48977
  · exact R48979
  · exact R48981
  · exact R48983
  · exact R48985
  · exact R48987
  · exact R48989
  · exact R48991
  · exact R48993
  · exact R48995
  · exact R48997
  · exact R48999
  · exact R49001
  · exact R49003
  · exact R49005
  · exact R49007
  · exact R49009
  · exact R49011
  · exact R49013
  · exact R49015
  · exact R49017
  · exact R49019
  · exact R49021
  · exact R49023
  · exact R49025
  · exact R49027
  · exact R49029
  · exact R49031
  · exact R49033
  · exact R49035
  · exact R49037
  · exact R49039
  · exact R49041
  · exact R49043
  · exact R49045
  · exact R49047
  · exact R49049
  · exact R49051
  · exact R49053
  · exact R49055
  · exact R49057
  · exact R49059
  · exact R49061
  · exact R49063
  · exact R49065
  · exact R49067
  · exact R49069
  · exact R49071
  · exact R49073
  · exact R49075
  · exact R49077
  · exact R49079
  · exact R49081
  · exact R49083
  · exact R49085
  · exact R49087
  · exact R49089
  · exact R49091
  · exact R49093
  · exact R49095
  · exact R49097
  · exact R49099
  · exact R49101
  · exact R49103
  · exact R49105
  · exact R49107
  · exact R49109
  · exact R49111
  · exact R49113
  · exact R49115
  · exact R49117
  · exact R49119
  · exact R49121
  · exact R49123
  · exact R49125
  · exact R49127
  · exact R49129
  · exact R49131
  · exact R49133
  · exact R49135
  · exact R49137
  · exact R49139
  · exact R49141
  · exact R49143
  · exact R49145
  · exact R49147
  · exact R49149
  · exact R49151
  · exact R49153
  · exact R49155
  · exact R49157
  · exact R49159
  · exact R49161
  · exact R49163
  · exact R49165
  · exact R49167
  · exact R49169
  · exact R49171
  · exact R49173
  · exact R49175
  · exact R49177
  · exact R49179
  · exact R49181
  · exact R49183
  · exact R49185
  · exact R49187
  · exact R49189
  · exact R49191
  · exact R49193
  · exact R49195
  · exact R49197
  · exact R49199
  · exact R49201
  · exact R49203
  · exact R49205
  · exact R49207
  · exact R49209
  · exact R49211
  · exact R49213
  · exact R49215
  · exact R49217
  · exact R49219
  · exact R49221
  · exact R49223
  · exact R49225
  · exact R49227
  · exact R49229
  · exact R49231
  · exact R49233
  · exact R49235
  · exact R49237
  · exact R49239
  · exact R49241
  · exact R49243
  · exact R49245
  · exact R49247
  · exact R49249
  · exact R49251
  · exact R49253
  · exact R49255
  · exact R49257
  · exact R49259
  · exact R49261
  · exact R49263
  · exact R49265
  · exact R49267
  · exact R49269
  · exact R49271
  · exact R49273
  · exact R49275
  · exact R49277
  · exact R49279
  · exact R49281
  · exact R49283
  · exact R49285
  · exact R49287
  · exact R49289
  · exact R49291
  · exact R49293
  · exact R49295
  · exact R49297
  · exact R49299
  · exact R49301
  · exact R49303
  · exact R49305
  · exact R49307
  · exact R49309
  · exact R49311
  · exact R49313
  · exact R49315
  · exact R49317
  · exact R49319
  · exact R49321
  · exact R49323
  · exact R49325
  · exact R49327
  · exact R49329
  · exact R49331
  · exact R49333
  · exact R49335
  · exact R49337
  · exact R49339
  · exact R49341
  · exact R49343
  · exact R49345
  · exact R49347
  · exact R49349
  · exact R49351
  · exact R49353
  · exact R49355
  · exact R49357
  · exact R49359
  · exact R49361
  · exact R49363
  · exact R49365
  · exact R49367
  · exact R49369
  · exact R49371
  · exact R49373
  · exact R49375
  · exact R49377
  · exact R49379
  · exact R49381
  · exact R49383
  · exact R49385
  · exact R49387
  · exact R49389
  · exact R49391
  · exact R49393
  · exact R49395
  · exact R49397
  · exact R49399
  · exact R49401
  · exact R49403
  · exact R49405
  · exact R49407
  · exact R49409
  · exact R49411
  · exact R49413
  · exact R49415
  · exact R49417
  · exact R49419
  · exact R49421
  · exact R49423
  · exact R49425
  · exact R49427
  · exact R49429
  · exact R49431
  · exact R49433
  · exact R49435
  · exact R49437
  · exact R49439
  · exact R49441
  · exact R49443
  · exact R49445
  · exact R49447
  · exact R49449
  · exact R49451
  · exact R49453
  · exact R49455
  · exact R49457
  · exact R49459
  · exact R49461
  · exact R49463
  · exact R49465
  · exact R49467
  · exact R49469
  · exact R49471
  · exact R49473
  · exact R49475
  · exact R49477
  · exact R49479
  · exact R49481
  · exact R49483
  · exact R49485
  · exact R49487
  · exact R49489
  · exact R49491
  · exact R49493
  · exact R49495
  · exact R49497
  · exact R49499
  · exact R49501
  · exact R49503
  · exact R49505
  · exact R49507
  · exact R49509
  · exact R49511
  · exact R49513
  · exact R49515
  · exact R49517
  · exact R49519
  · exact R49521
  · exact R49523
  · exact R49525
  · exact R49527
  · exact R49529
  · exact R49531
  · exact R49533
  · exact R49535
  · exact R49537
  · exact R49539
  · exact R49541
  · exact R49543
  · exact R49545
  · exact R49547
  · exact R49549
  · exact R49551
  · exact R49553
  · exact R49555
  · exact R49557
  · exact R49559
  · exact R49561
  · exact R49563
  · exact R49565
  · exact R49567
  · exact R49569
  · exact R49571
  · exact R49573
  · exact R49575
  · exact R49577
  · exact R49579
  · exact R49581
  · exact R49583
  · exact R49585
  · exact R49587
  · exact R49589
  · exact R49591
  · exact R49593
  · exact R49595
  · exact R49597
  · exact R49599
  · exact R49601
  · exact R49603
  · exact R49605
  · exact R49607
  · exact R49609
  · exact R49611
  · exact R49613
  · exact R49615
  · exact R49617
  · exact R49619
  · exact R49621
  · exact R49623
  · exact R49625
  · exact R49627
  · exact R49629
  · exact R49631
  · exact R49633
  · exact R49635
  · exact R49637
  · exact R49639
  · exact R49641
  · exact R49643
  · exact R49645
  · exact R49647
  · exact R49649
  · exact R49651
  · exact R49653
  · exact R49655
  · exact R49657
  · exact R49659
  · exact R49661
  · exact R49663
  · exact R49665
  · exact R49667
  · exact R49669
  · exact R49671
  · exact R49673
  · exact R49675
  · exact R49677
  · exact R49679
  · exact R49681
  · exact R49683
  · exact R49685
  · exact R49687
  · exact R49689
  · exact R49691
  · exact R49693
  · exact R49695
  · exact R49697
  · exact R49699
  · exact R49701
  · exact R49703
  · exact R49705
  · exact R49707
  · exact R49709
  · exact R49711
  · exact R49713
  · exact R49715
  · exact R49717
  · exact R49719
  · exact R49721
  · exact R49723
  · exact R49725
  · exact R49727
  · exact R49729
  · exact R49731
  · exact R49733
  · exact R49735
  · exact R49737
  · exact R49739
  · exact R49741
  · exact R49743
  · exact R49745
  · exact R49747
  · exact R49749
  · exact R49751
  · exact R49753
  · exact R49755
  · exact R49757
  · exact R49759
  · exact R49761
  · exact R49763
  · exact R49765
  · exact R49767
  · exact R49769
  · exact R49771
  · exact R49773
  · exact R49775
  · exact R49777
  · exact R49779
  · exact R49781
  · exact R49783
  · exact R49785
  · exact R49787
  · exact R49789
  · exact R49791
  · exact R49793
  · exact R49795
  · exact R49797
  · exact R49799
  · exact R49801
  · exact R49803
  · exact R49805
  · exact R49807
  · exact R49809
  · exact R49811
  · exact R49813
  · exact R49815
  · exact R49817
  · exact R49819
  · exact R49821
  · exact R49823
  · exact R49825
  · exact R49827
  · exact R49829
  · exact R49831
  · exact R49833
  · exact R49835
  · exact R49837
  · exact R49839
  · exact R49841
  · exact R49843
  · exact R49845
  · exact R49847
  · exact R49849
  · exact R49851
  · exact R49853
  · exact R49855
  · exact R49857
  · exact R49859
  · exact R49861
  · exact R49863
  · exact R49865
  · exact R49867
  · exact R49869
  · exact R49871
  · exact R49873
  · exact R49875
  · exact R49877
  · exact R49879
  · exact R49881
  · exact R49883
  · exact R49885
  · exact R49887
  · exact R49889
  · exact R49891
  · exact R49893
  · exact R49895
  · exact R49897
  · exact R49899
  · exact R49901
  · exact R49903
  · exact R49905
  · exact R49907
  · exact R49909
  · exact R49911
  · exact R49913
  · exact R49915
  · exact R49917

theorem C2 (j : ℕ) (h1 : 24959 ≤ j) (h2 : j ≤ 25559) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R49919
  · exact R49921
  · exact R49923
  · exact R49925
  · exact R49927
  · exact R49929
  · exact R49931
  · exact R49933
  · exact R49935
  · exact R49937
  · exact R49939
  · exact R49941
  · exact R49943
  · exact R49945
  · exact R49947
  · exact R49949
  · exact R49951
  · exact R49953
  · exact R49955
  · exact R49957
  · exact R49959
  · exact R49961
  · exact R49963
  · exact R49965
  · exact R49967
  · exact R49969
  · exact R49971
  · exact R49973
  · exact R49975
  · exact R49977
  · exact R49979
  · exact R49981
  · exact R49983
  · exact R49985
  · exact R49987
  · exact R49989
  · exact R49991
  · exact R49993
  · exact R49995
  · exact R49997
  · exact R49999
  · exact R50001
  · exact R50003
  · exact R50005
  · exact R50007
  · exact R50009
  · exact R50011
  · exact R50013
  · exact R50015
  · exact R50017
  · exact R50019
  · exact R50021
  · exact R50023
  · exact R50025
  · exact R50027
  · exact R50029
  · exact R50031
  · exact R50033
  · exact R50035
  · exact R50037
  · exact R50039
  · exact R50041
  · exact R50043
  · exact R50045
  · exact R50047
  · exact R50049
  · exact R50051
  · exact R50053
  · exact R50055
  · exact R50057
  · exact R50059
  · exact R50061
  · exact R50063
  · exact R50065
  · exact R50067
  · exact R50069
  · exact R50071
  · exact R50073
  · exact R50075
  · exact R50077
  · exact R50079
  · exact R50081
  · exact R50083
  · exact R50085
  · exact R50087
  · exact R50089
  · exact R50091
  · exact R50093
  · exact R50095
  · exact R50097
  · exact R50099
  · exact R50101
  · exact R50103
  · exact R50105
  · exact R50107
  · exact R50109
  · exact R50111
  · exact R50113
  · exact R50115
  · exact R50117
  · exact R50119
  · exact R50121
  · exact R50123
  · exact R50125
  · exact R50127
  · exact R50129
  · exact R50131
  · exact R50133
  · exact R50135
  · exact R50137
  · exact R50139
  · exact R50141
  · exact R50143
  · exact R50145
  · exact R50147
  · exact R50149
  · exact R50151
  · exact R50153
  · exact R50155
  · exact R50157
  · exact R50159
  · exact R50161
  · exact R50163
  · exact R50165
  · exact R50167
  · exact R50169
  · exact R50171
  · exact R50173
  · exact R50175
  · exact R50177
  · exact R50179
  · exact R50181
  · exact R50183
  · exact R50185
  · exact R50187
  · exact R50189
  · exact R50191
  · exact R50193
  · exact R50195
  · exact R50197
  · exact R50199
  · exact R50201
  · exact R50203
  · exact R50205
  · exact R50207
  · exact R50209
  · exact R50211
  · exact R50213
  · exact R50215
  · exact R50217
  · exact R50219
  · exact R50221
  · exact R50223
  · exact R50225
  · exact R50227
  · exact R50229
  · exact R50231
  · exact R50233
  · exact R50235
  · exact R50237
  · exact R50239
  · exact R50241
  · exact R50243
  · exact R50245
  · exact R50247
  · exact R50249
  · exact R50251
  · exact R50253
  · exact R50255
  · exact R50257
  · exact R50259
  · exact R50261
  · exact R50263
  · exact R50265
  · exact R50267
  · exact R50269
  · exact R50271
  · exact R50273
  · exact R50275
  · exact R50277
  · exact R50279
  · exact R50281
  · exact R50283
  · exact R50285
  · exact R50287
  · exact R50289
  · exact R50291
  · exact R50293
  · exact R50295
  · exact R50297
  · exact R50299
  · exact R50301
  · exact R50303
  · exact R50305
  · exact R50307
  · exact R50309
  · exact R50311
  · exact R50313
  · exact R50315
  · exact R50317
  · exact R50319
  · exact R50321
  · exact R50323
  · exact R50325
  · exact R50327
  · exact R50329
  · exact R50331
  · exact R50333
  · exact R50335
  · exact R50337
  · exact R50339
  · exact R50341
  · exact R50343
  · exact R50345
  · exact R50347
  · exact R50349
  · exact R50351
  · exact R50353
  · exact R50355
  · exact R50357
  · exact R50359
  · exact R50361
  · exact R50363
  · exact R50365
  · exact R50367
  · exact R50369
  · exact R50371
  · exact R50373
  · exact R50375
  · exact R50377
  · exact R50379
  · exact R50381
  · exact R50383
  · exact R50385
  · exact R50387
  · exact R50389
  · exact R50391
  · exact R50393
  · exact R50395
  · exact R50397
  · exact R50399
  · exact R50401
  · exact R50403
  · exact R50405
  · exact R50407
  · exact R50409
  · exact R50411
  · exact R50413
  · exact R50415
  · exact R50417
  · exact R50419
  · exact R50421
  · exact R50423
  · exact R50425
  · exact R50427
  · exact R50429
  · exact R50431
  · exact R50433
  · exact R50435
  · exact R50437
  · exact R50439
  · exact R50441
  · exact R50443
  · exact R50445
  · exact R50447
  · exact R50449
  · exact R50451
  · exact R50453
  · exact R50455
  · exact R50457
  · exact R50459
  · exact R50461
  · exact R50463
  · exact R50465
  · exact R50467
  · exact R50469
  · exact R50471
  · exact R50473
  · exact R50475
  · exact R50477
  · exact R50479
  · exact R50481
  · exact R50483
  · exact R50485
  · exact R50487
  · exact R50489
  · exact R50491
  · exact R50493
  · exact R50495
  · exact R50497
  · exact R50499
  · exact R50501
  · exact R50503
  · exact R50505
  · exact R50507
  · exact R50509
  · exact R50511
  · exact R50513
  · exact R50515
  · exact R50517
  · exact R50519
  · exact R50521
  · exact R50523
  · exact R50525
  · exact R50527
  · exact R50529
  · exact R50531
  · exact R50533
  · exact R50535
  · exact R50537
  · exact R50539
  · exact R50541
  · exact R50543
  · exact R50545
  · exact R50547
  · exact R50549
  · exact R50551
  · exact R50553
  · exact R50555
  · exact R50557
  · exact R50559
  · exact R50561
  · exact R50563
  · exact R50565
  · exact R50567
  · exact R50569
  · exact R50571
  · exact R50573
  · exact R50575
  · exact R50577
  · exact R50579
  · exact R50581
  · exact R50583
  · exact R50585
  · exact R50587
  · exact R50589
  · exact R50591
  · exact R50593
  · exact R50595
  · exact R50597
  · exact R50599
  · exact R50601
  · exact R50603
  · exact R50605
  · exact R50607
  · exact R50609
  · exact R50611
  · exact R50613
  · exact R50615
  · exact R50617
  · exact R50619
  · exact R50621
  · exact R50623
  · exact R50625
  · exact R50627
  · exact R50629
  · exact R50631
  · exact R50633
  · exact R50635
  · exact R50637
  · exact R50639
  · exact R50641
  · exact R50643
  · exact R50645
  · exact R50647
  · exact R50649
  · exact R50651
  · exact R50653
  · exact R50655
  · exact R50657
  · exact R50659
  · exact R50661
  · exact R50663
  · exact R50665
  · exact R50667
  · exact R50669
  · exact R50671
  · exact R50673
  · exact R50675
  · exact R50677
  · exact R50679
  · exact R50681
  · exact R50683
  · exact R50685
  · exact R50687
  · exact R50689
  · exact R50691
  · exact R50693
  · exact R50695
  · exact R50697
  · exact R50699
  · exact R50701
  · exact R50703
  · exact R50705
  · exact R50707
  · exact R50709
  · exact R50711
  · exact R50713
  · exact R50715
  · exact R50717
  · exact R50719
  · exact R50721
  · exact R50723
  · exact R50725
  · exact R50727
  · exact R50729
  · exact R50731
  · exact R50733
  · exact R50735
  · exact R50737
  · exact R50739
  · exact R50741
  · exact R50743
  · exact R50745
  · exact R50747
  · exact R50749
  · exact R50751
  · exact R50753
  · exact R50755
  · exact R50757
  · exact R50759
  · exact R50761
  · exact R50763
  · exact R50765
  · exact R50767
  · exact R50769
  · exact R50771
  · exact R50773
  · exact R50775
  · exact R50777
  · exact R50779
  · exact R50781
  · exact R50783
  · exact R50785
  · exact R50787
  · exact R50789
  · exact R50791
  · exact R50793
  · exact R50795
  · exact R50797
  · exact R50799
  · exact R50801
  · exact R50803
  · exact R50805
  · exact R50807
  · exact R50809
  · exact R50811
  · exact R50813
  · exact R50815
  · exact R50817
  · exact R50819
  · exact R50821
  · exact R50823
  · exact R50825
  · exact R50827
  · exact R50829
  · exact R50831
  · exact R50833
  · exact R50835
  · exact R50837
  · exact R50839
  · exact R50841
  · exact R50843
  · exact R50845
  · exact R50847
  · exact R50849
  · exact R50851
  · exact R50853
  · exact R50855
  · exact R50857
  · exact R50859
  · exact R50861
  · exact R50863
  · exact R50865
  · exact R50867
  · exact R50869
  · exact R50871
  · exact R50873
  · exact R50875
  · exact R50877
  · exact R50879
  · exact R50881
  · exact R50883
  · exact R50885
  · exact R50887
  · exact R50889
  · exact R50891
  · exact R50893
  · exact R50895
  · exact R50897
  · exact R50899
  · exact R50901
  · exact R50903
  · exact R50905
  · exact R50907
  · exact R50909
  · exact R50911
  · exact R50913
  · exact R50915
  · exact R50917
  · exact R50919
  · exact R50921
  · exact R50923
  · exact R50925
  · exact R50927
  · exact R50929
  · exact R50931
  · exact R50933
  · exact R50935
  · exact R50937
  · exact R50939
  · exact R50941
  · exact R50943
  · exact R50945
  · exact R50947
  · exact R50949
  · exact R50951
  · exact R50953
  · exact R50955
  · exact R50957
  · exact R50959
  · exact R50961
  · exact R50963
  · exact R50965
  · exact R50967
  · exact R50969
  · exact R50971
  · exact R50973
  · exact R50975
  · exact R50977
  · exact R50979
  · exact R50981
  · exact R50983
  · exact R50985
  · exact R50987
  · exact R50989
  · exact R50991
  · exact R50993
  · exact R50995
  · exact R50997
  · exact R50999
  · exact R51001
  · exact R51003
  · exact R51005
  · exact R51007
  · exact R51009
  · exact R51011
  · exact R51013
  · exact R51015
  · exact R51017
  · exact R51019
  · exact R51021
  · exact R51023
  · exact R51025
  · exact R51027
  · exact R51029
  · exact R51031
  · exact R51033
  · exact R51035
  · exact R51037
  · exact R51039
  · exact R51041
  · exact R51043
  · exact R51045
  · exact R51047
  · exact R51049
  · exact R51051
  · exact R51053
  · exact R51055
  · exact R51057
  · exact R51059
  · exact R51061
  · exact R51063
  · exact R51065
  · exact R51067
  · exact R51069
  · exact R51071
  · exact R51073
  · exact R51075
  · exact R51077
  · exact R51079
  · exact R51081
  · exact R51083
  · exact R51085
  · exact R51087
  · exact R51089
  · exact R51091
  · exact R51093
  · exact R51095
  · exact R51097
  · exact R51099
  · exact R51101
  · exact R51103
  · exact R51105
  · exact R51107
  · exact R51109
  · exact R51111
  · exact R51113
  · exact R51115
  · exact R51117
  · exact R51119

theorem solution (m : ℕ) (hm : 0 < m) (hodd : Odd m) (hle : m ≤ 51119) :
    ∃ k : ℕ, syracuseStep^[k] m = 1 := by
  rcases Nat.lt_or_ge m 47119 with hlo | hlo
  · exact syracuse_reaches_one_below_47119 m hm hodd (by omega)
  obtain ⟨j, rfl⟩ : ∃ j, m = 2 * j + 1 := by obtain ⟨t, ht⟩ := hodd; exact ⟨t, by omega⟩
  rcases Nat.lt_or_ge j 24259 with h0 | h0
  · exact C0 j (by omega) (by omega)
  rcases Nat.lt_or_ge j 24959 with h1 | h1
  · exact C1 j (by omega) (by omega)
  exact C2 j (by omega) (by omega)
