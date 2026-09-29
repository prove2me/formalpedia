-- Prove2me | solution 1 for syracuse_reaches_one_below_67124
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T06:12:15.375855+00:00
-- url     : https://prove2.me/submissions/2875124d-98a3-4c06-907f-d521ba13d934

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_reaches_one_below_63123

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
theorem B (n : ℕ) (h1 : 0 < n) (h2 : Odd n) (h3 : n ≤ 63122) : Reach n :=
  syracuse_reaches_one_below_63123 n h1 h2 h3
theorem R65537 : Reach 65537 := rs (se 2 (by rfl) ⟨24576, by rfl⟩) (B 49153 (by norm_num) ⟨24576, by rfl⟩ (by norm_num))
theorem R98309 : Reach 98309 := rs (se 4 (by rfl) ⟨9216, by rfl⟩) (B 18433 (by norm_num) ⟨9216, by rfl⟩ (by norm_num))
theorem R65541 : Reach 65541 := rs (se 4 (by rfl) ⟨6144, by rfl⟩) (B 12289 (by norm_num) ⟨6144, by rfl⟩ (by norm_num))
theorem R65545 : Reach 65545 := rs (se 2 (by rfl) ⟨24579, by rfl⟩) (B 49159 (by norm_num) ⟨24579, by rfl⟩ (by norm_num))
theorem R163853 : Reach 163853 := rs (se 3 (by rfl) ⟨30722, by rfl⟩) (B 61445 (by norm_num) ⟨30722, by rfl⟩ (by norm_num))
theorem R65549 : Reach 65549 := rs (se 3 (by rfl) ⟨12290, by rfl⟩) (B 24581 (by norm_num) ⟨12290, by rfl⟩ (by norm_num))
theorem R65553 : Reach 65553 := rs (se 2 (by rfl) ⟨24582, by rfl⟩) (B 49165 (by norm_num) ⟨24582, by rfl⟩ (by norm_num))
theorem R65557 : Reach 65557 := rs (se 6 (by rfl) ⟨1536, by rfl⟩) (B 3073 (by norm_num) ⟨1536, by rfl⟩ (by norm_num))
theorem R65561 : Reach 65561 := rs (se 2 (by rfl) ⟨24585, by rfl⟩) (B 49171 (by norm_num) ⟨24585, by rfl⟩ (by norm_num))
theorem R98333 : Reach 98333 := rs (se 3 (by rfl) ⟨18437, by rfl⟩) (B 36875 (by norm_num) ⟨18437, by rfl⟩ (by norm_num))
theorem R65565 : Reach 65565 := rs (se 3 (by rfl) ⟨12293, by rfl⟩) (B 24587 (by norm_num) ⟨12293, by rfl⟩ (by norm_num))
theorem R65569 : Reach 65569 := rs (se 2 (by rfl) ⟨24588, by rfl⟩) (B 49177 (by norm_num) ⟨24588, by rfl⟩ (by norm_num))
theorem R65573 : Reach 65573 := rs (se 4 (by rfl) ⟨6147, by rfl⟩) (B 12295 (by norm_num) ⟨6147, by rfl⟩ (by norm_num))
theorem R65577 : Reach 65577 := rs (se 2 (by rfl) ⟨24591, by rfl⟩) (B 49183 (by norm_num) ⟨24591, by rfl⟩ (by norm_num))
theorem R163885 : Reach 163885 := rs (se 3 (by rfl) ⟨30728, by rfl⟩) (B 61457 (by norm_num) ⟨30728, by rfl⟩ (by norm_num))
theorem R65581 : Reach 65581 := rs (se 3 (by rfl) ⟨12296, by rfl⟩) (B 24593 (by norm_num) ⟨12296, by rfl⟩ (by norm_num))
theorem R65585 : Reach 65585 := rs (se 2 (by rfl) ⟨24594, by rfl⟩) (B 49189 (by norm_num) ⟨24594, by rfl⟩ (by norm_num))
theorem R98357 : Reach 98357 := rs (se 5 (by rfl) ⟨4610, by rfl⟩) (B 9221 (by norm_num) ⟨4610, by rfl⟩ (by norm_num))
theorem R65589 : Reach 65589 := rs (se 5 (by rfl) ⟨3074, by rfl⟩) (B 6149 (by norm_num) ⟨3074, by rfl⟩ (by norm_num))
theorem R65593 : Reach 65593 := rs (se 2 (by rfl) ⟨24597, by rfl⟩) (B 49195 (by norm_num) ⟨24597, by rfl⟩ (by norm_num))
theorem R65597 : Reach 65597 := rs (se 3 (by rfl) ⟨12299, by rfl⟩) (B 24599 (by norm_num) ⟨12299, by rfl⟩ (by norm_num))
theorem R65601 : Reach 65601 := rs (se 2 (by rfl) ⟨24600, by rfl⟩) (B 49201 (by norm_num) ⟨24600, by rfl⟩ (by norm_num))
theorem R65605 : Reach 65605 := rs (se 4 (by rfl) ⟨6150, by rfl⟩) (B 12301 (by norm_num) ⟨6150, by rfl⟩ (by norm_num))
theorem R65609 : Reach 65609 := rs (se 2 (by rfl) ⟨24603, by rfl⟩) (B 49207 (by norm_num) ⟨24603, by rfl⟩ (by norm_num))
theorem R98381 : Reach 98381 := rs (se 3 (by rfl) ⟨18446, by rfl⟩) (B 36893 (by norm_num) ⟨18446, by rfl⟩ (by norm_num))
theorem R65613 : Reach 65613 := rs (se 3 (by rfl) ⟨12302, by rfl⟩) (B 24605 (by norm_num) ⟨12302, by rfl⟩ (by norm_num))
theorem R65617 : Reach 65617 := rs (se 2 (by rfl) ⟨24606, by rfl⟩) (B 49213 (by norm_num) ⟨24606, by rfl⟩ (by norm_num))
theorem R65621 : Reach 65621 := rs (se 8 (by rfl) ⟨384, by rfl⟩) (B 769 (by norm_num) ⟨384, by rfl⟩ (by norm_num))
theorem R65625 : Reach 65625 := rs (se 2 (by rfl) ⟨24609, by rfl⟩) (B 49219 (by norm_num) ⟨24609, by rfl⟩ (by norm_num))
theorem R65629 : Reach 65629 := rs (se 3 (by rfl) ⟨12305, by rfl⟩) (B 24611 (by norm_num) ⟨12305, by rfl⟩ (by norm_num))
theorem R65633 : Reach 65633 := rs (se 2 (by rfl) ⟨24612, by rfl⟩) (B 49225 (by norm_num) ⟨24612, by rfl⟩ (by norm_num))
theorem R98405 : Reach 98405 := rs (se 4 (by rfl) ⟨9225, by rfl⟩) (B 18451 (by norm_num) ⟨9225, by rfl⟩ (by norm_num))
theorem R65637 : Reach 65637 := rs (se 4 (by rfl) ⟨6153, by rfl⟩) (B 12307 (by norm_num) ⟨6153, by rfl⟩ (by norm_num))
theorem R65641 : Reach 65641 := rs (se 2 (by rfl) ⟨24615, by rfl⟩) (B 49231 (by norm_num) ⟨24615, by rfl⟩ (by norm_num))
theorem R65645 : Reach 65645 := rs (se 3 (by rfl) ⟨12308, by rfl⟩) (B 24617 (by norm_num) ⟨12308, by rfl⟩ (by norm_num))
theorem R65649 : Reach 65649 := rs (se 2 (by rfl) ⟨24618, by rfl⟩) (B 49237 (by norm_num) ⟨24618, by rfl⟩ (by norm_num))
theorem R65653 : Reach 65653 := rs (se 5 (by rfl) ⟨3077, by rfl⟩) (B 6155 (by norm_num) ⟨3077, by rfl⟩ (by norm_num))
theorem R65657 : Reach 65657 := rs (se 2 (by rfl) ⟨24621, by rfl⟩) (B 49243 (by norm_num) ⟨24621, by rfl⟩ (by norm_num))
theorem R98429 : Reach 98429 := rs (se 3 (by rfl) ⟨18455, by rfl⟩) (B 36911 (by norm_num) ⟨18455, by rfl⟩ (by norm_num))
theorem R65661 : Reach 65661 := rs (se 3 (by rfl) ⟨12311, by rfl⟩) (B 24623 (by norm_num) ⟨12311, by rfl⟩ (by norm_num))
theorem R65665 : Reach 65665 := rs (se 2 (by rfl) ⟨24624, by rfl⟩) (B 49249 (by norm_num) ⟨24624, by rfl⟩ (by norm_num))
theorem R65669 : Reach 65669 := rs (se 4 (by rfl) ⟨6156, by rfl⟩) (B 12313 (by norm_num) ⟨6156, by rfl⟩ (by norm_num))
theorem R65673 : Reach 65673 := rs (se 2 (by rfl) ⟨24627, by rfl⟩) (B 49255 (by norm_num) ⟨24627, by rfl⟩ (by norm_num))
theorem R65677 : Reach 65677 := rs (se 3 (by rfl) ⟨12314, by rfl⟩) (B 24629 (by norm_num) ⟨12314, by rfl⟩ (by norm_num))
theorem R65681 : Reach 65681 := rs (se 2 (by rfl) ⟨24630, by rfl⟩) (B 49261 (by norm_num) ⟨24630, by rfl⟩ (by norm_num))
theorem R98453 : Reach 98453 := rs (se 6 (by rfl) ⟨2307, by rfl⟩) (B 4615 (by norm_num) ⟨2307, by rfl⟩ (by norm_num))
theorem R65685 : Reach 65685 := rs (se 6 (by rfl) ⟨1539, by rfl⟩) (B 3079 (by norm_num) ⟨1539, by rfl⟩ (by norm_num))
theorem R65689 : Reach 65689 := rs (se 2 (by rfl) ⟨24633, by rfl⟩) (B 49267 (by norm_num) ⟨24633, by rfl⟩ (by norm_num))
theorem R65693 : Reach 65693 := rs (se 3 (by rfl) ⟨12317, by rfl⟩) (B 24635 (by norm_num) ⟨12317, by rfl⟩ (by norm_num))
theorem R65697 : Reach 65697 := rs (se 2 (by rfl) ⟨24636, by rfl⟩) (B 49273 (by norm_num) ⟨24636, by rfl⟩ (by norm_num))
theorem R65701 : Reach 65701 := rs (se 4 (by rfl) ⟨6159, by rfl⟩) (B 12319 (by norm_num) ⟨6159, by rfl⟩ (by norm_num))
theorem R65705 : Reach 65705 := rs (se 2 (by rfl) ⟨24639, by rfl⟩) (B 49279 (by norm_num) ⟨24639, by rfl⟩ (by norm_num))
theorem R98477 : Reach 98477 := rs (se 3 (by rfl) ⟨18464, by rfl⟩) (B 36929 (by norm_num) ⟨18464, by rfl⟩ (by norm_num))
theorem R65709 : Reach 65709 := rs (se 3 (by rfl) ⟨12320, by rfl⟩) (B 24641 (by norm_num) ⟨12320, by rfl⟩ (by norm_num))
theorem R65713 : Reach 65713 := rs (se 2 (by rfl) ⟨24642, by rfl⟩) (B 49285 (by norm_num) ⟨24642, by rfl⟩ (by norm_num))
theorem R65717 : Reach 65717 := rs (se 5 (by rfl) ⟨3080, by rfl⟩) (B 6161 (by norm_num) ⟨3080, by rfl⟩ (by norm_num))
theorem R65721 : Reach 65721 := rs (se 2 (by rfl) ⟨24645, by rfl⟩) (B 49291 (by norm_num) ⟨24645, by rfl⟩ (by norm_num))
theorem R65725 : Reach 65725 := rs (se 3 (by rfl) ⟨12323, by rfl⟩) (B 24647 (by norm_num) ⟨12323, by rfl⟩ (by norm_num))
theorem R65729 : Reach 65729 := rs (se 2 (by rfl) ⟨24648, by rfl⟩) (B 49297 (by norm_num) ⟨24648, by rfl⟩ (by norm_num))
theorem R98501 : Reach 98501 := rs (se 4 (by rfl) ⟨9234, by rfl⟩) (B 18469 (by norm_num) ⟨9234, by rfl⟩ (by norm_num))
theorem R65733 : Reach 65733 := rs (se 4 (by rfl) ⟨6162, by rfl⟩) (B 12325 (by norm_num) ⟨6162, by rfl⟩ (by norm_num))
theorem R65737 : Reach 65737 := rs (se 2 (by rfl) ⟨24651, by rfl⟩) (B 49303 (by norm_num) ⟨24651, by rfl⟩ (by norm_num))
theorem R164045 : Reach 164045 := rs (se 3 (by rfl) ⟨30758, by rfl⟩) (B 61517 (by norm_num) ⟨30758, by rfl⟩ (by norm_num))
theorem R65741 : Reach 65741 := rs (se 3 (by rfl) ⟨12326, by rfl⟩) (B 24653 (by norm_num) ⟨12326, by rfl⟩ (by norm_num))
theorem R65749 : Reach 65749 := rs (se 7 (by rfl) ⟨770, by rfl⟩) (B 1541 (by norm_num) ⟨770, by rfl⟩ (by norm_num))
theorem R65745 : Reach 65745 := rs (se 2 (by rfl) ⟨24654, by rfl⟩) (B 49309 (by norm_num) ⟨24654, by rfl⟩ (by norm_num))
theorem R65753 : Reach 65753 := rs (se 2 (by rfl) ⟨24657, by rfl⟩) (B 49315 (by norm_num) ⟨24657, by rfl⟩ (by norm_num))
theorem R98525 : Reach 98525 := rs (se 3 (by rfl) ⟨18473, by rfl⟩) (B 36947 (by norm_num) ⟨18473, by rfl⟩ (by norm_num))
theorem R65757 : Reach 65757 := rs (se 3 (by rfl) ⟨12329, by rfl⟩) (B 24659 (by norm_num) ⟨12329, by rfl⟩ (by norm_num))
theorem R65761 : Reach 65761 := rs (se 2 (by rfl) ⟨24660, by rfl⟩) (B 49321 (by norm_num) ⟨24660, by rfl⟩ (by norm_num))
theorem R65765 : Reach 65765 := rs (se 4 (by rfl) ⟨6165, by rfl⟩) (B 12331 (by norm_num) ⟨6165, by rfl⟩ (by norm_num))
theorem R65769 : Reach 65769 := rs (se 2 (by rfl) ⟨24663, by rfl⟩) (B 49327 (by norm_num) ⟨24663, by rfl⟩ (by norm_num))
theorem R65773 : Reach 65773 := rs (se 3 (by rfl) ⟨12332, by rfl⟩) (B 24665 (by norm_num) ⟨12332, by rfl⟩ (by norm_num))
theorem R65777 : Reach 65777 := rs (se 2 (by rfl) ⟨24666, by rfl⟩) (B 49333 (by norm_num) ⟨24666, by rfl⟩ (by norm_num))
theorem R98549 : Reach 98549 := rs (se 5 (by rfl) ⟨4619, by rfl⟩) (B 9239 (by norm_num) ⟨4619, by rfl⟩ (by norm_num))
theorem R65781 : Reach 65781 := rs (se 5 (by rfl) ⟨3083, by rfl⟩) (B 6167 (by norm_num) ⟨3083, by rfl⟩ (by norm_num))
theorem R65785 : Reach 65785 := rs (se 2 (by rfl) ⟨24669, by rfl⟩) (B 49339 (by norm_num) ⟨24669, by rfl⟩ (by norm_num))
theorem R65789 : Reach 65789 := rs (se 3 (by rfl) ⟨12335, by rfl⟩) (B 24671 (by norm_num) ⟨12335, by rfl⟩ (by norm_num))
theorem R65793 : Reach 65793 := rs (se 2 (by rfl) ⟨24672, by rfl⟩) (B 49345 (by norm_num) ⟨24672, by rfl⟩ (by norm_num))
theorem R65797 : Reach 65797 := rs (se 4 (by rfl) ⟨6168, by rfl⟩) (B 12337 (by norm_num) ⟨6168, by rfl⟩ (by norm_num))
theorem R65801 : Reach 65801 := rs (se 2 (by rfl) ⟨24675, by rfl⟩) (B 49351 (by norm_num) ⟨24675, by rfl⟩ (by norm_num))
theorem R98573 : Reach 98573 := rs (se 3 (by rfl) ⟨18482, by rfl⟩) (B 36965 (by norm_num) ⟨18482, by rfl⟩ (by norm_num))
theorem R65805 : Reach 65805 := rs (se 3 (by rfl) ⟨12338, by rfl⟩) (B 24677 (by norm_num) ⟨12338, by rfl⟩ (by norm_num))
theorem R65809 : Reach 65809 := rs (se 2 (by rfl) ⟨24678, by rfl⟩) (B 49357 (by norm_num) ⟨24678, by rfl⟩ (by norm_num))
theorem R65813 : Reach 65813 := rs (se 6 (by rfl) ⟨1542, by rfl⟩) (B 3085 (by norm_num) ⟨1542, by rfl⟩ (by norm_num))
theorem R65817 : Reach 65817 := rs (se 2 (by rfl) ⟨24681, by rfl⟩) (B 49363 (by norm_num) ⟨24681, by rfl⟩ (by norm_num))
theorem R65821 : Reach 65821 := rs (se 3 (by rfl) ⟨12341, by rfl⟩) (B 24683 (by norm_num) ⟨12341, by rfl⟩ (by norm_num))
theorem R65825 : Reach 65825 := rs (se 2 (by rfl) ⟨24684, by rfl⟩) (B 49369 (by norm_num) ⟨24684, by rfl⟩ (by norm_num))
theorem R98597 : Reach 98597 := rs (se 4 (by rfl) ⟨9243, by rfl⟩) (B 18487 (by norm_num) ⟨9243, by rfl⟩ (by norm_num))
theorem R65829 : Reach 65829 := rs (se 4 (by rfl) ⟨6171, by rfl⟩) (B 12343 (by norm_num) ⟨6171, by rfl⟩ (by norm_num))
theorem R65833 : Reach 65833 := rs (se 2 (by rfl) ⟨24687, by rfl⟩) (B 49375 (by norm_num) ⟨24687, by rfl⟩ (by norm_num))
theorem R65837 : Reach 65837 := rs (se 3 (by rfl) ⟨12344, by rfl⟩) (B 24689 (by norm_num) ⟨12344, by rfl⟩ (by norm_num))
theorem R65841 : Reach 65841 := rs (se 2 (by rfl) ⟨24690, by rfl⟩) (B 49381 (by norm_num) ⟨24690, by rfl⟩ (by norm_num))
theorem R65845 : Reach 65845 := rs (se 5 (by rfl) ⟨3086, by rfl⟩) (B 6173 (by norm_num) ⟨3086, by rfl⟩ (by norm_num))
theorem R65849 : Reach 65849 := rs (se 2 (by rfl) ⟨24693, by rfl⟩) (B 49387 (by norm_num) ⟨24693, by rfl⟩ (by norm_num))
theorem R98621 : Reach 98621 := rs (se 3 (by rfl) ⟨18491, by rfl⟩) (B 36983 (by norm_num) ⟨18491, by rfl⟩ (by norm_num))
theorem R65853 : Reach 65853 := rs (se 3 (by rfl) ⟨12347, by rfl⟩) (B 24695 (by norm_num) ⟨12347, by rfl⟩ (by norm_num))
theorem R65857 : Reach 65857 := rs (se 2 (by rfl) ⟨24696, by rfl⟩) (B 49393 (by norm_num) ⟨24696, by rfl⟩ (by norm_num))
theorem R65861 : Reach 65861 := rs (se 4 (by rfl) ⟨6174, by rfl⟩) (B 12349 (by norm_num) ⟨6174, by rfl⟩ (by norm_num))
theorem R65865 : Reach 65865 := rs (se 2 (by rfl) ⟨24699, by rfl⟩) (B 49399 (by norm_num) ⟨24699, by rfl⟩ (by norm_num))
theorem R65869 : Reach 65869 := rs (se 3 (by rfl) ⟨12350, by rfl⟩) (B 24701 (by norm_num) ⟨12350, by rfl⟩ (by norm_num))
theorem R65873 : Reach 65873 := rs (se 2 (by rfl) ⟨24702, by rfl⟩) (B 49405 (by norm_num) ⟨24702, by rfl⟩ (by norm_num))
theorem R98645 : Reach 98645 := rs (se 10 (by rfl) ⟨144, by rfl⟩) (B 289 (by norm_num) ⟨144, by rfl⟩ (by norm_num))
theorem R65877 : Reach 65877 := rs (se 10 (by rfl) ⟨96, by rfl⟩) (B 193 (by norm_num) ⟨96, by rfl⟩ (by norm_num))
theorem R65881 : Reach 65881 := rs (se 2 (by rfl) ⟨24705, by rfl⟩) (B 49411 (by norm_num) ⟨24705, by rfl⟩ (by norm_num))
theorem R65885 : Reach 65885 := rs (se 3 (by rfl) ⟨12353, by rfl⟩) (B 24707 (by norm_num) ⟨12353, by rfl⟩ (by norm_num))
theorem R65889 : Reach 65889 := rs (se 2 (by rfl) ⟨24708, by rfl⟩) (B 49417 (by norm_num) ⟨24708, by rfl⟩ (by norm_num))
theorem R65893 : Reach 65893 := rs (se 4 (by rfl) ⟨6177, by rfl⟩) (B 12355 (by norm_num) ⟨6177, by rfl⟩ (by norm_num))
theorem R65897 : Reach 65897 := rs (se 2 (by rfl) ⟨24711, by rfl⟩) (B 49423 (by norm_num) ⟨24711, by rfl⟩ (by norm_num))
theorem R98669 : Reach 98669 := rs (se 3 (by rfl) ⟨18500, by rfl⟩) (B 37001 (by norm_num) ⟨18500, by rfl⟩ (by norm_num))
theorem R65901 : Reach 65901 := rs (se 3 (by rfl) ⟨12356, by rfl⟩) (B 24713 (by norm_num) ⟨12356, by rfl⟩ (by norm_num))
theorem R65905 : Reach 65905 := rs (se 2 (by rfl) ⟨24714, by rfl⟩) (B 49429 (by norm_num) ⟨24714, by rfl⟩ (by norm_num))
theorem R65909 : Reach 65909 := rs (se 5 (by rfl) ⟨3089, by rfl⟩) (B 6179 (by norm_num) ⟨3089, by rfl⟩ (by norm_num))
theorem R65913 : Reach 65913 := rs (se 2 (by rfl) ⟨24717, by rfl⟩) (B 49435 (by norm_num) ⟨24717, by rfl⟩ (by norm_num))
theorem R65917 : Reach 65917 := rs (se 3 (by rfl) ⟨12359, by rfl⟩) (B 24719 (by norm_num) ⟨12359, by rfl⟩ (by norm_num))
theorem R65921 : Reach 65921 := rs (se 2 (by rfl) ⟨24720, by rfl⟩) (B 49441 (by norm_num) ⟨24720, by rfl⟩ (by norm_num))
theorem R98693 : Reach 98693 := rs (se 4 (by rfl) ⟨9252, by rfl⟩) (B 18505 (by norm_num) ⟨9252, by rfl⟩ (by norm_num))
theorem R65925 : Reach 65925 := rs (se 4 (by rfl) ⟨6180, by rfl⟩) (B 12361 (by norm_num) ⟨6180, by rfl⟩ (by norm_num))
theorem R65929 : Reach 65929 := rs (se 2 (by rfl) ⟨24723, by rfl⟩) (B 49447 (by norm_num) ⟨24723, by rfl⟩ (by norm_num))
theorem R65933 : Reach 65933 := rs (se 3 (by rfl) ⟨12362, by rfl⟩) (B 24725 (by norm_num) ⟨12362, by rfl⟩ (by norm_num))
theorem R65937 : Reach 65937 := rs (se 2 (by rfl) ⟨24726, by rfl⟩) (B 49453 (by norm_num) ⟨24726, by rfl⟩ (by norm_num))
theorem R65941 : Reach 65941 := rs (se 6 (by rfl) ⟨1545, by rfl⟩) (B 3091 (by norm_num) ⟨1545, by rfl⟩ (by norm_num))
theorem R65945 : Reach 65945 := rs (se 2 (by rfl) ⟨24729, by rfl⟩) (B 49459 (by norm_num) ⟨24729, by rfl⟩ (by norm_num))
theorem R98717 : Reach 98717 := rs (se 3 (by rfl) ⟨18509, by rfl⟩) (B 37019 (by norm_num) ⟨18509, by rfl⟩ (by norm_num))
theorem R65949 : Reach 65949 := rs (se 3 (by rfl) ⟨12365, by rfl⟩) (B 24731 (by norm_num) ⟨12365, by rfl⟩ (by norm_num))
theorem R65953 : Reach 65953 := rs (se 2 (by rfl) ⟨24732, by rfl⟩) (B 49465 (by norm_num) ⟨24732, by rfl⟩ (by norm_num))
theorem R65957 : Reach 65957 := rs (se 4 (by rfl) ⟨6183, by rfl⟩) (B 12367 (by norm_num) ⟨6183, by rfl⟩ (by norm_num))
theorem R65961 : Reach 65961 := rs (se 2 (by rfl) ⟨24735, by rfl⟩) (B 49471 (by norm_num) ⟨24735, by rfl⟩ (by norm_num))
theorem R65965 : Reach 65965 := rs (se 3 (by rfl) ⟨12368, by rfl⟩) (B 24737 (by norm_num) ⟨12368, by rfl⟩ (by norm_num))
theorem R65969 : Reach 65969 := rs (se 2 (by rfl) ⟨24738, by rfl⟩) (B 49477 (by norm_num) ⟨24738, by rfl⟩ (by norm_num))
theorem R98741 : Reach 98741 := rs (se 5 (by rfl) ⟨4628, by rfl⟩) (B 9257 (by norm_num) ⟨4628, by rfl⟩ (by norm_num))
theorem R65973 : Reach 65973 := rs (se 5 (by rfl) ⟨3092, by rfl⟩) (B 6185 (by norm_num) ⟨3092, by rfl⟩ (by norm_num))
theorem R65977 : Reach 65977 := rs (se 2 (by rfl) ⟨24741, by rfl⟩) (B 49483 (by norm_num) ⟨24741, by rfl⟩ (by norm_num))
theorem R65981 : Reach 65981 := rs (se 3 (by rfl) ⟨12371, by rfl⟩) (B 24743 (by norm_num) ⟨12371, by rfl⟩ (by norm_num))
theorem R65985 : Reach 65985 := rs (se 2 (by rfl) ⟨24744, by rfl⟩) (B 49489 (by norm_num) ⟨24744, by rfl⟩ (by norm_num))
theorem R65989 : Reach 65989 := rs (se 4 (by rfl) ⟨6186, by rfl⟩) (B 12373 (by norm_num) ⟨6186, by rfl⟩ (by norm_num))
theorem R65993 : Reach 65993 := rs (se 2 (by rfl) ⟨24747, by rfl⟩) (B 49495 (by norm_num) ⟨24747, by rfl⟩ (by norm_num))
theorem R98765 : Reach 98765 := rs (se 3 (by rfl) ⟨18518, by rfl⟩) (B 37037 (by norm_num) ⟨18518, by rfl⟩ (by norm_num))
theorem R65997 : Reach 65997 := rs (se 3 (by rfl) ⟨12374, by rfl⟩) (B 24749 (by norm_num) ⟨12374, by rfl⟩ (by norm_num))
theorem R66001 : Reach 66001 := rs (se 2 (by rfl) ⟨24750, by rfl⟩) (B 49501 (by norm_num) ⟨24750, by rfl⟩ (by norm_num))
theorem R66005 : Reach 66005 := rs (se 7 (by rfl) ⟨773, by rfl⟩) (B 1547 (by norm_num) ⟨773, by rfl⟩ (by norm_num))
theorem R66009 : Reach 66009 := rs (se 2 (by rfl) ⟨24753, by rfl⟩) (B 49507 (by norm_num) ⟨24753, by rfl⟩ (by norm_num))
theorem R66013 : Reach 66013 := rs (se 3 (by rfl) ⟨12377, by rfl⟩) (B 24755 (by norm_num) ⟨12377, by rfl⟩ (by norm_num))
theorem R66017 : Reach 66017 := rs (se 2 (by rfl) ⟨24756, by rfl⟩) (B 49513 (by norm_num) ⟨24756, by rfl⟩ (by norm_num))
theorem R98789 : Reach 98789 := rs (se 4 (by rfl) ⟨9261, by rfl⟩) (B 18523 (by norm_num) ⟨9261, by rfl⟩ (by norm_num))
theorem R66021 : Reach 66021 := rs (se 4 (by rfl) ⟨6189, by rfl⟩) (B 12379 (by norm_num) ⟨6189, by rfl⟩ (by norm_num))
theorem R66025 : Reach 66025 := rs (se 2 (by rfl) ⟨24759, by rfl⟩) (B 49519 (by norm_num) ⟨24759, by rfl⟩ (by norm_num))
theorem R66029 : Reach 66029 := rs (se 3 (by rfl) ⟨12380, by rfl⟩) (B 24761 (by norm_num) ⟨12380, by rfl⟩ (by norm_num))
theorem R66033 : Reach 66033 := rs (se 2 (by rfl) ⟨24762, by rfl⟩) (B 49525 (by norm_num) ⟨24762, by rfl⟩ (by norm_num))
theorem R66037 : Reach 66037 := rs (se 5 (by rfl) ⟨3095, by rfl⟩) (B 6191 (by norm_num) ⟨3095, by rfl⟩ (by norm_num))
theorem R66041 : Reach 66041 := rs (se 2 (by rfl) ⟨24765, by rfl⟩) (B 49531 (by norm_num) ⟨24765, by rfl⟩ (by norm_num))
theorem R98813 : Reach 98813 := rs (se 3 (by rfl) ⟨18527, by rfl⟩) (B 37055 (by norm_num) ⟨18527, by rfl⟩ (by norm_num))
theorem R66045 : Reach 66045 := rs (se 3 (by rfl) ⟨12383, by rfl⟩) (B 24767 (by norm_num) ⟨12383, by rfl⟩ (by norm_num))
theorem R66049 : Reach 66049 := rs (se 2 (by rfl) ⟨24768, by rfl⟩) (B 49537 (by norm_num) ⟨24768, by rfl⟩ (by norm_num))
theorem R66053 : Reach 66053 := rs (se 4 (by rfl) ⟨6192, by rfl⟩) (B 12385 (by norm_num) ⟨6192, by rfl⟩ (by norm_num))
theorem R66057 : Reach 66057 := rs (se 2 (by rfl) ⟨24771, by rfl⟩) (B 49543 (by norm_num) ⟨24771, by rfl⟩ (by norm_num))
theorem R66061 : Reach 66061 := rs (se 3 (by rfl) ⟨12386, by rfl⟩) (B 24773 (by norm_num) ⟨12386, by rfl⟩ (by norm_num))
theorem R66065 : Reach 66065 := rs (se 2 (by rfl) ⟨24774, by rfl⟩) (B 49549 (by norm_num) ⟨24774, by rfl⟩ (by norm_num))
theorem R98837 : Reach 98837 := rs (se 6 (by rfl) ⟨2316, by rfl⟩) (B 4633 (by norm_num) ⟨2316, by rfl⟩ (by norm_num))
theorem R66069 : Reach 66069 := rs (se 6 (by rfl) ⟨1548, by rfl⟩) (B 3097 (by norm_num) ⟨1548, by rfl⟩ (by norm_num))
theorem R66073 : Reach 66073 := rs (se 2 (by rfl) ⟨24777, by rfl⟩) (B 49555 (by norm_num) ⟨24777, by rfl⟩ (by norm_num))
theorem R66077 : Reach 66077 := rs (se 3 (by rfl) ⟨12389, by rfl⟩) (B 24779 (by norm_num) ⟨12389, by rfl⟩ (by norm_num))
theorem R66081 : Reach 66081 := rs (se 2 (by rfl) ⟨24780, by rfl⟩) (B 49561 (by norm_num) ⟨24780, by rfl⟩ (by norm_num))
theorem R164389 : Reach 164389 := rs (se 4 (by rfl) ⟨15411, by rfl⟩) (B 30823 (by norm_num) ⟨15411, by rfl⟩ (by norm_num))
theorem R66085 : Reach 66085 := rs (se 4 (by rfl) ⟨6195, by rfl⟩) (B 12391 (by norm_num) ⟨6195, by rfl⟩ (by norm_num))
theorem R66089 : Reach 66089 := rs (se 2 (by rfl) ⟨24783, by rfl⟩) (B 49567 (by norm_num) ⟨24783, by rfl⟩ (by norm_num))
theorem R98861 : Reach 98861 := rs (se 3 (by rfl) ⟨18536, by rfl⟩) (B 37073 (by norm_num) ⟨18536, by rfl⟩ (by norm_num))
theorem R66093 : Reach 66093 := rs (se 3 (by rfl) ⟨12392, by rfl⟩) (B 24785 (by norm_num) ⟨12392, by rfl⟩ (by norm_num))
theorem R66097 : Reach 66097 := rs (se 2 (by rfl) ⟨24786, by rfl⟩) (B 49573 (by norm_num) ⟨24786, by rfl⟩ (by norm_num))
theorem R66101 : Reach 66101 := rs (se 5 (by rfl) ⟨3098, by rfl⟩) (B 6197 (by norm_num) ⟨3098, by rfl⟩ (by norm_num))
theorem R66105 : Reach 66105 := rs (se 2 (by rfl) ⟨24789, by rfl⟩) (B 49579 (by norm_num) ⟨24789, by rfl⟩ (by norm_num))
theorem R66109 : Reach 66109 := rs (se 3 (by rfl) ⟨12395, by rfl⟩) (B 24791 (by norm_num) ⟨12395, by rfl⟩ (by norm_num))
theorem R66113 : Reach 66113 := rs (se 2 (by rfl) ⟨24792, by rfl⟩) (B 49585 (by norm_num) ⟨24792, by rfl⟩ (by norm_num))
theorem R98885 : Reach 98885 := rs (se 4 (by rfl) ⟨9270, by rfl⟩) (B 18541 (by norm_num) ⟨9270, by rfl⟩ (by norm_num))
theorem R66117 : Reach 66117 := rs (se 4 (by rfl) ⟨6198, by rfl⟩) (B 12397 (by norm_num) ⟨6198, by rfl⟩ (by norm_num))
theorem R66121 : Reach 66121 := rs (se 2 (by rfl) ⟨24795, by rfl⟩) (B 49591 (by norm_num) ⟨24795, by rfl⟩ (by norm_num))
theorem R66125 : Reach 66125 := rs (se 3 (by rfl) ⟨12398, by rfl⟩) (B 24797 (by norm_num) ⟨12398, by rfl⟩ (by norm_num))
theorem R66129 : Reach 66129 := rs (se 2 (by rfl) ⟨24798, by rfl⟩) (B 49597 (by norm_num) ⟨24798, by rfl⟩ (by norm_num))
theorem R66133 : Reach 66133 := rs (se 8 (by rfl) ⟨387, by rfl⟩) (B 775 (by norm_num) ⟨387, by rfl⟩ (by norm_num))
theorem R66137 : Reach 66137 := rs (se 2 (by rfl) ⟨24801, by rfl⟩) (B 49603 (by norm_num) ⟨24801, by rfl⟩ (by norm_num))
theorem R98909 : Reach 98909 := rs (se 3 (by rfl) ⟨18545, by rfl⟩) (B 37091 (by norm_num) ⟨18545, by rfl⟩ (by norm_num))
theorem R66141 : Reach 66141 := rs (se 3 (by rfl) ⟨12401, by rfl⟩) (B 24803 (by norm_num) ⟨12401, by rfl⟩ (by norm_num))
theorem R66145 : Reach 66145 := rs (se 2 (by rfl) ⟨24804, by rfl⟩) (B 49609 (by norm_num) ⟨24804, by rfl⟩ (by norm_num))
theorem R66149 : Reach 66149 := rs (se 4 (by rfl) ⟨6201, by rfl⟩) (B 12403 (by norm_num) ⟨6201, by rfl⟩ (by norm_num))
theorem R66153 : Reach 66153 := rs (se 2 (by rfl) ⟨24807, by rfl⟩) (B 49615 (by norm_num) ⟨24807, by rfl⟩ (by norm_num))
theorem R66157 : Reach 66157 := rs (se 3 (by rfl) ⟨12404, by rfl⟩) (B 24809 (by norm_num) ⟨12404, by rfl⟩ (by norm_num))
theorem R66161 : Reach 66161 := rs (se 2 (by rfl) ⟨24810, by rfl⟩) (B 49621 (by norm_num) ⟨24810, by rfl⟩ (by norm_num))
theorem R98933 : Reach 98933 := rs (se 5 (by rfl) ⟨4637, by rfl⟩) (B 9275 (by norm_num) ⟨4637, by rfl⟩ (by norm_num))
theorem R66165 : Reach 66165 := rs (se 5 (by rfl) ⟨3101, by rfl⟩) (B 6203 (by norm_num) ⟨3101, by rfl⟩ (by norm_num))
theorem R66169 : Reach 66169 := rs (se 2 (by rfl) ⟨24813, by rfl⟩) (B 49627 (by norm_num) ⟨24813, by rfl⟩ (by norm_num))
theorem R66173 : Reach 66173 := rs (se 3 (by rfl) ⟨12407, by rfl⟩) (B 24815 (by norm_num) ⟨12407, by rfl⟩ (by norm_num))
theorem R66177 : Reach 66177 := rs (se 2 (by rfl) ⟨24816, by rfl⟩) (B 49633 (by norm_num) ⟨24816, by rfl⟩ (by norm_num))
theorem R66181 : Reach 66181 := rs (se 4 (by rfl) ⟨6204, by rfl⟩) (B 12409 (by norm_num) ⟨6204, by rfl⟩ (by norm_num))
theorem R66185 : Reach 66185 := rs (se 2 (by rfl) ⟨24819, by rfl⟩) (B 49639 (by norm_num) ⟨24819, by rfl⟩ (by norm_num))
theorem R98957 : Reach 98957 := rs (se 3 (by rfl) ⟨18554, by rfl⟩) (B 37109 (by norm_num) ⟨18554, by rfl⟩ (by norm_num))
theorem R66189 : Reach 66189 := rs (se 3 (by rfl) ⟨12410, by rfl⟩) (B 24821 (by norm_num) ⟨12410, by rfl⟩ (by norm_num))
theorem R66193 : Reach 66193 := rs (se 2 (by rfl) ⟨24822, by rfl⟩) (B 49645 (by norm_num) ⟨24822, by rfl⟩ (by norm_num))
theorem R164501 : Reach 164501 := rs (se 6 (by rfl) ⟨3855, by rfl⟩) (B 7711 (by norm_num) ⟨3855, by rfl⟩ (by norm_num))
theorem R66197 : Reach 66197 := rs (se 6 (by rfl) ⟨1551, by rfl⟩) (B 3103 (by norm_num) ⟨1551, by rfl⟩ (by norm_num))
theorem R66201 : Reach 66201 := rs (se 2 (by rfl) ⟨24825, by rfl⟩) (B 49651 (by norm_num) ⟨24825, by rfl⟩ (by norm_num))
theorem R66205 : Reach 66205 := rs (se 3 (by rfl) ⟨12413, by rfl⟩) (B 24827 (by norm_num) ⟨12413, by rfl⟩ (by norm_num))
theorem R66209 : Reach 66209 := rs (se 2 (by rfl) ⟨24828, by rfl⟩) (B 49657 (by norm_num) ⟨24828, by rfl⟩ (by norm_num))
theorem R98981 : Reach 98981 := rs (se 4 (by rfl) ⟨9279, by rfl⟩) (B 18559 (by norm_num) ⟨9279, by rfl⟩ (by norm_num))
theorem R66213 : Reach 66213 := rs (se 4 (by rfl) ⟨6207, by rfl⟩) (B 12415 (by norm_num) ⟨6207, by rfl⟩ (by norm_num))
theorem R66217 : Reach 66217 := rs (se 2 (by rfl) ⟨24831, by rfl⟩) (B 49663 (by norm_num) ⟨24831, by rfl⟩ (by norm_num))
theorem R66221 : Reach 66221 := rs (se 3 (by rfl) ⟨12416, by rfl⟩) (B 24833 (by norm_num) ⟨12416, by rfl⟩ (by norm_num))
theorem R66225 : Reach 66225 := rs (se 2 (by rfl) ⟨24834, by rfl⟩) (B 49669 (by norm_num) ⟨24834, by rfl⟩ (by norm_num))
theorem R328373 : Reach 328373 := rs (se 5 (by rfl) ⟨15392, by rfl⟩) (B 30785 (by norm_num) ⟨15392, by rfl⟩ (by norm_num))
theorem R66229 : Reach 66229 := rs (se 5 (by rfl) ⟨3104, by rfl⟩) (B 6209 (by norm_num) ⟨3104, by rfl⟩ (by norm_num))
theorem R66233 : Reach 66233 := rs (se 2 (by rfl) ⟨24837, by rfl⟩) (B 49675 (by norm_num) ⟨24837, by rfl⟩ (by norm_num))
theorem R99005 : Reach 99005 := rs (se 3 (by rfl) ⟨18563, by rfl⟩) (B 37127 (by norm_num) ⟨18563, by rfl⟩ (by norm_num))
theorem R66237 : Reach 66237 := rs (se 3 (by rfl) ⟨12419, by rfl⟩) (B 24839 (by norm_num) ⟨12419, by rfl⟩ (by norm_num))
theorem R66241 : Reach 66241 := rs (se 2 (by rfl) ⟨24840, by rfl⟩) (B 49681 (by norm_num) ⟨24840, by rfl⟩ (by norm_num))
theorem R66245 : Reach 66245 := rs (se 4 (by rfl) ⟨6210, by rfl⟩) (B 12421 (by norm_num) ⟨6210, by rfl⟩ (by norm_num))
theorem R66249 : Reach 66249 := rs (se 2 (by rfl) ⟨24843, by rfl⟩) (B 49687 (by norm_num) ⟨24843, by rfl⟩ (by norm_num))
theorem R66253 : Reach 66253 := rs (se 3 (by rfl) ⟨12422, by rfl⟩) (B 24845 (by norm_num) ⟨12422, by rfl⟩ (by norm_num))
theorem R66257 : Reach 66257 := rs (se 2 (by rfl) ⟨24846, by rfl⟩) (B 49693 (by norm_num) ⟨24846, by rfl⟩ (by norm_num))
theorem R99029 : Reach 99029 := rs (se 7 (by rfl) ⟨1160, by rfl⟩) (B 2321 (by norm_num) ⟨1160, by rfl⟩ (by norm_num))
theorem R66261 : Reach 66261 := rs (se 7 (by rfl) ⟨776, by rfl⟩) (B 1553 (by norm_num) ⟨776, by rfl⟩ (by norm_num))
theorem R66265 : Reach 66265 := rs (se 2 (by rfl) ⟨24849, by rfl⟩) (B 49699 (by norm_num) ⟨24849, by rfl⟩ (by norm_num))
theorem R66269 : Reach 66269 := rs (se 3 (by rfl) ⟨12425, by rfl⟩) (B 24851 (by norm_num) ⟨12425, by rfl⟩ (by norm_num))
theorem R66273 : Reach 66273 := rs (se 2 (by rfl) ⟨24852, by rfl⟩) (B 49705 (by norm_num) ⟨24852, by rfl⟩ (by norm_num))
theorem R328421 : Reach 328421 := rs (se 4 (by rfl) ⟨30789, by rfl⟩) (B 61579 (by norm_num) ⟨30789, by rfl⟩ (by norm_num))
theorem R66277 : Reach 66277 := rs (se 4 (by rfl) ⟨6213, by rfl⟩) (B 12427 (by norm_num) ⟨6213, by rfl⟩ (by norm_num))
theorem R66281 : Reach 66281 := rs (se 2 (by rfl) ⟨24855, by rfl⟩) (B 49711 (by norm_num) ⟨24855, by rfl⟩ (by norm_num))
theorem R99053 : Reach 99053 := rs (se 3 (by rfl) ⟨18572, by rfl⟩) (B 37145 (by norm_num) ⟨18572, by rfl⟩ (by norm_num))
theorem R66285 : Reach 66285 := rs (se 3 (by rfl) ⟨12428, by rfl⟩) (B 24857 (by norm_num) ⟨12428, by rfl⟩ (by norm_num))
theorem R66289 : Reach 66289 := rs (se 2 (by rfl) ⟨24858, by rfl⟩) (B 49717 (by norm_num) ⟨24858, by rfl⟩ (by norm_num))
theorem R66293 : Reach 66293 := rs (se 5 (by rfl) ⟨3107, by rfl⟩) (B 6215 (by norm_num) ⟨3107, by rfl⟩ (by norm_num))
theorem R66297 : Reach 66297 := rs (se 2 (by rfl) ⟨24861, by rfl⟩) (B 49723 (by norm_num) ⟨24861, by rfl⟩ (by norm_num))
theorem R66301 : Reach 66301 := rs (se 3 (by rfl) ⟨12431, by rfl⟩) (B 24863 (by norm_num) ⟨12431, by rfl⟩ (by norm_num))
theorem R66305 : Reach 66305 := rs (se 2 (by rfl) ⟨24864, by rfl⟩) (B 49729 (by norm_num) ⟨24864, by rfl⟩ (by norm_num))
theorem R99077 : Reach 99077 := rs (se 4 (by rfl) ⟨9288, by rfl⟩) (B 18577 (by norm_num) ⟨9288, by rfl⟩ (by norm_num))
theorem R66309 : Reach 66309 := rs (se 4 (by rfl) ⟨6216, by rfl⟩) (B 12433 (by norm_num) ⟨6216, by rfl⟩ (by norm_num))
theorem R66313 : Reach 66313 := rs (se 2 (by rfl) ⟨24867, by rfl⟩) (B 49735 (by norm_num) ⟨24867, by rfl⟩ (by norm_num))
theorem R66317 : Reach 66317 := rs (se 3 (by rfl) ⟨12434, by rfl⟩) (B 24869 (by norm_num) ⟨12434, by rfl⟩ (by norm_num))
theorem R66321 : Reach 66321 := rs (se 2 (by rfl) ⟨24870, by rfl⟩) (B 49741 (by norm_num) ⟨24870, by rfl⟩ (by norm_num))
theorem R66325 : Reach 66325 := rs (se 6 (by rfl) ⟨1554, by rfl⟩) (B 3109 (by norm_num) ⟨1554, by rfl⟩ (by norm_num))
theorem R66329 : Reach 66329 := rs (se 2 (by rfl) ⟨24873, by rfl⟩) (B 49747 (by norm_num) ⟨24873, by rfl⟩ (by norm_num))
theorem R99101 : Reach 99101 := rs (se 3 (by rfl) ⟨18581, by rfl⟩) (B 37163 (by norm_num) ⟨18581, by rfl⟩ (by norm_num))
theorem R66333 : Reach 66333 := rs (se 3 (by rfl) ⟨12437, by rfl⟩) (B 24875 (by norm_num) ⟨12437, by rfl⟩ (by norm_num))
theorem R66337 : Reach 66337 := rs (se 2 (by rfl) ⟨24876, by rfl⟩) (B 49753 (by norm_num) ⟨24876, by rfl⟩ (by norm_num))
theorem R66341 : Reach 66341 := rs (se 4 (by rfl) ⟨6219, by rfl⟩) (B 12439 (by norm_num) ⟨6219, by rfl⟩ (by norm_num))
theorem R66345 : Reach 66345 := rs (se 2 (by rfl) ⟨24879, by rfl⟩) (B 49759 (by norm_num) ⟨24879, by rfl⟩ (by norm_num))
theorem R66349 : Reach 66349 := rs (se 3 (by rfl) ⟨12440, by rfl⟩) (B 24881 (by norm_num) ⟨12440, by rfl⟩ (by norm_num))
theorem R66353 : Reach 66353 := rs (se 2 (by rfl) ⟨24882, by rfl⟩) (B 49765 (by norm_num) ⟨24882, by rfl⟩ (by norm_num))
theorem R99125 : Reach 99125 := rs (se 5 (by rfl) ⟨4646, by rfl⟩) (B 9293 (by norm_num) ⟨4646, by rfl⟩ (by norm_num))
theorem R66357 : Reach 66357 := rs (se 5 (by rfl) ⟨3110, by rfl⟩) (B 6221 (by norm_num) ⟨3110, by rfl⟩ (by norm_num))
theorem R66361 : Reach 66361 := rs (se 2 (by rfl) ⟨24885, by rfl⟩) (B 49771 (by norm_num) ⟨24885, by rfl⟩ (by norm_num))
theorem R66365 : Reach 66365 := rs (se 3 (by rfl) ⟨12443, by rfl⟩) (B 24887 (by norm_num) ⟨12443, by rfl⟩ (by norm_num))
theorem R66369 : Reach 66369 := rs (se 2 (by rfl) ⟨24888, by rfl⟩) (B 49777 (by norm_num) ⟨24888, by rfl⟩ (by norm_num))
theorem R66373 : Reach 66373 := rs (se 4 (by rfl) ⟨6222, by rfl⟩) (B 12445 (by norm_num) ⟨6222, by rfl⟩ (by norm_num))
theorem R66377 : Reach 66377 := rs (se 2 (by rfl) ⟨24891, by rfl⟩) (B 49783 (by norm_num) ⟨24891, by rfl⟩ (by norm_num))
theorem R99149 : Reach 99149 := rs (se 3 (by rfl) ⟨18590, by rfl⟩) (B 37181 (by norm_num) ⟨18590, by rfl⟩ (by norm_num))
theorem R66381 : Reach 66381 := rs (se 3 (by rfl) ⟨12446, by rfl⟩) (B 24893 (by norm_num) ⟨12446, by rfl⟩ (by norm_num))
theorem R66385 : Reach 66385 := rs (se 2 (by rfl) ⟨24894, by rfl⟩) (B 49789 (by norm_num) ⟨24894, by rfl⟩ (by norm_num))
theorem R164693 : Reach 164693 := rs (se 9 (by rfl) ⟨482, by rfl⟩) (B 965 (by norm_num) ⟨482, by rfl⟩ (by norm_num))
theorem R66389 : Reach 66389 := rs (se 9 (by rfl) ⟨194, by rfl⟩) (B 389 (by norm_num) ⟨194, by rfl⟩ (by norm_num))
theorem R66393 : Reach 66393 := rs (se 2 (by rfl) ⟨24897, by rfl⟩) (B 49795 (by norm_num) ⟨24897, by rfl⟩ (by norm_num))
theorem R66397 : Reach 66397 := rs (se 3 (by rfl) ⟨12449, by rfl⟩) (B 24899 (by norm_num) ⟨12449, by rfl⟩ (by norm_num))
theorem R66401 : Reach 66401 := rs (se 2 (by rfl) ⟨24900, by rfl⟩) (B 49801 (by norm_num) ⟨24900, by rfl⟩ (by norm_num))
theorem R99173 : Reach 99173 := rs (se 4 (by rfl) ⟨9297, by rfl⟩) (B 18595 (by norm_num) ⟨9297, by rfl⟩ (by norm_num))
theorem R66405 : Reach 66405 := rs (se 4 (by rfl) ⟨6225, by rfl⟩) (B 12451 (by norm_num) ⟨6225, by rfl⟩ (by norm_num))
theorem R66409 : Reach 66409 := rs (se 2 (by rfl) ⟨24903, by rfl⟩) (B 49807 (by norm_num) ⟨24903, by rfl⟩ (by norm_num))
theorem R66413 : Reach 66413 := rs (se 3 (by rfl) ⟨12452, by rfl⟩) (B 24905 (by norm_num) ⟨12452, by rfl⟩ (by norm_num))
theorem R66417 : Reach 66417 := rs (se 2 (by rfl) ⟨24906, by rfl⟩) (B 49813 (by norm_num) ⟨24906, by rfl⟩ (by norm_num))
theorem R623477 : Reach 623477 := rs (se 5 (by rfl) ⟨29225, by rfl⟩) (B 58451 (by norm_num) ⟨29225, by rfl⟩ (by norm_num))
theorem R66421 : Reach 66421 := rs (se 5 (by rfl) ⟨3113, by rfl⟩) (B 6227 (by norm_num) ⟨3113, by rfl⟩ (by norm_num))
theorem R66425 : Reach 66425 := rs (se 2 (by rfl) ⟨24909, by rfl⟩) (B 49819 (by norm_num) ⟨24909, by rfl⟩ (by norm_num))
theorem R99197 : Reach 99197 := rs (se 3 (by rfl) ⟨18599, by rfl⟩) (B 37199 (by norm_num) ⟨18599, by rfl⟩ (by norm_num))
theorem R66429 : Reach 66429 := rs (se 3 (by rfl) ⟨12455, by rfl⟩) (B 24911 (by norm_num) ⟨12455, by rfl⟩ (by norm_num))
theorem R66433 : Reach 66433 := rs (se 2 (by rfl) ⟨24912, by rfl⟩) (B 49825 (by norm_num) ⟨24912, by rfl⟩ (by norm_num))
theorem R66437 : Reach 66437 := rs (se 4 (by rfl) ⟨6228, by rfl⟩) (B 12457 (by norm_num) ⟨6228, by rfl⟩ (by norm_num))
theorem R66441 : Reach 66441 := rs (se 2 (by rfl) ⟨24915, by rfl⟩) (B 49831 (by norm_num) ⟨24915, by rfl⟩ (by norm_num))
theorem R66445 : Reach 66445 := rs (se 3 (by rfl) ⟨12458, by rfl⟩) (B 24917 (by norm_num) ⟨12458, by rfl⟩ (by norm_num))
theorem R66449 : Reach 66449 := rs (se 2 (by rfl) ⟨24918, by rfl⟩) (B 49837 (by norm_num) ⟨24918, by rfl⟩ (by norm_num))
theorem R99221 : Reach 99221 := rs (se 6 (by rfl) ⟨2325, by rfl⟩) (B 4651 (by norm_num) ⟨2325, by rfl⟩ (by norm_num))
theorem R66453 : Reach 66453 := rs (se 6 (by rfl) ⟨1557, by rfl⟩) (B 3115 (by norm_num) ⟨1557, by rfl⟩ (by norm_num))
theorem R66457 : Reach 66457 := rs (se 2 (by rfl) ⟨24921, by rfl⟩) (B 49843 (by norm_num) ⟨24921, by rfl⟩ (by norm_num))
theorem R66461 : Reach 66461 := rs (se 3 (by rfl) ⟨12461, by rfl⟩) (B 24923 (by norm_num) ⟨12461, by rfl⟩ (by norm_num))
theorem R66465 : Reach 66465 := rs (se 2 (by rfl) ⟨24924, by rfl⟩) (B 49849 (by norm_num) ⟨24924, by rfl⟩ (by norm_num))
theorem R66469 : Reach 66469 := rs (se 4 (by rfl) ⟨6231, by rfl⟩) (B 12463 (by norm_num) ⟨6231, by rfl⟩ (by norm_num))
theorem R66473 : Reach 66473 := rs (se 2 (by rfl) ⟨24927, by rfl⟩) (B 49855 (by norm_num) ⟨24927, by rfl⟩ (by norm_num))
theorem R99245 : Reach 99245 := rs (se 3 (by rfl) ⟨18608, by rfl⟩) (B 37217 (by norm_num) ⟨18608, by rfl⟩ (by norm_num))
theorem R66477 : Reach 66477 := rs (se 3 (by rfl) ⟨12464, by rfl⟩) (B 24929 (by norm_num) ⟨12464, by rfl⟩ (by norm_num))
theorem R66481 : Reach 66481 := rs (se 2 (by rfl) ⟨24930, by rfl⟩) (B 49861 (by norm_num) ⟨24930, by rfl⟩ (by norm_num))
theorem R66485 : Reach 66485 := rs (se 5 (by rfl) ⟨3116, by rfl⟩) (B 6233 (by norm_num) ⟨3116, by rfl⟩ (by norm_num))
theorem R66489 : Reach 66489 := rs (se 2 (by rfl) ⟨24933, by rfl⟩) (B 49867 (by norm_num) ⟨24933, by rfl⟩ (by norm_num))
theorem R66493 : Reach 66493 := rs (se 3 (by rfl) ⟨12467, by rfl⟩) (B 24935 (by norm_num) ⟨12467, by rfl⟩ (by norm_num))
theorem R66497 : Reach 66497 := rs (se 2 (by rfl) ⟨24936, by rfl⟩) (B 49873 (by norm_num) ⟨24936, by rfl⟩ (by norm_num))
theorem R99269 : Reach 99269 := rs (se 4 (by rfl) ⟨9306, by rfl⟩) (B 18613 (by norm_num) ⟨9306, by rfl⟩ (by norm_num))
theorem R66501 : Reach 66501 := rs (se 4 (by rfl) ⟨6234, by rfl⟩) (B 12469 (by norm_num) ⟨6234, by rfl⟩ (by norm_num))
theorem R66505 : Reach 66505 := rs (se 2 (by rfl) ⟨24939, by rfl⟩) (B 49879 (by norm_num) ⟨24939, by rfl⟩ (by norm_num))
theorem R66509 : Reach 66509 := rs (se 3 (by rfl) ⟨12470, by rfl⟩) (B 24941 (by norm_num) ⟨12470, by rfl⟩ (by norm_num))
theorem R66513 : Reach 66513 := rs (se 2 (by rfl) ⟨24942, by rfl⟩) (B 49885 (by norm_num) ⟨24942, by rfl⟩ (by norm_num))
theorem R66517 : Reach 66517 := rs (se 7 (by rfl) ⟨779, by rfl⟩) (B 1559 (by norm_num) ⟨779, by rfl⟩ (by norm_num))
theorem R66521 : Reach 66521 := rs (se 2 (by rfl) ⟨24945, by rfl⟩) (B 49891 (by norm_num) ⟨24945, by rfl⟩ (by norm_num))
theorem R99293 : Reach 99293 := rs (se 3 (by rfl) ⟨18617, by rfl⟩) (B 37235 (by norm_num) ⟨18617, by rfl⟩ (by norm_num))
theorem R66525 : Reach 66525 := rs (se 3 (by rfl) ⟨12473, by rfl⟩) (B 24947 (by norm_num) ⟨12473, by rfl⟩ (by norm_num))
theorem R66529 : Reach 66529 := rs (se 2 (by rfl) ⟨24948, by rfl⟩) (B 49897 (by norm_num) ⟨24948, by rfl⟩ (by norm_num))
theorem R66533 : Reach 66533 := rs (se 4 (by rfl) ⟨6237, by rfl⟩) (B 12475 (by norm_num) ⟨6237, by rfl⟩ (by norm_num))
theorem R66537 : Reach 66537 := rs (se 2 (by rfl) ⟨24951, by rfl⟩) (B 49903 (by norm_num) ⟨24951, by rfl⟩ (by norm_num))
theorem R66541 : Reach 66541 := rs (se 3 (by rfl) ⟨12476, by rfl⟩) (B 24953 (by norm_num) ⟨12476, by rfl⟩ (by norm_num))
theorem R66545 : Reach 66545 := rs (se 2 (by rfl) ⟨24954, by rfl⟩) (B 49909 (by norm_num) ⟨24954, by rfl⟩ (by norm_num))
theorem R99317 : Reach 99317 := rs (se 5 (by rfl) ⟨4655, by rfl⟩) (B 9311 (by norm_num) ⟨4655, by rfl⟩ (by norm_num))
theorem R66549 : Reach 66549 := rs (se 5 (by rfl) ⟨3119, by rfl⟩) (B 6239 (by norm_num) ⟨3119, by rfl⟩ (by norm_num))
theorem R66553 : Reach 66553 := rs (se 2 (by rfl) ⟨24957, by rfl⟩) (B 49915 (by norm_num) ⟨24957, by rfl⟩ (by norm_num))
theorem R66557 : Reach 66557 := rs (se 3 (by rfl) ⟨12479, by rfl⟩) (B 24959 (by norm_num) ⟨12479, by rfl⟩ (by norm_num))
theorem R66561 : Reach 66561 := rs (se 2 (by rfl) ⟨24960, by rfl⟩) (B 49921 (by norm_num) ⟨24960, by rfl⟩ (by norm_num))
theorem R66565 : Reach 66565 := rs (se 4 (by rfl) ⟨6240, by rfl⟩) (B 12481 (by norm_num) ⟨6240, by rfl⟩ (by norm_num))
theorem R66569 : Reach 66569 := rs (se 2 (by rfl) ⟨24963, by rfl⟩) (B 49927 (by norm_num) ⟨24963, by rfl⟩ (by norm_num))
theorem R99341 : Reach 99341 := rs (se 3 (by rfl) ⟨18626, by rfl⟩) (B 37253 (by norm_num) ⟨18626, by rfl⟩ (by norm_num))
theorem R66573 : Reach 66573 := rs (se 3 (by rfl) ⟨12482, by rfl⟩) (B 24965 (by norm_num) ⟨12482, by rfl⟩ (by norm_num))
theorem R66577 : Reach 66577 := rs (se 2 (by rfl) ⟨24966, by rfl⟩) (B 49933 (by norm_num) ⟨24966, by rfl⟩ (by norm_num))
theorem R361493 : Reach 361493 := rs (se 6 (by rfl) ⟨8472, by rfl⟩) (B 16945 (by norm_num) ⟨8472, by rfl⟩ (by norm_num))
theorem R66581 : Reach 66581 := rs (se 6 (by rfl) ⟨1560, by rfl⟩) (B 3121 (by norm_num) ⟨1560, by rfl⟩ (by norm_num))
theorem R66585 : Reach 66585 := rs (se 2 (by rfl) ⟨24969, by rfl⟩) (B 49939 (by norm_num) ⟨24969, by rfl⟩ (by norm_num))
theorem R66589 : Reach 66589 := rs (se 3 (by rfl) ⟨12485, by rfl⟩) (B 24971 (by norm_num) ⟨12485, by rfl⟩ (by norm_num))
theorem R66593 : Reach 66593 := rs (se 2 (by rfl) ⟨24972, by rfl⟩) (B 49945 (by norm_num) ⟨24972, by rfl⟩ (by norm_num))
theorem R99365 : Reach 99365 := rs (se 4 (by rfl) ⟨9315, by rfl⟩) (B 18631 (by norm_num) ⟨9315, by rfl⟩ (by norm_num))
theorem R66597 : Reach 66597 := rs (se 4 (by rfl) ⟨6243, by rfl⟩) (B 12487 (by norm_num) ⟨6243, by rfl⟩ (by norm_num))
theorem R66601 : Reach 66601 := rs (se 2 (by rfl) ⟨24975, by rfl⟩) (B 49951 (by norm_num) ⟨24975, by rfl⟩ (by norm_num))
theorem R66605 : Reach 66605 := rs (se 3 (by rfl) ⟨12488, by rfl⟩) (B 24977 (by norm_num) ⟨12488, by rfl⟩ (by norm_num))
theorem R66609 : Reach 66609 := rs (se 2 (by rfl) ⟨24978, by rfl⟩) (B 49957 (by norm_num) ⟨24978, by rfl⟩ (by norm_num))
theorem R66613 : Reach 66613 := rs (se 5 (by rfl) ⟨3122, by rfl⟩) (B 6245 (by norm_num) ⟨3122, by rfl⟩ (by norm_num))
theorem R66617 : Reach 66617 := rs (se 2 (by rfl) ⟨24981, by rfl⟩) (B 49963 (by norm_num) ⟨24981, by rfl⟩ (by norm_num))
theorem R99389 : Reach 99389 := rs (se 3 (by rfl) ⟨18635, by rfl⟩) (B 37271 (by norm_num) ⟨18635, by rfl⟩ (by norm_num))
theorem R66621 : Reach 66621 := rs (se 3 (by rfl) ⟨12491, by rfl⟩) (B 24983 (by norm_num) ⟨12491, by rfl⟩ (by norm_num))
theorem R66625 : Reach 66625 := rs (se 2 (by rfl) ⟨24984, by rfl⟩) (B 49969 (by norm_num) ⟨24984, by rfl⟩ (by norm_num))
theorem R66629 : Reach 66629 := rs (se 4 (by rfl) ⟨6246, by rfl⟩) (B 12493 (by norm_num) ⟨6246, by rfl⟩ (by norm_num))
theorem R66633 : Reach 66633 := rs (se 2 (by rfl) ⟨24987, by rfl⟩) (B 49975 (by norm_num) ⟨24987, by rfl⟩ (by norm_num))
theorem R66637 : Reach 66637 := rs (se 3 (by rfl) ⟨12494, by rfl⟩) (B 24989 (by norm_num) ⟨12494, by rfl⟩ (by norm_num))
theorem R66641 : Reach 66641 := rs (se 2 (by rfl) ⟨24990, by rfl⟩) (B 49981 (by norm_num) ⟨24990, by rfl⟩ (by norm_num))
theorem R99413 : Reach 99413 := rs (se 8 (by rfl) ⟨582, by rfl⟩) (B 1165 (by norm_num) ⟨582, by rfl⟩ (by norm_num))
theorem R66645 : Reach 66645 := rs (se 8 (by rfl) ⟨390, by rfl⟩) (B 781 (by norm_num) ⟨390, by rfl⟩ (by norm_num))
theorem R66649 : Reach 66649 := rs (se 2 (by rfl) ⟨24993, by rfl⟩) (B 49987 (by norm_num) ⟨24993, by rfl⟩ (by norm_num))
theorem R66653 : Reach 66653 := rs (se 3 (by rfl) ⟨12497, by rfl⟩) (B 24995 (by norm_num) ⟨12497, by rfl⟩ (by norm_num))
theorem R66657 : Reach 66657 := rs (se 2 (by rfl) ⟨24996, by rfl⟩) (B 49993 (by norm_num) ⟨24996, by rfl⟩ (by norm_num))
theorem R66661 : Reach 66661 := rs (se 4 (by rfl) ⟨6249, by rfl⟩) (B 12499 (by norm_num) ⟨6249, by rfl⟩ (by norm_num))
theorem R66665 : Reach 66665 := rs (se 2 (by rfl) ⟨24999, by rfl⟩) (B 49999 (by norm_num) ⟨24999, by rfl⟩ (by norm_num))
theorem R99437 : Reach 99437 := rs (se 3 (by rfl) ⟨18644, by rfl⟩) (B 37289 (by norm_num) ⟨18644, by rfl⟩ (by norm_num))
theorem R66669 : Reach 66669 := rs (se 3 (by rfl) ⟨12500, by rfl⟩) (B 25001 (by norm_num) ⟨12500, by rfl⟩ (by norm_num))
theorem R66673 : Reach 66673 := rs (se 2 (by rfl) ⟨25002, by rfl⟩) (B 50005 (by norm_num) ⟨25002, by rfl⟩ (by norm_num))
theorem R66677 : Reach 66677 := rs (se 5 (by rfl) ⟨3125, by rfl⟩) (B 6251 (by norm_num) ⟨3125, by rfl⟩ (by norm_num))
theorem R66681 : Reach 66681 := rs (se 2 (by rfl) ⟨25005, by rfl⟩) (B 50011 (by norm_num) ⟨25005, by rfl⟩ (by norm_num))
theorem R66685 : Reach 66685 := rs (se 3 (by rfl) ⟨12503, by rfl⟩) (B 25007 (by norm_num) ⟨12503, by rfl⟩ (by norm_num))
theorem R66689 : Reach 66689 := rs (se 2 (by rfl) ⟨25008, by rfl⟩) (B 50017 (by norm_num) ⟨25008, by rfl⟩ (by norm_num))
theorem R99461 : Reach 99461 := rs (se 4 (by rfl) ⟨9324, by rfl⟩) (B 18649 (by norm_num) ⟨9324, by rfl⟩ (by norm_num))
theorem R66693 : Reach 66693 := rs (se 4 (by rfl) ⟨6252, by rfl⟩) (B 12505 (by norm_num) ⟨6252, by rfl⟩ (by norm_num))
theorem R66697 : Reach 66697 := rs (se 2 (by rfl) ⟨25011, by rfl⟩) (B 50023 (by norm_num) ⟨25011, by rfl⟩ (by norm_num))
theorem R66701 : Reach 66701 := rs (se 3 (by rfl) ⟨12506, by rfl⟩) (B 25013 (by norm_num) ⟨12506, by rfl⟩ (by norm_num))
theorem R66705 : Reach 66705 := rs (se 2 (by rfl) ⟨25014, by rfl⟩) (B 50029 (by norm_num) ⟨25014, by rfl⟩ (by norm_num))
theorem R66709 : Reach 66709 := rs (se 6 (by rfl) ⟨1563, by rfl⟩) (B 3127 (by norm_num) ⟨1563, by rfl⟩ (by norm_num))
theorem R66713 : Reach 66713 := rs (se 2 (by rfl) ⟨25017, by rfl⟩) (B 50035 (by norm_num) ⟨25017, by rfl⟩ (by norm_num))
theorem R99485 : Reach 99485 := rs (se 3 (by rfl) ⟨18653, by rfl⟩) (B 37307 (by norm_num) ⟨18653, by rfl⟩ (by norm_num))
theorem R66717 : Reach 66717 := rs (se 3 (by rfl) ⟨12509, by rfl⟩) (B 25019 (by norm_num) ⟨12509, by rfl⟩ (by norm_num))
theorem R66721 : Reach 66721 := rs (se 2 (by rfl) ⟨25020, by rfl⟩) (B 50041 (by norm_num) ⟨25020, by rfl⟩ (by norm_num))
theorem R66725 : Reach 66725 := rs (se 4 (by rfl) ⟨6255, by rfl⟩) (B 12511 (by norm_num) ⟨6255, by rfl⟩ (by norm_num))
theorem R66729 : Reach 66729 := rs (se 2 (by rfl) ⟨25023, by rfl⟩) (B 50047 (by norm_num) ⟨25023, by rfl⟩ (by norm_num))
theorem R165037 : Reach 165037 := rs (se 3 (by rfl) ⟨30944, by rfl⟩) (B 61889 (by norm_num) ⟨30944, by rfl⟩ (by norm_num))
theorem R66733 : Reach 66733 := rs (se 3 (by rfl) ⟨12512, by rfl⟩) (B 25025 (by norm_num) ⟨12512, by rfl⟩ (by norm_num))
theorem R66737 : Reach 66737 := rs (se 2 (by rfl) ⟨25026, by rfl⟩) (B 50053 (by norm_num) ⟨25026, by rfl⟩ (by norm_num))
theorem R99509 : Reach 99509 := rs (se 5 (by rfl) ⟨4664, by rfl⟩) (B 9329 (by norm_num) ⟨4664, by rfl⟩ (by norm_num))
theorem R66741 : Reach 66741 := rs (se 5 (by rfl) ⟨3128, by rfl⟩) (B 6257 (by norm_num) ⟨3128, by rfl⟩ (by norm_num))
theorem R66745 : Reach 66745 := rs (se 2 (by rfl) ⟨25029, by rfl⟩) (B 50059 (by norm_num) ⟨25029, by rfl⟩ (by norm_num))
theorem R66749 : Reach 66749 := rs (se 3 (by rfl) ⟨12515, by rfl⟩) (B 25031 (by norm_num) ⟨12515, by rfl⟩ (by norm_num))
theorem R66753 : Reach 66753 := rs (se 2 (by rfl) ⟨25032, by rfl⟩) (B 50065 (by norm_num) ⟨25032, by rfl⟩ (by norm_num))
theorem R66757 : Reach 66757 := rs (se 4 (by rfl) ⟨6258, by rfl⟩) (B 12517 (by norm_num) ⟨6258, by rfl⟩ (by norm_num))
theorem R66761 : Reach 66761 := rs (se 2 (by rfl) ⟨25035, by rfl⟩) (B 50071 (by norm_num) ⟨25035, by rfl⟩ (by norm_num))
theorem R99533 : Reach 99533 := rs (se 3 (by rfl) ⟨18662, by rfl⟩) (B 37325 (by norm_num) ⟨18662, by rfl⟩ (by norm_num))
theorem R66765 : Reach 66765 := rs (se 3 (by rfl) ⟨12518, by rfl⟩) (B 25037 (by norm_num) ⟨12518, by rfl⟩ (by norm_num))
theorem R66769 : Reach 66769 := rs (se 2 (by rfl) ⟨25038, by rfl⟩) (B 50077 (by norm_num) ⟨25038, by rfl⟩ (by norm_num))
theorem R66773 : Reach 66773 := rs (se 7 (by rfl) ⟨782, by rfl⟩) (B 1565 (by norm_num) ⟨782, by rfl⟩ (by norm_num))
theorem R66777 : Reach 66777 := rs (se 2 (by rfl) ⟨25041, by rfl⟩) (B 50083 (by norm_num) ⟨25041, by rfl⟩ (by norm_num))
theorem R66781 : Reach 66781 := rs (se 3 (by rfl) ⟨12521, by rfl⟩) (B 25043 (by norm_num) ⟨12521, by rfl⟩ (by norm_num))
theorem R66785 : Reach 66785 := rs (se 2 (by rfl) ⟨25044, by rfl⟩) (B 50089 (by norm_num) ⟨25044, by rfl⟩ (by norm_num))
theorem R99557 : Reach 99557 := rs (se 4 (by rfl) ⟨9333, by rfl⟩) (B 18667 (by norm_num) ⟨9333, by rfl⟩ (by norm_num))
theorem R66789 : Reach 66789 := rs (se 4 (by rfl) ⟨6261, by rfl⟩) (B 12523 (by norm_num) ⟨6261, by rfl⟩ (by norm_num))
theorem R66793 : Reach 66793 := rs (se 2 (by rfl) ⟨25047, by rfl⟩) (B 50095 (by norm_num) ⟨25047, by rfl⟩ (by norm_num))
theorem R66797 : Reach 66797 := rs (se 3 (by rfl) ⟨12524, by rfl⟩) (B 25049 (by norm_num) ⟨12524, by rfl⟩ (by norm_num))
theorem R66801 : Reach 66801 := rs (se 2 (by rfl) ⟨25050, by rfl⟩) (B 50101 (by norm_num) ⟨25050, by rfl⟩ (by norm_num))
theorem R66805 : Reach 66805 := rs (se 5 (by rfl) ⟨3131, by rfl⟩) (B 6263 (by norm_num) ⟨3131, by rfl⟩ (by norm_num))
theorem R66809 : Reach 66809 := rs (se 2 (by rfl) ⟨25053, by rfl⟩) (B 50107 (by norm_num) ⟨25053, by rfl⟩ (by norm_num))
theorem R99581 : Reach 99581 := rs (se 3 (by rfl) ⟨18671, by rfl⟩) (B 37343 (by norm_num) ⟨18671, by rfl⟩ (by norm_num))
theorem R66813 : Reach 66813 := rs (se 3 (by rfl) ⟨12527, by rfl⟩) (B 25055 (by norm_num) ⟨12527, by rfl⟩ (by norm_num))
theorem R66817 : Reach 66817 := rs (se 2 (by rfl) ⟨25056, by rfl⟩) (B 50113 (by norm_num) ⟨25056, by rfl⟩ (by norm_num))
theorem R66821 : Reach 66821 := rs (se 4 (by rfl) ⟨6264, by rfl⟩) (B 12529 (by norm_num) ⟨6264, by rfl⟩ (by norm_num))
theorem R66825 : Reach 66825 := rs (se 2 (by rfl) ⟨25059, by rfl⟩) (B 50119 (by norm_num) ⟨25059, by rfl⟩ (by norm_num))
theorem R66829 : Reach 66829 := rs (se 3 (by rfl) ⟨12530, by rfl⟩) (B 25061 (by norm_num) ⟨12530, by rfl⟩ (by norm_num))
theorem R66833 : Reach 66833 := rs (se 2 (by rfl) ⟨25062, by rfl⟩) (B 50125 (by norm_num) ⟨25062, by rfl⟩ (by norm_num))
theorem R99605 : Reach 99605 := rs (se 6 (by rfl) ⟨2334, by rfl⟩) (B 4669 (by norm_num) ⟨2334, by rfl⟩ (by norm_num))
theorem R427285 : Reach 427285 := rs (se 6 (by rfl) ⟨10014, by rfl⟩) (B 20029 (by norm_num) ⟨10014, by rfl⟩ (by norm_num))
theorem R66837 : Reach 66837 := rs (se 6 (by rfl) ⟨1566, by rfl⟩) (B 3133 (by norm_num) ⟨1566, by rfl⟩ (by norm_num))
theorem R66841 : Reach 66841 := rs (se 2 (by rfl) ⟨25065, by rfl⟩) (B 50131 (by norm_num) ⟨25065, by rfl⟩ (by norm_num))
theorem R66845 : Reach 66845 := rs (se 3 (by rfl) ⟨12533, by rfl⟩) (B 25067 (by norm_num) ⟨12533, by rfl⟩ (by norm_num))
theorem R165149 : Reach 165149 := rs (se 3 (by rfl) ⟨30965, by rfl⟩) (B 61931 (by norm_num) ⟨30965, by rfl⟩ (by norm_num))
theorem R66849 : Reach 66849 := rs (se 2 (by rfl) ⟨25068, by rfl⟩) (B 50137 (by norm_num) ⟨25068, by rfl⟩ (by norm_num))
theorem R66853 : Reach 66853 := rs (se 4 (by rfl) ⟨6267, by rfl⟩) (B 12535 (by norm_num) ⟨6267, by rfl⟩ (by norm_num))
theorem R66857 : Reach 66857 := rs (se 2 (by rfl) ⟨25071, by rfl⟩) (B 50143 (by norm_num) ⟨25071, by rfl⟩ (by norm_num))
theorem R99629 : Reach 99629 := rs (se 3 (by rfl) ⟨18680, by rfl⟩) (B 37361 (by norm_num) ⟨18680, by rfl⟩ (by norm_num))
theorem R66861 : Reach 66861 := rs (se 3 (by rfl) ⟨12536, by rfl⟩) (B 25073 (by norm_num) ⟨12536, by rfl⟩ (by norm_num))
theorem R66865 : Reach 66865 := rs (se 2 (by rfl) ⟨25074, by rfl⟩) (B 50149 (by norm_num) ⟨25074, by rfl⟩ (by norm_num))
theorem R66869 : Reach 66869 := rs (se 5 (by rfl) ⟨3134, by rfl⟩) (B 6269 (by norm_num) ⟨3134, by rfl⟩ (by norm_num))
theorem R66873 : Reach 66873 := rs (se 2 (by rfl) ⟨25077, by rfl⟩) (B 50155 (by norm_num) ⟨25077, by rfl⟩ (by norm_num))
theorem R66877 : Reach 66877 := rs (se 3 (by rfl) ⟨12539, by rfl⟩) (B 25079 (by norm_num) ⟨12539, by rfl⟩ (by norm_num))
theorem R66881 : Reach 66881 := rs (se 2 (by rfl) ⟨25080, by rfl⟩) (B 50161 (by norm_num) ⟨25080, by rfl⟩ (by norm_num))
theorem R99653 : Reach 99653 := rs (se 4 (by rfl) ⟨9342, by rfl⟩) (B 18685 (by norm_num) ⟨9342, by rfl⟩ (by norm_num))
theorem R66885 : Reach 66885 := rs (se 4 (by rfl) ⟨6270, by rfl⟩) (B 12541 (by norm_num) ⟨6270, by rfl⟩ (by norm_num))
theorem R66889 : Reach 66889 := rs (se 2 (by rfl) ⟨25083, by rfl⟩) (B 50167 (by norm_num) ⟨25083, by rfl⟩ (by norm_num))
theorem R66893 : Reach 66893 := rs (se 3 (by rfl) ⟨12542, by rfl⟩) (B 25085 (by norm_num) ⟨12542, by rfl⟩ (by norm_num))
theorem R66897 : Reach 66897 := rs (se 2 (by rfl) ⟨25086, by rfl⟩) (B 50173 (by norm_num) ⟨25086, by rfl⟩ (by norm_num))
theorem R66901 : Reach 66901 := rs (se 12 (by rfl) ⟨24, by rfl⟩) (B 49 (by norm_num) ⟨24, by rfl⟩ (by norm_num))
theorem R66905 : Reach 66905 := rs (se 2 (by rfl) ⟨25089, by rfl⟩) (B 50179 (by norm_num) ⟨25089, by rfl⟩ (by norm_num))
theorem R99677 : Reach 99677 := rs (se 3 (by rfl) ⟨18689, by rfl⟩) (B 37379 (by norm_num) ⟨18689, by rfl⟩ (by norm_num))
theorem R66909 : Reach 66909 := rs (se 3 (by rfl) ⟨12545, by rfl⟩) (B 25091 (by norm_num) ⟨12545, by rfl⟩ (by norm_num))
theorem R66913 : Reach 66913 := rs (se 2 (by rfl) ⟨25092, by rfl⟩) (B 50185 (by norm_num) ⟨25092, by rfl⟩ (by norm_num))
theorem R66917 : Reach 66917 := rs (se 4 (by rfl) ⟨6273, by rfl⟩) (B 12547 (by norm_num) ⟨6273, by rfl⟩ (by norm_num))
theorem R66921 : Reach 66921 := rs (se 2 (by rfl) ⟨25095, by rfl⟩) (B 50191 (by norm_num) ⟨25095, by rfl⟩ (by norm_num))
theorem R66925 : Reach 66925 := rs (se 3 (by rfl) ⟨12548, by rfl⟩) (B 25097 (by norm_num) ⟨12548, by rfl⟩ (by norm_num))
theorem R66929 : Reach 66929 := rs (se 2 (by rfl) ⟨25098, by rfl⟩) (B 50197 (by norm_num) ⟨25098, by rfl⟩ (by norm_num))
theorem R296309 : Reach 296309 := rs (se 5 (by rfl) ⟨13889, by rfl⟩) (B 27779 (by norm_num) ⟨13889, by rfl⟩ (by norm_num))
theorem R99701 : Reach 99701 := rs (se 5 (by rfl) ⟨4673, by rfl⟩) (B 9347 (by norm_num) ⟨4673, by rfl⟩ (by norm_num))
theorem R66933 : Reach 66933 := rs (se 5 (by rfl) ⟨3137, by rfl⟩) (B 6275 (by norm_num) ⟨3137, by rfl⟩ (by norm_num))
theorem R66937 : Reach 66937 := rs (se 2 (by rfl) ⟨25101, by rfl⟩) (B 50203 (by norm_num) ⟨25101, by rfl⟩ (by norm_num))
theorem R66941 : Reach 66941 := rs (se 3 (by rfl) ⟨12551, by rfl⟩) (B 25103 (by norm_num) ⟨12551, by rfl⟩ (by norm_num))
theorem R66945 : Reach 66945 := rs (se 2 (by rfl) ⟨25104, by rfl⟩) (B 50209 (by norm_num) ⟨25104, by rfl⟩ (by norm_num))
theorem R66949 : Reach 66949 := rs (se 4 (by rfl) ⟨6276, by rfl⟩) (B 12553 (by norm_num) ⟨6276, by rfl⟩ (by norm_num))
theorem R66953 : Reach 66953 := rs (se 2 (by rfl) ⟨25107, by rfl⟩) (B 50215 (by norm_num) ⟨25107, by rfl⟩ (by norm_num))
theorem R99725 : Reach 99725 := rs (se 3 (by rfl) ⟨18698, by rfl⟩) (B 37397 (by norm_num) ⟨18698, by rfl⟩ (by norm_num))
theorem R66957 : Reach 66957 := rs (se 3 (by rfl) ⟨12554, by rfl⟩) (B 25109 (by norm_num) ⟨12554, by rfl⟩ (by norm_num))
theorem R66961 : Reach 66961 := rs (se 2 (by rfl) ⟨25110, by rfl⟩) (B 50221 (by norm_num) ⟨25110, by rfl⟩ (by norm_num))
theorem R66965 : Reach 66965 := rs (se 6 (by rfl) ⟨1569, by rfl⟩) (B 3139 (by norm_num) ⟨1569, by rfl⟩ (by norm_num))
theorem R66969 : Reach 66969 := rs (se 2 (by rfl) ⟨25113, by rfl⟩) (B 50227 (by norm_num) ⟨25113, by rfl⟩ (by norm_num))
theorem R66973 : Reach 66973 := rs (se 3 (by rfl) ⟨12557, by rfl⟩) (B 25115 (by norm_num) ⟨12557, by rfl⟩ (by norm_num))
theorem R66977 : Reach 66977 := rs (se 2 (by rfl) ⟨25116, by rfl⟩) (B 50233 (by norm_num) ⟨25116, by rfl⟩ (by norm_num))
theorem R99749 : Reach 99749 := rs (se 4 (by rfl) ⟨9351, by rfl⟩) (B 18703 (by norm_num) ⟨9351, by rfl⟩ (by norm_num))
theorem R66981 : Reach 66981 := rs (se 4 (by rfl) ⟨6279, by rfl⟩) (B 12559 (by norm_num) ⟨6279, by rfl⟩ (by norm_num))
theorem R66985 : Reach 66985 := rs (se 2 (by rfl) ⟨25119, by rfl⟩) (B 50239 (by norm_num) ⟨25119, by rfl⟩ (by norm_num))
theorem R66989 : Reach 66989 := rs (se 3 (by rfl) ⟨12560, by rfl⟩) (B 25121 (by norm_num) ⟨12560, by rfl⟩ (by norm_num))
theorem R66993 : Reach 66993 := rs (se 2 (by rfl) ⟨25122, by rfl⟩) (B 50245 (by norm_num) ⟨25122, by rfl⟩ (by norm_num))
theorem R66997 : Reach 66997 := rs (se 5 (by rfl) ⟨3140, by rfl⟩) (B 6281 (by norm_num) ⟨3140, by rfl⟩ (by norm_num))
theorem R67001 : Reach 67001 := rs (se 2 (by rfl) ⟨25125, by rfl⟩) (B 50251 (by norm_num) ⟨25125, by rfl⟩ (by norm_num))
theorem R99773 : Reach 99773 := rs (se 3 (by rfl) ⟨18707, by rfl⟩) (B 37415 (by norm_num) ⟨18707, by rfl⟩ (by norm_num))
theorem R67005 : Reach 67005 := rs (se 3 (by rfl) ⟨12563, by rfl⟩) (B 25127 (by norm_num) ⟨12563, by rfl⟩ (by norm_num))
theorem R67009 : Reach 67009 := rs (se 2 (by rfl) ⟨25128, by rfl⟩) (B 50257 (by norm_num) ⟨25128, by rfl⟩ (by norm_num))
theorem R67013 : Reach 67013 := rs (se 4 (by rfl) ⟨6282, by rfl⟩) (B 12565 (by norm_num) ⟨6282, by rfl⟩ (by norm_num))
theorem R67017 : Reach 67017 := rs (se 2 (by rfl) ⟨25131, by rfl⟩) (B 50263 (by norm_num) ⟨25131, by rfl⟩ (by norm_num))
theorem R67021 : Reach 67021 := rs (se 3 (by rfl) ⟨12566, by rfl⟩) (B 25133 (by norm_num) ⟨12566, by rfl⟩ (by norm_num))
theorem R67025 : Reach 67025 := rs (se 2 (by rfl) ⟨25134, by rfl⟩) (B 50269 (by norm_num) ⟨25134, by rfl⟩ (by norm_num))
theorem R99797 : Reach 99797 := rs (se 7 (by rfl) ⟨1169, by rfl⟩) (B 2339 (by norm_num) ⟨1169, by rfl⟩ (by norm_num))
theorem R67029 : Reach 67029 := rs (se 7 (by rfl) ⟨785, by rfl⟩) (B 1571 (by norm_num) ⟨785, by rfl⟩ (by norm_num))
theorem R67033 : Reach 67033 := rs (se 2 (by rfl) ⟨25137, by rfl⟩) (B 50275 (by norm_num) ⟨25137, by rfl⟩ (by norm_num))
theorem R165341 : Reach 165341 := rs (se 3 (by rfl) ⟨31001, by rfl⟩) (B 62003 (by norm_num) ⟨31001, by rfl⟩ (by norm_num))
theorem R99805 : Reach 99805 := rs (se 3 (by rfl) ⟨18713, by rfl⟩) (B 37427 (by norm_num) ⟨18713, by rfl⟩ (by norm_num))
theorem R67037 : Reach 67037 := rs (se 3 (by rfl) ⟨12569, by rfl⟩) (B 25139 (by norm_num) ⟨12569, by rfl⟩ (by norm_num))
theorem R67041 : Reach 67041 := rs (se 2 (by rfl) ⟨25140, by rfl⟩) (B 50281 (by norm_num) ⟨25140, by rfl⟩ (by norm_num))
theorem R67045 : Reach 67045 := rs (se 4 (by rfl) ⟨6285, by rfl⟩) (B 12571 (by norm_num) ⟨6285, by rfl⟩ (by norm_num))
theorem R67049 : Reach 67049 := rs (se 2 (by rfl) ⟨25143, by rfl⟩) (B 50287 (by norm_num) ⟨25143, by rfl⟩ (by norm_num))
theorem R99821 : Reach 99821 := rs (se 3 (by rfl) ⟨18716, by rfl⟩) (B 37433 (by norm_num) ⟨18716, by rfl⟩ (by norm_num))
theorem R67053 : Reach 67053 := rs (se 3 (by rfl) ⟨12572, by rfl⟩) (B 25145 (by norm_num) ⟨12572, by rfl⟩ (by norm_num))
theorem R67057 : Reach 67057 := rs (se 2 (by rfl) ⟨25146, by rfl⟩) (B 50293 (by norm_num) ⟨25146, by rfl⟩ (by norm_num))
theorem R67061 : Reach 67061 := rs (se 5 (by rfl) ⟨3143, by rfl⟩) (B 6287 (by norm_num) ⟨3143, by rfl⟩ (by norm_num))
theorem R67065 : Reach 67065 := rs (se 2 (by rfl) ⟨25149, by rfl⟩) (B 50299 (by norm_num) ⟨25149, by rfl⟩ (by norm_num))
theorem R67069 : Reach 67069 := rs (se 3 (by rfl) ⟨12575, by rfl⟩) (B 25151 (by norm_num) ⟨12575, by rfl⟩ (by norm_num))
theorem R67073 : Reach 67073 := rs (se 2 (by rfl) ⟨25152, by rfl⟩) (B 50305 (by norm_num) ⟨25152, by rfl⟩ (by norm_num))
theorem R99845 : Reach 99845 := rs (se 4 (by rfl) ⟨9360, by rfl⟩) (B 18721 (by norm_num) ⟨9360, by rfl⟩ (by norm_num))
theorem R67077 : Reach 67077 := rs (se 4 (by rfl) ⟨6288, by rfl⟩) (B 12577 (by norm_num) ⟨6288, by rfl⟩ (by norm_num))
theorem R67081 : Reach 67081 := rs (se 2 (by rfl) ⟨25155, by rfl⟩) (B 50311 (by norm_num) ⟨25155, by rfl⟩ (by norm_num))
theorem R67085 : Reach 67085 := rs (se 3 (by rfl) ⟨12578, by rfl⟩) (B 25157 (by norm_num) ⟨12578, by rfl⟩ (by norm_num))
theorem R67089 : Reach 67089 := rs (se 2 (by rfl) ⟨25158, by rfl⟩) (B 50317 (by norm_num) ⟨25158, by rfl⟩ (by norm_num))
theorem R67093 : Reach 67093 := rs (se 6 (by rfl) ⟨1572, by rfl⟩) (B 3145 (by norm_num) ⟨1572, by rfl⟩ (by norm_num))
theorem R67097 : Reach 67097 := rs (se 2 (by rfl) ⟨25161, by rfl⟩) (B 50323 (by norm_num) ⟨25161, by rfl⟩ (by norm_num))
theorem R99869 : Reach 99869 := rs (se 3 (by rfl) ⟨18725, by rfl⟩) (B 37451 (by norm_num) ⟨18725, by rfl⟩ (by norm_num))
theorem R67101 : Reach 67101 := rs (se 3 (by rfl) ⟨12581, by rfl⟩) (B 25163 (by norm_num) ⟨12581, by rfl⟩ (by norm_num))
theorem R67105 : Reach 67105 := rs (se 2 (by rfl) ⟨25164, by rfl⟩) (B 50329 (by norm_num) ⟨25164, by rfl⟩ (by norm_num))
theorem R67109 : Reach 67109 := rs (se 4 (by rfl) ⟨6291, by rfl⟩) (B 12583 (by norm_num) ⟨6291, by rfl⟩ (by norm_num))
theorem R67113 : Reach 67113 := rs (se 2 (by rfl) ⟨25167, by rfl⟩) (B 50335 (by norm_num) ⟨25167, by rfl⟩ (by norm_num))
theorem R67117 : Reach 67117 := rs (se 3 (by rfl) ⟨12584, by rfl⟩) (B 25169 (by norm_num) ⟨12584, by rfl⟩ (by norm_num))
theorem R67121 : Reach 67121 := rs (se 2 (by rfl) ⟨25170, by rfl⟩) (B 50341 (by norm_num) ⟨25170, by rfl⟩ (by norm_num))
theorem R99893 : Reach 99893 := rs (se 5 (by rfl) ⟨4682, by rfl⟩) (B 9365 (by norm_num) ⟨4682, by rfl⟩ (by norm_num))
theorem R99917 : Reach 99917 := rs (se 3 (by rfl) ⟨18734, by rfl⟩) (B 37469 (by norm_num) ⟨18734, by rfl⟩ (by norm_num))
theorem R99941 : Reach 99941 := rs (se 4 (by rfl) ⟨9369, by rfl⟩) (B 18739 (by norm_num) ⟨9369, by rfl⟩ (by norm_num))
theorem R67181 : Reach 67181 := rs (se 3 (by rfl) ⟨12596, by rfl⟩) (B 25193 (by norm_num) ⟨12596, by rfl⟩ (by norm_num))
theorem R99965 : Reach 99965 := rs (se 3 (by rfl) ⟨18743, by rfl⟩) (B 37487 (by norm_num) ⟨18743, by rfl⟩ (by norm_num))
theorem R99989 : Reach 99989 := rs (se 6 (by rfl) ⟨2343, by rfl⟩) (B 4687 (by norm_num) ⟨2343, by rfl⟩ (by norm_num))
theorem R100013 : Reach 100013 := rs (se 3 (by rfl) ⟨18752, by rfl⟩) (B 37505 (by norm_num) ⟨18752, by rfl⟩ (by norm_num))
theorem R100037 : Reach 100037 := rs (se 4 (by rfl) ⟨9378, by rfl⟩) (B 18757 (by norm_num) ⟨9378, by rfl⟩ (by norm_num))
theorem R100061 : Reach 100061 := rs (se 3 (by rfl) ⟨18761, by rfl⟩) (B 37523 (by norm_num) ⟨18761, by rfl⟩ (by norm_num))
theorem R100085 : Reach 100085 := rs (se 5 (by rfl) ⟨4691, by rfl⟩) (B 9383 (by norm_num) ⟨4691, by rfl⟩ (by norm_num))
theorem R100109 : Reach 100109 := rs (se 3 (by rfl) ⟨18770, by rfl⟩) (B 37541 (by norm_num) ⟨18770, by rfl⟩ (by norm_num))
theorem R100133 : Reach 100133 := rs (se 4 (by rfl) ⟨9387, by rfl⟩) (B 18775 (by norm_num) ⟨9387, by rfl⟩ (by norm_num))
theorem R165685 : Reach 165685 := rs (se 5 (by rfl) ⟨7766, by rfl⟩) (B 15533 (by norm_num) ⟨7766, by rfl⟩ (by norm_num))
theorem R100157 : Reach 100157 := rs (se 3 (by rfl) ⟨18779, by rfl⟩) (B 37559 (by norm_num) ⟨18779, by rfl⟩ (by norm_num))
theorem R100181 : Reach 100181 := rs (se 9 (by rfl) ⟨293, by rfl⟩) (B 587 (by norm_num) ⟨293, by rfl⟩ (by norm_num))
theorem R100205 : Reach 100205 := rs (se 3 (by rfl) ⟨18788, by rfl⟩) (B 37577 (by norm_num) ⟨18788, by rfl⟩ (by norm_num))
theorem R100229 : Reach 100229 := rs (se 4 (by rfl) ⟨9396, by rfl⟩) (B 18793 (by norm_num) ⟨9396, by rfl⟩ (by norm_num))
theorem R100253 : Reach 100253 := rs (se 3 (by rfl) ⟨18797, by rfl⟩) (B 37595 (by norm_num) ⟨18797, by rfl⟩ (by norm_num))
theorem R165797 : Reach 165797 := rs (se 4 (by rfl) ⟨15543, by rfl⟩) (B 31087 (by norm_num) ⟨15543, by rfl⟩ (by norm_num))
theorem R100277 : Reach 100277 := rs (se 5 (by rfl) ⟨4700, by rfl⟩) (B 9401 (by norm_num) ⟨4700, by rfl⟩ (by norm_num))
theorem R329669 : Reach 329669 := rs (se 4 (by rfl) ⟨30906, by rfl⟩) (B 61813 (by norm_num) ⟨30906, by rfl⟩ (by norm_num))
theorem R100301 : Reach 100301 := rs (se 3 (by rfl) ⟨18806, by rfl⟩) (B 37613 (by norm_num) ⟨18806, by rfl⟩ (by norm_num))
theorem R755669 : Reach 755669 := rs (se 7 (by rfl) ⟨8855, by rfl⟩) (B 17711 (by norm_num) ⟨8855, by rfl⟩ (by norm_num))
theorem R65529 : Reach 65529 := rs (se 2 (by rfl) ⟨24573, by rfl⟩) (B 49147 (by norm_num) ⟨24573, by rfl⟩ (by norm_num))
theorem R100325 : Reach 100325 := rs (se 4 (by rfl) ⟨9405, by rfl⟩) (B 18811 (by norm_num) ⟨9405, by rfl⟩ (by norm_num))
theorem R100349 : Reach 100349 := rs (se 3 (by rfl) ⟨18815, by rfl⟩) (B 37631 (by norm_num) ⟨18815, by rfl⟩ (by norm_num))
theorem R67601 : Reach 67601 := rs (se 2 (by rfl) ⟨25350, by rfl⟩) (B 50701 (by norm_num) ⟨25350, by rfl⟩ (by norm_num))
theorem R100373 : Reach 100373 := rs (se 6 (by rfl) ⟨2352, by rfl⟩) (B 4705 (by norm_num) ⟨2352, by rfl⟩ (by norm_num))
theorem R100397 : Reach 100397 := rs (se 3 (by rfl) ⟨18824, by rfl⟩) (B 37649 (by norm_num) ⟨18824, by rfl⟩ (by norm_num))
theorem R100421 : Reach 100421 := rs (se 4 (by rfl) ⟨9414, by rfl⟩) (B 18829 (by norm_num) ⟨9414, by rfl⟩ (by norm_num))
theorem R100445 : Reach 100445 := rs (se 3 (by rfl) ⟨18833, by rfl⟩) (B 37667 (by norm_num) ⟨18833, by rfl⟩ (by norm_num))
theorem R165989 : Reach 165989 := rs (se 4 (by rfl) ⟨15561, by rfl⟩) (B 31123 (by norm_num) ⟨15561, by rfl⟩ (by norm_num))
theorem R100469 : Reach 100469 := rs (se 5 (by rfl) ⟨4709, by rfl⟩) (B 9419 (by norm_num) ⟨4709, by rfl⟩ (by norm_num))
theorem R100493 : Reach 100493 := rs (se 3 (by rfl) ⟨18842, by rfl⟩) (B 37685 (by norm_num) ⟨18842, by rfl⟩ (by norm_num))
theorem R100517 : Reach 100517 := rs (se 4 (by rfl) ⟨9423, by rfl⟩) (B 18847 (by norm_num) ⟨9423, by rfl⟩ (by norm_num))
theorem R362677 : Reach 362677 := rs (se 5 (by rfl) ⟨17000, by rfl⟩) (B 34001 (by norm_num) ⟨17000, by rfl⟩ (by norm_num))
theorem R100541 : Reach 100541 := rs (se 3 (by rfl) ⟨18851, by rfl⟩) (B 37703 (by norm_num) ⟨18851, by rfl⟩ (by norm_num))
theorem R100565 : Reach 100565 := rs (se 7 (by rfl) ⟨1178, by rfl⟩) (B 2357 (by norm_num) ⟨1178, by rfl⟩ (by norm_num))
theorem R100589 : Reach 100589 := rs (se 3 (by rfl) ⟨18860, by rfl⟩) (B 37721 (by norm_num) ⟨18860, by rfl⟩ (by norm_num))
theorem R166141 : Reach 166141 := rs (se 3 (by rfl) ⟨31151, by rfl⟩) (B 62303 (by norm_num) ⟨31151, by rfl⟩ (by norm_num))
theorem R133373 : Reach 133373 := rs (se 3 (by rfl) ⟨25007, by rfl⟩) (B 50015 (by norm_num) ⟨25007, by rfl⟩ (by norm_num))
theorem R100613 : Reach 100613 := rs (se 4 (by rfl) ⟨9432, by rfl⟩) (B 18865 (by norm_num) ⟨9432, by rfl⟩ (by norm_num))
theorem R100637 : Reach 100637 := rs (se 3 (by rfl) ⟨18869, by rfl⟩) (B 37739 (by norm_num) ⟨18869, by rfl⟩ (by norm_num))
theorem R100661 : Reach 100661 := rs (se 5 (by rfl) ⟨4718, by rfl⟩) (B 9437 (by norm_num) ⟨4718, by rfl⟩ (by norm_num))
theorem R100685 : Reach 100685 := rs (se 3 (by rfl) ⟨18878, by rfl⟩) (B 37757 (by norm_num) ⟨18878, by rfl⟩ (by norm_num))
theorem R166333 : Reach 166333 := rs (se 3 (by rfl) ⟨31187, by rfl⟩) (B 62375 (by norm_num) ⟨31187, by rfl⟩ (by norm_num))
theorem R68045 : Reach 68045 := rs (se 3 (by rfl) ⟨12758, by rfl⟩) (B 25517 (by norm_num) ⟨12758, by rfl⟩ (by norm_num))
theorem R395765 : Reach 395765 := rs (se 5 (by rfl) ⟨18551, by rfl⟩) (B 37103 (by norm_num) ⟨18551, by rfl⟩ (by norm_num))
theorem R166445 : Reach 166445 := rs (se 3 (by rfl) ⟨31208, by rfl⟩) (B 62417 (by norm_num) ⟨31208, by rfl⟩ (by norm_num))
theorem R199253 : Reach 199253 := rs (se 8 (by rfl) ⟨1167, by rfl⟩) (B 2335 (by norm_num) ⟨1167, by rfl⟩ (by norm_num))
theorem R494261 : Reach 494261 := rs (se 5 (by rfl) ⟨23168, by rfl⟩) (B 46337 (by norm_num) ⟨23168, by rfl⟩ (by norm_num))
theorem R68293 : Reach 68293 := rs (se 4 (by rfl) ⟨6402, by rfl⟩) (B 12805 (by norm_num) ⟨6402, by rfl⟩ (by norm_num))
theorem R166637 : Reach 166637 := rs (se 3 (by rfl) ⟨31244, by rfl⟩) (B 62489 (by norm_num) ⟨31244, by rfl⟩ (by norm_num))
theorem R330725 : Reach 330725 := rs (se 4 (by rfl) ⟨31005, by rfl⟩) (B 62011 (by norm_num) ⟨31005, by rfl⟩ (by norm_num))
theorem R166981 : Reach 166981 := rs (se 4 (by rfl) ⟨15654, by rfl⟩) (B 31309 (by norm_num) ⟨15654, by rfl⟩ (by norm_num))
theorem R68737 : Reach 68737 := rs (se 2 (by rfl) ⟨25776, by rfl⟩) (B 51553 (by norm_num) ⟨25776, by rfl⟩ (by norm_num))
theorem R494741 : Reach 494741 := rs (se 6 (by rfl) ⟨11595, by rfl⟩) (B 23191 (by norm_num) ⟨11595, by rfl⟩ (by norm_num))
theorem R167093 : Reach 167093 := rs (se 5 (by rfl) ⟨7832, by rfl⟩) (B 15665 (by norm_num) ⟨7832, by rfl⟩ (by norm_num))
theorem R68797 : Reach 68797 := rs (se 3 (by rfl) ⟨12899, by rfl⟩) (B 25799 (by norm_num) ⟨12899, by rfl⟩ (by norm_num))
theorem R330965 : Reach 330965 := rs (se 7 (by rfl) ⟨3878, by rfl⟩) (B 7757 (by norm_num) ⟨3878, by rfl⟩ (by norm_num))
theorem R101645 : Reach 101645 := rs (se 3 (by rfl) ⟨19058, by rfl⟩) (B 38117 (by norm_num) ⟨19058, by rfl⟩ (by norm_num))
theorem R101741 : Reach 101741 := rs (se 3 (by rfl) ⟨19076, by rfl⟩) (B 38153 (by norm_num) ⟨19076, by rfl⟩ (by norm_num))
theorem R167285 : Reach 167285 := rs (se 5 (by rfl) ⟨7841, by rfl⟩) (B 15683 (by norm_num) ⟨7841, by rfl⟩ (by norm_num))
theorem R101773 : Reach 101773 := rs (se 3 (by rfl) ⟨19082, by rfl⟩) (B 38165 (by norm_num) ⟨19082, by rfl⟩ (by norm_num))
theorem R69113 : Reach 69113 := rs (se 2 (by rfl) ⟨25917, by rfl⟩) (B 51835 (by norm_num) ⟨25917, by rfl⟩ (by norm_num))
theorem R167629 : Reach 167629 := rs (se 3 (by rfl) ⟨31430, by rfl⟩) (B 62861 (by norm_num) ⟨31430, by rfl⟩ (by norm_num))
theorem R167741 : Reach 167741 := rs (se 3 (by rfl) ⟨31451, by rfl⟩) (B 62903 (by norm_num) ⟨31451, by rfl⟩ (by norm_num))
theorem R69557 : Reach 69557 := rs (se 5 (by rfl) ⟨3260, by rfl⟩) (B 6521 (by norm_num) ⟨3260, by rfl⟩ (by norm_num))
theorem R135125 : Reach 135125 := rs (se 7 (by rfl) ⟨1583, by rfl⟩) (B 3167 (by norm_num) ⟨1583, by rfl⟩ (by norm_num))
theorem R69617 : Reach 69617 := rs (se 2 (by rfl) ⟨26106, by rfl⟩) (B 52213 (by norm_num) ⟨26106, by rfl⟩ (by norm_num))
theorem R167933 : Reach 167933 := rs (se 3 (by rfl) ⟨31487, by rfl⟩) (B 62975 (by norm_num) ⟨31487, by rfl⟩ (by norm_num))
theorem R167989 : Reach 167989 := rs (se 5 (by rfl) ⟨7874, by rfl⟩) (B 15749 (by norm_num) ⟨7874, by rfl⟩ (by norm_num))
theorem R135245 : Reach 135245 := rs (se 3 (by rfl) ⟨25358, by rfl⟩) (B 50717 (by norm_num) ⟨25358, by rfl⟩ (by norm_num))
theorem R69745 : Reach 69745 := rs (se 2 (by rfl) ⟨26154, by rfl⟩) (B 52309 (by norm_num) ⟨26154, by rfl⟩ (by norm_num))
theorem R364661 : Reach 364661 := rs (se 5 (by rfl) ⟨17093, by rfl⟩) (B 34187 (by norm_num) ⟨17093, by rfl⟩ (by norm_num))
theorem R102565 : Reach 102565 := rs (se 4 (by rfl) ⟨9615, by rfl⟩) (B 19231 (by norm_num) ⟨9615, by rfl⟩ (by norm_num))
theorem R135389 : Reach 135389 := rs (se 3 (by rfl) ⟨25385, by rfl⟩) (B 50771 (by norm_num) ⟨25385, by rfl⟩ (by norm_num))
theorem R168277 : Reach 168277 := rs (se 10 (by rfl) ⟨246, by rfl⟩) (B 493 (by norm_num) ⟨246, by rfl⟩ (by norm_num))
theorem R168389 : Reach 168389 := rs (se 4 (by rfl) ⟨15786, by rfl⟩) (B 31573 (by norm_num) ⟨15786, by rfl⟩ (by norm_num))
theorem R332261 : Reach 332261 := rs (se 4 (by rfl) ⟨31149, by rfl⟩) (B 62299 (by norm_num) ⟨31149, by rfl⟩ (by norm_num))
theorem R70189 : Reach 70189 := rs (se 3 (by rfl) ⟨13160, by rfl⟩) (B 26321 (by norm_num) ⟨13160, by rfl⟩ (by norm_num))
theorem R135749 : Reach 135749 := rs (se 4 (by rfl) ⟨12726, by rfl⟩) (B 25453 (by norm_num) ⟨12726, by rfl⟩ (by norm_num))
theorem R168581 : Reach 168581 := rs (se 4 (by rfl) ⟨15804, by rfl⟩) (B 31609 (by norm_num) ⟨15804, by rfl⟩ (by norm_num))
theorem R70309 : Reach 70309 := rs (se 4 (by rfl) ⟨6591, by rfl⟩) (B 13183 (by norm_num) ⟨6591, by rfl⟩ (by norm_num))
theorem R70417 : Reach 70417 := rs (se 2 (by rfl) ⟨26406, by rfl⟩) (B 52813 (by norm_num) ⟨26406, by rfl⟩ (by norm_num))
theorem R136037 : Reach 136037 := rs (se 4 (by rfl) ⟨12753, by rfl⟩) (B 25507 (by norm_num) ⟨12753, by rfl⟩ (by norm_num))
theorem R103285 : Reach 103285 := rs (se 5 (by rfl) ⟨4841, by rfl⟩) (B 9683 (by norm_num) ⟨4841, by rfl⟩ (by norm_num))
theorem R1217429 : Reach 1217429 := rs (se 6 (by rfl) ⟨28533, by rfl⟩) (B 57067 (by norm_num) ⟨28533, by rfl⟩ (by norm_num))
theorem R70561 : Reach 70561 := rs (se 2 (by rfl) ⟨26460, by rfl⟩) (B 52921 (by norm_num) ⟨26460, by rfl⟩ (by norm_num))
theorem R70565 : Reach 70565 := rs (se 4 (by rfl) ⟨6615, by rfl⟩) (B 13231 (by norm_num) ⟨6615, by rfl⟩ (by norm_num))
theorem R1151957 : Reach 1151957 := rs (se 7 (by rfl) ⟨13499, by rfl⟩) (B 26999 (by norm_num) ⟨13499, by rfl⟩ (by norm_num))
theorem R71041 : Reach 71041 := rs (se 2 (by rfl) ⟨26640, by rfl⟩) (B 53281 (by norm_num) ⟨26640, by rfl⟩ (by norm_num))
theorem R71077 : Reach 71077 := rs (se 4 (by rfl) ⟨6663, by rfl⟩) (B 13327 (by norm_num) ⟨6663, by rfl⟩ (by norm_num))
theorem R136637 : Reach 136637 := rs (se 3 (by rfl) ⟨25619, by rfl⟩) (B 51239 (by norm_num) ⟨25619, by rfl⟩ (by norm_num))
theorem R71113 : Reach 71113 := rs (se 2 (by rfl) ⟨26667, by rfl⟩) (B 53335 (by norm_num) ⟨26667, by rfl⟩ (by norm_num))
theorem R267733 : Reach 267733 := rs (se 7 (by rfl) ⟨3137, by rfl⟩) (B 6275 (by norm_num) ⟨3137, by rfl⟩ (by norm_num))
theorem R71129 : Reach 71129 := rs (se 2 (by rfl) ⟨26673, by rfl⟩) (B 53347 (by norm_num) ⟨26673, by rfl⟩ (by norm_num))
theorem R71149 : Reach 71149 := rs (se 3 (by rfl) ⟨13340, by rfl⟩) (B 26681 (by norm_num) ⟨13340, by rfl⟩ (by norm_num))
theorem R71185 : Reach 71185 := rs (se 2 (by rfl) ⟨26694, by rfl⟩) (B 53389 (by norm_num) ⟨26694, by rfl⟩ (by norm_num))
theorem R267797 : Reach 267797 := rs (se 6 (by rfl) ⟨6276, by rfl⟩) (B 12553 (by norm_num) ⟨6276, by rfl⟩ (by norm_num))
theorem R71221 : Reach 71221 := rs (se 5 (by rfl) ⟨3338, by rfl⟩) (B 6677 (by norm_num) ⟨3338, by rfl⟩ (by norm_num))
theorem R103997 : Reach 103997 := rs (se 3 (by rfl) ⟨19499, by rfl⟩) (B 38999 (by norm_num) ⟨19499, by rfl⟩ (by norm_num))
theorem R71257 : Reach 71257 := rs (se 2 (by rfl) ⟨26721, by rfl⟩) (B 53443 (by norm_num) ⟨26721, by rfl⟩ (by norm_num))
theorem R169573 : Reach 169573 := rs (se 4 (by rfl) ⟨15897, by rfl⟩) (B 31795 (by norm_num) ⟨15897, by rfl⟩ (by norm_num))
theorem R71293 : Reach 71293 := rs (se 3 (by rfl) ⟨13367, by rfl⟩) (B 26735 (by norm_num) ⟨13367, by rfl⟩ (by norm_num))
theorem R71317 : Reach 71317 := rs (se 6 (by rfl) ⟨1671, by rfl⟩) (B 3343 (by norm_num) ⟨1671, by rfl⟩ (by norm_num))
theorem R71329 : Reach 71329 := rs (se 2 (by rfl) ⟨26748, by rfl⟩) (B 53497 (by norm_num) ⟨26748, by rfl⟩ (by norm_num))
theorem R202405 : Reach 202405 := rs (se 4 (by rfl) ⟨18975, by rfl⟩) (B 37951 (by norm_num) ⟨18975, by rfl⟩ (by norm_num))
theorem R136885 : Reach 136885 := rs (se 5 (by rfl) ⟨6416, by rfl⟩) (B 12833 (by norm_num) ⟨6416, by rfl⟩ (by norm_num))
theorem R71365 : Reach 71365 := rs (se 4 (by rfl) ⟨6690, by rfl⟩) (B 13381 (by norm_num) ⟨6690, by rfl⟩ (by norm_num))
theorem R169685 : Reach 169685 := rs (se 7 (by rfl) ⟨1988, by rfl⟩) (B 3977 (by norm_num) ⟨1988, by rfl⟩ (by norm_num))
theorem R71401 : Reach 71401 := rs (se 2 (by rfl) ⟨26775, by rfl⟩) (B 53551 (by norm_num) ⟨26775, by rfl⟩ (by norm_num))
theorem R333557 : Reach 333557 := rs (se 5 (by rfl) ⟨15635, by rfl⟩) (B 31271 (by norm_num) ⟨15635, by rfl⟩ (by norm_num))
theorem R71425 : Reach 71425 := rs (se 2 (by rfl) ⟨26784, by rfl⟩) (B 53569 (by norm_num) ⟨26784, by rfl⟩ (by norm_num))
theorem R71437 : Reach 71437 := rs (se 3 (by rfl) ⟨13394, by rfl⟩) (B 26789 (by norm_num) ⟨13394, by rfl⟩ (by norm_num))
theorem R71473 : Reach 71473 := rs (se 2 (by rfl) ⟨26802, by rfl⟩) (B 53605 (by norm_num) ⟨26802, by rfl⟩ (by norm_num))
theorem R71509 : Reach 71509 := rs (se 9 (by rfl) ⟨209, by rfl⟩) (B 419 (by norm_num) ⟨209, by rfl⟩ (by norm_num))
theorem R71545 : Reach 71545 := rs (se 2 (by rfl) ⟨26829, by rfl⟩) (B 53659 (by norm_num) ⟨26829, by rfl⟩ (by norm_num))
theorem R169877 : Reach 169877 := rs (se 6 (by rfl) ⟨3981, by rfl⟩) (B 7963 (by norm_num) ⟨3981, by rfl⟩ (by norm_num))
theorem R71581 : Reach 71581 := rs (se 3 (by rfl) ⟨13421, by rfl⟩) (B 26843 (by norm_num) ⟨13421, by rfl⟩ (by norm_num))
theorem R71617 : Reach 71617 := rs (se 2 (by rfl) ⟨26856, by rfl⟩) (B 53713 (by norm_num) ⟨26856, by rfl⟩ (by norm_num))
theorem R71653 : Reach 71653 := rs (se 4 (by rfl) ⟨6717, by rfl⟩) (B 13435 (by norm_num) ⟨6717, by rfl⟩ (by norm_num))
theorem R71689 : Reach 71689 := rs (se 2 (by rfl) ⟨26883, by rfl⟩) (B 53767 (by norm_num) ⟨26883, by rfl⟩ (by norm_num))
theorem R71725 : Reach 71725 := rs (se 3 (by rfl) ⟨13448, by rfl⟩) (B 26897 (by norm_num) ⟨13448, by rfl⟩ (by norm_num))
theorem R71761 : Reach 71761 := rs (se 2 (by rfl) ⟨26910, by rfl⟩) (B 53821 (by norm_num) ⟨26910, by rfl⟩ (by norm_num))
theorem R71797 : Reach 71797 := rs (se 5 (by rfl) ⟨3365, by rfl⟩) (B 6731 (by norm_num) ⟨3365, by rfl⟩ (by norm_num))
theorem R71833 : Reach 71833 := rs (se 2 (by rfl) ⟨26937, by rfl⟩) (B 53875 (by norm_num) ⟨26937, by rfl⟩ (by norm_num))
theorem R137389 : Reach 137389 := rs (se 3 (by rfl) ⟨25760, by rfl⟩) (B 51521 (by norm_num) ⟨25760, by rfl⟩ (by norm_num))
theorem R71869 : Reach 71869 := rs (se 3 (by rfl) ⟨13475, by rfl⟩) (B 26951 (by norm_num) ⟨13475, by rfl⟩ (by norm_num))
theorem R104669 : Reach 104669 := rs (se 3 (by rfl) ⟨19625, by rfl⟩) (B 39251 (by norm_num) ⟨19625, by rfl⟩ (by norm_num))
theorem R71905 : Reach 71905 := rs (se 2 (by rfl) ⟨26964, by rfl⟩) (B 53929 (by norm_num) ⟨26964, by rfl⟩ (by norm_num))
theorem R202981 : Reach 202981 := rs (se 4 (by rfl) ⟨19029, by rfl⟩) (B 38059 (by norm_num) ⟨19029, by rfl⟩ (by norm_num))
theorem R71941 : Reach 71941 := rs (se 4 (by rfl) ⟨6744, by rfl⟩) (B 13489 (by norm_num) ⟨6744, by rfl⟩ (by norm_num))
theorem R366869 : Reach 366869 := rs (se 6 (by rfl) ⟨8598, by rfl⟩) (B 17197 (by norm_num) ⟨8598, by rfl⟩ (by norm_num))
theorem R71977 : Reach 71977 := rs (se 2 (by rfl) ⟨26991, by rfl⟩) (B 53983 (by norm_num) ⟨26991, by rfl⟩ (by norm_num))
theorem R72013 : Reach 72013 := rs (se 3 (by rfl) ⟨13502, by rfl⟩) (B 27005 (by norm_num) ⟨13502, by rfl⟩ (by norm_num))
theorem R72049 : Reach 72049 := rs (se 2 (by rfl) ⟨27018, by rfl⟩) (B 54037 (by norm_num) ⟨27018, by rfl⟩ (by norm_num))
theorem R72085 : Reach 72085 := rs (se 6 (by rfl) ⟨1689, by rfl⟩) (B 3379 (by norm_num) ⟨1689, by rfl⟩ (by norm_num))
theorem R72121 : Reach 72121 := rs (se 2 (by rfl) ⟨27045, by rfl⟩) (B 54091 (by norm_num) ⟨27045, by rfl⟩ (by norm_num))
theorem R72157 : Reach 72157 := rs (se 3 (by rfl) ⟨13529, by rfl⟩) (B 27059 (by norm_num) ⟨13529, by rfl⟩ (by norm_num))
theorem R72193 : Reach 72193 := rs (se 2 (by rfl) ⟨27072, by rfl⟩) (B 54145 (by norm_num) ⟨27072, by rfl⟩ (by norm_num))
theorem R72229 : Reach 72229 := rs (se 4 (by rfl) ⟨6771, by rfl⟩) (B 13543 (by norm_num) ⟨6771, by rfl⟩ (by norm_num))
theorem R72265 : Reach 72265 := rs (se 2 (by rfl) ⟨27099, by rfl⟩) (B 54199 (by norm_num) ⟨27099, by rfl⟩ (by norm_num))
theorem R72301 : Reach 72301 := rs (se 3 (by rfl) ⟨13556, by rfl⟩) (B 27113 (by norm_num) ⟨13556, by rfl⟩ (by norm_num))
theorem R203381 : Reach 203381 := rs (se 5 (by rfl) ⟨9533, by rfl⟩) (B 19067 (by norm_num) ⟨9533, by rfl⟩ (by norm_num))
theorem R72325 : Reach 72325 := rs (se 4 (by rfl) ⟨6780, by rfl⟩) (B 13561 (by norm_num) ⟨6780, by rfl⟩ (by norm_num))
theorem R72337 : Reach 72337 := rs (se 2 (by rfl) ⟨27126, by rfl⟩) (B 54253 (by norm_num) ⟨27126, by rfl⟩ (by norm_num))
theorem R72373 : Reach 72373 := rs (se 5 (by rfl) ⟨3392, by rfl⟩) (B 6785 (by norm_num) ⟨3392, by rfl⟩ (by norm_num))
theorem R137933 : Reach 137933 := rs (se 3 (by rfl) ⟨25862, by rfl⟩) (B 51725 (by norm_num) ⟨25862, by rfl⟩ (by norm_num))
theorem R72409 : Reach 72409 := rs (se 2 (by rfl) ⟨27153, by rfl⟩) (B 54307 (by norm_num) ⟨27153, by rfl⟩ (by norm_num))
theorem R105181 : Reach 105181 := rs (se 3 (by rfl) ⟨19721, by rfl⟩) (B 39443 (by norm_num) ⟨19721, by rfl⟩ (by norm_num))
theorem R170741 : Reach 170741 := rs (se 5 (by rfl) ⟨8003, by rfl⟩) (B 16007 (by norm_num) ⟨8003, by rfl⟩ (by norm_num))
theorem R72445 : Reach 72445 := rs (se 3 (by rfl) ⟨13583, by rfl⟩) (B 27167 (by norm_num) ⟨13583, by rfl⟩ (by norm_num))
theorem R72481 : Reach 72481 := rs (se 2 (by rfl) ⟨27180, by rfl⟩) (B 54361 (by norm_num) ⟨27180, by rfl⟩ (by norm_num))
theorem R72517 : Reach 72517 := rs (se 4 (by rfl) ⟨6798, by rfl⟩) (B 13597 (by norm_num) ⟨6798, by rfl⟩ (by norm_num))
theorem R72553 : Reach 72553 := rs (se 2 (by rfl) ⟨27207, by rfl⟩) (B 54415 (by norm_num) ⟨27207, by rfl⟩ (by norm_num))
theorem R72589 : Reach 72589 := rs (se 3 (by rfl) ⟨13610, by rfl⟩) (B 27221 (by norm_num) ⟨13610, by rfl⟩ (by norm_num))
theorem R72625 : Reach 72625 := rs (se 2 (by rfl) ⟨27234, by rfl⟩) (B 54469 (by norm_num) ⟨27234, by rfl⟩ (by norm_num))
theorem R72661 : Reach 72661 := rs (se 7 (by rfl) ⟨851, by rfl⟩) (B 1703 (by norm_num) ⟨851, by rfl⟩ (by norm_num))
theorem R72697 : Reach 72697 := rs (se 2 (by rfl) ⟨27261, by rfl⟩) (B 54523 (by norm_num) ⟨27261, by rfl⟩ (by norm_num))
theorem R334853 : Reach 334853 := rs (se 4 (by rfl) ⟨31392, by rfl⟩) (B 62785 (by norm_num) ⟨31392, by rfl⟩ (by norm_num))
theorem R72733 : Reach 72733 := rs (se 3 (by rfl) ⟨13637, by rfl⟩) (B 27275 (by norm_num) ⟨13637, by rfl⟩ (by norm_num))
theorem R138277 : Reach 138277 := rs (se 4 (by rfl) ⟨12963, by rfl⟩) (B 25927 (by norm_num) ⟨12963, by rfl⟩ (by norm_num))
theorem R72769 : Reach 72769 := rs (se 2 (by rfl) ⟨27288, by rfl⟩) (B 54577 (by norm_num) ⟨27288, by rfl⟩ (by norm_num))
theorem R72805 : Reach 72805 := rs (se 4 (by rfl) ⟨6825, by rfl⟩) (B 13651 (by norm_num) ⟨6825, by rfl⟩ (by norm_num))
theorem R72841 : Reach 72841 := rs (se 2 (by rfl) ⟨27315, by rfl⟩) (B 54631 (by norm_num) ⟨27315, by rfl⟩ (by norm_num))
theorem R105637 : Reach 105637 := rs (se 4 (by rfl) ⟨9903, by rfl⟩) (B 19807 (by norm_num) ⟨9903, by rfl⟩ (by norm_num))
theorem R72877 : Reach 72877 := rs (se 3 (by rfl) ⟨13664, by rfl⟩) (B 27329 (by norm_num) ⟨13664, by rfl⟩ (by norm_num))
theorem R72913 : Reach 72913 := rs (se 2 (by rfl) ⟨27342, by rfl⟩) (B 54685 (by norm_num) ⟨27342, by rfl⟩ (by norm_num))
theorem R236773 : Reach 236773 := rs (se 4 (by rfl) ⟨22197, by rfl⟩) (B 44395 (by norm_num) ⟨22197, by rfl⟩ (by norm_num))
theorem R466165 : Reach 466165 := rs (se 5 (by rfl) ⟨21851, by rfl⟩) (B 43703 (by norm_num) ⟨21851, by rfl⟩ (by norm_num))
theorem R72949 : Reach 72949 := rs (se 5 (by rfl) ⟨3419, by rfl⟩) (B 6839 (by norm_num) ⟨3419, by rfl⟩ (by norm_num))
theorem R72985 : Reach 72985 := rs (se 2 (by rfl) ⟨27369, by rfl⟩) (B 54739 (by norm_num) ⟨27369, by rfl⟩ (by norm_num))
theorem R73021 : Reach 73021 := rs (se 3 (by rfl) ⟨13691, by rfl⟩) (B 27383 (by norm_num) ⟨13691, by rfl⟩ (by norm_num))
theorem R73057 : Reach 73057 := rs (se 2 (by rfl) ⟨27396, by rfl⟩) (B 54793 (by norm_num) ⟨27396, by rfl⟩ (by norm_num))
theorem R269669 : Reach 269669 := rs (se 4 (by rfl) ⟨25281, by rfl⟩) (B 50563 (by norm_num) ⟨25281, by rfl⟩ (by norm_num))
theorem R73093 : Reach 73093 := rs (se 4 (by rfl) ⟨6852, by rfl⟩) (B 13705 (by norm_num) ⟨6852, by rfl⟩ (by norm_num))
theorem R73129 : Reach 73129 := rs (se 2 (by rfl) ⟨27423, by rfl⟩) (B 54847 (by norm_num) ⟨27423, by rfl⟩ (by norm_num))
theorem R73165 : Reach 73165 := rs (se 3 (by rfl) ⟨13718, by rfl⟩) (B 27437 (by norm_num) ⟨13718, by rfl⟩ (by norm_num))
theorem R73201 : Reach 73201 := rs (se 2 (by rfl) ⟨27450, by rfl⟩) (B 54901 (by norm_num) ⟨27450, by rfl⟩ (by norm_num))
theorem R138773 : Reach 138773 := rs (se 6 (by rfl) ⟨3252, by rfl⟩) (B 6505 (by norm_num) ⟨3252, by rfl⟩ (by norm_num))
theorem R73237 : Reach 73237 := rs (se 6 (by rfl) ⟨1716, by rfl⟩) (B 3433 (by norm_num) ⟨1716, by rfl⟩ (by norm_num))
theorem R138781 : Reach 138781 := rs (se 3 (by rfl) ⟨26021, by rfl⟩) (B 52043 (by norm_num) ⟨26021, by rfl⟩ (by norm_num))
theorem R73273 : Reach 73273 := rs (se 2 (by rfl) ⟨27477, by rfl⟩) (B 54955 (by norm_num) ⟨27477, by rfl⟩ (by norm_num))
theorem R73309 : Reach 73309 := rs (se 3 (by rfl) ⟨13745, by rfl⟩) (B 27491 (by norm_num) ⟨13745, by rfl⟩ (by norm_num))
theorem R73345 : Reach 73345 := rs (se 2 (by rfl) ⟨27504, by rfl⟩) (B 55009 (by norm_num) ⟨27504, by rfl⟩ (by norm_num))
theorem R73381 : Reach 73381 := rs (se 4 (by rfl) ⟨6879, by rfl⟩) (B 13759 (by norm_num) ⟨6879, by rfl⟩ (by norm_num))
theorem R73417 : Reach 73417 := rs (se 2 (by rfl) ⟨27531, by rfl⟩) (B 55063 (by norm_num) ⟨27531, by rfl⟩ (by norm_num))
theorem R73453 : Reach 73453 := rs (se 3 (by rfl) ⟨13772, by rfl⟩) (B 27545 (by norm_num) ⟨13772, by rfl⟩ (by norm_num))
theorem R73489 : Reach 73489 := rs (se 2 (by rfl) ⟨27558, by rfl⟩) (B 55117 (by norm_num) ⟨27558, by rfl⟩ (by norm_num))
theorem R73525 : Reach 73525 := rs (se 5 (by rfl) ⟨3446, by rfl⟩) (B 6893 (by norm_num) ⟨3446, by rfl⟩ (by norm_num))
theorem R106309 : Reach 106309 := rs (se 4 (by rfl) ⟨9966, by rfl⟩) (B 19933 (by norm_num) ⟨9966, by rfl⟩ (by norm_num))
theorem R73561 : Reach 73561 := rs (se 2 (by rfl) ⟨27585, by rfl⟩) (B 55171 (by norm_num) ⟨27585, by rfl⟩ (by norm_num))
theorem R73597 : Reach 73597 := rs (se 3 (by rfl) ⟨13799, by rfl⟩) (B 27599 (by norm_num) ⟨13799, by rfl⟩ (by norm_num))
theorem R73633 : Reach 73633 := rs (se 2 (by rfl) ⟨27612, by rfl⟩) (B 55225 (by norm_num) ⟨27612, by rfl⟩ (by norm_num))
theorem R73669 : Reach 73669 := rs (se 4 (by rfl) ⟨6906, by rfl⟩) (B 13813 (by norm_num) ⟨6906, by rfl⟩ (by norm_num))
theorem R73705 : Reach 73705 := rs (se 2 (by rfl) ⟨27639, by rfl⟩) (B 55279 (by norm_num) ⟨27639, by rfl⟩ (by norm_num))
theorem R73741 : Reach 73741 := rs (se 3 (by rfl) ⟨13826, by rfl⟩) (B 27653 (by norm_num) ⟨13826, by rfl⟩ (by norm_num))
theorem R73777 : Reach 73777 := rs (se 2 (by rfl) ⟨27666, by rfl⟩) (B 55333 (by norm_num) ⟨27666, by rfl⟩ (by norm_num))
theorem R303173 : Reach 303173 := rs (se 4 (by rfl) ⟨28422, by rfl⟩) (B 56845 (by norm_num) ⟨28422, by rfl⟩ (by norm_num))
theorem R73813 : Reach 73813 := rs (se 8 (by rfl) ⟨432, by rfl⟩) (B 865 (by norm_num) ⟨432, by rfl⟩ (by norm_num))
theorem R106589 : Reach 106589 := rs (se 3 (by rfl) ⟨19985, by rfl⟩) (B 39971 (by norm_num) ⟨19985, by rfl⟩ (by norm_num))
theorem R73849 : Reach 73849 := rs (se 2 (by rfl) ⟨27693, by rfl⟩) (B 55387 (by norm_num) ⟨27693, by rfl⟩ (by norm_num))
theorem R73885 : Reach 73885 := rs (se 3 (by rfl) ⟨13853, by rfl⟩) (B 27707 (by norm_num) ⟨13853, by rfl⟩ (by norm_num))
theorem R139445 : Reach 139445 := rs (se 5 (by rfl) ⟨6536, by rfl⟩) (B 13073 (by norm_num) ⟨6536, by rfl⟩ (by norm_num))
theorem R73921 : Reach 73921 := rs (se 2 (by rfl) ⟨27720, by rfl⟩) (B 55441 (by norm_num) ⟨27720, by rfl⟩ (by norm_num))
theorem R106717 : Reach 106717 := rs (se 3 (by rfl) ⟨20009, by rfl⟩) (B 40019 (by norm_num) ⟨20009, by rfl⟩ (by norm_num))
theorem R73957 : Reach 73957 := rs (se 4 (by rfl) ⟨6933, by rfl⟩) (B 13867 (by norm_num) ⟨6933, by rfl⟩ (by norm_num))
theorem R106733 : Reach 106733 := rs (se 3 (by rfl) ⟨20012, by rfl⟩) (B 40025 (by norm_num) ⟨20012, by rfl⟩ (by norm_num))
theorem R73993 : Reach 73993 := rs (se 2 (by rfl) ⟨27747, by rfl⟩) (B 55495 (by norm_num) ⟨27747, by rfl⟩ (by norm_num))
theorem R336149 : Reach 336149 := rs (se 6 (by rfl) ⟨7878, by rfl⟩) (B 15757 (by norm_num) ⟨7878, by rfl⟩ (by norm_num))
theorem R74029 : Reach 74029 := rs (se 3 (by rfl) ⟨13880, by rfl⟩) (B 27761 (by norm_num) ⟨13880, by rfl⟩ (by norm_num))
theorem R106805 : Reach 106805 := rs (se 5 (by rfl) ⟨5006, by rfl⟩) (B 10013 (by norm_num) ⟨5006, by rfl⟩ (by norm_num))
theorem R74041 : Reach 74041 := rs (se 2 (by rfl) ⟨27765, by rfl⟩) (B 55531 (by norm_num) ⟨27765, by rfl⟩ (by norm_num))
theorem R74065 : Reach 74065 := rs (se 2 (by rfl) ⟨27774, by rfl⟩) (B 55549 (by norm_num) ⟨27774, by rfl⟩ (by norm_num))
theorem R74101 : Reach 74101 := rs (se 5 (by rfl) ⟨3473, by rfl⟩) (B 6947 (by norm_num) ⟨3473, by rfl⟩ (by norm_num))
theorem R139661 : Reach 139661 := rs (se 3 (by rfl) ⟨26186, by rfl⟩) (B 52373 (by norm_num) ⟨26186, by rfl⟩ (by norm_num))
theorem R74137 : Reach 74137 := rs (se 2 (by rfl) ⟨27801, by rfl⟩) (B 55603 (by norm_num) ⟨27801, by rfl⟩ (by norm_num))
theorem R106933 : Reach 106933 := rs (se 5 (by rfl) ⟨5012, by rfl⟩) (B 10025 (by norm_num) ⟨5012, by rfl⟩ (by norm_num))
theorem R74173 : Reach 74173 := rs (se 3 (by rfl) ⟨13907, by rfl⟩) (B 27815 (by norm_num) ⟨13907, by rfl⟩ (by norm_num))
theorem R74209 : Reach 74209 := rs (se 2 (by rfl) ⟨27828, by rfl⟩) (B 55657 (by norm_num) ⟨27828, by rfl⟩ (by norm_num))
theorem R139781 : Reach 139781 := rs (se 4 (by rfl) ⟨13104, by rfl⟩) (B 26209 (by norm_num) ⟨13104, by rfl⟩ (by norm_num))
theorem R74245 : Reach 74245 := rs (se 4 (by rfl) ⟨6960, by rfl⟩) (B 13921 (by norm_num) ⟨6960, by rfl⟩ (by norm_num))
theorem R107021 : Reach 107021 := rs (se 3 (by rfl) ⟨20066, by rfl⟩) (B 40133 (by norm_num) ⟨20066, by rfl⟩ (by norm_num))
theorem R74281 : Reach 74281 := rs (se 2 (by rfl) ⟨27855, by rfl⟩) (B 55711 (by norm_num) ⟨27855, by rfl⟩ (by norm_num))
theorem R74317 : Reach 74317 := rs (se 3 (by rfl) ⟨13934, by rfl⟩) (B 27869 (by norm_num) ⟨13934, by rfl⟩ (by norm_num))
theorem R74353 : Reach 74353 := rs (se 2 (by rfl) ⟨27882, by rfl⟩) (B 55765 (by norm_num) ⟨27882, by rfl⟩ (by norm_num))
theorem R107149 : Reach 107149 := rs (se 3 (by rfl) ⟨20090, by rfl⟩) (B 40181 (by norm_num) ⟨20090, by rfl⟩ (by norm_num))
theorem R74389 : Reach 74389 := rs (se 6 (by rfl) ⟨1743, by rfl⟩) (B 3487 (by norm_num) ⟨1743, by rfl⟩ (by norm_num))
theorem R74425 : Reach 74425 := rs (se 2 (by rfl) ⟨27909, by rfl⟩) (B 55819 (by norm_num) ⟨27909, by rfl⟩ (by norm_num))
theorem R74461 : Reach 74461 := rs (se 3 (by rfl) ⟨13961, by rfl⟩) (B 27923 (by norm_num) ⟨13961, by rfl⟩ (by norm_num))
theorem R107237 : Reach 107237 := rs (se 4 (by rfl) ⟨10053, by rfl⟩) (B 20107 (by norm_num) ⟨10053, by rfl⟩ (by norm_num))
theorem R74497 : Reach 74497 := rs (se 2 (by rfl) ⟨27936, by rfl⟩) (B 55873 (by norm_num) ⟨27936, by rfl⟩ (by norm_num))
theorem R74533 : Reach 74533 := rs (se 4 (by rfl) ⟨6987, by rfl⟩) (B 13975 (by norm_num) ⟨6987, by rfl⟩ (by norm_num))
theorem R74569 : Reach 74569 := rs (se 2 (by rfl) ⟨27963, by rfl⟩) (B 55927 (by norm_num) ⟨27963, by rfl⟩ (by norm_num))
theorem R107365 : Reach 107365 := rs (se 4 (by rfl) ⟨10065, by rfl⟩) (B 20131 (by norm_num) ⟨10065, by rfl⟩ (by norm_num))
theorem R74605 : Reach 74605 := rs (se 3 (by rfl) ⟨13988, by rfl⟩) (B 27977 (by norm_num) ⟨13988, by rfl⟩ (by norm_num))
theorem R74641 : Reach 74641 := rs (se 2 (by rfl) ⟨27990, by rfl⟩) (B 55981 (by norm_num) ⟨27990, by rfl⟩ (by norm_num))
theorem R74677 : Reach 74677 := rs (se 5 (by rfl) ⟨3500, by rfl⟩) (B 7001 (by norm_num) ⟨3500, by rfl⟩ (by norm_num))
theorem R107453 : Reach 107453 := rs (se 3 (by rfl) ⟨20147, by rfl⟩) (B 40295 (by norm_num) ⟨20147, by rfl⟩ (by norm_num))
theorem R74713 : Reach 74713 := rs (se 2 (by rfl) ⟨28017, by rfl⟩) (B 56035 (by norm_num) ⟨28017, by rfl⟩ (by norm_num))
theorem R74749 : Reach 74749 := rs (se 3 (by rfl) ⟨14015, by rfl⟩) (B 28031 (by norm_num) ⟨14015, by rfl⟩ (by norm_num))
theorem R926741 : Reach 926741 := rs (se 6 (by rfl) ⟨21720, by rfl⟩) (B 43441 (by norm_num) ⟨21720, by rfl⟩ (by norm_num))
theorem R74785 : Reach 74785 := rs (se 2 (by rfl) ⟨28044, by rfl⟩) (B 56089 (by norm_num) ⟨28044, by rfl⟩ (by norm_num))
theorem R107581 : Reach 107581 := rs (se 3 (by rfl) ⟨20171, by rfl⟩) (B 40343 (by norm_num) ⟨20171, by rfl⟩ (by norm_num))
theorem R74821 : Reach 74821 := rs (se 4 (by rfl) ⟨7014, by rfl⟩) (B 14029 (by norm_num) ⟨7014, by rfl⟩ (by norm_num))
theorem R74857 : Reach 74857 := rs (se 2 (by rfl) ⟨28071, by rfl⟩) (B 56143 (by norm_num) ⟨28071, by rfl⟩ (by norm_num))
theorem R140413 : Reach 140413 := rs (se 3 (by rfl) ⟨26327, by rfl⟩) (B 52655 (by norm_num) ⟨26327, by rfl⟩ (by norm_num))
theorem R74893 : Reach 74893 := rs (se 3 (by rfl) ⟨14042, by rfl⟩) (B 28085 (by norm_num) ⟨14042, by rfl⟩ (by norm_num))
theorem R107669 : Reach 107669 := rs (se 6 (by rfl) ⟨2523, by rfl⟩) (B 5047 (by norm_num) ⟨2523, by rfl⟩ (by norm_num))
theorem R74929 : Reach 74929 := rs (se 2 (by rfl) ⟨28098, by rfl⟩) (B 56197 (by norm_num) ⟨28098, by rfl⟩ (by norm_num))
theorem R74965 : Reach 74965 := rs (se 7 (by rfl) ⟨878, by rfl⟩) (B 1757 (by norm_num) ⟨878, by rfl⟩ (by norm_num))
theorem R533749 : Reach 533749 := rs (se 5 (by rfl) ⟨25019, by rfl⟩) (B 50039 (by norm_num) ⟨25019, by rfl⟩ (by norm_num))
theorem R75001 : Reach 75001 := rs (se 2 (by rfl) ⟨28125, by rfl⟩) (B 56251 (by norm_num) ⟨28125, by rfl⟩ (by norm_num))
theorem R107797 : Reach 107797 := rs (se 6 (by rfl) ⟨2526, by rfl⟩) (B 5053 (by norm_num) ⟨2526, by rfl⟩ (by norm_num))
theorem R75037 : Reach 75037 := rs (se 3 (by rfl) ⟨14069, by rfl⟩) (B 28139 (by norm_num) ⟨14069, by rfl⟩ (by norm_num))
theorem R75073 : Reach 75073 := rs (se 2 (by rfl) ⟨28152, by rfl⟩) (B 56305 (by norm_num) ⟨28152, by rfl⟩ (by norm_num))
theorem R599381 : Reach 599381 := rs (se 12 (by rfl) ⟨219, by rfl⟩) (B 439 (by norm_num) ⟨219, by rfl⟩ (by norm_num))
theorem R75109 : Reach 75109 := rs (se 4 (by rfl) ⟨7041, by rfl⟩) (B 14083 (by norm_num) ⟨7041, by rfl⟩ (by norm_num))
theorem R107885 : Reach 107885 := rs (se 3 (by rfl) ⟨20228, by rfl⟩) (B 40457 (by norm_num) ⟨20228, by rfl⟩ (by norm_num))
theorem R75145 : Reach 75145 := rs (se 2 (by rfl) ⟨28179, by rfl⟩) (B 56359 (by norm_num) ⟨28179, by rfl⟩ (by norm_num))
theorem R75181 : Reach 75181 := rs (se 3 (by rfl) ⟨14096, by rfl⟩) (B 28193 (by norm_num) ⟨14096, by rfl⟩ (by norm_num))
theorem R75217 : Reach 75217 := rs (se 2 (by rfl) ⟨28206, by rfl⟩) (B 56413 (by norm_num) ⟨28206, by rfl⟩ (by norm_num))
theorem R959957 : Reach 959957 := rs (se 7 (by rfl) ⟨11249, by rfl⟩) (B 22499 (by norm_num) ⟨11249, by rfl⟩ (by norm_num))
theorem R108013 : Reach 108013 := rs (se 3 (by rfl) ⟨20252, by rfl⟩) (B 40505 (by norm_num) ⟨20252, by rfl⟩ (by norm_num))
theorem R75253 : Reach 75253 := rs (se 5 (by rfl) ⟨3527, by rfl⟩) (B 7055 (by norm_num) ⟨3527, by rfl⟩ (by norm_num))
theorem R75289 : Reach 75289 := rs (se 2 (by rfl) ⟨28233, by rfl⟩) (B 56467 (by norm_num) ⟨28233, by rfl⟩ (by norm_num))
theorem R75325 : Reach 75325 := rs (se 3 (by rfl) ⟨14123, by rfl⟩) (B 28247 (by norm_num) ⟨14123, by rfl⟩ (by norm_num))
theorem R108101 : Reach 108101 := rs (se 4 (by rfl) ⟨10134, by rfl⟩) (B 20269 (by norm_num) ⟨10134, by rfl⟩ (by norm_num))
theorem R75361 : Reach 75361 := rs (se 2 (by rfl) ⟨28260, by rfl⟩) (B 56521 (by norm_num) ⟨28260, by rfl⟩ (by norm_num))
theorem R75397 : Reach 75397 := rs (se 4 (by rfl) ⟨7068, by rfl⟩) (B 14137 (by norm_num) ⟨7068, by rfl⟩ (by norm_num))
theorem R75433 : Reach 75433 := rs (se 2 (by rfl) ⟨28287, by rfl⟩) (B 56575 (by norm_num) ⟨28287, by rfl⟩ (by norm_num))
theorem R108229 : Reach 108229 := rs (se 4 (by rfl) ⟨10146, by rfl⟩) (B 20293 (by norm_num) ⟨10146, by rfl⟩ (by norm_num))
theorem R75469 : Reach 75469 := rs (se 3 (by rfl) ⟨14150, by rfl⟩) (B 28301 (by norm_num) ⟨14150, by rfl⟩ (by norm_num))
theorem R403157 : Reach 403157 := rs (se 7 (by rfl) ⟨4724, by rfl⟩) (B 9449 (by norm_num) ⟨4724, by rfl⟩ (by norm_num))
theorem R75505 : Reach 75505 := rs (se 2 (by rfl) ⟨28314, by rfl⟩) (B 56629 (by norm_num) ⟨28314, by rfl⟩ (by norm_num))
theorem R1124117 : Reach 1124117 := rs (se 6 (by rfl) ⟨26346, by rfl⟩) (B 52693 (by norm_num) ⟨26346, by rfl⟩ (by norm_num))
theorem R108317 : Reach 108317 := rs (se 3 (by rfl) ⟨20309, by rfl⟩) (B 40619 (by norm_num) ⟨20309, by rfl⟩ (by norm_num))
theorem R108445 : Reach 108445 := rs (se 3 (by rfl) ⟨20333, by rfl⟩) (B 40667 (by norm_num) ⟨20333, by rfl⟩ (by norm_num))
theorem R75757 : Reach 75757 := rs (se 3 (by rfl) ⟨14204, by rfl⟩) (B 28409 (by norm_num) ⟨14204, by rfl⟩ (by norm_num))
theorem R108533 : Reach 108533 := rs (se 5 (by rfl) ⟨5087, by rfl⟩) (B 10175 (by norm_num) ⟨5087, by rfl⟩ (by norm_num))
theorem R141301 : Reach 141301 := rs (se 5 (by rfl) ⟨6623, by rfl⟩) (B 13247 (by norm_num) ⟨6623, by rfl⟩ (by norm_num))
theorem R141421 : Reach 141421 := rs (se 3 (by rfl) ⟨26516, by rfl⟩) (B 53033 (by norm_num) ⟨26516, by rfl⟩ (by norm_num))
theorem R108661 : Reach 108661 := rs (se 5 (by rfl) ⟨5093, by rfl⟩) (B 10187 (by norm_num) ⟨5093, by rfl⟩ (by norm_num))
theorem R108749 : Reach 108749 := rs (se 3 (by rfl) ⟨20390, by rfl⟩) (B 40781 (by norm_num) ⟨20390, by rfl⟩ (by norm_num))
theorem R76021 : Reach 76021 := rs (se 5 (by rfl) ⟨3563, by rfl⟩) (B 7127 (by norm_num) ⟨3563, by rfl⟩ (by norm_num))
theorem R698645 : Reach 698645 := rs (se 6 (by rfl) ⟨16374, by rfl⟩) (B 32749 (by norm_num) ⟨16374, by rfl⟩ (by norm_num))
theorem R502037 : Reach 502037 := rs (se 6 (by rfl) ⟨11766, by rfl⟩) (B 23533 (by norm_num) ⟨11766, by rfl⟩ (by norm_num))
theorem R207173 : Reach 207173 := rs (se 4 (by rfl) ⟨19422, by rfl⟩) (B 38845 (by norm_num) ⟨19422, by rfl⟩ (by norm_num))
theorem R108877 : Reach 108877 := rs (se 3 (by rfl) ⟨20414, by rfl⟩) (B 40829 (by norm_num) ⟨20414, by rfl⟩ (by norm_num))
theorem R1419605 : Reach 1419605 := rs (se 10 (by rfl) ⟨2079, by rfl⟩) (B 4159 (by norm_num) ⟨2079, by rfl⟩ (by norm_num))
theorem R141677 : Reach 141677 := rs (se 3 (by rfl) ⟨26564, by rfl⟩) (B 53129 (by norm_num) ⟨26564, by rfl⟩ (by norm_num))
theorem R108965 : Reach 108965 := rs (se 4 (by rfl) ⟨10215, by rfl⟩) (B 20431 (by norm_num) ⟨10215, by rfl⟩ (by norm_num))
theorem R109093 : Reach 109093 := rs (se 4 (by rfl) ⟨10227, by rfl⟩) (B 20455 (by norm_num) ⟨10227, by rfl⟩ (by norm_num))
theorem R76349 : Reach 76349 := rs (se 3 (by rfl) ⟨14315, by rfl⟩) (B 28631 (by norm_num) ⟨14315, by rfl⟩ (by norm_num))
theorem R272965 : Reach 272965 := rs (se 4 (by rfl) ⟨25590, by rfl⟩) (B 51181 (by norm_num) ⟨25590, by rfl⟩ (by norm_num))
theorem R76397 : Reach 76397 := rs (se 3 (by rfl) ⟨14324, by rfl⟩) (B 28649 (by norm_num) ⟨14324, by rfl⟩ (by norm_num))
theorem R109181 : Reach 109181 := rs (se 3 (by rfl) ⟨20471, by rfl⟩) (B 40943 (by norm_num) ⟨20471, by rfl⟩ (by norm_num))
theorem R142037 : Reach 142037 := rs (se 7 (by rfl) ⟨1664, by rfl⟩) (B 3329 (by norm_num) ⟨1664, by rfl⟩ (by norm_num))
theorem R109309 : Reach 109309 := rs (se 3 (by rfl) ⟨20495, by rfl⟩) (B 40991 (by norm_num) ⟨20495, by rfl⟩ (by norm_num))
theorem R142109 : Reach 142109 := rs (se 3 (by rfl) ⟨26645, by rfl⟩) (B 53291 (by norm_num) ⟨26645, by rfl⟩ (by norm_num))
theorem R338741 : Reach 338741 := rs (se 5 (by rfl) ⟨15878, by rfl⟩) (B 31757 (by norm_num) ⟨15878, by rfl⟩ (by norm_num))
theorem R109397 : Reach 109397 := rs (se 9 (by rfl) ⟨320, by rfl⟩) (B 641 (by norm_num) ⟨320, by rfl⟩ (by norm_num))
theorem R142181 : Reach 142181 := rs (se 4 (by rfl) ⟨13329, by rfl⟩) (B 26659 (by norm_num) ⟨13329, by rfl⟩ (by norm_num))
theorem R109421 : Reach 109421 := rs (se 3 (by rfl) ⟨20516, by rfl⟩) (B 41033 (by norm_num) ⟨20516, by rfl⟩ (by norm_num))
theorem R142253 : Reach 142253 := rs (se 3 (by rfl) ⟨26672, by rfl⟩) (B 53345 (by norm_num) ⟨26672, by rfl⟩ (by norm_num))
theorem R109525 : Reach 109525 := rs (se 7 (by rfl) ⟨1283, by rfl⟩) (B 2567 (by norm_num) ⟨1283, by rfl⟩ (by norm_num))
theorem R142325 : Reach 142325 := rs (se 5 (by rfl) ⟨6671, by rfl⟩) (B 13343 (by norm_num) ⟨6671, by rfl⟩ (by norm_num))
theorem R240677 : Reach 240677 := rs (se 4 (by rfl) ⟨22563, by rfl⟩) (B 45127 (by norm_num) ⟨22563, by rfl⟩ (by norm_num))
theorem R109613 : Reach 109613 := rs (se 3 (by rfl) ⟨20552, by rfl⟩) (B 41105 (by norm_num) ⟨20552, by rfl⟩ (by norm_num))
theorem R142397 : Reach 142397 := rs (se 3 (by rfl) ⟨26699, by rfl⟩) (B 53399 (by norm_num) ⟨26699, by rfl⟩ (by norm_num))
theorem R240725 : Reach 240725 := rs (se 8 (by rfl) ⟨1410, by rfl⟩) (B 2821 (by norm_num) ⟨1410, by rfl⟩ (by norm_num))
theorem R142469 : Reach 142469 := rs (se 4 (by rfl) ⟨13356, by rfl⟩) (B 26713 (by norm_num) ⟨13356, by rfl⟩ (by norm_num))
theorem R76945 : Reach 76945 := rs (se 2 (by rfl) ⟨28854, by rfl⟩) (B 57709 (by norm_num) ⟨28854, by rfl⟩ (by norm_num))
theorem R109741 : Reach 109741 := rs (se 3 (by rfl) ⟨20576, by rfl⟩) (B 41153 (by norm_num) ⟨20576, by rfl⟩ (by norm_num))
theorem R142541 : Reach 142541 := rs (se 3 (by rfl) ⟨26726, by rfl⟩) (B 53453 (by norm_num) ⟨26726, by rfl⟩ (by norm_num))
theorem R142565 : Reach 142565 := rs (se 4 (by rfl) ⟨13365, by rfl⟩) (B 26731 (by norm_num) ⟨13365, by rfl⟩ (by norm_num))
theorem R109829 : Reach 109829 := rs (se 4 (by rfl) ⟨10296, by rfl⟩) (B 20593 (by norm_num) ⟨10296, by rfl⟩ (by norm_num))
theorem R142613 : Reach 142613 := rs (se 6 (by rfl) ⟨3342, by rfl⟩) (B 6685 (by norm_num) ⟨3342, by rfl⟩ (by norm_num))
theorem R240965 : Reach 240965 := rs (se 4 (by rfl) ⟨22590, by rfl⟩) (B 45181 (by norm_num) ⟨22590, by rfl⟩ (by norm_num))
theorem R142685 : Reach 142685 := rs (se 3 (by rfl) ⟨26753, by rfl⟩) (B 53507 (by norm_num) ⟨26753, by rfl⟩ (by norm_num))
theorem R208261 : Reach 208261 := rs (se 4 (by rfl) ⟨19524, by rfl⟩) (B 39049 (by norm_num) ⟨19524, by rfl⟩ (by norm_num))
theorem R109957 : Reach 109957 := rs (se 4 (by rfl) ⟨10308, by rfl⟩) (B 20617 (by norm_num) ⟨10308, by rfl⟩ (by norm_num))
theorem R142757 : Reach 142757 := rs (se 4 (by rfl) ⟨13383, by rfl⟩) (B 26767 (by norm_num) ⟨13383, by rfl⟩ (by norm_num))
theorem R142805 : Reach 142805 := rs (se 7 (by rfl) ⟨1673, by rfl⟩) (B 3347 (by norm_num) ⟨1673, by rfl⟩ (by norm_num))
theorem R110045 : Reach 110045 := rs (se 3 (by rfl) ⟨20633, by rfl⟩) (B 41267 (by norm_num) ⟨20633, by rfl⟩ (by norm_num))
theorem R142829 : Reach 142829 := rs (se 3 (by rfl) ⟨26780, by rfl⟩) (B 53561 (by norm_num) ⟨26780, by rfl⟩ (by norm_num))
theorem R142901 : Reach 142901 := rs (se 5 (by rfl) ⟨6698, by rfl⟩) (B 13397 (by norm_num) ⟨6698, by rfl⟩ (by norm_num))
theorem R110173 : Reach 110173 := rs (se 3 (by rfl) ⟨20657, by rfl⟩) (B 41315 (by norm_num) ⟨20657, by rfl⟩ (by norm_num))
theorem R77425 : Reach 77425 := rs (se 2 (by rfl) ⟨29034, by rfl⟩) (B 58069 (by norm_num) ⟨29034, by rfl⟩ (by norm_num))
theorem R142973 : Reach 142973 := rs (se 3 (by rfl) ⟨26807, by rfl⟩) (B 53615 (by norm_num) ⟨26807, by rfl⟩ (by norm_num))
theorem R110261 : Reach 110261 := rs (se 5 (by rfl) ⟨5168, by rfl⟩) (B 10337 (by norm_num) ⟨5168, by rfl⟩ (by norm_num))
theorem R143045 : Reach 143045 := rs (se 4 (by rfl) ⟨13410, by rfl⟩) (B 26821 (by norm_num) ⟨13410, by rfl⟩ (by norm_num))
theorem R143117 : Reach 143117 := rs (se 3 (by rfl) ⟨26834, by rfl⟩) (B 53669 (by norm_num) ⟨26834, by rfl⟩ (by norm_num))
theorem R110389 : Reach 110389 := rs (se 5 (by rfl) ⟨5174, by rfl⟩) (B 10349 (by norm_num) ⟨5174, by rfl⟩ (by norm_num))
theorem R143189 : Reach 143189 := rs (se 9 (by rfl) ⟨419, by rfl⟩) (B 839 (by norm_num) ⟨419, by rfl⟩ (by norm_num))
theorem R110477 : Reach 110477 := rs (se 3 (by rfl) ⟨20714, by rfl⟩) (B 41429 (by norm_num) ⟨20714, by rfl⟩ (by norm_num))
theorem R143261 : Reach 143261 := rs (se 3 (by rfl) ⟨26861, by rfl⟩) (B 53723 (by norm_num) ⟨26861, by rfl⟩ (by norm_num))
theorem R143309 : Reach 143309 := rs (se 3 (by rfl) ⟨26870, by rfl⟩) (B 53741 (by norm_num) ⟨26870, by rfl⟩ (by norm_num))
theorem R143317 : Reach 143317 := rs (se 7 (by rfl) ⟨1679, by rfl⟩) (B 3359 (by norm_num) ⟨1679, by rfl⟩ (by norm_num))
theorem R143333 : Reach 143333 := rs (se 4 (by rfl) ⟨13437, by rfl⟩) (B 26875 (by norm_num) ⟨13437, by rfl⟩ (by norm_num))
theorem R110605 : Reach 110605 := rs (se 3 (by rfl) ⟨20738, by rfl⟩) (B 41477 (by norm_num) ⟨20738, by rfl⟩ (by norm_num))
theorem R143405 : Reach 143405 := rs (se 3 (by rfl) ⟨26888, by rfl⟩) (B 53777 (by norm_num) ⟨26888, by rfl⟩ (by norm_num))
theorem R110693 : Reach 110693 := rs (se 4 (by rfl) ⟨10377, by rfl⟩) (B 20755 (by norm_num) ⟨10377, by rfl⟩ (by norm_num))
theorem R143477 : Reach 143477 := rs (se 5 (by rfl) ⟨6725, by rfl⟩) (B 13451 (by norm_num) ⟨6725, by rfl⟩ (by norm_num))
theorem R143549 : Reach 143549 := rs (se 3 (by rfl) ⟨26915, by rfl⟩) (B 53831 (by norm_num) ⟨26915, by rfl⟩ (by norm_num))
theorem R110821 : Reach 110821 := rs (se 4 (by rfl) ⟨10389, by rfl⟩) (B 20779 (by norm_num) ⟨10389, by rfl⟩ (by norm_num))
theorem R110837 : Reach 110837 := rs (se 5 (by rfl) ⟨5195, by rfl⟩) (B 10391 (by norm_num) ⟨5195, by rfl⟩ (by norm_num))
theorem R143621 : Reach 143621 := rs (se 4 (by rfl) ⟨13464, by rfl⟩) (B 26929 (by norm_num) ⟨13464, by rfl⟩ (by norm_num))
theorem R110909 : Reach 110909 := rs (se 3 (by rfl) ⟨20795, by rfl⟩) (B 41591 (by norm_num) ⟨20795, by rfl⟩ (by norm_num))
theorem R143693 : Reach 143693 := rs (se 3 (by rfl) ⟨26942, by rfl⟩) (B 53885 (by norm_num) ⟨26942, by rfl⟩ (by norm_num))
theorem R143765 : Reach 143765 := rs (se 6 (by rfl) ⟨3369, by rfl⟩) (B 6739 (by norm_num) ⟨3369, by rfl⟩ (by norm_num))
theorem R111037 : Reach 111037 := rs (se 3 (by rfl) ⟨20819, by rfl⟩) (B 41639 (by norm_num) ⟨20819, by rfl⟩ (by norm_num))
theorem R143837 : Reach 143837 := rs (se 3 (by rfl) ⟨26969, by rfl⟩) (B 53939 (by norm_num) ⟨26969, by rfl⟩ (by norm_num))
theorem R78305 : Reach 78305 := rs (se 2 (by rfl) ⟨29364, by rfl⟩) (B 58729 (by norm_num) ⟨29364, by rfl⟩ (by norm_num))
theorem R242149 : Reach 242149 := rs (se 4 (by rfl) ⟨22701, by rfl⟩) (B 45403 (by norm_num) ⟨22701, by rfl⟩ (by norm_num))
theorem R209429 : Reach 209429 := rs (se 6 (by rfl) ⟨4908, by rfl⟩) (B 9817 (by norm_num) ⟨4908, by rfl⟩ (by norm_num))
theorem R111125 : Reach 111125 := rs (se 6 (by rfl) ⟨2604, by rfl⟩) (B 5209 (by norm_num) ⟨2604, by rfl⟩ (by norm_num))
theorem R143909 : Reach 143909 := rs (se 4 (by rfl) ⟨13491, by rfl⟩) (B 26983 (by norm_num) ⟨13491, by rfl⟩ (by norm_num))
theorem R78413 : Reach 78413 := rs (se 3 (by rfl) ⟨14702, by rfl⟩) (B 29405 (by norm_num) ⟨14702, by rfl⟩ (by norm_num))
theorem R78421 : Reach 78421 := rs (se 8 (by rfl) ⟨459, by rfl⟩) (B 919 (by norm_num) ⟨459, by rfl⟩ (by norm_num))
theorem R143981 : Reach 143981 := rs (se 3 (by rfl) ⟨26996, by rfl⟩) (B 53993 (by norm_num) ⟨26996, by rfl⟩ (by norm_num))
theorem R111253 : Reach 111253 := rs (se 6 (by rfl) ⟨2607, by rfl⟩) (B 5215 (by norm_num) ⟨2607, by rfl⟩ (by norm_num))
theorem R144053 : Reach 144053 := rs (se 5 (by rfl) ⟨6752, by rfl⟩) (B 13505 (by norm_num) ⟨6752, by rfl⟩ (by norm_num))
theorem R111341 : Reach 111341 := rs (se 3 (by rfl) ⟨20876, by rfl⟩) (B 41753 (by norm_num) ⟨20876, by rfl⟩ (by norm_num))
theorem R144125 : Reach 144125 := rs (se 3 (by rfl) ⟨27023, by rfl⟩) (B 54047 (by norm_num) ⟨27023, by rfl⟩ (by norm_num))
theorem R242453 : Reach 242453 := rs (se 6 (by rfl) ⟨5682, by rfl⟩) (B 11365 (by norm_num) ⟨5682, by rfl⟩ (by norm_num))
theorem R78617 : Reach 78617 := rs (se 2 (by rfl) ⟨29481, by rfl⟩) (B 58963 (by norm_num) ⟨29481, by rfl⟩ (by norm_num))
theorem R144197 : Reach 144197 := rs (se 4 (by rfl) ⟨13518, by rfl⟩) (B 27037 (by norm_num) ⟨13518, by rfl⟩ (by norm_num))
theorem R78697 : Reach 78697 := rs (se 2 (by rfl) ⟨29511, by rfl⟩) (B 59023 (by norm_num) ⟨29511, by rfl⟩ (by norm_num))
theorem R111469 : Reach 111469 := rs (se 3 (by rfl) ⟨20900, by rfl⟩) (B 41801 (by norm_num) ⟨20900, by rfl⟩ (by norm_num))
theorem R144269 : Reach 144269 := rs (se 3 (by rfl) ⟨27050, by rfl⟩) (B 54101 (by norm_num) ⟨27050, by rfl⟩ (by norm_num))
theorem R111557 : Reach 111557 := rs (se 4 (by rfl) ⟨10458, by rfl⟩) (B 20917 (by norm_num) ⟨10458, by rfl⟩ (by norm_num))
theorem R144341 : Reach 144341 := rs (se 7 (by rfl) ⟨1691, by rfl⟩) (B 3383 (by norm_num) ⟨1691, by rfl⟩ (by norm_num))
theorem R144413 : Reach 144413 := rs (se 3 (by rfl) ⟨27077, by rfl⟩) (B 54155 (by norm_num) ⟨27077, by rfl⟩ (by norm_num))
theorem R111685 : Reach 111685 := rs (se 4 (by rfl) ⟨10470, by rfl⟩) (B 20941 (by norm_num) ⟨10470, by rfl⟩ (by norm_num))
theorem R144485 : Reach 144485 := rs (se 4 (by rfl) ⟨13545, by rfl⟩) (B 27091 (by norm_num) ⟨13545, by rfl⟩ (by norm_num))
theorem R308357 : Reach 308357 := rs (se 4 (by rfl) ⟨28908, by rfl⟩) (B 57817 (by norm_num) ⟨28908, by rfl⟩ (by norm_num))
theorem R373909 : Reach 373909 := rs (se 6 (by rfl) ⟨8763, by rfl⟩) (B 17527 (by norm_num) ⟨8763, by rfl⟩ (by norm_num))
theorem R111773 : Reach 111773 := rs (se 3 (by rfl) ⟨20957, by rfl⟩) (B 41915 (by norm_num) ⟨20957, by rfl⟩ (by norm_num))
theorem R144557 : Reach 144557 := rs (se 3 (by rfl) ⟨27104, by rfl⟩) (B 54209 (by norm_num) ⟨27104, by rfl⟩ (by norm_num))
theorem R144629 : Reach 144629 := rs (se 5 (by rfl) ⟨6779, by rfl⟩) (B 13559 (by norm_num) ⟨6779, by rfl⟩ (by norm_num))
theorem R111901 : Reach 111901 := rs (se 3 (by rfl) ⟨20981, by rfl⟩) (B 41963 (by norm_num) ⟨20981, by rfl⟩ (by norm_num))
theorem R144701 : Reach 144701 := rs (se 3 (by rfl) ⟨27131, by rfl⟩) (B 54263 (by norm_num) ⟨27131, by rfl⟩ (by norm_num))
theorem R79165 : Reach 79165 := rs (se 3 (by rfl) ⟨14843, by rfl⟩) (B 29687 (by norm_num) ⟨14843, by rfl⟩ (by norm_num))
theorem R308549 : Reach 308549 := rs (se 4 (by rfl) ⟨28926, by rfl⟩) (B 57853 (by norm_num) ⟨28926, by rfl⟩ (by norm_num))
theorem R111989 : Reach 111989 := rs (se 5 (by rfl) ⟨5249, by rfl⟩) (B 10499 (by norm_num) ⟨5249, by rfl⟩ (by norm_num))
theorem R144773 : Reach 144773 := rs (se 4 (by rfl) ⟨13572, by rfl⟩) (B 27145 (by norm_num) ⟨13572, by rfl⟩ (by norm_num))
theorem R144797 : Reach 144797 := rs (se 3 (by rfl) ⟨27149, by rfl⟩) (B 54299 (by norm_num) ⟨27149, by rfl⟩ (by norm_num))
theorem R144845 : Reach 144845 := rs (se 3 (by rfl) ⟨27158, by rfl⟩) (B 54317 (by norm_num) ⟨27158, by rfl⟩ (by norm_num))
theorem R79309 : Reach 79309 := rs (se 3 (by rfl) ⟨14870, by rfl⟩) (B 29741 (by norm_num) ⟨14870, by rfl⟩ (by norm_num))
theorem R275957 : Reach 275957 := rs (se 5 (by rfl) ⟨12935, by rfl⟩) (B 25871 (by norm_num) ⟨12935, by rfl⟩ (by norm_num))
theorem R112117 : Reach 112117 := rs (se 5 (by rfl) ⟨5255, by rfl⟩) (B 10511 (by norm_num) ⟨5255, by rfl⟩ (by norm_num))
theorem R144917 : Reach 144917 := rs (se 6 (by rfl) ⟨3396, by rfl⟩) (B 6793 (by norm_num) ⟨3396, by rfl⟩ (by norm_num))
theorem R112205 : Reach 112205 := rs (se 3 (by rfl) ⟨21038, by rfl⟩) (B 42077 (by norm_num) ⟨21038, by rfl⟩ (by norm_num))
theorem R144989 : Reach 144989 := rs (se 3 (by rfl) ⟨27185, by rfl⟩) (B 54371 (by norm_num) ⟨27185, by rfl⟩ (by norm_num))
theorem R112261 : Reach 112261 := rs (se 4 (by rfl) ⟨10524, by rfl⟩) (B 21049 (by norm_num) ⟨10524, by rfl⟩ (by norm_num))
theorem R177797 : Reach 177797 := rs (se 4 (by rfl) ⟨16668, by rfl⟩) (B 33337 (by norm_num) ⟨16668, by rfl⟩ (by norm_num))
theorem R145061 : Reach 145061 := rs (se 4 (by rfl) ⟨13599, by rfl⟩) (B 27199 (by norm_num) ⟨13599, by rfl⟩ (by norm_num))
theorem R308933 : Reach 308933 := rs (se 4 (by rfl) ⟨28962, by rfl⟩) (B 57925 (by norm_num) ⟨28962, by rfl⟩ (by norm_num))
theorem R112333 : Reach 112333 := rs (se 3 (by rfl) ⟨21062, by rfl⟩) (B 42125 (by norm_num) ⟨21062, by rfl⟩ (by norm_num))
theorem R145133 : Reach 145133 := rs (se 3 (by rfl) ⟨27212, by rfl⟩) (B 54425 (by norm_num) ⟨27212, by rfl⟩ (by norm_num))
theorem R112421 : Reach 112421 := rs (se 4 (by rfl) ⟨10539, by rfl⟩) (B 21079 (by norm_num) ⟨10539, by rfl⟩ (by norm_num))
theorem R145205 : Reach 145205 := rs (se 5 (by rfl) ⟨6806, by rfl⟩) (B 13613 (by norm_num) ⟨6806, by rfl⟩ (by norm_num))
theorem R145277 : Reach 145277 := rs (se 3 (by rfl) ⟨27239, by rfl⟩) (B 54479 (by norm_num) ⟨27239, by rfl⟩ (by norm_num))
theorem R145309 : Reach 145309 := rs (se 3 (by rfl) ⟨27245, by rfl⟩) (B 54491 (by norm_num) ⟨27245, by rfl⟩ (by norm_num))
theorem R112549 : Reach 112549 := rs (se 4 (by rfl) ⟨10551, by rfl⟩) (B 21103 (by norm_num) ⟨10551, by rfl⟩ (by norm_num))
theorem R145349 : Reach 145349 := rs (se 4 (by rfl) ⟨13626, by rfl⟩) (B 27253 (by norm_num) ⟨13626, by rfl⟩ (by norm_num))
theorem R112637 : Reach 112637 := rs (se 3 (by rfl) ⟨21119, by rfl⟩) (B 42239 (by norm_num) ⟨21119, by rfl⟩ (by norm_num))
theorem R145421 : Reach 145421 := rs (se 3 (by rfl) ⟨27266, by rfl⟩) (B 54533 (by norm_num) ⟨27266, by rfl⟩ (by norm_num))
theorem R145493 : Reach 145493 := rs (se 8 (by rfl) ⟨852, by rfl⟩) (B 1705 (by norm_num) ⟨852, by rfl⟩ (by norm_num))
theorem R79957 : Reach 79957 := rs (se 8 (by rfl) ⟨468, by rfl⟩) (B 937 (by norm_num) ⟨468, by rfl⟩ (by norm_num))
theorem R112765 : Reach 112765 := rs (se 3 (by rfl) ⟨21143, by rfl⟩) (B 42287 (by norm_num) ⟨21143, by rfl⟩ (by norm_num))
theorem R145565 : Reach 145565 := rs (se 3 (by rfl) ⟨27293, by rfl⟩) (B 54587 (by norm_num) ⟨27293, by rfl⟩ (by norm_num))
theorem R211157 : Reach 211157 := rs (se 7 (by rfl) ⟨2474, by rfl⟩) (B 4949 (by norm_num) ⟨2474, by rfl⟩ (by norm_num))
theorem R112853 : Reach 112853 := rs (se 7 (by rfl) ⟨1322, by rfl⟩) (B 2645 (by norm_num) ⟨1322, by rfl⟩ (by norm_num))
theorem R145637 : Reach 145637 := rs (se 4 (by rfl) ⟨13653, by rfl⟩) (B 27307 (by norm_num) ⟨13653, by rfl⟩ (by norm_num))
theorem R80129 : Reach 80129 := rs (se 2 (by rfl) ⟨30048, by rfl⟩) (B 60097 (by norm_num) ⟨30048, by rfl⟩ (by norm_num))
theorem R178469 : Reach 178469 := rs (se 4 (by rfl) ⟨16731, by rfl⟩) (B 33463 (by norm_num) ⟨16731, by rfl⟩ (by norm_num))
theorem R145709 : Reach 145709 := rs (se 3 (by rfl) ⟨27320, by rfl⟩) (B 54641 (by norm_num) ⟨27320, by rfl⟩ (by norm_num))
theorem R407861 : Reach 407861 := rs (se 5 (by rfl) ⟨19118, by rfl⟩) (B 38237 (by norm_num) ⟨19118, by rfl⟩ (by norm_num))
theorem R637237 : Reach 637237 := rs (se 5 (by rfl) ⟨29870, by rfl⟩) (B 59741 (by norm_num) ⟨29870, by rfl⟩ (by norm_num))
theorem R80185 : Reach 80185 := rs (se 2 (by rfl) ⟨30069, by rfl⟩) (B 60139 (by norm_num) ⟨30069, by rfl⟩ (by norm_num))
theorem R211285 : Reach 211285 := rs (se 10 (by rfl) ⟨309, by rfl⟩) (B 619 (by norm_num) ⟨309, by rfl⟩ (by norm_num))
theorem R112981 : Reach 112981 := rs (se 10 (by rfl) ⟨165, by rfl⟩) (B 331 (by norm_num) ⟨165, by rfl⟩ (by norm_num))
theorem R145781 : Reach 145781 := rs (se 5 (by rfl) ⟨6833, by rfl⟩) (B 13667 (by norm_num) ⟨6833, by rfl⟩ (by norm_num))
theorem R80281 : Reach 80281 := rs (se 2 (by rfl) ⟨30105, by rfl⟩) (B 60211 (by norm_num) ⟨30105, by rfl⟩ (by norm_num))
theorem R113069 : Reach 113069 := rs (se 3 (by rfl) ⟨21200, by rfl⟩) (B 42401 (by norm_num) ⟨21200, by rfl⟩ (by norm_num))
theorem R145853 : Reach 145853 := rs (se 3 (by rfl) ⟨27347, by rfl⟩) (B 54695 (by norm_num) ⟨27347, by rfl⟩ (by norm_num))
theorem R276965 : Reach 276965 := rs (se 4 (by rfl) ⟨25965, by rfl⟩) (B 51931 (by norm_num) ⟨25965, by rfl⟩ (by norm_num))
theorem R80357 : Reach 80357 := rs (se 4 (by rfl) ⟨7533, by rfl⟩) (B 15067 (by norm_num) ⟨7533, by rfl⟩ (by norm_num))
theorem R145925 : Reach 145925 := rs (se 4 (by rfl) ⟨13680, by rfl⟩) (B 27361 (by norm_num) ⟨13680, by rfl⟩ (by norm_num))
theorem R113197 : Reach 113197 := rs (se 3 (by rfl) ⟨21224, by rfl⟩) (B 42449 (by norm_num) ⟨21224, by rfl⟩ (by norm_num))
theorem R80453 : Reach 80453 := rs (se 4 (by rfl) ⟨7542, by rfl⟩) (B 15085 (by norm_num) ⟨7542, by rfl⟩ (by norm_num))
theorem R145997 : Reach 145997 := rs (se 3 (by rfl) ⟨27374, by rfl⟩) (B 54749 (by norm_num) ⟨27374, by rfl⟩ (by norm_num))
theorem R80509 : Reach 80509 := rs (se 3 (by rfl) ⟨15095, by rfl⟩) (B 30191 (by norm_num) ⟨15095, by rfl⟩ (by norm_num))
theorem R146069 : Reach 146069 := rs (se 6 (by rfl) ⟨3423, by rfl⟩) (B 6847 (by norm_num) ⟨3423, by rfl⟩ (by norm_num))
theorem R146141 : Reach 146141 := rs (se 3 (by rfl) ⟨27401, by rfl⟩) (B 54803 (by norm_num) ⟨27401, by rfl⟩ (by norm_num))
theorem R80605 : Reach 80605 := rs (se 3 (by rfl) ⟨15113, by rfl⟩) (B 30227 (by norm_num) ⟨15113, by rfl⟩ (by norm_num))
theorem R146213 : Reach 146213 := rs (se 4 (by rfl) ⟨13707, by rfl⟩) (B 27415 (by norm_num) ⟨13707, by rfl⟩ (by norm_num))
theorem R244565 : Reach 244565 := rs (se 9 (by rfl) ⟨716, by rfl⟩) (B 1433 (by norm_num) ⟨716, by rfl⟩ (by norm_num))
theorem R146285 : Reach 146285 := rs (se 3 (by rfl) ⟨27428, by rfl⟩) (B 54857 (by norm_num) ⟨27428, by rfl⟩ (by norm_num))
theorem R80777 : Reach 80777 := rs (se 2 (by rfl) ⟨30291, by rfl⟩) (B 60583 (by norm_num) ⟨30291, by rfl⟩ (by norm_num))
theorem R146357 : Reach 146357 := rs (se 5 (by rfl) ⟨6860, by rfl⟩) (B 13721 (by norm_num) ⟨6860, by rfl⟩ (by norm_num))
theorem R80833 : Reach 80833 := rs (se 2 (by rfl) ⟨30312, by rfl⟩) (B 60625 (by norm_num) ⟨30312, by rfl⟩ (by norm_num))
theorem R146429 : Reach 146429 := rs (se 3 (by rfl) ⟨27455, by rfl⟩) (B 54911 (by norm_num) ⟨27455, by rfl⟩ (by norm_num))
theorem R80929 : Reach 80929 := rs (se 2 (by rfl) ⟨30348, by rfl⟩) (B 60697 (by norm_num) ⟨30348, by rfl⟩ (by norm_num))
theorem R146501 : Reach 146501 := rs (se 4 (by rfl) ⟨13734, by rfl⟩) (B 27469 (by norm_num) ⟨13734, by rfl⟩ (by norm_num))
theorem R244853 : Reach 244853 := rs (se 5 (by rfl) ⟨11477, by rfl⟩) (B 22955 (by norm_num) ⟨11477, by rfl⟩ (by norm_num))
theorem R146573 : Reach 146573 := rs (se 3 (by rfl) ⟨27482, by rfl⟩) (B 54965 (by norm_num) ⟨27482, by rfl⟩ (by norm_num))
theorem R113861 : Reach 113861 := rs (se 4 (by rfl) ⟨10674, by rfl⟩) (B 21349 (by norm_num) ⟨10674, by rfl⟩ (by norm_num))
theorem R81101 : Reach 81101 := rs (se 3 (by rfl) ⟨15206, by rfl⟩) (B 30413 (by norm_num) ⟨15206, by rfl⟩ (by norm_num))
theorem R146645 : Reach 146645 := rs (se 7 (by rfl) ⟨1718, by rfl⟩) (B 3437 (by norm_num) ⟨1718, by rfl⟩ (by norm_num))
theorem R81157 : Reach 81157 := rs (se 4 (by rfl) ⟨7608, by rfl⟩) (B 15217 (by norm_num) ⟨7608, by rfl⟩ (by norm_num))
theorem R146717 : Reach 146717 := rs (se 3 (by rfl) ⟨27509, by rfl⟩) (B 55019 (by norm_num) ⟨27509, by rfl⟩ (by norm_num))
theorem R146789 : Reach 146789 := rs (se 4 (by rfl) ⟨13761, by rfl⟩) (B 27523 (by norm_num) ⟨13761, by rfl⟩ (by norm_num))
theorem R81253 : Reach 81253 := rs (se 4 (by rfl) ⟨7617, by rfl⟩) (B 15235 (by norm_num) ⟨7617, by rfl⟩ (by norm_num))
theorem R540053 : Reach 540053 := rs (se 6 (by rfl) ⟨12657, by rfl⟩) (B 25315 (by norm_num) ⟨12657, by rfl⟩ (by norm_num))
theorem R146861 : Reach 146861 := rs (se 3 (by rfl) ⟨27536, by rfl⟩) (B 55073 (by norm_num) ⟨27536, by rfl⟩ (by norm_num))
theorem R114149 : Reach 114149 := rs (se 4 (by rfl) ⟨10701, by rfl⟩) (B 21403 (by norm_num) ⟨10701, by rfl⟩ (by norm_num))
theorem R146933 : Reach 146933 := rs (se 5 (by rfl) ⟨6887, by rfl⟩) (B 13775 (by norm_num) ⟨6887, by rfl⟩ (by norm_num))
theorem R81425 : Reach 81425 := rs (se 2 (by rfl) ⟨30534, by rfl⟩) (B 61069 (by norm_num) ⟨30534, by rfl⟩ (by norm_num))
theorem R147005 : Reach 147005 := rs (se 3 (by rfl) ⟨27563, by rfl⟩) (B 55127 (by norm_num) ⟨27563, by rfl⟩ (by norm_num))
theorem R81481 : Reach 81481 := rs (se 2 (by rfl) ⟨30555, by rfl⟩) (B 61111 (by norm_num) ⟨30555, by rfl⟩ (by norm_num))
theorem R179813 : Reach 179813 := rs (se 4 (by rfl) ⟨16857, by rfl⟩) (B 33715 (by norm_num) ⟨16857, by rfl⟩ (by norm_num))
theorem R114293 : Reach 114293 := rs (se 5 (by rfl) ⟨5357, by rfl⟩) (B 10715 (by norm_num) ⟨5357, by rfl⟩ (by norm_num))
theorem R147077 : Reach 147077 := rs (se 4 (by rfl) ⟨13788, by rfl⟩) (B 27577 (by norm_num) ⟨13788, by rfl⟩ (by norm_num))
theorem R212645 : Reach 212645 := rs (se 4 (by rfl) ⟨19935, by rfl⟩) (B 39871 (by norm_num) ⟨19935, by rfl⟩ (by norm_num))
theorem R81577 : Reach 81577 := rs (se 2 (by rfl) ⟨30591, by rfl⟩) (B 61183 (by norm_num) ⟨30591, by rfl⟩ (by norm_num))
theorem R147149 : Reach 147149 := rs (se 3 (by rfl) ⟨27590, by rfl⟩) (B 55181 (by norm_num) ⟨27590, by rfl⟩ (by norm_num))
theorem R147221 : Reach 147221 := rs (se 6 (by rfl) ⟨3450, by rfl⟩) (B 6901 (by norm_num) ⟨3450, by rfl⟩ (by norm_num))
theorem R180053 : Reach 180053 := rs (se 9 (by rfl) ⟨527, by rfl⟩) (B 1055 (by norm_num) ⟨527, by rfl⟩ (by norm_num))
theorem R81749 : Reach 81749 := rs (se 9 (by rfl) ⟨239, by rfl⟩) (B 479 (by norm_num) ⟨239, by rfl⟩ (by norm_num))
theorem R147293 : Reach 147293 := rs (se 3 (by rfl) ⟨27617, by rfl⟩) (B 55235 (by norm_num) ⟨27617, by rfl⟩ (by norm_num))
theorem R81757 : Reach 81757 := rs (se 3 (by rfl) ⟨15329, by rfl⟩) (B 30659 (by norm_num) ⟨15329, by rfl⟩ (by norm_num))
theorem R81805 : Reach 81805 := rs (se 3 (by rfl) ⟨15338, by rfl⟩) (B 30677 (by norm_num) ⟨15338, by rfl⟩ (by norm_num))
theorem R147365 : Reach 147365 := rs (se 4 (by rfl) ⟨13815, by rfl⟩) (B 27631 (by norm_num) ⟨13815, by rfl⟩ (by norm_num))
theorem R376757 : Reach 376757 := rs (se 5 (by rfl) ⟨17660, by rfl⟩) (B 35321 (by norm_num) ⟨17660, by rfl⟩ (by norm_num))
theorem R81901 : Reach 81901 := rs (se 3 (by rfl) ⟨15356, by rfl⟩) (B 30713 (by norm_num) ⟨15356, by rfl⟩ (by norm_num))
theorem R147437 : Reach 147437 := rs (se 3 (by rfl) ⟨27644, by rfl⟩) (B 55289 (by norm_num) ⟨27644, by rfl⟩ (by norm_num))
theorem R180245 : Reach 180245 := rs (se 6 (by rfl) ⟨4224, by rfl⟩) (B 8449 (by norm_num) ⟨4224, by rfl⟩ (by norm_num))
theorem R147509 : Reach 147509 := rs (se 5 (by rfl) ⟨6914, by rfl⟩) (B 13829 (by norm_num) ⟨6914, by rfl⟩ (by norm_num))
theorem R114797 : Reach 114797 := rs (se 3 (by rfl) ⟨21524, by rfl⟩) (B 43049 (by norm_num) ⟨21524, by rfl⟩ (by norm_num))
theorem R147581 : Reach 147581 := rs (se 3 (by rfl) ⟨27671, by rfl⟩) (B 55343 (by norm_num) ⟨27671, by rfl⟩ (by norm_num))
theorem R82073 : Reach 82073 := rs (se 2 (by rfl) ⟨30777, by rfl⟩) (B 61555 (by norm_num) ⟨30777, by rfl⟩ (by norm_num))
theorem R114869 : Reach 114869 := rs (se 5 (by rfl) ⟨5384, by rfl⟩) (B 10769 (by norm_num) ⟨5384, by rfl⟩ (by norm_num))
theorem R147653 : Reach 147653 := rs (se 4 (by rfl) ⟨13842, by rfl⟩) (B 27685 (by norm_num) ⟨13842, by rfl⟩ (by norm_num))
theorem R82129 : Reach 82129 := rs (se 2 (by rfl) ⟨30798, by rfl⟩) (B 61597 (by norm_num) ⟨30798, by rfl⟩ (by norm_num))
theorem R278741 : Reach 278741 := rs (se 7 (by rfl) ⟨3266, by rfl⟩) (B 6533 (by norm_num) ⟨3266, by rfl⟩ (by norm_num))
theorem R147725 : Reach 147725 := rs (se 3 (by rfl) ⟨27698, by rfl⟩) (B 55397 (by norm_num) ⟨27698, by rfl⟩ (by norm_num))
theorem R246037 : Reach 246037 := rs (se 6 (by rfl) ⟨5766, by rfl⟩) (B 11533 (by norm_num) ⟨5766, by rfl⟩ (by norm_num))
theorem R82225 : Reach 82225 := rs (se 2 (by rfl) ⟨30834, by rfl⟩) (B 61669 (by norm_num) ⟨30834, by rfl⟩ (by norm_num))
theorem R147797 : Reach 147797 := rs (se 10 (by rfl) ⟨216, by rfl⟩) (B 433 (by norm_num) ⟨216, by rfl⟩ (by norm_num))
theorem R147869 : Reach 147869 := rs (se 3 (by rfl) ⟨27725, by rfl⟩) (B 55451 (by norm_num) ⟨27725, by rfl⟩ (by norm_num))
theorem R213461 : Reach 213461 := rs (se 7 (by rfl) ⟨2501, by rfl⟩) (B 5003 (by norm_num) ⟨2501, by rfl⟩ (by norm_num))
theorem R82397 : Reach 82397 := rs (se 3 (by rfl) ⟨15449, by rfl⟩) (B 30899 (by norm_num) ⟨15449, by rfl⟩ (by norm_num))
theorem R147941 : Reach 147941 := rs (se 4 (by rfl) ⟨13869, by rfl⟩) (B 27739 (by norm_num) ⟨13869, by rfl⟩ (by norm_num))
theorem R82453 : Reach 82453 := rs (se 6 (by rfl) ⟨1932, by rfl⟩) (B 3865 (by norm_num) ⟨1932, by rfl⟩ (by norm_num))
theorem R148013 : Reach 148013 := rs (se 3 (by rfl) ⟨27752, by rfl⟩) (B 55505 (by norm_num) ⟨27752, by rfl⟩ (by norm_num))
theorem R246341 : Reach 246341 := rs (se 4 (by rfl) ⟨23094, by rfl⟩) (B 46189 (by norm_num) ⟨23094, by rfl⟩ (by norm_num))
theorem R82549 : Reach 82549 := rs (se 5 (by rfl) ⟨3869, by rfl⟩) (B 7739 (by norm_num) ⟨3869, by rfl⟩ (by norm_num))
theorem R148085 : Reach 148085 := rs (se 5 (by rfl) ⟨6941, by rfl⟩) (B 13883 (by norm_num) ⟨6941, by rfl⟩ (by norm_num))
theorem R148157 : Reach 148157 := rs (se 3 (by rfl) ⟨27779, by rfl⟩) (B 55559 (by norm_num) ⟨27779, by rfl⟩ (by norm_num))
theorem R541397 : Reach 541397 := rs (se 7 (by rfl) ⟨6344, by rfl⟩) (B 12689 (by norm_num) ⟨6344, by rfl⟩ (by norm_num))
theorem R148229 : Reach 148229 := rs (se 4 (by rfl) ⟨13896, by rfl⟩) (B 27793 (by norm_num) ⟨13896, by rfl⟩ (by norm_num))
theorem R82721 : Reach 82721 := rs (se 2 (by rfl) ⟨31020, by rfl⟩) (B 62041 (by norm_num) ⟨31020, by rfl⟩ (by norm_num))
theorem R148301 : Reach 148301 := rs (se 3 (by rfl) ⟨27806, by rfl⟩) (B 55613 (by norm_num) ⟨27806, by rfl⟩ (by norm_num))
theorem R82777 : Reach 82777 := rs (se 2 (by rfl) ⟨31041, by rfl⟩) (B 62083 (by norm_num) ⟨31041, by rfl⟩ (by norm_num))
theorem R213893 : Reach 213893 := rs (se 4 (by rfl) ⟨20052, by rfl⟩) (B 40105 (by norm_num) ⟨20052, by rfl⟩ (by norm_num))
theorem R148373 : Reach 148373 := rs (se 6 (by rfl) ⟨3477, by rfl⟩) (B 6955 (by norm_num) ⟨3477, by rfl⟩ (by norm_num))
theorem R82873 : Reach 82873 := rs (se 2 (by rfl) ⟨31077, by rfl⟩) (B 62155 (by norm_num) ⟨31077, by rfl⟩ (by norm_num))
theorem R148445 : Reach 148445 := rs (se 3 (by rfl) ⟨27833, by rfl⟩) (B 55667 (by norm_num) ⟨27833, by rfl⟩ (by norm_num))
theorem R181237 : Reach 181237 := rs (se 5 (by rfl) ⟨8495, by rfl⟩) (B 16991 (by norm_num) ⟨8495, by rfl⟩ (by norm_num))
theorem R148517 : Reach 148517 := rs (se 4 (by rfl) ⟨13923, by rfl⟩) (B 27847 (by norm_num) ⟨13923, by rfl⟩ (by norm_num))
theorem R83045 : Reach 83045 := rs (se 4 (by rfl) ⟨7785, by rfl⟩) (B 15571 (by norm_num) ⟨7785, by rfl⟩ (by norm_num))
theorem R148589 : Reach 148589 := rs (se 3 (by rfl) ⟨27860, by rfl⟩) (B 55721 (by norm_num) ⟨27860, by rfl⟩ (by norm_num))
theorem R181397 : Reach 181397 := rs (se 6 (by rfl) ⟨4251, by rfl⟩) (B 8503 (by norm_num) ⟨4251, by rfl⟩ (by norm_num))
theorem R83101 : Reach 83101 := rs (se 3 (by rfl) ⟨15581, by rfl⟩) (B 31163 (by norm_num) ⟨15581, by rfl⟩ (by norm_num))
theorem R148661 : Reach 148661 := rs (se 5 (by rfl) ⟨6968, by rfl⟩) (B 13937 (by norm_num) ⟨6968, by rfl⟩ (by norm_num))
theorem R83197 : Reach 83197 := rs (se 3 (by rfl) ⟨15599, by rfl⟩) (B 31199 (by norm_num) ⟨15599, by rfl⟩ (by norm_num))
theorem R148733 : Reach 148733 := rs (se 3 (by rfl) ⟨27887, by rfl⟩) (B 55775 (by norm_num) ⟨27887, by rfl⟩ (by norm_num))
theorem R83201 : Reach 83201 := rs (se 2 (by rfl) ⟨31200, by rfl⟩) (B 62401 (by norm_num) ⟨31200, by rfl⟩ (by norm_num))
theorem R214325 : Reach 214325 := rs (se 5 (by rfl) ⟨10046, by rfl⟩) (B 20093 (by norm_num) ⟨10046, by rfl⟩ (by norm_num))
theorem R148805 : Reach 148805 := rs (se 4 (by rfl) ⟨13950, by rfl⟩) (B 27901 (by norm_num) ⟨13950, by rfl⟩ (by norm_num))
theorem R673109 : Reach 673109 := rs (se 12 (by rfl) ⟨246, by rfl⟩) (B 493 (by norm_num) ⟨246, by rfl⟩ (by norm_num))
theorem R148877 : Reach 148877 := rs (se 3 (by rfl) ⟨27914, by rfl⟩) (B 55829 (by norm_num) ⟨27914, by rfl⟩ (by norm_num))
theorem R83369 : Reach 83369 := rs (se 2 (by rfl) ⟨31263, by rfl⟩) (B 62527 (by norm_num) ⟨31263, by rfl⟩ (by norm_num))
theorem R148949 : Reach 148949 := rs (se 7 (by rfl) ⟨1745, by rfl⟩) (B 3491 (by norm_num) ⟨1745, by rfl⟩ (by norm_num))
theorem R83425 : Reach 83425 := rs (se 2 (by rfl) ⟨31284, by rfl⟩) (B 62569 (by norm_num) ⟨31284, by rfl⟩ (by norm_num))
theorem R149021 : Reach 149021 := rs (se 3 (by rfl) ⟨27941, by rfl⟩) (B 55883 (by norm_num) ⟨27941, by rfl⟩ (by norm_num))
theorem R83521 : Reach 83521 := rs (se 2 (by rfl) ⟨31320, by rfl⟩) (B 62641 (by norm_num) ⟨31320, by rfl⟩ (by norm_num))
theorem R149093 : Reach 149093 := rs (se 4 (by rfl) ⟨13977, by rfl⟩) (B 27955 (by norm_num) ⟨13977, by rfl⟩ (by norm_num))
theorem R149165 : Reach 149165 := rs (se 3 (by rfl) ⟨27968, by rfl⟩) (B 55937 (by norm_num) ⟨27968, by rfl⟩ (by norm_num))
theorem R214757 : Reach 214757 := rs (se 4 (by rfl) ⟨20133, by rfl⟩) (B 40267 (by norm_num) ⟨20133, by rfl⟩ (by norm_num))
theorem R83693 : Reach 83693 := rs (se 3 (by rfl) ⟨15692, by rfl⟩) (B 31385 (by norm_num) ⟨15692, by rfl⟩ (by norm_num))
theorem R149237 : Reach 149237 := rs (se 5 (by rfl) ⟨6995, by rfl⟩) (B 13991 (by norm_num) ⟨6995, by rfl⟩ (by norm_num))
theorem R83749 : Reach 83749 := rs (se 4 (by rfl) ⟨7851, by rfl⟩) (B 15703 (by norm_num) ⟨7851, by rfl⟩ (by norm_num))
theorem R149309 : Reach 149309 := rs (se 3 (by rfl) ⟨27995, by rfl⟩) (B 55991 (by norm_num) ⟨27995, by rfl⟩ (by norm_num))
theorem R83845 : Reach 83845 := rs (se 4 (by rfl) ⟨7860, by rfl⟩) (B 15721 (by norm_num) ⟨7860, by rfl⟩ (by norm_num))
theorem R149381 : Reach 149381 := rs (se 4 (by rfl) ⟨14004, by rfl⟩) (B 28009 (by norm_num) ⟨14004, by rfl⟩ (by norm_num))
theorem R313237 : Reach 313237 := rs (se 6 (by rfl) ⟨7341, by rfl⟩) (B 14683 (by norm_num) ⟨7341, by rfl⟩ (by norm_num))
theorem R149453 : Reach 149453 := rs (se 3 (by rfl) ⟨28022, by rfl⟩) (B 56045 (by norm_num) ⟨28022, by rfl⟩ (by norm_num))
theorem R149525 : Reach 149525 := rs (se 6 (by rfl) ⟨3504, by rfl⟩) (B 7009 (by norm_num) ⟨3504, by rfl⟩ (by norm_num))
theorem R84017 : Reach 84017 := rs (se 2 (by rfl) ⟨31506, by rfl⟩) (B 63013 (by norm_num) ⟨31506, by rfl⟩ (by norm_num))
theorem R182341 : Reach 182341 := rs (se 4 (by rfl) ⟨17094, by rfl⟩) (B 34189 (by norm_num) ⟨17094, by rfl⟩ (by norm_num))
theorem R149597 : Reach 149597 := rs (se 3 (by rfl) ⟨28049, by rfl⟩) (B 56099 (by norm_num) ⟨28049, by rfl⟩ (by norm_num))
theorem R84073 : Reach 84073 := rs (se 2 (by rfl) ⟨31527, by rfl⟩) (B 63055 (by norm_num) ⟨31527, by rfl⟩ (by norm_num))
theorem R215189 : Reach 215189 := rs (se 6 (by rfl) ⟨5043, by rfl⟩) (B 10087 (by norm_num) ⟨5043, by rfl⟩ (by norm_num))
theorem R149669 : Reach 149669 := rs (se 4 (by rfl) ⟨14031, by rfl⟩) (B 28063 (by norm_num) ⟨14031, by rfl⟩ (by norm_num))
theorem R215237 : Reach 215237 := rs (se 4 (by rfl) ⟨20178, by rfl⟩) (B 40357 (by norm_num) ⟨20178, by rfl⟩ (by norm_num))
theorem R149741 : Reach 149741 := rs (se 3 (by rfl) ⟨28076, by rfl⟩) (B 56153 (by norm_num) ⟨28076, by rfl⟩ (by norm_num))
theorem R149813 : Reach 149813 := rs (se 5 (by rfl) ⟨7022, by rfl⟩) (B 14045 (by norm_num) ⟨7022, by rfl⟩ (by norm_num))
theorem R84341 : Reach 84341 := rs (se 5 (by rfl) ⟨3953, by rfl⟩) (B 7907 (by norm_num) ⟨3953, by rfl⟩ (by norm_num))
theorem R149885 : Reach 149885 := rs (se 3 (by rfl) ⟨28103, by rfl⟩) (B 56207 (by norm_num) ⟨28103, by rfl⟩ (by norm_num))
theorem R84397 : Reach 84397 := rs (se 3 (by rfl) ⟨15824, by rfl⟩) (B 31649 (by norm_num) ⟨15824, by rfl⟩ (by norm_num))
theorem R149957 : Reach 149957 := rs (se 4 (by rfl) ⟨14058, by rfl⟩) (B 28117 (by norm_num) ⟨14058, by rfl⟩ (by norm_num))
theorem R150029 : Reach 150029 := rs (se 3 (by rfl) ⟨28130, by rfl⟩) (B 56261 (by norm_num) ⟨28130, by rfl⟩ (by norm_num))
theorem R84493 : Reach 84493 := rs (se 3 (by rfl) ⟨15842, by rfl⟩) (B 31685 (by norm_num) ⟨15842, by rfl⟩ (by norm_num))
theorem R215621 : Reach 215621 := rs (se 4 (by rfl) ⟨20214, by rfl⟩) (B 40429 (by norm_num) ⟨20214, by rfl⟩ (by norm_num))
theorem R150101 : Reach 150101 := rs (se 8 (by rfl) ⟨879, by rfl⟩) (B 1759 (by norm_num) ⟨879, by rfl⟩ (by norm_num))
theorem R248453 : Reach 248453 := rs (se 4 (by rfl) ⟨23292, by rfl⟩) (B 46585 (by norm_num) ⟨23292, by rfl⟩ (by norm_num))
theorem R150173 : Reach 150173 := rs (se 3 (by rfl) ⟨28157, by rfl⟩) (B 56315 (by norm_num) ⟨28157, by rfl⟩ (by norm_num))
theorem R346837 : Reach 346837 := rs (se 7 (by rfl) ⟨4064, by rfl⟩) (B 8129 (by norm_num) ⟨4064, by rfl⟩ (by norm_num))
theorem R150245 : Reach 150245 := rs (se 4 (by rfl) ⟨14085, by rfl⟩) (B 28171 (by norm_num) ⟨14085, by rfl⟩ (by norm_num))
theorem R150317 : Reach 150317 := rs (se 3 (by rfl) ⟨28184, by rfl⟩) (B 56369 (by norm_num) ⟨28184, by rfl⟩ (by norm_num))
theorem R84829 : Reach 84829 := rs (se 3 (by rfl) ⟨15905, by rfl⟩) (B 31811 (by norm_num) ⟨15905, by rfl⟩ (by norm_num))
theorem R150389 : Reach 150389 := rs (se 5 (by rfl) ⟨7049, by rfl⟩) (B 14099 (by norm_num) ⟨7049, by rfl⟩ (by norm_num))
theorem R248741 : Reach 248741 := rs (se 4 (by rfl) ⟨23319, by rfl⟩) (B 46639 (by norm_num) ⟨23319, by rfl⟩ (by norm_num))
theorem R478133 : Reach 478133 := rs (se 5 (by rfl) ⟨22412, by rfl⟩) (B 44825 (by norm_num) ⟨22412, by rfl⟩ (by norm_num))
theorem R150461 : Reach 150461 := rs (se 3 (by rfl) ⟨28211, by rfl⟩) (B 56423 (by norm_num) ⟨28211, by rfl⟩ (by norm_num))
theorem R216053 : Reach 216053 := rs (se 5 (by rfl) ⟨10127, by rfl⟩) (B 20255 (by norm_num) ⟨10127, by rfl⟩ (by norm_num))
theorem R150533 : Reach 150533 := rs (se 4 (by rfl) ⟨14112, by rfl⟩) (B 28225 (by norm_num) ⟨14112, by rfl⟩ (by norm_num))
theorem R150605 : Reach 150605 := rs (se 3 (by rfl) ⟨28238, by rfl⟩) (B 56477 (by norm_num) ⟨28238, by rfl⟩ (by norm_num))
theorem R150677 : Reach 150677 := rs (se 6 (by rfl) ⟨3531, by rfl⟩) (B 7063 (by norm_num) ⟨3531, by rfl⟩ (by norm_num))
theorem R150749 : Reach 150749 := rs (se 3 (by rfl) ⟨28265, by rfl⟩) (B 56531 (by norm_num) ⟨28265, by rfl⟩ (by norm_num))
theorem R150821 : Reach 150821 := rs (se 4 (by rfl) ⟨14139, by rfl⟩) (B 28279 (by norm_num) ⟨14139, by rfl⟩ (by norm_num))
theorem R118093 : Reach 118093 := rs (se 3 (by rfl) ⟨22142, by rfl⟩) (B 44285 (by norm_num) ⟨22142, by rfl⟩ (by norm_num))
theorem R150893 : Reach 150893 := rs (se 3 (by rfl) ⟨28292, by rfl⟩) (B 56585 (by norm_num) ⟨28292, by rfl⟩ (by norm_num))
theorem R216485 : Reach 216485 := rs (se 4 (by rfl) ⟨20295, by rfl⟩) (B 40591 (by norm_num) ⟨20295, by rfl⟩ (by norm_num))
theorem R150965 : Reach 150965 := rs (se 5 (by rfl) ⟨7076, by rfl⟩) (B 14153 (by norm_num) ⟨7076, by rfl⟩ (by norm_num))
theorem R183845 : Reach 183845 := rs (se 4 (by rfl) ⟨17235, by rfl⟩) (B 34471 (by norm_num) ⟨17235, by rfl⟩ (by norm_num))
theorem R118381 : Reach 118381 := rs (se 3 (by rfl) ⟨22196, by rfl⟩) (B 44393 (by norm_num) ⟨22196, by rfl⟩ (by norm_num))
theorem R216917 : Reach 216917 := rs (se 9 (by rfl) ⟨635, by rfl⟩) (B 1271 (by norm_num) ⟨635, by rfl⟩ (by norm_num))
theorem R413525 : Reach 413525 := rs (se 9 (by rfl) ⟨1211, by rfl⟩) (B 2423 (by norm_num) ⟨1211, by rfl⟩ (by norm_num))
theorem R2117461 : Reach 2117461 := rs (se 9 (by rfl) ⟨6203, by rfl⟩) (B 12407 (by norm_num) ⟨6203, by rfl⟩ (by norm_num))
theorem R249925 : Reach 249925 := rs (se 4 (by rfl) ⟨23430, by rfl⟩) (B 46861 (by norm_num) ⟨23430, by rfl⟩ (by norm_num))
theorem R151733 : Reach 151733 := rs (se 5 (by rfl) ⟨7112, by rfl⟩) (B 14225 (by norm_num) ⟨7112, by rfl⟩ (by norm_num))
theorem R217349 : Reach 217349 := rs (se 4 (by rfl) ⟨20376, by rfl⟩) (B 40753 (by norm_num) ⟨20376, by rfl⟩ (by norm_num))
theorem R86293 : Reach 86293 := rs (se 6 (by rfl) ⟨2022, by rfl⟩) (B 4045 (by norm_num) ⟨2022, by rfl⟩ (by norm_num))
theorem R151877 : Reach 151877 := rs (se 4 (by rfl) ⟨14238, by rfl⟩) (B 28477 (by norm_num) ⟨14238, by rfl⟩ (by norm_num))
theorem R250229 : Reach 250229 := rs (se 5 (by rfl) ⟨11729, by rfl⟩) (B 23459 (by norm_num) ⟨11729, by rfl⟩ (by norm_num))
theorem R283013 : Reach 283013 := rs (se 4 (by rfl) ⟨26532, by rfl⟩) (B 53065 (by norm_num) ⟨26532, by rfl⟩ (by norm_num))
theorem R217637 : Reach 217637 := rs (se 4 (by rfl) ⟨20403, by rfl⟩) (B 40807 (by norm_num) ⟨20403, by rfl⟩ (by norm_num))
theorem R348725 : Reach 348725 := rs (se 5 (by rfl) ⟨16346, by rfl⟩) (B 32693 (by norm_num) ⟨16346, by rfl⟩ (by norm_num))
theorem R217781 : Reach 217781 := rs (se 5 (by rfl) ⟨10208, by rfl⟩) (B 20417 (by norm_num) ⟨10208, by rfl⟩ (by norm_num))
theorem R119477 : Reach 119477 := rs (se 5 (by rfl) ⟨5600, by rfl⟩) (B 11201 (by norm_num) ⟨5600, by rfl⟩ (by norm_num))
theorem R349109 : Reach 349109 := rs (se 5 (by rfl) ⟨16364, by rfl⟩) (B 32729 (by norm_num) ⟨16364, by rfl⟩ (by norm_num))
theorem R152621 : Reach 152621 := rs (se 3 (by rfl) ⟨28616, by rfl⟩) (B 57233 (by norm_num) ⟨28616, by rfl⟩ (by norm_num))
theorem R185429 : Reach 185429 := rs (se 8 (by rfl) ⟨1086, by rfl⟩) (B 2173 (by norm_num) ⟨1086, by rfl⟩ (by norm_num))
theorem R218213 : Reach 218213 := rs (se 4 (by rfl) ⟨20457, by rfl⟩) (B 40915 (by norm_num) ⟨20457, by rfl⟩ (by norm_num))
theorem R250997 : Reach 250997 := rs (se 5 (by rfl) ⟨11765, by rfl⟩) (B 23531 (by norm_num) ⟨11765, by rfl⟩ (by norm_num))
theorem R119981 : Reach 119981 := rs (se 3 (by rfl) ⟨22496, by rfl⟩) (B 44993 (by norm_num) ⟨22496, by rfl⟩ (by norm_num))
theorem R1823957 : Reach 1823957 := rs (se 7 (by rfl) ⟨21374, by rfl⟩) (B 42749 (by norm_num) ⟨21374, by rfl⟩ (by norm_num))
theorem R152813 : Reach 152813 := rs (se 3 (by rfl) ⟨28652, by rfl⟩) (B 57305 (by norm_num) ⟨28652, by rfl⟩ (by norm_num))
theorem R120133 : Reach 120133 := rs (se 4 (by rfl) ⟨11262, by rfl⟩) (B 22525 (by norm_num) ⟨11262, by rfl⟩ (by norm_num))
theorem R1037717 : Reach 1037717 := rs (se 6 (by rfl) ⟨24321, by rfl⟩) (B 48643 (by norm_num) ⟨24321, by rfl⟩ (by norm_num))
theorem R218645 : Reach 218645 := rs (se 6 (by rfl) ⟨5124, by rfl⟩) (B 10249 (by norm_num) ⟨5124, by rfl⟩ (by norm_num))
theorem R120437 : Reach 120437 := rs (se 5 (by rfl) ⟨5645, by rfl⟩) (B 11291 (by norm_num) ⟨5645, by rfl⟩ (by norm_num))
theorem R186101 : Reach 186101 := rs (se 5 (by rfl) ⟨8723, by rfl⟩) (B 17447 (by norm_num) ⟨8723, by rfl⟩ (by norm_num))
theorem R219077 : Reach 219077 := rs (se 4 (by rfl) ⟨20538, by rfl⟩) (B 41077 (by norm_num) ⟨20538, by rfl⟩ (by norm_num))
theorem R120781 : Reach 120781 := rs (se 3 (by rfl) ⟨22646, by rfl⟩) (B 45293 (by norm_num) ⟨22646, by rfl⟩ (by norm_num))
theorem R284789 : Reach 284789 := rs (se 5 (by rfl) ⟨13349, by rfl⟩) (B 26699 (by norm_num) ⟨13349, by rfl⟩ (by norm_num))
theorem R186533 : Reach 186533 := rs (se 4 (by rfl) ⟨17487, by rfl⟩) (B 34975 (by norm_num) ⟨17487, by rfl⟩ (by norm_num))
theorem R317621 : Reach 317621 := rs (se 5 (by rfl) ⟨14888, by rfl⟩) (B 29777 (by norm_num) ⟨14888, by rfl⟩ (by norm_num))
theorem R121189 : Reach 121189 := rs (se 4 (by rfl) ⟨11361, by rfl⟩) (B 22723 (by norm_num) ⟨11361, by rfl⟩ (by norm_num))
theorem R285029 : Reach 285029 := rs (se 4 (by rfl) ⟨26721, by rfl⟩) (B 53443 (by norm_num) ⟨26721, by rfl⟩ (by norm_num))
theorem R219509 : Reach 219509 := rs (se 5 (by rfl) ⟨10289, by rfl⟩) (B 20579 (by norm_num) ⟨10289, by rfl⟩ (by norm_num))
theorem R252341 : Reach 252341 := rs (se 5 (by rfl) ⟨11828, by rfl⟩) (B 23657 (by norm_num) ⟨11828, by rfl⟩ (by norm_num))
theorem R121333 : Reach 121333 := rs (se 5 (by rfl) ⟨5687, by rfl⟩) (B 11375 (by norm_num) ⟨5687, by rfl⟩ (by norm_num))
theorem R88661 : Reach 88661 := rs (se 8 (by rfl) ⟨519, by rfl⟩) (B 1039 (by norm_num) ⟨519, by rfl⟩ (by norm_num))
theorem R350837 : Reach 350837 := rs (se 5 (by rfl) ⟨16445, by rfl⟩) (B 32891 (by norm_num) ⟨16445, by rfl⟩ (by norm_num))
theorem R121493 : Reach 121493 := rs (se 6 (by rfl) ⟨2847, by rfl⟩) (B 5695 (by norm_num) ⟨2847, by rfl⟩ (by norm_num))
theorem R252629 : Reach 252629 := rs (se 7 (by rfl) ⟨2960, by rfl⟩) (B 5921 (by norm_num) ⟨2960, by rfl⟩ (by norm_num))
theorem R154381 : Reach 154381 := rs (se 3 (by rfl) ⟨28946, by rfl⟩) (B 57893 (by norm_num) ⟨28946, by rfl⟩ (by norm_num))
theorem R219941 : Reach 219941 := rs (se 4 (by rfl) ⟨20619, by rfl⟩) (B 41239 (by norm_num) ⟨20619, by rfl⟩ (by norm_num))
theorem R121637 : Reach 121637 := rs (se 4 (by rfl) ⟨11403, by rfl⟩) (B 22807 (by norm_num) ⟨11403, by rfl⟩ (by norm_num))
theorem R187285 : Reach 187285 := rs (se 6 (by rfl) ⟨4389, by rfl⟩) (B 8779 (by norm_num) ⟨4389, by rfl⟩ (by norm_num))
theorem R121925 : Reach 121925 := rs (se 4 (by rfl) ⟨11430, by rfl⟩) (B 22861 (by norm_num) ⟨11430, by rfl⟩ (by norm_num))
theorem R122005 : Reach 122005 := rs (se 6 (by rfl) ⟨2859, by rfl⟩) (B 5719 (by norm_num) ⟨2859, by rfl⟩ (by norm_num))
theorem R220373 : Reach 220373 := rs (se 7 (by rfl) ⟨2582, by rfl⟩) (B 5165 (by norm_num) ⟨2582, by rfl⟩ (by norm_num))
theorem R122077 : Reach 122077 := rs (se 3 (by rfl) ⟨22889, by rfl⟩) (B 45779 (by norm_num) ⟨22889, by rfl⟩ (by norm_num))
theorem R548117 : Reach 548117 := rs (se 6 (by rfl) ⟨12846, by rfl⟩) (B 25693 (by norm_num) ⟨12846, by rfl⟩ (by norm_num))
theorem R154997 : Reach 154997 := rs (se 5 (by rfl) ⟨7265, by rfl⟩) (B 14531 (by norm_num) ⟨7265, by rfl⟩ (by norm_num))
theorem R482773 : Reach 482773 := rs (se 7 (by rfl) ⟨5657, by rfl⟩) (B 11315 (by norm_num) ⟨5657, by rfl⟩ (by norm_num))
theorem R122381 : Reach 122381 := rs (se 3 (by rfl) ⟨22946, by rfl⟩) (B 45893 (by norm_num) ⟨22946, by rfl⟩ (by norm_num))
theorem R220805 : Reach 220805 := rs (se 4 (by rfl) ⟨20700, by rfl⟩) (B 41401 (by norm_num) ⟨20700, by rfl⟩ (by norm_num))
theorem R253813 : Reach 253813 := rs (se 5 (by rfl) ⟨11897, by rfl⟩) (B 23795 (by norm_num) ⟨11897, by rfl⟩ (by norm_num))
theorem R90077 : Reach 90077 := rs (se 3 (by rfl) ⟨16889, by rfl⟩) (B 33779 (by norm_num) ⟨16889, by rfl⟩ (by norm_num))
theorem R221237 : Reach 221237 := rs (se 5 (by rfl) ⟨10370, by rfl⟩) (B 20741 (by norm_num) ⟨10370, by rfl⟩ (by norm_num))
theorem R286805 : Reach 286805 := rs (se 8 (by rfl) ⟨1680, by rfl⟩) (B 3361 (by norm_num) ⟨1680, by rfl⟩ (by norm_num))
theorem R155773 : Reach 155773 := rs (se 3 (by rfl) ⟨29207, by rfl⟩) (B 58415 (by norm_num) ⟨29207, by rfl⟩ (by norm_num))
theorem R254117 : Reach 254117 := rs (se 4 (by rfl) ⟨23823, by rfl⟩) (B 47647 (by norm_num) ⟨23823, by rfl⟩ (by norm_num))
theorem R123133 : Reach 123133 := rs (se 3 (by rfl) ⟨23087, by rfl⟩) (B 46175 (by norm_num) ⟨23087, by rfl⟩ (by norm_num))
theorem R90445 : Reach 90445 := rs (se 3 (by rfl) ⟨16958, by rfl⟩) (B 33917 (by norm_num) ⟨16958, by rfl⟩ (by norm_num))
theorem R123277 : Reach 123277 := rs (se 3 (by rfl) ⟨23114, by rfl⟩) (B 46229 (by norm_num) ⟨23114, by rfl⟩ (by norm_num))
theorem R221669 : Reach 221669 := rs (se 4 (by rfl) ⟨20781, by rfl⟩) (B 41563 (by norm_num) ⟨20781, by rfl⟩ (by norm_num))
theorem R221717 : Reach 221717 := rs (se 6 (by rfl) ⟨5196, by rfl⟩) (B 10393 (by norm_num) ⟨5196, by rfl⟩ (by norm_num))
theorem R123437 : Reach 123437 := rs (se 3 (by rfl) ⟨23144, by rfl⟩) (B 46289 (by norm_num) ⟨23144, by rfl⟩ (by norm_num))
theorem R123581 : Reach 123581 := rs (se 3 (by rfl) ⟨23171, by rfl⟩) (B 46343 (by norm_num) ⟨23171, by rfl⟩ (by norm_num))
theorem R90829 : Reach 90829 := rs (se 3 (by rfl) ⟨17030, by rfl⟩) (B 34061 (by norm_num) ⟨17030, by rfl⟩ (by norm_num))
theorem R156485 : Reach 156485 := rs (se 4 (by rfl) ⟨14670, by rfl⟩) (B 29341 (by norm_num) ⟨14670, by rfl⟩ (by norm_num))
theorem R222101 : Reach 222101 := rs (se 6 (by rfl) ⟨5205, by rfl⟩) (B 10411 (by norm_num) ⟨5205, by rfl⟩ (by norm_num))
theorem R123869 : Reach 123869 := rs (se 3 (by rfl) ⟨23225, by rfl⟩) (B 46451 (by norm_num) ⟨23225, by rfl⟩ (by norm_num))
theorem R320597 : Reach 320597 := rs (se 8 (by rfl) ⟨1878, by rfl⟩) (B 3757 (by norm_num) ⟨1878, by rfl⟩ (by norm_num))
theorem R124021 : Reach 124021 := rs (se 5 (by rfl) ⟨5813, by rfl⟩) (B 11627 (by norm_num) ⟨5813, by rfl⟩ (by norm_num))
theorem R222533 : Reach 222533 := rs (se 4 (by rfl) ⟨20862, by rfl⟩) (B 41725 (by norm_num) ⟨20862, by rfl⟩ (by norm_num))
theorem R124325 : Reach 124325 := rs (se 4 (by rfl) ⟨11655, by rfl⟩) (B 23311 (by norm_num) ⟨11655, by rfl⟩ (by norm_num))
theorem R91621 : Reach 91621 := rs (se 4 (by rfl) ⟨8589, by rfl⟩) (B 17179 (by norm_num) ⟨8589, by rfl⟩ (by norm_num))
theorem R157157 : Reach 157157 := rs (se 4 (by rfl) ⟨14733, by rfl⟩) (B 29467 (by norm_num) ⟨14733, by rfl⟩ (by norm_num))
theorem R190133 : Reach 190133 := rs (se 5 (by rfl) ⟨8912, by rfl⟩) (B 17825 (by norm_num) ⟨8912, by rfl⟩ (by norm_num))
theorem R222965 : Reach 222965 := rs (se 5 (by rfl) ⟨10451, by rfl⟩) (B 20903 (by norm_num) ⟨10451, by rfl⟩ (by norm_num))
theorem R91957 : Reach 91957 := rs (se 5 (by rfl) ⟨4310, by rfl⟩) (B 8621 (by norm_num) ⟨4310, by rfl⟩ (by norm_num))
theorem R92173 : Reach 92173 := rs (se 3 (by rfl) ⟨17282, by rfl⟩) (B 34565 (by norm_num) ⟨17282, by rfl⟩ (by norm_num))
theorem R256117 : Reach 256117 := rs (se 5 (by rfl) ⟨12005, by rfl⟩) (B 24011 (by norm_num) ⟨12005, by rfl⟩ (by norm_num))
theorem R125069 : Reach 125069 := rs (se 3 (by rfl) ⟨23450, by rfl⟩) (B 46901 (by norm_num) ⟨23450, by rfl⟩ (by norm_num))
theorem R125077 : Reach 125077 := rs (se 6 (by rfl) ⟨2931, by rfl⟩) (B 5863 (by norm_num) ⟨2931, by rfl⟩ (by norm_num))
theorem R223397 : Reach 223397 := rs (se 4 (by rfl) ⟨20943, by rfl⟩) (B 41887 (by norm_num) ⟨20943, by rfl⟩ (by norm_num))
theorem R125221 : Reach 125221 := rs (se 4 (by rfl) ⟨11739, by rfl⟩) (B 23479 (by norm_num) ⟨11739, by rfl⟩ (by norm_num))
theorem R321893 : Reach 321893 := rs (se 4 (by rfl) ⟨30177, by rfl⟩) (B 60355 (by norm_num) ⟨30177, by rfl⟩ (by norm_num))
theorem R92549 : Reach 92549 := rs (se 4 (by rfl) ⟨8676, by rfl⟩) (B 17353 (by norm_num) ⟨8676, by rfl⟩ (by norm_num))
theorem R125381 : Reach 125381 := rs (se 4 (by rfl) ⟨11754, by rfl⟩) (B 23509 (by norm_num) ⟨11754, by rfl⟩ (by norm_num))
theorem R125525 : Reach 125525 := rs (se 8 (by rfl) ⟨735, by rfl⟩) (B 1471 (by norm_num) ⟨735, by rfl⟩ (by norm_num))
theorem R223829 : Reach 223829 := rs (se 8 (by rfl) ⟨1311, by rfl⟩) (B 2623 (by norm_num) ⟨1311, by rfl⟩ (by norm_num))
theorem R322309 : Reach 322309 := rs (se 4 (by rfl) ⟨30216, by rfl⟩) (B 60433 (by norm_num) ⟨30216, by rfl⟩ (by norm_num))
theorem R191333 : Reach 191333 := rs (se 4 (by rfl) ⟨17937, by rfl⟩) (B 35875 (by norm_num) ⟨17937, by rfl⟩ (by norm_num))
theorem R125813 : Reach 125813 := rs (se 5 (by rfl) ⟨5897, by rfl⟩) (B 11795 (by norm_num) ⟨5897, by rfl⟩ (by norm_num))
theorem R93053 : Reach 93053 := rs (se 3 (by rfl) ⟨17447, by rfl⟩) (B 34895 (by norm_num) ⟨17447, by rfl⟩ (by norm_num))
theorem R224261 : Reach 224261 := rs (se 4 (by rfl) ⟨21024, by rfl⟩) (B 42049 (by norm_num) ⟨21024, by rfl⟩ (by norm_num))
theorem R125965 : Reach 125965 := rs (se 3 (by rfl) ⟨23618, by rfl⟩) (B 47237 (by norm_num) ⟨23618, by rfl⟩ (by norm_num))
theorem R93253 : Reach 93253 := rs (se 4 (by rfl) ⟨8742, by rfl⟩) (B 17485 (by norm_num) ⟨8742, by rfl⟩ (by norm_num))
theorem R486485 : Reach 486485 := rs (se 8 (by rfl) ⟨2850, by rfl⟩) (B 5701 (by norm_num) ⟨2850, by rfl⟩ (by norm_num))
theorem R224453 : Reach 224453 := rs (se 4 (by rfl) ⟨21042, by rfl⟩) (B 42085 (by norm_num) ⟨21042, by rfl⟩ (by norm_num))
theorem R158917 : Reach 158917 := rs (se 4 (by rfl) ⟨14898, by rfl⟩) (B 29797 (by norm_num) ⟨14898, by rfl⟩ (by norm_num))
theorem R93485 : Reach 93485 := rs (se 3 (by rfl) ⟨17528, by rfl⟩) (B 35057 (by norm_num) ⟨17528, by rfl⟩ (by norm_num))
theorem R126269 : Reach 126269 := rs (se 3 (by rfl) ⟨23675, by rfl⟩) (B 47351 (by norm_num) ⟨23675, by rfl⟩ (by norm_num))
theorem R224693 : Reach 224693 := rs (se 5 (by rfl) ⟨10532, by rfl⟩) (B 21065 (by norm_num) ⟨10532, by rfl⟩ (by norm_num))
theorem R323189 : Reach 323189 := rs (se 5 (by rfl) ⟨15149, by rfl⟩) (B 30299 (by norm_num) ⟨15149, by rfl⟩ (by norm_num))
theorem R93973 : Reach 93973 := rs (se 6 (by rfl) ⟨2202, by rfl⟩) (B 4405 (by norm_num) ⟨2202, by rfl⟩ (by norm_num))
theorem R159533 : Reach 159533 := rs (se 3 (by rfl) ⟨29912, by rfl⟩) (B 59825 (by norm_num) ⟨29912, by rfl⟩ (by norm_num))
theorem R225125 : Reach 225125 := rs (se 4 (by rfl) ⟨21105, by rfl⟩) (B 42211 (by norm_num) ⟨21105, by rfl⟩ (by norm_num))
theorem R127021 : Reach 127021 := rs (se 3 (by rfl) ⟨23816, by rfl⟩) (B 47633 (by norm_num) ⟨23816, by rfl⟩ (by norm_num))
theorem R159853 : Reach 159853 := rs (se 3 (by rfl) ⟨29972, by rfl⟩) (B 59945 (by norm_num) ⟨29972, by rfl⟩ (by norm_num))
theorem R127165 : Reach 127165 := rs (se 3 (by rfl) ⟨23843, by rfl⟩) (B 47687 (by norm_num) ⟨23843, by rfl⟩ (by norm_num))
theorem R159965 : Reach 159965 := rs (se 3 (by rfl) ⟨29993, by rfl⟩) (B 59987 (by norm_num) ⟨29993, by rfl⟩ (by norm_num))
theorem R225557 : Reach 225557 := rs (se 6 (by rfl) ⟨5286, by rfl⟩) (B 10573 (by norm_num) ⟨5286, by rfl⟩ (by norm_num))
theorem R127325 : Reach 127325 := rs (se 3 (by rfl) ⟨23873, by rfl⟩) (B 47747 (by norm_num) ⟨23873, by rfl⟩ (by norm_num))
theorem R94565 : Reach 94565 := rs (se 4 (by rfl) ⟨8865, by rfl⟩) (B 17731 (by norm_num) ⟨8865, by rfl⟩ (by norm_num))
theorem R160157 : Reach 160157 := rs (se 3 (by rfl) ⟨30029, by rfl⟩) (B 60059 (by norm_num) ⟨30029, by rfl⟩ (by norm_num))
theorem R94645 : Reach 94645 := rs (se 5 (by rfl) ⟨4436, by rfl⟩) (B 8873 (by norm_num) ⟨4436, by rfl⟩ (by norm_num))
theorem R94685 : Reach 94685 := rs (se 3 (by rfl) ⟨17753, by rfl⟩) (B 35507 (by norm_num) ⟨17753, by rfl⟩ (by norm_num))
theorem R94709 : Reach 94709 := rs (se 5 (by rfl) ⟨4439, by rfl⟩) (B 8879 (by norm_num) ⟨4439, by rfl⟩ (by norm_num))
theorem R94733 : Reach 94733 := rs (se 3 (by rfl) ⟨17762, by rfl⟩) (B 35525 (by norm_num) ⟨17762, by rfl⟩ (by norm_num))
theorem R94757 : Reach 94757 := rs (se 4 (by rfl) ⟨8883, by rfl⟩) (B 17767 (by norm_num) ⟨8883, by rfl⟩ (by norm_num))
theorem R94765 : Reach 94765 := rs (se 3 (by rfl) ⟨17768, by rfl⟩) (B 35537 (by norm_num) ⟨17768, by rfl⟩ (by norm_num))
theorem R160301 : Reach 160301 := rs (se 3 (by rfl) ⟨30056, by rfl⟩) (B 60113 (by norm_num) ⟨30056, by rfl⟩ (by norm_num))
theorem R160309 : Reach 160309 := rs (se 5 (by rfl) ⟨7514, by rfl⟩) (B 15029 (by norm_num) ⟨7514, by rfl⟩ (by norm_num))
theorem R94781 : Reach 94781 := rs (se 3 (by rfl) ⟨17771, by rfl⟩) (B 35543 (by norm_num) ⟨17771, by rfl⟩ (by norm_num))
theorem R94805 : Reach 94805 := rs (se 8 (by rfl) ⟨555, by rfl⟩) (B 1111 (by norm_num) ⟨555, by rfl⟩ (by norm_num))
theorem R94829 : Reach 94829 := rs (se 3 (by rfl) ⟨17780, by rfl⟩) (B 35561 (by norm_num) ⟨17780, by rfl⟩ (by norm_num))
theorem R94853 : Reach 94853 := rs (se 4 (by rfl) ⟨8892, by rfl⟩) (B 17785 (by norm_num) ⟨8892, by rfl⟩ (by norm_num))
theorem R94861 : Reach 94861 := rs (se 3 (by rfl) ⟨17786, by rfl⟩) (B 35573 (by norm_num) ⟨17786, by rfl⟩ (by norm_num))
theorem R94877 : Reach 94877 := rs (se 3 (by rfl) ⟨17789, by rfl⟩) (B 35579 (by norm_num) ⟨17789, by rfl⟩ (by norm_num))
theorem R94901 : Reach 94901 := rs (se 5 (by rfl) ⟨4448, by rfl⟩) (B 8897 (by norm_num) ⟨4448, by rfl⟩ (by norm_num))
theorem R225989 : Reach 225989 := rs (se 4 (by rfl) ⟨21186, by rfl⟩) (B 42373 (by norm_num) ⟨21186, by rfl⟩ (by norm_num))
theorem R94925 : Reach 94925 := rs (se 3 (by rfl) ⟨17798, by rfl⟩) (B 35597 (by norm_num) ⟨17798, by rfl⟩ (by norm_num))
theorem R94949 : Reach 94949 := rs (se 4 (by rfl) ⟨8901, by rfl⟩) (B 17803 (by norm_num) ⟨8901, by rfl⟩ (by norm_num))
theorem R160501 : Reach 160501 := rs (se 5 (by rfl) ⟨7523, by rfl⟩) (B 15047 (by norm_num) ⟨7523, by rfl⟩ (by norm_num))
theorem R94973 : Reach 94973 := rs (se 3 (by rfl) ⟨17807, by rfl⟩) (B 35615 (by norm_num) ⟨17807, by rfl⟩ (by norm_num))
theorem R94997 : Reach 94997 := rs (se 6 (by rfl) ⟨2226, by rfl⟩) (B 4453 (by norm_num) ⟨2226, by rfl⟩ (by norm_num))
theorem R95021 : Reach 95021 := rs (se 3 (by rfl) ⟨17816, by rfl⟩) (B 35633 (by norm_num) ⟨17816, by rfl⟩ (by norm_num))
theorem R95045 : Reach 95045 := rs (se 4 (by rfl) ⟨8910, by rfl⟩) (B 17821 (by norm_num) ⟨8910, by rfl⟩ (by norm_num))
theorem R95069 : Reach 95069 := rs (se 3 (by rfl) ⟨17825, by rfl⟩) (B 35651 (by norm_num) ⟨17825, by rfl⟩ (by norm_num))
theorem R127837 : Reach 127837 := rs (se 3 (by rfl) ⟨23969, by rfl⟩) (B 47939 (by norm_num) ⟨23969, by rfl⟩ (by norm_num))
theorem R160613 : Reach 160613 := rs (se 4 (by rfl) ⟨15057, by rfl⟩) (B 30115 (by norm_num) ⟨15057, by rfl⟩ (by norm_num))
theorem R95093 : Reach 95093 := rs (se 5 (by rfl) ⟨4457, by rfl⟩) (B 8915 (by norm_num) ⟨4457, by rfl⟩ (by norm_num))
theorem R324485 : Reach 324485 := rs (se 4 (by rfl) ⟨30420, by rfl⟩) (B 60841 (by norm_num) ⟨30420, by rfl⟩ (by norm_num))
theorem R95117 : Reach 95117 := rs (se 3 (by rfl) ⟨17834, by rfl⟩) (B 35669 (by norm_num) ⟨17834, by rfl⟩ (by norm_num))
theorem R95141 : Reach 95141 := rs (se 4 (by rfl) ⟨8919, by rfl⟩) (B 17839 (by norm_num) ⟨8919, by rfl⟩ (by norm_num))
theorem R95165 : Reach 95165 := rs (se 3 (by rfl) ⟨17843, by rfl⟩) (B 35687 (by norm_num) ⟨17843, by rfl⟩ (by norm_num))
theorem R95189 : Reach 95189 := rs (se 7 (by rfl) ⟨1115, by rfl⟩) (B 2231 (by norm_num) ⟨1115, by rfl⟩ (by norm_num))
theorem R95213 : Reach 95213 := rs (se 3 (by rfl) ⟨17852, by rfl⟩) (B 35705 (by norm_num) ⟨17852, by rfl⟩ (by norm_num))
theorem R95237 : Reach 95237 := rs (se 4 (by rfl) ⟨8928, by rfl⟩) (B 17857 (by norm_num) ⟨8928, by rfl⟩ (by norm_num))
theorem R95261 : Reach 95261 := rs (se 3 (by rfl) ⟨17861, by rfl⟩) (B 35723 (by norm_num) ⟨17861, by rfl⟩ (by norm_num))
theorem R160805 : Reach 160805 := rs (se 4 (by rfl) ⟨15075, by rfl⟩) (B 30151 (by norm_num) ⟨15075, by rfl⟩ (by norm_num))
theorem R95285 : Reach 95285 := rs (se 5 (by rfl) ⟨4466, by rfl⟩) (B 8933 (by norm_num) ⟨4466, by rfl⟩ (by norm_num))
theorem R95309 : Reach 95309 := rs (se 3 (by rfl) ⟨17870, by rfl⟩) (B 35741 (by norm_num) ⟨17870, by rfl⟩ (by norm_num))
theorem R95333 : Reach 95333 := rs (se 4 (by rfl) ⟨8937, by rfl⟩) (B 17875 (by norm_num) ⟨8937, by rfl⟩ (by norm_num))
theorem R226421 : Reach 226421 := rs (se 5 (by rfl) ⟨10613, by rfl⟩) (B 21227 (by norm_num) ⟨10613, by rfl⟩ (by norm_num))
theorem R95357 : Reach 95357 := rs (se 3 (by rfl) ⟨17879, by rfl⟩) (B 35759 (by norm_num) ⟨17879, by rfl⟩ (by norm_num))
theorem R95381 : Reach 95381 := rs (se 6 (by rfl) ⟨2235, by rfl⟩) (B 4471 (by norm_num) ⟨2235, by rfl⟩ (by norm_num))
theorem R95405 : Reach 95405 := rs (se 3 (by rfl) ⟨17888, by rfl⟩) (B 35777 (by norm_num) ⟨17888, by rfl⟩ (by norm_num))
theorem R95429 : Reach 95429 := rs (se 4 (by rfl) ⟨8946, by rfl⟩) (B 17893 (by norm_num) ⟨8946, by rfl⟩ (by norm_num))
theorem R95453 : Reach 95453 := rs (se 3 (by rfl) ⟨17897, by rfl⟩) (B 35795 (by norm_num) ⟨17897, by rfl⟩ (by norm_num))
theorem R95477 : Reach 95477 := rs (se 5 (by rfl) ⟨4475, by rfl⟩) (B 8951 (by norm_num) ⟨4475, by rfl⟩ (by norm_num))
theorem R95501 : Reach 95501 := rs (se 3 (by rfl) ⟨17906, by rfl⟩) (B 35813 (by norm_num) ⟨17906, by rfl⟩ (by norm_num))
theorem R750869 : Reach 750869 := rs (se 6 (by rfl) ⟨17598, by rfl⟩) (B 35197 (by norm_num) ⟨17598, by rfl⟩ (by norm_num))
theorem R95525 : Reach 95525 := rs (se 4 (by rfl) ⟨8955, by rfl⟩) (B 17911 (by norm_num) ⟨8955, by rfl⟩ (by norm_num))
theorem R95549 : Reach 95549 := rs (se 3 (by rfl) ⟨17915, by rfl⟩) (B 35831 (by norm_num) ⟨17915, by rfl⟩ (by norm_num))
theorem R95573 : Reach 95573 := rs (se 13 (by rfl) ⟨17, by rfl⟩) (B 35 (by norm_num) ⟨17, by rfl⟩ (by norm_num))
theorem R161117 : Reach 161117 := rs (se 3 (by rfl) ⟨30209, by rfl⟩) (B 60419 (by norm_num) ⟨30209, by rfl⟩ (by norm_num))
theorem R95597 : Reach 95597 := rs (se 3 (by rfl) ⟨17924, by rfl⟩) (B 35849 (by norm_num) ⟨17924, by rfl⟩ (by norm_num))
theorem R161149 : Reach 161149 := rs (se 3 (by rfl) ⟨30215, by rfl⟩) (B 60431 (by norm_num) ⟨30215, by rfl⟩ (by norm_num))
theorem R95621 : Reach 95621 := rs (se 4 (by rfl) ⟨8964, by rfl⟩) (B 17929 (by norm_num) ⟨8964, by rfl⟩ (by norm_num))
theorem R95645 : Reach 95645 := rs (se 3 (by rfl) ⟨17933, by rfl⟩) (B 35867 (by norm_num) ⟨17933, by rfl⟩ (by norm_num))
theorem R95669 : Reach 95669 := rs (se 5 (by rfl) ⟨4484, by rfl⟩) (B 8969 (by norm_num) ⟨4484, by rfl⟩ (by norm_num))
theorem R95693 : Reach 95693 := rs (se 3 (by rfl) ⟨17942, by rfl⟩) (B 35885 (by norm_num) ⟨17942, by rfl⟩ (by norm_num))
theorem R95717 : Reach 95717 := rs (se 4 (by rfl) ⟨8973, by rfl⟩) (B 17947 (by norm_num) ⟨8973, by rfl⟩ (by norm_num))
theorem R161261 : Reach 161261 := rs (se 3 (by rfl) ⟨30236, by rfl⟩) (B 60473 (by norm_num) ⟨30236, by rfl⟩ (by norm_num))
theorem R95741 : Reach 95741 := rs (se 3 (by rfl) ⟨17951, by rfl⟩) (B 35903 (by norm_num) ⟨17951, by rfl⟩ (by norm_num))
theorem R95765 : Reach 95765 := rs (se 6 (by rfl) ⟨2244, by rfl⟩) (B 4489 (by norm_num) ⟨2244, by rfl⟩ (by norm_num))
theorem R95789 : Reach 95789 := rs (se 3 (by rfl) ⟨17960, by rfl⟩) (B 35921 (by norm_num) ⟨17960, by rfl⟩ (by norm_num))
theorem R95813 : Reach 95813 := rs (se 4 (by rfl) ⟨8982, by rfl⟩) (B 17965 (by norm_num) ⟨8982, by rfl⟩ (by norm_num))
theorem R1799765 : Reach 1799765 := rs (se 8 (by rfl) ⟨10545, by rfl⟩) (B 21091 (by norm_num) ⟨10545, by rfl⟩ (by norm_num))
theorem R95837 : Reach 95837 := rs (se 3 (by rfl) ⟨17969, by rfl⟩) (B 35939 (by norm_num) ⟨17969, by rfl⟩ (by norm_num))
theorem R95845 : Reach 95845 := rs (se 4 (by rfl) ⟨8985, by rfl⟩) (B 17971 (by norm_num) ⟨8985, by rfl⟩ (by norm_num))
theorem R95861 : Reach 95861 := rs (se 5 (by rfl) ⟨4493, by rfl⟩) (B 8987 (by norm_num) ⟨4493, by rfl⟩ (by norm_num))
theorem R95885 : Reach 95885 := rs (se 3 (by rfl) ⟨17978, by rfl⟩) (B 35957 (by norm_num) ⟨17978, by rfl⟩ (by norm_num))
theorem R63125 : Reach 63125 := rs (se 6 (by rfl) ⟨1479, by rfl⟩) (B 2959 (by norm_num) ⟨1479, by rfl⟩ (by norm_num))
theorem R63129 : Reach 63129 := rs (se 2 (by rfl) ⟨23673, by rfl⟩) (B 47347 (by norm_num) ⟨23673, by rfl⟩ (by norm_num))
theorem R63133 : Reach 63133 := rs (se 3 (by rfl) ⟨11837, by rfl⟩) (B 23675 (by norm_num) ⟨11837, by rfl⟩ (by norm_num))
theorem R63137 : Reach 63137 := rs (se 2 (by rfl) ⟨23676, by rfl⟩) (B 47353 (by norm_num) ⟨23676, by rfl⟩ (by norm_num))
theorem R63141 : Reach 63141 := rs (se 4 (by rfl) ⟨5919, by rfl⟩) (B 11839 (by norm_num) ⟨5919, by rfl⟩ (by norm_num))
theorem R95909 : Reach 95909 := rs (se 4 (by rfl) ⟨8991, by rfl⟩) (B 17983 (by norm_num) ⟨8991, by rfl⟩ (by norm_num))
theorem R63145 : Reach 63145 := rs (se 2 (by rfl) ⟨23679, by rfl⟩) (B 47359 (by norm_num) ⟨23679, by rfl⟩ (by norm_num))
theorem R292517 : Reach 292517 := rs (se 4 (by rfl) ⟨27423, by rfl⟩) (B 54847 (by norm_num) ⟨27423, by rfl⟩ (by norm_num))
theorem R161453 : Reach 161453 := rs (se 3 (by rfl) ⟨30272, by rfl⟩) (B 60545 (by norm_num) ⟨30272, by rfl⟩ (by norm_num))
theorem R63149 : Reach 63149 := rs (se 3 (by rfl) ⟨11840, by rfl⟩) (B 23681 (by norm_num) ⟨11840, by rfl⟩ (by norm_num))
theorem R63153 : Reach 63153 := rs (se 2 (by rfl) ⟨23682, by rfl⟩) (B 47365 (by norm_num) ⟨23682, by rfl⟩ (by norm_num))
theorem R521909 : Reach 521909 := rs (se 5 (by rfl) ⟨24464, by rfl⟩) (B 48929 (by norm_num) ⟨24464, by rfl⟩ (by norm_num))
theorem R63157 : Reach 63157 := rs (se 5 (by rfl) ⟨2960, by rfl⟩) (B 5921 (by norm_num) ⟨2960, by rfl⟩ (by norm_num))
theorem R63161 : Reach 63161 := rs (se 2 (by rfl) ⟨23685, by rfl⟩) (B 47371 (by norm_num) ⟨23685, by rfl⟩ (by norm_num))
theorem R63165 : Reach 63165 := rs (se 3 (by rfl) ⟨11843, by rfl⟩) (B 23687 (by norm_num) ⟨11843, by rfl⟩ (by norm_num))
theorem R95933 : Reach 95933 := rs (se 3 (by rfl) ⟨17987, by rfl⟩) (B 35975 (by norm_num) ⟨17987, by rfl⟩ (by norm_num))
theorem R63169 : Reach 63169 := rs (se 2 (by rfl) ⟨23688, by rfl⟩) (B 47377 (by norm_num) ⟨23688, by rfl⟩ (by norm_num))
theorem R63173 : Reach 63173 := rs (se 4 (by rfl) ⟨5922, by rfl⟩) (B 11845 (by norm_num) ⟨5922, by rfl⟩ (by norm_num))
theorem R259781 : Reach 259781 := rs (se 4 (by rfl) ⟨24354, by rfl⟩) (B 48709 (by norm_num) ⟨24354, by rfl⟩ (by norm_num))
theorem R63177 : Reach 63177 := rs (se 2 (by rfl) ⟨23691, by rfl⟩) (B 47383 (by norm_num) ⟨23691, by rfl⟩ (by norm_num))
theorem R63181 : Reach 63181 := rs (se 3 (by rfl) ⟨11846, by rfl⟩) (B 23693 (by norm_num) ⟨11846, by rfl⟩ (by norm_num))
theorem R63185 : Reach 63185 := rs (se 2 (by rfl) ⟨23694, by rfl⟩) (B 47389 (by norm_num) ⟨23694, by rfl⟩ (by norm_num))
theorem R63189 : Reach 63189 := rs (se 7 (by rfl) ⟨740, by rfl⟩) (B 1481 (by norm_num) ⟨740, by rfl⟩ (by norm_num))
theorem R95957 : Reach 95957 := rs (se 7 (by rfl) ⟨1124, by rfl⟩) (B 2249 (by norm_num) ⟨1124, by rfl⟩ (by norm_num))
theorem R63193 : Reach 63193 := rs (se 2 (by rfl) ⟨23697, by rfl⟩) (B 47395 (by norm_num) ⟨23697, by rfl⟩ (by norm_num))
theorem R63197 : Reach 63197 := rs (se 3 (by rfl) ⟨11849, by rfl⟩) (B 23699 (by norm_num) ⟨11849, by rfl⟩ (by norm_num))
theorem R63201 : Reach 63201 := rs (se 2 (by rfl) ⟨23700, by rfl⟩) (B 47401 (by norm_num) ⟨23700, by rfl⟩ (by norm_num))
theorem R63205 : Reach 63205 := rs (se 4 (by rfl) ⟨5925, by rfl⟩) (B 11851 (by norm_num) ⟨5925, by rfl⟩ (by norm_num))
theorem R63209 : Reach 63209 := rs (se 2 (by rfl) ⟨23703, by rfl⟩) (B 47407 (by norm_num) ⟨23703, by rfl⟩ (by norm_num))
theorem R63213 : Reach 63213 := rs (se 3 (by rfl) ⟨11852, by rfl⟩) (B 23705 (by norm_num) ⟨11852, by rfl⟩ (by norm_num))
theorem R95981 : Reach 95981 := rs (se 3 (by rfl) ⟨17996, by rfl⟩) (B 35993 (by norm_num) ⟨17996, by rfl⟩ (by norm_num))
theorem R63217 : Reach 63217 := rs (se 2 (by rfl) ⟨23706, by rfl⟩) (B 47413 (by norm_num) ⟨23706, by rfl⟩ (by norm_num))
theorem R63221 : Reach 63221 := rs (se 5 (by rfl) ⟨2963, by rfl⟩) (B 5927 (by norm_num) ⟨2963, by rfl⟩ (by norm_num))
theorem R63225 : Reach 63225 := rs (se 2 (by rfl) ⟨23709, by rfl⟩) (B 47419 (by norm_num) ⟨23709, by rfl⟩ (by norm_num))
theorem R63229 : Reach 63229 := rs (se 3 (by rfl) ⟨11855, by rfl⟩) (B 23711 (by norm_num) ⟨11855, by rfl⟩ (by norm_num))
theorem R63233 : Reach 63233 := rs (se 2 (by rfl) ⟨23712, by rfl⟩) (B 47425 (by norm_num) ⟨23712, by rfl⟩ (by norm_num))
theorem R63237 : Reach 63237 := rs (se 4 (by rfl) ⟨5928, by rfl⟩) (B 11857 (by norm_num) ⟨5928, by rfl⟩ (by norm_num))
theorem R96005 : Reach 96005 := rs (se 4 (by rfl) ⟨9000, by rfl⟩) (B 18001 (by norm_num) ⟨9000, by rfl⟩ (by norm_num))
theorem R63241 : Reach 63241 := rs (se 2 (by rfl) ⟨23715, by rfl⟩) (B 47431 (by norm_num) ⟨23715, by rfl⟩ (by norm_num))
theorem R63245 : Reach 63245 := rs (se 3 (by rfl) ⟨11858, by rfl⟩) (B 23717 (by norm_num) ⟨11858, by rfl⟩ (by norm_num))
theorem R63249 : Reach 63249 := rs (se 2 (by rfl) ⟨23718, by rfl⟩) (B 47437 (by norm_num) ⟨23718, by rfl⟩ (by norm_num))
theorem R63253 : Reach 63253 := rs (se 6 (by rfl) ⟨1482, by rfl⟩) (B 2965 (by norm_num) ⟨1482, by rfl⟩ (by norm_num))
theorem R63257 : Reach 63257 := rs (se 2 (by rfl) ⟨23721, by rfl⟩) (B 47443 (by norm_num) ⟨23721, by rfl⟩ (by norm_num))
theorem R63261 : Reach 63261 := rs (se 3 (by rfl) ⟨11861, by rfl⟩) (B 23723 (by norm_num) ⟨11861, by rfl⟩ (by norm_num))
theorem R96029 : Reach 96029 := rs (se 3 (by rfl) ⟨18005, by rfl⟩) (B 36011 (by norm_num) ⟨18005, by rfl⟩ (by norm_num))
theorem R63265 : Reach 63265 := rs (se 2 (by rfl) ⟨23724, by rfl⟩) (B 47449 (by norm_num) ⟨23724, by rfl⟩ (by norm_num))
theorem R63269 : Reach 63269 := rs (se 4 (by rfl) ⟨5931, by rfl⟩) (B 11863 (by norm_num) ⟨5931, by rfl⟩ (by norm_num))
theorem R63273 : Reach 63273 := rs (se 2 (by rfl) ⟨23727, by rfl⟩) (B 47455 (by norm_num) ⟨23727, by rfl⟩ (by norm_num))
theorem R63277 : Reach 63277 := rs (se 3 (by rfl) ⟨11864, by rfl⟩) (B 23729 (by norm_num) ⟨11864, by rfl⟩ (by norm_num))
theorem R63281 : Reach 63281 := rs (se 2 (by rfl) ⟨23730, by rfl⟩) (B 47461 (by norm_num) ⟨23730, by rfl⟩ (by norm_num))
theorem R63285 : Reach 63285 := rs (se 5 (by rfl) ⟨2966, by rfl⟩) (B 5933 (by norm_num) ⟨2966, by rfl⟩ (by norm_num))
theorem R96053 : Reach 96053 := rs (se 5 (by rfl) ⟨4502, by rfl⟩) (B 9005 (by norm_num) ⟨4502, by rfl⟩ (by norm_num))
theorem R63289 : Reach 63289 := rs (se 2 (by rfl) ⟨23733, by rfl⟩) (B 47467 (by norm_num) ⟨23733, by rfl⟩ (by norm_num))
theorem R63293 : Reach 63293 := rs (se 3 (by rfl) ⟨11867, by rfl⟩) (B 23735 (by norm_num) ⟨11867, by rfl⟩ (by norm_num))
theorem R63297 : Reach 63297 := rs (se 2 (by rfl) ⟨23736, by rfl⟩) (B 47473 (by norm_num) ⟨23736, by rfl⟩ (by norm_num))
theorem R63301 : Reach 63301 := rs (se 4 (by rfl) ⟨5934, by rfl⟩) (B 11869 (by norm_num) ⟨5934, by rfl⟩ (by norm_num))
theorem R63305 : Reach 63305 := rs (se 2 (by rfl) ⟨23739, by rfl⟩) (B 47479 (by norm_num) ⟨23739, by rfl⟩ (by norm_num))
theorem R63309 : Reach 63309 := rs (se 3 (by rfl) ⟨11870, by rfl⟩) (B 23741 (by norm_num) ⟨11870, by rfl⟩ (by norm_num))
theorem R96077 : Reach 96077 := rs (se 3 (by rfl) ⟨18014, by rfl⟩) (B 36029 (by norm_num) ⟨18014, by rfl⟩ (by norm_num))
theorem R63313 : Reach 63313 := rs (se 2 (by rfl) ⟨23742, by rfl⟩) (B 47485 (by norm_num) ⟨23742, by rfl⟩ (by norm_num))
theorem R63317 : Reach 63317 := rs (se 9 (by rfl) ⟨185, by rfl⟩) (B 371 (by norm_num) ⟨185, by rfl⟩ (by norm_num))
theorem R63321 : Reach 63321 := rs (se 2 (by rfl) ⟨23745, by rfl⟩) (B 47491 (by norm_num) ⟨23745, by rfl⟩ (by norm_num))
theorem R63325 : Reach 63325 := rs (se 3 (by rfl) ⟨11873, by rfl⟩) (B 23747 (by norm_num) ⟨11873, by rfl⟩ (by norm_num))
theorem R63329 : Reach 63329 := rs (se 2 (by rfl) ⟨23748, by rfl⟩) (B 47497 (by norm_num) ⟨23748, by rfl⟩ (by norm_num))
theorem R63333 : Reach 63333 := rs (se 4 (by rfl) ⟨5937, by rfl⟩) (B 11875 (by norm_num) ⟨5937, by rfl⟩ (by norm_num))
theorem R96101 : Reach 96101 := rs (se 4 (by rfl) ⟨9009, by rfl⟩) (B 18019 (by norm_num) ⟨9009, by rfl⟩ (by norm_num))
theorem R63337 : Reach 63337 := rs (se 2 (by rfl) ⟨23751, by rfl⟩) (B 47503 (by norm_num) ⟨23751, by rfl⟩ (by norm_num))
theorem R63341 : Reach 63341 := rs (se 3 (by rfl) ⟨11876, by rfl⟩) (B 23753 (by norm_num) ⟨11876, by rfl⟩ (by norm_num))
theorem R63345 : Reach 63345 := rs (se 2 (by rfl) ⟨23754, by rfl⟩) (B 47509 (by norm_num) ⟨23754, by rfl⟩ (by norm_num))
theorem R63349 : Reach 63349 := rs (se 5 (by rfl) ⟨2969, by rfl⟩) (B 5939 (by norm_num) ⟨2969, by rfl⟩ (by norm_num))
theorem R522101 : Reach 522101 := rs (se 5 (by rfl) ⟨24473, by rfl⟩) (B 48947 (by norm_num) ⟨24473, by rfl⟩ (by norm_num))
theorem R63353 : Reach 63353 := rs (se 2 (by rfl) ⟨23757, by rfl⟩) (B 47515 (by norm_num) ⟨23757, by rfl⟩ (by norm_num))
theorem R63357 : Reach 63357 := rs (se 3 (by rfl) ⟨11879, by rfl⟩) (B 23759 (by norm_num) ⟨11879, by rfl⟩ (by norm_num))
theorem R96125 : Reach 96125 := rs (se 3 (by rfl) ⟨18023, by rfl⟩) (B 36047 (by norm_num) ⟨18023, by rfl⟩ (by norm_num))
theorem R63361 : Reach 63361 := rs (se 2 (by rfl) ⟨23760, by rfl⟩) (B 47521 (by norm_num) ⟨23760, by rfl⟩ (by norm_num))
theorem R63365 : Reach 63365 := rs (se 4 (by rfl) ⟨5940, by rfl⟩) (B 11881 (by norm_num) ⟨5940, by rfl⟩ (by norm_num))
theorem R63369 : Reach 63369 := rs (se 2 (by rfl) ⟨23763, by rfl⟩) (B 47527 (by norm_num) ⟨23763, by rfl⟩ (by norm_num))
theorem R63373 : Reach 63373 := rs (se 3 (by rfl) ⟨11882, by rfl⟩) (B 23765 (by norm_num) ⟨11882, by rfl⟩ (by norm_num))
theorem R63377 : Reach 63377 := rs (se 2 (by rfl) ⟨23766, by rfl⟩) (B 47533 (by norm_num) ⟨23766, by rfl⟩ (by norm_num))
theorem R63381 : Reach 63381 := rs (se 6 (by rfl) ⟨1485, by rfl⟩) (B 2971 (by norm_num) ⟨1485, by rfl⟩ (by norm_num))
theorem R96149 : Reach 96149 := rs (se 6 (by rfl) ⟨2253, by rfl⟩) (B 4507 (by norm_num) ⟨2253, by rfl⟩ (by norm_num))
theorem R63385 : Reach 63385 := rs (se 2 (by rfl) ⟨23769, by rfl⟩) (B 47539 (by norm_num) ⟨23769, by rfl⟩ (by norm_num))
theorem R63389 : Reach 63389 := rs (se 3 (by rfl) ⟨11885, by rfl⟩) (B 23771 (by norm_num) ⟨11885, by rfl⟩ (by norm_num))
theorem R63393 : Reach 63393 := rs (se 2 (by rfl) ⟨23772, by rfl⟩) (B 47545 (by norm_num) ⟨23772, by rfl⟩ (by norm_num))
theorem R63397 : Reach 63397 := rs (se 4 (by rfl) ⟨5943, by rfl⟩) (B 11887 (by norm_num) ⟨5943, by rfl⟩ (by norm_num))
theorem R63401 : Reach 63401 := rs (se 2 (by rfl) ⟨23775, by rfl⟩) (B 47551 (by norm_num) ⟨23775, by rfl⟩ (by norm_num))
theorem R63405 : Reach 63405 := rs (se 3 (by rfl) ⟨11888, by rfl⟩) (B 23777 (by norm_num) ⟨11888, by rfl⟩ (by norm_num))
theorem R96173 : Reach 96173 := rs (se 3 (by rfl) ⟨18032, by rfl⟩) (B 36065 (by norm_num) ⟨18032, by rfl⟩ (by norm_num))
theorem R63409 : Reach 63409 := rs (se 2 (by rfl) ⟨23778, by rfl⟩) (B 47557 (by norm_num) ⟨23778, by rfl⟩ (by norm_num))
theorem R63413 : Reach 63413 := rs (se 5 (by rfl) ⟨2972, by rfl⟩) (B 5945 (by norm_num) ⟨2972, by rfl⟩ (by norm_num))
theorem R63417 : Reach 63417 := rs (se 2 (by rfl) ⟨23781, by rfl⟩) (B 47563 (by norm_num) ⟨23781, by rfl⟩ (by norm_num))
theorem R63421 : Reach 63421 := rs (se 3 (by rfl) ⟨11891, by rfl⟩) (B 23783 (by norm_num) ⟨11891, by rfl⟩ (by norm_num))
theorem R63425 : Reach 63425 := rs (se 2 (by rfl) ⟨23784, by rfl⟩) (B 47569 (by norm_num) ⟨23784, by rfl⟩ (by norm_num))
theorem R63429 : Reach 63429 := rs (se 4 (by rfl) ⟨5946, by rfl⟩) (B 11893 (by norm_num) ⟨5946, by rfl⟩ (by norm_num))
theorem R96197 : Reach 96197 := rs (se 4 (by rfl) ⟨9018, by rfl⟩) (B 18037 (by norm_num) ⟨9018, by rfl⟩ (by norm_num))
theorem R63433 : Reach 63433 := rs (se 2 (by rfl) ⟨23787, by rfl⟩) (B 47575 (by norm_num) ⟨23787, by rfl⟩ (by norm_num))
theorem R63437 : Reach 63437 := rs (se 3 (by rfl) ⟨11894, by rfl⟩) (B 23789 (by norm_num) ⟨11894, by rfl⟩ (by norm_num))
theorem R63441 : Reach 63441 := rs (se 2 (by rfl) ⟨23790, by rfl⟩) (B 47581 (by norm_num) ⟨23790, by rfl⟩ (by norm_num))
theorem R63445 : Reach 63445 := rs (se 7 (by rfl) ⟨743, by rfl⟩) (B 1487 (by norm_num) ⟨743, by rfl⟩ (by norm_num))
theorem R63449 : Reach 63449 := rs (se 2 (by rfl) ⟨23793, by rfl⟩) (B 47587 (by norm_num) ⟨23793, by rfl⟩ (by norm_num))
theorem R63453 : Reach 63453 := rs (se 3 (by rfl) ⟨11897, by rfl⟩) (B 23795 (by norm_num) ⟨11897, by rfl⟩ (by norm_num))
theorem R96221 : Reach 96221 := rs (se 3 (by rfl) ⟨18041, by rfl⟩) (B 36083 (by norm_num) ⟨18041, by rfl⟩ (by norm_num))
theorem R63457 : Reach 63457 := rs (se 2 (by rfl) ⟨23796, by rfl⟩) (B 47593 (by norm_num) ⟨23796, by rfl⟩ (by norm_num))
theorem R63461 : Reach 63461 := rs (se 4 (by rfl) ⟨5949, by rfl⟩) (B 11899 (by norm_num) ⟨5949, by rfl⟩ (by norm_num))
theorem R63465 : Reach 63465 := rs (se 2 (by rfl) ⟨23799, by rfl⟩) (B 47599 (by norm_num) ⟨23799, by rfl⟩ (by norm_num))
theorem R63469 : Reach 63469 := rs (se 3 (by rfl) ⟨11900, by rfl⟩) (B 23801 (by norm_num) ⟨11900, by rfl⟩ (by norm_num))
theorem R63473 : Reach 63473 := rs (se 2 (by rfl) ⟨23802, by rfl⟩) (B 47605 (by norm_num) ⟨23802, by rfl⟩ (by norm_num))
theorem R63477 : Reach 63477 := rs (se 5 (by rfl) ⟨2975, by rfl⟩) (B 5951 (by norm_num) ⟨2975, by rfl⟩ (by norm_num))
theorem R96245 : Reach 96245 := rs (se 5 (by rfl) ⟨4511, by rfl⟩) (B 9023 (by norm_num) ⟨4511, by rfl⟩ (by norm_num))
theorem R63481 : Reach 63481 := rs (se 2 (by rfl) ⟨23805, by rfl⟩) (B 47611 (by norm_num) ⟨23805, by rfl⟩ (by norm_num))
theorem R63485 : Reach 63485 := rs (se 3 (by rfl) ⟨11903, by rfl⟩) (B 23807 (by norm_num) ⟨11903, by rfl⟩ (by norm_num))
theorem R63489 : Reach 63489 := rs (se 2 (by rfl) ⟨23808, by rfl⟩) (B 47617 (by norm_num) ⟨23808, by rfl⟩ (by norm_num))
theorem R63493 : Reach 63493 := rs (se 4 (by rfl) ⟨5952, by rfl⟩) (B 11905 (by norm_num) ⟨5952, by rfl⟩ (by norm_num))
theorem R161797 : Reach 161797 := rs (se 4 (by rfl) ⟨15168, by rfl⟩) (B 30337 (by norm_num) ⟨15168, by rfl⟩ (by norm_num))
theorem R63497 : Reach 63497 := rs (se 2 (by rfl) ⟨23811, by rfl⟩) (B 47623 (by norm_num) ⟨23811, by rfl⟩ (by norm_num))
theorem R63501 : Reach 63501 := rs (se 3 (by rfl) ⟨11906, by rfl⟩) (B 23813 (by norm_num) ⟨11906, by rfl⟩ (by norm_num))
theorem R96269 : Reach 96269 := rs (se 3 (by rfl) ⟨18050, by rfl⟩) (B 36101 (by norm_num) ⟨18050, by rfl⟩ (by norm_num))
theorem R63505 : Reach 63505 := rs (se 2 (by rfl) ⟨23814, by rfl⟩) (B 47629 (by norm_num) ⟨23814, by rfl⟩ (by norm_num))
theorem R63509 : Reach 63509 := rs (se 6 (by rfl) ⟨1488, by rfl⟩) (B 2977 (by norm_num) ⟨1488, by rfl⟩ (by norm_num))
theorem R391189 : Reach 391189 := rs (se 6 (by rfl) ⟨9168, by rfl⟩) (B 18337 (by norm_num) ⟨9168, by rfl⟩ (by norm_num))
theorem R63513 : Reach 63513 := rs (se 2 (by rfl) ⟨23817, by rfl⟩) (B 47635 (by norm_num) ⟨23817, by rfl⟩ (by norm_num))
theorem R63517 : Reach 63517 := rs (se 3 (by rfl) ⟨11909, by rfl⟩) (B 23819 (by norm_num) ⟨11909, by rfl⟩ (by norm_num))
theorem R63521 : Reach 63521 := rs (se 2 (by rfl) ⟨23820, by rfl⟩) (B 47641 (by norm_num) ⟨23820, by rfl⟩ (by norm_num))
theorem R63525 : Reach 63525 := rs (se 4 (by rfl) ⟨5955, by rfl⟩) (B 11911 (by norm_num) ⟨5955, by rfl⟩ (by norm_num))
theorem R96293 : Reach 96293 := rs (se 4 (by rfl) ⟨9027, by rfl⟩) (B 18055 (by norm_num) ⟨9027, by rfl⟩ (by norm_num))
theorem R63529 : Reach 63529 := rs (se 2 (by rfl) ⟨23823, by rfl⟩) (B 47647 (by norm_num) ⟨23823, by rfl⟩ (by norm_num))
theorem R63533 : Reach 63533 := rs (se 3 (by rfl) ⟨11912, by rfl⟩) (B 23825 (by norm_num) ⟨11912, by rfl⟩ (by norm_num))
theorem R63537 : Reach 63537 := rs (se 2 (by rfl) ⟨23826, by rfl⟩) (B 47653 (by norm_num) ⟨23826, by rfl⟩ (by norm_num))
theorem R63541 : Reach 63541 := rs (se 5 (by rfl) ⟨2978, by rfl⟩) (B 5957 (by norm_num) ⟨2978, by rfl⟩ (by norm_num))
theorem R63545 : Reach 63545 := rs (se 2 (by rfl) ⟨23829, by rfl⟩) (B 47659 (by norm_num) ⟨23829, by rfl⟩ (by norm_num))
theorem R63549 : Reach 63549 := rs (se 3 (by rfl) ⟨11915, by rfl⟩) (B 23831 (by norm_num) ⟨11915, by rfl⟩ (by norm_num))
theorem R96317 : Reach 96317 := rs (se 3 (by rfl) ⟨18059, by rfl⟩) (B 36119 (by norm_num) ⟨18059, by rfl⟩ (by norm_num))
theorem R63553 : Reach 63553 := rs (se 2 (by rfl) ⟨23832, by rfl⟩) (B 47665 (by norm_num) ⟨23832, by rfl⟩ (by norm_num))
theorem R63557 : Reach 63557 := rs (se 4 (by rfl) ⟨5958, by rfl⟩) (B 11917 (by norm_num) ⟨5958, by rfl⟩ (by norm_num))
theorem R63561 : Reach 63561 := rs (se 2 (by rfl) ⟨23835, by rfl⟩) (B 47671 (by norm_num) ⟨23835, by rfl⟩ (by norm_num))
theorem R63565 : Reach 63565 := rs (se 3 (by rfl) ⟨11918, by rfl⟩) (B 23837 (by norm_num) ⟨11918, by rfl⟩ (by norm_num))
theorem R63569 : Reach 63569 := rs (se 2 (by rfl) ⟨23838, by rfl⟩) (B 47677 (by norm_num) ⟨23838, by rfl⟩ (by norm_num))
theorem R63573 : Reach 63573 := rs (se 8 (by rfl) ⟨372, by rfl⟩) (B 745 (by norm_num) ⟨372, by rfl⟩ (by norm_num))
theorem R96341 : Reach 96341 := rs (se 8 (by rfl) ⟨564, by rfl⟩) (B 1129 (by norm_num) ⟨564, by rfl⟩ (by norm_num))
theorem R63577 : Reach 63577 := rs (se 2 (by rfl) ⟨23841, by rfl⟩) (B 47683 (by norm_num) ⟨23841, by rfl⟩ (by norm_num))
theorem R63581 : Reach 63581 := rs (se 3 (by rfl) ⟨11921, by rfl⟩) (B 23843 (by norm_num) ⟨11921, by rfl⟩ (by norm_num))
theorem R63585 : Reach 63585 := rs (se 2 (by rfl) ⟨23844, by rfl⟩) (B 47689 (by norm_num) ⟨23844, by rfl⟩ (by norm_num))
theorem R63589 : Reach 63589 := rs (se 4 (by rfl) ⟨5961, by rfl⟩) (B 11923 (by norm_num) ⟨5961, by rfl⟩ (by norm_num))
theorem R63593 : Reach 63593 := rs (se 2 (by rfl) ⟨23847, by rfl⟩) (B 47695 (by norm_num) ⟨23847, by rfl⟩ (by norm_num))
theorem R63597 : Reach 63597 := rs (se 3 (by rfl) ⟨11924, by rfl⟩) (B 23849 (by norm_num) ⟨11924, by rfl⟩ (by norm_num))
theorem R96365 : Reach 96365 := rs (se 3 (by rfl) ⟨18068, by rfl⟩) (B 36137 (by norm_num) ⟨18068, by rfl⟩ (by norm_num))
theorem R63601 : Reach 63601 := rs (se 2 (by rfl) ⟨23850, by rfl⟩) (B 47701 (by norm_num) ⟨23850, by rfl⟩ (by norm_num))
theorem R63605 : Reach 63605 := rs (se 5 (by rfl) ⟨2981, by rfl⟩) (B 5963 (by norm_num) ⟨2981, by rfl⟩ (by norm_num))
theorem R161909 : Reach 161909 := rs (se 5 (by rfl) ⟨7589, by rfl⟩) (B 15179 (by norm_num) ⟨7589, by rfl⟩ (by norm_num))
theorem R63609 : Reach 63609 := rs (se 2 (by rfl) ⟨23853, by rfl⟩) (B 47707 (by norm_num) ⟨23853, by rfl⟩ (by norm_num))
theorem R63613 : Reach 63613 := rs (se 3 (by rfl) ⟨11927, by rfl⟩) (B 23855 (by norm_num) ⟨11927, by rfl⟩ (by norm_num))
theorem R63617 : Reach 63617 := rs (se 2 (by rfl) ⟨23856, by rfl⟩) (B 47713 (by norm_num) ⟨23856, by rfl⟩ (by norm_num))
theorem R63621 : Reach 63621 := rs (se 4 (by rfl) ⟨5964, by rfl⟩) (B 11929 (by norm_num) ⟨5964, by rfl⟩ (by norm_num))
theorem R96389 : Reach 96389 := rs (se 4 (by rfl) ⟨9036, by rfl⟩) (B 18073 (by norm_num) ⟨9036, by rfl⟩ (by norm_num))
theorem R63625 : Reach 63625 := rs (se 2 (by rfl) ⟨23859, by rfl⟩) (B 47719 (by norm_num) ⟨23859, by rfl⟩ (by norm_num))
theorem R63629 : Reach 63629 := rs (se 3 (by rfl) ⟨11930, by rfl⟩) (B 23861 (by norm_num) ⟨11930, by rfl⟩ (by norm_num))
theorem R63633 : Reach 63633 := rs (se 2 (by rfl) ⟨23862, by rfl⟩) (B 47725 (by norm_num) ⟨23862, by rfl⟩ (by norm_num))
theorem R63637 : Reach 63637 := rs (se 6 (by rfl) ⟨1491, by rfl⟩) (B 2983 (by norm_num) ⟨1491, by rfl⟩ (by norm_num))
theorem R325781 : Reach 325781 := rs (se 6 (by rfl) ⟨7635, by rfl⟩) (B 15271 (by norm_num) ⟨7635, by rfl⟩ (by norm_num))
theorem R63641 : Reach 63641 := rs (se 2 (by rfl) ⟨23865, by rfl⟩) (B 47731 (by norm_num) ⟨23865, by rfl⟩ (by norm_num))
theorem R63645 : Reach 63645 := rs (se 3 (by rfl) ⟨11933, by rfl⟩) (B 23867 (by norm_num) ⟨11933, by rfl⟩ (by norm_num))
theorem R96413 : Reach 96413 := rs (se 3 (by rfl) ⟨18077, by rfl⟩) (B 36155 (by norm_num) ⟨18077, by rfl⟩ (by norm_num))
theorem R63649 : Reach 63649 := rs (se 2 (by rfl) ⟨23868, by rfl⟩) (B 47737 (by norm_num) ⟨23868, by rfl⟩ (by norm_num))
theorem R63653 : Reach 63653 := rs (se 4 (by rfl) ⟨5967, by rfl⟩) (B 11935 (by norm_num) ⟨5967, by rfl⟩ (by norm_num))
theorem R63657 : Reach 63657 := rs (se 2 (by rfl) ⟨23871, by rfl⟩) (B 47743 (by norm_num) ⟨23871, by rfl⟩ (by norm_num))
theorem R63661 : Reach 63661 := rs (se 3 (by rfl) ⟨11936, by rfl⟩) (B 23873 (by norm_num) ⟨11936, by rfl⟩ (by norm_num))
theorem R63665 : Reach 63665 := rs (se 2 (by rfl) ⟨23874, by rfl⟩) (B 47749 (by norm_num) ⟨23874, by rfl⟩ (by norm_num))
theorem R63669 : Reach 63669 := rs (se 5 (by rfl) ⟨2984, by rfl⟩) (B 5969 (by norm_num) ⟨2984, by rfl⟩ (by norm_num))
theorem R96437 : Reach 96437 := rs (se 5 (by rfl) ⟨4520, by rfl⟩) (B 9041 (by norm_num) ⟨4520, by rfl⟩ (by norm_num))
theorem R63673 : Reach 63673 := rs (se 2 (by rfl) ⟨23877, by rfl⟩) (B 47755 (by norm_num) ⟨23877, by rfl⟩ (by norm_num))
theorem R63677 : Reach 63677 := rs (se 3 (by rfl) ⟨11939, by rfl⟩) (B 23879 (by norm_num) ⟨11939, by rfl⟩ (by norm_num))
theorem R63681 : Reach 63681 := rs (se 2 (by rfl) ⟨23880, by rfl⟩) (B 47761 (by norm_num) ⟨23880, by rfl⟩ (by norm_num))
theorem R63685 : Reach 63685 := rs (se 4 (by rfl) ⟨5970, by rfl⟩) (B 11941 (by norm_num) ⟨5970, by rfl⟩ (by norm_num))
theorem R63689 : Reach 63689 := rs (se 2 (by rfl) ⟨23883, by rfl⟩) (B 47767 (by norm_num) ⟨23883, by rfl⟩ (by norm_num))
theorem R63693 : Reach 63693 := rs (se 3 (by rfl) ⟨11942, by rfl⟩) (B 23885 (by norm_num) ⟨11942, by rfl⟩ (by norm_num))
theorem R96461 : Reach 96461 := rs (se 3 (by rfl) ⟨18086, by rfl⟩) (B 36173 (by norm_num) ⟨18086, by rfl⟩ (by norm_num))
theorem R63697 : Reach 63697 := rs (se 2 (by rfl) ⟨23886, by rfl⟩) (B 47773 (by norm_num) ⟨23886, by rfl⟩ (by norm_num))
theorem R63701 : Reach 63701 := rs (se 7 (by rfl) ⟨746, by rfl⟩) (B 1493 (by norm_num) ⟨746, by rfl⟩ (by norm_num))
theorem R63705 : Reach 63705 := rs (se 2 (by rfl) ⟨23889, by rfl⟩) (B 47779 (by norm_num) ⟨23889, by rfl⟩ (by norm_num))
theorem R63709 : Reach 63709 := rs (se 3 (by rfl) ⟨11945, by rfl⟩) (B 23891 (by norm_num) ⟨11945, by rfl⟩ (by norm_num))
theorem R63713 : Reach 63713 := rs (se 2 (by rfl) ⟨23892, by rfl⟩) (B 47785 (by norm_num) ⟨23892, by rfl⟩ (by norm_num))
theorem R63717 : Reach 63717 := rs (se 4 (by rfl) ⟨5973, by rfl⟩) (B 11947 (by norm_num) ⟨5973, by rfl⟩ (by norm_num))
theorem R96485 : Reach 96485 := rs (se 4 (by rfl) ⟨9045, by rfl⟩) (B 18091 (by norm_num) ⟨9045, by rfl⟩ (by norm_num))
theorem R63721 : Reach 63721 := rs (se 2 (by rfl) ⟨23895, by rfl⟩) (B 47791 (by norm_num) ⟨23895, by rfl⟩ (by norm_num))
theorem R63725 : Reach 63725 := rs (se 3 (by rfl) ⟨11948, by rfl⟩) (B 23897 (by norm_num) ⟨11948, by rfl⟩ (by norm_num))
theorem R63729 : Reach 63729 := rs (se 2 (by rfl) ⟨23898, by rfl⟩) (B 47797 (by norm_num) ⟨23898, by rfl⟩ (by norm_num))
theorem R63733 : Reach 63733 := rs (se 5 (by rfl) ⟨2987, by rfl⟩) (B 5975 (by norm_num) ⟨2987, by rfl⟩ (by norm_num))
theorem R63737 : Reach 63737 := rs (se 2 (by rfl) ⟨23901, by rfl⟩) (B 47803 (by norm_num) ⟨23901, by rfl⟩ (by norm_num))
theorem R63741 : Reach 63741 := rs (se 3 (by rfl) ⟨11951, by rfl⟩) (B 23903 (by norm_num) ⟨11951, by rfl⟩ (by norm_num))
theorem R96509 : Reach 96509 := rs (se 3 (by rfl) ⟨18095, by rfl⟩) (B 36191 (by norm_num) ⟨18095, by rfl⟩ (by norm_num))
theorem R63745 : Reach 63745 := rs (se 2 (by rfl) ⟨23904, by rfl⟩) (B 47809 (by norm_num) ⟨23904, by rfl⟩ (by norm_num))
theorem R63749 : Reach 63749 := rs (se 4 (by rfl) ⟨5976, by rfl⟩) (B 11953 (by norm_num) ⟨5976, by rfl⟩ (by norm_num))
theorem R63753 : Reach 63753 := rs (se 2 (by rfl) ⟨23907, by rfl⟩) (B 47815 (by norm_num) ⟨23907, by rfl⟩ (by norm_num))
theorem R63757 : Reach 63757 := rs (se 3 (by rfl) ⟨11954, by rfl⟩) (B 23909 (by norm_num) ⟨11954, by rfl⟩ (by norm_num))
theorem R63761 : Reach 63761 := rs (se 2 (by rfl) ⟨23910, by rfl⟩) (B 47821 (by norm_num) ⟨23910, by rfl⟩ (by norm_num))
theorem R63765 : Reach 63765 := rs (se 6 (by rfl) ⟨1494, by rfl⟩) (B 2989 (by norm_num) ⟨1494, by rfl⟩ (by norm_num))
theorem R96533 : Reach 96533 := rs (se 6 (by rfl) ⟨2262, by rfl⟩) (B 4525 (by norm_num) ⟨2262, by rfl⟩ (by norm_num))
theorem R63769 : Reach 63769 := rs (se 2 (by rfl) ⟨23913, by rfl⟩) (B 47827 (by norm_num) ⟨23913, by rfl⟩ (by norm_num))
theorem R63773 : Reach 63773 := rs (se 3 (by rfl) ⟨11957, by rfl⟩) (B 23915 (by norm_num) ⟨11957, by rfl⟩ (by norm_num))
theorem R63777 : Reach 63777 := rs (se 2 (by rfl) ⟨23916, by rfl⟩) (B 47833 (by norm_num) ⟨23916, by rfl⟩ (by norm_num))
theorem R63781 : Reach 63781 := rs (se 4 (by rfl) ⟨5979, by rfl⟩) (B 11959 (by norm_num) ⟨5979, by rfl⟩ (by norm_num))
theorem R63785 : Reach 63785 := rs (se 2 (by rfl) ⟨23919, by rfl⟩) (B 47839 (by norm_num) ⟨23919, by rfl⟩ (by norm_num))
theorem R63789 : Reach 63789 := rs (se 3 (by rfl) ⟨11960, by rfl⟩) (B 23921 (by norm_num) ⟨11960, by rfl⟩ (by norm_num))
theorem R96557 : Reach 96557 := rs (se 3 (by rfl) ⟨18104, by rfl⟩) (B 36209 (by norm_num) ⟨18104, by rfl⟩ (by norm_num))
theorem R63793 : Reach 63793 := rs (se 2 (by rfl) ⟨23922, by rfl⟩) (B 47845 (by norm_num) ⟨23922, by rfl⟩ (by norm_num))
theorem R63797 : Reach 63797 := rs (se 5 (by rfl) ⟨2990, by rfl⟩) (B 5981 (by norm_num) ⟨2990, by rfl⟩ (by norm_num))
theorem R162101 : Reach 162101 := rs (se 5 (by rfl) ⟨7598, by rfl⟩) (B 15197 (by norm_num) ⟨7598, by rfl⟩ (by norm_num))
theorem R63801 : Reach 63801 := rs (se 2 (by rfl) ⟨23925, by rfl⟩) (B 47851 (by norm_num) ⟨23925, by rfl⟩ (by norm_num))
theorem R63805 : Reach 63805 := rs (se 3 (by rfl) ⟨11963, by rfl⟩) (B 23927 (by norm_num) ⟨11963, by rfl⟩ (by norm_num))
theorem R63809 : Reach 63809 := rs (se 2 (by rfl) ⟨23928, by rfl⟩) (B 47857 (by norm_num) ⟨23928, by rfl⟩ (by norm_num))
theorem R63813 : Reach 63813 := rs (se 4 (by rfl) ⟨5982, by rfl⟩) (B 11965 (by norm_num) ⟨5982, by rfl⟩ (by norm_num))
theorem R96581 : Reach 96581 := rs (se 4 (by rfl) ⟨9054, by rfl⟩) (B 18109 (by norm_num) ⟨9054, by rfl⟩ (by norm_num))
theorem R63817 : Reach 63817 := rs (se 2 (by rfl) ⟨23931, by rfl⟩) (B 47863 (by norm_num) ⟨23931, by rfl⟩ (by norm_num))
theorem R63821 : Reach 63821 := rs (se 3 (by rfl) ⟨11966, by rfl⟩) (B 23933 (by norm_num) ⟨11966, by rfl⟩ (by norm_num))
theorem R63825 : Reach 63825 := rs (se 2 (by rfl) ⟨23934, by rfl⟩) (B 47869 (by norm_num) ⟨23934, by rfl⟩ (by norm_num))
theorem R63829 : Reach 63829 := rs (se 10 (by rfl) ⟨93, by rfl⟩) (B 187 (by norm_num) ⟨93, by rfl⟩ (by norm_num))
theorem R63833 : Reach 63833 := rs (se 2 (by rfl) ⟨23937, by rfl⟩) (B 47875 (by norm_num) ⟨23937, by rfl⟩ (by norm_num))
theorem R63837 : Reach 63837 := rs (se 3 (by rfl) ⟨11969, by rfl⟩) (B 23939 (by norm_num) ⟨11969, by rfl⟩ (by norm_num))
theorem R96605 : Reach 96605 := rs (se 3 (by rfl) ⟨18113, by rfl⟩) (B 36227 (by norm_num) ⟨18113, by rfl⟩ (by norm_num))
theorem R63841 : Reach 63841 := rs (se 2 (by rfl) ⟨23940, by rfl⟩) (B 47881 (by norm_num) ⟨23940, by rfl⟩ (by norm_num))
theorem R63845 : Reach 63845 := rs (se 4 (by rfl) ⟨5985, by rfl⟩) (B 11971 (by norm_num) ⟨5985, by rfl⟩ (by norm_num))
theorem R63849 : Reach 63849 := rs (se 2 (by rfl) ⟨23943, by rfl⟩) (B 47887 (by norm_num) ⟨23943, by rfl⟩ (by norm_num))
theorem R63853 : Reach 63853 := rs (se 3 (by rfl) ⟨11972, by rfl⟩) (B 23945 (by norm_num) ⟨11972, by rfl⟩ (by norm_num))
theorem R63857 : Reach 63857 := rs (se 2 (by rfl) ⟨23946, by rfl⟩) (B 47893 (by norm_num) ⟨23946, by rfl⟩ (by norm_num))
theorem R63861 : Reach 63861 := rs (se 5 (by rfl) ⟨2993, by rfl⟩) (B 5987 (by norm_num) ⟨2993, by rfl⟩ (by norm_num))
theorem R96629 : Reach 96629 := rs (se 5 (by rfl) ⟨4529, by rfl⟩) (B 9059 (by norm_num) ⟨4529, by rfl⟩ (by norm_num))
theorem R63865 : Reach 63865 := rs (se 2 (by rfl) ⟨23949, by rfl⟩) (B 47899 (by norm_num) ⟨23949, by rfl⟩ (by norm_num))
theorem R63869 : Reach 63869 := rs (se 3 (by rfl) ⟨11975, by rfl⟩) (B 23951 (by norm_num) ⟨11975, by rfl⟩ (by norm_num))
theorem R63873 : Reach 63873 := rs (se 2 (by rfl) ⟨23952, by rfl⟩) (B 47905 (by norm_num) ⟨23952, by rfl⟩ (by norm_num))
theorem R63877 : Reach 63877 := rs (se 4 (by rfl) ⟨5988, by rfl⟩) (B 11977 (by norm_num) ⟨5988, by rfl⟩ (by norm_num))
theorem R63881 : Reach 63881 := rs (se 2 (by rfl) ⟨23955, by rfl⟩) (B 47911 (by norm_num) ⟨23955, by rfl⟩ (by norm_num))
theorem R63885 : Reach 63885 := rs (se 3 (by rfl) ⟨11978, by rfl⟩) (B 23957 (by norm_num) ⟨11978, by rfl⟩ (by norm_num))
theorem R96653 : Reach 96653 := rs (se 3 (by rfl) ⟨18122, by rfl⟩) (B 36245 (by norm_num) ⟨18122, by rfl⟩ (by norm_num))
theorem R63889 : Reach 63889 := rs (se 2 (by rfl) ⟨23958, by rfl⟩) (B 47917 (by norm_num) ⟨23958, by rfl⟩ (by norm_num))
theorem R63893 : Reach 63893 := rs (se 6 (by rfl) ⟨1497, by rfl⟩) (B 2995 (by norm_num) ⟨1497, by rfl⟩ (by norm_num))
theorem R63897 : Reach 63897 := rs (se 2 (by rfl) ⟨23961, by rfl⟩) (B 47923 (by norm_num) ⟨23961, by rfl⟩ (by norm_num))
theorem R63901 : Reach 63901 := rs (se 3 (by rfl) ⟨11981, by rfl⟩) (B 23963 (by norm_num) ⟨11981, by rfl⟩ (by norm_num))
theorem R63905 : Reach 63905 := rs (se 2 (by rfl) ⟨23964, by rfl⟩) (B 47929 (by norm_num) ⟨23964, by rfl⟩ (by norm_num))
theorem R63909 : Reach 63909 := rs (se 4 (by rfl) ⟨5991, by rfl⟩) (B 11983 (by norm_num) ⟨5991, by rfl⟩ (by norm_num))
theorem R96677 : Reach 96677 := rs (se 4 (by rfl) ⟨9063, by rfl⟩) (B 18127 (by norm_num) ⟨9063, by rfl⟩ (by norm_num))
theorem R63913 : Reach 63913 := rs (se 2 (by rfl) ⟨23967, by rfl⟩) (B 47935 (by norm_num) ⟨23967, by rfl⟩ (by norm_num))
theorem R63917 : Reach 63917 := rs (se 3 (by rfl) ⟨11984, by rfl⟩) (B 23969 (by norm_num) ⟨11984, by rfl⟩ (by norm_num))
theorem R63921 : Reach 63921 := rs (se 2 (by rfl) ⟨23970, by rfl⟩) (B 47941 (by norm_num) ⟨23970, by rfl⟩ (by norm_num))
theorem R63925 : Reach 63925 := rs (se 5 (by rfl) ⟨2996, by rfl⟩) (B 5993 (by norm_num) ⟨2996, by rfl⟩ (by norm_num))
theorem R63929 : Reach 63929 := rs (se 2 (by rfl) ⟨23973, by rfl⟩) (B 47947 (by norm_num) ⟨23973, by rfl⟩ (by norm_num))
theorem R63933 : Reach 63933 := rs (se 3 (by rfl) ⟨11987, by rfl⟩) (B 23975 (by norm_num) ⟨11987, by rfl⟩ (by norm_num))
theorem R96701 : Reach 96701 := rs (se 3 (by rfl) ⟨18131, by rfl⟩) (B 36263 (by norm_num) ⟨18131, by rfl⟩ (by norm_num))
theorem R63937 : Reach 63937 := rs (se 2 (by rfl) ⟨23976, by rfl⟩) (B 47953 (by norm_num) ⟨23976, by rfl⟩ (by norm_num))
theorem R63941 : Reach 63941 := rs (se 4 (by rfl) ⟨5994, by rfl⟩) (B 11989 (by norm_num) ⟨5994, by rfl⟩ (by norm_num))
theorem R63945 : Reach 63945 := rs (se 2 (by rfl) ⟨23979, by rfl⟩) (B 47959 (by norm_num) ⟨23979, by rfl⟩ (by norm_num))
theorem R63949 : Reach 63949 := rs (se 3 (by rfl) ⟨11990, by rfl⟩) (B 23981 (by norm_num) ⟨11990, by rfl⟩ (by norm_num))
theorem R63953 : Reach 63953 := rs (se 2 (by rfl) ⟨23982, by rfl⟩) (B 47965 (by norm_num) ⟨23982, by rfl⟩ (by norm_num))
theorem R63957 : Reach 63957 := rs (se 7 (by rfl) ⟨749, by rfl⟩) (B 1499 (by norm_num) ⟨749, by rfl⟩ (by norm_num))
theorem R96725 : Reach 96725 := rs (se 7 (by rfl) ⟨1133, by rfl⟩) (B 2267 (by norm_num) ⟨1133, by rfl⟩ (by norm_num))
theorem R63961 : Reach 63961 := rs (se 2 (by rfl) ⟨23985, by rfl⟩) (B 47971 (by norm_num) ⟨23985, by rfl⟩ (by norm_num))
theorem R63965 : Reach 63965 := rs (se 3 (by rfl) ⟨11993, by rfl⟩) (B 23987 (by norm_num) ⟨11993, by rfl⟩ (by norm_num))
theorem R63969 : Reach 63969 := rs (se 2 (by rfl) ⟨23988, by rfl⟩) (B 47977 (by norm_num) ⟨23988, by rfl⟩ (by norm_num))
theorem R63973 : Reach 63973 := rs (se 4 (by rfl) ⟨5997, by rfl⟩) (B 11995 (by norm_num) ⟨5997, by rfl⟩ (by norm_num))
theorem R63977 : Reach 63977 := rs (se 2 (by rfl) ⟨23991, by rfl⟩) (B 47983 (by norm_num) ⟨23991, by rfl⟩ (by norm_num))
theorem R63981 : Reach 63981 := rs (se 3 (by rfl) ⟨11996, by rfl⟩) (B 23993 (by norm_num) ⟨11996, by rfl⟩ (by norm_num))
theorem R96749 : Reach 96749 := rs (se 3 (by rfl) ⟨18140, by rfl⟩) (B 36281 (by norm_num) ⟨18140, by rfl⟩ (by norm_num))
theorem R63985 : Reach 63985 := rs (se 2 (by rfl) ⟨23994, by rfl⟩) (B 47989 (by norm_num) ⟨23994, by rfl⟩ (by norm_num))
theorem R63989 : Reach 63989 := rs (se 5 (by rfl) ⟨2999, by rfl⟩) (B 5999 (by norm_num) ⟨2999, by rfl⟩ (by norm_num))
theorem R63993 : Reach 63993 := rs (se 2 (by rfl) ⟨23997, by rfl⟩) (B 47995 (by norm_num) ⟨23997, by rfl⟩ (by norm_num))
theorem R63997 : Reach 63997 := rs (se 3 (by rfl) ⟨11999, by rfl⟩) (B 23999 (by norm_num) ⟨11999, by rfl⟩ (by norm_num))
theorem R64001 : Reach 64001 := rs (se 2 (by rfl) ⟨24000, by rfl⟩) (B 48001 (by norm_num) ⟨24000, by rfl⟩ (by norm_num))
theorem R64005 : Reach 64005 := rs (se 4 (by rfl) ⟨6000, by rfl⟩) (B 12001 (by norm_num) ⟨6000, by rfl⟩ (by norm_num))
theorem R96773 : Reach 96773 := rs (se 4 (by rfl) ⟨9072, by rfl⟩) (B 18145 (by norm_num) ⟨9072, by rfl⟩ (by norm_num))
theorem R64009 : Reach 64009 := rs (se 2 (by rfl) ⟨24003, by rfl⟩) (B 48007 (by norm_num) ⟨24003, by rfl⟩ (by norm_num))
theorem R64013 : Reach 64013 := rs (se 3 (by rfl) ⟨12002, by rfl⟩) (B 24005 (by norm_num) ⟨12002, by rfl⟩ (by norm_num))
theorem R64017 : Reach 64017 := rs (se 2 (by rfl) ⟨24006, by rfl⟩) (B 48013 (by norm_num) ⟨24006, by rfl⟩ (by norm_num))
theorem R64021 : Reach 64021 := rs (se 6 (by rfl) ⟨1500, by rfl⟩) (B 3001 (by norm_num) ⟨1500, by rfl⟩ (by norm_num))
theorem R64025 : Reach 64025 := rs (se 2 (by rfl) ⟨24009, by rfl⟩) (B 48019 (by norm_num) ⟨24009, by rfl⟩ (by norm_num))
theorem R64029 : Reach 64029 := rs (se 3 (by rfl) ⟨12005, by rfl⟩) (B 24011 (by norm_num) ⟨12005, by rfl⟩ (by norm_num))
theorem R96797 : Reach 96797 := rs (se 3 (by rfl) ⟨18149, by rfl⟩) (B 36299 (by norm_num) ⟨18149, by rfl⟩ (by norm_num))
theorem R64033 : Reach 64033 := rs (se 2 (by rfl) ⟨24012, by rfl⟩) (B 48025 (by norm_num) ⟨24012, by rfl⟩ (by norm_num))
theorem R64037 : Reach 64037 := rs (se 4 (by rfl) ⟨6003, by rfl⟩) (B 12007 (by norm_num) ⟨6003, by rfl⟩ (by norm_num))
theorem R64041 : Reach 64041 := rs (se 2 (by rfl) ⟨24015, by rfl⟩) (B 48031 (by norm_num) ⟨24015, by rfl⟩ (by norm_num))
theorem R64045 : Reach 64045 := rs (se 3 (by rfl) ⟨12008, by rfl⟩) (B 24017 (by norm_num) ⟨12008, by rfl⟩ (by norm_num))
theorem R64049 : Reach 64049 := rs (se 2 (by rfl) ⟨24018, by rfl⟩) (B 48037 (by norm_num) ⟨24018, by rfl⟩ (by norm_num))
theorem R64053 : Reach 64053 := rs (se 5 (by rfl) ⟨3002, by rfl⟩) (B 6005 (by norm_num) ⟨3002, by rfl⟩ (by norm_num))
theorem R96821 : Reach 96821 := rs (se 5 (by rfl) ⟨4538, by rfl⟩) (B 9077 (by norm_num) ⟨4538, by rfl⟩ (by norm_num))
theorem R64057 : Reach 64057 := rs (se 2 (by rfl) ⟨24021, by rfl⟩) (B 48043 (by norm_num) ⟨24021, by rfl⟩ (by norm_num))
theorem R64061 : Reach 64061 := rs (se 3 (by rfl) ⟨12011, by rfl⟩) (B 24023 (by norm_num) ⟨12011, by rfl⟩ (by norm_num))
theorem R64065 : Reach 64065 := rs (se 2 (by rfl) ⟨24024, by rfl⟩) (B 48049 (by norm_num) ⟨24024, by rfl⟩ (by norm_num))
theorem R64069 : Reach 64069 := rs (se 4 (by rfl) ⟨6006, by rfl⟩) (B 12013 (by norm_num) ⟨6006, by rfl⟩ (by norm_num))
theorem R64073 : Reach 64073 := rs (se 2 (by rfl) ⟨24027, by rfl⟩) (B 48055 (by norm_num) ⟨24027, by rfl⟩ (by norm_num))
theorem R64077 : Reach 64077 := rs (se 3 (by rfl) ⟨12014, by rfl⟩) (B 24029 (by norm_num) ⟨12014, by rfl⟩ (by norm_num))
theorem R96845 : Reach 96845 := rs (se 3 (by rfl) ⟨18158, by rfl⟩) (B 36317 (by norm_num) ⟨18158, by rfl⟩ (by norm_num))
theorem R64081 : Reach 64081 := rs (se 2 (by rfl) ⟨24030, by rfl⟩) (B 48061 (by norm_num) ⟨24030, by rfl⟩ (by norm_num))
theorem R64085 : Reach 64085 := rs (se 8 (by rfl) ⟨375, by rfl⟩) (B 751 (by norm_num) ⟨375, by rfl⟩ (by norm_num))
theorem R64089 : Reach 64089 := rs (se 2 (by rfl) ⟨24033, by rfl⟩) (B 48067 (by norm_num) ⟨24033, by rfl⟩ (by norm_num))
theorem R64093 : Reach 64093 := rs (se 3 (by rfl) ⟨12017, by rfl⟩) (B 24035 (by norm_num) ⟨12017, by rfl⟩ (by norm_num))
theorem R64097 : Reach 64097 := rs (se 2 (by rfl) ⟨24036, by rfl⟩) (B 48073 (by norm_num) ⟨24036, by rfl⟩ (by norm_num))
theorem R64101 : Reach 64101 := rs (se 4 (by rfl) ⟨6009, by rfl⟩) (B 12019 (by norm_num) ⟨6009, by rfl⟩ (by norm_num))
theorem R96869 : Reach 96869 := rs (se 4 (by rfl) ⟨9081, by rfl⟩) (B 18163 (by norm_num) ⟨9081, by rfl⟩ (by norm_num))
theorem R64105 : Reach 64105 := rs (se 2 (by rfl) ⟨24039, by rfl⟩) (B 48079 (by norm_num) ⟨24039, by rfl⟩ (by norm_num))
theorem R64109 : Reach 64109 := rs (se 3 (by rfl) ⟨12020, by rfl⟩) (B 24041 (by norm_num) ⟨12020, by rfl⟩ (by norm_num))
theorem R64113 : Reach 64113 := rs (se 2 (by rfl) ⟨24042, by rfl⟩) (B 48085 (by norm_num) ⟨24042, by rfl⟩ (by norm_num))
theorem R64117 : Reach 64117 := rs (se 5 (by rfl) ⟨3005, by rfl⟩) (B 6011 (by norm_num) ⟨3005, by rfl⟩ (by norm_num))
theorem R64121 : Reach 64121 := rs (se 2 (by rfl) ⟨24045, by rfl⟩) (B 48091 (by norm_num) ⟨24045, by rfl⟩ (by norm_num))
theorem R96893 : Reach 96893 := rs (se 3 (by rfl) ⟨18167, by rfl⟩) (B 36335 (by norm_num) ⟨18167, by rfl⟩ (by norm_num))
theorem R64125 : Reach 64125 := rs (se 3 (by rfl) ⟨12023, by rfl⟩) (B 24047 (by norm_num) ⟨12023, by rfl⟩ (by norm_num))
theorem R64129 : Reach 64129 := rs (se 2 (by rfl) ⟨24048, by rfl⟩) (B 48097 (by norm_num) ⟨24048, by rfl⟩ (by norm_num))
theorem R64133 : Reach 64133 := rs (se 4 (by rfl) ⟨6012, by rfl⟩) (B 12025 (by norm_num) ⟨6012, by rfl⟩ (by norm_num))
theorem R195205 : Reach 195205 := rs (se 4 (by rfl) ⟨18300, by rfl⟩) (B 36601 (by norm_num) ⟨18300, by rfl⟩ (by norm_num))
theorem R64137 : Reach 64137 := rs (se 2 (by rfl) ⟨24051, by rfl⟩) (B 48103 (by norm_num) ⟨24051, by rfl⟩ (by norm_num))
theorem R64141 : Reach 64141 := rs (se 3 (by rfl) ⟨12026, by rfl⟩) (B 24053 (by norm_num) ⟨12026, by rfl⟩ (by norm_num))
theorem R162445 : Reach 162445 := rs (se 3 (by rfl) ⟨30458, by rfl⟩) (B 60917 (by norm_num) ⟨30458, by rfl⟩ (by norm_num))
theorem R64145 : Reach 64145 := rs (se 2 (by rfl) ⟨24054, by rfl⟩) (B 48109 (by norm_num) ⟨24054, by rfl⟩ (by norm_num))
theorem R64149 : Reach 64149 := rs (se 6 (by rfl) ⟨1503, by rfl⟩) (B 3007 (by norm_num) ⟨1503, by rfl⟩ (by norm_num))
theorem R96917 : Reach 96917 := rs (se 6 (by rfl) ⟨2271, by rfl⟩) (B 4543 (by norm_num) ⟨2271, by rfl⟩ (by norm_num))
theorem R64153 : Reach 64153 := rs (se 2 (by rfl) ⟨24057, by rfl⟩) (B 48115 (by norm_num) ⟨24057, by rfl⟩ (by norm_num))
theorem R64157 : Reach 64157 := rs (se 3 (by rfl) ⟨12029, by rfl⟩) (B 24059 (by norm_num) ⟨12029, by rfl⟩ (by norm_num))
theorem R64161 : Reach 64161 := rs (se 2 (by rfl) ⟨24060, by rfl⟩) (B 48121 (by norm_num) ⟨24060, by rfl⟩ (by norm_num))
theorem R64165 : Reach 64165 := rs (se 4 (by rfl) ⟨6015, by rfl⟩) (B 12031 (by norm_num) ⟨6015, by rfl⟩ (by norm_num))
theorem R64169 : Reach 64169 := rs (se 2 (by rfl) ⟨24063, by rfl⟩) (B 48127 (by norm_num) ⟨24063, by rfl⟩ (by norm_num))
theorem R64173 : Reach 64173 := rs (se 3 (by rfl) ⟨12032, by rfl⟩) (B 24065 (by norm_num) ⟨12032, by rfl⟩ (by norm_num))
theorem R96941 : Reach 96941 := rs (se 3 (by rfl) ⟨18176, by rfl⟩) (B 36353 (by norm_num) ⟨18176, by rfl⟩ (by norm_num))
theorem R64177 : Reach 64177 := rs (se 2 (by rfl) ⟨24066, by rfl⟩) (B 48133 (by norm_num) ⟨24066, by rfl⟩ (by norm_num))
theorem R64181 : Reach 64181 := rs (se 5 (by rfl) ⟨3008, by rfl⟩) (B 6017 (by norm_num) ⟨3008, by rfl⟩ (by norm_num))
theorem R64185 : Reach 64185 := rs (se 2 (by rfl) ⟨24069, by rfl⟩) (B 48139 (by norm_num) ⟨24069, by rfl⟩ (by norm_num))
theorem R64189 : Reach 64189 := rs (se 3 (by rfl) ⟨12035, by rfl⟩) (B 24071 (by norm_num) ⟨12035, by rfl⟩ (by norm_num))
theorem R64193 : Reach 64193 := rs (se 2 (by rfl) ⟨24072, by rfl⟩) (B 48145 (by norm_num) ⟨24072, by rfl⟩ (by norm_num))
theorem R96965 : Reach 96965 := rs (se 4 (by rfl) ⟨9090, by rfl⟩) (B 18181 (by norm_num) ⟨9090, by rfl⟩ (by norm_num))
theorem R64197 : Reach 64197 := rs (se 4 (by rfl) ⟨6018, by rfl⟩) (B 12037 (by norm_num) ⟨6018, by rfl⟩ (by norm_num))
theorem R64201 : Reach 64201 := rs (se 2 (by rfl) ⟨24075, by rfl⟩) (B 48151 (by norm_num) ⟨24075, by rfl⟩ (by norm_num))
theorem R64205 : Reach 64205 := rs (se 3 (by rfl) ⟨12038, by rfl⟩) (B 24077 (by norm_num) ⟨12038, by rfl⟩ (by norm_num))
theorem R64209 : Reach 64209 := rs (se 2 (by rfl) ⟨24078, by rfl⟩) (B 48157 (by norm_num) ⟨24078, by rfl⟩ (by norm_num))
theorem R64213 : Reach 64213 := rs (se 7 (by rfl) ⟨752, by rfl⟩) (B 1505 (by norm_num) ⟨752, by rfl⟩ (by norm_num))
theorem R64217 : Reach 64217 := rs (se 2 (by rfl) ⟨24081, by rfl⟩) (B 48163 (by norm_num) ⟨24081, by rfl⟩ (by norm_num))
theorem R64221 : Reach 64221 := rs (se 3 (by rfl) ⟨12041, by rfl⟩) (B 24083 (by norm_num) ⟨12041, by rfl⟩ (by norm_num))
theorem R96989 : Reach 96989 := rs (se 3 (by rfl) ⟨18185, by rfl⟩) (B 36371 (by norm_num) ⟨18185, by rfl⟩ (by norm_num))
theorem R64225 : Reach 64225 := rs (se 2 (by rfl) ⟨24084, by rfl⟩) (B 48169 (by norm_num) ⟨24084, by rfl⟩ (by norm_num))
theorem R64229 : Reach 64229 := rs (se 4 (by rfl) ⟨6021, by rfl⟩) (B 12043 (by norm_num) ⟨6021, by rfl⟩ (by norm_num))
theorem R64233 : Reach 64233 := rs (se 2 (by rfl) ⟨24087, by rfl⟩) (B 48175 (by norm_num) ⟨24087, by rfl⟩ (by norm_num))
theorem R64237 : Reach 64237 := rs (se 3 (by rfl) ⟨12044, by rfl⟩) (B 24089 (by norm_num) ⟨12044, by rfl⟩ (by norm_num))
theorem R64241 : Reach 64241 := rs (se 2 (by rfl) ⟨24090, by rfl⟩) (B 48181 (by norm_num) ⟨24090, by rfl⟩ (by norm_num))
theorem R64245 : Reach 64245 := rs (se 5 (by rfl) ⟨3011, by rfl⟩) (B 6023 (by norm_num) ⟨3011, by rfl⟩ (by norm_num))
theorem R97013 : Reach 97013 := rs (se 5 (by rfl) ⟨4547, by rfl⟩) (B 9095 (by norm_num) ⟨4547, by rfl⟩ (by norm_num))
theorem R64249 : Reach 64249 := rs (se 2 (by rfl) ⟨24093, by rfl⟩) (B 48187 (by norm_num) ⟨24093, by rfl⟩ (by norm_num))
theorem R162557 : Reach 162557 := rs (se 3 (by rfl) ⟨30479, by rfl⟩) (B 60959 (by norm_num) ⟨30479, by rfl⟩ (by norm_num))
theorem R64253 : Reach 64253 := rs (se 3 (by rfl) ⟨12047, by rfl⟩) (B 24095 (by norm_num) ⟨12047, by rfl⟩ (by norm_num))
theorem R64257 : Reach 64257 := rs (se 2 (by rfl) ⟨24096, by rfl⟩) (B 48193 (by norm_num) ⟨24096, by rfl⟩ (by norm_num))
theorem R64261 : Reach 64261 := rs (se 4 (by rfl) ⟨6024, by rfl⟩) (B 12049 (by norm_num) ⟨6024, by rfl⟩ (by norm_num))
theorem R64265 : Reach 64265 := rs (se 2 (by rfl) ⟨24099, by rfl⟩) (B 48199 (by norm_num) ⟨24099, by rfl⟩ (by norm_num))
theorem R64269 : Reach 64269 := rs (se 3 (by rfl) ⟨12050, by rfl⟩) (B 24101 (by norm_num) ⟨12050, by rfl⟩ (by norm_num))
theorem R97037 : Reach 97037 := rs (se 3 (by rfl) ⟨18194, by rfl⟩) (B 36389 (by norm_num) ⟨18194, by rfl⟩ (by norm_num))
theorem R64273 : Reach 64273 := rs (se 2 (by rfl) ⟨24102, by rfl⟩) (B 48205 (by norm_num) ⟨24102, by rfl⟩ (by norm_num))
theorem R64277 : Reach 64277 := rs (se 6 (by rfl) ⟨1506, by rfl⟩) (B 3013 (by norm_num) ⟨1506, by rfl⟩ (by norm_num))
theorem R64281 : Reach 64281 := rs (se 2 (by rfl) ⟨24105, by rfl⟩) (B 48211 (by norm_num) ⟨24105, by rfl⟩ (by norm_num))
theorem R64285 : Reach 64285 := rs (se 3 (by rfl) ⟨12053, by rfl⟩) (B 24107 (by norm_num) ⟨12053, by rfl⟩ (by norm_num))
theorem R64289 : Reach 64289 := rs (se 2 (by rfl) ⟨24108, by rfl⟩) (B 48217 (by norm_num) ⟨24108, by rfl⟩ (by norm_num))
theorem R64293 : Reach 64293 := rs (se 4 (by rfl) ⟨6027, by rfl⟩) (B 12055 (by norm_num) ⟨6027, by rfl⟩ (by norm_num))
theorem R97061 : Reach 97061 := rs (se 4 (by rfl) ⟨9099, by rfl⟩) (B 18199 (by norm_num) ⟨9099, by rfl⟩ (by norm_num))
theorem R64297 : Reach 64297 := rs (se 2 (by rfl) ⟨24111, by rfl⟩) (B 48223 (by norm_num) ⟨24111, by rfl⟩ (by norm_num))
theorem R64301 : Reach 64301 := rs (se 3 (by rfl) ⟨12056, by rfl⟩) (B 24113 (by norm_num) ⟨12056, by rfl⟩ (by norm_num))
theorem R64305 : Reach 64305 := rs (se 2 (by rfl) ⟨24114, by rfl⟩) (B 48229 (by norm_num) ⟨24114, by rfl⟩ (by norm_num))
theorem R64309 : Reach 64309 := rs (se 5 (by rfl) ⟨3014, by rfl⟩) (B 6029 (by norm_num) ⟨3014, by rfl⟩ (by norm_num))
theorem R64313 : Reach 64313 := rs (se 2 (by rfl) ⟨24117, by rfl⟩) (B 48235 (by norm_num) ⟨24117, by rfl⟩ (by norm_num))
theorem R64317 : Reach 64317 := rs (se 3 (by rfl) ⟨12059, by rfl⟩) (B 24119 (by norm_num) ⟨12059, by rfl⟩ (by norm_num))
theorem R97085 : Reach 97085 := rs (se 3 (by rfl) ⟨18203, by rfl⟩) (B 36407 (by norm_num) ⟨18203, by rfl⟩ (by norm_num))
theorem R64321 : Reach 64321 := rs (se 2 (by rfl) ⟨24120, by rfl⟩) (B 48241 (by norm_num) ⟨24120, by rfl⟩ (by norm_num))
theorem R64325 : Reach 64325 := rs (se 4 (by rfl) ⟨6030, by rfl⟩) (B 12061 (by norm_num) ⟨6030, by rfl⟩ (by norm_num))
theorem R64329 : Reach 64329 := rs (se 2 (by rfl) ⟨24123, by rfl⟩) (B 48247 (by norm_num) ⟨24123, by rfl⟩ (by norm_num))
theorem R64333 : Reach 64333 := rs (se 3 (by rfl) ⟨12062, by rfl⟩) (B 24125 (by norm_num) ⟨12062, by rfl⟩ (by norm_num))
theorem R64337 : Reach 64337 := rs (se 2 (by rfl) ⟨24126, by rfl⟩) (B 48253 (by norm_num) ⟨24126, by rfl⟩ (by norm_num))
theorem R64341 : Reach 64341 := rs (se 9 (by rfl) ⟨188, by rfl⟩) (B 377 (by norm_num) ⟨188, by rfl⟩ (by norm_num))
theorem R97109 : Reach 97109 := rs (se 9 (by rfl) ⟨284, by rfl⟩) (B 569 (by norm_num) ⟨284, by rfl⟩ (by norm_num))
theorem R64345 : Reach 64345 := rs (se 2 (by rfl) ⟨24129, by rfl⟩) (B 48259 (by norm_num) ⟨24129, by rfl⟩ (by norm_num))
theorem R64349 : Reach 64349 := rs (se 3 (by rfl) ⟨12065, by rfl⟩) (B 24131 (by norm_num) ⟨12065, by rfl⟩ (by norm_num))
theorem R64353 : Reach 64353 := rs (se 2 (by rfl) ⟨24132, by rfl⟩) (B 48265 (by norm_num) ⟨24132, by rfl⟩ (by norm_num))
theorem R64357 : Reach 64357 := rs (se 4 (by rfl) ⟨6033, by rfl⟩) (B 12067 (by norm_num) ⟨6033, by rfl⟩ (by norm_num))
theorem R64361 : Reach 64361 := rs (se 2 (by rfl) ⟨24135, by rfl⟩) (B 48271 (by norm_num) ⟨24135, by rfl⟩ (by norm_num))
theorem R64365 : Reach 64365 := rs (se 3 (by rfl) ⟨12068, by rfl⟩) (B 24137 (by norm_num) ⟨12068, by rfl⟩ (by norm_num))
theorem R97133 : Reach 97133 := rs (se 3 (by rfl) ⟨18212, by rfl⟩) (B 36425 (by norm_num) ⟨18212, by rfl⟩ (by norm_num))
theorem R64369 : Reach 64369 := rs (se 2 (by rfl) ⟨24138, by rfl⟩) (B 48277 (by norm_num) ⟨24138, by rfl⟩ (by norm_num))
theorem R64373 : Reach 64373 := rs (se 5 (by rfl) ⟨3017, by rfl⟩) (B 6035 (by norm_num) ⟨3017, by rfl⟩ (by norm_num))
theorem R64377 : Reach 64377 := rs (se 2 (by rfl) ⟨24141, by rfl⟩) (B 48283 (by norm_num) ⟨24141, by rfl⟩ (by norm_num))
theorem R64381 : Reach 64381 := rs (se 3 (by rfl) ⟨12071, by rfl⟩) (B 24143 (by norm_num) ⟨12071, by rfl⟩ (by norm_num))
theorem R64385 : Reach 64385 := rs (se 2 (by rfl) ⟨24144, by rfl⟩) (B 48289 (by norm_num) ⟨24144, by rfl⟩ (by norm_num))
theorem R64389 : Reach 64389 := rs (se 4 (by rfl) ⟨6036, by rfl⟩) (B 12073 (by norm_num) ⟨6036, by rfl⟩ (by norm_num))
theorem R97157 : Reach 97157 := rs (se 4 (by rfl) ⟨9108, by rfl⟩) (B 18217 (by norm_num) ⟨9108, by rfl⟩ (by norm_num))
theorem R64393 : Reach 64393 := rs (se 2 (by rfl) ⟨24147, by rfl⟩) (B 48295 (by norm_num) ⟨24147, by rfl⟩ (by norm_num))
theorem R64397 : Reach 64397 := rs (se 3 (by rfl) ⟨12074, by rfl⟩) (B 24149 (by norm_num) ⟨12074, by rfl⟩ (by norm_num))
theorem R64401 : Reach 64401 := rs (se 2 (by rfl) ⟨24150, by rfl⟩) (B 48301 (by norm_num) ⟨24150, by rfl⟩ (by norm_num))
theorem R129941 : Reach 129941 := rs (se 6 (by rfl) ⟨3045, by rfl⟩) (B 6091 (by norm_num) ⟨3045, by rfl⟩ (by norm_num))
theorem R64405 : Reach 64405 := rs (se 6 (by rfl) ⟨1509, by rfl⟩) (B 3019 (by norm_num) ⟨1509, by rfl⟩ (by norm_num))
theorem R64409 : Reach 64409 := rs (se 2 (by rfl) ⟨24153, by rfl⟩) (B 48307 (by norm_num) ⟨24153, by rfl⟩ (by norm_num))
theorem R64413 : Reach 64413 := rs (se 3 (by rfl) ⟨12077, by rfl⟩) (B 24155 (by norm_num) ⟨12077, by rfl⟩ (by norm_num))
theorem R97181 : Reach 97181 := rs (se 3 (by rfl) ⟨18221, by rfl⟩) (B 36443 (by norm_num) ⟨18221, by rfl⟩ (by norm_num))
theorem R64417 : Reach 64417 := rs (se 2 (by rfl) ⟨24156, by rfl⟩) (B 48313 (by norm_num) ⟨24156, by rfl⟩ (by norm_num))
theorem R64421 : Reach 64421 := rs (se 4 (by rfl) ⟨6039, by rfl⟩) (B 12079 (by norm_num) ⟨6039, by rfl⟩ (by norm_num))
theorem R64425 : Reach 64425 := rs (se 2 (by rfl) ⟨24159, by rfl⟩) (B 48319 (by norm_num) ⟨24159, by rfl⟩ (by norm_num))
theorem R64429 : Reach 64429 := rs (se 3 (by rfl) ⟨12080, by rfl⟩) (B 24161 (by norm_num) ⟨12080, by rfl⟩ (by norm_num))
theorem R64433 : Reach 64433 := rs (se 2 (by rfl) ⟨24162, by rfl⟩) (B 48325 (by norm_num) ⟨24162, by rfl⟩ (by norm_num))
theorem R64437 : Reach 64437 := rs (se 5 (by rfl) ⟨3020, by rfl⟩) (B 6041 (by norm_num) ⟨3020, by rfl⟩ (by norm_num))
theorem R97205 : Reach 97205 := rs (se 5 (by rfl) ⟨4556, by rfl⟩) (B 9113 (by norm_num) ⟨4556, by rfl⟩ (by norm_num))
theorem R64441 : Reach 64441 := rs (se 2 (by rfl) ⟨24165, by rfl⟩) (B 48331 (by norm_num) ⟨24165, by rfl⟩ (by norm_num))
theorem R162749 : Reach 162749 := rs (se 3 (by rfl) ⟨30515, by rfl⟩) (B 61031 (by norm_num) ⟨30515, by rfl⟩ (by norm_num))
theorem R64445 : Reach 64445 := rs (se 3 (by rfl) ⟨12083, by rfl⟩) (B 24167 (by norm_num) ⟨12083, by rfl⟩ (by norm_num))
theorem R64449 : Reach 64449 := rs (se 2 (by rfl) ⟨24168, by rfl⟩) (B 48337 (by norm_num) ⟨24168, by rfl⟩ (by norm_num))
theorem R64453 : Reach 64453 := rs (se 4 (by rfl) ⟨6042, by rfl⟩) (B 12085 (by norm_num) ⟨6042, by rfl⟩ (by norm_num))
theorem R64457 : Reach 64457 := rs (se 2 (by rfl) ⟨24171, by rfl⟩) (B 48343 (by norm_num) ⟨24171, by rfl⟩ (by norm_num))
theorem R97229 : Reach 97229 := rs (se 3 (by rfl) ⟨18230, by rfl⟩) (B 36461 (by norm_num) ⟨18230, by rfl⟩ (by norm_num))
theorem R64461 : Reach 64461 := rs (se 3 (by rfl) ⟨12086, by rfl⟩) (B 24173 (by norm_num) ⟨12086, by rfl⟩ (by norm_num))
theorem R64465 : Reach 64465 := rs (se 2 (by rfl) ⟨24174, by rfl⟩) (B 48349 (by norm_num) ⟨24174, by rfl⟩ (by norm_num))
theorem R64469 : Reach 64469 := rs (se 7 (by rfl) ⟨755, by rfl⟩) (B 1511 (by norm_num) ⟨755, by rfl⟩ (by norm_num))
theorem R64473 : Reach 64473 := rs (se 2 (by rfl) ⟨24177, by rfl⟩) (B 48355 (by norm_num) ⟨24177, by rfl⟩ (by norm_num))
theorem R64477 : Reach 64477 := rs (se 3 (by rfl) ⟨12089, by rfl⟩) (B 24179 (by norm_num) ⟨12089, by rfl⟩ (by norm_num))
theorem R64481 : Reach 64481 := rs (se 2 (by rfl) ⟨24180, by rfl⟩) (B 48361 (by norm_num) ⟨24180, by rfl⟩ (by norm_num))
theorem R64485 : Reach 64485 := rs (se 4 (by rfl) ⟨6045, by rfl⟩) (B 12091 (by norm_num) ⟨6045, by rfl⟩ (by norm_num))
theorem R97253 : Reach 97253 := rs (se 4 (by rfl) ⟨9117, by rfl⟩) (B 18235 (by norm_num) ⟨9117, by rfl⟩ (by norm_num))
theorem R64489 : Reach 64489 := rs (se 2 (by rfl) ⟨24183, by rfl⟩) (B 48367 (by norm_num) ⟨24183, by rfl⟩ (by norm_num))
theorem R64493 : Reach 64493 := rs (se 3 (by rfl) ⟨12092, by rfl⟩) (B 24185 (by norm_num) ⟨12092, by rfl⟩ (by norm_num))
theorem R64497 : Reach 64497 := rs (se 2 (by rfl) ⟨24186, by rfl⟩) (B 48373 (by norm_num) ⟨24186, by rfl⟩ (by norm_num))
theorem R64501 : Reach 64501 := rs (se 5 (by rfl) ⟨3023, by rfl⟩) (B 6047 (by norm_num) ⟨3023, by rfl⟩ (by norm_num))
theorem R64505 : Reach 64505 := rs (se 2 (by rfl) ⟨24189, by rfl⟩) (B 48379 (by norm_num) ⟨24189, by rfl⟩ (by norm_num))
theorem R64509 : Reach 64509 := rs (se 3 (by rfl) ⟨12095, by rfl⟩) (B 24191 (by norm_num) ⟨12095, by rfl⟩ (by norm_num))
theorem R97277 : Reach 97277 := rs (se 3 (by rfl) ⟨18239, by rfl⟩) (B 36479 (by norm_num) ⟨18239, by rfl⟩ (by norm_num))
theorem R64513 : Reach 64513 := rs (se 2 (by rfl) ⟨24192, by rfl⟩) (B 48385 (by norm_num) ⟨24192, by rfl⟩ (by norm_num))
theorem R64517 : Reach 64517 := rs (se 4 (by rfl) ⟨6048, by rfl⟩) (B 12097 (by norm_num) ⟨6048, by rfl⟩ (by norm_num))
theorem R64521 : Reach 64521 := rs (se 2 (by rfl) ⟨24195, by rfl⟩) (B 48391 (by norm_num) ⟨24195, by rfl⟩ (by norm_num))
theorem R64525 : Reach 64525 := rs (se 3 (by rfl) ⟨12098, by rfl⟩) (B 24197 (by norm_num) ⟨12098, by rfl⟩ (by norm_num))
theorem R64529 : Reach 64529 := rs (se 2 (by rfl) ⟨24198, by rfl⟩) (B 48397 (by norm_num) ⟨24198, by rfl⟩ (by norm_num))
theorem R64533 : Reach 64533 := rs (se 6 (by rfl) ⟨1512, by rfl⟩) (B 3025 (by norm_num) ⟨1512, by rfl⟩ (by norm_num))
theorem R97301 : Reach 97301 := rs (se 6 (by rfl) ⟨2280, by rfl⟩) (B 4561 (by norm_num) ⟨2280, by rfl⟩ (by norm_num))
theorem R64537 : Reach 64537 := rs (se 2 (by rfl) ⟨24201, by rfl⟩) (B 48403 (by norm_num) ⟨24201, by rfl⟩ (by norm_num))
theorem R64541 : Reach 64541 := rs (se 3 (by rfl) ⟨12101, by rfl⟩) (B 24203 (by norm_num) ⟨12101, by rfl⟩ (by norm_num))
theorem R64545 : Reach 64545 := rs (se 2 (by rfl) ⟨24204, by rfl⟩) (B 48409 (by norm_num) ⟨24204, by rfl⟩ (by norm_num))
theorem R64549 : Reach 64549 := rs (se 4 (by rfl) ⟨6051, by rfl⟩) (B 12103 (by norm_num) ⟨6051, by rfl⟩ (by norm_num))
theorem R64553 : Reach 64553 := rs (se 2 (by rfl) ⟨24207, by rfl⟩) (B 48415 (by norm_num) ⟨24207, by rfl⟩ (by norm_num))
theorem R64557 : Reach 64557 := rs (se 3 (by rfl) ⟨12104, by rfl⟩) (B 24209 (by norm_num) ⟨12104, by rfl⟩ (by norm_num))
theorem R97325 : Reach 97325 := rs (se 3 (by rfl) ⟨18248, by rfl⟩) (B 36497 (by norm_num) ⟨18248, by rfl⟩ (by norm_num))
theorem R64561 : Reach 64561 := rs (se 2 (by rfl) ⟨24210, by rfl⟩) (B 48421 (by norm_num) ⟨24210, by rfl⟩ (by norm_num))
theorem R64565 : Reach 64565 := rs (se 5 (by rfl) ⟨3026, by rfl⟩) (B 6053 (by norm_num) ⟨3026, by rfl⟩ (by norm_num))
theorem R64569 : Reach 64569 := rs (se 2 (by rfl) ⟨24213, by rfl⟩) (B 48427 (by norm_num) ⟨24213, by rfl⟩ (by norm_num))
theorem R64573 : Reach 64573 := rs (se 3 (by rfl) ⟨12107, by rfl⟩) (B 24215 (by norm_num) ⟨12107, by rfl⟩ (by norm_num))
theorem R64577 : Reach 64577 := rs (se 2 (by rfl) ⟨24216, by rfl⟩) (B 48433 (by norm_num) ⟨24216, by rfl⟩ (by norm_num))
theorem R64581 : Reach 64581 := rs (se 4 (by rfl) ⟨6054, by rfl⟩) (B 12109 (by norm_num) ⟨6054, by rfl⟩ (by norm_num))
theorem R97349 : Reach 97349 := rs (se 4 (by rfl) ⟨9126, by rfl⟩) (B 18253 (by norm_num) ⟨9126, by rfl⟩ (by norm_num))
theorem R64585 : Reach 64585 := rs (se 2 (by rfl) ⟨24219, by rfl⟩) (B 48439 (by norm_num) ⟨24219, by rfl⟩ (by norm_num))
theorem R64589 : Reach 64589 := rs (se 3 (by rfl) ⟨12110, by rfl⟩) (B 24221 (by norm_num) ⟨12110, by rfl⟩ (by norm_num))
theorem R64593 : Reach 64593 := rs (se 2 (by rfl) ⟨24222, by rfl⟩) (B 48445 (by norm_num) ⟨24222, by rfl⟩ (by norm_num))
theorem R64597 : Reach 64597 := rs (se 8 (by rfl) ⟨378, by rfl⟩) (B 757 (by norm_num) ⟨378, by rfl⟩ (by norm_num))
theorem R326741 : Reach 326741 := rs (se 8 (by rfl) ⟨1914, by rfl⟩) (B 3829 (by norm_num) ⟨1914, by rfl⟩ (by norm_num))
theorem R64601 : Reach 64601 := rs (se 2 (by rfl) ⟨24225, by rfl⟩) (B 48451 (by norm_num) ⟨24225, by rfl⟩ (by norm_num))
theorem R64605 : Reach 64605 := rs (se 3 (by rfl) ⟨12113, by rfl⟩) (B 24227 (by norm_num) ⟨12113, by rfl⟩ (by norm_num))
theorem R97373 : Reach 97373 := rs (se 3 (by rfl) ⟨18257, by rfl⟩) (B 36515 (by norm_num) ⟨18257, by rfl⟩ (by norm_num))
theorem R64609 : Reach 64609 := rs (se 2 (by rfl) ⟨24228, by rfl⟩) (B 48457 (by norm_num) ⟨24228, by rfl⟩ (by norm_num))
theorem R64613 : Reach 64613 := rs (se 4 (by rfl) ⟨6057, by rfl⟩) (B 12115 (by norm_num) ⟨6057, by rfl⟩ (by norm_num))
theorem R64617 : Reach 64617 := rs (se 2 (by rfl) ⟨24231, by rfl⟩) (B 48463 (by norm_num) ⟨24231, by rfl⟩ (by norm_num))
theorem R64621 : Reach 64621 := rs (se 3 (by rfl) ⟨12116, by rfl⟩) (B 24233 (by norm_num) ⟨12116, by rfl⟩ (by norm_num))
theorem R64625 : Reach 64625 := rs (se 2 (by rfl) ⟨24234, by rfl⟩) (B 48469 (by norm_num) ⟨24234, by rfl⟩ (by norm_num))
theorem R64629 : Reach 64629 := rs (se 5 (by rfl) ⟨3029, by rfl⟩) (B 6059 (by norm_num) ⟨3029, by rfl⟩ (by norm_num))
theorem R97397 : Reach 97397 := rs (se 5 (by rfl) ⟨4565, by rfl⟩) (B 9131 (by norm_num) ⟨4565, by rfl⟩ (by norm_num))
theorem R64633 : Reach 64633 := rs (se 2 (by rfl) ⟨24237, by rfl⟩) (B 48475 (by norm_num) ⟨24237, by rfl⟩ (by norm_num))
theorem R64637 : Reach 64637 := rs (se 3 (by rfl) ⟨12119, by rfl⟩) (B 24239 (by norm_num) ⟨12119, by rfl⟩ (by norm_num))
theorem R64641 : Reach 64641 := rs (se 2 (by rfl) ⟨24240, by rfl⟩) (B 48481 (by norm_num) ⟨24240, by rfl⟩ (by norm_num))
theorem R64645 : Reach 64645 := rs (se 4 (by rfl) ⟨6060, by rfl⟩) (B 12121 (by norm_num) ⟨6060, by rfl⟩ (by norm_num))
theorem R64649 : Reach 64649 := rs (se 2 (by rfl) ⟨24243, by rfl⟩) (B 48487 (by norm_num) ⟨24243, by rfl⟩ (by norm_num))
theorem R64653 : Reach 64653 := rs (se 3 (by rfl) ⟨12122, by rfl⟩) (B 24245 (by norm_num) ⟨12122, by rfl⟩ (by norm_num))
theorem R97421 : Reach 97421 := rs (se 3 (by rfl) ⟨18266, by rfl⟩) (B 36533 (by norm_num) ⟨18266, by rfl⟩ (by norm_num))
theorem R64657 : Reach 64657 := rs (se 2 (by rfl) ⟨24246, by rfl⟩) (B 48493 (by norm_num) ⟨24246, by rfl⟩ (by norm_num))
theorem R64661 : Reach 64661 := rs (se 6 (by rfl) ⟨1515, by rfl⟩) (B 3031 (by norm_num) ⟨1515, by rfl⟩ (by norm_num))
theorem R64665 : Reach 64665 := rs (se 2 (by rfl) ⟨24249, by rfl⟩) (B 48499 (by norm_num) ⟨24249, by rfl⟩ (by norm_num))
theorem R64669 : Reach 64669 := rs (se 3 (by rfl) ⟨12125, by rfl⟩) (B 24251 (by norm_num) ⟨12125, by rfl⟩ (by norm_num))
theorem R64673 : Reach 64673 := rs (se 2 (by rfl) ⟨24252, by rfl⟩) (B 48505 (by norm_num) ⟨24252, by rfl⟩ (by norm_num))
theorem R64677 : Reach 64677 := rs (se 4 (by rfl) ⟨6063, by rfl⟩) (B 12127 (by norm_num) ⟨6063, by rfl⟩ (by norm_num))
theorem R97445 : Reach 97445 := rs (se 4 (by rfl) ⟨9135, by rfl⟩) (B 18271 (by norm_num) ⟨9135, by rfl⟩ (by norm_num))
theorem R64681 : Reach 64681 := rs (se 2 (by rfl) ⟨24255, by rfl⟩) (B 48511 (by norm_num) ⟨24255, by rfl⟩ (by norm_num))
theorem R64685 : Reach 64685 := rs (se 3 (by rfl) ⟨12128, by rfl⟩) (B 24257 (by norm_num) ⟨12128, by rfl⟩ (by norm_num))
theorem R64689 : Reach 64689 := rs (se 2 (by rfl) ⟨24258, by rfl⟩) (B 48517 (by norm_num) ⟨24258, by rfl⟩ (by norm_num))
theorem R64693 : Reach 64693 := rs (se 5 (by rfl) ⟨3032, by rfl⟩) (B 6065 (by norm_num) ⟨3032, by rfl⟩ (by norm_num))
theorem R64697 : Reach 64697 := rs (se 2 (by rfl) ⟨24261, by rfl⟩) (B 48523 (by norm_num) ⟨24261, by rfl⟩ (by norm_num))
theorem R64701 : Reach 64701 := rs (se 3 (by rfl) ⟨12131, by rfl⟩) (B 24263 (by norm_num) ⟨12131, by rfl⟩ (by norm_num))
theorem R97469 : Reach 97469 := rs (se 3 (by rfl) ⟨18275, by rfl⟩) (B 36551 (by norm_num) ⟨18275, by rfl⟩ (by norm_num))
theorem R64705 : Reach 64705 := rs (se 2 (by rfl) ⟨24264, by rfl⟩) (B 48529 (by norm_num) ⟨24264, by rfl⟩ (by norm_num))
theorem R64709 : Reach 64709 := rs (se 4 (by rfl) ⟨6066, by rfl⟩) (B 12133 (by norm_num) ⟨6066, by rfl⟩ (by norm_num))
theorem R64713 : Reach 64713 := rs (se 2 (by rfl) ⟨24267, by rfl⟩) (B 48535 (by norm_num) ⟨24267, by rfl⟩ (by norm_num))
theorem R64717 : Reach 64717 := rs (se 3 (by rfl) ⟨12134, by rfl⟩) (B 24269 (by norm_num) ⟨12134, by rfl⟩ (by norm_num))
theorem R64721 : Reach 64721 := rs (se 2 (by rfl) ⟨24270, by rfl⟩) (B 48541 (by norm_num) ⟨24270, by rfl⟩ (by norm_num))
theorem R64725 : Reach 64725 := rs (se 7 (by rfl) ⟨758, by rfl⟩) (B 1517 (by norm_num) ⟨758, by rfl⟩ (by norm_num))
theorem R97493 : Reach 97493 := rs (se 7 (by rfl) ⟨1142, by rfl⟩) (B 2285 (by norm_num) ⟨1142, by rfl⟩ (by norm_num))
theorem R64729 : Reach 64729 := rs (se 2 (by rfl) ⟨24273, by rfl⟩) (B 48547 (by norm_num) ⟨24273, by rfl⟩ (by norm_num))
theorem R64733 : Reach 64733 := rs (se 3 (by rfl) ⟨12137, by rfl⟩) (B 24275 (by norm_num) ⟨12137, by rfl⟩ (by norm_num))
theorem R64737 : Reach 64737 := rs (se 2 (by rfl) ⟨24276, by rfl⟩) (B 48553 (by norm_num) ⟨24276, by rfl⟩ (by norm_num))
theorem R64741 : Reach 64741 := rs (se 4 (by rfl) ⟨6069, by rfl⟩) (B 12139 (by norm_num) ⟨6069, by rfl⟩ (by norm_num))
theorem R64745 : Reach 64745 := rs (se 2 (by rfl) ⟨24279, by rfl⟩) (B 48559 (by norm_num) ⟨24279, by rfl⟩ (by norm_num))
theorem R64749 : Reach 64749 := rs (se 3 (by rfl) ⟨12140, by rfl⟩) (B 24281 (by norm_num) ⟨12140, by rfl⟩ (by norm_num))
theorem R97517 : Reach 97517 := rs (se 3 (by rfl) ⟨18284, by rfl⟩) (B 36569 (by norm_num) ⟨18284, by rfl⟩ (by norm_num))
theorem R64753 : Reach 64753 := rs (se 2 (by rfl) ⟨24282, by rfl⟩) (B 48565 (by norm_num) ⟨24282, by rfl⟩ (by norm_num))
theorem R64757 : Reach 64757 := rs (se 5 (by rfl) ⟨3035, by rfl⟩) (B 6071 (by norm_num) ⟨3035, by rfl⟩ (by norm_num))
theorem R64761 : Reach 64761 := rs (se 2 (by rfl) ⟨24285, by rfl⟩) (B 48571 (by norm_num) ⟨24285, by rfl⟩ (by norm_num))
theorem R64765 : Reach 64765 := rs (se 3 (by rfl) ⟨12143, by rfl⟩) (B 24287 (by norm_num) ⟨12143, by rfl⟩ (by norm_num))
theorem R64769 : Reach 64769 := rs (se 2 (by rfl) ⟨24288, by rfl⟩) (B 48577 (by norm_num) ⟨24288, by rfl⟩ (by norm_num))
theorem R97541 : Reach 97541 := rs (se 4 (by rfl) ⟨9144, by rfl⟩) (B 18289 (by norm_num) ⟨9144, by rfl⟩ (by norm_num))
theorem R64773 : Reach 64773 := rs (se 4 (by rfl) ⟨6072, by rfl⟩) (B 12145 (by norm_num) ⟨6072, by rfl⟩ (by norm_num))
theorem R64777 : Reach 64777 := rs (se 2 (by rfl) ⟨24291, by rfl⟩) (B 48583 (by norm_num) ⟨24291, by rfl⟩ (by norm_num))
theorem R64781 : Reach 64781 := rs (se 3 (by rfl) ⟨12146, by rfl⟩) (B 24293 (by norm_num) ⟨12146, by rfl⟩ (by norm_num))
theorem R64785 : Reach 64785 := rs (se 2 (by rfl) ⟨24294, by rfl⟩) (B 48589 (by norm_num) ⟨24294, by rfl⟩ (by norm_num))
theorem R163093 : Reach 163093 := rs (se 6 (by rfl) ⟨3822, by rfl⟩) (B 7645 (by norm_num) ⟨3822, by rfl⟩ (by norm_num))
theorem R64789 : Reach 64789 := rs (se 6 (by rfl) ⟨1518, by rfl⟩) (B 3037 (by norm_num) ⟨1518, by rfl⟩ (by norm_num))
theorem R64793 : Reach 64793 := rs (se 2 (by rfl) ⟨24297, by rfl⟩) (B 48595 (by norm_num) ⟨24297, by rfl⟩ (by norm_num))
theorem R64797 : Reach 64797 := rs (se 3 (by rfl) ⟨12149, by rfl⟩) (B 24299 (by norm_num) ⟨12149, by rfl⟩ (by norm_num))
theorem R97565 : Reach 97565 := rs (se 3 (by rfl) ⟨18293, by rfl⟩) (B 36587 (by norm_num) ⟨18293, by rfl⟩ (by norm_num))
theorem R64801 : Reach 64801 := rs (se 2 (by rfl) ⟨24300, by rfl⟩) (B 48601 (by norm_num) ⟨24300, by rfl⟩ (by norm_num))
theorem R64805 : Reach 64805 := rs (se 4 (by rfl) ⟨6075, by rfl⟩) (B 12151 (by norm_num) ⟨6075, by rfl⟩ (by norm_num))
theorem R64809 : Reach 64809 := rs (se 2 (by rfl) ⟨24303, by rfl⟩) (B 48607 (by norm_num) ⟨24303, by rfl⟩ (by norm_num))
theorem R64813 : Reach 64813 := rs (se 3 (by rfl) ⟨12152, by rfl⟩) (B 24305 (by norm_num) ⟨12152, by rfl⟩ (by norm_num))
theorem R64817 : Reach 64817 := rs (se 2 (by rfl) ⟨24306, by rfl⟩) (B 48613 (by norm_num) ⟨24306, by rfl⟩ (by norm_num))
theorem R64821 : Reach 64821 := rs (se 5 (by rfl) ⟨3038, by rfl⟩) (B 6077 (by norm_num) ⟨3038, by rfl⟩ (by norm_num))
theorem R97589 : Reach 97589 := rs (se 5 (by rfl) ⟨4574, by rfl⟩) (B 9149 (by norm_num) ⟨4574, by rfl⟩ (by norm_num))
theorem R64825 : Reach 64825 := rs (se 2 (by rfl) ⟨24309, by rfl⟩) (B 48619 (by norm_num) ⟨24309, by rfl⟩ (by norm_num))
theorem R64829 : Reach 64829 := rs (se 3 (by rfl) ⟨12155, by rfl⟩) (B 24311 (by norm_num) ⟨12155, by rfl⟩ (by norm_num))
theorem R64833 : Reach 64833 := rs (se 2 (by rfl) ⟨24312, by rfl⟩) (B 48625 (by norm_num) ⟨24312, by rfl⟩ (by norm_num))
theorem R64837 : Reach 64837 := rs (se 4 (by rfl) ⟨6078, by rfl⟩) (B 12157 (by norm_num) ⟨6078, by rfl⟩ (by norm_num))
theorem R64841 : Reach 64841 := rs (se 2 (by rfl) ⟨24315, by rfl⟩) (B 48631 (by norm_num) ⟨24315, by rfl⟩ (by norm_num))
theorem R64845 : Reach 64845 := rs (se 3 (by rfl) ⟨12158, by rfl⟩) (B 24317 (by norm_num) ⟨12158, by rfl⟩ (by norm_num))
theorem R97613 : Reach 97613 := rs (se 3 (by rfl) ⟨18302, by rfl⟩) (B 36605 (by norm_num) ⟨18302, by rfl⟩ (by norm_num))
theorem R64849 : Reach 64849 := rs (se 2 (by rfl) ⟨24318, by rfl⟩) (B 48637 (by norm_num) ⟨24318, by rfl⟩ (by norm_num))
theorem R64853 : Reach 64853 := rs (se 11 (by rfl) ⟨47, by rfl⟩) (B 95 (by norm_num) ⟨47, by rfl⟩ (by norm_num))
theorem R64857 : Reach 64857 := rs (se 2 (by rfl) ⟨24321, by rfl⟩) (B 48643 (by norm_num) ⟨24321, by rfl⟩ (by norm_num))
theorem R64861 : Reach 64861 := rs (se 3 (by rfl) ⟨12161, by rfl⟩) (B 24323 (by norm_num) ⟨12161, by rfl⟩ (by norm_num))
theorem R64865 : Reach 64865 := rs (se 2 (by rfl) ⟨24324, by rfl⟩) (B 48649 (by norm_num) ⟨24324, by rfl⟩ (by norm_num))
theorem R64869 : Reach 64869 := rs (se 4 (by rfl) ⟨6081, by rfl⟩) (B 12163 (by norm_num) ⟨6081, by rfl⟩ (by norm_num))
theorem R97637 : Reach 97637 := rs (se 4 (by rfl) ⟨9153, by rfl⟩) (B 18307 (by norm_num) ⟨9153, by rfl⟩ (by norm_num))
theorem R64873 : Reach 64873 := rs (se 2 (by rfl) ⟨24327, by rfl⟩) (B 48655 (by norm_num) ⟨24327, by rfl⟩ (by norm_num))
theorem R64877 : Reach 64877 := rs (se 3 (by rfl) ⟨12164, by rfl⟩) (B 24329 (by norm_num) ⟨12164, by rfl⟩ (by norm_num))
theorem R64881 : Reach 64881 := rs (se 2 (by rfl) ⟨24330, by rfl⟩) (B 48661 (by norm_num) ⟨24330, by rfl⟩ (by norm_num))
theorem R64885 : Reach 64885 := rs (se 5 (by rfl) ⟨3041, by rfl⟩) (B 6083 (by norm_num) ⟨3041, by rfl⟩ (by norm_num))
theorem R64889 : Reach 64889 := rs (se 2 (by rfl) ⟨24333, by rfl⟩) (B 48667 (by norm_num) ⟨24333, by rfl⟩ (by norm_num))
theorem R64893 : Reach 64893 := rs (se 3 (by rfl) ⟨12167, by rfl⟩) (B 24335 (by norm_num) ⟨12167, by rfl⟩ (by norm_num))
theorem R97661 : Reach 97661 := rs (se 3 (by rfl) ⟨18311, by rfl⟩) (B 36623 (by norm_num) ⟨18311, by rfl⟩ (by norm_num))
theorem R64897 : Reach 64897 := rs (se 2 (by rfl) ⟨24336, by rfl⟩) (B 48673 (by norm_num) ⟨24336, by rfl⟩ (by norm_num))
theorem R163205 : Reach 163205 := rs (se 4 (by rfl) ⟨15300, by rfl⟩) (B 30601 (by norm_num) ⟨15300, by rfl⟩ (by norm_num))
theorem R64901 : Reach 64901 := rs (se 4 (by rfl) ⟨6084, by rfl⟩) (B 12169 (by norm_num) ⟨6084, by rfl⟩ (by norm_num))
theorem R64905 : Reach 64905 := rs (se 2 (by rfl) ⟨24339, by rfl⟩) (B 48679 (by norm_num) ⟨24339, by rfl⟩ (by norm_num))
theorem R64909 : Reach 64909 := rs (se 3 (by rfl) ⟨12170, by rfl⟩) (B 24341 (by norm_num) ⟨12170, by rfl⟩ (by norm_num))
theorem R64913 : Reach 64913 := rs (se 2 (by rfl) ⟨24342, by rfl⟩) (B 48685 (by norm_num) ⟨24342, by rfl⟩ (by norm_num))
theorem R64917 : Reach 64917 := rs (se 6 (by rfl) ⟨1521, by rfl⟩) (B 3043 (by norm_num) ⟨1521, by rfl⟩ (by norm_num))
theorem R97685 : Reach 97685 := rs (se 6 (by rfl) ⟨2289, by rfl⟩) (B 4579 (by norm_num) ⟨2289, by rfl⟩ (by norm_num))
theorem R64921 : Reach 64921 := rs (se 2 (by rfl) ⟨24345, by rfl⟩) (B 48691 (by norm_num) ⟨24345, by rfl⟩ (by norm_num))
theorem R64925 : Reach 64925 := rs (se 3 (by rfl) ⟨12173, by rfl⟩) (B 24347 (by norm_num) ⟨12173, by rfl⟩ (by norm_num))
theorem R64929 : Reach 64929 := rs (se 2 (by rfl) ⟨24348, by rfl⟩) (B 48697 (by norm_num) ⟨24348, by rfl⟩ (by norm_num))
theorem R327077 : Reach 327077 := rs (se 4 (by rfl) ⟨30663, by rfl⟩) (B 61327 (by norm_num) ⟨30663, by rfl⟩ (by norm_num))
theorem R64933 : Reach 64933 := rs (se 4 (by rfl) ⟨6087, by rfl⟩) (B 12175 (by norm_num) ⟨6087, by rfl⟩ (by norm_num))
theorem R64937 : Reach 64937 := rs (se 2 (by rfl) ⟨24351, by rfl⟩) (B 48703 (by norm_num) ⟨24351, by rfl⟩ (by norm_num))
theorem R64941 : Reach 64941 := rs (se 3 (by rfl) ⟨12176, by rfl⟩) (B 24353 (by norm_num) ⟨12176, by rfl⟩ (by norm_num))
theorem R97709 : Reach 97709 := rs (se 3 (by rfl) ⟨18320, by rfl⟩) (B 36641 (by norm_num) ⟨18320, by rfl⟩ (by norm_num))
theorem R64945 : Reach 64945 := rs (se 2 (by rfl) ⟨24354, by rfl⟩) (B 48709 (by norm_num) ⟨24354, by rfl⟩ (by norm_num))
theorem R64949 : Reach 64949 := rs (se 5 (by rfl) ⟨3044, by rfl⟩) (B 6089 (by norm_num) ⟨3044, by rfl⟩ (by norm_num))
theorem R64953 : Reach 64953 := rs (se 2 (by rfl) ⟨24357, by rfl⟩) (B 48715 (by norm_num) ⟨24357, by rfl⟩ (by norm_num))
theorem R64957 : Reach 64957 := rs (se 3 (by rfl) ⟨12179, by rfl⟩) (B 24359 (by norm_num) ⟨12179, by rfl⟩ (by norm_num))
theorem R64961 : Reach 64961 := rs (se 2 (by rfl) ⟨24360, by rfl⟩) (B 48721 (by norm_num) ⟨24360, by rfl⟩ (by norm_num))
theorem R64965 : Reach 64965 := rs (se 4 (by rfl) ⟨6090, by rfl⟩) (B 12181 (by norm_num) ⟨6090, by rfl⟩ (by norm_num))
theorem R97733 : Reach 97733 := rs (se 4 (by rfl) ⟨9162, by rfl⟩) (B 18325 (by norm_num) ⟨9162, by rfl⟩ (by norm_num))
theorem R64969 : Reach 64969 := rs (se 2 (by rfl) ⟨24363, by rfl⟩) (B 48727 (by norm_num) ⟨24363, by rfl⟩ (by norm_num))
theorem R64973 : Reach 64973 := rs (se 3 (by rfl) ⟨12182, by rfl⟩) (B 24365 (by norm_num) ⟨12182, by rfl⟩ (by norm_num))
theorem R64977 : Reach 64977 := rs (se 2 (by rfl) ⟨24366, by rfl⟩) (B 48733 (by norm_num) ⟨24366, by rfl⟩ (by norm_num))
theorem R261589 : Reach 261589 := rs (se 7 (by rfl) ⟨3065, by rfl⟩) (B 6131 (by norm_num) ⟨3065, by rfl⟩ (by norm_num))
theorem R64981 : Reach 64981 := rs (se 7 (by rfl) ⟨761, by rfl⟩) (B 1523 (by norm_num) ⟨761, by rfl⟩ (by norm_num))
theorem R64985 : Reach 64985 := rs (se 2 (by rfl) ⟨24369, by rfl⟩) (B 48739 (by norm_num) ⟨24369, by rfl⟩ (by norm_num))
theorem R64989 : Reach 64989 := rs (se 3 (by rfl) ⟨12185, by rfl⟩) (B 24371 (by norm_num) ⟨12185, by rfl⟩ (by norm_num))
theorem R97757 : Reach 97757 := rs (se 3 (by rfl) ⟨18329, by rfl⟩) (B 36659 (by norm_num) ⟨18329, by rfl⟩ (by norm_num))
theorem R64993 : Reach 64993 := rs (se 2 (by rfl) ⟨24372, by rfl⟩) (B 48745 (by norm_num) ⟨24372, by rfl⟩ (by norm_num))
theorem R64997 : Reach 64997 := rs (se 4 (by rfl) ⟨6093, by rfl⟩) (B 12187 (by norm_num) ⟨6093, by rfl⟩ (by norm_num))
theorem R65001 : Reach 65001 := rs (se 2 (by rfl) ⟨24375, by rfl⟩) (B 48751 (by norm_num) ⟨24375, by rfl⟩ (by norm_num))
theorem R65005 : Reach 65005 := rs (se 3 (by rfl) ⟨12188, by rfl⟩) (B 24377 (by norm_num) ⟨12188, by rfl⟩ (by norm_num))
theorem R65009 : Reach 65009 := rs (se 2 (by rfl) ⟨24378, by rfl⟩) (B 48757 (by norm_num) ⟨24378, by rfl⟩ (by norm_num))
theorem R65013 : Reach 65013 := rs (se 5 (by rfl) ⟨3047, by rfl⟩) (B 6095 (by norm_num) ⟨3047, by rfl⟩ (by norm_num))
theorem R97781 : Reach 97781 := rs (se 5 (by rfl) ⟨4583, by rfl⟩) (B 9167 (by norm_num) ⟨4583, by rfl⟩ (by norm_num))
theorem R65017 : Reach 65017 := rs (se 2 (by rfl) ⟨24381, by rfl⟩) (B 48763 (by norm_num) ⟨24381, by rfl⟩ (by norm_num))
theorem R65021 : Reach 65021 := rs (se 3 (by rfl) ⟨12191, by rfl⟩) (B 24383 (by norm_num) ⟨12191, by rfl⟩ (by norm_num))
theorem R65025 : Reach 65025 := rs (se 2 (by rfl) ⟨24384, by rfl⟩) (B 48769 (by norm_num) ⟨24384, by rfl⟩ (by norm_num))
theorem R65029 : Reach 65029 := rs (se 4 (by rfl) ⟨6096, by rfl⟩) (B 12193 (by norm_num) ⟨6096, by rfl⟩ (by norm_num))
theorem R65033 : Reach 65033 := rs (se 2 (by rfl) ⟨24387, by rfl⟩) (B 48775 (by norm_num) ⟨24387, by rfl⟩ (by norm_num))
theorem R65037 : Reach 65037 := rs (se 3 (by rfl) ⟨12194, by rfl⟩) (B 24389 (by norm_num) ⟨12194, by rfl⟩ (by norm_num))
theorem R97805 : Reach 97805 := rs (se 3 (by rfl) ⟨18338, by rfl⟩) (B 36677 (by norm_num) ⟨18338, by rfl⟩ (by norm_num))
theorem R65041 : Reach 65041 := rs (se 2 (by rfl) ⟨24390, by rfl⟩) (B 48781 (by norm_num) ⟨24390, by rfl⟩ (by norm_num))
theorem R65045 : Reach 65045 := rs (se 6 (by rfl) ⟨1524, by rfl⟩) (B 3049 (by norm_num) ⟨1524, by rfl⟩ (by norm_num))
theorem R65049 : Reach 65049 := rs (se 2 (by rfl) ⟨24393, by rfl⟩) (B 48787 (by norm_num) ⟨24393, by rfl⟩ (by norm_num))
theorem R65053 : Reach 65053 := rs (se 3 (by rfl) ⟨12197, by rfl⟩) (B 24395 (by norm_num) ⟨12197, by rfl⟩ (by norm_num))
theorem R65057 : Reach 65057 := rs (se 2 (by rfl) ⟨24396, by rfl⟩) (B 48793 (by norm_num) ⟨24396, by rfl⟩ (by norm_num))
theorem R65061 : Reach 65061 := rs (se 4 (by rfl) ⟨6099, by rfl⟩) (B 12199 (by norm_num) ⟨6099, by rfl⟩ (by norm_num))
theorem R97829 : Reach 97829 := rs (se 4 (by rfl) ⟨9171, by rfl⟩) (B 18343 (by norm_num) ⟨9171, by rfl⟩ (by norm_num))
theorem R65065 : Reach 65065 := rs (se 2 (by rfl) ⟨24399, by rfl⟩) (B 48799 (by norm_num) ⟨24399, by rfl⟩ (by norm_num))
theorem R65069 : Reach 65069 := rs (se 3 (by rfl) ⟨12200, by rfl⟩) (B 24401 (by norm_num) ⟨12200, by rfl⟩ (by norm_num))
theorem R65073 : Reach 65073 := rs (se 2 (by rfl) ⟨24402, by rfl⟩) (B 48805 (by norm_num) ⟨24402, by rfl⟩ (by norm_num))
theorem R65077 : Reach 65077 := rs (se 5 (by rfl) ⟨3050, by rfl⟩) (B 6101 (by norm_num) ⟨3050, by rfl⟩ (by norm_num))
theorem R65081 : Reach 65081 := rs (se 2 (by rfl) ⟨24405, by rfl⟩) (B 48811 (by norm_num) ⟨24405, by rfl⟩ (by norm_num))
theorem R65085 : Reach 65085 := rs (se 3 (by rfl) ⟨12203, by rfl⟩) (B 24407 (by norm_num) ⟨12203, by rfl⟩ (by norm_num))
theorem R97853 : Reach 97853 := rs (se 3 (by rfl) ⟨18347, by rfl⟩) (B 36695 (by norm_num) ⟨18347, by rfl⟩ (by norm_num))
theorem R65089 : Reach 65089 := rs (se 2 (by rfl) ⟨24408, by rfl⟩) (B 48817 (by norm_num) ⟨24408, by rfl⟩ (by norm_num))
theorem R261701 : Reach 261701 := rs (se 4 (by rfl) ⟨24534, by rfl⟩) (B 49069 (by norm_num) ⟨24534, by rfl⟩ (by norm_num))
theorem R163397 : Reach 163397 := rs (se 4 (by rfl) ⟨15318, by rfl⟩) (B 30637 (by norm_num) ⟨15318, by rfl⟩ (by norm_num))
theorem R65093 : Reach 65093 := rs (se 4 (by rfl) ⟨6102, by rfl⟩) (B 12205 (by norm_num) ⟨6102, by rfl⟩ (by norm_num))
theorem R65097 : Reach 65097 := rs (se 2 (by rfl) ⟨24411, by rfl⟩) (B 48823 (by norm_num) ⟨24411, by rfl⟩ (by norm_num))
theorem R65101 : Reach 65101 := rs (se 3 (by rfl) ⟨12206, by rfl⟩) (B 24413 (by norm_num) ⟨12206, by rfl⟩ (by norm_num))
theorem R65105 : Reach 65105 := rs (se 2 (by rfl) ⟨24414, by rfl⟩) (B 48829 (by norm_num) ⟨24414, by rfl⟩ (by norm_num))
theorem R65109 : Reach 65109 := rs (se 8 (by rfl) ⟨381, by rfl⟩) (B 763 (by norm_num) ⟨381, by rfl⟩ (by norm_num))
theorem R97877 : Reach 97877 := rs (se 8 (by rfl) ⟨573, by rfl⟩) (B 1147 (by norm_num) ⟨573, by rfl⟩ (by norm_num))
theorem R65113 : Reach 65113 := rs (se 2 (by rfl) ⟨24417, by rfl⟩) (B 48835 (by norm_num) ⟨24417, by rfl⟩ (by norm_num))
theorem R65117 : Reach 65117 := rs (se 3 (by rfl) ⟨12209, by rfl⟩) (B 24419 (by norm_num) ⟨12209, by rfl⟩ (by norm_num))
theorem R65121 : Reach 65121 := rs (se 2 (by rfl) ⟨24420, by rfl⟩) (B 48841 (by norm_num) ⟨24420, by rfl⟩ (by norm_num))
theorem R65125 : Reach 65125 := rs (se 4 (by rfl) ⟨6105, by rfl⟩) (B 12211 (by norm_num) ⟨6105, by rfl⟩ (by norm_num))
theorem R65129 : Reach 65129 := rs (se 2 (by rfl) ⟨24423, by rfl⟩) (B 48847 (by norm_num) ⟨24423, by rfl⟩ (by norm_num))
theorem R65133 : Reach 65133 := rs (se 3 (by rfl) ⟨12212, by rfl⟩) (B 24425 (by norm_num) ⟨12212, by rfl⟩ (by norm_num))
theorem R97901 : Reach 97901 := rs (se 3 (by rfl) ⟨18356, by rfl⟩) (B 36713 (by norm_num) ⟨18356, by rfl⟩ (by norm_num))
theorem R65137 : Reach 65137 := rs (se 2 (by rfl) ⟨24426, by rfl⟩) (B 48853 (by norm_num) ⟨24426, by rfl⟩ (by norm_num))
theorem R65141 : Reach 65141 := rs (se 5 (by rfl) ⟨3053, by rfl⟩) (B 6107 (by norm_num) ⟨3053, by rfl⟩ (by norm_num))
theorem R65145 : Reach 65145 := rs (se 2 (by rfl) ⟨24429, by rfl⟩) (B 48859 (by norm_num) ⟨24429, by rfl⟩ (by norm_num))
theorem R65149 : Reach 65149 := rs (se 3 (by rfl) ⟨12215, by rfl⟩) (B 24431 (by norm_num) ⟨12215, by rfl⟩ (by norm_num))
theorem R65153 : Reach 65153 := rs (se 2 (by rfl) ⟨24432, by rfl⟩) (B 48865 (by norm_num) ⟨24432, by rfl⟩ (by norm_num))
theorem R65157 : Reach 65157 := rs (se 4 (by rfl) ⟨6108, by rfl⟩) (B 12217 (by norm_num) ⟨6108, by rfl⟩ (by norm_num))
theorem R97925 : Reach 97925 := rs (se 4 (by rfl) ⟨9180, by rfl⟩) (B 18361 (by norm_num) ⟨9180, by rfl⟩ (by norm_num))
theorem R65161 : Reach 65161 := rs (se 2 (by rfl) ⟨24435, by rfl⟩) (B 48871 (by norm_num) ⟨24435, by rfl⟩ (by norm_num))
theorem R65165 : Reach 65165 := rs (se 3 (by rfl) ⟨12218, by rfl⟩) (B 24437 (by norm_num) ⟨12218, by rfl⟩ (by norm_num))
theorem R65169 : Reach 65169 := rs (se 2 (by rfl) ⟨24438, by rfl⟩) (B 48877 (by norm_num) ⟨24438, by rfl⟩ (by norm_num))
theorem R65173 : Reach 65173 := rs (se 6 (by rfl) ⟨1527, by rfl⟩) (B 3055 (by norm_num) ⟨1527, by rfl⟩ (by norm_num))
theorem R65177 : Reach 65177 := rs (se 2 (by rfl) ⟨24441, by rfl⟩) (B 48883 (by norm_num) ⟨24441, by rfl⟩ (by norm_num))
theorem R65181 : Reach 65181 := rs (se 3 (by rfl) ⟨12221, by rfl⟩) (B 24443 (by norm_num) ⟨12221, by rfl⟩ (by norm_num))
theorem R97949 : Reach 97949 := rs (se 3 (by rfl) ⟨18365, by rfl⟩) (B 36731 (by norm_num) ⟨18365, by rfl⟩ (by norm_num))
theorem R65185 : Reach 65185 := rs (se 2 (by rfl) ⟨24444, by rfl⟩) (B 48889 (by norm_num) ⟨24444, by rfl⟩ (by norm_num))
theorem R65189 : Reach 65189 := rs (se 4 (by rfl) ⟨6111, by rfl⟩) (B 12223 (by norm_num) ⟨6111, by rfl⟩ (by norm_num))
theorem R65193 : Reach 65193 := rs (se 2 (by rfl) ⟨24447, by rfl⟩) (B 48895 (by norm_num) ⟨24447, by rfl⟩ (by norm_num))
theorem R65197 : Reach 65197 := rs (se 3 (by rfl) ⟨12224, by rfl⟩) (B 24449 (by norm_num) ⟨12224, by rfl⟩ (by norm_num))
theorem R65201 : Reach 65201 := rs (se 2 (by rfl) ⟨24450, by rfl⟩) (B 48901 (by norm_num) ⟨24450, by rfl⟩ (by norm_num))
theorem R65205 : Reach 65205 := rs (se 5 (by rfl) ⟨3056, by rfl⟩) (B 6113 (by norm_num) ⟨3056, by rfl⟩ (by norm_num))
theorem R97973 : Reach 97973 := rs (se 5 (by rfl) ⟨4592, by rfl⟩) (B 9185 (by norm_num) ⟨4592, by rfl⟩ (by norm_num))
theorem R65209 : Reach 65209 := rs (se 2 (by rfl) ⟨24453, by rfl⟩) (B 48907 (by norm_num) ⟨24453, by rfl⟩ (by norm_num))
theorem R65213 : Reach 65213 := rs (se 3 (by rfl) ⟨12227, by rfl⟩) (B 24455 (by norm_num) ⟨12227, by rfl⟩ (by norm_num))
theorem R65217 : Reach 65217 := rs (se 2 (by rfl) ⟨24456, by rfl⟩) (B 48913 (by norm_num) ⟨24456, by rfl⟩ (by norm_num))
theorem R65221 : Reach 65221 := rs (se 4 (by rfl) ⟨6114, by rfl⟩) (B 12229 (by norm_num) ⟨6114, by rfl⟩ (by norm_num))
theorem R65225 : Reach 65225 := rs (se 2 (by rfl) ⟨24459, by rfl⟩) (B 48919 (by norm_num) ⟨24459, by rfl⟩ (by norm_num))
theorem R65229 : Reach 65229 := rs (se 3 (by rfl) ⟨12230, by rfl⟩) (B 24461 (by norm_num) ⟨12230, by rfl⟩ (by norm_num))
theorem R97997 : Reach 97997 := rs (se 3 (by rfl) ⟨18374, by rfl⟩) (B 36749 (by norm_num) ⟨18374, by rfl⟩ (by norm_num))
theorem R65233 : Reach 65233 := rs (se 2 (by rfl) ⟨24462, by rfl⟩) (B 48925 (by norm_num) ⟨24462, by rfl⟩ (by norm_num))
theorem R491221 : Reach 491221 := rs (se 7 (by rfl) ⟨5756, by rfl⟩) (B 11513 (by norm_num) ⟨5756, by rfl⟩ (by norm_num))
theorem R65237 : Reach 65237 := rs (se 7 (by rfl) ⟨764, by rfl⟩) (B 1529 (by norm_num) ⟨764, by rfl⟩ (by norm_num))
theorem R65241 : Reach 65241 := rs (se 2 (by rfl) ⟨24465, by rfl⟩) (B 48931 (by norm_num) ⟨24465, by rfl⟩ (by norm_num))
theorem R65245 : Reach 65245 := rs (se 3 (by rfl) ⟨12233, by rfl⟩) (B 24467 (by norm_num) ⟨12233, by rfl⟩ (by norm_num))
theorem R65249 : Reach 65249 := rs (se 2 (by rfl) ⟨24468, by rfl⟩) (B 48937 (by norm_num) ⟨24468, by rfl⟩ (by norm_num))
theorem R65253 : Reach 65253 := rs (se 4 (by rfl) ⟨6117, by rfl⟩) (B 12235 (by norm_num) ⟨6117, by rfl⟩ (by norm_num))
theorem R98021 : Reach 98021 := rs (se 4 (by rfl) ⟨9189, by rfl⟩) (B 18379 (by norm_num) ⟨9189, by rfl⟩ (by norm_num))
theorem R65257 : Reach 65257 := rs (se 2 (by rfl) ⟨24471, by rfl⟩) (B 48943 (by norm_num) ⟨24471, by rfl⟩ (by norm_num))
theorem R65261 : Reach 65261 := rs (se 3 (by rfl) ⟨12236, by rfl⟩) (B 24473 (by norm_num) ⟨12236, by rfl⟩ (by norm_num))
theorem R65265 : Reach 65265 := rs (se 2 (by rfl) ⟨24474, by rfl⟩) (B 48949 (by norm_num) ⟨24474, by rfl⟩ (by norm_num))
theorem R65269 : Reach 65269 := rs (se 5 (by rfl) ⟨3059, by rfl⟩) (B 6119 (by norm_num) ⟨3059, by rfl⟩ (by norm_num))
theorem R65273 : Reach 65273 := rs (se 2 (by rfl) ⟨24477, by rfl⟩) (B 48955 (by norm_num) ⟨24477, by rfl⟩ (by norm_num))
theorem R65277 : Reach 65277 := rs (se 3 (by rfl) ⟨12239, by rfl⟩) (B 24479 (by norm_num) ⟨12239, by rfl⟩ (by norm_num))
theorem R98045 : Reach 98045 := rs (se 3 (by rfl) ⟨18383, by rfl⟩) (B 36767 (by norm_num) ⟨18383, by rfl⟩ (by norm_num))
theorem R65281 : Reach 65281 := rs (se 2 (by rfl) ⟨24480, by rfl⟩) (B 48961 (by norm_num) ⟨24480, by rfl⟩ (by norm_num))
theorem R65285 : Reach 65285 := rs (se 4 (by rfl) ⟨6120, by rfl⟩) (B 12241 (by norm_num) ⟨6120, by rfl⟩ (by norm_num))
theorem R65289 : Reach 65289 := rs (se 2 (by rfl) ⟨24483, by rfl⟩) (B 48967 (by norm_num) ⟨24483, by rfl⟩ (by norm_num))
theorem R65293 : Reach 65293 := rs (se 3 (by rfl) ⟨12242, by rfl⟩) (B 24485 (by norm_num) ⟨12242, by rfl⟩ (by norm_num))
theorem R65297 : Reach 65297 := rs (se 2 (by rfl) ⟨24486, by rfl⟩) (B 48973 (by norm_num) ⟨24486, by rfl⟩ (by norm_num))
theorem R65301 : Reach 65301 := rs (se 6 (by rfl) ⟨1530, by rfl⟩) (B 3061 (by norm_num) ⟨1530, by rfl⟩ (by norm_num))
theorem R98069 : Reach 98069 := rs (se 6 (by rfl) ⟨2298, by rfl⟩) (B 4597 (by norm_num) ⟨2298, by rfl⟩ (by norm_num))
theorem R65305 : Reach 65305 := rs (se 2 (by rfl) ⟨24489, by rfl⟩) (B 48979 (by norm_num) ⟨24489, by rfl⟩ (by norm_num))
theorem R65309 : Reach 65309 := rs (se 3 (by rfl) ⟨12245, by rfl⟩) (B 24491 (by norm_num) ⟨12245, by rfl⟩ (by norm_num))
theorem R65313 : Reach 65313 := rs (se 2 (by rfl) ⟨24492, by rfl⟩) (B 48985 (by norm_num) ⟨24492, by rfl⟩ (by norm_num))
theorem R65317 : Reach 65317 := rs (se 4 (by rfl) ⟨6123, by rfl⟩) (B 12247 (by norm_num) ⟨6123, by rfl⟩ (by norm_num))
theorem R65321 : Reach 65321 := rs (se 2 (by rfl) ⟨24495, by rfl⟩) (B 48991 (by norm_num) ⟨24495, by rfl⟩ (by norm_num))
theorem R65325 : Reach 65325 := rs (se 3 (by rfl) ⟨12248, by rfl⟩) (B 24497 (by norm_num) ⟨12248, by rfl⟩ (by norm_num))
theorem R98093 : Reach 98093 := rs (se 3 (by rfl) ⟨18392, by rfl⟩) (B 36785 (by norm_num) ⟨18392, by rfl⟩ (by norm_num))
theorem R65329 : Reach 65329 := rs (se 2 (by rfl) ⟨24498, by rfl⟩) (B 48997 (by norm_num) ⟨24498, by rfl⟩ (by norm_num))
theorem R65333 : Reach 65333 := rs (se 5 (by rfl) ⟨3062, by rfl⟩) (B 6125 (by norm_num) ⟨3062, by rfl⟩ (by norm_num))
theorem R65337 : Reach 65337 := rs (se 2 (by rfl) ⟨24501, by rfl⟩) (B 49003 (by norm_num) ⟨24501, by rfl⟩ (by norm_num))
theorem R65341 : Reach 65341 := rs (se 3 (by rfl) ⟨12251, by rfl⟩) (B 24503 (by norm_num) ⟨12251, by rfl⟩ (by norm_num))
theorem R65345 : Reach 65345 := rs (se 2 (by rfl) ⟨24504, by rfl⟩) (B 49009 (by norm_num) ⟨24504, by rfl⟩ (by norm_num))
theorem R65349 : Reach 65349 := rs (se 4 (by rfl) ⟨6126, by rfl⟩) (B 12253 (by norm_num) ⟨6126, by rfl⟩ (by norm_num))
theorem R98117 : Reach 98117 := rs (se 4 (by rfl) ⟨9198, by rfl⟩) (B 18397 (by norm_num) ⟨9198, by rfl⟩ (by norm_num))
theorem R65353 : Reach 65353 := rs (se 2 (by rfl) ⟨24507, by rfl⟩) (B 49015 (by norm_num) ⟨24507, by rfl⟩ (by norm_num))
theorem R65357 : Reach 65357 := rs (se 3 (by rfl) ⟨12254, by rfl⟩) (B 24509 (by norm_num) ⟨12254, by rfl⟩ (by norm_num))
theorem R65361 : Reach 65361 := rs (se 2 (by rfl) ⟨24510, by rfl⟩) (B 49021 (by norm_num) ⟨24510, by rfl⟩ (by norm_num))
theorem R3211093 : Reach 3211093 := rs (se 9 (by rfl) ⟨9407, by rfl⟩) (B 18815 (by norm_num) ⟨9407, by rfl⟩ (by norm_num))
theorem R65365 : Reach 65365 := rs (se 9 (by rfl) ⟨191, by rfl⟩) (B 383 (by norm_num) ⟨191, by rfl⟩ (by norm_num))
theorem R65369 : Reach 65369 := rs (se 2 (by rfl) ⟨24513, by rfl⟩) (B 49027 (by norm_num) ⟨24513, by rfl⟩ (by norm_num))
theorem R65373 : Reach 65373 := rs (se 3 (by rfl) ⟨12257, by rfl⟩) (B 24515 (by norm_num) ⟨12257, by rfl⟩ (by norm_num))
theorem R98141 : Reach 98141 := rs (se 3 (by rfl) ⟨18401, by rfl⟩) (B 36803 (by norm_num) ⟨18401, by rfl⟩ (by norm_num))
theorem R65377 : Reach 65377 := rs (se 2 (by rfl) ⟨24516, by rfl⟩) (B 49033 (by norm_num) ⟨24516, by rfl⟩ (by norm_num))
theorem R65381 : Reach 65381 := rs (se 4 (by rfl) ⟨6129, by rfl⟩) (B 12259 (by norm_num) ⟨6129, by rfl⟩ (by norm_num))
theorem R65385 : Reach 65385 := rs (se 2 (by rfl) ⟨24519, by rfl⟩) (B 49039 (by norm_num) ⟨24519, by rfl⟩ (by norm_num))
theorem R65389 : Reach 65389 := rs (se 3 (by rfl) ⟨12260, by rfl⟩) (B 24521 (by norm_num) ⟨12260, by rfl⟩ (by norm_num))
theorem R65393 : Reach 65393 := rs (se 2 (by rfl) ⟨24522, by rfl⟩) (B 49045 (by norm_num) ⟨24522, by rfl⟩ (by norm_num))
theorem R65397 : Reach 65397 := rs (se 5 (by rfl) ⟨3065, by rfl⟩) (B 6131 (by norm_num) ⟨3065, by rfl⟩ (by norm_num))
theorem R98165 : Reach 98165 := rs (se 5 (by rfl) ⟨4601, by rfl⟩) (B 9203 (by norm_num) ⟨4601, by rfl⟩ (by norm_num))
theorem R65401 : Reach 65401 := rs (se 2 (by rfl) ⟨24525, by rfl⟩) (B 49051 (by norm_num) ⟨24525, by rfl⟩ (by norm_num))
theorem R65405 : Reach 65405 := rs (se 3 (by rfl) ⟨12263, by rfl⟩) (B 24527 (by norm_num) ⟨12263, by rfl⟩ (by norm_num))
theorem R65409 : Reach 65409 := rs (se 2 (by rfl) ⟨24528, by rfl⟩) (B 49057 (by norm_num) ⟨24528, by rfl⟩ (by norm_num))
theorem R65413 : Reach 65413 := rs (se 4 (by rfl) ⟨6132, by rfl⟩) (B 12265 (by norm_num) ⟨6132, by rfl⟩ (by norm_num))
theorem R98189 : Reach 98189 := rs (se 3 (by rfl) ⟨18410, by rfl⟩) (B 36821 (by norm_num) ⟨18410, by rfl⟩ (by norm_num))
theorem R65417 : Reach 65417 := rs (se 2 (by rfl) ⟨24531, by rfl⟩) (B 49063 (by norm_num) ⟨24531, by rfl⟩ (by norm_num))
theorem R65421 : Reach 65421 := rs (se 3 (by rfl) ⟨12266, by rfl⟩) (B 24533 (by norm_num) ⟨12266, by rfl⟩ (by norm_num))
theorem R65425 : Reach 65425 := rs (se 2 (by rfl) ⟨24534, by rfl⟩) (B 49069 (by norm_num) ⟨24534, by rfl⟩ (by norm_num))
theorem R65429 : Reach 65429 := rs (se 6 (by rfl) ⟨1533, by rfl⟩) (B 3067 (by norm_num) ⟨1533, by rfl⟩ (by norm_num))
theorem R556949 : Reach 556949 := rs (se 6 (by rfl) ⟨13053, by rfl⟩) (B 26107 (by norm_num) ⟨13053, by rfl⟩ (by norm_num))
theorem R65433 : Reach 65433 := rs (se 2 (by rfl) ⟨24537, by rfl⟩) (B 49075 (by norm_num) ⟨24537, by rfl⟩ (by norm_num))
theorem R163741 : Reach 163741 := rs (se 3 (by rfl) ⟨30701, by rfl⟩) (B 61403 (by norm_num) ⟨30701, by rfl⟩ (by norm_num))
theorem R65437 : Reach 65437 := rs (se 3 (by rfl) ⟨12269, by rfl⟩) (B 24539 (by norm_num) ⟨12269, by rfl⟩ (by norm_num))
theorem R65441 : Reach 65441 := rs (se 2 (by rfl) ⟨24540, by rfl⟩) (B 49081 (by norm_num) ⟨24540, by rfl⟩ (by norm_num))
theorem R98213 : Reach 98213 := rs (se 4 (by rfl) ⟨9207, by rfl⟩) (B 18415 (by norm_num) ⟨9207, by rfl⟩ (by norm_num))
theorem R65445 : Reach 65445 := rs (se 4 (by rfl) ⟨6135, by rfl⟩) (B 12271 (by norm_num) ⟨6135, by rfl⟩ (by norm_num))
theorem R65449 : Reach 65449 := rs (se 2 (by rfl) ⟨24543, by rfl⟩) (B 49087 (by norm_num) ⟨24543, by rfl⟩ (by norm_num))
theorem R65453 : Reach 65453 := rs (se 3 (by rfl) ⟨12272, by rfl⟩) (B 24545 (by norm_num) ⟨12272, by rfl⟩ (by norm_num))
theorem R65457 : Reach 65457 := rs (se 2 (by rfl) ⟨24546, by rfl⟩) (B 49093 (by norm_num) ⟨24546, by rfl⟩ (by norm_num))
theorem R65461 : Reach 65461 := rs (se 5 (by rfl) ⟨3068, by rfl⟩) (B 6137 (by norm_num) ⟨3068, by rfl⟩ (by norm_num))
theorem R65465 : Reach 65465 := rs (se 2 (by rfl) ⟨24549, by rfl⟩) (B 49099 (by norm_num) ⟨24549, by rfl⟩ (by norm_num))
theorem R65469 : Reach 65469 := rs (se 3 (by rfl) ⟨12275, by rfl⟩) (B 24551 (by norm_num) ⟨12275, by rfl⟩ (by norm_num))
theorem R98237 : Reach 98237 := rs (se 3 (by rfl) ⟨18419, by rfl⟩) (B 36839 (by norm_num) ⟨18419, by rfl⟩ (by norm_num))
theorem R65473 : Reach 65473 := rs (se 2 (by rfl) ⟨24552, by rfl⟩) (B 49105 (by norm_num) ⟨24552, by rfl⟩ (by norm_num))
theorem R65477 : Reach 65477 := rs (se 4 (by rfl) ⟨6138, by rfl⟩) (B 12277 (by norm_num) ⟨6138, by rfl⟩ (by norm_num))
theorem R65481 : Reach 65481 := rs (se 2 (by rfl) ⟨24555, by rfl⟩) (B 49111 (by norm_num) ⟨24555, by rfl⟩ (by norm_num))
theorem R65485 : Reach 65485 := rs (se 3 (by rfl) ⟨12278, by rfl⟩) (B 24557 (by norm_num) ⟨12278, by rfl⟩ (by norm_num))
theorem R65489 : Reach 65489 := rs (se 2 (by rfl) ⟨24558, by rfl⟩) (B 49117 (by norm_num) ⟨24558, by rfl⟩ (by norm_num))
theorem R65493 : Reach 65493 := rs (se 7 (by rfl) ⟨767, by rfl⟩) (B 1535 (by norm_num) ⟨767, by rfl⟩ (by norm_num))
theorem R98261 : Reach 98261 := rs (se 7 (by rfl) ⟨1151, by rfl⟩) (B 2303 (by norm_num) ⟨1151, by rfl⟩ (by norm_num))
theorem R65497 : Reach 65497 := rs (se 2 (by rfl) ⟨24561, by rfl⟩) (B 49123 (by norm_num) ⟨24561, by rfl⟩ (by norm_num))
theorem R65501 : Reach 65501 := rs (se 3 (by rfl) ⟨12281, by rfl⟩) (B 24563 (by norm_num) ⟨12281, by rfl⟩ (by norm_num))
theorem R65505 : Reach 65505 := rs (se 2 (by rfl) ⟨24564, by rfl⟩) (B 49129 (by norm_num) ⟨24564, by rfl⟩ (by norm_num))
theorem R65509 : Reach 65509 := rs (se 4 (by rfl) ⟨6141, by rfl⟩) (B 12283 (by norm_num) ⟨6141, by rfl⟩ (by norm_num))
theorem R65513 : Reach 65513 := rs (se 2 (by rfl) ⟨24567, by rfl⟩) (B 49135 (by norm_num) ⟨24567, by rfl⟩ (by norm_num))
theorem R65517 : Reach 65517 := rs (se 3 (by rfl) ⟨12284, by rfl⟩) (B 24569 (by norm_num) ⟨12284, by rfl⟩ (by norm_num))
theorem R98285 : Reach 98285 := rs (se 3 (by rfl) ⟨18428, by rfl⟩) (B 36857 (by norm_num) ⟨18428, by rfl⟩ (by norm_num))
theorem R65521 : Reach 65521 := rs (se 2 (by rfl) ⟨24570, by rfl⟩) (B 49141 (by norm_num) ⟨24570, by rfl⟩ (by norm_num))
theorem R65525 : Reach 65525 := rs (se 5 (by rfl) ⟨3071, by rfl⟩) (B 6143 (by norm_num) ⟨3071, by rfl⟩ (by norm_num))
theorem R65533 : Reach 65533 := rs (se 3 (by rfl) ⟨12287, by rfl⟩) (B 24575 (by norm_num) ⟨12287, by rfl⟩ (by norm_num))
theorem R65539 : Reach 65539 := rs (se 1 (by rfl) ⟨49154, by rfl⟩) R98309
theorem R98321 : Reach 98321 := rs (se 2 (by rfl) ⟨36870, by rfl⟩) R73741
theorem R65555 : Reach 65555 := rs (se 1 (by rfl) ⟨49166, by rfl⟩) R98333
theorem R98339 : Reach 98339 := rs (se 1 (by rfl) ⟨73754, by rfl⟩) R147509
theorem R65571 : Reach 65571 := rs (se 1 (by rfl) ⟨49178, by rfl⟩) R98357
theorem R65587 : Reach 65587 := rs (se 1 (by rfl) ⟨49190, by rfl⟩) R98381
theorem R98369 : Reach 98369 := rs (se 2 (by rfl) ⟨36888, by rfl⟩) R73777
theorem R65603 : Reach 65603 := rs (se 1 (by rfl) ⟨49202, by rfl⟩) R98405
theorem R98387 : Reach 98387 := rs (se 1 (by rfl) ⟨73790, by rfl⟩) R147581
theorem R65619 : Reach 65619 := rs (se 1 (by rfl) ⟨49214, by rfl⟩) R98429
theorem R65635 : Reach 65635 := rs (se 1 (by rfl) ⟨49226, by rfl⟩) R98453
theorem R98417 : Reach 98417 := rs (se 2 (by rfl) ⟨36906, by rfl⟩) R73813
theorem R65651 : Reach 65651 := rs (se 1 (by rfl) ⟨49238, by rfl⟩) R98477
theorem R98435 : Reach 98435 := rs (se 1 (by rfl) ⟨73826, by rfl⟩) R147653
theorem R65667 : Reach 65667 := rs (se 1 (by rfl) ⟨49250, by rfl⟩) R98501
theorem R65683 : Reach 65683 := rs (se 1 (by rfl) ⟨49262, by rfl⟩) R98525
theorem R98465 : Reach 98465 := rs (se 2 (by rfl) ⟨36924, by rfl⟩) R73849
theorem R65699 : Reach 65699 := rs (se 1 (by rfl) ⟨49274, by rfl⟩) R98549
theorem R98483 : Reach 98483 := rs (se 1 (by rfl) ⟨73862, by rfl⟩) R147725
theorem R65715 : Reach 65715 := rs (se 1 (by rfl) ⟨49286, by rfl⟩) R98573
theorem R65731 : Reach 65731 := rs (se 1 (by rfl) ⟨49298, by rfl⟩) R98597
theorem R262349 : Reach 262349 := rs (se 3 (by rfl) ⟨49190, by rfl⟩) R98381
theorem R98513 : Reach 98513 := rs (se 2 (by rfl) ⟨36942, by rfl⟩) R73885
theorem R65747 : Reach 65747 := rs (se 1 (by rfl) ⟨49310, by rfl⟩) R98621
theorem R98531 : Reach 98531 := rs (se 1 (by rfl) ⟨73898, by rfl⟩) R147797
theorem R65763 : Reach 65763 := rs (se 1 (by rfl) ⟨49322, by rfl⟩) R98645
theorem R65779 : Reach 65779 := rs (se 1 (by rfl) ⟨49334, by rfl⟩) R98669
theorem R98561 : Reach 98561 := rs (se 2 (by rfl) ⟨36960, by rfl⟩) R73921
theorem R65795 : Reach 65795 := rs (se 1 (by rfl) ⟨49346, by rfl⟩) R98693
theorem R98579 : Reach 98579 := rs (se 1 (by rfl) ⟨73934, by rfl⟩) R147869
theorem R65811 : Reach 65811 := rs (se 1 (by rfl) ⟨49358, by rfl⟩) R98717
theorem R65827 : Reach 65827 := rs (se 1 (by rfl) ⟨49370, by rfl⟩) R98741
theorem R98609 : Reach 98609 := rs (se 2 (by rfl) ⟨36978, by rfl⟩) R73957
theorem R65843 : Reach 65843 := rs (se 1 (by rfl) ⟨49382, by rfl⟩) R98765
theorem R98627 : Reach 98627 := rs (se 1 (by rfl) ⟨73970, by rfl⟩) R147941
theorem R65859 : Reach 65859 := rs (se 1 (by rfl) ⟨49394, by rfl⟩) R98789
theorem R164177 : Reach 164177 := rs (se 2 (by rfl) ⟨61566, by rfl⟩) R123133
theorem R65875 : Reach 65875 := rs (se 1 (by rfl) ⟨49406, by rfl⟩) R98813
theorem R98657 : Reach 98657 := rs (se 2 (by rfl) ⟨36996, by rfl⟩) R73993
theorem R65891 : Reach 65891 := rs (se 1 (by rfl) ⟨49418, by rfl⟩) R98837
theorem R328049 : Reach 328049 := rs (se 2 (by rfl) ⟨123018, by rfl⟩) R246037
theorem R98675 : Reach 98675 := rs (se 1 (by rfl) ⟨74006, by rfl⟩) R148013
theorem R65907 : Reach 65907 := rs (se 1 (by rfl) ⟨49430, by rfl⟩) R98861
theorem R164227 : Reach 164227 := rs (se 1 (by rfl) ⟨123170, by rfl⟩) R246341
theorem R65923 : Reach 65923 := rs (se 1 (by rfl) ⟨49442, by rfl⟩) R98885
theorem R98705 : Reach 98705 := rs (se 2 (by rfl) ⟨37014, by rfl⟩) R74029
theorem R65939 : Reach 65939 := rs (se 1 (by rfl) ⟨49454, by rfl⟩) R98909
theorem R98723 : Reach 98723 := rs (se 1 (by rfl) ⟨74042, by rfl⟩) R148085
theorem R65955 : Reach 65955 := rs (se 1 (by rfl) ⟨49466, by rfl⟩) R98933
theorem R65971 : Reach 65971 := rs (se 1 (by rfl) ⟨49478, by rfl⟩) R98957
theorem R98753 : Reach 98753 := rs (se 2 (by rfl) ⟨37032, by rfl⟩) R74065
theorem R65987 : Reach 65987 := rs (se 1 (by rfl) ⟨49490, by rfl⟩) R98981
theorem R98771 : Reach 98771 := rs (se 1 (by rfl) ⟨74078, by rfl⟩) R148157
theorem R66003 : Reach 66003 := rs (se 1 (by rfl) ⟨49502, by rfl⟩) R99005
theorem R360931 : Reach 360931 := rs (se 1 (by rfl) ⟨270698, by rfl⟩) R541397
theorem R66019 : Reach 66019 := rs (se 1 (by rfl) ⟨49514, by rfl⟩) R99029
theorem R98801 : Reach 98801 := rs (se 2 (by rfl) ⟨37050, by rfl⟩) R74101
theorem R66035 : Reach 66035 := rs (se 1 (by rfl) ⟨49526, by rfl⟩) R99053
theorem R98819 : Reach 98819 := rs (se 1 (by rfl) ⟨74114, by rfl⟩) R148229
theorem R66051 : Reach 66051 := rs (se 1 (by rfl) ⟨49538, by rfl⟩) R99077
theorem R164369 : Reach 164369 := rs (se 2 (by rfl) ⟨61638, by rfl⟩) R123277
theorem R66067 : Reach 66067 := rs (se 1 (by rfl) ⟨49550, by rfl⟩) R99101
theorem R98849 : Reach 98849 := rs (se 2 (by rfl) ⟨37068, by rfl⟩) R74137
theorem R66083 : Reach 66083 := rs (se 1 (by rfl) ⟨49562, by rfl⟩) R99125
theorem R98867 : Reach 98867 := rs (se 1 (by rfl) ⟨74150, by rfl⟩) R148301
theorem R66099 : Reach 66099 := rs (se 1 (by rfl) ⟨49574, by rfl⟩) R99149
theorem R66115 : Reach 66115 := rs (se 1 (by rfl) ⟨49586, by rfl⟩) R99173
theorem R361037 : Reach 361037 := rs (se 3 (by rfl) ⟨67694, by rfl⟩) R135389
theorem R98897 : Reach 98897 := rs (se 2 (by rfl) ⟨37086, by rfl⟩) R74173
theorem R66131 : Reach 66131 := rs (se 1 (by rfl) ⟨49598, by rfl⟩) R99197
theorem R98915 : Reach 98915 := rs (se 1 (by rfl) ⟨74186, by rfl⟩) R148373
theorem R66147 : Reach 66147 := rs (se 1 (by rfl) ⟨49610, by rfl⟩) R99221
theorem R66163 : Reach 66163 := rs (se 1 (by rfl) ⟨49622, by rfl⟩) R99245
theorem R98945 : Reach 98945 := rs (se 2 (by rfl) ⟨37104, by rfl⟩) R74209
theorem R66179 : Reach 66179 := rs (se 1 (by rfl) ⟨49634, by rfl⟩) R99269
theorem R98963 : Reach 98963 := rs (se 1 (by rfl) ⟨74222, by rfl⟩) R148445
theorem R66195 : Reach 66195 := rs (se 1 (by rfl) ⟨49646, by rfl⟩) R99293
theorem R66211 : Reach 66211 := rs (se 1 (by rfl) ⟨49658, by rfl⟩) R99317
theorem R98993 : Reach 98993 := rs (se 2 (by rfl) ⟨37122, by rfl⟩) R74245
theorem R66227 : Reach 66227 := rs (se 1 (by rfl) ⟨49670, by rfl⟩) R99341
theorem R99011 : Reach 99011 := rs (se 1 (by rfl) ⟨74258, by rfl⟩) R148517
theorem R66243 : Reach 66243 := rs (se 1 (by rfl) ⟨49682, by rfl⟩) R99365
theorem R66259 : Reach 66259 := rs (se 1 (by rfl) ⟨49694, by rfl⟩) R99389
theorem R99041 : Reach 99041 := rs (se 2 (by rfl) ⟨37140, by rfl⟩) R74281
theorem R66275 : Reach 66275 := rs (se 1 (by rfl) ⟨49706, by rfl⟩) R99413
theorem R99059 : Reach 99059 := rs (se 1 (by rfl) ⟨74294, by rfl⟩) R148589
theorem R66291 : Reach 66291 := rs (se 1 (by rfl) ⟨49718, by rfl⟩) R99437
theorem R66307 : Reach 66307 := rs (se 1 (by rfl) ⟨49730, by rfl⟩) R99461
theorem R99089 : Reach 99089 := rs (se 2 (by rfl) ⟨37158, by rfl⟩) R74317
theorem R66323 : Reach 66323 := rs (se 1 (by rfl) ⟨49742, by rfl⟩) R99485
theorem R99107 : Reach 99107 := rs (se 1 (by rfl) ⟨74330, by rfl⟩) R148661
theorem R66339 : Reach 66339 := rs (se 1 (by rfl) ⟨49754, by rfl⟩) R99509
theorem R66355 : Reach 66355 := rs (se 1 (by rfl) ⟨49766, by rfl⟩) R99533
theorem R99137 : Reach 99137 := rs (se 2 (by rfl) ⟨37176, by rfl⟩) R74353
theorem R66371 : Reach 66371 := rs (se 1 (by rfl) ⟨49778, by rfl⟩) R99557
theorem R99155 : Reach 99155 := rs (se 1 (by rfl) ⟨74366, by rfl⟩) R148733
theorem R66387 : Reach 66387 := rs (se 1 (by rfl) ⟨49790, by rfl⟩) R99581
theorem R66403 : Reach 66403 := rs (se 1 (by rfl) ⟨49802, by rfl⟩) R99605
theorem R99185 : Reach 99185 := rs (se 2 (by rfl) ⟨37194, by rfl⟩) R74389
theorem R66419 : Reach 66419 := rs (se 1 (by rfl) ⟨49814, by rfl⟩) R99629
theorem R99203 : Reach 99203 := rs (se 1 (by rfl) ⟨74402, by rfl⟩) R148805
theorem R66435 : Reach 66435 := rs (se 1 (by rfl) ⟨49826, by rfl⟩) R99653
theorem R66451 : Reach 66451 := rs (se 1 (by rfl) ⟨49838, by rfl⟩) R99677
theorem R99233 : Reach 99233 := rs (se 2 (by rfl) ⟨37212, by rfl⟩) R74425
theorem R66467 : Reach 66467 := rs (se 1 (by rfl) ⟨49850, by rfl⟩) R99701
theorem R99251 : Reach 99251 := rs (se 1 (by rfl) ⟨74438, by rfl⟩) R148877
theorem R66483 : Reach 66483 := rs (se 1 (by rfl) ⟨49862, by rfl⟩) R99725
theorem R66499 : Reach 66499 := rs (se 1 (by rfl) ⟨49874, by rfl⟩) R99749
theorem R99281 : Reach 99281 := rs (se 2 (by rfl) ⟨37230, by rfl⟩) R74461
theorem R66515 : Reach 66515 := rs (se 1 (by rfl) ⟨49886, by rfl⟩) R99773
theorem R99299 : Reach 99299 := rs (se 1 (by rfl) ⟨74474, by rfl⟩) R148949
theorem R66531 : Reach 66531 := rs (se 1 (by rfl) ⟨49898, by rfl⟩) R99797
theorem R66547 : Reach 66547 := rs (se 1 (by rfl) ⟨49910, by rfl⟩) R99821
theorem R99329 : Reach 99329 := rs (se 2 (by rfl) ⟨37248, by rfl⟩) R74497
theorem R66563 : Reach 66563 := rs (se 1 (by rfl) ⟨49922, by rfl⟩) R99845
theorem R99347 : Reach 99347 := rs (se 1 (by rfl) ⟨74510, by rfl⟩) R149021
theorem R66579 : Reach 66579 := rs (se 1 (by rfl) ⟨49934, by rfl⟩) R99869
theorem R66595 : Reach 66595 := rs (se 1 (by rfl) ⟨49946, by rfl⟩) R99893
theorem R99377 : Reach 99377 := rs (se 2 (by rfl) ⟨37266, by rfl⟩) R74533
theorem R66611 : Reach 66611 := rs (se 1 (by rfl) ⟨49958, by rfl⟩) R99917
theorem R99395 : Reach 99395 := rs (se 1 (by rfl) ⟨74546, by rfl⟩) R149093
theorem R66627 : Reach 66627 := rs (se 1 (by rfl) ⟨49970, by rfl⟩) R99941
theorem R66643 : Reach 66643 := rs (se 1 (by rfl) ⟨49982, by rfl⟩) R99965
theorem R99425 : Reach 99425 := rs (se 2 (by rfl) ⟨37284, by rfl⟩) R74569
theorem R66659 : Reach 66659 := rs (se 1 (by rfl) ⟨49994, by rfl⟩) R99989
theorem R99443 : Reach 99443 := rs (se 1 (by rfl) ⟨74582, by rfl⟩) R149165
theorem R66675 : Reach 66675 := rs (se 1 (by rfl) ⟨50006, by rfl⟩) R100013
theorem R66691 : Reach 66691 := rs (se 1 (by rfl) ⟨50018, by rfl⟩) R100037
theorem R99473 : Reach 99473 := rs (se 2 (by rfl) ⟨37302, by rfl⟩) R74605
theorem R66707 : Reach 66707 := rs (se 1 (by rfl) ⟨50030, by rfl⟩) R100061
theorem R99491 : Reach 99491 := rs (se 1 (by rfl) ⟨74618, by rfl⟩) R149237
theorem R66723 : Reach 66723 := rs (se 1 (by rfl) ⟨50042, by rfl⟩) R100085
theorem R66739 : Reach 66739 := rs (se 1 (by rfl) ⟨50054, by rfl⟩) R100109
theorem R99521 : Reach 99521 := rs (se 2 (by rfl) ⟨37320, by rfl⟩) R74641
theorem R66755 : Reach 66755 := rs (se 1 (by rfl) ⟨50066, by rfl⟩) R100133
theorem R99539 : Reach 99539 := rs (se 1 (by rfl) ⟨74654, by rfl⟩) R149309
theorem R66771 : Reach 66771 := rs (se 1 (by rfl) ⟨50078, by rfl⟩) R100157
theorem R66787 : Reach 66787 := rs (se 1 (by rfl) ⟨50090, by rfl⟩) R100181
theorem R99569 : Reach 99569 := rs (se 2 (by rfl) ⟨37338, by rfl⟩) R74677
theorem R66803 : Reach 66803 := rs (se 1 (by rfl) ⟨50102, by rfl⟩) R100205
theorem R99587 : Reach 99587 := rs (se 1 (by rfl) ⟨74690, by rfl⟩) R149381
theorem R66819 : Reach 66819 := rs (se 1 (by rfl) ⟨50114, by rfl⟩) R100229
theorem R66835 : Reach 66835 := rs (se 1 (by rfl) ⟨50126, by rfl⟩) R100253
theorem R99617 : Reach 99617 := rs (se 2 (by rfl) ⟨37356, by rfl⟩) R74713
theorem R66851 : Reach 66851 := rs (se 1 (by rfl) ⟨50138, by rfl⟩) R100277
theorem R99635 : Reach 99635 := rs (se 1 (by rfl) ⟨74726, by rfl⟩) R149453
theorem R66867 : Reach 66867 := rs (se 1 (by rfl) ⟨50150, by rfl⟩) R100301
theorem R66883 : Reach 66883 := rs (se 1 (by rfl) ⟨50162, by rfl⟩) R100325
theorem R886085 : Reach 886085 := rs (se 4 (by rfl) ⟨83070, by rfl⟩) R166141
theorem R99665 : Reach 99665 := rs (se 2 (by rfl) ⟨37374, by rfl⟩) R74749
theorem R66899 : Reach 66899 := rs (se 1 (by rfl) ⟨50174, by rfl⟩) R100349
theorem R99683 : Reach 99683 := rs (se 1 (by rfl) ⟨74762, by rfl⟩) R149525
theorem R66915 : Reach 66915 := rs (se 1 (by rfl) ⟨50186, by rfl⟩) R100373
theorem R66931 : Reach 66931 := rs (se 1 (by rfl) ⟨50198, by rfl⟩) R100397
theorem R99713 : Reach 99713 := rs (se 2 (by rfl) ⟨37392, by rfl⟩) R74785
theorem R66947 : Reach 66947 := rs (se 1 (by rfl) ⟨50210, by rfl⟩) R100421
theorem R99731 : Reach 99731 := rs (se 1 (by rfl) ⟨74798, by rfl⟩) R149597
theorem R66963 : Reach 66963 := rs (se 1 (by rfl) ⟨50222, by rfl⟩) R100445
theorem R66979 : Reach 66979 := rs (se 1 (by rfl) ⟨50234, by rfl⟩) R100469
theorem R99761 : Reach 99761 := rs (se 2 (by rfl) ⟨37410, by rfl⟩) R74821
theorem R66995 : Reach 66995 := rs (se 1 (by rfl) ⟨50246, by rfl⟩) R100493
theorem R99779 : Reach 99779 := rs (se 1 (by rfl) ⟨74834, by rfl⟩) R149669
theorem R67011 : Reach 67011 := rs (se 1 (by rfl) ⟨50258, by rfl⟩) R100517
theorem R67027 : Reach 67027 := rs (se 1 (by rfl) ⟨50270, by rfl⟩) R100541
theorem R99809 : Reach 99809 := rs (se 2 (by rfl) ⟨37428, by rfl⟩) R74857
theorem R67043 : Reach 67043 := rs (se 1 (by rfl) ⟨50282, by rfl⟩) R100565
theorem R165361 : Reach 165361 := rs (se 2 (by rfl) ⟨62010, by rfl⟩) R124021
theorem R99827 : Reach 99827 := rs (se 1 (by rfl) ⟨74870, by rfl⟩) R149741
theorem R67059 : Reach 67059 := rs (se 1 (by rfl) ⟨50294, by rfl⟩) R100589
theorem R67075 : Reach 67075 := rs (se 1 (by rfl) ⟨50306, by rfl⟩) R100613
theorem R99857 : Reach 99857 := rs (se 2 (by rfl) ⟨37446, by rfl⟩) R74893
theorem R67091 : Reach 67091 := rs (se 1 (by rfl) ⟨50318, by rfl⟩) R100637
theorem R99875 : Reach 99875 := rs (se 1 (by rfl) ⟨74906, by rfl⟩) R149813
theorem R67107 : Reach 67107 := rs (se 1 (by rfl) ⟨50330, by rfl⟩) R100661
theorem R67123 : Reach 67123 := rs (se 1 (by rfl) ⟨50342, by rfl⟩) R100685
theorem R99905 : Reach 99905 := rs (se 2 (by rfl) ⟨37464, by rfl⟩) R74929
theorem R99923 : Reach 99923 := rs (se 1 (by rfl) ⟨74942, by rfl⟩) R149885
theorem R99953 : Reach 99953 := rs (se 2 (by rfl) ⟨37482, by rfl⟩) R74965
theorem R99971 : Reach 99971 := rs (se 1 (by rfl) ⟨74978, by rfl⟩) R149957
theorem R394885 : Reach 394885 := rs (se 4 (by rfl) ⟨37020, by rfl⟩) R74041
theorem R100001 : Reach 100001 := rs (se 2 (by rfl) ⟨37500, by rfl⟩) R75001
theorem R263843 : Reach 263843 := rs (se 1 (by rfl) ⟨197882, by rfl⟩) R395765
theorem R100019 : Reach 100019 := rs (se 1 (by rfl) ⟨75014, by rfl⟩) R150029
theorem R100049 : Reach 100049 := rs (se 2 (by rfl) ⟨37518, by rfl⟩) R75037
theorem R132835 : Reach 132835 := rs (se 1 (by rfl) ⟨99626, by rfl⟩) R199253
theorem R100067 : Reach 100067 := rs (se 1 (by rfl) ⟨75050, by rfl⟩) R150101
theorem R100097 : Reach 100097 := rs (se 2 (by rfl) ⟨37536, by rfl⟩) R75073
theorem R165635 : Reach 165635 := rs (se 1 (by rfl) ⟨124226, by rfl⟩) R248453
theorem R100115 : Reach 100115 := rs (se 1 (by rfl) ⟨75086, by rfl⟩) R150173
theorem R329507 : Reach 329507 := rs (se 1 (by rfl) ⟨247130, by rfl⟩) R494261
theorem R100145 : Reach 100145 := rs (se 2 (by rfl) ⟨37554, by rfl⟩) R75109
theorem R100163 : Reach 100163 := rs (se 1 (by rfl) ⟨75122, by rfl⟩) R150245
theorem R100193 : Reach 100193 := rs (se 2 (by rfl) ⟨37572, by rfl⟩) R75145
theorem R100211 : Reach 100211 := rs (se 1 (by rfl) ⟨75158, by rfl⟩) R150317
theorem R100241 : Reach 100241 := rs (se 2 (by rfl) ⟨37590, by rfl⟩) R75181
theorem R100259 : Reach 100259 := rs (se 1 (by rfl) ⟨75194, by rfl⟩) R150389
theorem R100289 : Reach 100289 := rs (se 2 (by rfl) ⟨37608, by rfl⟩) R75217
theorem R165827 : Reach 165827 := rs (se 1 (by rfl) ⟨124370, by rfl⟩) R248741
theorem R133073 : Reach 133073 := rs (se 2 (by rfl) ⟨49902, by rfl⟩) R99805
theorem R100307 : Reach 100307 := rs (se 1 (by rfl) ⟨75230, by rfl⟩) R150461
theorem R100337 : Reach 100337 := rs (se 2 (by rfl) ⟨37626, by rfl⟩) R75253
theorem R100355 : Reach 100355 := rs (se 1 (by rfl) ⟨75266, by rfl⟩) R150533
theorem R100385 : Reach 100385 := rs (se 2 (by rfl) ⟨37644, by rfl⟩) R75289
theorem R100403 : Reach 100403 := rs (se 1 (by rfl) ⟨75302, by rfl⟩) R150605
theorem R100433 : Reach 100433 := rs (se 2 (by rfl) ⟨37662, by rfl⟩) R75325
theorem R329827 : Reach 329827 := rs (se 1 (by rfl) ⟨247370, by rfl⟩) R494741
theorem R100451 : Reach 100451 := rs (se 1 (by rfl) ⟨75338, by rfl⟩) R150677
theorem R100481 : Reach 100481 := rs (se 2 (by rfl) ⟨37680, by rfl⟩) R75361
theorem R100499 : Reach 100499 := rs (se 1 (by rfl) ⟨75374, by rfl⟩) R150749
theorem R100529 : Reach 100529 := rs (se 2 (by rfl) ⟨37698, by rfl⟩) R75397
theorem R67763 : Reach 67763 := rs (se 1 (by rfl) ⟨50822, by rfl⟩) R101645
theorem R100547 : Reach 100547 := rs (se 1 (by rfl) ⟨75410, by rfl⟩) R150821
theorem R100577 : Reach 100577 := rs (se 2 (by rfl) ⟨37716, by rfl⟩) R75433
theorem R100595 : Reach 100595 := rs (se 1 (by rfl) ⟨75446, by rfl⟩) R150893
theorem R100625 : Reach 100625 := rs (se 2 (by rfl) ⟨37734, by rfl⟩) R75469
theorem R100643 : Reach 100643 := rs (se 1 (by rfl) ⟨75482, by rfl⟩) R150965
theorem R100673 : Reach 100673 := rs (se 2 (by rfl) ⟨37752, by rfl⟩) R75505
theorem R330317 : Reach 330317 := rs (se 3 (by rfl) ⟨61934, by rfl⟩) R123869
theorem R101009 : Reach 101009 := rs (se 2 (by rfl) ⟨37878, by rfl⟩) R75757
theorem R101155 : Reach 101155 := rs (se 1 (by rfl) ⟨75866, by rfl⟩) R151733
theorem R166769 : Reach 166769 := rs (se 2 (by rfl) ⟨62538, by rfl⟩) R125077
theorem R166819 : Reach 166819 := rs (se 1 (by rfl) ⟨125114, by rfl⟩) R250229
theorem R854981 : Reach 854981 := rs (se 4 (by rfl) ⟨80154, by rfl⟩) R160309
theorem R232483 : Reach 232483 := rs (se 1 (by rfl) ⟨174362, by rfl⟩) R348725
theorem R166961 : Reach 166961 := rs (se 2 (by rfl) ⟨62610, by rfl⟩) R125221
theorem R232739 : Reach 232739 := rs (se 1 (by rfl) ⟨174554, by rfl⟩) R349109
theorem R101747 : Reach 101747 := rs (se 1 (by rfl) ⟨76310, by rfl⟩) R152621
theorem R363953 : Reach 363953 := rs (se 2 (by rfl) ⟨136482, by rfl⟩) R272965
theorem R1215971 : Reach 1215971 := rs (se 1 (by rfl) ⟨911978, by rfl⟩) R1823957
theorem R691811 : Reach 691811 := rs (se 1 (by rfl) ⟨518858, by rfl⟩) R1037717
theorem R462449 : Reach 462449 := rs (se 2 (by rfl) ⟨173418, by rfl⟩) R346837
theorem R790157 : Reach 790157 := rs (se 3 (by rfl) ⟨148154, by rfl⟩) R296309
theorem R69331 : Reach 69331 := rs (se 1 (by rfl) ⟨51998, by rfl⟩) R103997
theorem R560965 : Reach 560965 := rs (se 4 (by rfl) ⟨52590, by rfl⟩) R105181
theorem R167953 : Reach 167953 := rs (se 2 (by rfl) ⟨62982, by rfl⟩) R125965
theorem R69779 : Reach 69779 := rs (se 1 (by rfl) ⟨52334, by rfl⟩) R104669
theorem R102593 : Reach 102593 := rs (se 2 (by rfl) ⟨38472, by rfl⟩) R76945
theorem R168227 : Reach 168227 := rs (se 1 (by rfl) ⟨126170, by rfl⟩) R252341
theorem R1544501 : Reach 1544501 := rs (se 5 (by rfl) ⟨72398, by rfl⟩) R144797
theorem R135587 : Reach 135587 := rs (se 1 (by rfl) ⟨101690, by rfl⟩) R203381
theorem R233891 : Reach 233891 := rs (se 1 (by rfl) ⟨175418, by rfl⟩) R350837
theorem R168419 : Reach 168419 := rs (se 1 (by rfl) ⟨126314, by rfl⟩) R252629
theorem R692749 : Reach 692749 := rs (se 3 (by rfl) ⟨129890, by rfl⟩) R259781
theorem R135697 : Reach 135697 := rs (se 2 (by rfl) ⟨50886, by rfl⟩) R101773
theorem R365411 : Reach 365411 := rs (se 1 (by rfl) ⟨274058, by rfl⟩) R548117
theorem R103331 : Reach 103331 := rs (se 1 (by rfl) ⟨77498, by rfl⟩) R154997
theorem R169037 : Reach 169037 := rs (se 3 (by rfl) ⟨31694, by rfl⟩) R63389
theorem R2823281 : Reach 2823281 := rs (se 2 (by rfl) ⟨1058730, by rfl⟩) R2117461
theorem R169229 : Reach 169229 := rs (se 3 (by rfl) ⟨31730, by rfl⟩) R63461
theorem R202115 : Reach 202115 := rs (se 1 (by rfl) ⟨151586, by rfl⟩) R303173
theorem R169361 : Reach 169361 := rs (se 2 (by rfl) ⟨63510, by rfl⟩) R127021
theorem R71059 : Reach 71059 := rs (se 1 (by rfl) ⟨53294, by rfl⟩) R106589
theorem R333233 : Reach 333233 := rs (se 2 (by rfl) ⟨124962, by rfl⟩) R249925
theorem R169411 : Reach 169411 := rs (se 1 (by rfl) ⟨127058, by rfl⟩) R254117
theorem R71155 : Reach 71155 := rs (se 1 (by rfl) ⟨53366, by rfl⟩) R106733
theorem R71203 : Reach 71203 := rs (se 1 (by rfl) ⟨53402, by rfl⟩) R106805
theorem R169553 : Reach 169553 := rs (se 2 (by rfl) ⟨63582, by rfl⟩) R127165
theorem R71347 : Reach 71347 := rs (se 1 (by rfl) ⟨53510, by rfl⟩) R107021
theorem R71491 : Reach 71491 := rs (se 1 (by rfl) ⟨53618, by rfl⟩) R107237
theorem R104323 : Reach 104323 := rs (se 1 (by rfl) ⟨78242, by rfl⟩) R156485
theorem R71635 : Reach 71635 := rs (se 1 (by rfl) ⟨53726, by rfl⟩) R107453
theorem R71779 : Reach 71779 := rs (se 1 (by rfl) ⟨53834, by rfl⟩) R107669
theorem R104561 : Reach 104561 := rs (se 2 (by rfl) ⟨39210, by rfl⟩) R78421
theorem R399587 : Reach 399587 := rs (se 1 (by rfl) ⟨299690, by rfl⟩) R599381
theorem R71923 : Reach 71923 := rs (se 1 (by rfl) ⟨53942, by rfl⟩) R107885
theorem R104771 : Reach 104771 := rs (se 1 (by rfl) ⟨78578, by rfl⟩) R157157
theorem R72067 : Reach 72067 := rs (se 1 (by rfl) ⟨54050, by rfl⟩) R108101
theorem R268771 : Reach 268771 := rs (se 1 (by rfl) ⟨201578, by rfl⟩) R403157
theorem R137713 : Reach 137713 := rs (se 2 (by rfl) ⟨51642, by rfl⟩) R103285
theorem R72211 : Reach 72211 := rs (se 1 (by rfl) ⟨54158, by rfl⟩) R108317
theorem R72355 : Reach 72355 := rs (se 1 (by rfl) ⟨54266, by rfl⟩) R108533
theorem R72499 : Reach 72499 := rs (se 1 (by rfl) ⟨54374, by rfl⟩) R108749
theorem R203597 : Reach 203597 := rs (se 3 (by rfl) ⟨38174, by rfl⟩) R76349
theorem R465763 : Reach 465763 := rs (se 1 (by rfl) ⟨349322, by rfl⟩) R698645
theorem R334691 : Reach 334691 := rs (se 1 (by rfl) ⟨251018, by rfl⟩) R502037
theorem R498545 : Reach 498545 := rs (se 2 (by rfl) ⟨186954, by rfl⟩) R373909
theorem R138115 : Reach 138115 := rs (se 1 (by rfl) ⟨103586, by rfl⟩) R207173
theorem R236429 : Reach 236429 := rs (se 3 (by rfl) ⟨44330, by rfl⟩) R88661
theorem R72643 : Reach 72643 := rs (se 1 (by rfl) ⟨54482, by rfl⟩) R108965
theorem R203725 : Reach 203725 := rs (se 3 (by rfl) ⟨38198, by rfl⟩) R76397
theorem R105553 : Reach 105553 := rs (se 2 (by rfl) ⟨39582, by rfl⟩) R79165
theorem R72787 : Reach 72787 := rs (se 1 (by rfl) ⟨54590, by rfl⟩) R109181
theorem R72931 : Reach 72931 := rs (se 1 (by rfl) ⟨54698, by rfl⟩) R109397
theorem R72947 : Reach 72947 := rs (se 1 (by rfl) ⟨54710, by rfl⟩) R109421
theorem R73075 : Reach 73075 := rs (se 1 (by rfl) ⟨54806, by rfl⟩) R109613
theorem R73219 : Reach 73219 := rs (se 1 (by rfl) ⟨54914, by rfl⟩) R109829
theorem R269873 : Reach 269873 := rs (se 2 (by rfl) ⟨101202, by rfl⟩) R202405
theorem R335501 : Reach 335501 := rs (se 3 (by rfl) ⟨62906, by rfl⟩) R125813
theorem R73363 : Reach 73363 := rs (se 1 (by rfl) ⟨55022, by rfl⟩) R110045
theorem R73507 : Reach 73507 := rs (se 1 (by rfl) ⟨55130, by rfl⟩) R110261
theorem R106355 : Reach 106355 := rs (se 1 (by rfl) ⟨79766, by rfl⟩) R159533
theorem R73651 : Reach 73651 := rs (se 1 (by rfl) ⟨55238, by rfl⟩) R110477
theorem R73795 : Reach 73795 := rs (se 1 (by rfl) ⟨55346, by rfl⟩) R110693
theorem R106609 : Reach 106609 := rs (se 2 (by rfl) ⟨39978, by rfl⟩) R79957
theorem R106643 : Reach 106643 := rs (se 1 (by rfl) ⟨79982, by rfl⟩) R159965
theorem R73891 : Reach 73891 := rs (se 1 (by rfl) ⟨55418, by rfl⟩) R110837
theorem R73939 : Reach 73939 := rs (se 1 (by rfl) ⟨55454, by rfl⟩) R110909
theorem R106771 : Reach 106771 := rs (se 1 (by rfl) ⟨80078, by rfl⟩) R160157
theorem R270641 : Reach 270641 := rs (se 2 (by rfl) ⟨101490, by rfl⟩) R202981
theorem R139619 : Reach 139619 := rs (se 1 (by rfl) ⟨104714, by rfl⟩) R209429
theorem R74083 : Reach 74083 := rs (se 1 (by rfl) ⟨55562, by rfl⟩) R111125
theorem R106867 : Reach 106867 := rs (se 1 (by rfl) ⟨80150, by rfl⟩) R160301
theorem R106913 : Reach 106913 := rs (se 2 (by rfl) ⟨40092, by rfl⟩) R80185
theorem R74227 : Reach 74227 := rs (se 1 (by rfl) ⟨55670, by rfl⟩) R111341
theorem R107041 : Reach 107041 := rs (se 2 (by rfl) ⟨40140, by rfl⟩) R80281
theorem R107075 : Reach 107075 := rs (se 1 (by rfl) ⟨80306, by rfl⟩) R160613
theorem R74371 : Reach 74371 := rs (se 1 (by rfl) ⟨55778, by rfl⟩) R111557
theorem R107203 : Reach 107203 := rs (se 1 (by rfl) ⟨80402, by rfl⟩) R160805
theorem R205571 : Reach 205571 := rs (se 1 (by rfl) ⟨154178, by rfl⟩) R308357
theorem R74515 : Reach 74515 := rs (se 1 (by rfl) ⟨55886, by rfl⟩) R111773
theorem R107345 : Reach 107345 := rs (se 2 (by rfl) ⟨40254, by rfl⟩) R80509
theorem R500579 : Reach 500579 := rs (se 1 (by rfl) ⟨375434, by rfl⟩) R750869
theorem R205699 : Reach 205699 := rs (se 1 (by rfl) ⟨154274, by rfl⟩) R308549
theorem R107411 : Reach 107411 := rs (se 1 (by rfl) ⟨80558, by rfl⟩) R161117
theorem R74659 : Reach 74659 := rs (se 1 (by rfl) ⟨55994, by rfl⟩) R111989
theorem R271309 : Reach 271309 := rs (se 3 (by rfl) ⟨50870, by rfl⟩) R101741
theorem R107473 : Reach 107473 := rs (se 2 (by rfl) ⟨40302, by rfl⟩) R80605
theorem R107507 : Reach 107507 := rs (se 1 (by rfl) ⟨80630, by rfl⟩) R161261
theorem R205841 : Reach 205841 := rs (se 2 (by rfl) ⟨77190, by rfl⟩) R154381
theorem R74803 : Reach 74803 := rs (se 1 (by rfl) ⟨56102, by rfl⟩) R112205
theorem R107635 : Reach 107635 := rs (se 1 (by rfl) ⟨80726, by rfl⟩) R161453
theorem R205955 : Reach 205955 := rs (se 1 (by rfl) ⟨154466, by rfl⟩) R308933
theorem R74947 : Reach 74947 := rs (se 1 (by rfl) ⟨56210, by rfl⟩) R112421
theorem R107777 : Reach 107777 := rs (se 2 (by rfl) ⟨40416, by rfl⟩) R80833
theorem R304397 : Reach 304397 := rs (se 3 (by rfl) ⟨57074, by rfl⟩) R114149
theorem R75091 : Reach 75091 := rs (se 1 (by rfl) ⟨56318, by rfl⟩) R112637
theorem R107905 : Reach 107905 := rs (se 2 (by rfl) ⟨40464, by rfl⟩) R80929
theorem R107939 : Reach 107939 := rs (se 1 (by rfl) ⟨80954, by rfl⟩) R161909
theorem R140771 : Reach 140771 := rs (se 1 (by rfl) ⟨105578, by rfl⟩) R211157
theorem R75235 : Reach 75235 := rs (se 1 (by rfl) ⟨56426, by rfl⟩) R112853
theorem R271907 : Reach 271907 := rs (se 1 (by rfl) ⟨203930, by rfl⟩) R407861
theorem R108067 : Reach 108067 := rs (se 1 (by rfl) ⟨81050, by rfl⟩) R162101
theorem R140849 : Reach 140849 := rs (se 2 (by rfl) ⟨52818, by rfl⟩) R105637
theorem R173645 : Reach 173645 := rs (se 3 (by rfl) ⟨32558, by rfl⟩) R65117
theorem R75379 : Reach 75379 := rs (se 1 (by rfl) ⟨56534, by rfl⟩) R113069
theorem R108209 : Reach 108209 := rs (se 2 (by rfl) ⟨40578, by rfl⟩) R81157
theorem R108337 : Reach 108337 := rs (se 2 (by rfl) ⟨40626, by rfl⟩) R81253
theorem R108371 : Reach 108371 := rs (se 1 (by rfl) ⟨81278, by rfl⟩) R162557
theorem R108499 : Reach 108499 := rs (se 1 (by rfl) ⟨81374, by rfl⟩) R162749
theorem R108641 : Reach 108641 := rs (se 2 (by rfl) ⟨40740, by rfl⟩) R81481
theorem R75907 : Reach 75907 := rs (se 1 (by rfl) ⟨56930, by rfl⟩) R113861
theorem R108769 : Reach 108769 := rs (se 2 (by rfl) ⟨40788, by rfl⟩) R81577
theorem R108803 : Reach 108803 := rs (se 1 (by rfl) ⟨81602, by rfl⟩) R163205
theorem R174467 : Reach 174467 := rs (se 1 (by rfl) ⟨130850, by rfl⟩) R261701
theorem R108931 : Reach 108931 := rs (se 1 (by rfl) ⟨81698, by rfl⟩) R163397
theorem R76195 : Reach 76195 := rs (se 1 (by rfl) ⟨57146, by rfl⟩) R114293
theorem R141745 : Reach 141745 := rs (se 2 (by rfl) ⟨53154, by rfl⟩) R106309
theorem R141763 : Reach 141763 := rs (se 1 (by rfl) ⟨106322, by rfl⟩) R212645
theorem R109009 : Reach 109009 := rs (se 2 (by rfl) ⟨40878, by rfl⟩) R81757
theorem R338417 : Reach 338417 := rs (se 2 (by rfl) ⟨126906, by rfl⟩) R253813
theorem R109073 : Reach 109073 := rs (se 2 (by rfl) ⟨40902, by rfl⟩) R81805
theorem R240205 : Reach 240205 := rs (se 3 (by rfl) ⟨45038, by rfl⟩) R90077
theorem R371299 : Reach 371299 := rs (se 1 (by rfl) ⟨278474, by rfl⟩) R556949
theorem R109201 : Reach 109201 := rs (se 2 (by rfl) ⟨40950, by rfl⟩) R81901
theorem R109235 : Reach 109235 := rs (se 1 (by rfl) ⟨81926, by rfl⟩) R163853
theorem R109363 : Reach 109363 := rs (se 1 (by rfl) ⟨82022, by rfl⟩) R164045
theorem R207697 : Reach 207697 := rs (se 2 (by rfl) ⟨77886, by rfl⟩) R155773
theorem R109505 : Reach 109505 := rs (se 2 (by rfl) ⟨41064, by rfl⟩) R82129
theorem R306125 : Reach 306125 := rs (se 3 (by rfl) ⟨57398, by rfl⟩) R114797
theorem R142289 : Reach 142289 := rs (se 2 (by rfl) ⟨53358, by rfl⟩) R106717
theorem R142307 : Reach 142307 := rs (se 1 (by rfl) ⟨106730, by rfl⟩) R213461
theorem R109633 : Reach 109633 := rs (se 2 (by rfl) ⟨41112, by rfl⟩) R82225
theorem R109667 : Reach 109667 := rs (se 1 (by rfl) ⟨82250, by rfl⟩) R164501
theorem R306317 : Reach 306317 := rs (se 3 (by rfl) ⟨57434, by rfl⟩) R114869
theorem R109795 : Reach 109795 := rs (se 1 (by rfl) ⟨82346, by rfl⟩) R164693
theorem R142577 : Reach 142577 := rs (se 2 (by rfl) ⟨53466, by rfl⟩) R106933
theorem R142595 : Reach 142595 := rs (se 1 (by rfl) ⟨106946, by rfl⟩) R213893
theorem R240995 : Reach 240995 := rs (se 1 (by rfl) ⟨180746, by rfl⟩) R361493
theorem R109937 : Reach 109937 := rs (se 2 (by rfl) ⟨41226, by rfl⟩) R82453
theorem R110065 : Reach 110065 := rs (se 2 (by rfl) ⟨41274, by rfl⟩) R82549
theorem R405005 : Reach 405005 := rs (se 3 (by rfl) ⟨75938, by rfl⟩) R151877
theorem R142865 : Reach 142865 := rs (se 2 (by rfl) ⟨53574, by rfl⟩) R107149
theorem R110099 : Reach 110099 := rs (se 1 (by rfl) ⟨82574, by rfl⟩) R165149
theorem R142883 : Reach 142883 := rs (se 1 (by rfl) ⟨107162, by rfl⟩) R214325
theorem R110227 : Reach 110227 := rs (se 1 (by rfl) ⟨82670, by rfl⟩) R165341
theorem R110369 : Reach 110369 := rs (se 2 (by rfl) ⟨41388, by rfl⟩) R82777
theorem R143153 : Reach 143153 := rs (se 2 (by rfl) ⟨53682, by rfl⟩) R107365
theorem R143171 : Reach 143171 := rs (se 1 (by rfl) ⟨107378, by rfl⟩) R214757
theorem R110497 : Reach 110497 := rs (se 2 (by rfl) ⟨41436, by rfl⟩) R82873
theorem R208813 : Reach 208813 := rs (se 3 (by rfl) ⟨39152, by rfl⟩) R78305
theorem R110531 : Reach 110531 := rs (se 1 (by rfl) ⟨82898, by rfl⟩) R165797
theorem R405445 : Reach 405445 := rs (se 4 (by rfl) ⟨38010, by rfl⟩) R76021
theorem R241649 : Reach 241649 := rs (se 2 (by rfl) ⟨90618, by rfl⟩) R181237
theorem R110659 : Reach 110659 := rs (se 1 (by rfl) ⟨82994, by rfl⟩) R165989
theorem R143441 : Reach 143441 := rs (se 2 (by rfl) ⟨53790, by rfl⟩) R107581
theorem R143459 : Reach 143459 := rs (se 1 (by rfl) ⟨107594, by rfl⟩) R215189
theorem R143491 : Reach 143491 := rs (se 1 (by rfl) ⟨107618, by rfl⟩) R215237
theorem R110801 : Reach 110801 := rs (se 2 (by rfl) ⟨41550, by rfl⟩) R83101
theorem R110929 : Reach 110929 := rs (se 2 (by rfl) ⟨41598, by rfl⟩) R83197
theorem R143729 : Reach 143729 := rs (se 2 (by rfl) ⟨53898, by rfl⟩) R107797
theorem R569713 : Reach 569713 := rs (se 2 (by rfl) ⟨213642, by rfl⟩) R427285
theorem R110963 : Reach 110963 := rs (se 1 (by rfl) ⟨83222, by rfl⟩) R166445
theorem R143747 : Reach 143747 := rs (se 1 (by rfl) ⟨107810, by rfl⟩) R215621
theorem R111091 : Reach 111091 := rs (se 1 (by rfl) ⟨83318, by rfl⟩) R166637
theorem R111233 : Reach 111233 := rs (se 2 (by rfl) ⟨41712, by rfl⟩) R83425
theorem R144017 : Reach 144017 := rs (se 2 (by rfl) ⟨54006, by rfl⟩) R108013
theorem R144035 : Reach 144035 := rs (se 1 (by rfl) ⟨108026, by rfl⟩) R216053
theorem R209645 : Reach 209645 := rs (se 3 (by rfl) ⟨39308, by rfl⟩) R78617
theorem R111361 : Reach 111361 := rs (se 2 (by rfl) ⟨41760, by rfl⟩) R83521
theorem R111395 : Reach 111395 := rs (se 1 (by rfl) ⟨83546, by rfl⟩) R167093
theorem R111523 : Reach 111523 := rs (se 1 (by rfl) ⟨83642, by rfl⟩) R167285
theorem R144305 : Reach 144305 := rs (se 2 (by rfl) ⟨54114, by rfl⟩) R108229
theorem R144323 : Reach 144323 := rs (se 1 (by rfl) ⟨108242, by rfl⟩) R216485
theorem R111665 : Reach 111665 := rs (se 2 (by rfl) ⟨41874, by rfl⟩) R83749
theorem R111793 : Reach 111793 := rs (se 2 (by rfl) ⟨41922, by rfl⟩) R83845
theorem R144593 : Reach 144593 := rs (se 2 (by rfl) ⟨54222, by rfl⟩) R108445
theorem R111827 : Reach 111827 := rs (se 1 (by rfl) ⟨83870, by rfl⟩) R167741
theorem R144611 : Reach 144611 := rs (se 1 (by rfl) ⟨108458, by rfl⟩) R216917
theorem R275683 : Reach 275683 := rs (se 1 (by rfl) ⟨206762, by rfl⟩) R413525
theorem R111955 : Reach 111955 := rs (se 1 (by rfl) ⟨83966, by rfl⟩) R167933
theorem R243107 : Reach 243107 := rs (se 1 (by rfl) ⟨182330, by rfl⟩) R364661
theorem R243121 : Reach 243121 := rs (se 2 (by rfl) ⟨91170, by rfl⟩) R182341
theorem R112097 : Reach 112097 := rs (se 2 (by rfl) ⟨42036, by rfl⟩) R84073
theorem R144881 : Reach 144881 := rs (se 2 (by rfl) ⟨54330, by rfl⟩) R108661
theorem R341489 : Reach 341489 := rs (se 2 (by rfl) ⟨128058, by rfl⟩) R256117
theorem R144899 : Reach 144899 := rs (se 1 (by rfl) ⟨108674, by rfl⟩) R217349
theorem R374341 : Reach 374341 := rs (se 4 (by rfl) ⟨35094, by rfl⟩) R70189
theorem R112259 : Reach 112259 := rs (se 1 (by rfl) ⟨84194, by rfl⟩) R168389
theorem R669325 : Reach 669325 := rs (se 3 (by rfl) ⟨125498, by rfl⟩) R250997
theorem R145091 : Reach 145091 := rs (se 1 (by rfl) ⟨108818, by rfl⟩) R217637
theorem R112387 : Reach 112387 := rs (se 1 (by rfl) ⟨84290, by rfl⟩) R168581
theorem R145169 : Reach 145169 := rs (se 2 (by rfl) ⟨54438, by rfl⟩) R108877
theorem R145187 : Reach 145187 := rs (se 1 (by rfl) ⟨108890, by rfl⟩) R217781
theorem R79651 : Reach 79651 := rs (se 1 (by rfl) ⟨59738, by rfl⟩) R119477
theorem R112529 : Reach 112529 := rs (se 2 (by rfl) ⟨42198, by rfl⟩) R84397
theorem R407501 : Reach 407501 := rs (se 3 (by rfl) ⟨76406, by rfl⟩) R152813
theorem R767971 : Reach 767971 := rs (se 1 (by rfl) ⟨575978, by rfl⟩) R1151957
theorem R112657 : Reach 112657 := rs (se 2 (by rfl) ⟨42246, by rfl⟩) R84493
theorem R145457 : Reach 145457 := rs (se 2 (by rfl) ⟨54546, by rfl⟩) R109093
theorem R145475 : Reach 145475 := rs (se 1 (by rfl) ⟨109106, by rfl⟩) R218213
theorem R505925 : Reach 505925 := rs (se 4 (by rfl) ⟨47430, by rfl⟩) R94861
theorem R178253 : Reach 178253 := rs (se 3 (by rfl) ⟨33422, by rfl⟩) R66845
theorem R145745 : Reach 145745 := rs (se 2 (by rfl) ⟨54654, by rfl⟩) R109309
theorem R145763 : Reach 145763 := rs (se 1 (by rfl) ⟨109322, by rfl⟩) R218645
theorem R178531 : Reach 178531 := rs (se 1 (by rfl) ⟨133898, by rfl⟩) R267797
theorem R80291 : Reach 80291 := rs (se 1 (by rfl) ⟨60218, by rfl⟩) R120437
theorem R113105 : Reach 113105 := rs (se 2 (by rfl) ⟨42414, by rfl⟩) R84829
theorem R113123 : Reach 113123 := rs (se 1 (by rfl) ⟨84842, by rfl⟩) R169685
theorem R113251 : Reach 113251 := rs (se 1 (by rfl) ⟨84938, by rfl⟩) R169877
theorem R146033 : Reach 146033 := rs (se 2 (by rfl) ⟨54762, by rfl⟩) R109525
theorem R146051 : Reach 146051 := rs (se 1 (by rfl) ⟨109538, by rfl⟩) R219077
theorem R1718981 : Reach 1718981 := rs (se 4 (by rfl) ⟨161154, by rfl⟩) R322309
theorem R211747 : Reach 211747 := rs (se 1 (by rfl) ⟨158810, by rfl⟩) R317621
theorem R244579 : Reach 244579 := rs (se 1 (by rfl) ⟨183434, by rfl⟩) R366869
theorem R146321 : Reach 146321 := rs (se 2 (by rfl) ⟨54870, by rfl⟩) R109741
theorem R146339 : Reach 146339 := rs (se 1 (by rfl) ⟨109754, by rfl⟩) R219509
theorem R211889 : Reach 211889 := rs (se 2 (by rfl) ⟨79458, by rfl⟩) R158917
theorem R80995 : Reach 80995 := rs (se 1 (by rfl) ⟨60746, by rfl⟩) R121493
theorem R113827 : Reach 113827 := rs (se 1 (by rfl) ⟨85370, by rfl⟩) R170741
theorem R277681 : Reach 277681 := rs (se 2 (by rfl) ⟨104130, by rfl⟩) R208261
theorem R146609 : Reach 146609 := rs (se 2 (by rfl) ⟨54978, by rfl⟩) R109957
theorem R81091 : Reach 81091 := rs (se 1 (by rfl) ⟨60818, by rfl⟩) R121637
theorem R146627 : Reach 146627 := rs (se 1 (by rfl) ⟨109970, by rfl⟩) R219941
theorem R146897 : Reach 146897 := rs (se 2 (by rfl) ⟨55086, by rfl⟩) R110173
theorem R146915 : Reach 146915 := rs (se 1 (by rfl) ⟨110186, by rfl⟩) R220373
theorem R376325 : Reach 376325 := rs (se 4 (by rfl) ⟨35280, by rfl⟩) R70561
theorem R179779 : Reach 179779 := rs (se 1 (by rfl) ⟨134834, by rfl⟩) R269669
theorem R81587 : Reach 81587 := rs (se 1 (by rfl) ⟨61190, by rfl⟩) R122381
theorem R147185 : Reach 147185 := rs (se 2 (by rfl) ⟨55194, by rfl⟩) R110389
theorem R147203 : Reach 147203 := rs (se 1 (by rfl) ⟨110402, by rfl⟩) R220805
theorem R2015117 : Reach 2015117 := rs (se 3 (by rfl) ⟨377834, by rfl⟩) R755669
theorem R147473 : Reach 147473 := rs (se 2 (by rfl) ⟨55302, by rfl⟩) R110605
theorem R147491 : Reach 147491 := rs (se 1 (by rfl) ⟨110618, by rfl⟩) R221237
theorem R180269 : Reach 180269 := rs (se 3 (by rfl) ⟨33800, by rfl⟩) R67601
theorem R213137 : Reach 213137 := rs (se 2 (by rfl) ⟨79926, by rfl⟩) R159853
theorem R147761 : Reach 147761 := rs (se 2 (by rfl) ⟨55410, by rfl⟩) R110821
theorem R147779 : Reach 147779 := rs (se 1 (by rfl) ⟨110834, by rfl⟩) R221669
theorem R147811 : Reach 147811 := rs (se 1 (by rfl) ⟨110858, by rfl⟩) R221717
theorem R115057 : Reach 115057 := rs (se 2 (by rfl) ⟨43146, by rfl⟩) R86293
theorem R82291 : Reach 82291 := rs (se 1 (by rfl) ⟨61718, by rfl⟩) R123437
theorem R82387 : Reach 82387 := rs (se 1 (by rfl) ⟨61790, by rfl⟩) R123581
theorem R148049 : Reach 148049 := rs (se 2 (by rfl) ⟨55518, by rfl⟩) R111037
theorem R148067 : Reach 148067 := rs (se 1 (by rfl) ⟨111050, by rfl⟩) R222101
theorem R213677 : Reach 213677 := rs (se 3 (by rfl) ⟨40064, by rfl⟩) R80129
theorem R213731 : Reach 213731 := rs (se 1 (by rfl) ⟨160298, by rfl⟩) R320597
theorem R836405 : Reach 836405 := rs (se 5 (by rfl) ⟨39206, by rfl⟩) R78413
theorem R148337 : Reach 148337 := rs (se 2 (by rfl) ⟨55626, by rfl⟩) R111253
theorem R148355 : Reach 148355 := rs (se 1 (by rfl) ⟨111266, by rfl⟩) R222533
theorem R82883 : Reach 82883 := rs (se 1 (by rfl) ⟨62162, by rfl⟩) R124325
theorem R639971 : Reach 639971 := rs (se 1 (by rfl) ⟨479978, by rfl⟩) R959957
theorem R214001 : Reach 214001 := rs (se 2 (by rfl) ⟨80250, by rfl⟩) R160501
theorem R246797 : Reach 246797 := rs (se 3 (by rfl) ⟨46274, by rfl⟩) R92549
theorem R148625 : Reach 148625 := rs (se 2 (by rfl) ⟨55734, by rfl⟩) R111469
theorem R148643 : Reach 148643 := rs (se 1 (by rfl) ⟨111482, by rfl⟩) R222965
theorem R1262789 : Reach 1262789 := rs (se 4 (by rfl) ⟨118386, by rfl⟩) R236773
theorem R181453 : Reach 181453 := rs (se 3 (by rfl) ⟨34022, by rfl⟩) R68045
theorem R214285 : Reach 214285 := rs (se 3 (by rfl) ⟨40178, by rfl⟩) R80357
theorem R148913 : Reach 148913 := rs (se 2 (by rfl) ⟨55842, by rfl⟩) R111685
theorem R148931 : Reach 148931 := rs (se 1 (by rfl) ⟨111698, by rfl⟩) R223397
theorem R214541 : Reach 214541 := rs (se 3 (by rfl) ⟨40226, by rfl⟩) R80453
theorem R214595 : Reach 214595 := rs (se 1 (by rfl) ⟨160946, by rfl⟩) R321893
theorem R83587 : Reach 83587 := rs (se 1 (by rfl) ⟨62690, by rfl⟩) R125381
theorem R149201 : Reach 149201 := rs (se 2 (by rfl) ⟨55950, by rfl⟩) R111901
theorem R83683 : Reach 83683 := rs (se 1 (by rfl) ⟨62762, by rfl⟩) R125525
theorem R149219 : Reach 149219 := rs (se 1 (by rfl) ⟨111914, by rfl⟩) R223829
theorem R214865 : Reach 214865 := rs (se 2 (by rfl) ⟨80574, by rfl⟩) R161149
theorem R149489 : Reach 149489 := rs (se 2 (by rfl) ⟨56058, by rfl⟩) R112117
theorem R149507 : Reach 149507 := rs (se 1 (by rfl) ⟨112130, by rfl⟩) R224261
theorem R149635 : Reach 149635 := rs (se 1 (by rfl) ⟨112226, by rfl⟩) R224453
theorem R149681 : Reach 149681 := rs (se 2 (by rfl) ⟨56130, by rfl⟩) R112261
theorem R84179 : Reach 84179 := rs (se 1 (by rfl) ⟨63134, by rfl⟩) R126269
theorem R182513 : Reach 182513 := rs (se 2 (by rfl) ⟨68442, by rfl⟩) R136885
theorem R149777 : Reach 149777 := rs (se 2 (by rfl) ⟨56166, by rfl⟩) R112333
theorem R149795 : Reach 149795 := rs (se 1 (by rfl) ⟨112346, by rfl⟩) R224693
theorem R248141 : Reach 248141 := rs (se 3 (by rfl) ⟨46526, by rfl⟩) R93053
theorem R215405 : Reach 215405 := rs (se 3 (by rfl) ⟨40388, by rfl⟩) R80777
theorem R215459 : Reach 215459 := rs (se 1 (by rfl) ⟨161594, by rfl⟩) R323189
theorem R150065 : Reach 150065 := rs (se 2 (by rfl) ⟨56274, by rfl⟩) R112549
theorem R150083 : Reach 150083 := rs (se 1 (by rfl) ⟨112562, by rfl⟩) R225125
theorem R215729 : Reach 215729 := rs (se 2 (by rfl) ⟨80898, by rfl⟩) R161797
theorem R84721 : Reach 84721 := rs (se 2 (by rfl) ⟨31770, by rfl⟩) R63541
theorem R150353 : Reach 150353 := rs (se 2 (by rfl) ⟨56382, by rfl⟩) R112765
theorem R84817 : Reach 84817 := rs (se 2 (by rfl) ⟨31806, by rfl⟩) R63613
theorem R150371 : Reach 150371 := rs (se 1 (by rfl) ⟨112778, by rfl⟩) R225557
theorem R871309 : Reach 871309 := rs (se 3 (by rfl) ⟨163370, by rfl⟩) R326741
theorem R183185 : Reach 183185 := rs (se 2 (by rfl) ⟨68694, by rfl⟩) R137389
theorem R84883 : Reach 84883 := rs (se 1 (by rfl) ⟨63662, by rfl⟩) R127325
theorem R281713 : Reach 281713 := rs (se 2 (by rfl) ⟨105642, by rfl⟩) R211285
theorem R150641 : Reach 150641 := rs (se 2 (by rfl) ⟨56490, by rfl⟩) R112981
theorem R150659 : Reach 150659 := rs (se 1 (by rfl) ⟨112994, by rfl⟩) R225989
theorem R216269 : Reach 216269 := rs (se 3 (by rfl) ⟨40550, by rfl⟩) R81101
theorem R216323 : Reach 216323 := rs (se 1 (by rfl) ⟨162242, by rfl⟩) R324485
theorem R412933 : Reach 412933 := rs (se 4 (by rfl) ⟨38712, by rfl⟩) R77425
theorem R380173 : Reach 380173 := rs (se 3 (by rfl) ⟨71282, by rfl⟩) R142565
theorem R150929 : Reach 150929 := rs (se 2 (by rfl) ⟨56598, by rfl⟩) R113197
theorem R150947 : Reach 150947 := rs (se 1 (by rfl) ⟨113210, by rfl⟩) R226421
theorem R249293 : Reach 249293 := rs (se 3 (by rfl) ⟨46742, by rfl⟩) R93485
theorem R216593 : Reach 216593 := rs (se 2 (by rfl) ⟨81222, by rfl⟩) R162445
theorem R183971 : Reach 183971 := rs (se 1 (by rfl) ⟨137978, by rfl⟩) R275957
theorem R1199843 : Reach 1199843 := rs (se 1 (by rfl) ⟨899882, by rfl⟩) R1799765
theorem R118531 : Reach 118531 := rs (se 1 (by rfl) ⟨88898, by rfl⟩) R177797
theorem R347939 : Reach 347939 := rs (se 1 (by rfl) ⟨260954, by rfl⟩) R521909
theorem R249713 : Reach 249713 := rs (se 2 (by rfl) ⟨93642, by rfl⟩) R187285
theorem R348067 : Reach 348067 := rs (se 1 (by rfl) ⟨261050, by rfl⟩) R522101
theorem R184301 : Reach 184301 := rs (se 3 (by rfl) ⟨34556, by rfl⟩) R69113
theorem R380933 : Reach 380933 := rs (se 4 (by rfl) ⟨35712, by rfl⟩) R71425
theorem R217133 : Reach 217133 := rs (se 3 (by rfl) ⟨40712, by rfl⟩) R81425
theorem R184369 : Reach 184369 := rs (se 2 (by rfl) ⟨69138, by rfl⟩) R138277
theorem R217187 : Reach 217187 := rs (se 1 (by rfl) ⟨162890, by rfl⟩) R325781
theorem R118979 : Reach 118979 := rs (se 1 (by rfl) ⟨89234, by rfl⟩) R178469
theorem R184643 : Reach 184643 := rs (se 1 (by rfl) ⟨138482, by rfl⟩) R276965
theorem R217457 : Reach 217457 := rs (se 2 (by rfl) ⟨81546, by rfl⟩) R163093
theorem R17125829 : Reach 17125829 := rs (se 4 (by rfl) ⟨1605546, by rfl⟩) R3211093
theorem R86627 : Reach 86627 := rs (se 1 (by rfl) ⟨64970, by rfl⟩) R129941
theorem R348785 : Reach 348785 := rs (se 2 (by rfl) ⟨130794, by rfl⟩) R261589
theorem R643697 : Reach 643697 := rs (se 2 (by rfl) ⟨241386, by rfl⟩) R482773
theorem R185041 : Reach 185041 := rs (se 2 (by rfl) ⟨69390, by rfl⟩) R138781
theorem R217997 : Reach 217997 := rs (se 3 (by rfl) ⟨40874, by rfl⟩) R81749
theorem R218051 : Reach 218051 := rs (se 1 (by rfl) ⟨163538, by rfl⟩) R327077
theorem R119875 : Reach 119875 := rs (se 1 (by rfl) ⟨89906, by rfl⟩) R179813
theorem R87169 : Reach 87169 := rs (se 2 (by rfl) ⟨32688, by rfl⟩) R65377
theorem R185485 : Reach 185485 := rs (se 3 (by rfl) ⟨34778, by rfl⟩) R69557
theorem R382157 : Reach 382157 := rs (se 3 (by rfl) ⟨71654, by rfl⟩) R143309
theorem R218321 : Reach 218321 := rs (se 2 (by rfl) ⟨81870, by rfl⟩) R163741
theorem R120035 : Reach 120035 := rs (se 1 (by rfl) ⟨90026, by rfl⟩) R180053
theorem R251171 : Reach 251171 := rs (se 1 (by rfl) ⟨188378, by rfl⟩) R376757
theorem R185645 : Reach 185645 := rs (se 3 (by rfl) ⟨34808, by rfl⟩) R69617
theorem R480653 : Reach 480653 := rs (se 3 (by rfl) ⟨90122, by rfl⟩) R180245
theorem R218513 : Reach 218513 := rs (se 2 (by rfl) ⟨81942, by rfl⟩) R163885
theorem R185827 : Reach 185827 := rs (se 1 (by rfl) ⟨139370, by rfl⟩) R278741
theorem R218861 : Reach 218861 := rs (se 3 (by rfl) ⟨41036, by rfl⟩) R82073
theorem R120593 : Reach 120593 := rs (se 2 (by rfl) ⟨45222, by rfl⟩) R90445
theorem R218915 : Reach 218915 := rs (se 1 (by rfl) ⟨164186, by rfl⟩) R328373
theorem R415651 : Reach 415651 := rs (se 1 (by rfl) ⟨311738, by rfl⟩) R623477
theorem R219185 : Reach 219185 := rs (se 2 (by rfl) ⟨82194, by rfl⟩) R164389
theorem R547013 : Reach 547013 := rs (se 4 (by rfl) ⟨51282, by rfl⟩) R102565
theorem R448739 : Reach 448739 := rs (se 1 (by rfl) ⟨336554, by rfl⟩) R673109
theorem R252173 : Reach 252173 := rs (se 3 (by rfl) ⟨47282, by rfl⟩) R94565
theorem R121105 : Reach 121105 := rs (se 2 (by rfl) ⟨45414, by rfl⟩) R90829
theorem R219725 : Reach 219725 := rs (se 3 (by rfl) ⟨41198, by rfl⟩) R82397
theorem R219779 : Reach 219779 := rs (se 1 (by rfl) ⟨164834, by rfl⟩) R329669
theorem R285389 : Reach 285389 := rs (se 3 (by rfl) ⟨53510, by rfl⟩) R107021
theorem R1334069 : Reach 1334069 := rs (se 5 (by rfl) ⟨62534, by rfl⟩) R125069
theorem R187217 : Reach 187217 := rs (se 2 (by rfl) ⟨70206, by rfl⟩) R140413
theorem R220049 : Reach 220049 := rs (se 2 (by rfl) ⟨82518, by rfl⟩) R165037
theorem R711665 : Reach 711665 := rs (se 2 (by rfl) ⟨266874, by rfl⟩) R533749
theorem R875789 : Reach 875789 := rs (se 3 (by rfl) ⟨164210, by rfl⟩) R328421
theorem R318755 : Reach 318755 := rs (se 1 (by rfl) ⟨239066, by rfl⟩) R478133
theorem R122161 : Reach 122161 := rs (se 2 (by rfl) ⟨45810, by rfl⟩) R91621
theorem R220483 : Reach 220483 := rs (se 1 (by rfl) ⟨165362, by rfl⟩) R330725
theorem R220589 : Reach 220589 := rs (se 3 (by rfl) ⟨41360, by rfl⟩) R82721
theorem R220643 : Reach 220643 := rs (se 1 (by rfl) ⟨165482, by rfl⟩) R330965
theorem R122563 : Reach 122563 := rs (se 1 (by rfl) ⟨91922, by rfl⟩) R183845
theorem R122609 : Reach 122609 := rs (se 2 (by rfl) ⟨45978, by rfl⟩) R91957
theorem R220913 : Reach 220913 := rs (se 2 (by rfl) ⟨82842, by rfl⟩) R165685
theorem R188173 : Reach 188173 := rs (se 3 (by rfl) ⟨35282, by rfl⟩) R70565
theorem R417649 : Reach 417649 := rs (se 2 (by rfl) ⟨156618, by rfl⟩) R313237
theorem R90083 : Reach 90083 := rs (se 1 (by rfl) ⟨67562, by rfl⟩) R135125
theorem R188401 : Reach 188401 := rs (se 2 (by rfl) ⟨70650, by rfl⟩) R141301
theorem R122897 : Reach 122897 := rs (se 2 (by rfl) ⟨46086, by rfl⟩) R92173
theorem R90163 : Reach 90163 := rs (se 1 (by rfl) ⟨67622, by rfl⟩) R135245
theorem R188561 : Reach 188561 := rs (se 2 (by rfl) ⟨70710, by rfl⟩) R141421
theorem R483569 : Reach 483569 := rs (se 2 (by rfl) ⟨181338, by rfl⟩) R362677
theorem R188675 : Reach 188675 := rs (se 1 (by rfl) ⟨141506, by rfl⟩) R283013
theorem R221453 : Reach 221453 := rs (se 3 (by rfl) ⟨41522, by rfl⟩) R83045
theorem R221507 : Reach 221507 := rs (se 1 (by rfl) ⟨166130, by rfl⟩) R332261
theorem R254285 : Reach 254285 := rs (se 3 (by rfl) ⟨47678, by rfl⟩) R95357
theorem R90499 : Reach 90499 := rs (se 1 (by rfl) ⟨67874, by rfl⟩) R135749
theorem R483725 : Reach 483725 := rs (se 3 (by rfl) ⟨90698, by rfl⟩) R181397
theorem R319949 : Reach 319949 := rs (se 3 (by rfl) ⟨59990, by rfl⟩) R119981
theorem R90691 : Reach 90691 := rs (se 1 (by rfl) ⟨68018, by rfl⟩) R136037
theorem R221777 : Reach 221777 := rs (se 2 (by rfl) ⟨83166, by rfl⟩) R166333
theorem R811619 : Reach 811619 := rs (se 1 (by rfl) ⟨608714, by rfl⟩) R1217429
theorem R221869 : Reach 221869 := rs (se 3 (by rfl) ⟨41600, by rfl⟩) R83201
theorem R123619 : Reach 123619 := rs (se 1 (by rfl) ⟨92714, by rfl⟩) R185429
theorem R91057 : Reach 91057 := rs (se 2 (by rfl) ⟨34146, by rfl⟩) R68293
theorem R91091 : Reach 91091 := rs (se 1 (by rfl) ⟨68318, by rfl⟩) R136637
theorem R222317 : Reach 222317 := rs (se 3 (by rfl) ⟨41684, by rfl⟩) R83369
theorem R124067 : Reach 124067 := rs (se 1 (by rfl) ⟨93050, by rfl⟩) R186101
theorem R222371 : Reach 222371 := rs (se 1 (by rfl) ⟨166778, by rfl⟩) R333557
theorem R189677 : Reach 189677 := rs (se 3 (by rfl) ⟨35564, by rfl⟩) R71129
theorem R189859 : Reach 189859 := rs (se 1 (by rfl) ⟨142394, by rfl⟩) R284789
theorem R124337 : Reach 124337 := rs (se 2 (by rfl) ⟨46626, by rfl⟩) R93253
theorem R222641 : Reach 222641 := rs (se 2 (by rfl) ⟨83490, by rfl⟩) R166981
theorem R124355 : Reach 124355 := rs (se 1 (by rfl) ⟨93266, by rfl⟩) R186533
theorem R91649 : Reach 91649 := rs (se 2 (by rfl) ⟨34368, by rfl⟩) R68737
theorem R190019 : Reach 190019 := rs (se 1 (by rfl) ⟨142514, by rfl⟩) R285029
theorem R91729 : Reach 91729 := rs (se 2 (by rfl) ⟨34398, by rfl⟩) R68797
theorem R157457 : Reach 157457 := rs (se 2 (by rfl) ⟨59046, by rfl⟩) R118093
theorem R91955 : Reach 91955 := rs (se 1 (by rfl) ⟨68966, by rfl⟩) R137933
theorem R681797 : Reach 681797 := rs (se 4 (by rfl) ⟨63918, by rfl⟩) R127837
theorem R419717 : Reach 419717 := rs (se 4 (by rfl) ⟨39348, by rfl⟩) R78697
theorem R223181 : Reach 223181 := rs (se 3 (by rfl) ⟨41846, by rfl⟩) R83693
theorem R223235 : Reach 223235 := rs (se 1 (by rfl) ⟨167426, by rfl⟩) R334853
theorem R157841 : Reach 157841 := rs (se 2 (by rfl) ⟨59190, by rfl⟩) R118381
theorem R223505 : Reach 223505 := rs (se 2 (by rfl) ⟨83814, by rfl⟩) R167629
theorem R92515 : Reach 92515 := rs (se 1 (by rfl) ⟨69386, by rfl⟩) R138773
theorem R125297 : Reach 125297 := rs (se 2 (by rfl) ⟨46986, by rfl⟩) R93973
theorem R191089 : Reach 191089 := rs (se 2 (by rfl) ⟨71658, by rfl⟩) R143317
theorem R191203 : Reach 191203 := rs (se 1 (by rfl) ⟨143402, by rfl⟩) R286805
theorem R223985 : Reach 223985 := rs (se 2 (by rfl) ⟨83994, by rfl⟩) R167989
theorem R92963 : Reach 92963 := rs (se 1 (by rfl) ⟨69722, by rfl⟩) R139445
theorem R224045 : Reach 224045 := rs (se 3 (by rfl) ⟨42008, by rfl⟩) R84017
theorem R92993 : Reach 92993 := rs (se 2 (by rfl) ⟨34872, by rfl⟩) R69745
theorem R224099 : Reach 224099 := rs (se 1 (by rfl) ⟨168074, by rfl⟩) R336149
theorem R355205 : Reach 355205 := rs (se 4 (by rfl) ⟨33300, by rfl⟩) R66601
theorem R93107 : Reach 93107 := rs (se 1 (by rfl) ⟨69830, by rfl⟩) R139661
theorem R93187 : Reach 93187 := rs (se 1 (by rfl) ⟨69890, by rfl⟩) R139781
theorem R224369 : Reach 224369 := rs (se 2 (by rfl) ⟨84138, by rfl⟩) R168277
theorem R126193 : Reach 126193 := rs (se 2 (by rfl) ⟨47322, by rfl⟩) R94645
theorem R322865 : Reach 322865 := rs (se 2 (by rfl) ⟨121074, by rfl⟩) R242149
theorem R355661 : Reach 355661 := rs (se 3 (by rfl) ⟨66686, by rfl⟩) R133373
theorem R617827 : Reach 617827 := rs (se 1 (by rfl) ⟨463370, by rfl⟩) R926741
theorem R126353 : Reach 126353 := rs (se 2 (by rfl) ⟨47382, by rfl⟩) R94765
theorem R650693 : Reach 650693 := rs (se 4 (by rfl) ⟨61002, by rfl⟩) R122005
theorem R93745 : Reach 93745 := rs (se 2 (by rfl) ⟨35154, by rfl⟩) R70309
theorem R224909 : Reach 224909 := rs (se 3 (by rfl) ⟨42170, by rfl⟩) R84341
theorem R93889 : Reach 93889 := rs (se 2 (by rfl) ⟨35208, by rfl⟩) R70417
theorem R126755 : Reach 126755 := rs (se 1 (by rfl) ⟨95066, by rfl⟩) R190133
theorem R716597 : Reach 716597 := rs (se 5 (by rfl) ⟨33590, by rfl⟩) R67181
theorem R749411 : Reach 749411 := rs (se 1 (by rfl) ⟨562058, by rfl⟩) R1124117
theorem R946403 : Reach 946403 := rs (se 1 (by rfl) ⟨709802, by rfl⟩) R1419605
theorem R94451 : Reach 94451 := rs (se 1 (by rfl) ⟨70838, by rfl⟩) R141677
theorem R160177 : Reach 160177 := rs (se 2 (by rfl) ⟨60066, by rfl⟩) R120133
theorem R94691 : Reach 94691 := rs (se 1 (by rfl) ⟨71018, by rfl⟩) R142037
theorem R94721 : Reach 94721 := rs (se 2 (by rfl) ⟨35520, by rfl⟩) R71041
theorem R94739 : Reach 94739 := rs (se 1 (by rfl) ⟨71054, by rfl⟩) R142109
theorem R225827 : Reach 225827 := rs (se 1 (by rfl) ⟨169370, by rfl⟩) R338741
theorem R94769 : Reach 94769 := rs (se 2 (by rfl) ⟨35538, by rfl⟩) R71077
theorem R94787 : Reach 94787 := rs (se 1 (by rfl) ⟨71090, by rfl⟩) R142181
theorem R127555 : Reach 127555 := rs (se 1 (by rfl) ⟨95666, by rfl⟩) R191333
theorem R94817 : Reach 94817 := rs (se 2 (by rfl) ⟨35556, by rfl⟩) R71113
theorem R356977 : Reach 356977 := rs (se 2 (by rfl) ⟨133866, by rfl⟩) R267733
theorem R94835 : Reach 94835 := rs (se 1 (by rfl) ⟨71126, by rfl⟩) R142253
theorem R94865 : Reach 94865 := rs (se 2 (by rfl) ⟨35574, by rfl⟩) R71149
theorem R94883 : Reach 94883 := rs (se 1 (by rfl) ⟨71162, by rfl⟩) R142325
theorem R94913 : Reach 94913 := rs (se 2 (by rfl) ⟨35592, by rfl⟩) R71185
theorem R160451 : Reach 160451 := rs (se 1 (by rfl) ⟨120338, by rfl⟩) R240677
theorem R94931 : Reach 94931 := rs (se 1 (by rfl) ⟨71198, by rfl⟩) R142397
theorem R324323 : Reach 324323 := rs (se 1 (by rfl) ⟨243242, by rfl⟩) R486485
theorem R160483 : Reach 160483 := rs (se 1 (by rfl) ⟨120362, by rfl⟩) R240725
theorem R94961 : Reach 94961 := rs (se 2 (by rfl) ⟨35610, by rfl⟩) R71221
theorem R94979 : Reach 94979 := rs (se 1 (by rfl) ⟨71234, by rfl⟩) R142469
theorem R95009 : Reach 95009 := rs (se 2 (by rfl) ⟨35628, by rfl⟩) R71257
theorem R127793 : Reach 127793 := rs (se 2 (by rfl) ⟨47922, by rfl⟩) R95845
theorem R226097 : Reach 226097 := rs (se 2 (by rfl) ⟨84786, by rfl⟩) R169573
theorem R95027 : Reach 95027 := rs (se 1 (by rfl) ⟨71270, by rfl⟩) R142541
theorem R95057 : Reach 95057 := rs (se 2 (by rfl) ⟨35646, by rfl⟩) R71293
theorem R95075 : Reach 95075 := rs (se 1 (by rfl) ⟨71306, by rfl⟩) R142613
theorem R95089 : Reach 95089 := rs (se 2 (by rfl) ⟨35658, by rfl⟩) R71317
theorem R95105 : Reach 95105 := rs (se 2 (by rfl) ⟨35664, by rfl⟩) R71329
theorem R160643 : Reach 160643 := rs (se 1 (by rfl) ⟨120482, by rfl⟩) R240965
theorem R95123 : Reach 95123 := rs (se 1 (by rfl) ⟨71342, by rfl⟩) R142685
theorem R95153 : Reach 95153 := rs (se 2 (by rfl) ⟨35682, by rfl⟩) R71365
theorem R95171 : Reach 95171 := rs (se 1 (by rfl) ⟨71378, by rfl⟩) R142757
theorem R95201 : Reach 95201 := rs (se 2 (by rfl) ⟨35700, by rfl⟩) R71401
theorem R95203 : Reach 95203 := rs (se 1 (by rfl) ⟨71402, by rfl⟩) R142805
theorem R95219 : Reach 95219 := rs (se 1 (by rfl) ⟨71414, by rfl⟩) R142829
theorem R95249 : Reach 95249 := rs (se 2 (by rfl) ⟨35718, by rfl⟩) R71437
theorem R95267 : Reach 95267 := rs (se 1 (by rfl) ⟨71450, by rfl⟩) R142901
theorem R95297 : Reach 95297 := rs (se 2 (by rfl) ⟨35736, by rfl⟩) R71473
theorem R422981 : Reach 422981 := rs (se 4 (by rfl) ⟨39654, by rfl⟩) R79309
theorem R95315 : Reach 95315 := rs (se 1 (by rfl) ⟨71486, by rfl⟩) R142973
theorem R95345 : Reach 95345 := rs (se 2 (by rfl) ⟨35754, by rfl⟩) R71509
theorem R95363 : Reach 95363 := rs (se 1 (by rfl) ⟨71522, by rfl⟩) R143045
theorem R95393 : Reach 95393 := rs (se 2 (by rfl) ⟨35772, by rfl⟩) R71545
theorem R95411 : Reach 95411 := rs (se 1 (by rfl) ⟨71558, by rfl⟩) R143117
theorem R95441 : Reach 95441 := rs (se 2 (by rfl) ⟨35790, by rfl⟩) R71581
theorem R193745 : Reach 193745 := rs (se 2 (by rfl) ⟨72654, by rfl⟩) R145309
theorem R95459 : Reach 95459 := rs (se 1 (by rfl) ⟨71594, by rfl⟩) R143189
theorem R95489 : Reach 95489 := rs (se 2 (by rfl) ⟨35808, by rfl⟩) R71617
theorem R161041 : Reach 161041 := rs (se 2 (by rfl) ⟨60390, by rfl⟩) R120781
theorem R95507 : Reach 95507 := rs (se 1 (by rfl) ⟨71630, by rfl⟩) R143261
theorem R95537 : Reach 95537 := rs (se 2 (by rfl) ⟨35826, by rfl⟩) R71653
theorem R95555 : Reach 95555 := rs (se 1 (by rfl) ⟨71666, by rfl⟩) R143333
theorem R95585 : Reach 95585 := rs (se 2 (by rfl) ⟨35844, by rfl⟩) R71689
theorem R521585 : Reach 521585 := rs (se 2 (by rfl) ⟨195594, by rfl⟩) R391189
theorem R95603 : Reach 95603 := rs (se 1 (by rfl) ⟨71702, by rfl⟩) R143405
theorem R95633 : Reach 95633 := rs (se 2 (by rfl) ⟨35862, by rfl⟩) R71725
theorem R95651 : Reach 95651 := rs (se 1 (by rfl) ⟨71738, by rfl⟩) R143477
theorem R95681 : Reach 95681 := rs (se 2 (by rfl) ⟨35880, by rfl⟩) R71761
theorem R95699 : Reach 95699 := rs (se 1 (by rfl) ⟨71774, by rfl⟩) R143549
theorem R95729 : Reach 95729 := rs (se 2 (by rfl) ⟨35898, by rfl⟩) R71797
theorem R95747 : Reach 95747 := rs (se 1 (by rfl) ⟨71810, by rfl⟩) R143621
theorem R325133 : Reach 325133 := rs (se 3 (by rfl) ⟨60962, by rfl⟩) R121925
theorem R95777 : Reach 95777 := rs (se 2 (by rfl) ⟨35916, by rfl⟩) R71833
theorem R95795 : Reach 95795 := rs (se 1 (by rfl) ⟨71846, by rfl⟩) R143693
theorem R95825 : Reach 95825 := rs (se 2 (by rfl) ⟨35934, by rfl⟩) R71869
theorem R95843 : Reach 95843 := rs (se 1 (by rfl) ⟨71882, by rfl⟩) R143765
theorem R95873 : Reach 95873 := rs (se 2 (by rfl) ⟨35952, by rfl⟩) R71905
theorem R63123 : Reach 63123 := rs (se 1 (by rfl) ⟨47342, by rfl⟩) R94685
theorem R95891 : Reach 95891 := rs (se 1 (by rfl) ⟨71918, by rfl⟩) R143837
theorem R63139 : Reach 63139 := rs (se 1 (by rfl) ⟨47354, by rfl⟩) R94709
theorem R95921 : Reach 95921 := rs (se 2 (by rfl) ⟨35970, by rfl⟩) R71941
theorem R63155 : Reach 63155 := rs (se 1 (by rfl) ⟨47366, by rfl⟩) R94733
theorem R63171 : Reach 63171 := rs (se 1 (by rfl) ⟨47378, by rfl⟩) R94757
theorem R95939 : Reach 95939 := rs (se 1 (by rfl) ⟨71954, by rfl⟩) R143909
theorem R63187 : Reach 63187 := rs (se 1 (by rfl) ⟨47390, by rfl⟩) R94781
theorem R95969 : Reach 95969 := rs (se 2 (by rfl) ⟨35988, by rfl⟩) R71977
theorem R63203 : Reach 63203 := rs (se 1 (by rfl) ⟨47402, by rfl⟩) R94805
theorem R849649 : Reach 849649 := rs (se 2 (by rfl) ⟨318618, by rfl⟩) R637237
theorem R63219 : Reach 63219 := rs (se 1 (by rfl) ⟨47414, by rfl⟩) R94829
theorem R95987 : Reach 95987 := rs (se 1 (by rfl) ⟨71990, by rfl⟩) R143981
theorem R63235 : Reach 63235 := rs (se 1 (by rfl) ⟨47426, by rfl⟩) R94853
theorem R96017 : Reach 96017 := rs (se 2 (by rfl) ⟨36006, by rfl⟩) R72013
theorem R63251 : Reach 63251 := rs (se 1 (by rfl) ⟨47438, by rfl⟩) R94877
theorem R63267 : Reach 63267 := rs (se 1 (by rfl) ⟨47450, by rfl⟩) R94901
theorem R96035 : Reach 96035 := rs (se 1 (by rfl) ⟨72026, by rfl⟩) R144053
theorem R161585 : Reach 161585 := rs (se 2 (by rfl) ⟨60594, by rfl⟩) R121189
theorem R63283 : Reach 63283 := rs (se 1 (by rfl) ⟨47462, by rfl⟩) R94925
theorem R96065 : Reach 96065 := rs (se 2 (by rfl) ⟨36024, by rfl⟩) R72049
theorem R63299 : Reach 63299 := rs (se 1 (by rfl) ⟨47474, by rfl⟩) R94949
theorem R63315 : Reach 63315 := rs (se 1 (by rfl) ⟨47486, by rfl⟩) R94973
theorem R96083 : Reach 96083 := rs (se 1 (by rfl) ⟨72062, by rfl⟩) R144125
theorem R63331 : Reach 63331 := rs (se 1 (by rfl) ⟨47498, by rfl⟩) R94997
theorem R161635 : Reach 161635 := rs (se 1 (by rfl) ⟨121226, by rfl⟩) R242453
theorem R96113 : Reach 96113 := rs (se 2 (by rfl) ⟨36042, by rfl⟩) R72085
theorem R63347 : Reach 63347 := rs (se 1 (by rfl) ⟨47510, by rfl⟩) R95021
theorem R63363 : Reach 63363 := rs (se 1 (by rfl) ⟨47522, by rfl⟩) R95045
theorem R96131 : Reach 96131 := rs (se 1 (by rfl) ⟨72098, by rfl⟩) R144197
theorem R63379 : Reach 63379 := rs (se 1 (by rfl) ⟨47534, by rfl⟩) R95069
theorem R96161 : Reach 96161 := rs (se 2 (by rfl) ⟨36060, by rfl⟩) R72121
theorem R63395 : Reach 63395 := rs (se 1 (by rfl) ⟨47546, by rfl⟩) R95093
theorem R63411 : Reach 63411 := rs (se 1 (by rfl) ⟨47558, by rfl⟩) R95117
theorem R96179 : Reach 96179 := rs (se 1 (by rfl) ⟨72134, by rfl⟩) R144269
theorem R63427 : Reach 63427 := rs (se 1 (by rfl) ⟨47570, by rfl⟩) R95141
theorem R96209 : Reach 96209 := rs (se 2 (by rfl) ⟨36078, by rfl⟩) R72157
theorem R63443 : Reach 63443 := rs (se 1 (by rfl) ⟨47582, by rfl⟩) R95165
theorem R63459 : Reach 63459 := rs (se 1 (by rfl) ⟨47594, by rfl⟩) R95189
theorem R96227 : Reach 96227 := rs (se 1 (by rfl) ⟨72170, by rfl⟩) R144341
theorem R161777 : Reach 161777 := rs (se 2 (by rfl) ⟨60666, by rfl⟩) R121333
theorem R63475 : Reach 63475 := rs (se 1 (by rfl) ⟨47606, by rfl⟩) R95213
theorem R96257 : Reach 96257 := rs (se 2 (by rfl) ⟨36096, by rfl⟩) R72193
theorem R63491 : Reach 63491 := rs (se 1 (by rfl) ⟨47618, by rfl⟩) R95237
theorem R63507 : Reach 63507 := rs (se 1 (by rfl) ⟨47630, by rfl⟩) R95261
theorem R96275 : Reach 96275 := rs (se 1 (by rfl) ⟨72206, by rfl⟩) R144413
theorem R63523 : Reach 63523 := rs (se 1 (by rfl) ⟨47642, by rfl⟩) R95285
theorem R96305 : Reach 96305 := rs (se 2 (by rfl) ⟨36114, by rfl⟩) R72229
theorem R63539 : Reach 63539 := rs (se 1 (by rfl) ⟨47654, by rfl⟩) R95309
theorem R63555 : Reach 63555 := rs (se 1 (by rfl) ⟨47666, by rfl⟩) R95333
theorem R96323 : Reach 96323 := rs (se 1 (by rfl) ⟨72242, by rfl⟩) R144485
theorem R63571 : Reach 63571 := rs (se 1 (by rfl) ⟨47678, by rfl⟩) R95357
theorem R96353 : Reach 96353 := rs (se 2 (by rfl) ⟨36132, by rfl⟩) R72265
theorem R63587 : Reach 63587 := rs (se 1 (by rfl) ⟨47690, by rfl⟩) R95381
theorem R63603 : Reach 63603 := rs (se 1 (by rfl) ⟨47702, by rfl⟩) R95405
theorem R96371 : Reach 96371 := rs (se 1 (by rfl) ⟨72278, by rfl⟩) R144557
theorem R63619 : Reach 63619 := rs (se 1 (by rfl) ⟨47714, by rfl⟩) R95429
theorem R96401 : Reach 96401 := rs (se 2 (by rfl) ⟨36150, by rfl⟩) R72301
theorem R63635 : Reach 63635 := rs (se 1 (by rfl) ⟨47726, by rfl⟩) R95453
theorem R63651 : Reach 63651 := rs (se 1 (by rfl) ⟨47738, by rfl⟩) R95477
theorem R96419 : Reach 96419 := rs (se 1 (by rfl) ⟨72314, by rfl⟩) R144629
theorem R260273 : Reach 260273 := rs (se 2 (by rfl) ⟨97602, by rfl⟩) R195205
theorem R63667 : Reach 63667 := rs (se 1 (by rfl) ⟨47750, by rfl⟩) R95501
theorem R96433 : Reach 96433 := rs (se 2 (by rfl) ⟨36162, by rfl⟩) R72325
theorem R96449 : Reach 96449 := rs (se 2 (by rfl) ⟨36168, by rfl⟩) R72337
theorem R63683 : Reach 63683 := rs (se 1 (by rfl) ⟨47762, by rfl⟩) R95525
theorem R63699 : Reach 63699 := rs (se 1 (by rfl) ⟨47774, by rfl⟩) R95549
theorem R96467 : Reach 96467 := rs (se 1 (by rfl) ⟨72350, by rfl⟩) R144701
theorem R63715 : Reach 63715 := rs (se 1 (by rfl) ⟨47786, by rfl⟩) R95573
theorem R96497 : Reach 96497 := rs (se 2 (by rfl) ⟨36186, by rfl⟩) R72373
theorem R63731 : Reach 63731 := rs (se 1 (by rfl) ⟨47798, by rfl⟩) R95597
theorem R63747 : Reach 63747 := rs (se 1 (by rfl) ⟨47810, by rfl⟩) R95621
theorem R96515 : Reach 96515 := rs (se 1 (by rfl) ⟨72386, by rfl⟩) R144773
theorem R63763 : Reach 63763 := rs (se 1 (by rfl) ⟨47822, by rfl⟩) R95645
theorem R96545 : Reach 96545 := rs (se 2 (by rfl) ⟨36204, by rfl⟩) R72409
theorem R63779 : Reach 63779 := rs (se 1 (by rfl) ⟨47834, by rfl⟩) R95669
theorem R63795 : Reach 63795 := rs (se 1 (by rfl) ⟨47846, by rfl⟩) R95693
theorem R96563 : Reach 96563 := rs (se 1 (by rfl) ⟨72422, by rfl⟩) R144845
theorem R63811 : Reach 63811 := rs (se 1 (by rfl) ⟨47858, by rfl⟩) R95717
theorem R96593 : Reach 96593 := rs (se 2 (by rfl) ⟨36222, by rfl⟩) R72445
theorem R63827 : Reach 63827 := rs (se 1 (by rfl) ⟨47870, by rfl⟩) R95741
theorem R63843 : Reach 63843 := rs (se 1 (by rfl) ⟨47882, by rfl⟩) R95765
theorem R96611 : Reach 96611 := rs (se 1 (by rfl) ⟨72458, by rfl⟩) R144917
theorem R63859 : Reach 63859 := rs (se 1 (by rfl) ⟨47894, by rfl⟩) R95789
theorem R63875 : Reach 63875 := rs (se 1 (by rfl) ⟨47906, by rfl⟩) R95813
theorem R96641 : Reach 96641 := rs (se 2 (by rfl) ⟨36240, by rfl⟩) R72481
theorem R63891 : Reach 63891 := rs (se 1 (by rfl) ⟨47918, by rfl⟩) R95837
theorem R96659 : Reach 96659 := rs (se 1 (by rfl) ⟨72494, by rfl⟩) R144989
theorem R63907 : Reach 63907 := rs (se 1 (by rfl) ⟨47930, by rfl⟩) R95861
theorem R96689 : Reach 96689 := rs (se 2 (by rfl) ⟨36258, by rfl⟩) R72517
theorem R63923 : Reach 63923 := rs (se 1 (by rfl) ⟨47942, by rfl⟩) R95885
theorem R63939 : Reach 63939 := rs (se 1 (by rfl) ⟨47954, by rfl⟩) R95909
theorem R195011 : Reach 195011 := rs (se 1 (by rfl) ⟨146258, by rfl⟩) R292517
theorem R96707 : Reach 96707 := rs (se 1 (by rfl) ⟨72530, by rfl⟩) R145061
theorem R63955 : Reach 63955 := rs (se 1 (by rfl) ⟨47966, by rfl⟩) R95933
theorem R96737 : Reach 96737 := rs (se 2 (by rfl) ⟨36276, by rfl⟩) R72553
theorem R63971 : Reach 63971 := rs (se 1 (by rfl) ⟨47978, by rfl⟩) R95957
theorem R63987 : Reach 63987 := rs (se 1 (by rfl) ⟨47990, by rfl⟩) R95981
theorem R96755 : Reach 96755 := rs (se 1 (by rfl) ⟨72566, by rfl⟩) R145133
theorem R64003 : Reach 64003 := rs (se 1 (by rfl) ⟨48002, by rfl⟩) R96005
theorem R96785 : Reach 96785 := rs (se 2 (by rfl) ⟨36294, by rfl⟩) R72589
theorem R64019 : Reach 64019 := rs (se 1 (by rfl) ⟨48014, by rfl⟩) R96029
theorem R64035 : Reach 64035 := rs (se 1 (by rfl) ⟨48026, by rfl⟩) R96053
theorem R96803 : Reach 96803 := rs (se 1 (by rfl) ⟨72602, by rfl⟩) R145205
theorem R64051 : Reach 64051 := rs (se 1 (by rfl) ⟨48038, by rfl⟩) R96077
theorem R96833 : Reach 96833 := rs (se 2 (by rfl) ⟨36312, by rfl⟩) R72625
theorem R64067 : Reach 64067 := rs (se 1 (by rfl) ⟨48050, by rfl⟩) R96101
theorem R64083 : Reach 64083 := rs (se 1 (by rfl) ⟨48062, by rfl⟩) R96125
theorem R96851 : Reach 96851 := rs (se 1 (by rfl) ⟨72638, by rfl⟩) R145277
theorem R64099 : Reach 64099 := rs (se 1 (by rfl) ⟨48074, by rfl⟩) R96149
theorem R96881 : Reach 96881 := rs (se 2 (by rfl) ⟨36330, by rfl⟩) R72661
theorem R64115 : Reach 64115 := rs (se 1 (by rfl) ⟨48086, by rfl⟩) R96173
theorem R64131 : Reach 64131 := rs (se 1 (by rfl) ⟨48098, by rfl⟩) R96197
theorem R96899 : Reach 96899 := rs (se 1 (by rfl) ⟨72674, by rfl⟩) R145349
theorem R64147 : Reach 64147 := rs (se 1 (by rfl) ⟨48110, by rfl⟩) R96221
theorem R96929 : Reach 96929 := rs (se 2 (by rfl) ⟨36348, by rfl⟩) R72697
theorem R64163 : Reach 64163 := rs (se 1 (by rfl) ⟨48122, by rfl⟩) R96245
theorem R64179 : Reach 64179 := rs (se 1 (by rfl) ⟨48134, by rfl⟩) R96269
theorem R96947 : Reach 96947 := rs (se 1 (by rfl) ⟨72710, by rfl⟩) R145421
theorem R64195 : Reach 64195 := rs (se 1 (by rfl) ⟨48146, by rfl⟩) R96293
theorem R96977 : Reach 96977 := rs (se 2 (by rfl) ⟨36366, by rfl⟩) R72733
theorem R64211 : Reach 64211 := rs (se 1 (by rfl) ⟨48158, by rfl⟩) R96317
theorem R64227 : Reach 64227 := rs (se 1 (by rfl) ⟨48170, by rfl⟩) R96341
theorem R96995 : Reach 96995 := rs (se 1 (by rfl) ⟨72746, by rfl⟩) R145493
theorem R64243 : Reach 64243 := rs (se 1 (by rfl) ⟨48182, by rfl⟩) R96365
theorem R97025 : Reach 97025 := rs (se 2 (by rfl) ⟨36384, by rfl⟩) R72769
theorem R64259 : Reach 64259 := rs (se 1 (by rfl) ⟨48194, by rfl⟩) R96389
theorem R64275 : Reach 64275 := rs (se 1 (by rfl) ⟨48206, by rfl⟩) R96413
theorem R97043 : Reach 97043 := rs (se 1 (by rfl) ⟨72782, by rfl⟩) R145565
theorem R64291 : Reach 64291 := rs (se 1 (by rfl) ⟨48218, by rfl⟩) R96437
theorem R97073 : Reach 97073 := rs (se 2 (by rfl) ⟨36402, by rfl⟩) R72805
theorem R64307 : Reach 64307 := rs (se 1 (by rfl) ⟨48230, by rfl⟩) R96461
theorem R64323 : Reach 64323 := rs (se 1 (by rfl) ⟨48242, by rfl⟩) R96485
theorem R97091 : Reach 97091 := rs (se 1 (by rfl) ⟨72818, by rfl⟩) R145637
theorem R64339 : Reach 64339 := rs (se 1 (by rfl) ⟨48254, by rfl⟩) R96509
theorem R97121 : Reach 97121 := rs (se 2 (by rfl) ⟨36420, by rfl⟩) R72841
theorem R64355 : Reach 64355 := rs (se 1 (by rfl) ⟨48266, by rfl⟩) R96533
theorem R64371 : Reach 64371 := rs (se 1 (by rfl) ⟨48278, by rfl⟩) R96557
theorem R97139 : Reach 97139 := rs (se 1 (by rfl) ⟨72854, by rfl⟩) R145709
theorem R64387 : Reach 64387 := rs (se 1 (by rfl) ⟨48290, by rfl⟩) R96581
theorem R97169 : Reach 97169 := rs (se 2 (by rfl) ⟨36438, by rfl⟩) R72877
theorem R64403 : Reach 64403 := rs (se 1 (by rfl) ⟨48302, by rfl⟩) R96605
theorem R64419 : Reach 64419 := rs (se 1 (by rfl) ⟨48314, by rfl⟩) R96629
theorem R97187 : Reach 97187 := rs (se 1 (by rfl) ⟨72890, by rfl⟩) R145781
theorem R64435 : Reach 64435 := rs (se 1 (by rfl) ⟨48326, by rfl⟩) R96653
theorem R97217 : Reach 97217 := rs (se 2 (by rfl) ⟨36456, by rfl⟩) R72913
theorem R64451 : Reach 64451 := rs (se 1 (by rfl) ⟨48338, by rfl⟩) R96677
theorem R162769 : Reach 162769 := rs (se 2 (by rfl) ⟨61038, by rfl⟩) R122077
theorem R97235 : Reach 97235 := rs (se 1 (by rfl) ⟨72926, by rfl⟩) R145853
theorem R64467 : Reach 64467 := rs (se 1 (by rfl) ⟨48350, by rfl⟩) R96701
theorem R64483 : Reach 64483 := rs (se 1 (by rfl) ⟨48362, by rfl⟩) R96725
theorem R621553 : Reach 621553 := rs (se 2 (by rfl) ⟨233082, by rfl⟩) R466165
theorem R64499 : Reach 64499 := rs (se 1 (by rfl) ⟨48374, by rfl⟩) R96749
theorem R97265 : Reach 97265 := rs (se 2 (by rfl) ⟨36474, by rfl⟩) R72949
theorem R64515 : Reach 64515 := rs (se 1 (by rfl) ⟨48386, by rfl⟩) R96773
theorem R97283 : Reach 97283 := rs (se 1 (by rfl) ⟨72962, by rfl⟩) R145925
theorem R64531 : Reach 64531 := rs (se 1 (by rfl) ⟨48398, by rfl⟩) R96797
theorem R97313 : Reach 97313 := rs (se 2 (by rfl) ⟨36492, by rfl⟩) R72985
theorem R64547 : Reach 64547 := rs (se 1 (by rfl) ⟨48410, by rfl⟩) R96821
theorem R64563 : Reach 64563 := rs (se 1 (by rfl) ⟨48422, by rfl⟩) R96845
theorem R97331 : Reach 97331 := rs (se 1 (by rfl) ⟨72998, by rfl⟩) R145997
theorem R64579 : Reach 64579 := rs (se 1 (by rfl) ⟨48434, by rfl⟩) R96869
theorem R97361 : Reach 97361 := rs (se 2 (by rfl) ⟨36510, by rfl⟩) R73021
theorem R64595 : Reach 64595 := rs (se 1 (by rfl) ⟨48446, by rfl⟩) R96893
theorem R64611 : Reach 64611 := rs (se 1 (by rfl) ⟨48458, by rfl⟩) R96917
theorem R97379 : Reach 97379 := rs (se 1 (by rfl) ⟨73034, by rfl⟩) R146069
theorem R64627 : Reach 64627 := rs (se 1 (by rfl) ⟨48470, by rfl⟩) R96941
theorem R97409 : Reach 97409 := rs (se 2 (by rfl) ⟨36528, by rfl⟩) R73057
theorem R64643 : Reach 64643 := rs (se 1 (by rfl) ⟨48482, by rfl⟩) R96965
theorem R64659 : Reach 64659 := rs (se 1 (by rfl) ⟨48494, by rfl⟩) R96989
theorem R97427 : Reach 97427 := rs (se 1 (by rfl) ⟨73070, by rfl⟩) R146141
theorem R64675 : Reach 64675 := rs (se 1 (by rfl) ⟨48506, by rfl⟩) R97013
theorem R97457 : Reach 97457 := rs (se 2 (by rfl) ⟨36546, by rfl⟩) R73093
theorem R64691 : Reach 64691 := rs (se 1 (by rfl) ⟨48518, by rfl⟩) R97037
theorem R64707 : Reach 64707 := rs (se 1 (by rfl) ⟨48530, by rfl⟩) R97061
theorem R97475 : Reach 97475 := rs (se 1 (by rfl) ⟨73106, by rfl⟩) R146213
theorem R64723 : Reach 64723 := rs (se 1 (by rfl) ⟨48542, by rfl⟩) R97085
theorem R163043 : Reach 163043 := rs (se 1 (by rfl) ⟨122282, by rfl⟩) R244565
theorem R64739 : Reach 64739 := rs (se 1 (by rfl) ⟨48554, by rfl⟩) R97109
theorem R97505 : Reach 97505 := rs (se 2 (by rfl) ⟨36564, by rfl⟩) R73129
theorem R64755 : Reach 64755 := rs (se 1 (by rfl) ⟨48566, by rfl⟩) R97133
theorem R97523 : Reach 97523 := rs (se 1 (by rfl) ⟨73142, by rfl⟩) R146285
theorem R64771 : Reach 64771 := rs (se 1 (by rfl) ⟨48578, by rfl⟩) R97157
theorem R97553 : Reach 97553 := rs (se 2 (by rfl) ⟨36582, by rfl⟩) R73165
theorem R64787 : Reach 64787 := rs (se 1 (by rfl) ⟨48590, by rfl⟩) R97181
theorem R64803 : Reach 64803 := rs (se 1 (by rfl) ⟨48602, by rfl⟩) R97205
theorem R97571 : Reach 97571 := rs (se 1 (by rfl) ⟨73178, by rfl⟩) R146357
theorem R64819 : Reach 64819 := rs (se 1 (by rfl) ⟨48614, by rfl⟩) R97229
theorem R64835 : Reach 64835 := rs (se 1 (by rfl) ⟨48626, by rfl⟩) R97253
theorem R97601 : Reach 97601 := rs (se 2 (by rfl) ⟨36600, by rfl⟩) R73201
theorem R64851 : Reach 64851 := rs (se 1 (by rfl) ⟨48638, by rfl⟩) R97277
theorem R97619 : Reach 97619 := rs (se 1 (by rfl) ⟨73214, by rfl⟩) R146429
theorem R64867 : Reach 64867 := rs (se 1 (by rfl) ⟨48650, by rfl⟩) R97301
theorem R97649 : Reach 97649 := rs (se 2 (by rfl) ⟨36618, by rfl⟩) R73237
theorem R64883 : Reach 64883 := rs (se 1 (by rfl) ⟨48662, by rfl⟩) R97325
theorem R64899 : Reach 64899 := rs (se 1 (by rfl) ⟨48674, by rfl⟩) R97349
theorem R97667 : Reach 97667 := rs (se 1 (by rfl) ⟨73250, by rfl⟩) R146501
theorem R64915 : Reach 64915 := rs (se 1 (by rfl) ⟨48686, by rfl⟩) R97373
theorem R97697 : Reach 97697 := rs (se 2 (by rfl) ⟨36636, by rfl⟩) R73273
theorem R163235 : Reach 163235 := rs (se 1 (by rfl) ⟨122426, by rfl⟩) R244853
theorem R64931 : Reach 64931 := rs (se 1 (by rfl) ⟨48698, by rfl⟩) R97397
theorem R64947 : Reach 64947 := rs (se 1 (by rfl) ⟨48710, by rfl⟩) R97421
theorem R97715 : Reach 97715 := rs (se 1 (by rfl) ⟨73286, by rfl⟩) R146573
theorem R64963 : Reach 64963 := rs (se 1 (by rfl) ⟨48722, by rfl⟩) R97445
theorem R97745 : Reach 97745 := rs (se 2 (by rfl) ⟨36654, by rfl⟩) R73309
theorem R64979 : Reach 64979 := rs (se 1 (by rfl) ⟨48734, by rfl⟩) R97469
theorem R64995 : Reach 64995 := rs (se 1 (by rfl) ⟨48746, by rfl⟩) R97493
theorem R97763 : Reach 97763 := rs (se 1 (by rfl) ⟨73322, by rfl⟩) R146645
theorem R65011 : Reach 65011 := rs (se 1 (by rfl) ⟨48758, by rfl⟩) R97517
theorem R97793 : Reach 97793 := rs (se 2 (by rfl) ⟨36672, by rfl⟩) R73345
theorem R65027 : Reach 65027 := rs (se 1 (by rfl) ⟨48770, by rfl⟩) R97541
theorem R97811 : Reach 97811 := rs (se 1 (by rfl) ⟨73358, by rfl⟩) R146717
theorem R65043 : Reach 65043 := rs (se 1 (by rfl) ⟨48782, by rfl⟩) R97565
theorem R65059 : Reach 65059 := rs (se 1 (by rfl) ⟨48794, by rfl⟩) R97589
theorem R97841 : Reach 97841 := rs (se 2 (by rfl) ⟨36690, by rfl⟩) R73381
theorem R65075 : Reach 65075 := rs (se 1 (by rfl) ⟨48806, by rfl⟩) R97613
theorem R97859 : Reach 97859 := rs (se 1 (by rfl) ⟨73394, by rfl⟩) R146789
theorem R65091 : Reach 65091 := rs (se 1 (by rfl) ⟨48818, by rfl⟩) R97637
theorem R65107 : Reach 65107 := rs (se 1 (by rfl) ⟨48830, by rfl⟩) R97661
theorem R97889 : Reach 97889 := rs (se 2 (by rfl) ⟨36708, by rfl⟩) R73417
theorem R360035 : Reach 360035 := rs (se 1 (by rfl) ⟨270026, by rfl⟩) R540053
theorem R65123 : Reach 65123 := rs (se 1 (by rfl) ⟨48842, by rfl⟩) R97685
theorem R654961 : Reach 654961 := rs (se 2 (by rfl) ⟨245610, by rfl⟩) R491221
theorem R65139 : Reach 65139 := rs (se 1 (by rfl) ⟨48854, by rfl⟩) R97709
theorem R97907 : Reach 97907 := rs (se 1 (by rfl) ⟨73430, by rfl⟩) R146861
theorem R65155 : Reach 65155 := rs (se 1 (by rfl) ⟨48866, by rfl⟩) R97733
theorem R97937 : Reach 97937 := rs (se 2 (by rfl) ⟨36726, by rfl⟩) R73453
theorem R65171 : Reach 65171 := rs (se 1 (by rfl) ⟨48878, by rfl⟩) R97757
theorem R65187 : Reach 65187 := rs (se 1 (by rfl) ⟨48890, by rfl⟩) R97781
theorem R97955 : Reach 97955 := rs (se 1 (by rfl) ⟨73466, by rfl⟩) R146933
theorem R65203 : Reach 65203 := rs (se 1 (by rfl) ⟨48902, by rfl⟩) R97805
theorem R97985 : Reach 97985 := rs (se 2 (by rfl) ⟨36744, by rfl⟩) R73489
theorem R65219 : Reach 65219 := rs (se 1 (by rfl) ⟨48914, by rfl⟩) R97829
theorem R65235 : Reach 65235 := rs (se 1 (by rfl) ⟨48926, by rfl⟩) R97853
theorem R98003 : Reach 98003 := rs (se 1 (by rfl) ⟨73502, by rfl⟩) R147005
theorem R65251 : Reach 65251 := rs (se 1 (by rfl) ⟨48938, by rfl⟩) R97877
theorem R98033 : Reach 98033 := rs (se 2 (by rfl) ⟨36762, by rfl⟩) R73525
theorem R65267 : Reach 65267 := rs (se 1 (by rfl) ⟨48950, by rfl⟩) R97901
theorem R65283 : Reach 65283 := rs (se 1 (by rfl) ⟨48962, by rfl⟩) R97925
theorem R98051 : Reach 98051 := rs (se 1 (by rfl) ⟨73538, by rfl⟩) R147077
theorem R65299 : Reach 65299 := rs (se 1 (by rfl) ⟨48974, by rfl⟩) R97949
theorem R98081 : Reach 98081 := rs (se 2 (by rfl) ⟨36780, by rfl⟩) R73561
theorem R65315 : Reach 65315 := rs (se 1 (by rfl) ⟨48986, by rfl⟩) R97973
theorem R65331 : Reach 65331 := rs (se 1 (by rfl) ⟨48998, by rfl⟩) R97997
theorem R98099 : Reach 98099 := rs (se 1 (by rfl) ⟨73574, by rfl⟩) R147149
theorem R65347 : Reach 65347 := rs (se 1 (by rfl) ⟨49010, by rfl⟩) R98021
theorem R98129 : Reach 98129 := rs (se 2 (by rfl) ⟨36798, by rfl⟩) R73597
theorem R65363 : Reach 65363 := rs (se 1 (by rfl) ⟨49022, by rfl⟩) R98045
theorem R65379 : Reach 65379 := rs (se 1 (by rfl) ⟨49034, by rfl⟩) R98069
theorem R98147 : Reach 98147 := rs (se 1 (by rfl) ⟨73610, by rfl⟩) R147221
theorem R65395 : Reach 65395 := rs (se 1 (by rfl) ⟨49046, by rfl⟩) R98093
theorem R65411 : Reach 65411 := rs (se 1 (by rfl) ⟨49058, by rfl⟩) R98117
theorem R98177 : Reach 98177 := rs (se 2 (by rfl) ⟨36816, by rfl⟩) R73633
theorem R65427 : Reach 65427 := rs (se 1 (by rfl) ⟨49070, by rfl⟩) R98141
theorem R98195 : Reach 98195 := rs (se 1 (by rfl) ⟨73646, by rfl⟩) R147293
theorem R65443 : Reach 65443 := rs (se 1 (by rfl) ⟨49082, by rfl⟩) R98165
theorem R98225 : Reach 98225 := rs (se 2 (by rfl) ⟨36834, by rfl⟩) R73669
theorem R65459 : Reach 65459 := rs (se 1 (by rfl) ⟨49094, by rfl⟩) R98189
theorem R65475 : Reach 65475 := rs (se 1 (by rfl) ⟨49106, by rfl⟩) R98213
theorem R98243 : Reach 98243 := rs (se 1 (by rfl) ⟨73682, by rfl⟩) R147365
theorem R65491 : Reach 65491 := rs (se 1 (by rfl) ⟨49118, by rfl⟩) R98237
theorem R98273 : Reach 98273 := rs (se 2 (by rfl) ⟨36852, by rfl⟩) R73705
theorem R65507 : Reach 65507 := rs (se 1 (by rfl) ⟨49130, by rfl⟩) R98261
theorem R65523 : Reach 65523 := rs (se 1 (by rfl) ⟨49142, by rfl⟩) R98285
theorem R98291 : Reach 98291 := rs (se 1 (by rfl) ⟨73718, by rfl⟩) R147437
theorem R98315 : Reach 98315 := rs (se 1 (by rfl) ⟨73736, by rfl⟩) R147473
theorem R65547 : Reach 65547 := rs (se 1 (by rfl) ⟨49160, by rfl⟩) R98321
theorem R98327 : Reach 98327 := rs (se 1 (by rfl) ⟨73745, by rfl⟩) R147491
theorem R65559 : Reach 65559 := rs (se 1 (by rfl) ⟨49169, by rfl⟩) R98339
theorem R65579 : Reach 65579 := rs (se 1 (by rfl) ⟨49184, by rfl⟩) R98369
theorem R327725 : Reach 327725 := rs (se 3 (by rfl) ⟨61448, by rfl⟩) R122897
theorem R65591 : Reach 65591 := rs (se 1 (by rfl) ⟨49193, by rfl⟩) R98387
theorem R65611 : Reach 65611 := rs (se 1 (by rfl) ⟨49208, by rfl⟩) R98417
theorem R65623 : Reach 65623 := rs (se 1 (by rfl) ⟨49217, by rfl⟩) R98435
theorem R98393 : Reach 98393 := rs (se 2 (by rfl) ⟨36897, by rfl⟩) R73795
theorem R65643 : Reach 65643 := rs (se 1 (by rfl) ⟨49232, by rfl⟩) R98465
theorem R65655 : Reach 65655 := rs (se 1 (by rfl) ⟨49241, by rfl⟩) R98483
theorem R65675 : Reach 65675 := rs (se 1 (by rfl) ⟨49256, by rfl⟩) R98513
theorem R65687 : Reach 65687 := rs (se 1 (by rfl) ⟨49265, by rfl⟩) R98531
theorem R65707 : Reach 65707 := rs (se 1 (by rfl) ⟨49280, by rfl⟩) R98561
theorem R65719 : Reach 65719 := rs (se 1 (by rfl) ⟨49289, by rfl⟩) R98579
theorem R98507 : Reach 98507 := rs (se 1 (by rfl) ⟨73880, by rfl⟩) R147761
theorem R65739 : Reach 65739 := rs (se 1 (by rfl) ⟨49304, by rfl⟩) R98609
theorem R98519 : Reach 98519 := rs (se 1 (by rfl) ⟨73889, by rfl⟩) R147779
theorem R65751 : Reach 65751 := rs (se 1 (by rfl) ⟨49313, by rfl⟩) R98627
theorem R65771 : Reach 65771 := rs (se 1 (by rfl) ⟨49328, by rfl⟩) R98657
theorem R65783 : Reach 65783 := rs (se 1 (by rfl) ⟨49337, by rfl⟩) R98675
theorem R65803 : Reach 65803 := rs (se 1 (by rfl) ⟨49352, by rfl⟩) R98705
theorem R65815 : Reach 65815 := rs (se 1 (by rfl) ⟨49361, by rfl⟩) R98723
theorem R98585 : Reach 98585 := rs (se 2 (by rfl) ⟨36969, by rfl⟩) R73939
theorem R65835 : Reach 65835 := rs (se 1 (by rfl) ⟨49376, by rfl⟩) R98753
theorem R65847 : Reach 65847 := rs (se 1 (by rfl) ⟨49385, by rfl⟩) R98771
theorem R65867 : Reach 65867 := rs (se 1 (by rfl) ⟨49400, by rfl⟩) R98801
theorem R65879 : Reach 65879 := rs (se 1 (by rfl) ⟨49409, by rfl⟩) R98819
theorem R65899 : Reach 65899 := rs (se 1 (by rfl) ⟨49424, by rfl⟩) R98849
theorem R65911 : Reach 65911 := rs (se 1 (by rfl) ⟨49433, by rfl⟩) R98867
theorem R98699 : Reach 98699 := rs (se 1 (by rfl) ⟨74024, by rfl⟩) R148049
theorem R65931 : Reach 65931 := rs (se 1 (by rfl) ⟨49448, by rfl⟩) R98897
theorem R98711 : Reach 98711 := rs (se 1 (by rfl) ⟨74033, by rfl⟩) R148067
theorem R65943 : Reach 65943 := rs (se 1 (by rfl) ⟨49457, by rfl⟩) R98915
theorem R65963 : Reach 65963 := rs (se 1 (by rfl) ⟨49472, by rfl⟩) R98945
theorem R65975 : Reach 65975 := rs (se 1 (by rfl) ⟨49481, by rfl⟩) R98963
theorem R65995 : Reach 65995 := rs (se 1 (by rfl) ⟨49496, by rfl⟩) R98993
theorem R66007 : Reach 66007 := rs (se 1 (by rfl) ⟨49505, by rfl⟩) R99011
theorem R197081 : Reach 197081 := rs (se 2 (by rfl) ⟨73905, by rfl⟩) R147811
theorem R98777 : Reach 98777 := rs (se 2 (by rfl) ⟨37041, by rfl⟩) R74083
theorem R66027 : Reach 66027 := rs (se 1 (by rfl) ⟨49520, by rfl⟩) R99041
theorem R66039 : Reach 66039 := rs (se 1 (by rfl) ⟨49529, by rfl⟩) R99059
theorem R66059 : Reach 66059 := rs (se 1 (by rfl) ⟨49544, by rfl⟩) R99089
theorem R66071 : Reach 66071 := rs (se 1 (by rfl) ⟨49553, by rfl⟩) R99107
theorem R557603 : Reach 557603 := rs (se 1 (by rfl) ⟨418202, by rfl⟩) R836405
theorem R66091 : Reach 66091 := rs (se 1 (by rfl) ⟨49568, by rfl⟩) R99137
theorem R66103 : Reach 66103 := rs (se 1 (by rfl) ⟨49577, by rfl⟩) R99155
theorem R98891 : Reach 98891 := rs (se 1 (by rfl) ⟨74168, by rfl⟩) R148337
theorem R66123 : Reach 66123 := rs (se 1 (by rfl) ⟨49592, by rfl⟩) R99185
theorem R98903 : Reach 98903 := rs (se 1 (by rfl) ⟨74177, by rfl⟩) R148355
theorem R66135 : Reach 66135 := rs (se 1 (by rfl) ⟨49601, by rfl⟩) R99203
theorem R66155 : Reach 66155 := rs (se 1 (by rfl) ⟨49616, by rfl⟩) R99233
theorem R66167 : Reach 66167 := rs (se 1 (by rfl) ⟨49625, by rfl⟩) R99251
theorem R66187 : Reach 66187 := rs (se 1 (by rfl) ⟨49640, by rfl⟩) R99281
theorem R66199 : Reach 66199 := rs (se 1 (by rfl) ⟨49649, by rfl⟩) R99299
theorem R426647 : Reach 426647 := rs (se 1 (by rfl) ⟨319985, by rfl⟩) R639971
theorem R98969 : Reach 98969 := rs (se 2 (by rfl) ⟨37113, by rfl⟩) R74227
theorem R66219 : Reach 66219 := rs (se 1 (by rfl) ⟨49664, by rfl⟩) R99329
theorem R164531 : Reach 164531 := rs (se 1 (by rfl) ⟨123398, by rfl⟩) R246797
theorem R66231 : Reach 66231 := rs (se 1 (by rfl) ⟨49673, by rfl⟩) R99347
theorem R66251 : Reach 66251 := rs (se 1 (by rfl) ⟨49688, by rfl⟩) R99377
theorem R66263 : Reach 66263 := rs (se 1 (by rfl) ⟨49697, by rfl⟩) R99395
theorem R66283 : Reach 66283 := rs (se 1 (by rfl) ⟨49712, by rfl⟩) R99425
theorem R66295 : Reach 66295 := rs (se 1 (by rfl) ⟨49721, by rfl⟩) R99443
theorem R99083 : Reach 99083 := rs (se 1 (by rfl) ⟨74312, by rfl⟩) R148625
theorem R66315 : Reach 66315 := rs (se 1 (by rfl) ⟨49736, by rfl⟩) R99473
theorem R99095 : Reach 99095 := rs (se 1 (by rfl) ⟨74321, by rfl⟩) R148643
theorem R66327 : Reach 66327 := rs (se 1 (by rfl) ⟨49745, by rfl⟩) R99491
theorem R66347 : Reach 66347 := rs (se 1 (by rfl) ⟨49760, by rfl⟩) R99521
theorem R721709 : Reach 721709 := rs (se 3 (by rfl) ⟨135320, by rfl⟩) R270641
theorem R66359 : Reach 66359 := rs (se 1 (by rfl) ⟨49769, by rfl⟩) R99539
theorem R66379 : Reach 66379 := rs (se 1 (by rfl) ⟨49784, by rfl⟩) R99569
theorem R66391 : Reach 66391 := rs (se 1 (by rfl) ⟨49793, by rfl⟩) R99587
theorem R99161 : Reach 99161 := rs (se 2 (by rfl) ⟨37185, by rfl⟩) R74371
theorem R394085 : Reach 394085 := rs (se 4 (by rfl) ⟨36945, by rfl⟩) R73891
theorem R66411 : Reach 66411 := rs (se 1 (by rfl) ⟨49808, by rfl⟩) R99617
theorem R66423 : Reach 66423 := rs (se 1 (by rfl) ⟨49817, by rfl⟩) R99635
theorem R590723 : Reach 590723 := rs (se 1 (by rfl) ⟨443042, by rfl⟩) R886085
theorem R66443 : Reach 66443 := rs (se 1 (by rfl) ⟨49832, by rfl⟩) R99665
theorem R295825 : Reach 295825 := rs (se 2 (by rfl) ⟨110934, by rfl⟩) R221869
theorem R66455 : Reach 66455 := rs (se 1 (by rfl) ⟨49841, by rfl⟩) R99683
theorem R66475 : Reach 66475 := rs (se 1 (by rfl) ⟨49856, by rfl⟩) R99713
theorem R66487 : Reach 66487 := rs (se 1 (by rfl) ⟨49865, by rfl⟩) R99731
theorem R99275 : Reach 99275 := rs (se 1 (by rfl) ⟨74456, by rfl⟩) R148913
theorem R66507 : Reach 66507 := rs (se 1 (by rfl) ⟨49880, by rfl⟩) R99761
theorem R99287 : Reach 99287 := rs (se 1 (by rfl) ⟨74465, by rfl⟩) R148931
theorem R66519 : Reach 66519 := rs (se 1 (by rfl) ⟨49889, by rfl⟩) R99779
theorem R164825 : Reach 164825 := rs (se 2 (by rfl) ⟨61809, by rfl⟩) R123619
theorem R66539 : Reach 66539 := rs (se 1 (by rfl) ⟨49904, by rfl⟩) R99809
theorem R66551 : Reach 66551 := rs (se 1 (by rfl) ⟨49913, by rfl⟩) R99827
theorem R66571 : Reach 66571 := rs (se 1 (by rfl) ⟨49928, by rfl⟩) R99857
theorem R66583 : Reach 66583 := rs (se 1 (by rfl) ⟨49937, by rfl⟩) R99875
theorem R99353 : Reach 99353 := rs (se 2 (by rfl) ⟨37257, by rfl⟩) R74515
theorem R66603 : Reach 66603 := rs (se 1 (by rfl) ⟨49952, by rfl⟩) R99905
theorem R66615 : Reach 66615 := rs (se 1 (by rfl) ⟨49961, by rfl⟩) R99923
theorem R66635 : Reach 66635 := rs (se 1 (by rfl) ⟨49976, by rfl⟩) R99953
theorem R66647 : Reach 66647 := rs (se 1 (by rfl) ⟨49985, by rfl⟩) R99971
theorem R66667 : Reach 66667 := rs (se 1 (by rfl) ⟨50000, by rfl⟩) R100001
theorem R66679 : Reach 66679 := rs (se 1 (by rfl) ⟨50009, by rfl⟩) R100019
theorem R99467 : Reach 99467 := rs (se 1 (by rfl) ⟨74600, by rfl⟩) R149201
theorem R66699 : Reach 66699 := rs (se 1 (by rfl) ⟨50024, by rfl⟩) R100049
theorem R99479 : Reach 99479 := rs (se 1 (by rfl) ⟨74609, by rfl⟩) R149219
theorem R66711 : Reach 66711 := rs (se 1 (by rfl) ⟨50033, by rfl⟩) R100067
theorem R66731 : Reach 66731 := rs (se 1 (by rfl) ⟨50048, by rfl⟩) R100097
theorem R66743 : Reach 66743 := rs (se 1 (by rfl) ⟨50057, by rfl⟩) R100115
theorem R66763 : Reach 66763 := rs (se 1 (by rfl) ⟨50072, by rfl⟩) R100145
theorem R66775 : Reach 66775 := rs (se 1 (by rfl) ⟨50081, by rfl⟩) R100163
theorem R99545 : Reach 99545 := rs (se 2 (by rfl) ⟨37329, by rfl⟩) R74659
theorem R66795 : Reach 66795 := rs (se 1 (by rfl) ⟨50096, by rfl⟩) R100193
theorem R66807 : Reach 66807 := rs (se 1 (by rfl) ⟨50105, by rfl⟩) R100211
theorem R66827 : Reach 66827 := rs (se 1 (by rfl) ⟨50120, by rfl⟩) R100241
theorem R361745 : Reach 361745 := rs (se 2 (by rfl) ⟨135654, by rfl⟩) R271309
theorem R66839 : Reach 66839 := rs (se 1 (by rfl) ⟨50129, by rfl⟩) R100259
theorem R66859 : Reach 66859 := rs (se 1 (by rfl) ⟨50144, by rfl⟩) R100289
theorem R66871 : Reach 66871 := rs (se 1 (by rfl) ⟨50153, by rfl⟩) R100307
theorem R99659 : Reach 99659 := rs (se 1 (by rfl) ⟨74744, by rfl⟩) R149489
theorem R66891 : Reach 66891 := rs (se 1 (by rfl) ⟨50168, by rfl⟩) R100337
theorem R99671 : Reach 99671 := rs (se 1 (by rfl) ⟨74753, by rfl⟩) R149507
theorem R66903 : Reach 66903 := rs (se 1 (by rfl) ⟨50177, by rfl⟩) R100355
theorem R66923 : Reach 66923 := rs (se 1 (by rfl) ⟨50192, by rfl⟩) R100385
theorem R66935 : Reach 66935 := rs (se 1 (by rfl) ⟨50201, by rfl⟩) R100403
theorem R66955 : Reach 66955 := rs (se 1 (by rfl) ⟨50216, by rfl⟩) R100433
theorem R66967 : Reach 66967 := rs (se 1 (by rfl) ⟨50225, by rfl⟩) R100451
theorem R99737 : Reach 99737 := rs (se 2 (by rfl) ⟨37401, by rfl⟩) R74803
theorem R66987 : Reach 66987 := rs (se 1 (by rfl) ⟨50240, by rfl⟩) R100481
theorem R66999 : Reach 66999 := rs (se 1 (by rfl) ⟨50249, by rfl⟩) R100499
theorem R99787 : Reach 99787 := rs (se 1 (by rfl) ⟨74840, by rfl⟩) R149681
theorem R67019 : Reach 67019 := rs (se 1 (by rfl) ⟨50264, by rfl⟩) R100529
theorem R67031 : Reach 67031 := rs (se 1 (by rfl) ⟨50273, by rfl⟩) R100547
theorem R67051 : Reach 67051 := rs (se 1 (by rfl) ⟨50288, by rfl⟩) R100577
theorem R67063 : Reach 67063 := rs (se 1 (by rfl) ⟨50297, by rfl⟩) R100595
theorem R99851 : Reach 99851 := rs (se 1 (by rfl) ⟨74888, by rfl⟩) R149777
theorem R67083 : Reach 67083 := rs (se 1 (by rfl) ⟨50312, by rfl⟩) R100625
theorem R99863 : Reach 99863 := rs (se 1 (by rfl) ⟨74897, by rfl⟩) R149795
theorem R67095 : Reach 67095 := rs (se 1 (by rfl) ⟨50321, by rfl⟩) R100643
theorem R67115 : Reach 67115 := rs (se 1 (by rfl) ⟨50336, by rfl⟩) R100673
theorem R99929 : Reach 99929 := rs (se 2 (by rfl) ⟨37473, by rfl⟩) R74947
theorem R231005 : Reach 231005 := rs (se 3 (by rfl) ⟨43313, by rfl⟩) R86627
theorem R100043 : Reach 100043 := rs (se 1 (by rfl) ⟨75032, by rfl⟩) R150065
theorem R100055 : Reach 100055 := rs (se 1 (by rfl) ⟨75041, by rfl⟩) R150083
theorem R67339 : Reach 67339 := rs (se 1 (by rfl) ⟨50504, by rfl⟩) R101009
theorem R100121 : Reach 100121 := rs (se 2 (by rfl) ⟨37545, by rfl⟩) R75091
theorem R952165 : Reach 952165 := rs (se 4 (by rfl) ⟨89265, by rfl⟩) R178531
theorem R100235 : Reach 100235 := rs (se 1 (by rfl) ⟨75176, by rfl⟩) R150353
theorem R100247 : Reach 100247 := rs (se 1 (by rfl) ⟨75185, by rfl⟩) R150371
theorem R100313 : Reach 100313 := rs (se 2 (by rfl) ⟨37617, by rfl⟩) R75235
theorem R100427 : Reach 100427 := rs (se 1 (by rfl) ⟨75320, by rfl⟩) R150641
theorem R100439 : Reach 100439 := rs (se 1 (by rfl) ⟨75329, by rfl⟩) R150659
theorem R100505 : Reach 100505 := rs (se 2 (by rfl) ⟨37689, by rfl⟩) R75379
theorem R526513 : Reach 526513 := rs (se 2 (by rfl) ⟨197442, by rfl⟩) R394885
theorem R100619 : Reach 100619 := rs (se 1 (by rfl) ⟨75464, by rfl⟩) R150929
theorem R100631 : Reach 100631 := rs (se 1 (by rfl) ⟨75473, by rfl⟩) R150947
theorem R166195 : Reach 166195 := rs (se 1 (by rfl) ⟨124646, by rfl⟩) R249293
theorem R461207 : Reach 461207 := rs (se 1 (by rfl) ⟨345905, by rfl⟩) R691811
theorem R526771 : Reach 526771 := rs (se 1 (by rfl) ⟨395078, by rfl⟩) R790157
theorem R231959 : Reach 231959 := rs (se 1 (by rfl) ⟨173969, by rfl⟩) R347939
theorem R166475 : Reach 166475 := rs (se 1 (by rfl) ⟨124856, by rfl⟩) R249713
theorem R199513 : Reach 199513 := rs (se 2 (by rfl) ⟨74817, by rfl⟩) R149635
theorem R232523 : Reach 232523 := rs (se 1 (by rfl) ⟨174392, by rfl⟩) R348785
theorem R429131 : Reach 429131 := rs (se 1 (by rfl) ⟨321848, by rfl⟩) R643697
theorem R101593 : Reach 101593 := rs (se 2 (by rfl) ⟨38097, by rfl⟩) R76195
theorem R68887 : Reach 68887 := rs (se 1 (by rfl) ⟨51665, by rfl⟩) R103331
theorem R495065 : Reach 495065 := rs (se 2 (by rfl) ⟨185649, by rfl⟩) R371299
theorem R167447 : Reach 167447 := rs (se 1 (by rfl) ⟨125585, by rfl⟩) R251171
theorem R134873 : Reach 134873 := rs (se 2 (by rfl) ⟨50577, by rfl⟩) R101155
theorem R331613 : Reach 331613 := rs (se 3 (by rfl) ⟨62177, by rfl⟩) R124355
theorem R69707 : Reach 69707 := rs (se 1 (by rfl) ⟨52280, by rfl⟩) R104561
theorem R364675 : Reach 364675 := rs (se 1 (by rfl) ⟨273506, by rfl⟩) R547013
theorem R299159 : Reach 299159 := rs (se 1 (by rfl) ⟨224369, by rfl⟩) R448739
theorem R168115 : Reach 168115 := rs (se 1 (by rfl) ⟨126086, by rfl⟩) R252173
theorem R168257 : Reach 168257 := rs (se 2 (by rfl) ⟨63096, by rfl⟩) R126193
theorem R823769 : Reach 823769 := rs (se 2 (by rfl) ⟨308913, by rfl⟩) R617827
theorem R889379 : Reach 889379 := rs (se 1 (by rfl) ⟨667034, by rfl⟩) R1334069
theorem R135731 : Reach 135731 := rs (se 1 (by rfl) ⟨101798, by rfl⟩) R203597
theorem R332363 : Reach 332363 := rs (se 1 (by rfl) ⟨249272, by rfl⟩) R498545
theorem R168925 : Reach 168925 := rs (se 3 (by rfl) ⟨31673, by rfl⟩) R63347
theorem R464089 : Reach 464089 := rs (se 2 (by rfl) ⟨174033, by rfl⟩) R348067
theorem R70903 : Reach 70903 := rs (se 1 (by rfl) ⟨53177, by rfl⟩) R106355
theorem R71095 : Reach 71095 := rs (se 1 (by rfl) ⟨53321, by rfl⟩) R106643
theorem R169523 : Reach 169523 := rs (se 1 (by rfl) ⟨127142, by rfl⟩) R254285
theorem R71275 : Reach 71275 := rs (se 1 (by rfl) ⟨53456, by rfl⟩) R106913
theorem R71383 : Reach 71383 := rs (se 1 (by rfl) ⟨53537, by rfl⟩) R107075
theorem R562949 : Reach 562949 := rs (se 4 (by rfl) ⟨52776, by rfl⟩) R105553
theorem R759617 : Reach 759617 := rs (se 2 (by rfl) ⟨284856, by rfl⟩) R569713
theorem R137047 : Reach 137047 := rs (se 1 (by rfl) ⟨102785, by rfl⟩) R205571
theorem R71563 : Reach 71563 := rs (se 1 (by rfl) ⟨53672, by rfl⟩) R107345
theorem R333719 : Reach 333719 := rs (se 1 (by rfl) ⟨250289, by rfl⟩) R500579
theorem R71671 : Reach 71671 := rs (se 1 (by rfl) ⟨53753, by rfl⟩) R107507
theorem R137227 : Reach 137227 := rs (se 1 (by rfl) ⟨102920, by rfl⟩) R205841
theorem R923665 : Reach 923665 := rs (se 2 (by rfl) ⟨346374, by rfl⟩) R692749
theorem R137303 : Reach 137303 := rs (se 1 (by rfl) ⟨102977, by rfl⟩) R205955
theorem R71851 : Reach 71851 := rs (se 1 (by rfl) ⟨53888, by rfl⟩) R107777
theorem R202931 : Reach 202931 := rs (se 1 (by rfl) ⟨152198, by rfl⟩) R304397
theorem R661709 : Reach 661709 := rs (se 3 (by rfl) ⟨124070, by rfl⟩) R248141
theorem R71959 : Reach 71959 := rs (se 1 (by rfl) ⟨53969, by rfl⟩) R107939
theorem R72139 : Reach 72139 := rs (se 1 (by rfl) ⟨54104, by rfl⟩) R108209
theorem R104971 : Reach 104971 := rs (se 1 (by rfl) ⟨78728, by rfl⟩) R157457
theorem R72247 : Reach 72247 := rs (se 1 (by rfl) ⟨54185, by rfl⟩) R108371
theorem R72427 : Reach 72427 := rs (se 1 (by rfl) ⟨54320, by rfl⟩) R108641
theorem R105227 : Reach 105227 := rs (se 1 (by rfl) ⟨78920, by rfl⟩) R157841
theorem R72535 : Reach 72535 := rs (se 1 (by rfl) ⟨54401, by rfl⟩) R108803
theorem R367577 : Reach 367577 := rs (se 2 (by rfl) ⟨137841, by rfl⟩) R275683
theorem R72715 : Reach 72715 := rs (se 1 (by rfl) ⟨54536, by rfl⟩) R109073
theorem R72823 : Reach 72823 := rs (se 1 (by rfl) ⟨54617, by rfl⟩) R109235
theorem R73003 : Reach 73003 := rs (se 1 (by rfl) ⟨54752, by rfl⟩) R109505
theorem R597293 : Reach 597293 := rs (se 3 (by rfl) ⟨111992, by rfl⟩) R223985
theorem R204083 : Reach 204083 := rs (se 1 (by rfl) ⟨153062, by rfl⟩) R306125
theorem R73111 : Reach 73111 := rs (se 1 (by rfl) ⟨54833, by rfl⟩) R109667
theorem R499121 : Reach 499121 := rs (se 2 (by rfl) ⟨187170, by rfl⟩) R374341
theorem R204211 : Reach 204211 := rs (se 1 (by rfl) ⟨153158, by rfl⟩) R306317
theorem R892433 : Reach 892433 := rs (se 2 (by rfl) ⟨334662, by rfl⟩) R669325
theorem R237107 : Reach 237107 := rs (se 1 (by rfl) ⟨177830, by rfl⟩) R355661
theorem R73291 : Reach 73291 := rs (se 1 (by rfl) ⟨54968, by rfl⟩) R109937
theorem R73399 : Reach 73399 := rs (se 1 (by rfl) ⟨55049, by rfl⟩) R110099
theorem R106201 : Reach 106201 := rs (se 2 (by rfl) ⟨39825, by rfl⟩) R79651
theorem R139097 : Reach 139097 := rs (se 2 (by rfl) ⟨52161, by rfl⟩) R104323
theorem R73579 : Reach 73579 := rs (se 1 (by rfl) ⟨55184, by rfl⟩) R110369
theorem R499607 : Reach 499607 := rs (se 1 (by rfl) ⟨374705, by rfl⟩) R749411
theorem R73687 : Reach 73687 := rs (se 1 (by rfl) ⟨55265, by rfl⟩) R110531
theorem R1023961 : Reach 1023961 := rs (se 2 (by rfl) ⟨383985, by rfl⟩) R767971
theorem R73867 : Reach 73867 := rs (se 1 (by rfl) ⟨55400, by rfl⟩) R110801
theorem R630935 : Reach 630935 := rs (se 1 (by rfl) ⟨473201, by rfl⟩) R946403
theorem R73975 : Reach 73975 := rs (se 1 (by rfl) ⟨55481, by rfl⟩) R110963
theorem R172381 : Reach 172381 := rs (se 3 (by rfl) ⟨32321, by rfl⟩) R64643
theorem R74155 : Reach 74155 := rs (se 1 (by rfl) ⟨55616, by rfl⟩) R111233
theorem R106967 : Reach 106967 := rs (se 1 (by rfl) ⟨80225, by rfl⟩) R160451
theorem R139763 : Reach 139763 := rs (se 1 (by rfl) ⟨104822, by rfl⟩) R209645
theorem R74263 : Reach 74263 := rs (se 1 (by rfl) ⟨55697, by rfl⟩) R111395
theorem R107095 : Reach 107095 := rs (se 1 (by rfl) ⟨80321, by rfl⟩) R160643
theorem R74443 : Reach 74443 := rs (se 1 (by rfl) ⟨55832, by rfl⟩) R111665
theorem R74551 : Reach 74551 := rs (se 1 (by rfl) ⟨55913, by rfl⟩) R111827
theorem R271325 : Reach 271325 := rs (se 3 (by rfl) ⟨50873, by rfl⟩) R101747
theorem R74731 : Reach 74731 := rs (se 1 (by rfl) ⟨56048, by rfl⟩) R112097
theorem R500741 : Reach 500741 := rs (se 4 (by rfl) ⟨46944, by rfl⟩) R93889
theorem R74839 : Reach 74839 := rs (se 1 (by rfl) ⟨56129, by rfl⟩) R112259
theorem R107723 : Reach 107723 := rs (se 1 (by rfl) ⟨80792, by rfl⟩) R161585
theorem R75019 : Reach 75019 := rs (se 1 (by rfl) ⟨56264, by rfl⟩) R112529
theorem R271633 : Reach 271633 := rs (se 2 (by rfl) ⟨101862, by rfl⟩) R203725
theorem R271667 : Reach 271667 := rs (se 1 (by rfl) ⟨203750, by rfl⟩) R407501
theorem R828737 : Reach 828737 := rs (se 2 (by rfl) ⟨310776, by rfl⟩) R621553
theorem R107851 : Reach 107851 := rs (se 1 (by rfl) ⟨80888, by rfl⟩) R161777
theorem R337283 : Reach 337283 := rs (se 1 (by rfl) ⟨252962, by rfl⟩) R505925
theorem R173515 : Reach 173515 := rs (se 1 (by rfl) ⟨130136, by rfl⟩) R260273
theorem R107993 : Reach 107993 := rs (se 2 (by rfl) ⟨40497, by rfl⟩) R80995
theorem R370241 : Reach 370241 := rs (se 2 (by rfl) ⟨138840, by rfl⟩) R277681
theorem R108121 : Reach 108121 := rs (se 2 (by rfl) ⟨40545, by rfl⟩) R81091
theorem R75403 : Reach 75403 := rs (se 1 (by rfl) ⟨56552, by rfl⟩) R113105
theorem R75415 : Reach 75415 := rs (se 1 (by rfl) ⟨56561, by rfl⟩) R113123
theorem R141259 : Reach 141259 := rs (se 1 (by rfl) ⟨105944, by rfl⟩) R211889
theorem R239705 : Reach 239705 := rs (se 2 (by rfl) ⟨89889, by rfl⟩) R179779
theorem R108695 : Reach 108695 := rs (se 1 (by rfl) ⟨81521, by rfl⟩) R163043
theorem R108823 : Reach 108823 := rs (se 1 (by rfl) ⟨81617, by rfl⟩) R163235
theorem R240023 : Reach 240023 := rs (se 1 (by rfl) ⟨180017, by rfl⟩) R360035
theorem R240221 : Reach 240221 := rs (se 3 (by rfl) ⟨45041, by rfl⟩) R90083
theorem R142091 : Reach 142091 := rs (se 1 (by rfl) ⟨106568, by rfl⟩) R213137
theorem R174899 : Reach 174899 := rs (se 1 (by rfl) ⟨131174, by rfl⟩) R262349
theorem R142145 : Reach 142145 := rs (se 2 (by rfl) ⟨53304, by rfl⟩) R106609
theorem R109451 : Reach 109451 := rs (se 1 (by rfl) ⟨82088, by rfl⟩) R164177
theorem R109579 : Reach 109579 := rs (se 1 (by rfl) ⟨82184, by rfl⟩) R164369
theorem R142361 : Reach 142361 := rs (se 2 (by rfl) ⟨53385, by rfl⟩) R106771
theorem R240691 : Reach 240691 := rs (se 1 (by rfl) ⟨180518, by rfl⟩) R361037
theorem R142451 : Reach 142451 := rs (se 1 (by rfl) ⟨106838, by rfl⟩) R213677
theorem R142487 : Reach 142487 := rs (se 1 (by rfl) ⟨106865, by rfl⟩) R213731
theorem R109721 : Reach 109721 := rs (se 2 (by rfl) ⟨41145, by rfl⟩) R82291
theorem R142489 : Reach 142489 := rs (se 2 (by rfl) ⟨53433, by rfl⟩) R106867
theorem R273581 : Reach 273581 := rs (se 3 (by rfl) ⟨51296, by rfl⟩) R102593
theorem R109849 : Reach 109849 := rs (se 2 (by rfl) ⟨41193, by rfl⟩) R82387
theorem R142667 : Reach 142667 := rs (se 1 (by rfl) ⟨107000, by rfl⟩) R214001
theorem R404837 : Reach 404837 := rs (se 4 (by rfl) ⟨37953, by rfl⟩) R75907
theorem R142721 : Reach 142721 := rs (se 2 (by rfl) ⟨53520, by rfl⟩) R107041
theorem R142937 : Reach 142937 := rs (se 2 (by rfl) ⟨53601, by rfl⟩) R107203
theorem R143027 : Reach 143027 := rs (se 1 (by rfl) ⟨107270, by rfl⟩) R214541
theorem R143063 : Reach 143063 := rs (se 1 (by rfl) ⟨107297, by rfl⟩) R214595
theorem R175895 : Reach 175895 := rs (se 1 (by rfl) ⟨131921, by rfl⟩) R263843
theorem R274265 : Reach 274265 := rs (se 2 (by rfl) ⟨102849, by rfl⟩) R205699
theorem R110423 : Reach 110423 := rs (se 1 (by rfl) ⟨82817, by rfl⟩) R165635
theorem R143243 : Reach 143243 := rs (se 1 (by rfl) ⟨107432, by rfl⟩) R214865
theorem R143297 : Reach 143297 := rs (se 2 (by rfl) ⟨53736, by rfl⟩) R107473
theorem R110551 : Reach 110551 := rs (se 1 (by rfl) ⟨82913, by rfl⟩) R165827
theorem R143513 : Reach 143513 := rs (se 2 (by rfl) ⟨53817, by rfl⟩) R107635
theorem R143603 : Reach 143603 := rs (se 1 (by rfl) ⟨107702, by rfl⟩) R215405
theorem R241937 : Reach 241937 := rs (se 2 (by rfl) ⟨90726, by rfl⟩) R181453
theorem R143639 : Reach 143639 := rs (se 1 (by rfl) ⟨107729, by rfl⟩) R215459
theorem R143819 : Reach 143819 := rs (se 1 (by rfl) ⟨107864, by rfl⟩) R215729
theorem R143873 : Reach 143873 := rs (se 2 (by rfl) ⟨53952, by rfl⟩) R107905
theorem R111179 : Reach 111179 := rs (se 1 (by rfl) ⟨83384, by rfl⟩) R166769
theorem R569987 : Reach 569987 := rs (se 1 (by rfl) ⟨427490, by rfl⟩) R854981
theorem R111307 : Reach 111307 := rs (se 1 (by rfl) ⟨83480, by rfl⟩) R166961
theorem R144089 : Reach 144089 := rs (se 2 (by rfl) ⟨54033, by rfl⟩) R108067
theorem R144179 : Reach 144179 := rs (se 1 (by rfl) ⟨108134, by rfl⟩) R216269
theorem R144215 : Reach 144215 := rs (se 1 (by rfl) ⟨108161, by rfl⟩) R216323
theorem R111449 : Reach 111449 := rs (se 2 (by rfl) ⟨41793, by rfl⟩) R83587
theorem R242635 : Reach 242635 := rs (se 1 (by rfl) ⟨181976, by rfl⟩) R363953
theorem R177113 : Reach 177113 := rs (se 2 (by rfl) ⟨66417, by rfl⟩) R132835
theorem R111577 : Reach 111577 := rs (se 2 (by rfl) ⟨41841, by rfl⟩) R83683
theorem R144395 : Reach 144395 := rs (se 1 (by rfl) ⟨108296, by rfl⟩) R216593
theorem R144449 : Reach 144449 := rs (se 2 (by rfl) ⟨54168, by rfl⟩) R108337
theorem R308299 : Reach 308299 := rs (se 1 (by rfl) ⟨231224, by rfl⟩) R462449
theorem R799895 : Reach 799895 := rs (se 1 (by rfl) ⟨599921, by rfl⟩) R1199843
theorem R242909 : Reach 242909 := rs (se 3 (by rfl) ⟨45545, by rfl⟩) R91091
theorem R144665 : Reach 144665 := rs (se 2 (by rfl) ⟨54249, by rfl⟩) R108499
theorem R144755 : Reach 144755 := rs (se 1 (by rfl) ⟨108566, by rfl⟩) R217133
theorem R144791 : Reach 144791 := rs (se 1 (by rfl) ⟨108593, by rfl⟩) R217187
theorem R79319 : Reach 79319 := rs (se 1 (by rfl) ⟨59489, by rfl⟩) R118979
theorem R439769 : Reach 439769 := rs (se 2 (by rfl) ⟨164913, by rfl⟩) R329827
theorem R112151 : Reach 112151 := rs (se 1 (by rfl) ⟨84113, by rfl⟩) R168227
theorem R1029667 : Reach 1029667 := rs (se 1 (by rfl) ⟨772250, by rfl⟩) R1544501
theorem R144971 : Reach 144971 := rs (se 1 (by rfl) ⟨108728, by rfl⟩) R217457
theorem R145025 : Reach 145025 := rs (se 2 (by rfl) ⟨54384, by rfl⟩) R108769
theorem R11417219 : Reach 11417219 := rs (se 1 (by rfl) ⟨8562914, by rfl⟩) R17125829
theorem R112279 : Reach 112279 := rs (se 1 (by rfl) ⟨84209, by rfl⟩) R168419
theorem R145241 : Reach 145241 := rs (se 2 (by rfl) ⟨54465, by rfl⟩) R108931
theorem R178013 : Reach 178013 := rs (se 3 (by rfl) ⟨33377, by rfl⟩) R66755
theorem R243607 : Reach 243607 := rs (se 1 (by rfl) ⟨182705, by rfl⟩) R365411
theorem R145331 : Reach 145331 := rs (se 1 (by rfl) ⟨108998, by rfl⟩) R217997
theorem R145367 : Reach 145367 := rs (se 1 (by rfl) ⟨109025, by rfl⟩) R218051
theorem R112691 : Reach 112691 := rs (se 1 (by rfl) ⟨84518, by rfl⟩) R169037
theorem R1882187 : Reach 1882187 := rs (se 1 (by rfl) ⟨1411640, by rfl⟩) R2823281
theorem R145547 : Reach 145547 := rs (se 1 (by rfl) ⟨109160, by rfl⟩) R218321
theorem R80023 : Reach 80023 := rs (se 1 (by rfl) ⟨60017, by rfl⟩) R120035
theorem R112819 : Reach 112819 := rs (se 1 (by rfl) ⟨84614, by rfl⟩) R169229
theorem R145601 : Reach 145601 := rs (se 2 (by rfl) ⟨54600, by rfl⟩) R109201
theorem R145675 : Reach 145675 := rs (se 1 (by rfl) ⟨109256, by rfl⟩) R218513
theorem R112907 : Reach 112907 := rs (se 1 (by rfl) ⟨84680, by rfl⟩) R169361
theorem R112961 : Reach 112961 := rs (se 2 (by rfl) ⟨42360, by rfl⟩) R84721
theorem R538973 : Reach 538973 := rs (se 3 (by rfl) ⟨101057, by rfl⟩) R202115
theorem R113035 : Reach 113035 := rs (se 1 (by rfl) ⟨84776, by rfl⟩) R169553
theorem R145817 : Reach 145817 := rs (se 2 (by rfl) ⟨54681, by rfl⟩) R109363
theorem R276929 : Reach 276929 := rs (se 2 (by rfl) ⟨103848, by rfl⟩) R207697
theorem R113089 : Reach 113089 := rs (se 2 (by rfl) ⟨42408, by rfl⟩) R84817
theorem R145907 : Reach 145907 := rs (se 1 (by rfl) ⟨109430, by rfl⟩) R218861
theorem R80395 : Reach 80395 := rs (se 1 (by rfl) ⟨60296, by rfl⟩) R120593
theorem R1161745 : Reach 1161745 := rs (se 2 (by rfl) ⟨435654, by rfl⟩) R871309
theorem R145943 : Reach 145943 := rs (se 1 (by rfl) ⟨109457, by rfl⟩) R218915
theorem R113177 : Reach 113177 := rs (se 2 (by rfl) ⟨42441, by rfl⟩) R84883
theorem R244397 : Reach 244397 := rs (se 3 (by rfl) ⟨45824, by rfl⟩) R91649
theorem R146123 : Reach 146123 := rs (se 1 (by rfl) ⟨109592, by rfl⟩) R219185
theorem R309977 : Reach 309977 := rs (se 2 (by rfl) ⟨116241, by rfl⟩) R232483
theorem R146177 : Reach 146177 := rs (se 2 (by rfl) ⟨54816, by rfl⟩) R109633
theorem R375617 : Reach 375617 := rs (se 2 (by rfl) ⟨140856, by rfl⟩) R281713
theorem R146393 : Reach 146393 := rs (se 2 (by rfl) ⟨54897, by rfl⟩) R109795
theorem R506897 : Reach 506897 := rs (se 2 (by rfl) ⟨190086, by rfl⟩) R380173
theorem R146483 : Reach 146483 := rs (se 1 (by rfl) ⟨109862, by rfl⟩) R219725
theorem R146519 : Reach 146519 := rs (se 1 (by rfl) ⟨109889, by rfl⟩) R219779
theorem R146699 : Reach 146699 := rs (se 1 (by rfl) ⟨110024, by rfl⟩) R220049
theorem R146753 : Reach 146753 := rs (se 2 (by rfl) ⟨55032, by rfl⟩) R110065
theorem R474443 : Reach 474443 := rs (se 1 (by rfl) ⟨355832, by rfl⟩) R711665
theorem R4078997 : Reach 4078997 := rs (se 6 (by rfl) ⟨95601, by rfl⟩) R191203
theorem R245213 : Reach 245213 := rs (se 3 (by rfl) ⟨45977, by rfl⟩) R91955
theorem R146969 : Reach 146969 := rs (se 2 (by rfl) ⟨55113, by rfl⟩) R110227
theorem R147059 : Reach 147059 := rs (se 1 (by rfl) ⟨110294, by rfl⟩) R220589
theorem R147095 : Reach 147095 := rs (se 1 (by rfl) ⟨110321, by rfl⟩) R220643
theorem R179915 : Reach 179915 := rs (se 1 (by rfl) ⟨134936, by rfl⟩) R269873
theorem R81739 : Reach 81739 := rs (se 1 (by rfl) ⟨61304, by rfl⟩) R122609
theorem R147275 : Reach 147275 := rs (se 1 (by rfl) ⟨110456, by rfl⟩) R220913
theorem R147329 : Reach 147329 := rs (se 2 (by rfl) ⟨55248, by rfl⟩) R110497
theorem R278417 : Reach 278417 := rs (se 2 (by rfl) ⟨104406, by rfl⟩) R208813
theorem R540593 : Reach 540593 := rs (se 2 (by rfl) ⟨202722, by rfl⟩) R405445
theorem R245825 : Reach 245825 := rs (se 2 (by rfl) ⟨92184, by rfl⟩) R184369
theorem R147545 : Reach 147545 := rs (se 2 (by rfl) ⟨55329, by rfl⟩) R110659
theorem R147635 : Reach 147635 := rs (se 1 (by rfl) ⟨110726, by rfl⟩) R221453
theorem R147671 : Reach 147671 := rs (se 1 (by rfl) ⟨110753, by rfl⟩) R221507
theorem R213299 : Reach 213299 := rs (se 1 (by rfl) ⟨159974, by rfl⟩) R319949
theorem R147851 : Reach 147851 := rs (se 1 (by rfl) ⟨110888, by rfl⟩) R221777
theorem R541079 : Reach 541079 := rs (se 1 (by rfl) ⟨405809, by rfl⟩) R811619
theorem R147905 : Reach 147905 := rs (se 2 (by rfl) ⟨55464, by rfl⟩) R110929
theorem R180701 : Reach 180701 := rs (se 3 (by rfl) ⟨33881, by rfl⟩) R67763
theorem R213569 : Reach 213569 := rs (se 2 (by rfl) ⟨80088, by rfl⟩) R160177
theorem R1065565 : Reach 1065565 := rs (se 3 (by rfl) ⟨199793, by rfl⟩) R399587
theorem R148121 : Reach 148121 := rs (se 2 (by rfl) ⟨55545, by rfl⟩) R111091
theorem R180929 : Reach 180929 := rs (se 2 (by rfl) ⟨67848, by rfl⟩) R135697
theorem R148211 : Reach 148211 := rs (se 1 (by rfl) ⟨111158, by rfl⟩) R222317
theorem R82711 : Reach 82711 := rs (se 1 (by rfl) ⟨62033, by rfl⟩) R124067
theorem R148247 : Reach 148247 := rs (se 1 (by rfl) ⟨111185, by rfl⟩) R222371
theorem R475969 : Reach 475969 := rs (se 2 (by rfl) ⟨178488, by rfl⟩) R356977
theorem R279389 : Reach 279389 := rs (se 3 (by rfl) ⟨52385, by rfl⟩) R104771
theorem R246721 : Reach 246721 := rs (se 2 (by rfl) ⟨92520, by rfl⟩) R185041
theorem R82891 : Reach 82891 := rs (se 1 (by rfl) ⟨62168, by rfl⟩) R124337
theorem R148427 : Reach 148427 := rs (se 1 (by rfl) ⟨111320, by rfl⟩) R222641
theorem R213977 : Reach 213977 := rs (se 2 (by rfl) ⟨80241, by rfl⟩) R160483
theorem R148481 : Reach 148481 := rs (se 2 (by rfl) ⟨55680, by rfl⟩) R111361
theorem R181271 : Reach 181271 := rs (se 1 (by rfl) ⟨135953, by rfl⟩) R271907
theorem R115763 : Reach 115763 := rs (se 1 (by rfl) ⟨86822, by rfl⟩) R173645
theorem R214109 : Reach 214109 := rs (se 3 (by rfl) ⟨40145, by rfl⟩) R80291
theorem R148697 : Reach 148697 := rs (se 2 (by rfl) ⟨55761, by rfl⟩) R111523
theorem R279811 : Reach 279811 := rs (se 1 (by rfl) ⟨209858, by rfl⟩) R419717
theorem R148787 : Reach 148787 := rs (se 1 (by rfl) ⟨111590, by rfl⟩) R223181
theorem R148823 : Reach 148823 := rs (se 1 (by rfl) ⟨111617, by rfl⟩) R223235
theorem R116225 : Reach 116225 := rs (se 2 (by rfl) ⟨43584, by rfl⟩) R87169
theorem R149003 : Reach 149003 := rs (se 1 (by rfl) ⟨111752, by rfl⟩) R223505
theorem R247313 : Reach 247313 := rs (se 2 (by rfl) ⟨92742, by rfl⟩) R185485
theorem R149057 : Reach 149057 := rs (se 2 (by rfl) ⟨55896, by rfl⟩) R111793
theorem R83531 : Reach 83531 := rs (se 1 (by rfl) ⟨62648, by rfl⟩) R125297
theorem R116311 : Reach 116311 := rs (se 1 (by rfl) ⟨87233, by rfl⟩) R174467
theorem R214721 : Reach 214721 := rs (se 2 (by rfl) ⟨80520, by rfl⟩) R161041
theorem R149273 : Reach 149273 := rs (se 2 (by rfl) ⟨55977, by rfl⟩) R111955
theorem R149363 : Reach 149363 := rs (se 1 (by rfl) ⟨112022, by rfl⟩) R224045
theorem R149399 : Reach 149399 := rs (se 1 (by rfl) ⟨112049, by rfl⟩) R224099
theorem R247769 : Reach 247769 := rs (se 2 (by rfl) ⟨92913, by rfl⟩) R185827
theorem R149579 : Reach 149579 := rs (se 1 (by rfl) ⟨112184, by rfl⟩) R224369
theorem R247901 : Reach 247901 := rs (se 3 (by rfl) ⟨46481, by rfl⟩) R92963
theorem R247981 : Reach 247981 := rs (se 3 (by rfl) ⟨46496, by rfl⟩) R92993
theorem R215243 : Reach 215243 := rs (se 1 (by rfl) ⟨161432, by rfl⟩) R322865
theorem R84235 : Reach 84235 := rs (se 1 (by rfl) ⟨63176, by rfl⟩) R126353
theorem R1132865 : Reach 1132865 := rs (se 2 (by rfl) ⟨424824, by rfl⟩) R849649
theorem R149849 : Reach 149849 := rs (se 2 (by rfl) ⟨56193, by rfl⟩) R112387
theorem R149939 : Reach 149939 := rs (se 1 (by rfl) ⟨112454, by rfl⟩) R224909
theorem R215513 : Reach 215513 := rs (se 2 (by rfl) ⟨80817, by rfl⟩) R161635
theorem R248285 : Reach 248285 := rs (se 3 (by rfl) ⟨46553, by rfl⟩) R93107
theorem R84503 : Reach 84503 := rs (se 1 (by rfl) ⟨63377, by rfl⟩) R126755
theorem R477731 : Reach 477731 := rs (se 1 (by rfl) ⟨358298, by rfl⟩) R716597
theorem R150209 : Reach 150209 := rs (se 2 (by rfl) ⟨56328, by rfl⟩) R112657
theorem R150551 : Reach 150551 := rs (se 1 (by rfl) ⟨112913, by rfl⟩) R225827
theorem R216215 : Reach 216215 := rs (se 1 (by rfl) ⟨162161, by rfl⟩) R324323
theorem R85195 : Reach 85195 := rs (se 1 (by rfl) ⟨63896, by rfl⟩) R127793
theorem R150731 : Reach 150731 := rs (se 1 (by rfl) ⟨113048, by rfl⟩) R226097
theorem R183617 : Reach 183617 := rs (se 2 (by rfl) ⟨68856, by rfl⟩) R137713
theorem R281987 : Reach 281987 := rs (se 1 (by rfl) ⟨211490, by rfl⟩) R422981
theorem R151001 : Reach 151001 := rs (se 2 (by rfl) ⟨56625, by rfl⟩) R113251
theorem R347723 : Reach 347723 := rs (se 1 (by rfl) ⟨260792, by rfl⟩) R521585
theorem R216755 : Reach 216755 := rs (se 1 (by rfl) ⟨162566, by rfl⟩) R325133
theorem R282329 : Reach 282329 := rs (se 2 (by rfl) ⟨105873, by rfl⟩) R211747
theorem R184153 : Reach 184153 := rs (se 2 (by rfl) ⟨69057, by rfl⟩) R138115
theorem R217025 : Reach 217025 := rs (se 2 (by rfl) ⟨81384, by rfl⟩) R162769
theorem R118835 : Reach 118835 := rs (se 1 (by rfl) ⟨89126, by rfl⟩) R178253
theorem R151769 : Reach 151769 := rs (se 2 (by rfl) ⟨56913, by rfl⟩) R113827
theorem R217565 : Reach 217565 := rs (se 3 (by rfl) ⟨40793, by rfl⟩) R81587
theorem R873281 : Reach 873281 := rs (se 2 (by rfl) ⟨327480, by rfl⟩) R654961
theorem R250883 : Reach 250883 := rs (se 1 (by rfl) ⟨188162, by rfl⟩) R376325
theorem R250897 : Reach 250897 := rs (se 2 (by rfl) ⟨94086, by rfl⟩) R188173
theorem R251201 : Reach 251201 := rs (se 2 (by rfl) ⟨94200, by rfl⟩) R188401
theorem R120179 : Reach 120179 := rs (se 1 (by rfl) ⟨90134, by rfl⟩) R180269
theorem R120217 : Reach 120217 := rs (se 2 (by rfl) ⟨45081, by rfl⟩) R90163
theorem R218699 : Reach 218699 := rs (se 1 (by rfl) ⟨164024, by rfl⟩) R328049
theorem R186077 : Reach 186077 := rs (se 3 (by rfl) ⟨34889, by rfl⟩) R69779
theorem R153409 : Reach 153409 := rs (se 2 (by rfl) ⟨57528, by rfl⟩) R115057
theorem R218969 : Reach 218969 := rs (se 2 (by rfl) ⟨82113, by rfl⟩) R164227
theorem R120665 : Reach 120665 := rs (se 2 (by rfl) ⟨45249, by rfl⟩) R90499
theorem R481241 : Reach 481241 := rs (se 2 (by rfl) ⟨180465, by rfl⟩) R360931
theorem R251869 : Reach 251869 := rs (se 3 (by rfl) ⟨47225, by rfl⟩) R94451
theorem R841859 : Reach 841859 := rs (se 1 (by rfl) ⟨631394, by rfl⟩) R1262789
theorem R219671 : Reach 219671 := rs (se 1 (by rfl) ⟨164753, by rfl⟩) R329507
theorem R121409 : Reach 121409 := rs (se 2 (by rfl) ⟨45528, by rfl⟩) R91057
theorem R88715 : Reach 88715 := rs (se 1 (by rfl) ⟨66536, by rfl⟩) R133073
theorem R121675 : Reach 121675 := rs (se 1 (by rfl) ⟨91256, by rfl⟩) R182513
theorem R285713 : Reach 285713 := rs (se 2 (by rfl) ⟨107142, by rfl⟩) R214285
theorem R220211 : Reach 220211 := rs (se 1 (by rfl) ⟨165158, by rfl⟩) R330317
theorem R253145 : Reach 253145 := rs (se 2 (by rfl) ⟨94929, by rfl⟩) R189859
theorem R122123 : Reach 122123 := rs (se 1 (by rfl) ⟨91592, by rfl⟩) R183185
theorem R220481 : Reach 220481 := rs (se 2 (by rfl) ⟨82680, by rfl⟩) R165361
theorem R122305 : Reach 122305 := rs (se 2 (by rfl) ⟨45864, by rfl⟩) R91729
theorem R155159 : Reach 155159 := rs (se 1 (by rfl) ⟨116369, by rfl⟩) R232739
theorem R810647 : Reach 810647 := rs (se 1 (by rfl) ⟨607985, by rfl⟩) R1215971
theorem R286429 : Reach 286429 := rs (se 3 (by rfl) ⟨53705, by rfl⟩) R107411
theorem R581381 : Reach 581381 := rs (se 4 (by rfl) ⟨54504, by rfl⟩) R109009
theorem R122647 : Reach 122647 := rs (se 1 (by rfl) ⟨91985, by rfl⟩) R183971
theorem R221021 : Reach 221021 := rs (se 3 (by rfl) ⟨41441, by rfl⟩) R82883
theorem R122867 : Reach 122867 := rs (se 1 (by rfl) ⟨92150, by rfl⟩) R184301
theorem R253955 : Reach 253955 := rs (se 1 (by rfl) ⟨190466, by rfl⟩) R380933
theorem R123095 : Reach 123095 := rs (se 1 (by rfl) ⟨92321, by rfl⟩) R184643
theorem R254173 : Reach 254173 := rs (se 3 (by rfl) ⟨47657, by rfl⟩) R95315
theorem R90391 : Reach 90391 := rs (se 1 (by rfl) ⟨67793, by rfl⟩) R135587
theorem R155927 : Reach 155927 := rs (se 1 (by rfl) ⟨116945, by rfl⟩) R233891
theorem R680293 : Reach 680293 := rs (se 4 (by rfl) ⟨63777, by rfl⟩) R127555
theorem R483685 : Reach 483685 := rs (se 4 (by rfl) ⟨45345, by rfl⟩) R90691
theorem R123353 : Reach 123353 := rs (se 2 (by rfl) ⟨46257, by rfl⟩) R92515
theorem R188993 : Reach 188993 := rs (se 2 (by rfl) ⟨70872, by rfl⟩) R141745
theorem R189017 : Reach 189017 := rs (se 2 (by rfl) ⟨70881, by rfl⟩) R141763
theorem R320273 : Reach 320273 := rs (se 2 (by rfl) ⟨120102, by rfl⟩) R240205
theorem R254771 : Reach 254771 := rs (se 1 (by rfl) ⟨191078, by rfl⟩) R382157
theorem R254785 : Reach 254785 := rs (se 2 (by rfl) ⟨95544, by rfl⟩) R191089
theorem R123763 : Reach 123763 := rs (se 1 (by rfl) ⟨92822, by rfl⟩) R185645
theorem R320435 : Reach 320435 := rs (se 1 (by rfl) ⟨240326, by rfl⟩) R480653
theorem R222155 : Reach 222155 := rs (se 1 (by rfl) ⟨166616, by rfl⟩) R333233
theorem R2057237 : Reach 2057237 := rs (se 6 (by rfl) ⟨48216, by rfl⟩) R96433
theorem R222425 : Reach 222425 := rs (se 2 (by rfl) ⟨83409, by rfl⟩) R166819
theorem R124249 : Reach 124249 := rs (se 2 (by rfl) ⟨46593, by rfl⟩) R93187
theorem R550577 : Reach 550577 := rs (se 2 (by rfl) ⟨206466, by rfl⟩) R412933
theorem R190259 : Reach 190259 := rs (se 1 (by rfl) ⟨142694, by rfl⟩) R285389
theorem R124811 : Reach 124811 := rs (se 1 (by rfl) ⟨93608, by rfl⟩) R187217
theorem R223127 : Reach 223127 := rs (se 1 (by rfl) ⟨167345, by rfl⟩) R334691
theorem R157619 : Reach 157619 := rs (se 1 (by rfl) ⟨118214, by rfl⟩) R236429
theorem R124993 : Reach 124993 := rs (se 2 (by rfl) ⟨46872, by rfl⟩) R93745
theorem R583859 : Reach 583859 := rs (se 1 (by rfl) ⟨437894, by rfl⟩) R875789
theorem R92441 : Reach 92441 := rs (se 2 (by rfl) ⟨34665, by rfl⟩) R69331
theorem R158041 : Reach 158041 := rs (se 2 (by rfl) ⟨59265, by rfl⟩) R118531
theorem R747953 : Reach 747953 := rs (se 2 (by rfl) ⟨280482, by rfl⟩) R560965
theorem R223667 : Reach 223667 := rs (se 1 (by rfl) ⟨167750, by rfl⟩) R335501
theorem R223937 : Reach 223937 := rs (se 2 (by rfl) ⟨83976, by rfl⟩) R167953
theorem R125707 : Reach 125707 := rs (se 1 (by rfl) ⟨94280, by rfl⟩) R188561
theorem R322379 : Reach 322379 := rs (se 1 (by rfl) ⟨241784, by rfl⟩) R483569
theorem R125783 : Reach 125783 := rs (se 1 (by rfl) ⟨94337, by rfl⟩) R188675
theorem R191321 : Reach 191321 := rs (se 2 (by rfl) ⟨71745, by rfl⟩) R143491
theorem R93079 : Reach 93079 := rs (se 1 (by rfl) ⟨69809, by rfl⟩) R139619
theorem R322483 : Reach 322483 := rs (se 1 (by rfl) ⟨241862, by rfl⟩) R483725
theorem R224477 : Reach 224477 := rs (se 3 (by rfl) ⟨42089, by rfl⟩) R84179
theorem R126451 : Reach 126451 := rs (se 1 (by rfl) ⟨94838, by rfl⟩) R189677
theorem R93847 : Reach 93847 := rs (se 1 (by rfl) ⟨70385, by rfl⟩) R140771
theorem R93899 : Reach 93899 := rs (se 1 (by rfl) ⟨70424, by rfl⟩) R140849
theorem R126679 : Reach 126679 := rs (se 1 (by rfl) ⟨95009, by rfl⟩) R190019
theorem R126785 : Reach 126785 := rs (se 2 (by rfl) ⟨47544, by rfl⟩) R95089
theorem R454531 : Reach 454531 := rs (se 1 (by rfl) ⟨340898, by rfl⟩) R681797
theorem R126937 : Reach 126937 := rs (se 2 (by rfl) ⟨47601, by rfl⟩) R95203
theorem R159833 : Reach 159833 := rs (se 2 (by rfl) ⟨59937, by rfl⟩) R119875
theorem R225611 : Reach 225611 := rs (se 1 (by rfl) ⟨169208, by rfl⟩) R338417
theorem R94745 : Reach 94745 := rs (se 2 (by rfl) ⟨35529, by rfl⟩) R71059
theorem R324161 : Reach 324161 := rs (se 2 (by rfl) ⟨121560, by rfl⟩) R243121
theorem R225881 : Reach 225881 := rs (se 2 (by rfl) ⟨84705, by rfl⟩) R169411
theorem R94859 : Reach 94859 := rs (se 1 (by rfl) ⟨71144, by rfl⟩) R142289
theorem R94871 : Reach 94871 := rs (se 1 (by rfl) ⟨71153, by rfl⟩) R142307
theorem R94873 : Reach 94873 := rs (se 2 (by rfl) ⟨35577, by rfl⟩) R71155
theorem R94937 : Reach 94937 := rs (se 2 (by rfl) ⟨35601, by rfl⟩) R71203
theorem R95051 : Reach 95051 := rs (se 1 (by rfl) ⟨71288, by rfl⟩) R142577
theorem R95063 : Reach 95063 := rs (se 1 (by rfl) ⟨71297, by rfl⟩) R142595
theorem R160663 : Reach 160663 := rs (se 1 (by rfl) ⟨120497, by rfl⟩) R240995
theorem R95129 : Reach 95129 := rs (se 2 (by rfl) ⟨35673, by rfl⟩) R71347
theorem R95243 : Reach 95243 := rs (se 1 (by rfl) ⟨71432, by rfl⟩) R142865
theorem R947213 : Reach 947213 := rs (se 3 (by rfl) ⟨177602, by rfl⟩) R355205
theorem R95255 : Reach 95255 := rs (se 1 (by rfl) ⟨71441, by rfl⟩) R142883
theorem R95321 : Reach 95321 := rs (se 2 (by rfl) ⟨35745, by rfl⟩) R71491
theorem R95435 : Reach 95435 := rs (se 1 (by rfl) ⟨71576, by rfl⟩) R143153
theorem R95447 : Reach 95447 := rs (se 1 (by rfl) ⟨71585, by rfl⟩) R143171
theorem R554201 : Reach 554201 := rs (se 2 (by rfl) ⟨207825, by rfl⟩) R415651
theorem R95513 : Reach 95513 := rs (se 2 (by rfl) ⟨35817, by rfl⟩) R71635
theorem R161099 : Reach 161099 := rs (se 1 (by rfl) ⟨120824, by rfl⟩) R241649
theorem R95627 : Reach 95627 := rs (se 1 (by rfl) ⟨71720, by rfl⟩) R143441
theorem R95639 : Reach 95639 := rs (se 1 (by rfl) ⟨71729, by rfl⟩) R143459
theorem R95705 : Reach 95705 := rs (se 2 (by rfl) ⟨35889, by rfl⟩) R71779
theorem R95819 : Reach 95819 := rs (se 1 (by rfl) ⟨71864, by rfl⟩) R143729
theorem R95831 : Reach 95831 := rs (se 1 (by rfl) ⟨71873, by rfl⟩) R143747
theorem R63127 : Reach 63127 := rs (se 1 (by rfl) ⟨47345, by rfl⟩) R94691
theorem R95897 : Reach 95897 := rs (se 2 (by rfl) ⟨35961, by rfl⟩) R71923
theorem R63147 : Reach 63147 := rs (se 1 (by rfl) ⟨47360, by rfl⟩) R94721
theorem R63159 : Reach 63159 := rs (se 1 (by rfl) ⟨47369, by rfl⟩) R94739
theorem R161473 : Reach 161473 := rs (se 2 (by rfl) ⟨60552, by rfl⟩) R121105
theorem R63179 : Reach 63179 := rs (se 1 (by rfl) ⟨47384, by rfl⟩) R94769
theorem R63191 : Reach 63191 := rs (se 1 (by rfl) ⟨47393, by rfl⟩) R94787
theorem R63211 : Reach 63211 := rs (se 1 (by rfl) ⟨47408, by rfl⟩) R94817
theorem R63223 : Reach 63223 := rs (se 1 (by rfl) ⟨47417, by rfl⟩) R94835
theorem R63243 : Reach 63243 := rs (se 1 (by rfl) ⟨47432, by rfl⟩) R94865
theorem R96011 : Reach 96011 := rs (se 1 (by rfl) ⟨72008, by rfl⟩) R144017
theorem R63255 : Reach 63255 := rs (se 1 (by rfl) ⟨47441, by rfl⟩) R94883
theorem R96023 : Reach 96023 := rs (se 1 (by rfl) ⟨72017, by rfl⟩) R144035
theorem R63275 : Reach 63275 := rs (se 1 (by rfl) ⟨47456, by rfl⟩) R94913
theorem R63287 : Reach 63287 := rs (se 1 (by rfl) ⟨47465, by rfl⟩) R94931
theorem R63307 : Reach 63307 := rs (se 1 (by rfl) ⟨47480, by rfl⟩) R94961
theorem R63319 : Reach 63319 := rs (se 1 (by rfl) ⟨47489, by rfl⟩) R94979
theorem R96089 : Reach 96089 := rs (se 2 (by rfl) ⟨36033, by rfl⟩) R72067
theorem R63339 : Reach 63339 := rs (se 1 (by rfl) ⟨47504, by rfl⟩) R95009
theorem R63351 : Reach 63351 := rs (se 1 (by rfl) ⟨47513, by rfl⟩) R95027
theorem R63371 : Reach 63371 := rs (se 1 (by rfl) ⟨47528, by rfl⟩) R95057
theorem R63383 : Reach 63383 := rs (se 1 (by rfl) ⟨47537, by rfl⟩) R95075
theorem R63403 : Reach 63403 := rs (se 1 (by rfl) ⟨47552, by rfl⟩) R95105
theorem R63415 : Reach 63415 := rs (se 1 (by rfl) ⟨47561, by rfl⟩) R95123
theorem R63435 : Reach 63435 := rs (se 1 (by rfl) ⟨47576, by rfl⟩) R95153
theorem R96203 : Reach 96203 := rs (se 1 (by rfl) ⟨72152, by rfl⟩) R144305
theorem R63447 : Reach 63447 := rs (se 1 (by rfl) ⟨47585, by rfl⟩) R95171
theorem R96215 : Reach 96215 := rs (se 1 (by rfl) ⟨72161, by rfl⟩) R144323
theorem R358361 : Reach 358361 := rs (se 2 (by rfl) ⟨134385, by rfl⟩) R268771
theorem R194525 : Reach 194525 := rs (se 3 (by rfl) ⟨36473, by rfl⟩) R72947
theorem R63467 : Reach 63467 := rs (se 1 (by rfl) ⟨47600, by rfl⟩) R95201
theorem R63479 : Reach 63479 := rs (se 1 (by rfl) ⟨47609, by rfl⟩) R95219
theorem R63499 : Reach 63499 := rs (se 1 (by rfl) ⟨47624, by rfl⟩) R95249
theorem R63511 : Reach 63511 := rs (se 1 (by rfl) ⟨47633, by rfl⟩) R95267
theorem R96281 : Reach 96281 := rs (se 2 (by rfl) ⟨36105, by rfl⟩) R72211
theorem R63531 : Reach 63531 := rs (se 1 (by rfl) ⟨47648, by rfl⟩) R95297
theorem R63543 : Reach 63543 := rs (se 1 (by rfl) ⟨47657, by rfl⟩) R95315
theorem R63563 : Reach 63563 := rs (se 1 (by rfl) ⟨47672, by rfl⟩) R95345
theorem R63575 : Reach 63575 := rs (se 1 (by rfl) ⟨47681, by rfl⟩) R95363
theorem R850013 : Reach 850013 := rs (se 3 (by rfl) ⟨159377, by rfl⟩) R318755
theorem R63595 : Reach 63595 := rs (se 1 (by rfl) ⟨47696, by rfl⟩) R95393
theorem R63607 : Reach 63607 := rs (se 1 (by rfl) ⟨47705, by rfl⟩) R95411
theorem R63627 : Reach 63627 := rs (se 1 (by rfl) ⟨47720, by rfl⟩) R95441
theorem R96395 : Reach 96395 := rs (se 1 (by rfl) ⟨72296, by rfl⟩) R144593
theorem R129163 : Reach 129163 := rs (se 1 (by rfl) ⟨96872, by rfl⟩) R193745
theorem R63639 : Reach 63639 := rs (se 1 (by rfl) ⟨47729, by rfl⟩) R95459
theorem R96407 : Reach 96407 := rs (se 1 (by rfl) ⟨72305, by rfl⟩) R144611
theorem R63659 : Reach 63659 := rs (se 1 (by rfl) ⟨47744, by rfl⟩) R95489
theorem R63671 : Reach 63671 := rs (se 1 (by rfl) ⟨47753, by rfl⟩) R95507
theorem R63691 : Reach 63691 := rs (se 1 (by rfl) ⟨47768, by rfl⟩) R95537
theorem R63703 : Reach 63703 := rs (se 1 (by rfl) ⟨47777, by rfl⟩) R95555
theorem R96473 : Reach 96473 := rs (se 2 (by rfl) ⟨36177, by rfl⟩) R72355
theorem R63723 : Reach 63723 := rs (se 1 (by rfl) ⟨47792, by rfl⟩) R95585
theorem R63735 : Reach 63735 := rs (se 1 (by rfl) ⟨47801, by rfl⟩) R95603
theorem R63755 : Reach 63755 := rs (se 1 (by rfl) ⟨47816, by rfl⟩) R95633
theorem R63767 : Reach 63767 := rs (se 1 (by rfl) ⟨47825, by rfl⟩) R95651
theorem R162071 : Reach 162071 := rs (se 1 (by rfl) ⟨121553, by rfl⟩) R243107
theorem R63787 : Reach 63787 := rs (se 1 (by rfl) ⟨47840, by rfl⟩) R95681
theorem R63799 : Reach 63799 := rs (se 1 (by rfl) ⟨47849, by rfl⟩) R95699
theorem R63819 : Reach 63819 := rs (se 1 (by rfl) ⟨47864, by rfl⟩) R95729
theorem R96587 : Reach 96587 := rs (se 1 (by rfl) ⟨72440, by rfl⟩) R144881
theorem R227659 : Reach 227659 := rs (se 1 (by rfl) ⟨170744, by rfl⟩) R341489
theorem R63831 : Reach 63831 := rs (se 1 (by rfl) ⟨47873, by rfl⟩) R95747
theorem R96599 : Reach 96599 := rs (se 1 (by rfl) ⟨72449, by rfl⟩) R144899
theorem R63851 : Reach 63851 := rs (se 1 (by rfl) ⟨47888, by rfl⟩) R95777
theorem R63863 : Reach 63863 := rs (se 1 (by rfl) ⟨47897, by rfl⟩) R95795
theorem R63883 : Reach 63883 := rs (se 1 (by rfl) ⟨47912, by rfl⟩) R95825
theorem R63895 : Reach 63895 := rs (se 1 (by rfl) ⟨47921, by rfl⟩) R95843
theorem R96665 : Reach 96665 := rs (se 2 (by rfl) ⟨36249, by rfl⟩) R72499
theorem R63915 : Reach 63915 := rs (se 1 (by rfl) ⟨47936, by rfl⟩) R95873
theorem R63927 : Reach 63927 := rs (se 1 (by rfl) ⟨47945, by rfl⟩) R95891
theorem R63947 : Reach 63947 := rs (se 1 (by rfl) ⟨47960, by rfl⟩) R95921
theorem R96727 : Reach 96727 := rs (se 1 (by rfl) ⟨72545, by rfl⟩) R145091
theorem R63959 : Reach 63959 := rs (se 1 (by rfl) ⟨47969, by rfl⟩) R95939
theorem R621017 : Reach 621017 := rs (se 2 (by rfl) ⟨232881, by rfl⟩) R465763
theorem R326105 : Reach 326105 := rs (se 2 (by rfl) ⟨122289, by rfl⟩) R244579
theorem R63979 : Reach 63979 := rs (se 1 (by rfl) ⟨47984, by rfl⟩) R95969
theorem R63991 : Reach 63991 := rs (se 1 (by rfl) ⟨47993, by rfl⟩) R95987
theorem R64011 : Reach 64011 := rs (se 1 (by rfl) ⟨48008, by rfl⟩) R96017
theorem R96779 : Reach 96779 := rs (se 1 (by rfl) ⟨72584, by rfl⟩) R145169
theorem R1735181 : Reach 1735181 := rs (se 3 (by rfl) ⟨325346, by rfl⟩) R650693
theorem R64023 : Reach 64023 := rs (se 1 (by rfl) ⟨48017, by rfl⟩) R96035
theorem R96791 : Reach 96791 := rs (se 1 (by rfl) ⟨72593, by rfl⟩) R145187
theorem R64043 : Reach 64043 := rs (se 1 (by rfl) ⟨48032, by rfl⟩) R96065
theorem R64055 : Reach 64055 := rs (se 1 (by rfl) ⟨48041, by rfl⟩) R96083
theorem R64075 : Reach 64075 := rs (se 1 (by rfl) ⟨48056, by rfl⟩) R96113
theorem R64087 : Reach 64087 := rs (se 1 (by rfl) ⟨48065, by rfl⟩) R96131
theorem R96857 : Reach 96857 := rs (se 2 (by rfl) ⟨36321, by rfl⟩) R72643
theorem R64107 : Reach 64107 := rs (se 1 (by rfl) ⟨48080, by rfl⟩) R96161
theorem R64119 : Reach 64119 := rs (se 1 (by rfl) ⟨48089, by rfl⟩) R96179
theorem R64139 : Reach 64139 := rs (se 1 (by rfl) ⟨48104, by rfl⟩) R96209
theorem R64151 : Reach 64151 := rs (se 1 (by rfl) ⟨48113, by rfl⟩) R96227
theorem R64171 : Reach 64171 := rs (se 1 (by rfl) ⟨48128, by rfl⟩) R96257
theorem R64183 : Reach 64183 := rs (se 1 (by rfl) ⟨48137, by rfl⟩) R96275
theorem R64203 : Reach 64203 := rs (se 1 (by rfl) ⟨48152, by rfl⟩) R96305
theorem R96971 : Reach 96971 := rs (se 1 (by rfl) ⟨72728, by rfl⟩) R145457
theorem R1080013 : Reach 1080013 := rs (se 3 (by rfl) ⟨202502, by rfl⟩) R405005
theorem R64215 : Reach 64215 := rs (se 1 (by rfl) ⟨48161, by rfl⟩) R96323
theorem R96983 : Reach 96983 := rs (se 1 (by rfl) ⟨72737, by rfl⟩) R145475
theorem R64235 : Reach 64235 := rs (se 1 (by rfl) ⟨48176, by rfl⟩) R96353
theorem R64247 : Reach 64247 := rs (se 1 (by rfl) ⟨48185, by rfl⟩) R96371
theorem R64267 : Reach 64267 := rs (se 1 (by rfl) ⟨48200, by rfl⟩) R96401
theorem R64279 : Reach 64279 := rs (se 1 (by rfl) ⟨48209, by rfl⟩) R96419
theorem R97049 : Reach 97049 := rs (se 2 (by rfl) ⟨36393, by rfl⟩) R72787
theorem R64299 : Reach 64299 := rs (se 1 (by rfl) ⟨48224, by rfl⟩) R96449
theorem R64311 : Reach 64311 := rs (se 1 (by rfl) ⟨48233, by rfl⟩) R96467
theorem R64331 : Reach 64331 := rs (se 1 (by rfl) ⟨48248, by rfl⟩) R96497
theorem R64343 : Reach 64343 := rs (se 1 (by rfl) ⟨48257, by rfl⟩) R96515
theorem R64363 : Reach 64363 := rs (se 1 (by rfl) ⟨48272, by rfl⟩) R96545
theorem R64375 : Reach 64375 := rs (se 1 (by rfl) ⟨48281, by rfl⟩) R96563
theorem R64395 : Reach 64395 := rs (se 1 (by rfl) ⟨48296, by rfl⟩) R96593
theorem R97163 : Reach 97163 := rs (se 1 (by rfl) ⟨72872, by rfl⟩) R145745
theorem R64407 : Reach 64407 := rs (se 1 (by rfl) ⟨48305, by rfl⟩) R96611
theorem R97175 : Reach 97175 := rs (se 1 (by rfl) ⟨72881, by rfl⟩) R145763
theorem R64427 : Reach 64427 := rs (se 1 (by rfl) ⟨48320, by rfl⟩) R96641
theorem R64439 : Reach 64439 := rs (se 1 (by rfl) ⟨48329, by rfl⟩) R96659
theorem R64459 : Reach 64459 := rs (se 1 (by rfl) ⟨48344, by rfl⟩) R96689
theorem R130007 : Reach 130007 := rs (se 1 (by rfl) ⟨97505, by rfl⟩) R195011
theorem R64471 : Reach 64471 := rs (se 1 (by rfl) ⟨48353, by rfl⟩) R96707
theorem R97241 : Reach 97241 := rs (se 2 (by rfl) ⟨36465, by rfl⟩) R72931
theorem R64491 : Reach 64491 := rs (se 1 (by rfl) ⟨48368, by rfl⟩) R96737
theorem R64503 : Reach 64503 := rs (se 1 (by rfl) ⟨48377, by rfl⟩) R96755
theorem R64523 : Reach 64523 := rs (se 1 (by rfl) ⟨48392, by rfl⟩) R96785
theorem R64535 : Reach 64535 := rs (se 1 (by rfl) ⟨48401, by rfl⟩) R96803
theorem R64555 : Reach 64555 := rs (se 1 (by rfl) ⟨48416, by rfl⟩) R96833
theorem R64567 : Reach 64567 := rs (se 1 (by rfl) ⟨48425, by rfl⟩) R96851
theorem R162881 : Reach 162881 := rs (se 2 (by rfl) ⟨61080, by rfl⟩) R122161
theorem R64587 : Reach 64587 := rs (se 1 (by rfl) ⟨48440, by rfl⟩) R96881
theorem R97355 : Reach 97355 := rs (se 1 (by rfl) ⟨73016, by rfl⟩) R146033
theorem R64599 : Reach 64599 := rs (se 1 (by rfl) ⟨48449, by rfl⟩) R96899
theorem R97367 : Reach 97367 := rs (se 1 (by rfl) ⟨73025, by rfl⟩) R146051
theorem R293977 : Reach 293977 := rs (se 2 (by rfl) ⟨110241, by rfl⟩) R220483
theorem R64619 : Reach 64619 := rs (se 1 (by rfl) ⟨48464, by rfl⟩) R96929
theorem R64631 : Reach 64631 := rs (se 1 (by rfl) ⟨48473, by rfl⟩) R96947
theorem R1145987 : Reach 1145987 := rs (se 1 (by rfl) ⟨859490, by rfl⟩) R1718981
theorem R64651 : Reach 64651 := rs (se 1 (by rfl) ⟨48488, by rfl⟩) R96977
theorem R64663 : Reach 64663 := rs (se 1 (by rfl) ⟨48497, by rfl⟩) R96995
theorem R97433 : Reach 97433 := rs (se 2 (by rfl) ⟨36537, by rfl⟩) R73075
theorem R64683 : Reach 64683 := rs (se 1 (by rfl) ⟨48512, by rfl⟩) R97025
theorem R64695 : Reach 64695 := rs (se 1 (by rfl) ⟨48521, by rfl⟩) R97043
theorem R64715 : Reach 64715 := rs (se 1 (by rfl) ⟨48536, by rfl⟩) R97073
theorem R64727 : Reach 64727 := rs (se 1 (by rfl) ⟨48545, by rfl⟩) R97091
theorem R64747 : Reach 64747 := rs (se 1 (by rfl) ⟨48560, by rfl⟩) R97121
theorem R64759 : Reach 64759 := rs (se 1 (by rfl) ⟨48569, by rfl⟩) R97139
theorem R64779 : Reach 64779 := rs (se 1 (by rfl) ⟨48584, by rfl⟩) R97169
theorem R97547 : Reach 97547 := rs (se 1 (by rfl) ⟨73160, by rfl⟩) R146321
theorem R64791 : Reach 64791 := rs (se 1 (by rfl) ⟨48593, by rfl⟩) R97187
theorem R97559 : Reach 97559 := rs (se 1 (by rfl) ⟨73169, by rfl⟩) R146339
theorem R64811 : Reach 64811 := rs (se 1 (by rfl) ⟨48608, by rfl⟩) R97217
theorem R64823 : Reach 64823 := rs (se 1 (by rfl) ⟨48617, by rfl⟩) R97235
theorem R64843 : Reach 64843 := rs (se 1 (by rfl) ⟨48632, by rfl⟩) R97265
theorem R64855 : Reach 64855 := rs (se 1 (by rfl) ⟨48641, by rfl⟩) R97283
theorem R97625 : Reach 97625 := rs (se 2 (by rfl) ⟨36609, by rfl⟩) R73219
theorem R64875 : Reach 64875 := rs (se 1 (by rfl) ⟨48656, by rfl⟩) R97313
theorem R64887 : Reach 64887 := rs (se 1 (by rfl) ⟨48665, by rfl⟩) R97331
theorem R64907 : Reach 64907 := rs (se 1 (by rfl) ⟨48680, by rfl⟩) R97361
theorem R64919 : Reach 64919 := rs (se 1 (by rfl) ⟨48689, by rfl⟩) R97379
theorem R64939 : Reach 64939 := rs (se 1 (by rfl) ⟨48704, by rfl⟩) R97409
theorem R64951 : Reach 64951 := rs (se 1 (by rfl) ⟨48713, by rfl⟩) R97427
theorem R64971 : Reach 64971 := rs (se 1 (by rfl) ⟨48728, by rfl⟩) R97457
theorem R97739 : Reach 97739 := rs (se 1 (by rfl) ⟨73304, by rfl⟩) R146609
theorem R64983 : Reach 64983 := rs (se 1 (by rfl) ⟨48737, by rfl⟩) R97475
theorem R97751 : Reach 97751 := rs (se 1 (by rfl) ⟨73313, by rfl⟩) R146627
theorem R65003 : Reach 65003 := rs (se 1 (by rfl) ⟨48752, by rfl⟩) R97505
theorem R65015 : Reach 65015 := rs (se 1 (by rfl) ⟨48761, by rfl⟩) R97523
theorem R65035 : Reach 65035 := rs (se 1 (by rfl) ⟨48776, by rfl⟩) R97553
theorem R65047 : Reach 65047 := rs (se 1 (by rfl) ⟨48785, by rfl⟩) R97571
theorem R97817 : Reach 97817 := rs (se 2 (by rfl) ⟨36681, by rfl⟩) R73363
theorem R65067 : Reach 65067 := rs (se 1 (by rfl) ⟨48800, by rfl⟩) R97601
theorem R65079 : Reach 65079 := rs (se 1 (by rfl) ⟨48809, by rfl⟩) R97619
theorem R65099 : Reach 65099 := rs (se 1 (by rfl) ⟨48824, by rfl⟩) R97649
theorem R65111 : Reach 65111 := rs (se 1 (by rfl) ⟨48833, by rfl⟩) R97667
theorem R163417 : Reach 163417 := rs (se 2 (by rfl) ⟨61281, by rfl⟩) R122563
theorem R65131 : Reach 65131 := rs (se 1 (by rfl) ⟨48848, by rfl⟩) R97697
theorem R65143 : Reach 65143 := rs (se 1 (by rfl) ⟨48857, by rfl⟩) R97715
theorem R65163 : Reach 65163 := rs (se 1 (by rfl) ⟨48872, by rfl⟩) R97745
theorem R97931 : Reach 97931 := rs (se 1 (by rfl) ⟨73448, by rfl⟩) R146897
theorem R65175 : Reach 65175 := rs (se 1 (by rfl) ⟨48881, by rfl⟩) R97763
theorem R97943 : Reach 97943 := rs (se 1 (by rfl) ⟨73457, by rfl⟩) R146915
theorem R65195 : Reach 65195 := rs (se 1 (by rfl) ⟨48896, by rfl⟩) R97793
theorem R65207 : Reach 65207 := rs (se 1 (by rfl) ⟨48905, by rfl⟩) R97811
theorem R65227 : Reach 65227 := rs (se 1 (by rfl) ⟨48920, by rfl⟩) R97841
theorem R65239 : Reach 65239 := rs (se 1 (by rfl) ⟨48929, by rfl⟩) R97859
theorem R98009 : Reach 98009 := rs (se 2 (by rfl) ⟨36753, by rfl⟩) R73507
theorem R65259 : Reach 65259 := rs (se 1 (by rfl) ⟨48944, by rfl⟩) R97889
theorem R65271 : Reach 65271 := rs (se 1 (by rfl) ⟨48953, by rfl⟩) R97907
theorem R65291 : Reach 65291 := rs (se 1 (by rfl) ⟨48968, by rfl⟩) R97937
theorem R65303 : Reach 65303 := rs (se 1 (by rfl) ⟨48977, by rfl⟩) R97955
theorem R65323 : Reach 65323 := rs (se 1 (by rfl) ⟨48992, by rfl⟩) R97985
theorem R65335 : Reach 65335 := rs (se 1 (by rfl) ⟨49001, by rfl⟩) R98003
theorem R556865 : Reach 556865 := rs (se 2 (by rfl) ⟨208824, by rfl⟩) R417649
theorem R65355 : Reach 65355 := rs (se 1 (by rfl) ⟨49016, by rfl⟩) R98033
theorem R98123 : Reach 98123 := rs (se 1 (by rfl) ⟨73592, by rfl⟩) R147185
theorem R98135 : Reach 98135 := rs (se 1 (by rfl) ⟨73601, by rfl⟩) R147203
theorem R65367 : Reach 65367 := rs (se 1 (by rfl) ⟨49025, by rfl⟩) R98051
theorem R65387 : Reach 65387 := rs (se 1 (by rfl) ⟨49040, by rfl⟩) R98081
theorem R65399 : Reach 65399 := rs (se 1 (by rfl) ⟨49049, by rfl⟩) R98099
theorem R65419 : Reach 65419 := rs (se 1 (by rfl) ⟨49064, by rfl⟩) R98129
theorem R65431 : Reach 65431 := rs (se 1 (by rfl) ⟨49073, by rfl⟩) R98147
theorem R98201 : Reach 98201 := rs (se 2 (by rfl) ⟨36825, by rfl⟩) R73651
theorem R65451 : Reach 65451 := rs (se 1 (by rfl) ⟨49088, by rfl⟩) R98177
theorem R1343411 : Reach 1343411 := rs (se 1 (by rfl) ⟨1007558, by rfl⟩) R2015117
theorem R65463 : Reach 65463 := rs (se 1 (by rfl) ⟨49097, by rfl⟩) R98195
theorem R65483 : Reach 65483 := rs (se 1 (by rfl) ⟨49112, by rfl⟩) R98225
theorem R65495 : Reach 65495 := rs (se 1 (by rfl) ⟨49121, by rfl⟩) R98243
theorem R65515 : Reach 65515 := rs (se 1 (by rfl) ⟨49136, by rfl⟩) R98273
theorem R65527 : Reach 65527 := rs (se 1 (by rfl) ⟨49145, by rfl⟩) R98291
theorem R65543 : Reach 65543 := rs (se 1 (by rfl) ⟨49157, by rfl⟩) R98315
theorem R65551 : Reach 65551 := rs (se 1 (by rfl) ⟨49163, by rfl⟩) R98327
theorem R163883 : Reach 163883 := rs (se 1 (by rfl) ⟨122912, by rfl⟩) R245825
theorem R98363 : Reach 98363 := rs (se 1 (by rfl) ⟨73772, by rfl⟩) R147545
theorem R65595 : Reach 65595 := rs (se 1 (by rfl) ⟨49196, by rfl⟩) R98393
theorem R98423 : Reach 98423 := rs (se 1 (by rfl) ⟨73817, by rfl⟩) R147635
theorem R65671 : Reach 65671 := rs (se 1 (by rfl) ⟨49253, by rfl⟩) R98507
theorem R98447 : Reach 98447 := rs (se 1 (by rfl) ⟨73835, by rfl⟩) R147671
theorem R65679 : Reach 65679 := rs (se 1 (by rfl) ⟨49259, by rfl⟩) R98519
theorem R98489 : Reach 98489 := rs (se 2 (by rfl) ⟨36933, by rfl⟩) R73867
theorem R65723 : Reach 65723 := rs (se 1 (by rfl) ⟨49292, by rfl⟩) R98585
theorem R98567 : Reach 98567 := rs (se 1 (by rfl) ⟨73925, by rfl⟩) R147851
theorem R65799 : Reach 65799 := rs (se 1 (by rfl) ⟨49349, by rfl⟩) R98699
theorem R360719 : Reach 360719 := rs (se 1 (by rfl) ⟨270539, by rfl⟩) R541079
theorem R65807 : Reach 65807 := rs (se 1 (by rfl) ⟨49355, by rfl⟩) R98711
theorem R98603 : Reach 98603 := rs (se 1 (by rfl) ⟨73952, by rfl⟩) R147905
theorem R131387 : Reach 131387 := rs (se 1 (by rfl) ⟨98540, by rfl⟩) R197081
theorem R65851 : Reach 65851 := rs (se 1 (by rfl) ⟨49388, by rfl⟩) R98777
theorem R98633 : Reach 98633 := rs (se 2 (by rfl) ⟨36987, by rfl⟩) R73975
theorem R65927 : Reach 65927 := rs (se 1 (by rfl) ⟨49445, by rfl⟩) R98891
theorem R65935 : Reach 65935 := rs (se 1 (by rfl) ⟨49451, by rfl⟩) R98903
theorem R98747 : Reach 98747 := rs (se 1 (by rfl) ⟨74060, by rfl⟩) R148121
theorem R65979 : Reach 65979 := rs (se 1 (by rfl) ⟨49484, by rfl⟩) R98969
theorem R229841 : Reach 229841 := rs (se 2 (by rfl) ⟨86190, by rfl⟩) R172381
theorem R98807 : Reach 98807 := rs (se 1 (by rfl) ⟨74105, by rfl⟩) R148211
theorem R66055 : Reach 66055 := rs (se 1 (by rfl) ⟨49541, by rfl⟩) R99083
theorem R98831 : Reach 98831 := rs (se 1 (by rfl) ⟨74123, by rfl⟩) R148247
theorem R66063 : Reach 66063 := rs (se 1 (by rfl) ⟨49547, by rfl⟩) R99095
theorem R98873 : Reach 98873 := rs (se 2 (by rfl) ⟨37077, by rfl⟩) R74155
theorem R66107 : Reach 66107 := rs (se 1 (by rfl) ⟨49580, by rfl⟩) R99161
theorem R262723 : Reach 262723 := rs (se 1 (by rfl) ⟨197042, by rfl⟩) R394085
theorem R393815 : Reach 393815 := rs (se 1 (by rfl) ⟨295361, by rfl⟩) R590723
theorem R98951 : Reach 98951 := rs (se 1 (by rfl) ⟨74213, by rfl⟩) R148427
theorem R66183 : Reach 66183 := rs (se 1 (by rfl) ⟨49637, by rfl⟩) R99275
theorem R66191 : Reach 66191 := rs (se 1 (by rfl) ⟨49643, by rfl⟩) R99287
theorem R98987 : Reach 98987 := rs (se 1 (by rfl) ⟨74240, by rfl⟩) R148481
theorem R66235 : Reach 66235 := rs (se 1 (by rfl) ⟨49676, by rfl⟩) R99353
theorem R99017 : Reach 99017 := rs (se 2 (by rfl) ⟨37131, by rfl⟩) R74263
theorem R66311 : Reach 66311 := rs (se 1 (by rfl) ⟨49733, by rfl⟩) R99467
theorem R66319 : Reach 66319 := rs (se 1 (by rfl) ⟨49739, by rfl⟩) R99479
theorem R99131 : Reach 99131 := rs (se 1 (by rfl) ⟨74348, by rfl⟩) R148697
theorem R66363 : Reach 66363 := rs (se 1 (by rfl) ⟨49772, by rfl⟩) R99545
theorem R99191 : Reach 99191 := rs (se 1 (by rfl) ⟨74393, by rfl⟩) R148787
theorem R66439 : Reach 66439 := rs (se 1 (by rfl) ⟨49829, by rfl⟩) R99659
theorem R99215 : Reach 99215 := rs (se 1 (by rfl) ⟨74411, by rfl⟩) R148823
theorem R66447 : Reach 66447 := rs (se 1 (by rfl) ⟨49835, by rfl⟩) R99671
theorem R99257 : Reach 99257 := rs (se 2 (by rfl) ⟨37221, by rfl⟩) R74443
theorem R66491 : Reach 66491 := rs (se 1 (by rfl) ⟨49868, by rfl⟩) R99737
theorem R99335 : Reach 99335 := rs (se 1 (by rfl) ⟨74501, by rfl⟩) R149003
theorem R66567 : Reach 66567 := rs (se 1 (by rfl) ⟨49925, by rfl⟩) R99851
theorem R164875 : Reach 164875 := rs (se 1 (by rfl) ⟨123656, by rfl⟩) R247313
theorem R66575 : Reach 66575 := rs (se 1 (by rfl) ⟨49931, by rfl⟩) R99863
theorem R99371 : Reach 99371 := rs (se 1 (by rfl) ⟨74528, by rfl⟩) R149057
theorem R66619 : Reach 66619 := rs (se 1 (by rfl) ⟨49964, by rfl⟩) R99929
theorem R99401 : Reach 99401 := rs (se 2 (by rfl) ⟨37275, by rfl⟩) R74551
theorem R66695 : Reach 66695 := rs (se 1 (by rfl) ⟨50021, by rfl⟩) R100043
theorem R66703 : Reach 66703 := rs (se 1 (by rfl) ⟨50027, by rfl⟩) R100055
theorem R165017 : Reach 165017 := rs (se 2 (by rfl) ⟨61881, by rfl⟩) R123763
theorem R99515 : Reach 99515 := rs (se 1 (by rfl) ⟨74636, by rfl⟩) R149273
theorem R66747 : Reach 66747 := rs (se 1 (by rfl) ⟨50060, by rfl⟩) R100121
theorem R394433 : Reach 394433 := rs (se 2 (by rfl) ⟨147912, by rfl⟩) R295825
theorem R99575 : Reach 99575 := rs (se 1 (by rfl) ⟨74681, by rfl⟩) R149363
theorem R328961 : Reach 328961 := rs (se 2 (by rfl) ⟨123360, by rfl⟩) R246721
theorem R66823 : Reach 66823 := rs (se 1 (by rfl) ⟨50117, by rfl⟩) R100235
theorem R99599 : Reach 99599 := rs (se 1 (by rfl) ⟨74699, by rfl⟩) R149399
theorem R66831 : Reach 66831 := rs (se 1 (by rfl) ⟨50123, by rfl⟩) R100247
theorem R99641 : Reach 99641 := rs (se 2 (by rfl) ⟨37365, by rfl⟩) R74731
theorem R165179 : Reach 165179 := rs (se 1 (by rfl) ⟨123884, by rfl⟩) R247769
theorem R66875 : Reach 66875 := rs (se 1 (by rfl) ⟨50156, by rfl⟩) R100313
theorem R99719 : Reach 99719 := rs (se 1 (by rfl) ⟨74789, by rfl⟩) R149579
theorem R66951 : Reach 66951 := rs (se 1 (by rfl) ⟨50213, by rfl⟩) R100427
theorem R66959 : Reach 66959 := rs (se 1 (by rfl) ⟨50219, by rfl⟩) R100439
theorem R67003 : Reach 67003 := rs (se 1 (by rfl) ⟨50252, by rfl⟩) R100505
theorem R99785 : Reach 99785 := rs (se 2 (by rfl) ⟨37419, by rfl⟩) R74839
theorem R67079 : Reach 67079 := rs (se 1 (by rfl) ⟨50309, by rfl⟩) R100619
theorem R67087 : Reach 67087 := rs (se 1 (by rfl) ⟨50315, by rfl⟩) R100631
theorem R886301 : Reach 886301 := rs (se 3 (by rfl) ⟨166181, by rfl⟩) R332363
theorem R755243 : Reach 755243 := rs (se 1 (by rfl) ⟨566432, by rfl⟩) R1132865
theorem R99899 : Reach 99899 := rs (se 1 (by rfl) ⟨74924, by rfl⟩) R149849
theorem R886373 : Reach 886373 := rs (se 4 (by rfl) ⟨83097, by rfl⟩) R166195
theorem R99959 : Reach 99959 := rs (se 1 (by rfl) ⟨74969, by rfl⟩) R149939
theorem R165523 : Reach 165523 := rs (se 1 (by rfl) ⟨124142, by rfl⟩) R248285
theorem R100025 : Reach 100025 := rs (se 2 (by rfl) ⟨37509, by rfl⟩) R75019
theorem R362177 : Reach 362177 := rs (se 2 (by rfl) ⟨135816, by rfl⟩) R271633
theorem R165665 : Reach 165665 := rs (se 2 (by rfl) ⟨62124, by rfl⟩) R124249
theorem R100139 : Reach 100139 := rs (se 1 (by rfl) ⟨75104, by rfl⟩) R150209
theorem R231353 : Reach 231353 := rs (se 2 (by rfl) ⟨86757, by rfl⟩) R173515
theorem R133049 : Reach 133049 := rs (se 2 (by rfl) ⟨49893, by rfl⟩) R99787
theorem R100367 : Reach 100367 := rs (se 1 (by rfl) ⟨75275, by rfl⟩) R150551
theorem R100487 : Reach 100487 := rs (se 1 (by rfl) ⟨75365, by rfl⟩) R150731
theorem R100553 : Reach 100553 := rs (se 2 (by rfl) ⟨37707, by rfl⟩) R75415
theorem R330043 : Reach 330043 := rs (se 1 (by rfl) ⟨247532, by rfl⟩) R495065
theorem R100667 : Reach 100667 := rs (se 1 (by rfl) ⟨75500, by rfl⟩) R151001
theorem R231815 : Reach 231815 := rs (se 1 (by rfl) ⟨173861, by rfl⟩) R347723
theorem R428773 : Reach 428773 := rs (se 4 (by rfl) ⟨40197, by rfl⟩) R80395
theorem R166657 : Reach 166657 := rs (se 2 (by rfl) ⟨62496, by rfl⟩) R124993
theorem R6195973 : Reach 6195973 := rs (se 4 (by rfl) ⟨580872, by rfl⟩) R1161745
theorem R199439 : Reach 199439 := rs (se 1 (by rfl) ⟨149579, by rfl⟩) R299159
theorem R101179 : Reach 101179 := rs (se 1 (by rfl) ⟨75884, by rfl⟩) R151769
theorem R330641 : Reach 330641 := rs (se 2 (by rfl) ⟨123990, by rfl⟩) R247981
theorem R592919 : Reach 592919 := rs (se 1 (by rfl) ⟨444689, by rfl⟩) R889379
theorem R167255 : Reach 167255 := rs (se 1 (by rfl) ⟨125441, by rfl⟩) R250883
theorem R167467 : Reach 167467 := rs (se 1 (by rfl) ⟨125600, by rfl⟩) R251201
theorem R167609 : Reach 167609 := rs (se 2 (by rfl) ⟨62853, by rfl⟩) R125707
theorem R266017 : Reach 266017 := rs (se 2 (by rfl) ⟨99756, by rfl⟩) R199513
theorem R429977 : Reach 429977 := rs (se 2 (by rfl) ⟨161241, by rfl⟩) R322483
theorem R561239 : Reach 561239 := rs (se 1 (by rfl) ⟨420929, by rfl⟩) R841859
theorem R135287 : Reach 135287 := rs (se 1 (by rfl) ⟨101465, by rfl⟩) R202931
theorem R70151 : Reach 70151 := rs (se 1 (by rfl) ⟨52613, by rfl⟩) R105227
theorem R496205 : Reach 496205 := rs (se 3 (by rfl) ⟨93038, by rfl⟩) R186077
theorem R168601 : Reach 168601 := rs (se 2 (by rfl) ⟨63225, by rfl⟩) R126451
theorem R168763 : Reach 168763 := rs (se 1 (by rfl) ⟨126572, by rfl⟩) R253145
theorem R398195 : Reach 398195 := rs (se 1 (by rfl) ⟨298646, by rfl⟩) R597293
theorem R168905 : Reach 168905 := rs (se 2 (by rfl) ⟨63339, by rfl⟩) R126679
theorem R332747 : Reach 332747 := rs (se 1 (by rfl) ⟨249560, by rfl⟩) R499121
theorem R594955 : Reach 594955 := rs (se 1 (by rfl) ⟨446216, by rfl⟩) R892433
theorem R103439 : Reach 103439 := rs (se 1 (by rfl) ⟨77579, by rfl⟩) R155159
theorem R1283309 : Reach 1283309 := rs (se 3 (by rfl) ⟨240620, by rfl⟩) R481241
theorem R333071 : Reach 333071 := rs (se 1 (by rfl) ⟨249803, by rfl⟩) R499607
theorem R169249 : Reach 169249 := rs (se 2 (by rfl) ⟨63468, by rfl⟩) R126937
theorem R169303 : Reach 169303 := rs (se 1 (by rfl) ⟨126977, by rfl⟩) R253955
theorem R103951 : Reach 103951 := rs (se 1 (by rfl) ⟨77963, by rfl⟩) R155927
theorem R661069 : Reach 661069 := rs (se 3 (by rfl) ⟨123950, by rfl⟩) R247901
theorem R71311 : Reach 71311 := rs (se 1 (by rfl) ⟨53483, by rfl⟩) R106967
theorem R169847 : Reach 169847 := rs (se 1 (by rfl) ⟨127385, by rfl⟩) R254771
theorem R333827 : Reach 333827 := rs (se 1 (by rfl) ⟨250370, by rfl⟩) R500741
theorem R71815 : Reach 71815 := rs (se 1 (by rfl) ⟨53861, by rfl⟩) R107723
theorem R71995 : Reach 71995 := rs (se 1 (by rfl) ⟨53996, by rfl⟩) R107993
theorem R367051 : Reach 367051 := rs (se 1 (by rfl) ⟨275288, by rfl⟩) R550577
theorem R105079 : Reach 105079 := rs (se 1 (by rfl) ⟨78809, by rfl⟩) R157619
theorem R334529 : Reach 334529 := rs (se 2 (by rfl) ⟨125448, by rfl⟩) R250897
theorem R72463 : Reach 72463 := rs (se 1 (by rfl) ⟨54347, by rfl⟩) R108695
theorem R498635 : Reach 498635 := rs (se 1 (by rfl) ⟨373976, by rfl⟩) R747953
theorem R236573 : Reach 236573 := rs (se 3 (by rfl) ⟨44357, by rfl⟩) R88715
theorem R72967 : Reach 72967 := rs (se 1 (by rfl) ⟨54725, by rfl⟩) R109451
theorem R73147 : Reach 73147 := rs (se 1 (by rfl) ⟨54860, by rfl⟩) R109721
theorem R466397 : Reach 466397 := rs (se 3 (by rfl) ⟨87449, by rfl⟩) R174899
theorem R269891 : Reach 269891 := rs (se 1 (by rfl) ⟨202418, by rfl⟩) R404837
theorem R1089125 : Reach 1089125 := rs (se 4 (by rfl) ⟨102105, by rfl⟩) R204211
theorem R204545 : Reach 204545 := rs (se 2 (by rfl) ⟨76704, by rfl⟩) R153409
theorem R73615 : Reach 73615 := rs (se 1 (by rfl) ⟨55211, by rfl⟩) R110423
theorem R335825 : Reach 335825 := rs (se 2 (by rfl) ⟨125934, by rfl⟩) R251869
theorem R106555 : Reach 106555 := rs (se 1 (by rfl) ⟨79916, by rfl⟩) R159833
theorem R172217 : Reach 172217 := rs (se 2 (by rfl) ⟨64581, by rfl⟩) R129163
theorem R106697 : Reach 106697 := rs (se 2 (by rfl) ⟨40011, by rfl⟩) R80023
theorem R74119 : Reach 74119 := rs (se 1 (by rfl) ⟨55589, by rfl⟩) R111179
theorem R303545 : Reach 303545 := rs (se 2 (by rfl) ⟨113829, by rfl⟩) R227659
theorem R74299 : Reach 74299 := rs (se 1 (by rfl) ⟨55724, by rfl⟩) R111449
theorem R631475 : Reach 631475 := rs (se 1 (by rfl) ⟨473606, by rfl⟩) R947213
theorem R139961 : Reach 139961 := rs (se 2 (by rfl) ⟨52485, by rfl⟩) R104971
theorem R402149 : Reach 402149 := rs (se 4 (by rfl) ⟨37701, by rfl⟩) R75403
theorem R533263 : Reach 533263 := rs (se 1 (by rfl) ⟨399947, by rfl⟩) R799895
theorem R369467 : Reach 369467 := rs (se 1 (by rfl) ⟨277100, by rfl⟩) R554201
theorem R107399 : Reach 107399 := rs (se 1 (by rfl) ⟨80549, by rfl⟩) R161099
theorem R74767 : Reach 74767 := rs (se 1 (by rfl) ⟨56075, by rfl⟩) R112151
theorem R7611479 : Reach 7611479 := rs (se 1 (by rfl) ⟨5708609, by rfl⟩) R11417219
theorem R238907 : Reach 238907 := rs (se 1 (by rfl) ⟨179180, by rfl⟩) R358361
theorem R75127 : Reach 75127 := rs (se 1 (by rfl) ⟨56345, by rfl⟩) R112691
theorem R1254791 : Reach 1254791 := rs (se 1 (by rfl) ⟨941093, by rfl⟩) R1882187
theorem R566675 : Reach 566675 := rs (se 1 (by rfl) ⟨425006, by rfl⟩) R850013
theorem R632285 : Reach 632285 := rs (se 3 (by rfl) ⟨118553, by rfl⟩) R237107
theorem R75271 : Reach 75271 := rs (se 1 (by rfl) ⟨56453, by rfl⟩) R112907
theorem R108047 : Reach 108047 := rs (se 1 (by rfl) ⟨81035, by rfl⟩) R162071
theorem R75307 : Reach 75307 := rs (se 1 (by rfl) ⟨56480, by rfl⟩) R112961
theorem R1156787 : Reach 1156787 := rs (se 1 (by rfl) ⟨867590, by rfl⟩) R1735181
theorem R75451 : Reach 75451 := rs (se 1 (by rfl) ⟨56588, by rfl⟩) R113177
theorem R206651 : Reach 206651 := rs (se 1 (by rfl) ⟨154988, by rfl⟩) R309977
theorem R337931 : Reach 337931 := rs (se 1 (by rfl) ⟨253448, by rfl⟩) R506897
theorem R108587 : Reach 108587 := rs (se 1 (by rfl) ⟨81440, by rfl⟩) R162881
theorem R763991 : Reach 763991 := rs (se 1 (by rfl) ⟨572993, by rfl⟩) R1145987
theorem R338093 : Reach 338093 := rs (se 3 (by rfl) ⟨63392, by rfl⟩) R126785
theorem R370925 : Reach 370925 := rs (se 3 (by rfl) ⟨69548, by rfl⟩) R139097
theorem R141601 : Reach 141601 := rs (se 2 (by rfl) ⟨53100, by rfl⟩) R106201
theorem R108985 : Reach 108985 := rs (se 2 (by rfl) ⟨40869, by rfl⟩) R81739
theorem R371243 : Reach 371243 := rs (se 1 (by rfl) ⟨278432, by rfl⟩) R556865
theorem R895607 : Reach 895607 := rs (se 1 (by rfl) ⟨671705, by rfl⟩) R1343411
theorem R142199 : Reach 142199 := rs (se 1 (by rfl) ⟨106649, by rfl⟩) R213299
theorem R338897 : Reach 338897 := rs (se 2 (by rfl) ⟨127086, by rfl⟩) R254173
theorem R371735 : Reach 371735 := rs (se 1 (by rfl) ⟨278801, by rfl⟩) R557603
theorem R142379 : Reach 142379 := rs (se 1 (by rfl) ⟨106784, by rfl⟩) R213569
theorem R109687 : Reach 109687 := rs (se 1 (by rfl) ⟨82265, by rfl⟩) R164531
theorem R109883 : Reach 109883 := rs (se 1 (by rfl) ⟨82412, by rfl⟩) R164825
theorem R142651 : Reach 142651 := rs (se 1 (by rfl) ⟨106988, by rfl⟩) R213977
theorem R142739 : Reach 142739 := rs (se 1 (by rfl) ⟨107054, by rfl⟩) R214109
theorem R142793 : Reach 142793 := rs (se 2 (by rfl) ⟨53547, by rfl⟩) R107095
theorem R1420753 : Reach 1420753 := rs (se 2 (by rfl) ⟨532782, by rfl⟩) R1065565
theorem R241163 : Reach 241163 := rs (se 1 (by rfl) ⟨180872, by rfl⟩) R361745
theorem R77483 : Reach 77483 := rs (se 1 (by rfl) ⟨58112, by rfl⟩) R116225
theorem R110281 : Reach 110281 := rs (se 2 (by rfl) ⟨41355, by rfl⟩) R82711
theorem R634625 : Reach 634625 := rs (se 2 (by rfl) ⟨237984, by rfl⟩) R475969
theorem R339713 : Reach 339713 := rs (se 2 (by rfl) ⟨127392, by rfl⟩) R254785
theorem R143147 : Reach 143147 := rs (se 1 (by rfl) ⟨107360, by rfl⟩) R214721
theorem R110521 : Reach 110521 := rs (se 2 (by rfl) ⟨41445, by rfl⟩) R82891
theorem R372701 : Reach 372701 := rs (se 3 (by rfl) ⟨69881, by rfl⟩) R139763
theorem R143495 : Reach 143495 := rs (se 1 (by rfl) ⟨107621, by rfl⟩) R215243
theorem R503981 : Reach 503981 := rs (se 3 (by rfl) ⟨94496, by rfl⟩) R188993
theorem R307471 : Reach 307471 := rs (se 1 (by rfl) ⟨230603, by rfl⟩) R461207
theorem R176413 : Reach 176413 := rs (se 3 (by rfl) ⟨33077, by rfl⟩) R66155
theorem R143675 : Reach 143675 := rs (se 1 (by rfl) ⟨107756, by rfl⟩) R215513
theorem R373081 : Reach 373081 := rs (se 2 (by rfl) ⟨139905, by rfl⟩) R279811
theorem R110983 : Reach 110983 := rs (se 1 (by rfl) ⟨83237, by rfl⟩) R166475
theorem R143801 : Reach 143801 := rs (se 2 (by rfl) ⟨53925, by rfl⟩) R107851
theorem R144143 : Reach 144143 := rs (se 1 (by rfl) ⟨108107, by rfl⟩) R216215
theorem R144161 : Reach 144161 := rs (se 2 (by rfl) ⟨54060, by rfl⟩) R108121
theorem R111631 : Reach 111631 := rs (se 1 (by rfl) ⟨83723, by rfl⟩) R167447
theorem R144503 : Reach 144503 := rs (se 1 (by rfl) ⟨108377, by rfl⟩) R216755
theorem R472301 : Reach 472301 := rs (se 3 (by rfl) ⟨88556, by rfl⟩) R177113
theorem R144683 : Reach 144683 := rs (se 1 (by rfl) ⟨108512, by rfl⟩) R217025
theorem R79223 : Reach 79223 := rs (se 1 (by rfl) ⟨59417, by rfl⟩) R118835
theorem R308701 : Reach 308701 := rs (se 3 (by rfl) ⟨57881, by rfl⟩) R115763
theorem R112171 : Reach 112171 := rs (se 1 (by rfl) ⟨84128, by rfl⟩) R168257
theorem R702017 : Reach 702017 := rs (se 2 (by rfl) ⟨263256, by rfl⟩) R526513
theorem R145043 : Reach 145043 := rs (se 1 (by rfl) ⟨108782, by rfl⟩) R217565
theorem R112313 : Reach 112313 := rs (se 2 (by rfl) ⟨42117, by rfl⟩) R84235
theorem R145097 : Reach 145097 := rs (se 2 (by rfl) ⟨54411, by rfl⟩) R108823
theorem R2176885 : Reach 2176885 := rs (se 5 (by rfl) ⟨102041, by rfl⟩) R204083
theorem R702361 : Reach 702361 := rs (se 2 (by rfl) ⟨263385, by rfl⟩) R526771
theorem R80119 : Reach 80119 := rs (se 1 (by rfl) ⟨60089, by rfl⟩) R120179
theorem R113015 : Reach 113015 := rs (se 1 (by rfl) ⟨84761, by rfl⟩) R169523
theorem R145799 : Reach 145799 := rs (se 1 (by rfl) ⟨109349, by rfl⟩) R218699
theorem R375299 : Reach 375299 := rs (se 1 (by rfl) ⟨281474, by rfl⟩) R562949
theorem R506411 : Reach 506411 := rs (se 1 (by rfl) ⟨379808, by rfl⟩) R759617
theorem R80443 : Reach 80443 := rs (se 1 (by rfl) ⟨60332, by rfl⟩) R120665
theorem R145979 : Reach 145979 := rs (se 1 (by rfl) ⟨109484, by rfl⟩) R218969
theorem R211517 : Reach 211517 := rs (se 3 (by rfl) ⟨39659, by rfl⟩) R79319
theorem R146105 : Reach 146105 := rs (se 2 (by rfl) ⟨54789, by rfl⟩) R109579
theorem R441139 : Reach 441139 := rs (se 1 (by rfl) ⟨330854, by rfl⟩) R661709
theorem R113593 : Reach 113593 := rs (se 2 (by rfl) ⟨42597, by rfl⟩) R85195
theorem R146447 : Reach 146447 := rs (se 1 (by rfl) ⟨109835, by rfl⟩) R219671
theorem R146465 : Reach 146465 := rs (se 2 (by rfl) ⟨54924, by rfl⟩) R109849
theorem R80939 : Reach 80939 := rs (se 1 (by rfl) ⟨60704, by rfl⟩) R121409
theorem R245051 : Reach 245051 := rs (se 1 (by rfl) ⟨183788, by rfl⟩) R367577
theorem R146807 : Reach 146807 := rs (se 1 (by rfl) ⟨110105, by rfl⟩) R220211
theorem R81415 : Reach 81415 := rs (se 1 (by rfl) ⟨61061, by rfl⟩) R122123
theorem R146987 : Reach 146987 := rs (se 1 (by rfl) ⟨110240, by rfl⟩) R220481
theorem R540431 : Reach 540431 := rs (se 1 (by rfl) ⟨405323, by rfl⟩) R810647
theorem R245537 : Reach 245537 := rs (se 2 (by rfl) ⟨92076, by rfl⟩) R184153
theorem R606041 : Reach 606041 := rs (se 2 (by rfl) ⟨227265, by rfl⟩) R454531
theorem R147347 : Reach 147347 := rs (se 1 (by rfl) ⟨110510, by rfl⟩) R221021
theorem R147401 : Reach 147401 := rs (se 2 (by rfl) ⟨55275, by rfl⟩) R110551
theorem R81911 : Reach 81911 := rs (se 1 (by rfl) ⟨61433, by rfl⟩) R122867
theorem R82063 : Reach 82063 := rs (se 1 (by rfl) ⟨61547, by rfl⟩) R123095
theorem R82235 : Reach 82235 := rs (se 1 (by rfl) ⟨61676, by rfl⟩) R123353
theorem R1556957 : Reach 1556957 := rs (se 3 (by rfl) ⟨291929, by rfl⟩) R583859
theorem R213515 : Reach 213515 := rs (se 1 (by rfl) ⟨160136, by rfl⟩) R320273
theorem R213623 : Reach 213623 := rs (se 1 (by rfl) ⟨160217, by rfl⟩) R320435
theorem R148103 : Reach 148103 := rs (se 1 (by rfl) ⟨111077, by rfl⟩) R222155
theorem R180883 : Reach 180883 := rs (se 1 (by rfl) ⟨135662, by rfl⟩) R271325
theorem R246509 : Reach 246509 := rs (se 3 (by rfl) ⟨46220, by rfl⟩) R92441
theorem R148283 : Reach 148283 := rs (se 1 (by rfl) ⟨111212, by rfl⟩) R222425
theorem R181111 : Reach 181111 := rs (se 1 (by rfl) ⟨135833, by rfl⟩) R271667
theorem R148409 : Reach 148409 := rs (se 2 (by rfl) ⟨55653, by rfl⟩) R111307
theorem R246827 : Reach 246827 := rs (se 1 (by rfl) ⟨185120, by rfl⟩) R370241
theorem R541829 : Reach 541829 := rs (se 4 (by rfl) ⟨50796, by rfl⟩) R101593
theorem R214217 : Reach 214217 := rs (se 2 (by rfl) ⟨80331, by rfl⟩) R160663
theorem R83207 : Reach 83207 := rs (se 1 (by rfl) ⟨62405, by rfl⟩) R124811
theorem R148751 : Reach 148751 := rs (se 1 (by rfl) ⟨111563, by rfl⟩) R223127
theorem R148769 : Reach 148769 := rs (se 2 (by rfl) ⟨55788, by rfl⟩) R111577
theorem R411065 : Reach 411065 := rs (se 2 (by rfl) ⟨154149, by rfl⟩) R308299
theorem R149111 : Reach 149111 := rs (se 1 (by rfl) ⟨111833, by rfl⟩) R223667
theorem R149291 : Reach 149291 := rs (se 1 (by rfl) ⟨111968, by rfl⟩) R223937
theorem R214919 : Reach 214919 := rs (se 1 (by rfl) ⟨161189, by rfl⟩) R322379
theorem R83855 : Reach 83855 := rs (se 1 (by rfl) ⟨62891, by rfl⟩) R125783
theorem R182387 : Reach 182387 := rs (se 1 (by rfl) ⟨136790, by rfl⟩) R273581
theorem R149651 : Reach 149651 := rs (se 1 (by rfl) ⟨112238, by rfl⟩) R224477
theorem R84169 : Reach 84169 := rs (se 2 (by rfl) ⟨31563, by rfl⟩) R63127
theorem R149705 : Reach 149705 := rs (se 2 (by rfl) ⟨56139, by rfl⟩) R112279
theorem R215297 : Reach 215297 := rs (se 2 (by rfl) ⟨80736, by rfl⟩) R161473
theorem R182729 : Reach 182729 := rs (se 2 (by rfl) ⟨68523, by rfl⟩) R137047
theorem R117263 : Reach 117263 := rs (se 1 (by rfl) ⟨87947, by rfl⟩) R175895
theorem R182843 : Reach 182843 := rs (se 1 (by rfl) ⟨137132, by rfl⟩) R274265
theorem R182969 : Reach 182969 := rs (se 2 (by rfl) ⟨68613, by rfl⟩) R137227
theorem R84665 : Reach 84665 := rs (se 2 (by rfl) ⟨31749, by rfl⟩) R63499
theorem R1231553 : Reach 1231553 := rs (se 2 (by rfl) ⟨461832, by rfl⟩) R923665
theorem R150407 : Reach 150407 := rs (se 1 (by rfl) ⟨112805, by rfl⟩) R225611
theorem R150425 : Reach 150425 := rs (se 2 (by rfl) ⟨56409, by rfl⟩) R112819
theorem R216107 : Reach 216107 := rs (se 1 (by rfl) ⟨162080, by rfl⟩) R324161
theorem R150587 : Reach 150587 := rs (se 1 (by rfl) ⟨112940, by rfl⟩) R225881
theorem R379991 : Reach 379991 := rs (se 1 (by rfl) ⟨284993, by rfl⟩) R569987
theorem R150713 : Reach 150713 := rs (se 2 (by rfl) ⟨56517, by rfl⟩) R113035
theorem R150785 : Reach 150785 := rs (se 2 (by rfl) ⟨56544, by rfl⟩) R113089
theorem R118675 : Reach 118675 := rs (se 1 (by rfl) ⟨89006, by rfl⟩) R178013
theorem R184619 : Reach 184619 := rs (se 1 (by rfl) ⟨138464, by rfl⟩) R276929
theorem R217403 : Reach 217403 := rs (se 1 (by rfl) ⟨163052, by rfl⟩) R326105
theorem R414011 : Reach 414011 := rs (se 1 (by rfl) ⟨310508, by rfl⟩) R621017
theorem R250397 : Reach 250397 := rs (se 3 (by rfl) ⟨46949, by rfl⟩) R93899
theorem R479773 : Reach 479773 := rs (se 3 (by rfl) ⟨89957, by rfl⟩) R179915
theorem R250411 : Reach 250411 := rs (se 1 (by rfl) ⟨187808, by rfl⟩) R375617
theorem R86671 : Reach 86671 := rs (se 1 (by rfl) ⟨65003, by rfl⟩) R130007
theorem R217889 : Reach 217889 := rs (se 2 (by rfl) ⟨81708, by rfl⟩) R163417
theorem R316295 : Reach 316295 := rs (se 1 (by rfl) ⟨237221, by rfl⟩) R474443
theorem R381905 : Reach 381905 := rs (se 2 (by rfl) ⟨143214, by rfl⟩) R286429
theorem R185611 : Reach 185611 := rs (se 1 (by rfl) ⟨139208, by rfl⟩) R278417
theorem R1365281 : Reach 1365281 := rs (se 2 (by rfl) ⟨511980, by rfl⟩) R1023961
theorem R218483 : Reach 218483 := rs (se 1 (by rfl) ⟨163862, by rfl⟩) R327725
theorem R185885 : Reach 185885 := rs (se 3 (by rfl) ⟨34853, by rfl⟩) R69707
theorem R120467 : Reach 120467 := rs (se 1 (by rfl) ⟨90350, by rfl⟩) R180701
theorem R120521 : Reach 120521 := rs (se 2 (by rfl) ⟨45195, by rfl⟩) R90391
theorem R284431 : Reach 284431 := rs (se 1 (by rfl) ⟨213323, by rfl⟩) R426647
theorem R120619 : Reach 120619 := rs (se 1 (by rfl) ⟨90464, by rfl⟩) R180929
theorem R907057 : Reach 907057 := rs (se 2 (by rfl) ⟨340146, by rfl⟩) R680293
theorem R481139 : Reach 481139 := rs (se 1 (by rfl) ⟨360854, by rfl⟩) R721709
theorem R120847 : Reach 120847 := rs (se 1 (by rfl) ⟨90635, by rfl⟩) R181271
theorem R154003 : Reach 154003 := rs (se 1 (by rfl) ⟨115502, by rfl⟩) R231005
theorem R154639 : Reach 154639 := rs (se 1 (by rfl) ⟨115979, by rfl⟩) R231959
theorem R318487 : Reach 318487 := rs (se 1 (by rfl) ⟨238865, by rfl⟩) R477731
theorem R842885 : Reach 842885 := rs (se 4 (by rfl) ⟨79020, by rfl⟩) R158041
theorem R2579653 : Reach 2579653 := rs (se 4 (by rfl) ⟨241842, by rfl⟩) R483685
theorem R155015 : Reach 155015 := rs (se 1 (by rfl) ⟨116261, by rfl⟩) R232523
theorem R286087 : Reach 286087 := rs (se 1 (by rfl) ⟨214565, by rfl⟩) R429131
theorem R155081 : Reach 155081 := rs (se 2 (by rfl) ⟨58155, by rfl⟩) R116311
theorem R122411 : Reach 122411 := rs (se 1 (by rfl) ⟨91808, by rfl⟩) R183617
theorem R745037 : Reach 745037 := rs (se 3 (by rfl) ⟨139694, by rfl⟩) R279389
theorem R187991 : Reach 187991 := rs (se 1 (by rfl) ⟨140993, by rfl⟩) R281987
theorem R89785 : Reach 89785 := rs (se 2 (by rfl) ⟨33669, by rfl⟩) R67339
theorem R1269553 : Reach 1269553 := rs (se 2 (by rfl) ⟨476082, by rfl⟩) R952165
theorem R188219 : Reach 188219 := rs (se 1 (by rfl) ⟨141164, by rfl⟩) R282329
theorem R89915 : Reach 89915 := rs (se 1 (by rfl) ⟨67436, by rfl⟩) R134873
theorem R221075 : Reach 221075 := rs (se 1 (by rfl) ⟨165806, by rfl⟩) R331613
theorem R188345 : Reach 188345 := rs (se 2 (by rfl) ⟨70629, by rfl⟩) R141259
theorem R549179 : Reach 549179 := rs (se 1 (by rfl) ⟨411884, by rfl⟩) R823769
theorem R90487 : Reach 90487 := rs (se 1 (by rfl) ⟨67865, by rfl⟩) R135731
theorem R582187 : Reach 582187 := rs (se 1 (by rfl) ⟨436640, by rfl⟩) R873281
theorem R124105 : Reach 124105 := rs (se 2 (by rfl) ⟨46539, by rfl⟩) R93079
theorem R222479 : Reach 222479 := rs (se 1 (by rfl) ⟨166859, by rfl⟩) R333719
theorem R91535 : Reach 91535 := rs (se 1 (by rfl) ⟨68651, by rfl⟩) R137303
theorem R320921 : Reach 320921 := rs (se 2 (by rfl) ⟨120345, by rfl⟩) R240691
theorem R222749 : Reach 222749 := rs (se 3 (by rfl) ⟨41765, by rfl⟩) R83531
theorem R189985 : Reach 189985 := rs (se 2 (by rfl) ⟨71244, by rfl⟩) R142489
theorem R91849 : Reach 91849 := rs (se 2 (by rfl) ⟨34443, by rfl⟩) R68887
theorem R190475 : Reach 190475 := rs (se 1 (by rfl) ⟨142856, by rfl⟩) R285713
theorem R125129 : Reach 125129 := rs (se 2 (by rfl) ⟨46923, by rfl⟩) R93847
theorem R387587 : Reach 387587 := rs (se 1 (by rfl) ⟨290690, by rfl⟩) R581381
theorem R420623 : Reach 420623 := rs (se 1 (by rfl) ⟨315467, by rfl⟩) R630935
theorem R486233 : Reach 486233 := rs (se 2 (by rfl) ⟨182337, by rfl⟩) R364675
theorem R224153 : Reach 224153 := rs (se 2 (by rfl) ⟨84057, by rfl⟩) R168115
theorem R126011 : Reach 126011 := rs (se 1 (by rfl) ⟨94508, by rfl⟩) R189017
theorem R1371491 : Reach 1371491 := rs (se 1 (by rfl) ⟨1028618, by rfl⟩) R2057237
theorem R126497 : Reach 126497 := rs (se 2 (by rfl) ⟨47436, by rfl⟩) R94873
theorem R552491 : Reach 552491 := rs (se 1 (by rfl) ⟨414368, by rfl⟩) R828737
theorem R224855 : Reach 224855 := rs (se 1 (by rfl) ⟨168641, by rfl⟩) R337283
theorem R126839 : Reach 126839 := rs (se 1 (by rfl) ⟨95129, by rfl⟩) R190259
theorem R323513 : Reach 323513 := rs (se 2 (by rfl) ⟨121317, by rfl⟩) R242635
theorem R225233 : Reach 225233 := rs (se 2 (by rfl) ⟨84462, by rfl⟩) R168925
theorem R159803 : Reach 159803 := rs (se 1 (by rfl) ⟨119852, by rfl⟩) R239705
theorem R225341 : Reach 225341 := rs (se 3 (by rfl) ⟨42251, by rfl⟩) R84503
theorem R160015 : Reach 160015 := rs (se 1 (by rfl) ⟨120011, by rfl⟩) R240023
theorem R618785 : Reach 618785 := rs (se 2 (by rfl) ⟨232044, by rfl⟩) R464089
theorem R94537 : Reach 94537 := rs (se 2 (by rfl) ⟨35451, by rfl⟩) R70903
theorem R160147 : Reach 160147 := rs (se 1 (by rfl) ⟨120110, by rfl⟩) R240221
theorem R94727 : Reach 94727 := rs (se 1 (by rfl) ⟨71045, by rfl⟩) R142091
theorem R160289 : Reach 160289 := rs (se 2 (by rfl) ⟨60108, by rfl⟩) R120217
theorem R94763 : Reach 94763 := rs (se 1 (by rfl) ⟨71072, by rfl⟩) R142145
theorem R127547 : Reach 127547 := rs (se 1 (by rfl) ⟨95660, by rfl⟩) R191321
theorem R94793 : Reach 94793 := rs (se 2 (by rfl) ⟨35547, by rfl⟩) R71095
theorem R94907 : Reach 94907 := rs (se 1 (by rfl) ⟨71180, by rfl⟩) R142361
theorem R1372889 : Reach 1372889 := rs (se 2 (by rfl) ⟨514833, by rfl⟩) R1029667
theorem R94967 : Reach 94967 := rs (se 1 (by rfl) ⟨71225, by rfl⟩) R142451
theorem R94991 : Reach 94991 := rs (se 1 (by rfl) ⟨71243, by rfl⟩) R142487
theorem R95033 : Reach 95033 := rs (se 2 (by rfl) ⟨35637, by rfl⟩) R71275
theorem R95111 : Reach 95111 := rs (se 1 (by rfl) ⟨71333, by rfl⟩) R142667
theorem R95147 : Reach 95147 := rs (se 1 (by rfl) ⟨71360, by rfl⟩) R142721
theorem R95177 : Reach 95177 := rs (se 2 (by rfl) ⟨35691, by rfl⟩) R71383
theorem R95291 : Reach 95291 := rs (se 1 (by rfl) ⟨71468, by rfl⟩) R142937
theorem R95351 : Reach 95351 := rs (se 1 (by rfl) ⟨71513, by rfl⟩) R143027
theorem R95375 : Reach 95375 := rs (se 1 (by rfl) ⟨71531, by rfl⟩) R143063
theorem R95417 : Reach 95417 := rs (se 2 (by rfl) ⟨35781, by rfl⟩) R71563
theorem R324809 : Reach 324809 := rs (se 2 (by rfl) ⟨121803, by rfl⟩) R243607
theorem R95495 : Reach 95495 := rs (se 1 (by rfl) ⟨71621, by rfl⟩) R143243
theorem R95531 : Reach 95531 := rs (se 1 (by rfl) ⟨71648, by rfl⟩) R143297
theorem R95561 : Reach 95561 := rs (se 2 (by rfl) ⟨35835, by rfl⟩) R71671
theorem R95675 : Reach 95675 := rs (se 1 (by rfl) ⟨71756, by rfl⟩) R143513
theorem R95735 : Reach 95735 := rs (se 1 (by rfl) ⟨71801, by rfl⟩) R143603
theorem R161291 : Reach 161291 := rs (se 1 (by rfl) ⟨120968, by rfl⟩) R241937
theorem R95759 : Reach 95759 := rs (se 1 (by rfl) ⟨71819, by rfl⟩) R143639
theorem R95801 : Reach 95801 := rs (se 2 (by rfl) ⟨35925, by rfl⟩) R71851
theorem R95879 : Reach 95879 := rs (se 1 (by rfl) ⟨71909, by rfl⟩) R143819
theorem R95915 : Reach 95915 := rs (se 1 (by rfl) ⟨71936, by rfl⟩) R143873
theorem R194233 : Reach 194233 := rs (se 2 (by rfl) ⟨72837, by rfl⟩) R145675
theorem R63163 : Reach 63163 := rs (se 1 (by rfl) ⟨47372, by rfl⟩) R94745
theorem R95945 : Reach 95945 := rs (se 2 (by rfl) ⟨35979, by rfl⟩) R71959
theorem R63239 : Reach 63239 := rs (se 1 (by rfl) ⟨47429, by rfl⟩) R94859
theorem R63247 : Reach 63247 := rs (se 1 (by rfl) ⟨47435, by rfl⟩) R94871
theorem R63291 : Reach 63291 := rs (se 1 (by rfl) ⟨47468, by rfl⟩) R94937
theorem R96059 : Reach 96059 := rs (se 1 (by rfl) ⟨72044, by rfl⟩) R144089
theorem R96119 : Reach 96119 := rs (se 1 (by rfl) ⟨72089, by rfl⟩) R144179
theorem R63367 : Reach 63367 := rs (se 1 (by rfl) ⟨47525, by rfl⟩) R95051
theorem R63375 : Reach 63375 := rs (se 1 (by rfl) ⟨47531, by rfl⟩) R95063
theorem R96143 : Reach 96143 := rs (se 1 (by rfl) ⟨72107, by rfl⟩) R144215
theorem R96185 : Reach 96185 := rs (se 2 (by rfl) ⟨36069, by rfl⟩) R72139
theorem R63419 : Reach 63419 := rs (se 1 (by rfl) ⟨47564, by rfl⟩) R95129
theorem R128969 : Reach 128969 := rs (se 2 (by rfl) ⟨48363, by rfl⟩) R96727
theorem R63495 : Reach 63495 := rs (se 1 (by rfl) ⟨47621, by rfl⟩) R95243
theorem R96263 : Reach 96263 := rs (se 1 (by rfl) ⟨72197, by rfl⟩) R144395
theorem R63503 : Reach 63503 := rs (se 1 (by rfl) ⟨47627, by rfl⟩) R95255
theorem R96299 : Reach 96299 := rs (se 1 (by rfl) ⟨72224, by rfl⟩) R144449
theorem R63547 : Reach 63547 := rs (se 1 (by rfl) ⟨47660, by rfl⟩) R95321
theorem R96329 : Reach 96329 := rs (se 2 (by rfl) ⟨36123, by rfl⟩) R72247
theorem R63623 : Reach 63623 := rs (se 1 (by rfl) ⟨47717, by rfl⟩) R95435
theorem R63631 : Reach 63631 := rs (se 1 (by rfl) ⟨47723, by rfl⟩) R95447
theorem R161939 : Reach 161939 := rs (se 1 (by rfl) ⟨121454, by rfl⟩) R242909
theorem R63675 : Reach 63675 := rs (se 1 (by rfl) ⟨47756, by rfl⟩) R95513
theorem R96443 : Reach 96443 := rs (se 1 (by rfl) ⟨72332, by rfl⟩) R144665
theorem R96503 : Reach 96503 := rs (se 1 (by rfl) ⟨72377, by rfl⟩) R144755
theorem R63751 : Reach 63751 := rs (se 1 (by rfl) ⟨47813, by rfl⟩) R95627
theorem R63759 : Reach 63759 := rs (se 1 (by rfl) ⟨47819, by rfl⟩) R95639
theorem R96527 : Reach 96527 := rs (se 1 (by rfl) ⟨72395, by rfl⟩) R144791
theorem R1440017 : Reach 1440017 := rs (se 2 (by rfl) ⟨540006, by rfl⟩) R1080013
theorem R96569 : Reach 96569 := rs (se 2 (by rfl) ⟨36213, by rfl⟩) R72427
theorem R63803 : Reach 63803 := rs (se 1 (by rfl) ⟨47852, by rfl⟩) R95705
theorem R293179 : Reach 293179 := rs (se 1 (by rfl) ⟨219884, by rfl⟩) R439769
theorem R63879 : Reach 63879 := rs (se 1 (by rfl) ⟨47909, by rfl⟩) R95819
theorem R96647 : Reach 96647 := rs (se 1 (by rfl) ⟨72485, by rfl⟩) R144971
theorem R63887 : Reach 63887 := rs (se 1 (by rfl) ⟨47915, by rfl⟩) R95831
theorem R96683 : Reach 96683 := rs (se 1 (by rfl) ⟨72512, by rfl⟩) R145025
theorem R162233 : Reach 162233 := rs (se 2 (by rfl) ⟨60837, by rfl⟩) R121675
theorem R63931 : Reach 63931 := rs (se 1 (by rfl) ⟨47948, by rfl⟩) R95897
theorem R96713 : Reach 96713 := rs (se 2 (by rfl) ⟨36267, by rfl⟩) R72535
theorem R64007 : Reach 64007 := rs (se 1 (by rfl) ⟨48005, by rfl⟩) R96011
theorem R64015 : Reach 64015 := rs (se 1 (by rfl) ⟨48011, by rfl⟩) R96023
theorem R64059 : Reach 64059 := rs (se 1 (by rfl) ⟨48044, by rfl⟩) R96089
theorem R96827 : Reach 96827 := rs (se 1 (by rfl) ⟨72620, by rfl⟩) R145241
theorem R96887 : Reach 96887 := rs (se 1 (by rfl) ⟨72665, by rfl⟩) R145331
theorem R64135 : Reach 64135 := rs (se 1 (by rfl) ⟨48101, by rfl⟩) R96203
theorem R96911 : Reach 96911 := rs (se 1 (by rfl) ⟨72683, by rfl⟩) R145367
theorem R64143 : Reach 64143 := rs (se 1 (by rfl) ⟨48107, by rfl⟩) R96215
theorem R129683 : Reach 129683 := rs (se 1 (by rfl) ⟨97262, by rfl⟩) R194525
theorem R96953 : Reach 96953 := rs (se 2 (by rfl) ⟨36357, by rfl⟩) R72715
theorem R64187 : Reach 64187 := rs (se 1 (by rfl) ⟨48140, by rfl⟩) R96281
theorem R64263 : Reach 64263 := rs (se 1 (by rfl) ⟨48197, by rfl⟩) R96395
theorem R97031 : Reach 97031 := rs (se 1 (by rfl) ⟨72773, by rfl⟩) R145547
theorem R64271 : Reach 64271 := rs (se 1 (by rfl) ⟨48203, by rfl⟩) R96407
theorem R391969 : Reach 391969 := rs (se 2 (by rfl) ⟨146988, by rfl⟩) R293977
theorem R97067 : Reach 97067 := rs (se 1 (by rfl) ⟨72800, by rfl⟩) R145601
theorem R64315 : Reach 64315 := rs (se 1 (by rfl) ⟨48236, by rfl⟩) R96473
theorem R97097 : Reach 97097 := rs (se 2 (by rfl) ⟨36411, by rfl⟩) R72823
theorem R64391 : Reach 64391 := rs (se 1 (by rfl) ⟨48293, by rfl⟩) R96587
theorem R64399 : Reach 64399 := rs (se 1 (by rfl) ⟨48299, by rfl⟩) R96599
theorem R359315 : Reach 359315 := rs (se 1 (by rfl) ⟨269486, by rfl⟩) R538973
theorem R64443 : Reach 64443 := rs (se 1 (by rfl) ⟨48332, by rfl⟩) R96665
theorem R97211 : Reach 97211 := rs (se 1 (by rfl) ⟨72908, by rfl⟩) R145817
theorem R97271 : Reach 97271 := rs (se 1 (by rfl) ⟨72953, by rfl⟩) R145907
theorem R64519 : Reach 64519 := rs (se 1 (by rfl) ⟨48389, by rfl⟩) R96779
theorem R64527 : Reach 64527 := rs (se 1 (by rfl) ⟨48395, by rfl⟩) R96791
theorem R97295 : Reach 97295 := rs (se 1 (by rfl) ⟨72971, by rfl⟩) R145943
theorem R64571 : Reach 64571 := rs (se 1 (by rfl) ⟨48428, by rfl⟩) R96857
theorem R97337 : Reach 97337 := rs (se 2 (by rfl) ⟨36501, by rfl⟩) R73003
theorem R162931 : Reach 162931 := rs (se 1 (by rfl) ⟨122198, by rfl⟩) R244397
theorem R64647 : Reach 64647 := rs (se 1 (by rfl) ⟨48485, by rfl⟩) R96971
theorem R97415 : Reach 97415 := rs (se 1 (by rfl) ⟨73061, by rfl⟩) R146123
theorem R64655 : Reach 64655 := rs (se 1 (by rfl) ⟨48491, by rfl⟩) R96983
theorem R97451 : Reach 97451 := rs (se 1 (by rfl) ⟨73088, by rfl⟩) R146177
theorem R64699 : Reach 64699 := rs (se 1 (by rfl) ⟨48524, by rfl⟩) R97049
theorem R97481 : Reach 97481 := rs (se 2 (by rfl) ⟨36555, by rfl⟩) R73111
theorem R163073 : Reach 163073 := rs (se 2 (by rfl) ⟨61152, by rfl⟩) R122305
theorem R64775 : Reach 64775 := rs (se 1 (by rfl) ⟨48581, by rfl⟩) R97163
theorem R64783 : Reach 64783 := rs (se 1 (by rfl) ⟨48587, by rfl⟩) R97175
theorem R64827 : Reach 64827 := rs (se 1 (by rfl) ⟨48620, by rfl⟩) R97241
theorem R97595 : Reach 97595 := rs (se 1 (by rfl) ⟨73196, by rfl⟩) R146393
theorem R97655 : Reach 97655 := rs (se 1 (by rfl) ⟨73241, by rfl⟩) R146483
theorem R64903 : Reach 64903 := rs (se 1 (by rfl) ⟨48677, by rfl⟩) R97355
theorem R64911 : Reach 64911 := rs (se 1 (by rfl) ⟨48683, by rfl⟩) R97367
theorem R97679 : Reach 97679 := rs (se 1 (by rfl) ⟨73259, by rfl⟩) R146519
theorem R97721 : Reach 97721 := rs (se 2 (by rfl) ⟨36645, by rfl⟩) R73291
theorem R64955 : Reach 64955 := rs (se 1 (by rfl) ⟨48716, by rfl⟩) R97433
theorem R65031 : Reach 65031 := rs (se 1 (by rfl) ⟨48773, by rfl⟩) R97547
theorem R97799 : Reach 97799 := rs (se 1 (by rfl) ⟨73349, by rfl⟩) R146699
theorem R65039 : Reach 65039 := rs (se 1 (by rfl) ⟨48779, by rfl⟩) R97559
theorem R97835 : Reach 97835 := rs (se 1 (by rfl) ⟨73376, by rfl⟩) R146753
theorem R65083 : Reach 65083 := rs (se 1 (by rfl) ⟨48812, by rfl⟩) R97625
theorem R97865 : Reach 97865 := rs (se 2 (by rfl) ⟨36699, by rfl⟩) R73399
theorem R2719331 : Reach 2719331 := rs (se 1 (by rfl) ⟨2039498, by rfl⟩) R4078997
theorem R65159 : Reach 65159 := rs (se 1 (by rfl) ⟨48869, by rfl⟩) R97739
theorem R65167 : Reach 65167 := rs (se 1 (by rfl) ⟨48875, by rfl⟩) R97751
theorem R163475 : Reach 163475 := rs (se 1 (by rfl) ⟨122606, by rfl⟩) R245213
theorem R65211 : Reach 65211 := rs (se 1 (by rfl) ⟨48908, by rfl⟩) R97817
theorem R97979 : Reach 97979 := rs (se 1 (by rfl) ⟨73484, by rfl⟩) R146969
theorem R163529 : Reach 163529 := rs (se 2 (by rfl) ⟨61323, by rfl⟩) R122647
theorem R98039 : Reach 98039 := rs (se 1 (by rfl) ⟨73529, by rfl⟩) R147059
theorem R65287 : Reach 65287 := rs (se 1 (by rfl) ⟨48965, by rfl⟩) R97931
theorem R65295 : Reach 65295 := rs (se 1 (by rfl) ⟨48971, by rfl⟩) R97943
theorem R98063 : Reach 98063 := rs (se 1 (by rfl) ⟨73547, by rfl⟩) R147095
theorem R98105 : Reach 98105 := rs (se 2 (by rfl) ⟨36789, by rfl⟩) R73579
theorem R65339 : Reach 65339 := rs (se 1 (by rfl) ⟨49004, by rfl⟩) R98009
theorem R65415 : Reach 65415 := rs (se 1 (by rfl) ⟨49061, by rfl⟩) R98123
theorem R98183 : Reach 98183 := rs (se 1 (by rfl) ⟨73637, by rfl⟩) R147275
theorem R65423 : Reach 65423 := rs (se 1 (by rfl) ⟨49067, by rfl⟩) R98135
theorem R98219 : Reach 98219 := rs (se 1 (by rfl) ⟨73664, by rfl⟩) R147329
theorem R65467 : Reach 65467 := rs (se 1 (by rfl) ⟨49100, by rfl⟩) R98201
theorem R98249 : Reach 98249 := rs (se 2 (by rfl) ⟨36843, by rfl⟩) R73687
theorem R360395 : Reach 360395 := rs (se 1 (by rfl) ⟨270296, by rfl⟩) R540593
theorem R65575 : Reach 65575 := rs (se 1 (by rfl) ⟨49181, by rfl⟩) R98363
theorem R65615 : Reach 65615 := rs (se 1 (by rfl) ⟨49211, by rfl⟩) R98423
theorem R65631 : Reach 65631 := rs (se 1 (by rfl) ⟨49223, by rfl⟩) R98447
theorem R65659 : Reach 65659 := rs (se 1 (by rfl) ⟨49244, by rfl⟩) R98489
theorem R65711 : Reach 65711 := rs (se 1 (by rfl) ⟨49283, by rfl⟩) R98567
theorem R65735 : Reach 65735 := rs (se 1 (by rfl) ⟨49301, by rfl⟩) R98603
theorem R65755 : Reach 65755 := rs (se 1 (by rfl) ⟨49316, by rfl⟩) R98633
theorem R65831 : Reach 65831 := rs (se 1 (by rfl) ⟨49373, by rfl⟩) R98747
theorem R65871 : Reach 65871 := rs (se 1 (by rfl) ⟨49403, by rfl⟩) R98807
theorem R65887 : Reach 65887 := rs (se 1 (by rfl) ⟨49415, by rfl⟩) R98831
theorem R65915 : Reach 65915 := rs (se 1 (by rfl) ⟨49436, by rfl⟩) R98873
theorem R262543 : Reach 262543 := rs (se 1 (by rfl) ⟨196907, by rfl⟩) R393815
theorem R98735 : Reach 98735 := rs (se 1 (by rfl) ⟨74051, by rfl⟩) R148103
theorem R65967 : Reach 65967 := rs (se 1 (by rfl) ⟨49475, by rfl⟩) R98951
theorem R65991 : Reach 65991 := rs (se 1 (by rfl) ⟨49493, by rfl⟩) R98987
theorem R66011 : Reach 66011 := rs (se 1 (by rfl) ⟨49508, by rfl⟩) R99017
theorem R459245 : Reach 459245 := rs (se 3 (by rfl) ⟨86108, by rfl⟩) R172217
theorem R164339 : Reach 164339 := rs (se 1 (by rfl) ⟨123254, by rfl⟩) R246509
theorem R98825 : Reach 98825 := rs (se 2 (by rfl) ⟨37059, by rfl⟩) R74119
theorem R98855 : Reach 98855 := rs (se 1 (by rfl) ⟨74141, by rfl⟩) R148283
theorem R66087 : Reach 66087 := rs (se 1 (by rfl) ⟨49565, by rfl⟩) R99131
theorem R66127 : Reach 66127 := rs (se 1 (by rfl) ⟨49595, by rfl⟩) R99191
theorem R66143 : Reach 66143 := rs (se 1 (by rfl) ⟨49607, by rfl⟩) R99215
theorem R98939 : Reach 98939 := rs (se 1 (by rfl) ⟨74204, by rfl⟩) R148409
theorem R66171 : Reach 66171 := rs (se 1 (by rfl) ⟨49628, by rfl⟩) R99257
theorem R66223 : Reach 66223 := rs (se 1 (by rfl) ⟨49667, by rfl⟩) R99335
theorem R164551 : Reach 164551 := rs (se 1 (by rfl) ⟨123413, by rfl⟩) R246827
theorem R66247 : Reach 66247 := rs (se 1 (by rfl) ⟨49685, by rfl⟩) R99371
theorem R66267 : Reach 66267 := rs (se 1 (by rfl) ⟨49700, by rfl⟩) R99401
theorem R99065 : Reach 99065 := rs (se 2 (by rfl) ⟨37149, by rfl⟩) R74299
theorem R361219 : Reach 361219 := rs (se 1 (by rfl) ⟨270914, by rfl⟩) R541829
theorem R492317 : Reach 492317 := rs (se 3 (by rfl) ⟨92309, by rfl⟩) R184619
theorem R66343 : Reach 66343 := rs (se 1 (by rfl) ⟨49757, by rfl⟩) R99515
theorem R66383 : Reach 66383 := rs (se 1 (by rfl) ⟨49787, by rfl⟩) R99575
theorem R99167 : Reach 99167 := rs (se 1 (by rfl) ⟨74375, by rfl⟩) R148751
theorem R66399 : Reach 66399 := rs (se 1 (by rfl) ⟨49799, by rfl⟩) R99599
theorem R99179 : Reach 99179 := rs (se 1 (by rfl) ⟨74384, by rfl⟩) R148769
theorem R66427 : Reach 66427 := rs (se 1 (by rfl) ⟨49820, by rfl⟩) R99641
theorem R66479 : Reach 66479 := rs (se 1 (by rfl) ⟨49859, by rfl⟩) R99719
theorem R66523 : Reach 66523 := rs (se 1 (by rfl) ⟨49892, by rfl⟩) R99785
theorem R590867 : Reach 590867 := rs (se 1 (by rfl) ⟨443150, by rfl⟩) R886301
theorem R66599 : Reach 66599 := rs (se 1 (by rfl) ⟨49949, by rfl⟩) R99899
theorem R590915 : Reach 590915 := rs (se 1 (by rfl) ⟨443186, by rfl⟩) R886373
theorem R99407 : Reach 99407 := rs (se 1 (by rfl) ⟨74555, by rfl⟩) R149111
theorem R66639 : Reach 66639 := rs (se 1 (by rfl) ⟨49979, by rfl⟩) R99959
theorem R66683 : Reach 66683 := rs (se 1 (by rfl) ⟨50012, by rfl⟩) R100025
theorem R99527 : Reach 99527 := rs (se 1 (by rfl) ⟨74645, by rfl⟩) R149291
theorem R66759 : Reach 66759 := rs (se 1 (by rfl) ⟨50069, by rfl⟩) R100139
theorem R66911 : Reach 66911 := rs (se 1 (by rfl) ⟨50183, by rfl⟩) R100367
theorem R99689 : Reach 99689 := rs (se 2 (by rfl) ⟨37383, by rfl⟩) R74767
theorem R66991 : Reach 66991 := rs (se 1 (by rfl) ⟨50243, by rfl⟩) R100487
theorem R99767 : Reach 99767 := rs (se 1 (by rfl) ⟨74825, by rfl⟩) R149651
theorem R99803 : Reach 99803 := rs (se 1 (by rfl) ⟨74852, by rfl⟩) R149705
theorem R67035 : Reach 67035 := rs (se 1 (by rfl) ⟨50276, by rfl⟩) R100553
theorem R67111 : Reach 67111 := rs (se 1 (by rfl) ⟨50333, by rfl⟩) R100667
theorem R165473 : Reach 165473 := rs (se 2 (by rfl) ⟨62052, by rfl⟩) R124105
theorem R821035 : Reach 821035 := rs (se 1 (by rfl) ⟨615776, by rfl⟩) R1231553
theorem R100169 : Reach 100169 := rs (se 2 (by rfl) ⟨37563, by rfl⟩) R75127
theorem R132959 : Reach 132959 := rs (se 1 (by rfl) ⟨99719, by rfl⟩) R199439
theorem R100271 : Reach 100271 := rs (se 1 (by rfl) ⟨75203, by rfl⟩) R150407
theorem R100283 : Reach 100283 := rs (se 1 (by rfl) ⟨75212, by rfl⟩) R150425
theorem R100361 : Reach 100361 := rs (se 2 (by rfl) ⟨37635, by rfl⟩) R75271
theorem R395279 : Reach 395279 := rs (se 1 (by rfl) ⟨296459, by rfl⟩) R592919
theorem R100391 : Reach 100391 := rs (se 1 (by rfl) ⟨75293, by rfl⟩) R150587
theorem R100409 : Reach 100409 := rs (se 2 (by rfl) ⟨37653, by rfl⟩) R75307
theorem R100475 : Reach 100475 := rs (se 1 (by rfl) ⟨75356, by rfl⟩) R150713
theorem R100523 : Reach 100523 := rs (se 1 (by rfl) ⟨75392, by rfl⟩) R150785
theorem R100601 : Reach 100601 := rs (se 2 (by rfl) ⟨37725, by rfl⟩) R75451
theorem R2558789 : Reach 2558789 := rs (se 4 (by rfl) ⟨239886, by rfl⟩) R479773
theorem R166931 : Reach 166931 := rs (se 1 (by rfl) ⟨125198, by rfl⟩) R250397
theorem R330803 : Reach 330803 := rs (se 1 (by rfl) ⟨248102, by rfl⟩) R496205
theorem R265463 : Reach 265463 := rs (se 1 (by rfl) ⟨199097, by rfl⟩) R398195
theorem R68959 : Reach 68959 := rs (se 1 (by rfl) ⟨51719, by rfl⟩) R103439
theorem R855539 : Reach 855539 := rs (se 1 (by rfl) ⟨641654, by rfl⟩) R1283309
theorem R8261297 : Reach 8261297 := rs (se 2 (by rfl) ⟨3097986, by rfl⟩) R6195973
theorem R332423 : Reach 332423 := rs (se 1 (by rfl) ⟨249317, by rfl⟩) R498635
theorem R561923 : Reach 561923 := rs (se 1 (by rfl) ⟨421442, by rfl⟩) R842885
theorem R103343 : Reach 103343 := rs (se 1 (by rfl) ⟨77507, by rfl⟩) R155015
theorem R496691 : Reach 496691 := rs (se 1 (by rfl) ⟨372518, by rfl⟩) R745037
theorem R726083 : Reach 726083 := rs (se 1 (by rfl) ⟨544562, by rfl⟩) R1089125
theorem R824741 : Reach 824741 := rs (se 4 (by rfl) ⟨77319, by rfl⟩) R154639
theorem R71131 : Reach 71131 := rs (se 1 (by rfl) ⟨53348, by rfl⟩) R106697
theorem R366119 : Reach 366119 := rs (se 1 (by rfl) ⟨274589, by rfl⟩) R549179
theorem R235217 : Reach 235217 := rs (se 2 (by rfl) ⟨88206, by rfl⟩) R176413
theorem R497441 : Reach 497441 := rs (se 2 (by rfl) ⟨186540, by rfl⟩) R373081
theorem R71599 : Reach 71599 := rs (se 1 (by rfl) ⟨53699, by rfl⟩) R107399
theorem R333881 : Reach 333881 := rs (se 2 (by rfl) ⟨125205, by rfl⟩) R250411
theorem R72031 : Reach 72031 := rs (se 1 (by rfl) ⟨54023, by rfl⟩) R108047
theorem R793273 : Reach 793273 := rs (se 2 (by rfl) ⟨297477, by rfl⟩) R594955
theorem R72391 : Reach 72391 := rs (se 1 (by rfl) ⟨54293, by rfl⟩) R108587
theorem R597071 : Reach 597071 := rs (se 1 (by rfl) ⟨447803, by rfl⟩) R895607
theorem R138601 : Reach 138601 := rs (se 2 (by rfl) ⟨51975, by rfl⟩) R103951
theorem R73255 : Reach 73255 := rs (se 1 (by rfl) ⟨54941, by rfl⟩) R109883
theorem R368327 : Reach 368327 := rs (se 1 (by rfl) ⟨276245, by rfl⟩) R552491
theorem R106535 : Reach 106535 := rs (se 1 (by rfl) ⟨79901, by rfl⟩) R159803
theorem R335987 : Reach 335987 := rs (se 1 (by rfl) ⟨251990, by rfl⟩) R503981
theorem R106825 : Reach 106825 := rs (se 2 (by rfl) ⟨40059, by rfl⟩) R80119
theorem R106859 : Reach 106859 := rs (se 1 (by rfl) ⟨80144, by rfl⟩) R160289
theorem R205337 : Reach 205337 := rs (se 2 (by rfl) ⟨77001, by rfl⟩) R154003
theorem R107257 : Reach 107257 := rs (se 2 (by rfl) ⟨40221, by rfl⟩) R80443
theorem R140105 : Reach 140105 := rs (se 2 (by rfl) ⟨52539, by rfl⟩) R105079
theorem R107527 : Reach 107527 := rs (se 1 (by rfl) ⟨80645, by rfl⟩) R161291
theorem R468011 : Reach 468011 := rs (se 1 (by rfl) ⟨351008, by rfl⟩) R702017
theorem R74875 : Reach 74875 := rs (se 1 (by rfl) ⟨56156, by rfl⟩) R112313
theorem R107959 : Reach 107959 := rs (se 1 (by rfl) ⟨80969, by rfl⟩) R161939
theorem R960011 : Reach 960011 := rs (se 1 (by rfl) ⟨720008, by rfl⟩) R1440017
theorem R75343 : Reach 75343 := rs (se 1 (by rfl) ⟨56507, by rfl⟩) R113015
theorem R108155 : Reach 108155 := rs (se 1 (by rfl) ⟨81116, by rfl⟩) R162233
theorem R337607 : Reach 337607 := rs (se 1 (by rfl) ⟨253205, by rfl⟩) R506411
theorem R141011 : Reach 141011 := rs (se 1 (by rfl) ⟨105758, by rfl⟩) R211517
theorem R206621 : Reach 206621 := rs (se 3 (by rfl) ⟨38741, by rfl⟩) R77483
theorem R239543 : Reach 239543 := rs (se 1 (by rfl) ⟨179657, by rfl⟩) R359315
theorem R11610053 : Reach 11610053 := rs (se 4 (by rfl) ⟨1088442, by rfl⟩) R2176885
theorem R108553 : Reach 108553 := rs (se 2 (by rfl) ⟨40707, by rfl⟩) R81415
theorem R632933 : Reach 632933 := rs (se 4 (by rfl) ⟨59337, by rfl⟩) R118675
theorem R239773 : Reach 239773 := rs (se 3 (by rfl) ⟨44957, by rfl⟩) R89915
theorem R108715 : Reach 108715 := rs (se 1 (by rfl) ⟨81536, by rfl⟩) R163073
theorem R1812887 : Reach 1812887 := rs (se 1 (by rfl) ⟨1359665, by rfl⟩) R2719331
theorem R108983 : Reach 108983 := rs (se 1 (by rfl) ⟨81737, by rfl⟩) R163475
theorem R109019 : Reach 109019 := rs (se 1 (by rfl) ⟨81764, by rfl⟩) R163529
theorem R404027 : Reach 404027 := rs (se 1 (by rfl) ⟨303020, by rfl⟩) R606041
theorem R240263 : Reach 240263 := rs (se 1 (by rfl) ⟨180197, by rfl⟩) R360395
theorem R109255 : Reach 109255 := rs (se 1 (by rfl) ⟨81941, by rfl⟩) R163883
theorem R142073 : Reach 142073 := rs (se 2 (by rfl) ⟨53277, by rfl⟩) R106555
theorem R240479 : Reach 240479 := rs (se 1 (by rfl) ⟨180359, by rfl⟩) R360719
theorem R109417 : Reach 109417 := rs (se 2 (by rfl) ⟨41031, by rfl⟩) R82063
theorem R142343 : Reach 142343 := rs (se 1 (by rfl) ⟨106757, by rfl⟩) R213515
theorem R142415 : Reach 142415 := rs (se 1 (by rfl) ⟨106811, by rfl⟩) R213623
theorem R110011 : Reach 110011 := rs (se 1 (by rfl) ⟨82508, by rfl⟩) R165017
theorem R142811 : Reach 142811 := rs (se 1 (by rfl) ⟨107108, by rfl⟩) R214217
theorem R241177 : Reach 241177 := rs (se 2 (by rfl) ⟨90441, by rfl⟩) R180883
theorem R110119 : Reach 110119 := rs (se 1 (by rfl) ⟨82589, by rfl⟩) R165179
theorem R274043 : Reach 274043 := rs (se 1 (by rfl) ⟨205532, by rfl⟩) R411065
theorem R503495 : Reach 503495 := rs (se 1 (by rfl) ⟨377621, by rfl⟩) R755243
theorem R241451 : Reach 241451 := rs (se 1 (by rfl) ⟨181088, by rfl⟩) R362177
theorem R241481 : Reach 241481 := rs (se 2 (by rfl) ⟨90555, by rfl⟩) R181111
theorem R110443 : Reach 110443 := rs (se 1 (by rfl) ⟨82832, by rfl⟩) R165665
theorem R143279 : Reach 143279 := rs (se 1 (by rfl) ⟨107459, by rfl⟩) R214919
theorem R143531 : Reach 143531 := rs (se 1 (by rfl) ⟨107648, by rfl⟩) R215297
theorem R78175 : Reach 78175 := rs (se 1 (by rfl) ⟨58631, by rfl⟩) R117263
theorem R4207285 : Reach 4207285 := rs (se 5 (by rfl) ⟨197216, by rfl⟩) R394433
theorem R144071 : Reach 144071 := rs (se 1 (by rfl) ⟨108053, by rfl⟩) R216107
theorem R111503 : Reach 111503 := rs (se 1 (by rfl) ⟨83627, by rfl⟩) R167255
theorem R111739 : Reach 111739 := rs (se 1 (by rfl) ⟨83804, by rfl⟩) R167609
theorem R374159 : Reach 374159 := rs (se 1 (by rfl) ⟨280619, by rfl⟩) R561239
theorem R144935 : Reach 144935 := rs (se 1 (by rfl) ⟨108701, by rfl⟩) R217403
theorem R276007 : Reach 276007 := rs (se 1 (by rfl) ⟨207005, by rfl⟩) R414011
theorem R112225 : Reach 112225 := rs (se 2 (by rfl) ⟨42084, by rfl⟩) R84169
theorem R440057 : Reach 440057 := rs (se 2 (by rfl) ⟨165021, by rfl⟩) R330043
theorem R145259 : Reach 145259 := rs (se 1 (by rfl) ⟨108944, by rfl⟩) R217889
theorem R145313 : Reach 145313 := rs (se 2 (by rfl) ⟨54492, by rfl⟩) R108985
theorem R210863 : Reach 210863 := rs (se 1 (by rfl) ⟨158147, by rfl⟩) R316295
theorem R112603 : Reach 112603 := rs (se 1 (by rfl) ⟨84452, by rfl⟩) R168905
theorem R637085 : Reach 637085 := rs (se 3 (by rfl) ⟨119453, by rfl⟩) R238907
theorem R145655 : Reach 145655 := rs (se 1 (by rfl) ⟨109241, by rfl⟩) R218483
theorem R571697 : Reach 571697 := rs (se 2 (by rfl) ⟨214386, by rfl⟩) R428773
theorem R211261 : Reach 211261 := rs (se 3 (by rfl) ⟨39611, by rfl⟩) R79223
theorem R244093 : Reach 244093 := rs (se 3 (by rfl) ⟨45767, by rfl⟩) R91535
theorem R80347 : Reach 80347 := rs (se 1 (by rfl) ⟨60260, by rfl⟩) R120521
theorem R113231 : Reach 113231 := rs (se 1 (by rfl) ⟨84923, by rfl⟩) R169847
theorem R146249 : Reach 146249 := rs (se 2 (by rfl) ⟨54843, by rfl⟩) R109687
theorem R539621 : Reach 539621 := rs (se 4 (by rfl) ⟨50589, by rfl⟩) R101179
theorem R147041 : Reach 147041 := rs (se 2 (by rfl) ⟨55140, by rfl⟩) R110281
theorem R310931 : Reach 310931 := rs (se 1 (by rfl) ⟨233198, by rfl⟩) R466397
theorem R179927 : Reach 179927 := rs (se 1 (by rfl) ⟨134945, by rfl⟩) R269891
theorem R147361 : Reach 147361 := rs (se 2 (by rfl) ⟨55260, by rfl⟩) R110521
theorem R147383 : Reach 147383 := rs (se 1 (by rfl) ⟨110537, by rfl⟩) R221075
theorem R213353 : Reach 213353 := rs (se 2 (by rfl) ⟨80007, by rfl⟩) R160015
theorem R409961 : Reach 409961 := rs (se 2 (by rfl) ⟨153735, by rfl⟩) R307471
theorem R147977 : Reach 147977 := rs (se 2 (by rfl) ⟨55491, by rfl⟩) R110983
theorem R213529 : Reach 213529 := rs (se 2 (by rfl) ⟨80073, by rfl⟩) R160147
theorem R246311 : Reach 246311 := rs (se 1 (by rfl) ⟨184733, by rfl⟩) R369467
theorem R148319 : Reach 148319 := rs (se 1 (by rfl) ⟨111239, by rfl⟩) R222479
theorem R115561 : Reach 115561 := rs (se 2 (by rfl) ⟨43335, by rfl⟩) R86671
theorem R836527 : Reach 836527 := rs (se 1 (by rfl) ⟨627395, by rfl⟩) R1254791
theorem R377783 : Reach 377783 := rs (se 1 (by rfl) ⟨283337, by rfl⟩) R566675
theorem R213947 : Reach 213947 := rs (se 1 (by rfl) ⟨160460, by rfl⟩) R320921
theorem R148499 : Reach 148499 := rs (se 1 (by rfl) ⟨111374, by rfl⟩) R222749
theorem R771191 : Reach 771191 := rs (se 1 (by rfl) ⟨578393, by rfl⟩) R1156787
theorem R148841 : Reach 148841 := rs (se 2 (by rfl) ⟨55815, by rfl⟩) R111631
theorem R509327 : Reach 509327 := rs (se 1 (by rfl) ⟨381995, by rfl⟩) R763991
theorem R83419 : Reach 83419 := rs (se 1 (by rfl) ⟨62564, by rfl⟩) R125129
theorem R247283 : Reach 247283 := rs (se 1 (by rfl) ⟨185462, by rfl⟩) R370925
theorem R247481 : Reach 247481 := rs (se 2 (by rfl) ⟨92805, by rfl⟩) R185611
theorem R247495 : Reach 247495 := rs (se 1 (by rfl) ⟨185621, by rfl⟩) R371243
theorem R280415 : Reach 280415 := rs (se 1 (by rfl) ⟨210311, by rfl⟩) R420623
theorem R149435 : Reach 149435 := rs (se 1 (by rfl) ⟨112076, by rfl⟩) R224153
theorem R411601 : Reach 411601 := rs (se 2 (by rfl) ⟨154350, by rfl⟩) R308701
theorem R247823 : Reach 247823 := rs (se 1 (by rfl) ⟨185867, by rfl⟩) R371735
theorem R84007 : Reach 84007 := rs (se 1 (by rfl) ⟨63005, by rfl⟩) R126011
theorem R149561 : Reach 149561 := rs (se 2 (by rfl) ⟨56085, by rfl⟩) R112171
theorem R379241 : Reach 379241 := rs (se 2 (by rfl) ⟨142215, by rfl⟩) R284431
theorem R84331 : Reach 84331 := rs (se 1 (by rfl) ⟨63248, by rfl⟩) R126497
theorem R149903 : Reach 149903 := rs (se 1 (by rfl) ⟨112427, by rfl⟩) R224855
theorem R936481 : Reach 936481 := rs (se 2 (by rfl) ⟨351180, by rfl⟩) R702361
theorem R84559 : Reach 84559 := rs (se 1 (by rfl) ⟨63419, by rfl⟩) R126839
theorem R215675 : Reach 215675 := rs (se 1 (by rfl) ⟨161756, by rfl⟩) R323513
theorem R150155 : Reach 150155 := rs (se 1 (by rfl) ⟨112616, by rfl⟩) R225233
theorem R248467 : Reach 248467 := rs (se 1 (by rfl) ⟨186350, by rfl⟩) R372701
theorem R150227 : Reach 150227 := rs (se 1 (by rfl) ⟨112670, by rfl⟩) R225341
theorem R215837 : Reach 215837 := rs (se 3 (by rfl) ⟨40469, by rfl⟩) R80939
theorem R412523 : Reach 412523 := rs (se 1 (by rfl) ⟨309392, by rfl⟩) R618785
theorem R85031 : Reach 85031 := rs (se 1 (by rfl) ⟨63773, by rfl⟩) R127547
theorem R216539 : Reach 216539 := rs (se 1 (by rfl) ⟨162404, by rfl⟩) R324809
theorem R314867 : Reach 314867 := rs (se 1 (by rfl) ⟨236150, by rfl⟩) R472301
theorem R413549 : Reach 413549 := rs (se 3 (by rfl) ⟨77540, by rfl⟩) R155081
theorem R85979 : Reach 85979 := rs (se 1 (by rfl) ⟨64484, by rfl⟩) R128969
theorem R217241 : Reach 217241 := rs (se 2 (by rfl) ⟨81465, by rfl⟩) R162931
theorem R4837637 : Reach 4837637 := rs (se 4 (by rfl) ⟨453528, by rfl⟩) R907057
theorem R250199 : Reach 250199 := rs (se 1 (by rfl) ⟨187649, by rfl⟩) R375299
theorem R86455 : Reach 86455 := rs (se 1 (by rfl) ⟨64841, by rfl⟩) R129683
theorem R381449 : Reach 381449 := rs (se 2 (by rfl) ⟨143043, by rfl⟩) R286087
theorem R545453 : Reach 545453 := rs (se 3 (by rfl) ⟨102272, by rfl⟩) R204545
theorem R119713 : Reach 119713 := rs (se 2 (by rfl) ⟨44892, by rfl⟩) R89785
theorem R1692737 : Reach 1692737 := rs (se 2 (by rfl) ⟨634776, by rfl⟩) R1269553
theorem R218429 : Reach 218429 := rs (se 3 (by rfl) ⟨40955, by rfl⟩) R81911
theorem R153227 : Reach 153227 := rs (se 1 (by rfl) ⟨114920, by rfl⟩) R229841
theorem R1037971 : Reach 1037971 := rs (se 1 (by rfl) ⟨778478, by rfl⟩) R1556957
theorem R776249 : Reach 776249 := rs (se 2 (by rfl) ⟨291093, by rfl⟩) R582187
theorem R350297 : Reach 350297 := rs (se 2 (by rfl) ⟨131361, by rfl⟩) R262723
theorem R219293 : Reach 219293 := rs (se 3 (by rfl) ⟨41117, by rfl⟩) R82235
theorem R350365 : Reach 350365 := rs (se 3 (by rfl) ⟨65693, by rfl⟩) R131387
theorem R711017 : Reach 711017 := rs (se 2 (by rfl) ⟨266631, by rfl⟩) R533263
theorem R809453 : Reach 809453 := rs (se 3 (by rfl) ⟨151772, by rfl⟩) R303545
theorem R88699 : Reach 88699 := rs (se 1 (by rfl) ⟨66524, by rfl⟩) R133049
theorem R154235 : Reach 154235 := rs (se 1 (by rfl) ⟨115676, by rfl⟩) R231353
theorem R219833 : Reach 219833 := rs (se 2 (by rfl) ⟨82437, by rfl⟩) R164875
theorem R187069 : Reach 187069 := rs (se 3 (by rfl) ⟨35075, by rfl⟩) R70151
theorem R121591 : Reach 121591 := rs (se 1 (by rfl) ⟨91193, by rfl⟩) R182387
theorem R154543 : Reach 154543 := rs (se 1 (by rfl) ⟨115907, by rfl⟩) R231815
theorem R121819 : Reach 121819 := rs (se 1 (by rfl) ⟨91364, by rfl⟩) R182729
theorem R121895 : Reach 121895 := rs (se 1 (by rfl) ⟨91421, by rfl⟩) R182843
theorem R121979 : Reach 121979 := rs (se 1 (by rfl) ⟨91484, by rfl⟩) R182969
theorem R3661037 : Reach 3661037 := rs (se 3 (by rfl) ⟨686444, by rfl⟩) R1372889
theorem R220427 : Reach 220427 := rs (se 1 (by rfl) ⟨165320, by rfl⟩) R330641
theorem R1072397 : Reach 1072397 := rs (se 3 (by rfl) ⟨201074, by rfl⟩) R402149
theorem R482597 : Reach 482597 := rs (se 4 (by rfl) ⟨45243, by rfl⟩) R90487
theorem R253313 : Reach 253313 := rs (se 2 (by rfl) ⟨94992, by rfl⟩) R189985
theorem R253327 : Reach 253327 := rs (se 1 (by rfl) ⟨189995, by rfl⟩) R379991
theorem R220697 : Reach 220697 := rs (se 2 (by rfl) ⟨82761, by rfl⟩) R165523
theorem R122465 : Reach 122465 := rs (se 2 (by rfl) ⟨45924, by rfl⟩) R91849
theorem R286651 : Reach 286651 := rs (se 1 (by rfl) ⟨214988, by rfl⟩) R429977
theorem R90191 : Reach 90191 := rs (se 1 (by rfl) ⟨67643, by rfl⟩) R135287
theorem R188801 : Reach 188801 := rs (se 2 (by rfl) ⟨70800, by rfl⟩) R141601
theorem R221831 : Reach 221831 := rs (se 1 (by rfl) ⟨166373, by rfl⟩) R332747
theorem R254603 : Reach 254603 := rs (se 1 (by rfl) ⟨190952, by rfl⟩) R381905
theorem R877229 : Reach 877229 := rs (se 3 (by rfl) ⟨164480, by rfl⟩) R328961
theorem R221885 : Reach 221885 := rs (se 3 (by rfl) ⟨41603, by rfl⟩) R83207
theorem R222047 : Reach 222047 := rs (se 1 (by rfl) ⟨166535, by rfl⟩) R333071
theorem R910187 : Reach 910187 := rs (se 1 (by rfl) ⟨682640, by rfl⟩) R1365281
theorem R222209 : Reach 222209 := rs (se 2 (by rfl) ⟨83328, by rfl⟩) R166657
theorem R123923 : Reach 123923 := rs (se 1 (by rfl) ⟨92942, by rfl⟩) R185885
theorem R320759 : Reach 320759 := rs (se 1 (by rfl) ⟨240569, by rfl⟩) R481139
theorem R222551 : Reach 222551 := rs (se 1 (by rfl) ⟨166913, by rfl⟩) R333827
theorem R321245 : Reach 321245 := rs (se 3 (by rfl) ⟨60233, by rfl⟩) R120467
theorem R190201 : Reach 190201 := rs (se 2 (by rfl) ⟨71325, by rfl⟩) R142651
theorem R223019 : Reach 223019 := rs (se 1 (by rfl) ⟨167264, by rfl⟩) R334529
theorem R1894337 : Reach 1894337 := rs (se 2 (by rfl) ⟨710376, by rfl⟩) R1420753
theorem R157715 : Reach 157715 := rs (se 1 (by rfl) ⟨118286, by rfl⟩) R236573
theorem R223289 : Reach 223289 := rs (se 2 (by rfl) ⟨83733, by rfl⟩) R167467
theorem R551069 : Reach 551069 := rs (se 3 (by rfl) ⟨103325, by rfl⟩) R206651
theorem R223613 : Reach 223613 := rs (se 3 (by rfl) ⟨41927, by rfl⟩) R83855
theorem R354689 : Reach 354689 := rs (se 2 (by rfl) ⟨133008, by rfl⟩) R266017
theorem R125327 : Reach 125327 := rs (se 1 (by rfl) ⟨93995, by rfl⟩) R187991
theorem R125479 : Reach 125479 := rs (se 1 (by rfl) ⟨94109, by rfl⟩) R188219
theorem R125563 : Reach 125563 := rs (se 1 (by rfl) ⟨94172, by rfl⟩) R188345
theorem R223883 : Reach 223883 := rs (se 1 (by rfl) ⟨167912, by rfl⟩) R335825
theorem R126049 : Reach 126049 := rs (se 2 (by rfl) ⟨47268, by rfl⟩) R94537
theorem R420983 : Reach 420983 := rs (se 1 (by rfl) ⟨315737, by rfl⟩) R631475
theorem R93307 : Reach 93307 := rs (se 1 (by rfl) ⟨69980, by rfl⟩) R139961
theorem R5074319 : Reach 5074319 := rs (se 1 (by rfl) ⟨3805739, by rfl⟩) R7611479
theorem R224801 : Reach 224801 := rs (se 2 (by rfl) ⟨84300, by rfl⟩) R168601
theorem R421523 : Reach 421523 := rs (se 1 (by rfl) ⟨316142, by rfl⟩) R632285
theorem R13758149 : Reach 13758149 := rs (se 4 (by rfl) ⟨1289826, by rfl⟩) R2579653
theorem R225017 : Reach 225017 := rs (se 2 (by rfl) ⟨84381, by rfl⟩) R168763
theorem R225287 : Reach 225287 := rs (se 1 (by rfl) ⟨168965, by rfl⟩) R337931
theorem R126983 : Reach 126983 := rs (se 1 (by rfl) ⟨95237, by rfl⟩) R190475
theorem R225395 : Reach 225395 := rs (se 1 (by rfl) ⟨169046, by rfl⟩) R338093
theorem R258391 : Reach 258391 := rs (se 1 (by rfl) ⟨193793, by rfl⟩) R387587
theorem R225665 : Reach 225665 := rs (se 2 (by rfl) ⟨84624, by rfl⟩) R169249
theorem R225737 : Reach 225737 := rs (se 2 (by rfl) ⟨84651, by rfl⟩) R169303
theorem R225773 : Reach 225773 := rs (se 3 (by rfl) ⟨42332, by rfl⟩) R84665
theorem R324155 : Reach 324155 := rs (se 1 (by rfl) ⟨243116, by rfl⟩) R486233
theorem R94799 : Reach 94799 := rs (se 1 (by rfl) ⟨71099, by rfl⟩) R142199
theorem R225931 : Reach 225931 := rs (se 1 (by rfl) ⟨169448, by rfl⟩) R338897
theorem R94919 : Reach 94919 := rs (se 1 (by rfl) ⟨71189, by rfl⟩) R142379
theorem R881425 : Reach 881425 := rs (se 2 (by rfl) ⟨330534, by rfl⟩) R661069
theorem R95081 : Reach 95081 := rs (se 2 (by rfl) ⟨35655, by rfl⟩) R71311
theorem R914327 : Reach 914327 := rs (se 1 (by rfl) ⟨685745, by rfl⟩) R1371491
theorem R258977 : Reach 258977 := rs (se 2 (by rfl) ⟨97116, by rfl⟩) R194233
theorem R95159 : Reach 95159 := rs (se 1 (by rfl) ⟨71369, by rfl⟩) R142739
theorem R95195 : Reach 95195 := rs (se 1 (by rfl) ⟨71396, by rfl⟩) R142793
theorem R160775 : Reach 160775 := rs (se 1 (by rfl) ⟨120581, by rfl⟩) R241163
theorem R160825 : Reach 160825 := rs (se 2 (by rfl) ⟨60309, by rfl⟩) R120619
theorem R423083 : Reach 423083 := rs (se 1 (by rfl) ⟨317312, by rfl⟩) R634625
theorem R226475 : Reach 226475 := rs (se 1 (by rfl) ⟨169856, by rfl⟩) R339713
theorem R95431 : Reach 95431 := rs (se 1 (by rfl) ⟨71573, by rfl⟩) R143147
theorem R161129 : Reach 161129 := rs (se 2 (by rfl) ⟨60423, by rfl⟩) R120847
theorem R95663 : Reach 95663 := rs (se 1 (by rfl) ⟨71747, by rfl⟩) R143495
theorem R95753 : Reach 95753 := rs (se 2 (by rfl) ⟨35907, by rfl⟩) R71815
theorem R95783 : Reach 95783 := rs (se 1 (by rfl) ⟨71837, by rfl⟩) R143675
theorem R95867 : Reach 95867 := rs (se 1 (by rfl) ⟨71900, by rfl⟩) R143801
theorem R63151 : Reach 63151 := rs (se 1 (by rfl) ⟨47363, by rfl⟩) R94727
theorem R63175 : Reach 63175 := rs (se 1 (by rfl) ⟨47381, by rfl⟩) R94763
theorem R63195 : Reach 63195 := rs (se 1 (by rfl) ⟨47396, by rfl⟩) R94793
theorem R95993 : Reach 95993 := rs (se 2 (by rfl) ⟨35997, by rfl⟩) R71995
theorem R390905 : Reach 390905 := rs (se 2 (by rfl) ⟨146589, by rfl⟩) R293179
theorem R63271 : Reach 63271 := rs (se 1 (by rfl) ⟨47453, by rfl⟩) R94907
theorem R63311 : Reach 63311 := rs (se 1 (by rfl) ⟨47483, by rfl⟩) R94967
theorem R63327 : Reach 63327 := rs (se 1 (by rfl) ⟨47495, by rfl⟩) R94991
theorem R96095 : Reach 96095 := rs (se 1 (by rfl) ⟨72071, by rfl⟩) R144143
theorem R96107 : Reach 96107 := rs (se 1 (by rfl) ⟨72080, by rfl⟩) R144161
theorem R259949 : Reach 259949 := rs (se 3 (by rfl) ⟨48740, by rfl⟩) R97481
theorem R63355 : Reach 63355 := rs (se 1 (by rfl) ⟨47516, by rfl⟩) R95033
theorem R63407 : Reach 63407 := rs (se 1 (by rfl) ⟨47555, by rfl⟩) R95111
theorem R489401 : Reach 489401 := rs (se 2 (by rfl) ⟨183525, by rfl⟩) R367051
theorem R63431 : Reach 63431 := rs (se 1 (by rfl) ⟨47573, by rfl⟩) R95147
theorem R63451 : Reach 63451 := rs (se 1 (by rfl) ⟨47588, by rfl⟩) R95177
theorem R63527 : Reach 63527 := rs (se 1 (by rfl) ⟨47645, by rfl⟩) R95291
theorem R63567 : Reach 63567 := rs (se 1 (by rfl) ⟨47675, by rfl⟩) R95351
theorem R96335 : Reach 96335 := rs (se 1 (by rfl) ⟨72251, by rfl⟩) R144503
theorem R63583 : Reach 63583 := rs (se 1 (by rfl) ⟨47687, by rfl⟩) R95375
theorem R63611 : Reach 63611 := rs (se 1 (by rfl) ⟨47708, by rfl⟩) R95417
theorem R63663 : Reach 63663 := rs (se 1 (by rfl) ⟨47747, by rfl⟩) R95495
theorem R63687 : Reach 63687 := rs (se 1 (by rfl) ⟨47765, by rfl⟩) R95531
theorem R96455 : Reach 96455 := rs (se 1 (by rfl) ⟨72341, by rfl⟩) R144683
theorem R63707 : Reach 63707 := rs (se 1 (by rfl) ⟨47780, by rfl⟩) R95561
theorem R63783 : Reach 63783 := rs (se 1 (by rfl) ⟨47837, by rfl⟩) R95675
theorem R63823 : Reach 63823 := rs (se 1 (by rfl) ⟨47867, by rfl⟩) R95735
theorem R63839 : Reach 63839 := rs (se 1 (by rfl) ⟨47879, by rfl⟩) R95759
theorem R96617 : Reach 96617 := rs (se 2 (by rfl) ⟨36231, by rfl⟩) R72463
theorem R63867 : Reach 63867 := rs (se 1 (by rfl) ⟨47900, by rfl⟩) R95801
theorem R522625 : Reach 522625 := rs (se 2 (by rfl) ⟨195984, by rfl⟩) R391969
theorem R588185 : Reach 588185 := rs (se 2 (by rfl) ⟨220569, by rfl⟩) R441139
theorem R63919 : Reach 63919 := rs (se 1 (by rfl) ⟨47939, by rfl⟩) R95879
theorem R96695 : Reach 96695 := rs (se 1 (by rfl) ⟨72521, by rfl⟩) R145043
theorem R63943 : Reach 63943 := rs (se 1 (by rfl) ⟨47957, by rfl⟩) R95915
theorem R63963 : Reach 63963 := rs (se 1 (by rfl) ⟨47972, by rfl⟩) R95945
theorem R96731 : Reach 96731 := rs (se 1 (by rfl) ⟨72548, by rfl⟩) R145097
theorem R2423317 : Reach 2423317 := rs (se 6 (by rfl) ⟨56796, by rfl⟩) R113593
theorem R64039 : Reach 64039 := rs (se 1 (by rfl) ⟨48029, by rfl⟩) R96059
theorem R64079 : Reach 64079 := rs (se 1 (by rfl) ⟨48059, by rfl⟩) R96119
theorem R64095 : Reach 64095 := rs (se 1 (by rfl) ⟨48071, by rfl⟩) R96143
theorem R64123 : Reach 64123 := rs (se 1 (by rfl) ⟨48092, by rfl⟩) R96185
theorem R64175 : Reach 64175 := rs (se 1 (by rfl) ⟨48131, by rfl⟩) R96263
theorem R64199 : Reach 64199 := rs (se 1 (by rfl) ⟨48149, by rfl⟩) R96299
theorem R424649 : Reach 424649 := rs (se 2 (by rfl) ⟨159243, by rfl⟩) R318487
theorem R64219 : Reach 64219 := rs (se 1 (by rfl) ⟨48164, by rfl⟩) R96329
theorem R326429 : Reach 326429 := rs (se 3 (by rfl) ⟨61205, by rfl⟩) R122411
theorem R64295 : Reach 64295 := rs (se 1 (by rfl) ⟨48221, by rfl⟩) R96443
theorem R64335 : Reach 64335 := rs (se 1 (by rfl) ⟨48251, by rfl⟩) R96503
theorem R64351 : Reach 64351 := rs (se 1 (by rfl) ⟨48263, by rfl⟩) R96527
theorem R64379 : Reach 64379 := rs (se 1 (by rfl) ⟨48284, by rfl⟩) R96569
theorem R64431 : Reach 64431 := rs (se 1 (by rfl) ⟨48323, by rfl⟩) R96647
theorem R97199 : Reach 97199 := rs (se 1 (by rfl) ⟨72899, by rfl⟩) R145799
theorem R64455 : Reach 64455 := rs (se 1 (by rfl) ⟨48341, by rfl⟩) R96683
theorem R64475 : Reach 64475 := rs (se 1 (by rfl) ⟨48356, by rfl⟩) R96713
theorem R97289 : Reach 97289 := rs (se 2 (by rfl) ⟨36483, by rfl⟩) R72967
theorem R64551 : Reach 64551 := rs (se 1 (by rfl) ⟨48413, by rfl⟩) R96827
theorem R97319 : Reach 97319 := rs (se 1 (by rfl) ⟨72989, by rfl⟩) R145979
theorem R64591 : Reach 64591 := rs (se 1 (by rfl) ⟨48443, by rfl⟩) R96887
theorem R64607 : Reach 64607 := rs (se 1 (by rfl) ⟨48455, by rfl⟩) R96911
theorem R64635 : Reach 64635 := rs (se 1 (by rfl) ⟨48476, by rfl⟩) R96953
theorem R97403 : Reach 97403 := rs (se 1 (by rfl) ⟨73052, by rfl⟩) R146105
theorem R64687 : Reach 64687 := rs (se 1 (by rfl) ⟨48515, by rfl⟩) R97031
theorem R64711 : Reach 64711 := rs (se 1 (by rfl) ⟨48533, by rfl⟩) R97067
theorem R64731 : Reach 64731 := rs (se 1 (by rfl) ⟨48548, by rfl⟩) R97097
theorem R97529 : Reach 97529 := rs (se 2 (by rfl) ⟨36573, by rfl⟩) R73147
theorem R64807 : Reach 64807 := rs (se 1 (by rfl) ⟨48605, by rfl⟩) R97211
theorem R64847 : Reach 64847 := rs (se 1 (by rfl) ⟨48635, by rfl⟩) R97271
theorem R64863 : Reach 64863 := rs (se 1 (by rfl) ⟨48647, by rfl⟩) R97295
theorem R97631 : Reach 97631 := rs (se 1 (by rfl) ⟨73223, by rfl⟩) R146447
theorem R97643 : Reach 97643 := rs (se 1 (by rfl) ⟨73232, by rfl⟩) R146465
theorem R64891 : Reach 64891 := rs (se 1 (by rfl) ⟨48668, by rfl⟩) R97337
theorem R64943 : Reach 64943 := rs (se 1 (by rfl) ⟨48707, by rfl⟩) R97415
theorem R64967 : Reach 64967 := rs (se 1 (by rfl) ⟨48725, by rfl⟩) R97451
theorem R64987 : Reach 64987 := rs (se 1 (by rfl) ⟨48740, by rfl⟩) R97481
theorem R163367 : Reach 163367 := rs (se 1 (by rfl) ⟨122525, by rfl⟩) R245051
theorem R65063 : Reach 65063 := rs (se 1 (by rfl) ⟨48797, by rfl⟩) R97595
theorem R65103 : Reach 65103 := rs (se 1 (by rfl) ⟨48827, by rfl⟩) R97655
theorem R97871 : Reach 97871 := rs (se 1 (by rfl) ⟨73403, by rfl⟩) R146807
theorem R65119 : Reach 65119 := rs (se 1 (by rfl) ⟨48839, by rfl⟩) R97679
theorem R65147 : Reach 65147 := rs (se 1 (by rfl) ⟨48860, by rfl⟩) R97721
theorem R65199 : Reach 65199 := rs (se 1 (by rfl) ⟨48899, by rfl⟩) R97799
theorem R65223 : Reach 65223 := rs (se 1 (by rfl) ⟨48917, by rfl⟩) R97835
theorem R97991 : Reach 97991 := rs (se 1 (by rfl) ⟨73493, by rfl⟩) R146987
theorem R65243 : Reach 65243 := rs (se 1 (by rfl) ⟨48932, by rfl⟩) R97865
theorem R65319 : Reach 65319 := rs (se 1 (by rfl) ⟨48989, by rfl⟩) R97979
theorem R65359 : Reach 65359 := rs (se 1 (by rfl) ⟨49019, by rfl⟩) R98039
theorem R360287 : Reach 360287 := rs (se 1 (by rfl) ⟨270215, by rfl⟩) R540431
theorem R65375 : Reach 65375 := rs (se 1 (by rfl) ⟨49031, by rfl⟩) R98063
theorem R163691 : Reach 163691 := rs (se 1 (by rfl) ⟨122768, by rfl⟩) R245537
theorem R98153 : Reach 98153 := rs (se 2 (by rfl) ⟨36807, by rfl⟩) R73615
theorem R65403 : Reach 65403 := rs (se 1 (by rfl) ⟨49052, by rfl⟩) R98105
theorem R65455 : Reach 65455 := rs (se 1 (by rfl) ⟨49091, by rfl⟩) R98183
theorem R98231 : Reach 98231 := rs (se 1 (by rfl) ⟨73673, by rfl⟩) R147347
theorem R65479 : Reach 65479 := rs (se 1 (by rfl) ⟨49109, by rfl⟩) R98219
theorem R65499 : Reach 65499 := rs (se 1 (by rfl) ⟨49124, by rfl⟩) R98249
theorem R98267 : Reach 98267 := rs (se 1 (by rfl) ⟨73700, by rfl⟩) R147401
theorem R65823 : Reach 65823 := rs (se 1 (by rfl) ⟨49367, by rfl⟩) R98735
theorem R98651 : Reach 98651 := rs (se 1 (by rfl) ⟨73988, by rfl⟩) R147977
theorem R65883 : Reach 65883 := rs (se 1 (by rfl) ⟨49412, by rfl⟩) R98825
theorem R164207 : Reach 164207 := rs (se 1 (by rfl) ⟨123155, by rfl⟩) R246311
theorem R65903 : Reach 65903 := rs (se 1 (by rfl) ⟨49427, by rfl⟩) R98855
theorem R65959 : Reach 65959 := rs (se 1 (by rfl) ⟨49469, by rfl⟩) R98939
theorem R66043 : Reach 66043 := rs (se 1 (by rfl) ⟨49532, by rfl⟩) R99065
theorem R328211 : Reach 328211 := rs (se 1 (by rfl) ⟨246158, by rfl⟩) R492317
theorem R98879 : Reach 98879 := rs (se 1 (by rfl) ⟨74159, by rfl⟩) R148319
theorem R66111 : Reach 66111 := rs (se 1 (by rfl) ⟨49583, by rfl⟩) R99167
theorem R66119 : Reach 66119 := rs (se 1 (by rfl) ⟨49589, by rfl⟩) R99179
theorem R393911 : Reach 393911 := rs (se 1 (by rfl) ⟨295433, by rfl⟩) R590867
theorem R98999 : Reach 98999 := rs (se 1 (by rfl) ⟨74249, by rfl⟩) R148499
theorem R393943 : Reach 393943 := rs (se 1 (by rfl) ⟨295457, by rfl⟩) R590915
theorem R66271 : Reach 66271 := rs (se 1 (by rfl) ⟨49703, by rfl⟩) R99407
theorem R66351 : Reach 66351 := rs (se 1 (by rfl) ⟨49763, by rfl⟩) R99527
theorem R99227 : Reach 99227 := rs (se 1 (by rfl) ⟨74420, by rfl⟩) R148841
theorem R66459 : Reach 66459 := rs (se 1 (by rfl) ⟨49844, by rfl⟩) R99689
theorem R66511 : Reach 66511 := rs (se 1 (by rfl) ⟨49883, by rfl⟩) R99767
theorem R66535 : Reach 66535 := rs (se 1 (by rfl) ⟨49901, by rfl⟩) R99803
theorem R164855 : Reach 164855 := rs (se 1 (by rfl) ⟨123641, by rfl⟩) R247283
theorem R164987 : Reach 164987 := rs (se 1 (by rfl) ⟨123740, by rfl⟩) R247481
theorem R66779 : Reach 66779 := rs (se 1 (by rfl) ⟨50084, by rfl⟩) R100169
theorem R1115369 : Reach 1115369 := rs (se 2 (by rfl) ⟨418263, by rfl⟩) R836527
theorem R66847 : Reach 66847 := rs (se 1 (by rfl) ⟨50135, by rfl⟩) R100271
theorem R99623 : Reach 99623 := rs (se 1 (by rfl) ⟨74717, by rfl⟩) R149435
theorem R66855 : Reach 66855 := rs (se 1 (by rfl) ⟨50141, by rfl⟩) R100283
theorem R66907 : Reach 66907 := rs (se 1 (by rfl) ⟨50180, by rfl⟩) R100361
theorem R165215 : Reach 165215 := rs (se 1 (by rfl) ⟨123911, by rfl⟩) R247823
theorem R263519 : Reach 263519 := rs (se 1 (by rfl) ⟨197639, by rfl⟩) R395279
theorem R66927 : Reach 66927 := rs (se 1 (by rfl) ⟨50195, by rfl⟩) R100391
theorem R99707 : Reach 99707 := rs (se 1 (by rfl) ⟨74780, by rfl⟩) R149561
theorem R66939 : Reach 66939 := rs (se 1 (by rfl) ⟨50204, by rfl⟩) R100409
theorem R66983 : Reach 66983 := rs (se 1 (by rfl) ⟨50237, by rfl⟩) R100475
theorem R67015 : Reach 67015 := rs (se 1 (by rfl) ⟨50261, by rfl⟩) R100523
theorem R99833 : Reach 99833 := rs (se 2 (by rfl) ⟨37437, by rfl⟩) R74875
theorem R67067 : Reach 67067 := rs (se 1 (by rfl) ⟨50300, by rfl⟩) R100601
theorem R99935 : Reach 99935 := rs (se 1 (by rfl) ⟨74951, by rfl⟩) R149903
theorem R100103 : Reach 100103 := rs (se 1 (by rfl) ⟨75077, by rfl⟩) R150155
theorem R100151 : Reach 100151 := rs (se 1 (by rfl) ⟨75113, by rfl⟩) R150227
theorem R1705859 : Reach 1705859 := rs (se 1 (by rfl) ⟨1279394, by rfl⟩) R2558789
theorem R100457 : Reach 100457 := rs (se 2 (by rfl) ⟨37671, by rfl⟩) R75343
theorem R329993 : Reach 329993 := rs (se 2 (by rfl) ⟨123747, by rfl⟩) R247495
theorem R5507531 : Reach 5507531 := rs (se 1 (by rfl) ⟨4130648, by rfl⟩) R8261297
theorem R166799 : Reach 166799 := rs (se 1 (by rfl) ⟨125099, by rfl⟩) R250199
theorem R363635 : Reach 363635 := rs (se 1 (by rfl) ⟨272726, by rfl⟩) R545453
theorem R331127 : Reach 331127 := rs (se 1 (by rfl) ⟨248345, by rfl⟩) R496691
theorem R1248641 : Reach 1248641 := rs (se 2 (by rfl) ⟨468240, by rfl⟩) R936481
theorem R167305 : Reach 167305 := rs (se 2 (by rfl) ⟨62739, by rfl⟩) R125479
theorem R167417 : Reach 167417 := rs (se 2 (by rfl) ⟨62781, by rfl⟩) R125563
theorem R331289 : Reach 331289 := rs (se 2 (by rfl) ⟨124233, by rfl⟩) R248467
theorem R265837 : Reach 265837 := rs (se 3 (by rfl) ⟨49844, by rfl⟩) R99689
theorem R102151 : Reach 102151 := rs (se 1 (by rfl) ⟨76613, by rfl⟩) R153227
theorem R331627 : Reach 331627 := rs (se 1 (by rfl) ⟨248720, by rfl⟩) R497441
theorem R233531 : Reach 233531 := rs (se 1 (by rfl) ⟨175148, by rfl⟩) R350297
theorem R168065 : Reach 168065 := rs (se 2 (by rfl) ⟨63024, by rfl⟩) R126049
theorem R398047 : Reach 398047 := rs (se 1 (by rfl) ⟨298535, by rfl⟩) R597071
theorem R168875 : Reach 168875 := rs (se 1 (by rfl) ⟨126656, by rfl⟩) R253313
theorem R693197 : Reach 693197 := rs (se 3 (by rfl) ⟨129974, by rfl⟩) R259949
theorem R562301 : Reach 562301 := rs (se 3 (by rfl) ⟨105431, by rfl⟩) R210863
theorem R71023 : Reach 71023 := rs (se 1 (by rfl) ⟨53267, by rfl⟩) R106535
theorem R71239 : Reach 71239 := rs (se 1 (by rfl) ⟨53429, by rfl⟩) R106859
theorem R136891 : Reach 136891 := rs (se 1 (by rfl) ⟨102668, by rfl⟩) R205337
theorem R169735 : Reach 169735 := rs (se 1 (by rfl) ⟨127301, by rfl⟩) R254603
theorem R301241 : Reach 301241 := rs (se 2 (by rfl) ⟨112965, by rfl⟩) R225931
theorem R334205 : Reach 334205 := rs (se 3 (by rfl) ⟨62663, by rfl⟩) R125327
theorem R72103 : Reach 72103 := rs (se 1 (by rfl) ⟨54077, by rfl⟩) R108155
theorem R137747 : Reach 137747 := rs (se 1 (by rfl) ⟨103310, by rfl⟩) R206621
theorem R7740035 : Reach 7740035 := rs (se 1 (by rfl) ⟨5805026, by rfl⟩) R11610053
theorem R105143 : Reach 105143 := rs (se 1 (by rfl) ⟨78857, by rfl⟩) R157715
theorem R367379 : Reach 367379 := rs (se 1 (by rfl) ⟨275534, by rfl⟩) R551069
theorem R236459 : Reach 236459 := rs (se 1 (by rfl) ⟨177344, by rfl⟩) R354689
theorem R72679 : Reach 72679 := rs (se 1 (by rfl) ⟨54509, by rfl⟩) R109019
theorem R269351 : Reach 269351 := rs (se 1 (by rfl) ⟨202013, by rfl⟩) R404027
theorem R368009 : Reach 368009 := rs (se 2 (by rfl) ⟨138003, by rfl⟩) R276007
theorem R1383961 : Reach 1383961 := rs (se 2 (by rfl) ⟨518985, by rfl⟩) R1037971
theorem R3382879 : Reach 3382879 := rs (se 1 (by rfl) ⟨2537159, by rfl⟩) R5074319
theorem R335663 : Reach 335663 := rs (se 1 (by rfl) ⟨251747, by rfl⟩) R503495
theorem R467153 : Reach 467153 := rs (se 2 (by rfl) ⟨175182, by rfl⟩) R350365
theorem R696833 : Reach 696833 := rs (se 2 (by rfl) ⟨261312, by rfl⟩) R522625
theorem R74335 : Reach 74335 := rs (se 1 (by rfl) ⟨55751, by rfl⟩) R111503
theorem R172651 : Reach 172651 := rs (se 1 (by rfl) ⟨129488, by rfl⟩) R258977
theorem R107129 : Reach 107129 := rs (se 2 (by rfl) ⟨40173, by rfl⟩) R80347
theorem R107183 : Reach 107183 := rs (se 1 (by rfl) ⟨80387, by rfl⟩) R160775
theorem R2859725 : Reach 2859725 := rs (se 3 (by rfl) ⟨536198, by rfl⟩) R1072397
theorem R107419 : Reach 107419 := rs (se 1 (by rfl) ⟨80564, by rfl⟩) R161129
theorem R1057697 : Reach 1057697 := rs (se 2 (by rfl) ⟨396636, by rfl⟩) R793273
theorem R206057 : Reach 206057 := rs (se 2 (by rfl) ⟨77271, by rfl⟩) R154543
theorem R337445 : Reach 337445 := rs (se 4 (by rfl) ⟨31635, by rfl⟩) R63271
theorem R75487 : Reach 75487 := rs (se 1 (by rfl) ⟨56615, by rfl⟩) R113231
theorem R337769 : Reach 337769 := rs (se 2 (by rfl) ⟨126663, by rfl⟩) R253327
theorem R108911 : Reach 108911 := rs (se 1 (by rfl) ⟨81683, by rfl⟩) R163367
theorem R207287 : Reach 207287 := rs (se 1 (by rfl) ⟨155465, by rfl⟩) R310931
theorem R240191 : Reach 240191 := rs (se 1 (by rfl) ⟨180143, by rfl⟩) R360287
theorem R109127 : Reach 109127 := rs (se 1 (by rfl) ⟨81845, by rfl⟩) R163691
theorem R240509 : Reach 240509 := rs (se 3 (by rfl) ⟨45095, by rfl⟩) R90191
theorem R142235 : Reach 142235 := rs (se 1 (by rfl) ⟨106676, by rfl⟩) R213353
theorem R273307 : Reach 273307 := rs (se 1 (by rfl) ⟨204980, by rfl⟩) R409961
theorem R306163 : Reach 306163 := rs (se 1 (by rfl) ⟨229622, by rfl⟩) R459245
theorem R109559 : Reach 109559 := rs (se 1 (by rfl) ⟨82169, by rfl⟩) R164339
theorem R142433 : Reach 142433 := rs (se 2 (by rfl) ⟨53412, by rfl⟩) R106825
theorem R142631 : Reach 142631 := rs (se 1 (by rfl) ⟨106973, by rfl⟩) R213947
theorem R339551 : Reach 339551 := rs (se 1 (by rfl) ⟨254663, by rfl⟩) R509327
theorem R143009 : Reach 143009 := rs (se 2 (by rfl) ⟨53628, by rfl⟩) R107257
theorem R110315 : Reach 110315 := rs (se 1 (by rfl) ⟨82736, by rfl⟩) R165473
theorem R143369 : Reach 143369 := rs (se 2 (by rfl) ⟨53763, by rfl⟩) R107527
theorem R143783 : Reach 143783 := rs (se 1 (by rfl) ⟨107837, by rfl⟩) R215675
theorem R143891 : Reach 143891 := rs (se 1 (by rfl) ⟨107918, by rfl⟩) R215837
theorem R275015 : Reach 275015 := rs (se 1 (by rfl) ⟨206261, by rfl⟩) R412523
theorem R143945 : Reach 143945 := rs (se 2 (by rfl) ⟨53979, by rfl⟩) R107959
theorem R111287 : Reach 111287 := rs (se 1 (by rfl) ⟨83465, by rfl⟩) R166931
theorem R176975 : Reach 176975 := rs (se 1 (by rfl) ⟨132731, by rfl⟩) R265463
theorem R144359 : Reach 144359 := rs (se 1 (by rfl) ⟨108269, by rfl⟩) R216539
theorem R209911 : Reach 209911 := rs (se 1 (by rfl) ⟨157433, by rfl⟩) R314867
theorem R570359 : Reach 570359 := rs (se 1 (by rfl) ⟨427769, by rfl⟩) R855539
theorem R275699 : Reach 275699 := rs (se 1 (by rfl) ⟨206774, by rfl⟩) R413549
theorem R144737 : Reach 144737 := rs (se 2 (by rfl) ⟨54276, by rfl⟩) R108553
theorem R112009 : Reach 112009 := rs (se 2 (by rfl) ⟨42003, by rfl⟩) R84007
theorem R144827 : Reach 144827 := rs (se 1 (by rfl) ⟨108620, by rfl⟩) R217241
theorem R3225091 : Reach 3225091 := rs (se 1 (by rfl) ⟨2418818, by rfl⟩) R4837637
theorem R144953 : Reach 144953 := rs (se 2 (by rfl) ⟨54357, by rfl⟩) R108715
theorem R112441 : Reach 112441 := rs (se 2 (by rfl) ⟨42165, by rfl⟩) R84331
theorem R374615 : Reach 374615 := rs (se 1 (by rfl) ⟨280961, by rfl⟩) R561923
theorem R1128491 : Reach 1128491 := rs (se 1 (by rfl) ⟨846368, by rfl⟩) R1692737
theorem R112745 : Reach 112745 := rs (se 2 (by rfl) ⟨42279, by rfl⟩) R84559
theorem R145619 : Reach 145619 := rs (se 1 (by rfl) ⟨109214, by rfl⟩) R218429
theorem R145673 : Reach 145673 := rs (se 2 (by rfl) ⟨54627, by rfl⟩) R109255
theorem R244079 : Reach 244079 := rs (se 1 (by rfl) ⟨183059, by rfl⟩) R366119
theorem R145889 : Reach 145889 := rs (se 2 (by rfl) ⟨54708, by rfl⟩) R109417
theorem R146195 : Reach 146195 := rs (se 1 (by rfl) ⟨109646, by rfl⟩) R219293
theorem R474011 : Reach 474011 := rs (se 1 (by rfl) ⟨355508, by rfl⟩) R711017
theorem R539635 : Reach 539635 := rs (se 1 (by rfl) ⟨404726, by rfl⟩) R809453
theorem R146555 : Reach 146555 := rs (se 1 (by rfl) ⟨109916, by rfl⟩) R219833
theorem R146681 : Reach 146681 := rs (se 2 (by rfl) ⟨55005, by rfl⟩) R110011
theorem R81263 : Reach 81263 := rs (se 1 (by rfl) ⟨60947, by rfl⟩) R121895
theorem R146825 : Reach 146825 := rs (se 2 (by rfl) ⟨55059, by rfl⟩) R110119
theorem R81319 : Reach 81319 := rs (se 1 (by rfl) ⟨60989, by rfl⟩) R121979
theorem R2440691 : Reach 2440691 := rs (se 1 (by rfl) ⟨1830518, by rfl⟩) R3661037
theorem R146951 : Reach 146951 := rs (se 1 (by rfl) ⟨110213, by rfl⟩) R220427
theorem R147131 : Reach 147131 := rs (se 1 (by rfl) ⟨110348, by rfl⟩) R220697
theorem R81643 : Reach 81643 := rs (se 1 (by rfl) ⟨61232, by rfl⟩) R122465
theorem R245551 : Reach 245551 := rs (se 1 (by rfl) ⟨184163, by rfl⟩) R368327
theorem R147257 : Reach 147257 := rs (se 2 (by rfl) ⟨55221, by rfl⟩) R110443
theorem R147887 : Reach 147887 := rs (se 1 (by rfl) ⟨110915, by rfl⟩) R221831
theorem R344521 : Reach 344521 := rs (se 2 (by rfl) ⟨129195, by rfl⟩) R258391
theorem R147923 : Reach 147923 := rs (se 1 (by rfl) ⟨110942, by rfl⟩) R221885
theorem R148031 : Reach 148031 := rs (se 1 (by rfl) ⟨111023, by rfl⟩) R222047
theorem R606791 : Reach 606791 := rs (se 1 (by rfl) ⟨455093, by rfl⟩) R910187
theorem R115273 : Reach 115273 := rs (se 2 (by rfl) ⟨43227, by rfl⟩) R86455
theorem R148139 : Reach 148139 := rs (se 1 (by rfl) ⟨111104, by rfl⟩) R222209
theorem R82615 : Reach 82615 := rs (se 1 (by rfl) ⟨61961, by rfl⟩) R123923
theorem R312007 : Reach 312007 := rs (se 1 (by rfl) ⟨234005, by rfl⟩) R468011
theorem R213839 : Reach 213839 := rs (se 1 (by rfl) ⟨160379, by rfl⟩) R320759
theorem R148367 : Reach 148367 := rs (se 1 (by rfl) ⟨111275, by rfl⟩) R222551
theorem R640007 : Reach 640007 := rs (se 1 (by rfl) ⟨480005, by rfl⟩) R960011
theorem R214163 : Reach 214163 := rs (se 1 (by rfl) ⟨160622, by rfl⟩) R321245
theorem R148679 : Reach 148679 := rs (se 1 (by rfl) ⟨111509, by rfl⟩) R223019
theorem R1262891 : Reach 1262891 := rs (se 1 (by rfl) ⟨947168, by rfl⟩) R1894337
theorem R148859 : Reach 148859 := rs (se 1 (by rfl) ⟨111644, by rfl⟩) R223289
theorem R214433 : Reach 214433 := rs (se 2 (by rfl) ⟨80412, by rfl⟩) R160825
theorem R148985 : Reach 148985 := rs (se 2 (by rfl) ⟨55869, by rfl⟩) R111739
theorem R149075 : Reach 149075 := rs (se 1 (by rfl) ⟨111806, by rfl⟩) R223613
theorem R411293 : Reach 411293 := rs (se 3 (by rfl) ⟨77117, by rfl⟩) R154235
theorem R149255 : Reach 149255 := rs (se 1 (by rfl) ⟨111941, by rfl⟩) R223883
theorem R739205 : Reach 739205 := rs (se 4 (by rfl) ⟨69300, by rfl⟩) R138601
theorem R280655 : Reach 280655 := rs (se 1 (by rfl) ⟨210491, by rfl⟩) R420983
theorem R149633 : Reach 149633 := rs (se 2 (by rfl) ⟨56112, by rfl⟩) R112225
theorem R149867 : Reach 149867 := rs (se 1 (by rfl) ⟨112400, by rfl⟩) R224801
theorem R182695 : Reach 182695 := rs (se 1 (by rfl) ⟨137021, by rfl⟩) R274043
theorem R281015 : Reach 281015 := rs (se 1 (by rfl) ⟨210761, by rfl⟩) R421523
theorem R444901 : Reach 444901 := rs (se 4 (by rfl) ⟨41709, by rfl⟩) R83419
theorem R150011 : Reach 150011 := rs (se 1 (by rfl) ⟨112508, by rfl⟩) R225017
theorem R150137 : Reach 150137 := rs (se 2 (by rfl) ⟨56301, by rfl⟩) R112603
theorem R150191 : Reach 150191 := rs (se 1 (by rfl) ⟨112643, by rfl⟩) R225287
theorem R84655 : Reach 84655 := rs (se 1 (by rfl) ⟨63491, by rfl⟩) R126983
theorem R150263 : Reach 150263 := rs (se 1 (by rfl) ⟨112697, by rfl⟩) R225395
theorem R150443 : Reach 150443 := rs (se 1 (by rfl) ⟨112832, by rfl⟩) R225665
theorem R150491 : Reach 150491 := rs (se 1 (by rfl) ⟨112868, by rfl⟩) R225737
theorem R150515 : Reach 150515 := rs (se 1 (by rfl) ⟨112886, by rfl⟩) R225773
theorem R216103 : Reach 216103 := rs (se 1 (by rfl) ⟨162077, by rfl⟩) R324155
theorem R281681 : Reach 281681 := rs (se 2 (by rfl) ⟨105630, by rfl⟩) R211261
theorem R609551 : Reach 609551 := rs (se 1 (by rfl) ⟨457163, by rfl⟩) R914327
theorem R3231089 : Reach 3231089 := rs (se 2 (by rfl) ⟨1211658, by rfl⟩) R2423317
theorem R282055 : Reach 282055 := rs (se 1 (by rfl) ⟨211541, by rfl⟩) R423083
theorem R150983 : Reach 150983 := rs (se 1 (by rfl) ⟨113237, by rfl⟩) R226475
theorem R118265 : Reach 118265 := rs (se 2 (by rfl) ⟨44349, by rfl⟩) R88699
theorem R249425 : Reach 249425 := rs (se 2 (by rfl) ⟨93534, by rfl⟩) R187069
theorem R249439 : Reach 249439 := rs (se 1 (by rfl) ⟨187079, by rfl⟩) R374159
theorem R381131 : Reach 381131 := rs (se 1 (by rfl) ⟨285848, by rfl⟩) R571697
theorem R4378853 : Reach 4378853 := rs (se 4 (by rfl) ⟨410517, by rfl⟩) R821035
theorem R283099 : Reach 283099 := rs (se 1 (by rfl) ⟨212324, by rfl⟩) R424649
theorem R1102325 : Reach 1102325 := rs (se 5 (by rfl) ⟨51671, by rfl⟩) R103343
theorem R217619 : Reach 217619 := rs (se 1 (by rfl) ⟨163214, by rfl⟩) R326429
theorem R119951 : Reach 119951 := rs (se 1 (by rfl) ⟨89963, by rfl⟩) R179927
theorem R382201 : Reach 382201 := rs (se 2 (by rfl) ⟨143325, by rfl⟩) R286651
theorem R906997 : Reach 906997 := rs (se 5 (by rfl) ⟨42515, by rfl⟩) R85031
theorem R350057 : Reach 350057 := rs (se 2 (by rfl) ⟨131271, by rfl⟩) R262543
theorem R251855 : Reach 251855 := rs (se 1 (by rfl) ⟨188891, by rfl⟩) R377783
theorem R284705 : Reach 284705 := rs (se 2 (by rfl) ⟨106764, by rfl⟩) R213529
theorem R514127 : Reach 514127 := rs (se 1 (by rfl) ⟨385595, by rfl⟩) R771191
theorem R219401 : Reach 219401 := rs (se 2 (by rfl) ⟨82275, by rfl⟩) R164551
theorem R481625 : Reach 481625 := rs (se 2 (by rfl) ⟨180609, by rfl⟩) R361219
theorem R154081 : Reach 154081 := rs (se 2 (by rfl) ⟨57780, by rfl⟩) R115561
theorem R186943 : Reach 186943 := rs (se 1 (by rfl) ⟨140207, by rfl⟩) R280415
theorem R252827 : Reach 252827 := rs (se 1 (by rfl) ⟨189620, by rfl⟩) R379241
theorem R416933 : Reach 416933 := rs (se 4 (by rfl) ⟨39087, by rfl⟩) R78175
theorem R220535 : Reach 220535 := rs (se 1 (by rfl) ⟨165401, by rfl⟩) R330803
theorem R253601 : Reach 253601 := rs (se 2 (by rfl) ⟨95100, by rfl⟩) R190201
theorem R548801 : Reach 548801 := rs (se 2 (by rfl) ⟨205800, by rfl⟩) R411601
theorem R319697 : Reach 319697 := rs (se 2 (by rfl) ⟨119886, by rfl⟩) R239773
theorem R254299 : Reach 254299 := rs (se 1 (by rfl) ⟨190724, by rfl⟩) R381449
theorem R221615 : Reach 221615 := rs (se 1 (by rfl) ⟨166211, by rfl⟩) R332423
theorem R484055 : Reach 484055 := rs (se 1 (by rfl) ⟨363041, by rfl⟩) R726083
theorem R549827 : Reach 549827 := rs (se 1 (by rfl) ⟨412370, by rfl⟩) R824741
theorem R22438853 : Reach 22438853 := rs (se 4 (by rfl) ⟨2103642, by rfl⟩) R4207285
theorem R156811 : Reach 156811 := rs (se 1 (by rfl) ⟨117608, by rfl⟩) R235217
theorem R517499 : Reach 517499 := rs (se 1 (by rfl) ⟨388124, by rfl⟩) R776249
theorem R222587 : Reach 222587 := rs (se 1 (by rfl) ⟨166940, by rfl⟩) R333881
theorem R124409 : Reach 124409 := rs (se 2 (by rfl) ⟨46653, by rfl⟩) R93307
theorem R91945 : Reach 91945 := rs (se 2 (by rfl) ⟨34479, by rfl⟩) R68959
theorem R321569 : Reach 321569 := rs (se 2 (by rfl) ⟨120588, by rfl⟩) R241177
theorem R321731 : Reach 321731 := rs (se 1 (by rfl) ⟨241298, by rfl⟩) R482597
theorem R354557 : Reach 354557 := rs (se 3 (by rfl) ⟨66479, by rfl⟩) R132959
theorem R223991 : Reach 223991 := rs (se 1 (by rfl) ⟨167993, by rfl⟩) R335987
theorem R125867 : Reach 125867 := rs (se 1 (by rfl) ⟨94400, by rfl⟩) R188801
theorem R584819 : Reach 584819 := rs (se 1 (by rfl) ⟨438614, by rfl⟩) R877229
theorem R93403 : Reach 93403 := rs (se 1 (by rfl) ⟨70052, by rfl⟩) R140105
theorem R1175233 : Reach 1175233 := rs (se 2 (by rfl) ⟨440712, by rfl⟩) R881425
theorem R225071 : Reach 225071 := rs (se 1 (by rfl) ⟨168803, by rfl⟩) R337607
theorem R94007 : Reach 94007 := rs (se 1 (by rfl) ⟨70505, by rfl⟩) R141011
theorem R290621 : Reach 290621 := rs (se 3 (by rfl) ⟨54491, by rfl⟩) R108983
theorem R159617 : Reach 159617 := rs (se 2 (by rfl) ⟨59856, by rfl⟩) R119713
theorem R159695 : Reach 159695 := rs (se 1 (by rfl) ⟨119771, by rfl⟩) R239543
theorem R421955 : Reach 421955 := rs (se 1 (by rfl) ⟨316466, by rfl⟩) R632933
theorem R127241 : Reach 127241 := rs (se 2 (by rfl) ⟨47715, by rfl⟩) R95431
theorem R1208591 : Reach 1208591 := rs (se 1 (by rfl) ⟨906443, by rfl⟩) R1812887
theorem R160175 : Reach 160175 := rs (se 1 (by rfl) ⟨120131, by rfl⟩) R240263
theorem R94715 : Reach 94715 := rs (se 1 (by rfl) ⟨71036, by rfl⟩) R142073
theorem R160319 : Reach 160319 := rs (se 1 (by rfl) ⟨120239, by rfl⟩) R240479
theorem R94841 : Reach 94841 := rs (se 2 (by rfl) ⟨35565, by rfl⟩) R71131
theorem R94895 : Reach 94895 := rs (se 1 (by rfl) ⟨71171, by rfl⟩) R142343
theorem R94943 : Reach 94943 := rs (se 1 (by rfl) ⟨71207, by rfl⟩) R142415
theorem R95207 : Reach 95207 := rs (se 1 (by rfl) ⟨71405, by rfl⟩) R142811
theorem R9172099 : Reach 9172099 := rs (se 1 (by rfl) ⟨6879074, by rfl⟩) R13758149
theorem R160967 : Reach 160967 := rs (se 1 (by rfl) ⟨120725, by rfl⟩) R241451
theorem R160987 : Reach 160987 := rs (se 1 (by rfl) ⟨120740, by rfl⟩) R241481
theorem R95465 : Reach 95465 := rs (se 2 (by rfl) ⟨35799, by rfl⟩) R71599
theorem R95519 : Reach 95519 := rs (se 1 (by rfl) ⟨71639, by rfl⟩) R143279
theorem R95687 : Reach 95687 := rs (se 1 (by rfl) ⟨71765, by rfl⟩) R143531
theorem R63199 : Reach 63199 := rs (se 1 (by rfl) ⟨47399, by rfl⟩) R94799
theorem R96041 : Reach 96041 := rs (se 2 (by rfl) ⟨36015, by rfl⟩) R72031
theorem R63279 : Reach 63279 := rs (se 1 (by rfl) ⟨47459, by rfl⟩) R94919
theorem R96047 : Reach 96047 := rs (se 1 (by rfl) ⟨72035, by rfl⟩) R144071
theorem R325457 : Reach 325457 := rs (se 2 (by rfl) ⟨122046, by rfl⟩) R244093
theorem R63387 : Reach 63387 := rs (se 1 (by rfl) ⟨47540, by rfl⟩) R95081
theorem R63439 : Reach 63439 := rs (se 1 (by rfl) ⟨47579, by rfl⟩) R95159
theorem R63463 : Reach 63463 := rs (se 1 (by rfl) ⟨47597, by rfl⟩) R95195
theorem R96521 : Reach 96521 := rs (se 2 (by rfl) ⟨36195, by rfl⟩) R72391
theorem R63775 : Reach 63775 := rs (se 1 (by rfl) ⟨47831, by rfl⟩) R95663
theorem R162121 : Reach 162121 := rs (se 2 (by rfl) ⟨60795, by rfl⟩) R121591
theorem R63835 : Reach 63835 := rs (se 1 (by rfl) ⟨47876, by rfl⟩) R95753
theorem R63855 : Reach 63855 := rs (se 1 (by rfl) ⟨47891, by rfl⟩) R95783
theorem R96623 : Reach 96623 := rs (se 1 (by rfl) ⟨72467, by rfl⟩) R144935
theorem R63911 : Reach 63911 := rs (se 1 (by rfl) ⟨47933, by rfl⟩) R95867
theorem R63995 : Reach 63995 := rs (se 1 (by rfl) ⟨47996, by rfl⟩) R95993
theorem R260603 : Reach 260603 := rs (se 1 (by rfl) ⟨195452, by rfl⟩) R390905
theorem R293371 : Reach 293371 := rs (se 1 (by rfl) ⟨220028, by rfl⟩) R440057
theorem R64063 : Reach 64063 := rs (se 1 (by rfl) ⟨48047, by rfl⟩) R96095
theorem R64071 : Reach 64071 := rs (se 1 (by rfl) ⟨48053, by rfl⟩) R96107
theorem R96839 : Reach 96839 := rs (se 1 (by rfl) ⟨72629, by rfl⟩) R145259
theorem R96875 : Reach 96875 := rs (se 1 (by rfl) ⟨72656, by rfl⟩) R145313
theorem R162425 : Reach 162425 := rs (se 2 (by rfl) ⟨60909, by rfl⟩) R121819
theorem R326267 : Reach 326267 := rs (se 1 (by rfl) ⟨244700, by rfl⟩) R489401
theorem R64223 : Reach 64223 := rs (se 1 (by rfl) ⟨48167, by rfl⟩) R96335
theorem R424723 : Reach 424723 := rs (se 1 (by rfl) ⟨318542, by rfl⟩) R637085
theorem R64303 : Reach 64303 := rs (se 1 (by rfl) ⟨48227, by rfl⟩) R96455
theorem R97103 : Reach 97103 := rs (se 1 (by rfl) ⟨72827, by rfl⟩) R145655
theorem R64411 : Reach 64411 := rs (se 1 (by rfl) ⟨48308, by rfl⟩) R96617
theorem R392123 : Reach 392123 := rs (se 1 (by rfl) ⟨294092, by rfl⟩) R588185
theorem R64463 : Reach 64463 := rs (se 1 (by rfl) ⟨48347, by rfl⟩) R96695
theorem R64487 : Reach 64487 := rs (se 1 (by rfl) ⟨48365, by rfl⟩) R96731
theorem R97499 : Reach 97499 := rs (se 1 (by rfl) ⟨73124, by rfl⟩) R146249
theorem R64799 : Reach 64799 := rs (se 1 (by rfl) ⟨48599, by rfl⟩) R97199
theorem R359747 : Reach 359747 := rs (se 1 (by rfl) ⟨269810, by rfl⟩) R539621
theorem R64859 : Reach 64859 := rs (se 1 (by rfl) ⟨48644, by rfl⟩) R97289
theorem R64879 : Reach 64879 := rs (se 1 (by rfl) ⟨48659, by rfl⟩) R97319
theorem R97673 : Reach 97673 := rs (se 2 (by rfl) ⟨36627, by rfl⟩) R73255
theorem R64935 : Reach 64935 := rs (se 1 (by rfl) ⟨48701, by rfl⟩) R97403
theorem R65019 : Reach 65019 := rs (se 1 (by rfl) ⟨48764, by rfl⟩) R97529
theorem R65087 : Reach 65087 := rs (se 1 (by rfl) ⟨48815, by rfl⟩) R97631
theorem R65095 : Reach 65095 := rs (se 1 (by rfl) ⟨48821, by rfl⟩) R97643
theorem R65247 : Reach 65247 := rs (se 1 (by rfl) ⟨48935, by rfl⟩) R97871
theorem R98027 : Reach 98027 := rs (se 1 (by rfl) ⟨73520, by rfl⟩) R147041
theorem R65327 : Reach 65327 := rs (se 1 (by rfl) ⟨48995, by rfl⟩) R97991
theorem R196481 : Reach 196481 := rs (se 2 (by rfl) ⟨73680, by rfl⟩) R147361
theorem R65435 : Reach 65435 := rs (se 1 (by rfl) ⟨49076, by rfl⟩) R98153
theorem R229277 : Reach 229277 := rs (se 3 (by rfl) ⟨42989, by rfl⟩) R85979
theorem R65487 : Reach 65487 := rs (se 1 (by rfl) ⟨49115, by rfl⟩) R98231
theorem R98255 : Reach 98255 := rs (se 1 (by rfl) ⟨73691, by rfl⟩) R147383
theorem R65511 : Reach 65511 := rs (se 1 (by rfl) ⟨49133, by rfl⟩) R98267
theorem R65767 : Reach 65767 := rs (se 1 (by rfl) ⟨49325, by rfl⟩) R98651
theorem R98591 : Reach 98591 := rs (se 1 (by rfl) ⟨73943, by rfl⟩) R147887
theorem R98615 : Reach 98615 := rs (se 1 (by rfl) ⟨73961, by rfl⟩) R147923
theorem R98687 : Reach 98687 := rs (se 1 (by rfl) ⟨74015, by rfl⟩) R148031
theorem R65919 : Reach 65919 := rs (se 1 (by rfl) ⟨49439, by rfl⟩) R98879
theorem R98759 : Reach 98759 := rs (se 1 (by rfl) ⟨74069, by rfl⟩) R148139
theorem R262607 : Reach 262607 := rs (se 1 (by rfl) ⟨196955, by rfl⟩) R393911
theorem R65999 : Reach 65999 := rs (se 1 (by rfl) ⟨49499, by rfl⟩) R98999
theorem R98911 : Reach 98911 := rs (se 1 (by rfl) ⟨74183, by rfl⟩) R148367
theorem R459361 : Reach 459361 := rs (se 2 (by rfl) ⟨172260, by rfl⟩) R344521
theorem R66151 : Reach 66151 := rs (se 1 (by rfl) ⟨49613, by rfl⟩) R99227
theorem R426671 : Reach 426671 := rs (se 1 (by rfl) ⟨320003, by rfl⟩) R640007
theorem R99113 : Reach 99113 := rs (se 2 (by rfl) ⟨37167, by rfl⟩) R74335
theorem R99119 : Reach 99119 := rs (se 1 (by rfl) ⟨74339, by rfl⟩) R148679
theorem R230201 : Reach 230201 := rs (se 2 (by rfl) ⟨86325, by rfl⟩) R172651
theorem R66415 : Reach 66415 := rs (se 1 (by rfl) ⟨49811, by rfl⟩) R99623
theorem R99239 : Reach 99239 := rs (se 1 (by rfl) ⟨74429, by rfl⟩) R148859
theorem R66471 : Reach 66471 := rs (se 1 (by rfl) ⟨49853, by rfl⟩) R99707
theorem R525257 : Reach 525257 := rs (se 2 (by rfl) ⟨196971, by rfl⟩) R393943
theorem R99323 : Reach 99323 := rs (se 1 (by rfl) ⟨74492, by rfl⟩) R148985
theorem R66555 : Reach 66555 := rs (se 1 (by rfl) ⟨49916, by rfl⟩) R99833
theorem R99383 : Reach 99383 := rs (se 1 (by rfl) ⟨74537, by rfl⟩) R149075
theorem R66623 : Reach 66623 := rs (se 1 (by rfl) ⟨49967, by rfl⟩) R99935
theorem R427133 : Reach 427133 := rs (se 3 (by rfl) ⟨80087, by rfl⟩) R160175
theorem R99503 : Reach 99503 := rs (se 1 (by rfl) ⟨74627, by rfl⟩) R149255
theorem R66735 : Reach 66735 := rs (se 1 (by rfl) ⟨50051, by rfl⟩) R100103
theorem R66767 : Reach 66767 := rs (se 1 (by rfl) ⟨50075, by rfl⟩) R100151
theorem R492803 : Reach 492803 := rs (se 1 (by rfl) ⟨369602, by rfl⟩) R739205
theorem R66971 : Reach 66971 := rs (se 1 (by rfl) ⟨50228, by rfl⟩) R100457
theorem R99755 : Reach 99755 := rs (se 1 (by rfl) ⟨74816, by rfl⟩) R149633
theorem R99911 : Reach 99911 := rs (se 1 (by rfl) ⟨74933, by rfl⟩) R149867
theorem R3671687 : Reach 3671687 := rs (se 1 (by rfl) ⟨2753765, by rfl⟩) R5507531
theorem R100007 : Reach 100007 := rs (se 1 (by rfl) ⟨75005, by rfl⟩) R150011
theorem R100091 : Reach 100091 := rs (se 1 (by rfl) ⟨75068, by rfl⟩) R150137
theorem R100127 : Reach 100127 := rs (se 1 (by rfl) ⟨75095, by rfl⟩) R150191
theorem R100175 : Reach 100175 := rs (se 1 (by rfl) ⟨75131, by rfl⟩) R150263
theorem R100295 : Reach 100295 := rs (se 1 (by rfl) ⟨75221, by rfl⟩) R150443
theorem R100327 : Reach 100327 := rs (se 1 (by rfl) ⟨75245, by rfl⟩) R150491
theorem R100343 : Reach 100343 := rs (se 1 (by rfl) ⟨75257, by rfl⟩) R150515
theorem R100649 : Reach 100649 := rs (se 2 (by rfl) ⟨37743, by rfl⟩) R75487
theorem R100655 : Reach 100655 := rs (se 1 (by rfl) ⟨75491, by rfl⟩) R150983
theorem R166283 : Reach 166283 := rs (se 1 (by rfl) ⟨124712, by rfl⟩) R249425
theorem R821765 : Reach 821765 := rs (se 4 (by rfl) ⟨77040, by rfl⟩) R154081
theorem R2919235 : Reach 2919235 := rs (se 1 (by rfl) ⟨2189426, by rfl⟩) R4378853
theorem R593201 : Reach 593201 := rs (se 2 (by rfl) ⟨222450, by rfl⟩) R444901
theorem R462131 : Reach 462131 := rs (se 1 (by rfl) ⟨346598, by rfl⟩) R693197
theorem R364409 : Reach 364409 := rs (se 2 (by rfl) ⟨136653, by rfl⟩) R273307
theorem R233371 : Reach 233371 := rs (se 1 (by rfl) ⟨175028, by rfl⟩) R350057
theorem R167903 : Reach 167903 := rs (se 1 (by rfl) ⟨125927, by rfl⟩) R251855
theorem R200827 : Reach 200827 := rs (se 1 (by rfl) ⟨150620, by rfl⟩) R301241
theorem R168551 : Reach 168551 := rs (se 1 (by rfl) ⟨126413, by rfl⟩) R252827
theorem R332585 : Reach 332585 := rs (se 2 (by rfl) ⟨124719, by rfl⟩) R249439
theorem R169067 : Reach 169067 := rs (se 1 (by rfl) ⟨126800, by rfl⟩) R253601
theorem R365867 : Reach 365867 := rs (se 1 (by rfl) ⟨274400, by rfl⟩) R548801
theorem R464555 : Reach 464555 := rs (se 1 (by rfl) ⟨348416, by rfl⟩) R696833
theorem R71419 : Reach 71419 := rs (se 1 (by rfl) ⟨53564, by rfl⟩) R107129
theorem R71455 : Reach 71455 := rs (se 1 (by rfl) ⟨53591, by rfl⟩) R107183
theorem R366551 : Reach 366551 := rs (se 1 (by rfl) ⟨274913, by rfl⟩) R549827
theorem R137371 : Reach 137371 := rs (se 1 (by rfl) ⟨103028, by rfl⟩) R206057
theorem R530729 : Reach 530729 := rs (se 2 (by rfl) ⟨199023, by rfl⟩) R398047
theorem R498149 : Reach 498149 := rs (se 4 (by rfl) ⟨46701, by rfl⟩) R93403
theorem R2038405 : Reach 2038405 := rs (se 4 (by rfl) ⟨191100, by rfl⟩) R382201
theorem R367325 : Reach 367325 := rs (se 3 (by rfl) ⟨68873, by rfl⟩) R137747
theorem R236371 : Reach 236371 := rs (se 1 (by rfl) ⟨177278, by rfl⟩) R354557
theorem R12229465 : Reach 12229465 := rs (se 2 (by rfl) ⟨4586049, by rfl⟩) R9172099
theorem R72607 : Reach 72607 := rs (se 1 (by rfl) ⟨54455, by rfl⟩) R108911
theorem R138191 : Reach 138191 := rs (se 1 (by rfl) ⟨103643, by rfl⟩) R207287
theorem R72751 : Reach 72751 := rs (se 1 (by rfl) ⟨54563, by rfl⟩) R109127
theorem R73039 : Reach 73039 := rs (se 1 (by rfl) ⟨54779, by rfl⟩) R109559
theorem R4300121 : Reach 4300121 := rs (se 2 (by rfl) ⟨1612545, by rfl⟩) R3225091
theorem R73543 : Reach 73543 := rs (se 1 (by rfl) ⟨55157, by rfl⟩) R110315
theorem R106463 : Reach 106463 := rs (se 1 (by rfl) ⟨79847, by rfl⟩) R159695
theorem R106879 : Reach 106879 := rs (se 1 (by rfl) ⟨80159, by rfl⟩) R160319
theorem R74191 : Reach 74191 := rs (se 1 (by rfl) ⟨55643, by rfl⟩) R111287
theorem R107311 : Reach 107311 := rs (se 1 (by rfl) ⟨80483, by rfl⟩) R160967
theorem R566297 : Reach 566297 := rs (se 2 (by rfl) ⟨212361, by rfl⟩) R424723
theorem R75163 : Reach 75163 := rs (se 1 (by rfl) ⟨56372, by rfl⟩) R112745
theorem R173735 : Reach 173735 := rs (se 1 (by rfl) ⟨130301, by rfl⟩) R260603
theorem R108283 : Reach 108283 := rs (se 1 (by rfl) ⟨81212, by rfl⟩) R162425
theorem R108425 : Reach 108425 := rs (se 2 (by rfl) ⟨40659, by rfl⟩) R81319
theorem R1845281 : Reach 1845281 := rs (se 2 (by rfl) ⟨691980, by rfl⟩) R1383961
theorem R239831 : Reach 239831 := rs (se 1 (by rfl) ⟨179873, by rfl⟩) R359747
theorem R108857 : Reach 108857 := rs (se 2 (by rfl) ⟨40821, by rfl⟩) R81643
theorem R109471 : Reach 109471 := rs (se 1 (by rfl) ⟨82103, by rfl⟩) R164207
theorem R404527 : Reach 404527 := rs (se 1 (by rfl) ⟨303395, by rfl⟩) R606791
theorem R339065 : Reach 339065 := rs (se 2 (by rfl) ⟨127149, by rfl⟩) R254299
theorem R142559 : Reach 142559 := rs (se 1 (by rfl) ⟨106919, by rfl⟩) R213839
theorem R109903 : Reach 109903 := rs (se 1 (by rfl) ⟨82427, by rfl⟩) R164855
theorem R109991 : Reach 109991 := rs (se 1 (by rfl) ⟨82493, by rfl⟩) R164987
theorem R142775 : Reach 142775 := rs (se 1 (by rfl) ⟨107081, by rfl⟩) R214163
theorem R110143 : Reach 110143 := rs (se 1 (by rfl) ⟨82607, by rfl⟩) R165215
theorem R175679 : Reach 175679 := rs (se 1 (by rfl) ⟨131759, by rfl⟩) R263519
theorem R110153 : Reach 110153 := rs (se 2 (by rfl) ⟨41307, by rfl⟩) R82615
theorem R142955 : Reach 142955 := rs (se 1 (by rfl) ⟨107216, by rfl⟩) R214433
theorem R274195 : Reach 274195 := rs (se 1 (by rfl) ⟨205646, by rfl⟩) R411293
theorem R143225 : Reach 143225 := rs (se 2 (by rfl) ⟨53709, by rfl⟩) R107419
theorem R209081 : Reach 209081 := rs (se 2 (by rfl) ⟨78405, by rfl⟩) R156811
theorem R733373 : Reach 733373 := rs (se 3 (by rfl) ⟨137507, by rfl⟩) R275015
theorem R111199 : Reach 111199 := rs (se 1 (by rfl) ⟨83399, by rfl⟩) R166799
theorem R242423 : Reach 242423 := rs (se 1 (by rfl) ⟨181817, by rfl⟩) R363635
theorem R406367 : Reach 406367 := rs (se 1 (by rfl) ⟨304775, by rfl⟩) R609551
theorem R832427 : Reach 832427 := rs (se 1 (by rfl) ⟨624320, by rfl⟩) R1248641
theorem R111611 : Reach 111611 := rs (se 1 (by rfl) ⟨83708, by rfl⟩) R167417
theorem R1520957 : Reach 1520957 := rs (se 3 (by rfl) ⟨285179, by rfl⟩) R570359
theorem R112043 : Reach 112043 := rs (se 1 (by rfl) ⟨84032, by rfl⟩) R168065
theorem R145079 : Reach 145079 := rs (se 1 (by rfl) ⟨108809, by rfl⟩) R217619
theorem R243593 : Reach 243593 := rs (se 2 (by rfl) ⟨91347, by rfl⟩) R182695
theorem R112583 : Reach 112583 := rs (se 1 (by rfl) ⟨84437, by rfl⟩) R168875
theorem R374867 : Reach 374867 := rs (se 1 (by rfl) ⟨281150, by rfl⟩) R562301
theorem R79967 : Reach 79967 := rs (se 1 (by rfl) ⟨59975, by rfl⟩) R119951
theorem R112873 : Reach 112873 := rs (se 2 (by rfl) ⟨42327, by rfl⟩) R84655
theorem R342751 : Reach 342751 := rs (se 1 (by rfl) ⟨257063, by rfl⟩) R514127
theorem R146267 : Reach 146267 := rs (se 1 (by rfl) ⟨109700, by rfl⟩) R219401
theorem R5160023 : Reach 5160023 := rs (se 1 (by rfl) ⟨3870017, by rfl⟩) R7740035
theorem R244919 : Reach 244919 := rs (se 1 (by rfl) ⟨183689, by rfl⟩) R367379
theorem R376073 : Reach 376073 := rs (se 2 (by rfl) ⟨141027, by rfl⟩) R282055
theorem R179567 : Reach 179567 := rs (se 1 (by rfl) ⟨134675, by rfl⟩) R269351
theorem R277955 : Reach 277955 := rs (se 1 (by rfl) ⟨208466, by rfl⟩) R416933
theorem R147023 : Reach 147023 := rs (se 1 (by rfl) ⟨110267, by rfl⟩) R220535
theorem R245339 : Reach 245339 := rs (se 1 (by rfl) ⟨184004, by rfl⟩) R368009
theorem R442169 : Reach 442169 := rs (se 2 (by rfl) ⟨165813, by rfl⟩) R331627
theorem R311435 : Reach 311435 := rs (se 1 (by rfl) ⟨233576, by rfl⟩) R467153
theorem R213131 : Reach 213131 := rs (se 1 (by rfl) ⟨159848, by rfl⟩) R319697
theorem R147743 : Reach 147743 := rs (se 1 (by rfl) ⟨110807, by rfl⟩) R221615
theorem R705131 : Reach 705131 := rs (se 1 (by rfl) ⟨528848, by rfl⟩) R1057697
theorem R377465 : Reach 377465 := rs (se 2 (by rfl) ⟨141549, by rfl⟩) R283099
theorem R14959235 : Reach 14959235 := rs (se 1 (by rfl) ⟨11219426, by rfl⟩) R22438853
theorem R344999 : Reach 344999 := rs (se 1 (by rfl) ⟨258749, by rfl⟩) R517499
theorem R148391 : Reach 148391 := rs (se 1 (by rfl) ⟨111293, by rfl⟩) R222587
theorem R82939 : Reach 82939 := rs (se 1 (by rfl) ⟨62204, by rfl⟩) R124409
theorem R279881 : Reach 279881 := rs (se 2 (by rfl) ⟨104955, by rfl⟩) R209911
theorem R214379 : Reach 214379 := rs (se 1 (by rfl) ⟨160784, by rfl⟩) R321569
theorem R214487 : Reach 214487 := rs (se 1 (by rfl) ⟨160865, by rfl⟩) R321731
theorem R214649 : Reach 214649 := rs (se 2 (by rfl) ⟨80493, by rfl⟩) R160987
theorem R280381 : Reach 280381 := rs (se 3 (by rfl) ⟨52571, by rfl⟩) R105143
theorem R149327 : Reach 149327 := rs (se 1 (by rfl) ⟨111995, by rfl⟩) R223991
theorem R149345 : Reach 149345 := rs (se 2 (by rfl) ⟨56004, by rfl⟩) R112009
theorem R83911 : Reach 83911 := rs (se 1 (by rfl) ⟨62933, by rfl⟩) R125867
theorem R182521 : Reach 182521 := rs (se 2 (by rfl) ⟨68445, by rfl⟩) R136891
theorem R149921 : Reach 149921 := rs (se 2 (by rfl) ⟨56220, by rfl⟩) R112441
theorem R150047 : Reach 150047 := rs (se 1 (by rfl) ⟨112535, by rfl⟩) R225071
theorem R281303 : Reach 281303 := rs (se 1 (by rfl) ⟨210977, by rfl⟩) R421955
theorem R84827 : Reach 84827 := rs (se 1 (by rfl) ⟨63620, by rfl⟩) R127241
theorem R805727 : Reach 805727 := rs (se 1 (by rfl) ⟨604295, by rfl⟩) R1208591
theorem R216161 : Reach 216161 := rs (se 2 (by rfl) ⟨81060, by rfl⟩) R162121
theorem R117983 : Reach 117983 := rs (se 1 (by rfl) ⟨88487, by rfl⟩) R176975
theorem R249257 : Reach 249257 := rs (se 2 (by rfl) ⟨93471, by rfl⟩) R186943
theorem R183799 : Reach 183799 := rs (se 1 (by rfl) ⟨137849, by rfl⟩) R275699
theorem R216701 : Reach 216701 := rs (se 3 (by rfl) ⟨40631, by rfl⟩) R81263
theorem R216971 : Reach 216971 := rs (se 1 (by rfl) ⟨162728, by rfl⟩) R325457
theorem R249743 : Reach 249743 := rs (se 1 (by rfl) ⟨187307, by rfl⟩) R374615
theorem R315373 : Reach 315373 := rs (se 3 (by rfl) ⟨59132, by rfl⟩) R118265
theorem R544805 : Reach 544805 := rs (se 4 (by rfl) ⟨51075, by rfl⟩) R102151
theorem R217511 : Reach 217511 := rs (se 1 (by rfl) ⟨163133, by rfl⟩) R326267
theorem R316007 : Reach 316007 := rs (se 1 (by rfl) ⟨237005, by rfl⟩) R474011
theorem R4510505 : Reach 4510505 := rs (se 2 (by rfl) ⟨1691439, by rfl⟩) R3382879
theorem R250685 : Reach 250685 := rs (se 3 (by rfl) ⟨47003, by rfl⟩) R94007
theorem R1627127 : Reach 1627127 := rs (se 1 (by rfl) ⟨1220345, by rfl⟩) R2440691
theorem R152851 : Reach 152851 := rs (se 1 (by rfl) ⟨114638, by rfl⟩) R229277
theorem R218807 : Reach 218807 := rs (se 1 (by rfl) ⟨164105, by rfl⟩) R328211
theorem R743579 : Reach 743579 := rs (se 1 (by rfl) ⟨557684, by rfl⟩) R1115369
theorem R841927 : Reach 841927 := rs (se 1 (by rfl) ⟨631445, by rfl⟩) R1262891
theorem R416009 : Reach 416009 := rs (se 2 (by rfl) ⟨156003, by rfl⟩) R312007
theorem R1137239 : Reach 1137239 := rs (se 1 (by rfl) ⟨852929, by rfl⟩) R1705859
theorem R2939533 : Reach 2939533 := rs (se 3 (by rfl) ⟨551162, by rfl⟩) R1102325
theorem R187103 : Reach 187103 := rs (se 1 (by rfl) ⟨140327, by rfl⟩) R280655
theorem R219995 : Reach 219995 := rs (se 1 (by rfl) ⟨164996, by rfl⟩) R329993
theorem R187343 : Reach 187343 := rs (se 1 (by rfl) ⟨140507, by rfl⟩) R281015
theorem R285677 : Reach 285677 := rs (se 3 (by rfl) ⟨53564, by rfl⟩) R107129
theorem R7625933 : Reach 7625933 := rs (se 3 (by rfl) ⟨1429862, by rfl⟩) R2859725
theorem R187787 : Reach 187787 := rs (se 1 (by rfl) ⟨140840, by rfl⟩) R281681
theorem R2154059 : Reach 2154059 := rs (se 1 (by rfl) ⟨1615544, by rfl⟩) R3231089
theorem R220751 : Reach 220751 := rs (se 1 (by rfl) ⟨165563, by rfl⟩) R331127
theorem R220859 : Reach 220859 := rs (se 1 (by rfl) ⟨165644, by rfl⟩) R331289
theorem R1564645 : Reach 1564645 := rs (se 4 (by rfl) ⟨146685, by rfl⟩) R293371
theorem R155687 : Reach 155687 := rs (se 1 (by rfl) ⟨116765, by rfl⟩) R233531
theorem R254087 : Reach 254087 := rs (se 1 (by rfl) ⟨190565, by rfl⟩) R381131
theorem R614789 : Reach 614789 := rs (se 4 (by rfl) ⟨57636, by rfl⟩) R115273
theorem R254573 : Reach 254573 := rs (se 3 (by rfl) ⟨47732, by rfl⟩) R95465
theorem R189803 : Reach 189803 := rs (se 1 (by rfl) ⟨142352, by rfl⟩) R284705
theorem R288137 : Reach 288137 := rs (se 2 (by rfl) ⟨108051, by rfl⟩) R216103
theorem R321083 : Reach 321083 := rs (se 1 (by rfl) ⟨240812, by rfl⟩) R481625
theorem R222803 : Reach 222803 := rs (se 1 (by rfl) ⟨167102, by rfl⟩) R334205
theorem R223073 : Reach 223073 := rs (se 2 (by rfl) ⟨83652, by rfl⟩) R167305
theorem R157639 : Reach 157639 := rs (se 1 (by rfl) ⟨118229, by rfl⟩) R236459
theorem R354449 : Reach 354449 := rs (se 2 (by rfl) ⟨132918, by rfl⟩) R265837
theorem R1566977 : Reach 1566977 := rs (se 2 (by rfl) ⟨587616, by rfl⟩) R1175233
theorem R223775 : Reach 223775 := rs (se 1 (by rfl) ⟨167831, by rfl⟩) R335663
theorem R1632869 : Reach 1632869 := rs (se 4 (by rfl) ⟨153081, by rfl⟩) R306163
theorem R322703 : Reach 322703 := rs (se 1 (by rfl) ⟨242027, by rfl⟩) R484055
theorem R224963 : Reach 224963 := rs (se 1 (by rfl) ⟨168722, by rfl⟩) R337445
theorem R225179 : Reach 225179 := rs (se 1 (by rfl) ⟨168884, by rfl⟩) R337769
theorem R160127 : Reach 160127 := rs (se 1 (by rfl) ⟨120095, by rfl⟩) R240191
theorem R94697 : Reach 94697 := rs (se 2 (by rfl) ⟨35511, by rfl⟩) R71023
theorem R160339 : Reach 160339 := rs (se 1 (by rfl) ⟨120254, by rfl⟩) R240509
theorem R94823 : Reach 94823 := rs (se 1 (by rfl) ⟨71117, by rfl⟩) R142235
theorem R94955 : Reach 94955 := rs (se 1 (by rfl) ⟨71216, by rfl⟩) R142433
theorem R389879 : Reach 389879 := rs (se 1 (by rfl) ⟨292409, by rfl⟩) R584819
theorem R94985 : Reach 94985 := rs (se 2 (by rfl) ⟨35619, by rfl⟩) R71239
theorem R95087 : Reach 95087 := rs (se 1 (by rfl) ⟨71315, by rfl⟩) R142631
theorem R1209329 : Reach 1209329 := rs (se 2 (by rfl) ⟨453498, by rfl⟩) R906997
theorem R226313 : Reach 226313 := rs (se 2 (by rfl) ⟨84867, by rfl⟩) R169735
theorem R226367 : Reach 226367 := rs (se 1 (by rfl) ⟨169775, by rfl⟩) R339551
theorem R95339 : Reach 95339 := rs (se 1 (by rfl) ⟨71504, by rfl⟩) R143009
theorem R193747 : Reach 193747 := rs (se 1 (by rfl) ⟨145310, by rfl⟩) R290621
theorem R95579 : Reach 95579 := rs (se 1 (by rfl) ⟨71684, by rfl⟩) R143369
theorem R95855 : Reach 95855 := rs (se 1 (by rfl) ⟨71891, by rfl⟩) R143783
theorem R63143 : Reach 63143 := rs (se 1 (by rfl) ⟨47357, by rfl⟩) R94715
theorem R95927 : Reach 95927 := rs (se 1 (by rfl) ⟨71945, by rfl⟩) R143891
theorem R95963 : Reach 95963 := rs (se 1 (by rfl) ⟨71972, by rfl⟩) R143945
theorem R63227 : Reach 63227 := rs (se 1 (by rfl) ⟨47420, by rfl⟩) R94841
theorem R63263 : Reach 63263 := rs (se 1 (by rfl) ⟨47447, by rfl⟩) R94895
theorem R63295 : Reach 63295 := rs (se 1 (by rfl) ⟨47471, by rfl⟩) R94943
theorem R96137 : Reach 96137 := rs (se 2 (by rfl) ⟨36051, by rfl⟩) R72103
theorem R63471 : Reach 63471 := rs (se 1 (by rfl) ⟨47603, by rfl⟩) R95207
theorem R96239 : Reach 96239 := rs (se 1 (by rfl) ⟨72179, by rfl⟩) R144359
theorem R63643 : Reach 63643 := rs (se 1 (by rfl) ⟨47732, by rfl⟩) R95465
theorem R63679 : Reach 63679 := rs (se 1 (by rfl) ⟨47759, by rfl⟩) R95519
theorem R96491 : Reach 96491 := rs (se 1 (by rfl) ⟨72368, by rfl⟩) R144737
theorem R96551 : Reach 96551 := rs (se 1 (by rfl) ⟨72413, by rfl⟩) R144827
theorem R63791 : Reach 63791 := rs (se 1 (by rfl) ⟨47843, by rfl⟩) R95687
theorem R96635 : Reach 96635 := rs (se 1 (by rfl) ⟨72476, by rfl⟩) R144953
theorem R64027 : Reach 64027 := rs (se 1 (by rfl) ⟨48020, by rfl⟩) R96041
theorem R64031 : Reach 64031 := rs (se 1 (by rfl) ⟨48023, by rfl⟩) R96047
theorem R96905 : Reach 96905 := rs (se 2 (by rfl) ⟨36339, by rfl⟩) R72679
theorem R719513 : Reach 719513 := rs (se 2 (by rfl) ⟨269817, by rfl⟩) R539635
theorem R752327 : Reach 752327 := rs (se 1 (by rfl) ⟨564245, by rfl⟩) R1128491
theorem R97079 : Reach 97079 := rs (se 1 (by rfl) ⟨72809, by rfl⟩) R145619
theorem R64347 : Reach 64347 := rs (se 1 (by rfl) ⟨48260, by rfl⟩) R96521
theorem R97115 : Reach 97115 := rs (se 1 (by rfl) ⟨72836, by rfl⟩) R145673
theorem R490373 : Reach 490373 := rs (se 4 (by rfl) ⟨45972, by rfl⟩) R91945
theorem R162719 : Reach 162719 := rs (se 1 (by rfl) ⟨122039, by rfl⟩) R244079
theorem R64415 : Reach 64415 := rs (se 1 (by rfl) ⟨48311, by rfl⟩) R96623
theorem R97259 : Reach 97259 := rs (se 1 (by rfl) ⟨72944, by rfl⟩) R145889
theorem R64559 : Reach 64559 := rs (se 1 (by rfl) ⟨48419, by rfl⟩) R96839
theorem R64583 : Reach 64583 := rs (se 1 (by rfl) ⟨48437, by rfl⟩) R96875
theorem R97463 : Reach 97463 := rs (se 1 (by rfl) ⟨73097, by rfl⟩) R146195
theorem R64735 : Reach 64735 := rs (se 1 (by rfl) ⟨48551, by rfl⟩) R97103
theorem R261415 : Reach 261415 := rs (se 1 (by rfl) ⟨196061, by rfl⟩) R392123
theorem R97703 : Reach 97703 := rs (se 1 (by rfl) ⟨73277, by rfl⟩) R146555
theorem R64999 : Reach 64999 := rs (se 1 (by rfl) ⟨48749, by rfl⟩) R97499
theorem R97787 : Reach 97787 := rs (se 1 (by rfl) ⟨73340, by rfl⟩) R146681
theorem R97883 : Reach 97883 := rs (se 1 (by rfl) ⟨73412, by rfl⟩) R146825
theorem R65115 : Reach 65115 := rs (se 1 (by rfl) ⟨48836, by rfl⟩) R97673
theorem R425645 : Reach 425645 := rs (se 3 (by rfl) ⟨79808, by rfl⟩) R159617
theorem R97967 : Reach 97967 := rs (se 1 (by rfl) ⟨73475, by rfl⟩) R146951
theorem R327401 : Reach 327401 := rs (se 2 (by rfl) ⟨122775, by rfl⟩) R245551
theorem R98087 : Reach 98087 := rs (se 1 (by rfl) ⟨73565, by rfl⟩) R147131
theorem R65351 : Reach 65351 := rs (se 1 (by rfl) ⟨49013, by rfl⟩) R98027
theorem R98171 : Reach 98171 := rs (se 1 (by rfl) ⟨73628, by rfl⟩) R147257
theorem R130987 : Reach 130987 := rs (se 1 (by rfl) ⟨98240, by rfl⟩) R196481
theorem R65503 : Reach 65503 := rs (se 1 (by rfl) ⟨49127, by rfl⟩) R98255
theorem R98495 : Reach 98495 := rs (se 1 (by rfl) ⟨73871, by rfl⟩) R147743
theorem R65727 : Reach 65727 := rs (se 1 (by rfl) ⟨49295, by rfl⟩) R98591
theorem R65743 : Reach 65743 := rs (se 1 (by rfl) ⟨49307, by rfl⟩) R98615
theorem R65791 : Reach 65791 := rs (se 1 (by rfl) ⟨49343, by rfl⟩) R98687
theorem R65839 : Reach 65839 := rs (se 1 (by rfl) ⟨49379, by rfl⟩) R98759
theorem R557549 : Reach 557549 := rs (se 3 (by rfl) ⟨104540, by rfl⟩) R209081
theorem R66075 : Reach 66075 := rs (se 1 (by rfl) ⟨49556, by rfl⟩) R99113
theorem R66079 : Reach 66079 := rs (se 1 (by rfl) ⟨49559, by rfl⟩) R99119
theorem R98921 : Reach 98921 := rs (se 2 (by rfl) ⟨37095, by rfl⟩) R74191
theorem R98927 : Reach 98927 := rs (se 1 (by rfl) ⟨74195, by rfl⟩) R148391
theorem R66159 : Reach 66159 := rs (se 1 (by rfl) ⟨49619, by rfl⟩) R99239
theorem R66215 : Reach 66215 := rs (se 1 (by rfl) ⟨49661, by rfl⟩) R99323
theorem R66255 : Reach 66255 := rs (se 1 (by rfl) ⟨49691, by rfl⟩) R99383
theorem R66335 : Reach 66335 := rs (se 1 (by rfl) ⟨49751, by rfl⟩) R99503
theorem R131881 : Reach 131881 := rs (se 2 (by rfl) ⟨49455, by rfl⟩) R98911
theorem R328535 : Reach 328535 := rs (se 1 (by rfl) ⟨246401, by rfl⟩) R492803
theorem R66503 : Reach 66503 := rs (se 1 (by rfl) ⟨49877, by rfl⟩) R99755
theorem R66607 : Reach 66607 := rs (se 1 (by rfl) ⟨49955, by rfl⟩) R99911
theorem R66671 : Reach 66671 := rs (se 1 (by rfl) ⟨50003, by rfl⟩) R100007
theorem R66727 : Reach 66727 := rs (se 1 (by rfl) ⟨50045, by rfl⟩) R100091
theorem R66751 : Reach 66751 := rs (se 1 (by rfl) ⟨50063, by rfl⟩) R100127
theorem R99551 : Reach 99551 := rs (se 1 (by rfl) ⟨74663, by rfl⟩) R149327
theorem R66783 : Reach 66783 := rs (se 1 (by rfl) ⟨50087, by rfl⟩) R100175
theorem R99563 : Reach 99563 := rs (se 1 (by rfl) ⟨74672, by rfl⟩) R149345
theorem R66863 : Reach 66863 := rs (se 1 (by rfl) ⟨50147, by rfl⟩) R100295
theorem R66895 : Reach 66895 := rs (se 1 (by rfl) ⟨50171, by rfl⟩) R100343
theorem R67099 : Reach 67099 := rs (se 1 (by rfl) ⟨50324, by rfl⟩) R100649
theorem R67103 : Reach 67103 := rs (se 1 (by rfl) ⟨50327, by rfl⟩) R100655
theorem R99947 : Reach 99947 := rs (se 1 (by rfl) ⟨74960, by rfl⟩) R149921
theorem R100031 : Reach 100031 := rs (se 1 (by rfl) ⟨75023, by rfl⟩) R150047
theorem R100217 : Reach 100217 := rs (se 2 (by rfl) ⟨37581, by rfl⟩) R75163
theorem R166171 : Reach 166171 := rs (se 1 (by rfl) ⟨124628, by rfl⟩) R249257
theorem R919997 : Reach 919997 := rs (se 3 (by rfl) ⟨172499, by rfl⟩) R344999
theorem R166495 : Reach 166495 := rs (se 1 (by rfl) ⟨124871, by rfl⟩) R249743
theorem R133769 : Reach 133769 := rs (se 2 (by rfl) ⟨50163, by rfl⟩) R100327
theorem R16714421 : Reach 16714421 := rs (se 5 (by rfl) ⟨783488, by rfl⟩) R1566977
theorem R363203 : Reach 363203 := rs (se 1 (by rfl) ⟨272402, by rfl⟩) R544805
theorem R167123 : Reach 167123 := rs (se 1 (by rfl) ⟨125342, by rfl⟩) R250685
theorem R1084751 : Reach 1084751 := rs (se 1 (by rfl) ⟨813563, by rfl⟩) R1627127
theorem R495719 : Reach 495719 := rs (se 1 (by rfl) ⟨371789, by rfl⟩) R743579
theorem R332099 : Reach 332099 := rs (se 1 (by rfl) ⟨249074, by rfl⟩) R498149
theorem R758159 : Reach 758159 := rs (se 1 (by rfl) ⟨568619, by rfl⟩) R1137239
theorem R5083955 : Reach 5083955 := rs (se 1 (by rfl) ⟨3812966, by rfl⟩) R7625933
theorem R365593 : Reach 365593 := rs (se 2 (by rfl) ⟨137097, by rfl⟩) R274195
theorem R70975 : Reach 70975 := rs (se 1 (by rfl) ⟨53231, by rfl⟩) R106463
theorem R169391 : Reach 169391 := rs (se 1 (by rfl) ⟨127043, by rfl⟩) R254087
theorem R267769 : Reach 267769 := rs (se 2 (by rfl) ⟨100413, by rfl⟩) R200827
theorem R169715 : Reach 169715 := rs (se 1 (by rfl) ⟨127286, by rfl⟩) R254573
theorem R72283 : Reach 72283 := rs (se 1 (by rfl) ⟨54212, by rfl⟩) R108425
theorem R236299 : Reach 236299 := rs (se 1 (by rfl) ⟨177224, by rfl⟩) R354449
theorem R72571 : Reach 72571 := rs (se 1 (by rfl) ⟨54428, by rfl⟩) R108857
theorem R203801 : Reach 203801 := rs (se 2 (by rfl) ⟨76425, by rfl⟩) R152851
theorem R1088579 : Reach 1088579 := rs (se 1 (by rfl) ⟨816434, by rfl⟩) R1632869
theorem R73327 : Reach 73327 := rs (se 1 (by rfl) ⟨54995, by rfl⟩) R109991
theorem R73435 : Reach 73435 := rs (se 1 (by rfl) ⟨55076, by rfl⟩) R110153
theorem R368509 : Reach 368509 := rs (se 3 (by rfl) ⟨69095, by rfl⟩) R138191
theorem R106751 : Reach 106751 := rs (se 1 (by rfl) ⟨80063, by rfl⟩) R160127
theorem R1122569 : Reach 1122569 := rs (se 2 (by rfl) ⟨420963, by rfl⟩) R841927
theorem R270911 : Reach 270911 := rs (se 1 (by rfl) ⟨203183, by rfl⟩) R406367
theorem R74407 : Reach 74407 := rs (se 1 (by rfl) ⟨55805, by rfl⟩) R111611
theorem R1581869 : Reach 1581869 := rs (se 3 (by rfl) ⟨296600, by rfl⟩) R593201
theorem R74695 : Reach 74695 := rs (se 1 (by rfl) ⟨56021, by rfl⟩) R112043
theorem R75055 : Reach 75055 := rs (se 1 (by rfl) ⟨56291, by rfl⟩) R112583
theorem R501551 : Reach 501551 := rs (se 1 (by rfl) ⟨376163, by rfl⟩) R752327
theorem R108479 : Reach 108479 := rs (se 1 (by rfl) ⟨81359, by rfl⟩) R162719
theorem R174649 : Reach 174649 := rs (se 2 (by rfl) ⟨65493, by rfl⟩) R130987
theorem R207623 : Reach 207623 := rs (se 1 (by rfl) ⟨155717, by rfl⟩) R311435
theorem R142087 : Reach 142087 := rs (se 1 (by rfl) ⟨106565, by rfl⟩) R213131
theorem R470087 : Reach 470087 := rs (se 1 (by rfl) ⟨352565, by rfl⟩) R705131
theorem R9972823 : Reach 9972823 := rs (se 1 (by rfl) ⟨7479617, by rfl⟩) R14959235
theorem R142505 : Reach 142505 := rs (se 2 (by rfl) ⟨53439, by rfl⟩) R106879
theorem R142919 : Reach 142919 := rs (se 1 (by rfl) ⟨107189, by rfl⟩) R214379
theorem R142991 : Reach 142991 := rs (se 1 (by rfl) ⟨107243, by rfl⟩) R214487
theorem R143081 : Reach 143081 := rs (se 2 (by rfl) ⟨53655, by rfl⟩) R107311
theorem R143099 : Reach 143099 := rs (se 1 (by rfl) ⟨107324, by rfl⟩) R214649
theorem R700285 : Reach 700285 := rs (se 3 (by rfl) ⟨131303, by rfl⟩) R262607
theorem R110585 : Reach 110585 := rs (se 2 (by rfl) ⟨41469, by rfl⟩) R82939
theorem R110855 : Reach 110855 := rs (se 1 (by rfl) ⟨83141, by rfl⟩) R166283
theorem R144107 : Reach 144107 := rs (se 1 (by rfl) ⟨108080, by rfl⟩) R216161
theorem R308087 : Reach 308087 := rs (se 1 (by rfl) ⟨231065, by rfl⟩) R462131
theorem R144377 : Reach 144377 := rs (se 2 (by rfl) ⟨54141, by rfl⟩) R108283
theorem R373841 : Reach 373841 := rs (se 2 (by rfl) ⟨140190, by rfl⟩) R280381
theorem R144467 : Reach 144467 := rs (se 1 (by rfl) ⟨108350, by rfl⟩) R216701
theorem R242939 : Reach 242939 := rs (se 1 (by rfl) ⟨182204, by rfl⟩) R364409
theorem R144647 : Reach 144647 := rs (se 1 (by rfl) ⟨108485, by rfl⟩) R216971
theorem R210185 : Reach 210185 := rs (se 2 (by rfl) ⟨78819, by rfl⟩) R157639
theorem R111881 : Reach 111881 := rs (se 2 (by rfl) ⟨41955, by rfl⟩) R83911
theorem R111935 : Reach 111935 := rs (se 1 (by rfl) ⟨83951, by rfl⟩) R167903
theorem R145007 : Reach 145007 := rs (se 1 (by rfl) ⟨108755, by rfl⟩) R217511
theorem R243361 : Reach 243361 := rs (se 2 (by rfl) ⟨91260, by rfl⟩) R182521
theorem R210671 : Reach 210671 := rs (se 1 (by rfl) ⟨158003, by rfl⟩) R316007
theorem R112367 : Reach 112367 := rs (se 1 (by rfl) ⟨84275, by rfl⟩) R168551
theorem R15677509 : Reach 15677509 := rs (se 4 (by rfl) ⟨1469766, by rfl⟩) R2939533
theorem R112711 : Reach 112711 := rs (se 1 (by rfl) ⟨84533, by rfl⟩) R169067
theorem R243911 : Reach 243911 := rs (se 1 (by rfl) ⟨182933, by rfl⟩) R365867
theorem R768365 : Reach 768365 := rs (se 3 (by rfl) ⟨144068, by rfl⟩) R288137
theorem R145871 : Reach 145871 := rs (se 1 (by rfl) ⟨109403, by rfl⟩) R218807
theorem R145961 : Reach 145961 := rs (se 2 (by rfl) ⟨54735, by rfl⟩) R109471
theorem R244367 : Reach 244367 := rs (se 1 (by rfl) ⟨183275, by rfl⟩) R366551
theorem R539369 : Reach 539369 := rs (se 2 (by rfl) ⟨202263, by rfl⟩) R404527
theorem R277339 : Reach 277339 := rs (se 1 (by rfl) ⟨208004, by rfl⟩) R416009
theorem R146537 : Reach 146537 := rs (se 2 (by rfl) ⟨54951, by rfl⟩) R109903
theorem R244883 : Reach 244883 := rs (se 1 (by rfl) ⟨183662, by rfl⟩) R367325
theorem R146663 : Reach 146663 := rs (se 1 (by rfl) ⟨109997, by rfl⟩) R219995
theorem R245065 : Reach 245065 := rs (se 2 (by rfl) ⟨91899, by rfl⟩) R183799
theorem R146857 : Reach 146857 := rs (se 2 (by rfl) ⟨55071, by rfl⟩) R110143
theorem R2866747 : Reach 2866747 := rs (se 1 (by rfl) ⟨2150060, by rfl⟩) R4300121
theorem R147167 : Reach 147167 := rs (se 1 (by rfl) ⟨110375, by rfl⟩) R220751
theorem R147239 : Reach 147239 := rs (se 1 (by rfl) ⟨110429, by rfl⟩) R220859
theorem R213245 : Reach 213245 := rs (se 3 (by rfl) ⟨39983, by rfl⟩) R79967
theorem R409859 : Reach 409859 := rs (se 1 (by rfl) ⟨307394, by rfl⟩) R614789
theorem R377531 : Reach 377531 := rs (se 1 (by rfl) ⟨283148, by rfl⟩) R566297
theorem R213785 : Reach 213785 := rs (se 2 (by rfl) ⟨80169, by rfl⟩) R160339
theorem R148265 : Reach 148265 := rs (se 2 (by rfl) ⟨55599, by rfl⟩) R111199
theorem R214055 : Reach 214055 := rs (se 1 (by rfl) ⟨160541, by rfl⟩) R321083
theorem R148535 : Reach 148535 := rs (se 1 (by rfl) ⟨111401, by rfl⟩) R222803
theorem R115823 : Reach 115823 := rs (se 1 (by rfl) ⟨86867, by rfl⟩) R173735
theorem R148715 : Reach 148715 := rs (se 1 (by rfl) ⟨111536, by rfl⟩) R223073
theorem R1230187 : Reach 1230187 := rs (se 1 (by rfl) ⟨922640, by rfl⟩) R1845281
theorem R149183 : Reach 149183 := rs (se 1 (by rfl) ⟨111887, by rfl⟩) R223775
theorem R215135 : Reach 215135 := rs (se 1 (by rfl) ⟨161351, by rfl⟩) R322703
theorem R2148605 : Reach 2148605 := rs (se 3 (by rfl) ⟨402863, by rfl⟩) R805727
theorem R117119 : Reach 117119 := rs (se 1 (by rfl) ⟨87839, by rfl⟩) R175679
theorem R149975 : Reach 149975 := rs (se 1 (by rfl) ⟨112481, by rfl⟩) R224963
theorem R150119 : Reach 150119 := rs (se 1 (by rfl) ⟨112589, by rfl⟩) R225179
theorem R183161 : Reach 183161 := rs (se 2 (by rfl) ⟨68685, by rfl⟩) R137371
theorem R150497 : Reach 150497 := rs (se 2 (by rfl) ⟨56436, by rfl⟩) R112873
theorem R314621 : Reach 314621 := rs (se 3 (by rfl) ⟨58991, by rfl⟩) R117983
theorem R806219 : Reach 806219 := rs (se 1 (by rfl) ⟨604664, by rfl⟩) R1209329
theorem R150875 : Reach 150875 := rs (se 1 (by rfl) ⟨113156, by rfl⟩) R226313
theorem R150911 : Reach 150911 := rs (se 1 (by rfl) ⟨113183, by rfl⟩) R226367
theorem R315161 : Reach 315161 := rs (se 2 (by rfl) ⟨118185, by rfl⟩) R236371
theorem R16305953 : Reach 16305953 := rs (se 2 (by rfl) ⟨6114732, by rfl⟩) R12229465
theorem R249911 : Reach 249911 := rs (se 1 (by rfl) ⟨187433, by rfl⟩) R374867
theorem R348553 : Reach 348553 := rs (se 2 (by rfl) ⟨130707, by rfl⟩) R261415
theorem R479675 : Reach 479675 := rs (se 1 (by rfl) ⟨359756, by rfl⟩) R719513
theorem R250715 : Reach 250715 := rs (se 1 (by rfl) ⟨188036, by rfl⟩) R376073
theorem R119711 : Reach 119711 := rs (se 1 (by rfl) ⟨89783, by rfl⟩) R179567
theorem R185303 : Reach 185303 := rs (se 1 (by rfl) ⟨138977, by rfl⟩) R277955
theorem R283763 : Reach 283763 := rs (se 1 (by rfl) ⟨212822, by rfl⟩) R425645
theorem R218267 : Reach 218267 := rs (se 1 (by rfl) ⟨163700, by rfl⟩) R327401
theorem R2086193 : Reach 2086193 := rs (se 2 (by rfl) ⟨782322, by rfl⟩) R1564645
theorem R415165 : Reach 415165 := rs (se 3 (by rfl) ⟨77843, by rfl⟩) R155687
theorem R284447 : Reach 284447 := rs (se 1 (by rfl) ⟨213335, by rfl⟩) R426671
theorem R153467 : Reach 153467 := rs (se 1 (by rfl) ⟨115100, by rfl⟩) R230201
theorem R350171 : Reach 350171 := rs (se 1 (by rfl) ⟨262628, by rfl⟩) R525257
theorem R284755 : Reach 284755 := rs (se 1 (by rfl) ⟨213566, by rfl⟩) R427133
theorem R612481 : Reach 612481 := rs (se 2 (by rfl) ⟨229680, by rfl⟩) R459361
theorem R186587 : Reach 186587 := rs (se 1 (by rfl) ⟨139940, by rfl⟩) R279881
theorem R88553 : Reach 88553 := rs (se 2 (by rfl) ⟨33207, by rfl⟩) R66415
theorem R1006573 : Reach 1006573 := rs (se 3 (by rfl) ⟨188732, by rfl⟩) R377465
theorem R547843 : Reach 547843 := rs (se 1 (by rfl) ⟨410882, by rfl⟩) R821765
theorem R187535 : Reach 187535 := rs (se 1 (by rfl) ⟨140651, by rfl⟩) R281303
theorem R3007003 : Reach 3007003 := rs (se 1 (by rfl) ⟨2255252, by rfl⟩) R4510505
theorem R221723 : Reach 221723 := rs (se 1 (by rfl) ⟨166292, by rfl⟩) R332585
theorem R3892313 : Reach 3892313 := rs (se 2 (by rfl) ⟨1459617, by rfl⟩) R2919235
theorem R353819 : Reach 353819 := rs (se 1 (by rfl) ⟨265364, by rfl⟩) R530729
theorem R9791165 : Reach 9791165 := rs (se 3 (by rfl) ⟨1835843, by rfl⟩) R3671687
theorem R1238813 : Reach 1238813 := rs (se 3 (by rfl) ⟨232277, by rfl⟩) R464555
theorem R124735 : Reach 124735 := rs (se 1 (by rfl) ⟨93551, by rfl⟩) R187103
theorem R124895 : Reach 124895 := rs (se 1 (by rfl) ⟨93671, by rfl⟩) R187343
theorem R190451 : Reach 190451 := rs (se 1 (by rfl) ⟨142838, by rfl⟩) R285677
theorem R125191 : Reach 125191 := rs (se 1 (by rfl) ⟨93893, by rfl⟩) R187787
theorem R1436039 : Reach 1436039 := rs (se 1 (by rfl) ⟨1077029, by rfl⟩) R2154059
theorem R420497 : Reach 420497 := rs (se 2 (by rfl) ⟨157686, by rfl⟩) R315373
theorem R126535 : Reach 126535 := rs (se 1 (by rfl) ⟨94901, by rfl⟩) R189803
theorem R159887 : Reach 159887 := rs (se 1 (by rfl) ⟨119915, by rfl⟩) R239831
theorem R258329 : Reach 258329 := rs (se 2 (by rfl) ⟨96873, by rfl⟩) R193747
theorem R226043 : Reach 226043 := rs (se 1 (by rfl) ⟨169532, by rfl⟩) R339065
theorem R95039 : Reach 95039 := rs (se 1 (by rfl) ⟨71279, by rfl⟩) R142559
theorem R226205 : Reach 226205 := rs (se 3 (by rfl) ⟨42413, by rfl⟩) R84827
theorem R95183 : Reach 95183 := rs (se 1 (by rfl) ⟨71387, by rfl⟩) R142775
theorem R95225 : Reach 95225 := rs (se 2 (by rfl) ⟨35709, by rfl⟩) R71419
theorem R95273 : Reach 95273 := rs (se 2 (by rfl) ⟨35727, by rfl⟩) R71455
theorem R95303 : Reach 95303 := rs (se 1 (by rfl) ⟨71477, by rfl⟩) R142955
theorem R95483 : Reach 95483 := rs (se 1 (by rfl) ⟨71612, by rfl⟩) R143225
theorem R488915 : Reach 488915 := rs (se 1 (by rfl) ⟨366686, by rfl⟩) R733373
theorem R63131 : Reach 63131 := rs (se 1 (by rfl) ⟨47348, by rfl⟩) R94697
theorem R63215 : Reach 63215 := rs (se 1 (by rfl) ⟨47411, by rfl⟩) R94823
theorem R63303 : Reach 63303 := rs (se 1 (by rfl) ⟨47477, by rfl⟩) R94955
theorem R161615 : Reach 161615 := rs (se 1 (by rfl) ⟨121211, by rfl⟩) R242423
theorem R259919 : Reach 259919 := rs (se 1 (by rfl) ⟨194939, by rfl⟩) R389879
theorem R63323 : Reach 63323 := rs (se 1 (by rfl) ⟨47492, by rfl⟩) R94985
theorem R63391 : Reach 63391 := rs (se 1 (by rfl) ⟨47543, by rfl⟩) R95087
theorem R554951 : Reach 554951 := rs (se 1 (by rfl) ⟨416213, by rfl⟩) R832427
theorem R63559 : Reach 63559 := rs (se 1 (by rfl) ⟨47669, by rfl⟩) R95339
theorem R2717873 : Reach 2717873 := rs (se 2 (by rfl) ⟨1019202, by rfl⟩) R2038405
theorem R1013971 : Reach 1013971 := rs (se 1 (by rfl) ⟨760478, by rfl⟩) R1520957
theorem R63719 : Reach 63719 := rs (se 1 (by rfl) ⟨47789, by rfl⟩) R95579
theorem R457001 : Reach 457001 := rs (se 2 (by rfl) ⟨171375, by rfl⟩) R342751
theorem R63903 : Reach 63903 := rs (se 1 (by rfl) ⟨47927, by rfl⟩) R95855
theorem R63951 : Reach 63951 := rs (se 1 (by rfl) ⟨47963, by rfl⟩) R95927
theorem R96719 : Reach 96719 := rs (se 1 (by rfl) ⟨72539, by rfl⟩) R145079
theorem R63975 : Reach 63975 := rs (se 1 (by rfl) ⟨47981, by rfl⟩) R95963
theorem R96809 : Reach 96809 := rs (se 2 (by rfl) ⟨36303, by rfl⟩) R72607
theorem R64091 : Reach 64091 := rs (se 1 (by rfl) ⟨48068, by rfl⟩) R96137
theorem R162395 : Reach 162395 := rs (se 1 (by rfl) ⟨121796, by rfl⟩) R243593
theorem R64159 : Reach 64159 := rs (se 1 (by rfl) ⟨48119, by rfl⟩) R96239
theorem R97001 : Reach 97001 := rs (se 2 (by rfl) ⟨36375, by rfl⟩) R72751
theorem R64327 : Reach 64327 := rs (se 1 (by rfl) ⟨48245, by rfl⟩) R96491
theorem R64367 : Reach 64367 := rs (se 1 (by rfl) ⟨48275, by rfl⟩) R96551
theorem R64423 : Reach 64423 := rs (se 1 (by rfl) ⟨48317, by rfl⟩) R96635
theorem R64603 : Reach 64603 := rs (se 1 (by rfl) ⟨48452, by rfl⟩) R96905
theorem R97385 : Reach 97385 := rs (se 2 (by rfl) ⟨36519, by rfl⟩) R73039
theorem R64719 : Reach 64719 := rs (se 1 (by rfl) ⟨48539, by rfl⟩) R97079
theorem R64743 : Reach 64743 := rs (se 1 (by rfl) ⟨48557, by rfl⟩) R97115
theorem R97511 : Reach 97511 := rs (se 1 (by rfl) ⟨73133, by rfl⟩) R146267
theorem R326915 : Reach 326915 := rs (se 1 (by rfl) ⟨245186, by rfl⟩) R490373
theorem R64839 : Reach 64839 := rs (se 1 (by rfl) ⟨48629, by rfl⟩) R97259
theorem R3440015 : Reach 3440015 := rs (se 1 (by rfl) ⟨2580011, by rfl⟩) R5160023
theorem R64975 : Reach 64975 := rs (se 1 (by rfl) ⟨48731, by rfl⟩) R97463
theorem R163279 : Reach 163279 := rs (se 1 (by rfl) ⟨122459, by rfl⟩) R244919
theorem R1244645 : Reach 1244645 := rs (se 4 (by rfl) ⟨116685, by rfl⟩) R233371
theorem R65135 : Reach 65135 := rs (se 1 (by rfl) ⟨48851, by rfl⟩) R97703
theorem R65191 : Reach 65191 := rs (se 1 (by rfl) ⟨48893, by rfl⟩) R97787
theorem R98015 : Reach 98015 := rs (se 1 (by rfl) ⟨73511, by rfl⟩) R147023
theorem R163559 : Reach 163559 := rs (se 1 (by rfl) ⟨122669, by rfl⟩) R245339
theorem R65255 : Reach 65255 := rs (se 1 (by rfl) ⟨48941, by rfl⟩) R97883
theorem R98057 : Reach 98057 := rs (se 2 (by rfl) ⟨36771, by rfl⟩) R73543
theorem R65311 : Reach 65311 := rs (se 1 (by rfl) ⟨48983, by rfl⟩) R97967
theorem R65391 : Reach 65391 := rs (se 1 (by rfl) ⟨49043, by rfl⟩) R98087
theorem R294779 : Reach 294779 := rs (se 1 (by rfl) ⟨221084, by rfl⟩) R442169
theorem R65447 : Reach 65447 := rs (se 1 (by rfl) ⟨49085, by rfl⟩) R98171
theorem R65663 : Reach 65663 := rs (se 1 (by rfl) ⟨49247, by rfl⟩) R98495
theorem R65947 : Reach 65947 := rs (se 1 (by rfl) ⟨49460, by rfl⟩) R98921
theorem R65951 : Reach 65951 := rs (se 1 (by rfl) ⟨49463, by rfl⟩) R98927
theorem R98843 : Reach 98843 := rs (se 1 (by rfl) ⟨74132, by rfl⟩) R148265
theorem R99023 : Reach 99023 := rs (se 1 (by rfl) ⟨74267, by rfl⟩) R148535
theorem R66367 : Reach 66367 := rs (se 1 (by rfl) ⟨49775, by rfl⟩) R99551
theorem R99143 : Reach 99143 := rs (se 1 (by rfl) ⟨74357, by rfl⟩) R148715
theorem R66375 : Reach 66375 := rs (se 1 (by rfl) ⟨49781, by rfl⟩) R99563
theorem R99209 : Reach 99209 := rs (se 2 (by rfl) ⟨37203, by rfl⟩) R74407
theorem R66631 : Reach 66631 := rs (se 1 (by rfl) ⟨49973, by rfl⟩) R99947
theorem R99455 : Reach 99455 := rs (se 1 (by rfl) ⟨74591, by rfl⟩) R149183
theorem R66687 : Reach 66687 := rs (se 1 (by rfl) ⟨50015, by rfl⟩) R100031
theorem R66811 : Reach 66811 := rs (se 1 (by rfl) ⟨50108, by rfl⟩) R100217
theorem R99593 : Reach 99593 := rs (se 2 (by rfl) ⟨37347, by rfl⟩) R74695
theorem R722429 : Reach 722429 := rs (se 3 (by rfl) ⟨135455, by rfl⟩) R270911
theorem R99983 : Reach 99983 := rs (se 1 (by rfl) ⟨74987, by rfl⟩) R149975
theorem R100073 : Reach 100073 := rs (se 2 (by rfl) ⟨37527, by rfl⟩) R75055
theorem R100079 : Reach 100079 := rs (se 1 (by rfl) ⟨75059, by rfl⟩) R150119
theorem R11142947 : Reach 11142947 := rs (se 1 (by rfl) ⟨8357210, by rfl⟩) R16714421
theorem R1640249 : Reach 1640249 := rs (se 2 (by rfl) ⟨615093, by rfl⟩) R1230187
theorem R100331 : Reach 100331 := rs (se 1 (by rfl) ⟨75248, by rfl⟩) R150497
theorem R723167 : Reach 723167 := rs (se 1 (by rfl) ⟨542375, by rfl⟩) R1084751
theorem R100583 : Reach 100583 := rs (se 1 (by rfl) ⟨75437, by rfl⟩) R150875
theorem R100607 : Reach 100607 := rs (se 1 (by rfl) ⟨75455, by rfl⟩) R150911
theorem R166313 : Reach 166313 := rs (se 2 (by rfl) ⟨62367, by rfl⟩) R124735
theorem R166607 : Reach 166607 := rs (se 1 (by rfl) ⟨124955, by rfl⟩) R249911
theorem R330479 : Reach 330479 := rs (se 1 (by rfl) ⟨247859, by rfl⟩) R495719
theorem R756701 : Reach 756701 := rs (se 3 (by rfl) ⟨141881, by rfl⟩) R283763
theorem R167143 : Reach 167143 := rs (se 1 (by rfl) ⟨125357, by rfl⟩) R250715
theorem R232865 : Reach 232865 := rs (se 2 (by rfl) ⟨87324, by rfl⟩) R174649
theorem R102311 : Reach 102311 := rs (se 1 (by rfl) ⟨76733, by rfl⟩) R153467
theorem R233447 : Reach 233447 := rs (se 1 (by rfl) ⟨175085, by rfl⟩) R350171
theorem R725719 : Reach 725719 := rs (se 1 (by rfl) ⟨544289, by rfl⟩) R1088579
theorem R168713 : Reach 168713 := rs (se 2 (by rfl) ⟨63267, by rfl⟩) R126535
theorem R71167 : Reach 71167 := rs (se 1 (by rfl) ⟨53375, by rfl⟩) R106751
theorem R464737 : Reach 464737 := rs (se 2 (by rfl) ⟨174276, by rfl⟩) R348553
theorem R1054579 : Reach 1054579 := rs (se 1 (by rfl) ⟨790934, by rfl⟩) R1581869
theorem R2594875 : Reach 2594875 := rs (se 1 (by rfl) ⟨1946156, by rfl⟩) R3892313
theorem R235879 : Reach 235879 := rs (se 1 (by rfl) ⟨176909, by rfl⟩) R353819
theorem R825875 : Reach 825875 := rs (se 1 (by rfl) ⟨619406, by rfl⟩) R1238813
theorem R334367 : Reach 334367 := rs (se 1 (by rfl) ⟨250775, by rfl⟩) R501551
theorem R236141 : Reach 236141 := rs (se 3 (by rfl) ⟨44276, by rfl⟩) R88553
theorem R72319 : Reach 72319 := rs (se 1 (by rfl) ⟨54239, by rfl⟩) R108479
theorem R957359 : Reach 957359 := rs (se 1 (by rfl) ⟨718019, by rfl⟩) R1436039
theorem R73723 : Reach 73723 := rs (se 1 (by rfl) ⟨55292, by rfl⟩) R110585
theorem R106591 : Reach 106591 := rs (se 1 (by rfl) ⟨79943, by rfl⟩) R159887
theorem R73903 : Reach 73903 := rs (se 1 (by rfl) ⟨55427, by rfl⟩) R110855
theorem R172219 : Reach 172219 := rs (se 1 (by rfl) ⟨129164, by rfl⟩) R258329
theorem R1351961 : Reach 1351961 := rs (se 2 (by rfl) ⟨506985, by rfl⟩) R1013971
theorem R500093 : Reach 500093 := rs (se 3 (by rfl) ⟨93767, by rfl⟩) R187535
theorem R205391 : Reach 205391 := rs (se 1 (by rfl) ⟨154043, by rfl⟩) R308087
theorem R140123 : Reach 140123 := rs (se 1 (by rfl) ⟨105092, by rfl⟩) R210185
theorem R74587 : Reach 74587 := rs (se 1 (by rfl) ⟨55940, by rfl⟩) R111881
theorem R74623 : Reach 74623 := rs (se 1 (by rfl) ⟨55967, by rfl⟩) R111935
theorem R369785 : Reach 369785 := rs (se 2 (by rfl) ⟨138669, by rfl⟩) R277339
theorem R140447 : Reach 140447 := rs (se 1 (by rfl) ⟨105335, by rfl⟩) R210671
theorem R74911 : Reach 74911 := rs (se 1 (by rfl) ⟨56183, by rfl⟩) R112367
theorem R107743 : Reach 107743 := rs (se 1 (by rfl) ⟨80807, by rfl⟩) R161615
theorem R173279 : Reach 173279 := rs (se 1 (by rfl) ⟨129959, by rfl⟩) R259919
theorem R369967 : Reach 369967 := rs (se 1 (by rfl) ⟨277475, by rfl⟩) R554951
theorem R730457 : Reach 730457 := rs (se 2 (by rfl) ⟨273921, by rfl⟩) R547843
theorem R1811915 : Reach 1811915 := rs (se 1 (by rfl) ⟨1358936, by rfl⟩) R2717873
theorem R304667 : Reach 304667 := rs (se 1 (by rfl) ⟨228500, by rfl⟩) R457001
theorem R108263 : Reach 108263 := rs (se 1 (by rfl) ⟨81197, by rfl⟩) R162395
theorem R829763 : Reach 829763 := rs (se 1 (by rfl) ⟨622322, by rfl⟩) R1244645
theorem R109039 : Reach 109039 := rs (se 1 (by rfl) ⟨81779, by rfl⟩) R163559
theorem R142163 : Reach 142163 := rs (se 1 (by rfl) ⟨106622, by rfl⟩) R213245
theorem R273239 : Reach 273239 := rs (se 1 (by rfl) ⟨204929, by rfl⟩) R409859
theorem R371699 : Reach 371699 := rs (se 1 (by rfl) ⟨278774, by rfl⟩) R557549
theorem R142523 : Reach 142523 := rs (se 1 (by rfl) ⟨106892, by rfl⟩) R213785
theorem R142703 : Reach 142703 := rs (se 1 (by rfl) ⟨107027, by rfl⟩) R214055
theorem R4009337 : Reach 4009337 := rs (se 2 (by rfl) ⟨1503501, by rfl⟩) R3007003
theorem R175841 : Reach 175841 := rs (se 2 (by rfl) ⟨65940, by rfl⟩) R131881
theorem R667685 : Reach 667685 := rs (se 4 (by rfl) ⟨62595, by rfl⟩) R125191
theorem R143423 : Reach 143423 := rs (se 1 (by rfl) ⟨107567, by rfl⟩) R215135
theorem R78079 : Reach 78079 := rs (se 1 (by rfl) ⟨58559, by rfl⟩) R117119
theorem R242135 : Reach 242135 := rs (se 1 (by rfl) ⟨181601, by rfl⟩) R363203
theorem R111415 : Reach 111415 := rs (se 1 (by rfl) ⟨83561, by rfl⟩) R167123
theorem R209747 : Reach 209747 := rs (se 1 (by rfl) ⟨157310, by rfl⟩) R314621
theorem R537479 : Reach 537479 := rs (se 1 (by rfl) ⟨403109, by rfl⟩) R806219
theorem R210107 : Reach 210107 := rs (se 1 (by rfl) ⟨157580, by rfl⟩) R315161
theorem R505439 : Reach 505439 := rs (se 1 (by rfl) ⟨379079, by rfl⟩) R758159
theorem R308861 : Reach 308861 := rs (se 3 (by rfl) ⟨57911, by rfl⟩) R115823
theorem R3389303 : Reach 3389303 := rs (se 1 (by rfl) ⟨2541977, by rfl⟩) R5083955
theorem R79807 : Reach 79807 := rs (se 1 (by rfl) ⟨59855, by rfl⟩) R119711
theorem R145511 : Reach 145511 := rs (se 1 (by rfl) ⟨109133, by rfl⟩) R218267
theorem R112927 : Reach 112927 := rs (se 1 (by rfl) ⟨84695, by rfl⟩) R169391
theorem R113143 : Reach 113143 := rs (se 1 (by rfl) ⟨84857, by rfl⟩) R169715
theorem R933713 : Reach 933713 := rs (se 2 (by rfl) ⟨350142, by rfl⟩) R700285
theorem R507869 : Reach 507869 := rs (se 3 (by rfl) ⟨95225, by rfl⟩) R190451
theorem R147815 : Reach 147815 := rs (se 1 (by rfl) ⟨110861, by rfl⟩) R221723
theorem R83263 : Reach 83263 := rs (se 1 (by rfl) ⟨62447, by rfl⟩) R124895
theorem R378533 : Reach 378533 := rs (se 4 (by rfl) ⟨35487, by rfl⟩) R70975
theorem R280331 : Reach 280331 := rs (se 1 (by rfl) ⟨210248, by rfl⟩) R420497
theorem R313391 : Reach 313391 := rs (se 1 (by rfl) ⟨235043, by rfl⟩) R470087
theorem R870821 : Reach 870821 := rs (se 4 (by rfl) ⟨81639, by rfl⟩) R163279
theorem R1428101 : Reach 1428101 := rs (se 4 (by rfl) ⟨133884, by rfl⟩) R267769
theorem R543469 : Reach 543469 := rs (se 3 (by rfl) ⟨101900, by rfl⟩) R203801
theorem R150281 : Reach 150281 := rs (se 2 (by rfl) ⟨56355, by rfl⟩) R112711
theorem R379673 : Reach 379673 := rs (se 2 (by rfl) ⟨142377, by rfl⟩) R284755
theorem R150695 : Reach 150695 := rs (se 1 (by rfl) ⟨113021, by rfl⟩) R226043
theorem R150803 : Reach 150803 := rs (se 1 (by rfl) ⟨113102, by rfl⟩) R226205
theorem R249227 : Reach 249227 := rs (se 1 (by rfl) ⟨186920, by rfl⟩) R373841
theorem R315065 : Reach 315065 := rs (se 2 (by rfl) ⟨118149, by rfl⟩) R236299
theorem R512243 : Reach 512243 := rs (se 1 (by rfl) ⟨384182, by rfl⟩) R768365
theorem R3822329 : Reach 3822329 := rs (se 2 (by rfl) ⟨1433373, by rfl⟩) R2866747
theorem R217943 : Reach 217943 := rs (se 1 (by rfl) ⟨163457, by rfl⟩) R326915
theorem R251687 : Reach 251687 := rs (se 1 (by rfl) ⟨188765, by rfl⟩) R377531
theorem R219023 : Reach 219023 := rs (se 1 (by rfl) ⟨164267, by rfl⟩) R328535
theorem R1432403 : Reach 1432403 := rs (se 1 (by rfl) ⟨1074302, by rfl⟩) R2148605
theorem R613331 : Reach 613331 := rs (se 1 (by rfl) ⟨459998, by rfl⟩) R919997
theorem R221399 : Reach 221399 := rs (se 1 (by rfl) ⟨166049, by rfl⟩) R332099
theorem R319783 : Reach 319783 := rs (se 1 (by rfl) ⟨239837, by rfl⟩) R479675
theorem R221561 : Reach 221561 := rs (se 2 (by rfl) ⟨83085, by rfl⟩) R166171
theorem R123535 : Reach 123535 := rs (se 1 (by rfl) ⟨92651, by rfl⟩) R185303
theorem R221993 : Reach 221993 := rs (se 2 (by rfl) ⟨83247, by rfl⟩) R166495
theorem R5563181 : Reach 5563181 := rs (se 3 (by rfl) ⟨1043096, by rfl⟩) R2086193
theorem R189449 : Reach 189449 := rs (se 2 (by rfl) ⟨71043, by rfl⟩) R142087
theorem R189631 : Reach 189631 := rs (se 1 (by rfl) ⟨142223, by rfl⟩) R284447
theorem R13297097 : Reach 13297097 := rs (se 2 (by rfl) ⟨4986411, by rfl⟩) R9972823
theorem R124391 : Reach 124391 := rs (se 1 (by rfl) ⟨93293, by rfl⟩) R186587
theorem R26109773 : Reach 26109773 := rs (se 3 (by rfl) ⟨4895582, by rfl⟩) R9791165
theorem R748379 : Reach 748379 := rs (se 1 (by rfl) ⟨561284, by rfl⟩) R1122569
theorem R487457 : Reach 487457 := rs (se 2 (by rfl) ⟨182796, by rfl⟩) R365593
theorem R356717 : Reach 356717 := rs (se 3 (by rfl) ⟨66884, by rfl⟩) R133769
theorem R553553 : Reach 553553 := rs (se 2 (by rfl) ⟨207582, by rfl⟩) R415165
theorem R553661 : Reach 553661 := rs (se 3 (by rfl) ⟨103811, by rfl⟩) R207623
theorem R95003 : Reach 95003 := rs (se 1 (by rfl) ⟨71252, by rfl⟩) R142505
theorem R324481 : Reach 324481 := rs (se 2 (by rfl) ⟨121680, by rfl⟩) R243361
theorem R488429 : Reach 488429 := rs (se 3 (by rfl) ⟨91580, by rfl⟩) R183161
theorem R95279 : Reach 95279 := rs (se 1 (by rfl) ⟨71459, by rfl⟩) R142919
theorem R95327 : Reach 95327 := rs (se 1 (by rfl) ⟨71495, by rfl⟩) R142991
theorem R95387 : Reach 95387 := rs (se 1 (by rfl) ⟨71540, by rfl⟩) R143081
theorem R95399 : Reach 95399 := rs (se 1 (by rfl) ⟨71549, by rfl⟩) R143099
theorem R20903345 : Reach 20903345 := rs (se 2 (by rfl) ⟨7838754, by rfl⟩) R15677509
theorem R816641 : Reach 816641 := rs (se 2 (by rfl) ⟨306240, by rfl⟩) R612481
theorem R173930165 : Reach 173930165 := rs (se 5 (by rfl) ⟨8152976, by rfl⟩) R16305953
theorem R96071 : Reach 96071 := rs (se 1 (by rfl) ⟨72053, by rfl⟩) R144107
theorem R63359 : Reach 63359 := rs (se 1 (by rfl) ⟨47519, by rfl⟩) R95039
theorem R63455 : Reach 63455 := rs (se 1 (by rfl) ⟨47591, by rfl⟩) R95183
theorem R63483 : Reach 63483 := rs (se 1 (by rfl) ⟨47612, by rfl⟩) R95225
theorem R96251 : Reach 96251 := rs (se 1 (by rfl) ⟨72188, by rfl⟩) R144377
theorem R63515 : Reach 63515 := rs (se 1 (by rfl) ⟨47636, by rfl⟩) R95273
theorem R63535 : Reach 63535 := rs (se 1 (by rfl) ⟨47651, by rfl⟩) R95303
theorem R96311 : Reach 96311 := rs (se 1 (by rfl) ⟨72233, by rfl⟩) R144467
theorem R96377 : Reach 96377 := rs (se 2 (by rfl) ⟨36141, by rfl⟩) R72283
theorem R63655 : Reach 63655 := rs (se 1 (by rfl) ⟨47741, by rfl⟩) R95483
theorem R161959 : Reach 161959 := rs (se 1 (by rfl) ⟨121469, by rfl⟩) R242939
theorem R96431 : Reach 96431 := rs (se 1 (by rfl) ⟨72323, by rfl⟩) R144647
theorem R325943 : Reach 325943 := rs (se 1 (by rfl) ⟨244457, by rfl⟩) R488915
theorem R96671 : Reach 96671 := rs (se 1 (by rfl) ⟨72503, by rfl⟩) R145007
theorem R96761 : Reach 96761 := rs (se 2 (by rfl) ⟨36285, by rfl⟩) R72571
theorem R1342097 : Reach 1342097 := rs (se 2 (by rfl) ⟨503286, by rfl⟩) R1006573
theorem R162607 : Reach 162607 := rs (se 1 (by rfl) ⟨121955, by rfl⟩) R243911
theorem R64479 : Reach 64479 := rs (se 1 (by rfl) ⟨48359, by rfl⟩) R96719
theorem R97247 : Reach 97247 := rs (se 1 (by rfl) ⟨72935, by rfl⟩) R145871
theorem R64539 : Reach 64539 := rs (se 1 (by rfl) ⟨48404, by rfl⟩) R96809
theorem R97307 : Reach 97307 := rs (se 1 (by rfl) ⟨72980, by rfl⟩) R145961
theorem R162911 : Reach 162911 := rs (se 1 (by rfl) ⟨122183, by rfl⟩) R244367
theorem R326753 : Reach 326753 := rs (se 2 (by rfl) ⟨122532, by rfl⟩) R245065
theorem R359579 : Reach 359579 := rs (se 1 (by rfl) ⟨269684, by rfl⟩) R539369
theorem R64667 : Reach 64667 := rs (se 1 (by rfl) ⟨48500, by rfl⟩) R97001
theorem R195809 : Reach 195809 := rs (se 2 (by rfl) ⟨73428, by rfl⟩) R146857
theorem R64923 : Reach 64923 := rs (se 1 (by rfl) ⟨48692, by rfl⟩) R97385
theorem R97691 : Reach 97691 := rs (se 1 (by rfl) ⟨73268, by rfl⟩) R146537
theorem R163255 : Reach 163255 := rs (se 1 (by rfl) ⟨122441, by rfl⟩) R244883
theorem R97769 : Reach 97769 := rs (se 2 (by rfl) ⟨36663, by rfl⟩) R73327
theorem R65007 : Reach 65007 := rs (se 1 (by rfl) ⟨48755, by rfl⟩) R97511
theorem R97775 : Reach 97775 := rs (se 1 (by rfl) ⟨73331, by rfl⟩) R146663
theorem R2293343 : Reach 2293343 := rs (se 1 (by rfl) ⟨1720007, by rfl⟩) R3440015
theorem R97913 : Reach 97913 := rs (se 2 (by rfl) ⟨36717, by rfl⟩) R73435
theorem R65343 : Reach 65343 := rs (se 1 (by rfl) ⟨49007, by rfl⟩) R98015
theorem R98111 : Reach 98111 := rs (se 1 (by rfl) ⟨73583, by rfl⟩) R147167
theorem R491345 : Reach 491345 := rs (se 2 (by rfl) ⟨184254, by rfl⟩) R368509
theorem R65371 : Reach 65371 := rs (se 1 (by rfl) ⟨49028, by rfl⟩) R98057
theorem R98159 : Reach 98159 := rs (se 1 (by rfl) ⟨73619, by rfl⟩) R147239
theorem R196519 : Reach 196519 := rs (se 1 (by rfl) ⟨147389, by rfl⟩) R294779
theorem R98537 : Reach 98537 := rs (se 2 (by rfl) ⟨36951, by rfl⟩) R73903
theorem R98543 : Reach 98543 := rs (se 1 (by rfl) ⟨73907, by rfl⟩) R147815
theorem R229625 : Reach 229625 := rs (se 2 (by rfl) ⟨86109, by rfl⟩) R172219
theorem R65895 : Reach 65895 := rs (se 1 (by rfl) ⟨49421, by rfl⟩) R98843
theorem R426377 : Reach 426377 := rs (se 2 (by rfl) ⟨159891, by rfl⟩) R319783
theorem R66015 : Reach 66015 := rs (se 1 (by rfl) ⟨49511, by rfl⟩) R99023
theorem R66095 : Reach 66095 := rs (se 1 (by rfl) ⟨49571, by rfl⟩) R99143
theorem R66139 : Reach 66139 := rs (se 1 (by rfl) ⟨49604, by rfl⟩) R99209
theorem R66303 : Reach 66303 := rs (se 1 (by rfl) ⟨49727, by rfl⟩) R99455
theorem R66395 : Reach 66395 := rs (se 1 (by rfl) ⟨49796, by rfl⟩) R99593
theorem R164713 : Reach 164713 := rs (se 2 (by rfl) ⟨61767, by rfl⟩) R123535
theorem R66655 : Reach 66655 := rs (se 1 (by rfl) ⟨49991, by rfl⟩) R99983
theorem R99449 : Reach 99449 := rs (se 2 (by rfl) ⟨37293, by rfl⟩) R74587
theorem R66715 : Reach 66715 := rs (se 1 (by rfl) ⟨50036, by rfl⟩) R100073
theorem R66719 : Reach 66719 := rs (se 1 (by rfl) ⟨50039, by rfl⟩) R100079
theorem R99497 : Reach 99497 := rs (se 2 (by rfl) ⟨37311, by rfl⟩) R74623
theorem R66887 : Reach 66887 := rs (se 1 (by rfl) ⟨50165, by rfl⟩) R100331
theorem R67055 : Reach 67055 := rs (se 1 (by rfl) ⟨50291, by rfl⟩) R100583
theorem R67071 : Reach 67071 := rs (se 1 (by rfl) ⟨50303, by rfl⟩) R100607
theorem R99881 : Reach 99881 := rs (se 2 (by rfl) ⟨37455, by rfl⟩) R74911
theorem R493289 : Reach 493289 := rs (se 2 (by rfl) ⟨184983, by rfl⟩) R369967
theorem R952067 : Reach 952067 := rs (se 1 (by rfl) ⟨714050, by rfl⟩) R1428101
theorem R100187 : Reach 100187 := rs (se 1 (by rfl) ⟨75140, by rfl⟩) R150281
theorem R10192877 : Reach 10192877 := rs (se 3 (by rfl) ⟨1911164, by rfl⟩) R3822329
theorem R100463 : Reach 100463 := rs (se 1 (by rfl) ⟨75347, by rfl⟩) R150695
theorem R100535 : Reach 100535 := rs (se 1 (by rfl) ⟨75401, by rfl⟩) R150803
theorem R559325 : Reach 559325 := rs (se 3 (by rfl) ⟨104873, by rfl⟩) R209747
theorem R166151 : Reach 166151 := rs (se 1 (by rfl) ⟨124613, by rfl⟩) R249227
theorem R68207 : Reach 68207 := rs (se 1 (by rfl) ⟨51155, by rfl⟩) R102311
theorem R724625 : Reach 724625 := rs (se 2 (by rfl) ⟨271734, by rfl⟩) R543469
theorem R167791 : Reach 167791 := rs (se 1 (by rfl) ⟨125843, by rfl⟩) R251687
theorem R954935 : Reach 954935 := rs (se 1 (by rfl) ⟨716201, by rfl⟩) R1432403
theorem R333395 : Reach 333395 := rs (se 1 (by rfl) ⟨250046, by rfl⟩) R500093
theorem R104105 : Reach 104105 := rs (se 2 (by rfl) ⟨39039, by rfl⟩) R78079
theorem R136927 : Reach 136927 := rs (se 1 (by rfl) ⟨102695, by rfl⟩) R205391
theorem R3708787 : Reach 3708787 := rs (se 1 (by rfl) ⟨2781590, by rfl⟩) R5563181
theorem R203111 : Reach 203111 := rs (se 1 (by rfl) ⟨152333, by rfl⟩) R304667
theorem R72175 : Reach 72175 := rs (se 1 (by rfl) ⟨54131, by rfl⟩) R108263
theorem R432641 : Reach 432641 := rs (se 2 (by rfl) ⟨162240, by rfl⟩) R324481
theorem R17406515 : Reach 17406515 := rs (se 1 (by rfl) ⟨13054886, by rfl⟩) R26109773
theorem R498919 : Reach 498919 := rs (se 1 (by rfl) ⟨374189, by rfl⟩) R748379
theorem R106409 : Reach 106409 := rs (se 2 (by rfl) ⟨39903, by rfl⟩) R79807
theorem R237811 : Reach 237811 := rs (se 1 (by rfl) ⟨178358, by rfl⟩) R356717
theorem R369035 : Reach 369035 := rs (se 1 (by rfl) ⟨276776, by rfl⟩) R553553
theorem R369107 : Reach 369107 := rs (se 1 (by rfl) ⟨276830, by rfl⟩) R553661
theorem R140071 : Reach 140071 := rs (se 1 (by rfl) ⟨105053, by rfl⟩) R210107
theorem R13935563 : Reach 13935563 := rs (se 1 (by rfl) ⟨10451672, by rfl⟩) R20903345
theorem R336959 : Reach 336959 := rs (se 1 (by rfl) ⟨252719, by rfl⟩) R505439
theorem R205907 : Reach 205907 := rs (se 1 (by rfl) ⟨154430, by rfl⟩) R308861
theorem R894731 : Reach 894731 := rs (se 1 (by rfl) ⟨671048, by rfl⟩) R1342097
theorem R108607 : Reach 108607 := rs (se 1 (by rfl) ⟨81455, by rfl⟩) R162911
theorem R239719 : Reach 239719 := rs (se 1 (by rfl) ⟨179789, by rfl⟩) R359579
theorem R338579 : Reach 338579 := rs (se 1 (by rfl) ⟨253934, by rfl⟩) R507869
theorem R142121 : Reach 142121 := rs (se 2 (by rfl) ⟨53295, by rfl⟩) R106591
theorem R1093499 : Reach 1093499 := rs (se 1 (by rfl) ⟨820124, by rfl⟩) R1640249
theorem R208927 : Reach 208927 := rs (se 1 (by rfl) ⟨156695, by rfl⟩) R313391
theorem R110875 : Reach 110875 := rs (se 1 (by rfl) ⟨83156, by rfl⟩) R166313
theorem R143657 : Reach 143657 := rs (se 2 (by rfl) ⟨53871, by rfl⟩) R107743
theorem R111017 : Reach 111017 := rs (se 2 (by rfl) ⟨41631, by rfl⟩) R83263
theorem R111071 : Reach 111071 := rs (se 1 (by rfl) ⟨83303, by rfl⟩) R166607
theorem R1258021 : Reach 1258021 := rs (se 4 (by rfl) ⟨117939, by rfl⟩) R235879
theorem R504467 : Reach 504467 := rs (se 1 (by rfl) ⟨378350, by rfl⟩) R756701
theorem R210043 : Reach 210043 := rs (se 1 (by rfl) ⟨157532, by rfl⟩) R315065
theorem R341495 : Reach 341495 := rs (se 1 (by rfl) ⟨256121, by rfl⟩) R512243
theorem R112475 : Reach 112475 := rs (se 1 (by rfl) ⟨84356, by rfl⟩) R168713
theorem R145295 : Reach 145295 := rs (se 1 (by rfl) ⟨108971, by rfl⟩) R217943
theorem R145385 : Reach 145385 := rs (se 2 (by rfl) ⟨54519, by rfl⟩) R109039
theorem R146015 : Reach 146015 := rs (se 1 (by rfl) ⟨109511, by rfl⟩) R219023
theorem R638239 : Reach 638239 := rs (se 1 (by rfl) ⟨478679, by rfl⟩) R957359
theorem R408887 : Reach 408887 := rs (se 1 (by rfl) ⟨306665, by rfl⟩) R613331
theorem R147599 : Reach 147599 := rs (se 1 (by rfl) ⟨110699, by rfl⟩) R221399
theorem R901307 : Reach 901307 := rs (se 1 (by rfl) ⟨675980, by rfl⟩) R1351961
theorem R147707 : Reach 147707 := rs (se 1 (by rfl) ⟨110780, by rfl⟩) R221561
theorem R147995 : Reach 147995 := rs (se 1 (by rfl) ⟨110996, by rfl⟩) R221993
theorem R246523 : Reach 246523 := rs (se 1 (by rfl) ⟨184892, by rfl⟩) R369785
theorem R115519 : Reach 115519 := rs (se 1 (by rfl) ⟨86639, by rfl⟩) R173279
theorem R967625 : Reach 967625 := rs (se 2 (by rfl) ⟨362859, by rfl⟩) R725719
theorem R8864731 : Reach 8864731 := rs (se 1 (by rfl) ⟨6648548, by rfl⟩) R13297097
theorem R82927 : Reach 82927 := rs (se 1 (by rfl) ⟨62195, by rfl⟩) R124391
theorem R148553 : Reach 148553 := rs (se 2 (by rfl) ⟨55707, by rfl⟩) R111415
theorem R182159 : Reach 182159 := rs (se 1 (by rfl) ⟨136619, by rfl⟩) R273239
theorem R247799 : Reach 247799 := rs (se 1 (by rfl) ⟨185849, by rfl⟩) R371699
theorem R2672891 : Reach 2672891 := rs (se 1 (by rfl) ⟨2004668, by rfl⟩) R4009337
theorem R117227 : Reach 117227 := rs (se 1 (by rfl) ⟨87920, by rfl⟩) R175841
theorem R445123 : Reach 445123 := rs (se 1 (by rfl) ⟨333842, by rfl⟩) R667685
theorem R3459833 : Reach 3459833 := rs (se 2 (by rfl) ⟨1297437, by rfl⟩) R2594875
theorem R215945 : Reach 215945 := rs (se 2 (by rfl) ⟨80979, by rfl⟩) R161959
theorem R150569 : Reach 150569 := rs (se 2 (by rfl) ⟨56463, by rfl⟩) R112927
theorem R150857 : Reach 150857 := rs (se 2 (by rfl) ⟨56571, by rfl⟩) R113143
theorem R544427 : Reach 544427 := rs (se 1 (by rfl) ⟨408320, by rfl⟩) R816641
theorem R216809 : Reach 216809 := rs (se 2 (by rfl) ⟨81303, by rfl⟩) R162607
theorem R115953443 : Reach 115953443 := rs (se 1 (by rfl) ⟨86965082, by rfl⟩) R173930165
theorem R217295 : Reach 217295 := rs (se 1 (by rfl) ⟨162971, by rfl⟩) R325943
theorem R217673 : Reach 217673 := rs (se 2 (by rfl) ⟨81627, by rfl⟩) R163255
theorem R217835 : Reach 217835 := rs (se 1 (by rfl) ⟨163376, by rfl⟩) R326753
theorem R1528895 : Reach 1528895 := rs (se 1 (by rfl) ⟨1146671, by rfl⟩) R2293343
theorem R481619 : Reach 481619 := rs (se 1 (by rfl) ⟨361214, by rfl⟩) R722429
theorem R252355 : Reach 252355 := rs (se 1 (by rfl) ⟨189266, by rfl⟩) R378533
theorem R186887 : Reach 186887 := rs (se 1 (by rfl) ⟨140165, by rfl⟩) R280331
theorem R7428631 : Reach 7428631 := rs (se 1 (by rfl) ⟨5571473, by rfl⟩) R11142947
theorem R482111 : Reach 482111 := rs (se 1 (by rfl) ⟨361583, by rfl⟩) R723167
theorem R252841 : Reach 252841 := rs (se 2 (by rfl) ⟨94815, by rfl⟩) R189631
theorem R580547 : Reach 580547 := rs (se 1 (by rfl) ⟨435410, by rfl⟩) R870821
theorem R220319 : Reach 220319 := rs (se 1 (by rfl) ⟨165239, by rfl⟩) R330479
theorem R253115 : Reach 253115 := rs (se 1 (by rfl) ⟨189836, by rfl⟩) R379673
theorem R155243 : Reach 155243 := rs (se 1 (by rfl) ⟨116432, by rfl⟩) R232865
theorem R2088629 : Reach 2088629 := rs (se 5 (by rfl) ⟨97904, by rfl⟩) R195809
theorem R222857 : Reach 222857 := rs (se 2 (by rfl) ⟨83571, by rfl⟩) R167143
theorem R550583 : Reach 550583 := rs (se 1 (by rfl) ⟨412937, by rfl⟩) R825875
theorem R222911 : Reach 222911 := rs (se 1 (by rfl) ⟨167183, by rfl⟩) R334367
theorem R157427 : Reach 157427 := rs (se 1 (by rfl) ⟨118070, by rfl⟩) R236141
theorem R9038141 : Reach 9038141 := rs (se 3 (by rfl) ⟨1694651, by rfl⟩) R3389303
theorem R93415 : Reach 93415 := rs (se 1 (by rfl) ⟨70061, by rfl⟩) R140123
theorem R126299 : Reach 126299 := rs (se 1 (by rfl) ⟨94724, by rfl⟩) R189449
theorem R93631 : Reach 93631 := rs (se 1 (by rfl) ⟨70223, by rfl⟩) R140447
theorem R486971 : Reach 486971 := rs (se 1 (by rfl) ⟨365228, by rfl⟩) R730457
theorem R1207943 : Reach 1207943 := rs (se 1 (by rfl) ⟨905957, by rfl⟩) R1811915
theorem R553175 : Reach 553175 := rs (se 1 (by rfl) ⟨414881, by rfl⟩) R829763
theorem R94775 : Reach 94775 := rs (se 1 (by rfl) ⟨71081, by rfl⟩) R142163
theorem R94889 : Reach 94889 := rs (se 2 (by rfl) ⟨35583, by rfl⟩) R71167
theorem R95015 : Reach 95015 := rs (se 1 (by rfl) ⟨71261, by rfl⟩) R142523
theorem R95135 : Reach 95135 := rs (se 1 (by rfl) ⟨71351, by rfl⟩) R142703
theorem R619649 : Reach 619649 := rs (se 2 (by rfl) ⟨232368, by rfl⟩) R464737
theorem R1406105 : Reach 1406105 := rs (se 2 (by rfl) ⟨527289, by rfl⟩) R1054579
theorem R324971 : Reach 324971 := rs (se 1 (by rfl) ⟨243728, by rfl⟩) R487457
theorem R95615 : Reach 95615 := rs (se 1 (by rfl) ⟨71711, by rfl⟩) R143423
theorem R161423 : Reach 161423 := rs (se 1 (by rfl) ⟨121067, by rfl⟩) R242135
theorem R63335 : Reach 63335 := rs (se 1 (by rfl) ⟨47501, by rfl⟩) R95003
theorem R358319 : Reach 358319 := rs (se 1 (by rfl) ⟨268739, by rfl⟩) R537479
theorem R325619 : Reach 325619 := rs (se 1 (by rfl) ⟨244214, by rfl⟩) R488429
theorem R63519 : Reach 63519 := rs (se 1 (by rfl) ⟨47639, by rfl⟩) R95279
theorem R63551 : Reach 63551 := rs (se 1 (by rfl) ⟨47663, by rfl⟩) R95327
theorem R63591 : Reach 63591 := rs (se 1 (by rfl) ⟨47693, by rfl⟩) R95387
theorem R63599 : Reach 63599 := rs (se 1 (by rfl) ⟨47699, by rfl⟩) R95399
theorem R96425 : Reach 96425 := rs (se 2 (by rfl) ⟨36159, by rfl⟩) R72319
theorem R64047 : Reach 64047 := rs (se 1 (by rfl) ⟨48035, by rfl⟩) R96071
theorem R64167 : Reach 64167 := rs (se 1 (by rfl) ⟨48125, by rfl⟩) R96251
theorem R64207 : Reach 64207 := rs (se 1 (by rfl) ⟨48155, by rfl⟩) R96311
theorem R97007 : Reach 97007 := rs (se 1 (by rfl) ⟨72755, by rfl⟩) R145511
theorem R64251 : Reach 64251 := rs (se 1 (by rfl) ⟨48188, by rfl⟩) R96377
theorem R64287 : Reach 64287 := rs (se 1 (by rfl) ⟨48215, by rfl⟩) R96431
theorem R64447 : Reach 64447 := rs (se 1 (by rfl) ⟨48335, by rfl⟩) R96671
theorem R64507 : Reach 64507 := rs (se 1 (by rfl) ⟨48380, by rfl⟩) R96761
theorem R64831 : Reach 64831 := rs (se 1 (by rfl) ⟨48623, by rfl⟩) R97247
theorem R64871 : Reach 64871 := rs (se 1 (by rfl) ⟨48653, by rfl⟩) R97307
theorem R65127 : Reach 65127 := rs (se 1 (by rfl) ⟨48845, by rfl⟩) R97691
theorem R65179 : Reach 65179 := rs (se 1 (by rfl) ⟨48884, by rfl⟩) R97769
theorem R65183 : Reach 65183 := rs (se 1 (by rfl) ⟨48887, by rfl⟩) R97775
theorem R65275 : Reach 65275 := rs (se 1 (by rfl) ⟨48956, by rfl⟩) R97913
theorem R65407 : Reach 65407 := rs (se 1 (by rfl) ⟨49055, by rfl⟩) R98111
theorem R262025 : Reach 262025 := rs (se 2 (by rfl) ⟨98259, by rfl⟩) R196519
theorem R327563 : Reach 327563 := rs (se 1 (by rfl) ⟨245672, by rfl⟩) R491345
theorem R622475 : Reach 622475 := rs (se 1 (by rfl) ⟨466856, by rfl⟩) R933713
theorem R65439 : Reach 65439 := rs (se 1 (by rfl) ⟨49079, by rfl⟩) R98159
theorem R622525 : Reach 622525 := rs (se 3 (by rfl) ⟨116723, by rfl⟩) R233447
theorem R98297 : Reach 98297 := rs (se 2 (by rfl) ⟨36861, by rfl⟩) R73723
theorem R98399 : Reach 98399 := rs (se 1 (by rfl) ⟨73799, by rfl⟩) R147599
theorem R65691 : Reach 65691 := rs (se 1 (by rfl) ⟨49268, by rfl⟩) R98537
theorem R65695 : Reach 65695 := rs (se 1 (by rfl) ⟨49271, by rfl⟩) R98543
theorem R98471 : Reach 98471 := rs (se 1 (by rfl) ⟨73853, by rfl⟩) R147707
theorem R98663 : Reach 98663 := rs (se 1 (by rfl) ⟨73997, by rfl⟩) R147995
theorem R99035 : Reach 99035 := rs (se 1 (by rfl) ⟨74276, by rfl⟩) R148553
theorem R66299 : Reach 66299 := rs (se 1 (by rfl) ⟨49724, by rfl⟩) R99449
theorem R66331 : Reach 66331 := rs (se 1 (by rfl) ⟨49748, by rfl⟩) R99497
theorem R2196341 : Reach 2196341 := rs (se 5 (by rfl) ⟨102953, by rfl⟩) R205907
theorem R328697 : Reach 328697 := rs (se 2 (by rfl) ⟨123261, by rfl⟩) R246523
theorem R66587 : Reach 66587 := rs (se 1 (by rfl) ⟨49940, by rfl⟩) R99881
theorem R328859 : Reach 328859 := rs (se 1 (by rfl) ⟨246644, by rfl⟩) R493289
theorem R66791 : Reach 66791 := rs (se 1 (by rfl) ⟨50093, by rfl⟩) R100187
theorem R165199 : Reach 165199 := rs (se 1 (by rfl) ⟨123899, by rfl⟩) R247799
theorem R66975 : Reach 66975 := rs (se 1 (by rfl) ⟨50231, by rfl⟩) R100463
theorem R67023 : Reach 67023 := rs (se 1 (by rfl) ⟨50267, by rfl⟩) R100535
theorem R100379 : Reach 100379 := rs (se 1 (by rfl) ⟨75284, by rfl⟩) R150569
theorem R100571 : Reach 100571 := rs (se 1 (by rfl) ⟨75428, by rfl⟩) R150857
theorem R362951 : Reach 362951 := rs (se 1 (by rfl) ⟨272213, by rfl⟩) R544427
theorem R77302295 : Reach 77302295 := rs (se 1 (by rfl) ⟨57976721, by rfl⟩) R115953443
theorem R1019263 : Reach 1019263 := rs (se 1 (by rfl) ⟨764447, by rfl⟩) R1528895
theorem R593497 : Reach 593497 := rs (se 2 (by rfl) ⟨222561, by rfl⟩) R445123
theorem R135407 : Reach 135407 := rs (se 1 (by rfl) ⟨101555, by rfl⟩) R203111
theorem R11604343 : Reach 11604343 := rs (se 1 (by rfl) ⟨8703257, by rfl⟩) R17406515
theorem R168743 : Reach 168743 := rs (se 1 (by rfl) ⟨126557, by rfl⟩) R253115
theorem R70939 : Reach 70939 := rs (se 1 (by rfl) ⟨53204, by rfl⟩) R106409
theorem R1677361 : Reach 1677361 := rs (se 2 (by rfl) ⟨629010, by rfl⟩) R1258021
theorem R367055 : Reach 367055 := rs (se 1 (by rfl) ⟨275291, by rfl⟩) R550583
theorem R727541 : Reach 727541 := rs (se 5 (by rfl) ⟨34103, by rfl⟩) R68207
theorem R104951 : Reach 104951 := rs (se 1 (by rfl) ⟨78713, by rfl⟩) R157427
theorem R728999 : Reach 728999 := rs (se 1 (by rfl) ⟨546749, by rfl⟩) R1093499
theorem R368783 : Reach 368783 := rs (se 1 (by rfl) ⟨276587, by rfl⟩) R553175
theorem R74011 : Reach 74011 := rs (se 1 (by rfl) ⟨55508, by rfl⟩) R111017
theorem R74047 : Reach 74047 := rs (se 1 (by rfl) ⟨55535, by rfl⟩) R111071
theorem R336311 : Reach 336311 := rs (se 1 (by rfl) ⟨252233, by rfl⟩) R504467
theorem R336473 : Reach 336473 := rs (se 2 (by rfl) ⟨126177, by rfl⟩) R252355
theorem R9904841 : Reach 9904841 := rs (se 2 (by rfl) ⟨3714315, by rfl⟩) R7428631
theorem R336797 : Reach 336797 := rs (se 3 (by rfl) ⟨63149, by rfl⟩) R126299
theorem R107615 : Reach 107615 := rs (se 1 (by rfl) ⟨80711, by rfl⟩) R161423
theorem R337121 : Reach 337121 := rs (se 2 (by rfl) ⟨126420, by rfl⟩) R252841
theorem R74983 : Reach 74983 := rs (se 1 (by rfl) ⟨56237, by rfl⟩) R112475
theorem R238879 : Reach 238879 := rs (se 1 (by rfl) ⟨179159, by rfl⟩) R358319
theorem R665225 : Reach 665225 := rs (se 2 (by rfl) ⟨249459, by rfl⟩) R498919
theorem R272591 : Reach 272591 := rs (se 1 (by rfl) ⟨204443, by rfl⟩) R408887
theorem R830033 : Reach 830033 := rs (se 2 (by rfl) ⟨311262, by rfl⟩) R622525
theorem R174683 : Reach 174683 := rs (se 1 (by rfl) ⟨131012, by rfl⟩) R262025
theorem R600871 : Reach 600871 := rs (se 1 (by rfl) ⟨450653, by rfl⟩) R901307
theorem R634711 : Reach 634711 := rs (se 1 (by rfl) ⟨476033, by rfl⟩) R952067
theorem R110569 : Reach 110569 := rs (se 2 (by rfl) ⟨41463, by rfl⟩) R82927
theorem R6795251 : Reach 6795251 := rs (se 1 (by rfl) ⟨5096438, by rfl⟩) R10192877
theorem R372883 : Reach 372883 := rs (se 1 (by rfl) ⟨279662, by rfl⟩) R559325
theorem R1781927 : Reach 1781927 := rs (se 1 (by rfl) ⟨1336445, by rfl⟩) R2672891
theorem R110767 : Reach 110767 := rs (se 1 (by rfl) ⟨83075, by rfl⟩) R166151
theorem R2306555 : Reach 2306555 := rs (se 1 (by rfl) ⟨1729916, by rfl⟩) R3459833
theorem R143963 : Reach 143963 := rs (se 1 (by rfl) ⟨107972, by rfl⟩) R215945
theorem R144539 : Reach 144539 := rs (se 1 (by rfl) ⟨108404, by rfl⟩) R216809
theorem R144809 : Reach 144809 := rs (se 2 (by rfl) ⟨54303, by rfl⟩) R108607
theorem R144863 : Reach 144863 := rs (se 1 (by rfl) ⟨108647, by rfl⟩) R217295
theorem R636623 : Reach 636623 := rs (se 1 (by rfl) ⟨477467, by rfl⟩) R954935
theorem R145115 : Reach 145115 := rs (se 1 (by rfl) ⟨108836, by rfl⟩) R217673
theorem R145223 : Reach 145223 := rs (se 1 (by rfl) ⟨108917, by rfl⟩) R217835
theorem R277613 : Reach 277613 := rs (se 3 (by rfl) ⟨52052, by rfl⟩) R104105
theorem R146879 : Reach 146879 := rs (se 1 (by rfl) ⟨110159, by rfl⟩) R220319
theorem R1392419 : Reach 1392419 := rs (se 1 (by rfl) ⟨1044314, by rfl⟩) R2088629
theorem R278569 : Reach 278569 := rs (se 2 (by rfl) ⟨104463, by rfl⟩) R208927
theorem R246023 : Reach 246023 := rs (se 1 (by rfl) ⟨184517, by rfl⟩) R369035
theorem R246071 : Reach 246071 := rs (se 1 (by rfl) ⟨184553, by rfl⟩) R369107
theorem R147833 : Reach 147833 := rs (se 2 (by rfl) ⟨55437, by rfl⟩) R110875
theorem R9290375 : Reach 9290375 := rs (se 1 (by rfl) ⟨6967781, by rfl⟩) R13935563
theorem R148571 : Reach 148571 := rs (se 1 (by rfl) ⟨111428, by rfl⟩) R222857
theorem R148607 : Reach 148607 := rs (se 1 (by rfl) ⟨111455, by rfl⟩) R222911
theorem R312605 : Reach 312605 := rs (se 3 (by rfl) ⟨58613, by rfl⟩) R117227
theorem R280057 : Reach 280057 := rs (se 2 (by rfl) ⟨105021, by rfl⟩) R210043
theorem R378989 : Reach 378989 := rs (se 3 (by rfl) ⟨71060, by rfl⟩) R142121
theorem R182569 : Reach 182569 := rs (se 2 (by rfl) ⟨68463, by rfl⟩) R136927
theorem R805295 : Reach 805295 := rs (se 1 (by rfl) ⟨603971, by rfl⟩) R1207943
theorem R413099 : Reach 413099 := rs (se 1 (by rfl) ⟨309824, by rfl⟩) R619649
theorem R937403 : Reach 937403 := rs (se 1 (by rfl) ⟨703052, by rfl⟩) R1406105
theorem R216647 : Reach 216647 := rs (se 1 (by rfl) ⟨162485, by rfl⟩) R324971
theorem R217079 : Reach 217079 := rs (se 1 (by rfl) ⟨162809, by rfl⟩) R325619
theorem R413981 : Reach 413981 := rs (se 3 (by rfl) ⟨77621, by rfl⟩) R155243
theorem R218375 : Reach 218375 := rs (se 1 (by rfl) ⟨163781, by rfl⟩) R327563
theorem R414983 : Reach 414983 := rs (se 1 (by rfl) ⟨311237, by rfl⟩) R622475
theorem R153083 : Reach 153083 := rs (se 1 (by rfl) ⟨114812, by rfl⟩) R229625
theorem R284251 : Reach 284251 := rs (se 1 (by rfl) ⟨213188, by rfl⟩) R426377
theorem R317081 : Reach 317081 := rs (se 2 (by rfl) ⟨118905, by rfl⟩) R237811
theorem R645083 : Reach 645083 := rs (se 1 (by rfl) ⟨483812, by rfl⟩) R967625
theorem R186761 : Reach 186761 := rs (se 2 (by rfl) ⟨70035, by rfl⟩) R140071
theorem R154025 : Reach 154025 := rs (se 2 (by rfl) ⟨57759, by rfl⟩) R115519
theorem R219617 : Reach 219617 := rs (se 2 (by rfl) ⟨82356, by rfl⟩) R164713
theorem R121439 : Reach 121439 := rs (se 1 (by rfl) ⟨91079, by rfl⟩) R182159
theorem R11819641 : Reach 11819641 := rs (se 2 (by rfl) ⟨4432365, by rfl⟩) R8864731
theorem R483083 : Reach 483083 := rs (se 1 (by rfl) ⟨362312, by rfl⟩) R724625
theorem R319625 : Reach 319625 := rs (se 2 (by rfl) ⟨119859, by rfl⟩) R239719
theorem R222263 : Reach 222263 := rs (se 1 (by rfl) ⟨166697, by rfl⟩) R333395
theorem R321079 : Reach 321079 := rs (se 1 (by rfl) ⟨240809, by rfl⟩) R481619
theorem R124553 : Reach 124553 := rs (se 2 (by rfl) ⟨46707, by rfl⟩) R93415
theorem R288427 : Reach 288427 := rs (se 1 (by rfl) ⟨216320, by rfl⟩) R432641
theorem R124591 : Reach 124591 := rs (se 1 (by rfl) ⟨93443, by rfl⟩) R186887
theorem R321407 : Reach 321407 := rs (se 1 (by rfl) ⟨241055, by rfl⟩) R482111
theorem R124841 : Reach 124841 := rs (se 2 (by rfl) ⟨46815, by rfl⟩) R93631
theorem R387031 : Reach 387031 := rs (se 1 (by rfl) ⟨290273, by rfl⟩) R580547
theorem R2385949 : Reach 2385949 := rs (se 3 (by rfl) ⟨447365, by rfl⟩) R894731
theorem R223721 : Reach 223721 := rs (se 2 (by rfl) ⟨83895, by rfl⟩) R167791
theorem R224639 : Reach 224639 := rs (se 1 (by rfl) ⟨168479, by rfl⟩) R336959
theorem R6025427 : Reach 6025427 := rs (se 1 (by rfl) ⟨4519070, by rfl⟩) R9038141
theorem R225719 : Reach 225719 := rs (se 1 (by rfl) ⟨169289, by rfl⟩) R338579
theorem R324647 : Reach 324647 := rs (se 1 (by rfl) ⟨243485, by rfl⟩) R486971
theorem R4945049 : Reach 4945049 := rs (se 2 (by rfl) ⟨1854393, by rfl⟩) R3708787
theorem R95771 : Reach 95771 := rs (se 1 (by rfl) ⟨71828, by rfl⟩) R143657
theorem R63183 : Reach 63183 := rs (se 1 (by rfl) ⟨47387, by rfl⟩) R94775
theorem R63259 : Reach 63259 := rs (se 1 (by rfl) ⟨47444, by rfl⟩) R94889
theorem R63343 : Reach 63343 := rs (se 1 (by rfl) ⟨47507, by rfl⟩) R95015
theorem R63423 : Reach 63423 := rs (se 1 (by rfl) ⟨47567, by rfl⟩) R95135
theorem R96233 : Reach 96233 := rs (se 2 (by rfl) ⟨36087, by rfl⟩) R72175
theorem R63743 : Reach 63743 := rs (se 1 (by rfl) ⟨47807, by rfl⟩) R95615
theorem R227663 : Reach 227663 := rs (se 1 (by rfl) ⟨170747, by rfl⟩) R341495
theorem R96863 : Reach 96863 := rs (se 1 (by rfl) ⟨72647, by rfl⟩) R145295
theorem R96923 : Reach 96923 := rs (se 1 (by rfl) ⟨72692, by rfl⟩) R145385
theorem R64283 : Reach 64283 := rs (se 1 (by rfl) ⟨48212, by rfl⟩) R96425
theorem R850985 : Reach 850985 := rs (se 2 (by rfl) ⟨319119, by rfl⟩) R638239
theorem R97343 : Reach 97343 := rs (se 1 (by rfl) ⟨73007, by rfl⟩) R146015
theorem R64671 : Reach 64671 := rs (se 1 (by rfl) ⟨48503, by rfl⟩) R97007
theorem R65531 : Reach 65531 := rs (se 1 (by rfl) ⟨49148, by rfl⟩) R98297
theorem R65599 : Reach 65599 := rs (se 1 (by rfl) ⟨49199, by rfl⟩) R98399
theorem R65647 : Reach 65647 := rs (se 1 (by rfl) ⟨49235, by rfl⟩) R98471
theorem R164015 : Reach 164015 := rs (se 1 (by rfl) ⟨123011, by rfl⟩) R246023
theorem R164047 : Reach 164047 := rs (se 1 (by rfl) ⟨123035, by rfl⟩) R246071
theorem R65775 : Reach 65775 := rs (se 1 (by rfl) ⟨49331, by rfl⟩) R98663
theorem R98555 : Reach 98555 := rs (se 1 (by rfl) ⟨73916, by rfl⟩) R147833
theorem R98681 : Reach 98681 := rs (se 2 (by rfl) ⟨37005, by rfl⟩) R74011
theorem R98729 : Reach 98729 := rs (se 2 (by rfl) ⟨37023, by rfl⟩) R74047
theorem R6193583 : Reach 6193583 := rs (se 1 (by rfl) ⟨4645187, by rfl⟩) R9290375
theorem R66023 : Reach 66023 := rs (se 1 (by rfl) ⟨49517, by rfl⟩) R99035
theorem R99047 : Reach 99047 := rs (se 1 (by rfl) ⟨74285, by rfl⟩) R148571
theorem R99071 : Reach 99071 := rs (se 1 (by rfl) ⟨74303, by rfl⟩) R148607
theorem R66919 : Reach 66919 := rs (se 1 (by rfl) ⟨50189, by rfl⟩) R100379
theorem R67047 : Reach 67047 := rs (se 1 (by rfl) ⟨50285, by rfl⟩) R100571
theorem R99977 : Reach 99977 := rs (se 2 (by rfl) ⟨37491, by rfl⟩) R74983
theorem R428105 : Reach 428105 := rs (se 2 (by rfl) ⟨160539, by rfl⟩) R321079
theorem R166121 : Reach 166121 := rs (se 2 (by rfl) ⟨62295, by rfl⟩) R124591
theorem R624935 : Reach 624935 := rs (se 1 (by rfl) ⟨468701, by rfl⟩) R937403
theorem R3181265 : Reach 3181265 := rs (se 2 (by rfl) ⟨1192974, by rfl⟩) R2385949
theorem R102055 : Reach 102055 := rs (se 1 (by rfl) ⟨76541, by rfl⟩) R153083
theorem R430055 : Reach 430055 := rs (se 1 (by rfl) ⟨322541, by rfl⟩) R645083
theorem R102683 : Reach 102683 := rs (se 1 (by rfl) ⟨77012, by rfl⟩) R154025
theorem R69967 : Reach 69967 := rs (se 1 (by rfl) ⟨52475, by rfl⟩) R104951
theorem R791329 : Reach 791329 := rs (se 2 (by rfl) ⟨296748, by rfl⟩) R593497
theorem R332909 : Reach 332909 := rs (se 3 (by rfl) ⟨62420, by rfl⟩) R124841
theorem R497177 : Reach 497177 := rs (se 2 (by rfl) ⟨186441, by rfl⟩) R372883
theorem R15472457 : Reach 15472457 := rs (se 2 (by rfl) ⟨5802171, by rfl⟩) R11604343
theorem R71743 : Reach 71743 := rs (se 1 (by rfl) ⟨53807, by rfl⟩) R107615
theorem R465821 : Reach 465821 := rs (se 3 (by rfl) ⟨87341, by rfl⟩) R174683
theorem R4530167 : Reach 4530167 := rs (se 1 (by rfl) ⟨3397625, by rfl⟩) R6795251
theorem R2236481 : Reach 2236481 := rs (se 2 (by rfl) ⟨838680, by rfl⟩) R1677361
theorem R1187951 : Reach 1187951 := rs (se 1 (by rfl) ⟨890963, by rfl⟩) R1781927
theorem R567323 : Reach 567323 := rs (se 1 (by rfl) ⟨425492, by rfl⟩) R850985
theorem R928279 : Reach 928279 := rs (se 1 (by rfl) ⟨696209, by rfl⟩) R1392419
theorem R371425 : Reach 371425 := rs (se 2 (by rfl) ⟨139284, by rfl⟩) R278569
theorem R208403 : Reach 208403 := rs (se 1 (by rfl) ⟨156302, by rfl⟩) R312605
theorem R536863 : Reach 536863 := rs (se 1 (by rfl) ⟨402647, by rfl⟩) R805295
theorem R241967 : Reach 241967 := rs (se 1 (by rfl) ⟨181475, by rfl⟩) R362951
theorem R373409 : Reach 373409 := rs (se 2 (by rfl) ⟨140028, by rfl⟩) R280057
theorem R275399 : Reach 275399 := rs (se 1 (by rfl) ⟨206549, by rfl⟩) R413099
theorem R144431 : Reach 144431 := rs (se 1 (by rfl) ⟨108323, by rfl⟩) R216647
theorem R144719 : Reach 144719 := rs (se 1 (by rfl) ⟨108539, by rfl⟩) R217079
theorem R275987 : Reach 275987 := rs (se 1 (by rfl) ⟨206990, by rfl⟩) R413981
theorem R243425 : Reach 243425 := rs (se 2 (by rfl) ⟨91284, by rfl⟩) R182569
theorem R112495 : Reach 112495 := rs (se 1 (by rfl) ⟨84371, by rfl⟩) R168743
theorem R145583 : Reach 145583 := rs (se 1 (by rfl) ⟨109187, by rfl⟩) R218375
theorem R801161 : Reach 801161 := rs (se 2 (by rfl) ⟨300435, by rfl⟩) R600871
theorem R244703 : Reach 244703 := rs (se 1 (by rfl) ⟨183527, by rfl⟩) R367055
theorem R146411 : Reach 146411 := rs (se 1 (by rfl) ⟨109808, by rfl⟩) R219617
theorem R1359017 : Reach 1359017 := rs (se 2 (by rfl) ⟨509631, by rfl⟩) R1019263
theorem R147425 : Reach 147425 := rs (se 2 (by rfl) ⟨55284, by rfl⟩) R110569
theorem R213083 : Reach 213083 := rs (se 1 (by rfl) ⟨159812, by rfl⟩) R319625
theorem R245855 : Reach 245855 := rs (se 1 (by rfl) ⟨184391, by rfl⟩) R368783
theorem R147689 : Reach 147689 := rs (se 2 (by rfl) ⟨55383, by rfl⟩) R110767
theorem R6603227 : Reach 6603227 := rs (se 1 (by rfl) ⟨4952420, by rfl⟩) R9904841
theorem R148175 : Reach 148175 := rs (se 1 (by rfl) ⟨111131, by rfl⟩) R222263
theorem R443483 : Reach 443483 := rs (se 1 (by rfl) ⟨332612, by rfl⟩) R665225
theorem R83035 : Reach 83035 := rs (se 1 (by rfl) ⟨62276, by rfl⟩) R124553
theorem R214271 : Reach 214271 := rs (se 1 (by rfl) ⟨160703, by rfl⟩) R321407
theorem R181727 : Reach 181727 := rs (se 1 (by rfl) ⟨136295, by rfl⟩) R272591
theorem R378341 : Reach 378341 := rs (se 4 (by rfl) ⟨35469, by rfl⟩) R70939
theorem R149147 : Reach 149147 := rs (se 1 (by rfl) ⟨111860, by rfl⟩) R223721
theorem R379001 : Reach 379001 := rs (se 2 (by rfl) ⟨142125, by rfl⟩) R284251
theorem R149759 : Reach 149759 := rs (se 1 (by rfl) ⟨112319, by rfl⟩) R224639
theorem R4016951 : Reach 4016951 := rs (se 1 (by rfl) ⟨3012713, by rfl⟩) R6025427
theorem R150479 : Reach 150479 := rs (se 1 (by rfl) ⟨112859, by rfl⟩) R225719
theorem R216431 : Reach 216431 := rs (se 1 (by rfl) ⟨162323, by rfl⟩) R324647
theorem R3296699 : Reach 3296699 := rs (se 1 (by rfl) ⟨2472524, by rfl⟩) R4945049
theorem R151775 : Reach 151775 := rs (se 1 (by rfl) ⟨113831, by rfl⟩) R227663
theorem R185075 : Reach 185075 := rs (se 1 (by rfl) ⟨138806, by rfl⟩) R277613
theorem R1464227 : Reach 1464227 := rs (se 1 (by rfl) ⟨1098170, by rfl⟩) R2196341
theorem R219131 : Reach 219131 := rs (se 1 (by rfl) ⟨164348, by rfl⟩) R328697
theorem R219239 : Reach 219239 := rs (se 1 (by rfl) ⟨164429, by rfl⟩) R328859
theorem R252659 : Reach 252659 := rs (se 1 (by rfl) ⟨189494, by rfl⟩) R378989
theorem R51534863 : Reach 51534863 := rs (se 1 (by rfl) ⟨38651147, by rfl⟩) R77302295
theorem R318505 : Reach 318505 := rs (se 2 (by rfl) ⟨119439, by rfl⟩) R238879
theorem R220265 : Reach 220265 := rs (se 2 (by rfl) ⟨82599, by rfl⟩) R165199
theorem R384569 : Reach 384569 := rs (se 2 (by rfl) ⟨144213, by rfl⟩) R288427
theorem R516041 : Reach 516041 := rs (se 2 (by rfl) ⟨193515, by rfl⟩) R387031
theorem R90271 : Reach 90271 := rs (se 1 (by rfl) ⟨67703, by rfl⟩) R135407
theorem R1106621 : Reach 1106621 := rs (se 3 (by rfl) ⟨207491, by rfl⟩) R414983
theorem R124507 : Reach 124507 := rs (se 1 (by rfl) ⟨93380, by rfl⟩) R186761
theorem R485027 : Reach 485027 := rs (se 1 (by rfl) ⟨363770, by rfl⟩) R727541
theorem R845549 : Reach 845549 := rs (se 3 (by rfl) ⟨158540, by rfl⟩) R317081
theorem R846281 : Reach 846281 := rs (se 2 (by rfl) ⟨317355, by rfl⟩) R634711
theorem R322055 : Reach 322055 := rs (se 1 (by rfl) ⟨241541, by rfl⟩) R483083
theorem R485999 : Reach 485999 := rs (se 1 (by rfl) ⟨364499, by rfl⟩) R728999
theorem R224207 : Reach 224207 := rs (se 1 (by rfl) ⟨168155, by rfl⟩) R336311
theorem R224315 : Reach 224315 := rs (se 1 (by rfl) ⟨168236, by rfl⟩) R336473
theorem R224531 : Reach 224531 := rs (se 1 (by rfl) ⟨168398, by rfl⟩) R336797
theorem R224747 : Reach 224747 := rs (se 1 (by rfl) ⟨168560, by rfl⟩) R337121
theorem R323837 : Reach 323837 := rs (se 3 (by rfl) ⟨60719, by rfl⟩) R121439
theorem R553355 : Reach 553355 := rs (se 1 (by rfl) ⟨415016, by rfl⟩) R830033
theorem R1537703 : Reach 1537703 := rs (se 1 (by rfl) ⟨1153277, by rfl⟩) R2306555
theorem R95975 : Reach 95975 := rs (se 1 (by rfl) ⟨71981, by rfl⟩) R143963
theorem R96359 : Reach 96359 := rs (se 1 (by rfl) ⟨72269, by rfl⟩) R144539
theorem R15759521 : Reach 15759521 := rs (se 2 (by rfl) ⟨5909820, by rfl⟩) R11819641
theorem R96539 : Reach 96539 := rs (se 1 (by rfl) ⟨72404, by rfl⟩) R144809
theorem R96575 : Reach 96575 := rs (se 1 (by rfl) ⟨72431, by rfl⟩) R144863
theorem R63847 : Reach 63847 := rs (se 1 (by rfl) ⟨47885, by rfl⟩) R95771
theorem R424415 : Reach 424415 := rs (se 1 (by rfl) ⟨318311, by rfl⟩) R636623
theorem R96743 : Reach 96743 := rs (se 1 (by rfl) ⟨72557, by rfl⟩) R145115
theorem R96815 : Reach 96815 := rs (se 1 (by rfl) ⟨72611, by rfl⟩) R145223
theorem R64155 : Reach 64155 := rs (se 1 (by rfl) ⟨48116, by rfl⟩) R96233
theorem R64575 : Reach 64575 := rs (se 1 (by rfl) ⟨48431, by rfl⟩) R96863
theorem R64615 : Reach 64615 := rs (se 1 (by rfl) ⟨48461, by rfl⟩) R96923
theorem R64895 : Reach 64895 := rs (se 1 (by rfl) ⟨48671, by rfl⟩) R97343
theorem R97919 : Reach 97919 := rs (se 1 (by rfl) ⟨73439, by rfl⟩) R146879
theorem R163903 : Reach 163903 := rs (se 1 (by rfl) ⟨122927, by rfl⟩) R245855
theorem R98459 : Reach 98459 := rs (se 1 (by rfl) ⟨73844, by rfl⟩) R147689
theorem R65703 : Reach 65703 := rs (se 1 (by rfl) ⟨49277, by rfl⟩) R98555
theorem R65787 : Reach 65787 := rs (se 1 (by rfl) ⟨49340, by rfl⟩) R98681
theorem R65819 : Reach 65819 := rs (se 1 (by rfl) ⟨49364, by rfl⟩) R98729
theorem R4129055 : Reach 4129055 := rs (se 1 (by rfl) ⟨3096791, by rfl⟩) R6193583
theorem R98783 : Reach 98783 := rs (se 1 (by rfl) ⟨74087, by rfl⟩) R148175
theorem R66031 : Reach 66031 := rs (se 1 (by rfl) ⟨49523, by rfl⟩) R99047
theorem R66047 : Reach 66047 := rs (se 1 (by rfl) ⟨49535, by rfl⟩) R99071
theorem R295655 : Reach 295655 := rs (se 1 (by rfl) ⟨221741, by rfl⟩) R443483
theorem R66651 : Reach 66651 := rs (se 1 (by rfl) ⟨49988, by rfl⟩) R99977
theorem R99431 : Reach 99431 := rs (se 1 (by rfl) ⟨74573, by rfl⟩) R149147
theorem R99839 : Reach 99839 := rs (se 1 (by rfl) ⟨74879, by rfl⟩) R149759
theorem R100319 : Reach 100319 := rs (se 1 (by rfl) ⟨75239, by rfl⟩) R150479
theorem R166009 : Reach 166009 := rs (se 2 (by rfl) ⟨62253, by rfl⟩) R124507
theorem R2197799 : Reach 2197799 := rs (se 1 (by rfl) ⟨1648349, by rfl⟩) R3296699
theorem R4950821 : Reach 4950821 := rs (se 4 (by rfl) ⟨464139, by rfl⟩) R928279
theorem R101183 : Reach 101183 := rs (se 1 (by rfl) ⟨75887, by rfl⟩) R151775
theorem R68455 : Reach 68455 := rs (se 1 (by rfl) ⟨51341, by rfl⟩) R102683
theorem R495233 : Reach 495233 := rs (se 2 (by rfl) ⟨185712, by rfl⟩) R371425
theorem R331451 : Reach 331451 := rs (se 1 (by rfl) ⟨248588, by rfl⟩) R497177
theorem R168439 : Reach 168439 := rs (se 1 (by rfl) ⟨126329, by rfl⟩) R252659
theorem R136073 : Reach 136073 := rs (se 2 (by rfl) ⟨51027, by rfl⟩) R102055
theorem R3020111 : Reach 3020111 := rs (se 1 (by rfl) ⟨2265083, by rfl⟩) R4530167
theorem R1055105 : Reach 1055105 := rs (se 2 (by rfl) ⟨395664, by rfl⟩) R791329
theorem R563699 : Reach 563699 := rs (se 1 (by rfl) ⟨422774, by rfl⟩) R845549
theorem R564187 : Reach 564187 := rs (se 1 (by rfl) ⟨423140, by rfl⟩) R846281
theorem R138935 : Reach 138935 := rs (se 1 (by rfl) ⟨104201, by rfl⟩) R208403
theorem R368903 : Reach 368903 := rs (se 1 (by rfl) ⟨276677, by rfl⟩) R553355
theorem R1025135 : Reach 1025135 := rs (se 1 (by rfl) ⟨768851, by rfl⟩) R1537703
theorem R534107 : Reach 534107 := rs (se 1 (by rfl) ⟨400580, by rfl⟩) R801161
theorem R142055 : Reach 142055 := rs (se 1 (by rfl) ⟨106541, by rfl⟩) R213083
theorem R109343 : Reach 109343 := rs (se 1 (by rfl) ⟨82007, by rfl⟩) R164015
theorem R4402151 : Reach 4402151 := rs (se 1 (by rfl) ⟨3301613, by rfl⟩) R6603227
theorem R142847 : Reach 142847 := rs (se 1 (by rfl) ⟨107135, by rfl⟩) R214271
theorem R110713 : Reach 110713 := rs (se 2 (by rfl) ⟨41517, by rfl⟩) R83035
theorem R110747 : Reach 110747 := rs (se 1 (by rfl) ⟨83060, by rfl⟩) R166121
theorem R373157 : Reach 373157 := rs (se 4 (by rfl) ⟨34983, by rfl⟩) R69967
theorem R144287 : Reach 144287 := rs (se 1 (by rfl) ⟨108215, by rfl⟩) R216431
theorem R146087 : Reach 146087 := rs (se 1 (by rfl) ⟨109565, by rfl⟩) R219131
theorem R146159 : Reach 146159 := rs (se 1 (by rfl) ⟨109619, by rfl⟩) R219239
theorem R310547 : Reach 310547 := rs (se 1 (by rfl) ⟨232910, by rfl⟩) R465821
theorem R34356575 : Reach 34356575 := rs (se 1 (by rfl) ⟨25767431, by rfl⟩) R51534863
theorem R146843 : Reach 146843 := rs (se 1 (by rfl) ⟨110132, by rfl⟩) R220265
theorem R344027 : Reach 344027 := rs (se 1 (by rfl) ⟨258020, by rfl⟩) R516041
theorem R1490987 : Reach 1490987 := rs (se 1 (by rfl) ⟨1118240, by rfl⟩) R2236481
theorem R737747 : Reach 737747 := rs (se 1 (by rfl) ⟨553310, by rfl⟩) R1106621
theorem R378215 : Reach 378215 := rs (se 1 (by rfl) ⟨283661, by rfl⟩) R567323
theorem R214703 : Reach 214703 := rs (se 1 (by rfl) ⟨161027, by rfl⟩) R322055
theorem R149471 : Reach 149471 := rs (se 1 (by rfl) ⟨112103, by rfl⟩) R224207
theorem R149543 : Reach 149543 := rs (se 1 (by rfl) ⟨112157, by rfl⟩) R224315
theorem R149687 : Reach 149687 := rs (se 1 (by rfl) ⟨112265, by rfl⟩) R224531
theorem R149831 : Reach 149831 := rs (se 1 (by rfl) ⟨112373, by rfl⟩) R224747
theorem R149993 : Reach 149993 := rs (se 2 (by rfl) ⟨56247, by rfl⟩) R112495
theorem R215891 : Reach 215891 := rs (se 1 (by rfl) ⟨161918, by rfl⟩) R323837
theorem R248939 : Reach 248939 := rs (se 1 (by rfl) ⟨186704, by rfl⟩) R373409
theorem R183599 : Reach 183599 := rs (se 1 (by rfl) ⟨137699, by rfl⟩) R275399
theorem R183991 : Reach 183991 := rs (se 1 (by rfl) ⟨137993, by rfl⟩) R275987
theorem R10506347 : Reach 10506347 := rs (se 1 (by rfl) ⟨7879760, by rfl⟩) R15759521
theorem R282943 : Reach 282943 := rs (se 1 (by rfl) ⟨212207, by rfl⟩) R424415
theorem R906011 : Reach 906011 := rs (se 1 (by rfl) ⟨679508, by rfl⟩) R1359017
theorem R120361 : Reach 120361 := rs (se 2 (by rfl) ⟨45135, by rfl⟩) R90271
theorem R218729 : Reach 218729 := rs (se 2 (by rfl) ⟨82023, by rfl⟩) R164047
theorem R121151 : Reach 121151 := rs (se 1 (by rfl) ⟨90863, by rfl⟩) R181727
theorem R252227 : Reach 252227 := rs (se 1 (by rfl) ⟨189170, by rfl⟩) R378341
theorem R12671477 : Reach 12671477 := rs (se 5 (by rfl) ⟨593975, by rfl⟩) R1187951
theorem R252667 : Reach 252667 := rs (se 1 (by rfl) ⟨189500, by rfl⟩) R379001
theorem R2120843 : Reach 2120843 := rs (se 1 (by rfl) ⟨1590632, by rfl⟩) R3181265
theorem R2677967 : Reach 2677967 := rs (se 1 (by rfl) ⟨2008475, by rfl⟩) R4016951
theorem R286703 : Reach 286703 := rs (se 1 (by rfl) ⟨215027, by rfl⟩) R430055
theorem R123383 : Reach 123383 := rs (se 1 (by rfl) ⟨92537, by rfl⟩) R185075
theorem R221939 : Reach 221939 := rs (se 1 (by rfl) ⟨166454, by rfl⟩) R332909
theorem R10314971 : Reach 10314971 := rs (se 1 (by rfl) ⟨7736228, by rfl⟩) R15472457
theorem R976151 : Reach 976151 := rs (se 1 (by rfl) ⟨732113, by rfl⟩) R1464227
theorem R256379 : Reach 256379 := rs (se 1 (by rfl) ⟨192284, by rfl⟩) R384569
theorem R1141613 : Reach 1141613 := rs (se 3 (by rfl) ⟨214052, by rfl⟩) R428105
theorem R715817 : Reach 715817 := rs (se 2 (by rfl) ⟨268431, by rfl⟩) R536863
theorem R1666493 : Reach 1666493 := rs (se 3 (by rfl) ⟨312467, by rfl⟩) R624935
theorem R323351 : Reach 323351 := rs (se 1 (by rfl) ⟨242513, by rfl⟩) R485027
theorem R323999 : Reach 323999 := rs (se 1 (by rfl) ⟨242999, by rfl⟩) R485999
theorem R95657 : Reach 95657 := rs (se 2 (by rfl) ⟨35871, by rfl⟩) R71743
theorem R161311 : Reach 161311 := rs (se 1 (by rfl) ⟨120983, by rfl⟩) R241967
theorem R96287 : Reach 96287 := rs (se 1 (by rfl) ⟨72215, by rfl⟩) R144431
theorem R96479 : Reach 96479 := rs (se 1 (by rfl) ⟨72359, by rfl⟩) R144719
theorem R162283 : Reach 162283 := rs (se 1 (by rfl) ⟨121712, by rfl⟩) R243425
theorem R63983 : Reach 63983 := rs (se 1 (by rfl) ⟨47987, by rfl⟩) R95975
theorem R424673 : Reach 424673 := rs (se 2 (by rfl) ⟨159252, by rfl⟩) R318505
theorem R64239 : Reach 64239 := rs (se 1 (by rfl) ⟨48179, by rfl⟩) R96359
theorem R97055 : Reach 97055 := rs (se 1 (by rfl) ⟨72791, by rfl⟩) R145583
theorem R64359 : Reach 64359 := rs (se 1 (by rfl) ⟨48269, by rfl⟩) R96539
theorem R64383 : Reach 64383 := rs (se 1 (by rfl) ⟨48287, by rfl⟩) R96575
theorem R64495 : Reach 64495 := rs (se 1 (by rfl) ⟨48371, by rfl⟩) R96743
theorem R64543 : Reach 64543 := rs (se 1 (by rfl) ⟨48407, by rfl⟩) R96815
theorem R163135 : Reach 163135 := rs (se 1 (by rfl) ⟨122351, by rfl⟩) R244703
theorem R97607 : Reach 97607 := rs (se 1 (by rfl) ⟨73205, by rfl⟩) R146411
theorem R65279 : Reach 65279 := rs (se 1 (by rfl) ⟨48959, by rfl⟩) R97919
theorem R393133 : Reach 393133 := rs (se 3 (by rfl) ⟨73712, by rfl⟩) R147425
theorem R65639 : Reach 65639 := rs (se 1 (by rfl) ⟨49229, by rfl⟩) R98459
theorem R2752703 : Reach 2752703 := rs (se 1 (by rfl) ⟨2064527, by rfl⟩) R4129055
theorem R491831 : Reach 491831 := rs (se 1 (by rfl) ⟨368873, by rfl⟩) R737747
theorem R65855 : Reach 65855 := rs (se 1 (by rfl) ⟨49391, by rfl⟩) R98783
theorem R66287 : Reach 66287 := rs (se 1 (by rfl) ⟨49715, by rfl⟩) R99431
theorem R66559 : Reach 66559 := rs (se 1 (by rfl) ⟨49919, by rfl⟩) R99839
theorem R329021 : Reach 329021 := rs (se 3 (by rfl) ⟨61691, by rfl⟩) R123383
theorem R99647 : Reach 99647 := rs (se 1 (by rfl) ⟨74735, by rfl⟩) R149471
theorem R66879 : Reach 66879 := rs (se 1 (by rfl) ⟨50159, by rfl⟩) R100319
theorem R99695 : Reach 99695 := rs (se 1 (by rfl) ⟨74771, by rfl⟩) R149543
theorem R99791 : Reach 99791 := rs (se 1 (by rfl) ⟨74843, by rfl⟩) R149687
theorem R99887 : Reach 99887 := rs (se 1 (by rfl) ⟨74915, by rfl⟩) R149831
theorem R99995 : Reach 99995 := rs (se 1 (by rfl) ⟨74996, by rfl⟩) R149993
theorem R788413 : Reach 788413 := rs (se 3 (by rfl) ⟨147827, by rfl⟩) R295655
theorem R165959 : Reach 165959 := rs (se 1 (by rfl) ⟨124469, by rfl⟩) R248939
theorem R330155 : Reach 330155 := rs (se 1 (by rfl) ⟨247616, by rfl⟩) R495233
theorem R365093 : Reach 365093 := rs (se 4 (by rfl) ⟨34227, by rfl⟩) R68455
theorem R1413895 : Reach 1413895 := rs (se 1 (by rfl) ⟨1060421, by rfl⟩) R2120843
theorem R72895 : Reach 72895 := rs (se 1 (by rfl) ⟨54671, by rfl⟩) R109343
theorem R761075 : Reach 761075 := rs (se 1 (by rfl) ⟨570806, by rfl⟩) R1141613
theorem R269821 : Reach 269821 := rs (se 3 (by rfl) ⟨50591, by rfl⟩) R101183
theorem R73831 : Reach 73831 := rs (se 1 (by rfl) ⟨55373, by rfl⟩) R110747
theorem R336889 : Reach 336889 := rs (se 2 (by rfl) ⟨126333, by rfl⟩) R252667
theorem R370493 : Reach 370493 := rs (se 3 (by rfl) ⟨69467, by rfl⟩) R138935
theorem R207031 : Reach 207031 := rs (se 1 (by rfl) ⟨155273, by rfl⟩) R310547
theorem R3975965 : Reach 3975965 := rs (se 3 (by rfl) ⟨745493, by rfl⟩) R1490987
theorem R143135 : Reach 143135 := rs (se 1 (by rfl) ⟨107351, by rfl⟩) R214703
theorem R143927 : Reach 143927 := rs (se 1 (by rfl) ⟨107945, by rfl⟩) R215891
theorem R604007 : Reach 604007 := rs (se 1 (by rfl) ⟨453005, by rfl⟩) R906011
theorem R2013407 : Reach 2013407 := rs (se 1 (by rfl) ⟨1510055, by rfl⟩) R3020111
theorem R145819 : Reach 145819 := rs (se 1 (by rfl) ⟨109364, by rfl⟩) R218729
theorem R80767 : Reach 80767 := rs (se 1 (by rfl) ⟨60575, by rfl⟩) R121151
theorem R703403 : Reach 703403 := rs (se 1 (by rfl) ⟨527552, by rfl⟩) R1055105
theorem R375799 : Reach 375799 := rs (se 1 (by rfl) ⟨281849, by rfl⟩) R563699
theorem R1785311 : Reach 1785311 := rs (se 1 (by rfl) ⟨1338983, by rfl⟩) R2677967
theorem R245321 : Reach 245321 := rs (se 2 (by rfl) ⟨91995, by rfl⟩) R183991
theorem R147617 : Reach 147617 := rs (se 2 (by rfl) ⟨55356, by rfl⟩) R110713
theorem R245935 : Reach 245935 := rs (se 1 (by rfl) ⟨184451, by rfl⟩) R368903
theorem R377257 : Reach 377257 := rs (se 2 (by rfl) ⟨141471, by rfl⟩) R282943
theorem R147959 : Reach 147959 := rs (se 1 (by rfl) ⟨110969, by rfl⟩) R221939
theorem R672605 : Reach 672605 := rs (se 3 (by rfl) ⟨126113, by rfl⟩) R252227
theorem R2934767 : Reach 2934767 := rs (se 1 (by rfl) ⟨2201075, by rfl⟩) R4402151
theorem R477211 : Reach 477211 := rs (se 1 (by rfl) ⟨357908, by rfl⟩) R715817
theorem R215081 : Reach 215081 := rs (se 2 (by rfl) ⟨80655, by rfl⟩) R161311
theorem R215567 : Reach 215567 := rs (se 1 (by rfl) ⟨161675, by rfl⟩) R323351
theorem R215999 : Reach 215999 := rs (se 1 (by rfl) ⟨161999, by rfl⟩) R323999
theorem R248771 : Reach 248771 := rs (se 1 (by rfl) ⟨186578, by rfl⟩) R373157
theorem R216377 : Reach 216377 := rs (se 2 (by rfl) ⟨81141, by rfl⟩) R162283
theorem R217513 : Reach 217513 := rs (se 2 (by rfl) ⟨81567, by rfl⟩) R163135
theorem R283115 : Reach 283115 := rs (se 1 (by rfl) ⟨212336, by rfl⟩) R424673
theorem R218537 : Reach 218537 := rs (se 2 (by rfl) ⟨81951, by rfl⟩) R163903
theorem R252143 : Reach 252143 := rs (se 1 (by rfl) ⟨189107, by rfl⟩) R378215
theorem R1465199 : Reach 1465199 := rs (se 1 (by rfl) ⟨1098899, by rfl⟩) R2197799
theorem R122399 : Reach 122399 := rs (se 1 (by rfl) ⟨91799, by rfl⟩) R183599
theorem R220967 : Reach 220967 := rs (se 1 (by rfl) ⟨165725, by rfl⟩) R331451
theorem R7004231 : Reach 7004231 := rs (se 1 (by rfl) ⟨5253173, by rfl⟩) R10506347
theorem R221345 : Reach 221345 := rs (se 2 (by rfl) ⟨83004, by rfl⟩) R166009
theorem R90715 : Reach 90715 := rs (se 1 (by rfl) ⟨68036, by rfl⟩) R136073
theorem R8447651 : Reach 8447651 := rs (se 1 (by rfl) ⟨6335738, by rfl⟩) R12671477
theorem R191135 : Reach 191135 := rs (se 1 (by rfl) ⟨143351, by rfl⟩) R286703
theorem R224585 : Reach 224585 := rs (se 2 (by rfl) ⟨84219, by rfl⟩) R168439
theorem R683423 : Reach 683423 := rs (se 1 (by rfl) ⟨512567, by rfl⟩) R1025135
theorem R6876647 : Reach 6876647 := rs (se 1 (by rfl) ⟨5157485, by rfl⟩) R10314971
theorem R650767 : Reach 650767 := rs (se 1 (by rfl) ⟨488075, by rfl⟩) R976151
theorem R683677 : Reach 683677 := rs (se 3 (by rfl) ⟨128189, by rfl⟩) R256379
theorem R356071 : Reach 356071 := rs (se 1 (by rfl) ⟨267053, by rfl⟩) R534107
theorem R94703 : Reach 94703 := rs (se 1 (by rfl) ⟨71027, by rfl⟩) R142055
theorem R160481 : Reach 160481 := rs (se 2 (by rfl) ⟨60180, by rfl⟩) R120361
theorem R13202189 : Reach 13202189 := rs (se 3 (by rfl) ⟨2475410, by rfl⟩) R4950821
theorem R1110995 : Reach 1110995 := rs (se 1 (by rfl) ⟨833246, by rfl⟩) R1666493
theorem R95231 : Reach 95231 := rs (se 1 (by rfl) ⟨71423, by rfl⟩) R142847
theorem R96191 : Reach 96191 := rs (se 1 (by rfl) ⟨72143, by rfl⟩) R144287
theorem R63771 : Reach 63771 := rs (se 1 (by rfl) ⟨47828, by rfl⟩) R95657
theorem R752249 : Reach 752249 := rs (se 2 (by rfl) ⟨282093, by rfl⟩) R564187
theorem R64191 : Reach 64191 := rs (se 1 (by rfl) ⟨48143, by rfl⟩) R96287
theorem R64319 : Reach 64319 := rs (se 1 (by rfl) ⟨48239, by rfl⟩) R96479
theorem R97391 : Reach 97391 := rs (se 1 (by rfl) ⟨73043, by rfl⟩) R146087
theorem R97439 : Reach 97439 := rs (se 1 (by rfl) ⟨73079, by rfl⟩) R146159
theorem R64703 : Reach 64703 := rs (se 1 (by rfl) ⟨48527, by rfl⟩) R97055
theorem R65071 : Reach 65071 := rs (se 1 (by rfl) ⟨48803, by rfl⟩) R97607
theorem R22904383 : Reach 22904383 := rs (se 1 (by rfl) ⟨17178287, by rfl⟩) R34356575
theorem R97895 : Reach 97895 := rs (se 1 (by rfl) ⟨73421, by rfl⟩) R146843
theorem R524177 : Reach 524177 := rs (se 2 (by rfl) ⟨196566, by rfl⟩) R393133
theorem R229351 : Reach 229351 := rs (se 1 (by rfl) ⟨172013, by rfl⟩) R344027
theorem R98411 : Reach 98411 := rs (se 1 (by rfl) ⟨73808, by rfl⟩) R147617
theorem R1835135 : Reach 1835135 := rs (se 1 (by rfl) ⟨1376351, by rfl⟩) R2752703
theorem R98441 : Reach 98441 := rs (se 2 (by rfl) ⟨36915, by rfl⟩) R73831
theorem R327887 : Reach 327887 := rs (se 1 (by rfl) ⟨245915, by rfl⟩) R491831
theorem R98639 : Reach 98639 := rs (se 1 (by rfl) ⟨73979, by rfl⟩) R147959
theorem R66431 : Reach 66431 := rs (se 1 (by rfl) ⟨49823, by rfl⟩) R99647
theorem R66463 : Reach 66463 := rs (se 1 (by rfl) ⟨49847, by rfl⟩) R99695
theorem R1311653 : Reach 1311653 := rs (se 4 (by rfl) ⟨122967, by rfl⟩) R245935
theorem R66527 : Reach 66527 := rs (se 1 (by rfl) ⟨49895, by rfl⟩) R99791
theorem R66591 : Reach 66591 := rs (se 1 (by rfl) ⟨49943, by rfl⟩) R99887
theorem R66663 : Reach 66663 := rs (se 1 (by rfl) ⟨49997, by rfl⟩) R99995
theorem R165847 : Reach 165847 := rs (se 1 (by rfl) ⟨124385, by rfl⟩) R248771
theorem R1051217 : Reach 1051217 := rs (se 2 (by rfl) ⟨394206, by rfl⟩) R788413
theorem R168095 : Reach 168095 := rs (se 1 (by rfl) ⟨126071, by rfl⟩) R252143
theorem R106987 : Reach 106987 := rs (se 1 (by rfl) ⟨80240, by rfl⟩) R160481
theorem R107689 : Reach 107689 := rs (se 2 (by rfl) ⟨40383, by rfl⟩) R80767
theorem R402671 : Reach 402671 := rs (se 1 (by rfl) ⟨302003, by rfl⟩) R604007
theorem R501065 : Reach 501065 := rs (se 2 (by rfl) ⟨187899, by rfl⟩) R375799
theorem R501499 : Reach 501499 := rs (se 1 (by rfl) ⟨376124, by rfl⟩) R752249
theorem R468935 : Reach 468935 := rs (se 1 (by rfl) ⟨351701, by rfl⟩) R703403
theorem R1190207 : Reach 1190207 := rs (se 1 (by rfl) ⟨892655, by rfl⟩) R1785311
theorem R305801 : Reach 305801 := rs (se 2 (by rfl) ⟨114675, by rfl⟩) R229351
theorem R503009 : Reach 503009 := rs (se 2 (by rfl) ⟨188628, by rfl⟩) R377257
theorem R143387 : Reach 143387 := rs (se 1 (by rfl) ⟨107540, by rfl⟩) R215081
theorem R110639 : Reach 110639 := rs (se 1 (by rfl) ⟨82979, by rfl⟩) R165959
theorem R143711 : Reach 143711 := rs (se 1 (by rfl) ⟨107783, by rfl⟩) R215567
theorem R143999 : Reach 143999 := rs (se 1 (by rfl) ⟨107999, by rfl⟩) R215999
theorem R144251 : Reach 144251 := rs (se 1 (by rfl) ⟨108188, by rfl⟩) R216377
theorem R636281 : Reach 636281 := rs (se 2 (by rfl) ⟨238605, by rfl⟩) R477211
theorem R276041 : Reach 276041 := rs (se 2 (by rfl) ⟨103515, by rfl⟩) R207031
theorem R243395 : Reach 243395 := rs (se 1 (by rfl) ⟨182546, by rfl⟩) R365093
theorem R145691 : Reach 145691 := rs (se 1 (by rfl) ⟨109268, by rfl⟩) R218537
theorem R867689 : Reach 867689 := rs (se 2 (by rfl) ⟨325383, by rfl⟩) R650767
theorem R507383 : Reach 507383 := rs (se 1 (by rfl) ⟨380537, by rfl⟩) R761075
theorem R474761 : Reach 474761 := rs (se 2 (by rfl) ⟨178035, by rfl⟩) R356071
theorem R81599 : Reach 81599 := rs (se 1 (by rfl) ⟨61199, by rfl⟩) R122399
theorem R147311 : Reach 147311 := rs (se 1 (by rfl) ⟨110483, by rfl⟩) R220967
theorem R4669487 : Reach 4669487 := rs (se 1 (by rfl) ⟨3502115, by rfl⟩) R7004231
theorem R147563 : Reach 147563 := rs (se 1 (by rfl) ⟨110672, by rfl⟩) R221345
theorem R1885193 : Reach 1885193 := rs (se 2 (by rfl) ⟨706947, by rfl⟩) R1413895
theorem R246995 : Reach 246995 := rs (se 1 (by rfl) ⟨185246, by rfl⟩) R370493
theorem R149723 : Reach 149723 := rs (se 1 (by rfl) ⟨112292, by rfl⟩) R224585
theorem R8801459 : Reach 8801459 := rs (se 1 (by rfl) ⟨6601094, by rfl⟩) R13202189
theorem R740663 : Reach 740663 := rs (se 1 (by rfl) ⟨555497, by rfl⟩) R1110995
theorem R349451 : Reach 349451 := rs (se 1 (by rfl) ⟨262088, by rfl⟩) R524177
theorem R120953 : Reach 120953 := rs (se 2 (by rfl) ⟨45357, by rfl⟩) R90715
theorem R219347 : Reach 219347 := rs (se 1 (by rfl) ⟨164510, by rfl⟩) R329021
theorem R1956511 : Reach 1956511 := rs (se 1 (by rfl) ⟨1467383, by rfl⟩) R2934767
theorem R449185 : Reach 449185 := rs (se 2 (by rfl) ⟨168444, by rfl⟩) R336889
theorem R220103 : Reach 220103 := rs (se 1 (by rfl) ⟨165077, by rfl⟩) R330155
theorem R777701 : Reach 777701 := rs (se 4 (by rfl) ⟨72909, by rfl⟩) R145819
theorem R188743 : Reach 188743 := rs (se 1 (by rfl) ⟨141557, by rfl⟩) R283115
theorem R28697813 : Reach 28697813 := rs (se 7 (by rfl) ⟨336302, by rfl⟩) R672605
theorem R976799 : Reach 976799 := rs (se 1 (by rfl) ⟨732599, by rfl⟩) R1465199
theorem R911569 : Reach 911569 := rs (se 2 (by rfl) ⟨341838, by rfl⟩) R683677
theorem R290017 : Reach 290017 := rs (se 2 (by rfl) ⟨108756, by rfl⟩) R217513
theorem R5631767 : Reach 5631767 := rs (se 1 (by rfl) ⟨4223825, by rfl⟩) R8447651
theorem R127423 : Reach 127423 := rs (se 1 (by rfl) ⟨95567, by rfl⟩) R191135
theorem R2650643 : Reach 2650643 := rs (se 1 (by rfl) ⟨1987982, by rfl⟩) R3975965
theorem R455615 : Reach 455615 := rs (se 1 (by rfl) ⟨341711, by rfl⟩) R683423
theorem R4584431 : Reach 4584431 := rs (se 1 (by rfl) ⟨3438323, by rfl⟩) R6876647
theorem R95423 : Reach 95423 := rs (se 1 (by rfl) ⟨71567, by rfl⟩) R143135
theorem R63135 : Reach 63135 := rs (se 1 (by rfl) ⟨47351, by rfl⟩) R94703
theorem R95951 : Reach 95951 := rs (se 1 (by rfl) ⟨71963, by rfl⟩) R143927
theorem R63487 : Reach 63487 := rs (se 1 (by rfl) ⟨47615, by rfl⟩) R95231
theorem R64127 : Reach 64127 := rs (se 1 (by rfl) ⟨48095, by rfl⟩) R96191
theorem R1342271 : Reach 1342271 := rs (se 1 (by rfl) ⟨1006703, by rfl⟩) R2013407
theorem R97193 : Reach 97193 := rs (se 2 (by rfl) ⟨36447, by rfl⟩) R72895
theorem R359761 : Reach 359761 := rs (se 2 (by rfl) ⟨134910, by rfl⟩) R269821
theorem R64927 : Reach 64927 := rs (se 1 (by rfl) ⟨48695, by rfl⟩) R97391
theorem R30539177 : Reach 30539177 := rs (se 2 (by rfl) ⟨11452191, by rfl⟩) R22904383
theorem R64959 : Reach 64959 := rs (se 1 (by rfl) ⟨48719, by rfl⟩) R97439
theorem R163547 : Reach 163547 := rs (se 1 (by rfl) ⟨122660, by rfl⟩) R245321
theorem R65263 : Reach 65263 := rs (se 1 (by rfl) ⟨48947, by rfl⟩) R97895
theorem R3112991 : Reach 3112991 := rs (se 1 (by rfl) ⟨2334743, by rfl⟩) R4669487
theorem R98375 : Reach 98375 := rs (se 1 (by rfl) ⟨73781, by rfl⟩) R147563
theorem R65607 : Reach 65607 := rs (se 1 (by rfl) ⟨49205, by rfl⟩) R98411
theorem R65627 : Reach 65627 := rs (se 1 (by rfl) ⟨49220, by rfl⟩) R98441
theorem R65759 : Reach 65759 := rs (se 1 (by rfl) ⟨49319, by rfl⟩) R98639
theorem R164663 : Reach 164663 := rs (se 1 (by rfl) ⟨123497, by rfl⟩) R246995
theorem R99815 : Reach 99815 := rs (se 1 (by rfl) ⟨74861, by rfl⟩) R149723
theorem R5867639 : Reach 5867639 := rs (se 1 (by rfl) ⟨4400729, by rfl⟩) R8801459
theorem R493775 : Reach 493775 := rs (se 1 (by rfl) ⟨370331, by rfl⟩) R740663
theorem R1215425 : Reach 1215425 := rs (se 2 (by rfl) ⟨455784, by rfl⟩) R911569
theorem R232967 : Reach 232967 := rs (se 1 (by rfl) ⟨174725, by rfl⟩) R349451
theorem R169897 : Reach 169897 := rs (se 2 (by rfl) ⟨63711, by rfl⟩) R127423
theorem R268447 : Reach 268447 := rs (se 1 (by rfl) ⟨201335, by rfl⟩) R402671
theorem R334043 : Reach 334043 := rs (se 1 (by rfl) ⟨250532, by rfl⟩) R501065
theorem R793471 : Reach 793471 := rs (se 1 (by rfl) ⟨595103, by rfl⟩) R1190207
theorem R203867 : Reach 203867 := rs (se 1 (by rfl) ⟨152900, by rfl⟩) R305801
theorem R335339 : Reach 335339 := rs (se 1 (by rfl) ⟨251504, by rfl⟩) R503009
theorem R3579389 : Reach 3579389 := rs (se 3 (by rfl) ⟨671135, by rfl⟩) R1342271
theorem R73759 : Reach 73759 := rs (se 1 (by rfl) ⟨55319, by rfl⟩) R110639
theorem R303743 : Reach 303743 := rs (se 1 (by rfl) ⟨227807, by rfl⟩) R455615
theorem R3056287 : Reach 3056287 := rs (se 1 (by rfl) ⟨2292215, by rfl⟩) R4584431
theorem R598913 : Reach 598913 := rs (se 2 (by rfl) ⟨224592, by rfl⟩) R449185
theorem R2073869 : Reach 2073869 := rs (se 3 (by rfl) ⟨388850, by rfl⟩) R777701
theorem R20359451 : Reach 20359451 := rs (se 1 (by rfl) ⟨15269588, by rfl⟩) R30539177
theorem R338255 : Reach 338255 := rs (se 1 (by rfl) ⟨253691, by rfl⟩) R507383
theorem R109031 : Reach 109031 := rs (se 1 (by rfl) ⟨81773, by rfl⟩) R163547
theorem R1223423 : Reach 1223423 := rs (se 1 (by rfl) ⟨917567, by rfl⟩) R1835135
theorem R142649 : Reach 142649 := rs (se 2 (by rfl) ⟨53493, by rfl⟩) R106987
theorem R1256795 : Reach 1256795 := rs (se 1 (by rfl) ⟨942596, by rfl⟩) R1885193
theorem R143585 : Reach 143585 := rs (se 2 (by rfl) ⟨53844, by rfl⟩) R107689
theorem R700811 : Reach 700811 := rs (se 1 (by rfl) ⟨525608, by rfl⟩) R1051217
theorem R668665 : Reach 668665 := rs (se 2 (by rfl) ⟨250749, by rfl⟩) R501499
theorem R112063 : Reach 112063 := rs (se 1 (by rfl) ⟨84047, by rfl⟩) R168095
theorem R146231 : Reach 146231 := rs (se 1 (by rfl) ⟨109673, by rfl⟩) R219347
theorem R146735 : Reach 146735 := rs (se 1 (by rfl) ⟨110051, by rfl⟩) R220103
theorem R312623 : Reach 312623 := rs (se 1 (by rfl) ⟨234467, by rfl⟩) R468935
theorem R870389 : Reach 870389 := rs (se 5 (by rfl) ⟨40799, by rfl⟩) R81599
theorem R3754511 : Reach 3754511 := rs (se 1 (by rfl) ⟨2815883, by rfl⟩) R5631767
theorem R2608681 : Reach 2608681 := rs (se 2 (by rfl) ⟨978255, by rfl⟩) R1956511
theorem R184027 : Reach 184027 := rs (se 1 (by rfl) ⟨138020, by rfl⟩) R276041
theorem R479681 : Reach 479681 := rs (se 2 (by rfl) ⟨179880, by rfl⟩) R359761
theorem R578459 : Reach 578459 := rs (se 1 (by rfl) ⟨433844, by rfl⟩) R867689
theorem R316507 : Reach 316507 := rs (se 1 (by rfl) ⟨237380, by rfl⟩) R474761
theorem R218591 : Reach 218591 := rs (se 1 (by rfl) ⟨163943, by rfl⟩) R327887
theorem R251657 : Reach 251657 := rs (se 2 (by rfl) ⟨94371, by rfl⟩) R188743
theorem R874435 : Reach 874435 := rs (se 1 (by rfl) ⟨655826, by rfl⟩) R1311653
theorem R221129 : Reach 221129 := rs (se 2 (by rfl) ⟨82923, by rfl⟩) R165847
theorem R386689 : Reach 386689 := rs (se 2 (by rfl) ⟨145008, by rfl⟩) R290017
theorem R354469 : Reach 354469 := rs (se 4 (by rfl) ⟨33231, by rfl⟩) R66463
theorem R322541 : Reach 322541 := rs (se 3 (by rfl) ⟨60476, by rfl⟩) R120953
theorem R19131875 : Reach 19131875 := rs (se 1 (by rfl) ⟨14348906, by rfl⟩) R28697813
theorem R651199 : Reach 651199 := rs (se 1 (by rfl) ⟨488399, by rfl⟩) R976799
theorem R95591 : Reach 95591 := rs (se 1 (by rfl) ⟨71693, by rfl⟩) R143387
theorem R95807 : Reach 95807 := rs (se 1 (by rfl) ⟨71855, by rfl⟩) R143711
theorem R1767095 : Reach 1767095 := rs (se 1 (by rfl) ⟨1325321, by rfl⟩) R2650643
theorem R95999 : Reach 95999 := rs (se 1 (by rfl) ⟨71999, by rfl⟩) R143999
theorem R96167 : Reach 96167 := rs (se 1 (by rfl) ⟨72125, by rfl⟩) R144251
theorem R63615 : Reach 63615 := rs (se 1 (by rfl) ⟨47711, by rfl⟩) R95423
theorem R424187 : Reach 424187 := rs (se 1 (by rfl) ⟨318140, by rfl⟩) R636281
theorem R162263 : Reach 162263 := rs (se 1 (by rfl) ⟨121697, by rfl⟩) R243395
theorem R63967 : Reach 63967 := rs (se 1 (by rfl) ⟨47975, by rfl⟩) R95951
theorem R97127 : Reach 97127 := rs (se 1 (by rfl) ⟨72845, by rfl⟩) R145691
theorem R64795 : Reach 64795 := rs (se 1 (by rfl) ⟨48596, by rfl⟩) R97193
theorem R98207 : Reach 98207 := rs (se 1 (by rfl) ⟨73655, by rfl⟩) R147311
theorem R98345 : Reach 98345 := rs (se 2 (by rfl) ⟨36879, by rfl⟩) R73759
theorem R65583 : Reach 65583 := rs (se 1 (by rfl) ⟨49187, by rfl⟩) R98375
theorem R66543 : Reach 66543 := rs (se 1 (by rfl) ⟨49907, by rfl⟩) R99815
theorem R329183 : Reach 329183 := rs (se 1 (by rfl) ⟨246887, by rfl⟩) R493775
theorem R1542557 : Reach 1542557 := rs (se 3 (by rfl) ⟨289229, by rfl⟩) R578459
theorem R167771 : Reach 167771 := rs (se 1 (by rfl) ⟨125828, by rfl⟩) R251657
theorem R3478241 : Reach 3478241 := rs (se 2 (by rfl) ⟨1304340, by rfl⟩) R2608681
theorem R135911 : Reach 135911 := rs (se 1 (by rfl) ⟨101933, by rfl⟩) R203867
theorem R202495 : Reach 202495 := rs (se 1 (by rfl) ⟨151871, by rfl⟩) R303743
theorem R399275 : Reach 399275 := rs (se 1 (by rfl) ⟨299456, by rfl⟩) R598913
theorem R1382579 : Reach 1382579 := rs (se 1 (by rfl) ⟨1036934, by rfl⟩) R2073869
theorem R13572967 : Reach 13572967 := rs (se 1 (by rfl) ⟨10179725, by rfl⟩) R20359451
theorem R12754583 : Reach 12754583 := rs (se 1 (by rfl) ⟨9565937, by rfl⟩) R19131875
theorem R467207 : Reach 467207 := rs (se 1 (by rfl) ⟨350405, by rfl⟩) R700811
theorem R1057961 : Reach 1057961 := rs (se 2 (by rfl) ⟨396735, by rfl⟩) R793471
theorem R108175 : Reach 108175 := rs (se 1 (by rfl) ⟨81131, by rfl⟩) R162263
theorem R2075327 : Reach 2075327 := rs (se 1 (by rfl) ⟨1556495, by rfl⟩) R3112991
theorem R109775 : Reach 109775 := rs (se 1 (by rfl) ⟨82331, by rfl⟩) R164663
theorem R208415 : Reach 208415 := rs (se 1 (by rfl) ⟨156311, by rfl⟩) R312623
theorem R4075049 : Reach 4075049 := rs (se 2 (by rfl) ⟨1528143, by rfl⟩) R3056287
theorem R3911759 : Reach 3911759 := rs (se 1 (by rfl) ⟨2933819, by rfl⟩) R5867639
theorem R2503007 : Reach 2503007 := rs (se 1 (by rfl) ⟨1877255, by rfl⟩) R3754511
theorem R472625 : Reach 472625 := rs (se 2 (by rfl) ⟨177234, by rfl⟩) R354469
theorem R145727 : Reach 145727 := rs (se 1 (by rfl) ⟨109295, by rfl⟩) R218591
theorem R245369 : Reach 245369 := rs (se 2 (by rfl) ⟨92013, by rfl⟩) R184027
theorem R868265 : Reach 868265 := rs (se 2 (by rfl) ⟨325599, by rfl⟩) R651199
theorem R147419 : Reach 147419 := rs (se 1 (by rfl) ⟨110564, by rfl⟩) R221129
theorem R149417 : Reach 149417 := rs (se 2 (by rfl) ⟨56031, by rfl⟩) R112063
theorem R215027 : Reach 215027 := rs (se 1 (by rfl) ⟨161270, by rfl⟩) R322541
theorem R837863 : Reach 837863 := rs (se 1 (by rfl) ⟨628397, by rfl⟩) R1256795
theorem R1165913 : Reach 1165913 := rs (se 2 (by rfl) ⟨437217, by rfl⟩) R874435
theorem R282791 : Reach 282791 := rs (se 1 (by rfl) ⟨212093, by rfl⟩) R424187
theorem R580259 : Reach 580259 := rs (se 1 (by rfl) ⟨435194, by rfl⟩) R870389
theorem R810283 : Reach 810283 := rs (se 1 (by rfl) ⟨607712, by rfl⟩) R1215425
theorem R515585 : Reach 515585 := rs (se 2 (by rfl) ⟨193344, by rfl⟩) R386689
theorem R319787 : Reach 319787 := rs (se 1 (by rfl) ⟨239840, by rfl⟩) R479681
theorem R222695 : Reach 222695 := rs (se 1 (by rfl) ⟨167021, by rfl⟩) R334043
theorem R223559 : Reach 223559 := rs (se 1 (by rfl) ⟨167669, by rfl⟩) R335339
theorem R2386259 : Reach 2386259 := rs (se 1 (by rfl) ⟨1789694, by rfl⟩) R3579389
theorem R3566213 : Reach 3566213 := rs (se 4 (by rfl) ⟨334332, by rfl⟩) R668665
theorem R290749 : Reach 290749 := rs (se 3 (by rfl) ⟨54515, by rfl⟩) R109031
theorem R422009 : Reach 422009 := rs (se 2 (by rfl) ⟨158253, by rfl⟩) R316507
theorem R225503 : Reach 225503 := rs (se 1 (by rfl) ⟨169127, by rfl⟩) R338255
theorem R815615 : Reach 815615 := rs (se 1 (by rfl) ⟨611711, by rfl⟩) R1223423
theorem R95099 : Reach 95099 := rs (se 1 (by rfl) ⟨71324, by rfl⟩) R142649
theorem R226529 : Reach 226529 := rs (se 2 (by rfl) ⟨84948, by rfl⟩) R169897
theorem R95723 : Reach 95723 := rs (se 1 (by rfl) ⟨71792, by rfl⟩) R143585
theorem R357929 : Reach 357929 := rs (se 2 (by rfl) ⟨134223, by rfl⟩) R268447
theorem R63727 : Reach 63727 := rs (se 1 (by rfl) ⟨47795, by rfl⟩) R95591
theorem R63871 : Reach 63871 := rs (se 1 (by rfl) ⟨47903, by rfl⟩) R95807
theorem R1178063 : Reach 1178063 := rs (se 1 (by rfl) ⟨883547, by rfl⟩) R1767095
theorem R63999 : Reach 63999 := rs (se 1 (by rfl) ⟨47999, by rfl⟩) R95999
theorem R64111 : Reach 64111 := rs (se 1 (by rfl) ⟨48083, by rfl⟩) R96167
theorem R621245 : Reach 621245 := rs (se 3 (by rfl) ⟨116483, by rfl⟩) R232967
theorem R97487 : Reach 97487 := rs (se 1 (by rfl) ⟨73115, by rfl⟩) R146231
theorem R64751 : Reach 64751 := rs (se 1 (by rfl) ⟨48563, by rfl⟩) R97127
theorem R97823 : Reach 97823 := rs (se 1 (by rfl) ⟨73367, by rfl⟩) R146735
theorem R65471 : Reach 65471 := rs (se 1 (by rfl) ⟨49103, by rfl⟩) R98207
theorem R65563 : Reach 65563 := rs (se 1 (by rfl) ⟨49172, by rfl⟩) R98345
theorem R262253 : Reach 262253 := rs (se 3 (by rfl) ⟨49172, by rfl⟩) R98345
theorem R99611 : Reach 99611 := rs (se 1 (by rfl) ⟨74708, by rfl⟩) R149417
theorem R558575 : Reach 558575 := rs (se 1 (by rfl) ⟨418931, by rfl⟩) R837863
theorem R9275309 : Reach 9275309 := rs (se 3 (by rfl) ⟨1739120, by rfl⟩) R3478241
theorem R266183 : Reach 266183 := rs (se 1 (by rfl) ⟨199637, by rfl⟩) R399275
theorem R921719 : Reach 921719 := rs (se 1 (by rfl) ⟨691289, by rfl⟩) R1382579
theorem R1383551 : Reach 1383551 := rs (se 1 (by rfl) ⟨1037663, by rfl⟩) R2075327
theorem R73183 : Reach 73183 := rs (se 1 (by rfl) ⟨54887, by rfl⟩) R109775
theorem R269993 : Reach 269993 := rs (se 2 (by rfl) ⟨101247, by rfl⟩) R202495
theorem R138943 : Reach 138943 := rs (se 1 (by rfl) ⟨104207, by rfl⟩) R208415
theorem R238619 : Reach 238619 := rs (se 1 (by rfl) ⟨178964, by rfl⟩) R357929
theorem R18097289 : Reach 18097289 := rs (se 2 (by rfl) ⟨6786483, by rfl⟩) R13572967
theorem R143351 : Reach 143351 := rs (se 1 (by rfl) ⟨107513, by rfl⟩) R215027
theorem R1028371 : Reach 1028371 := rs (se 1 (by rfl) ⟨771278, by rfl⟩) R1542557
theorem R144233 : Reach 144233 := rs (se 2 (by rfl) ⟨54087, by rfl⟩) R108175
theorem R111847 : Reach 111847 := rs (se 1 (by rfl) ⟨83885, by rfl⟩) R167771
theorem R8503055 : Reach 8503055 := rs (se 1 (by rfl) ⟨6377291, by rfl⟩) R12754583
theorem R311471 : Reach 311471 := rs (se 1 (by rfl) ⟨233603, by rfl⟩) R467207
theorem R213191 : Reach 213191 := rs (se 1 (by rfl) ⟨159893, by rfl⟩) R319787
theorem R705307 : Reach 705307 := rs (se 1 (by rfl) ⟨528980, by rfl⟩) R1057961
theorem R148463 : Reach 148463 := rs (se 1 (by rfl) ⟨111347, by rfl⟩) R222695
theorem R149039 : Reach 149039 := rs (se 1 (by rfl) ⟨111779, by rfl⟩) R223559
theorem R1590839 : Reach 1590839 := rs (se 1 (by rfl) ⟨1193129, by rfl⟩) R2386259
theorem R2377475 : Reach 2377475 := rs (se 1 (by rfl) ⟨1783106, by rfl⟩) R3566213
theorem R2607839 : Reach 2607839 := rs (se 1 (by rfl) ⟨1955879, by rfl⟩) R3911759
theorem R281339 : Reach 281339 := rs (se 1 (by rfl) ⟨211004, by rfl⟩) R422009
theorem R150335 : Reach 150335 := rs (se 1 (by rfl) ⟨112751, by rfl⟩) R225503
theorem R543743 : Reach 543743 := rs (se 1 (by rfl) ⟨407807, by rfl⟩) R815615
theorem R151019 : Reach 151019 := rs (se 1 (by rfl) ⟨113264, by rfl⟩) R226529
theorem R315083 : Reach 315083 := rs (se 1 (by rfl) ⟨236312, by rfl⟩) R472625
theorem R414163 : Reach 414163 := rs (se 1 (by rfl) ⟨310622, by rfl⟩) R621245
theorem R578843 : Reach 578843 := rs (se 1 (by rfl) ⟨434132, by rfl⟩) R868265
theorem R219455 : Reach 219455 := rs (se 1 (by rfl) ⟨164591, by rfl⟩) R329183
theorem R777275 : Reach 777275 := rs (se 1 (by rfl) ⟨582956, by rfl⟩) R1165913
theorem R188527 : Reach 188527 := rs (se 1 (by rfl) ⟨141395, by rfl⟩) R282791
theorem R90607 : Reach 90607 := rs (se 1 (by rfl) ⟨67955, by rfl⟩) R135911
theorem R386839 : Reach 386839 := rs (se 1 (by rfl) ⟨290129, by rfl⟩) R580259
theorem R387665 : Reach 387665 := rs (se 2 (by rfl) ⟨145374, by rfl⟩) R290749
theorem R2716699 : Reach 2716699 := rs (se 1 (by rfl) ⟨2037524, by rfl⟩) R4075049
theorem R1668671 : Reach 1668671 := rs (se 1 (by rfl) ⟨1251503, by rfl⟩) R2503007
theorem R63399 : Reach 63399 := rs (se 1 (by rfl) ⟨47549, by rfl⟩) R95099
theorem R63815 : Reach 63815 := rs (se 1 (by rfl) ⟨47861, by rfl⟩) R95723
theorem R1374893 : Reach 1374893 := rs (se 3 (by rfl) ⟨257792, by rfl⟩) R515585
theorem R97151 : Reach 97151 := rs (se 1 (by rfl) ⟨72863, by rfl⟩) R145727
theorem R785375 : Reach 785375 := rs (se 1 (by rfl) ⟨589031, by rfl⟩) R1178063
theorem R1080377 : Reach 1080377 := rs (se 2 (by rfl) ⟨405141, by rfl⟩) R810283
theorem R64991 : Reach 64991 := rs (se 1 (by rfl) ⟨48743, by rfl⟩) R97487
theorem R65215 : Reach 65215 := rs (se 1 (by rfl) ⟨48911, by rfl⟩) R97823
theorem R163579 : Reach 163579 := rs (se 1 (by rfl) ⟨122684, by rfl⟩) R245369
theorem R98279 : Reach 98279 := rs (se 1 (by rfl) ⟨73709, by rfl⟩) R147419
theorem R98975 : Reach 98975 := rs (se 1 (by rfl) ⟨74231, by rfl⟩) R148463
theorem R66407 : Reach 66407 := rs (se 1 (by rfl) ⟨49805, by rfl⟩) R99611
theorem R99359 : Reach 99359 := rs (se 1 (by rfl) ⟨74519, by rfl⟩) R149039
theorem R1738559 : Reach 1738559 := rs (se 1 (by rfl) ⟨1303919, by rfl⟩) R2607839
theorem R100223 : Reach 100223 := rs (se 1 (by rfl) ⟨75167, by rfl⟩) R150335
theorem R362495 : Reach 362495 := rs (se 1 (by rfl) ⟨271871, by rfl⟩) R543743
theorem R100679 : Reach 100679 := rs (se 1 (by rfl) ⟨75509, by rfl⟩) R151019
theorem R922367 : Reach 922367 := rs (se 1 (by rfl) ⟨691775, by rfl⟩) R1383551
theorem R12064859 : Reach 12064859 := rs (se 1 (by rfl) ⟨9048644, by rfl⟩) R18097289
theorem R174835 : Reach 174835 := rs (se 1 (by rfl) ⟨131126, by rfl⟩) R262253
theorem R207647 : Reach 207647 := rs (se 1 (by rfl) ⟨155735, by rfl⟩) R311471
theorem R142127 : Reach 142127 := rs (se 1 (by rfl) ⟨106595, by rfl⟩) R213191
theorem R372383 : Reach 372383 := rs (se 1 (by rfl) ⟨279287, by rfl⟩) R558575
theorem R1060559 : Reach 1060559 := rs (se 1 (by rfl) ⟨795419, by rfl⟩) R1590839
theorem R1584983 : Reach 1584983 := rs (se 1 (by rfl) ⟨1188737, by rfl⟩) R2377475
theorem R210055 : Reach 210055 := rs (se 1 (by rfl) ⟨157541, by rfl⟩) R315083
theorem R177455 : Reach 177455 := rs (se 1 (by rfl) ⟨133091, by rfl⟩) R266183
theorem R146303 : Reach 146303 := rs (se 1 (by rfl) ⟨109727, by rfl⟩) R219455
theorem R179995 : Reach 179995 := rs (se 1 (by rfl) ⟨134996, by rfl⟩) R269993
theorem R3622265 : Reach 3622265 := rs (se 2 (by rfl) ⟨1358349, by rfl⟩) R2716699
theorem R149129 : Reach 149129 := rs (se 2 (by rfl) ⟨55923, by rfl⟩) R111847
theorem R185257 : Reach 185257 := rs (se 2 (by rfl) ⟨69471, by rfl⟩) R138943
theorem R218105 : Reach 218105 := rs (se 2 (by rfl) ⟨81789, by rfl⟩) R163579
theorem R251369 : Reach 251369 := rs (se 2 (by rfl) ⟨94263, by rfl⟩) R188527
theorem R120809 : Reach 120809 := rs (se 2 (by rfl) ⟨45303, by rfl⟩) R90607
theorem R940409 : Reach 940409 := rs (se 2 (by rfl) ⟨352653, by rfl⟩) R705307
theorem R6183539 : Reach 6183539 := rs (se 1 (by rfl) ⟨4637654, by rfl⟩) R9275309
theorem R187559 : Reach 187559 := rs (se 1 (by rfl) ⟨140669, by rfl⟩) R281339
theorem R614479 : Reach 614479 := rs (se 1 (by rfl) ⟨460859, by rfl⟩) R921719
theorem R385895 : Reach 385895 := rs (se 1 (by rfl) ⟨289421, by rfl⟩) R578843
theorem R518183 : Reach 518183 := rs (se 1 (by rfl) ⟨388637, by rfl⟩) R777275
theorem R1371161 : Reach 1371161 := rs (se 2 (by rfl) ⟨514185, by rfl⟩) R1028371
theorem R552217 : Reach 552217 := rs (se 2 (by rfl) ⟨207081, by rfl⟩) R414163
theorem R159079 : Reach 159079 := rs (se 1 (by rfl) ⟨119309, by rfl⟩) R238619
theorem R258443 : Reach 258443 := rs (se 1 (by rfl) ⟨193832, by rfl⟩) R387665
theorem R95567 : Reach 95567 := rs (se 1 (by rfl) ⟨71675, by rfl⟩) R143351
theorem R96155 : Reach 96155 := rs (se 1 (by rfl) ⟨72116, by rfl⟩) R144233
theorem R1112447 : Reach 1112447 := rs (se 1 (by rfl) ⟨834335, by rfl⟩) R1668671
theorem R2063141 : Reach 2063141 := rs (se 4 (by rfl) ⟨193419, by rfl⟩) R386839
theorem R916595 : Reach 916595 := rs (se 1 (by rfl) ⟨687446, by rfl⟩) R1374893
theorem R64767 : Reach 64767 := rs (se 1 (by rfl) ⟨48575, by rfl⟩) R97151
theorem R97577 : Reach 97577 := rs (se 2 (by rfl) ⟨36591, by rfl⟩) R73183
theorem R523583 : Reach 523583 := rs (se 1 (by rfl) ⟨392687, by rfl⟩) R785375
theorem R720251 : Reach 720251 := rs (se 1 (by rfl) ⟨540188, by rfl⟩) R1080377
theorem R5668703 : Reach 5668703 := rs (se 1 (by rfl) ⟨4251527, by rfl⟩) R8503055
theorem R65519 : Reach 65519 := rs (se 1 (by rfl) ⟨49139, by rfl⟩) R98279
theorem R819305 : Reach 819305 := rs (se 2 (by rfl) ⟨307239, by rfl⟩) R614479
theorem R65983 : Reach 65983 := rs (se 1 (by rfl) ⟨49487, by rfl⟩) R98975
theorem R66239 : Reach 66239 := rs (se 1 (by rfl) ⟨49679, by rfl⟩) R99359
theorem R99419 : Reach 99419 := rs (se 1 (by rfl) ⟨74564, by rfl⟩) R149129
theorem R66815 : Reach 66815 := rs (se 1 (by rfl) ⟨50111, by rfl⟩) R100223
theorem R67119 : Reach 67119 := rs (se 1 (by rfl) ⟨50339, by rfl⟩) R100679
theorem R2459645 : Reach 2459645 := rs (se 3 (by rfl) ⟨461183, by rfl⟩) R922367
theorem R233113 : Reach 233113 := rs (se 2 (by rfl) ⟨87417, by rfl⟩) R174835
theorem R167579 : Reach 167579 := rs (se 1 (by rfl) ⟨125684, by rfl⟩) R251369
theorem R626939 : Reach 626939 := rs (se 1 (by rfl) ⟨470204, by rfl⟩) R940409
theorem R138431 : Reach 138431 := rs (se 1 (by rfl) ⟨103823, by rfl⟩) R207647
theorem R1056655 : Reach 1056655 := rs (se 1 (by rfl) ⟨792491, by rfl⟩) R1584983
theorem R172295 : Reach 172295 := rs (se 1 (by rfl) ⟨129221, by rfl⟩) R258443
theorem R239993 : Reach 239993 := rs (se 2 (by rfl) ⟨89997, by rfl⟩) R179995
theorem R3779135 : Reach 3779135 := rs (se 1 (by rfl) ⟨2834351, by rfl⟩) R5668703
theorem R1159039 : Reach 1159039 := rs (se 1 (by rfl) ⟨869279, by rfl⟩) R1738559
theorem R241663 : Reach 241663 := rs (se 1 (by rfl) ⟨181247, by rfl⟩) R362495
theorem R145403 : Reach 145403 := rs (se 1 (by rfl) ⟨109052, by rfl⟩) R218105
theorem R8043239 : Reach 8043239 := rs (se 1 (by rfl) ⟨6032429, by rfl⟩) R12064859
theorem R736289 : Reach 736289 := rs (se 2 (by rfl) ⟨276108, by rfl⟩) R552217
theorem R212105 : Reach 212105 := rs (se 2 (by rfl) ⟨79539, by rfl⟩) R159079
theorem R247009 : Reach 247009 := rs (se 2 (by rfl) ⟨92628, by rfl⟩) R185257
theorem R345455 : Reach 345455 := rs (se 1 (by rfl) ⟨259091, by rfl⟩) R518183
theorem R280073 : Reach 280073 := rs (se 2 (by rfl) ⟨105027, by rfl⟩) R210055
theorem R248255 : Reach 248255 := rs (se 1 (by rfl) ⟨186191, by rfl⟩) R372383
theorem R707039 : Reach 707039 := rs (se 1 (by rfl) ⟨530279, by rfl⟩) R1060559
theorem R118303 : Reach 118303 := rs (se 1 (by rfl) ⟨88727, by rfl⟩) R177455
theorem R741631 : Reach 741631 := rs (se 1 (by rfl) ⟨556223, by rfl⟩) R1112447
theorem R611063 : Reach 611063 := rs (se 1 (by rfl) ⟨458297, by rfl⟩) R916595
theorem R349055 : Reach 349055 := rs (se 1 (by rfl) ⟨261791, by rfl⟩) R523583
theorem R480167 : Reach 480167 := rs (se 1 (by rfl) ⟨360125, by rfl⟩) R720251
theorem R2414843 : Reach 2414843 := rs (se 1 (by rfl) ⟨1811132, by rfl⟩) R3622265
theorem R4122359 : Reach 4122359 := rs (se 1 (by rfl) ⟨3091769, by rfl⟩) R6183539
theorem R125039 : Reach 125039 := rs (se 1 (by rfl) ⟨93779, by rfl⟩) R187559
theorem R322157 : Reach 322157 := rs (se 3 (by rfl) ⟨60404, by rfl⟩) R120809
theorem R257263 : Reach 257263 := rs (se 1 (by rfl) ⟨192947, by rfl⟩) R385895
theorem R94751 : Reach 94751 := rs (se 1 (by rfl) ⟨71063, by rfl⟩) R142127
theorem R914107 : Reach 914107 := rs (se 1 (by rfl) ⟨685580, by rfl⟩) R1371161
theorem R63711 : Reach 63711 := rs (se 1 (by rfl) ⟨47783, by rfl⟩) R95567
theorem R64103 : Reach 64103 := rs (se 1 (by rfl) ⟨48077, by rfl⟩) R96155
theorem R1375427 : Reach 1375427 := rs (se 1 (by rfl) ⟨1031570, by rfl⟩) R2063141
theorem R97535 : Reach 97535 := rs (se 1 (by rfl) ⟨73151, by rfl⟩) R146303
theorem R65051 : Reach 65051 := rs (se 1 (by rfl) ⟨48788, by rfl⟩) R97577
theorem R66279 : Reach 66279 := rs (se 1 (by rfl) ⟨49709, by rfl⟩) R99419
theorem R230303 : Reach 230303 := rs (se 1 (by rfl) ⟨172727, by rfl⟩) R345455
theorem R1639763 : Reach 1639763 := rs (se 1 (by rfl) ⟨1229822, by rfl⟩) R2459645
theorem R165503 : Reach 165503 := rs (se 1 (by rfl) ⟨124127, by rfl⟩) R248255
theorem R329345 : Reach 329345 := rs (se 2 (by rfl) ⟨123504, by rfl⟩) R247009
theorem R232703 : Reach 232703 := rs (se 1 (by rfl) ⟨174527, by rfl⟩) R349055
theorem R1609895 : Reach 1609895 := rs (se 1 (by rfl) ⟨1207421, by rfl⟩) R2414843
theorem R988841 : Reach 988841 := rs (se 2 (by rfl) ⟨370815, by rfl⟩) R741631
theorem R1218809 : Reach 1218809 := rs (se 2 (by rfl) ⟨457053, by rfl⟩) R914107
theorem R630949 : Reach 630949 := rs (se 4 (by rfl) ⟨59151, by rfl⟩) R118303
theorem R565613 : Reach 565613 := rs (se 3 (by rfl) ⟨106052, by rfl⟩) R212105
theorem R471359 : Reach 471359 := rs (se 1 (by rfl) ⟨353519, by rfl⟩) R707039
theorem R111719 : Reach 111719 := rs (se 1 (by rfl) ⟨83789, by rfl⟩) R167579
theorem R407375 : Reach 407375 := rs (se 1 (by rfl) ⟨305531, by rfl⟩) R611063
theorem R310817 : Reach 310817 := rs (se 2 (by rfl) ⟨116556, by rfl⟩) R233113
theorem R114863 : Reach 114863 := rs (se 1 (by rfl) ⟨86147, by rfl⟩) R172295
theorem R83359 : Reach 83359 := rs (se 1 (by rfl) ⟨62519, by rfl⟩) R125039
theorem R214771 : Reach 214771 := rs (se 1 (by rfl) ⟨161078, by rfl⟩) R322157
theorem R5362159 : Reach 5362159 := rs (se 1 (by rfl) ⟨4021619, by rfl⟩) R8043239
theorem R6181541 : Reach 6181541 := rs (se 4 (by rfl) ⟨579519, by rfl⟩) R1159039
theorem R546203 : Reach 546203 := rs (se 1 (by rfl) ⟨409652, by rfl⟩) R819305
theorem R186715 : Reach 186715 := rs (se 1 (by rfl) ⟨140036, by rfl⟩) R280073
theorem R417959 : Reach 417959 := rs (se 1 (by rfl) ⟨313469, by rfl⟩) R626939
theorem R320111 : Reach 320111 := rs (se 1 (by rfl) ⟨240083, by rfl⟩) R480167
theorem R92287 : Reach 92287 := rs (se 1 (by rfl) ⟨69215, by rfl⟩) R138431
theorem R322217 : Reach 322217 := rs (se 2 (by rfl) ⟨120831, by rfl⟩) R241663
theorem R2748239 : Reach 2748239 := rs (se 1 (by rfl) ⟨2061179, by rfl⟩) R4122359
theorem R1372069 : Reach 1372069 := rs (se 4 (by rfl) ⟨128631, by rfl⟩) R257263
theorem R159995 : Reach 159995 := rs (se 1 (by rfl) ⟨119996, by rfl⟩) R239993
theorem R2519423 : Reach 2519423 := rs (se 1 (by rfl) ⟨1889567, by rfl⟩) R3779135
theorem R63167 : Reach 63167 := rs (se 1 (by rfl) ⟨47375, by rfl⟩) R94751
theorem R3667805 : Reach 3667805 := rs (se 3 (by rfl) ⟨687713, by rfl⟩) R1375427
theorem R96935 : Reach 96935 := rs (se 1 (by rfl) ⟨72701, by rfl⟩) R145403
theorem R490859 : Reach 490859 := rs (se 1 (by rfl) ⟨368144, by rfl⟩) R736289
theorem R65023 : Reach 65023 := rs (se 1 (by rfl) ⟨48767, by rfl⟩) R97535
theorem R1408873 : Reach 1408873 := rs (se 2 (by rfl) ⟨528327, by rfl⟩) R1056655
theorem R364135 : Reach 364135 := rs (se 1 (by rfl) ⟨273101, by rfl⟩) R546203
theorem R659227 : Reach 659227 := rs (se 1 (by rfl) ⟨494420, by rfl⟩) R988841
theorem R7149545 : Reach 7149545 := rs (se 2 (by rfl) ⟨2681079, by rfl⟩) R5362159
theorem R106663 : Reach 106663 := rs (se 1 (by rfl) ⟨79997, by rfl⟩) R159995
theorem R1679615 : Reach 1679615 := rs (se 1 (by rfl) ⟨1259711, by rfl⟩) R2519423
theorem R74479 : Reach 74479 := rs (se 1 (by rfl) ⟨55859, by rfl⟩) R111719
theorem R271583 : Reach 271583 := rs (se 1 (by rfl) ⟨203687, by rfl⟩) R407375
theorem R7317701 : Reach 7317701 := rs (se 4 (by rfl) ⟨686034, by rfl⟩) R1372069
theorem R207211 : Reach 207211 := rs (se 1 (by rfl) ⟨155408, by rfl⟩) R310817
theorem R1878497 : Reach 1878497 := rs (se 2 (by rfl) ⟨704436, by rfl⟩) R1408873
theorem R306301 : Reach 306301 := rs (se 3 (by rfl) ⟨57431, by rfl⟩) R114863
theorem R1256957 : Reach 1256957 := rs (se 3 (by rfl) ⟨235679, by rfl⟩) R471359
theorem R1093175 : Reach 1093175 := rs (se 1 (by rfl) ⟨819881, by rfl⟩) R1639763
theorem R110335 : Reach 110335 := rs (se 1 (by rfl) ⟨82751, by rfl⟩) R165503
theorem R111145 : Reach 111145 := rs (se 2 (by rfl) ⟨41679, by rfl⟩) R83359
theorem R278639 : Reach 278639 := rs (se 1 (by rfl) ⟨208979, by rfl⟩) R417959
theorem R377075 : Reach 377075 := rs (se 1 (by rfl) ⟨282806, by rfl⟩) R565613
theorem R213407 : Reach 213407 := rs (se 1 (by rfl) ⟨160055, by rfl⟩) R320111
theorem R214811 : Reach 214811 := rs (se 1 (by rfl) ⟨161108, by rfl⟩) R322217
theorem R248953 : Reach 248953 := rs (se 2 (by rfl) ⟨93357, by rfl⟩) R186715
theorem R2445203 : Reach 2445203 := rs (se 1 (by rfl) ⟨1833902, by rfl⟩) R3667805
theorem R841265 : Reach 841265 := rs (se 2 (by rfl) ⟨315474, by rfl⟩) R630949
theorem R153535 : Reach 153535 := rs (se 1 (by rfl) ⟨115151, by rfl⟩) R230303
theorem R219563 : Reach 219563 := rs (se 1 (by rfl) ⟨164672, by rfl⟩) R329345
theorem R155135 : Reach 155135 := rs (se 1 (by rfl) ⟨116351, by rfl⟩) R232703
theorem R286361 : Reach 286361 := rs (se 2 (by rfl) ⟨107385, by rfl⟩) R214771
theorem R1073263 : Reach 1073263 := rs (se 1 (by rfl) ⟨804947, by rfl⟩) R1609895
theorem R123049 : Reach 123049 := rs (se 2 (by rfl) ⟨46143, by rfl⟩) R92287
theorem R4121027 : Reach 4121027 := rs (se 1 (by rfl) ⟨3090770, by rfl⟩) R6181541
theorem R812539 : Reach 812539 := rs (se 1 (by rfl) ⟨609404, by rfl⟩) R1218809
theorem R1832159 : Reach 1832159 := rs (se 1 (by rfl) ⟨1374119, by rfl⟩) R2748239
theorem R64623 : Reach 64623 := rs (se 1 (by rfl) ⟨48467, by rfl⟩) R96935
theorem R327239 : Reach 327239 := rs (se 1 (by rfl) ⟨245429, by rfl⟩) R490859
theorem R164065 : Reach 164065 := rs (se 2 (by rfl) ⟨61524, by rfl⟩) R123049
theorem R99305 : Reach 99305 := rs (se 2 (by rfl) ⟨37239, by rfl⟩) R74479
theorem R1083385 : Reach 1083385 := rs (se 2 (by rfl) ⟨406269, by rfl⟩) R812539
theorem R560843 : Reach 560843 := rs (se 1 (by rfl) ⟨420632, by rfl⟩) R841265
theorem R331937 : Reach 331937 := rs (se 2 (by rfl) ⟨124476, by rfl⟩) R248953
theorem R103423 : Reach 103423 := rs (se 1 (by rfl) ⟨77567, by rfl⟩) R155135
theorem R1119743 : Reach 1119743 := rs (se 1 (by rfl) ⟨839807, by rfl⟩) R1679615
theorem R1252331 : Reach 1252331 := rs (se 1 (by rfl) ⟨939248, by rfl⟩) R1878497
theorem R728783 : Reach 728783 := rs (se 1 (by rfl) ⟨546587, by rfl⟩) R1093175
theorem R204713 : Reach 204713 := rs (se 2 (by rfl) ⟨76767, by rfl⟩) R153535
theorem R1221439 : Reach 1221439 := rs (se 1 (by rfl) ⟨916079, by rfl⟩) R1832159
theorem R142217 : Reach 142217 := rs (se 2 (by rfl) ⟨53331, by rfl⟩) R106663
theorem R142271 : Reach 142271 := rs (se 1 (by rfl) ⟨106703, by rfl⟩) R213407
theorem R143207 : Reach 143207 := rs (se 1 (by rfl) ⟨107405, by rfl⟩) R214811
theorem R276281 : Reach 276281 := rs (se 2 (by rfl) ⟨103605, by rfl⟩) R207211
theorem R4766363 : Reach 4766363 := rs (se 1 (by rfl) ⟨3574772, by rfl⟩) R7149545
theorem R408401 : Reach 408401 := rs (se 2 (by rfl) ⟨153150, by rfl⟩) R306301
theorem R146375 : Reach 146375 := rs (se 1 (by rfl) ⟨109781, by rfl⟩) R219563
theorem R147113 : Reach 147113 := rs (se 2 (by rfl) ⟨55167, by rfl⟩) R110335
theorem R148193 : Reach 148193 := rs (se 2 (by rfl) ⟨55572, by rfl⟩) R111145
theorem R181055 : Reach 181055 := rs (se 1 (by rfl) ⟨135791, by rfl⟩) R271583
theorem R837971 : Reach 837971 := rs (se 1 (by rfl) ⟨628478, by rfl⟩) R1256957
theorem R218159 : Reach 218159 := rs (se 1 (by rfl) ⟨163619, by rfl⟩) R327239
theorem R185759 : Reach 185759 := rs (se 1 (by rfl) ⟨139319, by rfl⟩) R278639
theorem R1431017 : Reach 1431017 := rs (se 2 (by rfl) ⟨536631, by rfl⟩) R1073263
theorem R251383 : Reach 251383 := rs (se 1 (by rfl) ⟨188537, by rfl⟩) R377075
theorem R1630135 : Reach 1630135 := rs (se 1 (by rfl) ⟨1222601, by rfl⟩) R2445203
theorem R485513 : Reach 485513 := rs (se 2 (by rfl) ⟨182067, by rfl⟩) R364135
theorem R878969 : Reach 878969 := rs (se 2 (by rfl) ⟨329613, by rfl⟩) R659227
theorem R190907 : Reach 190907 := rs (se 1 (by rfl) ⟨143180, by rfl⟩) R286361
theorem R2747351 : Reach 2747351 := rs (se 1 (by rfl) ⟨2060513, by rfl⟩) R4121027
theorem R4878467 : Reach 4878467 := rs (se 1 (by rfl) ⟨3658850, by rfl⟩) R7317701
theorem R98795 : Reach 98795 := rs (se 1 (by rfl) ⟨74096, by rfl⟩) R148193
theorem R66203 : Reach 66203 := rs (se 1 (by rfl) ⟨49652, by rfl⟩) R99305
theorem R558647 : Reach 558647 := rs (se 1 (by rfl) ⟨418985, by rfl⟩) R837971
theorem R1444513 : Reach 1444513 := rs (se 2 (by rfl) ⟨541692, by rfl⟩) R1083385
theorem R954011 : Reach 954011 := rs (se 1 (by rfl) ⟨715508, by rfl⟩) R1431017
theorem R136475 : Reach 136475 := rs (se 1 (by rfl) ⟨102356, by rfl⟩) R204713
theorem R137897 : Reach 137897 := rs (se 2 (by rfl) ⟨51711, by rfl⟩) R103423
theorem R335177 : Reach 335177 := rs (se 2 (by rfl) ⟨125691, by rfl⟩) R251383
theorem R3252311 : Reach 3252311 := rs (se 1 (by rfl) ⟨2439233, by rfl⟩) R4878467
theorem R272267 : Reach 272267 := rs (se 1 (by rfl) ⟨204200, by rfl⟩) R408401
theorem R2173513 : Reach 2173513 := rs (se 2 (by rfl) ⟨815067, by rfl⟩) R1630135
theorem R373895 : Reach 373895 := rs (se 1 (by rfl) ⟨280421, by rfl⟩) R560843
theorem R145439 : Reach 145439 := rs (se 1 (by rfl) ⟨109079, by rfl⟩) R218159
theorem R834887 : Reach 834887 := rs (se 1 (by rfl) ⟨626165, by rfl⟩) R1252331
theorem R2343917 : Reach 2343917 := rs (se 3 (by rfl) ⟨439484, by rfl⟩) R878969
theorem R184187 : Reach 184187 := rs (se 1 (by rfl) ⟨138140, by rfl⟩) R276281
theorem R218753 : Reach 218753 := rs (se 2 (by rfl) ⟨82032, by rfl⟩) R164065
theorem R120703 : Reach 120703 := rs (se 1 (by rfl) ⟨90527, by rfl⟩) R181055
theorem R1628585 : Reach 1628585 := rs (se 2 (by rfl) ⟨610719, by rfl⟩) R1221439
theorem R221291 : Reach 221291 := rs (se 1 (by rfl) ⟨165968, by rfl⟩) R331937
theorem R123839 : Reach 123839 := rs (se 1 (by rfl) ⟨92879, by rfl⟩) R185759
theorem R746495 : Reach 746495 := rs (se 1 (by rfl) ⟨559871, by rfl⟩) R1119743
theorem R485855 : Reach 485855 := rs (se 1 (by rfl) ⟨364391, by rfl⟩) R728783
theorem R323675 : Reach 323675 := rs (se 1 (by rfl) ⟨242756, by rfl⟩) R485513
theorem R127271 : Reach 127271 := rs (se 1 (by rfl) ⟨95453, by rfl⟩) R190907
theorem R94811 : Reach 94811 := rs (se 1 (by rfl) ⟨71108, by rfl⟩) R142217
theorem R94847 : Reach 94847 := rs (se 1 (by rfl) ⟨71135, by rfl⟩) R142271
theorem R1831567 : Reach 1831567 := rs (se 1 (by rfl) ⟨1373675, by rfl⟩) R2747351
theorem R95471 : Reach 95471 := rs (se 1 (by rfl) ⟨71603, by rfl⟩) R143207
theorem R3177575 : Reach 3177575 := rs (se 1 (by rfl) ⟨2383181, by rfl⟩) R4766363
theorem R97583 : Reach 97583 := rs (se 1 (by rfl) ⟨73187, by rfl⟩) R146375
theorem R98075 : Reach 98075 := rs (se 1 (by rfl) ⟨73556, by rfl⟩) R147113
theorem R65863 : Reach 65863 := rs (se 1 (by rfl) ⟨49397, by rfl⟩) R98795
theorem R1085723 : Reach 1085723 := rs (se 1 (by rfl) ⟨814292, by rfl⟩) R1628585
theorem R2168207 : Reach 2168207 := rs (se 1 (by rfl) ⟨1626155, by rfl⟩) R3252311
theorem R497663 : Reach 497663 := rs (se 1 (by rfl) ⟨373247, by rfl⟩) R746495
theorem R339389 : Reach 339389 := rs (se 3 (by rfl) ⟨63635, by rfl⟩) R127271
theorem R372431 : Reach 372431 := rs (se 1 (by rfl) ⟨279323, by rfl⟩) R558647
theorem R636007 : Reach 636007 := rs (se 1 (by rfl) ⟨477005, by rfl⟩) R954011
theorem R2898017 : Reach 2898017 := rs (se 2 (by rfl) ⟨1086756, by rfl⟩) R2173513
theorem R145835 : Reach 145835 := rs (se 1 (by rfl) ⟨109376, by rfl⟩) R218753
theorem R147527 : Reach 147527 := rs (se 1 (by rfl) ⟨110645, by rfl⟩) R221291
theorem R82559 : Reach 82559 := rs (se 1 (by rfl) ⟨61919, by rfl⟩) R123839
theorem R2442089 : Reach 2442089 := rs (se 2 (by rfl) ⟨915783, by rfl⟩) R1831567
theorem R181511 : Reach 181511 := rs (se 1 (by rfl) ⟨136133, by rfl⟩) R272267
theorem R215783 : Reach 215783 := rs (se 1 (by rfl) ⟨161837, by rfl⟩) R323675
theorem R249263 : Reach 249263 := rs (se 1 (by rfl) ⟨186947, by rfl⟩) R373895
theorem R2118383 : Reach 2118383 := rs (se 1 (by rfl) ⟨1588787, by rfl⟩) R3177575
theorem R1562611 : Reach 1562611 := rs (se 1 (by rfl) ⟨1171958, by rfl⟩) R2343917
theorem R122791 : Reach 122791 := rs (se 1 (by rfl) ⟨92093, by rfl⟩) R184187
theorem R90983 : Reach 90983 := rs (se 1 (by rfl) ⟨68237, by rfl⟩) R136475
theorem R1926017 : Reach 1926017 := rs (se 2 (by rfl) ⟨722256, by rfl⟩) R1444513
theorem R91931 : Reach 91931 := rs (se 1 (by rfl) ⟨68948, by rfl⟩) R137897
theorem R223451 : Reach 223451 := rs (se 1 (by rfl) ⟨167588, by rfl⟩) R335177
theorem R323903 : Reach 323903 := rs (se 1 (by rfl) ⟨242927, by rfl⟩) R485855
theorem R160937 : Reach 160937 := rs (se 2 (by rfl) ⟨60351, by rfl⟩) R120703
theorem R63207 : Reach 63207 := rs (se 1 (by rfl) ⟨47405, by rfl⟩) R94811
theorem R63231 : Reach 63231 := rs (se 1 (by rfl) ⟨47423, by rfl⟩) R94847
theorem R63647 : Reach 63647 := rs (se 1 (by rfl) ⟨47735, by rfl⟩) R95471
theorem R96959 : Reach 96959 := rs (se 1 (by rfl) ⟨72719, by rfl⟩) R145439
theorem R65055 : Reach 65055 := rs (se 1 (by rfl) ⟨48791, by rfl⟩) R97583
theorem R556591 : Reach 556591 := rs (se 1 (by rfl) ⟨417443, by rfl⟩) R834887
theorem R65383 : Reach 65383 := rs (se 1 (by rfl) ⟨49037, by rfl⟩) R98075
theorem R98351 : Reach 98351 := rs (se 1 (by rfl) ⟨73763, by rfl⟩) R147527
theorem R166175 : Reach 166175 := rs (se 1 (by rfl) ⟨124631, by rfl⟩) R249263
theorem R723815 : Reach 723815 := rs (se 1 (by rfl) ⟨542861, by rfl⟩) R1085723
theorem R1412255 : Reach 1412255 := rs (se 1 (by rfl) ⟨1059191, by rfl⟩) R2118383
theorem R1445471 : Reach 1445471 := rs (se 1 (by rfl) ⟨1084103, by rfl⟩) R2168207
theorem R331775 : Reach 331775 := rs (se 1 (by rfl) ⟨248831, by rfl⟩) R497663
theorem R1284011 : Reach 1284011 := rs (se 1 (by rfl) ⟨963008, by rfl⟩) R1926017
theorem R107291 : Reach 107291 := rs (se 1 (by rfl) ⟨80468, by rfl⟩) R160937
theorem R143855 : Reach 143855 := rs (se 1 (by rfl) ⟨107891, by rfl⟩) R215783
theorem R242621 : Reach 242621 := rs (se 3 (by rfl) ⟨45491, by rfl⟩) R90983
theorem R245149 : Reach 245149 := rs (se 3 (by rfl) ⟨45965, by rfl⟩) R91931
theorem R148967 : Reach 148967 := rs (se 1 (by rfl) ⟨111725, by rfl⟩) R223451
theorem R248287 : Reach 248287 := rs (se 1 (by rfl) ⟨186215, by rfl⟩) R372431
theorem R2083481 : Reach 2083481 := rs (se 2 (by rfl) ⟨781305, by rfl⟩) R1562611
theorem R215935 : Reach 215935 := rs (se 1 (by rfl) ⟨161951, by rfl⟩) R323903
theorem R742121 : Reach 742121 := rs (se 2 (by rfl) ⟨278295, by rfl⟩) R556591
theorem R1628059 : Reach 1628059 := rs (se 1 (by rfl) ⟨1221044, by rfl⟩) R2442089
theorem R121007 : Reach 121007 := rs (se 1 (by rfl) ⟨90755, by rfl⟩) R181511
theorem R220157 : Reach 220157 := rs (se 3 (by rfl) ⟨41279, by rfl⟩) R82559
theorem R848009 : Reach 848009 := rs (se 2 (by rfl) ⟨318003, by rfl⟩) R636007
theorem R226259 : Reach 226259 := rs (se 1 (by rfl) ⟨169694, by rfl⟩) R339389
theorem R1932011 : Reach 1932011 := rs (se 1 (by rfl) ⟨1449008, by rfl⟩) R2898017
theorem R97223 : Reach 97223 := rs (se 1 (by rfl) ⟨72917, by rfl⟩) R145835
theorem R64639 : Reach 64639 := rs (se 1 (by rfl) ⟨48479, by rfl⟩) R96959
theorem R163721 : Reach 163721 := rs (se 2 (by rfl) ⟨61395, by rfl⟩) R122791
theorem R65567 : Reach 65567 := rs (se 1 (by rfl) ⟨49175, by rfl⟩) R98351
theorem R99311 : Reach 99311 := rs (se 1 (by rfl) ⟨74483, by rfl⟩) R148967
theorem R494747 : Reach 494747 := rs (se 1 (by rfl) ⟨371060, by rfl⟩) R742121
theorem R331049 : Reach 331049 := rs (se 2 (by rfl) ⟨124143, by rfl⟩) R248287
theorem R856007 : Reach 856007 := rs (se 1 (by rfl) ⟨642005, by rfl⟩) R1284011
theorem R1151653 : Reach 1151653 := rs (se 4 (by rfl) ⟨107967, by rfl⟩) R215935
theorem R71527 : Reach 71527 := rs (se 1 (by rfl) ⟨53645, by rfl⟩) R107291
theorem R2170745 : Reach 2170745 := rs (se 2 (by rfl) ⟨814029, by rfl⟩) R1628059
theorem R565339 : Reach 565339 := rs (se 1 (by rfl) ⟨424004, by rfl⟩) R848009
theorem R1288007 : Reach 1288007 := rs (se 1 (by rfl) ⟨966005, by rfl⟩) R1932011
theorem R109147 : Reach 109147 := rs (se 1 (by rfl) ⟨81860, by rfl⟩) R163721
theorem R110783 : Reach 110783 := rs (se 1 (by rfl) ⟨83087, by rfl⟩) R166175
theorem R1388987 : Reach 1388987 := rs (se 1 (by rfl) ⟨1041740, by rfl⟩) R2083481
theorem R963647 : Reach 963647 := rs (se 1 (by rfl) ⟨722735, by rfl⟩) R1445471
theorem R80671 : Reach 80671 := rs (se 1 (by rfl) ⟨60503, by rfl⟩) R121007
theorem R146771 : Reach 146771 := rs (se 1 (by rfl) ⟨110078, by rfl⟩) R220157
theorem R150839 : Reach 150839 := rs (se 1 (by rfl) ⟨113129, by rfl⟩) R226259
theorem R482543 : Reach 482543 := rs (se 1 (by rfl) ⟨361907, by rfl⟩) R723815
theorem R941503 : Reach 941503 := rs (se 1 (by rfl) ⟨706127, by rfl⟩) R1412255
theorem R221183 : Reach 221183 := rs (se 1 (by rfl) ⟨165887, by rfl⟩) R331775
theorem R1307461 : Reach 1307461 := rs (se 4 (by rfl) ⟨122574, by rfl⟩) R245149
theorem R95903 : Reach 95903 := rs (se 1 (by rfl) ⟨71927, by rfl⟩) R143855
theorem R161747 : Reach 161747 := rs (se 1 (by rfl) ⟨121310, by rfl⟩) R242621
theorem R64815 : Reach 64815 := rs (se 1 (by rfl) ⟨48611, by rfl⟩) R97223
theorem R753785 : Reach 753785 := rs (se 2 (by rfl) ⟨282669, by rfl⟩) R565339
theorem R66207 : Reach 66207 := rs (se 1 (by rfl) ⟨49655, by rfl⟩) R99311
theorem R329831 : Reach 329831 := rs (se 1 (by rfl) ⟨247373, by rfl⟩) R494747
theorem R100559 : Reach 100559 := rs (se 1 (by rfl) ⟨75419, by rfl⟩) R150839
theorem R1447163 : Reach 1447163 := rs (se 1 (by rfl) ⟨1085372, by rfl⟩) R2170745
theorem R1743281 : Reach 1743281 := rs (se 2 (by rfl) ⟨653730, by rfl⟩) R1307461
theorem R858671 : Reach 858671 := rs (se 1 (by rfl) ⟨644003, by rfl⟩) R1288007
theorem R73855 : Reach 73855 := rs (se 1 (by rfl) ⟨55391, by rfl⟩) R110783
theorem R925991 : Reach 925991 := rs (se 1 (by rfl) ⟨694493, by rfl⟩) R1388987
theorem R107561 : Reach 107561 := rs (se 2 (by rfl) ⟨40335, by rfl⟩) R80671
theorem R107831 : Reach 107831 := rs (se 1 (by rfl) ⟨80873, by rfl⟩) R161747
theorem R1255337 : Reach 1255337 := rs (se 2 (by rfl) ⟨470751, by rfl⟩) R941503
theorem R570671 : Reach 570671 := rs (se 1 (by rfl) ⟨428003, by rfl⟩) R856007
theorem R145529 : Reach 145529 := rs (se 2 (by rfl) ⟨54573, by rfl⟩) R109147
theorem R147455 : Reach 147455 := rs (se 1 (by rfl) ⟨110591, by rfl⟩) R221183
theorem R642431 : Reach 642431 := rs (se 1 (by rfl) ⟨481823, by rfl⟩) R963647
theorem R220699 : Reach 220699 := rs (se 1 (by rfl) ⟨165524, by rfl⟩) R331049
theorem R321695 : Reach 321695 := rs (se 1 (by rfl) ⟨241271, by rfl⟩) R482543
theorem R1535537 : Reach 1535537 := rs (se 2 (by rfl) ⟨575826, by rfl⟩) R1151653
theorem R95369 : Reach 95369 := rs (se 2 (by rfl) ⟨35763, by rfl⟩) R71527
theorem R63935 : Reach 63935 := rs (se 1 (by rfl) ⟨47951, by rfl⟩) R95903
theorem R97847 : Reach 97847 := rs (se 1 (by rfl) ⟨73385, by rfl⟩) R146771
theorem R393893 : Reach 393893 := rs (se 4 (by rfl) ⟨36927, by rfl⟩) R73855
theorem R67039 : Reach 67039 := rs (se 1 (by rfl) ⟨50279, by rfl⟩) R100559
theorem R428287 : Reach 428287 := rs (se 1 (by rfl) ⟨321215, by rfl⟩) R642431
theorem R71707 : Reach 71707 := rs (se 1 (by rfl) ⟨53780, by rfl⟩) R107561
theorem R71887 : Reach 71887 := rs (se 1 (by rfl) ⟨53915, by rfl⟩) R107831
theorem R1023691 : Reach 1023691 := rs (se 1 (by rfl) ⟨767768, by rfl⟩) R1535537
theorem R502523 : Reach 502523 := rs (se 1 (by rfl) ⟨376892, by rfl⟩) R753785
theorem R964775 : Reach 964775 := rs (se 1 (by rfl) ⟨723581, by rfl⟩) R1447163
theorem R1162187 : Reach 1162187 := rs (se 1 (by rfl) ⟨871640, by rfl⟩) R1743281
theorem R572447 : Reach 572447 := rs (se 1 (by rfl) ⟨429335, by rfl⟩) R858671
theorem R836891 : Reach 836891 := rs (se 1 (by rfl) ⟨627668, by rfl⟩) R1255337
theorem R214463 : Reach 214463 := rs (se 1 (by rfl) ⟨160847, by rfl⟩) R321695
theorem R380447 : Reach 380447 := rs (se 1 (by rfl) ⟨285335, by rfl⟩) R570671
theorem R219887 : Reach 219887 := rs (se 1 (by rfl) ⟨164915, by rfl⟩) R329831
theorem R617327 : Reach 617327 := rs (se 1 (by rfl) ⟨462995, by rfl⟩) R925991
theorem R63579 : Reach 63579 := rs (se 1 (by rfl) ⟨47684, by rfl⟩) R95369
theorem R97019 : Reach 97019 := rs (se 1 (by rfl) ⟨72764, by rfl⟩) R145529
theorem R294265 : Reach 294265 := rs (se 2 (by rfl) ⟨110349, by rfl⟩) R220699
theorem R65231 : Reach 65231 := rs (se 1 (by rfl) ⟨48923, by rfl⟩) R97847
theorem R98303 : Reach 98303 := rs (se 1 (by rfl) ⟨73727, by rfl⟩) R147455
theorem R262595 : Reach 262595 := rs (se 1 (by rfl) ⟨196946, by rfl⟩) R393893
theorem R557927 : Reach 557927 := rs (se 1 (by rfl) ⟨418445, by rfl⟩) R836891
theorem R65535 : Reach 65535 := rs (se 1 (by rfl) ⟨49151, by rfl⟩) R98303
theorem R335015 : Reach 335015 := rs (se 1 (by rfl) ⟨251261, by rfl⟩) R502523
theorem R142975 : Reach 142975 := rs (se 1 (by rfl) ⟨107231, by rfl⟩) R214463
theorem R571049 : Reach 571049 := rs (se 2 (by rfl) ⟨214143, by rfl⟩) R428287
theorem R146591 : Reach 146591 := rs (se 1 (by rfl) ⟨109943, by rfl⟩) R219887
theorem R411551 : Reach 411551 := rs (se 1 (by rfl) ⟨308663, by rfl⟩) R617327
theorem R643183 : Reach 643183 := rs (se 1 (by rfl) ⟨482387, by rfl⟩) R964775
theorem R774791 : Reach 774791 := rs (se 1 (by rfl) ⟨581093, by rfl⟩) R1162187
theorem R381631 : Reach 381631 := rs (se 1 (by rfl) ⟨286223, by rfl⟩) R572447
theorem R1364921 : Reach 1364921 := rs (se 2 (by rfl) ⟨511845, by rfl⟩) R1023691
theorem R253631 : Reach 253631 := rs (se 1 (by rfl) ⟨190223, by rfl⟩) R380447
theorem R95609 : Reach 95609 := rs (se 2 (by rfl) ⟨35853, by rfl⟩) R71707
theorem R95849 : Reach 95849 := rs (se 2 (by rfl) ⟨35943, by rfl⟩) R71887
theorem R392353 : Reach 392353 := rs (se 2 (by rfl) ⟨147132, by rfl⟩) R294265
theorem R64679 : Reach 64679 := rs (se 1 (by rfl) ⟨48509, by rfl⟩) R97019
theorem R169087 : Reach 169087 := rs (se 1 (by rfl) ⟨126815, by rfl⟩) R253631
theorem R172477 : Reach 172477 := rs (se 3 (by rfl) ⟨32339, by rfl⟩) R64679
theorem R762533 : Reach 762533 := rs (se 4 (by rfl) ⟨71487, by rfl⟩) R142975
theorem R175063 : Reach 175063 := rs (se 1 (by rfl) ⟨131297, by rfl⟩) R262595
theorem R371951 : Reach 371951 := rs (se 1 (by rfl) ⟨278963, by rfl⟩) R557927
theorem R274367 : Reach 274367 := rs (se 1 (by rfl) ⟨205775, by rfl⟩) R411551
theorem R508841 : Reach 508841 := rs (se 2 (by rfl) ⟨190815, by rfl⟩) R381631
theorem R380699 : Reach 380699 := rs (se 1 (by rfl) ⟨285524, by rfl⟩) R571049
theorem R13721237 : Reach 13721237 := rs (se 6 (by rfl) ⟨321591, by rfl⟩) R643183
theorem R516527 : Reach 516527 := rs (se 1 (by rfl) ⟨387395, by rfl⟩) R774791
theorem R909947 : Reach 909947 := rs (se 1 (by rfl) ⟨682460, by rfl⟩) R1364921
theorem R223343 : Reach 223343 := rs (se 1 (by rfl) ⟨167507, by rfl⟩) R335015
theorem R2092549 : Reach 2092549 := rs (se 4 (by rfl) ⟨196176, by rfl⟩) R392353
theorem R63739 : Reach 63739 := rs (se 1 (by rfl) ⟨47804, by rfl⟩) R95609
theorem R63899 : Reach 63899 := rs (se 1 (by rfl) ⟨47924, by rfl⟩) R95849
theorem R97727 : Reach 97727 := rs (se 1 (by rfl) ⟨73295, by rfl⟩) R146591
theorem R229969 : Reach 229969 := rs (se 2 (by rfl) ⟨86238, by rfl⟩) R172477
theorem R233417 : Reach 233417 := rs (se 2 (by rfl) ⟨87531, by rfl⟩) R175063
theorem R2790065 : Reach 2790065 := rs (se 2 (by rfl) ⟨1046274, by rfl⟩) R2092549
theorem R9147491 : Reach 9147491 := rs (se 1 (by rfl) ⟨6860618, by rfl⟩) R13721237
theorem R339227 : Reach 339227 := rs (se 1 (by rfl) ⟨254420, by rfl⟩) R508841
theorem R344351 : Reach 344351 := rs (se 1 (by rfl) ⟨258263, by rfl⟩) R516527
theorem R606631 : Reach 606631 := rs (se 1 (by rfl) ⟨454973, by rfl⟩) R909947
theorem R508355 : Reach 508355 := rs (se 1 (by rfl) ⟨381266, by rfl⟩) R762533
theorem R148895 : Reach 148895 := rs (se 1 (by rfl) ⟨111671, by rfl⟩) R223343
theorem R247967 : Reach 247967 := rs (se 1 (by rfl) ⟨185975, by rfl⟩) R371951
theorem R182911 : Reach 182911 := rs (se 1 (by rfl) ⟨137183, by rfl⟩) R274367
theorem R253799 : Reach 253799 := rs (se 1 (by rfl) ⟨190349, by rfl⟩) R380699
theorem R225449 : Reach 225449 := rs (se 2 (by rfl) ⟨84543, by rfl⟩) R169087
theorem R65151 : Reach 65151 := rs (se 1 (by rfl) ⟨48863, by rfl⟩) R97727
theorem R229567 : Reach 229567 := rs (se 1 (by rfl) ⟨172175, by rfl⟩) R344351
theorem R99263 : Reach 99263 := rs (se 1 (by rfl) ⟨74447, by rfl⟩) R148895
theorem R165311 : Reach 165311 := rs (se 1 (by rfl) ⟨123983, by rfl⟩) R247967
theorem R6098327 : Reach 6098327 := rs (se 1 (by rfl) ⟨4573745, by rfl⟩) R9147491
theorem R169199 : Reach 169199 := rs (se 1 (by rfl) ⟨126899, by rfl⟩) R253799
theorem R338903 : Reach 338903 := rs (se 1 (by rfl) ⟨254177, by rfl⟩) R508355
theorem R306625 : Reach 306625 := rs (se 2 (by rfl) ⟨114984, by rfl⟩) R229969
theorem R243881 : Reach 243881 := rs (se 2 (by rfl) ⟨91455, by rfl⟩) R182911
theorem R150299 : Reach 150299 := rs (se 1 (by rfl) ⟨112724, by rfl⟩) R225449
theorem R808841 : Reach 808841 := rs (se 2 (by rfl) ⟨303315, by rfl⟩) R606631
theorem R155611 : Reach 155611 := rs (se 1 (by rfl) ⟨116708, by rfl⟩) R233417
theorem R1860043 : Reach 1860043 := rs (se 1 (by rfl) ⟨1395032, by rfl⟩) R2790065
theorem R226151 : Reach 226151 := rs (se 1 (by rfl) ⟨169613, by rfl⟩) R339227
theorem R66175 : Reach 66175 := rs (se 1 (by rfl) ⟨49631, by rfl⟩) R99263
theorem R100199 : Reach 100199 := rs (se 1 (by rfl) ⟨75149, by rfl⟩) R150299
theorem R4065551 : Reach 4065551 := rs (se 1 (by rfl) ⟨3049163, by rfl⟩) R6098327
theorem R207481 : Reach 207481 := rs (se 2 (by rfl) ⟨77805, by rfl⟩) R155611
theorem R306089 : Reach 306089 := rs (se 2 (by rfl) ⟨114783, by rfl⟩) R229567
theorem R110207 : Reach 110207 := rs (se 1 (by rfl) ⟨82655, by rfl⟩) R165311
theorem R112799 : Reach 112799 := rs (se 1 (by rfl) ⟨84599, by rfl⟩) R169199
theorem R539227 : Reach 539227 := rs (se 1 (by rfl) ⟨404420, by rfl⟩) R808841
theorem R408833 : Reach 408833 := rs (se 2 (by rfl) ⟨153312, by rfl⟩) R306625
theorem R150767 : Reach 150767 := rs (se 1 (by rfl) ⟨113075, by rfl⟩) R226151
theorem R2480057 : Reach 2480057 := rs (se 2 (by rfl) ⟨930021, by rfl⟩) R1860043
theorem R225935 : Reach 225935 := rs (se 1 (by rfl) ⟨169451, by rfl⟩) R338903
theorem R162587 : Reach 162587 := rs (se 1 (by rfl) ⟨121940, by rfl⟩) R243881
theorem R66799 : Reach 66799 := rs (se 1 (by rfl) ⟨50099, by rfl⟩) R100199
theorem R100511 : Reach 100511 := rs (se 1 (by rfl) ⟨75383, by rfl⟩) R150767
theorem R204059 : Reach 204059 := rs (se 1 (by rfl) ⟨153044, by rfl⟩) R306089
theorem R73471 : Reach 73471 := rs (se 1 (by rfl) ⟨55103, by rfl⟩) R110207
theorem R75199 : Reach 75199 := rs (se 1 (by rfl) ⟨56399, by rfl⟩) R112799
theorem R108391 : Reach 108391 := rs (se 1 (by rfl) ⟨81293, by rfl⟩) R162587
theorem R272555 : Reach 272555 := rs (se 1 (by rfl) ⟨204416, by rfl⟩) R408833
theorem R276641 : Reach 276641 := rs (se 2 (by rfl) ⟨103740, by rfl⟩) R207481
theorem R1653371 : Reach 1653371 := rs (se 1 (by rfl) ⟨1240028, by rfl⟩) R2480057
theorem R150623 : Reach 150623 := rs (se 1 (by rfl) ⟨112967, by rfl⟩) R225935
theorem R2710367 : Reach 2710367 := rs (se 1 (by rfl) ⟨2032775, by rfl⟩) R4065551
theorem R718969 : Reach 718969 := rs (se 2 (by rfl) ⟨269613, by rfl⟩) R539227
theorem R67007 : Reach 67007 := rs (se 1 (by rfl) ⟨50255, by rfl⟩) R100511
theorem R100265 : Reach 100265 := rs (se 2 (by rfl) ⟨37599, by rfl⟩) R75199
theorem R100415 : Reach 100415 := rs (se 1 (by rfl) ⟨75311, by rfl⟩) R150623
theorem R1806911 : Reach 1806911 := rs (se 1 (by rfl) ⟨1355183, by rfl⟩) R2710367
theorem R136039 : Reach 136039 := rs (se 1 (by rfl) ⟨102029, by rfl⟩) R204059
theorem R958625 : Reach 958625 := rs (se 2 (by rfl) ⟨359484, by rfl⟩) R718969
theorem R144521 : Reach 144521 := rs (se 2 (by rfl) ⟨54195, by rfl⟩) R108391
theorem R181703 : Reach 181703 := rs (se 1 (by rfl) ⟨136277, by rfl⟩) R272555
theorem R184427 : Reach 184427 := rs (se 1 (by rfl) ⟨138320, by rfl⟩) R276641
theorem R1102247 : Reach 1102247 := rs (se 1 (by rfl) ⟨826685, by rfl⟩) R1653371
theorem R97961 : Reach 97961 := rs (se 2 (by rfl) ⟨36735, by rfl⟩) R73471
theorem R66843 : Reach 66843 := rs (se 1 (by rfl) ⟨50132, by rfl⟩) R100265
theorem R66943 : Reach 66943 := rs (se 1 (by rfl) ⟨50207, by rfl⟩) R100415
theorem R734831 : Reach 734831 := rs (se 1 (by rfl) ⟨551123, by rfl⟩) R1102247
theorem R639083 : Reach 639083 := rs (se 1 (by rfl) ⟨479312, by rfl⟩) R958625
theorem R181385 : Reach 181385 := rs (se 2 (by rfl) ⟨68019, by rfl⟩) R136039
theorem R122951 : Reach 122951 := rs (se 1 (by rfl) ⟨92213, by rfl⟩) R184427
theorem R1204607 : Reach 1204607 := rs (se 1 (by rfl) ⟨903455, by rfl⟩) R1806911
theorem R484541 : Reach 484541 := rs (se 3 (by rfl) ⟨90851, by rfl⟩) R181703
theorem R96347 : Reach 96347 := rs (se 1 (by rfl) ⟨72260, by rfl⟩) R144521
theorem R65307 : Reach 65307 := rs (se 1 (by rfl) ⟨48980, by rfl⟩) R97961
theorem R426055 : Reach 426055 := rs (se 1 (by rfl) ⟨319541, by rfl⟩) R639083
theorem R81967 : Reach 81967 := rs (se 1 (by rfl) ⟨61475, by rfl⟩) R122951
theorem R803071 : Reach 803071 := rs (se 1 (by rfl) ⟨602303, by rfl⟩) R1204607
theorem R120923 : Reach 120923 := rs (se 1 (by rfl) ⟨90692, by rfl⟩) R181385
theorem R323027 : Reach 323027 := rs (se 1 (by rfl) ⟨242270, by rfl⟩) R484541
theorem R489887 : Reach 489887 := rs (se 1 (by rfl) ⟨367415, by rfl⟩) R734831
theorem R64231 : Reach 64231 := rs (se 1 (by rfl) ⟨48173, by rfl⟩) R96347
theorem R109289 : Reach 109289 := rs (se 2 (by rfl) ⟨40983, by rfl⟩) R81967
theorem R568073 : Reach 568073 := rs (se 2 (by rfl) ⟨213027, by rfl⟩) R426055
theorem R80615 : Reach 80615 := rs (se 1 (by rfl) ⟨60461, by rfl⟩) R120923
theorem R215351 : Reach 215351 := rs (se 1 (by rfl) ⟨161513, by rfl⟩) R323027
theorem R1070761 : Reach 1070761 := rs (se 2 (by rfl) ⟨401535, by rfl⟩) R803071
theorem R326591 : Reach 326591 := rs (se 1 (by rfl) ⟨244943, by rfl⟩) R489887
theorem R72859 : Reach 72859 := rs (se 1 (by rfl) ⟨54644, by rfl⟩) R109289
theorem R143567 : Reach 143567 := rs (se 1 (by rfl) ⟨107675, by rfl⟩) R215351
theorem R378715 : Reach 378715 := rs (se 1 (by rfl) ⟨284036, by rfl⟩) R568073
theorem R214973 : Reach 214973 := rs (se 3 (by rfl) ⟨40307, by rfl⟩) R80615
theorem R1427681 : Reach 1427681 := rs (se 2 (by rfl) ⟨535380, by rfl⟩) R1070761
theorem R217727 : Reach 217727 := rs (se 1 (by rfl) ⟨163295, by rfl⟩) R326591
theorem R951787 : Reach 951787 := rs (se 1 (by rfl) ⟨713840, by rfl⟩) R1427681
theorem R143315 : Reach 143315 := rs (se 1 (by rfl) ⟨107486, by rfl⟩) R214973
theorem R504953 : Reach 504953 := rs (se 2 (by rfl) ⟨189357, by rfl⟩) R378715
theorem R145151 : Reach 145151 := rs (se 1 (by rfl) ⟨108863, by rfl⟩) R217727
theorem R95711 : Reach 95711 := rs (se 1 (by rfl) ⟨71783, by rfl⟩) R143567
theorem R97145 : Reach 97145 := rs (se 2 (by rfl) ⟨36429, by rfl⟩) R72859
theorem R336635 : Reach 336635 := rs (se 1 (by rfl) ⟨252476, by rfl⟩) R504953
theorem R1269049 : Reach 1269049 := rs (se 2 (by rfl) ⟨475893, by rfl⟩) R951787
theorem R95543 : Reach 95543 := rs (se 1 (by rfl) ⟨71657, by rfl⟩) R143315
theorem R63807 : Reach 63807 := rs (se 1 (by rfl) ⟨47855, by rfl⟩) R95711
theorem R96767 : Reach 96767 := rs (se 1 (by rfl) ⟨72575, by rfl⟩) R145151
theorem R64763 : Reach 64763 := rs (se 1 (by rfl) ⟨48572, by rfl⟩) R97145
theorem R1692065 : Reach 1692065 := rs (se 2 (by rfl) ⟨634524, by rfl⟩) R1269049
theorem R224423 : Reach 224423 := rs (se 1 (by rfl) ⟨168317, by rfl⟩) R336635
theorem R63695 : Reach 63695 := rs (se 1 (by rfl) ⟨47771, by rfl⟩) R95543
theorem R64511 : Reach 64511 := rs (se 1 (by rfl) ⟨48383, by rfl⟩) R96767
theorem R1128043 : Reach 1128043 := rs (se 1 (by rfl) ⟨846032, by rfl⟩) R1692065
theorem R149615 : Reach 149615 := rs (se 1 (by rfl) ⟨112211, by rfl⟩) R224423
theorem R99743 : Reach 99743 := rs (se 1 (by rfl) ⟨74807, by rfl⟩) R149615
theorem R1504057 : Reach 1504057 := rs (se 2 (by rfl) ⟨564021, by rfl⟩) R1128043
theorem R66495 : Reach 66495 := rs (se 1 (by rfl) ⟨49871, by rfl⟩) R99743
theorem R2005409 : Reach 2005409 := rs (se 2 (by rfl) ⟨752028, by rfl⟩) R1504057
theorem R5347757 : Reach 5347757 := rs (se 3 (by rfl) ⟨1002704, by rfl⟩) R2005409
theorem R3565171 : Reach 3565171 := rs (se 1 (by rfl) ⟨2673878, by rfl⟩) R5347757
theorem R4753561 : Reach 4753561 := rs (se 2 (by rfl) ⟨1782585, by rfl⟩) R3565171
theorem R6338081 : Reach 6338081 := rs (se 2 (by rfl) ⟨2376780, by rfl⟩) R4753561
theorem R4225387 : Reach 4225387 := rs (se 1 (by rfl) ⟨3169040, by rfl⟩) R6338081
theorem R5633849 : Reach 5633849 := rs (se 2 (by rfl) ⟨2112693, by rfl⟩) R4225387
theorem R3755899 : Reach 3755899 := rs (se 1 (by rfl) ⟨2816924, by rfl⟩) R5633849
theorem R5007865 : Reach 5007865 := rs (se 2 (by rfl) ⟨1877949, by rfl⟩) R3755899
theorem R6677153 : Reach 6677153 := rs (se 2 (by rfl) ⟨2503932, by rfl⟩) R5007865
theorem R4451435 : Reach 4451435 := rs (se 1 (by rfl) ⟨3338576, by rfl⟩) R6677153
theorem R2967623 : Reach 2967623 := rs (se 1 (by rfl) ⟨2225717, by rfl⟩) R4451435
theorem R1978415 : Reach 1978415 := rs (se 1 (by rfl) ⟨1483811, by rfl⟩) R2967623
theorem R1318943 : Reach 1318943 := rs (se 1 (by rfl) ⟨989207, by rfl⟩) R1978415
theorem R879295 : Reach 879295 := rs (se 1 (by rfl) ⟨659471, by rfl⟩) R1318943
theorem R1172393 : Reach 1172393 := rs (se 2 (by rfl) ⟨439647, by rfl⟩) R879295
theorem R781595 : Reach 781595 := rs (se 1 (by rfl) ⟨586196, by rfl⟩) R1172393
theorem R521063 : Reach 521063 := rs (se 1 (by rfl) ⟨390797, by rfl⟩) R781595
theorem R347375 : Reach 347375 := rs (se 1 (by rfl) ⟨260531, by rfl⟩) R521063
theorem R231583 : Reach 231583 := rs (se 1 (by rfl) ⟨173687, by rfl⟩) R347375
theorem R308777 : Reach 308777 := rs (se 2 (by rfl) ⟨115791, by rfl⟩) R231583
theorem R823405 : Reach 823405 := rs (se 3 (by rfl) ⟨154388, by rfl⟩) R308777
theorem R1097873 : Reach 1097873 := rs (se 2 (by rfl) ⟨411702, by rfl⟩) R823405
theorem R731915 : Reach 731915 := rs (se 1 (by rfl) ⟨548936, by rfl⟩) R1097873
theorem R487943 : Reach 487943 := rs (se 1 (by rfl) ⟨365957, by rfl⟩) R731915
theorem R325295 : Reach 325295 := rs (se 1 (by rfl) ⟨243971, by rfl⟩) R487943
theorem R216863 : Reach 216863 := rs (se 1 (by rfl) ⟨162647, by rfl⟩) R325295
theorem R144575 : Reach 144575 := rs (se 1 (by rfl) ⟨108431, by rfl⟩) R216863
theorem R96383 : Reach 96383 := rs (se 1 (by rfl) ⟨72287, by rfl⟩) R144575
theorem R64255 : Reach 64255 := rs (se 1 (by rfl) ⟨48191, by rfl⟩) R96383

theorem C0 (j : ℕ) (h1 : 31561 ≤ j) (h2 : j ≤ 32260) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R63123
  · exact R63125
  · exact R63127
  · exact R63129
  · exact R63131
  · exact R63133
  · exact R63135
  · exact R63137
  · exact R63139
  · exact R63141
  · exact R63143
  · exact R63145
  · exact R63147
  · exact R63149
  · exact R63151
  · exact R63153
  · exact R63155
  · exact R63157
  · exact R63159
  · exact R63161
  · exact R63163
  · exact R63165
  · exact R63167
  · exact R63169
  · exact R63171
  · exact R63173
  · exact R63175
  · exact R63177
  · exact R63179
  · exact R63181
  · exact R63183
  · exact R63185
  · exact R63187
  · exact R63189
  · exact R63191
  · exact R63193
  · exact R63195
  · exact R63197
  · exact R63199
  · exact R63201
  · exact R63203
  · exact R63205
  · exact R63207
  · exact R63209
  · exact R63211
  · exact R63213
  · exact R63215
  · exact R63217
  · exact R63219
  · exact R63221
  · exact R63223
  · exact R63225
  · exact R63227
  · exact R63229
  · exact R63231
  · exact R63233
  · exact R63235
  · exact R63237
  · exact R63239
  · exact R63241
  · exact R63243
  · exact R63245
  · exact R63247
  · exact R63249
  · exact R63251
  · exact R63253
  · exact R63255
  · exact R63257
  · exact R63259
  · exact R63261
  · exact R63263
  · exact R63265
  · exact R63267
  · exact R63269
  · exact R63271
  · exact R63273
  · exact R63275
  · exact R63277
  · exact R63279
  · exact R63281
  · exact R63283
  · exact R63285
  · exact R63287
  · exact R63289
  · exact R63291
  · exact R63293
  · exact R63295
  · exact R63297
  · exact R63299
  · exact R63301
  · exact R63303
  · exact R63305
  · exact R63307
  · exact R63309
  · exact R63311
  · exact R63313
  · exact R63315
  · exact R63317
  · exact R63319
  · exact R63321
  · exact R63323
  · exact R63325
  · exact R63327
  · exact R63329
  · exact R63331
  · exact R63333
  · exact R63335
  · exact R63337
  · exact R63339
  · exact R63341
  · exact R63343
  · exact R63345
  · exact R63347
  · exact R63349
  · exact R63351
  · exact R63353
  · exact R63355
  · exact R63357
  · exact R63359
  · exact R63361
  · exact R63363
  · exact R63365
  · exact R63367
  · exact R63369
  · exact R63371
  · exact R63373
  · exact R63375
  · exact R63377
  · exact R63379
  · exact R63381
  · exact R63383
  · exact R63385
  · exact R63387
  · exact R63389
  · exact R63391
  · exact R63393
  · exact R63395
  · exact R63397
  · exact R63399
  · exact R63401
  · exact R63403
  · exact R63405
  · exact R63407
  · exact R63409
  · exact R63411
  · exact R63413
  · exact R63415
  · exact R63417
  · exact R63419
  · exact R63421
  · exact R63423
  · exact R63425
  · exact R63427
  · exact R63429
  · exact R63431
  · exact R63433
  · exact R63435
  · exact R63437
  · exact R63439
  · exact R63441
  · exact R63443
  · exact R63445
  · exact R63447
  · exact R63449
  · exact R63451
  · exact R63453
  · exact R63455
  · exact R63457
  · exact R63459
  · exact R63461
  · exact R63463
  · exact R63465
  · exact R63467
  · exact R63469
  · exact R63471
  · exact R63473
  · exact R63475
  · exact R63477
  · exact R63479
  · exact R63481
  · exact R63483
  · exact R63485
  · exact R63487
  · exact R63489
  · exact R63491
  · exact R63493
  · exact R63495
  · exact R63497
  · exact R63499
  · exact R63501
  · exact R63503
  · exact R63505
  · exact R63507
  · exact R63509
  · exact R63511
  · exact R63513
  · exact R63515
  · exact R63517
  · exact R63519
  · exact R63521
  · exact R63523
  · exact R63525
  · exact R63527
  · exact R63529
  · exact R63531
  · exact R63533
  · exact R63535
  · exact R63537
  · exact R63539
  · exact R63541
  · exact R63543
  · exact R63545
  · exact R63547
  · exact R63549
  · exact R63551
  · exact R63553
  · exact R63555
  · exact R63557
  · exact R63559
  · exact R63561
  · exact R63563
  · exact R63565
  · exact R63567
  · exact R63569
  · exact R63571
  · exact R63573
  · exact R63575
  · exact R63577
  · exact R63579
  · exact R63581
  · exact R63583
  · exact R63585
  · exact R63587
  · exact R63589
  · exact R63591
  · exact R63593
  · exact R63595
  · exact R63597
  · exact R63599
  · exact R63601
  · exact R63603
  · exact R63605
  · exact R63607
  · exact R63609
  · exact R63611
  · exact R63613
  · exact R63615
  · exact R63617
  · exact R63619
  · exact R63621
  · exact R63623
  · exact R63625
  · exact R63627
  · exact R63629
  · exact R63631
  · exact R63633
  · exact R63635
  · exact R63637
  · exact R63639
  · exact R63641
  · exact R63643
  · exact R63645
  · exact R63647
  · exact R63649
  · exact R63651
  · exact R63653
  · exact R63655
  · exact R63657
  · exact R63659
  · exact R63661
  · exact R63663
  · exact R63665
  · exact R63667
  · exact R63669
  · exact R63671
  · exact R63673
  · exact R63675
  · exact R63677
  · exact R63679
  · exact R63681
  · exact R63683
  · exact R63685
  · exact R63687
  · exact R63689
  · exact R63691
  · exact R63693
  · exact R63695
  · exact R63697
  · exact R63699
  · exact R63701
  · exact R63703
  · exact R63705
  · exact R63707
  · exact R63709
  · exact R63711
  · exact R63713
  · exact R63715
  · exact R63717
  · exact R63719
  · exact R63721
  · exact R63723
  · exact R63725
  · exact R63727
  · exact R63729
  · exact R63731
  · exact R63733
  · exact R63735
  · exact R63737
  · exact R63739
  · exact R63741
  · exact R63743
  · exact R63745
  · exact R63747
  · exact R63749
  · exact R63751
  · exact R63753
  · exact R63755
  · exact R63757
  · exact R63759
  · exact R63761
  · exact R63763
  · exact R63765
  · exact R63767
  · exact R63769
  · exact R63771
  · exact R63773
  · exact R63775
  · exact R63777
  · exact R63779
  · exact R63781
  · exact R63783
  · exact R63785
  · exact R63787
  · exact R63789
  · exact R63791
  · exact R63793
  · exact R63795
  · exact R63797
  · exact R63799
  · exact R63801
  · exact R63803
  · exact R63805
  · exact R63807
  · exact R63809
  · exact R63811
  · exact R63813
  · exact R63815
  · exact R63817
  · exact R63819
  · exact R63821
  · exact R63823
  · exact R63825
  · exact R63827
  · exact R63829
  · exact R63831
  · exact R63833
  · exact R63835
  · exact R63837
  · exact R63839
  · exact R63841
  · exact R63843
  · exact R63845
  · exact R63847
  · exact R63849
  · exact R63851
  · exact R63853
  · exact R63855
  · exact R63857
  · exact R63859
  · exact R63861
  · exact R63863
  · exact R63865
  · exact R63867
  · exact R63869
  · exact R63871
  · exact R63873
  · exact R63875
  · exact R63877
  · exact R63879
  · exact R63881
  · exact R63883
  · exact R63885
  · exact R63887
  · exact R63889
  · exact R63891
  · exact R63893
  · exact R63895
  · exact R63897
  · exact R63899
  · exact R63901
  · exact R63903
  · exact R63905
  · exact R63907
  · exact R63909
  · exact R63911
  · exact R63913
  · exact R63915
  · exact R63917
  · exact R63919
  · exact R63921
  · exact R63923
  · exact R63925
  · exact R63927
  · exact R63929
  · exact R63931
  · exact R63933
  · exact R63935
  · exact R63937
  · exact R63939
  · exact R63941
  · exact R63943
  · exact R63945
  · exact R63947
  · exact R63949
  · exact R63951
  · exact R63953
  · exact R63955
  · exact R63957
  · exact R63959
  · exact R63961
  · exact R63963
  · exact R63965
  · exact R63967
  · exact R63969
  · exact R63971
  · exact R63973
  · exact R63975
  · exact R63977
  · exact R63979
  · exact R63981
  · exact R63983
  · exact R63985
  · exact R63987
  · exact R63989
  · exact R63991
  · exact R63993
  · exact R63995
  · exact R63997
  · exact R63999
  · exact R64001
  · exact R64003
  · exact R64005
  · exact R64007
  · exact R64009
  · exact R64011
  · exact R64013
  · exact R64015
  · exact R64017
  · exact R64019
  · exact R64021
  · exact R64023
  · exact R64025
  · exact R64027
  · exact R64029
  · exact R64031
  · exact R64033
  · exact R64035
  · exact R64037
  · exact R64039
  · exact R64041
  · exact R64043
  · exact R64045
  · exact R64047
  · exact R64049
  · exact R64051
  · exact R64053
  · exact R64055
  · exact R64057
  · exact R64059
  · exact R64061
  · exact R64063
  · exact R64065
  · exact R64067
  · exact R64069
  · exact R64071
  · exact R64073
  · exact R64075
  · exact R64077
  · exact R64079
  · exact R64081
  · exact R64083
  · exact R64085
  · exact R64087
  · exact R64089
  · exact R64091
  · exact R64093
  · exact R64095
  · exact R64097
  · exact R64099
  · exact R64101
  · exact R64103
  · exact R64105
  · exact R64107
  · exact R64109
  · exact R64111
  · exact R64113
  · exact R64115
  · exact R64117
  · exact R64119
  · exact R64121
  · exact R64123
  · exact R64125
  · exact R64127
  · exact R64129
  · exact R64131
  · exact R64133
  · exact R64135
  · exact R64137
  · exact R64139
  · exact R64141
  · exact R64143
  · exact R64145
  · exact R64147
  · exact R64149
  · exact R64151
  · exact R64153
  · exact R64155
  · exact R64157
  · exact R64159
  · exact R64161
  · exact R64163
  · exact R64165
  · exact R64167
  · exact R64169
  · exact R64171
  · exact R64173
  · exact R64175
  · exact R64177
  · exact R64179
  · exact R64181
  · exact R64183
  · exact R64185
  · exact R64187
  · exact R64189
  · exact R64191
  · exact R64193
  · exact R64195
  · exact R64197
  · exact R64199
  · exact R64201
  · exact R64203
  · exact R64205
  · exact R64207
  · exact R64209
  · exact R64211
  · exact R64213
  · exact R64215
  · exact R64217
  · exact R64219
  · exact R64221
  · exact R64223
  · exact R64225
  · exact R64227
  · exact R64229
  · exact R64231
  · exact R64233
  · exact R64235
  · exact R64237
  · exact R64239
  · exact R64241
  · exact R64243
  · exact R64245
  · exact R64247
  · exact R64249
  · exact R64251
  · exact R64253
  · exact R64255
  · exact R64257
  · exact R64259
  · exact R64261
  · exact R64263
  · exact R64265
  · exact R64267
  · exact R64269
  · exact R64271
  · exact R64273
  · exact R64275
  · exact R64277
  · exact R64279
  · exact R64281
  · exact R64283
  · exact R64285
  · exact R64287
  · exact R64289
  · exact R64291
  · exact R64293
  · exact R64295
  · exact R64297
  · exact R64299
  · exact R64301
  · exact R64303
  · exact R64305
  · exact R64307
  · exact R64309
  · exact R64311
  · exact R64313
  · exact R64315
  · exact R64317
  · exact R64319
  · exact R64321
  · exact R64323
  · exact R64325
  · exact R64327
  · exact R64329
  · exact R64331
  · exact R64333
  · exact R64335
  · exact R64337
  · exact R64339
  · exact R64341
  · exact R64343
  · exact R64345
  · exact R64347
  · exact R64349
  · exact R64351
  · exact R64353
  · exact R64355
  · exact R64357
  · exact R64359
  · exact R64361
  · exact R64363
  · exact R64365
  · exact R64367
  · exact R64369
  · exact R64371
  · exact R64373
  · exact R64375
  · exact R64377
  · exact R64379
  · exact R64381
  · exact R64383
  · exact R64385
  · exact R64387
  · exact R64389
  · exact R64391
  · exact R64393
  · exact R64395
  · exact R64397
  · exact R64399
  · exact R64401
  · exact R64403
  · exact R64405
  · exact R64407
  · exact R64409
  · exact R64411
  · exact R64413
  · exact R64415
  · exact R64417
  · exact R64419
  · exact R64421
  · exact R64423
  · exact R64425
  · exact R64427
  · exact R64429
  · exact R64431
  · exact R64433
  · exact R64435
  · exact R64437
  · exact R64439
  · exact R64441
  · exact R64443
  · exact R64445
  · exact R64447
  · exact R64449
  · exact R64451
  · exact R64453
  · exact R64455
  · exact R64457
  · exact R64459
  · exact R64461
  · exact R64463
  · exact R64465
  · exact R64467
  · exact R64469
  · exact R64471
  · exact R64473
  · exact R64475
  · exact R64477
  · exact R64479
  · exact R64481
  · exact R64483
  · exact R64485
  · exact R64487
  · exact R64489
  · exact R64491
  · exact R64493
  · exact R64495
  · exact R64497
  · exact R64499
  · exact R64501
  · exact R64503
  · exact R64505
  · exact R64507
  · exact R64509
  · exact R64511
  · exact R64513
  · exact R64515
  · exact R64517
  · exact R64519
  · exact R64521

theorem C1 (j : ℕ) (h1 : 32261 ≤ j) (h2 : j ≤ 32960) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R64523
  · exact R64525
  · exact R64527
  · exact R64529
  · exact R64531
  · exact R64533
  · exact R64535
  · exact R64537
  · exact R64539
  · exact R64541
  · exact R64543
  · exact R64545
  · exact R64547
  · exact R64549
  · exact R64551
  · exact R64553
  · exact R64555
  · exact R64557
  · exact R64559
  · exact R64561
  · exact R64563
  · exact R64565
  · exact R64567
  · exact R64569
  · exact R64571
  · exact R64573
  · exact R64575
  · exact R64577
  · exact R64579
  · exact R64581
  · exact R64583
  · exact R64585
  · exact R64587
  · exact R64589
  · exact R64591
  · exact R64593
  · exact R64595
  · exact R64597
  · exact R64599
  · exact R64601
  · exact R64603
  · exact R64605
  · exact R64607
  · exact R64609
  · exact R64611
  · exact R64613
  · exact R64615
  · exact R64617
  · exact R64619
  · exact R64621
  · exact R64623
  · exact R64625
  · exact R64627
  · exact R64629
  · exact R64631
  · exact R64633
  · exact R64635
  · exact R64637
  · exact R64639
  · exact R64641
  · exact R64643
  · exact R64645
  · exact R64647
  · exact R64649
  · exact R64651
  · exact R64653
  · exact R64655
  · exact R64657
  · exact R64659
  · exact R64661
  · exact R64663
  · exact R64665
  · exact R64667
  · exact R64669
  · exact R64671
  · exact R64673
  · exact R64675
  · exact R64677
  · exact R64679
  · exact R64681
  · exact R64683
  · exact R64685
  · exact R64687
  · exact R64689
  · exact R64691
  · exact R64693
  · exact R64695
  · exact R64697
  · exact R64699
  · exact R64701
  · exact R64703
  · exact R64705
  · exact R64707
  · exact R64709
  · exact R64711
  · exact R64713
  · exact R64715
  · exact R64717
  · exact R64719
  · exact R64721
  · exact R64723
  · exact R64725
  · exact R64727
  · exact R64729
  · exact R64731
  · exact R64733
  · exact R64735
  · exact R64737
  · exact R64739
  · exact R64741
  · exact R64743
  · exact R64745
  · exact R64747
  · exact R64749
  · exact R64751
  · exact R64753
  · exact R64755
  · exact R64757
  · exact R64759
  · exact R64761
  · exact R64763
  · exact R64765
  · exact R64767
  · exact R64769
  · exact R64771
  · exact R64773
  · exact R64775
  · exact R64777
  · exact R64779
  · exact R64781
  · exact R64783
  · exact R64785
  · exact R64787
  · exact R64789
  · exact R64791
  · exact R64793
  · exact R64795
  · exact R64797
  · exact R64799
  · exact R64801
  · exact R64803
  · exact R64805
  · exact R64807
  · exact R64809
  · exact R64811
  · exact R64813
  · exact R64815
  · exact R64817
  · exact R64819
  · exact R64821
  · exact R64823
  · exact R64825
  · exact R64827
  · exact R64829
  · exact R64831
  · exact R64833
  · exact R64835
  · exact R64837
  · exact R64839
  · exact R64841
  · exact R64843
  · exact R64845
  · exact R64847
  · exact R64849
  · exact R64851
  · exact R64853
  · exact R64855
  · exact R64857
  · exact R64859
  · exact R64861
  · exact R64863
  · exact R64865
  · exact R64867
  · exact R64869
  · exact R64871
  · exact R64873
  · exact R64875
  · exact R64877
  · exact R64879
  · exact R64881
  · exact R64883
  · exact R64885
  · exact R64887
  · exact R64889
  · exact R64891
  · exact R64893
  · exact R64895
  · exact R64897
  · exact R64899
  · exact R64901
  · exact R64903
  · exact R64905
  · exact R64907
  · exact R64909
  · exact R64911
  · exact R64913
  · exact R64915
  · exact R64917
  · exact R64919
  · exact R64921
  · exact R64923
  · exact R64925
  · exact R64927
  · exact R64929
  · exact R64931
  · exact R64933
  · exact R64935
  · exact R64937
  · exact R64939
  · exact R64941
  · exact R64943
  · exact R64945
  · exact R64947
  · exact R64949
  · exact R64951
  · exact R64953
  · exact R64955
  · exact R64957
  · exact R64959
  · exact R64961
  · exact R64963
  · exact R64965
  · exact R64967
  · exact R64969
  · exact R64971
  · exact R64973
  · exact R64975
  · exact R64977
  · exact R64979
  · exact R64981
  · exact R64983
  · exact R64985
  · exact R64987
  · exact R64989
  · exact R64991
  · exact R64993
  · exact R64995
  · exact R64997
  · exact R64999
  · exact R65001
  · exact R65003
  · exact R65005
  · exact R65007
  · exact R65009
  · exact R65011
  · exact R65013
  · exact R65015
  · exact R65017
  · exact R65019
  · exact R65021
  · exact R65023
  · exact R65025
  · exact R65027
  · exact R65029
  · exact R65031
  · exact R65033
  · exact R65035
  · exact R65037
  · exact R65039
  · exact R65041
  · exact R65043
  · exact R65045
  · exact R65047
  · exact R65049
  · exact R65051
  · exact R65053
  · exact R65055
  · exact R65057
  · exact R65059
  · exact R65061
  · exact R65063
  · exact R65065
  · exact R65067
  · exact R65069
  · exact R65071
  · exact R65073
  · exact R65075
  · exact R65077
  · exact R65079
  · exact R65081
  · exact R65083
  · exact R65085
  · exact R65087
  · exact R65089
  · exact R65091
  · exact R65093
  · exact R65095
  · exact R65097
  · exact R65099
  · exact R65101
  · exact R65103
  · exact R65105
  · exact R65107
  · exact R65109
  · exact R65111
  · exact R65113
  · exact R65115
  · exact R65117
  · exact R65119
  · exact R65121
  · exact R65123
  · exact R65125
  · exact R65127
  · exact R65129
  · exact R65131
  · exact R65133
  · exact R65135
  · exact R65137
  · exact R65139
  · exact R65141
  · exact R65143
  · exact R65145
  · exact R65147
  · exact R65149
  · exact R65151
  · exact R65153
  · exact R65155
  · exact R65157
  · exact R65159
  · exact R65161
  · exact R65163
  · exact R65165
  · exact R65167
  · exact R65169
  · exact R65171
  · exact R65173
  · exact R65175
  · exact R65177
  · exact R65179
  · exact R65181
  · exact R65183
  · exact R65185
  · exact R65187
  · exact R65189
  · exact R65191
  · exact R65193
  · exact R65195
  · exact R65197
  · exact R65199
  · exact R65201
  · exact R65203
  · exact R65205
  · exact R65207
  · exact R65209
  · exact R65211
  · exact R65213
  · exact R65215
  · exact R65217
  · exact R65219
  · exact R65221
  · exact R65223
  · exact R65225
  · exact R65227
  · exact R65229
  · exact R65231
  · exact R65233
  · exact R65235
  · exact R65237
  · exact R65239
  · exact R65241
  · exact R65243
  · exact R65245
  · exact R65247
  · exact R65249
  · exact R65251
  · exact R65253
  · exact R65255
  · exact R65257
  · exact R65259
  · exact R65261
  · exact R65263
  · exact R65265
  · exact R65267
  · exact R65269
  · exact R65271
  · exact R65273
  · exact R65275
  · exact R65277
  · exact R65279
  · exact R65281
  · exact R65283
  · exact R65285
  · exact R65287
  · exact R65289
  · exact R65291
  · exact R65293
  · exact R65295
  · exact R65297
  · exact R65299
  · exact R65301
  · exact R65303
  · exact R65305
  · exact R65307
  · exact R65309
  · exact R65311
  · exact R65313
  · exact R65315
  · exact R65317
  · exact R65319
  · exact R65321
  · exact R65323
  · exact R65325
  · exact R65327
  · exact R65329
  · exact R65331
  · exact R65333
  · exact R65335
  · exact R65337
  · exact R65339
  · exact R65341
  · exact R65343
  · exact R65345
  · exact R65347
  · exact R65349
  · exact R65351
  · exact R65353
  · exact R65355
  · exact R65357
  · exact R65359
  · exact R65361
  · exact R65363
  · exact R65365
  · exact R65367
  · exact R65369
  · exact R65371
  · exact R65373
  · exact R65375
  · exact R65377
  · exact R65379
  · exact R65381
  · exact R65383
  · exact R65385
  · exact R65387
  · exact R65389
  · exact R65391
  · exact R65393
  · exact R65395
  · exact R65397
  · exact R65399
  · exact R65401
  · exact R65403
  · exact R65405
  · exact R65407
  · exact R65409
  · exact R65411
  · exact R65413
  · exact R65415
  · exact R65417
  · exact R65419
  · exact R65421
  · exact R65423
  · exact R65425
  · exact R65427
  · exact R65429
  · exact R65431
  · exact R65433
  · exact R65435
  · exact R65437
  · exact R65439
  · exact R65441
  · exact R65443
  · exact R65445
  · exact R65447
  · exact R65449
  · exact R65451
  · exact R65453
  · exact R65455
  · exact R65457
  · exact R65459
  · exact R65461
  · exact R65463
  · exact R65465
  · exact R65467
  · exact R65469
  · exact R65471
  · exact R65473
  · exact R65475
  · exact R65477
  · exact R65479
  · exact R65481
  · exact R65483
  · exact R65485
  · exact R65487
  · exact R65489
  · exact R65491
  · exact R65493
  · exact R65495
  · exact R65497
  · exact R65499
  · exact R65501
  · exact R65503
  · exact R65505
  · exact R65507
  · exact R65509
  · exact R65511
  · exact R65513
  · exact R65515
  · exact R65517
  · exact R65519
  · exact R65521
  · exact R65523
  · exact R65525
  · exact R65527
  · exact R65529
  · exact R65531
  · exact R65533
  · exact R65535
  · exact R65537
  · exact R65539
  · exact R65541
  · exact R65543
  · exact R65545
  · exact R65547
  · exact R65549
  · exact R65551
  · exact R65553
  · exact R65555
  · exact R65557
  · exact R65559
  · exact R65561
  · exact R65563
  · exact R65565
  · exact R65567
  · exact R65569
  · exact R65571
  · exact R65573
  · exact R65575
  · exact R65577
  · exact R65579
  · exact R65581
  · exact R65583
  · exact R65585
  · exact R65587
  · exact R65589
  · exact R65591
  · exact R65593
  · exact R65595
  · exact R65597
  · exact R65599
  · exact R65601
  · exact R65603
  · exact R65605
  · exact R65607
  · exact R65609
  · exact R65611
  · exact R65613
  · exact R65615
  · exact R65617
  · exact R65619
  · exact R65621
  · exact R65623
  · exact R65625
  · exact R65627
  · exact R65629
  · exact R65631
  · exact R65633
  · exact R65635
  · exact R65637
  · exact R65639
  · exact R65641
  · exact R65643
  · exact R65645
  · exact R65647
  · exact R65649
  · exact R65651
  · exact R65653
  · exact R65655
  · exact R65657
  · exact R65659
  · exact R65661
  · exact R65663
  · exact R65665
  · exact R65667
  · exact R65669
  · exact R65671
  · exact R65673
  · exact R65675
  · exact R65677
  · exact R65679
  · exact R65681
  · exact R65683
  · exact R65685
  · exact R65687
  · exact R65689
  · exact R65691
  · exact R65693
  · exact R65695
  · exact R65697
  · exact R65699
  · exact R65701
  · exact R65703
  · exact R65705
  · exact R65707
  · exact R65709
  · exact R65711
  · exact R65713
  · exact R65715
  · exact R65717
  · exact R65719
  · exact R65721
  · exact R65723
  · exact R65725
  · exact R65727
  · exact R65729
  · exact R65731
  · exact R65733
  · exact R65735
  · exact R65737
  · exact R65739
  · exact R65741
  · exact R65743
  · exact R65745
  · exact R65747
  · exact R65749
  · exact R65751
  · exact R65753
  · exact R65755
  · exact R65757
  · exact R65759
  · exact R65761
  · exact R65763
  · exact R65765
  · exact R65767
  · exact R65769
  · exact R65771
  · exact R65773
  · exact R65775
  · exact R65777
  · exact R65779
  · exact R65781
  · exact R65783
  · exact R65785
  · exact R65787
  · exact R65789
  · exact R65791
  · exact R65793
  · exact R65795
  · exact R65797
  · exact R65799
  · exact R65801
  · exact R65803
  · exact R65805
  · exact R65807
  · exact R65809
  · exact R65811
  · exact R65813
  · exact R65815
  · exact R65817
  · exact R65819
  · exact R65821
  · exact R65823
  · exact R65825
  · exact R65827
  · exact R65829
  · exact R65831
  · exact R65833
  · exact R65835
  · exact R65837
  · exact R65839
  · exact R65841
  · exact R65843
  · exact R65845
  · exact R65847
  · exact R65849
  · exact R65851
  · exact R65853
  · exact R65855
  · exact R65857
  · exact R65859
  · exact R65861
  · exact R65863
  · exact R65865
  · exact R65867
  · exact R65869
  · exact R65871
  · exact R65873
  · exact R65875
  · exact R65877
  · exact R65879
  · exact R65881
  · exact R65883
  · exact R65885
  · exact R65887
  · exact R65889
  · exact R65891
  · exact R65893
  · exact R65895
  · exact R65897
  · exact R65899
  · exact R65901
  · exact R65903
  · exact R65905
  · exact R65907
  · exact R65909
  · exact R65911
  · exact R65913
  · exact R65915
  · exact R65917
  · exact R65919
  · exact R65921

theorem C2 (j : ℕ) (h1 : 32961 ≤ j) (h2 : j ≤ 33561) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R65923
  · exact R65925
  · exact R65927
  · exact R65929
  · exact R65931
  · exact R65933
  · exact R65935
  · exact R65937
  · exact R65939
  · exact R65941
  · exact R65943
  · exact R65945
  · exact R65947
  · exact R65949
  · exact R65951
  · exact R65953
  · exact R65955
  · exact R65957
  · exact R65959
  · exact R65961
  · exact R65963
  · exact R65965
  · exact R65967
  · exact R65969
  · exact R65971
  · exact R65973
  · exact R65975
  · exact R65977
  · exact R65979
  · exact R65981
  · exact R65983
  · exact R65985
  · exact R65987
  · exact R65989
  · exact R65991
  · exact R65993
  · exact R65995
  · exact R65997
  · exact R65999
  · exact R66001
  · exact R66003
  · exact R66005
  · exact R66007
  · exact R66009
  · exact R66011
  · exact R66013
  · exact R66015
  · exact R66017
  · exact R66019
  · exact R66021
  · exact R66023
  · exact R66025
  · exact R66027
  · exact R66029
  · exact R66031
  · exact R66033
  · exact R66035
  · exact R66037
  · exact R66039
  · exact R66041
  · exact R66043
  · exact R66045
  · exact R66047
  · exact R66049
  · exact R66051
  · exact R66053
  · exact R66055
  · exact R66057
  · exact R66059
  · exact R66061
  · exact R66063
  · exact R66065
  · exact R66067
  · exact R66069
  · exact R66071
  · exact R66073
  · exact R66075
  · exact R66077
  · exact R66079
  · exact R66081
  · exact R66083
  · exact R66085
  · exact R66087
  · exact R66089
  · exact R66091
  · exact R66093
  · exact R66095
  · exact R66097
  · exact R66099
  · exact R66101
  · exact R66103
  · exact R66105
  · exact R66107
  · exact R66109
  · exact R66111
  · exact R66113
  · exact R66115
  · exact R66117
  · exact R66119
  · exact R66121
  · exact R66123
  · exact R66125
  · exact R66127
  · exact R66129
  · exact R66131
  · exact R66133
  · exact R66135
  · exact R66137
  · exact R66139
  · exact R66141
  · exact R66143
  · exact R66145
  · exact R66147
  · exact R66149
  · exact R66151
  · exact R66153
  · exact R66155
  · exact R66157
  · exact R66159
  · exact R66161
  · exact R66163
  · exact R66165
  · exact R66167
  · exact R66169
  · exact R66171
  · exact R66173
  · exact R66175
  · exact R66177
  · exact R66179
  · exact R66181
  · exact R66183
  · exact R66185
  · exact R66187
  · exact R66189
  · exact R66191
  · exact R66193
  · exact R66195
  · exact R66197
  · exact R66199
  · exact R66201
  · exact R66203
  · exact R66205
  · exact R66207
  · exact R66209
  · exact R66211
  · exact R66213
  · exact R66215
  · exact R66217
  · exact R66219
  · exact R66221
  · exact R66223
  · exact R66225
  · exact R66227
  · exact R66229
  · exact R66231
  · exact R66233
  · exact R66235
  · exact R66237
  · exact R66239
  · exact R66241
  · exact R66243
  · exact R66245
  · exact R66247
  · exact R66249
  · exact R66251
  · exact R66253
  · exact R66255
  · exact R66257
  · exact R66259
  · exact R66261
  · exact R66263
  · exact R66265
  · exact R66267
  · exact R66269
  · exact R66271
  · exact R66273
  · exact R66275
  · exact R66277
  · exact R66279
  · exact R66281
  · exact R66283
  · exact R66285
  · exact R66287
  · exact R66289
  · exact R66291
  · exact R66293
  · exact R66295
  · exact R66297
  · exact R66299
  · exact R66301
  · exact R66303
  · exact R66305
  · exact R66307
  · exact R66309
  · exact R66311
  · exact R66313
  · exact R66315
  · exact R66317
  · exact R66319
  · exact R66321
  · exact R66323
  · exact R66325
  · exact R66327
  · exact R66329
  · exact R66331
  · exact R66333
  · exact R66335
  · exact R66337
  · exact R66339
  · exact R66341
  · exact R66343
  · exact R66345
  · exact R66347
  · exact R66349
  · exact R66351
  · exact R66353
  · exact R66355
  · exact R66357
  · exact R66359
  · exact R66361
  · exact R66363
  · exact R66365
  · exact R66367
  · exact R66369
  · exact R66371
  · exact R66373
  · exact R66375
  · exact R66377
  · exact R66379
  · exact R66381
  · exact R66383
  · exact R66385
  · exact R66387
  · exact R66389
  · exact R66391
  · exact R66393
  · exact R66395
  · exact R66397
  · exact R66399
  · exact R66401
  · exact R66403
  · exact R66405
  · exact R66407
  · exact R66409
  · exact R66411
  · exact R66413
  · exact R66415
  · exact R66417
  · exact R66419
  · exact R66421
  · exact R66423
  · exact R66425
  · exact R66427
  · exact R66429
  · exact R66431
  · exact R66433
  · exact R66435
  · exact R66437
  · exact R66439
  · exact R66441
  · exact R66443
  · exact R66445
  · exact R66447
  · exact R66449
  · exact R66451
  · exact R66453
  · exact R66455
  · exact R66457
  · exact R66459
  · exact R66461
  · exact R66463
  · exact R66465
  · exact R66467
  · exact R66469
  · exact R66471
  · exact R66473
  · exact R66475
  · exact R66477
  · exact R66479
  · exact R66481
  · exact R66483
  · exact R66485
  · exact R66487
  · exact R66489
  · exact R66491
  · exact R66493
  · exact R66495
  · exact R66497
  · exact R66499
  · exact R66501
  · exact R66503
  · exact R66505
  · exact R66507
  · exact R66509
  · exact R66511
  · exact R66513
  · exact R66515
  · exact R66517
  · exact R66519
  · exact R66521
  · exact R66523
  · exact R66525
  · exact R66527
  · exact R66529
  · exact R66531
  · exact R66533
  · exact R66535
  · exact R66537
  · exact R66539
  · exact R66541
  · exact R66543
  · exact R66545
  · exact R66547
  · exact R66549
  · exact R66551
  · exact R66553
  · exact R66555
  · exact R66557
  · exact R66559
  · exact R66561
  · exact R66563
  · exact R66565
  · exact R66567
  · exact R66569
  · exact R66571
  · exact R66573
  · exact R66575
  · exact R66577
  · exact R66579
  · exact R66581
  · exact R66583
  · exact R66585
  · exact R66587
  · exact R66589
  · exact R66591
  · exact R66593
  · exact R66595
  · exact R66597
  · exact R66599
  · exact R66601
  · exact R66603
  · exact R66605
  · exact R66607
  · exact R66609
  · exact R66611
  · exact R66613
  · exact R66615
  · exact R66617
  · exact R66619
  · exact R66621
  · exact R66623
  · exact R66625
  · exact R66627
  · exact R66629
  · exact R66631
  · exact R66633
  · exact R66635
  · exact R66637
  · exact R66639
  · exact R66641
  · exact R66643
  · exact R66645
  · exact R66647
  · exact R66649
  · exact R66651
  · exact R66653
  · exact R66655
  · exact R66657
  · exact R66659
  · exact R66661
  · exact R66663
  · exact R66665
  · exact R66667
  · exact R66669
  · exact R66671
  · exact R66673
  · exact R66675
  · exact R66677
  · exact R66679
  · exact R66681
  · exact R66683
  · exact R66685
  · exact R66687
  · exact R66689
  · exact R66691
  · exact R66693
  · exact R66695
  · exact R66697
  · exact R66699
  · exact R66701
  · exact R66703
  · exact R66705
  · exact R66707
  · exact R66709
  · exact R66711
  · exact R66713
  · exact R66715
  · exact R66717
  · exact R66719
  · exact R66721
  · exact R66723
  · exact R66725
  · exact R66727
  · exact R66729
  · exact R66731
  · exact R66733
  · exact R66735
  · exact R66737
  · exact R66739
  · exact R66741
  · exact R66743
  · exact R66745
  · exact R66747
  · exact R66749
  · exact R66751
  · exact R66753
  · exact R66755
  · exact R66757
  · exact R66759
  · exact R66761
  · exact R66763
  · exact R66765
  · exact R66767
  · exact R66769
  · exact R66771
  · exact R66773
  · exact R66775
  · exact R66777
  · exact R66779
  · exact R66781
  · exact R66783
  · exact R66785
  · exact R66787
  · exact R66789
  · exact R66791
  · exact R66793
  · exact R66795
  · exact R66797
  · exact R66799
  · exact R66801
  · exact R66803
  · exact R66805
  · exact R66807
  · exact R66809
  · exact R66811
  · exact R66813
  · exact R66815
  · exact R66817
  · exact R66819
  · exact R66821
  · exact R66823
  · exact R66825
  · exact R66827
  · exact R66829
  · exact R66831
  · exact R66833
  · exact R66835
  · exact R66837
  · exact R66839
  · exact R66841
  · exact R66843
  · exact R66845
  · exact R66847
  · exact R66849
  · exact R66851
  · exact R66853
  · exact R66855
  · exact R66857
  · exact R66859
  · exact R66861
  · exact R66863
  · exact R66865
  · exact R66867
  · exact R66869
  · exact R66871
  · exact R66873
  · exact R66875
  · exact R66877
  · exact R66879
  · exact R66881
  · exact R66883
  · exact R66885
  · exact R66887
  · exact R66889
  · exact R66891
  · exact R66893
  · exact R66895
  · exact R66897
  · exact R66899
  · exact R66901
  · exact R66903
  · exact R66905
  · exact R66907
  · exact R66909
  · exact R66911
  · exact R66913
  · exact R66915
  · exact R66917
  · exact R66919
  · exact R66921
  · exact R66923
  · exact R66925
  · exact R66927
  · exact R66929
  · exact R66931
  · exact R66933
  · exact R66935
  · exact R66937
  · exact R66939
  · exact R66941
  · exact R66943
  · exact R66945
  · exact R66947
  · exact R66949
  · exact R66951
  · exact R66953
  · exact R66955
  · exact R66957
  · exact R66959
  · exact R66961
  · exact R66963
  · exact R66965
  · exact R66967
  · exact R66969
  · exact R66971
  · exact R66973
  · exact R66975
  · exact R66977
  · exact R66979
  · exact R66981
  · exact R66983
  · exact R66985
  · exact R66987
  · exact R66989
  · exact R66991
  · exact R66993
  · exact R66995
  · exact R66997
  · exact R66999
  · exact R67001
  · exact R67003
  · exact R67005
  · exact R67007
  · exact R67009
  · exact R67011
  · exact R67013
  · exact R67015
  · exact R67017
  · exact R67019
  · exact R67021
  · exact R67023
  · exact R67025
  · exact R67027
  · exact R67029
  · exact R67031
  · exact R67033
  · exact R67035
  · exact R67037
  · exact R67039
  · exact R67041
  · exact R67043
  · exact R67045
  · exact R67047
  · exact R67049
  · exact R67051
  · exact R67053
  · exact R67055
  · exact R67057
  · exact R67059
  · exact R67061
  · exact R67063
  · exact R67065
  · exact R67067
  · exact R67069
  · exact R67071
  · exact R67073
  · exact R67075
  · exact R67077
  · exact R67079
  · exact R67081
  · exact R67083
  · exact R67085
  · exact R67087
  · exact R67089
  · exact R67091
  · exact R67093
  · exact R67095
  · exact R67097
  · exact R67099
  · exact R67101
  · exact R67103
  · exact R67105
  · exact R67107
  · exact R67109
  · exact R67111
  · exact R67113
  · exact R67115
  · exact R67117
  · exact R67119
  · exact R67121
  · exact R67123

theorem solution (m : ℕ) (hm : 0 < m) (hodd : Odd m) (hle : m ≤ 67123) :
    ∃ k : ℕ, syracuseStep^[k] m = 1 := by
  rcases Nat.lt_or_ge m 63123 with hlo | hlo
  · exact syracuse_reaches_one_below_63123 m hm hodd (by omega)
  obtain ⟨j, rfl⟩ : ∃ j, m = 2 * j + 1 := by obtain ⟨t, ht⟩ := hodd; exact ⟨t, by omega⟩
  rcases Nat.lt_or_ge j 32261 with h0 | h0
  · exact C0 j (by omega) (by omega)
  rcases Nat.lt_or_ge j 32961 with h1 | h1
  · exact C1 j (by omega) (by omega)
  exact C2 j (by omega) (by omega)
