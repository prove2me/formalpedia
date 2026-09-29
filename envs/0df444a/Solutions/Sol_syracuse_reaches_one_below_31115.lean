-- Prove2me | solution 1 for syracuse_reaches_one_below_31115
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T05:24:11.968957+00:00
-- url     : https://prove2.me/submissions/4804f655-ddbf-4747-9af3-c6e4b9ba168c

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_reaches_one_below_27114

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
theorem B (n : ℕ) (h1 : 0 < n) (h2 : Odd n) (h3 : n ≤ 27113) : Reach n :=
  syracuse_reaches_one_below_27114 n h1 h2 h3
theorem R32773 : Reach 32773 := rs (se 4 (by rfl) ⟨3072, by rfl⟩) (B 6145 (by norm_num) ⟨3072, by rfl⟩ (by norm_num))
theorem R65573 : Reach 65573 := rs (se 4 (by rfl) ⟨6147, by rfl⟩) (B 12295 (by norm_num) ⟨6147, by rfl⟩ (by norm_num))
theorem R32809 : Reach 32809 := rs (se 2 (by rfl) ⟨12303, by rfl⟩) (B 24607 (by norm_num) ⟨12303, by rfl⟩ (by norm_num))
theorem R65605 : Reach 65605 := rs (se 4 (by rfl) ⟨6150, by rfl⟩) (B 12301 (by norm_num) ⟨6150, by rfl⟩ (by norm_num))
theorem R32845 : Reach 32845 := rs (se 3 (by rfl) ⟨6158, by rfl⟩) (B 12317 (by norm_num) ⟨6158, by rfl⟩ (by norm_num))
theorem R98405 : Reach 98405 := rs (se 4 (by rfl) ⟨9225, by rfl⟩) (B 18451 (by norm_num) ⟨9225, by rfl⟩ (by norm_num))
theorem R65645 : Reach 65645 := rs (se 3 (by rfl) ⟨12308, by rfl⟩) (B 24617 (by norm_num) ⟨12308, by rfl⟩ (by norm_num))
theorem R32881 : Reach 32881 := rs (se 2 (by rfl) ⟨12330, by rfl⟩) (B 24661 (by norm_num) ⟨12330, by rfl⟩ (by norm_num))
theorem R32917 : Reach 32917 := rs (se 6 (by rfl) ⟨771, by rfl⟩) (B 1543 (by norm_num) ⟨771, by rfl⟩ (by norm_num))
theorem R65701 : Reach 65701 := rs (se 4 (by rfl) ⟨6159, by rfl⟩) (B 12319 (by norm_num) ⟨6159, by rfl⟩ (by norm_num))
theorem R65717 : Reach 65717 := rs (se 5 (by rfl) ⟨3080, by rfl⟩) (B 6161 (by norm_num) ⟨3080, by rfl⟩ (by norm_num))
theorem R32953 : Reach 32953 := rs (se 2 (by rfl) ⟨12357, by rfl⟩) (B 24715 (by norm_num) ⟨12357, by rfl⟩ (by norm_num))
theorem R32989 : Reach 32989 := rs (se 3 (by rfl) ⟨6185, by rfl⟩) (B 12371 (by norm_num) ⟨6185, by rfl⟩ (by norm_num))
theorem R65765 : Reach 65765 := rs (se 4 (by rfl) ⟨6165, by rfl⟩) (B 12331 (by norm_num) ⟨6165, by rfl⟩ (by norm_num))
theorem R98549 : Reach 98549 := rs (se 5 (by rfl) ⟨4619, by rfl⟩) (B 9239 (by norm_num) ⟨4619, by rfl⟩ (by norm_num))
theorem R65789 : Reach 65789 := rs (se 3 (by rfl) ⟨12335, by rfl⟩) (B 24671 (by norm_num) ⟨12335, by rfl⟩ (by norm_num))
theorem R33025 : Reach 33025 := rs (se 2 (by rfl) ⟨12384, by rfl⟩) (B 24769 (by norm_num) ⟨12384, by rfl⟩ (by norm_num))
theorem R33053 : Reach 33053 := rs (se 3 (by rfl) ⟨6197, by rfl⟩) (B 12395 (by norm_num) ⟨6197, by rfl⟩ (by norm_num))
theorem R33061 : Reach 33061 := rs (se 4 (by rfl) ⟨3099, by rfl⟩) (B 6199 (by norm_num) ⟨3099, by rfl⟩ (by norm_num))
theorem R65861 : Reach 65861 := rs (se 4 (by rfl) ⟨6174, by rfl⟩) (B 12349 (by norm_num) ⟨6174, by rfl⟩ (by norm_num))
theorem R33097 : Reach 33097 := rs (se 2 (by rfl) ⟨12411, by rfl⟩) (B 24823 (by norm_num) ⟨12411, by rfl⟩ (by norm_num))
theorem R65893 : Reach 65893 := rs (se 4 (by rfl) ⟨6177, by rfl⟩) (B 12355 (by norm_num) ⟨6177, by rfl⟩ (by norm_num))
theorem R33133 : Reach 33133 := rs (se 3 (by rfl) ⟨6212, by rfl⟩) (B 12425 (by norm_num) ⟨6212, by rfl⟩ (by norm_num))
theorem R65933 : Reach 65933 := rs (se 3 (by rfl) ⟨12362, by rfl⟩) (B 24725 (by norm_num) ⟨12362, by rfl⟩ (by norm_num))
theorem R33169 : Reach 33169 := rs (se 2 (by rfl) ⟨12438, by rfl⟩) (B 24877 (by norm_num) ⟨12438, by rfl⟩ (by norm_num))
theorem R33205 : Reach 33205 := rs (se 5 (by rfl) ⟨1556, by rfl⟩) (B 3113 (by norm_num) ⟨1556, by rfl⟩ (by norm_num))
theorem R66005 : Reach 66005 := rs (se 7 (by rfl) ⟨773, by rfl⟩) (B 1547 (by norm_num) ⟨773, by rfl⟩ (by norm_num))
theorem R33241 : Reach 33241 := rs (se 2 (by rfl) ⟨12465, by rfl⟩) (B 24931 (by norm_num) ⟨12465, by rfl⟩ (by norm_num))
theorem R33253 : Reach 33253 := rs (se 4 (by rfl) ⟨3117, by rfl⟩) (B 6235 (by norm_num) ⟨3117, by rfl⟩ (by norm_num))
theorem R229877 : Reach 229877 := rs (se 5 (by rfl) ⟨10775, by rfl⟩) (B 21551 (by norm_num) ⟨10775, by rfl⟩ (by norm_num))
theorem R33277 : Reach 33277 := rs (se 3 (by rfl) ⟨6239, by rfl⟩) (B 12479 (by norm_num) ⟨6239, by rfl⟩ (by norm_num))
theorem R66077 : Reach 66077 := rs (se 3 (by rfl) ⟨12389, by rfl⟩) (B 24779 (by norm_num) ⟨12389, by rfl⟩ (by norm_num))
theorem R33313 : Reach 33313 := rs (se 2 (by rfl) ⟨12492, by rfl⟩) (B 24985 (by norm_num) ⟨12492, by rfl⟩ (by norm_num))
theorem R33349 : Reach 33349 := rs (se 4 (by rfl) ⟨3126, by rfl⟩) (B 6253 (by norm_num) ⟨3126, by rfl⟩ (by norm_num))
theorem R66149 : Reach 66149 := rs (se 4 (by rfl) ⟨6201, by rfl⟩) (B 12403 (by norm_num) ⟨6201, by rfl⟩ (by norm_num))
theorem R33385 : Reach 33385 := rs (se 2 (by rfl) ⟨12519, by rfl⟩) (B 25039 (by norm_num) ⟨12519, by rfl⟩ (by norm_num))
theorem R33409 : Reach 33409 := rs (se 2 (by rfl) ⟨12528, by rfl⟩) (B 25057 (by norm_num) ⟨12528, by rfl⟩ (by norm_num))
theorem R33421 : Reach 33421 := rs (se 3 (by rfl) ⟨6266, by rfl⟩) (B 12533 (by norm_num) ⟨6266, by rfl⟩ (by norm_num))
theorem R98981 : Reach 98981 := rs (se 4 (by rfl) ⟨9279, by rfl⟩) (B 18559 (by norm_num) ⟨9279, by rfl⟩ (by norm_num))
theorem R66221 : Reach 66221 := rs (se 3 (by rfl) ⟨12416, by rfl⟩) (B 24833 (by norm_num) ⟨12416, by rfl⟩ (by norm_num))
theorem R33457 : Reach 33457 := rs (se 2 (by rfl) ⟨12546, by rfl⟩) (B 25093 (by norm_num) ⟨12546, by rfl⟩ (by norm_num))
theorem R33493 : Reach 33493 := rs (se 7 (by rfl) ⟨392, by rfl⟩) (B 785 (by norm_num) ⟨392, by rfl⟩ (by norm_num))
theorem R131813 : Reach 131813 := rs (se 4 (by rfl) ⟨12357, by rfl⟩) (B 24715 (by norm_num) ⟨12357, by rfl⟩ (by norm_num))
theorem R66293 : Reach 66293 := rs (se 5 (by rfl) ⟨3107, by rfl⟩) (B 6215 (by norm_num) ⟨3107, by rfl⟩ (by norm_num))
theorem R33529 : Reach 33529 := rs (se 2 (by rfl) ⟨12573, by rfl⟩) (B 25147 (by norm_num) ⟨12573, by rfl⟩ (by norm_num))
theorem R33565 : Reach 33565 := rs (se 3 (by rfl) ⟨6293, by rfl⟩) (B 12587 (by norm_num) ⟨6293, by rfl⟩ (by norm_num))
theorem R33581 : Reach 33581 := rs (se 3 (by rfl) ⟨6296, by rfl⟩) (B 12593 (by norm_num) ⟨6296, by rfl⟩ (by norm_num))
theorem R66365 : Reach 66365 := rs (se 3 (by rfl) ⟨12443, by rfl⟩) (B 24887 (by norm_num) ⟨12443, by rfl⟩ (by norm_num))
theorem R33601 : Reach 33601 := rs (se 2 (by rfl) ⟨12600, by rfl⟩) (B 25201 (by norm_num) ⟨12600, by rfl⟩ (by norm_num))
theorem R33637 : Reach 33637 := rs (se 4 (by rfl) ⟨3153, by rfl⟩) (B 6307 (by norm_num) ⟨3153, by rfl⟩ (by norm_num))
theorem R66437 : Reach 66437 := rs (se 4 (by rfl) ⟨6228, by rfl⟩) (B 12457 (by norm_num) ⟨6228, by rfl⟩ (by norm_num))
theorem R33673 : Reach 33673 := rs (se 2 (by rfl) ⟨12627, by rfl⟩) (B 25255 (by norm_num) ⟨12627, by rfl⟩ (by norm_num))
theorem R33709 : Reach 33709 := rs (se 3 (by rfl) ⟨6320, by rfl⟩) (B 12641 (by norm_num) ⟨6320, by rfl⟩ (by norm_num))
theorem R66509 : Reach 66509 := rs (se 3 (by rfl) ⟨12470, by rfl⟩) (B 24941 (by norm_num) ⟨12470, by rfl⟩ (by norm_num))
theorem R33745 : Reach 33745 := rs (se 2 (by rfl) ⟨12654, by rfl⟩) (B 25309 (by norm_num) ⟨12654, by rfl⟩ (by norm_num))
theorem R33781 : Reach 33781 := rs (se 5 (by rfl) ⟨1583, by rfl⟩) (B 3167 (by norm_num) ⟨1583, by rfl⟩ (by norm_num))
theorem R66581 : Reach 66581 := rs (se 6 (by rfl) ⟨1560, by rfl⟩) (B 3121 (by norm_num) ⟨1560, by rfl⟩ (by norm_num))
theorem R33817 : Reach 33817 := rs (se 2 (by rfl) ⟨12681, by rfl⟩) (B 25363 (by norm_num) ⟨12681, by rfl⟩ (by norm_num))
theorem R33853 : Reach 33853 := rs (se 3 (by rfl) ⟨6347, by rfl⟩) (B 12695 (by norm_num) ⟨6347, by rfl⟩ (by norm_num))
theorem R33869 : Reach 33869 := rs (se 3 (by rfl) ⟨6350, by rfl⟩) (B 12701 (by norm_num) ⟨6350, by rfl⟩ (by norm_num))
theorem R99413 : Reach 99413 := rs (se 8 (by rfl) ⟨582, by rfl⟩) (B 1165 (by norm_num) ⟨582, by rfl⟩ (by norm_num))
theorem R66653 : Reach 66653 := rs (se 3 (by rfl) ⟨12497, by rfl⟩) (B 24995 (by norm_num) ⟨12497, by rfl⟩ (by norm_num))
theorem R33889 : Reach 33889 := rs (se 2 (by rfl) ⟨12708, by rfl⟩) (B 25417 (by norm_num) ⟨12708, by rfl⟩ (by norm_num))
theorem R33925 : Reach 33925 := rs (se 4 (by rfl) ⟨3180, by rfl⟩) (B 6361 (by norm_num) ⟨3180, by rfl⟩ (by norm_num))
theorem R33953 : Reach 33953 := rs (se 2 (by rfl) ⟨12732, by rfl⟩) (B 25465 (by norm_num) ⟨12732, by rfl⟩ (by norm_num))
theorem R66725 : Reach 66725 := rs (se 4 (by rfl) ⟨6255, by rfl⟩) (B 12511 (by norm_num) ⟨6255, by rfl⟩ (by norm_num))
theorem R33961 : Reach 33961 := rs (se 2 (by rfl) ⟨12735, by rfl⟩) (B 25471 (by norm_num) ⟨12735, by rfl⟩ (by norm_num))
theorem R33997 : Reach 33997 := rs (se 3 (by rfl) ⟨6374, by rfl⟩) (B 12749 (by norm_num) ⟨6374, by rfl⟩ (by norm_num))
theorem R66797 : Reach 66797 := rs (se 3 (by rfl) ⟨12524, by rfl⟩) (B 25049 (by norm_num) ⟨12524, by rfl⟩ (by norm_num))
theorem R34033 : Reach 34033 := rs (se 2 (by rfl) ⟨12762, by rfl⟩) (B 25525 (by norm_num) ⟨12762, by rfl⟩ (by norm_num))
theorem R99589 : Reach 99589 := rs (se 4 (by rfl) ⟨9336, by rfl⟩) (B 18673 (by norm_num) ⟨9336, by rfl⟩ (by norm_num))
theorem R34061 : Reach 34061 := rs (se 3 (by rfl) ⟨6386, by rfl⟩) (B 12773 (by norm_num) ⟨6386, by rfl⟩ (by norm_num))
theorem R197909 : Reach 197909 := rs (se 6 (by rfl) ⟨4638, by rfl⟩) (B 9277 (by norm_num) ⟨4638, by rfl⟩ (by norm_num))
theorem R34069 : Reach 34069 := rs (se 6 (by rfl) ⟨798, by rfl⟩) (B 1597 (by norm_num) ⟨798, by rfl⟩ (by norm_num))
theorem R66869 : Reach 66869 := rs (se 5 (by rfl) ⟨3134, by rfl⟩) (B 6269 (by norm_num) ⟨3134, by rfl⟩ (by norm_num))
theorem R34105 : Reach 34105 := rs (se 2 (by rfl) ⟨12789, by rfl⟩) (B 25579 (by norm_num) ⟨12789, by rfl⟩ (by norm_num))
theorem R34121 : Reach 34121 := rs (se 2 (by rfl) ⟨12795, by rfl⟩) (B 25591 (by norm_num) ⟨12795, by rfl⟩ (by norm_num))
theorem R34141 : Reach 34141 := rs (se 3 (by rfl) ⟨6401, by rfl⟩) (B 12803 (by norm_num) ⟨6401, by rfl⟩ (by norm_num))
theorem R66941 : Reach 66941 := rs (se 3 (by rfl) ⟨12551, by rfl⟩) (B 25103 (by norm_num) ⟨12551, by rfl⟩ (by norm_num))
theorem R34177 : Reach 34177 := rs (se 2 (by rfl) ⟨12816, by rfl⟩) (B 25633 (by norm_num) ⟨12816, by rfl⟩ (by norm_num))
theorem R99733 : Reach 99733 := rs (se 6 (by rfl) ⟨2337, by rfl⟩) (B 4675 (by norm_num) ⟨2337, by rfl⟩ (by norm_num))
theorem R34213 : Reach 34213 := rs (se 4 (by rfl) ⟨3207, by rfl⟩) (B 6415 (by norm_num) ⟨3207, by rfl⟩ (by norm_num))
theorem R66989 : Reach 66989 := rs (se 3 (by rfl) ⟨12560, by rfl⟩) (B 25121 (by norm_num) ⟨12560, by rfl⟩ (by norm_num))
theorem R67013 : Reach 67013 := rs (se 4 (by rfl) ⟨6282, by rfl⟩) (B 12565 (by norm_num) ⟨6282, by rfl⟩ (by norm_num))
theorem R34249 : Reach 34249 := rs (se 2 (by rfl) ⟨12843, by rfl⟩) (B 25687 (by norm_num) ⟨12843, by rfl⟩ (by norm_num))
theorem R34273 : Reach 34273 := rs (se 2 (by rfl) ⟨12852, by rfl⟩) (B 25705 (by norm_num) ⟨12852, by rfl⟩ (by norm_num))
theorem R34285 : Reach 34285 := rs (se 3 (by rfl) ⟨6428, by rfl⟩) (B 12857 (by norm_num) ⟨6428, by rfl⟩ (by norm_num))
theorem R99845 : Reach 99845 := rs (se 4 (by rfl) ⟨9360, by rfl⟩) (B 18721 (by norm_num) ⟨9360, by rfl⟩ (by norm_num))
theorem R67085 : Reach 67085 := rs (se 3 (by rfl) ⟨12578, by rfl⟩) (B 25157 (by norm_num) ⟨12578, by rfl⟩ (by norm_num))
theorem R34321 : Reach 34321 := rs (se 2 (by rfl) ⟨12870, by rfl⟩) (B 25741 (by norm_num) ⟨12870, by rfl⟩ (by norm_num))
theorem R198197 : Reach 198197 := rs (se 5 (by rfl) ⟨9290, by rfl⟩) (B 18581 (by norm_num) ⟨9290, by rfl⟩ (by norm_num))
theorem R34357 : Reach 34357 := rs (se 5 (by rfl) ⟨1610, by rfl⟩) (B 3221 (by norm_num) ⟨1610, by rfl⟩ (by norm_num))
theorem R67157 : Reach 67157 := rs (se 8 (by rfl) ⟨393, by rfl⟩) (B 787 (by norm_num) ⟨393, by rfl⟩ (by norm_num))
theorem R34393 : Reach 34393 := rs (se 2 (by rfl) ⟨12897, by rfl⟩) (B 25795 (by norm_num) ⟨12897, by rfl⟩ (by norm_num))
theorem R34429 : Reach 34429 := rs (se 3 (by rfl) ⟨6455, by rfl⟩) (B 12911 (by norm_num) ⟨6455, by rfl⟩ (by norm_num))
theorem R34445 : Reach 34445 := rs (se 3 (by rfl) ⟨6458, by rfl⟩) (B 12917 (by norm_num) ⟨6458, by rfl⟩ (by norm_num))
theorem R67229 : Reach 67229 := rs (se 3 (by rfl) ⟨12605, by rfl⟩) (B 25211 (by norm_num) ⟨12605, by rfl⟩ (by norm_num))
theorem R34465 : Reach 34465 := rs (se 2 (by rfl) ⟨12924, by rfl⟩) (B 25849 (by norm_num) ⟨12924, by rfl⟩ (by norm_num))
theorem R34501 : Reach 34501 := rs (se 4 (by rfl) ⟨3234, by rfl⟩) (B 6469 (by norm_num) ⟨3234, by rfl⟩ (by norm_num))
theorem R67301 : Reach 67301 := rs (se 4 (by rfl) ⟨6309, by rfl⟩) (B 12619 (by norm_num) ⟨6309, by rfl⟩ (by norm_num))
theorem R34537 : Reach 34537 := rs (se 2 (by rfl) ⟨12951, by rfl⟩) (B 25903 (by norm_num) ⟨12951, by rfl⟩ (by norm_num))
theorem R34573 : Reach 34573 := rs (se 3 (by rfl) ⟨6482, by rfl⟩) (B 12965 (by norm_num) ⟨6482, by rfl⟩ (by norm_num))
theorem R34597 : Reach 34597 := rs (se 4 (by rfl) ⟨3243, by rfl⟩) (B 6487 (by norm_num) ⟨3243, by rfl⟩ (by norm_num))
theorem R67373 : Reach 67373 := rs (se 3 (by rfl) ⟨12632, by rfl⟩) (B 25265 (by norm_num) ⟨12632, by rfl⟩ (by norm_num))
theorem R34609 : Reach 34609 := rs (se 2 (by rfl) ⟨12978, by rfl⟩) (B 25957 (by norm_num) ⟨12978, by rfl⟩ (by norm_num))
theorem R34645 : Reach 34645 := rs (se 9 (by rfl) ⟨101, by rfl⟩) (B 203 (by norm_num) ⟨101, by rfl⟩ (by norm_num))
theorem R67445 : Reach 67445 := rs (se 5 (by rfl) ⟨3161, by rfl⟩) (B 6323 (by norm_num) ⟨3161, by rfl⟩ (by norm_num))
theorem R34681 : Reach 34681 := rs (se 2 (by rfl) ⟨13005, by rfl⟩) (B 26011 (by norm_num) ⟨13005, by rfl⟩ (by norm_num))
theorem R132997 : Reach 132997 := rs (se 4 (by rfl) ⟨12468, by rfl⟩) (B 24937 (by norm_num) ⟨12468, by rfl⟩ (by norm_num))
theorem R34717 : Reach 34717 := rs (se 3 (by rfl) ⟨6509, by rfl⟩) (B 13019 (by norm_num) ⟨6509, by rfl⟩ (by norm_num))
theorem R100277 : Reach 100277 := rs (se 5 (by rfl) ⟨4700, by rfl⟩) (B 9401 (by norm_num) ⟨4700, by rfl⟩ (by norm_num))
theorem R67517 : Reach 67517 := rs (se 3 (by rfl) ⟨12659, by rfl⟩) (B 25319 (by norm_num) ⟨12659, by rfl⟩ (by norm_num))
theorem R34753 : Reach 34753 := rs (se 2 (by rfl) ⟨13032, by rfl⟩) (B 26065 (by norm_num) ⟨13032, by rfl⟩ (by norm_num))
theorem R34769 : Reach 34769 := rs (se 2 (by rfl) ⟨13038, by rfl⟩) (B 26077 (by norm_num) ⟨13038, by rfl⟩ (by norm_num))
theorem R165845 : Reach 165845 := rs (se 7 (by rfl) ⟨1943, by rfl⟩) (B 3887 (by norm_num) ⟨1943, by rfl⟩ (by norm_num))
theorem R34789 : Reach 34789 := rs (se 4 (by rfl) ⟨3261, by rfl⟩) (B 6523 (by norm_num) ⟨3261, by rfl⟩ (by norm_num))
theorem R67589 : Reach 67589 := rs (se 4 (by rfl) ⟨6336, by rfl⟩) (B 12673 (by norm_num) ⟨6336, by rfl⟩ (by norm_num))
theorem R34825 : Reach 34825 := rs (se 2 (by rfl) ⟨13059, by rfl⟩) (B 26119 (by norm_num) ⟨13059, by rfl⟩ (by norm_num))
theorem R133157 : Reach 133157 := rs (se 4 (by rfl) ⟨12483, by rfl⟩) (B 24967 (by norm_num) ⟨12483, by rfl⟩ (by norm_num))
theorem R34861 : Reach 34861 := rs (se 3 (by rfl) ⟨6536, by rfl⟩) (B 13073 (by norm_num) ⟨6536, by rfl⟩ (by norm_num))
theorem R67661 : Reach 67661 := rs (se 3 (by rfl) ⟨12686, by rfl⟩) (B 25373 (by norm_num) ⟨12686, by rfl⟩ (by norm_num))
theorem R34897 : Reach 34897 := rs (se 2 (by rfl) ⟨13086, by rfl⟩) (B 26173 (by norm_num) ⟨13086, by rfl⟩ (by norm_num))
theorem R34921 : Reach 34921 := rs (se 2 (by rfl) ⟨13095, by rfl⟩) (B 26191 (by norm_num) ⟨13095, by rfl⟩ (by norm_num))
theorem R34933 : Reach 34933 := rs (se 5 (by rfl) ⟨1637, by rfl⟩) (B 3275 (by norm_num) ⟨1637, by rfl⟩ (by norm_num))
theorem R67733 : Reach 67733 := rs (se 6 (by rfl) ⟨1587, by rfl⟩) (B 3175 (by norm_num) ⟨1587, by rfl⟩ (by norm_num))
theorem R34969 : Reach 34969 := rs (se 2 (by rfl) ⟨13113, by rfl⟩) (B 26227 (by norm_num) ⟨13113, by rfl⟩ (by norm_num))
theorem R67805 : Reach 67805 := rs (se 3 (by rfl) ⟨12713, by rfl⟩) (B 25427 (by norm_num) ⟨12713, by rfl⟩ (by norm_num))
theorem R35057 : Reach 35057 := rs (se 2 (by rfl) ⟨13146, by rfl⟩) (B 26293 (by norm_num) ⟨13146, by rfl⟩ (by norm_num))
theorem R35093 : Reach 35093 := rs (se 6 (by rfl) ⟨822, by rfl⟩) (B 1645 (by norm_num) ⟨822, by rfl⟩ (by norm_num))
theorem R67877 : Reach 67877 := rs (se 4 (by rfl) ⟨6363, by rfl⟩) (B 12727 (by norm_num) ⟨6363, by rfl⟩ (by norm_num))
theorem R35149 : Reach 35149 := rs (se 3 (by rfl) ⟨6590, by rfl⟩) (B 13181 (by norm_num) ⟨6590, by rfl⟩ (by norm_num))
theorem R100709 : Reach 100709 := rs (se 4 (by rfl) ⟨9441, by rfl⟩) (B 18883 (by norm_num) ⟨9441, by rfl⟩ (by norm_num))
theorem R67949 : Reach 67949 := rs (se 3 (by rfl) ⟨12740, by rfl⟩) (B 25481 (by norm_num) ⟨12740, by rfl⟩ (by norm_num))
theorem R35245 : Reach 35245 := rs (se 3 (by rfl) ⟨6608, by rfl⟩) (B 13217 (by norm_num) ⟨6608, by rfl⟩ (by norm_num))
theorem R68021 : Reach 68021 := rs (se 5 (by rfl) ⟨3188, by rfl⟩) (B 6377 (by norm_num) ⟨3188, by rfl⟩ (by norm_num))
theorem R68045 : Reach 68045 := rs (se 3 (by rfl) ⟨12758, by rfl⟩) (B 25517 (by norm_num) ⟨12758, by rfl⟩ (by norm_num))
theorem R68093 : Reach 68093 := rs (se 3 (by rfl) ⟨12767, by rfl⟩) (B 25535 (by norm_num) ⟨12767, by rfl⟩ (by norm_num))
theorem R68117 : Reach 68117 := rs (se 6 (by rfl) ⟨1596, by rfl⟩) (B 3193 (by norm_num) ⟨1596, by rfl⟩ (by norm_num))
theorem R68165 : Reach 68165 := rs (se 4 (by rfl) ⟨6390, by rfl⟩) (B 12781 (by norm_num) ⟨6390, by rfl⟩ (by norm_num))
theorem R35417 : Reach 35417 := rs (se 2 (by rfl) ⟨13281, by rfl⟩) (B 26563 (by norm_num) ⟨13281, by rfl⟩ (by norm_num))
theorem R68237 : Reach 68237 := rs (se 3 (by rfl) ⟨12794, by rfl⟩) (B 25589 (by norm_num) ⟨12794, by rfl⟩ (by norm_num))
theorem R35473 : Reach 35473 := rs (se 2 (by rfl) ⟨13302, by rfl⟩) (B 26605 (by norm_num) ⟨13302, by rfl⟩ (by norm_num))
theorem R68309 : Reach 68309 := rs (se 7 (by rfl) ⟨800, by rfl⟩) (B 1601 (by norm_num) ⟨800, by rfl⟩ (by norm_num))
theorem R35569 : Reach 35569 := rs (se 2 (by rfl) ⟨13338, by rfl⟩) (B 26677 (by norm_num) ⟨13338, by rfl⟩ (by norm_num))
theorem R101141 : Reach 101141 := rs (se 6 (by rfl) ⟨2370, by rfl⟩) (B 4741 (by norm_num) ⟨2370, by rfl⟩ (by norm_num))
theorem R68381 : Reach 68381 := rs (se 3 (by rfl) ⟨12821, by rfl⟩) (B 25643 (by norm_num) ⟨12821, by rfl⟩ (by norm_num))
theorem R68453 : Reach 68453 := rs (se 4 (by rfl) ⟨6417, by rfl⟩) (B 12835 (by norm_num) ⟨6417, by rfl⟩ (by norm_num))
theorem R166805 : Reach 166805 := rs (se 6 (by rfl) ⟨3909, by rfl⟩) (B 7819 (by norm_num) ⟨3909, by rfl⟩ (by norm_num))
theorem R35741 : Reach 35741 := rs (se 3 (by rfl) ⟨6701, by rfl⟩) (B 13403 (by norm_num) ⟨6701, by rfl⟩ (by norm_num))
theorem R68525 : Reach 68525 := rs (se 3 (by rfl) ⟨12848, by rfl⟩) (B 25697 (by norm_num) ⟨12848, by rfl⟩ (by norm_num))
theorem R35797 : Reach 35797 := rs (se 7 (by rfl) ⟨419, by rfl⟩) (B 839 (by norm_num) ⟨419, by rfl⟩ (by norm_num))
theorem R68597 : Reach 68597 := rs (se 5 (by rfl) ⟨3215, by rfl⟩) (B 6431 (by norm_num) ⟨3215, by rfl⟩ (by norm_num))
theorem R35893 : Reach 35893 := rs (se 5 (by rfl) ⟨1682, by rfl⟩) (B 3365 (by norm_num) ⟨1682, by rfl⟩ (by norm_num))
theorem R68669 : Reach 68669 := rs (se 3 (by rfl) ⟨12875, by rfl⟩) (B 25751 (by norm_num) ⟨12875, by rfl⟩ (by norm_num))
theorem R68677 : Reach 68677 := rs (se 4 (by rfl) ⟨6438, by rfl⟩) (B 12877 (by norm_num) ⟨6438, by rfl⟩ (by norm_num))
theorem R68741 : Reach 68741 := rs (se 4 (by rfl) ⟨6444, by rfl⟩) (B 12889 (by norm_num) ⟨6444, by rfl⟩ (by norm_num))
theorem R68789 : Reach 68789 := rs (se 5 (by rfl) ⟨3224, by rfl⟩) (B 6449 (by norm_num) ⟨3224, by rfl⟩ (by norm_num))
theorem R101573 : Reach 101573 := rs (se 4 (by rfl) ⟨9522, by rfl⟩) (B 19045 (by norm_num) ⟨9522, by rfl⟩ (by norm_num))
theorem R68813 : Reach 68813 := rs (se 3 (by rfl) ⟨12902, by rfl⟩) (B 25805 (by norm_num) ⟨12902, by rfl⟩ (by norm_num))
theorem R330965 : Reach 330965 := rs (se 7 (by rfl) ⟨3878, by rfl⟩) (B 7757 (by norm_num) ⟨3878, by rfl⟩ (by norm_num))
theorem R36065 : Reach 36065 := rs (se 2 (by rfl) ⟨13524, by rfl⟩) (B 27049 (by norm_num) ⟨13524, by rfl⟩ (by norm_num))
theorem R36077 : Reach 36077 := rs (se 3 (by rfl) ⟨6764, by rfl⟩) (B 13529 (by norm_num) ⟨6764, by rfl⟩ (by norm_num))
theorem R68885 : Reach 68885 := rs (se 6 (by rfl) ⟨1614, by rfl⟩) (B 3229 (by norm_num) ⟨1614, by rfl⟩ (by norm_num))
theorem R36121 : Reach 36121 := rs (se 2 (by rfl) ⟨13545, by rfl⟩) (B 27091 (by norm_num) ⟨13545, by rfl⟩ (by norm_num))
theorem R36137 : Reach 36137 := rs (se 2 (by rfl) ⟨13551, by rfl⟩) (B 27103 (by norm_num) ⟨13551, by rfl⟩ (by norm_num))
theorem R68957 : Reach 68957 := rs (se 3 (by rfl) ⟨12929, by rfl⟩) (B 25859 (by norm_num) ⟨12929, by rfl⟩ (by norm_num))
theorem R69029 : Reach 69029 := rs (se 4 (by rfl) ⟨6471, by rfl⟩) (B 12943 (by norm_num) ⟨6471, by rfl⟩ (by norm_num))
theorem R36325 : Reach 36325 := rs (se 4 (by rfl) ⟨3405, by rfl⟩) (B 6811 (by norm_num) ⟨3405, by rfl⟩ (by norm_num))
theorem R69101 : Reach 69101 := rs (se 3 (by rfl) ⟨12956, by rfl⟩) (B 25913 (by norm_num) ⟨12956, by rfl⟩ (by norm_num))
theorem R69133 : Reach 69133 := rs (se 3 (by rfl) ⟨12962, by rfl⟩) (B 25925 (by norm_num) ⟨12962, by rfl⟩ (by norm_num))
theorem R36389 : Reach 36389 := rs (se 4 (by rfl) ⟨3411, by rfl⟩) (B 6823 (by norm_num) ⟨3411, by rfl⟩ (by norm_num))
theorem R69173 : Reach 69173 := rs (se 5 (by rfl) ⟨3242, by rfl⟩) (B 6485 (by norm_num) ⟨3242, by rfl⟩ (by norm_num))
theorem R36445 : Reach 36445 := rs (se 3 (by rfl) ⟨6833, by rfl⟩) (B 13667 (by norm_num) ⟨6833, by rfl⟩ (by norm_num))
theorem R102005 : Reach 102005 := rs (se 5 (by rfl) ⟨4781, by rfl⟩) (B 9563 (by norm_num) ⟨4781, by rfl⟩ (by norm_num))
theorem R69245 : Reach 69245 := rs (se 3 (by rfl) ⟨12983, by rfl⟩) (B 25967 (by norm_num) ⟨12983, by rfl⟩ (by norm_num))
theorem R36541 : Reach 36541 := rs (se 3 (by rfl) ⟨6851, by rfl⟩) (B 13703 (by norm_num) ⟨6851, by rfl⟩ (by norm_num))
theorem R69317 : Reach 69317 := rs (se 4 (by rfl) ⟨6498, by rfl⟩) (B 12997 (by norm_num) ⟨6498, by rfl⟩ (by norm_num))
theorem R69389 : Reach 69389 := rs (se 3 (by rfl) ⟨13010, by rfl⟩) (B 26021 (by norm_num) ⟨13010, by rfl⟩ (by norm_num))
theorem R36661 : Reach 36661 := rs (se 5 (by rfl) ⟨1718, by rfl⟩) (B 3437 (by norm_num) ⟨1718, by rfl⟩ (by norm_num))
theorem R69437 : Reach 69437 := rs (se 3 (by rfl) ⟨13019, by rfl⟩) (B 26039 (by norm_num) ⟨13019, by rfl⟩ (by norm_num))
theorem R69461 : Reach 69461 := rs (se 9 (by rfl) ⟨203, by rfl⟩) (B 407 (by norm_num) ⟨203, by rfl⟩ (by norm_num))
theorem R69533 : Reach 69533 := rs (se 3 (by rfl) ⟨13037, by rfl⟩) (B 26075 (by norm_num) ⟨13037, by rfl⟩ (by norm_num))
theorem R36829 : Reach 36829 := rs (se 3 (by rfl) ⟨6905, by rfl⟩) (B 13811 (by norm_num) ⟨6905, by rfl⟩ (by norm_num))
theorem R69605 : Reach 69605 := rs (se 4 (by rfl) ⟨6525, by rfl⟩) (B 13051 (by norm_num) ⟨6525, by rfl⟩ (by norm_num))
theorem R102437 : Reach 102437 := rs (se 4 (by rfl) ⟨9603, by rfl⟩) (B 19207 (by norm_num) ⟨9603, by rfl⟩ (by norm_num))
theorem R69677 : Reach 69677 := rs (se 3 (by rfl) ⟨13064, by rfl⟩) (B 26129 (by norm_num) ⟨13064, by rfl⟩ (by norm_num))
theorem R69749 : Reach 69749 := rs (se 5 (by rfl) ⟨3269, by rfl⟩) (B 6539 (by norm_num) ⟨3269, by rfl⟩ (by norm_num))
theorem R69781 : Reach 69781 := rs (se 6 (by rfl) ⟨1635, by rfl⟩) (B 3271 (by norm_num) ⟨1635, by rfl⟩ (by norm_num))
theorem R102565 : Reach 102565 := rs (se 4 (by rfl) ⟨9615, by rfl⟩) (B 19231 (by norm_num) ⟨9615, by rfl⟩ (by norm_num))
theorem R37037 : Reach 37037 := rs (se 3 (by rfl) ⟨6944, by rfl⟩) (B 13889 (by norm_num) ⟨6944, by rfl⟩ (by norm_num))
theorem R69821 : Reach 69821 := rs (se 3 (by rfl) ⟨13091, by rfl⟩) (B 26183 (by norm_num) ⟨13091, by rfl⟩ (by norm_num))
theorem R37093 : Reach 37093 := rs (se 4 (by rfl) ⟨3477, by rfl⟩) (B 6955 (by norm_num) ⟨3477, by rfl⟩ (by norm_num))
theorem R69893 : Reach 69893 := rs (se 4 (by rfl) ⟨6552, by rfl⟩) (B 13105 (by norm_num) ⟨6552, by rfl⟩ (by norm_num))
theorem R299285 : Reach 299285 := rs (se 6 (by rfl) ⟨7014, by rfl⟩) (B 14029 (by norm_num) ⟨7014, by rfl⟩ (by norm_num))
theorem R37189 : Reach 37189 := rs (se 4 (by rfl) ⟨3486, by rfl⟩) (B 6973 (by norm_num) ⟨3486, by rfl⟩ (by norm_num))
theorem R69965 : Reach 69965 := rs (se 3 (by rfl) ⟨13118, by rfl⟩) (B 26237 (by norm_num) ⟨13118, by rfl⟩ (by norm_num))
theorem R70085 : Reach 70085 := rs (se 4 (by rfl) ⟨6570, by rfl⟩) (B 13141 (by norm_num) ⟨6570, by rfl⟩ (by norm_num))
theorem R102869 : Reach 102869 := rs (se 7 (by rfl) ⟨1205, by rfl⟩) (B 2411 (by norm_num) ⟨1205, by rfl⟩ (by norm_num))
theorem R70237 : Reach 70237 := rs (se 3 (by rfl) ⟨13169, by rfl⟩) (B 26339 (by norm_num) ⟨13169, by rfl⟩ (by norm_num))
theorem R135845 : Reach 135845 := rs (se 4 (by rfl) ⟨12735, by rfl⟩) (B 25471 (by norm_num) ⟨12735, by rfl⟩ (by norm_num))
theorem R70429 : Reach 70429 := rs (se 3 (by rfl) ⟨13205, by rfl⟩) (B 26411 (by norm_num) ⟨13205, by rfl⟩ (by norm_num))
theorem R37685 : Reach 37685 := rs (se 5 (by rfl) ⟨1766, by rfl⟩) (B 3533 (by norm_num) ⟨1766, by rfl⟩ (by norm_num))
theorem R299861 : Reach 299861 := rs (se 9 (by rfl) ⟨878, by rfl⟩) (B 1757 (by norm_num) ⟨878, by rfl⟩ (by norm_num))
theorem R37741 : Reach 37741 := rs (se 3 (by rfl) ⟨7076, by rfl⟩) (B 14153 (by norm_num) ⟨7076, by rfl⟩ (by norm_num))
theorem R103301 : Reach 103301 := rs (se 4 (by rfl) ⟨9684, by rfl⟩) (B 19369 (by norm_num) ⟨9684, by rfl⟩ (by norm_num))
theorem R70541 : Reach 70541 := rs (se 3 (by rfl) ⟨13226, by rfl⟩) (B 26453 (by norm_num) ⟨13226, by rfl⟩ (by norm_num))
theorem R37837 : Reach 37837 := rs (se 3 (by rfl) ⟨7094, by rfl⟩) (B 14189 (by norm_num) ⟨7094, by rfl⟩ (by norm_num))
theorem R37877 : Reach 37877 := rs (se 5 (by rfl) ⟨1775, by rfl⟩) (B 3551 (by norm_num) ⟨1775, by rfl⟩ (by norm_num))
theorem R70733 : Reach 70733 := rs (se 3 (by rfl) ⟨13262, by rfl⟩) (B 26525 (by norm_num) ⟨13262, by rfl⟩ (by norm_num))
theorem R103733 : Reach 103733 := rs (se 5 (by rfl) ⟨4862, by rfl⟩) (B 9725 (by norm_num) ⟨4862, by rfl⟩ (by norm_num))
theorem R71077 : Reach 71077 := rs (se 4 (by rfl) ⟨6663, by rfl⟩) (B 13327 (by norm_num) ⟨6663, by rfl⟩ (by norm_num))
theorem R38333 : Reach 38333 := rs (se 3 (by rfl) ⟨7187, by rfl⟩) (B 14375 (by norm_num) ⟨7187, by rfl⟩ (by norm_num))
theorem R38341 : Reach 38341 := rs (se 4 (by rfl) ⟨3594, by rfl⟩) (B 7189 (by norm_num) ⟨3594, by rfl⟩ (by norm_num))
theorem R38389 : Reach 38389 := rs (se 5 (by rfl) ⟨1799, by rfl⟩) (B 3599 (by norm_num) ⟨1799, by rfl⟩ (by norm_num))
theorem R71189 : Reach 71189 := rs (se 6 (by rfl) ⟨1668, by rfl⟩) (B 3337 (by norm_num) ⟨1668, by rfl⟩ (by norm_num))
theorem R38485 : Reach 38485 := rs (se 8 (by rfl) ⟨225, by rfl⟩) (B 451 (by norm_num) ⟨225, by rfl⟩ (by norm_num))
theorem R71381 : Reach 71381 := rs (se 7 (by rfl) ⟨836, by rfl⟩) (B 1673 (by norm_num) ⟨836, by rfl⟩ (by norm_num))
theorem R104165 : Reach 104165 := rs (se 4 (by rfl) ⟨9765, by rfl⟩) (B 19531 (by norm_num) ⟨9765, by rfl⟩ (by norm_num))
theorem R136997 : Reach 136997 := rs (se 4 (by rfl) ⟨12843, by rfl⟩) (B 25687 (by norm_num) ⟨12843, by rfl⟩ (by norm_num))
theorem R268181 : Reach 268181 := rs (se 6 (by rfl) ⟨6285, by rfl⟩) (B 12571 (by norm_num) ⟨6285, by rfl⟩ (by norm_num))
theorem R71621 : Reach 71621 := rs (se 4 (by rfl) ⟨6714, by rfl⟩) (B 13429 (by norm_num) ⟨6714, by rfl⟩ (by norm_num))
theorem R71725 : Reach 71725 := rs (se 3 (by rfl) ⟨13448, by rfl⟩) (B 26897 (by norm_num) ⟨13448, by rfl⟩ (by norm_num))
theorem R38981 : Reach 38981 := rs (se 4 (by rfl) ⟨3654, by rfl⟩) (B 7309 (by norm_num) ⟨3654, by rfl⟩ (by norm_num))
theorem R39037 : Reach 39037 := rs (se 3 (by rfl) ⟨7319, by rfl⟩) (B 14639 (by norm_num) ⟨7319, by rfl⟩ (by norm_num))
theorem R71813 : Reach 71813 := rs (se 4 (by rfl) ⟨6732, by rfl⟩) (B 13465 (by norm_num) ⟨6732, by rfl⟩ (by norm_num))
theorem R104597 : Reach 104597 := rs (se 6 (by rfl) ⟨2451, by rfl⟩) (B 4903 (by norm_num) ⟨2451, by rfl⟩ (by norm_num))
theorem R71837 : Reach 71837 := rs (se 3 (by rfl) ⟨13469, by rfl⟩) (B 26939 (by norm_num) ⟨13469, by rfl⟩ (by norm_num))
theorem R39133 : Reach 39133 := rs (se 3 (by rfl) ⟨7337, by rfl⟩) (B 14675 (by norm_num) ⟨7337, by rfl⟩ (by norm_num))
theorem R366869 : Reach 366869 := rs (se 6 (by rfl) ⟨8598, by rfl⟩) (B 17197 (by norm_num) ⟨8598, by rfl⟩ (by norm_num))
theorem R72029 : Reach 72029 := rs (se 3 (by rfl) ⟨13505, by rfl⟩) (B 27011 (by norm_num) ⟨13505, by rfl⟩ (by norm_num))
theorem R104885 : Reach 104885 := rs (se 5 (by rfl) ⟨4916, by rfl⟩) (B 9833 (by norm_num) ⟨4916, by rfl⟩ (by norm_num))
theorem R39469 : Reach 39469 := rs (se 3 (by rfl) ⟨7400, by rfl⟩) (B 14801 (by norm_num) ⟨7400, by rfl⟩ (by norm_num))
theorem R203381 : Reach 203381 := rs (se 5 (by rfl) ⟨9533, by rfl⟩) (B 19067 (by norm_num) ⟨9533, by rfl⟩ (by norm_num))
theorem R137861 : Reach 137861 := rs (se 4 (by rfl) ⟨12924, by rfl⟩) (B 25849 (by norm_num) ⟨12924, by rfl⟩ (by norm_num))
theorem R72325 : Reach 72325 := rs (se 4 (by rfl) ⟨6780, by rfl⟩) (B 13561 (by norm_num) ⟨6780, by rfl⟩ (by norm_num))
theorem R72373 : Reach 72373 := rs (se 5 (by rfl) ⟨3392, by rfl⟩) (B 6785 (by norm_num) ⟨3392, by rfl⟩ (by norm_num))
theorem R400085 : Reach 400085 := rs (se 7 (by rfl) ⟨4688, by rfl⟩) (B 9377 (by norm_num) ⟨4688, by rfl⟩ (by norm_num))
theorem R39685 : Reach 39685 := rs (se 4 (by rfl) ⟨3720, by rfl⟩) (B 7441 (by norm_num) ⟨3720, by rfl⟩ (by norm_num))
theorem R72485 : Reach 72485 := rs (se 4 (by rfl) ⟨6795, by rfl⟩) (B 13591 (by norm_num) ⟨6795, by rfl⟩ (by norm_num))
theorem R72581 : Reach 72581 := rs (se 4 (by rfl) ⟨6804, by rfl⟩) (B 13609 (by norm_num) ⟨6804, by rfl⟩ (by norm_num))
theorem R72677 : Reach 72677 := rs (se 4 (by rfl) ⟨6813, by rfl⟩) (B 13627 (by norm_num) ⟨6813, by rfl⟩ (by norm_num))
theorem R40061 : Reach 40061 := rs (se 3 (by rfl) ⟨7511, by rfl⟩) (B 15023 (by norm_num) ⟨7511, by rfl⟩ (by norm_num))
theorem R106069 : Reach 106069 := rs (se 8 (by rfl) ⟨621, by rfl⟩) (B 1243 (by norm_num) ⟨621, by rfl⟩ (by norm_num))
theorem R40685 : Reach 40685 := rs (se 3 (by rfl) ⟨7628, by rfl⟩) (B 15257 (by norm_num) ⟨7628, by rfl⟩ (by norm_num))
theorem R40709 : Reach 40709 := rs (se 4 (by rfl) ⟨3816, by rfl⟩) (B 7633 (by norm_num) ⟨3816, by rfl⟩ (by norm_num))
theorem R40733 : Reach 40733 := rs (se 3 (by rfl) ⟨7637, by rfl⟩) (B 15275 (by norm_num) ⟨7637, by rfl⟩ (by norm_num))
theorem R40757 : Reach 40757 := rs (se 5 (by rfl) ⟨1910, by rfl⟩) (B 3821 (by norm_num) ⟨1910, by rfl⟩ (by norm_num))
theorem R40781 : Reach 40781 := rs (se 3 (by rfl) ⟨7646, by rfl⟩) (B 15293 (by norm_num) ⟨7646, by rfl⟩ (by norm_num))
theorem R40805 : Reach 40805 := rs (se 4 (by rfl) ⟨3825, by rfl⟩) (B 7651 (by norm_num) ⟨3825, by rfl⟩ (by norm_num))
theorem R40829 : Reach 40829 := rs (se 3 (by rfl) ⟨7655, by rfl⟩) (B 15311 (by norm_num) ⟨7655, by rfl⟩ (by norm_num))
theorem R106373 : Reach 106373 := rs (se 4 (by rfl) ⟨9972, by rfl⟩) (B 19945 (by norm_num) ⟨9972, by rfl⟩ (by norm_num))
theorem R40853 : Reach 40853 := rs (se 6 (by rfl) ⟨957, by rfl⟩) (B 1915 (by norm_num) ⟨957, by rfl⟩ (by norm_num))
theorem R139157 : Reach 139157 := rs (se 6 (by rfl) ⟨3261, by rfl⟩) (B 6523 (by norm_num) ⟨3261, by rfl⟩ (by norm_num))
theorem R40877 : Reach 40877 := rs (se 3 (by rfl) ⟨7664, by rfl⟩) (B 15329 (by norm_num) ⟨7664, by rfl⟩ (by norm_num))
theorem R40901 : Reach 40901 := rs (se 4 (by rfl) ⟨3834, by rfl⟩) (B 7669 (by norm_num) ⟨3834, by rfl⟩ (by norm_num))
theorem R73669 : Reach 73669 := rs (se 4 (by rfl) ⟨6906, by rfl⟩) (B 13813 (by norm_num) ⟨6906, by rfl⟩ (by norm_num))
theorem R40925 : Reach 40925 := rs (se 3 (by rfl) ⟨7673, by rfl⟩) (B 15347 (by norm_num) ⟨7673, by rfl⟩ (by norm_num))
theorem R40949 : Reach 40949 := rs (se 5 (by rfl) ⟨1919, by rfl⟩) (B 3839 (by norm_num) ⟨1919, by rfl⟩ (by norm_num))
theorem R40973 : Reach 40973 := rs (se 3 (by rfl) ⟨7682, by rfl⟩) (B 15365 (by norm_num) ⟨7682, by rfl⟩ (by norm_num))
theorem R40997 : Reach 40997 := rs (se 4 (by rfl) ⟨3843, by rfl⟩) (B 7687 (by norm_num) ⟨3843, by rfl⟩ (by norm_num))
theorem R73781 : Reach 73781 := rs (se 5 (by rfl) ⟨3458, by rfl⟩) (B 6917 (by norm_num) ⟨3458, by rfl⟩ (by norm_num))
theorem R41021 : Reach 41021 := rs (se 3 (by rfl) ⟨7691, by rfl⟩) (B 15383 (by norm_num) ⟨7691, by rfl⟩ (by norm_num))
theorem R41045 : Reach 41045 := rs (se 8 (by rfl) ⟨240, by rfl⟩) (B 481 (by norm_num) ⟨240, by rfl⟩ (by norm_num))
theorem R41053 : Reach 41053 := rs (se 3 (by rfl) ⟨7697, by rfl⟩) (B 15395 (by norm_num) ⟨7697, by rfl⟩ (by norm_num))
theorem R41069 : Reach 41069 := rs (se 3 (by rfl) ⟨7700, by rfl⟩) (B 15401 (by norm_num) ⟨7700, by rfl⟩ (by norm_num))
theorem R41093 : Reach 41093 := rs (se 4 (by rfl) ⟨3852, by rfl⟩) (B 7705 (by norm_num) ⟨3852, by rfl⟩ (by norm_num))
theorem R41117 : Reach 41117 := rs (se 3 (by rfl) ⟨7709, by rfl⟩) (B 15419 (by norm_num) ⟨7709, by rfl⟩ (by norm_num))
theorem R41141 : Reach 41141 := rs (se 5 (by rfl) ⟨1928, by rfl⟩) (B 3857 (by norm_num) ⟨1928, by rfl⟩ (by norm_num))
theorem R41165 : Reach 41165 := rs (se 3 (by rfl) ⟨7718, by rfl⟩) (B 15437 (by norm_num) ⟨7718, by rfl⟩ (by norm_num))
theorem R41189 : Reach 41189 := rs (se 4 (by rfl) ⟨3861, by rfl⟩) (B 7723 (by norm_num) ⟨3861, by rfl⟩ (by norm_num))
theorem R73973 : Reach 73973 := rs (se 5 (by rfl) ⟨3467, by rfl⟩) (B 6935 (by norm_num) ⟨3467, by rfl⟩ (by norm_num))
theorem R41213 : Reach 41213 := rs (se 3 (by rfl) ⟨7727, by rfl⟩) (B 15455 (by norm_num) ⟨7727, by rfl⟩ (by norm_num))
theorem R41237 : Reach 41237 := rs (se 6 (by rfl) ⟨966, by rfl⟩) (B 1933 (by norm_num) ⟨966, by rfl⟩ (by norm_num))
theorem R41261 : Reach 41261 := rs (se 3 (by rfl) ⟨7736, by rfl⟩) (B 15473 (by norm_num) ⟨7736, by rfl⟩ (by norm_num))
theorem R41285 : Reach 41285 := rs (se 4 (by rfl) ⟨3870, by rfl⟩) (B 7741 (by norm_num) ⟨3870, by rfl⟩ (by norm_num))
theorem R41309 : Reach 41309 := rs (se 3 (by rfl) ⟨7745, by rfl⟩) (B 15491 (by norm_num) ⟨7745, by rfl⟩ (by norm_num))
theorem R41333 : Reach 41333 := rs (se 5 (by rfl) ⟨1937, by rfl⟩) (B 3875 (by norm_num) ⟨1937, by rfl⟩ (by norm_num))
theorem R41357 : Reach 41357 := rs (se 3 (by rfl) ⟨7754, by rfl⟩) (B 15509 (by norm_num) ⟨7754, by rfl⟩ (by norm_num))
theorem R41381 : Reach 41381 := rs (se 4 (by rfl) ⟨3879, by rfl⟩) (B 7759 (by norm_num) ⟨3879, by rfl⟩ (by norm_num))
theorem R41405 : Reach 41405 := rs (se 3 (by rfl) ⟨7763, by rfl⟩) (B 15527 (by norm_num) ⟨7763, by rfl⟩ (by norm_num))
theorem R41429 : Reach 41429 := rs (se 7 (by rfl) ⟨485, by rfl⟩) (B 971 (by norm_num) ⟨485, by rfl⟩ (by norm_num))
theorem R41453 : Reach 41453 := rs (se 3 (by rfl) ⟨7772, by rfl⟩) (B 15545 (by norm_num) ⟨7772, by rfl⟩ (by norm_num))
theorem R41477 : Reach 41477 := rs (se 4 (by rfl) ⟨3888, by rfl⟩) (B 7777 (by norm_num) ⟨3888, by rfl⟩ (by norm_num))
theorem R139781 : Reach 139781 := rs (se 4 (by rfl) ⟨13104, by rfl⟩) (B 26209 (by norm_num) ⟨13104, by rfl⟩ (by norm_num))
theorem R41485 : Reach 41485 := rs (se 3 (by rfl) ⟨7778, by rfl⟩) (B 15557 (by norm_num) ⟨7778, by rfl⟩ (by norm_num))
theorem R41501 : Reach 41501 := rs (se 3 (by rfl) ⟨7781, by rfl⟩) (B 15563 (by norm_num) ⟨7781, by rfl⟩ (by norm_num))
theorem R41525 : Reach 41525 := rs (se 5 (by rfl) ⟨1946, by rfl⟩) (B 3893 (by norm_num) ⟨1946, by rfl⟩ (by norm_num))
theorem R41549 : Reach 41549 := rs (se 3 (by rfl) ⟨7790, by rfl⟩) (B 15581 (by norm_num) ⟨7790, by rfl⟩ (by norm_num))
theorem R41573 : Reach 41573 := rs (se 4 (by rfl) ⟨3897, by rfl⟩) (B 7795 (by norm_num) ⟨3897, by rfl⟩ (by norm_num))
theorem R41597 : Reach 41597 := rs (se 3 (by rfl) ⟨7799, by rfl⟩) (B 15599 (by norm_num) ⟨7799, by rfl⟩ (by norm_num))
theorem R139909 : Reach 139909 := rs (se 4 (by rfl) ⟨13116, by rfl⟩) (B 26233 (by norm_num) ⟨13116, by rfl⟩ (by norm_num))
theorem R41621 : Reach 41621 := rs (se 6 (by rfl) ⟨975, by rfl⟩) (B 1951 (by norm_num) ⟨975, by rfl⟩ (by norm_num))
theorem R41645 : Reach 41645 := rs (se 3 (by rfl) ⟨7808, by rfl⟩) (B 15617 (by norm_num) ⟨7808, by rfl⟩ (by norm_num))
theorem R107189 : Reach 107189 := rs (se 5 (by rfl) ⟨5024, by rfl⟩) (B 10049 (by norm_num) ⟨5024, by rfl⟩ (by norm_num))
theorem R41669 : Reach 41669 := rs (se 4 (by rfl) ⟨3906, by rfl⟩) (B 7813 (by norm_num) ⟨3906, by rfl⟩ (by norm_num))
theorem R41693 : Reach 41693 := rs (se 3 (by rfl) ⟨7817, by rfl⟩) (B 15635 (by norm_num) ⟨7817, by rfl⟩ (by norm_num))
theorem R107237 : Reach 107237 := rs (se 4 (by rfl) ⟨10053, by rfl⟩) (B 20107 (by norm_num) ⟨10053, by rfl⟩ (by norm_num))
theorem R41717 : Reach 41717 := rs (se 5 (by rfl) ⟨1955, by rfl⟩) (B 3911 (by norm_num) ⟨1955, by rfl⟩ (by norm_num))
theorem R41741 : Reach 41741 := rs (se 3 (by rfl) ⟨7826, by rfl⟩) (B 15653 (by norm_num) ⟨7826, by rfl⟩ (by norm_num))
theorem R41765 : Reach 41765 := rs (se 4 (by rfl) ⟨3915, by rfl⟩) (B 7831 (by norm_num) ⟨3915, by rfl⟩ (by norm_num))
theorem R41789 : Reach 41789 := rs (se 3 (by rfl) ⟨7835, by rfl⟩) (B 15671 (by norm_num) ⟨7835, by rfl⟩ (by norm_num))
theorem R41813 : Reach 41813 := rs (se 9 (by rfl) ⟨122, by rfl⟩) (B 245 (by norm_num) ⟨122, by rfl⟩ (by norm_num))
theorem R107365 : Reach 107365 := rs (se 4 (by rfl) ⟨10065, by rfl⟩) (B 20131 (by norm_num) ⟨10065, by rfl⟩ (by norm_num))
theorem R41837 : Reach 41837 := rs (se 3 (by rfl) ⟨7844, by rfl⟩) (B 15689 (by norm_num) ⟨7844, by rfl⟩ (by norm_num))
theorem R41861 : Reach 41861 := rs (se 4 (by rfl) ⟨3924, by rfl⟩) (B 7849 (by norm_num) ⟨3924, by rfl⟩ (by norm_num))
theorem R41885 : Reach 41885 := rs (se 3 (by rfl) ⟨7853, by rfl⟩) (B 15707 (by norm_num) ⟨7853, by rfl⟩ (by norm_num))
theorem R41909 : Reach 41909 := rs (se 5 (by rfl) ⟨1964, by rfl⟩) (B 3929 (by norm_num) ⟨1964, by rfl⟩ (by norm_num))
theorem R74677 : Reach 74677 := rs (se 5 (by rfl) ⟨3500, by rfl⟩) (B 7001 (by norm_num) ⟨3500, by rfl⟩ (by norm_num))
theorem R41933 : Reach 41933 := rs (se 3 (by rfl) ⟨7862, by rfl⟩) (B 15725 (by norm_num) ⟨7862, by rfl⟩ (by norm_num))
theorem R41941 : Reach 41941 := rs (se 7 (by rfl) ⟨491, by rfl⟩) (B 983 (by norm_num) ⟨491, by rfl⟩ (by norm_num))
theorem R41957 : Reach 41957 := rs (se 4 (by rfl) ⟨3933, by rfl⟩) (B 7867 (by norm_num) ⟨3933, by rfl⟩ (by norm_num))
theorem R41981 : Reach 41981 := rs (se 3 (by rfl) ⟨7871, by rfl⟩) (B 15743 (by norm_num) ⟨7871, by rfl⟩ (by norm_num))
theorem R42005 : Reach 42005 := rs (se 6 (by rfl) ⟨984, by rfl⟩) (B 1969 (by norm_num) ⟨984, by rfl⟩ (by norm_num))
theorem R42029 : Reach 42029 := rs (se 3 (by rfl) ⟨7880, by rfl⟩) (B 15761 (by norm_num) ⟨7880, by rfl⟩ (by norm_num))
theorem R42053 : Reach 42053 := rs (se 4 (by rfl) ⟨3942, by rfl⟩) (B 7885 (by norm_num) ⟨3942, by rfl⟩ (by norm_num))
theorem R42077 : Reach 42077 := rs (se 3 (by rfl) ⟨7889, by rfl⟩) (B 15779 (by norm_num) ⟨7889, by rfl⟩ (by norm_num))
theorem R42101 : Reach 42101 := rs (se 5 (by rfl) ⟨1973, by rfl⟩) (B 3947 (by norm_num) ⟨1973, by rfl⟩ (by norm_num))
theorem R42125 : Reach 42125 := rs (se 3 (by rfl) ⟨7898, by rfl⟩) (B 15797 (by norm_num) ⟨7898, by rfl⟩ (by norm_num))
theorem R140453 : Reach 140453 := rs (se 4 (by rfl) ⟨13167, by rfl⟩) (B 26335 (by norm_num) ⟨13167, by rfl⟩ (by norm_num))
theorem R42149 : Reach 42149 := rs (se 4 (by rfl) ⟨3951, by rfl⟩) (B 7903 (by norm_num) ⟨3951, by rfl⟩ (by norm_num))
theorem R42157 : Reach 42157 := rs (se 3 (by rfl) ⟨7904, by rfl⟩) (B 15809 (by norm_num) ⟨7904, by rfl⟩ (by norm_num))
theorem R42173 : Reach 42173 := rs (se 3 (by rfl) ⟨7907, by rfl⟩) (B 15815 (by norm_num) ⟨7907, by rfl⟩ (by norm_num))
theorem R42197 : Reach 42197 := rs (se 7 (by rfl) ⟨494, by rfl⟩) (B 989 (by norm_num) ⟨494, by rfl⟩ (by norm_num))
theorem R74965 : Reach 74965 := rs (se 7 (by rfl) ⟨878, by rfl⟩) (B 1757 (by norm_num) ⟨878, by rfl⟩ (by norm_num))
theorem R42221 : Reach 42221 := rs (se 3 (by rfl) ⟨7916, by rfl⟩) (B 15833 (by norm_num) ⟨7916, by rfl⟩ (by norm_num))
theorem R140549 : Reach 140549 := rs (se 4 (by rfl) ⟨13176, by rfl⟩) (B 26353 (by norm_num) ⟨13176, by rfl⟩ (by norm_num))
theorem R42245 : Reach 42245 := rs (se 4 (by rfl) ⟨3960, by rfl⟩) (B 7921 (by norm_num) ⟨3960, by rfl⟩ (by norm_num))
theorem R42269 : Reach 42269 := rs (se 3 (by rfl) ⟨7925, by rfl⟩) (B 15851 (by norm_num) ⟨7925, by rfl⟩ (by norm_num))
theorem R42277 : Reach 42277 := rs (se 4 (by rfl) ⟨3963, by rfl⟩) (B 7927 (by norm_num) ⟨3963, by rfl⟩ (by norm_num))
theorem R42293 : Reach 42293 := rs (se 5 (by rfl) ⟨1982, by rfl⟩) (B 3965 (by norm_num) ⟨1982, by rfl⟩ (by norm_num))
theorem R75077 : Reach 75077 := rs (se 4 (by rfl) ⟨7038, by rfl⟩) (B 14077 (by norm_num) ⟨7038, by rfl⟩ (by norm_num))
theorem R42317 : Reach 42317 := rs (se 3 (by rfl) ⟨7934, by rfl⟩) (B 15869 (by norm_num) ⟨7934, by rfl⟩ (by norm_num))
theorem R42341 : Reach 42341 := rs (se 4 (by rfl) ⟨3969, by rfl⟩) (B 7939 (by norm_num) ⟨3969, by rfl⟩ (by norm_num))
theorem R42365 : Reach 42365 := rs (se 3 (by rfl) ⟨7943, by rfl⟩) (B 15887 (by norm_num) ⟨7943, by rfl⟩ (by norm_num))
theorem R42373 : Reach 42373 := rs (se 4 (by rfl) ⟨3972, by rfl⟩) (B 7945 (by norm_num) ⟨3972, by rfl⟩ (by norm_num))
theorem R42389 : Reach 42389 := rs (se 6 (by rfl) ⟨993, by rfl⟩) (B 1987 (by norm_num) ⟨993, by rfl⟩ (by norm_num))
theorem R42413 : Reach 42413 := rs (se 3 (by rfl) ⟨7952, by rfl⟩) (B 15905 (by norm_num) ⟨7952, by rfl⟩ (by norm_num))
theorem R42437 : Reach 42437 := rs (se 4 (by rfl) ⟨3978, by rfl⟩) (B 7957 (by norm_num) ⟨3978, by rfl⟩ (by norm_num))
theorem R42461 : Reach 42461 := rs (se 3 (by rfl) ⟨7961, by rfl⟩) (B 15923 (by norm_num) ⟨7961, by rfl⟩ (by norm_num))
theorem R42485 : Reach 42485 := rs (se 5 (by rfl) ⟨1991, by rfl⟩) (B 3983 (by norm_num) ⟨1991, by rfl⟩ (by norm_num))
theorem R75269 : Reach 75269 := rs (se 4 (by rfl) ⟨7056, by rfl⟩) (B 14113 (by norm_num) ⟨7056, by rfl⟩ (by norm_num))
theorem R42509 : Reach 42509 := rs (se 3 (by rfl) ⟨7970, by rfl⟩) (B 15941 (by norm_num) ⟨7970, by rfl⟩ (by norm_num))
theorem R42533 : Reach 42533 := rs (se 4 (by rfl) ⟨3987, by rfl⟩) (B 7975 (by norm_num) ⟨3987, by rfl⟩ (by norm_num))
theorem R42557 : Reach 42557 := rs (se 3 (by rfl) ⟨7979, by rfl⟩) (B 15959 (by norm_num) ⟨7979, by rfl⟩ (by norm_num))
theorem R42581 : Reach 42581 := rs (se 8 (by rfl) ⟨249, by rfl⟩) (B 499 (by norm_num) ⟨249, by rfl⟩ (by norm_num))
theorem R42605 : Reach 42605 := rs (se 3 (by rfl) ⟨7988, by rfl⟩) (B 15977 (by norm_num) ⟨7988, by rfl⟩ (by norm_num))
theorem R42629 : Reach 42629 := rs (se 4 (by rfl) ⟨3996, by rfl⟩) (B 7993 (by norm_num) ⟨3996, by rfl⟩ (by norm_num))
theorem R42653 : Reach 42653 := rs (se 3 (by rfl) ⟨7997, by rfl⟩) (B 15995 (by norm_num) ⟨7997, by rfl⟩ (by norm_num))
theorem R42677 : Reach 42677 := rs (se 5 (by rfl) ⟨2000, by rfl⟩) (B 4001 (by norm_num) ⟨2000, by rfl⟩ (by norm_num))
theorem R42701 : Reach 42701 := rs (se 3 (by rfl) ⟨8006, by rfl⟩) (B 16013 (by norm_num) ⟨8006, by rfl⟩ (by norm_num))
theorem R206549 : Reach 206549 := rs (se 7 (by rfl) ⟨2420, by rfl⟩) (B 4841 (by norm_num) ⟨2420, by rfl⟩ (by norm_num))
theorem R42725 : Reach 42725 := rs (se 4 (by rfl) ⟨4005, by rfl⟩) (B 8011 (by norm_num) ⟨4005, by rfl⟩ (by norm_num))
theorem R42749 : Reach 42749 := rs (se 3 (by rfl) ⟨8015, by rfl⟩) (B 16031 (by norm_num) ⟨8015, by rfl⟩ (by norm_num))
theorem R42773 : Reach 42773 := rs (se 6 (by rfl) ⟨1002, by rfl⟩) (B 2005 (by norm_num) ⟨1002, by rfl⟩ (by norm_num))
theorem R108325 : Reach 108325 := rs (se 4 (by rfl) ⟨10155, by rfl⟩) (B 20311 (by norm_num) ⟨10155, by rfl⟩ (by norm_num))
theorem R42797 : Reach 42797 := rs (se 3 (by rfl) ⟨8024, by rfl⟩) (B 16049 (by norm_num) ⟨8024, by rfl⟩ (by norm_num))
theorem R42821 : Reach 42821 := rs (se 4 (by rfl) ⟨4014, by rfl⟩) (B 8029 (by norm_num) ⟨4014, by rfl⟩ (by norm_num))
theorem R42845 : Reach 42845 := rs (se 3 (by rfl) ⟨8033, by rfl⟩) (B 16067 (by norm_num) ⟨8033, by rfl⟩ (by norm_num))
theorem R42869 : Reach 42869 := rs (se 5 (by rfl) ⟨2009, by rfl⟩) (B 4019 (by norm_num) ⟨2009, by rfl⟩ (by norm_num))
theorem R42893 : Reach 42893 := rs (se 3 (by rfl) ⟨8042, by rfl⟩) (B 16085 (by norm_num) ⟨8042, by rfl⟩ (by norm_num))
theorem R42917 : Reach 42917 := rs (se 4 (by rfl) ⟨4023, by rfl⟩) (B 8047 (by norm_num) ⟨4023, by rfl⟩ (by norm_num))
theorem R42941 : Reach 42941 := rs (se 3 (by rfl) ⟨8051, by rfl⟩) (B 16103 (by norm_num) ⟨8051, by rfl⟩ (by norm_num))
theorem R108485 : Reach 108485 := rs (se 4 (by rfl) ⟨10170, by rfl⟩) (B 20341 (by norm_num) ⟨10170, by rfl⟩ (by norm_num))
theorem R42965 : Reach 42965 := rs (se 7 (by rfl) ⟨503, by rfl⟩) (B 1007 (by norm_num) ⟨503, by rfl⟩ (by norm_num))
theorem R42989 : Reach 42989 := rs (se 3 (by rfl) ⟨8060, by rfl⟩) (B 16121 (by norm_num) ⟨8060, by rfl⟩ (by norm_num))
theorem R43013 : Reach 43013 := rs (se 4 (by rfl) ⟨4032, by rfl⟩) (B 8065 (by norm_num) ⟨4032, by rfl⟩ (by norm_num))
theorem R43037 : Reach 43037 := rs (se 3 (by rfl) ⟨8069, by rfl⟩) (B 16139 (by norm_num) ⟨8069, by rfl⟩ (by norm_num))
theorem R43061 : Reach 43061 := rs (se 5 (by rfl) ⟨2018, by rfl⟩) (B 4037 (by norm_num) ⟨2018, by rfl⟩ (by norm_num))
theorem R43085 : Reach 43085 := rs (se 3 (by rfl) ⟨8078, by rfl⟩) (B 16157 (by norm_num) ⟨8078, by rfl⟩ (by norm_num))
theorem R43109 : Reach 43109 := rs (se 4 (by rfl) ⟨4041, by rfl⟩) (B 8083 (by norm_num) ⟨4041, by rfl⟩ (by norm_num))
theorem R43133 : Reach 43133 := rs (se 3 (by rfl) ⟨8087, by rfl⟩) (B 16175 (by norm_num) ⟨8087, by rfl⟩ (by norm_num))
theorem R43157 : Reach 43157 := rs (se 6 (by rfl) ⟨1011, by rfl⟩) (B 2023 (by norm_num) ⟨1011, by rfl⟩ (by norm_num))
theorem R43181 : Reach 43181 := rs (se 3 (by rfl) ⟨8096, by rfl⟩) (B 16193 (by norm_num) ⟨8096, by rfl⟩ (by norm_num))
theorem R43205 : Reach 43205 := rs (se 4 (by rfl) ⟨4050, by rfl⟩) (B 8101 (by norm_num) ⟨4050, by rfl⟩ (by norm_num))
theorem R43229 : Reach 43229 := rs (se 3 (by rfl) ⟨8105, by rfl⟩) (B 16211 (by norm_num) ⟨8105, by rfl⟩ (by norm_num))
theorem R108773 : Reach 108773 := rs (se 4 (by rfl) ⟨10197, by rfl⟩) (B 20395 (by norm_num) ⟨10197, by rfl⟩ (by norm_num))
theorem R43253 : Reach 43253 := rs (se 5 (by rfl) ⟨2027, by rfl⟩) (B 4055 (by norm_num) ⟨2027, by rfl⟩ (by norm_num))
theorem R43277 : Reach 43277 := rs (se 3 (by rfl) ⟨8114, by rfl⟩) (B 16229 (by norm_num) ⟨8114, by rfl⟩ (by norm_num))
theorem R43301 : Reach 43301 := rs (se 4 (by rfl) ⟨4059, by rfl⟩) (B 8119 (by norm_num) ⟨4059, by rfl⟩ (by norm_num))
theorem R43325 : Reach 43325 := rs (se 3 (by rfl) ⟨8123, by rfl⟩) (B 16247 (by norm_num) ⟨8123, by rfl⟩ (by norm_num))
theorem R43349 : Reach 43349 := rs (se 10 (by rfl) ⟨63, by rfl⟩) (B 127 (by norm_num) ⟨63, by rfl⟩ (by norm_num))
theorem R43373 : Reach 43373 := rs (se 3 (by rfl) ⟨8132, by rfl⟩) (B 16265 (by norm_num) ⟨8132, by rfl⟩ (by norm_num))
theorem R43397 : Reach 43397 := rs (se 4 (by rfl) ⟨4068, by rfl⟩) (B 8137 (by norm_num) ⟨4068, by rfl⟩ (by norm_num))
theorem R43421 : Reach 43421 := rs (se 3 (by rfl) ⟨8141, by rfl⟩) (B 16283 (by norm_num) ⟨8141, by rfl⟩ (by norm_num))
theorem R141749 : Reach 141749 := rs (se 5 (by rfl) ⟨6644, by rfl⟩) (B 13289 (by norm_num) ⟨6644, by rfl⟩ (by norm_num))
theorem R43445 : Reach 43445 := rs (se 5 (by rfl) ⟨2036, by rfl⟩) (B 4073 (by norm_num) ⟨2036, by rfl⟩ (by norm_num))
theorem R43469 : Reach 43469 := rs (se 3 (by rfl) ⟨8150, by rfl⟩) (B 16301 (by norm_num) ⟨8150, by rfl⟩ (by norm_num))
theorem R43493 : Reach 43493 := rs (se 4 (by rfl) ⟨4077, by rfl⟩) (B 8155 (by norm_num) ⟨4077, by rfl⟩ (by norm_num))
theorem R76261 : Reach 76261 := rs (se 4 (by rfl) ⟨7149, by rfl⟩) (B 14299 (by norm_num) ⟨7149, by rfl⟩ (by norm_num))
theorem R43517 : Reach 43517 := rs (se 3 (by rfl) ⟨8159, by rfl⟩) (B 16319 (by norm_num) ⟨8159, by rfl⟩ (by norm_num))
theorem R43541 : Reach 43541 := rs (se 6 (by rfl) ⟨1020, by rfl⟩) (B 2041 (by norm_num) ⟨1020, by rfl⟩ (by norm_num))
theorem R43565 : Reach 43565 := rs (se 3 (by rfl) ⟨8168, by rfl⟩) (B 16337 (by norm_num) ⟨8168, by rfl⟩ (by norm_num))
theorem R43589 : Reach 43589 := rs (se 4 (by rfl) ⟨4086, by rfl⟩) (B 8173 (by norm_num) ⟨4086, by rfl⟩ (by norm_num))
theorem R76373 : Reach 76373 := rs (se 8 (by rfl) ⟨447, by rfl⟩) (B 895 (by norm_num) ⟨447, by rfl⟩ (by norm_num))
theorem R43613 : Reach 43613 := rs (se 3 (by rfl) ⟨8177, by rfl⟩) (B 16355 (by norm_num) ⟨8177, by rfl⟩ (by norm_num))
theorem R43637 : Reach 43637 := rs (se 5 (by rfl) ⟨2045, by rfl⟩) (B 4091 (by norm_num) ⟨2045, by rfl⟩ (by norm_num))
theorem R43661 : Reach 43661 := rs (se 3 (by rfl) ⟨8186, by rfl⟩) (B 16373 (by norm_num) ⟨8186, by rfl⟩ (by norm_num))
theorem R43669 : Reach 43669 := rs (se 6 (by rfl) ⟨1023, by rfl⟩) (B 2047 (by norm_num) ⟨1023, by rfl⟩ (by norm_num))
theorem R43685 : Reach 43685 := rs (se 4 (by rfl) ⟨4095, by rfl⟩) (B 8191 (by norm_num) ⟨4095, by rfl⟩ (by norm_num))
theorem R43709 : Reach 43709 := rs (se 3 (by rfl) ⟨8195, by rfl⟩) (B 16391 (by norm_num) ⟨8195, by rfl⟩ (by norm_num))
theorem R43733 : Reach 43733 := rs (se 7 (by rfl) ⟨512, by rfl⟩) (B 1025 (by norm_num) ⟨512, by rfl⟩ (by norm_num))
theorem R43757 : Reach 43757 := rs (se 3 (by rfl) ⟨8204, by rfl⟩) (B 16409 (by norm_num) ⟨8204, by rfl⟩ (by norm_num))
theorem R43781 : Reach 43781 := rs (se 4 (by rfl) ⟨4104, by rfl⟩) (B 8209 (by norm_num) ⟨4104, by rfl⟩ (by norm_num))
theorem R174869 : Reach 174869 := rs (se 6 (by rfl) ⟨4098, by rfl⟩) (B 8197 (by norm_num) ⟨4098, by rfl⟩ (by norm_num))
theorem R76565 : Reach 76565 := rs (se 6 (by rfl) ⟨1794, by rfl⟩) (B 3589 (by norm_num) ⟨1794, by rfl⟩ (by norm_num))
theorem R109333 : Reach 109333 := rs (se 6 (by rfl) ⟨2562, by rfl⟩) (B 5125 (by norm_num) ⟨2562, by rfl⟩ (by norm_num))
theorem R43805 : Reach 43805 := rs (se 3 (by rfl) ⟨8213, by rfl⟩) (B 16427 (by norm_num) ⟨8213, by rfl⟩ (by norm_num))
theorem R43829 : Reach 43829 := rs (se 5 (by rfl) ⟨2054, by rfl⟩) (B 4109 (by norm_num) ⟨2054, by rfl⟩ (by norm_num))
theorem R43853 : Reach 43853 := rs (se 3 (by rfl) ⟨8222, by rfl⟩) (B 16445 (by norm_num) ⟨8222, by rfl⟩ (by norm_num))
theorem R43877 : Reach 43877 := rs (se 4 (by rfl) ⟨4113, by rfl⟩) (B 8227 (by norm_num) ⟨4113, by rfl⟩ (by norm_num))
theorem R43901 : Reach 43901 := rs (se 3 (by rfl) ⟨8231, by rfl⟩) (B 16463 (by norm_num) ⟨8231, by rfl⟩ (by norm_num))
theorem R43925 : Reach 43925 := rs (se 6 (by rfl) ⟨1029, by rfl⟩) (B 2059 (by norm_num) ⟨1029, by rfl⟩ (by norm_num))
theorem R43949 : Reach 43949 := rs (se 3 (by rfl) ⟨8240, by rfl⟩) (B 16481 (by norm_num) ⟨8240, by rfl⟩ (by norm_num))
theorem R43973 : Reach 43973 := rs (se 4 (by rfl) ⟨4122, by rfl⟩) (B 8245 (by norm_num) ⟨4122, by rfl⟩ (by norm_num))
theorem R43997 : Reach 43997 := rs (se 3 (by rfl) ⟨8249, by rfl⟩) (B 16499 (by norm_num) ⟨8249, by rfl⟩ (by norm_num))
theorem R44021 : Reach 44021 := rs (se 5 (by rfl) ⟨2063, by rfl⟩) (B 4127 (by norm_num) ⟨2063, by rfl⟩ (by norm_num))
theorem R44045 : Reach 44045 := rs (se 3 (by rfl) ⟨8258, by rfl⟩) (B 16517 (by norm_num) ⟨8258, by rfl⟩ (by norm_num))
theorem R44069 : Reach 44069 := rs (se 4 (by rfl) ⟨4131, by rfl⟩) (B 8263 (by norm_num) ⟨4131, by rfl⟩ (by norm_num))
theorem R44093 : Reach 44093 := rs (se 3 (by rfl) ⟨8267, by rfl⟩) (B 16535 (by norm_num) ⟨8267, by rfl⟩ (by norm_num))
theorem R44101 : Reach 44101 := rs (se 4 (by rfl) ⟨4134, by rfl⟩) (B 8269 (by norm_num) ⟨4134, by rfl⟩ (by norm_num))
theorem R44117 : Reach 44117 := rs (se 8 (by rfl) ⟨258, by rfl⟩) (B 517 (by norm_num) ⟨258, by rfl⟩ (by norm_num))
theorem R44141 : Reach 44141 := rs (se 3 (by rfl) ⟨8276, by rfl⟩) (B 16553 (by norm_num) ⟨8276, by rfl⟩ (by norm_num))
theorem R44165 : Reach 44165 := rs (se 4 (by rfl) ⟨4140, by rfl⟩) (B 8281 (by norm_num) ⟨4140, by rfl⟩ (by norm_num))
theorem R44173 : Reach 44173 := rs (se 3 (by rfl) ⟨8282, by rfl⟩) (B 16565 (by norm_num) ⟨8282, by rfl⟩ (by norm_num))
theorem R44189 : Reach 44189 := rs (se 3 (by rfl) ⟨8285, by rfl⟩) (B 16571 (by norm_num) ⟨8285, by rfl⟩ (by norm_num))
theorem R44213 : Reach 44213 := rs (se 5 (by rfl) ⟨2072, by rfl⟩) (B 4145 (by norm_num) ⟨2072, by rfl⟩ (by norm_num))
theorem R44237 : Reach 44237 := rs (se 3 (by rfl) ⟨8294, by rfl⟩) (B 16589 (by norm_num) ⟨8294, by rfl⟩ (by norm_num))
theorem R44261 : Reach 44261 := rs (se 4 (by rfl) ⟨4149, by rfl⟩) (B 8299 (by norm_num) ⟨4149, by rfl⟩ (by norm_num))
theorem R44285 : Reach 44285 := rs (se 3 (by rfl) ⟨8303, by rfl⟩) (B 16607 (by norm_num) ⟨8303, by rfl⟩ (by norm_num))
theorem R44309 : Reach 44309 := rs (se 6 (by rfl) ⟨1038, by rfl⟩) (B 2077 (by norm_num) ⟨1038, by rfl⟩ (by norm_num))
theorem R44333 : Reach 44333 := rs (se 3 (by rfl) ⟨8312, by rfl⟩) (B 16625 (by norm_num) ⟨8312, by rfl⟩ (by norm_num))
theorem R44357 : Reach 44357 := rs (se 4 (by rfl) ⟨4158, by rfl⟩) (B 8317 (by norm_num) ⟨4158, by rfl⟩ (by norm_num))
theorem R44381 : Reach 44381 := rs (se 3 (by rfl) ⟨8321, by rfl⟩) (B 16643 (by norm_num) ⟨8321, by rfl⟩ (by norm_num))
theorem R44405 : Reach 44405 := rs (se 5 (by rfl) ⟨2081, by rfl⟩) (B 4163 (by norm_num) ⟨2081, by rfl⟩ (by norm_num))
theorem R109957 : Reach 109957 := rs (se 4 (by rfl) ⟨10308, by rfl⟩) (B 20617 (by norm_num) ⟨10308, by rfl⟩ (by norm_num))
theorem R44429 : Reach 44429 := rs (se 3 (by rfl) ⟨8330, by rfl⟩) (B 16661 (by norm_num) ⟨8330, by rfl⟩ (by norm_num))
theorem R44453 : Reach 44453 := rs (se 4 (by rfl) ⟨4167, by rfl⟩) (B 8335 (by norm_num) ⟨4167, by rfl⟩ (by norm_num))
theorem R44477 : Reach 44477 := rs (se 3 (by rfl) ⟨8339, by rfl⟩) (B 16679 (by norm_num) ⟨8339, by rfl⟩ (by norm_num))
theorem R44501 : Reach 44501 := rs (se 7 (by rfl) ⟨521, by rfl⟩) (B 1043 (by norm_num) ⟨521, by rfl⟩ (by norm_num))
theorem R44525 : Reach 44525 := rs (se 3 (by rfl) ⟨8348, by rfl⟩) (B 16697 (by norm_num) ⟨8348, by rfl⟩ (by norm_num))
theorem R44549 : Reach 44549 := rs (se 4 (by rfl) ⟨4176, by rfl⟩) (B 8353 (by norm_num) ⟨4176, by rfl⟩ (by norm_num))
theorem R44573 : Reach 44573 := rs (se 3 (by rfl) ⟨8357, by rfl⟩) (B 16715 (by norm_num) ⟨8357, by rfl⟩ (by norm_num))
theorem R77365 : Reach 77365 := rs (se 5 (by rfl) ⟨3626, by rfl⟩) (B 7253 (by norm_num) ⟨3626, by rfl⟩ (by norm_num))
theorem R44597 : Reach 44597 := rs (se 5 (by rfl) ⟨2090, by rfl⟩) (B 4181 (by norm_num) ⟨2090, by rfl⟩ (by norm_num))
theorem R44621 : Reach 44621 := rs (se 3 (by rfl) ⟨8366, by rfl⟩) (B 16733 (by norm_num) ⟨8366, by rfl⟩ (by norm_num))
theorem R44645 : Reach 44645 := rs (se 4 (by rfl) ⟨4185, by rfl⟩) (B 8371 (by norm_num) ⟨4185, by rfl⟩ (by norm_num))
theorem R77429 : Reach 77429 := rs (se 5 (by rfl) ⟨3629, by rfl⟩) (B 7259 (by norm_num) ⟨3629, by rfl⟩ (by norm_num))
theorem R44669 : Reach 44669 := rs (se 3 (by rfl) ⟨8375, by rfl⟩) (B 16751 (by norm_num) ⟨8375, by rfl⟩ (by norm_num))
theorem R44693 : Reach 44693 := rs (se 6 (by rfl) ⟨1047, by rfl⟩) (B 2095 (by norm_num) ⟨1047, by rfl⟩ (by norm_num))
theorem R44717 : Reach 44717 := rs (se 3 (by rfl) ⟨8384, by rfl⟩) (B 16769 (by norm_num) ⟨8384, by rfl⟩ (by norm_num))
theorem R110261 : Reach 110261 := rs (se 5 (by rfl) ⟨5168, by rfl⟩) (B 10337 (by norm_num) ⟨5168, by rfl⟩ (by norm_num))
theorem R143045 : Reach 143045 := rs (se 4 (by rfl) ⟨13410, by rfl⟩) (B 26821 (by norm_num) ⟨13410, by rfl⟩ (by norm_num))
theorem R44741 : Reach 44741 := rs (se 4 (by rfl) ⟨4194, by rfl⟩) (B 8389 (by norm_num) ⟨4194, by rfl⟩ (by norm_num))
theorem R44765 : Reach 44765 := rs (se 3 (by rfl) ⟨8393, by rfl⟩) (B 16787 (by norm_num) ⟨8393, by rfl⟩ (by norm_num))
theorem R44789 : Reach 44789 := rs (se 5 (by rfl) ⟨2099, by rfl⟩) (B 4199 (by norm_num) ⟨2099, by rfl⟩ (by norm_num))
theorem R77557 : Reach 77557 := rs (se 5 (by rfl) ⟨3635, by rfl⟩) (B 7271 (by norm_num) ⟨3635, by rfl⟩ (by norm_num))
theorem R44813 : Reach 44813 := rs (se 3 (by rfl) ⟨8402, by rfl⟩) (B 16805 (by norm_num) ⟨8402, by rfl⟩ (by norm_num))
theorem R306965 : Reach 306965 := rs (se 6 (by rfl) ⟨7194, by rfl⟩) (B 14389 (by norm_num) ⟨7194, by rfl⟩ (by norm_num))
theorem R44837 : Reach 44837 := rs (se 4 (by rfl) ⟨4203, by rfl⟩) (B 8407 (by norm_num) ⟨4203, by rfl⟩ (by norm_num))
theorem R44861 : Reach 44861 := rs (se 3 (by rfl) ⟨8411, by rfl⟩) (B 16823 (by norm_num) ⟨8411, by rfl⟩ (by norm_num))
theorem R44885 : Reach 44885 := rs (se 9 (by rfl) ⟨131, by rfl⟩) (B 263 (by norm_num) ⟨131, by rfl⟩ (by norm_num))
theorem R77669 : Reach 77669 := rs (se 4 (by rfl) ⟨7281, by rfl⟩) (B 14563 (by norm_num) ⟨7281, by rfl⟩ (by norm_num))
theorem R44909 : Reach 44909 := rs (se 3 (by rfl) ⟨8420, by rfl⟩) (B 16841 (by norm_num) ⟨8420, by rfl⟩ (by norm_num))
theorem R44933 : Reach 44933 := rs (se 4 (by rfl) ⟨4212, by rfl⟩) (B 8425 (by norm_num) ⟨4212, by rfl⟩ (by norm_num))
theorem R44957 : Reach 44957 := rs (se 3 (by rfl) ⟨8429, by rfl⟩) (B 16859 (by norm_num) ⟨8429, by rfl⟩ (by norm_num))
theorem R44981 : Reach 44981 := rs (se 5 (by rfl) ⟨2108, by rfl⟩) (B 4217 (by norm_num) ⟨2108, by rfl⟩ (by norm_num))
theorem R176053 : Reach 176053 := rs (se 5 (by rfl) ⟨8252, by rfl⟩) (B 16505 (by norm_num) ⟨8252, by rfl⟩ (by norm_num))
theorem R45005 : Reach 45005 := rs (se 3 (by rfl) ⟨8438, by rfl⟩) (B 16877 (by norm_num) ⟨8438, by rfl⟩ (by norm_num))
theorem R143317 : Reach 143317 := rs (se 7 (by rfl) ⟨1679, by rfl⟩) (B 3359 (by norm_num) ⟨1679, by rfl⟩ (by norm_num))
theorem R45029 : Reach 45029 := rs (se 4 (by rfl) ⟨4221, by rfl⟩) (B 8443 (by norm_num) ⟨4221, by rfl⟩ (by norm_num))
theorem R45053 : Reach 45053 := rs (se 3 (by rfl) ⟨8447, by rfl⟩) (B 16895 (by norm_num) ⟨8447, by rfl⟩ (by norm_num))
theorem R45077 : Reach 45077 := rs (se 6 (by rfl) ⟨1056, by rfl⟩) (B 2113 (by norm_num) ⟨1056, by rfl⟩ (by norm_num))
theorem R77861 : Reach 77861 := rs (se 4 (by rfl) ⟨7299, by rfl⟩) (B 14599 (by norm_num) ⟨7299, by rfl⟩ (by norm_num))
theorem R45101 : Reach 45101 := rs (se 3 (by rfl) ⟨8456, by rfl⟩) (B 16913 (by norm_num) ⟨8456, by rfl⟩ (by norm_num))
theorem R45125 : Reach 45125 := rs (se 4 (by rfl) ⟨4230, by rfl⟩) (B 8461 (by norm_num) ⟨4230, by rfl⟩ (by norm_num))
theorem R45149 : Reach 45149 := rs (se 3 (by rfl) ⟨8465, by rfl⟩) (B 16931 (by norm_num) ⟨8465, by rfl⟩ (by norm_num))
theorem R45173 : Reach 45173 := rs (se 5 (by rfl) ⟨2117, by rfl⟩) (B 4235 (by norm_num) ⟨2117, by rfl⟩ (by norm_num))
theorem R45197 : Reach 45197 := rs (se 3 (by rfl) ⟨8474, by rfl⟩) (B 16949 (by norm_num) ⟨8474, by rfl⟩ (by norm_num))
theorem R45221 : Reach 45221 := rs (se 4 (by rfl) ⟨4239, by rfl⟩) (B 8479 (by norm_num) ⟨4239, by rfl⟩ (by norm_num))
theorem R45245 : Reach 45245 := rs (se 3 (by rfl) ⟨8483, by rfl⟩) (B 16967 (by norm_num) ⟨8483, by rfl⟩ (by norm_num))
theorem R45269 : Reach 45269 := rs (se 7 (by rfl) ⟨530, by rfl⟩) (B 1061 (by norm_num) ⟨530, by rfl⟩ (by norm_num))
theorem R45293 : Reach 45293 := rs (se 3 (by rfl) ⟨8492, by rfl⟩) (B 16985 (by norm_num) ⟨8492, by rfl⟩ (by norm_num))
theorem R45317 : Reach 45317 := rs (se 4 (by rfl) ⟨4248, by rfl⟩) (B 8497 (by norm_num) ⟨4248, by rfl⟩ (by norm_num))
theorem R45341 : Reach 45341 := rs (se 3 (by rfl) ⟨8501, by rfl⟩) (B 17003 (by norm_num) ⟨8501, by rfl⟩ (by norm_num))
theorem R45365 : Reach 45365 := rs (se 5 (by rfl) ⟨2126, by rfl⟩) (B 4253 (by norm_num) ⟨2126, by rfl⟩ (by norm_num))
theorem R45389 : Reach 45389 := rs (se 3 (by rfl) ⟨8510, by rfl⟩) (B 17021 (by norm_num) ⟨8510, by rfl⟩ (by norm_num))
theorem R45413 : Reach 45413 := rs (se 4 (by rfl) ⟨4257, by rfl⟩) (B 8515 (by norm_num) ⟨4257, by rfl⟩ (by norm_num))
theorem R45437 : Reach 45437 := rs (se 3 (by rfl) ⟨8519, by rfl⟩) (B 17039 (by norm_num) ⟨8519, by rfl⟩ (by norm_num))
theorem R45461 : Reach 45461 := rs (se 6 (by rfl) ⟨1065, by rfl⟩) (B 2131 (by norm_num) ⟨1065, by rfl⟩ (by norm_num))
theorem R45485 : Reach 45485 := rs (se 3 (by rfl) ⟨8528, by rfl⟩) (B 17057 (by norm_num) ⟨8528, by rfl⟩ (by norm_num))
theorem R45509 : Reach 45509 := rs (se 4 (by rfl) ⟨4266, by rfl⟩) (B 8533 (by norm_num) ⟨4266, by rfl⟩ (by norm_num))
theorem R45533 : Reach 45533 := rs (se 3 (by rfl) ⟨8537, by rfl⟩) (B 17075 (by norm_num) ⟨8537, by rfl⟩ (by norm_num))
theorem R45557 : Reach 45557 := rs (se 5 (by rfl) ⟨2135, by rfl⟩) (B 4271 (by norm_num) ⟨2135, by rfl⟩ (by norm_num))
theorem R45581 : Reach 45581 := rs (se 3 (by rfl) ⟨8546, by rfl⟩) (B 17093 (by norm_num) ⟨8546, by rfl⟩ (by norm_num))
theorem R45605 : Reach 45605 := rs (se 4 (by rfl) ⟨4275, by rfl⟩) (B 8551 (by norm_num) ⟨4275, by rfl⟩ (by norm_num))
theorem R45629 : Reach 45629 := rs (se 3 (by rfl) ⟨8555, by rfl⟩) (B 17111 (by norm_num) ⟨8555, by rfl⟩ (by norm_num))
theorem R45653 : Reach 45653 := rs (se 8 (by rfl) ⟨267, by rfl⟩) (B 535 (by norm_num) ⟨267, by rfl⟩ (by norm_num))
theorem R45677 : Reach 45677 := rs (se 3 (by rfl) ⟨8564, by rfl⟩) (B 17129 (by norm_num) ⟨8564, by rfl⟩ (by norm_num))
theorem R45701 : Reach 45701 := rs (se 4 (by rfl) ⟨4284, by rfl⟩) (B 8569 (by norm_num) ⟨4284, by rfl⟩ (by norm_num))
theorem R45725 : Reach 45725 := rs (se 3 (by rfl) ⟨8573, by rfl⟩) (B 17147 (by norm_num) ⟨8573, by rfl⟩ (by norm_num))
theorem R45749 : Reach 45749 := rs (se 5 (by rfl) ⟨2144, by rfl⟩) (B 4289 (by norm_num) ⟨2144, by rfl⟩ (by norm_num))
theorem R45773 : Reach 45773 := rs (se 3 (by rfl) ⟨8582, by rfl⟩) (B 17165 (by norm_num) ⟨8582, by rfl⟩ (by norm_num))
theorem R45797 : Reach 45797 := rs (se 4 (by rfl) ⟨4293, by rfl⟩) (B 8587 (by norm_num) ⟨4293, by rfl⟩ (by norm_num))
theorem R45805 : Reach 45805 := rs (se 3 (by rfl) ⟨8588, by rfl⟩) (B 17177 (by norm_num) ⟨8588, by rfl⟩ (by norm_num))
theorem R45821 : Reach 45821 := rs (se 3 (by rfl) ⟨8591, by rfl⟩) (B 17183 (by norm_num) ⟨8591, by rfl⟩ (by norm_num))
theorem R45845 : Reach 45845 := rs (se 6 (by rfl) ⟨1074, by rfl⟩) (B 2149 (by norm_num) ⟨1074, by rfl⟩ (by norm_num))
theorem R45869 : Reach 45869 := rs (se 3 (by rfl) ⟨8600, by rfl⟩) (B 17201 (by norm_num) ⟨8600, by rfl⟩ (by norm_num))
theorem R45893 : Reach 45893 := rs (se 4 (by rfl) ⟨4302, by rfl⟩) (B 8605 (by norm_num) ⟨4302, by rfl⟩ (by norm_num))
theorem R45917 : Reach 45917 := rs (se 3 (by rfl) ⟨8609, by rfl⟩) (B 17219 (by norm_num) ⟨8609, by rfl⟩ (by norm_num))
theorem R45941 : Reach 45941 := rs (se 5 (by rfl) ⟨2153, by rfl⟩) (B 4307 (by norm_num) ⟨2153, by rfl⟩ (by norm_num))
theorem R45965 : Reach 45965 := rs (se 3 (by rfl) ⟨8618, by rfl⟩) (B 17237 (by norm_num) ⟨8618, by rfl⟩ (by norm_num))
theorem R45989 : Reach 45989 := rs (se 4 (by rfl) ⟨4311, by rfl⟩) (B 8623 (by norm_num) ⟨4311, by rfl⟩ (by norm_num))
theorem R46013 : Reach 46013 := rs (se 3 (by rfl) ⟨8627, by rfl⟩) (B 17255 (by norm_num) ⟨8627, by rfl⟩ (by norm_num))
theorem R46021 : Reach 46021 := rs (se 4 (by rfl) ⟨4314, by rfl⟩) (B 8629 (by norm_num) ⟨4314, by rfl⟩ (by norm_num))
theorem R144341 : Reach 144341 := rs (se 7 (by rfl) ⟨1691, by rfl⟩) (B 3383 (by norm_num) ⟨1691, by rfl⟩ (by norm_num))
theorem R46037 : Reach 46037 := rs (se 7 (by rfl) ⟨539, by rfl⟩) (B 1079 (by norm_num) ⟨539, by rfl⟩ (by norm_num))
theorem R46061 : Reach 46061 := rs (se 3 (by rfl) ⟨8636, by rfl⟩) (B 17273 (by norm_num) ⟨8636, by rfl⟩ (by norm_num))
theorem R46085 : Reach 46085 := rs (se 4 (by rfl) ⟨4320, by rfl⟩) (B 8641 (by norm_num) ⟨4320, by rfl⟩ (by norm_num))
theorem R78869 : Reach 78869 := rs (se 6 (by rfl) ⟨1848, by rfl⟩) (B 3697 (by norm_num) ⟨1848, by rfl⟩ (by norm_num))
theorem R46109 : Reach 46109 := rs (se 3 (by rfl) ⟨8645, by rfl⟩) (B 17291 (by norm_num) ⟨8645, by rfl⟩ (by norm_num))
theorem R46133 : Reach 46133 := rs (se 5 (by rfl) ⟨2162, by rfl⟩) (B 4325 (by norm_num) ⟨2162, by rfl⟩ (by norm_num))
theorem R46157 : Reach 46157 := rs (se 3 (by rfl) ⟨8654, by rfl⟩) (B 17309 (by norm_num) ⟨8654, by rfl⟩ (by norm_num))
theorem R46181 : Reach 46181 := rs (se 4 (by rfl) ⟨4329, by rfl⟩) (B 8659 (by norm_num) ⟨4329, by rfl⟩ (by norm_num))
theorem R78965 : Reach 78965 := rs (se 5 (by rfl) ⟨3701, by rfl⟩) (B 7403 (by norm_num) ⟨3701, by rfl⟩ (by norm_num))
theorem R46205 : Reach 46205 := rs (se 3 (by rfl) ⟨8663, by rfl⟩) (B 17327 (by norm_num) ⟨8663, by rfl⟩ (by norm_num))
theorem R46229 : Reach 46229 := rs (se 6 (by rfl) ⟨1083, by rfl⟩) (B 2167 (by norm_num) ⟨1083, by rfl⟩ (by norm_num))
theorem R46237 : Reach 46237 := rs (se 3 (by rfl) ⟨8669, by rfl⟩) (B 17339 (by norm_num) ⟨8669, by rfl⟩ (by norm_num))
theorem R46253 : Reach 46253 := rs (se 3 (by rfl) ⟨8672, by rfl⟩) (B 17345 (by norm_num) ⟨8672, by rfl⟩ (by norm_num))
theorem R46261 : Reach 46261 := rs (se 5 (by rfl) ⟨2168, by rfl⟩) (B 4337 (by norm_num) ⟨2168, by rfl⟩ (by norm_num))
theorem R46277 : Reach 46277 := rs (se 4 (by rfl) ⟨4338, by rfl⟩) (B 8677 (by norm_num) ⟨4338, by rfl⟩ (by norm_num))
theorem R46301 : Reach 46301 := rs (se 3 (by rfl) ⟨8681, by rfl⟩) (B 17363 (by norm_num) ⟨8681, by rfl⟩ (by norm_num))
theorem R46325 : Reach 46325 := rs (se 5 (by rfl) ⟨2171, by rfl⟩) (B 4343 (by norm_num) ⟨2171, by rfl⟩ (by norm_num))
theorem R46349 : Reach 46349 := rs (se 3 (by rfl) ⟨8690, by rfl⟩) (B 17381 (by norm_num) ⟨8690, by rfl⟩ (by norm_num))
theorem R46373 : Reach 46373 := rs (se 4 (by rfl) ⟨4347, by rfl⟩) (B 8695 (by norm_num) ⟨4347, by rfl⟩ (by norm_num))
theorem R46397 : Reach 46397 := rs (se 3 (by rfl) ⟨8699, by rfl⟩) (B 17399 (by norm_num) ⟨8699, by rfl⟩ (by norm_num))
theorem R46421 : Reach 46421 := rs (se 13 (by rfl) ⟨8, by rfl⟩) (B 17 (by norm_num) ⟨8, by rfl⟩ (by norm_num))
theorem R46445 : Reach 46445 := rs (se 3 (by rfl) ⟨8708, by rfl⟩) (B 17417 (by norm_num) ⟨8708, by rfl⟩ (by norm_num))
theorem R46453 : Reach 46453 := rs (se 5 (by rfl) ⟨2177, by rfl⟩) (B 4355 (by norm_num) ⟨2177, by rfl⟩ (by norm_num))
theorem R46469 : Reach 46469 := rs (se 4 (by rfl) ⟨4356, by rfl⟩) (B 8713 (by norm_num) ⟨4356, by rfl⟩ (by norm_num))
theorem R46493 : Reach 46493 := rs (se 3 (by rfl) ⟨8717, by rfl⟩) (B 17435 (by norm_num) ⟨8717, by rfl⟩ (by norm_num))
theorem R46517 : Reach 46517 := rs (se 5 (by rfl) ⟨2180, by rfl⟩) (B 4361 (by norm_num) ⟨2180, by rfl⟩ (by norm_num))
theorem R46541 : Reach 46541 := rs (se 3 (by rfl) ⟨8726, by rfl⟩) (B 17453 (by norm_num) ⟨8726, by rfl⟩ (by norm_num))
theorem R46565 : Reach 46565 := rs (se 4 (by rfl) ⟨4365, by rfl⟩) (B 8731 (by norm_num) ⟨4365, by rfl⟩ (by norm_num))
theorem R46589 : Reach 46589 := rs (se 3 (by rfl) ⟨8735, by rfl⟩) (B 17471 (by norm_num) ⟨8735, by rfl⟩ (by norm_num))
theorem R46613 : Reach 46613 := rs (se 6 (by rfl) ⟨1092, by rfl⟩) (B 2185 (by norm_num) ⟨1092, by rfl⟩ (by norm_num))
theorem R46637 : Reach 46637 := rs (se 3 (by rfl) ⟨8744, by rfl⟩) (B 17489 (by norm_num) ⟨8744, by rfl⟩ (by norm_num))
theorem R46661 : Reach 46661 := rs (se 4 (by rfl) ⟨4374, by rfl⟩) (B 8749 (by norm_num) ⟨4374, by rfl⟩ (by norm_num))
theorem R46669 : Reach 46669 := rs (se 3 (by rfl) ⟨8750, by rfl⟩) (B 17501 (by norm_num) ⟨8750, by rfl⟩ (by norm_num))
theorem R112261 : Reach 112261 := rs (se 4 (by rfl) ⟨10524, by rfl⟩) (B 21049 (by norm_num) ⟨10524, by rfl⟩ (by norm_num))
theorem R46757 : Reach 46757 := rs (se 4 (by rfl) ⟨4383, by rfl⟩) (B 8767 (by norm_num) ⟨4383, by rfl⟩ (by norm_num))
theorem R112373 : Reach 112373 := rs (se 5 (by rfl) ⟨5267, by rfl⟩) (B 10535 (by norm_num) ⟨5267, by rfl⟩ (by norm_num))
theorem R46885 : Reach 46885 := rs (se 4 (by rfl) ⟨4395, by rfl⟩) (B 8791 (by norm_num) ⟨4395, by rfl⟩ (by norm_num))
theorem R46973 : Reach 46973 := rs (se 3 (by rfl) ⟨8807, by rfl⟩) (B 17615 (by norm_num) ⟨8807, by rfl⟩ (by norm_num))
theorem R47101 : Reach 47101 := rs (se 3 (by rfl) ⟨8831, by rfl⟩) (B 17663 (by norm_num) ⟨8831, by rfl⟩ (by norm_num))
theorem R112661 : Reach 112661 := rs (se 6 (by rfl) ⟨2640, by rfl⟩) (B 5281 (by norm_num) ⟨2640, by rfl⟩ (by norm_num))
theorem R47189 : Reach 47189 := rs (se 8 (by rfl) ⟨276, by rfl⟩) (B 553 (by norm_num) ⟨276, by rfl⟩ (by norm_num))
theorem R47317 : Reach 47317 := rs (se 7 (by rfl) ⟨554, by rfl⟩) (B 1109 (by norm_num) ⟨554, by rfl⟩ (by norm_num))
theorem R47405 : Reach 47405 := rs (se 3 (by rfl) ⟨8888, by rfl⟩) (B 17777 (by norm_num) ⟨8888, by rfl⟩ (by norm_num))
theorem R211285 : Reach 211285 := rs (se 10 (by rfl) ⟨309, by rfl⟩) (B 619 (by norm_num) ⟨309, by rfl⟩ (by norm_num))
theorem R47509 : Reach 47509 := rs (se 6 (by rfl) ⟨1113, by rfl⟩) (B 2227 (by norm_num) ⟨1113, by rfl⟩ (by norm_num))
theorem R47533 : Reach 47533 := rs (se 3 (by rfl) ⟨8912, by rfl⟩) (B 17825 (by norm_num) ⟨8912, by rfl⟩ (by norm_num))
theorem R80357 : Reach 80357 := rs (se 4 (by rfl) ⟨7533, by rfl⟩) (B 15067 (by norm_num) ⟨7533, by rfl⟩ (by norm_num))
theorem R47621 : Reach 47621 := rs (se 4 (by rfl) ⟨4464, by rfl⟩) (B 8929 (by norm_num) ⟨4464, by rfl⟩ (by norm_num))
theorem R47645 : Reach 47645 := rs (se 3 (by rfl) ⟨8933, by rfl⟩) (B 17867 (by norm_num) ⟨8933, by rfl⟩ (by norm_num))
theorem R80453 : Reach 80453 := rs (se 4 (by rfl) ⟨7542, by rfl⟩) (B 15085 (by norm_num) ⟨7542, by rfl⟩ (by norm_num))
theorem R47717 : Reach 47717 := rs (se 4 (by rfl) ⟨4473, by rfl⟩) (B 8947 (by norm_num) ⟨4473, by rfl⟩ (by norm_num))
theorem R113269 : Reach 113269 := rs (se 5 (by rfl) ⟨5309, by rfl⟩) (B 10619 (by norm_num) ⟨5309, by rfl⟩ (by norm_num))
theorem R47749 : Reach 47749 := rs (se 4 (by rfl) ⟨4476, by rfl⟩) (B 8953 (by norm_num) ⟨4476, by rfl⟩ (by norm_num))
theorem R47837 : Reach 47837 := rs (se 3 (by rfl) ⟨8969, by rfl⟩) (B 17939 (by norm_num) ⟨8969, by rfl⟩ (by norm_num))
theorem R47965 : Reach 47965 := rs (se 3 (by rfl) ⟨8993, by rfl⟩) (B 17987 (by norm_num) ⟨8993, by rfl⟩ (by norm_num))
theorem R48053 : Reach 48053 := rs (se 5 (by rfl) ⟨2252, by rfl⟩) (B 4505 (by norm_num) ⟨2252, by rfl⟩ (by norm_num))
theorem R48181 : Reach 48181 := rs (se 5 (by rfl) ⟨2258, by rfl⟩) (B 4517 (by norm_num) ⟨2258, by rfl⟩ (by norm_num))
theorem R48269 : Reach 48269 := rs (se 3 (by rfl) ⟨9050, by rfl⟩) (B 18101 (by norm_num) ⟨9050, by rfl⟩ (by norm_num))
theorem R113845 : Reach 113845 := rs (se 5 (by rfl) ⟨5336, by rfl⟩) (B 10673 (by norm_num) ⟨5336, by rfl⟩ (by norm_num))
theorem R81125 : Reach 81125 := rs (se 4 (by rfl) ⟨7605, by rfl⟩) (B 15211 (by norm_num) ⟨7605, by rfl⟩ (by norm_num))
theorem R48397 : Reach 48397 := rs (se 3 (by rfl) ⟨9074, by rfl⟩) (B 18149 (by norm_num) ⟨9074, by rfl⟩ (by norm_num))
theorem R48485 : Reach 48485 := rs (se 4 (by rfl) ⟨4545, by rfl⟩) (B 9091 (by norm_num) ⟨4545, by rfl⟩ (by norm_num))
theorem R540053 : Reach 540053 := rs (se 6 (by rfl) ⟨12657, by rfl⟩) (B 25315 (by norm_num) ⟨12657, by rfl⟩ (by norm_num))
theorem R48613 : Reach 48613 := rs (se 4 (by rfl) ⟨4557, by rfl⟩) (B 9115 (by norm_num) ⟨4557, by rfl⟩ (by norm_num))
theorem R114149 : Reach 114149 := rs (se 4 (by rfl) ⟨10701, by rfl⟩) (B 21403 (by norm_num) ⟨10701, by rfl⟩ (by norm_num))
theorem R146933 : Reach 146933 := rs (se 5 (by rfl) ⟨6887, by rfl⟩) (B 13775 (by norm_num) ⟨6887, by rfl⟩ (by norm_num))
theorem R48701 : Reach 48701 := rs (se 3 (by rfl) ⟨9131, by rfl⟩) (B 18263 (by norm_num) ⟨9131, by rfl⟩ (by norm_num))
theorem R81557 : Reach 81557 := rs (se 6 (by rfl) ⟨1911, by rfl⟩) (B 3823 (by norm_num) ⟨1911, by rfl⟩ (by norm_num))
theorem R48829 : Reach 48829 := rs (se 3 (by rfl) ⟨9155, by rfl⟩) (B 18311 (by norm_num) ⟨9155, by rfl⟩ (by norm_num))
theorem R114389 : Reach 114389 := rs (se 7 (by rfl) ⟨1340, by rfl⟩) (B 2681 (by norm_num) ⟨1340, by rfl⟩ (by norm_num))
theorem R48917 : Reach 48917 := rs (se 6 (by rfl) ⟨1146, by rfl⟩) (B 2293 (by norm_num) ⟨1146, by rfl⟩ (by norm_num))
theorem R49045 : Reach 49045 := rs (se 6 (by rfl) ⟨1149, by rfl⟩) (B 2299 (by norm_num) ⟨1149, by rfl⟩ (by norm_num))
theorem R49133 : Reach 49133 := rs (se 3 (by rfl) ⟨9212, by rfl⟩) (B 18425 (by norm_num) ⟨9212, by rfl⟩ (by norm_num))
theorem R49157 : Reach 49157 := rs (se 4 (by rfl) ⟨4608, by rfl⟩) (B 9217 (by norm_num) ⟨4608, by rfl⟩ (by norm_num))
theorem R49189 : Reach 49189 := rs (se 4 (by rfl) ⟨4611, by rfl⟩) (B 9223 (by norm_num) ⟨4611, by rfl⟩ (by norm_num))
theorem R49253 : Reach 49253 := rs (se 4 (by rfl) ⟨4617, by rfl⟩) (B 9235 (by norm_num) ⟨4617, by rfl⟩ (by norm_num))
theorem R49261 : Reach 49261 := rs (se 3 (by rfl) ⟨9236, by rfl⟩) (B 18473 (by norm_num) ⟨9236, by rfl⟩ (by norm_num))
theorem R49285 : Reach 49285 := rs (se 4 (by rfl) ⟨4620, by rfl⟩) (B 9241 (by norm_num) ⟨4620, by rfl⟩ (by norm_num))
theorem R49333 : Reach 49333 := rs (se 5 (by rfl) ⟨2312, by rfl⟩) (B 4625 (by norm_num) ⟨2312, by rfl⟩ (by norm_num))
theorem R49349 : Reach 49349 := rs (se 4 (by rfl) ⟨4626, by rfl⟩) (B 9253 (by norm_num) ⟨4626, by rfl⟩ (by norm_num))
theorem R246037 : Reach 246037 := rs (se 6 (by rfl) ⟨5766, by rfl⟩) (B 11533 (by norm_num) ⟨5766, by rfl⟩ (by norm_num))
theorem R49477 : Reach 49477 := rs (se 4 (by rfl) ⟨4638, by rfl⟩) (B 9277 (by norm_num) ⟨4638, by rfl⟩ (by norm_num))
theorem R49493 : Reach 49493 := rs (se 10 (by rfl) ⟨72, by rfl⟩) (B 145 (by norm_num) ⟨72, by rfl⟩ (by norm_num))
theorem R82309 : Reach 82309 := rs (se 4 (by rfl) ⟨7716, by rfl⟩) (B 15433 (by norm_num) ⟨7716, by rfl⟩ (by norm_num))
theorem R82325 : Reach 82325 := rs (se 6 (by rfl) ⟨1929, by rfl⟩) (B 3859 (by norm_num) ⟨1929, by rfl⟩ (by norm_num))
theorem R49565 : Reach 49565 := rs (se 3 (by rfl) ⟨9293, by rfl⟩) (B 18587 (by norm_num) ⟨9293, by rfl⟩ (by norm_num))
theorem R49693 : Reach 49693 := rs (se 3 (by rfl) ⟨9317, by rfl⟩) (B 18635 (by norm_num) ⟨9317, by rfl⟩ (by norm_num))
theorem R148085 : Reach 148085 := rs (se 5 (by rfl) ⟨6941, by rfl⟩) (B 13883 (by norm_num) ⟨6941, by rfl⟩ (by norm_num))
theorem R49781 : Reach 49781 := rs (se 5 (by rfl) ⟨2333, by rfl⟩) (B 4667 (by norm_num) ⟨2333, by rfl⟩ (by norm_num))
theorem R49909 : Reach 49909 := rs (se 5 (by rfl) ⟨2339, by rfl⟩) (B 4679 (by norm_num) ⟨2339, by rfl⟩ (by norm_num))
theorem R377621 : Reach 377621 := rs (se 6 (by rfl) ⟨8850, by rfl⟩) (B 17701 (by norm_num) ⟨8850, by rfl⟩ (by norm_num))
theorem R148277 : Reach 148277 := rs (se 5 (by rfl) ⟨6950, by rfl⟩) (B 13901 (by norm_num) ⟨6950, by rfl⟩ (by norm_num))
theorem R49997 : Reach 49997 := rs (se 3 (by rfl) ⟨9374, by rfl⟩) (B 18749 (by norm_num) ⟨9374, by rfl⟩ (by norm_num))
theorem R50125 : Reach 50125 := rs (se 3 (by rfl) ⟨9398, by rfl⟩) (B 18797 (by norm_num) ⟨9398, by rfl⟩ (by norm_num))
theorem R50213 : Reach 50213 := rs (se 4 (by rfl) ⟨4707, by rfl⟩) (B 9415 (by norm_num) ⟨4707, by rfl⟩ (by norm_num))
theorem R181397 : Reach 181397 := rs (se 6 (by rfl) ⟨4251, by rfl⟩) (B 8503 (by norm_num) ⟨4251, by rfl⟩ (by norm_num))
theorem R50341 : Reach 50341 := rs (se 4 (by rfl) ⟨4719, by rfl⟩) (B 9439 (by norm_num) ⟨4719, by rfl⟩ (by norm_num))
theorem R50429 : Reach 50429 := rs (se 3 (by rfl) ⟨9455, by rfl⟩) (B 18911 (by norm_num) ⟨9455, by rfl⟩ (by norm_num))
theorem R214325 : Reach 214325 := rs (se 5 (by rfl) ⟨10046, by rfl⟩) (B 20093 (by norm_num) ⟨10046, by rfl⟩ (by norm_num))
theorem R148853 : Reach 148853 := rs (se 5 (by rfl) ⟨6977, by rfl⟩) (B 13955 (by norm_num) ⟨6977, by rfl⟩ (by norm_num))
theorem R50557 : Reach 50557 := rs (se 3 (by rfl) ⟨9479, by rfl⟩) (B 18959 (by norm_num) ⟨9479, by rfl⟩ (by norm_num))
theorem R50573 : Reach 50573 := rs (se 3 (by rfl) ⟨9482, by rfl⟩) (B 18965 (by norm_num) ⟨9482, by rfl⟩ (by norm_num))
theorem R116117 : Reach 116117 := rs (se 6 (by rfl) ⟨2721, by rfl⟩) (B 5443 (by norm_num) ⟨2721, by rfl⟩ (by norm_num))
theorem R50645 : Reach 50645 := rs (se 7 (by rfl) ⟨593, by rfl⟩) (B 1187 (by norm_num) ⟨593, by rfl⟩ (by norm_num))
theorem R50717 : Reach 50717 := rs (se 3 (by rfl) ⟨9509, by rfl⟩) (B 19019 (by norm_num) ⟨9509, by rfl⟩ (by norm_num))
theorem R116261 : Reach 116261 := rs (se 4 (by rfl) ⟨10899, by rfl⟩) (B 21799 (by norm_num) ⟨10899, by rfl⟩ (by norm_num))
theorem R50773 : Reach 50773 := rs (se 8 (by rfl) ⟨297, by rfl⟩) (B 595 (by norm_num) ⟨297, by rfl⟩ (by norm_num))
theorem R50797 : Reach 50797 := rs (se 3 (by rfl) ⟨9524, by rfl⟩) (B 19049 (by norm_num) ⟨9524, by rfl⟩ (by norm_num))
theorem R50861 : Reach 50861 := rs (se 3 (by rfl) ⟨9536, by rfl⟩) (B 19073 (by norm_num) ⟨9536, by rfl⟩ (by norm_num))
theorem R214805 : Reach 214805 := rs (se 6 (by rfl) ⟨5034, by rfl⟩) (B 10069 (by norm_num) ⟨5034, by rfl⟩ (by norm_num))
theorem R50989 : Reach 50989 := rs (se 3 (by rfl) ⟨9560, by rfl⟩) (B 19121 (by norm_num) ⟨9560, by rfl⟩ (by norm_num))
theorem R116549 : Reach 116549 := rs (se 4 (by rfl) ⟨10926, by rfl⟩) (B 21853 (by norm_num) ⟨10926, by rfl⟩ (by norm_num))
theorem R51077 : Reach 51077 := rs (se 4 (by rfl) ⟨4788, by rfl⟩) (B 9577 (by norm_num) ⟨4788, by rfl⟩ (by norm_num))
theorem R51205 : Reach 51205 := rs (se 4 (by rfl) ⟨4800, by rfl⟩) (B 9601 (by norm_num) ⟨4800, by rfl⟩ (by norm_num))
theorem R149525 : Reach 149525 := rs (se 6 (by rfl) ⟨3504, by rfl⟩) (B 7009 (by norm_num) ⟨3504, by rfl⟩ (by norm_num))
theorem R51293 : Reach 51293 := rs (se 3 (by rfl) ⟨9617, by rfl⟩) (B 19235 (by norm_num) ⟨9617, by rfl⟩ (by norm_num))
theorem R248021 : Reach 248021 := rs (se 7 (by rfl) ⟨2906, by rfl⟩) (B 5813 (by norm_num) ⟨2906, by rfl⟩ (by norm_num))
theorem R51421 : Reach 51421 := rs (se 3 (by rfl) ⟨9641, by rfl⟩) (B 19283 (by norm_num) ⟨9641, by rfl⟩ (by norm_num))
theorem R51509 : Reach 51509 := rs (se 5 (by rfl) ⟨2414, by rfl⟩) (B 4829 (by norm_num) ⟨2414, by rfl⟩ (by norm_num))
theorem R51637 : Reach 51637 := rs (se 5 (by rfl) ⟨2420, by rfl⟩) (B 4841 (by norm_num) ⟨2420, by rfl⟩ (by norm_num))
theorem R51653 : Reach 51653 := rs (se 4 (by rfl) ⟨4842, by rfl⟩) (B 9685 (by norm_num) ⟨4842, by rfl⟩ (by norm_num))
theorem R51725 : Reach 51725 := rs (se 3 (by rfl) ⟨9698, by rfl⟩) (B 19397 (by norm_num) ⟨9698, by rfl⟩ (by norm_num))
theorem R51853 : Reach 51853 := rs (se 3 (by rfl) ⟨9722, by rfl⟩) (B 19445 (by norm_num) ⟨9722, by rfl⟩ (by norm_num))
theorem R51941 : Reach 51941 := rs (se 4 (by rfl) ⟨4869, by rfl⟩) (B 9739 (by norm_num) ⟨4869, by rfl⟩ (by norm_num))
theorem R52069 : Reach 52069 := rs (se 4 (by rfl) ⟨4881, by rfl⟩) (B 9763 (by norm_num) ⟨4881, by rfl⟩ (by norm_num))
theorem R52093 : Reach 52093 := rs (se 3 (by rfl) ⟨9767, by rfl⟩) (B 19535 (by norm_num) ⟨9767, by rfl⟩ (by norm_num))
theorem R52157 : Reach 52157 := rs (se 3 (by rfl) ⟨9779, by rfl⟩) (B 19559 (by norm_num) ⟨9779, by rfl⟩ (by norm_num))
theorem R52181 : Reach 52181 := rs (se 7 (by rfl) ⟨611, by rfl⟩) (B 1223 (by norm_num) ⟨611, by rfl⟩ (by norm_num))
theorem R117733 : Reach 117733 := rs (se 4 (by rfl) ⟨11037, by rfl⟩) (B 22075 (by norm_num) ⟨11037, by rfl⟩ (by norm_num))
theorem R52285 : Reach 52285 := rs (se 3 (by rfl) ⟨9803, by rfl⟩) (B 19607 (by norm_num) ⟨9803, by rfl⟩ (by norm_num))
theorem R52373 : Reach 52373 := rs (se 6 (by rfl) ⟨1227, by rfl⟩) (B 2455 (by norm_num) ⟨1227, by rfl⟩ (by norm_num))
theorem R85157 : Reach 85157 := rs (se 4 (by rfl) ⟨7983, by rfl⟩) (B 15967 (by norm_num) ⟨7983, by rfl⟩ (by norm_num))
theorem R52397 : Reach 52397 := rs (se 3 (by rfl) ⟨9824, by rfl⟩) (B 19649 (by norm_num) ⟨9824, by rfl⟩ (by norm_num))
theorem R118037 : Reach 118037 := rs (se 6 (by rfl) ⟨2766, by rfl⟩) (B 5533 (by norm_num) ⟨2766, by rfl⟩ (by norm_num))
theorem R52501 : Reach 52501 := rs (se 6 (by rfl) ⟨1230, by rfl⟩) (B 2461 (by norm_num) ⟨1230, by rfl⟩ (by norm_num))
theorem R52741 : Reach 52741 := rs (se 4 (by rfl) ⟨4944, by rfl⟩) (B 9889 (by norm_num) ⟨4944, by rfl⟩ (by norm_num))
theorem R52813 : Reach 52813 := rs (se 3 (by rfl) ⟨9902, by rfl⟩) (B 19805 (by norm_num) ⟨9902, by rfl⟩ (by norm_num))
theorem R85765 : Reach 85765 := rs (se 4 (by rfl) ⟨8040, by rfl⟩) (B 16081 (by norm_num) ⟨8040, by rfl⟩ (by norm_num))
theorem R85781 : Reach 85781 := rs (se 6 (by rfl) ⟨2010, by rfl⟩) (B 4021 (by norm_num) ⟨2010, by rfl⟩ (by norm_num))
theorem R53149 : Reach 53149 := rs (se 3 (by rfl) ⟨9965, by rfl⟩) (B 19931 (by norm_num) ⟨9965, by rfl⟩ (by norm_num))
theorem R53293 : Reach 53293 := rs (se 3 (by rfl) ⟨9992, by rfl⟩) (B 19985 (by norm_num) ⟨9992, by rfl⟩ (by norm_num))
theorem R151733 : Reach 151733 := rs (se 5 (by rfl) ⟨7112, by rfl⟩) (B 14225 (by norm_num) ⟨7112, by rfl⟩ (by norm_num))
theorem R53453 : Reach 53453 := rs (se 3 (by rfl) ⟨10022, by rfl⟩) (B 20045 (by norm_num) ⟨10022, by rfl⟩ (by norm_num))
theorem R86341 : Reach 86341 := rs (se 4 (by rfl) ⟨8094, by rfl⟩) (B 16189 (by norm_num) ⟨8094, by rfl⟩ (by norm_num))
theorem R53597 : Reach 53597 := rs (se 3 (by rfl) ⟨10049, by rfl⟩) (B 20099 (by norm_num) ⟨10049, by rfl⟩ (by norm_num))
theorem R86501 : Reach 86501 := rs (se 4 (by rfl) ⟨8109, by rfl⟩) (B 16219 (by norm_num) ⟨8109, by rfl⟩ (by norm_num))
theorem R53813 : Reach 53813 := rs (se 5 (by rfl) ⟨2522, by rfl⟩) (B 5045 (by norm_num) ⟨2522, by rfl⟩ (by norm_num))
theorem R152117 : Reach 152117 := rs (se 5 (by rfl) ⟨7130, by rfl⟩) (B 14261 (by norm_num) ⟨7130, by rfl⟩ (by norm_num))
theorem R53885 : Reach 53885 := rs (se 3 (by rfl) ⟨10103, by rfl⟩) (B 20207 (by norm_num) ⟨10103, by rfl⟩ (by norm_num))
theorem R86741 : Reach 86741 := rs (se 7 (by rfl) ⟨1016, by rfl⟩) (B 2033 (by norm_num) ⟨1016, by rfl⟩ (by norm_num))
theorem R54037 : Reach 54037 := rs (se 6 (by rfl) ⟨1266, by rfl⟩) (B 2533 (by norm_num) ⟨1266, by rfl⟩ (by norm_num))
theorem R54101 : Reach 54101 := rs (se 9 (by rfl) ⟨158, by rfl⟩) (B 317 (by norm_num) ⟨158, by rfl⟩ (by norm_num))
theorem R86933 : Reach 86933 := rs (se 6 (by rfl) ⟨2037, by rfl⟩) (B 4075 (by norm_num) ⟨2037, by rfl⟩ (by norm_num))
theorem R54341 : Reach 54341 := rs (se 4 (by rfl) ⟨5094, by rfl⟩) (B 10189 (by norm_num) ⟨5094, by rfl⟩ (by norm_num))
theorem R120149 : Reach 120149 := rs (se 15 (by rfl) ⟨5, by rfl⟩) (B 11 (by norm_num) ⟨5, by rfl⟩ (by norm_num))
theorem R185813 : Reach 185813 := rs (se 7 (by rfl) ⟨2177, by rfl⟩) (B 4355 (by norm_num) ⟨2177, by rfl⟩ (by norm_num))
theorem R55085 : Reach 55085 := rs (se 3 (by rfl) ⟨10328, by rfl⟩) (B 20657 (by norm_num) ⟨10328, by rfl⟩ (by norm_num))
theorem R55093 : Reach 55093 := rs (se 5 (by rfl) ⟨2582, by rfl⟩) (B 5165 (by norm_num) ⟨2582, by rfl⟩ (by norm_num))
theorem R87925 : Reach 87925 := rs (se 5 (by rfl) ⟨4121, by rfl⟩) (B 8243 (by norm_num) ⟨4121, by rfl⟩ (by norm_num))
theorem R55237 : Reach 55237 := rs (se 4 (by rfl) ⟨5178, by rfl⟩) (B 10357 (by norm_num) ⟨5178, by rfl⟩ (by norm_num))
theorem R55397 : Reach 55397 := rs (se 4 (by rfl) ⟨5193, by rfl⟩) (B 10387 (by norm_num) ⟨5193, by rfl⟩ (by norm_num))
theorem R284789 : Reach 284789 := rs (se 5 (by rfl) ⟨13349, by rfl⟩) (B 26699 (by norm_num) ⟨13349, by rfl⟩ (by norm_num))
theorem R55541 : Reach 55541 := rs (se 5 (by rfl) ⟨2603, by rfl⟩) (B 5207 (by norm_num) ⟨2603, by rfl⟩ (by norm_num))
theorem R55829 : Reach 55829 := rs (se 6 (by rfl) ⟨1308, by rfl⟩) (B 2617 (by norm_num) ⟨1308, by rfl⟩ (by norm_num))
theorem R121445 : Reach 121445 := rs (se 4 (by rfl) ⟨11385, by rfl⟩) (B 22771 (by norm_num) ⟨11385, by rfl⟩ (by norm_num))
theorem R55981 : Reach 55981 := rs (se 3 (by rfl) ⟨10496, by rfl⟩) (B 20993 (by norm_num) ⟨10496, by rfl⟩ (by norm_num))
theorem R88933 : Reach 88933 := rs (se 4 (by rfl) ⟨8337, by rfl⟩) (B 16675 (by norm_num) ⟨8337, by rfl⟩ (by norm_num))
theorem R89029 : Reach 89029 := rs (se 4 (by rfl) ⟨8346, by rfl⟩) (B 16693 (by norm_num) ⟨8346, by rfl⟩ (by norm_num))
theorem R56285 : Reach 56285 := rs (se 3 (by rfl) ⟨10553, by rfl⟩) (B 21107 (by norm_num) ⟨10553, by rfl⟩ (by norm_num))
theorem R121925 : Reach 121925 := rs (se 4 (by rfl) ⟨11430, by rfl⟩) (B 22861 (by norm_num) ⟨11430, by rfl⟩ (by norm_num))
theorem R154709 : Reach 154709 := rs (se 8 (by rfl) ⟨906, by rfl⟩) (B 1813 (by norm_num) ⟨906, by rfl⟩ (by norm_num))
theorem R89189 : Reach 89189 := rs (se 4 (by rfl) ⟨8361, by rfl⟩) (B 16723 (by norm_num) ⟨8361, by rfl⟩ (by norm_num))
theorem R57037 : Reach 57037 := rs (se 3 (by rfl) ⟨10694, by rfl⟩) (B 21389 (by norm_num) ⟨10694, by rfl⟩ (by norm_num))
theorem R57181 : Reach 57181 := rs (se 3 (by rfl) ⟨10721, by rfl⟩) (B 21443 (by norm_num) ⟨10721, by rfl⟩ (by norm_num))
theorem R89957 : Reach 89957 := rs (se 4 (by rfl) ⟨8433, by rfl⟩) (B 16867 (by norm_num) ⟨8433, by rfl⟩ (by norm_num))
theorem R57341 : Reach 57341 := rs (se 3 (by rfl) ⟨10751, by rfl⟩) (B 21503 (by norm_num) ⟨10751, by rfl⟩ (by norm_num))
theorem R122917 : Reach 122917 := rs (se 4 (by rfl) ⟨11523, by rfl⟩) (B 23047 (by norm_num) ⟨11523, by rfl⟩ (by norm_num))
theorem R286805 : Reach 286805 := rs (se 8 (by rfl) ⟨1680, by rfl⟩) (B 3361 (by norm_num) ⟨1680, by rfl⟩ (by norm_num))
theorem R57485 : Reach 57485 := rs (se 3 (by rfl) ⟨10778, by rfl⟩) (B 21557 (by norm_num) ⟨10778, by rfl⟩ (by norm_num))
theorem R57773 : Reach 57773 := rs (se 3 (by rfl) ⟨10832, by rfl⟩) (B 21665 (by norm_num) ⟨10832, by rfl⟩ (by norm_num))
theorem R221717 : Reach 221717 := rs (se 6 (by rfl) ⟨5196, by rfl⟩) (B 10393 (by norm_num) ⟨5196, by rfl⟩ (by norm_num))
theorem R57925 : Reach 57925 := rs (se 4 (by rfl) ⟨5430, by rfl⟩) (B 10861 (by norm_num) ⟨5430, by rfl⟩ (by norm_num))
theorem R58229 : Reach 58229 := rs (se 5 (by rfl) ⟨2729, by rfl⟩) (B 5459 (by norm_num) ⟨2729, by rfl⟩ (by norm_num))
theorem R222101 : Reach 222101 := rs (se 6 (by rfl) ⟨5205, by rfl⟩) (B 10411 (by norm_num) ⟨5205, by rfl⟩ (by norm_num))
theorem R156917 : Reach 156917 := rs (se 5 (by rfl) ⟨7355, by rfl⟩) (B 14711 (by norm_num) ⟨7355, by rfl⟩ (by norm_num))
theorem R91637 : Reach 91637 := rs (se 5 (by rfl) ⟨4295, by rfl⟩) (B 8591 (by norm_num) ⟨4295, by rfl⟩ (by norm_num))
theorem R58981 : Reach 58981 := rs (se 4 (by rfl) ⟨5529, by rfl⟩) (B 11059 (by norm_num) ⟨5529, by rfl⟩ (by norm_num))
theorem R157301 : Reach 157301 := rs (se 5 (by rfl) ⟨7373, by rfl⟩) (B 14747 (by norm_num) ⟨7373, by rfl⟩ (by norm_num))
theorem R59165 : Reach 59165 := rs (se 3 (by rfl) ⟨11093, by rfl⟩) (B 22187 (by norm_num) ⟨11093, by rfl⟩ (by norm_num))
theorem R91957 : Reach 91957 := rs (se 5 (by rfl) ⟨4310, by rfl⟩) (B 8621 (by norm_num) ⟨4310, by rfl⟩ (by norm_num))
theorem R92069 : Reach 92069 := rs (se 4 (by rfl) ⟨8631, by rfl⟩) (B 17263 (by norm_num) ⟨8631, by rfl⟩ (by norm_num))
theorem R256117 : Reach 256117 := rs (se 5 (by rfl) ⟨12005, by rfl⟩) (B 24011 (by norm_num) ⟨12005, by rfl⟩ (by norm_num))
theorem R125077 : Reach 125077 := rs (se 6 (by rfl) ⟨2931, by rfl⟩) (B 5863 (by norm_num) ⟨2931, by rfl⟩ (by norm_num))
theorem R59549 : Reach 59549 := rs (se 3 (by rfl) ⟨11165, by rfl⟩) (B 22331 (by norm_num) ⟨11165, by rfl⟩ (by norm_num))
theorem R92501 : Reach 92501 := rs (se 10 (by rfl) ⟨135, by rfl⟩) (B 271 (by norm_num) ⟨135, by rfl⟩ (by norm_num))
theorem R59869 : Reach 59869 := rs (se 3 (by rfl) ⟨11225, by rfl⟩) (B 22451 (by norm_num) ⟨11225, by rfl⟩ (by norm_num))
theorem R27117 : Reach 27117 := rs (se 3 (by rfl) ⟨5084, by rfl⟩) (B 10169 (by norm_num) ⟨5084, by rfl⟩ (by norm_num))
theorem R27121 : Reach 27121 := rs (se 2 (by rfl) ⟨10170, by rfl⟩) (B 20341 (by norm_num) ⟨10170, by rfl⟩ (by norm_num))
theorem R27125 : Reach 27125 := rs (se 5 (by rfl) ⟨1271, by rfl⟩) (B 2543 (by norm_num) ⟨1271, by rfl⟩ (by norm_num))
theorem R27129 : Reach 27129 := rs (se 2 (by rfl) ⟨10173, by rfl⟩) (B 20347 (by norm_num) ⟨10173, by rfl⟩ (by norm_num))
theorem R27133 : Reach 27133 := rs (se 3 (by rfl) ⟨5087, by rfl⟩) (B 10175 (by norm_num) ⟨5087, by rfl⟩ (by norm_num))
theorem R27137 : Reach 27137 := rs (se 2 (by rfl) ⟨10176, by rfl⟩) (B 20353 (by norm_num) ⟨10176, by rfl⟩ (by norm_num))
theorem R27141 : Reach 27141 := rs (se 4 (by rfl) ⟨2544, by rfl⟩) (B 5089 (by norm_num) ⟨2544, by rfl⟩ (by norm_num))
theorem R27145 : Reach 27145 := rs (se 2 (by rfl) ⟨10179, by rfl⟩) (B 20359 (by norm_num) ⟨10179, by rfl⟩ (by norm_num))
theorem R27149 : Reach 27149 := rs (se 3 (by rfl) ⟨5090, by rfl⟩) (B 10181 (by norm_num) ⟨5090, by rfl⟩ (by norm_num))
theorem R27153 : Reach 27153 := rs (se 2 (by rfl) ⟨10182, by rfl⟩) (B 20365 (by norm_num) ⟨10182, by rfl⟩ (by norm_num))
theorem R27157 : Reach 27157 := rs (se 6 (by rfl) ⟨636, by rfl⟩) (B 1273 (by norm_num) ⟨636, by rfl⟩ (by norm_num))
theorem R27161 : Reach 27161 := rs (se 2 (by rfl) ⟨10185, by rfl⟩) (B 20371 (by norm_num) ⟨10185, by rfl⟩ (by norm_num))
theorem R27165 : Reach 27165 := rs (se 3 (by rfl) ⟨5093, by rfl⟩) (B 10187 (by norm_num) ⟨5093, by rfl⟩ (by norm_num))
theorem R27169 : Reach 27169 := rs (se 2 (by rfl) ⟨10188, by rfl⟩) (B 20377 (by norm_num) ⟨10188, by rfl⟩ (by norm_num))
theorem R27173 : Reach 27173 := rs (se 4 (by rfl) ⟨2547, by rfl⟩) (B 5095 (by norm_num) ⟨2547, by rfl⟩ (by norm_num))
theorem R27177 : Reach 27177 := rs (se 2 (by rfl) ⟨10191, by rfl⟩) (B 20383 (by norm_num) ⟨10191, by rfl⟩ (by norm_num))
theorem R27181 : Reach 27181 := rs (se 3 (by rfl) ⟨5096, by rfl⟩) (B 10193 (by norm_num) ⟨5096, by rfl⟩ (by norm_num))
theorem R27185 : Reach 27185 := rs (se 2 (by rfl) ⟨10194, by rfl⟩) (B 20389 (by norm_num) ⟨10194, by rfl⟩ (by norm_num))
theorem R27189 : Reach 27189 := rs (se 5 (by rfl) ⟨1274, by rfl⟩) (B 2549 (by norm_num) ⟨1274, by rfl⟩ (by norm_num))
theorem R27193 : Reach 27193 := rs (se 2 (by rfl) ⟨10197, by rfl⟩) (B 20395 (by norm_num) ⟨10197, by rfl⟩ (by norm_num))
theorem R27197 : Reach 27197 := rs (se 3 (by rfl) ⟨5099, by rfl⟩) (B 10199 (by norm_num) ⟨5099, by rfl⟩ (by norm_num))
theorem R27201 : Reach 27201 := rs (se 2 (by rfl) ⟨10200, by rfl⟩) (B 20401 (by norm_num) ⟨10200, by rfl⟩ (by norm_num))
theorem R27205 : Reach 27205 := rs (se 4 (by rfl) ⟨2550, by rfl⟩) (B 5101 (by norm_num) ⟨2550, by rfl⟩ (by norm_num))
theorem R27209 : Reach 27209 := rs (se 2 (by rfl) ⟨10203, by rfl⟩) (B 20407 (by norm_num) ⟨10203, by rfl⟩ (by norm_num))
theorem R27213 : Reach 27213 := rs (se 3 (by rfl) ⟨5102, by rfl⟩) (B 10205 (by norm_num) ⟨5102, by rfl⟩ (by norm_num))
theorem R27217 : Reach 27217 := rs (se 2 (by rfl) ⟨10206, by rfl⟩) (B 20413 (by norm_num) ⟨10206, by rfl⟩ (by norm_num))
theorem R27221 : Reach 27221 := rs (se 8 (by rfl) ⟨159, by rfl⟩) (B 319 (by norm_num) ⟨159, by rfl⟩ (by norm_num))
theorem R27225 : Reach 27225 := rs (se 2 (by rfl) ⟨10209, by rfl⟩) (B 20419 (by norm_num) ⟨10209, by rfl⟩ (by norm_num))
theorem R27229 : Reach 27229 := rs (se 3 (by rfl) ⟨5105, by rfl⟩) (B 10211 (by norm_num) ⟨5105, by rfl⟩ (by norm_num))
theorem R27233 : Reach 27233 := rs (se 2 (by rfl) ⟨10212, by rfl⟩) (B 20425 (by norm_num) ⟨10212, by rfl⟩ (by norm_num))
theorem R27237 : Reach 27237 := rs (se 4 (by rfl) ⟨2553, by rfl⟩) (B 5107 (by norm_num) ⟨2553, by rfl⟩ (by norm_num))
theorem R27241 : Reach 27241 := rs (se 2 (by rfl) ⟨10215, by rfl⟩) (B 20431 (by norm_num) ⟨10215, by rfl⟩ (by norm_num))
theorem R27245 : Reach 27245 := rs (se 3 (by rfl) ⟨5108, by rfl⟩) (B 10217 (by norm_num) ⟨5108, by rfl⟩ (by norm_num))
theorem R27249 : Reach 27249 := rs (se 2 (by rfl) ⟨10218, by rfl⟩) (B 20437 (by norm_num) ⟨10218, by rfl⟩ (by norm_num))
theorem R27253 : Reach 27253 := rs (se 5 (by rfl) ⟨1277, by rfl⟩) (B 2555 (by norm_num) ⟨1277, by rfl⟩ (by norm_num))
theorem R27257 : Reach 27257 := rs (se 2 (by rfl) ⟨10221, by rfl⟩) (B 20443 (by norm_num) ⟨10221, by rfl⟩ (by norm_num))
theorem R27261 : Reach 27261 := rs (se 3 (by rfl) ⟨5111, by rfl⟩) (B 10223 (by norm_num) ⟨5111, by rfl⟩ (by norm_num))
theorem R27265 : Reach 27265 := rs (se 2 (by rfl) ⟨10224, by rfl⟩) (B 20449 (by norm_num) ⟨10224, by rfl⟩ (by norm_num))
theorem R27269 : Reach 27269 := rs (se 4 (by rfl) ⟨2556, by rfl⟩) (B 5113 (by norm_num) ⟨2556, by rfl⟩ (by norm_num))
theorem R27273 : Reach 27273 := rs (se 2 (by rfl) ⟨10227, by rfl⟩) (B 20455 (by norm_num) ⟨10227, by rfl⟩ (by norm_num))
theorem R27277 : Reach 27277 := rs (se 3 (by rfl) ⟨5114, by rfl⟩) (B 10229 (by norm_num) ⟨5114, by rfl⟩ (by norm_num))
theorem R27281 : Reach 27281 := rs (se 2 (by rfl) ⟨10230, by rfl⟩) (B 20461 (by norm_num) ⟨10230, by rfl⟩ (by norm_num))
theorem R27285 : Reach 27285 := rs (se 6 (by rfl) ⟨639, by rfl⟩) (B 1279 (by norm_num) ⟨639, by rfl⟩ (by norm_num))
theorem R27289 : Reach 27289 := rs (se 2 (by rfl) ⟨10233, by rfl⟩) (B 20467 (by norm_num) ⟨10233, by rfl⟩ (by norm_num))
theorem R27293 : Reach 27293 := rs (se 3 (by rfl) ⟨5117, by rfl⟩) (B 10235 (by norm_num) ⟨5117, by rfl⟩ (by norm_num))
theorem R27297 : Reach 27297 := rs (se 2 (by rfl) ⟨10236, by rfl⟩) (B 20473 (by norm_num) ⟨10236, by rfl⟩ (by norm_num))
theorem R27301 : Reach 27301 := rs (se 4 (by rfl) ⟨2559, by rfl⟩) (B 5119 (by norm_num) ⟨2559, by rfl⟩ (by norm_num))
theorem R27305 : Reach 27305 := rs (se 2 (by rfl) ⟨10239, by rfl⟩) (B 20479 (by norm_num) ⟨10239, by rfl⟩ (by norm_num))
theorem R27309 : Reach 27309 := rs (se 3 (by rfl) ⟨5120, by rfl⟩) (B 10241 (by norm_num) ⟨5120, by rfl⟩ (by norm_num))
theorem R27313 : Reach 27313 := rs (se 2 (by rfl) ⟨10242, by rfl⟩) (B 20485 (by norm_num) ⟨10242, by rfl⟩ (by norm_num))
theorem R27317 : Reach 27317 := rs (se 5 (by rfl) ⟨1280, by rfl⟩) (B 2561 (by norm_num) ⟨1280, by rfl⟩ (by norm_num))
theorem R27321 : Reach 27321 := rs (se 2 (by rfl) ⟨10245, by rfl⟩) (B 20491 (by norm_num) ⟨10245, by rfl⟩ (by norm_num))
theorem R27325 : Reach 27325 := rs (se 3 (by rfl) ⟨5123, by rfl⟩) (B 10247 (by norm_num) ⟨5123, by rfl⟩ (by norm_num))
theorem R27329 : Reach 27329 := rs (se 2 (by rfl) ⟨10248, by rfl⟩) (B 20497 (by norm_num) ⟨10248, by rfl⟩ (by norm_num))
theorem R27333 : Reach 27333 := rs (se 4 (by rfl) ⟨2562, by rfl⟩) (B 5125 (by norm_num) ⟨2562, by rfl⟩ (by norm_num))
theorem R27337 : Reach 27337 := rs (se 2 (by rfl) ⟨10251, by rfl⟩) (B 20503 (by norm_num) ⟨10251, by rfl⟩ (by norm_num))
theorem R27341 : Reach 27341 := rs (se 3 (by rfl) ⟨5126, by rfl⟩) (B 10253 (by norm_num) ⟨5126, by rfl⟩ (by norm_num))
theorem R27345 : Reach 27345 := rs (se 2 (by rfl) ⟨10254, by rfl⟩) (B 20509 (by norm_num) ⟨10254, by rfl⟩ (by norm_num))
theorem R27349 : Reach 27349 := rs (se 7 (by rfl) ⟨320, by rfl⟩) (B 641 (by norm_num) ⟨320, by rfl⟩ (by norm_num))
theorem R27353 : Reach 27353 := rs (se 2 (by rfl) ⟨10257, by rfl⟩) (B 20515 (by norm_num) ⟨10257, by rfl⟩ (by norm_num))
theorem R27357 : Reach 27357 := rs (se 3 (by rfl) ⟨5129, by rfl⟩) (B 10259 (by norm_num) ⟨5129, by rfl⟩ (by norm_num))
theorem R27361 : Reach 27361 := rs (se 2 (by rfl) ⟨10260, by rfl⟩) (B 20521 (by norm_num) ⟨10260, by rfl⟩ (by norm_num))
theorem R27365 : Reach 27365 := rs (se 4 (by rfl) ⟨2565, by rfl⟩) (B 5131 (by norm_num) ⟨2565, by rfl⟩ (by norm_num))
theorem R27369 : Reach 27369 := rs (se 2 (by rfl) ⟨10263, by rfl⟩) (B 20527 (by norm_num) ⟨10263, by rfl⟩ (by norm_num))
theorem R27373 : Reach 27373 := rs (se 3 (by rfl) ⟨5132, by rfl⟩) (B 10265 (by norm_num) ⟨5132, by rfl⟩ (by norm_num))
theorem R27377 : Reach 27377 := rs (se 2 (by rfl) ⟨10266, by rfl⟩) (B 20533 (by norm_num) ⟨10266, by rfl⟩ (by norm_num))
theorem R27381 : Reach 27381 := rs (se 5 (by rfl) ⟨1283, by rfl⟩) (B 2567 (by norm_num) ⟨1283, by rfl⟩ (by norm_num))
theorem R27385 : Reach 27385 := rs (se 2 (by rfl) ⟨10269, by rfl⟩) (B 20539 (by norm_num) ⟨10269, by rfl⟩ (by norm_num))
theorem R27389 : Reach 27389 := rs (se 3 (by rfl) ⟨5135, by rfl⟩) (B 10271 (by norm_num) ⟨5135, by rfl⟩ (by norm_num))
theorem R27393 : Reach 27393 := rs (se 2 (by rfl) ⟨10272, by rfl⟩) (B 20545 (by norm_num) ⟨10272, by rfl⟩ (by norm_num))
theorem R27397 : Reach 27397 := rs (se 4 (by rfl) ⟨2568, by rfl⟩) (B 5137 (by norm_num) ⟨2568, by rfl⟩ (by norm_num))
theorem R92933 : Reach 92933 := rs (se 4 (by rfl) ⟨8712, by rfl⟩) (B 17425 (by norm_num) ⟨8712, by rfl⟩ (by norm_num))
theorem R27401 : Reach 27401 := rs (se 2 (by rfl) ⟨10275, by rfl⟩) (B 20551 (by norm_num) ⟨10275, by rfl⟩ (by norm_num))
theorem R27405 : Reach 27405 := rs (se 3 (by rfl) ⟨5138, by rfl⟩) (B 10277 (by norm_num) ⟨5138, by rfl⟩ (by norm_num))
theorem R27409 : Reach 27409 := rs (se 2 (by rfl) ⟨10278, by rfl⟩) (B 20557 (by norm_num) ⟨10278, by rfl⟩ (by norm_num))
theorem R27413 : Reach 27413 := rs (se 6 (by rfl) ⟨642, by rfl⟩) (B 1285 (by norm_num) ⟨642, by rfl⟩ (by norm_num))
theorem R27417 : Reach 27417 := rs (se 2 (by rfl) ⟨10281, by rfl⟩) (B 20563 (by norm_num) ⟨10281, by rfl⟩ (by norm_num))
theorem R27421 : Reach 27421 := rs (se 3 (by rfl) ⟨5141, by rfl⟩) (B 10283 (by norm_num) ⟨5141, by rfl⟩ (by norm_num))
theorem R27425 : Reach 27425 := rs (se 2 (by rfl) ⟨10284, by rfl⟩) (B 20569 (by norm_num) ⟨10284, by rfl⟩ (by norm_num))
theorem R27429 : Reach 27429 := rs (se 4 (by rfl) ⟨2571, by rfl⟩) (B 5143 (by norm_num) ⟨2571, by rfl⟩ (by norm_num))
theorem R27433 : Reach 27433 := rs (se 2 (by rfl) ⟨10287, by rfl⟩) (B 20575 (by norm_num) ⟨10287, by rfl⟩ (by norm_num))
theorem R27437 : Reach 27437 := rs (se 3 (by rfl) ⟨5144, by rfl⟩) (B 10289 (by norm_num) ⟨5144, by rfl⟩ (by norm_num))
theorem R27441 : Reach 27441 := rs (se 2 (by rfl) ⟨10290, by rfl⟩) (B 20581 (by norm_num) ⟨10290, by rfl⟩ (by norm_num))
theorem R27445 : Reach 27445 := rs (se 5 (by rfl) ⟨1286, by rfl⟩) (B 2573 (by norm_num) ⟨1286, by rfl⟩ (by norm_num))
theorem R27449 : Reach 27449 := rs (se 2 (by rfl) ⟨10293, by rfl⟩) (B 20587 (by norm_num) ⟨10293, by rfl⟩ (by norm_num))
theorem R27453 : Reach 27453 := rs (se 3 (by rfl) ⟨5147, by rfl⟩) (B 10295 (by norm_num) ⟨5147, by rfl⟩ (by norm_num))
theorem R27457 : Reach 27457 := rs (se 2 (by rfl) ⟨10296, by rfl⟩) (B 20593 (by norm_num) ⟨10296, by rfl⟩ (by norm_num))
theorem R27461 : Reach 27461 := rs (se 4 (by rfl) ⟨2574, by rfl⟩) (B 5149 (by norm_num) ⟨2574, by rfl⟩ (by norm_num))
theorem R27465 : Reach 27465 := rs (se 2 (by rfl) ⟨10299, by rfl⟩) (B 20599 (by norm_num) ⟨10299, by rfl⟩ (by norm_num))
theorem R27469 : Reach 27469 := rs (se 3 (by rfl) ⟨5150, by rfl⟩) (B 10301 (by norm_num) ⟨5150, by rfl⟩ (by norm_num))
theorem R27473 : Reach 27473 := rs (se 2 (by rfl) ⟨10302, by rfl⟩) (B 20605 (by norm_num) ⟨10302, by rfl⟩ (by norm_num))
theorem R27477 : Reach 27477 := rs (se 9 (by rfl) ⟨80, by rfl⟩) (B 161 (by norm_num) ⟨80, by rfl⟩ (by norm_num))
theorem R27481 : Reach 27481 := rs (se 2 (by rfl) ⟨10305, by rfl⟩) (B 20611 (by norm_num) ⟨10305, by rfl⟩ (by norm_num))
theorem R27485 : Reach 27485 := rs (se 3 (by rfl) ⟨5153, by rfl⟩) (B 10307 (by norm_num) ⟨5153, by rfl⟩ (by norm_num))
theorem R27489 : Reach 27489 := rs (se 2 (by rfl) ⟨10308, by rfl⟩) (B 20617 (by norm_num) ⟨10308, by rfl⟩ (by norm_num))
theorem R27493 : Reach 27493 := rs (se 4 (by rfl) ⟨2577, by rfl⟩) (B 5155 (by norm_num) ⟨2577, by rfl⟩ (by norm_num))
theorem R27497 : Reach 27497 := rs (se 2 (by rfl) ⟨10311, by rfl⟩) (B 20623 (by norm_num) ⟨10311, by rfl⟩ (by norm_num))
theorem R27501 : Reach 27501 := rs (se 3 (by rfl) ⟨5156, by rfl⟩) (B 10313 (by norm_num) ⟨5156, by rfl⟩ (by norm_num))
theorem R27505 : Reach 27505 := rs (se 2 (by rfl) ⟨10314, by rfl⟩) (B 20629 (by norm_num) ⟨10314, by rfl⟩ (by norm_num))
theorem R27509 : Reach 27509 := rs (se 5 (by rfl) ⟨1289, by rfl⟩) (B 2579 (by norm_num) ⟨1289, by rfl⟩ (by norm_num))
theorem R27513 : Reach 27513 := rs (se 2 (by rfl) ⟨10317, by rfl⟩) (B 20635 (by norm_num) ⟨10317, by rfl⟩ (by norm_num))
theorem R27517 : Reach 27517 := rs (se 3 (by rfl) ⟨5159, by rfl⟩) (B 10319 (by norm_num) ⟨5159, by rfl⟩ (by norm_num))
theorem R27521 : Reach 27521 := rs (se 2 (by rfl) ⟨10320, by rfl⟩) (B 20641 (by norm_num) ⟨10320, by rfl⟩ (by norm_num))
theorem R27525 : Reach 27525 := rs (se 4 (by rfl) ⟨2580, by rfl⟩) (B 5161 (by norm_num) ⟨2580, by rfl⟩ (by norm_num))
theorem R27529 : Reach 27529 := rs (se 2 (by rfl) ⟨10323, by rfl⟩) (B 20647 (by norm_num) ⟨10323, by rfl⟩ (by norm_num))
theorem R27533 : Reach 27533 := rs (se 3 (by rfl) ⟨5162, by rfl⟩) (B 10325 (by norm_num) ⟨5162, by rfl⟩ (by norm_num))
theorem R27537 : Reach 27537 := rs (se 2 (by rfl) ⟨10326, by rfl⟩) (B 20653 (by norm_num) ⟨10326, by rfl⟩ (by norm_num))
theorem R27541 : Reach 27541 := rs (se 6 (by rfl) ⟨645, by rfl⟩) (B 1291 (by norm_num) ⟨645, by rfl⟩ (by norm_num))
theorem R27545 : Reach 27545 := rs (se 2 (by rfl) ⟨10329, by rfl⟩) (B 20659 (by norm_num) ⟨10329, by rfl⟩ (by norm_num))
theorem R27549 : Reach 27549 := rs (se 3 (by rfl) ⟨5165, by rfl⟩) (B 10331 (by norm_num) ⟨5165, by rfl⟩ (by norm_num))
theorem R27553 : Reach 27553 := rs (se 2 (by rfl) ⟨10332, by rfl⟩) (B 20665 (by norm_num) ⟨10332, by rfl⟩ (by norm_num))
theorem R27557 : Reach 27557 := rs (se 4 (by rfl) ⟨2583, by rfl⟩) (B 5167 (by norm_num) ⟨2583, by rfl⟩ (by norm_num))
theorem R27561 : Reach 27561 := rs (se 2 (by rfl) ⟨10335, by rfl⟩) (B 20671 (by norm_num) ⟨10335, by rfl⟩ (by norm_num))
theorem R27565 : Reach 27565 := rs (se 3 (by rfl) ⟨5168, by rfl⟩) (B 10337 (by norm_num) ⟨5168, by rfl⟩ (by norm_num))
theorem R27569 : Reach 27569 := rs (se 2 (by rfl) ⟨10338, by rfl⟩) (B 20677 (by norm_num) ⟨10338, by rfl⟩ (by norm_num))
theorem R27573 : Reach 27573 := rs (se 5 (by rfl) ⟨1292, by rfl⟩) (B 2585 (by norm_num) ⟨1292, by rfl⟩ (by norm_num))
theorem R27577 : Reach 27577 := rs (se 2 (by rfl) ⟨10341, by rfl⟩) (B 20683 (by norm_num) ⟨10341, by rfl⟩ (by norm_num))
theorem R27581 : Reach 27581 := rs (se 3 (by rfl) ⟨5171, by rfl⟩) (B 10343 (by norm_num) ⟨5171, by rfl⟩ (by norm_num))
theorem R27585 : Reach 27585 := rs (se 2 (by rfl) ⟨10344, by rfl⟩) (B 20689 (by norm_num) ⟨10344, by rfl⟩ (by norm_num))
theorem R27589 : Reach 27589 := rs (se 4 (by rfl) ⟨2586, by rfl⟩) (B 5173 (by norm_num) ⟨2586, by rfl⟩ (by norm_num))
theorem R27593 : Reach 27593 := rs (se 2 (by rfl) ⟨10347, by rfl⟩) (B 20695 (by norm_num) ⟨10347, by rfl⟩ (by norm_num))
theorem R27597 : Reach 27597 := rs (se 3 (by rfl) ⟨5174, by rfl⟩) (B 10349 (by norm_num) ⟨5174, by rfl⟩ (by norm_num))
theorem R60365 : Reach 60365 := rs (se 3 (by rfl) ⟨11318, by rfl⟩) (B 22637 (by norm_num) ⟨11318, by rfl⟩ (by norm_num))
theorem R27601 : Reach 27601 := rs (se 2 (by rfl) ⟨10350, by rfl⟩) (B 20701 (by norm_num) ⟨10350, by rfl⟩ (by norm_num))
theorem R27605 : Reach 27605 := rs (se 7 (by rfl) ⟨323, by rfl⟩) (B 647 (by norm_num) ⟨323, by rfl⟩ (by norm_num))
theorem R27609 : Reach 27609 := rs (se 2 (by rfl) ⟨10353, by rfl⟩) (B 20707 (by norm_num) ⟨10353, by rfl⟩ (by norm_num))
theorem R27613 : Reach 27613 := rs (se 3 (by rfl) ⟨5177, by rfl⟩) (B 10355 (by norm_num) ⟨5177, by rfl⟩ (by norm_num))
theorem R27617 : Reach 27617 := rs (se 2 (by rfl) ⟨10356, by rfl⟩) (B 20713 (by norm_num) ⟨10356, by rfl⟩ (by norm_num))
theorem R27621 : Reach 27621 := rs (se 4 (by rfl) ⟨2589, by rfl⟩) (B 5179 (by norm_num) ⟨2589, by rfl⟩ (by norm_num))
theorem R27625 : Reach 27625 := rs (se 2 (by rfl) ⟨10359, by rfl⟩) (B 20719 (by norm_num) ⟨10359, by rfl⟩ (by norm_num))
theorem R27629 : Reach 27629 := rs (se 3 (by rfl) ⟨5180, by rfl⟩) (B 10361 (by norm_num) ⟨5180, by rfl⟩ (by norm_num))
theorem R27633 : Reach 27633 := rs (se 2 (by rfl) ⟨10362, by rfl⟩) (B 20725 (by norm_num) ⟨10362, by rfl⟩ (by norm_num))
theorem R27637 : Reach 27637 := rs (se 5 (by rfl) ⟨1295, by rfl⟩) (B 2591 (by norm_num) ⟨1295, by rfl⟩ (by norm_num))
theorem R27641 : Reach 27641 := rs (se 2 (by rfl) ⟨10365, by rfl⟩) (B 20731 (by norm_num) ⟨10365, by rfl⟩ (by norm_num))
theorem R27645 : Reach 27645 := rs (se 3 (by rfl) ⟨5183, by rfl⟩) (B 10367 (by norm_num) ⟨5183, by rfl⟩ (by norm_num))
theorem R27649 : Reach 27649 := rs (se 2 (by rfl) ⟨10368, by rfl⟩) (B 20737 (by norm_num) ⟨10368, by rfl⟩ (by norm_num))
theorem R27653 : Reach 27653 := rs (se 4 (by rfl) ⟨2592, by rfl⟩) (B 5185 (by norm_num) ⟨2592, by rfl⟩ (by norm_num))
theorem R27657 : Reach 27657 := rs (se 2 (by rfl) ⟨10371, by rfl⟩) (B 20743 (by norm_num) ⟨10371, by rfl⟩ (by norm_num))
theorem R27661 : Reach 27661 := rs (se 3 (by rfl) ⟨5186, by rfl⟩) (B 10373 (by norm_num) ⟨5186, by rfl⟩ (by norm_num))
theorem R27665 : Reach 27665 := rs (se 2 (by rfl) ⟨10374, by rfl⟩) (B 20749 (by norm_num) ⟨10374, by rfl⟩ (by norm_num))
theorem R27669 : Reach 27669 := rs (se 6 (by rfl) ⟨648, by rfl⟩) (B 1297 (by norm_num) ⟨648, by rfl⟩ (by norm_num))
theorem R27673 : Reach 27673 := rs (se 2 (by rfl) ⟨10377, by rfl⟩) (B 20755 (by norm_num) ⟨10377, by rfl⟩ (by norm_num))
theorem R27677 : Reach 27677 := rs (se 3 (by rfl) ⟨5189, by rfl⟩) (B 10379 (by norm_num) ⟨5189, by rfl⟩ (by norm_num))
theorem R27681 : Reach 27681 := rs (se 2 (by rfl) ⟨10380, by rfl⟩) (B 20761 (by norm_num) ⟨10380, by rfl⟩ (by norm_num))
theorem R93221 : Reach 93221 := rs (se 4 (by rfl) ⟨8739, by rfl⟩) (B 17479 (by norm_num) ⟨8739, by rfl⟩ (by norm_num))
theorem R27685 : Reach 27685 := rs (se 4 (by rfl) ⟨2595, by rfl⟩) (B 5191 (by norm_num) ⟨2595, by rfl⟩ (by norm_num))
theorem R27689 : Reach 27689 := rs (se 2 (by rfl) ⟨10383, by rfl⟩) (B 20767 (by norm_num) ⟨10383, by rfl⟩ (by norm_num))
theorem R27693 : Reach 27693 := rs (se 3 (by rfl) ⟨5192, by rfl⟩) (B 10385 (by norm_num) ⟨5192, by rfl⟩ (by norm_num))
theorem R27697 : Reach 27697 := rs (se 2 (by rfl) ⟨10386, by rfl⟩) (B 20773 (by norm_num) ⟨10386, by rfl⟩ (by norm_num))
theorem R27701 : Reach 27701 := rs (se 5 (by rfl) ⟨1298, by rfl⟩) (B 2597 (by norm_num) ⟨1298, by rfl⟩ (by norm_num))
theorem R27705 : Reach 27705 := rs (se 2 (by rfl) ⟨10389, by rfl⟩) (B 20779 (by norm_num) ⟨10389, by rfl⟩ (by norm_num))
theorem R27709 : Reach 27709 := rs (se 3 (by rfl) ⟨5195, by rfl⟩) (B 10391 (by norm_num) ⟨5195, by rfl⟩ (by norm_num))
theorem R27713 : Reach 27713 := rs (se 2 (by rfl) ⟨10392, by rfl⟩) (B 20785 (by norm_num) ⟨10392, by rfl⟩ (by norm_num))
theorem R27717 : Reach 27717 := rs (se 4 (by rfl) ⟨2598, by rfl⟩) (B 5197 (by norm_num) ⟨2598, by rfl⟩ (by norm_num))
theorem R27721 : Reach 27721 := rs (se 2 (by rfl) ⟨10395, by rfl⟩) (B 20791 (by norm_num) ⟨10395, by rfl⟩ (by norm_num))
theorem R27725 : Reach 27725 := rs (se 3 (by rfl) ⟨5198, by rfl⟩) (B 10397 (by norm_num) ⟨5198, by rfl⟩ (by norm_num))
theorem R27729 : Reach 27729 := rs (se 2 (by rfl) ⟨10398, by rfl⟩) (B 20797 (by norm_num) ⟨10398, by rfl⟩ (by norm_num))
theorem R27733 : Reach 27733 := rs (se 8 (by rfl) ⟨162, by rfl⟩) (B 325 (by norm_num) ⟨162, by rfl⟩ (by norm_num))
theorem R27737 : Reach 27737 := rs (se 2 (by rfl) ⟨10401, by rfl⟩) (B 20803 (by norm_num) ⟨10401, by rfl⟩ (by norm_num))
theorem R27741 : Reach 27741 := rs (se 3 (by rfl) ⟨5201, by rfl⟩) (B 10403 (by norm_num) ⟨5201, by rfl⟩ (by norm_num))
theorem R27745 : Reach 27745 := rs (se 2 (by rfl) ⟨10404, by rfl⟩) (B 20809 (by norm_num) ⟨10404, by rfl⟩ (by norm_num))
theorem R27749 : Reach 27749 := rs (se 4 (by rfl) ⟨2601, by rfl⟩) (B 5203 (by norm_num) ⟨2601, by rfl⟩ (by norm_num))
theorem R27753 : Reach 27753 := rs (se 2 (by rfl) ⟨10407, by rfl⟩) (B 20815 (by norm_num) ⟨10407, by rfl⟩ (by norm_num))
theorem R27757 : Reach 27757 := rs (se 3 (by rfl) ⟨5204, by rfl⟩) (B 10409 (by norm_num) ⟨5204, by rfl⟩ (by norm_num))
theorem R27761 : Reach 27761 := rs (se 2 (by rfl) ⟨10410, by rfl⟩) (B 20821 (by norm_num) ⟨10410, by rfl⟩ (by norm_num))
theorem R27765 : Reach 27765 := rs (se 5 (by rfl) ⟨1301, by rfl⟩) (B 2603 (by norm_num) ⟨1301, by rfl⟩ (by norm_num))
theorem R27769 : Reach 27769 := rs (se 2 (by rfl) ⟨10413, by rfl⟩) (B 20827 (by norm_num) ⟨10413, by rfl⟩ (by norm_num))
theorem R27773 : Reach 27773 := rs (se 3 (by rfl) ⟨5207, by rfl⟩) (B 10415 (by norm_num) ⟨5207, by rfl⟩ (by norm_num))
theorem R27777 : Reach 27777 := rs (se 2 (by rfl) ⟨10416, by rfl⟩) (B 20833 (by norm_num) ⟨10416, by rfl⟩ (by norm_num))
theorem R27781 : Reach 27781 := rs (se 4 (by rfl) ⟨2604, by rfl⟩) (B 5209 (by norm_num) ⟨2604, by rfl⟩ (by norm_num))
theorem R27785 : Reach 27785 := rs (se 2 (by rfl) ⟨10419, by rfl⟩) (B 20839 (by norm_num) ⟨10419, by rfl⟩ (by norm_num))
theorem R27789 : Reach 27789 := rs (se 3 (by rfl) ⟨5210, by rfl⟩) (B 10421 (by norm_num) ⟨5210, by rfl⟩ (by norm_num))
theorem R27793 : Reach 27793 := rs (se 2 (by rfl) ⟨10422, by rfl⟩) (B 20845 (by norm_num) ⟨10422, by rfl⟩ (by norm_num))
theorem R27797 : Reach 27797 := rs (se 6 (by rfl) ⟨651, by rfl⟩) (B 1303 (by norm_num) ⟨651, by rfl⟩ (by norm_num))
theorem R27801 : Reach 27801 := rs (se 2 (by rfl) ⟨10425, by rfl⟩) (B 20851 (by norm_num) ⟨10425, by rfl⟩ (by norm_num))
theorem R27805 : Reach 27805 := rs (se 3 (by rfl) ⟨5213, by rfl⟩) (B 10427 (by norm_num) ⟨5213, by rfl⟩ (by norm_num))
theorem R27809 : Reach 27809 := rs (se 2 (by rfl) ⟨10428, by rfl⟩) (B 20857 (by norm_num) ⟨10428, by rfl⟩ (by norm_num))
theorem R27813 : Reach 27813 := rs (se 4 (by rfl) ⟨2607, by rfl⟩) (B 5215 (by norm_num) ⟨2607, by rfl⟩ (by norm_num))
theorem R27817 : Reach 27817 := rs (se 2 (by rfl) ⟨10431, by rfl⟩) (B 20863 (by norm_num) ⟨10431, by rfl⟩ (by norm_num))
theorem R27821 : Reach 27821 := rs (se 3 (by rfl) ⟨5216, by rfl⟩) (B 10433 (by norm_num) ⟨5216, by rfl⟩ (by norm_num))
theorem R27825 : Reach 27825 := rs (se 2 (by rfl) ⟨10434, by rfl⟩) (B 20869 (by norm_num) ⟨10434, by rfl⟩ (by norm_num))
theorem R93365 : Reach 93365 := rs (se 5 (by rfl) ⟨4376, by rfl⟩) (B 8753 (by norm_num) ⟨4376, by rfl⟩ (by norm_num))
theorem R27829 : Reach 27829 := rs (se 5 (by rfl) ⟨1304, by rfl⟩) (B 2609 (by norm_num) ⟨1304, by rfl⟩ (by norm_num))
theorem R27833 : Reach 27833 := rs (se 2 (by rfl) ⟨10437, by rfl⟩) (B 20875 (by norm_num) ⟨10437, by rfl⟩ (by norm_num))
theorem R27837 : Reach 27837 := rs (se 3 (by rfl) ⟨5219, by rfl⟩) (B 10439 (by norm_num) ⟨5219, by rfl⟩ (by norm_num))
theorem R27841 : Reach 27841 := rs (se 2 (by rfl) ⟨10440, by rfl⟩) (B 20881 (by norm_num) ⟨10440, by rfl⟩ (by norm_num))
theorem R27845 : Reach 27845 := rs (se 4 (by rfl) ⟨2610, by rfl⟩) (B 5221 (by norm_num) ⟨2610, by rfl⟩ (by norm_num))
theorem R27849 : Reach 27849 := rs (se 2 (by rfl) ⟨10443, by rfl⟩) (B 20887 (by norm_num) ⟨10443, by rfl⟩ (by norm_num))
theorem R27853 : Reach 27853 := rs (se 3 (by rfl) ⟨5222, by rfl⟩) (B 10445 (by norm_num) ⟨5222, by rfl⟩ (by norm_num))
theorem R27857 : Reach 27857 := rs (se 2 (by rfl) ⟨10446, by rfl⟩) (B 20893 (by norm_num) ⟨10446, by rfl⟩ (by norm_num))
theorem R27861 : Reach 27861 := rs (se 7 (by rfl) ⟨326, by rfl⟩) (B 653 (by norm_num) ⟨326, by rfl⟩ (by norm_num))
theorem R27865 : Reach 27865 := rs (se 2 (by rfl) ⟨10449, by rfl⟩) (B 20899 (by norm_num) ⟨10449, by rfl⟩ (by norm_num))
theorem R27869 : Reach 27869 := rs (se 3 (by rfl) ⟨5225, by rfl⟩) (B 10451 (by norm_num) ⟨5225, by rfl⟩ (by norm_num))
theorem R27873 : Reach 27873 := rs (se 2 (by rfl) ⟨10452, by rfl⟩) (B 20905 (by norm_num) ⟨10452, by rfl⟩ (by norm_num))
theorem R27877 : Reach 27877 := rs (se 4 (by rfl) ⟨2613, by rfl⟩) (B 5227 (by norm_num) ⟨2613, by rfl⟩ (by norm_num))
theorem R27881 : Reach 27881 := rs (se 2 (by rfl) ⟨10455, by rfl⟩) (B 20911 (by norm_num) ⟨10455, by rfl⟩ (by norm_num))
theorem R27885 : Reach 27885 := rs (se 3 (by rfl) ⟨5228, by rfl⟩) (B 10457 (by norm_num) ⟨5228, by rfl⟩ (by norm_num))
theorem R27889 : Reach 27889 := rs (se 2 (by rfl) ⟨10458, by rfl⟩) (B 20917 (by norm_num) ⟨10458, by rfl⟩ (by norm_num))
theorem R27893 : Reach 27893 := rs (se 5 (by rfl) ⟨1307, by rfl⟩) (B 2615 (by norm_num) ⟨1307, by rfl⟩ (by norm_num))
theorem R27897 : Reach 27897 := rs (se 2 (by rfl) ⟨10461, by rfl⟩) (B 20923 (by norm_num) ⟨10461, by rfl⟩ (by norm_num))
theorem R27901 : Reach 27901 := rs (se 3 (by rfl) ⟨5231, by rfl⟩) (B 10463 (by norm_num) ⟨5231, by rfl⟩ (by norm_num))
theorem R27905 : Reach 27905 := rs (se 2 (by rfl) ⟨10464, by rfl⟩) (B 20929 (by norm_num) ⟨10464, by rfl⟩ (by norm_num))
theorem R27909 : Reach 27909 := rs (se 4 (by rfl) ⟨2616, by rfl⟩) (B 5233 (by norm_num) ⟨2616, by rfl⟩ (by norm_num))
theorem R27913 : Reach 27913 := rs (se 2 (by rfl) ⟨10467, by rfl⟩) (B 20935 (by norm_num) ⟨10467, by rfl⟩ (by norm_num))
theorem R27917 : Reach 27917 := rs (se 3 (by rfl) ⟨5234, by rfl⟩) (B 10469 (by norm_num) ⟨5234, by rfl⟩ (by norm_num))
theorem R27921 : Reach 27921 := rs (se 2 (by rfl) ⟨10470, by rfl⟩) (B 20941 (by norm_num) ⟨10470, by rfl⟩ (by norm_num))
theorem R27925 : Reach 27925 := rs (se 6 (by rfl) ⟨654, by rfl⟩) (B 1309 (by norm_num) ⟨654, by rfl⟩ (by norm_num))
theorem R27929 : Reach 27929 := rs (se 2 (by rfl) ⟨10473, by rfl⟩) (B 20947 (by norm_num) ⟨10473, by rfl⟩ (by norm_num))
theorem R27933 : Reach 27933 := rs (se 3 (by rfl) ⟨5237, by rfl⟩) (B 10475 (by norm_num) ⟨5237, by rfl⟩ (by norm_num))
theorem R27937 : Reach 27937 := rs (se 2 (by rfl) ⟨10476, by rfl⟩) (B 20953 (by norm_num) ⟨10476, by rfl⟩ (by norm_num))
theorem R27941 : Reach 27941 := rs (se 4 (by rfl) ⟨2619, by rfl⟩) (B 5239 (by norm_num) ⟨2619, by rfl⟩ (by norm_num))
theorem R27945 : Reach 27945 := rs (se 2 (by rfl) ⟨10479, by rfl⟩) (B 20959 (by norm_num) ⟨10479, by rfl⟩ (by norm_num))
theorem R27949 : Reach 27949 := rs (se 3 (by rfl) ⟨5240, by rfl⟩) (B 10481 (by norm_num) ⟨5240, by rfl⟩ (by norm_num))
theorem R27953 : Reach 27953 := rs (se 2 (by rfl) ⟨10482, by rfl⟩) (B 20965 (by norm_num) ⟨10482, by rfl⟩ (by norm_num))
theorem R27957 : Reach 27957 := rs (se 5 (by rfl) ⟨1310, by rfl⟩) (B 2621 (by norm_num) ⟨1310, by rfl⟩ (by norm_num))
theorem R159029 : Reach 159029 := rs (se 5 (by rfl) ⟨7454, by rfl⟩) (B 14909 (by norm_num) ⟨7454, by rfl⟩ (by norm_num))
theorem R27961 : Reach 27961 := rs (se 2 (by rfl) ⟨10485, by rfl⟩) (B 20971 (by norm_num) ⟨10485, by rfl⟩ (by norm_num))
theorem R27965 : Reach 27965 := rs (se 3 (by rfl) ⟨5243, by rfl⟩) (B 10487 (by norm_num) ⟨5243, by rfl⟩ (by norm_num))
theorem R27969 : Reach 27969 := rs (se 2 (by rfl) ⟨10488, by rfl⟩) (B 20977 (by norm_num) ⟨10488, by rfl⟩ (by norm_num))
theorem R27973 : Reach 27973 := rs (se 4 (by rfl) ⟨2622, by rfl⟩) (B 5245 (by norm_num) ⟨2622, by rfl⟩ (by norm_num))
theorem R27977 : Reach 27977 := rs (se 2 (by rfl) ⟨10491, by rfl⟩) (B 20983 (by norm_num) ⟨10491, by rfl⟩ (by norm_num))
theorem R27981 : Reach 27981 := rs (se 3 (by rfl) ⟨5246, by rfl⟩) (B 10493 (by norm_num) ⟨5246, by rfl⟩ (by norm_num))
theorem R27985 : Reach 27985 := rs (se 2 (by rfl) ⟨10494, by rfl⟩) (B 20989 (by norm_num) ⟨10494, by rfl⟩ (by norm_num))
theorem R27989 : Reach 27989 := rs (se 11 (by rfl) ⟨20, by rfl⟩) (B 41 (by norm_num) ⟨20, by rfl⟩ (by norm_num))
theorem R27993 : Reach 27993 := rs (se 2 (by rfl) ⟨10497, by rfl⟩) (B 20995 (by norm_num) ⟨10497, by rfl⟩ (by norm_num))
theorem R27997 : Reach 27997 := rs (se 3 (by rfl) ⟨5249, by rfl⟩) (B 10499 (by norm_num) ⟨5249, by rfl⟩ (by norm_num))
theorem R28001 : Reach 28001 := rs (se 2 (by rfl) ⟨10500, by rfl⟩) (B 21001 (by norm_num) ⟨10500, by rfl⟩ (by norm_num))
theorem R28005 : Reach 28005 := rs (se 4 (by rfl) ⟨2625, by rfl⟩) (B 5251 (by norm_num) ⟨2625, by rfl⟩ (by norm_num))
theorem R28009 : Reach 28009 := rs (se 2 (by rfl) ⟨10503, by rfl⟩) (B 21007 (by norm_num) ⟨10503, by rfl⟩ (by norm_num))
theorem R28013 : Reach 28013 := rs (se 3 (by rfl) ⟨5252, by rfl⟩) (B 10505 (by norm_num) ⟨5252, by rfl⟩ (by norm_num))
theorem R28017 : Reach 28017 := rs (se 2 (by rfl) ⟨10506, by rfl⟩) (B 21013 (by norm_num) ⟨10506, by rfl⟩ (by norm_num))
theorem R28021 : Reach 28021 := rs (se 5 (by rfl) ⟨1313, by rfl⟩) (B 2627 (by norm_num) ⟨1313, by rfl⟩ (by norm_num))
theorem R28025 : Reach 28025 := rs (se 2 (by rfl) ⟨10509, by rfl⟩) (B 21019 (by norm_num) ⟨10509, by rfl⟩ (by norm_num))
theorem R28029 : Reach 28029 := rs (se 3 (by rfl) ⟨5255, by rfl⟩) (B 10511 (by norm_num) ⟨5255, by rfl⟩ (by norm_num))
theorem R28033 : Reach 28033 := rs (se 2 (by rfl) ⟨10512, by rfl⟩) (B 21025 (by norm_num) ⟨10512, by rfl⟩ (by norm_num))
theorem R28037 : Reach 28037 := rs (se 4 (by rfl) ⟨2628, by rfl⟩) (B 5257 (by norm_num) ⟨2628, by rfl⟩ (by norm_num))
theorem R28041 : Reach 28041 := rs (se 2 (by rfl) ⟨10515, by rfl⟩) (B 21031 (by norm_num) ⟨10515, by rfl⟩ (by norm_num))
theorem R28045 : Reach 28045 := rs (se 3 (by rfl) ⟨5258, by rfl⟩) (B 10517 (by norm_num) ⟨5258, by rfl⟩ (by norm_num))
theorem R28049 : Reach 28049 := rs (se 2 (by rfl) ⟨10518, by rfl⟩) (B 21037 (by norm_num) ⟨10518, by rfl⟩ (by norm_num))
theorem R28053 : Reach 28053 := rs (se 6 (by rfl) ⟨657, by rfl⟩) (B 1315 (by norm_num) ⟨657, by rfl⟩ (by norm_num))
theorem R60821 : Reach 60821 := rs (se 6 (by rfl) ⟨1425, by rfl⟩) (B 2851 (by norm_num) ⟨1425, by rfl⟩ (by norm_num))
theorem R28057 : Reach 28057 := rs (se 2 (by rfl) ⟨10521, by rfl⟩) (B 21043 (by norm_num) ⟨10521, by rfl⟩ (by norm_num))
theorem R28061 : Reach 28061 := rs (se 3 (by rfl) ⟨5261, by rfl⟩) (B 10523 (by norm_num) ⟨5261, by rfl⟩ (by norm_num))
theorem R28065 : Reach 28065 := rs (se 2 (by rfl) ⟨10524, by rfl⟩) (B 21049 (by norm_num) ⟨10524, by rfl⟩ (by norm_num))
theorem R28069 : Reach 28069 := rs (se 4 (by rfl) ⟨2631, by rfl⟩) (B 5263 (by norm_num) ⟨2631, by rfl⟩ (by norm_num))
theorem R28073 : Reach 28073 := rs (se 2 (by rfl) ⟨10527, by rfl⟩) (B 21055 (by norm_num) ⟨10527, by rfl⟩ (by norm_num))
theorem R28077 : Reach 28077 := rs (se 3 (by rfl) ⟨5264, by rfl⟩) (B 10529 (by norm_num) ⟨5264, by rfl⟩ (by norm_num))
theorem R28081 : Reach 28081 := rs (se 2 (by rfl) ⟨10530, by rfl⟩) (B 21061 (by norm_num) ⟨10530, by rfl⟩ (by norm_num))
theorem R28085 : Reach 28085 := rs (se 5 (by rfl) ⟨1316, by rfl⟩) (B 2633 (by norm_num) ⟨1316, by rfl⟩ (by norm_num))
theorem R28089 : Reach 28089 := rs (se 2 (by rfl) ⟨10533, by rfl⟩) (B 21067 (by norm_num) ⟨10533, by rfl⟩ (by norm_num))
theorem R28093 : Reach 28093 := rs (se 3 (by rfl) ⟨5267, by rfl⟩) (B 10535 (by norm_num) ⟨5267, by rfl⟩ (by norm_num))
theorem R28097 : Reach 28097 := rs (se 2 (by rfl) ⟨10536, by rfl⟩) (B 21073 (by norm_num) ⟨10536, by rfl⟩ (by norm_num))
theorem R28101 : Reach 28101 := rs (se 4 (by rfl) ⟨2634, by rfl⟩) (B 5269 (by norm_num) ⟨2634, by rfl⟩ (by norm_num))
theorem R60869 : Reach 60869 := rs (se 4 (by rfl) ⟨5706, by rfl⟩) (B 11413 (by norm_num) ⟨5706, by rfl⟩ (by norm_num))
theorem R28105 : Reach 28105 := rs (se 2 (by rfl) ⟨10539, by rfl⟩) (B 21079 (by norm_num) ⟨10539, by rfl⟩ (by norm_num))
theorem R28109 : Reach 28109 := rs (se 3 (by rfl) ⟨5270, by rfl⟩) (B 10541 (by norm_num) ⟨5270, by rfl⟩ (by norm_num))
theorem R28113 : Reach 28113 := rs (se 2 (by rfl) ⟨10542, by rfl⟩) (B 21085 (by norm_num) ⟨10542, by rfl⟩ (by norm_num))
theorem R28117 : Reach 28117 := rs (se 7 (by rfl) ⟨329, by rfl⟩) (B 659 (by norm_num) ⟨329, by rfl⟩ (by norm_num))
theorem R28121 : Reach 28121 := rs (se 2 (by rfl) ⟨10545, by rfl⟩) (B 21091 (by norm_num) ⟨10545, by rfl⟩ (by norm_num))
theorem R28125 : Reach 28125 := rs (se 3 (by rfl) ⟨5273, by rfl⟩) (B 10547 (by norm_num) ⟨5273, by rfl⟩ (by norm_num))
theorem R28129 : Reach 28129 := rs (se 2 (by rfl) ⟨10548, by rfl⟩) (B 21097 (by norm_num) ⟨10548, by rfl⟩ (by norm_num))
theorem R28133 : Reach 28133 := rs (se 4 (by rfl) ⟨2637, by rfl⟩) (B 5275 (by norm_num) ⟨2637, by rfl⟩ (by norm_num))
theorem R28137 : Reach 28137 := rs (se 2 (by rfl) ⟨10551, by rfl⟩) (B 21103 (by norm_num) ⟨10551, by rfl⟩ (by norm_num))
theorem R28141 : Reach 28141 := rs (se 3 (by rfl) ⟨5276, by rfl⟩) (B 10553 (by norm_num) ⟨5276, by rfl⟩ (by norm_num))
theorem R28145 : Reach 28145 := rs (se 2 (by rfl) ⟨10554, by rfl⟩) (B 21109 (by norm_num) ⟨10554, by rfl⟩ (by norm_num))
theorem R28149 : Reach 28149 := rs (se 5 (by rfl) ⟨1319, by rfl⟩) (B 2639 (by norm_num) ⟨1319, by rfl⟩ (by norm_num))
theorem R28153 : Reach 28153 := rs (se 2 (by rfl) ⟨10557, by rfl⟩) (B 21115 (by norm_num) ⟨10557, by rfl⟩ (by norm_num))
theorem R28157 : Reach 28157 := rs (se 3 (by rfl) ⟨5279, by rfl⟩) (B 10559 (by norm_num) ⟨5279, by rfl⟩ (by norm_num))
theorem R28161 : Reach 28161 := rs (se 2 (by rfl) ⟨10560, by rfl⟩) (B 21121 (by norm_num) ⟨10560, by rfl⟩ (by norm_num))
theorem R28165 : Reach 28165 := rs (se 4 (by rfl) ⟨2640, by rfl⟩) (B 5281 (by norm_num) ⟨2640, by rfl⟩ (by norm_num))
theorem R28169 : Reach 28169 := rs (se 2 (by rfl) ⟨10563, by rfl⟩) (B 21127 (by norm_num) ⟨10563, by rfl⟩ (by norm_num))
theorem R28173 : Reach 28173 := rs (se 3 (by rfl) ⟨5282, by rfl⟩) (B 10565 (by norm_num) ⟨5282, by rfl⟩ (by norm_num))
theorem R28177 : Reach 28177 := rs (se 2 (by rfl) ⟨10566, by rfl⟩) (B 21133 (by norm_num) ⟨10566, by rfl⟩ (by norm_num))
theorem R28181 : Reach 28181 := rs (se 6 (by rfl) ⟨660, by rfl⟩) (B 1321 (by norm_num) ⟨660, by rfl⟩ (by norm_num))
theorem R28185 : Reach 28185 := rs (se 2 (by rfl) ⟨10569, by rfl⟩) (B 21139 (by norm_num) ⟨10569, by rfl⟩ (by norm_num))
theorem R28189 : Reach 28189 := rs (se 3 (by rfl) ⟨5285, by rfl⟩) (B 10571 (by norm_num) ⟨5285, by rfl⟩ (by norm_num))
theorem R28193 : Reach 28193 := rs (se 2 (by rfl) ⟨10572, by rfl⟩) (B 21145 (by norm_num) ⟨10572, by rfl⟩ (by norm_num))
theorem R28197 : Reach 28197 := rs (se 4 (by rfl) ⟨2643, by rfl⟩) (B 5287 (by norm_num) ⟨2643, by rfl⟩ (by norm_num))
theorem R28201 : Reach 28201 := rs (se 2 (by rfl) ⟨10575, by rfl⟩) (B 21151 (by norm_num) ⟨10575, by rfl⟩ (by norm_num))
theorem R28205 : Reach 28205 := rs (se 3 (by rfl) ⟨5288, by rfl⟩) (B 10577 (by norm_num) ⟨5288, by rfl⟩ (by norm_num))
theorem R28209 : Reach 28209 := rs (se 2 (by rfl) ⟨10578, by rfl⟩) (B 21157 (by norm_num) ⟨10578, by rfl⟩ (by norm_num))
theorem R28213 : Reach 28213 := rs (se 5 (by rfl) ⟨1322, by rfl⟩) (B 2645 (by norm_num) ⟨1322, by rfl⟩ (by norm_num))
theorem R28217 : Reach 28217 := rs (se 2 (by rfl) ⟨10581, by rfl⟩) (B 21163 (by norm_num) ⟨10581, by rfl⟩ (by norm_num))
theorem R28221 : Reach 28221 := rs (se 3 (by rfl) ⟨5291, by rfl⟩) (B 10583 (by norm_num) ⟨5291, by rfl⟩ (by norm_num))
theorem R28225 : Reach 28225 := rs (se 2 (by rfl) ⟨10584, by rfl⟩) (B 21169 (by norm_num) ⟨10584, by rfl⟩ (by norm_num))
theorem R28229 : Reach 28229 := rs (se 4 (by rfl) ⟨2646, by rfl⟩) (B 5293 (by norm_num) ⟨2646, by rfl⟩ (by norm_num))
theorem R28233 : Reach 28233 := rs (se 2 (by rfl) ⟨10587, by rfl⟩) (B 21175 (by norm_num) ⟨10587, by rfl⟩ (by norm_num))
theorem R28237 : Reach 28237 := rs (se 3 (by rfl) ⟨5294, by rfl⟩) (B 10589 (by norm_num) ⟨5294, by rfl⟩ (by norm_num))
theorem R28241 : Reach 28241 := rs (se 2 (by rfl) ⟨10590, by rfl⟩) (B 21181 (by norm_num) ⟨10590, by rfl⟩ (by norm_num))
theorem R28245 : Reach 28245 := rs (se 8 (by rfl) ⟨165, by rfl⟩) (B 331 (by norm_num) ⟨165, by rfl⟩ (by norm_num))
theorem R28249 : Reach 28249 := rs (se 2 (by rfl) ⟨10593, by rfl⟩) (B 21187 (by norm_num) ⟨10593, by rfl⟩ (by norm_num))
theorem R28253 : Reach 28253 := rs (se 3 (by rfl) ⟨5297, by rfl⟩) (B 10595 (by norm_num) ⟨5297, by rfl⟩ (by norm_num))
theorem R28257 : Reach 28257 := rs (se 2 (by rfl) ⟨10596, by rfl⟩) (B 21193 (by norm_num) ⟨10596, by rfl⟩ (by norm_num))
theorem R93797 : Reach 93797 := rs (se 4 (by rfl) ⟨8793, by rfl⟩) (B 17587 (by norm_num) ⟨8793, by rfl⟩ (by norm_num))
theorem R28261 : Reach 28261 := rs (se 4 (by rfl) ⟨2649, by rfl⟩) (B 5299 (by norm_num) ⟨2649, by rfl⟩ (by norm_num))
theorem R28265 : Reach 28265 := rs (se 2 (by rfl) ⟨10599, by rfl⟩) (B 21199 (by norm_num) ⟨10599, by rfl⟩ (by norm_num))
theorem R61037 : Reach 61037 := rs (se 3 (by rfl) ⟨11444, by rfl⟩) (B 22889 (by norm_num) ⟨11444, by rfl⟩ (by norm_num))
theorem R28269 : Reach 28269 := rs (se 3 (by rfl) ⟨5300, by rfl⟩) (B 10601 (by norm_num) ⟨5300, by rfl⟩ (by norm_num))
theorem R28273 : Reach 28273 := rs (se 2 (by rfl) ⟨10602, by rfl⟩) (B 21205 (by norm_num) ⟨10602, by rfl⟩ (by norm_num))
theorem R28277 : Reach 28277 := rs (se 5 (by rfl) ⟨1325, by rfl⟩) (B 2651 (by norm_num) ⟨1325, by rfl⟩ (by norm_num))
theorem R28281 : Reach 28281 := rs (se 2 (by rfl) ⟨10605, by rfl⟩) (B 21211 (by norm_num) ⟨10605, by rfl⟩ (by norm_num))
theorem R28285 : Reach 28285 := rs (se 3 (by rfl) ⟨5303, by rfl⟩) (B 10607 (by norm_num) ⟨5303, by rfl⟩ (by norm_num))
theorem R28289 : Reach 28289 := rs (se 2 (by rfl) ⟨10608, by rfl⟩) (B 21217 (by norm_num) ⟨10608, by rfl⟩ (by norm_num))
theorem R28293 : Reach 28293 := rs (se 4 (by rfl) ⟨2652, by rfl⟩) (B 5305 (by norm_num) ⟨2652, by rfl⟩ (by norm_num))
theorem R28297 : Reach 28297 := rs (se 2 (by rfl) ⟨10611, by rfl⟩) (B 21223 (by norm_num) ⟨10611, by rfl⟩ (by norm_num))
theorem R28301 : Reach 28301 := rs (se 3 (by rfl) ⟨5306, by rfl⟩) (B 10613 (by norm_num) ⟨5306, by rfl⟩ (by norm_num))
theorem R28305 : Reach 28305 := rs (se 2 (by rfl) ⟨10614, by rfl⟩) (B 21229 (by norm_num) ⟨10614, by rfl⟩ (by norm_num))
theorem R28309 : Reach 28309 := rs (se 6 (by rfl) ⟨663, by rfl⟩) (B 1327 (by norm_num) ⟨663, by rfl⟩ (by norm_num))
theorem R28313 : Reach 28313 := rs (se 2 (by rfl) ⟨10617, by rfl⟩) (B 21235 (by norm_num) ⟨10617, by rfl⟩ (by norm_num))
theorem R28317 : Reach 28317 := rs (se 3 (by rfl) ⟨5309, by rfl⟩) (B 10619 (by norm_num) ⟨5309, by rfl⟩ (by norm_num))
theorem R28321 : Reach 28321 := rs (se 2 (by rfl) ⟨10620, by rfl⟩) (B 21241 (by norm_num) ⟨10620, by rfl⟩ (by norm_num))
theorem R28325 : Reach 28325 := rs (se 4 (by rfl) ⟨2655, by rfl⟩) (B 5311 (by norm_num) ⟨2655, by rfl⟩ (by norm_num))
theorem R28329 : Reach 28329 := rs (se 2 (by rfl) ⟨10623, by rfl⟩) (B 21247 (by norm_num) ⟨10623, by rfl⟩ (by norm_num))
theorem R28333 : Reach 28333 := rs (se 3 (by rfl) ⟨5312, by rfl⟩) (B 10625 (by norm_num) ⟨5312, by rfl⟩ (by norm_num))
theorem R28337 : Reach 28337 := rs (se 2 (by rfl) ⟨10626, by rfl⟩) (B 21253 (by norm_num) ⟨10626, by rfl⟩ (by norm_num))
theorem R61109 : Reach 61109 := rs (se 5 (by rfl) ⟨2864, by rfl⟩) (B 5729 (by norm_num) ⟨2864, by rfl⟩ (by norm_num))
theorem R28341 : Reach 28341 := rs (se 5 (by rfl) ⟨1328, by rfl⟩) (B 2657 (by norm_num) ⟨1328, by rfl⟩ (by norm_num))
theorem R28345 : Reach 28345 := rs (se 2 (by rfl) ⟨10629, by rfl⟩) (B 21259 (by norm_num) ⟨10629, by rfl⟩ (by norm_num))
theorem R28349 : Reach 28349 := rs (se 3 (by rfl) ⟨5315, by rfl⟩) (B 10631 (by norm_num) ⟨5315, by rfl⟩ (by norm_num))
theorem R28353 : Reach 28353 := rs (se 2 (by rfl) ⟨10632, by rfl⟩) (B 21265 (by norm_num) ⟨10632, by rfl⟩ (by norm_num))
theorem R28357 : Reach 28357 := rs (se 4 (by rfl) ⟨2658, by rfl⟩) (B 5317 (by norm_num) ⟨2658, by rfl⟩ (by norm_num))
theorem R28361 : Reach 28361 := rs (se 2 (by rfl) ⟨10635, by rfl⟩) (B 21271 (by norm_num) ⟨10635, by rfl⟩ (by norm_num))
theorem R28365 : Reach 28365 := rs (se 3 (by rfl) ⟨5318, by rfl⟩) (B 10637 (by norm_num) ⟨5318, by rfl⟩ (by norm_num))
theorem R28369 : Reach 28369 := rs (se 2 (by rfl) ⟨10638, by rfl⟩) (B 21277 (by norm_num) ⟨10638, by rfl⟩ (by norm_num))
theorem R28373 : Reach 28373 := rs (se 7 (by rfl) ⟨332, by rfl⟩) (B 665 (by norm_num) ⟨332, by rfl⟩ (by norm_num))
theorem R28377 : Reach 28377 := rs (se 2 (by rfl) ⟨10641, by rfl⟩) (B 21283 (by norm_num) ⟨10641, by rfl⟩ (by norm_num))
theorem R28381 : Reach 28381 := rs (se 3 (by rfl) ⟨5321, by rfl⟩) (B 10643 (by norm_num) ⟨5321, by rfl⟩ (by norm_num))
theorem R28385 : Reach 28385 := rs (se 2 (by rfl) ⟨10644, by rfl⟩) (B 21289 (by norm_num) ⟨10644, by rfl⟩ (by norm_num))
theorem R28389 : Reach 28389 := rs (se 4 (by rfl) ⟨2661, by rfl⟩) (B 5323 (by norm_num) ⟨2661, by rfl⟩ (by norm_num))
theorem R28393 : Reach 28393 := rs (se 2 (by rfl) ⟨10647, by rfl⟩) (B 21295 (by norm_num) ⟨10647, by rfl⟩ (by norm_num))
theorem R28397 : Reach 28397 := rs (se 3 (by rfl) ⟨5324, by rfl⟩) (B 10649 (by norm_num) ⟨5324, by rfl⟩ (by norm_num))
theorem R28401 : Reach 28401 := rs (se 2 (by rfl) ⟨10650, by rfl⟩) (B 21301 (by norm_num) ⟨10650, by rfl⟩ (by norm_num))
theorem R28405 : Reach 28405 := rs (se 5 (by rfl) ⟨1331, by rfl⟩) (B 2663 (by norm_num) ⟨1331, by rfl⟩ (by norm_num))
theorem R28409 : Reach 28409 := rs (se 2 (by rfl) ⟨10653, by rfl⟩) (B 21307 (by norm_num) ⟨10653, by rfl⟩ (by norm_num))
theorem R61181 : Reach 61181 := rs (se 3 (by rfl) ⟨11471, by rfl⟩) (B 22943 (by norm_num) ⟨11471, by rfl⟩ (by norm_num))
theorem R28413 : Reach 28413 := rs (se 3 (by rfl) ⟨5327, by rfl⟩) (B 10655 (by norm_num) ⟨5327, by rfl⟩ (by norm_num))
theorem R28417 : Reach 28417 := rs (se 2 (by rfl) ⟨10656, by rfl⟩) (B 21313 (by norm_num) ⟨10656, by rfl⟩ (by norm_num))
theorem R28421 : Reach 28421 := rs (se 4 (by rfl) ⟨2664, by rfl⟩) (B 5329 (by norm_num) ⟨2664, by rfl⟩ (by norm_num))
theorem R28425 : Reach 28425 := rs (se 2 (by rfl) ⟨10659, by rfl⟩) (B 21319 (by norm_num) ⟨10659, by rfl⟩ (by norm_num))
theorem R28429 : Reach 28429 := rs (se 3 (by rfl) ⟨5330, by rfl⟩) (B 10661 (by norm_num) ⟨5330, by rfl⟩ (by norm_num))
theorem R28433 : Reach 28433 := rs (se 2 (by rfl) ⟨10662, by rfl⟩) (B 21325 (by norm_num) ⟨10662, by rfl⟩ (by norm_num))
theorem R28437 : Reach 28437 := rs (se 6 (by rfl) ⟨666, by rfl⟩) (B 1333 (by norm_num) ⟨666, by rfl⟩ (by norm_num))
theorem R28441 : Reach 28441 := rs (se 2 (by rfl) ⟨10665, by rfl⟩) (B 21331 (by norm_num) ⟨10665, by rfl⟩ (by norm_num))
theorem R28445 : Reach 28445 := rs (se 3 (by rfl) ⟨5333, by rfl⟩) (B 10667 (by norm_num) ⟨5333, by rfl⟩ (by norm_num))
theorem R28449 : Reach 28449 := rs (se 2 (by rfl) ⟨10668, by rfl⟩) (B 21337 (by norm_num) ⟨10668, by rfl⟩ (by norm_num))
theorem R28453 : Reach 28453 := rs (se 4 (by rfl) ⟨2667, by rfl⟩) (B 5335 (by norm_num) ⟨2667, by rfl⟩ (by norm_num))
theorem R28457 : Reach 28457 := rs (se 2 (by rfl) ⟨10671, by rfl⟩) (B 21343 (by norm_num) ⟨10671, by rfl⟩ (by norm_num))
theorem R28461 : Reach 28461 := rs (se 3 (by rfl) ⟨5336, by rfl⟩) (B 10673 (by norm_num) ⟨5336, by rfl⟩ (by norm_num))
theorem R61229 : Reach 61229 := rs (se 3 (by rfl) ⟨11480, by rfl⟩) (B 22961 (by norm_num) ⟨11480, by rfl⟩ (by norm_num))
theorem R28465 : Reach 28465 := rs (se 2 (by rfl) ⟨10674, by rfl⟩) (B 21349 (by norm_num) ⟨10674, by rfl⟩ (by norm_num))
theorem R28469 : Reach 28469 := rs (se 5 (by rfl) ⟨1334, by rfl⟩) (B 2669 (by norm_num) ⟨1334, by rfl⟩ (by norm_num))
theorem R28473 : Reach 28473 := rs (se 2 (by rfl) ⟨10677, by rfl⟩) (B 21355 (by norm_num) ⟨10677, by rfl⟩ (by norm_num))
theorem R28477 : Reach 28477 := rs (se 3 (by rfl) ⟨5339, by rfl⟩) (B 10679 (by norm_num) ⟨5339, by rfl⟩ (by norm_num))
theorem R28481 : Reach 28481 := rs (se 2 (by rfl) ⟨10680, by rfl⟩) (B 21361 (by norm_num) ⟨10680, by rfl⟩ (by norm_num))
theorem R61253 : Reach 61253 := rs (se 4 (by rfl) ⟨5742, by rfl⟩) (B 11485 (by norm_num) ⟨5742, by rfl⟩ (by norm_num))
theorem R28485 : Reach 28485 := rs (se 4 (by rfl) ⟨2670, by rfl⟩) (B 5341 (by norm_num) ⟨2670, by rfl⟩ (by norm_num))
theorem R28489 : Reach 28489 := rs (se 2 (by rfl) ⟨10683, by rfl⟩) (B 21367 (by norm_num) ⟨10683, by rfl⟩ (by norm_num))
theorem R28493 : Reach 28493 := rs (se 3 (by rfl) ⟨5342, by rfl⟩) (B 10685 (by norm_num) ⟨5342, by rfl⟩ (by norm_num))
theorem R28497 : Reach 28497 := rs (se 2 (by rfl) ⟨10686, by rfl⟩) (B 21373 (by norm_num) ⟨10686, by rfl⟩ (by norm_num))
theorem R28501 : Reach 28501 := rs (se 9 (by rfl) ⟨83, by rfl⟩) (B 167 (by norm_num) ⟨83, by rfl⟩ (by norm_num))
theorem R28505 : Reach 28505 := rs (se 2 (by rfl) ⟨10689, by rfl⟩) (B 21379 (by norm_num) ⟨10689, by rfl⟩ (by norm_num))
theorem R28509 : Reach 28509 := rs (se 3 (by rfl) ⟨5345, by rfl⟩) (B 10691 (by norm_num) ⟨5345, by rfl⟩ (by norm_num))
theorem R28513 : Reach 28513 := rs (se 2 (by rfl) ⟨10692, by rfl⟩) (B 21385 (by norm_num) ⟨10692, by rfl⟩ (by norm_num))
theorem R28517 : Reach 28517 := rs (se 4 (by rfl) ⟨2673, by rfl⟩) (B 5347 (by norm_num) ⟨2673, by rfl⟩ (by norm_num))
theorem R28521 : Reach 28521 := rs (se 2 (by rfl) ⟨10695, by rfl⟩) (B 21391 (by norm_num) ⟨10695, by rfl⟩ (by norm_num))
theorem R28525 : Reach 28525 := rs (se 3 (by rfl) ⟨5348, by rfl⟩) (B 10697 (by norm_num) ⟨5348, by rfl⟩ (by norm_num))
theorem R28529 : Reach 28529 := rs (se 2 (by rfl) ⟨10698, by rfl⟩) (B 21397 (by norm_num) ⟨10698, by rfl⟩ (by norm_num))
theorem R28533 : Reach 28533 := rs (se 5 (by rfl) ⟨1337, by rfl⟩) (B 2675 (by norm_num) ⟨1337, by rfl⟩ (by norm_num))
theorem R28537 : Reach 28537 := rs (se 2 (by rfl) ⟨10701, by rfl⟩) (B 21403 (by norm_num) ⟨10701, by rfl⟩ (by norm_num))
theorem R28541 : Reach 28541 := rs (se 3 (by rfl) ⟨5351, by rfl⟩) (B 10703 (by norm_num) ⟨5351, by rfl⟩ (by norm_num))
theorem R28545 : Reach 28545 := rs (se 2 (by rfl) ⟨10704, by rfl⟩) (B 21409 (by norm_num) ⟨10704, by rfl⟩ (by norm_num))
theorem R28549 : Reach 28549 := rs (se 4 (by rfl) ⟨2676, by rfl⟩) (B 5353 (by norm_num) ⟨2676, by rfl⟩ (by norm_num))
theorem R28553 : Reach 28553 := rs (se 2 (by rfl) ⟨10707, by rfl⟩) (B 21415 (by norm_num) ⟨10707, by rfl⟩ (by norm_num))
theorem R61325 : Reach 61325 := rs (se 3 (by rfl) ⟨11498, by rfl⟩) (B 22997 (by norm_num) ⟨11498, by rfl⟩ (by norm_num))
theorem R28557 : Reach 28557 := rs (se 3 (by rfl) ⟨5354, by rfl⟩) (B 10709 (by norm_num) ⟨5354, by rfl⟩ (by norm_num))
theorem R28561 : Reach 28561 := rs (se 2 (by rfl) ⟨10710, by rfl⟩) (B 21421 (by norm_num) ⟨10710, by rfl⟩ (by norm_num))
theorem R28565 : Reach 28565 := rs (se 6 (by rfl) ⟨669, by rfl⟩) (B 1339 (by norm_num) ⟨669, by rfl⟩ (by norm_num))
theorem R28569 : Reach 28569 := rs (se 2 (by rfl) ⟨10713, by rfl⟩) (B 21427 (by norm_num) ⟨10713, by rfl⟩ (by norm_num))
theorem R28573 : Reach 28573 := rs (se 3 (by rfl) ⟨5357, by rfl⟩) (B 10715 (by norm_num) ⟨5357, by rfl⟩ (by norm_num))
theorem R28577 : Reach 28577 := rs (se 2 (by rfl) ⟨10716, by rfl⟩) (B 21433 (by norm_num) ⟨10716, by rfl⟩ (by norm_num))
theorem R28581 : Reach 28581 := rs (se 4 (by rfl) ⟨2679, by rfl⟩) (B 5359 (by norm_num) ⟨2679, by rfl⟩ (by norm_num))
theorem R28585 : Reach 28585 := rs (se 2 (by rfl) ⟨10719, by rfl⟩) (B 21439 (by norm_num) ⟨10719, by rfl⟩ (by norm_num))
theorem R28589 : Reach 28589 := rs (se 3 (by rfl) ⟨5360, by rfl⟩) (B 10721 (by norm_num) ⟨5360, by rfl⟩ (by norm_num))
theorem R28593 : Reach 28593 := rs (se 2 (by rfl) ⟨10722, by rfl⟩) (B 21445 (by norm_num) ⟨10722, by rfl⟩ (by norm_num))
theorem R28597 : Reach 28597 := rs (se 5 (by rfl) ⟨1340, by rfl⟩) (B 2681 (by norm_num) ⟨1340, by rfl⟩ (by norm_num))
theorem R28601 : Reach 28601 := rs (se 2 (by rfl) ⟨10725, by rfl⟩) (B 21451 (by norm_num) ⟨10725, by rfl⟩ (by norm_num))
theorem R28605 : Reach 28605 := rs (se 3 (by rfl) ⟨5363, by rfl⟩) (B 10727 (by norm_num) ⟨5363, by rfl⟩ (by norm_num))
theorem R61373 : Reach 61373 := rs (se 3 (by rfl) ⟨11507, by rfl⟩) (B 23015 (by norm_num) ⟨11507, by rfl⟩ (by norm_num))
theorem R28609 : Reach 28609 := rs (se 2 (by rfl) ⟨10728, by rfl⟩) (B 21457 (by norm_num) ⟨10728, by rfl⟩ (by norm_num))
theorem R28613 : Reach 28613 := rs (se 4 (by rfl) ⟨2682, by rfl⟩) (B 5365 (by norm_num) ⟨2682, by rfl⟩ (by norm_num))
theorem R28617 : Reach 28617 := rs (se 2 (by rfl) ⟨10731, by rfl⟩) (B 21463 (by norm_num) ⟨10731, by rfl⟩ (by norm_num))
theorem R28621 : Reach 28621 := rs (se 3 (by rfl) ⟨5366, by rfl⟩) (B 10733 (by norm_num) ⟨5366, by rfl⟩ (by norm_num))
theorem R28625 : Reach 28625 := rs (se 2 (by rfl) ⟨10734, by rfl⟩) (B 21469 (by norm_num) ⟨10734, by rfl⟩ (by norm_num))
theorem R61397 : Reach 61397 := rs (se 7 (by rfl) ⟨719, by rfl⟩) (B 1439 (by norm_num) ⟨719, by rfl⟩ (by norm_num))
theorem R28629 : Reach 28629 := rs (se 7 (by rfl) ⟨335, by rfl⟩) (B 671 (by norm_num) ⟨335, by rfl⟩ (by norm_num))
theorem R28633 : Reach 28633 := rs (se 2 (by rfl) ⟨10737, by rfl⟩) (B 21475 (by norm_num) ⟨10737, by rfl⟩ (by norm_num))
theorem R28637 : Reach 28637 := rs (se 3 (by rfl) ⟨5369, by rfl⟩) (B 10739 (by norm_num) ⟨5369, by rfl⟩ (by norm_num))
theorem R28641 : Reach 28641 := rs (se 2 (by rfl) ⟨10740, by rfl⟩) (B 21481 (by norm_num) ⟨10740, by rfl⟩ (by norm_num))
theorem R28645 : Reach 28645 := rs (se 4 (by rfl) ⟨2685, by rfl⟩) (B 5371 (by norm_num) ⟨2685, by rfl⟩ (by norm_num))
theorem R28649 : Reach 28649 := rs (se 2 (by rfl) ⟨10743, by rfl⟩) (B 21487 (by norm_num) ⟨10743, by rfl⟩ (by norm_num))
theorem R28653 : Reach 28653 := rs (se 3 (by rfl) ⟨5372, by rfl⟩) (B 10745 (by norm_num) ⟨5372, by rfl⟩ (by norm_num))
theorem R28657 : Reach 28657 := rs (se 2 (by rfl) ⟨10746, by rfl⟩) (B 21493 (by norm_num) ⟨10746, by rfl⟩ (by norm_num))
theorem R28661 : Reach 28661 := rs (se 5 (by rfl) ⟨1343, by rfl⟩) (B 2687 (by norm_num) ⟨1343, by rfl⟩ (by norm_num))
theorem R28665 : Reach 28665 := rs (se 2 (by rfl) ⟨10749, by rfl⟩) (B 21499 (by norm_num) ⟨10749, by rfl⟩ (by norm_num))
theorem R28669 : Reach 28669 := rs (se 3 (by rfl) ⟨5375, by rfl⟩) (B 10751 (by norm_num) ⟨5375, by rfl⟩ (by norm_num))
theorem R28673 : Reach 28673 := rs (se 2 (by rfl) ⟨10752, by rfl⟩) (B 21505 (by norm_num) ⟨10752, by rfl⟩ (by norm_num))
theorem R28677 : Reach 28677 := rs (se 4 (by rfl) ⟨2688, by rfl⟩) (B 5377 (by norm_num) ⟨2688, by rfl⟩ (by norm_num))
theorem R28681 : Reach 28681 := rs (se 2 (by rfl) ⟨10755, by rfl⟩) (B 21511 (by norm_num) ⟨10755, by rfl⟩ (by norm_num))
theorem R28685 : Reach 28685 := rs (se 3 (by rfl) ⟨5378, by rfl⟩) (B 10757 (by norm_num) ⟨5378, by rfl⟩ (by norm_num))
theorem R28689 : Reach 28689 := rs (se 2 (by rfl) ⟨10758, by rfl⟩) (B 21517 (by norm_num) ⟨10758, by rfl⟩ (by norm_num))
theorem R94229 : Reach 94229 := rs (se 6 (by rfl) ⟨2208, by rfl⟩) (B 4417 (by norm_num) ⟨2208, by rfl⟩ (by norm_num))
theorem R28693 : Reach 28693 := rs (se 6 (by rfl) ⟨672, by rfl⟩) (B 1345 (by norm_num) ⟨672, by rfl⟩ (by norm_num))
theorem R28697 : Reach 28697 := rs (se 2 (by rfl) ⟨10761, by rfl⟩) (B 21523 (by norm_num) ⟨10761, by rfl⟩ (by norm_num))
theorem R61469 : Reach 61469 := rs (se 3 (by rfl) ⟨11525, by rfl⟩) (B 23051 (by norm_num) ⟨11525, by rfl⟩ (by norm_num))
theorem R28701 : Reach 28701 := rs (se 3 (by rfl) ⟨5381, by rfl⟩) (B 10763 (by norm_num) ⟨5381, by rfl⟩ (by norm_num))
theorem R28705 : Reach 28705 := rs (se 2 (by rfl) ⟨10764, by rfl⟩) (B 21529 (by norm_num) ⟨10764, by rfl⟩ (by norm_num))
theorem R28709 : Reach 28709 := rs (se 4 (by rfl) ⟨2691, by rfl⟩) (B 5383 (by norm_num) ⟨2691, by rfl⟩ (by norm_num))
theorem R28713 : Reach 28713 := rs (se 2 (by rfl) ⟨10767, by rfl⟩) (B 21535 (by norm_num) ⟨10767, by rfl⟩ (by norm_num))
theorem R28717 : Reach 28717 := rs (se 3 (by rfl) ⟨5384, by rfl⟩) (B 10769 (by norm_num) ⟨5384, by rfl⟩ (by norm_num))
theorem R28721 : Reach 28721 := rs (se 2 (by rfl) ⟨10770, by rfl⟩) (B 21541 (by norm_num) ⟨10770, by rfl⟩ (by norm_num))
theorem R28725 : Reach 28725 := rs (se 5 (by rfl) ⟨1346, by rfl⟩) (B 2693 (by norm_num) ⟨1346, by rfl⟩ (by norm_num))
theorem R28729 : Reach 28729 := rs (se 2 (by rfl) ⟨10773, by rfl⟩) (B 21547 (by norm_num) ⟨10773, by rfl⟩ (by norm_num))
theorem R28733 : Reach 28733 := rs (se 3 (by rfl) ⟨5387, by rfl⟩) (B 10775 (by norm_num) ⟨5387, by rfl⟩ (by norm_num))
theorem R28737 : Reach 28737 := rs (se 2 (by rfl) ⟨10776, by rfl⟩) (B 21553 (by norm_num) ⟨10776, by rfl⟩ (by norm_num))
theorem R28741 : Reach 28741 := rs (se 4 (by rfl) ⟨2694, by rfl⟩) (B 5389 (by norm_num) ⟨2694, by rfl⟩ (by norm_num))
theorem R28745 : Reach 28745 := rs (se 2 (by rfl) ⟨10779, by rfl⟩) (B 21559 (by norm_num) ⟨10779, by rfl⟩ (by norm_num))
theorem R28749 : Reach 28749 := rs (se 3 (by rfl) ⟨5390, by rfl⟩) (B 10781 (by norm_num) ⟨5390, by rfl⟩ (by norm_num))
theorem R28753 : Reach 28753 := rs (se 2 (by rfl) ⟨10782, by rfl⟩) (B 21565 (by norm_num) ⟨10782, by rfl⟩ (by norm_num))
theorem R28757 : Reach 28757 := rs (se 8 (by rfl) ⟨168, by rfl⟩) (B 337 (by norm_num) ⟨168, by rfl⟩ (by norm_num))
theorem R28761 : Reach 28761 := rs (se 2 (by rfl) ⟨10785, by rfl⟩) (B 21571 (by norm_num) ⟨10785, by rfl⟩ (by norm_num))
theorem R28765 : Reach 28765 := rs (se 3 (by rfl) ⟨5393, by rfl⟩) (B 10787 (by norm_num) ⟨5393, by rfl⟩ (by norm_num))
theorem R28769 : Reach 28769 := rs (se 2 (by rfl) ⟨10788, by rfl⟩) (B 21577 (by norm_num) ⟨10788, by rfl⟩ (by norm_num))
theorem R61541 : Reach 61541 := rs (se 4 (by rfl) ⟨5769, by rfl⟩) (B 11539 (by norm_num) ⟨5769, by rfl⟩ (by norm_num))
theorem R28773 : Reach 28773 := rs (se 4 (by rfl) ⟨2697, by rfl⟩) (B 5395 (by norm_num) ⟨2697, by rfl⟩ (by norm_num))
theorem R28777 : Reach 28777 := rs (se 2 (by rfl) ⟨10791, by rfl⟩) (B 21583 (by norm_num) ⟨10791, by rfl⟩ (by norm_num))
theorem R28781 : Reach 28781 := rs (se 3 (by rfl) ⟨5396, by rfl⟩) (B 10793 (by norm_num) ⟨5396, by rfl⟩ (by norm_num))
theorem R28785 : Reach 28785 := rs (se 2 (by rfl) ⟨10794, by rfl⟩) (B 21589 (by norm_num) ⟨10794, by rfl⟩ (by norm_num))
theorem R28789 : Reach 28789 := rs (se 5 (by rfl) ⟨1349, by rfl⟩) (B 2699 (by norm_num) ⟨1349, by rfl⟩ (by norm_num))
theorem R28793 : Reach 28793 := rs (se 2 (by rfl) ⟨10797, by rfl⟩) (B 21595 (by norm_num) ⟨10797, by rfl⟩ (by norm_num))
theorem R28797 : Reach 28797 := rs (se 3 (by rfl) ⟨5399, by rfl⟩) (B 10799 (by norm_num) ⟨5399, by rfl⟩ (by norm_num))
theorem R61565 : Reach 61565 := rs (se 3 (by rfl) ⟨11543, by rfl⟩) (B 23087 (by norm_num) ⟨11543, by rfl⟩ (by norm_num))
theorem R28801 : Reach 28801 := rs (se 2 (by rfl) ⟨10800, by rfl⟩) (B 21601 (by norm_num) ⟨10800, by rfl⟩ (by norm_num))
theorem R28805 : Reach 28805 := rs (se 4 (by rfl) ⟨2700, by rfl⟩) (B 5401 (by norm_num) ⟨2700, by rfl⟩ (by norm_num))
theorem R28809 : Reach 28809 := rs (se 2 (by rfl) ⟨10803, by rfl⟩) (B 21607 (by norm_num) ⟨10803, by rfl⟩ (by norm_num))
theorem R28813 : Reach 28813 := rs (se 3 (by rfl) ⟨5402, by rfl⟩) (B 10805 (by norm_num) ⟨5402, by rfl⟩ (by norm_num))
theorem R28817 : Reach 28817 := rs (se 2 (by rfl) ⟨10806, by rfl⟩) (B 21613 (by norm_num) ⟨10806, by rfl⟩ (by norm_num))
theorem R28821 : Reach 28821 := rs (se 6 (by rfl) ⟨675, by rfl⟩) (B 1351 (by norm_num) ⟨675, by rfl⟩ (by norm_num))
theorem R28825 : Reach 28825 := rs (se 2 (by rfl) ⟨10809, by rfl⟩) (B 21619 (by norm_num) ⟨10809, by rfl⟩ (by norm_num))
theorem R28829 : Reach 28829 := rs (se 3 (by rfl) ⟨5405, by rfl⟩) (B 10811 (by norm_num) ⟨5405, by rfl⟩ (by norm_num))
theorem R28833 : Reach 28833 := rs (se 2 (by rfl) ⟨10812, by rfl⟩) (B 21625 (by norm_num) ⟨10812, by rfl⟩ (by norm_num))
theorem R28837 : Reach 28837 := rs (se 4 (by rfl) ⟨2703, by rfl⟩) (B 5407 (by norm_num) ⟨2703, by rfl⟩ (by norm_num))
theorem R28841 : Reach 28841 := rs (se 2 (by rfl) ⟨10815, by rfl⟩) (B 21631 (by norm_num) ⟨10815, by rfl⟩ (by norm_num))
theorem R61613 : Reach 61613 := rs (se 3 (by rfl) ⟨11552, by rfl⟩) (B 23105 (by norm_num) ⟨11552, by rfl⟩ (by norm_num))
theorem R28845 : Reach 28845 := rs (se 3 (by rfl) ⟨5408, by rfl⟩) (B 10817 (by norm_num) ⟨5408, by rfl⟩ (by norm_num))
theorem R28849 : Reach 28849 := rs (se 2 (by rfl) ⟨10818, by rfl⟩) (B 21637 (by norm_num) ⟨10818, by rfl⟩ (by norm_num))
theorem R28853 : Reach 28853 := rs (se 5 (by rfl) ⟨1352, by rfl⟩) (B 2705 (by norm_num) ⟨1352, by rfl⟩ (by norm_num))
theorem R28857 : Reach 28857 := rs (se 2 (by rfl) ⟨10821, by rfl⟩) (B 21643 (by norm_num) ⟨10821, by rfl⟩ (by norm_num))
theorem R28861 : Reach 28861 := rs (se 3 (by rfl) ⟨5411, by rfl⟩) (B 10823 (by norm_num) ⟨5411, by rfl⟩ (by norm_num))
theorem R28865 : Reach 28865 := rs (se 2 (by rfl) ⟨10824, by rfl⟩) (B 21649 (by norm_num) ⟨10824, by rfl⟩ (by norm_num))
theorem R28869 : Reach 28869 := rs (se 4 (by rfl) ⟨2706, by rfl⟩) (B 5413 (by norm_num) ⟨2706, by rfl⟩ (by norm_num))
theorem R28873 : Reach 28873 := rs (se 2 (by rfl) ⟨10827, by rfl⟩) (B 21655 (by norm_num) ⟨10827, by rfl⟩ (by norm_num))
theorem R28877 : Reach 28877 := rs (se 3 (by rfl) ⟨5414, by rfl⟩) (B 10829 (by norm_num) ⟨5414, by rfl⟩ (by norm_num))
theorem R28881 : Reach 28881 := rs (se 2 (by rfl) ⟨10830, by rfl⟩) (B 21661 (by norm_num) ⟨10830, by rfl⟩ (by norm_num))
theorem R28885 : Reach 28885 := rs (se 7 (by rfl) ⟨338, by rfl⟩) (B 677 (by norm_num) ⟨338, by rfl⟩ (by norm_num))
theorem R28889 : Reach 28889 := rs (se 2 (by rfl) ⟨10833, by rfl⟩) (B 21667 (by norm_num) ⟨10833, by rfl⟩ (by norm_num))
theorem R28893 : Reach 28893 := rs (se 3 (by rfl) ⟨5417, by rfl⟩) (B 10835 (by norm_num) ⟨5417, by rfl⟩ (by norm_num))
theorem R28897 : Reach 28897 := rs (se 2 (by rfl) ⟨10836, by rfl⟩) (B 21673 (by norm_num) ⟨10836, by rfl⟩ (by norm_num))
theorem R28901 : Reach 28901 := rs (se 4 (by rfl) ⟨2709, by rfl⟩) (B 5419 (by norm_num) ⟨2709, by rfl⟩ (by norm_num))
theorem R28905 : Reach 28905 := rs (se 2 (by rfl) ⟨10839, by rfl⟩) (B 21679 (by norm_num) ⟨10839, by rfl⟩ (by norm_num))
theorem R28909 : Reach 28909 := rs (se 3 (by rfl) ⟨5420, by rfl⟩) (B 10841 (by norm_num) ⟨5420, by rfl⟩ (by norm_num))
theorem R28913 : Reach 28913 := rs (se 2 (by rfl) ⟨10842, by rfl⟩) (B 21685 (by norm_num) ⟨10842, by rfl⟩ (by norm_num))
theorem R61685 : Reach 61685 := rs (se 5 (by rfl) ⟨2891, by rfl⟩) (B 5783 (by norm_num) ⟨2891, by rfl⟩ (by norm_num))
theorem R28917 : Reach 28917 := rs (se 5 (by rfl) ⟨1355, by rfl⟩) (B 2711 (by norm_num) ⟨1355, by rfl⟩ (by norm_num))
theorem R28921 : Reach 28921 := rs (se 2 (by rfl) ⟨10845, by rfl⟩) (B 21691 (by norm_num) ⟨10845, by rfl⟩ (by norm_num))
theorem R28925 : Reach 28925 := rs (se 3 (by rfl) ⟨5423, by rfl⟩) (B 10847 (by norm_num) ⟨5423, by rfl⟩ (by norm_num))
theorem R28929 : Reach 28929 := rs (se 2 (by rfl) ⟨10848, by rfl⟩) (B 21697 (by norm_num) ⟨10848, by rfl⟩ (by norm_num))
theorem R28933 : Reach 28933 := rs (se 4 (by rfl) ⟨2712, by rfl⟩) (B 5425 (by norm_num) ⟨2712, by rfl⟩ (by norm_num))
theorem R28937 : Reach 28937 := rs (se 2 (by rfl) ⟨10851, by rfl⟩) (B 21703 (by norm_num) ⟨10851, by rfl⟩ (by norm_num))
theorem R28941 : Reach 28941 := rs (se 3 (by rfl) ⟨5426, by rfl⟩) (B 10853 (by norm_num) ⟨5426, by rfl⟩ (by norm_num))
theorem R28945 : Reach 28945 := rs (se 2 (by rfl) ⟨10854, by rfl⟩) (B 21709 (by norm_num) ⟨10854, by rfl⟩ (by norm_num))
theorem R28949 : Reach 28949 := rs (se 6 (by rfl) ⟨678, by rfl⟩) (B 1357 (by norm_num) ⟨678, by rfl⟩ (by norm_num))
theorem R28953 : Reach 28953 := rs (se 2 (by rfl) ⟨10857, by rfl⟩) (B 21715 (by norm_num) ⟨10857, by rfl⟩ (by norm_num))
theorem R28957 : Reach 28957 := rs (se 3 (by rfl) ⟨5429, by rfl⟩) (B 10859 (by norm_num) ⟨5429, by rfl⟩ (by norm_num))
theorem R28961 : Reach 28961 := rs (se 2 (by rfl) ⟨10860, by rfl⟩) (B 21721 (by norm_num) ⟨10860, by rfl⟩ (by norm_num))
theorem R28965 : Reach 28965 := rs (se 4 (by rfl) ⟨2715, by rfl⟩) (B 5431 (by norm_num) ⟨2715, by rfl⟩ (by norm_num))
theorem R28969 : Reach 28969 := rs (se 2 (by rfl) ⟨10863, by rfl⟩) (B 21727 (by norm_num) ⟨10863, by rfl⟩ (by norm_num))
theorem R28973 : Reach 28973 := rs (se 3 (by rfl) ⟨5432, by rfl⟩) (B 10865 (by norm_num) ⟨5432, by rfl⟩ (by norm_num))
theorem R28977 : Reach 28977 := rs (se 2 (by rfl) ⟨10866, by rfl⟩) (B 21733 (by norm_num) ⟨10866, by rfl⟩ (by norm_num))
theorem R28981 : Reach 28981 := rs (se 5 (by rfl) ⟨1358, by rfl⟩) (B 2717 (by norm_num) ⟨1358, by rfl⟩ (by norm_num))
theorem R28985 : Reach 28985 := rs (se 2 (by rfl) ⟨10869, by rfl⟩) (B 21739 (by norm_num) ⟨10869, by rfl⟩ (by norm_num))
theorem R61757 : Reach 61757 := rs (se 3 (by rfl) ⟨11579, by rfl⟩) (B 23159 (by norm_num) ⟨11579, by rfl⟩ (by norm_num))
theorem R28989 : Reach 28989 := rs (se 3 (by rfl) ⟨5435, by rfl⟩) (B 10871 (by norm_num) ⟨5435, by rfl⟩ (by norm_num))
theorem R28993 : Reach 28993 := rs (se 2 (by rfl) ⟨10872, by rfl⟩) (B 21745 (by norm_num) ⟨10872, by rfl⟩ (by norm_num))
theorem R28997 : Reach 28997 := rs (se 4 (by rfl) ⟨2718, by rfl⟩) (B 5437 (by norm_num) ⟨2718, by rfl⟩ (by norm_num))
theorem R29001 : Reach 29001 := rs (se 2 (by rfl) ⟨10875, by rfl⟩) (B 21751 (by norm_num) ⟨10875, by rfl⟩ (by norm_num))
theorem R29005 : Reach 29005 := rs (se 3 (by rfl) ⟨5438, by rfl⟩) (B 10877 (by norm_num) ⟨5438, by rfl⟩ (by norm_num))
theorem R29009 : Reach 29009 := rs (se 2 (by rfl) ⟨10878, by rfl⟩) (B 21757 (by norm_num) ⟨10878, by rfl⟩ (by norm_num))
theorem R29013 : Reach 29013 := rs (se 10 (by rfl) ⟨42, by rfl⟩) (B 85 (by norm_num) ⟨42, by rfl⟩ (by norm_num))
theorem R29017 : Reach 29017 := rs (se 2 (by rfl) ⟨10881, by rfl⟩) (B 21763 (by norm_num) ⟨10881, by rfl⟩ (by norm_num))
theorem R29021 : Reach 29021 := rs (se 3 (by rfl) ⟨5441, by rfl⟩) (B 10883 (by norm_num) ⟨5441, by rfl⟩ (by norm_num))
theorem R29025 : Reach 29025 := rs (se 2 (by rfl) ⟨10884, by rfl⟩) (B 21769 (by norm_num) ⟨10884, by rfl⟩ (by norm_num))
theorem R29029 : Reach 29029 := rs (se 4 (by rfl) ⟨2721, by rfl⟩) (B 5443 (by norm_num) ⟨2721, by rfl⟩ (by norm_num))
theorem R94565 : Reach 94565 := rs (se 4 (by rfl) ⟨8865, by rfl⟩) (B 17731 (by norm_num) ⟨8865, by rfl⟩ (by norm_num))
theorem R29033 : Reach 29033 := rs (se 2 (by rfl) ⟨10887, by rfl⟩) (B 21775 (by norm_num) ⟨10887, by rfl⟩ (by norm_num))
theorem R29037 : Reach 29037 := rs (se 3 (by rfl) ⟨5444, by rfl⟩) (B 10889 (by norm_num) ⟨5444, by rfl⟩ (by norm_num))
theorem R29041 : Reach 29041 := rs (se 2 (by rfl) ⟨10890, by rfl⟩) (B 21781 (by norm_num) ⟨10890, by rfl⟩ (by norm_num))
theorem R29045 : Reach 29045 := rs (se 5 (by rfl) ⟨1361, by rfl⟩) (B 2723 (by norm_num) ⟨1361, by rfl⟩ (by norm_num))
theorem R29049 : Reach 29049 := rs (se 2 (by rfl) ⟨10893, by rfl⟩) (B 21787 (by norm_num) ⟨10893, by rfl⟩ (by norm_num))
theorem R29053 : Reach 29053 := rs (se 3 (by rfl) ⟨5447, by rfl⟩) (B 10895 (by norm_num) ⟨5447, by rfl⟩ (by norm_num))
theorem R29057 : Reach 29057 := rs (se 2 (by rfl) ⟨10896, by rfl⟩) (B 21793 (by norm_num) ⟨10896, by rfl⟩ (by norm_num))
theorem R61829 : Reach 61829 := rs (se 4 (by rfl) ⟨5796, by rfl⟩) (B 11593 (by norm_num) ⟨5796, by rfl⟩ (by norm_num))
theorem R29061 : Reach 29061 := rs (se 4 (by rfl) ⟨2724, by rfl⟩) (B 5449 (by norm_num) ⟨2724, by rfl⟩ (by norm_num))
theorem R29065 : Reach 29065 := rs (se 2 (by rfl) ⟨10899, by rfl⟩) (B 21799 (by norm_num) ⟨10899, by rfl⟩ (by norm_num))
theorem R29069 : Reach 29069 := rs (se 3 (by rfl) ⟨5450, by rfl⟩) (B 10901 (by norm_num) ⟨5450, by rfl⟩ (by norm_num))
theorem R29073 : Reach 29073 := rs (se 2 (by rfl) ⟨10902, by rfl⟩) (B 21805 (by norm_num) ⟨10902, by rfl⟩ (by norm_num))
theorem R29077 : Reach 29077 := rs (se 6 (by rfl) ⟨681, by rfl⟩) (B 1363 (by norm_num) ⟨681, by rfl⟩ (by norm_num))
theorem R29081 : Reach 29081 := rs (se 2 (by rfl) ⟨10905, by rfl⟩) (B 21811 (by norm_num) ⟨10905, by rfl⟩ (by norm_num))
theorem R29085 : Reach 29085 := rs (se 3 (by rfl) ⟨5453, by rfl⟩) (B 10907 (by norm_num) ⟨5453, by rfl⟩ (by norm_num))
theorem R29089 : Reach 29089 := rs (se 2 (by rfl) ⟨10908, by rfl⟩) (B 21817 (by norm_num) ⟨10908, by rfl⟩ (by norm_num))
theorem R29093 : Reach 29093 := rs (se 4 (by rfl) ⟨2727, by rfl⟩) (B 5455 (by norm_num) ⟨2727, by rfl⟩ (by norm_num))
theorem R29097 : Reach 29097 := rs (se 2 (by rfl) ⟨10911, by rfl⟩) (B 21823 (by norm_num) ⟨10911, by rfl⟩ (by norm_num))
theorem R29101 : Reach 29101 := rs (se 3 (by rfl) ⟨5456, by rfl⟩) (B 10913 (by norm_num) ⟨5456, by rfl⟩ (by norm_num))
theorem R29105 : Reach 29105 := rs (se 2 (by rfl) ⟨10914, by rfl⟩) (B 21829 (by norm_num) ⟨10914, by rfl⟩ (by norm_num))
theorem R29109 : Reach 29109 := rs (se 5 (by rfl) ⟨1364, by rfl⟩) (B 2729 (by norm_num) ⟨1364, by rfl⟩ (by norm_num))
theorem R29113 : Reach 29113 := rs (se 2 (by rfl) ⟨10917, by rfl⟩) (B 21835 (by norm_num) ⟨10917, by rfl⟩ (by norm_num))
theorem R29117 : Reach 29117 := rs (se 3 (by rfl) ⟨5459, by rfl⟩) (B 10919 (by norm_num) ⟨5459, by rfl⟩ (by norm_num))
theorem R29121 : Reach 29121 := rs (se 2 (by rfl) ⟨10920, by rfl⟩) (B 21841 (by norm_num) ⟨10920, by rfl⟩ (by norm_num))
theorem R94661 : Reach 94661 := rs (se 4 (by rfl) ⟨8874, by rfl⟩) (B 17749 (by norm_num) ⟨8874, by rfl⟩ (by norm_num))
theorem R29125 : Reach 29125 := rs (se 4 (by rfl) ⟨2730, by rfl⟩) (B 5461 (by norm_num) ⟨2730, by rfl⟩ (by norm_num))
theorem R29129 : Reach 29129 := rs (se 2 (by rfl) ⟨10923, by rfl⟩) (B 21847 (by norm_num) ⟨10923, by rfl⟩ (by norm_num))
theorem R61901 : Reach 61901 := rs (se 3 (by rfl) ⟨11606, by rfl⟩) (B 23213 (by norm_num) ⟨11606, by rfl⟩ (by norm_num))
theorem R29133 : Reach 29133 := rs (se 3 (by rfl) ⟨5462, by rfl⟩) (B 10925 (by norm_num) ⟨5462, by rfl⟩ (by norm_num))
theorem R29137 : Reach 29137 := rs (se 2 (by rfl) ⟨10926, by rfl⟩) (B 21853 (by norm_num) ⟨10926, by rfl⟩ (by norm_num))
theorem R29141 : Reach 29141 := rs (se 7 (by rfl) ⟨341, by rfl⟩) (B 683 (by norm_num) ⟨341, by rfl⟩ (by norm_num))
theorem R29145 : Reach 29145 := rs (se 2 (by rfl) ⟨10929, by rfl⟩) (B 21859 (by norm_num) ⟨10929, by rfl⟩ (by norm_num))
theorem R29149 : Reach 29149 := rs (se 3 (by rfl) ⟨5465, by rfl⟩) (B 10931 (by norm_num) ⟨5465, by rfl⟩ (by norm_num))
theorem R29153 : Reach 29153 := rs (se 2 (by rfl) ⟨10932, by rfl⟩) (B 21865 (by norm_num) ⟨10932, by rfl⟩ (by norm_num))
theorem R29157 : Reach 29157 := rs (se 4 (by rfl) ⟨2733, by rfl⟩) (B 5467 (by norm_num) ⟨2733, by rfl⟩ (by norm_num))
theorem R29161 : Reach 29161 := rs (se 2 (by rfl) ⟨10935, by rfl⟩) (B 21871 (by norm_num) ⟨10935, by rfl⟩ (by norm_num))
theorem R29165 : Reach 29165 := rs (se 3 (by rfl) ⟨5468, by rfl⟩) (B 10937 (by norm_num) ⟨5468, by rfl⟩ (by norm_num))
theorem R29169 : Reach 29169 := rs (se 2 (by rfl) ⟨10938, by rfl⟩) (B 21877 (by norm_num) ⟨10938, by rfl⟩ (by norm_num))
theorem R29173 : Reach 29173 := rs (se 5 (by rfl) ⟨1367, by rfl⟩) (B 2735 (by norm_num) ⟨1367, by rfl⟩ (by norm_num))
theorem R29177 : Reach 29177 := rs (se 2 (by rfl) ⟨10941, by rfl⟩) (B 21883 (by norm_num) ⟨10941, by rfl⟩ (by norm_num))
theorem R29181 : Reach 29181 := rs (se 3 (by rfl) ⟨5471, by rfl⟩) (B 10943 (by norm_num) ⟨5471, by rfl⟩ (by norm_num))
theorem R29185 : Reach 29185 := rs (se 2 (by rfl) ⟨10944, by rfl⟩) (B 21889 (by norm_num) ⟨10944, by rfl⟩ (by norm_num))
theorem R29189 : Reach 29189 := rs (se 4 (by rfl) ⟨2736, by rfl⟩) (B 5473 (by norm_num) ⟨2736, by rfl⟩ (by norm_num))
theorem R29193 : Reach 29193 := rs (se 2 (by rfl) ⟨10947, by rfl⟩) (B 21895 (by norm_num) ⟨10947, by rfl⟩ (by norm_num))
theorem R29197 : Reach 29197 := rs (se 3 (by rfl) ⟨5474, by rfl⟩) (B 10949 (by norm_num) ⟨5474, by rfl⟩ (by norm_num))
theorem R29201 : Reach 29201 := rs (se 2 (by rfl) ⟨10950, by rfl⟩) (B 21901 (by norm_num) ⟨10950, by rfl⟩ (by norm_num))
theorem R61973 : Reach 61973 := rs (se 6 (by rfl) ⟨1452, by rfl⟩) (B 2905 (by norm_num) ⟨1452, by rfl⟩ (by norm_num))
theorem R29205 : Reach 29205 := rs (se 6 (by rfl) ⟨684, by rfl⟩) (B 1369 (by norm_num) ⟨684, by rfl⟩ (by norm_num))
theorem R29209 : Reach 29209 := rs (se 2 (by rfl) ⟨10953, by rfl⟩) (B 21907 (by norm_num) ⟨10953, by rfl⟩ (by norm_num))
theorem R29213 : Reach 29213 := rs (se 3 (by rfl) ⟨5477, by rfl⟩) (B 10955 (by norm_num) ⟨5477, by rfl⟩ (by norm_num))
theorem R29217 : Reach 29217 := rs (se 2 (by rfl) ⟨10956, by rfl⟩) (B 21913 (by norm_num) ⟨10956, by rfl⟩ (by norm_num))
theorem R29221 : Reach 29221 := rs (se 4 (by rfl) ⟨2739, by rfl⟩) (B 5479 (by norm_num) ⟨2739, by rfl⟩ (by norm_num))
theorem R29225 : Reach 29225 := rs (se 2 (by rfl) ⟨10959, by rfl⟩) (B 21919 (by norm_num) ⟨10959, by rfl⟩ (by norm_num))
theorem R29229 : Reach 29229 := rs (se 3 (by rfl) ⟨5480, by rfl⟩) (B 10961 (by norm_num) ⟨5480, by rfl⟩ (by norm_num))
theorem R29233 : Reach 29233 := rs (se 2 (by rfl) ⟨10962, by rfl⟩) (B 21925 (by norm_num) ⟨10962, by rfl⟩ (by norm_num))
theorem R29237 : Reach 29237 := rs (se 5 (by rfl) ⟨1370, by rfl⟩) (B 2741 (by norm_num) ⟨1370, by rfl⟩ (by norm_num))
theorem R29241 : Reach 29241 := rs (se 2 (by rfl) ⟨10965, by rfl⟩) (B 21931 (by norm_num) ⟨10965, by rfl⟩ (by norm_num))
theorem R29245 : Reach 29245 := rs (se 3 (by rfl) ⟨5483, by rfl⟩) (B 10967 (by norm_num) ⟨5483, by rfl⟩ (by norm_num))
theorem R29249 : Reach 29249 := rs (se 2 (by rfl) ⟨10968, by rfl⟩) (B 21937 (by norm_num) ⟨10968, by rfl⟩ (by norm_num))
theorem R29253 : Reach 29253 := rs (se 4 (by rfl) ⟨2742, by rfl⟩) (B 5485 (by norm_num) ⟨2742, by rfl⟩ (by norm_num))
theorem R29257 : Reach 29257 := rs (se 2 (by rfl) ⟨10971, by rfl⟩) (B 21943 (by norm_num) ⟨10971, by rfl⟩ (by norm_num))
theorem R29261 : Reach 29261 := rs (se 3 (by rfl) ⟨5486, by rfl⟩) (B 10973 (by norm_num) ⟨5486, by rfl⟩ (by norm_num))
theorem R29265 : Reach 29265 := rs (se 2 (by rfl) ⟨10974, by rfl⟩) (B 21949 (by norm_num) ⟨10974, by rfl⟩ (by norm_num))
theorem R29269 : Reach 29269 := rs (se 8 (by rfl) ⟨171, by rfl⟩) (B 343 (by norm_num) ⟨171, by rfl⟩ (by norm_num))
theorem R29273 : Reach 29273 := rs (se 2 (by rfl) ⟨10977, by rfl⟩) (B 21955 (by norm_num) ⟨10977, by rfl⟩ (by norm_num))
theorem R62045 : Reach 62045 := rs (se 3 (by rfl) ⟨11633, by rfl⟩) (B 23267 (by norm_num) ⟨11633, by rfl⟩ (by norm_num))
theorem R29277 : Reach 29277 := rs (se 3 (by rfl) ⟨5489, by rfl⟩) (B 10979 (by norm_num) ⟨5489, by rfl⟩ (by norm_num))
theorem R29281 : Reach 29281 := rs (se 2 (by rfl) ⟨10980, by rfl⟩) (B 21961 (by norm_num) ⟨10980, by rfl⟩ (by norm_num))
theorem R29285 : Reach 29285 := rs (se 4 (by rfl) ⟨2745, by rfl⟩) (B 5491 (by norm_num) ⟨2745, by rfl⟩ (by norm_num))
theorem R29289 : Reach 29289 := rs (se 2 (by rfl) ⟨10983, by rfl⟩) (B 21967 (by norm_num) ⟨10983, by rfl⟩ (by norm_num))
theorem R29293 : Reach 29293 := rs (se 3 (by rfl) ⟨5492, by rfl⟩) (B 10985 (by norm_num) ⟨5492, by rfl⟩ (by norm_num))
theorem R29297 : Reach 29297 := rs (se 2 (by rfl) ⟨10986, by rfl⟩) (B 21973 (by norm_num) ⟨10986, by rfl⟩ (by norm_num))
theorem R29301 : Reach 29301 := rs (se 5 (by rfl) ⟨1373, by rfl⟩) (B 2747 (by norm_num) ⟨1373, by rfl⟩ (by norm_num))
theorem R29305 : Reach 29305 := rs (se 2 (by rfl) ⟨10989, by rfl⟩) (B 21979 (by norm_num) ⟨10989, by rfl⟩ (by norm_num))
theorem R29309 : Reach 29309 := rs (se 3 (by rfl) ⟨5495, by rfl⟩) (B 10991 (by norm_num) ⟨5495, by rfl⟩ (by norm_num))
theorem R29313 : Reach 29313 := rs (se 2 (by rfl) ⟨10992, by rfl⟩) (B 21985 (by norm_num) ⟨10992, by rfl⟩ (by norm_num))
theorem R29317 : Reach 29317 := rs (se 4 (by rfl) ⟨2748, by rfl⟩) (B 5497 (by norm_num) ⟨2748, by rfl⟩ (by norm_num))
theorem R29321 : Reach 29321 := rs (se 2 (by rfl) ⟨10995, by rfl⟩) (B 21991 (by norm_num) ⟨10995, by rfl⟩ (by norm_num))
theorem R29325 : Reach 29325 := rs (se 3 (by rfl) ⟨5498, by rfl⟩) (B 10997 (by norm_num) ⟨5498, by rfl⟩ (by norm_num))
theorem R29329 : Reach 29329 := rs (se 2 (by rfl) ⟨10998, by rfl⟩) (B 21997 (by norm_num) ⟨10998, by rfl⟩ (by norm_num))
theorem R29333 : Reach 29333 := rs (se 6 (by rfl) ⟨687, by rfl⟩) (B 1375 (by norm_num) ⟨687, by rfl⟩ (by norm_num))
theorem R29337 : Reach 29337 := rs (se 2 (by rfl) ⟨11001, by rfl⟩) (B 22003 (by norm_num) ⟨11001, by rfl⟩ (by norm_num))
theorem R29341 : Reach 29341 := rs (se 3 (by rfl) ⟨5501, by rfl⟩) (B 11003 (by norm_num) ⟨5501, by rfl⟩ (by norm_num))
theorem R29345 : Reach 29345 := rs (se 2 (by rfl) ⟨11004, by rfl⟩) (B 22009 (by norm_num) ⟨11004, by rfl⟩ (by norm_num))
theorem R62117 : Reach 62117 := rs (se 4 (by rfl) ⟨5823, by rfl⟩) (B 11647 (by norm_num) ⟨5823, by rfl⟩ (by norm_num))
theorem R29349 : Reach 29349 := rs (se 4 (by rfl) ⟨2751, by rfl⟩) (B 5503 (by norm_num) ⟨2751, by rfl⟩ (by norm_num))
theorem R29353 : Reach 29353 := rs (se 2 (by rfl) ⟨11007, by rfl⟩) (B 22015 (by norm_num) ⟨11007, by rfl⟩ (by norm_num))
theorem R29357 : Reach 29357 := rs (se 3 (by rfl) ⟨5504, by rfl⟩) (B 11009 (by norm_num) ⟨5504, by rfl⟩ (by norm_num))
theorem R29361 : Reach 29361 := rs (se 2 (by rfl) ⟨11010, by rfl⟩) (B 22021 (by norm_num) ⟨11010, by rfl⟩ (by norm_num))
theorem R29365 : Reach 29365 := rs (se 5 (by rfl) ⟨1376, by rfl⟩) (B 2753 (by norm_num) ⟨1376, by rfl⟩ (by norm_num))
theorem R29369 : Reach 29369 := rs (se 2 (by rfl) ⟨11013, by rfl⟩) (B 22027 (by norm_num) ⟨11013, by rfl⟩ (by norm_num))
theorem R29373 : Reach 29373 := rs (se 3 (by rfl) ⟨5507, by rfl⟩) (B 11015 (by norm_num) ⟨5507, by rfl⟩ (by norm_num))
theorem R29377 : Reach 29377 := rs (se 2 (by rfl) ⟨11016, by rfl⟩) (B 22033 (by norm_num) ⟨11016, by rfl⟩ (by norm_num))
theorem R29381 : Reach 29381 := rs (se 4 (by rfl) ⟨2754, by rfl⟩) (B 5509 (by norm_num) ⟨2754, by rfl⟩ (by norm_num))
theorem R29385 : Reach 29385 := rs (se 2 (by rfl) ⟨11019, by rfl⟩) (B 22039 (by norm_num) ⟨11019, by rfl⟩ (by norm_num))
theorem R29389 : Reach 29389 := rs (se 3 (by rfl) ⟨5510, by rfl⟩) (B 11021 (by norm_num) ⟨5510, by rfl⟩ (by norm_num))
theorem R29393 : Reach 29393 := rs (se 2 (by rfl) ⟨11022, by rfl⟩) (B 22045 (by norm_num) ⟨11022, by rfl⟩ (by norm_num))
theorem R29397 : Reach 29397 := rs (se 7 (by rfl) ⟨344, by rfl⟩) (B 689 (by norm_num) ⟨344, by rfl⟩ (by norm_num))
theorem R29401 : Reach 29401 := rs (se 2 (by rfl) ⟨11025, by rfl⟩) (B 22051 (by norm_num) ⟨11025, by rfl⟩ (by norm_num))
theorem R29405 : Reach 29405 := rs (se 3 (by rfl) ⟨5513, by rfl⟩) (B 11027 (by norm_num) ⟨5513, by rfl⟩ (by norm_num))
theorem R29409 : Reach 29409 := rs (se 2 (by rfl) ⟨11028, by rfl⟩) (B 22057 (by norm_num) ⟨11028, by rfl⟩ (by norm_num))
theorem R29413 : Reach 29413 := rs (se 4 (by rfl) ⟨2757, by rfl⟩) (B 5515 (by norm_num) ⟨2757, by rfl⟩ (by norm_num))
theorem R29417 : Reach 29417 := rs (se 2 (by rfl) ⟨11031, by rfl⟩) (B 22063 (by norm_num) ⟨11031, by rfl⟩ (by norm_num))
theorem R62189 : Reach 62189 := rs (se 3 (by rfl) ⟨11660, by rfl⟩) (B 23321 (by norm_num) ⟨11660, by rfl⟩ (by norm_num))
theorem R29421 : Reach 29421 := rs (se 3 (by rfl) ⟨5516, by rfl⟩) (B 11033 (by norm_num) ⟨5516, by rfl⟩ (by norm_num))
theorem R29425 : Reach 29425 := rs (se 2 (by rfl) ⟨11034, by rfl⟩) (B 22069 (by norm_num) ⟨11034, by rfl⟩ (by norm_num))
theorem R29429 : Reach 29429 := rs (se 5 (by rfl) ⟨1379, by rfl⟩) (B 2759 (by norm_num) ⟨1379, by rfl⟩ (by norm_num))
theorem R29433 : Reach 29433 := rs (se 2 (by rfl) ⟨11037, by rfl⟩) (B 22075 (by norm_num) ⟨11037, by rfl⟩ (by norm_num))
theorem R29437 : Reach 29437 := rs (se 3 (by rfl) ⟨5519, by rfl⟩) (B 11039 (by norm_num) ⟨5519, by rfl⟩ (by norm_num))
theorem R29441 : Reach 29441 := rs (se 2 (by rfl) ⟨11040, by rfl⟩) (B 22081 (by norm_num) ⟨11040, by rfl⟩ (by norm_num))
theorem R29445 : Reach 29445 := rs (se 4 (by rfl) ⟨2760, by rfl⟩) (B 5521 (by norm_num) ⟨2760, by rfl⟩ (by norm_num))
theorem R29449 : Reach 29449 := rs (se 2 (by rfl) ⟨11043, by rfl⟩) (B 22087 (by norm_num) ⟨11043, by rfl⟩ (by norm_num))
theorem R29453 : Reach 29453 := rs (se 3 (by rfl) ⟨5522, by rfl⟩) (B 11045 (by norm_num) ⟨5522, by rfl⟩ (by norm_num))
theorem R29457 : Reach 29457 := rs (se 2 (by rfl) ⟨11046, by rfl⟩) (B 22093 (by norm_num) ⟨11046, by rfl⟩ (by norm_num))
theorem R29461 : Reach 29461 := rs (se 6 (by rfl) ⟨690, by rfl⟩) (B 1381 (by norm_num) ⟨690, by rfl⟩ (by norm_num))
theorem R29465 : Reach 29465 := rs (se 2 (by rfl) ⟨11049, by rfl⟩) (B 22099 (by norm_num) ⟨11049, by rfl⟩ (by norm_num))
theorem R29469 : Reach 29469 := rs (se 3 (by rfl) ⟨5525, by rfl⟩) (B 11051 (by norm_num) ⟨5525, by rfl⟩ (by norm_num))
theorem R29473 : Reach 29473 := rs (se 2 (by rfl) ⟨11052, by rfl⟩) (B 22105 (by norm_num) ⟨11052, by rfl⟩ (by norm_num))
theorem R29477 : Reach 29477 := rs (se 4 (by rfl) ⟨2763, by rfl⟩) (B 5527 (by norm_num) ⟨2763, by rfl⟩ (by norm_num))
theorem R29481 : Reach 29481 := rs (se 2 (by rfl) ⟨11055, by rfl⟩) (B 22111 (by norm_num) ⟨11055, by rfl⟩ (by norm_num))
theorem R29485 : Reach 29485 := rs (se 3 (by rfl) ⟨5528, by rfl⟩) (B 11057 (by norm_num) ⟨5528, by rfl⟩ (by norm_num))
theorem R29489 : Reach 29489 := rs (se 2 (by rfl) ⟨11058, by rfl⟩) (B 22117 (by norm_num) ⟨11058, by rfl⟩ (by norm_num))
theorem R62261 : Reach 62261 := rs (se 5 (by rfl) ⟨2918, by rfl⟩) (B 5837 (by norm_num) ⟨2918, by rfl⟩ (by norm_num))
theorem R29493 : Reach 29493 := rs (se 5 (by rfl) ⟨1382, by rfl⟩) (B 2765 (by norm_num) ⟨1382, by rfl⟩ (by norm_num))
theorem R29497 : Reach 29497 := rs (se 2 (by rfl) ⟨11061, by rfl⟩) (B 22123 (by norm_num) ⟨11061, by rfl⟩ (by norm_num))
theorem R29501 : Reach 29501 := rs (se 3 (by rfl) ⟨5531, by rfl⟩) (B 11063 (by norm_num) ⟨5531, by rfl⟩ (by norm_num))
theorem R29505 : Reach 29505 := rs (se 2 (by rfl) ⟨11064, by rfl⟩) (B 22129 (by norm_num) ⟨11064, by rfl⟩ (by norm_num))
theorem R29509 : Reach 29509 := rs (se 4 (by rfl) ⟨2766, by rfl⟩) (B 5533 (by norm_num) ⟨2766, by rfl⟩ (by norm_num))
theorem R29513 : Reach 29513 := rs (se 2 (by rfl) ⟨11067, by rfl⟩) (B 22135 (by norm_num) ⟨11067, by rfl⟩ (by norm_num))
theorem R29517 : Reach 29517 := rs (se 3 (by rfl) ⟨5534, by rfl⟩) (B 11069 (by norm_num) ⟨5534, by rfl⟩ (by norm_num))
theorem R29521 : Reach 29521 := rs (se 2 (by rfl) ⟨11070, by rfl⟩) (B 22141 (by norm_num) ⟨11070, by rfl⟩ (by norm_num))
theorem R29525 : Reach 29525 := rs (se 9 (by rfl) ⟨86, by rfl⟩) (B 173 (by norm_num) ⟨86, by rfl⟩ (by norm_num))
theorem R29529 : Reach 29529 := rs (se 2 (by rfl) ⟨11073, by rfl⟩) (B 22147 (by norm_num) ⟨11073, by rfl⟩ (by norm_num))
theorem R29533 : Reach 29533 := rs (se 3 (by rfl) ⟨5537, by rfl⟩) (B 11075 (by norm_num) ⟨5537, by rfl⟩ (by norm_num))
theorem R29537 : Reach 29537 := rs (se 2 (by rfl) ⟨11076, by rfl⟩) (B 22153 (by norm_num) ⟨11076, by rfl⟩ (by norm_num))
theorem R29541 : Reach 29541 := rs (se 4 (by rfl) ⟨2769, by rfl⟩) (B 5539 (by norm_num) ⟨2769, by rfl⟩ (by norm_num))
theorem R29545 : Reach 29545 := rs (se 2 (by rfl) ⟨11079, by rfl⟩) (B 22159 (by norm_num) ⟨11079, by rfl⟩ (by norm_num))
theorem R29549 : Reach 29549 := rs (se 3 (by rfl) ⟨5540, by rfl⟩) (B 11081 (by norm_num) ⟨5540, by rfl⟩ (by norm_num))
theorem R29553 : Reach 29553 := rs (se 2 (by rfl) ⟨11082, by rfl⟩) (B 22165 (by norm_num) ⟨11082, by rfl⟩ (by norm_num))
theorem R95093 : Reach 95093 := rs (se 5 (by rfl) ⟨4457, by rfl⟩) (B 8915 (by norm_num) ⟨4457, by rfl⟩ (by norm_num))
theorem R29557 : Reach 29557 := rs (se 5 (by rfl) ⟨1385, by rfl⟩) (B 2771 (by norm_num) ⟨1385, by rfl⟩ (by norm_num))
theorem R29561 : Reach 29561 := rs (se 2 (by rfl) ⟨11085, by rfl⟩) (B 22171 (by norm_num) ⟨11085, by rfl⟩ (by norm_num))
theorem R62333 : Reach 62333 := rs (se 3 (by rfl) ⟨11687, by rfl⟩) (B 23375 (by norm_num) ⟨11687, by rfl⟩ (by norm_num))
theorem R29565 : Reach 29565 := rs (se 3 (by rfl) ⟨5543, by rfl⟩) (B 11087 (by norm_num) ⟨5543, by rfl⟩ (by norm_num))
theorem R29569 : Reach 29569 := rs (se 2 (by rfl) ⟨11088, by rfl⟩) (B 22177 (by norm_num) ⟨11088, by rfl⟩ (by norm_num))
theorem R29573 : Reach 29573 := rs (se 4 (by rfl) ⟨2772, by rfl⟩) (B 5545 (by norm_num) ⟨2772, by rfl⟩ (by norm_num))
theorem R29577 : Reach 29577 := rs (se 2 (by rfl) ⟨11091, by rfl⟩) (B 22183 (by norm_num) ⟨11091, by rfl⟩ (by norm_num))
theorem R29581 : Reach 29581 := rs (se 3 (by rfl) ⟨5546, by rfl⟩) (B 11093 (by norm_num) ⟨5546, by rfl⟩ (by norm_num))
theorem R29585 : Reach 29585 := rs (se 2 (by rfl) ⟨11094, by rfl⟩) (B 22189 (by norm_num) ⟨11094, by rfl⟩ (by norm_num))
theorem R29589 : Reach 29589 := rs (se 6 (by rfl) ⟨693, by rfl⟩) (B 1387 (by norm_num) ⟨693, by rfl⟩ (by norm_num))
theorem R29593 : Reach 29593 := rs (se 2 (by rfl) ⟨11097, by rfl⟩) (B 22195 (by norm_num) ⟨11097, by rfl⟩ (by norm_num))
theorem R29597 : Reach 29597 := rs (se 3 (by rfl) ⟨5549, by rfl⟩) (B 11099 (by norm_num) ⟨5549, by rfl⟩ (by norm_num))
theorem R29601 : Reach 29601 := rs (se 2 (by rfl) ⟨11100, by rfl⟩) (B 22201 (by norm_num) ⟨11100, by rfl⟩ (by norm_num))
theorem R29605 : Reach 29605 := rs (se 4 (by rfl) ⟨2775, by rfl⟩) (B 5551 (by norm_num) ⟨2775, by rfl⟩ (by norm_num))
theorem R29609 : Reach 29609 := rs (se 2 (by rfl) ⟨11103, by rfl⟩) (B 22207 (by norm_num) ⟨11103, by rfl⟩ (by norm_num))
theorem R29613 : Reach 29613 := rs (se 3 (by rfl) ⟨5552, by rfl⟩) (B 11105 (by norm_num) ⟨5552, by rfl⟩ (by norm_num))
theorem R29617 : Reach 29617 := rs (se 2 (by rfl) ⟨11106, by rfl⟩) (B 22213 (by norm_num) ⟨11106, by rfl⟩ (by norm_num))
theorem R127925 : Reach 127925 := rs (se 5 (by rfl) ⟨5996, by rfl⟩) (B 11993 (by norm_num) ⟨5996, by rfl⟩ (by norm_num))
theorem R29621 : Reach 29621 := rs (se 5 (by rfl) ⟨1388, by rfl⟩) (B 2777 (by norm_num) ⟨1388, by rfl⟩ (by norm_num))
theorem R29625 : Reach 29625 := rs (se 2 (by rfl) ⟨11109, by rfl⟩) (B 22219 (by norm_num) ⟨11109, by rfl⟩ (by norm_num))
theorem R29629 : Reach 29629 := rs (se 3 (by rfl) ⟨5555, by rfl⟩) (B 11111 (by norm_num) ⟨5555, by rfl⟩ (by norm_num))
theorem R29633 : Reach 29633 := rs (se 2 (by rfl) ⟨11112, by rfl⟩) (B 22225 (by norm_num) ⟨11112, by rfl⟩ (by norm_num))
theorem R62405 : Reach 62405 := rs (se 4 (by rfl) ⟨5850, by rfl⟩) (B 11701 (by norm_num) ⟨5850, by rfl⟩ (by norm_num))
theorem R29637 : Reach 29637 := rs (se 4 (by rfl) ⟨2778, by rfl⟩) (B 5557 (by norm_num) ⟨2778, by rfl⟩ (by norm_num))
theorem R29641 : Reach 29641 := rs (se 2 (by rfl) ⟨11115, by rfl⟩) (B 22231 (by norm_num) ⟨11115, by rfl⟩ (by norm_num))
theorem R29645 : Reach 29645 := rs (se 3 (by rfl) ⟨5558, by rfl⟩) (B 11117 (by norm_num) ⟨5558, by rfl⟩ (by norm_num))
theorem R29649 : Reach 29649 := rs (se 2 (by rfl) ⟨11118, by rfl⟩) (B 22237 (by norm_num) ⟨11118, by rfl⟩ (by norm_num))
theorem R29653 : Reach 29653 := rs (se 7 (by rfl) ⟨347, by rfl⟩) (B 695 (by norm_num) ⟨347, by rfl⟩ (by norm_num))
theorem R29657 : Reach 29657 := rs (se 2 (by rfl) ⟨11121, by rfl⟩) (B 22243 (by norm_num) ⟨11121, by rfl⟩ (by norm_num))
theorem R29661 : Reach 29661 := rs (se 3 (by rfl) ⟨5561, by rfl⟩) (B 11123 (by norm_num) ⟨5561, by rfl⟩ (by norm_num))
theorem R29665 : Reach 29665 := rs (se 2 (by rfl) ⟨11124, by rfl⟩) (B 22249 (by norm_num) ⟨11124, by rfl⟩ (by norm_num))
theorem R29669 : Reach 29669 := rs (se 4 (by rfl) ⟨2781, by rfl⟩) (B 5563 (by norm_num) ⟨2781, by rfl⟩ (by norm_num))
theorem R29673 : Reach 29673 := rs (se 2 (by rfl) ⟨11127, by rfl⟩) (B 22255 (by norm_num) ⟨11127, by rfl⟩ (by norm_num))
theorem R29677 : Reach 29677 := rs (se 3 (by rfl) ⟨5564, by rfl⟩) (B 11129 (by norm_num) ⟨5564, by rfl⟩ (by norm_num))
theorem R29681 : Reach 29681 := rs (se 2 (by rfl) ⟨11130, by rfl⟩) (B 22261 (by norm_num) ⟨11130, by rfl⟩ (by norm_num))
theorem R29685 : Reach 29685 := rs (se 5 (by rfl) ⟨1391, by rfl⟩) (B 2783 (by norm_num) ⟨1391, by rfl⟩ (by norm_num))
theorem R29689 : Reach 29689 := rs (se 2 (by rfl) ⟨11133, by rfl⟩) (B 22267 (by norm_num) ⟨11133, by rfl⟩ (by norm_num))
theorem R29693 : Reach 29693 := rs (se 3 (by rfl) ⟨5567, by rfl⟩) (B 11135 (by norm_num) ⟨5567, by rfl⟩ (by norm_num))
theorem R29697 : Reach 29697 := rs (se 2 (by rfl) ⟨11136, by rfl⟩) (B 22273 (by norm_num) ⟨11136, by rfl⟩ (by norm_num))
theorem R29701 : Reach 29701 := rs (se 4 (by rfl) ⟨2784, by rfl⟩) (B 5569 (by norm_num) ⟨2784, by rfl⟩ (by norm_num))
theorem R29705 : Reach 29705 := rs (se 2 (by rfl) ⟨11139, by rfl⟩) (B 22279 (by norm_num) ⟨11139, by rfl⟩ (by norm_num))
theorem R62477 : Reach 62477 := rs (se 3 (by rfl) ⟨11714, by rfl⟩) (B 23429 (by norm_num) ⟨11714, by rfl⟩ (by norm_num))
theorem R29709 : Reach 29709 := rs (se 3 (by rfl) ⟨5570, by rfl⟩) (B 11141 (by norm_num) ⟨5570, by rfl⟩ (by norm_num))
theorem R29713 : Reach 29713 := rs (se 2 (by rfl) ⟨11142, by rfl⟩) (B 22285 (by norm_num) ⟨11142, by rfl⟩ (by norm_num))
theorem R29717 : Reach 29717 := rs (se 6 (by rfl) ⟨696, by rfl⟩) (B 1393 (by norm_num) ⟨696, by rfl⟩ (by norm_num))
theorem R29721 : Reach 29721 := rs (se 2 (by rfl) ⟨11145, by rfl⟩) (B 22291 (by norm_num) ⟨11145, by rfl⟩ (by norm_num))
theorem R29725 : Reach 29725 := rs (se 3 (by rfl) ⟨5573, by rfl⟩) (B 11147 (by norm_num) ⟨5573, by rfl⟩ (by norm_num))
theorem R29729 : Reach 29729 := rs (se 2 (by rfl) ⟨11148, by rfl⟩) (B 22297 (by norm_num) ⟨11148, by rfl⟩ (by norm_num))
theorem R29733 : Reach 29733 := rs (se 4 (by rfl) ⟨2787, by rfl⟩) (B 5575 (by norm_num) ⟨2787, by rfl⟩ (by norm_num))
theorem R29737 : Reach 29737 := rs (se 2 (by rfl) ⟨11151, by rfl⟩) (B 22303 (by norm_num) ⟨11151, by rfl⟩ (by norm_num))
theorem R29741 : Reach 29741 := rs (se 3 (by rfl) ⟨5576, by rfl⟩) (B 11153 (by norm_num) ⟨5576, by rfl⟩ (by norm_num))
theorem R29745 : Reach 29745 := rs (se 2 (by rfl) ⟨11154, by rfl⟩) (B 22309 (by norm_num) ⟨11154, by rfl⟩ (by norm_num))
theorem R29749 : Reach 29749 := rs (se 5 (by rfl) ⟨1394, by rfl⟩) (B 2789 (by norm_num) ⟨1394, by rfl⟩ (by norm_num))
theorem R29753 : Reach 29753 := rs (se 2 (by rfl) ⟨11157, by rfl⟩) (B 22315 (by norm_num) ⟨11157, by rfl⟩ (by norm_num))
theorem R29757 : Reach 29757 := rs (se 3 (by rfl) ⟨5579, by rfl⟩) (B 11159 (by norm_num) ⟨5579, by rfl⟩ (by norm_num))
theorem R29761 : Reach 29761 := rs (se 2 (by rfl) ⟨11160, by rfl⟩) (B 22321 (by norm_num) ⟨11160, by rfl⟩ (by norm_num))
theorem R29765 : Reach 29765 := rs (se 4 (by rfl) ⟨2790, by rfl⟩) (B 5581 (by norm_num) ⟨2790, by rfl⟩ (by norm_num))
theorem R29769 : Reach 29769 := rs (se 2 (by rfl) ⟨11163, by rfl⟩) (B 22327 (by norm_num) ⟨11163, by rfl⟩ (by norm_num))
theorem R29773 : Reach 29773 := rs (se 3 (by rfl) ⟨5582, by rfl⟩) (B 11165 (by norm_num) ⟨5582, by rfl⟩ (by norm_num))
theorem R29777 : Reach 29777 := rs (se 2 (by rfl) ⟨11166, by rfl⟩) (B 22333 (by norm_num) ⟨11166, by rfl⟩ (by norm_num))
theorem R62549 : Reach 62549 := rs (se 8 (by rfl) ⟨366, by rfl⟩) (B 733 (by norm_num) ⟨366, by rfl⟩ (by norm_num))
theorem R29781 : Reach 29781 := rs (se 8 (by rfl) ⟨174, by rfl⟩) (B 349 (by norm_num) ⟨174, by rfl⟩ (by norm_num))
theorem R29785 : Reach 29785 := rs (se 2 (by rfl) ⟨11169, by rfl⟩) (B 22339 (by norm_num) ⟨11169, by rfl⟩ (by norm_num))
theorem R29789 : Reach 29789 := rs (se 3 (by rfl) ⟨5585, by rfl⟩) (B 11171 (by norm_num) ⟨5585, by rfl⟩ (by norm_num))
theorem R29793 : Reach 29793 := rs (se 2 (by rfl) ⟨11172, by rfl⟩) (B 22345 (by norm_num) ⟨11172, by rfl⟩ (by norm_num))
theorem R29797 : Reach 29797 := rs (se 4 (by rfl) ⟨2793, by rfl⟩) (B 5587 (by norm_num) ⟨2793, by rfl⟩ (by norm_num))
theorem R29801 : Reach 29801 := rs (se 2 (by rfl) ⟨11175, by rfl⟩) (B 22351 (by norm_num) ⟨11175, by rfl⟩ (by norm_num))
theorem R29805 : Reach 29805 := rs (se 3 (by rfl) ⟨5588, by rfl⟩) (B 11177 (by norm_num) ⟨5588, by rfl⟩ (by norm_num))
theorem R29809 : Reach 29809 := rs (se 2 (by rfl) ⟨11178, by rfl⟩) (B 22357 (by norm_num) ⟨11178, by rfl⟩ (by norm_num))
theorem R29813 : Reach 29813 := rs (se 5 (by rfl) ⟨1397, by rfl⟩) (B 2795 (by norm_num) ⟨1397, by rfl⟩ (by norm_num))
theorem R29817 : Reach 29817 := rs (se 2 (by rfl) ⟨11181, by rfl⟩) (B 22363 (by norm_num) ⟨11181, by rfl⟩ (by norm_num))
theorem R29821 : Reach 29821 := rs (se 3 (by rfl) ⟨5591, by rfl⟩) (B 11183 (by norm_num) ⟨5591, by rfl⟩ (by norm_num))
theorem R29825 : Reach 29825 := rs (se 2 (by rfl) ⟨11184, by rfl⟩) (B 22369 (by norm_num) ⟨11184, by rfl⟩ (by norm_num))
theorem R29829 : Reach 29829 := rs (se 4 (by rfl) ⟨2796, by rfl⟩) (B 5593 (by norm_num) ⟨2796, by rfl⟩ (by norm_num))
theorem R29833 : Reach 29833 := rs (se 2 (by rfl) ⟨11187, by rfl⟩) (B 22375 (by norm_num) ⟨11187, by rfl⟩ (by norm_num))
theorem R29837 : Reach 29837 := rs (se 3 (by rfl) ⟨5594, by rfl⟩) (B 11189 (by norm_num) ⟨5594, by rfl⟩ (by norm_num))
theorem R29841 : Reach 29841 := rs (se 2 (by rfl) ⟨11190, by rfl⟩) (B 22381 (by norm_num) ⟨11190, by rfl⟩ (by norm_num))
theorem R29845 : Reach 29845 := rs (se 6 (by rfl) ⟨699, by rfl⟩) (B 1399 (by norm_num) ⟨699, by rfl⟩ (by norm_num))
theorem R29849 : Reach 29849 := rs (se 2 (by rfl) ⟨11193, by rfl⟩) (B 22387 (by norm_num) ⟨11193, by rfl⟩ (by norm_num))
theorem R62621 : Reach 62621 := rs (se 3 (by rfl) ⟨11741, by rfl⟩) (B 23483 (by norm_num) ⟨11741, by rfl⟩ (by norm_num))
theorem R29853 : Reach 29853 := rs (se 3 (by rfl) ⟨5597, by rfl⟩) (B 11195 (by norm_num) ⟨5597, by rfl⟩ (by norm_num))
theorem R29857 : Reach 29857 := rs (se 2 (by rfl) ⟨11196, by rfl⟩) (B 22393 (by norm_num) ⟨11196, by rfl⟩ (by norm_num))
theorem R29861 : Reach 29861 := rs (se 4 (by rfl) ⟨2799, by rfl⟩) (B 5599 (by norm_num) ⟨2799, by rfl⟩ (by norm_num))
theorem R29865 : Reach 29865 := rs (se 2 (by rfl) ⟨11199, by rfl⟩) (B 22399 (by norm_num) ⟨11199, by rfl⟩ (by norm_num))
theorem R29869 : Reach 29869 := rs (se 3 (by rfl) ⟨5600, by rfl⟩) (B 11201 (by norm_num) ⟨5600, by rfl⟩ (by norm_num))
theorem R29873 : Reach 29873 := rs (se 2 (by rfl) ⟨11202, by rfl⟩) (B 22405 (by norm_num) ⟨11202, by rfl⟩ (by norm_num))
theorem R29877 : Reach 29877 := rs (se 5 (by rfl) ⟨1400, by rfl⟩) (B 2801 (by norm_num) ⟨1400, by rfl⟩ (by norm_num))
theorem R29881 : Reach 29881 := rs (se 2 (by rfl) ⟨11205, by rfl⟩) (B 22411 (by norm_num) ⟨11205, by rfl⟩ (by norm_num))
theorem R29885 : Reach 29885 := rs (se 3 (by rfl) ⟨5603, by rfl⟩) (B 11207 (by norm_num) ⟨5603, by rfl⟩ (by norm_num))
theorem R29889 : Reach 29889 := rs (se 2 (by rfl) ⟨11208, by rfl⟩) (B 22417 (by norm_num) ⟨11208, by rfl⟩ (by norm_num))
theorem R29893 : Reach 29893 := rs (se 4 (by rfl) ⟨2802, by rfl⟩) (B 5605 (by norm_num) ⟨2802, by rfl⟩ (by norm_num))
theorem R29897 : Reach 29897 := rs (se 2 (by rfl) ⟨11211, by rfl⟩) (B 22423 (by norm_num) ⟨11211, by rfl⟩ (by norm_num))
theorem R29901 : Reach 29901 := rs (se 3 (by rfl) ⟨5606, by rfl⟩) (B 11213 (by norm_num) ⟨5606, by rfl⟩ (by norm_num))
theorem R29905 : Reach 29905 := rs (se 2 (by rfl) ⟨11214, by rfl⟩) (B 22429 (by norm_num) ⟨11214, by rfl⟩ (by norm_num))
theorem R29909 : Reach 29909 := rs (se 7 (by rfl) ⟨350, by rfl⟩) (B 701 (by norm_num) ⟨350, by rfl⟩ (by norm_num))
theorem R128213 : Reach 128213 := rs (se 7 (by rfl) ⟨1502, by rfl⟩) (B 3005 (by norm_num) ⟨1502, by rfl⟩ (by norm_num))
theorem R29913 : Reach 29913 := rs (se 2 (by rfl) ⟨11217, by rfl⟩) (B 22435 (by norm_num) ⟨11217, by rfl⟩ (by norm_num))
theorem R29917 : Reach 29917 := rs (se 3 (by rfl) ⟨5609, by rfl⟩) (B 11219 (by norm_num) ⟨5609, by rfl⟩ (by norm_num))
theorem R29921 : Reach 29921 := rs (se 2 (by rfl) ⟨11220, by rfl⟩) (B 22441 (by norm_num) ⟨11220, by rfl⟩ (by norm_num))
theorem R62693 : Reach 62693 := rs (se 4 (by rfl) ⟨5877, by rfl⟩) (B 11755 (by norm_num) ⟨5877, by rfl⟩ (by norm_num))
theorem R29925 : Reach 29925 := rs (se 4 (by rfl) ⟨2805, by rfl⟩) (B 5611 (by norm_num) ⟨2805, by rfl⟩ (by norm_num))
theorem R29929 : Reach 29929 := rs (se 2 (by rfl) ⟨11223, by rfl⟩) (B 22447 (by norm_num) ⟨11223, by rfl⟩ (by norm_num))
theorem R29933 : Reach 29933 := rs (se 3 (by rfl) ⟨5612, by rfl⟩) (B 11225 (by norm_num) ⟨5612, by rfl⟩ (by norm_num))
theorem R29937 : Reach 29937 := rs (se 2 (by rfl) ⟨11226, by rfl⟩) (B 22453 (by norm_num) ⟨11226, by rfl⟩ (by norm_num))
theorem R29941 : Reach 29941 := rs (se 5 (by rfl) ⟨1403, by rfl⟩) (B 2807 (by norm_num) ⟨1403, by rfl⟩ (by norm_num))
theorem R29945 : Reach 29945 := rs (se 2 (by rfl) ⟨11229, by rfl⟩) (B 22459 (by norm_num) ⟨11229, by rfl⟩ (by norm_num))
theorem R29949 : Reach 29949 := rs (se 3 (by rfl) ⟨5615, by rfl⟩) (B 11231 (by norm_num) ⟨5615, by rfl⟩ (by norm_num))
theorem R29953 : Reach 29953 := rs (se 2 (by rfl) ⟨11232, by rfl⟩) (B 22465 (by norm_num) ⟨11232, by rfl⟩ (by norm_num))
theorem R29957 : Reach 29957 := rs (se 4 (by rfl) ⟨2808, by rfl⟩) (B 5617 (by norm_num) ⟨2808, by rfl⟩ (by norm_num))
theorem R29961 : Reach 29961 := rs (se 2 (by rfl) ⟨11235, by rfl⟩) (B 22471 (by norm_num) ⟨11235, by rfl⟩ (by norm_num))
theorem R29965 : Reach 29965 := rs (se 3 (by rfl) ⟨5618, by rfl⟩) (B 11237 (by norm_num) ⟨5618, by rfl⟩ (by norm_num))
theorem R29969 : Reach 29969 := rs (se 2 (by rfl) ⟨11238, by rfl⟩) (B 22477 (by norm_num) ⟨11238, by rfl⟩ (by norm_num))
theorem R29973 : Reach 29973 := rs (se 6 (by rfl) ⟨702, by rfl⟩) (B 1405 (by norm_num) ⟨702, by rfl⟩ (by norm_num))
theorem R29977 : Reach 29977 := rs (se 2 (by rfl) ⟨11241, by rfl⟩) (B 22483 (by norm_num) ⟨11241, by rfl⟩ (by norm_num))
theorem R29981 : Reach 29981 := rs (se 3 (by rfl) ⟨5621, by rfl⟩) (B 11243 (by norm_num) ⟨5621, by rfl⟩ (by norm_num))
theorem R29985 : Reach 29985 := rs (se 2 (by rfl) ⟨11244, by rfl⟩) (B 22489 (by norm_num) ⟨11244, by rfl⟩ (by norm_num))
theorem R95525 : Reach 95525 := rs (se 4 (by rfl) ⟨8955, by rfl⟩) (B 17911 (by norm_num) ⟨8955, by rfl⟩ (by norm_num))
theorem R29989 : Reach 29989 := rs (se 4 (by rfl) ⟨2811, by rfl⟩) (B 5623 (by norm_num) ⟨2811, by rfl⟩ (by norm_num))
theorem R29993 : Reach 29993 := rs (se 2 (by rfl) ⟨11247, by rfl⟩) (B 22495 (by norm_num) ⟨11247, by rfl⟩ (by norm_num))
theorem R62765 : Reach 62765 := rs (se 3 (by rfl) ⟨11768, by rfl⟩) (B 23537 (by norm_num) ⟨11768, by rfl⟩ (by norm_num))
theorem R29997 : Reach 29997 := rs (se 3 (by rfl) ⟨5624, by rfl⟩) (B 11249 (by norm_num) ⟨5624, by rfl⟩ (by norm_num))
theorem R30001 : Reach 30001 := rs (se 2 (by rfl) ⟨11250, by rfl⟩) (B 22501 (by norm_num) ⟨11250, by rfl⟩ (by norm_num))
theorem R30005 : Reach 30005 := rs (se 5 (by rfl) ⟨1406, by rfl⟩) (B 2813 (by norm_num) ⟨1406, by rfl⟩ (by norm_num))
theorem R30009 : Reach 30009 := rs (se 2 (by rfl) ⟨11253, by rfl⟩) (B 22507 (by norm_num) ⟨11253, by rfl⟩ (by norm_num))
theorem R30013 : Reach 30013 := rs (se 3 (by rfl) ⟨5627, by rfl⟩) (B 11255 (by norm_num) ⟨5627, by rfl⟩ (by norm_num))
theorem R30017 : Reach 30017 := rs (se 2 (by rfl) ⟨11256, by rfl⟩) (B 22513 (by norm_num) ⟨11256, by rfl⟩ (by norm_num))
theorem R30021 : Reach 30021 := rs (se 4 (by rfl) ⟨2814, by rfl⟩) (B 5629 (by norm_num) ⟨2814, by rfl⟩ (by norm_num))
theorem R30025 : Reach 30025 := rs (se 2 (by rfl) ⟨11259, by rfl⟩) (B 22519 (by norm_num) ⟨11259, by rfl⟩ (by norm_num))
theorem R30029 : Reach 30029 := rs (se 3 (by rfl) ⟨5630, by rfl⟩) (B 11261 (by norm_num) ⟨5630, by rfl⟩ (by norm_num))
theorem R30033 : Reach 30033 := rs (se 2 (by rfl) ⟨11262, by rfl⟩) (B 22525 (by norm_num) ⟨11262, by rfl⟩ (by norm_num))
theorem R30037 : Reach 30037 := rs (se 13 (by rfl) ⟨5, by rfl⟩) (B 11 (by norm_num) ⟨5, by rfl⟩ (by norm_num))
theorem R30041 : Reach 30041 := rs (se 2 (by rfl) ⟨11265, by rfl⟩) (B 22531 (by norm_num) ⟨11265, by rfl⟩ (by norm_num))
theorem R30045 : Reach 30045 := rs (se 3 (by rfl) ⟨5633, by rfl⟩) (B 11267 (by norm_num) ⟨5633, by rfl⟩ (by norm_num))
theorem R30049 : Reach 30049 := rs (se 2 (by rfl) ⟨11268, by rfl⟩) (B 22537 (by norm_num) ⟨11268, by rfl⟩ (by norm_num))
theorem R30053 : Reach 30053 := rs (se 4 (by rfl) ⟨2817, by rfl⟩) (B 5635 (by norm_num) ⟨2817, by rfl⟩ (by norm_num))
theorem R30057 : Reach 30057 := rs (se 2 (by rfl) ⟨11271, by rfl⟩) (B 22543 (by norm_num) ⟨11271, by rfl⟩ (by norm_num))
theorem R30061 : Reach 30061 := rs (se 3 (by rfl) ⟨5636, by rfl⟩) (B 11273 (by norm_num) ⟨5636, by rfl⟩ (by norm_num))
theorem R30065 : Reach 30065 := rs (se 2 (by rfl) ⟨11274, by rfl⟩) (B 22549 (by norm_num) ⟨11274, by rfl⟩ (by norm_num))
theorem R62837 : Reach 62837 := rs (se 5 (by rfl) ⟨2945, by rfl⟩) (B 5891 (by norm_num) ⟨2945, by rfl⟩ (by norm_num))
theorem R30069 : Reach 30069 := rs (se 5 (by rfl) ⟨1409, by rfl⟩) (B 2819 (by norm_num) ⟨1409, by rfl⟩ (by norm_num))
theorem R30073 : Reach 30073 := rs (se 2 (by rfl) ⟨11277, by rfl⟩) (B 22555 (by norm_num) ⟨11277, by rfl⟩ (by norm_num))
theorem R30077 : Reach 30077 := rs (se 3 (by rfl) ⟨5639, by rfl⟩) (B 11279 (by norm_num) ⟨5639, by rfl⟩ (by norm_num))
theorem R30081 : Reach 30081 := rs (se 2 (by rfl) ⟨11280, by rfl⟩) (B 22561 (by norm_num) ⟨11280, by rfl⟩ (by norm_num))
theorem R30085 : Reach 30085 := rs (se 4 (by rfl) ⟨2820, by rfl⟩) (B 5641 (by norm_num) ⟨2820, by rfl⟩ (by norm_num))
theorem R30089 : Reach 30089 := rs (se 2 (by rfl) ⟨11283, by rfl⟩) (B 22567 (by norm_num) ⟨11283, by rfl⟩ (by norm_num))
theorem R30093 : Reach 30093 := rs (se 3 (by rfl) ⟨5642, by rfl⟩) (B 11285 (by norm_num) ⟨5642, by rfl⟩ (by norm_num))
theorem R30097 : Reach 30097 := rs (se 2 (by rfl) ⟨11286, by rfl⟩) (B 22573 (by norm_num) ⟨11286, by rfl⟩ (by norm_num))
theorem R62869 : Reach 62869 := rs (se 6 (by rfl) ⟨1473, by rfl⟩) (B 2947 (by norm_num) ⟨1473, by rfl⟩ (by norm_num))
theorem R30101 : Reach 30101 := rs (se 6 (by rfl) ⟨705, by rfl⟩) (B 1411 (by norm_num) ⟨705, by rfl⟩ (by norm_num))
theorem R30105 : Reach 30105 := rs (se 2 (by rfl) ⟨11289, by rfl⟩) (B 22579 (by norm_num) ⟨11289, by rfl⟩ (by norm_num))
theorem R30109 : Reach 30109 := rs (se 3 (by rfl) ⟨5645, by rfl⟩) (B 11291 (by norm_num) ⟨5645, by rfl⟩ (by norm_num))
theorem R30113 : Reach 30113 := rs (se 2 (by rfl) ⟨11292, by rfl⟩) (B 22585 (by norm_num) ⟨11292, by rfl⟩ (by norm_num))
theorem R30117 : Reach 30117 := rs (se 4 (by rfl) ⟨2823, by rfl⟩) (B 5647 (by norm_num) ⟨2823, by rfl⟩ (by norm_num))
theorem R30121 : Reach 30121 := rs (se 2 (by rfl) ⟨11295, by rfl⟩) (B 22591 (by norm_num) ⟨11295, by rfl⟩ (by norm_num))
theorem R30125 : Reach 30125 := rs (se 3 (by rfl) ⟨5648, by rfl⟩) (B 11297 (by norm_num) ⟨5648, by rfl⟩ (by norm_num))
theorem R30129 : Reach 30129 := rs (se 2 (by rfl) ⟨11298, by rfl⟩) (B 22597 (by norm_num) ⟨11298, by rfl⟩ (by norm_num))
theorem R30133 : Reach 30133 := rs (se 5 (by rfl) ⟨1412, by rfl⟩) (B 2825 (by norm_num) ⟨1412, by rfl⟩ (by norm_num))
theorem R30137 : Reach 30137 := rs (se 2 (by rfl) ⟨11301, by rfl⟩) (B 22603 (by norm_num) ⟨11301, by rfl⟩ (by norm_num))
theorem R62909 : Reach 62909 := rs (se 3 (by rfl) ⟨11795, by rfl⟩) (B 23591 (by norm_num) ⟨11795, by rfl⟩ (by norm_num))
theorem R30141 : Reach 30141 := rs (se 3 (by rfl) ⟨5651, by rfl⟩) (B 11303 (by norm_num) ⟨5651, by rfl⟩ (by norm_num))
theorem R30145 : Reach 30145 := rs (se 2 (by rfl) ⟨11304, by rfl⟩) (B 22609 (by norm_num) ⟨11304, by rfl⟩ (by norm_num))
theorem R30149 : Reach 30149 := rs (se 4 (by rfl) ⟨2826, by rfl⟩) (B 5653 (by norm_num) ⟨2826, by rfl⟩ (by norm_num))
theorem R30153 : Reach 30153 := rs (se 2 (by rfl) ⟨11307, by rfl⟩) (B 22615 (by norm_num) ⟨11307, by rfl⟩ (by norm_num))
theorem R30157 : Reach 30157 := rs (se 3 (by rfl) ⟨5654, by rfl⟩) (B 11309 (by norm_num) ⟨5654, by rfl⟩ (by norm_num))
theorem R30161 : Reach 30161 := rs (se 2 (by rfl) ⟨11310, by rfl⟩) (B 22621 (by norm_num) ⟨11310, by rfl⟩ (by norm_num))
theorem R30165 : Reach 30165 := rs (se 7 (by rfl) ⟨353, by rfl⟩) (B 707 (by norm_num) ⟨353, by rfl⟩ (by norm_num))
theorem R30169 : Reach 30169 := rs (se 2 (by rfl) ⟨11313, by rfl⟩) (B 22627 (by norm_num) ⟨11313, by rfl⟩ (by norm_num))
theorem R30173 : Reach 30173 := rs (se 3 (by rfl) ⟨5657, by rfl⟩) (B 11315 (by norm_num) ⟨5657, by rfl⟩ (by norm_num))
theorem R30177 : Reach 30177 := rs (se 2 (by rfl) ⟨11316, by rfl⟩) (B 22633 (by norm_num) ⟨11316, by rfl⟩ (by norm_num))
theorem R30181 : Reach 30181 := rs (se 4 (by rfl) ⟨2829, by rfl⟩) (B 5659 (by norm_num) ⟨2829, by rfl⟩ (by norm_num))
theorem R30185 : Reach 30185 := rs (se 2 (by rfl) ⟨11319, by rfl⟩) (B 22639 (by norm_num) ⟨11319, by rfl⟩ (by norm_num))
theorem R30189 : Reach 30189 := rs (se 3 (by rfl) ⟨5660, by rfl⟩) (B 11321 (by norm_num) ⟨5660, by rfl⟩ (by norm_num))
theorem R30193 : Reach 30193 := rs (se 2 (by rfl) ⟨11322, by rfl⟩) (B 22645 (by norm_num) ⟨11322, by rfl⟩ (by norm_num))
theorem R30197 : Reach 30197 := rs (se 5 (by rfl) ⟨1415, by rfl⟩) (B 2831 (by norm_num) ⟨1415, by rfl⟩ (by norm_num))
theorem R30201 : Reach 30201 := rs (se 2 (by rfl) ⟨11325, by rfl⟩) (B 22651 (by norm_num) ⟨11325, by rfl⟩ (by norm_num))
theorem R30205 : Reach 30205 := rs (se 3 (by rfl) ⟨5663, by rfl⟩) (B 11327 (by norm_num) ⟨5663, by rfl⟩ (by norm_num))
theorem R30209 : Reach 30209 := rs (se 2 (by rfl) ⟨11328, by rfl⟩) (B 22657 (by norm_num) ⟨11328, by rfl⟩ (by norm_num))
theorem R62981 : Reach 62981 := rs (se 4 (by rfl) ⟨5904, by rfl⟩) (B 11809 (by norm_num) ⟨5904, by rfl⟩ (by norm_num))
theorem R30213 : Reach 30213 := rs (se 4 (by rfl) ⟨2832, by rfl⟩) (B 5665 (by norm_num) ⟨2832, by rfl⟩ (by norm_num))
theorem R30217 : Reach 30217 := rs (se 2 (by rfl) ⟨11331, by rfl⟩) (B 22663 (by norm_num) ⟨11331, by rfl⟩ (by norm_num))
theorem R30221 : Reach 30221 := rs (se 3 (by rfl) ⟨5666, by rfl⟩) (B 11333 (by norm_num) ⟨5666, by rfl⟩ (by norm_num))
theorem R30225 : Reach 30225 := rs (se 2 (by rfl) ⟨11334, by rfl⟩) (B 22669 (by norm_num) ⟨11334, by rfl⟩ (by norm_num))
theorem R30229 : Reach 30229 := rs (se 6 (by rfl) ⟨708, by rfl⟩) (B 1417 (by norm_num) ⟨708, by rfl⟩ (by norm_num))
theorem R30233 : Reach 30233 := rs (se 2 (by rfl) ⟨11337, by rfl⟩) (B 22675 (by norm_num) ⟨11337, by rfl⟩ (by norm_num))
theorem R30237 : Reach 30237 := rs (se 3 (by rfl) ⟨5669, by rfl⟩) (B 11339 (by norm_num) ⟨5669, by rfl⟩ (by norm_num))
theorem R30241 : Reach 30241 := rs (se 2 (by rfl) ⟨11340, by rfl⟩) (B 22681 (by norm_num) ⟨11340, by rfl⟩ (by norm_num))
theorem R63013 : Reach 63013 := rs (se 4 (by rfl) ⟨5907, by rfl⟩) (B 11815 (by norm_num) ⟨5907, by rfl⟩ (by norm_num))
theorem R30245 : Reach 30245 := rs (se 4 (by rfl) ⟨2835, by rfl⟩) (B 5671 (by norm_num) ⟨2835, by rfl⟩ (by norm_num))
theorem R30249 : Reach 30249 := rs (se 2 (by rfl) ⟨11343, by rfl⟩) (B 22687 (by norm_num) ⟨11343, by rfl⟩ (by norm_num))
theorem R30253 : Reach 30253 := rs (se 3 (by rfl) ⟨5672, by rfl⟩) (B 11345 (by norm_num) ⟨5672, by rfl⟩ (by norm_num))
theorem R30257 : Reach 30257 := rs (se 2 (by rfl) ⟨11346, by rfl⟩) (B 22693 (by norm_num) ⟨11346, by rfl⟩ (by norm_num))
theorem R30261 : Reach 30261 := rs (se 5 (by rfl) ⟨1418, by rfl⟩) (B 2837 (by norm_num) ⟨1418, by rfl⟩ (by norm_num))
theorem R30265 : Reach 30265 := rs (se 2 (by rfl) ⟨11349, by rfl⟩) (B 22699 (by norm_num) ⟨11349, by rfl⟩ (by norm_num))
theorem R30269 : Reach 30269 := rs (se 3 (by rfl) ⟨5675, by rfl⟩) (B 11351 (by norm_num) ⟨5675, by rfl⟩ (by norm_num))
theorem R30273 : Reach 30273 := rs (se 2 (by rfl) ⟨11352, by rfl⟩) (B 22705 (by norm_num) ⟨11352, by rfl⟩ (by norm_num))
theorem R30277 : Reach 30277 := rs (se 4 (by rfl) ⟨2838, by rfl⟩) (B 5677 (by norm_num) ⟨2838, by rfl⟩ (by norm_num))
theorem R30281 : Reach 30281 := rs (se 2 (by rfl) ⟨11355, by rfl⟩) (B 22711 (by norm_num) ⟨11355, by rfl⟩ (by norm_num))
theorem R63053 : Reach 63053 := rs (se 3 (by rfl) ⟨11822, by rfl⟩) (B 23645 (by norm_num) ⟨11822, by rfl⟩ (by norm_num))
theorem R30285 : Reach 30285 := rs (se 3 (by rfl) ⟨5678, by rfl⟩) (B 11357 (by norm_num) ⟨5678, by rfl⟩ (by norm_num))
theorem R30289 : Reach 30289 := rs (se 2 (by rfl) ⟨11358, by rfl⟩) (B 22717 (by norm_num) ⟨11358, by rfl⟩ (by norm_num))
theorem R1799765 : Reach 1799765 := rs (se 8 (by rfl) ⟨10545, by rfl⟩) (B 21091 (by norm_num) ⟨10545, by rfl⟩ (by norm_num))
theorem R30293 : Reach 30293 := rs (se 8 (by rfl) ⟨177, by rfl⟩) (B 355 (by norm_num) ⟨177, by rfl⟩ (by norm_num))
theorem R30297 : Reach 30297 := rs (se 2 (by rfl) ⟨11361, by rfl⟩) (B 22723 (by norm_num) ⟨11361, by rfl⟩ (by norm_num))
theorem R30301 : Reach 30301 := rs (se 3 (by rfl) ⟨5681, by rfl⟩) (B 11363 (by norm_num) ⟨5681, by rfl⟩ (by norm_num))
theorem R30305 : Reach 30305 := rs (se 2 (by rfl) ⟨11364, by rfl⟩) (B 22729 (by norm_num) ⟨11364, by rfl⟩ (by norm_num))
theorem R30309 : Reach 30309 := rs (se 4 (by rfl) ⟨2841, by rfl⟩) (B 5683 (by norm_num) ⟨2841, by rfl⟩ (by norm_num))
theorem R30313 : Reach 30313 := rs (se 2 (by rfl) ⟨11367, by rfl⟩) (B 22735 (by norm_num) ⟨11367, by rfl⟩ (by norm_num))
theorem R30317 : Reach 30317 := rs (se 3 (by rfl) ⟨5684, by rfl⟩) (B 11369 (by norm_num) ⟨5684, by rfl⟩ (by norm_num))
theorem R30321 : Reach 30321 := rs (se 2 (by rfl) ⟨11370, by rfl⟩) (B 22741 (by norm_num) ⟨11370, by rfl⟩ (by norm_num))
theorem R30325 : Reach 30325 := rs (se 5 (by rfl) ⟨1421, by rfl⟩) (B 2843 (by norm_num) ⟨1421, by rfl⟩ (by norm_num))
theorem R30329 : Reach 30329 := rs (se 2 (by rfl) ⟨11373, by rfl⟩) (B 22747 (by norm_num) ⟨11373, by rfl⟩ (by norm_num))
theorem R30333 : Reach 30333 := rs (se 3 (by rfl) ⟨5687, by rfl⟩) (B 11375 (by norm_num) ⟨5687, by rfl⟩ (by norm_num))
theorem R30337 : Reach 30337 := rs (se 2 (by rfl) ⟨11376, by rfl⟩) (B 22753 (by norm_num) ⟨11376, by rfl⟩ (by norm_num))
theorem R30341 : Reach 30341 := rs (se 4 (by rfl) ⟨2844, by rfl⟩) (B 5689 (by norm_num) ⟨2844, by rfl⟩ (by norm_num))
theorem R30345 : Reach 30345 := rs (se 2 (by rfl) ⟨11379, by rfl⟩) (B 22759 (by norm_num) ⟨11379, by rfl⟩ (by norm_num))
theorem R30349 : Reach 30349 := rs (se 3 (by rfl) ⟨5690, by rfl⟩) (B 11381 (by norm_num) ⟨5690, by rfl⟩ (by norm_num))
theorem R30353 : Reach 30353 := rs (se 2 (by rfl) ⟨11382, by rfl⟩) (B 22765 (by norm_num) ⟨11382, by rfl⟩ (by norm_num))
theorem R63125 : Reach 63125 := rs (se 6 (by rfl) ⟨1479, by rfl⟩) (B 2959 (by norm_num) ⟨1479, by rfl⟩ (by norm_num))
theorem R30357 : Reach 30357 := rs (se 6 (by rfl) ⟨711, by rfl⟩) (B 1423 (by norm_num) ⟨711, by rfl⟩ (by norm_num))
theorem R30361 : Reach 30361 := rs (se 2 (by rfl) ⟨11385, by rfl⟩) (B 22771 (by norm_num) ⟨11385, by rfl⟩ (by norm_num))
theorem R30365 : Reach 30365 := rs (se 3 (by rfl) ⟨5693, by rfl⟩) (B 11387 (by norm_num) ⟨5693, by rfl⟩ (by norm_num))
theorem R30369 : Reach 30369 := rs (se 2 (by rfl) ⟨11388, by rfl⟩) (B 22777 (by norm_num) ⟨11388, by rfl⟩ (by norm_num))
theorem R30373 : Reach 30373 := rs (se 4 (by rfl) ⟨2847, by rfl⟩) (B 5695 (by norm_num) ⟨2847, by rfl⟩ (by norm_num))
theorem R30377 : Reach 30377 := rs (se 2 (by rfl) ⟨11391, by rfl⟩) (B 22783 (by norm_num) ⟨11391, by rfl⟩ (by norm_num))
theorem R30381 : Reach 30381 := rs (se 3 (by rfl) ⟨5696, by rfl⟩) (B 11393 (by norm_num) ⟨5696, by rfl⟩ (by norm_num))
theorem R30385 : Reach 30385 := rs (se 2 (by rfl) ⟨11394, by rfl⟩) (B 22789 (by norm_num) ⟨11394, by rfl⟩ (by norm_num))
theorem R30389 : Reach 30389 := rs (se 5 (by rfl) ⟨1424, by rfl⟩) (B 2849 (by norm_num) ⟨1424, by rfl⟩ (by norm_num))
theorem R30393 : Reach 30393 := rs (se 2 (by rfl) ⟨11397, by rfl⟩) (B 22795 (by norm_num) ⟨11397, by rfl⟩ (by norm_num))
theorem R30397 : Reach 30397 := rs (se 3 (by rfl) ⟨5699, by rfl⟩) (B 11399 (by norm_num) ⟨5699, by rfl⟩ (by norm_num))
theorem R30401 : Reach 30401 := rs (se 2 (by rfl) ⟨11400, by rfl⟩) (B 22801 (by norm_num) ⟨11400, by rfl⟩ (by norm_num))
theorem R95941 : Reach 95941 := rs (se 4 (by rfl) ⟨8994, by rfl⟩) (B 17989 (by norm_num) ⟨8994, by rfl⟩ (by norm_num))
theorem R30405 : Reach 30405 := rs (se 4 (by rfl) ⟨2850, by rfl⟩) (B 5701 (by norm_num) ⟨2850, by rfl⟩ (by norm_num))
theorem R30409 : Reach 30409 := rs (se 2 (by rfl) ⟨11403, by rfl⟩) (B 22807 (by norm_num) ⟨11403, by rfl⟩ (by norm_num))
theorem R30413 : Reach 30413 := rs (se 3 (by rfl) ⟨5702, by rfl⟩) (B 11405 (by norm_num) ⟨5702, by rfl⟩ (by norm_num))
theorem R30417 : Reach 30417 := rs (se 2 (by rfl) ⟨11406, by rfl⟩) (B 22813 (by norm_num) ⟨11406, by rfl⟩ (by norm_num))
theorem R95957 : Reach 95957 := rs (se 7 (by rfl) ⟨1124, by rfl⟩) (B 2249 (by norm_num) ⟨1124, by rfl⟩ (by norm_num))
theorem R30421 : Reach 30421 := rs (se 7 (by rfl) ⟨356, by rfl⟩) (B 713 (by norm_num) ⟨356, by rfl⟩ (by norm_num))
theorem R30425 : Reach 30425 := rs (se 2 (by rfl) ⟨11409, by rfl⟩) (B 22819 (by norm_num) ⟨11409, by rfl⟩ (by norm_num))
theorem R63197 : Reach 63197 := rs (se 3 (by rfl) ⟨11849, by rfl⟩) (B 23699 (by norm_num) ⟨11849, by rfl⟩ (by norm_num))
theorem R30429 : Reach 30429 := rs (se 3 (by rfl) ⟨5705, by rfl⟩) (B 11411 (by norm_num) ⟨5705, by rfl⟩ (by norm_num))
theorem R30433 : Reach 30433 := rs (se 2 (by rfl) ⟨11412, by rfl⟩) (B 22825 (by norm_num) ⟨11412, by rfl⟩ (by norm_num))
theorem R30437 : Reach 30437 := rs (se 4 (by rfl) ⟨2853, by rfl⟩) (B 5707 (by norm_num) ⟨2853, by rfl⟩ (by norm_num))
theorem R30441 : Reach 30441 := rs (se 2 (by rfl) ⟨11415, by rfl⟩) (B 22831 (by norm_num) ⟨11415, by rfl⟩ (by norm_num))
theorem R30445 : Reach 30445 := rs (se 3 (by rfl) ⟨5708, by rfl⟩) (B 11417 (by norm_num) ⟨5708, by rfl⟩ (by norm_num))
theorem R30449 : Reach 30449 := rs (se 2 (by rfl) ⟨11418, by rfl⟩) (B 22837 (by norm_num) ⟨11418, by rfl⟩ (by norm_num))
theorem R30453 : Reach 30453 := rs (se 5 (by rfl) ⟨1427, by rfl⟩) (B 2855 (by norm_num) ⟨1427, by rfl⟩ (by norm_num))
theorem R30457 : Reach 30457 := rs (se 2 (by rfl) ⟨11421, by rfl⟩) (B 22843 (by norm_num) ⟨11421, by rfl⟩ (by norm_num))
theorem R30461 : Reach 30461 := rs (se 3 (by rfl) ⟨5711, by rfl⟩) (B 11423 (by norm_num) ⟨5711, by rfl⟩ (by norm_num))
theorem R30465 : Reach 30465 := rs (se 2 (by rfl) ⟨11424, by rfl⟩) (B 22849 (by norm_num) ⟨11424, by rfl⟩ (by norm_num))
theorem R30469 : Reach 30469 := rs (se 4 (by rfl) ⟨2856, by rfl⟩) (B 5713 (by norm_num) ⟨2856, by rfl⟩ (by norm_num))
theorem R30473 : Reach 30473 := rs (se 2 (by rfl) ⟨11427, by rfl⟩) (B 22855 (by norm_num) ⟨11427, by rfl⟩ (by norm_num))
theorem R30477 : Reach 30477 := rs (se 3 (by rfl) ⟨5714, by rfl⟩) (B 11429 (by norm_num) ⟨5714, by rfl⟩ (by norm_num))
theorem R30481 : Reach 30481 := rs (se 2 (by rfl) ⟨11430, by rfl⟩) (B 22861 (by norm_num) ⟨11430, by rfl⟩ (by norm_num))
theorem R30485 : Reach 30485 := rs (se 6 (by rfl) ⟨714, by rfl⟩) (B 1429 (by norm_num) ⟨714, by rfl⟩ (by norm_num))
theorem R30489 : Reach 30489 := rs (se 2 (by rfl) ⟨11433, by rfl⟩) (B 22867 (by norm_num) ⟨11433, by rfl⟩ (by norm_num))
theorem R30493 : Reach 30493 := rs (se 3 (by rfl) ⟨5717, by rfl⟩) (B 11435 (by norm_num) ⟨5717, by rfl⟩ (by norm_num))
theorem R30497 : Reach 30497 := rs (se 2 (by rfl) ⟨11436, by rfl⟩) (B 22873 (by norm_num) ⟨11436, by rfl⟩ (by norm_num))
theorem R63269 : Reach 63269 := rs (se 4 (by rfl) ⟨5931, by rfl⟩) (B 11863 (by norm_num) ⟨5931, by rfl⟩ (by norm_num))
theorem R30501 : Reach 30501 := rs (se 4 (by rfl) ⟨2859, by rfl⟩) (B 5719 (by norm_num) ⟨2859, by rfl⟩ (by norm_num))
theorem R30505 : Reach 30505 := rs (se 2 (by rfl) ⟨11439, by rfl⟩) (B 22879 (by norm_num) ⟨11439, by rfl⟩ (by norm_num))
theorem R30509 : Reach 30509 := rs (se 3 (by rfl) ⟨5720, by rfl⟩) (B 11441 (by norm_num) ⟨5720, by rfl⟩ (by norm_num))
theorem R30513 : Reach 30513 := rs (se 2 (by rfl) ⟨11442, by rfl⟩) (B 22885 (by norm_num) ⟨11442, by rfl⟩ (by norm_num))
theorem R30517 : Reach 30517 := rs (se 5 (by rfl) ⟨1430, by rfl⟩) (B 2861 (by norm_num) ⟨1430, by rfl⟩ (by norm_num))
theorem R30521 : Reach 30521 := rs (se 2 (by rfl) ⟨11445, by rfl⟩) (B 22891 (by norm_num) ⟨11445, by rfl⟩ (by norm_num))
theorem R30525 : Reach 30525 := rs (se 3 (by rfl) ⟨5723, by rfl⟩) (B 11447 (by norm_num) ⟨5723, by rfl⟩ (by norm_num))
theorem R30529 : Reach 30529 := rs (se 2 (by rfl) ⟨11448, by rfl⟩) (B 22897 (by norm_num) ⟨11448, by rfl⟩ (by norm_num))
theorem R30533 : Reach 30533 := rs (se 4 (by rfl) ⟨2862, by rfl⟩) (B 5725 (by norm_num) ⟨2862, by rfl⟩ (by norm_num))
theorem R30537 : Reach 30537 := rs (se 2 (by rfl) ⟨11451, by rfl⟩) (B 22903 (by norm_num) ⟨11451, by rfl⟩ (by norm_num))
theorem R30541 : Reach 30541 := rs (se 3 (by rfl) ⟨5726, by rfl⟩) (B 11453 (by norm_num) ⟨5726, by rfl⟩ (by norm_num))
theorem R30545 : Reach 30545 := rs (se 2 (by rfl) ⟨11454, by rfl⟩) (B 22909 (by norm_num) ⟨11454, by rfl⟩ (by norm_num))
theorem R30549 : Reach 30549 := rs (se 9 (by rfl) ⟨89, by rfl⟩) (B 179 (by norm_num) ⟨89, by rfl⟩ (by norm_num))
theorem R30553 : Reach 30553 := rs (se 2 (by rfl) ⟨11457, by rfl⟩) (B 22915 (by norm_num) ⟨11457, by rfl⟩ (by norm_num))
theorem R30557 : Reach 30557 := rs (se 3 (by rfl) ⟨5729, by rfl⟩) (B 11459 (by norm_num) ⟨5729, by rfl⟩ (by norm_num))
theorem R30561 : Reach 30561 := rs (se 2 (by rfl) ⟨11460, by rfl⟩) (B 22921 (by norm_num) ⟨11460, by rfl⟩ (by norm_num))
theorem R30565 : Reach 30565 := rs (se 4 (by rfl) ⟨2865, by rfl⟩) (B 5731 (by norm_num) ⟨2865, by rfl⟩ (by norm_num))
theorem R30569 : Reach 30569 := rs (se 2 (by rfl) ⟨11463, by rfl⟩) (B 22927 (by norm_num) ⟨11463, by rfl⟩ (by norm_num))
theorem R63341 : Reach 63341 := rs (se 3 (by rfl) ⟨11876, by rfl⟩) (B 23753 (by norm_num) ⟨11876, by rfl⟩ (by norm_num))
theorem R30573 : Reach 30573 := rs (se 3 (by rfl) ⟨5732, by rfl⟩) (B 11465 (by norm_num) ⟨5732, by rfl⟩ (by norm_num))
theorem R30577 : Reach 30577 := rs (se 2 (by rfl) ⟨11466, by rfl⟩) (B 22933 (by norm_num) ⟨11466, by rfl⟩ (by norm_num))
theorem R63349 : Reach 63349 := rs (se 5 (by rfl) ⟨2969, by rfl⟩) (B 5939 (by norm_num) ⟨2969, by rfl⟩ (by norm_num))
theorem R30581 : Reach 30581 := rs (se 5 (by rfl) ⟨1433, by rfl⟩) (B 2867 (by norm_num) ⟨1433, by rfl⟩ (by norm_num))
theorem R30585 : Reach 30585 := rs (se 2 (by rfl) ⟨11469, by rfl⟩) (B 22939 (by norm_num) ⟨11469, by rfl⟩ (by norm_num))
theorem R30589 : Reach 30589 := rs (se 3 (by rfl) ⟨5735, by rfl⟩) (B 11471 (by norm_num) ⟨5735, by rfl⟩ (by norm_num))
theorem R30593 : Reach 30593 := rs (se 2 (by rfl) ⟨11472, by rfl⟩) (B 22945 (by norm_num) ⟨11472, by rfl⟩ (by norm_num))
theorem R30597 : Reach 30597 := rs (se 4 (by rfl) ⟨2868, by rfl⟩) (B 5737 (by norm_num) ⟨2868, by rfl⟩ (by norm_num))
theorem R30601 : Reach 30601 := rs (se 2 (by rfl) ⟨11475, by rfl⟩) (B 22951 (by norm_num) ⟨11475, by rfl⟩ (by norm_num))
theorem R30605 : Reach 30605 := rs (se 3 (by rfl) ⟨5738, by rfl⟩) (B 11477 (by norm_num) ⟨5738, by rfl⟩ (by norm_num))
theorem R30609 : Reach 30609 := rs (se 2 (by rfl) ⟨11478, by rfl⟩) (B 22957 (by norm_num) ⟨11478, by rfl⟩ (by norm_num))
theorem R30613 : Reach 30613 := rs (se 6 (by rfl) ⟨717, by rfl⟩) (B 1435 (by norm_num) ⟨717, by rfl⟩ (by norm_num))
theorem R30617 : Reach 30617 := rs (se 2 (by rfl) ⟨11481, by rfl⟩) (B 22963 (by norm_num) ⟨11481, by rfl⟩ (by norm_num))
theorem R63389 : Reach 63389 := rs (se 3 (by rfl) ⟨11885, by rfl⟩) (B 23771 (by norm_num) ⟨11885, by rfl⟩ (by norm_num))
theorem R30621 : Reach 30621 := rs (se 3 (by rfl) ⟨5741, by rfl⟩) (B 11483 (by norm_num) ⟨5741, by rfl⟩ (by norm_num))
theorem R30625 : Reach 30625 := rs (se 2 (by rfl) ⟨11484, by rfl⟩) (B 22969 (by norm_num) ⟨11484, by rfl⟩ (by norm_num))
theorem R30629 : Reach 30629 := rs (se 4 (by rfl) ⟨2871, by rfl⟩) (B 5743 (by norm_num) ⟨2871, by rfl⟩ (by norm_num))
theorem R30633 : Reach 30633 := rs (se 2 (by rfl) ⟨11487, by rfl⟩) (B 22975 (by norm_num) ⟨11487, by rfl⟩ (by norm_num))
theorem R30637 : Reach 30637 := rs (se 3 (by rfl) ⟨5744, by rfl⟩) (B 11489 (by norm_num) ⟨5744, by rfl⟩ (by norm_num))
theorem R30641 : Reach 30641 := rs (se 2 (by rfl) ⟨11490, by rfl⟩) (B 22981 (by norm_num) ⟨11490, by rfl⟩ (by norm_num))
theorem R63413 : Reach 63413 := rs (se 5 (by rfl) ⟨2972, by rfl⟩) (B 5945 (by norm_num) ⟨2972, by rfl⟩ (by norm_num))
theorem R30645 : Reach 30645 := rs (se 5 (by rfl) ⟨1436, by rfl⟩) (B 2873 (by norm_num) ⟨1436, by rfl⟩ (by norm_num))
theorem R30649 : Reach 30649 := rs (se 2 (by rfl) ⟨11493, by rfl⟩) (B 22987 (by norm_num) ⟨11493, by rfl⟩ (by norm_num))
theorem R30653 : Reach 30653 := rs (se 3 (by rfl) ⟨5747, by rfl⟩) (B 11495 (by norm_num) ⟨5747, by rfl⟩ (by norm_num))
theorem R30657 : Reach 30657 := rs (se 2 (by rfl) ⟨11496, by rfl⟩) (B 22993 (by norm_num) ⟨11496, by rfl⟩ (by norm_num))
theorem R128965 : Reach 128965 := rs (se 4 (by rfl) ⟨12090, by rfl⟩) (B 24181 (by norm_num) ⟨12090, by rfl⟩ (by norm_num))
theorem R30661 : Reach 30661 := rs (se 4 (by rfl) ⟨2874, by rfl⟩) (B 5749 (by norm_num) ⟨2874, by rfl⟩ (by norm_num))
theorem R30665 : Reach 30665 := rs (se 2 (by rfl) ⟨11499, by rfl⟩) (B 22999 (by norm_num) ⟨11499, by rfl⟩ (by norm_num))
theorem R30669 : Reach 30669 := rs (se 3 (by rfl) ⟨5750, by rfl⟩) (B 11501 (by norm_num) ⟨5750, by rfl⟩ (by norm_num))
theorem R30673 : Reach 30673 := rs (se 2 (by rfl) ⟨11502, by rfl⟩) (B 23005 (by norm_num) ⟨11502, by rfl⟩ (by norm_num))
theorem R30677 : Reach 30677 := rs (se 7 (by rfl) ⟨359, by rfl⟩) (B 719 (by norm_num) ⟨359, by rfl⟩ (by norm_num))
theorem R30681 : Reach 30681 := rs (se 2 (by rfl) ⟨11505, by rfl⟩) (B 23011 (by norm_num) ⟨11505, by rfl⟩ (by norm_num))
theorem R30685 : Reach 30685 := rs (se 3 (by rfl) ⟨5753, by rfl⟩) (B 11507 (by norm_num) ⟨5753, by rfl⟩ (by norm_num))
theorem R30689 : Reach 30689 := rs (se 2 (by rfl) ⟨11508, by rfl⟩) (B 23017 (by norm_num) ⟨11508, by rfl⟩ (by norm_num))
theorem R30693 : Reach 30693 := rs (se 4 (by rfl) ⟨2877, by rfl⟩) (B 5755 (by norm_num) ⟨2877, by rfl⟩ (by norm_num))
theorem R30697 : Reach 30697 := rs (se 2 (by rfl) ⟨11511, by rfl⟩) (B 23023 (by norm_num) ⟨11511, by rfl⟩ (by norm_num))
theorem R30701 : Reach 30701 := rs (se 3 (by rfl) ⟨5756, by rfl⟩) (B 11513 (by norm_num) ⟨5756, by rfl⟩ (by norm_num))
theorem R30705 : Reach 30705 := rs (se 2 (by rfl) ⟨11514, by rfl⟩) (B 23029 (by norm_num) ⟨11514, by rfl⟩ (by norm_num))
theorem R30709 : Reach 30709 := rs (se 5 (by rfl) ⟨1439, by rfl⟩) (B 2879 (by norm_num) ⟨1439, by rfl⟩ (by norm_num))
theorem R30713 : Reach 30713 := rs (se 2 (by rfl) ⟨11517, by rfl⟩) (B 23035 (by norm_num) ⟨11517, by rfl⟩ (by norm_num))
theorem R63485 : Reach 63485 := rs (se 3 (by rfl) ⟨11903, by rfl⟩) (B 23807 (by norm_num) ⟨11903, by rfl⟩ (by norm_num))
theorem R30717 : Reach 30717 := rs (se 3 (by rfl) ⟨5759, by rfl⟩) (B 11519 (by norm_num) ⟨5759, by rfl⟩ (by norm_num))
theorem R30721 : Reach 30721 := rs (se 2 (by rfl) ⟨11520, by rfl⟩) (B 23041 (by norm_num) ⟨11520, by rfl⟩ (by norm_num))
theorem R30725 : Reach 30725 := rs (se 4 (by rfl) ⟨2880, by rfl⟩) (B 5761 (by norm_num) ⟨2880, by rfl⟩ (by norm_num))
theorem R30729 : Reach 30729 := rs (se 2 (by rfl) ⟨11523, by rfl⟩) (B 23047 (by norm_num) ⟨11523, by rfl⟩ (by norm_num))
theorem R30733 : Reach 30733 := rs (se 3 (by rfl) ⟨5762, by rfl⟩) (B 11525 (by norm_num) ⟨5762, by rfl⟩ (by norm_num))
theorem R30737 : Reach 30737 := rs (se 2 (by rfl) ⟨11526, by rfl⟩) (B 23053 (by norm_num) ⟨11526, by rfl⟩ (by norm_num))
theorem R260117 : Reach 260117 := rs (se 6 (by rfl) ⟨6096, by rfl⟩) (B 12193 (by norm_num) ⟨6096, by rfl⟩ (by norm_num))
theorem R30741 : Reach 30741 := rs (se 6 (by rfl) ⟨720, by rfl⟩) (B 1441 (by norm_num) ⟨720, by rfl⟩ (by norm_num))
theorem R30745 : Reach 30745 := rs (se 2 (by rfl) ⟨11529, by rfl⟩) (B 23059 (by norm_num) ⟨11529, by rfl⟩ (by norm_num))
theorem R30749 : Reach 30749 := rs (se 3 (by rfl) ⟨5765, by rfl⟩) (B 11531 (by norm_num) ⟨5765, by rfl⟩ (by norm_num))
theorem R30753 : Reach 30753 := rs (se 2 (by rfl) ⟨11532, by rfl⟩) (B 23065 (by norm_num) ⟨11532, by rfl⟩ (by norm_num))
theorem R30757 : Reach 30757 := rs (se 4 (by rfl) ⟨2883, by rfl⟩) (B 5767 (by norm_num) ⟨2883, by rfl⟩ (by norm_num))
theorem R30761 : Reach 30761 := rs (se 2 (by rfl) ⟨11535, by rfl⟩) (B 23071 (by norm_num) ⟨11535, by rfl⟩ (by norm_num))
theorem R30765 : Reach 30765 := rs (se 3 (by rfl) ⟨5768, by rfl⟩) (B 11537 (by norm_num) ⟨5768, by rfl⟩ (by norm_num))
theorem R30769 : Reach 30769 := rs (se 2 (by rfl) ⟨11538, by rfl⟩) (B 23077 (by norm_num) ⟨11538, by rfl⟩ (by norm_num))
theorem R30773 : Reach 30773 := rs (se 5 (by rfl) ⟨1442, by rfl⟩) (B 2885 (by norm_num) ⟨1442, by rfl⟩ (by norm_num))
theorem R30777 : Reach 30777 := rs (se 2 (by rfl) ⟨11541, by rfl⟩) (B 23083 (by norm_num) ⟨11541, by rfl⟩ (by norm_num))
theorem R30781 : Reach 30781 := rs (se 3 (by rfl) ⟨5771, by rfl⟩) (B 11543 (by norm_num) ⟨5771, by rfl⟩ (by norm_num))
theorem R30785 : Reach 30785 := rs (se 2 (by rfl) ⟨11544, by rfl⟩) (B 23089 (by norm_num) ⟨11544, by rfl⟩ (by norm_num))
theorem R63557 : Reach 63557 := rs (se 4 (by rfl) ⟨5958, by rfl⟩) (B 11917 (by norm_num) ⟨5958, by rfl⟩ (by norm_num))
theorem R30789 : Reach 30789 := rs (se 4 (by rfl) ⟨2886, by rfl⟩) (B 5773 (by norm_num) ⟨2886, by rfl⟩ (by norm_num))
theorem R30793 : Reach 30793 := rs (se 2 (by rfl) ⟨11547, by rfl⟩) (B 23095 (by norm_num) ⟨11547, by rfl⟩ (by norm_num))
theorem R30797 : Reach 30797 := rs (se 3 (by rfl) ⟨5774, by rfl⟩) (B 11549 (by norm_num) ⟨5774, by rfl⟩ (by norm_num))
theorem R30801 : Reach 30801 := rs (se 2 (by rfl) ⟨11550, by rfl⟩) (B 23101 (by norm_num) ⟨11550, by rfl⟩ (by norm_num))
theorem R30805 : Reach 30805 := rs (se 8 (by rfl) ⟨180, by rfl⟩) (B 361 (by norm_num) ⟨180, by rfl⟩ (by norm_num))
theorem R30809 : Reach 30809 := rs (se 2 (by rfl) ⟨11553, by rfl⟩) (B 23107 (by norm_num) ⟨11553, by rfl⟩ (by norm_num))
theorem R30813 : Reach 30813 := rs (se 3 (by rfl) ⟨5777, by rfl⟩) (B 11555 (by norm_num) ⟨5777, by rfl⟩ (by norm_num))
theorem R30817 : Reach 30817 := rs (se 2 (by rfl) ⟨11556, by rfl⟩) (B 23113 (by norm_num) ⟨11556, by rfl⟩ (by norm_num))
theorem R30821 : Reach 30821 := rs (se 4 (by rfl) ⟨2889, by rfl⟩) (B 5779 (by norm_num) ⟨2889, by rfl⟩ (by norm_num))
theorem R30825 : Reach 30825 := rs (se 2 (by rfl) ⟨11559, by rfl⟩) (B 23119 (by norm_num) ⟨11559, by rfl⟩ (by norm_num))
theorem R30829 : Reach 30829 := rs (se 3 (by rfl) ⟨5780, by rfl⟩) (B 11561 (by norm_num) ⟨5780, by rfl⟩ (by norm_num))
theorem R30833 : Reach 30833 := rs (se 2 (by rfl) ⟨11562, by rfl⟩) (B 23125 (by norm_num) ⟨11562, by rfl⟩ (by norm_num))
theorem R30837 : Reach 30837 := rs (se 5 (by rfl) ⟨1445, by rfl⟩) (B 2891 (by norm_num) ⟨1445, by rfl⟩ (by norm_num))
theorem R30841 : Reach 30841 := rs (se 2 (by rfl) ⟨11565, by rfl⟩) (B 23131 (by norm_num) ⟨11565, by rfl⟩ (by norm_num))
theorem R30845 : Reach 30845 := rs (se 3 (by rfl) ⟨5783, by rfl⟩) (B 11567 (by norm_num) ⟨5783, by rfl⟩ (by norm_num))
theorem R30849 : Reach 30849 := rs (se 2 (by rfl) ⟨11568, by rfl⟩) (B 23137 (by norm_num) ⟨11568, by rfl⟩ (by norm_num))
theorem R96389 : Reach 96389 := rs (se 4 (by rfl) ⟨9036, by rfl⟩) (B 18073 (by norm_num) ⟨9036, by rfl⟩ (by norm_num))
theorem R30853 : Reach 30853 := rs (se 4 (by rfl) ⟨2892, by rfl⟩) (B 5785 (by norm_num) ⟨2892, by rfl⟩ (by norm_num))
theorem R30857 : Reach 30857 := rs (se 2 (by rfl) ⟨11571, by rfl⟩) (B 23143 (by norm_num) ⟨11571, by rfl⟩ (by norm_num))
theorem R63629 : Reach 63629 := rs (se 3 (by rfl) ⟨11930, by rfl⟩) (B 23861 (by norm_num) ⟨11930, by rfl⟩ (by norm_num))
theorem R30861 : Reach 30861 := rs (se 3 (by rfl) ⟨5786, by rfl⟩) (B 11573 (by norm_num) ⟨5786, by rfl⟩ (by norm_num))
theorem R30865 : Reach 30865 := rs (se 2 (by rfl) ⟨11574, by rfl⟩) (B 23149 (by norm_num) ⟨11574, by rfl⟩ (by norm_num))
theorem R30869 : Reach 30869 := rs (se 6 (by rfl) ⟨723, by rfl⟩) (B 1447 (by norm_num) ⟨723, by rfl⟩ (by norm_num))
theorem R30873 : Reach 30873 := rs (se 2 (by rfl) ⟨11577, by rfl⟩) (B 23155 (by norm_num) ⟨11577, by rfl⟩ (by norm_num))
theorem R30877 : Reach 30877 := rs (se 3 (by rfl) ⟨5789, by rfl⟩) (B 11579 (by norm_num) ⟨5789, by rfl⟩ (by norm_num))
theorem R30881 : Reach 30881 := rs (se 2 (by rfl) ⟨11580, by rfl⟩) (B 23161 (by norm_num) ⟨11580, by rfl⟩ (by norm_num))
theorem R30885 : Reach 30885 := rs (se 4 (by rfl) ⟨2895, by rfl⟩) (B 5791 (by norm_num) ⟨2895, by rfl⟩ (by norm_num))
theorem R30889 : Reach 30889 := rs (se 2 (by rfl) ⟨11583, by rfl⟩) (B 23167 (by norm_num) ⟨11583, by rfl⟩ (by norm_num))
theorem R30893 : Reach 30893 := rs (se 3 (by rfl) ⟨5792, by rfl⟩) (B 11585 (by norm_num) ⟨5792, by rfl⟩ (by norm_num))
theorem R30897 : Reach 30897 := rs (se 2 (by rfl) ⟨11586, by rfl⟩) (B 23173 (by norm_num) ⟨11586, by rfl⟩ (by norm_num))
theorem R30901 : Reach 30901 := rs (se 5 (by rfl) ⟨1448, by rfl⟩) (B 2897 (by norm_num) ⟨1448, by rfl⟩ (by norm_num))
theorem R30905 : Reach 30905 := rs (se 2 (by rfl) ⟨11589, by rfl⟩) (B 23179 (by norm_num) ⟨11589, by rfl⟩ (by norm_num))
theorem R30909 : Reach 30909 := rs (se 3 (by rfl) ⟨5795, by rfl⟩) (B 11591 (by norm_num) ⟨5795, by rfl⟩ (by norm_num))
theorem R30913 : Reach 30913 := rs (se 2 (by rfl) ⟨11592, by rfl⟩) (B 23185 (by norm_num) ⟨11592, by rfl⟩ (by norm_num))
theorem R30917 : Reach 30917 := rs (se 4 (by rfl) ⟨2898, by rfl⟩) (B 5797 (by norm_num) ⟨2898, by rfl⟩ (by norm_num))
theorem R30921 : Reach 30921 := rs (se 2 (by rfl) ⟨11595, by rfl⟩) (B 23191 (by norm_num) ⟨11595, by rfl⟩ (by norm_num))
theorem R30925 : Reach 30925 := rs (se 3 (by rfl) ⟨5798, by rfl⟩) (B 11597 (by norm_num) ⟨5798, by rfl⟩ (by norm_num))
theorem R30929 : Reach 30929 := rs (se 2 (by rfl) ⟨11598, by rfl⟩) (B 23197 (by norm_num) ⟨11598, by rfl⟩ (by norm_num))
theorem R63701 : Reach 63701 := rs (se 7 (by rfl) ⟨746, by rfl⟩) (B 1493 (by norm_num) ⟨746, by rfl⟩ (by norm_num))
theorem R30933 : Reach 30933 := rs (se 7 (by rfl) ⟨362, by rfl⟩) (B 725 (by norm_num) ⟨362, by rfl⟩ (by norm_num))
theorem R30937 : Reach 30937 := rs (se 2 (by rfl) ⟨11601, by rfl⟩) (B 23203 (by norm_num) ⟨11601, by rfl⟩ (by norm_num))
theorem R30941 : Reach 30941 := rs (se 3 (by rfl) ⟨5801, by rfl⟩) (B 11603 (by norm_num) ⟨5801, by rfl⟩ (by norm_num))
theorem R30945 : Reach 30945 := rs (se 2 (by rfl) ⟨11604, by rfl⟩) (B 23209 (by norm_num) ⟨11604, by rfl⟩ (by norm_num))
theorem R30949 : Reach 30949 := rs (se 4 (by rfl) ⟨2901, by rfl⟩) (B 5803 (by norm_num) ⟨2901, by rfl⟩ (by norm_num))
theorem R30953 : Reach 30953 := rs (se 2 (by rfl) ⟨11607, by rfl⟩) (B 23215 (by norm_num) ⟨11607, by rfl⟩ (by norm_num))
theorem R30957 : Reach 30957 := rs (se 3 (by rfl) ⟨5804, by rfl⟩) (B 11609 (by norm_num) ⟨5804, by rfl⟩ (by norm_num))
theorem R30961 : Reach 30961 := rs (se 2 (by rfl) ⟨11610, by rfl⟩) (B 23221 (by norm_num) ⟨11610, by rfl⟩ (by norm_num))
theorem R30965 : Reach 30965 := rs (se 5 (by rfl) ⟨1451, by rfl⟩) (B 2903 (by norm_num) ⟨1451, by rfl⟩ (by norm_num))
theorem R30969 : Reach 30969 := rs (se 2 (by rfl) ⟨11613, by rfl⟩) (B 23227 (by norm_num) ⟨11613, by rfl⟩ (by norm_num))
theorem R30973 : Reach 30973 := rs (se 3 (by rfl) ⟨5807, by rfl⟩) (B 11615 (by norm_num) ⟨5807, by rfl⟩ (by norm_num))
theorem R30977 : Reach 30977 := rs (se 2 (by rfl) ⟨11616, by rfl⟩) (B 23233 (by norm_num) ⟨11616, by rfl⟩ (by norm_num))
theorem R30981 : Reach 30981 := rs (se 4 (by rfl) ⟨2904, by rfl⟩) (B 5809 (by norm_num) ⟨2904, by rfl⟩ (by norm_num))
theorem R30985 : Reach 30985 := rs (se 2 (by rfl) ⟨11619, by rfl⟩) (B 23239 (by norm_num) ⟨11619, by rfl⟩ (by norm_num))
theorem R63757 : Reach 63757 := rs (se 3 (by rfl) ⟨11954, by rfl⟩) (B 23909 (by norm_num) ⟨11954, by rfl⟩ (by norm_num))
theorem R30989 : Reach 30989 := rs (se 3 (by rfl) ⟨5810, by rfl⟩) (B 11621 (by norm_num) ⟨5810, by rfl⟩ (by norm_num))
theorem R30993 : Reach 30993 := rs (se 2 (by rfl) ⟨11622, by rfl⟩) (B 23245 (by norm_num) ⟨11622, by rfl⟩ (by norm_num))
theorem R30997 : Reach 30997 := rs (se 6 (by rfl) ⟨726, by rfl⟩) (B 1453 (by norm_num) ⟨726, by rfl⟩ (by norm_num))
theorem R31001 : Reach 31001 := rs (se 2 (by rfl) ⟨11625, by rfl⟩) (B 23251 (by norm_num) ⟨11625, by rfl⟩ (by norm_num))
theorem R63773 : Reach 63773 := rs (se 3 (by rfl) ⟨11957, by rfl⟩) (B 23915 (by norm_num) ⟨11957, by rfl⟩ (by norm_num))
theorem R31005 : Reach 31005 := rs (se 3 (by rfl) ⟨5813, by rfl⟩) (B 11627 (by norm_num) ⟨5813, by rfl⟩ (by norm_num))
theorem R31009 : Reach 31009 := rs (se 2 (by rfl) ⟨11628, by rfl⟩) (B 23257 (by norm_num) ⟨11628, by rfl⟩ (by norm_num))
theorem R31013 : Reach 31013 := rs (se 4 (by rfl) ⟨2907, by rfl⟩) (B 5815 (by norm_num) ⟨2907, by rfl⟩ (by norm_num))
theorem R31017 : Reach 31017 := rs (se 2 (by rfl) ⟨11631, by rfl⟩) (B 23263 (by norm_num) ⟨11631, by rfl⟩ (by norm_num))
theorem R31021 : Reach 31021 := rs (se 3 (by rfl) ⟨5816, by rfl⟩) (B 11633 (by norm_num) ⟨5816, by rfl⟩ (by norm_num))
theorem R31025 : Reach 31025 := rs (se 2 (by rfl) ⟨11634, by rfl⟩) (B 23269 (by norm_num) ⟨11634, by rfl⟩ (by norm_num))
theorem R31029 : Reach 31029 := rs (se 5 (by rfl) ⟨1454, by rfl⟩) (B 2909 (by norm_num) ⟨1454, by rfl⟩ (by norm_num))
theorem R31033 : Reach 31033 := rs (se 2 (by rfl) ⟨11637, by rfl⟩) (B 23275 (by norm_num) ⟨11637, by rfl⟩ (by norm_num))
theorem R31037 : Reach 31037 := rs (se 3 (by rfl) ⟨5819, by rfl⟩) (B 11639 (by norm_num) ⟨5819, by rfl⟩ (by norm_num))
theorem R31041 : Reach 31041 := rs (se 2 (by rfl) ⟨11640, by rfl⟩) (B 23281 (by norm_num) ⟨11640, by rfl⟩ (by norm_num))
theorem R31045 : Reach 31045 := rs (se 4 (by rfl) ⟨2910, by rfl⟩) (B 5821 (by norm_num) ⟨2910, by rfl⟩ (by norm_num))
theorem R31049 : Reach 31049 := rs (se 2 (by rfl) ⟨11643, by rfl⟩) (B 23287 (by norm_num) ⟨11643, by rfl⟩ (by norm_num))
theorem R31053 : Reach 31053 := rs (se 3 (by rfl) ⟨5822, by rfl⟩) (B 11645 (by norm_num) ⟨5822, by rfl⟩ (by norm_num))
theorem R31057 : Reach 31057 := rs (se 2 (by rfl) ⟨11646, by rfl⟩) (B 23293 (by norm_num) ⟨11646, by rfl⟩ (by norm_num))
theorem R31061 : Reach 31061 := rs (se 10 (by rfl) ⟨45, by rfl⟩) (B 91 (by norm_num) ⟨45, by rfl⟩ (by norm_num))
theorem R31065 : Reach 31065 := rs (se 2 (by rfl) ⟨11649, by rfl⟩) (B 23299 (by norm_num) ⟨11649, by rfl⟩ (by norm_num))
theorem R31069 : Reach 31069 := rs (se 3 (by rfl) ⟨5825, by rfl⟩) (B 11651 (by norm_num) ⟨5825, by rfl⟩ (by norm_num))
theorem R31073 : Reach 31073 := rs (se 2 (by rfl) ⟨11652, by rfl⟩) (B 23305 (by norm_num) ⟨11652, by rfl⟩ (by norm_num))
theorem R63845 : Reach 63845 := rs (se 4 (by rfl) ⟨5985, by rfl⟩) (B 11971 (by norm_num) ⟨5985, by rfl⟩ (by norm_num))
theorem R31077 : Reach 31077 := rs (se 4 (by rfl) ⟨2913, by rfl⟩) (B 5827 (by norm_num) ⟨2913, by rfl⟩ (by norm_num))
theorem R31081 : Reach 31081 := rs (se 2 (by rfl) ⟨11655, by rfl⟩) (B 23311 (by norm_num) ⟨11655, by rfl⟩ (by norm_num))
theorem R31085 : Reach 31085 := rs (se 3 (by rfl) ⟨5828, by rfl⟩) (B 11657 (by norm_num) ⟨5828, by rfl⟩ (by norm_num))
theorem R31089 : Reach 31089 := rs (se 2 (by rfl) ⟨11658, by rfl⟩) (B 23317 (by norm_num) ⟨11658, by rfl⟩ (by norm_num))
theorem R31093 : Reach 31093 := rs (se 5 (by rfl) ⟨1457, by rfl⟩) (B 2915 (by norm_num) ⟨1457, by rfl⟩ (by norm_num))
theorem R31097 : Reach 31097 := rs (se 2 (by rfl) ⟨11661, by rfl⟩) (B 23323 (by norm_num) ⟨11661, by rfl⟩ (by norm_num))
theorem R31101 : Reach 31101 := rs (se 3 (by rfl) ⟨5831, by rfl⟩) (B 11663 (by norm_num) ⟨5831, by rfl⟩ (by norm_num))
theorem R31105 : Reach 31105 := rs (se 2 (by rfl) ⟨11664, by rfl⟩) (B 23329 (by norm_num) ⟨11664, by rfl⟩ (by norm_num))
theorem R31109 : Reach 31109 := rs (se 4 (by rfl) ⟨2916, by rfl⟩) (B 5833 (by norm_num) ⟨2916, by rfl⟩ (by norm_num))
theorem R31113 : Reach 31113 := rs (se 2 (by rfl) ⟨11667, by rfl⟩) (B 23335 (by norm_num) ⟨11667, by rfl⟩ (by norm_num))
theorem R31117 : Reach 31117 := rs (se 3 (by rfl) ⟨5834, by rfl⟩) (B 11669 (by norm_num) ⟨5834, by rfl⟩ (by norm_num))
theorem R63893 : Reach 63893 := rs (se 6 (by rfl) ⟨1497, by rfl⟩) (B 2995 (by norm_num) ⟨1497, by rfl⟩ (by norm_num))
theorem R63917 : Reach 63917 := rs (se 3 (by rfl) ⟨11984, by rfl⟩) (B 23969 (by norm_num) ⟨11984, by rfl⟩ (by norm_num))
theorem R31153 : Reach 31153 := rs (se 2 (by rfl) ⟨11682, by rfl⟩) (B 23365 (by norm_num) ⟨11682, by rfl⟩ (by norm_num))
theorem R31189 : Reach 31189 := rs (se 7 (by rfl) ⟨365, by rfl⟩) (B 731 (by norm_num) ⟨365, by rfl⟩ (by norm_num))
theorem R31205 : Reach 31205 := rs (se 4 (by rfl) ⟨2925, by rfl⟩) (B 5851 (by norm_num) ⟨2925, by rfl⟩ (by norm_num))
theorem R63989 : Reach 63989 := rs (se 5 (by rfl) ⟨2999, by rfl⟩) (B 5999 (by norm_num) ⟨2999, by rfl⟩ (by norm_num))
theorem R31225 : Reach 31225 := rs (se 2 (by rfl) ⟨11709, by rfl⟩) (B 23419 (by norm_num) ⟨11709, by rfl⟩ (by norm_num))
theorem R31261 : Reach 31261 := rs (se 3 (by rfl) ⟨5861, by rfl⟩) (B 11723 (by norm_num) ⟨5861, by rfl⟩ (by norm_num))
theorem R96821 : Reach 96821 := rs (se 5 (by rfl) ⟨4538, by rfl⟩) (B 9077 (by norm_num) ⟨4538, by rfl⟩ (by norm_num))
theorem R64061 : Reach 64061 := rs (se 3 (by rfl) ⟨12011, by rfl⟩) (B 24023 (by norm_num) ⟨12011, by rfl⟩ (by norm_num))
theorem R31297 : Reach 31297 := rs (se 2 (by rfl) ⟨11736, by rfl⟩) (B 23473 (by norm_num) ⟨11736, by rfl⟩ (by norm_num))
theorem R31333 : Reach 31333 := rs (se 4 (by rfl) ⟨2937, by rfl⟩) (B 5875 (by norm_num) ⟨2937, by rfl⟩ (by norm_num))
theorem R64133 : Reach 64133 := rs (se 4 (by rfl) ⟨6012, by rfl⟩) (B 12025 (by norm_num) ⟨6012, by rfl⟩ (by norm_num))
theorem R31369 : Reach 31369 := rs (se 2 (by rfl) ⟨11763, by rfl⟩) (B 23527 (by norm_num) ⟨11763, by rfl⟩ (by norm_num))
theorem R129701 : Reach 129701 := rs (se 4 (by rfl) ⟨12159, by rfl⟩) (B 24319 (by norm_num) ⟨12159, by rfl⟩ (by norm_num))
theorem R31405 : Reach 31405 := rs (se 3 (by rfl) ⟨5888, by rfl⟩) (B 11777 (by norm_num) ⟨5888, by rfl⟩ (by norm_num))
theorem R64205 : Reach 64205 := rs (se 3 (by rfl) ⟨12038, by rfl⟩) (B 24077 (by norm_num) ⟨12038, by rfl⟩ (by norm_num))
theorem R31441 : Reach 31441 := rs (se 2 (by rfl) ⟨11790, by rfl⟩) (B 23581 (by norm_num) ⟨11790, by rfl⟩ (by norm_num))
theorem R31477 : Reach 31477 := rs (se 5 (by rfl) ⟨1475, by rfl⟩) (B 2951 (by norm_num) ⟨1475, by rfl⟩ (by norm_num))
theorem R64277 : Reach 64277 := rs (se 6 (by rfl) ⟨1506, by rfl⟩) (B 3013 (by norm_num) ⟨1506, by rfl⟩ (by norm_num))
theorem R31513 : Reach 31513 := rs (se 2 (by rfl) ⟨11817, by rfl⟩) (B 23635 (by norm_num) ⟨11817, by rfl⟩ (by norm_num))
theorem R31537 : Reach 31537 := rs (se 2 (by rfl) ⟨11826, by rfl⟩) (B 23653 (by norm_num) ⟨11826, by rfl⟩ (by norm_num))
theorem R31549 : Reach 31549 := rs (se 3 (by rfl) ⟨5915, by rfl⟩) (B 11831 (by norm_num) ⟨5915, by rfl⟩ (by norm_num))
theorem R97109 : Reach 97109 := rs (se 9 (by rfl) ⟨284, by rfl⟩) (B 569 (by norm_num) ⟨284, by rfl⟩ (by norm_num))
theorem R64349 : Reach 64349 := rs (se 3 (by rfl) ⟨12065, by rfl⟩) (B 24131 (by norm_num) ⟨12065, by rfl⟩ (by norm_num))
theorem R31585 : Reach 31585 := rs (se 2 (by rfl) ⟨11844, by rfl⟩) (B 23689 (by norm_num) ⟨11844, by rfl⟩ (by norm_num))
theorem R31609 : Reach 31609 := rs (se 2 (by rfl) ⟨11853, by rfl⟩) (B 23707 (by norm_num) ⟨11853, by rfl⟩ (by norm_num))
theorem R31621 : Reach 31621 := rs (se 4 (by rfl) ⟨2964, by rfl⟩) (B 5929 (by norm_num) ⟨2964, by rfl⟩ (by norm_num))
theorem R64421 : Reach 64421 := rs (se 4 (by rfl) ⟨6039, by rfl⟩) (B 12079 (by norm_num) ⟨6039, by rfl⟩ (by norm_num))
theorem R31657 : Reach 31657 := rs (se 2 (by rfl) ⟨11871, by rfl⟩) (B 23743 (by norm_num) ⟨11871, by rfl⟩ (by norm_num))
theorem R31693 : Reach 31693 := rs (se 3 (by rfl) ⟨5942, by rfl⟩) (B 11885 (by norm_num) ⟨5942, by rfl⟩ (by norm_num))
theorem R97253 : Reach 97253 := rs (se 4 (by rfl) ⟨9117, by rfl⟩) (B 18235 (by norm_num) ⟨9117, by rfl⟩ (by norm_num))
theorem R64493 : Reach 64493 := rs (se 3 (by rfl) ⟨12092, by rfl⟩) (B 24185 (by norm_num) ⟨12092, by rfl⟩ (by norm_num))
theorem R31729 : Reach 31729 := rs (se 2 (by rfl) ⟨11898, by rfl⟩) (B 23797 (by norm_num) ⟨11898, by rfl⟩ (by norm_num))
theorem R31765 : Reach 31765 := rs (se 6 (by rfl) ⟨744, by rfl⟩) (B 1489 (by norm_num) ⟨744, by rfl⟩ (by norm_num))
theorem R31789 : Reach 31789 := rs (se 3 (by rfl) ⟨5960, by rfl⟩) (B 11921 (by norm_num) ⟨5960, by rfl⟩ (by norm_num))
theorem R64565 : Reach 64565 := rs (se 5 (by rfl) ⟨3026, by rfl⟩) (B 6053 (by norm_num) ⟨3026, by rfl⟩ (by norm_num))
theorem R31801 : Reach 31801 := rs (se 2 (by rfl) ⟨11925, by rfl⟩) (B 23851 (by norm_num) ⟨11925, by rfl⟩ (by norm_num))
theorem R31817 : Reach 31817 := rs (se 2 (by rfl) ⟨11931, by rfl⟩) (B 23863 (by norm_num) ⟨11931, by rfl⟩ (by norm_num))
theorem R31837 : Reach 31837 := rs (se 3 (by rfl) ⟨5969, by rfl⟩) (B 11939 (by norm_num) ⟨5969, by rfl⟩ (by norm_num))
theorem R64637 : Reach 64637 := rs (se 3 (by rfl) ⟨12119, by rfl⟩) (B 24239 (by norm_num) ⟨12119, by rfl⟩ (by norm_num))
theorem R31873 : Reach 31873 := rs (se 2 (by rfl) ⟨11952, by rfl⟩) (B 23905 (by norm_num) ⟨11952, by rfl⟩ (by norm_num))
theorem R31909 : Reach 31909 := rs (se 4 (by rfl) ⟨2991, by rfl⟩) (B 5983 (by norm_num) ⟨2991, by rfl⟩ (by norm_num))
theorem R64709 : Reach 64709 := rs (se 4 (by rfl) ⟨6066, by rfl⟩) (B 12133 (by norm_num) ⟨6066, by rfl⟩ (by norm_num))
theorem R31945 : Reach 31945 := rs (se 2 (by rfl) ⟨11979, by rfl⟩) (B 23959 (by norm_num) ⟨11979, by rfl⟩ (by norm_num))
theorem R31981 : Reach 31981 := rs (se 3 (by rfl) ⟨5996, by rfl⟩) (B 11993 (by norm_num) ⟨5996, by rfl⟩ (by norm_num))
theorem R64781 : Reach 64781 := rs (se 3 (by rfl) ⟨12146, by rfl⟩) (B 24293 (by norm_num) ⟨12146, by rfl⟩ (by norm_num))
theorem R32017 : Reach 32017 := rs (se 2 (by rfl) ⟨12006, by rfl⟩) (B 24013 (by norm_num) ⟨12006, by rfl⟩ (by norm_num))
theorem R32053 : Reach 32053 := rs (se 5 (by rfl) ⟨1502, by rfl⟩) (B 3005 (by norm_num) ⟨1502, by rfl⟩ (by norm_num))
theorem R64853 : Reach 64853 := rs (se 11 (by rfl) ⟨47, by rfl⟩) (B 95 (by norm_num) ⟨47, by rfl⟩ (by norm_num))
theorem R32089 : Reach 32089 := rs (se 2 (by rfl) ⟨12033, by rfl⟩) (B 24067 (by norm_num) ⟨12033, by rfl⟩ (by norm_num))
theorem R32113 : Reach 32113 := rs (se 2 (by rfl) ⟨12042, by rfl⟩) (B 24085 (by norm_num) ⟨12042, by rfl⟩ (by norm_num))
theorem R32125 : Reach 32125 := rs (se 3 (by rfl) ⟨6023, by rfl⟩) (B 12047 (by norm_num) ⟨6023, by rfl⟩ (by norm_num))
theorem R97685 : Reach 97685 := rs (se 6 (by rfl) ⟨2289, by rfl⟩) (B 4579 (by norm_num) ⟨2289, by rfl⟩ (by norm_num))
theorem R64925 : Reach 64925 := rs (se 3 (by rfl) ⟨12173, by rfl⟩) (B 24347 (by norm_num) ⟨12173, by rfl⟩ (by norm_num))
theorem R32161 : Reach 32161 := rs (se 2 (by rfl) ⟨12060, by rfl⟩) (B 24121 (by norm_num) ⟨12060, by rfl⟩ (by norm_num))
theorem R32197 : Reach 32197 := rs (se 4 (by rfl) ⟨3018, by rfl⟩) (B 6037 (by norm_num) ⟨3018, by rfl⟩ (by norm_num))
theorem R261589 : Reach 261589 := rs (se 7 (by rfl) ⟨3065, by rfl⟩) (B 6131 (by norm_num) ⟨3065, by rfl⟩ (by norm_num))
theorem R64997 : Reach 64997 := rs (se 4 (by rfl) ⟨6093, by rfl⟩) (B 12187 (by norm_num) ⟨6093, by rfl⟩ (by norm_num))
theorem R32233 : Reach 32233 := rs (se 2 (by rfl) ⟨12087, by rfl⟩) (B 24175 (by norm_num) ⟨12087, by rfl⟩ (by norm_num))
theorem R32269 : Reach 32269 := rs (se 3 (by rfl) ⟨6050, by rfl⟩) (B 12101 (by norm_num) ⟨6050, by rfl⟩ (by norm_num))
theorem R65069 : Reach 65069 := rs (se 3 (by rfl) ⟨12200, by rfl⟩) (B 24401 (by norm_num) ⟨12200, by rfl⟩ (by norm_num))
theorem R32305 : Reach 32305 := rs (se 2 (by rfl) ⟨12114, by rfl⟩) (B 24229 (by norm_num) ⟨12114, by rfl⟩ (by norm_num))
theorem R32341 : Reach 32341 := rs (se 8 (by rfl) ⟨189, by rfl⟩) (B 379 (by norm_num) ⟨189, by rfl⟩ (by norm_num))
theorem R32357 : Reach 32357 := rs (se 4 (by rfl) ⟨3033, by rfl⟩) (B 6067 (by norm_num) ⟨3033, by rfl⟩ (by norm_num))
theorem R65141 : Reach 65141 := rs (se 5 (by rfl) ⟨3053, by rfl⟩) (B 6107 (by norm_num) ⟨3053, by rfl⟩ (by norm_num))
theorem R32377 : Reach 32377 := rs (se 2 (by rfl) ⟨12141, by rfl⟩) (B 24283 (by norm_num) ⟨12141, by rfl⟩ (by norm_num))
theorem R32413 : Reach 32413 := rs (se 3 (by rfl) ⟨6077, by rfl⟩) (B 12155 (by norm_num) ⟨6077, by rfl⟩ (by norm_num))
theorem R65213 : Reach 65213 := rs (se 3 (by rfl) ⟨12227, by rfl⟩) (B 24455 (by norm_num) ⟨12227, by rfl⟩ (by norm_num))
theorem R32449 : Reach 32449 := rs (se 2 (by rfl) ⟨12168, by rfl⟩) (B 24337 (by norm_num) ⟨12168, by rfl⟩ (by norm_num))
theorem R98005 : Reach 98005 := rs (se 7 (by rfl) ⟨1148, by rfl⟩) (B 2297 (by norm_num) ⟨1148, by rfl⟩ (by norm_num))
theorem R32485 : Reach 32485 := rs (se 4 (by rfl) ⟨3045, by rfl⟩) (B 6091 (by norm_num) ⟨3045, by rfl⟩ (by norm_num))
theorem R65261 : Reach 65261 := rs (se 3 (by rfl) ⟨12236, by rfl⟩) (B 24473 (by norm_num) ⟨12236, by rfl⟩ (by norm_num))
theorem R65285 : Reach 65285 := rs (se 4 (by rfl) ⟨6120, by rfl⟩) (B 12241 (by norm_num) ⟨6120, by rfl⟩ (by norm_num))
theorem R32521 : Reach 32521 := rs (se 2 (by rfl) ⟨12195, by rfl⟩) (B 24391 (by norm_num) ⟨12195, by rfl⟩ (by norm_num))
theorem R32557 : Reach 32557 := rs (se 3 (by rfl) ⟨6104, by rfl⟩) (B 12209 (by norm_num) ⟨6104, by rfl⟩ (by norm_num))
theorem R32581 : Reach 32581 := rs (se 4 (by rfl) ⟨3054, by rfl⟩) (B 6109 (by norm_num) ⟨3054, by rfl⟩ (by norm_num))
theorem R98117 : Reach 98117 := rs (se 4 (by rfl) ⟨9198, by rfl⟩) (B 18397 (by norm_num) ⟨9198, by rfl⟩ (by norm_num))
theorem R65357 : Reach 65357 := rs (se 3 (by rfl) ⟨12254, by rfl⟩) (B 24509 (by norm_num) ⟨12254, by rfl⟩ (by norm_num))
theorem R32593 : Reach 32593 := rs (se 2 (by rfl) ⟨12222, by rfl⟩) (B 24445 (by norm_num) ⟨12222, by rfl⟩ (by norm_num))
theorem R32609 : Reach 32609 := rs (se 2 (by rfl) ⟨12228, by rfl⟩) (B 24457 (by norm_num) ⟨12228, by rfl⟩ (by norm_num))
theorem R32629 : Reach 32629 := rs (se 5 (by rfl) ⟨1529, by rfl⟩) (B 3059 (by norm_num) ⟨1529, by rfl⟩ (by norm_num))
theorem R65405 : Reach 65405 := rs (se 3 (by rfl) ⟨12263, by rfl⟩) (B 24527 (by norm_num) ⟨12263, by rfl⟩ (by norm_num))
theorem R65429 : Reach 65429 := rs (se 6 (by rfl) ⟨1533, by rfl⟩) (B 3067 (by norm_num) ⟨1533, by rfl⟩ (by norm_num))
theorem R32665 : Reach 32665 := rs (se 2 (by rfl) ⟨12249, by rfl⟩) (B 24499 (by norm_num) ⟨12249, by rfl⟩ (by norm_num))
theorem R32701 : Reach 32701 := rs (se 3 (by rfl) ⟨6131, by rfl⟩) (B 12263 (by norm_num) ⟨6131, by rfl⟩ (by norm_num))
theorem R32729 : Reach 32729 := rs (se 2 (by rfl) ⟨12273, by rfl⟩) (B 24547 (by norm_num) ⟨12273, by rfl⟩ (by norm_num))
theorem R65501 : Reach 65501 := rs (se 3 (by rfl) ⟨12281, by rfl⟩) (B 24563 (by norm_num) ⟨12281, by rfl⟩ (by norm_num))
theorem R32737 : Reach 32737 := rs (se 2 (by rfl) ⟨12276, by rfl⟩) (B 24553 (by norm_num) ⟨12276, by rfl⟩ (by norm_num))
theorem R32771 : Reach 32771 := rs (se 1 (by rfl) ⟨24578, by rfl⟩) R49157
theorem R65585 : Reach 65585 := rs (se 2 (by rfl) ⟨24594, by rfl⟩) R49189
theorem R163889 : Reach 163889 := rs (se 2 (by rfl) ⟨61458, by rfl⟩) R122917
theorem R65603 : Reach 65603 := rs (se 1 (by rfl) ⟨49202, by rfl⟩) R98405
theorem R32899 : Reach 32899 := rs (se 1 (by rfl) ⟨24674, by rfl⟩) R49349
theorem R65681 : Reach 65681 := rs (se 2 (by rfl) ⟨24630, by rfl⟩) R49261
theorem R65699 : Reach 65699 := rs (se 1 (by rfl) ⟨49274, by rfl⟩) R98549
theorem R65713 : Reach 65713 := rs (se 2 (by rfl) ⟨24642, by rfl⟩) R49285
theorem R32995 : Reach 32995 := rs (se 1 (by rfl) ⟨24746, by rfl⟩) R49493
theorem R65777 : Reach 65777 := rs (se 2 (by rfl) ⟨24666, by rfl⟩) R49333
theorem R131341 : Reach 131341 := rs (se 3 (by rfl) ⟨24626, by rfl⟩) R49253
theorem R33043 : Reach 33043 := rs (se 1 (by rfl) ⟨24782, by rfl⟩) R49565
theorem R328049 : Reach 328049 := rs (se 2 (by rfl) ⟨123018, by rfl⟩) R246037
theorem R98723 : Reach 98723 := rs (se 1 (by rfl) ⟨74042, by rfl⟩) R148085
theorem R33187 : Reach 33187 := rs (se 1 (by rfl) ⟨24890, by rfl⟩) R49781
theorem R65969 : Reach 65969 := rs (se 2 (by rfl) ⟨24738, by rfl⟩) R49477
theorem R65987 : Reach 65987 := rs (se 1 (by rfl) ⟨49490, by rfl⟩) R98981
theorem R98765 : Reach 98765 := rs (se 3 (by rfl) ⟨18518, by rfl⟩) R37037
theorem R98851 : Reach 98851 := rs (se 1 (by rfl) ⟨74138, by rfl⟩) R148277
theorem R33331 : Reach 33331 := rs (se 1 (by rfl) ⟨24998, by rfl⟩) R49997
theorem R33475 : Reach 33475 := rs (se 1 (by rfl) ⟨25106, by rfl⟩) R50213
theorem R66257 : Reach 66257 := rs (se 2 (by rfl) ⟨24846, by rfl⟩) R49693
theorem R66275 : Reach 66275 := rs (se 1 (by rfl) ⟨49706, by rfl⟩) R99413
theorem R33619 : Reach 33619 := rs (se 1 (by rfl) ⟨25214, by rfl⟩) R50429
theorem R131939 : Reach 131939 := rs (se 1 (by rfl) ⟨98954, by rfl⟩) R197909
theorem R99235 : Reach 99235 := rs (se 1 (by rfl) ⟨74426, by rfl⟩) R148853
theorem R33715 : Reach 33715 := rs (se 1 (by rfl) ⟨25286, by rfl⟩) R50573
theorem R33763 : Reach 33763 := rs (se 1 (by rfl) ⟨25322, by rfl⟩) R50645
theorem R66545 : Reach 66545 := rs (se 2 (by rfl) ⟨24954, by rfl⟩) R49909
theorem R66563 : Reach 66563 := rs (se 1 (by rfl) ⟨49922, by rfl⟩) R99845
theorem R132131 : Reach 132131 := rs (se 1 (by rfl) ⟨99098, by rfl⟩) R198197
theorem R33907 : Reach 33907 := rs (se 1 (by rfl) ⟨25430, by rfl⟩) R50861
theorem R99569 : Reach 99569 := rs (se 2 (by rfl) ⟨37338, by rfl⟩) R74677
theorem R34051 : Reach 34051 := rs (se 1 (by rfl) ⟨25538, by rfl⟩) R51077
theorem R66833 : Reach 66833 := rs (se 2 (by rfl) ⟨25062, by rfl⟩) R50125
theorem R66851 : Reach 66851 := rs (se 1 (by rfl) ⟨50138, by rfl⟩) R100277
theorem R656693 : Reach 656693 := rs (se 5 (by rfl) ⟨30782, by rfl⟩) R61565
theorem R99683 : Reach 99683 := rs (se 1 (by rfl) ⟨74762, by rfl⟩) R149525
theorem R34195 : Reach 34195 := rs (se 1 (by rfl) ⟨25646, by rfl⟩) R51293
theorem R165347 : Reach 165347 := rs (se 1 (by rfl) ⟨124010, by rfl⟩) R248021
theorem R34339 : Reach 34339 := rs (se 1 (by rfl) ⟨25754, by rfl⟩) R51509
theorem R67121 : Reach 67121 := rs (se 2 (by rfl) ⟨25170, by rfl⟩) R50341
theorem R67139 : Reach 67139 := rs (se 1 (by rfl) ⟨50354, by rfl⟩) R100709
theorem R99953 : Reach 99953 := rs (se 2 (by rfl) ⟨37482, by rfl⟩) R74965
theorem R34435 : Reach 34435 := rs (se 1 (by rfl) ⟨25826, by rfl⟩) R51653
theorem R132785 : Reach 132785 := rs (se 2 (by rfl) ⟨49794, by rfl⟩) R99589
theorem R34483 : Reach 34483 := rs (se 1 (by rfl) ⟨25862, by rfl⟩) R51725
theorem R362165 : Reach 362165 := rs (se 5 (by rfl) ⟨16976, by rfl⟩) R33953
theorem R34627 : Reach 34627 := rs (se 1 (by rfl) ⟨25970, by rfl⟩) R51941
theorem R67409 : Reach 67409 := rs (se 2 (by rfl) ⟨25278, by rfl⟩) R50557
theorem R67427 : Reach 67427 := rs (se 1 (by rfl) ⟨50570, by rfl⟩) R101141
theorem R132977 : Reach 132977 := rs (se 2 (by rfl) ⟨49866, by rfl⟩) R99733
theorem R34771 : Reach 34771 := rs (se 1 (by rfl) ⟨26078, by rfl⟩) R52157
theorem R34787 : Reach 34787 := rs (se 1 (by rfl) ⟨26090, by rfl⟩) R52181
theorem R34915 : Reach 34915 := rs (se 1 (by rfl) ⟨26186, by rfl⟩) R52373
theorem R67697 : Reach 67697 := rs (se 2 (by rfl) ⟨25386, by rfl⟩) R50773
theorem R34931 : Reach 34931 := rs (se 1 (by rfl) ⟨26198, by rfl⟩) R52397
theorem R67715 : Reach 67715 := rs (se 1 (by rfl) ⟨50786, by rfl⟩) R101573
theorem R100493 : Reach 100493 := rs (se 3 (by rfl) ⟨18842, by rfl⟩) R37685
theorem R67729 : Reach 67729 := rs (se 2 (by rfl) ⟨25398, by rfl⟩) R50797
theorem R231821 : Reach 231821 := rs (se 3 (by rfl) ⟨43466, by rfl⟩) R86933
theorem R67985 : Reach 67985 := rs (se 2 (by rfl) ⟨25494, by rfl⟩) R50989
theorem R68003 : Reach 68003 := rs (se 1 (by rfl) ⟨51002, by rfl⟩) R102005
theorem R68273 : Reach 68273 := rs (se 2 (by rfl) ⟨25602, by rfl⟩) R51205
theorem R68291 : Reach 68291 := rs (se 1 (by rfl) ⟨51218, by rfl⟩) R102437
theorem R101155 : Reach 101155 := rs (se 1 (by rfl) ⟨75866, by rfl⟩) R151733
theorem R35635 : Reach 35635 := rs (se 1 (by rfl) ⟨26726, by rfl⟩) R53453
theorem R199523 : Reach 199523 := rs (se 1 (by rfl) ⟨149642, by rfl⟩) R299285
theorem R166769 : Reach 166769 := rs (se 2 (by rfl) ⟨62538, by rfl⟩) R125077
theorem R35731 : Reach 35731 := rs (se 1 (by rfl) ⟨26798, by rfl⟩) R53597
theorem R68561 : Reach 68561 := rs (se 2 (by rfl) ⟨25710, by rfl⟩) R51421
theorem R68579 : Reach 68579 := rs (se 1 (by rfl) ⟨51434, by rfl⟩) R102869
theorem R35875 : Reach 35875 := rs (se 1 (by rfl) ⟨26906, by rfl⟩) R53813
theorem R101411 : Reach 101411 := rs (se 1 (by rfl) ⟨76058, by rfl⟩) R152117
theorem R36067 : Reach 36067 := rs (se 1 (by rfl) ⟨27050, by rfl⟩) R54101
theorem R199907 : Reach 199907 := rs (se 1 (by rfl) ⟨149930, by rfl⟩) R299861
theorem R68849 : Reach 68849 := rs (se 2 (by rfl) ⟨25818, by rfl⟩) R51637
theorem R68867 : Reach 68867 := rs (se 1 (by rfl) ⟨51650, by rfl⟩) R103301
theorem R101681 : Reach 101681 := rs (se 2 (by rfl) ⟨38130, by rfl⟩) R76261
theorem R36227 : Reach 36227 := rs (se 1 (by rfl) ⟨27170, by rfl⟩) R54341
theorem R232901 : Reach 232901 := rs (se 4 (by rfl) ⟨21834, by rfl⟩) R43669
theorem R69137 : Reach 69137 := rs (se 2 (by rfl) ⟨25926, by rfl⟩) R51853
theorem R69155 : Reach 69155 := rs (se 1 (by rfl) ⟨51866, by rfl⟩) R103733
theorem R69425 : Reach 69425 := rs (se 2 (by rfl) ⟨26034, by rfl⟩) R52069
theorem R69443 : Reach 69443 := rs (se 1 (by rfl) ⟨52082, by rfl⟩) R104165
theorem R102221 : Reach 102221 := rs (se 3 (by rfl) ⟨19166, by rfl⟩) R38333
theorem R69457 : Reach 69457 := rs (se 2 (by rfl) ⟨26046, by rfl⟩) R52093
theorem R36769 : Reach 36769 := rs (se 2 (by rfl) ⟨13788, by rfl⟩) R27577
theorem R36865 : Reach 36865 := rs (se 2 (by rfl) ⟨13824, by rfl⟩) R27649
theorem R36931 : Reach 36931 := rs (se 1 (by rfl) ⟨27698, by rfl⟩) R55397
theorem R135245 : Reach 135245 := rs (se 3 (by rfl) ⟨25358, by rfl⟩) R50717
theorem R69713 : Reach 69713 := rs (se 2 (by rfl) ⟨26142, by rfl⟩) R52285
theorem R69731 : Reach 69731 := rs (se 1 (by rfl) ⟨52298, by rfl⟩) R104597
theorem R37027 : Reach 37027 := rs (se 1 (by rfl) ⟨27770, by rfl⟩) R55541
theorem R69923 : Reach 69923 := rs (se 1 (by rfl) ⟨52442, by rfl⟩) R104885
theorem R70001 : Reach 70001 := rs (se 2 (by rfl) ⟨26250, by rfl⟩) R52501
theorem R135587 : Reach 135587 := rs (se 1 (by rfl) ⟨101690, by rfl⟩) R203381
theorem R266723 : Reach 266723 := rs (se 1 (by rfl) ⟨200042, by rfl⟩) R400085
theorem R37361 : Reach 37361 := rs (se 2 (by rfl) ⟨14010, by rfl⟩) R28021
theorem R168581 : Reach 168581 := rs (se 4 (by rfl) ⟨15804, by rfl⟩) R31609
theorem R37523 : Reach 37523 := rs (se 1 (by rfl) ⟨28142, by rfl⟩) R56285
theorem R70321 : Reach 70321 := rs (se 2 (by rfl) ⟨26370, by rfl⟩) R52741
theorem R103139 : Reach 103139 := rs (se 1 (by rfl) ⟨77354, by rfl⟩) R154709
theorem R103153 : Reach 103153 := rs (se 2 (by rfl) ⟨38682, by rfl⟩) R77365
theorem R70417 : Reach 70417 := rs (se 2 (by rfl) ⟨26406, by rfl⟩) R52813
theorem R103409 : Reach 103409 := rs (se 2 (by rfl) ⟨38778, by rfl⟩) R77557
theorem R169037 : Reach 169037 := rs (se 3 (by rfl) ⟨31694, by rfl⟩) R63389
theorem R38065 : Reach 38065 := rs (se 2 (by rfl) ⟨14274, by rfl⟩) R28549
theorem R70865 : Reach 70865 := rs (se 2 (by rfl) ⟨26574, by rfl⟩) R53149
theorem R234737 : Reach 234737 := rs (se 2 (by rfl) ⟨88026, by rfl⟩) R176053
theorem R70915 : Reach 70915 := rs (se 1 (by rfl) ⟨53186, by rfl⟩) R106373
theorem R38161 : Reach 38161 := rs (se 2 (by rfl) ⟨14310, by rfl⟩) R28621
theorem R38227 : Reach 38227 := rs (se 1 (by rfl) ⟨28670, by rfl⟩) R57341
theorem R71057 : Reach 71057 := rs (se 2 (by rfl) ⟨26646, by rfl⟩) R53293
theorem R38323 : Reach 38323 := rs (se 1 (by rfl) ⟨28742, by rfl⟩) R57485
theorem R103949 : Reach 103949 := rs (se 3 (by rfl) ⟨19490, by rfl⟩) R38981
theorem R366277 : Reach 366277 := rs (se 4 (by rfl) ⟨34338, by rfl⟩) R68677
theorem R38657 : Reach 38657 := rs (se 2 (by rfl) ⟨14496, by rfl⟩) R28993
theorem R71459 : Reach 71459 := rs (se 1 (by rfl) ⟨53594, by rfl⟩) R107189
theorem R71491 : Reach 71491 := rs (se 1 (by rfl) ⟨53618, by rfl⟩) R107237
theorem R38819 : Reach 38819 := rs (se 1 (by rfl) ⟨29114, by rfl⟩) R58229
theorem R104611 : Reach 104611 := rs (se 1 (by rfl) ⟨78458, by rfl⟩) R156917
theorem R72049 : Reach 72049 := rs (se 2 (by rfl) ⟨27018, by rfl⟩) R54037
theorem R170381 : Reach 170381 := rs (se 3 (by rfl) ⟨31946, by rfl⟩) R63893
theorem R104867 : Reach 104867 := rs (se 1 (by rfl) ⟨78650, by rfl⟩) R157301
theorem R39361 : Reach 39361 := rs (se 2 (by rfl) ⟨14760, by rfl⟩) R29521
theorem R137699 : Reach 137699 := rs (se 1 (by rfl) ⟨103274, by rfl⟩) R206549
theorem R39443 : Reach 39443 := rs (se 1 (by rfl) ⟨29582, by rfl⟩) R59165
theorem R39457 : Reach 39457 := rs (se 2 (by rfl) ⟨14796, by rfl⟩) R29593
theorem R72323 : Reach 72323 := rs (se 1 (by rfl) ⟨54242, by rfl⟩) R108485
theorem R137933 : Reach 137933 := rs (se 3 (by rfl) ⟨25862, by rfl⟩) R51725
theorem R72515 : Reach 72515 := rs (se 1 (by rfl) ⟨54386, by rfl⟩) R108773
theorem R39953 : Reach 39953 := rs (se 2 (by rfl) ⟨14982, by rfl⟩) R29965
theorem R138509 : Reach 138509 := rs (se 3 (by rfl) ⟨25970, by rfl⟩) R51941
theorem R73133 : Reach 73133 := rs (se 3 (by rfl) ⟨13712, by rfl⟩) R27425
theorem R106019 : Reach 106019 := rs (se 1 (by rfl) ⟨79514, by rfl⟩) R159029
theorem R40547 : Reach 40547 := rs (se 1 (by rfl) ⟨30410, by rfl⟩) R60821
theorem R73325 : Reach 73325 := rs (se 3 (by rfl) ⟨13748, by rfl⟩) R27497
theorem R40673 : Reach 40673 := rs (se 2 (by rfl) ⟨15252, by rfl⟩) R30505
theorem R73457 : Reach 73457 := rs (se 2 (by rfl) ⟨27546, by rfl⟩) R55093
theorem R40691 : Reach 40691 := rs (se 1 (by rfl) ⟨30518, by rfl⟩) R61037
theorem R40721 : Reach 40721 := rs (se 2 (by rfl) ⟨15270, by rfl⟩) R30541
theorem R40739 : Reach 40739 := rs (se 1 (by rfl) ⟨30554, by rfl⟩) R61109
theorem R73507 : Reach 73507 := rs (se 1 (by rfl) ⟨55130, by rfl⟩) R110261
theorem R40769 : Reach 40769 := rs (se 2 (by rfl) ⟨15288, by rfl⟩) R30577
theorem R40787 : Reach 40787 := rs (se 1 (by rfl) ⟨30590, by rfl⟩) R61181
theorem R204643 : Reach 204643 := rs (se 1 (by rfl) ⟨153482, by rfl⟩) R306965
theorem R40817 : Reach 40817 := rs (se 2 (by rfl) ⟨15306, by rfl⟩) R30613
theorem R40819 : Reach 40819 := rs (se 1 (by rfl) ⟨30614, by rfl⟩) R61229
theorem R40835 : Reach 40835 := rs (se 1 (by rfl) ⟨30626, by rfl⟩) R61253
theorem R40865 : Reach 40865 := rs (se 2 (by rfl) ⟨15324, by rfl⟩) R30649
theorem R171953 : Reach 171953 := rs (se 2 (by rfl) ⟨64482, by rfl⟩) R128965
theorem R73649 : Reach 73649 := rs (se 2 (by rfl) ⟨27618, by rfl⟩) R55237
theorem R40883 : Reach 40883 := rs (se 1 (by rfl) ⟨30662, by rfl⟩) R61325
theorem R40913 : Reach 40913 := rs (se 2 (by rfl) ⟨15342, by rfl⟩) R30685
theorem R40915 : Reach 40915 := rs (se 1 (by rfl) ⟨30686, by rfl⟩) R61373
theorem R40931 : Reach 40931 := rs (se 1 (by rfl) ⟨30698, by rfl⟩) R61397
theorem R40961 : Reach 40961 := rs (se 2 (by rfl) ⟨15360, by rfl⟩) R30721
theorem R40979 : Reach 40979 := rs (se 1 (by rfl) ⟨30734, by rfl⟩) R61469
theorem R41009 : Reach 41009 := rs (se 2 (by rfl) ⟨15378, by rfl⟩) R30757
theorem R41027 : Reach 41027 := rs (se 1 (by rfl) ⟨30770, by rfl⟩) R61541
theorem R41057 : Reach 41057 := rs (se 2 (by rfl) ⟨15396, by rfl⟩) R30793
theorem R41075 : Reach 41075 := rs (se 1 (by rfl) ⟨30806, by rfl⟩) R61613
theorem R41105 : Reach 41105 := rs (se 2 (by rfl) ⟨15414, by rfl⟩) R30829
theorem R41123 : Reach 41123 := rs (se 1 (by rfl) ⟨30842, by rfl⟩) R61685
theorem R41153 : Reach 41153 := rs (se 2 (by rfl) ⟨15432, by rfl⟩) R30865
theorem R41171 : Reach 41171 := rs (se 1 (by rfl) ⟨30878, by rfl⟩) R61757
theorem R41201 : Reach 41201 := rs (se 2 (by rfl) ⟨15450, by rfl⟩) R30901
theorem R41219 : Reach 41219 := rs (se 1 (by rfl) ⟨30914, by rfl⟩) R61829
theorem R41249 : Reach 41249 := rs (se 2 (by rfl) ⟨15468, by rfl⟩) R30937
theorem R41267 : Reach 41267 := rs (se 1 (by rfl) ⟨30950, by rfl⟩) R61901
theorem R106829 : Reach 106829 := rs (se 3 (by rfl) ⟨20030, by rfl⟩) R40061
theorem R41297 : Reach 41297 := rs (se 2 (by rfl) ⟨15486, by rfl⟩) R30973
theorem R41315 : Reach 41315 := rs (se 1 (by rfl) ⟨30986, by rfl⟩) R61973
theorem R41345 : Reach 41345 := rs (se 2 (by rfl) ⟨15504, by rfl⟩) R31009
theorem R41363 : Reach 41363 := rs (se 1 (by rfl) ⟨31022, by rfl⟩) R62045
theorem R41393 : Reach 41393 := rs (se 2 (by rfl) ⟨15522, by rfl⟩) R31045
theorem R41411 : Reach 41411 := rs (se 1 (by rfl) ⟨31058, by rfl⟩) R62117
theorem R41441 : Reach 41441 := rs (se 2 (by rfl) ⟨15540, by rfl⟩) R31081
theorem R41459 : Reach 41459 := rs (se 1 (by rfl) ⟨31094, by rfl⟩) R62189
theorem R41489 : Reach 41489 := rs (se 2 (by rfl) ⟨15558, by rfl⟩) R31117
theorem R41507 : Reach 41507 := rs (se 1 (by rfl) ⟨31130, by rfl⟩) R62261
theorem R41537 : Reach 41537 := rs (se 2 (by rfl) ⟨15576, by rfl⟩) R31153
theorem R74317 : Reach 74317 := rs (se 3 (by rfl) ⟨13934, by rfl⟩) R27869
theorem R41555 : Reach 41555 := rs (se 1 (by rfl) ⟨31166, by rfl⟩) R62333
theorem R41585 : Reach 41585 := rs (se 2 (by rfl) ⟨15594, by rfl⟩) R31189
theorem R41603 : Reach 41603 := rs (se 1 (by rfl) ⟨31202, by rfl⟩) R62405
theorem R41633 : Reach 41633 := rs (se 2 (by rfl) ⟨15612, by rfl⟩) R31225
theorem R41651 : Reach 41651 := rs (se 1 (by rfl) ⟨31238, by rfl⟩) R62477
theorem R41681 : Reach 41681 := rs (se 2 (by rfl) ⟨15630, by rfl⟩) R31261
theorem R41699 : Reach 41699 := rs (se 1 (by rfl) ⟨31274, by rfl⟩) R62549
theorem R41729 : Reach 41729 := rs (se 2 (by rfl) ⟨15648, by rfl⟩) R31297
theorem R41747 : Reach 41747 := rs (se 1 (by rfl) ⟨31310, by rfl⟩) R62621
theorem R41777 : Reach 41777 := rs (se 2 (by rfl) ⟨15666, by rfl⟩) R31333
theorem R41795 : Reach 41795 := rs (se 1 (by rfl) ⟨31346, by rfl⟩) R62693
theorem R41825 : Reach 41825 := rs (se 2 (by rfl) ⟨15684, by rfl⟩) R31369
theorem R41843 : Reach 41843 := rs (se 1 (by rfl) ⟨31382, by rfl⟩) R62765
theorem R41873 : Reach 41873 := rs (se 2 (by rfl) ⟨15702, by rfl⟩) R31405
theorem R74641 : Reach 74641 := rs (se 2 (by rfl) ⟨27990, by rfl⟩) R55981
theorem R41891 : Reach 41891 := rs (se 1 (by rfl) ⟨31418, by rfl⟩) R62837
theorem R41921 : Reach 41921 := rs (se 2 (by rfl) ⟨15720, by rfl⟩) R31441
theorem R41939 : Reach 41939 := rs (se 1 (by rfl) ⟨31454, by rfl⟩) R62909
theorem R41969 : Reach 41969 := rs (se 2 (by rfl) ⟨15738, by rfl⟩) R31477
theorem R41987 : Reach 41987 := rs (se 1 (by rfl) ⟨31490, by rfl⟩) R62981
theorem R42017 : Reach 42017 := rs (se 2 (by rfl) ⟨15756, by rfl⟩) R31513
theorem R42035 : Reach 42035 := rs (se 1 (by rfl) ⟨31526, by rfl⟩) R63053
theorem R42049 : Reach 42049 := rs (se 2 (by rfl) ⟨15768, by rfl⟩) R31537
theorem R42065 : Reach 42065 := rs (se 2 (by rfl) ⟨15774, by rfl⟩) R31549
theorem R42083 : Reach 42083 := rs (se 1 (by rfl) ⟨31562, by rfl⟩) R63125
theorem R42113 : Reach 42113 := rs (se 2 (by rfl) ⟨15792, by rfl⟩) R31585
theorem R42131 : Reach 42131 := rs (se 1 (by rfl) ⟨31598, by rfl⟩) R63197
theorem R74915 : Reach 74915 := rs (se 1 (by rfl) ⟨56186, by rfl⟩) R112373
theorem R42161 : Reach 42161 := rs (se 2 (by rfl) ⟨15810, by rfl⟩) R31621
theorem R42179 : Reach 42179 := rs (se 1 (by rfl) ⟨31634, by rfl⟩) R63269
theorem R42209 : Reach 42209 := rs (se 2 (by rfl) ⟨15828, by rfl⟩) R31657
theorem R42227 : Reach 42227 := rs (se 1 (by rfl) ⟨31670, by rfl⟩) R63341
theorem R42257 : Reach 42257 := rs (se 2 (by rfl) ⟨15846, by rfl⟩) R31693
theorem R42275 : Reach 42275 := rs (se 1 (by rfl) ⟨31706, by rfl⟩) R63413
theorem R42305 : Reach 42305 := rs (se 2 (by rfl) ⟨15864, by rfl⟩) R31729
theorem R42323 : Reach 42323 := rs (se 1 (by rfl) ⟨31742, by rfl⟩) R63485
theorem R75107 : Reach 75107 := rs (se 1 (by rfl) ⟨56330, by rfl⟩) R112661
theorem R173411 : Reach 173411 := rs (se 1 (by rfl) ⟨130058, by rfl⟩) R260117
theorem R42353 : Reach 42353 := rs (se 2 (by rfl) ⟨15882, by rfl⟩) R31765
theorem R42371 : Reach 42371 := rs (se 1 (by rfl) ⟨31778, by rfl⟩) R63557
theorem R42385 : Reach 42385 := rs (se 2 (by rfl) ⟨15894, by rfl⟩) R31789
theorem R42401 : Reach 42401 := rs (se 2 (by rfl) ⟨15900, by rfl⟩) R31801
theorem R42419 : Reach 42419 := rs (se 1 (by rfl) ⟨31814, by rfl⟩) R63629
theorem R42449 : Reach 42449 := rs (se 2 (by rfl) ⟨15918, by rfl⟩) R31837
theorem R42467 : Reach 42467 := rs (se 1 (by rfl) ⟨31850, by rfl⟩) R63701
theorem R42497 : Reach 42497 := rs (se 2 (by rfl) ⟨15936, by rfl⟩) R31873
theorem R42515 : Reach 42515 := rs (se 1 (by rfl) ⟨31886, by rfl⟩) R63773
theorem R42545 : Reach 42545 := rs (se 2 (by rfl) ⟨15954, by rfl⟩) R31909
theorem R42563 : Reach 42563 := rs (se 1 (by rfl) ⟨31922, by rfl⟩) R63845
theorem R42593 : Reach 42593 := rs (se 2 (by rfl) ⟨15972, by rfl⟩) R31945
theorem R42611 : Reach 42611 := rs (se 1 (by rfl) ⟨31958, by rfl⟩) R63917
theorem R42641 : Reach 42641 := rs (se 2 (by rfl) ⟨15990, by rfl⟩) R31981
theorem R42659 : Reach 42659 := rs (se 1 (by rfl) ⟨31994, by rfl⟩) R63989
theorem R42689 : Reach 42689 := rs (se 2 (by rfl) ⟨16008, by rfl⟩) R32017
theorem R173765 : Reach 173765 := rs (se 4 (by rfl) ⟨16290, by rfl⟩) R32581
theorem R42707 : Reach 42707 := rs (se 1 (by rfl) ⟨32030, by rfl⟩) R64061
theorem R42737 : Reach 42737 := rs (se 2 (by rfl) ⟨16026, by rfl⟩) R32053
theorem R42755 : Reach 42755 := rs (se 1 (by rfl) ⟨32066, by rfl⟩) R64133
theorem R42785 : Reach 42785 := rs (se 2 (by rfl) ⟨16044, by rfl⟩) R32089
theorem R42803 : Reach 42803 := rs (se 1 (by rfl) ⟨32102, by rfl⟩) R64205
theorem R42817 : Reach 42817 := rs (se 2 (by rfl) ⟨16056, by rfl⟩) R32113
theorem R42833 : Reach 42833 := rs (se 2 (by rfl) ⟨16062, by rfl⟩) R32125
theorem R42851 : Reach 42851 := rs (se 1 (by rfl) ⟨32138, by rfl⟩) R64277
theorem R42881 : Reach 42881 := rs (se 2 (by rfl) ⟨16080, by rfl⟩) R32161
theorem R42899 : Reach 42899 := rs (se 1 (by rfl) ⟨32174, by rfl⟩) R64349
theorem R42929 : Reach 42929 := rs (se 2 (by rfl) ⟨16098, by rfl⟩) R32197
theorem R42947 : Reach 42947 := rs (se 1 (by rfl) ⟨32210, by rfl⟩) R64421
theorem R337861 : Reach 337861 := rs (se 4 (by rfl) ⟨31674, by rfl⟩) R63349
theorem R75725 : Reach 75725 := rs (se 3 (by rfl) ⟨14198, by rfl⟩) R28397
theorem R42977 : Reach 42977 := rs (se 2 (by rfl) ⟨16116, by rfl⟩) R32233
theorem R75757 : Reach 75757 := rs (se 3 (by rfl) ⟨14204, by rfl⟩) R28409
theorem R42995 : Reach 42995 := rs (se 1 (by rfl) ⟨32246, by rfl⟩) R64493
theorem R43025 : Reach 43025 := rs (se 2 (by rfl) ⟨16134, by rfl⟩) R32269
theorem R43043 : Reach 43043 := rs (se 1 (by rfl) ⟨32282, by rfl⟩) R64565
theorem R43073 : Reach 43073 := rs (se 2 (by rfl) ⟨16152, by rfl⟩) R32305
theorem R43091 : Reach 43091 := rs (se 1 (by rfl) ⟨32318, by rfl⟩) R64637
theorem R141425 : Reach 141425 := rs (se 2 (by rfl) ⟨53034, by rfl⟩) R106069
theorem R43121 : Reach 43121 := rs (se 2 (by rfl) ⟨16170, by rfl⟩) R32341
theorem R43139 : Reach 43139 := rs (se 1 (by rfl) ⟨32354, by rfl⟩) R64709
theorem R75917 : Reach 75917 := rs (se 3 (by rfl) ⟨14234, by rfl⟩) R28469
theorem R43169 : Reach 43169 := rs (se 2 (by rfl) ⟨16188, by rfl⟩) R32377
theorem R43187 : Reach 43187 := rs (se 1 (by rfl) ⟨32390, by rfl⟩) R64781
theorem R43217 : Reach 43217 := rs (se 2 (by rfl) ⟨16206, by rfl⟩) R32413
theorem R43235 : Reach 43235 := rs (se 1 (by rfl) ⟨32426, by rfl⟩) R64853
theorem R43265 : Reach 43265 := rs (se 2 (by rfl) ⟨16224, by rfl⟩) R32449
theorem R76049 : Reach 76049 := rs (se 2 (by rfl) ⟨28518, by rfl⟩) R57037
theorem R43283 : Reach 43283 := rs (se 1 (by rfl) ⟨32462, by rfl⟩) R64925
theorem R43313 : Reach 43313 := rs (se 2 (by rfl) ⟨16242, by rfl⟩) R32485
theorem R43331 : Reach 43331 := rs (se 1 (by rfl) ⟨32498, by rfl⟩) R64997
theorem R76099 : Reach 76099 := rs (se 1 (by rfl) ⟨57074, by rfl⟩) R114149
theorem R174413 : Reach 174413 := rs (se 3 (by rfl) ⟨32702, by rfl⟩) R65405
theorem R43361 : Reach 43361 := rs (se 2 (by rfl) ⟨16260, by rfl⟩) R32521
theorem R43379 : Reach 43379 := rs (se 1 (by rfl) ⟨32534, by rfl⟩) R65069
theorem R43409 : Reach 43409 := rs (se 2 (by rfl) ⟨16278, by rfl⟩) R32557
theorem R43427 : Reach 43427 := rs (se 1 (by rfl) ⟨32570, by rfl⟩) R65141
theorem R43457 : Reach 43457 := rs (se 2 (by rfl) ⟨16296, by rfl⟩) R32593
theorem R76241 : Reach 76241 := rs (se 2 (by rfl) ⟨28590, by rfl⟩) R57181
theorem R43475 : Reach 43475 := rs (se 1 (by rfl) ⟨32606, by rfl⟩) R65213
theorem R76259 : Reach 76259 := rs (se 1 (by rfl) ⟨57194, by rfl⟩) R114389
theorem R43505 : Reach 43505 := rs (se 2 (by rfl) ⟨16314, by rfl⟩) R32629
theorem R43507 : Reach 43507 := rs (se 1 (by rfl) ⟨32630, by rfl⟩) R65261
theorem R43523 : Reach 43523 := rs (se 1 (by rfl) ⟨32642, by rfl⟩) R65285
theorem R43553 : Reach 43553 := rs (se 2 (by rfl) ⟨16332, by rfl⟩) R32665
theorem R43571 : Reach 43571 := rs (se 1 (by rfl) ⟨32678, by rfl⟩) R65357
theorem R404021 : Reach 404021 := rs (se 5 (by rfl) ⟨18938, by rfl⟩) R37877
theorem R43601 : Reach 43601 := rs (se 2 (by rfl) ⟨16350, by rfl⟩) R32701
theorem R43619 : Reach 43619 := rs (se 1 (by rfl) ⟨32714, by rfl⟩) R65429
theorem R43649 : Reach 43649 := rs (se 2 (by rfl) ⟨16368, by rfl⟩) R32737
theorem R43667 : Reach 43667 := rs (se 1 (by rfl) ⟨32750, by rfl⟩) R65501
theorem R43697 : Reach 43697 := rs (se 2 (by rfl) ⟨16386, by rfl⟩) R32773
theorem R43715 : Reach 43715 := rs (se 1 (by rfl) ⟨32786, by rfl⟩) R65573
theorem R43745 : Reach 43745 := rs (se 2 (by rfl) ⟨16404, by rfl⟩) R32809
theorem R43763 : Reach 43763 := rs (se 1 (by rfl) ⟨32822, by rfl⟩) R65645
theorem R43793 : Reach 43793 := rs (se 2 (by rfl) ⟨16422, by rfl⟩) R32845
theorem R43811 : Reach 43811 := rs (se 1 (by rfl) ⟨32858, by rfl⟩) R65717
theorem R43841 : Reach 43841 := rs (se 2 (by rfl) ⟨16440, by rfl⟩) R32881
theorem R43843 : Reach 43843 := rs (se 1 (by rfl) ⟨32882, by rfl⟩) R65765
theorem R43859 : Reach 43859 := rs (se 1 (by rfl) ⟨32894, by rfl⟩) R65789
theorem R43889 : Reach 43889 := rs (se 2 (by rfl) ⟨16458, by rfl⟩) R32917
theorem R43907 : Reach 43907 := rs (se 1 (by rfl) ⟨32930, by rfl⟩) R65861
theorem R43937 : Reach 43937 := rs (se 2 (by rfl) ⟨16476, by rfl⟩) R32953
theorem R43955 : Reach 43955 := rs (se 1 (by rfl) ⟨32966, by rfl⟩) R65933
theorem R43985 : Reach 43985 := rs (se 2 (by rfl) ⟨16494, by rfl⟩) R32989
theorem R44003 : Reach 44003 := rs (se 1 (by rfl) ⟨33002, by rfl⟩) R66005
theorem R44033 : Reach 44033 := rs (se 2 (by rfl) ⟨16512, by rfl⟩) R33025
theorem R44051 : Reach 44051 := rs (se 1 (by rfl) ⟨33038, by rfl⟩) R66077
theorem R44081 : Reach 44081 := rs (se 2 (by rfl) ⟨16530, by rfl⟩) R33061
theorem R44099 : Reach 44099 := rs (se 1 (by rfl) ⟨33074, by rfl⟩) R66149
theorem R44129 : Reach 44129 := rs (se 2 (by rfl) ⟨16548, by rfl⟩) R33097
theorem R76909 : Reach 76909 := rs (se 3 (by rfl) ⟨14420, by rfl⟩) R28841
theorem R44147 : Reach 44147 := rs (se 1 (by rfl) ⟨33110, by rfl⟩) R66221
theorem R44177 : Reach 44177 := rs (se 2 (by rfl) ⟨16566, by rfl⟩) R33133
theorem R44195 : Reach 44195 := rs (se 1 (by rfl) ⟨33146, by rfl⟩) R66293
theorem R109745 : Reach 109745 := rs (se 2 (by rfl) ⟨41154, by rfl⟩) R82309
theorem R44225 : Reach 44225 := rs (se 2 (by rfl) ⟨16584, by rfl⟩) R33169
theorem R44243 : Reach 44243 := rs (se 1 (by rfl) ⟨33182, by rfl⟩) R66365
theorem R44273 : Reach 44273 := rs (se 2 (by rfl) ⟨16602, by rfl⟩) R33205
theorem R44291 : Reach 44291 := rs (se 1 (by rfl) ⟨33218, by rfl⟩) R66437
theorem R44321 : Reach 44321 := rs (se 2 (by rfl) ⟨16620, by rfl⟩) R33241
theorem R44339 : Reach 44339 := rs (se 1 (by rfl) ⟨33254, by rfl⟩) R66509
theorem R44369 : Reach 44369 := rs (se 2 (by rfl) ⟨16638, by rfl⟩) R33277
theorem R44387 : Reach 44387 := rs (se 1 (by rfl) ⟨33290, by rfl⟩) R66581
theorem R44417 : Reach 44417 := rs (se 2 (by rfl) ⟨16656, by rfl⟩) R33313
theorem R44435 : Reach 44435 := rs (se 1 (by rfl) ⟨33326, by rfl⟩) R66653
theorem R44465 : Reach 44465 := rs (se 2 (by rfl) ⟨16674, by rfl⟩) R33349
theorem R77233 : Reach 77233 := rs (se 2 (by rfl) ⟨28962, by rfl⟩) R57925
theorem R44483 : Reach 44483 := rs (se 1 (by rfl) ⟨33362, by rfl⟩) R66725
theorem R44513 : Reach 44513 := rs (se 2 (by rfl) ⟨16692, by rfl⟩) R33385
theorem R44531 : Reach 44531 := rs (se 1 (by rfl) ⟨33398, by rfl⟩) R66797
theorem R44545 : Reach 44545 := rs (se 2 (by rfl) ⟨16704, by rfl⟩) R33409
theorem R44561 : Reach 44561 := rs (se 2 (by rfl) ⟨16710, by rfl⟩) R33421
theorem R142883 : Reach 142883 := rs (se 1 (by rfl) ⟨107162, by rfl⟩) R214325
theorem R44579 : Reach 44579 := rs (se 1 (by rfl) ⟨33434, by rfl⟩) R66869
theorem R44609 : Reach 44609 := rs (se 2 (by rfl) ⟨16728, by rfl⟩) R33457
theorem R44627 : Reach 44627 := rs (se 1 (by rfl) ⟨33470, by rfl⟩) R66941
theorem R77411 : Reach 77411 := rs (se 1 (by rfl) ⟨58058, by rfl⟩) R116117
theorem R44657 : Reach 44657 := rs (se 2 (by rfl) ⟨16746, by rfl⟩) R33493
theorem R44659 : Reach 44659 := rs (se 1 (by rfl) ⟨33494, by rfl⟩) R66989
theorem R44675 : Reach 44675 := rs (se 1 (by rfl) ⟨33506, by rfl⟩) R67013
theorem R44705 : Reach 44705 := rs (se 2 (by rfl) ⟨16764, by rfl⟩) R33529
theorem R44723 : Reach 44723 := rs (se 1 (by rfl) ⟨33542, by rfl⟩) R67085
theorem R77507 : Reach 77507 := rs (se 1 (by rfl) ⟨58130, by rfl⟩) R116261
theorem R44753 : Reach 44753 := rs (se 2 (by rfl) ⟨16782, by rfl⟩) R33565
theorem R44771 : Reach 44771 := rs (se 1 (by rfl) ⟨33578, by rfl⟩) R67157
theorem R44801 : Reach 44801 := rs (se 2 (by rfl) ⟨16800, by rfl⟩) R33601
theorem R44819 : Reach 44819 := rs (se 1 (by rfl) ⟨33614, by rfl⟩) R67229
theorem R143153 : Reach 143153 := rs (se 2 (by rfl) ⟨53682, by rfl⟩) R107365
theorem R44849 : Reach 44849 := rs (se 2 (by rfl) ⟨16818, by rfl⟩) R33637
theorem R44867 : Reach 44867 := rs (se 1 (by rfl) ⟨33650, by rfl⟩) R67301
theorem R44897 : Reach 44897 := rs (se 2 (by rfl) ⟨16836, by rfl⟩) R33673
theorem R143203 : Reach 143203 := rs (se 1 (by rfl) ⟨107402, by rfl⟩) R214805
theorem R44915 : Reach 44915 := rs (se 1 (by rfl) ⟨33686, by rfl⟩) R67373
theorem R77699 : Reach 77699 := rs (se 1 (by rfl) ⟨58274, by rfl⟩) R116549
theorem R44945 : Reach 44945 := rs (se 2 (by rfl) ⟨16854, by rfl⟩) R33709
theorem R44963 : Reach 44963 := rs (se 1 (by rfl) ⟨33722, by rfl⟩) R67445
theorem R44993 : Reach 44993 := rs (se 2 (by rfl) ⟨16872, by rfl⟩) R33745
theorem R45011 : Reach 45011 := rs (se 1 (by rfl) ⟨33758, by rfl⟩) R67517
theorem R45041 : Reach 45041 := rs (se 2 (by rfl) ⟨16890, by rfl⟩) R33781
theorem R45059 : Reach 45059 := rs (se 1 (by rfl) ⟨33794, by rfl⟩) R67589
theorem R45089 : Reach 45089 := rs (se 2 (by rfl) ⟨16908, by rfl⟩) R33817
theorem R45107 : Reach 45107 := rs (se 1 (by rfl) ⟨33830, by rfl⟩) R67661
theorem R45137 : Reach 45137 := rs (se 2 (by rfl) ⟨16926, by rfl⟩) R33853
theorem R45155 : Reach 45155 := rs (se 1 (by rfl) ⟨33866, by rfl⟩) R67733
theorem R45185 : Reach 45185 := rs (se 2 (by rfl) ⟨16944, by rfl⟩) R33889
theorem R45203 : Reach 45203 := rs (se 1 (by rfl) ⟨33902, by rfl⟩) R67805
theorem R45233 : Reach 45233 := rs (se 2 (by rfl) ⟨16962, by rfl⟩) R33925
theorem R45251 : Reach 45251 := rs (se 1 (by rfl) ⟨33938, by rfl⟩) R67877
theorem R45281 : Reach 45281 := rs (se 2 (by rfl) ⟨16980, by rfl⟩) R33961
theorem R45299 : Reach 45299 := rs (se 1 (by rfl) ⟨33974, by rfl⟩) R67949
theorem R45329 : Reach 45329 := rs (se 2 (by rfl) ⟨16998, by rfl⟩) R33997
theorem R45347 : Reach 45347 := rs (se 1 (by rfl) ⟨34010, by rfl⟩) R68021
theorem R45377 : Reach 45377 := rs (se 2 (by rfl) ⟨17016, by rfl⟩) R34033
theorem R143693 : Reach 143693 := rs (se 3 (by rfl) ⟨26942, by rfl⟩) R53885
theorem R45395 : Reach 45395 := rs (se 1 (by rfl) ⟨34046, by rfl⟩) R68093
theorem R45425 : Reach 45425 := rs (se 2 (by rfl) ⟨17034, by rfl⟩) R34069
theorem R45443 : Reach 45443 := rs (se 1 (by rfl) ⟨34082, by rfl⟩) R68165
theorem R45473 : Reach 45473 := rs (se 2 (by rfl) ⟨17052, by rfl⟩) R34105
theorem R45491 : Reach 45491 := rs (se 1 (by rfl) ⟨34118, by rfl⟩) R68237
theorem R45521 : Reach 45521 := rs (se 2 (by rfl) ⟨17070, by rfl⟩) R34141
theorem R45539 : Reach 45539 := rs (se 1 (by rfl) ⟨34154, by rfl⟩) R68309
theorem R78317 : Reach 78317 := rs (se 3 (by rfl) ⟨14684, by rfl⟩) R29369
theorem R45569 : Reach 45569 := rs (se 2 (by rfl) ⟨17088, by rfl⟩) R34177
theorem R45587 : Reach 45587 := rs (se 1 (by rfl) ⟨34190, by rfl⟩) R68381
theorem R45617 : Reach 45617 := rs (se 2 (by rfl) ⟨17106, by rfl⟩) R34213
theorem R45635 : Reach 45635 := rs (se 1 (by rfl) ⟨34226, by rfl⟩) R68453
theorem R45665 : Reach 45665 := rs (se 2 (by rfl) ⟨17124, by rfl⟩) R34249
theorem R111203 : Reach 111203 := rs (se 1 (by rfl) ⟨83402, by rfl⟩) R166805
theorem R45683 : Reach 45683 := rs (se 1 (by rfl) ⟨34262, by rfl⟩) R68525
theorem R45697 : Reach 45697 := rs (se 2 (by rfl) ⟨17136, by rfl⟩) R34273
theorem R45713 : Reach 45713 := rs (se 2 (by rfl) ⟨17142, by rfl⟩) R34285
theorem R45731 : Reach 45731 := rs (se 1 (by rfl) ⟨34298, by rfl⟩) R68597
theorem R78509 : Reach 78509 := rs (se 3 (by rfl) ⟨14720, by rfl⟩) R29441
theorem R45761 : Reach 45761 := rs (se 2 (by rfl) ⟨17160, by rfl⟩) R34321
theorem R45779 : Reach 45779 := rs (se 1 (by rfl) ⟨34334, by rfl⟩) R68669
theorem R45809 : Reach 45809 := rs (se 2 (by rfl) ⟨17178, by rfl⟩) R34357
theorem R45827 : Reach 45827 := rs (se 1 (by rfl) ⟨34370, by rfl⟩) R68741
theorem R45857 : Reach 45857 := rs (se 2 (by rfl) ⟨17196, by rfl⟩) R34393
theorem R45859 : Reach 45859 := rs (se 1 (by rfl) ⟨34394, by rfl⟩) R68789
theorem R78641 : Reach 78641 := rs (se 2 (by rfl) ⟨29490, by rfl⟩) R58981
theorem R45875 : Reach 45875 := rs (se 1 (by rfl) ⟨34406, by rfl⟩) R68813
theorem R45905 : Reach 45905 := rs (se 2 (by rfl) ⟨17214, by rfl⟩) R34429
theorem R45923 : Reach 45923 := rs (se 1 (by rfl) ⟨34442, by rfl⟩) R68885
theorem R78691 : Reach 78691 := rs (se 1 (by rfl) ⟨59018, by rfl⟩) R118037
theorem R45953 : Reach 45953 := rs (se 2 (by rfl) ⟨17232, by rfl⟩) R34465
theorem R45971 : Reach 45971 := rs (se 1 (by rfl) ⟨34478, by rfl⟩) R68957
theorem R46001 : Reach 46001 := rs (se 2 (by rfl) ⟨17250, by rfl⟩) R34501
theorem R46019 : Reach 46019 := rs (se 1 (by rfl) ⟨34514, by rfl⟩) R69029
theorem R46049 : Reach 46049 := rs (se 2 (by rfl) ⟨17268, by rfl⟩) R34537
theorem R46067 : Reach 46067 := rs (se 1 (by rfl) ⟨34550, by rfl⟩) R69101
theorem R46097 : Reach 46097 := rs (se 2 (by rfl) ⟨17286, by rfl⟩) R34573
theorem R46115 : Reach 46115 := rs (se 1 (by rfl) ⟨34586, by rfl⟩) R69173
theorem R46129 : Reach 46129 := rs (se 2 (by rfl) ⟨17298, by rfl⟩) R34597
theorem R144433 : Reach 144433 := rs (se 2 (by rfl) ⟨54162, by rfl⟩) R108325
theorem R46145 : Reach 46145 := rs (se 2 (by rfl) ⟨17304, by rfl⟩) R34609
theorem R46163 : Reach 46163 := rs (se 1 (by rfl) ⟨34622, by rfl⟩) R69245
theorem R46193 : Reach 46193 := rs (se 2 (by rfl) ⟨17322, by rfl⟩) R34645
theorem R46211 : Reach 46211 := rs (se 1 (by rfl) ⟨34658, by rfl⟩) R69317
theorem R46241 : Reach 46241 := rs (se 2 (by rfl) ⟨17340, by rfl⟩) R34681
theorem R177329 : Reach 177329 := rs (se 2 (by rfl) ⟨66498, by rfl⟩) R132997
theorem R46259 : Reach 46259 := rs (se 1 (by rfl) ⟨34694, by rfl⟩) R69389
theorem R177349 : Reach 177349 := rs (se 4 (by rfl) ⟨16626, by rfl⟩) R33253
theorem R46289 : Reach 46289 := rs (se 2 (by rfl) ⟨17358, by rfl⟩) R34717
theorem R46291 : Reach 46291 := rs (se 1 (by rfl) ⟨34718, by rfl⟩) R69437
theorem R46307 : Reach 46307 := rs (se 1 (by rfl) ⟨34730, by rfl⟩) R69461
theorem R46337 : Reach 46337 := rs (se 2 (by rfl) ⟨17376, by rfl⟩) R34753
theorem R46355 : Reach 46355 := rs (se 1 (by rfl) ⟨34766, by rfl⟩) R69533
theorem R46385 : Reach 46385 := rs (se 2 (by rfl) ⟨17394, by rfl⟩) R34789
theorem R46403 : Reach 46403 := rs (se 1 (by rfl) ⟨34802, by rfl⟩) R69605
theorem R46433 : Reach 46433 := rs (se 2 (by rfl) ⟨17412, by rfl⟩) R34825
theorem R46451 : Reach 46451 := rs (se 1 (by rfl) ⟨34838, by rfl⟩) R69677
theorem R46481 : Reach 46481 := rs (se 2 (by rfl) ⟨17430, by rfl⟩) R34861
theorem R46499 : Reach 46499 := rs (se 1 (by rfl) ⟨34874, by rfl⟩) R69749
theorem R46529 : Reach 46529 := rs (se 2 (by rfl) ⟨17448, by rfl⟩) R34897
theorem R79309 : Reach 79309 := rs (se 3 (by rfl) ⟨14870, by rfl⟩) R29741
theorem R46547 : Reach 46547 := rs (se 1 (by rfl) ⟨34910, by rfl⟩) R69821
theorem R46561 : Reach 46561 := rs (se 2 (by rfl) ⟨17460, by rfl⟩) R34921
theorem R46577 : Reach 46577 := rs (se 2 (by rfl) ⟨17466, by rfl⟩) R34933
theorem R341489 : Reach 341489 := rs (se 2 (by rfl) ⟨128058, by rfl⟩) R256117
theorem R46595 : Reach 46595 := rs (se 1 (by rfl) ⟨34946, by rfl⟩) R69893
theorem R46625 : Reach 46625 := rs (se 2 (by rfl) ⟨17484, by rfl⟩) R34969
theorem R46643 : Reach 46643 := rs (se 1 (by rfl) ⟨34982, by rfl⟩) R69965
theorem R112205 : Reach 112205 := rs (se 3 (by rfl) ⟨21038, by rfl⟩) R42077
theorem R46723 : Reach 46723 := rs (se 1 (by rfl) ⟨35042, by rfl⟩) R70085
theorem R46865 : Reach 46865 := rs (se 2 (by rfl) ⟨17574, by rfl⟩) R35149
theorem R46993 : Reach 46993 := rs (se 2 (by rfl) ⟨17622, by rfl⟩) R35245
theorem R47027 : Reach 47027 := rs (se 1 (by rfl) ⟨35270, by rfl⟩) R70541
theorem R374797 : Reach 374797 := rs (se 3 (by rfl) ⟨70274, by rfl⟩) R140549
theorem R47155 : Reach 47155 := rs (se 1 (by rfl) ⟨35366, by rfl⟩) R70733
theorem R47297 : Reach 47297 := rs (se 2 (by rfl) ⟨17736, by rfl⟩) R35473
theorem R80099 : Reach 80099 := rs (se 1 (by rfl) ⟨60074, by rfl⟩) R120149
theorem R47425 : Reach 47425 := rs (se 2 (by rfl) ⟨17784, by rfl⟩) R35569
theorem R47459 : Reach 47459 := rs (se 1 (by rfl) ⟨35594, by rfl⟩) R71189
theorem R47587 : Reach 47587 := rs (se 1 (by rfl) ⟨35690, by rfl⟩) R71381
theorem R178787 : Reach 178787 := rs (se 1 (by rfl) ⟨134090, by rfl⟩) R268181
theorem R47729 : Reach 47729 := rs (se 2 (by rfl) ⟨17898, by rfl⟩) R35797
theorem R47747 : Reach 47747 := rs (se 1 (by rfl) ⟨35810, by rfl⟩) R71621
theorem R47857 : Reach 47857 := rs (se 2 (by rfl) ⟨17946, by rfl⟩) R35893
theorem R47875 : Reach 47875 := rs (se 1 (by rfl) ⟨35906, by rfl⟩) R71813
theorem R47891 : Reach 47891 := rs (se 1 (by rfl) ⟨35918, by rfl⟩) R71837
theorem R244579 : Reach 244579 := rs (se 1 (by rfl) ⟨183434, by rfl⟩) R366869
theorem R48019 : Reach 48019 := rs (se 1 (by rfl) ⟨36014, by rfl⟩) R72029
theorem R80909 : Reach 80909 := rs (se 3 (by rfl) ⟨15170, by rfl⟩) R30341
theorem R48161 : Reach 48161 := rs (se 2 (by rfl) ⟨18060, by rfl⟩) R36121
theorem R80963 : Reach 80963 := rs (se 1 (by rfl) ⟨60722, by rfl⟩) R121445
theorem R146609 : Reach 146609 := rs (se 2 (by rfl) ⟨54978, by rfl⟩) R109957
theorem R48323 : Reach 48323 := rs (se 1 (by rfl) ⟨36242, by rfl⟩) R72485
theorem R81101 : Reach 81101 := rs (se 3 (by rfl) ⟨15206, by rfl⟩) R30413
theorem R48433 : Reach 48433 := rs (se 2 (by rfl) ⟨18162, by rfl⟩) R36325
theorem R48451 : Reach 48451 := rs (se 1 (by rfl) ⟨36338, by rfl⟩) R72677
theorem R48593 : Reach 48593 := rs (se 2 (by rfl) ⟨18222, by rfl⟩) R36445
theorem R48721 : Reach 48721 := rs (se 2 (by rfl) ⟨18270, by rfl⟩) R36541
theorem R114317 : Reach 114317 := rs (se 3 (by rfl) ⟨21434, by rfl⟩) R42869
theorem R114353 : Reach 114353 := rs (se 2 (by rfl) ⟨42882, by rfl⟩) R85765
theorem R474821 : Reach 474821 := rs (se 4 (by rfl) ⟨44514, by rfl⟩) R89029
theorem R48881 : Reach 48881 := rs (se 2 (by rfl) ⟨18330, by rfl⟩) R36661
theorem R442253 : Reach 442253 := rs (se 3 (by rfl) ⟨82922, by rfl⟩) R165845
theorem R49105 : Reach 49105 := rs (se 2 (by rfl) ⟨18414, by rfl⟩) R36829
theorem R49187 : Reach 49187 := rs (se 1 (by rfl) ⟨36890, by rfl⟩) R73781
theorem R49315 : Reach 49315 := rs (se 1 (by rfl) ⟨36986, by rfl⟩) R73973
theorem R82093 : Reach 82093 := rs (se 3 (by rfl) ⟨15392, by rfl⟩) R30785
theorem R49457 : Reach 49457 := rs (se 2 (by rfl) ⟨18546, by rfl⟩) R37093
theorem R147811 : Reach 147811 := rs (se 1 (by rfl) ⟨110858, by rfl⟩) R221717
theorem R115121 : Reach 115121 := rs (se 2 (by rfl) ⟨43170, by rfl⟩) R86341
theorem R49585 : Reach 49585 := rs (se 2 (by rfl) ⟨18594, by rfl⟩) R37189
theorem R148067 : Reach 148067 := rs (se 1 (by rfl) ⟨111050, by rfl⟩) R222101
theorem R148229 : Reach 148229 := rs (se 4 (by rfl) ⟨13896, by rfl⟩) R27793
theorem R50051 : Reach 50051 := rs (se 1 (by rfl) ⟨37538, by rfl⟩) R75077
theorem R50179 : Reach 50179 := rs (se 1 (by rfl) ⟨37634, by rfl⟩) R75269
theorem R115789 : Reach 115789 := rs (se 3 (by rfl) ⟨21710, by rfl⟩) R43421
theorem R50321 : Reach 50321 := rs (se 2 (by rfl) ⟨18870, by rfl⟩) R37741
theorem R181453 : Reach 181453 := rs (se 3 (by rfl) ⟨34022, by rfl⟩) R68045
theorem R214285 : Reach 214285 := rs (se 3 (by rfl) ⟨40178, by rfl⟩) R80357
theorem R83213 : Reach 83213 := rs (se 3 (by rfl) ⟨15602, by rfl⟩) R31205
theorem R50449 : Reach 50449 := rs (se 2 (by rfl) ⟨18918, by rfl⟩) R37837
theorem R181645 : Reach 181645 := rs (se 3 (by rfl) ⟨34058, by rfl⟩) R68117
theorem R148877 : Reach 148877 := rs (se 3 (by rfl) ⟨27914, by rfl⟩) R55829
theorem R50915 : Reach 50915 := rs (se 1 (by rfl) ⟨38186, by rfl⟩) R76373
theorem R116579 : Reach 116579 := rs (se 1 (by rfl) ⟨87434, by rfl⟩) R174869
theorem R51043 : Reach 51043 := rs (se 1 (by rfl) ⟨38282, by rfl⟩) R76565
theorem R83825 : Reach 83825 := rs (se 2 (by rfl) ⟨31434, by rfl⟩) R62869
theorem R51121 : Reach 51121 := rs (se 2 (by rfl) ⟨19170, by rfl⟩) R38341
theorem R51185 : Reach 51185 := rs (se 2 (by rfl) ⟨19194, by rfl⟩) R38389
theorem R84017 : Reach 84017 := rs (se 2 (by rfl) ⟨31506, by rfl⟩) R63013
theorem R51313 : Reach 51313 := rs (se 2 (by rfl) ⟨19242, by rfl⟩) R38485
theorem R149681 : Reach 149681 := rs (se 2 (by rfl) ⟨56130, by rfl⟩) R112261
theorem R51619 : Reach 51619 := rs (se 1 (by rfl) ⟨38714, by rfl⟩) R77429
theorem R117233 : Reach 117233 := rs (se 2 (by rfl) ⟨43962, by rfl⟩) R87925
theorem R51779 : Reach 51779 := rs (se 1 (by rfl) ⟨38834, by rfl⟩) R77669
theorem R51907 : Reach 51907 := rs (se 1 (by rfl) ⟨38930, by rfl⟩) R77861
theorem R52049 : Reach 52049 := rs (se 2 (by rfl) ⟨19518, by rfl⟩) R39037
theorem R84845 : Reach 84845 := rs (se 3 (by rfl) ⟨15908, by rfl⟩) R31817
theorem R52177 : Reach 52177 := rs (se 2 (by rfl) ⟨19566, by rfl⟩) R39133
theorem R85009 : Reach 85009 := rs (se 2 (by rfl) ⟨31878, by rfl⟩) R63757
theorem R281713 : Reach 281713 := rs (se 2 (by rfl) ⟨105642, by rfl⟩) R211285
theorem R85283 : Reach 85283 := rs (se 1 (by rfl) ⟨63962, by rfl⟩) R127925
theorem R52579 : Reach 52579 := rs (se 1 (by rfl) ⟨39434, by rfl⟩) R78869
theorem R52625 : Reach 52625 := rs (se 2 (by rfl) ⟨19734, by rfl⟩) R39469
theorem R52643 : Reach 52643 := rs (se 1 (by rfl) ⟨39482, by rfl⟩) R78965
theorem R85475 : Reach 85475 := rs (se 1 (by rfl) ⟨64106, by rfl⟩) R128213
theorem R151025 : Reach 151025 := rs (se 2 (by rfl) ⟨56634, by rfl⟩) R113269
theorem R52913 : Reach 52913 := rs (se 2 (by rfl) ⟨19842, by rfl⟩) R39685
theorem R1199843 : Reach 1199843 := rs (se 1 (by rfl) ⟨899882, by rfl⟩) R1799765
theorem R118577 : Reach 118577 := rs (se 2 (by rfl) ⟨44466, by rfl⟩) R88933
theorem R774197 : Reach 774197 := rs (se 5 (by rfl) ⟨36290, by rfl⟩) R72581
theorem R151793 : Reach 151793 := rs (se 2 (by rfl) ⟨56922, by rfl⟩) R113845
theorem R86285 : Reach 86285 := rs (se 3 (by rfl) ⟨16178, by rfl⟩) R32357
theorem R53635 : Reach 53635 := rs (se 1 (by rfl) ⟨40226, by rfl⟩) R80453
theorem R86467 : Reach 86467 := rs (se 1 (by rfl) ⟨64850, by rfl⟩) R129701
theorem R348785 : Reach 348785 := rs (se 2 (by rfl) ⟨130794, by rfl⟩) R261589
theorem R119501 : Reach 119501 := rs (se 3 (by rfl) ⟨22406, by rfl⟩) R44813
theorem R54083 : Reach 54083 := rs (se 1 (by rfl) ⟨40562, by rfl⟩) R81125
theorem R86957 : Reach 86957 := rs (se 3 (by rfl) ⟨16304, by rfl⟩) R32609
theorem R349109 : Reach 349109 := rs (se 5 (by rfl) ⟨16364, by rfl⟩) R32729
theorem R54371 : Reach 54371 := rs (se 1 (by rfl) ⟨40778, by rfl⟩) R81557
theorem R87473 : Reach 87473 := rs (se 2 (by rfl) ⟨32802, by rfl⟩) R65605
theorem R54737 : Reach 54737 := rs (se 2 (by rfl) ⟨20526, by rfl⟩) R41053
theorem R87601 : Reach 87601 := rs (se 2 (by rfl) ⟨32850, by rfl⟩) R65701
theorem R54883 : Reach 54883 := rs (se 1 (by rfl) ⟨41162, by rfl⟩) R82325
theorem R153251 : Reach 153251 := rs (se 1 (by rfl) ⟨114938, by rfl⟩) R229877
theorem R87857 : Reach 87857 := rs (se 2 (by rfl) ⟨32946, by rfl⟩) R65893
theorem R87875 : Reach 87875 := rs (se 1 (by rfl) ⟨65906, by rfl⟩) R131813
theorem R153413 : Reach 153413 := rs (se 4 (by rfl) ⟨14382, by rfl⟩) R28765
theorem R251747 : Reach 251747 := rs (se 1 (by rfl) ⟨188810, by rfl⟩) R377621
theorem R120781 : Reach 120781 := rs (se 3 (by rfl) ⟨22646, by rfl⟩) R45293
theorem R55313 : Reach 55313 := rs (se 2 (by rfl) ⟨20742, by rfl⟩) R41485
theorem R88141 : Reach 88141 := rs (se 3 (by rfl) ⟨16526, by rfl⟩) R33053
theorem R186545 : Reach 186545 := rs (se 2 (by rfl) ⟨69954, by rfl⟩) R139909
theorem R317621 : Reach 317621 := rs (se 5 (by rfl) ⟨14888, by rfl⟩) R29777
theorem R547013 : Reach 547013 := rs (se 4 (by rfl) ⟨51282, by rfl⟩) R102565
theorem R252173 : Reach 252173 := rs (se 3 (by rfl) ⟨47282, by rfl⟩) R94565
theorem R154061 : Reach 154061 := rs (se 3 (by rfl) ⟨28886, by rfl⟩) R57773
theorem R88771 : Reach 88771 := rs (se 1 (by rfl) ⟨66578, by rfl⟩) R133157
theorem R56209 : Reach 56209 := rs (se 2 (by rfl) ⟨21078, by rfl⟩) R42157
theorem R56369 : Reach 56369 := rs (se 2 (by rfl) ⟨21138, by rfl⟩) R42277
theorem R56771 : Reach 56771 := rs (se 1 (by rfl) ⟨42578, by rfl⟩) R85157
theorem R253381 : Reach 253381 := rs (se 4 (by rfl) ⟨23754, by rfl⟩) R47509
theorem R89549 : Reach 89549 := rs (se 3 (by rfl) ⟨16790, by rfl⟩) R33581
theorem R220643 : Reach 220643 := rs (se 1 (by rfl) ⟨165482, by rfl⟩) R330965
theorem R155141 : Reach 155141 := rs (se 4 (by rfl) ⟨14544, by rfl⟩) R29089
theorem R122609 : Reach 122609 := rs (se 2 (by rfl) ⟨45978, by rfl⟩) R91957
theorem R384821 : Reach 384821 := rs (se 5 (by rfl) ⟨18038, by rfl⟩) R36077
theorem R319301 : Reach 319301 := rs (se 4 (by rfl) ⟨29934, by rfl⟩) R59869
theorem R57187 : Reach 57187 := rs (se 1 (by rfl) ⟨42890, by rfl⟩) R85781
theorem R90317 : Reach 90317 := rs (se 3 (by rfl) ⟨16934, by rfl⟩) R33869
theorem R57667 : Reach 57667 := rs (se 1 (by rfl) ⟨43250, by rfl⟩) R86501
theorem R483725 : Reach 483725 := rs (se 3 (by rfl) ⟨90698, by rfl⟩) R181397
theorem R90563 : Reach 90563 := rs (se 1 (by rfl) ⟨67922, by rfl⟩) R135845
theorem R57827 : Reach 57827 := rs (se 1 (by rfl) ⟨43370, by rfl⟩) R86741
theorem R90829 : Reach 90829 := rs (se 3 (by rfl) ⟨17030, by rfl⟩) R34061
theorem R90989 : Reach 90989 := rs (se 3 (by rfl) ⟨17060, by rfl⟩) R34121
theorem R123875 : Reach 123875 := rs (se 1 (by rfl) ⟨92906, by rfl⟩) R185813
theorem R91331 : Reach 91331 := rs (se 1 (by rfl) ⟨68498, by rfl⟩) R136997
theorem R156977 : Reach 156977 := rs (se 2 (by rfl) ⟨58866, by rfl⟩) R117733
theorem R189859 : Reach 189859 := rs (se 1 (by rfl) ⟨142394, by rfl⟩) R284789
theorem R58801 : Reach 58801 := rs (se 2 (by rfl) ⟨22050, by rfl⟩) R44101
theorem R583109 : Reach 583109 := rs (se 4 (by rfl) ⟨54666, by rfl⟩) R109333
theorem R58897 : Reach 58897 := rs (se 2 (by rfl) ⟨22086, by rfl⟩) R44173
theorem R91853 : Reach 91853 := rs (se 3 (by rfl) ⟨17222, by rfl⟩) R34445
theorem R91907 : Reach 91907 := rs (se 1 (by rfl) ⟨68930, by rfl⟩) R137861
theorem R92177 : Reach 92177 := rs (se 2 (by rfl) ⟨34566, by rfl⟩) R69133
theorem R59459 : Reach 59459 := rs (se 1 (by rfl) ⟨44594, by rfl⟩) R89189
theorem R223685 : Reach 223685 := rs (se 4 (by rfl) ⟨20970, by rfl⟩) R41941
theorem R27123 : Reach 27123 := rs (se 1 (by rfl) ⟨20342, by rfl⟩) R40685
theorem R27139 : Reach 27139 := rs (se 1 (by rfl) ⟨20354, by rfl⟩) R40709
theorem R27155 : Reach 27155 := rs (se 1 (by rfl) ⟨20366, by rfl⟩) R40733
theorem R27171 : Reach 27171 := rs (se 1 (by rfl) ⟨20378, by rfl⟩) R40757
theorem R92717 : Reach 92717 := rs (se 3 (by rfl) ⟨17384, by rfl⟩) R34769
theorem R27187 : Reach 27187 := rs (se 1 (by rfl) ⟨20390, by rfl⟩) R40781
theorem R27203 : Reach 27203 := rs (se 1 (by rfl) ⟨20402, by rfl⟩) R40805
theorem R59971 : Reach 59971 := rs (se 1 (by rfl) ⟨44978, by rfl⟩) R89957
theorem R27219 : Reach 27219 := rs (se 1 (by rfl) ⟨20414, by rfl⟩) R40829
theorem R27235 : Reach 27235 := rs (se 1 (by rfl) ⟨20426, by rfl⟩) R40853
theorem R92771 : Reach 92771 := rs (se 1 (by rfl) ⟨69578, by rfl⟩) R139157
theorem R191089 : Reach 191089 := rs (se 2 (by rfl) ⟨71658, by rfl⟩) R143317
theorem R27251 : Reach 27251 := rs (se 1 (by rfl) ⟨20438, by rfl⟩) R40877
theorem R27267 : Reach 27267 := rs (se 1 (by rfl) ⟨20450, by rfl⟩) R40901
theorem R27283 : Reach 27283 := rs (se 1 (by rfl) ⟨20462, by rfl⟩) R40925
theorem R27299 : Reach 27299 := rs (se 1 (by rfl) ⟨20474, by rfl⟩) R40949
theorem R27315 : Reach 27315 := rs (se 1 (by rfl) ⟨20486, by rfl⟩) R40973
theorem R27331 : Reach 27331 := rs (se 1 (by rfl) ⟨20498, by rfl⟩) R40997
theorem R27347 : Reach 27347 := rs (se 1 (by rfl) ⟨20510, by rfl⟩) R41021
theorem R27363 : Reach 27363 := rs (se 1 (by rfl) ⟨20522, by rfl⟩) R41045
theorem R191203 : Reach 191203 := rs (se 1 (by rfl) ⟨143402, by rfl⟩) R286805
theorem R27379 : Reach 27379 := rs (se 1 (by rfl) ⟨20534, by rfl⟩) R41069
theorem R27395 : Reach 27395 := rs (se 1 (by rfl) ⟨20546, by rfl⟩) R41093
theorem R27411 : Reach 27411 := rs (se 1 (by rfl) ⟨20558, by rfl⟩) R41117
theorem R27427 : Reach 27427 := rs (se 1 (by rfl) ⟨20570, by rfl⟩) R41141
theorem R27443 : Reach 27443 := rs (se 1 (by rfl) ⟨20582, by rfl⟩) R41165
theorem R27459 : Reach 27459 := rs (se 1 (by rfl) ⟨20594, by rfl⟩) R41189
theorem R27475 : Reach 27475 := rs (se 1 (by rfl) ⟨20606, by rfl⟩) R41213
theorem R27491 : Reach 27491 := rs (se 1 (by rfl) ⟨20618, by rfl⟩) R41237
theorem R93041 : Reach 93041 := rs (se 2 (by rfl) ⟨34890, by rfl⟩) R69781
theorem R27507 : Reach 27507 := rs (se 1 (by rfl) ⟨20630, by rfl⟩) R41261
theorem R27523 : Reach 27523 := rs (se 1 (by rfl) ⟨20642, by rfl⟩) R41285
theorem R27539 : Reach 27539 := rs (se 1 (by rfl) ⟨20654, by rfl⟩) R41309
theorem R27555 : Reach 27555 := rs (se 1 (by rfl) ⟨20666, by rfl⟩) R41333
theorem R27571 : Reach 27571 := rs (se 1 (by rfl) ⟨20678, by rfl⟩) R41357
theorem R27587 : Reach 27587 := rs (se 1 (by rfl) ⟨20690, by rfl⟩) R41381
theorem R27603 : Reach 27603 := rs (se 1 (by rfl) ⟨20702, by rfl⟩) R41405
theorem R27619 : Reach 27619 := rs (se 1 (by rfl) ⟨20714, by rfl⟩) R41429
theorem R27635 : Reach 27635 := rs (se 1 (by rfl) ⟨20726, by rfl⟩) R41453
theorem R27651 : Reach 27651 := rs (se 1 (by rfl) ⟨20738, by rfl⟩) R41477
theorem R93187 : Reach 93187 := rs (se 1 (by rfl) ⟨69890, by rfl⟩) R139781
theorem R27667 : Reach 27667 := rs (se 1 (by rfl) ⟨20750, by rfl⟩) R41501
theorem R27683 : Reach 27683 := rs (se 1 (by rfl) ⟨20762, by rfl⟩) R41525
theorem R27699 : Reach 27699 := rs (se 1 (by rfl) ⟨20774, by rfl⟩) R41549
theorem R27715 : Reach 27715 := rs (se 1 (by rfl) ⟨20786, by rfl⟩) R41573
theorem R158797 : Reach 158797 := rs (se 3 (by rfl) ⟨29774, by rfl⟩) R59549
theorem R27731 : Reach 27731 := rs (se 1 (by rfl) ⟨20798, by rfl⟩) R41597
theorem R27747 : Reach 27747 := rs (se 1 (by rfl) ⟨20810, by rfl⟩) R41621
theorem R27763 : Reach 27763 := rs (se 1 (by rfl) ⟨20822, by rfl⟩) R41645
theorem R27779 : Reach 27779 := rs (se 1 (by rfl) ⟨20834, by rfl⟩) R41669
theorem R27795 : Reach 27795 := rs (se 1 (by rfl) ⟨20846, by rfl⟩) R41693
theorem R27811 : Reach 27811 := rs (se 1 (by rfl) ⟨20858, by rfl⟩) R41717
theorem R27827 : Reach 27827 := rs (se 1 (by rfl) ⟨20870, by rfl⟩) R41741
theorem R27843 : Reach 27843 := rs (se 1 (by rfl) ⟨20882, by rfl⟩) R41765
theorem R27859 : Reach 27859 := rs (se 1 (by rfl) ⟨20894, by rfl⟩) R41789
theorem R27875 : Reach 27875 := rs (se 1 (by rfl) ⟨20906, by rfl⟩) R41813
theorem R27891 : Reach 27891 := rs (se 1 (by rfl) ⟨20918, by rfl⟩) R41837
theorem R27907 : Reach 27907 := rs (se 1 (by rfl) ⟨20930, by rfl⟩) R41861
theorem R27923 : Reach 27923 := rs (se 1 (by rfl) ⟨20942, by rfl⟩) R41885
theorem R27939 : Reach 27939 := rs (se 1 (by rfl) ⟨20954, by rfl⟩) R41909
theorem R93485 : Reach 93485 := rs (se 3 (by rfl) ⟨17528, by rfl⟩) R35057
theorem R27955 : Reach 27955 := rs (se 1 (by rfl) ⟨20966, by rfl⟩) R41933
theorem R27971 : Reach 27971 := rs (se 1 (by rfl) ⟨20978, by rfl⟩) R41957
theorem R27987 : Reach 27987 := rs (se 1 (by rfl) ⟨20990, by rfl⟩) R41981
theorem R28003 : Reach 28003 := rs (se 1 (by rfl) ⟨21002, by rfl⟩) R42005
theorem R28019 : Reach 28019 := rs (se 1 (by rfl) ⟨21014, by rfl⟩) R42029
theorem R28035 : Reach 28035 := rs (se 1 (by rfl) ⟨21026, by rfl⟩) R42053
theorem R93581 : Reach 93581 := rs (se 3 (by rfl) ⟨17546, by rfl⟩) R35093
theorem R28051 : Reach 28051 := rs (se 1 (by rfl) ⟨21038, by rfl⟩) R42077
theorem R28067 : Reach 28067 := rs (se 1 (by rfl) ⟨21050, by rfl⟩) R42101
theorem R28083 : Reach 28083 := rs (se 1 (by rfl) ⟨21062, by rfl⟩) R42125
theorem R93635 : Reach 93635 := rs (se 1 (by rfl) ⟨70226, by rfl⟩) R140453
theorem R28099 : Reach 28099 := rs (se 1 (by rfl) ⟨21074, by rfl⟩) R42149
theorem R93649 : Reach 93649 := rs (se 2 (by rfl) ⟨35118, by rfl⟩) R70237
theorem R28115 : Reach 28115 := rs (se 1 (by rfl) ⟨21086, by rfl⟩) R42173
theorem R28131 : Reach 28131 := rs (se 1 (by rfl) ⟨21098, by rfl⟩) R42197
theorem R28147 : Reach 28147 := rs (se 1 (by rfl) ⟨21110, by rfl⟩) R42221
theorem R28163 : Reach 28163 := rs (se 1 (by rfl) ⟨21122, by rfl⟩) R42245
theorem R28179 : Reach 28179 := rs (se 1 (by rfl) ⟨21134, by rfl⟩) R42269
theorem R28195 : Reach 28195 := rs (se 1 (by rfl) ⟨21146, by rfl⟩) R42293
theorem R28211 : Reach 28211 := rs (se 1 (by rfl) ⟨21158, by rfl⟩) R42317
theorem R28227 : Reach 28227 := rs (se 1 (by rfl) ⟨21170, by rfl⟩) R42341
theorem R28243 : Reach 28243 := rs (se 1 (by rfl) ⟨21182, by rfl⟩) R42365
theorem R28259 : Reach 28259 := rs (se 1 (by rfl) ⟨21194, by rfl⟩) R42389
theorem R28275 : Reach 28275 := rs (se 1 (by rfl) ⟨21206, by rfl⟩) R42413
theorem R28291 : Reach 28291 := rs (se 1 (by rfl) ⟨21218, by rfl⟩) R42437
theorem R61073 : Reach 61073 := rs (se 2 (by rfl) ⟨22902, by rfl⟩) R45805
theorem R28307 : Reach 28307 := rs (se 1 (by rfl) ⟨21230, by rfl⟩) R42461
theorem R61091 : Reach 61091 := rs (se 1 (by rfl) ⟨45818, by rfl⟩) R91637
theorem R28323 : Reach 28323 := rs (se 1 (by rfl) ⟨21242, by rfl⟩) R42485
theorem R28339 : Reach 28339 := rs (se 1 (by rfl) ⟨21254, by rfl⟩) R42509
theorem R28355 : Reach 28355 := rs (se 1 (by rfl) ⟨21266, by rfl⟩) R42533
theorem R93905 : Reach 93905 := rs (se 2 (by rfl) ⟨35214, by rfl⟩) R70429
theorem R28371 : Reach 28371 := rs (se 1 (by rfl) ⟨21278, by rfl⟩) R42557
theorem R28387 : Reach 28387 := rs (se 1 (by rfl) ⟨21290, by rfl⟩) R42581
theorem R28403 : Reach 28403 := rs (se 1 (by rfl) ⟨21302, by rfl⟩) R42605
theorem R28419 : Reach 28419 := rs (se 1 (by rfl) ⟨21314, by rfl⟩) R42629
theorem R28435 : Reach 28435 := rs (se 1 (by rfl) ⟨21326, by rfl⟩) R42653
theorem R28451 : Reach 28451 := rs (se 1 (by rfl) ⟨21338, by rfl⟩) R42677
theorem R28467 : Reach 28467 := rs (se 1 (by rfl) ⟨21350, by rfl⟩) R42701
theorem R28483 : Reach 28483 := rs (se 1 (by rfl) ⟨21362, by rfl⟩) R42725
theorem R28499 : Reach 28499 := rs (se 1 (by rfl) ⟨21374, by rfl⟩) R42749
theorem R28515 : Reach 28515 := rs (se 1 (by rfl) ⟨21386, by rfl⟩) R42773
theorem R28531 : Reach 28531 := rs (se 1 (by rfl) ⟨21398, by rfl⟩) R42797
theorem R28547 : Reach 28547 := rs (se 1 (by rfl) ⟨21410, by rfl⟩) R42821
theorem R28563 : Reach 28563 := rs (se 1 (by rfl) ⟨21422, by rfl⟩) R42845
theorem R28579 : Reach 28579 := rs (se 1 (by rfl) ⟨21434, by rfl⟩) R42869
theorem R61361 : Reach 61361 := rs (se 2 (by rfl) ⟨23010, by rfl⟩) R46021
theorem R28595 : Reach 28595 := rs (se 1 (by rfl) ⟨21446, by rfl⟩) R42893
theorem R61379 : Reach 61379 := rs (se 1 (by rfl) ⟨46034, by rfl⟩) R92069
theorem R28611 : Reach 28611 := rs (se 1 (by rfl) ⟨21458, by rfl⟩) R42917
theorem R28627 : Reach 28627 := rs (se 1 (by rfl) ⟨21470, by rfl⟩) R42941
theorem R28643 : Reach 28643 := rs (se 1 (by rfl) ⟨21482, by rfl⟩) R42965
theorem R28659 : Reach 28659 := rs (se 1 (by rfl) ⟨21494, by rfl⟩) R42989
theorem R28675 : Reach 28675 := rs (se 1 (by rfl) ⟨21506, by rfl⟩) R43013
theorem R28691 : Reach 28691 := rs (se 1 (by rfl) ⟨21518, by rfl⟩) R43037
theorem R28707 : Reach 28707 := rs (se 1 (by rfl) ⟨21530, by rfl⟩) R43061
theorem R28723 : Reach 28723 := rs (se 1 (by rfl) ⟨21542, by rfl⟩) R43085
theorem R28739 : Reach 28739 := rs (se 1 (by rfl) ⟨21554, by rfl⟩) R43109
theorem R28755 : Reach 28755 := rs (se 1 (by rfl) ⟨21566, by rfl⟩) R43133
theorem R28771 : Reach 28771 := rs (se 1 (by rfl) ⟨21578, by rfl⟩) R43157
theorem R28787 : Reach 28787 := rs (se 1 (by rfl) ⟨21590, by rfl⟩) R43181
theorem R28803 : Reach 28803 := rs (se 1 (by rfl) ⟨21602, by rfl⟩) R43205
theorem R28819 : Reach 28819 := rs (se 1 (by rfl) ⟨21614, by rfl⟩) R43229
theorem R28835 : Reach 28835 := rs (se 1 (by rfl) ⟨21626, by rfl⟩) R43253
theorem R28851 : Reach 28851 := rs (se 1 (by rfl) ⟨21638, by rfl⟩) R43277
theorem R28867 : Reach 28867 := rs (se 1 (by rfl) ⟨21650, by rfl⟩) R43301
theorem R61649 : Reach 61649 := rs (se 2 (by rfl) ⟨23118, by rfl⟩) R46237
theorem R28883 : Reach 28883 := rs (se 1 (by rfl) ⟨21662, by rfl⟩) R43325
theorem R61667 : Reach 61667 := rs (se 1 (by rfl) ⟨46250, by rfl⟩) R92501
theorem R28899 : Reach 28899 := rs (se 1 (by rfl) ⟨21674, by rfl⟩) R43349
theorem R94445 : Reach 94445 := rs (se 3 (by rfl) ⟨17708, by rfl⟩) R35417
theorem R61681 : Reach 61681 := rs (se 2 (by rfl) ⟨23130, by rfl⟩) R46261
theorem R28915 : Reach 28915 := rs (se 1 (by rfl) ⟨21686, by rfl⟩) R43373
theorem R28931 : Reach 28931 := rs (se 1 (by rfl) ⟨21698, by rfl⟩) R43397
theorem R28947 : Reach 28947 := rs (se 1 (by rfl) ⟨21710, by rfl⟩) R43421
theorem R94499 : Reach 94499 := rs (se 1 (by rfl) ⟨70874, by rfl⟩) R141749
theorem R28963 : Reach 28963 := rs (se 1 (by rfl) ⟨21722, by rfl⟩) R43445
theorem R28979 : Reach 28979 := rs (se 1 (by rfl) ⟨21734, by rfl⟩) R43469
theorem R28995 : Reach 28995 := rs (se 1 (by rfl) ⟨21746, by rfl⟩) R43493
theorem R29011 : Reach 29011 := rs (se 1 (by rfl) ⟨21758, by rfl⟩) R43517
theorem R29027 : Reach 29027 := rs (se 1 (by rfl) ⟨21770, by rfl⟩) R43541
theorem R29043 : Reach 29043 := rs (se 1 (by rfl) ⟨21782, by rfl⟩) R43565
theorem R29059 : Reach 29059 := rs (se 1 (by rfl) ⟨21794, by rfl⟩) R43589
theorem R29075 : Reach 29075 := rs (se 1 (by rfl) ⟨21806, by rfl⟩) R43613
theorem R29091 : Reach 29091 := rs (se 1 (by rfl) ⟨21818, by rfl⟩) R43637
theorem R29107 : Reach 29107 := rs (se 1 (by rfl) ⟨21830, by rfl⟩) R43661
theorem R29123 : Reach 29123 := rs (se 1 (by rfl) ⟨21842, by rfl⟩) R43685
theorem R29139 : Reach 29139 := rs (se 1 (by rfl) ⟨21854, by rfl⟩) R43709
theorem R29155 : Reach 29155 := rs (se 1 (by rfl) ⟨21866, by rfl⟩) R43733
theorem R61937 : Reach 61937 := rs (se 2 (by rfl) ⟨23226, by rfl⟩) R46453
theorem R29171 : Reach 29171 := rs (se 1 (by rfl) ⟨21878, by rfl⟩) R43757
theorem R61955 : Reach 61955 := rs (se 1 (by rfl) ⟨46466, by rfl⟩) R92933
theorem R29187 : Reach 29187 := rs (se 1 (by rfl) ⟨21890, by rfl⟩) R43781
theorem R29203 : Reach 29203 := rs (se 1 (by rfl) ⟨21902, by rfl⟩) R43805
theorem R29219 : Reach 29219 := rs (se 1 (by rfl) ⟨21914, by rfl⟩) R43829
theorem R94769 : Reach 94769 := rs (se 2 (by rfl) ⟨35538, by rfl⟩) R71077
theorem R29235 : Reach 29235 := rs (se 1 (by rfl) ⟨21926, by rfl⟩) R43853
theorem R29251 : Reach 29251 := rs (se 1 (by rfl) ⟨21938, by rfl⟩) R43877
theorem R127565 : Reach 127565 := rs (se 3 (by rfl) ⟨23918, by rfl⟩) R47837
theorem R29267 : Reach 29267 := rs (se 1 (by rfl) ⟨21950, by rfl⟩) R43901
theorem R29283 : Reach 29283 := rs (se 1 (by rfl) ⟨21962, by rfl⟩) R43925
theorem R29299 : Reach 29299 := rs (se 1 (by rfl) ⟨21974, by rfl⟩) R43949
theorem R29315 : Reach 29315 := rs (se 1 (by rfl) ⟨21986, by rfl⟩) R43973
theorem R29331 : Reach 29331 := rs (se 1 (by rfl) ⟨21998, by rfl⟩) R43997
theorem R29347 : Reach 29347 := rs (se 1 (by rfl) ⟨22010, by rfl⟩) R44021
theorem R29363 : Reach 29363 := rs (se 1 (by rfl) ⟨22022, by rfl⟩) R44045
theorem R62147 : Reach 62147 := rs (se 1 (by rfl) ⟨46610, by rfl⟩) R93221
theorem R29379 : Reach 29379 := rs (se 1 (by rfl) ⟨22034, by rfl⟩) R44069
theorem R225989 : Reach 225989 := rs (se 4 (by rfl) ⟨21186, by rfl⟩) R42373
theorem R29395 : Reach 29395 := rs (se 1 (by rfl) ⟨22046, by rfl⟩) R44093
theorem R29411 : Reach 29411 := rs (se 1 (by rfl) ⟨22058, by rfl⟩) R44117
theorem R29427 : Reach 29427 := rs (se 1 (by rfl) ⟨22070, by rfl⟩) R44141
theorem R29443 : Reach 29443 := rs (se 1 (by rfl) ⟨22082, by rfl⟩) R44165
theorem R62225 : Reach 62225 := rs (se 2 (by rfl) ⟨23334, by rfl⟩) R46669
theorem R29459 : Reach 29459 := rs (se 1 (by rfl) ⟨22094, by rfl⟩) R44189
theorem R62243 : Reach 62243 := rs (se 1 (by rfl) ⟨46682, by rfl⟩) R93365
theorem R29475 : Reach 29475 := rs (se 1 (by rfl) ⟨22106, by rfl⟩) R44213
theorem R29491 : Reach 29491 := rs (se 1 (by rfl) ⟨22118, by rfl⟩) R44237
theorem R29507 : Reach 29507 := rs (se 1 (by rfl) ⟨22130, by rfl⟩) R44261
theorem R29523 : Reach 29523 := rs (se 1 (by rfl) ⟨22142, by rfl⟩) R44285
theorem R29539 : Reach 29539 := rs (se 1 (by rfl) ⟨22154, by rfl⟩) R44309
theorem R29555 : Reach 29555 := rs (se 1 (by rfl) ⟨22166, by rfl⟩) R44333
theorem R29571 : Reach 29571 := rs (se 1 (by rfl) ⟨22178, by rfl⟩) R44357
theorem R29587 : Reach 29587 := rs (se 1 (by rfl) ⟨22190, by rfl⟩) R44381
theorem R29603 : Reach 29603 := rs (se 1 (by rfl) ⟨22202, by rfl⟩) R44405
theorem R127921 : Reach 127921 := rs (se 2 (by rfl) ⟨47970, by rfl⟩) R95941
theorem R29619 : Reach 29619 := rs (se 1 (by rfl) ⟨22214, by rfl⟩) R44429
theorem R29635 : Reach 29635 := rs (se 1 (by rfl) ⟨22226, by rfl⟩) R44453
theorem R29651 : Reach 29651 := rs (se 1 (by rfl) ⟨22238, by rfl⟩) R44477
theorem R29667 : Reach 29667 := rs (se 1 (by rfl) ⟨22250, by rfl⟩) R44501
theorem R29683 : Reach 29683 := rs (se 1 (by rfl) ⟨22262, by rfl⟩) R44525
theorem R29699 : Reach 29699 := rs (se 1 (by rfl) ⟨22274, by rfl⟩) R44549
theorem R29715 : Reach 29715 := rs (se 1 (by rfl) ⟨22286, by rfl⟩) R44573
theorem R29731 : Reach 29731 := rs (se 1 (by rfl) ⟨22298, by rfl⟩) R44597
theorem R62513 : Reach 62513 := rs (se 2 (by rfl) ⟨23442, by rfl⟩) R46885
theorem R29747 : Reach 29747 := rs (se 1 (by rfl) ⟨22310, by rfl⟩) R44621
theorem R62531 : Reach 62531 := rs (se 1 (by rfl) ⟨46898, by rfl⟩) R93797
theorem R29763 : Reach 29763 := rs (se 1 (by rfl) ⟨22322, by rfl⟩) R44645
theorem R95309 : Reach 95309 := rs (se 3 (by rfl) ⟨17870, by rfl⟩) R35741
theorem R29779 : Reach 29779 := rs (se 1 (by rfl) ⟨22334, by rfl⟩) R44669
theorem R29795 : Reach 29795 := rs (se 1 (by rfl) ⟨22346, by rfl⟩) R44693
theorem R29811 : Reach 29811 := rs (se 1 (by rfl) ⟨22358, by rfl⟩) R44717
theorem R95363 : Reach 95363 := rs (se 1 (by rfl) ⟨71522, by rfl⟩) R143045
theorem R29827 : Reach 29827 := rs (se 1 (by rfl) ⟨22370, by rfl⟩) R44741
theorem R29843 : Reach 29843 := rs (se 1 (by rfl) ⟨22382, by rfl⟩) R44765
theorem R29859 : Reach 29859 := rs (se 1 (by rfl) ⟨22394, by rfl⟩) R44789
theorem R29875 : Reach 29875 := rs (se 1 (by rfl) ⟨22406, by rfl⟩) R44813
theorem R29891 : Reach 29891 := rs (se 1 (by rfl) ⟨22418, by rfl⟩) R44837
theorem R160973 : Reach 160973 := rs (se 3 (by rfl) ⟨30182, by rfl⟩) R60365
theorem R29907 : Reach 29907 := rs (se 1 (by rfl) ⟨22430, by rfl⟩) R44861
theorem R29923 : Reach 29923 := rs (se 1 (by rfl) ⟨22442, by rfl⟩) R44885
theorem R29939 : Reach 29939 := rs (se 1 (by rfl) ⟨22454, by rfl⟩) R44909
theorem R29955 : Reach 29955 := rs (se 1 (by rfl) ⟨22466, by rfl⟩) R44933
theorem R29971 : Reach 29971 := rs (se 1 (by rfl) ⟨22478, by rfl⟩) R44957
theorem R29987 : Reach 29987 := rs (se 1 (by rfl) ⟨22490, by rfl⟩) R44981
theorem R30003 : Reach 30003 := rs (se 1 (by rfl) ⟨22502, by rfl⟩) R45005
theorem R30019 : Reach 30019 := rs (se 1 (by rfl) ⟨22514, by rfl⟩) R45029
theorem R62801 : Reach 62801 := rs (se 2 (by rfl) ⟨23550, by rfl⟩) R47101
theorem R30035 : Reach 30035 := rs (se 1 (by rfl) ⟨22526, by rfl⟩) R45053
theorem R62819 : Reach 62819 := rs (se 1 (by rfl) ⟨47114, by rfl⟩) R94229
theorem R30051 : Reach 30051 := rs (se 1 (by rfl) ⟨22538, by rfl⟩) R45077
theorem R30067 : Reach 30067 := rs (se 1 (by rfl) ⟨22550, by rfl⟩) R45101
theorem R30083 : Reach 30083 := rs (se 1 (by rfl) ⟨22562, by rfl⟩) R45125
theorem R95633 : Reach 95633 := rs (se 2 (by rfl) ⟨35862, by rfl⟩) R71725
theorem R30099 : Reach 30099 := rs (se 1 (by rfl) ⟨22574, by rfl⟩) R45149
theorem R30115 : Reach 30115 := rs (se 1 (by rfl) ⟨22586, by rfl⟩) R45173
theorem R30131 : Reach 30131 := rs (se 1 (by rfl) ⟨22598, by rfl⟩) R45197
theorem R30147 : Reach 30147 := rs (se 1 (by rfl) ⟨22610, by rfl⟩) R45221
theorem R30163 : Reach 30163 := rs (se 1 (by rfl) ⟨22622, by rfl⟩) R45245
theorem R30179 : Reach 30179 := rs (se 1 (by rfl) ⟨22634, by rfl⟩) R45269
theorem R30195 : Reach 30195 := rs (se 1 (by rfl) ⟨22646, by rfl⟩) R45293
theorem R30211 : Reach 30211 := rs (se 1 (by rfl) ⟨22658, by rfl⟩) R45317
theorem R325133 : Reach 325133 := rs (se 3 (by rfl) ⟨60962, by rfl⟩) R121925
theorem R30227 : Reach 30227 := rs (se 1 (by rfl) ⟨22670, by rfl⟩) R45341
theorem R30243 : Reach 30243 := rs (se 1 (by rfl) ⟨22682, by rfl⟩) R45365
theorem R30259 : Reach 30259 := rs (se 1 (by rfl) ⟨22694, by rfl⟩) R45389
theorem R30275 : Reach 30275 := rs (se 1 (by rfl) ⟨22706, by rfl⟩) R45413
theorem R30291 : Reach 30291 := rs (se 1 (by rfl) ⟨22718, by rfl⟩) R45437
theorem R30307 : Reach 30307 := rs (se 1 (by rfl) ⟨22730, by rfl⟩) R45461
theorem R63089 : Reach 63089 := rs (se 2 (by rfl) ⟨23658, by rfl⟩) R47317
theorem R30323 : Reach 30323 := rs (se 1 (by rfl) ⟨22742, by rfl⟩) R45485
theorem R63107 : Reach 63107 := rs (se 1 (by rfl) ⟨47330, by rfl⟩) R94661
theorem R30339 : Reach 30339 := rs (se 1 (by rfl) ⟨22754, by rfl⟩) R45509
theorem R30355 : Reach 30355 := rs (se 1 (by rfl) ⟨22766, by rfl⟩) R45533
theorem R30371 : Reach 30371 := rs (se 1 (by rfl) ⟨22778, by rfl⟩) R45557
theorem R30387 : Reach 30387 := rs (se 1 (by rfl) ⟨22790, by rfl⟩) R45581
theorem R30403 : Reach 30403 := rs (se 1 (by rfl) ⟨22802, by rfl⟩) R45605
theorem R30419 : Reach 30419 := rs (se 1 (by rfl) ⟨22814, by rfl⟩) R45629
theorem R30435 : Reach 30435 := rs (se 1 (by rfl) ⟨22826, by rfl⟩) R45653
theorem R30451 : Reach 30451 := rs (se 1 (by rfl) ⟨22838, by rfl⟩) R45677
theorem R30467 : Reach 30467 := rs (se 1 (by rfl) ⟨22850, by rfl⟩) R45701
theorem R30483 : Reach 30483 := rs (se 1 (by rfl) ⟨22862, by rfl⟩) R45725
theorem R30499 : Reach 30499 := rs (se 1 (by rfl) ⟨22874, by rfl⟩) R45749
theorem R30515 : Reach 30515 := rs (se 1 (by rfl) ⟨22886, by rfl⟩) R45773
theorem R587573 : Reach 587573 := rs (se 5 (by rfl) ⟨27542, by rfl⟩) R55085
theorem R30531 : Reach 30531 := rs (se 1 (by rfl) ⟨22898, by rfl⟩) R45797
theorem R30547 : Reach 30547 := rs (se 1 (by rfl) ⟨22910, by rfl⟩) R45821
theorem R30563 : Reach 30563 := rs (se 1 (by rfl) ⟨22922, by rfl⟩) R45845
theorem R30579 : Reach 30579 := rs (se 1 (by rfl) ⟨22934, by rfl⟩) R45869
theorem R30595 : Reach 30595 := rs (se 1 (by rfl) ⟨22946, by rfl⟩) R45893
theorem R63377 : Reach 63377 := rs (se 2 (by rfl) ⟨23766, by rfl⟩) R47533
theorem R30611 : Reach 30611 := rs (se 1 (by rfl) ⟨22958, by rfl⟩) R45917
theorem R63395 : Reach 63395 := rs (se 1 (by rfl) ⟨47546, by rfl⟩) R95093
theorem R30627 : Reach 30627 := rs (se 1 (by rfl) ⟨22970, by rfl⟩) R45941
theorem R96173 : Reach 96173 := rs (se 3 (by rfl) ⟨18032, by rfl⟩) R36065
theorem R30643 : Reach 30643 := rs (se 1 (by rfl) ⟨22982, by rfl⟩) R45965
theorem R30659 : Reach 30659 := rs (se 1 (by rfl) ⟨22994, by rfl⟩) R45989
theorem R30675 : Reach 30675 := rs (se 1 (by rfl) ⟨23006, by rfl⟩) R46013
theorem R96227 : Reach 96227 := rs (se 1 (by rfl) ⟨72170, by rfl⟩) R144341
theorem R30691 : Reach 30691 := rs (se 1 (by rfl) ⟨23018, by rfl⟩) R46037
theorem R30707 : Reach 30707 := rs (se 1 (by rfl) ⟨23030, by rfl⟩) R46061
theorem R30723 : Reach 30723 := rs (se 1 (by rfl) ⟨23042, by rfl⟩) R46085
theorem R161797 : Reach 161797 := rs (se 4 (by rfl) ⟨15168, by rfl⟩) R30337
theorem R30739 : Reach 30739 := rs (se 1 (by rfl) ⟨23054, by rfl⟩) R46109
theorem R30755 : Reach 30755 := rs (se 1 (by rfl) ⟨23066, by rfl⟩) R46133
theorem R30771 : Reach 30771 := rs (se 1 (by rfl) ⟨23078, by rfl⟩) R46157
theorem R30787 : Reach 30787 := rs (se 1 (by rfl) ⟨23090, by rfl⟩) R46181
theorem R30803 : Reach 30803 := rs (se 1 (by rfl) ⟨23102, by rfl⟩) R46205
theorem R30819 : Reach 30819 := rs (se 1 (by rfl) ⟨23114, by rfl⟩) R46229
theorem R96365 : Reach 96365 := rs (se 3 (by rfl) ⟨18068, by rfl⟩) R36137
theorem R30835 : Reach 30835 := rs (se 1 (by rfl) ⟨23126, by rfl⟩) R46253
theorem R30851 : Reach 30851 := rs (se 1 (by rfl) ⟨23138, by rfl⟩) R46277
theorem R30867 : Reach 30867 := rs (se 1 (by rfl) ⟨23150, by rfl⟩) R46301
theorem R30883 : Reach 30883 := rs (se 1 (by rfl) ⟨23162, by rfl⟩) R46325
theorem R63665 : Reach 63665 := rs (se 2 (by rfl) ⟨23874, by rfl⟩) R47749
theorem R96433 : Reach 96433 := rs (se 2 (by rfl) ⟨36162, by rfl⟩) R72325
theorem R30899 : Reach 30899 := rs (se 1 (by rfl) ⟨23174, by rfl⟩) R46349
theorem R63683 : Reach 63683 := rs (se 1 (by rfl) ⟨47762, by rfl⟩) R95525
theorem R30915 : Reach 30915 := rs (se 1 (by rfl) ⟨23186, by rfl⟩) R46373
theorem R30931 : Reach 30931 := rs (se 1 (by rfl) ⟨23198, by rfl⟩) R46397
theorem R30947 : Reach 30947 := rs (se 1 (by rfl) ⟨23210, by rfl⟩) R46421
theorem R96497 : Reach 96497 := rs (se 2 (by rfl) ⟨36186, by rfl⟩) R72373
theorem R30963 : Reach 30963 := rs (se 1 (by rfl) ⟨23222, by rfl⟩) R46445
theorem R30979 : Reach 30979 := rs (se 1 (by rfl) ⟨23234, by rfl⟩) R46469
theorem R30995 : Reach 30995 := rs (se 1 (by rfl) ⟨23246, by rfl⟩) R46493
theorem R31011 : Reach 31011 := rs (se 1 (by rfl) ⟨23258, by rfl⟩) R46517
theorem R31027 : Reach 31027 := rs (se 1 (by rfl) ⟨23270, by rfl⟩) R46541
theorem R31043 : Reach 31043 := rs (se 1 (by rfl) ⟨23282, by rfl⟩) R46565
theorem R194885 : Reach 194885 := rs (se 4 (by rfl) ⟨18270, by rfl⟩) R36541
theorem R31059 : Reach 31059 := rs (se 1 (by rfl) ⟨23294, by rfl⟩) R46589
theorem R31075 : Reach 31075 := rs (se 1 (by rfl) ⟨23306, by rfl⟩) R46613
theorem R31091 : Reach 31091 := rs (se 1 (by rfl) ⟨23318, by rfl⟩) R46637
theorem R31107 : Reach 31107 := rs (se 1 (by rfl) ⟨23330, by rfl⟩) R46661
theorem R31171 : Reach 31171 := rs (se 1 (by rfl) ⟨23378, by rfl⟩) R46757
theorem R63953 : Reach 63953 := rs (se 2 (by rfl) ⟨23982, by rfl⟩) R47965
theorem R63971 : Reach 63971 := rs (se 1 (by rfl) ⟨47978, by rfl⟩) R95957
theorem R162317 : Reach 162317 := rs (se 3 (by rfl) ⟨30434, by rfl⟩) R60869
theorem R31315 : Reach 31315 := rs (se 1 (by rfl) ⟨23486, by rfl⟩) R46973
theorem R31459 : Reach 31459 := rs (se 1 (by rfl) ⟨23594, by rfl⟩) R47189
theorem R64241 : Reach 64241 := rs (se 2 (by rfl) ⟨24090, by rfl⟩) R48181
theorem R64259 : Reach 64259 := rs (se 1 (by rfl) ⟨48194, by rfl⟩) R96389
theorem R97037 : Reach 97037 := rs (se 3 (by rfl) ⟨18194, by rfl⟩) R36389
theorem R31603 : Reach 31603 := rs (se 1 (by rfl) ⟨23702, by rfl⟩) R47405
theorem R31747 : Reach 31747 := rs (se 1 (by rfl) ⟨23810, by rfl⟩) R47621
theorem R64529 : Reach 64529 := rs (se 2 (by rfl) ⟨24198, by rfl⟩) R48397
theorem R31763 : Reach 31763 := rs (se 1 (by rfl) ⟨23822, by rfl⟩) R47645
theorem R64547 : Reach 64547 := rs (se 1 (by rfl) ⟨48410, by rfl⟩) R96821
theorem R31811 : Reach 31811 := rs (se 1 (by rfl) ⟨23858, by rfl⟩) R47717
theorem R31891 : Reach 31891 := rs (se 1 (by rfl) ⟨23918, by rfl⟩) R47837
theorem R64739 : Reach 64739 := rs (se 1 (by rfl) ⟨48554, by rfl⟩) R97109
theorem R32035 : Reach 32035 := rs (se 1 (by rfl) ⟨24026, by rfl⟩) R48053
theorem R64817 : Reach 64817 := rs (se 2 (by rfl) ⟨24306, by rfl⟩) R48613
theorem R64835 : Reach 64835 := rs (se 1 (by rfl) ⟨48626, by rfl⟩) R97253
theorem R163205 : Reach 163205 := rs (se 4 (by rfl) ⟨15300, by rfl⟩) R30601
theorem R32179 : Reach 32179 := rs (se 1 (by rfl) ⟨24134, by rfl⟩) R48269
theorem R32323 : Reach 32323 := rs (se 1 (by rfl) ⟨24242, by rfl⟩) R48485
theorem R65105 : Reach 65105 := rs (se 2 (by rfl) ⟨24414, by rfl⟩) R48829
theorem R360035 : Reach 360035 := rs (se 1 (by rfl) ⟨270026, by rfl⟩) R540053
theorem R65123 : Reach 65123 := rs (se 1 (by rfl) ⟨48842, by rfl⟩) R97685
theorem R130673 : Reach 130673 := rs (se 2 (by rfl) ⟨49002, by rfl⟩) R98005
theorem R97955 : Reach 97955 := rs (se 1 (by rfl) ⟨73466, by rfl⟩) R146933
theorem R32467 : Reach 32467 := rs (se 1 (by rfl) ⟨24350, by rfl⟩) R48701
theorem R32611 : Reach 32611 := rs (se 1 (by rfl) ⟨24458, by rfl⟩) R48917
theorem R65393 : Reach 65393 := rs (se 2 (by rfl) ⟨24522, by rfl⟩) R49045
theorem R65411 : Reach 65411 := rs (se 1 (by rfl) ⟨49058, by rfl⟩) R98117
theorem R98225 : Reach 98225 := rs (se 2 (by rfl) ⟨36834, by rfl⟩) R73669
theorem R32755 : Reach 32755 := rs (se 1 (by rfl) ⟨24566, by rfl⟩) R49133
theorem R32791 : Reach 32791 := rs (se 1 (by rfl) ⟨24593, by rfl⟩) R49187
theorem R32971 : Reach 32971 := rs (se 1 (by rfl) ⟨24728, by rfl⟩) R49457
theorem R65753 : Reach 65753 := rs (se 2 (by rfl) ⟨24657, by rfl⟩) R49315
theorem R65815 : Reach 65815 := rs (se 1 (by rfl) ⟨49361, by rfl⟩) R98723
theorem R65843 : Reach 65843 := rs (se 1 (by rfl) ⟨49382, by rfl⟩) R98765
theorem R98711 : Reach 98711 := rs (se 1 (by rfl) ⟨74033, by rfl⟩) R148067
theorem R197081 : Reach 197081 := rs (se 2 (by rfl) ⟨73905, by rfl⟩) R147811
theorem R98819 : Reach 98819 := rs (se 1 (by rfl) ⟨74114, by rfl⟩) R148229
theorem R66113 : Reach 66113 := rs (se 2 (by rfl) ⟨24792, by rfl⟩) R49585
theorem R33367 : Reach 33367 := rs (se 1 (by rfl) ⟨25025, by rfl⟩) R50051
theorem R131801 : Reach 131801 := rs (se 2 (by rfl) ⟨49425, by rfl⟩) R98851
theorem R33547 : Reach 33547 := rs (se 1 (by rfl) ⟨25160, by rfl⟩) R50321
theorem R99089 : Reach 99089 := rs (se 2 (by rfl) ⟨37158, by rfl⟩) R74317
theorem R66455 : Reach 66455 := rs (se 1 (by rfl) ⟨49841, by rfl⟩) R99683
theorem R99251 : Reach 99251 := rs (se 1 (by rfl) ⟨74438, by rfl⟩) R148877
theorem R66635 : Reach 66635 := rs (se 1 (by rfl) ⟨49976, by rfl⟩) R99953
theorem R33943 : Reach 33943 := rs (se 1 (by rfl) ⟨25457, by rfl⟩) R50915
theorem R99521 : Reach 99521 := rs (se 2 (by rfl) ⟨37320, by rfl⟩) R74641
theorem R99629 : Reach 99629 := rs (se 3 (by rfl) ⟨18680, by rfl⟩) R37361
theorem R34123 : Reach 34123 := rs (se 1 (by rfl) ⟨25592, by rfl⟩) R51185
theorem R66905 : Reach 66905 := rs (se 2 (by rfl) ⟨25089, by rfl⟩) R50179
theorem R66995 : Reach 66995 := rs (se 1 (by rfl) ⟨50246, by rfl⟩) R100493
theorem R99787 : Reach 99787 := rs (se 1 (by rfl) ⟨74840, by rfl⟩) R149681
theorem R67265 : Reach 67265 := rs (se 2 (by rfl) ⟨25224, by rfl⟩) R50449
theorem R34519 : Reach 34519 := rs (se 1 (by rfl) ⟨25889, by rfl⟩) R51779
theorem R100061 : Reach 100061 := rs (se 3 (by rfl) ⟨18761, by rfl⟩) R37523
theorem R165725 : Reach 165725 := rs (se 3 (by rfl) ⟨31073, by rfl⟩) R62147
theorem R34699 : Reach 34699 := rs (se 1 (by rfl) ⟨26024, by rfl⟩) R52049
theorem R133015 : Reach 133015 := rs (se 1 (by rfl) ⟨99761, by rfl⟩) R199523
theorem R67607 : Reach 67607 := rs (se 1 (by rfl) ⟨50705, by rfl⟩) R101411
theorem R133271 : Reach 133271 := rs (se 1 (by rfl) ⟨99953, by rfl⟩) R199907
theorem R67787 : Reach 67787 := rs (se 1 (by rfl) ⟨50840, by rfl⟩) R101681
theorem R35083 : Reach 35083 := rs (se 1 (by rfl) ⟨26312, by rfl⟩) R52625
theorem R35095 : Reach 35095 := rs (se 1 (by rfl) ⟨26321, by rfl⟩) R52643
theorem R68057 : Reach 68057 := rs (se 2 (by rfl) ⟨25521, by rfl⟩) R51043
theorem R68147 : Reach 68147 := rs (se 1 (by rfl) ⟨51110, by rfl⟩) R102221
theorem R101009 : Reach 101009 := rs (se 2 (by rfl) ⟨37878, by rfl⟩) R75757
theorem R494261 : Reach 494261 := rs (se 5 (by rfl) ⟨23168, by rfl⟩) R46337
theorem R68417 : Reach 68417 := rs (se 2 (by rfl) ⟨25656, by rfl⟩) R51313
theorem R101195 : Reach 101195 := rs (se 1 (by rfl) ⟨75896, by rfl⟩) R151793
theorem R232523 : Reach 232523 := rs (se 1 (by rfl) ⟨174392, by rfl⟩) R348785
theorem R101465 : Reach 101465 := rs (se 2 (by rfl) ⟨38049, by rfl⟩) R76099
theorem R68759 : Reach 68759 := rs (se 1 (by rfl) ⟨51569, by rfl⟩) R103139
theorem R36055 : Reach 36055 := rs (se 1 (by rfl) ⟨27041, by rfl⟩) R54083
theorem R68825 : Reach 68825 := rs (se 2 (by rfl) ⟨25809, by rfl⟩) R51619
theorem R232739 : Reach 232739 := rs (se 1 (by rfl) ⟨174554, by rfl⟩) R349109
theorem R265517 : Reach 265517 := rs (se 3 (by rfl) ⟨49784, by rfl⟩) R99569
theorem R68939 : Reach 68939 := rs (se 1 (by rfl) ⟨51704, by rfl⟩) R103409
theorem R69209 : Reach 69209 := rs (se 2 (by rfl) ⟨25953, by rfl⟩) R51907
theorem R69299 : Reach 69299 := rs (se 1 (by rfl) ⟨51974, by rfl⟩) R103949
theorem R134873 : Reach 134873 := rs (se 2 (by rfl) ⟨50577, by rfl⟩) R101155
theorem R102167 : Reach 102167 := rs (se 1 (by rfl) ⟨76625, by rfl⟩) R153251
theorem R102275 : Reach 102275 := rs (se 1 (by rfl) ⟨76706, by rfl⟩) R153413
theorem R167831 : Reach 167831 := rs (se 1 (by rfl) ⟨125873, by rfl⟩) R251747
theorem R69569 : Reach 69569 := rs (se 2 (by rfl) ⟨26088, by rfl⟩) R52177
theorem R36875 : Reach 36875 := rs (se 1 (by rfl) ⟨27656, by rfl⟩) R55313
theorem R364675 : Reach 364675 := rs (se 1 (by rfl) ⟨273506, by rfl⟩) R547013
theorem R102545 : Reach 102545 := rs (se 2 (by rfl) ⟨38454, by rfl⟩) R76909
theorem R168115 : Reach 168115 := rs (se 1 (by rfl) ⟨126086, by rfl⟩) R252173
theorem R69911 : Reach 69911 := rs (se 1 (by rfl) ⟨52433, by rfl⟩) R104867
theorem R102707 : Reach 102707 := rs (se 1 (by rfl) ⟨77030, by rfl⟩) R154061
theorem R70105 : Reach 70105 := rs (se 2 (by rfl) ⟨26289, by rfl⟩) R52579
theorem R102977 : Reach 102977 := rs (se 2 (by rfl) ⟨38616, by rfl⟩) R77233
theorem R103085 : Reach 103085 := rs (se 3 (by rfl) ⟨19328, by rfl⟩) R38657
theorem R37579 : Reach 37579 := rs (se 1 (by rfl) ⟨28184, by rfl⟩) R56369
theorem R529253 : Reach 529253 := rs (se 4 (by rfl) ⟨49617, by rfl⟩) R99235
theorem R37847 : Reach 37847 := rs (se 1 (by rfl) ⟨28385, by rfl⟩) R56771
theorem R103427 : Reach 103427 := rs (se 1 (by rfl) ⟨77570, by rfl⟩) R155141
theorem R70679 : Reach 70679 := rs (se 1 (by rfl) ⟨53009, by rfl⟩) R106019
theorem R103517 : Reach 103517 := rs (se 3 (by rfl) ⟨19409, by rfl⟩) R38819
theorem R71219 : Reach 71219 := rs (se 1 (by rfl) ⟨53414, by rfl⟩) R106829
theorem R38551 : Reach 38551 := rs (se 1 (by rfl) ⟨28913, by rfl⟩) R57827
theorem R71513 : Reach 71513 := rs (se 2 (by rfl) ⟨26817, by rfl⟩) R53635
theorem R38809 : Reach 38809 := rs (se 2 (by rfl) ⟨14553, by rfl⟩) R29107
theorem R104651 : Reach 104651 := rs (se 1 (by rfl) ⟨78488, by rfl⟩) R156977
theorem R137537 : Reach 137537 := rs (se 2 (by rfl) ⟨51576, by rfl⟩) R103153
theorem R104921 : Reach 104921 := rs (se 2 (by rfl) ⟨39345, by rfl⟩) R78691
theorem R170561 : Reach 170561 := rs (se 2 (by rfl) ⟨63960, by rfl⟩) R127921
theorem R203357 : Reach 203357 := rs (se 3 (by rfl) ⟨38129, by rfl⟩) R76259
theorem R105181 : Reach 105181 := rs (se 3 (by rfl) ⟨19721, by rfl⟩) R39443
theorem R236465 : Reach 236465 := rs (se 2 (by rfl) ⟨88674, by rfl⟩) R177349
theorem R269347 : Reach 269347 := rs (se 1 (by rfl) ⟨202010, by rfl⟩) R404021
theorem R73163 : Reach 73163 := rs (se 1 (by rfl) ⟨54872, by rfl⟩) R109745
theorem R73177 : Reach 73177 := rs (se 2 (by rfl) ⟨27441, by rfl⟩) R54883
theorem R40715 : Reach 40715 := rs (se 1 (by rfl) ⟨30536, by rfl⟩) R61073
theorem R40727 : Reach 40727 := rs (se 1 (by rfl) ⟨30545, by rfl⟩) R61091
theorem R40793 : Reach 40793 := rs (se 2 (by rfl) ⟨15297, by rfl⟩) R30595
theorem R40907 : Reach 40907 := rs (se 1 (by rfl) ⟨30680, by rfl⟩) R61361
theorem R40919 : Reach 40919 := rs (se 1 (by rfl) ⟨30689, by rfl⟩) R61379
theorem R499729 : Reach 499729 := rs (se 2 (by rfl) ⟨187398, by rfl⟩) R374797
theorem R40985 : Reach 40985 := rs (se 2 (by rfl) ⟨15369, by rfl⟩) R30739
theorem R106541 : Reach 106541 := rs (se 3 (by rfl) ⟨19976, by rfl⟩) R39953
theorem R41099 : Reach 41099 := rs (se 1 (by rfl) ⟨30824, by rfl⟩) R61649
theorem R41111 : Reach 41111 := rs (se 1 (by rfl) ⟨30833, by rfl⟩) R61667
theorem R41177 : Reach 41177 := rs (se 2 (by rfl) ⟨15441, by rfl⟩) R30883
theorem R139481 : Reach 139481 := rs (se 2 (by rfl) ⟨52305, by rfl⟩) R104611
theorem R41291 : Reach 41291 := rs (se 1 (by rfl) ⟨30968, by rfl⟩) R61937
theorem R41303 : Reach 41303 := rs (se 1 (by rfl) ⟨30977, by rfl⟩) R61955
theorem R74135 : Reach 74135 := rs (se 1 (by rfl) ⟨55601, by rfl⟩) R111203
theorem R41369 : Reach 41369 := rs (se 2 (by rfl) ⟨15513, by rfl⟩) R31027
theorem R41483 : Reach 41483 := rs (se 1 (by rfl) ⟨31112, by rfl⟩) R62225
theorem R41495 : Reach 41495 := rs (se 1 (by rfl) ⟨31121, by rfl⟩) R62243
theorem R41561 : Reach 41561 := rs (se 2 (by rfl) ⟨15585, by rfl⟩) R31171
theorem R172637 : Reach 172637 := rs (se 3 (by rfl) ⟨32369, by rfl⟩) R64739
theorem R41675 : Reach 41675 := rs (se 1 (by rfl) ⟨31256, by rfl⟩) R62513
theorem R41687 : Reach 41687 := rs (se 1 (by rfl) ⟨31265, by rfl⟩) R62531
theorem R41753 : Reach 41753 := rs (se 2 (by rfl) ⟨15657, by rfl⟩) R31315
theorem R107315 : Reach 107315 := rs (se 1 (by rfl) ⟨80486, by rfl⟩) R160973
theorem R41867 : Reach 41867 := rs (se 1 (by rfl) ⟨31400, by rfl⟩) R62801
theorem R41879 : Reach 41879 := rs (se 1 (by rfl) ⟨31409, by rfl⟩) R62819
theorem R41945 : Reach 41945 := rs (se 2 (by rfl) ⟨15729, by rfl⟩) R31459
theorem R74803 : Reach 74803 := rs (se 1 (by rfl) ⟨56102, by rfl⟩) R112205
theorem R42059 : Reach 42059 := rs (se 1 (by rfl) ⟨31544, by rfl⟩) R63089
theorem R42071 : Reach 42071 := rs (se 1 (by rfl) ⟨31553, by rfl⟩) R63107
theorem R42137 : Reach 42137 := rs (se 2 (by rfl) ⟨15801, by rfl⟩) R31603
theorem R74945 : Reach 74945 := rs (se 2 (by rfl) ⟨28104, by rfl⟩) R56209
theorem R42251 : Reach 42251 := rs (se 1 (by rfl) ⟨31688, by rfl⟩) R63377
theorem R42263 : Reach 42263 := rs (se 1 (by rfl) ⟨31697, by rfl⟩) R63395
theorem R402733 : Reach 402733 := rs (se 3 (by rfl) ⟨75512, by rfl⟩) R151025
theorem R42329 : Reach 42329 := rs (se 2 (by rfl) ⟨15873, by rfl⟩) R31747
theorem R42443 : Reach 42443 := rs (se 1 (by rfl) ⟨31832, by rfl⟩) R63665
theorem R42455 : Reach 42455 := rs (se 1 (by rfl) ⟨31841, by rfl⟩) R63683
theorem R42521 : Reach 42521 := rs (se 2 (by rfl) ⟨15945, by rfl⟩) R31891
theorem R108125 : Reach 108125 := rs (se 3 (by rfl) ⟨20273, by rfl⟩) R40547
theorem R42635 : Reach 42635 := rs (se 1 (by rfl) ⟨31976, by rfl⟩) R63953
theorem R42647 : Reach 42647 := rs (se 1 (by rfl) ⟨31985, by rfl⟩) R63971
theorem R108211 : Reach 108211 := rs (se 1 (by rfl) ⟨81158, by rfl⟩) R162317
theorem R42713 : Reach 42713 := rs (se 2 (by rfl) ⟨16017, by rfl⟩) R32035
theorem R141101 : Reach 141101 := rs (se 3 (by rfl) ⟨26456, by rfl⟩) R52913
theorem R42827 : Reach 42827 := rs (se 1 (by rfl) ⟨32120, by rfl⟩) R64241
theorem R42839 : Reach 42839 := rs (se 1 (by rfl) ⟨32129, by rfl⟩) R64259
theorem R75613 : Reach 75613 := rs (se 3 (by rfl) ⟨14177, by rfl⟩) R28355
theorem R42905 : Reach 42905 := rs (se 2 (by rfl) ⟨16089, by rfl⟩) R32179
theorem R337841 : Reach 337841 := rs (se 2 (by rfl) ⟨126690, by rfl⟩) R253381
theorem R43019 : Reach 43019 := rs (se 1 (by rfl) ⟨32264, by rfl⟩) R64529
theorem R43031 : Reach 43031 := rs (se 1 (by rfl) ⟨32273, by rfl⟩) R64547
theorem R43097 : Reach 43097 := rs (se 2 (by rfl) ⟨16161, by rfl⟩) R32323
theorem R43211 : Reach 43211 := rs (se 1 (by rfl) ⟨32408, by rfl⟩) R64817
theorem R43223 : Reach 43223 := rs (se 1 (by rfl) ⟨32417, by rfl⟩) R64835
theorem R108803 : Reach 108803 := rs (se 1 (by rfl) ⟨81602, by rfl⟩) R163205
theorem R272645 : Reach 272645 := rs (se 4 (by rfl) ⟨25560, by rfl⟩) R51121
theorem R43289 : Reach 43289 := rs (se 2 (by rfl) ⟨16233, by rfl⟩) R32467
theorem R207197 : Reach 207197 := rs (se 3 (by rfl) ⟨38849, by rfl⟩) R77699
theorem R43403 : Reach 43403 := rs (se 1 (by rfl) ⟨32552, by rfl⟩) R65105
theorem R240023 : Reach 240023 := rs (se 1 (by rfl) ⟨180017, by rfl⟩) R360035
theorem R43415 : Reach 43415 := rs (se 1 (by rfl) ⟨32561, by rfl⟩) R65123
theorem R108973 : Reach 108973 := rs (se 3 (by rfl) ⟨20432, by rfl⟩) R40865
theorem R76211 : Reach 76211 := rs (se 1 (by rfl) ⟨57158, by rfl⟩) R114317
theorem R76235 : Reach 76235 := rs (se 1 (by rfl) ⟨57176, by rfl⟩) R114353
theorem R272857 : Reach 272857 := rs (se 2 (by rfl) ⟨102321, by rfl⟩) R204643
theorem R76249 : Reach 76249 := rs (se 2 (by rfl) ⟨28593, by rfl⟩) R57187
theorem R43481 : Reach 43481 := rs (se 2 (by rfl) ⟨16305, by rfl⟩) R32611
theorem R43595 : Reach 43595 := rs (se 1 (by rfl) ⟨32696, by rfl⟩) R65393
theorem R43607 : Reach 43607 := rs (se 1 (by rfl) ⟨32705, by rfl⟩) R65411
theorem R43673 : Reach 43673 := rs (se 2 (by rfl) ⟨16377, by rfl⟩) R32755
theorem R43723 : Reach 43723 := rs (se 1 (by rfl) ⟨32792, by rfl⟩) R65585
theorem R109259 : Reach 109259 := rs (se 1 (by rfl) ⟨81944, by rfl⟩) R163889
theorem R43735 : Reach 43735 := rs (se 1 (by rfl) ⟨32801, by rfl⟩) R65603
theorem R43787 : Reach 43787 := rs (se 1 (by rfl) ⟨32840, by rfl⟩) R65681
theorem R43799 : Reach 43799 := rs (se 1 (by rfl) ⟨32849, by rfl⟩) R65699
theorem R43865 : Reach 43865 := rs (se 2 (by rfl) ⟨16449, by rfl⟩) R32899
theorem R109457 : Reach 109457 := rs (se 2 (by rfl) ⟨41046, by rfl⟩) R82093
theorem R76747 : Reach 76747 := rs (se 1 (by rfl) ⟨57560, by rfl⟩) R115121
theorem R43979 : Reach 43979 := rs (se 1 (by rfl) ⟨32984, by rfl⟩) R65969
theorem R43991 : Reach 43991 := rs (se 1 (by rfl) ⟨32993, by rfl⟩) R65987
theorem R43993 : Reach 43993 := rs (se 2 (by rfl) ⟨16497, by rfl⟩) R32995
theorem R175121 : Reach 175121 := rs (se 2 (by rfl) ⟨65670, by rfl⟩) R131341
theorem R44057 : Reach 44057 := rs (se 2 (by rfl) ⟨16521, by rfl⟩) R33043
theorem R76889 : Reach 76889 := rs (se 2 (by rfl) ⟨28833, by rfl⟩) R57667
theorem R44171 : Reach 44171 := rs (se 1 (by rfl) ⟨33128, by rfl⟩) R66257
theorem R44183 : Reach 44183 := rs (se 1 (by rfl) ⟨33137, by rfl⟩) R66275
theorem R44249 : Reach 44249 := rs (se 2 (by rfl) ⟨16593, by rfl⟩) R33187
theorem R77021 : Reach 77021 := rs (se 3 (by rfl) ⟨14441, by rfl⟩) R28883
theorem R175405 : Reach 175405 := rs (se 3 (by rfl) ⟨32888, by rfl⟩) R65777
theorem R44363 : Reach 44363 := rs (se 1 (by rfl) ⟨33272, by rfl⟩) R66545
theorem R44375 : Reach 44375 := rs (se 1 (by rfl) ⟨33281, by rfl⟩) R66563
theorem R44441 : Reach 44441 := rs (se 2 (by rfl) ⟨16665, by rfl⟩) R33331
theorem R44555 : Reach 44555 := rs (se 1 (by rfl) ⟨33416, by rfl⟩) R66833
theorem R44567 : Reach 44567 := rs (se 1 (by rfl) ⟨33425, by rfl⟩) R66851
theorem R437795 : Reach 437795 := rs (se 1 (by rfl) ⟨328346, by rfl⟩) R656693
theorem R44633 : Reach 44633 := rs (se 2 (by rfl) ⟨16737, by rfl⟩) R33475
theorem R110231 : Reach 110231 := rs (se 1 (by rfl) ⟨82673, by rfl⟩) R165347
theorem R44747 : Reach 44747 := rs (se 1 (by rfl) ⟨33560, by rfl⟩) R67121
theorem R44759 : Reach 44759 := rs (se 1 (by rfl) ⟨33569, by rfl⟩) R67139
theorem R44825 : Reach 44825 := rs (se 2 (by rfl) ⟨16809, by rfl⟩) R33619
theorem R241501 : Reach 241501 := rs (se 3 (by rfl) ⟨45281, by rfl⟩) R90563
theorem R110429 : Reach 110429 := rs (se 3 (by rfl) ⟨20705, by rfl⟩) R41411
theorem R44939 : Reach 44939 := rs (se 1 (by rfl) ⟨33704, by rfl⟩) R67409
theorem R77719 : Reach 77719 := rs (se 1 (by rfl) ⟨58289, by rfl⟩) R116579
theorem R44951 : Reach 44951 := rs (se 1 (by rfl) ⟨33713, by rfl⟩) R67427
theorem R45017 : Reach 45017 := rs (se 2 (by rfl) ⟨16881, by rfl⟩) R33763
theorem R45131 : Reach 45131 := rs (se 1 (by rfl) ⟨33848, by rfl⟩) R67697
theorem R45143 : Reach 45143 := rs (se 1 (by rfl) ⟨33857, by rfl⟩) R67715
theorem R45209 : Reach 45209 := rs (se 2 (by rfl) ⟨16953, by rfl⟩) R33907
theorem R45323 : Reach 45323 := rs (se 1 (by rfl) ⟨33992, by rfl⟩) R67985
theorem R241937 : Reach 241937 := rs (se 2 (by rfl) ⟨90726, by rfl⟩) R181453
theorem R45335 : Reach 45335 := rs (se 1 (by rfl) ⟨34001, by rfl⟩) R68003
theorem R78155 : Reach 78155 := rs (se 1 (by rfl) ⟨58616, by rfl⟩) R117233
theorem R45401 : Reach 45401 := rs (se 2 (by rfl) ⟨17025, by rfl⟩) R34051
theorem R45515 : Reach 45515 := rs (se 1 (by rfl) ⟨34136, by rfl⟩) R68273
theorem R45527 : Reach 45527 := rs (se 1 (by rfl) ⟨34145, by rfl⟩) R68291
theorem R45593 : Reach 45593 := rs (se 2 (by rfl) ⟨17097, by rfl⟩) R34195
theorem R78401 : Reach 78401 := rs (se 2 (by rfl) ⟨29400, by rfl⟩) R58801
theorem R111179 : Reach 111179 := rs (se 1 (by rfl) ⟨83384, by rfl⟩) R166769
theorem R45707 : Reach 45707 := rs (se 1 (by rfl) ⟨34280, by rfl⟩) R68561
theorem R45719 : Reach 45719 := rs (se 1 (by rfl) ⟨34289, by rfl⟩) R68579
theorem R78529 : Reach 78529 := rs (se 2 (by rfl) ⟨29448, by rfl⟩) R58897
theorem R45785 : Reach 45785 := rs (se 2 (by rfl) ⟨17169, by rfl⟩) R34339
theorem R45899 : Reach 45899 := rs (se 1 (by rfl) ⟨34424, by rfl⟩) R68849
theorem R45911 : Reach 45911 := rs (se 1 (by rfl) ⟨34433, by rfl⟩) R68867
theorem R45913 : Reach 45913 := rs (se 2 (by rfl) ⟨17217, by rfl⟩) R34435
theorem R45977 : Reach 45977 := rs (se 2 (by rfl) ⟨17241, by rfl⟩) R34483
theorem R46091 : Reach 46091 := rs (se 1 (by rfl) ⟨34568, by rfl⟩) R69137
theorem R46103 : Reach 46103 := rs (se 1 (by rfl) ⟨34577, by rfl⟩) R69155
theorem R46169 : Reach 46169 := rs (se 2 (by rfl) ⟨17313, by rfl⟩) R34627
theorem R799895 : Reach 799895 := rs (se 1 (by rfl) ⟨599921, by rfl⟩) R1199843
theorem R79051 : Reach 79051 := rs (se 1 (by rfl) ⟨59288, by rfl⟩) R118577
theorem R46283 : Reach 46283 := rs (se 1 (by rfl) ⟨34712, by rfl⟩) R69425
theorem R46295 : Reach 46295 := rs (se 1 (by rfl) ⟨34721, by rfl⟩) R69443
theorem R46361 : Reach 46361 := rs (se 2 (by rfl) ⟨17385, by rfl⟩) R34771
theorem R46475 : Reach 46475 := rs (se 1 (by rfl) ⟨34856, by rfl⟩) R69713
theorem R46487 : Reach 46487 := rs (se 1 (by rfl) ⟨34865, by rfl⟩) R69731
theorem R46553 : Reach 46553 := rs (se 2 (by rfl) ⟨17457, by rfl⟩) R34915
theorem R79325 : Reach 79325 := rs (se 3 (by rfl) ⟨14873, by rfl⟩) R29747
theorem R210437 : Reach 210437 := rs (se 4 (by rfl) ⟨19728, by rfl⟩) R39457
theorem R46615 : Reach 46615 := rs (se 1 (by rfl) ⟨34961, by rfl⟩) R69923
theorem R46667 : Reach 46667 := rs (se 1 (by rfl) ⟨35000, by rfl⟩) R70001
theorem R144989 : Reach 144989 := rs (se 3 (by rfl) ⟨27185, by rfl⟩) R54371
theorem R177815 : Reach 177815 := rs (se 1 (by rfl) ⟨133361, by rfl⟩) R266723
theorem R112387 : Reach 112387 := rs (se 1 (by rfl) ⟨84290, by rfl⟩) R168581
theorem R79667 : Reach 79667 := rs (se 1 (by rfl) ⟨59750, by rfl⟩) R119501
theorem R112691 : Reach 112691 := rs (se 1 (by rfl) ⟨84518, by rfl⟩) R169037
theorem R79961 : Reach 79961 := rs (se 2 (by rfl) ⟨29985, by rfl⟩) R59971
theorem R47243 : Reach 47243 := rs (se 1 (by rfl) ⟨35432, by rfl⟩) R70865
theorem R47371 : Reach 47371 := rs (se 1 (by rfl) ⟨35528, by rfl⟩) R71057
theorem R47513 : Reach 47513 := rs (se 2 (by rfl) ⟨17817, by rfl⟩) R35635
theorem R47639 : Reach 47639 := rs (se 1 (by rfl) ⟨35729, by rfl⟩) R71459
theorem R47641 : Reach 47641 := rs (se 2 (by rfl) ⟨17865, by rfl⟩) R35731
theorem R113345 : Reach 113345 := rs (se 2 (by rfl) ⟨42504, by rfl⟩) R85009
theorem R211729 : Reach 211729 := rs (se 2 (by rfl) ⟨79398, by rfl⟩) R158797
theorem R211747 : Reach 211747 := rs (se 1 (by rfl) ⟨158810, by rfl⟩) R317621
theorem R375617 : Reach 375617 := rs (se 2 (by rfl) ⟨140856, by rfl⟩) R281713
theorem R48089 : Reach 48089 := rs (se 2 (by rfl) ⟨18033, by rfl⟩) R36067
theorem R48215 : Reach 48215 := rs (se 1 (by rfl) ⟨36161, by rfl⟩) R72323
theorem R965773 : Reach 965773 := rs (se 3 (by rfl) ⟨181082, by rfl⟩) R362165
theorem R48343 : Reach 48343 := rs (se 1 (by rfl) ⟨36257, by rfl⟩) R72515
theorem R4078997 : Reach 4078997 := rs (se 6 (by rfl) ⟨95601, by rfl⟩) R191203
theorem R179813 : Reach 179813 := rs (se 4 (by rfl) ⟨16857, by rfl⟩) R33715
theorem R48755 : Reach 48755 := rs (se 1 (by rfl) ⟨36566, by rfl⟩) R73133
theorem R147095 : Reach 147095 := rs (se 1 (by rfl) ⟨110321, by rfl⟩) R220643
theorem R48883 : Reach 48883 := rs (se 1 (by rfl) ⟨36662, by rfl⟩) R73325
theorem R81739 : Reach 81739 := rs (se 1 (by rfl) ⟨61304, by rfl⟩) R122609
theorem R48971 : Reach 48971 := rs (se 1 (by rfl) ⟨36728, by rfl⟩) R73457
theorem R49025 : Reach 49025 := rs (se 2 (by rfl) ⟨18384, by rfl⟩) R36769
theorem R212867 : Reach 212867 := rs (se 1 (by rfl) ⟨159650, by rfl⟩) R319301
theorem R114605 : Reach 114605 := rs (se 3 (by rfl) ⟨21488, by rfl⟩) R42977
theorem R114635 : Reach 114635 := rs (se 1 (by rfl) ⟨85976, by rfl⟩) R171953
theorem R49099 : Reach 49099 := rs (se 1 (by rfl) ⟨36824, by rfl⟩) R73649
theorem R49153 : Reach 49153 := rs (se 2 (by rfl) ⟨18432, by rfl⟩) R36865
theorem R49241 : Reach 49241 := rs (se 2 (by rfl) ⟨18465, by rfl⟩) R36931
theorem R49369 : Reach 49369 := rs (se 2 (by rfl) ⟨18513, by rfl⟩) R37027
theorem R82241 : Reach 82241 := rs (se 2 (by rfl) ⟨30840, by rfl⟩) R61681
theorem R115289 : Reach 115289 := rs (se 2 (by rfl) ⟨43233, by rfl⟩) R86467
theorem R82583 : Reach 82583 := rs (se 1 (by rfl) ⟨61937, by rfl⟩) R123875
theorem R49943 : Reach 49943 := rs (se 1 (by rfl) ⟨37457, by rfl⟩) R74915
theorem R50071 : Reach 50071 := rs (se 1 (by rfl) ⟨37553, by rfl⟩) R75107
theorem R115607 : Reach 115607 := rs (se 1 (by rfl) ⟨86705, by rfl⟩) R173411
theorem R115843 : Reach 115843 := rs (se 1 (by rfl) ⟨86882, by rfl⟩) R173765
theorem R50483 : Reach 50483 := rs (se 1 (by rfl) ⟨37862, by rfl⟩) R75725
theorem R148837 : Reach 148837 := rs (se 4 (by rfl) ⟨13953, by rfl⟩) R27907
theorem R50611 : Reach 50611 := rs (se 1 (by rfl) ⟨37958, by rfl⟩) R75917
theorem R50699 : Reach 50699 := rs (se 1 (by rfl) ⟨38024, by rfl⟩) R76049
theorem R116275 : Reach 116275 := rs (se 1 (by rfl) ⟨87206, by rfl⟩) R174413
theorem R50753 : Reach 50753 := rs (se 2 (by rfl) ⟨19032, by rfl⟩) R38065
theorem R476765 : Reach 476765 := rs (se 3 (by rfl) ⟨89393, by rfl⟩) R178787
theorem R149123 : Reach 149123 := rs (se 1 (by rfl) ⟨111842, by rfl⟩) R223685
theorem R50827 : Reach 50827 := rs (se 1 (by rfl) ⟨38120, by rfl⟩) R76241
theorem R50881 : Reach 50881 := rs (se 2 (by rfl) ⟨19080, by rfl⟩) R38161
theorem R50969 : Reach 50969 := rs (se 2 (by rfl) ⟨19113, by rfl⟩) R38227
theorem R51097 : Reach 51097 := rs (se 2 (by rfl) ⟨19161, by rfl⟩) R38323
theorem R116801 : Reach 116801 := rs (se 2 (by rfl) ⟨43800, by rfl⟩) R87601
theorem R968773 : Reach 968773 := rs (se 4 (by rfl) ⟨90822, by rfl⟩) R181645
theorem R51607 : Reach 51607 := rs (se 1 (by rfl) ⟨38705, by rfl⟩) R77411
theorem R51671 : Reach 51671 := rs (se 1 (by rfl) ⟨38753, by rfl⟩) R77507
theorem R51799 : Reach 51799 := rs (se 1 (by rfl) ⟨38849, by rfl⟩) R77699
theorem R215729 : Reach 215729 := rs (se 2 (by rfl) ⟨80898, by rfl⟩) R161797
theorem R84701 : Reach 84701 := rs (se 3 (by rfl) ⟨15881, by rfl⟩) R31763
theorem R117521 : Reach 117521 := rs (se 2 (by rfl) ⟨44070, by rfl⟩) R88141
theorem R84829 : Reach 84829 := rs (se 3 (by rfl) ⟨15905, by rfl⟩) R31811
theorem R52211 : Reach 52211 := rs (se 1 (by rfl) ⟨39158, by rfl⟩) R78317
theorem R85043 : Reach 85043 := rs (se 1 (by rfl) ⟨63782, by rfl⟩) R127565
theorem R52339 : Reach 52339 := rs (se 1 (by rfl) ⟨39254, by rfl⟩) R78509
theorem R150659 : Reach 150659 := rs (se 1 (by rfl) ⟨112994, by rfl⟩) R225989
theorem R52427 : Reach 52427 := rs (se 1 (by rfl) ⟨39320, by rfl⟩) R78641
theorem R216269 : Reach 216269 := rs (se 3 (by rfl) ⟨40550, by rfl⟩) R81101
theorem R52481 : Reach 52481 := rs (se 2 (by rfl) ⟨19680, by rfl⟩) R39361
theorem R118219 : Reach 118219 := rs (se 1 (by rfl) ⟨88664, by rfl⟩) R177329
theorem R249293 : Reach 249293 := rs (se 3 (by rfl) ⟨46742, by rfl⟩) R93485
theorem R118361 : Reach 118361 := rs (se 2 (by rfl) ⟨44385, by rfl⟩) R88771
theorem R216755 : Reach 216755 := rs (se 1 (by rfl) ⟨162566, by rfl⟩) R325133
theorem R118493 : Reach 118493 := rs (se 3 (by rfl) ⟨22217, by rfl⟩) R44435
theorem R53399 : Reach 53399 := rs (se 1 (by rfl) ⟨40049, by rfl⟩) R80099
theorem R348461 : Reach 348461 := rs (se 3 (by rfl) ⟨65336, by rfl⟩) R130673
theorem R53939 : Reach 53939 := rs (se 1 (by rfl) ⟨40454, by rfl⟩) R80909
theorem R53975 : Reach 53975 := rs (se 1 (by rfl) ⟨40481, by rfl⟩) R80963
theorem R218213 : Reach 218213 := rs (se 4 (by rfl) ⟨20457, by rfl⟩) R40915
theorem R316547 : Reach 316547 := rs (se 1 (by rfl) ⟨237410, by rfl⟩) R474821
theorem R54425 : Reach 54425 := rs (se 2 (by rfl) ⟨20409, by rfl⟩) R40819
theorem R87389 : Reach 87389 := rs (se 3 (by rfl) ⟨16385, by rfl⟩) R32771
theorem R87617 : Reach 87617 := rs (se 2 (by rfl) ⟨32856, by rfl⟩) R65713
theorem R218699 : Reach 218699 := rs (se 1 (by rfl) ⟨164024, by rfl⟩) R328049
theorem R87959 : Reach 87959 := rs (se 1 (by rfl) ⟨65969, by rfl⟩) R131939
theorem R55475 : Reach 55475 := rs (se 1 (by rfl) ⟨41606, by rfl⟩) R83213
theorem R121105 : Reach 121105 := rs (se 2 (by rfl) ⟨45414, by rfl⟩) R90829
theorem R88523 : Reach 88523 := rs (se 1 (by rfl) ⟨66392, by rfl⟩) R132785
theorem R88651 : Reach 88651 := rs (se 1 (by rfl) ⟨66488, by rfl⟩) R132977
theorem R55883 : Reach 55883 := rs (se 1 (by rfl) ⟨41912, by rfl⟩) R83825
theorem R56065 : Reach 56065 := rs (se 2 (by rfl) ⟨21024, by rfl⟩) R42049
theorem R154385 : Reach 154385 := rs (se 2 (by rfl) ⟨57894, by rfl⟩) R115789
theorem R154547 : Reach 154547 := rs (se 1 (by rfl) ⟨115910, by rfl⟩) R231821
theorem R285713 : Reach 285713 := rs (se 2 (by rfl) ⟨107142, by rfl⟩) R214285
theorem R56513 : Reach 56513 := rs (se 2 (by rfl) ⟨21192, by rfl⟩) R42385
theorem R253145 : Reach 253145 := rs (se 2 (by rfl) ⟨94929, by rfl⟩) R189859
theorem R56855 : Reach 56855 := rs (se 1 (by rfl) ⟨42641, by rfl⟩) R85283
theorem R155267 : Reach 155267 := rs (se 1 (by rfl) ⟨116450, by rfl⟩) R232901
theorem R57089 : Reach 57089 := rs (se 2 (by rfl) ⟨21408, by rfl⟩) R42817
theorem R450481 : Reach 450481 := rs (se 2 (by rfl) ⟨168930, by rfl⟩) R337861
theorem R516131 : Reach 516131 := rs (se 1 (by rfl) ⟨387098, by rfl⟩) R774197
theorem R90163 : Reach 90163 := rs (se 1 (by rfl) ⟨67622, by rfl⟩) R135245
theorem R352349 : Reach 352349 := rs (se 3 (by rfl) ⟨66065, by rfl⟩) R132131
theorem R57523 : Reach 57523 := rs (se 1 (by rfl) ⟨43142, by rfl⟩) R86285
theorem R90305 : Reach 90305 := rs (se 2 (by rfl) ⟨33864, by rfl⟩) R67729
theorem R90391 : Reach 90391 := rs (se 1 (by rfl) ⟨67793, by rfl⟩) R135587
theorem R156005 : Reach 156005 := rs (se 4 (by rfl) ⟨14625, by rfl⟩) R29251
theorem R57971 : Reach 57971 := rs (se 1 (by rfl) ⟨43478, by rfl⟩) R86957
theorem R58009 : Reach 58009 := rs (se 2 (by rfl) ⟨21753, by rfl⟩) R43507
theorem R254785 : Reach 254785 := rs (se 2 (by rfl) ⟨95544, by rfl⟩) R191089
theorem R156491 : Reach 156491 := rs (se 1 (by rfl) ⟨117368, by rfl⟩) R234737
theorem R58315 : Reach 58315 := rs (se 1 (by rfl) ⟨43736, by rfl⟩) R87473
theorem R2057237 : Reach 2057237 := rs (se 6 (by rfl) ⟨48216, by rfl⟩) R96433
theorem R58457 : Reach 58457 := rs (se 2 (by rfl) ⟨21921, by rfl⟩) R43843
theorem R58571 : Reach 58571 := rs (se 1 (by rfl) ⟨43928, by rfl⟩) R87857
theorem R58583 : Reach 58583 := rs (se 1 (by rfl) ⟨43937, by rfl⟩) R87875
theorem R124249 : Reach 124249 := rs (se 2 (by rfl) ⟨46593, by rfl⟩) R93187
theorem R124363 : Reach 124363 := rs (se 1 (by rfl) ⟨93272, by rfl⟩) R186545
theorem R91799 : Reach 91799 := rs (se 1 (by rfl) ⟨68849, by rfl⟩) R137699
theorem R91955 : Reach 91955 := rs (se 1 (by rfl) ⟨68966, by rfl⟩) R137933
theorem R124865 : Reach 124865 := rs (se 2 (by rfl) ⟨46824, by rfl⟩) R93649
theorem R59393 : Reach 59393 := rs (se 2 (by rfl) ⟨22272, by rfl⟩) R44545
theorem R59545 : Reach 59545 := rs (se 2 (by rfl) ⟨22329, by rfl⟩) R44659
theorem R92339 : Reach 92339 := rs (se 1 (by rfl) ⟨69254, by rfl⟩) R138509
theorem R583861 : Reach 583861 := rs (se 5 (by rfl) ⟨27368, by rfl⟩) R54737
theorem R59699 : Reach 59699 := rs (se 1 (by rfl) ⟨44774, by rfl⟩) R89549
theorem R92609 : Reach 92609 := rs (se 2 (by rfl) ⟨34728, by rfl⟩) R69457
theorem R190937 : Reach 190937 := rs (se 2 (by rfl) ⟨71601, by rfl⟩) R143203
theorem R27115 : Reach 27115 := rs (se 1 (by rfl) ⟨20336, by rfl⟩) R40673
theorem R27127 : Reach 27127 := rs (se 1 (by rfl) ⟨20345, by rfl⟩) R40691
theorem R27147 : Reach 27147 := rs (se 1 (by rfl) ⟨20360, by rfl⟩) R40721
theorem R27159 : Reach 27159 := rs (se 1 (by rfl) ⟨20369, by rfl⟩) R40739
theorem R256547 : Reach 256547 := rs (se 1 (by rfl) ⟨192410, by rfl⟩) R384821
theorem R27179 : Reach 27179 := rs (se 1 (by rfl) ⟨20384, by rfl⟩) R40769
theorem R27191 : Reach 27191 := rs (se 1 (by rfl) ⟨20393, by rfl⟩) R40787
theorem R27211 : Reach 27211 := rs (se 1 (by rfl) ⟨20408, by rfl⟩) R40817
theorem R27223 : Reach 27223 := rs (se 1 (by rfl) ⟨20417, by rfl⟩) R40835
theorem R92765 : Reach 92765 := rs (se 3 (by rfl) ⟨17393, by rfl⟩) R34787
theorem R27243 : Reach 27243 := rs (se 1 (by rfl) ⟨20432, by rfl⟩) R40865
theorem R27255 : Reach 27255 := rs (se 1 (by rfl) ⟨20441, by rfl⟩) R40883
theorem R27275 : Reach 27275 := rs (se 1 (by rfl) ⟨20456, by rfl⟩) R40913
theorem R27287 : Reach 27287 := rs (se 1 (by rfl) ⟨20465, by rfl⟩) R40931
theorem R27307 : Reach 27307 := rs (se 1 (by rfl) ⟨20480, by rfl⟩) R40961
theorem R27319 : Reach 27319 := rs (se 1 (by rfl) ⟨20489, by rfl⟩) R40979
theorem R27339 : Reach 27339 := rs (se 1 (by rfl) ⟨20504, by rfl⟩) R41009
theorem R27351 : Reach 27351 := rs (se 1 (by rfl) ⟨20513, by rfl⟩) R41027
theorem R27371 : Reach 27371 := rs (se 1 (by rfl) ⟨20528, by rfl⟩) R41057
theorem R27383 : Reach 27383 := rs (se 1 (by rfl) ⟨20537, by rfl⟩) R41075
theorem R27403 : Reach 27403 := rs (se 1 (by rfl) ⟨20552, by rfl⟩) R41105
theorem R27415 : Reach 27415 := rs (se 1 (by rfl) ⟨20561, by rfl⟩) R41123
theorem R27435 : Reach 27435 := rs (se 1 (by rfl) ⟨20576, by rfl⟩) R41153
theorem R224045 : Reach 224045 := rs (se 3 (by rfl) ⟨42008, by rfl⟩) R84017
theorem R60211 : Reach 60211 := rs (se 1 (by rfl) ⟨45158, by rfl⟩) R90317
theorem R27447 : Reach 27447 := rs (se 1 (by rfl) ⟨20585, by rfl⟩) R41171
theorem R27467 : Reach 27467 := rs (se 1 (by rfl) ⟨20600, by rfl⟩) R41201
theorem R27479 : Reach 27479 := rs (se 1 (by rfl) ⟨20609, by rfl⟩) R41219
theorem R158557 : Reach 158557 := rs (se 3 (by rfl) ⟨29729, by rfl⟩) R59459
theorem R191333 : Reach 191333 := rs (se 4 (by rfl) ⟨17937, by rfl⟩) R35875
theorem R27499 : Reach 27499 := rs (se 1 (by rfl) ⟨20624, by rfl⟩) R41249
theorem R27511 : Reach 27511 := rs (se 1 (by rfl) ⟨20633, by rfl⟩) R41267
theorem R27531 : Reach 27531 := rs (se 1 (by rfl) ⟨20648, by rfl⟩) R41297
theorem R27543 : Reach 27543 := rs (se 1 (by rfl) ⟨20657, by rfl⟩) R41315
theorem R27563 : Reach 27563 := rs (se 1 (by rfl) ⟨20672, by rfl⟩) R41345
theorem R322483 : Reach 322483 := rs (se 1 (by rfl) ⟨241862, by rfl⟩) R483725
theorem R27575 : Reach 27575 := rs (se 1 (by rfl) ⟨20681, by rfl⟩) R41363
theorem R27595 : Reach 27595 := rs (se 1 (by rfl) ⟨20696, by rfl⟩) R41393
theorem R27607 : Reach 27607 := rs (se 1 (by rfl) ⟨20705, by rfl⟩) R41411
theorem R93149 : Reach 93149 := rs (se 3 (by rfl) ⟨17465, by rfl⟩) R34931
theorem R27627 : Reach 27627 := rs (se 1 (by rfl) ⟨20720, by rfl⟩) R41441
theorem R27639 : Reach 27639 := rs (se 1 (by rfl) ⟨20729, by rfl⟩) R41459
theorem R27659 : Reach 27659 := rs (se 1 (by rfl) ⟨20744, by rfl⟩) R41489
theorem R27671 : Reach 27671 := rs (se 1 (by rfl) ⟨20753, by rfl⟩) R41507
theorem R27691 : Reach 27691 := rs (se 1 (by rfl) ⟨20768, by rfl⟩) R41537
theorem R27703 : Reach 27703 := rs (se 1 (by rfl) ⟨20777, by rfl⟩) R41555
theorem R27723 : Reach 27723 := rs (se 1 (by rfl) ⟨20792, by rfl⟩) R41585
theorem R27735 : Reach 27735 := rs (se 1 (by rfl) ⟨20801, by rfl⟩) R41603
theorem R27755 : Reach 27755 := rs (se 1 (by rfl) ⟨20816, by rfl⟩) R41633
theorem R27767 : Reach 27767 := rs (se 1 (by rfl) ⟨20825, by rfl⟩) R41651
theorem R27787 : Reach 27787 := rs (se 1 (by rfl) ⟨20840, by rfl⟩) R41681
theorem R27799 : Reach 27799 := rs (se 1 (by rfl) ⟨20849, by rfl⟩) R41699
theorem R27819 : Reach 27819 := rs (se 1 (by rfl) ⟨20864, by rfl⟩) R41729
theorem R27831 : Reach 27831 := rs (se 1 (by rfl) ⟨20873, by rfl⟩) R41747
theorem R27851 : Reach 27851 := rs (se 1 (by rfl) ⟨20888, by rfl⟩) R41777
theorem R27863 : Reach 27863 := rs (se 1 (by rfl) ⟨20897, by rfl⟩) R41795
theorem R27883 : Reach 27883 := rs (se 1 (by rfl) ⟨20912, by rfl⟩) R41825
theorem R60659 : Reach 60659 := rs (se 1 (by rfl) ⟨45494, by rfl⟩) R90989
theorem R27895 : Reach 27895 := rs (se 1 (by rfl) ⟨20921, by rfl⟩) R41843
theorem R27915 : Reach 27915 := rs (se 1 (by rfl) ⟨20936, by rfl⟩) R41873
theorem R27927 : Reach 27927 := rs (se 1 (by rfl) ⟨20945, by rfl⟩) R41891
theorem R27947 : Reach 27947 := rs (se 1 (by rfl) ⟨20960, by rfl⟩) R41921
theorem R27959 : Reach 27959 := rs (se 1 (by rfl) ⟨20969, by rfl⟩) R41939
theorem R27979 : Reach 27979 := rs (se 1 (by rfl) ⟨20984, by rfl⟩) R41969
theorem R27991 : Reach 27991 := rs (se 1 (by rfl) ⟨20993, by rfl⟩) R41987
theorem R28011 : Reach 28011 := rs (se 1 (by rfl) ⟨21008, by rfl⟩) R42017
theorem R28023 : Reach 28023 := rs (se 1 (by rfl) ⟨21017, by rfl⟩) R42035
theorem R28043 : Reach 28043 := rs (se 1 (by rfl) ⟨21032, by rfl⟩) R42065
theorem R28055 : Reach 28055 := rs (se 1 (by rfl) ⟨21041, by rfl⟩) R42083
theorem R28075 : Reach 28075 := rs (se 1 (by rfl) ⟨21056, by rfl⟩) R42113
theorem R28087 : Reach 28087 := rs (se 1 (by rfl) ⟨21065, by rfl⟩) R42131
theorem R28107 : Reach 28107 := rs (se 1 (by rfl) ⟨21080, by rfl⟩) R42161
theorem R28119 : Reach 28119 := rs (se 1 (by rfl) ⟨21089, by rfl⟩) R42179
theorem R60887 : Reach 60887 := rs (se 1 (by rfl) ⟨45665, by rfl⟩) R91331
theorem R28139 : Reach 28139 := rs (se 1 (by rfl) ⟨21104, by rfl⟩) R42209
theorem R28151 : Reach 28151 := rs (se 1 (by rfl) ⟨21113, by rfl⟩) R42227
theorem R60929 : Reach 60929 := rs (se 2 (by rfl) ⟨22848, by rfl⟩) R45697
theorem R28171 : Reach 28171 := rs (se 1 (by rfl) ⟨21128, by rfl⟩) R42257
theorem R28183 : Reach 28183 := rs (se 1 (by rfl) ⟨21137, by rfl⟩) R42275
theorem R28203 : Reach 28203 := rs (se 1 (by rfl) ⟨21152, by rfl⟩) R42305
theorem R28215 : Reach 28215 := rs (se 1 (by rfl) ⟨21161, by rfl⟩) R42323
theorem R93761 : Reach 93761 := rs (se 2 (by rfl) ⟨35160, by rfl⟩) R70321
theorem R28235 : Reach 28235 := rs (se 1 (by rfl) ⟨21176, by rfl⟩) R42353
theorem R28247 : Reach 28247 := rs (se 1 (by rfl) ⟨21185, by rfl⟩) R42371
theorem R28267 : Reach 28267 := rs (se 1 (by rfl) ⟨21200, by rfl⟩) R42401
theorem R28279 : Reach 28279 := rs (se 1 (by rfl) ⟨21209, by rfl⟩) R42419
theorem R388739 : Reach 388739 := rs (se 1 (by rfl) ⟨291554, by rfl⟩) R583109
theorem R28299 : Reach 28299 := rs (se 1 (by rfl) ⟨21224, by rfl⟩) R42449
theorem R28311 : Reach 28311 := rs (se 1 (by rfl) ⟨21233, by rfl⟩) R42467
theorem R28331 : Reach 28331 := rs (se 1 (by rfl) ⟨21248, by rfl⟩) R42497
theorem R28343 : Reach 28343 := rs (se 1 (by rfl) ⟨21257, by rfl⟩) R42515
theorem R93889 : Reach 93889 := rs (se 2 (by rfl) ⟨35208, by rfl⟩) R70417
theorem R28363 : Reach 28363 := rs (se 1 (by rfl) ⟨21272, by rfl⟩) R42545
theorem R454349 : Reach 454349 := rs (se 3 (by rfl) ⟨85190, by rfl⟩) R170381
theorem R28375 : Reach 28375 := rs (se 1 (by rfl) ⟨21281, by rfl⟩) R42563
theorem R61145 : Reach 61145 := rs (se 2 (by rfl) ⟨22929, by rfl⟩) R45859
theorem R28395 : Reach 28395 := rs (se 1 (by rfl) ⟨21296, by rfl⟩) R42593
theorem R28407 : Reach 28407 := rs (se 1 (by rfl) ⟨21305, by rfl⟩) R42611
theorem R28427 : Reach 28427 := rs (se 1 (by rfl) ⟨21320, by rfl⟩) R42641
theorem R28439 : Reach 28439 := rs (se 1 (by rfl) ⟨21329, by rfl⟩) R42659
theorem R28459 : Reach 28459 := rs (se 1 (by rfl) ⟨21344, by rfl⟩) R42689
theorem R61235 : Reach 61235 := rs (se 1 (by rfl) ⟨45926, by rfl⟩) R91853
theorem R28471 : Reach 28471 := rs (se 1 (by rfl) ⟨21353, by rfl⟩) R42707
theorem R28491 : Reach 28491 := rs (se 1 (by rfl) ⟨21368, by rfl⟩) R42737
theorem R61271 : Reach 61271 := rs (se 1 (by rfl) ⟨45953, by rfl⟩) R91907
theorem R28503 : Reach 28503 := rs (se 1 (by rfl) ⟨21377, by rfl⟩) R42755
theorem R28523 : Reach 28523 := rs (se 1 (by rfl) ⟨21392, by rfl⟩) R42785
theorem R28535 : Reach 28535 := rs (se 1 (by rfl) ⟨21401, by rfl⟩) R42803
theorem R28555 : Reach 28555 := rs (se 1 (by rfl) ⟨21416, by rfl⟩) R42833
theorem R28567 : Reach 28567 := rs (se 1 (by rfl) ⟨21425, by rfl⟩) R42851
theorem R28587 : Reach 28587 := rs (se 1 (by rfl) ⟨21440, by rfl⟩) R42881
theorem R28599 : Reach 28599 := rs (se 1 (by rfl) ⟨21449, by rfl⟩) R42899
theorem R28619 : Reach 28619 := rs (se 1 (by rfl) ⟨21464, by rfl⟩) R42929
theorem R28631 : Reach 28631 := rs (se 1 (by rfl) ⟨21473, by rfl⟩) R42947
theorem R28651 : Reach 28651 := rs (se 1 (by rfl) ⟨21488, by rfl⟩) R42977
theorem R28663 : Reach 28663 := rs (se 1 (by rfl) ⟨21497, by rfl⟩) R42995
theorem R61451 : Reach 61451 := rs (se 1 (by rfl) ⟨46088, by rfl⟩) R92177
theorem R28683 : Reach 28683 := rs (se 1 (by rfl) ⟨21512, by rfl⟩) R43025
theorem R28695 : Reach 28695 := rs (se 1 (by rfl) ⟨21521, by rfl⟩) R43043
theorem R28715 : Reach 28715 := rs (se 1 (by rfl) ⟨21536, by rfl⟩) R43073
theorem R28727 : Reach 28727 := rs (se 1 (by rfl) ⟨21545, by rfl⟩) R43091
theorem R61505 : Reach 61505 := rs (se 2 (by rfl) ⟨23064, by rfl⟩) R46129
theorem R192577 : Reach 192577 := rs (se 2 (by rfl) ⟨72216, by rfl⟩) R144433
theorem R94283 : Reach 94283 := rs (se 1 (by rfl) ⟨70712, by rfl⟩) R141425
theorem R28747 : Reach 28747 := rs (se 1 (by rfl) ⟨21560, by rfl⟩) R43121
theorem R28759 : Reach 28759 := rs (se 1 (by rfl) ⟨21569, by rfl⟩) R43139
theorem R28779 : Reach 28779 := rs (se 1 (by rfl) ⟨21584, by rfl⟩) R43169
theorem R28791 : Reach 28791 := rs (se 1 (by rfl) ⟨21593, by rfl⟩) R43187
theorem R28811 : Reach 28811 := rs (se 1 (by rfl) ⟨21608, by rfl⟩) R43217
theorem R28823 : Reach 28823 := rs (se 1 (by rfl) ⟨21617, by rfl⟩) R43235
theorem R28843 : Reach 28843 := rs (se 1 (by rfl) ⟨21632, by rfl⟩) R43265
theorem R28855 : Reach 28855 := rs (se 1 (by rfl) ⟨21641, by rfl⟩) R43283
theorem R28875 : Reach 28875 := rs (se 1 (by rfl) ⟨21656, by rfl⟩) R43313
theorem R28887 : Reach 28887 := rs (se 1 (by rfl) ⟨21665, by rfl⟩) R43331
theorem R28907 : Reach 28907 := rs (se 1 (by rfl) ⟨21680, by rfl⟩) R43361
theorem R28919 : Reach 28919 := rs (se 1 (by rfl) ⟨21689, by rfl⟩) R43379
theorem R28939 : Reach 28939 := rs (se 1 (by rfl) ⟨21704, by rfl⟩) R43409
theorem R28951 : Reach 28951 := rs (se 1 (by rfl) ⟨21713, by rfl⟩) R43427
theorem R61721 : Reach 61721 := rs (se 2 (by rfl) ⟨23145, by rfl⟩) R46291
theorem R28971 : Reach 28971 := rs (se 1 (by rfl) ⟨21728, by rfl⟩) R43457
theorem R28983 : Reach 28983 := rs (se 1 (by rfl) ⟨21737, by rfl⟩) R43475
theorem R29003 : Reach 29003 := rs (se 1 (by rfl) ⟨21752, by rfl⟩) R43505
theorem R29015 : Reach 29015 := rs (se 1 (by rfl) ⟨21761, by rfl⟩) R43523
theorem R94553 : Reach 94553 := rs (se 2 (by rfl) ⟨35457, by rfl⟩) R70915
theorem R127325 : Reach 127325 := rs (se 3 (by rfl) ⟨23873, by rfl⟩) R47747
theorem R29035 : Reach 29035 := rs (se 1 (by rfl) ⟨21776, by rfl⟩) R43553
theorem R61811 : Reach 61811 := rs (se 1 (by rfl) ⟨46358, by rfl⟩) R92717
theorem R29047 : Reach 29047 := rs (se 1 (by rfl) ⟨21785, by rfl⟩) R43571
theorem R29067 : Reach 29067 := rs (se 1 (by rfl) ⟨21800, by rfl⟩) R43601
theorem R61847 : Reach 61847 := rs (se 1 (by rfl) ⟨46385, by rfl⟩) R92771
theorem R29079 : Reach 29079 := rs (se 1 (by rfl) ⟨21809, by rfl⟩) R43619
theorem R29099 : Reach 29099 := rs (se 1 (by rfl) ⟨21824, by rfl⟩) R43649
theorem R29111 : Reach 29111 := rs (se 1 (by rfl) ⟨21833, by rfl⟩) R43667
theorem R29131 : Reach 29131 := rs (se 1 (by rfl) ⟨21848, by rfl⟩) R43697
theorem R29143 : Reach 29143 := rs (se 1 (by rfl) ⟨21857, by rfl⟩) R43715
theorem R29163 : Reach 29163 := rs (se 1 (by rfl) ⟨21872, by rfl⟩) R43745
theorem R29175 : Reach 29175 := rs (se 1 (by rfl) ⟨21881, by rfl⟩) R43763
theorem R29195 : Reach 29195 := rs (se 1 (by rfl) ⟨21896, by rfl⟩) R43793
theorem R29207 : Reach 29207 := rs (se 1 (by rfl) ⟨21905, by rfl⟩) R43811
theorem R29227 : Reach 29227 := rs (se 1 (by rfl) ⟨21920, by rfl⟩) R43841
theorem R29239 : Reach 29239 := rs (se 1 (by rfl) ⟨21929, by rfl⟩) R43859
theorem R62027 : Reach 62027 := rs (se 1 (by rfl) ⟨46520, by rfl⟩) R93041
theorem R29259 : Reach 29259 := rs (se 1 (by rfl) ⟨21944, by rfl⟩) R43889
theorem R29271 : Reach 29271 := rs (se 1 (by rfl) ⟨21953, by rfl⟩) R43907
theorem R29291 : Reach 29291 := rs (se 1 (by rfl) ⟨21968, by rfl⟩) R43937
theorem R29303 : Reach 29303 := rs (se 1 (by rfl) ⟨21977, by rfl⟩) R43955
theorem R62081 : Reach 62081 := rs (se 2 (by rfl) ⟨23280, by rfl⟩) R46561
theorem R29323 : Reach 29323 := rs (se 1 (by rfl) ⟨21992, by rfl⟩) R43985
theorem R29335 : Reach 29335 := rs (se 1 (by rfl) ⟨22001, by rfl⟩) R44003
theorem R29355 : Reach 29355 := rs (se 1 (by rfl) ⟨22016, by rfl⟩) R44033
theorem R29367 : Reach 29367 := rs (se 1 (by rfl) ⟨22025, by rfl⟩) R44051
theorem R29387 : Reach 29387 := rs (se 1 (by rfl) ⟨22040, by rfl⟩) R44081
theorem R29399 : Reach 29399 := rs (se 1 (by rfl) ⟨22049, by rfl⟩) R44099
theorem R29419 : Reach 29419 := rs (se 1 (by rfl) ⟨22064, by rfl⟩) R44129
theorem R29431 : Reach 29431 := rs (se 1 (by rfl) ⟨22073, by rfl⟩) R44147
theorem R29451 : Reach 29451 := rs (se 1 (by rfl) ⟨22088, by rfl⟩) R44177
theorem R29463 : Reach 29463 := rs (se 1 (by rfl) ⟨22097, by rfl⟩) R44195
theorem R29483 : Reach 29483 := rs (se 1 (by rfl) ⟨22112, by rfl⟩) R44225
theorem R29495 : Reach 29495 := rs (se 1 (by rfl) ⟨22121, by rfl⟩) R44243
theorem R29515 : Reach 29515 := rs (se 1 (by rfl) ⟨22136, by rfl⟩) R44273
theorem R29527 : Reach 29527 := rs (se 1 (by rfl) ⟨22145, by rfl⟩) R44291
theorem R62297 : Reach 62297 := rs (se 2 (by rfl) ⟨23361, by rfl⟩) R46723
theorem R29547 : Reach 29547 := rs (se 1 (by rfl) ⟨22160, by rfl⟩) R44321
theorem R29559 : Reach 29559 := rs (se 1 (by rfl) ⟨22169, by rfl⟩) R44339
theorem R29579 : Reach 29579 := rs (se 1 (by rfl) ⟨22184, by rfl⟩) R44369
theorem R29591 : Reach 29591 := rs (se 1 (by rfl) ⟨22193, by rfl⟩) R44387
theorem R29611 : Reach 29611 := rs (se 1 (by rfl) ⟨22208, by rfl⟩) R44417
theorem R488369 : Reach 488369 := rs (se 2 (by rfl) ⟨183138, by rfl⟩) R366277
theorem R62387 : Reach 62387 := rs (se 1 (by rfl) ⟨46790, by rfl⟩) R93581
theorem R29623 : Reach 29623 := rs (se 1 (by rfl) ⟨22217, by rfl⟩) R44435
theorem R29643 : Reach 29643 := rs (se 1 (by rfl) ⟨22232, by rfl⟩) R44465
theorem R226253 : Reach 226253 := rs (se 3 (by rfl) ⟨42422, by rfl⟩) R84845
theorem R62423 : Reach 62423 := rs (se 1 (by rfl) ⟨46817, by rfl⟩) R93635
theorem R29655 : Reach 29655 := rs (se 1 (by rfl) ⟨22241, by rfl⟩) R44483
theorem R29675 : Reach 29675 := rs (se 1 (by rfl) ⟨22256, by rfl⟩) R44513
theorem R29687 : Reach 29687 := rs (se 1 (by rfl) ⟨22265, by rfl⟩) R44531
theorem R29707 : Reach 29707 := rs (se 1 (by rfl) ⟨22280, by rfl⟩) R44561
theorem R95255 : Reach 95255 := rs (se 1 (by rfl) ⟨71441, by rfl⟩) R142883
theorem R29719 : Reach 29719 := rs (se 1 (by rfl) ⟨22289, by rfl⟩) R44579
theorem R29739 : Reach 29739 := rs (se 1 (by rfl) ⟨22304, by rfl⟩) R44609
theorem R29751 : Reach 29751 := rs (se 1 (by rfl) ⟨22313, by rfl⟩) R44627
theorem R422981 : Reach 422981 := rs (se 4 (by rfl) ⟨39654, by rfl⟩) R79309
theorem R29771 : Reach 29771 := rs (se 1 (by rfl) ⟨22328, by rfl⟩) R44657
theorem R29783 : Reach 29783 := rs (se 1 (by rfl) ⟨22337, by rfl⟩) R44675
theorem R95321 : Reach 95321 := rs (se 2 (by rfl) ⟨35745, by rfl⟩) R71491
theorem R29803 : Reach 29803 := rs (se 1 (by rfl) ⟨22352, by rfl⟩) R44705
theorem R29815 : Reach 29815 := rs (se 1 (by rfl) ⟨22361, by rfl⟩) R44723
theorem R62603 : Reach 62603 := rs (se 1 (by rfl) ⟨46952, by rfl⟩) R93905
theorem R29835 : Reach 29835 := rs (se 1 (by rfl) ⟨22376, by rfl⟩) R44753
theorem R29847 : Reach 29847 := rs (se 1 (by rfl) ⟨22385, by rfl⟩) R44771
theorem R29867 : Reach 29867 := rs (se 1 (by rfl) ⟨22400, by rfl⟩) R44801
theorem R29879 : Reach 29879 := rs (se 1 (by rfl) ⟨22409, by rfl⟩) R44819
theorem R62657 : Reach 62657 := rs (se 2 (by rfl) ⟨23496, by rfl⟩) R46993
theorem R95435 : Reach 95435 := rs (se 1 (by rfl) ⟨71576, by rfl⟩) R143153
theorem R29899 : Reach 29899 := rs (se 1 (by rfl) ⟨22424, by rfl⟩) R44849
theorem R29911 : Reach 29911 := rs (se 1 (by rfl) ⟨22433, by rfl⟩) R44867
theorem R29931 : Reach 29931 := rs (se 1 (by rfl) ⟨22448, by rfl⟩) R44897
theorem R29943 : Reach 29943 := rs (se 1 (by rfl) ⟨22457, by rfl⟩) R44915
theorem R29963 : Reach 29963 := rs (se 1 (by rfl) ⟨22472, by rfl⟩) R44945
theorem R161041 : Reach 161041 := rs (se 2 (by rfl) ⟨60390, by rfl⟩) R120781
theorem R29975 : Reach 29975 := rs (se 1 (by rfl) ⟨22481, by rfl⟩) R44963
theorem R29995 : Reach 29995 := rs (se 1 (by rfl) ⟨22496, by rfl⟩) R44993
theorem R30007 : Reach 30007 := rs (se 1 (by rfl) ⟨22505, by rfl⟩) R45011
theorem R30027 : Reach 30027 := rs (se 1 (by rfl) ⟨22520, by rfl⟩) R45041
theorem R30039 : Reach 30039 := rs (se 1 (by rfl) ⟨22529, by rfl⟩) R45059
theorem R30059 : Reach 30059 := rs (se 1 (by rfl) ⟨22544, by rfl⟩) R45089
theorem R30071 : Reach 30071 := rs (se 1 (by rfl) ⟨22553, by rfl⟩) R45107
theorem R30091 : Reach 30091 := rs (se 1 (by rfl) ⟨22568, by rfl⟩) R45137
theorem R30103 : Reach 30103 := rs (se 1 (by rfl) ⟨22577, by rfl⟩) R45155
theorem R62873 : Reach 62873 := rs (se 2 (by rfl) ⟨23577, by rfl⟩) R47155
theorem R30123 : Reach 30123 := rs (se 1 (by rfl) ⟨22592, by rfl⟩) R45185
theorem R30135 : Reach 30135 := rs (se 1 (by rfl) ⟨22601, by rfl⟩) R45203
theorem R30155 : Reach 30155 := rs (se 1 (by rfl) ⟨22616, by rfl⟩) R45233
theorem R30167 : Reach 30167 := rs (se 1 (by rfl) ⟨22625, by rfl⟩) R45251
theorem R30187 : Reach 30187 := rs (se 1 (by rfl) ⟨22640, by rfl⟩) R45281
theorem R62963 : Reach 62963 := rs (se 1 (by rfl) ⟨47222, by rfl⟩) R94445
theorem R30199 : Reach 30199 := rs (se 1 (by rfl) ⟨22649, by rfl⟩) R45299
theorem R30219 : Reach 30219 := rs (se 1 (by rfl) ⟨22664, by rfl⟩) R45329
theorem R62999 : Reach 62999 := rs (se 1 (by rfl) ⟨47249, by rfl⟩) R94499
theorem R30231 : Reach 30231 := rs (se 1 (by rfl) ⟨22673, by rfl⟩) R45347
theorem R30251 : Reach 30251 := rs (se 1 (by rfl) ⟨22688, by rfl⟩) R45377
theorem R95795 : Reach 95795 := rs (se 1 (by rfl) ⟨71846, by rfl⟩) R143693
theorem R30263 : Reach 30263 := rs (se 1 (by rfl) ⟨22697, by rfl⟩) R45395
theorem R30283 : Reach 30283 := rs (se 1 (by rfl) ⟨22712, by rfl⟩) R45425
theorem R30295 : Reach 30295 := rs (se 1 (by rfl) ⟨22721, by rfl⟩) R45443
theorem R30315 : Reach 30315 := rs (se 1 (by rfl) ⟨22736, by rfl⟩) R45473
theorem R30327 : Reach 30327 := rs (se 1 (by rfl) ⟨22745, by rfl⟩) R45491
theorem R30347 : Reach 30347 := rs (se 1 (by rfl) ⟨22760, by rfl⟩) R45521
theorem R30359 : Reach 30359 := rs (se 1 (by rfl) ⟨22769, by rfl⟩) R45539
theorem R30379 : Reach 30379 := rs (se 1 (by rfl) ⟨22784, by rfl⟩) R45569
theorem R30391 : Reach 30391 := rs (se 1 (by rfl) ⟨22793, by rfl⟩) R45587
theorem R63179 : Reach 63179 := rs (se 1 (by rfl) ⟨47384, by rfl⟩) R94769
theorem R30411 : Reach 30411 := rs (se 1 (by rfl) ⟨22808, by rfl⟩) R45617
theorem R30423 : Reach 30423 := rs (se 1 (by rfl) ⟨22817, by rfl⟩) R45635
theorem R30443 : Reach 30443 := rs (se 1 (by rfl) ⟨22832, by rfl⟩) R45665
theorem R30455 : Reach 30455 := rs (se 1 (by rfl) ⟨22841, by rfl⟩) R45683
theorem R63233 : Reach 63233 := rs (se 2 (by rfl) ⟨23712, by rfl⟩) R47425
theorem R30475 : Reach 30475 := rs (se 1 (by rfl) ⟨22856, by rfl⟩) R45713
theorem R30487 : Reach 30487 := rs (se 1 (by rfl) ⟨22865, by rfl⟩) R45731
theorem R30507 : Reach 30507 := rs (se 1 (by rfl) ⟨22880, by rfl⟩) R45761
theorem R30519 : Reach 30519 := rs (se 1 (by rfl) ⟨22889, by rfl⟩) R45779
theorem R96065 : Reach 96065 := rs (se 2 (by rfl) ⟨36024, by rfl⟩) R72049
theorem R30539 : Reach 30539 := rs (se 1 (by rfl) ⟨22904, by rfl⟩) R45809
theorem R30551 : Reach 30551 := rs (se 1 (by rfl) ⟨22913, by rfl⟩) R45827
theorem R30571 : Reach 30571 := rs (se 1 (by rfl) ⟨22928, by rfl⟩) R45857
theorem R30583 : Reach 30583 := rs (se 1 (by rfl) ⟨22937, by rfl⟩) R45875
theorem R30603 : Reach 30603 := rs (se 1 (by rfl) ⟨22952, by rfl⟩) R45905
theorem R30615 : Reach 30615 := rs (se 1 (by rfl) ⟨22961, by rfl⟩) R45923
theorem R30635 : Reach 30635 := rs (se 1 (by rfl) ⟨22976, by rfl⟩) R45953
theorem R30647 : Reach 30647 := rs (se 1 (by rfl) ⟨22985, by rfl⟩) R45971
theorem R30667 : Reach 30667 := rs (se 1 (by rfl) ⟨23000, by rfl⟩) R46001
theorem R30679 : Reach 30679 := rs (se 1 (by rfl) ⟨23009, by rfl⟩) R46019
theorem R63449 : Reach 63449 := rs (se 2 (by rfl) ⟨23793, by rfl⟩) R47587
theorem R30699 : Reach 30699 := rs (se 1 (by rfl) ⟨23024, by rfl⟩) R46049
theorem R30711 : Reach 30711 := rs (se 1 (by rfl) ⟨23033, by rfl⟩) R46067
theorem R30731 : Reach 30731 := rs (se 1 (by rfl) ⟨23048, by rfl⟩) R46097
theorem R30743 : Reach 30743 := rs (se 1 (by rfl) ⟨23057, by rfl⟩) R46115
theorem R30763 : Reach 30763 := rs (se 1 (by rfl) ⟨23072, by rfl⟩) R46145
theorem R63539 : Reach 63539 := rs (se 1 (by rfl) ⟨47654, by rfl⟩) R95309
theorem R30775 : Reach 30775 := rs (se 1 (by rfl) ⟨23081, by rfl⟩) R46163
theorem R30795 : Reach 30795 := rs (se 1 (by rfl) ⟨23096, by rfl⟩) R46193
theorem R63575 : Reach 63575 := rs (se 1 (by rfl) ⟨47681, by rfl⟩) R95363
theorem R30807 : Reach 30807 := rs (se 1 (by rfl) ⟨23105, by rfl⟩) R46211
theorem R30827 : Reach 30827 := rs (se 1 (by rfl) ⟨23120, by rfl⟩) R46241
theorem R30839 : Reach 30839 := rs (se 1 (by rfl) ⟨23129, by rfl⟩) R46259
theorem R30859 : Reach 30859 := rs (se 1 (by rfl) ⟨23144, by rfl⟩) R46289
theorem R30871 : Reach 30871 := rs (se 1 (by rfl) ⟨23153, by rfl⟩) R46307
theorem R30891 : Reach 30891 := rs (se 1 (by rfl) ⟨23168, by rfl⟩) R46337
theorem R30903 : Reach 30903 := rs (se 1 (by rfl) ⟨23177, by rfl⟩) R46355
theorem R30923 : Reach 30923 := rs (se 1 (by rfl) ⟨23192, by rfl⟩) R46385
theorem R30935 : Reach 30935 := rs (se 1 (by rfl) ⟨23201, by rfl⟩) R46403
theorem R30955 : Reach 30955 := rs (se 1 (by rfl) ⟨23216, by rfl⟩) R46433
theorem R30967 : Reach 30967 := rs (se 1 (by rfl) ⟨23225, by rfl⟩) R46451
theorem R63755 : Reach 63755 := rs (se 1 (by rfl) ⟨47816, by rfl⟩) R95633
theorem R30987 : Reach 30987 := rs (se 1 (by rfl) ⟨23240, by rfl⟩) R46481
theorem R30999 : Reach 30999 := rs (se 1 (by rfl) ⟨23249, by rfl⟩) R46499
theorem R31019 : Reach 31019 := rs (se 1 (by rfl) ⟨23264, by rfl⟩) R46529
theorem R31031 : Reach 31031 := rs (se 1 (by rfl) ⟨23273, by rfl⟩) R46547
theorem R63809 : Reach 63809 := rs (se 2 (by rfl) ⟨23928, by rfl⟩) R47857
theorem R31051 : Reach 31051 := rs (se 1 (by rfl) ⟨23288, by rfl⟩) R46577
theorem R227659 : Reach 227659 := rs (se 1 (by rfl) ⟨170744, by rfl⟩) R341489
theorem R31063 : Reach 31063 := rs (se 1 (by rfl) ⟨23297, by rfl⟩) R46595
theorem R63833 : Reach 63833 := rs (se 2 (by rfl) ⟨23937, by rfl⟩) R47875
theorem R96605 : Reach 96605 := rs (se 3 (by rfl) ⟨18113, by rfl⟩) R36227
theorem R31083 : Reach 31083 := rs (se 1 (by rfl) ⟨23312, by rfl⟩) R46625
theorem R31095 : Reach 31095 := rs (se 1 (by rfl) ⟨23321, by rfl⟩) R46643
theorem R326105 : Reach 326105 := rs (se 2 (by rfl) ⟨122289, by rfl⟩) R244579
theorem R31243 : Reach 31243 := rs (se 1 (by rfl) ⟨23432, by rfl⟩) R46865
theorem R64025 : Reach 64025 := rs (se 2 (by rfl) ⟨24009, by rfl⟩) R48019
theorem R391715 : Reach 391715 := rs (se 1 (by rfl) ⟨293786, by rfl⟩) R587573
theorem R227933 : Reach 227933 := rs (se 3 (by rfl) ⟨42737, by rfl⟩) R85475
theorem R64115 : Reach 64115 := rs (se 1 (by rfl) ⟨48086, by rfl⟩) R96173
theorem R31351 : Reach 31351 := rs (se 1 (by rfl) ⟨23513, by rfl⟩) R47027
theorem R64151 : Reach 64151 := rs (se 1 (by rfl) ⟨48113, by rfl⟩) R96227
theorem R64243 : Reach 64243 := rs (se 1 (by rfl) ⟨48182, by rfl⟩) R96365
theorem R31531 : Reach 31531 := rs (se 1 (by rfl) ⟨23648, by rfl⟩) R47297
theorem R64331 : Reach 64331 := rs (se 1 (by rfl) ⟨48248, by rfl⟩) R96497
theorem R129923 : Reach 129923 := rs (se 1 (by rfl) ⟨97442, by rfl⟩) R194885
theorem R31639 : Reach 31639 := rs (se 1 (by rfl) ⟨23729, by rfl⟩) R47459
theorem R64577 : Reach 64577 := rs (se 2 (by rfl) ⟨24216, by rfl⟩) R48433
theorem R31819 : Reach 31819 := rs (se 1 (by rfl) ⟨23864, by rfl⟩) R47729
theorem R64601 : Reach 64601 := rs (se 2 (by rfl) ⟨24225, by rfl⟩) R48451
theorem R64691 : Reach 64691 := rs (se 1 (by rfl) ⟨48518, by rfl⟩) R97037
theorem R31927 : Reach 31927 := rs (se 1 (by rfl) ⟨23945, by rfl⟩) R47891
theorem R130349 : Reach 130349 := rs (se 3 (by rfl) ⟨24440, by rfl⟩) R48881
theorem R32107 : Reach 32107 := rs (se 1 (by rfl) ⟨24080, by rfl⟩) R48161
theorem R64961 : Reach 64961 := rs (se 2 (by rfl) ⟨24360, by rfl⟩) R48721
theorem R97739 : Reach 97739 := rs (se 1 (by rfl) ⟨73304, by rfl⟩) R146609
theorem R32215 : Reach 32215 := rs (se 1 (by rfl) ⟨24161, by rfl⟩) R48323
theorem R32395 : Reach 32395 := rs (se 1 (by rfl) ⟨24296, by rfl⟩) R48593
theorem R98009 : Reach 98009 := rs (se 2 (by rfl) ⟨36753, by rfl⟩) R73507
theorem R261893 : Reach 261893 := rs (se 4 (by rfl) ⟨24552, by rfl⟩) R49105
theorem R65303 : Reach 65303 := rs (se 1 (by rfl) ⟨48977, by rfl⟩) R97955
theorem R294835 : Reach 294835 := rs (se 1 (by rfl) ⟨221126, by rfl⟩) R442253
theorem R65483 : Reach 65483 := rs (se 1 (by rfl) ⟨49112, by rfl⟩) R98225
theorem R65537 : Reach 65537 := rs (se 2 (by rfl) ⟨24576, by rfl⟩) R49153
theorem R98333 : Reach 98333 := rs (se 3 (by rfl) ⟨18437, by rfl⟩) R36875
theorem R32827 : Reach 32827 := rs (se 1 (by rfl) ⟨24620, by rfl⟩) R49241
theorem R65807 : Reach 65807 := rs (se 1 (by rfl) ⟨49355, by rfl⟩) R98711
theorem R65825 : Reach 65825 := rs (se 2 (by rfl) ⟨24684, by rfl⟩) R49369
theorem R131387 : Reach 131387 := rs (se 1 (by rfl) ⟨98540, by rfl⟩) R197081
theorem R65879 : Reach 65879 := rs (se 1 (by rfl) ⟨49409, by rfl⟩) R98819
theorem R66059 : Reach 66059 := rs (se 1 (by rfl) ⟨49544, by rfl⟩) R99089
theorem R33295 : Reach 33295 := rs (se 1 (by rfl) ⟨24971, by rfl⟩) R49943
theorem R66167 : Reach 66167 := rs (se 1 (by rfl) ⟨49625, by rfl⟩) R99251
theorem R66347 : Reach 66347 := rs (se 1 (by rfl) ⟨49760, by rfl⟩) R99521
theorem R66419 : Reach 66419 := rs (se 1 (by rfl) ⟨49814, by rfl⟩) R99629
theorem R33655 : Reach 33655 := rs (se 1 (by rfl) ⟨25241, by rfl⟩) R50483
theorem R33799 : Reach 33799 := rs (se 1 (by rfl) ⟨25349, by rfl⟩) R50699
theorem R33835 : Reach 33835 := rs (se 1 (by rfl) ⟨25376, by rfl⟩) R50753
theorem R99415 : Reach 99415 := rs (se 1 (by rfl) ⟨74561, by rfl⟩) R149123
theorem R66707 : Reach 66707 := rs (se 1 (by rfl) ⟨50030, by rfl⟩) R100061
theorem R33979 : Reach 33979 := rs (se 1 (by rfl) ⟨25484, by rfl⟩) R50969
theorem R66761 : Reach 66761 := rs (se 2 (by rfl) ⟨25035, by rfl⟩) R50071
theorem R99737 : Reach 99737 := rs (se 2 (by rfl) ⟨37401, by rfl⟩) R74803
theorem R34447 : Reach 34447 := rs (se 1 (by rfl) ⟨25835, by rfl⟩) R51671
theorem R67339 : Reach 67339 := rs (se 1 (by rfl) ⟨50504, by rfl⟩) R101009
theorem R165665 : Reach 165665 := rs (se 2 (by rfl) ⟨62124, by rfl⟩) R124249
theorem R329507 : Reach 329507 := rs (se 1 (by rfl) ⟨247130, by rfl⟩) R494261
theorem R198449 : Reach 198449 := rs (se 2 (by rfl) ⟨74418, by rfl⟩) R148837
theorem R67463 : Reach 67463 := rs (se 1 (by rfl) ⟨50597, by rfl⟩) R101195
theorem R67481 : Reach 67481 := rs (se 2 (by rfl) ⟨25305, by rfl⟩) R50611
theorem R165817 : Reach 165817 := rs (se 2 (by rfl) ⟨62181, by rfl⟩) R124363
theorem R133049 : Reach 133049 := rs (se 2 (by rfl) ⟨49893, by rfl⟩) R99787
theorem R34807 : Reach 34807 := rs (se 1 (by rfl) ⟨26105, by rfl⟩) R52211
theorem R67643 : Reach 67643 := rs (se 1 (by rfl) ⟨50732, by rfl⟩) R101465
theorem R100439 : Reach 100439 := rs (se 1 (by rfl) ⟨75329, by rfl⟩) R150659
theorem R34951 : Reach 34951 := rs (se 1 (by rfl) ⟨26213, by rfl⟩) R52427
theorem R34987 : Reach 34987 := rs (se 1 (by rfl) ⟨26240, by rfl⟩) R52481
theorem R67769 : Reach 67769 := rs (se 2 (by rfl) ⟨25413, by rfl⟩) R50827
theorem R67841 : Reach 67841 := rs (se 2 (by rfl) ⟨25440, by rfl⟩) R50881
theorem R166195 : Reach 166195 := rs (se 1 (by rfl) ⟨124646, by rfl⟩) R249293
theorem R100817 : Reach 100817 := rs (se 2 (by rfl) ⟨37806, by rfl⟩) R75613
theorem R68111 : Reach 68111 := rs (se 1 (by rfl) ⟨51083, by rfl⟩) R102167
theorem R68129 : Reach 68129 := rs (se 2 (by rfl) ⟨25548, by rfl⟩) R51097
theorem R100925 : Reach 100925 := rs (se 3 (by rfl) ⟨18923, by rfl⟩) R37847
theorem R68183 : Reach 68183 := rs (se 1 (by rfl) ⟨51137, by rfl⟩) R102275
theorem R68363 : Reach 68363 := rs (se 1 (by rfl) ⟨51272, by rfl⟩) R102545
theorem R232307 : Reach 232307 := rs (se 1 (by rfl) ⟨174230, by rfl⟩) R348461
theorem R68471 : Reach 68471 := rs (se 1 (by rfl) ⟨51353, by rfl⟩) R102707
theorem R68651 : Reach 68651 := rs (se 1 (by rfl) ⟨51488, by rfl⟩) R102977
theorem R68723 : Reach 68723 := rs (se 1 (by rfl) ⟨51542, by rfl⟩) R103085
theorem R35959 : Reach 35959 := rs (se 1 (by rfl) ⟨26969, by rfl⟩) R53939
theorem R35983 : Reach 35983 := rs (se 1 (by rfl) ⟨26987, by rfl⟩) R53975
theorem R68809 : Reach 68809 := rs (se 2 (by rfl) ⟨25803, by rfl⟩) R51607
theorem R363809 : Reach 363809 := rs (se 2 (by rfl) ⟨136428, by rfl⟩) R272857
theorem R101665 : Reach 101665 := rs (se 2 (by rfl) ⟨38124, by rfl⟩) R76249
theorem R68951 : Reach 68951 := rs (se 1 (by rfl) ⟨51713, by rfl⟩) R103427
theorem R69011 : Reach 69011 := rs (se 1 (by rfl) ⟨51758, by rfl⟩) R103517
theorem R36283 : Reach 36283 := rs (se 1 (by rfl) ⟨27212, by rfl⟩) R54425
theorem R69065 : Reach 69065 := rs (se 2 (by rfl) ⟨25899, by rfl⟩) R51799
theorem R233189 : Reach 233189 := rs (se 4 (by rfl) ⟨21861, by rfl⟩) R43723
theorem R560965 : Reach 560965 := rs (se 4 (by rfl) ⟨52590, by rfl⟩) R105181
theorem R429977 : Reach 429977 := rs (se 2 (by rfl) ⟨161241, by rfl⟩) R322483
theorem R102329 : Reach 102329 := rs (se 2 (by rfl) ⟨38373, by rfl⟩) R76747
theorem R36983 : Reach 36983 := rs (se 1 (by rfl) ⟨27737, by rfl⟩) R55475
theorem R69767 : Reach 69767 := rs (se 1 (by rfl) ⟨52325, by rfl⟩) R104651
theorem R69785 : Reach 69785 := rs (se 2 (by rfl) ⟨26169, by rfl⟩) R52339
theorem R69947 : Reach 69947 := rs (se 1 (by rfl) ⟨52460, by rfl⟩) R104921
theorem R37255 : Reach 37255 := rs (se 1 (by rfl) ⟨27941, by rfl⟩) R55883
theorem R233873 : Reach 233873 := rs (se 2 (by rfl) ⟨87702, by rfl⟩) R175405
theorem R102923 : Reach 102923 := rs (se 1 (by rfl) ⟨77192, by rfl⟩) R154385
theorem R103031 : Reach 103031 := rs (se 1 (by rfl) ⟨77273, by rfl⟩) R154547
theorem R37675 : Reach 37675 := rs (se 1 (by rfl) ⟨28256, by rfl⟩) R56513
theorem R168763 : Reach 168763 := rs (se 1 (by rfl) ⟨126572, by rfl⟩) R253145
theorem R37903 : Reach 37903 := rs (se 1 (by rfl) ⟨28427, by rfl⟩) R56855
theorem R103511 : Reach 103511 := rs (se 1 (by rfl) ⟨77633, by rfl⟩) R155267
theorem R38059 : Reach 38059 := rs (se 1 (by rfl) ⟨28544, by rfl⟩) R57089
theorem R103625 : Reach 103625 := rs (se 2 (by rfl) ⟨38859, by rfl⟩) R77719
theorem R71027 : Reach 71027 := rs (se 1 (by rfl) ⟨53270, by rfl⟩) R106541
theorem R234899 : Reach 234899 := rs (se 1 (by rfl) ⟨176174, by rfl⟩) R352349
theorem R104003 : Reach 104003 := rs (se 1 (by rfl) ⟨78002, by rfl⟩) R156005
theorem R38647 : Reach 38647 := rs (se 1 (by rfl) ⟨28985, by rfl⟩) R57971
theorem R38713 : Reach 38713 := rs (se 2 (by rfl) ⟨14517, by rfl⟩) R29035
theorem R71543 : Reach 71543 := rs (se 1 (by rfl) ⟨53657, by rfl⟩) R107315
theorem R104327 : Reach 104327 := rs (se 1 (by rfl) ⟨78245, by rfl⟩) R156491
theorem R38971 : Reach 38971 := rs (se 1 (by rfl) ⟨29228, by rfl⟩) R58457
theorem R5150789 : Reach 5150789 := rs (se 4 (by rfl) ⟨482886, by rfl⟩) R965773
theorem R39047 : Reach 39047 := rs (se 1 (by rfl) ⟨29285, by rfl⟩) R58571
theorem R39055 : Reach 39055 := rs (se 1 (by rfl) ⟨29291, by rfl⟩) R58583
theorem R170221 : Reach 170221 := rs (se 3 (by rfl) ⟨31916, by rfl⟩) R63833
theorem R104705 : Reach 104705 := rs (se 2 (by rfl) ⟨39264, by rfl⟩) R78529
theorem R39241 : Reach 39241 := rs (se 2 (by rfl) ⟨14715, by rfl⟩) R29431
theorem R72083 : Reach 72083 := rs (se 1 (by rfl) ⟨54062, by rfl⟩) R108125
theorem R203293 : Reach 203293 := rs (se 3 (by rfl) ⟨38117, by rfl⟩) R76235
theorem R72535 : Reach 72535 := rs (se 1 (by rfl) ⟨54401, by rfl⟩) R108803
theorem R39799 : Reach 39799 := rs (se 1 (by rfl) ⟨29849, by rfl⟩) R59699
theorem R138131 : Reach 138131 := rs (se 1 (by rfl) ⟨103598, by rfl⟩) R207197
theorem R105401 : Reach 105401 := rs (se 2 (by rfl) ⟨39525, by rfl⟩) R79051
theorem R171031 : Reach 171031 := rs (se 1 (by rfl) ⟨128273, by rfl⟩) R256547
theorem R72839 : Reach 72839 := rs (se 1 (by rfl) ⟨54629, by rfl⟩) R109259
theorem R72971 : Reach 72971 := rs (se 1 (by rfl) ⟨54728, by rfl⟩) R109457
theorem R73021 : Reach 73021 := rs (se 3 (by rfl) ⟨13691, by rfl⟩) R27383
theorem R40439 : Reach 40439 := rs (se 1 (by rfl) ⟨30329, by rfl⟩) R60659
theorem R40505 : Reach 40505 := rs (se 2 (by rfl) ⟨15189, by rfl⟩) R30379
theorem R40591 : Reach 40591 := rs (se 1 (by rfl) ⟨30443, by rfl⟩) R60887
theorem R40619 : Reach 40619 := rs (se 1 (by rfl) ⟨30464, by rfl⟩) R60929
theorem R73487 : Reach 73487 := rs (se 1 (by rfl) ⟨55115, by rfl⟩) R110231
theorem R302899 : Reach 302899 := rs (se 1 (by rfl) ⟨227174, by rfl⟩) R454349
theorem R40763 : Reach 40763 := rs (se 1 (by rfl) ⟨30572, by rfl⟩) R61145
theorem R40823 : Reach 40823 := rs (se 1 (by rfl) ⟨30617, by rfl⟩) R61235
theorem R40847 : Reach 40847 := rs (se 1 (by rfl) ⟨30635, by rfl⟩) R61271
theorem R73619 : Reach 73619 := rs (se 1 (by rfl) ⟨55214, by rfl⟩) R110429
theorem R40889 : Reach 40889 := rs (se 2 (by rfl) ⟨15333, by rfl⟩) R30667
theorem R40967 : Reach 40967 := rs (se 1 (by rfl) ⟨30725, by rfl⟩) R61451
theorem R41003 : Reach 41003 := rs (se 1 (by rfl) ⟨30752, by rfl⟩) R61505
theorem R41033 : Reach 41033 := rs (se 2 (by rfl) ⟨15387, by rfl⟩) R30775
theorem R172205 : Reach 172205 := rs (se 3 (by rfl) ⟨32288, by rfl⟩) R64577
theorem R41147 : Reach 41147 := rs (se 1 (by rfl) ⟨30860, by rfl⟩) R61721
theorem R41207 : Reach 41207 := rs (se 1 (by rfl) ⟨30905, by rfl⟩) R61811
theorem R41231 : Reach 41231 := rs (se 1 (by rfl) ⟨30923, by rfl⟩) R61847
theorem R41273 : Reach 41273 := rs (se 2 (by rfl) ⟨15477, by rfl⟩) R30955
theorem R74119 : Reach 74119 := rs (se 1 (by rfl) ⟨55589, by rfl⟩) R111179
theorem R41351 : Reach 41351 := rs (se 1 (by rfl) ⟨31013, by rfl⟩) R62027
theorem R41387 : Reach 41387 := rs (se 1 (by rfl) ⟨31040, by rfl⟩) R62081
theorem R41401 : Reach 41401 := rs (se 2 (by rfl) ⟨15525, by rfl⟩) R31051
theorem R303545 : Reach 303545 := rs (se 2 (by rfl) ⟨113829, by rfl⟩) R227659
theorem R41417 : Reach 41417 := rs (se 2 (by rfl) ⟨15531, by rfl⟩) R31063
theorem R139805 : Reach 139805 := rs (se 3 (by rfl) ⟨26213, by rfl⟩) R52427
theorem R41531 : Reach 41531 := rs (se 1 (by rfl) ⟨31148, by rfl⟩) R62297
theorem R41591 : Reach 41591 := rs (se 1 (by rfl) ⟨31193, by rfl⟩) R62387
theorem R41615 : Reach 41615 := rs (se 1 (by rfl) ⟨31211, by rfl⟩) R62423
theorem R41657 : Reach 41657 := rs (se 2 (by rfl) ⟨15621, by rfl⟩) R31243
theorem R41735 : Reach 41735 := rs (se 1 (by rfl) ⟨31301, by rfl⟩) R62603
theorem R533263 : Reach 533263 := rs (se 1 (by rfl) ⟨399947, by rfl⟩) R799895
theorem R41771 : Reach 41771 := rs (se 1 (by rfl) ⟨31328, by rfl⟩) R62657
theorem R41801 : Reach 41801 := rs (se 2 (by rfl) ⟨15675, by rfl⟩) R31351
theorem R41915 : Reach 41915 := rs (se 1 (by rfl) ⟨31436, by rfl⟩) R62873
theorem R41975 : Reach 41975 := rs (se 1 (by rfl) ⟨31481, by rfl⟩) R62963
theorem R74753 : Reach 74753 := rs (se 2 (by rfl) ⟨28032, by rfl⟩) R56065
theorem R140291 : Reach 140291 := rs (se 1 (by rfl) ⟨105218, by rfl⟩) R210437
theorem R500741 : Reach 500741 := rs (se 4 (by rfl) ⟨46944, by rfl⟩) R93889
theorem R41999 : Reach 41999 := rs (se 1 (by rfl) ⟨31499, by rfl⟩) R62999
theorem R42041 : Reach 42041 := rs (se 2 (by rfl) ⟨15765, by rfl⟩) R31531
theorem R42119 : Reach 42119 := rs (se 1 (by rfl) ⟨31589, by rfl⟩) R63179
theorem R42155 : Reach 42155 := rs (se 1 (by rfl) ⟨31616, by rfl⟩) R63233
theorem R42185 : Reach 42185 := rs (se 2 (by rfl) ⟨15819, by rfl⟩) R31639
theorem R42299 : Reach 42299 := rs (se 1 (by rfl) ⟨31724, by rfl⟩) R63449
theorem R42359 : Reach 42359 := rs (se 1 (by rfl) ⟨31769, by rfl⟩) R63539
theorem R75127 : Reach 75127 := rs (se 1 (by rfl) ⟨56345, by rfl⟩) R112691
theorem R42383 : Reach 42383 := rs (se 1 (by rfl) ⟨31787, by rfl⟩) R63575
theorem R42425 : Reach 42425 := rs (se 2 (by rfl) ⟨15909, by rfl⟩) R31819
theorem R42503 : Reach 42503 := rs (se 1 (by rfl) ⟨31877, by rfl⟩) R63755
theorem R75293 : Reach 75293 := rs (se 3 (by rfl) ⟨14117, by rfl⟩) R28235
theorem R42539 : Reach 42539 := rs (se 1 (by rfl) ⟨31904, by rfl⟩) R63809
theorem R42569 : Reach 42569 := rs (se 2 (by rfl) ⟨15963, by rfl⟩) R31927
theorem R42683 : Reach 42683 := rs (se 1 (by rfl) ⟨32012, by rfl⟩) R64025
theorem R42743 : Reach 42743 := rs (se 1 (by rfl) ⟨32057, by rfl⟩) R64115
theorem R42767 : Reach 42767 := rs (se 1 (by rfl) ⟨32075, by rfl⟩) R64151
theorem R75563 : Reach 75563 := rs (se 1 (by rfl) ⟨56672, by rfl⟩) R113345
theorem R42809 : Reach 42809 := rs (se 2 (by rfl) ⟨16053, by rfl⟩) R32107
theorem R42887 : Reach 42887 := rs (se 1 (by rfl) ⟨32165, by rfl⟩) R64331
theorem R42953 : Reach 42953 := rs (se 2 (by rfl) ⟨16107, by rfl⟩) R32215
theorem R43067 : Reach 43067 := rs (se 1 (by rfl) ⟨32300, by rfl⟩) R64601
theorem R43127 : Reach 43127 := rs (se 1 (by rfl) ⟨32345, by rfl⟩) R64691
theorem R43193 : Reach 43193 := rs (se 2 (by rfl) ⟨16197, by rfl⟩) R32395
theorem R43307 : Reach 43307 := rs (se 1 (by rfl) ⟨32480, by rfl⟩) R64961
theorem R108985 : Reach 108985 := rs (se 2 (by rfl) ⟨40869, by rfl⟩) R81739
theorem R174595 : Reach 174595 := rs (se 1 (by rfl) ⟨130946, by rfl⟩) R261893
theorem R43535 : Reach 43535 := rs (se 1 (by rfl) ⟨32651, by rfl⟩) R65303
theorem R600641 : Reach 600641 := rs (se 2 (by rfl) ⟨225240, by rfl⟩) R450481
theorem R141911 : Reach 141911 := rs (se 1 (by rfl) ⟨106433, by rfl⟩) R212867
theorem R76403 : Reach 76403 := rs (se 1 (by rfl) ⟨57302, by rfl⟩) R114605
theorem R76423 : Reach 76423 := rs (se 1 (by rfl) ⟨57317, by rfl⟩) R114635
theorem R43655 : Reach 43655 := rs (se 1 (by rfl) ⟨32741, by rfl⟩) R65483
theorem R666305 : Reach 666305 := rs (se 2 (by rfl) ⟨249864, by rfl⟩) R499729
theorem R43721 : Reach 43721 := rs (se 2 (by rfl) ⟨16395, by rfl⟩) R32791
theorem R43835 : Reach 43835 := rs (se 1 (by rfl) ⟨32876, by rfl⟩) R65753
theorem R43895 : Reach 43895 := rs (se 1 (by rfl) ⟨32921, by rfl⟩) R65843
theorem R76697 : Reach 76697 := rs (se 2 (by rfl) ⟨28761, by rfl⟩) R57523
theorem R43961 : Reach 43961 := rs (se 2 (by rfl) ⟨16485, by rfl⟩) R32971
theorem R44075 : Reach 44075 := rs (se 1 (by rfl) ⟨33056, by rfl⟩) R66113
theorem R76859 : Reach 76859 := rs (se 1 (by rfl) ⟨57644, by rfl⟩) R115289
theorem R142397 : Reach 142397 := rs (se 3 (by rfl) ⟨26699, by rfl⟩) R53399
theorem R44303 : Reach 44303 := rs (se 1 (by rfl) ⟨33227, by rfl⟩) R66455
theorem R77071 : Reach 77071 := rs (se 1 (by rfl) ⟨57803, by rfl⟩) R115607
theorem R44423 : Reach 44423 := rs (se 1 (by rfl) ⟨33317, by rfl⟩) R66635
theorem R44489 : Reach 44489 := rs (se 2 (by rfl) ⟨16683, by rfl⟩) R33367
theorem R77345 : Reach 77345 := rs (se 2 (by rfl) ⟨29004, by rfl⟩) R58009
theorem R44603 : Reach 44603 := rs (se 1 (by rfl) ⟨33452, by rfl⟩) R66905
theorem R44663 : Reach 44663 := rs (se 1 (by rfl) ⟨33497, by rfl⟩) R66995
theorem R44729 : Reach 44729 := rs (se 2 (by rfl) ⟨16773, by rfl⟩) R33547
theorem R339713 : Reach 339713 := rs (se 2 (by rfl) ⟨127392, by rfl⟩) R254785
theorem R44843 : Reach 44843 := rs (se 1 (by rfl) ⟨33632, by rfl⟩) R67265
theorem R110483 : Reach 110483 := rs (se 1 (by rfl) ⟨82862, by rfl⟩) R165725
theorem R77753 : Reach 77753 := rs (se 2 (by rfl) ⟨29157, by rfl⟩) R58315
theorem R45071 : Reach 45071 := rs (se 1 (by rfl) ⟨33803, by rfl⟩) R67607
theorem R77867 : Reach 77867 := rs (se 1 (by rfl) ⟨58400, by rfl⟩) R116801
theorem R45191 : Reach 45191 := rs (se 1 (by rfl) ⟨33893, by rfl⟩) R67787
theorem R45257 : Reach 45257 := rs (se 2 (by rfl) ⟨16971, by rfl⟩) R33943
theorem R45371 : Reach 45371 := rs (se 1 (by rfl) ⟨34028, by rfl⟩) R68057
theorem R45431 : Reach 45431 := rs (se 1 (by rfl) ⟨34073, by rfl⟩) R68147
theorem R536977 : Reach 536977 := rs (se 2 (by rfl) ⟨201366, by rfl⟩) R402733
theorem R45497 : Reach 45497 := rs (se 2 (by rfl) ⟨17061, by rfl⟩) R34123
theorem R143819 : Reach 143819 := rs (se 1 (by rfl) ⟨107864, by rfl⟩) R215729
theorem R78347 : Reach 78347 := rs (se 1 (by rfl) ⟨58760, by rfl⟩) R117521
theorem R45611 : Reach 45611 := rs (se 1 (by rfl) ⟨34208, by rfl⟩) R68417
theorem R45839 : Reach 45839 := rs (se 1 (by rfl) ⟨34379, by rfl⟩) R68759
theorem R144179 : Reach 144179 := rs (se 1 (by rfl) ⟨108134, by rfl⟩) R216269
theorem R45883 : Reach 45883 := rs (se 1 (by rfl) ⟨34412, by rfl⟩) R68825
theorem R177011 : Reach 177011 := rs (se 1 (by rfl) ⟨132758, by rfl⟩) R265517
theorem R45959 : Reach 45959 := rs (se 1 (by rfl) ⟨34469, by rfl⟩) R68939
theorem R144281 : Reach 144281 := rs (se 2 (by rfl) ⟨54105, by rfl⟩) R108211
theorem R46025 : Reach 46025 := rs (se 2 (by rfl) ⟨17259, by rfl⟩) R34519
theorem R78907 : Reach 78907 := rs (se 1 (by rfl) ⟨59180, by rfl⟩) R118361
theorem R46139 : Reach 46139 := rs (se 1 (by rfl) ⟨34604, by rfl⟩) R69209
theorem R144503 : Reach 144503 := rs (se 1 (by rfl) ⟨108377, by rfl⟩) R216755
theorem R46199 : Reach 46199 := rs (se 1 (by rfl) ⟨34649, by rfl⟩) R69299
theorem R78995 : Reach 78995 := rs (se 1 (by rfl) ⟨59246, by rfl⟩) R118493
theorem R46265 : Reach 46265 := rs (se 2 (by rfl) ⟨17349, by rfl⟩) R34699
theorem R177353 : Reach 177353 := rs (se 2 (by rfl) ⟨66507, by rfl⟩) R133015
theorem R111887 : Reach 111887 := rs (se 1 (by rfl) ⟨83915, by rfl⟩) R167831
theorem R46379 : Reach 46379 := rs (se 1 (by rfl) ⟨34784, by rfl⟩) R69569
theorem R1291697 : Reach 1291697 := rs (se 2 (by rfl) ⟨484386, by rfl⟩) R968773
theorem R46607 : Reach 46607 := rs (se 1 (by rfl) ⟨34955, by rfl⟩) R69911
theorem R79393 : Reach 79393 := rs (se 2 (by rfl) ⟨29772, by rfl⟩) R59545
theorem R46777 : Reach 46777 := rs (se 2 (by rfl) ⟨17541, by rfl⟩) R35083
theorem R46793 : Reach 46793 := rs (se 2 (by rfl) ⟨17547, by rfl⟩) R35095
theorem R145297 : Reach 145297 := rs (se 2 (by rfl) ⟨54486, by rfl⟩) R108973
theorem R145475 : Reach 145475 := rs (se 1 (by rfl) ⟨109106, by rfl⟩) R218213
theorem R211031 : Reach 211031 := rs (se 1 (by rfl) ⟨158273, by rfl⟩) R316547
theorem R145637 : Reach 145637 := rs (se 4 (by rfl) ⟨13653, by rfl⟩) R27307
theorem R47479 : Reach 47479 := rs (se 1 (by rfl) ⟨35609, by rfl⟩) R71219
theorem R145799 : Reach 145799 := rs (se 1 (by rfl) ⟨109349, by rfl⟩) R218699
theorem R80281 : Reach 80281 := rs (se 2 (by rfl) ⟨30105, by rfl⟩) R60211
theorem R211409 : Reach 211409 := rs (se 2 (by rfl) ⟨79278, by rfl⟩) R158557
theorem R113105 : Reach 113105 := rs (se 2 (by rfl) ⟨42414, by rfl⟩) R84829
theorem R47675 : Reach 47675 := rs (se 1 (by rfl) ⟨35756, by rfl⟩) R71513
theorem R342629 : Reach 342629 := rs (se 4 (by rfl) ⟨32121, by rfl⟩) R64243
theorem R80669 : Reach 80669 := rs (se 3 (by rfl) ⟨15125, by rfl⟩) R30251
theorem R48073 : Reach 48073 := rs (se 2 (by rfl) ⟨18027, by rfl⟩) R36055
theorem R113707 : Reach 113707 := rs (se 1 (by rfl) ⟨85280, by rfl⟩) R170561
theorem R245213 : Reach 245213 := rs (se 3 (by rfl) ⟨45977, by rfl⟩) R91955
theorem R48775 : Reach 48775 := rs (se 1 (by rfl) ⟨36581, by rfl⟩) R73163
theorem R344087 : Reach 344087 := rs (se 1 (by rfl) ⟨258065, by rfl⟩) R516131
theorem R213229 : Reach 213229 := rs (se 3 (by rfl) ⟨39980, by rfl⟩) R79961
theorem R49423 : Reach 49423 := rs (se 1 (by rfl) ⟨37067, by rfl⟩) R74135
theorem R115091 : Reach 115091 := rs (se 1 (by rfl) ⟨86318, by rfl⟩) R172637
theorem R49963 : Reach 49963 := rs (se 1 (by rfl) ⟨37472, by rfl⟩) R74945
theorem R50105 : Reach 50105 := rs (se 2 (by rfl) ⟨18789, by rfl⟩) R37579
theorem R83243 : Reach 83243 := rs (se 1 (by rfl) ⟨62432, by rfl⟩) R124865
theorem R181763 : Reach 181763 := rs (se 1 (by rfl) ⟨136322, by rfl⟩) R272645
theorem R542285 : Reach 542285 := rs (se 3 (by rfl) ⟨101678, by rfl⟩) R203357
theorem R247373 : Reach 247373 := rs (se 3 (by rfl) ⟨46382, by rfl⟩) R92765
theorem R50807 : Reach 50807 := rs (se 1 (by rfl) ⟨38105, by rfl⟩) R76211
theorem R214721 : Reach 214721 := rs (se 2 (by rfl) ⟨80520, by rfl⟩) R161041
theorem R149363 : Reach 149363 := rs (se 1 (by rfl) ⟨112022, by rfl⟩) R224045
theorem R116747 : Reach 116747 := rs (se 1 (by rfl) ⟨87560, by rfl⟩) R175121
theorem R51259 : Reach 51259 := rs (se 1 (by rfl) ⟨38444, by rfl⟩) R76889
theorem R51347 : Reach 51347 := rs (se 1 (by rfl) ⟨38510, by rfl⟩) R77021
theorem R1001645 : Reach 1001645 := rs (se 3 (by rfl) ⟨187808, by rfl⟩) R375617
theorem R51401 : Reach 51401 := rs (se 2 (by rfl) ⟨19275, by rfl⟩) R38551
theorem R149849 : Reach 149849 := rs (se 2 (by rfl) ⟨56193, by rfl⟩) R112387
theorem R51745 : Reach 51745 := rs (se 2 (by rfl) ⟨19404, by rfl⟩) R38809
theorem R52103 : Reach 52103 := rs (se 1 (by rfl) ⟨39077, by rfl⟩) R78155
theorem R84883 : Reach 84883 := rs (se 1 (by rfl) ⟨63662, by rfl⟩) R127325
theorem R52267 : Reach 52267 := rs (se 1 (by rfl) ⟨39200, by rfl⟩) R78401
theorem R150821 : Reach 150821 := rs (se 4 (by rfl) ⟨14139, by rfl⟩) R28279
theorem R150835 : Reach 150835 := rs (se 1 (by rfl) ⟨113126, by rfl⟩) R226253
theorem R281987 : Reach 281987 := rs (se 1 (by rfl) ⟨211490, by rfl⟩) R422981
theorem R118201 : Reach 118201 := rs (se 2 (by rfl) ⟨44325, by rfl⟩) R88651
theorem R347597 : Reach 347597 := rs (se 3 (by rfl) ⟨65174, by rfl⟩) R130349
theorem R52883 : Reach 52883 := rs (se 1 (by rfl) ⟨39662, by rfl⟩) R79325
theorem R282305 : Reach 282305 := rs (se 2 (by rfl) ⟨105864, by rfl⟩) R211729
theorem R282329 : Reach 282329 := rs (se 2 (by rfl) ⟨105873, by rfl⟩) R211747
theorem R118543 : Reach 118543 := rs (se 1 (by rfl) ⟨88907, by rfl⟩) R177815
theorem R53111 : Reach 53111 := rs (se 1 (by rfl) ⟨39833, by rfl⟩) R79667
theorem R217403 : Reach 217403 := rs (se 1 (by rfl) ⟨163052, by rfl⟩) R326105
theorem R151955 : Reach 151955 := rs (se 1 (by rfl) ⟨113966, by rfl⟩) R227933
theorem R250411 : Reach 250411 := rs (se 1 (by rfl) ⟨187808, by rfl⟩) R375617
theorem R86615 : Reach 86615 := rs (se 1 (by rfl) ⟨64961, by rfl⟩) R129923
theorem R119875 : Reach 119875 := rs (se 1 (by rfl) ⟨89906, by rfl⟩) R179813
theorem R120217 : Reach 120217 := rs (se 2 (by rfl) ⟨45081, by rfl⟩) R90163
theorem R54827 : Reach 54827 := rs (se 1 (by rfl) ⟨41120, by rfl⟩) R82241
theorem R120521 : Reach 120521 := rs (se 2 (by rfl) ⟨45195, by rfl⟩) R90391
theorem R55055 : Reach 55055 := rs (se 1 (by rfl) ⟨41291, by rfl⟩) R82583
theorem R317843 : Reach 317843 := rs (se 1 (by rfl) ⟨238382, by rfl⟩) R476765
theorem R88847 : Reach 88847 := rs (se 1 (by rfl) ⟨66635, by rfl⟩) R133271
theorem R351013 : Reach 351013 := rs (se 4 (by rfl) ⟨32907, by rfl⟩) R65815
theorem R154457 : Reach 154457 := rs (se 2 (by rfl) ⟨57921, by rfl⟩) R115843
theorem R56467 : Reach 56467 := rs (se 1 (by rfl) ⟨42350, by rfl⟩) R84701
theorem R351469 : Reach 351469 := rs (se 3 (by rfl) ⟨65900, by rfl⟩) R131801
theorem R56695 : Reach 56695 := rs (se 1 (by rfl) ⟨42521, by rfl⟩) R85043
theorem R155015 : Reach 155015 := rs (se 1 (by rfl) ⟨116261, by rfl⟩) R232523
theorem R155033 : Reach 155033 := rs (se 2 (by rfl) ⟨58137, by rfl⟩) R116275
theorem R155159 : Reach 155159 := rs (se 1 (by rfl) ⟨116369, by rfl⟩) R232739
theorem R89915 : Reach 89915 := rs (se 1 (by rfl) ⟨67436, by rfl⟩) R134873
theorem R188477 : Reach 188477 := rs (se 3 (by rfl) ⟨35339, by rfl⟩) R70679
theorem R778481 : Reach 778481 := rs (se 2 (by rfl) ⟨291930, by rfl⟩) R583861
theorem R352835 : Reach 352835 := rs (se 1 (by rfl) ⟨264626, by rfl⟩) R529253
theorem R58259 : Reach 58259 := rs (se 1 (by rfl) ⟨43694, by rfl⟩) R87389
theorem R58313 : Reach 58313 := rs (se 2 (by rfl) ⟨21867, by rfl⟩) R43735
theorem R58411 : Reach 58411 := rs (se 1 (by rfl) ⟨43808, by rfl⟩) R87617
theorem R58639 : Reach 58639 := rs (se 1 (by rfl) ⟨43979, by rfl⟩) R87959
theorem R58657 : Reach 58657 := rs (se 2 (by rfl) ⟨21996, by rfl⟩) R43993
theorem R91691 : Reach 91691 := rs (se 1 (by rfl) ⟨68768, by rfl⟩) R137537
theorem R59015 : Reach 59015 := rs (se 1 (by rfl) ⟨44261, by rfl⟩) R88523
theorem R157625 : Reach 157625 := rs (se 2 (by rfl) ⟨59109, by rfl⟩) R118219
theorem R157643 : Reach 157643 := rs (se 1 (by rfl) ⟨118232, by rfl⟩) R236465
theorem R190475 : Reach 190475 := rs (se 1 (by rfl) ⟨142856, by rfl⟩) R285713
theorem R322001 : Reach 322001 := rs (se 2 (by rfl) ⟨120750, by rfl⟩) R241501
theorem R27143 : Reach 27143 := rs (se 1 (by rfl) ⟨20357, by rfl⟩) R40715
theorem R27151 : Reach 27151 := rs (se 1 (by rfl) ⟨20363, by rfl⟩) R40727
theorem R27195 : Reach 27195 := rs (se 1 (by rfl) ⟨20396, by rfl⟩) R40793
theorem R27271 : Reach 27271 := rs (se 1 (by rfl) ⟨20453, by rfl⟩) R40907
theorem R27279 : Reach 27279 := rs (se 1 (by rfl) ⟨20459, by rfl⟩) R40919
theorem R158381 : Reach 158381 := rs (se 3 (by rfl) ⟨29696, by rfl⟩) R59393
theorem R27323 : Reach 27323 := rs (se 1 (by rfl) ⟨20492, by rfl⟩) R40985
theorem R256769 : Reach 256769 := rs (se 2 (by rfl) ⟨96288, by rfl⟩) R192577
theorem R27399 : Reach 27399 := rs (se 1 (by rfl) ⟨20549, by rfl⟩) R41099
theorem R27407 : Reach 27407 := rs (se 1 (by rfl) ⟨20555, by rfl⟩) R41111
theorem R60203 : Reach 60203 := rs (se 1 (by rfl) ⟨45152, by rfl⟩) R90305
theorem R27451 : Reach 27451 := rs (se 1 (by rfl) ⟨20588, by rfl⟩) R41177
theorem R92987 : Reach 92987 := rs (se 1 (by rfl) ⟨69740, by rfl⟩) R139481
theorem R486233 : Reach 486233 := rs (se 2 (by rfl) ⟨182337, by rfl⟩) R364675
theorem R27527 : Reach 27527 := rs (se 1 (by rfl) ⟨20645, by rfl⟩) R41291
theorem R27535 : Reach 27535 := rs (se 1 (by rfl) ⟨20651, by rfl⟩) R41303
theorem R224153 : Reach 224153 := rs (se 2 (by rfl) ⟨84057, by rfl⟩) R168115
theorem R27579 : Reach 27579 := rs (se 1 (by rfl) ⟨20684, by rfl⟩) R41369
theorem R27655 : Reach 27655 := rs (se 1 (by rfl) ⟨20741, by rfl⟩) R41483
theorem R27663 : Reach 27663 := rs (se 1 (by rfl) ⟨20747, by rfl⟩) R41495
theorem R27707 : Reach 27707 := rs (se 1 (by rfl) ⟨20780, by rfl⟩) R41561
theorem R27783 : Reach 27783 := rs (se 1 (by rfl) ⟨20837, by rfl⟩) R41675
theorem R27791 : Reach 27791 := rs (se 1 (by rfl) ⟨20843, by rfl⟩) R41687
theorem R27835 : Reach 27835 := rs (se 1 (by rfl) ⟨20876, by rfl⟩) R41753
theorem R27911 : Reach 27911 := rs (se 1 (by rfl) ⟨20933, by rfl⟩) R41867
theorem R27919 : Reach 27919 := rs (se 1 (by rfl) ⟨20939, by rfl⟩) R41879
theorem R93473 : Reach 93473 := rs (se 2 (by rfl) ⟨35052, by rfl⟩) R70105
theorem R27963 : Reach 27963 := rs (se 1 (by rfl) ⟨20972, by rfl⟩) R41945
theorem R1371491 : Reach 1371491 := rs (se 1 (by rfl) ⟨1028618, by rfl⟩) R2057237
theorem R28039 : Reach 28039 := rs (se 1 (by rfl) ⟨21029, by rfl⟩) R42059
theorem R28047 : Reach 28047 := rs (se 1 (by rfl) ⟨21035, by rfl⟩) R42071
theorem R28091 : Reach 28091 := rs (se 1 (by rfl) ⟨21068, by rfl⟩) R42137
theorem R28167 : Reach 28167 := rs (se 1 (by rfl) ⟨21125, by rfl⟩) R42251
theorem R28175 : Reach 28175 := rs (se 1 (by rfl) ⟨21131, by rfl⟩) R42263
theorem R28219 : Reach 28219 := rs (se 1 (by rfl) ⟨21164, by rfl⟩) R42329
theorem R28295 : Reach 28295 := rs (se 1 (by rfl) ⟨21221, by rfl⟩) R42443
theorem R28303 : Reach 28303 := rs (se 1 (by rfl) ⟨21227, by rfl⟩) R42455
theorem R28347 : Reach 28347 := rs (se 1 (by rfl) ⟨21260, by rfl⟩) R42521
theorem R28423 : Reach 28423 := rs (se 1 (by rfl) ⟨21317, by rfl⟩) R42635
theorem R61199 : Reach 61199 := rs (se 1 (by rfl) ⟨45899, by rfl⟩) R91799
theorem R28431 : Reach 28431 := rs (se 1 (by rfl) ⟨21323, by rfl⟩) R42647
theorem R61217 : Reach 61217 := rs (se 2 (by rfl) ⟨22956, by rfl⟩) R45913
theorem R28475 : Reach 28475 := rs (se 1 (by rfl) ⟨21356, by rfl⟩) R42713
theorem R94067 : Reach 94067 := rs (se 1 (by rfl) ⟨70550, by rfl⟩) R141101
theorem R28551 : Reach 28551 := rs (se 1 (by rfl) ⟨21413, by rfl⟩) R42827
theorem R28559 : Reach 28559 := rs (se 1 (by rfl) ⟨21419, by rfl⟩) R42839
theorem R28603 : Reach 28603 := rs (se 1 (by rfl) ⟨21452, by rfl⟩) R42905
theorem R225227 : Reach 225227 := rs (se 1 (by rfl) ⟨168920, by rfl⟩) R337841
theorem R28679 : Reach 28679 := rs (se 1 (by rfl) ⟨21509, by rfl⟩) R43019
theorem R28687 : Reach 28687 := rs (se 1 (by rfl) ⟨21515, by rfl⟩) R43031
theorem R28731 : Reach 28731 := rs (se 1 (by rfl) ⟨21548, by rfl⟩) R43097
theorem R127037 : Reach 127037 := rs (se 3 (by rfl) ⟨23819, by rfl⟩) R47639
theorem R61559 : Reach 61559 := rs (se 1 (by rfl) ⟨46169, by rfl⟩) R92339
theorem R28807 : Reach 28807 := rs (se 1 (by rfl) ⟨21605, by rfl⟩) R43211
theorem R28815 : Reach 28815 := rs (se 1 (by rfl) ⟨21611, by rfl⟩) R43223
theorem R28859 : Reach 28859 := rs (se 1 (by rfl) ⟨21644, by rfl⟩) R43289
theorem R28935 : Reach 28935 := rs (se 1 (by rfl) ⟨21701, by rfl⟩) R43403
theorem R160015 : Reach 160015 := rs (se 1 (by rfl) ⟨120011, by rfl⟩) R240023
theorem R28943 : Reach 28943 := rs (se 1 (by rfl) ⟨21707, by rfl⟩) R43415
theorem R61739 : Reach 61739 := rs (se 1 (by rfl) ⟨46304, by rfl⟩) R92609
theorem R28987 : Reach 28987 := rs (se 1 (by rfl) ⟨21740, by rfl⟩) R43481
theorem R127291 : Reach 127291 := rs (se 1 (by rfl) ⟨95468, by rfl⟩) R190937
theorem R29063 : Reach 29063 := rs (se 1 (by rfl) ⟨21797, by rfl⟩) R43595
theorem R29071 : Reach 29071 := rs (se 1 (by rfl) ⟨21803, by rfl⟩) R43607
theorem R29115 : Reach 29115 := rs (se 1 (by rfl) ⟨21836, by rfl⟩) R43673
theorem R29191 : Reach 29191 := rs (se 1 (by rfl) ⟨21893, by rfl⟩) R43787
theorem R29199 : Reach 29199 := rs (se 1 (by rfl) ⟨21899, by rfl⟩) R43799
theorem R29243 : Reach 29243 := rs (se 1 (by rfl) ⟨21932, by rfl⟩) R43865
theorem R127555 : Reach 127555 := rs (se 1 (by rfl) ⟨95666, by rfl⟩) R191333
theorem R29319 : Reach 29319 := rs (se 1 (by rfl) ⟨21989, by rfl⟩) R43979
theorem R29327 : Reach 29327 := rs (se 1 (by rfl) ⟨21995, by rfl⟩) R43991
theorem R62099 : Reach 62099 := rs (se 1 (by rfl) ⟨46574, by rfl⟩) R93149
theorem R29371 : Reach 29371 := rs (se 1 (by rfl) ⟨22028, by rfl⟩) R44057
theorem R62153 : Reach 62153 := rs (se 2 (by rfl) ⟨23307, by rfl⟩) R46615
theorem R29447 : Reach 29447 := rs (se 1 (by rfl) ⟨22085, by rfl⟩) R44171
theorem R29455 : Reach 29455 := rs (se 1 (by rfl) ⟨22091, by rfl⟩) R44183
theorem R29499 : Reach 29499 := rs (se 1 (by rfl) ⟨22124, by rfl⟩) R44249
theorem R29575 : Reach 29575 := rs (se 1 (by rfl) ⟨22181, by rfl⟩) R44363
theorem R29583 : Reach 29583 := rs (se 1 (by rfl) ⟨22187, by rfl⟩) R44375
theorem R29627 : Reach 29627 := rs (se 1 (by rfl) ⟨22220, by rfl⟩) R44441
theorem R29703 : Reach 29703 := rs (se 1 (by rfl) ⟨22277, by rfl⟩) R44555
theorem R29711 : Reach 29711 := rs (se 1 (by rfl) ⟨22283, by rfl⟩) R44567
theorem R291863 : Reach 291863 := rs (se 1 (by rfl) ⟨218897, by rfl⟩) R437795
theorem R62507 : Reach 62507 := rs (se 1 (by rfl) ⟨46880, by rfl⟩) R93761
theorem R29755 : Reach 29755 := rs (se 1 (by rfl) ⟨22316, by rfl⟩) R44633
theorem R259159 : Reach 259159 := rs (se 1 (by rfl) ⟨194369, by rfl⟩) R388739
theorem R390277 : Reach 390277 := rs (se 4 (by rfl) ⟨36588, by rfl⟩) R73177
theorem R29831 : Reach 29831 := rs (se 1 (by rfl) ⟨22373, by rfl⟩) R44747
theorem R29839 : Reach 29839 := rs (se 1 (by rfl) ⟨22379, by rfl⟩) R44759
theorem R29883 : Reach 29883 := rs (se 1 (by rfl) ⟨22412, by rfl⟩) R44825
theorem R29959 : Reach 29959 := rs (se 1 (by rfl) ⟨22469, by rfl⟩) R44939
theorem R29967 : Reach 29967 := rs (se 1 (by rfl) ⟨22475, by rfl⟩) R44951
theorem R30011 : Reach 30011 := rs (se 1 (by rfl) ⟨22508, by rfl⟩) R45017
theorem R62855 : Reach 62855 := rs (se 1 (by rfl) ⟨47141, by rfl⟩) R94283
theorem R30087 : Reach 30087 := rs (se 1 (by rfl) ⟨22565, by rfl⟩) R45131
theorem R30095 : Reach 30095 := rs (se 1 (by rfl) ⟨22571, by rfl⟩) R45143
theorem R30139 : Reach 30139 := rs (se 1 (by rfl) ⟨22604, by rfl⟩) R45209
theorem R30215 : Reach 30215 := rs (se 1 (by rfl) ⟨22661, by rfl⟩) R45323
theorem R161291 : Reach 161291 := rs (se 1 (by rfl) ⟨120968, by rfl⟩) R241937
theorem R30223 : Reach 30223 := rs (se 1 (by rfl) ⟨22667, by rfl⟩) R45335
theorem R63035 : Reach 63035 := rs (se 1 (by rfl) ⟨47276, by rfl⟩) R94553
theorem R30267 : Reach 30267 := rs (se 1 (by rfl) ⟨22700, by rfl⟩) R45401
theorem R30343 : Reach 30343 := rs (se 1 (by rfl) ⟨22757, by rfl⟩) R45515
theorem R30351 : Reach 30351 := rs (se 1 (by rfl) ⟨22763, by rfl⟩) R45527
theorem R63161 : Reach 63161 := rs (se 2 (by rfl) ⟨23685, by rfl⟩) R47371
theorem R30395 : Reach 30395 := rs (se 1 (by rfl) ⟨22796, by rfl⟩) R45593
theorem R161473 : Reach 161473 := rs (se 2 (by rfl) ⟨60552, by rfl⟩) R121105
theorem R30471 : Reach 30471 := rs (se 1 (by rfl) ⟨22853, by rfl⟩) R45707
theorem R30479 : Reach 30479 := rs (se 1 (by rfl) ⟨22859, by rfl⟩) R45719
theorem R30523 : Reach 30523 := rs (se 1 (by rfl) ⟨22892, by rfl⟩) R45785
theorem R30599 : Reach 30599 := rs (se 1 (by rfl) ⟨22949, by rfl⟩) R45899
theorem R30607 : Reach 30607 := rs (se 1 (by rfl) ⟨22955, by rfl⟩) R45911
theorem R30651 : Reach 30651 := rs (se 1 (by rfl) ⟨22988, by rfl⟩) R45977
theorem R325579 : Reach 325579 := rs (se 1 (by rfl) ⟨244184, by rfl⟩) R488369
theorem R30727 : Reach 30727 := rs (se 1 (by rfl) ⟨23045, by rfl⟩) R46091
theorem R63503 : Reach 63503 := rs (se 1 (by rfl) ⟨47627, by rfl⟩) R95255
theorem R30735 : Reach 30735 := rs (se 1 (by rfl) ⟨23051, by rfl⟩) R46103
theorem R63521 : Reach 63521 := rs (se 2 (by rfl) ⟨23820, by rfl⟩) R47641
theorem R63547 : Reach 63547 := rs (se 1 (by rfl) ⟨47660, by rfl⟩) R95321
theorem R30779 : Reach 30779 := rs (se 1 (by rfl) ⟨23084, by rfl⟩) R46169
theorem R63623 : Reach 63623 := rs (se 1 (by rfl) ⟨47717, by rfl⟩) R95435
theorem R30855 : Reach 30855 := rs (se 1 (by rfl) ⟨23141, by rfl⟩) R46283
theorem R30863 : Reach 30863 := rs (se 1 (by rfl) ⟨23147, by rfl⟩) R46295
theorem R30907 : Reach 30907 := rs (se 1 (by rfl) ⟨23180, by rfl⟩) R46361
theorem R30983 : Reach 30983 := rs (se 1 (by rfl) ⟨23237, by rfl⟩) R46475
theorem R30991 : Reach 30991 := rs (se 1 (by rfl) ⟨23243, by rfl⟩) R46487
theorem R31035 : Reach 31035 := rs (se 1 (by rfl) ⟨23276, by rfl⟩) R46553
theorem R63863 : Reach 63863 := rs (se 1 (by rfl) ⟨47897, by rfl⟩) R95795
theorem R31111 : Reach 31111 := rs (se 1 (by rfl) ⟨23333, by rfl⟩) R46667
theorem R96659 : Reach 96659 := rs (se 1 (by rfl) ⟨72494, by rfl⟩) R144989
theorem R64043 : Reach 64043 := rs (se 1 (by rfl) ⟨48032, by rfl⟩) R96065
theorem R359129 : Reach 359129 := rs (se 2 (by rfl) ⟨134673, by rfl⟩) R269347
theorem R31495 : Reach 31495 := rs (se 1 (by rfl) ⟨23621, by rfl⟩) R47243
theorem R64403 : Reach 64403 := rs (se 1 (by rfl) ⟨48302, by rfl⟩) R96605
theorem R31675 : Reach 31675 := rs (se 1 (by rfl) ⟨23756, by rfl⟩) R47513
theorem R64457 : Reach 64457 := rs (se 2 (by rfl) ⟨24171, by rfl⟩) R48343
theorem R261143 : Reach 261143 := rs (se 1 (by rfl) ⟨195857, by rfl⟩) R391715
theorem R32059 : Reach 32059 := rs (se 1 (by rfl) ⟨24044, by rfl⟩) R48089
theorem R32143 : Reach 32143 := rs (se 1 (by rfl) ⟨24107, by rfl⟩) R48215
theorem R2719331 : Reach 2719331 := rs (se 1 (by rfl) ⟨2039498, by rfl⟩) R4078997
theorem R65159 : Reach 65159 := rs (se 1 (by rfl) ⟨48869, by rfl⟩) R97739
theorem R65177 : Reach 65177 := rs (se 2 (by rfl) ⟨24441, by rfl⟩) R48883
theorem R32503 : Reach 32503 := rs (se 1 (by rfl) ⟨24377, by rfl⟩) R48755
theorem R98063 : Reach 98063 := rs (se 1 (by rfl) ⟨73547, by rfl⟩) R147095
theorem R65339 : Reach 65339 := rs (se 1 (by rfl) ⟨49004, by rfl⟩) R98009
theorem R32647 : Reach 32647 := rs (se 1 (by rfl) ⟨24485, by rfl⟩) R48971
theorem R393113 : Reach 393113 := rs (se 2 (by rfl) ⟨147417, by rfl⟩) R294835
theorem R32683 : Reach 32683 := rs (se 1 (by rfl) ⟨24512, by rfl⟩) R49025
theorem R65465 : Reach 65465 := rs (se 2 (by rfl) ⟨24549, by rfl⟩) R49099
theorem R229391 : Reach 229391 := rs (se 1 (by rfl) ⟨172043, by rfl⟩) R344087
theorem R65555 : Reach 65555 := rs (se 1 (by rfl) ⟨49166, by rfl⟩) R98333
theorem R98621 : Reach 98621 := rs (se 3 (by rfl) ⟨18491, by rfl⟩) R36983
theorem R65897 : Reach 65897 := rs (se 2 (by rfl) ⟨24711, by rfl⟩) R49423
theorem R98825 : Reach 98825 := rs (se 2 (by rfl) ⟨37059, by rfl⟩) R74119
theorem R33403 : Reach 33403 := rs (se 1 (by rfl) ⟨25052, by rfl⟩) R50105
theorem R66491 : Reach 66491 := rs (se 1 (by rfl) ⟨49868, by rfl⟩) R99737
theorem R361523 : Reach 361523 := rs (se 1 (by rfl) ⟨271142, by rfl⟩) R542285
theorem R164915 : Reach 164915 := rs (se 1 (by rfl) ⟨123686, by rfl⟩) R247373
theorem R66617 : Reach 66617 := rs (se 2 (by rfl) ⟨24981, by rfl⟩) R49963
theorem R33871 : Reach 33871 := rs (se 1 (by rfl) ⟨25403, by rfl⟩) R50807
theorem R132299 : Reach 132299 := rs (se 1 (by rfl) ⟨99224, by rfl⟩) R198449
theorem R99575 : Reach 99575 := rs (se 1 (by rfl) ⟨74681, by rfl⟩) R149363
theorem R66959 : Reach 66959 := rs (se 1 (by rfl) ⟨50219, by rfl⟩) R100439
theorem R34231 : Reach 34231 := rs (se 1 (by rfl) ⟨25673, by rfl⟩) R51347
theorem R132553 : Reach 132553 := rs (se 2 (by rfl) ⟨49707, by rfl⟩) R99415
theorem R34267 : Reach 34267 := rs (se 1 (by rfl) ⟨25700, by rfl⟩) R51401
theorem R99899 : Reach 99899 := rs (se 1 (by rfl) ⟨74924, by rfl⟩) R149849
theorem R886373 : Reach 886373 := rs (se 4 (by rfl) ⟨83097, by rfl⟩) R166195
theorem R67211 : Reach 67211 := rs (se 1 (by rfl) ⟨50408, by rfl⟩) R100817
theorem R67283 : Reach 67283 := rs (se 1 (by rfl) ⟨50462, by rfl⟩) R100925
theorem R100169 : Reach 100169 := rs (se 2 (by rfl) ⟨37563, by rfl⟩) R75127
theorem R34735 : Reach 34735 := rs (se 1 (by rfl) ⟨26051, by rfl⟩) R52103
theorem R100547 : Reach 100547 := rs (se 1 (by rfl) ⟨75410, by rfl⟩) R150821
theorem R231731 : Reach 231731 := rs (se 1 (by rfl) ⟨173798, by rfl⟩) R347597
theorem R35255 : Reach 35255 := rs (se 1 (by rfl) ⟨26441, by rfl⟩) R52883
theorem R133613 : Reach 133613 := rs (se 3 (by rfl) ⟨25052, by rfl⟩) R50105
theorem R35407 : Reach 35407 := rs (se 1 (by rfl) ⟨26555, by rfl⟩) R53111
theorem R68219 : Reach 68219 := rs (se 1 (by rfl) ⟨51164, by rfl⟩) R102329
theorem R68345 : Reach 68345 := rs (se 2 (by rfl) ⟨25629, by rfl⟩) R51259
theorem R1084229 : Reach 1084229 := rs (se 4 (by rfl) ⟨101646, by rfl⟩) R203293
theorem R101303 : Reach 101303 := rs (se 1 (by rfl) ⟨75977, by rfl⟩) R151955
theorem R68615 : Reach 68615 := rs (se 1 (by rfl) ⟨51461, by rfl⟩) R102923
theorem R68687 : Reach 68687 := rs (se 1 (by rfl) ⟨51515, by rfl⟩) R103031
theorem R232793 : Reach 232793 := rs (se 2 (by rfl) ⟨87297, by rfl⟩) R174595
theorem R68993 : Reach 68993 := rs (se 2 (by rfl) ⟨25872, by rfl⟩) R51745
theorem R69007 : Reach 69007 := rs (se 1 (by rfl) ⟨51755, by rfl⟩) R103511
theorem R69083 : Reach 69083 := rs (se 1 (by rfl) ⟨51812, by rfl⟩) R103625
theorem R101897 : Reach 101897 := rs (se 2 (by rfl) ⟨38211, by rfl⟩) R76423
theorem R36551 : Reach 36551 := rs (se 1 (by rfl) ⟨27413, by rfl⟩) R54827
theorem R69335 : Reach 69335 := rs (se 1 (by rfl) ⟨52001, by rfl⟩) R104003
theorem R36703 : Reach 36703 := rs (se 1 (by rfl) ⟨27527, by rfl⟩) R55055
theorem R36713 : Reach 36713 := rs (se 2 (by rfl) ⟨13767, by rfl⟩) R27535
theorem R69551 : Reach 69551 := rs (se 1 (by rfl) ⟨52163, by rfl⟩) R104327
theorem R69689 : Reach 69689 := rs (se 2 (by rfl) ⟨26133, by rfl⟩) R52267
theorem R69803 : Reach 69803 := rs (se 1 (by rfl) ⟨52352, by rfl⟩) R104705
theorem R102761 : Reach 102761 := rs (se 2 (by rfl) ⟨38535, by rfl⟩) R77071
theorem R135553 : Reach 135553 := rs (se 2 (by rfl) ⟨50832, by rfl⟩) R101665
theorem R201113 : Reach 201113 := rs (se 2 (by rfl) ⟨75417, by rfl⟩) R150835
theorem R102971 : Reach 102971 := rs (se 1 (by rfl) ⟨77228, by rfl⟩) R154457
theorem R70267 : Reach 70267 := rs (se 1 (by rfl) ⟨52700, by rfl⟩) R105401
theorem R103343 : Reach 103343 := rs (se 1 (by rfl) ⟨77507, by rfl⟩) R155015
theorem R103355 : Reach 103355 := rs (se 1 (by rfl) ⟨77516, by rfl⟩) R155033
theorem R103439 : Reach 103439 := rs (se 1 (by rfl) ⟨77579, by rfl⟩) R155159
theorem R104125 : Reach 104125 := rs (se 3 (by rfl) ⟨19523, by rfl⟩) R39047
theorem R169661 : Reach 169661 := rs (se 3 (by rfl) ⟨31811, by rfl⟩) R63623
theorem R235223 : Reach 235223 := rs (se 1 (by rfl) ⟨176417, by rfl⟩) R352835
theorem R169721 : Reach 169721 := rs (se 2 (by rfl) ⟨63645, by rfl⟩) R127291
theorem R38875 : Reach 38875 := rs (se 1 (by rfl) ⟨29156, by rfl⟩) R58313
theorem R333827 : Reach 333827 := rs (se 1 (by rfl) ⟨250370, by rfl⟩) R500741
theorem R333881 : Reach 333881 := rs (se 2 (by rfl) ⟨125205, by rfl⟩) R250411
theorem R202981 : Reach 202981 := rs (se 4 (by rfl) ⟨19029, by rfl⟩) R38059
theorem R39161 : Reach 39161 := rs (se 2 (by rfl) ⟨14685, by rfl⟩) R29371
theorem R1874501 : Reach 1874501 := rs (se 4 (by rfl) ⟨175734, by rfl⟩) R351469
theorem R105083 : Reach 105083 := rs (se 1 (by rfl) ⟨78812, by rfl⟩) R157625
theorem R105095 : Reach 105095 := rs (se 1 (by rfl) ⟨78821, by rfl⟩) R157643
theorem R105209 : Reach 105209 := rs (se 2 (by rfl) ⟨39453, by rfl⟩) R78907
theorem R170981 : Reach 170981 := rs (se 4 (by rfl) ⟨16029, by rfl⟩) R32059
theorem R400427 : Reach 400427 := rs (se 1 (by rfl) ⟨300320, by rfl⟩) R600641
theorem R105587 : Reach 105587 := rs (se 1 (by rfl) ⟨79190, by rfl⟩) R158381
theorem R171179 : Reach 171179 := rs (se 1 (by rfl) ⟨128384, by rfl⟩) R256769
theorem R40135 : Reach 40135 := rs (se 1 (by rfl) ⟨30101, by rfl⟩) R60203
theorem R105857 : Reach 105857 := rs (se 2 (by rfl) ⟨39696, by rfl⟩) R79393
theorem R40697 : Reach 40697 := rs (se 2 (by rfl) ⟨15261, by rfl⟩) R30523
theorem R40799 : Reach 40799 := rs (se 1 (by rfl) ⟨30599, by rfl⟩) R61199
theorem R40811 : Reach 40811 := rs (se 1 (by rfl) ⟨30608, by rfl⟩) R61217
theorem R73655 : Reach 73655 := rs (se 1 (by rfl) ⟨55241, by rfl⟩) R110483
theorem R434105 : Reach 434105 := rs (se 2 (by rfl) ⟨162789, by rfl⟩) R325579
theorem R41039 : Reach 41039 := rs (se 1 (by rfl) ⟨30779, by rfl⟩) R61559
theorem R41159 : Reach 41159 := rs (se 1 (by rfl) ⟨30869, by rfl⟩) R61739
theorem R41321 : Reach 41321 := rs (se 2 (by rfl) ⟨15495, by rfl⟩) R30991
theorem R41399 : Reach 41399 := rs (se 1 (by rfl) ⟨31049, by rfl⟩) R62099
theorem R41435 : Reach 41435 := rs (se 1 (by rfl) ⟨31076, by rfl⟩) R62153
theorem R107041 : Reach 107041 := rs (se 2 (by rfl) ⟨40140, by rfl⟩) R80281
theorem R74429 : Reach 74429 := rs (se 3 (by rfl) ⟨13955, by rfl⟩) R27911
theorem R41671 : Reach 41671 := rs (se 1 (by rfl) ⟨31253, by rfl⟩) R62507
theorem R74591 : Reach 74591 := rs (se 1 (by rfl) ⟨55943, by rfl⟩) R111887
theorem R41903 : Reach 41903 := rs (se 1 (by rfl) ⟨31427, by rfl⟩) R62855
theorem R861131 : Reach 861131 := rs (se 1 (by rfl) ⟨645848, by rfl⟩) R1291697
theorem R107527 : Reach 107527 := rs (se 1 (by rfl) ⟨80645, by rfl⟩) R161291
theorem R41993 : Reach 41993 := rs (se 2 (by rfl) ⟨15747, by rfl⟩) R31495
theorem R42023 : Reach 42023 := rs (se 1 (by rfl) ⟨31517, by rfl⟩) R63035
theorem R468017 : Reach 468017 := rs (se 2 (by rfl) ⟨175506, by rfl⟩) R351013
theorem R42107 : Reach 42107 := rs (se 1 (by rfl) ⟨31580, by rfl⟩) R63161
theorem R42233 : Reach 42233 := rs (se 2 (by rfl) ⟨15837, by rfl⟩) R31675
theorem R107837 : Reach 107837 := rs (se 3 (by rfl) ⟨20219, by rfl⟩) R40439
theorem R42335 : Reach 42335 := rs (se 1 (by rfl) ⟨31751, by rfl⟩) R63503
theorem R42347 : Reach 42347 := rs (se 1 (by rfl) ⟨31760, by rfl⟩) R63521
theorem R140687 : Reach 140687 := rs (se 1 (by rfl) ⟨105515, by rfl⟩) R211031
theorem R108013 : Reach 108013 := rs (se 3 (by rfl) ⟨20252, by rfl⟩) R40505
theorem R75289 : Reach 75289 := rs (se 2 (by rfl) ⟨28233, by rfl⟩) R56467
theorem R42575 : Reach 42575 := rs (se 1 (by rfl) ⟨31931, by rfl⟩) R63863
theorem R140939 : Reach 140939 := rs (se 1 (by rfl) ⟨105704, by rfl⟩) R211409
theorem R75403 : Reach 75403 := rs (se 1 (by rfl) ⟨56552, by rfl⟩) R113105
theorem R42695 : Reach 42695 := rs (se 1 (by rfl) ⟨32021, by rfl⟩) R64043
theorem R108317 : Reach 108317 := rs (se 3 (by rfl) ⟨20309, by rfl⟩) R40619
theorem R239419 : Reach 239419 := rs (se 1 (by rfl) ⟨179564, by rfl⟩) R359129
theorem R75593 : Reach 75593 := rs (se 2 (by rfl) ⟨28347, by rfl⟩) R56695
theorem R42857 : Reach 42857 := rs (se 2 (by rfl) ⟨16071, by rfl⟩) R32143
theorem R42935 : Reach 42935 := rs (se 1 (by rfl) ⟨32201, by rfl⟩) R64403
theorem R42971 : Reach 42971 := rs (se 1 (by rfl) ⟨32228, by rfl⟩) R64457
theorem R174095 : Reach 174095 := rs (se 1 (by rfl) ⟨130571, by rfl⟩) R261143
theorem R239773 : Reach 239773 := rs (se 3 (by rfl) ⟨44957, by rfl⟩) R89915
theorem R43337 : Reach 43337 := rs (se 2 (by rfl) ⟨16251, by rfl⟩) R32503
theorem R1812887 : Reach 1812887 := rs (se 1 (by rfl) ⟨1359665, by rfl⟩) R2719331
theorem R403865 : Reach 403865 := rs (se 2 (by rfl) ⟨151449, by rfl⟩) R302899
theorem R43439 : Reach 43439 := rs (se 1 (by rfl) ⟨32579, by rfl⟩) R65159
theorem R43451 : Reach 43451 := rs (se 1 (by rfl) ⟨32588, by rfl⟩) R65177
theorem R43529 : Reach 43529 := rs (se 2 (by rfl) ⟨16323, by rfl⟩) R32647
theorem R600605 : Reach 600605 := rs (se 3 (by rfl) ⟨112613, by rfl⟩) R225227
theorem R43559 : Reach 43559 := rs (se 1 (by rfl) ⟨32669, by rfl⟩) R65339
theorem R43577 : Reach 43577 := rs (se 2 (by rfl) ⟨16341, by rfl⟩) R32683
theorem R43643 : Reach 43643 := rs (se 1 (by rfl) ⟨32732, by rfl⟩) R65465
theorem R43691 : Reach 43691 := rs (se 1 (by rfl) ⟨32768, by rfl⟩) R65537
theorem R43769 : Reach 43769 := rs (se 2 (by rfl) ⟨16413, by rfl⟩) R32827
theorem R43871 : Reach 43871 := rs (se 1 (by rfl) ⟨32903, by rfl⟩) R65807
theorem R43883 : Reach 43883 := rs (se 1 (by rfl) ⟨32912, by rfl⟩) R65825
theorem R43919 : Reach 43919 := rs (se 1 (by rfl) ⟨32939, by rfl⟩) R65879
theorem R76727 : Reach 76727 := rs (se 1 (by rfl) ⟨57545, by rfl⟩) R115091
theorem R338917 : Reach 338917 := rs (se 4 (by rfl) ⟨31773, by rfl⟩) R63547
theorem R44039 : Reach 44039 := rs (se 1 (by rfl) ⟨33029, by rfl⟩) R66059
theorem R44111 : Reach 44111 := rs (se 1 (by rfl) ⟨33083, by rfl⟩) R66167
theorem R44231 : Reach 44231 := rs (se 1 (by rfl) ⟨33173, by rfl⟩) R66347
theorem R44279 : Reach 44279 := rs (se 1 (by rfl) ⟨33209, by rfl⟩) R66419
theorem R44393 : Reach 44393 := rs (se 2 (by rfl) ⟨16647, by rfl⟩) R33295
theorem R44471 : Reach 44471 := rs (se 1 (by rfl) ⟨33353, by rfl⟩) R66707
theorem R44507 : Reach 44507 := rs (se 1 (by rfl) ⟨33380, by rfl⟩) R66761
theorem R143147 : Reach 143147 := rs (se 1 (by rfl) ⟨107360, by rfl⟩) R214721
theorem R44873 : Reach 44873 := rs (se 2 (by rfl) ⟨16827, by rfl⟩) R33655
theorem R110443 : Reach 110443 := rs (se 1 (by rfl) ⟨82832, by rfl⟩) R165665
theorem R44975 : Reach 44975 := rs (se 1 (by rfl) ⟨33731, by rfl⟩) R67463
theorem R44987 : Reach 44987 := rs (se 1 (by rfl) ⟨33740, by rfl⟩) R67481
theorem R77831 : Reach 77831 := rs (se 1 (by rfl) ⟨58373, by rfl⟩) R116747
theorem R45065 : Reach 45065 := rs (se 2 (by rfl) ⟨16899, by rfl⟩) R33799
theorem R45095 : Reach 45095 := rs (se 1 (by rfl) ⟨33821, by rfl⟩) R67643
theorem R45113 : Reach 45113 := rs (se 2 (by rfl) ⟨16917, by rfl⟩) R33835
theorem R77881 : Reach 77881 := rs (se 2 (by rfl) ⟨29205, by rfl⟩) R58411
theorem R667763 : Reach 667763 := rs (se 1 (by rfl) ⟨500822, by rfl⟩) R1001645
theorem R45179 : Reach 45179 := rs (se 1 (by rfl) ⟨33884, by rfl⟩) R67769
theorem R45227 : Reach 45227 := rs (se 1 (by rfl) ⟨33920, by rfl⟩) R67841
theorem R45305 : Reach 45305 := rs (se 2 (by rfl) ⟨16989, by rfl⟩) R33979
theorem R45407 : Reach 45407 := rs (se 1 (by rfl) ⟨34055, by rfl⟩) R68111
theorem R78185 : Reach 78185 := rs (se 2 (by rfl) ⟨29319, by rfl⟩) R58639
theorem R45419 : Reach 45419 := rs (se 1 (by rfl) ⟨34064, by rfl⟩) R68129
theorem R78205 : Reach 78205 := rs (se 3 (by rfl) ⟨14663, by rfl⟩) R29327
theorem R78209 : Reach 78209 := rs (se 2 (by rfl) ⟨29328, by rfl⟩) R58657
theorem R45455 : Reach 45455 := rs (se 1 (by rfl) ⟨34091, by rfl⟩) R68183
theorem R45575 : Reach 45575 := rs (se 1 (by rfl) ⟨34181, by rfl⟩) R68363
theorem R45647 : Reach 45647 := rs (se 1 (by rfl) ⟨34235, by rfl⟩) R68471
theorem R45767 : Reach 45767 := rs (se 1 (by rfl) ⟨34325, by rfl⟩) R68651
theorem R45815 : Reach 45815 := rs (se 1 (by rfl) ⟨34361, by rfl⟩) R68723
theorem R45929 : Reach 45929 := rs (se 2 (by rfl) ⟨17223, by rfl⟩) R34447
theorem R111469 : Reach 111469 := rs (se 3 (by rfl) ⟨20900, by rfl⟩) R41801
theorem R45967 : Reach 45967 := rs (se 1 (by rfl) ⟨34475, by rfl⟩) R68951
theorem R46007 : Reach 46007 := rs (se 1 (by rfl) ⟨34505, by rfl⟩) R69011
theorem R46043 : Reach 46043 := rs (se 1 (by rfl) ⟨34532, by rfl⟩) R69065
theorem R46409 : Reach 46409 := rs (se 2 (by rfl) ⟨17403, by rfl⟩) R34807
theorem R46511 : Reach 46511 := rs (se 1 (by rfl) ⟨34883, by rfl⟩) R69767
theorem R46523 : Reach 46523 := rs (se 1 (by rfl) ⟨34892, by rfl⟩) R69785
theorem R46601 : Reach 46601 := rs (se 2 (by rfl) ⟨17475, by rfl⟩) R34951
theorem R144935 : Reach 144935 := rs (se 1 (by rfl) ⟨108701, by rfl⟩) R217403
theorem R46631 : Reach 46631 := rs (se 1 (by rfl) ⟨34973, by rfl⟩) R69947
theorem R46649 : Reach 46649 := rs (se 2 (by rfl) ⟨17493, by rfl⟩) R34987
theorem R145313 : Reach 145313 := rs (se 2 (by rfl) ⟨54492, by rfl⟩) R108985
theorem R47351 : Reach 47351 := rs (se 1 (by rfl) ⟨35513, by rfl⟩) R71027
theorem R80347 : Reach 80347 := rs (se 1 (by rfl) ⟨60260, by rfl⟩) R120521
theorem R113177 : Reach 113177 := rs (se 2 (by rfl) ⟨42441, by rfl⟩) R84883
theorem R47695 : Reach 47695 := rs (se 1 (by rfl) ⟨35771, by rfl⟩) R71543
theorem R47945 : Reach 47945 := rs (se 2 (by rfl) ⟨17979, by rfl⟩) R35959
theorem R211895 : Reach 211895 := rs (se 1 (by rfl) ⟨158921, by rfl⟩) R317843
theorem R48055 : Reach 48055 := rs (se 1 (by rfl) ⟨36041, by rfl⟩) R72083
theorem R48377 : Reach 48377 := rs (se 2 (by rfl) ⟨18141, by rfl⟩) R36283
theorem R48559 : Reach 48559 := rs (se 1 (by rfl) ⟨36419, by rfl⟩) R72839
theorem R48647 : Reach 48647 := rs (se 1 (by rfl) ⟨36485, by rfl⟩) R72971
theorem R48991 : Reach 48991 := rs (se 1 (by rfl) ⟨36743, by rfl⟩) R73487
theorem R49079 : Reach 49079 := rs (se 1 (by rfl) ⟨36809, by rfl⟩) R73619
theorem R114803 : Reach 114803 := rs (se 1 (by rfl) ⟨86102, by rfl⟩) R172205
theorem R606437 : Reach 606437 := rs (se 4 (by rfl) ⟨56853, by rfl⟩) R113707
theorem R213353 : Reach 213353 := rs (se 2 (by rfl) ⟨80007, by rfl⟩) R160015
theorem R49673 : Reach 49673 := rs (se 2 (by rfl) ⟨18627, by rfl⟩) R37255
theorem R49835 : Reach 49835 := rs (se 1 (by rfl) ⟨37376, by rfl⟩) R74753
theorem R2081477 : Reach 2081477 := rs (se 4 (by rfl) ⟨195138, by rfl⟩) R390277
theorem R50195 : Reach 50195 := rs (se 1 (by rfl) ⟨37646, by rfl⟩) R75293
theorem R50233 : Reach 50233 := rs (se 2 (by rfl) ⟨18837, by rfl⟩) R37675
theorem R50375 : Reach 50375 := rs (se 1 (by rfl) ⟨37781, by rfl⟩) R75563
theorem R50537 : Reach 50537 := rs (se 2 (by rfl) ⟨18951, by rfl⟩) R37903
theorem R116093 : Reach 116093 := rs (se 3 (by rfl) ⟨21767, by rfl⟩) R43535
theorem R345545 : Reach 345545 := rs (se 2 (by rfl) ⟨129579, by rfl⟩) R259159
theorem R214667 : Reach 214667 := rs (se 1 (by rfl) ⟨161000, by rfl⟩) R322001
theorem R50935 : Reach 50935 := rs (se 1 (by rfl) ⟨38201, by rfl⟩) R76403
theorem R444203 : Reach 444203 := rs (se 1 (by rfl) ⟨333152, by rfl⟩) R666305
theorem R149435 : Reach 149435 := rs (se 1 (by rfl) ⟨112076, by rfl⟩) R224153
theorem R51131 : Reach 51131 := rs (se 1 (by rfl) ⟨38348, by rfl⟩) R76697
theorem R51239 : Reach 51239 := rs (se 1 (by rfl) ⟨38429, by rfl⟩) R76859
theorem R215297 : Reach 215297 := rs (se 2 (by rfl) ⟨80736, by rfl⟩) R161473
theorem R51529 : Reach 51529 := rs (se 2 (by rfl) ⟨19323, by rfl⟩) R38647
theorem R51563 : Reach 51563 := rs (se 1 (by rfl) ⟨38672, by rfl⟩) R77345
theorem R51617 : Reach 51617 := rs (se 2 (by rfl) ⟨19356, by rfl⟩) R38713
theorem R51835 : Reach 51835 := rs (se 1 (by rfl) ⟨38876, by rfl⟩) R77753
theorem R51911 : Reach 51911 := rs (se 1 (by rfl) ⟨38933, by rfl⟩) R77867
theorem R84691 : Reach 84691 := rs (se 1 (by rfl) ⟨63518, by rfl⟩) R127037
theorem R51961 : Reach 51961 := rs (se 2 (by rfl) ⟨19485, by rfl⟩) R38971
theorem R52073 : Reach 52073 := rs (se 2 (by rfl) ⟨19527, by rfl⟩) R39055
theorem R52231 : Reach 52231 := rs (se 1 (by rfl) ⟨39173, by rfl⟩) R78347
theorem R52321 : Reach 52321 := rs (se 2 (by rfl) ⟨19620, by rfl⟩) R39241
theorem R118007 : Reach 118007 := rs (se 1 (by rfl) ⟨88505, by rfl⟩) R177011
theorem R970157 : Reach 970157 := rs (se 3 (by rfl) ⟨181904, by rfl⟩) R363809
theorem R52663 : Reach 52663 := rs (se 1 (by rfl) ⟨39497, by rfl⟩) R78995
theorem R118235 : Reach 118235 := rs (se 1 (by rfl) ⟨88676, by rfl⟩) R177353
theorem R53065 : Reach 53065 := rs (se 2 (by rfl) ⟨19899, by rfl⟩) R39799
theorem R53779 : Reach 53779 := rs (se 1 (by rfl) ⟨40334, by rfl⟩) R80669
theorem R774917 : Reach 774917 := rs (se 4 (by rfl) ⟨72648, by rfl⟩) R145297
theorem R54121 : Reach 54121 := rs (se 2 (by rfl) ⟨20295, by rfl⟩) R40591
theorem R284305 : Reach 284305 := rs (se 2 (by rfl) ⟨106614, by rfl⟩) R213229
theorem R350365 : Reach 350365 := rs (se 3 (by rfl) ⟨65693, by rfl⟩) R131387
theorem R55495 : Reach 55495 := rs (se 1 (by rfl) ⟨41621, by rfl⟩) R83243
theorem R121175 : Reach 121175 := rs (se 1 (by rfl) ⟨90881, by rfl⟩) R181763
theorem R711017 : Reach 711017 := rs (se 2 (by rfl) ⟨266631, by rfl⟩) R533263
theorem R809453 : Reach 809453 := rs (se 3 (by rfl) ⟨151772, by rfl⟩) R303545
theorem R219671 : Reach 219671 := rs (se 1 (by rfl) ⟨164753, by rfl⟩) R329507
theorem R88699 : Reach 88699 := rs (se 1 (by rfl) ⟨66524, by rfl⟩) R133049
theorem R154871 : Reach 154871 := rs (se 1 (by rfl) ⟨116153, by rfl⟩) R232307
theorem R187991 : Reach 187991 := rs (se 1 (by rfl) ⟨140993, by rfl⟩) R281987
theorem R220805 : Reach 220805 := rs (se 4 (by rfl) ⟨20700, by rfl⟩) R41401
theorem R89785 : Reach 89785 := rs (se 2 (by rfl) ⟨33669, by rfl⟩) R67339
theorem R155357 : Reach 155357 := rs (se 3 (by rfl) ⟨29129, by rfl⟩) R58259
theorem R188203 : Reach 188203 := rs (se 1 (by rfl) ⟨141152, by rfl⟩) R282305
theorem R188219 : Reach 188219 := rs (se 1 (by rfl) ⟨141164, by rfl⟩) R282329
theorem R155459 : Reach 155459 := rs (se 1 (by rfl) ⟨116594, by rfl⟩) R233189
theorem R221089 : Reach 221089 := rs (se 2 (by rfl) ⟨82908, by rfl⟩) R165817
theorem R286651 : Reach 286651 := rs (se 1 (by rfl) ⟨214988, by rfl⟩) R429977
theorem R155915 : Reach 155915 := rs (se 1 (by rfl) ⟨116936, by rfl⟩) R233873
theorem R680293 : Reach 680293 := rs (se 4 (by rfl) ⟨63777, by rfl⟩) R127555
theorem R57743 : Reach 57743 := rs (se 1 (by rfl) ⟨43307, by rfl⟩) R86615
theorem R156599 : Reach 156599 := rs (se 1 (by rfl) ⟨117449, by rfl⟩) R234899
theorem R3433859 : Reach 3433859 := rs (se 1 (by rfl) ⟨2575394, by rfl⟩) R5150789
theorem R91745 : Reach 91745 := rs (se 2 (by rfl) ⟨34404, by rfl⟩) R68809
theorem R157373 : Reach 157373 := rs (se 3 (by rfl) ⟨29507, by rfl⟩) R59015
theorem R59231 : Reach 59231 := rs (se 1 (by rfl) ⟨44423, by rfl⟩) R88847
theorem R157601 : Reach 157601 := rs (se 2 (by rfl) ⟨59100, by rfl⟩) R118201
theorem R92087 : Reach 92087 := rs (se 1 (by rfl) ⟨69065, by rfl⟩) R138131
theorem R158057 : Reach 158057 := rs (se 2 (by rfl) ⟨59271, by rfl⟩) R118543
theorem R747953 : Reach 747953 := rs (se 2 (by rfl) ⟨280482, by rfl⟩) R560965
theorem R27175 : Reach 27175 := rs (se 1 (by rfl) ⟨20381, by rfl⟩) R40763
theorem R27215 : Reach 27215 := rs (se 1 (by rfl) ⟨20411, by rfl⟩) R40823
theorem R27231 : Reach 27231 := rs (se 1 (by rfl) ⟨20423, by rfl⟩) R40847
theorem R27259 : Reach 27259 := rs (se 1 (by rfl) ⟨20444, by rfl⟩) R40889
theorem R27311 : Reach 27311 := rs (se 1 (by rfl) ⟨20483, by rfl⟩) R40967
theorem R27335 : Reach 27335 := rs (se 1 (by rfl) ⟨20501, by rfl⟩) R41003
theorem R125651 : Reach 125651 := rs (se 1 (by rfl) ⟨94238, by rfl⟩) R188477
theorem R27355 : Reach 27355 := rs (se 1 (by rfl) ⟨20516, by rfl⟩) R41033
theorem R27431 : Reach 27431 := rs (se 1 (by rfl) ⟨20573, by rfl⟩) R41147
theorem R518987 : Reach 518987 := rs (se 1 (by rfl) ⟨389240, by rfl⟩) R778481
theorem R27471 : Reach 27471 := rs (se 1 (by rfl) ⟨20603, by rfl⟩) R41207
theorem R27487 : Reach 27487 := rs (se 1 (by rfl) ⟨20615, by rfl⟩) R41231
theorem R27515 : Reach 27515 := rs (se 1 (by rfl) ⟨20636, by rfl⟩) R41273
theorem R27567 : Reach 27567 := rs (se 1 (by rfl) ⟨20675, by rfl⟩) R41351
theorem R27591 : Reach 27591 := rs (se 1 (by rfl) ⟨20693, by rfl⟩) R41387
theorem R27611 : Reach 27611 := rs (se 1 (by rfl) ⟨20708, by rfl⟩) R41417
theorem R93203 : Reach 93203 := rs (se 1 (by rfl) ⟨69902, by rfl⟩) R139805
theorem R27687 : Reach 27687 := rs (se 1 (by rfl) ⟨20765, by rfl⟩) R41531
theorem R27727 : Reach 27727 := rs (se 1 (by rfl) ⟨20795, by rfl⟩) R41591
theorem R27743 : Reach 27743 := rs (se 1 (by rfl) ⟨20807, by rfl⟩) R41615
theorem R27771 : Reach 27771 := rs (se 1 (by rfl) ⟨20828, by rfl⟩) R41657
theorem R27823 : Reach 27823 := rs (se 1 (by rfl) ⟨20867, by rfl⟩) R41735
theorem R715969 : Reach 715969 := rs (se 2 (by rfl) ⟨268488, by rfl⟩) R536977
theorem R27847 : Reach 27847 := rs (se 1 (by rfl) ⟨20885, by rfl⟩) R41771
theorem R27867 : Reach 27867 := rs (se 1 (by rfl) ⟨20900, by rfl⟩) R41801
theorem R27943 : Reach 27943 := rs (se 1 (by rfl) ⟨20957, by rfl⟩) R41915
theorem R27983 : Reach 27983 := rs (se 1 (by rfl) ⟨20987, by rfl⟩) R41975
theorem R93527 : Reach 93527 := rs (se 1 (by rfl) ⟨70145, by rfl⟩) R140291
theorem R27999 : Reach 27999 := rs (se 1 (by rfl) ⟨20999, by rfl⟩) R41999
theorem R28027 : Reach 28027 := rs (se 1 (by rfl) ⟨21020, by rfl⟩) R42041
theorem R191909 : Reach 191909 := rs (se 4 (by rfl) ⟨17991, by rfl⟩) R35983
theorem R28079 : Reach 28079 := rs (se 1 (by rfl) ⟨21059, by rfl⟩) R42119
theorem R28103 : Reach 28103 := rs (se 1 (by rfl) ⟨21077, by rfl⟩) R42155
theorem R28123 : Reach 28123 := rs (se 1 (by rfl) ⟨21092, by rfl⟩) R42185
theorem R28199 : Reach 28199 := rs (se 1 (by rfl) ⟨21149, by rfl⟩) R42299
theorem R28239 : Reach 28239 := rs (se 1 (by rfl) ⟨21179, by rfl⟩) R42359
theorem R28255 : Reach 28255 := rs (se 1 (by rfl) ⟨21191, by rfl⟩) R42383
theorem R28283 : Reach 28283 := rs (se 1 (by rfl) ⟨21212, by rfl⟩) R42425
theorem R28335 : Reach 28335 := rs (se 1 (by rfl) ⟨21251, by rfl⟩) R42503
theorem R61127 : Reach 61127 := rs (se 1 (by rfl) ⟨45845, by rfl⟩) R91691
theorem R28359 : Reach 28359 := rs (se 1 (by rfl) ⟨21269, by rfl⟩) R42539
theorem R28379 : Reach 28379 := rs (se 1 (by rfl) ⟨21284, by rfl⟩) R42569
theorem R225017 : Reach 225017 := rs (se 2 (by rfl) ⟨84381, by rfl⟩) R168763
theorem R61177 : Reach 61177 := rs (se 2 (by rfl) ⟨22941, by rfl⟩) R45883
theorem R28455 : Reach 28455 := rs (se 1 (by rfl) ⟨21341, by rfl⟩) R42683
theorem R28495 : Reach 28495 := rs (se 1 (by rfl) ⟨21371, by rfl⟩) R42743
theorem R28511 : Reach 28511 := rs (se 1 (by rfl) ⟨21383, by rfl⟩) R42767
theorem R28539 : Reach 28539 := rs (se 1 (by rfl) ⟨21404, by rfl⟩) R42809
theorem R28591 : Reach 28591 := rs (se 1 (by rfl) ⟨21443, by rfl⟩) R42887
theorem R28635 : Reach 28635 := rs (se 1 (by rfl) ⟨21476, by rfl⟩) R42953
theorem R126983 : Reach 126983 := rs (se 1 (by rfl) ⟨95237, by rfl⟩) R190475
theorem R28711 : Reach 28711 := rs (se 1 (by rfl) ⟨21533, by rfl⟩) R43067
theorem R28751 : Reach 28751 := rs (se 1 (by rfl) ⟨21563, by rfl⟩) R43127
theorem R159833 : Reach 159833 := rs (se 2 (by rfl) ⟨59937, by rfl⟩) R119875
theorem R28795 : Reach 28795 := rs (se 1 (by rfl) ⟨21596, by rfl⟩) R43193
theorem R28871 : Reach 28871 := rs (se 1 (by rfl) ⟨21653, by rfl⟩) R43307
theorem R29023 : Reach 29023 := rs (se 1 (by rfl) ⟨21767, by rfl⟩) R43535
theorem R94607 : Reach 94607 := rs (se 1 (by rfl) ⟨70955, by rfl⟩) R141911
theorem R29103 : Reach 29103 := rs (se 1 (by rfl) ⟨21827, by rfl⟩) R43655
theorem R29147 : Reach 29147 := rs (se 1 (by rfl) ⟨21860, by rfl⟩) R43721
theorem R160289 : Reach 160289 := rs (se 2 (by rfl) ⟨60108, by rfl⟩) R120217
theorem R61991 : Reach 61991 := rs (se 1 (by rfl) ⟨46493, by rfl⟩) R92987
theorem R29223 : Reach 29223 := rs (se 1 (by rfl) ⟨21917, by rfl⟩) R43835
theorem R324155 : Reach 324155 := rs (se 1 (by rfl) ⟨243116, by rfl⟩) R486233
theorem R29263 : Reach 29263 := rs (se 1 (by rfl) ⟨21947, by rfl⟩) R43895
theorem R29307 : Reach 29307 := rs (se 1 (by rfl) ⟨21980, by rfl⟩) R43961
theorem R29383 : Reach 29383 := rs (se 1 (by rfl) ⟨22037, by rfl⟩) R44075
theorem R94931 : Reach 94931 := rs (se 1 (by rfl) ⟨71198, by rfl⟩) R142397
theorem R160541 : Reach 160541 := rs (se 3 (by rfl) ⟨30101, by rfl⟩) R60203
theorem R29535 : Reach 29535 := rs (se 1 (by rfl) ⟨22151, by rfl⟩) R44303
theorem R62315 : Reach 62315 := rs (se 1 (by rfl) ⟨46736, by rfl⟩) R93473
theorem R914327 : Reach 914327 := rs (se 1 (by rfl) ⟨685745, by rfl⟩) R1371491
theorem R62369 : Reach 62369 := rs (se 2 (by rfl) ⟨23388, by rfl⟩) R46777
theorem R29615 : Reach 29615 := rs (se 1 (by rfl) ⟨22211, by rfl⟩) R44423
theorem R29659 : Reach 29659 := rs (se 1 (by rfl) ⟨22244, by rfl⟩) R44489
theorem R29735 : Reach 29735 := rs (se 1 (by rfl) ⟨22301, by rfl⟩) R44603
theorem R29775 : Reach 29775 := rs (se 1 (by rfl) ⟨22331, by rfl⟩) R44663
theorem R29819 : Reach 29819 := rs (se 1 (by rfl) ⟨22364, by rfl⟩) R44729
theorem R226475 : Reach 226475 := rs (se 1 (by rfl) ⟨169856, by rfl⟩) R339713
theorem R29895 : Reach 29895 := rs (se 1 (by rfl) ⟨22421, by rfl⟩) R44843
theorem R62711 : Reach 62711 := rs (se 1 (by rfl) ⟨47033, by rfl⟩) R94067
theorem R30047 : Reach 30047 := rs (se 1 (by rfl) ⟨22535, by rfl⟩) R45071
theorem R30127 : Reach 30127 := rs (se 1 (by rfl) ⟨22595, by rfl⟩) R45191
theorem R30171 : Reach 30171 := rs (se 1 (by rfl) ⟨22628, by rfl⟩) R45257
theorem R30247 : Reach 30247 := rs (se 1 (by rfl) ⟨22685, by rfl⟩) R45371
theorem R30287 : Reach 30287 := rs (se 1 (by rfl) ⟨22715, by rfl⟩) R45431
theorem R30331 : Reach 30331 := rs (se 1 (by rfl) ⟨22748, by rfl⟩) R45497
theorem R95879 : Reach 95879 := rs (se 1 (by rfl) ⟨71909, by rfl⟩) R143819
theorem R226961 : Reach 226961 := rs (se 2 (by rfl) ⟨85110, by rfl⟩) R170221
theorem R30407 : Reach 30407 := rs (se 1 (by rfl) ⟨22805, by rfl⟩) R45611
theorem R63305 : Reach 63305 := rs (se 2 (by rfl) ⟨23739, by rfl⟩) R47479
theorem R30559 : Reach 30559 := rs (se 1 (by rfl) ⟨22919, by rfl⟩) R45839
theorem R96119 : Reach 96119 := rs (se 1 (by rfl) ⟨72089, by rfl⟩) R144179
theorem R30639 : Reach 30639 := rs (se 1 (by rfl) ⟨22979, by rfl⟩) R45959
theorem R96187 : Reach 96187 := rs (se 1 (by rfl) ⟨72140, by rfl⟩) R144281
theorem R30683 : Reach 30683 := rs (se 1 (by rfl) ⟨23012, by rfl⟩) R46025
theorem R194575 : Reach 194575 := rs (se 1 (by rfl) ⟨145931, by rfl⟩) R291863
theorem R30759 : Reach 30759 := rs (se 1 (by rfl) ⟨23069, by rfl⟩) R46139
theorem R96335 : Reach 96335 := rs (se 1 (by rfl) ⟨72251, by rfl⟩) R144503
theorem R30799 : Reach 30799 := rs (se 1 (by rfl) ⟨23099, by rfl⟩) R46199
theorem R30843 : Reach 30843 := rs (se 1 (by rfl) ⟨23132, by rfl⟩) R46265
theorem R30919 : Reach 30919 := rs (se 1 (by rfl) ⟨23189, by rfl⟩) R46379
theorem R31071 : Reach 31071 := rs (se 1 (by rfl) ⟨23303, by rfl⟩) R46607
theorem R96713 : Reach 96713 := rs (se 2 (by rfl) ⟨36267, by rfl⟩) R72535
theorem R31195 : Reach 31195 := rs (se 1 (by rfl) ⟨23396, by rfl⟩) R46793
theorem R64097 : Reach 64097 := rs (se 2 (by rfl) ⟨24036, by rfl⟩) R48073
theorem R228041 : Reach 228041 := rs (se 2 (by rfl) ⟨85515, by rfl⟩) R171031
theorem R96983 : Reach 96983 := rs (se 1 (by rfl) ⟨72737, by rfl⟩) R145475
theorem R97091 : Reach 97091 := rs (se 1 (by rfl) ⟨72818, by rfl⟩) R145637
theorem R97199 : Reach 97199 := rs (se 1 (by rfl) ⟨72899, by rfl⟩) R145799
theorem R64439 : Reach 64439 := rs (se 1 (by rfl) ⟨48329, by rfl⟩) R96659
theorem R31783 : Reach 31783 := rs (se 1 (by rfl) ⟨23837, by rfl⟩) R47675
theorem R228419 : Reach 228419 := rs (se 1 (by rfl) ⟨171314, by rfl⟩) R342629
theorem R97361 : Reach 97361 := rs (se 2 (by rfl) ⟨36510, by rfl⟩) R73021
theorem R65033 : Reach 65033 := rs (se 2 (by rfl) ⟨24387, by rfl⟩) R48775
theorem R163475 : Reach 163475 := rs (se 1 (by rfl) ⟨122606, by rfl⟩) R245213
theorem R65375 : Reach 65375 := rs (se 1 (by rfl) ⟨49031, by rfl⟩) R98063
theorem R262075 : Reach 262075 := rs (se 1 (by rfl) ⟨196556, by rfl⟩) R393113
theorem R65747 : Reach 65747 := rs (se 1 (by rfl) ⟨49310, by rfl⟩) R98621
theorem R33115 : Reach 33115 := rs (se 1 (by rfl) ⟨24836, by rfl⟩) R49673
theorem R33223 : Reach 33223 := rs (se 1 (by rfl) ⟨24917, by rfl⟩) R49835
theorem R33463 : Reach 33463 := rs (se 1 (by rfl) ⟨25097, by rfl⟩) R50195
theorem R33583 : Reach 33583 := rs (se 1 (by rfl) ⟨25187, by rfl⟩) R50375
theorem R66383 : Reach 66383 := rs (se 1 (by rfl) ⟨49787, by rfl⟩) R99575
theorem R33691 : Reach 33691 := rs (se 1 (by rfl) ⟨25268, by rfl⟩) R50537
theorem R230363 : Reach 230363 := rs (se 1 (by rfl) ⟨172772, by rfl⟩) R345545
theorem R66599 : Reach 66599 := rs (se 1 (by rfl) ⟨49949, by rfl⟩) R99899
theorem R590915 : Reach 590915 := rs (se 1 (by rfl) ⟨443186, by rfl⟩) R886373
theorem R296135 : Reach 296135 := rs (se 1 (by rfl) ⟨222101, by rfl⟩) R444203
theorem R66779 : Reach 66779 := rs (se 1 (by rfl) ⟨50084, by rfl⟩) R100169
theorem R99623 : Reach 99623 := rs (se 1 (by rfl) ⟨74717, by rfl⟩) R149435
theorem R34087 : Reach 34087 := rs (se 1 (by rfl) ⟨25565, by rfl⟩) R51131
theorem R263533 : Reach 263533 := rs (se 3 (by rfl) ⟨49412, by rfl⟩) R98825
theorem R34159 : Reach 34159 := rs (se 1 (by rfl) ⟨25619, by rfl⟩) R51239
theorem R66977 : Reach 66977 := rs (se 2 (by rfl) ⟨25116, by rfl⟩) R50233
theorem R67031 : Reach 67031 := rs (se 1 (by rfl) ⟨50273, by rfl⟩) R100547
theorem R34375 : Reach 34375 := rs (se 1 (by rfl) ⟨25781, by rfl⟩) R51563
theorem R34411 : Reach 34411 := rs (se 1 (by rfl) ⟨25808, by rfl⟩) R51617
theorem R34607 : Reach 34607 := rs (se 1 (by rfl) ⟨25955, by rfl⟩) R51911
theorem R722819 : Reach 722819 := rs (se 1 (by rfl) ⟨542114, by rfl⟩) R1084229
theorem R34715 : Reach 34715 := rs (se 1 (by rfl) ⟨26036, by rfl⟩) R52073
theorem R67535 : Reach 67535 := rs (se 1 (by rfl) ⟨50651, by rfl⟩) R101303
theorem R100385 : Reach 100385 := rs (se 2 (by rfl) ⟨37644, by rfl⟩) R75289
theorem R67913 : Reach 67913 := rs (se 2 (by rfl) ⟨25467, by rfl⟩) R50935
theorem R67931 : Reach 67931 := rs (se 1 (by rfl) ⟨50948, by rfl⟩) R101897
theorem R166373 : Reach 166373 := rs (se 4 (by rfl) ⟨15597, by rfl⟩) R31195
theorem R2296349 : Reach 2296349 := rs (se 3 (by rfl) ⟨430565, by rfl⟩) R861131
theorem R68507 : Reach 68507 := rs (se 1 (by rfl) ⟨51380, by rfl⟩) R102761
theorem R134075 : Reach 134075 := rs (se 1 (by rfl) ⟨100556, by rfl⟩) R201113
theorem R68647 : Reach 68647 := rs (se 1 (by rfl) ⟨51485, by rfl⟩) R102971
theorem R68705 : Reach 68705 := rs (se 2 (by rfl) ⟨25764, by rfl⟩) R51529
theorem R68903 : Reach 68903 := rs (se 1 (by rfl) ⟨51677, by rfl⟩) R103355
theorem R68959 : Reach 68959 := rs (se 1 (by rfl) ⟨51719, by rfl⟩) R103439
theorem R69113 : Reach 69113 := rs (se 2 (by rfl) ⟨25917, by rfl⟩) R51835
theorem R69281 : Reach 69281 := rs (se 2 (by rfl) ⟨25980, by rfl⟩) R51961
theorem R69641 : Reach 69641 := rs (se 2 (by rfl) ⟨26115, by rfl⟩) R52231
theorem R69761 : Reach 69761 := rs (se 2 (by rfl) ⟨26160, by rfl⟩) R52321
theorem R954625 : Reach 954625 := rs (se 2 (by rfl) ⟨357984, by rfl⟩) R715969
theorem R1249667 : Reach 1249667 := rs (se 1 (by rfl) ⟨937250, by rfl⟩) R1874501
theorem R70055 : Reach 70055 := rs (se 1 (by rfl) ⟨52541, by rfl⟩) R105083
theorem R70139 : Reach 70139 := rs (se 1 (by rfl) ⟨52604, by rfl⟩) R105209
theorem R70217 : Reach 70217 := rs (se 2 (by rfl) ⟨26331, by rfl⟩) R52663
theorem R266951 : Reach 266951 := rs (se 1 (by rfl) ⟨200213, by rfl⟩) R400427
theorem R70391 : Reach 70391 := rs (se 1 (by rfl) ⟨52793, by rfl⟩) R105587
theorem R103247 : Reach 103247 := rs (se 1 (by rfl) ⟨77435, by rfl⟩) R154871
theorem R70571 : Reach 70571 := rs (se 1 (by rfl) ⟨52928, by rfl⟩) R105857
theorem R70753 : Reach 70753 := rs (se 2 (by rfl) ⟨26532, by rfl⟩) R53065
theorem R103571 : Reach 103571 := rs (se 1 (by rfl) ⟨77678, by rfl⟩) R155357
theorem R103639 : Reach 103639 := rs (se 1 (by rfl) ⟨77729, by rfl⟩) R155459
theorem R103841 : Reach 103841 := rs (se 2 (by rfl) ⟨38940, by rfl⟩) R77881
theorem R103943 : Reach 103943 := rs (se 1 (by rfl) ⟨77957, by rfl⟩) R155915
theorem R38495 : Reach 38495 := rs (se 1 (by rfl) ⟨28871, by rfl⟩) R57743
theorem R104273 : Reach 104273 := rs (se 2 (by rfl) ⟨39102, by rfl⟩) R78205
theorem R104399 : Reach 104399 := rs (se 1 (by rfl) ⟨78299, by rfl⟩) R156599
theorem R104429 : Reach 104429 := rs (se 3 (by rfl) ⟨19580, by rfl⟩) R39161
theorem R71705 : Reach 71705 := rs (se 2 (by rfl) ⟨26889, by rfl⟩) R53779
theorem R71891 : Reach 71891 := rs (se 1 (by rfl) ⟨53918, by rfl⟩) R107837
theorem R104915 : Reach 104915 := rs (se 1 (by rfl) ⟨78686, by rfl⟩) R157373
theorem R72161 : Reach 72161 := rs (se 2 (by rfl) ⟨27060, by rfl⟩) R54121
theorem R72211 : Reach 72211 := rs (se 1 (by rfl) ⟨54158, by rfl⟩) R108317
theorem R105067 : Reach 105067 := rs (se 1 (by rfl) ⟨78800, by rfl⟩) R157601
theorem R105371 : Reach 105371 := rs (se 1 (by rfl) ⟨79028, by rfl⟩) R158057
theorem R269243 : Reach 269243 := rs (se 1 (by rfl) ⟨201932, by rfl⟩) R403865
theorem R498635 : Reach 498635 := rs (se 1 (by rfl) ⟨373976, by rfl⟩) R747953
theorem R400403 : Reach 400403 := rs (se 1 (by rfl) ⟨300302, by rfl⟩) R600605
theorem R138833 : Reach 138833 := rs (se 2 (by rfl) ⟨52062, by rfl⟩) R104125
theorem R40745 : Reach 40745 := rs (se 2 (by rfl) ⟨15279, by rfl⟩) R30559
theorem R40751 : Reach 40751 := rs (se 1 (by rfl) ⟨30563, by rfl⟩) R61127
theorem R106555 : Reach 106555 := rs (se 1 (by rfl) ⟨79916, by rfl⟩) R159833
theorem R467153 : Reach 467153 := rs (se 2 (by rfl) ⟨175182, by rfl⟩) R350365
theorem R41225 : Reach 41225 := rs (se 2 (by rfl) ⟨15459, by rfl⟩) R30919
theorem R73993 : Reach 73993 := rs (se 2 (by rfl) ⟨27747, by rfl⟩) R55495
theorem R270641 : Reach 270641 := rs (se 2 (by rfl) ⟨101490, by rfl⟩) R202981
theorem R106859 : Reach 106859 := rs (se 1 (by rfl) ⟨80144, by rfl⟩) R160289
theorem R41327 : Reach 41327 := rs (se 1 (by rfl) ⟨30995, by rfl⟩) R61991
theorem R107027 : Reach 107027 := rs (se 1 (by rfl) ⟨80270, by rfl⟩) R160541
theorem R41543 : Reach 41543 := rs (se 1 (by rfl) ⟨31157, by rfl⟩) R62315
theorem R41579 : Reach 41579 := rs (se 1 (by rfl) ⟨31184, by rfl⟩) R62369
theorem R107129 : Reach 107129 := rs (se 2 (by rfl) ⟨40173, by rfl⟩) R80347
theorem R402149 : Reach 402149 := rs (se 4 (by rfl) ⟨37701, by rfl⟩) R75403
theorem R41807 : Reach 41807 := rs (se 1 (by rfl) ⟨31355, by rfl⟩) R62711
theorem R74621 : Reach 74621 := rs (se 3 (by rfl) ⟨13991, by rfl⟩) R27983
theorem R42203 : Reach 42203 := rs (se 1 (by rfl) ⟨31652, by rfl⟩) R63305
theorem R42377 : Reach 42377 := rs (se 2 (by rfl) ⟨15891, by rfl⟩) R31783
theorem R75451 : Reach 75451 := rs (se 1 (by rfl) ⟨56588, by rfl⟩) R113177
theorem R42731 : Reach 42731 := rs (se 1 (by rfl) ⟨32048, by rfl⟩) R64097
theorem R141263 : Reach 141263 := rs (se 1 (by rfl) ⟨105947, by rfl⟩) R211895
theorem R42959 : Reach 42959 := rs (se 1 (by rfl) ⟨32219, by rfl⟩) R64439
theorem R43355 : Reach 43355 := rs (se 1 (by rfl) ⟨32516, by rfl⟩) R65033
theorem R108983 : Reach 108983 := rs (se 1 (by rfl) ⟨81737, by rfl⟩) R163475
theorem R43583 : Reach 43583 := rs (se 1 (by rfl) ⟨32687, by rfl⟩) R65375
theorem R43703 : Reach 43703 := rs (se 1 (by rfl) ⟨32777, by rfl⟩) R65555
theorem R76535 : Reach 76535 := rs (se 1 (by rfl) ⟨57401, by rfl⟩) R114803
theorem R404291 : Reach 404291 := rs (se 1 (by rfl) ⟨303218, by rfl⟩) R606437
theorem R142235 : Reach 142235 := rs (se 1 (by rfl) ⟨106676, by rfl⟩) R213353
theorem R43931 : Reach 43931 := rs (se 1 (by rfl) ⟨32948, by rfl⟩) R65897
theorem R1387651 : Reach 1387651 := rs (se 1 (by rfl) ⟨1040738, by rfl⟩) R2081477
theorem R44327 : Reach 44327 := rs (se 1 (by rfl) ⟨33245, by rfl⟩) R66491
theorem R241015 : Reach 241015 := rs (se 1 (by rfl) ⟨180761, by rfl⟩) R361523
theorem R109943 : Reach 109943 := rs (se 1 (by rfl) ⟨82457, by rfl⟩) R164915
theorem R44411 : Reach 44411 := rs (se 1 (by rfl) ⟨33308, by rfl⟩) R66617
theorem R142721 : Reach 142721 := rs (se 2 (by rfl) ⟨53520, by rfl⟩) R107041
theorem R44537 : Reach 44537 := rs (se 2 (by rfl) ⟨16701, by rfl⟩) R33403
theorem R77395 : Reach 77395 := rs (se 1 (by rfl) ⟨58046, by rfl⟩) R116093
theorem R44639 : Reach 44639 := rs (se 1 (by rfl) ⟨33479, by rfl⟩) R66959
theorem R208493 : Reach 208493 := rs (se 3 (by rfl) ⟨39092, by rfl⟩) R78185
theorem R143111 : Reach 143111 := rs (se 1 (by rfl) ⟨107333, by rfl⟩) R214667
theorem R44807 : Reach 44807 := rs (se 1 (by rfl) ⟨33605, by rfl⟩) R67211
theorem R44855 : Reach 44855 := rs (se 1 (by rfl) ⟨33641, by rfl⟩) R67283
theorem R143369 : Reach 143369 := rs (se 2 (by rfl) ⟨53763, by rfl⟩) R107527
theorem R45161 : Reach 45161 := rs (se 2 (by rfl) ⟨16935, by rfl⟩) R33871
theorem R143531 : Reach 143531 := rs (se 1 (by rfl) ⟨107648, by rfl⟩) R215297
theorem R45479 : Reach 45479 := rs (se 1 (by rfl) ⟨34109, by rfl⟩) R68219
theorem R45563 : Reach 45563 := rs (se 1 (by rfl) ⟨34172, by rfl⟩) R68345
theorem R45641 : Reach 45641 := rs (se 2 (by rfl) ⟨17115, by rfl⟩) R34231
theorem R176737 : Reach 176737 := rs (se 2 (by rfl) ⟨66276, by rfl⟩) R132553
theorem R45689 : Reach 45689 := rs (se 2 (by rfl) ⟨17133, by rfl⟩) R34267
theorem R144017 : Reach 144017 := rs (se 2 (by rfl) ⟨54006, by rfl⟩) R108013
theorem R45743 : Reach 45743 := rs (se 1 (by rfl) ⟨34307, by rfl⟩) R68615
theorem R45791 : Reach 45791 := rs (se 1 (by rfl) ⟨34343, by rfl⟩) R68687
theorem R78671 : Reach 78671 := rs (se 1 (by rfl) ⟨59003, by rfl⟩) R118007
theorem R45995 : Reach 45995 := rs (se 1 (by rfl) ⟨34496, by rfl⟩) R68993
theorem R46055 : Reach 46055 := rs (se 1 (by rfl) ⟨34541, by rfl⟩) R69083
theorem R78823 : Reach 78823 := rs (se 1 (by rfl) ⟨59117, by rfl⟩) R118235
theorem R46223 : Reach 46223 := rs (se 1 (by rfl) ⟨34667, by rfl⟩) R69335
theorem R46313 : Reach 46313 := rs (se 2 (by rfl) ⟨17367, by rfl⟩) R34735
theorem R46367 : Reach 46367 := rs (se 1 (by rfl) ⟨34775, by rfl⟩) R69551
theorem R46459 : Reach 46459 := rs (se 1 (by rfl) ⟨34844, by rfl⟩) R69689
theorem R46535 : Reach 46535 := rs (se 1 (by rfl) ⟨34901, by rfl⟩) R69803
theorem R47209 : Reach 47209 := rs (se 2 (by rfl) ⟨17703, by rfl⟩) R35407
theorem R112921 : Reach 112921 := rs (se 2 (by rfl) ⟨42345, by rfl⟩) R84691
theorem R113147 : Reach 113147 := rs (se 1 (by rfl) ⟨84860, by rfl⟩) R169721
theorem R80783 : Reach 80783 := rs (se 1 (by rfl) ⟨60587, by rfl⟩) R121175
theorem R474011 : Reach 474011 := rs (se 1 (by rfl) ⟨355508, by rfl⟩) R711017
theorem R539635 : Reach 539635 := rs (se 1 (by rfl) ⟨404726, by rfl⟩) R809453
theorem R146447 : Reach 146447 := rs (se 1 (by rfl) ⟨109835, by rfl⟩) R219671
theorem R113987 : Reach 113987 := rs (se 1 (by rfl) ⟨85490, by rfl⟩) R170981
theorem R114119 : Reach 114119 := rs (se 1 (by rfl) ⟨85589, by rfl⟩) R171179
theorem R81569 : Reach 81569 := rs (se 2 (by rfl) ⟨30588, by rfl⟩) R61177
theorem R147203 : Reach 147203 := rs (se 1 (by rfl) ⟨110402, by rfl⟩) R220805
theorem R48937 : Reach 48937 := rs (se 2 (by rfl) ⟨18351, by rfl⟩) R36703
theorem R147257 : Reach 147257 := rs (se 2 (by rfl) ⟨55221, by rfl⟩) R110443
theorem R49103 : Reach 49103 := rs (se 1 (by rfl) ⟨36827, by rfl⟩) R73655
theorem R49619 : Reach 49619 := rs (se 1 (by rfl) ⟨37214, by rfl⟩) R74429
theorem R180737 : Reach 180737 := rs (se 2 (by rfl) ⟨67776, by rfl⟩) R135553
theorem R49727 : Reach 49727 := rs (se 1 (by rfl) ⟨37295, by rfl⟩) R74591
theorem R574087 : Reach 574087 := rs (se 1 (by rfl) ⟨430565, by rfl⟩) R861131
theorem R312011 : Reach 312011 := rs (se 1 (by rfl) ⟨234008, by rfl⟩) R468017
theorem R148625 : Reach 148625 := rs (se 2 (by rfl) ⟨55734, by rfl⟩) R111469
theorem R50395 : Reach 50395 := rs (se 1 (by rfl) ⟨37796, by rfl⟩) R75593
theorem R116063 : Reach 116063 := rs (se 1 (by rfl) ⟨87047, by rfl⟩) R174095
theorem R280253 : Reach 280253 := rs (se 3 (by rfl) ⟨52547, by rfl⟩) R105095
theorem R83767 : Reach 83767 := rs (se 1 (by rfl) ⟨62825, by rfl⟩) R125651
theorem R345991 : Reach 345991 := rs (se 1 (by rfl) ⟨259493, by rfl⟩) R518987
theorem R51151 : Reach 51151 := rs (se 1 (by rfl) ⟨38363, by rfl⟩) R76727
theorem R379073 : Reach 379073 := rs (se 2 (by rfl) ⟨142152, by rfl⟩) R284305
theorem R150011 : Reach 150011 := rs (se 1 (by rfl) ⟨112508, by rfl⟩) R225017
theorem R51833 : Reach 51833 := rs (se 2 (by rfl) ⟨19437, by rfl⟩) R38875
theorem R84655 : Reach 84655 := rs (se 1 (by rfl) ⟨63491, by rfl⟩) R126983
theorem R51887 : Reach 51887 := rs (se 1 (by rfl) ⟨38915, by rfl⟩) R77831
theorem R445175 : Reach 445175 := rs (se 1 (by rfl) ⟨333881, by rfl⟩) R667763
theorem R52123 : Reach 52123 := rs (se 1 (by rfl) ⟨39092, by rfl⟩) R78185
theorem R52139 : Reach 52139 := rs (se 1 (by rfl) ⟨39104, by rfl⟩) R78209
theorem R216103 : Reach 216103 := rs (se 1 (by rfl) ⟨162077, by rfl⟩) R324155
theorem R609551 : Reach 609551 := rs (se 1 (by rfl) ⟨457163, by rfl⟩) R914327
theorem R150983 : Reach 150983 := rs (se 1 (by rfl) ⟨113237, by rfl⟩) R226475
theorem R118265 : Reach 118265 := rs (se 2 (by rfl) ⟨44349, by rfl⟩) R88699
theorem R151307 : Reach 151307 := rs (se 1 (by rfl) ⟨113480, by rfl⟩) R226961
theorem R511757 : Reach 511757 := rs (se 3 (by rfl) ⟨95954, by rfl⟩) R191909
theorem R53513 : Reach 53513 := rs (se 2 (by rfl) ⟨20067, by rfl⟩) R40135
theorem R152027 : Reach 152027 := rs (se 1 (by rfl) ⟨114020, by rfl⟩) R228041
theorem R1102325 : Reach 1102325 := rs (se 5 (by rfl) ⟨51671, by rfl⟩) R103343
theorem R152279 : Reach 152279 := rs (se 1 (by rfl) ⟨114209, by rfl⟩) R228419
theorem R119713 : Reach 119713 := rs (se 2 (by rfl) ⟨44892, by rfl⟩) R89785
theorem R250937 : Reach 250937 := rs (se 2 (by rfl) ⟨94101, by rfl⟩) R188203
theorem R382201 : Reach 382201 := rs (se 2 (by rfl) ⟨143325, by rfl⟩) R286651
theorem R349433 : Reach 349433 := rs (se 2 (by rfl) ⟨131037, by rfl⟩) R262075
theorem R152927 : Reach 152927 := rs (se 1 (by rfl) ⟨114695, by rfl⟩) R229391
theorem R907057 : Reach 907057 := rs (se 2 (by rfl) ⟨340146, by rfl⟩) R680293
theorem R88199 : Reach 88199 := rs (se 1 (by rfl) ⟨66149, by rfl⟩) R132299
theorem R55561 : Reach 55561 := rs (se 2 (by rfl) ⟨20835, by rfl⟩) R41671
theorem R154487 : Reach 154487 := rs (se 1 (by rfl) ⟨115865, by rfl⟩) R231731
theorem R89075 : Reach 89075 := rs (se 1 (by rfl) ⟨66806, by rfl⟩) R133613
theorem R155195 : Reach 155195 := rs (se 1 (by rfl) ⟨116396, by rfl⟩) R232793
theorem R319697 : Reach 319697 := rs (se 2 (by rfl) ⟨119886, by rfl⟩) R239773
theorem R516611 : Reach 516611 := rs (se 1 (by rfl) ⟨387458, by rfl⟩) R774917
theorem R156815 : Reach 156815 := rs (se 1 (by rfl) ⟨117611, by rfl⟩) R235223
theorem R451889 : Reach 451889 := rs (se 2 (by rfl) ⟨169458, by rfl⟩) R338917
theorem R222551 : Reach 222551 := rs (se 1 (by rfl) ⟨166913, by rfl⟩) R333827
theorem R222587 : Reach 222587 := rs (se 1 (by rfl) ⟨166940, by rfl⟩) R333881
theorem R452429 : Reach 452429 := rs (se 3 (by rfl) ⟨84830, by rfl⟩) R169661
theorem R92009 : Reach 92009 := rs (se 2 (by rfl) ⟨34503, by rfl⟩) R69007
theorem R157949 : Reach 157949 := rs (se 3 (by rfl) ⟨29615, by rfl⟩) R59231
theorem R125327 : Reach 125327 := rs (se 1 (by rfl) ⟨93995, by rfl⟩) R187991
theorem R27131 : Reach 27131 := rs (se 1 (by rfl) ⟨20348, by rfl⟩) R40697
theorem R125479 : Reach 125479 := rs (se 1 (by rfl) ⟨94109, by rfl⟩) R188219
theorem R27199 : Reach 27199 := rs (se 1 (by rfl) ⟨20399, by rfl⟩) R40799
theorem R27207 : Reach 27207 := rs (se 1 (by rfl) ⟨20405, by rfl⟩) R40811
theorem R289403 : Reach 289403 := rs (se 1 (by rfl) ⟨217052, by rfl⟩) R434105
theorem R27359 : Reach 27359 := rs (se 1 (by rfl) ⟨20519, by rfl⟩) R41039
theorem R27439 : Reach 27439 := rs (se 1 (by rfl) ⟨20579, by rfl⟩) R41159
theorem R27547 : Reach 27547 := rs (se 1 (by rfl) ⟨20660, by rfl⟩) R41321
theorem R27599 : Reach 27599 := rs (se 1 (by rfl) ⟨20699, by rfl⟩) R41399
theorem R27623 : Reach 27623 := rs (se 1 (by rfl) ⟨20717, by rfl⟩) R41435
theorem R27935 : Reach 27935 := rs (se 1 (by rfl) ⟨20951, by rfl⟩) R41903
theorem R27995 : Reach 27995 := rs (se 1 (by rfl) ⟨20996, by rfl⟩) R41993
theorem R28015 : Reach 28015 := rs (se 1 (by rfl) ⟨21011, by rfl⟩) R42023
theorem R28071 : Reach 28071 := rs (se 1 (by rfl) ⟨21053, by rfl⟩) R42107
theorem R93689 : Reach 93689 := rs (se 2 (by rfl) ⟨35133, by rfl⟩) R70267
theorem R28155 : Reach 28155 := rs (se 1 (by rfl) ⟨21116, by rfl⟩) R42233
theorem R28223 : Reach 28223 := rs (se 1 (by rfl) ⟨21167, by rfl⟩) R42335
theorem R28231 : Reach 28231 := rs (se 1 (by rfl) ⟨21173, by rfl⟩) R42347
theorem R2289239 : Reach 2289239 := rs (se 1 (by rfl) ⟨1716929, by rfl⟩) R3433859
theorem R93791 : Reach 93791 := rs (se 1 (by rfl) ⟨70343, by rfl⟩) R140687
theorem R28383 : Reach 28383 := rs (se 1 (by rfl) ⟨21287, by rfl⟩) R42575
theorem R61163 : Reach 61163 := rs (se 1 (by rfl) ⟨45872, by rfl⟩) R91745
theorem R93959 : Reach 93959 := rs (se 1 (by rfl) ⟨70469, by rfl⟩) R140939
theorem R28463 : Reach 28463 := rs (se 1 (by rfl) ⟨21347, by rfl⟩) R42695
theorem R94013 : Reach 94013 := rs (se 3 (by rfl) ⟨17627, by rfl⟩) R35255
theorem R61289 : Reach 61289 := rs (se 2 (by rfl) ⟨22983, by rfl⟩) R45967
theorem R28571 : Reach 28571 := rs (se 1 (by rfl) ⟨21428, by rfl⟩) R42857
theorem R28623 : Reach 28623 := rs (se 1 (by rfl) ⟨21467, by rfl⟩) R42935
theorem R61391 : Reach 61391 := rs (se 1 (by rfl) ⟨46043, by rfl⟩) R92087
theorem R28647 : Reach 28647 := rs (se 1 (by rfl) ⟨21485, by rfl⟩) R42971
theorem R28891 : Reach 28891 := rs (se 1 (by rfl) ⟨21668, by rfl⟩) R43337
theorem R1208591 : Reach 1208591 := rs (se 1 (by rfl) ⟨906443, by rfl⟩) R1812887
theorem R28959 : Reach 28959 := rs (se 1 (by rfl) ⟨21719, by rfl⟩) R43439
theorem R28967 : Reach 28967 := rs (se 1 (by rfl) ⟨21725, by rfl⟩) R43451
theorem R29019 : Reach 29019 := rs (se 1 (by rfl) ⟨21764, by rfl⟩) R43529
theorem R29039 : Reach 29039 := rs (se 1 (by rfl) ⟨21779, by rfl⟩) R43559
theorem R29051 : Reach 29051 := rs (se 1 (by rfl) ⟨21788, by rfl⟩) R43577
theorem R29095 : Reach 29095 := rs (se 1 (by rfl) ⟨21821, by rfl⟩) R43643
theorem R29127 : Reach 29127 := rs (se 1 (by rfl) ⟨21845, by rfl⟩) R43691
theorem R29179 : Reach 29179 := rs (se 1 (by rfl) ⟨21884, by rfl⟩) R43769
theorem R29247 : Reach 29247 := rs (se 1 (by rfl) ⟨21935, by rfl⟩) R43871
theorem R29255 : Reach 29255 := rs (se 1 (by rfl) ⟨21941, by rfl⟩) R43883
theorem R29279 : Reach 29279 := rs (se 1 (by rfl) ⟨21959, by rfl⟩) R43919
theorem R29359 : Reach 29359 := rs (se 1 (by rfl) ⟨22019, by rfl⟩) R44039
theorem R62135 : Reach 62135 := rs (se 1 (by rfl) ⟨46601, by rfl⟩) R93203
theorem R29407 : Reach 29407 := rs (se 1 (by rfl) ⟨22055, by rfl⟩) R44111
theorem R29487 : Reach 29487 := rs (se 1 (by rfl) ⟨22115, by rfl⟩) R44231
theorem R29519 : Reach 29519 := rs (se 1 (by rfl) ⟨22139, by rfl⟩) R44279
theorem R62351 : Reach 62351 := rs (se 1 (by rfl) ⟨46763, by rfl⟩) R93527
theorem R29595 : Reach 29595 := rs (se 1 (by rfl) ⟨22196, by rfl⟩) R44393
theorem R29647 : Reach 29647 := rs (se 1 (by rfl) ⟨22235, by rfl⟩) R44471
theorem R29671 : Reach 29671 := rs (se 1 (by rfl) ⟨22253, by rfl⟩) R44507
theorem R95431 : Reach 95431 := rs (se 1 (by rfl) ⟨71573, by rfl⟩) R143147
theorem R29915 : Reach 29915 := rs (se 1 (by rfl) ⟨22436, by rfl⟩) R44873
theorem R128249 : Reach 128249 := rs (se 2 (by rfl) ⟨48093, by rfl⟩) R96187
theorem R29983 : Reach 29983 := rs (se 1 (by rfl) ⟨22487, by rfl⟩) R44975
theorem R29991 : Reach 29991 := rs (se 1 (by rfl) ⟨22493, by rfl⟩) R44987
theorem R30043 : Reach 30043 := rs (se 1 (by rfl) ⟨22532, by rfl⟩) R45065
theorem R259433 : Reach 259433 := rs (se 2 (by rfl) ⟨97287, by rfl⟩) R194575
theorem R30063 : Reach 30063 := rs (se 1 (by rfl) ⟨22547, by rfl⟩) R45095
theorem R30075 : Reach 30075 := rs (se 1 (by rfl) ⟨22556, by rfl⟩) R45113
theorem R30119 : Reach 30119 := rs (se 1 (by rfl) ⟨22589, by rfl⟩) R45179
theorem R30151 : Reach 30151 := rs (se 1 (by rfl) ⟨22613, by rfl⟩) R45227
theorem R30203 : Reach 30203 := rs (se 1 (by rfl) ⟨22652, by rfl⟩) R45305
theorem R30271 : Reach 30271 := rs (se 1 (by rfl) ⟨22703, by rfl⟩) R45407
theorem R30279 : Reach 30279 := rs (se 1 (by rfl) ⟨22709, by rfl⟩) R45419
theorem R63071 : Reach 63071 := rs (se 1 (by rfl) ⟨47303, by rfl⟩) R94607
theorem R30303 : Reach 30303 := rs (se 1 (by rfl) ⟨22727, by rfl⟩) R45455
theorem R30383 : Reach 30383 := rs (se 1 (by rfl) ⟨22787, by rfl⟩) R45575
theorem R30431 : Reach 30431 := rs (se 1 (by rfl) ⟨22823, by rfl⟩) R45647
theorem R30511 : Reach 30511 := rs (se 1 (by rfl) ⟨22883, by rfl⟩) R45767
theorem R63287 : Reach 63287 := rs (se 1 (by rfl) ⟨47465, by rfl⟩) R94931
theorem R30543 : Reach 30543 := rs (se 1 (by rfl) ⟨22907, by rfl⟩) R45815
theorem R30619 : Reach 30619 := rs (se 1 (by rfl) ⟨22964, by rfl⟩) R45929
theorem R30671 : Reach 30671 := rs (se 1 (by rfl) ⟨23003, by rfl⟩) R46007
theorem R30695 : Reach 30695 := rs (se 1 (by rfl) ⟨23021, by rfl⟩) R46043
theorem R63593 : Reach 63593 := rs (se 2 (by rfl) ⟨23847, by rfl⟩) R47695
theorem R30939 : Reach 30939 := rs (se 1 (by rfl) ⟨23204, by rfl⟩) R46409
theorem R31007 : Reach 31007 := rs (se 1 (by rfl) ⟨23255, by rfl⟩) R46511
theorem R31015 : Reach 31015 := rs (se 1 (by rfl) ⟨23261, by rfl⟩) R46523
theorem R31067 : Reach 31067 := rs (se 1 (by rfl) ⟨23300, by rfl⟩) R46601
theorem R96623 : Reach 96623 := rs (se 1 (by rfl) ⟨72467, by rfl⟩) R144935
theorem R31087 : Reach 31087 := rs (se 1 (by rfl) ⟨23315, by rfl⟩) R46631
theorem R31099 : Reach 31099 := rs (se 1 (by rfl) ⟨23324, by rfl⟩) R46649
theorem R63919 : Reach 63919 := rs (se 1 (by rfl) ⟨47939, by rfl⟩) R95879
theorem R2587085 : Reach 2587085 := rs (se 3 (by rfl) ⟨485078, by rfl⟩) R970157
theorem R64073 : Reach 64073 := rs (se 2 (by rfl) ⟨24027, by rfl⟩) R48055
theorem R64079 : Reach 64079 := rs (se 1 (by rfl) ⟨48059, by rfl⟩) R96119
theorem R96875 : Reach 96875 := rs (se 1 (by rfl) ⟨72656, by rfl⟩) R145313
theorem R64223 : Reach 64223 := rs (se 1 (by rfl) ⟨48167, by rfl⟩) R96335
theorem R31567 : Reach 31567 := rs (se 1 (by rfl) ⟨23675, by rfl⟩) R47351
theorem R64475 : Reach 64475 := rs (se 1 (by rfl) ⟨48356, by rfl⟩) R96713
theorem R1276901 : Reach 1276901 := rs (se 4 (by rfl) ⟨119709, by rfl⟩) R239419
theorem R64655 : Reach 64655 := rs (se 1 (by rfl) ⟨48491, by rfl⟩) R96983
theorem R97469 : Reach 97469 := rs (se 3 (by rfl) ⟨18275, by rfl⟩) R36551
theorem R64727 : Reach 64727 := rs (se 1 (by rfl) ⟨48545, by rfl⟩) R97091
theorem R31963 : Reach 31963 := rs (se 1 (by rfl) ⟨23972, by rfl⟩) R47945
theorem R64745 : Reach 64745 := rs (se 2 (by rfl) ⟨24279, by rfl⟩) R48559
theorem R64799 : Reach 64799 := rs (se 1 (by rfl) ⟨48599, by rfl⟩) R97199
theorem R64907 : Reach 64907 := rs (se 1 (by rfl) ⟨48680, by rfl⟩) R97361
theorem R32251 : Reach 32251 := rs (se 1 (by rfl) ⟨24188, by rfl⟩) R48377
theorem R97901 : Reach 97901 := rs (se 3 (by rfl) ⟨18356, by rfl⟩) R36713
theorem R32431 : Reach 32431 := rs (se 1 (by rfl) ⟨24323, by rfl⟩) R48647
theorem R65321 : Reach 65321 := rs (se 2 (by rfl) ⟨24495, by rfl⟩) R48991
theorem R294785 : Reach 294785 := rs (se 2 (by rfl) ⟨110544, by rfl⟩) R221089
theorem R32719 : Reach 32719 := rs (se 1 (by rfl) ⟨24539, by rfl⟩) R49079
theorem R33079 : Reach 33079 := rs (se 1 (by rfl) ⟨24809, by rfl⟩) R49619
theorem R98657 : Reach 98657 := rs (se 2 (by rfl) ⟨36996, by rfl⟩) R73993
theorem R33151 : Reach 33151 := rs (se 1 (by rfl) ⟨24863, by rfl⟩) R49727
theorem R393943 : Reach 393943 := rs (se 1 (by rfl) ⟨295457, by rfl⟩) R590915
theorem R99083 : Reach 99083 := rs (se 1 (by rfl) ⟨74312, by rfl⟩) R148625
theorem R721709 : Reach 721709 := rs (se 3 (by rfl) ⟨135320, by rfl⟩) R270641
theorem R197423 : Reach 197423 := rs (se 1 (by rfl) ⟨148067, by rfl⟩) R296135
theorem R66415 : Reach 66415 := rs (se 1 (by rfl) ⟨49811, by rfl⟩) R99623
theorem R66923 : Reach 66923 := rs (se 1 (by rfl) ⟨50192, by rfl⟩) R100385
theorem R67193 : Reach 67193 := rs (se 2 (by rfl) ⟨25197, by rfl⟩) R50395
theorem R100007 : Reach 100007 := rs (se 1 (by rfl) ⟨75005, by rfl⟩) R150011
theorem R34555 : Reach 34555 := rs (se 1 (by rfl) ⟨25916, by rfl⟩) R51833
theorem R34591 : Reach 34591 := rs (se 1 (by rfl) ⟨25943, by rfl⟩) R51887
theorem R296783 : Reach 296783 := rs (se 1 (by rfl) ⟨222587, by rfl⟩) R445175
theorem R34759 : Reach 34759 := rs (se 1 (by rfl) ⟨26069, by rfl⟩) R52139
theorem R100601 : Reach 100601 := rs (se 2 (by rfl) ⟨37725, by rfl⟩) R75451
theorem R100655 : Reach 100655 := rs (se 1 (by rfl) ⟨75491, by rfl⟩) R150983
theorem R100871 : Reach 100871 := rs (se 1 (by rfl) ⟨75653, by rfl⟩) R151307
theorem R461321 : Reach 461321 := rs (se 2 (by rfl) ⟨172995, by rfl⟩) R345991
theorem R68201 : Reach 68201 := rs (se 2 (by rfl) ⟨25575, by rfl⟩) R51151
theorem R35675 : Reach 35675 := rs (se 1 (by rfl) ⟨26756, by rfl⟩) R53513
theorem R101351 : Reach 101351 := rs (se 1 (by rfl) ⟨76013, by rfl⟩) R152027
theorem R101519 : Reach 101519 := rs (se 1 (by rfl) ⟨76139, by rfl⟩) R152279
theorem R68831 : Reach 68831 := rs (se 1 (by rfl) ⟨51623, by rfl⟩) R103247
theorem R167291 : Reach 167291 := rs (se 1 (by rfl) ⟨125468, by rfl⟩) R250937
theorem R167305 : Reach 167305 := rs (se 2 (by rfl) ⟨62739, by rfl⟩) R125479
theorem R69047 : Reach 69047 := rs (se 1 (by rfl) ⟨51785, by rfl⟩) R103571
theorem R232955 : Reach 232955 := rs (se 1 (by rfl) ⟨174716, by rfl⟩) R349433
theorem R101951 : Reach 101951 := rs (se 1 (by rfl) ⟨76463, by rfl⟩) R152927
theorem R69227 : Reach 69227 := rs (se 1 (by rfl) ⟨51920, by rfl⟩) R103841
theorem R69295 : Reach 69295 := rs (se 1 (by rfl) ⟨51971, by rfl⟩) R103943
theorem R69497 : Reach 69497 := rs (se 2 (by rfl) ⟨26061, by rfl⟩) R52123
theorem R69515 : Reach 69515 := rs (se 1 (by rfl) ⟨52136, by rfl⟩) R104273
theorem R69599 : Reach 69599 := rs (se 1 (by rfl) ⟨52199, by rfl⟩) R104399
theorem R69619 : Reach 69619 := rs (se 1 (by rfl) ⟨52214, by rfl⟩) R104429
theorem R102653 : Reach 102653 := rs (se 3 (by rfl) ⟨19247, by rfl⟩) R38495
theorem R69943 : Reach 69943 := rs (se 1 (by rfl) ⟨52457, by rfl⟩) R104915
theorem R102991 : Reach 102991 := rs (se 1 (by rfl) ⟨77243, by rfl⟩) R154487
theorem R70247 : Reach 70247 := rs (se 1 (by rfl) ⟨52685, by rfl⟩) R105371
theorem R332423 : Reach 332423 := rs (se 1 (by rfl) ⟨249317, by rfl⟩) R498635
theorem R266935 : Reach 266935 := rs (se 1 (by rfl) ⟨200201, by rfl⟩) R400403
theorem R103193 : Reach 103193 := rs (se 2 (by rfl) ⟨38697, by rfl⟩) R77395
theorem R103463 : Reach 103463 := rs (se 1 (by rfl) ⟨77597, by rfl⟩) R155195
theorem R71239 : Reach 71239 := rs (se 1 (by rfl) ⟨53429, by rfl⟩) R106859
theorem R71351 : Reach 71351 := rs (se 1 (by rfl) ⟨53513, by rfl⟩) R107027
theorem R104543 : Reach 104543 := rs (se 1 (by rfl) ⟨78407, by rfl⟩) R156815
theorem R235649 : Reach 235649 := rs (se 2 (by rfl) ⟨88368, by rfl⟩) R176737
theorem R301259 : Reach 301259 := rs (se 1 (by rfl) ⟨225944, by rfl⟩) R451889
theorem R301619 : Reach 301619 := rs (se 1 (by rfl) ⟨226214, by rfl⟩) R452429
theorem R2038405 : Reach 2038405 := rs (se 4 (by rfl) ⟨191100, by rfl⟩) R382201
theorem R105097 : Reach 105097 := rs (se 2 (by rfl) ⟨39411, by rfl⟩) R78823
theorem R105299 : Reach 105299 := rs (se 1 (by rfl) ⟨78974, by rfl⟩) R157949
theorem R138185 : Reach 138185 := rs (se 2 (by rfl) ⟨51819, by rfl⟩) R103639
theorem R73295 : Reach 73295 := rs (se 1 (by rfl) ⟨54971, by rfl⟩) R109943
theorem R138995 : Reach 138995 := rs (se 1 (by rfl) ⟨104246, by rfl⟩) R208493
theorem R40775 : Reach 40775 := rs (se 1 (by rfl) ⟨30581, by rfl⟩) R61163
theorem R40859 : Reach 40859 := rs (se 1 (by rfl) ⟨30644, by rfl⟩) R61289
theorem R40927 : Reach 40927 := rs (se 1 (by rfl) ⟨30695, by rfl⟩) R61391
theorem R74081 : Reach 74081 := rs (se 2 (by rfl) ⟨27780, by rfl⟩) R55561
theorem R41423 : Reach 41423 := rs (se 1 (by rfl) ⟨31067, by rfl⟩) R62135
theorem R41465 : Reach 41465 := rs (se 2 (by rfl) ⟨15549, by rfl⟩) R31099
theorem R41567 : Reach 41567 := rs (se 1 (by rfl) ⟨31175, by rfl⟩) R62351
theorem R140089 : Reach 140089 := rs (se 2 (by rfl) ⟨52533, by rfl⟩) R105067
theorem R172955 : Reach 172955 := rs (se 1 (by rfl) ⟨129716, by rfl⟩) R259433
theorem R42047 : Reach 42047 := rs (se 1 (by rfl) ⟨31535, by rfl⟩) R63071
theorem R42089 : Reach 42089 := rs (se 2 (by rfl) ⟨15783, by rfl⟩) R31567
theorem R42191 : Reach 42191 := rs (se 1 (by rfl) ⟨31643, by rfl⟩) R63287
theorem R42395 : Reach 42395 := rs (se 1 (by rfl) ⟨31796, by rfl⟩) R63593
theorem R42617 : Reach 42617 := rs (se 2 (by rfl) ⟨15981, by rfl⟩) R31963
theorem R75431 : Reach 75431 := rs (se 1 (by rfl) ⟨56573, by rfl⟩) R113147
theorem R42715 : Reach 42715 := rs (se 1 (by rfl) ⟨32036, by rfl⟩) R64073
theorem R42719 : Reach 42719 := rs (se 1 (by rfl) ⟨32039, by rfl⟩) R64079
theorem R42815 : Reach 42815 := rs (se 1 (by rfl) ⟨32111, by rfl⟩) R64223
theorem R42983 : Reach 42983 := rs (se 1 (by rfl) ⟨32237, by rfl⟩) R64475
theorem R43001 : Reach 43001 := rs (se 2 (by rfl) ⟨16125, by rfl⟩) R32251
theorem R43103 : Reach 43103 := rs (se 1 (by rfl) ⟨32327, by rfl⟩) R64655
theorem R43151 : Reach 43151 := rs (se 1 (by rfl) ⟨32363, by rfl⟩) R64727
theorem R43163 : Reach 43163 := rs (se 1 (by rfl) ⟨32372, by rfl⟩) R64745
theorem R43199 : Reach 43199 := rs (se 1 (by rfl) ⟨32399, by rfl⟩) R64799
theorem R75991 : Reach 75991 := rs (se 1 (by rfl) ⟨56993, by rfl⟩) R113987
theorem R43241 : Reach 43241 := rs (se 2 (by rfl) ⟨16215, by rfl⟩) R32431
theorem R43271 : Reach 43271 := rs (se 1 (by rfl) ⟨32453, by rfl⟩) R64907
theorem R76079 : Reach 76079 := rs (se 1 (by rfl) ⟨57059, by rfl⟩) R114119
theorem R43547 : Reach 43547 := rs (se 1 (by rfl) ⟨32660, by rfl⟩) R65321
theorem R43625 : Reach 43625 := rs (se 2 (by rfl) ⟨16359, by rfl⟩) R32719
theorem R142073 : Reach 142073 := rs (se 2 (by rfl) ⟨53277, by rfl⟩) R106555
theorem R43831 : Reach 43831 := rs (se 1 (by rfl) ⟨32873, by rfl⟩) R65747
theorem R44153 : Reach 44153 := rs (se 2 (by rfl) ⟨16557, by rfl⟩) R33115
theorem R208007 : Reach 208007 := rs (se 1 (by rfl) ⟨156005, by rfl⟩) R312011
theorem R44255 : Reach 44255 := rs (se 1 (by rfl) ⟨33191, by rfl⟩) R66383
theorem R44297 : Reach 44297 := rs (se 2 (by rfl) ⟨16611, by rfl⟩) R33223
theorem R44399 : Reach 44399 := rs (se 1 (by rfl) ⟨33299, by rfl⟩) R66599
theorem R44519 : Reach 44519 := rs (se 1 (by rfl) ⟨33389, by rfl⟩) R66779
theorem R765449 : Reach 765449 := rs (se 2 (by rfl) ⟨287043, by rfl⟩) R574087
theorem R77375 : Reach 77375 := rs (se 1 (by rfl) ⟨58031, by rfl⟩) R116063
theorem R44651 : Reach 44651 := rs (se 1 (by rfl) ⟨33488, by rfl⟩) R66977
theorem R44687 : Reach 44687 := rs (se 1 (by rfl) ⟨33515, by rfl⟩) R67031
theorem R44777 : Reach 44777 := rs (se 2 (by rfl) ⟨16791, by rfl⟩) R33583
theorem R44921 : Reach 44921 := rs (se 2 (by rfl) ⟨16845, by rfl⟩) R33691
theorem R45023 : Reach 45023 := rs (se 1 (by rfl) ⟨33767, by rfl⟩) R67535
theorem R602245 : Reach 602245 := rs (se 4 (by rfl) ⟨56460, by rfl⟩) R112921
theorem R45275 : Reach 45275 := rs (se 1 (by rfl) ⟨33956, by rfl⟩) R67913
theorem R45287 : Reach 45287 := rs (se 1 (by rfl) ⟨33965, by rfl⟩) R67931
theorem R110915 : Reach 110915 := rs (se 1 (by rfl) ⟨83186, by rfl⟩) R166373
theorem R45449 : Reach 45449 := rs (se 2 (by rfl) ⟨17043, by rfl⟩) R34087
theorem R45545 : Reach 45545 := rs (se 2 (by rfl) ⟨17079, by rfl⟩) R34159
theorem R45671 : Reach 45671 := rs (se 1 (by rfl) ⟨34253, by rfl⟩) R68507
theorem R45803 : Reach 45803 := rs (se 1 (by rfl) ⟨34352, by rfl⟩) R68705
theorem R45833 : Reach 45833 := rs (se 2 (by rfl) ⟨17187, by rfl⟩) R34375
theorem R45881 : Reach 45881 := rs (se 2 (by rfl) ⟨17205, by rfl⟩) R34411
theorem R406367 : Reach 406367 := rs (se 1 (by rfl) ⟨304775, by rfl⟩) R609551
theorem R45935 : Reach 45935 := rs (se 1 (by rfl) ⟨34451, by rfl⟩) R68903
theorem R46075 : Reach 46075 := rs (se 1 (by rfl) ⟨34556, by rfl⟩) R69113
theorem R111689 : Reach 111689 := rs (se 2 (by rfl) ⟨41883, by rfl⟩) R83767
theorem R46187 : Reach 46187 := rs (se 1 (by rfl) ⟨34640, by rfl⟩) R69281
theorem R341171 : Reach 341171 := rs (se 1 (by rfl) ⟨255878, by rfl⟩) R511757
theorem R46427 : Reach 46427 := rs (se 1 (by rfl) ⟨34820, by rfl⟩) R69641
theorem R46507 : Reach 46507 := rs (se 1 (by rfl) ⟨34880, by rfl⟩) R69761
theorem R833111 : Reach 833111 := rs (se 1 (by rfl) ⟨624833, by rfl⟩) R1249667
theorem R46703 : Reach 46703 := rs (se 1 (by rfl) ⟨35027, by rfl⟩) R70055
theorem R46759 : Reach 46759 := rs (se 1 (by rfl) ⟨35069, by rfl⟩) R70139
theorem R46811 : Reach 46811 := rs (se 1 (by rfl) ⟨35108, by rfl⟩) R70217
theorem R177967 : Reach 177967 := rs (se 1 (by rfl) ⟨133475, by rfl⟩) R266951
theorem R46927 : Reach 46927 := rs (se 1 (by rfl) ⟨35195, by rfl⟩) R70391
theorem R47047 : Reach 47047 := rs (se 1 (by rfl) ⟨35285, by rfl⟩) R70571
theorem R112873 : Reach 112873 := rs (se 2 (by rfl) ⟨42327, by rfl⟩) R84655
theorem R178469 : Reach 178469 := rs (se 4 (by rfl) ⟨16731, by rfl⟩) R33463
theorem R47803 : Reach 47803 := rs (se 1 (by rfl) ⟨35852, by rfl⟩) R71705
theorem R277181 : Reach 277181 := rs (se 3 (by rfl) ⟨51971, by rfl⟩) R103943
theorem R47927 : Reach 47927 := rs (se 1 (by rfl) ⟨35945, by rfl⟩) R71891
theorem R1850201 : Reach 1850201 := rs (se 2 (by rfl) ⟨693825, by rfl⟩) R1387651
theorem R48107 : Reach 48107 := rs (se 1 (by rfl) ⟨36080, by rfl⟩) R72161
theorem R179495 : Reach 179495 := rs (se 1 (by rfl) ⟨134621, by rfl⟩) R269243
theorem R311435 : Reach 311435 := rs (se 1 (by rfl) ⟨233576, by rfl⟩) R467153
theorem R213131 : Reach 213131 := rs (se 1 (by rfl) ⟨159848, by rfl⟩) R319697
theorem R344407 : Reach 344407 := rs (se 1 (by rfl) ⟨258305, by rfl⟩) R516611
theorem R49747 : Reach 49747 := rs (se 1 (by rfl) ⟨37310, by rfl⟩) R74621
theorem R148367 : Reach 148367 := rs (se 1 (by rfl) ⟨111275, by rfl⟩) R222551
theorem R148391 : Reach 148391 := rs (se 1 (by rfl) ⟨111293, by rfl⟩) R222587
theorem R83551 : Reach 83551 := rs (se 1 (by rfl) ⟨62663, by rfl⟩) R125327
theorem R51023 : Reach 51023 := rs (se 1 (by rfl) ⟨38267, by rfl⟩) R76535
theorem R247781 : Reach 247781 := rs (se 4 (by rfl) ⟨23229, by rfl⟩) R46459
theorem R1526159 : Reach 1526159 := rs (se 1 (by rfl) ⟨1144619, by rfl⟩) R2289239
theorem R805727 : Reach 805727 := rs (se 1 (by rfl) ⟨604295, by rfl⟩) R1208591
theorem R52447 : Reach 52447 := rs (se 1 (by rfl) ⟨39335, by rfl⟩) R78671
theorem R85225 : Reach 85225 := rs (se 2 (by rfl) ⟨31959, by rfl⟩) R63919
theorem R85499 : Reach 85499 := rs (se 1 (by rfl) ⟨64124, by rfl⟩) R128249
theorem R184301 : Reach 184301 := rs (se 3 (by rfl) ⟨34556, by rfl⟩) R69113
theorem R315373 : Reach 315373 := rs (se 3 (by rfl) ⟨59132, by rfl⟩) R118265
theorem R4837637 : Reach 4837637 := rs (se 4 (by rfl) ⟨453528, by rfl⟩) R907057
theorem R1724723 : Reach 1724723 := rs (se 1 (by rfl) ⟨1293542, by rfl⟩) R2587085
theorem R53855 : Reach 53855 := rs (se 1 (by rfl) ⟨40391, by rfl⟩) R80783
theorem R316007 : Reach 316007 := rs (se 1 (by rfl) ⟨237005, by rfl⟩) R474011
theorem R54379 : Reach 54379 := rs (se 1 (by rfl) ⟨40784, by rfl⟩) R81569
theorem R120491 : Reach 120491 := rs (se 1 (by rfl) ⟨90368, by rfl⟩) R180737
theorem R153575 : Reach 153575 := rs (se 1 (by rfl) ⟨115181, by rfl⟩) R230363
theorem R121277 : Reach 121277 := rs (se 3 (by rfl) ⟨22739, by rfl⟩) R45479
theorem R186835 : Reach 186835 := rs (se 1 (by rfl) ⟨140126, by rfl⟩) R280253
theorem R481879 : Reach 481879 := rs (se 1 (by rfl) ⟨361409, by rfl⟩) R722819
theorem R2939533 : Reach 2939533 := rs (se 3 (by rfl) ⟨551162, by rfl⟩) R1102325
theorem R252715 : Reach 252715 := rs (se 1 (by rfl) ⟨189536, by rfl⟩) R379073
theorem R285677 : Reach 285677 := rs (se 3 (by rfl) ⟨53564, by rfl⟩) R107129
theorem R1530899 : Reach 1530899 := rs (se 1 (by rfl) ⟨1148174, by rfl⟩) R2296349
theorem R351377 : Reach 351377 := rs (se 2 (by rfl) ⟨131766, by rfl⟩) R263533
theorem R1072397 : Reach 1072397 := rs (se 3 (by rfl) ⟨201074, by rfl⟩) R402149
theorem R89383 : Reach 89383 := rs (se 1 (by rfl) ⟨67037, by rfl⟩) R134075
theorem R91529 : Reach 91529 := rs (se 2 (by rfl) ⟨34323, by rfl⟩) R68647
theorem R288137 : Reach 288137 := rs (se 2 (by rfl) ⟨108051, by rfl⟩) R216103
theorem R58799 : Reach 58799 := rs (se 1 (by rfl) ⟨44099, by rfl⟩) R88199
theorem R91945 : Reach 91945 := rs (se 2 (by rfl) ⟨34479, by rfl⟩) R68959
theorem R321353 : Reach 321353 := rs (se 2 (by rfl) ⟨120507, by rfl⟩) R241015
theorem R59383 : Reach 59383 := rs (se 1 (by rfl) ⟨44537, by rfl⟩) R89075
theorem R92285 : Reach 92285 := rs (se 3 (by rfl) ⟨17303, by rfl⟩) R34607
theorem R92555 : Reach 92555 := rs (se 1 (by rfl) ⟨69416, by rfl⟩) R138833
theorem R92573 : Reach 92573 := rs (se 3 (by rfl) ⟨17357, by rfl⟩) R34715
theorem R27163 : Reach 27163 := rs (se 1 (by rfl) ⟨20372, by rfl⟩) R40745
theorem R27167 : Reach 27167 := rs (se 1 (by rfl) ⟨20375, by rfl⟩) R40751
theorem R27483 : Reach 27483 := rs (se 1 (by rfl) ⟨20612, by rfl⟩) R41225
theorem R27551 : Reach 27551 := rs (se 1 (by rfl) ⟨20663, by rfl⟩) R41327
theorem R1272833 : Reach 1272833 := rs (se 2 (by rfl) ⟨477312, by rfl⟩) R954625
theorem R27695 : Reach 27695 := rs (se 1 (by rfl) ⟨20771, by rfl⟩) R41543
theorem R27719 : Reach 27719 := rs (se 1 (by rfl) ⟨20789, by rfl⟩) R41579
theorem R27871 : Reach 27871 := rs (se 1 (by rfl) ⟨20903, by rfl⟩) R41807
theorem R28135 : Reach 28135 := rs (se 1 (by rfl) ⟨21101, by rfl⟩) R42203
theorem R28251 : Reach 28251 := rs (se 1 (by rfl) ⟨21188, by rfl⟩) R42377
theorem R290621 : Reach 290621 := rs (se 3 (by rfl) ⟨54491, by rfl⟩) R108983
theorem R28487 : Reach 28487 := rs (se 1 (by rfl) ⟨21365, by rfl⟩) R42731
theorem R159617 : Reach 159617 := rs (se 2 (by rfl) ⟨59856, by rfl⟩) R119713
theorem R61339 : Reach 61339 := rs (se 1 (by rfl) ⟨46004, by rfl⟩) R92009
theorem R94175 : Reach 94175 := rs (se 1 (by rfl) ⟨70631, by rfl⟩) R141263
theorem R28639 : Reach 28639 := rs (se 1 (by rfl) ⟨21479, by rfl⟩) R42959
theorem R94337 : Reach 94337 := rs (se 2 (by rfl) ⟨35376, by rfl⟩) R70753
theorem R28903 : Reach 28903 := rs (se 1 (by rfl) ⟨21677, by rfl⟩) R43355
theorem R127241 : Reach 127241 := rs (se 2 (by rfl) ⟨47715, by rfl⟩) R95431
theorem R29055 : Reach 29055 := rs (se 1 (by rfl) ⟨21791, by rfl⟩) R43583
theorem R192935 : Reach 192935 := rs (se 1 (by rfl) ⟨144701, by rfl⟩) R289403
theorem R29135 : Reach 29135 := rs (se 1 (by rfl) ⟨21851, by rfl⟩) R43703
theorem R94823 : Reach 94823 := rs (se 1 (by rfl) ⟨71117, by rfl⟩) R142235
theorem R29287 : Reach 29287 := rs (se 1 (by rfl) ⟨21965, by rfl⟩) R43931
theorem R1078109 : Reach 1078109 := rs (se 3 (by rfl) ⟨202145, by rfl⟩) R404291
theorem R29551 : Reach 29551 := rs (se 1 (by rfl) ⟨22163, by rfl⟩) R44327
theorem R29607 : Reach 29607 := rs (se 1 (by rfl) ⟨22205, by rfl⟩) R44411
theorem R95147 : Reach 95147 := rs (se 1 (by rfl) ⟨71360, by rfl⟩) R142721
theorem R62459 : Reach 62459 := rs (se 1 (by rfl) ⟨46844, by rfl⟩) R93689
theorem R29691 : Reach 29691 := rs (se 1 (by rfl) ⟨22268, by rfl⟩) R44537
theorem R62527 : Reach 62527 := rs (se 1 (by rfl) ⟨46895, by rfl⟩) R93791
theorem R29759 : Reach 29759 := rs (se 1 (by rfl) ⟨22319, by rfl⟩) R44639
theorem R62639 : Reach 62639 := rs (se 1 (by rfl) ⟨46979, by rfl⟩) R93959
theorem R95407 : Reach 95407 := rs (se 1 (by rfl) ⟨71555, by rfl⟩) R143111
theorem R29871 : Reach 29871 := rs (se 1 (by rfl) ⟨22403, by rfl⟩) R44807
theorem R29903 : Reach 29903 := rs (se 1 (by rfl) ⟨22427, by rfl⟩) R44855
theorem R62675 : Reach 62675 := rs (se 1 (by rfl) ⟨47006, by rfl⟩) R94013
theorem R95579 : Reach 95579 := rs (se 1 (by rfl) ⟨71684, by rfl⟩) R143369
theorem R30107 : Reach 30107 := rs (se 1 (by rfl) ⟨22580, by rfl⟩) R45161
theorem R95687 : Reach 95687 := rs (se 1 (by rfl) ⟨71765, by rfl⟩) R143531
theorem R62945 : Reach 62945 := rs (se 2 (by rfl) ⟨23604, by rfl⟩) R47209
theorem R30319 : Reach 30319 := rs (se 1 (by rfl) ⟨22739, by rfl⟩) R45479
theorem R30375 : Reach 30375 := rs (se 1 (by rfl) ⟨22781, by rfl⟩) R45563
theorem R30427 : Reach 30427 := rs (se 1 (by rfl) ⟨22820, by rfl⟩) R45641
theorem R30459 : Reach 30459 := rs (se 1 (by rfl) ⟨22844, by rfl⟩) R45689
theorem R96011 : Reach 96011 := rs (se 1 (by rfl) ⟨72008, by rfl⟩) R144017
theorem R30495 : Reach 30495 := rs (se 1 (by rfl) ⟨22871, by rfl⟩) R45743
theorem R30527 : Reach 30527 := rs (se 1 (by rfl) ⟨22895, by rfl⟩) R45791
theorem R30663 : Reach 30663 := rs (se 1 (by rfl) ⟨22997, by rfl⟩) R45995
theorem R30703 : Reach 30703 := rs (se 1 (by rfl) ⟨23027, by rfl⟩) R46055
theorem R96281 : Reach 96281 := rs (se 2 (by rfl) ⟨36105, by rfl⟩) R72211
theorem R30815 : Reach 30815 := rs (se 1 (by rfl) ⟨23111, by rfl⟩) R46223
theorem R30875 : Reach 30875 := rs (se 1 (by rfl) ⟨23156, by rfl⟩) R46313
theorem R30911 : Reach 30911 := rs (se 1 (by rfl) ⟨23183, by rfl⟩) R46367
theorem R31023 : Reach 31023 := rs (se 1 (by rfl) ⟨23267, by rfl⟩) R46535
theorem R719513 : Reach 719513 := rs (se 2 (by rfl) ⟨269817, by rfl⟩) R539635
theorem R64415 : Reach 64415 := rs (se 1 (by rfl) ⟨48311, by rfl⟩) R96623
theorem R64583 : Reach 64583 := rs (se 1 (by rfl) ⟨48437, by rfl⟩) R96875
theorem R851267 : Reach 851267 := rs (se 1 (by rfl) ⟨638450, by rfl⟩) R1276901
theorem R97631 : Reach 97631 := rs (se 1 (by rfl) ⟨73223, by rfl⟩) R146447
theorem R64979 : Reach 64979 := rs (se 1 (by rfl) ⟨48734, by rfl⟩) R97469
theorem R65249 : Reach 65249 := rs (se 2 (by rfl) ⟨24468, by rfl⟩) R48937
theorem R65267 : Reach 65267 := rs (se 1 (by rfl) ⟨48950, by rfl⟩) R97901
theorem R98135 : Reach 98135 := rs (se 1 (by rfl) ⟨73601, by rfl⟩) R147203
theorem R98171 : Reach 98171 := rs (se 1 (by rfl) ⟨73628, by rfl⟩) R147257
theorem R196523 : Reach 196523 := rs (se 1 (by rfl) ⟨147392, by rfl⟩) R294785
theorem R32735 : Reach 32735 := rs (se 1 (by rfl) ⟨24551, by rfl⟩) R49103
theorem R65771 : Reach 65771 := rs (se 1 (by rfl) ⟨49328, by rfl⟩) R98657
theorem R459209 : Reach 459209 := rs (se 2 (by rfl) ⟨172203, by rfl⟩) R344407
theorem R66055 : Reach 66055 := rs (se 1 (by rfl) ⟨49541, by rfl⟩) R99083
theorem R131615 : Reach 131615 := rs (se 1 (by rfl) ⟨98711, by rfl⟩) R197423
theorem R98911 : Reach 98911 := rs (se 1 (by rfl) ⟨74183, by rfl⟩) R148367
theorem R98927 : Reach 98927 := rs (se 1 (by rfl) ⟨74195, by rfl⟩) R148391
theorem R3211973 : Reach 3211973 := rs (se 4 (by rfl) ⟨301122, by rfl⟩) R602245
theorem R66329 : Reach 66329 := rs (se 2 (by rfl) ⟨24873, by rfl⟩) R49747
theorem R197549 : Reach 197549 := rs (se 3 (by rfl) ⟨37040, by rfl⟩) R74081
theorem R525257 : Reach 525257 := rs (se 2 (by rfl) ⟨196971, by rfl⟩) R393943
theorem R66671 : Reach 66671 := rs (se 1 (by rfl) ⟨50003, by rfl⟩) R100007
theorem R34015 : Reach 34015 := rs (se 1 (by rfl) ⟨25511, by rfl⟩) R51023
theorem R197855 : Reach 197855 := rs (se 1 (by rfl) ⟨148391, by rfl⟩) R296783
theorem R165187 : Reach 165187 := rs (se 1 (by rfl) ⟨123890, by rfl⟩) R247781
theorem R67067 : Reach 67067 := rs (se 1 (by rfl) ⟨50300, by rfl⟩) R100601
theorem R67103 : Reach 67103 := rs (se 1 (by rfl) ⟨50327, by rfl⟩) R100655
theorem R67247 : Reach 67247 := rs (se 1 (by rfl) ⟨50435, by rfl⟩) R100871
theorem R67567 : Reach 67567 := rs (se 1 (by rfl) ⟨50675, by rfl⟩) R101351
theorem R67679 : Reach 67679 := rs (se 1 (by rfl) ⟨50759, by rfl⟩) R101519
theorem R67967 : Reach 67967 := rs (se 1 (by rfl) ⟨50975, by rfl⟩) R101951
theorem R68435 : Reach 68435 := rs (se 1 (by rfl) ⟨51326, by rfl⟩) R102653
theorem R1149815 : Reach 1149815 := rs (se 1 (by rfl) ⟨862361, by rfl⟩) R1724723
theorem R101321 : Reach 101321 := rs (se 2 (by rfl) ⟨37995, by rfl⟩) R75991
theorem R35903 : Reach 35903 := rs (se 1 (by rfl) ⟨26927, by rfl⟩) R53855
theorem R68795 : Reach 68795 := rs (se 1 (by rfl) ⟨51596, by rfl⟩) R103193
theorem R68975 : Reach 68975 := rs (se 1 (by rfl) ⟨51731, by rfl⟩) R103463
theorem R36217 : Reach 36217 := rs (se 2 (by rfl) ⟨13581, by rfl⟩) R27163
theorem R102383 : Reach 102383 := rs (se 1 (by rfl) ⟨76787, by rfl⟩) R153575
theorem R69695 : Reach 69695 := rs (se 1 (by rfl) ⟨52271, by rfl⟩) R104543
theorem R200839 : Reach 200839 := rs (se 1 (by rfl) ⟨150629, by rfl⟩) R301259
theorem R233765 : Reach 233765 := rs (se 4 (by rfl) ⟨21915, by rfl⟩) R43831
theorem R69929 : Reach 69929 := rs (se 2 (by rfl) ⟨26223, by rfl⟩) R52447
theorem R201079 : Reach 201079 := rs (se 1 (by rfl) ⟨150809, by rfl⟩) R301619
theorem R70199 : Reach 70199 := rs (se 1 (by rfl) ⟨52649, by rfl⟩) R105299
theorem R37513 : Reach 37513 := rs (se 2 (by rfl) ⟨14067, by rfl⟩) R28135
theorem R1020599 : Reach 1020599 := rs (se 1 (by rfl) ⟨765449, by rfl⟩) R1530899
theorem R234251 : Reach 234251 := rs (se 1 (by rfl) ⟨175688, by rfl⟩) R351377
theorem R137321 : Reach 137321 := rs (se 2 (by rfl) ⟨51495, by rfl⟩) R102991
theorem R39199 : Reach 39199 := rs (se 1 (by rfl) ⟨29399, by rfl⟩) R58799
theorem R4069757 : Reach 4069757 := rs (se 3 (by rfl) ⟨763079, by rfl⟩) R1526159
theorem R72505 : Reach 72505 := rs (se 2 (by rfl) ⟨27189, by rfl⟩) R54379
theorem R138671 : Reach 138671 := rs (se 1 (by rfl) ⟨104003, by rfl⟩) R208007
theorem R237289 : Reach 237289 := rs (se 2 (by rfl) ⟨88983, by rfl⟩) R177967
theorem R40937 : Reach 40937 := rs (se 2 (by rfl) ⟨15351, by rfl⟩) R30703
theorem R73943 : Reach 73943 := rs (se 1 (by rfl) ⟨55457, by rfl⟩) R110915
theorem R270911 : Reach 270911 := rs (se 1 (by rfl) ⟨203183, by rfl⟩) R406367
theorem R41639 : Reach 41639 := rs (se 1 (by rfl) ⟨31229, by rfl⟩) R62459
theorem R2859725 : Reach 2859725 := rs (se 3 (by rfl) ⟨536198, by rfl⟩) R1072397
theorem R74459 : Reach 74459 := rs (se 1 (by rfl) ⟨55844, by rfl⟩) R111689
theorem R41759 : Reach 41759 := rs (se 1 (by rfl) ⟨31319, by rfl⟩) R62639
theorem R41783 : Reach 41783 := rs (se 1 (by rfl) ⟨31337, by rfl⟩) R62675
theorem R2270045 : Reach 2270045 := rs (se 3 (by rfl) ⟨425633, by rfl⟩) R851267
theorem R140129 : Reach 140129 := rs (se 2 (by rfl) ⟨52548, by rfl⟩) R105097
theorem R41963 : Reach 41963 := rs (se 1 (by rfl) ⟨31472, by rfl⟩) R62945
theorem R336953 : Reach 336953 := rs (se 2 (by rfl) ⟨126357, by rfl⟩) R252715
theorem R42943 : Reach 42943 := rs (se 1 (by rfl) ⟨32207, by rfl⟩) R64415
theorem R43055 : Reach 43055 := rs (se 1 (by rfl) ⟨32291, by rfl⟩) R64583
theorem R43319 : Reach 43319 := rs (se 1 (by rfl) ⟨32489, by rfl⟩) R64979
theorem R43499 : Reach 43499 := rs (se 1 (by rfl) ⟨32624, by rfl⟩) R65249
theorem R43511 : Reach 43511 := rs (se 1 (by rfl) ⟨32633, by rfl⟩) R65267
theorem R207623 : Reach 207623 := rs (se 1 (by rfl) ⟨155717, by rfl⟩) R311435
theorem R142087 : Reach 142087 := rs (se 1 (by rfl) ⟨106565, by rfl⟩) R213131
theorem R44105 : Reach 44105 := rs (se 2 (by rfl) ⟨16539, by rfl⟩) R33079
theorem R44201 : Reach 44201 := rs (se 2 (by rfl) ⟨16575, by rfl⟩) R33151
theorem R44615 : Reach 44615 := rs (se 1 (by rfl) ⟨33461, by rfl⟩) R66923
theorem R44795 : Reach 44795 := rs (se 1 (by rfl) ⟨33596, by rfl⟩) R67193
theorem R307547 : Reach 307547 := rs (se 1 (by rfl) ⟨230660, by rfl⟩) R461321
theorem R45467 : Reach 45467 := rs (se 1 (by rfl) ⟨34100, by rfl⟩) R68201
theorem R111401 : Reach 111401 := rs (se 2 (by rfl) ⟨41775, by rfl⟩) R83551
theorem R45887 : Reach 45887 := rs (se 1 (by rfl) ⟨34415, by rfl⟩) R68831
theorem R111527 : Reach 111527 := rs (se 1 (by rfl) ⟨83645, by rfl⟩) R167291
theorem R46031 : Reach 46031 := rs (se 1 (by rfl) ⟨34523, by rfl⟩) R69047
theorem R46073 : Reach 46073 := rs (se 2 (by rfl) ⟨17277, by rfl⟩) R34555
theorem R46121 : Reach 46121 := rs (se 2 (by rfl) ⟨17295, by rfl⟩) R34591
theorem R46151 : Reach 46151 := rs (se 1 (by rfl) ⟨34613, by rfl⟩) R69227
theorem R46331 : Reach 46331 := rs (se 1 (by rfl) ⟨34748, by rfl⟩) R69497
theorem R46343 : Reach 46343 := rs (se 1 (by rfl) ⟨34757, by rfl⟩) R69515
theorem R46345 : Reach 46345 := rs (se 2 (by rfl) ⟨17379, by rfl⟩) R34759
theorem R46399 : Reach 46399 := rs (se 1 (by rfl) ⟨34799, by rfl⟩) R69599
theorem R79177 : Reach 79177 := rs (se 2 (by rfl) ⟨29691, by rfl⟩) R59383
theorem R3225091 : Reach 3225091 := rs (se 1 (by rfl) ⟨2418818, by rfl⟩) R4837637
theorem R46831 : Reach 46831 := rs (se 1 (by rfl) ⟨35123, by rfl⟩) R70247
theorem R210671 : Reach 210671 := rs (se 1 (by rfl) ⟨158003, by rfl⟩) R316007
theorem R15677509 : Reach 15677509 := rs (se 4 (by rfl) ⟨1469766, by rfl⟩) R2939533
theorem R80327 : Reach 80327 := rs (se 1 (by rfl) ⟨60245, by rfl⟩) R120491
theorem R47567 : Reach 47567 := rs (se 1 (by rfl) ⟨35675, by rfl⟩) R71351
theorem R80851 : Reach 80851 := rs (se 1 (by rfl) ⟨60638, by rfl⟩) R121277
theorem R113633 : Reach 113633 := rs (se 2 (by rfl) ⟨42612, by rfl⟩) R85225
theorem R114173 : Reach 114173 := rs (se 3 (by rfl) ⟨21407, by rfl⟩) R42815
theorem R48863 : Reach 48863 := rs (se 1 (by rfl) ⟨36647, by rfl⟩) R73295
theorem R81785 : Reach 81785 := rs (se 2 (by rfl) ⟨30669, by rfl⟩) R61339
theorem R115303 : Reach 115303 := rs (se 1 (by rfl) ⟨86477, by rfl⟩) R172955
theorem R508837 : Reach 508837 := rs (se 4 (by rfl) ⟨47703, by rfl⟩) R95407
theorem R50287 : Reach 50287 := rs (se 1 (by rfl) ⟨37715, by rfl⟩) R75431
theorem R214235 : Reach 214235 := rs (se 1 (by rfl) ⟨160676, by rfl⟩) R321353
theorem R83369 : Reach 83369 := rs (se 2 (by rfl) ⟨31263, by rfl⟩) R62527
theorem R50719 : Reach 50719 := rs (se 1 (by rfl) ⟨38039, by rfl⟩) R76079
theorem R2148605 : Reach 2148605 := rs (se 3 (by rfl) ⟨402863, by rfl⟩) R805727
theorem R510299 : Reach 510299 := rs (se 1 (by rfl) ⟨382724, by rfl⟩) R765449
theorem R51583 : Reach 51583 := rs (se 1 (by rfl) ⟨38687, by rfl⟩) R77375
theorem R84827 : Reach 84827 := rs (se 1 (by rfl) ⟨63620, by rfl⟩) R127241
theorem R150497 : Reach 150497 := rs (se 2 (by rfl) ⟨56436, by rfl⟩) R112873
theorem R249113 : Reach 249113 := rs (se 2 (by rfl) ⟨93417, by rfl⟩) R186835
theorem R642505 : Reach 642505 := rs (se 2 (by rfl) ⟨240939, by rfl⟩) R481879
theorem R380533 : Reach 380533 := rs (se 5 (by rfl) ⟨17837, by rfl⟩) R35675
theorem R118979 : Reach 118979 := rs (se 1 (by rfl) ⟨89234, by rfl⟩) R178469
theorem R119177 : Reach 119177 := rs (se 2 (by rfl) ⟨44691, by rfl⟩) R89383
theorem R479675 : Reach 479675 := rs (se 1 (by rfl) ⟨359756, by rfl⟩) R719513
theorem R184787 : Reach 184787 := rs (se 1 (by rfl) ⟨138590, by rfl⟩) R277181
theorem R1233467 : Reach 1233467 := rs (se 1 (by rfl) ⟨925100, by rfl⟩) R1850201
theorem R119663 : Reach 119663 := rs (se 1 (by rfl) ⟨89747, by rfl⟩) R179495
theorem R87293 : Reach 87293 := rs (se 3 (by rfl) ⟨16367, by rfl⟩) R32735
theorem R54569 : Reach 54569 := rs (se 2 (by rfl) ⟨20463, by rfl⟩) R40927
theorem R481139 : Reach 481139 := rs (se 1 (by rfl) ⟨360854, by rfl⟩) R721709
theorem R186785 : Reach 186785 := rs (se 2 (by rfl) ⟨70044, by rfl⟩) R140089
theorem R88553 : Reach 88553 := rs (se 2 (by rfl) ⟨33207, by rfl⟩) R66415
theorem R56953 : Reach 56953 := rs (se 2 (by rfl) ⟨21357, by rfl⟩) R42715
theorem R155303 : Reach 155303 := rs (se 1 (by rfl) ⟨116477, by rfl⟩) R232955
theorem R56999 : Reach 56999 := rs (se 1 (by rfl) ⟨42749, by rfl⟩) R85499
theorem R122593 : Reach 122593 := rs (se 2 (by rfl) ⟨45972, by rfl⟩) R91945
theorem R122867 : Reach 122867 := rs (se 1 (by rfl) ⟨92150, by rfl⟩) R184301
theorem R221615 : Reach 221615 := rs (se 1 (by rfl) ⟨166211, by rfl⟩) R332423
theorem R157099 : Reach 157099 := rs (se 1 (by rfl) ⟨117824, by rfl⟩) R235649
theorem R223073 : Reach 223073 := rs (se 2 (by rfl) ⟨83652, by rfl⟩) R167305
theorem R92123 : Reach 92123 := rs (se 1 (by rfl) ⟨69092, by rfl⟩) R138185
theorem R190451 : Reach 190451 := rs (se 1 (by rfl) ⟨142838, by rfl⟩) R285677
theorem R92393 : Reach 92393 := rs (se 2 (by rfl) ⟨34647, by rfl⟩) R69295
theorem R92663 : Reach 92663 := rs (se 1 (by rfl) ⟨69497, by rfl⟩) R138995
theorem R27183 : Reach 27183 := rs (se 1 (by rfl) ⟨20387, by rfl⟩) R40775
theorem R27239 : Reach 27239 := rs (se 1 (by rfl) ⟨20429, by rfl⟩) R40859
theorem R420497 : Reach 420497 := rs (se 2 (by rfl) ⟨157686, by rfl⟩) R315373
theorem R92825 : Reach 92825 := rs (se 2 (by rfl) ⟨34809, by rfl⟩) R69619
theorem R27615 : Reach 27615 := rs (se 1 (by rfl) ⟨20711, by rfl⟩) R41423
theorem R27643 : Reach 27643 := rs (se 1 (by rfl) ⟨20732, by rfl⟩) R41465
theorem R27711 : Reach 27711 := rs (se 1 (by rfl) ⟨20783, by rfl⟩) R41567
theorem R93257 : Reach 93257 := rs (se 2 (by rfl) ⟨34971, by rfl⟩) R69943
theorem R28031 : Reach 28031 := rs (se 1 (by rfl) ⟨21023, by rfl⟩) R42047
theorem R28059 : Reach 28059 := rs (se 1 (by rfl) ⟨21044, by rfl⟩) R42089
theorem R28127 : Reach 28127 := rs (se 1 (by rfl) ⟨21095, by rfl⟩) R42191
theorem R355913 : Reach 355913 := rs (se 2 (by rfl) ⟨133467, by rfl⟩) R266935
theorem R61019 : Reach 61019 := rs (se 1 (by rfl) ⟨45764, by rfl⟩) R91529
theorem R192091 : Reach 192091 := rs (se 1 (by rfl) ⟨144068, by rfl⟩) R288137
theorem R28263 : Reach 28263 := rs (se 1 (by rfl) ⟨21197, by rfl⟩) R42395
theorem R28411 : Reach 28411 := rs (se 1 (by rfl) ⟨21308, by rfl⟩) R42617
theorem R28479 : Reach 28479 := rs (se 1 (by rfl) ⟨21359, by rfl⟩) R42719
theorem R28543 : Reach 28543 := rs (se 1 (by rfl) ⟨21407, by rfl⟩) R42815
theorem R28655 : Reach 28655 := rs (se 1 (by rfl) ⟨21491, by rfl⟩) R42983
theorem R61433 : Reach 61433 := rs (se 2 (by rfl) ⟨23037, by rfl⟩) R46075
theorem R28667 : Reach 28667 := rs (se 1 (by rfl) ⟨21500, by rfl⟩) R43001
theorem R28735 : Reach 28735 := rs (se 1 (by rfl) ⟨21551, by rfl⟩) R43103
theorem R61523 : Reach 61523 := rs (se 1 (by rfl) ⟨46142, by rfl⟩) R92285
theorem R28767 : Reach 28767 := rs (se 1 (by rfl) ⟨21575, by rfl⟩) R43151
theorem R28775 : Reach 28775 := rs (se 1 (by rfl) ⟨21581, by rfl⟩) R43163
theorem R28799 : Reach 28799 := rs (se 1 (by rfl) ⟨21599, by rfl⟩) R43199
theorem R28827 : Reach 28827 := rs (se 1 (by rfl) ⟨21620, by rfl⟩) R43241
theorem R28847 : Reach 28847 := rs (se 1 (by rfl) ⟨21635, by rfl⟩) R43271
theorem R61703 : Reach 61703 := rs (se 1 (by rfl) ⟨46277, by rfl⟩) R92555
theorem R61715 : Reach 61715 := rs (se 1 (by rfl) ⟨46286, by rfl⟩) R92573
theorem R29031 : Reach 29031 := rs (se 1 (by rfl) ⟨21773, by rfl⟩) R43547
theorem R29083 : Reach 29083 := rs (se 1 (by rfl) ⟨21812, by rfl⟩) R43625
theorem R94715 : Reach 94715 := rs (se 1 (by rfl) ⟨71036, by rfl⟩) R142073
theorem R62009 : Reach 62009 := rs (se 2 (by rfl) ⟨23253, by rfl⟩) R46507
theorem R848555 : Reach 848555 := rs (se 1 (by rfl) ⟨636416, by rfl⟩) R1272833
theorem R29435 : Reach 29435 := rs (se 1 (by rfl) ⟨22076, by rfl⟩) R44153
theorem R94985 : Reach 94985 := rs (se 2 (by rfl) ⟨35619, by rfl⟩) R71239
theorem R29503 : Reach 29503 := rs (se 1 (by rfl) ⟨22127, by rfl⟩) R44255
theorem R29531 : Reach 29531 := rs (se 1 (by rfl) ⟨22148, by rfl⟩) R44297
theorem R62345 : Reach 62345 := rs (se 2 (by rfl) ⟨23379, by rfl⟩) R46759
theorem R29599 : Reach 29599 := rs (se 1 (by rfl) ⟨22199, by rfl⟩) R44399
theorem R29679 : Reach 29679 := rs (se 1 (by rfl) ⟨22259, by rfl⟩) R44519
theorem R29767 : Reach 29767 := rs (se 1 (by rfl) ⟨22325, by rfl⟩) R44651
theorem R29791 : Reach 29791 := rs (se 1 (by rfl) ⟨22343, by rfl⟩) R44687
theorem R62569 : Reach 62569 := rs (se 2 (by rfl) ⟨23463, by rfl⟩) R46927
theorem R29851 : Reach 29851 := rs (se 1 (by rfl) ⟨22388, by rfl⟩) R44777
theorem R193747 : Reach 193747 := rs (se 1 (by rfl) ⟨145310, by rfl⟩) R290621
theorem R29947 : Reach 29947 := rs (se 1 (by rfl) ⟨22460, by rfl⟩) R44921
theorem R62729 : Reach 62729 := rs (se 2 (by rfl) ⟨23523, by rfl⟩) R47047
theorem R62783 : Reach 62783 := rs (se 1 (by rfl) ⟨47087, by rfl⟩) R94175
theorem R30015 : Reach 30015 := rs (se 1 (by rfl) ⟨22511, by rfl⟩) R45023
theorem R62891 : Reach 62891 := rs (se 1 (by rfl) ⟨47168, by rfl⟩) R94337
theorem R30183 : Reach 30183 := rs (se 1 (by rfl) ⟨22637, by rfl⟩) R45275
theorem R30191 : Reach 30191 := rs (se 1 (by rfl) ⟨22643, by rfl⟩) R45287
theorem R30299 : Reach 30299 := rs (se 1 (by rfl) ⟨22724, by rfl⟩) R45449
theorem R128623 : Reach 128623 := rs (se 1 (by rfl) ⟨96467, by rfl⟩) R192935
theorem R30363 : Reach 30363 := rs (se 1 (by rfl) ⟨22772, by rfl⟩) R45545
theorem R63215 : Reach 63215 := rs (se 1 (by rfl) ⟨47411, by rfl⟩) R94823
theorem R30447 : Reach 30447 := rs (se 1 (by rfl) ⟨22835, by rfl⟩) R45671
theorem R30535 : Reach 30535 := rs (se 1 (by rfl) ⟨22901, by rfl⟩) R45803
theorem R30555 : Reach 30555 := rs (se 1 (by rfl) ⟨22916, by rfl⟩) R45833
theorem R30587 : Reach 30587 := rs (se 1 (by rfl) ⟨22940, by rfl⟩) R45881
theorem R718739 : Reach 718739 := rs (se 1 (by rfl) ⟨539054, by rfl⟩) R1078109
theorem R30623 : Reach 30623 := rs (se 1 (by rfl) ⟨22967, by rfl⟩) R45935
theorem R63431 : Reach 63431 := rs (se 1 (by rfl) ⟨47573, by rfl⟩) R95147
theorem R30791 : Reach 30791 := rs (se 1 (by rfl) ⟨23093, by rfl⟩) R46187
theorem R227447 : Reach 227447 := rs (se 1 (by rfl) ⟨170585, by rfl⟩) R341171
theorem R2717873 : Reach 2717873 := rs (se 2 (by rfl) ⟨1019202, by rfl⟩) R2038405
theorem R63719 : Reach 63719 := rs (se 1 (by rfl) ⟨47789, by rfl⟩) R95579
theorem R30951 : Reach 30951 := rs (se 1 (by rfl) ⟨23213, by rfl⟩) R46427
theorem R63737 : Reach 63737 := rs (se 2 (by rfl) ⟨23901, by rfl⟩) R47803
theorem R63791 : Reach 63791 := rs (se 1 (by rfl) ⟨47843, by rfl⟩) R95687
theorem R555407 : Reach 555407 := rs (se 1 (by rfl) ⟨416555, by rfl⟩) R833111
theorem R31135 : Reach 31135 := rs (se 1 (by rfl) ⟨23351, by rfl⟩) R46703
theorem R31207 : Reach 31207 := rs (se 1 (by rfl) ⟨23405, by rfl⟩) R46811
theorem R64007 : Reach 64007 := rs (se 1 (by rfl) ⟨48005, by rfl⟩) R96011
theorem R64187 : Reach 64187 := rs (se 1 (by rfl) ⟨48140, by rfl⟩) R96281
theorem R31951 : Reach 31951 := rs (se 1 (by rfl) ⟨23963, by rfl⟩) R47927
theorem R32071 : Reach 32071 := rs (se 1 (by rfl) ⟨24053, by rfl⟩) R48107
theorem R65087 : Reach 65087 := rs (se 1 (by rfl) ⟨48815, by rfl⟩) R97631
theorem R425645 : Reach 425645 := rs (se 3 (by rfl) ⟨79808, by rfl⟩) R159617
theorem R65423 : Reach 65423 := rs (se 1 (by rfl) ⟨49067, by rfl⟩) R98135
theorem R65447 : Reach 65447 := rs (se 1 (by rfl) ⟨49085, by rfl⟩) R98171
theorem R131015 : Reach 131015 := rs (se 1 (by rfl) ⟨98261, by rfl⟩) R196523
theorem R65951 : Reach 65951 := rs (se 1 (by rfl) ⟨49463, by rfl⟩) R98927
theorem R131699 : Reach 131699 := rs (se 1 (by rfl) ⟨98774, by rfl⟩) R197549
theorem R131881 : Reach 131881 := rs (se 2 (by rfl) ⟨49455, by rfl⟩) R98911
theorem R131903 : Reach 131903 := rs (se 1 (by rfl) ⟨98927, by rfl⟩) R197855
theorem R67049 : Reach 67049 := rs (se 2 (by rfl) ⟨25143, by rfl⟩) R50287
theorem R722429 : Reach 722429 := rs (se 3 (by rfl) ⟨135455, by rfl⟩) R270911
theorem R67547 : Reach 67547 := rs (se 1 (by rfl) ⟨50660, by rfl⟩) R101321
theorem R100331 : Reach 100331 := rs (se 1 (by rfl) ⟨75248, by rfl⟩) R150497
theorem R67625 : Reach 67625 := rs (se 2 (by rfl) ⟨25359, by rfl⟩) R50719
theorem R68255 : Reach 68255 := rs (se 1 (by rfl) ⟨51191, by rfl⟩) R102383
theorem R822311 : Reach 822311 := rs (se 1 (by rfl) ⟨616733, by rfl⟩) R1233467
theorem R68777 : Reach 68777 := rs (se 2 (by rfl) ⟨25791, by rfl⟩) R51583
theorem R36379 : Reach 36379 := rs (se 1 (by rfl) ⟨27284, by rfl⟩) R54569
theorem R856673 : Reach 856673 := rs (se 2 (by rfl) ⟨321252, by rfl⟩) R642505
theorem R103535 : Reach 103535 := rs (se 1 (by rfl) ⟨77651, by rfl⟩) R155303
theorem R37999 : Reach 37999 := rs (se 1 (by rfl) ⟨28499, by rfl⟩) R56999
theorem R267785 : Reach 267785 := rs (se 2 (by rfl) ⟨100419, by rfl⟩) R200839
theorem R268105 : Reach 268105 := rs (se 2 (by rfl) ⟨100539, by rfl⟩) R201079
theorem R1513363 : Reach 1513363 := rs (se 1 (by rfl) ⟨1135022, by rfl⟩) R2270045
theorem R236141 : Reach 236141 := rs (se 3 (by rfl) ⟨44276, by rfl⟩) R88553
theorem R105569 : Reach 105569 := rs (se 2 (by rfl) ⟨39588, by rfl⟩) R79177
theorem R4300121 : Reach 4300121 := rs (se 2 (by rfl) ⟨1612545, by rfl⟩) R3225091
theorem R171497 : Reach 171497 := rs (se 2 (by rfl) ⟨64311, by rfl⟩) R128623
theorem R237275 : Reach 237275 := rs (se 1 (by rfl) ⟨177956, by rfl⟩) R355913
theorem R40679 : Reach 40679 := rs (se 1 (by rfl) ⟨30509, by rfl⟩) R61019
theorem R40955 : Reach 40955 := rs (se 1 (by rfl) ⟨30716, by rfl⟩) R61433
theorem R41015 : Reach 41015 := rs (se 1 (by rfl) ⟨30761, by rfl⟩) R61523
theorem R41135 : Reach 41135 := rs (se 1 (by rfl) ⟨30851, by rfl⟩) R61703
theorem R41143 : Reach 41143 := rs (se 1 (by rfl) ⟨30857, by rfl⟩) R61715
theorem R205031 : Reach 205031 := rs (se 1 (by rfl) ⟨153773, by rfl⟩) R307547
theorem R41339 : Reach 41339 := rs (se 1 (by rfl) ⟨31004, by rfl⟩) R62009
theorem R565703 : Reach 565703 := rs (se 1 (by rfl) ⟨424277, by rfl⟩) R848555
theorem R74267 : Reach 74267 := rs (se 1 (by rfl) ⟨55700, by rfl⟩) R111401
theorem R41513 : Reach 41513 := rs (se 2 (by rfl) ⟨15567, by rfl⟩) R31135
theorem R41563 : Reach 41563 := rs (se 1 (by rfl) ⟨31172, by rfl⟩) R62345
theorem R74351 : Reach 74351 := rs (se 1 (by rfl) ⟨55763, by rfl⟩) R111527
theorem R41609 : Reach 41609 := rs (se 2 (by rfl) ⟨15603, by rfl⟩) R31207
theorem R664301 : Reach 664301 := rs (se 3 (by rfl) ⟨124556, by rfl⟩) R249113
theorem R41819 : Reach 41819 := rs (se 1 (by rfl) ⟨31364, by rfl⟩) R62729
theorem R41855 : Reach 41855 := rs (se 1 (by rfl) ⟨31391, by rfl⟩) R62783
theorem R41927 : Reach 41927 := rs (se 1 (by rfl) ⟨31445, by rfl⟩) R62891
theorem R42143 : Reach 42143 := rs (se 1 (by rfl) ⟨31607, by rfl⟩) R63215
theorem R140447 : Reach 140447 := rs (se 1 (by rfl) ⟨105335, by rfl⟩) R210671
theorem R107801 : Reach 107801 := rs (se 2 (by rfl) ⟨40425, by rfl⟩) R80851
theorem R42287 : Reach 42287 := rs (se 1 (by rfl) ⟨31715, by rfl⟩) R63431
theorem R1811915 : Reach 1811915 := rs (se 1 (by rfl) ⟨1358936, by rfl⟩) R2717873
theorem R42479 : Reach 42479 := rs (se 1 (by rfl) ⟨31859, by rfl⟩) R63719
theorem R42491 : Reach 42491 := rs (se 1 (by rfl) ⟨31868, by rfl⟩) R63737
theorem R42527 : Reach 42527 := rs (se 1 (by rfl) ⟨31895, by rfl⟩) R63791
theorem R370271 : Reach 370271 := rs (se 1 (by rfl) ⟨277703, by rfl⟩) R555407
theorem R42601 : Reach 42601 := rs (se 2 (by rfl) ⟨15975, by rfl⟩) R31951
theorem R42671 : Reach 42671 := rs (se 1 (by rfl) ⟨32003, by rfl⟩) R64007
theorem R42761 : Reach 42761 := rs (se 2 (by rfl) ⟨16035, by rfl⟩) R32071
theorem R42791 : Reach 42791 := rs (se 1 (by rfl) ⟨32093, by rfl⟩) R64187
theorem R75755 : Reach 75755 := rs (se 1 (by rfl) ⟨56816, by rfl⟩) R113633
theorem R75937 : Reach 75937 := rs (se 2 (by rfl) ⟨28476, by rfl⟩) R56953
theorem R76115 : Reach 76115 := rs (se 1 (by rfl) ⟨57086, by rfl⟩) R114173
theorem R43391 : Reach 43391 := rs (se 1 (by rfl) ⟨32543, by rfl⟩) R65087
theorem R43615 : Reach 43615 := rs (se 1 (by rfl) ⟨32711, by rfl⟩) R65423
theorem R43631 : Reach 43631 := rs (se 1 (by rfl) ⟨32723, by rfl⟩) R65447
theorem R43847 : Reach 43847 := rs (se 1 (by rfl) ⟨32885, by rfl⟩) R65771
theorem R306139 : Reach 306139 := rs (se 1 (by rfl) ⟨229604, by rfl⟩) R459209
theorem R2141315 : Reach 2141315 := rs (se 1 (by rfl) ⟨1605986, by rfl⟩) R3211973
theorem R44219 : Reach 44219 := rs (se 1 (by rfl) ⟨33164, by rfl⟩) R66329
theorem R44447 : Reach 44447 := rs (se 1 (by rfl) ⟨33335, by rfl⟩) R66671
theorem R142823 : Reach 142823 := rs (se 1 (by rfl) ⟨107117, by rfl⟩) R214235
theorem R44711 : Reach 44711 := rs (se 1 (by rfl) ⟨33533, by rfl⟩) R67067
theorem R44735 : Reach 44735 := rs (se 1 (by rfl) ⟨33551, by rfl⟩) R67103
theorem R44831 : Reach 44831 := rs (se 1 (by rfl) ⟨33623, by rfl⟩) R67247
theorem R45119 : Reach 45119 := rs (se 1 (by rfl) ⟨33839, by rfl⟩) R67679
theorem R340199 : Reach 340199 := rs (se 1 (by rfl) ⟨255149, by rfl⟩) R510299
theorem R45311 : Reach 45311 := rs (se 1 (by rfl) ⟨33983, by rfl⟩) R67967
theorem R45353 : Reach 45353 := rs (se 2 (by rfl) ⟨17007, by rfl⟩) R34015
theorem R45623 : Reach 45623 := rs (se 1 (by rfl) ⟨34217, by rfl⟩) R68435
theorem R209465 : Reach 209465 := rs (se 2 (by rfl) ⟨78549, by rfl⟩) R157099
theorem R45863 : Reach 45863 := rs (se 1 (by rfl) ⟨34397, by rfl⟩) R68795
theorem R45983 : Reach 45983 := rs (se 1 (by rfl) ⟨34487, by rfl⟩) R68975
theorem R111901 : Reach 111901 := rs (se 3 (by rfl) ⟨20981, by rfl⟩) R41963
theorem R46463 : Reach 46463 := rs (se 1 (by rfl) ⟨34847, by rfl⟩) R69695
theorem R79319 : Reach 79319 := rs (se 1 (by rfl) ⟨59489, by rfl⟩) R118979
theorem R46619 : Reach 46619 := rs (se 1 (by rfl) ⟨34964, by rfl⟩) R69929
theorem R79451 : Reach 79451 := rs (se 1 (by rfl) ⟨59588, by rfl⟩) R119177
theorem R46799 : Reach 46799 := rs (se 1 (by rfl) ⟨35099, by rfl⟩) R70199
theorem R79775 : Reach 79775 := rs (se 1 (by rfl) ⟨59831, by rfl⟩) R119663
theorem R80509 : Reach 80509 := rs (se 3 (by rfl) ⟨15095, by rfl⟩) R30191
theorem R48289 : Reach 48289 := rs (se 2 (by rfl) ⟨18108, by rfl⟩) R36217
theorem R507377 : Reach 507377 := rs (se 2 (by rfl) ⟨190266, by rfl⟩) R380533
theorem R81911 : Reach 81911 := rs (se 1 (by rfl) ⟨61433, by rfl⟩) R122867
theorem R49295 : Reach 49295 := rs (se 1 (by rfl) ⟨36971, by rfl⟩) R73943
theorem R147743 : Reach 147743 := rs (se 1 (by rfl) ⟨110807, by rfl⟩) R221615
theorem R49639 : Reach 49639 := rs (se 1 (by rfl) ⟨37229, by rfl⟩) R74459
theorem R50017 : Reach 50017 := rs (se 2 (by rfl) ⟨18756, by rfl⟩) R37513
theorem R148715 : Reach 148715 := rs (se 1 (by rfl) ⟨111536, by rfl⟩) R223073
theorem R83425 : Reach 83425 := rs (se 2 (by rfl) ⟨31284, by rfl⟩) R62569
theorem R280331 : Reach 280331 := rs (se 1 (by rfl) ⟨210248, by rfl⟩) R420497
theorem R3066173 : Reach 3066173 := rs (se 3 (by rfl) ⟨574907, by rfl⟩) R1149815
theorem R52265 : Reach 52265 := rs (se 2 (by rfl) ⟨19599, by rfl⟩) R39199
theorem R479159 : Reach 479159 := rs (se 1 (by rfl) ⟨359369, by rfl⟩) R718739
theorem R151631 : Reach 151631 := rs (se 1 (by rfl) ⟨113723, by rfl⟩) R227447
theorem R53551 : Reach 53551 := rs (se 1 (by rfl) ⟨40163, by rfl⟩) R80327
theorem R316385 : Reach 316385 := rs (se 2 (by rfl) ⟨118644, by rfl⟩) R237289
theorem R283763 : Reach 283763 := rs (se 1 (by rfl) ⟨212822, by rfl⟩) R425645
theorem R447605 : Reach 447605 := rs (se 5 (by rfl) ⟨20981, by rfl⟩) R41963
theorem R349373 : Reach 349373 := rs (se 3 (by rfl) ⟨65507, by rfl⟩) R131015
theorem R54523 : Reach 54523 := rs (se 1 (by rfl) ⟨40892, by rfl⟩) R81785
theorem R87743 : Reach 87743 := rs (se 1 (by rfl) ⟨65807, by rfl⟩) R131615
theorem R350171 : Reach 350171 := rs (se 1 (by rfl) ⟨262628, by rfl⟩) R525257
theorem R88073 : Reach 88073 := rs (se 2 (by rfl) ⟨33027, by rfl⟩) R66055
theorem R153737 : Reach 153737 := rs (se 2 (by rfl) ⟨57651, by rfl⟩) R115303
theorem R55579 : Reach 55579 := rs (se 1 (by rfl) ⟨41684, by rfl⟩) R83369
theorem R678449 : Reach 678449 := rs (se 2 (by rfl) ⟨254418, by rfl⟩) R508837
theorem R1432403 : Reach 1432403 := rs (se 1 (by rfl) ⟨1074302, by rfl⟩) R2148605
theorem R220249 : Reach 220249 := rs (se 2 (by rfl) ⟨82593, by rfl⟩) R165187
theorem R7625933 : Reach 7625933 := rs (se 3 (by rfl) ⟨1429862, by rfl⟩) R2859725
theorem R56551 : Reach 56551 := rs (se 1 (by rfl) ⟨42413, by rfl⟩) R84827
theorem R57257 : Reach 57257 := rs (se 2 (by rfl) ⟨21471, by rfl⟩) R42943
theorem R90089 : Reach 90089 := rs (se 2 (by rfl) ⟨33783, by rfl⟩) R67567
theorem R155843 : Reach 155843 := rs (se 1 (by rfl) ⟨116882, by rfl⟩) R233765
theorem R319783 : Reach 319783 := rs (se 1 (by rfl) ⟨239837, by rfl⟩) R479675
theorem R123191 : Reach 123191 := rs (se 1 (by rfl) ⟨92393, by rfl⟩) R184787
theorem R680399 : Reach 680399 := rs (se 1 (by rfl) ⟨510299, by rfl⟩) R1020599
theorem R156167 : Reach 156167 := rs (se 1 (by rfl) ⟨117125, by rfl⟩) R234251
theorem R58195 : Reach 58195 := rs (se 1 (by rfl) ⟨43646, by rfl⟩) R87293
theorem R189449 : Reach 189449 := rs (se 2 (by rfl) ⟨71043, by rfl⟩) R142087
theorem R320759 : Reach 320759 := rs (se 1 (by rfl) ⟨240569, by rfl⟩) R481139
theorem R91547 : Reach 91547 := rs (se 1 (by rfl) ⟨68660, by rfl⟩) R137321
theorem R2713171 : Reach 2713171 := rs (se 1 (by rfl) ⟨2034878, by rfl⟩) R4069757
theorem R124523 : Reach 124523 := rs (se 1 (by rfl) ⟨93392, by rfl⟩) R186785
theorem R256121 : Reach 256121 := rs (se 2 (by rfl) ⟨96045, by rfl⟩) R192091
theorem R92447 : Reach 92447 := rs (se 1 (by rfl) ⟨69335, by rfl⟩) R138671
theorem R27291 : Reach 27291 := rs (se 1 (by rfl) ⟨20468, by rfl⟩) R40937
theorem R27759 : Reach 27759 := rs (se 1 (by rfl) ⟨20819, by rfl⟩) R41639
theorem R27839 : Reach 27839 := rs (se 1 (by rfl) ⟨20879, by rfl⟩) R41759
theorem R27855 : Reach 27855 := rs (se 1 (by rfl) ⟨20891, by rfl⟩) R41783
theorem R93419 : Reach 93419 := rs (se 1 (by rfl) ⟨70064, by rfl⟩) R140129
theorem R27975 : Reach 27975 := rs (se 1 (by rfl) ⟨20981, by rfl⟩) R41963
theorem R224635 : Reach 224635 := rs (se 1 (by rfl) ⟨168476, by rfl⟩) R336953
theorem R61415 : Reach 61415 := rs (se 1 (by rfl) ⟨46061, by rfl⟩) R92123
theorem R126967 : Reach 126967 := rs (se 1 (by rfl) ⟨95225, by rfl⟩) R190451
theorem R28703 : Reach 28703 := rs (se 1 (by rfl) ⟨21527, by rfl⟩) R43055
theorem R61595 : Reach 61595 := rs (se 1 (by rfl) ⟨46196, by rfl⟩) R92393
theorem R28879 : Reach 28879 := rs (se 1 (by rfl) ⟨21659, by rfl⟩) R43319
theorem R258329 : Reach 258329 := rs (se 2 (by rfl) ⟨96873, by rfl⟩) R193747
theorem R28999 : Reach 28999 := rs (se 1 (by rfl) ⟨21749, by rfl⟩) R43499
theorem R61775 : Reach 61775 := rs (se 1 (by rfl) ⟨46331, by rfl⟩) R92663
theorem R29007 : Reach 29007 := rs (se 1 (by rfl) ⟨21755, by rfl⟩) R43511
theorem R61793 : Reach 61793 := rs (se 2 (by rfl) ⟨23172, by rfl⟩) R46345
theorem R61865 : Reach 61865 := rs (se 2 (by rfl) ⟨23199, by rfl⟩) R46399
theorem R61883 : Reach 61883 := rs (se 1 (by rfl) ⟨46412, by rfl⟩) R92825
theorem R553661 : Reach 553661 := rs (se 3 (by rfl) ⟨103811, by rfl⟩) R207623
theorem R62171 : Reach 62171 := rs (se 1 (by rfl) ⟨46628, by rfl⟩) R93257
theorem R29403 : Reach 29403 := rs (se 1 (by rfl) ⟨22052, by rfl⟩) R44105
theorem R29467 : Reach 29467 := rs (se 1 (by rfl) ⟨22100, by rfl⟩) R44201
theorem R62441 : Reach 62441 := rs (se 2 (by rfl) ⟨23415, by rfl⟩) R46831
theorem R29743 : Reach 29743 := rs (se 1 (by rfl) ⟨22307, by rfl⟩) R44615
theorem R29863 : Reach 29863 := rs (se 1 (by rfl) ⟨22397, by rfl⟩) R44795
theorem R20903345 : Reach 20903345 := rs (se 2 (by rfl) ⟨7838754, by rfl⟩) R15677509
theorem R95741 : Reach 95741 := rs (se 3 (by rfl) ⟨17951, by rfl⟩) R35903
theorem R30311 : Reach 30311 := rs (se 1 (by rfl) ⟨22733, by rfl⟩) R45467
theorem R63143 : Reach 63143 := rs (se 1 (by rfl) ⟨47357, by rfl⟩) R94715
theorem R63323 : Reach 63323 := rs (se 1 (by rfl) ⟨47492, by rfl⟩) R94985
theorem R30591 : Reach 30591 := rs (se 1 (by rfl) ⟨22943, by rfl⟩) R45887
theorem R30687 : Reach 30687 := rs (se 1 (by rfl) ⟨23015, by rfl⟩) R46031
theorem R30715 : Reach 30715 := rs (se 1 (by rfl) ⟨23036, by rfl⟩) R46073
theorem R30747 : Reach 30747 := rs (se 1 (by rfl) ⟨23060, by rfl⟩) R46121
theorem R30767 : Reach 30767 := rs (se 1 (by rfl) ⟨23075, by rfl⟩) R46151
theorem R30887 : Reach 30887 := rs (se 1 (by rfl) ⟨23165, by rfl⟩) R46331
theorem R30895 : Reach 30895 := rs (se 1 (by rfl) ⟨23171, by rfl⟩) R46343
theorem R96673 : Reach 96673 := rs (se 2 (by rfl) ⟨36252, by rfl⟩) R72505
theorem R31711 : Reach 31711 := rs (se 1 (by rfl) ⟨23783, by rfl⟩) R47567
theorem R163457 : Reach 163457 := rs (se 2 (by rfl) ⟨61296, by rfl⟩) R122593
theorem R32575 : Reach 32575 := rs (se 1 (by rfl) ⟨24431, by rfl⟩) R48863
theorem R32863 : Reach 32863 := rs (se 1 (by rfl) ⟨24647, by rfl⟩) R49295
theorem R98495 : Reach 98495 := rs (se 1 (by rfl) ⟨73871, by rfl⟩) R147743
theorem R426377 : Reach 426377 := rs (se 2 (by rfl) ⟨159891, by rfl⟩) R319783
theorem R66185 : Reach 66185 := rs (se 2 (by rfl) ⟨24819, by rfl⟩) R49639
theorem R99143 : Reach 99143 := rs (se 1 (by rfl) ⟨74357, by rfl⟩) R148715
theorem R66689 : Reach 66689 := rs (se 2 (by rfl) ⟨25008, by rfl⟩) R50017
theorem R66887 : Reach 66887 := rs (se 1 (by rfl) ⟨50165, by rfl⟩) R100331
theorem R1771469 : Reach 1771469 := rs (se 3 (by rfl) ⟨332150, by rfl⟩) R664301
theorem R34843 : Reach 34843 := rs (se 1 (by rfl) ⟨26132, by rfl⟩) R52265
theorem R101087 : Reach 101087 := rs (se 1 (by rfl) ⟨75815, by rfl⟩) R151631
theorem R101249 : Reach 101249 := rs (se 2 (by rfl) ⟨37968, by rfl⟩) R75937
theorem R69023 : Reach 69023 := rs (se 1 (by rfl) ⟨51767, by rfl⟩) R103535
theorem R298403 : Reach 298403 := rs (se 1 (by rfl) ⟨223802, by rfl⟩) R447605
theorem R232915 : Reach 232915 := rs (se 1 (by rfl) ⟨174686, by rfl⟩) R349373
theorem R233447 : Reach 233447 := rs (se 1 (by rfl) ⟨175085, by rfl⟩) R350171
theorem R102491 : Reach 102491 := rs (se 1 (by rfl) ⟨76868, by rfl⟩) R153737
theorem R299513 : Reach 299513 := rs (se 2 (by rfl) ⟨112317, by rfl⟩) R224635
theorem R954935 : Reach 954935 := rs (se 1 (by rfl) ⟨716201, by rfl⟩) R1432403
theorem R70379 : Reach 70379 := rs (se 1 (by rfl) ⟨52784, by rfl⟩) R105569
theorem R5083955 : Reach 5083955 := rs (se 1 (by rfl) ⟨3812966, by rfl⟩) R7625933
theorem R38171 : Reach 38171 := rs (se 1 (by rfl) ⟨28628, by rfl⟩) R57257
theorem R169289 : Reach 169289 := rs (se 2 (by rfl) ⟨63483, by rfl⟩) R126967
theorem R103895 : Reach 103895 := rs (se 1 (by rfl) ⟨77921, by rfl⟩) R155843
theorem R104111 : Reach 104111 := rs (se 1 (by rfl) ⟨78083, by rfl⟩) R156167
theorem R71401 : Reach 71401 := rs (se 2 (by rfl) ⟨26775, by rfl⟩) R53551
theorem R38665 : Reach 38665 := rs (se 2 (by rfl) ⟨14499, by rfl⟩) R28999
theorem R71867 : Reach 71867 := rs (se 1 (by rfl) ⟨53900, by rfl⟩) R107801
theorem R170747 : Reach 170747 := rs (se 1 (by rfl) ⟨128060, by rfl⟩) R256121
theorem R72697 : Reach 72697 := rs (se 2 (by rfl) ⟨27261, by rfl⟩) R54523
theorem R40943 : Reach 40943 := rs (se 1 (by rfl) ⟨30707, by rfl⟩) R61415
theorem R41063 : Reach 41063 := rs (se 1 (by rfl) ⟨30797, by rfl⟩) R61595
theorem R172219 : Reach 172219 := rs (se 1 (by rfl) ⟨129164, by rfl⟩) R258329
theorem R41183 : Reach 41183 := rs (se 1 (by rfl) ⟨30887, by rfl⟩) R61775
theorem R41195 : Reach 41195 := rs (se 1 (by rfl) ⟨30896, by rfl⟩) R61793
theorem R41243 : Reach 41243 := rs (se 1 (by rfl) ⟨30932, by rfl⟩) R61865
theorem R41255 : Reach 41255 := rs (se 1 (by rfl) ⟨30941, by rfl⟩) R61883
theorem R74105 : Reach 74105 := rs (se 2 (by rfl) ⟨27789, by rfl⟩) R55579
theorem R139643 : Reach 139643 := rs (se 1 (by rfl) ⟨104732, by rfl⟩) R209465
theorem R369107 : Reach 369107 := rs (se 1 (by rfl) ⟨276830, by rfl⟩) R553661
theorem R41447 : Reach 41447 := rs (se 1 (by rfl) ⟨31085, by rfl⟩) R62171
theorem R41627 : Reach 41627 := rs (se 1 (by rfl) ⟨31220, by rfl⟩) R62441
theorem R107345 : Reach 107345 := rs (se 2 (by rfl) ⟨40254, by rfl⟩) R80509
theorem R13935563 : Reach 13935563 := rs (se 1 (by rfl) ⟨10451672, by rfl⟩) R20903345
theorem R42095 : Reach 42095 := rs (se 1 (by rfl) ⟨31571, by rfl⟩) R63143
theorem R42215 : Reach 42215 := rs (se 1 (by rfl) ⟨31661, by rfl⟩) R63323
theorem R42281 : Reach 42281 := rs (se 2 (by rfl) ⟨15855, by rfl⟩) R31711
theorem R75401 : Reach 75401 := rs (se 2 (by rfl) ⟨28275, by rfl⟩) R56551
theorem R338251 : Reach 338251 := rs (se 1 (by rfl) ⟨253688, by rfl⟩) R507377
theorem R43433 : Reach 43433 := rs (se 2 (by rfl) ⟨16287, by rfl⟩) R32575
theorem R108971 : Reach 108971 := rs (se 1 (by rfl) ⟨81728, by rfl⟩) R163457
theorem R43967 : Reach 43967 := rs (se 1 (by rfl) ⟨32975, by rfl⟩) R65951
theorem R44699 : Reach 44699 := rs (se 1 (by rfl) ⟨33524, by rfl⟩) R67049
theorem R175841 : Reach 175841 := rs (se 2 (by rfl) ⟨65940, by rfl⟩) R131881
theorem R77593 : Reach 77593 := rs (se 2 (by rfl) ⟨29097, by rfl⟩) R58195
theorem R45031 : Reach 45031 := rs (se 1 (by rfl) ⟨33773, by rfl⟩) R67547
theorem R45083 : Reach 45083 := rs (se 1 (by rfl) ⟨33812, by rfl⟩) R67625
theorem R2044115 : Reach 2044115 := rs (se 1 (by rfl) ⟨1533086, by rfl⟩) R3066173
theorem R45503 : Reach 45503 := rs (se 1 (by rfl) ⟨34127, by rfl⟩) R68255
theorem R111233 : Reach 111233 := rs (se 2 (by rfl) ⟨41712, by rfl⟩) R83425
theorem R3617561 : Reach 3617561 := rs (se 2 (by rfl) ⟨1356585, by rfl⟩) R2713171
theorem R45851 : Reach 45851 := rs (se 1 (by rfl) ⟨34388, by rfl⟩) R68777
theorem R571115 : Reach 571115 := rs (se 1 (by rfl) ⟨428336, by rfl⟩) R856673
theorem R210923 : Reach 210923 := rs (se 1 (by rfl) ⟨158192, by rfl⟩) R316385
theorem R178523 : Reach 178523 := rs (se 1 (by rfl) ⟨133892, by rfl⟩) R267785
theorem R211517 : Reach 211517 := rs (se 3 (by rfl) ⟨39659, by rfl⟩) R79319
theorem R408185 : Reach 408185 := rs (se 2 (by rfl) ⟨153069, by rfl⟩) R306139
theorem R48505 : Reach 48505 := rs (se 2 (by rfl) ⟨18189, by rfl⟩) R36379
theorem R2866747 : Reach 2866747 := rs (se 1 (by rfl) ⟨2150060, by rfl⟩) R4300121
theorem R114331 : Reach 114331 := rs (se 1 (by rfl) ⟨85748, by rfl⟩) R171497
theorem R82127 : Reach 82127 := rs (se 1 (by rfl) ⟨61595, by rfl⟩) R123191
theorem R377135 : Reach 377135 := rs (se 1 (by rfl) ⟨282851, by rfl⟩) R565703
theorem R49511 : Reach 49511 := rs (se 1 (by rfl) ⟨37133, by rfl⟩) R74267
theorem R49567 : Reach 49567 := rs (se 1 (by rfl) ⟨37175, by rfl⟩) R74351
theorem R213839 : Reach 213839 := rs (se 1 (by rfl) ⟨160379, by rfl⟩) R320759
theorem R246847 : Reach 246847 := rs (se 1 (by rfl) ⟨185135, by rfl⟩) R370271
theorem R83015 : Reach 83015 := rs (se 1 (by rfl) ⟨62261, by rfl⟩) R124523
theorem R50503 : Reach 50503 := rs (se 1 (by rfl) ⟨37877, by rfl⟩) R75755
theorem R50665 : Reach 50665 := rs (se 2 (by rfl) ⟨18999, by rfl⟩) R37999
theorem R50743 : Reach 50743 := rs (se 1 (by rfl) ⟨38057, by rfl⟩) R76115
theorem R149201 : Reach 149201 := rs (se 2 (by rfl) ⟨55950, by rfl⟩) R111901
theorem R1427543 : Reach 1427543 := rs (se 1 (by rfl) ⟨1070657, by rfl⟩) R2141315
theorem R2017817 : Reach 2017817 := rs (se 2 (by rfl) ⟨756681, by rfl⟩) R1513363
theorem R52967 : Reach 52967 := rs (se 1 (by rfl) ⟨39725, by rfl⟩) R79451
theorem R53183 : Reach 53183 := rs (se 1 (by rfl) ⟨39887, by rfl⟩) R79775
theorem R54607 : Reach 54607 := rs (se 1 (by rfl) ⟨40955, by rfl⟩) R81911
theorem R54857 : Reach 54857 := rs (se 2 (by rfl) ⟨20571, by rfl⟩) R41143
theorem R87799 : Reach 87799 := rs (se 1 (by rfl) ⟨65849, by rfl⟩) R131699
theorem R87935 : Reach 87935 := rs (se 1 (by rfl) ⟨65951, by rfl⟩) R131903
theorem R546749 : Reach 546749 := rs (se 3 (by rfl) ⟨102515, by rfl⟩) R205031
theorem R55417 : Reach 55417 := rs (se 2 (by rfl) ⟨20781, by rfl⟩) R41563
theorem R481619 : Reach 481619 := rs (se 1 (by rfl) ⟨361214, by rfl⟩) R722429
theorem R186887 : Reach 186887 := rs (se 1 (by rfl) ⟨140165, by rfl⟩) R280331
theorem R548207 : Reach 548207 := rs (se 1 (by rfl) ⟨411155, by rfl⟩) R822311
theorem R56801 : Reach 56801 := rs (se 2 (by rfl) ⟨21300, by rfl⟩) R42601
theorem R319439 : Reach 319439 := rs (se 1 (by rfl) ⟨239579, by rfl⟩) R479159
theorem R189175 : Reach 189175 := rs (se 1 (by rfl) ⟨141881, by rfl⟩) R283763
theorem R58153 : Reach 58153 := rs (se 2 (by rfl) ⟨21807, by rfl⟩) R43615
theorem R58495 : Reach 58495 := rs (se 1 (by rfl) ⟨43871, by rfl⟩) R87743
theorem R58715 : Reach 58715 := rs (se 1 (by rfl) ⟨44036, by rfl⟩) R88073
theorem R452299 : Reach 452299 := rs (se 1 (by rfl) ⟨339224, by rfl⟩) R678449
theorem R157427 : Reach 157427 := rs (se 1 (by rfl) ⟨118070, by rfl⟩) R236141
theorem R158183 : Reach 158183 := rs (se 1 (by rfl) ⟨118637, by rfl⟩) R237275
theorem R27119 : Reach 27119 := rs (se 1 (by rfl) ⟨20339, by rfl⟩) R40679
theorem R60059 : Reach 60059 := rs (se 1 (by rfl) ⟨45044, by rfl⟩) R90089
theorem R27303 : Reach 27303 := rs (se 1 (by rfl) ⟨20477, by rfl⟩) R40955
theorem R27343 : Reach 27343 := rs (se 1 (by rfl) ⟨20507, by rfl⟩) R41015
theorem R27423 : Reach 27423 := rs (se 1 (by rfl) ⟨20567, by rfl⟩) R41135
theorem R27559 : Reach 27559 := rs (se 1 (by rfl) ⟨20669, by rfl⟩) R41339
theorem R453599 : Reach 453599 := rs (se 1 (by rfl) ⟨340199, by rfl⟩) R680399
theorem R27675 : Reach 27675 := rs (se 1 (by rfl) ⟨20756, by rfl⟩) R41513
theorem R27739 : Reach 27739 := rs (se 1 (by rfl) ⟨20804, by rfl⟩) R41609
theorem R27879 : Reach 27879 := rs (se 1 (by rfl) ⟨20909, by rfl⟩) R41819
theorem R27903 : Reach 27903 := rs (se 1 (by rfl) ⟨20927, by rfl⟩) R41855
theorem R27951 : Reach 27951 := rs (se 1 (by rfl) ⟨20963, by rfl⟩) R41927
theorem R126299 : Reach 126299 := rs (se 1 (by rfl) ⟨94724, by rfl⟩) R189449
theorem R28095 : Reach 28095 := rs (se 1 (by rfl) ⟨21071, by rfl⟩) R42143
theorem R93631 : Reach 93631 := rs (se 1 (by rfl) ⟨70223, by rfl⟩) R140447
theorem R28191 : Reach 28191 := rs (se 1 (by rfl) ⟨21143, by rfl⟩) R42287
theorem R61031 : Reach 61031 := rs (se 1 (by rfl) ⟨45773, by rfl⟩) R91547
theorem R1207943 : Reach 1207943 := rs (se 1 (by rfl) ⟨905957, by rfl⟩) R1811915
theorem R28319 : Reach 28319 := rs (se 1 (by rfl) ⟨21239, by rfl⟩) R42479
theorem R28327 : Reach 28327 := rs (se 1 (by rfl) ⟨21245, by rfl⟩) R42491
theorem R28351 : Reach 28351 := rs (se 1 (by rfl) ⟨21263, by rfl⟩) R42527
theorem R28447 : Reach 28447 := rs (se 1 (by rfl) ⟨21335, by rfl⟩) R42671
theorem R28507 : Reach 28507 := rs (se 1 (by rfl) ⟨21380, by rfl⟩) R42761
theorem R28527 : Reach 28527 := rs (se 1 (by rfl) ⟨21395, by rfl⟩) R42791
theorem R290789 : Reach 290789 := rs (se 4 (by rfl) ⟨27261, by rfl⟩) R54523
theorem R61631 : Reach 61631 := rs (se 1 (by rfl) ⟨46223, by rfl⟩) R92447
theorem R28927 : Reach 28927 := rs (se 1 (by rfl) ⟨21695, by rfl⟩) R43391
theorem R29087 : Reach 29087 := rs (se 1 (by rfl) ⟨21815, by rfl⟩) R43631
theorem R29231 : Reach 29231 := rs (se 1 (by rfl) ⟨21923, by rfl⟩) R43847
theorem R29479 : Reach 29479 := rs (se 1 (by rfl) ⟨22109, by rfl⟩) R44219
theorem R62279 : Reach 62279 := rs (se 1 (by rfl) ⟨46709, by rfl⟩) R93419
theorem R29631 : Reach 29631 := rs (se 1 (by rfl) ⟨22223, by rfl⟩) R44447
theorem R95215 : Reach 95215 := rs (se 1 (by rfl) ⟨71411, by rfl⟩) R142823
theorem R357473 : Reach 357473 := rs (se 2 (by rfl) ⟨134052, by rfl⟩) R268105
theorem R29807 : Reach 29807 := rs (se 1 (by rfl) ⟨22355, by rfl⟩) R44711
theorem R29823 : Reach 29823 := rs (se 1 (by rfl) ⟨22367, by rfl⟩) R44735
theorem R29887 : Reach 29887 := rs (se 1 (by rfl) ⟨22415, by rfl⟩) R44831
theorem R30079 : Reach 30079 := rs (se 1 (by rfl) ⟨22559, by rfl⟩) R45119
theorem R226799 : Reach 226799 := rs (se 1 (by rfl) ⟨170099, by rfl⟩) R340199
theorem R30207 : Reach 30207 := rs (se 1 (by rfl) ⟨22655, by rfl⟩) R45311
theorem R30235 : Reach 30235 := rs (se 1 (by rfl) ⟨22676, by rfl⟩) R45353
theorem R30415 : Reach 30415 := rs (se 1 (by rfl) ⟨22811, by rfl⟩) R45623
theorem R30575 : Reach 30575 := rs (se 1 (by rfl) ⟨22931, by rfl⟩) R45863
theorem R128897 : Reach 128897 := rs (se 2 (by rfl) ⟨48336, by rfl⟩) R96673
theorem R30655 : Reach 30655 := rs (se 1 (by rfl) ⟨22991, by rfl⟩) R45983
theorem R30975 : Reach 30975 := rs (se 1 (by rfl) ⟨23231, by rfl⟩) R46463
theorem R63827 : Reach 63827 := rs (se 1 (by rfl) ⟨47870, by rfl⟩) R95741
theorem R31079 : Reach 31079 := rs (se 1 (by rfl) ⟨23309, by rfl⟩) R46619
theorem R31199 : Reach 31199 := rs (se 1 (by rfl) ⟨23399, by rfl⟩) R46799
theorem R457325 : Reach 457325 := rs (se 3 (by rfl) ⟨85748, by rfl⟩) R171497
theorem R293665 : Reach 293665 := rs (se 2 (by rfl) ⟨110124, by rfl⟩) R220249
theorem R64385 : Reach 64385 := rs (se 2 (by rfl) ⟨24144, by rfl⟩) R48289
theorem R65663 : Reach 65663 := rs (se 1 (by rfl) ⟨49247, by rfl⟩) R98495
theorem R33007 : Reach 33007 := rs (se 1 (by rfl) ⟨24755, by rfl⟩) R49511
theorem R229625 : Reach 229625 := rs (se 2 (by rfl) ⟨86109, by rfl⟩) R172219
theorem R66089 : Reach 66089 := rs (se 2 (by rfl) ⟨24783, by rfl⟩) R49567
theorem R66095 : Reach 66095 := rs (se 1 (by rfl) ⟨49571, by rfl⟩) R99143
theorem R99467 : Reach 99467 := rs (se 1 (by rfl) ⟨74600, by rfl⟩) R149201
theorem R1180979 : Reach 1180979 := rs (se 1 (by rfl) ⟨885734, by rfl⟩) R1771469
theorem R951695 : Reach 951695 := rs (se 1 (by rfl) ⟨713771, by rfl⟩) R1427543
theorem R329129 : Reach 329129 := rs (se 2 (by rfl) ⟨123423, by rfl⟩) R246847
theorem R1345211 : Reach 1345211 := rs (se 1 (by rfl) ⟨1008908, by rfl⟩) R2017817
theorem R67337 : Reach 67337 := rs (se 2 (by rfl) ⟨25251, by rfl⟩) R50503
theorem R67391 : Reach 67391 := rs (se 1 (by rfl) ⟨50543, by rfl⟩) R101087
theorem R67499 : Reach 67499 := rs (se 1 (by rfl) ⟨50624, by rfl⟩) R101249
theorem R67553 : Reach 67553 := rs (se 2 (by rfl) ⟨25332, by rfl⟩) R50665
theorem R67657 : Reach 67657 := rs (se 2 (by rfl) ⟨25371, by rfl⟩) R50743
theorem R198935 : Reach 198935 := rs (se 1 (by rfl) ⟨149201, by rfl⟩) R298403
theorem R35311 : Reach 35311 := rs (se 1 (by rfl) ⟨26483, by rfl⟩) R52967
theorem R68327 : Reach 68327 := rs (se 1 (by rfl) ⟨51245, by rfl⟩) R102491
theorem R199675 : Reach 199675 := rs (se 1 (by rfl) ⟨149756, by rfl⟩) R299513
theorem R101789 : Reach 101789 := rs (se 3 (by rfl) ⟨19085, by rfl⟩) R38171
theorem R69263 : Reach 69263 := rs (se 1 (by rfl) ⟨51947, by rfl⟩) R103895
theorem R69407 : Reach 69407 := rs (se 1 (by rfl) ⟨52055, by rfl⟩) R104111
theorem R364499 : Reach 364499 := rs (se 1 (by rfl) ⟨273374, by rfl⟩) R546749
theorem R365471 : Reach 365471 := rs (se 1 (by rfl) ⟨274103, by rfl⟩) R548207
theorem R103457 : Reach 103457 := rs (se 2 (by rfl) ⟨38796, by rfl⟩) R77593
theorem R38009 : Reach 38009 := rs (se 2 (by rfl) ⟨14253, by rfl⟩) R28507
theorem R71563 : Reach 71563 := rs (se 1 (by rfl) ⟨53672, by rfl⟩) R107345
theorem R39143 : Reach 39143 := rs (se 1 (by rfl) ⟨29357, by rfl⟩) R58715
theorem R39305 : Reach 39305 := rs (se 2 (by rfl) ⟨14739, by rfl⟩) R29479
theorem R104951 : Reach 104951 := rs (se 1 (by rfl) ⟨78713, by rfl⟩) R157427
theorem R72647 : Reach 72647 := rs (se 1 (by rfl) ⟨54485, by rfl⟩) R108971
theorem R105455 : Reach 105455 := rs (se 1 (by rfl) ⟨79091, by rfl⟩) R158183
theorem R72809 : Reach 72809 := rs (se 2 (by rfl) ⟨27303, by rfl⟩) R54607
theorem R302399 : Reach 302399 := rs (se 1 (by rfl) ⟨226799, by rfl⟩) R453599
theorem R41087 : Reach 41087 := rs (se 1 (by rfl) ⟨30815, by rfl⟩) R61631
theorem R73889 : Reach 73889 := rs (se 2 (by rfl) ⟨27708, by rfl⟩) R55417
theorem R74155 : Reach 74155 := rs (se 1 (by rfl) ⟨55616, by rfl⟩) R111233
theorem R41519 : Reach 41519 := rs (se 1 (by rfl) ⟨31139, by rfl⟩) R62279
theorem R238315 : Reach 238315 := rs (se 1 (by rfl) ⟨178736, by rfl⟩) R357473
theorem R336797 : Reach 336797 := rs (se 3 (by rfl) ⟨63149, by rfl⟩) R126299
theorem R140615 : Reach 140615 := rs (se 1 (by rfl) ⟨105461, by rfl⟩) R210923
theorem R42551 : Reach 42551 := rs (se 1 (by rfl) ⟨31913, by rfl⟩) R63827
theorem R141011 : Reach 141011 := rs (se 1 (by rfl) ⟨105758, by rfl⟩) R211517
theorem R304883 : Reach 304883 := rs (se 1 (by rfl) ⟨228662, by rfl⟩) R457325
theorem R272123 : Reach 272123 := rs (se 1 (by rfl) ⟨204092, by rfl⟩) R408185
theorem R42923 : Reach 42923 := rs (se 1 (by rfl) ⟨32192, by rfl⟩) R64385
theorem R141821 : Reach 141821 := rs (se 3 (by rfl) ⟨26591, by rfl⟩) R53183
theorem R43817 : Reach 43817 := rs (se 2 (by rfl) ⟨16431, by rfl⟩) R32863
theorem R44123 : Reach 44123 := rs (se 1 (by rfl) ⟨33092, by rfl⟩) R66185
theorem R142559 : Reach 142559 := rs (se 1 (by rfl) ⟨106919, by rfl⟩) R213839
theorem R44459 : Reach 44459 := rs (se 1 (by rfl) ⟨33344, by rfl⟩) R66689
theorem R44591 : Reach 44591 := rs (se 1 (by rfl) ⟨33443, by rfl⟩) R66887
theorem R77537 : Reach 77537 := rs (se 2 (by rfl) ⟨29076, by rfl⟩) R58153
theorem R77993 : Reach 77993 := rs (se 2 (by rfl) ⟨29247, by rfl⟩) R58495
theorem R603065 : Reach 603065 := rs (se 2 (by rfl) ⟨226149, by rfl⟩) R452299
theorem R46015 : Reach 46015 := rs (se 1 (by rfl) ⟨34511, by rfl⟩) R69023
theorem R46457 : Reach 46457 := rs (se 2 (by rfl) ⟨17421, by rfl⟩) R34843
theorem R636623 : Reach 636623 := rs (se 1 (by rfl) ⟨477467, by rfl⟩) R954935
theorem R46919 : Reach 46919 := rs (se 1 (by rfl) ⟨35189, by rfl⟩) R70379
theorem R3389303 : Reach 3389303 := rs (se 1 (by rfl) ⟨2541977, by rfl⟩) R5083955
theorem R112859 : Reach 112859 := rs (se 1 (by rfl) ⟨84644, by rfl⟩) R169289
theorem R47911 : Reach 47911 := rs (se 1 (by rfl) ⟨35933, by rfl⟩) R71867
theorem R146285 : Reach 146285 := rs (se 3 (by rfl) ⟨27428, by rfl⟩) R54857
theorem R113831 : Reach 113831 := rs (se 1 (by rfl) ⟨85373, by rfl⟩) R170747
theorem R310553 : Reach 310553 := rs (se 2 (by rfl) ⟨116457, by rfl⟩) R232915
theorem R212959 : Reach 212959 := rs (se 1 (by rfl) ⟨159719, by rfl⟩) R319439
theorem R49403 : Reach 49403 := rs (se 1 (by rfl) ⟨37052, by rfl⟩) R74105
theorem R246071 : Reach 246071 := rs (se 1 (by rfl) ⟨184553, by rfl⟩) R369107
theorem R9290375 : Reach 9290375 := rs (se 1 (by rfl) ⟨6967781, by rfl⟩) R13935563
theorem R50267 : Reach 50267 := rs (se 1 (by rfl) ⟨37700, by rfl⟩) R75401
theorem R83197 : Reach 83197 := rs (se 3 (by rfl) ⟨15599, by rfl⟩) R31199
theorem R117065 : Reach 117065 := rs (se 2 (by rfl) ⟨43899, by rfl⟩) R87799
theorem R51553 : Reach 51553 := rs (se 2 (by rfl) ⟨19332, by rfl⟩) R38665
theorem R805295 : Reach 805295 := rs (se 1 (by rfl) ⟨603971, by rfl⟩) R1207943
theorem R117227 : Reach 117227 := rs (se 1 (by rfl) ⟨87920, by rfl⟩) R175841
theorem R1362743 : Reach 1362743 := rs (se 1 (by rfl) ⟨1022057, by rfl⟩) R2044115
theorem R2411707 : Reach 2411707 := rs (se 1 (by rfl) ⟨1808780, by rfl⟩) R3617561
theorem R151199 : Reach 151199 := rs (se 1 (by rfl) ⟨113399, by rfl⟩) R226799
theorem R380743 : Reach 380743 := rs (se 1 (by rfl) ⟨285557, by rfl⟩) R571115
theorem R85931 : Reach 85931 := rs (se 1 (by rfl) ⟨64448, by rfl⟩) R128897
theorem R151469 : Reach 151469 := rs (se 3 (by rfl) ⟨28400, by rfl⟩) R56801
theorem R937973 : Reach 937973 := rs (se 5 (by rfl) ⟨43967, by rfl⟩) R87935
theorem R119015 : Reach 119015 := rs (se 1 (by rfl) ⟨89261, by rfl⟩) R178523
theorem R3822329 : Reach 3822329 := rs (se 2 (by rfl) ⟨1433373, by rfl⟩) R2866747
theorem R152441 : Reach 152441 := rs (se 2 (by rfl) ⟨57165, by rfl⟩) R114331
theorem R54751 : Reach 54751 := rs (se 1 (by rfl) ⟨41063, by rfl⟩) R82127
theorem R251423 : Reach 251423 := rs (se 1 (by rfl) ⟨188567, by rfl⟩) R377135
theorem R284251 : Reach 284251 := rs (se 1 (by rfl) ⟨213188, by rfl⟩) R426377
theorem R55343 : Reach 55343 := rs (se 1 (by rfl) ⟨41507, by rfl⟩) R83015
theorem R252233 : Reach 252233 := rs (se 2 (by rfl) ⟨94587, by rfl⟩) R189175
theorem R451001 : Reach 451001 := rs (se 2 (by rfl) ⟨169125, by rfl⟩) R338251
theorem R321079 : Reach 321079 := rs (se 1 (by rfl) ⟨240809, by rfl⟩) R481619
theorem R124591 : Reach 124591 := rs (se 1 (by rfl) ⟨93443, by rfl⟩) R186887
theorem R124841 : Reach 124841 := rs (se 2 (by rfl) ⟨46815, by rfl⟩) R93631
theorem R60041 : Reach 60041 := rs (se 2 (by rfl) ⟨22515, by rfl⟩) R45031
theorem R27295 : Reach 27295 := rs (se 1 (by rfl) ⟨20471, by rfl⟩) R40943
theorem R27375 : Reach 27375 := rs (se 1 (by rfl) ⟨20531, by rfl⟩) R41063
theorem R27455 : Reach 27455 := rs (se 1 (by rfl) ⟨20591, by rfl⟩) R41183
theorem R27463 : Reach 27463 := rs (se 1 (by rfl) ⟨20597, by rfl⟩) R41195
theorem R27495 : Reach 27495 := rs (se 1 (by rfl) ⟨20621, by rfl⟩) R41243
theorem R27503 : Reach 27503 := rs (se 1 (by rfl) ⟨20627, by rfl⟩) R41255
theorem R93095 : Reach 93095 := rs (se 1 (by rfl) ⟨69821, by rfl⟩) R139643
theorem R27631 : Reach 27631 := rs (se 1 (by rfl) ⟨20723, by rfl⟩) R41447
theorem R27751 : Reach 27751 := rs (se 1 (by rfl) ⟨20813, by rfl⟩) R41627
theorem R28063 : Reach 28063 := rs (se 1 (by rfl) ⟨21047, by rfl⟩) R42095
theorem R28143 : Reach 28143 := rs (se 1 (by rfl) ⟨21107, by rfl⟩) R42215
theorem R28187 : Reach 28187 := rs (se 1 (by rfl) ⟨21140, by rfl⟩) R42281
theorem R126953 : Reach 126953 := rs (se 2 (by rfl) ⟨47607, by rfl⟩) R95215
theorem R28955 : Reach 28955 := rs (se 1 (by rfl) ⟨21716, by rfl⟩) R43433
theorem R160157 : Reach 160157 := rs (se 3 (by rfl) ⟨30029, by rfl⟩) R60059
theorem R29311 : Reach 29311 := rs (se 1 (by rfl) ⟨21983, by rfl⟩) R43967
theorem R95201 : Reach 95201 := rs (se 2 (by rfl) ⟨35700, by rfl⟩) R71401
theorem R29799 : Reach 29799 := rs (se 1 (by rfl) ⟨22349, by rfl⟩) R44699
theorem R193859 : Reach 193859 := rs (se 1 (by rfl) ⟨145394, by rfl⟩) R290789
theorem R30055 : Reach 30055 := rs (se 1 (by rfl) ⟨22541, by rfl⟩) R45083
theorem R30335 : Reach 30335 := rs (se 1 (by rfl) ⟨22751, by rfl⟩) R45503
theorem R30567 : Reach 30567 := rs (se 1 (by rfl) ⟨22925, by rfl⟩) R45851
theorem R391553 : Reach 391553 := rs (se 2 (by rfl) ⟨146832, by rfl⟩) R293665
theorem R96929 : Reach 96929 := rs (se 2 (by rfl) ⟨36348, by rfl⟩) R72697
theorem R162749 : Reach 162749 := rs (se 3 (by rfl) ⟨30515, by rfl⟩) R61031
theorem R64673 : Reach 64673 := rs (se 2 (by rfl) ⟨24252, by rfl⟩) R48505
theorem R622525 : Reach 622525 := rs (se 3 (by rfl) ⟨116723, by rfl⟩) R233447
theorem R32935 : Reach 32935 := rs (se 1 (by rfl) ⟨24701, by rfl⟩) R49403
theorem R164047 : Reach 164047 := rs (se 1 (by rfl) ⟨123035, by rfl⟩) R246071
theorem R6193583 : Reach 6193583 := rs (se 1 (by rfl) ⟨4645187, by rfl⟩) R9290375
theorem R98873 : Reach 98873 := rs (se 2 (by rfl) ⟨37077, by rfl⟩) R74155
theorem R33511 : Reach 33511 := rs (se 1 (by rfl) ⟨25133, by rfl⟩) R50267
theorem R66311 : Reach 66311 := rs (se 1 (by rfl) ⟨49733, by rfl⟩) R99467
theorem R787319 : Reach 787319 := rs (se 1 (by rfl) ⟨590489, by rfl⟩) R1180979
theorem R132623 : Reach 132623 := rs (se 1 (by rfl) ⟨99467, by rfl⟩) R198935
theorem R10192877 : Reach 10192877 := rs (se 3 (by rfl) ⟨1911164, by rfl⟩) R3822329
theorem R428105 : Reach 428105 := rs (se 2 (by rfl) ⟨160539, by rfl⟩) R321079
theorem R166121 : Reach 166121 := rs (se 2 (by rfl) ⟨62295, by rfl⟩) R124591
theorem R67859 : Reach 67859 := rs (se 1 (by rfl) ⟨50894, by rfl⟩) R101789
theorem R100799 : Reach 100799 := rs (se 1 (by rfl) ⟨75599, by rfl⟩) R151199
theorem R100979 : Reach 100979 := rs (se 1 (by rfl) ⟨75734, by rfl⟩) R151469
theorem R625315 : Reach 625315 := rs (se 1 (by rfl) ⟨468986, by rfl⟩) R937973
theorem R101357 : Reach 101357 := rs (se 3 (by rfl) ⟨19004, by rfl⟩) R38009
theorem R68737 : Reach 68737 := rs (se 2 (by rfl) ⟨25776, by rfl⟩) R51553
theorem R101627 : Reach 101627 := rs (se 1 (by rfl) ⟨76220, by rfl⟩) R152441
theorem R68971 : Reach 68971 := rs (se 1 (by rfl) ⟨51728, by rfl⟩) R103457
theorem R167615 : Reach 167615 := rs (se 1 (by rfl) ⟨125711, by rfl⟩) R251423
theorem R168155 : Reach 168155 := rs (se 1 (by rfl) ⟨126116, by rfl⟩) R252233
theorem R3215609 : Reach 3215609 := rs (se 2 (by rfl) ⟨1205853, by rfl⟩) R2411707
theorem R69967 : Reach 69967 := rs (se 1 (by rfl) ⟨52475, by rfl⟩) R104951
theorem R37417 : Reach 37417 := rs (se 2 (by rfl) ⟨14031, by rfl⟩) R28063
theorem R70303 : Reach 70303 := rs (se 1 (by rfl) ⟨52727, by rfl⟩) R105455
theorem R201599 : Reach 201599 := rs (se 1 (by rfl) ⟨151199, by rfl⟩) R302399
theorem R300667 : Reach 300667 := rs (se 1 (by rfl) ⟨225500, by rfl⟩) R451001
theorem R104381 : Reach 104381 := rs (se 3 (by rfl) ⟨19571, by rfl⟩) R39143
theorem R104813 : Reach 104813 := rs (se 3 (by rfl) ⟨19652, by rfl⟩) R39305
theorem R203255 : Reach 203255 := rs (se 1 (by rfl) ⟨152441, by rfl⟩) R304883
theorem R40027 : Reach 40027 := rs (se 1 (by rfl) ⟨30020, by rfl⟩) R60041
theorem R73001 : Reach 73001 := rs (se 2 (by rfl) ⟨27375, by rfl⟩) R54751
theorem R106771 : Reach 106771 := rs (se 1 (by rfl) ⟨80078, by rfl⟩) R160157
theorem R402043 : Reach 402043 := rs (se 1 (by rfl) ⟨301532, by rfl⟩) R603065
theorem R75239 : Reach 75239 := rs (se 1 (by rfl) ⟨56429, by rfl⟩) R112859
theorem R108499 : Reach 108499 := rs (se 1 (by rfl) ⟨81374, by rfl⟩) R162749
theorem R43115 : Reach 43115 := rs (se 1 (by rfl) ⟨32336, by rfl⟩) R64673
theorem R75887 : Reach 75887 := rs (se 1 (by rfl) ⟨56915, by rfl⟩) R113831
theorem R207035 : Reach 207035 := rs (se 1 (by rfl) ⟨155276, by rfl⟩) R310553
theorem R830033 : Reach 830033 := rs (se 2 (by rfl) ⟨311262, by rfl⟩) R622525
theorem R43775 : Reach 43775 := rs (se 1 (by rfl) ⟨32831, by rfl⟩) R65663
theorem R44009 : Reach 44009 := rs (se 2 (by rfl) ⟨16503, by rfl⟩) R33007
theorem R109565 : Reach 109565 := rs (se 3 (by rfl) ⟨20543, by rfl⟩) R41087
theorem R44059 : Reach 44059 := rs (se 1 (by rfl) ⟨33044, by rfl⟩) R66089
theorem R44063 : Reach 44063 := rs (se 1 (by rfl) ⟨33047, by rfl⟩) R66095
theorem R77213 : Reach 77213 := rs (se 3 (by rfl) ⟨14477, by rfl⟩) R28955
theorem R634463 : Reach 634463 := rs (se 1 (by rfl) ⟨475847, by rfl⟩) R951695
theorem R896807 : Reach 896807 := rs (se 1 (by rfl) ⟨672605, by rfl⟩) R1345211
theorem R44891 : Reach 44891 := rs (se 1 (by rfl) ⟨33668, by rfl⟩) R67337
theorem R44927 : Reach 44927 := rs (se 1 (by rfl) ⟨33695, by rfl⟩) R67391
theorem R44999 : Reach 44999 := rs (se 1 (by rfl) ⟨33749, by rfl⟩) R67499
theorem R45035 : Reach 45035 := rs (se 1 (by rfl) ⟨33776, by rfl⟩) R67553
theorem R110717 : Reach 110717 := rs (se 3 (by rfl) ⟨20759, by rfl⟩) R41519
theorem R78043 : Reach 78043 := rs (se 1 (by rfl) ⟨58532, by rfl⟩) R117065
theorem R536863 : Reach 536863 := rs (se 1 (by rfl) ⟨402647, by rfl⟩) R805295
theorem R110929 : Reach 110929 := rs (se 2 (by rfl) ⟨41598, by rfl⟩) R83197
theorem R45551 : Reach 45551 := rs (se 1 (by rfl) ⟨34163, by rfl⟩) R68327
theorem R46175 : Reach 46175 := rs (se 1 (by rfl) ⟨34631, by rfl⟩) R69263
theorem R46271 : Reach 46271 := rs (se 1 (by rfl) ⟨34703, by rfl⟩) R69407
theorem R242999 : Reach 242999 := rs (se 1 (by rfl) ⟨182249, by rfl⟩) R364499
theorem R79343 : Reach 79343 := rs (se 1 (by rfl) ⟨59507, by rfl⟩) R119015
theorem R243647 : Reach 243647 := rs (se 1 (by rfl) ⟨182735, by rfl⟩) R365471
theorem R47081 : Reach 47081 := rs (se 2 (by rfl) ⟨17655, by rfl⟩) R35311
theorem R48431 : Reach 48431 := rs (se 1 (by rfl) ⟨36323, by rfl⟩) R72647
theorem R48539 : Reach 48539 := rs (se 1 (by rfl) ⟨36404, by rfl⟩) R72809
theorem R245413 : Reach 245413 := rs (se 4 (by rfl) ⟨23007, by rfl⟩) R46015
theorem R1064933 : Reach 1064933 := rs (se 4 (by rfl) ⟨99837, by rfl⟩) R199675
theorem R49259 : Reach 49259 := rs (se 1 (by rfl) ⟨36944, by rfl⟩) R73889
theorem R147581 : Reach 147581 := rs (se 3 (by rfl) ⟨27671, by rfl⟩) R55343
theorem R181415 : Reach 181415 := rs (se 1 (by rfl) ⟨136061, by rfl⟩) R272123
theorem R83227 : Reach 83227 := rs (se 1 (by rfl) ⟨62420, by rfl⟩) R124841
theorem R312605 : Reach 312605 := rs (se 3 (by rfl) ⟨58613, by rfl⟩) R117227
theorem R379001 : Reach 379001 := rs (se 2 (by rfl) ⟨142125, by rfl⟩) R284251
theorem R51691 : Reach 51691 := rs (se 1 (by rfl) ⟨38768, by rfl⟩) R77537
theorem R84635 : Reach 84635 := rs (se 1 (by rfl) ⟨63476, by rfl⟩) R126953
theorem R51995 : Reach 51995 := rs (se 1 (by rfl) ⟨38996, by rfl⟩) R77993
theorem R283945 : Reach 283945 := rs (se 2 (by rfl) ⟨106479, by rfl⟩) R212959
theorem R153083 : Reach 153083 := rs (se 1 (by rfl) ⟨114812, by rfl⟩) R229625
theorem R219419 : Reach 219419 := rs (se 1 (by rfl) ⟨164564, by rfl⟩) R329129
theorem R317753 : Reach 317753 := rs (se 2 (by rfl) ⟨119157, by rfl⟩) R238315
theorem R908495 : Reach 908495 := rs (se 1 (by rfl) ⟨681371, by rfl⟩) R1362743
theorem R57287 : Reach 57287 := rs (se 1 (by rfl) ⟨42965, by rfl⟩) R85931
theorem R90209 : Reach 90209 := rs (se 2 (by rfl) ⟨33828, by rfl⟩) R67657
theorem R9038141 : Reach 9038141 := rs (se 3 (by rfl) ⟨1694651, by rfl⟩) R3389303
theorem R27391 : Reach 27391 := rs (se 1 (by rfl) ⟨20543, by rfl⟩) R41087
theorem R27679 : Reach 27679 := rs (se 1 (by rfl) ⟨20759, by rfl⟩) R41519
theorem R224531 : Reach 224531 := rs (se 1 (by rfl) ⟨168398, by rfl⟩) R336797
theorem R93743 : Reach 93743 := rs (se 1 (by rfl) ⟨70307, by rfl⟩) R140615
theorem R28367 : Reach 28367 := rs (se 1 (by rfl) ⟨21275, by rfl⟩) R42551
theorem R94007 : Reach 94007 := rs (se 1 (by rfl) ⟨70505, by rfl⟩) R141011
theorem R28615 : Reach 28615 := rs (se 1 (by rfl) ⟨21461, by rfl⟩) R42923
theorem R94547 : Reach 94547 := rs (se 1 (by rfl) ⟨70910, by rfl⟩) R141821
theorem R29211 : Reach 29211 := rs (se 1 (by rfl) ⟨21908, by rfl⟩) R43817
theorem R62063 : Reach 62063 := rs (se 1 (by rfl) ⟨46547, by rfl⟩) R93095
theorem R29415 : Reach 29415 := rs (se 1 (by rfl) ⟨22061, by rfl⟩) R44123
theorem R95039 : Reach 95039 := rs (se 1 (by rfl) ⟨71279, by rfl⟩) R142559
theorem R29639 : Reach 29639 := rs (se 1 (by rfl) ⟨22229, by rfl⟩) R44459
theorem R29727 : Reach 29727 := rs (se 1 (by rfl) ⟨22295, by rfl⟩) R44591
theorem R95417 : Reach 95417 := rs (se 2 (by rfl) ⟨35781, by rfl⟩) R71563
theorem R63467 : Reach 63467 := rs (se 1 (by rfl) ⟨47600, by rfl⟩) R95201
theorem R129239 : Reach 129239 := rs (se 1 (by rfl) ⟨96929, by rfl⟩) R193859
theorem R30971 : Reach 30971 := rs (se 1 (by rfl) ⟨23228, by rfl⟩) R46457
theorem R63881 : Reach 63881 := rs (se 2 (by rfl) ⟨23955, by rfl⟩) R47911
theorem R424415 : Reach 424415 := rs (se 1 (by rfl) ⟨318311, by rfl⟩) R636623
theorem R31279 : Reach 31279 := rs (se 1 (by rfl) ⟨23459, by rfl⟩) R46919
theorem R261035 : Reach 261035 := rs (se 1 (by rfl) ⟨195776, by rfl⟩) R391553
theorem R2030629 : Reach 2030629 := rs (se 4 (by rfl) ⟨190371, by rfl⟩) R380743
theorem R64619 : Reach 64619 := rs (se 1 (by rfl) ⟨48464, by rfl⟩) R96929
theorem R97523 : Reach 97523 := rs (se 1 (by rfl) ⟨73142, by rfl⟩) R146285
theorem R98387 : Reach 98387 := rs (se 1 (by rfl) ⟨73790, by rfl⟩) R147581
theorem R131357 : Reach 131357 := rs (se 3 (by rfl) ⟨24629, by rfl⟩) R49259
theorem R4129055 : Reach 4129055 := rs (se 1 (by rfl) ⟨3096791, by rfl⟩) R6193583
theorem R65915 : Reach 65915 := rs (se 1 (by rfl) ⟨49436, by rfl⟩) R98873
theorem R524879 : Reach 524879 := rs (se 1 (by rfl) ⟨393659, by rfl⟩) R787319
theorem R67199 : Reach 67199 := rs (se 1 (by rfl) ⟨50399, by rfl⟩) R100799
theorem R67319 : Reach 67319 := rs (se 1 (by rfl) ⟨50489, by rfl⟩) R100979
theorem R34663 : Reach 34663 := rs (se 1 (by rfl) ⟨25997, by rfl⟩) R51995
theorem R67571 : Reach 67571 := rs (se 1 (by rfl) ⟨50678, by rfl⟩) R101357
theorem R67751 : Reach 67751 := rs (se 1 (by rfl) ⟨50813, by rfl⟩) R101627
theorem R134399 : Reach 134399 := rs (se 1 (by rfl) ⟨100799, by rfl⟩) R201599
theorem R68921 : Reach 68921 := rs (se 2 (by rfl) ⟨25845, by rfl⟩) R51691
theorem R102055 : Reach 102055 := rs (se 1 (by rfl) ⟨76541, by rfl⟩) R153083
theorem R69587 : Reach 69587 := rs (se 1 (by rfl) ⟨52190, by rfl⟩) R104381
theorem R69875 : Reach 69875 := rs (se 1 (by rfl) ⟨52406, by rfl⟩) R104813
theorem R135503 : Reach 135503 := rs (se 1 (by rfl) ⟨101627, by rfl⟩) R203255
theorem R104057 : Reach 104057 := rs (se 2 (by rfl) ⟨39021, by rfl⟩) R78043
theorem R138023 : Reach 138023 := rs (se 1 (by rfl) ⟨103517, by rfl⟩) R207035
theorem R73043 : Reach 73043 := rs (se 1 (by rfl) ⟨54782, by rfl⟩) R109565
theorem R400889 : Reach 400889 := rs (se 2 (by rfl) ⟨150333, by rfl⟩) R300667
theorem R597871 : Reach 597871 := rs (se 1 (by rfl) ⟨448403, by rfl⟩) R896807
theorem R73811 : Reach 73811 := rs (se 1 (by rfl) ⟨55358, by rfl⟩) R110717
theorem R41375 : Reach 41375 := rs (se 1 (by rfl) ⟨31031, by rfl⟩) R62063
theorem R41705 : Reach 41705 := rs (se 2 (by rfl) ⟨15639, by rfl⟩) R31279
theorem R42311 : Reach 42311 := rs (se 1 (by rfl) ⟨31733, by rfl⟩) R63467
theorem R42587 : Reach 42587 := rs (se 1 (by rfl) ⟨31940, by rfl⟩) R63881
theorem R174023 : Reach 174023 := rs (se 1 (by rfl) ⟨130517, by rfl⟩) R261035
theorem R43079 : Reach 43079 := rs (se 1 (by rfl) ⟨32309, by rfl⟩) R64619
theorem R43913 : Reach 43913 := rs (se 2 (by rfl) ⟨16467, by rfl⟩) R32935
theorem R142361 : Reach 142361 := rs (se 2 (by rfl) ⟨53385, by rfl⟩) R106771
theorem R44207 : Reach 44207 := rs (se 1 (by rfl) ⟨33155, by rfl⟩) R66311
theorem R536057 : Reach 536057 := rs (se 2 (by rfl) ⟨201021, by rfl⟩) R402043
theorem R208403 : Reach 208403 := rs (se 1 (by rfl) ⟨156302, by rfl⟩) R312605
theorem R44681 : Reach 44681 := rs (se 2 (by rfl) ⟨16755, by rfl⟩) R33511
theorem R6795251 : Reach 6795251 := rs (se 1 (by rfl) ⟨5096438, by rfl⟩) R10192877
theorem R110747 : Reach 110747 := rs (se 1 (by rfl) ⟨83060, by rfl⟩) R166121
theorem R45239 : Reach 45239 := rs (se 1 (by rfl) ⟨33929, by rfl⟩) R67859
theorem R110969 : Reach 110969 := rs (se 2 (by rfl) ⟨41613, by rfl⟩) R83227
theorem R373157 : Reach 373157 := rs (se 4 (by rfl) ⟨34983, by rfl⟩) R69967
theorem R111743 : Reach 111743 := rs (se 1 (by rfl) ⟨83807, by rfl⟩) R167615
theorem R144665 : Reach 144665 := rs (se 2 (by rfl) ⟨54249, by rfl⟩) R108499
theorem R112103 : Reach 112103 := rs (se 1 (by rfl) ⟨84077, by rfl⟩) R168155
theorem R2143739 : Reach 2143739 := rs (se 1 (by rfl) ⟨1607804, by rfl⟩) R3215609
theorem R833753 : Reach 833753 := rs (se 2 (by rfl) ⟨312657, by rfl⟩) R625315
theorem R146279 : Reach 146279 := rs (se 1 (by rfl) ⟨109709, by rfl⟩) R219419
theorem R211835 : Reach 211835 := rs (se 1 (by rfl) ⟨158876, by rfl⟩) R317753
theorem R605663 : Reach 605663 := rs (se 1 (by rfl) ⟨454247, by rfl⟩) R908495
theorem R48667 : Reach 48667 := rs (se 1 (by rfl) ⟨36500, by rfl⟩) R73001
theorem R147905 : Reach 147905 := rs (se 2 (by rfl) ⟨55464, by rfl⟩) R110929
theorem R49889 : Reach 49889 := rs (se 2 (by rfl) ⟨18708, by rfl⟩) R37417
theorem R50159 : Reach 50159 := rs (se 1 (by rfl) ⟨37619, by rfl⟩) R75239
theorem R50591 : Reach 50591 := rs (se 1 (by rfl) ⟨37943, by rfl⟩) R75887
theorem R378593 : Reach 378593 := rs (se 2 (by rfl) ⟨141972, by rfl⟩) R283945
theorem R149687 : Reach 149687 := rs (se 1 (by rfl) ⟨112265, by rfl⟩) R224531
theorem R51475 : Reach 51475 := rs (se 1 (by rfl) ⟨38606, by rfl⟩) R77213
theorem R52895 : Reach 52895 := rs (se 1 (by rfl) ⟨39671, by rfl⟩) R79343
theorem R2707505 : Reach 2707505 := rs (se 2 (by rfl) ⟨1015314, by rfl⟩) R2030629
theorem R53369 : Reach 53369 := rs (se 2 (by rfl) ⟨20013, by rfl⟩) R40027
theorem R86159 : Reach 86159 := rs (se 1 (by rfl) ⟨64619, by rfl⟩) R129239
theorem R282943 : Reach 282943 := rs (se 1 (by rfl) ⟨212207, by rfl⟩) R424415
theorem R250685 : Reach 250685 := rs (se 3 (by rfl) ⟨47003, by rfl⟩) R94007
theorem R152765 : Reach 152765 := rs (se 3 (by rfl) ⟨28643, by rfl⟩) R57287
theorem R709955 : Reach 709955 := rs (se 1 (by rfl) ⟨532466, by rfl⟩) R1064933
theorem R218729 : Reach 218729 := rs (se 2 (by rfl) ⟨82023, by rfl⟩) R164047
theorem R120943 : Reach 120943 := rs (se 1 (by rfl) ⟨90707, by rfl⟩) R181415
theorem R88415 : Reach 88415 := rs (se 1 (by rfl) ⟨66311, by rfl⟩) R132623
theorem R252667 : Reach 252667 := rs (se 1 (by rfl) ⟨189500, by rfl⟩) R379001
theorem R56423 : Reach 56423 := rs (se 1 (by rfl) ⟨42317, by rfl⟩) R84635
theorem R58745 : Reach 58745 := rs (se 2 (by rfl) ⟨22029, by rfl⟩) R44059
theorem R91649 : Reach 91649 := rs (se 2 (by rfl) ⟨34368, by rfl⟩) R68737
theorem R91961 : Reach 91961 := rs (se 2 (by rfl) ⟨34485, by rfl⟩) R68971
theorem R125549 : Reach 125549 := rs (se 3 (by rfl) ⟨23540, by rfl⟩) R47081
theorem R60139 : Reach 60139 := rs (se 1 (by rfl) ⟨45104, by rfl⟩) R90209
theorem R1141613 : Reach 1141613 := rs (se 3 (by rfl) ⟨214052, by rfl⟩) R428105
theorem R715817 : Reach 715817 := rs (se 2 (by rfl) ⟨268431, by rfl⟩) R536863
theorem R93737 : Reach 93737 := rs (se 2 (by rfl) ⟨35151, by rfl⟩) R70303
theorem R28743 : Reach 28743 := rs (se 1 (by rfl) ⟨21557, by rfl⟩) R43115
theorem R6025427 : Reach 6025427 := rs (se 1 (by rfl) ⟨4519070, by rfl⟩) R9038141
theorem R553355 : Reach 553355 := rs (se 1 (by rfl) ⟨415016, by rfl⟩) R830033
theorem R29183 : Reach 29183 := rs (se 1 (by rfl) ⟨21887, by rfl⟩) R43775
theorem R29339 : Reach 29339 := rs (se 1 (by rfl) ⟨22004, by rfl⟩) R44009
theorem R29375 : Reach 29375 := rs (se 1 (by rfl) ⟨22031, by rfl⟩) R44063
theorem R62495 : Reach 62495 := rs (se 1 (by rfl) ⟨46871, by rfl⟩) R93743
theorem R422975 : Reach 422975 := rs (se 1 (by rfl) ⟨317231, by rfl⟩) R634463
theorem R29927 : Reach 29927 := rs (se 1 (by rfl) ⟨22445, by rfl⟩) R44891
theorem R29951 : Reach 29951 := rs (se 1 (by rfl) ⟨22463, by rfl⟩) R44927
theorem R29999 : Reach 29999 := rs (se 1 (by rfl) ⟨22499, by rfl⟩) R44999
theorem R30023 : Reach 30023 := rs (se 1 (by rfl) ⟨22517, by rfl⟩) R45035
theorem R63031 : Reach 63031 := rs (se 1 (by rfl) ⟨47273, by rfl⟩) R94547
theorem R30367 : Reach 30367 := rs (se 1 (by rfl) ⟨22775, by rfl⟩) R45551
theorem R63359 : Reach 63359 := rs (se 1 (by rfl) ⟨47519, by rfl⟩) R95039
theorem R30783 : Reach 30783 := rs (se 1 (by rfl) ⟨23087, by rfl⟩) R46175
theorem R63611 : Reach 63611 := rs (se 1 (by rfl) ⟨47708, by rfl⟩) R95417
theorem R30847 : Reach 30847 := rs (se 1 (by rfl) ⟨23135, by rfl⟩) R46271
theorem R1308869 : Reach 1308869 := rs (se 4 (by rfl) ⟨122706, by rfl⟩) R245413
theorem R161999 : Reach 161999 := rs (se 1 (by rfl) ⟨121499, by rfl⟩) R242999
theorem R162431 : Reach 162431 := rs (se 1 (by rfl) ⟨121823, by rfl⟩) R243647
theorem R31387 : Reach 31387 := rs (se 1 (by rfl) ⟨23540, by rfl⟩) R47081
theorem R65015 : Reach 65015 := rs (se 1 (by rfl) ⟨48761, by rfl⟩) R97523
theorem R32287 : Reach 32287 := rs (se 1 (by rfl) ⟨24215, by rfl⟩) R48431
theorem R32359 : Reach 32359 := rs (se 1 (by rfl) ⟨24269, by rfl⟩) R48539
theorem R65591 : Reach 65591 := rs (se 1 (by rfl) ⟨49193, by rfl⟩) R98387
theorem R2752703 : Reach 2752703 := rs (se 1 (by rfl) ⟨2064527, by rfl⟩) R4129055
theorem R98603 : Reach 98603 := rs (se 1 (by rfl) ⟨73952, by rfl⟩) R147905
theorem R33259 : Reach 33259 := rs (se 1 (by rfl) ⟨24944, by rfl⟩) R49889
theorem R33439 : Reach 33439 := rs (se 1 (by rfl) ⟨25079, by rfl⟩) R50159
theorem R33727 : Reach 33727 := rs (se 1 (by rfl) ⟨25295, by rfl⟩) R50591
theorem R99791 : Reach 99791 := rs (se 1 (by rfl) ⟨74843, by rfl⟩) R149687
theorem R35263 : Reach 35263 := rs (se 1 (by rfl) ⟨26447, by rfl⟩) R52895
theorem R1805003 : Reach 1805003 := rs (se 1 (by rfl) ⟨1353752, by rfl⟩) R2707505
theorem R35579 : Reach 35579 := rs (se 1 (by rfl) ⟨26684, by rfl⟩) R53369
theorem R68633 : Reach 68633 := rs (se 2 (by rfl) ⟨25737, by rfl⟩) R51475
theorem R167123 : Reach 167123 := rs (se 1 (by rfl) ⟨125342, by rfl⟩) R250685
theorem R101843 : Reach 101843 := rs (se 1 (by rfl) ⟨76382, by rfl⟩) R152765
theorem R69371 : Reach 69371 := rs (se 1 (by rfl) ⟨52028, by rfl⟩) R104057
theorem R37615 : Reach 37615 := rs (se 1 (by rfl) ⟨28211, by rfl⟩) R56423
theorem R136073 : Reach 136073 := rs (se 2 (by rfl) ⟨51027, by rfl⟩) R102055
theorem R267259 : Reach 267259 := rs (se 1 (by rfl) ⟨200444, by rfl⟩) R400889
theorem R761075 : Reach 761075 := rs (se 1 (by rfl) ⟨570806, by rfl⟩) R1141613
theorem R138935 : Reach 138935 := rs (se 1 (by rfl) ⟨104201, by rfl⟩) R208403
theorem R4530167 : Reach 4530167 := rs (se 1 (by rfl) ⟨3397625, by rfl⟩) R6795251
theorem R73831 : Reach 73831 := rs (se 1 (by rfl) ⟨55373, by rfl⟩) R110747
theorem R41129 : Reach 41129 := rs (se 2 (by rfl) ⟨15423, by rfl⟩) R30847
theorem R73979 : Reach 73979 := rs (se 1 (by rfl) ⟨55484, by rfl⟩) R110969
theorem R368903 : Reach 368903 := rs (se 1 (by rfl) ⟨276677, by rfl⟩) R553355
theorem R41663 : Reach 41663 := rs (se 1 (by rfl) ⟨31247, by rfl⟩) R62495
theorem R74495 : Reach 74495 := rs (se 1 (by rfl) ⟨55871, by rfl⟩) R111743
theorem R41849 : Reach 41849 := rs (se 2 (by rfl) ⟨15693, by rfl⟩) R31387
theorem R74735 : Reach 74735 := rs (se 1 (by rfl) ⟨56051, by rfl⟩) R112103
theorem R336889 : Reach 336889 := rs (se 2 (by rfl) ⟨126333, by rfl⟩) R252667
theorem R42239 : Reach 42239 := rs (se 1 (by rfl) ⟨31679, by rfl⟩) R63359
theorem R42407 : Reach 42407 := rs (se 1 (by rfl) ⟨31805, by rfl⟩) R63611
theorem R107999 : Reach 107999 := rs (se 1 (by rfl) ⟨80999, by rfl⟩) R161999
theorem R108287 : Reach 108287 := rs (se 1 (by rfl) ⟨81215, by rfl⟩) R162431
theorem R141223 : Reach 141223 := rs (se 1 (by rfl) ⟨105917, by rfl⟩) R211835
theorem R43049 : Reach 43049 := rs (se 2 (by rfl) ⟨16143, by rfl⟩) R32287
theorem R43145 : Reach 43145 := rs (se 2 (by rfl) ⟨16179, by rfl⟩) R32359
theorem R403775 : Reach 403775 := rs (se 1 (by rfl) ⟨302831, by rfl⟩) R605663
theorem R43343 : Reach 43343 := rs (se 1 (by rfl) ⟨32507, by rfl⟩) R65015
theorem R797161 : Reach 797161 := rs (se 2 (by rfl) ⟨298935, by rfl⟩) R597871
theorem R43943 : Reach 43943 := rs (se 1 (by rfl) ⟨32957, by rfl⟩) R65915
theorem R44879 : Reach 44879 := rs (se 1 (by rfl) ⟨33659, by rfl⟩) R67319
theorem R45047 : Reach 45047 := rs (se 1 (by rfl) ⟨33785, by rfl⟩) R67571
theorem R45167 : Reach 45167 := rs (se 1 (by rfl) ⟨33875, by rfl⟩) R67751
theorem R45947 : Reach 45947 := rs (se 1 (by rfl) ⟨34460, by rfl⟩) R68921
theorem R46217 : Reach 46217 := rs (se 2 (by rfl) ⟨17331, by rfl⟩) R34663
theorem R46391 : Reach 46391 := rs (se 1 (by rfl) ⟨34793, by rfl⟩) R69587
theorem R46583 : Reach 46583 := rs (se 1 (by rfl) ⟨34937, by rfl⟩) R69875
theorem R473303 : Reach 473303 := rs (se 1 (by rfl) ⟨354977, by rfl⟩) R709955
theorem R80185 : Reach 80185 := rs (se 2 (by rfl) ⟨30069, by rfl⟩) R60139
theorem R145819 : Reach 145819 := rs (se 1 (by rfl) ⟨109364, by rfl⟩) R218729
theorem R244397 : Reach 244397 := rs (se 3 (by rfl) ⟨45824, by rfl⟩) R91649
theorem R48695 : Reach 48695 := rs (se 1 (by rfl) ⟨36521, by rfl⟩) R73043
theorem R49207 : Reach 49207 := rs (se 1 (by rfl) ⟨36905, by rfl⟩) R73811
theorem R377257 : Reach 377257 := rs (se 2 (by rfl) ⟨141471, by rfl⟩) R282943
theorem R116015 : Reach 116015 := rs (se 1 (by rfl) ⟨87011, by rfl⟩) R174023
theorem R83699 : Reach 83699 := rs (se 1 (by rfl) ⟨62774, by rfl⟩) R125549
theorem R477211 : Reach 477211 := rs (se 1 (by rfl) ⟨357908, by rfl⟩) R715817
theorem R84041 : Reach 84041 := rs (se 2 (by rfl) ⟨31515, by rfl⟩) R63031
theorem R4016951 : Reach 4016951 := rs (se 1 (by rfl) ⟨3012713, by rfl⟩) R6025427
theorem R248771 : Reach 248771 := rs (se 1 (by rfl) ⟨186578, by rfl⟩) R373157
theorem R281983 : Reach 281983 := rs (se 1 (by rfl) ⟨211487, by rfl⟩) R422975
theorem R1429159 : Reach 1429159 := rs (se 1 (by rfl) ⟨1071869, by rfl⟩) R2143739
theorem R872579 : Reach 872579 := rs (se 1 (by rfl) ⟨654434, by rfl⟩) R1308869
theorem R87571 : Reach 87571 := rs (se 1 (by rfl) ⟨65678, by rfl⟩) R131357
theorem R349919 : Reach 349919 := rs (se 1 (by rfl) ⟨262439, by rfl⟩) R524879
theorem R645029 : Reach 645029 := rs (se 4 (by rfl) ⟨60471, by rfl⟩) R120943
theorem R252395 : Reach 252395 := rs (se 1 (by rfl) ⟨189296, by rfl⟩) R378593
theorem R89599 : Reach 89599 := rs (se 1 (by rfl) ⟨67199, by rfl⟩) R134399
theorem R57439 : Reach 57439 := rs (se 1 (by rfl) ⟨43079, by rfl⟩) R86159
theorem R90335 : Reach 90335 := rs (se 1 (by rfl) ⟨67751, by rfl⟩) R135503
theorem R156653 : Reach 156653 := rs (se 3 (by rfl) ⟨29372, by rfl⟩) R58745
theorem R58943 : Reach 58943 := rs (se 1 (by rfl) ⟨44207, by rfl⟩) R88415
theorem R92015 : Reach 92015 := rs (se 1 (by rfl) ⟨69011, by rfl⟩) R138023
theorem R27583 : Reach 27583 := rs (se 1 (by rfl) ⟨20687, by rfl⟩) R41375
theorem R27803 : Reach 27803 := rs (se 1 (by rfl) ⟨20852, by rfl⟩) R41705
theorem R28207 : Reach 28207 := rs (se 1 (by rfl) ⟨21155, by rfl⟩) R42311
theorem R28391 : Reach 28391 := rs (se 1 (by rfl) ⟨21293, by rfl⟩) R42587
theorem R61307 : Reach 61307 := rs (se 1 (by rfl) ⟨45980, by rfl⟩) R91961
theorem R716789 : Reach 716789 := rs (se 5 (by rfl) ⟨33599, by rfl⟩) R67199
theorem R28719 : Reach 28719 := rs (se 1 (by rfl) ⟨21539, by rfl⟩) R43079
theorem R29275 : Reach 29275 := rs (se 1 (by rfl) ⟨21956, by rfl⟩) R43913
theorem R94907 : Reach 94907 := rs (se 1 (by rfl) ⟨71180, by rfl⟩) R142361
theorem R29471 : Reach 29471 := rs (se 1 (by rfl) ⟨22103, by rfl⟩) R44207
theorem R357371 : Reach 357371 := rs (se 1 (by rfl) ⟨268028, by rfl⟩) R536057
theorem R62491 : Reach 62491 := rs (se 1 (by rfl) ⟨46868, by rfl⟩) R93737
theorem R29787 : Reach 29787 := rs (se 1 (by rfl) ⟨22340, by rfl⟩) R44681
theorem R30159 : Reach 30159 := rs (se 1 (by rfl) ⟨22619, by rfl⟩) R45239
theorem R96443 : Reach 96443 := rs (se 1 (by rfl) ⟨72332, by rfl⟩) R144665
theorem R555835 : Reach 555835 := rs (se 1 (by rfl) ⟨416876, by rfl⟩) R833753
theorem R97519 : Reach 97519 := rs (se 1 (by rfl) ⟨73139, by rfl⟩) R146279
theorem R64889 : Reach 64889 := rs (se 2 (by rfl) ⟨24333, by rfl⟩) R48667
theorem R65609 : Reach 65609 := rs (se 2 (by rfl) ⟨24603, by rfl⟩) R49207
theorem R1835135 : Reach 1835135 := rs (se 1 (by rfl) ⟨1376351, by rfl⟩) R2752703
theorem R98441 : Reach 98441 := rs (se 2 (by rfl) ⟨36915, by rfl⟩) R73831
theorem R65735 : Reach 65735 := rs (se 1 (by rfl) ⟨49301, by rfl⟩) R98603
theorem R2326877 : Reach 2326877 := rs (se 3 (by rfl) ⟨436289, by rfl⟩) R872579
theorem R66527 : Reach 66527 := rs (se 1 (by rfl) ⟨49895, by rfl⟩) R99791
theorem R165847 : Reach 165847 := rs (se 1 (by rfl) ⟨124385, by rfl⟩) R248771
theorem R67895 : Reach 67895 := rs (se 1 (by rfl) ⟨50921, by rfl⟩) R101843
theorem R233279 : Reach 233279 := rs (se 1 (by rfl) ⟨174959, by rfl⟩) R349919
theorem R430019 : Reach 430019 := rs (se 1 (by rfl) ⟨322514, by rfl⟩) R645029
theorem R168263 : Reach 168263 := rs (se 1 (by rfl) ⟨126197, by rfl⟩) R252395
theorem R1905545 : Reach 1905545 := rs (se 2 (by rfl) ⟨714579, by rfl⟩) R1429159
theorem R3020111 : Reach 3020111 := rs (se 1 (by rfl) ⟨2265083, by rfl⟩) R4530167
theorem R104435 : Reach 104435 := rs (se 1 (by rfl) ⟨78326, by rfl⟩) R156653
theorem R71999 : Reach 71999 := rs (se 1 (by rfl) ⟨53999, by rfl⟩) R107999
theorem R39295 : Reach 39295 := rs (se 1 (by rfl) ⟨29471, by rfl⟩) R58943
theorem R72191 : Reach 72191 := rs (se 1 (by rfl) ⟨54143, by rfl⟩) R108287
theorem R269183 : Reach 269183 := rs (se 1 (by rfl) ⟨201887, by rfl⟩) R403775
theorem R40871 : Reach 40871 := rs (se 1 (by rfl) ⟨30653, by rfl⟩) R61307
theorem R106913 : Reach 106913 := rs (se 2 (by rfl) ⟨40092, by rfl⟩) R80185
theorem R238247 : Reach 238247 := rs (se 1 (by rfl) ⟨178685, by rfl⟩) R357371
theorem R370493 : Reach 370493 := rs (se 3 (by rfl) ⟨69467, by rfl⟩) R138935
theorem R43259 : Reach 43259 := rs (se 1 (by rfl) ⟨32444, by rfl⟩) R64889
theorem R1911437 : Reach 1911437 := rs (se 3 (by rfl) ⟨358394, by rfl⟩) R716789
theorem R43727 : Reach 43727 := rs (se 1 (by rfl) ⟨32795, by rfl⟩) R65591
theorem R76585 : Reach 76585 := rs (se 2 (by rfl) ⟨28719, by rfl⟩) R57439
theorem R503009 : Reach 503009 := rs (se 2 (by rfl) ⟨188628, by rfl⟩) R377257
theorem R44345 : Reach 44345 := rs (se 2 (by rfl) ⟨16629, by rfl⟩) R33259
theorem R44585 : Reach 44585 := rs (se 2 (by rfl) ⟨16719, by rfl⟩) R33439
theorem R44969 : Reach 44969 := rs (se 2 (by rfl) ⟨16863, by rfl⟩) R33727
theorem R45755 : Reach 45755 := rs (se 1 (by rfl) ⟨34316, by rfl⟩) R68633
theorem R111415 : Reach 111415 := rs (se 1 (by rfl) ⟨83561, by rfl⟩) R167123
theorem R46247 : Reach 46247 := rs (se 1 (by rfl) ⟨34685, by rfl⟩) R69371
theorem R636281 : Reach 636281 := rs (se 2 (by rfl) ⟨238605, by rfl⟩) R477211
theorem R47017 : Reach 47017 := rs (se 2 (by rfl) ⟨17631, by rfl⟩) R35263
theorem R1062881 : Reach 1062881 := rs (se 2 (by rfl) ⟨398580, by rfl⟩) R797161
theorem R375977 : Reach 375977 := rs (se 2 (by rfl) ⟨140991, by rfl⟩) R281983
theorem R507383 : Reach 507383 := rs (se 1 (by rfl) ⟨380537, by rfl⟩) R761075
theorem R49319 : Reach 49319 := rs (se 1 (by rfl) ⟨36989, by rfl⟩) R73979
theorem R245935 : Reach 245935 := rs (se 1 (by rfl) ⟨184451, by rfl⟩) R368903
theorem R49663 : Reach 49663 := rs (se 1 (by rfl) ⟨37247, by rfl⟩) R74495
theorem R1262141 : Reach 1262141 := rs (se 3 (by rfl) ⟨236651, by rfl⟩) R473303
theorem R49823 : Reach 49823 := rs (se 1 (by rfl) ⟨37367, by rfl⟩) R74735
theorem R50153 : Reach 50153 := rs (se 2 (by rfl) ⟨18807, by rfl⟩) R37615
theorem R83321 : Reach 83321 := rs (se 2 (by rfl) ⟨31245, by rfl⟩) R62491
theorem R116761 : Reach 116761 := rs (se 2 (by rfl) ⟨43785, by rfl⟩) R87571
theorem R741113 : Reach 741113 := rs (se 2 (by rfl) ⟨277917, by rfl⟩) R555835
theorem R119465 : Reach 119465 := rs (se 2 (by rfl) ⟨44799, by rfl⟩) R89599
theorem R55799 : Reach 55799 := rs (se 1 (by rfl) ⟨41849, by rfl⟩) R83699
theorem R449185 : Reach 449185 := rs (se 2 (by rfl) ⟨168444, by rfl⟩) R336889
theorem R56027 : Reach 56027 := rs (se 1 (by rfl) ⟨42020, by rfl⟩) R84041
theorem R1203335 : Reach 1203335 := rs (se 1 (by rfl) ⟨902501, by rfl⟩) R1805003
theorem R253085 : Reach 253085 := rs (se 3 (by rfl) ⟨47453, by rfl⟩) R94907
theorem R2677967 : Reach 2677967 := rs (se 1 (by rfl) ⟨2008475, by rfl⟩) R4016951
theorem R777701 : Reach 777701 := rs (se 4 (by rfl) ⟨72909, by rfl⟩) R145819
theorem R188297 : Reach 188297 := rs (se 2 (by rfl) ⟨70611, by rfl⟩) R141223
theorem R1237493 : Reach 1237493 := rs (se 5 (by rfl) ⟨58007, by rfl⟩) R116015
theorem R90715 : Reach 90715 := rs (se 1 (by rfl) ⟨68036, by rfl⟩) R136073
theorem R27419 : Reach 27419 := rs (se 1 (by rfl) ⟨20564, by rfl⟩) R41129
theorem R60223 : Reach 60223 := rs (se 1 (by rfl) ⟨45167, by rfl⟩) R90335
theorem R27775 : Reach 27775 := rs (se 1 (by rfl) ⟨20831, by rfl⟩) R41663
theorem R27899 : Reach 27899 := rs (se 1 (by rfl) ⟨20924, by rfl⟩) R41849
theorem R28159 : Reach 28159 := rs (se 1 (by rfl) ⟨21119, by rfl⟩) R42239
theorem R28271 : Reach 28271 := rs (se 1 (by rfl) ⟨21203, by rfl⟩) R42407
theorem R61343 : Reach 61343 := rs (se 1 (by rfl) ⟨46007, by rfl⟩) R92015
theorem R356345 : Reach 356345 := rs (se 2 (by rfl) ⟨133629, by rfl⟩) R267259
theorem R28699 : Reach 28699 := rs (se 1 (by rfl) ⟨21524, by rfl⟩) R43049
theorem R28763 : Reach 28763 := rs (se 1 (by rfl) ⟨21572, by rfl⟩) R43145
theorem R28895 : Reach 28895 := rs (se 1 (by rfl) ⟨21671, by rfl⟩) R43343
theorem R29295 : Reach 29295 := rs (se 1 (by rfl) ⟨21971, by rfl⟩) R43943
theorem R94877 : Reach 94877 := rs (se 3 (by rfl) ⟨17789, by rfl⟩) R35579
theorem R29919 : Reach 29919 := rs (se 1 (by rfl) ⟨22439, by rfl⟩) R44879
theorem R30031 : Reach 30031 := rs (se 1 (by rfl) ⟨22523, by rfl⟩) R45047
theorem R30111 : Reach 30111 := rs (se 1 (by rfl) ⟨22583, by rfl⟩) R45167
theorem R30631 : Reach 30631 := rs (se 1 (by rfl) ⟨22973, by rfl⟩) R45947
theorem R30811 : Reach 30811 := rs (se 1 (by rfl) ⟨23108, by rfl⟩) R46217
theorem R30927 : Reach 30927 := rs (se 1 (by rfl) ⟨23195, by rfl⟩) R46391
theorem R31055 : Reach 31055 := rs (se 1 (by rfl) ⟨23291, by rfl⟩) R46583
theorem R64295 : Reach 64295 := rs (se 1 (by rfl) ⟨48221, by rfl⟩) R96443
theorem R129853 : Reach 129853 := rs (se 3 (by rfl) ⟨24347, by rfl⟩) R48695
theorem R130025 : Reach 130025 := rs (se 2 (by rfl) ⟨48759, by rfl⟩) R97519
theorem R162931 : Reach 162931 := rs (se 1 (by rfl) ⟨122198, by rfl⟩) R244397
theorem R65627 : Reach 65627 := rs (se 1 (by rfl) ⟨49220, by rfl⟩) R98441
theorem R32879 : Reach 32879 := rs (se 1 (by rfl) ⟨24659, by rfl⟩) R49319
theorem R33215 : Reach 33215 := rs (se 1 (by rfl) ⟨24911, by rfl⟩) R49823
theorem R1311653 : Reach 1311653 := rs (se 4 (by rfl) ⟨122967, by rfl⟩) R245935
theorem R494075 : Reach 494075 := rs (se 1 (by rfl) ⟨370556, by rfl⟩) R741113
theorem R133741 : Reach 133741 := rs (se 3 (by rfl) ⟨25076, by rfl⟩) R50153
theorem R264869 : Reach 264869 := rs (se 4 (by rfl) ⟨24831, by rfl⟩) R49663
theorem R102113 : Reach 102113 := rs (se 2 (by rfl) ⟨38292, by rfl⟩) R76585
theorem R69623 : Reach 69623 := rs (se 1 (by rfl) ⟨52217, by rfl⟩) R104435
theorem R37199 : Reach 37199 := rs (se 1 (by rfl) ⟨27899, by rfl⟩) R55799
theorem R37351 : Reach 37351 := rs (se 1 (by rfl) ⟨28013, by rfl⟩) R56027
theorem R71275 : Reach 71275 := rs (se 1 (by rfl) ⟨53456, by rfl⟩) R106913
theorem R824995 : Reach 824995 := rs (se 1 (by rfl) ⟨618746, by rfl⟩) R1237493
theorem R335339 : Reach 335339 := rs (se 1 (by rfl) ⟨251504, by rfl⟩) R503009
theorem R40841 : Reach 40841 := rs (se 2 (by rfl) ⟨15315, by rfl⟩) R30631
theorem R40895 : Reach 40895 := rs (se 1 (by rfl) ⟨30671, by rfl⟩) R61343
theorem R237563 : Reach 237563 := rs (se 1 (by rfl) ⟨178172, by rfl⟩) R356345
theorem R41081 : Reach 41081 := rs (se 2 (by rfl) ⟨15405, by rfl⟩) R30811
theorem R598913 : Reach 598913 := rs (se 2 (by rfl) ⟨224592, by rfl⟩) R449185
theorem R173137 : Reach 173137 := rs (se 2 (by rfl) ⟨64926, by rfl⟩) R129853
theorem R2073869 : Reach 2073869 := rs (se 3 (by rfl) ⟨388850, by rfl⟩) R777701
theorem R42863 : Reach 42863 := rs (se 1 (by rfl) ⟨32147, by rfl⟩) R64295
theorem R338255 : Reach 338255 := rs (se 1 (by rfl) ⟨253691, by rfl⟩) R507383
theorem R108989 : Reach 108989 := rs (se 3 (by rfl) ⟨20435, by rfl⟩) R40871
theorem R43739 : Reach 43739 := rs (se 1 (by rfl) ⟨32804, by rfl⟩) R65609
theorem R1223423 : Reach 1223423 := rs (se 1 (by rfl) ⟨917567, by rfl⟩) R1835135
theorem R43823 : Reach 43823 := rs (se 1 (by rfl) ⟨32867, by rfl⟩) R65735
theorem R1551251 : Reach 1551251 := rs (se 1 (by rfl) ⟨1163438, by rfl⟩) R2326877
theorem R44351 : Reach 44351 := rs (se 1 (by rfl) ⟨33263, by rfl⟩) R66527
theorem R45263 : Reach 45263 := rs (se 1 (by rfl) ⟨33947, by rfl⟩) R67895
theorem R112175 : Reach 112175 := rs (se 1 (by rfl) ⟨84131, by rfl⟩) R168263
theorem R79643 : Reach 79643 := rs (se 1 (by rfl) ⟨59732, by rfl⟩) R119465
theorem R2013407 : Reach 2013407 := rs (se 1 (by rfl) ⟨1510055, by rfl⟩) R3020111
theorem R80297 : Reach 80297 := rs (se 2 (by rfl) ⟨30111, by rfl⟩) R60223
theorem R47999 : Reach 47999 := rs (se 1 (by rfl) ⟨35999, by rfl⟩) R71999
theorem R48127 : Reach 48127 := rs (se 1 (by rfl) ⟨36095, by rfl⟩) R72191
theorem R179455 : Reach 179455 := rs (se 1 (by rfl) ⟨134591, by rfl⟩) R269183
theorem R802223 : Reach 802223 := rs (se 1 (by rfl) ⟨601667, by rfl⟩) R1203335
theorem R1785311 : Reach 1785311 := rs (se 1 (by rfl) ⟨1338983, by rfl⟩) R2677967
theorem R148553 : Reach 148553 := rs (se 2 (by rfl) ⟨55707, by rfl⟩) R111415
theorem R246995 : Reach 246995 := rs (se 1 (by rfl) ⟨185246, by rfl⟩) R370493
theorem R674893 : Reach 674893 := rs (se 3 (by rfl) ⟨126542, by rfl⟩) R253085
theorem R52393 : Reach 52393 := rs (se 2 (by rfl) ⟨19647, by rfl⟩) R39295
theorem R708587 : Reach 708587 := rs (se 1 (by rfl) ⟨531440, by rfl⟩) R1062881
theorem R217241 : Reach 217241 := rs (se 2 (by rfl) ⟨81465, by rfl⟩) R162931
theorem R86683 : Reach 86683 := rs (se 1 (by rfl) ⟨65012, by rfl⟩) R130025
theorem R250651 : Reach 250651 := rs (se 1 (by rfl) ⟨187988, by rfl⟩) R375977
theorem R841427 : Reach 841427 := rs (se 1 (by rfl) ⟨631070, by rfl⟩) R1262141
theorem R120953 : Reach 120953 := rs (se 2 (by rfl) ⟨45357, by rfl⟩) R90715
theorem R55547 : Reach 55547 := rs (se 1 (by rfl) ⟨41660, by rfl⟩) R83321
theorem R155519 : Reach 155519 := rs (se 1 (by rfl) ⟨116639, by rfl⟩) R233279
theorem R221129 : Reach 221129 := rs (se 2 (by rfl) ⟨82923, by rfl⟩) R165847
theorem R286679 : Reach 286679 := rs (se 1 (by rfl) ⟨215009, by rfl⟩) R430019
theorem R155681 : Reach 155681 := rs (se 2 (by rfl) ⟨58380, by rfl⟩) R116761
theorem R1270363 : Reach 1270363 := rs (se 1 (by rfl) ⟨952772, by rfl⟩) R1905545
theorem R518467 : Reach 518467 := rs (se 1 (by rfl) ⟨388850, by rfl⟩) R777701
theorem R125531 : Reach 125531 := rs (se 1 (by rfl) ⟨94148, by rfl⟩) R188297
theorem R27247 : Reach 27247 := rs (se 1 (by rfl) ⟨20435, by rfl⟩) R40871
theorem R158831 : Reach 158831 := rs (se 1 (by rfl) ⟨119123, by rfl⟩) R238247
theorem R28839 : Reach 28839 := rs (se 1 (by rfl) ⟨21629, by rfl⟩) R43259
theorem R1274291 : Reach 1274291 := rs (se 1 (by rfl) ⟨955718, by rfl⟩) R1911437
theorem R29151 : Reach 29151 := rs (se 1 (by rfl) ⟨21863, by rfl⟩) R43727
theorem R29563 : Reach 29563 := rs (se 1 (by rfl) ⟨22172, by rfl⟩) R44345
theorem R29723 : Reach 29723 := rs (se 1 (by rfl) ⟨22292, by rfl⟩) R44585
theorem R62689 : Reach 62689 := rs (se 2 (by rfl) ⟨23508, by rfl⟩) R47017
theorem R29979 : Reach 29979 := rs (se 1 (by rfl) ⟨22484, by rfl⟩) R44969
theorem R63251 : Reach 63251 := rs (se 1 (by rfl) ⟨47438, by rfl⟩) R94877
theorem R30503 : Reach 30503 := rs (se 1 (by rfl) ⟨22877, by rfl⟩) R45755
theorem R30831 : Reach 30831 := rs (se 1 (by rfl) ⟨23123, by rfl⟩) R46247
theorem R424187 : Reach 424187 := rs (se 1 (by rfl) ⟨318140, by rfl⟩) R636281
theorem R99035 : Reach 99035 := rs (se 1 (by rfl) ⟨74276, by rfl⟩) R148553
theorem R164663 : Reach 164663 := rs (se 1 (by rfl) ⟨123497, by rfl⟩) R246995
theorem R99197 : Reach 99197 := rs (se 3 (by rfl) ⟨18599, by rfl⟩) R37199
theorem R230849 : Reach 230849 := rs (se 2 (by rfl) ⟨86568, by rfl⟩) R173137
theorem R329383 : Reach 329383 := rs (se 1 (by rfl) ⟨247037, by rfl⟩) R494075
theorem R68075 : Reach 68075 := rs (se 1 (by rfl) ⟨51056, by rfl⟩) R102113
theorem R691289 : Reach 691289 := rs (se 2 (by rfl) ⟨259233, by rfl⟩) R518467
theorem R560951 : Reach 560951 := rs (se 1 (by rfl) ⟨420713, by rfl⟩) R841427
theorem R37031 : Reach 37031 := rs (se 1 (by rfl) ⟨27773, by rfl⟩) R55547
theorem R69857 : Reach 69857 := rs (se 2 (by rfl) ⟨26196, by rfl⟩) R52393
theorem R103679 : Reach 103679 := rs (se 1 (by rfl) ⟨77759, by rfl⟩) R155519
theorem R103787 : Reach 103787 := rs (se 1 (by rfl) ⟨77840, by rfl⟩) R155681
theorem R399275 : Reach 399275 := rs (se 1 (by rfl) ⟨299456, by rfl⟩) R598913
theorem R1382579 : Reach 1382579 := rs (se 1 (by rfl) ⟨1036934, by rfl⟩) R2073869
theorem R334201 : Reach 334201 := rs (se 2 (by rfl) ⟨125325, by rfl⟩) R250651
theorem R72659 : Reach 72659 := rs (se 1 (by rfl) ⟨54494, by rfl⟩) R108989
theorem R105887 : Reach 105887 := rs (se 1 (by rfl) ⟨79415, by rfl⟩) R158831
theorem R74783 : Reach 74783 := rs (se 1 (by rfl) ⟨56087, by rfl⟩) R112175
theorem R42167 : Reach 42167 := rs (se 1 (by rfl) ⟨31625, by rfl⟩) R63251
theorem R239273 : Reach 239273 := rs (se 2 (by rfl) ⟨89727, by rfl⟩) R179455
theorem R534815 : Reach 534815 := rs (se 1 (by rfl) ⟨401111, by rfl⟩) R802223
theorem R1190207 : Reach 1190207 := rs (se 1 (by rfl) ⟨892655, by rfl⟩) R1785311
theorem R43751 : Reach 43751 := rs (se 1 (by rfl) ⟨32813, by rfl⟩) R65627
theorem R176579 : Reach 176579 := rs (se 1 (by rfl) ⟨132434, by rfl⟩) R264869
theorem R472391 : Reach 472391 := rs (se 1 (by rfl) ⟨354293, by rfl⟩) R708587
theorem R46415 : Reach 46415 := rs (se 1 (by rfl) ⟨34811, by rfl⟩) R69623
theorem R144827 : Reach 144827 := rs (se 1 (by rfl) ⟨108620, by rfl⟩) R217241
theorem R178321 : Reach 178321 := rs (se 2 (by rfl) ⟨66870, by rfl⟩) R133741
theorem R80635 : Reach 80635 := rs (se 1 (by rfl) ⟨60476, by rfl⟩) R120953
theorem R899857 : Reach 899857 := rs (se 2 (by rfl) ⟨337446, by rfl⟩) R674893
theorem R212381 : Reach 212381 := rs (se 3 (by rfl) ⟨39821, by rfl⟩) R79643
theorem R147419 : Reach 147419 := rs (se 1 (by rfl) ⟨110564, by rfl⟩) R221129
theorem R49801 : Reach 49801 := rs (se 2 (by rfl) ⟨18675, by rfl⟩) R37351
theorem R115577 : Reach 115577 := rs (se 2 (by rfl) ⟨43341, by rfl⟩) R86683
theorem R83585 : Reach 83585 := rs (se 2 (by rfl) ⟨31344, by rfl⟩) R62689
theorem R83687 : Reach 83687 := rs (se 1 (by rfl) ⟨62765, by rfl⟩) R125531
theorem R1034167 : Reach 1034167 := rs (se 1 (by rfl) ⟨775625, by rfl⟩) R1551251
theorem R1099993 : Reach 1099993 := rs (se 2 (by rfl) ⟨412497, by rfl⟩) R824995
theorem R282791 : Reach 282791 := rs (se 1 (by rfl) ⟨212093, by rfl⟩) R424187
theorem R53531 : Reach 53531 := rs (se 1 (by rfl) ⟨40148, by rfl⟩) R80297
theorem R87677 : Reach 87677 := rs (se 3 (by rfl) ⟨16439, by rfl⟩) R32879
theorem R874435 : Reach 874435 := rs (se 1 (by rfl) ⟨655826, by rfl⟩) R1311653
theorem R1693817 : Reach 1693817 := rs (se 2 (by rfl) ⟨635181, by rfl⟩) R1270363
theorem R354293 : Reach 354293 := rs (se 5 (by rfl) ⟨16607, by rfl⟩) R33215
theorem R223559 : Reach 223559 := rs (se 1 (by rfl) ⟨167669, by rfl⟩) R335339
theorem R27227 : Reach 27227 := rs (se 1 (by rfl) ⟨20420, by rfl⟩) R40841
theorem R27263 : Reach 27263 := rs (se 1 (by rfl) ⟨20447, by rfl⟩) R40895
theorem R191119 : Reach 191119 := rs (se 1 (by rfl) ⟨143339, by rfl⟩) R286679
theorem R158375 : Reach 158375 := rs (se 1 (by rfl) ⟨118781, by rfl⟩) R237563
theorem R27387 : Reach 27387 := rs (se 1 (by rfl) ⟨20540, by rfl⟩) R41081
theorem R28575 : Reach 28575 := rs (se 1 (by rfl) ⟨21431, by rfl⟩) R42863
theorem R225503 : Reach 225503 := rs (se 1 (by rfl) ⟨169127, by rfl⟩) R338255
theorem R29159 : Reach 29159 := rs (se 1 (by rfl) ⟨21869, by rfl⟩) R43739
theorem R815615 : Reach 815615 := rs (se 1 (by rfl) ⟨611711, by rfl⟩) R1223423
theorem R29215 : Reach 29215 := rs (se 1 (by rfl) ⟨21911, by rfl⟩) R43823
theorem R95033 : Reach 95033 := rs (se 2 (by rfl) ⟨35637, by rfl⟩) R71275
theorem R29567 : Reach 29567 := rs (se 1 (by rfl) ⟨22175, by rfl⟩) R44351
theorem R30175 : Reach 30175 := rs (se 1 (by rfl) ⟨22631, by rfl⟩) R45263
theorem R849527 : Reach 849527 := rs (se 1 (by rfl) ⟨637145, by rfl⟩) R1274291
theorem R64169 : Reach 64169 := rs (se 2 (by rfl) ⟨24063, by rfl⟩) R48127
theorem R1342271 : Reach 1342271 := rs (se 1 (by rfl) ⟨1006703, by rfl⟩) R2013407
theorem R31999 : Reach 31999 := rs (se 1 (by rfl) ⟨23999, by rfl⟩) R47999
theorem R98749 : Reach 98749 := rs (se 3 (by rfl) ⟨18515, by rfl⟩) R37031
theorem R66023 : Reach 66023 := rs (se 1 (by rfl) ⟨49517, by rfl⟩) R99035
theorem R66131 : Reach 66131 := rs (se 1 (by rfl) ⟨49598, by rfl⟩) R99197
theorem R66401 : Reach 66401 := rs (se 2 (by rfl) ⟨24900, by rfl⟩) R49801
theorem R460859 : Reach 460859 := rs (se 1 (by rfl) ⟨345644, by rfl⟩) R691289
theorem R1378889 : Reach 1378889 := rs (se 2 (by rfl) ⟨517083, by rfl⟩) R1034167
theorem R35687 : Reach 35687 := rs (se 1 (by rfl) ⟨26765, by rfl⟩) R53531
theorem R69119 : Reach 69119 := rs (se 1 (by rfl) ⟨51839, by rfl⟩) R103679
theorem R69191 : Reach 69191 := rs (se 1 (by rfl) ⟨51893, by rfl⟩) R103787
theorem R266183 : Reach 266183 := rs (se 1 (by rfl) ⟨199637, by rfl⟩) R399275
theorem R921719 : Reach 921719 := rs (se 1 (by rfl) ⟨691289, by rfl⟩) R1382579
theorem R70591 : Reach 70591 := rs (se 1 (by rfl) ⟨52943, by rfl⟩) R105887
theorem R236195 : Reach 236195 := rs (se 1 (by rfl) ⟨177146, by rfl⟩) R354293
theorem R793471 : Reach 793471 := rs (se 1 (by rfl) ⟨595103, by rfl⟩) R1190207
theorem R105583 : Reach 105583 := rs (se 1 (by rfl) ⟨79187, by rfl⟩) R158375
theorem R3579389 : Reach 3579389 := rs (se 3 (by rfl) ⟨671135, by rfl⟩) R1342271
theorem R237761 : Reach 237761 := rs (se 2 (by rfl) ⟨89160, by rfl⟩) R178321
theorem R107513 : Reach 107513 := rs (se 2 (by rfl) ⟨40317, by rfl⟩) R80635
theorem R566351 : Reach 566351 := rs (se 1 (by rfl) ⟨424763, by rfl⟩) R849527
theorem R42665 : Reach 42665 := rs (se 2 (by rfl) ⟨15999, by rfl⟩) R31999
theorem R42779 : Reach 42779 := rs (se 1 (by rfl) ⟨32084, by rfl⟩) R64169
theorem R141587 : Reach 141587 := rs (se 1 (by rfl) ⟨106190, by rfl⟩) R212381
theorem R109775 : Reach 109775 := rs (se 1 (by rfl) ⟨82331, by rfl⟩) R164663
theorem R77051 : Reach 77051 := rs (se 1 (by rfl) ⟨57788, by rfl⟩) R115577
theorem R45383 : Reach 45383 := rs (se 1 (by rfl) ⟨34037, by rfl⟩) R68075
theorem R439177 : Reach 439177 := rs (se 2 (by rfl) ⟨164691, by rfl⟩) R329383
theorem R373967 : Reach 373967 := rs (se 1 (by rfl) ⟨280475, by rfl⟩) R560951
theorem R46571 : Reach 46571 := rs (se 1 (by rfl) ⟨34928, by rfl⟩) R69857
theorem R1129211 : Reach 1129211 := rs (se 1 (by rfl) ⟨846908, by rfl⟩) R1693817
theorem R48439 : Reach 48439 := rs (se 1 (by rfl) ⟨36329, by rfl⟩) R72659
theorem R49855 : Reach 49855 := rs (se 1 (by rfl) ⟨37391, by rfl⟩) R74783
theorem R149039 : Reach 149039 := rs (se 1 (by rfl) ⟨111779, by rfl⟩) R223559
theorem R1165913 : Reach 1165913 := rs (se 2 (by rfl) ⟨437217, by rfl⟩) R874435
theorem R150335 : Reach 150335 := rs (se 1 (by rfl) ⟨112751, by rfl⟩) R225503
theorem R117719 : Reach 117719 := rs (se 1 (by rfl) ⟨88289, by rfl⟩) R176579
theorem R543743 : Reach 543743 := rs (se 1 (by rfl) ⟨407807, by rfl⟩) R815615
theorem R445601 : Reach 445601 := rs (se 2 (by rfl) ⟨167100, by rfl⟩) R334201
theorem R314927 : Reach 314927 := rs (se 1 (by rfl) ⟨236195, by rfl⟩) R472391
theorem R1199809 : Reach 1199809 := rs (se 2 (by rfl) ⟨449928, by rfl⟩) R899857
theorem R153899 : Reach 153899 := rs (se 1 (by rfl) ⟨115424, by rfl⟩) R230849
theorem R55723 : Reach 55723 := rs (se 1 (by rfl) ⟨41792, by rfl⟩) R83585
theorem R188527 : Reach 188527 := rs (se 1 (by rfl) ⟨141395, by rfl⟩) R282791
theorem R1466657 : Reach 1466657 := rs (se 2 (by rfl) ⟨549996, by rfl⟩) R1099993
theorem R254825 : Reach 254825 := rs (se 2 (by rfl) ⟨95559, by rfl⟩) R191119
theorem R58451 : Reach 58451 := rs (se 1 (by rfl) ⟨43838, by rfl⟩) R87677
theorem R223165 : Reach 223165 := rs (se 3 (by rfl) ⟨41843, by rfl⟩) R83687
theorem R28111 : Reach 28111 := rs (se 1 (by rfl) ⟨21083, by rfl⟩) R42167
theorem R159515 : Reach 159515 := rs (se 1 (by rfl) ⟨119636, by rfl⟩) R239273
theorem R356543 : Reach 356543 := rs (se 1 (by rfl) ⟨267407, by rfl⟩) R534815
theorem R29167 : Reach 29167 := rs (se 1 (by rfl) ⟨21875, by rfl⟩) R43751
theorem R63355 : Reach 63355 := rs (se 1 (by rfl) ⟨47516, by rfl⟩) R95033
theorem R30943 : Reach 30943 := rs (se 1 (by rfl) ⟨23207, by rfl⟩) R46415
theorem R96551 : Reach 96551 := rs (se 1 (by rfl) ⟨72413, by rfl⟩) R144827
theorem R98279 : Reach 98279 := rs (se 1 (by rfl) ⟨73709, by rfl⟩) R147419
theorem R131665 : Reach 131665 := rs (se 2 (by rfl) ⟨49374, by rfl⟩) R98749
theorem R4915829 : Reach 4915829 := rs (se 5 (by rfl) ⟨230429, by rfl⟩) R460859
theorem R623477 : Reach 623477 := rs (se 5 (by rfl) ⟨29225, by rfl⟩) R58451
theorem R66473 : Reach 66473 := rs (se 2 (by rfl) ⟨24927, by rfl⟩) R49855
theorem R99359 : Reach 99359 := rs (se 1 (by rfl) ⟨74519, by rfl⟩) R149039
theorem R919259 : Reach 919259 := rs (se 1 (by rfl) ⟨689444, by rfl⟩) R1378889
theorem R100223 : Reach 100223 := rs (se 1 (by rfl) ⟨75167, by rfl⟩) R150335
theorem R3803125 : Reach 3803125 := rs (se 5 (by rfl) ⟨178271, by rfl⟩) R356543
theorem R362495 : Reach 362495 := rs (se 1 (by rfl) ⟨271871, by rfl⟩) R543743
theorem R297067 : Reach 297067 := rs (se 1 (by rfl) ⟨222800, by rfl⟩) R445601
theorem R297553 : Reach 297553 := rs (se 2 (by rfl) ⟨111582, by rfl⟩) R223165
theorem R102599 : Reach 102599 := rs (se 1 (by rfl) ⟨76949, by rfl⟩) R153899
theorem R169883 : Reach 169883 := rs (se 1 (by rfl) ⟨127412, by rfl⟩) R254825
theorem R71675 : Reach 71675 := rs (se 1 (by rfl) ⟨53756, by rfl⟩) R107513
theorem R73183 : Reach 73183 := rs (se 1 (by rfl) ⟨54887, by rfl⟩) R109775
theorem R106343 : Reach 106343 := rs (se 1 (by rfl) ⟨79757, by rfl⟩) R159515
theorem R41257 : Reach 41257 := rs (se 2 (by rfl) ⟨15471, by rfl⟩) R30943
theorem R74297 : Reach 74297 := rs (se 2 (by rfl) ⟨27861, by rfl⟩) R55723
theorem R1057961 : Reach 1057961 := rs (se 2 (by rfl) ⟨396735, by rfl⟩) R793471
theorem R140777 : Reach 140777 := rs (se 2 (by rfl) ⟨52791, by rfl⟩) R105583
theorem R44015 : Reach 44015 := rs (se 1 (by rfl) ⟨33011, by rfl⟩) R66023
theorem R44087 : Reach 44087 := rs (se 1 (by rfl) ⟨33065, by rfl⟩) R66131
theorem R44267 : Reach 44267 := rs (se 1 (by rfl) ⟨33200, by rfl⟩) R66401
theorem R78479 : Reach 78479 := rs (se 1 (by rfl) ⟨58859, by rfl⟩) R117719
theorem R46079 : Reach 46079 := rs (se 1 (by rfl) ⟨34559, by rfl⟩) R69119
theorem R209951 : Reach 209951 := rs (se 1 (by rfl) ⟨157463, by rfl⟩) R314927
theorem R46127 : Reach 46127 := rs (se 1 (by rfl) ⟨34595, by rfl⟩) R69191
theorem R177455 : Reach 177455 := rs (se 1 (by rfl) ⟨133091, by rfl⟩) R266183
theorem R377567 : Reach 377567 := rs (se 1 (by rfl) ⟨283175, by rfl⟩) R566351
theorem R51367 : Reach 51367 := rs (se 1 (by rfl) ⟨38525, by rfl⟩) R77051
theorem R84473 : Reach 84473 := rs (se 2 (by rfl) ⟨31677, by rfl⟩) R63355
theorem R249311 : Reach 249311 := rs (se 1 (by rfl) ⟨186983, by rfl⟩) R373967
theorem R251369 : Reach 251369 := rs (se 2 (by rfl) ⟨94263, by rfl⟩) R188527
theorem R777275 : Reach 777275 := rs (se 1 (by rfl) ⟨582956, by rfl⟩) R1165913
theorem R614479 : Reach 614479 := rs (se 1 (by rfl) ⟨460859, by rfl⟩) R921719
theorem R157463 : Reach 157463 := rs (se 1 (by rfl) ⟨118097, by rfl⟩) R236195
theorem R1599745 : Reach 1599745 := rs (se 2 (by rfl) ⟨599904, by rfl⟩) R1199809
theorem R2386259 : Reach 2386259 := rs (se 1 (by rfl) ⟨1789694, by rfl⟩) R3579389
theorem R158507 : Reach 158507 := rs (se 1 (by rfl) ⟨118880, by rfl⟩) R237761
theorem R977771 : Reach 977771 := rs (se 1 (by rfl) ⟨733328, by rfl⟩) R1466657
theorem R28443 : Reach 28443 := rs (se 1 (by rfl) ⟨21332, by rfl⟩) R42665
theorem R585569 : Reach 585569 := rs (se 2 (by rfl) ⟨219588, by rfl⟩) R439177
theorem R28519 : Reach 28519 := rs (se 1 (by rfl) ⟨21389, by rfl⟩) R42779
theorem R94121 : Reach 94121 := rs (se 2 (by rfl) ⟨35295, by rfl⟩) R70591
theorem R94391 : Reach 94391 := rs (se 1 (by rfl) ⟨70793, by rfl⟩) R141587
theorem R95165 : Reach 95165 := rs (se 3 (by rfl) ⟨17843, by rfl⟩) R35687
theorem R30255 : Reach 30255 := rs (se 1 (by rfl) ⟨22691, by rfl⟩) R45383
theorem R31047 : Reach 31047 := rs (se 1 (by rfl) ⟨23285, by rfl⟩) R46571
theorem R64367 : Reach 64367 := rs (se 1 (by rfl) ⟨48275, by rfl⟩) R96551
theorem R64585 : Reach 64585 := rs (se 2 (by rfl) ⟨24219, by rfl⟩) R48439
theorem R752807 : Reach 752807 := rs (se 1 (by rfl) ⟨564605, by rfl⟩) R1129211
theorem R65519 : Reach 65519 := rs (se 1 (by rfl) ⟨49139, by rfl⟩) R98279
theorem R819305 : Reach 819305 := rs (se 2 (by rfl) ⟨307239, by rfl⟩) R614479
theorem R3277219 : Reach 3277219 := rs (se 1 (by rfl) ⟨2457914, by rfl⟩) R4915829
theorem R66239 : Reach 66239 := rs (se 1 (by rfl) ⟨49679, by rfl⟩) R99359
theorem R66815 : Reach 66815 := rs (se 1 (by rfl) ⟨50111, by rfl⟩) R100223
theorem R166207 : Reach 166207 := rs (se 1 (by rfl) ⟨124655, by rfl⟩) R249311
theorem R68399 : Reach 68399 := rs (se 1 (by rfl) ⟨51299, by rfl⟩) R102599
theorem R396089 : Reach 396089 := rs (se 2 (by rfl) ⟨148533, by rfl⟩) R297067
theorem R68489 : Reach 68489 := rs (se 2 (by rfl) ⟨25683, by rfl⟩) R51367
theorem R2132993 : Reach 2132993 := rs (se 2 (by rfl) ⟨799872, by rfl⟩) R1599745
theorem R396737 : Reach 396737 := rs (se 2 (by rfl) ⟨148776, by rfl⟩) R297553
theorem R167579 : Reach 167579 := rs (se 1 (by rfl) ⟨125684, by rfl⟩) R251369
theorem R70895 : Reach 70895 := rs (se 1 (by rfl) ⟨53171, by rfl⟩) R106343
theorem R104975 : Reach 104975 := rs (se 1 (by rfl) ⟨78731, by rfl⟩) R157463
theorem R105671 : Reach 105671 := rs (se 1 (by rfl) ⟨79253, by rfl⟩) R158507
theorem R139967 : Reach 139967 := rs (se 1 (by rfl) ⟨104975, by rfl⟩) R209951
theorem R42911 : Reach 42911 := rs (se 1 (by rfl) ⟨32183, by rfl⟩) R64367
theorem R501871 : Reach 501871 := rs (se 1 (by rfl) ⟨376403, by rfl⟩) R752807
theorem R43679 : Reach 43679 := rs (se 1 (by rfl) ⟨32759, by rfl⟩) R65519
theorem R44315 : Reach 44315 := rs (se 1 (by rfl) ⟨33236, by rfl⟩) R66473
theorem R175553 : Reach 175553 := rs (se 2 (by rfl) ⟨65832, by rfl⟩) R131665
theorem R241663 : Reach 241663 := rs (se 1 (by rfl) ⟨181247, by rfl⟩) R362495
theorem R113255 : Reach 113255 := rs (se 1 (by rfl) ⟨84941, by rfl⟩) R169883
theorem R47783 : Reach 47783 := rs (se 1 (by rfl) ⟨35837, by rfl⟩) R71675
theorem R49531 : Reach 49531 := rs (se 1 (by rfl) ⟨37148, by rfl⟩) R74297
theorem R705307 : Reach 705307 := rs (se 1 (by rfl) ⟨528980, by rfl⟩) R1057961
theorem R1590839 : Reach 1590839 := rs (se 1 (by rfl) ⟨1193129, by rfl⟩) R2386259
theorem R52319 : Reach 52319 := rs (se 1 (by rfl) ⟨39239, by rfl⟩) R78479
theorem R118303 : Reach 118303 := rs (se 1 (by rfl) ⟨88727, by rfl⟩) R177455
theorem R86113 : Reach 86113 := rs (se 2 (by rfl) ⟨32292, by rfl⟩) R64585
theorem R55009 : Reach 55009 := rs (se 2 (by rfl) ⟨20628, by rfl⟩) R41257
theorem R251711 : Reach 251711 := rs (se 1 (by rfl) ⟨188783, by rfl⟩) R377567
theorem R415651 : Reach 415651 := rs (se 1 (by rfl) ⟨311738, by rfl⟩) R623477
theorem R612839 : Reach 612839 := rs (se 1 (by rfl) ⟨459629, by rfl⟩) R919259
theorem R56315 : Reach 56315 := rs (se 1 (by rfl) ⟨42236, by rfl⟩) R84473
theorem R5070833 : Reach 5070833 := rs (se 2 (by rfl) ⟨1901562, by rfl⟩) R3803125
theorem R518183 : Reach 518183 := rs (se 1 (by rfl) ⟨388637, by rfl⟩) R777275
theorem R93851 : Reach 93851 := rs (se 1 (by rfl) ⟨70388, by rfl⟩) R140777
theorem R651847 : Reach 651847 := rs (se 1 (by rfl) ⟨488885, by rfl⟩) R977771
theorem R29343 : Reach 29343 := rs (se 1 (by rfl) ⟨22007, by rfl⟩) R44015
theorem R29391 : Reach 29391 := rs (se 1 (by rfl) ⟨22043, by rfl⟩) R44087
theorem R29511 : Reach 29511 := rs (se 1 (by rfl) ⟨22133, by rfl⟩) R44267
theorem R390379 : Reach 390379 := rs (se 1 (by rfl) ⟨292784, by rfl⟩) R585569
theorem R62747 : Reach 62747 := rs (se 1 (by rfl) ⟨47060, by rfl⟩) R94121
theorem R62927 : Reach 62927 := rs (se 1 (by rfl) ⟨47195, by rfl⟩) R94391
theorem R63443 : Reach 63443 := rs (se 1 (by rfl) ⟨47582, by rfl⟩) R95165
theorem R30719 : Reach 30719 := rs (se 1 (by rfl) ⟨23039, by rfl⟩) R46079
theorem R30751 : Reach 30751 := rs (se 1 (by rfl) ⟨23063, by rfl⟩) R46127
theorem R97577 : Reach 97577 := rs (se 2 (by rfl) ⟨36591, by rfl⟩) R73183
theorem R66041 : Reach 66041 := rs (se 2 (by rfl) ⟨24765, by rfl⟩) R49531
theorem R264059 : Reach 264059 := rs (se 1 (by rfl) ⟨198044, by rfl⟩) R396089
theorem R34879 : Reach 34879 := rs (se 1 (by rfl) ⟨26159, by rfl⟩) R52319
theorem R264491 : Reach 264491 := rs (se 1 (by rfl) ⟨198368, by rfl⟩) R396737
theorem R167807 : Reach 167807 := rs (se 1 (by rfl) ⟨125855, by rfl⟩) R251711
theorem R69983 : Reach 69983 := rs (se 1 (by rfl) ⟨52487, by rfl⟩) R104975
theorem R3380555 : Reach 3380555 := rs (se 1 (by rfl) ⟨2535416, by rfl⟩) R5070833
theorem R73345 : Reach 73345 := rs (se 2 (by rfl) ⟨27504, by rfl⟩) R55009
theorem R630949 : Reach 630949 := rs (se 4 (by rfl) ⟨59151, by rfl⟩) R118303
theorem R41831 : Reach 41831 := rs (se 1 (by rfl) ⟨31373, by rfl⟩) R62747
theorem R41951 : Reach 41951 := rs (se 1 (by rfl) ⟨31463, by rfl⟩) R62927
theorem R42295 : Reach 42295 := rs (se 1 (by rfl) ⟨31721, by rfl⟩) R63443
theorem R75503 : Reach 75503 := rs (se 1 (by rfl) ⟨56627, by rfl⟩) R113255
theorem R44159 : Reach 44159 := rs (se 1 (by rfl) ⟨33119, by rfl⟩) R66239
theorem R4369625 : Reach 4369625 := rs (se 2 (by rfl) ⟨1638609, by rfl⟩) R3277219
theorem R44543 : Reach 44543 := rs (se 1 (by rfl) ⟨33407, by rfl⟩) R66815
theorem R1060559 : Reach 1060559 := rs (se 1 (by rfl) ⟨795419, by rfl⟩) R1590839
theorem R45599 : Reach 45599 := rs (se 1 (by rfl) ⟨34199, by rfl⟩) R68399
theorem R45659 : Reach 45659 := rs (se 1 (by rfl) ⟨34244, by rfl⟩) R68489
theorem R1421995 : Reach 1421995 := rs (se 1 (by rfl) ⟨1066496, by rfl⟩) R2132993
theorem R111719 : Reach 111719 := rs (se 1 (by rfl) ⟨83789, by rfl⟩) R167579
theorem R669161 : Reach 669161 := rs (se 2 (by rfl) ⟨250935, by rfl⟩) R501871
theorem R47263 : Reach 47263 := rs (se 1 (by rfl) ⟨35447, by rfl⟩) R70895
theorem R408559 : Reach 408559 := rs (se 1 (by rfl) ⟨306419, by rfl⟩) R612839
theorem R114817 : Reach 114817 := rs (se 2 (by rfl) ⟨43056, by rfl⟩) R86113
theorem R869129 : Reach 869129 := rs (se 2 (by rfl) ⟨325923, by rfl⟩) R651847
theorem R345455 : Reach 345455 := rs (se 1 (by rfl) ⟨259091, by rfl⟩) R518183
theorem R117035 : Reach 117035 := rs (se 1 (by rfl) ⟨87776, by rfl⟩) R175553
theorem R150173 : Reach 150173 := rs (se 3 (by rfl) ⟨28157, by rfl⟩) R56315
theorem R281789 : Reach 281789 := rs (se 3 (by rfl) ⟨52835, by rfl⟩) R105671
theorem R546203 : Reach 546203 := rs (se 1 (by rfl) ⟨409652, by rfl⟩) R819305
theorem R940409 : Reach 940409 := rs (se 2 (by rfl) ⟨352653, by rfl⟩) R705307
theorem R221609 : Reach 221609 := rs (se 2 (by rfl) ⟨83103, by rfl⟩) R166207
theorem R322217 : Reach 322217 := rs (se 2 (by rfl) ⟨120831, by rfl⟩) R241663
theorem R93311 : Reach 93311 := rs (se 1 (by rfl) ⟨69983, by rfl⟩) R139967
theorem R28607 : Reach 28607 := rs (se 1 (by rfl) ⟨21455, by rfl⟩) R42911
theorem R520505 : Reach 520505 := rs (se 2 (by rfl) ⟨195189, by rfl⟩) R390379
theorem R29119 : Reach 29119 := rs (se 1 (by rfl) ⟨21839, by rfl⟩) R43679
theorem R29543 : Reach 29543 := rs (se 1 (by rfl) ⟨22157, by rfl⟩) R44315
theorem R62567 : Reach 62567 := rs (se 1 (by rfl) ⟨46925, by rfl⟩) R93851
theorem R554201 : Reach 554201 := rs (se 2 (by rfl) ⟨207825, by rfl⟩) R415651
theorem R31855 : Reach 31855 := rs (se 1 (by rfl) ⟨23891, by rfl⟩) R47783
theorem R65051 : Reach 65051 := rs (se 1 (by rfl) ⟨48788, by rfl⟩) R97577
theorem R230303 : Reach 230303 := rs (se 1 (by rfl) ⟨172727, by rfl⟩) R345455
theorem R100115 : Reach 100115 := rs (se 1 (by rfl) ⟨75086, by rfl⟩) R150173
theorem R364135 : Reach 364135 := rs (se 1 (by rfl) ⟨273101, by rfl⟩) R546203
theorem R626939 : Reach 626939 := rs (se 1 (by rfl) ⟨470204, by rfl⟩) R940409
theorem R201341 : Reach 201341 := rs (se 3 (by rfl) ⟨37751, by rfl⟩) R75503
theorem R41711 : Reach 41711 := rs (se 1 (by rfl) ⟨31283, by rfl⟩) R62567
theorem R74479 : Reach 74479 := rs (se 1 (by rfl) ⟨55859, by rfl⟩) R111719
theorem R369467 : Reach 369467 := rs (se 1 (by rfl) ⟨277100, by rfl⟩) R554201
theorem R42473 : Reach 42473 := rs (se 2 (by rfl) ⟨15927, by rfl⟩) R31855
theorem R43367 : Reach 43367 := rs (se 1 (by rfl) ⟨32525, by rfl⟩) R65051
theorem R44027 : Reach 44027 := rs (se 1 (by rfl) ⟨33020, by rfl⟩) R66041
theorem R176039 : Reach 176039 := rs (se 1 (by rfl) ⟨132029, by rfl⟩) R264059
theorem R176327 : Reach 176327 := rs (se 1 (by rfl) ⟨132245, by rfl⟩) R264491
theorem R78023 : Reach 78023 := rs (se 1 (by rfl) ⟨58517, by rfl⟩) R117035
theorem R111871 : Reach 111871 := rs (se 1 (by rfl) ⟨83903, by rfl⟩) R167807
theorem R46505 : Reach 46505 := rs (se 2 (by rfl) ⟨17439, by rfl⟩) R34879
theorem R46655 : Reach 46655 := rs (se 1 (by rfl) ⟨34991, by rfl⟩) R69983
theorem R147739 : Reach 147739 := rs (se 1 (by rfl) ⟨110804, by rfl⟩) R221609
theorem R214811 : Reach 214811 := rs (se 1 (by rfl) ⟨161108, by rfl⟩) R322217
theorem R707039 : Reach 707039 := rs (se 1 (by rfl) ⟨530279, by rfl⟩) R1060559
theorem R347003 : Reach 347003 := rs (se 1 (by rfl) ⟨260252, by rfl⟩) R520505
theorem R446107 : Reach 446107 := rs (se 1 (by rfl) ⟨334580, by rfl⟩) R669161
theorem R544745 : Reach 544745 := rs (se 2 (by rfl) ⟨204279, by rfl⟩) R408559
theorem R153089 : Reach 153089 := rs (se 2 (by rfl) ⟨57408, by rfl⟩) R114817
theorem R841265 : Reach 841265 := rs (se 2 (by rfl) ⟨315474, by rfl⟩) R630949
theorem R579419 : Reach 579419 := rs (se 1 (by rfl) ⟨434564, by rfl⟩) R869129
theorem R56393 : Reach 56393 := rs (se 2 (by rfl) ⟨21147, by rfl⟩) R42295
theorem R187859 : Reach 187859 := rs (se 1 (by rfl) ⟨140894, by rfl⟩) R281789
theorem R2253703 : Reach 2253703 := rs (se 1 (by rfl) ⟨1690277, by rfl⟩) R3380555
theorem R27887 : Reach 27887 := rs (se 1 (by rfl) ⟨20915, by rfl⟩) R41831
theorem R27967 : Reach 27967 := rs (se 1 (by rfl) ⟨20975, by rfl⟩) R41951
theorem R1895993 : Reach 1895993 := rs (se 2 (by rfl) ⟨710997, by rfl⟩) R1421995
theorem R62207 : Reach 62207 := rs (se 1 (by rfl) ⟨46655, by rfl⟩) R93311
theorem R29439 : Reach 29439 := rs (se 1 (by rfl) ⟨22079, by rfl⟩) R44159
theorem R2913083 : Reach 2913083 := rs (se 1 (by rfl) ⟨2184812, by rfl⟩) R4369625
theorem R29695 : Reach 29695 := rs (se 1 (by rfl) ⟨22271, by rfl⟩) R44543
theorem R63017 : Reach 63017 := rs (se 2 (by rfl) ⟨23631, by rfl⟩) R47263
theorem R30399 : Reach 30399 := rs (se 1 (by rfl) ⟨22799, by rfl⟩) R45599
theorem R30439 : Reach 30439 := rs (se 1 (by rfl) ⟨22829, by rfl⟩) R45659
theorem R97793 : Reach 97793 := rs (se 2 (by rfl) ⟨36672, by rfl⟩) R73345
theorem R196985 : Reach 196985 := rs (se 2 (by rfl) ⟨73869, by rfl⟩) R147739
theorem R99305 : Reach 99305 := rs (se 2 (by rfl) ⟨37239, by rfl⟩) R74479
theorem R66743 : Reach 66743 := rs (se 1 (by rfl) ⟨50057, by rfl⟩) R100115
theorem R231335 : Reach 231335 := rs (se 1 (by rfl) ⟨173501, by rfl⟩) R347003
theorem R363163 : Reach 363163 := rs (se 1 (by rfl) ⟨272372, by rfl⟩) R544745
theorem R134227 : Reach 134227 := rs (se 1 (by rfl) ⟨100670, by rfl⟩) R201341
theorem R102059 : Reach 102059 := rs (se 1 (by rfl) ⟨76544, by rfl⟩) R153089
theorem R560843 : Reach 560843 := rs (se 1 (by rfl) ⟨420632, by rfl⟩) R841265
theorem R37595 : Reach 37595 := rs (se 1 (by rfl) ⟨28196, by rfl⟩) R56393
theorem R594809 : Reach 594809 := rs (se 2 (by rfl) ⟨223053, by rfl⟩) R446107
theorem R41471 : Reach 41471 := rs (se 1 (by rfl) ⟨31103, by rfl⟩) R62207
theorem R1942055 : Reach 1942055 := rs (se 1 (by rfl) ⟨1456541, by rfl⟩) R2913083
theorem R42011 : Reach 42011 := rs (se 1 (by rfl) ⟨31508, by rfl⟩) R63017
theorem R143207 : Reach 143207 := rs (se 1 (by rfl) ⟨107405, by rfl⟩) R214811
theorem R471359 : Reach 471359 := rs (se 1 (by rfl) ⟨353519, by rfl⟩) R707039
theorem R246311 : Reach 246311 := rs (se 1 (by rfl) ⟨184733, by rfl⟩) R369467
theorem R149161 : Reach 149161 := rs (se 2 (by rfl) ⟨55935, by rfl⟩) R111871
theorem R1263995 : Reach 1263995 := rs (se 1 (by rfl) ⟨947996, by rfl⟩) R1895993
theorem R117359 : Reach 117359 := rs (se 1 (by rfl) ⟨88019, by rfl⟩) R176039
theorem R117551 : Reach 117551 := rs (se 1 (by rfl) ⟨88163, by rfl⟩) R176327
theorem R52015 : Reach 52015 := rs (se 1 (by rfl) ⟨39011, by rfl⟩) R78023
theorem R153535 : Reach 153535 := rs (se 1 (by rfl) ⟨115151, by rfl⟩) R230303
theorem R3004937 : Reach 3004937 := rs (se 2 (by rfl) ⟨1126851, by rfl⟩) R2253703
theorem R417959 : Reach 417959 := rs (se 1 (by rfl) ⟨313469, by rfl⟩) R626939
theorem R386279 : Reach 386279 := rs (se 1 (by rfl) ⟨289709, by rfl⟩) R579419
theorem R485513 : Reach 485513 := rs (se 2 (by rfl) ⟨182067, by rfl⟩) R364135
theorem R125239 : Reach 125239 := rs (se 1 (by rfl) ⟨93929, by rfl⟩) R187859
theorem R27807 : Reach 27807 := rs (se 1 (by rfl) ⟨20855, by rfl⟩) R41711
theorem R28315 : Reach 28315 := rs (se 1 (by rfl) ⟨21236, by rfl⟩) R42473
theorem R28911 : Reach 28911 := rs (se 1 (by rfl) ⟨21683, by rfl⟩) R43367
theorem R29351 : Reach 29351 := rs (se 1 (by rfl) ⟨22013, by rfl⟩) R44027
theorem R31003 : Reach 31003 := rs (se 1 (by rfl) ⟨23252, by rfl⟩) R46505
theorem R31103 : Reach 31103 := rs (se 1 (by rfl) ⟨23327, by rfl⟩) R46655
theorem R65195 : Reach 65195 := rs (se 1 (by rfl) ⟨48896, by rfl⟩) R97793
theorem R131323 : Reach 131323 := rs (se 1 (by rfl) ⟨98492, by rfl⟩) R196985
theorem R164207 : Reach 164207 := rs (se 1 (by rfl) ⟨123155, by rfl⟩) R246311
theorem R66203 : Reach 66203 := rs (se 1 (by rfl) ⟨49652, by rfl⟩) R99305
theorem R100253 : Reach 100253 := rs (se 3 (by rfl) ⟨18797, by rfl⟩) R37595
theorem R198881 : Reach 198881 := rs (se 2 (by rfl) ⟨74580, by rfl⟩) R149161
theorem R68039 : Reach 68039 := rs (se 1 (by rfl) ⟨51029, by rfl⟩) R102059
theorem R166985 : Reach 166985 := rs (se 2 (by rfl) ⟨62619, by rfl⟩) R125239
theorem R396539 : Reach 396539 := rs (se 1 (by rfl) ⟨297404, by rfl⟩) R594809
theorem R69353 : Reach 69353 := rs (se 2 (by rfl) ⟨26007, by rfl⟩) R52015
theorem R2003291 : Reach 2003291 := rs (se 1 (by rfl) ⟨1502468, by rfl⟩) R3004937
theorem R204713 : Reach 204713 := rs (se 2 (by rfl) ⟨76767, by rfl⟩) R153535
theorem R43463 : Reach 43463 := rs (se 1 (by rfl) ⟨32597, by rfl⟩) R65195
theorem R44495 : Reach 44495 := rs (se 1 (by rfl) ⟨33371, by rfl⟩) R66743
theorem R1256957 : Reach 1256957 := rs (se 3 (by rfl) ⟨235679, by rfl⟩) R471359
theorem R78239 : Reach 78239 := rs (se 1 (by rfl) ⟨58679, by rfl⟩) R117359
theorem R78367 : Reach 78367 := rs (se 1 (by rfl) ⟨58775, by rfl⟩) R117551
theorem R373895 : Reach 373895 := rs (se 1 (by rfl) ⟨280421, by rfl⟩) R560843
theorem R178969 : Reach 178969 := rs (se 2 (by rfl) ⟨67113, by rfl⟩) R134227
theorem R278639 : Reach 278639 := rs (se 1 (by rfl) ⟨208979, by rfl⟩) R417959
theorem R1294703 : Reach 1294703 := rs (se 1 (by rfl) ⟨971027, by rfl⟩) R1942055
theorem R313469 : Reach 313469 := rs (se 3 (by rfl) ⟨58775, by rfl⟩) R117551
theorem R154223 : Reach 154223 := rs (se 1 (by rfl) ⟨115667, by rfl⟩) R231335
theorem R842663 : Reach 842663 := rs (se 1 (by rfl) ⟨631997, by rfl⟩) R1263995
theorem R484217 : Reach 484217 := rs (se 2 (by rfl) ⟨181581, by rfl⟩) R363163
theorem R27647 : Reach 27647 := rs (se 1 (by rfl) ⟨20735, by rfl⟩) R41471
theorem R28007 : Reach 28007 := rs (se 1 (by rfl) ⟨21005, by rfl⟩) R42011
theorem R257519 : Reach 257519 := rs (se 1 (by rfl) ⟨193139, by rfl⟩) R386279
theorem R323675 : Reach 323675 := rs (se 1 (by rfl) ⟨242756, by rfl⟩) R485513
theorem R95471 : Reach 95471 := rs (se 1 (by rfl) ⟨71603, by rfl⟩) R143207
theorem R66835 : Reach 66835 := rs (se 1 (by rfl) ⟨50126, by rfl⟩) R100253
theorem R132587 : Reach 132587 := rs (se 1 (by rfl) ⟨99440, by rfl⟩) R198881
theorem R264359 : Reach 264359 := rs (se 1 (by rfl) ⟨198269, by rfl⟩) R396539
theorem R102815 : Reach 102815 := rs (se 1 (by rfl) ⟨77111, by rfl⟩) R154223
theorem R561775 : Reach 561775 := rs (se 1 (by rfl) ⟨421331, by rfl⟩) R842663
theorem R136475 : Reach 136475 := rs (se 1 (by rfl) ⟨102356, by rfl⟩) R204713
theorem R104489 : Reach 104489 := rs (se 2 (by rfl) ⟨39183, by rfl⟩) R78367
theorem R171679 : Reach 171679 := rs (se 1 (by rfl) ⟨128759, by rfl⟩) R257519
theorem R238625 : Reach 238625 := rs (se 2 (by rfl) ⟨89484, by rfl⟩) R178969
theorem R109471 : Reach 109471 := rs (se 1 (by rfl) ⟨82103, by rfl⟩) R164207
theorem R863135 : Reach 863135 := rs (se 1 (by rfl) ⟨647351, by rfl⟩) R1294703
theorem R175097 : Reach 175097 := rs (se 2 (by rfl) ⟨65661, by rfl⟩) R131323
theorem R44135 : Reach 44135 := rs (se 1 (by rfl) ⟨33101, by rfl⟩) R66203
theorem R208979 : Reach 208979 := rs (se 1 (by rfl) ⟨156734, by rfl⟩) R313469
theorem R45359 : Reach 45359 := rs (se 1 (by rfl) ⟨34019, by rfl⟩) R68039
theorem R111323 : Reach 111323 := rs (se 1 (by rfl) ⟨83492, by rfl⟩) R166985
theorem R46235 : Reach 46235 := rs (se 1 (by rfl) ⟨34676, by rfl⟩) R69353
theorem R115901 : Reach 115901 := rs (se 3 (by rfl) ⟨21731, by rfl⟩) R43463
theorem R837971 : Reach 837971 := rs (se 1 (by rfl) ⟨628478, by rfl⟩) R1256957
theorem R215783 : Reach 215783 := rs (se 1 (by rfl) ⟨161837, by rfl⟩) R323675
theorem R52159 : Reach 52159 := rs (se 1 (by rfl) ⟨39119, by rfl⟩) R78239
theorem R249263 : Reach 249263 := rs (se 1 (by rfl) ⟨186947, by rfl⟩) R373895
theorem R185759 : Reach 185759 := rs (se 1 (by rfl) ⟨139319, by rfl⟩) R278639
theorem R1335527 : Reach 1335527 := rs (se 1 (by rfl) ⟨1001645, by rfl⟩) R2003291
theorem R322811 : Reach 322811 := rs (se 1 (by rfl) ⟨242108, by rfl⟩) R484217
theorem R28975 : Reach 28975 := rs (se 1 (by rfl) ⟨21731, by rfl⟩) R43463
theorem R29663 : Reach 29663 := rs (se 1 (by rfl) ⟨22247, by rfl⟩) R44495
theorem R63647 : Reach 63647 := rs (se 1 (by rfl) ⟨47735, by rfl⟩) R95471
theorem R558647 : Reach 558647 := rs (se 1 (by rfl) ⟨418985, by rfl⟩) R837971
theorem R166175 : Reach 166175 := rs (se 1 (by rfl) ⟨124631, by rfl⟩) R249263
theorem R68543 : Reach 68543 := rs (se 1 (by rfl) ⟨51407, by rfl⟩) R102815
theorem R69545 : Reach 69545 := rs (se 2 (by rfl) ⟨26079, by rfl⟩) R52159
theorem R69659 : Reach 69659 := rs (se 1 (by rfl) ⟨52244, by rfl⟩) R104489
theorem R890351 : Reach 890351 := rs (se 1 (by rfl) ⟨667763, by rfl⟩) R1335527
theorem R139319 : Reach 139319 := rs (se 1 (by rfl) ⟨104489, by rfl⟩) R208979
theorem R74215 : Reach 74215 := rs (se 1 (by rfl) ⟨55661, by rfl⟩) R111323
theorem R42431 : Reach 42431 := rs (se 1 (by rfl) ⟨31823, by rfl⟩) R63647
theorem R77267 : Reach 77267 := rs (se 1 (by rfl) ⟨57950, by rfl⟩) R115901
theorem R176239 : Reach 176239 := rs (se 1 (by rfl) ⟨132179, by rfl⟩) R264359
theorem R143855 : Reach 143855 := rs (se 1 (by rfl) ⟨107891, by rfl⟩) R215783
theorem R145961 : Reach 145961 := rs (se 2 (by rfl) ⟨54735, by rfl⟩) R109471
theorem R575423 : Reach 575423 := rs (se 1 (by rfl) ⟨431567, by rfl⟩) R863135
theorem R116731 : Reach 116731 := rs (se 1 (by rfl) ⟨87548, by rfl⟩) R175097
theorem R215207 : Reach 215207 := rs (se 1 (by rfl) ⟨161405, by rfl⟩) R322811
theorem R88391 : Reach 88391 := rs (se 1 (by rfl) ⟨66293, by rfl⟩) R132587
theorem R89113 : Reach 89113 := rs (se 2 (by rfl) ⟨33417, by rfl⟩) R66835
theorem R90983 : Reach 90983 := rs (se 1 (by rfl) ⟨68237, by rfl⟩) R136475
theorem R123839 : Reach 123839 := rs (se 1 (by rfl) ⟨92879, by rfl⟩) R185759
theorem R159083 : Reach 159083 := rs (se 1 (by rfl) ⟨119312, by rfl⟩) R238625
theorem R749033 : Reach 749033 := rs (se 2 (by rfl) ⟨280887, by rfl⟩) R561775
theorem R29423 : Reach 29423 := rs (se 1 (by rfl) ⟨22067, by rfl⟩) R44135
theorem R30239 : Reach 30239 := rs (se 1 (by rfl) ⟨22679, by rfl⟩) R45359
theorem R30823 : Reach 30823 := rs (se 1 (by rfl) ⟨23117, by rfl⟩) R46235
theorem R228905 : Reach 228905 := rs (se 2 (by rfl) ⟨85839, by rfl⟩) R171679
theorem R164389 : Reach 164389 := rs (se 4 (by rfl) ⟨15411, by rfl⟩) R30823
theorem R395813 : Reach 395813 := rs (se 4 (by rfl) ⟨37107, by rfl⟩) R74215
theorem R593567 : Reach 593567 := rs (se 1 (by rfl) ⟨445175, by rfl⟩) R890351
theorem R235709 : Reach 235709 := rs (se 3 (by rfl) ⟨44195, by rfl⟩) R88391
theorem R106055 : Reach 106055 := rs (se 1 (by rfl) ⟨79541, by rfl⟩) R159083
theorem R499355 : Reach 499355 := rs (se 1 (by rfl) ⟨374516, by rfl⟩) R749033
theorem R372431 : Reach 372431 := rs (se 1 (by rfl) ⟨279323, by rfl⟩) R558647
theorem R143471 : Reach 143471 := rs (se 1 (by rfl) ⟨107603, by rfl⟩) R215207
theorem R110783 : Reach 110783 := rs (se 1 (by rfl) ⟨83087, by rfl⟩) R166175
theorem R45695 : Reach 45695 := rs (se 1 (by rfl) ⟨34271, by rfl⟩) R68543
theorem R242621 : Reach 242621 := rs (se 3 (by rfl) ⟨45491, by rfl⟩) R90983
theorem R46363 : Reach 46363 := rs (se 1 (by rfl) ⟨34772, by rfl⟩) R69545
theorem R46439 : Reach 46439 := rs (se 1 (by rfl) ⟨34829, by rfl⟩) R69659
theorem R82559 : Reach 82559 := rs (se 1 (by rfl) ⟨61919, by rfl⟩) R123839
theorem R51511 : Reach 51511 := rs (se 1 (by rfl) ⟨38633, by rfl⟩) R77267
theorem R118817 : Reach 118817 := rs (se 2 (by rfl) ⟨44556, by rfl⟩) R89113
theorem R152603 : Reach 152603 := rs (se 1 (by rfl) ⟨114452, by rfl⟩) R228905
theorem R939941 : Reach 939941 := rs (se 4 (by rfl) ⟨88119, by rfl⟩) R176239
theorem R383615 : Reach 383615 := rs (se 1 (by rfl) ⟨287711, by rfl⟩) R575423
theorem R155641 : Reach 155641 := rs (se 2 (by rfl) ⟨58365, by rfl⟩) R116731
theorem R92879 : Reach 92879 := rs (se 1 (by rfl) ⟨69659, by rfl⟩) R139319
theorem R28287 : Reach 28287 := rs (se 1 (by rfl) ⟨21215, by rfl⟩) R42431
theorem R95903 : Reach 95903 := rs (se 1 (by rfl) ⟨71927, by rfl⟩) R143855
theorem R97307 : Reach 97307 := rs (se 1 (by rfl) ⟨72980, by rfl⟩) R145961
theorem R395711 : Reach 395711 := rs (se 1 (by rfl) ⟨296783, by rfl⟩) R593567
theorem R68681 : Reach 68681 := rs (se 2 (by rfl) ⟨25755, by rfl⟩) R51511
theorem R101735 : Reach 101735 := rs (se 1 (by rfl) ⟨76301, by rfl⟩) R152603
theorem R626627 : Reach 626627 := rs (se 1 (by rfl) ⟨469970, by rfl⟩) R939941
theorem R70703 : Reach 70703 := rs (se 1 (by rfl) ⟨53027, by rfl⟩) R106055
theorem R332903 : Reach 332903 := rs (se 1 (by rfl) ⟨249677, by rfl⟩) R499355
theorem R1055501 : Reach 1055501 := rs (se 3 (by rfl) ⟨197906, by rfl⟩) R395813
theorem R73855 : Reach 73855 := rs (se 1 (by rfl) ⟨55391, by rfl⟩) R110783
theorem R207521 : Reach 207521 := rs (se 2 (by rfl) ⟨77820, by rfl⟩) R155641
theorem R79211 : Reach 79211 := rs (se 1 (by rfl) ⟨59408, by rfl⟩) R118817
theorem R248287 : Reach 248287 := rs (se 1 (by rfl) ⟨186215, by rfl⟩) R372431
theorem R382589 : Reach 382589 := rs (se 3 (by rfl) ⟨71735, by rfl⟩) R143471
theorem R219185 : Reach 219185 := rs (se 2 (by rfl) ⟨82194, by rfl⟩) R164389
theorem R220157 : Reach 220157 := rs (se 3 (by rfl) ⟨41279, by rfl⟩) R82559
theorem R157139 : Reach 157139 := rs (se 1 (by rfl) ⟨117854, by rfl⟩) R235709
theorem R255743 : Reach 255743 := rs (se 1 (by rfl) ⟨191807, by rfl⟩) R383615
theorem R61817 : Reach 61817 := rs (se 2 (by rfl) ⟨23181, by rfl⟩) R46363
theorem R61919 : Reach 61919 := rs (se 1 (by rfl) ⟨46439, by rfl⟩) R92879
theorem R30463 : Reach 30463 := rs (se 1 (by rfl) ⟨22847, by rfl⟩) R45695
theorem R161747 : Reach 161747 := rs (se 1 (by rfl) ⟨121310, by rfl⟩) R242621
theorem R30959 : Reach 30959 := rs (se 1 (by rfl) ⟨23219, by rfl⟩) R46439
theorem R63935 : Reach 63935 := rs (se 1 (by rfl) ⟨47951, by rfl⟩) R95903
theorem R64871 : Reach 64871 := rs (se 1 (by rfl) ⟨48653, by rfl⟩) R97307
theorem R393893 : Reach 393893 := rs (se 4 (by rfl) ⟨36927, by rfl⟩) R73855
theorem R164845 : Reach 164845 := rs (se 3 (by rfl) ⟨30908, by rfl⟩) R61817
theorem R263807 : Reach 263807 := rs (se 1 (by rfl) ⟨197855, by rfl⟩) R395711
theorem R67823 : Reach 67823 := rs (se 1 (by rfl) ⟨50867, by rfl⟩) R101735
theorem R331049 : Reach 331049 := rs (se 2 (by rfl) ⟨124143, by rfl⟩) R248287
theorem R104759 : Reach 104759 := rs (se 1 (by rfl) ⟨78569, by rfl⟩) R157139
theorem R170495 : Reach 170495 := rs (se 1 (by rfl) ⟨127871, by rfl⟩) R255743
theorem R138347 : Reach 138347 := rs (se 1 (by rfl) ⟨103760, by rfl⟩) R207521
theorem R41279 : Reach 41279 := rs (se 1 (by rfl) ⟨30959, by rfl⟩) R61919
theorem R107831 : Reach 107831 := rs (se 1 (by rfl) ⟨80873, by rfl⟩) R161747
theorem R42623 : Reach 42623 := rs (se 1 (by rfl) ⟨31967, by rfl⟩) R63935
theorem R43247 : Reach 43247 := rs (se 1 (by rfl) ⟨32435, by rfl⟩) R64871
theorem R45787 : Reach 45787 := rs (se 1 (by rfl) ⟨34340, by rfl⟩) R68681
theorem R47135 : Reach 47135 := rs (se 1 (by rfl) ⟨35351, by rfl⟩) R70703
theorem R146123 : Reach 146123 := rs (se 1 (by rfl) ⟨109592, by rfl⟩) R219185
theorem R703667 : Reach 703667 := rs (se 1 (by rfl) ⟨527750, by rfl⟩) R1055501
theorem R146771 : Reach 146771 := rs (se 1 (by rfl) ⟨110078, by rfl⟩) R220157
theorem R52807 : Reach 52807 := rs (se 1 (by rfl) ⟨39605, by rfl⟩) R79211
theorem R221935 : Reach 221935 := rs (se 1 (by rfl) ⟨166451, by rfl⟩) R332903
theorem R255059 : Reach 255059 := rs (se 1 (by rfl) ⟨191294, by rfl⟩) R382589
theorem R1671005 : Reach 1671005 := rs (se 3 (by rfl) ⟨313313, by rfl⟩) R626627
theorem R262595 : Reach 262595 := rs (se 1 (by rfl) ⟨196946, by rfl⟩) R393893
theorem R295913 : Reach 295913 := rs (se 2 (by rfl) ⟨110967, by rfl⟩) R221935
theorem R69839 : Reach 69839 := rs (se 1 (by rfl) ⟨52379, by rfl⟩) R104759
theorem R70409 : Reach 70409 := rs (se 2 (by rfl) ⟨26403, by rfl⟩) R52807
theorem R170039 : Reach 170039 := rs (se 1 (by rfl) ⟨127529, by rfl⟩) R255059
theorem R71887 : Reach 71887 := rs (se 1 (by rfl) ⟨53915, by rfl⟩) R107831
theorem R469111 : Reach 469111 := rs (se 1 (by rfl) ⟨351833, by rfl⟩) R703667
theorem R175871 : Reach 175871 := rs (se 1 (by rfl) ⟨131903, by rfl⟩) R263807
theorem R45215 : Reach 45215 := rs (se 1 (by rfl) ⟨33911, by rfl⟩) R67823
theorem R113663 : Reach 113663 := rs (se 1 (by rfl) ⟨85247, by rfl⟩) R170495
theorem R220699 : Reach 220699 := rs (se 1 (by rfl) ⟨165524, by rfl⟩) R331049
theorem R92231 : Reach 92231 := rs (se 1 (by rfl) ⟨69173, by rfl⟩) R138347
theorem R879173 : Reach 879173 := rs (se 4 (by rfl) ⟨82422, by rfl⟩) R164845
theorem R27519 : Reach 27519 := rs (se 1 (by rfl) ⟨20639, by rfl⟩) R41279
theorem R61049 : Reach 61049 := rs (se 2 (by rfl) ⟨22893, by rfl⟩) R45787
theorem R28415 : Reach 28415 := rs (se 1 (by rfl) ⟨21311, by rfl⟩) R42623
theorem R28831 : Reach 28831 := rs (se 1 (by rfl) ⟨21623, by rfl⟩) R43247
theorem R31423 : Reach 31423 := rs (se 1 (by rfl) ⟨23567, by rfl⟩) R47135
theorem R97415 : Reach 97415 := rs (se 1 (by rfl) ⟨73061, by rfl⟩) R146123
theorem R97847 : Reach 97847 := rs (se 1 (by rfl) ⟨73385, by rfl⟩) R146771
theorem R1114003 : Reach 1114003 := rs (se 1 (by rfl) ⟨835502, by rfl⟩) R1671005
theorem R197275 : Reach 197275 := rs (se 1 (by rfl) ⟨147956, by rfl⟩) R295913
theorem R625481 : Reach 625481 := rs (se 2 (by rfl) ⟨234555, by rfl⟩) R469111
theorem R40699 : Reach 40699 := rs (se 1 (by rfl) ⟨30524, by rfl⟩) R61049
theorem R41897 : Reach 41897 := rs (se 2 (by rfl) ⟨15711, by rfl⟩) R31423
theorem R75775 : Reach 75775 := rs (se 1 (by rfl) ⟨56831, by rfl⟩) R113663
theorem R5941349 : Reach 5941349 := rs (se 4 (by rfl) ⟨557001, by rfl⟩) R1114003
theorem R175063 : Reach 175063 := rs (se 1 (by rfl) ⟨131297, by rfl⟩) R262595
theorem R46559 : Reach 46559 := rs (se 1 (by rfl) ⟨34919, by rfl⟩) R69839
theorem R46939 : Reach 46939 := rs (se 1 (by rfl) ⟨35204, by rfl⟩) R70409
theorem R113359 : Reach 113359 := rs (se 1 (by rfl) ⟨85019, by rfl⟩) R170039
theorem R117247 : Reach 117247 := rs (se 1 (by rfl) ⟨87935, by rfl⟩) R175871
theorem R61487 : Reach 61487 := rs (se 1 (by rfl) ⟨46115, by rfl⟩) R92231
theorem R586115 : Reach 586115 := rs (se 1 (by rfl) ⟨439586, by rfl⟩) R879173
theorem R30143 : Reach 30143 := rs (se 1 (by rfl) ⟨22607, by rfl⟩) R45215
theorem R95849 : Reach 95849 := rs (se 2 (by rfl) ⟨35943, by rfl⟩) R71887
theorem R294265 : Reach 294265 := rs (se 2 (by rfl) ⟨110349, by rfl⟩) R220699
theorem R64943 : Reach 64943 := rs (se 1 (by rfl) ⟨48707, by rfl⟩) R97415
theorem R65231 : Reach 65231 := rs (se 1 (by rfl) ⟨48923, by rfl⟩) R97847
theorem R263033 : Reach 263033 := rs (se 2 (by rfl) ⟨98637, by rfl⟩) R197275
theorem R101033 : Reach 101033 := rs (se 2 (by rfl) ⟨37887, by rfl⟩) R75775
theorem R233417 : Reach 233417 := rs (se 2 (by rfl) ⟨87531, by rfl⟩) R175063
theorem R40991 : Reach 40991 := rs (se 1 (by rfl) ⟨30743, by rfl⟩) R61487
theorem R43295 : Reach 43295 := rs (se 1 (by rfl) ⟨32471, by rfl⟩) R64943
theorem R43487 : Reach 43487 := rs (se 1 (by rfl) ⟨32615, by rfl⟩) R65231
theorem R151145 : Reach 151145 := rs (se 2 (by rfl) ⟨56679, by rfl⟩) R113359
theorem R54265 : Reach 54265 := rs (se 2 (by rfl) ⟨20349, by rfl⟩) R40699
theorem R416987 : Reach 416987 := rs (se 1 (by rfl) ⟨312740, by rfl⟩) R625481
theorem R156329 : Reach 156329 := rs (se 2 (by rfl) ⟨58623, by rfl⟩) R117247
theorem R27931 : Reach 27931 := rs (se 1 (by rfl) ⟨20948, by rfl⟩) R41897
theorem R3960899 : Reach 3960899 := rs (se 1 (by rfl) ⟨2970674, by rfl⟩) R5941349
theorem R62585 : Reach 62585 := rs (se 2 (by rfl) ⟨23469, by rfl⟩) R46939
theorem R390743 : Reach 390743 := rs (se 1 (by rfl) ⟨293057, by rfl⟩) R586115
theorem R31039 : Reach 31039 := rs (se 1 (by rfl) ⟨23279, by rfl⟩) R46559
theorem R63899 : Reach 63899 := rs (se 1 (by rfl) ⟨47924, by rfl⟩) R95849
theorem R392353 : Reach 392353 := rs (se 2 (by rfl) ⟨147132, by rfl⟩) R294265
theorem R67355 : Reach 67355 := rs (se 1 (by rfl) ⟨50516, by rfl⟩) R101033
theorem R100763 : Reach 100763 := rs (se 1 (by rfl) ⟨75572, by rfl⟩) R151145
theorem R104219 : Reach 104219 := rs (se 1 (by rfl) ⟨78164, by rfl⟩) R156329
theorem R72353 : Reach 72353 := rs (se 2 (by rfl) ⟨27132, by rfl⟩) R54265
theorem R41723 : Reach 41723 := rs (se 1 (by rfl) ⟨31292, by rfl⟩) R62585
theorem R42599 : Reach 42599 := rs (se 1 (by rfl) ⟨31949, by rfl⟩) R63899
theorem R175355 : Reach 175355 := rs (se 1 (by rfl) ⟨131516, by rfl⟩) R263033
theorem R277991 : Reach 277991 := rs (se 1 (by rfl) ⟨208493, by rfl⟩) R416987
theorem R2640599 : Reach 2640599 := rs (se 1 (by rfl) ⟨1980449, by rfl⟩) R3960899
theorem R155611 : Reach 155611 := rs (se 1 (by rfl) ⟨116708, by rfl⟩) R233417
theorem R27327 : Reach 27327 := rs (se 1 (by rfl) ⟨20495, by rfl⟩) R40991
theorem R2092549 : Reach 2092549 := rs (se 4 (by rfl) ⟨196176, by rfl⟩) R392353
theorem R28863 : Reach 28863 := rs (se 1 (by rfl) ⟨21647, by rfl⟩) R43295
theorem R28991 : Reach 28991 := rs (se 1 (by rfl) ⟨21743, by rfl⟩) R43487
theorem R260495 : Reach 260495 := rs (se 1 (by rfl) ⟨195371, by rfl⟩) R390743
theorem R67175 : Reach 67175 := rs (se 1 (by rfl) ⟨50381, by rfl⟩) R100763
theorem R69479 : Reach 69479 := rs (se 1 (by rfl) ⟨52109, by rfl⟩) R104219
theorem R2790065 : Reach 2790065 := rs (se 2 (by rfl) ⟨1046274, by rfl⟩) R2092549
theorem R173663 : Reach 173663 := rs (se 1 (by rfl) ⟨130247, by rfl⟩) R260495
theorem R207481 : Reach 207481 := rs (se 2 (by rfl) ⟨77805, by rfl⟩) R155611
theorem R44903 : Reach 44903 := rs (se 1 (by rfl) ⟨33677, by rfl⟩) R67355
theorem R48235 : Reach 48235 := rs (se 1 (by rfl) ⟨36176, by rfl⟩) R72353
theorem R116903 : Reach 116903 := rs (se 1 (by rfl) ⟨87677, by rfl⟩) R175355
theorem R185327 : Reach 185327 := rs (se 1 (by rfl) ⟨138995, by rfl⟩) R277991
theorem R1760399 : Reach 1760399 := rs (se 1 (by rfl) ⟨1320299, by rfl⟩) R2640599
theorem R27815 : Reach 27815 := rs (se 1 (by rfl) ⟨20861, by rfl⟩) R41723
theorem R28399 : Reach 28399 := rs (se 1 (by rfl) ⟨21299, by rfl⟩) R42599
theorem R44783 : Reach 44783 := rs (se 1 (by rfl) ⟨33587, by rfl⟩) R67175
theorem R77935 : Reach 77935 := rs (se 1 (by rfl) ⟨58451, by rfl⟩) R116903
theorem R46319 : Reach 46319 := rs (se 1 (by rfl) ⟨34739, by rfl⟩) R69479
theorem R276641 : Reach 276641 := rs (se 2 (by rfl) ⟨103740, by rfl⟩) R207481
theorem R115775 : Reach 115775 := rs (se 1 (by rfl) ⟨86831, by rfl⟩) R173663
theorem R1860043 : Reach 1860043 := rs (se 1 (by rfl) ⟨1395032, by rfl⟩) R2790065
theorem R123551 : Reach 123551 := rs (se 1 (by rfl) ⟨92663, by rfl⟩) R185327
theorem R1173599 : Reach 1173599 := rs (se 1 (by rfl) ⟨880199, by rfl⟩) R1760399
theorem R29935 : Reach 29935 := rs (se 1 (by rfl) ⟨22451, by rfl⟩) R44903
theorem R64313 : Reach 64313 := rs (se 2 (by rfl) ⟨24117, by rfl⟩) R48235
theorem R103913 : Reach 103913 := rs (se 2 (by rfl) ⟨38967, by rfl⟩) R77935
theorem R42875 : Reach 42875 := rs (se 1 (by rfl) ⟨32156, by rfl⟩) R64313
theorem R77183 : Reach 77183 := rs (se 1 (by rfl) ⟨57887, by rfl⟩) R115775
theorem R82367 : Reach 82367 := rs (se 1 (by rfl) ⟨61775, by rfl⟩) R123551
theorem R184427 : Reach 184427 := rs (se 1 (by rfl) ⟨138320, by rfl⟩) R276641
theorem R2480057 : Reach 2480057 := rs (se 2 (by rfl) ⟨930021, by rfl⟩) R1860043
theorem R782399 : Reach 782399 := rs (se 1 (by rfl) ⟨586799, by rfl⟩) R1173599
theorem R29855 : Reach 29855 := rs (se 1 (by rfl) ⟨22391, by rfl⟩) R44783
theorem R30879 : Reach 30879 := rs (se 1 (by rfl) ⟨23159, by rfl⟩) R46319
theorem R69275 : Reach 69275 := rs (se 1 (by rfl) ⟨51956, by rfl⟩) R103913
theorem R1653371 : Reach 1653371 := rs (se 1 (by rfl) ⟨1240028, by rfl⟩) R2480057
theorem R51455 : Reach 51455 := rs (se 1 (by rfl) ⟨38591, by rfl⟩) R77183
theorem R54911 : Reach 54911 := rs (se 1 (by rfl) ⟨41183, by rfl⟩) R82367
theorem R122951 : Reach 122951 := rs (se 1 (by rfl) ⟨92213, by rfl⟩) R184427
theorem R28583 : Reach 28583 := rs (se 1 (by rfl) ⟨21437, by rfl⟩) R42875
theorem R521599 : Reach 521599 := rs (se 1 (by rfl) ⟨391199, by rfl⟩) R782399
theorem R34303 : Reach 34303 := rs (se 1 (by rfl) ⟨25727, by rfl⟩) R51455
theorem R36607 : Reach 36607 := rs (se 1 (by rfl) ⟨27455, by rfl⟩) R54911
theorem R695465 : Reach 695465 := rs (se 2 (by rfl) ⟨260799, by rfl⟩) R521599
theorem R46183 : Reach 46183 := rs (se 1 (by rfl) ⟨34637, by rfl⟩) R69275
theorem R81967 : Reach 81967 := rs (se 1 (by rfl) ⟨61475, by rfl⟩) R122951
theorem R1102247 : Reach 1102247 := rs (se 1 (by rfl) ⟨826685, by rfl⟩) R1653371
theorem R463643 : Reach 463643 := rs (se 1 (by rfl) ⟨347732, by rfl⟩) R695465
theorem R109289 : Reach 109289 := rs (se 2 (by rfl) ⟨40983, by rfl⟩) R81967
theorem R45737 : Reach 45737 := rs (se 2 (by rfl) ⟨17151, by rfl⟩) R34303
theorem R734831 : Reach 734831 := rs (se 1 (by rfl) ⟨551123, by rfl⟩) R1102247
theorem R48809 : Reach 48809 := rs (se 2 (by rfl) ⟨18303, by rfl⟩) R36607
theorem R61577 : Reach 61577 := rs (se 2 (by rfl) ⟨23091, by rfl⟩) R46183
theorem R72859 : Reach 72859 := rs (se 1 (by rfl) ⟨54644, by rfl⟩) R109289
theorem R41051 : Reach 41051 := rs (se 1 (by rfl) ⟨30788, by rfl⟩) R61577
theorem R309095 : Reach 309095 := rs (se 1 (by rfl) ⟨231821, by rfl⟩) R463643
theorem R30491 : Reach 30491 := rs (se 1 (by rfl) ⟨22868, by rfl⟩) R45737
theorem R489887 : Reach 489887 := rs (se 1 (by rfl) ⟨367415, by rfl⟩) R734831
theorem R32539 : Reach 32539 := rs (se 1 (by rfl) ⟨24404, by rfl⟩) R48809
theorem R206063 : Reach 206063 := rs (se 1 (by rfl) ⟨154547, by rfl⟩) R309095
theorem R43385 : Reach 43385 := rs (se 2 (by rfl) ⟨16269, by rfl⟩) R32539
theorem R27367 : Reach 27367 := rs (se 1 (by rfl) ⟨20525, by rfl⟩) R41051
theorem R97145 : Reach 97145 := rs (se 2 (by rfl) ⟨36429, by rfl⟩) R72859
theorem R326591 : Reach 326591 := rs (se 1 (by rfl) ⟨244943, by rfl⟩) R489887
theorem R137375 : Reach 137375 := rs (se 1 (by rfl) ⟨103031, by rfl⟩) R206063
theorem R217727 : Reach 217727 := rs (se 1 (by rfl) ⟨163295, by rfl⟩) R326591
theorem R28923 : Reach 28923 := rs (se 1 (by rfl) ⟨21692, by rfl⟩) R43385
theorem R64763 : Reach 64763 := rs (se 1 (by rfl) ⟨48572, by rfl⟩) R97145
theorem R43175 : Reach 43175 := rs (se 1 (by rfl) ⟨32381, by rfl⟩) R64763
theorem R145151 : Reach 145151 := rs (se 1 (by rfl) ⟨108863, by rfl⟩) R217727
theorem R91583 : Reach 91583 := rs (se 1 (by rfl) ⟨68687, by rfl⟩) R137375
theorem R61055 : Reach 61055 := rs (se 1 (by rfl) ⟨45791, by rfl⟩) R91583
theorem R28783 : Reach 28783 := rs (se 1 (by rfl) ⟨21587, by rfl⟩) R43175
theorem R96767 : Reach 96767 := rs (se 1 (by rfl) ⟨72575, by rfl⟩) R145151
theorem R40703 : Reach 40703 := rs (se 1 (by rfl) ⟨30527, by rfl⟩) R61055
theorem R64511 : Reach 64511 := rs (se 1 (by rfl) ⟨48383, by rfl⟩) R96767
theorem R43007 : Reach 43007 := rs (se 1 (by rfl) ⟨32255, by rfl⟩) R64511
theorem R27135 : Reach 27135 := rs (se 1 (by rfl) ⟨20351, by rfl⟩) R40703
theorem R28671 : Reach 28671 := rs (se 1 (by rfl) ⟨21503, by rfl⟩) R43007

theorem C0 (j : ℕ) (h1 : 13557 ≤ j) (h2 : j ≤ 14256) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R27115
  · exact R27117
  · exact R27119
  · exact R27121
  · exact R27123
  · exact R27125
  · exact R27127
  · exact R27129
  · exact R27131
  · exact R27133
  · exact R27135
  · exact R27137
  · exact R27139
  · exact R27141
  · exact R27143
  · exact R27145
  · exact R27147
  · exact R27149
  · exact R27151
  · exact R27153
  · exact R27155
  · exact R27157
  · exact R27159
  · exact R27161
  · exact R27163
  · exact R27165
  · exact R27167
  · exact R27169
  · exact R27171
  · exact R27173
  · exact R27175
  · exact R27177
  · exact R27179
  · exact R27181
  · exact R27183
  · exact R27185
  · exact R27187
  · exact R27189
  · exact R27191
  · exact R27193
  · exact R27195
  · exact R27197
  · exact R27199
  · exact R27201
  · exact R27203
  · exact R27205
  · exact R27207
  · exact R27209
  · exact R27211
  · exact R27213
  · exact R27215
  · exact R27217
  · exact R27219
  · exact R27221
  · exact R27223
  · exact R27225
  · exact R27227
  · exact R27229
  · exact R27231
  · exact R27233
  · exact R27235
  · exact R27237
  · exact R27239
  · exact R27241
  · exact R27243
  · exact R27245
  · exact R27247
  · exact R27249
  · exact R27251
  · exact R27253
  · exact R27255
  · exact R27257
  · exact R27259
  · exact R27261
  · exact R27263
  · exact R27265
  · exact R27267
  · exact R27269
  · exact R27271
  · exact R27273
  · exact R27275
  · exact R27277
  · exact R27279
  · exact R27281
  · exact R27283
  · exact R27285
  · exact R27287
  · exact R27289
  · exact R27291
  · exact R27293
  · exact R27295
  · exact R27297
  · exact R27299
  · exact R27301
  · exact R27303
  · exact R27305
  · exact R27307
  · exact R27309
  · exact R27311
  · exact R27313
  · exact R27315
  · exact R27317
  · exact R27319
  · exact R27321
  · exact R27323
  · exact R27325
  · exact R27327
  · exact R27329
  · exact R27331
  · exact R27333
  · exact R27335
  · exact R27337
  · exact R27339
  · exact R27341
  · exact R27343
  · exact R27345
  · exact R27347
  · exact R27349
  · exact R27351
  · exact R27353
  · exact R27355
  · exact R27357
  · exact R27359
  · exact R27361
  · exact R27363
  · exact R27365
  · exact R27367
  · exact R27369
  · exact R27371
  · exact R27373
  · exact R27375
  · exact R27377
  · exact R27379
  · exact R27381
  · exact R27383
  · exact R27385
  · exact R27387
  · exact R27389
  · exact R27391
  · exact R27393
  · exact R27395
  · exact R27397
  · exact R27399
  · exact R27401
  · exact R27403
  · exact R27405
  · exact R27407
  · exact R27409
  · exact R27411
  · exact R27413
  · exact R27415
  · exact R27417
  · exact R27419
  · exact R27421
  · exact R27423
  · exact R27425
  · exact R27427
  · exact R27429
  · exact R27431
  · exact R27433
  · exact R27435
  · exact R27437
  · exact R27439
  · exact R27441
  · exact R27443
  · exact R27445
  · exact R27447
  · exact R27449
  · exact R27451
  · exact R27453
  · exact R27455
  · exact R27457
  · exact R27459
  · exact R27461
  · exact R27463
  · exact R27465
  · exact R27467
  · exact R27469
  · exact R27471
  · exact R27473
  · exact R27475
  · exact R27477
  · exact R27479
  · exact R27481
  · exact R27483
  · exact R27485
  · exact R27487
  · exact R27489
  · exact R27491
  · exact R27493
  · exact R27495
  · exact R27497
  · exact R27499
  · exact R27501
  · exact R27503
  · exact R27505
  · exact R27507
  · exact R27509
  · exact R27511
  · exact R27513
  · exact R27515
  · exact R27517
  · exact R27519
  · exact R27521
  · exact R27523
  · exact R27525
  · exact R27527
  · exact R27529
  · exact R27531
  · exact R27533
  · exact R27535
  · exact R27537
  · exact R27539
  · exact R27541
  · exact R27543
  · exact R27545
  · exact R27547
  · exact R27549
  · exact R27551
  · exact R27553
  · exact R27555
  · exact R27557
  · exact R27559
  · exact R27561
  · exact R27563
  · exact R27565
  · exact R27567
  · exact R27569
  · exact R27571
  · exact R27573
  · exact R27575
  · exact R27577
  · exact R27579
  · exact R27581
  · exact R27583
  · exact R27585
  · exact R27587
  · exact R27589
  · exact R27591
  · exact R27593
  · exact R27595
  · exact R27597
  · exact R27599
  · exact R27601
  · exact R27603
  · exact R27605
  · exact R27607
  · exact R27609
  · exact R27611
  · exact R27613
  · exact R27615
  · exact R27617
  · exact R27619
  · exact R27621
  · exact R27623
  · exact R27625
  · exact R27627
  · exact R27629
  · exact R27631
  · exact R27633
  · exact R27635
  · exact R27637
  · exact R27639
  · exact R27641
  · exact R27643
  · exact R27645
  · exact R27647
  · exact R27649
  · exact R27651
  · exact R27653
  · exact R27655
  · exact R27657
  · exact R27659
  · exact R27661
  · exact R27663
  · exact R27665
  · exact R27667
  · exact R27669
  · exact R27671
  · exact R27673
  · exact R27675
  · exact R27677
  · exact R27679
  · exact R27681
  · exact R27683
  · exact R27685
  · exact R27687
  · exact R27689
  · exact R27691
  · exact R27693
  · exact R27695
  · exact R27697
  · exact R27699
  · exact R27701
  · exact R27703
  · exact R27705
  · exact R27707
  · exact R27709
  · exact R27711
  · exact R27713
  · exact R27715
  · exact R27717
  · exact R27719
  · exact R27721
  · exact R27723
  · exact R27725
  · exact R27727
  · exact R27729
  · exact R27731
  · exact R27733
  · exact R27735
  · exact R27737
  · exact R27739
  · exact R27741
  · exact R27743
  · exact R27745
  · exact R27747
  · exact R27749
  · exact R27751
  · exact R27753
  · exact R27755
  · exact R27757
  · exact R27759
  · exact R27761
  · exact R27763
  · exact R27765
  · exact R27767
  · exact R27769
  · exact R27771
  · exact R27773
  · exact R27775
  · exact R27777
  · exact R27779
  · exact R27781
  · exact R27783
  · exact R27785
  · exact R27787
  · exact R27789
  · exact R27791
  · exact R27793
  · exact R27795
  · exact R27797
  · exact R27799
  · exact R27801
  · exact R27803
  · exact R27805
  · exact R27807
  · exact R27809
  · exact R27811
  · exact R27813
  · exact R27815
  · exact R27817
  · exact R27819
  · exact R27821
  · exact R27823
  · exact R27825
  · exact R27827
  · exact R27829
  · exact R27831
  · exact R27833
  · exact R27835
  · exact R27837
  · exact R27839
  · exact R27841
  · exact R27843
  · exact R27845
  · exact R27847
  · exact R27849
  · exact R27851
  · exact R27853
  · exact R27855
  · exact R27857
  · exact R27859
  · exact R27861
  · exact R27863
  · exact R27865
  · exact R27867
  · exact R27869
  · exact R27871
  · exact R27873
  · exact R27875
  · exact R27877
  · exact R27879
  · exact R27881
  · exact R27883
  · exact R27885
  · exact R27887
  · exact R27889
  · exact R27891
  · exact R27893
  · exact R27895
  · exact R27897
  · exact R27899
  · exact R27901
  · exact R27903
  · exact R27905
  · exact R27907
  · exact R27909
  · exact R27911
  · exact R27913
  · exact R27915
  · exact R27917
  · exact R27919
  · exact R27921
  · exact R27923
  · exact R27925
  · exact R27927
  · exact R27929
  · exact R27931
  · exact R27933
  · exact R27935
  · exact R27937
  · exact R27939
  · exact R27941
  · exact R27943
  · exact R27945
  · exact R27947
  · exact R27949
  · exact R27951
  · exact R27953
  · exact R27955
  · exact R27957
  · exact R27959
  · exact R27961
  · exact R27963
  · exact R27965
  · exact R27967
  · exact R27969
  · exact R27971
  · exact R27973
  · exact R27975
  · exact R27977
  · exact R27979
  · exact R27981
  · exact R27983
  · exact R27985
  · exact R27987
  · exact R27989
  · exact R27991
  · exact R27993
  · exact R27995
  · exact R27997
  · exact R27999
  · exact R28001
  · exact R28003
  · exact R28005
  · exact R28007
  · exact R28009
  · exact R28011
  · exact R28013
  · exact R28015
  · exact R28017
  · exact R28019
  · exact R28021
  · exact R28023
  · exact R28025
  · exact R28027
  · exact R28029
  · exact R28031
  · exact R28033
  · exact R28035
  · exact R28037
  · exact R28039
  · exact R28041
  · exact R28043
  · exact R28045
  · exact R28047
  · exact R28049
  · exact R28051
  · exact R28053
  · exact R28055
  · exact R28057
  · exact R28059
  · exact R28061
  · exact R28063
  · exact R28065
  · exact R28067
  · exact R28069
  · exact R28071
  · exact R28073
  · exact R28075
  · exact R28077
  · exact R28079
  · exact R28081
  · exact R28083
  · exact R28085
  · exact R28087
  · exact R28089
  · exact R28091
  · exact R28093
  · exact R28095
  · exact R28097
  · exact R28099
  · exact R28101
  · exact R28103
  · exact R28105
  · exact R28107
  · exact R28109
  · exact R28111
  · exact R28113
  · exact R28115
  · exact R28117
  · exact R28119
  · exact R28121
  · exact R28123
  · exact R28125
  · exact R28127
  · exact R28129
  · exact R28131
  · exact R28133
  · exact R28135
  · exact R28137
  · exact R28139
  · exact R28141
  · exact R28143
  · exact R28145
  · exact R28147
  · exact R28149
  · exact R28151
  · exact R28153
  · exact R28155
  · exact R28157
  · exact R28159
  · exact R28161
  · exact R28163
  · exact R28165
  · exact R28167
  · exact R28169
  · exact R28171
  · exact R28173
  · exact R28175
  · exact R28177
  · exact R28179
  · exact R28181
  · exact R28183
  · exact R28185
  · exact R28187
  · exact R28189
  · exact R28191
  · exact R28193
  · exact R28195
  · exact R28197
  · exact R28199
  · exact R28201
  · exact R28203
  · exact R28205
  · exact R28207
  · exact R28209
  · exact R28211
  · exact R28213
  · exact R28215
  · exact R28217
  · exact R28219
  · exact R28221
  · exact R28223
  · exact R28225
  · exact R28227
  · exact R28229
  · exact R28231
  · exact R28233
  · exact R28235
  · exact R28237
  · exact R28239
  · exact R28241
  · exact R28243
  · exact R28245
  · exact R28247
  · exact R28249
  · exact R28251
  · exact R28253
  · exact R28255
  · exact R28257
  · exact R28259
  · exact R28261
  · exact R28263
  · exact R28265
  · exact R28267
  · exact R28269
  · exact R28271
  · exact R28273
  · exact R28275
  · exact R28277
  · exact R28279
  · exact R28281
  · exact R28283
  · exact R28285
  · exact R28287
  · exact R28289
  · exact R28291
  · exact R28293
  · exact R28295
  · exact R28297
  · exact R28299
  · exact R28301
  · exact R28303
  · exact R28305
  · exact R28307
  · exact R28309
  · exact R28311
  · exact R28313
  · exact R28315
  · exact R28317
  · exact R28319
  · exact R28321
  · exact R28323
  · exact R28325
  · exact R28327
  · exact R28329
  · exact R28331
  · exact R28333
  · exact R28335
  · exact R28337
  · exact R28339
  · exact R28341
  · exact R28343
  · exact R28345
  · exact R28347
  · exact R28349
  · exact R28351
  · exact R28353
  · exact R28355
  · exact R28357
  · exact R28359
  · exact R28361
  · exact R28363
  · exact R28365
  · exact R28367
  · exact R28369
  · exact R28371
  · exact R28373
  · exact R28375
  · exact R28377
  · exact R28379
  · exact R28381
  · exact R28383
  · exact R28385
  · exact R28387
  · exact R28389
  · exact R28391
  · exact R28393
  · exact R28395
  · exact R28397
  · exact R28399
  · exact R28401
  · exact R28403
  · exact R28405
  · exact R28407
  · exact R28409
  · exact R28411
  · exact R28413
  · exact R28415
  · exact R28417
  · exact R28419
  · exact R28421
  · exact R28423
  · exact R28425
  · exact R28427
  · exact R28429
  · exact R28431
  · exact R28433
  · exact R28435
  · exact R28437
  · exact R28439
  · exact R28441
  · exact R28443
  · exact R28445
  · exact R28447
  · exact R28449
  · exact R28451
  · exact R28453
  · exact R28455
  · exact R28457
  · exact R28459
  · exact R28461
  · exact R28463
  · exact R28465
  · exact R28467
  · exact R28469
  · exact R28471
  · exact R28473
  · exact R28475
  · exact R28477
  · exact R28479
  · exact R28481
  · exact R28483
  · exact R28485
  · exact R28487
  · exact R28489
  · exact R28491
  · exact R28493
  · exact R28495
  · exact R28497
  · exact R28499
  · exact R28501
  · exact R28503
  · exact R28505
  · exact R28507
  · exact R28509
  · exact R28511
  · exact R28513

theorem C1 (j : ℕ) (h1 : 14257 ≤ j) (h2 : j ≤ 14956) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R28515
  · exact R28517
  · exact R28519
  · exact R28521
  · exact R28523
  · exact R28525
  · exact R28527
  · exact R28529
  · exact R28531
  · exact R28533
  · exact R28535
  · exact R28537
  · exact R28539
  · exact R28541
  · exact R28543
  · exact R28545
  · exact R28547
  · exact R28549
  · exact R28551
  · exact R28553
  · exact R28555
  · exact R28557
  · exact R28559
  · exact R28561
  · exact R28563
  · exact R28565
  · exact R28567
  · exact R28569
  · exact R28571
  · exact R28573
  · exact R28575
  · exact R28577
  · exact R28579
  · exact R28581
  · exact R28583
  · exact R28585
  · exact R28587
  · exact R28589
  · exact R28591
  · exact R28593
  · exact R28595
  · exact R28597
  · exact R28599
  · exact R28601
  · exact R28603
  · exact R28605
  · exact R28607
  · exact R28609
  · exact R28611
  · exact R28613
  · exact R28615
  · exact R28617
  · exact R28619
  · exact R28621
  · exact R28623
  · exact R28625
  · exact R28627
  · exact R28629
  · exact R28631
  · exact R28633
  · exact R28635
  · exact R28637
  · exact R28639
  · exact R28641
  · exact R28643
  · exact R28645
  · exact R28647
  · exact R28649
  · exact R28651
  · exact R28653
  · exact R28655
  · exact R28657
  · exact R28659
  · exact R28661
  · exact R28663
  · exact R28665
  · exact R28667
  · exact R28669
  · exact R28671
  · exact R28673
  · exact R28675
  · exact R28677
  · exact R28679
  · exact R28681
  · exact R28683
  · exact R28685
  · exact R28687
  · exact R28689
  · exact R28691
  · exact R28693
  · exact R28695
  · exact R28697
  · exact R28699
  · exact R28701
  · exact R28703
  · exact R28705
  · exact R28707
  · exact R28709
  · exact R28711
  · exact R28713
  · exact R28715
  · exact R28717
  · exact R28719
  · exact R28721
  · exact R28723
  · exact R28725
  · exact R28727
  · exact R28729
  · exact R28731
  · exact R28733
  · exact R28735
  · exact R28737
  · exact R28739
  · exact R28741
  · exact R28743
  · exact R28745
  · exact R28747
  · exact R28749
  · exact R28751
  · exact R28753
  · exact R28755
  · exact R28757
  · exact R28759
  · exact R28761
  · exact R28763
  · exact R28765
  · exact R28767
  · exact R28769
  · exact R28771
  · exact R28773
  · exact R28775
  · exact R28777
  · exact R28779
  · exact R28781
  · exact R28783
  · exact R28785
  · exact R28787
  · exact R28789
  · exact R28791
  · exact R28793
  · exact R28795
  · exact R28797
  · exact R28799
  · exact R28801
  · exact R28803
  · exact R28805
  · exact R28807
  · exact R28809
  · exact R28811
  · exact R28813
  · exact R28815
  · exact R28817
  · exact R28819
  · exact R28821
  · exact R28823
  · exact R28825
  · exact R28827
  · exact R28829
  · exact R28831
  · exact R28833
  · exact R28835
  · exact R28837
  · exact R28839
  · exact R28841
  · exact R28843
  · exact R28845
  · exact R28847
  · exact R28849
  · exact R28851
  · exact R28853
  · exact R28855
  · exact R28857
  · exact R28859
  · exact R28861
  · exact R28863
  · exact R28865
  · exact R28867
  · exact R28869
  · exact R28871
  · exact R28873
  · exact R28875
  · exact R28877
  · exact R28879
  · exact R28881
  · exact R28883
  · exact R28885
  · exact R28887
  · exact R28889
  · exact R28891
  · exact R28893
  · exact R28895
  · exact R28897
  · exact R28899
  · exact R28901
  · exact R28903
  · exact R28905
  · exact R28907
  · exact R28909
  · exact R28911
  · exact R28913
  · exact R28915
  · exact R28917
  · exact R28919
  · exact R28921
  · exact R28923
  · exact R28925
  · exact R28927
  · exact R28929
  · exact R28931
  · exact R28933
  · exact R28935
  · exact R28937
  · exact R28939
  · exact R28941
  · exact R28943
  · exact R28945
  · exact R28947
  · exact R28949
  · exact R28951
  · exact R28953
  · exact R28955
  · exact R28957
  · exact R28959
  · exact R28961
  · exact R28963
  · exact R28965
  · exact R28967
  · exact R28969
  · exact R28971
  · exact R28973
  · exact R28975
  · exact R28977
  · exact R28979
  · exact R28981
  · exact R28983
  · exact R28985
  · exact R28987
  · exact R28989
  · exact R28991
  · exact R28993
  · exact R28995
  · exact R28997
  · exact R28999
  · exact R29001
  · exact R29003
  · exact R29005
  · exact R29007
  · exact R29009
  · exact R29011
  · exact R29013
  · exact R29015
  · exact R29017
  · exact R29019
  · exact R29021
  · exact R29023
  · exact R29025
  · exact R29027
  · exact R29029
  · exact R29031
  · exact R29033
  · exact R29035
  · exact R29037
  · exact R29039
  · exact R29041
  · exact R29043
  · exact R29045
  · exact R29047
  · exact R29049
  · exact R29051
  · exact R29053
  · exact R29055
  · exact R29057
  · exact R29059
  · exact R29061
  · exact R29063
  · exact R29065
  · exact R29067
  · exact R29069
  · exact R29071
  · exact R29073
  · exact R29075
  · exact R29077
  · exact R29079
  · exact R29081
  · exact R29083
  · exact R29085
  · exact R29087
  · exact R29089
  · exact R29091
  · exact R29093
  · exact R29095
  · exact R29097
  · exact R29099
  · exact R29101
  · exact R29103
  · exact R29105
  · exact R29107
  · exact R29109
  · exact R29111
  · exact R29113
  · exact R29115
  · exact R29117
  · exact R29119
  · exact R29121
  · exact R29123
  · exact R29125
  · exact R29127
  · exact R29129
  · exact R29131
  · exact R29133
  · exact R29135
  · exact R29137
  · exact R29139
  · exact R29141
  · exact R29143
  · exact R29145
  · exact R29147
  · exact R29149
  · exact R29151
  · exact R29153
  · exact R29155
  · exact R29157
  · exact R29159
  · exact R29161
  · exact R29163
  · exact R29165
  · exact R29167
  · exact R29169
  · exact R29171
  · exact R29173
  · exact R29175
  · exact R29177
  · exact R29179
  · exact R29181
  · exact R29183
  · exact R29185
  · exact R29187
  · exact R29189
  · exact R29191
  · exact R29193
  · exact R29195
  · exact R29197
  · exact R29199
  · exact R29201
  · exact R29203
  · exact R29205
  · exact R29207
  · exact R29209
  · exact R29211
  · exact R29213
  · exact R29215
  · exact R29217
  · exact R29219
  · exact R29221
  · exact R29223
  · exact R29225
  · exact R29227
  · exact R29229
  · exact R29231
  · exact R29233
  · exact R29235
  · exact R29237
  · exact R29239
  · exact R29241
  · exact R29243
  · exact R29245
  · exact R29247
  · exact R29249
  · exact R29251
  · exact R29253
  · exact R29255
  · exact R29257
  · exact R29259
  · exact R29261
  · exact R29263
  · exact R29265
  · exact R29267
  · exact R29269
  · exact R29271
  · exact R29273
  · exact R29275
  · exact R29277
  · exact R29279
  · exact R29281
  · exact R29283
  · exact R29285
  · exact R29287
  · exact R29289
  · exact R29291
  · exact R29293
  · exact R29295
  · exact R29297
  · exact R29299
  · exact R29301
  · exact R29303
  · exact R29305
  · exact R29307
  · exact R29309
  · exact R29311
  · exact R29313
  · exact R29315
  · exact R29317
  · exact R29319
  · exact R29321
  · exact R29323
  · exact R29325
  · exact R29327
  · exact R29329
  · exact R29331
  · exact R29333
  · exact R29335
  · exact R29337
  · exact R29339
  · exact R29341
  · exact R29343
  · exact R29345
  · exact R29347
  · exact R29349
  · exact R29351
  · exact R29353
  · exact R29355
  · exact R29357
  · exact R29359
  · exact R29361
  · exact R29363
  · exact R29365
  · exact R29367
  · exact R29369
  · exact R29371
  · exact R29373
  · exact R29375
  · exact R29377
  · exact R29379
  · exact R29381
  · exact R29383
  · exact R29385
  · exact R29387
  · exact R29389
  · exact R29391
  · exact R29393
  · exact R29395
  · exact R29397
  · exact R29399
  · exact R29401
  · exact R29403
  · exact R29405
  · exact R29407
  · exact R29409
  · exact R29411
  · exact R29413
  · exact R29415
  · exact R29417
  · exact R29419
  · exact R29421
  · exact R29423
  · exact R29425
  · exact R29427
  · exact R29429
  · exact R29431
  · exact R29433
  · exact R29435
  · exact R29437
  · exact R29439
  · exact R29441
  · exact R29443
  · exact R29445
  · exact R29447
  · exact R29449
  · exact R29451
  · exact R29453
  · exact R29455
  · exact R29457
  · exact R29459
  · exact R29461
  · exact R29463
  · exact R29465
  · exact R29467
  · exact R29469
  · exact R29471
  · exact R29473
  · exact R29475
  · exact R29477
  · exact R29479
  · exact R29481
  · exact R29483
  · exact R29485
  · exact R29487
  · exact R29489
  · exact R29491
  · exact R29493
  · exact R29495
  · exact R29497
  · exact R29499
  · exact R29501
  · exact R29503
  · exact R29505
  · exact R29507
  · exact R29509
  · exact R29511
  · exact R29513
  · exact R29515
  · exact R29517
  · exact R29519
  · exact R29521
  · exact R29523
  · exact R29525
  · exact R29527
  · exact R29529
  · exact R29531
  · exact R29533
  · exact R29535
  · exact R29537
  · exact R29539
  · exact R29541
  · exact R29543
  · exact R29545
  · exact R29547
  · exact R29549
  · exact R29551
  · exact R29553
  · exact R29555
  · exact R29557
  · exact R29559
  · exact R29561
  · exact R29563
  · exact R29565
  · exact R29567
  · exact R29569
  · exact R29571
  · exact R29573
  · exact R29575
  · exact R29577
  · exact R29579
  · exact R29581
  · exact R29583
  · exact R29585
  · exact R29587
  · exact R29589
  · exact R29591
  · exact R29593
  · exact R29595
  · exact R29597
  · exact R29599
  · exact R29601
  · exact R29603
  · exact R29605
  · exact R29607
  · exact R29609
  · exact R29611
  · exact R29613
  · exact R29615
  · exact R29617
  · exact R29619
  · exact R29621
  · exact R29623
  · exact R29625
  · exact R29627
  · exact R29629
  · exact R29631
  · exact R29633
  · exact R29635
  · exact R29637
  · exact R29639
  · exact R29641
  · exact R29643
  · exact R29645
  · exact R29647
  · exact R29649
  · exact R29651
  · exact R29653
  · exact R29655
  · exact R29657
  · exact R29659
  · exact R29661
  · exact R29663
  · exact R29665
  · exact R29667
  · exact R29669
  · exact R29671
  · exact R29673
  · exact R29675
  · exact R29677
  · exact R29679
  · exact R29681
  · exact R29683
  · exact R29685
  · exact R29687
  · exact R29689
  · exact R29691
  · exact R29693
  · exact R29695
  · exact R29697
  · exact R29699
  · exact R29701
  · exact R29703
  · exact R29705
  · exact R29707
  · exact R29709
  · exact R29711
  · exact R29713
  · exact R29715
  · exact R29717
  · exact R29719
  · exact R29721
  · exact R29723
  · exact R29725
  · exact R29727
  · exact R29729
  · exact R29731
  · exact R29733
  · exact R29735
  · exact R29737
  · exact R29739
  · exact R29741
  · exact R29743
  · exact R29745
  · exact R29747
  · exact R29749
  · exact R29751
  · exact R29753
  · exact R29755
  · exact R29757
  · exact R29759
  · exact R29761
  · exact R29763
  · exact R29765
  · exact R29767
  · exact R29769
  · exact R29771
  · exact R29773
  · exact R29775
  · exact R29777
  · exact R29779
  · exact R29781
  · exact R29783
  · exact R29785
  · exact R29787
  · exact R29789
  · exact R29791
  · exact R29793
  · exact R29795
  · exact R29797
  · exact R29799
  · exact R29801
  · exact R29803
  · exact R29805
  · exact R29807
  · exact R29809
  · exact R29811
  · exact R29813
  · exact R29815
  · exact R29817
  · exact R29819
  · exact R29821
  · exact R29823
  · exact R29825
  · exact R29827
  · exact R29829
  · exact R29831
  · exact R29833
  · exact R29835
  · exact R29837
  · exact R29839
  · exact R29841
  · exact R29843
  · exact R29845
  · exact R29847
  · exact R29849
  · exact R29851
  · exact R29853
  · exact R29855
  · exact R29857
  · exact R29859
  · exact R29861
  · exact R29863
  · exact R29865
  · exact R29867
  · exact R29869
  · exact R29871
  · exact R29873
  · exact R29875
  · exact R29877
  · exact R29879
  · exact R29881
  · exact R29883
  · exact R29885
  · exact R29887
  · exact R29889
  · exact R29891
  · exact R29893
  · exact R29895
  · exact R29897
  · exact R29899
  · exact R29901
  · exact R29903
  · exact R29905
  · exact R29907
  · exact R29909
  · exact R29911
  · exact R29913

theorem C2 (j : ℕ) (h1 : 14957 ≤ j) (h2 : j ≤ 15556) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R29915
  · exact R29917
  · exact R29919
  · exact R29921
  · exact R29923
  · exact R29925
  · exact R29927
  · exact R29929
  · exact R29931
  · exact R29933
  · exact R29935
  · exact R29937
  · exact R29939
  · exact R29941
  · exact R29943
  · exact R29945
  · exact R29947
  · exact R29949
  · exact R29951
  · exact R29953
  · exact R29955
  · exact R29957
  · exact R29959
  · exact R29961
  · exact R29963
  · exact R29965
  · exact R29967
  · exact R29969
  · exact R29971
  · exact R29973
  · exact R29975
  · exact R29977
  · exact R29979
  · exact R29981
  · exact R29983
  · exact R29985
  · exact R29987
  · exact R29989
  · exact R29991
  · exact R29993
  · exact R29995
  · exact R29997
  · exact R29999
  · exact R30001
  · exact R30003
  · exact R30005
  · exact R30007
  · exact R30009
  · exact R30011
  · exact R30013
  · exact R30015
  · exact R30017
  · exact R30019
  · exact R30021
  · exact R30023
  · exact R30025
  · exact R30027
  · exact R30029
  · exact R30031
  · exact R30033
  · exact R30035
  · exact R30037
  · exact R30039
  · exact R30041
  · exact R30043
  · exact R30045
  · exact R30047
  · exact R30049
  · exact R30051
  · exact R30053
  · exact R30055
  · exact R30057
  · exact R30059
  · exact R30061
  · exact R30063
  · exact R30065
  · exact R30067
  · exact R30069
  · exact R30071
  · exact R30073
  · exact R30075
  · exact R30077
  · exact R30079
  · exact R30081
  · exact R30083
  · exact R30085
  · exact R30087
  · exact R30089
  · exact R30091
  · exact R30093
  · exact R30095
  · exact R30097
  · exact R30099
  · exact R30101
  · exact R30103
  · exact R30105
  · exact R30107
  · exact R30109
  · exact R30111
  · exact R30113
  · exact R30115
  · exact R30117
  · exact R30119
  · exact R30121
  · exact R30123
  · exact R30125
  · exact R30127
  · exact R30129
  · exact R30131
  · exact R30133
  · exact R30135
  · exact R30137
  · exact R30139
  · exact R30141
  · exact R30143
  · exact R30145
  · exact R30147
  · exact R30149
  · exact R30151
  · exact R30153
  · exact R30155
  · exact R30157
  · exact R30159
  · exact R30161
  · exact R30163
  · exact R30165
  · exact R30167
  · exact R30169
  · exact R30171
  · exact R30173
  · exact R30175
  · exact R30177
  · exact R30179
  · exact R30181
  · exact R30183
  · exact R30185
  · exact R30187
  · exact R30189
  · exact R30191
  · exact R30193
  · exact R30195
  · exact R30197
  · exact R30199
  · exact R30201
  · exact R30203
  · exact R30205
  · exact R30207
  · exact R30209
  · exact R30211
  · exact R30213
  · exact R30215
  · exact R30217
  · exact R30219
  · exact R30221
  · exact R30223
  · exact R30225
  · exact R30227
  · exact R30229
  · exact R30231
  · exact R30233
  · exact R30235
  · exact R30237
  · exact R30239
  · exact R30241
  · exact R30243
  · exact R30245
  · exact R30247
  · exact R30249
  · exact R30251
  · exact R30253
  · exact R30255
  · exact R30257
  · exact R30259
  · exact R30261
  · exact R30263
  · exact R30265
  · exact R30267
  · exact R30269
  · exact R30271
  · exact R30273
  · exact R30275
  · exact R30277
  · exact R30279
  · exact R30281
  · exact R30283
  · exact R30285
  · exact R30287
  · exact R30289
  · exact R30291
  · exact R30293
  · exact R30295
  · exact R30297
  · exact R30299
  · exact R30301
  · exact R30303
  · exact R30305
  · exact R30307
  · exact R30309
  · exact R30311
  · exact R30313
  · exact R30315
  · exact R30317
  · exact R30319
  · exact R30321
  · exact R30323
  · exact R30325
  · exact R30327
  · exact R30329
  · exact R30331
  · exact R30333
  · exact R30335
  · exact R30337
  · exact R30339
  · exact R30341
  · exact R30343
  · exact R30345
  · exact R30347
  · exact R30349
  · exact R30351
  · exact R30353
  · exact R30355
  · exact R30357
  · exact R30359
  · exact R30361
  · exact R30363
  · exact R30365
  · exact R30367
  · exact R30369
  · exact R30371
  · exact R30373
  · exact R30375
  · exact R30377
  · exact R30379
  · exact R30381
  · exact R30383
  · exact R30385
  · exact R30387
  · exact R30389
  · exact R30391
  · exact R30393
  · exact R30395
  · exact R30397
  · exact R30399
  · exact R30401
  · exact R30403
  · exact R30405
  · exact R30407
  · exact R30409
  · exact R30411
  · exact R30413
  · exact R30415
  · exact R30417
  · exact R30419
  · exact R30421
  · exact R30423
  · exact R30425
  · exact R30427
  · exact R30429
  · exact R30431
  · exact R30433
  · exact R30435
  · exact R30437
  · exact R30439
  · exact R30441
  · exact R30443
  · exact R30445
  · exact R30447
  · exact R30449
  · exact R30451
  · exact R30453
  · exact R30455
  · exact R30457
  · exact R30459
  · exact R30461
  · exact R30463
  · exact R30465
  · exact R30467
  · exact R30469
  · exact R30471
  · exact R30473
  · exact R30475
  · exact R30477
  · exact R30479
  · exact R30481
  · exact R30483
  · exact R30485
  · exact R30487
  · exact R30489
  · exact R30491
  · exact R30493
  · exact R30495
  · exact R30497
  · exact R30499
  · exact R30501
  · exact R30503
  · exact R30505
  · exact R30507
  · exact R30509
  · exact R30511
  · exact R30513
  · exact R30515
  · exact R30517
  · exact R30519
  · exact R30521
  · exact R30523
  · exact R30525
  · exact R30527
  · exact R30529
  · exact R30531
  · exact R30533
  · exact R30535
  · exact R30537
  · exact R30539
  · exact R30541
  · exact R30543
  · exact R30545
  · exact R30547
  · exact R30549
  · exact R30551
  · exact R30553
  · exact R30555
  · exact R30557
  · exact R30559
  · exact R30561
  · exact R30563
  · exact R30565
  · exact R30567
  · exact R30569
  · exact R30571
  · exact R30573
  · exact R30575
  · exact R30577
  · exact R30579
  · exact R30581
  · exact R30583
  · exact R30585
  · exact R30587
  · exact R30589
  · exact R30591
  · exact R30593
  · exact R30595
  · exact R30597
  · exact R30599
  · exact R30601
  · exact R30603
  · exact R30605
  · exact R30607
  · exact R30609
  · exact R30611
  · exact R30613
  · exact R30615
  · exact R30617
  · exact R30619
  · exact R30621
  · exact R30623
  · exact R30625
  · exact R30627
  · exact R30629
  · exact R30631
  · exact R30633
  · exact R30635
  · exact R30637
  · exact R30639
  · exact R30641
  · exact R30643
  · exact R30645
  · exact R30647
  · exact R30649
  · exact R30651
  · exact R30653
  · exact R30655
  · exact R30657
  · exact R30659
  · exact R30661
  · exact R30663
  · exact R30665
  · exact R30667
  · exact R30669
  · exact R30671
  · exact R30673
  · exact R30675
  · exact R30677
  · exact R30679
  · exact R30681
  · exact R30683
  · exact R30685
  · exact R30687
  · exact R30689
  · exact R30691
  · exact R30693
  · exact R30695
  · exact R30697
  · exact R30699
  · exact R30701
  · exact R30703
  · exact R30705
  · exact R30707
  · exact R30709
  · exact R30711
  · exact R30713
  · exact R30715
  · exact R30717
  · exact R30719
  · exact R30721
  · exact R30723
  · exact R30725
  · exact R30727
  · exact R30729
  · exact R30731
  · exact R30733
  · exact R30735
  · exact R30737
  · exact R30739
  · exact R30741
  · exact R30743
  · exact R30745
  · exact R30747
  · exact R30749
  · exact R30751
  · exact R30753
  · exact R30755
  · exact R30757
  · exact R30759
  · exact R30761
  · exact R30763
  · exact R30765
  · exact R30767
  · exact R30769
  · exact R30771
  · exact R30773
  · exact R30775
  · exact R30777
  · exact R30779
  · exact R30781
  · exact R30783
  · exact R30785
  · exact R30787
  · exact R30789
  · exact R30791
  · exact R30793
  · exact R30795
  · exact R30797
  · exact R30799
  · exact R30801
  · exact R30803
  · exact R30805
  · exact R30807
  · exact R30809
  · exact R30811
  · exact R30813
  · exact R30815
  · exact R30817
  · exact R30819
  · exact R30821
  · exact R30823
  · exact R30825
  · exact R30827
  · exact R30829
  · exact R30831
  · exact R30833
  · exact R30835
  · exact R30837
  · exact R30839
  · exact R30841
  · exact R30843
  · exact R30845
  · exact R30847
  · exact R30849
  · exact R30851
  · exact R30853
  · exact R30855
  · exact R30857
  · exact R30859
  · exact R30861
  · exact R30863
  · exact R30865
  · exact R30867
  · exact R30869
  · exact R30871
  · exact R30873
  · exact R30875
  · exact R30877
  · exact R30879
  · exact R30881
  · exact R30883
  · exact R30885
  · exact R30887
  · exact R30889
  · exact R30891
  · exact R30893
  · exact R30895
  · exact R30897
  · exact R30899
  · exact R30901
  · exact R30903
  · exact R30905
  · exact R30907
  · exact R30909
  · exact R30911
  · exact R30913
  · exact R30915
  · exact R30917
  · exact R30919
  · exact R30921
  · exact R30923
  · exact R30925
  · exact R30927
  · exact R30929
  · exact R30931
  · exact R30933
  · exact R30935
  · exact R30937
  · exact R30939
  · exact R30941
  · exact R30943
  · exact R30945
  · exact R30947
  · exact R30949
  · exact R30951
  · exact R30953
  · exact R30955
  · exact R30957
  · exact R30959
  · exact R30961
  · exact R30963
  · exact R30965
  · exact R30967
  · exact R30969
  · exact R30971
  · exact R30973
  · exact R30975
  · exact R30977
  · exact R30979
  · exact R30981
  · exact R30983
  · exact R30985
  · exact R30987
  · exact R30989
  · exact R30991
  · exact R30993
  · exact R30995
  · exact R30997
  · exact R30999
  · exact R31001
  · exact R31003
  · exact R31005
  · exact R31007
  · exact R31009
  · exact R31011
  · exact R31013
  · exact R31015
  · exact R31017
  · exact R31019
  · exact R31021
  · exact R31023
  · exact R31025
  · exact R31027
  · exact R31029
  · exact R31031
  · exact R31033
  · exact R31035
  · exact R31037
  · exact R31039
  · exact R31041
  · exact R31043
  · exact R31045
  · exact R31047
  · exact R31049
  · exact R31051
  · exact R31053
  · exact R31055
  · exact R31057
  · exact R31059
  · exact R31061
  · exact R31063
  · exact R31065
  · exact R31067
  · exact R31069
  · exact R31071
  · exact R31073
  · exact R31075
  · exact R31077
  · exact R31079
  · exact R31081
  · exact R31083
  · exact R31085
  · exact R31087
  · exact R31089
  · exact R31091
  · exact R31093
  · exact R31095
  · exact R31097
  · exact R31099
  · exact R31101
  · exact R31103
  · exact R31105
  · exact R31107
  · exact R31109
  · exact R31111
  · exact R31113

theorem solution (m : ℕ) (hm : 0 < m) (hodd : Odd m) (hle : m ≤ 31114) :
    ∃ k : ℕ, syracuseStep^[k] m = 1 := by
  rcases Nat.lt_or_ge m 27114 with hlo | hlo
  · exact syracuse_reaches_one_below_27114 m hm hodd (by omega)
  obtain ⟨j, rfl⟩ : ∃ j, m = 2 * j + 1 := by obtain ⟨t, ht⟩ := hodd; exact ⟨t, by omega⟩
  rcases Nat.lt_or_ge j 14257 with h0 | h0
  · exact C0 j (by omega) (by omega)
  rcases Nat.lt_or_ge j 14957 with h1 | h1
  · exact C1 j (by omega) (by omega)
  exact C2 j (by omega) (by omega)
