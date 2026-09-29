-- Prove2me | solution 1 for syracuse_reaches_one_below_43118
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T05:40:00.175051+00:00
-- url     : https://prove2.me/submissions/956f0001-6ba3-4eff-9293-8f9a84ea16ba

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_reaches_one_below_39117

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
theorem B (n : ℕ) (h1 : 0 < n) (h2 : Odd n) (h3 : n ≤ 39116) : Reach n :=
  syracuse_reaches_one_below_39117 n h1 h2 h3
theorem R65605 : Reach 65605 := rs (se 4 (by rfl) ⟨6150, by rfl⟩) (B 12301 (by norm_num) ⟨6150, by rfl⟩ (by norm_num))
theorem R65861 : Reach 65861 := rs (se 4 (by rfl) ⟨6174, by rfl⟩) (B 12349 (by norm_num) ⟨6174, by rfl⟩ (by norm_num))
theorem R66109 : Reach 66109 := rs (se 3 (by rfl) ⟨12395, by rfl⟩) (B 24791 (by norm_num) ⟨12395, by rfl⟩ (by norm_num))
theorem R66197 : Reach 66197 := rs (se 6 (by rfl) ⟨1551, by rfl⟩) (B 3103 (by norm_num) ⟨1551, by rfl⟩ (by norm_num))
theorem R131765 : Reach 131765 := rs (se 5 (by rfl) ⟨6176, by rfl⟩) (B 12353 (by norm_num) ⟨6176, by rfl⟩ (by norm_num))
theorem R99053 : Reach 99053 := rs (se 3 (by rfl) ⟨18572, by rfl⟩) (B 37145 (by norm_num) ⟨18572, by rfl⟩ (by norm_num))
theorem R66325 : Reach 66325 := rs (se 6 (by rfl) ⟨1554, by rfl⟩) (B 3109 (by norm_num) ⟨1554, by rfl⟩ (by norm_num))
theorem R66413 : Reach 66413 := rs (se 3 (by rfl) ⟨12452, by rfl⟩) (B 24905 (by norm_num) ⟨12452, by rfl⟩ (by norm_num))
theorem R99245 : Reach 99245 := rs (se 3 (by rfl) ⟨18608, by rfl⟩) (B 37217 (by norm_num) ⟨18608, by rfl⟩ (by norm_num))
theorem R66541 : Reach 66541 := rs (se 3 (by rfl) ⟨12476, by rfl⟩) (B 24953 (by norm_num) ⟨12476, by rfl⟩ (by norm_num))
theorem R99389 : Reach 99389 := rs (se 3 (by rfl) ⟨18635, by rfl⟩) (B 37271 (by norm_num) ⟨18635, by rfl⟩ (by norm_num))
theorem R66629 : Reach 66629 := rs (se 4 (by rfl) ⟨6246, by rfl⟩) (B 12493 (by norm_num) ⟨6246, by rfl⟩ (by norm_num))
theorem R132245 : Reach 132245 := rs (se 6 (by rfl) ⟨3099, by rfl⟩) (B 6199 (by norm_num) ⟨3099, by rfl⟩ (by norm_num))
theorem R66757 : Reach 66757 := rs (se 4 (by rfl) ⟨6258, by rfl⟩) (B 12517 (by norm_num) ⟨6258, by rfl⟩ (by norm_num))
theorem R99589 : Reach 99589 := rs (se 4 (by rfl) ⟨9336, by rfl⟩) (B 18673 (by norm_num) ⟨9336, by rfl⟩ (by norm_num))
theorem R197909 : Reach 197909 := rs (se 6 (by rfl) ⟨4638, by rfl⟩) (B 9277 (by norm_num) ⟨4638, by rfl⟩ (by norm_num))
theorem R66845 : Reach 66845 := rs (se 3 (by rfl) ⟨12533, by rfl⟩) (B 25067 (by norm_num) ⟨12533, by rfl⟩ (by norm_num))
theorem R99701 : Reach 99701 := rs (se 5 (by rfl) ⟨4673, by rfl⟩) (B 9347 (by norm_num) ⟨4673, by rfl⟩ (by norm_num))
theorem R66973 : Reach 66973 := rs (se 3 (by rfl) ⟨12557, by rfl⟩) (B 25115 (by norm_num) ⟨12557, by rfl⟩ (by norm_num))
theorem R66989 : Reach 66989 := rs (se 3 (by rfl) ⟨12560, by rfl⟩) (B 25121 (by norm_num) ⟨12560, by rfl⟩ (by norm_num))
theorem R67061 : Reach 67061 := rs (se 5 (by rfl) ⟨3143, by rfl⟩) (B 6287 (by norm_num) ⟨3143, by rfl⟩ (by norm_num))
theorem R99893 : Reach 99893 := rs (se 5 (by rfl) ⟨4682, by rfl⟩) (B 9365 (by norm_num) ⟨4682, by rfl⟩ (by norm_num))
theorem R198197 : Reach 198197 := rs (se 5 (by rfl) ⟨9290, by rfl⟩) (B 18581 (by norm_num) ⟨9290, by rfl⟩ (by norm_num))
theorem R132677 : Reach 132677 := rs (se 4 (by rfl) ⟨12438, by rfl⟩) (B 24877 (by norm_num) ⟨12438, by rfl⟩ (by norm_num))
theorem R67189 : Reach 67189 := rs (se 5 (by rfl) ⟨3149, by rfl⟩) (B 6299 (by norm_num) ⟨3149, by rfl⟩ (by norm_num))
theorem R362165 : Reach 362165 := rs (se 5 (by rfl) ⟨16976, by rfl⟩) (B 33953 (by norm_num) ⟨16976, by rfl⟩ (by norm_num))
theorem R67277 : Reach 67277 := rs (se 3 (by rfl) ⟨12614, by rfl⟩) (B 25229 (by norm_num) ⟨12614, by rfl⟩ (by norm_num))
theorem R67405 : Reach 67405 := rs (se 3 (by rfl) ⟨12638, by rfl⟩) (B 25277 (by norm_num) ⟨12638, by rfl⟩ (by norm_num))
theorem R100237 : Reach 100237 := rs (se 3 (by rfl) ⟨18794, by rfl⟩) (B 37589 (by norm_num) ⟨18794, by rfl⟩ (by norm_num))
theorem R100253 : Reach 100253 := rs (se 3 (by rfl) ⟨18797, by rfl⟩) (B 37595 (by norm_num) ⟨18797, by rfl⟩ (by norm_num))
theorem R67493 : Reach 67493 := rs (se 4 (by rfl) ⟨6327, by rfl⟩) (B 12655 (by norm_num) ⟨6327, by rfl⟩ (by norm_num))
theorem R67501 : Reach 67501 := rs (se 3 (by rfl) ⟨12656, by rfl⟩) (B 25313 (by norm_num) ⟨12656, by rfl⟩ (by norm_num))
theorem R165845 : Reach 165845 := rs (se 7 (by rfl) ⟨1943, by rfl⟩) (B 3887 (by norm_num) ⟨1943, by rfl⟩ (by norm_num))
theorem R755669 : Reach 755669 := rs (se 7 (by rfl) ⟨8855, by rfl⟩) (B 17711 (by norm_num) ⟨8855, by rfl⟩ (by norm_num))
theorem R133109 : Reach 133109 := rs (se 5 (by rfl) ⟨6239, by rfl⟩) (B 12479 (by norm_num) ⟨6239, by rfl⟩ (by norm_num))
theorem R100349 : Reach 100349 := rs (se 3 (by rfl) ⟨18815, by rfl⟩) (B 37631 (by norm_num) ⟨18815, by rfl⟩ (by norm_num))
theorem R67621 : Reach 67621 := rs (se 4 (by rfl) ⟨6339, by rfl⟩) (B 12679 (by norm_num) ⟨6339, by rfl⟩ (by norm_num))
theorem R133157 : Reach 133157 := rs (se 4 (by rfl) ⟨12483, by rfl⟩) (B 24967 (by norm_num) ⟨12483, by rfl⟩ (by norm_num))
theorem R165989 : Reach 165989 := rs (se 4 (by rfl) ⟨15561, by rfl⟩) (B 31123 (by norm_num) ⟨15561, by rfl⟩ (by norm_num))
theorem R198773 : Reach 198773 := rs (se 5 (by rfl) ⟨9317, by rfl⟩) (B 18635 (by norm_num) ⟨9317, by rfl⟩ (by norm_num))
theorem R67709 : Reach 67709 := rs (se 3 (by rfl) ⟨12695, by rfl⟩) (B 25391 (by norm_num) ⟨12695, by rfl⟩ (by norm_num))
theorem R100541 : Reach 100541 := rs (se 3 (by rfl) ⟨18851, by rfl⟩) (B 37703 (by norm_num) ⟨18851, by rfl⟩ (by norm_num))
theorem R67837 : Reach 67837 := rs (se 3 (by rfl) ⟨12719, by rfl⟩) (B 25439 (by norm_num) ⟨12719, by rfl⟩ (by norm_num))
theorem R67925 : Reach 67925 := rs (se 10 (by rfl) ⟨99, by rfl⟩) (B 199 (by norm_num) ⟨99, by rfl⟩ (by norm_num))
theorem R133541 : Reach 133541 := rs (se 4 (by rfl) ⟨12519, by rfl⟩) (B 25039 (by norm_num) ⟨12519, by rfl⟩ (by norm_num))
theorem R68045 : Reach 68045 := rs (se 3 (by rfl) ⟨12758, by rfl⟩) (B 25517 (by norm_num) ⟨12758, by rfl⟩ (by norm_num))
theorem R68053 : Reach 68053 := rs (se 7 (by rfl) ⟨797, by rfl⟩) (B 1595 (by norm_num) ⟨797, by rfl⟩ (by norm_num))
theorem R166373 : Reach 166373 := rs (se 4 (by rfl) ⟨15597, by rfl⟩) (B 31195 (by norm_num) ⟨15597, by rfl⟩ (by norm_num))
theorem R100885 : Reach 100885 := rs (se 6 (by rfl) ⟨2364, by rfl⟩) (B 4729 (by norm_num) ⟨2364, by rfl⟩ (by norm_num))
theorem R68117 : Reach 68117 := rs (se 6 (by rfl) ⟨1596, by rfl⟩) (B 3193 (by norm_num) ⟨1596, by rfl⟩ (by norm_num))
theorem R68141 : Reach 68141 := rs (se 3 (by rfl) ⟨12776, by rfl⟩) (B 25553 (by norm_num) ⟨12776, by rfl⟩ (by norm_num))
theorem R100997 : Reach 100997 := rs (se 4 (by rfl) ⟨9468, by rfl⟩) (B 18937 (by norm_num) ⟨9468, by rfl⟩ (by norm_num))
theorem R68269 : Reach 68269 := rs (se 3 (by rfl) ⟨12800, by rfl⟩) (B 25601 (by norm_num) ⟨12800, by rfl⟩ (by norm_num))
theorem R68357 : Reach 68357 := rs (se 4 (by rfl) ⟨6408, by rfl⟩) (B 12817 (by norm_num) ⟨6408, by rfl⟩ (by norm_num))
theorem R101189 : Reach 101189 := rs (se 4 (by rfl) ⟨9486, by rfl⟩) (B 18973 (by norm_num) ⟨9486, by rfl⟩ (by norm_num))
theorem R133973 : Reach 133973 := rs (se 9 (by rfl) ⟨392, by rfl⟩) (B 785 (by norm_num) ⟨392, by rfl⟩ (by norm_num))
theorem R68485 : Reach 68485 := rs (se 4 (by rfl) ⟨6420, by rfl⟩) (B 12841 (by norm_num) ⟨6420, by rfl⟩ (by norm_num))
theorem R68573 : Reach 68573 := rs (se 3 (by rfl) ⟨12857, by rfl⟩) (B 25715 (by norm_num) ⟨12857, by rfl⟩ (by norm_num))
theorem R68597 : Reach 68597 := rs (se 5 (by rfl) ⟨3215, by rfl⟩) (B 6431 (by norm_num) ⟨3215, by rfl⟩ (by norm_num))
theorem R68629 : Reach 68629 := rs (se 6 (by rfl) ⟨1608, by rfl⟩) (B 3217 (by norm_num) ⟨1608, by rfl⟩ (by norm_num))
theorem R68701 : Reach 68701 := rs (se 3 (by rfl) ⟨12881, by rfl⟩) (B 25763 (by norm_num) ⟨12881, by rfl⟩ (by norm_num))
theorem R101533 : Reach 101533 := rs (se 3 (by rfl) ⟨19037, by rfl⟩) (B 38075 (by norm_num) ⟨19037, by rfl⟩ (by norm_num))
theorem R68789 : Reach 68789 := rs (se 5 (by rfl) ⟨3224, by rfl⟩) (B 6449 (by norm_num) ⟨3224, by rfl⟩ (by norm_num))
theorem R134405 : Reach 134405 := rs (se 4 (by rfl) ⟨12600, by rfl⟩) (B 25201 (by norm_num) ⟨12600, by rfl⟩ (by norm_num))
theorem R101645 : Reach 101645 := rs (se 3 (by rfl) ⟨19058, by rfl⟩) (B 38117 (by norm_num) ⟨19058, by rfl⟩ (by norm_num))
theorem R68917 : Reach 68917 := rs (se 5 (by rfl) ⟨3230, by rfl⟩) (B 6461 (by norm_num) ⟨3230, by rfl⟩ (by norm_num))
theorem R101741 : Reach 101741 := rs (se 3 (by rfl) ⟨19076, by rfl⟩) (B 38153 (by norm_num) ⟨19076, by rfl⟩ (by norm_num))
theorem R200069 : Reach 200069 := rs (se 4 (by rfl) ⟨18756, by rfl⟩) (B 37513 (by norm_num) ⟨18756, by rfl⟩ (by norm_num))
theorem R69005 : Reach 69005 := rs (se 3 (by rfl) ⟨12938, by rfl⟩) (B 25877 (by norm_num) ⟨12938, by rfl⟩ (by norm_num))
theorem R101837 : Reach 101837 := rs (se 3 (by rfl) ⟨19094, by rfl⟩) (B 38189 (by norm_num) ⟨19094, by rfl⟩ (by norm_num))
theorem R69133 : Reach 69133 := rs (se 3 (by rfl) ⟨12962, by rfl⟩) (B 25925 (by norm_num) ⟨12962, by rfl⟩ (by norm_num))
theorem R527957 : Reach 527957 := rs (se 8 (by rfl) ⟨3093, by rfl⟩) (B 6187 (by norm_num) ⟨3093, by rfl⟩ (by norm_num))
theorem R69221 : Reach 69221 := rs (se 4 (by rfl) ⟨6489, by rfl⟩) (B 12979 (by norm_num) ⟨6489, by rfl⟩ (by norm_num))
theorem R134837 : Reach 134837 := rs (se 5 (by rfl) ⟨6320, by rfl⟩) (B 12641 (by norm_num) ⟨6320, by rfl⟩ (by norm_num))
theorem R69349 : Reach 69349 := rs (se 4 (by rfl) ⟨6501, by rfl⟩) (B 13003 (by norm_num) ⟨6501, by rfl⟩ (by norm_num))
theorem R102181 : Reach 102181 := rs (se 4 (by rfl) ⟨9579, by rfl⟩) (B 19159 (by norm_num) ⟨9579, by rfl⟩ (by norm_num))
theorem R69437 : Reach 69437 := rs (se 3 (by rfl) ⟨13019, by rfl⟩) (B 26039 (by norm_num) ⟨13019, by rfl⟩ (by norm_num))
theorem R102293 : Reach 102293 := rs (se 6 (by rfl) ⟨2397, by rfl⟩) (B 4795 (by norm_num) ⟨2397, by rfl⟩ (by norm_num))
theorem R69565 : Reach 69565 := rs (se 3 (by rfl) ⟨13043, by rfl⟩) (B 26087 (by norm_num) ⟨13043, by rfl⟩ (by norm_num))
theorem R69653 : Reach 69653 := rs (se 6 (by rfl) ⟨1632, by rfl⟩) (B 3265 (by norm_num) ⟨1632, by rfl⟩ (by norm_num))
theorem R167989 : Reach 167989 := rs (se 5 (by rfl) ⟨7874, by rfl⟩) (B 15749 (by norm_num) ⟨7874, by rfl⟩ (by norm_num))
theorem R102485 : Reach 102485 := rs (se 8 (by rfl) ⟨600, by rfl⟩) (B 1201 (by norm_num) ⟨600, by rfl⟩ (by norm_num))
theorem R135269 : Reach 135269 := rs (se 4 (by rfl) ⟨12681, by rfl⟩) (B 25363 (by norm_num) ⟨12681, by rfl⟩ (by norm_num))
theorem R69781 : Reach 69781 := rs (se 6 (by rfl) ⟨1635, by rfl⟩) (B 3271 (by norm_num) ⟨1635, by rfl⟩ (by norm_num))
theorem R102565 : Reach 102565 := rs (se 4 (by rfl) ⟨9615, by rfl⟩) (B 19231 (by norm_num) ⟨9615, by rfl⟩ (by norm_num))
theorem R69869 : Reach 69869 := rs (se 3 (by rfl) ⟨13100, by rfl⟩) (B 26201 (by norm_num) ⟨13100, by rfl⟩ (by norm_num))
theorem R299285 : Reach 299285 := rs (se 6 (by rfl) ⟨7014, by rfl⟩) (B 14029 (by norm_num) ⟨7014, by rfl⟩ (by norm_num))
theorem R69997 : Reach 69997 := rs (se 3 (by rfl) ⟨13124, by rfl⟩) (B 26249 (by norm_num) ⟨13124, by rfl⟩ (by norm_num))
theorem R102797 : Reach 102797 := rs (se 3 (by rfl) ⟨19274, by rfl⟩) (B 38549 (by norm_num) ⟨19274, by rfl⟩ (by norm_num))
theorem R102829 : Reach 102829 := rs (se 3 (by rfl) ⟨19280, by rfl⟩) (B 38561 (by norm_num) ⟨19280, by rfl⟩ (by norm_num))
theorem R70085 : Reach 70085 := rs (se 4 (by rfl) ⟨6570, by rfl⟩) (B 13141 (by norm_num) ⟨6570, by rfl⟩ (by norm_num))
theorem R135701 : Reach 135701 := rs (se 6 (by rfl) ⟨3180, by rfl⟩) (B 6361 (by norm_num) ⟨3180, by rfl⟩ (by norm_num))
theorem R102941 : Reach 102941 := rs (se 3 (by rfl) ⟨19301, by rfl⟩) (B 38603 (by norm_num) ⟨19301, by rfl⟩ (by norm_num))
theorem R70189 : Reach 70189 := rs (se 3 (by rfl) ⟨13160, by rfl⟩) (B 26321 (by norm_num) ⟨13160, by rfl⟩ (by norm_num))
theorem R135749 : Reach 135749 := rs (se 4 (by rfl) ⟨12726, by rfl⟩) (B 25453 (by norm_num) ⟨12726, by rfl⟩ (by norm_num))
theorem R70213 : Reach 70213 := rs (se 4 (by rfl) ⟨6582, by rfl⟩) (B 13165 (by norm_num) ⟨6582, by rfl⟩ (by norm_num))
theorem R201365 : Reach 201365 := rs (se 6 (by rfl) ⟨4719, by rfl⟩) (B 9439 (by norm_num) ⟨4719, by rfl⟩ (by norm_num))
theorem R70301 : Reach 70301 := rs (se 3 (by rfl) ⟨13181, by rfl⟩) (B 26363 (by norm_num) ⟨13181, by rfl⟩ (by norm_num))
theorem R135845 : Reach 135845 := rs (se 4 (by rfl) ⟨12735, by rfl⟩) (B 25471 (by norm_num) ⟨12735, by rfl⟩ (by norm_num))
theorem R103085 : Reach 103085 := rs (se 3 (by rfl) ⟨19328, by rfl⟩) (B 38657 (by norm_num) ⟨19328, by rfl⟩ (by norm_num))
theorem R103133 : Reach 103133 := rs (se 3 (by rfl) ⟨19337, by rfl⟩) (B 38675 (by norm_num) ⟨19337, by rfl⟩ (by norm_num))
theorem R70429 : Reach 70429 := rs (se 3 (by rfl) ⟨13205, by rfl⟩) (B 26411 (by norm_num) ⟨13205, by rfl⟩ (by norm_num))
theorem R135989 : Reach 135989 := rs (se 5 (by rfl) ⟨6374, by rfl⟩) (B 12749 (by norm_num) ⟨6374, by rfl⟩ (by norm_num))
theorem R299861 : Reach 299861 := rs (se 9 (by rfl) ⟨878, by rfl⟩) (B 1757 (by norm_num) ⟨878, by rfl⟩ (by norm_num))
theorem R70517 : Reach 70517 := rs (se 5 (by rfl) ⟨3305, by rfl⟩) (B 6611 (by norm_num) ⟨3305, by rfl⟩ (by norm_num))
theorem R136133 : Reach 136133 := rs (se 4 (by rfl) ⟨12762, by rfl⟩) (B 25525 (by norm_num) ⟨12762, by rfl⟩ (by norm_num))
theorem R70645 : Reach 70645 := rs (se 5 (by rfl) ⟨3311, by rfl⟩) (B 6623 (by norm_num) ⟨3311, by rfl⟩ (by norm_num))
theorem R103477 : Reach 103477 := rs (se 5 (by rfl) ⟨4850, by rfl⟩) (B 9701 (by norm_num) ⟨4850, by rfl⟩ (by norm_num))
theorem R70733 : Reach 70733 := rs (se 3 (by rfl) ⟨13262, by rfl⟩) (B 26525 (by norm_num) ⟨13262, by rfl⟩ (by norm_num))
theorem R103589 : Reach 103589 := rs (se 4 (by rfl) ⟨9711, by rfl⟩) (B 19423 (by norm_num) ⟨9711, by rfl⟩ (by norm_num))
theorem R70861 : Reach 70861 := rs (se 3 (by rfl) ⟨13286, by rfl⟩) (B 26573 (by norm_num) ⟨13286, by rfl⟩ (by norm_num))
theorem R70949 : Reach 70949 := rs (se 4 (by rfl) ⟨6651, by rfl⟩) (B 13303 (by norm_num) ⟨6651, by rfl⟩ (by norm_num))
theorem R103781 : Reach 103781 := rs (se 4 (by rfl) ⟨9729, by rfl⟩) (B 19459 (by norm_num) ⟨9729, by rfl⟩ (by norm_num))
theorem R136565 : Reach 136565 := rs (se 5 (by rfl) ⟨6401, by rfl⟩) (B 12803 (by norm_num) ⟨6401, by rfl⟩ (by norm_num))
theorem R71077 : Reach 71077 := rs (se 4 (by rfl) ⟨6663, by rfl⟩) (B 13327 (by norm_num) ⟨6663, by rfl⟩ (by norm_num))
theorem R71165 : Reach 71165 := rs (se 3 (by rfl) ⟨13343, by rfl⟩) (B 26687 (by norm_num) ⟨13343, by rfl⟩ (by norm_num))
theorem R71293 : Reach 71293 := rs (se 3 (by rfl) ⟨13367, by rfl⟩) (B 26735 (by norm_num) ⟨13367, by rfl⟩ (by norm_num))
theorem R136885 : Reach 136885 := rs (se 5 (by rfl) ⟨6416, by rfl⟩) (B 12833 (by norm_num) ⟨6416, by rfl⟩ (by norm_num))
theorem R104125 : Reach 104125 := rs (se 3 (by rfl) ⟨19523, by rfl⟩) (B 39047 (by norm_num) ⟨19523, by rfl⟩ (by norm_num))
theorem R71381 : Reach 71381 := rs (se 7 (by rfl) ⟨836, by rfl⟩) (B 1673 (by norm_num) ⟨836, by rfl⟩ (by norm_num))
theorem R136997 : Reach 136997 := rs (se 4 (by rfl) ⟨12843, by rfl⟩) (B 25687 (by norm_num) ⟨12843, by rfl⟩ (by norm_num))
theorem R104237 : Reach 104237 := rs (se 3 (by rfl) ⟨19544, by rfl⟩) (B 39089 (by norm_num) ⟨19544, by rfl⟩ (by norm_num))
theorem R71509 : Reach 71509 := rs (se 9 (by rfl) ⟨209, by rfl⟩) (B 419 (by norm_num) ⟨209, by rfl⟩ (by norm_num))
theorem R268181 : Reach 268181 := rs (se 6 (by rfl) ⟨6285, by rfl⟩) (B 12571 (by norm_num) ⟨6285, by rfl⟩ (by norm_num))
theorem R202661 : Reach 202661 := rs (se 4 (by rfl) ⟨18999, by rfl⟩) (B 37999 (by norm_num) ⟨18999, by rfl⟩ (by norm_num))
theorem R71597 : Reach 71597 := rs (se 3 (by rfl) ⟨13424, by rfl⟩) (B 26849 (by norm_num) ⟨13424, by rfl⟩ (by norm_num))
theorem R71621 : Reach 71621 := rs (se 4 (by rfl) ⟨6714, by rfl⟩) (B 13429 (by norm_num) ⟨6714, by rfl⟩ (by norm_num))
theorem R137173 : Reach 137173 := rs (se 7 (by rfl) ⟨1607, by rfl⟩) (B 3215 (by norm_num) ⟨1607, by rfl⟩ (by norm_num))
theorem R71693 : Reach 71693 := rs (se 3 (by rfl) ⟨13442, by rfl⟩) (B 26885 (by norm_num) ⟨13442, by rfl⟩ (by norm_num))
theorem R71725 : Reach 71725 := rs (se 3 (by rfl) ⟨13448, by rfl⟩) (B 26897 (by norm_num) ⟨13448, by rfl⟩ (by norm_num))
theorem R71813 : Reach 71813 := rs (se 4 (by rfl) ⟨6732, by rfl⟩) (B 13465 (by norm_num) ⟨6732, by rfl⟩ (by norm_num))
theorem R39117 : Reach 39117 := rs (se 3 (by rfl) ⟨7334, by rfl⟩) (B 14669 (by norm_num) ⟨7334, by rfl⟩ (by norm_num))
theorem R39121 : Reach 39121 := rs (se 2 (by rfl) ⟨14670, by rfl⟩) (B 29341 (by norm_num) ⟨14670, by rfl⟩ (by norm_num))
theorem R39125 : Reach 39125 := rs (se 7 (by rfl) ⟨458, by rfl⟩) (B 917 (by norm_num) ⟨458, by rfl⟩ (by norm_num))
theorem R137429 : Reach 137429 := rs (se 7 (by rfl) ⟨1610, by rfl⟩) (B 3221 (by norm_num) ⟨1610, by rfl⟩ (by norm_num))
theorem R39129 : Reach 39129 := rs (se 2 (by rfl) ⟨14673, by rfl⟩) (B 29347 (by norm_num) ⟨14673, by rfl⟩ (by norm_num))
theorem R39133 : Reach 39133 := rs (se 3 (by rfl) ⟨7337, by rfl⟩) (B 14675 (by norm_num) ⟨7337, by rfl⟩ (by norm_num))
theorem R39137 : Reach 39137 := rs (se 2 (by rfl) ⟨14676, by rfl⟩) (B 29353 (by norm_num) ⟨14676, by rfl⟩ (by norm_num))
theorem R39141 : Reach 39141 := rs (se 4 (by rfl) ⟨3669, by rfl⟩) (B 7339 (by norm_num) ⟨3669, by rfl⟩ (by norm_num))
theorem R202981 : Reach 202981 := rs (se 4 (by rfl) ⟨19029, by rfl⟩) (B 38059 (by norm_num) ⟨19029, by rfl⟩ (by norm_num))
theorem R39145 : Reach 39145 := rs (se 2 (by rfl) ⟨14679, by rfl⟩) (B 29359 (by norm_num) ⟨14679, by rfl⟩ (by norm_num))
theorem R39149 : Reach 39149 := rs (se 3 (by rfl) ⟨7340, by rfl⟩) (B 14681 (by norm_num) ⟨7340, by rfl⟩ (by norm_num))
theorem R39153 : Reach 39153 := rs (se 2 (by rfl) ⟨14682, by rfl⟩) (B 29365 (by norm_num) ⟨14682, by rfl⟩ (by norm_num))
theorem R39157 : Reach 39157 := rs (se 5 (by rfl) ⟨1835, by rfl⟩) (B 3671 (by norm_num) ⟨1835, by rfl⟩ (by norm_num))
theorem R39161 : Reach 39161 := rs (se 2 (by rfl) ⟨14685, by rfl⟩) (B 29371 (by norm_num) ⟨14685, by rfl⟩ (by norm_num))
theorem R39165 : Reach 39165 := rs (se 3 (by rfl) ⟨7343, by rfl⟩) (B 14687 (by norm_num) ⟨7343, by rfl⟩ (by norm_num))
theorem R39169 : Reach 39169 := rs (se 2 (by rfl) ⟨14688, by rfl⟩) (B 29377 (by norm_num) ⟨14688, by rfl⟩ (by norm_num))
theorem R39173 : Reach 39173 := rs (se 4 (by rfl) ⟨3672, by rfl⟩) (B 7345 (by norm_num) ⟨3672, by rfl⟩ (by norm_num))
theorem R71941 : Reach 71941 := rs (se 4 (by rfl) ⟨6744, by rfl⟩) (B 13489 (by norm_num) ⟨6744, by rfl⟩ (by norm_num))
theorem R39177 : Reach 39177 := rs (se 2 (by rfl) ⟨14691, by rfl⟩) (B 29383 (by norm_num) ⟨14691, by rfl⟩ (by norm_num))
theorem R39181 : Reach 39181 := rs (se 3 (by rfl) ⟨7346, by rfl⟩) (B 14693 (by norm_num) ⟨7346, by rfl⟩ (by norm_num))
theorem R39185 : Reach 39185 := rs (se 2 (by rfl) ⟨14694, by rfl⟩) (B 29389 (by norm_num) ⟨14694, by rfl⟩ (by norm_num))
theorem R39189 : Reach 39189 := rs (se 6 (by rfl) ⟨918, by rfl⟩) (B 1837 (by norm_num) ⟨918, by rfl⟩ (by norm_num))
theorem R366869 : Reach 366869 := rs (se 6 (by rfl) ⟨8598, by rfl⟩) (B 17197 (by norm_num) ⟨8598, by rfl⟩ (by norm_num))
theorem R39193 : Reach 39193 := rs (se 2 (by rfl) ⟨14697, by rfl⟩) (B 29395 (by norm_num) ⟨14697, by rfl⟩ (by norm_num))
theorem R39197 : Reach 39197 := rs (se 3 (by rfl) ⟨7349, by rfl⟩) (B 14699 (by norm_num) ⟨7349, by rfl⟩ (by norm_num))
theorem R39201 : Reach 39201 := rs (se 2 (by rfl) ⟨14700, by rfl⟩) (B 29401 (by norm_num) ⟨14700, by rfl⟩ (by norm_num))
theorem R39205 : Reach 39205 := rs (se 4 (by rfl) ⟨3675, by rfl⟩) (B 7351 (by norm_num) ⟨3675, by rfl⟩ (by norm_num))
theorem R39209 : Reach 39209 := rs (se 2 (by rfl) ⟨14703, by rfl⟩) (B 29407 (by norm_num) ⟨14703, by rfl⟩ (by norm_num))
theorem R39213 : Reach 39213 := rs (se 3 (by rfl) ⟨7352, by rfl⟩) (B 14705 (by norm_num) ⟨7352, by rfl⟩ (by norm_num))
theorem R39217 : Reach 39217 := rs (se 2 (by rfl) ⟨14706, by rfl⟩) (B 29413 (by norm_num) ⟨14706, by rfl⟩ (by norm_num))
theorem R39221 : Reach 39221 := rs (se 5 (by rfl) ⟨1838, by rfl⟩) (B 3677 (by norm_num) ⟨1838, by rfl⟩ (by norm_num))
theorem R39225 : Reach 39225 := rs (se 2 (by rfl) ⟨14709, by rfl⟩) (B 29419 (by norm_num) ⟨14709, by rfl⟩ (by norm_num))
theorem R39229 : Reach 39229 := rs (se 3 (by rfl) ⟨7355, by rfl⟩) (B 14711 (by norm_num) ⟨7355, by rfl⟩ (by norm_num))
theorem R39233 : Reach 39233 := rs (se 2 (by rfl) ⟨14712, by rfl⟩) (B 29425 (by norm_num) ⟨14712, by rfl⟩ (by norm_num))
theorem R39237 : Reach 39237 := rs (se 4 (by rfl) ⟨3678, by rfl⟩) (B 7357 (by norm_num) ⟨3678, by rfl⟩ (by norm_num))
theorem R104773 : Reach 104773 := rs (se 4 (by rfl) ⟨9822, by rfl⟩) (B 19645 (by norm_num) ⟨9822, by rfl⟩ (by norm_num))
theorem R39241 : Reach 39241 := rs (se 2 (by rfl) ⟨14715, by rfl⟩) (B 29431 (by norm_num) ⟨14715, by rfl⟩ (by norm_num))
theorem R39245 : Reach 39245 := rs (se 3 (by rfl) ⟨7358, by rfl⟩) (B 14717 (by norm_num) ⟨7358, by rfl⟩ (by norm_num))
theorem R39249 : Reach 39249 := rs (se 2 (by rfl) ⟨14718, by rfl⟩) (B 29437 (by norm_num) ⟨14718, by rfl⟩ (by norm_num))
theorem R39253 : Reach 39253 := rs (se 10 (by rfl) ⟨57, by rfl⟩) (B 115 (by norm_num) ⟨57, by rfl⟩ (by norm_num))
theorem R39257 : Reach 39257 := rs (se 2 (by rfl) ⟨14721, by rfl⟩) (B 29443 (by norm_num) ⟨14721, by rfl⟩ (by norm_num))
theorem R39261 : Reach 39261 := rs (se 3 (by rfl) ⟨7361, by rfl⟩) (B 14723 (by norm_num) ⟨7361, by rfl⟩ (by norm_num))
theorem R72029 : Reach 72029 := rs (se 3 (by rfl) ⟨13505, by rfl⟩) (B 27011 (by norm_num) ⟨13505, by rfl⟩ (by norm_num))
theorem R39265 : Reach 39265 := rs (se 2 (by rfl) ⟨14724, by rfl⟩) (B 29449 (by norm_num) ⟨14724, by rfl⟩ (by norm_num))
theorem R39269 : Reach 39269 := rs (se 4 (by rfl) ⟨3681, by rfl⟩) (B 7363 (by norm_num) ⟨3681, by rfl⟩ (by norm_num))
theorem R39273 : Reach 39273 := rs (se 2 (by rfl) ⟨14727, by rfl⟩) (B 29455 (by norm_num) ⟨14727, by rfl⟩ (by norm_num))
theorem R39277 : Reach 39277 := rs (se 3 (by rfl) ⟨7364, by rfl⟩) (B 14729 (by norm_num) ⟨7364, by rfl⟩ (by norm_num))
theorem R39281 : Reach 39281 := rs (se 2 (by rfl) ⟨14730, by rfl⟩) (B 29461 (by norm_num) ⟨14730, by rfl⟩ (by norm_num))
theorem R39285 : Reach 39285 := rs (se 5 (by rfl) ⟨1841, by rfl⟩) (B 3683 (by norm_num) ⟨1841, by rfl⟩ (by norm_num))
theorem R39289 : Reach 39289 := rs (se 2 (by rfl) ⟨14733, by rfl⟩) (B 29467 (by norm_num) ⟨14733, by rfl⟩ (by norm_num))
theorem R39293 : Reach 39293 := rs (se 3 (by rfl) ⟨7367, by rfl⟩) (B 14735 (by norm_num) ⟨7367, by rfl⟩ (by norm_num))
theorem R39297 : Reach 39297 := rs (se 2 (by rfl) ⟨14736, by rfl⟩) (B 29473 (by norm_num) ⟨14736, by rfl⟩ (by norm_num))
theorem R39301 : Reach 39301 := rs (se 4 (by rfl) ⟨3684, by rfl⟩) (B 7369 (by norm_num) ⟨3684, by rfl⟩ (by norm_num))
theorem R39305 : Reach 39305 := rs (se 2 (by rfl) ⟨14739, by rfl⟩) (B 29479 (by norm_num) ⟨14739, by rfl⟩ (by norm_num))
theorem R39309 : Reach 39309 := rs (se 3 (by rfl) ⟨7370, by rfl⟩) (B 14741 (by norm_num) ⟨7370, by rfl⟩ (by norm_num))
theorem R39313 : Reach 39313 := rs (se 2 (by rfl) ⟨14742, by rfl⟩) (B 29485 (by norm_num) ⟨14742, by rfl⟩ (by norm_num))
theorem R39317 : Reach 39317 := rs (se 6 (by rfl) ⟨921, by rfl⟩) (B 1843 (by norm_num) ⟨921, by rfl⟩ (by norm_num))
theorem R39321 : Reach 39321 := rs (se 2 (by rfl) ⟨14745, by rfl⟩) (B 29491 (by norm_num) ⟨14745, by rfl⟩ (by norm_num))
theorem R39325 : Reach 39325 := rs (se 3 (by rfl) ⟨7373, by rfl⟩) (B 14747 (by norm_num) ⟨7373, by rfl⟩ (by norm_num))
theorem R39329 : Reach 39329 := rs (se 2 (by rfl) ⟨14748, by rfl⟩) (B 29497 (by norm_num) ⟨14748, by rfl⟩ (by norm_num))
theorem R39333 : Reach 39333 := rs (se 4 (by rfl) ⟨3687, by rfl⟩) (B 7375 (by norm_num) ⟨3687, by rfl⟩ (by norm_num))
theorem R39337 : Reach 39337 := rs (se 2 (by rfl) ⟨14751, by rfl⟩) (B 29503 (by norm_num) ⟨14751, by rfl⟩ (by norm_num))
theorem R39341 : Reach 39341 := rs (se 3 (by rfl) ⟨7376, by rfl⟩) (B 14753 (by norm_num) ⟨7376, by rfl⟩ (by norm_num))
theorem R39345 : Reach 39345 := rs (se 2 (by rfl) ⟨14754, by rfl⟩) (B 29509 (by norm_num) ⟨14754, by rfl⟩ (by norm_num))
theorem R39349 : Reach 39349 := rs (se 5 (by rfl) ⟨1844, by rfl⟩) (B 3689 (by norm_num) ⟨1844, by rfl⟩ (by norm_num))
theorem R104885 : Reach 104885 := rs (se 5 (by rfl) ⟨4916, by rfl⟩) (B 9833 (by norm_num) ⟨4916, by rfl⟩ (by norm_num))
theorem R39353 : Reach 39353 := rs (se 2 (by rfl) ⟨14757, by rfl⟩) (B 29515 (by norm_num) ⟨14757, by rfl⟩ (by norm_num))
theorem R39357 : Reach 39357 := rs (se 3 (by rfl) ⟨7379, by rfl⟩) (B 14759 (by norm_num) ⟨7379, by rfl⟩ (by norm_num))
theorem R39361 : Reach 39361 := rs (se 2 (by rfl) ⟨14760, by rfl⟩) (B 29521 (by norm_num) ⟨14760, by rfl⟩ (by norm_num))
theorem R39365 : Reach 39365 := rs (se 4 (by rfl) ⟨3690, by rfl⟩) (B 7381 (by norm_num) ⟨3690, by rfl⟩ (by norm_num))
theorem R39369 : Reach 39369 := rs (se 2 (by rfl) ⟨14763, by rfl⟩) (B 29527 (by norm_num) ⟨14763, by rfl⟩ (by norm_num))
theorem R39373 : Reach 39373 := rs (se 3 (by rfl) ⟨7382, by rfl⟩) (B 14765 (by norm_num) ⟨7382, by rfl⟩ (by norm_num))
theorem R39377 : Reach 39377 := rs (se 2 (by rfl) ⟨14766, by rfl⟩) (B 29533 (by norm_num) ⟨14766, by rfl⟩ (by norm_num))
theorem R39381 : Reach 39381 := rs (se 7 (by rfl) ⟨461, by rfl⟩) (B 923 (by norm_num) ⟨461, by rfl⟩ (by norm_num))
theorem R39385 : Reach 39385 := rs (se 2 (by rfl) ⟨14769, by rfl⟩) (B 29539 (by norm_num) ⟨14769, by rfl⟩ (by norm_num))
theorem R39389 : Reach 39389 := rs (se 3 (by rfl) ⟨7385, by rfl⟩) (B 14771 (by norm_num) ⟨7385, by rfl⟩ (by norm_num))
theorem R72157 : Reach 72157 := rs (se 3 (by rfl) ⟨13529, by rfl⟩) (B 27059 (by norm_num) ⟨13529, by rfl⟩ (by norm_num))
theorem R39393 : Reach 39393 := rs (se 2 (by rfl) ⟨14772, by rfl⟩) (B 29545 (by norm_num) ⟨14772, by rfl⟩ (by norm_num))
theorem R39397 : Reach 39397 := rs (se 4 (by rfl) ⟨3693, by rfl⟩) (B 7387 (by norm_num) ⟨3693, by rfl⟩ (by norm_num))
theorem R39401 : Reach 39401 := rs (se 2 (by rfl) ⟨14775, by rfl⟩) (B 29551 (by norm_num) ⟨14775, by rfl⟩ (by norm_num))
theorem R39405 : Reach 39405 := rs (se 3 (by rfl) ⟨7388, by rfl⟩) (B 14777 (by norm_num) ⟨7388, by rfl⟩ (by norm_num))
theorem R39409 : Reach 39409 := rs (se 2 (by rfl) ⟨14778, by rfl⟩) (B 29557 (by norm_num) ⟨14778, by rfl⟩ (by norm_num))
theorem R39413 : Reach 39413 := rs (se 5 (by rfl) ⟨1847, by rfl⟩) (B 3695 (by norm_num) ⟨1847, by rfl⟩ (by norm_num))
theorem R39417 : Reach 39417 := rs (se 2 (by rfl) ⟨14781, by rfl⟩) (B 29563 (by norm_num) ⟨14781, by rfl⟩ (by norm_num))
theorem R39421 : Reach 39421 := rs (se 3 (by rfl) ⟨7391, by rfl⟩) (B 14783 (by norm_num) ⟨7391, by rfl⟩ (by norm_num))
theorem R39425 : Reach 39425 := rs (se 2 (by rfl) ⟨14784, by rfl⟩) (B 29569 (by norm_num) ⟨14784, by rfl⟩ (by norm_num))
theorem R39429 : Reach 39429 := rs (se 4 (by rfl) ⟨3696, by rfl⟩) (B 7393 (by norm_num) ⟨3696, by rfl⟩ (by norm_num))
theorem R39433 : Reach 39433 := rs (se 2 (by rfl) ⟨14787, by rfl⟩) (B 29575 (by norm_num) ⟨14787, by rfl⟩ (by norm_num))
theorem R39437 : Reach 39437 := rs (se 3 (by rfl) ⟨7394, by rfl⟩) (B 14789 (by norm_num) ⟨7394, by rfl⟩ (by norm_num))
theorem R39441 : Reach 39441 := rs (se 2 (by rfl) ⟨14790, by rfl⟩) (B 29581 (by norm_num) ⟨14790, by rfl⟩ (by norm_num))
theorem R39445 : Reach 39445 := rs (se 6 (by rfl) ⟨924, by rfl⟩) (B 1849 (by norm_num) ⟨924, by rfl⟩ (by norm_num))
theorem R39449 : Reach 39449 := rs (se 2 (by rfl) ⟨14793, by rfl⟩) (B 29587 (by norm_num) ⟨14793, by rfl⟩ (by norm_num))
theorem R39453 : Reach 39453 := rs (se 3 (by rfl) ⟨7397, by rfl⟩) (B 14795 (by norm_num) ⟨7397, by rfl⟩ (by norm_num))
theorem R39457 : Reach 39457 := rs (se 2 (by rfl) ⟨14796, by rfl⟩) (B 29593 (by norm_num) ⟨14796, by rfl⟩ (by norm_num))
theorem R39461 : Reach 39461 := rs (se 4 (by rfl) ⟨3699, by rfl⟩) (B 7399 (by norm_num) ⟨3699, by rfl⟩ (by norm_num))
theorem R39465 : Reach 39465 := rs (se 2 (by rfl) ⟨14799, by rfl⟩) (B 29599 (by norm_num) ⟨14799, by rfl⟩ (by norm_num))
theorem R39469 : Reach 39469 := rs (se 3 (by rfl) ⟨7400, by rfl⟩) (B 14801 (by norm_num) ⟨7400, by rfl⟩ (by norm_num))
theorem R39473 : Reach 39473 := rs (se 2 (by rfl) ⟨14802, by rfl⟩) (B 29605 (by norm_num) ⟨14802, by rfl⟩ (by norm_num))
theorem R39477 : Reach 39477 := rs (se 5 (by rfl) ⟨1850, by rfl⟩) (B 3701 (by norm_num) ⟨1850, by rfl⟩ (by norm_num))
theorem R72245 : Reach 72245 := rs (se 5 (by rfl) ⟨3386, by rfl⟩) (B 6773 (by norm_num) ⟨3386, by rfl⟩ (by norm_num))
theorem R39481 : Reach 39481 := rs (se 2 (by rfl) ⟨14805, by rfl⟩) (B 29611 (by norm_num) ⟨14805, by rfl⟩ (by norm_num))
theorem R39485 : Reach 39485 := rs (se 3 (by rfl) ⟨7403, by rfl⟩) (B 14807 (by norm_num) ⟨7403, by rfl⟩ (by norm_num))
theorem R39489 : Reach 39489 := rs (se 2 (by rfl) ⟨14808, by rfl⟩) (B 29617 (by norm_num) ⟨14808, by rfl⟩ (by norm_num))
theorem R39493 : Reach 39493 := rs (se 4 (by rfl) ⟨3702, by rfl⟩) (B 7405 (by norm_num) ⟨3702, by rfl⟩ (by norm_num))
theorem R39497 : Reach 39497 := rs (se 2 (by rfl) ⟨14811, by rfl⟩) (B 29623 (by norm_num) ⟨14811, by rfl⟩ (by norm_num))
theorem R39501 : Reach 39501 := rs (se 3 (by rfl) ⟨7406, by rfl⟩) (B 14813 (by norm_num) ⟨7406, by rfl⟩ (by norm_num))
theorem R39505 : Reach 39505 := rs (se 2 (by rfl) ⟨14814, by rfl⟩) (B 29629 (by norm_num) ⟨14814, by rfl⟩ (by norm_num))
theorem R39509 : Reach 39509 := rs (se 8 (by rfl) ⟨231, by rfl⟩) (B 463 (by norm_num) ⟨231, by rfl⟩ (by norm_num))
theorem R39513 : Reach 39513 := rs (se 2 (by rfl) ⟨14817, by rfl⟩) (B 29635 (by norm_num) ⟨14817, by rfl⟩ (by norm_num))
theorem R39517 : Reach 39517 := rs (se 3 (by rfl) ⟨7409, by rfl⟩) (B 14819 (by norm_num) ⟨7409, by rfl⟩ (by norm_num))
theorem R39521 : Reach 39521 := rs (se 2 (by rfl) ⟨14820, by rfl⟩) (B 29641 (by norm_num) ⟨14820, by rfl⟩ (by norm_num))
theorem R39525 : Reach 39525 := rs (se 4 (by rfl) ⟨3705, by rfl⟩) (B 7411 (by norm_num) ⟨3705, by rfl⟩ (by norm_num))
theorem R39529 : Reach 39529 := rs (se 2 (by rfl) ⟨14823, by rfl⟩) (B 29647 (by norm_num) ⟨14823, by rfl⟩ (by norm_num))
theorem R39533 : Reach 39533 := rs (se 3 (by rfl) ⟨7412, by rfl⟩) (B 14825 (by norm_num) ⟨7412, by rfl⟩ (by norm_num))
theorem R39537 : Reach 39537 := rs (se 2 (by rfl) ⟨14826, by rfl⟩) (B 29653 (by norm_num) ⟨14826, by rfl⟩ (by norm_num))
theorem R39541 : Reach 39541 := rs (se 5 (by rfl) ⟨1853, by rfl⟩) (B 3707 (by norm_num) ⟨1853, by rfl⟩ (by norm_num))
theorem R203381 : Reach 203381 := rs (se 5 (by rfl) ⟨9533, by rfl⟩) (B 19067 (by norm_num) ⟨9533, by rfl⟩ (by norm_num))
theorem R105077 : Reach 105077 := rs (se 5 (by rfl) ⟨4925, by rfl⟩) (B 9851 (by norm_num) ⟨4925, by rfl⟩ (by norm_num))
theorem R39545 : Reach 39545 := rs (se 2 (by rfl) ⟨14829, by rfl⟩) (B 29659 (by norm_num) ⟨14829, by rfl⟩ (by norm_num))
theorem R39549 : Reach 39549 := rs (se 3 (by rfl) ⟨7415, by rfl⟩) (B 14831 (by norm_num) ⟨7415, by rfl⟩ (by norm_num))
theorem R39553 : Reach 39553 := rs (se 2 (by rfl) ⟨14832, by rfl⟩) (B 29665 (by norm_num) ⟨14832, by rfl⟩ (by norm_num))
theorem R137861 : Reach 137861 := rs (se 4 (by rfl) ⟨12924, by rfl⟩) (B 25849 (by norm_num) ⟨12924, by rfl⟩ (by norm_num))
theorem R39557 : Reach 39557 := rs (se 4 (by rfl) ⟨3708, by rfl⟩) (B 7417 (by norm_num) ⟨3708, by rfl⟩ (by norm_num))
theorem R39561 : Reach 39561 := rs (se 2 (by rfl) ⟨14835, by rfl⟩) (B 29671 (by norm_num) ⟨14835, by rfl⟩ (by norm_num))
theorem R39565 : Reach 39565 := rs (se 3 (by rfl) ⟨7418, by rfl⟩) (B 14837 (by norm_num) ⟨7418, by rfl⟩ (by norm_num))
theorem R39569 : Reach 39569 := rs (se 2 (by rfl) ⟨14838, by rfl⟩) (B 29677 (by norm_num) ⟨14838, by rfl⟩ (by norm_num))
theorem R39573 : Reach 39573 := rs (se 6 (by rfl) ⟨927, by rfl⟩) (B 1855 (by norm_num) ⟨927, by rfl⟩ (by norm_num))
theorem R39577 : Reach 39577 := rs (se 2 (by rfl) ⟨14841, by rfl⟩) (B 29683 (by norm_num) ⟨14841, by rfl⟩ (by norm_num))
theorem R39581 : Reach 39581 := rs (se 3 (by rfl) ⟨7421, by rfl⟩) (B 14843 (by norm_num) ⟨7421, by rfl⟩ (by norm_num))
theorem R39585 : Reach 39585 := rs (se 2 (by rfl) ⟨14844, by rfl⟩) (B 29689 (by norm_num) ⟨14844, by rfl⟩ (by norm_num))
theorem R39589 : Reach 39589 := rs (se 4 (by rfl) ⟨3711, by rfl⟩) (B 7423 (by norm_num) ⟨3711, by rfl⟩ (by norm_num))
theorem R39593 : Reach 39593 := rs (se 2 (by rfl) ⟨14847, by rfl⟩) (B 29695 (by norm_num) ⟨14847, by rfl⟩ (by norm_num))
theorem R39597 : Reach 39597 := rs (se 3 (by rfl) ⟨7424, by rfl⟩) (B 14849 (by norm_num) ⟨7424, by rfl⟩ (by norm_num))
theorem R39601 : Reach 39601 := rs (se 2 (by rfl) ⟨14850, by rfl⟩) (B 29701 (by norm_num) ⟨14850, by rfl⟩ (by norm_num))
theorem R39605 : Reach 39605 := rs (se 5 (by rfl) ⟨1856, by rfl⟩) (B 3713 (by norm_num) ⟨1856, by rfl⟩ (by norm_num))
theorem R72373 : Reach 72373 := rs (se 5 (by rfl) ⟨3392, by rfl⟩) (B 6785 (by norm_num) ⟨3392, by rfl⟩ (by norm_num))
theorem R39609 : Reach 39609 := rs (se 2 (by rfl) ⟨14853, by rfl⟩) (B 29707 (by norm_num) ⟨14853, by rfl⟩ (by norm_num))
theorem R39613 : Reach 39613 := rs (se 3 (by rfl) ⟨7427, by rfl⟩) (B 14855 (by norm_num) ⟨7427, by rfl⟩ (by norm_num))
theorem R39617 : Reach 39617 := rs (se 2 (by rfl) ⟨14856, by rfl⟩) (B 29713 (by norm_num) ⟨14856, by rfl⟩ (by norm_num))
theorem R39621 : Reach 39621 := rs (se 4 (by rfl) ⟨3714, by rfl⟩) (B 7429 (by norm_num) ⟨3714, by rfl⟩ (by norm_num))
theorem R39625 : Reach 39625 := rs (se 2 (by rfl) ⟨14859, by rfl⟩) (B 29719 (by norm_num) ⟨14859, by rfl⟩ (by norm_num))
theorem R39629 : Reach 39629 := rs (se 3 (by rfl) ⟨7430, by rfl⟩) (B 14861 (by norm_num) ⟨7430, by rfl⟩ (by norm_num))
theorem R39633 : Reach 39633 := rs (se 2 (by rfl) ⟨14862, by rfl⟩) (B 29725 (by norm_num) ⟨14862, by rfl⟩ (by norm_num))
theorem R39637 : Reach 39637 := rs (se 7 (by rfl) ⟨464, by rfl⟩) (B 929 (by norm_num) ⟨464, by rfl⟩ (by norm_num))
theorem R400085 : Reach 400085 := rs (se 7 (by rfl) ⟨4688, by rfl⟩) (B 9377 (by norm_num) ⟨4688, by rfl⟩ (by norm_num))
theorem R39641 : Reach 39641 := rs (se 2 (by rfl) ⟨14865, by rfl⟩) (B 29731 (by norm_num) ⟨14865, by rfl⟩ (by norm_num))
theorem R39645 : Reach 39645 := rs (se 3 (by rfl) ⟨7433, by rfl⟩) (B 14867 (by norm_num) ⟨7433, by rfl⟩ (by norm_num))
theorem R39649 : Reach 39649 := rs (se 2 (by rfl) ⟨14868, by rfl⟩) (B 29737 (by norm_num) ⟨14868, by rfl⟩ (by norm_num))
theorem R39653 : Reach 39653 := rs (se 4 (by rfl) ⟨3717, by rfl⟩) (B 7435 (by norm_num) ⟨3717, by rfl⟩ (by norm_num))
theorem R39657 : Reach 39657 := rs (se 2 (by rfl) ⟨14871, by rfl⟩) (B 29743 (by norm_num) ⟨14871, by rfl⟩ (by norm_num))
theorem R39661 : Reach 39661 := rs (se 3 (by rfl) ⟨7436, by rfl⟩) (B 14873 (by norm_num) ⟨7436, by rfl⟩ (by norm_num))
theorem R39665 : Reach 39665 := rs (se 2 (by rfl) ⟨14874, by rfl⟩) (B 29749 (by norm_num) ⟨14874, by rfl⟩ (by norm_num))
theorem R39669 : Reach 39669 := rs (se 5 (by rfl) ⟨1859, by rfl⟩) (B 3719 (by norm_num) ⟨1859, by rfl⟩ (by norm_num))
theorem R39673 : Reach 39673 := rs (se 2 (by rfl) ⟨14877, by rfl⟩) (B 29755 (by norm_num) ⟨14877, by rfl⟩ (by norm_num))
theorem R39677 : Reach 39677 := rs (se 3 (by rfl) ⟨7439, by rfl⟩) (B 14879 (by norm_num) ⟨7439, by rfl⟩ (by norm_num))
theorem R39681 : Reach 39681 := rs (se 2 (by rfl) ⟨14880, by rfl⟩) (B 29761 (by norm_num) ⟨14880, by rfl⟩ (by norm_num))
theorem R39685 : Reach 39685 := rs (se 4 (by rfl) ⟨3720, by rfl⟩) (B 7441 (by norm_num) ⟨3720, by rfl⟩ (by norm_num))
theorem R39689 : Reach 39689 := rs (se 2 (by rfl) ⟨14883, by rfl⟩) (B 29767 (by norm_num) ⟨14883, by rfl⟩ (by norm_num))
theorem R39693 : Reach 39693 := rs (se 3 (by rfl) ⟨7442, by rfl⟩) (B 14885 (by norm_num) ⟨7442, by rfl⟩ (by norm_num))
theorem R72461 : Reach 72461 := rs (se 3 (by rfl) ⟨13586, by rfl⟩) (B 27173 (by norm_num) ⟨13586, by rfl⟩ (by norm_num))
theorem R39697 : Reach 39697 := rs (se 2 (by rfl) ⟨14886, by rfl⟩) (B 29773 (by norm_num) ⟨14886, by rfl⟩ (by norm_num))
theorem R39701 : Reach 39701 := rs (se 6 (by rfl) ⟨930, by rfl⟩) (B 1861 (by norm_num) ⟨930, by rfl⟩ (by norm_num))
theorem R39705 : Reach 39705 := rs (se 2 (by rfl) ⟨14889, by rfl⟩) (B 29779 (by norm_num) ⟨14889, by rfl⟩ (by norm_num))
theorem R39709 : Reach 39709 := rs (se 3 (by rfl) ⟨7445, by rfl⟩) (B 14891 (by norm_num) ⟨7445, by rfl⟩ (by norm_num))
theorem R39713 : Reach 39713 := rs (se 2 (by rfl) ⟨14892, by rfl⟩) (B 29785 (by norm_num) ⟨14892, by rfl⟩ (by norm_num))
theorem R39717 : Reach 39717 := rs (se 4 (by rfl) ⟨3723, by rfl⟩) (B 7447 (by norm_num) ⟨3723, by rfl⟩ (by norm_num))
theorem R39721 : Reach 39721 := rs (se 2 (by rfl) ⟨14895, by rfl⟩) (B 29791 (by norm_num) ⟨14895, by rfl⟩ (by norm_num))
theorem R39725 : Reach 39725 := rs (se 3 (by rfl) ⟨7448, by rfl⟩) (B 14897 (by norm_num) ⟨7448, by rfl⟩ (by norm_num))
theorem R39729 : Reach 39729 := rs (se 2 (by rfl) ⟨14898, by rfl⟩) (B 29797 (by norm_num) ⟨14898, by rfl⟩ (by norm_num))
theorem R39733 : Reach 39733 := rs (se 5 (by rfl) ⟨1862, by rfl⟩) (B 3725 (by norm_num) ⟨1862, by rfl⟩ (by norm_num))
theorem R39737 : Reach 39737 := rs (se 2 (by rfl) ⟨14901, by rfl⟩) (B 29803 (by norm_num) ⟨14901, by rfl⟩ (by norm_num))
theorem R39741 : Reach 39741 := rs (se 3 (by rfl) ⟨7451, by rfl⟩) (B 14903 (by norm_num) ⟨7451, by rfl⟩ (by norm_num))
theorem R39745 : Reach 39745 := rs (se 2 (by rfl) ⟨14904, by rfl⟩) (B 29809 (by norm_num) ⟨14904, by rfl⟩ (by norm_num))
theorem R39749 : Reach 39749 := rs (se 4 (by rfl) ⟨3726, by rfl⟩) (B 7453 (by norm_num) ⟨3726, by rfl⟩ (by norm_num))
theorem R39753 : Reach 39753 := rs (se 2 (by rfl) ⟨14907, by rfl⟩) (B 29815 (by norm_num) ⟨14907, by rfl⟩ (by norm_num))
theorem R39757 : Reach 39757 := rs (se 3 (by rfl) ⟨7454, by rfl⟩) (B 14909 (by norm_num) ⟨7454, by rfl⟩ (by norm_num))
theorem R39761 : Reach 39761 := rs (se 2 (by rfl) ⟨14910, by rfl⟩) (B 29821 (by norm_num) ⟨14910, by rfl⟩ (by norm_num))
theorem R39765 : Reach 39765 := rs (se 9 (by rfl) ⟨116, by rfl⟩) (B 233 (by norm_num) ⟨116, by rfl⟩ (by norm_num))
theorem R39769 : Reach 39769 := rs (se 2 (by rfl) ⟨14913, by rfl⟩) (B 29827 (by norm_num) ⟨14913, by rfl⟩ (by norm_num))
theorem R39773 : Reach 39773 := rs (se 3 (by rfl) ⟨7457, by rfl⟩) (B 14915 (by norm_num) ⟨7457, by rfl⟩ (by norm_num))
theorem R39777 : Reach 39777 := rs (se 2 (by rfl) ⟨14916, by rfl⟩) (B 29833 (by norm_num) ⟨14916, by rfl⟩ (by norm_num))
theorem R39781 : Reach 39781 := rs (se 4 (by rfl) ⟨3729, by rfl⟩) (B 7459 (by norm_num) ⟨3729, by rfl⟩ (by norm_num))
theorem R39785 : Reach 39785 := rs (se 2 (by rfl) ⟨14919, by rfl⟩) (B 29839 (by norm_num) ⟨14919, by rfl⟩ (by norm_num))
theorem R39789 : Reach 39789 := rs (se 3 (by rfl) ⟨7460, by rfl⟩) (B 14921 (by norm_num) ⟨7460, by rfl⟩ (by norm_num))
theorem R39793 : Reach 39793 := rs (se 2 (by rfl) ⟨14922, by rfl⟩) (B 29845 (by norm_num) ⟨14922, by rfl⟩ (by norm_num))
theorem R39797 : Reach 39797 := rs (se 5 (by rfl) ⟨1865, by rfl⟩) (B 3731 (by norm_num) ⟨1865, by rfl⟩ (by norm_num))
theorem R39801 : Reach 39801 := rs (se 2 (by rfl) ⟨14925, by rfl⟩) (B 29851 (by norm_num) ⟨14925, by rfl⟩ (by norm_num))
theorem R39805 : Reach 39805 := rs (se 3 (by rfl) ⟨7463, by rfl⟩) (B 14927 (by norm_num) ⟨7463, by rfl⟩ (by norm_num))
theorem R39809 : Reach 39809 := rs (se 2 (by rfl) ⟨14928, by rfl⟩) (B 29857 (by norm_num) ⟨14928, by rfl⟩ (by norm_num))
theorem R39813 : Reach 39813 := rs (se 4 (by rfl) ⟨3732, by rfl⟩) (B 7465 (by norm_num) ⟨3732, by rfl⟩ (by norm_num))
theorem R39817 : Reach 39817 := rs (se 2 (by rfl) ⟨14931, by rfl⟩) (B 29863 (by norm_num) ⟨14931, by rfl⟩ (by norm_num))
theorem R39821 : Reach 39821 := rs (se 3 (by rfl) ⟨7466, by rfl⟩) (B 14933 (by norm_num) ⟨7466, by rfl⟩ (by norm_num))
theorem R72589 : Reach 72589 := rs (se 3 (by rfl) ⟨13610, by rfl⟩) (B 27221 (by norm_num) ⟨13610, by rfl⟩ (by norm_num))
theorem R39825 : Reach 39825 := rs (se 2 (by rfl) ⟨14934, by rfl⟩) (B 29869 (by norm_num) ⟨14934, by rfl⟩ (by norm_num))
theorem R39829 : Reach 39829 := rs (se 6 (by rfl) ⟨933, by rfl⟩) (B 1867 (by norm_num) ⟨933, by rfl⟩ (by norm_num))
theorem R39833 : Reach 39833 := rs (se 2 (by rfl) ⟨14937, by rfl⟩) (B 29875 (by norm_num) ⟨14937, by rfl⟩ (by norm_num))
theorem R39837 : Reach 39837 := rs (se 3 (by rfl) ⟨7469, by rfl⟩) (B 14939 (by norm_num) ⟨7469, by rfl⟩ (by norm_num))
theorem R39841 : Reach 39841 := rs (se 2 (by rfl) ⟨14940, by rfl⟩) (B 29881 (by norm_num) ⟨14940, by rfl⟩ (by norm_num))
theorem R39845 : Reach 39845 := rs (se 4 (by rfl) ⟨3735, by rfl⟩) (B 7471 (by norm_num) ⟨3735, by rfl⟩ (by norm_num))
theorem R39849 : Reach 39849 := rs (se 2 (by rfl) ⟨14943, by rfl⟩) (B 29887 (by norm_num) ⟨14943, by rfl⟩ (by norm_num))
theorem R39853 : Reach 39853 := rs (se 3 (by rfl) ⟨7472, by rfl⟩) (B 14945 (by norm_num) ⟨7472, by rfl⟩ (by norm_num))
theorem R39857 : Reach 39857 := rs (se 2 (by rfl) ⟨14946, by rfl⟩) (B 29893 (by norm_num) ⟨14946, by rfl⟩ (by norm_num))
theorem R39861 : Reach 39861 := rs (se 5 (by rfl) ⟨1868, by rfl⟩) (B 3737 (by norm_num) ⟨1868, by rfl⟩ (by norm_num))
theorem R39865 : Reach 39865 := rs (se 2 (by rfl) ⟨14949, by rfl⟩) (B 29899 (by norm_num) ⟨14949, by rfl⟩ (by norm_num))
theorem R39869 : Reach 39869 := rs (se 3 (by rfl) ⟨7475, by rfl⟩) (B 14951 (by norm_num) ⟨7475, by rfl⟩ (by norm_num))
theorem R39873 : Reach 39873 := rs (se 2 (by rfl) ⟨14952, by rfl⟩) (B 29905 (by norm_num) ⟨14952, by rfl⟩ (by norm_num))
theorem R39877 : Reach 39877 := rs (se 4 (by rfl) ⟨3738, by rfl⟩) (B 7477 (by norm_num) ⟨3738, by rfl⟩ (by norm_num))
theorem R39881 : Reach 39881 := rs (se 2 (by rfl) ⟨14955, by rfl⟩) (B 29911 (by norm_num) ⟨14955, by rfl⟩ (by norm_num))
theorem R39885 : Reach 39885 := rs (se 3 (by rfl) ⟨7478, by rfl⟩) (B 14957 (by norm_num) ⟨7478, by rfl⟩ (by norm_num))
theorem R39889 : Reach 39889 := rs (se 2 (by rfl) ⟨14958, by rfl⟩) (B 29917 (by norm_num) ⟨14958, by rfl⟩ (by norm_num))
theorem R39893 : Reach 39893 := rs (se 7 (by rfl) ⟨467, by rfl⟩) (B 935 (by norm_num) ⟨467, by rfl⟩ (by norm_num))
theorem R39897 : Reach 39897 := rs (se 2 (by rfl) ⟨14961, by rfl⟩) (B 29923 (by norm_num) ⟨14961, by rfl⟩ (by norm_num))
theorem R39901 : Reach 39901 := rs (se 3 (by rfl) ⟨7481, by rfl⟩) (B 14963 (by norm_num) ⟨7481, by rfl⟩ (by norm_num))
theorem R39905 : Reach 39905 := rs (se 2 (by rfl) ⟨14964, by rfl⟩) (B 29929 (by norm_num) ⟨14964, by rfl⟩ (by norm_num))
theorem R39909 : Reach 39909 := rs (se 4 (by rfl) ⟨3741, by rfl⟩) (B 7483 (by norm_num) ⟨3741, by rfl⟩ (by norm_num))
theorem R170981 : Reach 170981 := rs (se 4 (by rfl) ⟨16029, by rfl⟩) (B 32059 (by norm_num) ⟨16029, by rfl⟩ (by norm_num))
theorem R72677 : Reach 72677 := rs (se 4 (by rfl) ⟨6813, by rfl⟩) (B 13627 (by norm_num) ⟨6813, by rfl⟩ (by norm_num))
theorem R39913 : Reach 39913 := rs (se 2 (by rfl) ⟨14967, by rfl⟩) (B 29935 (by norm_num) ⟨14967, by rfl⟩ (by norm_num))
theorem R39917 : Reach 39917 := rs (se 3 (by rfl) ⟨7484, by rfl⟩) (B 14969 (by norm_num) ⟨7484, by rfl⟩ (by norm_num))
theorem R39921 : Reach 39921 := rs (se 2 (by rfl) ⟨14970, by rfl⟩) (B 29941 (by norm_num) ⟨14970, by rfl⟩ (by norm_num))
theorem R39925 : Reach 39925 := rs (se 5 (by rfl) ⟨1871, by rfl⟩) (B 3743 (by norm_num) ⟨1871, by rfl⟩ (by norm_num))
theorem R39929 : Reach 39929 := rs (se 2 (by rfl) ⟨14973, by rfl⟩) (B 29947 (by norm_num) ⟨14973, by rfl⟩ (by norm_num))
theorem R39933 : Reach 39933 := rs (se 3 (by rfl) ⟨7487, by rfl⟩) (B 14975 (by norm_num) ⟨7487, by rfl⟩ (by norm_num))
theorem R39937 : Reach 39937 := rs (se 2 (by rfl) ⟨14976, by rfl⟩) (B 29953 (by norm_num) ⟨14976, by rfl⟩ (by norm_num))
theorem R39941 : Reach 39941 := rs (se 4 (by rfl) ⟨3744, by rfl⟩) (B 7489 (by norm_num) ⟨3744, by rfl⟩ (by norm_num))
theorem R39945 : Reach 39945 := rs (se 2 (by rfl) ⟨14979, by rfl⟩) (B 29959 (by norm_num) ⟨14979, by rfl⟩ (by norm_num))
theorem R39949 : Reach 39949 := rs (se 3 (by rfl) ⟨7490, by rfl⟩) (B 14981 (by norm_num) ⟨7490, by rfl⟩ (by norm_num))
theorem R39953 : Reach 39953 := rs (se 2 (by rfl) ⟨14982, by rfl⟩) (B 29965 (by norm_num) ⟨14982, by rfl⟩ (by norm_num))
theorem R39957 : Reach 39957 := rs (se 6 (by rfl) ⟨936, by rfl⟩) (B 1873 (by norm_num) ⟨936, by rfl⟩ (by norm_num))
theorem R39961 : Reach 39961 := rs (se 2 (by rfl) ⟨14985, by rfl⟩) (B 29971 (by norm_num) ⟨14985, by rfl⟩ (by norm_num))
theorem R39965 : Reach 39965 := rs (se 3 (by rfl) ⟨7493, by rfl⟩) (B 14987 (by norm_num) ⟨7493, by rfl⟩ (by norm_num))
theorem R39969 : Reach 39969 := rs (se 2 (by rfl) ⟨14988, by rfl⟩) (B 29977 (by norm_num) ⟨14988, by rfl⟩ (by norm_num))
theorem R39973 : Reach 39973 := rs (se 4 (by rfl) ⟨3747, by rfl⟩) (B 7495 (by norm_num) ⟨3747, by rfl⟩ (by norm_num))
theorem R39977 : Reach 39977 := rs (se 2 (by rfl) ⟨14991, by rfl⟩) (B 29983 (by norm_num) ⟨14991, by rfl⟩ (by norm_num))
theorem R39981 : Reach 39981 := rs (se 3 (by rfl) ⟨7496, by rfl⟩) (B 14993 (by norm_num) ⟨7496, by rfl⟩ (by norm_num))
theorem R39985 : Reach 39985 := rs (se 2 (by rfl) ⟨14994, by rfl⟩) (B 29989 (by norm_num) ⟨14994, by rfl⟩ (by norm_num))
theorem R39989 : Reach 39989 := rs (se 5 (by rfl) ⟨1874, by rfl⟩) (B 3749 (by norm_num) ⟨1874, by rfl⟩ (by norm_num))
theorem R138293 : Reach 138293 := rs (se 5 (by rfl) ⟨6482, by rfl⟩) (B 12965 (by norm_num) ⟨6482, by rfl⟩ (by norm_num))
theorem R39993 : Reach 39993 := rs (se 2 (by rfl) ⟨14997, by rfl⟩) (B 29995 (by norm_num) ⟨14997, by rfl⟩ (by norm_num))
theorem R39997 : Reach 39997 := rs (se 3 (by rfl) ⟨7499, by rfl⟩) (B 14999 (by norm_num) ⟨7499, by rfl⟩ (by norm_num))
theorem R40001 : Reach 40001 := rs (se 2 (by rfl) ⟨15000, by rfl⟩) (B 30001 (by norm_num) ⟨15000, by rfl⟩ (by norm_num))
theorem R40005 : Reach 40005 := rs (se 4 (by rfl) ⟨3750, by rfl⟩) (B 7501 (by norm_num) ⟨3750, by rfl⟩ (by norm_num))
theorem R40009 : Reach 40009 := rs (se 2 (by rfl) ⟨15003, by rfl⟩) (B 30007 (by norm_num) ⟨15003, by rfl⟩ (by norm_num))
theorem R40013 : Reach 40013 := rs (se 3 (by rfl) ⟨7502, by rfl⟩) (B 15005 (by norm_num) ⟨7502, by rfl⟩ (by norm_num))
theorem R40017 : Reach 40017 := rs (se 2 (by rfl) ⟨15006, by rfl⟩) (B 30013 (by norm_num) ⟨15006, by rfl⟩ (by norm_num))
theorem R40021 : Reach 40021 := rs (se 8 (by rfl) ⟨234, by rfl⟩) (B 469 (by norm_num) ⟨234, by rfl⟩ (by norm_num))
theorem R236629 : Reach 236629 := rs (se 8 (by rfl) ⟨1386, by rfl⟩) (B 2773 (by norm_num) ⟨1386, by rfl⟩ (by norm_num))
theorem R40025 : Reach 40025 := rs (se 2 (by rfl) ⟨15009, by rfl⟩) (B 30019 (by norm_num) ⟨15009, by rfl⟩ (by norm_num))
theorem R40029 : Reach 40029 := rs (se 3 (by rfl) ⟨7505, by rfl⟩) (B 15011 (by norm_num) ⟨7505, by rfl⟩ (by norm_num))
theorem R40033 : Reach 40033 := rs (se 2 (by rfl) ⟨15012, by rfl⟩) (B 30025 (by norm_num) ⟨15012, by rfl⟩ (by norm_num))
theorem R40037 : Reach 40037 := rs (se 4 (by rfl) ⟨3753, by rfl⟩) (B 7507 (by norm_num) ⟨3753, by rfl⟩ (by norm_num))
theorem R40041 : Reach 40041 := rs (se 2 (by rfl) ⟨15015, by rfl⟩) (B 30031 (by norm_num) ⟨15015, by rfl⟩ (by norm_num))
theorem R40045 : Reach 40045 := rs (se 3 (by rfl) ⟨7508, by rfl⟩) (B 15017 (by norm_num) ⟨7508, by rfl⟩ (by norm_num))
theorem R40049 : Reach 40049 := rs (se 2 (by rfl) ⟨15018, by rfl⟩) (B 30037 (by norm_num) ⟨15018, by rfl⟩ (by norm_num))
theorem R40053 : Reach 40053 := rs (se 5 (by rfl) ⟨1877, by rfl⟩) (B 3755 (by norm_num) ⟨1877, by rfl⟩ (by norm_num))
theorem R40057 : Reach 40057 := rs (se 2 (by rfl) ⟨15021, by rfl⟩) (B 30043 (by norm_num) ⟨15021, by rfl⟩ (by norm_num))
theorem R40061 : Reach 40061 := rs (se 3 (by rfl) ⟨7511, by rfl⟩) (B 15023 (by norm_num) ⟨7511, by rfl⟩ (by norm_num))
theorem R40065 : Reach 40065 := rs (se 2 (by rfl) ⟨15024, by rfl⟩) (B 30049 (by norm_num) ⟨15024, by rfl⟩ (by norm_num))
theorem R40069 : Reach 40069 := rs (se 4 (by rfl) ⟨3756, by rfl⟩) (B 7513 (by norm_num) ⟨3756, by rfl⟩ (by norm_num))
theorem R40073 : Reach 40073 := rs (se 2 (by rfl) ⟨15027, by rfl⟩) (B 30055 (by norm_num) ⟨15027, by rfl⟩ (by norm_num))
theorem R40077 : Reach 40077 := rs (se 3 (by rfl) ⟨7514, by rfl⟩) (B 15029 (by norm_num) ⟨7514, by rfl⟩ (by norm_num))
theorem R40081 : Reach 40081 := rs (se 2 (by rfl) ⟨15030, by rfl⟩) (B 30061 (by norm_num) ⟨15030, by rfl⟩ (by norm_num))
theorem R40085 : Reach 40085 := rs (se 6 (by rfl) ⟨939, by rfl⟩) (B 1879 (by norm_num) ⟨939, by rfl⟩ (by norm_num))
theorem R40089 : Reach 40089 := rs (se 2 (by rfl) ⟨15033, by rfl⟩) (B 30067 (by norm_num) ⟨15033, by rfl⟩ (by norm_num))
theorem R40093 : Reach 40093 := rs (se 3 (by rfl) ⟨7517, by rfl⟩) (B 15035 (by norm_num) ⟨7517, by rfl⟩ (by norm_num))
theorem R40097 : Reach 40097 := rs (se 2 (by rfl) ⟨15036, by rfl⟩) (B 30073 (by norm_num) ⟨15036, by rfl⟩ (by norm_num))
theorem R40101 : Reach 40101 := rs (se 4 (by rfl) ⟨3759, by rfl⟩) (B 7519 (by norm_num) ⟨3759, by rfl⟩ (by norm_num))
theorem R40105 : Reach 40105 := rs (se 2 (by rfl) ⟨15039, by rfl⟩) (B 30079 (by norm_num) ⟨15039, by rfl⟩ (by norm_num))
theorem R40109 : Reach 40109 := rs (se 3 (by rfl) ⟨7520, by rfl⟩) (B 15041 (by norm_num) ⟨7520, by rfl⟩ (by norm_num))
theorem R40113 : Reach 40113 := rs (se 2 (by rfl) ⟨15042, by rfl⟩) (B 30085 (by norm_num) ⟨15042, by rfl⟩ (by norm_num))
theorem R40117 : Reach 40117 := rs (se 5 (by rfl) ⟨1880, by rfl⟩) (B 3761 (by norm_num) ⟨1880, by rfl⟩ (by norm_num))
theorem R203957 : Reach 203957 := rs (se 5 (by rfl) ⟨9560, by rfl⟩) (B 19121 (by norm_num) ⟨9560, by rfl⟩ (by norm_num))
theorem R40121 : Reach 40121 := rs (se 2 (by rfl) ⟨15045, by rfl⟩) (B 30091 (by norm_num) ⟨15045, by rfl⟩ (by norm_num))
theorem R40125 : Reach 40125 := rs (se 3 (by rfl) ⟨7523, by rfl⟩) (B 15047 (by norm_num) ⟨7523, by rfl⟩ (by norm_num))
theorem R40129 : Reach 40129 := rs (se 2 (by rfl) ⟨15048, by rfl⟩) (B 30097 (by norm_num) ⟨15048, by rfl⟩ (by norm_num))
theorem R40133 : Reach 40133 := rs (se 4 (by rfl) ⟨3762, by rfl⟩) (B 7525 (by norm_num) ⟨3762, by rfl⟩ (by norm_num))
theorem R40137 : Reach 40137 := rs (se 2 (by rfl) ⟨15051, by rfl⟩) (B 30103 (by norm_num) ⟨15051, by rfl⟩ (by norm_num))
theorem R40141 : Reach 40141 := rs (se 3 (by rfl) ⟨7526, by rfl⟩) (B 15053 (by norm_num) ⟨7526, by rfl⟩ (by norm_num))
theorem R40145 : Reach 40145 := rs (se 2 (by rfl) ⟨15054, by rfl⟩) (B 30109 (by norm_num) ⟨15054, by rfl⟩ (by norm_num))
theorem R40149 : Reach 40149 := rs (se 7 (by rfl) ⟨470, by rfl⟩) (B 941 (by norm_num) ⟨470, by rfl⟩ (by norm_num))
theorem R40153 : Reach 40153 := rs (se 2 (by rfl) ⟨15057, by rfl⟩) (B 30115 (by norm_num) ⟨15057, by rfl⟩ (by norm_num))
theorem R40157 : Reach 40157 := rs (se 3 (by rfl) ⟨7529, by rfl⟩) (B 15059 (by norm_num) ⟨7529, by rfl⟩ (by norm_num))
theorem R40161 : Reach 40161 := rs (se 2 (by rfl) ⟨15060, by rfl⟩) (B 30121 (by norm_num) ⟨15060, by rfl⟩ (by norm_num))
theorem R40165 : Reach 40165 := rs (se 4 (by rfl) ⟨3765, by rfl⟩) (B 7531 (by norm_num) ⟨3765, by rfl⟩ (by norm_num))
theorem R40169 : Reach 40169 := rs (se 2 (by rfl) ⟨15063, by rfl⟩) (B 30127 (by norm_num) ⟨15063, by rfl⟩ (by norm_num))
theorem R40173 : Reach 40173 := rs (se 3 (by rfl) ⟨7532, by rfl⟩) (B 15065 (by norm_num) ⟨7532, by rfl⟩ (by norm_num))
theorem R40177 : Reach 40177 := rs (se 2 (by rfl) ⟨15066, by rfl⟩) (B 30133 (by norm_num) ⟨15066, by rfl⟩ (by norm_num))
theorem R40181 : Reach 40181 := rs (se 5 (by rfl) ⟨1883, by rfl⟩) (B 3767 (by norm_num) ⟨1883, by rfl⟩ (by norm_num))
theorem R236789 : Reach 236789 := rs (se 5 (by rfl) ⟨11099, by rfl⟩) (B 22199 (by norm_num) ⟨11099, by rfl⟩ (by norm_num))
theorem R40185 : Reach 40185 := rs (se 2 (by rfl) ⟨15069, by rfl⟩) (B 30139 (by norm_num) ⟨15069, by rfl⟩ (by norm_num))
theorem R40189 : Reach 40189 := rs (se 3 (by rfl) ⟨7535, by rfl⟩) (B 15071 (by norm_num) ⟨7535, by rfl⟩ (by norm_num))
theorem R40193 : Reach 40193 := rs (se 2 (by rfl) ⟨15072, by rfl⟩) (B 30145 (by norm_num) ⟨15072, by rfl⟩ (by norm_num))
theorem R40197 : Reach 40197 := rs (se 4 (by rfl) ⟨3768, by rfl⟩) (B 7537 (by norm_num) ⟨3768, by rfl⟩ (by norm_num))
theorem R72965 : Reach 72965 := rs (se 4 (by rfl) ⟨6840, by rfl⟩) (B 13681 (by norm_num) ⟨6840, by rfl⟩ (by norm_num))
theorem R40201 : Reach 40201 := rs (se 2 (by rfl) ⟨15075, by rfl⟩) (B 30151 (by norm_num) ⟨15075, by rfl⟩ (by norm_num))
theorem R40205 : Reach 40205 := rs (se 3 (by rfl) ⟨7538, by rfl⟩) (B 15077 (by norm_num) ⟨7538, by rfl⟩ (by norm_num))
theorem R40209 : Reach 40209 := rs (se 2 (by rfl) ⟨15078, by rfl⟩) (B 30157 (by norm_num) ⟨15078, by rfl⟩ (by norm_num))
theorem R40213 : Reach 40213 := rs (se 6 (by rfl) ⟨942, by rfl⟩) (B 1885 (by norm_num) ⟨942, by rfl⟩ (by norm_num))
theorem R40217 : Reach 40217 := rs (se 2 (by rfl) ⟨15081, by rfl⟩) (B 30163 (by norm_num) ⟨15081, by rfl⟩ (by norm_num))
theorem R40221 : Reach 40221 := rs (se 3 (by rfl) ⟨7541, by rfl⟩) (B 15083 (by norm_num) ⟨7541, by rfl⟩ (by norm_num))
theorem R40225 : Reach 40225 := rs (se 2 (by rfl) ⟨15084, by rfl⟩) (B 30169 (by norm_num) ⟨15084, by rfl⟩ (by norm_num))
theorem R40229 : Reach 40229 := rs (se 4 (by rfl) ⟨3771, by rfl⟩) (B 7543 (by norm_num) ⟨3771, by rfl⟩ (by norm_num))
theorem R40233 : Reach 40233 := rs (se 2 (by rfl) ⟨15087, by rfl⟩) (B 30175 (by norm_num) ⟨15087, by rfl⟩ (by norm_num))
theorem R40237 : Reach 40237 := rs (se 3 (by rfl) ⟨7544, by rfl⟩) (B 15089 (by norm_num) ⟨7544, by rfl⟩ (by norm_num))
theorem R40241 : Reach 40241 := rs (se 2 (by rfl) ⟨15090, by rfl⟩) (B 30181 (by norm_num) ⟨15090, by rfl⟩ (by norm_num))
theorem R40245 : Reach 40245 := rs (se 5 (by rfl) ⟨1886, by rfl⟩) (B 3773 (by norm_num) ⟨1886, by rfl⟩ (by norm_num))
theorem R40249 : Reach 40249 := rs (se 2 (by rfl) ⟨15093, by rfl⟩) (B 30187 (by norm_num) ⟨15093, by rfl⟩ (by norm_num))
theorem R40253 : Reach 40253 := rs (se 3 (by rfl) ⟨7547, by rfl⟩) (B 15095 (by norm_num) ⟨7547, by rfl⟩ (by norm_num))
theorem R40257 : Reach 40257 := rs (se 2 (by rfl) ⟨15096, by rfl⟩) (B 30193 (by norm_num) ⟨15096, by rfl⟩ (by norm_num))
theorem R40261 : Reach 40261 := rs (se 4 (by rfl) ⟨3774, by rfl⟩) (B 7549 (by norm_num) ⟨3774, by rfl⟩ (by norm_num))
theorem R40265 : Reach 40265 := rs (se 2 (by rfl) ⟨15099, by rfl⟩) (B 30199 (by norm_num) ⟨15099, by rfl⟩ (by norm_num))
theorem R40269 : Reach 40269 := rs (se 3 (by rfl) ⟨7550, by rfl⟩) (B 15101 (by norm_num) ⟨7550, by rfl⟩ (by norm_num))
theorem R40273 : Reach 40273 := rs (se 2 (by rfl) ⟨15102, by rfl⟩) (B 30205 (by norm_num) ⟨15102, by rfl⟩ (by norm_num))
theorem R40277 : Reach 40277 := rs (se 11 (by rfl) ⟨29, by rfl⟩) (B 59 (by norm_num) ⟨29, by rfl⟩ (by norm_num))
theorem R40281 : Reach 40281 := rs (se 2 (by rfl) ⟨15105, by rfl⟩) (B 30211 (by norm_num) ⟨15105, by rfl⟩ (by norm_num))
theorem R40285 : Reach 40285 := rs (se 3 (by rfl) ⟨7553, by rfl⟩) (B 15107 (by norm_num) ⟨7553, by rfl⟩ (by norm_num))
theorem R40289 : Reach 40289 := rs (se 2 (by rfl) ⟨15108, by rfl⟩) (B 30217 (by norm_num) ⟨15108, by rfl⟩ (by norm_num))
theorem R40293 : Reach 40293 := rs (se 4 (by rfl) ⟨3777, by rfl⟩) (B 7555 (by norm_num) ⟨3777, by rfl⟩ (by norm_num))
theorem R40297 : Reach 40297 := rs (se 2 (by rfl) ⟨15111, by rfl⟩) (B 30223 (by norm_num) ⟨15111, by rfl⟩ (by norm_num))
theorem R40301 : Reach 40301 := rs (se 3 (by rfl) ⟨7556, by rfl⟩) (B 15113 (by norm_num) ⟨7556, by rfl⟩ (by norm_num))
theorem R40305 : Reach 40305 := rs (se 2 (by rfl) ⟨15114, by rfl⟩) (B 30229 (by norm_num) ⟨15114, by rfl⟩ (by norm_num))
theorem R40309 : Reach 40309 := rs (se 5 (by rfl) ⟨1889, by rfl⟩) (B 3779 (by norm_num) ⟨1889, by rfl⟩ (by norm_num))
theorem R40313 : Reach 40313 := rs (se 2 (by rfl) ⟨15117, by rfl⟩) (B 30235 (by norm_num) ⟨15117, by rfl⟩ (by norm_num))
theorem R40317 : Reach 40317 := rs (se 3 (by rfl) ⟨7559, by rfl⟩) (B 15119 (by norm_num) ⟨7559, by rfl⟩ (by norm_num))
theorem R40321 : Reach 40321 := rs (se 2 (by rfl) ⟨15120, by rfl⟩) (B 30241 (by norm_num) ⟨15120, by rfl⟩ (by norm_num))
theorem R40325 : Reach 40325 := rs (se 4 (by rfl) ⟨3780, by rfl⟩) (B 7561 (by norm_num) ⟨3780, by rfl⟩ (by norm_num))
theorem R40329 : Reach 40329 := rs (se 2 (by rfl) ⟨15123, by rfl⟩) (B 30247 (by norm_num) ⟨15123, by rfl⟩ (by norm_num))
theorem R40333 : Reach 40333 := rs (se 3 (by rfl) ⟨7562, by rfl⟩) (B 15125 (by norm_num) ⟨7562, by rfl⟩ (by norm_num))
theorem R40337 : Reach 40337 := rs (se 2 (by rfl) ⟨15126, by rfl⟩) (B 30253 (by norm_num) ⟨15126, by rfl⟩ (by norm_num))
theorem R40341 : Reach 40341 := rs (se 6 (by rfl) ⟨945, by rfl⟩) (B 1891 (by norm_num) ⟨945, by rfl⟩ (by norm_num))
theorem R40345 : Reach 40345 := rs (se 2 (by rfl) ⟨15129, by rfl⟩) (B 30259 (by norm_num) ⟨15129, by rfl⟩ (by norm_num))
theorem R40349 : Reach 40349 := rs (se 3 (by rfl) ⟨7565, by rfl⟩) (B 15131 (by norm_num) ⟨7565, by rfl⟩ (by norm_num))
theorem R40353 : Reach 40353 := rs (se 2 (by rfl) ⟨15132, by rfl⟩) (B 30265 (by norm_num) ⟨15132, by rfl⟩ (by norm_num))
theorem R40357 : Reach 40357 := rs (se 4 (by rfl) ⟨3783, by rfl⟩) (B 7567 (by norm_num) ⟨3783, by rfl⟩ (by norm_num))
theorem R40361 : Reach 40361 := rs (se 2 (by rfl) ⟨15135, by rfl⟩) (B 30271 (by norm_num) ⟨15135, by rfl⟩ (by norm_num))
theorem R40365 : Reach 40365 := rs (se 3 (by rfl) ⟨7568, by rfl⟩) (B 15137 (by norm_num) ⟨7568, by rfl⟩ (by norm_num))
theorem R40369 : Reach 40369 := rs (se 2 (by rfl) ⟨15138, by rfl⟩) (B 30277 (by norm_num) ⟨15138, by rfl⟩ (by norm_num))
theorem R40373 : Reach 40373 := rs (se 5 (by rfl) ⟨1892, by rfl⟩) (B 3785 (by norm_num) ⟨1892, by rfl⟩ (by norm_num))
theorem R40377 : Reach 40377 := rs (se 2 (by rfl) ⟨15141, by rfl⟩) (B 30283 (by norm_num) ⟨15141, by rfl⟩ (by norm_num))
theorem R40381 : Reach 40381 := rs (se 3 (by rfl) ⟨7571, by rfl⟩) (B 15143 (by norm_num) ⟨7571, by rfl⟩ (by norm_num))
theorem R40385 : Reach 40385 := rs (se 2 (by rfl) ⟨15144, by rfl⟩) (B 30289 (by norm_num) ⟨15144, by rfl⟩ (by norm_num))
theorem R40389 : Reach 40389 := rs (se 4 (by rfl) ⟨3786, by rfl⟩) (B 7573 (by norm_num) ⟨3786, by rfl⟩ (by norm_num))
theorem R40393 : Reach 40393 := rs (se 2 (by rfl) ⟨15147, by rfl⟩) (B 30295 (by norm_num) ⟨15147, by rfl⟩ (by norm_num))
theorem R40397 : Reach 40397 := rs (se 3 (by rfl) ⟨7574, by rfl⟩) (B 15149 (by norm_num) ⟨7574, by rfl⟩ (by norm_num))
theorem R40401 : Reach 40401 := rs (se 2 (by rfl) ⟨15150, by rfl⟩) (B 30301 (by norm_num) ⟨15150, by rfl⟩ (by norm_num))
theorem R40405 : Reach 40405 := rs (se 7 (by rfl) ⟨473, by rfl⟩) (B 947 (by norm_num) ⟨473, by rfl⟩ (by norm_num))
theorem R40409 : Reach 40409 := rs (se 2 (by rfl) ⟨15153, by rfl⟩) (B 30307 (by norm_num) ⟨15153, by rfl⟩ (by norm_num))
theorem R40413 : Reach 40413 := rs (se 3 (by rfl) ⟨7577, by rfl⟩) (B 15155 (by norm_num) ⟨7577, by rfl⟩ (by norm_num))
theorem R40417 : Reach 40417 := rs (se 2 (by rfl) ⟨15156, by rfl⟩) (B 30313 (by norm_num) ⟨15156, by rfl⟩ (by norm_num))
theorem R40421 : Reach 40421 := rs (se 4 (by rfl) ⟨3789, by rfl⟩) (B 7579 (by norm_num) ⟨3789, by rfl⟩ (by norm_num))
theorem R138725 : Reach 138725 := rs (se 4 (by rfl) ⟨13005, by rfl⟩) (B 26011 (by norm_num) ⟨13005, by rfl⟩ (by norm_num))
theorem R40425 : Reach 40425 := rs (se 2 (by rfl) ⟨15159, by rfl⟩) (B 30319 (by norm_num) ⟨15159, by rfl⟩ (by norm_num))
theorem R40429 : Reach 40429 := rs (se 3 (by rfl) ⟨7580, by rfl⟩) (B 15161 (by norm_num) ⟨7580, by rfl⟩ (by norm_num))
theorem R40433 : Reach 40433 := rs (se 2 (by rfl) ⟨15162, by rfl⟩) (B 30325 (by norm_num) ⟨15162, by rfl⟩ (by norm_num))
theorem R40437 : Reach 40437 := rs (se 5 (by rfl) ⟨1895, by rfl⟩) (B 3791 (by norm_num) ⟨1895, by rfl⟩ (by norm_num))
theorem R40441 : Reach 40441 := rs (se 2 (by rfl) ⟨15165, by rfl⟩) (B 30331 (by norm_num) ⟨15165, by rfl⟩ (by norm_num))
theorem R40445 : Reach 40445 := rs (se 3 (by rfl) ⟨7583, by rfl⟩) (B 15167 (by norm_num) ⟨7583, by rfl⟩ (by norm_num))
theorem R40449 : Reach 40449 := rs (se 2 (by rfl) ⟨15168, by rfl⟩) (B 30337 (by norm_num) ⟨15168, by rfl⟩ (by norm_num))
theorem R40453 : Reach 40453 := rs (se 4 (by rfl) ⟨3792, by rfl⟩) (B 7585 (by norm_num) ⟨3792, by rfl⟩ (by norm_num))
theorem R40457 : Reach 40457 := rs (se 2 (by rfl) ⟨15171, by rfl⟩) (B 30343 (by norm_num) ⟨15171, by rfl⟩ (by norm_num))
theorem R40461 : Reach 40461 := rs (se 3 (by rfl) ⟨7586, by rfl⟩) (B 15173 (by norm_num) ⟨7586, by rfl⟩ (by norm_num))
theorem R40465 : Reach 40465 := rs (se 2 (by rfl) ⟨15174, by rfl⟩) (B 30349 (by norm_num) ⟨15174, by rfl⟩ (by norm_num))
theorem R40469 : Reach 40469 := rs (se 6 (by rfl) ⟨948, by rfl⟩) (B 1897 (by norm_num) ⟨948, by rfl⟩ (by norm_num))
theorem R40473 : Reach 40473 := rs (se 2 (by rfl) ⟨15177, by rfl⟩) (B 30355 (by norm_num) ⟨15177, by rfl⟩ (by norm_num))
theorem R40477 : Reach 40477 := rs (se 3 (by rfl) ⟨7589, by rfl⟩) (B 15179 (by norm_num) ⟨7589, by rfl⟩ (by norm_num))
theorem R40481 : Reach 40481 := rs (se 2 (by rfl) ⟨15180, by rfl⟩) (B 30361 (by norm_num) ⟨15180, by rfl⟩ (by norm_num))
theorem R40485 : Reach 40485 := rs (se 4 (by rfl) ⟨3795, by rfl⟩) (B 7591 (by norm_num) ⟨3795, by rfl⟩ (by norm_num))
theorem R40489 : Reach 40489 := rs (se 2 (by rfl) ⟨15183, by rfl⟩) (B 30367 (by norm_num) ⟨15183, by rfl⟩ (by norm_num))
theorem R40493 : Reach 40493 := rs (se 3 (by rfl) ⟨7592, by rfl⟩) (B 15185 (by norm_num) ⟨7592, by rfl⟩ (by norm_num))
theorem R40497 : Reach 40497 := rs (se 2 (by rfl) ⟨15186, by rfl⟩) (B 30373 (by norm_num) ⟨15186, by rfl⟩ (by norm_num))
theorem R40501 : Reach 40501 := rs (se 5 (by rfl) ⟨1898, by rfl⟩) (B 3797 (by norm_num) ⟨1898, by rfl⟩ (by norm_num))
theorem R40505 : Reach 40505 := rs (se 2 (by rfl) ⟨15189, by rfl⟩) (B 30379 (by norm_num) ⟨15189, by rfl⟩ (by norm_num))
theorem R40509 : Reach 40509 := rs (se 3 (by rfl) ⟨7595, by rfl⟩) (B 15191 (by norm_num) ⟨7595, by rfl⟩ (by norm_num))
theorem R40513 : Reach 40513 := rs (se 2 (by rfl) ⟨15192, by rfl⟩) (B 30385 (by norm_num) ⟨15192, by rfl⟩ (by norm_num))
theorem R40517 : Reach 40517 := rs (se 4 (by rfl) ⟨3798, by rfl⟩) (B 7597 (by norm_num) ⟨3798, by rfl⟩ (by norm_num))
theorem R40521 : Reach 40521 := rs (se 2 (by rfl) ⟨15195, by rfl⟩) (B 30391 (by norm_num) ⟨15195, by rfl⟩ (by norm_num))
theorem R40525 : Reach 40525 := rs (se 3 (by rfl) ⟨7598, by rfl⟩) (B 15197 (by norm_num) ⟨7598, by rfl⟩ (by norm_num))
theorem R40529 : Reach 40529 := rs (se 2 (by rfl) ⟨15198, by rfl⟩) (B 30397 (by norm_num) ⟨15198, by rfl⟩ (by norm_num))
theorem R40533 : Reach 40533 := rs (se 8 (by rfl) ⟨237, by rfl⟩) (B 475 (by norm_num) ⟨237, by rfl⟩ (by norm_num))
theorem R106069 : Reach 106069 := rs (se 8 (by rfl) ⟨621, by rfl⟩) (B 1243 (by norm_num) ⟨621, by rfl⟩ (by norm_num))
theorem R40537 : Reach 40537 := rs (se 2 (by rfl) ⟨15201, by rfl⟩) (B 30403 (by norm_num) ⟨15201, by rfl⟩ (by norm_num))
theorem R40541 : Reach 40541 := rs (se 3 (by rfl) ⟨7601, by rfl⟩) (B 15203 (by norm_num) ⟨7601, by rfl⟩ (by norm_num))
theorem R40545 : Reach 40545 := rs (se 2 (by rfl) ⟨15204, by rfl⟩) (B 30409 (by norm_num) ⟨15204, by rfl⟩ (by norm_num))
theorem R40549 : Reach 40549 := rs (se 4 (by rfl) ⟨3801, by rfl⟩) (B 7603 (by norm_num) ⟨3801, by rfl⟩ (by norm_num))
theorem R40553 : Reach 40553 := rs (se 2 (by rfl) ⟨15207, by rfl⟩) (B 30415 (by norm_num) ⟨15207, by rfl⟩ (by norm_num))
theorem R40557 : Reach 40557 := rs (se 3 (by rfl) ⟨7604, by rfl⟩) (B 15209 (by norm_num) ⟨7604, by rfl⟩ (by norm_num))
theorem R40561 : Reach 40561 := rs (se 2 (by rfl) ⟨15210, by rfl⟩) (B 30421 (by norm_num) ⟨15210, by rfl⟩ (by norm_num))
theorem R40565 : Reach 40565 := rs (se 5 (by rfl) ⟨1901, by rfl⟩) (B 3803 (by norm_num) ⟨1901, by rfl⟩ (by norm_num))
theorem R40569 : Reach 40569 := rs (se 2 (by rfl) ⟨15213, by rfl⟩) (B 30427 (by norm_num) ⟨15213, by rfl⟩ (by norm_num))
theorem R40573 : Reach 40573 := rs (se 3 (by rfl) ⟨7607, by rfl⟩) (B 15215 (by norm_num) ⟨7607, by rfl⟩ (by norm_num))
theorem R40577 : Reach 40577 := rs (se 2 (by rfl) ⟨15216, by rfl⟩) (B 30433 (by norm_num) ⟨15216, by rfl⟩ (by norm_num))
theorem R40581 : Reach 40581 := rs (se 4 (by rfl) ⟨3804, by rfl⟩) (B 7609 (by norm_num) ⟨3804, by rfl⟩ (by norm_num))
theorem R40585 : Reach 40585 := rs (se 2 (by rfl) ⟨15219, by rfl⟩) (B 30439 (by norm_num) ⟨15219, by rfl⟩ (by norm_num))
theorem R40589 : Reach 40589 := rs (se 3 (by rfl) ⟨7610, by rfl⟩) (B 15221 (by norm_num) ⟨7610, by rfl⟩ (by norm_num))
theorem R40593 : Reach 40593 := rs (se 2 (by rfl) ⟨15222, by rfl⟩) (B 30445 (by norm_num) ⟨15222, by rfl⟩ (by norm_num))
theorem R40597 : Reach 40597 := rs (se 6 (by rfl) ⟨951, by rfl⟩) (B 1903 (by norm_num) ⟨951, by rfl⟩ (by norm_num))
theorem R40601 : Reach 40601 := rs (se 2 (by rfl) ⟨15225, by rfl⟩) (B 30451 (by norm_num) ⟨15225, by rfl⟩ (by norm_num))
theorem R40605 : Reach 40605 := rs (se 3 (by rfl) ⟨7613, by rfl⟩) (B 15227 (by norm_num) ⟨7613, by rfl⟩ (by norm_num))
theorem R40609 : Reach 40609 := rs (se 2 (by rfl) ⟨15228, by rfl⟩) (B 30457 (by norm_num) ⟨15228, by rfl⟩ (by norm_num))
theorem R40613 : Reach 40613 := rs (se 4 (by rfl) ⟨3807, by rfl⟩) (B 7615 (by norm_num) ⟨3807, by rfl⟩ (by norm_num))
theorem R40617 : Reach 40617 := rs (se 2 (by rfl) ⟨15231, by rfl⟩) (B 30463 (by norm_num) ⟨15231, by rfl⟩ (by norm_num))
theorem R40621 : Reach 40621 := rs (se 3 (by rfl) ⟨7616, by rfl⟩) (B 15233 (by norm_num) ⟨7616, by rfl⟩ (by norm_num))
theorem R40625 : Reach 40625 := rs (se 2 (by rfl) ⟨15234, by rfl⟩) (B 30469 (by norm_num) ⟨15234, by rfl⟩ (by norm_num))
theorem R40629 : Reach 40629 := rs (se 5 (by rfl) ⟨1904, by rfl⟩) (B 3809 (by norm_num) ⟨1904, by rfl⟩ (by norm_num))
theorem R40633 : Reach 40633 := rs (se 2 (by rfl) ⟨15237, by rfl⟩) (B 30475 (by norm_num) ⟨15237, by rfl⟩ (by norm_num))
theorem R40637 : Reach 40637 := rs (se 3 (by rfl) ⟨7619, by rfl⟩) (B 15239 (by norm_num) ⟨7619, by rfl⟩ (by norm_num))
theorem R40641 : Reach 40641 := rs (se 2 (by rfl) ⟨15240, by rfl⟩) (B 30481 (by norm_num) ⟨15240, by rfl⟩ (by norm_num))
theorem R40645 : Reach 40645 := rs (se 4 (by rfl) ⟨3810, by rfl⟩) (B 7621 (by norm_num) ⟨3810, by rfl⟩ (by norm_num))
theorem R106181 : Reach 106181 := rs (se 4 (by rfl) ⟨9954, by rfl⟩) (B 19909 (by norm_num) ⟨9954, by rfl⟩ (by norm_num))
theorem R40649 : Reach 40649 := rs (se 2 (by rfl) ⟨15243, by rfl⟩) (B 30487 (by norm_num) ⟨15243, by rfl⟩ (by norm_num))
theorem R40653 : Reach 40653 := rs (se 3 (by rfl) ⟨7622, by rfl⟩) (B 15245 (by norm_num) ⟨7622, by rfl⟩ (by norm_num))
theorem R40657 : Reach 40657 := rs (se 2 (by rfl) ⟨15246, by rfl⟩) (B 30493 (by norm_num) ⟨15246, by rfl⟩ (by norm_num))
theorem R40661 : Reach 40661 := rs (se 7 (by rfl) ⟨476, by rfl⟩) (B 953 (by norm_num) ⟨476, by rfl⟩ (by norm_num))
theorem R40665 : Reach 40665 := rs (se 2 (by rfl) ⟨15249, by rfl⟩) (B 30499 (by norm_num) ⟨15249, by rfl⟩ (by norm_num))
theorem R40669 : Reach 40669 := rs (se 3 (by rfl) ⟨7625, by rfl⟩) (B 15251 (by norm_num) ⟨7625, by rfl⟩ (by norm_num))
theorem R40673 : Reach 40673 := rs (se 2 (by rfl) ⟨15252, by rfl⟩) (B 30505 (by norm_num) ⟨15252, by rfl⟩ (by norm_num))
theorem R40677 : Reach 40677 := rs (se 4 (by rfl) ⟨3813, by rfl⟩) (B 7627 (by norm_num) ⟨3813, by rfl⟩ (by norm_num))
theorem R40681 : Reach 40681 := rs (se 2 (by rfl) ⟨15255, by rfl⟩) (B 30511 (by norm_num) ⟨15255, by rfl⟩ (by norm_num))
theorem R40685 : Reach 40685 := rs (se 3 (by rfl) ⟨7628, by rfl⟩) (B 15257 (by norm_num) ⟨7628, by rfl⟩ (by norm_num))
theorem R40689 : Reach 40689 := rs (se 2 (by rfl) ⟨15258, by rfl⟩) (B 30517 (by norm_num) ⟨15258, by rfl⟩ (by norm_num))
theorem R40693 : Reach 40693 := rs (se 5 (by rfl) ⟨1907, by rfl⟩) (B 3815 (by norm_num) ⟨1907, by rfl⟩ (by norm_num))
theorem R40697 : Reach 40697 := rs (se 2 (by rfl) ⟨15261, by rfl⟩) (B 30523 (by norm_num) ⟨15261, by rfl⟩ (by norm_num))
theorem R40701 : Reach 40701 := rs (se 3 (by rfl) ⟨7631, by rfl⟩) (B 15263 (by norm_num) ⟨7631, by rfl⟩ (by norm_num))
theorem R40705 : Reach 40705 := rs (se 2 (by rfl) ⟨15264, by rfl⟩) (B 30529 (by norm_num) ⟨15264, by rfl⟩ (by norm_num))
theorem R40709 : Reach 40709 := rs (se 4 (by rfl) ⟨3816, by rfl⟩) (B 7633 (by norm_num) ⟨3816, by rfl⟩ (by norm_num))
theorem R40713 : Reach 40713 := rs (se 2 (by rfl) ⟨15267, by rfl⟩) (B 30535 (by norm_num) ⟨15267, by rfl⟩ (by norm_num))
theorem R40717 : Reach 40717 := rs (se 3 (by rfl) ⟨7634, by rfl⟩) (B 15269 (by norm_num) ⟨7634, by rfl⟩ (by norm_num))
theorem R40721 : Reach 40721 := rs (se 2 (by rfl) ⟨15270, by rfl⟩) (B 30541 (by norm_num) ⟨15270, by rfl⟩ (by norm_num))
theorem R40725 : Reach 40725 := rs (se 6 (by rfl) ⟨954, by rfl⟩) (B 1909 (by norm_num) ⟨954, by rfl⟩ (by norm_num))
theorem R40729 : Reach 40729 := rs (se 2 (by rfl) ⟨15273, by rfl⟩) (B 30547 (by norm_num) ⟨15273, by rfl⟩ (by norm_num))
theorem R40733 : Reach 40733 := rs (se 3 (by rfl) ⟨7637, by rfl⟩) (B 15275 (by norm_num) ⟨7637, by rfl⟩ (by norm_num))
theorem R40737 : Reach 40737 := rs (se 2 (by rfl) ⟨15276, by rfl⟩) (B 30553 (by norm_num) ⟨15276, by rfl⟩ (by norm_num))
theorem R40741 : Reach 40741 := rs (se 4 (by rfl) ⟨3819, by rfl⟩) (B 7639 (by norm_num) ⟨3819, by rfl⟩ (by norm_num))
theorem R40745 : Reach 40745 := rs (se 2 (by rfl) ⟨15279, by rfl⟩) (B 30559 (by norm_num) ⟨15279, by rfl⟩ (by norm_num))
theorem R40749 : Reach 40749 := rs (se 3 (by rfl) ⟨7640, by rfl⟩) (B 15281 (by norm_num) ⟨7640, by rfl⟩ (by norm_num))
theorem R40753 : Reach 40753 := rs (se 2 (by rfl) ⟨15282, by rfl⟩) (B 30565 (by norm_num) ⟨15282, by rfl⟩ (by norm_num))
theorem R40757 : Reach 40757 := rs (se 5 (by rfl) ⟨1910, by rfl⟩) (B 3821 (by norm_num) ⟨1910, by rfl⟩ (by norm_num))
theorem R40761 : Reach 40761 := rs (se 2 (by rfl) ⟨15285, by rfl⟩) (B 30571 (by norm_num) ⟨15285, by rfl⟩ (by norm_num))
theorem R40765 : Reach 40765 := rs (se 3 (by rfl) ⟨7643, by rfl⟩) (B 15287 (by norm_num) ⟨7643, by rfl⟩ (by norm_num))
theorem R40769 : Reach 40769 := rs (se 2 (by rfl) ⟨15288, by rfl⟩) (B 30577 (by norm_num) ⟨15288, by rfl⟩ (by norm_num))
theorem R40773 : Reach 40773 := rs (se 4 (by rfl) ⟨3822, by rfl⟩) (B 7645 (by norm_num) ⟨3822, by rfl⟩ (by norm_num))
theorem R40777 : Reach 40777 := rs (se 2 (by rfl) ⟨15291, by rfl⟩) (B 30583 (by norm_num) ⟨15291, by rfl⟩ (by norm_num))
theorem R40781 : Reach 40781 := rs (se 3 (by rfl) ⟨7646, by rfl⟩) (B 15293 (by norm_num) ⟨7646, by rfl⟩ (by norm_num))
theorem R40785 : Reach 40785 := rs (se 2 (by rfl) ⟨15294, by rfl⟩) (B 30589 (by norm_num) ⟨15294, by rfl⟩ (by norm_num))
theorem R40789 : Reach 40789 := rs (se 9 (by rfl) ⟨119, by rfl⟩) (B 239 (by norm_num) ⟨119, by rfl⟩ (by norm_num))
theorem R40793 : Reach 40793 := rs (se 2 (by rfl) ⟨15297, by rfl⟩) (B 30595 (by norm_num) ⟨15297, by rfl⟩ (by norm_num))
theorem R40797 : Reach 40797 := rs (se 3 (by rfl) ⟨7649, by rfl⟩) (B 15299 (by norm_num) ⟨7649, by rfl⟩ (by norm_num))
theorem R40801 : Reach 40801 := rs (se 2 (by rfl) ⟨15300, by rfl⟩) (B 30601 (by norm_num) ⟨15300, by rfl⟩ (by norm_num))
theorem R40805 : Reach 40805 := rs (se 4 (by rfl) ⟨3825, by rfl⟩) (B 7651 (by norm_num) ⟨3825, by rfl⟩ (by norm_num))
theorem R40809 : Reach 40809 := rs (se 2 (by rfl) ⟨15303, by rfl⟩) (B 30607 (by norm_num) ⟨15303, by rfl⟩ (by norm_num))
theorem R40813 : Reach 40813 := rs (se 3 (by rfl) ⟨7652, by rfl⟩) (B 15305 (by norm_num) ⟨7652, by rfl⟩ (by norm_num))
theorem R40817 : Reach 40817 := rs (se 2 (by rfl) ⟨15306, by rfl⟩) (B 30613 (by norm_num) ⟨15306, by rfl⟩ (by norm_num))
theorem R40821 : Reach 40821 := rs (se 5 (by rfl) ⟨1913, by rfl⟩) (B 3827 (by norm_num) ⟨1913, by rfl⟩ (by norm_num))
theorem R40825 : Reach 40825 := rs (se 2 (by rfl) ⟨15309, by rfl⟩) (B 30619 (by norm_num) ⟨15309, by rfl⟩ (by norm_num))
theorem R40829 : Reach 40829 := rs (se 3 (by rfl) ⟨7655, by rfl⟩) (B 15311 (by norm_num) ⟨7655, by rfl⟩ (by norm_num))
theorem R40833 : Reach 40833 := rs (se 2 (by rfl) ⟨15312, by rfl⟩) (B 30625 (by norm_num) ⟨15312, by rfl⟩ (by norm_num))
theorem R40837 : Reach 40837 := rs (se 4 (by rfl) ⟨3828, by rfl⟩) (B 7657 (by norm_num) ⟨3828, by rfl⟩ (by norm_num))
theorem R106373 : Reach 106373 := rs (se 4 (by rfl) ⟨9972, by rfl⟩) (B 19945 (by norm_num) ⟨9972, by rfl⟩ (by norm_num))
theorem R40841 : Reach 40841 := rs (se 2 (by rfl) ⟨15315, by rfl⟩) (B 30631 (by norm_num) ⟨15315, by rfl⟩ (by norm_num))
theorem R40845 : Reach 40845 := rs (se 3 (by rfl) ⟨7658, by rfl⟩) (B 15317 (by norm_num) ⟨7658, by rfl⟩ (by norm_num))
theorem R40849 : Reach 40849 := rs (se 2 (by rfl) ⟨15318, by rfl⟩) (B 30637 (by norm_num) ⟨15318, by rfl⟩ (by norm_num))
theorem R40853 : Reach 40853 := rs (se 6 (by rfl) ⟨957, by rfl⟩) (B 1915 (by norm_num) ⟨957, by rfl⟩ (by norm_num))
theorem R139157 : Reach 139157 := rs (se 6 (by rfl) ⟨3261, by rfl⟩) (B 6523 (by norm_num) ⟨3261, by rfl⟩ (by norm_num))
theorem R40857 : Reach 40857 := rs (se 2 (by rfl) ⟨15321, by rfl⟩) (B 30643 (by norm_num) ⟨15321, by rfl⟩ (by norm_num))
theorem R40861 : Reach 40861 := rs (se 3 (by rfl) ⟨7661, by rfl⟩) (B 15323 (by norm_num) ⟨7661, by rfl⟩ (by norm_num))
theorem R40865 : Reach 40865 := rs (se 2 (by rfl) ⟨15324, by rfl⟩) (B 30649 (by norm_num) ⟨15324, by rfl⟩ (by norm_num))
theorem R40869 : Reach 40869 := rs (se 4 (by rfl) ⟨3831, by rfl⟩) (B 7663 (by norm_num) ⟨3831, by rfl⟩ (by norm_num))
theorem R40873 : Reach 40873 := rs (se 2 (by rfl) ⟨15327, by rfl⟩) (B 30655 (by norm_num) ⟨15327, by rfl⟩ (by norm_num))
theorem R40877 : Reach 40877 := rs (se 3 (by rfl) ⟨7664, by rfl⟩) (B 15329 (by norm_num) ⟨7664, by rfl⟩ (by norm_num))
theorem R40881 : Reach 40881 := rs (se 2 (by rfl) ⟨15330, by rfl⟩) (B 30661 (by norm_num) ⟨15330, by rfl⟩ (by norm_num))
theorem R40885 : Reach 40885 := rs (se 5 (by rfl) ⟨1916, by rfl⟩) (B 3833 (by norm_num) ⟨1916, by rfl⟩ (by norm_num))
theorem R40889 : Reach 40889 := rs (se 2 (by rfl) ⟨15333, by rfl⟩) (B 30667 (by norm_num) ⟨15333, by rfl⟩ (by norm_num))
theorem R40893 : Reach 40893 := rs (se 3 (by rfl) ⟨7667, by rfl⟩) (B 15335 (by norm_num) ⟨7667, by rfl⟩ (by norm_num))
theorem R40897 : Reach 40897 := rs (se 2 (by rfl) ⟨15336, by rfl⟩) (B 30673 (by norm_num) ⟨15336, by rfl⟩ (by norm_num))
theorem R40901 : Reach 40901 := rs (se 4 (by rfl) ⟨3834, by rfl⟩) (B 7669 (by norm_num) ⟨3834, by rfl⟩ (by norm_num))
theorem R40905 : Reach 40905 := rs (se 2 (by rfl) ⟨15339, by rfl⟩) (B 30679 (by norm_num) ⟨15339, by rfl⟩ (by norm_num))
theorem R40909 : Reach 40909 := rs (se 3 (by rfl) ⟨7670, by rfl⟩) (B 15341 (by norm_num) ⟨7670, by rfl⟩ (by norm_num))
theorem R40913 : Reach 40913 := rs (se 2 (by rfl) ⟨15342, by rfl⟩) (B 30685 (by norm_num) ⟨15342, by rfl⟩ (by norm_num))
theorem R171989 : Reach 171989 := rs (se 7 (by rfl) ⟨2015, by rfl⟩) (B 4031 (by norm_num) ⟨2015, by rfl⟩ (by norm_num))
theorem R40917 : Reach 40917 := rs (se 7 (by rfl) ⟨479, by rfl⟩) (B 959 (by norm_num) ⟨479, by rfl⟩ (by norm_num))
theorem R40921 : Reach 40921 := rs (se 2 (by rfl) ⟨15345, by rfl⟩) (B 30691 (by norm_num) ⟨15345, by rfl⟩ (by norm_num))
theorem R40925 : Reach 40925 := rs (se 3 (by rfl) ⟨7673, by rfl⟩) (B 15347 (by norm_num) ⟨7673, by rfl⟩ (by norm_num))
theorem R40929 : Reach 40929 := rs (se 2 (by rfl) ⟨15348, by rfl⟩) (B 30697 (by norm_num) ⟨15348, by rfl⟩ (by norm_num))
theorem R40933 : Reach 40933 := rs (se 4 (by rfl) ⟨3837, by rfl⟩) (B 7675 (by norm_num) ⟨3837, by rfl⟩ (by norm_num))
theorem R40937 : Reach 40937 := rs (se 2 (by rfl) ⟨15351, by rfl⟩) (B 30703 (by norm_num) ⟨15351, by rfl⟩ (by norm_num))
theorem R40941 : Reach 40941 := rs (se 3 (by rfl) ⟨7676, by rfl⟩) (B 15353 (by norm_num) ⟨7676, by rfl⟩ (by norm_num))
theorem R40945 : Reach 40945 := rs (se 2 (by rfl) ⟨15354, by rfl⟩) (B 30709 (by norm_num) ⟨15354, by rfl⟩ (by norm_num))
theorem R40949 : Reach 40949 := rs (se 5 (by rfl) ⟨1919, by rfl⟩) (B 3839 (by norm_num) ⟨1919, by rfl⟩ (by norm_num))
theorem R40953 : Reach 40953 := rs (se 2 (by rfl) ⟨15357, by rfl⟩) (B 30715 (by norm_num) ⟨15357, by rfl⟩ (by norm_num))
theorem R40957 : Reach 40957 := rs (se 3 (by rfl) ⟨7679, by rfl⟩) (B 15359 (by norm_num) ⟨7679, by rfl⟩ (by norm_num))
theorem R40961 : Reach 40961 := rs (se 2 (by rfl) ⟨15360, by rfl⟩) (B 30721 (by norm_num) ⟨15360, by rfl⟩ (by norm_num))
theorem R40965 : Reach 40965 := rs (se 4 (by rfl) ⟨3840, by rfl⟩) (B 7681 (by norm_num) ⟨3840, by rfl⟩ (by norm_num))
theorem R40969 : Reach 40969 := rs (se 2 (by rfl) ⟨15363, by rfl⟩) (B 30727 (by norm_num) ⟨15363, by rfl⟩ (by norm_num))
theorem R40973 : Reach 40973 := rs (se 3 (by rfl) ⟨7682, by rfl⟩) (B 15365 (by norm_num) ⟨7682, by rfl⟩ (by norm_num))
theorem R40977 : Reach 40977 := rs (se 2 (by rfl) ⟨15366, by rfl⟩) (B 30733 (by norm_num) ⟨15366, by rfl⟩ (by norm_num))
theorem R40981 : Reach 40981 := rs (se 6 (by rfl) ⟨960, by rfl⟩) (B 1921 (by norm_num) ⟨960, by rfl⟩ (by norm_num))
theorem R40985 : Reach 40985 := rs (se 2 (by rfl) ⟨15369, by rfl⟩) (B 30739 (by norm_num) ⟨15369, by rfl⟩ (by norm_num))
theorem R40989 : Reach 40989 := rs (se 3 (by rfl) ⟨7685, by rfl⟩) (B 15371 (by norm_num) ⟨7685, by rfl⟩ (by norm_num))
theorem R40993 : Reach 40993 := rs (se 2 (by rfl) ⟨15372, by rfl⟩) (B 30745 (by norm_num) ⟨15372, by rfl⟩ (by norm_num))
theorem R40997 : Reach 40997 := rs (se 4 (by rfl) ⟨3843, by rfl⟩) (B 7687 (by norm_num) ⟨3843, by rfl⟩ (by norm_num))
theorem R41001 : Reach 41001 := rs (se 2 (by rfl) ⟨15375, by rfl⟩) (B 30751 (by norm_num) ⟨15375, by rfl⟩ (by norm_num))
theorem R41005 : Reach 41005 := rs (se 3 (by rfl) ⟨7688, by rfl⟩) (B 15377 (by norm_num) ⟨7688, by rfl⟩ (by norm_num))
theorem R41009 : Reach 41009 := rs (se 2 (by rfl) ⟨15378, by rfl⟩) (B 30757 (by norm_num) ⟨15378, by rfl⟩ (by norm_num))
theorem R41013 : Reach 41013 := rs (se 5 (by rfl) ⟨1922, by rfl⟩) (B 3845 (by norm_num) ⟨1922, by rfl⟩ (by norm_num))
theorem R41017 : Reach 41017 := rs (se 2 (by rfl) ⟨15381, by rfl⟩) (B 30763 (by norm_num) ⟨15381, by rfl⟩ (by norm_num))
theorem R41021 : Reach 41021 := rs (se 3 (by rfl) ⟨7691, by rfl⟩) (B 15383 (by norm_num) ⟨7691, by rfl⟩ (by norm_num))
theorem R41025 : Reach 41025 := rs (se 2 (by rfl) ⟨15384, by rfl⟩) (B 30769 (by norm_num) ⟨15384, by rfl⟩ (by norm_num))
theorem R106565 : Reach 106565 := rs (se 4 (by rfl) ⟨9990, by rfl⟩) (B 19981 (by norm_num) ⟨9990, by rfl⟩ (by norm_num))
theorem R41029 : Reach 41029 := rs (se 4 (by rfl) ⟨3846, by rfl⟩) (B 7693 (by norm_num) ⟨3846, by rfl⟩ (by norm_num))
theorem R41033 : Reach 41033 := rs (se 2 (by rfl) ⟨15387, by rfl⟩) (B 30775 (by norm_num) ⟨15387, by rfl⟩ (by norm_num))
theorem R41037 : Reach 41037 := rs (se 3 (by rfl) ⟨7694, by rfl⟩) (B 15389 (by norm_num) ⟨7694, by rfl⟩ (by norm_num))
theorem R41041 : Reach 41041 := rs (se 2 (by rfl) ⟨15390, by rfl⟩) (B 30781 (by norm_num) ⟨15390, by rfl⟩ (by norm_num))
theorem R41045 : Reach 41045 := rs (se 8 (by rfl) ⟨240, by rfl⟩) (B 481 (by norm_num) ⟨240, by rfl⟩ (by norm_num))
theorem R41049 : Reach 41049 := rs (se 2 (by rfl) ⟨15393, by rfl⟩) (B 30787 (by norm_num) ⟨15393, by rfl⟩ (by norm_num))
theorem R41053 : Reach 41053 := rs (se 3 (by rfl) ⟨7697, by rfl⟩) (B 15395 (by norm_num) ⟨7697, by rfl⟩ (by norm_num))
theorem R41057 : Reach 41057 := rs (se 2 (by rfl) ⟨15396, by rfl⟩) (B 30793 (by norm_num) ⟨15396, by rfl⟩ (by norm_num))
theorem R41061 : Reach 41061 := rs (se 4 (by rfl) ⟨3849, by rfl⟩) (B 7699 (by norm_num) ⟨3849, by rfl⟩ (by norm_num))
theorem R41065 : Reach 41065 := rs (se 2 (by rfl) ⟨15399, by rfl⟩) (B 30799 (by norm_num) ⟨15399, by rfl⟩ (by norm_num))
theorem R41069 : Reach 41069 := rs (se 3 (by rfl) ⟨7700, by rfl⟩) (B 15401 (by norm_num) ⟨7700, by rfl⟩ (by norm_num))
theorem R41073 : Reach 41073 := rs (se 2 (by rfl) ⟨15402, by rfl⟩) (B 30805 (by norm_num) ⟨15402, by rfl⟩ (by norm_num))
theorem R41077 : Reach 41077 := rs (se 5 (by rfl) ⟨1925, by rfl⟩) (B 3851 (by norm_num) ⟨1925, by rfl⟩ (by norm_num))
theorem R41081 : Reach 41081 := rs (se 2 (by rfl) ⟨15405, by rfl⟩) (B 30811 (by norm_num) ⟨15405, by rfl⟩ (by norm_num))
theorem R41085 : Reach 41085 := rs (se 3 (by rfl) ⟨7703, by rfl⟩) (B 15407 (by norm_num) ⟨7703, by rfl⟩ (by norm_num))
theorem R41089 : Reach 41089 := rs (se 2 (by rfl) ⟨15408, by rfl⟩) (B 30817 (by norm_num) ⟨15408, by rfl⟩ (by norm_num))
theorem R41093 : Reach 41093 := rs (se 4 (by rfl) ⟨3852, by rfl⟩) (B 7705 (by norm_num) ⟨3852, by rfl⟩ (by norm_num))
theorem R41097 : Reach 41097 := rs (se 2 (by rfl) ⟨15411, by rfl⟩) (B 30823 (by norm_num) ⟨15411, by rfl⟩ (by norm_num))
theorem R41101 : Reach 41101 := rs (se 3 (by rfl) ⟨7706, by rfl⟩) (B 15413 (by norm_num) ⟨7706, by rfl⟩ (by norm_num))
theorem R41105 : Reach 41105 := rs (se 2 (by rfl) ⟨15414, by rfl⟩) (B 30829 (by norm_num) ⟨15414, by rfl⟩ (by norm_num))
theorem R41109 : Reach 41109 := rs (se 6 (by rfl) ⟨963, by rfl⟩) (B 1927 (by norm_num) ⟨963, by rfl⟩ (by norm_num))
theorem R41113 : Reach 41113 := rs (se 2 (by rfl) ⟨15417, by rfl⟩) (B 30835 (by norm_num) ⟨15417, by rfl⟩ (by norm_num))
theorem R41117 : Reach 41117 := rs (se 3 (by rfl) ⟨7709, by rfl⟩) (B 15419 (by norm_num) ⟨7709, by rfl⟩ (by norm_num))
theorem R41121 : Reach 41121 := rs (se 2 (by rfl) ⟨15420, by rfl⟩) (B 30841 (by norm_num) ⟨15420, by rfl⟩ (by norm_num))
theorem R41125 : Reach 41125 := rs (se 4 (by rfl) ⟨3855, by rfl⟩) (B 7711 (by norm_num) ⟨3855, by rfl⟩ (by norm_num))
theorem R41129 : Reach 41129 := rs (se 2 (by rfl) ⟨15423, by rfl⟩) (B 30847 (by norm_num) ⟨15423, by rfl⟩ (by norm_num))
theorem R41133 : Reach 41133 := rs (se 3 (by rfl) ⟨7712, by rfl⟩) (B 15425 (by norm_num) ⟨7712, by rfl⟩ (by norm_num))
theorem R41137 : Reach 41137 := rs (se 2 (by rfl) ⟨15426, by rfl⟩) (B 30853 (by norm_num) ⟨15426, by rfl⟩ (by norm_num))
theorem R41141 : Reach 41141 := rs (se 5 (by rfl) ⟨1928, by rfl⟩) (B 3857 (by norm_num) ⟨1928, by rfl⟩ (by norm_num))
theorem R139445 : Reach 139445 := rs (se 5 (by rfl) ⟨6536, by rfl⟩) (B 13073 (by norm_num) ⟨6536, by rfl⟩ (by norm_num))
theorem R41145 : Reach 41145 := rs (se 2 (by rfl) ⟨15429, by rfl⟩) (B 30859 (by norm_num) ⟨15429, by rfl⟩ (by norm_num))
theorem R41149 : Reach 41149 := rs (se 3 (by rfl) ⟨7715, by rfl⟩) (B 15431 (by norm_num) ⟨7715, by rfl⟩ (by norm_num))
theorem R41153 : Reach 41153 := rs (se 2 (by rfl) ⟨15432, by rfl⟩) (B 30865 (by norm_num) ⟨15432, by rfl⟩ (by norm_num))
theorem R41157 : Reach 41157 := rs (se 4 (by rfl) ⟨3858, by rfl⟩) (B 7717 (by norm_num) ⟨3858, by rfl⟩ (by norm_num))
theorem R41161 : Reach 41161 := rs (se 2 (by rfl) ⟨15435, by rfl⟩) (B 30871 (by norm_num) ⟨15435, by rfl⟩ (by norm_num))
theorem R41165 : Reach 41165 := rs (se 3 (by rfl) ⟨7718, by rfl⟩) (B 15437 (by norm_num) ⟨7718, by rfl⟩ (by norm_num))
theorem R41169 : Reach 41169 := rs (se 2 (by rfl) ⟨15438, by rfl⟩) (B 30877 (by norm_num) ⟨15438, by rfl⟩ (by norm_num))
theorem R41173 : Reach 41173 := rs (se 7 (by rfl) ⟨482, by rfl⟩) (B 965 (by norm_num) ⟨482, by rfl⟩ (by norm_num))
theorem R41177 : Reach 41177 := rs (se 2 (by rfl) ⟨15441, by rfl⟩) (B 30883 (by norm_num) ⟨15441, by rfl⟩ (by norm_num))
theorem R41181 : Reach 41181 := rs (se 3 (by rfl) ⟨7721, by rfl⟩) (B 15443 (by norm_num) ⟨7721, by rfl⟩ (by norm_num))
theorem R41185 : Reach 41185 := rs (se 2 (by rfl) ⟨15444, by rfl⟩) (B 30889 (by norm_num) ⟨15444, by rfl⟩ (by norm_num))
theorem R41189 : Reach 41189 := rs (se 4 (by rfl) ⟨3861, by rfl⟩) (B 7723 (by norm_num) ⟨3861, by rfl⟩ (by norm_num))
theorem R41193 : Reach 41193 := rs (se 2 (by rfl) ⟨15447, by rfl⟩) (B 30895 (by norm_num) ⟨15447, by rfl⟩ (by norm_num))
theorem R41197 : Reach 41197 := rs (se 3 (by rfl) ⟨7724, by rfl⟩) (B 15449 (by norm_num) ⟨7724, by rfl⟩ (by norm_num))
theorem R41201 : Reach 41201 := rs (se 2 (by rfl) ⟨15450, by rfl⟩) (B 30901 (by norm_num) ⟨15450, by rfl⟩ (by norm_num))
theorem R41205 : Reach 41205 := rs (se 5 (by rfl) ⟨1931, by rfl⟩) (B 3863 (by norm_num) ⟨1931, by rfl⟩ (by norm_num))
theorem R41209 : Reach 41209 := rs (se 2 (by rfl) ⟨15453, by rfl⟩) (B 30907 (by norm_num) ⟨15453, by rfl⟩ (by norm_num))
theorem R41213 : Reach 41213 := rs (se 3 (by rfl) ⟨7727, by rfl⟩) (B 15455 (by norm_num) ⟨7727, by rfl⟩ (by norm_num))
theorem R41217 : Reach 41217 := rs (se 2 (by rfl) ⟨15456, by rfl⟩) (B 30913 (by norm_num) ⟨15456, by rfl⟩ (by norm_num))
theorem R41221 : Reach 41221 := rs (se 4 (by rfl) ⟨3864, by rfl⟩) (B 7729 (by norm_num) ⟨3864, by rfl⟩ (by norm_num))
theorem R41225 : Reach 41225 := rs (se 2 (by rfl) ⟨15459, by rfl⟩) (B 30919 (by norm_num) ⟨15459, by rfl⟩ (by norm_num))
theorem R41229 : Reach 41229 := rs (se 3 (by rfl) ⟨7730, by rfl⟩) (B 15461 (by norm_num) ⟨7730, by rfl⟩ (by norm_num))
theorem R41233 : Reach 41233 := rs (se 2 (by rfl) ⟨15462, by rfl⟩) (B 30925 (by norm_num) ⟨15462, by rfl⟩ (by norm_num))
theorem R41237 : Reach 41237 := rs (se 6 (by rfl) ⟨966, by rfl⟩) (B 1933 (by norm_num) ⟨966, by rfl⟩ (by norm_num))
theorem R41241 : Reach 41241 := rs (se 2 (by rfl) ⟨15465, by rfl⟩) (B 30931 (by norm_num) ⟨15465, by rfl⟩ (by norm_num))
theorem R41245 : Reach 41245 := rs (se 3 (by rfl) ⟨7733, by rfl⟩) (B 15467 (by norm_num) ⟨7733, by rfl⟩ (by norm_num))
theorem R41249 : Reach 41249 := rs (se 2 (by rfl) ⟨15468, by rfl⟩) (B 30937 (by norm_num) ⟨15468, by rfl⟩ (by norm_num))
theorem R41253 : Reach 41253 := rs (se 4 (by rfl) ⟨3867, by rfl⟩) (B 7735 (by norm_num) ⟨3867, by rfl⟩ (by norm_num))
theorem R41257 : Reach 41257 := rs (se 2 (by rfl) ⟨15471, by rfl⟩) (B 30943 (by norm_num) ⟨15471, by rfl⟩ (by norm_num))
theorem R41261 : Reach 41261 := rs (se 3 (by rfl) ⟨7736, by rfl⟩) (B 15473 (by norm_num) ⟨7736, by rfl⟩ (by norm_num))
theorem R41265 : Reach 41265 := rs (se 2 (by rfl) ⟨15474, by rfl⟩) (B 30949 (by norm_num) ⟨15474, by rfl⟩ (by norm_num))
theorem R41269 : Reach 41269 := rs (se 5 (by rfl) ⟨1934, by rfl⟩) (B 3869 (by norm_num) ⟨1934, by rfl⟩ (by norm_num))
theorem R41273 : Reach 41273 := rs (se 2 (by rfl) ⟨15477, by rfl⟩) (B 30955 (by norm_num) ⟨15477, by rfl⟩ (by norm_num))
theorem R41277 : Reach 41277 := rs (se 3 (by rfl) ⟨7739, by rfl⟩) (B 15479 (by norm_num) ⟨7739, by rfl⟩ (by norm_num))
theorem R41281 : Reach 41281 := rs (se 2 (by rfl) ⟨15480, by rfl⟩) (B 30961 (by norm_num) ⟨15480, by rfl⟩ (by norm_num))
theorem R41285 : Reach 41285 := rs (se 4 (by rfl) ⟨3870, by rfl⟩) (B 7741 (by norm_num) ⟨3870, by rfl⟩ (by norm_num))
theorem R139589 : Reach 139589 := rs (se 4 (by rfl) ⟨13086, by rfl⟩) (B 26173 (by norm_num) ⟨13086, by rfl⟩ (by norm_num))
theorem R41289 : Reach 41289 := rs (se 2 (by rfl) ⟨15483, by rfl⟩) (B 30967 (by norm_num) ⟨15483, by rfl⟩ (by norm_num))
theorem R41293 : Reach 41293 := rs (se 3 (by rfl) ⟨7742, by rfl⟩) (B 15485 (by norm_num) ⟨7742, by rfl⟩ (by norm_num))
theorem R41297 : Reach 41297 := rs (se 2 (by rfl) ⟨15486, by rfl⟩) (B 30973 (by norm_num) ⟨15486, by rfl⟩ (by norm_num))
theorem R41301 : Reach 41301 := rs (se 10 (by rfl) ⟨60, by rfl⟩) (B 121 (by norm_num) ⟨60, by rfl⟩ (by norm_num))
theorem R41305 : Reach 41305 := rs (se 2 (by rfl) ⟨15489, by rfl⟩) (B 30979 (by norm_num) ⟨15489, by rfl⟩ (by norm_num))
theorem R41309 : Reach 41309 := rs (se 3 (by rfl) ⟨7745, by rfl⟩) (B 15491 (by norm_num) ⟨7745, by rfl⟩ (by norm_num))
theorem R41313 : Reach 41313 := rs (se 2 (by rfl) ⟨15492, by rfl⟩) (B 30985 (by norm_num) ⟨15492, by rfl⟩ (by norm_num))
theorem R41317 : Reach 41317 := rs (se 4 (by rfl) ⟨3873, by rfl⟩) (B 7747 (by norm_num) ⟨3873, by rfl⟩ (by norm_num))
theorem R41321 : Reach 41321 := rs (se 2 (by rfl) ⟨15495, by rfl⟩) (B 30991 (by norm_num) ⟨15495, by rfl⟩ (by norm_num))
theorem R41325 : Reach 41325 := rs (se 3 (by rfl) ⟨7748, by rfl⟩) (B 15497 (by norm_num) ⟨7748, by rfl⟩ (by norm_num))
theorem R41329 : Reach 41329 := rs (se 2 (by rfl) ⟨15498, by rfl⟩) (B 30997 (by norm_num) ⟨15498, by rfl⟩ (by norm_num))
theorem R41333 : Reach 41333 := rs (se 5 (by rfl) ⟨1937, by rfl⟩) (B 3875 (by norm_num) ⟨1937, by rfl⟩ (by norm_num))
theorem R41337 : Reach 41337 := rs (se 2 (by rfl) ⟨15501, by rfl⟩) (B 31003 (by norm_num) ⟨15501, by rfl⟩ (by norm_num))
theorem R41341 : Reach 41341 := rs (se 3 (by rfl) ⟨7751, by rfl⟩) (B 15503 (by norm_num) ⟨7751, by rfl⟩ (by norm_num))
theorem R41345 : Reach 41345 := rs (se 2 (by rfl) ⟨15504, by rfl⟩) (B 31009 (by norm_num) ⟨15504, by rfl⟩ (by norm_num))
theorem R41349 : Reach 41349 := rs (se 4 (by rfl) ⟨3876, by rfl⟩) (B 7753 (by norm_num) ⟨3876, by rfl⟩ (by norm_num))
theorem R41353 : Reach 41353 := rs (se 2 (by rfl) ⟨15507, by rfl⟩) (B 31015 (by norm_num) ⟨15507, by rfl⟩ (by norm_num))
theorem R41357 : Reach 41357 := rs (se 3 (by rfl) ⟨7754, by rfl⟩) (B 15509 (by norm_num) ⟨7754, by rfl⟩ (by norm_num))
theorem R41361 : Reach 41361 := rs (se 2 (by rfl) ⟨15510, by rfl⟩) (B 31021 (by norm_num) ⟨15510, by rfl⟩ (by norm_num))
theorem R41365 : Reach 41365 := rs (se 6 (by rfl) ⟨969, by rfl⟩) (B 1939 (by norm_num) ⟨969, by rfl⟩ (by norm_num))
theorem R41369 : Reach 41369 := rs (se 2 (by rfl) ⟨15513, by rfl⟩) (B 31027 (by norm_num) ⟨15513, by rfl⟩ (by norm_num))
theorem R41373 : Reach 41373 := rs (se 3 (by rfl) ⟨7757, by rfl⟩) (B 15515 (by norm_num) ⟨7757, by rfl⟩ (by norm_num))
theorem R41377 : Reach 41377 := rs (se 2 (by rfl) ⟨15516, by rfl⟩) (B 31033 (by norm_num) ⟨15516, by rfl⟩ (by norm_num))
theorem R41381 : Reach 41381 := rs (se 4 (by rfl) ⟨3879, by rfl⟩) (B 7759 (by norm_num) ⟨3879, by rfl⟩ (by norm_num))
theorem R41385 : Reach 41385 := rs (se 2 (by rfl) ⟨15519, by rfl⟩) (B 31039 (by norm_num) ⟨15519, by rfl⟩ (by norm_num))
theorem R41389 : Reach 41389 := rs (se 3 (by rfl) ⟨7760, by rfl⟩) (B 15521 (by norm_num) ⟨7760, by rfl⟩ (by norm_num))
theorem R41393 : Reach 41393 := rs (se 2 (by rfl) ⟨15522, by rfl⟩) (B 31045 (by norm_num) ⟨15522, by rfl⟩ (by norm_num))
theorem R41397 : Reach 41397 := rs (se 5 (by rfl) ⟨1940, by rfl⟩) (B 3881 (by norm_num) ⟨1940, by rfl⟩ (by norm_num))
theorem R41401 : Reach 41401 := rs (se 2 (by rfl) ⟨15525, by rfl⟩) (B 31051 (by norm_num) ⟨15525, by rfl⟩ (by norm_num))
theorem R41405 : Reach 41405 := rs (se 3 (by rfl) ⟨7763, by rfl⟩) (B 15527 (by norm_num) ⟨7763, by rfl⟩ (by norm_num))
theorem R41409 : Reach 41409 := rs (se 2 (by rfl) ⟨15528, by rfl⟩) (B 31057 (by norm_num) ⟨15528, by rfl⟩ (by norm_num))
theorem R205253 : Reach 205253 := rs (se 4 (by rfl) ⟨19242, by rfl⟩) (B 38485 (by norm_num) ⟨19242, by rfl⟩ (by norm_num))
theorem R41413 : Reach 41413 := rs (se 4 (by rfl) ⟨3882, by rfl⟩) (B 7765 (by norm_num) ⟨3882, by rfl⟩ (by norm_num))
theorem R41417 : Reach 41417 := rs (se 2 (by rfl) ⟨15531, by rfl⟩) (B 31063 (by norm_num) ⟨15531, by rfl⟩ (by norm_num))
theorem R41421 : Reach 41421 := rs (se 3 (by rfl) ⟨7766, by rfl⟩) (B 15533 (by norm_num) ⟨7766, by rfl⟩ (by norm_num))
theorem R41425 : Reach 41425 := rs (se 2 (by rfl) ⟨15534, by rfl⟩) (B 31069 (by norm_num) ⟨15534, by rfl⟩ (by norm_num))
theorem R41429 : Reach 41429 := rs (se 7 (by rfl) ⟨485, by rfl⟩) (B 971 (by norm_num) ⟨485, by rfl⟩ (by norm_num))
theorem R41433 : Reach 41433 := rs (se 2 (by rfl) ⟨15537, by rfl⟩) (B 31075 (by norm_num) ⟨15537, by rfl⟩ (by norm_num))
theorem R41437 : Reach 41437 := rs (se 3 (by rfl) ⟨7769, by rfl⟩) (B 15539 (by norm_num) ⟨7769, by rfl⟩ (by norm_num))
theorem R41441 : Reach 41441 := rs (se 2 (by rfl) ⟨15540, by rfl⟩) (B 31081 (by norm_num) ⟨15540, by rfl⟩ (by norm_num))
theorem R41445 : Reach 41445 := rs (se 4 (by rfl) ⟨3885, by rfl⟩) (B 7771 (by norm_num) ⟨3885, by rfl⟩ (by norm_num))
theorem R41449 : Reach 41449 := rs (se 2 (by rfl) ⟨15543, by rfl⟩) (B 31087 (by norm_num) ⟨15543, by rfl⟩ (by norm_num))
theorem R41453 : Reach 41453 := rs (se 3 (by rfl) ⟨7772, by rfl⟩) (B 15545 (by norm_num) ⟨7772, by rfl⟩ (by norm_num))
theorem R41457 : Reach 41457 := rs (se 2 (by rfl) ⟨15546, by rfl⟩) (B 31093 (by norm_num) ⟨15546, by rfl⟩ (by norm_num))
theorem R41461 : Reach 41461 := rs (se 5 (by rfl) ⟨1943, by rfl⟩) (B 3887 (by norm_num) ⟨1943, by rfl⟩ (by norm_num))
theorem R41465 : Reach 41465 := rs (se 2 (by rfl) ⟨15549, by rfl⟩) (B 31099 (by norm_num) ⟨15549, by rfl⟩ (by norm_num))
theorem R41469 : Reach 41469 := rs (se 3 (by rfl) ⟨7775, by rfl⟩) (B 15551 (by norm_num) ⟨7775, by rfl⟩ (by norm_num))
theorem R41473 : Reach 41473 := rs (se 2 (by rfl) ⟨15552, by rfl⟩) (B 31105 (by norm_num) ⟨15552, by rfl⟩ (by norm_num))
theorem R41477 : Reach 41477 := rs (se 4 (by rfl) ⟨3888, by rfl⟩) (B 7777 (by norm_num) ⟨3888, by rfl⟩ (by norm_num))
theorem R41481 : Reach 41481 := rs (se 2 (by rfl) ⟨15555, by rfl⟩) (B 31111 (by norm_num) ⟨15555, by rfl⟩ (by norm_num))
theorem R41485 : Reach 41485 := rs (se 3 (by rfl) ⟨7778, by rfl⟩) (B 15557 (by norm_num) ⟨7778, by rfl⟩ (by norm_num))
theorem R41489 : Reach 41489 := rs (se 2 (by rfl) ⟨15558, by rfl⟩) (B 31117 (by norm_num) ⟨15558, by rfl⟩ (by norm_num))
theorem R41493 : Reach 41493 := rs (se 6 (by rfl) ⟨972, by rfl⟩) (B 1945 (by norm_num) ⟨972, by rfl⟩ (by norm_num))
theorem R41497 : Reach 41497 := rs (se 2 (by rfl) ⟨15561, by rfl⟩) (B 31123 (by norm_num) ⟨15561, by rfl⟩ (by norm_num))
theorem R41501 : Reach 41501 := rs (se 3 (by rfl) ⟨7781, by rfl⟩) (B 15563 (by norm_num) ⟨7781, by rfl⟩ (by norm_num))
theorem R41505 : Reach 41505 := rs (se 2 (by rfl) ⟨15564, by rfl⟩) (B 31129 (by norm_num) ⟨15564, by rfl⟩ (by norm_num))
theorem R41509 : Reach 41509 := rs (se 4 (by rfl) ⟨3891, by rfl⟩) (B 7783 (by norm_num) ⟨3891, by rfl⟩ (by norm_num))
theorem R41513 : Reach 41513 := rs (se 2 (by rfl) ⟨15567, by rfl⟩) (B 31135 (by norm_num) ⟨15567, by rfl⟩ (by norm_num))
theorem R41517 : Reach 41517 := rs (se 3 (by rfl) ⟨7784, by rfl⟩) (B 15569 (by norm_num) ⟨7784, by rfl⟩ (by norm_num))
theorem R41521 : Reach 41521 := rs (se 2 (by rfl) ⟨15570, by rfl⟩) (B 31141 (by norm_num) ⟨15570, by rfl⟩ (by norm_num))
theorem R41525 : Reach 41525 := rs (se 5 (by rfl) ⟨1946, by rfl⟩) (B 3893 (by norm_num) ⟨1946, by rfl⟩ (by norm_num))
theorem R41529 : Reach 41529 := rs (se 2 (by rfl) ⟨15573, by rfl⟩) (B 31147 (by norm_num) ⟨15573, by rfl⟩ (by norm_num))
theorem R41533 : Reach 41533 := rs (se 3 (by rfl) ⟨7787, by rfl⟩) (B 15575 (by norm_num) ⟨7787, by rfl⟩ (by norm_num))
theorem R41537 : Reach 41537 := rs (se 2 (by rfl) ⟨15576, by rfl⟩) (B 31153 (by norm_num) ⟨15576, by rfl⟩ (by norm_num))
theorem R41541 : Reach 41541 := rs (se 4 (by rfl) ⟨3894, by rfl⟩) (B 7789 (by norm_num) ⟨3894, by rfl⟩ (by norm_num))
theorem R41545 : Reach 41545 := rs (se 2 (by rfl) ⟨15579, by rfl⟩) (B 31159 (by norm_num) ⟨15579, by rfl⟩ (by norm_num))
theorem R41549 : Reach 41549 := rs (se 3 (by rfl) ⟨7790, by rfl⟩) (B 15581 (by norm_num) ⟨7790, by rfl⟩ (by norm_num))
theorem R41553 : Reach 41553 := rs (se 2 (by rfl) ⟨15582, by rfl⟩) (B 31165 (by norm_num) ⟨15582, by rfl⟩ (by norm_num))
theorem R41557 : Reach 41557 := rs (se 8 (by rfl) ⟨243, by rfl⟩) (B 487 (by norm_num) ⟨243, by rfl⟩ (by norm_num))
theorem R41561 : Reach 41561 := rs (se 2 (by rfl) ⟨15585, by rfl⟩) (B 31171 (by norm_num) ⟨15585, by rfl⟩ (by norm_num))
theorem R41565 : Reach 41565 := rs (se 3 (by rfl) ⟨7793, by rfl⟩) (B 15587 (by norm_num) ⟨7793, by rfl⟩ (by norm_num))
theorem R41569 : Reach 41569 := rs (se 2 (by rfl) ⟨15588, by rfl⟩) (B 31177 (by norm_num) ⟨15588, by rfl⟩ (by norm_num))
theorem R41573 : Reach 41573 := rs (se 4 (by rfl) ⟨3897, by rfl⟩) (B 7795 (by norm_num) ⟨3897, by rfl⟩ (by norm_num))
theorem R41577 : Reach 41577 := rs (se 2 (by rfl) ⟨15591, by rfl⟩) (B 31183 (by norm_num) ⟨15591, by rfl⟩ (by norm_num))
theorem R41581 : Reach 41581 := rs (se 3 (by rfl) ⟨7796, by rfl⟩) (B 15593 (by norm_num) ⟨7796, by rfl⟩ (by norm_num))
theorem R41585 : Reach 41585 := rs (se 2 (by rfl) ⟨15594, by rfl⟩) (B 31189 (by norm_num) ⟨15594, by rfl⟩ (by norm_num))
theorem R41589 : Reach 41589 := rs (se 5 (by rfl) ⟨1949, by rfl⟩) (B 3899 (by norm_num) ⟨1949, by rfl⟩ (by norm_num))
theorem R41593 : Reach 41593 := rs (se 2 (by rfl) ⟨15597, by rfl⟩) (B 31195 (by norm_num) ⟨15597, by rfl⟩ (by norm_num))
theorem R41597 : Reach 41597 := rs (se 3 (by rfl) ⟨7799, by rfl⟩) (B 15599 (by norm_num) ⟨7799, by rfl⟩ (by norm_num))
theorem R41601 : Reach 41601 := rs (se 2 (by rfl) ⟨15600, by rfl⟩) (B 31201 (by norm_num) ⟨15600, by rfl⟩ (by norm_num))
theorem R139909 : Reach 139909 := rs (se 4 (by rfl) ⟨13116, by rfl⟩) (B 26233 (by norm_num) ⟨13116, by rfl⟩ (by norm_num))
theorem R41605 : Reach 41605 := rs (se 4 (by rfl) ⟨3900, by rfl⟩) (B 7801 (by norm_num) ⟨3900, by rfl⟩ (by norm_num))
theorem R41609 : Reach 41609 := rs (se 2 (by rfl) ⟨15603, by rfl⟩) (B 31207 (by norm_num) ⟨15603, by rfl⟩ (by norm_num))
theorem R41613 : Reach 41613 := rs (se 3 (by rfl) ⟨7802, by rfl⟩) (B 15605 (by norm_num) ⟨7802, by rfl⟩ (by norm_num))
theorem R41617 : Reach 41617 := rs (se 2 (by rfl) ⟨15606, by rfl⟩) (B 31213 (by norm_num) ⟨15606, by rfl⟩ (by norm_num))
theorem R41621 : Reach 41621 := rs (se 6 (by rfl) ⟨975, by rfl⟩) (B 1951 (by norm_num) ⟨975, by rfl⟩ (by norm_num))
theorem R41625 : Reach 41625 := rs (se 2 (by rfl) ⟨15609, by rfl⟩) (B 31219 (by norm_num) ⟨15609, by rfl⟩ (by norm_num))
theorem R41629 : Reach 41629 := rs (se 3 (by rfl) ⟨7805, by rfl⟩) (B 15611 (by norm_num) ⟨7805, by rfl⟩ (by norm_num))
theorem R41633 : Reach 41633 := rs (se 2 (by rfl) ⟨15612, by rfl⟩) (B 31225 (by norm_num) ⟨15612, by rfl⟩ (by norm_num))
theorem R41637 : Reach 41637 := rs (se 4 (by rfl) ⟨3903, by rfl⟩) (B 7807 (by norm_num) ⟨3903, by rfl⟩ (by norm_num))
theorem R41641 : Reach 41641 := rs (se 2 (by rfl) ⟨15615, by rfl⟩) (B 31231 (by norm_num) ⟨15615, by rfl⟩ (by norm_num))
theorem R41645 : Reach 41645 := rs (se 3 (by rfl) ⟨7808, by rfl⟩) (B 15617 (by norm_num) ⟨7808, by rfl⟩ (by norm_num))
theorem R41649 : Reach 41649 := rs (se 2 (by rfl) ⟨15618, by rfl⟩) (B 31237 (by norm_num) ⟨15618, by rfl⟩ (by norm_num))
theorem R107189 : Reach 107189 := rs (se 5 (by rfl) ⟨5024, by rfl⟩) (B 10049 (by norm_num) ⟨5024, by rfl⟩ (by norm_num))
theorem R41653 : Reach 41653 := rs (se 5 (by rfl) ⟨1952, by rfl⟩) (B 3905 (by norm_num) ⟨1952, by rfl⟩ (by norm_num))
theorem R41657 : Reach 41657 := rs (se 2 (by rfl) ⟨15621, by rfl⟩) (B 31243 (by norm_num) ⟨15621, by rfl⟩ (by norm_num))
theorem R41661 : Reach 41661 := rs (se 3 (by rfl) ⟨7811, by rfl⟩) (B 15623 (by norm_num) ⟨7811, by rfl⟩ (by norm_num))
theorem R41665 : Reach 41665 := rs (se 2 (by rfl) ⟨15624, by rfl⟩) (B 31249 (by norm_num) ⟨15624, by rfl⟩ (by norm_num))
theorem R41669 : Reach 41669 := rs (se 4 (by rfl) ⟨3906, by rfl⟩) (B 7813 (by norm_num) ⟨3906, by rfl⟩ (by norm_num))
theorem R41673 : Reach 41673 := rs (se 2 (by rfl) ⟨15627, by rfl⟩) (B 31255 (by norm_num) ⟨15627, by rfl⟩ (by norm_num))
theorem R41677 : Reach 41677 := rs (se 3 (by rfl) ⟨7814, by rfl⟩) (B 15629 (by norm_num) ⟨7814, by rfl⟩ (by norm_num))
theorem R41681 : Reach 41681 := rs (se 2 (by rfl) ⟨15630, by rfl⟩) (B 31261 (by norm_num) ⟨15630, by rfl⟩ (by norm_num))
theorem R41685 : Reach 41685 := rs (se 7 (by rfl) ⟨488, by rfl⟩) (B 977 (by norm_num) ⟨488, by rfl⟩ (by norm_num))
theorem R41689 : Reach 41689 := rs (se 2 (by rfl) ⟨15633, by rfl⟩) (B 31267 (by norm_num) ⟨15633, by rfl⟩ (by norm_num))
theorem R74461 : Reach 74461 := rs (se 3 (by rfl) ⟨13961, by rfl⟩) (B 27923 (by norm_num) ⟨13961, by rfl⟩ (by norm_num))
theorem R41693 : Reach 41693 := rs (se 3 (by rfl) ⟨7817, by rfl⟩) (B 15635 (by norm_num) ⟨7817, by rfl⟩ (by norm_num))
theorem R41697 : Reach 41697 := rs (se 2 (by rfl) ⟨15636, by rfl⟩) (B 31273 (by norm_num) ⟨15636, by rfl⟩ (by norm_num))
theorem R41701 : Reach 41701 := rs (se 4 (by rfl) ⟨3909, by rfl⟩) (B 7819 (by norm_num) ⟨3909, by rfl⟩ (by norm_num))
theorem R41705 : Reach 41705 := rs (se 2 (by rfl) ⟨15639, by rfl⟩) (B 31279 (by norm_num) ⟨15639, by rfl⟩ (by norm_num))
theorem R41709 : Reach 41709 := rs (se 3 (by rfl) ⟨7820, by rfl⟩) (B 15641 (by norm_num) ⟨7820, by rfl⟩ (by norm_num))
theorem R41713 : Reach 41713 := rs (se 2 (by rfl) ⟨15642, by rfl⟩) (B 31285 (by norm_num) ⟨15642, by rfl⟩ (by norm_num))
theorem R140021 : Reach 140021 := rs (se 5 (by rfl) ⟨6563, by rfl⟩) (B 13127 (by norm_num) ⟨6563, by rfl⟩ (by norm_num))
theorem R41717 : Reach 41717 := rs (se 5 (by rfl) ⟨1955, by rfl⟩) (B 3911 (by norm_num) ⟨1955, by rfl⟩ (by norm_num))
theorem R41721 : Reach 41721 := rs (se 2 (by rfl) ⟨15645, by rfl⟩) (B 31291 (by norm_num) ⟨15645, by rfl⟩ (by norm_num))
theorem R41725 : Reach 41725 := rs (se 3 (by rfl) ⟨7823, by rfl⟩) (B 15647 (by norm_num) ⟨7823, by rfl⟩ (by norm_num))
theorem R41729 : Reach 41729 := rs (se 2 (by rfl) ⟨15648, by rfl⟩) (B 31297 (by norm_num) ⟨15648, by rfl⟩ (by norm_num))
theorem R41733 : Reach 41733 := rs (se 4 (by rfl) ⟨3912, by rfl⟩) (B 7825 (by norm_num) ⟨3912, by rfl⟩ (by norm_num))
theorem R41737 : Reach 41737 := rs (se 2 (by rfl) ⟨15651, by rfl⟩) (B 31303 (by norm_num) ⟨15651, by rfl⟩ (by norm_num))
theorem R41741 : Reach 41741 := rs (se 3 (by rfl) ⟨7826, by rfl⟩) (B 15653 (by norm_num) ⟨7826, by rfl⟩ (by norm_num))
theorem R41745 : Reach 41745 := rs (se 2 (by rfl) ⟨15654, by rfl⟩) (B 31309 (by norm_num) ⟨15654, by rfl⟩ (by norm_num))
theorem R41749 : Reach 41749 := rs (se 6 (by rfl) ⟨978, by rfl⟩) (B 1957 (by norm_num) ⟨978, by rfl⟩ (by norm_num))
theorem R41753 : Reach 41753 := rs (se 2 (by rfl) ⟨15657, by rfl⟩) (B 31315 (by norm_num) ⟨15657, by rfl⟩ (by norm_num))
theorem R41757 : Reach 41757 := rs (se 3 (by rfl) ⟨7829, by rfl⟩) (B 15659 (by norm_num) ⟨7829, by rfl⟩ (by norm_num))
theorem R41761 : Reach 41761 := rs (se 2 (by rfl) ⟨15660, by rfl⟩) (B 31321 (by norm_num) ⟨15660, by rfl⟩ (by norm_num))
theorem R74533 : Reach 74533 := rs (se 4 (by rfl) ⟨6987, by rfl⟩) (B 13975 (by norm_num) ⟨6987, by rfl⟩ (by norm_num))
theorem R41765 : Reach 41765 := rs (se 4 (by rfl) ⟨3915, by rfl⟩) (B 7831 (by norm_num) ⟨3915, by rfl⟩ (by norm_num))
theorem R41769 : Reach 41769 := rs (se 2 (by rfl) ⟨15663, by rfl⟩) (B 31327 (by norm_num) ⟨15663, by rfl⟩ (by norm_num))
theorem R41773 : Reach 41773 := rs (se 3 (by rfl) ⟨7832, by rfl⟩) (B 15665 (by norm_num) ⟨7832, by rfl⟩ (by norm_num))
theorem R41777 : Reach 41777 := rs (se 2 (by rfl) ⟨15666, by rfl⟩) (B 31333 (by norm_num) ⟨15666, by rfl⟩ (by norm_num))
theorem R41781 : Reach 41781 := rs (se 5 (by rfl) ⟨1958, by rfl⟩) (B 3917 (by norm_num) ⟨1958, by rfl⟩ (by norm_num))
theorem R41785 : Reach 41785 := rs (se 2 (by rfl) ⟨15669, by rfl⟩) (B 31339 (by norm_num) ⟨15669, by rfl⟩ (by norm_num))
theorem R41789 : Reach 41789 := rs (se 3 (by rfl) ⟨7835, by rfl⟩) (B 15671 (by norm_num) ⟨7835, by rfl⟩ (by norm_num))
theorem R41793 : Reach 41793 := rs (se 2 (by rfl) ⟨15672, by rfl⟩) (B 31345 (by norm_num) ⟨15672, by rfl⟩ (by norm_num))
theorem R41797 : Reach 41797 := rs (se 4 (by rfl) ⟨3918, by rfl⟩) (B 7837 (by norm_num) ⟨3918, by rfl⟩ (by norm_num))
theorem R41801 : Reach 41801 := rs (se 2 (by rfl) ⟨15675, by rfl⟩) (B 31351 (by norm_num) ⟨15675, by rfl⟩ (by norm_num))
theorem R41805 : Reach 41805 := rs (se 3 (by rfl) ⟨7838, by rfl⟩) (B 15677 (by norm_num) ⟨7838, by rfl⟩ (by norm_num))
theorem R41809 : Reach 41809 := rs (se 2 (by rfl) ⟨15678, by rfl⟩) (B 31357 (by norm_num) ⟨15678, by rfl⟩ (by norm_num))
theorem R41813 : Reach 41813 := rs (se 9 (by rfl) ⟨122, by rfl⟩) (B 245 (by norm_num) ⟨122, by rfl⟩ (by norm_num))
theorem R41817 : Reach 41817 := rs (se 2 (by rfl) ⟨15681, by rfl⟩) (B 31363 (by norm_num) ⟨15681, by rfl⟩ (by norm_num))
theorem R41821 : Reach 41821 := rs (se 3 (by rfl) ⟨7841, by rfl⟩) (B 15683 (by norm_num) ⟨7841, by rfl⟩ (by norm_num))
theorem R41825 : Reach 41825 := rs (se 2 (by rfl) ⟨15684, by rfl⟩) (B 31369 (by norm_num) ⟨15684, by rfl⟩ (by norm_num))
theorem R107365 : Reach 107365 := rs (se 4 (by rfl) ⟨10065, by rfl⟩) (B 20131 (by norm_num) ⟨10065, by rfl⟩ (by norm_num))
theorem R41829 : Reach 41829 := rs (se 4 (by rfl) ⟨3921, by rfl⟩) (B 7843 (by norm_num) ⟨3921, by rfl⟩ (by norm_num))
theorem R41833 : Reach 41833 := rs (se 2 (by rfl) ⟨15687, by rfl⟩) (B 31375 (by norm_num) ⟨15687, by rfl⟩ (by norm_num))
theorem R41837 : Reach 41837 := rs (se 3 (by rfl) ⟨7844, by rfl⟩) (B 15689 (by norm_num) ⟨7844, by rfl⟩ (by norm_num))
theorem R41841 : Reach 41841 := rs (se 2 (by rfl) ⟨15690, by rfl⟩) (B 31381 (by norm_num) ⟨15690, by rfl⟩ (by norm_num))
theorem R41845 : Reach 41845 := rs (se 5 (by rfl) ⟨1961, by rfl⟩) (B 3923 (by norm_num) ⟨1961, by rfl⟩ (by norm_num))
theorem R41849 : Reach 41849 := rs (se 2 (by rfl) ⟨15693, by rfl⟩) (B 31387 (by norm_num) ⟨15693, by rfl⟩ (by norm_num))
theorem R41853 : Reach 41853 := rs (se 3 (by rfl) ⟨7847, by rfl⟩) (B 15695 (by norm_num) ⟨7847, by rfl⟩ (by norm_num))
theorem R41857 : Reach 41857 := rs (se 2 (by rfl) ⟨15696, by rfl⟩) (B 31393 (by norm_num) ⟨15696, by rfl⟩ (by norm_num))
theorem R41861 : Reach 41861 := rs (se 4 (by rfl) ⟨3924, by rfl⟩) (B 7849 (by norm_num) ⟨3924, by rfl⟩ (by norm_num))
theorem R41865 : Reach 41865 := rs (se 2 (by rfl) ⟨15699, by rfl⟩) (B 31399 (by norm_num) ⟨15699, by rfl⟩ (by norm_num))
theorem R41869 : Reach 41869 := rs (se 3 (by rfl) ⟨7850, by rfl⟩) (B 15701 (by norm_num) ⟨7850, by rfl⟩ (by norm_num))
theorem R41873 : Reach 41873 := rs (se 2 (by rfl) ⟨15702, by rfl⟩) (B 31405 (by norm_num) ⟨15702, by rfl⟩ (by norm_num))
theorem R41877 : Reach 41877 := rs (se 6 (by rfl) ⟨981, by rfl⟩) (B 1963 (by norm_num) ⟨981, by rfl⟩ (by norm_num))
theorem R41881 : Reach 41881 := rs (se 2 (by rfl) ⟨15705, by rfl⟩) (B 31411 (by norm_num) ⟨15705, by rfl⟩ (by norm_num))
theorem R41885 : Reach 41885 := rs (se 3 (by rfl) ⟨7853, by rfl⟩) (B 15707 (by norm_num) ⟨7853, by rfl⟩ (by norm_num))
theorem R41889 : Reach 41889 := rs (se 2 (by rfl) ⟨15708, by rfl⟩) (B 31417 (by norm_num) ⟨15708, by rfl⟩ (by norm_num))
theorem R41893 : Reach 41893 := rs (se 4 (by rfl) ⟨3927, by rfl⟩) (B 7855 (by norm_num) ⟨3927, by rfl⟩ (by norm_num))
theorem R41897 : Reach 41897 := rs (se 2 (by rfl) ⟨15711, by rfl⟩) (B 31423 (by norm_num) ⟨15711, by rfl⟩ (by norm_num))
theorem R41901 : Reach 41901 := rs (se 3 (by rfl) ⟨7856, by rfl⟩) (B 15713 (by norm_num) ⟨7856, by rfl⟩ (by norm_num))
theorem R41905 : Reach 41905 := rs (se 2 (by rfl) ⟨15714, by rfl⟩) (B 31429 (by norm_num) ⟨15714, by rfl⟩ (by norm_num))
theorem R74677 : Reach 74677 := rs (se 5 (by rfl) ⟨3500, by rfl⟩) (B 7001 (by norm_num) ⟨3500, by rfl⟩ (by norm_num))
theorem R41909 : Reach 41909 := rs (se 5 (by rfl) ⟨1964, by rfl⟩) (B 3929 (by norm_num) ⟨1964, by rfl⟩ (by norm_num))
theorem R41913 : Reach 41913 := rs (se 2 (by rfl) ⟨15717, by rfl⟩) (B 31435 (by norm_num) ⟨15717, by rfl⟩ (by norm_num))
theorem R41917 : Reach 41917 := rs (se 3 (by rfl) ⟨7859, by rfl⟩) (B 15719 (by norm_num) ⟨7859, by rfl⟩ (by norm_num))
theorem R41921 : Reach 41921 := rs (se 2 (by rfl) ⟨15720, by rfl⟩) (B 31441 (by norm_num) ⟨15720, by rfl⟩ (by norm_num))
theorem R41925 : Reach 41925 := rs (se 4 (by rfl) ⟨3930, by rfl⟩) (B 7861 (by norm_num) ⟨3930, by rfl⟩ (by norm_num))
theorem R41929 : Reach 41929 := rs (se 2 (by rfl) ⟨15723, by rfl⟩) (B 31447 (by norm_num) ⟨15723, by rfl⟩ (by norm_num))
theorem R41933 : Reach 41933 := rs (se 3 (by rfl) ⟨7862, by rfl⟩) (B 15725 (by norm_num) ⟨7862, by rfl⟩ (by norm_num))
theorem R41937 : Reach 41937 := rs (se 2 (by rfl) ⟨15726, by rfl⟩) (B 31453 (by norm_num) ⟨15726, by rfl⟩ (by norm_num))
theorem R41941 : Reach 41941 := rs (se 7 (by rfl) ⟨491, by rfl⟩) (B 983 (by norm_num) ⟨491, by rfl⟩ (by norm_num))
theorem R107477 : Reach 107477 := rs (se 7 (by rfl) ⟨1259, by rfl⟩) (B 2519 (by norm_num) ⟨1259, by rfl⟩ (by norm_num))
theorem R41945 : Reach 41945 := rs (se 2 (by rfl) ⟨15729, by rfl⟩) (B 31459 (by norm_num) ⟨15729, by rfl⟩ (by norm_num))
theorem R41949 : Reach 41949 := rs (se 3 (by rfl) ⟨7865, by rfl⟩) (B 15731 (by norm_num) ⟨7865, by rfl⟩ (by norm_num))
theorem R41953 : Reach 41953 := rs (se 2 (by rfl) ⟨15732, by rfl⟩) (B 31465 (by norm_num) ⟨15732, by rfl⟩ (by norm_num))
theorem R41957 : Reach 41957 := rs (se 4 (by rfl) ⟨3933, by rfl⟩) (B 7867 (by norm_num) ⟨3933, by rfl⟩ (by norm_num))
theorem R41961 : Reach 41961 := rs (se 2 (by rfl) ⟨15735, by rfl⟩) (B 31471 (by norm_num) ⟨15735, by rfl⟩ (by norm_num))
theorem R41965 : Reach 41965 := rs (se 3 (by rfl) ⟨7868, by rfl⟩) (B 15737 (by norm_num) ⟨7868, by rfl⟩ (by norm_num))
theorem R41969 : Reach 41969 := rs (se 2 (by rfl) ⟨15738, by rfl⟩) (B 31477 (by norm_num) ⟨15738, by rfl⟩ (by norm_num))
theorem R41973 : Reach 41973 := rs (se 5 (by rfl) ⟨1967, by rfl⟩) (B 3935 (by norm_num) ⟨1967, by rfl⟩ (by norm_num))
theorem R41977 : Reach 41977 := rs (se 2 (by rfl) ⟨15741, by rfl⟩) (B 31483 (by norm_num) ⟨15741, by rfl⟩ (by norm_num))
theorem R41981 : Reach 41981 := rs (se 3 (by rfl) ⟨7871, by rfl⟩) (B 15743 (by norm_num) ⟨7871, by rfl⟩ (by norm_num))
theorem R41985 : Reach 41985 := rs (se 2 (by rfl) ⟨15744, by rfl⟩) (B 31489 (by norm_num) ⟨15744, by rfl⟩ (by norm_num))
theorem R140293 : Reach 140293 := rs (se 4 (by rfl) ⟨13152, by rfl⟩) (B 26305 (by norm_num) ⟨13152, by rfl⟩ (by norm_num))
theorem R41989 : Reach 41989 := rs (se 4 (by rfl) ⟨3936, by rfl⟩) (B 7873 (by norm_num) ⟨3936, by rfl⟩ (by norm_num))
theorem R41993 : Reach 41993 := rs (se 2 (by rfl) ⟨15747, by rfl⟩) (B 31495 (by norm_num) ⟨15747, by rfl⟩ (by norm_num))
theorem R41997 : Reach 41997 := rs (se 3 (by rfl) ⟨7874, by rfl⟩) (B 15749 (by norm_num) ⟨7874, by rfl⟩ (by norm_num))
theorem R42001 : Reach 42001 := rs (se 2 (by rfl) ⟨15750, by rfl⟩) (B 31501 (by norm_num) ⟨15750, by rfl⟩ (by norm_num))
theorem R42005 : Reach 42005 := rs (se 6 (by rfl) ⟨984, by rfl⟩) (B 1969 (by norm_num) ⟨984, by rfl⟩ (by norm_num))
theorem R42009 : Reach 42009 := rs (se 2 (by rfl) ⟨15753, by rfl⟩) (B 31507 (by norm_num) ⟨15753, by rfl⟩ (by norm_num))
theorem R42013 : Reach 42013 := rs (se 3 (by rfl) ⟨7877, by rfl⟩) (B 15755 (by norm_num) ⟨7877, by rfl⟩ (by norm_num))
theorem R42017 : Reach 42017 := rs (se 2 (by rfl) ⟨15756, by rfl⟩) (B 31513 (by norm_num) ⟨15756, by rfl⟩ (by norm_num))
theorem R42021 : Reach 42021 := rs (se 4 (by rfl) ⟨3939, by rfl⟩) (B 7879 (by norm_num) ⟨3939, by rfl⟩ (by norm_num))
theorem R42025 : Reach 42025 := rs (se 2 (by rfl) ⟨15759, by rfl⟩) (B 31519 (by norm_num) ⟨15759, by rfl⟩ (by norm_num))
theorem R42029 : Reach 42029 := rs (se 3 (by rfl) ⟨7880, by rfl⟩) (B 15761 (by norm_num) ⟨7880, by rfl⟩ (by norm_num))
theorem R42033 : Reach 42033 := rs (se 2 (by rfl) ⟨15762, by rfl⟩) (B 31525 (by norm_num) ⟨15762, by rfl⟩ (by norm_num))
theorem R42037 : Reach 42037 := rs (se 5 (by rfl) ⟨1970, by rfl⟩) (B 3941 (by norm_num) ⟨1970, by rfl⟩ (by norm_num))
theorem R42041 : Reach 42041 := rs (se 2 (by rfl) ⟨15765, by rfl⟩) (B 31531 (by norm_num) ⟨15765, by rfl⟩ (by norm_num))
theorem R42045 : Reach 42045 := rs (se 3 (by rfl) ⟨7883, by rfl⟩) (B 15767 (by norm_num) ⟨7883, by rfl⟩ (by norm_num))
theorem R42049 : Reach 42049 := rs (se 2 (by rfl) ⟨15768, by rfl⟩) (B 31537 (by norm_num) ⟨15768, by rfl⟩ (by norm_num))
theorem R42053 : Reach 42053 := rs (se 4 (by rfl) ⟨3942, by rfl⟩) (B 7885 (by norm_num) ⟨3942, by rfl⟩ (by norm_num))
theorem R42057 : Reach 42057 := rs (se 2 (by rfl) ⟨15771, by rfl⟩) (B 31543 (by norm_num) ⟨15771, by rfl⟩ (by norm_num))
theorem R42061 : Reach 42061 := rs (se 3 (by rfl) ⟨7886, by rfl⟩) (B 15773 (by norm_num) ⟨7886, by rfl⟩ (by norm_num))
theorem R42065 : Reach 42065 := rs (se 2 (by rfl) ⟨15774, by rfl⟩) (B 31549 (by norm_num) ⟨15774, by rfl⟩ (by norm_num))
theorem R74837 : Reach 74837 := rs (se 8 (by rfl) ⟨438, by rfl⟩) (B 877 (by norm_num) ⟨438, by rfl⟩ (by norm_num))
theorem R42069 : Reach 42069 := rs (se 8 (by rfl) ⟨246, by rfl⟩) (B 493 (by norm_num) ⟨246, by rfl⟩ (by norm_num))
theorem R42073 : Reach 42073 := rs (se 2 (by rfl) ⟨15777, by rfl⟩) (B 31555 (by norm_num) ⟨15777, by rfl⟩ (by norm_num))
theorem R42077 : Reach 42077 := rs (se 3 (by rfl) ⟨7889, by rfl⟩) (B 15779 (by norm_num) ⟨7889, by rfl⟩ (by norm_num))
theorem R42081 : Reach 42081 := rs (se 2 (by rfl) ⟨15780, by rfl⟩) (B 31561 (by norm_num) ⟨15780, by rfl⟩ (by norm_num))
theorem R42085 : Reach 42085 := rs (se 4 (by rfl) ⟨3945, by rfl⟩) (B 7891 (by norm_num) ⟨3945, by rfl⟩ (by norm_num))
theorem R42089 : Reach 42089 := rs (se 2 (by rfl) ⟨15783, by rfl⟩) (B 31567 (by norm_num) ⟨15783, by rfl⟩ (by norm_num))
theorem R42093 : Reach 42093 := rs (se 3 (by rfl) ⟨7892, by rfl⟩) (B 15785 (by norm_num) ⟨7892, by rfl⟩ (by norm_num))
theorem R42097 : Reach 42097 := rs (se 2 (by rfl) ⟨15786, by rfl⟩) (B 31573 (by norm_num) ⟨15786, by rfl⟩ (by norm_num))
theorem R42101 : Reach 42101 := rs (se 5 (by rfl) ⟨1973, by rfl⟩) (B 3947 (by norm_num) ⟨1973, by rfl⟩ (by norm_num))
theorem R42105 : Reach 42105 := rs (se 2 (by rfl) ⟨15789, by rfl⟩) (B 31579 (by norm_num) ⟨15789, by rfl⟩ (by norm_num))
theorem R42109 : Reach 42109 := rs (se 3 (by rfl) ⟨7895, by rfl⟩) (B 15791 (by norm_num) ⟨7895, by rfl⟩ (by norm_num))
theorem R42113 : Reach 42113 := rs (se 2 (by rfl) ⟨15792, by rfl⟩) (B 31585 (by norm_num) ⟨15792, by rfl⟩ (by norm_num))
theorem R42117 : Reach 42117 := rs (se 4 (by rfl) ⟨3948, by rfl⟩) (B 7897 (by norm_num) ⟨3948, by rfl⟩ (by norm_num))
theorem R42121 : Reach 42121 := rs (se 2 (by rfl) ⟨15795, by rfl⟩) (B 31591 (by norm_num) ⟨15795, by rfl⟩ (by norm_num))
theorem R42125 : Reach 42125 := rs (se 3 (by rfl) ⟨7898, by rfl⟩) (B 15797 (by norm_num) ⟨7898, by rfl⟩ (by norm_num))
theorem R42129 : Reach 42129 := rs (se 2 (by rfl) ⟨15798, by rfl⟩) (B 31597 (by norm_num) ⟨15798, by rfl⟩ (by norm_num))
theorem R42133 : Reach 42133 := rs (se 6 (by rfl) ⟨987, by rfl⟩) (B 1975 (by norm_num) ⟨987, by rfl⟩ (by norm_num))
theorem R107669 : Reach 107669 := rs (se 6 (by rfl) ⟨2523, by rfl⟩) (B 5047 (by norm_num) ⟨2523, by rfl⟩ (by norm_num))
theorem R42137 : Reach 42137 := rs (se 2 (by rfl) ⟨15801, by rfl⟩) (B 31603 (by norm_num) ⟨15801, by rfl⟩ (by norm_num))
theorem R42141 : Reach 42141 := rs (se 3 (by rfl) ⟨7901, by rfl⟩) (B 15803 (by norm_num) ⟨7901, by rfl⟩ (by norm_num))
theorem R42145 : Reach 42145 := rs (se 2 (by rfl) ⟨15804, by rfl⟩) (B 31609 (by norm_num) ⟨15804, by rfl⟩ (by norm_num))
theorem R140453 : Reach 140453 := rs (se 4 (by rfl) ⟨13167, by rfl⟩) (B 26335 (by norm_num) ⟨13167, by rfl⟩ (by norm_num))
theorem R42149 : Reach 42149 := rs (se 4 (by rfl) ⟨3951, by rfl⟩) (B 7903 (by norm_num) ⟨3951, by rfl⟩ (by norm_num))
theorem R42153 : Reach 42153 := rs (se 2 (by rfl) ⟨15807, by rfl⟩) (B 31615 (by norm_num) ⟨15807, by rfl⟩ (by norm_num))
theorem R42157 : Reach 42157 := rs (se 3 (by rfl) ⟨7904, by rfl⟩) (B 15809 (by norm_num) ⟨7904, by rfl⟩ (by norm_num))
theorem R42161 : Reach 42161 := rs (se 2 (by rfl) ⟨15810, by rfl⟩) (B 31621 (by norm_num) ⟨15810, by rfl⟩ (by norm_num))
theorem R42165 : Reach 42165 := rs (se 5 (by rfl) ⟨1976, by rfl⟩) (B 3953 (by norm_num) ⟨1976, by rfl⟩ (by norm_num))
theorem R42169 : Reach 42169 := rs (se 2 (by rfl) ⟨15813, by rfl⟩) (B 31627 (by norm_num) ⟨15813, by rfl⟩ (by norm_num))
theorem R42173 : Reach 42173 := rs (se 3 (by rfl) ⟨7907, by rfl⟩) (B 15815 (by norm_num) ⟨7907, by rfl⟩ (by norm_num))
theorem R42177 : Reach 42177 := rs (se 2 (by rfl) ⟨15816, by rfl⟩) (B 31633 (by norm_num) ⟨15816, by rfl⟩ (by norm_num))
theorem R42181 : Reach 42181 := rs (se 4 (by rfl) ⟨3954, by rfl⟩) (B 7909 (by norm_num) ⟨3954, by rfl⟩ (by norm_num))
theorem R42185 : Reach 42185 := rs (se 2 (by rfl) ⟨15819, by rfl⟩) (B 31639 (by norm_num) ⟨15819, by rfl⟩ (by norm_num))
theorem R42189 : Reach 42189 := rs (se 3 (by rfl) ⟨7910, by rfl⟩) (B 15821 (by norm_num) ⟨7910, by rfl⟩ (by norm_num))
theorem R42193 : Reach 42193 := rs (se 2 (by rfl) ⟨15822, by rfl⟩) (B 31645 (by norm_num) ⟨15822, by rfl⟩ (by norm_num))
theorem R42197 : Reach 42197 := rs (se 7 (by rfl) ⟨494, by rfl⟩) (B 989 (by norm_num) ⟨494, by rfl⟩ (by norm_num))
theorem R42201 : Reach 42201 := rs (se 2 (by rfl) ⟨15825, by rfl⟩) (B 31651 (by norm_num) ⟨15825, by rfl⟩ (by norm_num))
theorem R42205 : Reach 42205 := rs (se 3 (by rfl) ⟨7913, by rfl⟩) (B 15827 (by norm_num) ⟨7913, by rfl⟩ (by norm_num))
theorem R42209 : Reach 42209 := rs (se 2 (by rfl) ⟨15828, by rfl⟩) (B 31657 (by norm_num) ⟨15828, by rfl⟩ (by norm_num))
theorem R74981 : Reach 74981 := rs (se 4 (by rfl) ⟨7029, by rfl⟩) (B 14059 (by norm_num) ⟨7029, by rfl⟩ (by norm_num))
theorem R42213 : Reach 42213 := rs (se 4 (by rfl) ⟨3957, by rfl⟩) (B 7915 (by norm_num) ⟨3957, by rfl⟩ (by norm_num))
theorem R42217 : Reach 42217 := rs (se 2 (by rfl) ⟨15831, by rfl⟩) (B 31663 (by norm_num) ⟨15831, by rfl⟩ (by norm_num))
theorem R42221 : Reach 42221 := rs (se 3 (by rfl) ⟨7916, by rfl⟩) (B 15833 (by norm_num) ⟨7916, by rfl⟩ (by norm_num))
theorem R42225 : Reach 42225 := rs (se 2 (by rfl) ⟨15834, by rfl⟩) (B 31669 (by norm_num) ⟨15834, by rfl⟩ (by norm_num))
theorem R42229 : Reach 42229 := rs (se 5 (by rfl) ⟨1979, by rfl⟩) (B 3959 (by norm_num) ⟨1979, by rfl⟩ (by norm_num))
theorem R42233 : Reach 42233 := rs (se 2 (by rfl) ⟨15837, by rfl⟩) (B 31675 (by norm_num) ⟨15837, by rfl⟩ (by norm_num))
theorem R42237 : Reach 42237 := rs (se 3 (by rfl) ⟨7919, by rfl⟩) (B 15839 (by norm_num) ⟨7919, by rfl⟩ (by norm_num))
theorem R42241 : Reach 42241 := rs (se 2 (by rfl) ⟨15840, by rfl⟩) (B 31681 (by norm_num) ⟨15840, by rfl⟩ (by norm_num))
theorem R42245 : Reach 42245 := rs (se 4 (by rfl) ⟨3960, by rfl⟩) (B 7921 (by norm_num) ⟨3960, by rfl⟩ (by norm_num))
theorem R42249 : Reach 42249 := rs (se 2 (by rfl) ⟨15843, by rfl⟩) (B 31687 (by norm_num) ⟨15843, by rfl⟩ (by norm_num))
theorem R42253 : Reach 42253 := rs (se 3 (by rfl) ⟨7922, by rfl⟩) (B 15845 (by norm_num) ⟨7922, by rfl⟩ (by norm_num))
theorem R42257 : Reach 42257 := rs (se 2 (by rfl) ⟨15846, by rfl⟩) (B 31693 (by norm_num) ⟨15846, by rfl⟩ (by norm_num))
theorem R42261 : Reach 42261 := rs (se 6 (by rfl) ⟨990, by rfl⟩) (B 1981 (by norm_num) ⟨990, by rfl⟩ (by norm_num))
theorem R42265 : Reach 42265 := rs (se 2 (by rfl) ⟨15849, by rfl⟩) (B 31699 (by norm_num) ⟨15849, by rfl⟩ (by norm_num))
theorem R42269 : Reach 42269 := rs (se 3 (by rfl) ⟨7925, by rfl⟩) (B 15851 (by norm_num) ⟨7925, by rfl⟩ (by norm_num))
theorem R42273 : Reach 42273 := rs (se 2 (by rfl) ⟨15852, by rfl⟩) (B 31705 (by norm_num) ⟨15852, by rfl⟩ (by norm_num))
theorem R42277 : Reach 42277 := rs (se 4 (by rfl) ⟨3963, by rfl⟩) (B 7927 (by norm_num) ⟨3963, by rfl⟩ (by norm_num))
theorem R42281 : Reach 42281 := rs (se 2 (by rfl) ⟨15855, by rfl⟩) (B 31711 (by norm_num) ⟨15855, by rfl⟩ (by norm_num))
theorem R42285 : Reach 42285 := rs (se 3 (by rfl) ⟨7928, by rfl⟩) (B 15857 (by norm_num) ⟨7928, by rfl⟩ (by norm_num))
theorem R42289 : Reach 42289 := rs (se 2 (by rfl) ⟨15858, by rfl⟩) (B 31717 (by norm_num) ⟨15858, by rfl⟩ (by norm_num))
theorem R42293 : Reach 42293 := rs (se 5 (by rfl) ⟨1982, by rfl⟩) (B 3965 (by norm_num) ⟨1982, by rfl⟩ (by norm_num))
theorem R42297 : Reach 42297 := rs (se 2 (by rfl) ⟨15861, by rfl⟩) (B 31723 (by norm_num) ⟨15861, by rfl⟩ (by norm_num))
theorem R42301 : Reach 42301 := rs (se 3 (by rfl) ⟨7931, by rfl⟩) (B 15863 (by norm_num) ⟨7931, by rfl⟩ (by norm_num))
theorem R42305 : Reach 42305 := rs (se 2 (by rfl) ⟨15864, by rfl⟩) (B 31729 (by norm_num) ⟨15864, by rfl⟩ (by norm_num))
theorem R42309 : Reach 42309 := rs (se 4 (by rfl) ⟨3966, by rfl⟩) (B 7933 (by norm_num) ⟨3966, by rfl⟩ (by norm_num))
theorem R42313 : Reach 42313 := rs (se 2 (by rfl) ⟨15867, by rfl⟩) (B 31735 (by norm_num) ⟨15867, by rfl⟩ (by norm_num))
theorem R42317 : Reach 42317 := rs (se 3 (by rfl) ⟨7934, by rfl⟩) (B 15869 (by norm_num) ⟨7934, by rfl⟩ (by norm_num))
theorem R42321 : Reach 42321 := rs (se 2 (by rfl) ⟨15870, by rfl⟩) (B 31741 (by norm_num) ⟨15870, by rfl⟩ (by norm_num))
theorem R42325 : Reach 42325 := rs (se 12 (by rfl) ⟨15, by rfl⟩) (B 31 (by norm_num) ⟨15, by rfl⟩ (by norm_num))
theorem R42329 : Reach 42329 := rs (se 2 (by rfl) ⟨15873, by rfl⟩) (B 31747 (by norm_num) ⟨15873, by rfl⟩ (by norm_num))
theorem R42333 : Reach 42333 := rs (se 3 (by rfl) ⟨7937, by rfl⟩) (B 15875 (by norm_num) ⟨7937, by rfl⟩ (by norm_num))
theorem R42337 : Reach 42337 := rs (se 2 (by rfl) ⟨15876, by rfl⟩) (B 31753 (by norm_num) ⟨15876, by rfl⟩ (by norm_num))
theorem R42341 : Reach 42341 := rs (se 4 (by rfl) ⟨3969, by rfl⟩) (B 7939 (by norm_num) ⟨3969, by rfl⟩ (by norm_num))
theorem R42345 : Reach 42345 := rs (se 2 (by rfl) ⟨15879, by rfl⟩) (B 31759 (by norm_num) ⟨15879, by rfl⟩ (by norm_num))
theorem R42349 : Reach 42349 := rs (se 3 (by rfl) ⟨7940, by rfl⟩) (B 15881 (by norm_num) ⟨7940, by rfl⟩ (by norm_num))
theorem R42353 : Reach 42353 := rs (se 2 (by rfl) ⟨15882, by rfl⟩) (B 31765 (by norm_num) ⟨15882, by rfl⟩ (by norm_num))
theorem R42357 : Reach 42357 := rs (se 5 (by rfl) ⟨1985, by rfl⟩) (B 3971 (by norm_num) ⟨1985, by rfl⟩ (by norm_num))
theorem R42361 : Reach 42361 := rs (se 2 (by rfl) ⟨15885, by rfl⟩) (B 31771 (by norm_num) ⟨15885, by rfl⟩ (by norm_num))
theorem R42365 : Reach 42365 := rs (se 3 (by rfl) ⟨7943, by rfl⟩) (B 15887 (by norm_num) ⟨7943, by rfl⟩ (by norm_num))
theorem R42369 : Reach 42369 := rs (se 2 (by rfl) ⟨15888, by rfl⟩) (B 31777 (by norm_num) ⟨15888, by rfl⟩ (by norm_num))
theorem R42373 : Reach 42373 := rs (se 4 (by rfl) ⟨3972, by rfl⟩) (B 7945 (by norm_num) ⟨3972, by rfl⟩ (by norm_num))
theorem R42377 : Reach 42377 := rs (se 2 (by rfl) ⟨15891, by rfl⟩) (B 31783 (by norm_num) ⟨15891, by rfl⟩ (by norm_num))
theorem R42381 : Reach 42381 := rs (se 3 (by rfl) ⟨7946, by rfl⟩) (B 15893 (by norm_num) ⟨7946, by rfl⟩ (by norm_num))
theorem R42385 : Reach 42385 := rs (se 2 (by rfl) ⟨15894, by rfl⟩) (B 31789 (by norm_num) ⟨15894, by rfl⟩ (by norm_num))
theorem R42389 : Reach 42389 := rs (se 6 (by rfl) ⟨993, by rfl⟩) (B 1987 (by norm_num) ⟨993, by rfl⟩ (by norm_num))
theorem R42393 : Reach 42393 := rs (se 2 (by rfl) ⟨15897, by rfl⟩) (B 31795 (by norm_num) ⟨15897, by rfl⟩ (by norm_num))
theorem R42397 : Reach 42397 := rs (se 3 (by rfl) ⟨7949, by rfl⟩) (B 15899 (by norm_num) ⟨7949, by rfl⟩ (by norm_num))
theorem R42401 : Reach 42401 := rs (se 2 (by rfl) ⟨15900, by rfl⟩) (B 31801 (by norm_num) ⟨15900, by rfl⟩ (by norm_num))
theorem R42405 : Reach 42405 := rs (se 4 (by rfl) ⟨3975, by rfl⟩) (B 7951 (by norm_num) ⟨3975, by rfl⟩ (by norm_num))
theorem R42409 : Reach 42409 := rs (se 2 (by rfl) ⟨15903, by rfl⟩) (B 31807 (by norm_num) ⟨15903, by rfl⟩ (by norm_num))
theorem R42413 : Reach 42413 := rs (se 3 (by rfl) ⟨7952, by rfl⟩) (B 15905 (by norm_num) ⟨7952, by rfl⟩ (by norm_num))
theorem R42417 : Reach 42417 := rs (se 2 (by rfl) ⟨15906, by rfl⟩) (B 31813 (by norm_num) ⟨15906, by rfl⟩ (by norm_num))
theorem R42421 : Reach 42421 := rs (se 5 (by rfl) ⟨1988, by rfl⟩) (B 3977 (by norm_num) ⟨1988, by rfl⟩ (by norm_num))
theorem R42425 : Reach 42425 := rs (se 2 (by rfl) ⟨15909, by rfl⟩) (B 31819 (by norm_num) ⟨15909, by rfl⟩ (by norm_num))
theorem R42429 : Reach 42429 := rs (se 3 (by rfl) ⟨7955, by rfl⟩) (B 15911 (by norm_num) ⟨7955, by rfl⟩ (by norm_num))
theorem R42433 : Reach 42433 := rs (se 2 (by rfl) ⟨15912, by rfl⟩) (B 31825 (by norm_num) ⟨15912, by rfl⟩ (by norm_num))
theorem R42437 : Reach 42437 := rs (se 4 (by rfl) ⟨3978, by rfl⟩) (B 7957 (by norm_num) ⟨3978, by rfl⟩ (by norm_num))
theorem R42441 : Reach 42441 := rs (se 2 (by rfl) ⟨15915, by rfl⟩) (B 31831 (by norm_num) ⟨15915, by rfl⟩ (by norm_num))
theorem R42445 : Reach 42445 := rs (se 3 (by rfl) ⟨7958, by rfl⟩) (B 15917 (by norm_num) ⟨7958, by rfl⟩ (by norm_num))
theorem R42449 : Reach 42449 := rs (se 2 (by rfl) ⟨15918, by rfl⟩) (B 31837 (by norm_num) ⟨15918, by rfl⟩ (by norm_num))
theorem R42453 : Reach 42453 := rs (se 7 (by rfl) ⟨497, by rfl⟩) (B 995 (by norm_num) ⟨497, by rfl⟩ (by norm_num))
theorem R42457 : Reach 42457 := rs (se 2 (by rfl) ⟨15921, by rfl⟩) (B 31843 (by norm_num) ⟨15921, by rfl⟩ (by norm_num))
theorem R42461 : Reach 42461 := rs (se 3 (by rfl) ⟨7961, by rfl⟩) (B 15923 (by norm_num) ⟨7961, by rfl⟩ (by norm_num))
theorem R42465 : Reach 42465 := rs (se 2 (by rfl) ⟨15924, by rfl⟩) (B 31849 (by norm_num) ⟨15924, by rfl⟩ (by norm_num))
theorem R42469 : Reach 42469 := rs (se 4 (by rfl) ⟨3981, by rfl⟩) (B 7963 (by norm_num) ⟨3981, by rfl⟩ (by norm_num))
theorem R42473 : Reach 42473 := rs (se 2 (by rfl) ⟨15927, by rfl⟩) (B 31855 (by norm_num) ⟨15927, by rfl⟩ (by norm_num))
theorem R42477 : Reach 42477 := rs (se 3 (by rfl) ⟨7964, by rfl⟩) (B 15929 (by norm_num) ⟨7964, by rfl⟩ (by norm_num))
theorem R42481 : Reach 42481 := rs (se 2 (by rfl) ⟨15930, by rfl⟩) (B 31861 (by norm_num) ⟨15930, by rfl⟩ (by norm_num))
theorem R42485 : Reach 42485 := rs (se 5 (by rfl) ⟨1991, by rfl⟩) (B 3983 (by norm_num) ⟨1991, by rfl⟩ (by norm_num))
theorem R42489 : Reach 42489 := rs (se 2 (by rfl) ⟨15933, by rfl⟩) (B 31867 (by norm_num) ⟨15933, by rfl⟩ (by norm_num))
theorem R42493 : Reach 42493 := rs (se 3 (by rfl) ⟨7967, by rfl⟩) (B 15935 (by norm_num) ⟨7967, by rfl⟩ (by norm_num))
theorem R42497 : Reach 42497 := rs (se 2 (by rfl) ⟨15936, by rfl⟩) (B 31873 (by norm_num) ⟨15936, by rfl⟩ (by norm_num))
theorem R75269 : Reach 75269 := rs (se 4 (by rfl) ⟨7056, by rfl⟩) (B 14113 (by norm_num) ⟨7056, by rfl⟩ (by norm_num))
theorem R42501 : Reach 42501 := rs (se 4 (by rfl) ⟨3984, by rfl⟩) (B 7969 (by norm_num) ⟨3984, by rfl⟩ (by norm_num))
theorem R42505 : Reach 42505 := rs (se 2 (by rfl) ⟨15939, by rfl⟩) (B 31879 (by norm_num) ⟨15939, by rfl⟩ (by norm_num))
theorem R42509 : Reach 42509 := rs (se 3 (by rfl) ⟨7970, by rfl⟩) (B 15941 (by norm_num) ⟨7970, by rfl⟩ (by norm_num))
theorem R42513 : Reach 42513 := rs (se 2 (by rfl) ⟨15942, by rfl⟩) (B 31885 (by norm_num) ⟨15942, by rfl⟩ (by norm_num))
theorem R42517 : Reach 42517 := rs (se 6 (by rfl) ⟨996, by rfl⟩) (B 1993 (by norm_num) ⟨996, by rfl⟩ (by norm_num))
theorem R42521 : Reach 42521 := rs (se 2 (by rfl) ⟨15945, by rfl⟩) (B 31891 (by norm_num) ⟨15945, by rfl⟩ (by norm_num))
theorem R42525 : Reach 42525 := rs (se 3 (by rfl) ⟨7973, by rfl⟩) (B 15947 (by norm_num) ⟨7973, by rfl⟩ (by norm_num))
theorem R42529 : Reach 42529 := rs (se 2 (by rfl) ⟨15948, by rfl⟩) (B 31897 (by norm_num) ⟨15948, by rfl⟩ (by norm_num))
theorem R42533 : Reach 42533 := rs (se 4 (by rfl) ⟨3987, by rfl⟩) (B 7975 (by norm_num) ⟨3987, by rfl⟩ (by norm_num))
theorem R42537 : Reach 42537 := rs (se 2 (by rfl) ⟨15951, by rfl⟩) (B 31903 (by norm_num) ⟨15951, by rfl⟩ (by norm_num))
theorem R42541 : Reach 42541 := rs (se 3 (by rfl) ⟨7976, by rfl⟩) (B 15953 (by norm_num) ⟨7976, by rfl⟩ (by norm_num))
theorem R42545 : Reach 42545 := rs (se 2 (by rfl) ⟨15954, by rfl⟩) (B 31909 (by norm_num) ⟨15954, by rfl⟩ (by norm_num))
theorem R42549 : Reach 42549 := rs (se 5 (by rfl) ⟨1994, by rfl⟩) (B 3989 (by norm_num) ⟨1994, by rfl⟩ (by norm_num))
theorem R42553 : Reach 42553 := rs (se 2 (by rfl) ⟨15957, by rfl⟩) (B 31915 (by norm_num) ⟨15957, by rfl⟩ (by norm_num))
theorem R42557 : Reach 42557 := rs (se 3 (by rfl) ⟨7979, by rfl⟩) (B 15959 (by norm_num) ⟨7979, by rfl⟩ (by norm_num))
theorem R42561 : Reach 42561 := rs (se 2 (by rfl) ⟨15960, by rfl⟩) (B 31921 (by norm_num) ⟨15960, by rfl⟩ (by norm_num))
theorem R42565 : Reach 42565 := rs (se 4 (by rfl) ⟨3990, by rfl⟩) (B 7981 (by norm_num) ⟨3990, by rfl⟩ (by norm_num))
theorem R42569 : Reach 42569 := rs (se 2 (by rfl) ⟨15963, by rfl⟩) (B 31927 (by norm_num) ⟨15963, by rfl⟩ (by norm_num))
theorem R42573 : Reach 42573 := rs (se 3 (by rfl) ⟨7982, by rfl⟩) (B 15965 (by norm_num) ⟨7982, by rfl⟩ (by norm_num))
theorem R42577 : Reach 42577 := rs (se 2 (by rfl) ⟨15966, by rfl⟩) (B 31933 (by norm_num) ⟨15966, by rfl⟩ (by norm_num))
theorem R140885 : Reach 140885 := rs (se 8 (by rfl) ⟨825, by rfl⟩) (B 1651 (by norm_num) ⟨825, by rfl⟩ (by norm_num))
theorem R42581 : Reach 42581 := rs (se 8 (by rfl) ⟨249, by rfl⟩) (B 499 (by norm_num) ⟨249, by rfl⟩ (by norm_num))
theorem R42585 : Reach 42585 := rs (se 2 (by rfl) ⟨15969, by rfl⟩) (B 31939 (by norm_num) ⟨15969, by rfl⟩ (by norm_num))
theorem R42589 : Reach 42589 := rs (se 3 (by rfl) ⟨7985, by rfl⟩) (B 15971 (by norm_num) ⟨7985, by rfl⟩ (by norm_num))
theorem R42593 : Reach 42593 := rs (se 2 (by rfl) ⟨15972, by rfl⟩) (B 31945 (by norm_num) ⟨15972, by rfl⟩ (by norm_num))
theorem R42597 : Reach 42597 := rs (se 4 (by rfl) ⟨3993, by rfl⟩) (B 7987 (by norm_num) ⟨3993, by rfl⟩ (by norm_num))
theorem R42601 : Reach 42601 := rs (se 2 (by rfl) ⟨15975, by rfl⟩) (B 31951 (by norm_num) ⟨15975, by rfl⟩ (by norm_num))
theorem R42605 : Reach 42605 := rs (se 3 (by rfl) ⟨7988, by rfl⟩) (B 15977 (by norm_num) ⟨7988, by rfl⟩ (by norm_num))
theorem R42609 : Reach 42609 := rs (se 2 (by rfl) ⟨15978, by rfl⟩) (B 31957 (by norm_num) ⟨15978, by rfl⟩ (by norm_num))
theorem R42613 : Reach 42613 := rs (se 5 (by rfl) ⟨1997, by rfl⟩) (B 3995 (by norm_num) ⟨1997, by rfl⟩ (by norm_num))
theorem R42617 : Reach 42617 := rs (se 2 (by rfl) ⟨15981, by rfl⟩) (B 31963 (by norm_num) ⟨15981, by rfl⟩ (by norm_num))
theorem R42621 : Reach 42621 := rs (se 3 (by rfl) ⟨7991, by rfl⟩) (B 15983 (by norm_num) ⟨7991, by rfl⟩ (by norm_num))
theorem R42625 : Reach 42625 := rs (se 2 (by rfl) ⟨15984, by rfl⟩) (B 31969 (by norm_num) ⟨15984, by rfl⟩ (by norm_num))
theorem R42629 : Reach 42629 := rs (se 4 (by rfl) ⟨3996, by rfl⟩) (B 7993 (by norm_num) ⟨3996, by rfl⟩ (by norm_num))
theorem R42633 : Reach 42633 := rs (se 2 (by rfl) ⟨15987, by rfl⟩) (B 31975 (by norm_num) ⟨15987, by rfl⟩ (by norm_num))
theorem R42637 : Reach 42637 := rs (se 3 (by rfl) ⟨7994, by rfl⟩) (B 15989 (by norm_num) ⟨7994, by rfl⟩ (by norm_num))
theorem R42641 : Reach 42641 := rs (se 2 (by rfl) ⟨15990, by rfl⟩) (B 31981 (by norm_num) ⟨15990, by rfl⟩ (by norm_num))
theorem R42645 : Reach 42645 := rs (se 6 (by rfl) ⟨999, by rfl⟩) (B 1999 (by norm_num) ⟨999, by rfl⟩ (by norm_num))
theorem R42649 : Reach 42649 := rs (se 2 (by rfl) ⟨15993, by rfl⟩) (B 31987 (by norm_num) ⟨15993, by rfl⟩ (by norm_num))
theorem R75421 : Reach 75421 := rs (se 3 (by rfl) ⟨14141, by rfl⟩) (B 28283 (by norm_num) ⟨14141, by rfl⟩ (by norm_num))
theorem R42653 : Reach 42653 := rs (se 3 (by rfl) ⟨7997, by rfl⟩) (B 15995 (by norm_num) ⟨7997, by rfl⟩ (by norm_num))
theorem R42657 : Reach 42657 := rs (se 2 (by rfl) ⟨15996, by rfl⟩) (B 31993 (by norm_num) ⟨15996, by rfl⟩ (by norm_num))
theorem R42661 : Reach 42661 := rs (se 4 (by rfl) ⟨3999, by rfl⟩) (B 7999 (by norm_num) ⟨3999, by rfl⟩ (by norm_num))
theorem R42665 : Reach 42665 := rs (se 2 (by rfl) ⟨15999, by rfl⟩) (B 31999 (by norm_num) ⟨15999, by rfl⟩ (by norm_num))
theorem R42669 : Reach 42669 := rs (se 3 (by rfl) ⟨8000, by rfl⟩) (B 16001 (by norm_num) ⟨8000, by rfl⟩ (by norm_num))
theorem R42673 : Reach 42673 := rs (se 2 (by rfl) ⟨16002, by rfl⟩) (B 32005 (by norm_num) ⟨16002, by rfl⟩ (by norm_num))
theorem R42677 : Reach 42677 := rs (se 5 (by rfl) ⟨2000, by rfl⟩) (B 4001 (by norm_num) ⟨2000, by rfl⟩ (by norm_num))
theorem R42681 : Reach 42681 := rs (se 2 (by rfl) ⟨16005, by rfl⟩) (B 32011 (by norm_num) ⟨16005, by rfl⟩ (by norm_num))
theorem R42685 : Reach 42685 := rs (se 3 (by rfl) ⟨8003, by rfl⟩) (B 16007 (by norm_num) ⟨8003, by rfl⟩ (by norm_num))
theorem R42689 : Reach 42689 := rs (se 2 (by rfl) ⟨16008, by rfl⟩) (B 32017 (by norm_num) ⟨16008, by rfl⟩ (by norm_num))
theorem R173765 : Reach 173765 := rs (se 4 (by rfl) ⟨16290, by rfl⟩) (B 32581 (by norm_num) ⟨16290, by rfl⟩ (by norm_num))
theorem R42693 : Reach 42693 := rs (se 4 (by rfl) ⟨4002, by rfl⟩) (B 8005 (by norm_num) ⟨4002, by rfl⟩ (by norm_num))
theorem R42697 : Reach 42697 := rs (se 2 (by rfl) ⟨16011, by rfl⟩) (B 32023 (by norm_num) ⟨16011, by rfl⟩ (by norm_num))
theorem R42701 : Reach 42701 := rs (se 3 (by rfl) ⟨8006, by rfl⟩) (B 16013 (by norm_num) ⟨8006, by rfl⟩ (by norm_num))
theorem R42705 : Reach 42705 := rs (se 2 (by rfl) ⟨16014, by rfl⟩) (B 32029 (by norm_num) ⟨16014, by rfl⟩ (by norm_num))
theorem R206549 : Reach 206549 := rs (se 7 (by rfl) ⟨2420, by rfl⟩) (B 4841 (by norm_num) ⟨2420, by rfl⟩ (by norm_num))
theorem R42709 : Reach 42709 := rs (se 7 (by rfl) ⟨500, by rfl⟩) (B 1001 (by norm_num) ⟨500, by rfl⟩ (by norm_num))
theorem R42713 : Reach 42713 := rs (se 2 (by rfl) ⟨16017, by rfl⟩) (B 32035 (by norm_num) ⟨16017, by rfl⟩ (by norm_num))
theorem R75485 : Reach 75485 := rs (se 3 (by rfl) ⟨14153, by rfl⟩) (B 28307 (by norm_num) ⟨14153, by rfl⟩ (by norm_num))
theorem R42717 : Reach 42717 := rs (se 3 (by rfl) ⟨8009, by rfl⟩) (B 16019 (by norm_num) ⟨8009, by rfl⟩ (by norm_num))
theorem R42721 : Reach 42721 := rs (se 2 (by rfl) ⟨16020, by rfl⟩) (B 32041 (by norm_num) ⟨16020, by rfl⟩ (by norm_num))
theorem R42725 : Reach 42725 := rs (se 4 (by rfl) ⟨4005, by rfl⟩) (B 8011 (by norm_num) ⟨4005, by rfl⟩ (by norm_num))
theorem R42729 : Reach 42729 := rs (se 2 (by rfl) ⟨16023, by rfl⟩) (B 32047 (by norm_num) ⟨16023, by rfl⟩ (by norm_num))
theorem R42733 : Reach 42733 := rs (se 3 (by rfl) ⟨8012, by rfl⟩) (B 16025 (by norm_num) ⟨8012, by rfl⟩ (by norm_num))
theorem R42737 : Reach 42737 := rs (se 2 (by rfl) ⟨16026, by rfl⟩) (B 32053 (by norm_num) ⟨16026, by rfl⟩ (by norm_num))
theorem R42741 : Reach 42741 := rs (se 5 (by rfl) ⟨2003, by rfl⟩) (B 4007 (by norm_num) ⟨2003, by rfl⟩ (by norm_num))
theorem R42745 : Reach 42745 := rs (se 2 (by rfl) ⟨16029, by rfl⟩) (B 32059 (by norm_num) ⟨16029, by rfl⟩ (by norm_num))
theorem R42749 : Reach 42749 := rs (se 3 (by rfl) ⟨8015, by rfl⟩) (B 16031 (by norm_num) ⟨8015, by rfl⟩ (by norm_num))
theorem R42753 : Reach 42753 := rs (se 2 (by rfl) ⟨16032, by rfl⟩) (B 32065 (by norm_num) ⟨16032, by rfl⟩ (by norm_num))
theorem R42757 : Reach 42757 := rs (se 4 (by rfl) ⟨4008, by rfl⟩) (B 8017 (by norm_num) ⟨4008, by rfl⟩ (by norm_num))
theorem R42761 : Reach 42761 := rs (se 2 (by rfl) ⟨16035, by rfl⟩) (B 32071 (by norm_num) ⟨16035, by rfl⟩ (by norm_num))
theorem R42765 : Reach 42765 := rs (se 3 (by rfl) ⟨8018, by rfl⟩) (B 16037 (by norm_num) ⟨8018, by rfl⟩ (by norm_num))
theorem R42769 : Reach 42769 := rs (se 2 (by rfl) ⟨16038, by rfl⟩) (B 32077 (by norm_num) ⟨16038, by rfl⟩ (by norm_num))
theorem R42773 : Reach 42773 := rs (se 6 (by rfl) ⟨1002, by rfl⟩) (B 2005 (by norm_num) ⟨1002, by rfl⟩ (by norm_num))
theorem R42777 : Reach 42777 := rs (se 2 (by rfl) ⟨16041, by rfl⟩) (B 32083 (by norm_num) ⟨16041, by rfl⟩ (by norm_num))
theorem R42781 : Reach 42781 := rs (se 3 (by rfl) ⟨8021, by rfl⟩) (B 16043 (by norm_num) ⟨8021, by rfl⟩ (by norm_num))
theorem R42785 : Reach 42785 := rs (se 2 (by rfl) ⟨16044, by rfl⟩) (B 32089 (by norm_num) ⟨16044, by rfl⟩ (by norm_num))
theorem R42789 : Reach 42789 := rs (se 4 (by rfl) ⟨4011, by rfl⟩) (B 8023 (by norm_num) ⟨4011, by rfl⟩ (by norm_num))
theorem R42793 : Reach 42793 := rs (se 2 (by rfl) ⟨16047, by rfl⟩) (B 32095 (by norm_num) ⟨16047, by rfl⟩ (by norm_num))
theorem R42797 : Reach 42797 := rs (se 3 (by rfl) ⟨8024, by rfl⟩) (B 16049 (by norm_num) ⟨8024, by rfl⟩ (by norm_num))
theorem R42801 : Reach 42801 := rs (se 2 (by rfl) ⟨16050, by rfl⟩) (B 32101 (by norm_num) ⟨16050, by rfl⟩ (by norm_num))
theorem R108341 : Reach 108341 := rs (se 5 (by rfl) ⟨5078, by rfl⟩) (B 10157 (by norm_num) ⟨5078, by rfl⟩ (by norm_num))
theorem R42805 : Reach 42805 := rs (se 5 (by rfl) ⟨2006, by rfl⟩) (B 4013 (by norm_num) ⟨2006, by rfl⟩ (by norm_num))
theorem R42809 : Reach 42809 := rs (se 2 (by rfl) ⟨16053, by rfl⟩) (B 32107 (by norm_num) ⟨16053, by rfl⟩ (by norm_num))
theorem R42813 : Reach 42813 := rs (se 3 (by rfl) ⟨8027, by rfl⟩) (B 16055 (by norm_num) ⟨8027, by rfl⟩ (by norm_num))
theorem R42817 : Reach 42817 := rs (se 2 (by rfl) ⟨16056, by rfl⟩) (B 32113 (by norm_num) ⟨16056, by rfl⟩ (by norm_num))
theorem R42821 : Reach 42821 := rs (se 4 (by rfl) ⟨4014, by rfl⟩) (B 8029 (by norm_num) ⟨4014, by rfl⟩ (by norm_num))
theorem R42825 : Reach 42825 := rs (se 2 (by rfl) ⟨16059, by rfl⟩) (B 32119 (by norm_num) ⟨16059, by rfl⟩ (by norm_num))
theorem R42829 : Reach 42829 := rs (se 3 (by rfl) ⟨8030, by rfl⟩) (B 16061 (by norm_num) ⟨8030, by rfl⟩ (by norm_num))
theorem R42833 : Reach 42833 := rs (se 2 (by rfl) ⟨16062, by rfl⟩) (B 32125 (by norm_num) ⟨16062, by rfl⟩ (by norm_num))
theorem R108373 : Reach 108373 := rs (se 9 (by rfl) ⟨317, by rfl⟩) (B 635 (by norm_num) ⟨317, by rfl⟩ (by norm_num))
theorem R42837 : Reach 42837 := rs (se 9 (by rfl) ⟨125, by rfl⟩) (B 251 (by norm_num) ⟨125, by rfl⟩ (by norm_num))
theorem R42841 : Reach 42841 := rs (se 2 (by rfl) ⟨16065, by rfl⟩) (B 32131 (by norm_num) ⟨16065, by rfl⟩ (by norm_num))
theorem R42845 : Reach 42845 := rs (se 3 (by rfl) ⟨8033, by rfl⟩) (B 16067 (by norm_num) ⟨8033, by rfl⟩ (by norm_num))
theorem R42849 : Reach 42849 := rs (se 2 (by rfl) ⟨16068, by rfl⟩) (B 32137 (by norm_num) ⟨16068, by rfl⟩ (by norm_num))
theorem R42853 : Reach 42853 := rs (se 4 (by rfl) ⟨4017, by rfl⟩) (B 8035 (by norm_num) ⟨4017, by rfl⟩ (by norm_num))
theorem R42857 : Reach 42857 := rs (se 2 (by rfl) ⟨16071, by rfl⟩) (B 32143 (by norm_num) ⟨16071, by rfl⟩ (by norm_num))
theorem R75629 : Reach 75629 := rs (se 3 (by rfl) ⟨14180, by rfl⟩) (B 28361 (by norm_num) ⟨14180, by rfl⟩ (by norm_num))
theorem R42861 : Reach 42861 := rs (se 3 (by rfl) ⟨8036, by rfl⟩) (B 16073 (by norm_num) ⟨8036, by rfl⟩ (by norm_num))
theorem R42865 : Reach 42865 := rs (se 2 (by rfl) ⟨16074, by rfl⟩) (B 32149 (by norm_num) ⟨16074, by rfl⟩ (by norm_num))
theorem R42869 : Reach 42869 := rs (se 5 (by rfl) ⟨2009, by rfl⟩) (B 4019 (by norm_num) ⟨2009, by rfl⟩ (by norm_num))
theorem R42873 : Reach 42873 := rs (se 2 (by rfl) ⟨16077, by rfl⟩) (B 32155 (by norm_num) ⟨16077, by rfl⟩ (by norm_num))
theorem R42877 : Reach 42877 := rs (se 3 (by rfl) ⟨8039, by rfl⟩) (B 16079 (by norm_num) ⟨8039, by rfl⟩ (by norm_num))
theorem R42881 : Reach 42881 := rs (se 2 (by rfl) ⟨16080, by rfl⟩) (B 32161 (by norm_num) ⟨16080, by rfl⟩ (by norm_num))
theorem R42885 : Reach 42885 := rs (se 4 (by rfl) ⟨4020, by rfl⟩) (B 8041 (by norm_num) ⟨4020, by rfl⟩ (by norm_num))
theorem R42889 : Reach 42889 := rs (se 2 (by rfl) ⟨16083, by rfl⟩) (B 32167 (by norm_num) ⟨16083, by rfl⟩ (by norm_num))
theorem R42893 : Reach 42893 := rs (se 3 (by rfl) ⟨8042, by rfl⟩) (B 16085 (by norm_num) ⟨8042, by rfl⟩ (by norm_num))
theorem R42897 : Reach 42897 := rs (se 2 (by rfl) ⟨16086, by rfl⟩) (B 32173 (by norm_num) ⟨16086, by rfl⟩ (by norm_num))
theorem R42901 : Reach 42901 := rs (se 6 (by rfl) ⟨1005, by rfl⟩) (B 2011 (by norm_num) ⟨1005, by rfl⟩ (by norm_num))
theorem R42905 : Reach 42905 := rs (se 2 (by rfl) ⟨16089, by rfl⟩) (B 32179 (by norm_num) ⟨16089, by rfl⟩ (by norm_num))
theorem R42909 : Reach 42909 := rs (se 3 (by rfl) ⟨8045, by rfl⟩) (B 16091 (by norm_num) ⟨8045, by rfl⟩ (by norm_num))
theorem R42913 : Reach 42913 := rs (se 2 (by rfl) ⟨16092, by rfl⟩) (B 32185 (by norm_num) ⟨16092, by rfl⟩ (by norm_num))
theorem R42917 : Reach 42917 := rs (se 4 (by rfl) ⟨4023, by rfl⟩) (B 8047 (by norm_num) ⟨4023, by rfl⟩ (by norm_num))
theorem R42921 : Reach 42921 := rs (se 2 (by rfl) ⟨16095, by rfl⟩) (B 32191 (by norm_num) ⟨16095, by rfl⟩ (by norm_num))
theorem R42925 : Reach 42925 := rs (se 3 (by rfl) ⟨8048, by rfl⟩) (B 16097 (by norm_num) ⟨8048, by rfl⟩ (by norm_num))
theorem R42929 : Reach 42929 := rs (se 2 (by rfl) ⟨16098, by rfl⟩) (B 32197 (by norm_num) ⟨16098, by rfl⟩ (by norm_num))
theorem R108469 : Reach 108469 := rs (se 5 (by rfl) ⟨5084, by rfl⟩) (B 10169 (by norm_num) ⟨5084, by rfl⟩ (by norm_num))
theorem R42933 : Reach 42933 := rs (se 5 (by rfl) ⟨2012, by rfl⟩) (B 4025 (by norm_num) ⟨2012, by rfl⟩ (by norm_num))
theorem R42937 : Reach 42937 := rs (se 2 (by rfl) ⟨16101, by rfl⟩) (B 32203 (by norm_num) ⟨16101, by rfl⟩ (by norm_num))
theorem R42941 : Reach 42941 := rs (se 3 (by rfl) ⟨8051, by rfl⟩) (B 16103 (by norm_num) ⟨8051, by rfl⟩ (by norm_num))
theorem R42945 : Reach 42945 := rs (se 2 (by rfl) ⟨16104, by rfl⟩) (B 32209 (by norm_num) ⟨16104, by rfl⟩ (by norm_num))
theorem R42949 : Reach 42949 := rs (se 4 (by rfl) ⟨4026, by rfl⟩) (B 8053 (by norm_num) ⟨4026, by rfl⟩ (by norm_num))
theorem R42953 : Reach 42953 := rs (se 2 (by rfl) ⟨16107, by rfl⟩) (B 32215 (by norm_num) ⟨16107, by rfl⟩ (by norm_num))
theorem R75725 : Reach 75725 := rs (se 3 (by rfl) ⟨14198, by rfl⟩) (B 28397 (by norm_num) ⟨14198, by rfl⟩ (by norm_num))
theorem R42957 : Reach 42957 := rs (se 3 (by rfl) ⟨8054, by rfl⟩) (B 16109 (by norm_num) ⟨8054, by rfl⟩ (by norm_num))
theorem R42961 : Reach 42961 := rs (se 2 (by rfl) ⟨16110, by rfl⟩) (B 32221 (by norm_num) ⟨16110, by rfl⟩ (by norm_num))
theorem R42965 : Reach 42965 := rs (se 7 (by rfl) ⟨503, by rfl⟩) (B 1007 (by norm_num) ⟨503, by rfl⟩ (by norm_num))
theorem R42969 : Reach 42969 := rs (se 2 (by rfl) ⟨16113, by rfl⟩) (B 32227 (by norm_num) ⟨16113, by rfl⟩ (by norm_num))
theorem R42973 : Reach 42973 := rs (se 3 (by rfl) ⟨8057, by rfl⟩) (B 16115 (by norm_num) ⟨8057, by rfl⟩ (by norm_num))
theorem R42977 : Reach 42977 := rs (se 2 (by rfl) ⟨16116, by rfl⟩) (B 32233 (by norm_num) ⟨16116, by rfl⟩ (by norm_num))
theorem R42981 : Reach 42981 := rs (se 4 (by rfl) ⟨4029, by rfl⟩) (B 8059 (by norm_num) ⟨4029, by rfl⟩ (by norm_num))
theorem R42985 : Reach 42985 := rs (se 2 (by rfl) ⟨16119, by rfl⟩) (B 32239 (by norm_num) ⟨16119, by rfl⟩ (by norm_num))
theorem R42989 : Reach 42989 := rs (se 3 (by rfl) ⟨8060, by rfl⟩) (B 16121 (by norm_num) ⟨8060, by rfl⟩ (by norm_num))
theorem R42993 : Reach 42993 := rs (se 2 (by rfl) ⟨16122, by rfl⟩) (B 32245 (by norm_num) ⟨16122, by rfl⟩ (by norm_num))
theorem R42997 : Reach 42997 := rs (se 5 (by rfl) ⟨2015, by rfl⟩) (B 4031 (by norm_num) ⟨2015, by rfl⟩ (by norm_num))
theorem R43001 : Reach 43001 := rs (se 2 (by rfl) ⟨16125, by rfl⟩) (B 32251 (by norm_num) ⟨16125, by rfl⟩ (by norm_num))
theorem R43005 : Reach 43005 := rs (se 3 (by rfl) ⟨8063, by rfl⟩) (B 16127 (by norm_num) ⟨8063, by rfl⟩ (by norm_num))
theorem R43009 : Reach 43009 := rs (se 2 (by rfl) ⟨16128, by rfl⟩) (B 32257 (by norm_num) ⟨16128, by rfl⟩ (by norm_num))
theorem R141317 : Reach 141317 := rs (se 4 (by rfl) ⟨13248, by rfl⟩) (B 26497 (by norm_num) ⟨13248, by rfl⟩ (by norm_num))
theorem R43013 : Reach 43013 := rs (se 4 (by rfl) ⟨4032, by rfl⟩) (B 8065 (by norm_num) ⟨4032, by rfl⟩ (by norm_num))
theorem R43017 : Reach 43017 := rs (se 2 (by rfl) ⟨16131, by rfl⟩) (B 32263 (by norm_num) ⟨16131, by rfl⟩ (by norm_num))
theorem R43021 : Reach 43021 := rs (se 3 (by rfl) ⟨8066, by rfl⟩) (B 16133 (by norm_num) ⟨8066, by rfl⟩ (by norm_num))
theorem R43025 : Reach 43025 := rs (se 2 (by rfl) ⟨16134, by rfl⟩) (B 32269 (by norm_num) ⟨16134, by rfl⟩ (by norm_num))
theorem R43029 : Reach 43029 := rs (se 6 (by rfl) ⟨1008, by rfl⟩) (B 2017 (by norm_num) ⟨1008, by rfl⟩ (by norm_num))
theorem R43033 : Reach 43033 := rs (se 2 (by rfl) ⟨16137, by rfl⟩) (B 32275 (by norm_num) ⟨16137, by rfl⟩ (by norm_num))
theorem R43037 : Reach 43037 := rs (se 3 (by rfl) ⟨8069, by rfl⟩) (B 16139 (by norm_num) ⟨8069, by rfl⟩ (by norm_num))
theorem R43041 : Reach 43041 := rs (se 2 (by rfl) ⟨16140, by rfl⟩) (B 32281 (by norm_num) ⟨16140, by rfl⟩ (by norm_num))
theorem R43045 : Reach 43045 := rs (se 4 (by rfl) ⟨4035, by rfl⟩) (B 8071 (by norm_num) ⟨4035, by rfl⟩ (by norm_num))
theorem R43049 : Reach 43049 := rs (se 2 (by rfl) ⟨16143, by rfl⟩) (B 32287 (by norm_num) ⟨16143, by rfl⟩ (by norm_num))
theorem R43053 : Reach 43053 := rs (se 3 (by rfl) ⟨8072, by rfl⟩) (B 16145 (by norm_num) ⟨8072, by rfl⟩ (by norm_num))
theorem R43057 : Reach 43057 := rs (se 2 (by rfl) ⟨16146, by rfl⟩) (B 32293 (by norm_num) ⟨16146, by rfl⟩ (by norm_num))
theorem R43061 : Reach 43061 := rs (se 5 (by rfl) ⟨2018, by rfl⟩) (B 4037 (by norm_num) ⟨2018, by rfl⟩ (by norm_num))
theorem R43065 : Reach 43065 := rs (se 2 (by rfl) ⟨16149, by rfl⟩) (B 32299 (by norm_num) ⟨16149, by rfl⟩ (by norm_num))
theorem R43069 : Reach 43069 := rs (se 3 (by rfl) ⟨8075, by rfl⟩) (B 16151 (by norm_num) ⟨8075, by rfl⟩ (by norm_num))
theorem R43073 : Reach 43073 := rs (se 2 (by rfl) ⟨16152, by rfl⟩) (B 32305 (by norm_num) ⟨16152, by rfl⟩ (by norm_num))
theorem R75845 : Reach 75845 := rs (se 4 (by rfl) ⟨7110, by rfl⟩) (B 14221 (by norm_num) ⟨7110, by rfl⟩ (by norm_num))
theorem R43077 : Reach 43077 := rs (se 4 (by rfl) ⟨4038, by rfl⟩) (B 8077 (by norm_num) ⟨4038, by rfl⟩ (by norm_num))
theorem R43081 : Reach 43081 := rs (se 2 (by rfl) ⟨16155, by rfl⟩) (B 32311 (by norm_num) ⟨16155, by rfl⟩ (by norm_num))
theorem R43085 : Reach 43085 := rs (se 3 (by rfl) ⟨8078, by rfl⟩) (B 16157 (by norm_num) ⟨8078, by rfl⟩ (by norm_num))
theorem R43089 : Reach 43089 := rs (se 2 (by rfl) ⟨16158, by rfl⟩) (B 32317 (by norm_num) ⟨16158, by rfl⟩ (by norm_num))
theorem R43093 : Reach 43093 := rs (se 8 (by rfl) ⟨252, by rfl⟩) (B 505 (by norm_num) ⟨252, by rfl⟩ (by norm_num))
theorem R43097 : Reach 43097 := rs (se 2 (by rfl) ⟨16161, by rfl⟩) (B 32323 (by norm_num) ⟨16161, by rfl⟩ (by norm_num))
theorem R43101 : Reach 43101 := rs (se 3 (by rfl) ⟨8081, by rfl⟩) (B 16163 (by norm_num) ⟨8081, by rfl⟩ (by norm_num))
theorem R43105 : Reach 43105 := rs (se 2 (by rfl) ⟨16164, by rfl⟩) (B 32329 (by norm_num) ⟨16164, by rfl⟩ (by norm_num))
theorem R43109 : Reach 43109 := rs (se 4 (by rfl) ⟨4041, by rfl⟩) (B 8083 (by norm_num) ⟨4041, by rfl⟩ (by norm_num))
theorem R43113 : Reach 43113 := rs (se 2 (by rfl) ⟨16167, by rfl⟩) (B 32335 (by norm_num) ⟨16167, by rfl⟩ (by norm_num))
theorem R43117 : Reach 43117 := rs (se 3 (by rfl) ⟨8084, by rfl⟩) (B 16169 (by norm_num) ⟨8084, by rfl⟩ (by norm_num))
theorem R108661 : Reach 108661 := rs (se 5 (by rfl) ⟨5093, by rfl⟩) (B 10187 (by norm_num) ⟨5093, by rfl⟩ (by norm_num))
theorem R206981 : Reach 206981 := rs (se 4 (by rfl) ⟨19404, by rfl⟩) (B 38809 (by norm_num) ⟨19404, by rfl⟩ (by norm_num))
theorem R108773 : Reach 108773 := rs (se 4 (by rfl) ⟨10197, by rfl⟩) (B 20395 (by norm_num) ⟨10197, by rfl⟩ (by norm_num))
theorem R338165 : Reach 338165 := rs (se 5 (by rfl) ⟨15851, by rfl⟩) (B 31703 (by norm_num) ⟨15851, by rfl⟩ (by norm_num))
theorem R43313 : Reach 43313 := rs (se 2 (by rfl) ⟨16242, by rfl⟩) (B 32485 (by norm_num) ⟨16242, by rfl⟩ (by norm_num))
theorem R207173 : Reach 207173 := rs (se 4 (by rfl) ⟨19422, by rfl⟩) (B 38845 (by norm_num) ⟨19422, by rfl⟩ (by norm_num))
theorem R43373 : Reach 43373 := rs (se 3 (by rfl) ⟨8132, by rfl⟩) (B 16265 (by norm_num) ⟨8132, by rfl⟩ (by norm_num))
theorem R108965 : Reach 108965 := rs (se 4 (by rfl) ⟨10215, by rfl⟩) (B 20431 (by norm_num) ⟨10215, by rfl⟩ (by norm_num))
theorem R43441 : Reach 43441 := rs (se 2 (by rfl) ⟨16290, by rfl⟩) (B 32581 (by norm_num) ⟨16290, by rfl⟩ (by norm_num))
theorem R141749 : Reach 141749 := rs (se 5 (by rfl) ⟨6644, by rfl⟩) (B 13289 (by norm_num) ⟨6644, by rfl⟩ (by norm_num))
theorem R43501 : Reach 43501 := rs (se 3 (by rfl) ⟨8156, by rfl⟩) (B 16313 (by norm_num) ⟨8156, by rfl⟩ (by norm_num))
theorem R404021 : Reach 404021 := rs (se 5 (by rfl) ⟨18938, by rfl⟩) (B 37877 (by norm_num) ⟨18938, by rfl⟩ (by norm_num))
theorem R76349 : Reach 76349 := rs (se 3 (by rfl) ⟨14315, by rfl⟩) (B 28631 (by norm_num) ⟨14315, by rfl⟩ (by norm_num))
theorem R43669 : Reach 43669 := rs (se 6 (by rfl) ⟨1023, by rfl⟩) (B 2047 (by norm_num) ⟨1023, by rfl⟩ (by norm_num))
theorem R76477 : Reach 76477 := rs (se 3 (by rfl) ⟨14339, by rfl⟩) (B 28679 (by norm_num) ⟨14339, by rfl⟩ (by norm_num))
theorem R109333 : Reach 109333 := rs (se 6 (by rfl) ⟨2562, by rfl⟩) (B 5125 (by norm_num) ⟨2562, by rfl⟩ (by norm_num))
theorem R76621 : Reach 76621 := rs (se 3 (by rfl) ⟨14366, by rfl⟩) (B 28733 (by norm_num) ⟨14366, by rfl⟩ (by norm_num))
theorem R142181 : Reach 142181 := rs (se 4 (by rfl) ⟨13329, by rfl⟩) (B 26659 (by norm_num) ⟨13329, by rfl⟩ (by norm_num))
theorem R732053 : Reach 732053 := rs (se 6 (by rfl) ⟨17157, by rfl⟩) (B 34315 (by norm_num) ⟨17157, by rfl⟩ (by norm_num))
theorem R43945 : Reach 43945 := rs (se 2 (by rfl) ⟨16479, by rfl⟩) (B 32959 (by norm_num) ⟨16479, by rfl⟩ (by norm_num))
theorem R207845 : Reach 207845 := rs (se 4 (by rfl) ⟨19485, by rfl⟩) (B 38971 (by norm_num) ⟨19485, by rfl⟩ (by norm_num))
theorem R76781 : Reach 76781 := rs (se 3 (by rfl) ⟨14396, by rfl⟩) (B 28793 (by norm_num) ⟨14396, by rfl⟩ (by norm_num))
theorem R44041 : Reach 44041 := rs (se 2 (by rfl) ⟨16515, by rfl⟩) (B 33031 (by norm_num) ⟨16515, by rfl⟩ (by norm_num))
theorem R44065 : Reach 44065 := rs (se 2 (by rfl) ⟨16524, by rfl⟩) (B 33049 (by norm_num) ⟨16524, by rfl⟩ (by norm_num))
theorem R44077 : Reach 44077 := rs (se 3 (by rfl) ⟨8264, by rfl⟩) (B 16529 (by norm_num) ⟨8264, by rfl⟩ (by norm_num))
theorem R44101 : Reach 44101 := rs (se 4 (by rfl) ⟨4134, by rfl⟩) (B 8269 (by norm_num) ⟨4134, by rfl⟩ (by norm_num))
theorem R44113 : Reach 44113 := rs (se 2 (by rfl) ⟨16542, by rfl⟩) (B 33085 (by norm_num) ⟨16542, by rfl⟩ (by norm_num))
theorem R240725 : Reach 240725 := rs (se 8 (by rfl) ⟨1410, by rfl⟩) (B 2821 (by norm_num) ⟨1410, by rfl⟩ (by norm_num))
theorem R44149 : Reach 44149 := rs (se 5 (by rfl) ⟨2069, by rfl⟩) (B 4139 (by norm_num) ⟨2069, by rfl⟩ (by norm_num))
theorem R76925 : Reach 76925 := rs (se 3 (by rfl) ⟨14423, by rfl⟩) (B 28847 (by norm_num) ⟨14423, by rfl⟩ (by norm_num))
theorem R44185 : Reach 44185 := rs (se 2 (by rfl) ⟨16569, by rfl⟩) (B 33139 (by norm_num) ⟨16569, by rfl⟩ (by norm_num))
theorem R44221 : Reach 44221 := rs (se 3 (by rfl) ⟨8291, by rfl⟩) (B 16583 (by norm_num) ⟨8291, by rfl⟩ (by norm_num))
theorem R44257 : Reach 44257 := rs (se 2 (by rfl) ⟨16596, by rfl⟩) (B 33193 (by norm_num) ⟨16596, by rfl⟩ (by norm_num))
theorem R44293 : Reach 44293 := rs (se 4 (by rfl) ⟨4152, by rfl⟩) (B 8305 (by norm_num) ⟨4152, by rfl⟩ (by norm_num))
theorem R142613 : Reach 142613 := rs (se 6 (by rfl) ⟨3342, by rfl⟩) (B 6685 (by norm_num) ⟨3342, by rfl⟩ (by norm_num))
theorem R44317 : Reach 44317 := rs (se 3 (by rfl) ⟨8309, by rfl⟩) (B 16619 (by norm_num) ⟨8309, by rfl⟩ (by norm_num))
theorem R44321 : Reach 44321 := rs (se 2 (by rfl) ⟨16620, by rfl⟩) (B 33241 (by norm_num) ⟨16620, by rfl⟩ (by norm_num))
theorem R44329 : Reach 44329 := rs (se 2 (by rfl) ⟨16623, by rfl⟩) (B 33247 (by norm_num) ⟨16623, by rfl⟩ (by norm_num))
theorem R44365 : Reach 44365 := rs (se 3 (by rfl) ⟨8318, by rfl⟩) (B 16637 (by norm_num) ⟨8318, by rfl⟩ (by norm_num))
theorem R44401 : Reach 44401 := rs (se 2 (by rfl) ⟨16650, by rfl⟩) (B 33301 (by norm_num) ⟨16650, by rfl⟩ (by norm_num))
theorem R44437 : Reach 44437 := rs (se 6 (by rfl) ⟨1041, by rfl⟩) (B 2083 (by norm_num) ⟨1041, by rfl⟩ (by norm_num))
theorem R77213 : Reach 77213 := rs (se 3 (by rfl) ⟨14477, by rfl⟩) (B 28955 (by norm_num) ⟨14477, by rfl⟩ (by norm_num))
theorem R44473 : Reach 44473 := rs (se 2 (by rfl) ⟨16677, by rfl⟩) (B 33355 (by norm_num) ⟨16677, by rfl⟩ (by norm_num))
theorem R44509 : Reach 44509 := rs (se 3 (by rfl) ⟨8345, by rfl⟩) (B 16691 (by norm_num) ⟨8345, by rfl⟩ (by norm_num))
theorem R44545 : Reach 44545 := rs (se 2 (by rfl) ⟨16704, by rfl⟩) (B 33409 (by norm_num) ⟨16704, by rfl⟩ (by norm_num))
theorem R44581 : Reach 44581 := rs (se 4 (by rfl) ⟨4179, by rfl⟩) (B 8359 (by norm_num) ⟨4179, by rfl⟩ (by norm_num))
theorem R77365 : Reach 77365 := rs (se 5 (by rfl) ⟨3626, by rfl⟩) (B 7253 (by norm_num) ⟨3626, by rfl⟩ (by norm_num))
theorem R44617 : Reach 44617 := rs (se 2 (by rfl) ⟨16731, by rfl⟩) (B 33463 (by norm_num) ⟨16731, by rfl⟩ (by norm_num))
theorem R44653 : Reach 44653 := rs (se 3 (by rfl) ⟨8372, by rfl⟩) (B 16745 (by norm_num) ⟨8372, by rfl⟩ (by norm_num))
theorem R44689 : Reach 44689 := rs (se 2 (by rfl) ⟨16758, by rfl⟩) (B 33517 (by norm_num) ⟨16758, by rfl⟩ (by norm_num))
theorem R44693 : Reach 44693 := rs (se 6 (by rfl) ⟨1047, by rfl⟩) (B 2095 (by norm_num) ⟨1047, by rfl⟩ (by norm_num))
theorem R44725 : Reach 44725 := rs (se 5 (by rfl) ⟨2096, by rfl⟩) (B 4193 (by norm_num) ⟨2096, by rfl⟩ (by norm_num))
theorem R143045 : Reach 143045 := rs (se 4 (by rfl) ⟨13410, by rfl⟩) (B 26821 (by norm_num) ⟨13410, by rfl⟩ (by norm_num))
theorem R44761 : Reach 44761 := rs (se 2 (by rfl) ⟨16785, by rfl⟩) (B 33571 (by norm_num) ⟨16785, by rfl⟩ (by norm_num))
theorem R44797 : Reach 44797 := rs (se 3 (by rfl) ⟨8399, by rfl⟩) (B 16799 (by norm_num) ⟨8399, by rfl⟩ (by norm_num))
theorem R306965 : Reach 306965 := rs (se 6 (by rfl) ⟨7194, by rfl⟩) (B 14389 (by norm_num) ⟨7194, by rfl⟩ (by norm_num))
theorem R44833 : Reach 44833 := rs (se 2 (by rfl) ⟨16812, by rfl⟩) (B 33625 (by norm_num) ⟨16812, by rfl⟩ (by norm_num))
theorem R44869 : Reach 44869 := rs (se 4 (by rfl) ⟨4206, by rfl⟩) (B 8413 (by norm_num) ⟨4206, by rfl⟩ (by norm_num))
theorem R44885 : Reach 44885 := rs (se 9 (by rfl) ⟨131, by rfl⟩) (B 263 (by norm_num) ⟨131, by rfl⟩ (by norm_num))
theorem R77669 : Reach 77669 := rs (se 4 (by rfl) ⟨7281, by rfl⟩) (B 14563 (by norm_num) ⟨7281, by rfl⟩ (by norm_num))
theorem R44905 : Reach 44905 := rs (se 2 (by rfl) ⟨16839, by rfl⟩) (B 33679 (by norm_num) ⟨16839, by rfl⟩ (by norm_num))
theorem R44941 : Reach 44941 := rs (se 3 (by rfl) ⟨8426, by rfl⟩) (B 16853 (by norm_num) ⟨8426, by rfl⟩ (by norm_num))
theorem R470933 : Reach 470933 := rs (se 6 (by rfl) ⟨11037, by rfl⟩) (B 22075 (by norm_num) ⟨11037, by rfl⟩ (by norm_num))
theorem R44977 : Reach 44977 := rs (se 2 (by rfl) ⟨16866, by rfl⟩) (B 33733 (by norm_num) ⟨16866, by rfl⟩ (by norm_num))
theorem R45013 : Reach 45013 := rs (se 7 (by rfl) ⟨527, by rfl⟩) (B 1055 (by norm_num) ⟨527, by rfl⟩ (by norm_num))
theorem R45049 : Reach 45049 := rs (se 2 (by rfl) ⟨16893, by rfl⟩) (B 33787 (by norm_num) ⟨16893, by rfl⟩ (by norm_num))
theorem R45073 : Reach 45073 := rs (se 2 (by rfl) ⟨16902, by rfl⟩) (B 33805 (by norm_num) ⟨16902, by rfl⟩ (by norm_num))
theorem R45085 : Reach 45085 := rs (se 3 (by rfl) ⟨8453, by rfl⟩) (B 16907 (by norm_num) ⟨8453, by rfl⟩ (by norm_num))
theorem R45121 : Reach 45121 := rs (se 2 (by rfl) ⟨16920, by rfl⟩) (B 33841 (by norm_num) ⟨16920, by rfl⟩ (by norm_num))
theorem R45157 : Reach 45157 := rs (se 4 (by rfl) ⟨4233, by rfl⟩) (B 8467 (by norm_num) ⟨4233, by rfl⟩ (by norm_num))
theorem R143477 : Reach 143477 := rs (se 5 (by rfl) ⟨6725, by rfl⟩) (B 13451 (by norm_num) ⟨6725, by rfl⟩ (by norm_num))
theorem R45193 : Reach 45193 := rs (se 2 (by rfl) ⟨16947, by rfl⟩) (B 33895 (by norm_num) ⟨16947, by rfl⟩ (by norm_num))
theorem R45229 : Reach 45229 := rs (se 3 (by rfl) ⟨8480, by rfl⟩) (B 16961 (by norm_num) ⟨8480, by rfl⟩ (by norm_num))
theorem R45265 : Reach 45265 := rs (se 2 (by rfl) ⟨16974, by rfl⟩) (B 33949 (by norm_num) ⟨16974, by rfl⟩ (by norm_num))
theorem R45301 : Reach 45301 := rs (se 5 (by rfl) ⟨2123, by rfl⟩) (B 4247 (by norm_num) ⟨2123, by rfl⟩ (by norm_num))
theorem R209141 : Reach 209141 := rs (se 5 (by rfl) ⟨9803, by rfl⟩) (B 19607 (by norm_num) ⟨9803, by rfl⟩ (by norm_num))
theorem R45337 : Reach 45337 := rs (se 2 (by rfl) ⟨17001, by rfl⟩) (B 34003 (by norm_num) ⟨17001, by rfl⟩ (by norm_num))
theorem R45373 : Reach 45373 := rs (se 3 (by rfl) ⟨8507, by rfl⟩) (B 17015 (by norm_num) ⟨8507, by rfl⟩ (by norm_num))
theorem R45409 : Reach 45409 := rs (se 2 (by rfl) ⟨17028, by rfl⟩) (B 34057 (by norm_num) ⟨17028, by rfl⟩ (by norm_num))
theorem R45445 : Reach 45445 := rs (se 4 (by rfl) ⟨4260, by rfl⟩) (B 8521 (by norm_num) ⟨4260, by rfl⟩ (by norm_num))
theorem R45469 : Reach 45469 := rs (se 3 (by rfl) ⟨8525, by rfl⟩) (B 17051 (by norm_num) ⟨8525, by rfl⟩ (by norm_num))
theorem R45481 : Reach 45481 := rs (se 2 (by rfl) ⟨17055, by rfl⟩) (B 34111 (by norm_num) ⟨17055, by rfl⟩ (by norm_num))
theorem R307637 : Reach 307637 := rs (se 5 (by rfl) ⟨14420, by rfl⟩) (B 28841 (by norm_num) ⟨14420, by rfl⟩ (by norm_num))
theorem R45517 : Reach 45517 := rs (se 3 (by rfl) ⟨8534, by rfl⟩) (B 17069 (by norm_num) ⟨8534, by rfl⟩ (by norm_num))
theorem R45553 : Reach 45553 := rs (se 2 (by rfl) ⟨17082, by rfl⟩) (B 34165 (by norm_num) ⟨17082, by rfl⟩ (by norm_num))
theorem R45589 : Reach 45589 := rs (se 6 (by rfl) ⟨1068, by rfl⟩) (B 2137 (by norm_num) ⟨1068, by rfl⟩ (by norm_num))
theorem R143909 : Reach 143909 := rs (se 4 (by rfl) ⟨13491, by rfl⟩) (B 26983 (by norm_num) ⟨13491, by rfl⟩ (by norm_num))
theorem R45625 : Reach 45625 := rs (se 2 (by rfl) ⟨17109, by rfl⟩) (B 34219 (by norm_num) ⟨17109, by rfl⟩ (by norm_num))
theorem R78421 : Reach 78421 := rs (se 8 (by rfl) ⟨459, by rfl⟩) (B 919 (by norm_num) ⟨459, by rfl⟩ (by norm_num))
theorem R45661 : Reach 45661 := rs (se 3 (by rfl) ⟨8561, by rfl⟩) (B 17123 (by norm_num) ⟨8561, by rfl⟩ (by norm_num))
theorem R45697 : Reach 45697 := rs (se 2 (by rfl) ⟨17136, by rfl⟩) (B 34273 (by norm_num) ⟨17136, by rfl⟩ (by norm_num))
theorem R45733 : Reach 45733 := rs (se 4 (by rfl) ⟨4287, by rfl⟩) (B 8575 (by norm_num) ⟨4287, by rfl⟩ (by norm_num))
theorem R45769 : Reach 45769 := rs (se 2 (by rfl) ⟨17163, by rfl⟩) (B 34327 (by norm_num) ⟨17163, by rfl⟩ (by norm_num))
theorem R78565 : Reach 78565 := rs (se 4 (by rfl) ⟨7365, by rfl⟩) (B 14731 (by norm_num) ⟨7365, by rfl⟩ (by norm_num))
theorem R45805 : Reach 45805 := rs (se 3 (by rfl) ⟨8588, by rfl⟩) (B 17177 (by norm_num) ⟨8588, by rfl⟩ (by norm_num))
theorem R45841 : Reach 45841 := rs (se 2 (by rfl) ⟨17190, by rfl⟩) (B 34381 (by norm_num) ⟨17190, by rfl⟩ (by norm_num))
theorem R45877 : Reach 45877 := rs (se 5 (by rfl) ⟨2150, by rfl⟩) (B 4301 (by norm_num) ⟨2150, by rfl⟩ (by norm_num))
theorem R45893 : Reach 45893 := rs (se 4 (by rfl) ⟨4302, by rfl⟩) (B 8605 (by norm_num) ⟨4302, by rfl⟩ (by norm_num))
theorem R45913 : Reach 45913 := rs (se 2 (by rfl) ⟨17217, by rfl⟩) (B 34435 (by norm_num) ⟨17217, by rfl⟩ (by norm_num))
theorem R45949 : Reach 45949 := rs (se 3 (by rfl) ⟨8615, by rfl⟩) (B 17231 (by norm_num) ⟨8615, by rfl⟩ (by norm_num))
theorem R78725 : Reach 78725 := rs (se 4 (by rfl) ⟨7380, by rfl⟩) (B 14761 (by norm_num) ⟨7380, by rfl⟩ (by norm_num))
theorem R45985 : Reach 45985 := rs (se 2 (by rfl) ⟨17244, by rfl⟩) (B 34489 (by norm_num) ⟨17244, by rfl⟩ (by norm_num))
theorem R46021 : Reach 46021 := rs (se 4 (by rfl) ⟨4314, by rfl⟩) (B 8629 (by norm_num) ⟨4314, by rfl⟩ (by norm_num))
theorem R144341 : Reach 144341 := rs (se 7 (by rfl) ⟨1691, by rfl⟩) (B 3383 (by norm_num) ⟨1691, by rfl⟩ (by norm_num))
theorem R46057 : Reach 46057 := rs (se 2 (by rfl) ⟨17271, by rfl⟩) (B 34543 (by norm_num) ⟨17271, by rfl⟩ (by norm_num))
theorem R46093 : Reach 46093 := rs (se 3 (by rfl) ⟨8642, by rfl⟩) (B 17285 (by norm_num) ⟨8642, by rfl⟩ (by norm_num))
theorem R78869 : Reach 78869 := rs (se 6 (by rfl) ⟨1848, by rfl⟩) (B 3697 (by norm_num) ⟨1848, by rfl⟩ (by norm_num))
theorem R46129 : Reach 46129 := rs (se 2 (by rfl) ⟨17298, by rfl⟩) (B 34597 (by norm_num) ⟨17298, by rfl⟩ (by norm_num))
theorem R46165 : Reach 46165 := rs (se 8 (by rfl) ⟨270, by rfl⟩) (B 541 (by norm_num) ⟨270, by rfl⟩ (by norm_num))
theorem R46201 : Reach 46201 := rs (se 2 (by rfl) ⟨17325, by rfl⟩) (B 34651 (by norm_num) ⟨17325, by rfl⟩ (by norm_num))
theorem R46237 : Reach 46237 := rs (se 3 (by rfl) ⟨8669, by rfl⟩) (B 17339 (by norm_num) ⟨8669, by rfl⟩ (by norm_num))
theorem R46273 : Reach 46273 := rs (se 2 (by rfl) ⟨17352, by rfl⟩) (B 34705 (by norm_num) ⟨17352, by rfl⟩ (by norm_num))
theorem R46309 : Reach 46309 := rs (se 4 (by rfl) ⟨4341, by rfl⟩) (B 8683 (by norm_num) ⟨4341, by rfl⟩ (by norm_num))
theorem R46345 : Reach 46345 := rs (se 2 (by rfl) ⟨17379, by rfl⟩) (B 34759 (by norm_num) ⟨17379, by rfl⟩ (by norm_num))
theorem R46381 : Reach 46381 := rs (se 3 (by rfl) ⟨8696, by rfl⟩) (B 17393 (by norm_num) ⟨8696, by rfl⟩ (by norm_num))
theorem R79157 : Reach 79157 := rs (se 5 (by rfl) ⟨3710, by rfl⟩) (B 7421 (by norm_num) ⟨3710, by rfl⟩ (by norm_num))
theorem R46417 : Reach 46417 := rs (se 2 (by rfl) ⟨17406, by rfl⟩) (B 34813 (by norm_num) ⟨17406, by rfl⟩ (by norm_num))
theorem R46453 : Reach 46453 := rs (se 5 (by rfl) ⟨2177, by rfl⟩) (B 4355 (by norm_num) ⟨2177, by rfl⟩ (by norm_num))
theorem R144773 : Reach 144773 := rs (se 4 (by rfl) ⟨13572, by rfl⟩) (B 27145 (by norm_num) ⟨13572, by rfl⟩ (by norm_num))
theorem R46489 : Reach 46489 := rs (se 2 (by rfl) ⟨17433, by rfl⟩) (B 34867 (by norm_num) ⟨17433, by rfl⟩ (by norm_num))
theorem R46525 : Reach 46525 := rs (se 3 (by rfl) ⟨8723, by rfl⟩) (B 17447 (by norm_num) ⟨8723, by rfl⟩ (by norm_num))
theorem R79309 : Reach 79309 := rs (se 3 (by rfl) ⟨14870, by rfl⟩) (B 29741 (by norm_num) ⟨14870, by rfl⟩ (by norm_num))
theorem R46561 : Reach 46561 := rs (se 2 (by rfl) ⟨17460, by rfl⟩) (B 34921 (by norm_num) ⟨17460, by rfl⟩ (by norm_num))
theorem R46597 : Reach 46597 := rs (se 4 (by rfl) ⟨4368, by rfl⟩) (B 8737 (by norm_num) ⟨4368, by rfl⟩ (by norm_num))
theorem R79373 : Reach 79373 := rs (se 3 (by rfl) ⟨14882, by rfl⟩) (B 29765 (by norm_num) ⟨14882, by rfl⟩ (by norm_num))
theorem R46633 : Reach 46633 := rs (se 2 (by rfl) ⟨17487, by rfl⟩) (B 34975 (by norm_num) ⟨17487, by rfl⟩ (by norm_num))
theorem R46669 : Reach 46669 := rs (se 3 (by rfl) ⟨8750, by rfl⟩) (B 17501 (by norm_num) ⟨8750, by rfl⟩ (by norm_num))
theorem R46705 : Reach 46705 := rs (se 2 (by rfl) ⟨17514, by rfl⟩) (B 35029 (by norm_num) ⟨17514, by rfl⟩ (by norm_num))
theorem R46741 : Reach 46741 := rs (se 6 (by rfl) ⟨1095, by rfl⟩) (B 2191 (by norm_num) ⟨1095, by rfl⟩ (by norm_num))
theorem R46777 : Reach 46777 := rs (se 2 (by rfl) ⟨17541, by rfl⟩) (B 35083 (by norm_num) ⟨17541, by rfl⟩ (by norm_num))
theorem R46813 : Reach 46813 := rs (se 3 (by rfl) ⟨8777, by rfl⟩) (B 17555 (by norm_num) ⟨8777, by rfl⟩ (by norm_num))
theorem R112357 : Reach 112357 := rs (se 4 (by rfl) ⟨10533, by rfl⟩) (B 21067 (by norm_num) ⟨10533, by rfl⟩ (by norm_num))
theorem R46837 : Reach 46837 := rs (se 5 (by rfl) ⟨2195, by rfl⟩) (B 4391 (by norm_num) ⟨2195, by rfl⟩ (by norm_num))
theorem R79613 : Reach 79613 := rs (se 3 (by rfl) ⟨14927, by rfl⟩) (B 29855 (by norm_num) ⟨14927, by rfl⟩ (by norm_num))
theorem R46849 : Reach 46849 := rs (se 2 (by rfl) ⟨17568, by rfl⟩) (B 35137 (by norm_num) ⟨17568, by rfl⟩ (by norm_num))
theorem R46885 : Reach 46885 := rs (se 4 (by rfl) ⟨4395, by rfl⟩) (B 8791 (by norm_num) ⟨4395, by rfl⟩ (by norm_num))
theorem R46901 : Reach 46901 := rs (se 5 (by rfl) ⟨2198, by rfl⟩) (B 4397 (by norm_num) ⟨2198, by rfl⟩ (by norm_num))
theorem R145205 : Reach 145205 := rs (se 5 (by rfl) ⟨6806, by rfl⟩) (B 13613 (by norm_num) ⟨6806, by rfl⟩ (by norm_num))
theorem R46921 : Reach 46921 := rs (se 2 (by rfl) ⟨17595, by rfl⟩) (B 35191 (by norm_num) ⟨17595, by rfl⟩ (by norm_num))
theorem R46957 : Reach 46957 := rs (se 3 (by rfl) ⟨8804, by rfl⟩) (B 17609 (by norm_num) ⟨8804, by rfl⟩ (by norm_num))
theorem R178037 : Reach 178037 := rs (se 5 (by rfl) ⟨8345, by rfl⟩) (B 16691 (by norm_num) ⟨8345, by rfl⟩ (by norm_num))
theorem R46993 : Reach 46993 := rs (se 2 (by rfl) ⟨17622, by rfl⟩) (B 35245 (by norm_num) ⟨17622, by rfl⟩ (by norm_num))
theorem R47017 : Reach 47017 := rs (se 2 (by rfl) ⟨17631, by rfl⟩) (B 35263 (by norm_num) ⟨17631, by rfl⟩ (by norm_num))
theorem R47029 : Reach 47029 := rs (se 5 (by rfl) ⟨2204, by rfl⟩) (B 4409 (by norm_num) ⟨2204, by rfl⟩ (by norm_num))
theorem R47065 : Reach 47065 := rs (se 2 (by rfl) ⟨17649, by rfl⟩) (B 35299 (by norm_num) ⟨17649, by rfl⟩ (by norm_num))
theorem R47089 : Reach 47089 := rs (se 2 (by rfl) ⟨17658, by rfl⟩) (B 35317 (by norm_num) ⟨17658, by rfl⟩ (by norm_num))
theorem R47101 : Reach 47101 := rs (se 3 (by rfl) ⟨8831, by rfl⟩) (B 17663 (by norm_num) ⟨8831, by rfl⟩ (by norm_num))
theorem R47137 : Reach 47137 := rs (se 2 (by rfl) ⟨17676, by rfl⟩) (B 35353 (by norm_num) ⟨17676, by rfl⟩ (by norm_num))
theorem R47173 : Reach 47173 := rs (se 4 (by rfl) ⟨4422, by rfl⟩) (B 8845 (by norm_num) ⟨4422, by rfl⟩ (by norm_num))
theorem R47209 : Reach 47209 := rs (se 2 (by rfl) ⟨17703, by rfl⟩) (B 35407 (by norm_num) ⟨17703, by rfl⟩ (by norm_num))
theorem R47245 : Reach 47245 := rs (se 3 (by rfl) ⟨8858, by rfl⟩) (B 17717 (by norm_num) ⟨8858, by rfl⟩ (by norm_num))
theorem R47281 : Reach 47281 := rs (se 2 (by rfl) ⟨17730, by rfl⟩) (B 35461 (by norm_num) ⟨17730, by rfl⟩ (by norm_num))
theorem R47317 : Reach 47317 := rs (se 7 (by rfl) ⟨554, by rfl⟩) (B 1109 (by norm_num) ⟨554, by rfl⟩ (by norm_num))
theorem R47353 : Reach 47353 := rs (se 2 (by rfl) ⟨17757, by rfl⟩) (B 35515 (by norm_num) ⟨17757, by rfl⟩ (by norm_num))
theorem R47389 : Reach 47389 := rs (se 3 (by rfl) ⟨8885, by rfl⟩) (B 17771 (by norm_num) ⟨8885, by rfl⟩ (by norm_num))
theorem R47425 : Reach 47425 := rs (se 2 (by rfl) ⟨17784, by rfl⟩) (B 35569 (by norm_num) ⟨17784, by rfl⟩ (by norm_num))
theorem R47461 : Reach 47461 := rs (se 4 (by rfl) ⟨4449, by rfl⟩) (B 8899 (by norm_num) ⟨4449, by rfl⟩ (by norm_num))
theorem R47497 : Reach 47497 := rs (se 2 (by rfl) ⟨17811, by rfl⟩) (B 35623 (by norm_num) ⟨17811, by rfl⟩ (by norm_num))
theorem R47533 : Reach 47533 := rs (se 3 (by rfl) ⟨8912, by rfl⟩) (B 17825 (by norm_num) ⟨8912, by rfl⟩ (by norm_num))
theorem R47569 : Reach 47569 := rs (se 2 (by rfl) ⟨17838, by rfl⟩) (B 35677 (by norm_num) ⟨17838, by rfl⟩ (by norm_num))
theorem R47585 : Reach 47585 := rs (se 2 (by rfl) ⟨17844, by rfl⟩) (B 35689 (by norm_num) ⟨17844, by rfl⟩ (by norm_num))
theorem R47593 : Reach 47593 := rs (se 2 (by rfl) ⟨17847, by rfl⟩) (B 35695 (by norm_num) ⟨17847, by rfl⟩ (by norm_num))
theorem R80365 : Reach 80365 := rs (se 3 (by rfl) ⟨15068, by rfl⟩) (B 30137 (by norm_num) ⟨15068, by rfl⟩ (by norm_num))
theorem R47605 : Reach 47605 := rs (se 5 (by rfl) ⟨2231, by rfl⟩) (B 4463 (by norm_num) ⟨2231, by rfl⟩ (by norm_num))
theorem R47641 : Reach 47641 := rs (se 2 (by rfl) ⟨17865, by rfl⟩) (B 35731 (by norm_num) ⟨17865, by rfl⟩ (by norm_num))
theorem R47677 : Reach 47677 := rs (se 3 (by rfl) ⟨8939, by rfl⟩) (B 17879 (by norm_num) ⟨8939, by rfl⟩ (by norm_num))
theorem R47713 : Reach 47713 := rs (se 2 (by rfl) ⟨17892, by rfl⟩) (B 35785 (by norm_num) ⟨17892, by rfl⟩ (by norm_num))
theorem R113269 : Reach 113269 := rs (se 5 (by rfl) ⟨5309, by rfl⟩) (B 10619 (by norm_num) ⟨5309, by rfl⟩ (by norm_num))
theorem R80509 : Reach 80509 := rs (se 3 (by rfl) ⟨15095, by rfl⟩) (B 30191 (by norm_num) ⟨15095, by rfl⟩ (by norm_num))
theorem R47749 : Reach 47749 := rs (se 4 (by rfl) ⟨4476, by rfl⟩) (B 8953 (by norm_num) ⟨4476, by rfl⟩ (by norm_num))
theorem R47785 : Reach 47785 := rs (se 2 (by rfl) ⟨17919, by rfl⟩) (B 35839 (by norm_num) ⟨17919, by rfl⟩ (by norm_num))
theorem R47821 : Reach 47821 := rs (se 3 (by rfl) ⟨8966, by rfl⟩) (B 17933 (by norm_num) ⟨8966, by rfl⟩ (by norm_num))
theorem R47857 : Reach 47857 := rs (se 2 (by rfl) ⟨17946, by rfl⟩) (B 35893 (by norm_num) ⟨17946, by rfl⟩ (by norm_num))
theorem R211733 : Reach 211733 := rs (se 6 (by rfl) ⟨4962, by rfl⟩) (B 9925 (by norm_num) ⟨4962, by rfl⟩ (by norm_num))
theorem R47893 : Reach 47893 := rs (se 6 (by rfl) ⟨1122, by rfl⟩) (B 2245 (by norm_num) ⟨1122, by rfl⟩ (by norm_num))
theorem R80669 : Reach 80669 := rs (se 3 (by rfl) ⟨15125, by rfl⟩) (B 30251 (by norm_num) ⟨15125, by rfl⟩ (by norm_num))
theorem R47929 : Reach 47929 := rs (se 2 (by rfl) ⟨17973, by rfl⟩) (B 35947 (by norm_num) ⟨17973, by rfl⟩ (by norm_num))
theorem R47965 : Reach 47965 := rs (se 3 (by rfl) ⟨8993, by rfl⟩) (B 17987 (by norm_num) ⟨8993, by rfl⟩ (by norm_num))
theorem R48001 : Reach 48001 := rs (se 2 (by rfl) ⟨18000, by rfl⟩) (B 36001 (by norm_num) ⟨18000, by rfl⟩ (by norm_num))
theorem R48037 : Reach 48037 := rs (se 4 (by rfl) ⟨4503, by rfl⟩) (B 9007 (by norm_num) ⟨4503, by rfl⟩ (by norm_num))
theorem R80813 : Reach 80813 := rs (se 3 (by rfl) ⟨15152, by rfl⟩) (B 30305 (by norm_num) ⟨15152, by rfl⟩ (by norm_num))
theorem R48073 : Reach 48073 := rs (se 2 (by rfl) ⟨18027, by rfl⟩) (B 36055 (by norm_num) ⟨18027, by rfl⟩ (by norm_num))
theorem R506837 : Reach 506837 := rs (se 7 (by rfl) ⟨5939, by rfl⟩) (B 11879 (by norm_num) ⟨5939, by rfl⟩ (by norm_num))
theorem R48109 : Reach 48109 := rs (se 3 (by rfl) ⟨9020, by rfl⟩) (B 18041 (by norm_num) ⟨9020, by rfl⟩ (by norm_num))
theorem R80885 : Reach 80885 := rs (se 5 (by rfl) ⟨3791, by rfl⟩) (B 7583 (by norm_num) ⟨3791, by rfl⟩ (by norm_num))
theorem R48145 : Reach 48145 := rs (se 2 (by rfl) ⟨18054, by rfl⟩) (B 36109 (by norm_num) ⟨18054, by rfl⟩ (by norm_num))
theorem R48181 : Reach 48181 := rs (se 5 (by rfl) ⟨2258, by rfl⟩) (B 4517 (by norm_num) ⟨2258, by rfl⟩ (by norm_num))
theorem R48217 : Reach 48217 := rs (se 2 (by rfl) ⟨18081, by rfl⟩) (B 36163 (by norm_num) ⟨18081, by rfl⟩ (by norm_num))
theorem R244853 : Reach 244853 := rs (se 5 (by rfl) ⟨11477, by rfl⟩) (B 22955 (by norm_num) ⟨11477, by rfl⟩ (by norm_num))
theorem R48253 : Reach 48253 := rs (se 3 (by rfl) ⟨9047, by rfl⟩) (B 18095 (by norm_num) ⟨9047, by rfl⟩ (by norm_num))
theorem R48281 : Reach 48281 := rs (se 2 (by rfl) ⟨18105, by rfl⟩) (B 36211 (by norm_num) ⟨18105, by rfl⟩ (by norm_num))
theorem R48289 : Reach 48289 := rs (se 2 (by rfl) ⟨18108, by rfl⟩) (B 36217 (by norm_num) ⟨18108, by rfl⟩ (by norm_num))
theorem R113861 : Reach 113861 := rs (se 4 (by rfl) ⟨10674, by rfl⟩) (B 21349 (by norm_num) ⟨10674, by rfl⟩ (by norm_num))
theorem R48325 : Reach 48325 := rs (se 4 (by rfl) ⟨4530, by rfl⟩) (B 9061 (by norm_num) ⟨4530, by rfl⟩ (by norm_num))
theorem R81101 : Reach 81101 := rs (se 3 (by rfl) ⟨15206, by rfl⟩) (B 30413 (by norm_num) ⟨15206, by rfl⟩ (by norm_num))
theorem R48361 : Reach 48361 := rs (se 2 (by rfl) ⟨18135, by rfl⟩) (B 36271 (by norm_num) ⟨18135, by rfl⟩ (by norm_num))
theorem R48397 : Reach 48397 := rs (se 3 (by rfl) ⟨9074, by rfl⟩) (B 18149 (by norm_num) ⟨9074, by rfl⟩ (by norm_num))
theorem R48433 : Reach 48433 := rs (se 2 (by rfl) ⟨18162, by rfl⟩) (B 36325 (by norm_num) ⟨18162, by rfl⟩ (by norm_num))
theorem R48469 : Reach 48469 := rs (se 11 (by rfl) ⟨35, by rfl⟩) (B 71 (by norm_num) ⟨35, by rfl⟩ (by norm_num))
theorem R81253 : Reach 81253 := rs (se 4 (by rfl) ⟨7617, by rfl⟩) (B 15235 (by norm_num) ⟨7617, by rfl⟩ (by norm_num))
theorem R48505 : Reach 48505 := rs (se 2 (by rfl) ⟨18189, by rfl⟩) (B 36379 (by norm_num) ⟨18189, by rfl⟩ (by norm_num))
theorem R540053 : Reach 540053 := rs (se 6 (by rfl) ⟨12657, by rfl⟩) (B 25315 (by norm_num) ⟨12657, by rfl⟩ (by norm_num))
theorem R146933 : Reach 146933 := rs (se 5 (by rfl) ⟨6887, by rfl⟩) (B 13775 (by norm_num) ⟨6887, by rfl⟩ (by norm_num))
theorem R605717 : Reach 605717 := rs (se 6 (by rfl) ⟨14196, by rfl⟩) (B 28393 (by norm_num) ⟨14196, by rfl⟩ (by norm_num))
theorem R179813 : Reach 179813 := rs (se 4 (by rfl) ⟨16857, by rfl⟩) (B 33715 (by norm_num) ⟨16857, by rfl⟩ (by norm_num))
theorem R81557 : Reach 81557 := rs (se 6 (by rfl) ⟨1911, by rfl⟩) (B 3823 (by norm_num) ⟨1911, by rfl⟩ (by norm_num))
theorem R704213 : Reach 704213 := rs (se 7 (by rfl) ⟨8252, by rfl⟩) (B 16505 (by norm_num) ⟨8252, by rfl⟩ (by norm_num))
theorem R48881 : Reach 48881 := rs (se 2 (by rfl) ⟨18330, by rfl⟩) (B 36661 (by norm_num) ⟨18330, by rfl⟩ (by norm_num))
theorem R180053 : Reach 180053 := rs (se 9 (by rfl) ⟨527, by rfl⟩) (B 1055 (by norm_num) ⟨527, by rfl⟩ (by norm_num))
theorem R49189 : Reach 49189 := rs (se 4 (by rfl) ⟨4611, by rfl⟩) (B 9223 (by norm_num) ⟨4611, by rfl⟩ (by norm_num))
theorem R49285 : Reach 49285 := rs (se 4 (by rfl) ⟨4620, by rfl⟩) (B 9241 (by norm_num) ⟨4620, by rfl⟩ (by norm_num))
theorem R49333 : Reach 49333 := rs (se 5 (by rfl) ⟨2312, by rfl⟩) (B 4625 (by norm_num) ⟨2312, by rfl⟩ (by norm_num))
theorem R114869 : Reach 114869 := rs (se 5 (by rfl) ⟨5384, by rfl⟩) (B 10769 (by norm_num) ⟨5384, by rfl⟩ (by norm_num))
theorem R82325 : Reach 82325 := rs (se 6 (by rfl) ⟨1929, by rfl⟩) (B 3859 (by norm_num) ⟨1929, by rfl⟩ (by norm_num))
theorem R49673 : Reach 49673 := rs (se 2 (by rfl) ⟨18627, by rfl⟩) (B 37255 (by norm_num) ⟨18627, by rfl⟩ (by norm_num))
theorem R49729 : Reach 49729 := rs (se 2 (by rfl) ⟨18648, by rfl⟩) (B 37297 (by norm_num) ⟨18648, by rfl⟩ (by norm_num))
theorem R148085 : Reach 148085 := rs (se 5 (by rfl) ⟨6941, by rfl⟩) (B 13883 (by norm_num) ⟨6941, by rfl⟩ (by norm_num))
theorem R49825 : Reach 49825 := rs (se 2 (by rfl) ⟨18684, by rfl⟩) (B 37369 (by norm_num) ⟨18684, by rfl⟩ (by norm_num))
theorem R115445 : Reach 115445 := rs (se 5 (by rfl) ⟨5411, by rfl⟩) (B 10823 (by norm_num) ⟨5411, by rfl⟩ (by norm_num))
theorem R49997 : Reach 49997 := rs (se 3 (by rfl) ⟨9374, by rfl⟩) (B 18749 (by norm_num) ⟨9374, by rfl⟩ (by norm_num))
theorem R50053 : Reach 50053 := rs (se 4 (by rfl) ⟨4692, by rfl⟩) (B 9385 (by norm_num) ⟨4692, by rfl⟩ (by norm_num))
theorem R50149 : Reach 50149 := rs (se 4 (by rfl) ⟨4701, by rfl⟩) (B 9403 (by norm_num) ⟨4701, by rfl⟩ (by norm_num))
theorem R50321 : Reach 50321 := rs (se 2 (by rfl) ⟨18870, by rfl⟩) (B 37741 (by norm_num) ⟨18870, by rfl⟩ (by norm_num))
theorem R181397 : Reach 181397 := rs (se 6 (by rfl) ⟨4251, by rfl⟩) (B 8503 (by norm_num) ⟨4251, by rfl⟩ (by norm_num))
theorem R50377 : Reach 50377 := rs (se 2 (by rfl) ⟨18891, by rfl⟩) (B 37783 (by norm_num) ⟨18891, by rfl⟩ (by norm_num))
theorem R50473 : Reach 50473 := rs (se 2 (by rfl) ⟨18927, by rfl⟩) (B 37855 (by norm_num) ⟨18927, by rfl⟩ (by norm_num))
theorem R214325 : Reach 214325 := rs (se 5 (by rfl) ⟨10046, by rfl⟩) (B 20093 (by norm_num) ⟨10046, by rfl⟩ (by norm_num))
theorem R148837 : Reach 148837 := rs (se 4 (by rfl) ⟨13953, by rfl⟩) (B 27907 (by norm_num) ⟨13953, by rfl⟩ (by norm_num))
theorem R50549 : Reach 50549 := rs (se 5 (by rfl) ⟨2369, by rfl⟩) (B 4739 (by norm_num) ⟨2369, by rfl⟩ (by norm_num))
theorem R116117 : Reach 116117 := rs (se 6 (by rfl) ⟨2721, by rfl⟩) (B 5443 (by norm_num) ⟨2721, by rfl⟩ (by norm_num))
theorem R50645 : Reach 50645 := rs (se 7 (by rfl) ⟨593, by rfl⟩) (B 1187 (by norm_num) ⟨593, by rfl⟩ (by norm_num))
theorem R148949 : Reach 148949 := rs (se 7 (by rfl) ⟨1745, by rfl⟩) (B 3491 (by norm_num) ⟨1745, by rfl⟩ (by norm_num))
theorem R50701 : Reach 50701 := rs (se 3 (by rfl) ⟨9506, by rfl⟩) (B 19013 (by norm_num) ⟨9506, by rfl⟩ (by norm_num))
theorem R116245 : Reach 116245 := rs (se 6 (by rfl) ⟨2724, by rfl⟩) (B 5449 (by norm_num) ⟨2724, by rfl⟩ (by norm_num))
theorem R50717 : Reach 50717 := rs (se 3 (by rfl) ⟨9509, by rfl⟩) (B 19019 (by norm_num) ⟨9509, by rfl⟩ (by norm_num))
theorem R50797 : Reach 50797 := rs (se 3 (by rfl) ⟨9524, by rfl⟩) (B 19049 (by norm_num) ⟨9524, by rfl⟩ (by norm_num))
theorem R149141 : Reach 149141 := rs (se 6 (by rfl) ⟨3495, by rfl⟩) (B 6991 (by norm_num) ⟨3495, by rfl⟩ (by norm_num))
theorem R50905 : Reach 50905 := rs (se 2 (by rfl) ⟨19089, by rfl⟩) (B 38179 (by norm_num) ⟨19089, by rfl⟩ (by norm_num))
theorem R50969 : Reach 50969 := rs (se 2 (by rfl) ⟨19113, by rfl⟩) (B 38227 (by norm_num) ⟨19113, by rfl⟩ (by norm_num))
theorem R116549 : Reach 116549 := rs (se 4 (by rfl) ⟨10926, by rfl⟩) (B 21853 (by norm_num) ⟨10926, by rfl⟩ (by norm_num))
theorem R51025 : Reach 51025 := rs (se 2 (by rfl) ⟨19134, by rfl⟩) (B 38269 (by norm_num) ⟨19134, by rfl⟩ (by norm_num))
theorem R51121 : Reach 51121 := rs (se 2 (by rfl) ⟨19170, by rfl⟩) (B 38341 (by norm_num) ⟨19170, by rfl⟩ (by norm_num))
theorem R51241 : Reach 51241 := rs (se 2 (by rfl) ⟨19215, by rfl⟩) (B 38431 (by norm_num) ⟨19215, by rfl⟩ (by norm_num))
theorem R182341 : Reach 182341 := rs (se 4 (by rfl) ⟨17094, by rfl⟩) (B 34189 (by norm_num) ⟨17094, by rfl⟩ (by norm_num))
theorem R51293 : Reach 51293 := rs (se 3 (by rfl) ⟨9617, by rfl⟩) (B 19235 (by norm_num) ⟨9617, by rfl⟩ (by norm_num))
theorem R51349 : Reach 51349 := rs (se 6 (by rfl) ⟨1203, by rfl⟩) (B 2407 (by norm_num) ⟨1203, by rfl⟩ (by norm_num))
theorem R84149 : Reach 84149 := rs (se 5 (by rfl) ⟨3944, by rfl⟩) (B 7889 (by norm_num) ⟨3944, by rfl⟩ (by norm_num))
theorem R51445 : Reach 51445 := rs (se 5 (by rfl) ⟨2411, by rfl⟩) (B 4823 (by norm_num) ⟨2411, by rfl⟩ (by norm_num))
theorem R51553 : Reach 51553 := rs (se 2 (by rfl) ⟨19332, by rfl⟩) (B 38665 (by norm_num) ⟨19332, by rfl⟩ (by norm_num))
theorem R51617 : Reach 51617 := rs (se 2 (by rfl) ⟨19356, by rfl⟩) (B 38713 (by norm_num) ⟨19356, by rfl⟩ (by norm_num))
theorem R84397 : Reach 84397 := rs (se 3 (by rfl) ⟨15824, by rfl⟩) (B 31649 (by norm_num) ⟨15824, by rfl⟩ (by norm_num))
theorem R51673 : Reach 51673 := rs (se 2 (by rfl) ⟨19377, by rfl⟩) (B 38755 (by norm_num) ⟨19377, by rfl⟩ (by norm_num))
theorem R117301 : Reach 117301 := rs (se 5 (by rfl) ⟨5498, by rfl⟩) (B 10997 (by norm_num) ⟨5498, by rfl⟩ (by norm_num))
theorem R51769 : Reach 51769 := rs (se 2 (by rfl) ⟨19413, by rfl⟩) (B 38827 (by norm_num) ⟨19413, by rfl⟩ (by norm_num))
theorem R84653 : Reach 84653 := rs (se 3 (by rfl) ⟨15872, by rfl⟩) (B 31745 (by norm_num) ⟨15872, by rfl⟩ (by norm_num))
theorem R51941 : Reach 51941 := rs (se 4 (by rfl) ⟨4869, by rfl⟩) (B 9739 (by norm_num) ⟨4869, by rfl⟩ (by norm_num))
theorem R51997 : Reach 51997 := rs (se 3 (by rfl) ⟨9749, by rfl⟩) (B 19499 (by norm_num) ⟨9749, by rfl⟩ (by norm_num))
theorem R52093 : Reach 52093 := rs (se 3 (by rfl) ⟨9767, by rfl⟩) (B 19535 (by norm_num) ⟨9767, by rfl⟩ (by norm_num))
theorem R84901 : Reach 84901 := rs (se 4 (by rfl) ⟨7959, by rfl⟩) (B 15919 (by norm_num) ⟨7959, by rfl⟩ (by norm_num))
theorem R216053 : Reach 216053 := rs (se 5 (by rfl) ⟨10127, by rfl⟩) (B 20255 (by norm_num) ⟨10127, by rfl⟩ (by norm_num))
theorem R52589 : Reach 52589 := rs (se 3 (by rfl) ⟨9860, by rfl⟩) (B 19721 (by norm_num) ⟨9860, by rfl⟩ (by norm_num))
theorem R52645 : Reach 52645 := rs (se 4 (by rfl) ⟨4935, by rfl⟩) (B 9871 (by norm_num) ⟨4935, by rfl⟩ (by norm_num))
theorem R52741 : Reach 52741 := rs (se 4 (by rfl) ⟨4944, by rfl⟩) (B 9889 (by norm_num) ⟨4944, by rfl⟩ (by norm_num))
theorem R183829 : Reach 183829 := rs (se 6 (by rfl) ⟨4308, by rfl⟩) (B 8617 (by norm_num) ⟨4308, by rfl⟩ (by norm_num))
theorem R183845 : Reach 183845 := rs (se 4 (by rfl) ⟨17235, by rfl⟩) (B 34471 (by norm_num) ⟨17235, by rfl⟩ (by norm_num))
theorem R380533 : Reach 380533 := rs (se 5 (by rfl) ⟨17837, by rfl⟩) (B 35675 (by norm_num) ⟨17837, by rfl⟩ (by norm_num))
theorem R151253 : Reach 151253 := rs (se 7 (by rfl) ⟨1772, by rfl⟩) (B 3545 (by norm_num) ⟨1772, by rfl⟩ (by norm_num))
theorem R85781 : Reach 85781 := rs (se 6 (by rfl) ⟨2010, by rfl⟩) (B 4021 (by norm_num) ⟨2010, by rfl⟩ (by norm_num))
theorem R85789 : Reach 85789 := rs (se 3 (by rfl) ⟨16085, by rfl⟩) (B 32171 (by norm_num) ⟨16085, by rfl⟩ (by norm_num))
theorem R216917 : Reach 216917 := rs (se 9 (by rfl) ⟨635, by rfl⟩) (B 1271 (by norm_num) ⟨635, by rfl⟩ (by norm_num))
theorem R53149 : Reach 53149 := rs (se 3 (by rfl) ⟨9965, by rfl⟩) (B 19931 (by norm_num) ⟨9965, by rfl⟩ (by norm_num))
theorem R151541 : Reach 151541 := rs (se 5 (by rfl) ⟨7103, by rfl⟩) (B 14207 (by norm_num) ⟨7103, by rfl⟩ (by norm_num))
theorem R53237 : Reach 53237 := rs (se 5 (by rfl) ⟨2495, by rfl⟩) (B 4991 (by norm_num) ⟨2495, by rfl⟩ (by norm_num))
theorem R315413 : Reach 315413 := rs (se 6 (by rfl) ⟨7392, by rfl⟩) (B 14785 (by norm_num) ⟨7392, by rfl⟩ (by norm_num))
theorem R53293 : Reach 53293 := rs (se 3 (by rfl) ⟨9992, by rfl⟩) (B 19985 (by norm_num) ⟨9992, by rfl⟩ (by norm_num))
theorem R53389 : Reach 53389 := rs (se 3 (by rfl) ⟨10010, by rfl⟩) (B 20021 (by norm_num) ⟨10010, by rfl⟩ (by norm_num))
theorem R86285 : Reach 86285 := rs (se 3 (by rfl) ⟨16178, by rfl⟩) (B 32357 (by norm_num) ⟨16178, by rfl⟩ (by norm_num))
theorem R86341 : Reach 86341 := rs (se 4 (by rfl) ⟨8094, by rfl⟩) (B 16189 (by norm_num) ⟨8094, by rfl⟩ (by norm_num))
theorem R53885 : Reach 53885 := rs (se 3 (by rfl) ⟨10103, by rfl⟩) (B 20207 (by norm_num) ⟨10103, by rfl⟩ (by norm_num))
theorem R53941 : Reach 53941 := rs (se 5 (by rfl) ⟨2528, by rfl⟩) (B 5057 (by norm_num) ⟨2528, by rfl⟩ (by norm_num))
theorem R53989 : Reach 53989 := rs (se 4 (by rfl) ⟨5061, by rfl⟩) (B 10123 (by norm_num) ⟨5061, by rfl⟩ (by norm_num))
theorem R54037 : Reach 54037 := rs (se 6 (by rfl) ⟨1266, by rfl⟩) (B 2533 (by norm_num) ⟨1266, by rfl⟩ (by norm_num))
theorem R87173 : Reach 87173 := rs (se 4 (by rfl) ⟨8172, by rfl⟩) (B 16345 (by norm_num) ⟨8172, by rfl⟩ (by norm_num))
theorem R152725 : Reach 152725 := rs (se 6 (by rfl) ⟨3579, by rfl⟩) (B 7159 (by norm_num) ⟨3579, by rfl⟩ (by norm_num))
theorem R87293 : Reach 87293 := rs (se 3 (by rfl) ⟨16367, by rfl⟩) (B 32735 (by norm_num) ⟨16367, by rfl⟩ (by norm_num))
theorem R54533 : Reach 54533 := rs (se 4 (by rfl) ⟨5112, by rfl⟩) (B 10225 (by norm_num) ⟨5112, by rfl⟩ (by norm_num))
theorem R120149 : Reach 120149 := rs (se 15 (by rfl) ⟨5, by rfl⟩) (B 11 (by norm_num) ⟨5, by rfl⟩ (by norm_num))
theorem R153029 : Reach 153029 := rs (se 4 (by rfl) ⟨14346, by rfl⟩) (B 28693 (by norm_num) ⟨14346, by rfl⟩ (by norm_num))
theorem R185797 : Reach 185797 := rs (se 4 (by rfl) ⟨17418, by rfl⟩) (B 34837 (by norm_num) ⟨17418, by rfl⟩ (by norm_num))
theorem R87925 : Reach 87925 := rs (se 5 (by rfl) ⟨4121, by rfl⟩) (B 8243 (by norm_num) ⟨4121, by rfl⟩ (by norm_num))
theorem R88037 : Reach 88037 := rs (se 4 (by rfl) ⟨8253, by rfl⟩) (B 16507 (by norm_num) ⟨8253, by rfl⟩ (by norm_num))
theorem R88109 : Reach 88109 := rs (se 3 (by rfl) ⟨16520, by rfl⟩) (B 33041 (by norm_num) ⟨16520, by rfl⟩ (by norm_num))
theorem R88181 : Reach 88181 := rs (se 5 (by rfl) ⟨4133, by rfl⟩) (B 8267 (by norm_num) ⟨4133, by rfl⟩ (by norm_num))
theorem R317621 : Reach 317621 := rs (se 5 (by rfl) ⟨14888, by rfl⟩) (B 29777 (by norm_num) ⟨14888, by rfl⟩ (by norm_num))
theorem R88253 : Reach 88253 := rs (se 3 (by rfl) ⟨16547, by rfl⟩) (B 33095 (by norm_num) ⟨16547, by rfl⟩ (by norm_num))
theorem R88325 : Reach 88325 := rs (se 4 (by rfl) ⟨8280, by rfl⟩) (B 16561 (by norm_num) ⟨8280, by rfl⟩ (by norm_num))
theorem R88397 : Reach 88397 := rs (se 3 (by rfl) ⟨16574, by rfl⟩) (B 33149 (by norm_num) ⟨16574, by rfl⟩ (by norm_num))
theorem R88469 : Reach 88469 := rs (se 6 (by rfl) ⟨2073, by rfl⟩) (B 4147 (by norm_num) ⟨2073, by rfl⟩ (by norm_num))
theorem R88541 : Reach 88541 := rs (se 3 (by rfl) ⟨16601, by rfl⟩) (B 33203 (by norm_num) ⟨16601, by rfl⟩ (by norm_num))
theorem R121333 : Reach 121333 := rs (se 5 (by rfl) ⟨5687, by rfl⟩) (B 11375 (by norm_num) ⟨5687, by rfl⟩ (by norm_num))
theorem R55837 : Reach 55837 := rs (se 3 (by rfl) ⟨10469, by rfl⟩) (B 20939 (by norm_num) ⟨10469, by rfl⟩ (by norm_num))
theorem R88613 : Reach 88613 := rs (se 4 (by rfl) ⟨8307, by rfl⟩) (B 16615 (by norm_num) ⟨8307, by rfl⟩ (by norm_num))
theorem R88685 : Reach 88685 := rs (se 3 (by rfl) ⟨16628, by rfl⟩) (B 33257 (by norm_num) ⟨16628, by rfl⟩ (by norm_num))
theorem R121493 : Reach 121493 := rs (se 6 (by rfl) ⟨2847, by rfl⟩) (B 5695 (by norm_num) ⟨2847, by rfl⟩ (by norm_num))
theorem R88757 : Reach 88757 := rs (se 5 (by rfl) ⟨4160, by rfl⟩) (B 8321 (by norm_num) ⟨4160, by rfl⟩ (by norm_num))
theorem R88813 : Reach 88813 := rs (se 3 (by rfl) ⟨16652, by rfl⟩) (B 33305 (by norm_num) ⟨16652, by rfl⟩ (by norm_num))
theorem R416501 : Reach 416501 := rs (se 5 (by rfl) ⟨19523, by rfl⟩) (B 39047 (by norm_num) ⟨19523, by rfl⟩ (by norm_num))
theorem R88829 : Reach 88829 := rs (se 3 (by rfl) ⟨16655, by rfl⟩) (B 33311 (by norm_num) ⟨16655, by rfl⟩ (by norm_num))
theorem R88901 : Reach 88901 := rs (se 4 (by rfl) ⟨8334, by rfl⟩) (B 16669 (by norm_num) ⟨8334, by rfl⟩ (by norm_num))
theorem R88933 : Reach 88933 := rs (se 4 (by rfl) ⟨8337, by rfl⟩) (B 16675 (by norm_num) ⟨8337, by rfl⟩ (by norm_num))
theorem R121733 : Reach 121733 := rs (se 4 (by rfl) ⟨11412, by rfl⟩) (B 22825 (by norm_num) ⟨11412, by rfl⟩ (by norm_num))
theorem R88973 : Reach 88973 := rs (se 3 (by rfl) ⟨16682, by rfl⟩) (B 33365 (by norm_num) ⟨16682, by rfl⟩ (by norm_num))
theorem R89045 : Reach 89045 := rs (se 7 (by rfl) ⟨1043, by rfl⟩) (B 2087 (by norm_num) ⟨1043, by rfl⟩ (by norm_num))
theorem R89117 : Reach 89117 := rs (se 3 (by rfl) ⟨16709, by rfl⟩) (B 33419 (by norm_num) ⟨16709, by rfl⟩ (by norm_num))
theorem R121925 : Reach 121925 := rs (se 4 (by rfl) ⟨11430, by rfl⟩) (B 22861 (by norm_num) ⟨11430, by rfl⟩ (by norm_num))
theorem R89189 : Reach 89189 := rs (se 4 (by rfl) ⟨8361, by rfl⟩) (B 16723 (by norm_num) ⟨8361, by rfl⟩ (by norm_num))
theorem R89261 : Reach 89261 := rs (se 3 (by rfl) ⟨16736, by rfl⟩) (B 33473 (by norm_num) ⟨16736, by rfl⟩ (by norm_num))
theorem R89333 : Reach 89333 := rs (se 5 (by rfl) ⟨4187, by rfl⟩) (B 8375 (by norm_num) ⟨4187, by rfl⟩ (by norm_num))
theorem R253205 : Reach 253205 := rs (se 6 (by rfl) ⟨5934, by rfl⟩) (B 11869 (by norm_num) ⟨5934, by rfl⟩ (by norm_num))
theorem R56629 : Reach 56629 := rs (se 5 (by rfl) ⟨2654, by rfl⟩) (B 5309 (by norm_num) ⟨2654, by rfl⟩ (by norm_num))
theorem R89405 : Reach 89405 := rs (se 3 (by rfl) ⟨16763, by rfl⟩) (B 33527 (by norm_num) ⟨16763, by rfl⟩ (by norm_num))
theorem R89477 : Reach 89477 := rs (se 4 (by rfl) ⟨8388, by rfl⟩) (B 16777 (by norm_num) ⟨8388, by rfl⟩ (by norm_num))
theorem R89549 : Reach 89549 := rs (se 3 (by rfl) ⟨16790, by rfl⟩) (B 33581 (by norm_num) ⟨16790, by rfl⟩ (by norm_num))
theorem R155141 : Reach 155141 := rs (se 4 (by rfl) ⟨14544, by rfl⟩) (B 29089 (by norm_num) ⟨14544, by rfl⟩ (by norm_num))
theorem R89621 : Reach 89621 := rs (se 6 (by rfl) ⟨2100, by rfl⟩) (B 4201 (by norm_num) ⟨2100, by rfl⟩ (by norm_num))
theorem R89693 : Reach 89693 := rs (se 3 (by rfl) ⟨16817, by rfl⟩) (B 33635 (by norm_num) ⟨16817, by rfl⟩ (by norm_num))
theorem R56965 : Reach 56965 := rs (se 4 (by rfl) ⟨5340, by rfl⟩) (B 10681 (by norm_num) ⟨5340, by rfl⟩ (by norm_num))
theorem R89765 : Reach 89765 := rs (se 4 (by rfl) ⟨8415, by rfl⟩) (B 16831 (by norm_num) ⟨8415, by rfl⟩ (by norm_num))
theorem R89837 : Reach 89837 := rs (se 3 (by rfl) ⟨16844, by rfl⟩) (B 33689 (by norm_num) ⟨16844, by rfl⟩ (by norm_num))
theorem R89885 : Reach 89885 := rs (se 3 (by rfl) ⟨16853, by rfl⟩) (B 33707 (by norm_num) ⟨16853, by rfl⟩ (by norm_num))
theorem R155429 : Reach 155429 := rs (se 4 (by rfl) ⟨14571, by rfl⟩) (B 29143 (by norm_num) ⟨14571, by rfl⟩ (by norm_num))
theorem R89909 : Reach 89909 := rs (se 5 (by rfl) ⟨4214, by rfl⟩) (B 8429 (by norm_num) ⟨4214, by rfl⟩ (by norm_num))
theorem R384821 : Reach 384821 := rs (se 5 (by rfl) ⟨18038, by rfl⟩) (B 36077 (by norm_num) ⟨18038, by rfl⟩ (by norm_num))
theorem R57181 : Reach 57181 := rs (se 3 (by rfl) ⟨10721, by rfl⟩) (B 21443 (by norm_num) ⟨10721, by rfl⟩ (by norm_num))
theorem R89957 : Reach 89957 := rs (se 4 (by rfl) ⟨8433, by rfl⟩) (B 16867 (by norm_num) ⟨8433, by rfl⟩ (by norm_num))
theorem R89981 : Reach 89981 := rs (se 3 (by rfl) ⟨16871, by rfl⟩) (B 33743 (by norm_num) ⟨16871, by rfl⟩ (by norm_num))
theorem R90053 : Reach 90053 := rs (se 4 (by rfl) ⟨8442, by rfl⟩) (B 16885 (by norm_num) ⟨8442, by rfl⟩ (by norm_num))
theorem R90077 : Reach 90077 := rs (se 3 (by rfl) ⟨16889, by rfl⟩) (B 33779 (by norm_num) ⟨16889, by rfl⟩ (by norm_num))
theorem R90125 : Reach 90125 := rs (se 3 (by rfl) ⟨16898, by rfl⟩) (B 33797 (by norm_num) ⟨16898, by rfl⟩ (by norm_num))
theorem R90197 : Reach 90197 := rs (se 8 (by rfl) ⟨528, by rfl⟩) (B 1057 (by norm_num) ⟨528, by rfl⟩ (by norm_num))
theorem R90269 : Reach 90269 := rs (se 3 (by rfl) ⟨16925, by rfl⟩) (B 33851 (by norm_num) ⟨16925, by rfl⟩ (by norm_num))
theorem R90317 : Reach 90317 := rs (se 3 (by rfl) ⟨16934, by rfl⟩) (B 33869 (by norm_num) ⟨16934, by rfl⟩ (by norm_num))
theorem R57557 : Reach 57557 := rs (se 7 (by rfl) ⟨674, by rfl⟩) (B 1349 (by norm_num) ⟨674, by rfl⟩ (by norm_num))
theorem R90341 : Reach 90341 := rs (se 4 (by rfl) ⟨8469, by rfl⟩) (B 16939 (by norm_num) ⟨8469, by rfl⟩ (by norm_num))
theorem R90413 : Reach 90413 := rs (se 3 (by rfl) ⟨16952, by rfl⟩) (B 33905 (by norm_num) ⟨16952, by rfl⟩ (by norm_num))
theorem R90445 : Reach 90445 := rs (se 3 (by rfl) ⟨16958, by rfl⟩) (B 33917 (by norm_num) ⟨16958, by rfl⟩ (by norm_num))
theorem R90485 : Reach 90485 := rs (se 5 (by rfl) ⟨4241, by rfl⟩) (B 8483 (by norm_num) ⟨4241, by rfl⟩ (by norm_num))
theorem R90557 : Reach 90557 := rs (se 3 (by rfl) ⟨16979, by rfl⟩) (B 33959 (by norm_num) ⟨16979, by rfl⟩ (by norm_num))
theorem R90629 : Reach 90629 := rs (se 4 (by rfl) ⟨8496, by rfl⟩) (B 16993 (by norm_num) ⟨8496, by rfl⟩ (by norm_num))
theorem R221717 : Reach 221717 := rs (se 6 (by rfl) ⟨5196, by rfl⟩) (B 10393 (by norm_num) ⟨5196, by rfl⟩ (by norm_num))
theorem R90701 : Reach 90701 := rs (se 3 (by rfl) ⟨17006, by rfl⟩) (B 34013 (by norm_num) ⟨17006, by rfl⟩ (by norm_num))
theorem R90773 : Reach 90773 := rs (se 6 (by rfl) ⟨2127, by rfl⟩) (B 4255 (by norm_num) ⟨2127, by rfl⟩ (by norm_num))
theorem R90821 : Reach 90821 := rs (se 4 (by rfl) ⟨8514, by rfl⟩) (B 17029 (by norm_num) ⟨8514, by rfl⟩ (by norm_num))
theorem R90829 : Reach 90829 := rs (se 3 (by rfl) ⟨17030, by rfl⟩) (B 34061 (by norm_num) ⟨17030, by rfl⟩ (by norm_num))
theorem R320213 : Reach 320213 := rs (se 7 (by rfl) ⟨3752, by rfl⟩) (B 7505 (by norm_num) ⟨3752, by rfl⟩ (by norm_num))
theorem R90845 : Reach 90845 := rs (se 3 (by rfl) ⟨17033, by rfl⟩) (B 34067 (by norm_num) ⟨17033, by rfl⟩ (by norm_num))
theorem R90917 : Reach 90917 := rs (se 4 (by rfl) ⟨8523, by rfl⟩) (B 17047 (by norm_num) ⟨8523, by rfl⟩ (by norm_num))
theorem R90989 : Reach 90989 := rs (se 3 (by rfl) ⟨17060, by rfl⟩) (B 34121 (by norm_num) ⟨17060, by rfl⟩ (by norm_num))
theorem R418709 : Reach 418709 := rs (se 6 (by rfl) ⟨9813, by rfl⟩) (B 19627 (by norm_num) ⟨9813, by rfl⟩ (by norm_num))
theorem R91061 : Reach 91061 := rs (se 5 (by rfl) ⟨4268, by rfl⟩) (B 8537 (by norm_num) ⟨4268, by rfl⟩ (by norm_num))
theorem R156613 : Reach 156613 := rs (se 4 (by rfl) ⟨14682, by rfl⟩) (B 29365 (by norm_num) ⟨14682, by rfl⟩ (by norm_num))
theorem R91133 : Reach 91133 := rs (se 3 (by rfl) ⟨17087, by rfl⟩) (B 34175 (by norm_num) ⟨17087, by rfl⟩ (by norm_num))
theorem R91205 : Reach 91205 := rs (se 4 (by rfl) ⟨8550, by rfl⟩) (B 17101 (by norm_num) ⟨8550, by rfl⟩ (by norm_num))
theorem R91277 : Reach 91277 := rs (se 3 (by rfl) ⟨17114, by rfl⟩) (B 34229 (by norm_num) ⟨17114, by rfl⟩ (by norm_num))
theorem R58549 : Reach 58549 := rs (se 5 (by rfl) ⟨2744, by rfl⟩) (B 5489 (by norm_num) ⟨2744, by rfl⟩ (by norm_num))
theorem R91349 : Reach 91349 := rs (se 7 (by rfl) ⟨1070, by rfl⟩) (B 2141 (by norm_num) ⟨1070, by rfl⟩ (by norm_num))
theorem R156917 : Reach 156917 := rs (se 5 (by rfl) ⟨7355, by rfl⟩) (B 14711 (by norm_num) ⟨7355, by rfl⟩ (by norm_num))
theorem R91421 : Reach 91421 := rs (se 3 (by rfl) ⟨17141, by rfl⟩) (B 34283 (by norm_num) ⟨17141, by rfl⟩ (by norm_num))
theorem R58685 : Reach 58685 := rs (se 3 (by rfl) ⟨11003, by rfl⟩) (B 22007 (by norm_num) ⟨11003, by rfl⟩ (by norm_num))
theorem R58709 : Reach 58709 := rs (se 12 (by rfl) ⟨21, by rfl⟩) (B 43 (by norm_num) ⟨21, by rfl⟩ (by norm_num))
theorem R91493 : Reach 91493 := rs (se 4 (by rfl) ⟨8577, by rfl⟩) (B 17155 (by norm_num) ⟨8577, by rfl⟩ (by norm_num))
theorem R58733 : Reach 58733 := rs (se 3 (by rfl) ⟨11012, by rfl⟩) (B 22025 (by norm_num) ⟨11012, by rfl⟩ (by norm_num))
theorem R58757 : Reach 58757 := rs (se 4 (by rfl) ⟨5508, by rfl⟩) (B 11017 (by norm_num) ⟨5508, by rfl⟩ (by norm_num))
theorem R58781 : Reach 58781 := rs (se 3 (by rfl) ⟨11021, by rfl⟩) (B 22043 (by norm_num) ⟨11021, by rfl⟩ (by norm_num))
theorem R91565 : Reach 91565 := rs (se 3 (by rfl) ⟨17168, by rfl⟩) (B 34337 (by norm_num) ⟨17168, by rfl⟩ (by norm_num))
theorem R58805 : Reach 58805 := rs (se 5 (by rfl) ⟨2756, by rfl⟩) (B 5513 (by norm_num) ⟨2756, by rfl⟩ (by norm_num))
theorem R58829 : Reach 58829 := rs (se 3 (by rfl) ⟨11030, by rfl⟩) (B 22061 (by norm_num) ⟨11030, by rfl⟩ (by norm_num))
theorem R58853 : Reach 58853 := rs (se 4 (by rfl) ⟨5517, by rfl⟩) (B 11035 (by norm_num) ⟨5517, by rfl⟩ (by norm_num))
theorem R91637 : Reach 91637 := rs (se 5 (by rfl) ⟨4295, by rfl⟩) (B 8591 (by norm_num) ⟨4295, by rfl⟩ (by norm_num))
theorem R58877 : Reach 58877 := rs (se 3 (by rfl) ⟨11039, by rfl⟩) (B 22079 (by norm_num) ⟨11039, by rfl⟩ (by norm_num))
theorem R58901 : Reach 58901 := rs (se 6 (by rfl) ⟨1380, by rfl⟩) (B 2761 (by norm_num) ⟨1380, by rfl⟩ (by norm_num))
theorem R189989 : Reach 189989 := rs (se 4 (by rfl) ⟨17811, by rfl⟩) (B 35623 (by norm_num) ⟨17811, by rfl⟩ (by norm_num))
theorem R58925 : Reach 58925 := rs (se 3 (by rfl) ⟨11048, by rfl⟩) (B 22097 (by norm_num) ⟨11048, by rfl⟩ (by norm_num))
theorem R91709 : Reach 91709 := rs (se 3 (by rfl) ⟨17195, by rfl⟩) (B 34391 (by norm_num) ⟨17195, by rfl⟩ (by norm_num))
theorem R58949 : Reach 58949 := rs (se 4 (by rfl) ⟨5526, by rfl⟩) (B 11053 (by norm_num) ⟨5526, by rfl⟩ (by norm_num))
theorem R58973 : Reach 58973 := rs (se 3 (by rfl) ⟨11057, by rfl⟩) (B 22115 (by norm_num) ⟨11057, by rfl⟩ (by norm_num))
theorem R58981 : Reach 58981 := rs (se 4 (by rfl) ⟨5529, by rfl⟩) (B 11059 (by norm_num) ⟨5529, by rfl⟩ (by norm_num))
theorem R58997 : Reach 58997 := rs (se 5 (by rfl) ⟨2765, by rfl⟩) (B 5531 (by norm_num) ⟨2765, by rfl⟩ (by norm_num))
theorem R91781 : Reach 91781 := rs (se 4 (by rfl) ⟨8604, by rfl⟩) (B 17209 (by norm_num) ⟨8604, by rfl⟩ (by norm_num))
theorem R59021 : Reach 59021 := rs (se 3 (by rfl) ⟨11066, by rfl⟩) (B 22133 (by norm_num) ⟨11066, by rfl⟩ (by norm_num))
theorem R59045 : Reach 59045 := rs (se 4 (by rfl) ⟨5535, by rfl⟩) (B 11071 (by norm_num) ⟨5535, by rfl⟩ (by norm_num))
theorem R59069 : Reach 59069 := rs (se 3 (by rfl) ⟨11075, by rfl⟩) (B 22151 (by norm_num) ⟨11075, by rfl⟩ (by norm_num))
theorem R91853 : Reach 91853 := rs (se 3 (by rfl) ⟨17222, by rfl⟩) (B 34445 (by norm_num) ⟨17222, by rfl⟩ (by norm_num))
theorem R59093 : Reach 59093 := rs (se 7 (by rfl) ⟨692, by rfl⟩) (B 1385 (by norm_num) ⟨692, by rfl⟩ (by norm_num))
theorem R59117 : Reach 59117 := rs (se 3 (by rfl) ⟨11084, by rfl⟩) (B 22169 (by norm_num) ⟨11084, by rfl⟩ (by norm_num))
theorem R59141 : Reach 59141 := rs (se 4 (by rfl) ⟨5544, by rfl⟩) (B 11089 (by norm_num) ⟨5544, by rfl⟩ (by norm_num))
theorem R91925 : Reach 91925 := rs (se 6 (by rfl) ⟨2154, by rfl⟩) (B 4309 (by norm_num) ⟨2154, by rfl⟩ (by norm_num))
theorem R59165 : Reach 59165 := rs (se 3 (by rfl) ⟨11093, by rfl⟩) (B 22187 (by norm_num) ⟨11093, by rfl⟩ (by norm_num))
theorem R59189 : Reach 59189 := rs (se 5 (by rfl) ⟨2774, by rfl⟩) (B 5549 (by norm_num) ⟨2774, by rfl⟩ (by norm_num))
theorem R91957 : Reach 91957 := rs (se 5 (by rfl) ⟨4310, by rfl⟩) (B 8621 (by norm_num) ⟨4310, by rfl⟩ (by norm_num))
theorem R59213 : Reach 59213 := rs (se 3 (by rfl) ⟨11102, by rfl⟩) (B 22205 (by norm_num) ⟨11102, by rfl⟩ (by norm_num))
theorem R91997 : Reach 91997 := rs (se 3 (by rfl) ⟨17249, by rfl⟩) (B 34499 (by norm_num) ⟨17249, by rfl⟩ (by norm_num))
theorem R59237 : Reach 59237 := rs (se 4 (by rfl) ⟨5553, by rfl⟩) (B 11107 (by norm_num) ⟨5553, by rfl⟩ (by norm_num))
theorem R59261 : Reach 59261 := rs (se 3 (by rfl) ⟨11111, by rfl⟩) (B 22223 (by norm_num) ⟨11111, by rfl⟩ (by norm_num))
theorem R59285 : Reach 59285 := rs (se 6 (by rfl) ⟨1389, by rfl⟩) (B 2779 (by norm_num) ⟨1389, by rfl⟩ (by norm_num))
theorem R92069 : Reach 92069 := rs (se 4 (by rfl) ⟨8631, by rfl⟩) (B 17263 (by norm_num) ⟨8631, by rfl⟩ (by norm_num))
theorem R59309 : Reach 59309 := rs (se 3 (by rfl) ⟨11120, by rfl⟩) (B 22241 (by norm_num) ⟨11120, by rfl⟩ (by norm_num))
theorem R59333 : Reach 59333 := rs (se 4 (by rfl) ⟨5562, by rfl⟩) (B 11125 (by norm_num) ⟨5562, by rfl⟩ (by norm_num))
theorem R59357 : Reach 59357 := rs (se 3 (by rfl) ⟨11129, by rfl⟩) (B 22259 (by norm_num) ⟨11129, by rfl⟩ (by norm_num))
theorem R92141 : Reach 92141 := rs (se 3 (by rfl) ⟨17276, by rfl⟩) (B 34553 (by norm_num) ⟨17276, by rfl⟩ (by norm_num))
theorem R59381 : Reach 59381 := rs (se 5 (by rfl) ⟨2783, by rfl⟩) (B 5567 (by norm_num) ⟨2783, by rfl⟩ (by norm_num))
theorem R59405 : Reach 59405 := rs (se 3 (by rfl) ⟨11138, by rfl⟩) (B 22277 (by norm_num) ⟨11138, by rfl⟩ (by norm_num))
theorem R59429 : Reach 59429 := rs (se 4 (by rfl) ⟨5571, by rfl⟩) (B 11143 (by norm_num) ⟨5571, by rfl⟩ (by norm_num))
theorem R92213 : Reach 92213 := rs (se 5 (by rfl) ⟨4322, by rfl⟩) (B 8645 (by norm_num) ⟨4322, by rfl⟩ (by norm_num))
theorem R59453 : Reach 59453 := rs (se 3 (by rfl) ⟨11147, by rfl⟩) (B 22295 (by norm_num) ⟨11147, by rfl⟩ (by norm_num))
theorem R59477 : Reach 59477 := rs (se 8 (by rfl) ⟨348, by rfl⟩) (B 697 (by norm_num) ⟨348, by rfl⟩ (by norm_num))
theorem R256085 : Reach 256085 := rs (se 8 (by rfl) ⟨1500, by rfl⟩) (B 3001 (by norm_num) ⟨1500, by rfl⟩ (by norm_num))
theorem R59501 : Reach 59501 := rs (se 3 (by rfl) ⟨11156, by rfl⟩) (B 22313 (by norm_num) ⟨11156, by rfl⟩ (by norm_num))
theorem R92285 : Reach 92285 := rs (se 3 (by rfl) ⟨17303, by rfl⟩) (B 34607 (by norm_num) ⟨17303, by rfl⟩ (by norm_num))
theorem R59525 : Reach 59525 := rs (se 4 (by rfl) ⟨5580, by rfl⟩) (B 11161 (by norm_num) ⟨5580, by rfl⟩ (by norm_num))
theorem R59549 : Reach 59549 := rs (se 3 (by rfl) ⟨11165, by rfl⟩) (B 22331 (by norm_num) ⟨11165, by rfl⟩ (by norm_num))
theorem R59573 : Reach 59573 := rs (se 5 (by rfl) ⟨2792, by rfl⟩) (B 5585 (by norm_num) ⟨2792, by rfl⟩ (by norm_num))
theorem R92357 : Reach 92357 := rs (se 4 (by rfl) ⟨8658, by rfl⟩) (B 17317 (by norm_num) ⟨8658, by rfl⟩ (by norm_num))
theorem R59597 : Reach 59597 := rs (se 3 (by rfl) ⟨11174, by rfl⟩) (B 22349 (by norm_num) ⟨11174, by rfl⟩ (by norm_num))
theorem R59621 : Reach 59621 := rs (se 4 (by rfl) ⟨5589, by rfl⟩) (B 11179 (by norm_num) ⟨5589, by rfl⟩ (by norm_num))
theorem R59645 : Reach 59645 := rs (se 3 (by rfl) ⟨11183, by rfl⟩) (B 22367 (by norm_num) ⟨11183, by rfl⟩ (by norm_num))
theorem R59653 : Reach 59653 := rs (se 4 (by rfl) ⟨5592, by rfl⟩) (B 11185 (by norm_num) ⟨5592, by rfl⟩ (by norm_num))
theorem R92429 : Reach 92429 := rs (se 3 (by rfl) ⟨17330, by rfl⟩) (B 34661 (by norm_num) ⟨17330, by rfl⟩ (by norm_num))
theorem R59669 : Reach 59669 := rs (se 6 (by rfl) ⟨1398, by rfl⟩) (B 2797 (by norm_num) ⟨1398, by rfl⟩ (by norm_num))
theorem R59693 : Reach 59693 := rs (se 3 (by rfl) ⟨11192, by rfl⟩) (B 22385 (by norm_num) ⟨11192, by rfl⟩ (by norm_num))
theorem R59717 : Reach 59717 := rs (se 4 (by rfl) ⟨5598, by rfl⟩) (B 11197 (by norm_num) ⟨5598, by rfl⟩ (by norm_num))
theorem R92501 : Reach 92501 := rs (se 10 (by rfl) ⟨135, by rfl⟩) (B 271 (by norm_num) ⟨135, by rfl⟩ (by norm_num))
theorem R59741 : Reach 59741 := rs (se 3 (by rfl) ⟨11201, by rfl⟩) (B 22403 (by norm_num) ⟨11201, by rfl⟩ (by norm_num))
theorem R59765 : Reach 59765 := rs (se 5 (by rfl) ⟨2801, by rfl⟩) (B 5603 (by norm_num) ⟨2801, by rfl⟩ (by norm_num))
theorem R59773 : Reach 59773 := rs (se 3 (by rfl) ⟨11207, by rfl⟩) (B 22415 (by norm_num) ⟨11207, by rfl⟩ (by norm_num))
theorem R59789 : Reach 59789 := rs (se 3 (by rfl) ⟨11210, by rfl⟩) (B 22421 (by norm_num) ⟨11210, by rfl⟩ (by norm_num))
theorem R92573 : Reach 92573 := rs (se 3 (by rfl) ⟨17357, by rfl⟩) (B 34715 (by norm_num) ⟨17357, by rfl⟩ (by norm_num))
theorem R59813 : Reach 59813 := rs (se 4 (by rfl) ⟨5607, by rfl⟩) (B 11215 (by norm_num) ⟨5607, by rfl⟩ (by norm_num))
theorem R59837 : Reach 59837 := rs (se 3 (by rfl) ⟨11219, by rfl⟩) (B 22439 (by norm_num) ⟨11219, by rfl⟩ (by norm_num))
theorem R59861 : Reach 59861 := rs (se 7 (by rfl) ⟨701, by rfl⟩) (B 1403 (by norm_num) ⟨701, by rfl⟩ (by norm_num))
theorem R59869 : Reach 59869 := rs (se 3 (by rfl) ⟨11225, by rfl⟩) (B 22451 (by norm_num) ⟨11225, by rfl⟩ (by norm_num))
theorem R92645 : Reach 92645 := rs (se 4 (by rfl) ⟨8685, by rfl⟩) (B 17371 (by norm_num) ⟨8685, by rfl⟩ (by norm_num))
theorem R59885 : Reach 59885 := rs (se 3 (by rfl) ⟨11228, by rfl⟩) (B 22457 (by norm_num) ⟨11228, by rfl⟩ (by norm_num))
theorem R59909 : Reach 59909 := rs (se 4 (by rfl) ⟨5616, by rfl⟩) (B 11233 (by norm_num) ⟨5616, by rfl⟩ (by norm_num))
theorem R59933 : Reach 59933 := rs (se 3 (by rfl) ⟨11237, by rfl⟩) (B 22475 (by norm_num) ⟨11237, by rfl⟩ (by norm_num))
theorem R92717 : Reach 92717 := rs (se 3 (by rfl) ⟨17384, by rfl⟩) (B 34769 (by norm_num) ⟨17384, by rfl⟩ (by norm_num))
theorem R59957 : Reach 59957 := rs (se 5 (by rfl) ⟨2810, by rfl⟩) (B 5621 (by norm_num) ⟨2810, by rfl⟩ (by norm_num))
theorem R59981 : Reach 59981 := rs (se 3 (by rfl) ⟨11246, by rfl⟩) (B 22493 (by norm_num) ⟨11246, by rfl⟩ (by norm_num))
theorem R60005 : Reach 60005 := rs (se 4 (by rfl) ⟨5625, by rfl⟩) (B 11251 (by norm_num) ⟨5625, by rfl⟩ (by norm_num))
theorem R92789 : Reach 92789 := rs (se 5 (by rfl) ⟨4349, by rfl⟩) (B 8699 (by norm_num) ⟨4349, by rfl⟩ (by norm_num))
theorem R60029 : Reach 60029 := rs (se 3 (by rfl) ⟨11255, by rfl⟩) (B 22511 (by norm_num) ⟨11255, by rfl⟩ (by norm_num))
theorem R60053 : Reach 60053 := rs (se 6 (by rfl) ⟨1407, by rfl⟩) (B 2815 (by norm_num) ⟨1407, by rfl⟩ (by norm_num))
theorem R60077 : Reach 60077 := rs (se 3 (by rfl) ⟨11264, by rfl⟩) (B 22529 (by norm_num) ⟨11264, by rfl⟩ (by norm_num))
theorem R92861 : Reach 92861 := rs (se 3 (by rfl) ⟨17411, by rfl⟩) (B 34823 (by norm_num) ⟨17411, by rfl⟩ (by norm_num))
theorem R60101 : Reach 60101 := rs (se 4 (by rfl) ⟨5634, by rfl⟩) (B 11269 (by norm_num) ⟨5634, by rfl⟩ (by norm_num))
theorem R60125 : Reach 60125 := rs (se 3 (by rfl) ⟨11273, by rfl⟩) (B 22547 (by norm_num) ⟨11273, by rfl⟩ (by norm_num))
theorem R60149 : Reach 60149 := rs (se 5 (by rfl) ⟨2819, by rfl⟩) (B 5639 (by norm_num) ⟨2819, by rfl⟩ (by norm_num))
theorem R92933 : Reach 92933 := rs (se 4 (by rfl) ⟨8712, by rfl⟩) (B 17425 (by norm_num) ⟨8712, by rfl⟩ (by norm_num))
theorem R60173 : Reach 60173 := rs (se 3 (by rfl) ⟨11282, by rfl⟩) (B 22565 (by norm_num) ⟨11282, by rfl⟩ (by norm_num))
theorem R60197 : Reach 60197 := rs (se 4 (by rfl) ⟨5643, by rfl⟩) (B 11287 (by norm_num) ⟨5643, by rfl⟩ (by norm_num))
theorem R60221 : Reach 60221 := rs (se 3 (by rfl) ⟨11291, by rfl⟩) (B 22583 (by norm_num) ⟨11291, by rfl⟩ (by norm_num))
theorem R93005 : Reach 93005 := rs (se 3 (by rfl) ⟨17438, by rfl⟩) (B 34877 (by norm_num) ⟨17438, by rfl⟩ (by norm_num))
theorem R60245 : Reach 60245 := rs (se 9 (by rfl) ⟨176, by rfl⟩) (B 353 (by norm_num) ⟨176, by rfl⟩ (by norm_num))
theorem R191333 : Reach 191333 := rs (se 4 (by rfl) ⟨17937, by rfl⟩) (B 35875 (by norm_num) ⟨17937, by rfl⟩ (by norm_num))
theorem R60269 : Reach 60269 := rs (se 3 (by rfl) ⟨11300, by rfl⟩) (B 22601 (by norm_num) ⟨11300, by rfl⟩ (by norm_num))
theorem R125813 : Reach 125813 := rs (se 5 (by rfl) ⟨5897, by rfl⟩) (B 11795 (by norm_num) ⟨5897, by rfl⟩ (by norm_num))
theorem R224117 : Reach 224117 := rs (se 5 (by rfl) ⟨10505, by rfl⟩) (B 21011 (by norm_num) ⟨10505, by rfl⟩ (by norm_num))
theorem R93053 : Reach 93053 := rs (se 3 (by rfl) ⟨17447, by rfl⟩) (B 34895 (by norm_num) ⟨17447, by rfl⟩ (by norm_num))
theorem R60293 : Reach 60293 := rs (se 4 (by rfl) ⟨5652, by rfl⟩) (B 11305 (by norm_num) ⟨5652, by rfl⟩ (by norm_num))
theorem R93077 : Reach 93077 := rs (se 6 (by rfl) ⟨2181, by rfl⟩) (B 4363 (by norm_num) ⟨2181, by rfl⟩ (by norm_num))
theorem R60317 : Reach 60317 := rs (se 3 (by rfl) ⟨11309, by rfl⟩) (B 22619 (by norm_num) ⟨11309, by rfl⟩ (by norm_num))
theorem R60341 : Reach 60341 := rs (se 5 (by rfl) ⟨2828, by rfl⟩) (B 5657 (by norm_num) ⟨2828, by rfl⟩ (by norm_num))
theorem R60365 : Reach 60365 := rs (se 3 (by rfl) ⟨11318, by rfl⟩) (B 22637 (by norm_num) ⟨11318, by rfl⟩ (by norm_num))
theorem R93149 : Reach 93149 := rs (se 3 (by rfl) ⟨17465, by rfl⟩) (B 34931 (by norm_num) ⟨17465, by rfl⟩ (by norm_num))
theorem R60389 : Reach 60389 := rs (se 4 (by rfl) ⟨5661, by rfl⟩) (B 11323 (by norm_num) ⟨5661, by rfl⟩ (by norm_num))
theorem R60413 : Reach 60413 := rs (se 3 (by rfl) ⟨11327, by rfl⟩) (B 22655 (by norm_num) ⟨11327, by rfl⟩ (by norm_num))
theorem R60437 : Reach 60437 := rs (se 6 (by rfl) ⟨1416, by rfl⟩) (B 2833 (by norm_num) ⟨1416, by rfl⟩ (by norm_num))
theorem R93221 : Reach 93221 := rs (se 4 (by rfl) ⟨8739, by rfl⟩) (B 17479 (by norm_num) ⟨8739, by rfl⟩ (by norm_num))
theorem R60461 : Reach 60461 := rs (se 3 (by rfl) ⟨11336, by rfl⟩) (B 22673 (by norm_num) ⟨11336, by rfl⟩ (by norm_num))
theorem R60485 : Reach 60485 := rs (se 4 (by rfl) ⟨5670, by rfl⟩) (B 11341 (by norm_num) ⟨5670, by rfl⟩ (by norm_num))
theorem R60509 : Reach 60509 := rs (se 3 (by rfl) ⟨11345, by rfl⟩) (B 22691 (by norm_num) ⟨11345, by rfl⟩ (by norm_num))
theorem R93293 : Reach 93293 := rs (se 3 (by rfl) ⟨17492, by rfl⟩) (B 34985 (by norm_num) ⟨17492, by rfl⟩ (by norm_num))
theorem R60533 : Reach 60533 := rs (se 5 (by rfl) ⟨2837, by rfl⟩) (B 5675 (by norm_num) ⟨2837, by rfl⟩ (by norm_num))
theorem R60557 : Reach 60557 := rs (se 3 (by rfl) ⟨11354, by rfl⟩) (B 22709 (by norm_num) ⟨11354, by rfl⟩ (by norm_num))
theorem R60581 : Reach 60581 := rs (se 4 (by rfl) ⟨5679, by rfl⟩) (B 11359 (by norm_num) ⟨5679, by rfl⟩ (by norm_num))
theorem R93365 : Reach 93365 := rs (se 5 (by rfl) ⟨4376, by rfl⟩) (B 8753 (by norm_num) ⟨4376, by rfl⟩ (by norm_num))
theorem R60605 : Reach 60605 := rs (se 3 (by rfl) ⟨11363, by rfl⟩) (B 22727 (by norm_num) ⟨11363, by rfl⟩ (by norm_num))
theorem R60629 : Reach 60629 := rs (se 7 (by rfl) ⟨710, by rfl⟩) (B 1421 (by norm_num) ⟨710, by rfl⟩ (by norm_num))
theorem R60653 : Reach 60653 := rs (se 3 (by rfl) ⟨11372, by rfl⟩) (B 22745 (by norm_num) ⟨11372, by rfl⟩ (by norm_num))
theorem R93437 : Reach 93437 := rs (se 3 (by rfl) ⟨17519, by rfl⟩) (B 35039 (by norm_num) ⟨17519, by rfl⟩ (by norm_num))
theorem R60677 : Reach 60677 := rs (se 4 (by rfl) ⟨5688, by rfl⟩) (B 11377 (by norm_num) ⟨5688, by rfl⟩ (by norm_num))
theorem R60701 : Reach 60701 := rs (se 3 (by rfl) ⟨11381, by rfl⟩) (B 22763 (by norm_num) ⟨11381, by rfl⟩ (by norm_num))
theorem R93485 : Reach 93485 := rs (se 3 (by rfl) ⟨17528, by rfl⟩) (B 35057 (by norm_num) ⟨17528, by rfl⟩ (by norm_num))
theorem R60725 : Reach 60725 := rs (se 5 (by rfl) ⟨2846, by rfl⟩) (B 5693 (by norm_num) ⟨2846, by rfl⟩ (by norm_num))
theorem R159029 : Reach 159029 := rs (se 5 (by rfl) ⟨7454, by rfl⟩) (B 14909 (by norm_num) ⟨7454, by rfl⟩ (by norm_num))
theorem R93509 : Reach 93509 := rs (se 4 (by rfl) ⟨8766, by rfl⟩) (B 17533 (by norm_num) ⟨8766, by rfl⟩ (by norm_num))
theorem R60749 : Reach 60749 := rs (se 3 (by rfl) ⟨11390, by rfl⟩) (B 22781 (by norm_num) ⟨11390, by rfl⟩ (by norm_num))
theorem R60773 : Reach 60773 := rs (se 4 (by rfl) ⟨5697, by rfl⟩) (B 11395 (by norm_num) ⟨5697, by rfl⟩ (by norm_num))
theorem R60797 : Reach 60797 := rs (se 3 (by rfl) ⟨11399, by rfl⟩) (B 22799 (by norm_num) ⟨11399, by rfl⟩ (by norm_num))
theorem R93581 : Reach 93581 := rs (se 3 (by rfl) ⟨17546, by rfl⟩) (B 35093 (by norm_num) ⟨17546, by rfl⟩ (by norm_num))
theorem R60821 : Reach 60821 := rs (se 6 (by rfl) ⟨1425, by rfl⟩) (B 2851 (by norm_num) ⟨1425, by rfl⟩ (by norm_num))
theorem R60845 : Reach 60845 := rs (se 3 (by rfl) ⟨11408, by rfl⟩) (B 22817 (by norm_num) ⟨11408, by rfl⟩ (by norm_num))
theorem R224693 : Reach 224693 := rs (se 5 (by rfl) ⟨10532, by rfl⟩) (B 21065 (by norm_num) ⟨10532, by rfl⟩ (by norm_num))
theorem R60869 : Reach 60869 := rs (se 4 (by rfl) ⟨5706, by rfl⟩) (B 11413 (by norm_num) ⟨5706, by rfl⟩ (by norm_num))
theorem R93653 : Reach 93653 := rs (se 7 (by rfl) ⟨1097, by rfl⟩) (B 2195 (by norm_num) ⟨1097, by rfl⟩ (by norm_num))
theorem R60893 : Reach 60893 := rs (se 3 (by rfl) ⟨11417, by rfl⟩) (B 22835 (by norm_num) ⟨11417, by rfl⟩ (by norm_num))
theorem R60917 : Reach 60917 := rs (se 5 (by rfl) ⟨2855, by rfl⟩) (B 5711 (by norm_num) ⟨2855, by rfl⟩ (by norm_num))
theorem R60941 : Reach 60941 := rs (se 3 (by rfl) ⟨11426, by rfl⟩) (B 22853 (by norm_num) ⟨11426, by rfl⟩ (by norm_num))
theorem R93725 : Reach 93725 := rs (se 3 (by rfl) ⟨17573, by rfl⟩) (B 35147 (by norm_num) ⟨17573, by rfl⟩ (by norm_num))
theorem R60965 : Reach 60965 := rs (se 4 (by rfl) ⟨5715, by rfl⟩) (B 11431 (by norm_num) ⟨5715, by rfl⟩ (by norm_num))
theorem R60989 : Reach 60989 := rs (se 3 (by rfl) ⟨11435, by rfl⟩) (B 22871 (by norm_num) ⟨11435, by rfl⟩ (by norm_num))
theorem R61013 : Reach 61013 := rs (se 8 (by rfl) ⟨357, by rfl⟩) (B 715 (by norm_num) ⟨357, by rfl⟩ (by norm_num))
theorem R159317 : Reach 159317 := rs (se 8 (by rfl) ⟨933, by rfl⟩) (B 1867 (by norm_num) ⟨933, by rfl⟩ (by norm_num))
theorem R93797 : Reach 93797 := rs (se 4 (by rfl) ⟨8793, by rfl⟩) (B 17587 (by norm_num) ⟨8793, by rfl⟩ (by norm_num))
theorem R61037 : Reach 61037 := rs (se 3 (by rfl) ⟨11444, by rfl⟩) (B 22889 (by norm_num) ⟨11444, by rfl⟩ (by norm_num))
theorem R323189 : Reach 323189 := rs (se 5 (by rfl) ⟨15149, by rfl⟩) (B 30299 (by norm_num) ⟨15149, by rfl⟩ (by norm_num))
theorem R61061 : Reach 61061 := rs (se 4 (by rfl) ⟨5724, by rfl⟩) (B 11449 (by norm_num) ⟨5724, by rfl⟩ (by norm_num))
theorem R61085 : Reach 61085 := rs (se 3 (by rfl) ⟨11453, by rfl⟩) (B 22907 (by norm_num) ⟨11453, by rfl⟩ (by norm_num))
theorem R93869 : Reach 93869 := rs (se 3 (by rfl) ⟨17600, by rfl⟩) (B 35201 (by norm_num) ⟨17600, by rfl⟩ (by norm_num))
theorem R61109 : Reach 61109 := rs (se 5 (by rfl) ⟨2864, by rfl⟩) (B 5729 (by norm_num) ⟨2864, by rfl⟩ (by norm_num))
theorem R61133 : Reach 61133 := rs (se 3 (by rfl) ⟨11462, by rfl⟩) (B 22925 (by norm_num) ⟨11462, by rfl⟩ (by norm_num))
theorem R61157 : Reach 61157 := rs (se 4 (by rfl) ⟨5733, by rfl⟩) (B 11467 (by norm_num) ⟨5733, by rfl⟩ (by norm_num))
theorem R93941 : Reach 93941 := rs (se 5 (by rfl) ⟨4403, by rfl⟩) (B 8807 (by norm_num) ⟨4403, by rfl⟩ (by norm_num))
theorem R61181 : Reach 61181 := rs (se 3 (by rfl) ⟨11471, by rfl⟩) (B 22943 (by norm_num) ⟨11471, by rfl⟩ (by norm_num))
theorem R61205 : Reach 61205 := rs (se 6 (by rfl) ⟨1434, by rfl⟩) (B 2869 (by norm_num) ⟨1434, by rfl⟩ (by norm_num))
theorem R61229 : Reach 61229 := rs (se 3 (by rfl) ⟨11480, by rfl⟩) (B 22961 (by norm_num) ⟨11480, by rfl⟩ (by norm_num))
theorem R94013 : Reach 94013 := rs (se 3 (by rfl) ⟨17627, by rfl⟩) (B 35255 (by norm_num) ⟨17627, by rfl⟩ (by norm_num))
theorem R61253 : Reach 61253 := rs (se 4 (by rfl) ⟨5742, by rfl⟩) (B 11485 (by norm_num) ⟨5742, by rfl⟩ (by norm_num))
theorem R61277 : Reach 61277 := rs (se 3 (by rfl) ⟨11489, by rfl⟩) (B 22979 (by norm_num) ⟨11489, by rfl⟩ (by norm_num))
theorem R126821 : Reach 126821 := rs (se 4 (by rfl) ⟨11889, by rfl⟩) (B 23779 (by norm_num) ⟨11889, by rfl⟩ (by norm_num))
theorem R61301 : Reach 61301 := rs (se 5 (by rfl) ⟨2873, by rfl⟩) (B 5747 (by norm_num) ⟨2873, by rfl⟩ (by norm_num))
theorem R94085 : Reach 94085 := rs (se 4 (by rfl) ⟨8820, by rfl⟩) (B 17641 (by norm_num) ⟨8820, by rfl⟩ (by norm_num))
theorem R61325 : Reach 61325 := rs (se 3 (by rfl) ⟨11498, by rfl⟩) (B 22997 (by norm_num) ⟨11498, by rfl⟩ (by norm_num))
theorem R61349 : Reach 61349 := rs (se 4 (by rfl) ⟨5751, by rfl⟩) (B 11503 (by norm_num) ⟨5751, by rfl⟩ (by norm_num))
theorem R61373 : Reach 61373 := rs (se 3 (by rfl) ⟨11507, by rfl⟩) (B 23015 (by norm_num) ⟨11507, by rfl⟩ (by norm_num))
theorem R94157 : Reach 94157 := rs (se 3 (by rfl) ⟨17654, by rfl⟩) (B 35309 (by norm_num) ⟨17654, by rfl⟩ (by norm_num))
theorem R61397 : Reach 61397 := rs (se 7 (by rfl) ⟨719, by rfl⟩) (B 1439 (by norm_num) ⟨719, by rfl⟩ (by norm_num))
theorem R61421 : Reach 61421 := rs (se 3 (by rfl) ⟨11516, by rfl⟩) (B 23033 (by norm_num) ⟨11516, by rfl⟩ (by norm_num))
theorem R61445 : Reach 61445 := rs (se 4 (by rfl) ⟨5760, by rfl⟩) (B 11521 (by norm_num) ⟨5760, by rfl⟩ (by norm_num))
theorem R94229 : Reach 94229 := rs (se 6 (by rfl) ⟨2208, by rfl⟩) (B 4417 (by norm_num) ⟨2208, by rfl⟩ (by norm_num))
theorem R61469 : Reach 61469 := rs (se 3 (by rfl) ⟨11525, by rfl⟩) (B 23051 (by norm_num) ⟨11525, by rfl⟩ (by norm_num))
theorem R61493 : Reach 61493 := rs (se 5 (by rfl) ⟨2882, by rfl⟩) (B 5765 (by norm_num) ⟨2882, by rfl⟩ (by norm_num))
theorem R61517 : Reach 61517 := rs (se 3 (by rfl) ⟨11534, by rfl⟩) (B 23069 (by norm_num) ⟨11534, by rfl⟩ (by norm_num))
theorem R94301 : Reach 94301 := rs (se 3 (by rfl) ⟨17681, by rfl⟩) (B 35363 (by norm_num) ⟨17681, by rfl⟩ (by norm_num))
theorem R61541 : Reach 61541 := rs (se 4 (by rfl) ⟨5769, by rfl⟩) (B 11539 (by norm_num) ⟨5769, by rfl⟩ (by norm_num))
theorem R61565 : Reach 61565 := rs (se 3 (by rfl) ⟨11543, by rfl⟩) (B 23087 (by norm_num) ⟨11543, by rfl⟩ (by norm_num))
theorem R127109 : Reach 127109 := rs (se 4 (by rfl) ⟨11916, by rfl⟩) (B 23833 (by norm_num) ⟨11916, by rfl⟩ (by norm_num))
theorem R61589 : Reach 61589 := rs (se 6 (by rfl) ⟨1443, by rfl⟩) (B 2887 (by norm_num) ⟨1443, by rfl⟩ (by norm_num))
theorem R94373 : Reach 94373 := rs (se 4 (by rfl) ⟨8847, by rfl⟩) (B 17695 (by norm_num) ⟨8847, by rfl⟩ (by norm_num))
theorem R61613 : Reach 61613 := rs (se 3 (by rfl) ⟨11552, by rfl⟩) (B 23105 (by norm_num) ⟨11552, by rfl⟩ (by norm_num))
theorem R61637 : Reach 61637 := rs (se 4 (by rfl) ⟨5778, by rfl⟩) (B 11557 (by norm_num) ⟨5778, by rfl⟩ (by norm_num))
theorem R192725 : Reach 192725 := rs (se 7 (by rfl) ⟨2258, by rfl⟩) (B 4517 (by norm_num) ⟨2258, by rfl⟩ (by norm_num))
theorem R61661 : Reach 61661 := rs (se 3 (by rfl) ⟨11561, by rfl⟩) (B 23123 (by norm_num) ⟨11561, by rfl⟩ (by norm_num))
theorem R94445 : Reach 94445 := rs (se 3 (by rfl) ⟨17708, by rfl⟩) (B 35417 (by norm_num) ⟨17708, by rfl⟩ (by norm_num))
theorem R61685 : Reach 61685 := rs (se 5 (by rfl) ⟨2891, by rfl⟩) (B 5783 (by norm_num) ⟨2891, by rfl⟩ (by norm_num))
theorem R61709 : Reach 61709 := rs (se 3 (by rfl) ⟨11570, by rfl⟩) (B 23141 (by norm_num) ⟨11570, by rfl⟩ (by norm_num))
theorem R61733 : Reach 61733 := rs (se 4 (by rfl) ⟨5787, by rfl⟩) (B 11575 (by norm_num) ⟨5787, by rfl⟩ (by norm_num))
theorem R94517 : Reach 94517 := rs (se 5 (by rfl) ⟨4430, by rfl⟩) (B 8861 (by norm_num) ⟨4430, by rfl⟩ (by norm_num))
theorem R61757 : Reach 61757 := rs (se 3 (by rfl) ⟨11579, by rfl⟩) (B 23159 (by norm_num) ⟨11579, by rfl⟩ (by norm_num))
theorem R61781 : Reach 61781 := rs (se 10 (by rfl) ⟨90, by rfl⟩) (B 181 (by norm_num) ⟨90, by rfl⟩ (by norm_num))
theorem R61805 : Reach 61805 := rs (se 3 (by rfl) ⟨11588, by rfl⟩) (B 23177 (by norm_num) ⟨11588, by rfl⟩ (by norm_num))
theorem R94589 : Reach 94589 := rs (se 3 (by rfl) ⟨17735, by rfl⟩) (B 35471 (by norm_num) ⟨17735, by rfl⟩ (by norm_num))
theorem R61829 : Reach 61829 := rs (se 4 (by rfl) ⟨5796, by rfl⟩) (B 11593 (by norm_num) ⟨5796, by rfl⟩ (by norm_num))
theorem R61853 : Reach 61853 := rs (se 3 (by rfl) ⟨11597, by rfl⟩) (B 23195 (by norm_num) ⟨11597, by rfl⟩ (by norm_num))
theorem R61877 : Reach 61877 := rs (se 5 (by rfl) ⟨2900, by rfl⟩) (B 5801 (by norm_num) ⟨2900, by rfl⟩ (by norm_num))
theorem R94661 : Reach 94661 := rs (se 4 (by rfl) ⟨8874, by rfl⟩) (B 17749 (by norm_num) ⟨8874, by rfl⟩ (by norm_num))
theorem R61901 : Reach 61901 := rs (se 3 (by rfl) ⟨11606, by rfl⟩) (B 23213 (by norm_num) ⟨11606, by rfl⟩ (by norm_num))
theorem R61925 : Reach 61925 := rs (se 4 (by rfl) ⟨5805, by rfl⟩) (B 11611 (by norm_num) ⟨5805, by rfl⟩ (by norm_num))
theorem R61949 : Reach 61949 := rs (se 3 (by rfl) ⟨11615, by rfl⟩) (B 23231 (by norm_num) ⟨11615, by rfl⟩ (by norm_num))
theorem R94733 : Reach 94733 := rs (se 3 (by rfl) ⟨17762, by rfl⟩) (B 35525 (by norm_num) ⟨17762, by rfl⟩ (by norm_num))
theorem R61973 : Reach 61973 := rs (se 6 (by rfl) ⟨1452, by rfl⟩) (B 2905 (by norm_num) ⟨1452, by rfl⟩ (by norm_num))
theorem R61997 : Reach 61997 := rs (se 3 (by rfl) ⟨11624, by rfl⟩) (B 23249 (by norm_num) ⟨11624, by rfl⟩ (by norm_num))
theorem R62021 : Reach 62021 := rs (se 4 (by rfl) ⟨5814, by rfl⟩) (B 11629 (by norm_num) ⟨5814, by rfl⟩ (by norm_num))
theorem R94805 : Reach 94805 := rs (se 8 (by rfl) ⟨555, by rfl⟩) (B 1111 (by norm_num) ⟨555, by rfl⟩ (by norm_num))
theorem R62045 : Reach 62045 := rs (se 3 (by rfl) ⟨11633, by rfl⟩) (B 23267 (by norm_num) ⟨11633, by rfl⟩ (by norm_num))
theorem R62069 : Reach 62069 := rs (se 5 (by rfl) ⟨2909, by rfl⟩) (B 5819 (by norm_num) ⟨2909, by rfl⟩ (by norm_num))
theorem R62093 : Reach 62093 := rs (se 3 (by rfl) ⟨11642, by rfl⟩) (B 23285 (by norm_num) ⟨11642, by rfl⟩ (by norm_num))
theorem R94877 : Reach 94877 := rs (se 3 (by rfl) ⟨17789, by rfl⟩) (B 35579 (by norm_num) ⟨17789, by rfl⟩ (by norm_num))
theorem R62117 : Reach 62117 := rs (se 4 (by rfl) ⟨5823, by rfl⟩) (B 11647 (by norm_num) ⟨5823, by rfl⟩ (by norm_num))
theorem R62141 : Reach 62141 := rs (se 3 (by rfl) ⟨11651, by rfl⟩) (B 23303 (by norm_num) ⟨11651, by rfl⟩ (by norm_num))
theorem R62165 : Reach 62165 := rs (se 7 (by rfl) ⟨728, by rfl⟩) (B 1457 (by norm_num) ⟨728, by rfl⟩ (by norm_num))
theorem R94949 : Reach 94949 := rs (se 4 (by rfl) ⟨8901, by rfl⟩) (B 17803 (by norm_num) ⟨8901, by rfl⟩ (by norm_num))
theorem R62189 : Reach 62189 := rs (se 3 (by rfl) ⟨11660, by rfl⟩) (B 23321 (by norm_num) ⟨11660, by rfl⟩ (by norm_num))
theorem R160501 : Reach 160501 := rs (se 5 (by rfl) ⟨7523, by rfl⟩) (B 15047 (by norm_num) ⟨7523, by rfl⟩ (by norm_num))
theorem R62213 : Reach 62213 := rs (se 4 (by rfl) ⟨5832, by rfl⟩) (B 11665 (by norm_num) ⟨5832, by rfl⟩ (by norm_num))
theorem R62237 : Reach 62237 := rs (se 3 (by rfl) ⟨11669, by rfl⟩) (B 23339 (by norm_num) ⟨11669, by rfl⟩ (by norm_num))
theorem R95021 : Reach 95021 := rs (se 3 (by rfl) ⟨17816, by rfl⟩) (B 35633 (by norm_num) ⟨17816, by rfl⟩ (by norm_num))
theorem R62261 : Reach 62261 := rs (se 5 (by rfl) ⟨2918, by rfl⟩) (B 5837 (by norm_num) ⟨2918, by rfl⟩ (by norm_num))
theorem R62285 : Reach 62285 := rs (se 3 (by rfl) ⟨11678, by rfl⟩) (B 23357 (by norm_num) ⟨11678, by rfl⟩ (by norm_num))
theorem R62309 : Reach 62309 := rs (se 4 (by rfl) ⟨5841, by rfl⟩) (B 11683 (by norm_num) ⟨5841, by rfl⟩ (by norm_num))
theorem R62317 : Reach 62317 := rs (se 3 (by rfl) ⟨11684, by rfl⟩) (B 23369 (by norm_num) ⟨11684, by rfl⟩ (by norm_num))
theorem R95093 : Reach 95093 := rs (se 5 (by rfl) ⟨4457, by rfl⟩) (B 8915 (by norm_num) ⟨4457, by rfl⟩ (by norm_num))
theorem R62333 : Reach 62333 := rs (se 3 (by rfl) ⟨11687, by rfl⟩) (B 23375 (by norm_num) ⟨11687, by rfl⟩ (by norm_num))
theorem R62357 : Reach 62357 := rs (se 6 (by rfl) ⟨1461, by rfl⟩) (B 2923 (by norm_num) ⟨1461, by rfl⟩ (by norm_num))
theorem R62381 : Reach 62381 := rs (se 3 (by rfl) ⟨11696, by rfl⟩) (B 23393 (by norm_num) ⟨11696, by rfl⟩ (by norm_num))
theorem R95165 : Reach 95165 := rs (se 3 (by rfl) ⟨17843, by rfl⟩) (B 35687 (by norm_num) ⟨17843, by rfl⟩ (by norm_num))
theorem R62405 : Reach 62405 := rs (se 4 (by rfl) ⟨5850, by rfl⟩) (B 11701 (by norm_num) ⟨5850, by rfl⟩ (by norm_num))
theorem R62429 : Reach 62429 := rs (se 3 (by rfl) ⟨11705, by rfl⟩) (B 23411 (by norm_num) ⟨11705, by rfl⟩ (by norm_num))
theorem R62453 : Reach 62453 := rs (se 5 (by rfl) ⟨2927, by rfl⟩) (B 5855 (by norm_num) ⟨2927, by rfl⟩ (by norm_num))
theorem R95237 : Reach 95237 := rs (se 4 (by rfl) ⟨8928, by rfl⟩) (B 17857 (by norm_num) ⟨8928, by rfl⟩ (by norm_num))
theorem R62477 : Reach 62477 := rs (se 3 (by rfl) ⟨11714, by rfl⟩) (B 23429 (by norm_num) ⟨11714, by rfl⟩ (by norm_num))
theorem R62501 : Reach 62501 := rs (se 4 (by rfl) ⟨5859, by rfl⟩) (B 11719 (by norm_num) ⟨5859, by rfl⟩ (by norm_num))
theorem R160805 : Reach 160805 := rs (se 4 (by rfl) ⟨15075, by rfl⟩) (B 30151 (by norm_num) ⟨15075, by rfl⟩ (by norm_num))
theorem R62525 : Reach 62525 := rs (se 3 (by rfl) ⟨11723, by rfl⟩) (B 23447 (by norm_num) ⟨11723, by rfl⟩ (by norm_num))
theorem R95309 : Reach 95309 := rs (se 3 (by rfl) ⟨17870, by rfl⟩) (B 35741 (by norm_num) ⟨17870, by rfl⟩ (by norm_num))
theorem R62549 : Reach 62549 := rs (se 8 (by rfl) ⟨366, by rfl⟩) (B 733 (by norm_num) ⟨366, by rfl⟩ (by norm_num))
theorem R62573 : Reach 62573 := rs (se 3 (by rfl) ⟨11732, by rfl⟩) (B 23465 (by norm_num) ⟨11732, by rfl⟩ (by norm_num))
theorem R62597 : Reach 62597 := rs (se 4 (by rfl) ⟨5868, by rfl⟩) (B 11737 (by norm_num) ⟨5868, by rfl⟩ (by norm_num))
theorem R95381 : Reach 95381 := rs (se 6 (by rfl) ⟨2235, by rfl⟩) (B 4471 (by norm_num) ⟨2235, by rfl⟩ (by norm_num))
theorem R62621 : Reach 62621 := rs (se 3 (by rfl) ⟨11741, by rfl⟩) (B 23483 (by norm_num) ⟨11741, by rfl⟩ (by norm_num))
theorem R62645 : Reach 62645 := rs (se 5 (by rfl) ⟨2936, by rfl⟩) (B 5873 (by norm_num) ⟨2936, by rfl⟩ (by norm_num))
theorem R62669 : Reach 62669 := rs (se 3 (by rfl) ⟨11750, by rfl⟩) (B 23501 (by norm_num) ⟨11750, by rfl⟩ (by norm_num))
theorem R95453 : Reach 95453 := rs (se 3 (by rfl) ⟨17897, by rfl⟩) (B 35795 (by norm_num) ⟨17897, by rfl⟩ (by norm_num))
theorem R62693 : Reach 62693 := rs (se 4 (by rfl) ⟨5877, by rfl⟩) (B 11755 (by norm_num) ⟨5877, by rfl⟩ (by norm_num))
theorem R62717 : Reach 62717 := rs (se 3 (by rfl) ⟨11759, by rfl⟩) (B 23519 (by norm_num) ⟨11759, by rfl⟩ (by norm_num))
theorem R62741 : Reach 62741 := rs (se 6 (by rfl) ⟨1470, by rfl⟩) (B 2941 (by norm_num) ⟨1470, by rfl⟩ (by norm_num))
theorem R95525 : Reach 95525 := rs (se 4 (by rfl) ⟨8955, by rfl⟩) (B 17911 (by norm_num) ⟨8955, by rfl⟩ (by norm_num))
theorem R62765 : Reach 62765 := rs (se 3 (by rfl) ⟨11768, by rfl⟩) (B 23537 (by norm_num) ⟨11768, by rfl⟩ (by norm_num))
theorem R62789 : Reach 62789 := rs (se 4 (by rfl) ⟨5886, by rfl⟩) (B 11773 (by norm_num) ⟨5886, by rfl⟩ (by norm_num))
theorem R62813 : Reach 62813 := rs (se 3 (by rfl) ⟨11777, by rfl⟩) (B 23555 (by norm_num) ⟨11777, by rfl⟩ (by norm_num))
theorem R95597 : Reach 95597 := rs (se 3 (by rfl) ⟨17924, by rfl⟩) (B 35849 (by norm_num) ⟨17924, by rfl⟩ (by norm_num))
theorem R193909 : Reach 193909 := rs (se 5 (by rfl) ⟨9089, by rfl⟩) (B 18179 (by norm_num) ⟨9089, by rfl⟩ (by norm_num))
theorem R62837 : Reach 62837 := rs (se 5 (by rfl) ⟨2945, by rfl⟩) (B 5891 (by norm_num) ⟨2945, by rfl⟩ (by norm_num))
theorem R62861 : Reach 62861 := rs (se 3 (by rfl) ⟨11786, by rfl⟩) (B 23573 (by norm_num) ⟨11786, by rfl⟩ (by norm_num))
theorem R62885 : Reach 62885 := rs (se 4 (by rfl) ⟨5895, by rfl⟩) (B 11791 (by norm_num) ⟨5895, by rfl⟩ (by norm_num))
theorem R95669 : Reach 95669 := rs (se 5 (by rfl) ⟨4484, by rfl⟩) (B 8969 (by norm_num) ⟨4484, by rfl⟩ (by norm_num))
theorem R62909 : Reach 62909 := rs (se 3 (by rfl) ⟨11795, by rfl⟩) (B 23591 (by norm_num) ⟨11795, by rfl⟩ (by norm_num))
theorem R62933 : Reach 62933 := rs (se 7 (by rfl) ⟨737, by rfl⟩) (B 1475 (by norm_num) ⟨737, by rfl⟩ (by norm_num))
theorem R62957 : Reach 62957 := rs (se 3 (by rfl) ⟨11804, by rfl⟩) (B 23609 (by norm_num) ⟨11804, by rfl⟩ (by norm_num))
theorem R95741 : Reach 95741 := rs (se 3 (by rfl) ⟨17951, by rfl⟩) (B 35903 (by norm_num) ⟨17951, by rfl⟩ (by norm_num))
theorem R62981 : Reach 62981 := rs (se 4 (by rfl) ⟨5904, by rfl⟩) (B 11809 (by norm_num) ⟨5904, by rfl⟩ (by norm_num))
theorem R63005 : Reach 63005 := rs (se 3 (by rfl) ⟨11813, by rfl⟩) (B 23627 (by norm_num) ⟨11813, by rfl⟩ (by norm_num))
theorem R63029 : Reach 63029 := rs (se 5 (by rfl) ⟨2954, by rfl⟩) (B 5909 (by norm_num) ⟨2954, by rfl⟩ (by norm_num))
theorem R95813 : Reach 95813 := rs (se 4 (by rfl) ⟨8982, by rfl⟩) (B 17965 (by norm_num) ⟨8982, by rfl⟩ (by norm_num))
theorem R63053 : Reach 63053 := rs (se 3 (by rfl) ⟨11822, by rfl⟩) (B 23645 (by norm_num) ⟨11822, by rfl⟩ (by norm_num))
theorem R226901 : Reach 226901 := rs (se 8 (by rfl) ⟨1329, by rfl⟩) (B 2659 (by norm_num) ⟨1329, by rfl⟩ (by norm_num))
theorem R63077 : Reach 63077 := rs (se 4 (by rfl) ⟨5913, by rfl⟩) (B 11827 (by norm_num) ⟨5913, by rfl⟩ (by norm_num))
theorem R63101 : Reach 63101 := rs (se 3 (by rfl) ⟨11831, by rfl⟩) (B 23663 (by norm_num) ⟨11831, by rfl⟩ (by norm_num))
theorem R95885 : Reach 95885 := rs (se 3 (by rfl) ⟨17978, by rfl⟩) (B 35957 (by norm_num) ⟨17978, by rfl⟩ (by norm_num))
theorem R63125 : Reach 63125 := rs (se 6 (by rfl) ⟨1479, by rfl⟩) (B 2959 (by norm_num) ⟨1479, by rfl⟩ (by norm_num))
theorem R95917 : Reach 95917 := rs (se 3 (by rfl) ⟨17984, by rfl⟩) (B 35969 (by norm_num) ⟨17984, by rfl⟩ (by norm_num))
theorem R63149 : Reach 63149 := rs (se 3 (by rfl) ⟨11840, by rfl⟩) (B 23681 (by norm_num) ⟨11840, by rfl⟩ (by norm_num))
theorem R95941 : Reach 95941 := rs (se 4 (by rfl) ⟨8994, by rfl⟩) (B 17989 (by norm_num) ⟨8994, by rfl⟩ (by norm_num))
theorem R63173 : Reach 63173 := rs (se 4 (by rfl) ⟨5922, by rfl⟩) (B 11845 (by norm_num) ⟨5922, by rfl⟩ (by norm_num))
theorem R95957 : Reach 95957 := rs (se 7 (by rfl) ⟨1124, by rfl⟩) (B 2249 (by norm_num) ⟨1124, by rfl⟩ (by norm_num))
theorem R63197 : Reach 63197 := rs (se 3 (by rfl) ⟨11849, by rfl⟩) (B 23699 (by norm_num) ⟨11849, by rfl⟩ (by norm_num))
theorem R63221 : Reach 63221 := rs (se 5 (by rfl) ⟨2963, by rfl⟩) (B 5927 (by norm_num) ⟨2963, by rfl⟩ (by norm_num))
theorem R63245 : Reach 63245 := rs (se 3 (by rfl) ⟨11858, by rfl⟩) (B 23717 (by norm_num) ⟨11858, by rfl⟩ (by norm_num))
theorem R96029 : Reach 96029 := rs (se 3 (by rfl) ⟨18005, by rfl⟩) (B 36011 (by norm_num) ⟨18005, by rfl⟩ (by norm_num))
theorem R63269 : Reach 63269 := rs (se 4 (by rfl) ⟨5931, by rfl⟩) (B 11863 (by norm_num) ⟨5931, by rfl⟩ (by norm_num))
theorem R63293 : Reach 63293 := rs (se 3 (by rfl) ⟨11867, by rfl⟩) (B 23735 (by norm_num) ⟨11867, by rfl⟩ (by norm_num))
theorem R63317 : Reach 63317 := rs (se 9 (by rfl) ⟨185, by rfl⟩) (B 371 (by norm_num) ⟨185, by rfl⟩ (by norm_num))
theorem R96101 : Reach 96101 := rs (se 4 (by rfl) ⟨9009, by rfl⟩) (B 18019 (by norm_num) ⟨9009, by rfl⟩ (by norm_num))
theorem R63341 : Reach 63341 := rs (se 3 (by rfl) ⟨11876, by rfl⟩) (B 23753 (by norm_num) ⟨11876, by rfl⟩ (by norm_num))
theorem R63349 : Reach 63349 := rs (se 5 (by rfl) ⟨2969, by rfl⟩) (B 5939 (by norm_num) ⟨2969, by rfl⟩ (by norm_num))
theorem R63365 : Reach 63365 := rs (se 4 (by rfl) ⟨5940, by rfl⟩) (B 11881 (by norm_num) ⟨5940, by rfl⟩ (by norm_num))
theorem R63389 : Reach 63389 := rs (se 3 (by rfl) ⟨11885, by rfl⟩) (B 23771 (by norm_num) ⟨11885, by rfl⟩ (by norm_num))
theorem R96173 : Reach 96173 := rs (se 3 (by rfl) ⟨18032, by rfl⟩) (B 36065 (by norm_num) ⟨18032, by rfl⟩ (by norm_num))
theorem R63413 : Reach 63413 := rs (se 5 (by rfl) ⟨2972, by rfl⟩) (B 5945 (by norm_num) ⟨2972, by rfl⟩ (by norm_num))
theorem R128965 : Reach 128965 := rs (se 4 (by rfl) ⟨12090, by rfl⟩) (B 24181 (by norm_num) ⟨12090, by rfl⟩ (by norm_num))
theorem R63437 : Reach 63437 := rs (se 3 (by rfl) ⟨11894, by rfl⟩) (B 23789 (by norm_num) ⟨11894, by rfl⟩ (by norm_num))
theorem R63461 : Reach 63461 := rs (se 4 (by rfl) ⟨5949, by rfl⟩) (B 11899 (by norm_num) ⟨5949, by rfl⟩ (by norm_num))
theorem R96245 : Reach 96245 := rs (se 5 (by rfl) ⟨4511, by rfl⟩) (B 9023 (by norm_num) ⟨4511, by rfl⟩ (by norm_num))
theorem R63485 : Reach 63485 := rs (se 3 (by rfl) ⟨11903, by rfl⟩) (B 23807 (by norm_num) ⟨11903, by rfl⟩ (by norm_num))
theorem R161797 : Reach 161797 := rs (se 4 (by rfl) ⟨15168, by rfl⟩) (B 30337 (by norm_num) ⟨15168, by rfl⟩ (by norm_num))
theorem R63509 : Reach 63509 := rs (se 6 (by rfl) ⟨1488, by rfl⟩) (B 2977 (by norm_num) ⟨1488, by rfl⟩ (by norm_num))
theorem R391189 : Reach 391189 := rs (se 6 (by rfl) ⟨9168, by rfl⟩) (B 18337 (by norm_num) ⟨9168, by rfl⟩ (by norm_num))
theorem R63533 : Reach 63533 := rs (se 3 (by rfl) ⟨11912, by rfl⟩) (B 23825 (by norm_num) ⟨11912, by rfl⟩ (by norm_num))
theorem R96317 : Reach 96317 := rs (se 3 (by rfl) ⟨18059, by rfl⟩) (B 36119 (by norm_num) ⟨18059, by rfl⟩ (by norm_num))
theorem R63557 : Reach 63557 := rs (se 4 (by rfl) ⟨5958, by rfl⟩) (B 11917 (by norm_num) ⟨5958, by rfl⟩ (by norm_num))
theorem R63581 : Reach 63581 := rs (se 3 (by rfl) ⟨11921, by rfl⟩) (B 23843 (by norm_num) ⟨11921, by rfl⟩ (by norm_num))
theorem R63605 : Reach 63605 := rs (se 5 (by rfl) ⟨2981, by rfl⟩) (B 5963 (by norm_num) ⟨2981, by rfl⟩ (by norm_num))
theorem R96389 : Reach 96389 := rs (se 4 (by rfl) ⟨9036, by rfl⟩) (B 18073 (by norm_num) ⟨9036, by rfl⟩ (by norm_num))
theorem R63629 : Reach 63629 := rs (se 3 (by rfl) ⟨11930, by rfl⟩) (B 23861 (by norm_num) ⟨11930, by rfl⟩ (by norm_num))
theorem R63653 : Reach 63653 := rs (se 4 (by rfl) ⟨5967, by rfl⟩) (B 11935 (by norm_num) ⟨5967, by rfl⟩ (by norm_num))
theorem R63677 : Reach 63677 := rs (se 3 (by rfl) ⟨11939, by rfl⟩) (B 23879 (by norm_num) ⟨11939, by rfl⟩ (by norm_num))
theorem R96461 : Reach 96461 := rs (se 3 (by rfl) ⟨18086, by rfl⟩) (B 36173 (by norm_num) ⟨18086, by rfl⟩ (by norm_num))
theorem R63701 : Reach 63701 := rs (se 7 (by rfl) ⟨746, by rfl⟩) (B 1493 (by norm_num) ⟨746, by rfl⟩ (by norm_num))
theorem R63725 : Reach 63725 := rs (se 3 (by rfl) ⟨11948, by rfl⟩) (B 23897 (by norm_num) ⟨11948, by rfl⟩ (by norm_num))
theorem R63749 : Reach 63749 := rs (se 4 (by rfl) ⟨5976, by rfl⟩) (B 11953 (by norm_num) ⟨5976, by rfl⟩ (by norm_num))
theorem R96533 : Reach 96533 := rs (se 6 (by rfl) ⟨2262, by rfl⟩) (B 4525 (by norm_num) ⟨2262, by rfl⟩ (by norm_num))
theorem R63773 : Reach 63773 := rs (se 3 (by rfl) ⟨11957, by rfl⟩) (B 23915 (by norm_num) ⟨11957, by rfl⟩ (by norm_num))
theorem R63797 : Reach 63797 := rs (se 5 (by rfl) ⟨2990, by rfl⟩) (B 5981 (by norm_num) ⟨2990, by rfl⟩ (by norm_num))
theorem R63821 : Reach 63821 := rs (se 3 (by rfl) ⟨11966, by rfl⟩) (B 23933 (by norm_num) ⟨11966, by rfl⟩ (by norm_num))
theorem R96605 : Reach 96605 := rs (se 3 (by rfl) ⟨18113, by rfl⟩) (B 36227 (by norm_num) ⟨18113, by rfl⟩ (by norm_num))
theorem R63845 : Reach 63845 := rs (se 4 (by rfl) ⟨5985, by rfl⟩) (B 11971 (by norm_num) ⟨5985, by rfl⟩ (by norm_num))
theorem R63869 : Reach 63869 := rs (se 3 (by rfl) ⟨11975, by rfl⟩) (B 23951 (by norm_num) ⟨11975, by rfl⟩ (by norm_num))
theorem R63893 : Reach 63893 := rs (se 6 (by rfl) ⟨1497, by rfl⟩) (B 2995 (by norm_num) ⟨1497, by rfl⟩ (by norm_num))
theorem R96677 : Reach 96677 := rs (se 4 (by rfl) ⟨9063, by rfl⟩) (B 18127 (by norm_num) ⟨9063, by rfl⟩ (by norm_num))
theorem R63917 : Reach 63917 := rs (se 3 (by rfl) ⟨11984, by rfl⟩) (B 23969 (by norm_num) ⟨11984, by rfl⟩ (by norm_num))
theorem R63941 : Reach 63941 := rs (se 4 (by rfl) ⟨5994, by rfl⟩) (B 11989 (by norm_num) ⟨5994, by rfl⟩ (by norm_num))
theorem R63965 : Reach 63965 := rs (se 3 (by rfl) ⟨11993, by rfl⟩) (B 23987 (by norm_num) ⟨11993, by rfl⟩ (by norm_num))
theorem R96749 : Reach 96749 := rs (se 3 (by rfl) ⟨18140, by rfl⟩) (B 36281 (by norm_num) ⟨18140, by rfl⟩ (by norm_num))
theorem R63989 : Reach 63989 := rs (se 5 (by rfl) ⟨2999, by rfl⟩) (B 5999 (by norm_num) ⟨2999, by rfl⟩ (by norm_num))
theorem R64013 : Reach 64013 := rs (se 3 (by rfl) ⟨12002, by rfl⟩) (B 24005 (by norm_num) ⟨12002, by rfl⟩ (by norm_num))
theorem R64037 : Reach 64037 := rs (se 4 (by rfl) ⟨6003, by rfl⟩) (B 12007 (by norm_num) ⟨6003, by rfl⟩ (by norm_num))
theorem R96821 : Reach 96821 := rs (se 5 (by rfl) ⟨4538, by rfl⟩) (B 9077 (by norm_num) ⟨4538, by rfl⟩ (by norm_num))
theorem R64061 : Reach 64061 := rs (se 3 (by rfl) ⟨12011, by rfl⟩) (B 24023 (by norm_num) ⟨12011, by rfl⟩ (by norm_num))
theorem R64085 : Reach 64085 := rs (se 8 (by rfl) ⟨375, by rfl⟩) (B 751 (by norm_num) ⟨375, by rfl⟩ (by norm_num))
theorem R64109 : Reach 64109 := rs (se 3 (by rfl) ⟨12020, by rfl⟩) (B 24041 (by norm_num) ⟨12020, by rfl⟩ (by norm_num))
theorem R96893 : Reach 96893 := rs (se 3 (by rfl) ⟨18167, by rfl⟩) (B 36335 (by norm_num) ⟨18167, by rfl⟩ (by norm_num))
theorem R64133 : Reach 64133 := rs (se 4 (by rfl) ⟨6012, by rfl⟩) (B 12025 (by norm_num) ⟨6012, by rfl⟩ (by norm_num))
theorem R64157 : Reach 64157 := rs (se 3 (by rfl) ⟨12029, by rfl⟩) (B 24059 (by norm_num) ⟨12029, by rfl⟩ (by norm_num))
theorem R64181 : Reach 64181 := rs (se 5 (by rfl) ⟨3008, by rfl⟩) (B 6017 (by norm_num) ⟨3008, by rfl⟩ (by norm_num))
theorem R96965 : Reach 96965 := rs (se 4 (by rfl) ⟨9090, by rfl⟩) (B 18181 (by norm_num) ⟨9090, by rfl⟩ (by norm_num))
theorem R64205 : Reach 64205 := rs (se 3 (by rfl) ⟨12038, by rfl⟩) (B 24077 (by norm_num) ⟨12038, by rfl⟩ (by norm_num))
theorem R64229 : Reach 64229 := rs (se 4 (by rfl) ⟨6021, by rfl⟩) (B 12043 (by norm_num) ⟨6021, by rfl⟩ (by norm_num))
theorem R64253 : Reach 64253 := rs (se 3 (by rfl) ⟨12047, by rfl⟩) (B 24095 (by norm_num) ⟨12047, by rfl⟩ (by norm_num))
theorem R64277 : Reach 64277 := rs (se 6 (by rfl) ⟨1506, by rfl⟩) (B 3013 (by norm_num) ⟨1506, by rfl⟩ (by norm_num))
theorem R64301 : Reach 64301 := rs (se 3 (by rfl) ⟨12056, by rfl⟩) (B 24113 (by norm_num) ⟨12056, by rfl⟩ (by norm_num))
theorem R64325 : Reach 64325 := rs (se 4 (by rfl) ⟨6030, by rfl⟩) (B 12061 (by norm_num) ⟨6030, by rfl⟩ (by norm_num))
theorem R97109 : Reach 97109 := rs (se 9 (by rfl) ⟨284, by rfl⟩) (B 569 (by norm_num) ⟨284, by rfl⟩ (by norm_num))
theorem R64349 : Reach 64349 := rs (se 3 (by rfl) ⟨12065, by rfl⟩) (B 24131 (by norm_num) ⟨12065, by rfl⟩ (by norm_num))
theorem R64373 : Reach 64373 := rs (se 5 (by rfl) ⟨3017, by rfl⟩) (B 6035 (by norm_num) ⟨3017, by rfl⟩ (by norm_num))
theorem R64397 : Reach 64397 := rs (se 3 (by rfl) ⟨12074, by rfl⟩) (B 24149 (by norm_num) ⟨12074, by rfl⟩ (by norm_num))
theorem R64421 : Reach 64421 := rs (se 4 (by rfl) ⟨6039, by rfl⟩) (B 12079 (by norm_num) ⟨6039, by rfl⟩ (by norm_num))
theorem R64445 : Reach 64445 := rs (se 3 (by rfl) ⟨12083, by rfl⟩) (B 24167 (by norm_num) ⟨12083, by rfl⟩ (by norm_num))
theorem R64469 : Reach 64469 := rs (se 7 (by rfl) ⟨755, by rfl⟩) (B 1511 (by norm_num) ⟨755, by rfl⟩ (by norm_num))
theorem R64493 : Reach 64493 := rs (se 3 (by rfl) ⟨12092, by rfl⟩) (B 24185 (by norm_num) ⟨12092, by rfl⟩ (by norm_num))
theorem R64517 : Reach 64517 := rs (se 4 (by rfl) ⟨6048, by rfl⟩) (B 12097 (by norm_num) ⟨6048, by rfl⟩ (by norm_num))
theorem R97301 : Reach 97301 := rs (se 6 (by rfl) ⟨2280, by rfl⟩) (B 4561 (by norm_num) ⟨2280, by rfl⟩ (by norm_num))
theorem R64541 : Reach 64541 := rs (se 3 (by rfl) ⟨12101, by rfl⟩) (B 24203 (by norm_num) ⟨12101, by rfl⟩ (by norm_num))
theorem R64565 : Reach 64565 := rs (se 5 (by rfl) ⟨3026, by rfl⟩) (B 6053 (by norm_num) ⟨3026, by rfl⟩ (by norm_num))
theorem R64589 : Reach 64589 := rs (se 3 (by rfl) ⟨12110, by rfl⟩) (B 24221 (by norm_num) ⟨12110, by rfl⟩ (by norm_num))
theorem R162917 : Reach 162917 := rs (se 4 (by rfl) ⟨15273, by rfl⟩) (B 30547 (by norm_num) ⟨15273, by rfl⟩ (by norm_num))
theorem R64613 : Reach 64613 := rs (se 4 (by rfl) ⟨6057, by rfl⟩) (B 12115 (by norm_num) ⟨6057, by rfl⟩ (by norm_num))
theorem R64637 : Reach 64637 := rs (se 3 (by rfl) ⟨12119, by rfl⟩) (B 24239 (by norm_num) ⟨12119, by rfl⟩ (by norm_num))
theorem R64661 : Reach 64661 := rs (se 6 (by rfl) ⟨1515, by rfl⟩) (B 3031 (by norm_num) ⟨1515, by rfl⟩ (by norm_num))
theorem R163205 : Reach 163205 := rs (se 4 (by rfl) ⟨15300, by rfl⟩) (B 30601 (by norm_num) ⟨15300, by rfl⟩ (by norm_num))
theorem R64957 : Reach 64957 := rs (se 3 (by rfl) ⟨12179, by rfl⟩) (B 24359 (by norm_num) ⟨12179, by rfl⟩ (by norm_num))
theorem R261589 : Reach 261589 := rs (se 7 (by rfl) ⟨3065, by rfl⟩) (B 6131 (by norm_num) ⟨3065, by rfl⟩ (by norm_num))
theorem R65117 : Reach 65117 := rs (se 3 (by rfl) ⟨12209, by rfl⟩) (B 24419 (by norm_num) ⟨12209, by rfl⟩ (by norm_num))
theorem R491221 : Reach 491221 := rs (se 7 (by rfl) ⟨5756, by rfl⟩) (B 11513 (by norm_num) ⟨5756, by rfl⟩ (by norm_num))
theorem R65261 : Reach 65261 := rs (se 3 (by rfl) ⟨12236, by rfl⟩) (B 24473 (by norm_num) ⟨12236, by rfl⟩ (by norm_num))
theorem R65405 : Reach 65405 := rs (se 3 (by rfl) ⟨12263, by rfl⟩) (B 24527 (by norm_num) ⟨12263, by rfl⟩ (by norm_num))
theorem R262133 : Reach 262133 := rs (se 5 (by rfl) ⟨12287, by rfl⟩) (B 24575 (by norm_num) ⟨12287, by rfl⟩ (by norm_num))
theorem R65585 : Reach 65585 := rs (se 2 (by rfl) ⟨24594, by rfl⟩) R49189
theorem R65713 : Reach 65713 := rs (se 2 (by rfl) ⟨24642, by rfl⟩) R49285
theorem R65777 : Reach 65777 := rs (se 2 (by rfl) ⟨24666, by rfl⟩) R49333
theorem R98723 : Reach 98723 := rs (se 1 (by rfl) ⟨74042, by rfl⟩) R148085
theorem R66035 : Reach 66035 := rs (se 1 (by rfl) ⟨49526, by rfl⟩) R99053
theorem R66163 : Reach 66163 := rs (se 1 (by rfl) ⟨49622, by rfl⟩) R99245
theorem R66305 : Reach 66305 := rs (se 2 (by rfl) ⟨24864, by rfl⟩) R49729
theorem R131939 : Reach 131939 := rs (se 1 (by rfl) ⟨98954, by rfl⟩) R197909
theorem R66433 : Reach 66433 := rs (se 2 (by rfl) ⟨24912, by rfl⟩) R49825
theorem R66467 : Reach 66467 := rs (se 1 (by rfl) ⟨49850, by rfl⟩) R99701
theorem R99281 : Reach 99281 := rs (se 2 (by rfl) ⟨37230, by rfl⟩) R74461
theorem R99299 : Reach 99299 := rs (se 1 (by rfl) ⟨74474, by rfl⟩) R148949
theorem R66595 : Reach 66595 := rs (se 1 (by rfl) ⟨49946, by rfl⟩) R99893
theorem R132131 : Reach 132131 := rs (se 1 (by rfl) ⟨99098, by rfl⟩) R198197
theorem R99377 : Reach 99377 := rs (se 2 (by rfl) ⟨37266, by rfl⟩) R74533
theorem R99427 : Reach 99427 := rs (se 1 (by rfl) ⟨74570, by rfl⟩) R149141
theorem R66737 : Reach 66737 := rs (se 2 (by rfl) ⟨25026, by rfl⟩) R50053
theorem R99569 : Reach 99569 := rs (se 2 (by rfl) ⟨37338, by rfl⟩) R74677
theorem R66835 : Reach 66835 := rs (se 1 (by rfl) ⟨50126, by rfl⟩) R100253
theorem R66865 : Reach 66865 := rs (se 2 (by rfl) ⟨25074, by rfl⟩) R50149
theorem R66899 : Reach 66899 := rs (se 1 (by rfl) ⟨50174, by rfl⟩) R100349
theorem R132461 : Reach 132461 := rs (se 3 (by rfl) ⟨24836, by rfl⟩) R49673
theorem R132515 : Reach 132515 := rs (se 1 (by rfl) ⟨99386, by rfl⟩) R198773
theorem R67027 : Reach 67027 := rs (se 1 (by rfl) ⟨50270, by rfl⟩) R100541
theorem R67169 : Reach 67169 := rs (se 2 (by rfl) ⟨25188, by rfl⟩) R50377
theorem R132785 : Reach 132785 := rs (se 2 (by rfl) ⟨49794, by rfl⟩) R99589
theorem R67297 : Reach 67297 := rs (se 2 (by rfl) ⟨25236, by rfl⟩) R50473
theorem R67331 : Reach 67331 := rs (se 1 (by rfl) ⟨50498, by rfl⟩) R100997
theorem R198449 : Reach 198449 := rs (se 2 (by rfl) ⟨74418, by rfl⟩) R148837
theorem R67459 : Reach 67459 := rs (se 1 (by rfl) ⟨50594, by rfl⟩) R101189
theorem R853901 : Reach 853901 := rs (se 3 (by rfl) ⟨160106, by rfl⟩) R320213
theorem R67601 : Reach 67601 := rs (se 2 (by rfl) ⟨25350, by rfl⟩) R50701
theorem R67729 : Reach 67729 := rs (se 2 (by rfl) ⟨25398, by rfl⟩) R50797
theorem R67763 : Reach 67763 := rs (se 1 (by rfl) ⟨50822, by rfl⟩) R101645
theorem R133325 : Reach 133325 := rs (se 3 (by rfl) ⟨24998, by rfl⟩) R49997
theorem R100561 : Reach 100561 := rs (se 2 (by rfl) ⟨37710, by rfl⟩) R75421
theorem R133379 : Reach 133379 := rs (se 1 (by rfl) ⟨100034, by rfl⟩) R200069
theorem R67873 : Reach 67873 := rs (se 2 (by rfl) ⟨25452, by rfl⟩) R50905
theorem R67891 : Reach 67891 := rs (se 1 (by rfl) ⟨50918, by rfl⟩) R101837
theorem R68033 : Reach 68033 := rs (se 2 (by rfl) ⟨25512, by rfl⟩) R51025
theorem R100835 : Reach 100835 := rs (se 1 (by rfl) ⟨75626, by rfl⟩) R151253
theorem R133649 : Reach 133649 := rs (se 2 (by rfl) ⟨50118, by rfl⟩) R100237
theorem R68161 : Reach 68161 := rs (se 2 (by rfl) ⟨25560, by rfl⟩) R51121
theorem R68195 : Reach 68195 := rs (se 1 (by rfl) ⟨51146, by rfl⟩) R102293
theorem R101027 : Reach 101027 := rs (se 1 (by rfl) ⟨75770, by rfl⟩) R151541
theorem R68321 : Reach 68321 := rs (se 2 (by rfl) ⟨25620, by rfl⟩) R51241
theorem R68323 : Reach 68323 := rs (se 1 (by rfl) ⟨51242, by rfl⟩) R102485
theorem R265037 : Reach 265037 := rs (se 3 (by rfl) ⟨49694, by rfl⟩) R99389
theorem R199523 : Reach 199523 := rs (se 1 (by rfl) ⟨149642, by rfl⟩) R299285
theorem R68465 : Reach 68465 := rs (se 2 (by rfl) ⟨25674, by rfl⟩) R51349
theorem R68531 : Reach 68531 := rs (se 1 (by rfl) ⟨51398, by rfl⟩) R102797
theorem R68593 : Reach 68593 := rs (se 2 (by rfl) ⟨25722, by rfl⟩) R51445
theorem R68627 : Reach 68627 := rs (se 1 (by rfl) ⟨51470, by rfl⟩) R102941
theorem R134189 : Reach 134189 := rs (se 3 (by rfl) ⟨25160, by rfl⟩) R50321
theorem R134243 : Reach 134243 := rs (se 1 (by rfl) ⟨100682, by rfl⟩) R201365
theorem R68723 : Reach 68723 := rs (se 1 (by rfl) ⟨51542, by rfl⟩) R103085
theorem R68737 : Reach 68737 := rs (se 2 (by rfl) ⟨25776, by rfl⟩) R51553
theorem R68755 : Reach 68755 := rs (se 1 (by rfl) ⟨51566, by rfl⟩) R103133
theorem R199907 : Reach 199907 := rs (se 1 (by rfl) ⟨149930, by rfl⟩) R299861
theorem R68897 : Reach 68897 := rs (se 2 (by rfl) ⟨25836, by rfl⟩) R51673
theorem R134513 : Reach 134513 := rs (se 2 (by rfl) ⟨50442, by rfl⟩) R100885
theorem R69025 : Reach 69025 := rs (se 2 (by rfl) ⟨25884, by rfl⟩) R51769
theorem R69059 : Reach 69059 := rs (se 1 (by rfl) ⟨51794, by rfl⟩) R103589
theorem R232901 : Reach 232901 := rs (se 4 (by rfl) ⟨21834, by rfl⟩) R43669
theorem R69187 : Reach 69187 := rs (se 1 (by rfl) ⟨51890, by rfl⟩) R103781
theorem R101969 : Reach 101969 := rs (se 2 (by rfl) ⟨38238, by rfl⟩) R76477
theorem R102019 : Reach 102019 := rs (se 1 (by rfl) ⟨76514, by rfl⟩) R153029
theorem R134797 : Reach 134797 := rs (se 3 (by rfl) ⟨25274, by rfl⟩) R50549
theorem R69329 : Reach 69329 := rs (se 2 (by rfl) ⟨25998, by rfl⟩) R51997
theorem R102161 : Reach 102161 := rs (se 2 (by rfl) ⟨38310, by rfl⟩) R76621
theorem R69457 : Reach 69457 := rs (se 2 (by rfl) ⟨26046, by rfl⟩) R52093
theorem R69491 : Reach 69491 := rs (se 1 (by rfl) ⟨52118, by rfl⟩) R104237
theorem R135053 : Reach 135053 := rs (se 3 (by rfl) ⟨25322, by rfl⟩) R50645
theorem R135107 : Reach 135107 := rs (se 1 (by rfl) ⟨101330, by rfl⟩) R202661
theorem R200717 : Reach 200717 := rs (se 3 (by rfl) ⟨37634, by rfl⟩) R75269
theorem R135245 : Reach 135245 := rs (se 3 (by rfl) ⟨25358, by rfl⟩) R50717
theorem R135377 : Reach 135377 := rs (se 2 (by rfl) ⟨50766, by rfl⟩) R101533
theorem R69923 : Reach 69923 := rs (se 1 (by rfl) ⟨52442, by rfl⟩) R104885
theorem R135587 : Reach 135587 := rs (se 1 (by rfl) ⟨101690, by rfl⟩) R203381
theorem R70051 : Reach 70051 := rs (se 1 (by rfl) ⟨52538, by rfl⟩) R105077
theorem R266723 : Reach 266723 := rs (se 1 (by rfl) ⟨200042, by rfl⟩) R400085
theorem R70193 : Reach 70193 := rs (se 2 (by rfl) ⟨26322, by rfl⟩) R52645
theorem R70321 : Reach 70321 := rs (se 2 (by rfl) ⟨26370, by rfl⟩) R52741
theorem R135917 : Reach 135917 := rs (se 3 (by rfl) ⟨25484, by rfl⟩) R50969
theorem R103153 : Reach 103153 := rs (se 2 (by rfl) ⟨38682, by rfl⟩) R77365
theorem R1151765 : Reach 1151765 := rs (se 6 (by rfl) ⟨26994, by rfl⟩) R53989
theorem R135971 : Reach 135971 := rs (se 1 (by rfl) ⟨101978, by rfl⟩) R203957
theorem R168803 : Reach 168803 := rs (se 1 (by rfl) ⟨126602, by rfl⟩) R253205
theorem R234373 : Reach 234373 := rs (se 4 (by rfl) ⟨21972, by rfl⟩) R43945
theorem R103427 : Reach 103427 := rs (se 1 (by rfl) ⟨77570, by rfl⟩) R155141
theorem R136241 : Reach 136241 := rs (se 2 (by rfl) ⟨51090, by rfl⟩) R102181
theorem R70787 : Reach 70787 := rs (se 1 (by rfl) ⟨53090, by rfl⟩) R106181
theorem R103619 : Reach 103619 := rs (se 1 (by rfl) ⟨77714, by rfl⟩) R155429
theorem R70865 : Reach 70865 := rs (se 2 (by rfl) ⟨26574, by rfl⟩) R53149
theorem R70915 : Reach 70915 := rs (se 1 (by rfl) ⟨53186, by rfl⟩) R106373
theorem R71057 : Reach 71057 := rs (se 2 (by rfl) ⟨26646, by rfl⟩) R53293
theorem R71185 : Reach 71185 := rs (se 2 (by rfl) ⟨26694, by rfl⟩) R53389
theorem R136781 : Reach 136781 := rs (se 3 (by rfl) ⟨25646, by rfl⟩) R51293
theorem R136835 : Reach 136835 := rs (se 1 (by rfl) ⟨102626, by rfl⟩) R205253
theorem R71459 : Reach 71459 := rs (se 1 (by rfl) ⟨53594, by rfl⟩) R107189
theorem R137105 : Reach 137105 := rs (se 2 (by rfl) ⟨51414, by rfl⟩) R102829
theorem R71651 : Reach 71651 := rs (se 1 (by rfl) ⟨53738, by rfl⟩) R107477
theorem R104429 : Reach 104429 := rs (se 3 (by rfl) ⟨19580, by rfl⟩) R39161
theorem R71779 : Reach 71779 := rs (se 1 (by rfl) ⟨53834, by rfl⟩) R107669
theorem R104561 : Reach 104561 := rs (se 2 (by rfl) ⟨39210, by rfl⟩) R78421
theorem R104611 : Reach 104611 := rs (se 1 (by rfl) ⟨78458, by rfl⟩) R156917
theorem R39123 : Reach 39123 := rs (se 1 (by rfl) ⟨29342, by rfl⟩) R58685
theorem R39139 : Reach 39139 := rs (se 1 (by rfl) ⟨29354, by rfl⟩) R58709
theorem R71921 : Reach 71921 := rs (se 2 (by rfl) ⟨26970, by rfl⟩) R53941
theorem R39155 : Reach 39155 := rs (se 1 (by rfl) ⟨29366, by rfl⟩) R58733
theorem R39171 : Reach 39171 := rs (se 1 (by rfl) ⟨29378, by rfl⟩) R58757
theorem R39187 : Reach 39187 := rs (se 1 (by rfl) ⟨29390, by rfl⟩) R58781
theorem R39203 : Reach 39203 := rs (se 1 (by rfl) ⟨29402, by rfl⟩) R58805
theorem R104753 : Reach 104753 := rs (se 2 (by rfl) ⟨39282, by rfl⟩) R78565
theorem R39219 : Reach 39219 := rs (se 1 (by rfl) ⟨29414, by rfl⟩) R58829
theorem R39235 : Reach 39235 := rs (se 1 (by rfl) ⟨29426, by rfl⟩) R58853
theorem R39251 : Reach 39251 := rs (se 1 (by rfl) ⟨29438, by rfl⟩) R58877
theorem R39267 : Reach 39267 := rs (se 1 (by rfl) ⟨29450, by rfl⟩) R58901
theorem R72049 : Reach 72049 := rs (se 2 (by rfl) ⟨27018, by rfl⟩) R54037
theorem R39283 : Reach 39283 := rs (se 1 (by rfl) ⟨29462, by rfl⟩) R58925
theorem R39299 : Reach 39299 := rs (se 1 (by rfl) ⟨29474, by rfl⟩) R58949
theorem R39315 : Reach 39315 := rs (se 1 (by rfl) ⟨29486, by rfl⟩) R58973
theorem R39331 : Reach 39331 := rs (se 1 (by rfl) ⟨29498, by rfl⟩) R58997
theorem R137645 : Reach 137645 := rs (se 3 (by rfl) ⟨25808, by rfl⟩) R51617
theorem R39347 : Reach 39347 := rs (se 1 (by rfl) ⟨29510, by rfl⟩) R59021
theorem R39363 : Reach 39363 := rs (se 1 (by rfl) ⟨29522, by rfl⟩) R59045
theorem R39379 : Reach 39379 := rs (se 1 (by rfl) ⟨29534, by rfl⟩) R59069
theorem R39395 : Reach 39395 := rs (se 1 (by rfl) ⟨29546, by rfl⟩) R59093
theorem R137699 : Reach 137699 := rs (se 1 (by rfl) ⟨103274, by rfl⟩) R206549
theorem R39411 : Reach 39411 := rs (se 1 (by rfl) ⟨29558, by rfl⟩) R59117
theorem R39427 : Reach 39427 := rs (se 1 (by rfl) ⟨29570, by rfl⟩) R59141
theorem R39443 : Reach 39443 := rs (se 1 (by rfl) ⟨29582, by rfl⟩) R59165
theorem R39459 : Reach 39459 := rs (se 1 (by rfl) ⟨29594, by rfl⟩) R59189
theorem R72227 : Reach 72227 := rs (se 1 (by rfl) ⟨54170, by rfl⟩) R108341
theorem R39475 : Reach 39475 := rs (se 1 (by rfl) ⟨29606, by rfl⟩) R59213
theorem R39491 : Reach 39491 := rs (se 1 (by rfl) ⟨29618, by rfl⟩) R59237
theorem R39507 : Reach 39507 := rs (se 1 (by rfl) ⟨29630, by rfl⟩) R59261
theorem R39523 : Reach 39523 := rs (se 1 (by rfl) ⟨29642, by rfl⟩) R59285
theorem R39539 : Reach 39539 := rs (se 1 (by rfl) ⟨29654, by rfl⟩) R59309
theorem R39555 : Reach 39555 := rs (se 1 (by rfl) ⟨29666, by rfl⟩) R59333
theorem R39571 : Reach 39571 := rs (se 1 (by rfl) ⟨29678, by rfl⟩) R59357
theorem R39587 : Reach 39587 := rs (se 1 (by rfl) ⟨29690, by rfl⟩) R59381
theorem R39603 : Reach 39603 := rs (se 1 (by rfl) ⟨29702, by rfl⟩) R59405
theorem R39619 : Reach 39619 := rs (se 1 (by rfl) ⟨29714, by rfl⟩) R59429
theorem R39635 : Reach 39635 := rs (se 1 (by rfl) ⟨29726, by rfl⟩) R59453
theorem R39651 : Reach 39651 := rs (se 1 (by rfl) ⟨29738, by rfl⟩) R59477
theorem R170723 : Reach 170723 := rs (se 1 (by rfl) ⟨128042, by rfl⟩) R256085
theorem R137969 : Reach 137969 := rs (se 2 (by rfl) ⟨51738, by rfl⟩) R103477
theorem R39667 : Reach 39667 := rs (se 1 (by rfl) ⟨29750, by rfl⟩) R59501
theorem R39683 : Reach 39683 := rs (se 1 (by rfl) ⟨29762, by rfl⟩) R59525
theorem R137987 : Reach 137987 := rs (se 1 (by rfl) ⟨103490, by rfl⟩) R206981
theorem R39699 : Reach 39699 := rs (se 1 (by rfl) ⟨29774, by rfl⟩) R59549
theorem R39715 : Reach 39715 := rs (se 1 (by rfl) ⟨29786, by rfl⟩) R59573
theorem R39731 : Reach 39731 := rs (se 1 (by rfl) ⟨29798, by rfl⟩) R59597
theorem R39747 : Reach 39747 := rs (se 1 (by rfl) ⟨29810, by rfl⟩) R59621
theorem R72515 : Reach 72515 := rs (se 1 (by rfl) ⟨54386, by rfl⟩) R108773
theorem R236357 : Reach 236357 := rs (se 4 (by rfl) ⟨22158, by rfl⟩) R44317
theorem R203597 : Reach 203597 := rs (se 3 (by rfl) ⟨38174, by rfl⟩) R76349
theorem R39763 : Reach 39763 := rs (se 1 (by rfl) ⟨29822, by rfl⟩) R59645
theorem R39779 : Reach 39779 := rs (se 1 (by rfl) ⟨29834, by rfl⟩) R59669
theorem R203633 : Reach 203633 := rs (se 2 (by rfl) ⟨76362, by rfl⟩) R152725
theorem R39795 : Reach 39795 := rs (se 1 (by rfl) ⟨29846, by rfl⟩) R59693
theorem R39811 : Reach 39811 := rs (se 1 (by rfl) ⟨29858, by rfl⟩) R59717
theorem R138115 : Reach 138115 := rs (se 1 (by rfl) ⟨103586, by rfl⟩) R207173
theorem R39827 : Reach 39827 := rs (se 1 (by rfl) ⟨29870, by rfl⟩) R59741
theorem R39843 : Reach 39843 := rs (se 1 (by rfl) ⟨29882, by rfl⟩) R59765
theorem R39859 : Reach 39859 := rs (se 1 (by rfl) ⟨29894, by rfl⟩) R59789
theorem R39875 : Reach 39875 := rs (se 1 (by rfl) ⟨29906, by rfl⟩) R59813
theorem R72643 : Reach 72643 := rs (se 1 (by rfl) ⟨54482, by rfl⟩) R108965
theorem R105421 : Reach 105421 := rs (se 3 (by rfl) ⟨19766, by rfl⟩) R39533
theorem R39891 : Reach 39891 := rs (se 1 (by rfl) ⟨29918, by rfl⟩) R59837
theorem R39907 : Reach 39907 := rs (se 1 (by rfl) ⟨29930, by rfl⟩) R59861
theorem R39923 : Reach 39923 := rs (se 1 (by rfl) ⟨29942, by rfl⟩) R59885
theorem R39939 : Reach 39939 := rs (se 1 (by rfl) ⟨29954, by rfl⟩) R59909
theorem R39955 : Reach 39955 := rs (se 1 (by rfl) ⟨29966, by rfl⟩) R59933
theorem R39971 : Reach 39971 := rs (se 1 (by rfl) ⟨29978, by rfl⟩) R59957
theorem R269347 : Reach 269347 := rs (se 1 (by rfl) ⟨202010, by rfl⟩) R404021
theorem R39987 : Reach 39987 := rs (se 1 (by rfl) ⟨29990, by rfl⟩) R59981
theorem R40003 : Reach 40003 := rs (se 1 (by rfl) ⟨30002, by rfl⟩) R60005
theorem R40019 : Reach 40019 := rs (se 1 (by rfl) ⟨30014, by rfl⟩) R60029
theorem R40035 : Reach 40035 := rs (se 1 (by rfl) ⟨30026, by rfl⟩) R60053
theorem R40051 : Reach 40051 := rs (se 1 (by rfl) ⟨30038, by rfl⟩) R60077
theorem R40067 : Reach 40067 := rs (se 1 (by rfl) ⟨30050, by rfl⟩) R60101
theorem R40083 : Reach 40083 := rs (se 1 (by rfl) ⟨30062, by rfl⟩) R60125
theorem R40099 : Reach 40099 := rs (se 1 (by rfl) ⟨30074, by rfl⟩) R60149
theorem R40115 : Reach 40115 := rs (se 1 (by rfl) ⟨30086, by rfl⟩) R60173
theorem R40131 : Reach 40131 := rs (se 1 (by rfl) ⟨30098, by rfl⟩) R60197
theorem R40147 : Reach 40147 := rs (se 1 (by rfl) ⟨30110, by rfl⟩) R60221
theorem R40163 : Reach 40163 := rs (se 1 (by rfl) ⟨30122, by rfl⟩) R60245
theorem R40179 : Reach 40179 := rs (se 1 (by rfl) ⟨30134, by rfl⟩) R60269
theorem R40195 : Reach 40195 := rs (se 1 (by rfl) ⟨30146, by rfl⟩) R60293
theorem R138509 : Reach 138509 := rs (se 3 (by rfl) ⟨25970, by rfl⟩) R51941
theorem R105745 : Reach 105745 := rs (se 2 (by rfl) ⟨39654, by rfl⟩) R79309
theorem R40211 : Reach 40211 := rs (se 1 (by rfl) ⟨30158, by rfl⟩) R60317
theorem R40227 : Reach 40227 := rs (se 1 (by rfl) ⟨30170, by rfl⟩) R60341
theorem R40243 : Reach 40243 := rs (se 1 (by rfl) ⟨30182, by rfl⟩) R60365
theorem R40259 : Reach 40259 := rs (se 1 (by rfl) ⟨30194, by rfl⟩) R60389
theorem R138563 : Reach 138563 := rs (se 1 (by rfl) ⟨103922, by rfl⟩) R207845
theorem R40275 : Reach 40275 := rs (se 1 (by rfl) ⟨30206, by rfl⟩) R60413
theorem R40291 : Reach 40291 := rs (se 1 (by rfl) ⟨30218, by rfl⟩) R60437
theorem R40307 : Reach 40307 := rs (se 1 (by rfl) ⟨30230, by rfl⟩) R60461
theorem R40323 : Reach 40323 := rs (se 1 (by rfl) ⟨30242, by rfl⟩) R60485
theorem R40339 : Reach 40339 := rs (se 1 (by rfl) ⟨30254, by rfl⟩) R60509
theorem R40355 : Reach 40355 := rs (se 1 (by rfl) ⟨30266, by rfl⟩) R60533
theorem R40371 : Reach 40371 := rs (se 1 (by rfl) ⟨30278, by rfl⟩) R60557
theorem R40387 : Reach 40387 := rs (se 1 (by rfl) ⟨30290, by rfl⟩) R60581
theorem R40403 : Reach 40403 := rs (se 1 (by rfl) ⟨30302, by rfl⟩) R60605
theorem R40419 : Reach 40419 := rs (se 1 (by rfl) ⟨30314, by rfl⟩) R60629
theorem R40435 : Reach 40435 := rs (se 1 (by rfl) ⟨30326, by rfl⟩) R60653
theorem R40451 : Reach 40451 := rs (se 1 (by rfl) ⟨30338, by rfl⟩) R60677
theorem R40467 : Reach 40467 := rs (se 1 (by rfl) ⟨30350, by rfl⟩) R60701
theorem R40483 : Reach 40483 := rs (se 1 (by rfl) ⟨30362, by rfl⟩) R60725
theorem R106019 : Reach 106019 := rs (se 1 (by rfl) ⟨79514, by rfl⟩) R159029
theorem R40499 : Reach 40499 := rs (se 1 (by rfl) ⟨30374, by rfl⟩) R60749
theorem R40515 : Reach 40515 := rs (se 1 (by rfl) ⟨30386, by rfl⟩) R60773
theorem R138833 : Reach 138833 := rs (se 2 (by rfl) ⟨52062, by rfl⟩) R104125
theorem R40531 : Reach 40531 := rs (se 1 (by rfl) ⟨30398, by rfl⟩) R60797
theorem R40547 : Reach 40547 := rs (se 1 (by rfl) ⟨30410, by rfl⟩) R60821
theorem R40563 : Reach 40563 := rs (se 1 (by rfl) ⟨30422, by rfl⟩) R60845
theorem R40579 : Reach 40579 := rs (se 1 (by rfl) ⟨30434, by rfl⟩) R60869
theorem R335501 : Reach 335501 := rs (se 3 (by rfl) ⟨62906, by rfl⟩) R125813
theorem R40595 : Reach 40595 := rs (se 1 (by rfl) ⟨30446, by rfl⟩) R60893
theorem R40611 : Reach 40611 := rs (se 1 (by rfl) ⟨30458, by rfl⟩) R60917
theorem R40627 : Reach 40627 := rs (se 1 (by rfl) ⟨30470, by rfl⟩) R60941
theorem R40643 : Reach 40643 := rs (se 1 (by rfl) ⟨30482, by rfl⟩) R60965
theorem R990917 : Reach 990917 := rs (se 4 (by rfl) ⟨92898, by rfl⟩) R185797
theorem R40659 : Reach 40659 := rs (se 1 (by rfl) ⟨30494, by rfl⟩) R60989
theorem R40675 : Reach 40675 := rs (se 1 (by rfl) ⟨30506, by rfl⟩) R61013
theorem R106211 : Reach 106211 := rs (se 1 (by rfl) ⟨79658, by rfl⟩) R159317
theorem R40691 : Reach 40691 := rs (se 1 (by rfl) ⟨30518, by rfl⟩) R61037
theorem R40707 : Reach 40707 := rs (se 1 (by rfl) ⟨30530, by rfl⟩) R61061
theorem R40723 : Reach 40723 := rs (se 1 (by rfl) ⟨30542, by rfl⟩) R61085
theorem R40739 : Reach 40739 := rs (se 1 (by rfl) ⟨30554, by rfl⟩) R61109
theorem R40755 : Reach 40755 := rs (se 1 (by rfl) ⟨30566, by rfl⟩) R61133
theorem R40771 : Reach 40771 := rs (se 1 (by rfl) ⟨30578, by rfl⟩) R61157
theorem R40787 : Reach 40787 := rs (se 1 (by rfl) ⟨30590, by rfl⟩) R61181
theorem R40803 : Reach 40803 := rs (se 1 (by rfl) ⟨30602, by rfl⟩) R61205
theorem R204643 : Reach 204643 := rs (se 1 (by rfl) ⟨153482, by rfl⟩) R306965
theorem R40819 : Reach 40819 := rs (se 1 (by rfl) ⟨30614, by rfl⟩) R61229
theorem R40835 : Reach 40835 := rs (se 1 (by rfl) ⟨30626, by rfl⟩) R61253
theorem R40851 : Reach 40851 := rs (se 1 (by rfl) ⟨30638, by rfl⟩) R61277
theorem R40867 : Reach 40867 := rs (se 1 (by rfl) ⟨30650, by rfl⟩) R61301
theorem R171953 : Reach 171953 := rs (se 2 (by rfl) ⟨64482, by rfl⟩) R128965
theorem R40883 : Reach 40883 := rs (se 1 (by rfl) ⟨30662, by rfl⟩) R61325
theorem R40899 : Reach 40899 := rs (se 1 (by rfl) ⟨30674, by rfl⟩) R61349
theorem R40915 : Reach 40915 := rs (se 1 (by rfl) ⟨30686, by rfl⟩) R61373
theorem R40931 : Reach 40931 := rs (se 1 (by rfl) ⟨30698, by rfl⟩) R61397
theorem R40947 : Reach 40947 := rs (se 1 (by rfl) ⟨30710, by rfl⟩) R61421
theorem R40963 : Reach 40963 := rs (se 1 (by rfl) ⟨30722, by rfl⟩) R61445
theorem R40979 : Reach 40979 := rs (se 1 (by rfl) ⟨30734, by rfl⟩) R61469
theorem R40995 : Reach 40995 := rs (se 1 (by rfl) ⟨30746, by rfl⟩) R61493
theorem R41011 : Reach 41011 := rs (se 1 (by rfl) ⟨30758, by rfl⟩) R61517
theorem R41027 : Reach 41027 := rs (se 1 (by rfl) ⟨30770, by rfl⟩) R61541
theorem R41043 : Reach 41043 := rs (se 1 (by rfl) ⟨30782, by rfl⟩) R61565
theorem R41059 : Reach 41059 := rs (se 1 (by rfl) ⟨30794, by rfl⟩) R61589
theorem R41075 : Reach 41075 := rs (se 1 (by rfl) ⟨30806, by rfl⟩) R61613
theorem R41091 : Reach 41091 := rs (se 1 (by rfl) ⟨30818, by rfl⟩) R61637
theorem R41107 : Reach 41107 := rs (se 1 (by rfl) ⟨30830, by rfl⟩) R61661
theorem R41123 : Reach 41123 := rs (se 1 (by rfl) ⟨30842, by rfl⟩) R61685
theorem R139427 : Reach 139427 := rs (se 1 (by rfl) ⟨104570, by rfl⟩) R209141
theorem R41139 : Reach 41139 := rs (se 1 (by rfl) ⟨30854, by rfl⟩) R61709
theorem R41155 : Reach 41155 := rs (se 1 (by rfl) ⟨30866, by rfl⟩) R61733
theorem R41171 : Reach 41171 := rs (se 1 (by rfl) ⟨30878, by rfl⟩) R61757
theorem R41187 : Reach 41187 := rs (se 1 (by rfl) ⟨30890, by rfl⟩) R61781
theorem R41203 : Reach 41203 := rs (se 1 (by rfl) ⟨30902, by rfl⟩) R61805
theorem R41219 : Reach 41219 := rs (se 1 (by rfl) ⟨30914, by rfl⟩) R61829
theorem R41235 : Reach 41235 := rs (se 1 (by rfl) ⟨30926, by rfl⟩) R61853
theorem R205091 : Reach 205091 := rs (se 1 (by rfl) ⟨153818, by rfl⟩) R307637
theorem R41251 : Reach 41251 := rs (se 1 (by rfl) ⟨30938, by rfl⟩) R61877
theorem R270641 : Reach 270641 := rs (se 2 (by rfl) ⟨101490, by rfl⟩) R202981
theorem R41267 : Reach 41267 := rs (se 1 (by rfl) ⟨30950, by rfl⟩) R61901
theorem R41283 : Reach 41283 := rs (se 1 (by rfl) ⟨30962, by rfl⟩) R61925
theorem R106829 : Reach 106829 := rs (se 3 (by rfl) ⟨20030, by rfl⟩) R40061
theorem R41299 : Reach 41299 := rs (se 1 (by rfl) ⟨30974, by rfl⟩) R61949
theorem R41315 : Reach 41315 := rs (se 1 (by rfl) ⟨30986, by rfl⟩) R61973
theorem R41331 : Reach 41331 := rs (se 1 (by rfl) ⟨30998, by rfl⟩) R61997
theorem R41347 : Reach 41347 := rs (se 1 (by rfl) ⟨31010, by rfl⟩) R62021
theorem R41363 : Reach 41363 := rs (se 1 (by rfl) ⟨31022, by rfl⟩) R62045
theorem R41379 : Reach 41379 := rs (se 1 (by rfl) ⟨31034, by rfl⟩) R62069
theorem R139697 : Reach 139697 := rs (se 2 (by rfl) ⟨52386, by rfl⟩) R104773
theorem R41395 : Reach 41395 := rs (se 1 (by rfl) ⟨31046, by rfl⟩) R62093
theorem R41411 : Reach 41411 := rs (se 1 (by rfl) ⟨31058, by rfl⟩) R62117
theorem R41427 : Reach 41427 := rs (se 1 (by rfl) ⟨31070, by rfl⟩) R62141
theorem R41443 : Reach 41443 := rs (se 1 (by rfl) ⟨31082, by rfl⟩) R62165
theorem R41459 : Reach 41459 := rs (se 1 (by rfl) ⟨31094, by rfl⟩) R62189
theorem R41475 : Reach 41475 := rs (se 1 (by rfl) ⟨31106, by rfl⟩) R62213
theorem R107021 : Reach 107021 := rs (se 3 (by rfl) ⟨20066, by rfl⟩) R40133
theorem R41491 : Reach 41491 := rs (se 1 (by rfl) ⟨31118, by rfl⟩) R62237
theorem R41507 : Reach 41507 := rs (se 1 (by rfl) ⟨31130, by rfl⟩) R62261
theorem R41523 : Reach 41523 := rs (se 1 (by rfl) ⟨31142, by rfl⟩) R62285
theorem R41539 : Reach 41539 := rs (se 1 (by rfl) ⟨31154, by rfl⟩) R62309
theorem R41555 : Reach 41555 := rs (se 1 (by rfl) ⟨31166, by rfl⟩) R62333
theorem R41571 : Reach 41571 := rs (se 1 (by rfl) ⟨31178, by rfl⟩) R62357
theorem R41587 : Reach 41587 := rs (se 1 (by rfl) ⟨31190, by rfl⟩) R62381
theorem R41603 : Reach 41603 := rs (se 1 (by rfl) ⟨31202, by rfl⟩) R62405
theorem R107153 : Reach 107153 := rs (se 2 (by rfl) ⟨40182, by rfl⟩) R80365
theorem R41619 : Reach 41619 := rs (se 1 (by rfl) ⟨31214, by rfl⟩) R62429
theorem R41635 : Reach 41635 := rs (se 1 (by rfl) ⟨31226, by rfl⟩) R62453
theorem R41651 : Reach 41651 := rs (se 1 (by rfl) ⟨31238, by rfl⟩) R62477
theorem R41667 : Reach 41667 := rs (se 1 (by rfl) ⟨31250, by rfl⟩) R62501
theorem R107203 : Reach 107203 := rs (se 1 (by rfl) ⟨80402, by rfl⟩) R160805
theorem R74449 : Reach 74449 := rs (se 2 (by rfl) ⟨27918, by rfl⟩) R55837
theorem R41683 : Reach 41683 := rs (se 1 (by rfl) ⟨31262, by rfl⟩) R62525
theorem R41699 : Reach 41699 := rs (se 1 (by rfl) ⟨31274, by rfl⟩) R62549
theorem R41715 : Reach 41715 := rs (se 1 (by rfl) ⟨31286, by rfl⟩) R62573
theorem R41731 : Reach 41731 := rs (se 1 (by rfl) ⟨31298, by rfl⟩) R62597
theorem R41747 : Reach 41747 := rs (se 1 (by rfl) ⟨31310, by rfl⟩) R62621
theorem R41763 : Reach 41763 := rs (se 1 (by rfl) ⟨31322, by rfl⟩) R62645
theorem R41779 : Reach 41779 := rs (se 1 (by rfl) ⟨31334, by rfl⟩) R62669
theorem R41795 : Reach 41795 := rs (se 1 (by rfl) ⟨31346, by rfl⟩) R62693
theorem R107345 : Reach 107345 := rs (se 2 (by rfl) ⟨40254, by rfl⟩) R80509
theorem R41811 : Reach 41811 := rs (se 1 (by rfl) ⟨31358, by rfl⟩) R62717
theorem R41827 : Reach 41827 := rs (se 1 (by rfl) ⟨31370, by rfl⟩) R62741
theorem R41843 : Reach 41843 := rs (se 1 (by rfl) ⟨31382, by rfl⟩) R62765
theorem R41859 : Reach 41859 := rs (se 1 (by rfl) ⟨31394, by rfl⟩) R62789
theorem R41875 : Reach 41875 := rs (se 1 (by rfl) ⟨31406, by rfl⟩) R62813
theorem R41891 : Reach 41891 := rs (se 1 (by rfl) ⟨31418, by rfl⟩) R62837
theorem R41907 : Reach 41907 := rs (se 1 (by rfl) ⟨31430, by rfl⟩) R62861
theorem R41923 : Reach 41923 := rs (se 1 (by rfl) ⟨31442, by rfl⟩) R62885
theorem R140237 : Reach 140237 := rs (se 3 (by rfl) ⟨26294, by rfl⟩) R52589
theorem R271309 : Reach 271309 := rs (se 3 (by rfl) ⟨50870, by rfl⟩) R101741
theorem R41939 : Reach 41939 := rs (se 1 (by rfl) ⟨31454, by rfl⟩) R62909
theorem R41955 : Reach 41955 := rs (se 1 (by rfl) ⟨31466, by rfl⟩) R62933
theorem R41971 : Reach 41971 := rs (se 1 (by rfl) ⟨31478, by rfl⟩) R62957
theorem R41987 : Reach 41987 := rs (se 1 (by rfl) ⟨31490, by rfl⟩) R62981
theorem R42003 : Reach 42003 := rs (se 1 (by rfl) ⟨31502, by rfl⟩) R63005
theorem R926741 : Reach 926741 := rs (se 6 (by rfl) ⟨21720, by rfl⟩) R43441
theorem R42019 : Reach 42019 := rs (se 1 (by rfl) ⟨31514, by rfl⟩) R63029
theorem R42035 : Reach 42035 := rs (se 1 (by rfl) ⟨31526, by rfl⟩) R63053
theorem R42051 : Reach 42051 := rs (se 1 (by rfl) ⟨31538, by rfl⟩) R63077
theorem R205901 : Reach 205901 := rs (se 3 (by rfl) ⟨38606, by rfl⟩) R77213
theorem R42067 : Reach 42067 := rs (se 1 (by rfl) ⟨31550, by rfl⟩) R63101
theorem R42083 : Reach 42083 := rs (se 1 (by rfl) ⟨31562, by rfl⟩) R63125
theorem R42099 : Reach 42099 := rs (se 1 (by rfl) ⟨31574, by rfl⟩) R63149
theorem R42115 : Reach 42115 := rs (se 1 (by rfl) ⟨31586, by rfl⟩) R63173
theorem R42131 : Reach 42131 := rs (se 1 (by rfl) ⟨31598, by rfl⟩) R63197
theorem R42147 : Reach 42147 := rs (se 1 (by rfl) ⟨31610, by rfl⟩) R63221
theorem R42163 : Reach 42163 := rs (se 1 (by rfl) ⟨31622, by rfl⟩) R63245
theorem R42179 : Reach 42179 := rs (se 1 (by rfl) ⟨31634, by rfl⟩) R63269
theorem R42195 : Reach 42195 := rs (se 1 (by rfl) ⟨31646, by rfl⟩) R63293
theorem R42211 : Reach 42211 := rs (se 1 (by rfl) ⟨31658, by rfl⟩) R63317
theorem R42227 : Reach 42227 := rs (se 1 (by rfl) ⟨31670, by rfl⟩) R63341
theorem R42243 : Reach 42243 := rs (se 1 (by rfl) ⟨31682, by rfl⟩) R63365
theorem R42259 : Reach 42259 := rs (se 1 (by rfl) ⟨31694, by rfl⟩) R63389
theorem R42275 : Reach 42275 := rs (se 1 (by rfl) ⟨31706, by rfl⟩) R63413
theorem R42291 : Reach 42291 := rs (se 1 (by rfl) ⟨31718, by rfl⟩) R63437
theorem R42307 : Reach 42307 := rs (se 1 (by rfl) ⟨31730, by rfl⟩) R63461
theorem R42323 : Reach 42323 := rs (se 1 (by rfl) ⟨31742, by rfl⟩) R63485
theorem R42339 : Reach 42339 := rs (se 1 (by rfl) ⟨31754, by rfl⟩) R63509
theorem R42355 : Reach 42355 := rs (se 1 (by rfl) ⟨31766, by rfl⟩) R63533
theorem R42371 : Reach 42371 := rs (se 1 (by rfl) ⟨31778, by rfl⟩) R63557
theorem R42387 : Reach 42387 := rs (se 1 (by rfl) ⟨31790, by rfl⟩) R63581
theorem R42403 : Reach 42403 := rs (se 1 (by rfl) ⟨31802, by rfl⟩) R63605
theorem R42419 : Reach 42419 := rs (se 1 (by rfl) ⟨31814, by rfl⟩) R63629
theorem R42435 : Reach 42435 := rs (se 1 (by rfl) ⟨31826, by rfl⟩) R63653
theorem R42451 : Reach 42451 := rs (se 1 (by rfl) ⟨31838, by rfl⟩) R63677
theorem R42467 : Reach 42467 := rs (se 1 (by rfl) ⟨31850, by rfl⟩) R63701
theorem R108013 : Reach 108013 := rs (se 3 (by rfl) ⟨20252, by rfl⟩) R40505
theorem R42483 : Reach 42483 := rs (se 1 (by rfl) ⟨31862, by rfl⟩) R63725
theorem R42499 : Reach 42499 := rs (se 1 (by rfl) ⟨31874, by rfl⟩) R63749
theorem R42515 : Reach 42515 := rs (se 1 (by rfl) ⟨31886, by rfl⟩) R63773
theorem R42531 : Reach 42531 := rs (se 1 (by rfl) ⟨31898, by rfl⟩) R63797
theorem R42547 : Reach 42547 := rs (se 1 (by rfl) ⟨31910, by rfl⟩) R63821
theorem R42563 : Reach 42563 := rs (se 1 (by rfl) ⟨31922, by rfl⟩) R63845
theorem R173645 : Reach 173645 := rs (se 3 (by rfl) ⟨32558, by rfl⟩) R65117
theorem R42579 : Reach 42579 := rs (se 1 (by rfl) ⟨31934, by rfl⟩) R63869
theorem R42595 : Reach 42595 := rs (se 1 (by rfl) ⟨31946, by rfl⟩) R63893
theorem R42611 : Reach 42611 := rs (se 1 (by rfl) ⟨31958, by rfl⟩) R63917
theorem R42627 : Reach 42627 := rs (se 1 (by rfl) ⟨31970, by rfl⟩) R63941
theorem R42643 : Reach 42643 := rs (se 1 (by rfl) ⟨31982, by rfl⟩) R63965
theorem R42659 : Reach 42659 := rs (se 1 (by rfl) ⟨31994, by rfl⟩) R63989
theorem R42675 : Reach 42675 := rs (se 1 (by rfl) ⟨32006, by rfl⟩) R64013
theorem R42691 : Reach 42691 := rs (se 1 (by rfl) ⟨32018, by rfl⟩) R64037
theorem R42707 : Reach 42707 := rs (se 1 (by rfl) ⟨32030, by rfl⟩) R64061
theorem R42723 : Reach 42723 := rs (se 1 (by rfl) ⟨32042, by rfl⟩) R64085
theorem R75505 : Reach 75505 := rs (se 2 (by rfl) ⟨28314, by rfl⟩) R56629
theorem R42739 : Reach 42739 := rs (se 1 (by rfl) ⟨32054, by rfl⟩) R64109
theorem R42755 : Reach 42755 := rs (se 1 (by rfl) ⟨32066, by rfl⟩) R64133
theorem R42771 : Reach 42771 := rs (se 1 (by rfl) ⟨32078, by rfl⟩) R64157
theorem R42787 : Reach 42787 := rs (se 1 (by rfl) ⟨32090, by rfl⟩) R64181
theorem R108337 : Reach 108337 := rs (se 2 (by rfl) ⟨40626, by rfl⟩) R81253
theorem R42803 : Reach 42803 := rs (se 1 (by rfl) ⟨32102, by rfl⟩) R64205
theorem R42819 : Reach 42819 := rs (se 1 (by rfl) ⟨32114, by rfl⟩) R64229
theorem R42835 : Reach 42835 := rs (se 1 (by rfl) ⟨32126, by rfl⟩) R64253
theorem R141155 : Reach 141155 := rs (se 1 (by rfl) ⟨105866, by rfl⟩) R211733
theorem R42851 : Reach 42851 := rs (se 1 (by rfl) ⟨32138, by rfl⟩) R64277
theorem R42867 : Reach 42867 := rs (se 1 (by rfl) ⟨32150, by rfl⟩) R64301
theorem R42883 : Reach 42883 := rs (se 1 (by rfl) ⟨32162, by rfl⟩) R64325
theorem R42899 : Reach 42899 := rs (se 1 (by rfl) ⟨32174, by rfl⟩) R64349
theorem R42915 : Reach 42915 := rs (se 1 (by rfl) ⟨32186, by rfl⟩) R64373
theorem R42931 : Reach 42931 := rs (se 1 (by rfl) ⟨32198, by rfl⟩) R64397
theorem R42947 : Reach 42947 := rs (se 1 (by rfl) ⟨32210, by rfl⟩) R64421
theorem R337861 : Reach 337861 := rs (se 4 (by rfl) ⟨31674, by rfl⟩) R63349
theorem R42963 : Reach 42963 := rs (se 1 (by rfl) ⟨32222, by rfl⟩) R64445
theorem R337891 : Reach 337891 := rs (se 1 (by rfl) ⟨253418, by rfl⟩) R506837
theorem R42979 : Reach 42979 := rs (se 1 (by rfl) ⟨32234, by rfl⟩) R64469
theorem R42995 : Reach 42995 := rs (se 1 (by rfl) ⟨32246, by rfl⟩) R64493
theorem R43011 : Reach 43011 := rs (se 1 (by rfl) ⟨32258, by rfl⟩) R64517
theorem R43027 : Reach 43027 := rs (se 1 (by rfl) ⟨32270, by rfl⟩) R64541
theorem R43043 : Reach 43043 := rs (se 1 (by rfl) ⟨32282, by rfl⟩) R64565
theorem R43059 : Reach 43059 := rs (se 1 (by rfl) ⟨32294, by rfl⟩) R64589
theorem R108611 : Reach 108611 := rs (se 1 (by rfl) ⟨81458, by rfl⟩) R162917
theorem R43075 : Reach 43075 := rs (se 1 (by rfl) ⟨32306, by rfl⟩) R64613
theorem R43091 : Reach 43091 := rs (se 1 (by rfl) ⟨32318, by rfl⟩) R64637
theorem R43107 : Reach 43107 := rs (se 1 (by rfl) ⟨32330, by rfl⟩) R64661
theorem R141425 : Reach 141425 := rs (se 2 (by rfl) ⟨53034, by rfl⟩) R106069
theorem R75907 : Reach 75907 := rs (se 1 (by rfl) ⟨56930, by rfl⟩) R113861
theorem R75953 : Reach 75953 := rs (se 2 (by rfl) ⟨28482, by rfl⟩) R56965
theorem R108803 : Reach 108803 := rs (se 1 (by rfl) ⟨81602, by rfl⟩) R163205
theorem R174413 : Reach 174413 := rs (se 3 (by rfl) ⟨32702, by rfl⟩) R65405
theorem R403811 : Reach 403811 := rs (se 1 (by rfl) ⟨302858, by rfl⟩) R605717
theorem R76241 : Reach 76241 := rs (se 2 (by rfl) ⟨28590, by rfl⟩) R57181
theorem R469475 : Reach 469475 := rs (se 1 (by rfl) ⟨352106, by rfl⟩) R704213
theorem R43507 : Reach 43507 := rs (se 1 (by rfl) ⟨32630, by rfl⟩) R65261
theorem R240205 : Reach 240205 := rs (se 3 (by rfl) ⟨45038, by rfl⟩) R90077
theorem R141965 : Reach 141965 := rs (se 3 (by rfl) ⟨26618, by rfl⟩) R53237
theorem R174755 : Reach 174755 := rs (se 1 (by rfl) ⟨131066, by rfl⟩) R262133
theorem R109421 : Reach 109421 := rs (se 3 (by rfl) ⟨20516, by rfl⟩) R41033
theorem R43907 : Reach 43907 := rs (se 1 (by rfl) ⟨32930, by rfl⟩) R65861
theorem R44131 : Reach 44131 := rs (se 1 (by rfl) ⟨33098, by rfl⟩) R66197
theorem R306317 : Reach 306317 := rs (se 3 (by rfl) ⟨57434, by rfl⟩) R114869
theorem R76963 : Reach 76963 := rs (se 1 (by rfl) ⟨57722, by rfl⟩) R115445
theorem R44275 : Reach 44275 := rs (se 1 (by rfl) ⟨33206, by rfl⟩) R66413
theorem R44419 : Reach 44419 := rs (se 1 (by rfl) ⟨33314, by rfl⟩) R66629
theorem R44563 : Reach 44563 := rs (se 1 (by rfl) ⟨33422, by rfl⟩) R66845
theorem R142883 : Reach 142883 := rs (se 1 (by rfl) ⟨107162, by rfl⟩) R214325
theorem R77411 : Reach 77411 := rs (se 1 (by rfl) ⟨58058, by rfl⟩) R116117
theorem R44659 : Reach 44659 := rs (se 1 (by rfl) ⟨33494, by rfl⟩) R66989
theorem R44707 : Reach 44707 := rs (se 1 (by rfl) ⟨33530, by rfl⟩) R67061
theorem R143153 : Reach 143153 := rs (se 2 (by rfl) ⟨53682, by rfl⟩) R107365
theorem R44851 : Reach 44851 := rs (se 1 (by rfl) ⟨33638, by rfl⟩) R67277
theorem R110413 : Reach 110413 := rs (se 3 (by rfl) ⟨20702, by rfl⟩) R41405
theorem R77699 : Reach 77699 := rs (se 1 (by rfl) ⟨58274, by rfl⟩) R116549
theorem R208817 : Reach 208817 := rs (se 2 (by rfl) ⟨78306, by rfl⟩) R156613
theorem R44995 : Reach 44995 := rs (se 1 (by rfl) ⟨33746, by rfl⟩) R67493
theorem R110659 : Reach 110659 := rs (se 1 (by rfl) ⟨82994, by rfl⟩) R165989
theorem R45139 : Reach 45139 := rs (se 1 (by rfl) ⟨33854, by rfl⟩) R67709
theorem R45283 : Reach 45283 := rs (se 1 (by rfl) ⟨33962, by rfl⟩) R67925
theorem R78065 : Reach 78065 := rs (se 2 (by rfl) ⟨29274, by rfl⟩) R58549
theorem R110915 : Reach 110915 := rs (se 1 (by rfl) ⟨83186, by rfl⟩) R166373
theorem R143693 : Reach 143693 := rs (se 3 (by rfl) ⟨26942, by rfl⟩) R53885
theorem R45427 : Reach 45427 := rs (se 1 (by rfl) ⟨34070, by rfl⟩) R68141
theorem R45571 : Reach 45571 := rs (se 1 (by rfl) ⟨34178, by rfl⟩) R68357
theorem R242189 : Reach 242189 := rs (se 3 (by rfl) ⟨45410, by rfl⟩) R90821
theorem R45715 : Reach 45715 := rs (se 1 (by rfl) ⟨34286, by rfl⟩) R68573
theorem R144035 : Reach 144035 := rs (se 1 (by rfl) ⟨108026, by rfl⟩) R216053
theorem R45731 : Reach 45731 := rs (se 1 (by rfl) ⟨34298, by rfl⟩) R68597
theorem R45859 : Reach 45859 := rs (se 1 (by rfl) ⟨34394, by rfl⟩) R68789
theorem R78641 : Reach 78641 := rs (se 2 (by rfl) ⟨29490, by rfl⟩) R58981
theorem R111469 : Reach 111469 := rs (se 3 (by rfl) ⟨20900, by rfl⟩) R41801
theorem R46003 : Reach 46003 := rs (se 1 (by rfl) ⟨34502, by rfl⟩) R69005
theorem R46147 : Reach 46147 := rs (se 1 (by rfl) ⟨34610, by rfl⟩) R69221
theorem R144497 : Reach 144497 := rs (se 2 (by rfl) ⟨54186, by rfl⟩) R108373
theorem R46291 : Reach 46291 := rs (se 1 (by rfl) ⟨34718, by rfl⟩) R69437
theorem R144611 : Reach 144611 := rs (se 1 (by rfl) ⟨108458, by rfl⟩) R216917
theorem R144625 : Reach 144625 := rs (se 2 (by rfl) ⟨54234, by rfl⟩) R108469
theorem R46435 : Reach 46435 := rs (se 1 (by rfl) ⟨34826, by rfl⟩) R69653
theorem R210275 : Reach 210275 := rs (se 1 (by rfl) ⟨157706, by rfl⟩) R315413
theorem R243121 : Reach 243121 := rs (se 2 (by rfl) ⟨91170, by rfl⟩) R182341
theorem R144881 : Reach 144881 := rs (se 2 (by rfl) ⟨54330, by rfl⟩) R108661
theorem R46579 : Reach 46579 := rs (se 1 (by rfl) ⟨34934, by rfl⟩) R69869
theorem R210437 : Reach 210437 := rs (se 4 (by rfl) ⟨19728, by rfl⟩) R39457
theorem R374341 : Reach 374341 := rs (se 4 (by rfl) ⟨35094, by rfl⟩) R70189
theorem R46723 : Reach 46723 := rs (se 1 (by rfl) ⟨35042, by rfl⟩) R70085
theorem R79537 : Reach 79537 := rs (se 2 (by rfl) ⟨29826, by rfl⟩) R59653
theorem R46867 : Reach 46867 := rs (se 1 (by rfl) ⟨35150, by rfl⟩) R70301
theorem R79697 : Reach 79697 := rs (se 2 (by rfl) ⟨29886, by rfl⟩) R59773
theorem R112529 : Reach 112529 := rs (se 2 (by rfl) ⟨42198, by rfl⟩) R84397
theorem R47011 : Reach 47011 := rs (se 1 (by rfl) ⟨35258, by rfl⟩) R70517
theorem R112589 : Reach 112589 := rs (se 3 (by rfl) ⟨21110, by rfl⟩) R42221
theorem R145421 : Reach 145421 := rs (se 3 (by rfl) ⟨27266, by rfl⟩) R54533
theorem R47155 : Reach 47155 := rs (se 1 (by rfl) ⟨35366, by rfl⟩) R70733
theorem R211085 : Reach 211085 := rs (se 3 (by rfl) ⟨39578, by rfl⟩) R79157
theorem R47299 : Reach 47299 := rs (se 1 (by rfl) ⟨35474, by rfl⟩) R70949
theorem R80099 : Reach 80099 := rs (se 1 (by rfl) ⟨60074, by rfl⟩) R120149
theorem R47443 : Reach 47443 := rs (se 1 (by rfl) ⟨35582, by rfl⟩) R71165
theorem R47587 : Reach 47587 := rs (se 1 (by rfl) ⟨35690, by rfl⟩) R71381
theorem R113201 : Reach 113201 := rs (se 2 (by rfl) ⟨42450, by rfl⟩) R84901
theorem R178787 : Reach 178787 := rs (se 1 (by rfl) ⟨134090, by rfl⟩) R268181
theorem R47731 : Reach 47731 := rs (se 1 (by rfl) ⟨35798, by rfl⟩) R71597
theorem R47747 : Reach 47747 := rs (se 1 (by rfl) ⟨35810, by rfl⟩) R71621
theorem R47795 : Reach 47795 := rs (se 1 (by rfl) ⟨35846, by rfl⟩) R71693
theorem R211661 : Reach 211661 := rs (se 3 (by rfl) ⟨39686, by rfl⟩) R79373
theorem R47875 : Reach 47875 := rs (se 1 (by rfl) ⟨35906, by rfl⟩) R71813
theorem R211747 : Reach 211747 := rs (se 1 (by rfl) ⟨158810, by rfl⟩) R317621
theorem R113485 : Reach 113485 := rs (se 3 (by rfl) ⟨21278, by rfl⟩) R42557
theorem R244579 : Reach 244579 := rs (se 1 (by rfl) ⟨183434, by rfl⟩) R366869
theorem R48019 : Reach 48019 := rs (se 1 (by rfl) ⟨36014, by rfl⟩) R72029
theorem R48163 : Reach 48163 := rs (se 1 (by rfl) ⟨36122, by rfl⟩) R72245
theorem R80995 : Reach 80995 := rs (se 1 (by rfl) ⟨60746, by rfl⟩) R121493
theorem R965773 : Reach 965773 := rs (se 3 (by rfl) ⟨181082, by rfl⟩) R362165
theorem R277667 : Reach 277667 := rs (se 1 (by rfl) ⟨208250, by rfl⟩) R416501
theorem R48307 : Reach 48307 := rs (se 1 (by rfl) ⟨36230, by rfl⟩) R72461
theorem R81155 : Reach 81155 := rs (se 1 (by rfl) ⟨60866, by rfl⟩) R121733
theorem R113987 : Reach 113987 := rs (se 1 (by rfl) ⟨85490, by rfl⟩) R170981
theorem R48451 : Reach 48451 := rs (se 1 (by rfl) ⟨36338, by rfl⟩) R72677
theorem R245105 : Reach 245105 := rs (se 2 (by rfl) ⟨91914, by rfl⟩) R183829
theorem R507377 : Reach 507377 := rs (se 2 (by rfl) ⟨190266, by rfl⟩) R380533
theorem R48643 : Reach 48643 := rs (se 1 (by rfl) ⟨36482, by rfl⟩) R72965
theorem R114317 : Reach 114317 := rs (se 3 (by rfl) ⟨21434, by rfl⟩) R42869
theorem R114385 : Reach 114385 := rs (se 2 (by rfl) ⟨42894, by rfl⟩) R85789
theorem R442253 : Reach 442253 := rs (se 3 (by rfl) ⟨82922, by rfl⟩) R165845
theorem R2015117 : Reach 2015117 := rs (se 3 (by rfl) ⟨377834, by rfl⟩) R755669
theorem R114659 : Reach 114659 := rs (se 1 (by rfl) ⟨85994, by rfl⟩) R171989
theorem R147811 : Reach 147811 := rs (se 1 (by rfl) ⟨110858, by rfl⟩) R221717
theorem R115121 : Reach 115121 := rs (se 2 (by rfl) ⟨43170, by rfl⟩) R86341
theorem R279139 : Reach 279139 := rs (se 1 (by rfl) ⟨209354, by rfl⟩) R418709
theorem R49891 : Reach 49891 := rs (se 1 (by rfl) ⟨37418, by rfl⟩) R74837
theorem R115501 : Reach 115501 := rs (se 3 (by rfl) ⟨21656, by rfl⟩) R43313
theorem R49987 : Reach 49987 := rs (se 1 (by rfl) ⟨37490, by rfl⟩) R74981
theorem R115661 : Reach 115661 := rs (se 3 (by rfl) ⟨21686, by rfl⟩) R43373
theorem R214001 : Reach 214001 := rs (se 2 (by rfl) ⟨80250, by rfl⟩) R160501
theorem R115843 : Reach 115843 := rs (se 1 (by rfl) ⟨86882, by rfl⟩) R173765
theorem R83089 : Reach 83089 := rs (se 2 (by rfl) ⟨31158, by rfl⟩) R62317
theorem R50323 : Reach 50323 := rs (se 1 (by rfl) ⟨37742, by rfl⟩) R75485
theorem R181453 : Reach 181453 := rs (se 3 (by rfl) ⟨34022, by rfl⟩) R68045
theorem R50419 : Reach 50419 := rs (se 1 (by rfl) ⟨37814, by rfl⟩) R75629
theorem R50483 : Reach 50483 := rs (se 1 (by rfl) ⟨37862, by rfl⟩) R75725
theorem R50563 : Reach 50563 := rs (se 1 (by rfl) ⟨37922, by rfl⟩) R75845
theorem R181645 : Reach 181645 := rs (se 3 (by rfl) ⟨34058, by rfl⟩) R68117
theorem R476725 : Reach 476725 := rs (se 5 (by rfl) ⟨22346, by rfl⟩) R44693
theorem R149411 : Reach 149411 := rs (se 1 (by rfl) ⟨112058, by rfl⟩) R224117
theorem R51187 : Reach 51187 := rs (se 1 (by rfl) ⟨38390, by rfl⟩) R76781
theorem R215117 : Reach 215117 := rs (se 3 (by rfl) ⟨40334, by rfl⟩) R80669
theorem R51283 : Reach 51283 := rs (se 1 (by rfl) ⟨38462, by rfl⟩) R76925
theorem R182513 : Reach 182513 := rs (se 2 (by rfl) ⟨68442, by rfl⟩) R136885
theorem R149795 : Reach 149795 := rs (se 1 (by rfl) ⟨112346, by rfl⟩) R224693
theorem R149809 : Reach 149809 := rs (se 2 (by rfl) ⟨56178, by rfl⟩) R112357
theorem R248141 : Reach 248141 := rs (se 3 (by rfl) ⟨46526, by rfl⟩) R93053
theorem R215459 : Reach 215459 := rs (se 1 (by rfl) ⟨161594, by rfl⟩) R323189
theorem R117233 : Reach 117233 := rs (se 2 (by rfl) ⟨43962, by rfl⟩) R87925
theorem R51779 : Reach 51779 := rs (se 1 (by rfl) ⟨38834, by rfl⟩) R77669
theorem R84547 : Reach 84547 := rs (se 1 (by rfl) ⟨63410, by rfl⟩) R126821
theorem R215621 : Reach 215621 := rs (se 4 (by rfl) ⟨20214, by rfl⟩) R40429
theorem R313955 : Reach 313955 := rs (se 1 (by rfl) ⟨235466, by rfl⟩) R470933
theorem R182897 : Reach 182897 := rs (se 2 (by rfl) ⟨68586, by rfl⟩) R137173
theorem R215693 : Reach 215693 := rs (se 3 (by rfl) ⟨40442, by rfl⟩) R80885
theorem R215729 : Reach 215729 := rs (se 2 (by rfl) ⟨80898, by rfl⟩) R161797
theorem R84739 : Reach 84739 := rs (se 1 (by rfl) ⟨63554, by rfl⟩) R127109
theorem R52321 : Reach 52321 := rs (se 2 (by rfl) ⟨19620, by rfl⟩) R39241
theorem R52417 : Reach 52417 := rs (se 2 (by rfl) ⟨19656, by rfl⟩) R39313
theorem R216269 : Reach 216269 := rs (se 3 (by rfl) ⟨40550, by rfl⟩) R81101
theorem R52483 : Reach 52483 := rs (se 1 (by rfl) ⟨39362, by rfl⟩) R78725
theorem R52579 : Reach 52579 := rs (se 1 (by rfl) ⟨39434, by rfl⟩) R78869
theorem R118189 : Reach 118189 := rs (se 3 (by rfl) ⟨22160, by rfl⟩) R44321
theorem R249293 : Reach 249293 := rs (se 3 (by rfl) ⟨46742, by rfl⟩) R93485
theorem R151025 : Reach 151025 := rs (se 2 (by rfl) ⟨56634, by rfl⟩) R113269
theorem R118417 : Reach 118417 := rs (se 2 (by rfl) ⟨44406, by rfl⟩) R88813
theorem R52913 : Reach 52913 := rs (se 2 (by rfl) ⟨19842, by rfl⟩) R39685
theorem R151267 : Reach 151267 := rs (se 1 (by rfl) ⟨113450, by rfl⟩) R226901
theorem R118577 : Reach 118577 := rs (se 2 (by rfl) ⟨44466, by rfl⟩) R88933
theorem R53075 : Reach 53075 := rs (se 1 (by rfl) ⟨39806, by rfl⟩) R79613
theorem R118691 : Reach 118691 := rs (se 1 (by rfl) ⟨89018, by rfl⟩) R178037
theorem R249797 : Reach 249797 := rs (se 4 (by rfl) ⟨23418, by rfl⟩) R46837
theorem R315505 : Reach 315505 := rs (se 2 (by rfl) ⟨118314, by rfl⟩) R236629
theorem R53617 : Reach 53617 := rs (se 2 (by rfl) ⟨20106, by rfl⟩) R40213
theorem R53713 : Reach 53713 := rs (se 2 (by rfl) ⟨20142, by rfl⟩) R40285
theorem R53779 : Reach 53779 := rs (se 1 (by rfl) ⟨40334, by rfl⟩) R80669
theorem R86609 : Reach 86609 := rs (se 2 (by rfl) ⟨32478, by rfl⟩) R64957
theorem R348785 : Reach 348785 := rs (se 2 (by rfl) ⟨130794, by rfl⟩) R261589
theorem R53875 : Reach 53875 := rs (se 1 (by rfl) ⟨40406, by rfl⟩) R80813
theorem R119693 : Reach 119693 := rs (se 3 (by rfl) ⟨22442, by rfl⟩) R44885
theorem R54209 : Reach 54209 := rs (se 2 (by rfl) ⟨20328, by rfl⟩) R40657
theorem R119875 : Reach 119875 := rs (se 1 (by rfl) ⟨89906, by rfl⟩) R179813
theorem R54371 : Reach 54371 := rs (se 1 (by rfl) ⟨40778, by rfl⟩) R81557
theorem R120035 : Reach 120035 := rs (se 1 (by rfl) ⟨90026, by rfl⟩) R180053
theorem R87473 : Reach 87473 := rs (se 2 (by rfl) ⟨32802, by rfl⟩) R65605
theorem R54883 : Reach 54883 := rs (se 1 (by rfl) ⟨41162, by rfl⟩) R82325
theorem R218821 : Reach 218821 := rs (se 4 (by rfl) ⟨20514, by rfl⟩) R41029
theorem R55009 : Reach 55009 := rs (se 2 (by rfl) ⟨20628, by rfl⟩) R41257
theorem R120593 : Reach 120593 := rs (se 2 (by rfl) ⟨45222, by rfl⟩) R90445
theorem R153485 : Reach 153485 := rs (se 3 (by rfl) ⟨28778, by rfl⟩) R57557
theorem R1136693 : Reach 1136693 := rs (se 5 (by rfl) ⟨53282, by rfl⟩) R106565
theorem R88145 : Reach 88145 := rs (se 2 (by rfl) ⟨33054, by rfl⟩) R66109
theorem R88163 : Reach 88163 := rs (se 1 (by rfl) ⟨66122, by rfl⟩) R132245
theorem R186545 : Reach 186545 := rs (se 2 (by rfl) ⟨69954, by rfl⟩) R139909
theorem R547013 : Reach 547013 := rs (se 4 (by rfl) ⟨51282, by rfl⟩) R102565
theorem R121105 : Reach 121105 := rs (se 2 (by rfl) ⟨45414, by rfl⟩) R90829
theorem R88433 : Reach 88433 := rs (se 2 (by rfl) ⟨33162, by rfl⟩) R66325
theorem R88451 : Reach 88451 := rs (se 1 (by rfl) ⟨66338, by rfl⟩) R132677
theorem R88721 : Reach 88721 := rs (se 2 (by rfl) ⟨33270, by rfl⟩) R66541
theorem R88739 : Reach 88739 := rs (se 1 (by rfl) ⟨66554, by rfl⟩) R133109
theorem R187057 : Reach 187057 := rs (se 2 (by rfl) ⟨70146, by rfl⟩) R140293
theorem R88771 : Reach 88771 := rs (se 1 (by rfl) ⟨66578, by rfl⟩) R133157
theorem R56065 : Reach 56065 := rs (se 2 (by rfl) ⟨21024, by rfl⟩) R42049
theorem R56099 : Reach 56099 := rs (se 1 (by rfl) ⟨42074, by rfl⟩) R84149
theorem R89009 : Reach 89009 := rs (se 2 (by rfl) ⟨33378, by rfl⟩) R66757
theorem R89027 : Reach 89027 := rs (se 1 (by rfl) ⟨66770, by rfl⟩) R133541
theorem R56435 : Reach 56435 := rs (se 1 (by rfl) ⟨42326, by rfl⟩) R84653
theorem R351373 : Reach 351373 := rs (se 3 (by rfl) ⟨65882, by rfl⟩) R131765
theorem R89297 : Reach 89297 := rs (se 2 (by rfl) ⟨33486, by rfl⟩) R66973
theorem R89315 : Reach 89315 := rs (se 1 (by rfl) ⟨66986, by rfl⟩) R133973
theorem R56657 : Reach 56657 := rs (se 2 (by rfl) ⟨21246, by rfl⟩) R42493
theorem R154993 : Reach 154993 := rs (se 2 (by rfl) ⟨58122, by rfl⟩) R116245
theorem R56737 : Reach 56737 := rs (se 2 (by rfl) ⟨21276, by rfl⟩) R42553
theorem R89585 : Reach 89585 := rs (se 2 (by rfl) ⟨33594, by rfl⟩) R67189
theorem R89603 : Reach 89603 := rs (se 1 (by rfl) ⟨67202, by rfl⟩) R134405
theorem R122381 : Reach 122381 := rs (se 3 (by rfl) ⟨22946, by rfl⟩) R45893
theorem R122563 : Reach 122563 := rs (se 1 (by rfl) ⟨91922, by rfl⟩) R183845
theorem R351971 : Reach 351971 := rs (se 1 (by rfl) ⟨263978, by rfl⟩) R527957
theorem R122609 : Reach 122609 := rs (se 2 (by rfl) ⟨45978, by rfl⟩) R91957
theorem R89873 : Reach 89873 := rs (se 2 (by rfl) ⟨33702, by rfl⟩) R67405
theorem R89891 : Reach 89891 := rs (se 1 (by rfl) ⟨67418, by rfl⟩) R134837
theorem R319301 : Reach 319301 := rs (se 4 (by rfl) ⟨29934, by rfl⟩) R59869
theorem R57187 : Reach 57187 := rs (se 1 (by rfl) ⟨42890, by rfl⟩) R85781
theorem R253829 : Reach 253829 := rs (se 4 (by rfl) ⟨23796, by rfl⟩) R47593
theorem R90001 : Reach 90001 := rs (se 2 (by rfl) ⟨33750, by rfl⟩) R67501
theorem R90161 : Reach 90161 := rs (se 2 (by rfl) ⟨33810, by rfl⟩) R67621
theorem R90179 : Reach 90179 := rs (se 1 (by rfl) ⟨67634, by rfl⟩) R135269
theorem R57523 : Reach 57523 := rs (se 1 (by rfl) ⟨43142, by rfl⟩) R86285
theorem R90449 : Reach 90449 := rs (se 2 (by rfl) ⟨33918, by rfl⟩) R67837
theorem R90467 : Reach 90467 := rs (se 1 (by rfl) ⟨67850, by rfl⟩) R135701
theorem R90499 : Reach 90499 := rs (se 1 (by rfl) ⟨67874, by rfl⟩) R135749
theorem R483725 : Reach 483725 := rs (se 3 (by rfl) ⟨90698, by rfl⟩) R181397
theorem R90563 : Reach 90563 := rs (se 1 (by rfl) ⟨67922, by rfl⟩) R135845
theorem R90659 : Reach 90659 := rs (se 1 (by rfl) ⟨67994, by rfl⟩) R135989
theorem R90737 : Reach 90737 := rs (se 2 (by rfl) ⟨34026, by rfl⟩) R68053
theorem R90755 : Reach 90755 := rs (se 1 (by rfl) ⟨68066, by rfl⟩) R136133
theorem R58001 : Reach 58001 := rs (se 2 (by rfl) ⟨21750, by rfl⟩) R43501
theorem R156401 : Reach 156401 := rs (se 2 (by rfl) ⟨58650, by rfl⟩) R117301
theorem R58115 : Reach 58115 := rs (se 1 (by rfl) ⟨43586, by rfl⟩) R87173
theorem R58195 : Reach 58195 := rs (se 1 (by rfl) ⟨43646, by rfl⟩) R87293
theorem R91025 : Reach 91025 := rs (se 2 (by rfl) ⟨34134, by rfl⟩) R68269
theorem R91043 : Reach 91043 := rs (se 1 (by rfl) ⟨68282, by rfl⟩) R136565
theorem R91313 : Reach 91313 := rs (se 2 (by rfl) ⟨34242, by rfl⟩) R68485
theorem R91331 : Reach 91331 := rs (se 1 (by rfl) ⟨68498, by rfl⟩) R136997
theorem R58691 : Reach 58691 := rs (se 1 (by rfl) ⟨44018, by rfl⟩) R88037
theorem R58721 : Reach 58721 := rs (se 2 (by rfl) ⟨22020, by rfl⟩) R44041
theorem R91505 : Reach 91505 := rs (se 2 (by rfl) ⟨34314, by rfl⟩) R68629
theorem R58739 : Reach 58739 := rs (se 1 (by rfl) ⟨44054, by rfl⟩) R88109
theorem R58753 : Reach 58753 := rs (se 2 (by rfl) ⟨22032, by rfl⟩) R44065
theorem R58769 : Reach 58769 := rs (se 2 (by rfl) ⟨22038, by rfl⟩) R44077
theorem R58787 : Reach 58787 := rs (se 1 (by rfl) ⟨44090, by rfl⟩) R88181
theorem R58801 : Reach 58801 := rs (se 2 (by rfl) ⟨22050, by rfl⟩) R44101
theorem R58817 : Reach 58817 := rs (se 2 (by rfl) ⟨22056, by rfl⟩) R44113
theorem R583109 : Reach 583109 := rs (se 4 (by rfl) ⟨54666, by rfl⟩) R109333
theorem R91601 : Reach 91601 := rs (se 2 (by rfl) ⟨34350, by rfl⟩) R68701
theorem R58835 : Reach 58835 := rs (se 1 (by rfl) ⟨44126, by rfl⟩) R88253
theorem R91619 : Reach 91619 := rs (se 1 (by rfl) ⟨68714, by rfl⟩) R137429
theorem R58865 : Reach 58865 := rs (se 2 (by rfl) ⟨22074, by rfl⟩) R44149
theorem R58883 : Reach 58883 := rs (se 1 (by rfl) ⟨44162, by rfl⟩) R88325
theorem R58913 : Reach 58913 := rs (se 2 (by rfl) ⟨22092, by rfl⟩) R44185
theorem R58931 : Reach 58931 := rs (se 1 (by rfl) ⟨44198, by rfl⟩) R88397
theorem R58961 : Reach 58961 := rs (se 2 (by rfl) ⟨22110, by rfl⟩) R44221
theorem R58979 : Reach 58979 := rs (se 1 (by rfl) ⟨44234, by rfl⟩) R88469
theorem R59009 : Reach 59009 := rs (se 2 (by rfl) ⟨22128, by rfl⟩) R44257
theorem R59027 : Reach 59027 := rs (se 1 (by rfl) ⟨44270, by rfl⟩) R88541
theorem R59057 : Reach 59057 := rs (se 2 (by rfl) ⟨22146, by rfl⟩) R44293
theorem R59075 : Reach 59075 := rs (se 1 (by rfl) ⟨44306, by rfl⟩) R88613
theorem R59105 : Reach 59105 := rs (se 2 (by rfl) ⟨22164, by rfl⟩) R44329
theorem R91889 : Reach 91889 := rs (se 2 (by rfl) ⟨34458, by rfl⟩) R68917
theorem R59123 : Reach 59123 := rs (se 1 (by rfl) ⟨44342, by rfl⟩) R88685
theorem R91907 : Reach 91907 := rs (se 1 (by rfl) ⟨68930, by rfl⟩) R137861
theorem R59153 : Reach 59153 := rs (se 2 (by rfl) ⟨22182, by rfl⟩) R44365
theorem R59171 : Reach 59171 := rs (se 1 (by rfl) ⟨44378, by rfl⟩) R88757
theorem R59201 : Reach 59201 := rs (se 2 (by rfl) ⟨22200, by rfl⟩) R44401
theorem R59219 : Reach 59219 := rs (se 1 (by rfl) ⟨44414, by rfl⟩) R88829
theorem R59249 : Reach 59249 := rs (se 2 (by rfl) ⟨22218, by rfl⟩) R44437
theorem R59267 : Reach 59267 := rs (se 1 (by rfl) ⟨44450, by rfl⟩) R88901
theorem R59297 : Reach 59297 := rs (se 2 (by rfl) ⟨22236, by rfl⟩) R44473
theorem R59315 : Reach 59315 := rs (se 1 (by rfl) ⟨44486, by rfl⟩) R88973
theorem R59345 : Reach 59345 := rs (se 2 (by rfl) ⟨22254, by rfl⟩) R44509
theorem R59363 : Reach 59363 := rs (se 1 (by rfl) ⟨44522, by rfl⟩) R89045
theorem R59393 : Reach 59393 := rs (se 2 (by rfl) ⟨22272, by rfl⟩) R44545
theorem R92177 : Reach 92177 := rs (se 2 (by rfl) ⟨34566, by rfl⟩) R69133
theorem R59411 : Reach 59411 := rs (se 1 (by rfl) ⟨44558, by rfl⟩) R89117
theorem R92195 : Reach 92195 := rs (se 1 (by rfl) ⟨69146, by rfl⟩) R138293
theorem R59441 : Reach 59441 := rs (se 2 (by rfl) ⟨22290, by rfl⟩) R44581
theorem R59459 : Reach 59459 := rs (se 1 (by rfl) ⟨44594, by rfl⟩) R89189
theorem R59489 : Reach 59489 := rs (se 2 (by rfl) ⟨22308, by rfl⟩) R44617
theorem R59507 : Reach 59507 := rs (se 1 (by rfl) ⟨44630, by rfl⟩) R89261
theorem R125069 : Reach 125069 := rs (se 3 (by rfl) ⟨23450, by rfl⟩) R46901
theorem R59537 : Reach 59537 := rs (se 2 (by rfl) ⟨22326, by rfl⟩) R44653
theorem R59555 : Reach 59555 := rs (se 1 (by rfl) ⟨44666, by rfl⟩) R89333
theorem R157859 : Reach 157859 := rs (se 1 (by rfl) ⟨118394, by rfl⟩) R236789
theorem R59585 : Reach 59585 := rs (se 2 (by rfl) ⟨22344, by rfl⟩) R44689
theorem R59603 : Reach 59603 := rs (se 1 (by rfl) ⟨44702, by rfl⟩) R89405
theorem R59633 : Reach 59633 := rs (se 2 (by rfl) ⟨22362, by rfl⟩) R44725
theorem R59651 : Reach 59651 := rs (se 1 (by rfl) ⟨44738, by rfl⟩) R89477
theorem R59681 : Reach 59681 := rs (se 2 (by rfl) ⟨22380, by rfl⟩) R44761
theorem R92465 : Reach 92465 := rs (se 2 (by rfl) ⟨34674, by rfl⟩) R69349
theorem R59699 : Reach 59699 := rs (se 1 (by rfl) ⟨44774, by rfl⟩) R89549
theorem R92483 : Reach 92483 := rs (se 1 (by rfl) ⟨69362, by rfl⟩) R138725
theorem R59729 : Reach 59729 := rs (se 2 (by rfl) ⟨22398, by rfl⟩) R44797
theorem R59747 : Reach 59747 := rs (se 1 (by rfl) ⟨44810, by rfl⟩) R89621
theorem R59777 : Reach 59777 := rs (se 2 (by rfl) ⟨22416, by rfl⟩) R44833
theorem R59795 : Reach 59795 := rs (se 1 (by rfl) ⟨44846, by rfl⟩) R89693
theorem R59825 : Reach 59825 := rs (se 2 (by rfl) ⟨22434, by rfl⟩) R44869
theorem R59843 : Reach 59843 := rs (se 1 (by rfl) ⟨44882, by rfl⟩) R89765
theorem R223685 : Reach 223685 := rs (se 4 (by rfl) ⟨20970, by rfl⟩) R41941
theorem R59873 : Reach 59873 := rs (se 2 (by rfl) ⟨22452, by rfl⟩) R44905
theorem R59891 : Reach 59891 := rs (se 1 (by rfl) ⟨44918, by rfl⟩) R89837
theorem R59921 : Reach 59921 := rs (se 2 (by rfl) ⟨22470, by rfl⟩) R44941
theorem R59923 : Reach 59923 := rs (se 1 (by rfl) ⟨44942, by rfl⟩) R89885
theorem R59939 : Reach 59939 := rs (se 1 (by rfl) ⟨44954, by rfl⟩) R89909
theorem R256547 : Reach 256547 := rs (se 1 (by rfl) ⟨192410, by rfl⟩) R384821
theorem R59969 : Reach 59969 := rs (se 2 (by rfl) ⟨22488, by rfl⟩) R44977
theorem R59971 : Reach 59971 := rs (se 1 (by rfl) ⟨44978, by rfl⟩) R89957
theorem R92753 : Reach 92753 := rs (se 2 (by rfl) ⟨34782, by rfl⟩) R69565
theorem R59987 : Reach 59987 := rs (se 1 (by rfl) ⟨44990, by rfl⟩) R89981
theorem R92771 : Reach 92771 := rs (se 1 (by rfl) ⟨69578, by rfl⟩) R139157
theorem R60017 : Reach 60017 := rs (se 2 (by rfl) ⟨22506, by rfl⟩) R45013
theorem R60035 : Reach 60035 := rs (se 1 (by rfl) ⟨45026, by rfl⟩) R90053
theorem R60065 : Reach 60065 := rs (se 2 (by rfl) ⟨22524, by rfl⟩) R45049
theorem R60083 : Reach 60083 := rs (se 1 (by rfl) ⟨45062, by rfl⟩) R90125
theorem R60097 : Reach 60097 := rs (se 2 (by rfl) ⟨22536, by rfl⟩) R45073
theorem R60113 : Reach 60113 := rs (se 2 (by rfl) ⟨22542, by rfl⟩) R45085
theorem R60131 : Reach 60131 := rs (se 1 (by rfl) ⟨45098, by rfl⟩) R90197
theorem R223985 : Reach 223985 := rs (se 2 (by rfl) ⟨83994, by rfl⟩) R167989
theorem R60161 : Reach 60161 := rs (se 2 (by rfl) ⟨22560, by rfl⟩) R45121
theorem R60179 : Reach 60179 := rs (se 1 (by rfl) ⟨45134, by rfl⟩) R90269
theorem R92963 : Reach 92963 := rs (se 1 (by rfl) ⟨69722, by rfl⟩) R139445
theorem R60209 : Reach 60209 := rs (se 2 (by rfl) ⟨22578, by rfl⟩) R45157
theorem R60211 : Reach 60211 := rs (se 1 (by rfl) ⟨45158, by rfl⟩) R90317
theorem R60227 : Reach 60227 := rs (se 1 (by rfl) ⟨45170, by rfl⟩) R90341
theorem R60257 : Reach 60257 := rs (se 2 (by rfl) ⟨22596, by rfl⟩) R45193
theorem R93041 : Reach 93041 := rs (se 2 (by rfl) ⟨34890, by rfl⟩) R69781
theorem R60275 : Reach 60275 := rs (se 1 (by rfl) ⟨45206, by rfl⟩) R90413
theorem R93059 : Reach 93059 := rs (se 1 (by rfl) ⟨69794, by rfl⟩) R139589
theorem R60305 : Reach 60305 := rs (se 2 (by rfl) ⟨22614, by rfl⟩) R45229
theorem R60323 : Reach 60323 := rs (se 1 (by rfl) ⟨45242, by rfl⟩) R90485
theorem R60353 : Reach 60353 := rs (se 2 (by rfl) ⟨22632, by rfl⟩) R45265
theorem R60371 : Reach 60371 := rs (se 1 (by rfl) ⟨45278, by rfl⟩) R90557
theorem R60401 : Reach 60401 := rs (se 2 (by rfl) ⟨22650, by rfl⟩) R45301
theorem R60419 : Reach 60419 := rs (se 1 (by rfl) ⟨45314, by rfl⟩) R90629
theorem R60449 : Reach 60449 := rs (se 2 (by rfl) ⟨22668, by rfl⟩) R45337
theorem R60467 : Reach 60467 := rs (se 1 (by rfl) ⟨45350, by rfl⟩) R90701
theorem R158797 : Reach 158797 := rs (se 3 (by rfl) ⟨29774, by rfl⟩) R59549
theorem R60497 : Reach 60497 := rs (se 2 (by rfl) ⟨22686, by rfl⟩) R45373
theorem R60515 : Reach 60515 := rs (se 1 (by rfl) ⟨45386, by rfl⟩) R90773
theorem R60545 : Reach 60545 := rs (se 2 (by rfl) ⟨22704, by rfl⟩) R45409
theorem R158861 : Reach 158861 := rs (se 3 (by rfl) ⟨29786, by rfl⟩) R59573
theorem R93329 : Reach 93329 := rs (se 2 (by rfl) ⟨34998, by rfl⟩) R69997
theorem R60563 : Reach 60563 := rs (se 1 (by rfl) ⟨45422, by rfl⟩) R90845
theorem R93347 : Reach 93347 := rs (se 1 (by rfl) ⟨70010, by rfl⟩) R140021
theorem R60593 : Reach 60593 := rs (se 2 (by rfl) ⟨22722, by rfl⟩) R45445
theorem R60611 : Reach 60611 := rs (se 1 (by rfl) ⟨45458, by rfl⟩) R90917
theorem R60625 : Reach 60625 := rs (se 2 (by rfl) ⟨22734, by rfl⟩) R45469
theorem R60641 : Reach 60641 := rs (se 2 (by rfl) ⟨22740, by rfl⟩) R45481
theorem R60659 : Reach 60659 := rs (se 1 (by rfl) ⟨45494, by rfl⟩) R90989
theorem R60689 : Reach 60689 := rs (se 2 (by rfl) ⟨22758, by rfl⟩) R45517
theorem R60707 : Reach 60707 := rs (se 1 (by rfl) ⟨45530, by rfl⟩) R91061
theorem R60737 : Reach 60737 := rs (se 2 (by rfl) ⟨22776, by rfl⟩) R45553
theorem R60755 : Reach 60755 := rs (se 1 (by rfl) ⟨45566, by rfl⟩) R91133
theorem R60785 : Reach 60785 := rs (se 2 (by rfl) ⟨22794, by rfl⟩) R45589
theorem R60803 : Reach 60803 := rs (se 1 (by rfl) ⟨45602, by rfl⟩) R91205
theorem R60833 : Reach 60833 := rs (se 2 (by rfl) ⟨22812, by rfl⟩) R45625
theorem R93617 : Reach 93617 := rs (se 2 (by rfl) ⟨35106, by rfl⟩) R70213
theorem R60851 : Reach 60851 := rs (se 1 (by rfl) ⟨45638, by rfl⟩) R91277
theorem R93635 : Reach 93635 := rs (se 1 (by rfl) ⟨70226, by rfl⟩) R140453
theorem R60881 : Reach 60881 := rs (se 2 (by rfl) ⟨22830, by rfl⟩) R45661
theorem R60899 : Reach 60899 := rs (se 1 (by rfl) ⟨45674, by rfl⟩) R91349
theorem R60929 : Reach 60929 := rs (se 2 (by rfl) ⟨22848, by rfl⟩) R45697
theorem R60947 : Reach 60947 := rs (se 1 (by rfl) ⟨45710, by rfl⟩) R91421
theorem R60977 : Reach 60977 := rs (se 2 (by rfl) ⟨22866, by rfl⟩) R45733
theorem R60995 : Reach 60995 := rs (se 1 (by rfl) ⟨45746, by rfl⟩) R91493
theorem R61025 : Reach 61025 := rs (se 2 (by rfl) ⟨22884, by rfl⟩) R45769
theorem R61043 : Reach 61043 := rs (se 1 (by rfl) ⟨45782, by rfl⟩) R91565
theorem R61073 : Reach 61073 := rs (se 2 (by rfl) ⟨22902, by rfl⟩) R45805
theorem R61091 : Reach 61091 := rs (se 1 (by rfl) ⟨45818, by rfl⟩) R91637
theorem R61121 : Reach 61121 := rs (se 2 (by rfl) ⟨22920, by rfl⟩) R45841
theorem R126659 : Reach 126659 := rs (se 1 (by rfl) ⟨94994, by rfl⟩) R189989
theorem R93905 : Reach 93905 := rs (se 2 (by rfl) ⟨35214, by rfl⟩) R70429
theorem R61139 : Reach 61139 := rs (se 1 (by rfl) ⟨45854, by rfl⟩) R91709
theorem R93923 : Reach 93923 := rs (se 1 (by rfl) ⟨70442, by rfl⟩) R140885
theorem R61169 : Reach 61169 := rs (se 2 (by rfl) ⟨22938, by rfl⟩) R45877
theorem R61187 : Reach 61187 := rs (se 1 (by rfl) ⟨45890, by rfl⟩) R91781
theorem R61217 : Reach 61217 := rs (se 2 (by rfl) ⟨22956, by rfl⟩) R45913
theorem R61235 : Reach 61235 := rs (se 1 (by rfl) ⟨45926, by rfl⟩) R91853
theorem R61265 : Reach 61265 := rs (se 2 (by rfl) ⟨22974, by rfl⟩) R45949
theorem R61283 : Reach 61283 := rs (se 1 (by rfl) ⟨45962, by rfl⟩) R91925
theorem R61313 : Reach 61313 := rs (se 2 (by rfl) ⟨22992, by rfl⟩) R45985
theorem R61331 : Reach 61331 := rs (se 1 (by rfl) ⟨45998, by rfl⟩) R91997
theorem R126893 : Reach 126893 := rs (se 3 (by rfl) ⟨23792, by rfl⟩) R47585
theorem R61361 : Reach 61361 := rs (se 2 (by rfl) ⟨23010, by rfl⟩) R46021
theorem R61379 : Reach 61379 := rs (se 1 (by rfl) ⟨46034, by rfl⟩) R92069
theorem R61409 : Reach 61409 := rs (se 2 (by rfl) ⟨23028, by rfl⟩) R46057
theorem R94193 : Reach 94193 := rs (se 2 (by rfl) ⟨35322, by rfl⟩) R70645
theorem R61427 : Reach 61427 := rs (se 1 (by rfl) ⟨46070, by rfl⟩) R92141
theorem R94211 : Reach 94211 := rs (se 1 (by rfl) ⟨70658, by rfl⟩) R141317
theorem R61457 : Reach 61457 := rs (se 2 (by rfl) ⟨23046, by rfl⟩) R46093
theorem R61475 : Reach 61475 := rs (se 1 (by rfl) ⟨46106, by rfl⟩) R92213
theorem R61505 : Reach 61505 := rs (se 2 (by rfl) ⟨23064, by rfl⟩) R46129
theorem R61523 : Reach 61523 := rs (se 1 (by rfl) ⟨46142, by rfl⟩) R92285
theorem R61553 : Reach 61553 := rs (se 2 (by rfl) ⟨23082, by rfl⟩) R46165
theorem R61571 : Reach 61571 := rs (se 1 (by rfl) ⟨46178, by rfl⟩) R92357
theorem R61601 : Reach 61601 := rs (se 2 (by rfl) ⟨23100, by rfl⟩) R46201
theorem R225443 : Reach 225443 := rs (se 1 (by rfl) ⟨169082, by rfl⟩) R338165
theorem R61619 : Reach 61619 := rs (se 1 (by rfl) ⟨46214, by rfl⟩) R92429
theorem R61649 : Reach 61649 := rs (se 2 (by rfl) ⟨23118, by rfl⟩) R46237
theorem R61667 : Reach 61667 := rs (se 1 (by rfl) ⟨46250, by rfl⟩) R92501
theorem R61697 : Reach 61697 := rs (se 2 (by rfl) ⟨23136, by rfl⟩) R46273
theorem R94481 : Reach 94481 := rs (se 2 (by rfl) ⟨35430, by rfl⟩) R70861
theorem R61715 : Reach 61715 := rs (se 1 (by rfl) ⟨46286, by rfl⟩) R92573
theorem R94499 : Reach 94499 := rs (se 1 (by rfl) ⟨70874, by rfl⟩) R141749
theorem R61745 : Reach 61745 := rs (se 2 (by rfl) ⟨23154, by rfl⟩) R46309
theorem R61763 : Reach 61763 := rs (se 1 (by rfl) ⟨46322, by rfl⟩) R92645
theorem R61793 : Reach 61793 := rs (se 2 (by rfl) ⟨23172, by rfl⟩) R46345
theorem R61811 : Reach 61811 := rs (se 1 (by rfl) ⟨46358, by rfl⟩) R92717
theorem R61841 : Reach 61841 := rs (se 2 (by rfl) ⟨23190, by rfl⟩) R46381
theorem R61859 : Reach 61859 := rs (se 1 (by rfl) ⟨46394, by rfl⟩) R92789
theorem R61889 : Reach 61889 := rs (se 2 (by rfl) ⟨23208, by rfl⟩) R46417
theorem R61907 : Reach 61907 := rs (se 1 (by rfl) ⟨46430, by rfl⟩) R92861
theorem R258545 : Reach 258545 := rs (se 2 (by rfl) ⟨96954, by rfl⟩) R193909
theorem R61937 : Reach 61937 := rs (se 2 (by rfl) ⟨23226, by rfl⟩) R46453
theorem R61955 : Reach 61955 := rs (se 1 (by rfl) ⟨46466, by rfl⟩) R92933
theorem R61985 : Reach 61985 := rs (se 2 (by rfl) ⟨23244, by rfl⟩) R46489
theorem R94769 : Reach 94769 := rs (se 2 (by rfl) ⟨35538, by rfl⟩) R71077
theorem R62003 : Reach 62003 := rs (se 1 (by rfl) ⟨46502, by rfl⟩) R93005
theorem R94787 : Reach 94787 := rs (se 1 (by rfl) ⟨71090, by rfl⟩) R142181
theorem R127555 : Reach 127555 := rs (se 1 (by rfl) ⟨95666, by rfl⟩) R191333
theorem R62033 : Reach 62033 := rs (se 2 (by rfl) ⟨23262, by rfl⟩) R46525
theorem R62051 : Reach 62051 := rs (se 1 (by rfl) ⟨46538, by rfl⟩) R93077
theorem R488035 : Reach 488035 := rs (se 1 (by rfl) ⟨366026, by rfl⟩) R732053
theorem R62081 : Reach 62081 := rs (se 2 (by rfl) ⟨23280, by rfl⟩) R46561
theorem R62099 : Reach 62099 := rs (se 1 (by rfl) ⟨46574, by rfl⟩) R93149
theorem R62129 : Reach 62129 := rs (se 2 (by rfl) ⟨23298, by rfl⟩) R46597
theorem R62147 : Reach 62147 := rs (se 1 (by rfl) ⟨46610, by rfl⟩) R93221
theorem R62177 : Reach 62177 := rs (se 2 (by rfl) ⟨23316, by rfl⟩) R46633
theorem R160483 : Reach 160483 := rs (se 1 (by rfl) ⟨120362, by rfl⟩) R240725
theorem R62195 : Reach 62195 := rs (se 1 (by rfl) ⟨46646, by rfl⟩) R93293
theorem R62225 : Reach 62225 := rs (se 2 (by rfl) ⟨23334, by rfl⟩) R46669
theorem R62243 : Reach 62243 := rs (se 1 (by rfl) ⟨46682, by rfl⟩) R93365
theorem R62273 : Reach 62273 := rs (se 2 (by rfl) ⟨23352, by rfl⟩) R46705
theorem R95057 : Reach 95057 := rs (se 2 (by rfl) ⟨35646, by rfl⟩) R71293
theorem R62291 : Reach 62291 := rs (se 1 (by rfl) ⟨46718, by rfl⟩) R93437
theorem R95075 : Reach 95075 := rs (se 1 (by rfl) ⟨71306, by rfl⟩) R142613
theorem R62321 : Reach 62321 := rs (se 2 (by rfl) ⟨23370, by rfl⟩) R46741
theorem R62339 : Reach 62339 := rs (se 1 (by rfl) ⟨46754, by rfl⟩) R93509
theorem R127889 : Reach 127889 := rs (se 2 (by rfl) ⟨47958, by rfl⟩) R95917
theorem R62369 : Reach 62369 := rs (se 2 (by rfl) ⟨23388, by rfl⟩) R46777
theorem R127921 : Reach 127921 := rs (se 2 (by rfl) ⟨47970, by rfl⟩) R95941
theorem R62387 : Reach 62387 := rs (se 1 (by rfl) ⟨46790, by rfl⟩) R93581
theorem R62417 : Reach 62417 := rs (se 2 (by rfl) ⟨23406, by rfl⟩) R46813
theorem R62435 : Reach 62435 := rs (se 1 (by rfl) ⟨46826, by rfl⟩) R93653
theorem R62465 : Reach 62465 := rs (se 2 (by rfl) ⟨23424, by rfl⟩) R46849
theorem R62483 : Reach 62483 := rs (se 1 (by rfl) ⟨46862, by rfl⟩) R93725
theorem R62513 : Reach 62513 := rs (se 2 (by rfl) ⟨23442, by rfl⟩) R46885
theorem R62531 : Reach 62531 := rs (se 1 (by rfl) ⟨46898, by rfl⟩) R93797
theorem R422981 : Reach 422981 := rs (se 4 (by rfl) ⟨39654, by rfl⟩) R79309
theorem R62561 : Reach 62561 := rs (se 2 (by rfl) ⟨23460, by rfl⟩) R46921
theorem R95345 : Reach 95345 := rs (se 2 (by rfl) ⟨35754, by rfl⟩) R71509
theorem R62579 : Reach 62579 := rs (se 1 (by rfl) ⟨46934, by rfl⟩) R93869
theorem R95363 : Reach 95363 := rs (se 1 (by rfl) ⟨71522, by rfl⟩) R143045
theorem R62609 : Reach 62609 := rs (se 2 (by rfl) ⟨23478, by rfl⟩) R46957
theorem R62627 : Reach 62627 := rs (se 1 (by rfl) ⟨46970, by rfl⟩) R93941
theorem R62657 : Reach 62657 := rs (se 2 (by rfl) ⟨23496, by rfl⟩) R46993
theorem R160973 : Reach 160973 := rs (se 3 (by rfl) ⟨30182, by rfl⟩) R60365
theorem R62675 : Reach 62675 := rs (se 1 (by rfl) ⟨47006, by rfl⟩) R94013
theorem R62689 : Reach 62689 := rs (se 2 (by rfl) ⟨23508, by rfl⟩) R47017
theorem R62705 : Reach 62705 := rs (se 2 (by rfl) ⟨23514, by rfl⟩) R47029
theorem R62723 : Reach 62723 := rs (se 1 (by rfl) ⟨47042, by rfl⟩) R94085
theorem R62753 : Reach 62753 := rs (se 2 (by rfl) ⟨23532, by rfl⟩) R47065
theorem R62771 : Reach 62771 := rs (se 1 (by rfl) ⟨47078, by rfl⟩) R94157
theorem R62785 : Reach 62785 := rs (se 2 (by rfl) ⟨23544, by rfl⟩) R47089
theorem R62801 : Reach 62801 := rs (se 2 (by rfl) ⟨23550, by rfl⟩) R47101
theorem R62819 : Reach 62819 := rs (se 1 (by rfl) ⟨47114, by rfl⟩) R94229
theorem R521585 : Reach 521585 := rs (se 2 (by rfl) ⟨195594, by rfl⟩) R391189
theorem R62849 : Reach 62849 := rs (se 2 (by rfl) ⟨23568, by rfl⟩) R47137
theorem R259469 : Reach 259469 := rs (se 3 (by rfl) ⟨48650, by rfl⟩) R97301
theorem R95633 : Reach 95633 := rs (se 2 (by rfl) ⟨35862, by rfl⟩) R71725
theorem R62867 : Reach 62867 := rs (se 1 (by rfl) ⟨47150, by rfl⟩) R94301
theorem R95651 : Reach 95651 := rs (se 1 (by rfl) ⟨71738, by rfl⟩) R143477
theorem R62897 : Reach 62897 := rs (se 2 (by rfl) ⟨23586, by rfl⟩) R47173
theorem R62915 : Reach 62915 := rs (se 1 (by rfl) ⟨47186, by rfl⟩) R94373
theorem R62945 : Reach 62945 := rs (se 2 (by rfl) ⟨23604, by rfl⟩) R47209
theorem R128483 : Reach 128483 := rs (se 1 (by rfl) ⟨96362, by rfl⟩) R192725
theorem R62963 : Reach 62963 := rs (se 1 (by rfl) ⟨47222, by rfl⟩) R94445
theorem R325133 : Reach 325133 := rs (se 3 (by rfl) ⟨60962, by rfl⟩) R121925
theorem R62993 : Reach 62993 := rs (se 2 (by rfl) ⟨23622, by rfl⟩) R47245
theorem R63011 : Reach 63011 := rs (se 1 (by rfl) ⟨47258, by rfl⟩) R94517
theorem R63041 : Reach 63041 := rs (se 2 (by rfl) ⟨23640, by rfl⟩) R47281
theorem R63059 : Reach 63059 := rs (se 1 (by rfl) ⟨47294, by rfl⟩) R94589
theorem R63089 : Reach 63089 := rs (se 2 (by rfl) ⟨23658, by rfl⟩) R47317
theorem R63107 : Reach 63107 := rs (se 1 (by rfl) ⟨47330, by rfl⟩) R94661
theorem R63137 : Reach 63137 := rs (se 2 (by rfl) ⟨23676, by rfl⟩) R47353
theorem R95921 : Reach 95921 := rs (se 2 (by rfl) ⟨35970, by rfl⟩) R71941
theorem R63155 : Reach 63155 := rs (se 1 (by rfl) ⟨47366, by rfl⟩) R94733
theorem R95939 : Reach 95939 := rs (se 1 (by rfl) ⟨71954, by rfl⟩) R143909
theorem R63185 : Reach 63185 := rs (se 2 (by rfl) ⟨23694, by rfl⟩) R47389
theorem R63203 : Reach 63203 := rs (se 1 (by rfl) ⟨47402, by rfl⟩) R94805
theorem R128749 : Reach 128749 := rs (se 3 (by rfl) ⟨24140, by rfl⟩) R48281
theorem R63233 : Reach 63233 := rs (se 2 (by rfl) ⟨23712, by rfl⟩) R47425
theorem R63251 : Reach 63251 := rs (se 1 (by rfl) ⟨47438, by rfl⟩) R94877
theorem R63281 : Reach 63281 := rs (se 2 (by rfl) ⟨23730, by rfl⟩) R47461
theorem R63299 : Reach 63299 := rs (se 1 (by rfl) ⟨47474, by rfl⟩) R94949
theorem R63329 : Reach 63329 := rs (se 2 (by rfl) ⟨23748, by rfl⟩) R47497
theorem R63347 : Reach 63347 := rs (se 1 (by rfl) ⟨47510, by rfl⟩) R95021
theorem R63377 : Reach 63377 := rs (se 2 (by rfl) ⟨23766, by rfl⟩) R47533
theorem R63395 : Reach 63395 := rs (se 1 (by rfl) ⟨47546, by rfl⟩) R95093
theorem R63425 : Reach 63425 := rs (se 2 (by rfl) ⟨23784, by rfl⟩) R47569
theorem R96209 : Reach 96209 := rs (se 2 (by rfl) ⟨36078, by rfl⟩) R72157
theorem R63443 : Reach 63443 := rs (se 1 (by rfl) ⟨47582, by rfl⟩) R95165
theorem R96227 : Reach 96227 := rs (se 1 (by rfl) ⟨72170, by rfl⟩) R144341
theorem R63473 : Reach 63473 := rs (se 2 (by rfl) ⟨23802, by rfl⟩) R47605
theorem R161777 : Reach 161777 := rs (se 2 (by rfl) ⟨60666, by rfl⟩) R121333
theorem R63491 : Reach 63491 := rs (se 1 (by rfl) ⟨47618, by rfl⟩) R95237
theorem R63521 : Reach 63521 := rs (se 2 (by rfl) ⟨23820, by rfl⟩) R47641
theorem R63539 : Reach 63539 := rs (se 1 (by rfl) ⟨47654, by rfl⟩) R95309
theorem R63569 : Reach 63569 := rs (se 2 (by rfl) ⟨23838, by rfl⟩) R47677
theorem R63587 : Reach 63587 := rs (se 1 (by rfl) ⟨47690, by rfl⟩) R95381
theorem R63617 : Reach 63617 := rs (se 2 (by rfl) ⟨23856, by rfl⟩) R47713
theorem R63635 : Reach 63635 := rs (se 1 (by rfl) ⟨47726, by rfl⟩) R95453
theorem R63665 : Reach 63665 := rs (se 2 (by rfl) ⟨23874, by rfl⟩) R47749
theorem R63683 : Reach 63683 := rs (se 1 (by rfl) ⟨47762, by rfl⟩) R95525
theorem R63713 : Reach 63713 := rs (se 2 (by rfl) ⟨23892, by rfl⟩) R47785
theorem R96497 : Reach 96497 := rs (se 2 (by rfl) ⟨36186, by rfl⟩) R72373
theorem R63731 : Reach 63731 := rs (se 1 (by rfl) ⟨47798, by rfl⟩) R95597
theorem R96515 : Reach 96515 := rs (se 1 (by rfl) ⟨72386, by rfl⟩) R144773
theorem R63761 : Reach 63761 := rs (se 2 (by rfl) ⟨23910, by rfl⟩) R47821
theorem R63779 : Reach 63779 := rs (se 1 (by rfl) ⟨47834, by rfl⟩) R95669
theorem R63809 : Reach 63809 := rs (se 2 (by rfl) ⟨23928, by rfl⟩) R47857
theorem R63827 : Reach 63827 := rs (se 1 (by rfl) ⟨47870, by rfl⟩) R95741
theorem R63857 : Reach 63857 := rs (se 2 (by rfl) ⟨23946, by rfl⟩) R47893
theorem R63875 : Reach 63875 := rs (se 1 (by rfl) ⟨47906, by rfl⟩) R95813
theorem R63905 : Reach 63905 := rs (se 2 (by rfl) ⟨23964, by rfl⟩) R47929
theorem R63923 : Reach 63923 := rs (se 1 (by rfl) ⟨47942, by rfl⟩) R95885
theorem R63953 : Reach 63953 := rs (se 2 (by rfl) ⟨23982, by rfl⟩) R47965
theorem R63971 : Reach 63971 := rs (se 1 (by rfl) ⟨47978, by rfl⟩) R95957
theorem R64001 : Reach 64001 := rs (se 2 (by rfl) ⟨24000, by rfl⟩) R48001
theorem R96785 : Reach 96785 := rs (se 2 (by rfl) ⟨36294, by rfl⟩) R72589
theorem R64019 : Reach 64019 := rs (se 1 (by rfl) ⟨48014, by rfl⟩) R96029
theorem R96803 : Reach 96803 := rs (se 1 (by rfl) ⟨72602, by rfl⟩) R145205
theorem R64049 : Reach 64049 := rs (se 2 (by rfl) ⟨24018, by rfl⟩) R48037
theorem R64067 : Reach 64067 := rs (se 1 (by rfl) ⟨48050, by rfl⟩) R96101
theorem R64097 : Reach 64097 := rs (se 2 (by rfl) ⟨24036, by rfl⟩) R48073
theorem R64115 : Reach 64115 := rs (se 1 (by rfl) ⟨48086, by rfl⟩) R96173
theorem R162445 : Reach 162445 := rs (se 3 (by rfl) ⟨30458, by rfl⟩) R60917
theorem R64145 : Reach 64145 := rs (se 2 (by rfl) ⟨24054, by rfl⟩) R48109
theorem R64163 : Reach 64163 := rs (se 1 (by rfl) ⟨48122, by rfl⟩) R96245
theorem R64193 : Reach 64193 := rs (se 2 (by rfl) ⟨24072, by rfl⟩) R48145
theorem R64211 : Reach 64211 := rs (se 1 (by rfl) ⟨48158, by rfl⟩) R96317
theorem R64241 : Reach 64241 := rs (se 2 (by rfl) ⟨24090, by rfl⟩) R48181
theorem R64259 : Reach 64259 := rs (se 1 (by rfl) ⟨48194, by rfl⟩) R96389
theorem R64289 : Reach 64289 := rs (se 2 (by rfl) ⟨24108, by rfl⟩) R48217
theorem R64307 : Reach 64307 := rs (se 1 (by rfl) ⟨48230, by rfl⟩) R96461
theorem R64337 : Reach 64337 := rs (se 2 (by rfl) ⟨24126, by rfl⟩) R48253
theorem R64355 : Reach 64355 := rs (se 1 (by rfl) ⟨48266, by rfl⟩) R96533
theorem R64385 : Reach 64385 := rs (se 2 (by rfl) ⟨24144, by rfl⟩) R48289
theorem R64403 : Reach 64403 := rs (se 1 (by rfl) ⟨48302, by rfl⟩) R96605
theorem R64433 : Reach 64433 := rs (se 2 (by rfl) ⟨24162, by rfl⟩) R48325
theorem R64451 : Reach 64451 := rs (se 1 (by rfl) ⟨48338, by rfl⟩) R96677
theorem R64481 : Reach 64481 := rs (se 2 (by rfl) ⟨24180, by rfl⟩) R48361
theorem R64499 : Reach 64499 := rs (se 1 (by rfl) ⟨48374, by rfl⟩) R96749
theorem R64529 : Reach 64529 := rs (se 2 (by rfl) ⟨24198, by rfl⟩) R48397
theorem R64547 : Reach 64547 := rs (se 1 (by rfl) ⟨48410, by rfl⟩) R96821
theorem R64577 : Reach 64577 := rs (se 2 (by rfl) ⟨24216, by rfl⟩) R48433
theorem R64595 : Reach 64595 := rs (se 1 (by rfl) ⟨48446, by rfl⟩) R96893
theorem R64625 : Reach 64625 := rs (se 2 (by rfl) ⟨24234, by rfl⟩) R48469
theorem R64643 : Reach 64643 := rs (se 1 (by rfl) ⟨48482, by rfl⟩) R96965
theorem R64673 : Reach 64673 := rs (se 2 (by rfl) ⟨24252, by rfl⟩) R48505
theorem R64739 : Reach 64739 := rs (se 1 (by rfl) ⟨48554, by rfl⟩) R97109
theorem R130349 : Reach 130349 := rs (se 3 (by rfl) ⟨24440, by rfl⟩) R48881
theorem R163235 : Reach 163235 := rs (se 1 (by rfl) ⟨122426, by rfl⟩) R244853
theorem R360035 : Reach 360035 := rs (se 1 (by rfl) ⟨270026, by rfl⟩) R540053
theorem R654961 : Reach 654961 := rs (se 2 (by rfl) ⟨245610, by rfl⟩) R491221
theorem R97955 : Reach 97955 := rs (se 1 (by rfl) ⟨73466, by rfl⟩) R146933
theorem R65815 : Reach 65815 := rs (se 1 (by rfl) ⟨49361, by rfl⟩) R98723
theorem R197081 : Reach 197081 := rs (se 2 (by rfl) ⟨73905, by rfl⟩) R147811
theorem R66187 : Reach 66187 := rs (se 1 (by rfl) ⟨49640, by rfl⟩) R99281
theorem R66199 : Reach 66199 := rs (se 1 (by rfl) ⟨49649, by rfl⟩) R99299
theorem R66251 : Reach 66251 := rs (se 1 (by rfl) ⟨49688, by rfl⟩) R99377
theorem R721709 : Reach 721709 := rs (se 3 (by rfl) ⟨135320, by rfl⟩) R270641
theorem R66379 : Reach 66379 := rs (se 1 (by rfl) ⟨49784, by rfl⟩) R99569
theorem R99265 : Reach 99265 := rs (se 2 (by rfl) ⟨37224, by rfl⟩) R74449
theorem R66521 : Reach 66521 := rs (se 2 (by rfl) ⟨24945, by rfl⟩) R49891
theorem R66649 : Reach 66649 := rs (se 2 (by rfl) ⟨24993, by rfl⟩) R49987
theorem R132299 : Reach 132299 := rs (se 1 (by rfl) ⟨99224, by rfl⟩) R198449
theorem R361745 : Reach 361745 := rs (se 2 (by rfl) ⟨135654, by rfl⟩) R271309
theorem R132569 : Reach 132569 := rs (se 2 (by rfl) ⟨49713, by rfl⟩) R99427
theorem R99863 : Reach 99863 := rs (se 1 (by rfl) ⟨74897, by rfl⟩) R149795
theorem R67097 : Reach 67097 := rs (se 2 (by rfl) ⟨25161, by rfl⟩) R50323
theorem R230957 : Reach 230957 := rs (se 3 (by rfl) ⟨43304, by rfl⟩) R86609
theorem R67223 : Reach 67223 := rs (se 1 (by rfl) ⟨50417, by rfl⟩) R100835
theorem R67225 : Reach 67225 := rs (se 2 (by rfl) ⟨25209, by rfl⟩) R50419
theorem R67351 : Reach 67351 := rs (se 1 (by rfl) ⟨50513, by rfl⟩) R101027
theorem R133015 : Reach 133015 := rs (se 1 (by rfl) ⟨99761, by rfl⟩) R199523
theorem R133271 : Reach 133271 := rs (se 1 (by rfl) ⟨99953, by rfl⟩) R199907
theorem R166195 : Reach 166195 := rs (se 1 (by rfl) ⟨124646, by rfl⟩) R249293
theorem R100673 : Reach 100673 := rs (se 2 (by rfl) ⟨37752, by rfl⟩) R75505
theorem R67979 : Reach 67979 := rs (se 1 (by rfl) ⟨50984, by rfl⟩) R101969
theorem R68107 : Reach 68107 := rs (se 1 (by rfl) ⟨51080, by rfl⟩) R102161
theorem R166531 : Reach 166531 := rs (se 1 (by rfl) ⟨124898, by rfl⟩) R249797
theorem R68249 : Reach 68249 := rs (se 2 (by rfl) ⟨25593, by rfl⟩) R51187
theorem R133811 : Reach 133811 := rs (se 1 (by rfl) ⟨100358, by rfl⟩) R200717
theorem R68377 : Reach 68377 := rs (se 2 (by rfl) ⟨25641, by rfl⟩) R51283
theorem R101209 : Reach 101209 := rs (se 2 (by rfl) ⟨37953, by rfl⟩) R75907
theorem R134081 : Reach 134081 := rs (se 2 (by rfl) ⟨50280, by rfl⟩) R100561
theorem R199745 : Reach 199745 := rs (se 2 (by rfl) ⟨74904, by rfl⟩) R149809
theorem R232523 : Reach 232523 := rs (se 1 (by rfl) ⟨174392, by rfl⟩) R348785
theorem R265517 : Reach 265517 := rs (se 3 (by rfl) ⟨49784, by rfl⟩) R99569
theorem R68951 : Reach 68951 := rs (se 1 (by rfl) ⟨51713, by rfl⟩) R103427
theorem R69079 : Reach 69079 := rs (se 1 (by rfl) ⟨51809, by rfl⟩) R103619
theorem R134621 : Reach 134621 := rs (se 3 (by rfl) ⟨25241, by rfl⟩) R50483
theorem R102323 : Reach 102323 := rs (se 1 (by rfl) ⟨76742, by rfl⟩) R153485
theorem R69619 : Reach 69619 := rs (se 1 (by rfl) ⟨52214, by rfl⟩) R104429
theorem R757795 : Reach 757795 := rs (se 1 (by rfl) ⟨568346, by rfl⟩) R1136693
theorem R69707 : Reach 69707 := rs (se 1 (by rfl) ⟨52280, by rfl⟩) R104561
theorem R69761 : Reach 69761 := rs (se 2 (by rfl) ⟨26160, by rfl⟩) R52321
theorem R364675 : Reach 364675 := rs (se 1 (by rfl) ⟨273506, by rfl⟩) R547013
theorem R69835 : Reach 69835 := rs (se 1 (by rfl) ⟨52376, by rfl⟩) R104753
theorem R102617 : Reach 102617 := rs (se 2 (by rfl) ⟨38481, by rfl⟩) R76963
theorem R69889 : Reach 69889 := rs (se 2 (by rfl) ⟨26208, by rfl⟩) R52417
theorem R69977 : Reach 69977 := rs (se 2 (by rfl) ⟨26241, by rfl⟩) R52483
theorem R70105 : Reach 70105 := rs (se 2 (by rfl) ⟨26289, by rfl⟩) R52579
theorem R135731 : Reach 135731 := rs (se 1 (by rfl) ⟨101798, by rfl⟩) R203597
theorem R135755 : Reach 135755 := rs (se 1 (by rfl) ⟨101816, by rfl⟩) R203633
theorem R136025 : Reach 136025 := rs (se 2 (by rfl) ⟨51009, by rfl⟩) R102019
theorem R201689 : Reach 201689 := rs (se 2 (by rfl) ⟨75633, by rfl⟩) R151267
theorem R70679 : Reach 70679 := rs (se 1 (by rfl) ⟨53009, by rfl⟩) R106019
theorem R398429 : Reach 398429 := rs (se 3 (by rfl) ⟨74705, by rfl⟩) R149411
theorem R660611 : Reach 660611 := rs (se 1 (by rfl) ⟨495458, by rfl⟩) R990917
theorem R234647 : Reach 234647 := rs (se 1 (by rfl) ⟨175985, by rfl⟩) R351971
theorem R70807 : Reach 70807 := rs (se 1 (by rfl) ⟨53105, by rfl⟩) R106211
theorem R169219 : Reach 169219 := rs (se 1 (by rfl) ⟨126914, by rfl⟩) R253829
theorem R136727 : Reach 136727 := rs (se 1 (by rfl) ⟨102545, by rfl⟩) R205091
theorem R71219 : Reach 71219 := rs (se 1 (by rfl) ⟨53414, by rfl⟩) R106829
theorem R71347 : Reach 71347 := rs (se 1 (by rfl) ⟨53510, by rfl⟩) R107021
theorem R71435 : Reach 71435 := rs (se 1 (by rfl) ⟨53576, by rfl⟩) R107153
theorem R71489 : Reach 71489 := rs (se 2 (by rfl) ⟨26808, by rfl⟩) R53617
theorem R104267 : Reach 104267 := rs (se 1 (by rfl) ⟨78200, by rfl⟩) R156401
theorem R71563 : Reach 71563 := rs (se 1 (by rfl) ⟨53672, by rfl⟩) R107345
theorem R71617 : Reach 71617 := rs (se 2 (by rfl) ⟨26856, by rfl⟩) R53713
theorem R71705 : Reach 71705 := rs (se 2 (by rfl) ⟨26889, by rfl⟩) R53779
theorem R137267 : Reach 137267 := rs (se 1 (by rfl) ⟨102950, by rfl⟩) R205901
theorem R5150789 : Reach 5150789 := rs (se 4 (by rfl) ⟨482886, by rfl⟩) R965773
theorem R71833 : Reach 71833 := rs (se 2 (by rfl) ⟨26937, by rfl⟩) R53875
theorem R661709 : Reach 661709 := rs (se 3 (by rfl) ⟨124070, by rfl⟩) R248141
theorem R465101 : Reach 465101 := rs (se 3 (by rfl) ⟨87206, by rfl⟩) R174413
theorem R39127 : Reach 39127 := rs (se 1 (by rfl) ⟨29345, by rfl⟩) R58691
theorem R39147 : Reach 39147 := rs (se 1 (by rfl) ⟨29360, by rfl⟩) R58721
theorem R39159 : Reach 39159 := rs (se 1 (by rfl) ⟨29369, by rfl⟩) R58739
theorem R39179 : Reach 39179 := rs (se 1 (by rfl) ⟨29384, by rfl⟩) R58769
theorem R39191 : Reach 39191 := rs (se 1 (by rfl) ⟨29393, by rfl⟩) R58787
theorem R39211 : Reach 39211 := rs (se 1 (by rfl) ⟨29408, by rfl⟩) R58817
theorem R39223 : Reach 39223 := rs (se 1 (by rfl) ⟨29417, by rfl⟩) R58835
theorem R137537 : Reach 137537 := rs (se 2 (by rfl) ⟨51576, by rfl⟩) R103153
theorem R39243 : Reach 39243 := rs (se 1 (by rfl) ⟨29432, by rfl⟩) R58865
theorem R39255 : Reach 39255 := rs (se 1 (by rfl) ⟨29441, by rfl⟩) R58883
theorem R39275 : Reach 39275 := rs (se 1 (by rfl) ⟨29456, by rfl⟩) R58913
theorem R39287 : Reach 39287 := rs (se 1 (by rfl) ⟨29465, by rfl⟩) R58931
theorem R39307 : Reach 39307 := rs (se 1 (by rfl) ⟨29480, by rfl⟩) R58961
theorem R39319 : Reach 39319 := rs (se 1 (by rfl) ⟨29489, by rfl⟩) R58979
theorem R39339 : Reach 39339 := rs (se 1 (by rfl) ⟨29504, by rfl⟩) R59009
theorem R39351 : Reach 39351 := rs (se 1 (by rfl) ⟨29513, by rfl⟩) R59027
theorem R39371 : Reach 39371 := rs (se 1 (by rfl) ⟨29528, by rfl⟩) R59057
theorem R39383 : Reach 39383 := rs (se 1 (by rfl) ⟨29537, by rfl⟩) R59075
theorem R39403 : Reach 39403 := rs (se 1 (by rfl) ⟨29552, by rfl⟩) R59105
theorem R39415 : Reach 39415 := rs (se 1 (by rfl) ⟨29561, by rfl⟩) R59123
theorem R39435 : Reach 39435 := rs (se 1 (by rfl) ⟨29576, by rfl⟩) R59153
theorem R39447 : Reach 39447 := rs (se 1 (by rfl) ⟨29585, by rfl⟩) R59171
theorem R39467 : Reach 39467 := rs (se 1 (by rfl) ⟨29600, by rfl⟩) R59201
theorem R203309 : Reach 203309 := rs (se 3 (by rfl) ⟨38120, by rfl⟩) R76241
theorem R39479 : Reach 39479 := rs (se 1 (by rfl) ⟨29609, by rfl⟩) R59219
theorem R170561 : Reach 170561 := rs (se 2 (by rfl) ⟨63960, by rfl⟩) R127921
theorem R39499 : Reach 39499 := rs (se 1 (by rfl) ⟨29624, by rfl⟩) R59249
theorem R39511 : Reach 39511 := rs (se 1 (by rfl) ⟨29633, by rfl⟩) R59267
theorem R39531 : Reach 39531 := rs (se 1 (by rfl) ⟨29648, by rfl⟩) R59297
theorem R39543 : Reach 39543 := rs (se 1 (by rfl) ⟨29657, by rfl⟩) R59315
theorem R39563 : Reach 39563 := rs (se 1 (by rfl) ⟨29672, by rfl⟩) R59345
theorem R39575 : Reach 39575 := rs (se 1 (by rfl) ⟨29681, by rfl⟩) R59363
theorem R39595 : Reach 39595 := rs (se 1 (by rfl) ⟨29696, by rfl⟩) R59393
theorem R39607 : Reach 39607 := rs (se 1 (by rfl) ⟨29705, by rfl⟩) R59411
theorem R39627 : Reach 39627 := rs (se 1 (by rfl) ⟨29720, by rfl⟩) R59441
theorem R39639 : Reach 39639 := rs (se 1 (by rfl) ⟨29729, by rfl⟩) R59459
theorem R72407 : Reach 72407 := rs (se 1 (by rfl) ⟨54305, by rfl⟩) R108611
theorem R39659 : Reach 39659 := rs (se 1 (by rfl) ⟨29744, by rfl⟩) R59489
theorem R39671 : Reach 39671 := rs (se 1 (by rfl) ⟨29753, by rfl⟩) R59507
theorem R39691 : Reach 39691 := rs (se 1 (by rfl) ⟨29768, by rfl⟩) R59537
theorem R39703 : Reach 39703 := rs (se 1 (by rfl) ⟨29777, by rfl⟩) R59555
theorem R105239 : Reach 105239 := rs (se 1 (by rfl) ⟨78929, by rfl⟩) R157859
theorem R39723 : Reach 39723 := rs (se 1 (by rfl) ⟨29792, by rfl⟩) R59585
theorem R39735 : Reach 39735 := rs (se 1 (by rfl) ⟨29801, by rfl⟩) R59603
theorem R39755 : Reach 39755 := rs (se 1 (by rfl) ⟨29816, by rfl⟩) R59633
theorem R39767 : Reach 39767 := rs (se 1 (by rfl) ⟨29825, by rfl⟩) R59651
theorem R72535 : Reach 72535 := rs (se 1 (by rfl) ⟨54401, by rfl⟩) R108803
theorem R138077 : Reach 138077 := rs (se 3 (by rfl) ⟨25889, by rfl⟩) R51779
theorem R39787 : Reach 39787 := rs (se 1 (by rfl) ⟨29840, by rfl⟩) R59681
theorem R39799 : Reach 39799 := rs (se 1 (by rfl) ⟨29849, by rfl⟩) R59699
theorem R39819 : Reach 39819 := rs (se 1 (by rfl) ⟨29864, by rfl⟩) R59729
theorem R39831 : Reach 39831 := rs (se 1 (by rfl) ⟨29873, by rfl⟩) R59747
theorem R269207 : Reach 269207 := rs (se 1 (by rfl) ⟨201905, by rfl⟩) R403811
theorem R39851 : Reach 39851 := rs (se 1 (by rfl) ⟨29888, by rfl⟩) R59777
theorem R39863 : Reach 39863 := rs (se 1 (by rfl) ⟨29897, by rfl⟩) R59795
theorem R39883 : Reach 39883 := rs (se 1 (by rfl) ⟨29912, by rfl⟩) R59825
theorem R39895 : Reach 39895 := rs (se 1 (by rfl) ⟨29921, by rfl⟩) R59843
theorem R39915 : Reach 39915 := rs (se 1 (by rfl) ⟨29936, by rfl⟩) R59873
theorem R39927 : Reach 39927 := rs (se 1 (by rfl) ⟨29945, by rfl⟩) R59891
theorem R334853 : Reach 334853 := rs (se 4 (by rfl) ⟨31392, by rfl⟩) R62785
theorem R39947 : Reach 39947 := rs (se 1 (by rfl) ⟨29960, by rfl⟩) R59921
theorem R39959 : Reach 39959 := rs (se 1 (by rfl) ⟨29969, by rfl⟩) R59939
theorem R171031 : Reach 171031 := rs (se 1 (by rfl) ⟨128273, by rfl⟩) R256547
theorem R39979 : Reach 39979 := rs (se 1 (by rfl) ⟨29984, by rfl⟩) R59969
theorem R39991 : Reach 39991 := rs (se 1 (by rfl) ⟨29993, by rfl⟩) R59987
theorem R40011 : Reach 40011 := rs (se 1 (by rfl) ⟨30008, by rfl⟩) R60017
theorem R40023 : Reach 40023 := rs (se 1 (by rfl) ⟨30017, by rfl⟩) R60035
theorem R466013 : Reach 466013 := rs (se 3 (by rfl) ⟨87377, by rfl⟩) R174755
theorem R40043 : Reach 40043 := rs (se 1 (by rfl) ⟨30032, by rfl⟩) R60065
theorem R40055 : Reach 40055 := rs (se 1 (by rfl) ⟨30041, by rfl⟩) R60083
theorem R40075 : Reach 40075 := rs (se 1 (by rfl) ⟨30056, by rfl⟩) R60113
theorem R40087 : Reach 40087 := rs (se 1 (by rfl) ⟨30065, by rfl⟩) R60131
theorem R40107 : Reach 40107 := rs (se 1 (by rfl) ⟨30080, by rfl⟩) R60161
theorem R40119 : Reach 40119 := rs (se 1 (by rfl) ⟨30089, by rfl⟩) R60179
theorem R40139 : Reach 40139 := rs (se 1 (by rfl) ⟨30104, by rfl⟩) R60209
theorem R40151 : Reach 40151 := rs (se 1 (by rfl) ⟨30113, by rfl⟩) R60227
theorem R40171 : Reach 40171 := rs (se 1 (by rfl) ⟨30128, by rfl⟩) R60257
theorem R72947 : Reach 72947 := rs (se 1 (by rfl) ⟨54710, by rfl⟩) R109421
theorem R40183 : Reach 40183 := rs (se 1 (by rfl) ⟨30137, by rfl⟩) R60275
theorem R40203 : Reach 40203 := rs (se 1 (by rfl) ⟨30152, by rfl⟩) R60305
theorem R40215 : Reach 40215 := rs (se 1 (by rfl) ⟨30161, by rfl⟩) R60323
theorem R40235 : Reach 40235 := rs (se 1 (by rfl) ⟨30176, by rfl⟩) R60353
theorem R40247 : Reach 40247 := rs (se 1 (by rfl) ⟨30185, by rfl⟩) R60371
theorem R40267 : Reach 40267 := rs (se 1 (by rfl) ⟨30200, by rfl⟩) R60401
theorem R40279 : Reach 40279 := rs (se 1 (by rfl) ⟨30209, by rfl⟩) R60419
theorem R269669 : Reach 269669 := rs (se 4 (by rfl) ⟨25281, by rfl⟩) R50563
theorem R40299 : Reach 40299 := rs (se 1 (by rfl) ⟨30224, by rfl⟩) R60449
theorem R40311 : Reach 40311 := rs (se 1 (by rfl) ⟨30233, by rfl⟩) R60467
theorem R40331 : Reach 40331 := rs (se 1 (by rfl) ⟨30248, by rfl⟩) R60497
theorem R40343 : Reach 40343 := rs (se 1 (by rfl) ⟨30257, by rfl⟩) R60515
theorem R40363 : Reach 40363 := rs (se 1 (by rfl) ⟨30272, by rfl⟩) R60545
theorem R499121 : Reach 499121 := rs (se 2 (by rfl) ⟨187170, by rfl⟩) R374341
theorem R105907 : Reach 105907 := rs (se 1 (by rfl) ⟨79430, by rfl⟩) R158861
theorem R204211 : Reach 204211 := rs (se 1 (by rfl) ⟨153158, by rfl⟩) R306317
theorem R40375 : Reach 40375 := rs (se 1 (by rfl) ⟨30281, by rfl⟩) R60563
theorem R40395 : Reach 40395 := rs (se 1 (by rfl) ⟨30296, by rfl⟩) R60593
theorem R40407 : Reach 40407 := rs (se 1 (by rfl) ⟨30305, by rfl⟩) R60611
theorem R73177 : Reach 73177 := rs (se 2 (by rfl) ⟨27441, by rfl⟩) R54883
theorem R40427 : Reach 40427 := rs (se 1 (by rfl) ⟨30320, by rfl⟩) R60641
theorem R40439 : Reach 40439 := rs (se 1 (by rfl) ⟨30329, by rfl⟩) R60659
theorem R40459 : Reach 40459 := rs (se 1 (by rfl) ⟨30344, by rfl⟩) R60689
theorem R40471 : Reach 40471 := rs (se 1 (by rfl) ⟨30353, by rfl⟩) R60707
theorem R40491 : Reach 40491 := rs (se 1 (by rfl) ⟨30368, by rfl⟩) R60737
theorem R40503 : Reach 40503 := rs (se 1 (by rfl) ⟨30377, by rfl⟩) R60755
theorem R106049 : Reach 106049 := rs (se 2 (by rfl) ⟨39768, by rfl⟩) R79537
theorem R40523 : Reach 40523 := rs (se 1 (by rfl) ⟨30392, by rfl⟩) R60785
theorem R40535 : Reach 40535 := rs (se 1 (by rfl) ⟨30401, by rfl⟩) R60803
theorem R40555 : Reach 40555 := rs (se 1 (by rfl) ⟨30416, by rfl⟩) R60833
theorem R40567 : Reach 40567 := rs (se 1 (by rfl) ⟨30425, by rfl⟩) R60851
theorem R73345 : Reach 73345 := rs (se 2 (by rfl) ⟨27504, by rfl⟩) R55009
theorem R40587 : Reach 40587 := rs (se 1 (by rfl) ⟨30440, by rfl⟩) R60881
theorem R171665 : Reach 171665 := rs (se 2 (by rfl) ⟨64374, by rfl⟩) R128749
theorem R40599 : Reach 40599 := rs (se 1 (by rfl) ⟨30449, by rfl⟩) R60899
theorem R40619 : Reach 40619 := rs (se 1 (by rfl) ⟨30464, by rfl⟩) R60929
theorem R40631 : Reach 40631 := rs (se 1 (by rfl) ⟨30473, by rfl⟩) R60947
theorem R40651 : Reach 40651 := rs (se 1 (by rfl) ⟨30488, by rfl⟩) R60977
theorem R40663 : Reach 40663 := rs (se 1 (by rfl) ⟨30497, by rfl⟩) R60995
theorem R40683 : Reach 40683 := rs (se 1 (by rfl) ⟨30512, by rfl⟩) R61025
theorem R40695 : Reach 40695 := rs (se 1 (by rfl) ⟨30521, by rfl⟩) R61043
theorem R40715 : Reach 40715 := rs (se 1 (by rfl) ⟨30536, by rfl⟩) R61073
theorem R40727 : Reach 40727 := rs (se 1 (by rfl) ⟨30545, by rfl⟩) R61091
theorem R40747 : Reach 40747 := rs (se 1 (by rfl) ⟨30560, by rfl⟩) R61121
theorem R40759 : Reach 40759 := rs (se 1 (by rfl) ⟨30569, by rfl⟩) R61139
theorem R40779 : Reach 40779 := rs (se 1 (by rfl) ⟨30584, by rfl⟩) R61169
theorem R40791 : Reach 40791 := rs (se 1 (by rfl) ⟨30593, by rfl⟩) R61187
theorem R40811 : Reach 40811 := rs (se 1 (by rfl) ⟨30608, by rfl⟩) R61217
theorem R40823 : Reach 40823 := rs (se 1 (by rfl) ⟨30617, by rfl⟩) R61235
theorem R40843 : Reach 40843 := rs (se 1 (by rfl) ⟨30632, by rfl⟩) R61265
theorem R40855 : Reach 40855 := rs (se 1 (by rfl) ⟨30641, by rfl⟩) R61283
theorem R40875 : Reach 40875 := rs (se 1 (by rfl) ⟨30656, by rfl⟩) R61313
theorem R40887 : Reach 40887 := rs (se 1 (by rfl) ⟨30665, by rfl⟩) R61331
theorem R40907 : Reach 40907 := rs (se 1 (by rfl) ⟨30680, by rfl⟩) R61361
theorem R139211 : Reach 139211 := rs (se 1 (by rfl) ⟨104408, by rfl⟩) R208817
theorem R40919 : Reach 40919 := rs (se 1 (by rfl) ⟨30689, by rfl⟩) R61379
theorem R40939 : Reach 40939 := rs (se 1 (by rfl) ⟨30704, by rfl⟩) R61409
theorem R40951 : Reach 40951 := rs (se 1 (by rfl) ⟨30713, by rfl⟩) R61427
theorem R40971 : Reach 40971 := rs (se 1 (by rfl) ⟨30728, by rfl⟩) R61457
theorem R40983 : Reach 40983 := rs (se 1 (by rfl) ⟨30737, by rfl⟩) R61475
theorem R41003 : Reach 41003 := rs (se 1 (by rfl) ⟨30752, by rfl⟩) R61505
theorem R41015 : Reach 41015 := rs (se 1 (by rfl) ⟨30761, by rfl⟩) R61523
theorem R41035 : Reach 41035 := rs (se 1 (by rfl) ⟨30776, by rfl⟩) R61553
theorem R41047 : Reach 41047 := rs (se 1 (by rfl) ⟨30785, by rfl⟩) R61571
theorem R41067 : Reach 41067 := rs (se 1 (by rfl) ⟨30800, by rfl⟩) R61601
theorem R41079 : Reach 41079 := rs (se 1 (by rfl) ⟨30809, by rfl⟩) R61619
theorem R41099 : Reach 41099 := rs (se 1 (by rfl) ⟨30824, by rfl⟩) R61649
theorem R41111 : Reach 41111 := rs (se 1 (by rfl) ⟨30833, by rfl⟩) R61667
theorem R41131 : Reach 41131 := rs (se 1 (by rfl) ⟨30848, by rfl⟩) R61697
theorem R41143 : Reach 41143 := rs (se 1 (by rfl) ⟨30857, by rfl⟩) R61715
theorem R41163 : Reach 41163 := rs (se 1 (by rfl) ⟨30872, by rfl⟩) R61745
theorem R73943 : Reach 73943 := rs (se 1 (by rfl) ⟨55457, by rfl⟩) R110915
theorem R41175 : Reach 41175 := rs (se 1 (by rfl) ⟨30881, by rfl⟩) R61763
theorem R139481 : Reach 139481 := rs (se 2 (by rfl) ⟨52305, by rfl⟩) R104611
theorem R106717 : Reach 106717 := rs (se 3 (by rfl) ⟨20009, by rfl⟩) R40019
theorem R41195 : Reach 41195 := rs (se 1 (by rfl) ⟨30896, by rfl⟩) R61793
theorem R41207 : Reach 41207 := rs (se 1 (by rfl) ⟨30905, by rfl⟩) R61811
theorem R41227 : Reach 41227 := rs (se 1 (by rfl) ⟨30920, by rfl⟩) R61841
theorem R41239 : Reach 41239 := rs (se 1 (by rfl) ⟨30929, by rfl⟩) R61859
theorem R41259 : Reach 41259 := rs (se 1 (by rfl) ⟨30944, by rfl⟩) R61889
theorem R41271 : Reach 41271 := rs (se 1 (by rfl) ⟨30953, by rfl⟩) R61907
theorem R172363 : Reach 172363 := rs (se 1 (by rfl) ⟨129272, by rfl⟩) R258545
theorem R41291 : Reach 41291 := rs (se 1 (by rfl) ⟨30968, by rfl⟩) R61937
theorem R41303 : Reach 41303 := rs (se 1 (by rfl) ⟨30977, by rfl⟩) R61955
theorem R41323 : Reach 41323 := rs (se 1 (by rfl) ⟨30992, by rfl⟩) R61985
theorem R41335 : Reach 41335 := rs (se 1 (by rfl) ⟨31001, by rfl⟩) R62003
theorem R41355 : Reach 41355 := rs (se 1 (by rfl) ⟨31016, by rfl⟩) R62033
theorem R41367 : Reach 41367 := rs (se 1 (by rfl) ⟨31025, by rfl⟩) R62051
theorem R41387 : Reach 41387 := rs (se 1 (by rfl) ⟨31040, by rfl⟩) R62081
theorem R41399 : Reach 41399 := rs (se 1 (by rfl) ⟨31049, by rfl⟩) R62099
theorem R41419 : Reach 41419 := rs (se 1 (by rfl) ⟨31064, by rfl⟩) R62129
theorem R41431 : Reach 41431 := rs (se 1 (by rfl) ⟨31073, by rfl⟩) R62147
theorem R41451 : Reach 41451 := rs (se 1 (by rfl) ⟨31088, by rfl⟩) R62177
theorem R41463 : Reach 41463 := rs (se 1 (by rfl) ⟨31097, by rfl⟩) R62195
theorem R41483 : Reach 41483 := rs (se 1 (by rfl) ⟨31112, by rfl⟩) R62225
theorem R41495 : Reach 41495 := rs (se 1 (by rfl) ⟨31121, by rfl⟩) R62243
theorem R41515 : Reach 41515 := rs (se 1 (by rfl) ⟨31136, by rfl⟩) R62273
theorem R41527 : Reach 41527 := rs (se 1 (by rfl) ⟨31145, by rfl⟩) R62291
theorem R41547 : Reach 41547 := rs (se 1 (by rfl) ⟨31160, by rfl⟩) R62321
theorem R41559 : Reach 41559 := rs (se 1 (by rfl) ⟨31169, by rfl⟩) R62339
theorem R172637 : Reach 172637 := rs (se 3 (by rfl) ⟨32369, by rfl⟩) R64739
theorem R41579 : Reach 41579 := rs (se 1 (by rfl) ⟨31184, by rfl⟩) R62369
theorem R41591 : Reach 41591 := rs (se 1 (by rfl) ⟨31193, by rfl⟩) R62387
theorem R41611 : Reach 41611 := rs (se 1 (by rfl) ⟨31208, by rfl⟩) R62417
theorem R41623 : Reach 41623 := rs (se 1 (by rfl) ⟨31217, by rfl⟩) R62435
theorem R41643 : Reach 41643 := rs (se 1 (by rfl) ⟨31232, by rfl⟩) R62465
theorem R41655 : Reach 41655 := rs (se 1 (by rfl) ⟨31241, by rfl⟩) R62483
theorem R41675 : Reach 41675 := rs (se 1 (by rfl) ⟨31256, by rfl⟩) R62513
theorem R41687 : Reach 41687 := rs (se 1 (by rfl) ⟨31265, by rfl⟩) R62531
theorem R41707 : Reach 41707 := rs (se 1 (by rfl) ⟨31280, by rfl⟩) R62561
theorem R41719 : Reach 41719 := rs (se 1 (by rfl) ⟨31289, by rfl⟩) R62579
theorem R41739 : Reach 41739 := rs (se 1 (by rfl) ⟨31304, by rfl⟩) R62609
theorem R41751 : Reach 41751 := rs (se 1 (by rfl) ⟨31313, by rfl⟩) R62627
theorem R41771 : Reach 41771 := rs (se 1 (by rfl) ⟨31328, by rfl⟩) R62657
theorem R107315 : Reach 107315 := rs (se 1 (by rfl) ⟨80486, by rfl⟩) R160973
theorem R41783 : Reach 41783 := rs (se 1 (by rfl) ⟨31337, by rfl⟩) R62675
theorem R41803 : Reach 41803 := rs (se 1 (by rfl) ⟨31352, by rfl⟩) R62705
theorem R41815 : Reach 41815 := rs (se 1 (by rfl) ⟨31361, by rfl⟩) R62723
theorem R41835 : Reach 41835 := rs (se 1 (by rfl) ⟨31376, by rfl⟩) R62753
theorem R41847 : Reach 41847 := rs (se 1 (by rfl) ⟨31385, by rfl⟩) R62771
theorem R41867 : Reach 41867 := rs (se 1 (by rfl) ⟨31400, by rfl⟩) R62801
theorem R140183 : Reach 140183 := rs (se 1 (by rfl) ⟨105137, by rfl⟩) R210275
theorem R41879 : Reach 41879 := rs (se 1 (by rfl) ⟨31409, by rfl⟩) R62819
theorem R41899 : Reach 41899 := rs (se 1 (by rfl) ⟨31424, by rfl⟩) R62849
theorem R172979 : Reach 172979 := rs (se 1 (by rfl) ⟨129734, by rfl⟩) R259469
theorem R41911 : Reach 41911 := rs (se 1 (by rfl) ⟨31433, by rfl⟩) R62867
theorem R41931 : Reach 41931 := rs (se 1 (by rfl) ⟨31448, by rfl⟩) R62897
theorem R41943 : Reach 41943 := rs (se 1 (by rfl) ⟨31457, by rfl⟩) R62915
theorem R41963 : Reach 41963 := rs (se 1 (by rfl) ⟨31472, by rfl⟩) R62945
theorem R41975 : Reach 41975 := rs (se 1 (by rfl) ⟨31481, by rfl⟩) R62963
theorem R74753 : Reach 74753 := rs (se 2 (by rfl) ⟨28032, by rfl⟩) R56065
theorem R140291 : Reach 140291 := rs (se 1 (by rfl) ⟨105218, by rfl⟩) R210437
theorem R41995 : Reach 41995 := rs (se 1 (by rfl) ⟨31496, by rfl⟩) R62993
theorem R42007 : Reach 42007 := rs (se 1 (by rfl) ⟨31505, by rfl⟩) R63011
theorem R42027 : Reach 42027 := rs (se 1 (by rfl) ⟨31520, by rfl⟩) R63041
theorem R42039 : Reach 42039 := rs (se 1 (by rfl) ⟨31529, by rfl⟩) R63059
theorem R42059 : Reach 42059 := rs (se 1 (by rfl) ⟨31544, by rfl⟩) R63089
theorem R42071 : Reach 42071 := rs (se 1 (by rfl) ⟨31553, by rfl⟩) R63107
theorem R42091 : Reach 42091 := rs (se 1 (by rfl) ⟨31568, by rfl⟩) R63137
theorem R42103 : Reach 42103 := rs (se 1 (by rfl) ⟨31577, by rfl⟩) R63155
theorem R42123 : Reach 42123 := rs (se 1 (by rfl) ⟨31592, by rfl⟩) R63185
theorem R42135 : Reach 42135 := rs (se 1 (by rfl) ⟨31601, by rfl⟩) R63203
theorem R42155 : Reach 42155 := rs (se 1 (by rfl) ⟨31616, by rfl⟩) R63233
theorem R42167 : Reach 42167 := rs (se 1 (by rfl) ⟨31625, by rfl⟩) R63251
theorem R42187 : Reach 42187 := rs (se 1 (by rfl) ⟨31640, by rfl⟩) R63281
theorem R42199 : Reach 42199 := rs (se 1 (by rfl) ⟨31649, by rfl⟩) R63299
theorem R42219 : Reach 42219 := rs (se 1 (by rfl) ⟨31664, by rfl⟩) R63329
theorem R42231 : Reach 42231 := rs (se 1 (by rfl) ⟨31673, by rfl⟩) R63347
theorem R75019 : Reach 75019 := rs (se 1 (by rfl) ⟨56264, by rfl⟩) R112529
theorem R42251 : Reach 42251 := rs (se 1 (by rfl) ⟨31688, by rfl⟩) R63377
theorem R140561 : Reach 140561 := rs (se 2 (by rfl) ⟨52710, by rfl⟩) R105421
theorem R42263 : Reach 42263 := rs (se 1 (by rfl) ⟨31697, by rfl⟩) R63395
theorem R42283 : Reach 42283 := rs (se 1 (by rfl) ⟨31712, by rfl⟩) R63425
theorem R402733 : Reach 402733 := rs (se 3 (by rfl) ⟨75512, by rfl⟩) R151025
theorem R75059 : Reach 75059 := rs (se 1 (by rfl) ⟨56294, by rfl⟩) R112589
theorem R42295 : Reach 42295 := rs (se 1 (by rfl) ⟨31721, by rfl⟩) R63443
theorem R42315 : Reach 42315 := rs (se 1 (by rfl) ⟨31736, by rfl⟩) R63473
theorem R107851 : Reach 107851 := rs (se 1 (by rfl) ⟨80888, by rfl⟩) R161777
theorem R42327 : Reach 42327 := rs (se 1 (by rfl) ⟨31745, by rfl⟩) R63491
theorem R42347 : Reach 42347 := rs (se 1 (by rfl) ⟨31760, by rfl⟩) R63521
theorem R42359 : Reach 42359 := rs (se 1 (by rfl) ⟨31769, by rfl⟩) R63539
theorem R42379 : Reach 42379 := rs (se 1 (by rfl) ⟨31784, by rfl⟩) R63569
theorem R42391 : Reach 42391 := rs (se 1 (by rfl) ⟨31793, by rfl⟩) R63587
theorem R42411 : Reach 42411 := rs (se 1 (by rfl) ⟨31808, by rfl⟩) R63617
theorem R140723 : Reach 140723 := rs (se 1 (by rfl) ⟨105542, by rfl⟩) R211085
theorem R42423 : Reach 42423 := rs (se 1 (by rfl) ⟨31817, by rfl⟩) R63635
theorem R42443 : Reach 42443 := rs (se 1 (by rfl) ⟨31832, by rfl⟩) R63665
theorem R42455 : Reach 42455 := rs (se 1 (by rfl) ⟨31841, by rfl⟩) R63683
theorem R107993 : Reach 107993 := rs (se 2 (by rfl) ⟨40497, by rfl⟩) R80995
theorem R42475 : Reach 42475 := rs (se 1 (by rfl) ⟨31856, by rfl⟩) R63713
theorem R42487 : Reach 42487 := rs (se 1 (by rfl) ⟨31865, by rfl⟩) R63731
theorem R42507 : Reach 42507 := rs (se 1 (by rfl) ⟨31880, by rfl⟩) R63761
theorem R468497 : Reach 468497 := rs (se 2 (by rfl) ⟨175686, by rfl⟩) R351373
theorem R42519 : Reach 42519 := rs (se 1 (by rfl) ⟨31889, by rfl⟩) R63779
theorem R42539 : Reach 42539 := rs (se 1 (by rfl) ⟨31904, by rfl⟩) R63809
theorem R42551 : Reach 42551 := rs (se 1 (by rfl) ⟨31913, by rfl⟩) R63827
theorem R42571 : Reach 42571 := rs (se 1 (by rfl) ⟨31928, by rfl⟩) R63857
theorem R42583 : Reach 42583 := rs (se 1 (by rfl) ⟨31937, by rfl⟩) R63875
theorem R108125 : Reach 108125 := rs (se 3 (by rfl) ⟨20273, by rfl⟩) R40547
theorem R42603 : Reach 42603 := rs (se 1 (by rfl) ⟨31952, by rfl⟩) R63905
theorem R42615 : Reach 42615 := rs (se 1 (by rfl) ⟨31961, by rfl⟩) R63923
theorem R42635 : Reach 42635 := rs (se 1 (by rfl) ⟨31976, by rfl⟩) R63953
theorem R42647 : Reach 42647 := rs (se 1 (by rfl) ⟨31985, by rfl⟩) R63971
theorem R42667 : Reach 42667 := rs (se 1 (by rfl) ⟨32000, by rfl⟩) R64001
theorem R42679 : Reach 42679 := rs (se 1 (by rfl) ⟨32009, by rfl⟩) R64019
theorem R140993 : Reach 140993 := rs (se 2 (by rfl) ⟨52872, by rfl⟩) R105745
theorem R75467 : Reach 75467 := rs (se 1 (by rfl) ⟨56600, by rfl⟩) R113201
theorem R42699 : Reach 42699 := rs (se 1 (by rfl) ⟨32024, by rfl⟩) R64049
theorem R42711 : Reach 42711 := rs (se 1 (by rfl) ⟨32033, by rfl⟩) R64067
theorem R108253 : Reach 108253 := rs (se 3 (by rfl) ⟨20297, by rfl⟩) R40595
theorem R42731 : Reach 42731 := rs (se 1 (by rfl) ⟨32048, by rfl⟩) R64097
theorem R42743 : Reach 42743 := rs (se 1 (by rfl) ⟨32057, by rfl⟩) R64115
theorem R42763 : Reach 42763 := rs (se 1 (by rfl) ⟨32072, by rfl⟩) R64145
theorem R42775 : Reach 42775 := rs (se 1 (by rfl) ⟨32081, by rfl⟩) R64163
theorem R42795 : Reach 42795 := rs (se 1 (by rfl) ⟨32096, by rfl⟩) R64193
theorem R141101 : Reach 141101 := rs (se 3 (by rfl) ⟨26456, by rfl⟩) R52913
theorem R141107 : Reach 141107 := rs (se 1 (by rfl) ⟨105830, by rfl⟩) R211661
theorem R42807 : Reach 42807 := rs (se 1 (by rfl) ⟨32105, by rfl⟩) R64211
theorem R206657 : Reach 206657 := rs (se 2 (by rfl) ⟨77496, by rfl⟩) R154993
theorem R42827 : Reach 42827 := rs (se 1 (by rfl) ⟨32120, by rfl⟩) R64241
theorem R42839 : Reach 42839 := rs (se 1 (by rfl) ⟨32129, by rfl⟩) R64259
theorem R42859 : Reach 42859 := rs (se 1 (by rfl) ⟨32144, by rfl⟩) R64289
theorem R42871 : Reach 42871 := rs (se 1 (by rfl) ⟨32153, by rfl⟩) R64307
theorem R75649 : Reach 75649 := rs (se 2 (by rfl) ⟨28368, by rfl⟩) R56737
theorem R42891 : Reach 42891 := rs (se 1 (by rfl) ⟨32168, by rfl⟩) R64337
theorem R42903 : Reach 42903 := rs (se 1 (by rfl) ⟨32177, by rfl⟩) R64355
theorem R42923 : Reach 42923 := rs (se 1 (by rfl) ⟨32192, by rfl⟩) R64385
theorem R42935 : Reach 42935 := rs (se 1 (by rfl) ⟨32201, by rfl⟩) R64403
theorem R42955 : Reach 42955 := rs (se 1 (by rfl) ⟨32216, by rfl⟩) R64433
theorem R42967 : Reach 42967 := rs (se 1 (by rfl) ⟨32225, by rfl⟩) R64451
theorem R42987 : Reach 42987 := rs (se 1 (by rfl) ⟨32240, by rfl⟩) R64481
theorem R42999 : Reach 42999 := rs (se 1 (by rfl) ⟨32249, by rfl⟩) R64499
theorem R43019 : Reach 43019 := rs (se 1 (by rfl) ⟨32264, by rfl⟩) R64529
theorem R43031 : Reach 43031 := rs (se 1 (by rfl) ⟨32273, by rfl⟩) R64547
theorem R43051 : Reach 43051 := rs (se 1 (by rfl) ⟨32288, by rfl⟩) R64577
theorem R43063 : Reach 43063 := rs (se 1 (by rfl) ⟨32297, by rfl⟩) R64595
theorem R43083 : Reach 43083 := rs (se 1 (by rfl) ⟨32312, by rfl⟩) R64625
theorem R43095 : Reach 43095 := rs (se 1 (by rfl) ⟨32321, by rfl⟩) R64643
theorem R43115 : Reach 43115 := rs (se 1 (by rfl) ⟨32336, by rfl⟩) R64673
theorem R75991 : Reach 75991 := rs (se 1 (by rfl) ⟨56993, by rfl⟩) R113987
theorem R141533 : Reach 141533 := rs (se 3 (by rfl) ⟨26537, by rfl⟩) R53075
theorem R108823 : Reach 108823 := rs (se 1 (by rfl) ⟨81617, by rfl⟩) R163235
theorem R338251 : Reach 338251 := rs (se 1 (by rfl) ⟨253688, by rfl⟩) R507377
theorem R207197 : Reach 207197 := rs (se 3 (by rfl) ⟨38849, by rfl⟩) R77699
theorem R240023 : Reach 240023 := rs (se 1 (by rfl) ⟨180017, by rfl⟩) R360035
theorem R76211 : Reach 76211 := rs (se 1 (by rfl) ⟨57158, by rfl⟩) R114317
theorem R272857 : Reach 272857 := rs (se 2 (by rfl) ⟨102321, by rfl⟩) R204643
theorem R76249 : Reach 76249 := rs (se 2 (by rfl) ⟨28593, by rfl⟩) R57187
theorem R76439 : Reach 76439 := rs (se 1 (by rfl) ⟨57329, by rfl⟩) R114659
theorem R43723 : Reach 43723 := rs (se 1 (by rfl) ⟨32792, by rfl⟩) R65585
theorem R76697 : Reach 76697 := rs (se 2 (by rfl) ⟨28761, by rfl⟩) R57523
theorem R76747 : Reach 76747 := rs (se 1 (by rfl) ⟨57560, by rfl⟩) R115121
theorem R44023 : Reach 44023 := rs (se 1 (by rfl) ⟨33017, by rfl⟩) R66035
theorem R44203 : Reach 44203 := rs (se 1 (by rfl) ⟨33152, by rfl⟩) R66305
theorem R1682693 : Reach 1682693 := rs (se 4 (by rfl) ⟨157752, by rfl⟩) R315505
theorem R44311 : Reach 44311 := rs (se 1 (by rfl) ⟨33233, by rfl⟩) R66467
theorem R175405 : Reach 175405 := rs (se 3 (by rfl) ⟨32888, by rfl⟩) R65777
theorem R77107 : Reach 77107 := rs (se 1 (by rfl) ⟨57830, by rfl⟩) R115661
theorem R142667 : Reach 142667 := rs (se 1 (by rfl) ⟨107000, by rfl⟩) R214001
theorem R44491 : Reach 44491 := rs (se 1 (by rfl) ⟨33368, by rfl⟩) R66737
theorem R372185 : Reach 372185 := rs (se 2 (by rfl) ⟨139569, by rfl⟩) R279139
theorem R44599 : Reach 44599 := rs (se 1 (by rfl) ⟨33449, by rfl⟩) R66899
theorem R142937 : Reach 142937 := rs (se 2 (by rfl) ⟨53601, by rfl⟩) R107203
theorem R44779 : Reach 44779 := rs (se 1 (by rfl) ⟨33584, by rfl⟩) R67169
theorem R77593 : Reach 77593 := rs (se 2 (by rfl) ⟨29097, by rfl⟩) R58195
theorem R44887 : Reach 44887 := rs (se 1 (by rfl) ⟨33665, by rfl⟩) R67331
theorem R241501 : Reach 241501 := rs (se 3 (by rfl) ⟨45281, by rfl⟩) R90563
theorem R569267 : Reach 569267 := rs (se 1 (by rfl) ⟨426950, by rfl⟩) R853901
theorem R45067 : Reach 45067 := rs (se 1 (by rfl) ⟨33800, by rfl⟩) R67601
theorem R143411 : Reach 143411 := rs (se 1 (by rfl) ⟨107558, by rfl⟩) R215117
theorem R45175 : Reach 45175 := rs (se 1 (by rfl) ⟨33881, by rfl⟩) R67763
theorem R241937 : Reach 241937 := rs (se 2 (by rfl) ⟨90726, by rfl⟩) R181453
theorem R143639 : Reach 143639 := rs (se 1 (by rfl) ⟨107729, by rfl⟩) R215459
theorem R45355 : Reach 45355 := rs (se 1 (by rfl) ⟨34016, by rfl⟩) R68033
theorem R78155 : Reach 78155 := rs (se 1 (by rfl) ⟨58616, by rfl⟩) R117233
theorem R143747 : Reach 143747 := rs (se 1 (by rfl) ⟨107810, by rfl⟩) R215621
theorem R45463 : Reach 45463 := rs (se 1 (by rfl) ⟨34097, by rfl⟩) R68195
theorem R209303 : Reach 209303 := rs (se 1 (by rfl) ⟨156977, by rfl⟩) R313955
theorem R143795 : Reach 143795 := rs (se 1 (by rfl) ⟨107846, by rfl⟩) R215693
theorem R143819 : Reach 143819 := rs (se 1 (by rfl) ⟨107864, by rfl⟩) R215729
theorem R78337 : Reach 78337 := rs (se 2 (by rfl) ⟨29376, by rfl⟩) R58753
theorem R78401 : Reach 78401 := rs (se 2 (by rfl) ⟨29400, by rfl⟩) R58801
theorem R45643 : Reach 45643 := rs (se 1 (by rfl) ⟨34232, by rfl⟩) R68465
theorem R144017 : Reach 144017 := rs (se 2 (by rfl) ⟨54006, by rfl⟩) R108013
theorem R45751 : Reach 45751 := rs (se 1 (by rfl) ⟨34313, by rfl⟩) R68627
theorem R635633 : Reach 635633 := rs (se 2 (by rfl) ⟨238362, by rfl⟩) R476725
theorem R45815 : Reach 45815 := rs (se 1 (by rfl) ⟨34361, by rfl⟩) R68723
theorem R144179 : Reach 144179 := rs (se 1 (by rfl) ⟨108134, by rfl⟩) R216269
theorem R45931 : Reach 45931 := rs (se 1 (by rfl) ⟨34448, by rfl⟩) R68897
theorem R46039 : Reach 46039 := rs (se 1 (by rfl) ⟨34529, by rfl⟩) R69059
theorem R144449 : Reach 144449 := rs (se 2 (by rfl) ⟨54168, by rfl⟩) R108337
theorem R46219 : Reach 46219 := rs (se 1 (by rfl) ⟨34664, by rfl⟩) R69329
theorem R144557 : Reach 144557 := rs (se 3 (by rfl) ⟨27104, by rfl⟩) R54209
theorem R79051 : Reach 79051 := rs (se 1 (by rfl) ⟨59288, by rfl⟩) R118577
theorem R46327 : Reach 46327 := rs (se 1 (by rfl) ⟨34745, by rfl⟩) R69491
theorem R79127 : Reach 79127 := rs (se 1 (by rfl) ⟨59345, by rfl⟩) R118691
theorem R46615 : Reach 46615 := rs (se 1 (by rfl) ⟨34961, by rfl⟩) R69923
theorem R144989 : Reach 144989 := rs (se 3 (by rfl) ⟨27185, by rfl⟩) R54371
theorem R177815 : Reach 177815 := rs (se 1 (by rfl) ⟨133361, by rfl⟩) R266723
theorem R46795 : Reach 46795 := rs (se 1 (by rfl) ⟨35096, by rfl⟩) R70193
theorem R767843 : Reach 767843 := rs (se 1 (by rfl) ⟨575882, by rfl⟩) R1151765
theorem R112535 : Reach 112535 := rs (se 1 (by rfl) ⟨84401, by rfl⟩) R168803
theorem R79795 : Reach 79795 := rs (se 1 (by rfl) ⟨59846, by rfl⟩) R119693
theorem R79897 : Reach 79897 := rs (se 2 (by rfl) ⟨29961, by rfl⟩) R59923
theorem R47191 : Reach 47191 := rs (se 1 (by rfl) ⟨35393, by rfl⟩) R70787
theorem R79961 : Reach 79961 := rs (se 2 (by rfl) ⟨29985, by rfl⟩) R59971
theorem R47243 : Reach 47243 := rs (se 1 (by rfl) ⟨35432, by rfl⟩) R70865
theorem R80023 : Reach 80023 := rs (se 1 (by rfl) ⟨60017, by rfl⟩) R120035
theorem R80129 : Reach 80129 := rs (se 2 (by rfl) ⟨30048, by rfl⟩) R60097
theorem R47371 : Reach 47371 := rs (se 1 (by rfl) ⟨35528, by rfl⟩) R71057
theorem R112985 : Reach 112985 := rs (se 2 (by rfl) ⟨42369, by rfl⟩) R84739
theorem R80281 : Reach 80281 := rs (se 2 (by rfl) ⟨30105, by rfl⟩) R60211
theorem R80395 : Reach 80395 := rs (se 1 (by rfl) ⟨60296, by rfl⟩) R120593
theorem R47639 : Reach 47639 := rs (se 1 (by rfl) ⟨35729, by rfl⟩) R71459
theorem R47767 : Reach 47767 := rs (se 1 (by rfl) ⟨35825, by rfl⟩) R71651
theorem R211729 : Reach 211729 := rs (se 2 (by rfl) ⟨79398, by rfl⟩) R158797
theorem R47947 : Reach 47947 := rs (se 1 (by rfl) ⟨35960, by rfl⟩) R71921
theorem R80833 : Reach 80833 := rs (se 2 (by rfl) ⟨30312, by rfl⟩) R60625
theorem R48151 : Reach 48151 := rs (se 1 (by rfl) ⟨36113, by rfl⟩) R72227
theorem R113815 : Reach 113815 := rs (se 1 (by rfl) ⟨85361, by rfl⟩) R170723
theorem R48343 : Reach 48343 := rs (se 1 (by rfl) ⟨36257, by rfl⟩) R72515
theorem R179729 : Reach 179729 := rs (se 2 (by rfl) ⟨67398, by rfl⟩) R134797
theorem R81587 : Reach 81587 := rs (se 1 (by rfl) ⟨61190, by rfl⟩) R122381
theorem R147217 : Reach 147217 := rs (se 2 (by rfl) ⟨55206, by rfl⟩) R110413
theorem R81739 : Reach 81739 := rs (se 1 (by rfl) ⟨61304, by rfl⟩) R122609
theorem R212867 : Reach 212867 := rs (se 1 (by rfl) ⟨159650, by rfl⟩) R319301
theorem R114635 : Reach 114635 := rs (se 1 (by rfl) ⟨85976, by rfl⟩) R171953
theorem R147545 : Reach 147545 := rs (se 2 (by rfl) ⟨55329, by rfl⟩) R110659
theorem R180701 : Reach 180701 := rs (se 3 (by rfl) ⟨33881, by rfl⟩) R67763
theorem R443141 : Reach 443141 := rs (se 4 (by rfl) ⟨41544, by rfl⟩) R83089
theorem R213977 : Reach 213977 := rs (se 2 (by rfl) ⟨80241, by rfl⟩) R160483
theorem R115763 : Reach 115763 := rs (se 1 (by rfl) ⟨86822, by rfl⟩) R173645
theorem R148625 : Reach 148625 := rs (se 2 (by rfl) ⟨55734, by rfl⟩) R111469
theorem R312497 : Reach 312497 := rs (se 2 (by rfl) ⟨117186, by rfl⟩) R234373
theorem R50635 : Reach 50635 := rs (se 1 (by rfl) ⟨37976, by rfl⟩) R75953
theorem R476765 : Reach 476765 := rs (se 3 (by rfl) ⟨89393, by rfl⟩) R178787
theorem R83585 : Reach 83585 := rs (se 2 (by rfl) ⟨31344, by rfl⟩) R62689
theorem R149123 : Reach 149123 := rs (se 1 (by rfl) ⟨111842, by rfl⟩) R223685
theorem R312983 : Reach 312983 := rs (se 1 (by rfl) ⟨234737, by rfl⟩) R469475
theorem R149323 : Reach 149323 := rs (se 1 (by rfl) ⟨111992, by rfl⟩) R223985
theorem R509813 : Reach 509813 := rs (se 5 (by rfl) ⟨23897, by rfl⟩) R47795
theorem R182189 : Reach 182189 := rs (se 3 (by rfl) ⟨34160, by rfl⟩) R68321
theorem R968773 : Reach 968773 := rs (se 4 (by rfl) ⟨90822, by rfl⟩) R181645
theorem R149597 : Reach 149597 := rs (se 3 (by rfl) ⟨28049, by rfl⟩) R56099
theorem R247901 : Reach 247901 := rs (se 3 (by rfl) ⟨46481, by rfl⟩) R92963
theorem R706765 : Reach 706765 := rs (se 3 (by rfl) ⟨132518, by rfl⟩) R265037
theorem R117085 : Reach 117085 := rs (se 3 (by rfl) ⟨21953, by rfl⟩) R43907
theorem R51607 : Reach 51607 := rs (se 1 (by rfl) ⟨38705, by rfl⟩) R77411
theorem R84439 : Reach 84439 := rs (se 1 (by rfl) ⟨63329, by rfl⟩) R126659
theorem R182749 : Reach 182749 := rs (se 3 (by rfl) ⟨34265, by rfl⟩) R68531
theorem R84595 : Reach 84595 := rs (se 1 (by rfl) ⟨63446, by rfl⟩) R126893
theorem R150295 : Reach 150295 := rs (se 1 (by rfl) ⟨112721, by rfl⟩) R225443
theorem R52043 : Reach 52043 := rs (se 1 (by rfl) ⟨39032, by rfl⟩) R78065
theorem R150493 : Reach 150493 := rs (se 3 (by rfl) ⟨28217, by rfl⟩) R56435
theorem R52427 : Reach 52427 := rs (se 1 (by rfl) ⟨39320, by rfl⟩) R78641
theorem R85259 : Reach 85259 := rs (se 1 (by rfl) ⟨63944, by rfl⟩) R127889
theorem R281987 : Reach 281987 := rs (se 1 (by rfl) ⟨211490, by rfl⟩) R422981
theorem R347597 : Reach 347597 := rs (se 3 (by rfl) ⟨65174, by rfl⟩) R130349
theorem R216593 : Reach 216593 := rs (se 2 (by rfl) ⟨81222, by rfl⟩) R162445
theorem R151085 : Reach 151085 := rs (se 3 (by rfl) ⟨28328, by rfl⟩) R56657
theorem R249409 : Reach 249409 := rs (se 2 (by rfl) ⟨93528, by rfl⟩) R187057
theorem R347723 : Reach 347723 := rs (se 1 (by rfl) ⟨260792, by rfl⟩) R521585
theorem R118361 : Reach 118361 := rs (se 2 (by rfl) ⟨44385, by rfl⟩) R88771
theorem R85655 : Reach 85655 := rs (se 1 (by rfl) ⟨64241, by rfl⟩) R128483
theorem R216755 : Reach 216755 := rs (se 1 (by rfl) ⟨162566, by rfl⟩) R325133
theorem R282329 : Reach 282329 := rs (se 2 (by rfl) ⟨105873, by rfl⟩) R211747
theorem R151313 : Reach 151313 := rs (se 2 (by rfl) ⟨56742, by rfl⟩) R113485
theorem R184153 : Reach 184153 := rs (se 2 (by rfl) ⟨69057, by rfl⟩) R138115
theorem R53131 : Reach 53131 := rs (se 1 (by rfl) ⟨39848, by rfl⟩) R79697
theorem R53399 : Reach 53399 := rs (se 1 (by rfl) ⟨40049, by rfl⟩) R80099
theorem R185111 : Reach 185111 := rs (se 1 (by rfl) ⟨138833, by rfl⟩) R277667
theorem R873281 : Reach 873281 := rs (se 2 (by rfl) ⟨327480, by rfl⟩) R654961
theorem R54103 : Reach 54103 := rs (se 1 (by rfl) ⟨40577, by rfl⟩) R81155
theorem R152513 : Reach 152513 := rs (se 2 (by rfl) ⟨57192, by rfl⟩) R114385
theorem R54361 : Reach 54361 := rs (se 2 (by rfl) ⟨20385, by rfl⟩) R40771
theorem R218213 : Reach 218213 := rs (se 4 (by rfl) ⟨20457, by rfl⟩) R40915
theorem R120001 : Reach 120001 := rs (se 2 (by rfl) ⟨45000, by rfl⟩) R90001
theorem R1037717 : Reach 1037717 := rs (se 6 (by rfl) ⟨24321, by rfl⟩) R48643
theorem R87617 : Reach 87617 := rs (se 2 (by rfl) ⟨32856, by rfl⟩) R65713
theorem R120665 : Reach 120665 := rs (se 2 (by rfl) ⟨45249, by rfl⟩) R90499
theorem R87959 : Reach 87959 := rs (se 1 (by rfl) ⟨65969, by rfl⟩) R131939
theorem R88217 : Reach 88217 := rs (se 2 (by rfl) ⟨33081, by rfl⟩) R66163
theorem R88307 : Reach 88307 := rs (se 1 (by rfl) ⟨66230, by rfl⟩) R132461
theorem R88343 : Reach 88343 := rs (se 1 (by rfl) ⟨66257, by rfl⟩) R132515
theorem R154001 : Reach 154001 := rs (se 2 (by rfl) ⟨57750, by rfl⟩) R115501
theorem R88523 : Reach 88523 := rs (se 1 (by rfl) ⟨66392, by rfl⟩) R132785
theorem R88577 : Reach 88577 := rs (se 2 (by rfl) ⟨33216, by rfl⟩) R66433
theorem R285389 : Reach 285389 := rs (se 3 (by rfl) ⟨53510, by rfl⟩) R107021
theorem R88793 : Reach 88793 := rs (se 2 (by rfl) ⟨33297, by rfl⟩) R66595
theorem R88883 : Reach 88883 := rs (se 1 (by rfl) ⟨66662, by rfl⟩) R133325
theorem R1334069 : Reach 1334069 := rs (se 5 (by rfl) ⟨62534, by rfl⟩) R125069
theorem R121675 : Reach 121675 := rs (se 1 (by rfl) ⟨91256, by rfl⟩) R182513
theorem R88919 : Reach 88919 := rs (se 1 (by rfl) ⟨66689, by rfl⟩) R133379
theorem R154457 : Reach 154457 := rs (se 2 (by rfl) ⟨57921, by rfl⟩) R115843
theorem R89099 : Reach 89099 := rs (se 1 (by rfl) ⟨66824, by rfl⟩) R133649
theorem R89113 : Reach 89113 := rs (se 2 (by rfl) ⟨33417, by rfl⟩) R66835
theorem R154669 : Reach 154669 := rs (se 3 (by rfl) ⟨29000, by rfl⟩) R58001
theorem R89153 : Reach 89153 := rs (se 2 (by rfl) ⟨33432, by rfl⟩) R66865
theorem R121931 : Reach 121931 := rs (se 1 (by rfl) ⟨91448, by rfl⟩) R182897
theorem R121949 : Reach 121949 := rs (se 3 (by rfl) ⟨22865, by rfl⟩) R45731
theorem R89369 : Reach 89369 := rs (se 2 (by rfl) ⟨33513, by rfl⟩) R67027
theorem R154973 : Reach 154973 := rs (se 3 (by rfl) ⟨29057, by rfl⟩) R58115
theorem R89459 : Reach 89459 := rs (se 1 (by rfl) ⟨67094, by rfl⟩) R134189
theorem R89495 : Reach 89495 := rs (se 1 (by rfl) ⟨67121, by rfl⟩) R134243
theorem R56857 : Reach 56857 := rs (se 2 (by rfl) ⟨21321, by rfl⟩) R42643
theorem R286253 : Reach 286253 := rs (se 3 (by rfl) ⟨53672, by rfl⟩) R107345
theorem R89675 : Reach 89675 := rs (se 1 (by rfl) ⟨67256, by rfl⟩) R134513
theorem R89729 : Reach 89729 := rs (se 2 (by rfl) ⟨33648, by rfl⟩) R67297
theorem R155267 : Reach 155267 := rs (se 1 (by rfl) ⟨116450, by rfl⟩) R232901
theorem R89945 : Reach 89945 := rs (se 2 (by rfl) ⟨33729, by rfl⟩) R67459
theorem R450481 : Reach 450481 := rs (se 2 (by rfl) ⟨168930, by rfl⟩) R337861
theorem R90035 : Reach 90035 := rs (se 1 (by rfl) ⟨67526, by rfl⟩) R135053
theorem R90071 : Reach 90071 := rs (se 1 (by rfl) ⟨67553, by rfl⟩) R135107
theorem R450521 : Reach 450521 := rs (se 2 (by rfl) ⟨168945, by rfl⟩) R337891
theorem R57305 : Reach 57305 := rs (se 2 (by rfl) ⟨21489, by rfl⟩) R42979
theorem R90163 : Reach 90163 := rs (se 1 (by rfl) ⟨67622, by rfl⟩) R135245
theorem R352349 : Reach 352349 := rs (se 3 (by rfl) ⟨66065, by rfl⟩) R132131
theorem R90251 : Reach 90251 := rs (se 1 (by rfl) ⟨67688, by rfl⟩) R135377
theorem R90305 : Reach 90305 := rs (se 2 (by rfl) ⟨33864, by rfl⟩) R67729
theorem R90391 : Reach 90391 := rs (se 1 (by rfl) ⟨67793, by rfl⟩) R135587
theorem R450917 : Reach 450917 := rs (se 4 (by rfl) ⟨42273, by rfl⟩) R84547
theorem R680293 : Reach 680293 := rs (se 4 (by rfl) ⟨63777, by rfl⟩) R127555
theorem R90497 : Reach 90497 := rs (se 2 (by rfl) ⟨33936, by rfl⟩) R67873
theorem R90521 : Reach 90521 := rs (se 2 (by rfl) ⟨33945, by rfl⟩) R67891
theorem R90611 : Reach 90611 := rs (se 1 (by rfl) ⟨67958, by rfl⟩) R135917
theorem R90647 : Reach 90647 := rs (se 1 (by rfl) ⟨67985, by rfl⟩) R135971
theorem R58009 : Reach 58009 := rs (se 2 (by rfl) ⟨21753, by rfl⟩) R43507
theorem R90827 : Reach 90827 := rs (se 1 (by rfl) ⟨68120, by rfl⟩) R136241
theorem R90881 : Reach 90881 := rs (se 2 (by rfl) ⟨34080, by rfl⟩) R68161
theorem R320273 : Reach 320273 := rs (se 2 (by rfl) ⟨120102, by rfl⟩) R240205
theorem R58315 : Reach 58315 := rs (se 1 (by rfl) ⟨43736, by rfl⟩) R87473
theorem R91097 : Reach 91097 := rs (se 2 (by rfl) ⟨34161, by rfl⟩) R68323
theorem R91187 : Reach 91187 := rs (se 1 (by rfl) ⟨68390, by rfl⟩) R136781
theorem R91223 : Reach 91223 := rs (se 1 (by rfl) ⟨68417, by rfl⟩) R136835
theorem R91403 : Reach 91403 := rs (se 1 (by rfl) ⟨68552, by rfl⟩) R137105
theorem R91457 : Reach 91457 := rs (se 2 (by rfl) ⟨34296, by rfl⟩) R68593
theorem R58763 : Reach 58763 := rs (se 1 (by rfl) ⟨44072, by rfl⟩) R88145
theorem R58775 : Reach 58775 := rs (se 1 (by rfl) ⟨44081, by rfl⟩) R88163
theorem R124363 : Reach 124363 := rs (se 1 (by rfl) ⟨93272, by rfl⟩) R186545
theorem R58841 : Reach 58841 := rs (se 2 (by rfl) ⟨22065, by rfl⟩) R44131
theorem R91649 : Reach 91649 := rs (se 2 (by rfl) ⟨34368, by rfl⟩) R68737
theorem R91673 : Reach 91673 := rs (se 2 (by rfl) ⟨34377, by rfl⟩) R68755
theorem R58955 : Reach 58955 := rs (se 1 (by rfl) ⟨44216, by rfl⟩) R88433
theorem R58967 : Reach 58967 := rs (se 1 (by rfl) ⟨44225, by rfl⟩) R88451
theorem R157277 : Reach 157277 := rs (se 3 (by rfl) ⟨29489, by rfl⟩) R58979
theorem R91763 : Reach 91763 := rs (se 1 (by rfl) ⟨68822, by rfl⟩) R137645
theorem R91799 : Reach 91799 := rs (se 1 (by rfl) ⟨68849, by rfl⟩) R137699
theorem R59033 : Reach 59033 := rs (se 2 (by rfl) ⟨22137, by rfl⟩) R44275
theorem R59147 : Reach 59147 := rs (se 1 (by rfl) ⟨44360, by rfl⟩) R88721
theorem R59159 : Reach 59159 := rs (se 1 (by rfl) ⟨44369, by rfl⟩) R88739
theorem R91979 : Reach 91979 := rs (se 1 (by rfl) ⟨68984, by rfl⟩) R137969
theorem R91991 : Reach 91991 := rs (se 1 (by rfl) ⟨68993, by rfl⟩) R137987
theorem R59225 : Reach 59225 := rs (se 2 (by rfl) ⟨22209, by rfl⟩) R44419
theorem R92033 : Reach 92033 := rs (se 2 (by rfl) ⟨34512, by rfl⟩) R69025
theorem R157571 : Reach 157571 := rs (se 1 (by rfl) ⟨118178, by rfl⟩) R236357
theorem R157585 : Reach 157585 := rs (se 2 (by rfl) ⟨59094, by rfl⟩) R118189
theorem R59339 : Reach 59339 := rs (se 1 (by rfl) ⟨44504, by rfl⟩) R89009
theorem R59351 : Reach 59351 := rs (se 1 (by rfl) ⟨44513, by rfl⟩) R89027
theorem R59417 : Reach 59417 := rs (se 2 (by rfl) ⟨22281, by rfl⟩) R44563
theorem R92249 : Reach 92249 := rs (se 2 (by rfl) ⟨34593, by rfl⟩) R69187
theorem R59531 : Reach 59531 := rs (se 1 (by rfl) ⟨44648, by rfl⟩) R89297
theorem R59543 : Reach 59543 := rs (se 1 (by rfl) ⟨44657, by rfl⟩) R89315
theorem R59545 : Reach 59545 := rs (se 2 (by rfl) ⟨22329, by rfl⟩) R44659
theorem R92339 : Reach 92339 := rs (se 1 (by rfl) ⟨69254, by rfl⟩) R138509
theorem R157889 : Reach 157889 := rs (se 2 (by rfl) ⟨59208, by rfl⟩) R118417
theorem R92375 : Reach 92375 := rs (se 1 (by rfl) ⟨69281, by rfl⟩) R138563
theorem R59609 : Reach 59609 := rs (se 2 (by rfl) ⟨22353, by rfl⟩) R44707
theorem R59723 : Reach 59723 := rs (se 1 (by rfl) ⟨44792, by rfl⟩) R89585
theorem R59735 : Reach 59735 := rs (se 1 (by rfl) ⟨44801, by rfl⟩) R89603
theorem R92555 : Reach 92555 := rs (se 1 (by rfl) ⟨69416, by rfl⟩) R138833
theorem R59801 : Reach 59801 := rs (se 2 (by rfl) ⟨22425, by rfl⟩) R44851
theorem R223667 : Reach 223667 := rs (se 1 (by rfl) ⟨167750, by rfl⟩) R335501
theorem R92609 : Reach 92609 := rs (se 2 (by rfl) ⟨34728, by rfl⟩) R69457
theorem R59915 : Reach 59915 := rs (se 1 (by rfl) ⟨44936, by rfl⟩) R89873
theorem R59927 : Reach 59927 := rs (se 1 (by rfl) ⟨44945, by rfl⟩) R89891
theorem R59993 : Reach 59993 := rs (se 2 (by rfl) ⟨22497, by rfl⟩) R44995
theorem R60107 : Reach 60107 := rs (se 1 (by rfl) ⟨45080, by rfl⟩) R90161
theorem R60119 : Reach 60119 := rs (se 1 (by rfl) ⟨45089, by rfl⟩) R90179
theorem R92951 : Reach 92951 := rs (se 1 (by rfl) ⟨69713, by rfl⟩) R139427
theorem R60185 : Reach 60185 := rs (se 2 (by rfl) ⟨22569, by rfl⟩) R45139
theorem R158557 : Reach 158557 := rs (se 3 (by rfl) ⟨29729, by rfl⟩) R59459
theorem R60299 : Reach 60299 := rs (se 1 (by rfl) ⟨45224, by rfl⟩) R90449
theorem R60311 : Reach 60311 := rs (se 1 (by rfl) ⟨45233, by rfl⟩) R90467
theorem R322483 : Reach 322483 := rs (se 1 (by rfl) ⟨241862, by rfl⟩) R483725
theorem R93131 : Reach 93131 := rs (se 1 (by rfl) ⟨69848, by rfl⟩) R139697
theorem R60377 : Reach 60377 := rs (se 2 (by rfl) ⟨22641, by rfl⟩) R45283
theorem R60439 : Reach 60439 := rs (se 1 (by rfl) ⟨45329, by rfl⟩) R90659
theorem R60491 : Reach 60491 := rs (se 1 (by rfl) ⟨45368, by rfl⟩) R90737
theorem R60503 : Reach 60503 := rs (se 1 (by rfl) ⟨45377, by rfl⟩) R90755
theorem R60569 : Reach 60569 := rs (se 2 (by rfl) ⟨22713, by rfl⟩) R45427
theorem R93401 : Reach 93401 := rs (se 2 (by rfl) ⟨35025, by rfl⟩) R70051
theorem R60683 : Reach 60683 := rs (se 1 (by rfl) ⟨45512, by rfl⟩) R91025
theorem R60695 : Reach 60695 := rs (se 1 (by rfl) ⟨45521, by rfl⟩) R91043
theorem R93491 : Reach 93491 := rs (se 1 (by rfl) ⟨70118, by rfl⟩) R140237
theorem R60761 : Reach 60761 := rs (se 2 (by rfl) ⟨22785, by rfl⟩) R45571
theorem R617827 : Reach 617827 := rs (se 1 (by rfl) ⟨463370, by rfl⟩) R926741
theorem R60875 : Reach 60875 := rs (se 1 (by rfl) ⟨45656, by rfl⟩) R91313
theorem R60887 : Reach 60887 := rs (se 1 (by rfl) ⟨45665, by rfl⟩) R91331
theorem R650713 : Reach 650713 := rs (se 2 (by rfl) ⟨244017, by rfl⟩) R488035
theorem R60953 : Reach 60953 := rs (se 2 (by rfl) ⟨22857, by rfl⟩) R45715
theorem R93761 : Reach 93761 := rs (se 2 (by rfl) ⟨35160, by rfl⟩) R70321
theorem R61003 : Reach 61003 := rs (se 1 (by rfl) ⟨45752, by rfl⟩) R91505
theorem R388739 : Reach 388739 := rs (se 1 (by rfl) ⟨291554, by rfl⟩) R583109
theorem R61067 : Reach 61067 := rs (se 1 (by rfl) ⟨45800, by rfl⟩) R91601
theorem R61079 : Reach 61079 := rs (se 1 (by rfl) ⟨45809, by rfl⟩) R91619
theorem R61145 : Reach 61145 := rs (se 2 (by rfl) ⟨22929, by rfl⟩) R45859
theorem R61259 : Reach 61259 := rs (se 1 (by rfl) ⟨45944, by rfl⟩) R91889
theorem R61271 : Reach 61271 := rs (se 1 (by rfl) ⟨45953, by rfl⟩) R91907
theorem R225125 : Reach 225125 := rs (se 4 (by rfl) ⟨21105, by rfl⟩) R42211
theorem R94103 : Reach 94103 := rs (se 1 (by rfl) ⟨70577, by rfl⟩) R141155
theorem R61337 : Reach 61337 := rs (se 2 (by rfl) ⟨23001, by rfl⟩) R46003
theorem R61451 : Reach 61451 := rs (se 1 (by rfl) ⟨46088, by rfl⟩) R92177
theorem R61463 : Reach 61463 := rs (se 1 (by rfl) ⟨46097, by rfl⟩) R92195
theorem R94283 : Reach 94283 := rs (se 1 (by rfl) ⟨70712, by rfl⟩) R141425
theorem R61529 : Reach 61529 := rs (se 2 (by rfl) ⟨23073, by rfl⟩) R46147
theorem R159833 : Reach 159833 := rs (se 2 (by rfl) ⟨59937, by rfl⟩) R119875
theorem R61643 : Reach 61643 := rs (se 1 (by rfl) ⟨46232, by rfl⟩) R92465
theorem R61655 : Reach 61655 := rs (se 1 (by rfl) ⟨46241, by rfl⟩) R92483
theorem R61721 : Reach 61721 := rs (se 2 (by rfl) ⟨23145, by rfl⟩) R46291
theorem R192833 : Reach 192833 := rs (se 2 (by rfl) ⟨72312, by rfl⟩) R144625
theorem R94553 : Reach 94553 := rs (se 2 (by rfl) ⟨35457, by rfl⟩) R70915
theorem R127325 : Reach 127325 := rs (se 3 (by rfl) ⟨23873, by rfl⟩) R47747
theorem R61835 : Reach 61835 := rs (se 1 (by rfl) ⟨46376, by rfl⟩) R92753
theorem R61847 : Reach 61847 := rs (se 1 (by rfl) ⟨46385, by rfl⟩) R92771
theorem R94643 : Reach 94643 := rs (se 1 (by rfl) ⟨70982, by rfl⟩) R141965
theorem R61913 : Reach 61913 := rs (se 2 (by rfl) ⟨23217, by rfl⟩) R46435
theorem R324161 : Reach 324161 := rs (se 2 (by rfl) ⟨121560, by rfl⟩) R243121
theorem R62027 : Reach 62027 := rs (se 1 (by rfl) ⟨46520, by rfl⟩) R93041
theorem R62039 : Reach 62039 := rs (se 1 (by rfl) ⟨46529, by rfl⟩) R93059
theorem R62105 : Reach 62105 := rs (se 2 (by rfl) ⟨23289, by rfl⟩) R46579
theorem R94913 : Reach 94913 := rs (se 2 (by rfl) ⟨35592, by rfl⟩) R71185
theorem R62219 : Reach 62219 := rs (se 1 (by rfl) ⟨46664, by rfl⟩) R93329
theorem R62231 : Reach 62231 := rs (se 1 (by rfl) ⟨46673, by rfl⟩) R93347
theorem R62297 : Reach 62297 := rs (se 2 (by rfl) ⟨23361, by rfl⟩) R46723
theorem R193373 : Reach 193373 := rs (se 3 (by rfl) ⟨36257, by rfl⟩) R72515
theorem R291761 : Reach 291761 := rs (se 2 (by rfl) ⟨109410, by rfl⟩) R218821
theorem R62411 : Reach 62411 := rs (se 1 (by rfl) ⟨46808, by rfl⟩) R93617
theorem R62423 : Reach 62423 := rs (se 1 (by rfl) ⟨46817, by rfl⟩) R93635
theorem R95255 : Reach 95255 := rs (se 1 (by rfl) ⟨71441, by rfl⟩) R142883
theorem R62489 : Reach 62489 := rs (se 2 (by rfl) ⟨23433, by rfl⟩) R46867
theorem R62603 : Reach 62603 := rs (se 1 (by rfl) ⟨46952, by rfl⟩) R93905
theorem R62615 : Reach 62615 := rs (se 1 (by rfl) ⟨46961, by rfl⟩) R93923
theorem R95435 : Reach 95435 := rs (se 1 (by rfl) ⟨71576, by rfl⟩) R143153
theorem R62681 : Reach 62681 := rs (se 2 (by rfl) ⟨23505, by rfl⟩) R47011
theorem R62795 : Reach 62795 := rs (se 1 (by rfl) ⟨47096, by rfl⟩) R94193
theorem R62807 : Reach 62807 := rs (se 1 (by rfl) ⟨47105, by rfl⟩) R94211
theorem R62873 : Reach 62873 := rs (se 2 (by rfl) ⟨23577, by rfl⟩) R47155
theorem R95705 : Reach 95705 := rs (se 2 (by rfl) ⟨35889, by rfl⟩) R71779
theorem R62987 : Reach 62987 := rs (se 1 (by rfl) ⟨47240, by rfl⟩) R94481
theorem R62999 : Reach 62999 := rs (se 1 (by rfl) ⟨47249, by rfl⟩) R94499
theorem R95795 : Reach 95795 := rs (se 1 (by rfl) ⟨71846, by rfl⟩) R143693
theorem R63065 : Reach 63065 := rs (se 2 (by rfl) ⟨23649, by rfl⟩) R47299
theorem R161459 : Reach 161459 := rs (se 1 (by rfl) ⟨121094, by rfl⟩) R242189
theorem R161473 : Reach 161473 := rs (se 2 (by rfl) ⟨60552, by rfl⟩) R121105
theorem R63179 : Reach 63179 := rs (se 1 (by rfl) ⟨47384, by rfl⟩) R94769
theorem R63191 : Reach 63191 := rs (se 1 (by rfl) ⟨47393, by rfl⟩) R94787
theorem R96023 : Reach 96023 := rs (se 1 (by rfl) ⟨72017, by rfl⟩) R144035
theorem R63257 : Reach 63257 := rs (se 2 (by rfl) ⟨23721, by rfl⟩) R47443
theorem R96065 : Reach 96065 := rs (se 2 (by rfl) ⟨36024, by rfl⟩) R72049
theorem R292709 : Reach 292709 := rs (se 4 (by rfl) ⟨27441, by rfl⟩) R54883
theorem R63371 : Reach 63371 := rs (se 1 (by rfl) ⟨47528, by rfl⟩) R95057
theorem R63383 : Reach 63383 := rs (se 1 (by rfl) ⟨47537, by rfl⟩) R95075
theorem R63449 : Reach 63449 := rs (se 2 (by rfl) ⟨23793, by rfl⟩) R47587
theorem R96331 : Reach 96331 := rs (se 1 (by rfl) ⟨72248, by rfl⟩) R144497
theorem R63563 : Reach 63563 := rs (se 1 (by rfl) ⟨47672, by rfl⟩) R95345
theorem R63575 : Reach 63575 := rs (se 1 (by rfl) ⟨47681, by rfl⟩) R95363
theorem R96407 : Reach 96407 := rs (se 1 (by rfl) ⟨72305, by rfl⟩) R144611
theorem R63641 : Reach 63641 := rs (se 2 (by rfl) ⟨23865, by rfl⟩) R47731
theorem R63755 : Reach 63755 := rs (se 1 (by rfl) ⟨47816, by rfl⟩) R95633
theorem R63767 : Reach 63767 := rs (se 1 (by rfl) ⟨47825, by rfl⟩) R95651
theorem R96587 : Reach 96587 := rs (se 1 (by rfl) ⟨72440, by rfl⟩) R144881
theorem R63833 : Reach 63833 := rs (se 2 (by rfl) ⟨23937, by rfl⟩) R47875
theorem R63947 : Reach 63947 := rs (se 1 (by rfl) ⟨47960, by rfl⟩) R95921
theorem R63959 : Reach 63959 := rs (se 1 (by rfl) ⟨47969, by rfl⟩) R95939
theorem R326105 : Reach 326105 := rs (se 2 (by rfl) ⟨122289, by rfl⟩) R244579
theorem R64025 : Reach 64025 := rs (se 2 (by rfl) ⟨24009, by rfl⟩) R48019
theorem R96857 : Reach 96857 := rs (se 2 (by rfl) ⟨36321, by rfl⟩) R72643
theorem R64139 : Reach 64139 := rs (se 1 (by rfl) ⟨48104, by rfl⟩) R96209
theorem R64151 : Reach 64151 := rs (se 1 (by rfl) ⟨48113, by rfl⟩) R96227
theorem R96947 : Reach 96947 := rs (se 1 (by rfl) ⟨72710, by rfl⟩) R145421
theorem R359129 : Reach 359129 := rs (se 2 (by rfl) ⟨134673, by rfl⟩) R269347
theorem R64217 : Reach 64217 := rs (se 2 (by rfl) ⟨24081, by rfl⟩) R48163
theorem R64331 : Reach 64331 := rs (se 1 (by rfl) ⟨48248, by rfl⟩) R96497
theorem R64343 : Reach 64343 := rs (se 1 (by rfl) ⟨48257, by rfl⟩) R96515
theorem R64409 : Reach 64409 := rs (se 2 (by rfl) ⟨24153, by rfl⟩) R48307
theorem R64523 : Reach 64523 := rs (se 1 (by rfl) ⟨48392, by rfl⟩) R96785
theorem R64535 : Reach 64535 := rs (se 1 (by rfl) ⟨48401, by rfl⟩) R96803
theorem R64601 : Reach 64601 := rs (se 2 (by rfl) ⟨24225, by rfl⟩) R48451
theorem R163403 : Reach 163403 := rs (se 1 (by rfl) ⟨122552, by rfl⟩) R245105
theorem R163417 : Reach 163417 := rs (se 2 (by rfl) ⟨61281, by rfl⟩) R122563
theorem R65303 : Reach 65303 := rs (se 1 (by rfl) ⟨48977, by rfl⟩) R97955
theorem R294835 : Reach 294835 := rs (se 1 (by rfl) ⟨221126, by rfl⟩) R442253
theorem R1343411 : Reach 1343411 := rs (se 1 (by rfl) ⟨1007558, by rfl⟩) R2015117
theorem R98363 : Reach 98363 := rs (se 1 (by rfl) ⟨73772, by rfl⟩) R147545
theorem R131387 : Reach 131387 := rs (se 1 (by rfl) ⟨98540, by rfl⟩) R197081
theorem R229817 : Reach 229817 := rs (se 2 (by rfl) ⟨86181, by rfl⟩) R172363
theorem R295427 : Reach 295427 := rs (se 1 (by rfl) ⟨221570, by rfl⟩) R443141
theorem R99083 : Reach 99083 := rs (se 1 (by rfl) ⟨74312, by rfl⟩) R148625
theorem R66575 : Reach 66575 := rs (se 1 (by rfl) ⟨49931, by rfl⟩) R99863
theorem R99415 : Reach 99415 := rs (se 1 (by rfl) ⟨74561, by rfl⟩) R149123
theorem R132353 : Reach 132353 := rs (se 2 (by rfl) ⟨49632, by rfl⟩) R99265
theorem R99731 : Reach 99731 := rs (se 1 (by rfl) ⟨74798, by rfl⟩) R149597
theorem R67115 : Reach 67115 := rs (se 1 (by rfl) ⟨50336, by rfl⟩) R100673
theorem R886373 : Reach 886373 := rs (se 4 (by rfl) ⟨83097, by rfl⟩) R166195
theorem R100025 : Reach 100025 := rs (se 2 (by rfl) ⟨37509, by rfl⟩) R75019
theorem R67513 : Reach 67513 := rs (se 2 (by rfl) ⟨25317, by rfl⟩) R50635
theorem R165817 : Reach 165817 := rs (se 2 (by rfl) ⟨62181, by rfl⟩) R124363
theorem R133163 : Reach 133163 := rs (se 1 (by rfl) ⟨99872, by rfl⟩) R199745
theorem R231731 : Reach 231731 := rs (se 1 (by rfl) ⟨173798, by rfl⟩) R347597
theorem R100723 : Reach 100723 := rs (se 1 (by rfl) ⟨75542, by rfl⟩) R151085
theorem R231815 : Reach 231815 := rs (se 1 (by rfl) ⟨173861, by rfl⟩) R347723
theorem R199097 : Reach 199097 := rs (se 2 (by rfl) ⟨74661, by rfl⟩) R149323
theorem R100865 : Reach 100865 := rs (se 2 (by rfl) ⟨37824, by rfl⟩) R75649
theorem R68215 : Reach 68215 := rs (se 1 (by rfl) ⟨51161, by rfl⟩) R102323
theorem R428773 : Reach 428773 := rs (se 4 (by rfl) ⟨40197, by rfl⟩) R80395
theorem R68411 : Reach 68411 := rs (se 1 (by rfl) ⟨51308, by rfl⟩) R102617
theorem R101321 : Reach 101321 := rs (se 2 (by rfl) ⟨37995, by rfl⟩) R75991
theorem R68809 : Reach 68809 := rs (se 2 (by rfl) ⟨25803, by rfl⟩) R51607
theorem R363809 : Reach 363809 := rs (se 2 (by rfl) ⟨136428, by rfl⟩) R272857
theorem R101665 : Reach 101665 := rs (se 2 (by rfl) ⟨38124, by rfl⟩) R76249
theorem R101675 : Reach 101675 := rs (se 1 (by rfl) ⟨76256, by rfl⟩) R152513
theorem R134459 : Reach 134459 := rs (se 1 (by rfl) ⟨100844, by rfl⟩) R201689
theorem R265619 : Reach 265619 := rs (se 1 (by rfl) ⟨199214, by rfl⟩) R398429
theorem R691811 : Reach 691811 := rs (se 1 (by rfl) ⟨518858, by rfl⟩) R1037717
theorem R200393 : Reach 200393 := rs (se 2 (by rfl) ⟨75147, by rfl⟩) R150295
theorem R233189 : Reach 233189 := rs (se 4 (by rfl) ⟨21861, by rfl⟩) R43723
theorem R134945 : Reach 134945 := rs (se 2 (by rfl) ⟨50604, by rfl⟩) R101209
theorem R69511 : Reach 69511 := rs (se 1 (by rfl) ⟨52133, by rfl⟩) R104267
theorem R429977 : Reach 429977 := rs (se 2 (by rfl) ⟨161241, by rfl⟩) R322483
theorem R102329 : Reach 102329 := rs (se 2 (by rfl) ⟨38373, by rfl⟩) R76747
theorem R200657 : Reach 200657 := rs (se 2 (by rfl) ⟨75246, by rfl⟩) R150493
theorem R102667 : Reach 102667 := rs (se 1 (by rfl) ⟨77000, by rfl⟩) R154001
theorem R135539 : Reach 135539 := rs (se 1 (by rfl) ⟨101654, by rfl⟩) R203309
theorem R233873 : Reach 233873 := rs (se 2 (by rfl) ⟨87702, by rfl⟩) R175405
theorem R102809 : Reach 102809 := rs (se 2 (by rfl) ⟨38553, by rfl⟩) R77107
theorem R823769 : Reach 823769 := rs (se 2 (by rfl) ⟨308913, by rfl⟩) R617827
theorem R70159 : Reach 70159 := rs (se 1 (by rfl) ⟨52619, by rfl⟩) R105239
theorem R889379 : Reach 889379 := rs (se 1 (by rfl) ⟨667034, by rfl⟩) R1334069
theorem R102971 : Reach 102971 := rs (se 1 (by rfl) ⟨77228, by rfl⟩) R154457
theorem R332545 : Reach 332545 := rs (se 2 (by rfl) ⟨124704, by rfl⟩) R249409
theorem R103315 : Reach 103315 := rs (se 1 (by rfl) ⟨77486, by rfl⟩) R154973
theorem R332747 : Reach 332747 := rs (se 1 (by rfl) ⟨249560, by rfl⟩) R499121
theorem R103457 : Reach 103457 := rs (se 2 (by rfl) ⟨38796, by rfl⟩) R77593
theorem R70699 : Reach 70699 := rs (se 1 (by rfl) ⟨53024, by rfl⟩) R106049
theorem R103511 : Reach 103511 := rs (se 1 (by rfl) ⟨77633, by rfl⟩) R155267
theorem R70841 : Reach 70841 := rs (se 2 (by rfl) ⟨26565, by rfl⟩) R53131
theorem R300347 : Reach 300347 := rs (se 1 (by rfl) ⟨225260, by rfl⟩) R450521
theorem R234899 : Reach 234899 := rs (se 1 (by rfl) ⟨176174, by rfl⟩) R352349
theorem R300611 : Reach 300611 := rs (se 1 (by rfl) ⟨225458, by rfl⟩) R450917
theorem R661069 : Reach 661069 := rs (se 3 (by rfl) ⟨123950, by rfl⟩) R247901
theorem R71543 : Reach 71543 := rs (se 1 (by rfl) ⟨53657, by rfl⟩) R107315
theorem R104449 : Reach 104449 := rs (se 2 (by rfl) ⟨39168, by rfl⟩) R78337
theorem R39175 : Reach 39175 := rs (se 1 (by rfl) ⟨29381, by rfl⟩) R58763
theorem R39183 : Reach 39183 := rs (se 1 (by rfl) ⟨29387, by rfl⟩) R58775
theorem R39227 : Reach 39227 := rs (se 1 (by rfl) ⟨29420, by rfl⟩) R58841
theorem R71995 : Reach 71995 := rs (se 1 (by rfl) ⟨53996, by rfl⟩) R107993
theorem R39303 : Reach 39303 := rs (se 1 (by rfl) ⟨29477, by rfl⟩) R58955
theorem R39311 : Reach 39311 := rs (se 1 (by rfl) ⟨29483, by rfl⟩) R58967
theorem R72083 : Reach 72083 := rs (se 1 (by rfl) ⟨54062, by rfl⟩) R108125
theorem R104851 : Reach 104851 := rs (se 1 (by rfl) ⟨78638, by rfl⟩) R157277
theorem R39355 : Reach 39355 := rs (se 1 (by rfl) ⟨29516, by rfl⟩) R59033
theorem R72137 : Reach 72137 := rs (se 2 (by rfl) ⟨27051, by rfl⟩) R54103
theorem R39431 : Reach 39431 := rs (se 1 (by rfl) ⟨29573, by rfl⟩) R59147
theorem R39439 : Reach 39439 := rs (se 1 (by rfl) ⟨29579, by rfl⟩) R59159
theorem R170525 : Reach 170525 := rs (se 3 (by rfl) ⟨31973, by rfl⟩) R63947
theorem R137771 : Reach 137771 := rs (se 1 (by rfl) ⟨103328, by rfl⟩) R206657
theorem R39483 : Reach 39483 := rs (se 1 (by rfl) ⟨29612, by rfl⟩) R59225
theorem R105047 : Reach 105047 := rs (se 1 (by rfl) ⟨78785, by rfl⟩) R157571
theorem R39559 : Reach 39559 := rs (se 1 (by rfl) ⟨29669, by rfl⟩) R59339
theorem R39567 : Reach 39567 := rs (se 1 (by rfl) ⟨29675, by rfl⟩) R59351
theorem R39611 : Reach 39611 := rs (se 1 (by rfl) ⟨29708, by rfl⟩) R59417
theorem R39687 : Reach 39687 := rs (se 1 (by rfl) ⟨29765, by rfl⟩) R59531
theorem R39695 : Reach 39695 := rs (se 1 (by rfl) ⟨29771, by rfl⟩) R59543
theorem R72481 : Reach 72481 := rs (se 2 (by rfl) ⟨27180, by rfl⟩) R54361
theorem R105259 : Reach 105259 := rs (se 1 (by rfl) ⟨78944, by rfl⟩) R157889
theorem R39739 : Reach 39739 := rs (se 1 (by rfl) ⟨29804, by rfl⟩) R59609
theorem R39815 : Reach 39815 := rs (se 1 (by rfl) ⟨29861, by rfl⟩) R59723
theorem R39823 : Reach 39823 := rs (se 1 (by rfl) ⟨29867, by rfl⟩) R59735
theorem R138131 : Reach 138131 := rs (se 1 (by rfl) ⟨103598, by rfl⟩) R207197
theorem R105401 : Reach 105401 := rs (se 2 (by rfl) ⟨39525, by rfl⟩) R79051
theorem R39867 : Reach 39867 := rs (se 1 (by rfl) ⟨29900, by rfl⟩) R59801
theorem R39943 : Reach 39943 := rs (se 1 (by rfl) ⟨29957, by rfl⟩) R59915
theorem R39951 : Reach 39951 := rs (se 1 (by rfl) ⟨29963, by rfl⟩) R59927
theorem R39995 : Reach 39995 := rs (se 1 (by rfl) ⟨29996, by rfl⟩) R59993
theorem R105533 : Reach 105533 := rs (se 3 (by rfl) ⟨19787, by rfl⟩) R39575
theorem R40071 : Reach 40071 := rs (se 1 (by rfl) ⟨30053, by rfl⟩) R60107
theorem R40079 : Reach 40079 := rs (se 1 (by rfl) ⟨30059, by rfl⟩) R60119
theorem R40123 : Reach 40123 := rs (se 1 (by rfl) ⟨30092, by rfl⟩) R60185
theorem R40199 : Reach 40199 := rs (se 1 (by rfl) ⟨30149, by rfl⟩) R60299
theorem R40207 : Reach 40207 := rs (se 1 (by rfl) ⟨30155, by rfl⟩) R60311
theorem R40251 : Reach 40251 := rs (se 1 (by rfl) ⟨30188, by rfl⟩) R60377
theorem R40327 : Reach 40327 := rs (se 1 (by rfl) ⟨30245, by rfl⟩) R60491
theorem R40335 : Reach 40335 := rs (se 1 (by rfl) ⟨30251, by rfl⟩) R60503
theorem R40379 : Reach 40379 := rs (se 1 (by rfl) ⟨30284, by rfl⟩) R60569
theorem R1121795 : Reach 1121795 := rs (se 1 (by rfl) ⟨841346, by rfl⟩) R1682693
theorem R40455 : Reach 40455 := rs (se 1 (by rfl) ⟨30341, by rfl⟩) R60683
theorem R40463 : Reach 40463 := rs (se 1 (by rfl) ⟨30347, by rfl⟩) R60695
theorem R138781 : Reach 138781 := rs (se 3 (by rfl) ⟨26021, by rfl⟩) R52043
theorem R40507 : Reach 40507 := rs (se 1 (by rfl) ⟨30380, by rfl⟩) R60761
theorem R1089125 : Reach 1089125 := rs (se 4 (by rfl) ⟨102105, by rfl⟩) R204211
theorem R40583 : Reach 40583 := rs (se 1 (by rfl) ⟨30437, by rfl⟩) R60875
theorem R40591 : Reach 40591 := rs (se 1 (by rfl) ⟨30443, by rfl⟩) R60887
theorem R40635 : Reach 40635 := rs (se 1 (by rfl) ⟨30476, by rfl⟩) R60953
theorem R40711 : Reach 40711 := rs (se 1 (by rfl) ⟨30533, by rfl⟩) R61067
theorem R40719 : Reach 40719 := rs (se 1 (by rfl) ⟨30539, by rfl⟩) R61079
theorem R40763 : Reach 40763 := rs (se 1 (by rfl) ⟨30572, by rfl⟩) R61145
theorem R40839 : Reach 40839 := rs (se 1 (by rfl) ⟨30629, by rfl⟩) R61259
theorem R40847 : Reach 40847 := rs (se 1 (by rfl) ⟨30635, by rfl⟩) R61271
theorem R106393 : Reach 106393 := rs (se 2 (by rfl) ⟨39897, by rfl⟩) R79795
theorem R40891 : Reach 40891 := rs (se 1 (by rfl) ⟨30668, by rfl⟩) R61337
theorem R40967 : Reach 40967 := rs (se 1 (by rfl) ⟨30725, by rfl⟩) R61451
theorem R40975 : Reach 40975 := rs (se 1 (by rfl) ⟨30731, by rfl⟩) R61463
theorem R106529 : Reach 106529 := rs (se 2 (by rfl) ⟨39948, by rfl⟩) R79897
theorem R41019 : Reach 41019 := rs (se 1 (by rfl) ⟨30764, by rfl⟩) R61529
theorem R106555 : Reach 106555 := rs (se 1 (by rfl) ⟨79916, by rfl⟩) R159833
theorem R41095 : Reach 41095 := rs (se 1 (by rfl) ⟨30821, by rfl⟩) R61643
theorem R41103 : Reach 41103 := rs (se 1 (by rfl) ⟨30827, by rfl⟩) R61655
theorem R1614005 : Reach 1614005 := rs (se 5 (by rfl) ⟨75656, by rfl⟩) R151313
theorem R41147 : Reach 41147 := rs (se 1 (by rfl) ⟨30860, by rfl⟩) R61721
theorem R106697 : Reach 106697 := rs (se 2 (by rfl) ⟨40011, by rfl⟩) R80023
theorem R41223 : Reach 41223 := rs (se 1 (by rfl) ⟨30917, by rfl⟩) R61835
theorem R41231 : Reach 41231 := rs (se 1 (by rfl) ⟨30923, by rfl⟩) R61847
theorem R139535 : Reach 139535 := rs (se 1 (by rfl) ⟨104651, by rfl⟩) R209303
theorem R41275 : Reach 41275 := rs (se 1 (by rfl) ⟨30956, by rfl⟩) R61913
theorem R41351 : Reach 41351 := rs (se 1 (by rfl) ⟨31013, by rfl⟩) R62027
theorem R41359 : Reach 41359 := rs (se 1 (by rfl) ⟨31019, by rfl⟩) R62039
theorem R41403 : Reach 41403 := rs (se 1 (by rfl) ⟨31052, by rfl⟩) R62105
theorem R41479 : Reach 41479 := rs (se 1 (by rfl) ⟨31109, by rfl⟩) R62219
theorem R41487 : Reach 41487 := rs (se 1 (by rfl) ⟨31115, by rfl⟩) R62231
theorem R139805 : Reach 139805 := rs (se 3 (by rfl) ⟨26213, by rfl⟩) R52427
theorem R107041 : Reach 107041 := rs (se 2 (by rfl) ⟨40140, by rfl⟩) R80281
theorem R41531 : Reach 41531 := rs (se 1 (by rfl) ⟨31148, by rfl⟩) R62297
theorem R41607 : Reach 41607 := rs (se 1 (by rfl) ⟨31205, by rfl⟩) R62411
theorem R41615 : Reach 41615 := rs (se 1 (by rfl) ⟨31211, by rfl⟩) R62423
theorem R41659 : Reach 41659 := rs (se 1 (by rfl) ⟨31244, by rfl⟩) R62489
theorem R41735 : Reach 41735 := rs (se 1 (by rfl) ⟨31301, by rfl⟩) R62603
theorem R41743 : Reach 41743 := rs (se 1 (by rfl) ⟨31307, by rfl⟩) R62615
theorem R41787 : Reach 41787 := rs (se 1 (by rfl) ⟨31340, by rfl⟩) R62681
theorem R41863 : Reach 41863 := rs (se 1 (by rfl) ⟨31397, by rfl⟩) R62795
theorem R41871 : Reach 41871 := rs (se 1 (by rfl) ⟨31403, by rfl⟩) R62807
theorem R41915 : Reach 41915 := rs (se 1 (by rfl) ⟨31436, by rfl⟩) R62873
theorem R41991 : Reach 41991 := rs (se 1 (by rfl) ⟨31493, by rfl⟩) R62987
theorem R41999 : Reach 41999 := rs (se 1 (by rfl) ⟨31499, by rfl⟩) R62999
theorem R42043 : Reach 42043 := rs (se 1 (by rfl) ⟨31532, by rfl⟩) R63065
theorem R107639 : Reach 107639 := rs (se 1 (by rfl) ⟨80729, by rfl⟩) R161459
theorem R42119 : Reach 42119 := rs (se 1 (by rfl) ⟨31589, by rfl⟩) R63179
theorem R42127 : Reach 42127 := rs (se 1 (by rfl) ⟨31595, by rfl⟩) R63191
theorem R42171 : Reach 42171 := rs (se 1 (by rfl) ⟨31628, by rfl⟩) R63257
theorem R107777 : Reach 107777 := rs (se 2 (by rfl) ⟨40416, by rfl⟩) R80833
theorem R42247 : Reach 42247 := rs (se 1 (by rfl) ⟨31685, by rfl⟩) R63371
theorem R75023 : Reach 75023 := rs (se 1 (by rfl) ⟨56267, by rfl⟩) R112535
theorem R42255 : Reach 42255 := rs (se 1 (by rfl) ⟨31691, by rfl⟩) R63383
theorem R42299 : Reach 42299 := rs (se 1 (by rfl) ⟨31724, by rfl⟩) R63449
theorem R42375 : Reach 42375 := rs (se 1 (by rfl) ⟨31781, by rfl⟩) R63563
theorem R42383 : Reach 42383 := rs (se 1 (by rfl) ⟨31787, by rfl⟩) R63575
theorem R206225 : Reach 206225 := rs (se 2 (by rfl) ⟨77334, by rfl⟩) R154669
theorem R42427 : Reach 42427 := rs (se 1 (by rfl) ⟨31820, by rfl⟩) R63641
theorem R42503 : Reach 42503 := rs (se 1 (by rfl) ⟨31877, by rfl⟩) R63755
theorem R42511 : Reach 42511 := rs (se 1 (by rfl) ⟨31883, by rfl⟩) R63767
theorem R75323 : Reach 75323 := rs (se 1 (by rfl) ⟨56492, by rfl⟩) R112985
theorem R42555 : Reach 42555 := rs (se 1 (by rfl) ⟨31916, by rfl⟩) R63833
theorem R42631 : Reach 42631 := rs (se 1 (by rfl) ⟨31973, by rfl⟩) R63947
theorem R42639 : Reach 42639 := rs (se 1 (by rfl) ⟨31979, by rfl⟩) R63959
theorem R42683 : Reach 42683 := rs (se 1 (by rfl) ⟨32012, by rfl⟩) R64025
theorem R42759 : Reach 42759 := rs (se 1 (by rfl) ⟨32069, by rfl⟩) R64139
theorem R42767 : Reach 42767 := rs (se 1 (by rfl) ⟨32075, by rfl⟩) R64151
theorem R108317 : Reach 108317 := rs (se 3 (by rfl) ⟨20309, by rfl⟩) R40619
theorem R239419 : Reach 239419 := rs (se 1 (by rfl) ⟨179564, by rfl⟩) R359129
theorem R42811 : Reach 42811 := rs (se 1 (by rfl) ⟨32108, by rfl⟩) R64217
theorem R42887 : Reach 42887 := rs (se 1 (by rfl) ⟨32165, by rfl⟩) R64331
theorem R42895 : Reach 42895 := rs (se 1 (by rfl) ⟨32171, by rfl⟩) R64343
theorem R141209 : Reach 141209 := rs (se 2 (by rfl) ⟨52953, by rfl⟩) R105907
theorem R42939 : Reach 42939 := rs (se 1 (by rfl) ⟨32204, by rfl⟩) R64409
theorem R43015 : Reach 43015 := rs (se 1 (by rfl) ⟨32261, by rfl⟩) R64523
theorem R43023 : Reach 43023 := rs (se 1 (by rfl) ⟨32267, by rfl⟩) R64535
theorem R75809 : Reach 75809 := rs (se 2 (by rfl) ⟨28428, by rfl⟩) R56857
theorem R43067 : Reach 43067 := rs (se 1 (by rfl) ⟨32300, by rfl⟩) R64601
theorem R108935 : Reach 108935 := rs (se 1 (by rfl) ⟨81701, by rfl⟩) R163403
theorem R108985 : Reach 108985 := rs (se 2 (by rfl) ⟨40869, by rfl⟩) R81739
theorem R43535 : Reach 43535 := rs (se 1 (by rfl) ⟨32651, by rfl⟩) R65303
theorem R305693 : Reach 305693 := rs (se 3 (by rfl) ⟨57317, by rfl⟩) R114635
theorem R600641 : Reach 600641 := rs (se 2 (by rfl) ⟨225240, by rfl⟩) R450481
theorem R141911 : Reach 141911 := rs (se 1 (by rfl) ⟨106433, by rfl⟩) R212867
theorem R895607 : Reach 895607 := rs (se 1 (by rfl) ⟨671705, by rfl⟩) R1343411
theorem R142289 : Reach 142289 := rs (se 2 (by rfl) ⟨53358, by rfl⟩) R106717
theorem R142397 : Reach 142397 := rs (se 3 (by rfl) ⟨26699, by rfl⟩) R53399
theorem R44167 : Reach 44167 := rs (se 1 (by rfl) ⟨33125, by rfl⟩) R66251
theorem R109853 : Reach 109853 := rs (se 3 (by rfl) ⟨20597, by rfl⟩) R41195
theorem R44347 : Reach 44347 := rs (se 1 (by rfl) ⟨33260, by rfl⟩) R66521
theorem R142651 : Reach 142651 := rs (se 1 (by rfl) ⟨106988, by rfl⟩) R213977
theorem R208331 : Reach 208331 := rs (se 1 (by rfl) ⟨156248, by rfl⟩) R312497
theorem R241163 : Reach 241163 := rs (se 1 (by rfl) ⟨180872, by rfl⟩) R361745
theorem R77345 : Reach 77345 := rs (se 2 (by rfl) ⟨29004, by rfl⟩) R58009
theorem R44731 : Reach 44731 := rs (se 1 (by rfl) ⟨33548, by rfl⟩) R67097
theorem R44815 : Reach 44815 := rs (se 1 (by rfl) ⟨33611, by rfl⟩) R67223
theorem R208655 : Reach 208655 := rs (se 1 (by rfl) ⟨156491, by rfl⟩) R312983
theorem R339875 : Reach 339875 := rs (se 1 (by rfl) ⟨254906, by rfl⟩) R509813
theorem R77753 : Reach 77753 := rs (se 2 (by rfl) ⟨29157, by rfl⟩) R58315
theorem R45319 : Reach 45319 := rs (se 1 (by rfl) ⟨33989, by rfl⟩) R67979
theorem R536977 : Reach 536977 := rs (se 2 (by rfl) ⟨201366, by rfl⟩) R402733
theorem R143801 : Reach 143801 := rs (se 2 (by rfl) ⟨53925, by rfl⟩) R107851
theorem R45499 : Reach 45499 := rs (se 1 (by rfl) ⟨34124, by rfl⟩) R68249
theorem R177011 : Reach 177011 := rs (se 1 (by rfl) ⟨132758, by rfl⟩) R265517
theorem R45967 : Reach 45967 := rs (se 1 (by rfl) ⟨34475, by rfl⟩) R68951
theorem R144337 : Reach 144337 := rs (se 2 (by rfl) ⟨54126, by rfl⟩) R108253
theorem R144395 : Reach 144395 := rs (se 1 (by rfl) ⟨108296, by rfl⟩) R216593
theorem R78907 : Reach 78907 := rs (se 1 (by rfl) ⟨59180, by rfl⟩) R118361
theorem R144503 : Reach 144503 := rs (se 1 (by rfl) ⟨108377, by rfl⟩) R216755
theorem R210113 : Reach 210113 := rs (se 2 (by rfl) ⟨78792, by rfl⟩) R157585
theorem R177353 : Reach 177353 := rs (se 2 (by rfl) ⟨66507, by rfl⟩) R133015
theorem R46471 : Reach 46471 := rs (se 1 (by rfl) ⟨34853, by rfl⟩) R69707
theorem R46507 : Reach 46507 := rs (se 1 (by rfl) ⟨34880, by rfl⟩) R69761
theorem R1291697 : Reach 1291697 := rs (se 2 (by rfl) ⟨484386, by rfl⟩) R968773
theorem R308701 : Reach 308701 := rs (se 3 (by rfl) ⟨57881, by rfl⟩) R115763
theorem R79393 : Reach 79393 := rs (se 2 (by rfl) ⟨29772, by rfl⟩) R59545
theorem R46651 : Reach 46651 := rs (se 1 (by rfl) ⟨34988, by rfl⟩) R69977
theorem R145097 : Reach 145097 := rs (se 2 (by rfl) ⟨54411, by rfl⟩) R108823
theorem R112585 : Reach 112585 := rs (se 2 (by rfl) ⟨42219, by rfl⟩) R84439
theorem R243665 : Reach 243665 := rs (se 2 (by rfl) ⟨91374, by rfl⟩) R182749
theorem R47119 : Reach 47119 := rs (se 1 (by rfl) ⟨35339, by rfl⟩) R70679
theorem R145475 : Reach 145475 := rs (se 1 (by rfl) ⟨109106, by rfl⟩) R218213
theorem R440407 : Reach 440407 := rs (se 1 (by rfl) ⟨330305, by rfl⟩) R660611
theorem R112793 : Reach 112793 := rs (se 2 (by rfl) ⟨42297, by rfl⟩) R84595
theorem R47479 : Reach 47479 := rs (se 1 (by rfl) ⟨35609, by rfl⟩) R71219
theorem R211409 : Reach 211409 := rs (se 2 (by rfl) ⟨79278, by rfl⟩) R158557
theorem R47623 : Reach 47623 := rs (se 1 (by rfl) ⟨35717, by rfl⟩) R71435
theorem R47659 : Reach 47659 := rs (se 1 (by rfl) ⟨35744, by rfl⟩) R71489
theorem R80443 : Reach 80443 := rs (se 1 (by rfl) ⟨60332, by rfl⟩) R120665
theorem R244397 : Reach 244397 := rs (se 3 (by rfl) ⟨45824, by rfl⟩) R91649
theorem R47803 : Reach 47803 := rs (se 1 (by rfl) ⟨35852, by rfl⟩) R71705
theorem R80585 : Reach 80585 := rs (se 2 (by rfl) ⟨30219, by rfl⟩) R60439
theorem R441139 : Reach 441139 := rs (se 1 (by rfl) ⟨330854, by rfl⟩) R661709
theorem R310067 : Reach 310067 := rs (se 1 (by rfl) ⟨232550, by rfl⟩) R465101
theorem R113707 : Reach 113707 := rs (se 1 (by rfl) ⟨85280, by rfl⟩) R170561
theorem R48271 : Reach 48271 := rs (se 1 (by rfl) ⟨36203, by rfl⟩) R72407
theorem R179471 : Reach 179471 := rs (se 1 (by rfl) ⟨134603, by rfl⟩) R269207
theorem R867617 : Reach 867617 := rs (se 2 (by rfl) ⟨325356, by rfl⟩) R650713
theorem R81287 : Reach 81287 := rs (se 1 (by rfl) ⟨60965, by rfl⟩) R121931
theorem R81299 : Reach 81299 := rs (se 1 (by rfl) ⟨60974, by rfl⟩) R121949
theorem R310675 : Reach 310675 := rs (se 1 (by rfl) ⟨233006, by rfl⟩) R466013
theorem R81337 : Reach 81337 := rs (se 2 (by rfl) ⟨30501, by rfl⟩) R61003
theorem R376285 : Reach 376285 := rs (se 3 (by rfl) ⟨70553, by rfl⟩) R141107
theorem R179779 : Reach 179779 := rs (se 1 (by rfl) ⟨134834, by rfl⟩) R269669
theorem R114443 : Reach 114443 := rs (se 1 (by rfl) ⟨85832, by rfl⟩) R171665
theorem R245537 : Reach 245537 := rs (se 2 (by rfl) ⟨92076, by rfl⟩) R184153
theorem R49295 : Reach 49295 := rs (se 1 (by rfl) ⟨36971, by rfl⟩) R73943
theorem R213229 : Reach 213229 := rs (se 3 (by rfl) ⟨39980, by rfl⟩) R79961
theorem R115091 : Reach 115091 := rs (se 1 (by rfl) ⟨86318, by rfl⟩) R172637
theorem R213515 : Reach 213515 := rs (se 1 (by rfl) ⟨160136, by rfl⟩) R320273
theorem R115319 : Reach 115319 := rs (se 1 (by rfl) ⟨86489, by rfl⟩) R172979
theorem R49835 : Reach 49835 := rs (se 1 (by rfl) ⟨37376, by rfl⟩) R74753
theorem R213677 : Reach 213677 := rs (se 3 (by rfl) ⟨40064, by rfl⟩) R80129
theorem R50039 : Reach 50039 := rs (se 1 (by rfl) ⟨37529, by rfl⟩) R75059
theorem R312331 : Reach 312331 := rs (se 1 (by rfl) ⟨234248, by rfl⟩) R468497
theorem R50311 : Reach 50311 := rs (se 1 (by rfl) ⟨37733, by rfl⟩) R75467
theorem R149111 : Reach 149111 := rs (se 1 (by rfl) ⟨111833, by rfl⟩) R223667
theorem R50807 : Reach 50807 := rs (se 1 (by rfl) ⟨38105, by rfl⟩) R76211
theorem R50959 : Reach 50959 := rs (se 1 (by rfl) ⟨38219, by rfl⟩) R76439
theorem R51131 : Reach 51131 := rs (se 1 (by rfl) ⟨38348, by rfl⟩) R76697
theorem R215297 : Reach 215297 := rs (se 2 (by rfl) ⟨80736, by rfl⟩) R161473
theorem R248123 : Reach 248123 := rs (se 1 (by rfl) ⟨186092, by rfl⟩) R372185
theorem R150083 : Reach 150083 := rs (se 1 (by rfl) ⟨112562, by rfl⟩) R225125
theorem R379511 : Reach 379511 := rs (se 1 (by rfl) ⟨284633, by rfl⟩) R569267
theorem R52103 : Reach 52103 := rs (se 1 (by rfl) ⟨39077, by rfl⟩) R78155
theorem R84883 : Reach 84883 := rs (se 1 (by rfl) ⟨63662, by rfl⟩) R127325
theorem R52267 : Reach 52267 := rs (se 1 (by rfl) ⟨39200, by rfl⟩) R78401
theorem R216107 : Reach 216107 := rs (se 1 (by rfl) ⟨162080, by rfl⟩) R324161
theorem R52751 : Reach 52751 := rs (se 1 (by rfl) ⟨39563, by rfl⟩) R79127
theorem R282305 : Reach 282305 := rs (se 2 (by rfl) ⟨105864, by rfl⟩) R211729
theorem R118543 : Reach 118543 := rs (se 1 (by rfl) ⟨88907, by rfl⟩) R177815
theorem R53065 : Reach 53065 := rs (se 2 (by rfl) ⟨19899, by rfl⟩) R39799
theorem R511895 : Reach 511895 := rs (se 1 (by rfl) ⟨383921, by rfl⟩) R767843
theorem R118817 : Reach 118817 := rs (se 2 (by rfl) ⟨44556, by rfl⟩) R89113
theorem R151753 : Reach 151753 := rs (se 2 (by rfl) ⟨56907, by rfl⟩) R113815
theorem R53561 : Reach 53561 := rs (se 2 (by rfl) ⟨20085, by rfl⟩) R40171
theorem R217403 : Reach 217403 := rs (se 1 (by rfl) ⟨163052, by rfl⟩) R326105
theorem R1036637 : Reach 1036637 := rs (se 3 (by rfl) ⟨194369, by rfl⟩) R388739
theorem R217565 : Reach 217565 := rs (se 3 (by rfl) ⟨40793, by rfl⟩) R81587
theorem R217889 : Reach 217889 := rs (se 2 (by rfl) ⟨81708, by rfl⟩) R163417
theorem R119819 : Reach 119819 := rs (se 1 (by rfl) ⟨89864, by rfl⟩) R179729
theorem R447605 : Reach 447605 := rs (se 5 (by rfl) ⟨20981, by rfl⟩) R41963
theorem R152813 : Reach 152813 := rs (se 3 (by rfl) ⟨28652, by rfl⟩) R57305
theorem R120217 : Reach 120217 := rs (se 2 (by rfl) ⟨45081, by rfl⟩) R90163
theorem R382429 : Reach 382429 := rs (se 3 (by rfl) ⟨71705, by rfl⟩) R143411
theorem R120467 : Reach 120467 := rs (se 1 (by rfl) ⟨90350, by rfl⟩) R180701
theorem R120521 : Reach 120521 := rs (se 2 (by rfl) ⟨45195, by rfl⟩) R90391
theorem R907057 : Reach 907057 := rs (se 2 (by rfl) ⟨340146, by rfl⟩) R680293
theorem R481139 : Reach 481139 := rs (se 1 (by rfl) ⟨360854, by rfl⟩) R721709
theorem R88199 : Reach 88199 := rs (se 1 (by rfl) ⟨66149, by rfl⟩) R132299
theorem R88265 : Reach 88265 := rs (se 2 (by rfl) ⟨33099, by rfl⟩) R66199
theorem R88379 : Reach 88379 := rs (se 1 (by rfl) ⟨66284, by rfl⟩) R132569
theorem R153971 : Reach 153971 := rs (se 1 (by rfl) ⟨115478, by rfl⟩) R230957
theorem R317843 : Reach 317843 := rs (se 1 (by rfl) ⟨238382, by rfl⟩) R476765
theorem R55723 : Reach 55723 := rs (se 1 (by rfl) ⟨41792, by rfl⟩) R83585
theorem R88505 : Reach 88505 := rs (se 2 (by rfl) ⟨33189, by rfl⟩) R66379
theorem R383453 : Reach 383453 := rs (se 3 (by rfl) ⟨71897, by rfl⟩) R143795
theorem R121459 : Reach 121459 := rs (se 1 (by rfl) ⟨91094, by rfl⟩) R182189
theorem R88847 : Reach 88847 := rs (se 1 (by rfl) ⟨66635, by rfl⟩) R133271
theorem R88865 : Reach 88865 := rs (se 2 (by rfl) ⟨33324, by rfl⟩) R66649
theorem R351013 : Reach 351013 := rs (se 4 (by rfl) ⟨32907, by rfl⟩) R65815
theorem R89207 : Reach 89207 := rs (se 1 (by rfl) ⟨66905, by rfl⟩) R133811
theorem R89387 : Reach 89387 := rs (se 1 (by rfl) ⟨67040, by rfl⟩) R134081
theorem R155015 : Reach 155015 := rs (se 1 (by rfl) ⟨116261, by rfl⟩) R232523
theorem R89633 : Reach 89633 := rs (se 2 (by rfl) ⟨33612, by rfl⟩) R67225
theorem R187991 : Reach 187991 := rs (se 1 (by rfl) ⟨140993, by rfl⟩) R281987
theorem R89747 : Reach 89747 := rs (se 1 (by rfl) ⟨67310, by rfl⟩) R134621
theorem R89801 : Reach 89801 := rs (se 2 (by rfl) ⟨33675, by rfl⟩) R67351
theorem R188219 : Reach 188219 := rs (se 1 (by rfl) ⟨141164, by rfl⟩) R282329
theorem R942353 : Reach 942353 := rs (se 2 (by rfl) ⟨353382, by rfl⟩) R706765
theorem R90487 : Reach 90487 := rs (se 1 (by rfl) ⟨67865, by rfl⟩) R135731
theorem R90503 : Reach 90503 := rs (se 1 (by rfl) ⟨67877, by rfl⟩) R135755
theorem R451001 : Reach 451001 := rs (se 2 (by rfl) ⟨169125, by rfl⟩) R338251
theorem R156113 : Reach 156113 := rs (se 2 (by rfl) ⟨58542, by rfl⟩) R117085
theorem R123407 : Reach 123407 := rs (se 1 (by rfl) ⟨92555, by rfl⟩) R185111
theorem R582187 : Reach 582187 := rs (se 1 (by rfl) ⟨436640, by rfl⟩) R873281
theorem R90683 : Reach 90683 := rs (se 1 (by rfl) ⟨68012, by rfl⟩) R136025
theorem R90809 : Reach 90809 := rs (se 2 (by rfl) ⟨34053, by rfl⟩) R68107
theorem R352997 : Reach 352997 := rs (se 4 (by rfl) ⟨33093, by rfl⟩) R66187
theorem R156431 : Reach 156431 := rs (se 1 (by rfl) ⟨117323, by rfl⟩) R234647
theorem R222041 : Reach 222041 := rs (se 2 (by rfl) ⟨83265, by rfl⟩) R166531
theorem R91151 : Reach 91151 := rs (se 1 (by rfl) ⟨68363, by rfl⟩) R136727
theorem R91169 : Reach 91169 := rs (se 2 (by rfl) ⟨34188, by rfl⟩) R68377
theorem R58411 : Reach 58411 := rs (se 1 (by rfl) ⟨43808, by rfl⟩) R87617
theorem R58639 : Reach 58639 := rs (se 1 (by rfl) ⟨43979, by rfl⟩) R87959
theorem R58697 : Reach 58697 := rs (se 2 (by rfl) ⟨22011, by rfl⟩) R44023
theorem R91511 : Reach 91511 := rs (se 1 (by rfl) ⟨68633, by rfl⟩) R137267
theorem R3433859 : Reach 3433859 := rs (se 1 (by rfl) ⟨2575394, by rfl⟩) R5150789
theorem R58811 : Reach 58811 := rs (se 1 (by rfl) ⟨44108, by rfl⟩) R88217
theorem R58871 : Reach 58871 := rs (se 1 (by rfl) ⟨44153, by rfl⟩) R88307
theorem R58895 : Reach 58895 := rs (se 1 (by rfl) ⟨44171, by rfl⟩) R88343
theorem R91691 : Reach 91691 := rs (se 1 (by rfl) ⟨68768, by rfl⟩) R137537
theorem R58937 : Reach 58937 := rs (se 2 (by rfl) ⟨22101, by rfl⟩) R44203
theorem R59015 : Reach 59015 := rs (se 1 (by rfl) ⟨44261, by rfl⟩) R88523
theorem R59051 : Reach 59051 := rs (se 1 (by rfl) ⟨44288, by rfl⟩) R88577
theorem R59081 : Reach 59081 := rs (se 2 (by rfl) ⟨22155, by rfl⟩) R44311
theorem R190259 : Reach 190259 := rs (se 1 (by rfl) ⟨142694, by rfl⟩) R285389
theorem R59195 : Reach 59195 := rs (se 1 (by rfl) ⟨44396, by rfl⟩) R88793
theorem R59255 : Reach 59255 := rs (se 1 (by rfl) ⟨44441, by rfl⟩) R88883
theorem R59279 : Reach 59279 := rs (se 1 (by rfl) ⟨44459, by rfl⟩) R88919
theorem R92051 : Reach 92051 := rs (se 1 (by rfl) ⟨69038, by rfl⟩) R138077
theorem R59321 : Reach 59321 := rs (se 2 (by rfl) ⟨22245, by rfl⟩) R44491
theorem R92105 : Reach 92105 := rs (se 2 (by rfl) ⟨34539, by rfl⟩) R69079
theorem R223235 : Reach 223235 := rs (se 1 (by rfl) ⟨167426, by rfl⟩) R334853
theorem R59399 : Reach 59399 := rs (se 1 (by rfl) ⟨44549, by rfl⟩) R89099
theorem R59435 : Reach 59435 := rs (se 1 (by rfl) ⟨44576, by rfl⟩) R89153
theorem R256061 : Reach 256061 := rs (se 3 (by rfl) ⟨48011, by rfl⟩) R96023
theorem R59465 : Reach 59465 := rs (se 2 (by rfl) ⟨22299, by rfl⟩) R44599
theorem R59579 : Reach 59579 := rs (se 1 (by rfl) ⟨44684, by rfl⟩) R89369
theorem R59639 : Reach 59639 := rs (se 1 (by rfl) ⟨44729, by rfl⟩) R89459
theorem R59663 : Reach 59663 := rs (se 1 (by rfl) ⟨44747, by rfl⟩) R89495
theorem R59705 : Reach 59705 := rs (se 2 (by rfl) ⟨22389, by rfl⟩) R44779
theorem R190835 : Reach 190835 := rs (se 1 (by rfl) ⟨143126, by rfl⟩) R286253
theorem R59783 : Reach 59783 := rs (se 1 (by rfl) ⟨44837, by rfl⟩) R89675
theorem R59819 : Reach 59819 := rs (se 1 (by rfl) ⟨44864, by rfl⟩) R89729
theorem R59849 : Reach 59849 := rs (se 2 (by rfl) ⟨22443, by rfl⟩) R44887
theorem R322001 : Reach 322001 := rs (se 2 (by rfl) ⟨120750, by rfl⟩) R241501
theorem R59963 : Reach 59963 := rs (se 1 (by rfl) ⟨44972, by rfl⟩) R89945
theorem R60023 : Reach 60023 := rs (se 1 (by rfl) ⟨45017, by rfl⟩) R90035
theorem R92807 : Reach 92807 := rs (se 1 (by rfl) ⟨69605, by rfl⟩) R139211
theorem R60047 : Reach 60047 := rs (se 1 (by rfl) ⟨45035, by rfl⟩) R90071
theorem R92825 : Reach 92825 := rs (se 2 (by rfl) ⟨34809, by rfl⟩) R69619
theorem R60089 : Reach 60089 := rs (se 2 (by rfl) ⟨22533, by rfl⟩) R45067
theorem R1010393 : Reach 1010393 := rs (se 2 (by rfl) ⟨378897, by rfl⟩) R757795
theorem R60167 : Reach 60167 := rs (se 1 (by rfl) ⟨45125, by rfl⟩) R90251
theorem R60203 : Reach 60203 := rs (se 1 (by rfl) ⟨45152, by rfl⟩) R90305
theorem R92987 : Reach 92987 := rs (se 1 (by rfl) ⟨69740, by rfl⟩) R139481
theorem R60233 : Reach 60233 := rs (se 2 (by rfl) ⟨22587, by rfl⟩) R45175
theorem R486233 : Reach 486233 := rs (se 2 (by rfl) ⟨182337, by rfl⟩) R364675
theorem R60331 : Reach 60331 := rs (se 1 (by rfl) ⟨45248, by rfl⟩) R90497
theorem R93113 : Reach 93113 := rs (se 2 (by rfl) ⟨34917, by rfl⟩) R69835
theorem R60347 : Reach 60347 := rs (se 1 (by rfl) ⟨45260, by rfl⟩) R90521
theorem R60407 : Reach 60407 := rs (se 1 (by rfl) ⟨45305, by rfl⟩) R90611
theorem R93185 : Reach 93185 := rs (se 2 (by rfl) ⟨34944, by rfl⟩) R69889
theorem R60431 : Reach 60431 := rs (se 1 (by rfl) ⟨45323, by rfl⟩) R90647
theorem R125981 : Reach 125981 := rs (se 3 (by rfl) ⟨23621, by rfl⟩) R47243
theorem R60473 : Reach 60473 := rs (se 2 (by rfl) ⟨22677, by rfl⟩) R45355
theorem R60551 : Reach 60551 := rs (se 1 (by rfl) ⟨45413, by rfl⟩) R90827
theorem R60587 : Reach 60587 := rs (se 1 (by rfl) ⟨45440, by rfl⟩) R90881
theorem R60617 : Reach 60617 := rs (se 2 (by rfl) ⟨22731, by rfl⟩) R45463
theorem R93455 : Reach 93455 := rs (se 1 (by rfl) ⟨70091, by rfl⟩) R140183
theorem R93473 : Reach 93473 := rs (se 2 (by rfl) ⟨35052, by rfl⟩) R70105
theorem R60731 : Reach 60731 := rs (se 1 (by rfl) ⟨45548, by rfl⟩) R91097
theorem R93527 : Reach 93527 := rs (se 1 (by rfl) ⟨70145, by rfl⟩) R140291
theorem R60791 : Reach 60791 := rs (se 1 (by rfl) ⟨45593, by rfl⟩) R91187
theorem R60815 : Reach 60815 := rs (se 1 (by rfl) ⟨45611, by rfl⟩) R91223
theorem R60857 : Reach 60857 := rs (se 2 (by rfl) ⟨22821, by rfl⟩) R45643
theorem R60935 : Reach 60935 := rs (se 1 (by rfl) ⟨45701, by rfl⟩) R91403
theorem R93707 : Reach 93707 := rs (se 1 (by rfl) ⟨70280, by rfl⟩) R140561
theorem R60971 : Reach 60971 := rs (se 1 (by rfl) ⟨45728, by rfl⟩) R91457
theorem R61001 : Reach 61001 := rs (se 2 (by rfl) ⟨22875, by rfl⟩) R45751
theorem R93815 : Reach 93815 := rs (se 1 (by rfl) ⟨70361, by rfl⟩) R140723
theorem R61115 : Reach 61115 := rs (se 1 (by rfl) ⟨45836, by rfl⟩) R91673
theorem R61175 : Reach 61175 := rs (se 1 (by rfl) ⟨45881, by rfl⟩) R91763
theorem R61199 : Reach 61199 := rs (se 1 (by rfl) ⟨45899, by rfl⟩) R91799
theorem R93995 : Reach 93995 := rs (se 1 (by rfl) ⟨70496, by rfl⟩) R140993
theorem R61241 : Reach 61241 := rs (se 2 (by rfl) ⟨22965, by rfl⟩) R45931
theorem R94067 : Reach 94067 := rs (se 1 (by rfl) ⟨70550, by rfl⟩) R141101
theorem R61319 : Reach 61319 := rs (se 1 (by rfl) ⟨45989, by rfl⟩) R91979
theorem R61327 : Reach 61327 := rs (se 1 (by rfl) ⟨45995, by rfl⟩) R91991
theorem R61355 : Reach 61355 := rs (se 1 (by rfl) ⟨46016, by rfl⟩) R92033
theorem R61385 : Reach 61385 := rs (se 2 (by rfl) ⟨23019, by rfl⟩) R46039
theorem R61499 : Reach 61499 := rs (se 1 (by rfl) ⟨46124, by rfl⟩) R92249
theorem R127037 : Reach 127037 := rs (se 3 (by rfl) ⟨23819, by rfl⟩) R47639
theorem R61559 : Reach 61559 := rs (se 1 (by rfl) ⟨46169, by rfl⟩) R92339
theorem R61583 : Reach 61583 := rs (se 1 (by rfl) ⟨46187, by rfl⟩) R92375
theorem R94355 : Reach 94355 := rs (se 1 (by rfl) ⟨70766, by rfl⟩) R141533
theorem R61625 : Reach 61625 := rs (se 2 (by rfl) ⟨23109, by rfl⟩) R46219
theorem R94409 : Reach 94409 := rs (se 2 (by rfl) ⟨35403, by rfl⟩) R70807
theorem R160001 : Reach 160001 := rs (se 2 (by rfl) ⟨60000, by rfl⟩) R120001
theorem R61703 : Reach 61703 := rs (se 1 (by rfl) ⟨46277, by rfl⟩) R92555
theorem R160015 : Reach 160015 := rs (se 1 (by rfl) ⟨120011, by rfl⟩) R240023
theorem R61739 : Reach 61739 := rs (se 1 (by rfl) ⟨46304, by rfl⟩) R92609
theorem R61769 : Reach 61769 := rs (se 2 (by rfl) ⟨23163, by rfl⟩) R46327
theorem R225625 : Reach 225625 := rs (se 2 (by rfl) ⟨84609, by rfl⟩) R169219
theorem R61967 : Reach 61967 := rs (se 1 (by rfl) ⟨46475, by rfl⟩) R92951
theorem R62087 : Reach 62087 := rs (se 1 (by rfl) ⟨46565, by rfl⟩) R93131
theorem R62153 : Reach 62153 := rs (se 2 (by rfl) ⟨23307, by rfl⟩) R46615
theorem R62267 : Reach 62267 := rs (se 1 (by rfl) ⟨46700, by rfl⟩) R93401
theorem R62327 : Reach 62327 := rs (se 1 (by rfl) ⟨46745, by rfl⟩) R93491
theorem R95111 : Reach 95111 := rs (se 1 (by rfl) ⟨71333, by rfl⟩) R142667
theorem R95129 : Reach 95129 := rs (se 2 (by rfl) ⟨35673, by rfl⟩) R71347
theorem R62393 : Reach 62393 := rs (se 2 (by rfl) ⟨23397, by rfl⟩) R46795
theorem R62507 : Reach 62507 := rs (se 1 (by rfl) ⟨46880, by rfl⟩) R93761
theorem R95291 : Reach 95291 := rs (se 1 (by rfl) ⟨71468, by rfl⟩) R142937
theorem R390277 : Reach 390277 := rs (se 4 (by rfl) ⟨36588, by rfl⟩) R73177
theorem R95417 : Reach 95417 := rs (se 2 (by rfl) ⟨35781, by rfl⟩) R71563
theorem R488693 : Reach 488693 := rs (se 5 (by rfl) ⟨22907, by rfl⟩) R45815
theorem R95489 : Reach 95489 := rs (se 2 (by rfl) ⟨35808, by rfl⟩) R71617
theorem R62735 : Reach 62735 := rs (se 1 (by rfl) ⟨47051, by rfl⟩) R94103
theorem R62855 : Reach 62855 := rs (se 1 (by rfl) ⟨47141, by rfl⟩) R94283
theorem R128441 : Reach 128441 := rs (se 2 (by rfl) ⟨48165, by rfl⟩) R96331
theorem R62921 : Reach 62921 := rs (se 2 (by rfl) ⟨23595, by rfl⟩) R47191
theorem R161291 : Reach 161291 := rs (se 1 (by rfl) ⟨120968, by rfl⟩) R241937
theorem R95759 : Reach 95759 := rs (se 1 (by rfl) ⟨71819, by rfl⟩) R143639
theorem R95777 : Reach 95777 := rs (se 2 (by rfl) ⟨35916, by rfl⟩) R71833
theorem R128555 : Reach 128555 := rs (se 1 (by rfl) ⟨96416, by rfl⟩) R192833
theorem R63035 : Reach 63035 := rs (se 1 (by rfl) ⟨47276, by rfl⟩) R94553
theorem R95831 : Reach 95831 := rs (se 1 (by rfl) ⟨71873, by rfl⟩) R143747
theorem R63095 : Reach 63095 := rs (se 1 (by rfl) ⟨47321, by rfl⟩) R94643
theorem R95879 : Reach 95879 := rs (se 1 (by rfl) ⟨71909, by rfl⟩) R143819
theorem R63161 : Reach 63161 := rs (se 2 (by rfl) ⟨23685, by rfl⟩) R47371
theorem R96011 : Reach 96011 := rs (se 1 (by rfl) ⟨72008, by rfl⟩) R144017
theorem R63275 : Reach 63275 := rs (se 1 (by rfl) ⟨47456, by rfl⟩) R94913
theorem R423755 : Reach 423755 := rs (se 1 (by rfl) ⟨317816, by rfl⟩) R635633
theorem R96119 : Reach 96119 := rs (se 1 (by rfl) ⟨72089, by rfl⟩) R144179
theorem R128915 : Reach 128915 := rs (se 1 (by rfl) ⟨96686, by rfl⟩) R193373
theorem R194507 : Reach 194507 := rs (se 1 (by rfl) ⟨145880, by rfl⟩) R291761
theorem R194525 : Reach 194525 := rs (se 3 (by rfl) ⟨36473, by rfl⟩) R72947
theorem R63503 : Reach 63503 := rs (se 1 (by rfl) ⟨47627, by rfl⟩) R95255
theorem R227357 : Reach 227357 := rs (se 3 (by rfl) ⟨42629, by rfl⟩) R85259
theorem R96299 : Reach 96299 := rs (se 1 (by rfl) ⟨72224, by rfl⟩) R144449
theorem R96371 : Reach 96371 := rs (se 1 (by rfl) ⟨72278, by rfl⟩) R144557
theorem R63623 : Reach 63623 := rs (se 1 (by rfl) ⟨47717, by rfl⟩) R95435
theorem R63689 : Reach 63689 := rs (se 2 (by rfl) ⟨23883, by rfl⟩) R47767
theorem R63803 : Reach 63803 := rs (se 1 (by rfl) ⟨47852, by rfl⟩) R95705
theorem R63863 : Reach 63863 := rs (se 1 (by rfl) ⟨47897, by rfl⟩) R95795
theorem R96659 : Reach 96659 := rs (se 1 (by rfl) ⟨72494, by rfl⟩) R144989
theorem R63929 : Reach 63929 := rs (se 2 (by rfl) ⟨23973, by rfl⟩) R47947
theorem R162233 : Reach 162233 := rs (se 2 (by rfl) ⟨60837, by rfl⟩) R121675
theorem R96713 : Reach 96713 := rs (se 2 (by rfl) ⟨36267, by rfl⟩) R72535
theorem R64043 : Reach 64043 := rs (se 1 (by rfl) ⟨48032, by rfl⟩) R96065
theorem R195139 : Reach 195139 := rs (se 1 (by rfl) ⟨146354, by rfl⟩) R292709
theorem R228041 : Reach 228041 := rs (se 2 (by rfl) ⟨85515, by rfl⟩) R171031
theorem R64201 : Reach 64201 := rs (se 2 (by rfl) ⟨24075, by rfl⟩) R48151
theorem R64271 : Reach 64271 := rs (se 1 (by rfl) ⟨48203, by rfl⟩) R96407
theorem R64391 : Reach 64391 := rs (se 1 (by rfl) ⟨48293, by rfl⟩) R96587
theorem R64457 : Reach 64457 := rs (se 2 (by rfl) ⟨24171, by rfl⟩) R48343
theorem R64571 : Reach 64571 := rs (se 1 (by rfl) ⟨48428, by rfl⟩) R96857
theorem R228413 : Reach 228413 := rs (se 3 (by rfl) ⟨42827, by rfl⟩) R85655
theorem R64631 : Reach 64631 := rs (se 1 (by rfl) ⟨48473, by rfl⟩) R96947
theorem R457973 : Reach 457973 := rs (se 5 (by rfl) ⟨21467, by rfl⟩) R42935
theorem R97793 : Reach 97793 := rs (se 2 (by rfl) ⟨36672, by rfl⟩) R73345
theorem R196289 : Reach 196289 := rs (se 2 (by rfl) ⟨73608, by rfl⟩) R147217
theorem R393113 : Reach 393113 := rs (se 2 (by rfl) ⟨147417, by rfl⟩) R294835
theorem R65575 : Reach 65575 := rs (se 1 (by rfl) ⟨49181, by rfl⟩) R98363
theorem R196951 : Reach 196951 := rs (se 1 (by rfl) ⟨147713, by rfl⟩) R295427
theorem R131453 : Reach 131453 := rs (se 3 (by rfl) ⟨24647, by rfl⟩) R49295
theorem R66055 : Reach 66055 := rs (se 1 (by rfl) ⟨49541, by rfl⟩) R99083
theorem R66487 : Reach 66487 := rs (se 1 (by rfl) ⟨49865, by rfl⟩) R99731
theorem R590915 : Reach 590915 := rs (se 1 (by rfl) ⟨443186, by rfl⟩) R886373
theorem R99407 : Reach 99407 := rs (se 1 (by rfl) ⟨74555, by rfl⟩) R149111
theorem R66683 : Reach 66683 := rs (se 1 (by rfl) ⟨50012, by rfl⟩) R100025
theorem R132553 : Reach 132553 := rs (se 2 (by rfl) ⟨49707, by rfl⟩) R99415
theorem R67081 : Reach 67081 := rs (se 2 (by rfl) ⟨25155, by rfl⟩) R50311
theorem R165415 : Reach 165415 := rs (se 1 (by rfl) ⟨124061, by rfl⟩) R248123
theorem R132731 : Reach 132731 := rs (se 1 (by rfl) ⟨99548, by rfl⟩) R199097
theorem R67243 : Reach 67243 := rs (se 1 (by rfl) ⟨50432, by rfl⟩) R100865
theorem R100055 : Reach 100055 := rs (se 1 (by rfl) ⟨75041, by rfl⟩) R150083
theorem R132893 : Reach 132893 := rs (se 3 (by rfl) ⟨24917, by rfl⟩) R49835
theorem R67547 : Reach 67547 := rs (se 1 (by rfl) ⟨50660, by rfl⟩) R101321
theorem R67783 : Reach 67783 := rs (se 1 (by rfl) ⟨50837, by rfl⟩) R101675
theorem R592109 : Reach 592109 := rs (se 3 (by rfl) ⟨111020, by rfl⟩) R222041
theorem R67945 : Reach 67945 := rs (se 2 (by rfl) ⟨25479, by rfl⟩) R50959
theorem R461207 : Reach 461207 := rs (se 1 (by rfl) ⟨345905, by rfl⟩) R691811
theorem R133595 : Reach 133595 := rs (se 1 (by rfl) ⟨100196, by rfl⟩) R200393
theorem R68219 : Reach 68219 := rs (se 1 (by rfl) ⟨51164, by rfl⟩) R102329
theorem R691091 : Reach 691091 := rs (se 1 (by rfl) ⟨518318, by rfl⟩) R1036637
theorem R68539 : Reach 68539 := rs (se 1 (by rfl) ⟨51404, by rfl⟩) R102809
theorem R429029 : Reach 429029 := rs (se 4 (by rfl) ⟨40221, by rfl⟩) R80443
theorem R592919 : Reach 592919 := rs (se 1 (by rfl) ⟨444689, by rfl⟩) R889379
theorem R68647 : Reach 68647 := rs (se 1 (by rfl) ⟨51485, by rfl⟩) R102971
theorem R134297 : Reach 134297 := rs (se 2 (by rfl) ⟨50361, by rfl⟩) R100723
theorem R68971 : Reach 68971 := rs (se 1 (by rfl) ⟨51728, by rfl⟩) R103457
theorem R69007 : Reach 69007 := rs (se 1 (by rfl) ⟨51755, by rfl⟩) R103511
theorem R298403 : Reach 298403 := rs (se 1 (by rfl) ⟨223802, by rfl⟩) R447605
theorem R200231 : Reach 200231 := rs (se 1 (by rfl) ⟨150173, by rfl⟩) R300347
theorem R200407 : Reach 200407 := rs (se 1 (by rfl) ⟨150305, by rfl⟩) R300611
theorem R69689 : Reach 69689 := rs (se 2 (by rfl) ⟨26133, by rfl⟩) R52267
theorem R102647 : Reach 102647 := rs (se 1 (by rfl) ⟨76985, by rfl⟩) R153971
theorem R135485 : Reach 135485 := rs (se 3 (by rfl) ⟨25403, by rfl⟩) R50807
theorem R135553 : Reach 135553 := rs (se 2 (by rfl) ⟨50832, by rfl⟩) R101665
theorem R70031 : Reach 70031 := rs (se 1 (by rfl) ⟨52523, by rfl⟩) R105047
theorem R70267 : Reach 70267 := rs (se 1 (by rfl) ⟨52700, by rfl⟩) R105401
theorem R70355 : Reach 70355 := rs (se 1 (by rfl) ⟨52766, by rfl⟩) R105533
theorem R103343 : Reach 103343 := rs (se 1 (by rfl) ⟨77507, by rfl⟩) R155015
theorem R726083 : Reach 726083 := rs (se 1 (by rfl) ⟨544562, by rfl⟩) R1089125
theorem R70753 : Reach 70753 := rs (se 2 (by rfl) ⟨26532, by rfl⟩) R53065
theorem R136349 : Reach 136349 := rs (se 3 (by rfl) ⟨25565, by rfl⟩) R51131
theorem R71131 : Reach 71131 := rs (se 1 (by rfl) ⟨53348, by rfl⟩) R106697
theorem R628235 : Reach 628235 := rs (se 1 (by rfl) ⟨471176, by rfl⟩) R942353
theorem R202337 : Reach 202337 := rs (se 2 (by rfl) ⟨75876, by rfl⟩) R151753
theorem R300667 : Reach 300667 := rs (se 1 (by rfl) ⟨225500, by rfl⟩) R451001
theorem R104075 : Reach 104075 := rs (se 1 (by rfl) ⟨78056, by rfl⟩) R156113
theorem R136889 : Reach 136889 := rs (se 2 (by rfl) ⟨51333, by rfl⟩) R102667
theorem R169661 : Reach 169661 := rs (se 3 (by rfl) ⟨31811, by rfl⟩) R63623
theorem R300781 : Reach 300781 := rs (se 3 (by rfl) ⟨56396, by rfl⟩) R112793
theorem R300833 : Reach 300833 := rs (se 2 (by rfl) ⟨112812, by rfl⟩) R225625
theorem R235331 : Reach 235331 := rs (se 1 (by rfl) ⟨176498, by rfl⟩) R352997
theorem R104287 : Reach 104287 := rs (se 1 (by rfl) ⟨78215, by rfl⟩) R156431
theorem R71759 : Reach 71759 := rs (se 1 (by rfl) ⟨53819, by rfl⟩) R107639
theorem R71851 : Reach 71851 := rs (se 1 (by rfl) ⟨53888, by rfl⟩) R107777
theorem R39131 : Reach 39131 := rs (se 1 (by rfl) ⟨29348, by rfl⟩) R58697
theorem R137483 : Reach 137483 := rs (se 1 (by rfl) ⟨103112, by rfl⟩) R206225
theorem R39207 : Reach 39207 := rs (se 1 (by rfl) ⟨29405, by rfl⟩) R58811
theorem R39247 : Reach 39247 := rs (se 1 (by rfl) ⟨29435, by rfl⟩) R58871
theorem R39263 : Reach 39263 := rs (se 1 (by rfl) ⟨29447, by rfl⟩) R58895
theorem R39291 : Reach 39291 := rs (se 1 (by rfl) ⟨29468, by rfl⟩) R58937
theorem R39343 : Reach 39343 := rs (se 1 (by rfl) ⟨29507, by rfl⟩) R59015
theorem R39367 : Reach 39367 := rs (se 1 (by rfl) ⟨29525, by rfl⟩) R59051
theorem R39387 : Reach 39387 := rs (se 1 (by rfl) ⟨29540, by rfl⟩) R59081
theorem R72211 : Reach 72211 := rs (se 1 (by rfl) ⟨54158, by rfl⟩) R108317
theorem R137753 : Reach 137753 := rs (se 2 (by rfl) ⟨51657, by rfl⟩) R103315
theorem R39463 : Reach 39463 := rs (se 1 (by rfl) ⟨29597, by rfl⟩) R59195
theorem R39503 : Reach 39503 := rs (se 1 (by rfl) ⟨29627, by rfl⟩) R59255
theorem R39519 : Reach 39519 := rs (se 1 (by rfl) ⟨29639, by rfl⟩) R59279
theorem R39547 : Reach 39547 := rs (se 1 (by rfl) ⟨29660, by rfl⟩) R59321
theorem R39599 : Reach 39599 := rs (se 1 (by rfl) ⟨29699, by rfl⟩) R59399
theorem R39623 : Reach 39623 := rs (se 1 (by rfl) ⟨29717, by rfl⟩) R59435
theorem R170707 : Reach 170707 := rs (se 1 (by rfl) ⟨128030, by rfl⟩) R256061
theorem R39643 : Reach 39643 := rs (se 1 (by rfl) ⟨29732, by rfl⟩) R59465
theorem R105209 : Reach 105209 := rs (se 2 (by rfl) ⟨39453, by rfl⟩) R78907
theorem R39719 : Reach 39719 := rs (se 1 (by rfl) ⟨29789, by rfl⟩) R59579
theorem R39759 : Reach 39759 := rs (se 1 (by rfl) ⟨29819, by rfl⟩) R59639
theorem R39775 : Reach 39775 := rs (se 1 (by rfl) ⟨29831, by rfl⟩) R59663
theorem R39803 : Reach 39803 := rs (se 1 (by rfl) ⟨29852, by rfl⟩) R59705
theorem R39855 : Reach 39855 := rs (se 1 (by rfl) ⟨29891, by rfl⟩) R59783
theorem R72623 : Reach 72623 := rs (se 1 (by rfl) ⟨54467, by rfl⟩) R108935
theorem R39879 : Reach 39879 := rs (se 1 (by rfl) ⟨29909, by rfl⟩) R59819
theorem R39899 : Reach 39899 := rs (se 1 (by rfl) ⟨29924, by rfl⟩) R59849
theorem R203795 : Reach 203795 := rs (se 1 (by rfl) ⟨152846, by rfl⟩) R305693
theorem R39975 : Reach 39975 := rs (se 1 (by rfl) ⟨29981, by rfl⟩) R59963
theorem R400427 : Reach 400427 := rs (se 1 (by rfl) ⟨300320, by rfl⟩) R600641
theorem R40015 : Reach 40015 := rs (se 1 (by rfl) ⟨30011, by rfl⟩) R60023
theorem R597071 : Reach 597071 := rs (se 1 (by rfl) ⟨447803, by rfl⟩) R895607
theorem R40031 : Reach 40031 := rs (se 1 (by rfl) ⟨30023, by rfl⟩) R60047
theorem R40059 : Reach 40059 := rs (se 1 (by rfl) ⟨30044, by rfl⟩) R60089
theorem R40111 : Reach 40111 := rs (se 1 (by rfl) ⟨30083, by rfl⟩) R60167
theorem R40135 : Reach 40135 := rs (se 1 (by rfl) ⟨30101, by rfl⟩) R60203
theorem R40155 : Reach 40155 := rs (se 1 (by rfl) ⟨30116, by rfl⟩) R60233
theorem R40231 : Reach 40231 := rs (se 1 (by rfl) ⟨30173, by rfl⟩) R60347
theorem R40271 : Reach 40271 := rs (se 1 (by rfl) ⟨30203, by rfl⟩) R60407
theorem R40287 : Reach 40287 := rs (se 1 (by rfl) ⟨30215, by rfl⟩) R60431
theorem R40315 : Reach 40315 := rs (se 1 (by rfl) ⟨30236, by rfl⟩) R60473
theorem R105857 : Reach 105857 := rs (se 2 (by rfl) ⟨39696, by rfl⟩) R79393
theorem R40367 : Reach 40367 := rs (se 1 (by rfl) ⟨30275, by rfl⟩) R60551
theorem R40391 : Reach 40391 := rs (se 1 (by rfl) ⟨30293, by rfl⟩) R60587
theorem R40411 : Reach 40411 := rs (se 1 (by rfl) ⟨30308, by rfl⟩) R60617
theorem R73235 : Reach 73235 := rs (se 1 (by rfl) ⟨54926, by rfl⟩) R109853
theorem R40487 : Reach 40487 := rs (se 1 (by rfl) ⟨30365, by rfl⟩) R60731
theorem R40527 : Reach 40527 := rs (se 1 (by rfl) ⟨30395, by rfl⟩) R60791
theorem R40543 : Reach 40543 := rs (se 1 (by rfl) ⟨30407, by rfl⟩) R60815
theorem R40571 : Reach 40571 := rs (se 1 (by rfl) ⟨30428, by rfl⟩) R60857
theorem R138887 : Reach 138887 := rs (se 1 (by rfl) ⟨104165, by rfl⟩) R208331
theorem R40623 : Reach 40623 := rs (se 1 (by rfl) ⟨30467, by rfl⟩) R60935
theorem R138941 : Reach 138941 := rs (se 3 (by rfl) ⟨26051, by rfl⟩) R52103
theorem R40647 : Reach 40647 := rs (se 1 (by rfl) ⟨30485, by rfl⟩) R60971
theorem R40667 : Reach 40667 := rs (se 1 (by rfl) ⟨30500, by rfl⟩) R61001
theorem R40743 : Reach 40743 := rs (se 1 (by rfl) ⟨30557, by rfl⟩) R61115
theorem R40783 : Reach 40783 := rs (se 1 (by rfl) ⟨30587, by rfl⟩) R61175
theorem R40799 : Reach 40799 := rs (se 1 (by rfl) ⟨30599, by rfl⟩) R61199
theorem R139103 : Reach 139103 := rs (se 1 (by rfl) ⟨104327, by rfl⟩) R208655
theorem R40827 : Reach 40827 := rs (se 1 (by rfl) ⟨30620, by rfl⟩) R61241
theorem R40879 : Reach 40879 := rs (se 1 (by rfl) ⟨30659, by rfl⟩) R61319
theorem R40903 : Reach 40903 := rs (se 1 (by rfl) ⟨30677, by rfl⟩) R61355
theorem R40923 : Reach 40923 := rs (se 1 (by rfl) ⟨30692, by rfl⟩) R61385
theorem R139265 : Reach 139265 := rs (se 2 (by rfl) ⟨52224, by rfl⟩) R104449
theorem R40999 : Reach 40999 := rs (se 1 (by rfl) ⟨30749, by rfl⟩) R61499
theorem R41039 : Reach 41039 := rs (se 1 (by rfl) ⟨30779, by rfl⟩) R61559
theorem R41055 : Reach 41055 := rs (se 1 (by rfl) ⟨30791, by rfl⟩) R61583
theorem R41083 : Reach 41083 := rs (se 1 (by rfl) ⟨30812, by rfl⟩) R61625
theorem R106667 : Reach 106667 := rs (se 1 (by rfl) ⟨80000, by rfl⟩) R160001
theorem R41135 : Reach 41135 := rs (se 1 (by rfl) ⟨30851, by rfl⟩) R61703
theorem R41159 : Reach 41159 := rs (se 1 (by rfl) ⟨30869, by rfl⟩) R61739
theorem R41179 : Reach 41179 := rs (se 1 (by rfl) ⟨30884, by rfl⟩) R61769
theorem R41311 : Reach 41311 := rs (se 1 (by rfl) ⟨30983, by rfl⟩) R61967
theorem R41391 : Reach 41391 := rs (se 1 (by rfl) ⟨31043, by rfl⟩) R62087
theorem R41435 : Reach 41435 := rs (se 1 (by rfl) ⟨31076, by rfl⟩) R62153
theorem R139801 : Reach 139801 := rs (se 2 (by rfl) ⟨52425, by rfl⟩) R104851
theorem R41511 : Reach 41511 := rs (se 1 (by rfl) ⟨31133, by rfl⟩) R62267
theorem R74297 : Reach 74297 := rs (se 2 (by rfl) ⟨27861, by rfl⟩) R55723
theorem R41551 : Reach 41551 := rs (se 1 (by rfl) ⟨31163, by rfl⟩) R62327
theorem R41595 : Reach 41595 := rs (se 1 (by rfl) ⟨31196, by rfl⟩) R62393
theorem R41671 : Reach 41671 := rs (se 1 (by rfl) ⟨31253, by rfl⟩) R62507
theorem R140075 : Reach 140075 := rs (se 1 (by rfl) ⟨105056, by rfl⟩) R210113
theorem R41823 : Reach 41823 := rs (se 1 (by rfl) ⟨31367, by rfl⟩) R62735
theorem R41903 : Reach 41903 := rs (se 1 (by rfl) ⟨31427, by rfl⟩) R62855
theorem R861131 : Reach 861131 := rs (se 1 (by rfl) ⟨645848, by rfl⟩) R1291697
theorem R41947 : Reach 41947 := rs (se 1 (by rfl) ⟨31460, by rfl⟩) R62921
theorem R238565 : Reach 238565 := rs (se 4 (by rfl) ⟨22365, by rfl⟩) R44731
theorem R107527 : Reach 107527 := rs (se 1 (by rfl) ⟨80645, by rfl⟩) R161291
theorem R42023 : Reach 42023 := rs (se 1 (by rfl) ⟨31517, by rfl⟩) R63035
theorem R468017 : Reach 468017 := rs (se 2 (by rfl) ⟨175506, by rfl⟩) R351013
theorem R140345 : Reach 140345 := rs (se 2 (by rfl) ⟨52629, by rfl⟩) R105259
theorem R42063 : Reach 42063 := rs (se 1 (by rfl) ⟨31547, by rfl⟩) R63095
theorem R42107 : Reach 42107 := rs (se 1 (by rfl) ⟨31580, by rfl⟩) R63161
theorem R42183 : Reach 42183 := rs (se 1 (by rfl) ⟨31637, by rfl⟩) R63275
theorem R533749 : Reach 533749 := rs (se 5 (by rfl) ⟨25019, by rfl⟩) R50039
theorem R42335 : Reach 42335 := rs (se 1 (by rfl) ⟨31751, by rfl⟩) R63503
theorem R140669 : Reach 140669 := rs (se 3 (by rfl) ⟨26375, by rfl⟩) R52751
theorem R239021 : Reach 239021 := rs (se 3 (by rfl) ⟨44816, by rfl⟩) R89633
theorem R42415 : Reach 42415 := rs (se 1 (by rfl) ⟨31811, by rfl⟩) R63623
theorem R42459 : Reach 42459 := rs (se 1 (by rfl) ⟨31844, by rfl⟩) R63689
theorem R42535 : Reach 42535 := rs (se 1 (by rfl) ⟨31901, by rfl⟩) R63803
theorem R42575 : Reach 42575 := rs (se 1 (by rfl) ⟨31931, by rfl⟩) R63863
theorem R42619 : Reach 42619 := rs (se 1 (by rfl) ⟨31964, by rfl⟩) R63929
theorem R108155 : Reach 108155 := rs (se 1 (by rfl) ⟨81116, by rfl⟩) R162233
theorem R140939 : Reach 140939 := rs (se 1 (by rfl) ⟨105704, by rfl⟩) R211409
theorem R42695 : Reach 42695 := rs (se 1 (by rfl) ⟨32021, by rfl⟩) R64043
theorem R42847 : Reach 42847 := rs (se 1 (by rfl) ⟨32135, by rfl⟩) R64271
theorem R206711 : Reach 206711 := rs (se 1 (by rfl) ⟨155033, by rfl⟩) R310067
theorem R108449 : Reach 108449 := rs (se 2 (by rfl) ⟨40668, by rfl⟩) R81337
theorem R42927 : Reach 42927 := rs (se 1 (by rfl) ⟨32195, by rfl⟩) R64391
theorem R501713 : Reach 501713 := rs (se 2 (by rfl) ⟨188142, by rfl⟩) R376285
theorem R42971 : Reach 42971 := rs (se 1 (by rfl) ⟨32228, by rfl⟩) R64457
theorem R43047 : Reach 43047 := rs (se 1 (by rfl) ⟨32285, by rfl⟩) R64571
theorem R43087 : Reach 43087 := rs (se 1 (by rfl) ⟨32315, by rfl⟩) R64631
theorem R239705 : Reach 239705 := rs (se 2 (by rfl) ⟨89889, by rfl⟩) R179779
theorem R305315 : Reach 305315 := rs (se 1 (by rfl) ⟨228986, by rfl⟩) R457973
theorem R76295 : Reach 76295 := rs (se 1 (by rfl) ⟨57221, by rfl⟩) R114443
theorem R141857 : Reach 141857 := rs (se 2 (by rfl) ⟨53196, by rfl⟩) R106393
theorem R535085 : Reach 535085 := rs (se 3 (by rfl) ⟨100328, by rfl⟩) R200657
theorem R142073 : Reach 142073 := rs (se 2 (by rfl) ⟨53277, by rfl⟩) R106555
theorem R76727 : Reach 76727 := rs (se 1 (by rfl) ⟨57545, by rfl⟩) R115091
theorem R142343 : Reach 142343 := rs (se 1 (by rfl) ⟨106757, by rfl⟩) R213515
theorem R76879 : Reach 76879 := rs (se 1 (by rfl) ⟨57659, by rfl⟩) R115319
theorem R142451 : Reach 142451 := rs (se 1 (by rfl) ⟨106838, by rfl⟩) R213677
theorem R44383 : Reach 44383 := rs (se 1 (by rfl) ⟨33287, by rfl⟩) R66575
theorem R142721 : Reach 142721 := rs (se 2 (by rfl) ⟨53520, by rfl⟩) R107041
theorem R142829 : Reach 142829 := rs (se 3 (by rfl) ⟨26780, by rfl⟩) R53561
theorem R44743 : Reach 44743 := rs (se 1 (by rfl) ⟨33557, by rfl⟩) R67115
theorem R143531 : Reach 143531 := rs (se 1 (by rfl) ⟨107648, by rfl⟩) R215297
theorem R78185 : Reach 78185 := rs (se 2 (by rfl) ⟨29319, by rfl⟩) R58639
theorem R45607 : Reach 45607 := rs (se 1 (by rfl) ⟨34205, by rfl⟩) R68411
theorem R144071 : Reach 144071 := rs (se 1 (by rfl) ⟨108053, by rfl⟩) R216107
theorem R177079 : Reach 177079 := rs (se 1 (by rfl) ⟨132809, by rfl⟩) R265619
theorem R341263 : Reach 341263 := rs (se 1 (by rfl) ⟨255947, by rfl⟩) R511895
theorem R79211 : Reach 79211 := rs (se 1 (by rfl) ⟨59408, by rfl⟩) R118817
theorem R144935 : Reach 144935 := rs (se 1 (by rfl) ⟨108701, by rfl⟩) R217403
theorem R145043 : Reach 145043 := rs (se 1 (by rfl) ⟨108782, by rfl⟩) R217565
theorem R145259 : Reach 145259 := rs (se 1 (by rfl) ⟨108944, by rfl⟩) R217889
theorem R145313 : Reach 145313 := rs (se 2 (by rfl) ⟨54492, by rfl⟩) R108985
theorem R407501 : Reach 407501 := rs (se 3 (by rfl) ⟨76406, by rfl⟩) R152813
theorem R79879 : Reach 79879 := rs (se 1 (by rfl) ⟨59909, by rfl⟩) R119819
theorem R47227 : Reach 47227 := rs (se 1 (by rfl) ⟨35420, by rfl⟩) R70841
theorem R571697 : Reach 571697 := rs (se 2 (by rfl) ⟨214386, by rfl⟩) R428773
theorem R80347 : Reach 80347 := rs (se 1 (by rfl) ⟨60260, by rfl⟩) R120521
theorem R113177 : Reach 113177 := rs (se 2 (by rfl) ⟨42441, by rfl⟩) R84883
theorem R80441 : Reach 80441 := rs (se 2 (by rfl) ⟨30165, by rfl⟩) R60331
theorem R47695 : Reach 47695 := rs (se 1 (by rfl) ⟨35771, by rfl⟩) R71543
theorem R48055 : Reach 48055 := rs (se 1 (by rfl) ⟨36041, by rfl⟩) R72083
theorem R211895 : Reach 211895 := rs (se 1 (by rfl) ⟨158921, by rfl⟩) R317843
theorem R48091 : Reach 48091 := rs (se 1 (by rfl) ⟨36068, by rfl⟩) R72137
theorem R113683 : Reach 113683 := rs (se 1 (by rfl) ⟨85262, by rfl⟩) R170525
theorem R213029 : Reach 213029 := rs (se 4 (by rfl) ⟨19971, by rfl⟩) R39943
theorem R606437 : Reach 606437 := rs (se 4 (by rfl) ⟨56853, by rfl⟩) R113707
theorem R311525 : Reach 311525 := rs (se 4 (by rfl) ⟨29205, by rfl⟩) R58411
theorem R82271 : Reach 82271 := rs (se 1 (by rfl) ⟨61703, by rfl⟩) R123407
theorem R213353 : Reach 213353 := rs (se 2 (by rfl) ⟨80007, by rfl⟩) R160015
theorem R2081477 : Reach 2081477 := rs (se 4 (by rfl) ⟨195138, by rfl⟩) R390277
theorem R50015 : Reach 50015 := rs (se 1 (by rfl) ⟨37511, by rfl⟩) R75023
theorem R443393 : Reach 443393 := rs (se 2 (by rfl) ⟨166272, by rfl⟩) R332545
theorem R50215 : Reach 50215 := rs (se 1 (by rfl) ⟨37661, by rfl⟩) R75323
theorem R148823 : Reach 148823 := rs (se 1 (by rfl) ⟨111617, by rfl⟩) R223235
theorem R50539 : Reach 50539 := rs (se 1 (by rfl) ⟨37904, by rfl⟩) R75809
theorem R116093 : Reach 116093 := rs (se 3 (by rfl) ⟨21767, by rfl⟩) R43535
theorem R214667 : Reach 214667 := rs (se 1 (by rfl) ⟨161000, by rfl⟩) R322001
theorem R673595 : Reach 673595 := rs (se 1 (by rfl) ⟨505196, by rfl⟩) R1010393
theorem R411601 : Reach 411601 := rs (se 2 (by rfl) ⟨154350, by rfl⟩) R308701
theorem R509905 : Reach 509905 := rs (se 2 (by rfl) ⟨191214, by rfl⟩) R382429
theorem R83987 : Reach 83987 := rs (se 1 (by rfl) ⟨62990, by rfl⟩) R125981
theorem R51563 : Reach 51563 := rs (se 1 (by rfl) ⟨38672, by rfl⟩) R77345
theorem R150113 : Reach 150113 := rs (se 2 (by rfl) ⟨56292, by rfl⟩) R112585
theorem R51835 : Reach 51835 := rs (se 1 (by rfl) ⟨38876, by rfl⟩) R77753
theorem R84691 : Reach 84691 := rs (se 1 (by rfl) ⟨63518, by rfl⟩) R127037
theorem R118007 : Reach 118007 := rs (se 1 (by rfl) ⟨88505, by rfl⟩) R177011
theorem R970157 : Reach 970157 := rs (se 3 (by rfl) ⟨181904, by rfl⟩) R363809
theorem R118235 : Reach 118235 := rs (se 1 (by rfl) ⟨88676, by rfl⟩) R177353
theorem R85601 : Reach 85601 := rs (se 2 (by rfl) ⟨32100, by rfl⟩) R64201
theorem R85627 : Reach 85627 := rs (se 1 (by rfl) ⟨64220, by rfl⟩) R128441
theorem R85703 : Reach 85703 := rs (se 1 (by rfl) ⟨64277, by rfl⟩) R128555
theorem R282503 : Reach 282503 := rs (se 1 (by rfl) ⟨211877, by rfl⟩) R423755
theorem R85943 : Reach 85943 := rs (se 1 (by rfl) ⟨64457, by rfl⟩) R128915
theorem R151571 : Reach 151571 := rs (se 1 (by rfl) ⟨113678, by rfl⟩) R227357
theorem R4837637 : Reach 4837637 := rs (se 4 (by rfl) ⟨453528, by rfl⟩) R907057
theorem R152027 : Reach 152027 := rs (se 1 (by rfl) ⟨114020, by rfl⟩) R228041
theorem R53723 : Reach 53723 := rs (se 1 (by rfl) ⟨40292, by rfl⟩) R80585
theorem R414233 : Reach 414233 := rs (se 2 (by rfl) ⟨155337, by rfl⟩) R310675
theorem R185041 : Reach 185041 := rs (se 2 (by rfl) ⟨69390, by rfl⟩) R138781
theorem R152275 : Reach 152275 := rs (se 1 (by rfl) ⟨114206, by rfl⟩) R228413
theorem R119647 : Reach 119647 := rs (se 1 (by rfl) ⟨89735, by rfl⟩) R179471
theorem R578411 : Reach 578411 := rs (se 1 (by rfl) ⟨433808, by rfl⟩) R867617
theorem R54191 : Reach 54191 := rs (se 1 (by rfl) ⟨40643, by rfl⟩) R81287
theorem R54199 : Reach 54199 := rs (se 1 (by rfl) ⟨40649, by rfl⟩) R81299
theorem R284077 : Reach 284077 := rs (se 3 (by rfl) ⟨53264, by rfl⟩) R106529
theorem R153211 : Reach 153211 := rs (se 1 (by rfl) ⟨114908, by rfl⟩) R229817
theorem R284305 : Reach 284305 := rs (se 2 (by rfl) ⟨106614, by rfl⟩) R213229
theorem R776249 : Reach 776249 := rs (se 2 (by rfl) ⟨291093, by rfl⟩) R582187
theorem R350365 : Reach 350365 := rs (se 3 (by rfl) ⟨65693, by rfl⟩) R131387
theorem R88235 : Reach 88235 := rs (se 1 (by rfl) ⟨66176, by rfl⟩) R132353
theorem R416441 : Reach 416441 := rs (se 2 (by rfl) ⟨156165, by rfl⟩) R312331
theorem R88775 : Reach 88775 := rs (se 1 (by rfl) ⟨66581, by rfl⟩) R133163
theorem R154487 : Reach 154487 := rs (se 1 (by rfl) ⟨115865, by rfl⟩) R231731
theorem R154543 : Reach 154543 := rs (se 1 (by rfl) ⟨115907, by rfl⟩) R231815
theorem R253007 : Reach 253007 := rs (se 1 (by rfl) ⟨189755, by rfl⟩) R379511
theorem R482597 : Reach 482597 := rs (se 4 (by rfl) ⟨45243, by rfl⟩) R90487
theorem R89639 : Reach 89639 := rs (se 1 (by rfl) ⟨67229, by rfl⟩) R134459
theorem R188203 : Reach 188203 := rs (se 1 (by rfl) ⟨141152, by rfl⟩) R282305
theorem R155459 : Reach 155459 := rs (se 1 (by rfl) ⟨116594, by rfl⟩) R233189
theorem R89963 : Reach 89963 := rs (se 1 (by rfl) ⟨67472, by rfl⟩) R134945
theorem R90017 : Reach 90017 := rs (se 2 (by rfl) ⟨33756, by rfl⟩) R67513
theorem R221089 : Reach 221089 := rs (se 2 (by rfl) ⟨82908, by rfl⟩) R165817
theorem R286651 : Reach 286651 := rs (se 1 (by rfl) ⟨214988, by rfl⟩) R429977
theorem R90359 : Reach 90359 := rs (se 1 (by rfl) ⟨67769, by rfl⟩) R135539
theorem R155915 : Reach 155915 := rs (se 1 (by rfl) ⟨116936, by rfl⟩) R233873
theorem R549179 : Reach 549179 := rs (se 1 (by rfl) ⟨411884, by rfl⟩) R823769
theorem R221831 : Reach 221831 := rs (se 1 (by rfl) ⟨166373, by rfl⟩) R332747
theorem R90953 : Reach 90953 := rs (se 2 (by rfl) ⟨34107, by rfl⟩) R68215
theorem R156599 : Reach 156599 := rs (se 1 (by rfl) ⟨117449, by rfl⟩) R234899
theorem R320759 : Reach 320759 := rs (se 1 (by rfl) ⟨240569, by rfl⟩) R481139
theorem R58799 : Reach 58799 := rs (se 1 (by rfl) ⟨44099, by rfl⟩) R88199
theorem R58843 : Reach 58843 := rs (se 1 (by rfl) ⟨44132, by rfl⟩) R88265
theorem R58889 : Reach 58889 := rs (se 2 (by rfl) ⟨22083, by rfl⟩) R44167
theorem R58919 : Reach 58919 := rs (se 1 (by rfl) ⟨44189, by rfl⟩) R88379
theorem R91745 : Reach 91745 := rs (se 2 (by rfl) ⟨34404, by rfl⟩) R68809
theorem R59003 : Reach 59003 := rs (se 1 (by rfl) ⟨44252, by rfl⟩) R88505
theorem R255635 : Reach 255635 := rs (se 1 (by rfl) ⟨191726, by rfl⟩) R383453
theorem R157373 : Reach 157373 := rs (se 3 (by rfl) ⟨29507, by rfl⟩) R59015
theorem R91847 : Reach 91847 := rs (se 1 (by rfl) ⟨68885, by rfl⟩) R137771
theorem R321245 : Reach 321245 := rs (se 3 (by rfl) ⟨60233, by rfl⟩) R120467
theorem R59129 : Reach 59129 := rs (se 2 (by rfl) ⟨22173, by rfl⟩) R44347
theorem R190201 : Reach 190201 := rs (se 2 (by rfl) ⟨71325, by rfl⟩) R142651
theorem R59231 : Reach 59231 := rs (se 1 (by rfl) ⟨44423, by rfl⟩) R88847
theorem R59243 : Reach 59243 := rs (se 1 (by rfl) ⟨44432, by rfl⟩) R88865
theorem R92087 : Reach 92087 := rs (se 1 (by rfl) ⟨69065, by rfl⟩) R138131
theorem R59471 : Reach 59471 := rs (se 1 (by rfl) ⟨44603, by rfl⟩) R89207
theorem R59591 : Reach 59591 := rs (se 1 (by rfl) ⟨44693, by rfl⟩) R89387
theorem R747863 : Reach 747863 := rs (se 1 (by rfl) ⟨560897, by rfl⟩) R1121795
theorem R59753 : Reach 59753 := rs (se 2 (by rfl) ⟨22407, by rfl⟩) R44815
theorem R158057 : Reach 158057 := rs (se 2 (by rfl) ⟨59271, by rfl⟩) R118543
theorem R125327 : Reach 125327 := rs (se 1 (by rfl) ⟨93995, by rfl⟩) R187991
theorem R59831 : Reach 59831 := rs (se 1 (by rfl) ⟨44873, by rfl⟩) R89747
theorem R59867 : Reach 59867 := rs (se 1 (by rfl) ⟨44900, by rfl⟩) R89801
theorem R92681 : Reach 92681 := rs (se 2 (by rfl) ⟨34755, by rfl⟩) R69511
theorem R125479 : Reach 125479 := rs (se 1 (by rfl) ⟨94109, by rfl⟩) R188219
theorem R1076003 : Reach 1076003 := rs (se 1 (by rfl) ⟨807002, by rfl⟩) R1614005
theorem R93023 : Reach 93023 := rs (se 1 (by rfl) ⟨69767, by rfl⟩) R139535
theorem R60335 : Reach 60335 := rs (se 1 (by rfl) ⟨45251, by rfl⟩) R90503
theorem R60425 : Reach 60425 := rs (se 2 (by rfl) ⟨22659, by rfl⟩) R45319
theorem R93203 : Reach 93203 := rs (se 1 (by rfl) ⟨69902, by rfl⟩) R139805
theorem R60455 : Reach 60455 := rs (se 1 (by rfl) ⟨45341, by rfl⟩) R90683
theorem R60539 : Reach 60539 := rs (se 1 (by rfl) ⟨45404, by rfl⟩) R90809
theorem R715969 : Reach 715969 := rs (se 2 (by rfl) ⟨268488, by rfl⟩) R536977
theorem R60665 : Reach 60665 := rs (se 2 (by rfl) ⟨22749, by rfl⟩) R45499
theorem R60767 : Reach 60767 := rs (se 1 (by rfl) ⟨45575, by rfl⟩) R91151
theorem R93545 : Reach 93545 := rs (se 2 (by rfl) ⟨35079, by rfl⟩) R70159
theorem R60779 : Reach 60779 := rs (se 1 (by rfl) ⟨45584, by rfl⟩) R91169
theorem R61007 : Reach 61007 := rs (se 1 (by rfl) ⟨45755, by rfl⟩) R91511
theorem R2289239 : Reach 2289239 := rs (se 1 (by rfl) ⟨1716929, by rfl⟩) R3433859
theorem R61127 : Reach 61127 := rs (se 1 (by rfl) ⟨45845, by rfl⟩) R91691
theorem R61289 : Reach 61289 := rs (se 2 (by rfl) ⟨22983, by rfl⟩) R45967
theorem R126839 : Reach 126839 := rs (se 1 (by rfl) ⟨95129, by rfl⟩) R190259
theorem R61367 : Reach 61367 := rs (se 1 (by rfl) ⟨46025, by rfl⟩) R92051
theorem R94139 : Reach 94139 := rs (se 1 (by rfl) ⟨70604, by rfl⟩) R141209
theorem R192449 : Reach 192449 := rs (se 2 (by rfl) ⟨72168, by rfl⟩) R144337
theorem R61403 : Reach 61403 := rs (se 1 (by rfl) ⟨46052, by rfl⟩) R92105
theorem R94265 : Reach 94265 := rs (se 2 (by rfl) ⟨35349, by rfl⟩) R70699
theorem R127223 : Reach 127223 := rs (se 1 (by rfl) ⟨95417, by rfl⟩) R190835
theorem R94607 : Reach 94607 := rs (se 1 (by rfl) ⟨70955, by rfl⟩) R141911
theorem R61871 : Reach 61871 := rs (se 1 (by rfl) ⟨46403, by rfl⟩) R92807
theorem R61883 : Reach 61883 := rs (se 1 (by rfl) ⟨46412, by rfl⟩) R92825
theorem R61961 : Reach 61961 := rs (se 2 (by rfl) ⟨23235, by rfl⟩) R46471
theorem R160289 : Reach 160289 := rs (se 2 (by rfl) ⟨60108, by rfl⟩) R120217
theorem R61991 : Reach 61991 := rs (se 1 (by rfl) ⟨46493, by rfl⟩) R92987
theorem R62009 : Reach 62009 := rs (se 2 (by rfl) ⟨23253, by rfl⟩) R46507
theorem R324155 : Reach 324155 := rs (se 1 (by rfl) ⟨243116, by rfl⟩) R486233
theorem R62075 : Reach 62075 := rs (se 1 (by rfl) ⟨46556, by rfl⟩) R93113
theorem R94859 : Reach 94859 := rs (se 1 (by rfl) ⟨71144, by rfl⟩) R142289
theorem R62123 : Reach 62123 := rs (se 1 (by rfl) ⟨46592, by rfl⟩) R93185
theorem R94931 : Reach 94931 := rs (se 1 (by rfl) ⟨71198, by rfl⟩) R142397
theorem R62201 : Reach 62201 := rs (se 2 (by rfl) ⟨23325, by rfl⟩) R46651
theorem R881425 : Reach 881425 := rs (se 2 (by rfl) ⟨330534, by rfl⟩) R661069
theorem R62303 : Reach 62303 := rs (se 1 (by rfl) ⟨46727, by rfl⟩) R93455
theorem R62315 : Reach 62315 := rs (se 1 (by rfl) ⟨46736, by rfl⟩) R93473
theorem R62351 : Reach 62351 := rs (se 1 (by rfl) ⟨46763, by rfl⟩) R93527
theorem R62471 : Reach 62471 := rs (se 1 (by rfl) ⟨46853, by rfl⟩) R93707
theorem R160775 : Reach 160775 := rs (se 1 (by rfl) ⟨120581, by rfl⟩) R241163
theorem R62543 : Reach 62543 := rs (se 1 (by rfl) ⟨46907, by rfl⟩) R93815
theorem R62663 : Reach 62663 := rs (se 1 (by rfl) ⟨46997, by rfl⟩) R93995
theorem R62711 : Reach 62711 := rs (se 1 (by rfl) ⟨47033, by rfl⟩) R94067
theorem R226583 : Reach 226583 := rs (se 1 (by rfl) ⟨169937, by rfl⟩) R339875
theorem R62825 : Reach 62825 := rs (se 2 (by rfl) ⟨23559, by rfl⟩) R47119
theorem R62903 : Reach 62903 := rs (se 1 (by rfl) ⟨47177, by rfl⟩) R94355
theorem R587209 : Reach 587209 := rs (se 2 (by rfl) ⟨220203, by rfl⟩) R440407
theorem R62939 : Reach 62939 := rs (se 1 (by rfl) ⟨47204, by rfl⟩) R94409
theorem R161261 : Reach 161261 := rs (se 3 (by rfl) ⟨30236, by rfl⟩) R60473
theorem R95867 : Reach 95867 := rs (se 1 (by rfl) ⟨71900, by rfl⟩) R143801
theorem R95993 : Reach 95993 := rs (se 2 (by rfl) ⟨35997, by rfl⟩) R71995
theorem R63305 : Reach 63305 := rs (se 2 (by rfl) ⟨23739, by rfl⟩) R47479
theorem R63407 : Reach 63407 := rs (se 1 (by rfl) ⟨47555, by rfl⟩) R95111
theorem R63419 : Reach 63419 := rs (se 1 (by rfl) ⟨47564, by rfl⟩) R95129
theorem R96263 : Reach 96263 := rs (se 1 (by rfl) ⟨72197, by rfl⟩) R144395
theorem R63497 : Reach 63497 := rs (se 2 (by rfl) ⟨23811, by rfl⟩) R47623
theorem R63527 : Reach 63527 := rs (se 1 (by rfl) ⟨47645, by rfl⟩) R95291
theorem R63545 : Reach 63545 := rs (se 2 (by rfl) ⟨23829, by rfl⟩) R47659
theorem R96335 : Reach 96335 := rs (se 1 (by rfl) ⟨72251, by rfl⟩) R144503
theorem R260185 : Reach 260185 := rs (se 2 (by rfl) ⟨97569, by rfl⟩) R195139
theorem R63611 : Reach 63611 := rs (se 1 (by rfl) ⟨47708, by rfl⟩) R95417
theorem R161945 : Reach 161945 := rs (se 2 (by rfl) ⟨60729, by rfl⟩) R121459
theorem R325795 : Reach 325795 := rs (se 1 (by rfl) ⟨244346, by rfl⟩) R488693
theorem R63659 : Reach 63659 := rs (se 1 (by rfl) ⟨47744, by rfl⟩) R95489
theorem R63737 : Reach 63737 := rs (se 2 (by rfl) ⟨23901, by rfl⟩) R47803
theorem R63839 : Reach 63839 := rs (se 1 (by rfl) ⟨47879, by rfl⟩) R95759
theorem R63851 : Reach 63851 := rs (se 1 (by rfl) ⟨47888, by rfl⟩) R95777
theorem R96641 : Reach 96641 := rs (se 2 (by rfl) ⟨36240, by rfl⟩) R72481
theorem R63887 : Reach 63887 := rs (se 1 (by rfl) ⟨47915, by rfl⟩) R95831
theorem R588185 : Reach 588185 := rs (se 2 (by rfl) ⟨220569, by rfl⟩) R441139
theorem R63919 : Reach 63919 := rs (se 1 (by rfl) ⟨47939, by rfl⟩) R95879
theorem R96731 : Reach 96731 := rs (se 1 (by rfl) ⟨72548, by rfl⟩) R145097
theorem R64007 : Reach 64007 := rs (se 1 (by rfl) ⟨48005, by rfl⟩) R96011
theorem R64079 : Reach 64079 := rs (se 1 (by rfl) ⟨48059, by rfl⟩) R96119
theorem R129671 : Reach 129671 := rs (se 1 (by rfl) ⟨97253, by rfl⟩) R194507
theorem R162443 : Reach 162443 := rs (se 1 (by rfl) ⟨121832, by rfl⟩) R243665
theorem R129683 : Reach 129683 := rs (se 1 (by rfl) ⟨97262, by rfl⟩) R194525
theorem R64199 : Reach 64199 := rs (se 1 (by rfl) ⟨48149, by rfl⟩) R96299
theorem R96983 : Reach 96983 := rs (se 1 (by rfl) ⟨72737, by rfl⟩) R145475
theorem R64247 : Reach 64247 := rs (se 1 (by rfl) ⟨48185, by rfl⟩) R96371
theorem R64361 : Reach 64361 := rs (se 2 (by rfl) ⟨24135, by rfl⟩) R48271
theorem R64439 : Reach 64439 := rs (se 1 (by rfl) ⟨48329, by rfl⟩) R96659
theorem R64475 : Reach 64475 := rs (se 1 (by rfl) ⟨48356, by rfl⟩) R96713
theorem R1276901 : Reach 1276901 := rs (se 4 (by rfl) ⟨119709, by rfl⟩) R239419
theorem R162931 : Reach 162931 := rs (se 1 (by rfl) ⟨122198, by rfl⟩) R244397
theorem R327077 : Reach 327077 := rs (se 4 (by rfl) ⟨30663, by rfl⟩) R61327
theorem R65195 : Reach 65195 := rs (se 1 (by rfl) ⟨48896, by rfl⟩) R97793
theorem R130859 : Reach 130859 := rs (se 1 (by rfl) ⟨98144, by rfl⟩) R196289
theorem R163691 : Reach 163691 := rs (se 1 (by rfl) ⟨122768, by rfl⟩) R245537
theorem R262075 : Reach 262075 := rs (se 1 (by rfl) ⟨196556, by rfl⟩) R393113
theorem R262601 : Reach 262601 := rs (se 2 (by rfl) ⟨98475, by rfl⟩) R196951
theorem R295595 : Reach 295595 := rs (se 1 (by rfl) ⟨221696, by rfl⟩) R443393
theorem R393943 : Reach 393943 := rs (se 1 (by rfl) ⟨295457, by rfl⟩) R590915
theorem R66271 : Reach 66271 := rs (se 1 (by rfl) ⟨49703, by rfl⟩) R99407
theorem R99215 : Reach 99215 := rs (se 1 (by rfl) ⟨74411, by rfl⟩) R148823
theorem R66703 : Reach 66703 := rs (se 1 (by rfl) ⟨50027, by rfl⟩) R100055
theorem R66953 : Reach 66953 := rs (se 2 (by rfl) ⟨25107, by rfl⟩) R50215
theorem R198125 : Reach 198125 := rs (se 3 (by rfl) ⟨37148, by rfl⟩) R74297
theorem R394739 : Reach 394739 := rs (se 1 (by rfl) ⟨296054, by rfl⟩) R592109
theorem R100075 : Reach 100075 := rs (se 1 (by rfl) ⟨75056, by rfl⟩) R150113
theorem R67385 : Reach 67385 := rs (se 2 (by rfl) ⟨25269, by rfl⟩) R50539
theorem R460727 : Reach 460727 := rs (se 1 (by rfl) ⟨345545, by rfl⟩) R691091
theorem R395279 : Reach 395279 := rs (se 1 (by rfl) ⟨296459, by rfl⟩) R592919
theorem R133373 : Reach 133373 := rs (se 3 (by rfl) ⟨25007, by rfl⟩) R50015
theorem R198935 : Reach 198935 := rs (se 1 (by rfl) ⟨149201, by rfl⟩) R298403
theorem R133487 : Reach 133487 := rs (se 1 (by rfl) ⟨100115, by rfl⟩) R200231
theorem R2296349 : Reach 2296349 := rs (se 3 (by rfl) ⟨430565, by rfl⟩) R861131
theorem R101047 : Reach 101047 := rs (se 1 (by rfl) ⟨75785, by rfl⟩) R151571
theorem R68431 : Reach 68431 := rs (se 1 (by rfl) ⟨51323, by rfl⟩) R102647
theorem R101351 : Reach 101351 := rs (se 1 (by rfl) ⟨76013, by rfl⟩) R152027
theorem R69113 : Reach 69113 := rs (se 2 (by rfl) ⟨25917, by rfl⟩) R51835
theorem R134891 : Reach 134891 := rs (se 1 (by rfl) ⟨101168, by rfl⟩) R202337
theorem R69383 : Reach 69383 := rs (se 1 (by rfl) ⟨52037, by rfl⟩) R104075
theorem R200555 : Reach 200555 := rs (se 1 (by rfl) ⟨150416, by rfl⟩) R300833
theorem R102505 : Reach 102505 := rs (se 2 (by rfl) ⟨38439, by rfl⟩) R76879
theorem R954625 : Reach 954625 := rs (se 2 (by rfl) ⟨357984, by rfl⟩) R715969
theorem R70139 : Reach 70139 := rs (se 1 (by rfl) ⟨52604, by rfl⟩) R105209
theorem R102991 : Reach 102991 := rs (se 1 (by rfl) ⟨77243, by rfl⟩) R154487
theorem R135863 : Reach 135863 := rs (se 1 (by rfl) ⟨101897, by rfl⟩) R203795
theorem R266951 : Reach 266951 := rs (se 1 (by rfl) ⟨200213, by rfl⟩) R400427
theorem R168671 : Reach 168671 := rs (se 1 (by rfl) ⟨126503, by rfl⟩) R253007
theorem R398047 : Reach 398047 := rs (se 1 (by rfl) ⟨298535, by rfl⟩) R597071
theorem R70571 : Reach 70571 := rs (se 1 (by rfl) ⟨52928, by rfl⟩) R105857
theorem R267209 : Reach 267209 := rs (se 2 (by rfl) ⟨100203, by rfl⟩) R200407
theorem R103639 : Reach 103639 := rs (se 1 (by rfl) ⟨77729, by rfl⟩) R155459
theorem R71111 : Reach 71111 := rs (se 1 (by rfl) ⟨53333, by rfl⟩) R106667
theorem R103943 : Reach 103943 := rs (se 1 (by rfl) ⟨77957, by rfl⟩) R155915
theorem R366119 : Reach 366119 := rs (se 1 (by rfl) ⟨274589, by rfl⟩) R549179
theorem R104399 : Reach 104399 := rs (se 1 (by rfl) ⟨78299, by rfl⟩) R156599
theorem R203033 : Reach 203033 := rs (se 2 (by rfl) ⟨76137, by rfl⟩) R152275
theorem R137501 : Reach 137501 := rs (se 3 (by rfl) ⟨25781, by rfl⟩) R51563
theorem R39199 : Reach 39199 := rs (se 1 (by rfl) ⟨29399, by rfl⟩) R58799
theorem R39259 : Reach 39259 := rs (se 1 (by rfl) ⟨29444, by rfl⟩) R58889
theorem R39279 : Reach 39279 := rs (se 1 (by rfl) ⟨29459, by rfl⟩) R58919
theorem R39335 : Reach 39335 := rs (se 1 (by rfl) ⟨29501, by rfl⟩) R59003
theorem R72103 : Reach 72103 := rs (se 1 (by rfl) ⟨54077, by rfl⟩) R108155
theorem R170423 : Reach 170423 := rs (se 1 (by rfl) ⟨127817, by rfl⟩) R255635
theorem R104915 : Reach 104915 := rs (se 1 (by rfl) ⟨78686, by rfl⟩) R157373
theorem R39419 : Reach 39419 := rs (se 1 (by rfl) ⟨29564, by rfl⟩) R59129
theorem R39487 : Reach 39487 := rs (se 1 (by rfl) ⟨29615, by rfl⟩) R59231
theorem R39495 : Reach 39495 := rs (se 1 (by rfl) ⟨29621, by rfl⟩) R59243
theorem R236105 : Reach 236105 := rs (se 2 (by rfl) ⟨88539, by rfl⟩) R177079
theorem R72265 : Reach 72265 := rs (se 2 (by rfl) ⟨27099, by rfl⟩) R54199
theorem R137807 : Reach 137807 := rs (se 1 (by rfl) ⟨103355, by rfl⟩) R206711
theorem R72299 : Reach 72299 := rs (se 1 (by rfl) ⟨54224, by rfl⟩) R108449
theorem R334475 : Reach 334475 := rs (se 1 (by rfl) ⟨250856, by rfl⟩) R501713
theorem R39647 : Reach 39647 := rs (se 1 (by rfl) ⟨29735, by rfl⟩) R59471
theorem R301805 : Reach 301805 := rs (se 3 (by rfl) ⟨56588, by rfl⟩) R113177
theorem R203543 : Reach 203543 := rs (se 1 (by rfl) ⟨152657, by rfl⟩) R305315
theorem R39727 : Reach 39727 := rs (se 1 (by rfl) ⟨29795, by rfl⟩) R59591
theorem R498575 : Reach 498575 := rs (se 1 (by rfl) ⟨373931, by rfl⟩) R747863
theorem R39835 : Reach 39835 := rs (se 1 (by rfl) ⟨29876, by rfl⟩) R59753
theorem R105371 : Reach 105371 := rs (se 1 (by rfl) ⟨79028, by rfl⟩) R158057
theorem R39887 : Reach 39887 := rs (se 1 (by rfl) ⟨29915, by rfl⟩) R59831
theorem R39911 : Reach 39911 := rs (se 1 (by rfl) ⟨29933, by rfl⟩) R59867
theorem R433181 : Reach 433181 := rs (se 3 (by rfl) ⟨81221, by rfl⟩) R162443
theorem R40223 : Reach 40223 := rs (se 1 (by rfl) ⟨30167, by rfl⟩) R60335
theorem R40283 : Reach 40283 := rs (se 1 (by rfl) ⟨30212, by rfl⟩) R60425
theorem R40303 : Reach 40303 := rs (se 1 (by rfl) ⟨30227, by rfl⟩) R60455
theorem R40359 : Reach 40359 := rs (se 1 (by rfl) ⟨30269, by rfl⟩) R60539
theorem R204281 : Reach 204281 := rs (se 2 (by rfl) ⟨76605, by rfl⟩) R153211
theorem R40443 : Reach 40443 := rs (se 1 (by rfl) ⟨30332, by rfl⟩) R60665
theorem R400889 : Reach 400889 := rs (se 2 (by rfl) ⟨150333, by rfl⟩) R300667
theorem R40511 : Reach 40511 := rs (se 1 (by rfl) ⟨30383, by rfl⟩) R60767
theorem R40519 : Reach 40519 := rs (se 1 (by rfl) ⟨30389, by rfl⟩) R60779
theorem R401041 : Reach 401041 := rs (se 2 (by rfl) ⟨150390, by rfl⟩) R300781
theorem R40671 : Reach 40671 := rs (se 1 (by rfl) ⟨30503, by rfl⟩) R61007
theorem R139049 : Reach 139049 := rs (se 2 (by rfl) ⟨52143, by rfl⟩) R104287
theorem R40751 : Reach 40751 := rs (se 1 (by rfl) ⟨30563, by rfl⟩) R61127
theorem R204605 : Reach 204605 := rs (se 3 (by rfl) ⟨38363, by rfl⟩) R76727
theorem R40859 : Reach 40859 := rs (se 1 (by rfl) ⟨30644, by rfl⟩) R61289
theorem R40911 : Reach 40911 := rs (se 1 (by rfl) ⟨30683, by rfl⟩) R61367
theorem R40935 : Reach 40935 := rs (se 1 (by rfl) ⟨30701, by rfl⟩) R61403
theorem R106505 : Reach 106505 := rs (se 2 (by rfl) ⟨39939, by rfl⟩) R79879
theorem R467153 : Reach 467153 := rs (se 2 (by rfl) ⟨175182, by rfl⟩) R350365
theorem R434393 : Reach 434393 := rs (se 2 (by rfl) ⟨162897, by rfl⟩) R325795
theorem R41247 : Reach 41247 := rs (se 1 (by rfl) ⟨30935, by rfl⟩) R61871
theorem R41255 : Reach 41255 := rs (se 1 (by rfl) ⟨30941, by rfl⟩) R61883
theorem R41307 : Reach 41307 := rs (se 1 (by rfl) ⟨30980, by rfl⟩) R61961
theorem R106859 : Reach 106859 := rs (se 1 (by rfl) ⟨80144, by rfl⟩) R160289
theorem R41327 : Reach 41327 := rs (se 1 (by rfl) ⟨30995, by rfl⟩) R61991
theorem R41339 : Reach 41339 := rs (se 1 (by rfl) ⟨31004, by rfl⟩) R62009
theorem R41383 : Reach 41383 := rs (se 1 (by rfl) ⟨31037, by rfl⟩) R62075
theorem R41415 : Reach 41415 := rs (se 1 (by rfl) ⟨31061, by rfl⟩) R62123
theorem R41467 : Reach 41467 := rs (se 1 (by rfl) ⟨31100, by rfl⟩) R62201
theorem R41535 : Reach 41535 := rs (se 1 (by rfl) ⟨31151, by rfl⟩) R62303
theorem R41543 : Reach 41543 := rs (se 1 (by rfl) ⟨31157, by rfl⟩) R62315
theorem R41567 : Reach 41567 := rs (se 1 (by rfl) ⟨31175, by rfl⟩) R62351
theorem R107129 : Reach 107129 := rs (se 2 (by rfl) ⟨40173, by rfl⟩) R80347
theorem R41647 : Reach 41647 := rs (se 1 (by rfl) ⟨31235, by rfl⟩) R62471
theorem R107183 : Reach 107183 := rs (se 1 (by rfl) ⟨80387, by rfl⟩) R160775
theorem R41695 : Reach 41695 := rs (se 1 (by rfl) ⟨31271, by rfl⟩) R62543
theorem R41775 : Reach 41775 := rs (se 1 (by rfl) ⟨31331, by rfl⟩) R62663
theorem R41807 : Reach 41807 := rs (se 1 (by rfl) ⟨31355, by rfl⟩) R62711
theorem R41883 : Reach 41883 := rs (se 1 (by rfl) ⟨31412, by rfl⟩) R62825
theorem R41935 : Reach 41935 := rs (se 1 (by rfl) ⟨31451, by rfl⟩) R62903
theorem R41959 : Reach 41959 := rs (se 1 (by rfl) ⟨31469, by rfl⟩) R62939
theorem R107507 : Reach 107507 := rs (se 1 (by rfl) ⟨80630, by rfl⟩) R161261
theorem R42203 : Reach 42203 := rs (se 1 (by rfl) ⟨31652, by rfl⟩) R63305
theorem R206057 : Reach 206057 := rs (se 2 (by rfl) ⟨77271, by rfl⟩) R154543
theorem R42271 : Reach 42271 := rs (se 1 (by rfl) ⟨31703, by rfl⟩) R63407
theorem R42279 : Reach 42279 := rs (se 1 (by rfl) ⟨31709, by rfl⟩) R63419
theorem R271667 : Reach 271667 := rs (se 1 (by rfl) ⟨203750, by rfl⟩) R407501
theorem R42331 : Reach 42331 := rs (se 1 (by rfl) ⟨31748, by rfl⟩) R63497
theorem R42351 : Reach 42351 := rs (se 1 (by rfl) ⟨31763, by rfl⟩) R63527
theorem R42363 : Reach 42363 := rs (se 1 (by rfl) ⟨31772, by rfl⟩) R63545
theorem R42407 : Reach 42407 := rs (se 1 (by rfl) ⟨31805, by rfl⟩) R63611
theorem R107963 : Reach 107963 := rs (se 1 (by rfl) ⟨80972, by rfl⟩) R161945
theorem R42439 : Reach 42439 := rs (se 1 (by rfl) ⟨31829, by rfl⟩) R63659
theorem R42491 : Reach 42491 := rs (se 1 (by rfl) ⟨31868, by rfl⟩) R63737
theorem R42559 : Reach 42559 := rs (se 1 (by rfl) ⟨31919, by rfl⟩) R63839
theorem R42567 : Reach 42567 := rs (se 1 (by rfl) ⟨31925, by rfl⟩) R63851
theorem R42591 : Reach 42591 := rs (se 1 (by rfl) ⟨31943, by rfl⟩) R63887
theorem R42671 : Reach 42671 := rs (se 1 (by rfl) ⟨32003, by rfl⟩) R64007
theorem R42719 : Reach 42719 := rs (se 1 (by rfl) ⟨32039, by rfl⟩) R64079
theorem R42799 : Reach 42799 := rs (se 1 (by rfl) ⟨32099, by rfl⟩) R64199
theorem R42831 : Reach 42831 := rs (se 1 (by rfl) ⟨32123, by rfl⟩) R64247
theorem R42907 : Reach 42907 := rs (se 1 (by rfl) ⟨32180, by rfl⟩) R64361
theorem R141263 : Reach 141263 := rs (se 1 (by rfl) ⟨105947, by rfl⟩) R211895
theorem R42959 : Reach 42959 := rs (se 1 (by rfl) ⟨32219, by rfl⟩) R64439
theorem R42983 : Reach 42983 := rs (se 1 (by rfl) ⟨32237, by rfl⟩) R64475
theorem R43463 : Reach 43463 := rs (se 1 (by rfl) ⟨32597, by rfl⟩) R65195
theorem R109127 : Reach 109127 := rs (se 1 (by rfl) ⟨81845, by rfl⟩) R163691
theorem R142019 : Reach 142019 := rs (se 1 (by rfl) ⟨106514, by rfl⟩) R213029
theorem R404291 : Reach 404291 := rs (se 1 (by rfl) ⟨303218, by rfl⟩) R606437
theorem R207683 : Reach 207683 := rs (se 1 (by rfl) ⟨155762, by rfl⟩) R311525
theorem R142235 : Reach 142235 := rs (se 1 (by rfl) ⟨106676, by rfl⟩) R213353
theorem R1387651 : Reach 1387651 := rs (se 1 (by rfl) ⟨1040738, by rfl⟩) R2081477
theorem R109757 : Reach 109757 := rs (se 3 (by rfl) ⟨20579, by rfl⟩) R41159
theorem R44455 : Reach 44455 := rs (se 1 (by rfl) ⟨33341, by rfl⟩) R66683
theorem R208493 : Reach 208493 := rs (se 3 (by rfl) ⟨39092, by rfl⟩) R78185
theorem R143111 : Reach 143111 := rs (se 1 (by rfl) ⟨107333, by rfl⟩) R214667
theorem R143261 : Reach 143261 := rs (se 3 (by rfl) ⟨26861, by rfl⟩) R53723
theorem R45031 : Reach 45031 := rs (se 1 (by rfl) ⟨33773, by rfl⟩) R67547
theorem R143369 : Reach 143369 := rs (se 2 (by rfl) ⟨53763, by rfl⟩) R107527
theorem R307471 : Reach 307471 := rs (se 1 (by rfl) ⟨230603, by rfl⟩) R461207
theorem R45479 : Reach 45479 := rs (se 1 (by rfl) ⟨34109, by rfl⟩) R68219
theorem R176737 : Reach 176737 := rs (se 2 (by rfl) ⟨66276, by rfl⟩) R132553
theorem R78457 : Reach 78457 := rs (se 2 (by rfl) ⟨29421, by rfl⟩) R58843
theorem R78671 : Reach 78671 := rs (se 1 (by rfl) ⟨59003, by rfl⟩) R118007
theorem R78823 : Reach 78823 := rs (se 1 (by rfl) ⟨59117, by rfl⟩) R118235
theorem R144509 : Reach 144509 := rs (se 3 (by rfl) ⟨27095, by rfl⟩) R54191
theorem R46459 : Reach 46459 := rs (se 1 (by rfl) ⟨34844, by rfl⟩) R69689
theorem R3225091 : Reach 3225091 := rs (se 1 (by rfl) ⟨2418818, by rfl⟩) R4837637
theorem R669221 : Reach 669221 := rs (se 4 (by rfl) ⟨62739, by rfl⟩) R125479
theorem R46687 : Reach 46687 := rs (se 1 (by rfl) ⟨35015, by rfl⟩) R70031
theorem R276155 : Reach 276155 := rs (se 1 (by rfl) ⟨207116, by rfl⟩) R414233
theorem R46903 : Reach 46903 := rs (se 1 (by rfl) ⟨35177, by rfl⟩) R70355
theorem R112921 : Reach 112921 := rs (se 2 (by rfl) ⟨42345, by rfl⟩) R84691
theorem R309581 : Reach 309581 := rs (se 3 (by rfl) ⟨58046, by rfl⟩) R116093
theorem R47839 : Reach 47839 := rs (se 1 (by rfl) ⟨35879, by rfl⟩) R71759
theorem R277627 : Reach 277627 := rs (se 1 (by rfl) ⟨208220, by rfl⟩) R416441
theorem R48415 : Reach 48415 := rs (se 1 (by rfl) ⟨36311, by rfl⟩) R72623
theorem R114169 : Reach 114169 := rs (se 2 (by rfl) ⟨42813, by rfl⟩) R85627
theorem R147887 : Reach 147887 := rs (se 1 (by rfl) ⟨110915, by rfl⟩) R221831
theorem R180737 : Reach 180737 := rs (se 2 (by rfl) ⟨67776, by rfl⟩) R135553
theorem R312011 : Reach 312011 := rs (se 1 (by rfl) ⟨234008, by rfl⟩) R468017
theorem R213839 : Reach 213839 := rs (se 1 (by rfl) ⟨160379, by rfl⟩) R320759
theorem R246721 : Reach 246721 := rs (se 2 (by rfl) ⟨92520, by rfl⟩) R185041
theorem R214163 : Reach 214163 := rs (se 1 (by rfl) ⟨160622, by rfl⟩) R321245
theorem R83551 : Reach 83551 := rs (se 1 (by rfl) ⟨62663, by rfl⟩) R125327
theorem R50863 : Reach 50863 := rs (se 1 (by rfl) ⟨38147, by rfl⟩) R76295
theorem R378769 : Reach 378769 := rs (se 2 (by rfl) ⟨142038, by rfl⟩) R284077
theorem R379073 : Reach 379073 := rs (se 2 (by rfl) ⟨142152, by rfl⟩) R284305
theorem R1526159 : Reach 1526159 := rs (se 1 (by rfl) ⟨1144619, by rfl⟩) R2289239
theorem R84559 : Reach 84559 := rs (se 1 (by rfl) ⟨63419, by rfl⟩) R126839
theorem R346913 : Reach 346913 := rs (se 2 (by rfl) ⟨130092, by rfl⟩) R260185
theorem R84815 : Reach 84815 := rs (se 1 (by rfl) ⟨63611, by rfl⟩) R127223
theorem R216103 : Reach 216103 := rs (se 1 (by rfl) ⟨162077, by rfl⟩) R324155
theorem R85225 : Reach 85225 := rs (se 2 (by rfl) ⟨31959, by rfl⟩) R63919
theorem R151055 : Reach 151055 := rs (se 1 (by rfl) ⟨113291, by rfl⟩) R226583
theorem R52807 : Reach 52807 := rs (se 1 (by rfl) ⟨39605, by rfl⟩) R79211
theorem R151577 : Reach 151577 := rs (se 2 (by rfl) ⟨56841, by rfl⟩) R113683
theorem R217241 : Reach 217241 := rs (se 2 (by rfl) ⟨81465, by rfl⟩) R162931
theorem R381131 : Reach 381131 := rs (se 1 (by rfl) ⟨285848, by rfl⟩) R571697
theorem R53627 : Reach 53627 := rs (se 1 (by rfl) ⟨40220, by rfl⟩) R80441
theorem R86447 : Reach 86447 := rs (se 1 (by rfl) ⟨64835, by rfl⟩) R129671
theorem R86455 : Reach 86455 := rs (se 1 (by rfl) ⟨64841, by rfl⟩) R129683
theorem R1102325 : Reach 1102325 := rs (se 5 (by rfl) ⟨51671, by rfl⟩) R103343
theorem R218051 : Reach 218051 := rs (se 1 (by rfl) ⟨163538, by rfl⟩) R327077
theorem R250937 : Reach 250937 := rs (se 2 (by rfl) ⟨94101, by rfl⟩) R188203
theorem R87239 : Reach 87239 := rs (se 1 (by rfl) ⟨65429, by rfl⟩) R130859
theorem R382201 : Reach 382201 := rs (se 2 (by rfl) ⟨143325, by rfl⟩) R286651
theorem R349433 : Reach 349433 := rs (se 2 (by rfl) ⟨131037, by rfl⟩) R262075
theorem R349733 : Reach 349733 := rs (se 4 (by rfl) ⟨32787, by rfl⟩) R65575
theorem R54847 : Reach 54847 := rs (se 1 (by rfl) ⟨41135, by rfl⟩) R82271
theorem R87635 : Reach 87635 := rs (se 1 (by rfl) ⟨65726, by rfl⟩) R131453
theorem R88073 : Reach 88073 := rs (se 2 (by rfl) ⟨33027, by rfl⟩) R66055
theorem R186401 : Reach 186401 := rs (se 2 (by rfl) ⟨69900, by rfl⟩) R139801
theorem R88487 : Reach 88487 := rs (se 1 (by rfl) ⟨66365, by rfl⟩) R132731
theorem R88595 : Reach 88595 := rs (se 1 (by rfl) ⟨66446, by rfl⟩) R132893
theorem R449063 : Reach 449063 := rs (se 1 (by rfl) ⟨336797, by rfl⟩) R673595
theorem R88649 : Reach 88649 := rs (se 2 (by rfl) ⟨33243, by rfl⟩) R66487
theorem R55991 : Reach 55991 := rs (se 1 (by rfl) ⟨41993, by rfl⟩) R83987
theorem R89063 : Reach 89063 := rs (se 1 (by rfl) ⟨66797, by rfl⟩) R133595
theorem R711665 : Reach 711665 := rs (se 2 (by rfl) ⟨266874, by rfl⟩) R533749
theorem R286019 : Reach 286019 := rs (se 1 (by rfl) ⟨214514, by rfl⟩) R429029
theorem R89441 : Reach 89441 := rs (se 2 (by rfl) ⟨33540, by rfl⟩) R67081
theorem R220553 : Reach 220553 := rs (se 2 (by rfl) ⟨82707, by rfl⟩) R165415
theorem R89531 : Reach 89531 := rs (se 1 (by rfl) ⟨67148, by rfl⟩) R134297
theorem R89657 : Reach 89657 := rs (se 2 (by rfl) ⟨33621, by rfl⟩) R67243
theorem R253601 : Reach 253601 := rs (se 2 (by rfl) ⟨95100, by rfl⟩) R190201
theorem R57067 : Reach 57067 := rs (se 1 (by rfl) ⟨42800, by rfl⟩) R85601
theorem R188335 : Reach 188335 := rs (se 1 (by rfl) ⟨141251, by rfl⟩) R282503
theorem R548801 : Reach 548801 := rs (se 2 (by rfl) ⟨205800, by rfl⟩) R411601
theorem R679873 : Reach 679873 := rs (se 2 (by rfl) ⟨254952, by rfl⟩) R509905
theorem R57295 : Reach 57295 := rs (se 1 (by rfl) ⟨42971, by rfl⟩) R85943
theorem R57449 : Reach 57449 := rs (se 2 (by rfl) ⟨21543, by rfl⟩) R43087
theorem R90323 : Reach 90323 := rs (se 1 (by rfl) ⟨67742, by rfl⟩) R135485
theorem R90377 : Reach 90377 := rs (se 2 (by rfl) ⟨33891, by rfl⟩) R67783
theorem R90593 : Reach 90593 := rs (se 2 (by rfl) ⟨33972, by rfl⟩) R67945
theorem R385607 : Reach 385607 := rs (se 1 (by rfl) ⟨289205, by rfl⟩) R578411
theorem R484055 : Reach 484055 := rs (se 1 (by rfl) ⟨363041, by rfl⟩) R726083
theorem R90899 : Reach 90899 := rs (se 1 (by rfl) ⟨68174, by rfl⟩) R136349
theorem R418823 : Reach 418823 := rs (se 1 (by rfl) ⟨314117, by rfl⟩) R628235
theorem R91259 : Reach 91259 := rs (se 1 (by rfl) ⟨68444, by rfl⟩) R136889
theorem R156887 : Reach 156887 := rs (se 1 (by rfl) ⟨117665, by rfl⟩) R235331
theorem R91385 : Reach 91385 := rs (se 2 (by rfl) ⟨34269, by rfl⟩) R68539
theorem R517499 : Reach 517499 := rs (se 1 (by rfl) ⟨388124, by rfl⟩) R776249
theorem R91529 : Reach 91529 := rs (se 2 (by rfl) ⟨34323, by rfl⟩) R68647
theorem R58823 : Reach 58823 := rs (se 1 (by rfl) ⟨44117, by rfl⟩) R88235
theorem R91655 : Reach 91655 := rs (se 1 (by rfl) ⟨68741, by rfl⟩) R137483
theorem R91835 : Reach 91835 := rs (se 1 (by rfl) ⟨68876, by rfl⟩) R137753
theorem R59177 : Reach 59177 := rs (se 2 (by rfl) ⟨22191, by rfl⟩) R44383
theorem R59183 : Reach 59183 := rs (se 1 (by rfl) ⟨44387, by rfl⟩) R88775
theorem R91961 : Reach 91961 := rs (se 2 (by rfl) ⟨34485, by rfl⟩) R68971
theorem R452429 : Reach 452429 := rs (se 3 (by rfl) ⟨84830, by rfl⟩) R169661
theorem R92009 : Reach 92009 := rs (se 2 (by rfl) ⟨34503, by rfl⟩) R69007
theorem R321731 : Reach 321731 := rs (se 1 (by rfl) ⟨241298, by rfl⟩) R482597
theorem R59657 : Reach 59657 := rs (se 2 (by rfl) ⟨22371, by rfl⟩) R44743
theorem R59759 : Reach 59759 := rs (se 1 (by rfl) ⟨44819, by rfl⟩) R89639
theorem R92591 : Reach 92591 := rs (se 1 (by rfl) ⟨69443, by rfl⟩) R138887
theorem R92627 : Reach 92627 := rs (se 1 (by rfl) ⟨69470, by rfl⟩) R138941
theorem R92735 : Reach 92735 := rs (se 1 (by rfl) ⟨69551, by rfl⟩) R139103
theorem R59975 : Reach 59975 := rs (se 1 (by rfl) ⟨44981, by rfl⟩) R89963
theorem R60011 : Reach 60011 := rs (se 1 (by rfl) ⟨45008, by rfl⟩) R90017
theorem R92843 : Reach 92843 := rs (se 1 (by rfl) ⟨69632, by rfl⟩) R139265
theorem R60239 : Reach 60239 := rs (se 1 (by rfl) ⟨45179, by rfl⟩) R90359
theorem R93383 : Reach 93383 := rs (se 1 (by rfl) ⟨70037, by rfl⟩) R140075
theorem R60635 : Reach 60635 := rs (se 1 (by rfl) ⟨45476, by rfl⟩) R90953
theorem R159043 : Reach 159043 := rs (se 1 (by rfl) ⟨119282, by rfl⟩) R238565
theorem R93563 : Reach 93563 := rs (se 1 (by rfl) ⟨70172, by rfl⟩) R140345
theorem R60809 : Reach 60809 := rs (se 2 (by rfl) ⟨22803, by rfl⟩) R45607
theorem R93689 : Reach 93689 := rs (se 2 (by rfl) ⟨35133, by rfl⟩) R70267
theorem R93779 : Reach 93779 := rs (se 1 (by rfl) ⟨70334, by rfl⟩) R140669
theorem R159347 : Reach 159347 := rs (se 1 (by rfl) ⟨119510, by rfl⟩) R239021
theorem R1175233 : Reach 1175233 := rs (se 2 (by rfl) ⟨440712, by rfl⟩) R881425
theorem R61163 : Reach 61163 := rs (se 1 (by rfl) ⟨45872, by rfl⟩) R91745
theorem R93959 : Reach 93959 := rs (se 1 (by rfl) ⟨70469, by rfl⟩) R140939
theorem R159529 : Reach 159529 := rs (se 2 (by rfl) ⟨59823, by rfl⟩) R119647
theorem R61231 : Reach 61231 := rs (se 1 (by rfl) ⟨45923, by rfl⟩) R91847
theorem R61391 : Reach 61391 := rs (se 1 (by rfl) ⟨46043, by rfl⟩) R92087
theorem R159803 : Reach 159803 := rs (se 1 (by rfl) ⟨119852, by rfl⟩) R239705
theorem R94337 : Reach 94337 := rs (se 2 (by rfl) ⟨35376, by rfl⟩) R70753
theorem R61787 : Reach 61787 := rs (se 1 (by rfl) ⟨46340, by rfl⟩) R92681
theorem R455017 : Reach 455017 := rs (se 2 (by rfl) ⟨170631, by rfl⟩) R341263
theorem R94571 : Reach 94571 := rs (se 1 (by rfl) ⟨70928, by rfl⟩) R141857
theorem R356723 : Reach 356723 := rs (se 1 (by rfl) ⟨267542, by rfl⟩) R535085
theorem R94715 : Reach 94715 := rs (se 1 (by rfl) ⟨71036, by rfl⟩) R142073
theorem R717335 : Reach 717335 := rs (se 1 (by rfl) ⟨538001, by rfl⟩) R1076003
theorem R62015 : Reach 62015 := rs (se 1 (by rfl) ⟨46511, by rfl⟩) R93023
theorem R782945 : Reach 782945 := rs (se 2 (by rfl) ⟨293604, by rfl⟩) R587209
theorem R94841 : Reach 94841 := rs (se 2 (by rfl) ⟨35565, by rfl⟩) R71131
theorem R94895 : Reach 94895 := rs (se 1 (by rfl) ⟨71171, by rfl⟩) R142343
theorem R62135 : Reach 62135 := rs (se 1 (by rfl) ⟨46601, by rfl⟩) R93203
theorem R94967 : Reach 94967 := rs (se 1 (by rfl) ⟨71225, by rfl⟩) R142451
theorem R62363 : Reach 62363 := rs (se 1 (by rfl) ⟨46772, by rfl⟩) R93545
theorem R95147 : Reach 95147 := rs (se 1 (by rfl) ⟨71360, by rfl⟩) R142721
theorem R95219 : Reach 95219 := rs (se 1 (by rfl) ⟨71414, by rfl⟩) R142829
theorem R62759 : Reach 62759 := rs (se 1 (by rfl) ⟨47069, by rfl⟩) R94139
theorem R128299 : Reach 128299 := rs (se 1 (by rfl) ⟨96224, by rfl⟩) R192449
theorem R62843 : Reach 62843 := rs (se 1 (by rfl) ⟨47132, by rfl⟩) R94265
theorem R95687 : Reach 95687 := rs (se 1 (by rfl) ⟨71765, by rfl⟩) R143531
theorem R62969 : Reach 62969 := rs (se 2 (by rfl) ⟨23613, by rfl⟩) R47227
theorem R95801 : Reach 95801 := rs (se 2 (by rfl) ⟨35925, by rfl⟩) R71851
theorem R63071 : Reach 63071 := rs (se 1 (by rfl) ⟨47303, by rfl⟩) R94607
theorem R63239 : Reach 63239 := rs (se 1 (by rfl) ⟨47429, by rfl⟩) R94859
theorem R96047 : Reach 96047 := rs (se 1 (by rfl) ⟨72035, by rfl⟩) R144071
theorem R63287 : Reach 63287 := rs (se 1 (by rfl) ⟨47465, by rfl⟩) R94931
theorem R96281 : Reach 96281 := rs (se 2 (by rfl) ⟨36105, by rfl⟩) R72211
theorem R63593 : Reach 63593 := rs (se 2 (by rfl) ⟨23847, by rfl⟩) R47695
theorem R227609 : Reach 227609 := rs (se 2 (by rfl) ⟨85353, by rfl⟩) R170707
theorem R96623 : Reach 96623 := rs (se 1 (by rfl) ⟨72467, by rfl⟩) R144935
theorem R63911 : Reach 63911 := rs (se 1 (by rfl) ⟨47933, by rfl⟩) R95867
theorem R96695 : Reach 96695 := rs (se 1 (by rfl) ⟨72521, by rfl⟩) R145043
theorem R2587085 : Reach 2587085 := rs (se 3 (by rfl) ⟨485078, by rfl⟩) R970157
theorem R63995 : Reach 63995 := rs (se 1 (by rfl) ⟨47996, by rfl⟩) R95993
theorem R96839 : Reach 96839 := rs (se 1 (by rfl) ⟨72629, by rfl⟩) R145259
theorem R64073 : Reach 64073 := rs (se 2 (by rfl) ⟨24027, by rfl⟩) R48055
theorem R96875 : Reach 96875 := rs (se 1 (by rfl) ⟨72656, by rfl⟩) R145313
theorem R64121 : Reach 64121 := rs (se 2 (by rfl) ⟨24045, by rfl⟩) R48091
theorem R64175 : Reach 64175 := rs (se 1 (by rfl) ⟨48131, by rfl⟩) R96263
theorem R195293 : Reach 195293 := rs (se 3 (by rfl) ⟨36617, by rfl⟩) R73235
theorem R64223 : Reach 64223 := rs (se 1 (by rfl) ⟨48167, by rfl⟩) R96335
theorem R64427 : Reach 64427 := rs (se 1 (by rfl) ⟨48320, by rfl⟩) R96641
theorem R392123 : Reach 392123 := rs (se 1 (by rfl) ⟨294092, by rfl⟩) R588185
theorem R64487 : Reach 64487 := rs (se 1 (by rfl) ⟨48365, by rfl⟩) R96731
theorem R64655 : Reach 64655 := rs (se 1 (by rfl) ⟨48491, by rfl⟩) R96983
theorem R228541 : Reach 228541 := rs (se 3 (by rfl) ⟨42851, by rfl⟩) R85703
theorem R851267 : Reach 851267 := rs (se 1 (by rfl) ⟨638450, by rfl⟩) R1276901
theorem R294785 : Reach 294785 := rs (se 2 (by rfl) ⟨110544, by rfl⟩) R221089
theorem R98591 : Reach 98591 := rs (se 1 (by rfl) ⟨73943, by rfl⟩) R147887
theorem R197063 : Reach 197063 := rs (se 1 (by rfl) ⟨147797, by rfl⟩) R295595
theorem R66143 : Reach 66143 := rs (se 1 (by rfl) ⟨49607, by rfl⟩) R99215
theorem R525257 : Reach 525257 := rs (se 2 (by rfl) ⟨196971, by rfl⟩) R393943
theorem R132083 : Reach 132083 := rs (se 1 (by rfl) ⟨99062, by rfl⟩) R198125
theorem R263159 : Reach 263159 := rs (se 1 (by rfl) ⟨197369, by rfl⟩) R394739
theorem R230525 : Reach 230525 := rs (se 3 (by rfl) ⟨43223, by rfl⟩) R86447
theorem R328961 : Reach 328961 := rs (se 2 (by rfl) ⟨123360, by rfl⟩) R246721
theorem R263519 : Reach 263519 := rs (se 1 (by rfl) ⟨197639, by rfl⟩) R395279
theorem R132623 : Reach 132623 := rs (se 1 (by rfl) ⟨99467, by rfl⟩) R198935
theorem R231275 : Reach 231275 := rs (se 1 (by rfl) ⟨173456, by rfl⟩) R346913
theorem R67567 : Reach 67567 := rs (se 1 (by rfl) ⟨50675, by rfl⟩) R101351
theorem R67817 : Reach 67817 := rs (se 2 (by rfl) ⟨25431, by rfl⟩) R50863
theorem R133433 : Reach 133433 := rs (se 2 (by rfl) ⟨50037, by rfl⟩) R100075
theorem R100703 : Reach 100703 := rs (se 1 (by rfl) ⟨75527, by rfl⟩) R151055
theorem R133703 : Reach 133703 := rs (se 1 (by rfl) ⟨100277, by rfl⟩) R200555
theorem R101051 : Reach 101051 := rs (se 1 (by rfl) ⟨75788, by rfl⟩) R151577
theorem R167291 : Reach 167291 := rs (se 1 (by rfl) ⟨125468, by rfl⟩) R250937
theorem R232955 : Reach 232955 := rs (se 1 (by rfl) ⟨174716, by rfl⟩) R349433
theorem R134729 : Reach 134729 := rs (se 2 (by rfl) ⟨50523, by rfl⟩) R101047
theorem R69295 : Reach 69295 := rs (se 1 (by rfl) ⟨51971, by rfl⟩) R103943
theorem R233155 : Reach 233155 := rs (se 1 (by rfl) ⟨174866, by rfl⟩) R349733
theorem R69599 : Reach 69599 := rs (se 1 (by rfl) ⟨52199, by rfl⟩) R104399
theorem R135355 : Reach 135355 := rs (se 1 (by rfl) ⟨101516, by rfl⟩) R203033
theorem R69943 : Reach 69943 := rs (se 1 (by rfl) ⟨52457, by rfl⟩) R104915
theorem R299375 : Reach 299375 := rs (se 1 (by rfl) ⟨224531, by rfl⟩) R449063
theorem R201203 : Reach 201203 := rs (se 1 (by rfl) ⟨150902, by rfl⟩) R301805
theorem R135695 : Reach 135695 := rs (se 1 (by rfl) ⟨101771, by rfl⟩) R203543
theorem R332383 : Reach 332383 := rs (se 1 (by rfl) ⟨249287, by rfl⟩) R498575
theorem R70247 : Reach 70247 := rs (se 1 (by rfl) ⟨52685, by rfl⟩) R105371
theorem R70409 : Reach 70409 := rs (se 2 (by rfl) ⟨26403, by rfl⟩) R52807
theorem R1217429 : Reach 1217429 := rs (se 6 (by rfl) ⟨28533, by rfl⟩) R57067
theorem R136187 : Reach 136187 := rs (se 1 (by rfl) ⟨102140, by rfl⟩) R204281
theorem R267259 : Reach 267259 := rs (se 1 (by rfl) ⟨200444, by rfl⟩) R400889
theorem R169067 : Reach 169067 := rs (se 1 (by rfl) ⟨126800, by rfl⟩) R253601
theorem R136403 : Reach 136403 := rs (se 1 (by rfl) ⟨102302, by rfl⟩) R204605
theorem R365867 : Reach 365867 := rs (se 1 (by rfl) ⟨274400, by rfl⟩) R548801
theorem R71003 : Reach 71003 := rs (se 1 (by rfl) ⟨53252, by rfl⟩) R106505
theorem R136673 : Reach 136673 := rs (se 2 (by rfl) ⟨51252, by rfl⟩) R102505
theorem R71239 : Reach 71239 := rs (se 1 (by rfl) ⟨53429, by rfl⟩) R106859
theorem R71455 : Reach 71455 := rs (se 1 (by rfl) ⟨53591, by rfl⟩) R107183
theorem R71671 : Reach 71671 := rs (se 1 (by rfl) ⟨53753, by rfl⟩) R107507
theorem R137321 : Reach 137321 := rs (se 2 (by rfl) ⟨51495, by rfl⟩) R102991
theorem R235649 : Reach 235649 := rs (se 2 (by rfl) ⟨88368, by rfl⟩) R176737
theorem R104591 : Reach 104591 := rs (se 1 (by rfl) ⟨78443, by rfl⟩) R156887
theorem R137371 : Reach 137371 := rs (se 1 (by rfl) ⟨103028, by rfl⟩) R206057
theorem R104609 : Reach 104609 := rs (se 2 (by rfl) ⟨39228, by rfl⟩) R78457
theorem R71975 : Reach 71975 := rs (se 1 (by rfl) ⟨53981, by rfl⟩) R107963
theorem R530729 : Reach 530729 := rs (se 2 (by rfl) ⟨199023, by rfl⟩) R398047
theorem R39215 : Reach 39215 := rs (se 1 (by rfl) ⟨29411, by rfl⟩) R58823
theorem R4069757 : Reach 4069757 := rs (se 3 (by rfl) ⟨763079, by rfl⟩) R1526159
theorem R39451 : Reach 39451 := rs (se 1 (by rfl) ⟨29588, by rfl⟩) R59177
theorem R39455 : Reach 39455 := rs (se 1 (by rfl) ⟨29591, by rfl⟩) R59183
theorem R301619 : Reach 301619 := rs (se 1 (by rfl) ⟨226214, by rfl⟩) R452429
theorem R2038405 : Reach 2038405 := rs (se 4 (by rfl) ⟨191100, by rfl⟩) R382201
theorem R105097 : Reach 105097 := rs (se 2 (by rfl) ⟨39411, by rfl⟩) R78823
theorem R39771 : Reach 39771 := rs (se 1 (by rfl) ⟨29828, by rfl⟩) R59657
theorem R39839 : Reach 39839 := rs (se 1 (by rfl) ⟨29879, by rfl⟩) R59759
theorem R138185 : Reach 138185 := rs (se 2 (by rfl) ⟨51819, by rfl⟩) R103639
theorem R39983 : Reach 39983 := rs (se 1 (by rfl) ⟨29987, by rfl⟩) R59975
theorem R72751 : Reach 72751 := rs (se 1 (by rfl) ⟨54563, by rfl⟩) R109127
theorem R171065 : Reach 171065 := rs (se 2 (by rfl) ⟨64149, by rfl⟩) R128299
theorem R40007 : Reach 40007 := rs (se 1 (by rfl) ⟨30005, by rfl⟩) R60011
theorem R138455 : Reach 138455 := rs (se 1 (by rfl) ⟨103841, by rfl⟩) R207683
theorem R40159 : Reach 40159 := rs (se 1 (by rfl) ⟨30119, by rfl⟩) R60239
theorem R105725 : Reach 105725 := rs (se 3 (by rfl) ⟨19823, by rfl⟩) R39647
theorem R4300121 : Reach 4300121 := rs (se 2 (by rfl) ⟨1612545, by rfl⟩) R3225091
theorem R73171 : Reach 73171 := rs (se 1 (by rfl) ⟨54878, by rfl⟩) R109757
theorem R40423 : Reach 40423 := rs (se 1 (by rfl) ⟨30317, by rfl⟩) R60635
theorem R40539 : Reach 40539 := rs (se 1 (by rfl) ⟨30404, by rfl⟩) R60809
theorem R138995 : Reach 138995 := rs (se 1 (by rfl) ⟨104246, by rfl⟩) R208493
theorem R106231 : Reach 106231 := rs (se 1 (by rfl) ⟨79673, by rfl⟩) R159347
theorem R40775 : Reach 40775 := rs (se 1 (by rfl) ⟨30581, by rfl⟩) R61163
theorem R40927 : Reach 40927 := rs (se 1 (by rfl) ⟨30695, by rfl⟩) R61391
theorem R106535 : Reach 106535 := rs (se 1 (by rfl) ⟨79901, by rfl⟩) R159803
theorem R41191 : Reach 41191 := rs (se 1 (by rfl) ⟨30893, by rfl⟩) R61787
theorem R237815 : Reach 237815 := rs (se 1 (by rfl) ⟨178361, by rfl⟩) R356723
theorem R41343 : Reach 41343 := rs (se 1 (by rfl) ⟨31007, by rfl⟩) R62015
theorem R41423 : Reach 41423 := rs (se 1 (by rfl) ⟨31067, by rfl⟩) R62135
theorem R41575 : Reach 41575 := rs (se 1 (by rfl) ⟨31181, by rfl⟩) R62363
theorem R2270045 : Reach 2270045 := rs (se 3 (by rfl) ⟨425633, by rfl⟩) R851267
theorem R41839 : Reach 41839 := rs (se 1 (by rfl) ⟨31379, by rfl⟩) R62759
theorem R41895 : Reach 41895 := rs (se 1 (by rfl) ⟨31421, by rfl⟩) R62843
theorem R41979 : Reach 41979 := rs (se 1 (by rfl) ⟨31484, by rfl⟩) R62969
theorem R42047 : Reach 42047 := rs (se 1 (by rfl) ⟨31535, by rfl⟩) R63071
theorem R42159 : Reach 42159 := rs (se 1 (by rfl) ⟨31619, by rfl⟩) R63239
theorem R42191 : Reach 42191 := rs (se 1 (by rfl) ⟨31643, by rfl⟩) R63287
theorem R42395 : Reach 42395 := rs (se 1 (by rfl) ⟨31796, by rfl⟩) R63593
theorem R370169 : Reach 370169 := rs (se 2 (by rfl) ⟨138813, by rfl⟩) R277627
theorem R206387 : Reach 206387 := rs (se 1 (by rfl) ⟨154790, by rfl⟩) R309581
theorem R304721 : Reach 304721 := rs (se 2 (by rfl) ⟨114270, by rfl⟩) R228541
theorem R42607 : Reach 42607 := rs (se 1 (by rfl) ⟨31955, by rfl⟩) R63911
theorem R42663 : Reach 42663 := rs (se 1 (by rfl) ⟨31997, by rfl⟩) R63995
theorem R42715 : Reach 42715 := rs (se 1 (by rfl) ⟨32036, by rfl⟩) R64073
theorem R42747 : Reach 42747 := rs (se 1 (by rfl) ⟨32060, by rfl⟩) R64121
theorem R42783 : Reach 42783 := rs (se 1 (by rfl) ⟨32087, by rfl⟩) R64175
theorem R42815 : Reach 42815 := rs (se 1 (by rfl) ⟨32111, by rfl⟩) R64223
theorem R42951 : Reach 42951 := rs (se 1 (by rfl) ⟨32213, by rfl⟩) R64427
theorem R42991 : Reach 42991 := rs (se 1 (by rfl) ⟨32243, by rfl⟩) R64487
theorem R43103 : Reach 43103 := rs (se 1 (by rfl) ⟨32327, by rfl⟩) R64655
theorem R534721 : Reach 534721 := rs (se 2 (by rfl) ⟨200520, by rfl⟩) R401041
theorem R76393 : Reach 76393 := rs (se 2 (by rfl) ⟨28647, by rfl⟩) R57295
theorem R175067 : Reach 175067 := rs (se 1 (by rfl) ⟨131300, by rfl⟩) R262601
theorem R208007 : Reach 208007 := rs (se 1 (by rfl) ⟨156005, by rfl⟩) R312011
theorem R142559 : Reach 142559 := rs (se 1 (by rfl) ⟨106919, by rfl⟩) R213839
theorem R142775 : Reach 142775 := rs (se 1 (by rfl) ⟨107081, by rfl⟩) R214163
theorem R44635 : Reach 44635 := rs (se 1 (by rfl) ⟨33476, by rfl⟩) R66953
theorem R143005 : Reach 143005 := rs (se 3 (by rfl) ⟨26813, by rfl⟩) R53627
theorem R44923 : Reach 44923 := rs (se 1 (by rfl) ⟨33692, by rfl⟩) R67385
theorem R307151 : Reach 307151 := rs (se 1 (by rfl) ⟨230363, by rfl⟩) R460727
theorem R602245 : Reach 602245 := rs (se 4 (by rfl) ⟨56460, by rfl⟩) R112921
theorem R1028285 : Reach 1028285 := rs (se 3 (by rfl) ⟨192803, by rfl⟩) R385607
theorem R111401 : Reach 111401 := rs (se 2 (by rfl) ⟨41775, by rfl⟩) R83551
theorem R209789 : Reach 209789 := rs (se 3 (by rfl) ⟨39335, by rfl⟩) R78671
theorem R46075 : Reach 46075 := rs (se 1 (by rfl) ⟨34556, by rfl⟩) R69113
theorem R46255 : Reach 46255 := rs (se 1 (by rfl) ⟨34691, by rfl⟩) R69383
theorem R505025 : Reach 505025 := rs (se 2 (by rfl) ⟨189384, by rfl⟩) R378769
theorem R144827 : Reach 144827 := rs (se 1 (by rfl) ⟨108620, by rfl⟩) R217241
theorem R46759 : Reach 46759 := rs (se 1 (by rfl) ⟨35069, by rfl⟩) R70139
theorem R177967 : Reach 177967 := rs (se 1 (by rfl) ⟨133475, by rfl⟩) R266951
theorem R112447 : Reach 112447 := rs (se 1 (by rfl) ⟨84335, by rfl⟩) R168671
theorem R47047 : Reach 47047 := rs (se 1 (by rfl) ⟨35285, by rfl⟩) R70571
theorem R145367 : Reach 145367 := rs (se 1 (by rfl) ⟨109025, by rfl⟩) R218051
theorem R178139 : Reach 178139 := rs (se 1 (by rfl) ⟨133604, by rfl⟩) R267209
theorem R112745 : Reach 112745 := rs (se 2 (by rfl) ⟨42279, by rfl⟩) R84559
theorem R47407 : Reach 47407 := rs (se 1 (by rfl) ⟨35555, by rfl⟩) R71111
theorem R244079 : Reach 244079 := rs (se 1 (by rfl) ⟨183059, by rfl⟩) R366119
theorem R1850201 : Reach 1850201 := rs (se 2 (by rfl) ⟨693825, by rfl⟩) R1387651
theorem R113615 : Reach 113615 := rs (se 1 (by rfl) ⟨85211, by rfl⟩) R170423
theorem R113633 : Reach 113633 := rs (se 2 (by rfl) ⟨42612, by rfl⟩) R85225
theorem R48199 : Reach 48199 := rs (se 1 (by rfl) ⟨36149, by rfl⟩) R72299
theorem R212057 : Reach 212057 := rs (se 2 (by rfl) ⟨79521, by rfl⟩) R159043
theorem R474443 : Reach 474443 := rs (se 1 (by rfl) ⟨355832, by rfl⟩) R711665
theorem R147035 : Reach 147035 := rs (se 1 (by rfl) ⟨110276, by rfl⟩) R220553
theorem R212705 : Reach 212705 := rs (se 2 (by rfl) ⟨79764, by rfl⟩) R159529
theorem R81641 : Reach 81641 := rs (se 2 (by rfl) ⟨30615, by rfl⟩) R61231
theorem R311435 : Reach 311435 := rs (se 1 (by rfl) ⟨233576, by rfl⟩) R467153
theorem R409961 : Reach 409961 := rs (se 2 (by rfl) ⟨153735, by rfl⟩) R307471
theorem R606689 : Reach 606689 := rs (se 2 (by rfl) ⟨227508, by rfl⟩) R455017
theorem R115273 : Reach 115273 := rs (se 2 (by rfl) ⟨43227, by rfl⟩) R86455
theorem R279215 : Reach 279215 := rs (se 1 (by rfl) ⟨209411, by rfl⟩) R418823
theorem R181111 : Reach 181111 := rs (se 1 (by rfl) ⟨135833, by rfl⟩) R271667
theorem R344999 : Reach 344999 := rs (se 1 (by rfl) ⟨258749, by rfl⟩) R517499
theorem R115901 : Reach 115901 := rs (se 3 (by rfl) ⟨21731, by rfl⟩) R43463
theorem R214487 : Reach 214487 := rs (se 1 (by rfl) ⟨160865, by rfl⟩) R321731
theorem R149309 : Reach 149309 := rs (se 3 (by rfl) ⟨27995, by rfl⟩) R55991
theorem R247781 : Reach 247781 := rs (se 4 (by rfl) ⟨23229, by rfl⟩) R46459
theorem R478223 : Reach 478223 := rs (se 1 (by rfl) ⟨358667, by rfl⟩) R717335
theorem R52265 : Reach 52265 := rs (se 2 (by rfl) ⟨19599, by rfl⟩) R39199
theorem R446147 : Reach 446147 := rs (se 1 (by rfl) ⟨334610, by rfl⟩) R669221
theorem R52969 : Reach 52969 := rs (se 2 (by rfl) ⟨19863, by rfl⟩) R39727
theorem R184103 : Reach 184103 := rs (se 1 (by rfl) ⟨138077, by rfl⟩) R276155
theorem R151739 : Reach 151739 := rs (se 1 (by rfl) ⟨113804, by rfl⟩) R227609
theorem R1724723 : Reach 1724723 := rs (se 1 (by rfl) ⟨1293542, by rfl⟩) R2587085
theorem R152225 : Reach 152225 := rs (se 2 (by rfl) ⟨57084, by rfl⟩) R114169
theorem R251113 : Reach 251113 := rs (se 2 (by rfl) ⟨94167, by rfl⟩) R188335
theorem R906497 : Reach 906497 := rs (se 2 (by rfl) ⟨339936, by rfl⟩) R679873
theorem R153197 : Reach 153197 := rs (se 3 (by rfl) ⟨28724, by rfl⟩) R57449
theorem R120491 : Reach 120491 := rs (se 1 (by rfl) ⟨90368, by rfl⟩) R180737
theorem R88361 : Reach 88361 := rs (se 2 (by rfl) ⟨33135, by rfl⟩) R66271
theorem R121277 : Reach 121277 := rs (se 3 (by rfl) ⟨22739, by rfl⟩) R45479
theorem R2939533 : Reach 2939533 := rs (se 3 (by rfl) ⟨551162, by rfl⟩) R1102325
theorem R252715 : Reach 252715 := rs (se 1 (by rfl) ⟨189536, by rfl⟩) R379073
theorem R88937 : Reach 88937 := rs (se 2 (by rfl) ⟨33351, by rfl⟩) R66703
theorem R88991 : Reach 88991 := rs (se 1 (by rfl) ⟨66743, by rfl⟩) R133487
theorem R285677 : Reach 285677 := rs (se 3 (by rfl) ⟨53564, by rfl⟩) R107129
theorem R1530899 : Reach 1530899 := rs (se 1 (by rfl) ⟨1148174, by rfl⟩) R2296349
theorem R56543 : Reach 56543 := rs (se 1 (by rfl) ⟨42407, by rfl⟩) R84815
theorem R89927 : Reach 89927 := rs (se 1 (by rfl) ⟨67445, by rfl⟩) R134891
theorem R254087 : Reach 254087 := rs (se 1 (by rfl) ⟨190565, by rfl⟩) R381131
theorem R385357 : Reach 385357 := rs (se 3 (by rfl) ⟨72254, by rfl⟩) R144509
theorem R90575 : Reach 90575 := rs (se 1 (by rfl) ⟨67931, by rfl⟩) R135863
theorem R58159 : Reach 58159 := rs (se 1 (by rfl) ⟨43619, by rfl⟩) R87239
theorem R58423 : Reach 58423 := rs (se 1 (by rfl) ⟨43817, by rfl⟩) R87635
theorem R91241 : Reach 91241 := rs (se 2 (by rfl) ⟨34215, by rfl⟩) R68431
theorem R58715 : Reach 58715 := rs (se 1 (by rfl) ⟨44036, by rfl⟩) R88073
theorem R124267 : Reach 124267 := rs (se 1 (by rfl) ⟨93200, by rfl⟩) R186401
theorem R288137 : Reach 288137 := rs (se 2 (by rfl) ⟨108051, by rfl⟩) R216103
theorem R255469 : Reach 255469 := rs (se 3 (by rfl) ⟨47900, by rfl⟩) R95801
theorem R91667 : Reach 91667 := rs (se 1 (by rfl) ⟨68750, by rfl⟩) R137501
theorem R58991 : Reach 58991 := rs (se 1 (by rfl) ⟨44243, by rfl⟩) R88487
theorem R59063 : Reach 59063 := rs (se 1 (by rfl) ⟨44297, by rfl⟩) R88595
theorem R59099 : Reach 59099 := rs (se 1 (by rfl) ⟨44324, by rfl⟩) R88649
theorem R157403 : Reach 157403 := rs (se 1 (by rfl) ⟨118052, by rfl⟩) R236105
theorem R91871 : Reach 91871 := rs (se 1 (by rfl) ⟨68903, by rfl⟩) R137807
theorem R222983 : Reach 222983 := rs (se 1 (by rfl) ⟨167237, by rfl⟩) R334475
theorem R59273 : Reach 59273 := rs (se 2 (by rfl) ⟨22227, by rfl⟩) R44455
theorem R59375 : Reach 59375 := rs (se 1 (by rfl) ⟨44531, by rfl⟩) R89063
theorem R288787 : Reach 288787 := rs (se 1 (by rfl) ⟨216590, by rfl⟩) R433181
theorem R190679 : Reach 190679 := rs (se 1 (by rfl) ⟨143009, by rfl⟩) R286019
theorem R59627 : Reach 59627 := rs (se 1 (by rfl) ⟨44720, by rfl⟩) R89441
theorem R1566977 : Reach 1566977 := rs (se 2 (by rfl) ⟨587616, by rfl⟩) R1175233
theorem R59687 : Reach 59687 := rs (se 1 (by rfl) ⟨44765, by rfl⟩) R89531
theorem R59771 : Reach 59771 := rs (se 1 (by rfl) ⟨44828, by rfl⟩) R89657
theorem R92699 : Reach 92699 := rs (se 1 (by rfl) ⟨69524, by rfl⟩) R139049
theorem R60041 : Reach 60041 := rs (se 2 (by rfl) ⟨22515, by rfl⟩) R45031
theorem R60215 : Reach 60215 := rs (se 1 (by rfl) ⟨45161, by rfl⟩) R90323
theorem R289595 : Reach 289595 := rs (se 1 (by rfl) ⟨217196, by rfl⟩) R434393
theorem R60251 : Reach 60251 := rs (se 1 (by rfl) ⟨45188, by rfl⟩) R90377
theorem R60395 : Reach 60395 := rs (se 1 (by rfl) ⟨45296, by rfl⟩) R90593
theorem R1272833 : Reach 1272833 := rs (se 2 (by rfl) ⟨477312, by rfl⟩) R954625
theorem R322703 : Reach 322703 := rs (se 1 (by rfl) ⟨242027, by rfl⟩) R484055
theorem R60599 : Reach 60599 := rs (se 1 (by rfl) ⟨45449, by rfl⟩) R90899
theorem R355661 : Reach 355661 := rs (se 3 (by rfl) ⟨66686, by rfl⟩) R133373
theorem R60839 : Reach 60839 := rs (se 1 (by rfl) ⟨45629, by rfl⟩) R91259
theorem R60923 : Reach 60923 := rs (se 1 (by rfl) ⟨45692, by rfl⟩) R91385
theorem R61019 : Reach 61019 := rs (se 1 (by rfl) ⟨45764, by rfl⟩) R91529
theorem R61103 : Reach 61103 := rs (se 1 (by rfl) ⟨45827, by rfl⟩) R91655
theorem R61223 : Reach 61223 := rs (se 1 (by rfl) ⟨45917, by rfl⟩) R91835
theorem R61307 : Reach 61307 := rs (se 1 (by rfl) ⟨45980, by rfl⟩) R91961
theorem R61339 : Reach 61339 := rs (se 1 (by rfl) ⟨46004, by rfl⟩) R92009
theorem R94175 : Reach 94175 := rs (se 1 (by rfl) ⟨70631, by rfl⟩) R141263
theorem R61727 : Reach 61727 := rs (se 1 (by rfl) ⟨46295, by rfl⟩) R92591
theorem R61751 : Reach 61751 := rs (se 1 (by rfl) ⟨46313, by rfl⟩) R92627
theorem R61823 : Reach 61823 := rs (se 1 (by rfl) ⟨46367, by rfl⟩) R92735
theorem R61895 : Reach 61895 := rs (se 1 (by rfl) ⟨46421, by rfl⟩) R92843
theorem R94679 : Reach 94679 := rs (se 1 (by rfl) ⟨71009, by rfl⟩) R142019
theorem R94823 : Reach 94823 := rs (se 1 (by rfl) ⟨71117, by rfl⟩) R142235
theorem R62249 : Reach 62249 := rs (se 2 (by rfl) ⟨23343, by rfl⟩) R46687
theorem R62255 : Reach 62255 := rs (se 1 (by rfl) ⟨46691, by rfl⟩) R93383
theorem R1078109 : Reach 1078109 := rs (se 3 (by rfl) ⟨202145, by rfl⟩) R404291
theorem R62375 : Reach 62375 := rs (se 1 (by rfl) ⟨46781, by rfl⟩) R93563
theorem R62459 : Reach 62459 := rs (se 1 (by rfl) ⟨46844, by rfl⟩) R93689
theorem R62519 : Reach 62519 := rs (se 1 (by rfl) ⟨46889, by rfl⟩) R93779
theorem R62537 : Reach 62537 := rs (se 2 (by rfl) ⟨23451, by rfl⟩) R46903
theorem R62639 : Reach 62639 := rs (se 1 (by rfl) ⟨46979, by rfl⟩) R93959
theorem R95407 : Reach 95407 := rs (se 1 (by rfl) ⟨71555, by rfl⟩) R143111
theorem R95507 : Reach 95507 := rs (se 1 (by rfl) ⟨71630, by rfl⟩) R143261
theorem R95579 : Reach 95579 := rs (se 1 (by rfl) ⟨71684, by rfl⟩) R143369
theorem R62891 : Reach 62891 := rs (se 1 (by rfl) ⟨47168, by rfl⟩) R94337
theorem R63047 : Reach 63047 := rs (se 1 (by rfl) ⟨47285, by rfl⟩) R94571
theorem R292517 : Reach 292517 := rs (se 4 (by rfl) ⟨27423, by rfl⟩) R54847
theorem R63143 : Reach 63143 := rs (se 1 (by rfl) ⟨47357, by rfl⟩) R94715
theorem R521963 : Reach 521963 := rs (se 1 (by rfl) ⟨391472, by rfl⟩) R782945
theorem R63227 : Reach 63227 := rs (se 1 (by rfl) ⟨47420, by rfl⟩) R94841
theorem R63263 : Reach 63263 := rs (se 1 (by rfl) ⟨47447, by rfl⟩) R94895
theorem R63311 : Reach 63311 := rs (se 1 (by rfl) ⟨47483, by rfl⟩) R94967
theorem R96137 : Reach 96137 := rs (se 2 (by rfl) ⟨36051, by rfl⟩) R72103
theorem R63431 : Reach 63431 := rs (se 1 (by rfl) ⟨47573, by rfl⟩) R95147
theorem R63479 : Reach 63479 := rs (se 1 (by rfl) ⟨47609, by rfl⟩) R95219
theorem R96353 : Reach 96353 := rs (se 2 (by rfl) ⟨36132, by rfl⟩) R72265
theorem R63785 : Reach 63785 := rs (se 2 (by rfl) ⟨23919, by rfl⟩) R47839
theorem R63791 : Reach 63791 := rs (se 1 (by rfl) ⟨47843, by rfl⟩) R95687
theorem R64031 : Reach 64031 := rs (se 1 (by rfl) ⟨48023, by rfl⟩) R96047
theorem R64187 : Reach 64187 := rs (se 1 (by rfl) ⟨48140, by rfl⟩) R96281
theorem R64415 : Reach 64415 := rs (se 1 (by rfl) ⟨48311, by rfl⟩) R96623
theorem R64463 : Reach 64463 := rs (se 1 (by rfl) ⟨48347, by rfl⟩) R96695
theorem R64553 : Reach 64553 := rs (se 2 (by rfl) ⟨24207, by rfl⟩) R48415
theorem R64559 : Reach 64559 := rs (se 1 (by rfl) ⟨48419, by rfl⟩) R96839
theorem R64583 : Reach 64583 := rs (se 1 (by rfl) ⟨48437, by rfl⟩) R96875
theorem R130195 : Reach 130195 := rs (se 1 (by rfl) ⟨97646, by rfl⟩) R195293
theorem R261415 : Reach 261415 := rs (se 1 (by rfl) ⟨196061, by rfl⟩) R392123
theorem R196523 : Reach 196523 := rs (se 1 (by rfl) ⟨147392, by rfl⟩) R294785
theorem R131375 : Reach 131375 := rs (se 1 (by rfl) ⟨98531, by rfl⟩) R197063
theorem R229999 : Reach 229999 := rs (se 1 (by rfl) ⟨172499, by rfl⟩) R344999
theorem R3211973 : Reach 3211973 := rs (se 4 (by rfl) ⟨301122, by rfl⟩) R602245
theorem R262909 : Reach 262909 := rs (se 3 (by rfl) ⟨49295, by rfl⟩) R98591
theorem R99539 : Reach 99539 := rs (se 1 (by rfl) ⟨74654, by rfl⟩) R149309
theorem R165187 : Reach 165187 := rs (se 1 (by rfl) ⟨123890, by rfl⟩) R247781
theorem R67135 : Reach 67135 := rs (se 1 (by rfl) ⟨50351, by rfl⟩) R100703
theorem R67367 : Reach 67367 := rs (se 1 (by rfl) ⟨50525, by rfl⟩) R101051
theorem R165689 : Reach 165689 := rs (se 2 (by rfl) ⟨62133, by rfl⟩) R124267
theorem R919997 : Reach 919997 := rs (se 3 (by rfl) ⟨172499, by rfl⟩) R344999
theorem R297431 : Reach 297431 := rs (se 1 (by rfl) ⟨223073, by rfl⟩) R446147
theorem R16714421 : Reach 16714421 := rs (se 5 (by rfl) ⟨783488, by rfl⟩) R1566977
theorem R101159 : Reach 101159 := rs (se 1 (by rfl) ⟨75869, by rfl⟩) R151739
theorem R1149815 : Reach 1149815 := rs (se 1 (by rfl) ⟨862361, by rfl⟩) R1724723
theorem R199583 : Reach 199583 := rs (se 1 (by rfl) ⟨149687, by rfl⟩) R299375
theorem R134135 : Reach 134135 := rs (se 1 (by rfl) ⟨100601, by rfl⟩) R201203
theorem R101483 : Reach 101483 := rs (se 1 (by rfl) ⟨76112, by rfl⟩) R152225
theorem R101857 : Reach 101857 := rs (se 2 (by rfl) ⟨38196, by rfl⟩) R76393
theorem R102131 : Reach 102131 := rs (se 1 (by rfl) ⟨76598, by rfl⟩) R153197
theorem R69727 : Reach 69727 := rs (se 1 (by rfl) ⟨52295, by rfl⟩) R104591
theorem R201079 : Reach 201079 := rs (se 1 (by rfl) ⟨150809, by rfl⟩) R301619
theorem R168605 : Reach 168605 := rs (se 3 (by rfl) ⟨31613, by rfl⟩) R63227
theorem R1020599 : Reach 1020599 := rs (se 1 (by rfl) ⟨765449, by rfl⟩) R1530899
theorem R70483 : Reach 70483 := rs (se 1 (by rfl) ⟨52862, by rfl⟩) R105725
theorem R70625 : Reach 70625 := rs (se 2 (by rfl) ⟨26484, by rfl⟩) R52969
theorem R71023 : Reach 71023 := rs (se 1 (by rfl) ⟨53267, by rfl⟩) R106535
theorem R169391 : Reach 169391 := rs (se 1 (by rfl) ⟨127043, by rfl⟩) R254087
theorem R1513363 : Reach 1513363 := rs (se 1 (by rfl) ⟨1135022, by rfl⟩) R2270045
theorem R39143 : Reach 39143 := rs (se 1 (by rfl) ⟨29357, by rfl⟩) R58715
theorem R137591 : Reach 137591 := rs (se 1 (by rfl) ⟨103193, by rfl⟩) R206387
theorem R203147 : Reach 203147 := rs (se 1 (by rfl) ⟨152360, by rfl⟩) R304721
theorem R39327 : Reach 39327 := rs (se 1 (by rfl) ⟨29495, by rfl⟩) R58991
theorem R39375 : Reach 39375 := rs (se 1 (by rfl) ⟨29531, by rfl⟩) R59063
theorem R39399 : Reach 39399 := rs (se 1 (by rfl) ⟨29549, by rfl⟩) R59099
theorem R104935 : Reach 104935 := rs (se 1 (by rfl) ⟨78701, by rfl⟩) R157403
theorem R39515 : Reach 39515 := rs (se 1 (by rfl) ⟨29636, by rfl⟩) R59273
theorem R39583 : Reach 39583 := rs (se 1 (by rfl) ⟨29687, by rfl⟩) R59375
theorem R39751 : Reach 39751 := rs (se 1 (by rfl) ⟨29813, by rfl⟩) R59627
theorem R39791 : Reach 39791 := rs (se 1 (by rfl) ⟨29843, by rfl⟩) R59687
theorem R39847 : Reach 39847 := rs (se 1 (by rfl) ⟨29885, by rfl⟩) R59771
theorem R334817 : Reach 334817 := rs (se 2 (by rfl) ⟨125556, by rfl⟩) R251113
theorem R40027 : Reach 40027 := rs (se 1 (by rfl) ⟨30020, by rfl⟩) R60041
theorem R40143 : Reach 40143 := rs (se 1 (by rfl) ⟨30107, by rfl⟩) R60215
theorem R40167 : Reach 40167 := rs (se 1 (by rfl) ⟨30125, by rfl⟩) R60251
theorem R40263 : Reach 40263 := rs (se 1 (by rfl) ⟨30197, by rfl⟩) R60395
theorem R138671 : Reach 138671 := rs (se 1 (by rfl) ⟨104003, by rfl⟩) R208007
theorem R40399 : Reach 40399 := rs (se 1 (by rfl) ⟨30299, by rfl⟩) R60599
theorem R237107 : Reach 237107 := rs (se 1 (by rfl) ⟨177830, by rfl⟩) R355661
theorem R40559 : Reach 40559 := rs (se 1 (by rfl) ⟨30419, by rfl⟩) R60839
theorem R40615 : Reach 40615 := rs (se 1 (by rfl) ⟨30461, by rfl⟩) R60923
theorem R40679 : Reach 40679 := rs (se 1 (by rfl) ⟨30509, by rfl⟩) R61019
theorem R237289 : Reach 237289 := rs (se 2 (by rfl) ⟨88983, by rfl⟩) R177967
theorem R40735 : Reach 40735 := rs (se 1 (by rfl) ⟨30551, by rfl⟩) R61103
theorem R40815 : Reach 40815 := rs (se 1 (by rfl) ⟨30611, by rfl⟩) R61223
theorem R40871 : Reach 40871 := rs (se 1 (by rfl) ⟨30653, by rfl⟩) R61307
theorem R204767 : Reach 204767 := rs (se 1 (by rfl) ⟨153575, by rfl⟩) R307151
theorem R139373 : Reach 139373 := rs (se 3 (by rfl) ⟨26132, by rfl⟩) R52265
theorem R41151 : Reach 41151 := rs (se 1 (by rfl) ⟨30863, by rfl⟩) R61727
theorem R41167 : Reach 41167 := rs (se 1 (by rfl) ⟨30875, by rfl⟩) R61751
theorem R41215 : Reach 41215 := rs (se 1 (by rfl) ⟨30911, by rfl⟩) R61823
theorem R41263 : Reach 41263 := rs (se 1 (by rfl) ⟨30947, by rfl⟩) R61895
theorem R74267 : Reach 74267 := rs (se 1 (by rfl) ⟨55700, by rfl⟩) R111401
theorem R41499 : Reach 41499 := rs (se 1 (by rfl) ⟨31124, by rfl⟩) R62249
theorem R41503 : Reach 41503 := rs (se 1 (by rfl) ⟨31127, by rfl⟩) R62255
theorem R139859 : Reach 139859 := rs (se 1 (by rfl) ⟨104894, by rfl⟩) R209789
theorem R41583 : Reach 41583 := rs (se 1 (by rfl) ⟨31187, by rfl⟩) R62375
theorem R41639 : Reach 41639 := rs (se 1 (by rfl) ⟨31229, by rfl⟩) R62459
theorem R41679 : Reach 41679 := rs (se 1 (by rfl) ⟨31259, by rfl⟩) R62519
theorem R41691 : Reach 41691 := rs (se 1 (by rfl) ⟨31268, by rfl⟩) R62537
theorem R41759 : Reach 41759 := rs (se 1 (by rfl) ⟨31319, by rfl⟩) R62639
theorem R336683 : Reach 336683 := rs (se 1 (by rfl) ⟨252512, by rfl⟩) R505025
theorem R140129 : Reach 140129 := rs (se 2 (by rfl) ⟨52548, by rfl⟩) R105097
theorem R41927 : Reach 41927 := rs (se 1 (by rfl) ⟨31445, by rfl⟩) R62891
theorem R42031 : Reach 42031 := rs (se 1 (by rfl) ⟨31523, by rfl⟩) R63047
theorem R336953 : Reach 336953 := rs (se 2 (by rfl) ⟨126357, by rfl⟩) R252715
theorem R42095 : Reach 42095 := rs (se 1 (by rfl) ⟨31571, by rfl⟩) R63143
theorem R42151 : Reach 42151 := rs (se 1 (by rfl) ⟨31613, by rfl⟩) R63227
theorem R42175 : Reach 42175 := rs (se 1 (by rfl) ⟨31631, by rfl⟩) R63263
theorem R42207 : Reach 42207 := rs (se 1 (by rfl) ⟨31655, by rfl⟩) R63311
theorem R42287 : Reach 42287 := rs (se 1 (by rfl) ⟨31715, by rfl⟩) R63431
theorem R42319 : Reach 42319 := rs (se 1 (by rfl) ⟨31739, by rfl⟩) R63479
theorem R75163 : Reach 75163 := rs (se 1 (by rfl) ⟨56372, by rfl⟩) R112745
theorem R173593 : Reach 173593 := rs (se 2 (by rfl) ⟨65097, by rfl⟩) R130195
theorem R42523 : Reach 42523 := rs (se 1 (by rfl) ⟨31892, by rfl⟩) R63785
theorem R42527 : Reach 42527 := rs (se 1 (by rfl) ⟨31895, by rfl⟩) R63791
theorem R599717 : Reach 599717 := rs (se 4 (by rfl) ⟨56223, by rfl⟩) R112447
theorem R42687 : Reach 42687 := rs (se 1 (by rfl) ⟨32015, by rfl⟩) R64031
theorem R42791 : Reach 42791 := rs (se 1 (by rfl) ⟨32093, by rfl⟩) R64187
theorem R42943 : Reach 42943 := rs (se 1 (by rfl) ⟨32207, by rfl⟩) R64415
theorem R75743 : Reach 75743 := rs (se 1 (by rfl) ⟨56807, by rfl⟩) R113615
theorem R42975 : Reach 42975 := rs (se 1 (by rfl) ⟨32231, by rfl⟩) R64463
theorem R75755 : Reach 75755 := rs (se 1 (by rfl) ⟨56816, by rfl⟩) R113633
theorem R43035 : Reach 43035 := rs (se 1 (by rfl) ⟨32276, by rfl⟩) R64553
theorem R43039 : Reach 43039 := rs (se 1 (by rfl) ⟨32279, by rfl⟩) R64559
theorem R43055 : Reach 43055 := rs (se 1 (by rfl) ⟨32291, by rfl⟩) R64583
theorem R141371 : Reach 141371 := rs (se 1 (by rfl) ⟨106028, by rfl⟩) R212057
theorem R141641 : Reach 141641 := rs (se 2 (by rfl) ⟨53115, by rfl⟩) R106231
theorem R141803 : Reach 141803 := rs (se 1 (by rfl) ⟨106352, by rfl⟩) R212705
theorem R207623 : Reach 207623 := rs (se 1 (by rfl) ⟨155717, by rfl⟩) R311435
theorem R273307 : Reach 273307 := rs (se 1 (by rfl) ⟨204980, by rfl⟩) R409961
theorem R404459 : Reach 404459 := rs (se 1 (by rfl) ⟨303344, by rfl⟩) R606689
theorem R44095 : Reach 44095 := rs (se 1 (by rfl) ⟨33071, by rfl⟩) R66143
theorem R175439 : Reach 175439 := rs (se 1 (by rfl) ⟨131579, by rfl⟩) R263159
theorem R77267 : Reach 77267 := rs (se 1 (by rfl) ⟨57950, by rfl⟩) R115901
theorem R175679 : Reach 175679 := rs (se 1 (by rfl) ⟨131759, by rfl⟩) R263519
theorem R142991 : Reach 142991 := rs (se 1 (by rfl) ⟨107243, by rfl⟩) R214487
theorem R77545 : Reach 77545 := rs (se 2 (by rfl) ⟨29079, by rfl⟩) R58159
theorem R241481 : Reach 241481 := rs (se 2 (by rfl) ⟨90555, by rfl⟩) R181111
theorem R77897 : Reach 77897 := rs (se 2 (by rfl) ⟨29211, by rfl⟩) R58423
theorem R45211 : Reach 45211 := rs (se 1 (by rfl) ⟨33908, by rfl⟩) R67817
theorem R340625 : Reach 340625 := rs (se 2 (by rfl) ⟨127734, by rfl⟩) R255469
theorem R111527 : Reach 111527 := rs (se 1 (by rfl) ⟨83645, by rfl⟩) R167291
theorem R46399 : Reach 46399 := rs (se 1 (by rfl) ⟨34799, by rfl⟩) R69599
theorem R46831 : Reach 46831 := rs (se 1 (by rfl) ⟨35123, by rfl⟩) R70247
theorem R46939 : Reach 46939 := rs (se 1 (by rfl) ⟨35204, by rfl⟩) R70409
theorem R15677509 : Reach 15677509 := rs (se 4 (by rfl) ⟨1469766, by rfl⟩) R2939533
theorem R112711 : Reach 112711 := rs (se 1 (by rfl) ⟨84533, by rfl⟩) R169067
theorem R604331 : Reach 604331 := rs (se 1 (by rfl) ⟨453248, by rfl⟩) R906497
theorem R243911 : Reach 243911 := rs (se 1 (by rfl) ⟨182933, by rfl⟩) R365867
theorem R47335 : Reach 47335 := rs (se 1 (by rfl) ⟨35501, by rfl⟩) R71003
theorem R768365 : Reach 768365 := rs (se 3 (by rfl) ⟨144068, by rfl⟩) R288137
theorem R80327 : Reach 80327 := rs (se 1 (by rfl) ⟨60245, by rfl⟩) R120491
theorem R47983 : Reach 47983 := rs (se 1 (by rfl) ⟨35987, by rfl⟩) R71975
theorem R80851 : Reach 80851 := rs (se 1 (by rfl) ⟨60638, by rfl⟩) R121277
theorem R114043 : Reach 114043 := rs (se 1 (by rfl) ⟨85532, by rfl⟩) R171065
theorem R2866747 : Reach 2866747 := rs (se 1 (by rfl) ⟨2150060, by rfl⟩) R4300121
theorem R310873 : Reach 310873 := rs (se 2 (by rfl) ⟨116577, by rfl⟩) R233155
theorem R81785 : Reach 81785 := rs (se 2 (by rfl) ⟨30669, by rfl⟩) R61339
theorem R180473 : Reach 180473 := rs (se 2 (by rfl) ⟨67677, by rfl⟩) R135355
theorem R278957 : Reach 278957 := rs (se 3 (by rfl) ⟨52304, by rfl⟩) R104609
theorem R508477 : Reach 508477 := rs (se 3 (by rfl) ⟨95339, by rfl⟩) R190679
theorem R443177 : Reach 443177 := rs (se 2 (by rfl) ⟨166191, by rfl⟩) R332383
theorem R508837 : Reach 508837 := rs (se 4 (by rfl) ⟨47703, by rfl⟩) R95407
theorem R246779 : Reach 246779 := rs (se 1 (by rfl) ⟨185084, by rfl⟩) R370169
theorem R148655 : Reach 148655 := rs (se 1 (by rfl) ⟨111491, by rfl⟩) R222983
theorem R116711 : Reach 116711 := rs (se 1 (by rfl) ⟨87533, by rfl⟩) R175067
theorem R215135 : Reach 215135 := rs (se 1 (by rfl) ⟨161351, by rfl⟩) R322703
theorem R772253 : Reach 772253 := rs (se 3 (by rfl) ⟨144797, by rfl⟩) R289595
theorem R183161 : Reach 183161 := rs (se 2 (by rfl) ⟨68685, by rfl⟩) R137371
theorem R150781 : Reach 150781 := rs (se 3 (by rfl) ⟨28271, by rfl⟩) R56543
theorem R347975 : Reach 347975 := rs (se 1 (by rfl) ⟨260981, by rfl⟩) R521963
theorem R118759 : Reach 118759 := rs (se 1 (by rfl) ⟨89069, by rfl⟩) R178139
theorem R348553 : Reach 348553 := rs (se 2 (by rfl) ⟨130707, by rfl⟩) R261415
theorem R1233467 : Reach 1233467 := rs (se 1 (by rfl) ⟨925100, by rfl⟩) R1850201
theorem R316295 : Reach 316295 := rs (se 1 (by rfl) ⟨237221, by rfl⟩) R474443
theorem R54427 : Reach 54427 := rs (se 1 (by rfl) ⟨40820, by rfl⟩) R81641
theorem R513809 : Reach 513809 := rs (se 2 (by rfl) ⟨192678, by rfl⟩) R385357
theorem R186143 : Reach 186143 := rs (se 1 (by rfl) ⟨139607, by rfl⟩) R279215
theorem R350171 : Reach 350171 := rs (se 1 (by rfl) ⟨262628, by rfl⟩) R525257
theorem R88055 : Reach 88055 := rs (se 1 (by rfl) ⟨66041, by rfl⟩) R132083
theorem R153683 : Reach 153683 := rs (se 1 (by rfl) ⟨115262, by rfl⟩) R230525
theorem R153697 : Reach 153697 := rs (se 2 (by rfl) ⟨57636, by rfl⟩) R115273
theorem R88415 : Reach 88415 := rs (se 1 (by rfl) ⟨66311, by rfl⟩) R132623
theorem R154183 : Reach 154183 := rs (se 1 (by rfl) ⟨115637, by rfl⟩) R231275
theorem R88955 : Reach 88955 := rs (se 1 (by rfl) ⟨66716, by rfl⟩) R133433
theorem R89135 : Reach 89135 := rs (se 1 (by rfl) ⟨66851, by rfl⟩) R133703
theorem R318815 : Reach 318815 := rs (se 1 (by rfl) ⟨239111, by rfl⟩) R478223
theorem R56953 : Reach 56953 := rs (se 2 (by rfl) ⟨21357, by rfl⟩) R42715
theorem R155303 : Reach 155303 := rs (se 1 (by rfl) ⟨116477, by rfl⟩) R232955
theorem R89819 : Reach 89819 := rs (se 1 (by rfl) ⟨67364, by rfl⟩) R134729
theorem R122735 : Reach 122735 := rs (se 1 (by rfl) ⟨92051, by rfl⟩) R184103
theorem R90089 : Reach 90089 := rs (se 2 (by rfl) ⟨33783, by rfl⟩) R67567
theorem R385049 : Reach 385049 := rs (se 2 (by rfl) ⟨144393, by rfl⟩) R288787
theorem R712961 : Reach 712961 := rs (se 2 (by rfl) ⟨267360, by rfl⟩) R534721
theorem R90463 : Reach 90463 := rs (se 1 (by rfl) ⟨67847, by rfl⟩) R135695
theorem R811619 : Reach 811619 := rs (se 1 (by rfl) ⟨608714, by rfl⟩) R1217429
theorem R90791 : Reach 90791 := rs (se 1 (by rfl) ⟨68093, by rfl⟩) R136187
theorem R877229 : Reach 877229 := rs (se 3 (by rfl) ⟨164480, by rfl⟩) R328961
theorem R90935 : Reach 90935 := rs (se 1 (by rfl) ⟨68201, by rfl⟩) R136403
theorem R91115 : Reach 91115 := rs (se 1 (by rfl) ⟨68336, by rfl⟩) R136673
theorem R91547 : Reach 91547 := rs (se 1 (by rfl) ⟨68660, by rfl⟩) R137321
theorem R157099 : Reach 157099 := rs (se 1 (by rfl) ⟨117824, by rfl⟩) R235649
theorem R58907 : Reach 58907 := rs (se 1 (by rfl) ⟨44180, by rfl⟩) R88361
theorem R353819 : Reach 353819 := rs (se 1 (by rfl) ⟨265364, by rfl⟩) R530729
theorem R2713171 : Reach 2713171 := rs (se 1 (by rfl) ⟨2034878, by rfl⟩) R4069757
theorem R59291 : Reach 59291 := rs (se 1 (by rfl) ⟨44468, by rfl⟩) R88937
theorem R59327 : Reach 59327 := rs (se 1 (by rfl) ⟨44495, by rfl⟩) R88991
theorem R92123 : Reach 92123 := rs (se 1 (by rfl) ⟨69092, by rfl⟩) R138185
theorem R190451 : Reach 190451 := rs (se 1 (by rfl) ⟨142838, by rfl⟩) R285677
theorem R59513 : Reach 59513 := rs (se 2 (by rfl) ⟨22317, by rfl⟩) R44635
theorem R92303 : Reach 92303 := rs (se 1 (by rfl) ⟨69227, by rfl⟩) R138455
theorem R190673 : Reach 190673 := rs (se 2 (by rfl) ⟨71502, by rfl⟩) R143005
theorem R92393 : Reach 92393 := rs (se 2 (by rfl) ⟨34647, by rfl⟩) R69295
theorem R92663 : Reach 92663 := rs (se 1 (by rfl) ⟨69497, by rfl⟩) R138995
theorem R59897 : Reach 59897 := rs (se 2 (by rfl) ⟨22461, by rfl⟩) R44923
theorem R59951 : Reach 59951 := rs (se 1 (by rfl) ⟨44963, by rfl⟩) R89927
theorem R158543 : Reach 158543 := rs (se 1 (by rfl) ⟨118907, by rfl⟩) R237815
theorem R60383 : Reach 60383 := rs (se 1 (by rfl) ⟨45287, by rfl⟩) R90575
theorem R93257 : Reach 93257 := rs (se 2 (by rfl) ⟨34971, by rfl⟩) R69943
theorem R60827 : Reach 60827 := rs (se 1 (by rfl) ⟨45620, by rfl⟩) R91241
theorem R61111 : Reach 61111 := rs (se 1 (by rfl) ⟨45833, by rfl⟩) R91667
theorem R61247 : Reach 61247 := rs (se 1 (by rfl) ⟨45935, by rfl⟩) R91871
theorem R61433 : Reach 61433 := rs (se 2 (by rfl) ⟨23037, by rfl⟩) R46075
theorem R356345 : Reach 356345 := rs (se 2 (by rfl) ⟨133629, by rfl⟩) R267259
theorem R61673 : Reach 61673 := rs (se 2 (by rfl) ⟨23127, by rfl⟩) R46255
theorem R61799 : Reach 61799 := rs (se 1 (by rfl) ⟨46349, by rfl⟩) R92699
theorem R848555 : Reach 848555 := rs (se 1 (by rfl) ⟨636416, by rfl⟩) R1272833
theorem R94985 : Reach 94985 := rs (se 2 (by rfl) ⟨35619, by rfl⟩) R71239
theorem R95039 : Reach 95039 := rs (se 1 (by rfl) ⟨71279, by rfl⟩) R142559
theorem R62345 : Reach 62345 := rs (se 2 (by rfl) ⟨23379, by rfl⟩) R46759
theorem R95183 : Reach 95183 := rs (se 1 (by rfl) ⟨71387, by rfl⟩) R142775
theorem R95273 : Reach 95273 := rs (se 2 (by rfl) ⟨35727, by rfl⟩) R71455
theorem R62729 : Reach 62729 := rs (se 2 (by rfl) ⟨23523, by rfl⟩) R47047
theorem R62783 : Reach 62783 := rs (se 1 (by rfl) ⟨47087, by rfl⟩) R94175
theorem R95561 : Reach 95561 := rs (se 2 (by rfl) ⟨35835, by rfl⟩) R71671
theorem R685523 : Reach 685523 := rs (se 1 (by rfl) ⟨514142, by rfl⟩) R1028285
theorem R63119 : Reach 63119 := rs (se 1 (by rfl) ⟨47339, by rfl⟩) R94679
theorem R63209 : Reach 63209 := rs (se 2 (by rfl) ⟨23703, by rfl⟩) R47407
theorem R63215 : Reach 63215 := rs (se 1 (by rfl) ⟨47411, by rfl⟩) R94823
theorem R718739 : Reach 718739 := rs (se 1 (by rfl) ⟨539054, by rfl⟩) R1078109
theorem R2717873 : Reach 2717873 := rs (se 2 (by rfl) ⟨1019202, by rfl⟩) R2038405
theorem R63671 : Reach 63671 := rs (se 1 (by rfl) ⟨47753, by rfl⟩) R95507
theorem R63719 : Reach 63719 := rs (se 1 (by rfl) ⟨47789, by rfl⟩) R95579
theorem R96551 : Reach 96551 := rs (se 1 (by rfl) ⟨72413, by rfl⟩) R144827
theorem R195011 : Reach 195011 := rs (se 1 (by rfl) ⟨146258, by rfl⟩) R292517
theorem R64091 : Reach 64091 := rs (se 1 (by rfl) ⟨48068, by rfl⟩) R96137
theorem R96911 : Reach 96911 := rs (se 1 (by rfl) ⟨72683, by rfl⟩) R145367
theorem R97001 : Reach 97001 := rs (se 2 (by rfl) ⟨36375, by rfl⟩) R72751
theorem R64235 : Reach 64235 := rs (se 1 (by rfl) ⟨48176, by rfl⟩) R96353
theorem R64265 : Reach 64265 := rs (se 2 (by rfl) ⟨24099, by rfl⟩) R48199
theorem R162719 : Reach 162719 := rs (se 1 (by rfl) ⟨122039, by rfl⟩) R244079
theorem R97561 : Reach 97561 := rs (se 2 (by rfl) ⟨36585, by rfl⟩) R73171
theorem R98023 : Reach 98023 := rs (se 1 (by rfl) ⟨73517, by rfl⟩) R147035
theorem R131015 : Reach 131015 := rs (se 1 (by rfl) ⟨98261, by rfl⟩) R196523
theorem R295451 : Reach 295451 := rs (se 1 (by rfl) ⟨221588, by rfl⟩) R443177
theorem R164519 : Reach 164519 := rs (se 1 (by rfl) ⟨123389, by rfl⟩) R246779
theorem R99103 : Reach 99103 := rs (se 1 (by rfl) ⟨74327, by rfl⟩) R148655
theorem R66359 : Reach 66359 := rs (se 1 (by rfl) ⟨49769, by rfl⟩) R99539
theorem R198287 : Reach 198287 := rs (se 1 (by rfl) ⟨148715, by rfl⟩) R297431
theorem R11142947 : Reach 11142947 := rs (se 1 (by rfl) ⟨8357210, by rfl⟩) R16714421
theorem R67439 : Reach 67439 := rs (se 1 (by rfl) ⟨50579, by rfl⟩) R101159
theorem R100217 : Reach 100217 := rs (se 2 (by rfl) ⟨37581, by rfl⟩) R75163
theorem R133055 : Reach 133055 := rs (se 1 (by rfl) ⟨99791, by rfl⟩) R199583
theorem R231457 : Reach 231457 := rs (se 2 (by rfl) ⟨86796, by rfl⟩) R173593
theorem R67655 : Reach 67655 := rs (se 1 (by rfl) ⟨50741, by rfl⟩) R101483
theorem R68087 : Reach 68087 := rs (se 1 (by rfl) ⟨51065, by rfl⟩) R102131
theorem R231983 : Reach 231983 := rs (se 1 (by rfl) ⟨173987, by rfl⟩) R347975
theorem R822311 : Reach 822311 := rs (se 1 (by rfl) ⟨616733, by rfl⟩) R1233467
theorem R364409 : Reach 364409 := rs (se 2 (by rfl) ⟨136653, by rfl⟩) R273307
theorem R233447 : Reach 233447 := rs (se 1 (by rfl) ⟨175085, by rfl⟩) R350171
theorem R102455 : Reach 102455 := rs (se 1 (by rfl) ⟨76841, by rfl⟩) R153683
theorem R135431 : Reach 135431 := rs (se 1 (by rfl) ⟨101573, by rfl⟩) R203147
theorem R201041 : Reach 201041 := rs (se 2 (by rfl) ⟨75390, by rfl⟩) R150781
theorem R135809 : Reach 135809 := rs (se 2 (by rfl) ⟨50928, by rfl⟩) R101857
theorem R496381 : Reach 496381 := rs (se 3 (by rfl) ⟨93071, by rfl⟩) R186143
theorem R103393 : Reach 103393 := rs (se 2 (by rfl) ⟨38772, by rfl⟩) R77545
theorem R103535 : Reach 103535 := rs (se 1 (by rfl) ⟨77651, by rfl⟩) R155303
theorem R202013 : Reach 202013 := rs (se 3 (by rfl) ⟨37877, by rfl⟩) R75755
theorem R136511 : Reach 136511 := rs (se 1 (by rfl) ⟨102383, by rfl⟩) R204767
theorem R268105 : Reach 268105 := rs (se 2 (by rfl) ⟨100539, by rfl⟩) R201079
theorem R464737 : Reach 464737 := rs (se 2 (by rfl) ⟨174276, by rfl⟩) R348553
theorem R39271 : Reach 39271 := rs (se 1 (by rfl) ⟨29453, by rfl⟩) R58907
theorem R235879 : Reach 235879 := rs (se 1 (by rfl) ⟨176909, by rfl⟩) R353819
theorem R399811 : Reach 399811 := rs (se 1 (by rfl) ⟨299858, by rfl⟩) R599717
theorem R39527 : Reach 39527 := rs (se 1 (by rfl) ⟨29645, by rfl⟩) R59291
theorem R39551 : Reach 39551 := rs (se 1 (by rfl) ⟨29663, by rfl⟩) R59327
theorem R39675 : Reach 39675 := rs (se 1 (by rfl) ⟨29756, by rfl⟩) R59513
theorem R72569 : Reach 72569 := rs (se 2 (by rfl) ⟨27213, by rfl⟩) R54427
theorem R39931 : Reach 39931 := rs (se 1 (by rfl) ⟨29948, by rfl⟩) R59897
theorem R39967 : Reach 39967 := rs (se 1 (by rfl) ⟨29975, by rfl⟩) R59951
theorem R105695 : Reach 105695 := rs (se 1 (by rfl) ⟨79271, by rfl⟩) R158543
theorem R40255 : Reach 40255 := rs (se 1 (by rfl) ⟨30191, by rfl⟩) R60383
theorem R269639 : Reach 269639 := rs (se 1 (by rfl) ⟨202229, by rfl⟩) R404459
theorem R40551 : Reach 40551 := rs (se 1 (by rfl) ⟨30413, by rfl⟩) R60827
theorem R40831 : Reach 40831 := rs (se 1 (by rfl) ⟨30623, by rfl⟩) R61247
theorem R40955 : Reach 40955 := rs (se 1 (by rfl) ⟨30716, by rfl⟩) R61433
theorem R237563 : Reach 237563 := rs (se 1 (by rfl) ⟨178172, by rfl⟩) R356345
theorem R204929 : Reach 204929 := rs (se 2 (by rfl) ⟨76848, by rfl⟩) R153697
theorem R41115 : Reach 41115 := rs (se 1 (by rfl) ⟨30836, by rfl⟩) R61673
theorem R41199 : Reach 41199 := rs (se 1 (by rfl) ⟨30899, by rfl⟩) R61799
theorem R565703 : Reach 565703 := rs (se 1 (by rfl) ⟨424277, by rfl⟩) R848555
theorem R41563 : Reach 41563 := rs (se 1 (by rfl) ⟨31172, by rfl⟩) R62345
theorem R74351 : Reach 74351 := rs (se 1 (by rfl) ⟨55763, by rfl⟩) R111527
theorem R303749 : Reach 303749 := rs (se 4 (by rfl) ⟨28476, by rfl⟩) R56953
theorem R139913 : Reach 139913 := rs (se 2 (by rfl) ⟨52467, by rfl⟩) R104935
theorem R205577 : Reach 205577 := rs (se 2 (by rfl) ⟨77091, by rfl⟩) R154183
theorem R41819 : Reach 41819 := rs (se 1 (by rfl) ⟨31364, by rfl⟩) R62729
theorem R41855 : Reach 41855 := rs (se 1 (by rfl) ⟨31391, by rfl⟩) R62783
theorem R42079 : Reach 42079 := rs (se 1 (by rfl) ⟨31559, by rfl⟩) R63119
theorem R42139 : Reach 42139 := rs (se 1 (by rfl) ⟨31604, by rfl⟩) R63209
theorem R42143 : Reach 42143 := rs (se 1 (by rfl) ⟨31607, by rfl⟩) R63215
theorem R107801 : Reach 107801 := rs (se 2 (by rfl) ⟨40425, by rfl⟩) R80851
theorem R402887 : Reach 402887 := rs (se 1 (by rfl) ⟨302165, by rfl⟩) R604331
theorem R1811915 : Reach 1811915 := rs (se 1 (by rfl) ⟨1358936, by rfl⟩) R2717873
theorem R42447 : Reach 42447 := rs (se 1 (by rfl) ⟨31835, by rfl⟩) R63671
theorem R42479 : Reach 42479 := rs (se 1 (by rfl) ⟨31859, by rfl⟩) R63719
theorem R42727 : Reach 42727 := rs (se 1 (by rfl) ⟨32045, by rfl⟩) R64091
theorem R42823 : Reach 42823 := rs (se 1 (by rfl) ⟨32117, by rfl⟩) R64235
theorem R42843 : Reach 42843 := rs (se 1 (by rfl) ⟨32132, by rfl⟩) R64265
theorem R108479 : Reach 108479 := rs (se 1 (by rfl) ⟨81359, by rfl⟩) R162719
theorem R108989 : Reach 108989 := rs (se 3 (by rfl) ⟨20435, by rfl⟩) R40871
theorem R2141315 : Reach 2141315 := rs (se 1 (by rfl) ⟨1605986, by rfl⟩) R3211973
theorem R306665 : Reach 306665 := rs (se 2 (by rfl) ⟨114999, by rfl⟩) R229999
theorem R44911 : Reach 44911 := rs (se 1 (by rfl) ⟨33683, by rfl⟩) R67367
theorem R110459 : Reach 110459 := rs (se 1 (by rfl) ⟨82844, by rfl⟩) R165689
theorem R77807 : Reach 77807 := rs (se 1 (by rfl) ⟨58355, by rfl⟩) R116711
theorem R143423 : Reach 143423 := rs (se 1 (by rfl) ⟨107567, by rfl⟩) R215135
theorem R209465 : Reach 209465 := rs (se 2 (by rfl) ⟨78549, by rfl⟩) R157099
theorem R3617561 : Reach 3617561 := rs (se 2 (by rfl) ⟨1356585, by rfl⟩) R2713171
theorem R897821 : Reach 897821 := rs (se 3 (by rfl) ⟨168341, by rfl⟩) R336683
theorem R112403 : Reach 112403 := rs (se 1 (by rfl) ⟨84302, by rfl⟩) R168605
theorem R210863 : Reach 210863 := rs (se 1 (by rfl) ⟨158147, by rfl⟩) R316295
theorem R47083 : Reach 47083 := rs (se 1 (by rfl) ⟨35312, by rfl⟩) R70625
theorem R112927 : Reach 112927 := rs (se 1 (by rfl) ⟨84695, by rfl⟩) R169391
theorem R342539 : Reach 342539 := rs (se 1 (by rfl) ⟨256904, by rfl⟩) R513809
theorem R212543 : Reach 212543 := rs (se 1 (by rfl) ⟨159407, by rfl⟩) R318815
theorem R81481 : Reach 81481 := rs (se 2 (by rfl) ⟨30555, by rfl⟩) R61111
theorem R81823 : Reach 81823 := rs (se 1 (by rfl) ⟨61367, by rfl⟩) R122735
theorem R475307 : Reach 475307 := rs (se 1 (by rfl) ⟨356480, by rfl⟩) R712961
theorem R49511 : Reach 49511 := rs (se 1 (by rfl) ⟨37133, by rfl⟩) R74267
theorem R541079 : Reach 541079 := rs (se 1 (by rfl) ⟨405809, by rfl⟩) R811619
theorem R50495 : Reach 50495 := rs (se 1 (by rfl) ⟨37871, by rfl⟩) R75743
theorem R116959 : Reach 116959 := rs (se 1 (by rfl) ⟨87719, by rfl⟩) R175439
theorem R51511 : Reach 51511 := rs (se 1 (by rfl) ⟨38633, by rfl⟩) R77267
theorem R3066173 : Reach 3066173 := rs (se 3 (by rfl) ⟨574907, by rfl⟩) R1149815
theorem R117119 : Reach 117119 := rs (se 1 (by rfl) ⟨87839, by rfl⟩) R175679
theorem R2017817 : Reach 2017817 := rs (se 2 (by rfl) ⟨756681, by rfl⟩) R1513363
theorem R51931 : Reach 51931 := rs (se 1 (by rfl) ⟨38948, by rfl⟩) R77897
theorem R150281 : Reach 150281 := rs (se 2 (by rfl) ⟨56355, by rfl⟩) R112711
theorem R479159 : Reach 479159 := rs (se 1 (by rfl) ⟨359369, by rfl⟩) R718739
theorem R512243 : Reach 512243 := rs (se 1 (by rfl) ⟨384182, by rfl⟩) R768365
theorem R53551 : Reach 53551 := rs (se 1 (by rfl) ⟨40163, by rfl⟩) R80327
theorem R152057 : Reach 152057 := rs (se 2 (by rfl) ⟨57021, by rfl⟩) R114043
theorem R3822329 : Reach 3822329 := rs (se 2 (by rfl) ⟨1433373, by rfl⟩) R2866747
theorem R414497 : Reach 414497 := rs (se 2 (by rfl) ⟨155436, by rfl⟩) R310873
theorem R316385 : Reach 316385 := rs (se 2 (by rfl) ⟨118644, by rfl⟩) R237289
theorem R349373 : Reach 349373 := rs (se 3 (by rfl) ⟨65507, by rfl⟩) R131015
theorem R54523 : Reach 54523 := rs (se 1 (by rfl) ⟨40892, by rfl⟩) R81785
theorem R87583 : Reach 87583 := rs (se 1 (by rfl) ⟨65687, by rfl⟩) R131375
theorem R185971 : Reach 185971 := rs (se 1 (by rfl) ⟨139478, by rfl⟩) R278957
theorem R120617 : Reach 120617 := rs (se 2 (by rfl) ⟨45231, by rfl⟩) R90463
theorem R481261 : Reach 481261 := rs (se 3 (by rfl) ⟨90236, by rfl⟩) R180473
theorem R677969 : Reach 677969 := rs (se 2 (by rfl) ⟨254238, by rfl⟩) R508477
theorem R678449 : Reach 678449 := rs (se 2 (by rfl) ⟨254418, by rfl⟩) R508837
theorem R514835 : Reach 514835 := rs (se 1 (by rfl) ⟨386126, by rfl⟩) R772253
theorem R613331 : Reach 613331 := rs (se 1 (by rfl) ⟨459998, by rfl⟩) R919997
theorem R220249 : Reach 220249 := rs (se 2 (by rfl) ⟨82593, by rfl⟩) R165187
theorem R89423 : Reach 89423 := rs (se 1 (by rfl) ⟨67067, by rfl⟩) R134135
theorem R89513 : Reach 89513 := rs (se 2 (by rfl) ⟨33567, by rfl⟩) R67135
theorem R680399 : Reach 680399 := rs (se 1 (by rfl) ⟨510299, by rfl⟩) R1020599
theorem R1402181 : Reach 1402181 := rs (se 4 (by rfl) ⟨131454, by rfl⟩) R262909
theorem R58703 : Reach 58703 := rs (se 1 (by rfl) ⟨44027, by rfl⟩) R88055
theorem R157085 : Reach 157085 := rs (se 3 (by rfl) ⟨29453, by rfl⟩) R58907
theorem R58793 : Reach 58793 := rs (se 2 (by rfl) ⟨22047, by rfl⟩) R44095
theorem R58943 : Reach 58943 := rs (se 1 (by rfl) ⟨44207, by rfl⟩) R88415
theorem R91727 : Reach 91727 := rs (se 1 (by rfl) ⟨68795, by rfl⟩) R137591
theorem R59303 : Reach 59303 := rs (se 1 (by rfl) ⟨44477, by rfl⟩) R88955
theorem R223211 : Reach 223211 := rs (se 1 (by rfl) ⟨167408, by rfl⟩) R334817
theorem R59423 : Reach 59423 := rs (se 1 (by rfl) ⟨44567, by rfl⟩) R89135
theorem R92447 : Reach 92447 := rs (se 1 (by rfl) ⟨69335, by rfl⟩) R138671
theorem R158071 : Reach 158071 := rs (se 1 (by rfl) ⟨118553, by rfl⟩) R237107
theorem R59879 : Reach 59879 := rs (se 1 (by rfl) ⟨44909, by rfl⟩) R89819
theorem R158345 : Reach 158345 := rs (se 2 (by rfl) ⟨59379, by rfl⟩) R118759
theorem R60059 : Reach 60059 := rs (se 1 (by rfl) ⟨45044, by rfl⟩) R90089
theorem R256699 : Reach 256699 := rs (se 1 (by rfl) ⟨192524, by rfl⟩) R385049
theorem R92915 : Reach 92915 := rs (se 1 (by rfl) ⟨69686, by rfl⟩) R139373
theorem R92969 : Reach 92969 := rs (se 2 (by rfl) ⟨34863, by rfl⟩) R69727
theorem R60281 : Reach 60281 := rs (se 2 (by rfl) ⟨22605, by rfl⟩) R45211
theorem R93239 : Reach 93239 := rs (se 1 (by rfl) ⟨69929, by rfl⟩) R139859
theorem R60527 : Reach 60527 := rs (se 1 (by rfl) ⟨45395, by rfl⟩) R90791
theorem R584819 : Reach 584819 := rs (se 1 (by rfl) ⟨438614, by rfl⟩) R877229
theorem R650429 : Reach 650429 := rs (se 3 (by rfl) ⟨121955, by rfl⟩) R243911
theorem R60623 : Reach 60623 := rs (se 1 (by rfl) ⟨45467, by rfl⟩) R90935
theorem R93419 : Reach 93419 := rs (se 1 (by rfl) ⟨70064, by rfl⟩) R140129
theorem R60743 : Reach 60743 := rs (se 1 (by rfl) ⟨45557, by rfl⟩) R91115
theorem R224635 : Reach 224635 := rs (se 1 (by rfl) ⟨168476, by rfl⟩) R336953
theorem R61031 : Reach 61031 := rs (se 1 (by rfl) ⟨45773, by rfl⟩) R91547
theorem R93977 : Reach 93977 := rs (se 2 (by rfl) ⟨35241, by rfl⟩) R70483
theorem R61415 : Reach 61415 := rs (se 1 (by rfl) ⟨46061, by rfl⟩) R92123
theorem R126967 : Reach 126967 := rs (se 1 (by rfl) ⟨95225, by rfl⟩) R190451
theorem R94247 : Reach 94247 := rs (se 1 (by rfl) ⟨70685, by rfl⟩) R141371
theorem R61535 : Reach 61535 := rs (se 1 (by rfl) ⟨46151, by rfl⟩) R92303
theorem R127115 : Reach 127115 := rs (se 1 (by rfl) ⟨95336, by rfl⟩) R190673
theorem R61595 : Reach 61595 := rs (se 1 (by rfl) ⟨46196, by rfl⟩) R92393
theorem R94427 : Reach 94427 := rs (se 1 (by rfl) ⟨70820, by rfl⟩) R141641
theorem R94535 : Reach 94535 := rs (se 1 (by rfl) ⟨70901, by rfl⟩) R141803
theorem R61775 : Reach 61775 := rs (se 1 (by rfl) ⟨46331, by rfl⟩) R92663
theorem R61865 : Reach 61865 := rs (se 2 (by rfl) ⟨23199, by rfl⟩) R46399
theorem R94697 : Reach 94697 := rs (se 2 (by rfl) ⟨35511, by rfl⟩) R71023
theorem R553661 : Reach 553661 := rs (se 3 (by rfl) ⟨103811, by rfl⟩) R207623
theorem R62171 : Reach 62171 := rs (se 1 (by rfl) ⟨46628, by rfl⟩) R93257
theorem R62441 : Reach 62441 := rs (se 2 (by rfl) ⟨23415, by rfl⟩) R46831
theorem R488429 : Reach 488429 := rs (se 3 (by rfl) ⟨91580, by rfl⟩) R183161
theorem R95327 : Reach 95327 := rs (se 1 (by rfl) ⟨71495, by rfl⟩) R142991
theorem R62585 : Reach 62585 := rs (se 2 (by rfl) ⟨23469, by rfl⟩) R46939
theorem R160987 : Reach 160987 := rs (se 1 (by rfl) ⟨120740, by rfl⟩) R241481
theorem R20903345 : Reach 20903345 := rs (se 2 (by rfl) ⟨7838754, by rfl⟩) R15677509
theorem R63113 : Reach 63113 := rs (se 2 (by rfl) ⟨23667, by rfl⟩) R47335
theorem R227083 : Reach 227083 := rs (se 1 (by rfl) ⟨170312, by rfl⟩) R340625
theorem R63323 : Reach 63323 := rs (se 1 (by rfl) ⟨47492, by rfl⟩) R94985
theorem R63359 : Reach 63359 := rs (se 1 (by rfl) ⟨47519, by rfl⟩) R95039
theorem R63455 : Reach 63455 := rs (se 1 (by rfl) ⟨47591, by rfl⟩) R95183
theorem R63515 : Reach 63515 := rs (se 1 (by rfl) ⟨47636, by rfl⟩) R95273
theorem R63707 : Reach 63707 := rs (se 1 (by rfl) ⟨47780, by rfl⟩) R95561
theorem R457015 : Reach 457015 := rs (se 1 (by rfl) ⟨342761, by rfl⟩) R685523
theorem R63977 : Reach 63977 := rs (se 2 (by rfl) ⟨23991, by rfl⟩) R47983
theorem R64367 : Reach 64367 := rs (se 1 (by rfl) ⟨48275, by rfl⟩) R96551
theorem R130007 : Reach 130007 := rs (se 1 (by rfl) ⟨97505, by rfl⟩) R195011
theorem R130081 : Reach 130081 := rs (se 2 (by rfl) ⟨48780, by rfl⟩) R97561
theorem R64607 : Reach 64607 := rs (se 1 (by rfl) ⟨48455, by rfl⟩) R96911
theorem R64667 : Reach 64667 := rs (se 1 (by rfl) ⟨48500, by rfl⟩) R97001
theorem R130697 : Reach 130697 := rs (se 2 (by rfl) ⟨49011, by rfl⟩) R98023
theorem R360719 : Reach 360719 := rs (se 1 (by rfl) ⟨270539, by rfl⟩) R541079
theorem R196967 : Reach 196967 := rs (se 1 (by rfl) ⟨147725, by rfl⟩) R295451
theorem R132029 : Reach 132029 := rs (se 3 (by rfl) ⟨24755, by rfl⟩) R49511
theorem R132137 : Reach 132137 := rs (se 2 (by rfl) ⟨49551, by rfl⟩) R99103
theorem R132191 : Reach 132191 := rs (se 1 (by rfl) ⟨99143, by rfl⟩) R198287
theorem R66811 : Reach 66811 := rs (se 1 (by rfl) ⟨50108, by rfl⟩) R100217
theorem R1345211 : Reach 1345211 := rs (se 1 (by rfl) ⟨1008908, by rfl⟩) R2017817
theorem R100187 : Reach 100187 := rs (se 1 (by rfl) ⟨75140, by rfl⟩) R150281
theorem R10192877 : Reach 10192877 := rs (se 3 (by rfl) ⟨1911164, by rfl⟩) R3822329
theorem R68303 : Reach 68303 := rs (se 1 (by rfl) ⟨51227, by rfl⟩) R102455
theorem R134027 : Reach 134027 := rs (se 1 (by rfl) ⟨100520, by rfl⟩) R201041
theorem R101371 : Reach 101371 := rs (se 1 (by rfl) ⟨76028, by rfl⟩) R152057
theorem R68681 : Reach 68681 := rs (se 2 (by rfl) ⟨25755, by rfl⟩) R51511
theorem R69023 : Reach 69023 := rs (se 1 (by rfl) ⟨51767, by rfl⟩) R103535
theorem R232915 : Reach 232915 := rs (se 1 (by rfl) ⟨174686, by rfl⟩) R349373
theorem R134675 : Reach 134675 := rs (se 1 (by rfl) ⟨101006, by rfl⟩) R202013
theorem R69241 : Reach 69241 := rs (se 2 (by rfl) ⟨25965, by rfl⟩) R51931
theorem R299513 : Reach 299513 := rs (se 2 (by rfl) ⟨112317, by rfl⟩) R224635
theorem R70463 : Reach 70463 := rs (se 1 (by rfl) ⟨52847, by rfl⟩) R105695
theorem R562301 : Reach 562301 := rs (se 3 (by rfl) ⟨105431, by rfl⟩) R210863
theorem R169289 : Reach 169289 := rs (se 2 (by rfl) ⟨63483, by rfl⟩) R126967
theorem R136619 : Reach 136619 := rs (se 1 (by rfl) ⟨102464, by rfl⟩) R204929
theorem R71401 : Reach 71401 := rs (se 2 (by rfl) ⟨26775, by rfl⟩) R53551
theorem R202499 : Reach 202499 := rs (se 1 (by rfl) ⟨151874, by rfl⟩) R303749
theorem R137051 : Reach 137051 := rs (se 1 (by rfl) ⟨102788, by rfl⟩) R205577
theorem R71867 : Reach 71867 := rs (se 1 (by rfl) ⟨53900, by rfl⟩) R107801
theorem R39135 : Reach 39135 := rs (se 1 (by rfl) ⟨29351, by rfl⟩) R58703
theorem R104723 : Reach 104723 := rs (se 1 (by rfl) ⟨78542, by rfl⟩) R157085
theorem R39195 : Reach 39195 := rs (se 1 (by rfl) ⟨29396, by rfl⟩) R58793
theorem R268591 : Reach 268591 := rs (se 1 (by rfl) ⟨201443, by rfl⟩) R402887
theorem R661841 : Reach 661841 := rs (se 2 (by rfl) ⟨248190, by rfl⟩) R496381
theorem R39295 : Reach 39295 := rs (se 1 (by rfl) ⟨29471, by rfl⟩) R58943
theorem R39535 : Reach 39535 := rs (se 1 (by rfl) ⟨29651, by rfl⟩) R59303
theorem R72319 : Reach 72319 := rs (se 1 (by rfl) ⟨54239, by rfl⟩) R108479
theorem R137857 : Reach 137857 := rs (se 2 (by rfl) ⟨51696, by rfl⟩) R103393
theorem R39615 : Reach 39615 := rs (se 1 (by rfl) ⟨29711, by rfl⟩) R59423
theorem R72659 : Reach 72659 := rs (se 1 (by rfl) ⟨54494, by rfl⟩) R108989
theorem R39919 : Reach 39919 := rs (se 1 (by rfl) ⟨29939, by rfl⟩) R59879
theorem R72697 : Reach 72697 := rs (se 2 (by rfl) ⟨27261, by rfl⟩) R54523
theorem R105563 : Reach 105563 := rs (se 1 (by rfl) ⟨79172, by rfl⟩) R158345
theorem R40039 : Reach 40039 := rs (se 1 (by rfl) ⟨30029, by rfl⟩) R60059
theorem R40187 : Reach 40187 := rs (se 1 (by rfl) ⟨30140, by rfl⟩) R60281
theorem R40351 : Reach 40351 := rs (se 1 (by rfl) ⟨30263, by rfl⟩) R60527
theorem R433619 : Reach 433619 := rs (se 1 (by rfl) ⟨325214, by rfl⟩) R650429
theorem R40415 : Reach 40415 := rs (se 1 (by rfl) ⟨30311, by rfl⟩) R60623
theorem R40495 : Reach 40495 := rs (se 1 (by rfl) ⟨30371, by rfl⟩) R60743
theorem R204443 : Reach 204443 := rs (se 1 (by rfl) ⟨153332, by rfl⟩) R306665
theorem R302777 : Reach 302777 := rs (se 2 (by rfl) ⟨113541, by rfl⟩) R227083
theorem R40687 : Reach 40687 := rs (se 1 (by rfl) ⟨30515, by rfl⟩) R61031
theorem R73639 : Reach 73639 := rs (se 1 (by rfl) ⟨55229, by rfl⟩) R110459
theorem R40943 : Reach 40943 := rs (se 1 (by rfl) ⟨30707, by rfl⟩) R61415
theorem R41023 : Reach 41023 := rs (se 1 (by rfl) ⟨30767, by rfl⟩) R61535
theorem R41063 : Reach 41063 := rs (se 1 (by rfl) ⟨30797, by rfl⟩) R61595
theorem R41183 : Reach 41183 := rs (se 1 (by rfl) ⟨30887, by rfl⟩) R61775
theorem R41243 : Reach 41243 := rs (se 1 (by rfl) ⟨30932, by rfl⟩) R61865
theorem R139643 : Reach 139643 := rs (se 1 (by rfl) ⟨104732, by rfl⟩) R209465
theorem R369107 : Reach 369107 := rs (se 1 (by rfl) ⟨276830, by rfl⟩) R553661
theorem R41447 : Reach 41447 := rs (se 1 (by rfl) ⟨31085, by rfl⟩) R62171
theorem R598547 : Reach 598547 := rs (se 1 (by rfl) ⟨448910, by rfl⟩) R897821
theorem R533081 : Reach 533081 := rs (se 2 (by rfl) ⟨199905, by rfl⟩) R399811
theorem R41627 : Reach 41627 := rs (se 1 (by rfl) ⟨31220, by rfl⟩) R62441
theorem R41723 : Reach 41723 := rs (se 1 (by rfl) ⟨31292, by rfl⟩) R62585
theorem R13935563 : Reach 13935563 := rs (se 1 (by rfl) ⟨10451672, by rfl⟩) R20903345
theorem R42075 : Reach 42075 := rs (se 1 (by rfl) ⟨31556, by rfl⟩) R63113
theorem R74935 : Reach 74935 := rs (se 1 (by rfl) ⟨56201, by rfl⟩) R112403
theorem R42215 : Reach 42215 := rs (se 1 (by rfl) ⟨31661, by rfl⟩) R63323
theorem R42239 : Reach 42239 := rs (se 1 (by rfl) ⟨31679, by rfl⟩) R63359
theorem R42303 : Reach 42303 := rs (se 1 (by rfl) ⟨31727, by rfl⟩) R63455
theorem R42343 : Reach 42343 := rs (se 1 (by rfl) ⟨31757, by rfl⟩) R63515
theorem R173441 : Reach 173441 := rs (se 2 (by rfl) ⟨65040, by rfl⟩) R130081
theorem R42471 : Reach 42471 := rs (se 1 (by rfl) ⟨31853, by rfl⟩) R63707
theorem R42651 : Reach 42651 := rs (se 1 (by rfl) ⟨31988, by rfl⟩) R63977
theorem R42911 : Reach 42911 := rs (se 1 (by rfl) ⟨32183, by rfl⟩) R64367
theorem R43071 : Reach 43071 := rs (se 1 (by rfl) ⟨32303, by rfl⟩) R64607
theorem R108641 : Reach 108641 := rs (se 2 (by rfl) ⟨40740, by rfl⟩) R81481
theorem R43111 : Reach 43111 := rs (se 1 (by rfl) ⟨32333, by rfl⟩) R64667
theorem R141695 : Reach 141695 := rs (se 1 (by rfl) ⟨106271, by rfl⟩) R212543
theorem R109097 : Reach 109097 := rs (se 2 (by rfl) ⟨40911, by rfl⟩) R81823
theorem R207485 : Reach 207485 := rs (se 3 (by rfl) ⟨38903, by rfl⟩) R77807
theorem R109679 : Reach 109679 := rs (se 1 (by rfl) ⟨82259, by rfl⟩) R164519
theorem R44239 : Reach 44239 := rs (se 1 (by rfl) ⟨33179, by rfl⟩) R66359
theorem R44959 : Reach 44959 := rs (se 1 (by rfl) ⟨33719, by rfl⟩) R67439
theorem R45103 : Reach 45103 := rs (se 1 (by rfl) ⟨33827, by rfl⟩) R67655
theorem R2044115 : Reach 2044115 := rs (se 1 (by rfl) ⟨1533086, by rfl⟩) R3066173
theorem R78079 : Reach 78079 := rs (se 1 (by rfl) ⟨58559, by rfl⟩) R117119
theorem R45391 : Reach 45391 := rs (se 1 (by rfl) ⟨34043, by rfl⟩) R68087
theorem R1258021 : Reach 1258021 := rs (se 4 (by rfl) ⟨117939, by rfl⟩) R235879
theorem R242939 : Reach 242939 := rs (se 1 (by rfl) ⟨182204, by rfl⟩) R364409
theorem R308609 : Reach 308609 := rs (se 2 (by rfl) ⟨115728, by rfl⟩) R231457
theorem R341495 : Reach 341495 := rs (se 1 (by rfl) ⟨256121, by rfl⟩) R512243
theorem R210761 : Reach 210761 := rs (se 2 (by rfl) ⟨79035, by rfl⟩) R158071
theorem R210923 : Reach 210923 := rs (se 1 (by rfl) ⟨158192, by rfl⟩) R316385
theorem R538613 : Reach 538613 := rs (se 5 (by rfl) ⟨25247, by rfl⟩) R50495
theorem R14956597 : Reach 14956597 := rs (se 5 (by rfl) ⟨701090, by rfl⟩) R1402181
theorem R342265 : Reach 342265 := rs (se 2 (by rfl) ⟨128349, by rfl⟩) R256699
theorem R80411 : Reach 80411 := rs (se 1 (by rfl) ⟨60308, by rfl⟩) R120617
theorem R343223 : Reach 343223 := rs (se 1 (by rfl) ⟨257417, by rfl⟩) R514835
theorem R48379 : Reach 48379 := rs (se 1 (by rfl) ⟨36284, by rfl⟩) R72569
theorem R408887 : Reach 408887 := rs (se 1 (by rfl) ⟨306665, by rfl⟩) R613331
theorem R179759 : Reach 179759 := rs (se 1 (by rfl) ⟨134819, by rfl⟩) R269639
theorem R180413 : Reach 180413 := rs (se 3 (by rfl) ⟨33827, by rfl⟩) R67655
theorem R377135 : Reach 377135 := rs (se 1 (by rfl) ⟨282851, by rfl⟩) R565703
theorem R49567 : Reach 49567 := rs (se 1 (by rfl) ⟨37175, by rfl⟩) R74351
theorem R148807 : Reach 148807 := rs (se 1 (by rfl) ⟨111605, by rfl⟩) R223211
theorem R214649 : Reach 214649 := rs (se 2 (by rfl) ⟨80493, by rfl⟩) R160987
theorem R116777 : Reach 116777 := rs (se 2 (by rfl) ⟨43791, by rfl⟩) R87583
theorem R1427543 : Reach 1427543 := rs (se 1 (by rfl) ⟨1070657, by rfl⟩) R2141315
theorem R247961 : Reach 247961 := rs (se 2 (by rfl) ⟨92985, by rfl⟩) R185971
theorem R641681 : Reach 641681 := rs (se 2 (by rfl) ⟨240630, by rfl⟩) R481261
theorem R84743 : Reach 84743 := rs (se 1 (by rfl) ⟨63557, by rfl⟩) R127115
theorem R150569 : Reach 150569 := rs (se 2 (by rfl) ⟨56463, by rfl⟩) R112927
theorem R609353 : Reach 609353 := rs (se 2 (by rfl) ⟨228507, by rfl⟩) R457015
theorem R2411707 : Reach 2411707 := rs (se 1 (by rfl) ⟨1808780, by rfl⟩) R3617561
theorem R86671 : Reach 86671 := rs (se 1 (by rfl) ⟨65003, by rfl⟩) R130007
theorem R87131 : Reach 87131 := rs (se 1 (by rfl) ⟨65348, by rfl⟩) R130697
theorem R316871 : Reach 316871 := rs (se 1 (by rfl) ⟨237653, by rfl⟩) R475307
theorem R7428631 : Reach 7428631 := rs (se 1 (by rfl) ⟨5571473, by rfl⟩) R11142947
theorem R88703 : Reach 88703 := rs (se 1 (by rfl) ⟨66527, by rfl⟩) R133055
theorem R154655 : Reach 154655 := rs (se 1 (by rfl) ⟨115991, by rfl⟩) R231983
theorem R548207 : Reach 548207 := rs (se 1 (by rfl) ⟨411155, by rfl⟩) R822311
theorem R1105325 : Reach 1105325 := rs (se 3 (by rfl) ⟨207248, by rfl⟩) R414497
theorem R319439 : Reach 319439 := rs (se 1 (by rfl) ⟨239579, by rfl⟩) R479159
theorem R90287 : Reach 90287 := rs (se 1 (by rfl) ⟨67715, by rfl⟩) R135431
theorem R155945 : Reach 155945 := rs (se 2 (by rfl) ⟨58479, by rfl⟩) R116959
theorem R90539 : Reach 90539 := rs (se 1 (by rfl) ⟨67904, by rfl⟩) R135809
theorem R91007 : Reach 91007 := rs (se 1 (by rfl) ⟨68255, by rfl⟩) R136511
theorem R451979 : Reach 451979 := rs (se 1 (by rfl) ⟨338984, by rfl⟩) R677969
theorem R452299 : Reach 452299 := rs (se 1 (by rfl) ⟨339224, by rfl⟩) R678449
theorem R59615 : Reach 59615 := rs (se 1 (by rfl) ⟨44711, by rfl⟩) R89423
theorem R59675 : Reach 59675 := rs (se 1 (by rfl) ⟨44756, by rfl⟩) R89513
theorem R59881 : Reach 59881 := rs (se 2 (by rfl) ⟨22455, by rfl⟩) R44911
theorem R158375 : Reach 158375 := rs (se 1 (by rfl) ⟨118781, by rfl⟩) R237563
theorem R453599 : Reach 453599 := rs (se 1 (by rfl) ⟨340199, by rfl⟩) R680399
theorem R93275 : Reach 93275 := rs (se 1 (by rfl) ⟨69956, by rfl⟩) R139913
theorem R1207943 : Reach 1207943 := rs (se 1 (by rfl) ⟨905957, by rfl⟩) R1811915
theorem R61151 : Reach 61151 := rs (se 1 (by rfl) ⟨45863, by rfl⟩) R91727
theorem R61631 : Reach 61631 := rs (se 1 (by rfl) ⟨46223, by rfl⟩) R92447
theorem R160157 : Reach 160157 := rs (se 3 (by rfl) ⟨30029, by rfl⟩) R60059
theorem R61943 : Reach 61943 := rs (se 1 (by rfl) ⟨46457, by rfl⟩) R92915
theorem R61979 : Reach 61979 := rs (se 1 (by rfl) ⟨46484, by rfl⟩) R92969
theorem R62159 : Reach 62159 := rs (se 1 (by rfl) ⟨46619, by rfl⟩) R93239
theorem R389879 : Reach 389879 := rs (se 1 (by rfl) ⟨292409, by rfl⟩) R584819
theorem R62279 : Reach 62279 := rs (se 1 (by rfl) ⟨46709, by rfl⟩) R93419
theorem R357473 : Reach 357473 := rs (se 2 (by rfl) ⟨134052, by rfl⟩) R268105
theorem R619649 : Reach 619649 := rs (se 2 (by rfl) ⟨232368, by rfl⟩) R464737
theorem R62651 : Reach 62651 := rs (se 1 (by rfl) ⟨46988, by rfl⟩) R93977
theorem R62777 : Reach 62777 := rs (se 2 (by rfl) ⟨23541, by rfl⟩) R47083
theorem R62831 : Reach 62831 := rs (se 1 (by rfl) ⟨47123, by rfl⟩) R94247
theorem R95615 : Reach 95615 := rs (se 1 (by rfl) ⟨71711, by rfl⟩) R143423
theorem R62951 : Reach 62951 := rs (se 1 (by rfl) ⟨47213, by rfl⟩) R94427
theorem R63023 : Reach 63023 := rs (se 1 (by rfl) ⟨47267, by rfl⟩) R94535
theorem R63131 : Reach 63131 := rs (se 1 (by rfl) ⟨47348, by rfl⟩) R94697
theorem R325619 : Reach 325619 := rs (se 1 (by rfl) ⟨244214, by rfl⟩) R488429
theorem R63551 : Reach 63551 := rs (se 1 (by rfl) ⟨47663, by rfl⟩) R95327
theorem R293665 : Reach 293665 := rs (se 2 (by rfl) ⟨110124, by rfl⟩) R220249
theorem R162749 : Reach 162749 := rs (se 3 (by rfl) ⟨30515, by rfl⟩) R61031
theorem R228359 : Reach 228359 := rs (se 1 (by rfl) ⟨171269, by rfl⟩) R342539
theorem R622525 : Reach 622525 := rs (se 3 (by rfl) ⟨116723, by rfl⟩) R233447
theorem R131311 : Reach 131311 := rs (se 1 (by rfl) ⟨98483, by rfl⟩) R196967
theorem R66089 : Reach 66089 := rs (se 2 (by rfl) ⟨24783, by rfl⟩) R49567
theorem R66791 : Reach 66791 := rs (se 1 (by rfl) ⟨50093, by rfl⟩) R100187
theorem R951695 : Reach 951695 := rs (se 1 (by rfl) ⟨713771, by rfl⟩) R1427543
theorem R165307 : Reach 165307 := rs (se 1 (by rfl) ⟨123980, by rfl⟩) R247961
theorem R99913 : Reach 99913 := rs (se 2 (by rfl) ⟨37467, by rfl⟩) R74935
theorem R198409 : Reach 198409 := rs (se 2 (by rfl) ⟨74403, by rfl⟩) R148807
theorem R427787 : Reach 427787 := rs (se 1 (by rfl) ⟨320840, by rfl⟩) R641681
theorem R100379 : Reach 100379 := rs (se 1 (by rfl) ⟨75284, by rfl⟩) R150569
theorem R199675 : Reach 199675 := rs (se 1 (by rfl) ⟨149756, by rfl⟩) R299513
theorem R134999 : Reach 134999 := rs (se 1 (by rfl) ⟨101249, by rfl⟩) R202499
theorem R135161 : Reach 135161 := rs (se 2 (by rfl) ⟨50685, by rfl⟩) R101371
theorem R69815 : Reach 69815 := rs (se 1 (by rfl) ⟨52361, by rfl⟩) R104723
theorem R3215609 : Reach 3215609 := rs (se 2 (by rfl) ⟨1205853, by rfl⟩) R2411707
theorem R103103 : Reach 103103 := rs (se 1 (by rfl) ⟨77327, by rfl⟩) R154655
theorem R70375 : Reach 70375 := rs (se 1 (by rfl) ⟨52781, by rfl⟩) R105563
theorem R365471 : Reach 365471 := rs (se 1 (by rfl) ⟨274103, by rfl⟩) R548207
theorem R136295 : Reach 136295 := rs (se 1 (by rfl) ⟨102221, by rfl⟩) R204443
theorem R201851 : Reach 201851 := rs (se 1 (by rfl) ⟨151388, by rfl⟩) R302777
theorem R103963 : Reach 103963 := rs (se 1 (by rfl) ⟨77972, by rfl⟩) R155945
theorem R104105 : Reach 104105 := rs (se 2 (by rfl) ⟨39039, by rfl⟩) R78079
theorem R1677361 : Reach 1677361 := rs (se 2 (by rfl) ⟨629010, by rfl⟩) R1258021
theorem R301319 : Reach 301319 := rs (se 1 (by rfl) ⟨225989, by rfl⟩) R451979
theorem R72427 : Reach 72427 := rs (se 1 (by rfl) ⟨54320, by rfl⟩) R108641
theorem R39743 : Reach 39743 := rs (se 1 (by rfl) ⟨29807, by rfl⟩) R59615
theorem R39783 : Reach 39783 := rs (se 1 (by rfl) ⟨29837, by rfl⟩) R59675
theorem R72731 : Reach 72731 := rs (se 1 (by rfl) ⟨54548, by rfl⟩) R109097
theorem R138323 : Reach 138323 := rs (se 1 (by rfl) ⟨103742, by rfl⟩) R207485
theorem R105583 : Reach 105583 := rs (se 1 (by rfl) ⟨79187, by rfl⟩) R158375
theorem R302399 : Reach 302399 := rs (se 1 (by rfl) ⟨226799, by rfl⟩) R453599
theorem R40767 : Reach 40767 := rs (se 1 (by rfl) ⟨30575, by rfl⟩) R61151
theorem R41087 : Reach 41087 := rs (se 1 (by rfl) ⟨30815, by rfl⟩) R61631
theorem R106771 : Reach 106771 := rs (se 1 (by rfl) ⟨80078, by rfl⟩) R160157
theorem R41295 : Reach 41295 := rs (se 1 (by rfl) ⟨30971, by rfl⟩) R61943
theorem R41319 : Reach 41319 := rs (se 1 (by rfl) ⟨30989, by rfl⟩) R61979
theorem R41439 : Reach 41439 := rs (se 1 (by rfl) ⟨31079, by rfl⟩) R62159
theorem R41519 : Reach 41519 := rs (se 1 (by rfl) ⟨31139, by rfl⟩) R62279
theorem R9904841 : Reach 9904841 := rs (se 2 (by rfl) ⟨3714315, by rfl⟩) R7428631
theorem R238315 : Reach 238315 := rs (se 1 (by rfl) ⟨178736, by rfl⟩) R357473
theorem R41767 : Reach 41767 := rs (se 1 (by rfl) ⟨31325, by rfl⟩) R62651
theorem R41851 : Reach 41851 := rs (se 1 (by rfl) ⟨31388, by rfl⟩) R62777
theorem R41887 : Reach 41887 := rs (se 1 (by rfl) ⟨31415, by rfl⟩) R62831
theorem R205739 : Reach 205739 := rs (se 1 (by rfl) ⟨154304, by rfl⟩) R308609
theorem R41967 : Reach 41967 := rs (se 1 (by rfl) ⟨31475, by rfl⟩) R62951
theorem R42015 : Reach 42015 := rs (se 1 (by rfl) ⟨31511, by rfl⟩) R63023
theorem R42087 : Reach 42087 := rs (se 1 (by rfl) ⟨31565, by rfl⟩) R63131
theorem R140507 : Reach 140507 := rs (se 1 (by rfl) ⟨105380, by rfl⟩) R210761
theorem R140615 : Reach 140615 := rs (se 1 (by rfl) ⟨105461, by rfl⟩) R210923
theorem R42367 : Reach 42367 := rs (se 1 (by rfl) ⟨31775, by rfl⟩) R63551
theorem R108499 : Reach 108499 := rs (se 1 (by rfl) ⟨81374, by rfl⟩) R162749
theorem R272591 : Reach 272591 := rs (se 1 (by rfl) ⟨204443, by rfl⟩) R408887
theorem R830033 : Reach 830033 := rs (se 2 (by rfl) ⟨311262, by rfl⟩) R622525
theorem R240479 : Reach 240479 := rs (se 1 (by rfl) ⟨180359, by rfl⟩) R360719
theorem R143099 : Reach 143099 := rs (se 1 (by rfl) ⟨107324, by rfl⟩) R214649
theorem R896807 : Reach 896807 := rs (se 1 (by rfl) ⟨672605, by rfl⟩) R1345211
theorem R6795251 : Reach 6795251 := rs (se 1 (by rfl) ⟨5096438, by rfl⟩) R10192877
theorem R77851 : Reach 77851 := rs (se 1 (by rfl) ⟨58388, by rfl⟩) R116777
theorem R45535 : Reach 45535 := rs (se 1 (by rfl) ⟨34151, by rfl⟩) R68303
theorem R45787 : Reach 45787 := rs (se 1 (by rfl) ⟨34340, by rfl⟩) R68681
theorem R406235 : Reach 406235 := rs (se 1 (by rfl) ⟨304676, by rfl⟩) R609353
theorem R603065 : Reach 603065 := rs (se 2 (by rfl) ⟨226149, by rfl⟩) R452299
theorem R46015 : Reach 46015 := rs (se 1 (by rfl) ⟨34511, by rfl⟩) R69023
theorem R46975 : Reach 46975 := rs (se 1 (by rfl) ⟨35231, by rfl⟩) R70463
theorem R79841 : Reach 79841 := rs (se 2 (by rfl) ⟨29940, by rfl⟩) R59881
theorem R374867 : Reach 374867 := rs (se 1 (by rfl) ⟨281150, by rfl⟩) R562301
theorem R112859 : Reach 112859 := rs (se 1 (by rfl) ⟨84644, by rfl⟩) R169289
theorem R211247 : Reach 211247 := rs (se 1 (by rfl) ⟨158435, by rfl⟩) R316871
theorem R47911 : Reach 47911 := rs (se 1 (by rfl) ⟨35933, by rfl⟩) R71867
theorem R441227 : Reach 441227 := rs (se 1 (by rfl) ⟨330920, by rfl⟩) R661841
theorem R310553 : Reach 310553 := rs (se 2 (by rfl) ⟨116457, by rfl⟩) R232915
theorem R48439 : Reach 48439 := rs (se 1 (by rfl) ⟨36329, by rfl⟩) R72659
theorem R736883 : Reach 736883 := rs (se 1 (by rfl) ⟨552662, by rfl⟩) R1105325
theorem R212959 : Reach 212959 := rs (se 1 (by rfl) ⟨159719, by rfl⟩) R319439
theorem R246071 : Reach 246071 := rs (se 1 (by rfl) ⟨184553, by rfl⟩) R369107
theorem R9290375 : Reach 9290375 := rs (se 1 (by rfl) ⟨6967781, by rfl⟩) R13935563
theorem R115561 : Reach 115561 := rs (se 2 (by rfl) ⟨43335, by rfl⟩) R86671
theorem R115627 : Reach 115627 := rs (se 1 (by rfl) ⟨86720, by rfl⟩) R173441
theorem R214429 : Reach 214429 := rs (se 3 (by rfl) ⟨40205, by rfl⟩) R80411
theorem R805295 : Reach 805295 := rs (se 1 (by rfl) ⟨603971, by rfl⟩) R1207943
theorem R19942129 : Reach 19942129 := rs (se 2 (by rfl) ⟨7478298, by rfl⟩) R14956597
theorem R1362743 : Reach 1362743 := rs (se 1 (by rfl) ⟨1022057, by rfl⟩) R2044115
theorem R413099 : Reach 413099 := rs (se 1 (by rfl) ⟨309824, by rfl⟩) R619649
theorem R183809 : Reach 183809 := rs (se 2 (by rfl) ⟨68928, by rfl⟩) R137857
theorem R217079 : Reach 217079 := rs (se 1 (by rfl) ⟨162809, by rfl⟩) R325619
theorem R152239 : Reach 152239 := rs (se 1 (by rfl) ⟨114179, by rfl⟩) R228359
theorem R119839 : Reach 119839 := rs (se 1 (by rfl) ⟨89879, by rfl⟩) R179759
theorem R120275 : Reach 120275 := rs (se 1 (by rfl) ⟨90206, by rfl⟩) R180413
theorem R251423 : Reach 251423 := rs (se 1 (by rfl) ⟨188567, by rfl⟩) R377135
theorem R88019 : Reach 88019 := rs (se 1 (by rfl) ⟨66014, by rfl⟩) R132029
theorem R88091 : Reach 88091 := rs (se 1 (by rfl) ⟨66068, by rfl⟩) R132137
theorem R88127 : Reach 88127 := rs (se 1 (by rfl) ⟨66095, by rfl⟩) R132191
theorem R1169909 : Reach 1169909 := rs (se 5 (by rfl) ⟨54839, by rfl⟩) R109679
theorem R1596125 : Reach 1596125 := rs (se 3 (by rfl) ⟨299273, by rfl⟩) R598547
theorem R89081 : Reach 89081 := rs (se 2 (by rfl) ⟨33405, by rfl⟩) R66811
theorem R56495 : Reach 56495 := rs (se 1 (by rfl) ⟨42371, by rfl⟩) R84743
theorem R89351 : Reach 89351 := rs (se 1 (by rfl) ⟨67013, by rfl⟩) R134027
theorem R89783 : Reach 89783 := rs (se 1 (by rfl) ⟨67337, by rfl⟩) R134675
theorem R58087 : Reach 58087 := rs (se 1 (by rfl) ⟨43565, by rfl⟩) R87131
theorem R91079 : Reach 91079 := rs (se 1 (by rfl) ⟨68309, by rfl⟩) R136619
theorem R91367 : Reach 91367 := rs (se 1 (by rfl) ⟨68525, by rfl⟩) R137051
theorem R58985 : Reach 58985 := rs (se 2 (by rfl) ⟨22119, by rfl⟩) R44239
theorem R59135 : Reach 59135 := rs (se 1 (by rfl) ⟨44351, by rfl⟩) R88703
theorem R92321 : Reach 92321 := rs (se 2 (by rfl) ⟨34620, by rfl⟩) R69241
theorem R289079 : Reach 289079 := rs (se 1 (by rfl) ⟨216809, by rfl⟩) R433619
theorem R59945 : Reach 59945 := rs (se 2 (by rfl) ⟨22479, by rfl⟩) R44959
theorem R60137 : Reach 60137 := rs (se 2 (by rfl) ⟨22551, by rfl⟩) R45103
theorem R60191 : Reach 60191 := rs (se 1 (by rfl) ⟨45143, by rfl⟩) R90287
theorem R93095 : Reach 93095 := rs (se 1 (by rfl) ⟨69821, by rfl⟩) R139643
theorem R60359 : Reach 60359 := rs (se 1 (by rfl) ⟨45269, by rfl⟩) R90539
theorem R355387 : Reach 355387 := rs (se 1 (by rfl) ⟨266540, by rfl⟩) R533081
theorem R60521 : Reach 60521 := rs (se 2 (by rfl) ⟨22695, by rfl⟩) R45391
theorem R60671 : Reach 60671 := rs (se 1 (by rfl) ⟨45503, by rfl⟩) R91007
theorem R94463 : Reach 94463 := rs (se 1 (by rfl) ⟨70847, by rfl⟩) R141695
theorem R62183 : Reach 62183 := rs (se 1 (by rfl) ⟨46637, by rfl⟩) R93275
theorem R95201 : Reach 95201 := rs (se 2 (by rfl) ⟨35700, by rfl⟩) R71401
theorem R456353 : Reach 456353 := rs (se 2 (by rfl) ⟨171132, by rfl⟩) R342265
theorem R358121 : Reach 358121 := rs (se 2 (by rfl) ⟨134295, by rfl⟩) R268591
theorem R259919 : Reach 259919 := rs (se 1 (by rfl) ⟨194939, by rfl⟩) R389879
theorem R161959 : Reach 161959 := rs (se 1 (by rfl) ⟨121469, by rfl⟩) R242939
theorem R96425 : Reach 96425 := rs (se 2 (by rfl) ⟨36159, by rfl⟩) R72319
theorem R63743 : Reach 63743 := rs (se 1 (by rfl) ⟨47807, by rfl⟩) R95615
theorem R227663 : Reach 227663 := rs (se 1 (by rfl) ⟨170747, by rfl⟩) R341495
theorem R391553 : Reach 391553 := rs (se 2 (by rfl) ⟨146832, by rfl⟩) R293665
theorem R96929 : Reach 96929 := rs (se 2 (by rfl) ⟨36348, by rfl⟩) R72697
theorem R359075 : Reach 359075 := rs (se 1 (by rfl) ⟨269306, by rfl⟩) R538613
theorem R64505 : Reach 64505 := rs (se 2 (by rfl) ⟨24189, by rfl⟩) R48379
theorem R228815 : Reach 228815 := rs (se 1 (by rfl) ⟨171611, by rfl⟩) R343223
theorem R98185 : Reach 98185 := rs (se 2 (by rfl) ⟨36819, by rfl⟩) R73639
theorem R164047 : Reach 164047 := rs (se 1 (by rfl) ⟨123035, by rfl⟩) R246071
theorem R6193583 : Reach 6193583 := rs (se 1 (by rfl) ⟨4645187, by rfl⟩) R9290375
theorem R66919 : Reach 66919 := rs (se 1 (by rfl) ⟨50189, by rfl⟩) R100379
theorem R133217 : Reach 133217 := rs (se 2 (by rfl) ⟨49956, by rfl⟩) R99913
theorem R264545 : Reach 264545 := rs (se 2 (by rfl) ⟨99204, by rfl⟩) R198409
theorem R68735 : Reach 68735 := rs (se 1 (by rfl) ⟨51551, by rfl⟩) R103103
theorem R134567 : Reach 134567 := rs (se 1 (by rfl) ⟨100925, by rfl⟩) R201851
theorem R167615 : Reach 167615 := rs (se 1 (by rfl) ⟨125711, by rfl⟩) R251423
theorem R69403 : Reach 69403 := rs (se 1 (by rfl) ⟨52052, by rfl⟩) R104105
theorem R200879 : Reach 200879 := rs (se 1 (by rfl) ⟨150659, by rfl⟩) R301319
theorem R201599 : Reach 201599 := rs (se 1 (by rfl) ⟨151199, by rfl⟩) R302399
theorem R103801 : Reach 103801 := rs (se 2 (by rfl) ⟨38925, by rfl⟩) R77851
theorem R137159 : Reach 137159 := rs (se 1 (by rfl) ⟨102869, by rfl⟩) R205739
theorem R202985 : Reach 202985 := rs (se 2 (by rfl) ⟨76119, by rfl⟩) R152239
theorem R39323 : Reach 39323 := rs (se 1 (by rfl) ⟨29492, by rfl⟩) R58985
theorem R39423 : Reach 39423 := rs (se 1 (by rfl) ⟨29567, by rfl⟩) R59135
theorem R39963 : Reach 39963 := rs (se 1 (by rfl) ⟨29972, by rfl⟩) R59945
theorem R40091 : Reach 40091 := rs (se 1 (by rfl) ⟨30068, by rfl⟩) R60137
theorem R40127 : Reach 40127 := rs (se 1 (by rfl) ⟨30095, by rfl⟩) R60191
theorem R40239 : Reach 40239 := rs (se 1 (by rfl) ⟨30179, by rfl⟩) R60359
theorem R138617 : Reach 138617 := rs (se 2 (by rfl) ⟨51981, by rfl⟩) R103963
theorem R40347 : Reach 40347 := rs (se 1 (by rfl) ⟨30260, by rfl⟩) R60521
theorem R40447 : Reach 40447 := rs (se 1 (by rfl) ⟨30335, by rfl⟩) R60671
theorem R597871 : Reach 597871 := rs (se 1 (by rfl) ⟨448403, by rfl⟩) R896807
theorem R4530167 : Reach 4530167 := rs (se 1 (by rfl) ⟨3397625, by rfl⟩) R6795251
theorem R2236481 : Reach 2236481 := rs (se 2 (by rfl) ⟨838680, by rfl⟩) R1677361
theorem R270823 : Reach 270823 := rs (se 1 (by rfl) ⟨203117, by rfl⟩) R406235
theorem R41455 : Reach 41455 := rs (se 1 (by rfl) ⟨31091, by rfl⟩) R62183
theorem R402043 : Reach 402043 := rs (se 1 (by rfl) ⟨301532, by rfl⟩) R603065
theorem R304235 : Reach 304235 := rs (se 1 (by rfl) ⟨228176, by rfl⟩) R456353
theorem R238747 : Reach 238747 := rs (se 1 (by rfl) ⟨179060, by rfl⟩) R358121
theorem R173279 : Reach 173279 := rs (se 1 (by rfl) ⟨129959, by rfl⟩) R259919
theorem R75239 : Reach 75239 := rs (se 1 (by rfl) ⟨56429, by rfl⟩) R112859
theorem R140777 : Reach 140777 := rs (se 2 (by rfl) ⟨52791, by rfl⟩) R105583
theorem R42495 : Reach 42495 := rs (se 1 (by rfl) ⟨31871, by rfl⟩) R63743
theorem R140831 : Reach 140831 := rs (se 1 (by rfl) ⟨105623, by rfl⟩) R211247
theorem R239383 : Reach 239383 := rs (se 1 (by rfl) ⟨179537, by rfl⟩) R359075
theorem R43003 : Reach 43003 := rs (se 1 (by rfl) ⟨32252, by rfl⟩) R64505
theorem R207035 : Reach 207035 := rs (se 1 (by rfl) ⟨155276, by rfl⟩) R310553
theorem R175081 : Reach 175081 := rs (se 2 (by rfl) ⟨65655, by rfl⟩) R131311
theorem R142361 : Reach 142361 := rs (se 2 (by rfl) ⟨53385, by rfl⟩) R106771
theorem R44059 : Reach 44059 := rs (se 1 (by rfl) ⟨33044, by rfl⟩) R66089
theorem R44527 : Reach 44527 := rs (se 1 (by rfl) ⟨33395, by rfl⟩) R66791
theorem R634463 : Reach 634463 := rs (se 1 (by rfl) ⟨475847, by rfl⟩) R951695
theorem R77449 : Reach 77449 := rs (se 2 (by rfl) ⟨29043, by rfl⟩) R58087
theorem R536863 : Reach 536863 := rs (se 1 (by rfl) ⟨402647, by rfl⟩) R805295
theorem R275399 : Reach 275399 := rs (se 1 (by rfl) ⟨206549, by rfl⟩) R413099
theorem R144665 : Reach 144665 := rs (se 2 (by rfl) ⟨54249, by rfl⟩) R108499
theorem R144719 : Reach 144719 := rs (se 1 (by rfl) ⟨108539, by rfl⟩) R217079
theorem R46543 : Reach 46543 := rs (se 1 (by rfl) ⟨34907, by rfl⟩) R69815
theorem R2143739 : Reach 2143739 := rs (se 1 (by rfl) ⟨1607804, by rfl⟩) R3215609
theorem R243647 : Reach 243647 := rs (se 1 (by rfl) ⟨182735, by rfl⟩) R365471
theorem R80183 : Reach 80183 := rs (se 1 (by rfl) ⟨60137, by rfl⟩) R120275
theorem R26589505 : Reach 26589505 := rs (se 2 (by rfl) ⟨9971064, by rfl⟩) R19942129
theorem R473849 : Reach 473849 := rs (se 2 (by rfl) ⟨177693, by rfl⟩) R355387
theorem R1064083 : Reach 1064083 := rs (se 1 (by rfl) ⟨798062, by rfl⟩) R1596125
theorem R48487 : Reach 48487 := rs (se 1 (by rfl) ⟨36365, by rfl⟩) R72731
theorem R245413 : Reach 245413 := rs (se 4 (by rfl) ⟨23007, by rfl⟩) R46015
theorem R1064933 : Reach 1064933 := rs (se 4 (by rfl) ⟨99837, by rfl⟩) R199675
theorem R6603227 : Reach 6603227 := rs (se 1 (by rfl) ⟨4952420, by rfl⟩) R9904841
theorem R181727 : Reach 181727 := rs (se 1 (by rfl) ⟨136295, by rfl⟩) R272591
theorem R215945 : Reach 215945 := rs (se 2 (by rfl) ⟨80979, by rfl⟩) R161959
theorem R150653 : Reach 150653 := rs (se 3 (by rfl) ⟨28247, by rfl⟩) R56495
theorem R53227 : Reach 53227 := rs (se 1 (by rfl) ⟨39920, by rfl⟩) R79841
theorem R249911 : Reach 249911 := rs (se 1 (by rfl) ⟨187433, by rfl⟩) R374867
theorem R151775 : Reach 151775 := rs (se 1 (by rfl) ⟨113831, by rfl⟩) R227663
theorem R152543 : Reach 152543 := rs (se 1 (by rfl) ⟨114407, by rfl⟩) R228815
theorem R283945 : Reach 283945 := rs (se 2 (by rfl) ⟨106479, by rfl⟩) R212959
theorem R317753 : Reach 317753 := rs (se 2 (by rfl) ⟨119157, by rfl⟩) R238315
theorem R154081 : Reach 154081 := rs (se 2 (by rfl) ⟨57780, by rfl⟩) R115561
theorem R285191 : Reach 285191 := rs (se 1 (by rfl) ⟨213893, by rfl⟩) R427787
theorem R154169 : Reach 154169 := rs (se 2 (by rfl) ⟨57813, by rfl⟩) R115627
theorem R908495 : Reach 908495 := rs (se 1 (by rfl) ⟨681371, by rfl⟩) R1362743
theorem R285905 : Reach 285905 := rs (se 2 (by rfl) ⟨107214, by rfl⟩) R214429
theorem R220409 : Reach 220409 := rs (se 2 (by rfl) ⟨82653, by rfl⟩) R165307
theorem R122539 : Reach 122539 := rs (se 1 (by rfl) ⟨91904, by rfl⟩) R183809
theorem R89999 : Reach 89999 := rs (se 1 (by rfl) ⟨67499, by rfl⟩) R134999
theorem R90107 : Reach 90107 := rs (se 1 (by rfl) ⟨67580, by rfl⟩) R135161
theorem R90863 : Reach 90863 := rs (se 1 (by rfl) ⟨68147, by rfl⟩) R136295
theorem R58679 : Reach 58679 := rs (se 1 (by rfl) ⟨44009, by rfl⟩) R88019
theorem R58727 : Reach 58727 := rs (se 1 (by rfl) ⟨44045, by rfl⟩) R88091
theorem R58751 : Reach 58751 := rs (se 1 (by rfl) ⟨44063, by rfl⟩) R88127
theorem R779939 : Reach 779939 := rs (se 1 (by rfl) ⟨584954, by rfl⟩) R1169909
theorem R59387 : Reach 59387 := rs (se 1 (by rfl) ⟨44540, by rfl⟩) R89081
theorem R92215 : Reach 92215 := rs (se 1 (by rfl) ⟨69161, by rfl⟩) R138323
theorem R59567 : Reach 59567 := rs (se 1 (by rfl) ⟨44675, by rfl⟩) R89351
theorem R59855 : Reach 59855 := rs (se 1 (by rfl) ⟨44891, by rfl⟩) R89783
theorem R60713 : Reach 60713 := rs (se 2 (by rfl) ⟨22767, by rfl⟩) R45535
theorem R60719 : Reach 60719 := rs (se 1 (by rfl) ⟨45539, by rfl⟩) R91079
theorem R93671 : Reach 93671 := rs (se 1 (by rfl) ⟨70253, by rfl⟩) R140507
theorem R60911 : Reach 60911 := rs (se 1 (by rfl) ⟨45683, by rfl⟩) R91367
theorem R93743 : Reach 93743 := rs (se 1 (by rfl) ⟨70307, by rfl⟩) R140615
theorem R61049 : Reach 61049 := rs (se 2 (by rfl) ⟨22893, by rfl⟩) R45787
theorem R93833 : Reach 93833 := rs (se 2 (by rfl) ⟨35187, by rfl⟩) R70375
theorem R159785 : Reach 159785 := rs (se 2 (by rfl) ⟨59919, by rfl⟩) R119839
theorem R61547 : Reach 61547 := rs (se 1 (by rfl) ⟨46160, by rfl⟩) R92321
theorem R192719 : Reach 192719 := rs (se 1 (by rfl) ⟨144539, by rfl⟩) R289079
theorem R553355 : Reach 553355 := rs (se 1 (by rfl) ⟨415016, by rfl⟩) R830033
theorem R160319 : Reach 160319 := rs (se 1 (by rfl) ⟨120239, by rfl⟩) R240479
theorem R62063 : Reach 62063 := rs (se 1 (by rfl) ⟨46547, by rfl⟩) R93095
theorem R1176605 : Reach 1176605 := rs (se 3 (by rfl) ⟨220613, by rfl⟩) R441227
theorem R95399 : Reach 95399 := rs (se 1 (by rfl) ⟨71549, by rfl⟩) R143099
theorem R62633 : Reach 62633 := rs (se 2 (by rfl) ⟨23487, by rfl⟩) R46975
theorem R62975 : Reach 62975 := rs (se 1 (by rfl) ⟨47231, by rfl⟩) R94463
theorem R63467 : Reach 63467 := rs (se 1 (by rfl) ⟨47600, by rfl⟩) R95201
theorem R96569 : Reach 96569 := rs (se 2 (by rfl) ⟨36213, by rfl⟩) R72427
theorem R63881 : Reach 63881 := rs (se 2 (by rfl) ⟨23955, by rfl⟩) R47911
theorem R64283 : Reach 64283 := rs (se 1 (by rfl) ⟨48212, by rfl⟩) R96425
theorem R261035 : Reach 261035 := rs (se 1 (by rfl) ⟨195776, by rfl⟩) R391553
theorem R64585 : Reach 64585 := rs (se 2 (by rfl) ⟨24219, by rfl⟩) R48439
theorem R64619 : Reach 64619 := rs (se 1 (by rfl) ⟨48464, by rfl⟩) R96929
theorem R491255 : Reach 491255 := rs (se 1 (by rfl) ⟨368441, by rfl⟩) R736883
theorem R130913 : Reach 130913 := rs (se 2 (by rfl) ⟨49092, by rfl⟩) R98185
theorem R4129055 : Reach 4129055 := rs (se 1 (by rfl) ⟨3096791, by rfl⟩) R6193583
theorem R361097 : Reach 361097 := rs (se 2 (by rfl) ⟨135411, by rfl⟩) R270823
theorem R100435 : Reach 100435 := rs (se 1 (by rfl) ⟨75326, by rfl⟩) R150653
theorem R821765 : Reach 821765 := rs (se 4 (by rfl) ⟨77040, by rfl⟩) R154081
theorem R166607 : Reach 166607 := rs (se 1 (by rfl) ⟨124955, by rfl⟩) R249911
theorem R133919 : Reach 133919 := rs (se 1 (by rfl) ⟨100439, by rfl⟩) R200879
theorem R101183 : Reach 101183 := rs (se 1 (by rfl) ⟨75887, by rfl⟩) R151775
theorem R134399 : Reach 134399 := rs (se 1 (by rfl) ⟨100799, by rfl⟩) R201599
theorem R101695 : Reach 101695 := rs (se 1 (by rfl) ⟨76271, by rfl⟩) R152543
theorem R233441 : Reach 233441 := rs (se 2 (by rfl) ⟨87540, by rfl⟩) R175081
theorem R135323 : Reach 135323 := rs (se 1 (by rfl) ⟨101492, by rfl⟩) R202985
theorem R102779 : Reach 102779 := rs (se 1 (by rfl) ⟨77084, by rfl⟩) R154169
theorem R103265 : Reach 103265 := rs (se 2 (by rfl) ⟨38724, by rfl⟩) R77449
theorem R70969 : Reach 70969 := rs (se 2 (by rfl) ⟨26613, by rfl⟩) R53227
theorem R3020111 : Reach 3020111 := rs (se 1 (by rfl) ⟨2265083, by rfl⟩) R4530167
theorem R202823 : Reach 202823 := rs (se 1 (by rfl) ⟨152117, by rfl⟩) R304235
theorem R39119 : Reach 39119 := rs (se 1 (by rfl) ⟨29339, by rfl⟩) R58679
theorem R39151 : Reach 39151 := rs (se 1 (by rfl) ⟨29363, by rfl⟩) R58727
theorem R39167 : Reach 39167 := rs (se 1 (by rfl) ⟨29375, by rfl⟩) R58751
theorem R39591 : Reach 39591 := rs (se 1 (by rfl) ⟨29693, by rfl⟩) R59387
theorem R39711 : Reach 39711 := rs (se 1 (by rfl) ⟨29783, by rfl⟩) R59567
theorem R138023 : Reach 138023 := rs (se 1 (by rfl) ⟨103517, by rfl⟩) R207035
theorem R39903 : Reach 39903 := rs (se 1 (by rfl) ⟨29927, by rfl⟩) R59855
theorem R138401 : Reach 138401 := rs (se 2 (by rfl) ⟨51900, by rfl⟩) R103801
theorem R40475 : Reach 40475 := rs (se 1 (by rfl) ⟨30356, by rfl⟩) R60713
theorem R40479 : Reach 40479 := rs (se 1 (by rfl) ⟨30359, by rfl⟩) R60719
theorem R40607 : Reach 40607 := rs (se 1 (by rfl) ⟨30455, by rfl⟩) R60911
theorem R40699 : Reach 40699 := rs (se 1 (by rfl) ⟨30524, by rfl⟩) R61049
theorem R106523 : Reach 106523 := rs (se 1 (by rfl) ⟨79892, by rfl⟩) R159785
theorem R41031 : Reach 41031 := rs (se 1 (by rfl) ⟨30773, by rfl⟩) R61547
theorem R368903 : Reach 368903 := rs (se 1 (by rfl) ⟨276677, by rfl⟩) R553355
theorem R106879 : Reach 106879 := rs (se 1 (by rfl) ⟨80159, by rfl⟩) R160319
theorem R41375 : Reach 41375 := rs (se 1 (by rfl) ⟨31031, by rfl⟩) R62063
theorem R41755 : Reach 41755 := rs (se 1 (by rfl) ⟨31316, by rfl⟩) R62633
theorem R41983 : Reach 41983 := rs (se 1 (by rfl) ⟨31487, by rfl⟩) R62975
theorem R42311 : Reach 42311 := rs (se 1 (by rfl) ⟨31733, by rfl⟩) R63467
theorem R1418777 : Reach 1418777 := rs (se 2 (by rfl) ⟨532041, by rfl⟩) R1064083
theorem R42587 : Reach 42587 := rs (se 1 (by rfl) ⟨31940, by rfl⟩) R63881
theorem R42855 : Reach 42855 := rs (se 1 (by rfl) ⟨32141, by rfl⟩) R64283
theorem R174023 : Reach 174023 := rs (se 1 (by rfl) ⟨130517, by rfl⟩) R261035
theorem R43079 : Reach 43079 := rs (se 1 (by rfl) ⟨32309, by rfl⟩) R64619
theorem R797161 : Reach 797161 := rs (se 2 (by rfl) ⟨298935, by rfl⟩) R597871
theorem R4402151 : Reach 4402151 := rs (se 1 (by rfl) ⟨3301613, by rfl⟩) R6603227
theorem R536057 : Reach 536057 := rs (se 2 (by rfl) ⟨201021, by rfl⟩) R402043
theorem R176363 : Reach 176363 := rs (se 1 (by rfl) ⟨132272, by rfl⟩) R264545
theorem R143963 : Reach 143963 := rs (se 1 (by rfl) ⟨107972, by rfl⟩) R215945
theorem R45823 : Reach 45823 := rs (se 1 (by rfl) ⟨34367, by rfl⟩) R68735
theorem R111743 : Reach 111743 := rs (se 1 (by rfl) ⟨83807, by rfl⟩) R167615
theorem R211835 : Reach 211835 := rs (se 1 (by rfl) ⟨158876, by rfl⟩) R317753
theorem R605663 : Reach 605663 := rs (se 1 (by rfl) ⟨454247, by rfl⟩) R908495
theorem R146939 : Reach 146939 := rs (se 1 (by rfl) ⟨110204, by rfl⟩) R220409
theorem R1490987 : Reach 1490987 := rs (se 1 (by rfl) ⟨1118240, by rfl⟩) R2236481
theorem R115519 : Reach 115519 := rs (se 1 (by rfl) ⟨86639, by rfl⟩) R173279
theorem R50159 : Reach 50159 := rs (se 1 (by rfl) ⟨37619, by rfl⟩) R75239
theorem R378593 : Reach 378593 := rs (se 2 (by rfl) ⟨141972, by rfl⟩) R283945
theorem R183599 : Reach 183599 := rs (se 1 (by rfl) ⟨137699, by rfl⟩) R275399
theorem R1429159 : Reach 1429159 := rs (se 1 (by rfl) ⟨1071869, by rfl⟩) R2143739
theorem R86113 : Reach 86113 := rs (se 2 (by rfl) ⟨32292, by rfl⟩) R64585
theorem R53455 : Reach 53455 := rs (se 1 (by rfl) ⟨40091, by rfl⟩) R80183
theorem R315899 : Reach 315899 := rs (se 1 (by rfl) ⟨236924, by rfl⟩) R473849
theorem R87275 : Reach 87275 := rs (se 1 (by rfl) ⟨65456, by rfl⟩) R130913
theorem R709955 : Reach 709955 := rs (se 1 (by rfl) ⟨532466, by rfl⟩) R1064933
theorem R218729 : Reach 218729 := rs (se 2 (by rfl) ⟨82023, by rfl⟩) R164047
theorem R121151 : Reach 121151 := rs (se 1 (by rfl) ⟨90863, by rfl⟩) R181727
theorem R88811 : Reach 88811 := rs (se 1 (by rfl) ⟨66608, by rfl⟩) R133217
theorem R318329 : Reach 318329 := rs (se 2 (by rfl) ⟨119373, by rfl⟩) R238747
theorem R89225 : Reach 89225 := rs (se 2 (by rfl) ⟨33459, by rfl⟩) R66919
theorem R89711 : Reach 89711 := rs (se 1 (by rfl) ⟨67283, by rfl⟩) R134567
theorem R319177 : Reach 319177 := rs (se 2 (by rfl) ⟨119691, by rfl⟩) R239383
theorem R122953 : Reach 122953 := rs (se 2 (by rfl) ⟨46107, by rfl⟩) R92215
theorem R91439 : Reach 91439 := rs (se 1 (by rfl) ⟨68579, by rfl⟩) R137159
theorem R58745 : Reach 58745 := rs (se 2 (by rfl) ⟨22029, by rfl⟩) R44059
theorem R190127 : Reach 190127 := rs (se 1 (by rfl) ⟨142595, by rfl⟩) R285191
theorem R59369 : Reach 59369 := rs (se 2 (by rfl) ⟨22263, by rfl⟩) R44527
theorem R190603 : Reach 190603 := rs (se 1 (by rfl) ⟨142952, by rfl⟩) R285905
theorem R92411 : Reach 92411 := rs (se 1 (by rfl) ⟨69308, by rfl⟩) R138617
theorem R92537 : Reach 92537 := rs (se 2 (by rfl) ⟨34701, by rfl⟩) R69403
theorem R59999 : Reach 59999 := rs (se 1 (by rfl) ⟨44999, by rfl⟩) R89999
theorem R60071 : Reach 60071 := rs (se 1 (by rfl) ⟨45053, by rfl⟩) R90107
theorem R715817 : Reach 715817 := rs (se 2 (by rfl) ⟨268431, by rfl⟩) R536863
theorem R60575 : Reach 60575 := rs (se 1 (by rfl) ⟨45431, by rfl⟩) R90863
theorem R93851 : Reach 93851 := rs (se 1 (by rfl) ⟨70388, by rfl⟩) R140777
theorem R93887 : Reach 93887 := rs (se 1 (by rfl) ⟨70415, by rfl⟩) R140831
theorem R519959 : Reach 519959 := rs (se 1 (by rfl) ⟨389969, by rfl⟩) R779939
theorem R62057 : Reach 62057 := rs (se 2 (by rfl) ⟨23271, by rfl⟩) R46543
theorem R94907 : Reach 94907 := rs (se 1 (by rfl) ⟨71180, by rfl⟩) R142361
theorem R62447 : Reach 62447 := rs (se 1 (by rfl) ⟨46835, by rfl⟩) R93671
theorem R62495 : Reach 62495 := rs (se 1 (by rfl) ⟨46871, by rfl⟩) R93743
theorem R422975 : Reach 422975 := rs (se 1 (by rfl) ⟨317231, by rfl⟩) R634463
theorem R62555 : Reach 62555 := rs (se 1 (by rfl) ⟨46916, by rfl⟩) R93833
theorem R128479 : Reach 128479 := rs (se 1 (by rfl) ⟨96359, by rfl⟩) R192719
theorem R35452673 : Reach 35452673 := rs (se 2 (by rfl) ⟨13294752, by rfl⟩) R26589505
theorem R784403 : Reach 784403 := rs (se 1 (by rfl) ⟨588302, by rfl⟩) R1176605
theorem R63599 : Reach 63599 := rs (se 1 (by rfl) ⟨47699, by rfl⟩) R95399
theorem R96443 : Reach 96443 := rs (se 1 (by rfl) ⟨72332, by rfl⟩) R144665
theorem R1308869 : Reach 1308869 := rs (se 4 (by rfl) ⟨122706, by rfl⟩) R245413
theorem R96479 : Reach 96479 := rs (se 1 (by rfl) ⟨72359, by rfl⟩) R144719
theorem R162431 : Reach 162431 := rs (se 1 (by rfl) ⟨121823, by rfl⟩) R243647
theorem R64379 : Reach 64379 := rs (se 1 (by rfl) ⟨48284, by rfl⟩) R96569
theorem R64649 : Reach 64649 := rs (se 2 (by rfl) ⟨24243, by rfl⟩) R48487
theorem R163385 : Reach 163385 := rs (se 2 (by rfl) ⟨61269, by rfl⟩) R122539
theorem R327503 : Reach 327503 := rs (se 1 (by rfl) ⟨245627, by rfl⟩) R491255
theorem R163937 : Reach 163937 := rs (se 2 (by rfl) ⟨61476, by rfl⟩) R122953
theorem R2752703 : Reach 2752703 := rs (se 1 (by rfl) ⟨2064527, by rfl⟩) R4129055
theorem R459269 : Reach 459269 := rs (se 4 (by rfl) ⟨43056, by rfl⟩) R86113
theorem R133757 : Reach 133757 := rs (se 3 (by rfl) ⟨25079, by rfl⟩) R50159
theorem R133913 : Reach 133913 := rs (se 2 (by rfl) ⟨50217, by rfl⟩) R100435
theorem R68519 : Reach 68519 := rs (se 1 (by rfl) ⟨51389, by rfl⟩) R102779
theorem R68843 : Reach 68843 := rs (se 1 (by rfl) ⟨51632, by rfl⟩) R103265
theorem R232733 : Reach 232733 := rs (se 3 (by rfl) ⟨43637, by rfl⟩) R87275
theorem R135215 : Reach 135215 := rs (se 1 (by rfl) ⟨101411, by rfl⟩) R202823
theorem R135593 : Reach 135593 := rs (se 2 (by rfl) ⟨50847, by rfl⟩) R101695
theorem R1905545 : Reach 1905545 := rs (se 2 (by rfl) ⟨714579, by rfl⟩) R1429159
theorem R71015 : Reach 71015 := rs (se 1 (by rfl) ⟨53261, by rfl⟩) R106523
theorem R71273 : Reach 71273 := rs (se 2 (by rfl) ⟨26727, by rfl⟩) R53455
theorem R39163 : Reach 39163 := rs (se 1 (by rfl) ⟨29372, by rfl⟩) R58745
theorem R39579 : Reach 39579 := rs (se 1 (by rfl) ⟨29684, by rfl⟩) R59369
theorem R39999 : Reach 39999 := rs (se 1 (by rfl) ⟨29999, by rfl⟩) R59999
theorem R40047 : Reach 40047 := rs (se 1 (by rfl) ⟨30035, by rfl⟩) R60071
theorem R171305 : Reach 171305 := rs (se 2 (by rfl) ⟨64239, by rfl⟩) R128479
theorem R40383 : Reach 40383 := rs (se 1 (by rfl) ⟨30287, by rfl⟩) R60575
theorem R269821 : Reach 269821 := rs (se 3 (by rfl) ⟨50591, by rfl⟩) R101183
theorem R41371 : Reach 41371 := rs (se 1 (by rfl) ⟨31028, by rfl⟩) R62057
theorem R41631 : Reach 41631 := rs (se 1 (by rfl) ⟨31223, by rfl⟩) R62447
theorem R41663 : Reach 41663 := rs (se 1 (by rfl) ⟨31247, by rfl⟩) R62495
theorem R41703 : Reach 41703 := rs (se 1 (by rfl) ⟨31277, by rfl⟩) R62555
theorem R74495 : Reach 74495 := rs (se 1 (by rfl) ⟨55871, by rfl⟩) R111743
theorem R23635115 : Reach 23635115 := rs (se 1 (by rfl) ⟨17726336, by rfl⟩) R35452673
theorem R42399 : Reach 42399 := rs (se 1 (by rfl) ⟨31799, by rfl⟩) R63599
theorem R108287 : Reach 108287 := rs (se 1 (by rfl) ⟨81215, by rfl⟩) R162431
theorem R141223 : Reach 141223 := rs (se 1 (by rfl) ⟨105917, by rfl⟩) R211835
theorem R42919 : Reach 42919 := rs (se 1 (by rfl) ⟨32189, by rfl⟩) R64379
theorem R43099 : Reach 43099 := rs (se 1 (by rfl) ⟨32324, by rfl⟩) R64649
theorem R403775 : Reach 403775 := rs (se 1 (by rfl) ⟨302831, by rfl⟩) R605663
theorem R108923 : Reach 108923 := rs (se 1 (by rfl) ⟨81692, by rfl⟩) R163385
theorem R3975965 : Reach 3975965 := rs (se 3 (by rfl) ⟨745493, by rfl⟩) R1490987
theorem R240731 : Reach 240731 := rs (se 1 (by rfl) ⟨180548, by rfl⟩) R361097
theorem R142505 : Reach 142505 := rs (se 2 (by rfl) ⟨53439, by rfl⟩) R106879
theorem R111071 : Reach 111071 := rs (se 1 (by rfl) ⟨83303, by rfl⟩) R166607
theorem R210599 : Reach 210599 := rs (se 1 (by rfl) ⟨157949, by rfl⟩) R315899
theorem R1062881 : Reach 1062881 := rs (se 2 (by rfl) ⟨398580, by rfl⟩) R797161
theorem R473303 : Reach 473303 := rs (se 1 (by rfl) ⟨354977, by rfl⟩) R709955
theorem R2013407 : Reach 2013407 := rs (se 1 (by rfl) ⟨1510055, by rfl⟩) R3020111
theorem R145819 : Reach 145819 := rs (se 1 (by rfl) ⟨109364, by rfl⟩) R218729
theorem R80767 : Reach 80767 := rs (se 1 (by rfl) ⟨60575, by rfl⟩) R121151
theorem R507005 : Reach 507005 := rs (se 3 (by rfl) ⟨95063, by rfl⟩) R190127
theorem R212219 : Reach 212219 := rs (se 1 (by rfl) ⟨159164, by rfl⟩) R318329
theorem R245935 : Reach 245935 := rs (se 1 (by rfl) ⟨184451, by rfl⟩) R368903
theorem R116015 : Reach 116015 := rs (se 1 (by rfl) ⟨87011, by rfl⟩) R174023
theorem R2934767 : Reach 2934767 := rs (se 1 (by rfl) ⟨2201075, by rfl⟩) R4402151
theorem R477211 : Reach 477211 := rs (se 1 (by rfl) ⟨357908, by rfl⟩) R715817
theorem R346639 : Reach 346639 := rs (se 1 (by rfl) ⟨259979, by rfl⟩) R519959
theorem R117575 : Reach 117575 := rs (se 1 (by rfl) ⟨88181, by rfl⟩) R176363
theorem R281983 : Reach 281983 := rs (se 1 (by rfl) ⟨211487, by rfl⟩) R422975
theorem R872579 : Reach 872579 := rs (se 1 (by rfl) ⟨654434, by rfl⟩) R1308869
theorem R54265 : Reach 54265 := rs (se 2 (by rfl) ⟨20349, by rfl⟩) R40699
theorem R218335 : Reach 218335 := rs (se 1 (by rfl) ⟨163751, by rfl⟩) R327503
theorem R154025 : Reach 154025 := rs (se 2 (by rfl) ⟨57759, by rfl⟩) R115519
theorem R252395 : Reach 252395 := rs (se 1 (by rfl) ⟨189296, by rfl⟩) R378593
theorem R547843 : Reach 547843 := rs (se 1 (by rfl) ⟨410882, by rfl⟩) R821765
theorem R253085 : Reach 253085 := rs (se 3 (by rfl) ⟨47453, by rfl⟩) R94907
theorem R89279 : Reach 89279 := rs (se 1 (by rfl) ⟨66959, by rfl⟩) R133919
theorem R89599 : Reach 89599 := rs (se 1 (by rfl) ⟨67199, by rfl⟩) R134399
theorem R122399 : Reach 122399 := rs (se 1 (by rfl) ⟨91799, by rfl⟩) R183599
theorem R155627 : Reach 155627 := rs (se 1 (by rfl) ⟨116720, by rfl⟩) R233441
theorem R90215 : Reach 90215 := rs (se 1 (by rfl) ⟨67661, by rfl⟩) R135323
theorem R254137 : Reach 254137 := rs (se 2 (by rfl) ⟨95301, by rfl⟩) R190603
theorem R59207 : Reach 59207 := rs (se 1 (by rfl) ⟨44405, by rfl⟩) R88811
theorem R92015 : Reach 92015 := rs (se 1 (by rfl) ⟨69011, by rfl⟩) R138023
theorem R59483 : Reach 59483 := rs (se 1 (by rfl) ⟨44612, by rfl⟩) R89225
theorem R92267 : Reach 92267 := rs (se 1 (by rfl) ⟨69200, by rfl⟩) R138401
theorem R59807 : Reach 59807 := rs (se 1 (by rfl) ⟨44855, by rfl⟩) R89711
theorem R60959 : Reach 60959 := rs (se 1 (by rfl) ⟨45719, by rfl⟩) R91439
theorem R61097 : Reach 61097 := rs (se 2 (by rfl) ⟨22911, by rfl⟩) R45823
theorem R945851 : Reach 945851 := rs (se 1 (by rfl) ⟨709388, by rfl⟩) R1418777
theorem R61607 : Reach 61607 := rs (se 1 (by rfl) ⟨46205, by rfl⟩) R92411
theorem R61691 : Reach 61691 := rs (se 1 (by rfl) ⟨46268, by rfl⟩) R92537
theorem R94625 : Reach 94625 := rs (se 2 (by rfl) ⟨35484, by rfl⟩) R70969
theorem R357371 : Reach 357371 := rs (se 1 (by rfl) ⟨268028, by rfl⟩) R536057
theorem R62567 : Reach 62567 := rs (se 1 (by rfl) ⟨46925, by rfl⟩) R93851
theorem R62591 : Reach 62591 := rs (se 1 (by rfl) ⟨46943, by rfl⟩) R93887
theorem R95975 : Reach 95975 := rs (se 1 (by rfl) ⟨71981, by rfl⟩) R143963
theorem R391837 : Reach 391837 := rs (se 3 (by rfl) ⟨73469, by rfl⟩) R146939
theorem R522935 : Reach 522935 := rs (se 1 (by rfl) ⟨392201, by rfl⟩) R784403
theorem R64295 : Reach 64295 := rs (se 1 (by rfl) ⟨48221, by rfl⟩) R96443
theorem R64319 : Reach 64319 := rs (se 1 (by rfl) ⟨48239, by rfl⟩) R96479
theorem R425569 : Reach 425569 := rs (se 2 (by rfl) ⟨159588, by rfl⟩) R319177
theorem R1835135 : Reach 1835135 := rs (se 1 (by rfl) ⟨1376351, by rfl⟩) R2752703
theorem R2326877 : Reach 2326877 := rs (se 3 (by rfl) ⟨436289, by rfl⟩) R872579
theorem R1311653 : Reach 1311653 := rs (se 4 (by rfl) ⟨122967, by rfl⟩) R245935
theorem R462185 : Reach 462185 := rs (se 2 (by rfl) ⟨173319, by rfl⟩) R346639
theorem R102683 : Reach 102683 := rs (se 1 (by rfl) ⟨77012, by rfl⟩) R154025
theorem R168263 : Reach 168263 := rs (se 1 (by rfl) ⟨126197, by rfl⟩) R252395
theorem R103751 : Reach 103751 := rs (se 1 (by rfl) ⟨77813, by rfl⟩) R155627
theorem R72191 : Reach 72191 := rs (se 1 (by rfl) ⟨54143, by rfl⟩) R108287
theorem R39471 : Reach 39471 := rs (se 1 (by rfl) ⟨29603, by rfl⟩) R59207
theorem R72353 : Reach 72353 := rs (se 2 (by rfl) ⟨27132, by rfl⟩) R54265
theorem R39655 : Reach 39655 := rs (se 1 (by rfl) ⟨29741, by rfl⟩) R59483
theorem R269183 : Reach 269183 := rs (se 1 (by rfl) ⟨201887, by rfl⟩) R403775
theorem R39871 : Reach 39871 := rs (se 1 (by rfl) ⟨29903, by rfl⟩) R59807
theorem R40639 : Reach 40639 := rs (se 1 (by rfl) ⟨30479, by rfl⟩) R60959
theorem R40731 : Reach 40731 := rs (se 1 (by rfl) ⟨30548, by rfl⟩) R61097
theorem R41071 : Reach 41071 := rs (se 1 (by rfl) ⟨30803, by rfl⟩) R61607
theorem R41127 : Reach 41127 := rs (se 1 (by rfl) ⟨30845, by rfl⟩) R61691
theorem R74047 : Reach 74047 := rs (se 1 (by rfl) ⟨55535, by rfl⟩) R111071
theorem R238247 : Reach 238247 := rs (se 1 (by rfl) ⟨178685, by rfl⟩) R357371
theorem R41711 : Reach 41711 := rs (se 1 (by rfl) ⟨31283, by rfl⟩) R62567
theorem R41727 : Reach 41727 := rs (se 1 (by rfl) ⟨31295, by rfl⟩) R62591
theorem R140399 : Reach 140399 := rs (se 1 (by rfl) ⟨105299, by rfl⟩) R210599
theorem R107689 : Reach 107689 := rs (se 2 (by rfl) ⟨40383, by rfl⟩) R80767
theorem R730457 : Reach 730457 := rs (se 2 (by rfl) ⟨273921, by rfl⟩) R547843
theorem R42863 : Reach 42863 := rs (se 1 (by rfl) ⟨32147, by rfl⟩) R64295
theorem R42879 : Reach 42879 := rs (se 1 (by rfl) ⟨32159, by rfl⟩) R64319
theorem R338003 : Reach 338003 := rs (se 1 (by rfl) ⟨253502, by rfl⟩) R507005
theorem R567425 : Reach 567425 := rs (se 2 (by rfl) ⟨212784, by rfl⟩) R425569
theorem R141479 : Reach 141479 := rs (se 1 (by rfl) ⟨106109, by rfl⟩) R212219
theorem R109291 : Reach 109291 := rs (se 1 (by rfl) ⟨81968, by rfl⟩) R163937
theorem R338849 : Reach 338849 := rs (se 2 (by rfl) ⟨127068, by rfl⟩) R254137
theorem R306179 : Reach 306179 := rs (se 1 (by rfl) ⟨229634, by rfl⟩) R459269
theorem R78383 : Reach 78383 := rs (se 1 (by rfl) ⟨58787, by rfl⟩) R117575
theorem R45679 : Reach 45679 := rs (se 1 (by rfl) ⟨34259, by rfl⟩) R68519
theorem R45895 : Reach 45895 := rs (se 1 (by rfl) ⟨34421, by rfl⟩) R68843
theorem R636281 : Reach 636281 := rs (se 2 (by rfl) ⟨238605, by rfl⟩) R477211
theorem R47515 : Reach 47515 := rs (se 1 (by rfl) ⟨35636, by rfl⟩) R71273
theorem R375977 : Reach 375977 := rs (se 2 (by rfl) ⟨140991, by rfl⟩) R281983
theorem R114203 : Reach 114203 := rs (se 1 (by rfl) ⟨85652, by rfl⟩) R171305
theorem R81599 : Reach 81599 := rs (se 1 (by rfl) ⟨61199, by rfl⟩) R122399
theorem R49663 : Reach 49663 := rs (se 1 (by rfl) ⟨37247, by rfl⟩) R74495
theorem R1262141 : Reach 1262141 := rs (se 3 (by rfl) ⟨236651, by rfl⟩) R473303
theorem R674893 : Reach 674893 := rs (se 3 (by rfl) ⟨126542, by rfl⟩) R253085
theorem R708587 : Reach 708587 := rs (se 1 (by rfl) ⟨531440, by rfl⟩) R1062881
theorem R348623 : Reach 348623 := rs (se 1 (by rfl) ⟨261467, by rfl⟩) R522935
theorem R119465 : Reach 119465 := rs (se 2 (by rfl) ⟨44799, by rfl⟩) R89599
theorem R1956511 : Reach 1956511 := rs (se 1 (by rfl) ⟨1467383, by rfl⟩) R2934767
theorem R89171 : Reach 89171 := rs (se 1 (by rfl) ⟨66878, by rfl⟩) R133757
theorem R89275 : Reach 89275 := rs (se 1 (by rfl) ⟨66956, by rfl⟩) R133913
theorem R777701 : Reach 777701 := rs (se 4 (by rfl) ⟨72909, by rfl⟩) R145819
theorem R155155 : Reach 155155 := rs (se 1 (by rfl) ⟨116366, by rfl⟩) R232733
theorem R188297 : Reach 188297 := rs (se 2 (by rfl) ⟨70611, by rfl⟩) R141223
theorem R90143 : Reach 90143 := rs (se 1 (by rfl) ⟨67607, by rfl⟩) R135215
theorem R90395 : Reach 90395 := rs (se 1 (by rfl) ⟨67796, by rfl⟩) R135593
theorem R1237493 : Reach 1237493 := rs (se 5 (by rfl) ⟨58007, by rfl⟩) R116015
theorem R1270363 : Reach 1270363 := rs (se 1 (by rfl) ⟨952772, by rfl⟩) R1905545
theorem R189373 : Reach 189373 := rs (se 3 (by rfl) ⟨35507, by rfl⟩) R71015
theorem R59519 : Reach 59519 := rs (se 1 (by rfl) ⟨44639, by rfl⟩) R89279
theorem R60143 : Reach 60143 := rs (se 1 (by rfl) ⟨45107, by rfl⟩) R90215
theorem R15756743 : Reach 15756743 := rs (se 1 (by rfl) ⟨11817557, by rfl⟩) R23635115
theorem R290461 : Reach 290461 := rs (se 3 (by rfl) ⟨54461, by rfl⟩) R108923
theorem R61343 : Reach 61343 := rs (se 1 (by rfl) ⟨46007, by rfl⟩) R92015
theorem R61511 : Reach 61511 := rs (se 1 (by rfl) ⟨46133, by rfl⟩) R92267
theorem R291113 : Reach 291113 := rs (se 2 (by rfl) ⟨109167, by rfl⟩) R218335
theorem R2650643 : Reach 2650643 := rs (se 1 (by rfl) ⟨1987982, by rfl⟩) R3975965
theorem R160487 : Reach 160487 := rs (se 1 (by rfl) ⟨120365, by rfl⟩) R240731
theorem R95003 : Reach 95003 := rs (se 1 (by rfl) ⟨71252, by rfl⟩) R142505
theorem R63083 : Reach 63083 := rs (se 1 (by rfl) ⟨47312, by rfl⟩) R94625
theorem R522449 : Reach 522449 := rs (se 2 (by rfl) ⟨195918, by rfl⟩) R391837
theorem R63983 : Reach 63983 := rs (se 1 (by rfl) ⟨47987, by rfl⟩) R95975
theorem R1342271 : Reach 1342271 := rs (se 1 (by rfl) ⟨1006703, by rfl⟩) R2013407
theorem R2522269 : Reach 2522269 := rs (se 3 (by rfl) ⟨472925, by rfl⟩) R945851
theorem R359761 : Reach 359761 := rs (se 2 (by rfl) ⟨134910, by rfl⟩) R269821
theorem R98729 : Reach 98729 := rs (se 2 (by rfl) ⟨37023, by rfl⟩) R74047
theorem R66217 : Reach 66217 := rs (se 2 (by rfl) ⟨24831, by rfl⟩) R49663
theorem R68455 : Reach 68455 := rs (se 1 (by rfl) ⟨51341, by rfl⟩) R102683
theorem R232415 : Reach 232415 := rs (se 1 (by rfl) ⟨174311, by rfl⟩) R348623
theorem R69167 : Reach 69167 := rs (se 1 (by rfl) ⟨51875, by rfl⟩) R103751
theorem R824995 : Reach 824995 := rs (se 1 (by rfl) ⟨618746, by rfl⟩) R1237493
theorem R39679 : Reach 39679 := rs (se 1 (by rfl) ⟨29759, by rfl⟩) R59519
theorem R40095 : Reach 40095 := rs (se 1 (by rfl) ⟨30071, by rfl⟩) R60143
theorem R204119 : Reach 204119 := rs (se 1 (by rfl) ⟨153089, by rfl⟩) R306179
theorem R3579389 : Reach 3579389 := rs (se 3 (by rfl) ⟨671135, by rfl⟩) R1342271
theorem R40895 : Reach 40895 := rs (se 1 (by rfl) ⟨30671, by rfl⟩) R61343
theorem R41007 : Reach 41007 := rs (se 1 (by rfl) ⟨30755, by rfl⟩) R61511
theorem R106991 : Reach 106991 := rs (se 1 (by rfl) ⟨80243, by rfl⟩) R160487
theorem R42055 : Reach 42055 := rs (se 1 (by rfl) ⟨31541, by rfl⟩) R63083
theorem R2073869 : Reach 2073869 := rs (se 3 (by rfl) ⟨388850, by rfl⟩) R777701
theorem R42655 : Reach 42655 := rs (se 1 (by rfl) ⟨31991, by rfl⟩) R63983
theorem R206873 : Reach 206873 := rs (se 2 (by rfl) ⟨77577, by rfl⟩) R155155
theorem R76135 : Reach 76135 := rs (se 1 (by rfl) ⟨57101, by rfl⟩) R114203
theorem R1223423 : Reach 1223423 := rs (se 1 (by rfl) ⟨917567, by rfl⟩) R1835135
theorem R1551251 : Reach 1551251 := rs (se 1 (by rfl) ⟨1163438, by rfl⟩) R2326877
theorem R143585 : Reach 143585 := rs (se 2 (by rfl) ⟨53844, by rfl⟩) R107689
theorem R308123 : Reach 308123 := rs (se 1 (by rfl) ⟨231092, by rfl⟩) R462185
theorem R472391 : Reach 472391 := rs (se 1 (by rfl) ⟨354293, by rfl⟩) R708587
theorem R112175 : Reach 112175 := rs (se 1 (by rfl) ⟨84131, by rfl⟩) R168263
theorem R79643 : Reach 79643 := rs (se 1 (by rfl) ⟨59732, by rfl⟩) R119465
theorem R145721 : Reach 145721 := rs (se 2 (by rfl) ⟨54645, by rfl⟩) R109291
theorem R899857 : Reach 899857 := rs (se 2 (by rfl) ⟨337446, by rfl⟩) R674893
theorem R48127 : Reach 48127 := rs (se 1 (by rfl) ⟨36095, by rfl⟩) R72191
theorem R48235 : Reach 48235 := rs (se 1 (by rfl) ⟨36176, by rfl⟩) R72353
theorem R179455 : Reach 179455 := rs (se 1 (by rfl) ⟨134591, by rfl⟩) R269183
theorem R13452101 : Reach 13452101 := rs (se 4 (by rfl) ⟨1261134, by rfl⟩) R2522269
theorem R378283 : Reach 378283 := rs (se 1 (by rfl) ⟨283712, by rfl⟩) R567425
theorem R870389 : Reach 870389 := rs (se 5 (by rfl) ⟨40799, by rfl⟩) R81599
theorem R10504495 : Reach 10504495 := rs (se 1 (by rfl) ⟨7878371, by rfl⟩) R15756743
theorem R52255 : Reach 52255 := rs (se 1 (by rfl) ⟨39191, by rfl⟩) R78383
theorem R2608681 : Reach 2608681 := rs (se 2 (by rfl) ⟨978255, by rfl⟩) R1956511
theorem R348299 : Reach 348299 := rs (se 1 (by rfl) ⟨261224, by rfl⟩) R522449
theorem R119033 : Reach 119033 := rs (se 2 (by rfl) ⟨44637, by rfl⟩) R89275
theorem R479681 : Reach 479681 := rs (se 2 (by rfl) ⟨179880, by rfl⟩) R359761
theorem R250651 : Reach 250651 := rs (se 1 (by rfl) ⟨187988, by rfl⟩) R375977
theorem R841427 : Reach 841427 := rs (se 1 (by rfl) ⟨631070, by rfl⟩) R1262141
theorem R874435 : Reach 874435 := rs (se 1 (by rfl) ⟨655826, by rfl⟩) R1311653
theorem R1693817 : Reach 1693817 := rs (se 2 (by rfl) ⟨635181, by rfl⟩) R1270363
theorem R252497 : Reach 252497 := rs (se 2 (by rfl) ⟨94686, by rfl⟩) R189373
theorem R59447 : Reach 59447 := rs (se 1 (by rfl) ⟨44585, by rfl⟩) R89171
theorem R387281 : Reach 387281 := rs (se 2 (by rfl) ⟨145230, by rfl⟩) R290461
theorem R125531 : Reach 125531 := rs (se 1 (by rfl) ⟨94148, by rfl⟩) R188297
theorem R60095 : Reach 60095 := rs (se 1 (by rfl) ⟨45071, by rfl⟩) R90143
theorem R60263 : Reach 60263 := rs (se 1 (by rfl) ⟨45197, by rfl⟩) R90395
theorem R158831 : Reach 158831 := rs (se 1 (by rfl) ⟨119123, by rfl⟩) R238247
theorem R93599 : Reach 93599 := rs (se 1 (by rfl) ⟨70199, by rfl⟩) R140399
theorem R60905 : Reach 60905 := rs (se 2 (by rfl) ⟨22839, by rfl⟩) R45679
theorem R486971 : Reach 486971 := rs (se 1 (by rfl) ⟨365228, by rfl⟩) R730457
theorem R61193 : Reach 61193 := rs (se 2 (by rfl) ⟨22947, by rfl⟩) R45895
theorem R225335 : Reach 225335 := rs (se 1 (by rfl) ⟨169001, by rfl⟩) R338003
theorem R94319 : Reach 94319 := rs (se 1 (by rfl) ⟨70739, by rfl⟩) R141479
theorem R225899 : Reach 225899 := rs (se 1 (by rfl) ⟨169424, by rfl⟩) R338849
theorem R194075 : Reach 194075 := rs (se 1 (by rfl) ⟨145556, by rfl⟩) R291113
theorem R1767095 : Reach 1767095 := rs (se 1 (by rfl) ⟨1325321, by rfl⟩) R2650643
theorem R63335 : Reach 63335 := rs (se 1 (by rfl) ⟨47501, by rfl⟩) R95003
theorem R63353 : Reach 63353 := rs (se 2 (by rfl) ⟨23757, by rfl⟩) R47515
theorem R424187 : Reach 424187 := rs (se 1 (by rfl) ⟨318140, by rfl⟩) R636281
theorem R65819 : Reach 65819 := rs (se 1 (by rfl) ⟨49364, by rfl⟩) R98729
theorem R232199 : Reach 232199 := rs (se 1 (by rfl) ⟨174149, by rfl⟩) R348299
theorem R101513 : Reach 101513 := rs (se 2 (by rfl) ⟨38067, by rfl⟩) R76135
theorem R560951 : Reach 560951 := rs (se 1 (by rfl) ⟨420713, by rfl⟩) R841427
theorem R69673 : Reach 69673 := rs (se 2 (by rfl) ⟨26127, by rfl⟩) R52255
theorem R168331 : Reach 168331 := rs (se 1 (by rfl) ⟨126248, by rfl⟩) R252497
theorem R365093 : Reach 365093 := rs (se 4 (by rfl) ⟨34227, by rfl⟩) R68455
theorem R3478241 : Reach 3478241 := rs (se 2 (by rfl) ⟨1304340, by rfl⟩) R2608681
theorem R136079 : Reach 136079 := rs (se 1 (by rfl) ⟨102059, by rfl⟩) R204119
theorem R71327 : Reach 71327 := rs (se 1 (by rfl) ⟨53495, by rfl⟩) R106991
theorem R1382579 : Reach 1382579 := rs (se 1 (by rfl) ⟨1036934, by rfl⟩) R2073869
theorem R334201 : Reach 334201 := rs (se 2 (by rfl) ⟨125325, by rfl⟩) R250651
theorem R137915 : Reach 137915 := rs (se 1 (by rfl) ⟨103436, by rfl⟩) R206873
theorem R39631 : Reach 39631 := rs (se 1 (by rfl) ⟨29723, by rfl⟩) R59447
theorem R40063 : Reach 40063 := rs (se 1 (by rfl) ⟨30047, by rfl⟩) R60095
theorem R40175 : Reach 40175 := rs (se 1 (by rfl) ⟨30131, by rfl⟩) R60263
theorem R105887 : Reach 105887 := rs (se 1 (by rfl) ⟨79415, by rfl⟩) R158831
theorem R40603 : Reach 40603 := rs (se 1 (by rfl) ⟨30452, by rfl⟩) R60905
theorem R40795 : Reach 40795 := rs (se 1 (by rfl) ⟨30596, by rfl⟩) R61193
theorem R205415 : Reach 205415 := rs (se 1 (by rfl) ⟨154061, by rfl⟩) R308123
theorem R74783 : Reach 74783 := rs (se 1 (by rfl) ⟨56087, by rfl⟩) R112175
theorem R42223 : Reach 42223 := rs (se 1 (by rfl) ⟨31667, by rfl⟩) R63335
theorem R42235 : Reach 42235 := rs (se 1 (by rfl) ⟨31676, by rfl⟩) R63353
theorem R239273 : Reach 239273 := rs (se 2 (by rfl) ⟨89727, by rfl⟩) R179455
theorem R504377 : Reach 504377 := rs (se 2 (by rfl) ⟨189141, by rfl⟩) R378283
theorem R46111 : Reach 46111 := rs (se 1 (by rfl) ⟨34583, by rfl⟩) R69167
theorem R79355 : Reach 79355 := rs (se 1 (by rfl) ⟨59516, by rfl⟩) R119033
theorem R14005993 : Reach 14005993 := rs (se 2 (by rfl) ⟨5252247, by rfl⟩) R10504495
theorem R1129211 : Reach 1129211 := rs (se 1 (by rfl) ⟨846908, by rfl⟩) R1693817
theorem R212381 : Reach 212381 := rs (se 3 (by rfl) ⟨39821, by rfl⟩) R79643
theorem R83687 : Reach 83687 := rs (se 1 (by rfl) ⟨62765, by rfl⟩) R125531
theorem R1034167 : Reach 1034167 := rs (se 1 (by rfl) ⟨775625, by rfl⟩) R1551251
theorem R1099993 : Reach 1099993 := rs (se 2 (by rfl) ⟨412497, by rfl⟩) R824995
theorem R1165913 : Reach 1165913 := rs (se 2 (by rfl) ⟨437217, by rfl⟩) R874435
theorem R150223 : Reach 150223 := rs (se 1 (by rfl) ⟨112667, by rfl⟩) R225335
theorem R150599 : Reach 150599 := rs (se 1 (by rfl) ⟨112949, by rfl⟩) R225899
theorem R314927 : Reach 314927 := rs (se 1 (by rfl) ⟨236195, by rfl⟩) R472391
theorem R1199809 : Reach 1199809 := rs (se 2 (by rfl) ⟨449928, by rfl⟩) R899857
theorem R282791 : Reach 282791 := rs (se 1 (by rfl) ⟨212093, by rfl⟩) R424187
theorem R8968067 : Reach 8968067 := rs (se 1 (by rfl) ⟨6726050, by rfl⟩) R13452101
theorem R88289 : Reach 88289 := rs (se 2 (by rfl) ⟨33108, by rfl⟩) R66217
theorem R580259 : Reach 580259 := rs (se 1 (by rfl) ⟨435194, by rfl⟩) R870389
theorem R154943 : Reach 154943 := rs (se 1 (by rfl) ⟨116207, by rfl⟩) R232415
theorem R319787 : Reach 319787 := rs (se 1 (by rfl) ⟨239840, by rfl⟩) R479681
theorem R2386259 : Reach 2386259 := rs (se 1 (by rfl) ⟨1789694, by rfl⟩) R3579389
theorem R258187 : Reach 258187 := rs (se 1 (by rfl) ⟨193640, by rfl⟩) R387281
theorem R815615 : Reach 815615 := rs (se 1 (by rfl) ⟨611711, by rfl⟩) R1223423
theorem R62399 : Reach 62399 := rs (se 1 (by rfl) ⟨46799, by rfl⟩) R93599
theorem R324647 : Reach 324647 := rs (se 1 (by rfl) ⟨243485, by rfl⟩) R486971
theorem R62879 : Reach 62879 := rs (se 1 (by rfl) ⟨47159, by rfl⟩) R94319
theorem R95723 : Reach 95723 := rs (se 1 (by rfl) ⟨71792, by rfl⟩) R143585
theorem R129383 : Reach 129383 := rs (se 1 (by rfl) ⟨97037, by rfl⟩) R194075
theorem R1178063 : Reach 1178063 := rs (se 1 (by rfl) ⟨883547, by rfl⟩) R1767095
theorem R64169 : Reach 64169 := rs (se 2 (by rfl) ⟨24063, by rfl⟩) R48127
theorem R64313 : Reach 64313 := rs (se 2 (by rfl) ⟨24117, by rfl⟩) R48235
theorem R97147 : Reach 97147 := rs (se 1 (by rfl) ⟨72860, by rfl⟩) R145721
theorem R9275309 : Reach 9275309 := rs (se 3 (by rfl) ⟨1739120, by rfl⟩) R3478241
theorem R100399 : Reach 100399 := rs (se 1 (by rfl) ⟨75299, by rfl⟩) R150599
theorem R67675 : Reach 67675 := rs (se 1 (by rfl) ⟨50756, by rfl⟩) R101513
theorem R1378889 : Reach 1378889 := rs (se 2 (by rfl) ⟨517083, by rfl⟩) R1034167
theorem R199421 : Reach 199421 := rs (se 3 (by rfl) ⟨37391, by rfl⟩) R74783
theorem R200297 : Reach 200297 := rs (se 2 (by rfl) ⟨75111, by rfl⟩) R150223
theorem R921719 : Reach 921719 := rs (se 1 (by rfl) ⟨691289, by rfl⟩) R1382579
theorem R103295 : Reach 103295 := rs (se 1 (by rfl) ⟨77471, by rfl⟩) R154943
theorem R70591 : Reach 70591 := rs (se 1 (by rfl) ⟨52943, by rfl⟩) R105887
theorem R136943 : Reach 136943 := rs (se 1 (by rfl) ⟨102707, by rfl⟩) R205415
theorem R336251 : Reach 336251 := rs (se 1 (by rfl) ⟨252188, by rfl⟩) R504377
theorem R41599 : Reach 41599 := rs (se 1 (by rfl) ⟨31199, by rfl⟩) R62399
theorem R41919 : Reach 41919 := rs (se 1 (by rfl) ⟨31439, by rfl⟩) R62879
theorem R42779 : Reach 42779 := rs (se 1 (by rfl) ⟨32084, by rfl⟩) R64169
theorem R42875 : Reach 42875 := rs (se 1 (by rfl) ⟨32156, by rfl⟩) R64313
theorem R141587 : Reach 141587 := rs (se 1 (by rfl) ⟨106190, by rfl⟩) R212381
theorem R175517 : Reach 175517 := rs (se 3 (by rfl) ⟨32909, by rfl⟩) R65819
theorem R209951 : Reach 209951 := rs (se 1 (by rfl) ⟨157463, by rfl⟩) R314927
theorem R373967 : Reach 373967 := rs (se 1 (by rfl) ⟨280475, by rfl⟩) R560951
theorem R243395 : Reach 243395 := rs (se 1 (by rfl) ⟨182546, by rfl⟩) R365093
theorem R47551 : Reach 47551 := rs (se 1 (by rfl) ⟨35663, by rfl⟩) R71327
theorem R5978711 : Reach 5978711 := rs (se 1 (by rfl) ⟨4484033, by rfl⟩) R8968067
theorem R344249 : Reach 344249 := rs (se 2 (by rfl) ⟨129093, by rfl⟩) R258187
theorem R213191 : Reach 213191 := rs (se 1 (by rfl) ⟨159893, by rfl⟩) R319787
theorem R1590839 : Reach 1590839 := rs (se 1 (by rfl) ⟨1193129, by rfl⟩) R2386259
theorem R543743 : Reach 543743 := rs (se 1 (by rfl) ⟨407807, by rfl⟩) R815615
theorem R445601 : Reach 445601 := rs (se 2 (by rfl) ⟨167100, by rfl⟩) R334201
theorem R216431 : Reach 216431 := rs (se 1 (by rfl) ⟨162323, by rfl⟩) R324647
theorem R52903 : Reach 52903 := rs (se 1 (by rfl) ⟨39677, by rfl⟩) R79355
theorem R86255 : Reach 86255 := rs (se 1 (by rfl) ⟨64691, by rfl⟩) R129383
theorem R777275 : Reach 777275 := rs (se 1 (by rfl) ⟨582956, by rfl⟩) R1165913
theorem R154799 : Reach 154799 := rs (se 1 (by rfl) ⟨116099, by rfl⟩) R232199
theorem R188527 : Reach 188527 := rs (se 1 (by rfl) ⟨141395, by rfl⟩) R282791
theorem R1466657 : Reach 1466657 := rs (se 2 (by rfl) ⟨549996, by rfl⟩) R1099993
theorem R90719 : Reach 90719 := rs (se 1 (by rfl) ⟨68039, by rfl⟩) R136079
theorem R58859 : Reach 58859 := rs (se 1 (by rfl) ⟨44144, by rfl⟩) R88289
theorem R386839 : Reach 386839 := rs (se 1 (by rfl) ⟨290129, by rfl⟩) R580259
theorem R91943 : Reach 91943 := rs (se 1 (by rfl) ⟨68957, by rfl⟩) R137915
theorem R223165 : Reach 223165 := rs (se 3 (by rfl) ⟨41843, by rfl⟩) R83687
theorem R1599745 : Reach 1599745 := rs (se 2 (by rfl) ⟨599904, by rfl⟩) R1199809
theorem R92897 : Reach 92897 := rs (se 2 (by rfl) ⟨34836, by rfl⟩) R69673
theorem R224441 : Reach 224441 := rs (se 2 (by rfl) ⟨84165, by rfl⟩) R168331
theorem R159515 : Reach 159515 := rs (se 1 (by rfl) ⟨119636, by rfl⟩) R239273
theorem R61481 : Reach 61481 := rs (se 2 (by rfl) ⟨23055, by rfl⟩) R46111
theorem R18674657 : Reach 18674657 := rs (se 2 (by rfl) ⟨7002996, by rfl⟩) R14005993
theorem R63815 : Reach 63815 := rs (se 1 (by rfl) ⟨47861, by rfl⟩) R95723
theorem R129529 : Reach 129529 := rs (se 2 (by rfl) ⟨48573, by rfl⟩) R97147
theorem R785375 : Reach 785375 := rs (se 1 (by rfl) ⟨589031, by rfl⟩) R1178063
theorem R752807 : Reach 752807 := rs (se 1 (by rfl) ⟨564605, by rfl⟩) R1129211
theorem R229499 : Reach 229499 := rs (se 1 (by rfl) ⟨172124, by rfl⟩) R344249
theorem R919259 : Reach 919259 := rs (se 1 (by rfl) ⟨689444, by rfl⟩) R1378889
theorem R132947 : Reach 132947 := rs (se 1 (by rfl) ⟨99710, by rfl⟩) R199421
theorem R362495 : Reach 362495 := rs (se 1 (by rfl) ⟨271871, by rfl⟩) R543743
theorem R297067 : Reach 297067 := rs (se 1 (by rfl) ⟨222800, by rfl⟩) R445601
theorem R133531 : Reach 133531 := rs (se 1 (by rfl) ⟨100148, by rfl⟩) R200297
theorem R297553 : Reach 297553 := rs (se 2 (by rfl) ⟨111582, by rfl⟩) R223165
theorem R133865 : Reach 133865 := rs (se 2 (by rfl) ⟨50199, by rfl⟩) R100399
theorem R2132993 : Reach 2132993 := rs (se 2 (by rfl) ⟨799872, by rfl⟩) R1599745
theorem R68863 : Reach 68863 := rs (se 1 (by rfl) ⟨51647, by rfl⟩) R103295
theorem R103199 : Reach 103199 := rs (se 1 (by rfl) ⟨77399, by rfl⟩) R154799
theorem R70537 : Reach 70537 := rs (se 2 (by rfl) ⟨26451, by rfl⟩) R52903
theorem R39239 : Reach 39239 := rs (se 1 (by rfl) ⟨29429, by rfl⟩) R58859
theorem R106343 : Reach 106343 := rs (se 1 (by rfl) ⟨79757, by rfl⟩) R159515
theorem R40987 : Reach 40987 := rs (se 1 (by rfl) ⟨30740, by rfl⟩) R61481
theorem R172705 : Reach 172705 := rs (se 2 (by rfl) ⟨64764, by rfl⟩) R129529
theorem R139967 : Reach 139967 := rs (se 1 (by rfl) ⟨104975, by rfl⟩) R209951
theorem R42543 : Reach 42543 := rs (se 1 (by rfl) ⟨31907, by rfl⟩) R63815
theorem R501871 : Reach 501871 := rs (se 1 (by rfl) ⟨376403, by rfl⟩) R752807
theorem R142127 : Reach 142127 := rs (se 1 (by rfl) ⟨106595, by rfl⟩) R213191
theorem R1060559 : Reach 1060559 := rs (se 1 (by rfl) ⟨795419, by rfl⟩) R1590839
theorem R144287 : Reach 144287 := rs (se 1 (by rfl) ⟨108215, by rfl⟩) R216431
theorem R149627 : Reach 149627 := rs (se 1 (by rfl) ⟨112220, by rfl⟩) R224441
theorem R117011 : Reach 117011 := rs (se 1 (by rfl) ⟨87758, by rfl⟩) R175517
theorem R249311 : Reach 249311 := rs (se 1 (by rfl) ⟨186983, by rfl⟩) R373967
theorem R3985807 : Reach 3985807 := rs (se 1 (by rfl) ⟨2989355, by rfl⟩) R5978711
theorem R251369 : Reach 251369 := rs (se 2 (by rfl) ⟨94263, by rfl⟩) R188527
theorem R6183539 : Reach 6183539 := rs (se 1 (by rfl) ⟨4637654, by rfl⟩) R9275309
theorem R614479 : Reach 614479 := rs (se 1 (by rfl) ⟨460859, by rfl⟩) R921719
theorem R90233 : Reach 90233 := rs (se 2 (by rfl) ⟨33837, by rfl⟩) R67675
theorem R57503 : Reach 57503 := rs (se 1 (by rfl) ⟨43127, by rfl⟩) R86255
theorem R91295 : Reach 91295 := rs (se 1 (by rfl) ⟨68471, by rfl⟩) R136943
theorem R518183 : Reach 518183 := rs (se 1 (by rfl) ⟨388637, by rfl⟩) R777275
theorem R977771 : Reach 977771 := rs (se 1 (by rfl) ⟨733328, by rfl⟩) R1466657
theorem R224167 : Reach 224167 := rs (se 1 (by rfl) ⟨168125, by rfl⟩) R336251
theorem R60479 : Reach 60479 := rs (se 1 (by rfl) ⟨45359, by rfl⟩) R90719
theorem R61295 : Reach 61295 := rs (se 1 (by rfl) ⟨45971, by rfl⟩) R91943
theorem R94121 : Reach 94121 := rs (se 2 (by rfl) ⟨35295, by rfl⟩) R70591
theorem R94391 : Reach 94391 := rs (se 1 (by rfl) ⟨70793, by rfl⟩) R141587
theorem R61931 : Reach 61931 := rs (se 1 (by rfl) ⟨46448, by rfl⟩) R92897
theorem R63401 : Reach 63401 := rs (se 2 (by rfl) ⟨23775, by rfl⟩) R47551
theorem R12449771 : Reach 12449771 := rs (se 1 (by rfl) ⟨9337328, by rfl⟩) R18674657
theorem R162263 : Reach 162263 := rs (se 1 (by rfl) ⟨121697, by rfl⟩) R243395
theorem R2063141 : Reach 2063141 := rs (se 4 (by rfl) ⟨193419, by rfl⟩) R386839
theorem R523583 : Reach 523583 := rs (se 1 (by rfl) ⟨392687, by rfl⟩) R785375
theorem R819305 : Reach 819305 := rs (se 2 (by rfl) ⟨307239, by rfl⟩) R614479
theorem R230273 : Reach 230273 := rs (se 2 (by rfl) ⟨86352, by rfl⟩) R172705
theorem R99751 : Reach 99751 := rs (se 1 (by rfl) ⟨74813, by rfl⟩) R149627
theorem R166207 : Reach 166207 := rs (se 1 (by rfl) ⟨124655, by rfl⟩) R249311
theorem R396089 : Reach 396089 := rs (se 2 (by rfl) ⟨148533, by rfl⟩) R297067
theorem R396737 : Reach 396737 := rs (se 2 (by rfl) ⟨148776, by rfl⟩) R297553
theorem R167579 : Reach 167579 := rs (se 1 (by rfl) ⟨125684, by rfl⟩) R251369
theorem R298889 : Reach 298889 := rs (se 2 (by rfl) ⟨112083, by rfl⟩) R224167
theorem R70895 : Reach 70895 := rs (se 1 (by rfl) ⟨53171, by rfl⟩) R106343
theorem R5314409 : Reach 5314409 := rs (se 2 (by rfl) ⟨1992903, by rfl⟩) R3985807
theorem R40319 : Reach 40319 := rs (se 1 (by rfl) ⟨30239, by rfl⟩) R60479
theorem R40863 : Reach 40863 := rs (se 1 (by rfl) ⟨30647, by rfl⟩) R61295
theorem R41287 : Reach 41287 := rs (se 1 (by rfl) ⟨30965, by rfl⟩) R61931
theorem R42267 : Reach 42267 := rs (se 1 (by rfl) ⟨31700, by rfl⟩) R63401
theorem R8299847 : Reach 8299847 := rs (se 1 (by rfl) ⟨6224885, by rfl⟩) R12449771
theorem R108175 : Reach 108175 := rs (se 1 (by rfl) ⟨81131, by rfl⟩) R162263
theorem R241663 : Reach 241663 := rs (se 1 (by rfl) ⟨181247, by rfl⟩) R362495
theorem R78007 : Reach 78007 := rs (se 1 (by rfl) ⟨58505, by rfl⟩) R117011
theorem R1421995 : Reach 1421995 := rs (se 1 (by rfl) ⟨1066496, by rfl⟩) R2132993
theorem R275197 : Reach 275197 := rs (se 3 (by rfl) ⟨51599, by rfl⟩) R103199
theorem R669161 : Reach 669161 := rs (se 2 (by rfl) ⟨250935, by rfl⟩) R501871
theorem R345455 : Reach 345455 := rs (se 1 (by rfl) ⟨259091, by rfl⟩) R518183
theorem R707039 : Reach 707039 := rs (se 1 (by rfl) ⟨530279, by rfl⟩) R1060559
theorem R349055 : Reach 349055 := rs (se 1 (by rfl) ⟨261791, by rfl⟩) R523583
theorem R152999 : Reach 152999 := rs (se 1 (by rfl) ⟨114749, by rfl⟩) R229499
theorem R153341 : Reach 153341 := rs (se 3 (by rfl) ⟨28751, by rfl⟩) R57503
theorem R612839 : Reach 612839 := rs (se 1 (by rfl) ⟨459629, by rfl⟩) R919259
theorem R88631 : Reach 88631 := rs (se 1 (by rfl) ⟨66473, by rfl⟩) R132947
theorem R89243 : Reach 89243 := rs (se 1 (by rfl) ⟨66932, by rfl⟩) R133865
theorem R712165 : Reach 712165 := rs (se 4 (by rfl) ⟨66765, by rfl⟩) R133531
theorem R91817 : Reach 91817 := rs (se 2 (by rfl) ⟨34431, by rfl⟩) R68863
theorem R4122359 : Reach 4122359 := rs (se 1 (by rfl) ⟨3091769, by rfl⟩) R6183539
theorem R60155 : Reach 60155 := rs (se 1 (by rfl) ⟨45116, by rfl⟩) R90233
theorem R93311 : Reach 93311 := rs (se 1 (by rfl) ⟨69983, by rfl⟩) R139967
theorem R60863 : Reach 60863 := rs (se 1 (by rfl) ⟨45647, by rfl⟩) R91295
theorem R94049 : Reach 94049 := rs (se 2 (by rfl) ⟨35268, by rfl⟩) R70537
theorem R94751 : Reach 94751 := rs (se 1 (by rfl) ⟨71063, by rfl⟩) R142127
theorem R651847 : Reach 651847 := rs (se 1 (by rfl) ⟨488885, by rfl⟩) R977771
theorem R62747 : Reach 62747 := rs (se 1 (by rfl) ⟨47060, by rfl⟩) R94121
theorem R62927 : Reach 62927 := rs (se 1 (by rfl) ⟨47195, by rfl⟩) R94391
theorem R96191 : Reach 96191 := rs (se 1 (by rfl) ⟨72143, by rfl⟩) R144287
theorem R1375427 : Reach 1375427 := rs (se 1 (by rfl) ⟨1031570, by rfl⟩) R2063141
theorem R230303 : Reach 230303 := rs (se 1 (by rfl) ⟨172727, by rfl⟩) R345455
theorem R264059 : Reach 264059 := rs (se 1 (by rfl) ⟨198044, by rfl⟩) R396089
theorem R133001 : Reach 133001 := rs (se 2 (by rfl) ⟨49875, by rfl⟩) R99751
theorem R264491 : Reach 264491 := rs (se 1 (by rfl) ⟨198368, by rfl⟩) R396737
theorem R199259 : Reach 199259 := rs (se 1 (by rfl) ⟨149444, by rfl⟩) R298889
theorem R232703 : Reach 232703 := rs (se 1 (by rfl) ⟨174527, by rfl⟩) R349055
theorem R101999 : Reach 101999 := rs (se 1 (by rfl) ⟨76499, by rfl⟩) R152999
theorem R102227 : Reach 102227 := rs (se 1 (by rfl) ⟨76670, by rfl⟩) R153341
theorem R3542939 : Reach 3542939 := rs (se 1 (by rfl) ⟨2657204, by rfl⟩) R5314409
theorem R104009 : Reach 104009 := rs (se 2 (by rfl) ⟨39003, by rfl⟩) R78007
theorem R366929 : Reach 366929 := rs (se 2 (by rfl) ⟨137598, by rfl⟩) R275197
theorem R40103 : Reach 40103 := rs (se 1 (by rfl) ⟨30077, by rfl⟩) R60155
theorem R40575 : Reach 40575 := rs (se 1 (by rfl) ⟨30431, by rfl⟩) R60863
theorem R41831 : Reach 41831 := rs (se 1 (by rfl) ⟨31373, by rfl⟩) R62747
theorem R41951 : Reach 41951 := rs (se 1 (by rfl) ⟨31463, by rfl⟩) R62927
theorem R471359 : Reach 471359 := rs (se 1 (by rfl) ⟨353519, by rfl⟩) R707039
theorem R144233 : Reach 144233 := rs (se 2 (by rfl) ⟨54087, by rfl⟩) R108175
theorem R111719 : Reach 111719 := rs (se 1 (by rfl) ⟨83789, by rfl⟩) R167579
theorem R47263 : Reach 47263 := rs (se 1 (by rfl) ⟨35447, by rfl⟩) R70895
theorem R408559 : Reach 408559 := rs (se 1 (by rfl) ⟨306419, by rfl⟩) R612839
theorem R869129 : Reach 869129 := rs (se 2 (by rfl) ⟨325923, by rfl⟩) R651847
theorem R446107 : Reach 446107 := rs (se 1 (by rfl) ⟨334580, by rfl⟩) R669161
theorem R546203 : Reach 546203 := rs (se 1 (by rfl) ⟨409652, by rfl⟩) R819305
theorem R153515 : Reach 153515 := rs (se 1 (by rfl) ⟨115136, by rfl⟩) R230273
theorem R221609 : Reach 221609 := rs (se 2 (by rfl) ⟨83103, by rfl⟩) R166207
theorem R59087 : Reach 59087 := rs (se 1 (by rfl) ⟨44315, by rfl⟩) R88631
theorem R59495 : Reach 59495 := rs (se 1 (by rfl) ⟨44621, by rfl⟩) R89243
theorem R322217 : Reach 322217 := rs (se 2 (by rfl) ⟨120831, by rfl⟩) R241663
theorem R5533231 : Reach 5533231 := rs (se 1 (by rfl) ⟨4149923, by rfl⟩) R8299847
theorem R1895993 : Reach 1895993 := rs (se 2 (by rfl) ⟨710997, by rfl⟩) R1421995
theorem R61211 : Reach 61211 := rs (se 1 (by rfl) ⟨45908, by rfl⟩) R91817
theorem R2748239 : Reach 2748239 := rs (se 1 (by rfl) ⟨2061179, by rfl⟩) R4122359
theorem R62207 : Reach 62207 := rs (se 1 (by rfl) ⟨46655, by rfl⟩) R93311
theorem R62699 : Reach 62699 := rs (se 1 (by rfl) ⟨47024, by rfl⟩) R94049
theorem R63167 : Reach 63167 := rs (se 1 (by rfl) ⟨47375, by rfl⟩) R94751
theorem R3667805 : Reach 3667805 := rs (se 3 (by rfl) ⟨687713, by rfl⟩) R1375427
theorem R64127 : Reach 64127 := rs (se 1 (by rfl) ⟨48095, by rfl⟩) R96191
theorem R949553 : Reach 949553 := rs (se 2 (by rfl) ⟨356082, by rfl⟩) R712165
theorem R132839 : Reach 132839 := rs (se 1 (by rfl) ⟨99629, by rfl⟩) R199259
theorem R67999 : Reach 67999 := rs (se 1 (by rfl) ⟨50999, by rfl⟩) R101999
theorem R2361959 : Reach 2361959 := rs (se 1 (by rfl) ⟨1771469, by rfl⟩) R3542939
theorem R297917 : Reach 297917 := rs (se 3 (by rfl) ⟨55859, by rfl⟩) R111719
theorem R364135 : Reach 364135 := rs (se 1 (by rfl) ⟨273101, by rfl⟩) R546203
theorem R102343 : Reach 102343 := rs (se 1 (by rfl) ⟨76757, by rfl⟩) R153515
theorem R7377641 : Reach 7377641 := rs (se 2 (by rfl) ⟨2766615, by rfl⟩) R5533231
theorem R594809 : Reach 594809 := rs (se 2 (by rfl) ⟨223053, by rfl⟩) R446107
theorem R39391 : Reach 39391 := rs (se 1 (by rfl) ⟨29543, by rfl⟩) R59087
theorem R39663 : Reach 39663 := rs (se 1 (by rfl) ⟨29747, by rfl⟩) R59495
theorem R40807 : Reach 40807 := rs (se 1 (by rfl) ⟨30605, by rfl⟩) R61211
theorem R41471 : Reach 41471 := rs (se 1 (by rfl) ⟨31103, by rfl⟩) R62207
theorem R41799 : Reach 41799 := rs (se 1 (by rfl) ⟨31349, by rfl⟩) R62699
theorem R42111 : Reach 42111 := rs (se 1 (by rfl) ⟨31583, by rfl⟩) R63167
theorem R42751 : Reach 42751 := rs (se 1 (by rfl) ⟨32063, by rfl⟩) R64127
theorem R633035 : Reach 633035 := rs (se 1 (by rfl) ⟨474776, by rfl⟩) R949553
theorem R272605 : Reach 272605 := rs (se 3 (by rfl) ⟨51113, by rfl⟩) R102227
theorem R1256957 : Reach 1256957 := rs (se 3 (by rfl) ⟨235679, by rfl⟩) R471359
theorem R176039 : Reach 176039 := rs (se 1 (by rfl) ⟨132029, by rfl⟩) R264059
theorem R176327 : Reach 176327 := rs (se 1 (by rfl) ⟨132245, by rfl⟩) R264491
theorem R277357 : Reach 277357 := rs (se 3 (by rfl) ⟨52004, by rfl⟩) R104009
theorem R244619 : Reach 244619 := rs (se 1 (by rfl) ⟨183464, by rfl⟩) R366929
theorem R147739 : Reach 147739 := rs (se 1 (by rfl) ⟨110804, by rfl⟩) R221609
theorem R214811 : Reach 214811 := rs (se 1 (by rfl) ⟨161108, by rfl⟩) R322217
theorem R1263995 : Reach 1263995 := rs (se 1 (by rfl) ⟨947996, by rfl⟩) R1895993
theorem R2445203 : Reach 2445203 := rs (se 1 (by rfl) ⟨1833902, by rfl⟩) R3667805
theorem R544745 : Reach 544745 := rs (se 2 (by rfl) ⟨204279, by rfl⟩) R408559
theorem R579419 : Reach 579419 := rs (se 1 (by rfl) ⟨434564, by rfl⟩) R869129
theorem R153535 : Reach 153535 := rs (se 1 (by rfl) ⟨115151, by rfl⟩) R230303
theorem R88667 : Reach 88667 := rs (se 1 (by rfl) ⟨66500, by rfl⟩) R133001
theorem R155135 : Reach 155135 := rs (se 1 (by rfl) ⟨116351, by rfl⟩) R232703
theorem R1832159 : Reach 1832159 := rs (se 1 (by rfl) ⟨1374119, by rfl⟩) R2748239
theorem R63017 : Reach 63017 := rs (se 2 (by rfl) ⟨23631, by rfl⟩) R47263
theorem R96155 : Reach 96155 := rs (se 1 (by rfl) ⟨72116, by rfl⟩) R144233
theorem R196985 : Reach 196985 := rs (se 2 (by rfl) ⟨73869, by rfl⟩) R147739
theorem R1574639 : Reach 1574639 := rs (se 1 (by rfl) ⟨1180979, by rfl⟩) R2361959
theorem R198611 : Reach 198611 := rs (se 1 (by rfl) ⟨148958, by rfl⟩) R297917
theorem R363163 : Reach 363163 := rs (se 1 (by rfl) ⟨272372, by rfl⟩) R544745
theorem R363473 : Reach 363473 := rs (se 2 (by rfl) ⟨136302, by rfl⟩) R272605
theorem R4918427 : Reach 4918427 := rs (se 1 (by rfl) ⟨3688820, by rfl⟩) R7377641
theorem R396539 : Reach 396539 := rs (se 1 (by rfl) ⟨297404, by rfl⟩) R594809
theorem R103423 : Reach 103423 := rs (se 1 (by rfl) ⟨77567, by rfl⟩) R155135
theorem R136457 : Reach 136457 := rs (se 2 (by rfl) ⟨51171, by rfl⟩) R102343
theorem R204713 : Reach 204713 := rs (se 2 (by rfl) ⟨76767, by rfl⟩) R153535
theorem R1221439 : Reach 1221439 := rs (se 1 (by rfl) ⟨916079, by rfl⟩) R1832159
theorem R42011 : Reach 42011 := rs (se 1 (by rfl) ⟨31508, by rfl⟩) R63017
theorem R369809 : Reach 369809 := rs (se 2 (by rfl) ⟨138678, by rfl⟩) R277357
theorem R143207 : Reach 143207 := rs (se 1 (by rfl) ⟨107405, by rfl⟩) R214811
theorem R837971 : Reach 837971 := rs (se 1 (by rfl) ⟨628478, by rfl⟩) R1256957
theorem R117359 : Reach 117359 := rs (se 1 (by rfl) ⟨88019, by rfl⟩) R176039
theorem R117551 : Reach 117551 := rs (se 1 (by rfl) ⟨88163, by rfl⟩) R176327
theorem R88559 : Reach 88559 := rs (se 1 (by rfl) ⟨66419, by rfl⟩) R132839
theorem R842663 : Reach 842663 := rs (se 1 (by rfl) ⟨631997, by rfl⟩) R1263995
theorem R1630135 : Reach 1630135 := rs (se 1 (by rfl) ⟨1222601, by rfl⟩) R2445203
theorem R90665 : Reach 90665 := rs (se 2 (by rfl) ⟨33999, by rfl⟩) R67999
theorem R386279 : Reach 386279 := rs (se 1 (by rfl) ⟨289709, by rfl⟩) R579419
theorem R59111 : Reach 59111 := rs (se 1 (by rfl) ⟨44333, by rfl⟩) R88667
theorem R485513 : Reach 485513 := rs (se 2 (by rfl) ⟨182067, by rfl⟩) R364135
theorem R422023 : Reach 422023 := rs (se 1 (by rfl) ⟨316517, by rfl⟩) R633035
theorem R64103 : Reach 64103 := rs (se 1 (by rfl) ⟨48077, by rfl⟩) R96155
theorem R163079 : Reach 163079 := rs (se 1 (by rfl) ⟨122309, by rfl⟩) R244619
theorem R131323 : Reach 131323 := rs (se 1 (by rfl) ⟨98492, by rfl⟩) R196985
theorem R1049759 : Reach 1049759 := rs (se 1 (by rfl) ⟨787319, by rfl⟩) R1574639
theorem R132407 : Reach 132407 := rs (se 1 (by rfl) ⟨99305, by rfl⟩) R198611
theorem R558647 : Reach 558647 := rs (se 1 (by rfl) ⟨418985, by rfl⟩) R837971
theorem R3278951 : Reach 3278951 := rs (se 1 (by rfl) ⟨2459213, by rfl⟩) R4918427
theorem R264359 : Reach 264359 := rs (se 1 (by rfl) ⟨198269, by rfl⟩) R396539
theorem R561775 : Reach 561775 := rs (se 1 (by rfl) ⟨421331, by rfl⟩) R842663
theorem R136475 : Reach 136475 := rs (se 1 (by rfl) ⟨102356, by rfl⟩) R204713
theorem R562697 : Reach 562697 := rs (se 2 (by rfl) ⟨211011, by rfl⟩) R422023
theorem R39407 : Reach 39407 := rs (se 1 (by rfl) ⟨29555, by rfl⟩) R59111
theorem R137897 : Reach 137897 := rs (se 2 (by rfl) ⟨51711, by rfl⟩) R103423
theorem R42735 : Reach 42735 := rs (se 1 (by rfl) ⟨32051, by rfl⟩) R64103
theorem R108719 : Reach 108719 := rs (se 1 (by rfl) ⟨81539, by rfl⟩) R163079
theorem R2173513 : Reach 2173513 := rs (se 2 (by rfl) ⟨815067, by rfl⟩) R1630135
theorem R78239 : Reach 78239 := rs (se 1 (by rfl) ⟨58679, by rfl⟩) R117359
theorem R242315 : Reach 242315 := rs (se 1 (by rfl) ⟨181736, by rfl⟩) R363473
theorem R246539 : Reach 246539 := rs (se 1 (by rfl) ⟨184904, by rfl⟩) R369809
theorem R313469 : Reach 313469 := rs (se 3 (by rfl) ⟨58775, by rfl⟩) R117551
theorem R1628585 : Reach 1628585 := rs (se 2 (by rfl) ⟨610719, by rfl⟩) R1221439
theorem R90971 : Reach 90971 := rs (se 1 (by rfl) ⟨68228, by rfl⟩) R136457
theorem R484217 : Reach 484217 := rs (se 2 (by rfl) ⟨181581, by rfl⟩) R363163
theorem R59039 : Reach 59039 := rs (se 1 (by rfl) ⟨44279, by rfl⟩) R88559
theorem R60443 : Reach 60443 := rs (se 1 (by rfl) ⟨45332, by rfl⟩) R90665
theorem R257519 : Reach 257519 := rs (se 1 (by rfl) ⟨193139, by rfl⟩) R386279
theorem R323675 : Reach 323675 := rs (se 1 (by rfl) ⟨242756, by rfl⟩) R485513
theorem R95471 : Reach 95471 := rs (se 1 (by rfl) ⟨71603, by rfl⟩) R143207
theorem R164359 : Reach 164359 := rs (se 1 (by rfl) ⟨123269, by rfl⟩) R246539
theorem R1085723 : Reach 1085723 := rs (se 1 (by rfl) ⟨814292, by rfl⟩) R1628585
theorem R39359 : Reach 39359 := rs (se 1 (by rfl) ⟨29519, by rfl⟩) R59039
theorem R72479 : Reach 72479 := rs (se 1 (by rfl) ⟨54359, by rfl⟩) R108719
theorem R40295 : Reach 40295 := rs (se 1 (by rfl) ⟨30221, by rfl⟩) R60443
theorem R175097 : Reach 175097 := rs (se 2 (by rfl) ⟨65661, by rfl⟩) R131323
theorem R699839 : Reach 699839 := rs (se 1 (by rfl) ⟨524879, by rfl⟩) R1049759
theorem R372431 : Reach 372431 := rs (se 1 (by rfl) ⟨279323, by rfl⟩) R558647
theorem R208979 : Reach 208979 := rs (se 1 (by rfl) ⟨156734, by rfl⟩) R313469
theorem R176239 : Reach 176239 := rs (se 1 (by rfl) ⟨132179, by rfl⟩) R264359
theorem R2898017 : Reach 2898017 := rs (se 2 (by rfl) ⟨1086756, by rfl⟩) R2173513
theorem R375131 : Reach 375131 := rs (se 1 (by rfl) ⟨281348, by rfl⟩) R562697
theorem R215783 : Reach 215783 := rs (se 1 (by rfl) ⟨161837, by rfl⟩) R323675
theorem R52159 : Reach 52159 := rs (se 1 (by rfl) ⟨39119, by rfl⟩) R78239
theorem R88271 : Reach 88271 := rs (se 1 (by rfl) ⟨66203, by rfl⟩) R132407
theorem R2185967 : Reach 2185967 := rs (se 1 (by rfl) ⟨1639475, by rfl⟩) R3278951
theorem R90983 : Reach 90983 := rs (se 1 (by rfl) ⟨68237, by rfl⟩) R136475
theorem R91931 : Reach 91931 := rs (se 1 (by rfl) ⟨68948, by rfl⟩) R137897
theorem R60647 : Reach 60647 := rs (se 1 (by rfl) ⟨45485, by rfl⟩) R90971
theorem R322811 : Reach 322811 := rs (se 1 (by rfl) ⟨242108, by rfl⟩) R484217
theorem R749033 : Reach 749033 := rs (se 2 (by rfl) ⟨280887, by rfl⟩) R561775
theorem R161543 : Reach 161543 := rs (se 1 (by rfl) ⟨121157, by rfl⟩) R242315
theorem R63647 : Reach 63647 := rs (se 1 (by rfl) ⟨47735, by rfl⟩) R95471
theorem R686717 : Reach 686717 := rs (se 3 (by rfl) ⟨128759, by rfl⟩) R257519
theorem R723815 : Reach 723815 := rs (se 1 (by rfl) ⟨542861, by rfl⟩) R1085723
theorem R69545 : Reach 69545 := rs (se 2 (by rfl) ⟨26079, by rfl⟩) R52159
theorem R40431 : Reach 40431 := rs (se 1 (by rfl) ⟨30323, by rfl⟩) R60647
theorem R466559 : Reach 466559 := rs (se 1 (by rfl) ⟨349919, by rfl⟩) R699839
theorem R499355 : Reach 499355 := rs (se 1 (by rfl) ⟨374516, by rfl⟩) R749033
theorem R139319 : Reach 139319 := rs (se 1 (by rfl) ⟨104489, by rfl⟩) R208979
theorem R107695 : Reach 107695 := rs (se 1 (by rfl) ⟨80771, by rfl⟩) R161543
theorem R42431 : Reach 42431 := rs (se 1 (by rfl) ⟨31823, by rfl⟩) R63647
theorem R143855 : Reach 143855 := rs (se 1 (by rfl) ⟨107891, by rfl⟩) R215783
theorem R242621 : Reach 242621 := rs (se 3 (by rfl) ⟨45491, by rfl⟩) R90983
theorem R48319 : Reach 48319 := rs (se 1 (by rfl) ⟨36239, by rfl⟩) R72479
theorem R245149 : Reach 245149 := rs (se 3 (by rfl) ⟨45965, by rfl⟩) R91931
theorem R1000349 : Reach 1000349 := rs (se 3 (by rfl) ⟨187565, by rfl⟩) R375131
theorem R116731 : Reach 116731 := rs (se 1 (by rfl) ⟨87548, by rfl⟩) R175097
theorem R215207 : Reach 215207 := rs (se 1 (by rfl) ⟨161405, by rfl⟩) R322811
theorem R248287 : Reach 248287 := rs (se 1 (by rfl) ⟨186215, by rfl⟩) R372431
theorem R939941 : Reach 939941 := rs (se 4 (by rfl) ⟨88119, by rfl⟩) R176239
theorem R219145 : Reach 219145 := rs (se 2 (by rfl) ⟨82179, by rfl⟩) R164359
theorem R58847 : Reach 58847 := rs (se 1 (by rfl) ⟨44135, by rfl⟩) R88271
theorem R5829245 : Reach 5829245 := rs (se 3 (by rfl) ⟨1092983, by rfl⟩) R2185967
theorem R1932011 : Reach 1932011 := rs (se 1 (by rfl) ⟨1449008, by rfl⟩) R2898017
theorem R457811 : Reach 457811 := rs (se 1 (by rfl) ⟨343358, by rfl⟩) R686717
theorem R331049 : Reach 331049 := rs (se 2 (by rfl) ⟨124143, by rfl⟩) R248287
theorem R626627 : Reach 626627 := rs (se 1 (by rfl) ⟨469970, by rfl⟩) R939941
theorem R332903 : Reach 332903 := rs (se 1 (by rfl) ⟨249677, by rfl⟩) R499355
theorem R39231 : Reach 39231 := rs (se 1 (by rfl) ⟨29423, by rfl⟩) R58847
theorem R1288007 : Reach 1288007 := rs (se 1 (by rfl) ⟨966005, by rfl⟩) R1932011
theorem R305207 : Reach 305207 := rs (se 1 (by rfl) ⟨228905, by rfl⟩) R457811
theorem R666899 : Reach 666899 := rs (se 1 (by rfl) ⟨500174, by rfl⟩) R1000349
theorem R143471 : Reach 143471 := rs (se 1 (by rfl) ⟨107603, by rfl⟩) R215207
theorem R46363 : Reach 46363 := rs (se 1 (by rfl) ⟨34772, by rfl⟩) R69545
theorem R311039 : Reach 311039 := rs (se 1 (by rfl) ⟨233279, by rfl⟩) R466559
theorem R574373 : Reach 574373 := rs (se 4 (by rfl) ⟨53847, by rfl⟩) R107695
theorem R3886163 : Reach 3886163 := rs (se 1 (by rfl) ⟨2914622, by rfl⟩) R5829245
theorem R482543 : Reach 482543 := rs (se 1 (by rfl) ⟨361907, by rfl⟩) R723815
theorem R155641 : Reach 155641 := rs (se 2 (by rfl) ⟨58365, by rfl⟩) R116731
theorem R92879 : Reach 92879 := rs (se 1 (by rfl) ⟨69659, by rfl⟩) R139319
theorem R257701 : Reach 257701 := rs (se 4 (by rfl) ⟨24159, by rfl⟩) R48319
theorem R1307461 : Reach 1307461 := rs (se 4 (by rfl) ⟨122574, by rfl⟩) R245149
theorem R292193 : Reach 292193 := rs (se 2 (by rfl) ⟨109572, by rfl⟩) R219145
theorem R95903 : Reach 95903 := rs (se 1 (by rfl) ⟨71927, by rfl⟩) R143855
theorem R161747 : Reach 161747 := rs (se 1 (by rfl) ⟨121310, by rfl⟩) R242621
theorem R2590775 : Reach 2590775 := rs (se 1 (by rfl) ⟨1943081, by rfl⟩) R3886163
theorem R1743281 : Reach 1743281 := rs (se 2 (by rfl) ⟨653730, by rfl⟩) R1307461
theorem R858671 : Reach 858671 := rs (se 1 (by rfl) ⟨644003, by rfl⟩) R1288007
theorem R203471 : Reach 203471 := rs (se 1 (by rfl) ⟨152603, by rfl⟩) R305207
theorem R107831 : Reach 107831 := rs (se 1 (by rfl) ⟨80873, by rfl⟩) R161747
theorem R207359 : Reach 207359 := rs (se 1 (by rfl) ⟨155519, by rfl⟩) R311039
theorem R207521 : Reach 207521 := rs (se 2 (by rfl) ⟨77820, by rfl⟩) R155641
theorem R343601 : Reach 343601 := rs (se 2 (by rfl) ⟨128850, by rfl⟩) R257701
theorem R444599 : Reach 444599 := rs (se 1 (by rfl) ⟨333449, by rfl⟩) R666899
theorem R382589 : Reach 382589 := rs (se 3 (by rfl) ⟨71735, by rfl⟩) R143471
theorem R382915 : Reach 382915 := rs (se 1 (by rfl) ⟨287186, by rfl⟩) R574373
theorem R220699 : Reach 220699 := rs (se 1 (by rfl) ⟨165524, by rfl⟩) R331049
theorem R221935 : Reach 221935 := rs (se 1 (by rfl) ⟨166451, by rfl⟩) R332903
theorem R321695 : Reach 321695 := rs (se 1 (by rfl) ⟨241271, by rfl⟩) R482543
theorem R61817 : Reach 61817 := rs (se 2 (by rfl) ⟨23181, by rfl⟩) R46363
theorem R61919 : Reach 61919 := rs (se 1 (by rfl) ⟨46439, by rfl⟩) R92879
theorem R194795 : Reach 194795 := rs (se 1 (by rfl) ⟨146096, by rfl⟩) R292193
theorem R63935 : Reach 63935 := rs (se 1 (by rfl) ⟨47951, by rfl⟩) R95903
theorem R1671005 : Reach 1671005 := rs (se 3 (by rfl) ⟨313313, by rfl⟩) R626627
theorem R295913 : Reach 295913 := rs (se 2 (by rfl) ⟨110967, by rfl⟩) R221935
theorem R164845 : Reach 164845 := rs (se 3 (by rfl) ⟨30908, by rfl⟩) R61817
theorem R296399 : Reach 296399 := rs (se 1 (by rfl) ⟨222299, by rfl⟩) R444599
theorem R135647 : Reach 135647 := rs (se 1 (by rfl) ⟨101735, by rfl⟩) R203471
theorem R71887 : Reach 71887 := rs (se 1 (by rfl) ⟨53915, by rfl⟩) R107831
theorem R138239 : Reach 138239 := rs (se 1 (by rfl) ⟨103679, by rfl⟩) R207359
theorem R138347 : Reach 138347 := rs (se 1 (by rfl) ⟨103760, by rfl⟩) R207521
theorem R41211 : Reach 41211 := rs (se 1 (by rfl) ⟨30908, by rfl⟩) R61817
theorem R41279 : Reach 41279 := rs (se 1 (by rfl) ⟨30959, by rfl⟩) R61919
theorem R42623 : Reach 42623 := rs (se 1 (by rfl) ⟨31967, by rfl⟩) R63935
theorem R1162187 : Reach 1162187 := rs (se 1 (by rfl) ⟨871640, by rfl⟩) R1743281
theorem R572447 : Reach 572447 := rs (se 1 (by rfl) ⟨429335, by rfl⟩) R858671
theorem R214463 : Reach 214463 := rs (se 1 (by rfl) ⟨160847, by rfl⟩) R321695
theorem R510553 : Reach 510553 := rs (se 2 (by rfl) ⟨191457, by rfl⟩) R382915
theorem R1727183 : Reach 1727183 := rs (se 1 (by rfl) ⟨1295387, by rfl⟩) R2590775
theorem R255059 : Reach 255059 := rs (se 1 (by rfl) ⟨191294, by rfl⟩) R382589
theorem R129863 : Reach 129863 := rs (se 1 (by rfl) ⟨97397, by rfl⟩) R194795
theorem R294265 : Reach 294265 := rs (se 2 (by rfl) ⟨110349, by rfl⟩) R220699
theorem R229067 : Reach 229067 := rs (se 1 (by rfl) ⟨171800, by rfl⟩) R343601
theorem R1114003 : Reach 1114003 := rs (se 1 (by rfl) ⟨835502, by rfl⟩) R1671005
theorem R197275 : Reach 197275 := rs (se 1 (by rfl) ⟨147956, by rfl⟩) R295913
theorem R790397 : Reach 790397 := rs (se 3 (by rfl) ⟨148199, by rfl⟩) R296399
theorem R1151455 : Reach 1151455 := rs (se 1 (by rfl) ⟨863591, by rfl⟩) R1727183
theorem R170039 : Reach 170039 := rs (se 1 (by rfl) ⟨127529, by rfl⟩) R255059
theorem R5941349 : Reach 5941349 := rs (se 4 (by rfl) ⟨557001, by rfl⟩) R1114003
theorem R142975 : Reach 142975 := rs (se 1 (by rfl) ⟨107231, by rfl⟩) R214463
theorem R86575 : Reach 86575 := rs (se 1 (by rfl) ⟨64931, by rfl⟩) R129863
theorem R774791 : Reach 774791 := rs (se 1 (by rfl) ⟨581093, by rfl⟩) R1162187
theorem R381631 : Reach 381631 := rs (se 1 (by rfl) ⟨286223, by rfl⟩) R572447
theorem R152711 : Reach 152711 := rs (se 1 (by rfl) ⟨114533, by rfl⟩) R229067
theorem R90431 : Reach 90431 := rs (se 1 (by rfl) ⟨67823, by rfl⟩) R135647
theorem R680737 : Reach 680737 := rs (se 2 (by rfl) ⟨255276, by rfl⟩) R510553
theorem R92159 : Reach 92159 := rs (se 1 (by rfl) ⟨69119, by rfl⟩) R138239
theorem R92231 : Reach 92231 := rs (se 1 (by rfl) ⟨69173, by rfl⟩) R138347
theorem R879173 : Reach 879173 := rs (se 4 (by rfl) ⟨82422, by rfl⟩) R164845
theorem R95849 : Reach 95849 := rs (se 2 (by rfl) ⟨35943, by rfl⟩) R71887
theorem R392353 : Reach 392353 := rs (se 2 (by rfl) ⟨147132, by rfl⟩) R294265
theorem R263033 : Reach 263033 := rs (se 2 (by rfl) ⟨98637, by rfl⟩) R197275
theorem R526931 : Reach 526931 := rs (se 1 (by rfl) ⟨395198, by rfl⟩) R790397
theorem R101807 : Reach 101807 := rs (se 1 (by rfl) ⟨76355, by rfl⟩) R152711
theorem R762533 : Reach 762533 := rs (se 4 (by rfl) ⟨71487, by rfl⟩) R142975
theorem R115433 : Reach 115433 := rs (se 2 (by rfl) ⟨43287, by rfl⟩) R86575
theorem R508841 : Reach 508841 := rs (se 2 (by rfl) ⟨190815, by rfl⟩) R381631
theorem R907649 : Reach 907649 := rs (se 2 (by rfl) ⟨340368, by rfl⟩) R680737
theorem R516527 : Reach 516527 := rs (se 1 (by rfl) ⟨387395, by rfl⟩) R774791
theorem R453437 : Reach 453437 := rs (se 3 (by rfl) ⟨85019, by rfl⟩) R170039
theorem R60287 : Reach 60287 := rs (se 1 (by rfl) ⟨45215, by rfl⟩) R90431
theorem R1535273 : Reach 1535273 := rs (se 2 (by rfl) ⟨575727, by rfl⟩) R1151455
theorem R2092549 : Reach 2092549 := rs (se 4 (by rfl) ⟨196176, by rfl⟩) R392353
theorem R61439 : Reach 61439 := rs (se 1 (by rfl) ⟨46079, by rfl⟩) R92159
theorem R61487 : Reach 61487 := rs (se 1 (by rfl) ⟨46115, by rfl⟩) R92231
theorem R3960899 : Reach 3960899 := rs (se 1 (by rfl) ⟨2970674, by rfl⟩) R5941349
theorem R586115 : Reach 586115 := rs (se 1 (by rfl) ⟨439586, by rfl⟩) R879173
theorem R63899 : Reach 63899 := rs (se 1 (by rfl) ⟨47924, by rfl⟩) R95849
theorem R67871 : Reach 67871 := rs (se 1 (by rfl) ⟨50903, by rfl⟩) R101807
theorem R2790065 : Reach 2790065 := rs (se 2 (by rfl) ⟨1046274, by rfl⟩) R2092549
theorem R302291 : Reach 302291 := rs (se 1 (by rfl) ⟨226718, by rfl⟩) R453437
theorem R40191 : Reach 40191 := rs (se 1 (by rfl) ⟨30143, by rfl⟩) R60287
theorem R1023515 : Reach 1023515 := rs (se 1 (by rfl) ⟨767636, by rfl⟩) R1535273
theorem R40959 : Reach 40959 := rs (se 1 (by rfl) ⟨30719, by rfl⟩) R61439
theorem R40991 : Reach 40991 := rs (se 1 (by rfl) ⟨30743, by rfl⟩) R61487
theorem R42599 : Reach 42599 := rs (se 1 (by rfl) ⟨31949, by rfl⟩) R63899
theorem R76955 : Reach 76955 := rs (se 1 (by rfl) ⟨57716, by rfl⟩) R115433
theorem R175355 : Reach 175355 := rs (se 1 (by rfl) ⟨131516, by rfl⟩) R263033
theorem R339227 : Reach 339227 := rs (se 1 (by rfl) ⟨254420, by rfl⟩) R508841
theorem R605099 : Reach 605099 := rs (se 1 (by rfl) ⟨453824, by rfl⟩) R907649
theorem R344351 : Reach 344351 := rs (se 1 (by rfl) ⟨258263, by rfl⟩) R516527
theorem R508355 : Reach 508355 := rs (se 1 (by rfl) ⟨381266, by rfl⟩) R762533
theorem R2640599 : Reach 2640599 := rs (se 1 (by rfl) ⟨1980449, by rfl⟩) R3960899
theorem R351287 : Reach 351287 := rs (se 1 (by rfl) ⟨263465, by rfl⟩) R526931
theorem R390743 : Reach 390743 := rs (se 1 (by rfl) ⟨293057, by rfl⟩) R586115
theorem R229567 : Reach 229567 := rs (se 1 (by rfl) ⟨172175, by rfl⟩) R344351
theorem R234191 : Reach 234191 := rs (se 1 (by rfl) ⟨175643, by rfl⟩) R351287
theorem R201527 : Reach 201527 := rs (se 1 (by rfl) ⟨151145, by rfl⟩) R302291
theorem R205213 : Reach 205213 := rs (se 3 (by rfl) ⟨38477, by rfl⟩) R76955
theorem R403399 : Reach 403399 := rs (se 1 (by rfl) ⟨302549, by rfl⟩) R605099
theorem R338903 : Reach 338903 := rs (se 1 (by rfl) ⟨254177, by rfl⟩) R508355
theorem R45247 : Reach 45247 := rs (se 1 (by rfl) ⟨33935, by rfl⟩) R67871
theorem R116903 : Reach 116903 := rs (se 1 (by rfl) ⟨87677, by rfl⟩) R175355
theorem R1760399 : Reach 1760399 := rs (se 1 (by rfl) ⟨1320299, by rfl⟩) R2640599
theorem R1860043 : Reach 1860043 := rs (se 1 (by rfl) ⟨1395032, by rfl⟩) R2790065
theorem R682343 : Reach 682343 := rs (se 1 (by rfl) ⟨511757, by rfl⟩) R1023515
theorem R226151 : Reach 226151 := rs (se 1 (by rfl) ⟨169613, by rfl⟩) R339227
theorem R260495 : Reach 260495 := rs (se 1 (by rfl) ⟨195371, by rfl⟩) R390743
theorem R134351 : Reach 134351 := rs (se 1 (by rfl) ⟨100763, by rfl⟩) R201527
theorem R173663 : Reach 173663 := rs (se 1 (by rfl) ⟨130247, by rfl⟩) R260495
theorem R306089 : Reach 306089 := rs (se 2 (by rfl) ⟨114783, by rfl⟩) R229567
theorem R273617 : Reach 273617 := rs (se 2 (by rfl) ⟨102606, by rfl⟩) R205213
theorem R77935 : Reach 77935 := rs (se 1 (by rfl) ⟨58451, by rfl⟩) R116903
theorem R150767 : Reach 150767 := rs (se 1 (by rfl) ⟨113075, by rfl⟩) R226151
theorem R2151461 : Reach 2151461 := rs (se 4 (by rfl) ⟨201699, by rfl⟩) R403399
theorem R2480057 : Reach 2480057 := rs (se 2 (by rfl) ⟨930021, by rfl⟩) R1860043
theorem R156127 : Reach 156127 := rs (se 1 (by rfl) ⟨117095, by rfl⟩) R234191
theorem R1173599 : Reach 1173599 := rs (se 1 (by rfl) ⟨880199, by rfl⟩) R1760399
theorem R60329 : Reach 60329 := rs (se 2 (by rfl) ⟨22623, by rfl⟩) R45247
theorem R454895 : Reach 454895 := rs (se 1 (by rfl) ⟨341171, by rfl⟩) R682343
theorem R225935 : Reach 225935 := rs (se 1 (by rfl) ⟨169451, by rfl⟩) R338903
theorem R100511 : Reach 100511 := rs (se 1 (by rfl) ⟨75383, by rfl⟩) R150767
theorem R103913 : Reach 103913 := rs (se 2 (by rfl) ⟨38967, by rfl⟩) R77935
theorem R40219 : Reach 40219 := rs (se 1 (by rfl) ⟨30164, by rfl⟩) R60329
theorem R204059 : Reach 204059 := rs (se 1 (by rfl) ⟨153044, by rfl⟩) R306089
theorem R303263 : Reach 303263 := rs (se 1 (by rfl) ⟨227447, by rfl⟩) R454895
theorem R208169 : Reach 208169 := rs (se 2 (by rfl) ⟨78063, by rfl⟩) R156127
theorem R1653371 : Reach 1653371 := rs (se 1 (by rfl) ⟨1240028, by rfl⟩) R2480057
theorem R115775 : Reach 115775 := rs (se 1 (by rfl) ⟨86831, by rfl⟩) R173663
theorem R182411 : Reach 182411 := rs (se 1 (by rfl) ⟨136808, by rfl⟩) R273617
theorem R150623 : Reach 150623 := rs (se 1 (by rfl) ⟨112967, by rfl⟩) R225935
theorem R89567 : Reach 89567 := rs (se 1 (by rfl) ⟨67175, by rfl⟩) R134351
theorem R1434307 : Reach 1434307 := rs (se 1 (by rfl) ⟨1075730, by rfl⟩) R2151461
theorem R782399 : Reach 782399 := rs (se 1 (by rfl) ⟨586799, by rfl⟩) R1173599
theorem R67007 : Reach 67007 := rs (se 1 (by rfl) ⟨50255, by rfl⟩) R100511
theorem R100415 : Reach 100415 := rs (se 1 (by rfl) ⟨75311, by rfl⟩) R150623
theorem R69275 : Reach 69275 := rs (se 1 (by rfl) ⟨51956, by rfl⟩) R103913
theorem R136039 : Reach 136039 := rs (se 1 (by rfl) ⟨102029, by rfl⟩) R204059
theorem R202175 : Reach 202175 := rs (se 1 (by rfl) ⟨151631, by rfl⟩) R303263
theorem R138779 : Reach 138779 := rs (se 1 (by rfl) ⟨104084, by rfl⟩) R208169
theorem R77183 : Reach 77183 := rs (se 1 (by rfl) ⟨57887, by rfl⟩) R115775
theorem R1912409 : Reach 1912409 := rs (se 2 (by rfl) ⟨717153, by rfl⟩) R1434307
theorem R1102247 : Reach 1102247 := rs (se 1 (by rfl) ⟨826685, by rfl⟩) R1653371
theorem R121607 : Reach 121607 := rs (se 1 (by rfl) ⟨91205, by rfl⟩) R182411
theorem R59711 : Reach 59711 := rs (se 1 (by rfl) ⟨44783, by rfl⟩) R89567
theorem R521599 : Reach 521599 := rs (se 1 (by rfl) ⟨391199, by rfl⟩) R782399
theorem R66943 : Reach 66943 := rs (se 1 (by rfl) ⟨50207, by rfl⟩) R100415
theorem R134783 : Reach 134783 := rs (se 1 (by rfl) ⟨101087, by rfl⟩) R202175
theorem R39807 : Reach 39807 := rs (se 1 (by rfl) ⟨29855, by rfl⟩) R59711
theorem R695465 : Reach 695465 := rs (se 2 (by rfl) ⟨260799, by rfl⟩) R521599
theorem R44671 : Reach 44671 := rs (se 1 (by rfl) ⟨33503, by rfl⟩) R67007
theorem R46183 : Reach 46183 := rs (se 1 (by rfl) ⟨34637, by rfl⟩) R69275
theorem R734831 : Reach 734831 := rs (se 1 (by rfl) ⟨551123, by rfl⟩) R1102247
theorem R81071 : Reach 81071 := rs (se 1 (by rfl) ⟨60803, by rfl⟩) R121607
theorem R181385 : Reach 181385 := rs (se 2 (by rfl) ⟨68019, by rfl⟩) R136039
theorem R51455 : Reach 51455 := rs (se 1 (by rfl) ⟨38591, by rfl⟩) R77183
theorem R92519 : Reach 92519 := rs (se 1 (by rfl) ⟨69389, by rfl⟩) R138779
theorem R1274939 : Reach 1274939 := rs (se 1 (by rfl) ⟨956204, by rfl⟩) R1912409
theorem R463643 : Reach 463643 := rs (se 1 (by rfl) ⟨347732, by rfl⟩) R695465
theorem R137213 : Reach 137213 := rs (se 3 (by rfl) ⟨25727, by rfl⟩) R51455
theorem R54047 : Reach 54047 := rs (se 1 (by rfl) ⟨40535, by rfl⟩) R81071
theorem R120923 : Reach 120923 := rs (se 1 (by rfl) ⟨90692, by rfl⟩) R181385
theorem R89257 : Reach 89257 := rs (se 2 (by rfl) ⟨33471, by rfl⟩) R66943
theorem R89855 : Reach 89855 := rs (se 1 (by rfl) ⟨67391, by rfl⟩) R134783
theorem R59561 : Reach 59561 := rs (se 2 (by rfl) ⟨22335, by rfl⟩) R44671
theorem R61577 : Reach 61577 := rs (se 2 (by rfl) ⟨23091, by rfl⟩) R46183
theorem R61679 : Reach 61679 := rs (se 1 (by rfl) ⟨46259, by rfl⟩) R92519
theorem R849959 : Reach 849959 := rs (se 1 (by rfl) ⟨637469, by rfl⟩) R1274939
theorem R489887 : Reach 489887 := rs (se 1 (by rfl) ⟨367415, by rfl⟩) R734831
theorem R39707 : Reach 39707 := rs (se 1 (by rfl) ⟨29780, by rfl⟩) R59561
theorem R41051 : Reach 41051 := rs (se 1 (by rfl) ⟨30788, by rfl⟩) R61577
theorem R41119 : Reach 41119 := rs (se 1 (by rfl) ⟨30839, by rfl⟩) R61679
theorem R566639 : Reach 566639 := rs (se 1 (by rfl) ⟨424979, by rfl⟩) R849959
theorem R144125 : Reach 144125 := rs (se 3 (by rfl) ⟨27023, by rfl⟩) R54047
theorem R309095 : Reach 309095 := rs (se 1 (by rfl) ⟨231821, by rfl⟩) R463643
theorem R80615 : Reach 80615 := rs (se 1 (by rfl) ⟨60461, by rfl⟩) R120923
theorem R119009 : Reach 119009 := rs (se 2 (by rfl) ⟨44628, by rfl⟩) R89257
theorem R91475 : Reach 91475 := rs (se 1 (by rfl) ⟨68606, by rfl⟩) R137213
theorem R59903 : Reach 59903 := rs (se 1 (by rfl) ⟨44927, by rfl⟩) R89855
theorem R326591 : Reach 326591 := rs (se 1 (by rfl) ⟨244943, by rfl⟩) R489887
theorem R39935 : Reach 39935 := rs (se 1 (by rfl) ⟨29951, by rfl⟩) R59903
theorem R206063 : Reach 206063 := rs (se 1 (by rfl) ⟨154547, by rfl⟩) R309095
theorem R377759 : Reach 377759 := rs (se 1 (by rfl) ⟨283319, by rfl⟩) R566639
theorem R214973 : Reach 214973 := rs (se 3 (by rfl) ⟨40307, by rfl⟩) R80615
theorem R217727 : Reach 217727 := rs (se 1 (by rfl) ⟨163295, by rfl⟩) R326591
theorem R317357 : Reach 317357 := rs (se 3 (by rfl) ⟨59504, by rfl⟩) R119009
theorem R60983 : Reach 60983 := rs (se 1 (by rfl) ⟨45737, by rfl⟩) R91475
theorem R96083 : Reach 96083 := rs (se 1 (by rfl) ⟨72062, by rfl⟩) R144125
theorem R137375 : Reach 137375 := rs (se 1 (by rfl) ⟨103031, by rfl⟩) R206063
theorem R40655 : Reach 40655 := rs (se 1 (by rfl) ⟨30491, by rfl⟩) R60983
theorem R143315 : Reach 143315 := rs (se 1 (by rfl) ⟨107486, by rfl⟩) R214973
theorem R145151 : Reach 145151 := rs (se 1 (by rfl) ⟨108863, by rfl⟩) R217727
theorem R211571 : Reach 211571 := rs (se 1 (by rfl) ⟨158678, by rfl⟩) R317357
theorem R251839 : Reach 251839 := rs (se 1 (by rfl) ⟨188879, by rfl⟩) R377759
theorem R64055 : Reach 64055 := rs (se 1 (by rfl) ⟨48041, by rfl⟩) R96083
theorem R335785 : Reach 335785 := rs (se 2 (by rfl) ⟨125919, by rfl⟩) R251839
theorem R42703 : Reach 42703 := rs (se 1 (by rfl) ⟨32027, by rfl⟩) R64055
theorem R141047 : Reach 141047 := rs (se 1 (by rfl) ⟨105785, by rfl⟩) R211571
theorem R91583 : Reach 91583 := rs (se 1 (by rfl) ⟨68687, by rfl⟩) R137375
theorem R95543 : Reach 95543 := rs (se 1 (by rfl) ⟨71657, by rfl⟩) R143315
theorem R96767 : Reach 96767 := rs (se 1 (by rfl) ⟨72575, by rfl⟩) R145151
theorem R447713 : Reach 447713 := rs (se 2 (by rfl) ⟨167892, by rfl⟩) R335785
theorem R61055 : Reach 61055 := rs (se 1 (by rfl) ⟨45791, by rfl⟩) R91583
theorem R94031 : Reach 94031 := rs (se 1 (by rfl) ⟨70523, by rfl⟩) R141047
theorem R63695 : Reach 63695 := rs (se 1 (by rfl) ⟨47771, by rfl⟩) R95543
theorem R64511 : Reach 64511 := rs (se 1 (by rfl) ⟨48383, by rfl⟩) R96767
theorem R298475 : Reach 298475 := rs (se 1 (by rfl) ⟨223856, by rfl⟩) R447713
theorem R40703 : Reach 40703 := rs (se 1 (by rfl) ⟨30527, by rfl⟩) R61055
theorem R42463 : Reach 42463 := rs (se 1 (by rfl) ⟨31847, by rfl⟩) R63695
theorem R43007 : Reach 43007 := rs (se 1 (by rfl) ⟨32255, by rfl⟩) R64511
theorem R62687 : Reach 62687 := rs (se 1 (by rfl) ⟨47015, by rfl⟩) R94031
theorem R198983 : Reach 198983 := rs (se 1 (by rfl) ⟨149237, by rfl⟩) R298475
theorem R41791 : Reach 41791 := rs (se 1 (by rfl) ⟨31343, by rfl⟩) R62687
theorem R530621 : Reach 530621 := rs (se 3 (by rfl) ⟨99491, by rfl⟩) R198983
theorem R353747 : Reach 353747 := rs (se 1 (by rfl) ⟨265310, by rfl⟩) R530621
theorem R235831 : Reach 235831 := rs (se 1 (by rfl) ⟨176873, by rfl⟩) R353747
theorem R314441 : Reach 314441 := rs (se 2 (by rfl) ⟨117915, by rfl⟩) R235831
theorem R209627 : Reach 209627 := rs (se 1 (by rfl) ⟨157220, by rfl⟩) R314441
theorem R139751 : Reach 139751 := rs (se 1 (by rfl) ⟨104813, by rfl⟩) R209627
theorem R93167 : Reach 93167 := rs (se 1 (by rfl) ⟨69875, by rfl⟩) R139751
theorem R62111 : Reach 62111 := rs (se 1 (by rfl) ⟨46583, by rfl⟩) R93167
theorem R41407 : Reach 41407 := rs (se 1 (by rfl) ⟨31055, by rfl⟩) R62111

theorem C0 (j : ℕ) (h1 : 19558 ≤ j) (h2 : j ≤ 20257) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R39117
  · exact R39119
  · exact R39121
  · exact R39123
  · exact R39125
  · exact R39127
  · exact R39129
  · exact R39131
  · exact R39133
  · exact R39135
  · exact R39137
  · exact R39139
  · exact R39141
  · exact R39143
  · exact R39145
  · exact R39147
  · exact R39149
  · exact R39151
  · exact R39153
  · exact R39155
  · exact R39157
  · exact R39159
  · exact R39161
  · exact R39163
  · exact R39165
  · exact R39167
  · exact R39169
  · exact R39171
  · exact R39173
  · exact R39175
  · exact R39177
  · exact R39179
  · exact R39181
  · exact R39183
  · exact R39185
  · exact R39187
  · exact R39189
  · exact R39191
  · exact R39193
  · exact R39195
  · exact R39197
  · exact R39199
  · exact R39201
  · exact R39203
  · exact R39205
  · exact R39207
  · exact R39209
  · exact R39211
  · exact R39213
  · exact R39215
  · exact R39217
  · exact R39219
  · exact R39221
  · exact R39223
  · exact R39225
  · exact R39227
  · exact R39229
  · exact R39231
  · exact R39233
  · exact R39235
  · exact R39237
  · exact R39239
  · exact R39241
  · exact R39243
  · exact R39245
  · exact R39247
  · exact R39249
  · exact R39251
  · exact R39253
  · exact R39255
  · exact R39257
  · exact R39259
  · exact R39261
  · exact R39263
  · exact R39265
  · exact R39267
  · exact R39269
  · exact R39271
  · exact R39273
  · exact R39275
  · exact R39277
  · exact R39279
  · exact R39281
  · exact R39283
  · exact R39285
  · exact R39287
  · exact R39289
  · exact R39291
  · exact R39293
  · exact R39295
  · exact R39297
  · exact R39299
  · exact R39301
  · exact R39303
  · exact R39305
  · exact R39307
  · exact R39309
  · exact R39311
  · exact R39313
  · exact R39315
  · exact R39317
  · exact R39319
  · exact R39321
  · exact R39323
  · exact R39325
  · exact R39327
  · exact R39329
  · exact R39331
  · exact R39333
  · exact R39335
  · exact R39337
  · exact R39339
  · exact R39341
  · exact R39343
  · exact R39345
  · exact R39347
  · exact R39349
  · exact R39351
  · exact R39353
  · exact R39355
  · exact R39357
  · exact R39359
  · exact R39361
  · exact R39363
  · exact R39365
  · exact R39367
  · exact R39369
  · exact R39371
  · exact R39373
  · exact R39375
  · exact R39377
  · exact R39379
  · exact R39381
  · exact R39383
  · exact R39385
  · exact R39387
  · exact R39389
  · exact R39391
  · exact R39393
  · exact R39395
  · exact R39397
  · exact R39399
  · exact R39401
  · exact R39403
  · exact R39405
  · exact R39407
  · exact R39409
  · exact R39411
  · exact R39413
  · exact R39415
  · exact R39417
  · exact R39419
  · exact R39421
  · exact R39423
  · exact R39425
  · exact R39427
  · exact R39429
  · exact R39431
  · exact R39433
  · exact R39435
  · exact R39437
  · exact R39439
  · exact R39441
  · exact R39443
  · exact R39445
  · exact R39447
  · exact R39449
  · exact R39451
  · exact R39453
  · exact R39455
  · exact R39457
  · exact R39459
  · exact R39461
  · exact R39463
  · exact R39465
  · exact R39467
  · exact R39469
  · exact R39471
  · exact R39473
  · exact R39475
  · exact R39477
  · exact R39479
  · exact R39481
  · exact R39483
  · exact R39485
  · exact R39487
  · exact R39489
  · exact R39491
  · exact R39493
  · exact R39495
  · exact R39497
  · exact R39499
  · exact R39501
  · exact R39503
  · exact R39505
  · exact R39507
  · exact R39509
  · exact R39511
  · exact R39513
  · exact R39515
  · exact R39517
  · exact R39519
  · exact R39521
  · exact R39523
  · exact R39525
  · exact R39527
  · exact R39529
  · exact R39531
  · exact R39533
  · exact R39535
  · exact R39537
  · exact R39539
  · exact R39541
  · exact R39543
  · exact R39545
  · exact R39547
  · exact R39549
  · exact R39551
  · exact R39553
  · exact R39555
  · exact R39557
  · exact R39559
  · exact R39561
  · exact R39563
  · exact R39565
  · exact R39567
  · exact R39569
  · exact R39571
  · exact R39573
  · exact R39575
  · exact R39577
  · exact R39579
  · exact R39581
  · exact R39583
  · exact R39585
  · exact R39587
  · exact R39589
  · exact R39591
  · exact R39593
  · exact R39595
  · exact R39597
  · exact R39599
  · exact R39601
  · exact R39603
  · exact R39605
  · exact R39607
  · exact R39609
  · exact R39611
  · exact R39613
  · exact R39615
  · exact R39617
  · exact R39619
  · exact R39621
  · exact R39623
  · exact R39625
  · exact R39627
  · exact R39629
  · exact R39631
  · exact R39633
  · exact R39635
  · exact R39637
  · exact R39639
  · exact R39641
  · exact R39643
  · exact R39645
  · exact R39647
  · exact R39649
  · exact R39651
  · exact R39653
  · exact R39655
  · exact R39657
  · exact R39659
  · exact R39661
  · exact R39663
  · exact R39665
  · exact R39667
  · exact R39669
  · exact R39671
  · exact R39673
  · exact R39675
  · exact R39677
  · exact R39679
  · exact R39681
  · exact R39683
  · exact R39685
  · exact R39687
  · exact R39689
  · exact R39691
  · exact R39693
  · exact R39695
  · exact R39697
  · exact R39699
  · exact R39701
  · exact R39703
  · exact R39705
  · exact R39707
  · exact R39709
  · exact R39711
  · exact R39713
  · exact R39715
  · exact R39717
  · exact R39719
  · exact R39721
  · exact R39723
  · exact R39725
  · exact R39727
  · exact R39729
  · exact R39731
  · exact R39733
  · exact R39735
  · exact R39737
  · exact R39739
  · exact R39741
  · exact R39743
  · exact R39745
  · exact R39747
  · exact R39749
  · exact R39751
  · exact R39753
  · exact R39755
  · exact R39757
  · exact R39759
  · exact R39761
  · exact R39763
  · exact R39765
  · exact R39767
  · exact R39769
  · exact R39771
  · exact R39773
  · exact R39775
  · exact R39777
  · exact R39779
  · exact R39781
  · exact R39783
  · exact R39785
  · exact R39787
  · exact R39789
  · exact R39791
  · exact R39793
  · exact R39795
  · exact R39797
  · exact R39799
  · exact R39801
  · exact R39803
  · exact R39805
  · exact R39807
  · exact R39809
  · exact R39811
  · exact R39813
  · exact R39815
  · exact R39817
  · exact R39819
  · exact R39821
  · exact R39823
  · exact R39825
  · exact R39827
  · exact R39829
  · exact R39831
  · exact R39833
  · exact R39835
  · exact R39837
  · exact R39839
  · exact R39841
  · exact R39843
  · exact R39845
  · exact R39847
  · exact R39849
  · exact R39851
  · exact R39853
  · exact R39855
  · exact R39857
  · exact R39859
  · exact R39861
  · exact R39863
  · exact R39865
  · exact R39867
  · exact R39869
  · exact R39871
  · exact R39873
  · exact R39875
  · exact R39877
  · exact R39879
  · exact R39881
  · exact R39883
  · exact R39885
  · exact R39887
  · exact R39889
  · exact R39891
  · exact R39893
  · exact R39895
  · exact R39897
  · exact R39899
  · exact R39901
  · exact R39903
  · exact R39905
  · exact R39907
  · exact R39909
  · exact R39911
  · exact R39913
  · exact R39915
  · exact R39917
  · exact R39919
  · exact R39921
  · exact R39923
  · exact R39925
  · exact R39927
  · exact R39929
  · exact R39931
  · exact R39933
  · exact R39935
  · exact R39937
  · exact R39939
  · exact R39941
  · exact R39943
  · exact R39945
  · exact R39947
  · exact R39949
  · exact R39951
  · exact R39953
  · exact R39955
  · exact R39957
  · exact R39959
  · exact R39961
  · exact R39963
  · exact R39965
  · exact R39967
  · exact R39969
  · exact R39971
  · exact R39973
  · exact R39975
  · exact R39977
  · exact R39979
  · exact R39981
  · exact R39983
  · exact R39985
  · exact R39987
  · exact R39989
  · exact R39991
  · exact R39993
  · exact R39995
  · exact R39997
  · exact R39999
  · exact R40001
  · exact R40003
  · exact R40005
  · exact R40007
  · exact R40009
  · exact R40011
  · exact R40013
  · exact R40015
  · exact R40017
  · exact R40019
  · exact R40021
  · exact R40023
  · exact R40025
  · exact R40027
  · exact R40029
  · exact R40031
  · exact R40033
  · exact R40035
  · exact R40037
  · exact R40039
  · exact R40041
  · exact R40043
  · exact R40045
  · exact R40047
  · exact R40049
  · exact R40051
  · exact R40053
  · exact R40055
  · exact R40057
  · exact R40059
  · exact R40061
  · exact R40063
  · exact R40065
  · exact R40067
  · exact R40069
  · exact R40071
  · exact R40073
  · exact R40075
  · exact R40077
  · exact R40079
  · exact R40081
  · exact R40083
  · exact R40085
  · exact R40087
  · exact R40089
  · exact R40091
  · exact R40093
  · exact R40095
  · exact R40097
  · exact R40099
  · exact R40101
  · exact R40103
  · exact R40105
  · exact R40107
  · exact R40109
  · exact R40111
  · exact R40113
  · exact R40115
  · exact R40117
  · exact R40119
  · exact R40121
  · exact R40123
  · exact R40125
  · exact R40127
  · exact R40129
  · exact R40131
  · exact R40133
  · exact R40135
  · exact R40137
  · exact R40139
  · exact R40141
  · exact R40143
  · exact R40145
  · exact R40147
  · exact R40149
  · exact R40151
  · exact R40153
  · exact R40155
  · exact R40157
  · exact R40159
  · exact R40161
  · exact R40163
  · exact R40165
  · exact R40167
  · exact R40169
  · exact R40171
  · exact R40173
  · exact R40175
  · exact R40177
  · exact R40179
  · exact R40181
  · exact R40183
  · exact R40185
  · exact R40187
  · exact R40189
  · exact R40191
  · exact R40193
  · exact R40195
  · exact R40197
  · exact R40199
  · exact R40201
  · exact R40203
  · exact R40205
  · exact R40207
  · exact R40209
  · exact R40211
  · exact R40213
  · exact R40215
  · exact R40217
  · exact R40219
  · exact R40221
  · exact R40223
  · exact R40225
  · exact R40227
  · exact R40229
  · exact R40231
  · exact R40233
  · exact R40235
  · exact R40237
  · exact R40239
  · exact R40241
  · exact R40243
  · exact R40245
  · exact R40247
  · exact R40249
  · exact R40251
  · exact R40253
  · exact R40255
  · exact R40257
  · exact R40259
  · exact R40261
  · exact R40263
  · exact R40265
  · exact R40267
  · exact R40269
  · exact R40271
  · exact R40273
  · exact R40275
  · exact R40277
  · exact R40279
  · exact R40281
  · exact R40283
  · exact R40285
  · exact R40287
  · exact R40289
  · exact R40291
  · exact R40293
  · exact R40295
  · exact R40297
  · exact R40299
  · exact R40301
  · exact R40303
  · exact R40305
  · exact R40307
  · exact R40309
  · exact R40311
  · exact R40313
  · exact R40315
  · exact R40317
  · exact R40319
  · exact R40321
  · exact R40323
  · exact R40325
  · exact R40327
  · exact R40329
  · exact R40331
  · exact R40333
  · exact R40335
  · exact R40337
  · exact R40339
  · exact R40341
  · exact R40343
  · exact R40345
  · exact R40347
  · exact R40349
  · exact R40351
  · exact R40353
  · exact R40355
  · exact R40357
  · exact R40359
  · exact R40361
  · exact R40363
  · exact R40365
  · exact R40367
  · exact R40369
  · exact R40371
  · exact R40373
  · exact R40375
  · exact R40377
  · exact R40379
  · exact R40381
  · exact R40383
  · exact R40385
  · exact R40387
  · exact R40389
  · exact R40391
  · exact R40393
  · exact R40395
  · exact R40397
  · exact R40399
  · exact R40401
  · exact R40403
  · exact R40405
  · exact R40407
  · exact R40409
  · exact R40411
  · exact R40413
  · exact R40415
  · exact R40417
  · exact R40419
  · exact R40421
  · exact R40423
  · exact R40425
  · exact R40427
  · exact R40429
  · exact R40431
  · exact R40433
  · exact R40435
  · exact R40437
  · exact R40439
  · exact R40441
  · exact R40443
  · exact R40445
  · exact R40447
  · exact R40449
  · exact R40451
  · exact R40453
  · exact R40455
  · exact R40457
  · exact R40459
  · exact R40461
  · exact R40463
  · exact R40465
  · exact R40467
  · exact R40469
  · exact R40471
  · exact R40473
  · exact R40475
  · exact R40477
  · exact R40479
  · exact R40481
  · exact R40483
  · exact R40485
  · exact R40487
  · exact R40489
  · exact R40491
  · exact R40493
  · exact R40495
  · exact R40497
  · exact R40499
  · exact R40501
  · exact R40503
  · exact R40505
  · exact R40507
  · exact R40509
  · exact R40511
  · exact R40513
  · exact R40515

theorem C1 (j : ℕ) (h1 : 20258 ≤ j) (h2 : j ≤ 20957) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R40517
  · exact R40519
  · exact R40521
  · exact R40523
  · exact R40525
  · exact R40527
  · exact R40529
  · exact R40531
  · exact R40533
  · exact R40535
  · exact R40537
  · exact R40539
  · exact R40541
  · exact R40543
  · exact R40545
  · exact R40547
  · exact R40549
  · exact R40551
  · exact R40553
  · exact R40555
  · exact R40557
  · exact R40559
  · exact R40561
  · exact R40563
  · exact R40565
  · exact R40567
  · exact R40569
  · exact R40571
  · exact R40573
  · exact R40575
  · exact R40577
  · exact R40579
  · exact R40581
  · exact R40583
  · exact R40585
  · exact R40587
  · exact R40589
  · exact R40591
  · exact R40593
  · exact R40595
  · exact R40597
  · exact R40599
  · exact R40601
  · exact R40603
  · exact R40605
  · exact R40607
  · exact R40609
  · exact R40611
  · exact R40613
  · exact R40615
  · exact R40617
  · exact R40619
  · exact R40621
  · exact R40623
  · exact R40625
  · exact R40627
  · exact R40629
  · exact R40631
  · exact R40633
  · exact R40635
  · exact R40637
  · exact R40639
  · exact R40641
  · exact R40643
  · exact R40645
  · exact R40647
  · exact R40649
  · exact R40651
  · exact R40653
  · exact R40655
  · exact R40657
  · exact R40659
  · exact R40661
  · exact R40663
  · exact R40665
  · exact R40667
  · exact R40669
  · exact R40671
  · exact R40673
  · exact R40675
  · exact R40677
  · exact R40679
  · exact R40681
  · exact R40683
  · exact R40685
  · exact R40687
  · exact R40689
  · exact R40691
  · exact R40693
  · exact R40695
  · exact R40697
  · exact R40699
  · exact R40701
  · exact R40703
  · exact R40705
  · exact R40707
  · exact R40709
  · exact R40711
  · exact R40713
  · exact R40715
  · exact R40717
  · exact R40719
  · exact R40721
  · exact R40723
  · exact R40725
  · exact R40727
  · exact R40729
  · exact R40731
  · exact R40733
  · exact R40735
  · exact R40737
  · exact R40739
  · exact R40741
  · exact R40743
  · exact R40745
  · exact R40747
  · exact R40749
  · exact R40751
  · exact R40753
  · exact R40755
  · exact R40757
  · exact R40759
  · exact R40761
  · exact R40763
  · exact R40765
  · exact R40767
  · exact R40769
  · exact R40771
  · exact R40773
  · exact R40775
  · exact R40777
  · exact R40779
  · exact R40781
  · exact R40783
  · exact R40785
  · exact R40787
  · exact R40789
  · exact R40791
  · exact R40793
  · exact R40795
  · exact R40797
  · exact R40799
  · exact R40801
  · exact R40803
  · exact R40805
  · exact R40807
  · exact R40809
  · exact R40811
  · exact R40813
  · exact R40815
  · exact R40817
  · exact R40819
  · exact R40821
  · exact R40823
  · exact R40825
  · exact R40827
  · exact R40829
  · exact R40831
  · exact R40833
  · exact R40835
  · exact R40837
  · exact R40839
  · exact R40841
  · exact R40843
  · exact R40845
  · exact R40847
  · exact R40849
  · exact R40851
  · exact R40853
  · exact R40855
  · exact R40857
  · exact R40859
  · exact R40861
  · exact R40863
  · exact R40865
  · exact R40867
  · exact R40869
  · exact R40871
  · exact R40873
  · exact R40875
  · exact R40877
  · exact R40879
  · exact R40881
  · exact R40883
  · exact R40885
  · exact R40887
  · exact R40889
  · exact R40891
  · exact R40893
  · exact R40895
  · exact R40897
  · exact R40899
  · exact R40901
  · exact R40903
  · exact R40905
  · exact R40907
  · exact R40909
  · exact R40911
  · exact R40913
  · exact R40915
  · exact R40917
  · exact R40919
  · exact R40921
  · exact R40923
  · exact R40925
  · exact R40927
  · exact R40929
  · exact R40931
  · exact R40933
  · exact R40935
  · exact R40937
  · exact R40939
  · exact R40941
  · exact R40943
  · exact R40945
  · exact R40947
  · exact R40949
  · exact R40951
  · exact R40953
  · exact R40955
  · exact R40957
  · exact R40959
  · exact R40961
  · exact R40963
  · exact R40965
  · exact R40967
  · exact R40969
  · exact R40971
  · exact R40973
  · exact R40975
  · exact R40977
  · exact R40979
  · exact R40981
  · exact R40983
  · exact R40985
  · exact R40987
  · exact R40989
  · exact R40991
  · exact R40993
  · exact R40995
  · exact R40997
  · exact R40999
  · exact R41001
  · exact R41003
  · exact R41005
  · exact R41007
  · exact R41009
  · exact R41011
  · exact R41013
  · exact R41015
  · exact R41017
  · exact R41019
  · exact R41021
  · exact R41023
  · exact R41025
  · exact R41027
  · exact R41029
  · exact R41031
  · exact R41033
  · exact R41035
  · exact R41037
  · exact R41039
  · exact R41041
  · exact R41043
  · exact R41045
  · exact R41047
  · exact R41049
  · exact R41051
  · exact R41053
  · exact R41055
  · exact R41057
  · exact R41059
  · exact R41061
  · exact R41063
  · exact R41065
  · exact R41067
  · exact R41069
  · exact R41071
  · exact R41073
  · exact R41075
  · exact R41077
  · exact R41079
  · exact R41081
  · exact R41083
  · exact R41085
  · exact R41087
  · exact R41089
  · exact R41091
  · exact R41093
  · exact R41095
  · exact R41097
  · exact R41099
  · exact R41101
  · exact R41103
  · exact R41105
  · exact R41107
  · exact R41109
  · exact R41111
  · exact R41113
  · exact R41115
  · exact R41117
  · exact R41119
  · exact R41121
  · exact R41123
  · exact R41125
  · exact R41127
  · exact R41129
  · exact R41131
  · exact R41133
  · exact R41135
  · exact R41137
  · exact R41139
  · exact R41141
  · exact R41143
  · exact R41145
  · exact R41147
  · exact R41149
  · exact R41151
  · exact R41153
  · exact R41155
  · exact R41157
  · exact R41159
  · exact R41161
  · exact R41163
  · exact R41165
  · exact R41167
  · exact R41169
  · exact R41171
  · exact R41173
  · exact R41175
  · exact R41177
  · exact R41179
  · exact R41181
  · exact R41183
  · exact R41185
  · exact R41187
  · exact R41189
  · exact R41191
  · exact R41193
  · exact R41195
  · exact R41197
  · exact R41199
  · exact R41201
  · exact R41203
  · exact R41205
  · exact R41207
  · exact R41209
  · exact R41211
  · exact R41213
  · exact R41215
  · exact R41217
  · exact R41219
  · exact R41221
  · exact R41223
  · exact R41225
  · exact R41227
  · exact R41229
  · exact R41231
  · exact R41233
  · exact R41235
  · exact R41237
  · exact R41239
  · exact R41241
  · exact R41243
  · exact R41245
  · exact R41247
  · exact R41249
  · exact R41251
  · exact R41253
  · exact R41255
  · exact R41257
  · exact R41259
  · exact R41261
  · exact R41263
  · exact R41265
  · exact R41267
  · exact R41269
  · exact R41271
  · exact R41273
  · exact R41275
  · exact R41277
  · exact R41279
  · exact R41281
  · exact R41283
  · exact R41285
  · exact R41287
  · exact R41289
  · exact R41291
  · exact R41293
  · exact R41295
  · exact R41297
  · exact R41299
  · exact R41301
  · exact R41303
  · exact R41305
  · exact R41307
  · exact R41309
  · exact R41311
  · exact R41313
  · exact R41315
  · exact R41317
  · exact R41319
  · exact R41321
  · exact R41323
  · exact R41325
  · exact R41327
  · exact R41329
  · exact R41331
  · exact R41333
  · exact R41335
  · exact R41337
  · exact R41339
  · exact R41341
  · exact R41343
  · exact R41345
  · exact R41347
  · exact R41349
  · exact R41351
  · exact R41353
  · exact R41355
  · exact R41357
  · exact R41359
  · exact R41361
  · exact R41363
  · exact R41365
  · exact R41367
  · exact R41369
  · exact R41371
  · exact R41373
  · exact R41375
  · exact R41377
  · exact R41379
  · exact R41381
  · exact R41383
  · exact R41385
  · exact R41387
  · exact R41389
  · exact R41391
  · exact R41393
  · exact R41395
  · exact R41397
  · exact R41399
  · exact R41401
  · exact R41403
  · exact R41405
  · exact R41407
  · exact R41409
  · exact R41411
  · exact R41413
  · exact R41415
  · exact R41417
  · exact R41419
  · exact R41421
  · exact R41423
  · exact R41425
  · exact R41427
  · exact R41429
  · exact R41431
  · exact R41433
  · exact R41435
  · exact R41437
  · exact R41439
  · exact R41441
  · exact R41443
  · exact R41445
  · exact R41447
  · exact R41449
  · exact R41451
  · exact R41453
  · exact R41455
  · exact R41457
  · exact R41459
  · exact R41461
  · exact R41463
  · exact R41465
  · exact R41467
  · exact R41469
  · exact R41471
  · exact R41473
  · exact R41475
  · exact R41477
  · exact R41479
  · exact R41481
  · exact R41483
  · exact R41485
  · exact R41487
  · exact R41489
  · exact R41491
  · exact R41493
  · exact R41495
  · exact R41497
  · exact R41499
  · exact R41501
  · exact R41503
  · exact R41505
  · exact R41507
  · exact R41509
  · exact R41511
  · exact R41513
  · exact R41515
  · exact R41517
  · exact R41519
  · exact R41521
  · exact R41523
  · exact R41525
  · exact R41527
  · exact R41529
  · exact R41531
  · exact R41533
  · exact R41535
  · exact R41537
  · exact R41539
  · exact R41541
  · exact R41543
  · exact R41545
  · exact R41547
  · exact R41549
  · exact R41551
  · exact R41553
  · exact R41555
  · exact R41557
  · exact R41559
  · exact R41561
  · exact R41563
  · exact R41565
  · exact R41567
  · exact R41569
  · exact R41571
  · exact R41573
  · exact R41575
  · exact R41577
  · exact R41579
  · exact R41581
  · exact R41583
  · exact R41585
  · exact R41587
  · exact R41589
  · exact R41591
  · exact R41593
  · exact R41595
  · exact R41597
  · exact R41599
  · exact R41601
  · exact R41603
  · exact R41605
  · exact R41607
  · exact R41609
  · exact R41611
  · exact R41613
  · exact R41615
  · exact R41617
  · exact R41619
  · exact R41621
  · exact R41623
  · exact R41625
  · exact R41627
  · exact R41629
  · exact R41631
  · exact R41633
  · exact R41635
  · exact R41637
  · exact R41639
  · exact R41641
  · exact R41643
  · exact R41645
  · exact R41647
  · exact R41649
  · exact R41651
  · exact R41653
  · exact R41655
  · exact R41657
  · exact R41659
  · exact R41661
  · exact R41663
  · exact R41665
  · exact R41667
  · exact R41669
  · exact R41671
  · exact R41673
  · exact R41675
  · exact R41677
  · exact R41679
  · exact R41681
  · exact R41683
  · exact R41685
  · exact R41687
  · exact R41689
  · exact R41691
  · exact R41693
  · exact R41695
  · exact R41697
  · exact R41699
  · exact R41701
  · exact R41703
  · exact R41705
  · exact R41707
  · exact R41709
  · exact R41711
  · exact R41713
  · exact R41715
  · exact R41717
  · exact R41719
  · exact R41721
  · exact R41723
  · exact R41725
  · exact R41727
  · exact R41729
  · exact R41731
  · exact R41733
  · exact R41735
  · exact R41737
  · exact R41739
  · exact R41741
  · exact R41743
  · exact R41745
  · exact R41747
  · exact R41749
  · exact R41751
  · exact R41753
  · exact R41755
  · exact R41757
  · exact R41759
  · exact R41761
  · exact R41763
  · exact R41765
  · exact R41767
  · exact R41769
  · exact R41771
  · exact R41773
  · exact R41775
  · exact R41777
  · exact R41779
  · exact R41781
  · exact R41783
  · exact R41785
  · exact R41787
  · exact R41789
  · exact R41791
  · exact R41793
  · exact R41795
  · exact R41797
  · exact R41799
  · exact R41801
  · exact R41803
  · exact R41805
  · exact R41807
  · exact R41809
  · exact R41811
  · exact R41813
  · exact R41815
  · exact R41817
  · exact R41819
  · exact R41821
  · exact R41823
  · exact R41825
  · exact R41827
  · exact R41829
  · exact R41831
  · exact R41833
  · exact R41835
  · exact R41837
  · exact R41839
  · exact R41841
  · exact R41843
  · exact R41845
  · exact R41847
  · exact R41849
  · exact R41851
  · exact R41853
  · exact R41855
  · exact R41857
  · exact R41859
  · exact R41861
  · exact R41863
  · exact R41865
  · exact R41867
  · exact R41869
  · exact R41871
  · exact R41873
  · exact R41875
  · exact R41877
  · exact R41879
  · exact R41881
  · exact R41883
  · exact R41885
  · exact R41887
  · exact R41889
  · exact R41891
  · exact R41893
  · exact R41895
  · exact R41897
  · exact R41899
  · exact R41901
  · exact R41903
  · exact R41905
  · exact R41907
  · exact R41909
  · exact R41911
  · exact R41913
  · exact R41915

theorem C2 (j : ℕ) (h1 : 20958 ≤ j) (h2 : j ≤ 21558) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R41917
  · exact R41919
  · exact R41921
  · exact R41923
  · exact R41925
  · exact R41927
  · exact R41929
  · exact R41931
  · exact R41933
  · exact R41935
  · exact R41937
  · exact R41939
  · exact R41941
  · exact R41943
  · exact R41945
  · exact R41947
  · exact R41949
  · exact R41951
  · exact R41953
  · exact R41955
  · exact R41957
  · exact R41959
  · exact R41961
  · exact R41963
  · exact R41965
  · exact R41967
  · exact R41969
  · exact R41971
  · exact R41973
  · exact R41975
  · exact R41977
  · exact R41979
  · exact R41981
  · exact R41983
  · exact R41985
  · exact R41987
  · exact R41989
  · exact R41991
  · exact R41993
  · exact R41995
  · exact R41997
  · exact R41999
  · exact R42001
  · exact R42003
  · exact R42005
  · exact R42007
  · exact R42009
  · exact R42011
  · exact R42013
  · exact R42015
  · exact R42017
  · exact R42019
  · exact R42021
  · exact R42023
  · exact R42025
  · exact R42027
  · exact R42029
  · exact R42031
  · exact R42033
  · exact R42035
  · exact R42037
  · exact R42039
  · exact R42041
  · exact R42043
  · exact R42045
  · exact R42047
  · exact R42049
  · exact R42051
  · exact R42053
  · exact R42055
  · exact R42057
  · exact R42059
  · exact R42061
  · exact R42063
  · exact R42065
  · exact R42067
  · exact R42069
  · exact R42071
  · exact R42073
  · exact R42075
  · exact R42077
  · exact R42079
  · exact R42081
  · exact R42083
  · exact R42085
  · exact R42087
  · exact R42089
  · exact R42091
  · exact R42093
  · exact R42095
  · exact R42097
  · exact R42099
  · exact R42101
  · exact R42103
  · exact R42105
  · exact R42107
  · exact R42109
  · exact R42111
  · exact R42113
  · exact R42115
  · exact R42117
  · exact R42119
  · exact R42121
  · exact R42123
  · exact R42125
  · exact R42127
  · exact R42129
  · exact R42131
  · exact R42133
  · exact R42135
  · exact R42137
  · exact R42139
  · exact R42141
  · exact R42143
  · exact R42145
  · exact R42147
  · exact R42149
  · exact R42151
  · exact R42153
  · exact R42155
  · exact R42157
  · exact R42159
  · exact R42161
  · exact R42163
  · exact R42165
  · exact R42167
  · exact R42169
  · exact R42171
  · exact R42173
  · exact R42175
  · exact R42177
  · exact R42179
  · exact R42181
  · exact R42183
  · exact R42185
  · exact R42187
  · exact R42189
  · exact R42191
  · exact R42193
  · exact R42195
  · exact R42197
  · exact R42199
  · exact R42201
  · exact R42203
  · exact R42205
  · exact R42207
  · exact R42209
  · exact R42211
  · exact R42213
  · exact R42215
  · exact R42217
  · exact R42219
  · exact R42221
  · exact R42223
  · exact R42225
  · exact R42227
  · exact R42229
  · exact R42231
  · exact R42233
  · exact R42235
  · exact R42237
  · exact R42239
  · exact R42241
  · exact R42243
  · exact R42245
  · exact R42247
  · exact R42249
  · exact R42251
  · exact R42253
  · exact R42255
  · exact R42257
  · exact R42259
  · exact R42261
  · exact R42263
  · exact R42265
  · exact R42267
  · exact R42269
  · exact R42271
  · exact R42273
  · exact R42275
  · exact R42277
  · exact R42279
  · exact R42281
  · exact R42283
  · exact R42285
  · exact R42287
  · exact R42289
  · exact R42291
  · exact R42293
  · exact R42295
  · exact R42297
  · exact R42299
  · exact R42301
  · exact R42303
  · exact R42305
  · exact R42307
  · exact R42309
  · exact R42311
  · exact R42313
  · exact R42315
  · exact R42317
  · exact R42319
  · exact R42321
  · exact R42323
  · exact R42325
  · exact R42327
  · exact R42329
  · exact R42331
  · exact R42333
  · exact R42335
  · exact R42337
  · exact R42339
  · exact R42341
  · exact R42343
  · exact R42345
  · exact R42347
  · exact R42349
  · exact R42351
  · exact R42353
  · exact R42355
  · exact R42357
  · exact R42359
  · exact R42361
  · exact R42363
  · exact R42365
  · exact R42367
  · exact R42369
  · exact R42371
  · exact R42373
  · exact R42375
  · exact R42377
  · exact R42379
  · exact R42381
  · exact R42383
  · exact R42385
  · exact R42387
  · exact R42389
  · exact R42391
  · exact R42393
  · exact R42395
  · exact R42397
  · exact R42399
  · exact R42401
  · exact R42403
  · exact R42405
  · exact R42407
  · exact R42409
  · exact R42411
  · exact R42413
  · exact R42415
  · exact R42417
  · exact R42419
  · exact R42421
  · exact R42423
  · exact R42425
  · exact R42427
  · exact R42429
  · exact R42431
  · exact R42433
  · exact R42435
  · exact R42437
  · exact R42439
  · exact R42441
  · exact R42443
  · exact R42445
  · exact R42447
  · exact R42449
  · exact R42451
  · exact R42453
  · exact R42455
  · exact R42457
  · exact R42459
  · exact R42461
  · exact R42463
  · exact R42465
  · exact R42467
  · exact R42469
  · exact R42471
  · exact R42473
  · exact R42475
  · exact R42477
  · exact R42479
  · exact R42481
  · exact R42483
  · exact R42485
  · exact R42487
  · exact R42489
  · exact R42491
  · exact R42493
  · exact R42495
  · exact R42497
  · exact R42499
  · exact R42501
  · exact R42503
  · exact R42505
  · exact R42507
  · exact R42509
  · exact R42511
  · exact R42513
  · exact R42515
  · exact R42517
  · exact R42519
  · exact R42521
  · exact R42523
  · exact R42525
  · exact R42527
  · exact R42529
  · exact R42531
  · exact R42533
  · exact R42535
  · exact R42537
  · exact R42539
  · exact R42541
  · exact R42543
  · exact R42545
  · exact R42547
  · exact R42549
  · exact R42551
  · exact R42553
  · exact R42555
  · exact R42557
  · exact R42559
  · exact R42561
  · exact R42563
  · exact R42565
  · exact R42567
  · exact R42569
  · exact R42571
  · exact R42573
  · exact R42575
  · exact R42577
  · exact R42579
  · exact R42581
  · exact R42583
  · exact R42585
  · exact R42587
  · exact R42589
  · exact R42591
  · exact R42593
  · exact R42595
  · exact R42597
  · exact R42599
  · exact R42601
  · exact R42603
  · exact R42605
  · exact R42607
  · exact R42609
  · exact R42611
  · exact R42613
  · exact R42615
  · exact R42617
  · exact R42619
  · exact R42621
  · exact R42623
  · exact R42625
  · exact R42627
  · exact R42629
  · exact R42631
  · exact R42633
  · exact R42635
  · exact R42637
  · exact R42639
  · exact R42641
  · exact R42643
  · exact R42645
  · exact R42647
  · exact R42649
  · exact R42651
  · exact R42653
  · exact R42655
  · exact R42657
  · exact R42659
  · exact R42661
  · exact R42663
  · exact R42665
  · exact R42667
  · exact R42669
  · exact R42671
  · exact R42673
  · exact R42675
  · exact R42677
  · exact R42679
  · exact R42681
  · exact R42683
  · exact R42685
  · exact R42687
  · exact R42689
  · exact R42691
  · exact R42693
  · exact R42695
  · exact R42697
  · exact R42699
  · exact R42701
  · exact R42703
  · exact R42705
  · exact R42707
  · exact R42709
  · exact R42711
  · exact R42713
  · exact R42715
  · exact R42717
  · exact R42719
  · exact R42721
  · exact R42723
  · exact R42725
  · exact R42727
  · exact R42729
  · exact R42731
  · exact R42733
  · exact R42735
  · exact R42737
  · exact R42739
  · exact R42741
  · exact R42743
  · exact R42745
  · exact R42747
  · exact R42749
  · exact R42751
  · exact R42753
  · exact R42755
  · exact R42757
  · exact R42759
  · exact R42761
  · exact R42763
  · exact R42765
  · exact R42767
  · exact R42769
  · exact R42771
  · exact R42773
  · exact R42775
  · exact R42777
  · exact R42779
  · exact R42781
  · exact R42783
  · exact R42785
  · exact R42787
  · exact R42789
  · exact R42791
  · exact R42793
  · exact R42795
  · exact R42797
  · exact R42799
  · exact R42801
  · exact R42803
  · exact R42805
  · exact R42807
  · exact R42809
  · exact R42811
  · exact R42813
  · exact R42815
  · exact R42817
  · exact R42819
  · exact R42821
  · exact R42823
  · exact R42825
  · exact R42827
  · exact R42829
  · exact R42831
  · exact R42833
  · exact R42835
  · exact R42837
  · exact R42839
  · exact R42841
  · exact R42843
  · exact R42845
  · exact R42847
  · exact R42849
  · exact R42851
  · exact R42853
  · exact R42855
  · exact R42857
  · exact R42859
  · exact R42861
  · exact R42863
  · exact R42865
  · exact R42867
  · exact R42869
  · exact R42871
  · exact R42873
  · exact R42875
  · exact R42877
  · exact R42879
  · exact R42881
  · exact R42883
  · exact R42885
  · exact R42887
  · exact R42889
  · exact R42891
  · exact R42893
  · exact R42895
  · exact R42897
  · exact R42899
  · exact R42901
  · exact R42903
  · exact R42905
  · exact R42907
  · exact R42909
  · exact R42911
  · exact R42913
  · exact R42915
  · exact R42917
  · exact R42919
  · exact R42921
  · exact R42923
  · exact R42925
  · exact R42927
  · exact R42929
  · exact R42931
  · exact R42933
  · exact R42935
  · exact R42937
  · exact R42939
  · exact R42941
  · exact R42943
  · exact R42945
  · exact R42947
  · exact R42949
  · exact R42951
  · exact R42953
  · exact R42955
  · exact R42957
  · exact R42959
  · exact R42961
  · exact R42963
  · exact R42965
  · exact R42967
  · exact R42969
  · exact R42971
  · exact R42973
  · exact R42975
  · exact R42977
  · exact R42979
  · exact R42981
  · exact R42983
  · exact R42985
  · exact R42987
  · exact R42989
  · exact R42991
  · exact R42993
  · exact R42995
  · exact R42997
  · exact R42999
  · exact R43001
  · exact R43003
  · exact R43005
  · exact R43007
  · exact R43009
  · exact R43011
  · exact R43013
  · exact R43015
  · exact R43017
  · exact R43019
  · exact R43021
  · exact R43023
  · exact R43025
  · exact R43027
  · exact R43029
  · exact R43031
  · exact R43033
  · exact R43035
  · exact R43037
  · exact R43039
  · exact R43041
  · exact R43043
  · exact R43045
  · exact R43047
  · exact R43049
  · exact R43051
  · exact R43053
  · exact R43055
  · exact R43057
  · exact R43059
  · exact R43061
  · exact R43063
  · exact R43065
  · exact R43067
  · exact R43069
  · exact R43071
  · exact R43073
  · exact R43075
  · exact R43077
  · exact R43079
  · exact R43081
  · exact R43083
  · exact R43085
  · exact R43087
  · exact R43089
  · exact R43091
  · exact R43093
  · exact R43095
  · exact R43097
  · exact R43099
  · exact R43101
  · exact R43103
  · exact R43105
  · exact R43107
  · exact R43109
  · exact R43111
  · exact R43113
  · exact R43115
  · exact R43117

theorem solution (m : ℕ) (hm : 0 < m) (hodd : Odd m) (hle : m ≤ 43117) :
    ∃ k : ℕ, syracuseStep^[k] m = 1 := by
  rcases Nat.lt_or_ge m 39117 with hlo | hlo
  · exact syracuse_reaches_one_below_39117 m hm hodd (by omega)
  obtain ⟨j, rfl⟩ : ∃ j, m = 2 * j + 1 := by obtain ⟨t, ht⟩ := hodd; exact ⟨t, by omega⟩
  rcases Nat.lt_or_ge j 20258 with h0 | h0
  · exact C0 j (by omega) (by omega)
  rcases Nat.lt_or_ge j 20958 with h1 | h1
  · exact C1 j (by omega) (by omega)
  exact C2 j (by omega) (by omega)
